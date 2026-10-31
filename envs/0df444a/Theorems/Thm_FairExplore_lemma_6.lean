-- Prove2me | Theorems.Thm_FairExplore_lemma_6
-- name    : FairExplore.lemma_6
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T21:18:10.591806+00:00
-- url     : https://prove2.me/theorems/389ed34f-89b5-4006-bc2f-cb6e86d3509f
-- title:
--   Lemma 6, p.42 — PF-UCB: non-greedy UCB pulls of an arm $a\notin\mathcal A_{\mathrm{sub}}$ occur $O(\log\log T)$ times
-- statement:
--   Let $\mathcal I$ be a grouped $K$-armed bandit instance with parameter $\theta\in(0,1)^K$ (distinct entries), and run PF-UCB. Let $a\notin\mathcal A_{\mathrm{sub}}$, and let $G$ be the set of groups in which $a$ is optimal. Then
--   $$\sum_{t=1}^T\Pr\big(\mathrm{Pull}_t(a),\ A^{\mathrm{greedy}}_t(g)\neq a\ \forall g\in G,\ a\in\mathcal A^{\mathrm{UCB}}_t\big)=O(\log\log T).$$
--
--   **Formalization Note** $G=\{g: a\in\mathcal A^g,\ \theta(a)=\mathrm{OPT}(g)\}$; it is nonempty because $a\notin\mathcal A_{\mathrm{sub}}$. $\mathcal A^{\mathrm{UCB}}_t$ and the greedy arms use PF-UCB's tie-breaking rule.
--
--   Differences from the source:
--   - reading: p_g ≥ 0 with Σ_g p_g = 1 (p.6) → ∀ g, 0 < p g; reason: §2.1 does not say whether a group may have p_g = 0; the paper results about this model (Theorem 3, Theorem 9, Propositions 1, 2, 8–11, Lemmas 4 and 9) are false at p_g = 0 (counterexamples in those items), so p_g > 0 is read as a standing assumption of the model, as every proof of App. C–E uses it (W^g_t, p.34; Claim 3, p.44); no counterexample to this item at p_g = 0 is known
--   - encoding: A^g unrestricted → every A^g nonempty; reason: OPT(g) = max over A^g and the pull A_t ∈ A^{g_t} are undefined otherwise
--   - encoding: G_a unrestricted → every arm belongs to some group; reason: J(a) = max over G_a is undefined otherwise and (13) is infeasible (Σ_g q^g(a) = 1 with every q^g(a) = 0)
--   - reading: UCB_t(a) = max{q : N_t(a)KL(θ̂_t(a), q) ≤ log t + 3 log log t}, θ̂_t empirical mean → f(1) = f(2) = f(3) = log 3 + 3 log log 3, UCB = +∞ and θ̂ = 0 for an unpulled arm; reason: log log t is undefined at t = 1 and negative at t = 2, and θ̂ of an unpulled arm is undefined; the convention is that of the published CappeKLUCB_ExpFam_Setting, and the result is asymptotic
--   - generalization: PF-UCB with an unspecified choice in each "∈ arg max" → PF-UCB with every tie-breaking rule sel; reason: a statement for every rule specializes to the paper policy whatever choice it makes
--   - encoding: A = [K], G a finite set → any finite linearly ordered arm type and any finite group type with the discrete σ-algebra; reason: every finite set of arms is order-isomorphic to [K]; the order is only used to index the uniform choice in step 1 of PF-UCB
--   - encoding: times t = 1, 2, …; Pr and E → Lean step s is paper time s + 1; probabilities are measures of events, expectations are ∫⁻ of nonnegative quantities; reason: Lean indexing; same values
--   - encoding: O(h(T)) as T → ∞, constants depending on the instance and the fixed parameters → ∃ C T₀, ∀ T ≥ T₀, … ≤ C · h(T), with C, T₀ chosen after the instance and the fixed parameters; reason: App. B.1, p.31
-- source:
--   Baek & Farias, Fair Exploration via Axiomatic Bargaining, arXiv:2106.02553v2, Lemma 6, p.42 (proof pp.44–45)

import Mathlib
import Definitions.Def_FairExplore_Policies

open MeasureTheory

namespace FairExplore

/-- Lemma 6: under PF-UCB, let `a ∉ A_sub` and let `G` be the set of groups in which `a` is
optimal. Then `∑_{t=1}^T Pr(Pull_t(a), A^greedy_t(g) ≠ a ∀ g ∈ G, a ∈ A^UCB_t) = O(log log T)`.
Baek & Farias, *Fair Exploration via Axiomatic Bargaining*, arXiv:2106.02553v2, Lemma 6, p.42 (proof pp.44–45).

**Formalization Note** `G = {g : a ∈ A^g, θ(a) = OPT(g)}`, nonempty because `a ∉ A_sub`.
`A^UCB_t` and the greedy arms use the selector `sel` of PF-UCB. Step `s` is paper time `s + 1`. -/
theorem lemma_6 {γ α : Type*} [Fintype γ] [MeasurableSpace γ] [DiscreteMeasurableSpace γ] [DecidableEq γ]
    [Fintype α] [LinearOrder α]
    (S : GroupedStructure γ α) (hp : ∀ g, 0 < S.p g) (hA : ∀ g, (S.A g).Nonempty)
    (hG : ∀ a, ∃ g, a ∈ S.A g) (θ : α → ℝ) (hθ : InKClass θ)
    (sel : Finset α → α) (hsel : IsSelector sel)
    (a : α) (ha : a ∉ subAll S.A θ) :
    ∃ C T₀ : ℝ, ∀ T : ℕ, T₀ ≤ T →
      ∑ s ∈ Finset.range T,
          (law S (gaussLaw θ) {ω | arm (pfucb S.A sel) ω s = a ∧
              (∀ g ∈ Finset.univ.filter (fun g => a ∈ S.A g ∧ θ a = opt S.A θ g),
                (hist (pfucb S.A sel) ω s).greedy sel S.A g ≠ a) ∧
              a ∈ (hist (pfucb S.A sel) ω s).ucbSet sel S.A}).toReal
        ≤ C * Real.log (Real.log T) := by sorry

end FairExplore
