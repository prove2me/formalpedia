-- Prove2me | Theorems.Thm_FairExplore_lemma_1
-- name    : FairExplore.lemma_1
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T21:15:36.445984+00:00
-- url     : https://prove2.me/theorems/3cceb511-9c29-4fb6-b31c-348c09aa64b3
-- title:
--   Lemma 1, p.32 — the UCBs are valid except on $O(\log\log T)$ rounds
-- statement:
--   Consider a grouped $K$-armed bandit with parameter $\theta\in(0,1)^K$ (distinct entries) and any admissible measurable policy. Let
--   $$\Lambda_t=\{\mathrm{UCB}_t(a)\ge\theta(a)\ \ \forall a\in\mathcal A\}$$
--   be the event that the KL-UCB index of every arm is at least its mean at time $t$. Then
--   $$\sum_{t=1}^T\Pr(\bar\Lambda_t)=O(\log\log T),$$
--   the constant depending on the instance.
--
--   This lemma does not depend on the policy; it is used in the proofs of Propositions 2, 4, 7 and Lemma 6.
--
--   Differences from the source:
--   - encoding: any policy → any admissible, measurable policy; reason: a policy of the model pulls an available arm (p.6), and expectations of the run presuppose measurability
--   - reading: UCB_t(a) = max{q : N_t(a)KL(θ̂_t(a), q) ≤ log t + 3 log log t}, θ̂_t empirical mean → f(1) = f(2) = f(3) = log 3 + 3 log log 3, UCB = +∞ and θ̂ = 0 for an unpulled arm; reason: log log t is undefined at t = 1 and negative at t = 2, and θ̂ of an unpulled arm is undefined; the convention is that of the published CappeKLUCB_ExpFam_Setting, and the result is asymptotic
--   - encoding: A = [K], G a finite set → any finite linearly ordered arm type and any finite group type with the discrete σ-algebra; reason: every finite set of arms is order-isomorphic to [K]; the order is only used to index the uniform choice in step 1 of PF-UCB
--   - encoding: O(h(T)) as T → ∞, constants depending on the instance and the fixed parameters → ∃ C T₀, ∀ T ≥ T₀, … ≤ C · h(T), with C, T₀ chosen after the instance and the fixed parameters; reason: App. B.1, p.31
--   - encoding: times t = 1, 2, …; Pr and E → Lean step s is paper time s + 1; probabilities are measures of events, expectations are ∫⁻ of nonnegative quantities; reason: Lean indexing; same values
-- source:
--   Baek & Farias, Fair Exploration via Axiomatic Bargaining, arXiv:2106.02553v2, Lemma 1, p.32

import Mathlib
import Definitions.Def_FairExplore_KArmed

open MeasureTheory

namespace FairExplore

/-- Lemma 1 (validity of the UCBs): for any policy,
`∑_{t=1}^T Pr(Λ̄_t) = O(log log T)`, where `Λ_t = {UCB_t(a) ≥ θ(a) ∀ a ∈ A}`.
Baek & Farias, *Fair Exploration via Axiomatic Bargaining*, arXiv:2106.02553v2, Lemma 1, p.32 (B.2: "These lemmas do not depend on the policy that is used").

**Formalization Note** Lean step `s` is paper time `t = s + 1`; `(hist π ω s).ucb a` is `UCB_t(a)`
of (16). `O(log log T)` is `∃ C T₀, ∀ T ≥ T₀, … ≤ C log log T` (App. B.1, p.31), the constant
depending on the instance. The policy is any admissible measurable policy. -/
theorem lemma_1 {γ α : Type*} [Fintype γ] [MeasurableSpace γ] [DiscreteMeasurableSpace γ] [DecidableEq γ]
    [Fintype α] [DecidableEq α]
    (S : GroupedStructure γ α) (θ : α → ℝ) (hθ : InKClass θ)
    (π : Policy γ α) (hπA : IsAdmissible S.A π) (hπM : IsMeasurablePolicy π) :
    ∃ C T₀ : ℝ, ∀ T : ℕ, T₀ ≤ T →
      ∑ s ∈ Finset.range T,
          (law S (gaussLaw θ) {ω | ∃ a, (hist π ω s).ucb a < ((θ a : ℝ) : EReal)}).toReal
        ≤ C * Real.log (Real.log T) := by sorry

end FairExplore
