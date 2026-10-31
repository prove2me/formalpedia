-- Prove2me | Theorems.Thm_FairExplore_proposition_1
-- name    : FairExplore.proposition_1
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T21:19:06.535815+00:00
-- url     : https://prove2.me/theorems/4acb7ad9-c7a4-4e07-a10f-4e355654f3e6
-- title:
--   Proposition 1, p.9 — KL-UCB is regret-optimal on $\mathcal I_g$ and $\tilde R^g_T/\log T\to\sum_{a\in\mathcal A^g}\Delta^g(a)J^g(a)$ (corrected: $p_g>0$)
-- statement:
--   Let $\mathcal I$ be a grouped $K$-armed bandit instance with parameter $\theta\in(0,1)^K$ (distinct entries), let $g$ be a group with $\mathcal A^g\neq\emptyset$, and let $\mathcal I_g$ be its single-group instance (arms $\mathcal A\cup\{a_0\}$, the null action $a_0$ of mean $0$ the only arm of the other groups). Taking $\pi^*_g$ to be the KL-UCB policy (with any tie-breaking rule):
--
--   1. $\pi^*_g$ is a consistent policy for instances of type $\mathcal I_g$;
--   2. (2) holds: for every consistent (admissible, measurable) policy $\pi'_g$ for instances of type $\mathcal I_g$,
--   $$\limsup_{T\to\infty}\frac{R_T(\pi^*_g,\mathcal I_g)}{\log T}\le\liminf_{T\to\infty}\frac{R_T(\pi'_g,\mathcal I_g)}{\log T};$$
--   3. (7) holds: with $\tilde R^g_T(\mathcal I)=R_T(\pi^*_g,\mathcal I_g)$,
--   $$\lim_{T\to\infty}\frac{\tilde R^g_T(\mathcal I)}{\log T}=\sum_{a\in\mathcal A^g}\Delta^g(a)J^g(a),\qquad J^g(a)=\frac1{\mathrm{KL}(\theta(a),\mathrm{OPT}(g))}.$$
--
--   This fixes the disagreement point of the bargaining problem: the regret group $g$ would incur learning on its own.
--
--   **Formalization Note** In (7) the term of the optimal arm is $0$ (Lean's $1/0=0$ times $\Delta^g=0$). The limsup and liminf in (2) are taken in the extended reals. Clause 2 is stated for the instance $\mathcal I_g(\theta)$; since $\theta$ is arbitrary in the class, this is (2) for every instance of type $\mathcal I_g$.
--
--   Differences from the source:
--   - correction: p_g ≥ 0 with Σ_g p_g = 1 (p.6) → ∀ g, 0 < p g; reason: with p = (1, 0), A^1 = A^2 = {1, 2}, θ = (0.3, 0.6), group g = 2 never arrives, so R̃^2_T = 0, while the right side of (7) is ∆^2(1)J^2(1) = 0.3 · 200/9 > 0; the proofs use p_g > 0 throughout (W^g_t, p.34; Claim 3, p.44; p.61)
--   - encoding: every A^g (implicit) → the group g has A^g nonempty; reason: OPT(g) is undefined otherwise
--   - reading: "Taking π*_g to be the KL-UCB policy satisfies (2)" → KL-UCB is consistent for instances of type I_g, and (2) holds against every consistent π′_g; reason: a regret-optimal policy is by definition consistent (p.7: "a policy π* ∈ Ψ is regret-optimal")
--   - reading: I_g has the action set A ∩ {a₀} → arms Option α (none = a₀); the null action pays the deterministic reward 0; reason: the printed ∩ is a typo for ∪; "we receive no reward under any action" (p.8)
--   - encoding: J^g(a) = 1/KL(θ(a), OPT(g)) for the optimal arm of g (1/0) → Lean 1/0 = 0; reason: the term is multiplied by ∆^g(a) = 0, so (7) is unchanged
--   - generalization: KL-UCB with an unspecified choice in "the arm with the highest UCB" → KL-UCB with every tie-breaking rule selD; reason: a statement for every rule specializes to whatever choice the paper makes
--   - encoding: any policy → any admissible, measurable policy; reason: a policy of the model pulls an available arm (p.6), and expectations of the run presuppose measurability
--   - reading: consistency / log-consistency over every instance of the class → over every θ ∈ (0,1)^K with distinct entries, the structure (G, p, A^g) fixed; reason: the policy knows every quantity except θ (p.6), so the class it is designed for varies θ
--   - reading: UCB_t(a) = max{q : N_t(a)KL(θ̂_t(a), q) ≤ log t + 3 log log t}, θ̂_t empirical mean → f(1) = f(2) = f(3) = log 3 + 3 log log 3, UCB = +∞ and θ̂ = 0 for an unpulled arm; reason: log log t is undefined at t = 1 and negative at t = 2, and θ̂ of an unpulled arm is undefined; the convention is that of the published CappeKLUCB_ExpFam_Setting, and the result is asymptotic
--   - encoding: A = [K], G a finite set → any finite linearly ordered arm type and any finite group type with the discrete σ-algebra; reason: every finite set of arms is order-isomorphic to [K]; the order is only used to index the uniform choice in step 1 of PF-UCB
--   - encoding: times t = 1, 2, …; Pr and E → Lean step s is paper time s + 1; probabilities are measures of events, expectations are ∫⁻ of nonnegative quantities; reason: Lean indexing; same values
-- source:
--   Baek & Farias, Fair Exploration via Axiomatic Bargaining, arXiv:2106.02553v2, Proposition 1, p.9, with (2) and the definition of I_g, p.8 (proof pp.60–61)

import Mathlib
import Definitions.Def_FairExplore_Welfare

open MeasureTheory Filter Topology

namespace FairExplore

/-- Proposition 1: taking `π*_g` to be the KL-UCB policy satisfies (2), i.e. it is a consistent
policy for instances of type `I_g` with
`limsup_T R_T(π*_g, I_g)/log T ≤ liminf_T R_T(π′_g, I_g)/log T` for every consistent `π′_g`; moreover
`lim_T R̃^g_T(I)/log T = ∑_{a ∈ A^g} ∆^g(a) J^g(a)` (7).
Baek & Farias, *Fair Exploration via Axiomatic Bargaining*, arXiv:2106.02553v2, Proposition 1, p.9, with (2), p.8 (proof pp.60–61).

**Formalization Note** `I_g` is `single S g` on the arms `Option α` (`none` = `a₀`, mean `0`, no
reward). KL-UCB on `I_g` breaks ties with any selector `selD`. "Regret-optimal" includes membership
in the consistent class (p.7), stated as the first conjunct. The terms of (7) at the optimal arm are
`∆ = 0` times Lean's `1/0 = 0`. -/
theorem proposition_1 {γ α : Type*} [Fintype γ] [MeasurableSpace γ] [DiscreteMeasurableSpace γ] [DecidableEq γ]
    [Fintype α] [DecidableEq α]
    (S : GroupedStructure γ α) (hp : ∀ g, 0 < S.p g) (θ : α → ℝ) (hθ : InKClass θ)
    (g : γ) (hAg : (S.A g).Nonempty)
    (selD : Finset (Option α) → Option α) (hselD : IsSelector selD) :
    IsConsistentNull S g (klucb (single S g).A selD) ∧
    (∀ π' : Policy γ (Option α), IsAdmissible (single S g).A π' → IsMeasurablePolicy π' →
      IsConsistentNull S g π' →
      limsup (fun T : ℕ =>
          ((regretNull S θ g (klucb (single S g).A selD) T / Real.log T : ℝ) : EReal)) atTop
        ≤ liminf (fun T : ℕ => ((regretNull S θ g π' T / Real.log T : ℝ) : EReal)) atTop) ∧
    Tendsto (fun T : ℕ => Rtilde S θ selD g T / Real.log T) atTop
      (𝓝 (∑ a ∈ S.A g, gap S.A θ g a * Jg S.A θ g a)) := by sorry

end FairExplore
