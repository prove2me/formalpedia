-- Prove2me | Theorems.Thm_BudgetAgg_NashChar_Supplement_theorem_5
-- name    : BudgetAgg.NashChar.Supplement.theorem_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-23T06:11:11.151496+00:00
-- url     : https://prove2.me/theorems/12c07a71-c26e-4fba-935e-b0a7ba2d348b
-- title:
--   Theorem 5 — m = 2, any domain U ⊆ U_SP: a continuous mechanism is anonymous and strategyproof iff it is a generalized median rule
-- statement:
--   Let $m=2$ and let $U\subseteq U_{SP}$ be any domain with at least one utility per peak. A continuous mechanism $f:[0,1]^n\to[0,1]$ is anonymous and strategyproof on $U$ if and only if there are phantoms $0\le\alpha_0\le\alpha_1\le\dots\le\alpha_n\le1$ with
--
--   $$f(P)=\mathrm{med}(p_1,\dots,p_n,\alpha_0,\dots,\alpha_n)\qquad\text{for every profile }P.$$
--
--   This is a companion theorem: the goal (Theorem 3) is not proved from it. It extends Moulin's characterization of generalized median rules from $U_{SP}$ to every subdomain, under continuity. Its proof rests on Lemmas 12 and 13.
--
--   **Formalization Note** $n\ge1$; continuity is a hypothesis on $f$, as in the theorem's wording "a continuous mechanism $f$". Anonymity is $f(P\circ\sigma)=f(P)$ for every permutation $\sigma$ of `Fin n`.
--
--   Differences from the source:
--   - encoding: m = 2: outcomes and peaks are scalars in [0, 1], the share of b (§7, p. 17) → Profile2 n = Fin n → unitInterval, Mechanism2 n = Profile2 n → unitInterval (tops-only); reason: the identification of ∆2 with [0, 1] made on p. 17
--   - encoding: arbitrary domain U ⊆ U_SP with at least one utility per peak (§7, p. 17); single-peakedness = star-shapedness (1) for m = 2 → U : Set (ℝ → ℝ) with IsSPDomain U: every u ∈ U satisfies (1) on [0, 1] at some peak p, and every p ∈ [0, 1] is the peak of some u ∈ U; values of u outside [0, 1] are never used; reason: a utility on [0, 1] extends to ℝ in any way; condition (1) is evaluated only on [0, 1]
--   - encoding: strategyproofness (Definition 8, |N′| = 1) on the domain U → IsSP2 U f: for every i, P, misreport p′ and u ∈ U single-peaked at the true peak P i, u(f(P with p_i replaced by p′)) ≤ u(f(P)); reason: an agent with peak p_i may hold any utility of U peaked at p_i, so the inequality must hold for each of them
--   - encoding: med(x_1, …, x_{2k+1}) (p. 18) → med sorts the 2k+1 values ascending and takes index k (0-based), i.e. the (k+1)-th smallest; reason: definition of the median of an odd number of reals
--   - encoding: continuity in the ℓ1 distance (Definition 7) → Continuous f for the product topology on Fin n → unitInterval and the subspace topology on unitInterval; reason: for m = 2 the ℓ1 distance on ∆2 is twice the distance of the b-shares, and all norms on a finite-dimensional space induce the same topology (p. 8)
-- source:
--   Brandt, Greger, Segal-Halevi, Suksompong, Optimal Budget Aggregation with Star-Shaped Preference Domains, arXiv:2402.15904v3, p. 18, Theorem 5 (proof pp. 38–39)

import Mathlib
import Definitions.Def_BudgetAgg_NashChar_Supplement_TwoAlt

namespace BudgetAgg.NashChar.Supplement

/-- Theorem 5, p. 18: for `m = 2` and any admissible domain `U ⊆ U_SP`, a continuous
mechanism is anonymous and strategyproof iff it is a generalized median rule
`med(p₁, …, pₙ, α₀, …, αₙ)` with `0 ≤ α₀ ≤ ⋯ ≤ αₙ ≤ 1`. -/
theorem theorem_5 {n : ℕ} [NeZero n] (U : Set (ℝ → ℝ)) (hU : IsSPDomain U)
    (f : Mechanism2 n) (hf_cont : Continuous f) :
    (IsAnonymous2 f ∧ IsSP2 U f) ↔
      ∃ α : Fin (n + 1) → ℝ, Monotone α ∧ (∀ k, 0 ≤ α k ∧ α k ≤ 1) ∧
        ∀ P, (f P : ℝ) = genMedian α P := by sorry

end BudgetAgg.NashChar.Supplement
