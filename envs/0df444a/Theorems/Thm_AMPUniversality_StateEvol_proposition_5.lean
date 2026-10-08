-- Prove2me | Theorems.Thm_AMPUniversality_StateEvol_proposition_5
-- name    : AMPUniversality.StateEvol.proposition_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T05:32:14.84313+00:00
-- url     : https://prove2.me/theorems/5ccee461-81de-4faa-b48c-12d8dc56439d
-- title:
--   Proposition 5 — variance of each class-average monomial tends to zero
-- statement:
--   For a polynomial and converging AMP sequence, fix a class $a$, a positive iteration time $t$, and a nonnegative multi-index $m$. The empirical monomial average over that class concentrates in mean square:
--
--   $$\lim_{N\to\infty}\operatorname{Var}\!\left(\frac1{|C_a^N|}\sum_{i\in C_a^N}(x_i^t)^m\right)=0.$$
--
--   This provides the concentration step used to turn coordinate moment limits into empirical convergence. The statement also asserts integrability of the squared average for every size, preventing the variance from taking Lean's default value on a non-square-integrable function.
-- source:
--   Bayati, Lelarge and Montanari, Universality in polytope phase transitions and message passing algorithms, arXiv:1207.7321v2, p. 32, Proposition 5, (4.38)

import Definitions.Def_AMPUniversality_StateEvol_SE

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Filter
open scoped Topology

namespace AMPUniversality.StateEvol

/-- Proposition 5: the variance of each class-average monomial tends to zero. -/
theorem proposition_5 {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {q h k d : ℕ}
    (M : Model Ω q h k d) (hconv : IsConverging P M)
    (t : ℕ) (ht : 1 ≤ t) (a : Fin k) (m : Fin q → ℕ) :
    (∀ N, Integrable
      (fun ω => (((M.class N a).card : ℝ)⁻¹ *
        ∑ i ∈ M.class N a, monomial m (M.orbit N ω t i)) ^ 2) P) ∧
    Tendsto
      (fun N => variance
        (fun ω => ((M.class N a).card : ℝ)⁻¹ *
          ∑ i ∈ M.class N a, monomial m (M.orbit N ω t i)) P)
      atTop (𝓝 0) := by sorry

end AMPUniversality.StateEvol
