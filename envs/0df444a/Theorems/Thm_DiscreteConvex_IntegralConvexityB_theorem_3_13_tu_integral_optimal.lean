-- Prove2me | Theorems.Thm_DiscreteConvex_IntegralConvexityB_theorem_3_13_tu_integral_optimal
-- name    : DiscreteConvex.IntegralConvexityB.theorem_3_13_tu_integral_optimal
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-09-27T22:02:47.20799+00:00
-- url     : https://prove2.me/theorems/a8e207ca-2b9e-4536-8af5-d7c619889e89
-- title:
--   Theorem 3.13 -- total unimodularity gives integral optimal LP solutions
-- statement:
--   For totally unimodular $A$: integral $b$ (resp. $c$) gives an integral optimal primal (resp. dual) solution whenever an optimal solution exists.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.109, Theorem 3.13.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.109, Theorem 3.13

import Mathlib
import Definitions.Def_DiscreteConvex_IntegralConvexityB_IsTotallyUnimodular
import Definitions.Def_DiscreteConvex_IntegralConvexityB_PrimalFeas
import Definitions.Def_DiscreteConvex_IntegralConvexityB_DualFeas

/-!
Murota, *Discrete Convex Analysis*, SIAM 2003, p.109, Theorem 3.13, in
`DiscreteConvex.IntegralConvexityB`.
-/

namespace DiscreteConvex.IntegralConvexityB

/-- **Theorem 3.13.** Let `A` be totally unimodular. (1) If `b` is integral, the primal LP has
an integral optimal solution as long as it has an optimal solution. (2) If `c` is integral, the
dual LP has an integral optimal solution as long as it has an optimal solution. -/
theorem theorem_3_13_tu_integral_optimal {V W : Type*} [Fintype V] [Fintype W] [DecidableEq V]
    [DecidableEq W] (A : Matrix W V ℝ) (b : W → ℝ) (c : V → ℝ)
    (hTU : IsTotallyUnimodular A) :
    ((∃ bz : W → ℤ, b = fun w => (bz w : ℝ)) →
        (∃ x0 ∈ PrimalFeas A b, ∀ x' ∈ PrimalFeas A b, dotProduct c x0 ≤ dotProduct c x') →
          ∃ x ∈ PrimalFeas A b, (∃ xz : V → ℤ, x = fun v => (xz v : ℝ)) ∧
            ∀ x' ∈ PrimalFeas A b, dotProduct c x ≤ dotProduct c x') ∧
      ((∃ cz : V → ℤ, c = fun v => (cz v : ℝ)) →
        (∃ y0 ∈ DualFeas A c, ∀ y' ∈ DualFeas A c, dotProduct b y0 ≥ dotProduct b y') →
          ∃ y ∈ DualFeas A c, (∃ yz : W → ℤ, y = fun w => (yz w : ℝ)) ∧
            ∀ y' ∈ DualFeas A c, dotProduct b y ≥ dotProduct b y') := by sorry

end DiscreteConvex.IntegralConvexityB
