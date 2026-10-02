-- Prove2me | Theorems.Thm_DiscreteConvex_AlgorithmsC_khat1_lift_bound
-- name    : DiscreteConvex.AlgorithmsC.khat1_lift_bound
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-09-28T04:36:15.193791+00:00
-- url     : https://prove2.me/theorems/919fbae8-64f3-47ed-a9b8-f478ae2e7b52
-- title:
--   Proposition 10.32 -- khat1_lift_bound
-- statement:
--   **Proposition 10.32** (p.307). For the lift $\tilde g$ of an integer-domain function $g$ to `Option V` (Eq. (10.35)), $\hat K_1(\tilde g)\le K_1(g)+n\cdot K_\infty(g)\le\min[(n+1)K_1(g),2nK_\infty(g)]$.
--
--   **Not in this chunk's own `BRIEF.md` table** — found by direct reading, the size-parameter bound underlying the complexity analysis (excluded, `hard`) of the L$^
--   atural$-convex steepest descent algorithm.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.307, Proposition 10.32.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.307, Proposition 10.32

import Mathlib
import Definitions.Def_DiscreteConvex_AlgorithmsC_LiftedFunctionL
import Definitions.Def_DiscreteConvex_AlgorithmsC_Khat1
import Definitions.Def_DiscreteConvex_AlgorithmsC_K1
import Definitions.Def_DiscreteConvex_AlgorithmsC_KInfty

namespace DiscreteConvex.AlgorithmsC

open Classical
open scoped Pointwise
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- Proposition 10.32 (p.307). For the lift `g̃` of an integer-domain function `g` to
`Option V` (Eq. (10.35)), `K̂₁(g̃) ≤ K₁(g) + n·K∞(g) ≤ min[(n+1)K₁(g), 2n·K∞(g)]`. -/
theorem khat1_lift_bound [Nonempty V] (g : (V → ℤ) → WithTop ℝ) :
    (Khat1 (LiftedFunctionL g) : ℝ) ≤ (K1 g : ℝ) + (Fintype.card V : ℝ) * (KInfty g : ℝ) ∧
    (K1 g : ℝ) + (Fintype.card V : ℝ) * (KInfty g : ℝ) ≤
      min ((Fintype.card V + 1 : ℝ) * (K1 g : ℝ)) (2 * (Fintype.card V : ℝ) * (KInfty g : ℝ)) := by sorry

end DiscreteConvex.AlgorithmsC
