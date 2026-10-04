-- Prove2me | Theorems.Thm_DiscreteConvex_AlgorithmsB_scaling_phase_fixing
-- name    : DiscreteConvex.AlgorithmsB.scaling_phase_fixing
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-09-28T04:11:26.978377+00:00
-- url     : https://prove2.me/theorems/8f2983a5-eac1-4137-a061-3c2e49035ba0
-- title:
--   Proposition 10.23 -- scaling_phase_fixing
-- statement:
--   **Proposition 10.23** (p.300). At the end of a scaling phase (i.e. under the hypotheses of Proposition 10.20), a coordinate of $x$ far below (resp. above) $0$ relative to $n^2\delta$ is contained in every (resp. no) minimizer of $\rho$.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.300, Proposition 10.23.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.300, Proposition 10.23

import Mathlib
import Definitions.Def_DiscreteConvex_AlgorithmsB_Submodular
import Definitions.Def_DiscreteConvex_AlgorithmsB_MinRho
import Definitions.Def_DiscreteConvex_AlgorithmsB_IsConvexCombOfExtremeBases
import Definitions.Def_DiscreteConvex_AlgorithmsB_IsDeltaFeasibleFlow
import Definitions.Def_DiscreteConvex_AlgorithmsB_AphiActive
import Definitions.Def_DiscreteConvex_AlgorithmsB_ZVec
import Definitions.Def_DiscreteConvex_AlgorithmsB_NoArcsLeaving
import Definitions.Def_DiscreteConvex_AlgorithmsB_NoActiveTriples

namespace DiscreteConvex.AlgorithmsB

open Classical
open scoped Pointwise
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- Proposition 10.23 (p.300). At the end of a scaling phase (i.e. under the hypotheses of
Theorem 10.20), a coordinate of `x` far below (resp. above) `0` relative to `n²δ` is in every
(resp. no) minimizer of `ρ`. -/
theorem scaling_phase_fixing {ι : Type*} [DecidableEq ι] (rho : Finset V → ℤ)
    (hrho : Submodular rho) (I : Finset ι) (L : ι → (V ≃ Fin (Fintype.card V))) (lam : ι → ℝ)
    (x : V → ℝ) (hx : IsConvexCombOfExtremeBases rho I L lam x) (delta : ℝ) (hdelta : 0 < delta)
    (phi : V → V → ℝ) (hphi : IsDeltaFeasibleFlow delta phi) (W : Finset V)
    (hSW : ∀ v, ZVec x phi v ≤ -delta → v ∈ W) (hWT : ∀ v ∈ W, ¬ (delta ≤ ZVec x phi v))
    (hnoarcs : NoArcsLeaving (AphiActive phi) W) (hnoactive : NoActiveTriples I L W) (w : V) :
    (x w < -(Fintype.card V : ℝ)^2 * delta → ∀ X : Finset V, (rho X : ℤ) = MinRho rho → w ∈ X) ∧
    (x w > (Fintype.card V : ℝ)^2 * delta → ∀ X : Finset V, (rho X : ℤ) = MinRho rho → w ∉ X) := by sorry

end DiscreteConvex.AlgorithmsB
