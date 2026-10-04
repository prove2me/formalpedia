-- Prove2me | Theorems.Thm_DiscreteConvex_AlgorithmsB_approx_optimality_from_no_augmenting_path
-- name    : DiscreteConvex.AlgorithmsB.approx_optimality_from_no_augmenting_path
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-09-28T04:11:03.144774+00:00
-- url     : https://prove2.me/theorems/65b3c3e0-81d2-4218-8208-b6e39d5c7af9
-- title:
--   Proposition 10.20 -- approx_optimality_from_no_augmenting_path
-- statement:
--   **Proposition 10.20** (p.297). GOAL. If $S\subseteq W\subseteq V\setminus T$, no arcs of the auxiliary network $G_\phi$ leave $W$, and no active triple exists, then $z^-(V)\ge\rho(W)-n\delta$ and $x^-(V)\ge\rho(W)-n^2\delta$ (Eq. (10.23)); moreover $W$ minimizes $\rho$ once $\delta<\Delta/n^2$ for $\Delta$ a lower bound on the least positive gap between two values of $\rho$ (Eq. (10.24)).
--
--   Chosen as goal: the book calls this "a key property of the scaling algorithm" and "a relaxation version of the min-max relation in Proposition 10.8"; its own proof is the most substantial argument in this chunk's placed results, combining the base-polyhedron theory of Propositions 10.8-10.9 with flow augmentation, and Proposition 10.23 is a direct, immediate corollary of it.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.297, Proposition 10.20.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.297, Proposition 10.20

import Mathlib
import Definitions.Def_DiscreteConvex_AlgorithmsB_Submodular
import Definitions.Def_DiscreteConvex_AlgorithmsB_MinRho
import Definitions.Def_DiscreteConvex_AlgorithmsB_NegPart
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
/-- Proposition 10.20 (p.297). GOAL. If `S⊆W⊆V∖T`, no arcs of the auxiliary network leave `W`,
and no active triple exists, then `z⁻(V) ≥ ρ(W)-nδ` and `x⁻(V) ≥ ρ(W)-n²δ`; moreover `W`
minimizes `ρ` once `δ` is smaller than the least positive gap between two values of `ρ`, scaled
by `n²`. -/
theorem approx_optimality_from_no_augmenting_path {ι : Type*} [DecidableEq ι] (rho : Finset V → ℤ)
    (hrho : Submodular rho) (I : Finset ι) (L : ι → (V ≃ Fin (Fintype.card V))) (lam : ι → ℝ)
    (x : V → ℝ) (hx : IsConvexCombOfExtremeBases rho I L lam x) (delta : ℝ) (hdelta : 0 < delta)
    (phi : V → V → ℝ) (hphi : IsDeltaFeasibleFlow delta phi) (W : Finset V)
    (hSW : ∀ v, ZVec x phi v ≤ -delta → v ∈ W) (hWT : ∀ v ∈ W, ¬ (delta ≤ ZVec x phi v))
    (hnoarcs : NoArcsLeaving (AphiActive phi) W) (hnoactive : NoActiveTriples I L W) :
    (∑ v, NegPart (ZVec x phi) v) ≥ (rho W : ℝ) - (Fintype.card V : ℝ) * delta ∧
    (∑ v, NegPart x v) ≥ (rho W : ℝ) - (Fintype.card V : ℝ)^2 * delta ∧
    (∀ Delta : ℝ, (∀ X Y : Finset V, (rho X : ℝ) - (rho Y : ℝ) > 0 → Delta ≤ (rho X : ℝ) - (rho Y : ℝ)) →
      delta < Delta / (Fintype.card V : ℝ)^2 → (rho W : ℤ) = MinRho rho) := by sorry

end DiscreteConvex.AlgorithmsB
