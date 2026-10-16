-- Prove2me | Theorems.Thm_ExactVacuumAtlas_CoordRelation_jacobian_inv
-- name    : ExactVacuumAtlas.CoordRelation.jacobian_inv
-- status  : Proved
-- author  : @He Wang
-- created : 2026-10-15T21:20:32.375369+00:00
-- url     : https://prove2.me/theorems/338d7397-eec7-455b-ad46-89a79eba2cb4
-- title:
--   Slice derivatives of the inverse map of a coordinate relation
-- statement:
--   Given CoordRelation g₁ g₂ U V Φ Ψ J with U, V open and J x · K x = I on U: for every y ∈ V and all k, i, the slice u ↦ Ψ(y[y_i := u])_k has derivative K (Ψ y) k i at y_i.
-- source:
--   He Wang, Exact Vacuum Atlas II, local source snapshot (public Git repository not yet available), commit 11fb317259353b71a41d6daed466c495cffd7db4; Atlas/Transport/Inverse.lean#L47-L86; SHA-256 42307986732fed628bcabd660036bfa0c301394389ffa58632d43a90d35f262c. Mathematical background: See mission/PHYSICS_BOUNDARY.md §A-F for registered definitions and literature references (Wald, Müller-Grave arXiv:0904.4184, Visser arXiv:0706.0622, Martel-Poisson gr-qc/0001069).

import Mathlib
import Definitions.Def_Atlas_Core_Basic
import Definitions.Def_Atlas_Core_Certificate
import Definitions.Def_Atlas_Core_Relation
import Definitions.Def_Atlas_Transport_Connection
import Definitions.Def_Atlas_Transport_Curvature
import Definitions.Def_Atlas_Transport_MatrixCalc
open scoped ContDiff
open Matrix Filter Topology
open ExactVacuumAtlas
variable {g₁ g₂ : Metric 4} {U V : Set (Pt 4)} {Φ Ψ : Pt 4 → Pt 4}
  {J K : Pt 4 → Matrix (Fin 4) (Fin 4) ℝ}

theorem ExactVacuumAtlas.CoordRelation.jacobian_inv (h : CoordRelation g₁ g₂ U V Φ Ψ J) (hU : IsOpen U) (hV : IsOpen V)
    (hJK : ∀ x ∈ U, J x * K x = 1) {y : Pt 4} (hy : y ∈ V) (k i : Fin 4) :
    HasDerivAt (fun u : ℝ => Ψ (Function.update y i u) k) (K (Ψ y) k i) (y i) := by sorry
