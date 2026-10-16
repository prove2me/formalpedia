-- Prove2me | Theorems.Thm_ExactVacuumAtlas_fderiv_eq_mulVec
-- name    : ExactVacuumAtlas.fderiv_eq_mulVec
-- status  : Proved
-- author  : @He Wang
-- created : 2026-10-15T21:18:27.402109+00:00
-- url     : https://prove2.me/theorems/a45b8640-c0ec-4658-9a55-65c825dc615d
-- title:
--   Fréchet derivative of a map with genuine slice derivatives
-- statement:
--   Dimension 4. If U is open, Φ is C^∞ on U, x ∈ U and the slices of Φ have genuine derivatives J x k i at x, then fderiv ℝ Φ x v = (J x) ·ᵥ v for every vector v.
-- source:
--   He Wang, Exact Vacuum Atlas II, local source snapshot (public Git repository not yet available), commit 11fb317259353b71a41d6daed466c495cffd7db4; Atlas/Transport/Inverse.lean#L19-L40; SHA-256 42307986732fed628bcabd660036bfa0c301394389ffa58632d43a90d35f262c. Mathematical background: See mission/PHYSICS_BOUNDARY.md §A-F for registered definitions and literature references (Wald, Müller-Grave arXiv:0904.4184, Visser arXiv:0706.0622, Martel-Poisson gr-qc/0001069).

import Mathlib
import Definitions.Def_Atlas_Core_Basic
import Definitions.Def_Atlas_Core_Certificate
import Definitions.Def_Atlas_Core_Relation
import Definitions.Def_Atlas_Transport_Connection
import Definitions.Def_Atlas_Transport_Curvature
import Definitions.Def_Atlas_Transport_MatrixCalc
open scoped ContDiff
open Matrix Filter Topology

theorem ExactVacuumAtlas.fderiv_eq_mulVec {U : Set (Pt 4)} (hU : IsOpen U) {Φ : Pt 4 → Pt 4}
    (hΦ : ContDiffOn ℝ ∞ Φ U) {J : Pt 4 → Matrix (Fin 4) (Fin 4) ℝ} {x : Pt 4} (hx : x ∈ U)
    (hJ : ∀ k i : Fin 4, HasDerivAt (fun u : ℝ => Φ (Function.update x i u) k) (J x k i) (x i))
    (v : Pt 4) : fderiv ℝ Φ x v = J x *ᵥ v := by sorry
