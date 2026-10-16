-- Prove2me | Theorems.Thm_ExactVacuumAtlas_CoordRelation_jacobian_comp
-- name    : ExactVacuumAtlas.CoordRelation.jacobian_comp
-- status  : Proved
-- author  : @He Wang
-- created : 2026-10-15T21:14:47.021339+00:00
-- url     : https://prove2.me/theorems/a9779cfc-1f1d-45f1-bcca-1d32adc551d5
-- title:
--   Chain rule for slice derivatives of composed relations
-- statement:
--   Dimension 4. If V is open and CoordRelation g₁ g₂ U V Φ₁ Ψ₁ J₁, CoordRelation g₂ g₃ V W Φ₂ Ψ₂ J₂, then for x ∈ U the slice u ↦ Φ₂(Φ₁(x[x_i := u]))_k has derivative (J₂(Φ₁ x) · J₁ x)_{ki} at x_i.
-- source:
--   He Wang, Exact Vacuum Atlas II, local source snapshot (public Git repository not yet available), commit 11fb317259353b71a41d6daed466c495cffd7db4; Atlas/Transport/Relation.lean#L54-L75; SHA-256 8a3ea409772f1e9745156a223c9320dc9990fadec23f28f8530bb252ce3422bd. Mathematical background: See mission/PHYSICS_BOUNDARY.md §A-F for registered definitions and literature references (Wald, Müller-Grave arXiv:0904.4184, Visser arXiv:0706.0622, Martel-Poisson gr-qc/0001069).

import Mathlib
import Definitions.Def_Atlas_Core_Basic
import Definitions.Def_Atlas_Core_Relation
open scoped ContDiff
open ExactVacuumAtlas
variable {g₁ g₂ g₃ : Metric 4} {U V W : Set (Pt 4)} {Φ₁ Ψ₁ Φ₂ Ψ₂ : Pt 4 → Pt 4}
  {J₁ J₂ : Pt 4 → Matrix (Fin 4) (Fin 4) ℝ}

theorem ExactVacuumAtlas.CoordRelation.jacobian_comp (hV : IsOpen V) (h₁ : CoordRelation g₁ g₂ U V Φ₁ Ψ₁ J₁)
    (h₂ : CoordRelation g₂ g₃ V W Φ₂ Ψ₂ J₂) {x : Pt 4} (hx : x ∈ U) (k i : Fin 4) :
    HasDerivAt (fun u => Φ₂ (Φ₁ (Function.update x i u)) k) ((J₂ (Φ₁ x) * J₁ x) k i) (x i) := by sorry
