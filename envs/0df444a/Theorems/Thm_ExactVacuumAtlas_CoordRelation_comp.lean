-- Prove2me | Theorems.Thm_ExactVacuumAtlas_CoordRelation_comp
-- name    : ExactVacuumAtlas.CoordRelation.comp
-- status  : Proved
-- author  : @He Wang
-- created : 2026-10-15T21:16:47.004521+00:00
-- url     : https://prove2.me/theorems/dcc02005-19a0-4c94-b715-894e1bed19df
-- title:
--   Composition of coordinate relations U → V → W
-- statement:
--   Dimension 4. If V is open, CoordRelation g₁ g₂ U V Φ₁ Ψ₁ J₁ and CoordRelation g₂ g₃ V W Φ₂ Ψ₂ J₂, then CoordRelation g₁ g₃ U W (Φ₂ ∘ Φ₁) (Ψ₁ ∘ Ψ₂) (x ↦ J₂(Φ₁ x) · J₁ x). The middle domain must be open (for the chain rule); no Ricci content.
-- source:
--   He Wang, Exact Vacuum Atlas II, local source snapshot (public Git repository not yet available), commit 11fb317259353b71a41d6daed466c495cffd7db4; Atlas/Transport/Relation.lean#L77-L92; SHA-256 8a3ea409772f1e9745156a223c9320dc9990fadec23f28f8530bb252ce3422bd. Mathematical background: See mission/PHYSICS_BOUNDARY.md §A-F for registered definitions and literature references (Wald, Müller-Grave arXiv:0904.4184, Visser arXiv:0706.0622, Martel-Poisson gr-qc/0001069).

import Mathlib
import Definitions.Def_Atlas_Core_Basic
import Definitions.Def_Atlas_Core_Relation
open scoped ContDiff
open ExactVacuumAtlas
variable {g₁ g₂ g₃ : Metric 4} {U V W : Set (Pt 4)} {Φ₁ Ψ₁ Φ₂ Ψ₂ : Pt 4 → Pt 4}
  {J₁ J₂ : Pt 4 → Matrix (Fin 4) (Fin 4) ℝ}

theorem ExactVacuumAtlas.CoordRelation.comp (hV : IsOpen V) (h₁ : CoordRelation g₁ g₂ U V Φ₁ Ψ₁ J₁)
    (h₂ : CoordRelation g₂ g₃ V W Φ₂ Ψ₂ J₂) :
    CoordRelation g₁ g₃ U W (fun x => Φ₂ (Φ₁ x)) (fun z => Ψ₁ (Ψ₂ z))
      (fun x => J₂ (Φ₁ x) * J₁ x) := by sorry
