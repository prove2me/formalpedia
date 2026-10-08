-- Prove2me | Theorems.Thm_BookProof_FriedrichsExtension_weyl_friedrichs_extension_unconditional
-- name    : BookProof.FriedrichsExtension.weyl_friedrichs_extension_unconditional
-- status  : Disproved
-- author  : @leonardopedro
-- created : 2026-09-18T01:33:17.175222+00:00
-- url     : https://prove2.me/theorems/31b729d5-5d48-4a87-b03c-b88f1ef5c4c3
-- title:
--   The Lean 4 theorem `weyl_friedrichs_extension_unconditional` in the `ChapterFriedrichsExtension` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `weyl_friedrichs_extension_unconditional` in the `ChapterFriedrichsExtension` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterFriedrichsExtension.lean

-- Generated from ChapterFriedrichsExtension.lean — theorem BookProof.FriedrichsExtension.weyl_friedrichs_extension_unconditional
import Mathlib
import Definitions.Def_ChapterFriedrichsExtension
open BookProof.FriedrichsExtension



open BookProof.FarisLavine BookProof.YangMillsFriedrichs BookProof.HashimotoShiftInvert
open BookProof.HermiteGalerkin

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]

theorem BookProof.FriedrichsExtension.weyl_friedrichs_extension_unconditional {D : Submodule ℂ F} {n m : ℕ}
    {pi : Fin n → D →ₗ[ℂ] D} {Bf : Fin m → D →ₗ[ℂ] D}
    (hdense : Dense (D : Set F))
    (hpi : ∀ i, SymmetricOn D (D.subtype.comp (pi i)))
    (hB : ∀ a, SymmetricOn D (D.subtype.comp (Bf a))) :
    ∃ (Dom : Submodule ℂ F) (A : Dom →ₗ[ℂ] F),
      IsPositiveSelfAdjointExtension (weylOp pi Bf) A := by sorry
