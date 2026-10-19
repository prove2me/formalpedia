-- Prove2me | Theorems.Thm_BookProof_YangMillsFriedrichs_weylOpDom_symmetricOn_inc
-- name    : BookProof.YangMillsFriedrichs.weylOpDom_symmetricOn_inc
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-17T20:14:09.599254+00:00
-- url     : https://prove2.me/theorems/55b142cc-6db6-4e82-914d-cfaae6be7896
-- title:
--   The Lean 4 theorem `weylOpDom_symmetricOn` in the `ChapterYangMillsFriedrichs` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `weylOpDom_symmetricOn` in the `ChapterYangMillsFriedrichs` chapter of the timepiece formalization.
--
--   Replaces the unuploadable node `BookProof_YangMillsFriedrichs_weylOpDom_symmetricOn`, whose statement name is already declared inside its published definition bundle; the `_inc` suffix publishes the same statement as its own node.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterYangMillsFriedrichs.lean

-- Generated from ChapterYangMillsFriedrichs.lean — theorem BookProof.YangMillsFriedrichs.weylOpDom_symmetricOn_inc
import Definitions.Def_ChapterFarisLavine
import Mathlib
import Definitions.Def_ChapterYangMillsFriedrichs
import Definitions.Def_ChapterFarisLavineCore
open BookProof.YangMillsFriedrichs



open BookProof.FarisLavine



variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] {D : Submodule ℂ F}

theorem BookProof.YangMillsFriedrichs.weylOpDom_symmetricOn_inc {n m : ℕ} {pi : Fin n → D →ₗ[ℂ] D} {Bf : Fin m → D →ₗ[ℂ] D}
    (hpi : ∀ i, SymmetricOn D (D.subtype.comp (pi i)))
    (hB : ∀ a, SymmetricOn D (D.subtype.comp (Bf a))) :
    SymmetricOn D (weylOp pi Bf) := by sorry
