-- Prove2me | Theorems.Thm_BookProof_YangMillsFriedrichs_weylForm_closable
-- name    : BookProof.YangMillsFriedrichs.weylForm_closable
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-13T00:19:37.189969+00:00
-- url     : https://prove2.me/theorems/cdaa5ef3-92a8-4796-aaf2-26dd7d8aeeb4
-- title:
--   The Lean 4 theorem `weylForm_closable` in the `ChapterYangMillsFriedrichs` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `weylForm_closable` in the `ChapterYangMillsFriedrichs` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterYangMillsFriedrichs.lean

-- Generated from ChapterYangMillsFriedrichs.lean — theorem BookProof.YangMillsFriedrichs.weylForm_closable
import Mathlib
import Definitions.Def_ChapterYangMillsFriedrichs
open BookProof.YangMillsFriedrichs


















open BookProof.FarisLavine




variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] {D : Submodule ℂ F}





















variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] {D : Submodule ℂ F}

theorem BookProof.YangMillsFriedrichs.weylForm_closable {n m : ℕ} {pi : Fin n → D →ₗ[ℂ] D} {Bf : Fin m → D →ₗ[ℂ] D}
    (hpi : ∀ i, SymmetricOn D (D.subtype.comp (pi i)))
    (hB : ∀ a, SymmetricOn D (D.subtype.comp (Bf a))) (x : ℕ → D)
    (hCauchy : ∀ ε > 0, ∃ N : ℕ, ∀ p ≥ N, ∀ q ≥ N, formNormSq (weylOp pi Bf) (x p - x q) < ε)
    (hzero : Filter.Tendsto (fun k => ((x k : F))) Filter.atTop (nhds 0)) :
    Filter.Tendsto (fun k => formNormSq (weylOp pi Bf) (x k)) Filter.atTop (nhds 0) := by sorry
