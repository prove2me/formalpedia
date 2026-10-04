-- Prove2me | Theorems.Thm_BookProof_FriedrichsExtension_weyl_hashimoto_selects_friedrichs
-- name    : BookProof.FriedrichsExtension.weyl_hashimoto_selects_friedrichs
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-03T15:21:02.486785+00:00
-- url     : https://prove2.me/theorems/1d5acad2-30f8-4ba6-b56a-6f8adec0c0b2
-- title:
--   The Lean 4 theorem `weyl_hashimoto_selects_friedrichs` in the `ChapterFriedrichsExtension` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `weyl_hashimoto_selects_friedrichs` in the `ChapterFriedrichsExtension` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterFriedrichsExtension.lean

-- Generated from ChapterFriedrichsExtension.lean — theorem BookProof.FriedrichsExtension.weyl_hashimoto_selects_friedrichs
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterComplexShiftCore
import Mathlib
import Definitions.Def_ChapterFriedrichsExtension
import Definitions.Def_ChapterFarisLavineCore
import Definitions.Def_ChapterHashimotoShiftInvert
import Definitions.Def_ChapterHermiteGalerkinFriedrichs
import Definitions.Def_ChapterYangMillsFriedrichs
open BookProof.HermiteGalerkin
open BookProof.YangMillsFriedrichs
open BookProof.FriedrichsExtension

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
variable [CompleteSpace F]



open BookProof.FarisLavine BookProof.YangMillsFriedrichs BookProof.HashimotoShiftInvert
open BookProof.HermiteGalerkin
open scoped InnerProductSpace ENNReal lp
open FormDom
open Filter Topology

theorem BookProof.FriedrichsExtension.weyl_hashimoto_selects_friedrichs (b : HilbertBasis ℕ ℂ F) {n m : ℕ}
    {pi : Fin n → finiteModeDomain b →ₗ[ℂ] finiteModeDomain b}
    {Bf : Fin m → finiteModeDomain b →ₗ[ℂ] finiteModeDomain b}
    (hpi : ∀ i, SymmetricOn (finiteModeDomain b) ((finiteModeDomain b).subtype.comp (pi i)))
    (hB : ∀ a, SymmetricOn (finiteModeDomain b) ((finiteModeDomain b).subtype.comp (Bf a)))
    {γ : ℝ} (hγ : 0 < γ) :
    ∃ (Dom : Submodule ℂ F) (A : Dom →ₗ[ℂ] F) (R : F →L[ℂ] F),
      IsPositiveSelfAdjointExtension (weylOp pi Bf) A ∧ IsShiftInvert A γ R ∧
        IsSelfAdjoint R ∧
        (∀ u : F, Tendsto (fun k : ℕ => galerkinCompression R b k u) atTop (nhds (R u))) ∧
        (∀ (Dom' : Submodule ℂ F) (A' : Dom' →ₗ[ℂ] F), IsShiftInvert A' γ R → Dom' = Dom) := by sorry
