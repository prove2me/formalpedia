-- Prove2me | Theorems.Thm_BookProof_QgOuterFockFL_dsFibOp_symmetricOn
-- name    : BookProof.QgOuterFockFL.dsFibOp_symmetricOn
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-10T10:33:39.305541+00:00
-- url     : https://prove2.me/theorems/8483e9cc-583c-4418-9977-1d47bf382542
-- title:
--   `BookProof.QgOuterFockFL.dsFibOp_symmetricOn` {K : ℝ} (hrel : ∀ (i : ι) (u : (C i).dom), ‖H i u‖ ≤ K * ‖(C i).op u + (u : G i)‖) (hsym : ∀ i, SymmetricOn (C i).dom (H i)) : Symmetr
-- statement:
--   Prove the following Lean 4 theorem from `ChapterQgOuterFockFarisLavine`.
--
--   `BookProof.QgOuterFockFL.dsFibOp_symmetricOn` {K : ℝ} (hrel : ∀ (i : ι) (u : (C i).dom), ‖H i u‖ ≤ K * ‖(C i).op u + (u : G i)‖) (hsym : ∀ i, SymmetricOn (C i).dom (H i)) : SymmetricOn (dsDom C) (dsFibOp C H K hrel)
--
--   Formalization note: Lean 4 identifier `BookProof.QgOuterFockFL.dsFibOp_symmetricOn`.

-- Generated from ChapterQgOuterFockFarisLavine.lean — theorem BookProof.QgOuterFockFL.dsFibOp_symmetricOn
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterDirectSumEsa
import Definitions.Def_ChapterQgOuterFockEsa
import Definitions.Def_ChapterYangMillsFriedrichs
import Definitions.Def_ChapterFriedrichsExtension
import Definitions.Def_ChapterComplexShiftCore
import Definitions.Def_ChapterQgHermiteOscillatorEsa
import Definitions.Def_ChapterHermiteProductCore
import Mathlib
import Definitions.Def_ChapterQgOuterFockFarisLavine
import Definitions.Def_ChapterFarisLavineCore
open BookProof.QgOuterFockFL


open scoped ENNReal


open BookProof.FarisLavine
open BookProof.DirectSumEsa
open BookProof.QgOuterFock
open BookProof.YangMillsFriedrichs
open BookProof.FriedrichsExtension
open BookProof.FriedrichsExtension.FormDom
open BookProof.HashimotoShiftInvert
open BookProof.QgHermiteOscillator
open BookProof.HermiteProductCore

noncomputable section

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
variable {ι : Type*} {G : ι → Type*} [∀ i, NormedAddCommGroup (G i)]
  [∀ i, InnerProductSpace ℂ (G i)]
variable (C : ∀ i, Comparison (G i))
variable (H : ∀ i, (C i).dom →ₗ[ℂ] G i)
variable {C H}

theorem BookProof.QgOuterFockFL.dsFibOp_symmetricOn {K : ℝ}
    (hrel : ∀ (i : ι) (u : (C i).dom), ‖H i u‖ ≤ K * ‖(C i).op u + (u : G i)‖)
    (hsym : ∀ i, SymmetricOn (C i).dom (H i)) :
    SymmetricOn (dsDom C) (dsFibOp C H K hrel) := by sorry
