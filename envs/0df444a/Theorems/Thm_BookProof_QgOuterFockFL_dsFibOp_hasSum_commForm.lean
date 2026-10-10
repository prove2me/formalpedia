-- Prove2me | Theorems.Thm_BookProof_QgOuterFockFL_dsFibOp_hasSum_commForm
-- name    : BookProof.QgOuterFockFL.dsFibOp_hasSum_commForm
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-10T10:33:20.415202+00:00
-- url     : https://prove2.me/theorems/cd8b4222-d44c-4886-9707-103a3bc66a53
-- title:
--   `BookProof.QgOuterFockFL.dsFibOp_hasSum_commForm` {K : ℝ} (hrel : ∀ (i : ι) (u : (C i).dom), ‖H i u‖ ≤ K * ‖(C i).op u + (u : G i)‖) (x : dsDom C) : HasSum (fun i => commForm (H i)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterQgOuterFockFarisLavine`.
--
--   `BookProof.QgOuterFockFL.dsFibOp_hasSum_commForm` {K : ℝ} (hrel : ∀ (i : ι) (u : (C i).dom), ‖H i u‖ ≤ K * ‖(C i).op u + (u : G i)‖) (x : dsDom C) : HasSum (fun i => commForm (H i) (C i).op (fib C x i)) (commForm (dsFibOp C H K hrel) (dsCompOp C) x)
--
--   Formalization note: Lean 4 identifier `BookProof.QgOuterFockFL.dsFibOp_hasSum_commForm`.

-- Generated from ChapterQgOuterFockFarisLavine.lean — theorem BookProof.QgOuterFockFL.dsFibOp_hasSum_commForm
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

theorem BookProof.QgOuterFockFL.dsFibOp_hasSum_commForm {K : ℝ}
    (hrel : ∀ (i : ι) (u : (C i).dom), ‖H i u‖ ≤ K * ‖(C i).op u + (u : G i)‖)
    (x : dsDom C) :
    HasSum (fun i => commForm (H i) (C i).op (fib C x i))
      (commForm (dsFibOp C H K hrel) (dsCompOp C) x) := by sorry
