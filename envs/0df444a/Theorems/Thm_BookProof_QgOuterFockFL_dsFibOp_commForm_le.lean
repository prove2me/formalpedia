-- Prove2me | Theorems.Thm_BookProof_QgOuterFockFL_dsFibOp_commForm_le
-- name    : BookProof.QgOuterFockFL.dsFibOp_commForm_le
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-10T10:33:49.769465+00:00
-- url     : https://prove2.me/theorems/2c597deb-8510-47ec-aaf8-2c65ab8353ca
-- title:
--   `BookProof.QgOuterFockFL.dsFibOp_commForm_le` {K c : ℝ} (hrel : ∀ (i : ι) (u : (C i).dom), ‖H i u‖ ≤ K * ‖(C i).op u + (u : G i)‖) (hcomm : ∀ (i : ι) (u : (C i).dom), |commForm (H
-- statement:
--   Prove the following Lean 4 theorem from `ChapterQgOuterFockFarisLavine`.
--
--   `BookProof.QgOuterFockFL.dsFibOp_commForm_le` {K c : ℝ} (hrel : ∀ (i : ι) (u : (C i).dom), ‖H i u‖ ≤ K * ‖(C i).op u + (u : G i)‖) (hcomm : ∀ (i : ι) (u : (C i).dom), |commForm (H i) (C i).op u| ≤ c * quadForm (C i).op u) (x : dsDom C) : |commForm (dsFibOp C H K hrel) (dsCompOp C) x| ≤ c * quadForm (dsCompOp C) x
--
--   Formalization note: Lean 4 identifier `BookProof.QgOuterFockFL.dsFibOp_commForm_le`.

-- Generated from ChapterQgOuterFockFarisLavine.lean — theorem BookProof.QgOuterFockFL.dsFibOp_commForm_le
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

theorem BookProof.QgOuterFockFL.dsFibOp_commForm_le {K c : ℝ}
    (hrel : ∀ (i : ι) (u : (C i).dom), ‖H i u‖ ≤ K * ‖(C i).op u + (u : G i)‖)
    (hcomm : ∀ (i : ι) (u : (C i).dom), |commForm (H i) (C i).op u| ≤ c * quadForm (C i).op u)
    (x : dsDom C) :
    |commForm (dsFibOp C H K hrel) (dsCompOp C) x| ≤ c * quadForm (dsCompOp C) x := by sorry
