-- Prove2me | Theorems.Thm_BookProof_QgOuterFockFL_polyGaussCore_le_harmFriedDom
-- name    : BookProof.QgOuterFockFL.polyGaussCore_le_harmFriedDom
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-10T10:33:31.256348+00:00
-- url     : https://prove2.me/theorems/c6d4f89c-eec9-4310-b807-46a6afa2f6a6
-- title:
--   `BookProof.QgOuterFockFL.polyGaussCore_le_harmFriedDom` (d : ℕ) : (polyGaussCore (d := d)) ≤ (harmFried d).dom
-- statement:
--   Prove the following Lean 4 theorem from `ChapterQgOuterFockFarisLavine`.
--
--   `BookProof.QgOuterFockFL.polyGaussCore_le_harmFriedDom` (d : ℕ) : (polyGaussCore (d := d)) ≤ (harmFried d).dom
--
--   Formalization note: Lean 4 identifier `BookProof.QgOuterFockFL.polyGaussCore_le_harmFriedDom`.

-- Generated from ChapterQgOuterFockFarisLavine.lean — theorem BookProof.QgOuterFockFL.polyGaussCore_le_harmFriedDom
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterDirectSumEsa
import Definitions.Def_ChapterQgOuterFockEsa
import Definitions.Def_ChapterYangMillsFriedrichs
import Definitions.Def_ChapterFriedrichsExtension
import Definitions.Def_ChapterComplexShiftCore
import Definitions.Def_ChapterQgHermiteOscillatorEsa
import Mathlib
import Definitions.Def_ChapterQgOuterFockFarisLavine
import Definitions.Def_ChapterHermiteProductCore
open BookProof.HermiteProductCore
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

theorem BookProof.QgOuterFockFL.polyGaussCore_le_harmFriedDom (d : ℕ) :
    (polyGaussCore (d := d)) ≤ (harmFried d).dom := by sorry
