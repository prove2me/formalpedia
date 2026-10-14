-- Prove2me | Theorems.Thm_BookProof_QgOuterFockFL_harmFried_isPositiveSelfAdjointExtension
-- name    : BookProof.QgOuterFockFL.harmFried_isPositiveSelfAdjointExtension
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-11T19:46:19.311253+00:00
-- url     : https://prove2.me/theorems/b3f38a45-2d71-42e7-b1e6-4b5dfa5f1e7c
-- title:
--   `BookProof.QgOuterFockFL.harmFried_isPositiveSelfAdjointExtension` (d : ℕ) : IsPositiveSelfAdjointExtension (harmCore (d := d)) (harmFried d).op
-- statement:
--   Prove the following Lean 4 theorem from `ChapterQgOuterFockFarisLavine`.
--
--   `BookProof.QgOuterFockFL.harmFried_isPositiveSelfAdjointExtension` (d : ℕ) : IsPositiveSelfAdjointExtension (harmCore (d := d)) (harmFried d).op
--
--   Formalization note: Lean 4 identifier `BookProof.QgOuterFockFL.harmFried_isPositiveSelfAdjointExtension`.

-- Generated from ChapterQgOuterFockFarisLavine.lean — theorem BookProof.QgOuterFockFL.harmFried_isPositiveSelfAdjointExtension
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterDirectSumEsa
import Definitions.Def_ChapterQgOuterFockEsa
import Definitions.Def_ChapterFriedrichsExtension
import Definitions.Def_ChapterComplexShiftCore
import Mathlib
import Definitions.Def_ChapterQgOuterFockFarisLavine
import Definitions.Def_ChapterHermiteProductCore
import Definitions.Def_ChapterQgHermiteOscillatorEsa
import Definitions.Def_ChapterYangMillsFriedrichs
open BookProof.HermiteProductCore
open BookProof.QgHermiteOscillator
open BookProof.YangMillsFriedrichs
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

theorem BookProof.QgOuterFockFL.harmFried_isPositiveSelfAdjointExtension (d : ℕ) :
    IsPositiveSelfAdjointExtension (harmCore (d := d)) (harmFried d).op := by sorry
