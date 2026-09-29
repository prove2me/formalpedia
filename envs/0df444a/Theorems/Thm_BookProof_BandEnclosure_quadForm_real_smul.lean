-- Prove2me | Theorems.Thm_BookProof_BandEnclosure_quadForm_real_smul
-- name    : BookProof.BandEnclosure.quadForm_real_smul
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-10T10:59:31.033547+00:00
-- url     : https://prove2.me/theorems/b8770fa8-7be3-45e0-ace1-8ccba2db115e
-- title:
--   {D : Submodule ℂ F} (H : D →ₗ[ℂ] F) (c : ℝ) (x : D) : quadForm H ((c : ℂ) • x) = c ^ 2 * quadForm H x
-- statement:
--   Lean 4 theorem `BookProof.BandEnclosure.quadForm_real_smul` (module `BookProof.BandEnclosure`), source chapter `BookProof/ChapterBandEnclosure.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterBandEnclosure.lean

-- Generated from ChapterBandEnclosure.lean — theorem BookProof.BandEnclosure.quadForm_real_smul
import Mathlib
import Definitions.Def_ChapterBandEnclosure
import Definitions.Def_ChapterFriedrichsFormGap
open BookProof.BandEnclosure










noncomputable section

open Filter Topology


open BookProof.FockOneParticleGap BookProof.FockSecondQuantization
open BookProof.ChapterH6 BookProof.ChapterH8















open BookProof.HermiteGalerkin BookProof.YangMillsFriedrichs
open BookProof.YangMillsFriedrichsLimit BookProof.ChapterSirkRitzSpectrum

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]













open BookProof.FarisLavine BookProof.HermiteGalerkin BookProof.YangMillsFriedrichs
open BookProof.HashimotoShiftInvert BookProof.FriedrichsExtension
open BookProof.FriedrichsFormGap

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

theorem BookProof.BandEnclosure.quadForm_real_smul {D : Submodule ℂ F} (H : D →ₗ[ℂ] F) (c : ℝ) (x : D) :
    quadForm H ((c : ℂ) • x) = c ^ 2 * quadForm H x := by sorry
