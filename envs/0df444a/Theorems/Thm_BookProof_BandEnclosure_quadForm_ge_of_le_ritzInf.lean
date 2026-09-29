-- Prove2me | Theorems.Thm_BookProof_BandEnclosure_quadForm_ge_of_le_ritzInf
-- name    : BookProof.BandEnclosure.quadForm_ge_of_le_ritzInf
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-10T12:51:53.222606+00:00
-- url     : https://prove2.me/theorems/052b80bc-e84e-492f-bc67-ed33e5a77856
-- title:
--   {D : Submodule ℂ F} (H : D →ₗ[ℂ] F) (hpos : ∀ x : D, 0 ≤ quadForm H x) {mu : ℝ} (hmu : mu ≤ ritzInf H D) (x : D) : mu * ‖(x : F)‖ ^ 2 ≤ quadForm H x
-- statement:
--   Lean 4 theorem `BookProof.BandEnclosure.quadForm_ge_of_le_ritzInf` (module `BookProof.BandEnclosure`), source chapter `BookProof/ChapterBandEnclosure.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterBandEnclosure.lean

-- Generated from ChapterBandEnclosure.lean — theorem BookProof.BandEnclosure.quadForm_ge_of_le_ritzInf
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

theorem BookProof.BandEnclosure.quadForm_ge_of_le_ritzInf {D : Submodule ℂ F} (H : D →ₗ[ℂ] F)
    (hpos : ∀ x : D, 0 ≤ quadForm H x) {mu : ℝ} (hmu : mu ≤ ritzInf H D) (x : D) :
    mu * ‖(x : F)‖ ^ 2 ≤ quadForm H x := by sorry
