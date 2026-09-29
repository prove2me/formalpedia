-- Prove2me | Theorems.Thm_BookProof_BandEnclosure_shiftInvert_widths_tendsto_zero
-- name    : BookProof.BandEnclosure.shiftInvert_widths_tendsto_zero
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-10T11:01:16.10923+00:00
-- url     : https://prove2.me/theorems/bf4c415b-df6c-4ea2-a1ae-14e349a60653
-- title:
--   {lo hi : ℕ → ℝ} {nu gam : ℝ} (hnu : nu ≠ 0) (hlo : Tendsto lo atTop (𝓝 nu)) (hhi : Tendsto hi atTop (𝓝 nu)) : Tendsto (fun m => ((lo m)⁻¹ - gam) - ((hi m)⁻¹ - gam)) atTop (𝓝 0)
-- statement:
--   Lean 4 theorem `BookProof.BandEnclosure.shiftInvert_widths_tendsto_zero` (module `BookProof.BandEnclosure`), source chapter `BookProof/ChapterBandEnclosure.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterBandEnclosure.lean

-- Generated from ChapterBandEnclosure.lean — theorem BookProof.BandEnclosure.shiftInvert_widths_tendsto_zero
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

theorem BookProof.BandEnclosure.shiftInvert_widths_tendsto_zero {lo hi : ℕ → ℝ} {nu gam : ℝ} (hnu : nu ≠ 0)
    (hlo : Tendsto lo atTop (𝓝 nu)) (hhi : Tendsto hi atTop (𝓝 nu)) :
    Tendsto (fun m => ((lo m)⁻¹ - gam) - ((hi m)⁻¹ - gam)) atTop (𝓝 0) := by sorry
