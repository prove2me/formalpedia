-- Prove2me | Theorems.Thm_BookProof_BandEnclosure_shiftInvert_band_enclosure
-- name    : BookProof.BandEnclosure.shiftInvert_band_enclosure
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-10T11:00:30.39475+00:00
-- url     : https://prove2.me/theorems/ad68d771-493e-452f-9c2e-dfcc4b03d253
-- title:
--   {lo hi : ℕ → ℝ} {nu lam gam : ℝ} (hlopos : ∀ m, 0 < lo m) (hband : ∀ m, nu ∈ Set.Icc (lo m) (hi m)) (hmap : lam = nu⁻¹ - gam) : ∀ m, lam ∈ Set.Icc ((hi m)⁻¹ - gam) ((lo m)⁻¹ - gam)
-- statement:
--   Lean 4 theorem `BookProof.BandEnclosure.shiftInvert_band_enclosure` (module `BookProof.BandEnclosure`), source chapter `BookProof/ChapterBandEnclosure.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterBandEnclosure.lean

-- Generated from ChapterBandEnclosure.lean — theorem BookProof.BandEnclosure.shiftInvert_band_enclosure
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

theorem BookProof.BandEnclosure.shiftInvert_band_enclosure {lo hi : ℕ → ℝ} {nu lam gam : ℝ}
    (hlopos : ∀ m, 0 < lo m) (hband : ∀ m, nu ∈ Set.Icc (lo m) (hi m))
    (hmap : lam = nu⁻¹ - gam) :
    ∀ m, lam ∈ Set.Icc ((hi m)⁻¹ - gam) ((lo m)⁻¹ - gam) := by sorry
