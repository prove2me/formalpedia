-- Prove2me | Theorems.Thm_BookProof_BandEnclosure_fock_mass_gap_of_nested_ritz_bands
-- name    : BookProof.BandEnclosure.fock_mass_gap_of_nested_ritz_bands
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-12T12:04:58.76829+00:00
-- url     : https://prove2.me/theorems/97e6b778-61a5-4339-8edb-c99db05cea56
-- title:
--   [Nontrivial F] (A : F →L[ℂ] F) (hsa : IsSelfAdjoint A) (hpos : ∀ u : F, 0 ≤ (inner ℂ u (A u) : ℂ).re) (b : HilbertBasis ℕ ℂ F) {e : ℕ → ℝ} (heig : ∀ k, A (b k) = ((e k :...
-- statement:
--   Lean 4 theorem `BookProof.BandEnclosure.fock_mass_gap_of_nested_ritz_bands` (module `BookProof.BandEnclosure`), source chapter `BookProof/ChapterBandEnclosure.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterBandEnclosure.lean

-- Generated from ChapterBandEnclosure.lean — theorem BookProof.BandEnclosure.fock_mass_gap_of_nested_ritz_bands
import Mathlib
import Definitions.Def_ChapterBandEnclosure
open BookProof.BandEnclosure










noncomputable section

open Filter Topology


open BookProof.FockOneParticleGap BookProof.FockSecondQuantization
open BookProof.ChapterH6 BookProof.ChapterH8















open BookProof.HermiteGalerkin BookProof.YangMillsFriedrichs
open BookProof.YangMillsFriedrichsLimit BookProof.ChapterSirkRitzSpectrum
open BookProof.FockOneParticleGap

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

theorem BookProof.BandEnclosure.fock_mass_gap_of_nested_ritz_bands [Nontrivial F] (A : F →L[ℂ] F)
    (hsa : IsSelfAdjoint A) (hpos : ∀ u : F, 0 ≤ (inner ℂ u (A u) : ℂ).re)
    (b : HilbertBasis ℕ ℂ F) {e : ℕ → ℝ}
    (heig : ∀ k, A (b k) = ((e k : ℝ) : ℂ) • b k)
    {lo hi : ℕ → ℝ} {mu : ℝ} (hmu : 0 ≤ mu) (hnest : NestedBands lo hi)
    (hritz : ∀ m, ritzInf (finiteModeRestrict A b) (galerkinSpan b (m + 1)) ∈
      Set.Icc (lo m) (hi m))
    (hwidth : Tendsto (fun m => hi m - lo m) atTop (𝓝 0))
    {m₀ : ℕ} (hlo : mu ≤ lo m₀) :
    IsPositiveSelfAdjointExtension (finiteModeRestrict A b) (topRestrict A) ∧
      Tendsto lo atTop (𝓝 (sInf (spectrum ℝ A))) ∧ mu ≤ sInf (spectrum ℝ A) ∧
      dGamma (diagCol e) vac = 0 ∧
      ∀ u : FockAlg, u 0 = 0 →
        mu * ‖toLp u‖ ^ 2 ≤ (inner ℂ (toLp u) (toLp (dGamma (diagCol e) u)) : ℂ).re := by sorry
