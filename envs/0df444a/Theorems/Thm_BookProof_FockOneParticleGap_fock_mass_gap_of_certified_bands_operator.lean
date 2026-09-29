-- Prove2me | Theorems.Thm_BookProof_FockOneParticleGap_fock_mass_gap_of_certified_bands_operator
-- name    : BookProof.FockOneParticleGap.fock_mass_gap_of_certified_bands_operator
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-12T13:20:58.977326+00:00
-- url     : https://prove2.me/theorems/807c8904-9022-4e2d-9413-692884d51e7a
-- title:
--   {A : F →L[ℂ] F} (hA : IsSelfAdjoint A) {b : HilbertBasis ℕ ℂ F} {e : ℕ → ℝ} (heig : ∀ k, A (b k) = ((e k : ℝ) : ℂ) • b k) {lo hi : ℕ → ℝ} {mu : ℝ} (hmu : 0 ≤ mu)...
-- statement:
--   Lean 4 theorem `BookProof.FockOneParticleGap.fock_mass_gap_of_certified_bands_operator` (module `BookProof.FockOneParticleGap`), source chapter `BookProof/ChapterFockOneParticleGap.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterFockOneParticleGap.lean

-- Generated from ChapterFockOneParticleGap.lean — theorem BookProof.FockOneParticleGap.fock_mass_gap_of_certified_bands_operator
import Mathlib
import Definitions.Def_ChapterFockOneParticleGap
open BookProof.FockOneParticleGap












noncomputable section


open BookProof.FockSecondQuantization BookProof.FarisLavine BookProof.NavierStokesFlow
open Filter Topology
















































variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

open BookProof.SirkCertifiedGap






open BookProof.ChapterSirkRitzSpectrum

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

theorem BookProof.FockOneParticleGap.fock_mass_gap_of_certified_bands_operator {A : F →L[ℂ] F} (hA : IsSelfAdjoint A)
    {b : HilbertBasis ℕ ℂ F} {e : ℕ → ℝ}
    (heig : ∀ k, A (b k) = ((e k : ℝ) : ℂ) • b k) {lo hi : ℕ → ℝ} {mu : ℝ} (hmu : 0 ≤ mu)
    (hband : ∀ m, sInf (spectrum ℝ A) ∈ Set.Icc (lo m) (hi m))
    (hwidth : Tendsto (fun m => hi m - lo m) atTop (𝓝 0))
    {m₀ : ℕ} (hlo : mu ≤ lo m₀) :
    Tendsto lo atTop (𝓝 (sInf (spectrum ℝ A))) ∧ mu ≤ sInf (spectrum ℝ A) ∧
      dGamma (diagCol e) vac = 0 ∧
      ∀ u : FockAlg, u 0 = 0 →
        mu * ‖toLp u‖ ^ 2 ≤ (inner ℂ (toLp u) (toLp (dGamma (diagCol e) u)) : ℂ).re := by sorry
