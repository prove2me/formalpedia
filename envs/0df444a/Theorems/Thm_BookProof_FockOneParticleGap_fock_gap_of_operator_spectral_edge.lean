-- Prove2me | Theorems.Thm_BookProof_FockOneParticleGap_fock_gap_of_operator_spectral_edge
-- name    : BookProof.FockOneParticleGap.fock_gap_of_operator_spectral_edge
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-12T13:14:47.187986+00:00
-- url     : https://prove2.me/theorems/50216a03-57a4-4a9a-a10b-4b522e7d133d
-- title:
--   {A : F →L[ℂ] F} (hA : IsSelfAdjoint A) {b : HilbertBasis ℕ ℂ F} {e : ℕ → ℝ} (heig : ∀ k, A (b k) = ((e k : ℝ) : ℂ) • b k) {mu : ℝ} (hmu : 0 ≤ mu) (hspec : ∀ lam ∈...
-- statement:
--   Lean 4 theorem `BookProof.FockOneParticleGap.fock_gap_of_operator_spectral_edge` (module `BookProof.FockOneParticleGap`), source chapter `BookProof/ChapterFockOneParticleGap.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterFockOneParticleGap.lean

-- Generated from ChapterFockOneParticleGap.lean — theorem BookProof.FockOneParticleGap.fock_gap_of_operator_spectral_edge
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

theorem BookProof.FockOneParticleGap.fock_gap_of_operator_spectral_edge {A : F →L[ℂ] F} (hA : IsSelfAdjoint A)
    {b : HilbertBasis ℕ ℂ F} {e : ℕ → ℝ}
    (heig : ∀ k, A (b k) = ((e k : ℝ) : ℂ) • b k) {mu : ℝ} (hmu : 0 ≤ mu)
    (hspec : ∀ lam ∈ spectrum ℝ A, mu ≤ lam) :
    dGamma (diagCol e) vac = 0 ∧
      ∀ u : FockAlg, u 0 = 0 →
        mu * ‖toLp u‖ ^ 2 ≤ (inner ℂ (toLp u) (toLp (dGamma (diagCol e) u)) : ℂ).re := by sorry
