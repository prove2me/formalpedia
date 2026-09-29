-- Prove2me | Theorems.Thm_BookProof_FockOneParticleGap_le_eigenvalue_of_le_spectrum
-- name    : BookProof.FockOneParticleGap.le_eigenvalue_of_le_spectrum
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-10T11:11:57.604189+00:00
-- url     : https://prove2.me/theorems/08a6788e-72dc-4f3e-983d-846cb059a862
-- title:
--   {A : F →L[ℂ] F} (hA : IsSelfAdjoint A) {b : HilbertBasis ℕ ℂ F} {e : ℕ → ℝ} (heig : ∀ k, A (b k) = ((e k : ℝ) : ℂ) • b k) {mu : ℝ} (hspec : ∀ lam ∈ spectrum ℝ A, mu ≤ lam) : ∀ k, mu ≤ e k
-- statement:
--   Lean 4 theorem `BookProof.FockOneParticleGap.le_eigenvalue_of_le_spectrum` (module `BookProof.FockOneParticleGap`), source chapter `BookProof/ChapterFockOneParticleGap.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterFockOneParticleGap.lean

-- Generated from ChapterFockOneParticleGap.lean — theorem BookProof.FockOneParticleGap.le_eigenvalue_of_le_spectrum
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

theorem BookProof.FockOneParticleGap.le_eigenvalue_of_le_spectrum {A : F →L[ℂ] F} (hA : IsSelfAdjoint A)
    {b : HilbertBasis ℕ ℂ F} {e : ℕ → ℝ}
    (heig : ∀ k, A (b k) = ((e k : ℝ) : ℂ) • b k) {mu : ℝ}
    (hspec : ∀ lam ∈ spectrum ℝ A, mu ≤ lam) : ∀ k, mu ≤ e k := by sorry
