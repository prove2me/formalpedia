-- Prove2me | Theorems.Thm_BookProof_QgHermiteOscillator_deficiencyTrivialAt_of_eigenbasis
-- name    : BookProof.QgHermiteOscillator.deficiencyTrivialAt_of_eigenbasis
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-12T23:13:44.840786+00:00
-- url     : https://prove2.me/theorems/2425f9d9-1cdc-4fe2-b744-7213469f6ee8
-- title:
--   The Lean 4 theorem `deficiencyTrivialAt_of_eigenbasis` in the `ChapterQgHermiteOscillatorEsa` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `deficiencyTrivialAt_of_eigenbasis` in the `ChapterQgHermiteOscillatorEsa` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterQgHermiteOscillatorEsa.lean

-- Generated from ChapterQgHermiteOscillatorEsa.lean — theorem BookProof.QgHermiteOscillator.deficiencyTrivialAt_of_eigenbasis
import Mathlib
import Definitions.Def_ChapterQgHermiteOscillatorEsa
open BookProof.QgHermiteOscillator











open MeasureTheory Complex MvPolynomial
open BookProof.HermiteProductCore BookProof.HermiteProductBasis
open BookProof.QgHermiteCore BookProof.QgHermiteFriedrichs BookProof.FarisLavine
open BookProof.StoneBridge BookProof.EsaClosure BookProof.ChapterStoneResolvent

noncomputable section



variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
  {ι : Type*} {D : Submodule ℂ F}

theorem BookProof.QgHermiteOscillator.deficiencyTrivialAt_of_eigenbasis (T : D →ₗ[ℂ] F) (b : HilbertBasis ι ℂ F)
    (lam : ι → ℝ) (hmem : ∀ i, (b i : F) ∈ D)
    (heig : ∀ i, T ⟨b i, hmem i⟩ = ((lam i : ℝ) : ℂ) • (b i : F))
    {z : ℂ} (hz : z.im ≠ 0) : DeficiencyTrivialAt D T z := by sorry
