-- Prove2me | Theorems.Thm_BookProof_QgHermiteOscillator_essentiallySelfAdjointOn_of_eigenbasis
-- name    : BookProof.QgHermiteOscillator.essentiallySelfAdjointOn_of_eigenbasis
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-12T23:27:09.896254+00:00
-- url     : https://prove2.me/theorems/0f3c81df-3ed8-41b2-a80e-3684b081e80a
-- title:
--   The Lean 4 theorem `essentiallySelfAdjointOn_of_eigenbasis` in the `ChapterQgHermiteOscillatorEsa` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `essentiallySelfAdjointOn_of_eigenbasis` in the `ChapterQgHermiteOscillatorEsa` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterQgHermiteOscillatorEsa.lean

-- Generated from ChapterQgHermiteOscillatorEsa.lean — theorem BookProof.QgHermiteOscillator.essentiallySelfAdjointOn_of_eigenbasis
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

theorem BookProof.QgHermiteOscillator.essentiallySelfAdjointOn_of_eigenbasis (T : D →ₗ[ℂ] F) (b : HilbertBasis ι ℂ F)
    (lam : ι → ℝ) (hmem : ∀ i, (b i : F) ∈ D)
    (heig : ∀ i, T ⟨b i, hmem i⟩ = ((lam i : ℝ) : ℂ) • (b i : F)) :
    EssentiallySelfAdjointOn D T := by sorry
