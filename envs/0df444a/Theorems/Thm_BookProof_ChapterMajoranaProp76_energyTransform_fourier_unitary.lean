-- Prove2me | Theorems.Thm_BookProof_ChapterMajoranaProp76_energyTransform_fourier_unitary
-- name    : BookProof.ChapterMajoranaProp76.energyTransform_fourier_unitary
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-08T02:13:05.841675+00:00
-- url     : https://prove2.me/theorems/fd0c9b4c-df02-4afd-8937-07cc6ac02641
-- title:
--   The concrete energy transform on `L²` is a Note-4 unitary.** Conjugating the `L²`-Fourier transform by any linear isometry equivalence `Θ` yields a Note-4 unitary — the honest realization
-- statement:
--   **The concrete energy transform on `L²` is a Note-4 unitary.**  Conjugating
--   the `L²`-Fourier transform by any linear isometry equivalence `Θ` yields a Note-4
--   unitary — the honest realization of `𝓔` in the Mathlib `L²` model.
--
--
--
--   **Formalization Note.** Lean 4 identifier: `BookProof.ChapterMajoranaProp76.energyTransform_fourier_unitary` (module `BookProof.MajoranaProp76`), line-linked source: `ChapterMajoranaProp76.lean` lines 140–146.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterMajoranaProp76.lean#L140-L146

-- Generated from ChapterMajoranaProp76.lean — theorem BookProof.ChapterMajoranaProp76.energyTransform_fourier_unitary
import Mathlib
import Definitions.Def_ChapterMajoranaProp76
open BookProof.ChapterMajoranaProp76










open scoped InnerProductSpace


variable {𝕜 : Type*} [RCLike 𝕜]


variable {H K L : Type*}
  [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]
  [NormedAddCommGroup K] [InnerProductSpace 𝕜 K]
  [NormedAddCommGroup L] [InnerProductSpace 𝕜 L]






variable {H K : Type*}
  [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]
  [NormedAddCommGroup K] [InnerProductSpace 𝕜 K]






open MeasureTheory

variable {E F : Type*} [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

theorem BookProof.ChapterMajoranaProp76.energyTransform_fourier_unitary {K : Type*} [NormedAddCommGroup K]
    [InnerProductSpace ℂ K] (Θ : Lp F 2 volume ≃ₗᵢ[ℂ] K) :
    IsNote4Unitary ℂ (energyTransform Θ (Lp.fourierTransformₗᵢ E F)) := by sorry
