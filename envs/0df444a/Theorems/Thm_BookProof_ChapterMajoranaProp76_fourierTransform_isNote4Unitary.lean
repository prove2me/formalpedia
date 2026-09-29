-- Prove2me | Theorems.Thm_BookProof_ChapterMajoranaProp76_fourierTransform_isNote4Unitary
-- name    : BookProof.ChapterMajoranaProp76.fourierTransform_isNote4Unitary
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-08T02:01:10.868243+00:00
-- url     : https://prove2.me/theorems/2cdf5458-531e-46ef-a4e3-e76ff33a66c8
-- title:
--   The Pauli–Fourier transform `𝓕_P` is a Note-4 unitary on `L²`.** This is Plancherel's theorem: Mathlib's `Lp.fourierTransformₗᵢ` is a `≃ₗᵢ[ℂ]`, hence a Note-4 unitary
-- statement:
--   **The Pauli–Fourier transform `𝓕_P` is a Note-4 unitary on `L²`.**  This is
--   Plancherel's theorem: Mathlib's `Lp.fourierTransformₗᵢ` is a `≃ₗᵢ[ℂ]`, hence a
--   Note-4 unitary.
--
--
--
--   **Formalization Note.** Lean 4 identifier: `BookProof.ChapterMajoranaProp76.fourierTransform_isNote4Unitary` (module `BookProof.MajoranaProp76`), line-linked source: `ChapterMajoranaProp76.lean` lines 133–138.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterMajoranaProp76.lean#L133-L138

-- Generated from ChapterMajoranaProp76.lean — theorem BookProof.ChapterMajoranaProp76.fourierTransform_isNote4Unitary
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

theorem BookProof.ChapterMajoranaProp76.fourierTransform_isNote4Unitary :
    IsNote4Unitary ℂ (Lp.fourierTransformₗᵢ E F : Lp F 2 volume → Lp F 2 volume) := by sorry
