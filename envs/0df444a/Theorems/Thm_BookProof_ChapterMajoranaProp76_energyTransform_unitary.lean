-- Prove2me | Theorems.Thm_BookProof_ChapterMajoranaProp76_energyTransform_unitary
-- name    : BookProof.ChapterMajoranaProp76.energyTransform_unitary
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-08T02:09:49.641215+00:00
-- url     : https://prove2.me/theorems/8036f21d-dd9a-40e4-bcc2-09731bc29c60
-- title:
--   Proposition 76 (energy transform is unitary).** For any Note-4 unitary `V` (the time-Fourier transform `𝓕_P(−p⁰)`) and any linear isometry equivalence `Θ`, the energy transform `𝓔 = Θ ∘ V
-- statement:
--   **Proposition 76 (energy transform is unitary).**  For any Note-4 unitary
--   `V` (the time-Fourier transform `𝓕_P(−p⁰)`) and any linear isometry equivalence
--   `Θ`, the energy transform `𝓔 = Θ ∘ V ∘ Θ⁻¹` is a Note-4 unitary.
--
--
--
--   **Formalization Note.** Lean 4 identifier: `BookProof.ChapterMajoranaProp76.energyTransform_unitary` (module `BookProof.MajoranaProp76`), line-linked source: `ChapterMajoranaProp76.lean` lines 107–112.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterMajoranaProp76.lean#L107-L112

-- Generated from ChapterMajoranaProp76.lean — theorem BookProof.ChapterMajoranaProp76.energyTransform_unitary
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

theorem BookProof.ChapterMajoranaProp76.energyTransform_unitary (Θ : H ≃ₗᵢ[𝕜] K) {V : H → H}
    (hV : IsNote4Unitary 𝕜 V) : IsNote4Unitary 𝕜 (energyTransform Θ V) := by sorry
