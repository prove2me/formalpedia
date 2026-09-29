-- Prove2me | Theorems.Thm_BookProof_ChapterMajoranaProp76_energyMomentum_unitary
-- name    : BookProof.ChapterMajoranaProp76.energyMomentum_unitary
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-08T02:12:25.047711+00:00
-- url     : https://prove2.me/theorems/77bb8464-b98a-4862-8ded-5f26f67f4d7c
-- title:
--   Proposition 76 (energy–momentum transform is unitary).** Composing the energy transform `𝓔` with the (unitary) Majorana–Fourier transform `𝓕_M` (any Note-4 unitary `FM : K → K`) yields the
-- statement:
--   **Proposition 76 (energy–momentum transform is unitary).**  Composing the
--   energy transform `𝓔` with the (unitary) Majorana–Fourier transform `𝓕_M`
--   (any Note-4 unitary `FM : K → K`) yields the unitary energy–momentum transform
--   `𝓔 ∘ 𝓕_M`.
--
--
--
--   **Formalization Note.** Lean 4 identifier: `BookProof.ChapterMajoranaProp76.energyMomentum_unitary` (module `BookProof.MajoranaProp76`), line-linked source: `ChapterMajoranaProp76.lean` lines 114–121.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterMajoranaProp76.lean#L114-L121

-- Generated from ChapterMajoranaProp76.lean — theorem BookProof.ChapterMajoranaProp76.energyMomentum_unitary
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

theorem BookProof.ChapterMajoranaProp76.energyMomentum_unitary (Θ : H ≃ₗᵢ[𝕜] K) {V : H → H} {FM : K → K}
    (hV : IsNote4Unitary 𝕜 V) (hFM : IsNote4Unitary 𝕜 FM) :
    IsNote4Unitary 𝕜 (energyTransform Θ V ∘ FM) := by sorry
