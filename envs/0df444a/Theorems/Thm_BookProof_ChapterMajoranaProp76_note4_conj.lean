-- Prove2me | Theorems.Thm_BookProof_ChapterMajoranaProp76_note4_conj
-- name    : BookProof.ChapterMajoranaProp76.note4_conj
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-08T02:01:43.859714+00:00
-- url     : https://prove2.me/theorems/1d96d635-0969-4ced-9029-f3cf12ca18fd
-- title:
--   Conjugation preserves Note-4 unitarity.** If `V : H → H` is a Note-4 unitary and `Θ : H ≃ₗᵢ[𝕜] K` is a linear isometry equivalence, then the conjugate `Θ ∘ V ∘ Θ⁻¹ : K → K` is a Note-4 uni
-- statement:
--   **Conjugation preserves Note-4 unitarity.**  If `V : H → H` is a Note-4
--   unitary and `Θ : H ≃ₗᵢ[𝕜] K` is a linear isometry equivalence, then the conjugate
--   `Θ ∘ V ∘ Θ⁻¹ : K → K` is a Note-4 unitary.  This is Proposition 76's "same
--   conjugation reason": it is a composition of the unitaries `Θ⁻¹`, `V`, `Θ`.
--
--
--
--   **Formalization Note.** Lean 4 identifier: `BookProof.ChapterMajoranaProp76.note4_conj` (module `BookProof.MajoranaProp76`), line-linked source: `ChapterMajoranaProp76.lean` lines 81–91.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterMajoranaProp76.lean#L81-L91

-- Generated from ChapterMajoranaProp76.lean — theorem BookProof.ChapterMajoranaProp76.note4_conj
import Mathlib
import Definitions.Def_ChapterMajoranaProp76
open BookProof.ChapterMajoranaProp76










open scoped InnerProductSpace


variable {𝕜 : Type*} [RCLike 𝕜]


variable {H K L : Type*}
  [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]
  [NormedAddCommGroup K] [InnerProductSpace 𝕜 K]
  [NormedAddCommGroup L] [InnerProductSpace 𝕜 L]

theorem BookProof.ChapterMajoranaProp76.note4_conj (Θ : H ≃ₗᵢ[𝕜] K) {V : H → H} (hV : IsNote4Unitary 𝕜 V) :
    IsNote4Unitary 𝕜 ((Θ : H → K) ∘ V ∘ (Θ.symm : K → H)) := by sorry
