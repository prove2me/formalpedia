-- Prove2me | Theorems.Thm_BookProof_ChapterMajoranaProp76_note4_comp
-- name    : BookProof.ChapterMajoranaProp76.note4_comp
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-08T01:45:00.039425+00:00
-- url     : https://prove2.me/theorems/32995b2f-d63a-4386-8931-e2e2407f4dfc
-- title:
--   Composition of Note-4 unitaries is a Note-4 unitary.** Surjectivity composes, and the diagonal-inner-preservation chains `⟪g (f x), g (f x)⟫ = ⟪f x, f x⟫ = ⟪x, x⟫`
-- statement:
--   **Composition of Note-4 unitaries is a Note-4 unitary.**  Surjectivity
--   composes, and the diagonal-inner-preservation chains
--   `⟪g (f x), g (f x)⟫ = ⟪f x, f x⟫ = ⟪x, x⟫`.
--
--
--
--   **Formalization Note.** Lean 4 identifier: `BookProof.ChapterMajoranaProp76.note4_comp` (module `BookProof.MajoranaProp76`), line-linked source: `ChapterMajoranaProp76.lean` lines 71–79.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterMajoranaProp76.lean#L71-L79

-- Generated from ChapterMajoranaProp76.lean — theorem BookProof.ChapterMajoranaProp76.note4_comp
import Mathlib
import Definitions.Def_ChapterMajoranaProp76
open BookProof.ChapterMajoranaProp76










open scoped InnerProductSpace


variable {𝕜 : Type*} [RCLike 𝕜]


variable {H K L : Type*}
  [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]
  [NormedAddCommGroup K] [InnerProductSpace 𝕜 K]
  [NormedAddCommGroup L] [InnerProductSpace 𝕜 L]

theorem BookProof.ChapterMajoranaProp76.note4_comp {f : H → K} {g : K → L}
    (hf : IsNote4Unitary 𝕜 f) (hg : IsNote4Unitary 𝕜 g) :
    IsNote4Unitary 𝕜 (g ∘ f) := by sorry
