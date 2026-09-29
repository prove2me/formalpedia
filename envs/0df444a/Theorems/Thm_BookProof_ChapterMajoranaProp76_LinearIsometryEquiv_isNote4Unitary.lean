-- Prove2me | Theorems.Thm_BookProof_ChapterMajoranaProp76_LinearIsometryEquiv_isNote4Unitary
-- name    : BookProof.ChapterMajoranaProp76.LinearIsometryEquiv.isNote4Unitary
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-08T01:44:25.811368+00:00
-- url     : https://prove2.me/theorems/b3da917e-e1cd-4760-a550-838d8a2b9aaa
-- title:
--   The Lean 4 theorem `isNote4Unitary` in the `ChapterMajoranaProp76` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `isNote4Unitary` in the `ChapterMajoranaProp76` chapter of the timepiece formalization.
--
--
--
--   **Formalization Note.** Lean 4 identifier: `BookProof.ChapterMajoranaProp76.LinearIsometryEquiv.isNote4Unitary` (module `BookProof.MajoranaProp76`), line-linked source: `ChapterMajoranaProp76.lean` lines 0–0.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterMajoranaProp76.lean#L0-L0

-- Generated from ChapterMajoranaProp76.lean — theorem BookProof.ChapterMajoranaProp76.LinearIsometryEquiv.isNote4Unitary
import Mathlib
import Definitions.Def_ChapterMajoranaProp76
open BookProof.ChapterMajoranaProp76










open scoped InnerProductSpace


variable {𝕜 : Type*} [RCLike 𝕜]


variable {H K L : Type*}
  [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]
  [NormedAddCommGroup K] [InnerProductSpace 𝕜 K]
  [NormedAddCommGroup L] [InnerProductSpace 𝕜 L]

theorem BookProof.ChapterMajoranaProp76.LinearIsometryEquiv.isNote4Unitary (e : H ≃ₗᵢ[𝕜] K) :
    IsNote4Unitary 𝕜 (e : H → K) := by sorry
