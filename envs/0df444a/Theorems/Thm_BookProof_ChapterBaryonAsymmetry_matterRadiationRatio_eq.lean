-- Prove2me | Theorems.Thm_BookProof_ChapterBaryonAsymmetry_matterRadiationRatio_eq
-- name    : BookProof.ChapterBaryonAsymmetry.matterRadiationRatio_eq
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-08T01:42:18.535219+00:00
-- url     : https://prove2.me/theorems/d3bb639c-b414-4c11-82cb-b5672a3fb56e
-- title:
--   The book's "proportional to the scale of the Universe".** For a positive scale factor and nonzero present-day radiation density, the matter-to-radiation ratio equals `(ρ_{m,0}/ρ_{r,0}) · a
-- statement:
--   **The book's "proportional to the scale of the Universe".** For a positive
--   scale factor and nonzero present-day radiation density, the matter-to-radiation
--   ratio equals `(ρ_{m,0}/ρ_{r,0}) · a`.
--
--
--
--   **Formalization Note.** Lean 4 identifier: `BookProof.ChapterBaryonAsymmetry.matterRadiationRatio_eq` (module `BookProof.BaryonAsymmetry`), line-linked source: `ChapterBaryonAsymmetry.lean` lines 99–106.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterBaryonAsymmetry.lean#L99-L106

-- Generated from ChapterBaryonAsymmetry.lean — theorem BookProof.ChapterBaryonAsymmetry.matterRadiationRatio_eq
import Mathlib
import Definitions.Def_ChapterBaryonAsymmetry
open BookProof.ChapterBaryonAsymmetry












open Filter Topology

theorem BookProof.ChapterBaryonAsymmetry.matterRadiationRatio_eq (ρm0 ρr0 a : ℝ) (ha : 0 < a) (hr : ρr0 ≠ 0) :
    matterRadiationRatio ρm0 ρr0 a = (ρm0 / ρr0) * a := by sorry
