-- Prove2me | Theorems.Thm_BookProof_ChapterBaryonAsymmetry_matterRadiationRatio_tendsto_atTop
-- name    : BookProof.ChapterBaryonAsymmetry.matterRadiationRatio_tendsto_atTop
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-08T01:59:46.208207+00:00
-- url     : https://prove2.me/theorems/8f4b425e-3d60-48b1-8390-acacf21c865f
-- title:
--   The book's "amplified by the expansion of the Universe".** As the scale factor grows, the matter-to-radiation energy ratio tends to `+∞`
-- statement:
--   **The book's "amplified by the expansion of the Universe".** As the scale
--   factor grows, the matter-to-radiation energy ratio tends to `+∞`.
--
--
--
--   **Formalization Note.** Lean 4 identifier: `BookProof.ChapterBaryonAsymmetry.matterRadiationRatio_tendsto_atTop` (module `BookProof.BaryonAsymmetry`), line-linked source: `ChapterBaryonAsymmetry.lean` lines 119–128.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterBaryonAsymmetry.lean#L119-L128

-- Generated from ChapterBaryonAsymmetry.lean — theorem BookProof.ChapterBaryonAsymmetry.matterRadiationRatio_tendsto_atTop
import Mathlib
import Definitions.Def_ChapterBaryonAsymmetry
open BookProof.ChapterBaryonAsymmetry












open Filter Topology

theorem BookProof.ChapterBaryonAsymmetry.matterRadiationRatio_tendsto_atTop (ρm0 ρr0 : ℝ) (hm : 0 < ρm0) (hr : 0 < ρr0) :
    Tendsto (fun a => matterRadiationRatio ρm0 ρr0 a) atTop atTop := by sorry
