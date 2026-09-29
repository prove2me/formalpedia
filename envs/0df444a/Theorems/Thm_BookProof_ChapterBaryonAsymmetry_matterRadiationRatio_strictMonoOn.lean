-- Prove2me | Theorems.Thm_BookProof_ChapterBaryonAsymmetry_matterRadiationRatio_strictMonoOn
-- name    : BookProof.ChapterBaryonAsymmetry.matterRadiationRatio_strictMonoOn
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-08T01:59:10.86655+00:00
-- url     : https://prove2.me/theorems/d511ef14-f03a-4654-a606-3c2e9808fffc
-- title:
--   The matter-to-radiation ratio is strictly increasing in the scale factor (for positive present-day densities): expansion monotonically favours matter
-- statement:
--   The matter-to-radiation ratio is strictly increasing in the scale factor
--   (for positive present-day densities): expansion monotonically favours matter.
--
--
--
--   **Formalization Note.** Lean 4 identifier: `BookProof.ChapterBaryonAsymmetry.matterRadiationRatio_strictMonoOn` (module `BookProof.BaryonAsymmetry`), line-linked source: `ChapterBaryonAsymmetry.lean` lines 108–117.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterBaryonAsymmetry.lean#L108-L117

-- Generated from ChapterBaryonAsymmetry.lean — theorem BookProof.ChapterBaryonAsymmetry.matterRadiationRatio_strictMonoOn
import Mathlib
import Definitions.Def_ChapterBaryonAsymmetry
open BookProof.ChapterBaryonAsymmetry












open Filter Topology

theorem BookProof.ChapterBaryonAsymmetry.matterRadiationRatio_strictMonoOn (ρm0 ρr0 : ℝ) (hm : 0 < ρm0) (hr : 0 < ρr0) :
    StrictMonoOn (fun a => matterRadiationRatio ρm0 ρr0 a) (Set.Ioi (0 : ℝ)) := by sorry
