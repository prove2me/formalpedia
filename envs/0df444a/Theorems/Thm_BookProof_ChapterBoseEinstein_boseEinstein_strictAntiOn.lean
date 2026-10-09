-- Prove2me | Theorems.Thm_BookProof_ChapterBoseEinstein_boseEinstein_strictAntiOn
-- name    : BookProof.ChapterBoseEinstein.boseEinstein_strictAntiOn
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-07T21:06:46.537402+00:00
-- url     : https://prove2.me/theorems/1aa96462-ce79-4489-9e55-948839139e7a
-- title:
--   `BookProof.ChapterBoseEinstein.boseEinstein_strictAntiOn` : StrictAntiOn boseEinstein (Set.Ioi 0)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterBoseEinstein`.
--
--   `BookProof.ChapterBoseEinstein.boseEinstein_strictAntiOn` : StrictAntiOn boseEinstein (Set.Ioi 0)
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterBoseEinstein.boseEinstein_strictAntiOn`.

-- Generated from ChapterBoseEinstein.lean — theorem BookProof.ChapterBoseEinstein.boseEinstein_strictAntiOn
import Definitions.Def_ChapterCoherentTemperature
import Definitions.Def_ChapterCoherentOccupation
import Mathlib
import Definitions.Def_ChapterBoseEinstein
open BookProof.ChapterBoseEinstein


noncomputable section

open Filter Topology


open BookProof.ChapterCoherentTemperature BookProof.ChapterCoherentOccupation

variable {x : ℝ}

theorem BookProof.ChapterBoseEinstein.boseEinstein_strictAntiOn : StrictAntiOn boseEinstein (Set.Ioi 0) := by sorry
