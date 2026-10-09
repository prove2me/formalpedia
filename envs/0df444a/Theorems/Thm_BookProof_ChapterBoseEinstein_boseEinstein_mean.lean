-- Prove2me | Theorems.Thm_BookProof_ChapterBoseEinstein_boseEinstein_mean
-- name    : BookProof.ChapterBoseEinstein.boseEinstein_mean
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-07T21:06:38.889987+00:00
-- url     : https://prove2.me/theorems/a32d91e3-bf35-4f3a-8a27-39ebc30d2a47
-- title:
--   `BookProof.ChapterBoseEinstein.boseEinstein_mean` (hx : 0 < x) : ∑' n : ℕ, (n : ℝ) * thermalProb (boseEinstein x) n = boseEinstein x
-- statement:
--   Prove the following Lean 4 theorem from `ChapterBoseEinstein`.
--
--   `BookProof.ChapterBoseEinstein.boseEinstein_mean` (hx : 0 < x) : ∑' n : ℕ, (n : ℝ) * thermalProb (boseEinstein x) n = boseEinstein x
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterBoseEinstein.boseEinstein_mean`.

-- Generated from ChapterBoseEinstein.lean — theorem BookProof.ChapterBoseEinstein.boseEinstein_mean
import Definitions.Def_ChapterCoherentOccupation
import Mathlib
import Definitions.Def_ChapterBoseEinstein
import Definitions.Def_ChapterCoherentTemperature
open BookProof.ChapterCoherentTemperature
open BookProof.ChapterBoseEinstein


noncomputable section

open Filter Topology


open BookProof.ChapterCoherentTemperature BookProof.ChapterCoherentOccupation

variable {x : ℝ}

theorem BookProof.ChapterBoseEinstein.boseEinstein_mean (hx : 0 < x) :
    ∑' n : ℕ, (n : ℝ) * thermalProb (boseEinstein x) n = boseEinstein x := by sorry
