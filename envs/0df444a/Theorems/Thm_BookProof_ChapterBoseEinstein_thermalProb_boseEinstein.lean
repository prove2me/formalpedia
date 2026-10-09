-- Prove2me | Theorems.Thm_BookProof_ChapterBoseEinstein_thermalProb_boseEinstein
-- name    : BookProof.ChapterBoseEinstein.thermalProb_boseEinstein
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-07T21:07:01.771207+00:00
-- url     : https://prove2.me/theorems/9b1b39dd-7897-46bd-b873-b726f913abd1
-- title:
--   `BookProof.ChapterBoseEinstein.thermalProb_boseEinstein` (hx : 0 < x) (n : ℕ) : thermalProb (boseEinstein x) n = (1 - Real.exp (-x)) * Real.exp (-x) ^ n
-- statement:
--   Prove the following Lean 4 theorem from `ChapterBoseEinstein`.
--
--   `BookProof.ChapterBoseEinstein.thermalProb_boseEinstein` (hx : 0 < x) (n : ℕ) : thermalProb (boseEinstein x) n = (1 - Real.exp (-x)) * Real.exp (-x) ^ n
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterBoseEinstein.thermalProb_boseEinstein`.

-- Generated from ChapterBoseEinstein.lean — theorem BookProof.ChapterBoseEinstein.thermalProb_boseEinstein
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

theorem BookProof.ChapterBoseEinstein.thermalProb_boseEinstein (hx : 0 < x) (n : ℕ) :
    thermalProb (boseEinstein x) n = (1 - Real.exp (-x)) * Real.exp (-x) ^ n := by sorry
