-- Prove2me | Theorems.Thm_BookProof_ChapterCoherentOccupation_thermalProb_summable
-- name    : BookProof.ChapterCoherentOccupation.thermalProb_summable
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-07T21:55:10.445993+00:00
-- url     : https://prove2.me/theorems/4588393b-c181-4a38-ae2d-d86da4ce18eb
-- title:
--   `BookProof.ChapterCoherentOccupation.thermalProb_summable` {nbar : ℝ} (h : 0 ≤ nbar) : Summable (fun n : ℕ => thermalProb nbar n)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterCoherentOccupation`.
--
--   `BookProof.ChapterCoherentOccupation.thermalProb_summable` {nbar : ℝ} (h : 0 ≤ nbar) : Summable (fun n : ℕ => thermalProb nbar n)
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterCoherentOccupation.thermalProb_summable`.

-- Generated from ChapterCoherentOccupation.lean — theorem BookProof.ChapterCoherentOccupation.thermalProb_summable
import Mathlib
import Definitions.Def_ChapterCoherentOccupation
import Definitions.Def_ChapterCoherentTemperature
open BookProof.ChapterCoherentTemperature
open BookProof.ChapterCoherentOccupation


noncomputable section


open Real Nat ProbabilityTheory

theorem BookProof.ChapterCoherentOccupation.thermalProb_summable {nbar : ℝ} (h : 0 ≤ nbar) :
    Summable (fun n : ℕ => thermalProb nbar n) := by sorry
