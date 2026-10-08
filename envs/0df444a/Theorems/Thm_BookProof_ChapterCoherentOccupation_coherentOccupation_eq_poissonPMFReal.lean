-- Prove2me | Theorems.Thm_BookProof_ChapterCoherentOccupation_coherentOccupation_eq_poissonPMFReal
-- name    : BookProof.ChapterCoherentOccupation.coherentOccupation_eq_poissonPMFReal
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-07T21:53:12.024986+00:00
-- url     : https://prove2.me/theorems/6d8ea54e-9f16-4560-9eac-367397108888
-- title:
--   `BookProof.ChapterCoherentOccupation.coherentOccupation_eq_poissonPMFReal` (r : NNReal) (n : ℕ) : coherentOccupation r n = poissonPMFReal r n
-- statement:
--   Prove the following Lean 4 theorem from `ChapterCoherentOccupation`.
--
--   `BookProof.ChapterCoherentOccupation.coherentOccupation_eq_poissonPMFReal` (r : NNReal) (n : ℕ) : coherentOccupation r n = poissonPMFReal r n
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterCoherentOccupation.coherentOccupation_eq_poissonPMFReal`.

-- Generated from ChapterCoherentOccupation.lean — theorem BookProof.ChapterCoherentOccupation.coherentOccupation_eq_poissonPMFReal
import Mathlib
import Definitions.Def_ChapterCoherentOccupation
open BookProof.ChapterCoherentOccupation


noncomputable section


open Real Nat ProbabilityTheory

theorem BookProof.ChapterCoherentOccupation.coherentOccupation_eq_poissonPMFReal (r : NNReal) (n : ℕ) :
    coherentOccupation r n = poissonPMFReal r n := by sorry
