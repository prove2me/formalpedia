-- Prove2me | Theorems.Thm_BookProof_NavierStokesFlow_MomentumPerturbation_rankTwo_symmetric
-- name    : BookProof.NavierStokesFlow.MomentumPerturbation.rankTwo_symmetric
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-09T17:45:19.825052+00:00
-- url     : https://prove2.me/theorems/588a12e1-6c65-4d94-8ccb-89352c75741a
-- title:
--   `BookProof.NavierStokesFlow.MomentumPerturbation.rankTwo_symmetric` (u w x y : L2I ι) : (inner ℂ (rankTwo u w x) y : ℂ) = inner ℂ x (rankTwo u w y)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterNavierStokesMomentumPerturbation`.
--
--   `BookProof.NavierStokesFlow.MomentumPerturbation.rankTwo_symmetric` (u w x y : L2I ι) : (inner ℂ (rankTwo u w x) y : ℂ) = inner ℂ x (rankTwo u w y)
--
--   Formalization note: Lean 4 identifier `BookProof.NavierStokesFlow.MomentumPerturbation.rankTwo_symmetric`.

-- Generated from ChapterNavierStokesMomentumPerturbation.lean — theorem BookProof.NavierStokesFlow.MomentumPerturbation.rankTwo_symmetric
import Mathlib
import Definitions.Def_ChapterNavierStokesMomentumPerturbation
import Definitions.Def_ChapterNavierStokesIkebeKato
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.MomentumPerturbation




open LpNat BookProof.FarisLavine IkebeKato

variable {ι : Type*}

theorem BookProof.NavierStokesFlow.MomentumPerturbation.rankTwo_symmetric (u w x y : L2I ι) :
    (inner ℂ (rankTwo u w x) y : ℂ) = inner ℂ x (rankTwo u w y) := by sorry
