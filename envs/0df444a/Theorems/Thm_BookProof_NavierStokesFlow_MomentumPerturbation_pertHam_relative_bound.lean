-- Prove2me | Theorems.Thm_BookProof_NavierStokesFlow_MomentumPerturbation_pertHam_relative_bound
-- name    : BookProof.NavierStokesFlow.MomentumPerturbation.pertHam_relative_bound
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-09T17:45:42.074975+00:00
-- url     : https://prove2.me/theorems/824f8ef0-b1da-4692-80d8-c52a47d7448b
-- title:
--   `BookProof.NavierStokesFlow.MomentumPerturbation.pertHam_relative_bound` (c : ι → ℝ) (u w : L2I ι) (x : maxDom c) : ‖pertHam c u w x‖ ^ 2 ≤ 2 * ‖diagMax c x‖ ^ 2 + (2 * (2 * (‖u‖ *
-- statement:
--   Prove the following Lean 4 theorem from `ChapterNavierStokesMomentumPerturbation`.
--
--   `BookProof.NavierStokesFlow.MomentumPerturbation.pertHam_relative_bound` (c : ι → ℝ) (u w : L2I ι) (x : maxDom c) : ‖pertHam c u w x‖ ^ 2 ≤ 2 * ‖diagMax c x‖ ^ 2 + (2 * (2 * (‖u‖ * ‖w‖)) ^ 2) * ‖(x : L2I ι)‖ ^ 2
--
--   Formalization note: Lean 4 identifier `BookProof.NavierStokesFlow.MomentumPerturbation.pertHam_relative_bound`.

-- Generated from ChapterNavierStokesMomentumPerturbation.lean — theorem BookProof.NavierStokesFlow.MomentumPerturbation.pertHam_relative_bound
import Mathlib
import Definitions.Def_ChapterNavierStokesMomentumPerturbation
import Definitions.Def_ChapterNavierStokesIkebeKato
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.MomentumPerturbation




open LpNat BookProof.FarisLavine IkebeKato

variable {ι : Type*}

theorem BookProof.NavierStokesFlow.MomentumPerturbation.pertHam_relative_bound (c : ι → ℝ) (u w : L2I ι) (x : maxDom c) :
    ‖pertHam c u w x‖ ^ 2
      ≤ 2 * ‖diagMax c x‖ ^ 2 + (2 * (2 * (‖u‖ * ‖w‖)) ^ 2) * ‖(x : L2I ι)‖ ^ 2 := by sorry
