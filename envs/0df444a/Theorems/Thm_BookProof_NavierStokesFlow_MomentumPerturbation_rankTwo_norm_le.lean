-- Prove2me | Theorems.Thm_BookProof_NavierStokesFlow_MomentumPerturbation_rankTwo_norm_le
-- name    : BookProof.NavierStokesFlow.MomentumPerturbation.rankTwo_norm_le
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-10T07:51:48.666974+00:00
-- url     : https://prove2.me/theorems/63dcebe2-7735-4a59-a121-49dba6c2814e
-- title:
--   `BookProof.NavierStokesFlow.MomentumPerturbation.rankTwo_norm_le` (u w x : L2I ι) : ‖rankTwo u w x‖ ≤ 2 * (‖u‖ * ‖w‖) * ‖x‖
-- statement:
--   Prove the following Lean 4 theorem from `ChapterNavierStokesMomentumPerturbation`.
--
--   `BookProof.NavierStokesFlow.MomentumPerturbation.rankTwo_norm_le` (u w x : L2I ι) : ‖rankTwo u w x‖ ≤ 2 * (‖u‖ * ‖w‖) * ‖x‖
--
--   Formalization note: Lean 4 identifier `BookProof.NavierStokesFlow.MomentumPerturbation.rankTwo_norm_le`.

-- Generated from ChapterNavierStokesMomentumPerturbation.lean — theorem BookProof.NavierStokesFlow.MomentumPerturbation.rankTwo_norm_le
import Mathlib
import Definitions.Def_ChapterNavierStokesMomentumPerturbation
import Definitions.Def_ChapterNavierStokesIkebeKato
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.MomentumPerturbation




open LpNat BookProof.FarisLavine IkebeKato

variable {ι : Type*}

theorem BookProof.NavierStokesFlow.MomentumPerturbation.rankTwo_norm_le (u w x : L2I ι) : ‖rankTwo u w x‖ ≤ 2 * (‖u‖ * ‖w‖) * ‖x‖ := by sorry
