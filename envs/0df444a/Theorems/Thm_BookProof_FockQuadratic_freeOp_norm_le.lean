-- Prove2me | Theorems.Thm_BookProof_FockQuadratic_freeOp_norm_le
-- name    : BookProof.FockQuadratic.freeOp_norm_le
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-05T21:04:07.024595+00:00
-- url     : https://prove2.me/theorems/dccd9eb3-1103-4e5a-b0b4-cbaf280916e1
-- title:
--   `BookProof.FockQuadratic.freeOp_norm_le` (hω : ∀ i, 0 ≤ ω i) (x : maxDom (sig ω)) : ‖(freeOp hω x : L2I (Idx ι))‖ ≤ 1 * ‖(diagMax (sig ω) x : L2I (Idx ι))‖
-- statement:
--   Prove the following Lean 4 theorem from `ChapterFockQuadraticEsa`.
--
--   `BookProof.FockQuadratic.freeOp_norm_le` (hω : ∀ i, 0 ≤ ω i) (x : maxDom (sig ω)) : ‖(freeOp hω x : L2I (Idx ι))‖ ≤ 1 * ‖(diagMax (sig ω) x : L2I (Idx ι))‖
--
--   Formalization note: Lean 4 identifier `BookProof.FockQuadratic.freeOp_norm_le`.

-- Generated from ChapterFockQuadraticEsa.lean — theorem BookProof.FockQuadratic.freeOp_norm_le
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
import Definitions.Def_ChapterNavierStokesDeficiency
import Definitions.Def_ChapterOperatorSeriesEsa
import Mathlib
import Definitions.Def_ChapterFockQuadraticEsa
import Definitions.Def_ChapterA3n
import Definitions.Def_ChapterNavierStokesHermiteFarisLavine
import Definitions.Def_ChapterNavierStokesIkebeKato
open BookProof.ChapterA3n
open BookProof.NavierStokesFlow.HermiteFarisLavine
open BookProof.NavierStokesFlow.IkebeKato
open BookProof.FockQuadratic

variable {ι : Type*}
variable {ω : ι → ℝ}


open scoped ENNReal


open BookProof.FarisLavine BookProof.NavierStokesFlow BookProof.NavierStokesFlow.IkebeKato
open BookProof.NavierStokesFlow.LpNat BookProof.OperatorSeries

noncomputable section

theorem BookProof.FockQuadratic.freeOp_norm_le (hω : ∀ i, 0 ≤ ω i) (x : maxDom (sig ω)) :
    ‖(freeOp hω x : L2I (Idx ι))‖ ≤ 1 * ‖(diagMax (sig ω) x : L2I (Idx ι))‖ := by sorry
