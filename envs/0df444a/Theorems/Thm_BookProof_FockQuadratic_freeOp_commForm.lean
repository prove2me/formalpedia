-- Prove2me | Theorems.Thm_BookProof_FockQuadratic_freeOp_commForm
-- name    : BookProof.FockQuadratic.freeOp_commForm
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-05T21:14:33.594369+00:00
-- url     : https://prove2.me/theorems/87e1cc83-eb9e-4db3-b43d-750a824e8a1c
-- title:
--   `BookProof.FockQuadratic.freeOp_commForm` (hω : ∀ i, 0 ≤ ω i) (x : maxDom (sig ω)) : commForm (freeOp hω) (diagMax (sig ω)) x = 0
-- statement:
--   Prove the following Lean 4 theorem from `ChapterFockQuadraticEsa`.
--
--   `BookProof.FockQuadratic.freeOp_commForm` (hω : ∀ i, 0 ≤ ω i) (x : maxDom (sig ω)) : commForm (freeOp hω) (diagMax (sig ω)) x = 0
--
--   Formalization note: Lean 4 identifier `BookProof.FockQuadratic.freeOp_commForm`.

-- Generated from ChapterFockQuadraticEsa.lean — theorem BookProof.FockQuadratic.freeOp_commForm
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
import Definitions.Def_ChapterNavierStokesDeficiency
import Definitions.Def_ChapterOperatorSeriesEsa
import Mathlib
import Definitions.Def_ChapterFockQuadraticEsa
import Definitions.Def_ChapterA3n
import Definitions.Def_ChapterFarisLavineCore
import Definitions.Def_ChapterNavierStokesIkebeKato
open BookProof.ChapterA3n
open BookProof.NavierStokesFlow.IkebeKato
open BookProof.FockQuadratic

variable {ι : Type*}
variable {ω : ι → ℝ}


open scoped ENNReal


open BookProof.FarisLavine BookProof.NavierStokesFlow BookProof.NavierStokesFlow.IkebeKato
open BookProof.NavierStokesFlow.LpNat BookProof.OperatorSeries

noncomputable section

theorem BookProof.FockQuadratic.freeOp_commForm (hω : ∀ i, 0 ≤ ω i) (x : maxDom (sig ω)) :
    commForm (freeOp hω) (diagMax (sig ω)) x = 0 := by sorry
