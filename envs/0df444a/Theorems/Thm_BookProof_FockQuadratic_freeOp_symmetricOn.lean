-- Prove2me | Theorems.Thm_BookProof_FockQuadratic_freeOp_symmetricOn
-- name    : BookProof.FockQuadratic.freeOp_symmetricOn
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-05T21:03:54.585995+00:00
-- url     : https://prove2.me/theorems/c92cb497-7ebd-4d86-b95f-0118206d0161
-- title:
--   `BookProof.FockQuadratic.freeOp_symmetricOn` (hω : ∀ i, 0 ≤ ω i) : SymmetricOn (maxDom (sig ω)) (freeOp hω)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterFockQuadraticEsa`.
--
--   `BookProof.FockQuadratic.freeOp_symmetricOn` (hω : ∀ i, 0 ≤ ω i) : SymmetricOn (maxDom (sig ω)) (freeOp hω)
--
--   Formalization note: Lean 4 identifier `BookProof.FockQuadratic.freeOp_symmetricOn`.

-- Generated from ChapterFockQuadraticEsa.lean — theorem BookProof.FockQuadratic.freeOp_symmetricOn
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

theorem BookProof.FockQuadratic.freeOp_symmetricOn (hω : ∀ i, 0 ≤ ω i) :
    SymmetricOn (maxDom (sig ω)) (freeOp hω) := by sorry
