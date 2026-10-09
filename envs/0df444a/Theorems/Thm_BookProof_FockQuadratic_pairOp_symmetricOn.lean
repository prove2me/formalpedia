-- Prove2me | Theorems.Thm_BookProof_FockQuadratic_pairOp_symmetricOn
-- name    : BookProof.FockQuadratic.pairOp_symmetricOn
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-05T21:01:41.804635+00:00
-- url     : https://prove2.me/theorems/9ec2e6d6-73b4-40ea-8ef6-8d9055875e8b
-- title:
--   `BookProof.FockQuadratic.pairOp_symmetricOn` (hω : ∀ i, 0 ≤ ω i) (g : ℂ) (P Q : Idx ι) (hPQ : deg P + deg Q ≤ 2) : SymmetricOn (maxDom (sig ω)) (pairOp hω g P Q hPQ)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterFockQuadraticEsa`.
--
--   `BookProof.FockQuadratic.pairOp_symmetricOn` (hω : ∀ i, 0 ≤ ω i) (g : ℂ) (P Q : Idx ι) (hPQ : deg P + deg Q ≤ 2) : SymmetricOn (maxDom (sig ω)) (pairOp hω g P Q hPQ)
--
--   Formalization note: Lean 4 identifier `BookProof.FockQuadratic.pairOp_symmetricOn`.

-- Generated from ChapterFockQuadraticEsa.lean — theorem BookProof.FockQuadratic.pairOp_symmetricOn
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

theorem BookProof.FockQuadratic.pairOp_symmetricOn (hω : ∀ i, 0 ≤ ω i) (g : ℂ) (P Q : Idx ι)
    (hPQ : deg P + deg Q ≤ 2) : SymmetricOn (maxDom (sig ω)) (pairOp hω g P Q hPQ) := by sorry
