-- Prove2me | Theorems.Thm_BookProof_FockQuadratic_pairOp_commForm_le
-- name    : BookProof.FockQuadratic.pairOp_commForm_le
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-05T21:01:50.00559+00:00
-- url     : https://prove2.me/theorems/83e6c4a7-4300-4aa0-a7f8-5fe652aee3ab
-- title:
--   `BookProof.FockQuadratic.pairOp_commForm_le` (hω : ∀ i, 0 ≤ ω i) (g : ℂ) (P Q : Idx ι) (hPQ : deg P + deg Q ≤ 2) (x : maxDom (sig ω)) : |commForm (pairOp hω g P Q hPQ) (diagMax (si
-- statement:
--   Prove the following Lean 4 theorem from `ChapterFockQuadraticEsa`.
--
--   `BookProof.FockQuadratic.pairOp_commForm_le` (hω : ∀ i, 0 ≤ ω i) (g : ℂ) (P Q : Idx ι) (hPQ : deg P + deg Q ≤ 2) (x : maxDom (sig ω)) : |commForm (pairOp hω g P Q hPQ) (diagMax (sig ω)) x| ≤ (4 * ‖g‖ * (wsum ω P + wsum ω Q + 2)) * quadForm (diagMax (sig ω)) x
--
--   Formalization note: Lean 4 identifier `BookProof.FockQuadratic.pairOp_commForm_le`.

-- Generated from ChapterFockQuadraticEsa.lean — theorem BookProof.FockQuadratic.pairOp_commForm_le
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
import Definitions.Def_ChapterNavierStokesDeficiency
import Definitions.Def_ChapterOperatorSeriesEsa
import Mathlib
import Definitions.Def_ChapterFockQuadraticEsa
import Definitions.Def_ChapterA3n
import Definitions.Def_ChapterFarisLavineCore
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

theorem BookProof.FockQuadratic.pairOp_commForm_le (hω : ∀ i, 0 ≤ ω i) (g : ℂ) (P Q : Idx ι)
    (hPQ : deg P + deg Q ≤ 2) (x : maxDom (sig ω)) :
    |commForm (pairOp hω g P Q hPQ) (diagMax (sig ω)) x|
      ≤ (4 * ‖g‖ * (wsum ω P + wsum ω Q + 2)) * quadForm (diagMax (sig ω)) x := by sorry
