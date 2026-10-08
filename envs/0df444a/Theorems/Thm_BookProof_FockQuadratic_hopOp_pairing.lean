-- Prove2me | Theorems.Thm_BookProof_FockQuadratic_hopOp_pairing
-- name    : BookProof.FockQuadratic.hopOp_pairing
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-05T20:59:17.685402+00:00
-- url     : https://prove2.me/theorems/612e5f58-51ab-4009-9514-300588b372ed
-- title:
--   `BookProof.FockQuadratic.hopOp_pairing` (hω : ∀ i, 0 ≤ ω i) {P Q : Idx ι} (hPQ : deg P + deg Q ≤ 2) (hQP : deg Q + deg P ≤ 2) (x y : maxDom (sig ω)) : (inner ℂ (hopOp hω P Q hPQ x
-- statement:
--   Prove the following Lean 4 theorem from `ChapterFockQuadraticEsa`.
--
--   `BookProof.FockQuadratic.hopOp_pairing` (hω : ∀ i, 0 ≤ ω i) {P Q : Idx ι} (hPQ : deg P + deg Q ≤ 2) (hQP : deg Q + deg P ≤ 2) (x y : maxDom (sig ω)) : (inner ℂ (hopOp hω P Q hPQ x : L2I (Idx ι)) (y : L2I (Idx ι)) : ℂ) = inner ℂ (x : L2I (Idx ι)) (hopOp hω Q P hQP y : L2I (Idx ι))
--
--   Formalization note: Lean 4 identifier `BookProof.FockQuadratic.hopOp_pairing`.

-- Generated from ChapterFockQuadraticEsa.lean — theorem BookProof.FockQuadratic.hopOp_pairing
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

theorem BookProof.FockQuadratic.hopOp_pairing (hω : ∀ i, 0 ≤ ω i) {P Q : Idx ι} (hPQ : deg P + deg Q ≤ 2)
    (hQP : deg Q + deg P ≤ 2) (x y : maxDom (sig ω)) :
    (inner ℂ (hopOp hω P Q hPQ x : L2I (Idx ι)) (y : L2I (Idx ι)) : ℂ)
      = inner ℂ (x : L2I (Idx ι)) (hopOp hω Q P hQP y : L2I (Idx ι)) := by sorry
