-- Prove2me | Theorems.Thm_BookProof_FockQuadratic_amp_mul_le
-- name    : BookProof.FockQuadratic.amp_mul_le
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-05T21:01:11.956409+00:00
-- url     : https://prove2.me/theorems/b3313407-dd5c-4dba-8be8-ea641e53b12c
-- title:
--   `BookProof.FockQuadratic.amp_mul_le` (hω : ∀ i, 0 ≤ ω i) {P Q : Idx ι} (hPQ : deg P + deg Q ≤ 2) (b : Idx ι) (p r : ℝ) : amp P Q b * r * p ≤ sig ω b * p ^ 2 + sig ω (tgt P Q b) * r
-- statement:
--   Prove the following Lean 4 theorem from `ChapterFockQuadraticEsa`.
--
--   `BookProof.FockQuadratic.amp_mul_le` (hω : ∀ i, 0 ≤ ω i) {P Q : Idx ι} (hPQ : deg P + deg Q ≤ 2) (b : Idx ι) (p r : ℝ) : amp P Q b * r * p ≤ sig ω b * p ^ 2 + sig ω (tgt P Q b) * r ^ 2
--
--   Formalization note: Lean 4 identifier `BookProof.FockQuadratic.amp_mul_le`.

-- Generated from ChapterFockQuadraticEsa.lean — theorem BookProof.FockQuadratic.amp_mul_le
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
import Definitions.Def_ChapterNavierStokesIkebeKato
import Definitions.Def_ChapterNavierStokesDeficiency
import Definitions.Def_ChapterOperatorSeriesEsa
import Mathlib
import Definitions.Def_ChapterFockQuadraticEsa
import Definitions.Def_ChapterA3n
import Definitions.Def_ChapterNavierStokesHermiteFarisLavine
open BookProof.ChapterA3n
open BookProof.NavierStokesFlow.HermiteFarisLavine
open BookProof.FockQuadratic

variable {ι : Type*}
variable {ω : ι → ℝ}


open scoped ENNReal


open BookProof.FarisLavine BookProof.NavierStokesFlow BookProof.NavierStokesFlow.IkebeKato
open BookProof.NavierStokesFlow.LpNat BookProof.OperatorSeries

noncomputable section

theorem BookProof.FockQuadratic.amp_mul_le (hω : ∀ i, 0 ≤ ω i) {P Q : Idx ι} (hPQ : deg P + deg Q ≤ 2) (b : Idx ι)
    (p r : ℝ) :
    amp P Q b * r * p ≤ sig ω b * p ^ 2 + sig ω (tgt P Q b) * r ^ 2 := by sorry
