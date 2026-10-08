-- Prove2me | Theorems.Thm_BookProof_FockQuadratic_amp_le_sig
-- name    : BookProof.FockQuadratic.amp_le_sig
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-05T20:57:34.494231+00:00
-- url     : https://prove2.me/theorems/3732b409-0013-4043-b10a-558b5bed6dcf
-- title:
--   `BookProof.FockQuadratic.amp_le_sig` {ω : ι → ℝ} (hω : ∀ i, 0 ≤ ω i) {P Q a : Idx ι} (hPQ : deg P + deg Q ≤ 2) : amp P Q a ≤ 2 * sig ω a
-- statement:
--   Prove the following Lean 4 theorem from `ChapterFockQuadraticEsa`.
--
--   `BookProof.FockQuadratic.amp_le_sig` {ω : ι → ℝ} (hω : ∀ i, 0 ≤ ω i) {P Q a : Idx ι} (hPQ : deg P + deg Q ≤ 2) : amp P Q a ≤ 2 * sig ω a
--
--   Formalization note: Lean 4 identifier `BookProof.FockQuadratic.amp_le_sig`.

-- Generated from ChapterFockQuadraticEsa.lean — theorem BookProof.FockQuadratic.amp_le_sig
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


open scoped ENNReal


open BookProof.FarisLavine BookProof.NavierStokesFlow BookProof.NavierStokesFlow.IkebeKato
open BookProof.NavierStokesFlow.LpNat BookProof.OperatorSeries

noncomputable section

theorem BookProof.FockQuadratic.amp_le_sig {ω : ι → ℝ} (hω : ∀ i, 0 ≤ ω i) {P Q a : Idx ι} (hPQ : deg P + deg Q ≤ 2) :
    amp P Q a ≤ 2 * sig ω a := by sorry
