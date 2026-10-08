-- Prove2me | Theorems.Thm_BookProof_FockQuadratic_abs_sig_sub_sig_tgt_le
-- name    : BookProof.FockQuadratic.abs_sig_sub_sig_tgt_le
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-05T21:01:21.663209+00:00
-- url     : https://prove2.me/theorems/78385649-3736-43bb-958a-f24c4623a9b0
-- title:
--   `BookProof.FockQuadratic.abs_sig_sub_sig_tgt_le` (hω : ∀ i, 0 ≤ ω i) {P Q b : Idx ι} (hPQ : deg P + deg Q ≤ 2) (h : P ≤ b) : |sig ω b - sig ω (tgt P Q b)| ≤ wsum ω P + wsum ω Q + 2
-- statement:
--   Prove the following Lean 4 theorem from `ChapterFockQuadraticEsa`.
--
--   `BookProof.FockQuadratic.abs_sig_sub_sig_tgt_le` (hω : ∀ i, 0 ≤ ω i) {P Q b : Idx ι} (hPQ : deg P + deg Q ≤ 2) (h : P ≤ b) : |sig ω b - sig ω (tgt P Q b)| ≤ wsum ω P + wsum ω Q + 2
--
--   Formalization note: Lean 4 identifier `BookProof.FockQuadratic.abs_sig_sub_sig_tgt_le`.

-- Generated from ChapterFockQuadraticEsa.lean — theorem BookProof.FockQuadratic.abs_sig_sub_sig_tgt_le
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
import Definitions.Def_ChapterNavierStokesIkebeKato
import Definitions.Def_ChapterNavierStokesDeficiency
import Definitions.Def_ChapterOperatorSeriesEsa
import Mathlib
import Definitions.Def_ChapterFockQuadraticEsa
import Definitions.Def_ChapterA3n
open BookProof.ChapterA3n
open BookProof.FockQuadratic

variable {ι : Type*}
variable {ω : ι → ℝ}


open scoped ENNReal


open BookProof.FarisLavine BookProof.NavierStokesFlow BookProof.NavierStokesFlow.IkebeKato
open BookProof.NavierStokesFlow.LpNat BookProof.OperatorSeries

noncomputable section

theorem BookProof.FockQuadratic.abs_sig_sub_sig_tgt_le (hω : ∀ i, 0 ≤ ω i) {P Q b : Idx ι} (hPQ : deg P + deg Q ≤ 2)
    (h : P ≤ b) : |sig ω b - sig ω (tgt P Q b)| ≤ wsum ω P + wsum ω Q + 2 := by sorry
