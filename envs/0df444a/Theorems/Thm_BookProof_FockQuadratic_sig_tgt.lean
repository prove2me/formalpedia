-- Prove2me | Theorems.Thm_BookProof_FockQuadratic_sig_tgt
-- name    : BookProof.FockQuadratic.sig_tgt
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-05T20:57:26.205816+00:00
-- url     : https://prove2.me/theorems/4e8e9fba-f336-4a53-b786-c71799653323
-- title:
--   `BookProof.FockQuadratic.sig_tgt` {ω : ι → ℝ} {P Q a : Idx ι} (h : P ≤ a) : sig ω (tgt P Q a) = sig ω a - wsum ω P - deg P + wsum ω Q + deg Q
-- statement:
--   Prove the following Lean 4 theorem from `ChapterFockQuadraticEsa`.
--
--   `BookProof.FockQuadratic.sig_tgt` {ω : ι → ℝ} {P Q a : Idx ι} (h : P ≤ a) : sig ω (tgt P Q a) = sig ω a - wsum ω P - deg P + wsum ω Q + deg Q
--
--   Formalization note: Lean 4 identifier `BookProof.FockQuadratic.sig_tgt`.

-- Generated from ChapterFockQuadraticEsa.lean — theorem BookProof.FockQuadratic.sig_tgt
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


open scoped ENNReal


open BookProof.FarisLavine BookProof.NavierStokesFlow BookProof.NavierStokesFlow.IkebeKato
open BookProof.NavierStokesFlow.LpNat BookProof.OperatorSeries

noncomputable section

theorem BookProof.FockQuadratic.sig_tgt {ω : ι → ℝ} {P Q a : Idx ι} (h : P ≤ a) :
    sig ω (tgt P Q a) = sig ω a - wsum ω P - deg P + wsum ω Q + deg Q := by sorry
