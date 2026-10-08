-- Prove2me | Theorems.Thm_BookProof_FockQuadratic_wsum_single
-- name    : BookProof.FockQuadratic.wsum_single
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-05T21:16:41.569357+00:00
-- url     : https://prove2.me/theorems/92409db5-1c74-48c2-9c12-9a9b66b78b2f
-- title:
--   `BookProof.FockQuadratic.wsum_single` (ω : ι → ℝ) (i : ι) (k : ℕ) : wsum ω (Finsupp.single i k) = ω i * k
-- statement:
--   Prove the following Lean 4 theorem from `ChapterFockQuadraticEsa`.
--
--   `BookProof.FockQuadratic.wsum_single` (ω : ι → ℝ) (i : ι) (k : ℕ) : wsum ω (Finsupp.single i k) = ω i * k
--
--   Formalization note: Lean 4 identifier `BookProof.FockQuadratic.wsum_single`.

-- Generated from ChapterFockQuadraticEsa.lean — theorem BookProof.FockQuadratic.wsum_single
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
import Definitions.Def_ChapterNavierStokesIkebeKato
import Definitions.Def_ChapterNavierStokesDeficiency
import Definitions.Def_ChapterOperatorSeriesEsa
import Mathlib
import Definitions.Def_ChapterFockQuadraticEsa
open BookProof.FockQuadratic

variable {ι : Type*}
variable {ω : ι → ℝ}
variable {κ : Type*}


open scoped ENNReal


open BookProof.FarisLavine BookProof.NavierStokesFlow BookProof.NavierStokesFlow.IkebeKato
open BookProof.NavierStokesFlow.LpNat BookProof.OperatorSeries

noncomputable section

theorem BookProof.FockQuadratic.wsum_single (ω : ι → ℝ) (i : ι) (k : ℕ) : wsum ω (Finsupp.single i k) = ω i * k := by sorry
