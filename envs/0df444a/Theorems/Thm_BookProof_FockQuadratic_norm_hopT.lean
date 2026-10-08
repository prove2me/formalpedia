-- Prove2me | Theorems.Thm_BookProof_FockQuadratic_norm_hopT
-- name    : BookProof.FockQuadratic.norm_hopT
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-05T20:59:36.003687+00:00
-- url     : https://prove2.me/theorems/91d8d640-3574-4b34-88db-21062d126121
-- title:
--   `BookProof.FockQuadratic.norm_hopT` (P Q : Idx ι) (x : Idx ι → ℂ) (b : Idx ι) : ‖hopT P Q x b‖ = amp P Q b * ‖x (tgt P Q b)‖ * ‖x b‖
-- statement:
--   Prove the following Lean 4 theorem from `ChapterFockQuadraticEsa`.
--
--   `BookProof.FockQuadratic.norm_hopT` (P Q : Idx ι) (x : Idx ι → ℂ) (b : Idx ι) : ‖hopT P Q x b‖ = amp P Q b * ‖x (tgt P Q b)‖ * ‖x b‖
--
--   Formalization note: Lean 4 identifier `BookProof.FockQuadratic.norm_hopT`.

-- Generated from ChapterFockQuadraticEsa.lean — theorem BookProof.FockQuadratic.norm_hopT
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

theorem BookProof.FockQuadratic.norm_hopT (P Q : Idx ι) (x : Idx ι → ℂ) (b : Idx ι) :
    ‖hopT P Q x b‖ = amp P Q b * ‖x (tgt P Q b)‖ * ‖x b‖ := by sorry
