-- Prove2me | Theorems.Thm_BookProof_QgPhysicalSectorIdentity_wsum_creIdx
-- name    : BookProof.QgPhysicalSectorIdentity.wsum_creIdx
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-16T23:34:19.071353+00:00
-- url     : https://prove2.me/theorems/a7e64535-c718-4dcf-b0c2-42f66e73aae3
-- title:
--   `BookProof.QgPhysicalSectorIdentity.wsum_creIdx` (ω : ι → ℝ) (i : ι) : wsum ω (creIdx i) = ω i
-- statement:
--   Prove the following Lean 4 theorem from `ChapterQgPhysicalSectorIdentity`.
--
--   `BookProof.QgPhysicalSectorIdentity.wsum_creIdx` (ω : ι → ℝ) (i : ι) : wsum ω (creIdx i) = ω i
--
--   Formalization note: Lean 4 identifier `BookProof.QgPhysicalSectorIdentity.wsum_creIdx`.

-- Generated from ChapterQgPhysicalSectorIdentity.lean — theorem BookProof.QgPhysicalSectorIdentity.wsum_creIdx
import Definitions.Def_ChapterGaugeFixing
import Definitions.Def_ChapterFockQuadraticEsa
import Definitions.Def_ChapterOperatorSeriesEsa
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
import Definitions.Def_ChapterNavierStokesDeficiency
import Definitions.Def_ChapterNavierStokesIkebeKato
import Mathlib
import Definitions.Def_ChapterQgPhysicalSectorIdentity
import Definitions.Def_ChapterA3n
open BookProof.ChapterA3n
open BookProof.QgPhysicalSectorIdentity



open BookProof.GaugeFixing
open BookProof.FockQuadratic
open BookProof.OperatorSeries
open BookProof.FarisLavine
open BookProof.NavierStokesFlow BookProof.NavierStokesFlow.LpNat
open BookProof.NavierStokesFlow.IkebeKato
open scoped ENNReal

variable {F : BiDegree → Type} (S : DerivativeVariableFixingSystem F)
variable {ι : Type*}

theorem BookProof.QgPhysicalSectorIdentity.wsum_creIdx (ω : ι → ℝ) (i : ι) : wsum ω (creIdx i) = ω i := by sorry
