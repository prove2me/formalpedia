-- Prove2me | Theorems.Thm_BookProof_QgPhysicalSectorIdentity_wsum_annIdx
-- name    : BookProof.QgPhysicalSectorIdentity.wsum_annIdx
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-16T23:34:04.430975+00:00
-- url     : https://prove2.me/theorems/dc8423a7-a6dc-4a1f-a113-10130f1f57ac
-- title:
--   `BookProof.QgPhysicalSectorIdentity.wsum_annIdx` (ω : ι → ℝ) (j : ι) : wsum ω (annIdx j) = ω j
-- statement:
--   Prove the following Lean 4 theorem from `ChapterQgPhysicalSectorIdentity`.
--
--   `BookProof.QgPhysicalSectorIdentity.wsum_annIdx` (ω : ι → ℝ) (j : ι) : wsum ω (annIdx j) = ω j
--
--   Formalization note: Lean 4 identifier `BookProof.QgPhysicalSectorIdentity.wsum_annIdx`.

-- Generated from ChapterQgPhysicalSectorIdentity.lean — theorem BookProof.QgPhysicalSectorIdentity.wsum_annIdx
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

theorem BookProof.QgPhysicalSectorIdentity.wsum_annIdx (ω : ι → ℝ) (j : ι) : wsum ω (annIdx j) = ω j := by sorry
