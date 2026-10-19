-- Prove2me | Theorems.Thm_BookProof_QgPhysicalSectorIdentity_coupling_weighted_summable
-- name    : BookProof.QgPhysicalSectorIdentity.coupling_weighted_summable
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-16T23:34:29.695786+00:00
-- url     : https://prove2.me/theorems/5ee8312b-c353-45c8-955b-d4a8ad1343f6
-- title:
--   `BookProof.QgPhysicalSectorIdentity.coupling_weighted_summable` {ω : ι → ℝ} (h : ι × ι → ℂ) (hsum : Summable fun k : ι × ι => ‖h k‖ * (ω k.1 + ω k.2 + 2)) : Summable fun k...
-- statement:
--   Prove the following Lean 4 theorem from `ChapterQgPhysicalSectorIdentity`.
--
--   `BookProof.QgPhysicalSectorIdentity.coupling_weighted_summable` {ω : ι → ℝ} (h : ι × ι → ℂ) (hsum : Summable fun k : ι × ι => ‖h k‖ * (ω k.1 + ω k.2 + 2)) : Summable fun k : ι × ι => ‖h k‖ * (wsum ω (creIdx k.1) + wsum ω (annIdx k.2) + 2)
--
--   Formalization note: Lean 4 identifier `BookProof.QgPhysicalSectorIdentity.coupling_weighted_summable`.

-- Generated from ChapterQgPhysicalSectorIdentity.lean — theorem BookProof.QgPhysicalSectorIdentity.coupling_weighted_summable
import Definitions.Def_ChapterGaugeFixing
import Definitions.Def_ChapterFockQuadraticEsa
import Definitions.Def_ChapterOperatorSeriesEsa
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
import Definitions.Def_ChapterNavierStokesDeficiency
import Definitions.Def_ChapterNavierStokesIkebeKato
import Mathlib
import Definitions.Def_ChapterQgPhysicalSectorIdentity
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

theorem BookProof.QgPhysicalSectorIdentity.coupling_weighted_summable {ω : ι → ℝ} (h : ι × ι → ℂ)
    (hsum : Summable fun k : ι × ι => ‖h k‖ * (ω k.1 + ω k.2 + 2)) :
    Summable fun k : ι × ι => ‖h k‖ * (wsum ω (creIdx k.1) + wsum ω (annIdx k.2) + 2) := by sorry
