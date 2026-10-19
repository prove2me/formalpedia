-- Prove2me | Theorems.Thm_BookProof_QgPhysicalSectorIdentity_int_L_gf_eq_zero_physical
-- name    : BookProof.QgPhysicalSectorIdentity.int_L_gf_eq_zero_physical
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-16T23:32:48.877644+00:00
-- url     : https://prove2.me/theorems/b1a672fd-4a60-4681-9e23-c3929198512e
-- title:
--   `BookProof.QgPhysicalSectorIdentity.int_L_gf_eq_zero_physical` (I : BrstIntegral S.toGaugeFixingSystem) : I.int (sTop S.toGaugeFixingSystem (Psi S.toGaugeFixingSystem)) = 0
-- statement:
--   Prove the following Lean 4 theorem from `ChapterQgPhysicalSectorIdentity`.
--
--   `BookProof.QgPhysicalSectorIdentity.int_L_gf_eq_zero_physical` (I : BrstIntegral S.toGaugeFixingSystem) : I.int (sTop S.toGaugeFixingSystem (Psi S.toGaugeFixingSystem)) = 0
--
--   Formalization note: Lean 4 identifier `BookProof.QgPhysicalSectorIdentity.int_L_gf_eq_zero_physical`.

-- Generated from ChapterQgPhysicalSectorIdentity.lean — theorem BookProof.QgPhysicalSectorIdentity.int_L_gf_eq_zero_physical
import Definitions.Def_ChapterFockQuadraticEsa
import Definitions.Def_ChapterOperatorSeriesEsa
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
import Definitions.Def_ChapterNavierStokesDeficiency
import Definitions.Def_ChapterNavierStokesIkebeKato
import Mathlib
import Definitions.Def_ChapterQgPhysicalSectorIdentity
import Definitions.Def_ChapterGaugeFixing
open BookProof.GaugeFixing
open BookProof.QgPhysicalSectorIdentity



open BookProof.GaugeFixing
open BookProof.FockQuadratic
open BookProof.OperatorSeries
open BookProof.FarisLavine
open BookProof.NavierStokesFlow BookProof.NavierStokesFlow.LpNat
open BookProof.NavierStokesFlow.IkebeKato
open scoped ENNReal

variable {F : BiDegree → Type} (S : DerivativeVariableFixingSystem F)

theorem BookProof.QgPhysicalSectorIdentity.int_L_gf_eq_zero_physical (I : BrstIntegral S.toGaugeFixingSystem) :
    I.int (sTop S.toGaugeFixingSystem (Psi S.toGaugeFixingSystem)) = 0 := by sorry
