-- Prove2me | Theorems.Thm_BookProof_QgPhysicalSectorIdentity_L_gf_constraint_surface
-- name    : BookProof.QgPhysicalSectorIdentity.L_gf_constraint_surface
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-16T23:32:25.347993+00:00
-- url     : https://prove2.me/theorems/7cfe6977-eb9a-4848-83eb-dba2ae09ffae
-- title:
--   `BookProof.QgPhysicalSectorIdentity.L_gf_constraint_surface` (hfix : gaugeField S.toGaugeFixingSystem = S.toGaugeFixingSystem.zero (1, 0)) : S.s (Psi S.toGaugeFixingSystem) = S.sub
-- statement:
--   Prove the following Lean 4 theorem from `ChapterQgPhysicalSectorIdentity`.
--
--   `BookProof.QgPhysicalSectorIdentity.L_gf_constraint_surface` (hfix : gaugeField S.toGaugeFixingSystem = S.toGaugeFixingSystem.zero (1, 0)) : S.s (Psi S.toGaugeFixingSystem) = S.sub (2, 0) (S.zero (2, 0)) (S.mul (1, -1) (1, 1) S.c_bar S.c)
--
--   Formalization note: Lean 4 identifier `BookProof.QgPhysicalSectorIdentity.L_gf_constraint_surface`.

-- Generated from ChapterQgPhysicalSectorIdentity.lean — theorem BookProof.QgPhysicalSectorIdentity.L_gf_constraint_surface
import Definitions.Def_ChapterFockQuadraticEsa
import Definitions.Def_ChapterOperatorSeriesEsa
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
import Definitions.Def_ChapterNavierStokesDeficiency
import Definitions.Def_ChapterNavierStokesIkebeKato
import Mathlib
import Definitions.Def_ChapterQgPhysicalSectorIdentity
import Definitions.Def_ChapterGaugeFixing
import Definitions.Def_ChapterSirkFinitePrecision
open BookProof.GaugeFixing
open BookProof.SirkFinitePrecision
open BookProof.SirkFinitePrecision.CertInterval
open BookProof.QgPhysicalSectorIdentity



open BookProof.GaugeFixing
open BookProof.FockQuadratic
open BookProof.OperatorSeries
open BookProof.FarisLavine
open BookProof.NavierStokesFlow BookProof.NavierStokesFlow.LpNat
open BookProof.NavierStokesFlow.IkebeKato
open scoped ENNReal

variable {F : BiDegree → Type} (S : DerivativeVariableFixingSystem F)

theorem BookProof.QgPhysicalSectorIdentity.L_gf_constraint_surface
    (hfix : gaugeField S.toGaugeFixingSystem = S.toGaugeFixingSystem.zero (1, 0)) :
    S.s (Psi S.toGaugeFixingSystem) =
      S.sub (2, 0) (S.zero (2, 0)) (S.mul (1, -1) (1, 1) S.c_bar S.c) := by sorry
