-- Prove2me | Theorems.Thm_BookProof_NsBrstDerivativeGauge_nsGaugeConstraint2_comm
-- name    : BookProof.NsBrstDerivativeGauge.nsGaugeConstraint2_comm
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-21T12:07:06.900114+00:00
-- url     : https://prove2.me/theorems/626d8069-443c-4cc9-b6b4-62c3f5f57a13
-- title:
--   `BookProof.NsBrstDerivativeGauge.nsGaugeConstraint2_comm` (j k : Fin 3) : nsGaugeConstraint2 j * nsGaugeConstraint2 k = nsGaugeConstraint2 k * nsGaugeConstraint2 j
-- statement:
--   Prove the following Lean 4 theorem from `ChapterNsBrstDerivativeGauge`.
--
--   `BookProof.NsBrstDerivativeGauge.nsGaugeConstraint2_comm` (j k : Fin 3) : nsGaugeConstraint2 j * nsGaugeConstraint2 k = nsGaugeConstraint2 k * nsGaugeConstraint2 j
--
--   Formalization note: Lean 4 identifier `BookProof.NsBrstDerivativeGauge.nsGaugeConstraint2_comm`.

-- Generated from ChapterNsBrstDerivativeGauge.lean — theorem BookProof.NsBrstDerivativeGauge.nsGaugeConstraint2_comm
import Definitions.Def_ChapterBRSTNilpotent
import Definitions.Def_ChapterQuantumGravityBrstCharge
import Mathlib
import Definitions.Def_ChapterNsBrstDerivativeGauge
import Definitions.Def_ChapterNavierStokesGaugeY
import Definitions.Def_ChapterNavierStokesGaugeY2
open BookProof.NavierStokesGaugeY
open BookProof.NavierStokesGaugeY2
open BookProof.NsBrstDerivativeGauge



open MvPolynomial BookProof.BRSTNilpotent BookProof.QuantumGravityBrstCharge
open BookProof.NavierStokesGaugeY BookProof.NavierStokesGaugeY2

noncomputable section

theorem BookProof.NsBrstDerivativeGauge.nsGaugeConstraint2_comm (j k : Fin 3) :
    nsGaugeConstraint2 j * nsGaugeConstraint2 k
      = nsGaugeConstraint2 k * nsGaugeConstraint2 j := by sorry
