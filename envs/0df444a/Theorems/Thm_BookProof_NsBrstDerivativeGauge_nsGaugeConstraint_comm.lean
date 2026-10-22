-- Prove2me | Theorems.Thm_BookProof_NsBrstDerivativeGauge_nsGaugeConstraint_comm
-- name    : BookProof.NsBrstDerivativeGauge.nsGaugeConstraint_comm
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-21T12:06:49.479473+00:00
-- url     : https://prove2.me/theorems/279b8c1f-71f9-4cb2-b864-7783bd6712c6
-- title:
--   `BookProof.NsBrstDerivativeGauge.nsGaugeConstraint_comm` (j k : Fin 3) : nsGaugeConstraint j * nsGaugeConstraint k = nsGaugeConstraint k * nsGaugeConstraint j
-- statement:
--   Prove the following Lean 4 theorem from `ChapterNsBrstDerivativeGauge`.
--
--   `BookProof.NsBrstDerivativeGauge.nsGaugeConstraint_comm` (j k : Fin 3) : nsGaugeConstraint j * nsGaugeConstraint k = nsGaugeConstraint k * nsGaugeConstraint j
--
--   Formalization note: Lean 4 identifier `BookProof.NsBrstDerivativeGauge.nsGaugeConstraint_comm`.

-- Generated from ChapterNsBrstDerivativeGauge.lean — theorem BookProof.NsBrstDerivativeGauge.nsGaugeConstraint_comm
import Definitions.Def_ChapterBRSTNilpotent
import Definitions.Def_ChapterQuantumGravityBrstCharge
import Definitions.Def_ChapterNavierStokesGaugeY2
import Mathlib
import Definitions.Def_ChapterNsBrstDerivativeGauge
import Definitions.Def_ChapterNavierStokesGaugeY
open BookProof.NavierStokesGaugeY
open BookProof.NsBrstDerivativeGauge



open MvPolynomial BookProof.BRSTNilpotent BookProof.QuantumGravityBrstCharge
open BookProof.NavierStokesGaugeY BookProof.NavierStokesGaugeY2

noncomputable section

theorem BookProof.NsBrstDerivativeGauge.nsGaugeConstraint_comm (j k : Fin 3) :
    nsGaugeConstraint j * nsGaugeConstraint k = nsGaugeConstraint k * nsGaugeConstraint j := by sorry
