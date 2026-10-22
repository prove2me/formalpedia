-- Prove2me | Theorems.Thm_BookProof_NsBrstDerivativeGauge_genU_leibniz
-- name    : BookProof.NsBrstDerivativeGauge.genU_leibniz
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-21T12:05:43.318061+00:00
-- url     : https://prove2.me/theorems/903e0933-ff96-4fdc-9bb5-726ec2419740
-- title:
--   `BookProof.NsBrstDerivativeGauge.genU_leibniz` (i : Fin 3) (p q : NSAlg) : genU i (p * q) = genU i p * q + p * genU i q
-- statement:
--   Prove the following Lean 4 theorem from `ChapterNsBrstDerivativeGauge`.
--
--   `BookProof.NsBrstDerivativeGauge.genU_leibniz` (i : Fin 3) (p q : NSAlg) : genU i (p * q) = genU i p * q + p * genU i q
--
--   Formalization note: Lean 4 identifier `BookProof.NsBrstDerivativeGauge.genU_leibniz`.

-- Generated from ChapterNsBrstDerivativeGauge.lean — theorem BookProof.NsBrstDerivativeGauge.genU_leibniz
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

theorem BookProof.NsBrstDerivativeGauge.genU_leibniz (i : Fin 3) (p q : NSAlg) :
    genU i (p * q) = genU i p * q + p * genU i q := by sorry
