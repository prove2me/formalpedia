-- Prove2me | Theorems.Thm_BookProof_NsBrstDerivativeGauge_genU_ccr_x
-- name    : BookProof.NsBrstDerivativeGauge.genU_ccr_x
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-21T12:05:32.355559+00:00
-- url     : https://prove2.me/theorems/0a8e60ec-20c7-4bf1-97b2-893e433e7357
-- title:
--   `BookProof.NsBrstDerivativeGauge.genU_ccr_x` (i k : Fin 3) (p : NSAlg) : genU i (X (NSVar.x k) * p) - X (NSVar.x k) * genU i p = 0
-- statement:
--   Prove the following Lean 4 theorem from `ChapterNsBrstDerivativeGauge`.
--
--   `BookProof.NsBrstDerivativeGauge.genU_ccr_x` (i k : Fin 3) (p : NSAlg) : genU i (X (NSVar.x k) * p) - X (NSVar.x k) * genU i p = 0
--
--   Formalization note: Lean 4 identifier `BookProof.NsBrstDerivativeGauge.genU_ccr_x`.

-- Generated from ChapterNsBrstDerivativeGauge.lean — theorem BookProof.NsBrstDerivativeGauge.genU_ccr_x
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

theorem BookProof.NsBrstDerivativeGauge.genU_ccr_x (i k : Fin 3) (p : NSAlg) :
    genU i (X (NSVar.x k) * p) - X (NSVar.x k) * genU i p = 0 := by sorry
