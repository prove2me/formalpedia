-- Prove2me | Theorems.Thm_BookProof_NsBrstDerivativeGauge_genU_ccr_u
-- name    : BookProof.NsBrstDerivativeGauge.genU_ccr_u
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-21T12:05:35.162996+00:00
-- url     : https://prove2.me/theorems/b9ed8017-8f45-4ab2-be24-5bbabb745d4b
-- title:
--   `BookProof.NsBrstDerivativeGauge.genU_ccr_u` (i k : Fin 3) (p : NSAlg) : genU i (X (NSVar.u k) * p) - X (NSVar.u k) * genU i p = if i = k then p else 0
-- statement:
--   Prove the following Lean 4 theorem from `ChapterNsBrstDerivativeGauge`.
--
--   `BookProof.NsBrstDerivativeGauge.genU_ccr_u` (i k : Fin 3) (p : NSAlg) : genU i (X (NSVar.u k) * p) - X (NSVar.u k) * genU i p = if i = k then p else 0
--
--   Formalization note: Lean 4 identifier `BookProof.NsBrstDerivativeGauge.genU_ccr_u`.

-- Generated from ChapterNsBrstDerivativeGauge.lean — theorem BookProof.NsBrstDerivativeGauge.genU_ccr_u
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

theorem BookProof.NsBrstDerivativeGauge.genU_ccr_u (i k : Fin 3) (p : NSAlg) :
    genU i (X (NSVar.u k) * p) - X (NSVar.u k) * genU i p = if i = k then p else 0 := by sorry
