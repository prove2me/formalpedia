-- Prove2me | Theorems.Thm_BookProof_NsBrstDerivativeGauge_pderiv_u_mul_uL
-- name    : BookProof.NsBrstDerivativeGauge.pderiv_u_mul_uL
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-21T12:06:00.47264+00:00
-- url     : https://prove2.me/theorems/4c316a67-0673-4a86-ad3c-4fa557619022
-- title:
--   `BookProof.NsBrstDerivativeGauge.pderiv_u_mul_uL` (m i : Fin 3) (q : NSAlg) : pderiv (NSVar.u m) (X (NSVar.uL i) * q) = X (NSVar.uL i) * pderiv (NSVar.u m) q
-- statement:
--   Prove the following Lean 4 theorem from `ChapterNsBrstDerivativeGauge`.
--
--   `BookProof.NsBrstDerivativeGauge.pderiv_u_mul_uL` (m i : Fin 3) (q : NSAlg) : pderiv (NSVar.u m) (X (NSVar.uL i) * q) = X (NSVar.uL i) * pderiv (NSVar.u m) q
--
--   Formalization note: Lean 4 identifier `BookProof.NsBrstDerivativeGauge.pderiv_u_mul_uL`.

-- Generated from ChapterNsBrstDerivativeGauge.lean — theorem BookProof.NsBrstDerivativeGauge.pderiv_u_mul_uL
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

theorem BookProof.NsBrstDerivativeGauge.pderiv_u_mul_uL (m i : Fin 3) (q : NSAlg) :
    pderiv (NSVar.u m) (X (NSVar.uL i) * q) = X (NSVar.uL i) * pderiv (NSVar.u m) q := by sorry
