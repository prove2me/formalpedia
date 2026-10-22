-- Prove2me | Theorems.Thm_BookProof_NsBrstDerivativeGauge_nsHamiltonian2_mapsTo_ker
-- name    : BookProof.NsBrstDerivativeGauge.nsHamiltonian2_mapsTo_ker
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-21T12:07:48.033898+00:00
-- url     : https://prove2.me/theorems/7ec41827-b8dc-4bbf-a2d4-22122e6e8191
-- title:
--   `BookProof.NsBrstDerivativeGauge.nsHamiltonian2_mapsTo_ker` (nu : ℂ) {v : NSGraded} (hv : nsDerivBrstCharge2 v = 0) : nsDerivBrstCharge2 (nsHamiltonian2 nu v) = 0
-- statement:
--   Prove the following Lean 4 theorem from `ChapterNsBrstDerivativeGauge`.
--
--   `BookProof.NsBrstDerivativeGauge.nsHamiltonian2_mapsTo_ker` (nu : ℂ) {v : NSGraded} (hv : nsDerivBrstCharge2 v = 0) : nsDerivBrstCharge2 (nsHamiltonian2 nu v) = 0
--
--   Formalization note: Lean 4 identifier `BookProof.NsBrstDerivativeGauge.nsHamiltonian2_mapsTo_ker`.

-- Generated from ChapterNsBrstDerivativeGauge.lean — theorem BookProof.NsBrstDerivativeGauge.nsHamiltonian2_mapsTo_ker
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

theorem BookProof.NsBrstDerivativeGauge.nsHamiltonian2_mapsTo_ker (nu : ℂ) {v : NSGraded} (hv : nsDerivBrstCharge2 v = 0) :
    nsDerivBrstCharge2 (nsHamiltonian2 nu v) = 0 := by sorry
