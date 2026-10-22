-- Prove2me | Theorems.Thm_BookProof_NsBrstDerivativeGauge_genU_nsSymbol
-- name    : BookProof.NsBrstDerivativeGauge.genU_nsSymbol
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-21T12:05:39.521292+00:00
-- url     : https://prove2.me/theorems/d8dcd630-aa75-4056-8da3-a85614747149
-- title:
--   `BookProof.NsBrstDerivativeGauge.genU_nsSymbol` (nu : ℂ) (i m : Fin 3) : genU m (nsSymbol nu i) = X (NSVar.uD i m)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterNsBrstDerivativeGauge`.
--
--   `BookProof.NsBrstDerivativeGauge.genU_nsSymbol` (nu : ℂ) (i m : Fin 3) : genU m (nsSymbol nu i) = X (NSVar.uD i m)
--
--   Formalization note: Lean 4 identifier `BookProof.NsBrstDerivativeGauge.genU_nsSymbol`.

-- Generated from ChapterNsBrstDerivativeGauge.lean — theorem BookProof.NsBrstDerivativeGauge.genU_nsSymbol
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

theorem BookProof.NsBrstDerivativeGauge.genU_nsSymbol (nu : ℂ) (i m : Fin 3) :
    genU m (nsSymbol nu i) = X (NSVar.uD i m) := by sorry
