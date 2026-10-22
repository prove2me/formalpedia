-- Prove2me | Theorems.Thm_BookProof_NsBrstDerivativeGauge_nsHamAlg_one
-- name    : BookProof.NsBrstDerivativeGauge.nsHamAlg_one
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-21T12:06:40.701631+00:00
-- url     : https://prove2.me/theorems/9bd84019-217e-47e4-bd60-d4bea7d5fdfe
-- title:
--   `BookProof.NsBrstDerivativeGauge.nsHamAlg_one` (nu : ℂ) : nsHamAlg nu 1 = ∑ i : Fin 3, X (NSVar.uD i i)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterNsBrstDerivativeGauge`.
--
--   `BookProof.NsBrstDerivativeGauge.nsHamAlg_one` (nu : ℂ) : nsHamAlg nu 1 = ∑ i : Fin 3, X (NSVar.uD i i)
--
--   Formalization note: Lean 4 identifier `BookProof.NsBrstDerivativeGauge.nsHamAlg_one`.

-- Generated from ChapterNsBrstDerivativeGauge.lean — theorem BookProof.NsBrstDerivativeGauge.nsHamAlg_one
import Definitions.Def_ChapterBRSTNilpotent
import Definitions.Def_ChapterQuantumGravityBrstCharge
import Definitions.Def_ChapterNavierStokesGaugeY2
import Mathlib
import Definitions.Def_ChapterNsBrstDerivativeGauge
import Definitions.Def_ChapterF7
import Definitions.Def_ChapterNavierStokesGaugeY
open BookProof.ChapterF7
open BookProof.NavierStokesGaugeY
open BookProof.NsBrstDerivativeGauge



open MvPolynomial BookProof.BRSTNilpotent BookProof.QuantumGravityBrstCharge
open BookProof.NavierStokesGaugeY BookProof.NavierStokesGaugeY2

noncomputable section

theorem BookProof.NsBrstDerivativeGauge.nsHamAlg_one (nu : ℂ) : nsHamAlg nu 1 = ∑ i : Fin 3, X (NSVar.uD i i) := by sorry
