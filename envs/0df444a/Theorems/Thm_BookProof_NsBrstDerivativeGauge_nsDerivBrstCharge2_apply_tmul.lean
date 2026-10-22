-- Prove2me | Theorems.Thm_BookProof_NsBrstDerivativeGauge_nsDerivBrstCharge2_apply_tmul
-- name    : BookProof.NsBrstDerivativeGauge.nsDerivBrstCharge2_apply_tmul
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-21T12:08:25.42603+00:00
-- url     : https://prove2.me/theorems/be4b19b1-f546-44fb-b5e8-54034291f4d9
-- title:
--   `BookProof.NsBrstDerivativeGauge.nsDerivBrstCharge2_apply_tmul` (p : NSAlg) (w : nsGhostSpace) : nsDerivBrstCharge2 (p ⊗ₜ[ℂ] w) = ∑ j : Fin 3, genY2 j p ⊗ₜ[ℂ] nsGhostCre j w
-- statement:
--   Prove the following Lean 4 theorem from `ChapterNsBrstDerivativeGauge`.
--
--   `BookProof.NsBrstDerivativeGauge.nsDerivBrstCharge2_apply_tmul` (p : NSAlg) (w : nsGhostSpace) : nsDerivBrstCharge2 (p ⊗ₜ[ℂ] w) = ∑ j : Fin 3, genY2 j p ⊗ₜ[ℂ] nsGhostCre j w
--
--   Formalization note: Lean 4 identifier `BookProof.NsBrstDerivativeGauge.nsDerivBrstCharge2_apply_tmul`.

-- Generated from ChapterNsBrstDerivativeGauge.lean — theorem BookProof.NsBrstDerivativeGauge.nsDerivBrstCharge2_apply_tmul
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

theorem BookProof.NsBrstDerivativeGauge.nsDerivBrstCharge2_apply_tmul (p : NSAlg) (w : nsGhostSpace) :
    nsDerivBrstCharge2 (p ⊗ₜ[ℂ] w) = ∑ j : Fin 3, genY2 j p ⊗ₜ[ℂ] nsGhostCre j w := by sorry
