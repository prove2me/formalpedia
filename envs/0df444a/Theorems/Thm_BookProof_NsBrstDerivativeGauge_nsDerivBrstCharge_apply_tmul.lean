-- Prove2me | Theorems.Thm_BookProof_NsBrstDerivativeGauge_nsDerivBrstCharge_apply_tmul
-- name    : BookProof.NsBrstDerivativeGauge.nsDerivBrstCharge_apply_tmul
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-21T12:08:12.304993+00:00
-- url     : https://prove2.me/theorems/da68b14d-3a05-445f-8034-5c485cd22cc2
-- title:
--   `BookProof.NsBrstDerivativeGauge.nsDerivBrstCharge_apply_tmul` (p : NSAlg) (w : nsGhostSpace) : nsDerivBrstCharge (p ⊗ₜ[ℂ] w) = ∑ j : Fin 3, genY j p ⊗ₜ[ℂ] nsGhostCre j w
-- statement:
--   Prove the following Lean 4 theorem from `ChapterNsBrstDerivativeGauge`.
--
--   `BookProof.NsBrstDerivativeGauge.nsDerivBrstCharge_apply_tmul` (p : NSAlg) (w : nsGhostSpace) : nsDerivBrstCharge (p ⊗ₜ[ℂ] w) = ∑ j : Fin 3, genY j p ⊗ₜ[ℂ] nsGhostCre j w
--
--   Formalization note: Lean 4 identifier `BookProof.NsBrstDerivativeGauge.nsDerivBrstCharge_apply_tmul`.

-- Generated from ChapterNsBrstDerivativeGauge.lean — theorem BookProof.NsBrstDerivativeGauge.nsDerivBrstCharge_apply_tmul
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

theorem BookProof.NsBrstDerivativeGauge.nsDerivBrstCharge_apply_tmul (p : NSAlg) (w : nsGhostSpace) :
    nsDerivBrstCharge (p ⊗ₜ[ℂ] w) = ∑ j : Fin 3, genY j p ⊗ₜ[ℂ] nsGhostCre j w := by sorry
