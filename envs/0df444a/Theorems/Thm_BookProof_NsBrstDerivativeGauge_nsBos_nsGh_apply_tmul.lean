-- Prove2me | Theorems.Thm_BookProof_NsBrstDerivativeGauge_nsBos_nsGh_apply_tmul
-- name    : BookProof.NsBrstDerivativeGauge.nsBos_nsGh_apply_tmul
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-21T12:07:33.229922+00:00
-- url     : https://prove2.me/theorems/488d09dc-cb61-4258-b3f8-1515d5f794b2
-- title:
--   `BookProof.NsBrstDerivativeGauge.nsBos_nsGh_apply_tmul` (S : Module.End ℂ NSAlg) (T : Module.End ℂ nsGhostSpace) (p : NSAlg) (w : nsGhostSpace) : (nsBos S * nsGh T) (p ⊗ₜ[ℂ] w) = S
-- statement:
--   Prove the following Lean 4 theorem from `ChapterNsBrstDerivativeGauge`.
--
--   `BookProof.NsBrstDerivativeGauge.nsBos_nsGh_apply_tmul` (S : Module.End ℂ NSAlg) (T : Module.End ℂ nsGhostSpace) (p : NSAlg) (w : nsGhostSpace) : (nsBos S * nsGh T) (p ⊗ₜ[ℂ] w) = S p ⊗ₜ[ℂ] T w
--
--   Formalization note: Lean 4 identifier `BookProof.NsBrstDerivativeGauge.nsBos_nsGh_apply_tmul`.

-- Generated from ChapterNsBrstDerivativeGauge.lean — theorem BookProof.NsBrstDerivativeGauge.nsBos_nsGh_apply_tmul
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

theorem BookProof.NsBrstDerivativeGauge.nsBos_nsGh_apply_tmul (S : Module.End ℂ NSAlg) (T : Module.End ℂ nsGhostSpace)
    (p : NSAlg) (w : nsGhostSpace) :
    (nsBos S * nsGh T) (p ⊗ₜ[ℂ] w) = S p ⊗ₜ[ℂ] T w := by sorry
