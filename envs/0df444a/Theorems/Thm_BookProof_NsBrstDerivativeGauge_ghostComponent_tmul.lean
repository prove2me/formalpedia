-- Prove2me | Theorems.Thm_BookProof_NsBrstDerivativeGauge_ghostComponent_tmul
-- name    : BookProof.NsBrstDerivativeGauge.ghostComponent_tmul
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-21T12:08:09.849314+00:00
-- url     : https://prove2.me/theorems/049e131c-8e4e-423f-9879-5ea7f8d8767c
-- title:
--   `BookProof.NsBrstDerivativeGauge.ghostComponent_tmul` (p : NSAlg) (w : nsGhostSpace) : ghostComponent (p ⊗ₜ[ℂ] w) = (MvPolynomial.aeval (fun _ => (0 : ℂ)) p) • w
-- statement:
--   Prove the following Lean 4 theorem from `ChapterNsBrstDerivativeGauge`.
--
--   `BookProof.NsBrstDerivativeGauge.ghostComponent_tmul` (p : NSAlg) (w : nsGhostSpace) : ghostComponent (p ⊗ₜ[ℂ] w) = (MvPolynomial.aeval (fun _ => (0 : ℂ)) p) • w
--
--   Formalization note: Lean 4 identifier `BookProof.NsBrstDerivativeGauge.ghostComponent_tmul`.

-- Generated from ChapterNsBrstDerivativeGauge.lean — theorem BookProof.NsBrstDerivativeGauge.ghostComponent_tmul
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

theorem BookProof.NsBrstDerivativeGauge.ghostComponent_tmul (p : NSAlg) (w : nsGhostSpace) :
    ghostComponent (p ⊗ₜ[ℂ] w) = (MvPolynomial.aeval (fun _ => (0 : ℂ)) p) • w := by sorry
