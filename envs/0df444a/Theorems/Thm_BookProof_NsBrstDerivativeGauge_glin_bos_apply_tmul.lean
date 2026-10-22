-- Prove2me | Theorems.Thm_BookProof_NsBrstDerivativeGauge_glin_bos_apply_tmul
-- name    : BookProof.NsBrstDerivativeGauge.glin_bos_apply_tmul
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-21T12:08:10.973282+00:00
-- url     : https://prove2.me/theorems/699880da-7f44-49d9-a11c-310ab29d2fdf
-- title:
--   `BookProof.NsBrstDerivativeGauge.glin_bos_apply_tmul` (G : Fin 3 → Module.End ℂ NSAlg) (p : NSAlg) (w : nsGhostSpace) : glin (fun j => nsBos (G j)) nsChi (p ⊗ₜ[ℂ] w) = ∑ j : Fin 3,
-- statement:
--   Prove the following Lean 4 theorem from `ChapterNsBrstDerivativeGauge`.
--
--   `BookProof.NsBrstDerivativeGauge.glin_bos_apply_tmul` (G : Fin 3 → Module.End ℂ NSAlg) (p : NSAlg) (w : nsGhostSpace) : glin (fun j => nsBos (G j)) nsChi (p ⊗ₜ[ℂ] w) = ∑ j : Fin 3, G j p ⊗ₜ[ℂ] nsGhostCre j w
--
--   Formalization note: Lean 4 identifier `BookProof.NsBrstDerivativeGauge.glin_bos_apply_tmul`.

-- Generated from ChapterNsBrstDerivativeGauge.lean — theorem BookProof.NsBrstDerivativeGauge.glin_bos_apply_tmul
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

theorem BookProof.NsBrstDerivativeGauge.glin_bos_apply_tmul (G : Fin 3 → Module.End ℂ NSAlg) (p : NSAlg) (w : nsGhostSpace) :
    glin (fun j => nsBos (G j)) nsChi (p ⊗ₜ[ℂ] w)
      = ∑ j : Fin 3, G j p ⊗ₜ[ℂ] nsGhostCre j w := by sorry
