-- Prove2me | Theorems.Thm_BookProof_NsLagrangianDet_ev_volPot
-- name    : BookProof.NsLagrangianDet.ev_volPot
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-10T07:56:02.373991+00:00
-- url     : https://prove2.me/theorems/6f8e2057-2175-4bc4-915f-a1df4d81aaae
-- title:
--   `BookProof.NsLagrangianDet.ev_volPot` (kappa : ℝ) (kv : K → Fin 3 → ℝ) (y : DIdx K → ℝ) : ev y (volPot kappa kv) = ((kappa / 2 * ∑ q ∈ waveSet kv, Complex.normSq (ev y (volCoef kv
-- statement:
--   Prove the following Lean 4 theorem from `ChapterNsLagrangianDetConvolution`.
--
--   `BookProof.NsLagrangianDet.ev_volPot` (kappa : ℝ) (kv : K → Fin 3 → ℝ) (y : DIdx K → ℝ) : ev y (volPot kappa kv) = ((kappa / 2 * ∑ q ∈ waveSet kv, Complex.normSq (ev y (volCoef kv q)) : ℝ) : ℂ)
--
--   Formalization note: Lean 4 identifier `BookProof.NsLagrangianDet.ev_volPot`.

-- Generated from ChapterNsLagrangianDetConvolution.lean — theorem BookProof.NsLagrangianDet.ev_volPot
import Mathlib
import Definitions.Def_ChapterNsLagrangianDetConvolution
open BookProof.NsLagrangianDet



open MvPolynomial Matrix

noncomputable section

variable {K : Type*} [Fintype K]

theorem BookProof.NsLagrangianDet.ev_volPot (kappa : ℝ) (kv : K → Fin 3 → ℝ) (y : DIdx K → ℝ) :
    ev y (volPot kappa kv)
      = ((kappa / 2 * ∑ q ∈ waveSet kv, Complex.normSq (ev y (volCoef kv q)) : ℝ) : ℂ) := by sorry
