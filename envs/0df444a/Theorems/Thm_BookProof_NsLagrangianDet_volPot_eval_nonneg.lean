-- Prove2me | Theorems.Thm_BookProof_NsLagrangianDet_volPot_eval_nonneg
-- name    : BookProof.NsLagrangianDet.volPot_eval_nonneg
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-10T07:56:21.094718+00:00
-- url     : https://prove2.me/theorems/663ecee8-0c6e-420f-b05b-51626757afba
-- title:
--   `BookProof.NsLagrangianDet.volPot_eval_nonneg` {kappa : ℝ} (hk : 0 ≤ kappa) (kv : K → Fin 3 → ℝ) (y : DIdx K → ℝ) : 0 ≤ (ev y (volPot kappa kv)).re
-- statement:
--   Prove the following Lean 4 theorem from `ChapterNsLagrangianDetConvolution`.
--
--   `BookProof.NsLagrangianDet.volPot_eval_nonneg` {kappa : ℝ} (hk : 0 ≤ kappa) (kv : K → Fin 3 → ℝ) (y : DIdx K → ℝ) : 0 ≤ (ev y (volPot kappa kv)).re
--
--   Formalization note: Lean 4 identifier `BookProof.NsLagrangianDet.volPot_eval_nonneg`.

-- Generated from ChapterNsLagrangianDetConvolution.lean — theorem BookProof.NsLagrangianDet.volPot_eval_nonneg
import Mathlib
import Definitions.Def_ChapterNsLagrangianDetConvolution
open BookProof.NsLagrangianDet



open MvPolynomial Matrix

noncomputable section

variable {K : Type*} [Fintype K]

theorem BookProof.NsLagrangianDet.volPot_eval_nonneg {kappa : ℝ} (hk : 0 ≤ kappa) (kv : K → Fin 3 → ℝ)
    (y : DIdx K → ℝ) : 0 ≤ (ev y (volPot kappa kv)).re := by sorry
