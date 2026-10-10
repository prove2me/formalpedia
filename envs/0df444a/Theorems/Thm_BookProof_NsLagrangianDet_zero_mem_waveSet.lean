-- Prove2me | Theorems.Thm_BookProof_NsLagrangianDet_zero_mem_waveSet
-- name    : BookProof.NsLagrangianDet.zero_mem_waveSet
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-10T07:55:45.192318+00:00
-- url     : https://prove2.me/theorems/21318fcf-7bce-4437-8fee-4a2528ec06ed
-- title:
--   `BookProof.NsLagrangianDet.zero_mem_waveSet` (kv : K → Fin 3 → ℝ) : (0 : Fin 3 → ℝ) ∈ waveSet kv
-- statement:
--   Prove the following Lean 4 theorem from `ChapterNsLagrangianDetConvolution`.
--
--   `BookProof.NsLagrangianDet.zero_mem_waveSet` (kv : K → Fin 3 → ℝ) : (0 : Fin 3 → ℝ) ∈ waveSet kv
--
--   Formalization note: Lean 4 identifier `BookProof.NsLagrangianDet.zero_mem_waveSet`.

-- Generated from ChapterNsLagrangianDetConvolution.lean — theorem BookProof.NsLagrangianDet.zero_mem_waveSet
import Mathlib
import Definitions.Def_ChapterNsLagrangianDetConvolution
open BookProof.NsLagrangianDet



open MvPolynomial Matrix

noncomputable section

variable {K : Type*} [Fintype K]

theorem BookProof.NsLagrangianDet.zero_mem_waveSet (kv : K → Fin 3 → ℝ) : (0 : Fin 3 → ℝ) ∈ waveSet kv := by sorry
