-- Prove2me | Theorems.Thm_BookProof_NsLagrangianDet_phase_sum
-- name    : BookProof.NsLagrangianDet.phase_sum
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-10T07:54:50.259228+00:00
-- url     : https://prove2.me/theorems/89cf3eeb-927c-448e-8f15-0c71ff1f25aa
-- title:
--   `BookProof.NsLagrangianDet.phase_sum` {ι : Type*} (s : Finset ι) (w : ι → Fin 3 → ℝ) (a : Fin 3 → ℝ) : ∏ i ∈ s, phase (w i) a = phase (∑ i ∈ s, w i) a
-- statement:
--   Prove the following Lean 4 theorem from `ChapterNsLagrangianDetConvolution`.
--
--   `BookProof.NsLagrangianDet.phase_sum` {ι : Type*} (s : Finset ι) (w : ι → Fin 3 → ℝ) (a : Fin 3 → ℝ) : ∏ i ∈ s, phase (w i) a = phase (∑ i ∈ s, w i) a
--
--   Formalization note: Lean 4 identifier `BookProof.NsLagrangianDet.phase_sum`.

-- Generated from ChapterNsLagrangianDetConvolution.lean — theorem BookProof.NsLagrangianDet.phase_sum
import Mathlib
import Definitions.Def_ChapterNsLagrangianDetConvolution
open BookProof.NsLagrangianDet



open MvPolynomial Matrix

noncomputable section

variable {K : Type*} [Fintype K]

theorem BookProof.NsLagrangianDet.phase_sum {ι : Type*} (s : Finset ι) (w : ι → Fin 3 → ℝ) (a : Fin 3 → ℝ) :
    ∏ i ∈ s, phase (w i) a = phase (∑ i ∈ s, w i) a := by sorry
