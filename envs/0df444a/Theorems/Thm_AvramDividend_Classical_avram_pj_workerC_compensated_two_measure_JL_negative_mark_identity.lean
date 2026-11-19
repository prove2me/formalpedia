-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_pj_workerC_compensated_two_measure_JL_negative_mark_identity
-- name    : AvramDividend.Classical.avram_pj_workerC_compensated_two_measure_JL_negative_mark_identity
-- status  : Open
-- author  : @WillR
-- created : 2026-11-19T00:47:04.7817+00:00
-- url     : https://prove2.me/theorems/464d0c7d-4dfc-452d-a258-17bd7186b87e
-- title:
--   Two-measure compensated stopped Lévy J plus annular L combine exactly into one very-small-mark adjusted nonlinear Taylor integral
-- statement:
--   For actual jump-count and time×Lévy compensator measures supported on strictly negative jump marks, each with integrable nonlinear Taylor and annular linear kernels, the compensated nonlinear jump J plus compensated linear L equals the compensated single nonlinear kernel whose first-order subtraction occurs only for z>=-eta. This is the exact two-measure cancellation needed for original stopped purejump physical Ito; no martingale assumptions or zero-measure substitutions.
-- source:
--   Public Proved 97521e90 true negative mark kernel identity, Mathlib integral_add, integration a.e. and ring.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_pj_workerC_negative_mark_JL_cutoff_exact_kernel
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_pj_workerC_compensated_two_measure_JL_negative_mark_identity
    (M N : Measure (ℝ≥0 × ℝ)) (η : ℝ)
    (S d : (ℝ≥0 × ℝ) → ℝ)
    (hη : 0 < η) (hηone : η < 1)
    (hMneg : ∀ᵐ p ∂M, p.2 < 0)
    (hNneg : ∀ᵐ p ∂N, p.2 < 0)
    (hHM : Integrable (fun p => S p -
      (if -1 < p.2 then p.2 * d p else 0)) M)
    (hLM : Integrable (fun p =>
      if p.2 ∈ Ioo (-1 : ℝ) (-η) then p.2 * d p else 0) M)
    (hHN : Integrable (fun p => S p -
      (if -1 < p.2 then p.2 * d p else 0)) N)
    (hLN : Integrable (fun p =>
      if p.2 ∈ Ioo (-1 : ℝ) (-η) then p.2 * d p else 0) N) :
    ((∫ p, S p - (if -1 < p.2 then p.2 * d p else 0) ∂M) -
      (∫ p, S p - (if -1 < p.2 then p.2 * d p else 0) ∂N)) +
    ((∫ p, if p.2 ∈ Ioo (-1 : ℝ) (-η) then p.2 * d p else 0 ∂M) -
      (∫ p, if p.2 ∈ Ioo (-1 : ℝ) (-η) then p.2 * d p else 0 ∂N)) =
    (∫ p, S p - (if -η ≤ p.2 then p.2 * d p else 0) ∂M) -
    (∫ p, S p - (if -η ≤ p.2 then p.2 * d p else 0) ∂N) := by sorry
