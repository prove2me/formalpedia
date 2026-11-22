-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_twoagentA_public_original_physical_compensated_mark_finitebin_pathwise_bound_20261122
-- name    : AvramDividend.Classical.avram_twoagentA_public_original_physical_compensated_mark_finitebin_pathwise_bound_20261122
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-22T14:19:45.570706+00:00
-- url     : https://prove2.me/theorems/ebe8f57e-d66d-4760-b421-36c2e1412ba6
-- title:
--   Original true finite-band signed mark compensated count error bridge 2
-- statement:
--   Republish exact accepted physically marked signed-jump original-X finite reciprocal negative-band vs compensation and count-proxy error proof after replacing all private worker dependencies with equivalent Proved public original-X proof declarations.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_twoagentA_public_original_finite_reciprocal_mark_vs_count_error_20261122
import Theorems.Thm_AvramDividend_Classical_avram_twoagentA_public_original_levy_compensator_finite_reciprocal_band_error_20261122
import Theorems.Thm_AvramDividend_Classical_avram_twoagentA_public_finite_count_proxy_compensated_signed_error_triangle_20261122
open MeasureTheory Set AvramDividend.Classical
open scoped Classical NNReal ENNReal
noncomputable section
set_option autoImplicit false

theorem AvramDividend.Classical.avram_twoagentA_public_original_physical_compensated_mark_finitebin_pathwise_bound_20261122
    (μ : Measure (ℝ≥0 × ℝ)) (ν : Measure ℝ) (T : ℝ≥0)
    (n m : ℕ) (hnm : n ≤ m)
    (hMono : Monotone (fun i : ℕ => -(1 / ((i : ℝ) + 1))))
    (hμFin : μ (Ioc 0 T ×ˢ Ioc
      (-(1 / ((n : ℝ) + 1))) (-(1 / ((m : ℝ) + 1)))) < ⊤)
    (hμInt : IntegrableOn (fun p : ℝ≥0 × ℝ => p.2)
      (Ioc 0 T ×ˢ Ioc
        (-(1 / ((n : ℝ) + 1))) (-(1 / ((m : ℝ) + 1)))) μ)
    (hνFin : ∀ i ∈ Finset.Ico n m,
      ν (Ioc (-(1 / ((i : ℝ) + 1))) (-(1 / ((i : ℝ) + 2)))) < ⊤)
    (hνInt : IntegrableOn (fun z : ℝ => z)
      (Ioc (-(1 / ((n : ℝ) + 1))) (-(1 / ((m : ℝ) + 1)))) ν) :
    let B : Set ℝ :=
      Ioc (-(1 / ((n : ℝ) + 1))) (-(1 / ((m : ℝ) + 1)))
    let A : ℕ → Set ℝ := fun i =>
      Ioc (-(1 / ((i : ℝ) + 1))) (-(1 / ((i : ℝ) + 2)))
    let c : ℕ → ℝ := fun i => -(1 / ((i : ℝ) + 1))
    let δ : ℕ → ℝ := fun i =>
      1 / ((i : ℝ) + 1) - 1 / ((i : ℝ) + 2)
    let N : ℕ → ℝ := fun i =>
      (μ (Ioc 0 T ×ˢ A i)).toReal
    let rate : ℕ → ℝ := fun i => (ν (A i)).toReal
    let U : ℝ := ∫ p in Ioc 0 T ×ˢ B, p.2 ∂μ
    let V : ℝ := ∫ z in B, z ∂ν
    |(U - (T : ℝ) * V) -
      ∑ i ∈ Finset.Ico n m,
        c i * (N i - (T : ℝ) * rate i)| ≤
      ∑ i ∈ Finset.Ico n m,
        δ i * (N i + (T : ℝ) * rate i) := by sorry
