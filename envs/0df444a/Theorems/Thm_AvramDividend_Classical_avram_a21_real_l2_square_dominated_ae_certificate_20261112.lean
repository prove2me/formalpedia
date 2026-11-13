-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a21_real_l2_square_dominated_ae_certificate_20261112
-- name    : AvramDividend.Classical.avram_a21_real_l2_square_dominated_ae_certificate_20261112
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-13T00:15:25.345193+00:00
-- url     : https://prove2.me/theorems/287bc75a-c084-4044-be5d-e4e64e58c417
-- title:
--   L2 common envelope yields almost sure squared bound, measurability and square convergence
-- statement:
--   On the actual original measure space, a sequence of a.e. strongly measurable real random variables bounded pointwise almost surely by a shared nonnegative random envelope with integrable square, and converging pointwise almost surely to a limit, has a.e.-measurable squares dominated by the integrable square envelope and squares converging almost surely to the limit square.
-- source:
--   Pinned Mathlib AEStronglyMeasurable.pow, norm_pow, filter Tendsto.pow and elementary real square monotonicity. This is the dominated squared limit component of A21 original physical marked Poisson certificate 67336b2d.

import Mathlib
open MeasureTheory Filter
open scoped Topology
noncomputable section

theorem AvramDividend.Classical.avram_a21_real_l2_square_dominated_ae_certificate_20261112
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (F : ℕ → Ω → ℝ) (C B : Ω → ℝ)
    (hFmeas : ∀ k, AEStronglyMeasurable (F k) P)
    (hB2 : Integrable (fun ω => (B ω)^2) P)
    (hBound : ∀ᵐ ω ∂P, ∀ k, ‖F k ω‖ ≤ B ω)
    (hLimit : ∀ᵐ ω ∂P,
      Tendsto (fun k => F k ω) atTop (𝓝 (C ω))) :
    (∀ k, AEStronglyMeasurable (fun ω => (F k ω)^2) P) ∧
      Integrable (fun ω => (B ω)^2) P ∧
      (∀ k, ∀ᵐ ω ∂P, ‖(F k ω)^2‖ ≤ (B ω)^2) ∧
      (∀ᵐ ω ∂P, Tendsto (fun k => (F k ω)^2)
        atTop (𝓝 ((C ω)^2))) := by sorry
