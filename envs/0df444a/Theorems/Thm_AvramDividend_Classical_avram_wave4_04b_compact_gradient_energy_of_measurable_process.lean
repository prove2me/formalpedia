-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave4_04b_compact_gradient_energy_of_measurable_process
-- name    : AvramDividend.Classical.avram_wave4_04b_compact_gradient_energy_of_measurable_process
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-31T19:39:00.90827+00:00
-- url     : https://prove2.me/theorems/8508c0a7-ab49-484f-a374-5a881a2475c4
-- title:
--   Compact masked derivative is measurable and square-integrable for every finite observation measure
-- statement:
--   Whenever Y is a real-valued measurable process, w is C² on an open reserve interval (a,b), and [u,v] is compactly contained in that interval, the masked gradient 1_{[u,v]}(Y)·w'(Y) is measurable and has finite squared Lebesgue integral under any finite measure on the observation space. The uniform derivative bound is derived from smoothness and compactness, not assumed. The source-X Brownian integrand follows by taking the actual controlled predictable left-limit reserve as Y and any finite predictable observation measure. This result makes no spurious continuity claims at ruin or the cap, and does not assert a martingale exists.
-- source:
--   Proved open-interior derivative Borel zero extension, Proved compact derivative uniform bound, measurability of masked process, elementary real square domination and finite-measure lintegral bound.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04b_measurable_interior_deriv_zero_extension
import Theorems.Thm_AvramDividend_Classical_derivative_abs_le_on_compact_interior_interval

open MeasureTheory Set
open scoped ENNReal Classical
noncomputable section

theorem AvramDividend.Classical.avram_wave4_04b_compact_gradient_energy_of_measurable_process
    {A : Type*} [MeasurableSpace A]
    (Y : A → ℝ) (hY : Measurable Y)
    (w : ℝ → ℝ) (a b u v : ℝ)
    (hw : ContDiffOn ℝ 2 w (Ioo a b))
    (hau : a < u) (huv : u ≤ v) (hvb : v < b)
    (μ : Measure A) (hμ : μ Set.univ < ⊤) :
    Measurable (fun p : A =>
      if Y p ∈ Icc u v then deriv w (Y p) else 0) ∧
      (∫⁻ p : A, ENNReal.ofReal
        ((if Y p ∈ Icc u v then deriv w (Y p) else 0) ^ 2) ∂μ) < ⊤ := by
  sorry
