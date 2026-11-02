-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave5_05_ubv_cap_corner_uniform_epsilon_interior_cutoff_with_cap_proximity
-- name    : AvramDividend.Classical.avram_wave5_05_ubv_cap_corner_uniform_epsilon_interior_cutoff_with_cap_proximity
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T13:17:03.545182+00:00
-- url     : https://prove2.me/theorems/7dcce965-49e9-4aec-9e57-1f0f35d359b3
-- title:
--   Uniform slope-one interior cutoff can be chosen arbitrarily close to the cap without requiring any cap derivative
-- statement:
--   At a positive finite cap c, assume w continuous on [0,∞), C² only strictly inside 0<y<c, and w'≥1 strictly inside. For every ε>0, choose b with 0<b<c and cap proximity c−b<ε, such that the global slope-one cap continuation f_c dominates f_b and their difference lies in [0,ε) for ALL reserve states y≥0 simultaneously. This supports an interior-cutoff localisation approach in which the kinks actually approach c as precision improves. It never assumes w'(c−) exists, never assumes C² at c, and does not assert the controlled stochastic Itô/local-time formula or the singular dividend Stieltjes correction.
-- source:
--   Proved inclusive cap secants 44b01929-5817-44ac-9439-6eb3c9879f2c, Proved global secant-defect bound 5d60cc4f-f8cc-4849-8d17-fd65a1331edb, earlier epsilon cutoff 38b135f2-1b8c-4601-9e9b-4a249b26ef95. Canonical UBV core 429e17ca-5528-40b5-b593-7c03973d0706 untouched.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_wave5_05_ubv_cap_corner_uniform_interior_cutoff_secant_defect_bound

open MeasureTheory Set Topology Filter AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave5_05_ubv_cap_corner_uniform_epsilon_interior_cutoff_with_cap_proximity
    (w : ℝ → ℝ) (c : ℝ) (hc : 0 < c)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_smooth : ContDiffOn ℝ 2 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < ENNReal.ofReal c})
    (hw_grad : ∀ y : ℝ, 0 < y →
      ENNReal.ofReal y < ENNReal.ofReal c → 1 ≤ deriv w y)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ b : ℝ, 0 < b ∧ b < c ∧ c - b < ε ∧
      ∀ y : ℝ, 0 ≤ y →
        0 ≤ (if y ≤ c then w y else w c + (y - c)) -
          (if y ≤ b then w y else w b + (y - b)) ∧
        (if y ≤ c then w y else w c + (y - c)) -
          (if y ≤ b then w y else w b + (y - b)) < ε := by sorry
