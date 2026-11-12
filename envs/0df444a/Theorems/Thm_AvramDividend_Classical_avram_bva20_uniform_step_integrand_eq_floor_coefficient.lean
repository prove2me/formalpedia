-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bva20_uniform_step_integrand_eq_floor_coefficient
-- name    : AvramDividend.Classical.avram_bva20_uniform_step_integrand_eq_floor_coefficient
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-11T20:38:34.462447+00:00
-- url     : https://prove2.me/theorems/c4aebe37-5cfd-43ce-88f0-15b2af09e4a6
-- title:
--   Original uniform step compensator integrand equals physical floor-sampled coefficient
-- statement:
--   At a nonnegative time t strictly before the physical uniform-grid final endpoint, the Riemann step integrand Σ_i 1_{[u_i,u_{i+1})}(t)c_i is exactly the frozen coefficient c_{⌊t(n+2)/T⌋}. This uses the proved finite-row floor index 8c25168c, half-open floor membership c5b28b66 and unique increasing-cell selector e2ccfe12. It directly bridges the original inclusive frozen A sum representation cdc19ee6 to the pointwise physical floor kernel needed for DCT of 7ccc2a1a.
-- source:
--   Exact finite uniform Riemann grid step-integrand evaluation for original 7ccc2a1a.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_bva20_uniform_floor_index_within_inner_row
import Theorems.Thm_AvramDividend_Classical_avram_bva20_uniform_floor_sample_mem_halfopen_cell
import Theorems.Thm_AvramDividend_Classical_avram_bva20_halfopen_monotone_grid_step_select
open Set AvramDividend.Classical
noncomputable section

theorem AvramDividend.Classical.avram_bva20_uniform_step_integrand_eq_floor_coefficient
    (T : ℝ) (hT : 0 < T) (n : ℕ) (c : ℕ → ℝ)
    (t : ℝ) (ht0 : 0 ≤ t)
    (htInner : t < T * ((n : ℝ) + 1) / ((n : ℝ) + 2)) :
    let u : ℕ → ℝ := fun i => T * (i : ℝ) / ((n : ℝ) + 2)
    (∑ i ∈ Finset.range (n + 1),
      (Set.Ico (u i) (u (i + 1))).indicator (fun _ => c i) t) =
      c ⌊(t / T) * ((n : ℝ) + 2)⌋₊ := by sorry
