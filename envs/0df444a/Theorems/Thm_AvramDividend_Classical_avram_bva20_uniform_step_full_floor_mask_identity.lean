-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bva20_uniform_step_full_floor_mask_identity
-- name    : AvramDividend.Classical.avram_bva20_uniform_step_full_floor_mask_identity
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-11T20:45:02.624621+00:00
-- url     : https://prove2.me/theorems/ac1e45d7-fad3-4bdd-9001-99af1a2a28ae
-- title:
--   Full real-time uniform frozen-step integrand equals masked original floor coefficient
-- statement:
--   At every real time, including negative times and those at or after the final strict inner-horizon endpoint, the finite uniform frozen-step integrand is exactly the floor-indexed coefficient when 0≤t<T(n+1)/(n+2), and zero otherwise. Combine separately Proved inside-cell floor selector c4aebe37 and outside-row zero sum 29a5ecfb. This exact global identity completes the deterministic source-independent A-to-real-floor-integrand representation needed to apply paired dominated convergence to 7ccc2a1a.
-- source:
--   Necessary global Riemann frozen-step mask identity for source-exact 7ccc2a1a.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_bva20_uniform_step_integrand_eq_floor_coefficient
import Theorems.Thm_AvramDividend_Classical_avram_bva20_monotone_grid_step_zero_outside_row
open Set AvramDividend.Classical
noncomputable section

theorem AvramDividend.Classical.avram_bva20_uniform_step_full_floor_mask_identity
    (T : ℝ) (hT : 0 < T) (n : ℕ) (c : ℕ → ℝ) (t : ℝ) :
    let u : ℕ → ℝ := fun i => T * (i : ℝ) / ((n : ℝ) + 2)
    (∑ i ∈ Finset.range (n + 1),
      (Set.Ico (u i) (u (i + 1))).indicator (fun _ => c i) t) =
    if 0 ≤ t ∧ t < T * ((n : ℝ) + 1) / ((n : ℝ) + 2) then
      c ⌊(t / T) * ((n : ℝ) + 2)⌋₊ else 0 := by sorry
