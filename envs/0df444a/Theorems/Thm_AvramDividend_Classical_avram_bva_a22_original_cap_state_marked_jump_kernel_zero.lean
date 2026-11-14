-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bva_a22_original_cap_state_marked_jump_kernel_zero
-- name    : AvramDividend.Classical.avram_bva_a22_original_cap_state_marked_jump_kernel_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-13T12:43:27.313193+00:00
-- url     : https://prove2.me/theorems/71018585-aea8-47fd-a3c7-1eddb32c9ffd
-- title:
--   The original BV A22 marked negative-jump cash kernel vanishes identically when the prepayment reserve is at the upper cap
-- statement:
--   For the original marked negative-jump source integrand from A22, evaluate the signed discounted candidate jump difference at any original time, mark and sample path, with the row-n original strict spatial band mask. If the true prepayment left-limit reserve has extended-real value exactly equal to the cap, the integrand vanishes identically. This is exact for every prescribed row and strategy and requires no surrogate process or finite jump activity. The original full source H has an additional stopped clock mask, so it vanishes at the upper cap as well. This lemma is the necessary kernel-level cap-occupation defect underpinning the finite-cap A22 and A23 analytic counterexample.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_bva_a22_original_strict_cofinal_rows_never_contain_upper_cap_reserve
open Classical MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_bva_a22_original_cap_state_marked_jump_kernel_zero
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x q : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (w : ℝ → ℝ)
    (C : ℝ≥0∞) (a b : ℕ → ℝ)
    (ha : ∀ n, 0 < a n)
    (hinside : ∀ n, Icc (a n / 2) (b n) ⊆
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (n : ℕ) (t : ℝ≥0) (ω : Ω) (z : ℝ)
    (hcap : ENNReal.ofReal
        (Function.leftLim
          (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t) = C) :
    (if
        Function.leftLim
          (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t ∈
            Icc (a n) (b n) ∧ z < 0
      then
        Real.exp (-(q * (t : ℝ))) *
          (w (Function.leftLim
            (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t + z) -
           w (Function.leftLim
            (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t))
      else 0) = 0 := by sorry
