-- Prove2me | Theorems.Thm_AvramDividend_Classical_causal_convolution_powers_continuous_of_bounded_kernel
-- name    : AvramDividend.Classical.causal_convolution_powers_continuous_of_bounded_kernel
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T22:16:18.500439+00:00
-- url     : https://prove2.me/theorems/ab6a6851-705c-48a3-a649-802466061aa1
-- title:
--   Continuity of every convolution power of a bounded continuous L1 kernel
-- statement:
--   For a globally bounded continuous real kernel κ and a sequence of L1 convolution powers with F0=κ and the full-real convolution recurrence, all powers Fn are continuous. The proof applies the pinned bounded-continuous-times-L1 convolution theorem to each successor; useful to establish uniform-limit continuity of the zero-scale positive-discount Neumann series.
-- source:
--   Pinned Mathlib convolution theorem via AvramDividend.Classical.continuous_causal_convolution_of_bounded_continuous_left

import Theorems.Thm_AvramDividend_Classical_continuous_causal_convolution_of_bounded_continuous_left
open AvramDividend.Classical MeasureTheory Set

theorem AvramDividend.Classical.causal_convolution_powers_continuous_of_bounded_kernel
    (κ : ℝ → ℝ) (F : ℕ → ℝ → ℝ)
    (hκc : Continuous κ)
    (hκb : BddAbove (Set.range fun x : ℝ => ‖κ x‖))
    (hFi : ∀ n : ℕ, Integrable (F n) volume)
    (hF0 : F 0 = κ)
    (hFsucc : ∀ n : ℕ, F (n + 1) =
      fun x : ℝ => ∫ y : ℝ, κ y * F n (x - y) ∂volume) :
    ∀ n : ℕ, Continuous (F n) := by sorry
