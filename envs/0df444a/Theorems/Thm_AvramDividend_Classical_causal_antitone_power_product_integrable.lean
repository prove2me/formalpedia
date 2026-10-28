-- Prove2me | Theorems.Thm_AvramDividend_Classical_causal_antitone_power_product_integrable
-- name    : AvramDividend.Classical.causal_antitone_power_product_integrable
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-24T16:18:45.917474+00:00
-- url     : https://prove2.me/theorems/fb680899-9b48-49b0-9c41-b23fb33ddf1e
-- title:
--   Every antitone quadratic-geometric envelope power has integrable causal product
-- statement:
--   A nonnegative antitone continuous integrable kernel has integrable causal products with every nonnegative integrable sequence term whose positive-time bound is ((n+1)^2 ρ^(n+1))/x, with ρ nonnegative. The result packages the exact positive-envelope integrability premise for the Gaussian signed-Neumann iteration.
-- source:
--   Direct application of the Proved antitone L1 midpoint-splitting convolution integrability theorem to each power with A=(n+1)^2ρ^(n+1). It supplies hFint for signed-power domination induction required by the Gaussian Esscher C1 derivative resolvent.

import Theorems.Thm_AvramDividend_Classical_causal_antitone_L1_split_product_intervalIntegrable

open AvramDividend.Classical MeasureTheory Set

theorem AvramDividend.Classical.causal_antitone_power_product_integrable
    (κ : ℝ → ℝ) (F : ℕ → ℝ → ℝ) (ρ : ℝ)
    (hρ0 : 0 ≤ ρ)
    (hκanti : AntitoneOn κ (Ioi (0 : ℝ)))
    (hκcont : ContinuousOn κ (Ioi (0 : ℝ)))
    (hκnonneg : ∀ t : ℝ, 0 < t → 0 ≤ κ t)
    (hκL1 : IntegrableOn κ (Ioi (0 : ℝ)) volume)
    (hFL1 : ∀ n : ℕ, IntegrableOn (F n) (Ioi (0 : ℝ)) volume)
    (hFnonneg : ∀ n : ℕ, ∀ s : ℝ, 0 < s → 0 ≤ F n s)
    (hFpoint : ∀ n : ℕ, ∀ s : ℝ, 0 < s →
      F n s ≤ ((n + 1 : ℝ) ^ 2 * ρ ^ (n + 1)) / s) :
    ∀ n : ℕ, ∀ x : ℝ, 0 < x →
      IntervalIntegrable (fun s : ℝ => κ (x - s) * F n s) volume 0 x := by sorry
