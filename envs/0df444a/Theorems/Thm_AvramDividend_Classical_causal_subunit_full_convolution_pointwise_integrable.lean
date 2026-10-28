-- Prove2me | Theorems.Thm_AvramDividend_Classical_causal_subunit_full_convolution_pointwise_integrable
-- name    : AvramDividend.Classical.causal_subunit_full_convolution_pointwise_integrable
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T23:17:46.329435+00:00
-- url     : https://prove2.me/theorems/ea714313-33ed-4fae-8f59-146ffd223ed8
-- title:
--   Pointwise integrability of all causal subunit renewal convolution powers on the full line
-- statement:
--   For a continuous-on-positive, antitone, integrable causal kernel of mass below one and any exact convolution recurrence, every product k(y)F_n(x−y) is globally Lebesgue integrable for every n and x. At x>0, combine the existing antitone endpoint-splitting estimate with the interval-to-global reflection lemma. At x≤0, causal support makes the product vanish. This closes the last hard integrability premise of the generic geometric renewal density bridge in bounded-variation zero-barrier scale identification.
-- source:
--   Proved causal_subunit_any_real_recursion_power_bounds, causal_full_convolution_powers_zero_nonpositive, causal_antitone_L1_split_product_intervalIntegrable, causal_reflected_interval_to_global_convolution_integrable.

import Theorems.Thm_AvramDividend_Classical_causal_subunit_any_real_recursion_power_bounds
import Theorems.Thm_AvramDividend_Classical_causal_full_convolution_powers_zero_nonpositive
import Theorems.Thm_AvramDividend_Classical_causal_antitone_L1_split_product_intervalIntegrable
import Theorems.Thm_AvramDividend_Classical_causal_reflected_interval_to_global_convolution_integrable
import Mathlib.Tactic.Linarith

open AvramDividend.Classical MeasureTheory Set

theorem AvramDividend.Classical.causal_subunit_full_convolution_pointwise_integrable
    (k : ℝ → ℝ) (ρ : ℝ) (F : ℕ → ℝ → ℝ)
    (hρpos : 0 < ρ) (hρlt : ρ < 1)
    (hcont : ContinuousOn k (Ioi (0 : ℝ)))
    (hanti : AntitoneOn k (Ioi (0 : ℝ)))
    (hkzero : ∀ t : ℝ, t ≤ 0 → k t = 0)
    (hkpos : ∀ t : ℝ, 0 ≤ t → 0 ≤ k t)
    (hkL1 : IntegrableOn k (Ioi (0 : ℝ)) volume)
    (hmass : (∫ t in Ioi (0 : ℝ), k t ∂volume) = ρ)
    (hFzero : F 0 = k)
    (hFsucc : ∀ n : ℕ, F (n + 1) =
      fun x : ℝ => ∫ y : ℝ, k y * F n (x - y) ∂volume) :
    ∀ n : ℕ, ∀ x : ℝ,
      Integrable (fun y : ℝ => k y * F n (x - y)) volume  := by sorry
