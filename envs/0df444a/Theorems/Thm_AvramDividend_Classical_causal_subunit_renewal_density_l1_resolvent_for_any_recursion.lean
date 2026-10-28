-- Prove2me | Theorems.Thm_AvramDividend_Classical_causal_subunit_renewal_density_l1_resolvent_for_any_recursion
-- name    : AvramDividend.Classical.causal_subunit_renewal_density_l1_resolvent_for_any_recursion
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T11:00:34.484889+00:00
-- url     : https://prove2.me/theorems/f4d3f7f2-c984-4f37-8ce8-6d5b8f4cedb0
-- title:
--   Every subunit causal recursive renewal density is L1 and has exact resolvent mass
-- statement:
--   For any real-line convolution-power recurrence driven by a continuous antitone nonnegative causal kernel with mass in (0,1), the summed renewal density is integrable on positive times and has total mass rho/(1-rho). The recurrence uniquely determines each power, transferring the constructed L1 resolvent theorem to every prospective kernel representation used in the BV Esscher Lévy scale identification.

import Theorems.Thm_AvramDividend_Classical_causal_subunit_renewal_density_l1_resolvent

open AvramDividend.Classical MeasureTheory Set

theorem AvramDividend.Classical.causal_subunit_renewal_density_l1_resolvent_for_any_recursion
    (κ : ℝ → ℝ) (ρ : ℝ)
    (hρpos : 0 < ρ) (hρlt : ρ < 1)
    (hcont : ContinuousOn κ (Ioi (0 : ℝ)))
    (hanti : AntitoneOn κ (Ioi (0 : ℝ)))
    (hκzero : ∀ x : ℝ, x ≤ 0 → κ x = 0)
    (hκpos : ∀ x : ℝ, 0 ≤ x → 0 ≤ κ x)
    (hκL1 : IntegrableOn κ (Ioi (0 : ℝ)) volume)
    (hmass : (∫ x in Ioi (0 : ℝ), κ x ∂volume) = ρ)
    (G : ℕ → ℝ → ℝ)
    (hGzero : G 0 = κ)
    (hGrec : ∀ n : ℕ, G (n + 1) =
      fun x : ℝ => ∫ y : ℝ, κ y * G n (x - y) ∂volume) :
    IntegrableOn (fun x : ℝ => ∑' n : ℕ, G n x)
      (Ioi (0 : ℝ)) volume ∧
    (∫ x in Ioi (0 : ℝ), ∑' n : ℕ, G n x ∂volume) =
      ρ / (1 - ρ) := by sorry
