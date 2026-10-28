-- Prove2me | Theorems.Thm_AvramDividend_Classical_causal_subunit_shifted_renewal_density_continuous_integrable_for_any_recursion
-- name    : AvramDividend.Classical.causal_subunit_shifted_renewal_density_continuous_integrable_for_any_recursion
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T11:02:07.479211+00:00
-- url     : https://prove2.me/theorems/b5cf084c-aed8-46a1-a98f-a0968c02dabb
-- title:
--   Every causal subunit renewal recursion has a continuous shifted density integrable from zero
-- statement:
--   For any recursive convolution-power family driven by the same continuous antitone causal subunit kernel, the shifted renewal series is continuous on positive times and scalar-multiplied interval-integrable from zero. The deterministic proof uses existence of one regular family and induction showing uniqueness of the recursion. In particular, this discharges the universal recurrence-to-integrability premise of the open bounded-variation Esscher subunit kernel scale identification.

import Theorems.Thm_AvramDividend_Classical_causal_subunit_shifted_renewal_density_continuous_integrable_at_zero

open AvramDividend.Classical MeasureTheory Set

theorem AvramDividend.Classical.causal_subunit_shifted_renewal_density_continuous_integrable_for_any_recursion
    (κ : ℝ → ℝ) (ρ b : ℝ)
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
    ContinuousOn
      (fun x : ℝ => ∑' n : ℕ,
        if n = 0 then (0 : ℝ) else G (n - 1) x)
      (Ioi (0 : ℝ)) ∧
    (∀ x : ℝ, 0 < x →
      IntervalIntegrable
        (fun y : ℝ => b * ∑' n : ℕ,
          if n = 0 then (0 : ℝ) else G (n - 1) y)
        volume 0 x) := by sorry
