-- Prove2me | Theorems.Thm_AvramDividend_Classical_causal_neumann_C1_with_power_domination
-- name    : AvramDividend.Classical.causal_neumann_C1_with_power_domination
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-24T22:29:44.656323+00:00
-- url     : https://prove2.me/theorems/4322e6f7-9112-47a8-82d7-e0a78ffa6320
-- title:
--   Gaussian signed C1 Neumann resolvent retaining convolution-power L1 and envelope bounds
-- statement:
--   Under the same antitone Gaussian kernel and contraction hypotheses as the proved C1 Neumann-series existence theorem, provide the actual convolution powers together with their integrability and signed-envelope bounds. These extra certificates make it possible to verify the series satisfies its Volterra equation.
-- source:
--   Strengthen the canonical Proved causal_neumann_C1_from_antitone_envelope_powers by retaining the existing hPL1 and pointwise signed envelope hPdom witnesses from causal_l1_signed_powers_exist_dominated. The original proof constructed both but discarded them. These bounds feed the exact Gaussian Neumann primitive mass estimate and the signed Volterra resolvent identity.

import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Theorems.Thm_AvramDividend_Classical_causal_antitone_power_product_integrable
import Theorems.Thm_AvramDividend_Classical_causal_l1_signed_powers_exist_dominated
import Theorems.Thm_AvramDividend_Classical_causal_neumann_C1_resolvent_from_envelope
open AvramDividend.Classical MeasureTheory Set

theorem AvramDividend.Classical.causal_neumann_C1_with_power_domination
    (k κ : ℝ → ℝ) (F : ℕ → ℝ → ℝ) (a ρ w : ℝ)
    (ha : 0 < a) (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) (hw : 0 ≤ w)
    (hkL1 : IntegrableOn k (Ioi (0 : ℝ)) volume)
    (hkmeas : Measurable k)
    (hkcont : ContinuousOn k (Ioi (0 : ℝ)))
    (hkzero : ∀ x : ℝ, x ≤ 0 → k x = 0)
    (hκL1 : IntegrableOn κ (Ioi (0 : ℝ)) volume)
    (hκanti : AntitoneOn κ (Ioi (0 : ℝ)))
    (hκcont : ContinuousOn κ (Ioi (0 : ℝ)))
    (hκnonneg : ∀ t : ℝ, 0 < t → 0 ≤ κ t)
    (hkdom : ∀ t : ℝ, 0 ≤ t → |k t| ≤ κ t)
    (hF0 : F 0 = κ)
    (hFrec : ∀ n : ℕ, F (n + 1) =
      fun x : ℝ => ∫ s in Ioc (0 : ℝ) x, κ s * F n (x - s) ∂volume)
    (hFL1 : ∀ n : ℕ, IntegrableOn (F n) (Ioi (0 : ℝ)) volume)
    (hFnonneg : ∀ n : ℕ, ∀ s : ℝ, 0 ≤ s → 0 ≤ F n s)
    (hFmass : ∀ n : ℕ, ∀ x : ℝ, 0 ≤ x →
      (∫ s in Ioc (0 : ℝ) x, F n s ∂volume) ≤ ρ ^ (n + 1))
    (hFpoint : ∀ n : ℕ, ∀ x : ℝ, 0 < x →
      F n x ≤ ((n + 1 : ℝ) ^ 2 * ρ ^ (n + 1)) / x) :
    ∃ (P : ℕ → ℝ → ℝ) (g : ℝ → ℝ),
      P 0 = k ∧
      (∀ n : ℕ, P (n + 1) =
        fun x : ℝ => ∫ s in Ioc (0 : ℝ) x, k s * P n (x - s) ∂volume) ∧
      (∀ n : ℕ, IntegrableOn (P n) (Ioi (0 : ℝ)) volume) ∧
      (∀ n : ℕ, ∀ x : ℝ, 0 ≤ x → |P n x| ≤ F n x) ∧
      (g = fun y : ℝ => 1 / a + Real.exp (w * y) *
        (∑' n : ℕ, (Real.exp (-w * y) *
          (∫ s in Ioc (0 : ℝ) y,
            Real.exp (w * s) * P n s ∂volume)) / a)) ∧
      ContinuousOn g (Ici (0 : ℝ)) ∧
      ContDiffOn ℝ 1 g (Ioi (0 : ℝ)) := by sorry
