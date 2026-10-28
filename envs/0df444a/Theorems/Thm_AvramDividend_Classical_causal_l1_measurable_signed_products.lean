-- Prove2me | Theorems.Thm_AvramDividend_Classical_causal_l1_measurable_signed_products
-- name    : AvramDividend.Classical.causal_l1_measurable_signed_products
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-24T16:38:13.479589+00:00
-- url     : https://prove2.me/theorems/e46f120e-8f4e-46cd-8187-a271e2e56b67
-- title:
--   Signed causal convolution products are measurable from L1 powers
-- statement:
--   For a globally measurable signed kernel k and any sequence of functions individually integrable on positive time, all causal reflected products k(x-s)P_n(s) are almost-everywhere strongly measurable on (0,x] for x>0. This allows signed-power domination to be proved before continuity of the powers is established.
-- source:
--   Use IntegrableOn.mono_set for the inclusion (0,x]⊆(0,∞), so each signed power is AEStronglyMeasurable under the restricted volume measure. The measurable reflected kernel multiplies this integrand, giving exactly the hMeas condition for causal_signed_powers_domination_induction without requiring positive-time continuity of the signed powers.

import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Function.StronglyMeasurable.AEStronglyMeasurable
import Mathlib.MeasureTheory.Group.Arithmetic
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

open AvramDividend.Classical MeasureTheory Set

theorem AvramDividend.Classical.causal_l1_measurable_signed_products
    (k : ℝ → ℝ) (P : ℕ → ℝ → ℝ)
    (hkmeas : Measurable k)
    (hPL1 : ∀ n : ℕ, IntegrableOn (P n) (Ioi (0 : ℝ)) volume) :
    ∀ n : ℕ, ∀ x : ℝ, 0 < x →
      AEStronglyMeasurable
        (fun s : ℝ => k (x - s) * P n s)
        (volume.restrict (Ioc (0 : ℝ) x)) := by sorry
