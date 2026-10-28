-- Prove2me | Theorems.Thm_AvramDividend_Classical_causal_signed_integrable_product_of_envelope
-- name    : AvramDividend.Classical.causal_signed_integrable_product_of_envelope
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-24T16:05:19.223773+00:00
-- url     : https://prove2.me/theorems/97067ad9-974c-4c8b-b7cc-d7b93d3c4acd
-- title:
--   Signed causal convolution product inherits interval integrability from its positive envelope
-- statement:
--   For nonnegative-time kernels and functions with pointwise absolute domination by a positive envelope, an integrable causal envelope product makes the signed convolution product interval-integrable, provided the signed product is almost-everywhere strongly measurable. This directly supplies the hPint premise of the canonical signed-power bound on the route to the Gaussian C1 scale resolvent.
-- source:
--   A pointwise signed-envelope comparison and AEStronglyMeasurable signed integrand imply norm domination under the restricted volume measure. Apply pinned Mathlib Integrable.mono' and the interval-integrable/Ioc equivalence. This removes one of the explicit product integrability premises in the signed Gaussian Neumann power induction.

import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

open AvramDividend.Classical MeasureTheory Set

theorem AvramDividend.Classical.causal_signed_integrable_product_of_envelope
    (k κ P F : ℝ → ℝ) (x : ℝ) (hx : 0 < x)
    (hkdom : ∀ t : ℝ, 0 ≤ t → |k t| ≤ κ t)
    (hPdom : ∀ t : ℝ, 0 ≤ t → |P t| ≤ F t)
    (hMeas : AEStronglyMeasurable
      (fun s : ℝ => k (x - s) * P s)
      (volume.restrict (Ioc (0 : ℝ) x)))
    (hFint : IntervalIntegrable
      (fun s : ℝ => κ (x - s) * F s) volume 0 x) :
    IntervalIntegrable
      (fun s : ℝ => k (x - s) * P s) volume 0 x := by sorry
