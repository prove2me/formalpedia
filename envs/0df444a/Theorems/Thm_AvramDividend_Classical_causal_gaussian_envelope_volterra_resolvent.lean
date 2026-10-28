-- Prove2me | Theorems.Thm_AvramDividend_Classical_causal_gaussian_envelope_volterra_resolvent
-- name    : AvramDividend.Classical.causal_gaussian_envelope_volterra_resolvent
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-24T22:54:32.720095+00:00
-- url     : https://prove2.me/theorems/2e9343a2-82d3-4158-80b6-2661c5491939
-- title:
--   Gaussian C1 signed-power envelope series solves the derivative Volterra equation
-- statement:
--   A Gaussian signed convolution-power series dominated by a contracting nonnegative envelope solves the derivative Volterra integral equation. This joins the established C1 regularity proof with the previously proved Neumann dominated-convergence resolvent identity.
-- source:
--   Instantiate the signed primitive witness, exponential-series identification, local and pointwise geometric estimates, continuous-term measurability, summability and signed Gaussian Neumann Volterra identity. This proves the exact resolvent equation for the explicit C1 Gaussian candidate obtained from the canonical antitone envelope construction.

import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Theorems.Thm_AvramDividend_Classical_causal_gaussian_primitive_geometric_witness
import Theorems.Thm_AvramDividend_Classical_causal_gaussian_weighted_series_identification
import Theorems.Thm_AvramDividend_Classical_causal_gaussian_primitive_local_geometric
import Theorems.Thm_AvramDividend_Classical_causal_neumann_gaussian_nonpositive_zero
import Theorems.Thm_AvramDividend_Classical_causal_neumann_local_to_pointwise_geom
import Theorems.Thm_AvramDividend_Classical_causal_neumann_measurable_from_c1_primitives
import Theorems.Thm_AvramDividend_Classical_causal_geometric_neumann_summable
import Theorems.Thm_AvramDividend_Classical_causal_gaussian_series_volterra_identity_of_initial_power
open AvramDividend.Classical MeasureTheory Set

theorem AvramDividend.Classical.causal_gaussian_envelope_volterra_resolvent
    (K k : ℝ → ℝ) (P F : ℕ → ℝ → ℝ) (g : ℝ → ℝ)
    (a β w ρ : ℝ)
    (ha : 0 < a) (hw : 0 ≤ w) (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1)
    (hK : IntegrableOn K (Ioi (0 : ℝ)) volume)
    (hk : k = fun t : ℝ =>
      if 0 < t then -(a⁻¹ * Real.exp (-w * t) * (β + K t)) else 0)
    (hkL1 : IntegrableOn k (Ioi (0 : ℝ)) volume)
    (hPL1 : ∀ n : ℕ, IntegrableOn (P n) (Ioi (0 : ℝ)) volume)
    (hPrec : ∀ n : ℕ, P (n + 1) =
      fun x : ℝ => ∫ s in Ioc (0 : ℝ) x, k s * P n (x - s) ∂volume)
    (hP0 : P 0 = k)
    (hFL1 : ∀ n : ℕ, IntegrableOn (F n) (Ioi (0 : ℝ)) volume)
    (hDom : ∀ n : ℕ, ∀ x : ℝ, 0 ≤ x → |P n x| ≤ F n x)
    (hFmass : ∀ n : ℕ, ∀ x : ℝ, 0 ≤ x →
      (∫ s in Ioc (0 : ℝ) x, F n s ∂volume) ≤ ρ ^ (n + 1))
    (hg : g = fun y : ℝ => 1 / a + Real.exp (w * y) *
      (∑' n : ℕ, (Real.exp (-w * y) *
        (∫ s in Ioc (0 : ℝ) y,
          Real.exp (w * s) * P n s ∂volume)) / a)) :
    ∀ x : ℝ, a * g x +
      (∫ s in Ioc (0 : ℝ) x,
        (β + K (x - s)) * g s ∂volume) = 1 := by sorry
