-- Prove2me | Theorems.Thm_AvramDividend_Classical_causal_geometric_renewal_total_mass_sum
-- name    : AvramDividend.Classical.causal_geometric_renewal_total_mass_sum
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T10:37:51.287237+00:00
-- url     : https://prove2.me/theorems/0ddf841d-8020-44a3-97bb-66a0688bb6c9
-- title:
--   Geometric renewal total mass equals rho divided by one minus rho
-- statement:
--   If the positive-time integrated masses of recursive causal convolution powers are exactly the successive powers of a subunit parameter rho, the sum of all their integrated masses is rho/(1-rho). This computes the deterministic renewal resolvent's total mass and supports the normalisation and Laplace-identity steps of the Esscher scale-function representation.

import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Ring
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

open MeasureTheory Set

theorem AvramDividend.Classical.causal_geometric_renewal_total_mass_sum
    (F : ℕ → ℝ → ℝ) (ρ : ℝ)
    (hρnonneg : 0 ≤ ρ) (hρlt : ρ < 1)
    (hmass : ∀ n : ℕ,
      (∫ x in Ioi (0 : ℝ), F n x ∂volume) = ρ ^ (n + 1)) :
    (∑' n : ℕ, ∫ x in Ioi (0 : ℝ), F n x ∂volume) =
      ρ / (1 - ρ) := by sorry
