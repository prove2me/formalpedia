-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ga_a374_finite_masked_Young_half_epsilon_energy_cross_factor_identity
-- name    : AvramDividend.Classical.avram_ga_a374_finite_masked_Young_half_epsilon_energy_cross_factor_identity
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T12:24:07.78245+00:00
-- url     : https://prove2.me/theorems/07ca254c-0987-4387-8897-18a06ce9d331
-- title:
--   Finite Gaussian masked Young source with half-epsilon parameters factors into original energy/cross and discount-width terms
-- statement:
--   For an arbitrary finite mask, the weighted raw second energy with Taylor and Young coefficients ε/2+ε/2, the weighted absolute raw-centred Hessian cross and the per-cell discount Young allowance simplify exactly to ε times the masked raw energy, M/2 times the masked cross energy, and cellcount times (qΔL)²/(2ε). This scalar identity is the exact algebra between a372 and the original a373 small-source AE modulus, keeping source expectations and stopping masks untouched.
-- source:
--   Original Gaussian physical fullcell selected-threshold Young error normalization.

import Mathlib
open MeasureTheory Filter Topology
noncomputable section

theorem AvramDividend.Classical.avram_ga_a374_finite_masked_Young_half_epsilon_energy_cross_factor_identity
    {ι : Type*} (S : Finset ι) (A : ι → Prop) [DecidablePred A]
    (r z : ι → ℝ) (ε M q Δ L : ℝ) (hε : 0 < ε) :
    (∑ i ∈ S, if A i then ((ε / 2) + (ε / 2)) * (r i)^2 else 0) +
    (∑ i ∈ S, if A i then M / 2 * |(r i)^2-(z i)^2| else 0) +
      (S.card : ℝ) * ((q*Δ*L)^2/(4*(ε/2))) =
    ε * (∑ i ∈ S, if A i then (r i)^2 else 0) +
    (M/2) * (∑ i ∈ S, if A i then |(r i)^2-(z i)^2| else 0) +
      (S.card : ℝ) * ((q*Δ*L)^2/(2*ε)) := by sorry
