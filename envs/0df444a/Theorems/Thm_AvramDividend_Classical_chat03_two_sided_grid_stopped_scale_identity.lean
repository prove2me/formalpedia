-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat03_two_sided_grid_stopped_scale_identity
-- name    : AvramDividend.Classical.chat03_two_sided_grid_stopped_scale_identity
-- status  : Disproved
-- author  : @WillR
-- created : 2026-10-21T04:13:04.283443+00:00
-- url     : https://prove2.me/theorems/ac7212b2-18ee-4ce5-b5aa-ea36159e92a4
-- title:
--   Bounded optional stopping of the q-scale payoff at the first strict two-sided grid exit
-- statement:
--   Let W be a q-scale function that vanishes at the origin, let a and x satisfy 0 <= x <= a, and let the process be sampled on a deterministic increasing clock. Stop at the first strict two-sided exit of the interval (lower, upper), that is, the first sampled time at which the reserve leaves the interval. The discounted q-scale payoff of the stopped reserve satisfies the optional-stopping identity: the discounted probability of a successful upward exit, multiplied by the scale value at the upper barrier, equals the scale value at the starting point. This is the discrete, finite-grid version of the two-sided exit identity, and it is the step that lets the continuous identity be obtained by passing to the limit on increasingly fine meshes. It is stated here with no standing assumption, because the two ingredients it needs, the vanishing of the scale function at the origin and the absence of positive overshoot, are both available without integrability of the process increment.
-- source:
--   The optional-stopping step of the two-sided exit identity, at a bounded two-sided grid stop; the continuous counterpart is Chan, Kyprianou and Savov (2011), Smoothness of scale functions for spectrally negative Levy processes. Formalised in the Avram Dividend Classical proof programme.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_TwoSidedExit

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.chat03_two_sided_grid_stopped_scale_identity
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 < q) (W : ℝ → ℝ)
    (hW : IsScaleFunction X q W)
    (hzero : W 0 = 0)
    (a x : ℝ) (ha : 0 < a) (hx0 : 0 ≤ x) (hxa : x ≤ a)
    (clock : ℕ → ℝ≥0) (hc : Monotone clock) (hc0 : clock 0 = 0)
    (H : Filtration ℕ mΩ) (hH : ∀ k, H k = 𝓕 (clock k))
    (lower upper : ℝ) (m : ℕ)
    (K : Ω → ℕ)
    (hK : ∀ ω, K ω = hittingBtwn
      (fun k ω => max (X.X (clock k) ω - upper)
        (lower - X.X (clock k) ω)) (Set.Ioi (0 : ℝ)) 0 m ω) :
    (∫⁻ ω,
      if twoSidedExitUpTime X (a - x) ω <
          twoSidedExitDownTime X (-x) ω then
        ENNReal.ofReal
          (Real.exp (-(q * ENNReal.toReal
            (twoSidedExitUpTime X (a - x) ω))))
      else 0 ∂P) * ENNReal.ofReal (W a) =
      ENNReal.ofReal (W x) := by sorry
