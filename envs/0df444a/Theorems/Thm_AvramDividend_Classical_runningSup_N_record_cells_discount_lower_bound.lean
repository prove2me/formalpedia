-- Prove2me | Theorems.Thm_AvramDividend_Classical_runningSup_N_record_cells_discount_lower_bound
-- name    : AvramDividend.Classical.runningSup_N_record_cells_discount_lower_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-23T21:04:01.336053+00:00
-- url     : https://prove2.me/theorems/5790103a-80ba-4c28-9676-ed18f9501e92
-- title:
--   N attained record cells give an additive discounted stopped-reward lower bound
-- statement:
--   Fix a sample path of a spectrally negative Lévy process, a payment horizon tau, a discount rate q >= 0, a base record level b >= 0 and a record spacing h >= 0. Suppose the first N consecutive h-spaced record levels b, b+h, ..., b+N*h are all attained at finite record times u_0 <= u_1 <= ... <= u_N, with the last record strictly before the horizon tau. Then the stopped discounted dividend reward over the half-open time interval (u_0, u_N] is at least the sum over the N cells of the terminal-endpoint-discounted cell masses h. This is the finite-horizon N-cell stage of the renewal lower-bound argument for Proposition 1 (barrier strategy value): it generalizes the proved one-cell, two-cell and four-cell stopped discount bounds to arbitrary N, after which passage to the countable record limit and the scale-function cycle law remain.
-- source:
--   Avram, Palmowski, Pistorius, On the optimal dividend problem for a spectrally negative Lévy process, arXiv:math/0702893v1, p. 7, Proposition 1 renewal argument, finite-horizon N-record stage; generalizes Theorems runningSup_stopped_firstRecord_step_discount_bounds, runningSup_stopped_two_firstRecord_steps_discount_bounds and runningSup_stopped_four_firstRecord_steps_discount_pair_bounds

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Definitions.Def_AvramDividend_Classical_ReflectionBarrier

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

namespace AvramDividend.Classical

theorem runningSup_N_record_cells_discount_lower_bound
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (ω : Ω) (τ : ℝ≥0∞) (q : ℝ) (hq : 0 ≤ q)
    (b h : ℝ) (hb : 0 ≤ b) (hh : 0 ≤ h)
    (N : ℕ) (u : ℕ → ℝ≥0)
    (hu : ∀ k : ℕ, k ≤ N → ((u k : ℝ≥0∞) =
      (⨅ (r : ℝ≥0) (_ : b + (k : ℝ) * h < X.X r ω), (r : ℝ≥0∞))))
    (hord : ∀ k : ℕ, k < N → ((u k : ℝ) ≤ (u (k + 1) : ℝ)))
    (hSurvive : ENNReal.ofReal ((u N : ℝ)) < τ) :
    ∑ k ∈ Finset.range N,
        (ENNReal.ofReal (Real.exp (-(q * ((u (k + 1) : ℝ)))))) * ENNReal.ofReal h ≤
      ∫⁻ r in paymentTimes τ,
        if r ∈ Set.Ioc ((u 0 : ℝ)) ((u N : ℝ))
        then ENNReal.ofReal (Real.exp (-(q * r))) else 0
        ∂(dividendMeasure (runningSup X) ω) := by sorry

end AvramDividend.Classical
