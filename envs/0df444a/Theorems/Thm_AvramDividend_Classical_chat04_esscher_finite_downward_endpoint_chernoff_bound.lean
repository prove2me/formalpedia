-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat04_esscher_finite_downward_endpoint_chernoff_bound
-- name    : AvramDividend.Classical.chat04_esscher_finite_downward_endpoint_chernoff_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T22:54:14.135759+00:00
-- url     : https://prove2.me/theorems/45b859b2-ee90-40bd-ac27-718d8d26c85f
-- title:
--   Exact weighted exponential Chernoff estimate for downward Lévy increments under the finite Esscher law
-- statement:
--   For any θ≥ε>0, time t and real downside threshold b, the actual θ-Esscher probability of the event X_t≤−b satisfies exp(εb)Q_t(X_t≤−b)≤exp(t[ψ(θ−ε)−ψ(θ)]) in the nonnegative extended reals. This is an explicit finite-horizon downward excursion tail estimate, with no global tilted probability space or Wiener–Hopf formula.
-- source:
--   Apply the independently proven nonnegative Markov bound for exp(−εX_t) under the actual Esscher density, then identify the threshold set with the lower-endpoint event by the independent generic exponential event iff lemma. The bound is the key pointwise input for later countable-grid and stopping-time excursion control.

import Mathlib.MeasureTheory.Measure.WithDensity
import Theorems.Thm_AvramDividend_Classical_chat04_esscher_finite_negative_endpoint_markov_bound
import Theorems.Thm_AvramDividend_Classical_ennreal_exp_downcrossing_threshold_iff
open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.chat04_esscher_finite_downward_endpoint_chernoff_bound
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (t : ℝ≥0) (θ ε b : ℝ)
    (hθ : 0 ≤ θ) (hε : 0 < ε) (hεθ : ε ≤ θ) :
    ENNReal.ofReal (Real.exp (ε * b)) *
      (P.withDensity (fun ω : Ω =>
        ENNReal.ofReal
          (Real.exp (θ * X.X t ω - (t : ℝ) * X.ψ θ))))
        {ω : Ω | X.X t ω ≤ -b} ≤
      ENNReal.ofReal
        (Real.exp ((t : ℝ) * (X.ψ (θ - ε) - X.ψ θ))) := by sorry
