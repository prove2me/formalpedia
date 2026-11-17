-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a25_original_negative_Borel_binomial_grid_singleton_approx_20261115
-- name    : AvramDividend.Classical.avram_a25_original_negative_Borel_binomial_grid_singleton_approx_20261115
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-15T15:27:17.15039+00:00
-- url     : https://prove2.me/theorems/96c80e24-c7cb-4b17-9b88-18606992761e
-- title:
--   Original physical negative-Borel marked jump count approximated by binomial occupied-cell laws
-- statement:
--   Let K be the measurable natural-valued actual original Lévy negative-Borel jump count by T, with rate r=Tν(B). Then there exists a sequence of unit-interval cell occupancy probabilities p_n with n p_n→r for which each binomial singleton mass Bin(n,p_n){k} converges to the original source count pushforward law (P.map K){k}. This is the sole substantive stochastic approximation remaining in the Bernoulli-grid proof of the full original Poisson count law. A sound proof uses the now-Proved future physical count independent of past observables 0832c67e, shifted exact void formula 103eb83a, shifted quadratic collision bound f0852f64, original finite physical count realisation 84a4791e, and physical marked-count disjoint-interval additivity. The discrepancy between the full count and the number of occupied cells is bounded by the chance of a multiple-jump grid cell, O(r²/n), while independent equal-length occupied-cell indicators have Bin(n,p_n) law. No replacement process or artificial Poisson marks.
-- source:
--   Proved original independence 0832c67e, shifted void 103eb83a (pending at authoring time), shifted collisions f0852f64, source physical marked count and Mathlib Binomial.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory ProbabilityTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_a25_original_negative_Borel_binomial_grid_singleton_approx_20261115
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (T : ℝ≥0) (B : Set ℝ)
    (hB : MeasurableSet B) (hNeg : B ⊆ Iio (0 : ℝ))
    (K : Ω → ℕ) (hK : Measurable K)
    (hCount : ∀ᵐ ω ∂P, (K ω : ℝ) =
      (((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc 0 T ×ˢ B)).toReal)
    (r : ℝ≥0)
    (hr : (r : ℝ) = ((T : ℝ≥0∞) * X.ν B).toReal) :
    ∃ p : ℕ → unitInterval,
      Tendsto (fun n : ℕ => (n : ℝ) * (p n : ℝ))
        atTop (𝓝 (r : ℝ)) ∧
      ∀ k : ℕ, Tendsto (fun n : ℕ => Bin(n, p n) {k})
        atTop (𝓝 (P.map K {k})) := by sorry
