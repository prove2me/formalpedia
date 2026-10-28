-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat04_esscher_positive_root_perpetual_infimum_probability_full_mass
-- name    : AvramDividend.Classical.chat04_esscher_positive_root_perpetual_infimum_probability_full_mass
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-27T00:14:11.410879+00:00
-- url     : https://prove2.me/theorems/70aae7c7-2361-4464-b02e-667af1a518a9
-- title:
--   The perpetual positive-root Esscher reflected-infimum law is a probability with an exponential survival-CDF lower bound
-- statement:
--   For q>0 and a positive Esscher root φ with ψ(φ)=q, the finite Borel measure representing the genuine infinite-horizon Esscher survival distribution has total mass one. Quantitatively the CDF of −inf X under the positive-root Esscher law is at least 1−exp(−φ b/2) at every b>0. The proof must transfer the already proved uniform finite-grid downcrossing inequality to all continuous times using right continuity, a countable dense schedule and an explicit terminal observation, then use projective consistency of Esscher finite-horizon laws and limit b→∞. No infinite-horizon tilted law or Wiener–Hopf transform is assumed.
-- source:
--   Avram, Palmowski, Pistorius (2007), spectrally negative Lévy positive-root Esscher transform; Kyprianou, Kuznetsov and Rivero, The Theory of Scale Functions for Spectrally Negative Lévy Processes, Esscher transform and Wiener-Hopf section; Prove2Me proved fixed-terminal finite-grid Doob bound and perpetual infimum finite-measure theorem.

import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.MeasureTheory.Measure.Typeclasses.Finite
import Mathlib.Probability.Process.Filtration
import Mathlib.Analysis.SpecialFunctions.Exp
import Theorems.Thm_AvramDividend_Classical_chat04_esscher_perpetual_infimum_finite_distribution_measure
import Theorems.Thm_AvramDividend_Classical_chat04_esscher_positive_root_finite_grid_downcrossing_probability_bound
import Theorems.Thm_AvramDividend_Classical_chat04_random_reserve_lower_survival_closed_grid_iff
open AvramDividend.Classical MeasureTheory Set Filter Topology
open scoped NNReal ENNReal

theorem AvramDividend.Classical.chat04_esscher_positive_root_perpetual_infimum_probability_full_mass
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (q φ : ℝ)
    (hq : 0 < q) (hφ : 0 < φ) (hroot : X.ψ φ = q) :
    ∃ ν : Measure ℝ, IsProbabilityMeasure ν ∧
      (∀ x : ℝ, ν (Iic x) =
        (⨅ t : ℝ≥0, ENNReal.ofReal
          (∫ ω, ({ω | ∀ s : ℝ≥0, s ≤ t → 0 ≤ x + X.X s ω}).indicator
            (fun ω => Real.exp (φ * X.X t ω -
              (t : ℝ) * laplaceExponent X.c X.σ X.ν φ)) ω ∂P))) ∧
      ∀ b : ℝ, 0 < b →
        ENNReal.ofReal (1 - Real.exp (-(φ / 2) * b)) ≤ ν (Iic b) := by sorry
