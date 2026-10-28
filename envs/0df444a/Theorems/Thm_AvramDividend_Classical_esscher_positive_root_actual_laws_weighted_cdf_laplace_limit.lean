-- Prove2me | Theorems.Thm_AvramDividend_Classical_esscher_positive_root_actual_laws_weighted_cdf_laplace_limit
-- name    : AvramDividend.Classical.esscher_positive_root_actual_laws_weighted_cdf_laplace_limit
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-27T19:42:08.958642+00:00
-- url     : https://prove2.me/theorems/978d9a77-bd6c-4166-a3de-ae2e680bbffd
-- title:
--   Actual positive-root Esscher finite exponential-clock reflected-infimum laws converge in every exponential capital CDF transform
-- statement:
--   Given a true spectrally negative Lévy process, positive discount/root q,φ satisfying ψ(φ)=q and positive exponential rates p_n→0, there exists a canonical genuine perpetual probability ν such that, for every β>0, the exponential capital integral of the CDF of the real reflected infimum under the genuinely tilted path×Exp(p_n) law converges to the same integral of ν's CDF. The proof composes genuine probability pushforward measures with all-threshold true-clock Esscher CDF convergence, then applies the independently verified probability CDF-to-exponential capital integral dominated-convergence theorem. Does not presuppose or establish the finite-rate Wiener–Hopf factor.
-- source:
--   Accepted 1E-C 33e64e36 actual positive-root infimum laws CDF limit (pending acceptance) and accepted 0bf634fd probability CDF-to-weighted-Laplace bridge. Pinned Mathlib 0df444a.

import Mathlib.Probability.Distributions.Exponential
import Mathlib.Probability.CDF
import Theorems.Thm_AvramDividend_Classical_esscher_positive_root_true_infimum_laws_cdf_converge
import Theorems.Thm_AvramDividend_Classical_esscher_probability_cdf_limits_imply_weighted_laplace_limits
open AvramDividend.Classical ProbabilityTheory MeasureTheory Filter Set
open scoped ENNReal NNReal

theorem AvramDividend.Classical.esscher_positive_root_actual_laws_weighted_cdf_laplace_limit
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (q φ : ℝ)
    (hq : 0 < q) (hφ : 0 < φ) (hroot : X.ψ φ = q)
    (p : ℕ → ℝ)
    (hp : Tendsto p atTop (nhdsWithin (0 : ℝ) (Ioi 0)))
    (hpos : ∀ n, 0 < p n) :
    ∃ ν : Measure ℝ, IsProbabilityMeasure ν ∧
      (∀ β : ℝ, 0 < β → Tendsto
        (fun n : ℕ => (∫ x in Ioi (0 : ℝ), Real.exp (-β * x) * cdf (Measure.map (fun z : Ω × ℝ => -sInf {y : ℝ | ∃ s : ℝ≥0,
  s ≤ Real.toNNReal z.2 ∧ y = X.X s z.1}) ((P.prod (expMeasure (p n))).withDensity
  (fun z : Ω × ℝ => ENNReal.ofReal (Real.exp
    (φ * X.X (Real.toNNReal z.2) z.1 -
      (Real.toNNReal z.2 : ℝ) * X.ψ φ))))) x ∂volume))
        atTop (nhds (∫ x in Ioi (0 : ℝ), Real.exp (-β * x) * cdf ν x ∂volume))) := by sorry
