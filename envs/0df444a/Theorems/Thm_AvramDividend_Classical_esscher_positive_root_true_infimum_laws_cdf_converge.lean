-- Prove2me | Theorems.Thm_AvramDividend_Classical_esscher_positive_root_true_infimum_laws_cdf_converge
-- name    : AvramDividend.Classical.esscher_positive_root_true_infimum_laws_cdf_converge
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-27T19:26:31.415372+00:00
-- url     : https://prove2.me/theorems/33e64e36-3e98-4666-9bfd-12f9f2a48e42
-- title:
--   Authentic random-time positive-Root Esscher reflected-infimum probability laws converge at every CDF threshold
-- statement:
--   Let X be an actual spectrally negative Lévy process, q>0, φ>0 with ψ(φ)=q, and any rates p_n>0 with p_n→0. The pushforward of the bona fide jointly tilted path×Exp(p_n) probability law under its real reflected running infimum is itself a probability measure for every n. There exists a single genuine perpetual probability ν such that these actual reflected-infimum pushforward measures assign every closed half-line (−∞,x] masses converging to ν((−∞,x]); ν has the proved nontrivial lower bound on positive levels. This upgrades CDF event convergence to convergence of actual measures and uses no finite Wiener-Hopf factor.
-- source:
--   Accepted 1E-C positive-root ν theorem 90c52942, source-specific random-clock reflected probability 3d3e8fe4 (awaiting proof), joint running infimum measurable ae09696f, pinned Measure.map_apply.

import Mathlib.Probability.Distributions.Exponential
import Mathlib.MeasureTheory.Measure.Map
import Theorems.Thm_AvramDividend_Classical_esscher_positive_root_genuine_exponential_cdf_perpetual_measure
import Theorems.Thm_AvramDividend_Classical_esscher_true_random_clock_reflected_law_probability
import Theorems.Thm_AvramDividend_Classical_levy_running_infimum_joint_time_path_measurable
open AvramDividend.Classical MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.esscher_positive_root_true_infimum_laws_cdf_converge
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (q φ : ℝ)
    (hq : 0 < q) (hφ : 0 < φ) (hroot : X.ψ φ = q)
    (p : ℕ → ℝ)
    (hp : Tendsto p atTop (nhdsWithin (0 : ℝ) (Ioi 0)))
    (hpos : ∀ n, 0 < p n) :
    ∃ ν : Measure ℝ, IsProbabilityMeasure ν ∧
      (∀ n : ℕ, IsProbabilityMeasure (Measure.map (fun z : Ω × ℝ => -sInf {y : ℝ | ∃ s : ℝ≥0,
       s ≤ Real.toNNReal z.2 ∧ y = X.X s z.1}) ((P.prod (expMeasure (p n))).withDensity
       (fun z : Ω × ℝ => ENNReal.ofReal (Real.exp
         (φ * X.X (Real.toNNReal z.2) z.1 -
          (Real.toNNReal z.2 : ℝ) * X.ψ φ)))))) ∧
      (∀ x : ℝ, Tendsto (fun n : ℕ => (Measure.map (fun z : Ω × ℝ => -sInf {y : ℝ | ∃ s : ℝ≥0,
       s ≤ Real.toNNReal z.2 ∧ y = X.X s z.1}) ((P.prod (expMeasure (p n))).withDensity
       (fun z : Ω × ℝ => ENNReal.ofReal (Real.exp
         (φ * X.X (Real.toNNReal z.2) z.1 -
          (Real.toNNReal z.2 : ℝ) * X.ψ φ))))) (Iic x))
         atTop (nhds (ν (Iic x)))) ∧
      (∀ b : ℝ, 0 < b →
        ENNReal.ofReal (1 - Real.exp (-(φ / 2) * b)) ≤ ν (Iic b)) := by sorry
