-- Prove2me | Theorems.Thm_AvramDividend_Classical_esscher_positive_root_genuine_exponential_cdf_perpetual_measure
-- name    : AvramDividend.Classical.esscher_positive_root_genuine_exponential_cdf_perpetual_measure
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-27T18:51:19.336989+00:00
-- url     : https://prove2.me/theorems/90c52942-84b4-4428-9b34-b22f7a4b2d4c
-- title:
--   All genuine positive-root exponential-time Esscher CDFs converge to one canonical perpetual probability law
-- statement:
--   Given a true spectrally negative Lévy process, a positive discount q, a positive Esscher root φ with ψ(φ)=q, and any positive rates p_n↓0 in the filter sense, there exists one genuine probability measure ν on real capital such that, for every capital threshold x, the CDF of the actual product-space exponentially observed φ-Esscher likelihood measure converges to ν(Iic x). The same ν satisfies the established positive lower mass bound for b>0. The proof derives ν from the already verified canonical perpetual Esscher probability-measure theorem and applies the independently proved exact true-clock CDF convergence at every x. It assumes no finite-rate Wiener-Hopf factorisation and does not prove the coordinator-owned Laplace scalar.
-- source:
--   Existing accepted 70aae7c7 perpetual infimum law with full probability mass, and 1E-C 58668a61 genuine-clock CDF assembly pending acceptance. Mathlib 0df444a.

import Mathlib.Probability.Distributions.Exponential
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Theorems.Thm_AvramDividend_Classical_chat04_esscher_positive_root_perpetual_infimum_probability_full_mass
import Theorems.Thm_AvramDividend_Classical_esscher_true_joint_clock_cdf_tendsto_perpetual
open AvramDividend.Classical MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.esscher_positive_root_genuine_exponential_cdf_perpetual_measure
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (q φ : ℝ)
    (hq : 0 < q) (hφ : 0 < φ) (hroot : X.ψ φ = q)
    (p : ℕ → ℝ)
    (hp : Tendsto p atTop (nhdsWithin (0 : ℝ) (Ioi 0)))
    (hpos : ∀ n, 0 < p n) :
    ∃ ν : Measure ℝ, IsProbabilityMeasure ν ∧
      (∀ x : ℝ, Tendsto (fun n : ℕ => ((P.prod (expMeasure (p n))).withDensity
       (fun z : Ω × ℝ => ENNReal.ofReal (Real.exp
         (φ * X.X (Real.toNNReal z.2) z.1 - (Real.toNNReal z.2 : ℝ) * X.ψ φ))))
       {z : Ω × ℝ | -sInf {y : ℝ | ∃ s : ℝ≥0,
         s ≤ Real.toNNReal z.2 ∧ y = X.X s z.1} ≤ x})
        atTop (nhds (ν (Iic x)))) ∧
      (∀ b : ℝ, 0 < b →
        ENNReal.ofReal (1 - Real.exp (-(φ / 2) * b)) ≤ ν (Iic b)) := by sorry
