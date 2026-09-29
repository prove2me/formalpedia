-- Prove2me | Theorems.Thm_Concentration_hoeffding_two_sided
-- name    : Concentration.hoeffding_two_sided
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-21T06:14:59.306324+00:00
-- url     : https://prove2.me/theorems/ee322cc7-d658-4ccb-ab4a-6f5d7c4a423e
-- title:
--   Hoeffding's inequality for sums of independent bounded random variables
-- statement:
--   **Hoeffding's inequality**, in two-sided form, bounds the probability that a sum of independent
--   bounded random variables deviates from its mean.
--
--   $$\mathbb{P}\Bigl(\Bigl|\sum_{i \in s} X_i - \sum_{i \in s} \mathbb{E}[X_i]\Bigr| \ge \varepsilon\Bigr)
--   \;\le\; 2\exp\left(\frac{-\varepsilon^2}{2\sum_{i \in s} \bigl(\tfrac{h_i - l_i}{2}\bigr)^2}\right)$$
--
--   Here $(X_i)_{i \in \iota}$ are independent real random variables on a probability space, $s$ is a
--   finite index set, and each $X_i$ lies almost surely in the interval $[l_i, h_i]$. The deviation
--   $\varepsilon \ge 0$ is arbitrary.
--
--   The content is that boundedness alone forces **subgaussian** tails: the probability of a deviation
--   of size $\varepsilon$ decays like $\exp(-\varepsilon^2 / 2v)$, where $v = \sum_i ((h_i-l_i)/2)^2$
--   plays the role of a variance proxy. No assumption on the distributions is needed beyond
--   independence and the range constraint. Chebyshev's inequality would give only polynomial decay;
--   Hoeffding upgrades this to Gaussian-type decay, which is what makes it the workhorse of
--   concentration of measure. It underlies the standard generalisation bounds in statistical learning
--   theory, the analysis of randomised algorithms, and empirical-process arguments throughout
--   probability and statistics.
--
--   **Formalization note.** Independence is Mathlib's `iIndepFun`, the almost-sure range constraint is
--   stated with `∀ᵐ ω ∂μ, X i ω ∈ Set.Icc (lo i) (hi i)`, and the conclusion is phrased with
--   `Measure.real` so that the bound is an inequality between real numbers. The variance proxy is
--   accumulated in `ℝ≥0` and cast to `ℝ`. Only Mathlib is required.
-- source:
--   Hoeffding's inequality. Lean proof from the Salt project by Jason Hickey, Salt/Entropy/Chowla/Concentration.lean (https://github.com/jyh/salt, Apache-2.0).

import Mathlib

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace Concentration

/-- Hoeffding's inequality, two-sided: a sum of independent bounded random variables
concentrates around its mean with subgaussian tails. -/
theorem hoeffding_two_sided {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {ι : Type*} {X : ι → Ω → ℝ}
    (h_indep : iIndepFun X μ) {s : Finset ι} {lo hi : ι → ℝ}
    (h_meas : ∀ i, AEMeasurable (X i) μ)
    (h_bdd : ∀ i, ∀ᵐ ω ∂μ, X i ω ∈ Set.Icc (lo i) (hi i)) {ε : ℝ} (hε : 0 ≤ ε) :
    μ.real {ω | ε ≤ |(∑ i ∈ s, X i ω) - ∑ i ∈ s, μ[X i]|}
      ≤ 2 * Real.exp (-ε ^ 2 /
          (2 * ((∑ i ∈ s, (‖hi i - lo i‖₊ / 2) ^ 2 : ℝ≥0) : ℝ))) := by
  sorry

end Concentration
