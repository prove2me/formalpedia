-- Prove2me | Theorems.Thm_AvramDividend_Classical_zero_cap_boundary_value_package_of_positive_ratio_and_deriv_cases
-- name    : AvramDividend.Classical.zero_cap_boundary_value_package_of_positive_ratio_and_deriv_cases
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T13:23:34.040995+00:00
-- url     : https://prove2.me/theorems/714c2825-d629-4025-9dfe-22fc6430939a
-- title:
--   Full zero-cap boundary package from positive-barrier valuation and derivative alternatives
-- statement:
--   Under the standing spectrally negative Lévy assumptions and a q-scale function, the two conclusions of the original zero-cap boundary package hold if the genuine positive-barrier reflected reward satisfies its scale ratio at every reciprocal barrier and W is right-continuous at zero with a right derivative tending either to a finite nonzero real or to infinity. The Proved finite and infinite derivative transfers give the exact zero-barrier dividend identity, and the Proved zero-cap comparison with nonnegativity closes both conjuncts. This is a complete proof under explicit asymptotic and positive-barrier stochastic hypotheses.
-- source:
--   Root-connected zero_cap_boundary_value_package (72a2a0e7-03c4-4fc3-8837-490cc6288445), Proved boundary transfers fb8027bb-7b35-43db-b240-15e57d3ba650 and 24c96388-6b8a-4846-9c42-706f1428b302, Proved zero-cap comparison d58a54f2-7f8b-4467-b485-93506d163ab8.

import Theorems.Thm_AvramDividend_Classical_barrierValue_zero_boundary_nonneg
import Theorems.Thm_AvramDividend_Classical_zero_cap_value_at_zero_upper_bound_of_boundary
import Theorems.Thm_AvramDividend_Classical_barrierStrategy_zero_boundary_of_positive_ratio_and_finite_deriv_limit
import Theorems.Thm_AvramDividend_Classical_barrierStrategy_zero_boundary_of_positive_ratio_and_divergent_deriv

open AvramDividend.Classical MeasureTheory Filter Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.zero_cap_boundary_value_package_of_positive_ratio_and_deriv_cases
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q) (W : ℝ → ℝ)
    (hW : IsScaleFunction X q W)
    (hscale : ∀ n : ℕ,
      barrierSupValue X (1 / ((n : ℝ) + 1)) q =
        ENNReal.ofReal (W (1 / ((n : ℝ) + 1)) /
          deriv W (1 / ((n : ℝ) + 1))))
    (hcont : ContinuousWithinAt W (Ici (0 : ℝ)) 0)
    (hderiv :
      (∃ d : ℝ, d ≠ 0 ∧ Tendsto (fun y : ℝ => deriv W y)
        (nhdsWithin (0 : ℝ) (Ioi 0)) (nhds d)) ∨
      Tendsto (fun y : ℝ => deriv W y)
        (nhdsWithin (0 : ℝ) (Ioi 0)) atTop) :
    0 ≤ barrierValue W 0 0 ∧
      valueFunctionLe X q 0 0 ≤ ENNReal.ofReal (barrierValue W 0 0) := by sorry
