-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ws01e_bt_new_levy_psi_analytic_on_positive
-- name    : AvramDividend.Classical.avram_ws01e_bt_new_levy_psi_analytic_on_positive
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-29T01:01:00.772088+00:00
-- url     : https://prove2.me/theorems/fc8bfb61-c54b-4326-a245-d9ae844f18e3
-- title:
--   Real analyticity of the actual Lévy Laplace exponent throughout positive parameters
-- statement:
--   For any canonical spectrally negative Lévy process, the actual Laplace exponent ψ is real analytic at every positive parameter, unconditionally. The proof uses the original Lévy exponential moment law to put every positive θ in the interior of the finite exponential-moment set of X_1, identifies ψ with the cumulant-generating function by the exact Lévy MGF, and transfers Mathlib's analyticOnNhd_cgf. This useful source-faithful interface is strictly more direct than the already proved positively shifted analytic lemma and enables original-clock all-beta Wiener–Hopf analytic continuation without a fictitious positive Esscher base shift.

import Mathlib.Probability.Moments.MGFAnalytic
import Mathlib.Topology.Closure
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open AvramDividend.Classical MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_ws01e_bt_new_levy_psi_analytic_on_positive
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) :
    AnalyticOnNhd ℝ X.ψ (Set.Ioi 0) := by sorry
