-- Prove2me | Theorems.Thm_Erdos970_Mertens_sum_M_eq_summand_le_jb247
-- name    : Erdos970.Mertens.sum_M_eq_summand_le_jb247
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-11T18:46:13.144205+00:00
-- url     : https://prove2.me/theorems/1c43d485-991b-402a-9b00-62ab6cca043d
-- title:
--   Erdos970.Mertens.sum_M_eq_summand_le_jb247: intermediate lemma from OpenAI, A quadratic bound for Jacobsthal's function (result family 21)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Erdos970.Erdos970Final.erdos_970_iterated_log`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *A quadratic bound for Jacobsthal's function (result family 21)*, OpenAI Math Release, September 25, 2026, result family 21, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `Erdos970.Mertens`, with `open OAI`, `open _root_.Real _root_.Finset _root_.Filter _root_.Asymptotics _root_.Topology`, `open _root_.ArithmeticFunction hiding log`):
--
--   ```lean
--   lemma sum_M_eq_summand_le_jb247 {N : ℕ} (hN : 0 < N) :
--       |∑ n ∈ range N, M_eq_summand n - (M - γ)| ≤ 4 / N
--   ```
--
--   **Definitions.** The statement is written with `Erdos970.Mertens.M`, `Erdos970.Mertens.M_eq_summand` and `Erdos970.Mertens.γ` (definitions bundle `OAIQ247J001` of this split).
--
--   **Used by.** The proofs of `OAI_Erdos970_ErdosContinuousAnomaly_boundaryProduct_tendsto_half_jb247`, `OAI.Erdos970.ErdosContinuousAnomaly.common_anomaly_exponential_jb247`, `OAI.Erdos970.ErdosContinuousAnomaly.weighted_anomaly_convergence_jb247`, `OAI_Erdos970_ErdosInverseSampleCost_source_expected_cost_small_jb247`, `OAI.Erdos970.ErdosInverseSampleCost.source_good_sample_jb247`, `OAI_Erdos970_ErdosRandomVariance_stable_source_chebyshev_jb247`, `OAI_Erdos970_ErdosSourceReferenceMargin_root_nodeBenchmark_tendsto_jb247`, `OAI.Erdos970.ErdosStoppedArithmetic.moving_subbin_actual_pair_lower_jb247`, `OAI.Erdos970.ErdosVarianceLargeMap.source_full_pattern_domination_jb247`, `OAI_Erdos970_ErdosVarianceLargeScale_source_large_pair_bound_jb247`, `OAI.Erdos970.ErdosVarianceSmallModel.source_residue_fibre_bound_jb247`, `OAI_Erdos970_ErdosVarianceUniformMoments_uniform_density_inverse_jb247`, `OAI.Erdos970.ErdosVarianceUniformMoments.uniform_model_chebyshev_jb247`, `OAI.Erdos970.ErdosVarianceWeighted.source_selection_hard_mass_jb247`, `OAI.Erdos970.EulerWeightedLower.uniformLowerEnvelope_limit_jb247`, `OAI.Erdos970.NumberTheoryLean.CanonicalKeyReference.moving_key_reference_jb247`, `OAI.Erdos970.NumberTheoryLean.HighGapResidual.high_gap_residual_power_jb247`, `OAI.Erdos970.NumberTheoryLean.HighResidualSum.high_residual_sum_bound_jb247`, `OAI.Erdos970.NumberTheoryLean.IteratedLogBound.of_source_root_lower_jb247`, `OAI_Erdos970_NumberTheoryLean_IteratedLogBudget_separation_jb247`, `OAI.Erdos970.NumberTheoryLean.LowStateResidualBound.low_state_normalized_residual_jb247`, `OAI_Erdos970_NumberTheoryLean_ReferenceIntervalBound_source_residual_split_bound_jb247`, `OAI_Erdos970_NumberTheoryLean_ReferenceProductLower_reference_product_lower_jb247`, `OAI_Erdos970_NumberTheoryLean_ReferenceResidualPointwise_source_residual_pointwise_jb247`, `OAI.Erdos970.NumberTheoryLean.ReferenceResidualSum.summed_source_residual_bound_jb247` and `OAI.Erdos970.NumberTheoryLean.SourceRootErrorLower.source_root_lower_with_stopped_correction_jb247` of this split import it.
-- source:
--   OpenAI, A quadratic bound for Jacobsthal's function (result family 21), OpenAI Math Release, September 25, 2026, https://github.com/openai/math (result family 21; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/A-quadratic-bound-for-Jacobsthals-function-September-25-2026/paper.pdf; Apache License 2.0)

import Mathlib
import Mathlib.Algebra.Group.Submonoid.BigOperators
import Mathlib.Algebra.Order.Field.GeomSum
import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
import Mathlib.Analysis.SpecialFunctions.Integrability.LogMeromorphic
import Mathlib.Analysis.SpecialFunctions.Log.Summable
import Mathlib.Analysis.SumIntegralComparisons
import Mathlib.NumberTheory.AbelSummation
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.EulerProduct.DirichletLSeries
import Mathlib.NumberTheory.EulerProduct.ExpLog
import Mathlib.NumberTheory.Harmonic.EulerMascheroni
import Mathlib.NumberTheory.Harmonic.GammaDeriv
import Mathlib.NumberTheory.LSeries.PrimesInAP
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Definitions.Def_OAIQ247J001

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

namespace Erdos970

namespace Mertens

open _root_.Real _root_.Finset _root_.Filter _root_.Asymptotics _root_.Topology
open _root_.ArithmeticFunction hiding log

attribute [fun_prop] measurable_from_top

lemma sum_M_eq_summand_le_jb247 {N : ℕ} (hN : 0 < N) :
    |∑ n ∈ range N, M_eq_summand n - (M - γ)| ≤ 4 / N := by
  sorry

end Mertens

end Erdos970
end
