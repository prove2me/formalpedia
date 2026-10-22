-- Prove2me | Theorems.Thm_AvramDividend_Classical_simple_reserve_adapted_L1_approximants
-- name    : AvramDividend.Classical.simple_reserve_adapted_L1_approximants
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-21T18:21:57.375344+00:00
-- url     : https://prove2.me/theorems/9b1915ea-bc34-4faa-ab73-750c679b02ce
-- title:
--   Canonical finite-valued adapted reserve approximations converging in ordinary L1
-- statement:
--   Let Z be an integrable real-valued reserve measurable at observation time s for a filtration. The canonical Mathlib SimpleFunc.approxOn approximations constructed from Z are all measurable in the past filtration sigma-algebra and converge to Z in ordinary L1 norm under P. Combine the already Proved L1 convergence theorem simple_reserve_approxOn_real_L1 with the separately published adaptedness preservation theorem simple_reserve_approxOn_preserves_adaptedness. This supplies the adapted approximants needed by the general-reserve Lévy conditional Markov limit. It does not establish joint payoff integrability or a stopped generator inequality.
-- source:
--   Accepted simple_reserve_approxOn_real_L1 candidate 12844 and dependency-gated simple_reserve_approxOn_preserves_adaptedness publication request 0baf6cab-2f66-4481-8139-fcdb2352e920.

import Mathlib.MeasureTheory.Function.SimpleFuncDenseLp
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_simple_reserve_approxOn_preserves_adaptedness
import Theorems.Thm_AvramDividend_Classical_simple_reserve_approxOn_real_L1

open Filter MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.simple_reserve_adapted_L1_approximants
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (s : ℝ≥0) (Z : Ω → ℝ)
    (hZ : Measurable[𝓕 s] Z)
    (hZm : Measurable Z) (hI : Integrable Z P) :
    (∀ n : ℕ, Measurable[𝓕 s] (fun ω =>
      (SimpleFunc.approxOn Z hZm (Set.range Z ∪ {0}) 0
        (by simp) n) ω)) ∧
    Tendsto (fun n : ℕ =>
      ∫ ω, |(SimpleFunc.approxOn Z hZm
          (Set.range Z ∪ {0}) 0 (by simp) n) ω - Z ω| ∂P)
      atTop (nhds 0) := by sorry
