-- Prove2me | Theorems.Thm_AvramDividend_Classical_levy_rightCont_indep_from_sequence
-- name    : AvramDividend.Classical.levy_rightCont_indep_from_sequence
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-19T18:06:09.160441+00:00
-- url     : https://prove2.me/theorems/5a23ae7b-5b41-44f2-8a64-544d5e3126fd
-- title:
--   Transfer Lévy increment independence to a right-continuous past using time approximations
-- statement:
--   Given deterministic times s,t and a sequence u_n of times in (s,t] converging to s from the right, the increment X_t-X_s of the published spectrally negative Lévy process is independent of the right-continuous filtration F_{s+}. The proof combines three already-Proved results: shifted increment independence from F_{s+}, right-continuous convergence of shifted increments, and independence preserved under pointwise limits of ambient-measurable real random variables. This is a substantive independent-increments bridge, not a sketch of the eventual stochastic dividend verification bound.
-- source:
--   Pinned Mathlib; Proved AvramDividend.Classical.levy_future_increment_indep_rightCont_prior, levy_increment_right_limit and independence_of_ambient_pointwise_limit_real.

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_levy_future_increment_indep_rightCont_prior
import Theorems.Thm_AvramDividend_Classical_levy_increment_right_limit
import Theorems.Thm_AvramDividend_Classical_independence_of_ambient_pointwise_limit_real

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.levy_rightCont_indep_from_sequence
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (s t : ℝ≥0)
    (u : ℕ → ℝ≥0) (hsu : ∀ n, s < u n)
    (hut : ∀ n, u n ≤ t)
    (hlim : Tendsto u atTop (𝓝[>] s)) :
    Indep
      (MeasurableSpace.comap (fun ω => X.X t ω - X.X s ω) inferInstance)
      (𝓕.rightCont s) P := by sorry
