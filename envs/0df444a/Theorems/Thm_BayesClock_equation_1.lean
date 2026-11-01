-- Prove2me | Theorems.Thm_BayesClock_equation_1
-- name    : BayesClock.equation_1
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T09:15:12.22921+00:00
-- url     : https://prove2.me/theorems/57697d5f-0475-488b-ba6a-c45682ffafb1
-- title:
--   Equation (1): $\mathrm{OPT}=\mathbb E[\max_{S\in\mathcal S}\sum_{i\in S}v_i]\le\mathrm{LOW}+\mathrm{HIGH}$
-- statement:
--   For a downward-closed constraint $\mathcal F$ with maximal sets $\mathcal S$, independent values, and any family of thresholds $(t_S)_S$,
--
--   $$\mathrm{OPT}=\mathbb E\Big[\max_{S\in\mathcal S}\sum_{i\in S}v_i\Big]\le\mathbb E\Big[\max_{S\in\mathcal S}\sum_{i\in S}\min(v_i,t_S)\Big]+\mathbb E\Big[\max_{S\in\mathcal S}\sum_{i\in S}v_i\cdot\mathbb I[v_i>t_S]\Big].$$
--
--   The two terms on the right are LOW and HIGH. This is the low-high decomposition of the benchmark.
--
--   Differences from the source:
--   - encoding: values are amounts a buyer is willing to pay, with expectations written E → values in ℝ≥0, expectations as ℝ≥0∞-valued lower integrals; reason: the proof starts every integral at 0 and a bidder pays nothing by leaving; a lower integral agrees with the expectation of a nonnegative value
--   - generalization: finite means are implicit → arbitrary probability laws on [0, ∞), means may be ∞; reason: the case of finite means is a special case of the Lean statement
--   - generalization: the thresholds tS of §3.2 → an arbitrary family of thresholds t; reason: the argument at this step does not use the choice of tS; tS is one instance
-- source:
--   Feldman, Gkatzelis, Gravin & Schoepflin, Bayesian and Randomized Clock Auctions, arXiv:2202.09291v1, equation (1), p.8

import Mathlib
import Definitions.Def_BayesClock_IsDownwardClosed
import Definitions.Def_BayesClock_maximalSets
import Definitions.Def_BayesClock_OPT
import Definitions.Def_BayesClock_LowHighTerms

open MeasureTheory
open scoped NNReal ENNReal

namespace BayesClock

/-- Equation (1), Feldman et al., arXiv:2202.09291v1, p.8:
`OPT = E[max S ∈ 𝒮, ∑ i ∈ S, vᵢ] ≤ LOW + HIGH`.

**Formalization Note** The first clause is the bridge from `OPT` of §2, a maximum over `𝓕`, to the
maximum over the maximal sets `𝒮`. Both clauses hold for an arbitrary family of thresholds `t`. -/
theorem equation_1 {N : Type*} [Fintype N] [DecidableEq N] (𝓕 : Finset (Finset N))
    (h𝓕 : IsDownwardClosed 𝓕) (ν : N → Measure ℝ≥0) [∀ i, IsProbabilityMeasure (ν i)]
    (t : Finset N → ℝ≥0) :
    OPT 𝓕 ν = ∫⁻ v, ⨆ S ∈ maximalSets 𝓕, ∑ i ∈ S, (v i : ℝ≥0∞) ∂Measure.pi ν ∧
      OPT 𝓕 ν ≤ LOW 𝓕 ν t + HIGH 𝓕 ν t := by sorry

end BayesClock
