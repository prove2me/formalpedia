-- Prove2me | Theorems.Thm_BayesClock_claim_14
-- name    : BayesClock.claim_14
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T09:15:37.122739+00:00
-- url     : https://prove2.me/theorems/9a81adbd-f299-4a72-9063-c13d67da0ac4
-- title:
--   Claim 14: $\mathrm{LOW}\le12\cdot\mathbb E_v[\mathrm{auc}_o(v)]=12\cdot\max_{S\in\mathcal S}\sum_{i\in S}\mathbb E[v_i]$
-- statement:
--   Let $\mathcal F$ be downward-closed with $k\ge2$ maximal sets, the values independent, $t_S$ the thresholds of §3.2, and $\mathrm{auc}_o$ a zero-price auction. Then
--
--   $$\mathrm{LOW}\le12\cdot\mathbb E_v[\mathrm{auc}_o(v)]=12\cdot\max_{S\in\mathcal S}\sum_{i\in S}\mathbb E[v_i].$$
--
--   So the zero-price auction is a constant-factor approximation to the low part of the benchmark.
--
--   Differences from the source:
--   - reading: k unrestricted, tS the solution of E[|S(tS, v)|] = log k → 2 ≤ k and tS the least t with E[|S(t, v)|] ≤ log k (footnote 2); reason: at k = 1, log k = 0 and footnote 2 gives no threshold, so the printed step has no content; there is one maximal set and theorem_1 is immediate
--   - encoding: values are amounts a buyer is willing to pay, with expectations written E → values in ℝ≥0, expectations as ℝ≥0∞-valued lower integrals; reason: the proof starts every integral at 0 and a bidder pays nothing by leaving; a lower integral agrees with the expectation of a nonnegative value
--   - generalization: finite means are implicit → arbitrary probability laws on [0, ∞), means may be ∞; reason: the case of finite means is a special case of the Lean statement
-- source:
--   Feldman, Gkatzelis, Gravin & Schoepflin, Bayesian and Randomized Clock Auctions, arXiv:2202.09291v1, Claim 14, §A.3, p.21

import Mathlib
import Definitions.Def_BayesClock_IsDownwardClosed
import Definitions.Def_BayesClock_maximalSets
import Definitions.Def_BayesClock_SinglePriceAuction
import Definitions.Def_BayesClock_thresholds
import Definitions.Def_BayesClock_expectedValue
import Definitions.Def_BayesClock_IsZeroPriceAuction
import Definitions.Def_BayesClock_LowHighTerms

open MeasureTheory
open scoped NNReal ENNReal

namespace BayesClock

/-- Claim 14, Feldman et al., arXiv:2202.09291v1, §A.3, p.21:
`LOW ≤ 12 · E_v[auc_o(v)] = 12 · max S ∈ 𝒮, ∑ i ∈ S, E[vᵢ]`.

**Formalization Note** `LOW` is taken at the thresholds `tS`, and `2 ≤ k`. -/
theorem claim_14 {N : Type*} [Fintype N] [DecidableEq N] (𝓕 : Finset (Finset N))
    (h𝓕 : IsDownwardClosed 𝓕) (ν : N → Measure ℝ≥0) [∀ i, IsProbabilityMeasure (ν i)]
    (hk : 2 ≤ (maximalSets 𝓕).card) (a₀ : SinglePriceAuction 𝓕)
    (ha₀ : IsZeroPriceAuction 𝓕 ν a₀) :
    LOW 𝓕 ν (thresholds 𝓕 ν) ≤ 12 * a₀.expectedWelfare ν ∧
      12 * a₀.expectedWelfare ν = 12 * ⨆ S ∈ maximalSets 𝓕, ∑ i ∈ S, expectedValue (ν i) := by sorry

end BayesClock
