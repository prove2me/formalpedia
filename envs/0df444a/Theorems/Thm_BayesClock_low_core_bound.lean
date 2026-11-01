-- Prove2me | Theorems.Thm_BayesClock_low_core_bound
-- name    : BayesClock.low_core_bound
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T09:15:17.286988+00:00
-- url     : https://prove2.me/theorems/65d57afc-c9e8-4976-bcde-b1cbc7fa09dd
-- title:
--   Bound on $\mathrm{LOW\text-CORE}$: $\mathrm{LOW\text-CORE}\le11\max_{S}\mathbb E_v[\sum_{i\in S}v_i]$
-- statement:
--   Let $\mathcal F$ be downward-closed with $k\ge2$ maximal sets, the values independent, and let $t_S$ be the thresholds of §3.2. Then
--
--   $$\mathrm{LOW\text-CORE}\le11\max_{S\in\mathcal S}\mathbb E_v\Big[\sum_{i\in S}v_i\Big].$$
--
--   It says the core of LOW is at most a constant multiple of the best fixed set's expected value. The logarithm in $t_S$ is base 2, so $\mathbb E_v[|S(x,v)|]\ge\log k\ge1$ on $[0,t_S)$, which is the printed step $10\,\mathbb E+1\le11\,\mathbb E$.
--
--   Differences from the source:
--   - reading: k unrestricted, tS the solution of E[|S(tS, v)|] = log k → 2 ≤ k and tS the least t with E[|S(t, v)|] ≤ log k (footnote 2); reason: at k = 1, log k = 0 and footnote 2 gives no threshold, so the printed step has no content; there is one maximal set and theorem_1 is immediate
--   - encoding: values are amounts a buyer is willing to pay, with expectations written E → values in ℝ≥0, expectations as ℝ≥0∞-valued lower integrals; reason: the proof starts every integral at 0 and a bidder pays nothing by leaving; a lower integral agrees with the expectation of a nonnegative value
--   - generalization: finite means are implicit → arbitrary probability laws on [0, ∞), means may be ∞; reason: the case of finite means is a special case of the Lean statement
-- source:
--   Feldman, Gkatzelis, Gravin & Schoepflin, Bayesian and Randomized Clock Auctions, arXiv:2202.09291v1, Section 3.2, p.10, display ending "= 11 max"

import Mathlib
import Definitions.Def_BayesClock_IsDownwardClosed
import Definitions.Def_BayesClock_maximalSets
import Definitions.Def_BayesClock_thresholds
import Definitions.Def_BayesClock_LowHighTerms

open MeasureTheory
open scoped NNReal ENNReal

namespace BayesClock

/-- The bound on `LOW-CORE`, Feldman et al., arXiv:2202.09291v1, Section 3.2, p.10: the display ending
`… = 11 max S ∈ 𝒮, E_v[∑ i ∈ S, vᵢ]`.

**Formalization Note** `LOW-CORE` is taken at the thresholds `tS`, and `2 ≤ k`, because `tS` is
defined only then. With the paper's base-2 logarithm, `E_v[|S(x, v)|] ≥ log k ≥ 1` on `[0, tS)` for
every `k ≥ 2`, which is the printed step `10 E + 1 ≤ 11 E`. -/
theorem low_core_bound {N : Type*} [Fintype N] [DecidableEq N] (𝓕 : Finset (Finset N))
    (h𝓕 : IsDownwardClosed 𝓕) (ν : N → Measure ℝ≥0) [∀ i, IsProbabilityMeasure (ν i)]
    (hk : 2 ≤ (maximalSets 𝓕).card) :
    LOW_CORE 𝓕 ν (thresholds 𝓕 ν) ≤
      11 * ⨆ S ∈ maximalSets 𝓕, ∫⁻ v, ∑ i ∈ S, (v i : ℝ≥0∞) ∂Measure.pi ν := by sorry

end BayesClock
