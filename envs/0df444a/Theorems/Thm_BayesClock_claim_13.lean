-- Prove2me | Theorems.Thm_BayesClock_claim_13
-- name    : BayesClock.claim_13
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T09:15:32.861643+00:00
-- url     : https://prove2.me/theorems/76fcbd51-7b0b-4786-be3d-c4ff546fd50e
-- title:
--   Claim 13: $\mathrm{HIGH\text-TAIL}\le\mathbb E_v[\mathrm{auc}_o(v)]=\max_{S\in\mathcal S}\sum_{i\in S}\mathbb E[v_i]$
-- statement:
--   Let $\mathcal F$ be downward-closed with $k\ge2$ maximal sets, the values independent, and let $t_S$ be the thresholds of §3.2. The auction $\mathrm{auc}_o$ exists, and every such auction satisfies
--
--   $$\mathrm{HIGH\text-TAIL}\le\mathbb E_v[\mathrm{auc}_o(v)]=\max_{S\in\mathcal S}\sum_{i\in S}\mathbb E[v_i].$$
--
--   So the zero-price auction covers the tail of the high part.
--
--   Differences from the source:
--   - reading: k unrestricted, tS the solution of E[|S(tS, v)|] = log k → 2 ≤ k and tS the least t with E[|S(t, v)|] ≤ log k (footnote 2); reason: at k = 1, log k = 0 and footnote 2 gives no threshold, so the printed step has no content; there is one maximal set and theorem_1 is immediate
--   - encoding: values are amounts a buyer is willing to pay, with expectations written E → values in ℝ≥0, expectations as ℝ≥0∞-valued lower integrals; reason: the proof starts every integral at 0 and a bidder pays nothing by leaving; a lower integral agrees with the expectation of a nonnegative value
--   - generalization: finite means are implicit → arbitrary probability laws on [0, ∞), means may be ∞; reason: the case of finite means is a special case of the Lean statement
-- source:
--   Feldman, Gkatzelis, Gravin & Schoepflin, Bayesian and Randomized Clock Auctions, arXiv:2202.09291v1, Claim 13, §A.3, p.21

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

/-- Claim 13, Feldman et al., arXiv:2202.09291v1, §A.3, p.21:
`HIGH-TAIL ≤ E_v[auc_o(v)] = max S ∈ 𝒮, ∑ i ∈ S, E[vᵢ]`.

**Formalization Note** The auction `auc_o` exists (first clause) and every auction of that form
satisfies the identity and the inequality (second clause). `HIGH-TAIL` is taken at the thresholds
`tS`, and `2 ≤ k`, because `tS` is defined only then. -/
theorem claim_13 {N : Type*} [Fintype N] [DecidableEq N] (𝓕 : Finset (Finset N))
    (h𝓕 : IsDownwardClosed 𝓕) (ν : N → Measure ℝ≥0) [∀ i, IsProbabilityMeasure (ν i)]
    (hk : 2 ≤ (maximalSets 𝓕).card) :
    (∃ a₀ : SinglePriceAuction 𝓕, IsZeroPriceAuction 𝓕 ν a₀) ∧
      ∀ a₀ : SinglePriceAuction 𝓕, IsZeroPriceAuction 𝓕 ν a₀ →
        HIGH_TAIL 𝓕 ν (thresholds 𝓕 ν) ≤ a₀.expectedWelfare ν ∧
          a₀.expectedWelfare ν = ⨆ S ∈ maximalSets 𝓕, ∑ i ∈ S, expectedValue (ν i) := by sorry

end BayesClock
