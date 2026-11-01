-- Prove2me | Theorems.Thm_BayesClock_equation_2
-- name    : BayesClock.equation_2
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T09:15:19.350863+00:00
-- url     : https://prove2.me/theorems/4b7aa92c-61e4-4606-9efd-0e47a46a71b3
-- title:
--   Equation (2): $\mathrm{HIGH}\le\mathrm{HIGH\text-CORE}+\mathrm{HIGH\text-TAIL}$
-- statement:
--   For a downward-closed constraint with $k$ maximal sets, independent values, and any family of thresholds,
--
--   $$\mathrm{HIGH}\le\mathrm{HIGH\text-CORE}+\sum_{S\in\mathcal S}\sum_{i\in S}\mathbb E[v_i]\cdot\Pr_v\big[|S(t_S,v)-\{i\}|>10\log k\big].$$
--
--   The double sum is HIGH-TAIL. The core keeps only those realizations in which at most $10\log k+1$ bidders of $S$ lie above the threshold.
--
--   Differences from the source:
--   - encoding: values are amounts a buyer is willing to pay, with expectations written E → values in ℝ≥0, expectations as ℝ≥0∞-valued lower integrals; reason: the proof starts every integral at 0 and a bidder pays nothing by leaving; a lower integral agrees with the expectation of a nonnegative value
--   - generalization: finite means are implicit → arbitrary probability laws on [0, ∞), means may be ∞; reason: the case of finite means is a special case of the Lean statement
--   - generalization: the thresholds tS of §3.2 → an arbitrary family of thresholds t; reason: the argument at this step does not use the choice of tS; tS is one instance
-- source:
--   Feldman, Gkatzelis, Gravin & Schoepflin, Bayesian and Randomized Clock Auctions, arXiv:2202.09291v1, equation (2), p.9

import Mathlib
import Definitions.Def_BayesClock_IsDownwardClosed
import Definitions.Def_BayesClock_LowHighTerms

open MeasureTheory
open scoped NNReal ENNReal

namespace BayesClock

/-- Equation (2), Feldman et al., arXiv:2202.09291v1, p.9: `HIGH ≤ HIGH-CORE + HIGH-TAIL`, where
`HIGH-TAIL = ∑ S ∈ 𝒮, ∑ i ∈ S, E[vᵢ] · Pr_v[|S(tS, v) − {i}| > 10 log k]`.

**Formalization Note** It holds for an arbitrary family of thresholds `t`; the event of `HIGH-TAIL`
does not depend on bidder `i`, which is where the independence of the coordinates is used. -/
theorem equation_2 {N : Type*} [Fintype N] [DecidableEq N] (𝓕 : Finset (Finset N))
    (h𝓕 : IsDownwardClosed 𝓕) (ν : N → Measure ℝ≥0) [∀ i, IsProbabilityMeasure (ν i)]
    (t : Finset N → ℝ≥0) :
    HIGH 𝓕 ν t ≤ HIGH_CORE 𝓕 ν t + HIGH_TAIL 𝓕 ν t := by sorry

end BayesClock
