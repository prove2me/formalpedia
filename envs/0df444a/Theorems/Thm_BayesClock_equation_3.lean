-- Prove2me | Theorems.Thm_BayesClock_equation_3
-- name    : BayesClock.equation_3
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T09:15:13.122556+00:00
-- url     : https://prove2.me/theorems/c3ed58ac-bd87-443d-9065-40645f60f19e
-- title:
--   Equation (3): $\mathrm{LOW}\le\mathrm{LOW\text-CORE}+\mathrm{LOW\text-TAIL}$
-- statement:
--   For a downward-closed constraint, independent values, and any family of thresholds,
--
--   $$\mathrm{LOW}\le\mathrm{LOW\text-CORE}+\sum_{S\in\mathcal S}\sum_{i\in S}\mathbb E[v_i]\cdot\Pr\big[\exists x\in[0,t_S):|S(x,v)-\{i\}|>10\,\mathbb E_v[|S(x,v)|]\big].$$
--
--   The double sum is LOW-TAIL. The expectation inside the event is that of the whole set $S$, also after bidder $i$ is removed.
--
--   Differences from the source:
--   - encoding: values are amounts a buyer is willing to pay, with expectations written E → values in ℝ≥0, expectations as ℝ≥0∞-valued lower integrals; reason: the proof starts every integral at 0 and a bidder pays nothing by leaving; a lower integral agrees with the expectation of a nonnegative value
--   - generalization: finite means are implicit → arbitrary probability laws on [0, ∞), means may be ∞; reason: the case of finite means is a special case of the Lean statement
--   - generalization: the thresholds tS of §3.2 → an arbitrary family of thresholds t; reason: the argument at this step does not use the choice of tS; tS is one instance
-- source:
--   Feldman, Gkatzelis, Gravin & Schoepflin, Bayesian and Randomized Clock Auctions, arXiv:2202.09291v1, equation (3), p.10

import Mathlib
import Definitions.Def_BayesClock_IsDownwardClosed
import Definitions.Def_BayesClock_LowHighTerms

open MeasureTheory
open scoped NNReal ENNReal

namespace BayesClock

/-- Equation (3), Feldman et al., arXiv:2202.09291v1, p.10: `LOW ≤ LOW-CORE + LOW-TAIL`, where
`LOW-TAIL = ∑ S ∈ 𝒮, ∑ i ∈ S, E[vᵢ] · Pr[∃ x ∈ [0, tS) : |S(x, v) − {i}| > 10 E_v[|S(x, v)|]]`.

**Formalization Note** It holds for an arbitrary family of thresholds `t`. -/
theorem equation_3 {N : Type*} [Fintype N] [DecidableEq N] (𝓕 : Finset (Finset N))
    (h𝓕 : IsDownwardClosed 𝓕) (ν : N → Measure ℝ≥0) [∀ i, IsProbabilityMeasure (ν i)]
    (t : Finset N → ℝ≥0) :
    LOW 𝓕 ν t ≤ LOW_CORE 𝓕 ν t + LOW_TAIL 𝓕 ν t := by sorry

end BayesClock
