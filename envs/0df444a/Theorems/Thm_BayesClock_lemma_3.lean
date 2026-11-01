-- Prove2me | Theorems.Thm_BayesClock_lemma_3
-- name    : BayesClock.lemma_3
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T09:14:59.228559+00:00
-- url     : https://prove2.me/theorems/db500eb3-581a-469f-9675-e2eb15535cb1
-- title:
--   Lemma 3: some uniform price gives $\Delta\le C(1+\log m)\cdot W(p)$
-- statement:
--   There is an absolute constant $C>0$ with the following property. For every downward-closed constraint with maximal sets $\mathcal S$, all independent values, every family of thresholds $(t_S)_S$ and every positive integer $m$, with
--
--   $$\Delta=\mathbb E\Big[\max_{S\in\mathcal S}\sum_{i\in S}\hat v_i\cdot\mathbb I\big[|S(t_S,v)|\le m\big]\Big],$$
--
--   there is a uniform price $p$ such that
--
--   $$\Delta\le C(1+\log m)\cdot\mathbb E\Big[\max_{S\in\mathcal S}\sum_{i\in S}\mathbb E[v_i\mid v_i\ge p]\cdot\mathbb I[v_i\ge p]\Big].$$
--
--   With $m=\lfloor10\log k+1\rfloor$ this handles HIGH-CORE and is the source of the factor $\log\log k$.
--
--   Differences from the source:
--   - reading: O(log m) for any positive integer m → C(1 + log m) with C absolute; reason: the literal factor is 0 at m = 1, where the claim is false: one bidder of value 1 a.s., thresholds 0, gives Δ = 1
--   - generalization: the thresholds tS → an arbitrary family of thresholds t; reason: §3.3, p.12 says the lemma holds for any threshold; tS is one instance
--   - encoding: log m in base 2 → Real.log m (natural); reason: log₂ m = ln m / ln 2, so C(1 + log₂ m) and C'(1 + ln m) bound each other with C' = C / ln 2; C is existential
--   - encoding: values are amounts a buyer is willing to pay, with expectations written E → values in ℝ≥0, expectations as ℝ≥0∞-valued lower integrals; reason: the proof starts every integral at 0 and a bidder pays nothing by leaving; a lower integral agrees with the expectation of a nonnegative value
--   - generalization: finite means are implicit → arbitrary probability laws on [0, ∞), means may be ∞; reason: the case of finite means is a special case of the Lean statement
-- source:
--   Feldman, Gkatzelis, Gravin & Schoepflin, Bayesian and Randomized Clock Auctions, arXiv:2202.09291v1, Lemma 3, p.10; proof in §A.1, p.20; §3.3, p.12 ("Lemma 3 holds for any threshold tS")

import Mathlib
import Definitions.Def_BayesClock_IsDownwardClosed
import Definitions.Def_BayesClock_LowHighTerms
import Definitions.Def_BayesClock_uniformPriceValue

open MeasureTheory
open scoped NNReal ENNReal

namespace BayesClock

/-- Lemma 3, Feldman et al., arXiv:2202.09291v1, p.10, proved in §A.1, p.20: for every positive
integer `m` there is a uniform price `p` with
`Δ ≤ O(log m) · E[max S ∈ 𝒮, ∑ i ∈ S, E[vᵢ | vᵢ ≥ p] · I[vᵢ ≥ p]]`.

**Formalization Note** The constant `C` is absolute: it comes before the bidders, the constraint and
the laws. `O(log m)` is read as `C (1 + log m)`, because the literal factor `log 1 = 0` makes the
claim false at `m = 1`: for one bidder of value `1`, thresholds `0` and `m = 1`, `Δ = 1`. The thresholds
are arbitrary, as §3.3, p.12 says ("Lemma 3 holds for any threshold tS"). -/
theorem lemma_3 :
    ∃ C : ℝ, 0 < C ∧
      ∀ (N : Type*) [Fintype N] [DecidableEq N] (𝓕 : Finset (Finset N)),
        IsDownwardClosed 𝓕 →
        ∀ (ν : N → Measure ℝ≥0) [∀ i, IsProbabilityMeasure (ν i)] (t : Finset N → ℝ≥0) (m : ℕ),
          1 ≤ m →
          ∃ p : ℝ≥0,
            Delta 𝓕 ν t m ≤
              ENNReal.ofReal (C * (1 + Real.log m)) * uniformPriceValue 𝓕 ν p := by sorry

end BayesClock
