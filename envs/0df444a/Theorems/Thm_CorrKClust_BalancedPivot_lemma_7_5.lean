-- Prove2me | Theorems.Thm_CorrKClust_BalancedPivot_lemma_7_5
-- name    : CorrKClust.BalancedPivot.lemma_7_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T20:45:57.709971+00:00
-- url     : https://prove2.me/theorems/3b54f900-5639-4e58-b143-6e2bf69aa4d1
-- title:
--   Lemma 7.5 — projected pivot cluster size is predictable
-- statement:
--   For any graph with $n\ge2$ and any real $c>0$, the probability that there are a time $1\le t\le n$ and a vertex $v$ arriving by t, chosen as a pivot, with
--   $$p_n(v)\ge\frac{4np_t(v)}t+\frac{2cn\ln n}t+1$$
--   is at most $n^{2-c/8}$. The event ranges simultaneously over every vertex and every valid time; $p_t(v)$ counts arrivals in v's pivot cluster by t.
--
--   This estimate controls final mass using the observed partial cluster size, with exactly the paper's threshold and exponent.
--
--   Differences from the source:
--   - encoding: finite vertex set and unordered disagreements → Fintype V, SimpleGraph V, maps to labels, and unordered distinct Sym2 pairs; reason: decidable equality is classical data and no finite graph or clustering is excluded
--   - encoding: uniform random arrival order → the finite average over all bijections Fin (card V) ≃ V; reason: there are exactly n! such bijections, each with equal weight
--   - encoding: n ≥ 2 for the remainder of §7.3.2–§7.3.4, p. 30 → 2 ≤ Fintype.card V; reason: this is the stated standing assumption, ensuring positive natural logarithms and denominators
-- source:
--   Mahsa Derakhshan, Andisheh Ghasemi, Rajmohan Rajaraman, Omer Wasim, Tegan Wilson, STOC 2027 submission #302 (October 2026), Lemma 7.5, p. 31, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/302.pdf

import Definitions.Def_CorrKClust_BalancedPivot_Analysis

set_option autoImplicit false
open Classical
noncomputable section

namespace CorrKClust.BalancedPivot

/-- Lemma 7.5, p. 31: simultaneous over vertices and valid times. -/
theorem lemma_7_5 {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) (hn : 2 ≤ Fintype.card V) (c : ℝ) (hc : 0 < c) :
    probability (fun σ : ArrivalOrder V => ∃ (t : ℕ) (v : V),
      1 ≤ t ∧ t ≤ Fintype.card V ∧ arrivalTime σ v ≤ t ∧ v ∈ pivots G σ ∧
      4 * (Fintype.card V : ℝ) * pivotSize G σ t v / t +
        2 * c * Fintype.card V * Real.log (Fintype.card V) / t + 1 ≤ (finalSize G σ v : ℝ)) ≤
      Real.rpow (Fintype.card V : ℝ) (2 - c / 8) := by sorry

end CorrKClust.BalancedPivot
