-- Prove2me | Theorems.Thm_CorrKClust_BalancedPivot_lemma_7_7
-- name    : CorrKClust.BalancedPivot.lemma_7_7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T20:45:53.93576+00:00
-- url     : https://prove2.me/theorems/fe0c5b60-04fe-4229-b6e1-84dcfa448b77
-- title:
--   Lemma 7.7 — pivot cluster size at an arbitrary instant
-- statement:
--   Fix a graph on $n\ge2$ vertices, a vertex $v$, integers $1\le j\le t\le n$, and a real $c>0$. Let $A=\{v\text{ is a pivot},t_v=j\}$. Then
--   $$\Pr\!\left[A\cap\left\{p_t(v)>1+\frac{2p_n(v)t}{n}+c\ln n\right\}\right]\le n^{-c/3}\Pr(A).$$
--   This is the conditional bound given that v is a pivot arriving at j, without dividing by a possibly zero probability. The proof on p. 33 establishes the bound after conditioning on every such arrival prefix, and therefore supports this reading.
--
--   Differences from the source:
--   - encoding: finite vertex set and unordered disagreements → Fintype V, SimpleGraph V, maps to labels, and unordered distinct Sym2 pairs; reason: decidable equality is classical data and no finite graph or clustering is excluded
--   - encoding: uniform random arrival order → the finite average over all bijections Fin (card V) ≃ V; reason: there are exactly n! such bijections, each with equal weight
--   - encoding: n ≥ 2 for the remainder of §7.3.2–§7.3.4, p. 30 → 2 ≤ Fintype.card V; reason: this is the stated standing assumption, ensuring positive natural logarithms and denominators
--   - reading: let v be a pivot that arrives at time t_v → a bound conditional on v being a pivot and arriving at each fixed j ≤ t; reason: the proof conditions on the entire history through arrival of v, giving the stronger conditional interpretation
-- source:
--   Mahsa Derakhshan, Andisheh Ghasemi, Rajmohan Rajaraman, Omer Wasim, Tegan Wilson, STOC 2027 submission #302 (October 2026), Lemma 7.7, p. 33, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/302.pdf

import Definitions.Def_CorrKClust_BalancedPivot_Analysis

set_option autoImplicit false
open Classical
noncomputable section

namespace CorrKClust.BalancedPivot

/-- Lemma 7.7, p. 33, conditional on being a pivot arriving at j, as in its proof. -/
theorem lemma_7_7 {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) (hn : 2 ≤ Fintype.card V)
    (c : ℝ) (hc : 0 < c) (v : V) (j t : ℕ) (hj : 1 ≤ j) (hjt : j ≤ t)
    (htn : t ≤ Fintype.card V) :
    probability (fun σ : ArrivalOrder V => v ∈ pivots G σ ∧ arrivalTime σ v = j ∧
      1 + 2 * (finalSize G σ v : ℝ) * t / Fintype.card V + c * Real.log (Fintype.card V) <
        (pivotSize G σ t v : ℝ)) ≤
      Real.rpow (Fintype.card V : ℝ) (-c / 3) *
        probability (fun σ : ArrivalOrder V => v ∈ pivots G σ ∧ arrivalTime σ v = j) := by sorry

end CorrKClust.BalancedPivot
