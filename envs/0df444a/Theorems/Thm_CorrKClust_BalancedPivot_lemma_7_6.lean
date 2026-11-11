-- Prove2me | Theorems.Thm_CorrKClust_BalancedPivot_lemma_7_6
-- name    : CorrKClust.BalancedPivot.lemma_7_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T20:45:38.386498+00:00
-- url     : https://prove2.me/theorems/384f3ca2-d057-412d-8328-8cfe9fc9b7ea
-- title:
--   Lemma 7.6 — late pivots found small clusters
-- statement:
--   Let $G$ have $n\ge2$ vertices, fix a vertex $v$, a real $m\ge0$, and an arrival time $1\le j\le n$. Under a uniform arrival order,
--   $$\Pr[v\text{ is a pivot and }p_n(v)\ge m+1\mid t_v=j]\le\exp\!\left(-\frac{m(j-1)}{n-1}\right).$$
--   Here $p_n(v)$ is the final size of the pivot cluster founded by $v$. The conditioning event has probability $1/n>0$. This bounds large late-founded pivot clusters without requiring m to be an integer.
--
--   Differences from the source:
--   - encoding: finite vertex set and unordered disagreements → Fintype V, SimpleGraph V, maps to labels, and unordered distinct Sym2 pairs; reason: decidable equality is classical data and no finite graph or clustering is excluded
--   - encoding: uniform random arrival order → the finite average over all bijections Fin (card V) ≃ V; reason: there are exactly n! such bijections, each with equal weight
--   - encoding: n ≥ 2 for the remainder of §7.3.2–§7.3.4, p. 30 → 2 ≤ Fintype.card V; reason: this is the stated standing assumption, ensuring positive natural logarithms and denominators
-- source:
--   Mahsa Derakhshan, Andisheh Ghasemi, Rajmohan Rajaraman, Omer Wasim, Tegan Wilson, STOC 2027 submission #302 (October 2026), Lemma 7.6, p. 31, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/302.pdf

import Definitions.Def_CorrKClust_BalancedPivot_Analysis

set_option autoImplicit false
open Classical
noncomputable section

namespace CorrKClust.BalancedPivot

/-- Lemma 7.6, p. 31; conditioning has positive probability 1/n. -/
theorem lemma_7_6 {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) (hn : 2 ≤ Fintype.card V)
    (m : ℝ) (hm : 0 ≤ m) (v : V) (j : ℕ) (hj : 1 ≤ j) (hjn : j ≤ Fintype.card V) :
    conditional (fun σ : ArrivalOrder V => v ∈ pivots G σ ∧ m + 1 ≤ (finalSize G σ v : ℝ))
      (fun σ => arrivalTime σ v = j) ≤
        Real.exp (-(m * ((j : ℝ) - 1) / ((Fintype.card V : ℝ) - 1))) := by sorry

end CorrKClust.BalancedPivot
