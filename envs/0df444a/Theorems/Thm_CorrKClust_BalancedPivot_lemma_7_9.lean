-- Prove2me | Theorems.Thm_CorrKClust_BalancedPivot_lemma_7_9
-- name    : CorrKClust.BalancedPivot.lemma_7_9
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T20:46:03.818613+00:00
-- url     : https://prove2.me/theorems/b77bcd5d-cf39-4ecc-8f73-b25a8c0b4636
-- title:
--   Lemma 7.9 — pivot clusters with many early arrivals remain large
-- statement:
--   Let $G$ have $n\ge2$ vertices, let $c>6$ be real, and fix an integer $1\le t\le n$. Then
--   $$\Pr\!\left[\exists v\text{ pivot with }t_v\le t:\ p_t(v)\ge c\ln n+1,\quad p_n(v)<\frac{cn\ln n}{2t}\right]\le n^{1-c/6}.$$
--   This retains the exact strict and non-strict inequalities, the range c > 6 and the paper's exponent. It prevents a large observed pivot cluster from having too small a final mass.
--
--   Differences from the source:
--   - encoding: finite vertex set and unordered disagreements → Fintype V, SimpleGraph V, maps to labels, and unordered distinct Sym2 pairs; reason: decidable equality is classical data and no finite graph or clustering is excluded
--   - encoding: uniform random arrival order → the finite average over all bijections Fin (card V) ≃ V; reason: there are exactly n! such bijections, each with equal weight
--   - encoding: n ≥ 2 for the remainder of §7.3.2–§7.3.4, p. 30 → 2 ≤ Fintype.card V; reason: this is the stated standing assumption, ensuring positive natural logarithms and denominators
-- source:
--   Mahsa Derakhshan, Andisheh Ghasemi, Rajmohan Rajaraman, Omer Wasim, Tegan Wilson, STOC 2027 submission #302 (October 2026), Lemma 7.9, p. 35, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/302.pdf

import Definitions.Def_CorrKClust_BalancedPivot_Analysis

set_option autoImplicit false
open Classical
noncomputable section

namespace CorrKClust.BalancedPivot

/-- Lemma 7.9, p. 35: retain c > 6 and exponent 1-c/6 exactly. -/
theorem lemma_7_9 {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) (hn : 2 ≤ Fintype.card V) (c : ℝ) (hc : 6 < c)
    (t : ℕ) (ht : 1 ≤ t) (htn : t ≤ Fintype.card V) :
    probability (fun σ : ArrivalOrder V => ∃ v : V, v ∈ pivots G σ ∧ arrivalTime σ v ≤ t ∧
      c * Real.log (Fintype.card V) + 1 ≤ (pivotSize G σ t v : ℝ) ∧
      (finalSize G σ v : ℝ) < c * Fintype.card V * Real.log (Fintype.card V) / (2 * t)) ≤
        Real.rpow (Fintype.card V : ℝ) (1 - c / 6) := by sorry

end CorrKClust.BalancedPivot
