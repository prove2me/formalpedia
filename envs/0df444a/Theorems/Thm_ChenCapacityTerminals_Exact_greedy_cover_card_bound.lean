-- Prove2me | Theorems.Thm_ChenCapacityTerminals_Exact_greedy_cover_card_bound
-- name    : ChenCapacityTerminals.Exact.greedy_cover_card_bound
-- status  : Proved
-- author  : @Mr Robbins
-- created : 2026-11-23T02:24:16.12781+00:00
-- url     : https://prove2.me/theorems/0235a1eb-7195-4dd3-a463-a8b6c558048f
-- title:
--   Logarithmic cardinality bound for the greedy full-group cover
-- statement:
--   Let $V$ be a finite vertex set, let $1\le d\le |V|$, and let $\mathcal G$ be a listed family of $d$-element subsets of $V$. Repeatedly choose a vertex of $V$ meeting the largest positive number of still-uncovered groups, and remove precisely the groups it meets. If $D$ is the resulting list of chosen vertices, then
--
--   $$
--   |D|\le 2\frac{|V|}{d}\log\!\left(2+\sum_{g\in\mathcal G}|g|\right).
--   $$
--
--   The sum in the logarithm is the total number of group incidences, with repetitions in the list counted separately. The empty family produces the empty selection. This is the finite combinatorial form of the geometric-decay argument in Lemma 2.2.
-- source:
--   Thomas Chen, STOC 2027 submission #665 (October 2026), PDF p. 5 (printed p. 4), Lemma 2.2, first paragraph of the proof; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/665.pdf#page=5

import Definitions.Def_ChenCapacityTerminals_Exact_Construction

set_option autoImplicit false

theorem ChenCapacityTerminals.Exact.greedy_cover_card_bound (V : Finset ℕ) (d : ℕ)
    (groups : List (Finset ℕ)) (D : List ℕ) :
    1 ≤ d → d ≤ V.card →
    (∀ g ∈ groups, g ⊆ V ∧ g.card = d) →
    Greedy V groups D →
    (D.toFinset.card : ℝ) ≤
      2 * ((V.card : ℝ) / d) * Real.log (2 + (groups.map Finset.card).sum) := by sorry
