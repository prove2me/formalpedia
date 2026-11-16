-- Prove2me | Theorems.Thm_EntropyLocalCoord_Leader_Supplement_lemma_5_3
-- name    : EntropyLocalCoord.Leader.Supplement.lemma_5_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T17:27:57.752738+00:00
-- url     : https://prove2.me/theorems/e556c549-de8b-47c8-8af2-0991b7b81968
-- title:
--   Lemma 5.3 — a relevant coordinate shared with every neighbour in $H$
-- statement:
--   Fix an integer $k\ge5$ (the standing assumption of §5) and let $H$ be the graph of positive-weight, tie-free weighted majority functions on $k$ inputs, where $f\sim g$ when $f$ and $g$ disagree on exactly one antipodal pair. For every $f\in V(H)$ there is a coordinate $i_f$ with
--
--   $$i_f\in\operatorname{supp}(f)\quad\text{and}\quad i_f\in\operatorname{supp}(g)\ \text{ for every } g\sim f.$$
--
--   It lets every leader at an ordinary vertex of the construction be replaced by a special vertex visible to all its followers, which reduces arbitrary leader assignments to coordinate assignments.
--
--   Differences from the source:
--   - encoding: f ∼ g iff the regions of f and g share a facet inside (0,∞)^k → f ∼ g iff f and g disagree exactly on one antipodal pair {x, −x}; reason: the source states this equivalence on p. 14 ("Notice that f ∼ g in H if and only if ..."); the two descriptions give the same graph H
-- source:
--   Peretz and Kraizberg, Entropy Bounds for Local Coordination and Graph Amenability, STOC 2027 submission #272 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/272.pdf, SHA-256 ed0fb53954295c5258fc56b2780b62aad05401917ee1fb4064ff953d9d1d0526, Lemma 5.3, p. 18; standing assumption k ≥ 5, §5 Step 1, p. 13; H, Step 1, p. 14; supp(f), Step 2, p. 14.

import Mathlib
import Definitions.Def_EntropyLocalCoord_Leader_Supplement_Majority

namespace EntropyLocalCoord.Leader.Supplement

/-- Peretz--Kraizberg, STOC 2027 submission #272, Lemma 5.3, p. 18 (standing assumption `k ≥ 5`
of §5, p. 13). Every vertex `f` of `H` has a coordinate `i_f ∈ supp(f)` lying in `supp(g)` for
every neighbour `g ∼ f`. -/
theorem lemma_5_3 (k : ℕ) (hk : 5 ≤ k) (f : MajFun k) :
    ∃ i ∈ supp f.1, ∀ g : MajFun k, (auxGraph k).Adj f g → i ∈ supp g.1 := by sorry

end EntropyLocalCoord.Leader.Supplement
