-- Prove2me | Theorems.Thm_DetStreamClique_MaxClique_lemma_3_13
-- name    : DetStreamClique.MaxClique.lemma_3_13
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:12:00.09392+00:00
-- url     : https://prove2.me/theorems/79acd2a0-7e07-4e20-9298-c777d108f435
-- title:
--   Lemma 3.13 — information controls the common core
-- statement:
--   Fix any block family, base graph $g$, deterministic protocol, message $m$ in its range and block index $i$. Let $C_i$ be the vertices present in every projected tuple in that message fiber. Then the information in bits satisfies
--   $$|C_i|\le J(A_i\mid M=m,G_0=g).$$
--   Consequently $J(A_{i_*}\mid M=m,G_0=g)=o(b)$ implies $|C_{i_*}|=o(b)$ along every sequence, including bounded gadget sizes. This finite form also implies the template bound $J(A_i\mid m,g)\ge |C_i|-\log_2(18b+1)$.
--
--   Differences from the source:
--   - encoding: blocks have size 18b and sampled subsets size 9b with b ≥ 1 → k=9b is a natural number with k ≥ 9, and block size is 2k; reason: these cardinalities require 9b integral and this parametrization covers exactly those instances; k is not the goal approximation ratio
--   - generalization: the blocks supplied by Lemma 3.10 → every block family with the same cardinalities and pairwise intersections at most one; reason: the proof uses precisely these properties, so the family supplied by Lemma 3.10 is included
--   - encoding: conditional distributions at realized messages and background values → positive conditioning events or nonempty message fibers; reason: realized finite-law values have positive probability; undefined null conditionings are excluded
--   - encoding: conditioning on the realized base graph → the uniform tuple law at a fixed base graph; reason: the tuple is independent of the base graph and each graph has positive uniform mass
--   - reading: J at the minimizing gadget is o(b), hence its common core is o(b) → an explicit finite information inequality valid at every instance; reason: it implies the printed little-o conclusion for every sequence, with no hidden growth requirement on b
--   - generalization: only the minimizing gadget, with the entropy estimate of Lemma 3.3 as template → every block index and the sharper finite estimate |C_i|≤J_i; reason: uniform k-subsets of a 2k-set containing t prescribed vertices occupy at most 2^(-t) of the full support; the printed conclusion and its logarithmic-error template both follow
-- source:
--   Adithya Diddapur, Deterministic Streaming Lower Bounds for Approximate Maximum Clique and Maximum Independent Set, STOC 2027 submission #248 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/248.pdf, Lemma 3.13; template Lemma 3.3, p. 17; p. 11

import Mathlib
import Definitions.Def_DetStreamClique_MaxClique_HardInstance

open scoped Classical BigOperators

namespace DetStreamClique.MaxClique

/-- Lemma 3.13, p. 17 (counting template: Lemma 3.3, p. 11).
The sharper exact core bound implies the little-o assertion even for bounded k:
a fixed core of t vertices occupies at most a 2^(-t) fraction of uniform k-subsets of 2k. -/
theorem lemma_3_13 {n ℓ k : ℕ} (B : BlockSystem n ℓ k) (hk : 9 ≤ k)
    {M : Type} [Fintype M]
    (π : OneWayProtocol (Graph n) (Graph n) M (Finset (Fin n)))
    (G : Graph n) (m : M) (hm : (fiber B π G m).Nonempty) (i : Fin ℓ) :
    ((commonCore B π G m i).card : ℝ) ≤ coordinateInfo B π G m i := by sorry

end DetStreamClique.MaxClique
