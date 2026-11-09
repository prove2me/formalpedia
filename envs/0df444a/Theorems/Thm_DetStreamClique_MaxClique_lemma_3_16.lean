-- Prove2me | Theorems.Thm_DetStreamClique_MaxClique_lemma_3_16
-- name    : DetStreamClique.MaxClique.lemma_3_16
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:12:44.865137+00:00
-- url     : https://prove2.me/theorems/99773285-a514-45ef-8ec1-fb0712dd7704
-- title:
--   Lemma 3.16 — a clique when Bob guesses correctly
-- statement:
--   For any base graph $g$, legal tuple $A$, deterministic protocol and block index $i$, give Bob the complement edges on $A_i\setminus C_i$, where $C_i$ is computed from Alice's actual message. The combined graph satisfies
--   $$\omega(E_A\cup E_B)\ge k-|C_i|=9b-|C_i|.$$
--   There is no assumption on the message size or approximation guarantee. This is the deterministic planted-clique-size assertion used when Bob's guess equals the sampled subset.
--
--   Differences from the source:
--   - encoding: blocks have size 18b and sampled subsets size 9b with b ≥ 1 → k=9b is a natural number with k ≥ 9, and block size is 2k; reason: these cardinalities require 9b integral and this parametrization covers exactly those instances; k is not the goal approximation ratio
--   - generalization: the blocks supplied by Lemma 3.10 → every block family with the same cardinalities and pairwise intersections at most one; reason: the proof uses precisely these properties, so the family supplied by Lemma 3.10 is included
--   - generalization: the minimizing index with A′min=Amin → every index i, with Bob’s guess set to the actual A_i; reason: the printed argument applies at every block and specializes to the minimizing index
--   - encoding: a real-valued size lower bound 9b-|C_i| → k-|C_i| in the real numbers; reason: the fiber contains the actual tuple, hence the core lies in A_i and no truncated subtraction occurs
-- source:
--   Adithya Diddapur, Deterministic Streaming Lower Bounds for Approximate Maximum Clique and Maximum Independent Set, STOC 2027 submission #248 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/248.pdf, Lemma 3.16, p. 17

import Mathlib
import Definitions.Def_DetStreamClique_MaxClique_HardInstance

open scoped Classical BigOperators

namespace DetStreamClique.MaxClique

/-- Lemma 3.16, p. 17: Bob guesses the actual subset; all indices are covered. -/
theorem lemma_3_16 {n ℓ k : ℕ} (B : BlockSystem n ℓ k) (hk : 9 ≤ k)
    {M : Type} [Fintype M]
    (π : OneWayProtocol (Graph n) (Graph n) M (Finset (Fin n)))
    (G : Graph n) (A : Tuple B) (i : Fin ℓ) :
    (k : ℝ) - ((commonCore B π G (π.send (aliceGraph G A)) i).card : ℝ) ≤
      ((aliceGraph G A ⊔ bobGraph B π G (π.send (aliceGraph G A)) i (A i).val).cliqueNum : ℝ) := by sorry

end DetStreamClique.MaxClique
