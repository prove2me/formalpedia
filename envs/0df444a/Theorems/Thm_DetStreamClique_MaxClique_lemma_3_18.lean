-- Prove2me | Theorems.Thm_DetStreamClique_MaxClique_lemma_3_18
-- name    : DetStreamClique.MaxClique.lemma_3_18
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:12:25.016496+00:00
-- url     : https://prove2.me/theorems/ac02374f-cd72-42bb-90fa-30041e8c40ce
-- title:
--   Lemma 3.18 — a uniform small-output probability bound
-- statement:
--   Let $n\ge1$. Take any block family, a block index $i$, and a deterministic one-way protocol whose output is a clique for every edge-disjoint pair of graph inputs. Draw $G_0\sim G_{n,1/2}$. With probability at least $1-2/n$, simultaneously for every legal tuple $A$ and every guess $A'_i$ in the projection of its realized message fiber, Bob's output obeys
--   $$|\mathrm{OUT}(M(E_A),E_B)|\le6\log_2 n,$$
--   where $E_B=E(\overline G_0[A'_i\setminus C_i])$. Both universal quantifiers lie inside the probability. No approximation assumption or small-message hypothesis is needed.
--
--   Differences from the source:
--   - encoding: blocks have size 18b and sampled subsets size 9b with b ≥ 1 → k=9b is a natural number with k ≥ 9, and block size is 2k; reason: these cardinalities require 9b integral and this parametrization covers exactly those instances; k is not the goal approximation ratio
--   - generalization: the blocks supplied by Lemma 3.10 → every block family with the same cardinalities and pairwise intersections at most one; reason: the proof uses precisely these properties, so the family supplied by Lemma 3.10 is included
--   - generalization: Bob at the minimizing index, under a correct approximate-clique protocol → every index and any protocol always outputting a valid clique on edge-disjoint inputs; reason: Claims 6–9 use only universal clique validity and block intersection at most one
--   - reading: probability over the base graph that Bob’s output is small → one good base graph works for every tuple and every legal guess; reason: the proof gives the deterministic bound by ω(G_0)+ω(complement G_0), so its good-graph event is independent of the tuple and guess
--   - encoding: log n and the error probability 2/n → n≥1 and base-2 real logarithms; reason: these are the paper conventions and exclude only an undefined probability formula
-- source:
--   Adithya Diddapur, Deterministic Streaming Lower Bounds for Approximate Maximum Clique and Maximum Independent Set, STOC 2027 submission #248 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/248.pdf, Lemma 3.18 and Claims 6–9, pp. 18–19

import Mathlib
import Definitions.Def_DetStreamClique_MaxClique_HardInstance

open scoped Classical BigOperators

namespace DetStreamClique.MaxClique

/-- Lemma 3.18, pp. 18–19. One good base graph works for all tuples and guesses.
Only universal clique validity is used; no approximation hypothesis is imposed. -/
theorem lemma_3_18 {n ℓ k : ℕ} (hn : 1 ≤ n)
    (B : BlockSystem n ℓ k) (hk : 9 ≤ k) {M : Type} [Fintype M]
    (π : OneWayProtocol (Graph n) (Graph n) M (Finset (Fin n)))
    (hvalid : ProtocolCliqueValid π) (i : Fin ℓ) :
    1 - 2 / (n : ℝ) ≤ graphProbability n (fun G =>
      ∀ A : Tuple B, ∀ a' ∈ projectedFiber B π G (π.send (aliceGraph G A)) i,
        ((π.receive (π.send (aliceGraph G A))
          (bobGraph B π G (π.send (aliceGraph G A)) i a')).card : ℝ) ≤
            6 * Real.logb 2 (n : ℝ)) := by sorry

end DetStreamClique.MaxClique
