-- Prove2me | Theorems.Thm_DetStreamClique_MaxClique_lemma_3_11
-- name    : DetStreamClique.MaxClique.lemma_3_11
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:12:29.463594+00:00
-- url     : https://prove2.me/theorems/4fdc435f-1587-4495-9154-8b900532cad5
-- title:
--   Lemma 3.11 — finite expectation and tail bounds
-- statement:
--   For a block system of Input Distribution 3.2.2, let a deterministic protocol have a message alphabet of size at most $2^c$. Write $M=M(E_A)$ for its realized message and $J_A=J(A\mid M,G_0)$. Then
--   $$J(A\mid M=m,G_0=g)\ge0\quad(m\text{ in range}),\qquad \mathbb E_{A,G_0}J_A\le c,$$
--   and for every $t>0$,
--   $$\Pr_{A,G_0}(J_A\ge t)\le c/t.$$
--   In particular, along every sequence with $c=o(n^2/b)$, a threshold $t=o(n^2/b)$ can be chosen with exceptional probability $o(1)$. This states the printed high-probability assertion with explicit finite inequalities.
--
--   Differences from the source:
--   - encoding: blocks have size 18b and sampled subsets size 9b with b ≥ 1 → k=9b is a natural number with k ≥ 9, and block size is 2k; reason: these cardinalities require 9b integral and this parametrization covers exactly those instances; k is not the goal approximation ratio
--   - generalization: the blocks supplied by Lemma 3.10 → every block family with the same cardinalities and pairwise intersections at most one; reason: the proof uses precisely these properties, so the family supplied by Lemma 3.10 is included
--   - reading: messages of size o(n²/b) give J=o(n²/b) with probability 1-o(1) → nonnegativity, expectation at most c and tail at most c/t for all t>0; reason: these finite inequalities from the cited proof imply the printed assertion for every sequence; e.g. t=√((c+1)n²/b)
--   - encoding: conditioning on the realized base graph → the uniform tuple law at a fixed base graph; reason: the tuple is independent of the base graph and each graph has positive uniform mass
-- source:
--   Adithya Diddapur, Deterministic Streaming Lower Bounds for Approximate Maximum Clique and Maximum Independent Set, STOC 2027 submission #248 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/248.pdf, Lemma 3.11; single-gadget template Lemma 3.4, p. 17; p. 12

import Mathlib
import Definitions.Def_DetStreamClique_MaxClique_HardInstance

open scoped Classical BigOperators

namespace DetStreamClique.MaxClique

/-- Lemma 3.11, p. 17: finite expectation and Markov bounds imply the printed little-o form. -/
theorem lemma_3_11 {n ℓ k : ℕ} (B : BlockSystem n ℓ k) (hk : 9 ≤ k)
    {M : Type} [Fintype M]
    (π : OneWayProtocol (Graph n) (Graph n) M (Finset (Fin n)))
    (c : ℕ) (hbits : FitsBits M c) :
    (∀ G m, (fiber B π G m).Nonempty → 0 ≤ jointInfo B π G m) ∧
    hardExpectation B (fun G A => jointInfo B π G (π.send (aliceGraph G A))) ≤ (c : ℝ) ∧
    ∀ t : ℝ, 0 < t →
      hardProbability B (fun G A => t ≤ jointInfo B π G (π.send (aliceGraph G A))) ≤ (c : ℝ) / t := by sorry

end DetStreamClique.MaxClique
