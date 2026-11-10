-- Prove2me | Theorems.Thm_DistancePreserver934_Exact_lemma_12
-- name    : DistancePreserver934.Exact.lemma_12
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-09T08:37:40.839423+00:00
-- url     : https://prove2.me/theorems/f9ccaed9-870b-4f86-bd68-2968dfe2f1d8
-- title:
--   Lemma 12 — essential edges along shortest paths
-- statement:
--   Let $H$ be a minimal distance preserver of $(G,R)$, $R$ a demand set, and $q\in R$.
--
--   1. Every vertex is an endpoint of at most two edges of $H$ essential to $q$.
--   2. For every shortest path $\pi$ for $q$ in $H$ and every vertex $u$, at most three vertices of $\pi$ belong to the neighbourhood $N_H(u)$. Moreover, for every vertex $u$ there are at most six pairs $(x,e)$ such that $e\in E_H$ is essential to $q$ and $x\in N_H(u)$ is an endpoint of $e$.
--   3. If $e$ is essential to $q$, $\pi$ is a shortest path for $q$, and a subpath $P$ of $\pi$ from $a$ to $b$ contains $e$, then every shortest $a$–$b$ path in $H$ contains $e$.
--
--   These three facts control how often a single demand can be seen near a vertex; they are used in Lemmas 14, 17, 10 and 16.
--
--   Differences from the source:
--   - encoding: a fixed arbitrary shortest path π(q) for each demand → the clauses about π(q) are stated for every shortest walk π for q; reason: the source fixes an arbitrary choice, so its claim holds for every choice
--   - encoding: a subpath P of π(q) → a walk P with π = p₁ ++ P ++ p₂ for walks p₁, p₂; reason: this is exactly a contiguous subpath of π
--   - generalization: the standing size bounds and private-length/radius assumptions (4)–(5) of §5 → only the demand-set and minimal-preserver assumptions, with q ∈ R; reason: the source proof of all three clauses uses only shortest paths and essentiality; every instance of the standing context satisfies these retained assumptions
-- source:
--   Yanyu Chen, Yu Chen, Zihan Tan, Mingyang Yang, Improved Bounds on Distance Preservers, STOC 2027 submission #934 (October 2026), SHA-256 79b3d23a6e7b7fc6148c7a627181474a0129fb2f4c1d04ccd94c1da7987ed76b, Lemma 12 (with the §5.1 convention fixing a shortest path π(q)), printed p. 14 (PDF p. 15)

import Mathlib
import Definitions.Def_DistancePreserver934_Exact_Preservers
import Definitions.Def_DistancePreserver934_Exact_Essential

namespace DistancePreserver934.Exact

open Classical

/-- Lemma 12, printed p.14 / PDF p.15.  For a minimal distance preserver `H` of `(G, R)` and a
demand `q ∈ R`: (1) a vertex is incident to at most two edges essential to `q`; (2) for every
vertex `u` and every shortest path `π` for `q`, at most three vertices of `π` are neighbours of
`u`, and there are at most six pairs `(x, e)` with `e` essential to `q` and `x ∈ N_H(u)` an
endpoint of `e`; (3) if `e` is essential to `q` and a subpath `P` of a shortest path `π` for `q`
contains `e`, then every shortest path between the endpoints of `P` contains `e`. -/
theorem lemma_12 {V : Type} [Fintype V] (G H : SimpleGraph V) (R : Finset (Sym2 V))
    (hR : IsDemandSet G R) (hH : IsMinimalPreserver G H R) (q : Sym2 V) (hq : q ∈ R) :
    (∀ x : V, ((edgesF H).filter (fun e => x ∈ e ∧ IsEssential H q e)).card ≤ 2) ∧
    (∀ s t : V, s(s, t) = q → ∀ π : H.Walk s t, IsShortest π → ∀ u : V,
      (π.support.toFinset.filter (fun v => H.Adj u v)).card ≤ 3) ∧
    (∀ u : V, ((Finset.univ : Finset (V × Sym2 V)).filter (fun xe =>
        xe.2 ∈ H.edgeSet ∧ IsEssential H q xe.2 ∧ xe.1 ∈ xe.2 ∧ H.Adj u xe.1)).card ≤ 6) ∧
    (∀ e : Sym2 V, IsEssential H q e → ∀ s t : V, s(s, t) = q → ∀ π : H.Walk s t,
      IsShortest π → ∀ (a b : V) (p₁ : H.Walk s a) (P : H.Walk a b) (p₂ : H.Walk b t),
        π = p₁.append (P.append p₂) → e ∈ P.edges →
        ∀ P' : H.Walk a b, IsShortest P' → e ∈ P'.edges) := by sorry

end DistancePreserver934.Exact
