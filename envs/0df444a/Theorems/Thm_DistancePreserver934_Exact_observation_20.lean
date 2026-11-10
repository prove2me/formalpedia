-- Prove2me | Theorems.Thm_DistancePreserver934_Exact_observation_20
-- name    : DistancePreserver934.Exact.observation_20
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-09T08:37:47.776478+00:00
-- url     : https://prove2.me/theorems/e33f27d1-6344-4a12-bb4d-c5c9bf7ff910
-- title:
--   Observation 20 (removing one demand)
-- statement:
--   Let $R$ be a demand set of $K$ and $K$ a minimal distance preserver of $(K,R)$; let $q\in R$ and $R'=R\setminus\{q\}$. Every distance preserver $K'\subseteq K$ of $(K,R')$ contains every edge $e\in E(K)$ with $D_K^R(e)\neq\{q\}$. Consequently
--   $$|E(K)|-|E(K')|\le\lambda_K(q),\tag{27}$$
--   where $\lambda_K(q)$ is the private length before $q$ is removed. $K'$ need not be minimal.
--
--   This bounds the loss of each Step 1 removal in Lemma 23.
--
--   **Formalization Note** The subtraction is in the integers.
--
--   Differences from the source: none.
-- source:
--   Yanyu Chen, Yu Chen, Zihan Tan, Mingyang Yang, Improved Bounds on Distance Preservers, STOC 2027 submission #934 (October 2026), SHA-256 79b3d23a6e7b7fc6148c7a627181474a0129fb2f4c1d04ccd94c1da7987ed76b, Observation 20, printed p. 21 (PDF p. 22)

import Mathlib
import Definitions.Def_DistancePreserver934_Exact_Preservers
import Definitions.Def_DistancePreserver934_Exact_Essential

namespace DistancePreserver934.Exact

open Classical

/-- Observation 20 (removing one demand), printed p.21 / PDF p.22.  Let `K` be a minimal distance
preserver of `(K, R)`, `q ∈ R`, `R' = R \ {q}`.  Every distance preserver `K' ⊆ K` of `(K, R')`
contains every edge `e ∈ E(K)` with `D_K^R(e) ≠ {q}`; consequently
`|E(K)| − |E(K')| ≤ λ_K(q)` (Equation (27)), the private length before removal. -/
theorem observation_20 {V : Type} [Fintype V] (K : SimpleGraph V) (R : Finset (Sym2 V))
    (hR : IsDemandSet K R) (hK : IsMinimalPreserver K K R) (q : Sym2 V) (hq : q ∈ R)
    (K' : SimpleGraph V) (hK' : IsPreserver K K' (R.erase q)) :
    (∀ e ∈ K.edgeSet, essSet K R e ≠ {q} → e ∈ K'.edgeSet) ∧
    (numEdges K : ℤ) - (numEdges K' : ℤ) ≤ (privLen K R q : ℤ) := by sorry

end DistancePreserver934.Exact
