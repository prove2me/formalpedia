-- Prove2me | Theorems.Thm_CBCLowerBound_EveryNorm_lemma_2
-- name    : CBCLowerBound.EveryNorm.lemma_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:22:43.212256+00:00
-- url     : https://prove2.me/theorems/289f0204-e649-4422-bb65-a330026e96eb
-- title:
--   Lemma 2 — requests have at most $r+1$ vertices and the offline optimum is $L_r$
-- statement:
--   Fix admissible parameters $(m_r,C_r)$, a tie rule and a level $r\ge0$, and let $S_1,\dots,S_T$ be a request sequence in the support of $D_r$ on the graph $G=G_r$ with source $s_r$, target $t_r$ and $L_r=d_G(s_r,t_r)$. Then:
--
--   1. every request has at most $r+1$ vertices: $|S_t|\le r+1$;
--   2. the sequence can be served along a directed shortest path from $s_r$: there are $y_0=s_r$ and $y_t\in S_t$ ($1\le t\le T$) whose depths $h(y_t)=d_G(s_r,y_t)$ are nondecreasing in $t$ and
--   $$\sum_{t=1}^T d_G(y_{t-1},y_t)=L_r;$$
--   3. consequently the discrete offline optimum equals $L_r$:
--   $$\inf\Big\{\sum_{t=1}^T d_G(y_{t-1},y_t): y_0=s_r,\ y_t\in S_t\Big\}=L_r.$$
--
--   The second and third clauses provide the offline side of every comparison in the mission: they bound the offline cost of the mapped convex instance in Proposition 9.
--
--   **Formalization Note** The sequence is an annotated sequence in the support of the probability mass function $D_r$; its plain requests are the sets $U\cup Z$. "Directed" is expressed by nondecreasing depth together with total length $L_r$.
--
--   Differences from the source:
--   - encoding: a realized level-r request sequence → a list of annotated requests in the support of the PMF D_r, read through its plain sets; reason: the annotation records the call structure and does not change the requested sets
--   - reading: "a fixed rule to break a tie" (Stage 3) → the statement holds for both fixed rules (tie : Bool); reason: the paper does not specify the rule
--   - reading: "the final request of this stage consists of the two current vertices" (Stage 2) → the last request of the last Stage-2 call, no extra request; reason: that last request is exactly the pair of current vertices
--   - reading: "directed shortest path" → nondecreasing depth along the selection with total length L_r; reason: a walk from s_r of length d_G(s_r, t_r) ending at t_r with monotone depth is a directed shortest path
-- source:
--   Nicolas Christianson, A Linear Lower Bound for Convex Body Chasing in Every Norm, STOC 2027 submission #674 (October 2026), p.7, Lemma 2, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/674.pdf

import Mathlib
import Definitions.Def_CBCLowerBound_EveryNorm_Requests

namespace CBCLowerBound.EveryNorm

/-- **Lemma 2** (request size and offline path; Christianson, STOC 2027 #674, p.7). For every
parameter choice `θ`, tie rule and level `r`, every annotated request sequence `σ` in the
support of `D_r` satisfies:
1. every request has at most `r + 1` vertices;
2. it can be served along a directed shortest path from `s_r`: there are `y₀ = s_r` and
   `y_t ∈ S_t` with nondecreasing depth and total length `∑_t d_G(y_{t−1}, y_t) = L_r`;
3. hence the offline optimum of the discrete sequence is `L_r`. -/
theorem lemma_2 (θ : Params) (tie : Bool) (r : ℕ) (σ : List (AReq θ r))
    (hσ : σ ∈ (reqDist θ tie r).support) :
    (∀ q ∈ σ, q.set.card ≤ r + 1) ∧
    (∃ y : ℕ → Vert θ r, y 0 = .src ∧
      (∀ (t : ℕ) (ht : t < σ.length), y (t + 1) ∈ (σ[t]).set) ∧
      (∀ t < σ.length, depth θ r (y t) ≤ depth θ r (y (t + 1))) ∧
      ∑ t ∈ Finset.range σ.length, dist θ r (y t) (y (t + 1)) = L θ r) ∧
    mssOpt θ r (requests σ) = L θ r := by sorry

end CBCLowerBound.EveryNorm
