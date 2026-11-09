-- Prove2me | Theorems.Thm_CBCLowerBound_EveryNorm_lemma_5
-- name    : CBCLowerBound.EveryNorm.lemma_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:23:15.711325+00:00
-- url     : https://prove2.me/theorems/502a6f15-b416-45f6-bda3-29017f335a75
-- title:
--   Lemma 5 — structure of consecutive requests: a local change in one copy plus retained waiting vertices
-- statement:
--   Fix admissible parameters, a tie rule and a level $r$, and let $S,S'$ be consecutive requests of a sequence in the support of $D_r$.
--
--   1. If $S\ne S'$, there are a copy $H$ of some $G_s$ ($0\le s\le r$) and local requests $U,U'$ within $H$, both requests being issued during the call to $H$, and the set $Z$ of waiting vertices retained by the higher-level calls containing $H$, such that
--   $$S=U\cup Z,\qquad S'=U'\cup Z,\qquad (U\cup U')\cap Z=\varnothing\qquad\text{(eq. (7))},$$
--   and $(U,U')$ has one of the forms
--      - traverse a level-zero copy: $s=0$, $U=\{s_H\}$, $U'=\{t_H\}$;
--      - traverse the two entrance edges: $s\ge1$, $U=\{s_H\}$, $U'=\{u_L,u_R\}$, the terminal endpoints of the entrance edges of $H$;
--      - start Stage 3: $s\ge1$, $U=\{u,v\}$, $U'=\{v\}$, where $u$ is the discarded branch's current vertex and $v$ the surviving one; that is, writing $m=m_{s-1}$, $u$ and $v$ are the sources of the large copies with indices $j$ and $j'$ (counted from $0$ along their branches) on opposite branches of $H$, with $m^2\le j'\le j$ and $j+j'=2m^2+m$.
--   2. If $S=S'$, the common request is the first or last request of the call to a copy $H$ of some level $s$: for the requested endpoint $u\in\{s_H,t_H\}$ and the waiting vertices $Z$ retained by the higher-level calls, that request is $\{u\}\cup Z$ with $u\notin Z$, i.e. one can take $U=U'=\{u\}$ in (7).
--   3. In every request the retained waiting vertices come from levels above the innermost active call, at most one from each level.
--
--   The lemma localizes every change between consecutive requests to one copy; Corollary 6 and Lemma 8 are built on it.
--
--   **Formalization Note** "Issued during the call to $H$" means that $H$ contains the innermost active call recorded in the request's annotation; $Z$ is the set of annotated waiting vertices with level $>s$. In case 2 the request lying in the call to $H$ may be either $S$ or $S'$ (e.g. the entrance pair $\{u_L,u_R\}$ is repeated as the first request of the first Stage-1 call). Clause 3 says that the levels labelling the waiting vertices of a request are distinct and lie strictly between the request's innermost call level and $r+1$.
--
--   Differences from the source:
--   - encoding: "a copy H", "the call to H" and "waiting vertices retained by the higher-level calls containing H" → the annotation of D_r: H contains the innermost call, Z = annotated waiting vertices of level > s; reason: this is how the construction (p.7) defines the calls and the retained waiting vertices
--   - reading: "u denotes the discarded branch's current vertex and v is the surviving one" → u, v are the sources of the large copies with indices j, j' on opposite branches of H, m² ≤ j' ≤ j, j + j' = 2m² + m; reason: after Stage 2 the branches have advanced X and m − X times, the surviving one fewer times
--   - encoding: a realized level-r request sequence → a list of annotated requests in the support of the PMF D_r, read through its plain sets; reason: the annotation records the call structure and does not change the requested sets
--   - reading: "a fixed rule to break a tie" (Stage 3) → the statement holds for both fixed rules (tie : Bool); reason: the paper does not specify the rule
--   - reading: "the final request of this stage consists of the two current vertices" (Stage 2) → the last request of the last Stage-2 call, no extra request; reason: that last request is exactly the pair of current vertices
-- source:
--   Nicolas Christianson, A Linear Lower Bound for Convex Body Chasing in Every Norm, STOC 2027 submission #674 (October 2026), p.10, Lemma 5, eq. (7), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/674.pdf

import Mathlib
import Definitions.Def_CBCLowerBound_EveryNorm_Requests

namespace CBCLowerBound.EveryNorm

/-- **Lemma 5** (structure of consecutive requests; Christianson, STOC 2027 #674, p.10). Let
`S = σ[t].set` and `S' = σ[t+1].set` be consecutive requests of a sequence `σ` in the support
of `D_r` (any parameters `θ`, tie rule, level `r`).
1. If `S ≠ S'`, there are a copy `H` of some `G_s` and local requests `U, U'` in `H` such that
   both requests occur in the call to `H` and `S = U ∪ Z`, `S' = U' ∪ Z`, `(U ∪ U') ∩ Z = ∅`,
   with `Z` the waiting vertices retained by the higher-level calls containing `H` (eq. (7)),
   where `(U, U')` is one of: `({s_H}, {t_H})` with `H` a level-zero copy (traversing a base
   edge); `({s_H}, {u_L, u_R})` with `H` of level `≥ 1` and `u_L, u_R` the terminal endpoints
   of its entrance edges; or `({u, v}, {v})` with `H` of level `s + 1 ≥ 1` (start of Stage 3),
   where `u` is the current vertex of the discarded branch and `v` that of the surviving
   branch after Stage 2, i.e. `u, v` are the sources of the large copies with indices `j`, `j'`
   on opposite branches, `m_s² ≤ j' ≤ j`, `j + j' = 2m_s² + m_s`.
2. If `S = S'`, the common request is the first or last request of the call to some copy `H`:
   for an endpoint `u ∈ {s_H, t_H}` and the waiting vertices `Z` retained by the higher-level
   calls, the request in the call to `H` is `{u} ∪ Z` with `u ∉ Z` (`U = U' = {u}` in (7)).
3. In every request the retained waiting vertices come from levels above the innermost call,
   at most one from each level. -/
theorem lemma_5 (θ : Params) (tie : Bool) (r : ℕ) (σ : List (AReq θ r))
    (hσ : σ ∈ (reqDist θ tie r).support) (t : ℕ) (ht : t + 1 < σ.length) :
    ((σ[t]).set ≠ (σ[t + 1]).set →
      (∃ H : Copy θ r 0, IsLocalChange σ[t] σ[t + 1] H {H.src} {H.tgt}) ∨
      (∃ (s : ℕ) (H : Copy θ r (s + 1)),
        IsLocalChange σ[t] σ[t + 1] H {H.src} {H.junc false 0, H.junc true 0}) ∨
      (∃ (s : ℕ) (H : Copy θ r (s + 1)) (a : Bool) (j j' : ℕ),
        θ.m s ^ 2 ≤ j' ∧ j' ≤ j ∧ j + j' = 2 * θ.m s ^ 2 + θ.m s ∧
        IsLocalChange σ[t] σ[t + 1] H {H.junc a j, H.junc (!a) j'} {H.junc (!a) j'})) ∧
    ((σ[t]).set = (σ[t + 1]).set →
      ∃ (s : ℕ) (H : Copy θ r s) (u : Vert θ r), (u = H.src ∨ u = H.tgt) ∧
        ((H.Contains (σ[t]).copy ∧ (σ[t]).set = {u} ∪ (σ[t]).waitAbove s ∧
            u ∉ (σ[t]).waitAbove s) ∨
          (H.Contains (σ[t + 1]).copy ∧ (σ[t + 1]).set = {u} ∪ (σ[t + 1]).waitAbove s ∧
            u ∉ (σ[t + 1]).waitAbove s))) ∧
    (∀ q ∈ [σ[t], σ[t + 1]], (q.wait.map Prod.fst).Nodup ∧
      ∀ p ∈ q.wait, q.lvl < p.1 ∧ p.1 ≤ r) := by sorry

end CBCLowerBound.EveryNorm
