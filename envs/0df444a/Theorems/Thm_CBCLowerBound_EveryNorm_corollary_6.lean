-- Prove2me | Theorems.Thm_CBCLowerBound_EveryNorm_corollary_6
-- name    : CBCLowerBound.EveryNorm.corollary_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:23:03.059926+00:00
-- url     : https://prove2.me/theorems/a6a44566-5b4e-4163-abf2-8556d680db70
-- title:
--   Corollary 6 — on two consecutive requests each level has one active copy, and $\psi_{s,a}=\phi_{H_s,a}$
-- statement:
--   Fix admissible parameters, a tie rule and a level $r$, and let $S,S'$ be consecutive requests of a sequence in the support of $D_r$. For each level $s\in\{1,\dots,r\}$ there is a level-$s$ copy $H_s$ such that every other level-$s$ copy $H'_s\ne H_s$ has both branch functions equal to zero on $S\cup S'$:
--   $$\phi_{H'_s,a}(v)=0\quad\text{for all }v\in S\cup S',\ a\in\{L,R\}.$$
--   Consequently, $\psi_{s,a}(v)=\phi_{H_s,a}(v)$ for every $v\in S\cup S'$ and $a\in\{L,R\}$.
--
--   The same copy serves every vertex of both requests, so changes of each aggregate coordinate of $\Psi$ between consecutive requests are changes of a single branch function (used in Lemma 8).
--
--   Differences from the source:
--   - encoding: a realized level-r request sequence → a list of annotated requests in the support of the PMF D_r, read through its plain sets; reason: the annotation records the call structure and does not change the requested sets
--   - reading: "a fixed rule to break a tie" (Stage 3) → the statement holds for both fixed rules (tie : Bool); reason: the paper does not specify the rule
--   - reading: "the final request of this stage consists of the two current vertices" (Stage 2) → the last request of the last Stage-2 call, no extra request; reason: that last request is exactly the pair of current vertices
-- source:
--   Nicolas Christianson, A Linear Lower Bound for Convex Body Chasing in Every Norm, STOC 2027 submission #674 (October 2026), pp.10–11, Corollary 6, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/674.pdf

import Mathlib
import Definitions.Def_CBCLowerBound_EveryNorm_Requests

namespace CBCLowerBound.EveryNorm

/-- **Corollary 6** (Christianson, STOC 2027 #674, pp.10–11). Let `S, S'` be consecutive
requests of a sequence in the support of `D_r` (any parameters, tie rule, level `r`). For each
level `s ∈ {1, …, r}` there is a level-`s` copy `H_s` such that every other level-`s` copy
`H'_s ≠ H_s` has both branch functions equal to zero on `S ∪ S'`; consequently
`ψ_{s,a}(v) = ϕ_{H_s,a}(v)` for every `v ∈ S ∪ S'` and `a ∈ {L, R}`. -/
theorem corollary_6 (θ : Params) (tie : Bool) (r : ℕ) (σ : List (AReq θ r))
    (hσ : σ ∈ (reqDist θ tie r).support) (t : ℕ) (ht : t + 1 < σ.length) :
    ∀ s : ℕ, 1 ≤ s → s ≤ r → ∃ Hs : Copy θ r s,
      (∀ H' : Copy θ r s, H' ≠ Hs → ∀ v ∈ (σ[t]).set ∪ (σ[t + 1]).set, ∀ a : Bool,
        H'.phi a v = 0) ∧
      ∀ v ∈ (σ[t]).set ∪ (σ[t + 1]).set, ∀ a : Bool, psi θ r s a v = Hs.phi a v := by sorry

end CBCLowerBound.EveryNorm
