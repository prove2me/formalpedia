-- Prove2me | Theorems.Thm_CBCLowerBound_EveryNorm_lemma_7
-- name    : CBCLowerBound.EveryNorm.lemma_7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:22:46.563011+00:00
-- url     : https://prove2.me/theorems/a090e72f-8252-497c-8c3f-c954e416a741
-- title:
--   Lemma 7 — co-occurring vertices on opposite branches of $H$ satisfy $d_G(u,v)\le 4g_H(u)$
-- statement:
--   Fix admissible parameters, a tie rule and a level $r$, and let $\sigma$ be a request sequence in the support of $D_r$ on $G=G_r$. Let $H$ be a copy of $G_{s+1}$ in $G$ (a copy with two branches), and let $u,v$ be vertices that lie on opposite branches of $H$ and co-occur in a request issued during the call to $H$. Then
--   $$d_G(u,v)\le 4\,g_H(u)\qquad\text{(eq. (8))},$$
--   where $g_H(u)=\min\{h_H(u),L_H-h_H(u)\}$ is the distance of $u$ to the nearer endpoint of $H$, all lengths measured in $G$.
--
--   The bound controls the cost of moving mass from a waiting vertex, and of the Stage-3 removal, by the corresponding aggregate coordinate of $\Psi$ (Lemma 8).
--
--   **Formalization Note** "Lies on branch $a$ of $H$" includes the endpoints $s_H,t_H$, which lie on both branches (p.9). "Issued during the call to $H$" means $H$ contains the request's innermost active call.
--
--   Differences from the source:
--   - encoding: "a copy H" with two branches → a copy of G_{s+1}, s ≥ 0; reason: only copies of level ≥ 1 have branches
--   - encoding: "co-occur in a request in a call to H" → both lie in the set of an annotated request of σ whose innermost call is contained in H; reason: the annotation records the calls of the construction
--   - encoding: a realized level-r request sequence → a list of annotated requests in the support of the PMF D_r, read through its plain sets; reason: the annotation records the call structure and does not change the requested sets
--   - reading: "a fixed rule to break a tie" (Stage 3) → the statement holds for both fixed rules (tie : Bool); reason: the paper does not specify the rule
--   - reading: "the final request of this stage consists of the two current vertices" (Stage 2) → the last request of the last Stage-2 call, no extra request; reason: that last request is exactly the pair of current vertices
-- source:
--   Nicolas Christianson, A Linear Lower Bound for Convex Body Chasing in Every Norm, STOC 2027 submission #674 (October 2026), p.11, Lemma 7, eq. (8), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/674.pdf

import Mathlib
import Definitions.Def_CBCLowerBound_EveryNorm_Requests

namespace CBCLowerBound.EveryNorm

/-- **Lemma 7** (distance between co-occurring vertices; Christianson, STOC 2027 #674, p.11).
Let `σ` be in the support of `D_r` (any parameters, tie rule, level `r`), let `H` be a copy of
`G_{s+1}` (a copy with two branches), and let `u, v` lie on opposite branches of `H` and
co-occur in a request issued in the call to `H`. Then `d_G(u, v) ≤ 4 g_H(u)` (eq. (8)). -/
theorem lemma_7 (θ : Params) (tie : Bool) (r : ℕ) (σ : List (AReq θ r))
    (hσ : σ ∈ (reqDist θ tie r).support) (q : AReq θ r) (hq : q ∈ σ) (s : ℕ)
    (H : Copy θ r (s + 1)) (hH : H.Contains q.copy) (u v : Vert θ r) (a : Bool)
    (hu : u ∈ q.set) (hv : v ∈ q.set) (hua : H.OnBranch a u) (hvb : H.OnBranch (!a) v) :
    dist θ r u v ≤ 4 * H.g u := by sorry

end CBCLowerBound.EveryNorm
