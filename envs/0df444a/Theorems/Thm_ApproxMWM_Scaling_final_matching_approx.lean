-- Prove2me | Theorems.Thm_ApproxMWM_Scaling_final_matching_approx
-- name    : ApproxMWM.Scaling.final_matching_approx
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-27T13:10:17.643621+00:00
-- url     : https://prove2.me/theorems/3d9072f3-bb1a-4e78-abc3-4f256b6862ba
-- title:
--   Lemma 3.7 — after scale $L$, $M$ is a $(1-5\epsilon')$-MWM
-- statement:
--   Let $G$ be a finite simple graph with integer edge weights $1\le w(e)\le N=2^L$ and $\epsilon'=2^{-g}\le1/4$. Every matching $M$ returned by a terminating run of the scaling algorithm of Figure 2 with the eligibility of Definition 3.2 (that is, $M$ after scale $L=\log N$) is a $(1-5\epsilon')$-MWM: $M$ is a matching of $G$ and
--   $$w(M)\ \ge\ (1-5\epsilon')\,w(M')$$
--   for every matching $M'$ of $G$.
--
--   Combined with the existence of a terminating run, this gives the approximation half of Theorem 3.8.
--
--   **Formalization Note** The proof in the paper obtains the intermediate bound $w(M)\ge(1-\epsilon')(1+4\epsilon')^{-1}w(M^*)$; the lemma's own statement, formalized here, is the $(1-5\epsilon')$ bound.
-- source:
--   Duan and Pettie, Linear-Time Approximation for Maximum Weight Matching, J. ACM 61(1), Article 1 (2014), https://doi.org/10.1145/2529989, p. 1:17, Lemma 3.7

import Mathlib
import Definitions.Def_ApproxMWM_Scaling_Property31

namespace ApproxMWM.Scaling

/-- Lemma 3.7 (Duan–Pettie, J. ACM 61(1) 2014, p. 1:17): after scale `L = log N`, `M` is a
`(1 - 5ε')`-MWM. For integer weights `1 ≤ w(e) ≤ N = 2^L` on the edges of `G`, every matching
returned by a terminating run of the algorithm of Figure 2 with the eligibility of Definition 3.2
is a `(1 - 5ε')`-MWM of `(G, w)`. -/
theorem final_matching_approx {V : Type*} [Fintype V] [DecidableEq V]
    (P : Params) (G : SimpleGraph V) (w : Sym2 V → ℕ)
    (hw : ∀ e ∈ G.edgeSet, 1 ≤ w e ∧ w e ≤ 2 ^ P.L)
    (M : Finset (Sym2 V)) (hM : Returns P G (elig32 P G w) M) :
    IsApproxMWM G (fun e => (w e : ℝ)) (1 - 5 * P.eps') M := by sorry

end ApproxMWM.Scaling
