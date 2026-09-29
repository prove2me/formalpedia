-- Prove2me | Theorems.Thm_ApproxMWM_Scaling_preserves_property31
-- name    : ApproxMWM.Scaling.preserves_property31
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-27T13:08:47.448856+00:00
-- url     : https://prove2.me/theorems/1ab61ffb-3399-45a9-8e7b-068779124e62
-- title:
--   Lemma 3.5 — the scaling algorithm preserves Property 3.1
-- statement:
--   Let $G$ be a finite simple graph with integer edge weights $1\le w(e)\le N=2^L$, and let $\epsilon'=2^{-g}\le1/4$. Run the scaling algorithm of Figure 2 with the eligibility of Definition 3.2. Then every state that occurs at scale $i$ — at the start of the scale or between two iterations — satisfies Property 3.1 at scale $i$: granularity, active blossoms, near domination $yz(e)\ge w_i(e)-\delta_i$, near tightness $yz(e)\le w_i(e)+2(\delta_j-\delta_i)$ for type-$j$ matched and blossom edges, and equal free-vertex duals strictly below the matched ones.
--
--   This invariant is what makes the output of the algorithm analysable by Lemma 2.3.
--
--   **Formalization Note** "Preserves" is stated for every state reachable by some execution (`Reach`), at the points between complete iterations; between Dual Adjustment and Blossom Dissolution a root blossom may have $z=0$, so Property 3.1(2) is not claimed there.
-- source:
--   Duan and Pettie, Linear-Time Approximation for Maximum Weight Matching, J. ACM 61(1), Article 1 (2014), https://doi.org/10.1145/2529989, p. 1:15, Lemma 3.5

import Mathlib
import Definitions.Def_ApproxMWM_Scaling_Property31

namespace ApproxMWM.Scaling

/-- Lemma 3.5 (Duan–Pettie, J. ACM 61(1) 2014, p. 1:15): the algorithm of Figure 2 with the
eligibility of Definition 3.2 preserves Property 3.1. For integer weights `1 ≤ w(e) ≤ N = 2^L` on the
edges of `G`, every state reached by an execution at scale `i` (at the start of the scale or
between two iterations) satisfies Property 3.1 at scale `i`. -/
theorem preserves_property31 {V : Type*} [Fintype V] [DecidableEq V]
    (P : Params) (G : SimpleGraph V) (w : Sym2 V → ℕ)
    (hw : ∀ e ∈ G.edgeSet, 1 ≤ w e ∧ w e ≤ 2 ^ P.L) :
    ∀ (i : ℕ) (s : State V), Reach P G (elig32 P G w) i s → Property31 P G w i s := by sorry

end ApproxMWM.Scaling
