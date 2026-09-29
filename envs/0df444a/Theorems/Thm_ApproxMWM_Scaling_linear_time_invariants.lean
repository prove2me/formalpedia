-- Prove2me | Theorems.Thm_ApproxMWM_Scaling_linear_time_invariants
-- name    : ApproxMWM.Scaling.linear_time_invariants
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-27T13:11:36.999913+00:00
-- url     : https://prove2.me/theorems/c4d68493-f6f1-4427-98ca-b10dfbc97eab
-- title:
--   Lemma 3.11 — invariants of the linear-time variant (Definition 3.10)
-- statement:
--   Let $G$ be a finite simple graph with integer edge weights $1\le w(e)\le N=2^L$, $\epsilon'=2^{-g}\le1/4$ and $\gamma=\log\epsilon'^{-1}=g$. Run the scaling algorithm of Figure 2 with the eligibility of Definition 3.10 instead of Definition 3.2. Then, at every state of the execution at scale $i$ (start of the scale or between iterations):
--
--   1. Property 3.1(1,2,5) (granularity, active blossoms, free vertex duals) holds;
--   2. for every edge $e$ with $k=\mathrm{scale}(e)$: if $i\le k+\gamma$, Property 3.1(3,4) (near domination and near tightness) hold for $e$; if $i>k+\gamma$, then
--   $$yz(e)>(1-\epsilon')\,w_i(e),$$
--   and, if $e$ is a matched or blossom edge,
--   $$yz(e)<(1+6\epsilon')\,w_i(e).$$
--
--   Together with Lemma 2.3 this yields the approximation guarantee of the linear-time algorithm.
--
--   **Formalization Note** "Throughout the execution" is formalized at the states between complete iterations and at the starts of scales (`Reach`).
-- source:
--   Duan and Pettie, Linear-Time Approximation for Maximum Weight Matching, J. ACM 61(1), Article 1 (2014), https://doi.org/10.1145/2529989, p. 1:18, Lemma 3.11

import Mathlib
import Definitions.Def_ApproxMWM_Scaling_Property31

namespace ApproxMWM.Scaling

/-- Lemma 3.11 (Duan–Pettie, J. ACM 61(1) 2014, p. 1:18). Run the algorithm of Figure 2 with the
eligibility of Definition 3.10 (integer weights `1 ≤ w(e) ≤ N = 2^L`, `γ = log ε'⁻¹ = g`).
Property 3.1(1,2,5) holds throughout the execution. For an edge `e` with `k = scale(e)`,
Property 3.1(3,4) hold for `e` in all scales `i ≤ k + γ`, and in scales `i > k + γ` in the form
`yz(e) > (1 - ε') w_i(e)` and, if `e` is a matched or blossom edge, `yz(e) < (1 + 6ε') w_i(e)`. -/
theorem linear_time_invariants {V : Type*} [Fintype V] [DecidableEq V]
    (P : Params) (G : SimpleGraph V) (w : Sym2 V → ℕ)
    (hw : ∀ e ∈ G.edgeSet, 1 ≤ w e ∧ w e ≤ 2 ^ P.L) :
    ∀ (i : ℕ) (s : State V), Reach P G (elig310 P G w) i s →
      Granularity P i s ∧ ActiveBlossoms s ∧ FreeVertexDuals s ∧
      ∀ e ∈ G.edgeSet,
        (i ≤ scaleOf P w e + P.g → NearDomAt P w i s e ∧ NearTightAt P w i s e) ∧
        (scaleOf P w e + P.g < i →
          (1 - P.eps') * truncW P w i e < yz s.y s.z e ∧
          (e ∈ s.tight → yz s.y s.z e < (1 + 6 * P.eps') * truncW P w i e)) := by sorry

end ApproxMWM.Scaling
