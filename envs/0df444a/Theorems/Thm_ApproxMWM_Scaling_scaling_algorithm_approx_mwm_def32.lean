-- Prove2me | Theorems.Thm_ApproxMWM_Scaling_scaling_algorithm_approx_mwm_def32
-- name    : ApproxMWM.Scaling.scaling_algorithm_approx_mwm_def32
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-27T13:11:08.970418+00:00
-- url     : https://prove2.me/theorems/00262fb2-5007-4581-9c27-1b3e02b7f271
-- title:
--   Theorem 3.8 (approximation half) — the scaling algorithm computes a $(1-\epsilon)$-MWM
-- statement:
--   Let $G$ be a finite simple graph with integer edge weights $1\le w(e)\le N=2^L$, let $\epsilon'=2^{-g}\le1/4$, and let $\epsilon$ be a real number with $\epsilon'\le\epsilon/5$. Then the scaling algorithm of Figure 2 with the eligibility of Definition 3.2
--
--   1. has a terminating run, and
--   2. every terminating run returns a matching $M$ of $G$ with
--   $$w(M)\ \ge\ (1-\epsilon)\,w(M')\quad\text{for every matching } M' \text{ of } G .$$
--
--   The constant $\epsilon'\le\epsilon/5$ is the one the paper's proof supplies via Lemma 3.7. The paper's theorem also asserts an $O(m\epsilon^{-1}\log N)$ running time, which this item does not state.
--
--   **Formalization Note** The running time is not formalized: the paper gives no cost model (it uses a modified depth-first search of Gabow and Tarjan and word-RAM operations). The existence conjunct rules out a vacuous statement about an unsatisfiable run relation.
-- source:
--   Duan and Pettie, Linear-Time Approximation for Maximum Weight Matching, J. ACM 61(1), Article 1 (2014), https://doi.org/10.1145/2529989, p. 1:17, Theorem 3.8 (approximation half; ϵ′ ≤ ϵ/5 from its proof)

import Mathlib
import Definitions.Def_ApproxMWM_Scaling_Property31

namespace ApproxMWM.Scaling

/-- Theorem 3.8 (Duan–Pettie, J. ACM 61(1) 2014, p. 1:17), approximation half. For integer
weights `1 ≤ w(e) ≤ N = 2^L` on the edges of `G`, `ε' = 2^{-g} ≤ 1/4` and `ε' ≤ ε/5`, the
algorithm of Figure 2 with the eligibility of Definition 3.2 has a terminating run, and every
terminating run returns a `(1 - ε)`-MWM of `(G, w)`. The paper's theorem also asserts an
`O(m ε⁻¹ log N)` running time, which is not stated here. -/
theorem scaling_algorithm_approx_mwm_def32 {V : Type*} [Fintype V] [DecidableEq V]
    (P : Params) (G : SimpleGraph V) (w : Sym2 V → ℕ)
    (hw : ∀ e ∈ G.edgeSet, 1 ≤ w e ∧ w e ≤ 2 ^ P.L)
    (ε : ℝ) (hε : P.eps' ≤ ε / 5) :
    (∃ M : Finset (Sym2 V), Returns P G (elig32 P G w) M) ∧
    ∀ M : Finset (Sym2 V), Returns P G (elig32 P G w) M →
      IsApproxMWM G (fun e => (w e : ℝ)) (1 - ε) M := by sorry

end ApproxMWM.Scaling
