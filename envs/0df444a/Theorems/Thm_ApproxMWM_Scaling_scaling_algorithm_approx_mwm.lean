-- Prove2me | Theorems.Thm_ApproxMWM_Scaling_scaling_algorithm_approx_mwm
-- name    : ApproxMWM.Scaling.scaling_algorithm_approx_mwm
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-27T13:12:12.927855+00:00
-- url     : https://prove2.me/theorems/e81d8972-f382-4812-a5b6-7cfe18369596
-- title:
--   Theorem 3.12 (approximation half) — the linear-time scaling algorithm computes a $(1-\epsilon)$-MWM
-- statement:
--   Let $G$ be a finite simple graph with integer edge weights $1\le w(e)\le N=2^L$, let $\epsilon'=2^{-g}\le1/4$, and let $\epsilon$ be a real number with $\epsilon'\le\epsilon/7$. Then the scaling algorithm of Figure 2 run with the eligibility of Definition 3.10
--
--   1. has a terminating run, and
--   2. every terminating run returns a matching $M$ of $G$ with
--   $$w(M)\ \ge\ (1-\epsilon)\,w(M')\quad\text{for every matching } M' \text{ of } G .$$
--
--   The paper's proof shows the output is a $\big((1-\epsilon')(1+6\epsilon')^{-1}\big)$-MWM, which for $\epsilon'\le\epsilon/7$ is a $(1-\epsilon)$-MWM; the proof yields the constant $7$. The paper's theorem also asserts an $O(m\epsilon^{-1}\log\epsilon^{-1})$ running time, which this item does not state.
--
--   **Formalization Note** The running time is not formalized: the paper fixes no cost model (it relies on a modified depth-first search of Gabow and Tarjan and on a most-significant-bit table in the word RAM). The algorithm is a nondeterministic relation; the statement asserts that a terminating run exists and bounds the output of every terminating run.
-- source:
--   Duan and Pettie, Linear-Time Approximation for Maximum Weight Matching, J. ACM 61(1), Article 1 (2014), https://doi.org/10.1145/2529989, p. 1:19, Theorem 3.12 (approximation half; ϵ′ ≤ ϵ/7 from its proof)

import Mathlib
import Definitions.Def_ApproxMWM_Scaling_Property31

namespace ApproxMWM.Scaling

/-- Theorem 3.12 (Duan–Pettie, J. ACM 61(1) 2014, p. 1:19), approximation half. For integer
weights `1 ≤ w(e) ≤ N = 2^L` on the edges of `G`, `ε' = 2^{-g} ≤ 1/4` and `ε' ≤ ε/7`, the
algorithm of Figure 2 with the eligibility of Definition 3.10 has a terminating run, and every
terminating run returns a `(1 - ε)`-MWM of `(G, w)`. The paper's theorem also asserts an
`O(m ε⁻¹ log ε⁻¹)` running time, which is not stated here. -/
theorem scaling_algorithm_approx_mwm {V : Type*} [Fintype V] [DecidableEq V]
    (P : Params) (G : SimpleGraph V) (w : Sym2 V → ℕ)
    (hw : ∀ e ∈ G.edgeSet, 1 ≤ w e ∧ w e ≤ 2 ^ P.L)
    (ε : ℝ) (hε : P.eps' ≤ ε / 7) :
    (∃ M : Finset (Sym2 V), Returns P G (elig310 P G w) M) ∧
    ∀ M : Finset (Sym2 V), Returns P G (elig310 P G w) M →
      IsApproxMWM G (fun e => (w e : ℝ)) (1 - ε) M := by sorry

end ApproxMWM.Scaling
