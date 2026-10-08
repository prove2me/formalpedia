-- Prove2me | Theorems.Thm_CongestionPoA_SymSum_sum_over_j_bound
-- name    : CongestionPoA.SymSum.sum_over_j_bound
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-04T17:51:08.693299+00:00
-- url     : https://prove2.me/theorems/da99f130-36b2-4859-ae54-b9d8fcf51948
-- title:
--   Theorem 3, proof — summing over $j$: a bound on $N\cdot c_i(A)$
-- statement:
--   Let $G$ be a symmetric congestion game with $N$ players and linear latencies $f_e(k)=a_ek+b_e$, $a_e,b_e\ge0$; let $A$ be a pure Nash equilibrium and $P$ any pure strategy profile. Then for every player $i$
--   $$N\,c_i(A)\le \sum_{e\in E} n_e(P)\bigl(a_e n_e(A)+b_e\bigr)+\sum_{e\in E}a_e\,n_e(P)-\sum_{e\in A_i}a_e\,n_e(P).$$
--   For identity latencies this is the paper's $N\,c_i(A)\le\sum_{e}n_e(P)n_e(A)+\sum_e n_e(P)-\sum_{e\in A_i}n_e(P)$.
--
--   It is obtained by adding the deviation inequalities over all $j\in N$; the negative last term is what makes the symmetric bound smaller than $5/2$.
--
--   **Formalization Note** The coefficients are explicit parameters; $N$ is the number of players.
-- source:
--   Christodoulou and Koutsoupias, The Price of Anarchy of Finite Congestion Games, STOC 2005, DOI 10.1145/1060590.1060600, PDF p. 3, Theorem 3, proof (second display)

import Mathlib
import Definitions.Def_CongestionPoA_SymSum_Model

namespace CongestionPoA.SymSum

/-- Christodoulou and Koutsoupias, *The Price of Anarchy of Finite Congestion Games*, STOC 2005,
PDF p. 3, unnumbered step of the proof of Theorem 3: summing the deviation inequality over all
`j ∈ N` bounds player `i`'s cost,
`N · cᵢ(A) ≤ Σ_{e∈E} n_e(P)n_e(A) + Σ_{e∈E} n_e(P) − Σ_{e∈Aᵢ} n_e(P)`.

**Formalization Note.** Printed for identity latencies; for linear latencies `f_e(k) = a_e k + b_e`
(`a_e, b_e ≥ 0`, explicit binders) the bound reads
`N · cᵢ(A) ≤ Σ_e n_e(P)(a_e n_e(A) + b_e) + Σ_e a_e n_e(P) − Σ_{e∈Aᵢ} a_e n_e(P)`, the printed one when
`a_e = 1`, `b_e = 0`. `N` is the number of players (`Fin N`); `P` is any pure strategy profile. -/
theorem sum_over_j_bound {N : ℕ} {E : Type*} [Fintype E] [DecidableEq E]
    (G : CongestionPoA.AsymSum.CongestionGame (Fin N) E) (a b : E → ℝ) (ha : ∀ e, 0 ≤ a e) (hb : ∀ e, 0 ≤ b e)
    (hlin : ∀ e k, G.latency e k = a e * k + b e) (hsym : IsSymmetric G)
    (A P : Fin N → Finset E) (hA : CongestionPoA.AsymSum.IsPureNash G A) (hP : CongestionPoA.AsymSum.IsProfile G P) (i : Fin N) :
    (N : ℝ) * CongestionPoA.AsymSum.cost G A i ≤
      ∑ e, (CongestionPoA.AsymSum.load P e : ℝ) * (a e * (CongestionPoA.AsymSum.load A e : ℝ) + b e) + ∑ e, a e * (CongestionPoA.AsymSum.load P e : ℝ)
        - ∑ e ∈ A i, a e * (CongestionPoA.AsymSum.load P e : ℝ) := by sorry

end CongestionPoA.SymSum
