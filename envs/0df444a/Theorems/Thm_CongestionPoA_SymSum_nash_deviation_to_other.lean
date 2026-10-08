-- Prove2me | Theorems.Thm_CongestionPoA_SymSum_nash_deviation_to_other
-- name    : CongestionPoA.SymSum.nash_deviation_to_other
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-04T17:50:48.210977+00:00
-- url     : https://prove2.me/theorems/d6a3022e-aa70-4ce2-ba9c-c24735bcbdb5
-- title:
--   Theorem 3, proof — at a Nash equilibrium of a symmetric game, deviating to any $P_j$ does not help
-- statement:
--   Let $G$ be a symmetric congestion game with $N$ players and linear latencies $f_e(k)=a_ek+b_e$, $a_e,b_e\ge0$. Let $A$ be a pure Nash equilibrium and $P$ any pure strategy profile. Because the game is symmetric, every $P_j$ is a strategy of every player, so for all players $i$ and $j$
--   $$c_i(A)\le \sum_{e\in P_j}\bigl(a_e\,n_e(A)+b_e\bigr)+\sum_{e\in P_j\setminus A_i} a_e .$$
--   For identity latencies ($a_e=1$, $b_e=0$) this is the paper's $c_i(A)\le\sum_{e\in P_j} n_e(A)+|P_j-A_i|$.
--
--   This is the first step of the upper bound of Theorem 3: unlike the asymmetric case, player $i$ may compare its cost with the strategy of *every* player $j$ in the comparison profile.
--
--   **Formalization Note** The coefficients $a_e,b_e$ are explicit parameters with $G$'s latency equal to $a_ek+b_e$. Players are $\{0,\dots,N-1\}$.
-- source:
--   Christodoulou and Koutsoupias, The Price of Anarchy of Finite Congestion Games, STOC 2005, DOI 10.1145/1060590.1060600, PDF p. 3, Theorem 3, proof (first display)

import Mathlib
import Definitions.Def_CongestionPoA_SymSum_Model

namespace CongestionPoA.SymSum

/-- Christodoulou and Koutsoupias, *The Price of Anarchy of Finite Congestion Games*, STOC 2005,
PDF p. 3, unnumbered step of the proof of Theorem 3: in a symmetric game every strategy is
available to every player, so at a pure Nash equilibrium `A` the cost of player `i` is at most the
cost of deviating to the strategy `Pⱼ` of any player `j` in any pure strategy profile `P`:
`cᵢ(A) ≤ Σ_{e∈Pⱼ} n_e(A) + |Pⱼ − Aᵢ|`.

**Formalization Note.** The paper displays the identity latencies `f_e(k) = k`; for the linear
latencies `f_e(k) = a_e k + b_e` (`a_e, b_e ≥ 0`) of Sect. 2 the right-hand side is
`Σ_{e∈Pⱼ} (a_e n_e(A) + b_e) + Σ_{e∈Pⱼ∖Aᵢ} a_e`, which is the printed one when `a_e = 1`,
`b_e = 0`. The coefficients are explicit binders. Players are `Fin N`; `Pⱼ ∈ Σᵢ` follows from
`P` being a profile and the game being symmetric. -/
theorem nash_deviation_to_other {N : ℕ} {E : Type*} [Fintype E] [DecidableEq E]
    (G : CongestionPoA.AsymSum.CongestionGame (Fin N) E) (a b : E → ℝ) (ha : ∀ e, 0 ≤ a e) (hb : ∀ e, 0 ≤ b e)
    (hlin : ∀ e k, G.latency e k = a e * k + b e) (hsym : IsSymmetric G)
    (A P : Fin N → Finset E) (hA : CongestionPoA.AsymSum.IsPureNash G A) (hP : CongestionPoA.AsymSum.IsProfile G P) (i j : Fin N) :
    CongestionPoA.AsymSum.cost G A i ≤ ∑ e ∈ P j, (a e * (CongestionPoA.AsymSum.load A e : ℝ) + b e) + ∑ e ∈ P j \ A i, a e := by sorry

end CongestionPoA.SymSum
