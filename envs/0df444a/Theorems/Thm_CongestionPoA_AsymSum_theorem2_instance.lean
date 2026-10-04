-- Prove2me | Theorems.Thm_CongestionPoA_AsymSum_theorem2_instance
-- name    : CongestionPoA.AsymSum.theorem2_instance
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-04T08:48:50.197866+00:00
-- url     : https://prove2.me/theorems/008f55c2-304e-4e26-9f7b-ba11516bbf98
-- title:
--   Theorem 2 — for every N ≥ 3, a linear congestion game with pure price of anarchy 5/2
-- statement:
--   There are linear congestion games with $3$ or more players with pure price of anarchy for the average social cost equal to $5/2$.
--
--   Precisely: for every integer $N\ge3$ there exist a congestion game $G$ with $N$ players, finitely many facilities and linear latencies $f_e(k)=a_ek+b_e$ ($a_e,b_e\ge0$), a pure Nash equilibrium $A$ of $G$ and an optimal pure strategy profile $P$ of $G$ ($\mathrm{SUM}(P)\le\mathrm{SUM}(Q)$ for every pure strategy profile $Q$) with $\mathrm{SUM}(P)>0$ and
--   $$\mathrm{SUM}(A)=\frac52\,\mathrm{SUM}(P).$$
--
--   So the pure price of anarchy of $G$ is at least $5/2$; combined with Theorem 1 it is exactly $5/2$; hence the bound of Theorem 1 is tight for every number of players $N\ge3$.
--
--   **Formalization Note** The statement asserts only the existence of such a game; the paper's construction (with $2N$ facilities $h_1,\dots,h_N,g_1,\dots,g_N$, player $i$ choosing $\{h_i,g_i\}$ or $\{g_{i+1},h_{i-1},h_{i+1}\}$ with indices taken cyclically, and identity latencies) is one witness, but any witness proves the statement. Players are the type $\mathrm{Fin}\,N$. The condition $\mathrm{SUM}(P)>0$ excludes the all-zero latency game, in which $0=\frac52\cdot0$ holds trivially.
-- source:
--   Christodoulou and Koutsoupias, The Price of Anarchy of Finite Congestion Games, STOC 2005, DOI 10.1145/1060590.1060600, PDF p. 3, Theorem 2

import Mathlib
import Definitions.Def_CongestionPoA_AsymSum_Model

namespace CongestionPoA.AsymSum

/-- Christodoulou and Koutsoupias, *The Price of Anarchy of Finite Congestion Games*, STOC 2005,
PDF p. 3, Theorem 2: there are linear congestion games with `3` or more players with pure price of
anarchy for the average social cost equal to `5/2`. Stated as: for every `N ≥ 3` there is a linear
congestion game with players `Fin N` and finitely many facilities, a pure Nash equilibrium `A` and a
pure strategy profile `P` that is optimal (`SUM(P) ≤ SUM(Q)` for every pure strategy profile `Q`),
with `0 < SUM(P)` and `SUM(A) = (5/2)·SUM(P)`.

**Formalization Note.** `opt = SUM(P) > 0` and `SUM(A)/opt = 5/2` give `PA ≥ 5/2` for this game, and
Theorem 1 gives `PA ≤ 5/2`, so `PA = 5/2`. The positivity `0 < SUM(P)` is needed: without it the
all-zero latency game (`a_e = b_e = 0`, linear) satisfies `0 = (5/2)·0` and the statement says nothing. Linear latencies are `f_e(k) = a_e k + b_e` with
`a_e, b_e ≥ 0`. The paper's construction (2N facilities `h₁…h_N, g₁…g_N`, strategies `{hᵢ, gᵢ}` and
`{g_{i+1}, h_{i−1}, h_{i+1}}` with cyclic indices, identity latencies) is one witness; the statement
does not fix it. -/
theorem theorem2_instance (N : ℕ) (hN : 3 ≤ N) :
    ∃ (E : Type) (_ : Fintype E) (_ : DecidableEq E) (G : CongestionGame (Fin N) E)
      (A P : Fin N → Finset E),
      IsLinear G ∧ IsPureNash G A ∧ IsProfile G P ∧
        (∀ Q : Fin N → Finset E, IsProfile G Q → sumCost G P ≤ sumCost G Q) ∧
        0 < sumCost G P ∧ sumCost G A = 5 / 2 * sumCost G P := by sorry

end CongestionPoA.AsymSum
