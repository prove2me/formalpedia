-- Prove2me | Theorems.Thm_CongestionPoA_SymSum_symmetric_poa_sum_eq
-- name    : CongestionPoA.SymSum.symmetric_poa_sum_eq
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-04T17:51:43.033155+00:00
-- url     : https://prove2.me/theorems/cd06efa6-16a3-4572-9e13-3e512ad1bf3d
-- title:
--   Theorems 3 and 4 — the pure price of anarchy of the average social cost of symmetric linear congestion games is $\frac{5N-2}{2N+1}$
-- statement:
--   Fix the number of players $N\ge1$.
--
--   1. (Theorem 3) For every symmetric congestion game with $N$ players and linear latencies $f_e(k)=a_ek+b_e$, $a_e,b_e\ge0$, every pure Nash equilibrium $A$ and every pure strategy profile $P$ satisfy
--   $$\mathrm{SUM}(A)\le\frac{5N-2}{2N+1}\,\mathrm{SUM}(P).$$
--   2. (Theorem 4) There is such a game, with a pure Nash equilibrium $A$ and a pure strategy profile $P$ with $\mathrm{SUM}(P)>0$, for which equality holds.
--
--   Together: the pure price of anarchy of the average social cost over symmetric linear congestion games with $N$ players is exactly $(5N-2)/(2N+1)$, strictly below the value $5/2$ of asymmetric games for every $N$.
--
--   **Formalization Note** Facility sets are arbitrary finite types; the condition $\mathrm{SUM}(P)>0$ excludes the trivial all-zero witness of the lower bound.
-- source:
--   Christodoulou and Koutsoupias, The Price of Anarchy of Finite Congestion Games, STOC 2005, DOI 10.1145/1060590.1060600, PDF p. 3, Theorem 3 and PDF p. 4, Theorem 4

import Mathlib
import Definitions.Def_CongestionPoA_SymSum_Model

namespace CongestionPoA.SymSum

/-- Christodoulou and Koutsoupias, *The Price of Anarchy of Finite Congestion Games*, STOC 2005,
PDF pp. 3–4, Theorems 3 and 4: for symmetric linear congestion games with `N` players the pure price
of anarchy of the average social cost is exactly `(5N − 2)/(2N + 1)`. For every `N ≥ 1`:
(Theorem 3) every pure Nash equilibrium `A` of every symmetric linear congestion game with players
`Fin N` satisfies `SUM(A) ≤ ((5N − 2)/(2N + 1))·SUM(P)` for every pure strategy profile `P`; and
(Theorem 4) some symmetric linear game with players `Fin N` has a pure Nash equilibrium `A` and a
profile `P` with `SUM(P) > 0` and `SUM(A) = ((5N − 2)/(2N + 1))·SUM(P)`.

**Formalization Note.** The bound for every profile `P` is equivalent to `PA ≤ (5N − 2)/(2N + 1)`
(the optimum is attained); with the second part it gives `PA = (5N − 2)/(2N + 1)` as a worst case over
the class. `SUM(P) > 0` excludes the trivial all-zero witness. Linear latencies are
`f_e(k) = a_e k + b_e` with `a_e, b_e ≥ 0`; the paper's proofs display `f_e(k) = k`. Facility types
range over `Type` with `Fintype` and `DecidableEq`. -/
theorem symmetric_poa_sum_eq (N : ℕ) (hN : 1 ≤ N) :
    (∀ (E : Type) [Fintype E] [DecidableEq E] (G : CongestionPoA.AsymSum.CongestionGame (Fin N) E)
        (A P : Fin N → Finset E),
        CongestionPoA.AsymSum.IsLinear G → IsSymmetric G → CongestionPoA.AsymSum.IsPureNash G A → CongestionPoA.AsymSum.IsProfile G P →
          CongestionPoA.AsymSum.sumCost G A ≤ (5 * (N : ℝ) - 2) / (2 * (N : ℝ) + 1) * CongestionPoA.AsymSum.sumCost G P) ∧
    ∃ (E : Type) (_ : Fintype E) (_ : DecidableEq E) (G : CongestionPoA.AsymSum.CongestionGame (Fin N) E)
      (A P : Fin N → Finset E),
      CongestionPoA.AsymSum.IsLinear G ∧ IsSymmetric G ∧ CongestionPoA.AsymSum.IsPureNash G A ∧ CongestionPoA.AsymSum.IsProfile G P ∧ 0 < CongestionPoA.AsymSum.sumCost G P ∧
        CongestionPoA.AsymSum.sumCost G A = (5 * (N : ℝ) - 2) / (2 * (N : ℝ) + 1) * CongestionPoA.AsymSum.sumCost G P := by sorry

end CongestionPoA.SymSum
