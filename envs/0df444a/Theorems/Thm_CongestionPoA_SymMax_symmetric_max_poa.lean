-- Prove2me | Theorems.Thm_CongestionPoA_SymMax_symmetric_max_poa
-- name    : CongestionPoA.SymMax.symmetric_max_poa
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-04T09:12:16.336216+00:00
-- url     : https://prove2.me/theorems/49f15c59-dd01-4b2d-aff8-4bc3a1114dff
-- title:
--   Theorems 7 and 8 — symmetric linear congestion games: maximum social cost PoA $\le 5/2$, tight in the limit
-- statement:
--   For symmetric congestion games with linear latencies $f_e(k)=a_ek+b_e$ ($a_e,b_e\ge0$), the pure price of anarchy of the maximum social cost $\mathrm{MAX}(A)=\max_i c_i(A)$ is at most $5/2$, and this is tight in the limit.
--
--   1. (Theorem 7) For every symmetric linear congestion game with at least one player, every pure Nash equilibrium $A$ and every pure strategy profile $P$,
--   $$\mathrm{MAX}(A)\le\tfrac52\,\mathrm{MAX}(P).$$
--   2. (Theorem 8) For every $N\ge3$ there is a symmetric linear congestion game with $N$ players, a pure Nash equilibrium $A$ and a profile $P$ minimizing the maximum social cost, with $\mathrm{MAX}(P)>0$ and
--   $$\mathrm{MAX}(A)=\frac{5N+1}{2N+2}\,\mathrm{MAX}(P).$$
--
--   Since $\frac{5N+1}{2N+2}\to\frac52$, the constant of part 1 cannot be lowered uniformly in $N$. Without symmetry the maximum social cost price of anarchy grows like $\sqrt N$.
--
--   **Formalization Note** Part 1 is stated for every Nash $A$ and feasible $P$, which is equivalent to $\mathrm{PA}\le5/2$ without dividing by the optimum. Part 2 gives $\mathrm{PA}\ge\frac{5N+1}{2N+2}$ for the instance, which is what the paper's construction shows.
-- source:
--   Christodoulou and Koutsoupias, The Price of Anarchy of Finite Congestion Games, STOC 2005, DOI 10.1145/1060590.1060600, PDF p. 5, Theorems 7 and 8

import Mathlib
import Definitions.Def_CongestionPoA_SymMax_Model

namespace CongestionPoA.SymMax

/-- Christodoulou and Koutsoupias, *The Price of Anarchy of Finite Congestion Games*, STOC 2005,
PDF p. 5, Theorems 7 and 8 (Sect. 3.4): for symmetric linear congestion games the pure price of
anarchy of the maximum social cost is at most `5/2`, and for every `N ≥ 3` some symmetric linear
instance with `N` players has a pure Nash equilibrium whose maximum cost is `(5N+1)/(2N+2)` times the
optimal one (positive) — so the bound `5/2` is tight in the limit `N → ∞`.

**Formalization Note.** First conjunct: every finite nonempty player type `ι`, every finite facility
type, affine latencies `f_e(k) = a_e k + b_e` with `a_e, b_e ≥ 0`, `MAX(A) ≤ (5/2)·MAX(P)` for every
Nash `A` and every feasible `P` (equivalent to `PA ≤ 5/2`, without dividing by the optimum). Second
conjunct: as in `theorem8_instance` — `P` is optimal for the maximum social cost, `MAX(P) > 0`, and
the ratio is exact for the pair `(A, P)`, i.e. `PA ≥ (5N+1)/(2N+2)` for the instance. -/
theorem symmetric_max_poa :
    (∀ (ι E : Type) [Fintype ι] [DecidableEq ι] [Nonempty ι] [Fintype E] [DecidableEq E]
        (G : CongestionGame ι E) (A P : ι → Finset E),
        IsLinear G → IsSymmetric G → IsPureNash G A → IsProfile G P →
        maxCost G A ≤ 5 / 2 * maxCost G P) ∧
    (∀ (N : ℕ) [NeZero N], 3 ≤ N →
      ∃ (E : Type) (_ : Fintype E) (_ : DecidableEq E) (G : CongestionGame (Fin N) E)
        (A P : Fin N → Finset E),
        IsLinear G ∧ IsSymmetric G ∧ IsPureNash G A ∧ IsProfile G P ∧
        (∀ Q : Fin N → Finset E, IsProfile G Q → maxCost G P ≤ maxCost G Q) ∧
        0 < maxCost G P ∧
        maxCost G A = (5 * N + 1) / (2 * N + 2) * maxCost G P) := by sorry

end CongestionPoA.SymMax
