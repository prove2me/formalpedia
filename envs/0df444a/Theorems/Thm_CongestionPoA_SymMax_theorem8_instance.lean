-- Prove2me | Theorems.Thm_CongestionPoA_SymMax_theorem8_instance
-- name    : CongestionPoA.SymMax.theorem8_instance
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-04T09:12:07.841348+00:00
-- url     : https://prove2.me/theorems/8a70100d-8a6e-4671-87cd-947b74f519d6
-- title:
--   Theorem 8 — symmetric instances with $\mathrm{MAX}(A)=\frac{5N+1}{2N+2}\mathrm{MAX}(P)$
-- statement:
--   There are instances of symmetric congestion games for which the price of anarchy of the maximum social cost is $\frac{5N+1}{2N+2}$. Precisely: for every $N\ge 3$ there is a symmetric congestion game with $N$ players, finitely many facilities and linear latencies, together with a pure Nash equilibrium $A$ and a pure strategy profile $P$ such that
--
--   1. $P$ minimizes the maximum social cost: $\mathrm{MAX}(P)\le\mathrm{MAX}(Q)$ for every pure profile $Q$;
--   2. $\mathrm{MAX}(P)>0$;
--   3. the maximum costs satisfy
--   $$\mathrm{MAX}(A)=\frac{5N+1}{2N+2}\,\mathrm{MAX}(P).$$
--
--   Hence the price of anarchy of that instance is at least $\frac{5N+1}{2N+2}$, which tends to $5/2$: Theorem 7 is tight in the limit.
--
--   **Formalization Note** The statement gives $\mathrm{PA}\ge\frac{5N+1}{2N+2}$ for the instance; the paper's proof exhibits the pair $(A,P)$ and does not show that $A$ is a worst equilibrium. $\mathrm{MAX}(P)>0$ excludes the trivial witness with all costs $0$. The paper's construction uses identity latencies, which are linear. The range $N\ge3$ is that of the construction. The typeclass assumption `NeZero N` only provides the nonempty player set required by $\mathrm{MAX}$.
-- source:
--   Christodoulou and Koutsoupias, The Price of Anarchy of Finite Congestion Games, STOC 2005, DOI 10.1145/1060590.1060600, PDF p. 5, Theorem 8

import Mathlib
import Definitions.Def_CongestionPoA_SymMax_Model

namespace CongestionPoA.SymMax

/-- Christodoulou and Koutsoupias, *The Price of Anarchy of Finite Congestion Games*, STOC 2005,
PDF p. 5, Theorem 8: there are instances of symmetric congestion games for which the price of anarchy
is `(5N+1)/(2N+2)`, for maximum social cost. Stated as: for every `N ≥ 3` there is a symmetric linear
congestion game with players `Fin N` and finitely many facilities, a pure Nash equilibrium `A` and a
pure profile `P` that minimizes the maximum social cost, with `MAX(P) > 0` and
`MAX(A) = ((5N+1)/(2N+2))·MAX(P)`.

**Formalization Note.** The conclusion gives `PA ≥ (5N+1)/(2N+2)` for the instance (`P` attains the
optimum `min_Q MAX(Q)`, `A` is a Nash equilibrium); this is what the paper's proof establishes — it
does not show that `A` is a worst equilibrium. `MAX(P) > 0` excludes the trivial witness with all
costs `0`. The paper's construction uses identity latencies `f_e(k) = k`, which are linear, so the
word "linear" omitted in the theorem's sentence is harmless (the section is about linear latencies).
`N ≥ 3` is the range of the construction (its equation (2) has the factor `N − 3`, and `α₂ = 0` at
`N = 3`); the paper leaves the range implicit. `[NeZero N]` only supplies the nonempty player set
`MAX` needs and is implied by `3 ≤ N`. The statement does not fix the construction. -/
theorem theorem8_instance (N : ℕ) [NeZero N] (hN : 3 ≤ N) :
    ∃ (E : Type) (_ : Fintype E) (_ : DecidableEq E) (G : CongestionGame (Fin N) E)
      (A P : Fin N → Finset E),
      IsLinear G ∧ IsSymmetric G ∧ IsPureNash G A ∧ IsProfile G P ∧
      (∀ Q : Fin N → Finset E, IsProfile G Q → maxCost G P ≤ maxCost G Q) ∧
      0 < maxCost G P ∧
      maxCost G A = (5 * N + 1) / (2 * N + 2) * maxCost G P := by sorry

end CongestionPoA.SymMax
