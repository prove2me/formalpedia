-- Prove2me | Theorems.Thm_CongestionPoA_SymMax_theorem7_max_le_five_halves
-- name    : CongestionPoA.SymMax.theorem7_max_le_five_halves
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-04T09:12:05.923585+00:00
-- url     : https://prove2.me/theorems/af6dbffb-7d37-467f-ab48-7820709b5a52
-- title:
--   Theorem 7 — symmetric linear congestion games: $\mathrm{MAX}(A)\le\frac52\mathrm{MAX}(P)$
-- statement:
--   The pure price of anarchy of symmetric linear congestion games for the maximum social cost is at most $5/2$. Precisely: let $G$ be a symmetric congestion game with at least one player and latencies $f_e(k)=a_ek+b_e$, $a_e,b_e\ge0$. For every pure Nash equilibrium $A$ and every pure strategy profile $P$,
--   $$\mathrm{MAX}(A)\;\le\;\tfrac52\,\mathrm{MAX}(P).$$
--
--   Without symmetry the maximum social cost can be of order $\sqrt N$ times optimal (Theorems 5 and 6 of the paper), so the symmetry hypothesis is essential; Theorem 8 shows the constant $5/2$ cannot be improved.
--
--   **Formalization Note** The ratio form ($\mathrm{PA}\le 5/2$) is equivalent to the inequality for every feasible $P$; no division by the optimum. The paper's proof displays only $f_e(k)=k$.
-- source:
--   Christodoulou and Koutsoupias, The Price of Anarchy of Finite Congestion Games, STOC 2005, DOI 10.1145/1060590.1060600, PDF p. 5, Theorem 7

import Mathlib
import Definitions.Def_CongestionPoA_SymMax_Model

namespace CongestionPoA.SymMax

/-- Christodoulou and Koutsoupias, *The Price of Anarchy of Finite Congestion Games*, STOC 2005,
PDF p. 5, Theorem 7: the pure price of anarchy of symmetric linear congestion games for the maximum
social cost is at most `5/2`. Stated multiplicatively: for every pure Nash equilibrium `A` and every
pure strategy profile `P` of a symmetric linear congestion game with at least one player,
`MAX(A) ≤ (5/2)·MAX(P)`.

**Formalization Note.** Linear latencies are `f_e(k) = a_e k + b_e` with `a_e, b_e ≥ 0` (Sect. 2,
§1.1; the printed proof uses `f_e(k) = k`). `PA ≤ 5/2` for the maximum social cost is equivalent to the
inequality for every Nash `A` and every feasible `P` (the optimum is a minimum over finitely many
profiles); no division by the optimum. The player set is any finite nonempty type `ι` (the paper's
`N = {1, …, n}`, `n ≥ 1`); `MAX` needs a player. -/
theorem theorem7_max_le_five_halves {ι E : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    [Fintype E] [DecidableEq E] (G : CongestionGame ι E) (A P : ι → Finset E)
    (hlin : IsLinear G) (hsym : IsSymmetric G) (hA : IsPureNash G A) (hP : IsProfile G P) :
    maxCost G A ≤ 5 / 2 * maxCost G P := by sorry

end CongestionPoA.SymMax
