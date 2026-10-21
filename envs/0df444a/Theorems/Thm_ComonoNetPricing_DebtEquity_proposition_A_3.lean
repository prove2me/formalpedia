-- Prove2me | Theorems.Thm_ComonoNetPricing_DebtEquity_proposition_A_3
-- name    : ComonoNetPricing.DebtEquity.proposition_A_3
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-19T04:15:40.997625+00:00
-- url     : https://prove2.me/theorems/84365c11-7173-4ebe-81b5-a3ebdc545929
-- title:
--   Proposition A.3, p. 34 — the greatest fixed point of Ψ is the greatest real fixed point of Ψ*, hence the clearing wealth V(x)
-- statement:
--   For a positive integer $n$, consider the Rogers–Veraart network under the standing assumptions, including Assumption 2.1 ($\sum_j\pi_{ij}<1$ and $\bar p_i>0$), and endowments $x \in \mathbb R^n_+$. Let $V^\uparrow$ be the greatest fixed point of the clearing map $\Psi$ of (6). Then
--
--   1. $V^\uparrow = \Psi^*(V^\uparrow)$, where $\Psi^*$ is the clearing process (1);
--   2. $V^\uparrow$ is the greatest real-valued fixed point of $\Psi^*$;
--   3. consequently $V^\uparrow = V(x)$, the greatest clearing wealth of Definition 2.2:
--   $$V(x) = \sup\{V \in \mathbb R^n \mid V = \Psi^*(V)\} = V^\uparrow.$$
--
--   The two clearing maps differ only below $-\bar p$, so this identifies the paper's clearing wealth with the solution produced by the lattice argument of Proposition A.1.
--
--   **Formalization Note** Item 3 is the immediate consequence of item 2 for the `sSup` definition of $V(x)$, stated so that later results may use it directly.
-- source:
--   Banerjee & Feinstein, Pricing of debt and equity in a financial network with comonotonic endowments, arXiv:1810.01372v5, p. 34, Proposition A.3

import Mathlib
import Definitions.Def_ComonoNetPricing_DebtEquity_Network

namespace ComonoNetPricing.DebtEquity

open Matrix

/-- Proposition A.3, p. 34: if `W` is the greatest fixed point of the clearing map `Ψ` of (6)
(endowments `x ≥ 0`, standing assumptions including Assumption 2.1), then `W = Ψ*(W)` and `W`
is the greatest real-valued fixed point of `Ψ*` of (1); in particular `W` is the greatest
clearing wealth `V(x)` of Definition 2.2. -/
theorem proposition_A_3 {n : ℕ} (hn : 0 < n) (N : Network n) (hN : N.Standing) (x : Fin n → ℝ) (hx : 0 ≤ x)
    (W : Fin n → ℝ) (hW : IsGreatest (Function.fixedPoints (N.Psi x)) W) :
    N.PsiStar x W = W ∧ IsGreatest (Function.fixedPoints (N.PsiStar x)) W ∧
      N.clearingWealth x = W := by sorry

end ComonoNetPricing.DebtEquity
