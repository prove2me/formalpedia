-- Prove2me | Theorems.Thm_ComonoNetPricing_DebtEquity_proposition_A_1
-- name    : ComonoNetPricing.DebtEquity.proposition_A_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-19T04:15:42.858429+00:00
-- url     : https://prove2.me/theorems/565e22cf-c7be-4f7e-b147-38a90b35dee7
-- title:
--   Proposition A.1, p. 34 — greatest and least clearing solutions of V = Ψ(V) exist and lie in [−p̄, x + Π⊤p̄ − p̄]
-- statement:
--   For a positive integer $n$, consider the Rogers–Veraart network under the standing assumptions ($\pi_{ij}\ge 0$, $\pi_{ii}=0$, $\sum_j\pi_{ij}<1$, $\bar p_i>0$, $\alpha_x,\alpha_L\in[0,1]$) and endowments $x \in \mathbb R^n_+$. Let $\Psi$ be the clearing map (6).
--
--   1. The set of clearing solutions $\{V \in \mathbb R^n \mid V = \Psi(V)\}$ has a greatest element and a least element.
--   2. Every clearing solution satisfies
--   $$-\bar p \le V \le x + \Pi^\top\bar p - \bar p.$$
--
--   This is the existence result for the clearing wealths; the greatest solution is the one the paper works with throughout.
--
--   **Formalization Note** "Finite" clearing solution is automatic for vectors in $\mathbb R^n$. The statement is made under the paper's standing assumptions, which include Assumption 2.1 (not needed for this particular claim).
-- source:
--   Banerjee & Feinstein, Pricing of debt and equity in a financial network with comonotonic endowments, arXiv:1810.01372v5, p. 34, Proposition A.1

import Mathlib
import Definitions.Def_ComonoNetPricing_DebtEquity_Network

namespace ComonoNetPricing.DebtEquity

open Matrix

/-- Proposition A.1, p. 34: under the standing assumptions and for endowments `x ≥ 0`, the
clearing map `Ψ` of (6) has a greatest and a least fixed point, and every fixed point lies in the
box `[−p̄, x + Π⊤ p̄ − p̄]`. -/
theorem proposition_A_1 {n : ℕ} (hn : 0 < n) (N : Network n) (hN : N.Standing) (x : Fin n → ℝ) (hx : 0 ≤ x) :
    (∃ V, IsGreatest (Function.fixedPoints (N.Psi x)) V) ∧
      (∃ V, IsLeast (Function.fixedPoints (N.Psi x)) V) ∧
      ∀ V ∈ Function.fixedPoints (N.Psi x),
        V ∈ Set.Icc (-N.pbar) (x + N.piMᵀ *ᵥ N.pbar - N.pbar) := by sorry

end ComonoNetPricing.DebtEquity
