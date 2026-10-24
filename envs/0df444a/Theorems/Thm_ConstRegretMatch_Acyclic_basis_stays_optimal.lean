-- Prove2me | Theorems.Thm_ConstRegretMatch_Acyclic_basis_stays_optimal
-- name    : ConstRegretMatch.Acyclic.basis_stays_optimal
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-15T04:36:37.987725+00:00
-- url     : https://prove2.me/theorems/b4c6c495-1984-40fa-9dee-603a1b2ef9e0
-- title:
--   §4.2, p. 20 — under GP the same basis stays optimal for every λ̃ > 0 with ‖λ̃ − λ‖∞ ≤ ζ₀, for small ζ₀ > 0
-- statement:
--   Let $(M, \lambda, r)$ be a matching network satisfying the general position condition, with unique non-degenerate optimal solution $(z^*, s^*)$ of (SPP), active matches $\mathcal M_+$ and under-demanded queues $\mathcal Q_+$.
--
--   Then there is $\zeta_0 > 0$ such that for every right-hand side $\tilde\lambda$ with
--   $$\tilde\lambda > 0 \qquad\text{and}\qquad \|\tilde\lambda - \lambda\|_\infty \le \zeta_0$$
--   the same basis remains optimal: for suitable basic values $w$, the solution $(\tilde z, \tilde s)$ with $\tilde z_m = w_m$ for $m \in \mathcal M_+$, $\tilde s_j = w_j$ for $j \in \mathcal Q_+$ and all other entries $0$ is an optimal solution of the static-planning problem with right-hand side $\tilde\lambda$:
--   $$\max\ r\cdot z \quad\text{s.t.}\quad Mz + s = \tilde\lambda,\quad z \ge 0,\ s \ge 0.$$
--
--   This is the standard sensitivity property of a non-degenerate optimal basis, applied to (SPP).
--
--   **Formalization Note** "For all sufficiently small $\zeta_0 > 0$" is stated as the existence of one $\zeta_0 > 0$, which is equivalent because the conclusion only gets weaker as $\zeta_0$ decreases. $\tilde\lambda$ need not sum to one.
-- source:
--   Kerimov, Ashlagi, Gurvich, Dynamic Matching: Characterizing and Achieving Constant Regret, SSRN 3824407 (Sep 14, 2022), p. 20, §4.2 (paragraph after display (4))

import Mathlib
import Definitions.Def_ConstRegretMatch_Acyclic_Network
import Definitions.Def_ConstRegretMatch_Acyclic_SPP

namespace ConstRegretMatch.Acyclic

/-- §4.2, p. 20: under GP the optimal basis stays optimal for every positive right-hand side close
to `λ`: there is `ζ₀ > 0` such that for every `λ̃ > 0` with `‖λ̃ - λ‖_∞ ≤ ζ₀` the solution of
(SPP) with right-hand side `λ̃` supported on the basic variables `ℳ₊ ∪ 𝒬₊` of `(z*, s*)`
(for suitable basic values `w`) is optimal. -/
theorem basis_stays_optimal {n d : ℕ} (N : MatchingNetwork n d) (r : Fin d → ℝ)
    (hr : ConstRegretMatch.Upper.IsMatchValues r) (lam : Fin n → ℝ) (hlam : ConstRegretMatch.Upper.IsArrivalRates lam)
    (z : Fin d → ℝ) (s : Fin n → ℝ) (hGP : IsGP N r lam z s) :
    ∃ ζ₀ : ℝ, 0 < ζ₀ ∧
      ∀ lamt : Fin n → ℝ, (∀ i, 0 < lamt i) → (∀ i, |lamt i - lam i| ≤ ζ₀) →
        ∃ w : ConstRegretMatch.Upper.BasisIdx z s → ℝ, SPPOptimal N r lamt (basisSolZ w) (basisSolS w) := by sorry

end ConstRegretMatch.Acyclic
