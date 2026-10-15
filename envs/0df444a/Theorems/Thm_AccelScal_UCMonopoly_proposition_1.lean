-- Prove2me | Theorems.Thm_AccelScal_UCMonopoly_proposition_1
-- name    : AccelScal.UCMonopoly.proposition_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T06:47:45.017622+00:00
-- url     : https://prove2.me/theorems/d4dc728c-e791-4d57-b1c3-7ef4e17eb50b
-- title:
--   Proposition 1, p. 5 — comparative statics of the unconstrained monopoly's optimal R&D intensity
-- statement:
--   Let $T=(A,\beta,\eta,\gamma)$ satisfy the standing assumptions ($A,\eta>0$, $\beta,\gamma\in[0,1)$, $\beta+\gamma<1$, $A\eta>1$), let $r>0$, and let $R^*_{uc}(A,\beta,\eta,r)$ be the set of intensities in $[1,\bar R]$, $\bar R=(A\eta)^{1/(1-\beta-\gamma)}$, that maximize the unconstrained monopoly's R&D value
--   $$\Pi(R)=\mathbb E\Big[e^{-r\tau_d}u(R)-R\int_0^{\tau_d}e^{-rt}dt\Big],\qquad\tau_d\sim\mathrm{Exp}(\lambda(R)).$$
--   Say that a set $S'$ lies above a set $S$ if $x\le y$ for all $x\in S$, $y\in S'$, with $x<y$ whenever $x>1$. Then $R^*_{uc}$ is nonempty and:
--
--   1. If $u'=0$ and $\lambda'=0$ ($\beta=\gamma=0$), then $R^*_{uc}=\{\underline R\}=\{1\}$.
--   2. If $u'>0$ or $\lambda'>0$ ($\beta>0$ or $\gamma>0$), then for $A<A'$ the set $R^*_{uc}$ at $A'$ lies above the set at $A$.
--   3. If $u'>0$ ($\beta>0$), then for $\beta<\beta'$ with $\beta'+\gamma<1$ the set at $\beta'$ lies above the set at $\beta$.
--   4. If $\lambda'=0$ and $u'>0$ ($\gamma=0<\beta$), then for $\eta<\eta'$ the set at $\eta'$ lies above the set at $\eta$.
--   5. If $\lambda'=0$ ($\gamma=0$), $R^*_{uc}$ is the same for every discount rate $r'>0$. If $\lambda'>0$ ($\gamma>0$), then for $r<r'$ the set at $r'$ lies above the set at $r$.
--
--   The proposition says what drives an unconstrained firm's R&D intensity: the payoff scale always pushes it up when investment matters at all, scalability pushes it up, the speed factor pushes it up when discovery speed does not respond to investment, and a higher interest rate raises intensity exactly when the project is accelerable.
--
--   **Formalization Note** The paper writes (ii)–(v) as derivatives of an optimal intensity, $\partial R^*_{uc}/\partial s>0$. The optimum need not be unique or differentiable, and at the corner $R^*_{uc}=\underline R$ the strict sign fails (e.g. $\gamma=0,\beta=0.1,\eta=1,r=1$ and $A=2$ versus $2.2$: the optimum is $1$ in both). The claims are therefore posed as orderings of the optimal sets, strict at interior optima; "$\partial R^*_{uc}/\partial r=0$" is invariance of the set. Optima are taken over the range (7), which moves with the parameter. Nonemptiness is added so that no clause is vacuous. $u'=0\Leftrightarrow\beta=0$ and $\lambda'=0\Leftrightarrow\gamma=0$ for $R\ge1$ under (2). $A\eta>1$ (investment takes place) is part of the standing assumptions; the payoff $\tilde u$ is replaced by its mean and the cash-flow term of (4) is dropped.
-- source:
--   Lin, Accelerability vs. Scalability: R&D Investment Under Financial Constraints and Competition, Management Science, Articles in Advance (2022), doi:10.1287/mnsc.2022.4503, p. 5, Proposition 1

import Mathlib
import Definitions.Def_AccelScal_UCMonopoly_Setting

namespace AccelScal.UCMonopoly
theorem proposition_1 (T : Tech) (hT : T.Standing) (r : ℝ) (hr : 0 < r) :
    (RstarUC T r).Nonempty ∧
    (T.β = 0 → T.γ = 0 → RstarUC T r = {1}) ∧
    ((0 < T.β ∨ 0 < T.γ) → ∀ A' : ℝ, T.A < A' →
        OrderedAbove (RstarUC T r) (RstarUC { T with A := A' } r)) ∧
    (0 < T.β → ∀ β' : ℝ, T.β < β' → β' + T.γ < 1 →
        OrderedAbove (RstarUC T r) (RstarUC { T with β := β' } r)) ∧
    (T.γ = 0 → 0 < T.β → ∀ η' : ℝ, T.η < η' →
        OrderedAbove (RstarUC T r) (RstarUC { T with η := η' } r)) ∧
    (T.γ = 0 → ∀ r' : ℝ, 0 < r' → RstarUC T r' = RstarUC T r) ∧
    (0 < T.γ → ∀ r' : ℝ, r < r' → OrderedAbove (RstarUC T r) (RstarUC T r')) := by sorry
end AccelScal.UCMonopoly
