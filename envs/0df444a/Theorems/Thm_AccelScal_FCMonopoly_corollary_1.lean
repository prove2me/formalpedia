-- Prove2me | Theorems.Thm_AccelScal_FCMonopoly_corollary_1
-- name    : AccelScal.FCMonopoly.corollary_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-15T02:32:29.718629+00:00
-- url     : https://prove2.me/theorems/7697b906-a89d-4aa9-8e6d-e5d1727c6f6d
-- title:
--   Corollary 1 (first statement), p. 6 — if λ′ = 0 and u′ > 0, then R*_fc < R*_uc
-- statement:
--   Let the project technology $(A,\beta,\eta,\gamma)$ satisfy the standing assumptions, let $r>0$ be the discount rate, and let the FC firm's AIP cash flow have drift $\mu\in\mathbb R$, volatility $\sigma>0$ and level $X\ge1$ at the project's arrival. Suppose the project is **not accelerable** ($\gamma=0$, i.e. $\lambda'=0$) but **scalable** ($\beta>0$, i.e. $u'>0$), and that $A\beta\eta>1$.
--
--   Let $R^*_{uc}$ be the set of maximizers of $V_{uc}$ of (5) over $[1,\bar R]$ and $R^*_{fc}$ the set of maximizers of $V_{fc}$ of (6) over $[1,\min\{\bar R,X\}]$. Then both sets are nonempty, and every FC optimum lies strictly below every UC optimum:
--   $$x<y\qquad\text{for all } x\in R^*_{fc},\ y\in R^*_{uc}.$$
--
--   In words: when investment cannot speed up discovery, financial constraints lead to under-investment, $R^*_{fc}<R^*_{uc}$. This is the first statement of the paper's Corollary 1; its second statement (possible over-investment when $\lambda'>0$) rests on numerical exercises and is not posed.
--
--   **Formalization Note.** (i) The two firms' problems are the reduced values (5) and (6) of Lemma 1, taken as definitions; the derivation of (6) from the GBM model (3) is not posed. (ii) $A\beta\eta>1$ is a disclosed, necessary addition: it says the unconstrained optimum is interior; if $A\beta\eta\le1$ both optimal sets equal $\{1\}$ and the strict inequality fails. (iii) $X\ge1$ keeps the FC range $[1,\min\{\bar R,X\}]$ of (7) nonempty. (iv) The paper's single-valued $R^*$ is read as a set of maximizers; the inequality is claimed for every pair of optima and the sets are asserted nonempty, so no clause is vacuous. (v) No sign condition on $\mu$ is imposed.
-- source:
--   Lin, Accelerability vs. Scalability: R&D Investment Under Financial Constraints and Competition, Management Science, Articles in Advance (2022), doi:10.1287/mnsc.2022.4503, p. 6, Corollary 1 (first statement); proof Appendix A.4, p. 20

import Mathlib
import Definitions.Def_AccelScal_FCMonopoly_Setting

namespace AccelScal.FCMonopoly
theorem corollary_1 (T : Tech) (hT : T.Standing) (r : ℝ) (hr : 0 < r) (μ σ X : ℝ) (hσ : 0 < σ)
    (hX : 1 ≤ X) (hγ : T.γ = 0) (hβ : 0 < T.β) (hint : 1 < T.A * T.β * T.η) :
    (RstarUC T r).Nonempty ∧ (RstarFC T r μ σ X).Nonempty ∧
    ∀ x ∈ RstarFC T r μ σ X, ∀ y ∈ RstarUC T r, x < y := by sorry
end AccelScal.FCMonopoly
