-- Prove2me | Theorems.Thm_AccelScal_FCMonopoly_fc_first_order
-- name    : AccelScal.FCMonopoly.fc_first_order
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T02:32:17.151155+00:00
-- url     : https://prove2.me/theorems/198524aa-e90c-46bf-96c3-e85c135b8669
-- title:
--   Appendix A.4, (A.25), p. 20 — without accelerability, an interior FC optimum has u′(R)λ − 1 > 0
-- statement:
--   Let $(A,\beta,\eta,\gamma)$ satisfy the standing assumptions, let $r>0$, $\mu\in\mathbb R$, $\sigma>0$, $X\in\mathbb R$, and suppose the project is **not accelerable but scalable**: $\gamma=0$ (so $\lambda'\equiv0$) and $\beta>0$ (so $u'>0$). Let $R^*_{fc}$ be the set of maximizers of the FC value $V_{fc}$ of (6) over $[1,\min\{\bar R,X\}]$.
--
--   Then every interior FC optimum, i.e. every $R\in R^*_{fc}$ with $1<R<\min\{\bar R,X\}$, satisfies
--   $$u'(R)\,\lambda(R)-1>0.$$
--
--   This is the consequence the paper draws from the FC first-order condition (A.25): the survival factor $1-(X/R)^\alpha$ decreases in $R$, so at an interior optimum the marginal perpetuity value must be strictly positive. Combined with the UC first-order condition $u'\lambda=1$ and the concavity of $f(R)=u(R)\lambda-R$, it places every FC optimum below the UC optimum.
--
--   **Formalization Note.** The FC value is the reduced problem (6), taken as the definition (its derivation from (3), Lemma 1, is not posed). "$\lambda'=0$ and $u'>0$" is encoded as $\gamma=0$ and $\beta>0$, which under (2) and $R\ge1$ are equivalent. The paper writes the exponent in this passage as $\alpha_1$; it is Lemma 1's $\alpha$. $u'(R)$ is Mathlib's `deriv` of $u$ at $R$.
-- source:
--   Lin, Accelerability vs. Scalability: R&D Investment Under Financial Constraints and Competition, Management Science, Articles in Advance (2022), doi:10.1287/mnsc.2022.4503, p. 20, Appendix A.4, (A.25)

import Mathlib
import Definitions.Def_AccelScal_FCMonopoly_Setting

namespace AccelScal.FCMonopoly
theorem fc_first_order (T : Tech) (hT : T.Standing) (r : ℝ) (hr : 0 < r) (μ σ X : ℝ)
    (hσ : 0 < σ) (hγ : T.γ = 0) (hβ : 0 < T.β) :
    ∀ R ∈ RstarFC T r μ σ X, 1 < R → R < min T.Rbar X → 0 < deriv T.u R * T.lam R - 1 := by sorry
end AccelScal.FCMonopoly
