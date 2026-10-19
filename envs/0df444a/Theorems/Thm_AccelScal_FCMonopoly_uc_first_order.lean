-- Prove2me | Theorems.Thm_AccelScal_FCMonopoly_uc_first_order
-- name    : AccelScal.FCMonopoly.uc_first_order
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-15T02:32:21.203963+00:00
-- url     : https://prove2.me/theorems/67e59326-a07d-4b83-8910-0401dbb252ac
-- title:
--   Appendix A.4, p. 20 — without accelerability and with Aβη > 1, every UC optimum satisfies u′(R)λ = 1
-- statement:
--   Let $(A,\beta,\eta,\gamma)$ satisfy the standing assumptions, let $r>0$, and suppose $\gamma=0$ (not accelerable), $\beta>0$ (scalable) and $A\beta\eta>1$. Let $R^*_{uc}$ be the set of maximizers of the UC value $V_{uc}(R)=\frac{u(R)\lambda(R)-R}{\lambda(R)+r}$ of (5) over $[1,\bar R]$.
--
--   Then every UC optimum $R\in R^*_{uc}$ satisfies the first-order condition
--   $$u'(R)\,\lambda(R)-1=0.$$
--
--   This is the UC side of the paper's first-order-condition comparison in Appendix A.4; it is the benchmark against which (A.25) is compared.
--
--   **Formalization Note.** The page states the condition at $R^*_{uc}$ without qualification; it fails at the corner $R=\underline R=1$ when $A\beta\eta<1$ (then $R^*_{uc}=\{1\}$ and $u'(1)\lambda-1=A\beta\eta-1$). The milestone therefore carries Corollary 1's disclosed hypothesis $A\beta\eta>1$, under which the sentence holds at every UC optimum as printed (no optimum sits at either end of $[1,\bar R]$). "$\lambda'=0$ and $u'>0$" is encoded as $\gamma=0$ and $\beta>0$. The UC value is the reduced problem (5), taken as the definition, as in the paper's proof.
-- source:
--   Lin, Accelerability vs. Scalability: R&D Investment Under Financial Constraints and Competition, Management Science, Articles in Advance (2022), doi:10.1287/mnsc.2022.4503, p. 20, Appendix A.4, after (A.25)

import Mathlib
import Definitions.Def_AccelScal_FCMonopoly_Setting

namespace AccelScal.FCMonopoly
theorem uc_first_order (T : Tech) (hT : T.Standing) (r : ℝ) (hr : 0 < r) (hγ : T.γ = 0)
    (hβ : 0 < T.β) (hint : 1 < T.A * T.β * T.η) :
    ∀ R ∈ RstarUC T r, deriv T.u R * T.lam R - 1 = 0 := by sorry
end AccelScal.FCMonopoly
