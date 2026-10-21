-- Prove2me | Theorems.Thm_EndoCredit_Baseline_binding_equivalences
-- name    : EndoCredit.Baseline.binding_equivalences
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T09:17:02.00858+00:00
-- url     : https://prove2.me/theorems/d0e7609f-9972-4743-9a4e-a8dbcfd5a7c1
-- title:
--   §3.2, p. 10 — deterministic part of the binding equivalences
-- statement:
--   Put $\bar y=Q^{-\gamma}$ and let $w$ be the income-adjusted dual level $y_t^*/(1+D_t^*)$. On $0<w\le\bar y$, the consumption-to-income ratio $w^{-1/\gamma}$ reaches its minimum $Q$ exactly when $w=\bar y$. The wealth-to-income map $\phi$ is strictly decreasing on this interval and reaches $-m^*$ exactly at the same level:
--
--   $$w^{-1/\gamma}=Q\quad\Longleftrightarrow\quad w=\bar y\quad\Longleftrightarrow\quad\phi(w)=-m^*.$$
--
--   The map also satisfies $\phi(\bar y)=-m^*$, $w^{-1/\gamma}\ge Q$, and $\phi(w)\ge-m^*$ throughout this interval. These are the algebraic relations behind statements (ii)–(iv) of §3.2's four binding conditions.
--
--   **Formalization Note** Statement (i), binding of the conditional participation constraint, needs the stochastic verification theorem and is not asserted here. The paper refers the explicit $\bar y$ to its unavailable Online Appendix; $Q^{-\gamma}$ follows from the printed running-maximum formula in Proposition 3.1.
-- source:
--   Choi, Koo, Lim & Yoo, Endogenous Credit, Business Cycle, and Portfolio Selection, SSRN 2560607, https://ssrn.com/abstract=2560607 (version of October 25, 2023), p. 10, §3.2, 'the following four statements are equivalent'

import Mathlib
import Definitions.Def_EndoCredit_Baseline_Model

namespace EndoCredit.Baseline

/-- The deterministic content of the binding equivalences in §3.2. -/
theorem binding_equivalences (p : Params) (hp : p.Standing) :
    StrictAntiOn (phi p) (Set.Ioc 0 (ybar p)) ∧
    phi p (ybar p) = -(mStar p) ∧
    ∀ w ∈ Set.Ioc (0 : ℝ) (ybar p),
      Q p ≤ w ^ (-(1 / p.gam)) ∧
      (w ^ (-(1 / p.gam)) = Q p ↔ w = ybar p) ∧
      -(mStar p) ≤ phi p w ∧
      (phi p w = -(mStar p) ↔ w = ybar p) := by sorry

end EndoCredit.Baseline
