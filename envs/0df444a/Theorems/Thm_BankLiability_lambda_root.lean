-- Prove2me | Theorems.Thm_BankLiability_lambda_root
-- name    : BankLiability.lambda_root
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T19:49:21.395752+00:00
-- url     : https://prove2.me/theorems/935ce9fe-84f3-49bb-bdaa-f2159ba4c038
-- title:
--   $\lambda$ is the unique positive root of $\sigma^2\lambda(1+\lambda)/2-(r-\delta)\lambda-r=0$; $\lambda=2r/\sigma^2$ when $\delta=0$
-- statement:
--   Let $\sigma>0$, $\delta\ge0$, $r>0$, and let $\lambda$ be the exponent of the model. Then
--
--   1. $\lambda>0$;
--   2. $\lambda$ solves the quadratic equation
--   $$\frac{\sigma^2\lambda(1+\lambda)}{2}-(r-\delta)\lambda-r=0;$$
--   3. every positive solution $x>0$ of this equation equals $\lambda$;
--   4. if the asset cash flow is zero, $\delta=0$, then $\lambda=2r/\sigma^2$.
--
--   This justifies the paper's phrase "the positive solution": the exponent of every state price in the model is well defined, and in the cash-flow-free case it is proportional to $r$ and inversely proportional to $\sigma^2$.
--
--   Differences from the source:
--   - encoding: λ is "the positive solution" of the quadratic → λ is defined by the quadratic formula, and positivity, being a root, and uniqueness among positive roots are stated as clauses; reason: the same number, made explicit
-- source:
--   Sundaresan–Wang, Strategic Bank Liability Structure Under Capital Requirements, Management Science (2023), doi:10.1287/mnsc.2022.4570, Articles in Advance, §2.2, sentence after eq. (2), p.5

import Mathlib
import Definitions.Def_BankLiability_Params
import Definitions.Def_BankLiability_lam

namespace BankLiability

/-- **λ is the positive root of σ²λ(1 + λ)/2 − (r − δ)λ − r = 0, and λ = 2r/σ² when δ = 0.**
Sundaresan–Wang, *Strategic Bank Liability Structure Under Capital Requirements*, Management
Science (2023), doi:10.1287/mnsc.2022.4570, Articles in Advance, §2.2, sentence after (2), p.5:
"where λ is the positive solution to the quadratic equation σ²λ(1 + λ)/2 − (r − δ)λ − r = 0. If the
cash flow of the assets is zero, that is, δ = 0, we have λ = 2r/σ²".

The four clauses: `lam P` is positive; it solves the quadratic; it is the only positive solution
(so "the positive solution" is well defined); and for δ = 0 it equals `2r/σ²`.

**Formalization Note.** `lam P` is the explicit `+` root of the quadratic formula
(`Definitions.Def_BankLiability_lam`); the ranges σ > 0, r > 0, δ ≥ 0 come from `Params`
(Table 1, p.6). -/
theorem lambda_root (P : Params) :
    0 < lam P ∧
    P.sigma ^ 2 * lam P * (1 + lam P) / 2 - (P.r - P.delta) * lam P - P.r = 0 ∧
    (∀ x : ℝ, 0 < x →
      P.sigma ^ 2 * x * (1 + x) / 2 - (P.r - P.delta) * x - P.r = 0 → x = lam P) ∧
    (P.delta = 0 → lam P = 2 * P.r / P.sigma ^ 2) := by sorry

end BankLiability
