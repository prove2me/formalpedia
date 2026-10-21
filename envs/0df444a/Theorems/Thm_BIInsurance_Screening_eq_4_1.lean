-- Prove2me | Theorems.Thm_BIInsurance_Screening_eq_4_1
-- name    : BIInsurance.Screening.eq_4_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T12:43:42.98062+00:00
-- url     : https://prove2.me/theorems/4452ee17-8939-48f8-bc9f-ffe710d97dd2
-- title:
--   Eq. (4.1)–(4.2), p. 11 — expected sales under logistic demand: E[min(D, x)] = x + m − γ ln[exp(x/γ) + exp(m/γ)]
-- statement:
--   Let $\gamma>0$, $m\in\mathbb R$ and $x\in\mathbb R$, and let $D$ be logistic with location $m$ and scale $\gamma$ (density $f_{m,\gamma}$). Then $t\mapsto\min(t,x)f_{m,\gamma}(t)$ is integrable and
--
--   $$
--   E[\min(D,x)]=x+m-\gamma\,\ln\!\Big[\exp\!\Big(\frac{x}{\gamma}\Big)+\exp\!\Big(\frac{m}{\gamma}\Big)\Big].
--   $$
--
--   With $m=\mu_i+\delta_j$ and $x=K$ this is eq. (4.1), $pE_{\epsilon_t}[\min(D_{ijt},K)]=p\{K+\mu_i+\delta_j-\gamma\xi(K,\mu_i,\delta_j)\}$ with $\xi$ from (4.2); with $x=eK$ it is (4.3). Every profit expression of the model reduces to this closed form, which is what turns the effort and coverage problems into explicit calculus.
-- source:
--   Kao, Keskin & Shang, Impact of information asymmetry and limited production capacity on business interruption insurance, SSRN 3184530 (version of May 13, 2020), p. 11, eqs. (4.1)–(4.3)

import Mathlib
import Definitions.Def_BIInsurance_Screening_Logistic

namespace BIInsurance.Screening

theorem eq_4_1 (γ m x : ℝ) (hγ : 0 < γ) :
    MeasureTheory.Integrable (fun t => min t x * logisticPDF γ m t) ∧
      expSales γ m x = x + m - γ * Real.log (Real.exp (x / γ) + Real.exp (m / γ)) := by sorry

end BIInsurance.Screening
