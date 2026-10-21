-- Prove2me | Theorems.Thm_BIInsurance_Screening_proposition_2
-- name    : BIInsurance.Screening.proposition_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T12:44:35.379894+00:00
-- url     : https://prove2.me/theorems/e83b90f3-8c2b-4185-9ecc-acbd5343af13
-- title:
--   Proposition 2, p. 15 — reverse single crossing: the marginal profit in coverage s is non-increasing in the early forecast µ
-- statement:
--   Assume the standing assumptions, let $y\in\mathbb R$ and $s\in[0,\bar s]$. Then:
--   1. for every early forecast $\mu\ge\mu_L$, the expected profit with insurance $s'\mapsto E_{\delta,Z}[\pi^I(K,y,s')]$ (for early forecast $\mu$) is differentiable at $s$;
--   2. the marginal profit in coverage is non-increasing in the early forecast:
--
--   $$
--   \mu\longmapsto\frac{d}{ds}E_{\delta,Z}\big[\pi^I(K,y,s)\big]\ \text{ is non-increasing on }[\mu_L,\infty),\qquad\text{i.e. }\ \frac{d^2}{ds\,d\mu}E_{\delta,Z}[\pi^I(K,y,s)]\le0 .
--   $$
--
--   The low-demand firm benefits more from coverage than the high-demand firm: this "reverse" single-crossing property is why, in the insurer's problem, the low type's incentive constraint and the high type's participation constraint bind.
--
--   **Formalization Note** The page treats $\mu_i$ as a real variable when it differentiates in it; the statement takes $\mu$ ranging over $[\mu_L,\infty)$ and states the monotonicity of the $s$-derivative directly, with differentiability made explicit so that `deriv` is the true derivative.
-- source:
--   Kao, Keskin & Shang, Impact of information asymmetry and limited production capacity on business interruption insurance, SSRN 3184530 (version of May 13, 2020), p. 15, Proposition 2; proof pp. 33–34

import Mathlib
import Definitions.Def_BIInsurance_Screening_Model

namespace BIInsurance.Screening

theorem proposition_2 (P : Params) (hS : P.Standing) (y s : ℝ) (hs : s ∈ Set.Icc 0 P.sbar) :
    (∀ mu ∈ Set.Ici P.muL, DifferentiableAt ℝ (fun s' => EpiI P mu y s') s) ∧
      AntitoneOn (fun mu => deriv (fun s' => EpiI P mu y s') s) (Set.Ici P.muL) := by sorry

end BIInsurance.Screening
