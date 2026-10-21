-- Prove2me | Theorems.Thm_BIInsurance_Screening_lemma_1_ii
-- name    : BIInsurance.Screening.lemma_1_ii
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T12:44:45.700727+00:00
-- url     : https://prove2.me/theorems/7465248e-853d-491a-a05f-eb52cde35156
-- title:
--   Lemma 1(ii), p. 18 — under the K-condition and (5.5), R(s_H, s_L) is quasi-concave in s_H; its slope at s_H = 0 is ≥ 0, and > 0 if (5.5) is strict
-- statement:
--   Assume the standing assumptions, $K>\mu_H+\delta_H+\gamma\ln\frac{(T-\tau)p-c}{c}$, and condition (5.5):
--
--   $$
--   (1-\alpha)(1+\lambda)\gamma E_\delta[\xi(K,\mu_L,\delta)-\xi(K,\mu_H,\delta)]+\alpha\lambda\Big(K+\gamma\ln\Big[\frac{(T-\tau)p}{(T-\tau)p-c}\Big]-\gamma E_\delta[\xi(K,\mu_H,\delta)]\Big)\ \ge 0 .
--   $$
--
--   Let $R(s_H,s_L)$ be the objective of (5.1) at $y_H=g_H(s_H)$, $y_L=g_L(s_H,s_L)$. Then for every $s_L\in[0,\bar s]$:
--   1. $s_H\mapsto R(s_H,s_L)$ is quasi-concave on $[0,\bar s]$;
--   2. it is differentiable at $s_H=0$ with non-negative derivative there;
--   3. if (5.5) holds strictly, this derivative is positive.
--
--   Together with Lemma 1(i), this makes both cross sections of $R$ unimodal, which is the basis of Proposition 3.
--
--   **Formalization Note** The page concludes "the marginal profit at $s_H=0$ is positive" from (5.5) with "$\ge$". By (B.1), p. 34, that marginal profit equals $p\rho(T-\tau-w)$ times the left side of (5.5), so a non-strict (5.5) gives only a non-negative slope. The statement records the non-negative slope under (5.5) and the positive slope under strict (5.5).
-- source:
--   Kao, Keskin & Shang, Impact of information asymmetry and limited production capacity on business interruption insurance, SSRN 3184530 (version of May 13, 2020), p. 18, Lemma 1(ii), eq. (5.5); proof pp. 34–35, (B.1)

import Mathlib
import Definitions.Def_BIInsurance_Screening_Model

namespace BIInsurance.Screening

theorem lemma_1_ii (P : Params) (hS : P.Standing) (hK : KCond P) (h55 : Cond55 P)
    (sL : ℝ) (hsL : sL ∈ Set.Icc 0 P.sbar) :
    QuasiconcaveOn ℝ (Set.Icc 0 P.sbar) (fun sH => R P sH sL) ∧
      DifferentiableAt ℝ (fun sH => R P sH sL) 0 ∧
      0 ≤ deriv (fun sH => R P sH sL) 0 ∧
      (0 < cond55LHS P → 0 < deriv (fun sH => R P sH sL) 0) := by sorry

end BIInsurance.Screening
