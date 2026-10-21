-- Prove2me | Theorems.Thm_BIInsurance_Screening_lemma_1_i
-- name    : BIInsurance.Screening.lemma_1_i
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T12:44:50.353065+00:00
-- url     : https://prove2.me/theorems/f033768e-5c58-4365-91ea-8c65261e613b
-- title:
--   Lemma 1(i), p. 18 — if K > µ_L + δ_H + γ ln(((T−τ)p−c)/c), R(s_H, s_L) is quasi-concave in s_L with positive slope at s_L = 0
-- statement:
--   Assume the standing assumptions and
--
--   $$
--   K>\mu_L+\delta_H+\gamma\ln\frac{(T-\tau)p-c}{c}.
--   $$
--
--   Let $R(s_H,s_L)$ be the insurer's objective of (5.1) with the premiums $y_H=g_H(s_H)$, $y_L=g_L(s_H,s_L)$ of (5.3)–(5.4). Then for every $s_H\in[0,\bar s]$:
--   1. $s_L\mapsto R(s_H,s_L)$ is quasi-concave on $[0,\bar s]$;
--   2. the marginal profit at $s_L=0$ is positive: $\frac{\partial}{\partial s_L}R(s_H,s_L)\big|_{s_L=0}>0$.
--
--   So offering the low-demand firm some coverage is always profitable, and the optimal $s_L$ is characterized by a first-order condition or the cap $\bar s$.
-- source:
--   Kao, Keskin & Shang, Impact of information asymmetry and limited production capacity on business interruption insurance, SSRN 3184530 (version of May 13, 2020), p. 18, Lemma 1(i); proof pp. 34–35

import Mathlib
import Definitions.Def_BIInsurance_Screening_Model

namespace BIInsurance.Screening

theorem lemma_1_i (P : Params) (hS : P.Standing)
    (hK : P.muL + P.dH + P.γ * Real.log ((((P.T : ℝ) - P.τ) * P.p - P.c) / P.c) < P.K)
    (sH : ℝ) (hsH : sH ∈ Set.Icc 0 P.sbar) :
    QuasiconcaveOn ℝ (Set.Icc 0 P.sbar) (fun sL => R P sH sL) ∧
      0 < deriv (fun sL => R P sH sL) 0 := by sorry

end BIInsurance.Screening
