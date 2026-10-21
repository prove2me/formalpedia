-- Prove2me | Theorems.Thm_BIInsurance_Screening_foc_comparison
-- name    : BIInsurance.Screening.foc_comparison
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T12:45:09.375179+00:00
-- url     : https://prove2.me/theorems/02e60290-cd50-4a89-a202-a9a3b2a77685
-- title:
--   Proof of Proposition 4, p. 36 — at a root s′_L of (5.7), the left side of (5.6) is negative
-- statement:
--   Assume the standing assumptions, with $w_H=w_L=w$. Let $\Phi_H$ and $\Phi_L$ be the left sides of the first-order conditions (5.6) and (5.7). If $s\in[0,\bar s]$ satisfies $\Phi_L(s)=0$, then
--
--   $$
--   \Phi_H(s)=(1-\alpha)(1+\lambda)\gamma E_\delta[\xi(K,\mu_L,\delta)-\xi(K,\mu_H,\delta)]-\alpha\frac{(T-\tau-w)c\gamma s}{(B(s)p-c)B(s)}+\alpha\lambda\Big(K+\gamma\ln\Big[\frac{B(s)p}{B(s)p-c}\Big]-\gamma E_\delta[\xi(K,\mu_H,\delta)]\Big)<0,
--   $$
--
--   with $B(s)=(T-\tau)(1-s)+sw$. Thus the derivative of the insurer's reduced profit in $s_H$ is negative at $s_H=s'_L$, which, combined with quasi-concavity, places the high-demand coverage below the low-demand one.
-- source:
--   Kao, Keskin & Shang, Impact of information asymmetry and limited production capacity on business interruption insurance, SSRN 3184530 (version of May 13, 2020), p. 36, proof of Proposition 4

import Mathlib
import Definitions.Def_BIInsurance_Screening_Model

namespace BIInsurance.Screening

theorem foc_comparison (P : Params) (hS : P.Standing) (s : ℝ) (hs : s ∈ Set.Icc 0 P.sbar)
    (h57 : foc57 P s = 0) :
    foc56 P s < 0 := by sorry

end BIInsurance.Screening
