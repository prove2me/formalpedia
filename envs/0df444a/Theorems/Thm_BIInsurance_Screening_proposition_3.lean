-- Prove2me | Theorems.Thm_BIInsurance_Screening_proposition_3
-- name    : BIInsurance.Screening.proposition_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T12:45:25.093321+00:00
-- url     : https://prove2.me/theorems/bf5b4a88-120d-4efa-8c9b-13b29ef24215
-- title:
--   Proposition 3, p. 19 — the optimal coverages satisfy the first-order conditions (5.6)–(5.7), with boundary cases
-- statement:
--   Assume the standing assumptions, $K>\mu_H+\delta_H+\gamma\ln\frac{(T-\tau)p-c}{c}$ and (5.5). Write $B(s)=(T-\tau)(1-s)+sw$ and let $\Phi_H(s)$, $\Phi_L(s)$ be the left sides of the first-order conditions
--
--   $$
--   \Phi_H(s)=(1-\alpha)(1+\lambda)\gamma E_\delta[\xi(K,\mu_L,\delta)-\xi(K,\mu_H,\delta)]-\alpha\frac{(T-\tau-w)c\gamma s}{(B(s)p-c)B(s)}+\alpha\lambda\Big(K+\gamma\ln\Big[\frac{B(s)p}{B(s)p-c}\Big]-\gamma E_\delta[\xi(K,\mu_H,\delta)]\Big),
--   $$
--   $$
--   \Phi_L(s)=\lambda\Big(K+\gamma\ln\Big[\frac{B(s)p}{B(s)p-c}\Big]-\gamma E_\delta[\xi(K,\mu_L,\delta)]\Big)-\frac{(T-\tau-w)c\gamma s}{(B(s)p-c)B(s)}
--   $$
--
--   ((5.6) and (5.7) with $w_H=w_L=w$). There exist selected coverages $s^\circ_H,s^\circ_L$: $s^\circ_H$ is a positive root of $\Phi_H$ in $(0,\bar s]$ if one exists. When (5.5) holds with equality and $\lambda\leq1$, the zero root instead gives $s^\circ_H=0$. In the remaining case with no positive root, take $s^\circ_H=\bar s$. Likewise, $s^\circ_L$ is a root of $\Phi_L$ in $(0,\bar s]$, or $\bar s$ if $\Phi_L$ has no root in $[0,\bar s]$. The maximizers of the reduced objective $R(s_H,s_L)$ over $[0,\bar s]^2$ are exactly the single point
--
--   $$
--   (s^*_H,s^*_L)=(s^\circ_H,s^\circ_L),
--   $$
--
--   with the selected roots and cap cases corresponding to the first-order conditions (5.6) and (5.7).
--
--   The optimal coverages are therefore pinned down by the first-order conditions, or by the cap when coverage is never too costly.
--
--   **Formalization Note** The page's minimum formula needs a boundary case when (5.5) holds with equality: $s=0$ solves (5.6). For $\lambda\leq1$ it is the maximizing coverage; for $\lambda>1$ it can be a nonmaximizing stationary point, so the positive root or the cap is selected. The Lean statement asserts existence of the selected coverages and describes the cases explicitly. Roots beyond $\bar s$ are not used, since beyond the cap the first-order formulas need not describe $R$.
-- source:
--   Kao, Keskin & Shang, Impact of information asymmetry and limited production capacity on business interruption insurance, SSRN 3184530 (version of May 13, 2020), p. 19, Proposition 3, eqs. (5.6)–(5.7); proof pp. 34–35

import Mathlib
import Definitions.Def_BIInsurance_Screening_Model

namespace BIInsurance.Screening

theorem proposition_3 (P : Params) (hS : P.Standing) (hK : KCond P) (h55 : Cond55 P)
    : ∃ sH' sL' : ℝ,
      ((0 < sH' ∧ sH' ≤ P.sbar ∧ foc56 P sH' = 0) ∨
        (sH' = 0 ∧ foc56 P 0 = 0 ∧ P.lam ≤ 1) ∨
        (sH' = P.sbar ∧ (0 < cond55LHS P ∨ 1 < P.lam) ∧
          ∀ s ∈ Set.Ioc 0 P.sbar, foc56 P s ≠ 0)) ∧
      ((0 < sL' ∧ sL' ≤ P.sbar ∧ foc57 P sL' = 0) ∨
        (sL' = P.sbar ∧ ∀ s ∈ Set.Icc 0 P.sbar, foc57 P s ≠ 0)) ∧
      ∀ sH sL : ℝ,
        (sH ∈ Set.Icc 0 P.sbar ∧ sL ∈ Set.Icc 0 P.sbar ∧
          ∀ a ∈ Set.Icc 0 P.sbar, ∀ b ∈ Set.Icc 0 P.sbar, R P a b ≤ R P sH sL) ↔
        (sH = sH' ∧ sL = sL') := by sorry

end BIInsurance.Screening
