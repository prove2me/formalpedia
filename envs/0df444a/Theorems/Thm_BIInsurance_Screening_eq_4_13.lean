-- Prove2me | Theorems.Thm_BIInsurance_Screening_eq_4_13
-- name    : BIInsurance.Screening.eq_4_13
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T12:44:30.379962+00:00
-- url     : https://prove2.me/theorems/0ac3a930-ea9b-40aa-9941-2a0acaf6a614
-- title:
--   Eq. (4.13)–(4.14), p. 13 (Appendix A, p. 32) — e∗(s) is the unique maximizer of the insured disruption profit (4.11) on [0, 1]
-- statement:
--   Assume the standing assumptions of the model. Let $m\ge\mu_L+\delta_L$ be a demand location (in the paper $m=\mu_i+\delta_j$), $y\in\mathbb R$ a premium and $s\in[0,\bar s]$ a coverage percentage. Let $A(s)=wp+(T-\tau-w)p(1-s)$ and
--
--   $$
--   e^*(s)=\begin{cases}\dfrac1K\Big[m+\gamma\ln\dfrac{A(s)-c}{c}\Big] & \text{if } m+\gamma\ln\dfrac{A(s)-c}{c}<K,\\[1ex] 1&\text{otherwise.}\end{cases}
--   $$
--
--   Then
--   1. $0<e^*(s)\le1$;
--   2. $e^*(s)$ maximizes the insured profit under disruption $e\mapsto\pi^I_{1}(K,e,y,s)$ of (4.11)–(4.12) over $e\in[0,1]$;
--   3. it is the only maximizer on $[0,1]$;
--   4. at zero coverage it coincides with the uninsured optimal effort: $e^*(0)=\hat e$ of (4.7).
--
--   This identifies the recovery effort that the firm chooses under every contract and that the insurer anticipates in (5.1).
--
--   **Formalization Note** The page states the result for $m=\mu_i+\delta_j$, $i,j\in\{H,L\}$; here it is stated for every $m\ge\mu_L+\delta_L$, which contains all four. The positivity of $e^*$ is the role of the cap on $\bar s$ (p. 13).
-- source:
--   Kao, Keskin & Shang, Impact of information asymmetry and limited production capacity on business interruption insurance, SSRN 3184530 (version of May 13, 2020), p. 13, eqs. (4.13)–(4.14); p. 32, Appendix A; p. 14 (e∗(0) = ê)

import Mathlib
import Definitions.Def_BIInsurance_Screening_Model

namespace BIInsurance.Screening

theorem eq_4_13 (P : Params) (hS : P.Standing) (m y s : ℝ) (hm : P.muL + P.dL ≤ m)
    (hs : s ∈ Set.Icc 0 P.sbar) :
    0 < eStar P m s ∧ eStar P m s ≤ 1 ∧
      IsMaxOn (fun e => piI1e P m e y s) (Set.Icc 0 1) (eStar P m s) ∧
      (∀ e ∈ Set.Icc (0 : ℝ) 1, piI1e P m e y s = piI1e P m (eStar P m s) y s →
        e = eStar P m s) ∧
      eStar P m 0 = eHat P m := by sorry

end BIInsurance.Screening
