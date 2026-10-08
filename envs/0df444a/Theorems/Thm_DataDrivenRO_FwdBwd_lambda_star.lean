-- Prove2me | Theorems.Thm_DataDrivenRO_FwdBwd_lambda_star
-- name    : DataDrivenRO.FwdBwd.lambda_star
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-05T14:02:37.649027+00:00
-- url     : https://prove2.me/theorems/8c1c115f-d6bf-4179-93a5-82a87e406039
-- title:
--   Proof of Theorem 6, p. ec5 — inf_{λ>0} λL + S/(2λ) = √(2LS), attained at λ* = √(S/(2L))
-- statement:
--   Let $L>0$ and $S\ge0$ be real numbers. Then
--   $$\inf_{\lambda>0}\Big\{\lambda L + \frac{S}{2\lambda}\Big\} = \sqrt{2LS},$$
--   and when $S>0$ the infimum is attained at $\lambda^* = \sqrt{S/(2L)}>0$.
--
--   With $L=\log(1/\varepsilon)$ and $S=\sum_{i:v_i>0}v_i^2\bar\sigma_{fi}^2+\sum_{i:v_i\le0}v_i^2\bar\sigma_{bi}^2$ this is the closed-form solution of the last step of the proof of Theorem 6, and it yields the square-root term of (24).
--
--   **Formalization Note** When $S=0$ the infimum $0$ is not attained by any $\lambda>0$; the page's "min" is an infimum there, which `IsGLB` covers.
-- source:
--   Bertsimas, Gupta & Kallus, Data-Driven Robust Optimization, arXiv:1401.0212v2, EC.1.4, proof of Theorem 6, λ* display, p. ec5

import Mathlib
import Definitions.Def_DataDrivenRO_FwdBwd_Setting

namespace DataDrivenRO.FwdBwd

theorem lambda_star (L S : ℝ) (hL : 0 < L) (hS : 0 ≤ S) :
    IsGLB ((fun lam : ℝ => lam * L + S / (2 * lam)) '' Set.Ioi 0) (Real.sqrt (2 * L * S)) ∧
    (0 < S → 0 < Real.sqrt (S / (2 * L)) ∧
      Real.sqrt (S / (2 * L)) * L + S / (2 * Real.sqrt (S / (2 * L))) =
        Real.sqrt (2 * L * S)) := by sorry

end DataDrivenRO.FwdBwd
