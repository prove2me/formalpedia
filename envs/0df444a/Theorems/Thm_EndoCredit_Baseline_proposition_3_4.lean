-- Prove2me | Theorems.Thm_EndoCredit_Baseline_proposition_3_4
-- name    : EndoCredit.Baseline.proposition_3_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T09:16:54.239717+00:00
-- url     : https://prove2.me/theorems/543c89bc-fa0d-4271-996f-048f2781b6b7
-- title:
--   Proposition 3.4, p. 12 — the credit limit decreases linearly to zero as δ rises
-- statement:
--   Fix all baseline parameters except the default-consumption fraction $\delta$. On the interval $0\le\delta\le\bar\delta$, the credit-limit ratio is affine and strictly decreasing, with
--
--   $$m^*(\delta)=\frac{1-\delta/\bar\delta}{r_I},\qquad m^*(\bar\delta)=0.$$
--
--   This identifies how the participation value changes the borrowing limit, including the zero-borrowing endpoint.
--
--   **Formalization Note** Proposition 3.4 includes $\delta=0$, although §2 otherwise assumes $\delta>0$. This item uses only $m^*$, for which that endpoint is defined; it does not evaluate $\delta^{1-\gamma}$ there.
-- source:
--   Choi, Koo, Lim & Yoo, Endogenous Credit, Business Cycle, and Portfolio Selection, SSRN 2560607, https://ssrn.com/abstract=2560607 (version of October 25, 2023), p. 12, Proposition 3.4(a)–(b)

import Mathlib
import Definitions.Def_EndoCredit_Baseline_Model

namespace EndoCredit.Baseline

/-- Proposition 3.4: the credit-limit coefficient is affine and strictly decreasing in δ,
and vanishes at the upper reservation-utility bound. -/
theorem proposition_3_4 (p : Params) (hp : p.Core) :
    (∀ d ∈ Set.Icc (0 : ℝ) (deltaBar p),
      mStar {p with delta := d} = (1 - d / deltaBar p) / rI p) ∧
    StrictAntiOn (fun d : ℝ => mStar {p with delta := d})
      (Set.Icc 0 (deltaBar p)) ∧
    mStar {p with delta := deltaBar p} = 0 := by sorry

end EndoCredit.Baseline
