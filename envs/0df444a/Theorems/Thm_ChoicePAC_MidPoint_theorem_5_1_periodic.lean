-- Prove2me | Theorems.Thm_ChoicePAC_MidPoint_theorem_5_1_periodic
-- name    : ChoicePAC.MidPoint.theorem_5_1_periodic
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T10:30:25.457776+00:00
-- url     : https://prove2.me/theorems/1d260680-7c2e-4860-af7f-b866fa858932
-- title:
--   Theorem 5.1 — periodic PAC: loss $\le \rho + \hat\rho\sqrt{kh}$
-- statement:
--   Consider a valid instance satisfying Assumptions 2.1 and 2.2, and periodic PAC with period $h > 0$, which re-solves at $t_l = lh$, $l = 1,\dots,M$, where $1 - h \le Mh < 1$. There are constants $\rho, \hat\rho > 0$, independent of $k$ (and of $h$), such that for every $k \ge 1$ and every admissible DLP selector,
--   $$V^k_{\mathrm{DLP}} - \mathbb E[R^k_{\mathrm{PAC}}] \le \rho + \hat\rho\sqrt{kh}.$$
--
--   Re-solving about $k$ times ($h \approx 1/k$) therefore keeps the loss bounded uniformly in $k$, which is (6).
--
--   **Formalization Note** This is the first inequality of (5). The strict middle inequality $\rho + \hat\rho\sqrt{kh} < \rho + \hat\rho\sqrt{k/M}$ holds for $M \ge 1$ by $Mh < 1$, and (6) with $\rho' = \rho + \hat\rho$ follows from it for the $h$ with $M = k$; neither is stated. (6) "choosing $M = k$" makes $h$ depend on $k$, so it only makes sense when $\rho, \hat\rho$ do not depend on $h$; the constants are chosen before $h$ accordingly (the proof's constants in App. C.5 do not depend on $h$). The standing hypotheses (`IsValid`) are the disclosed reading of Sec. 2.1, p. 315, Sec. 2.3, p. 317 and Sec. 5.2, p. 327: printed are $\lambda_q \ge 0$, bounded nonnegative consumption and $r_j(0)=0$; read in are $C \ge 0$, consumption laws that are probability measures, $A_{ij} \le \xi_j$ almost surely (the page writes $\xi_j \ge A_{ij}$ on p. 317 and $A_{ij} < \xi_j$ on p. 327; the weaker $\le$ is used), measurable revenue functions, and revenue that is nonnegative and bounded by a common constant (implicit on the page, needed in App. C.4).
-- source:
--   Jasin, Kumar, A Re-Solving Heuristic with Bounded Revenue Loss for Network Revenue Management with Customer Choice, Math. Oper. Res. 37(2), 2012, Theorem 5.1, p. 327, eq. (5)

import Mathlib
import Definitions.Def_ChoicePAC_MidPoint_Model
import Definitions.Def_ChoicePAC_MidPoint_Assumptions

namespace ChoicePAC.MidPoint
theorem theorem_5_1_periodic {NT n m : ℕ} (I : Instance NT n m) (hI : I.IsValid)
    (h21 : I.Assumption21) (h22 : I.Assumption22) :
    ∃ ρ ρhat : ℝ, 0 < ρ ∧ 0 < ρhat ∧
      ∀ h : ℝ, ∀ hh : 0 < h, ∀ k : ℕ, 1 ≤ k → ∀ sel, I.IsAdmissibleSelector sel →
        I.dlpValue ((k : ℝ) • I.C) ((k : ℝ) • I.lam) - I.pacValue sel k (periodicSchedule h hh) ≤
          ρ + ρhat * Real.sqrt (k * h) := by sorry
end ChoicePAC.MidPoint
