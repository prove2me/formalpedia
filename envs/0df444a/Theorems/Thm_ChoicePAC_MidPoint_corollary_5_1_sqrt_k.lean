-- Prove2me | Theorems.Thm_ChoicePAC_MidPoint_corollary_5_1_sqrt_k
-- name    : ChoicePAC.MidPoint.corollary_5_1_sqrt_k
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T10:30:43.031982+00:00
-- url     : https://prove2.me/theorems/b9752a83-e3a2-477a-9770-7b5d7f66a98e
-- title:
--   Corollary 5.1 — any re-solving schedule: loss $\le \rho + \hat\rho\sqrt k$
-- statement:
--   Consider a valid instance satisfying Assumptions 2.1 and 2.2. There are constants $\rho, \hat\rho > 0$, independent of $k$, such that for every $k \ge 1$, every choice of re-solving times $\Gamma^k = \{t^k_l : l = 1,\dots,M^k\}$ and every admissible DLP selector,
--   $$V^k_{\mathrm{DLP}} - \mathbb E[R^k_{\mathrm{PAC}}(0,1)] \le \rho + \hat\rho\sqrt{k}. \qquad (9)$$
--
--   So re-solving, however it is scheduled, never worsens PAC's loss beyond the $O(\sqrt k)$ bound of the static policy.
--
--   **Formalization Note** The constants are chosen before $k$, the schedule and the selector. The standing hypotheses (`IsValid`) are the disclosed reading of Sec. 2.1, p. 315, Sec. 2.3, p. 317 and Sec. 5.2, p. 327: printed are $\lambda_q \ge 0$, bounded nonnegative consumption and $r_j(0)=0$; read in are $C \ge 0$, consumption laws that are probability measures, $A_{ij} \le \xi_j$ almost surely (the page writes $\xi_j \ge A_{ij}$ on p. 317 and $A_{ij} < \xi_j$ on p. 327; the weaker $\le$ is used), measurable revenue functions, and revenue that is nonnegative and bounded by a common constant (implicit on the page, needed in App. C.4).
-- source:
--   Jasin, Kumar, A Re-Solving Heuristic with Bounded Revenue Loss for Network Revenue Management with Customer Choice, Math. Oper. Res. 37(2), 2012, Corollary 5.1, p. 328, eq. (9)

import Mathlib
import Definitions.Def_ChoicePAC_MidPoint_Model
import Definitions.Def_ChoicePAC_MidPoint_Assumptions

namespace ChoicePAC.MidPoint
theorem corollary_5_1_sqrt_k {NT n m : ℕ} (I : Instance NT n m) (hI : I.IsValid)
    (h21 : I.Assumption21) (h22 : I.Assumption22) :
    ∃ ρ ρhat : ℝ, 0 < ρ ∧ 0 < ρhat ∧
      ∀ k : ℕ, 1 ≤ k → ∀ s : Schedule, ∀ sel, I.IsAdmissibleSelector sel →
        I.dlpValue ((k : ℝ) • I.C) ((k : ℝ) • I.lam) - I.pacValue sel k s ≤
          ρ + ρhat * Real.sqrt k := by sorry
end ChoicePAC.MidPoint
