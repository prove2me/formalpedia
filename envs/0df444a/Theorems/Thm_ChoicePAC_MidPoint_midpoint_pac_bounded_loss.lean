-- Prove2me | Theorems.Thm_ChoicePAC_MidPoint_midpoint_pac_bounded_loss
-- name    : ChoicePAC.MidPoint.midpoint_pac_bounded_loss
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T10:30:37.039023+00:00
-- url     : https://prove2.me/theorems/848fe5cc-bae8-48da-bd01-aebd0f3b25ec
-- title:
--   Theorem 5.2 — mid-point PAC has revenue loss $O(1)$ against the DLP, uniformly in $k$
-- statement:
--   Consider a valid instance of network revenue management with customer choice satisfying Assumptions 2.1 and 2.2. Run mid-point PAC in the $k$-th system (capacities $kC$, rates $k\lambda$): it re-solves the DLP at $t_l = 1 - 2^{-l}$, $l = 1,\dots,M^k$, where $M^k$ is the smallest integer with $2^{-M^k} \le 1/k$. There is a constant $\rho > 0$, independent of $k$, such that for every $k \ge 1$ and every admissible DLP selector,
--   $$V^k_{\mathrm{DLP}} - \mathbb E[R^k_{\mathrm{PAC}}] \le \rho . \qquad (7)$$
--
--   With only $O(\log_2 k)$ re-solves, the expected revenue of PAC stays within a constant of the deterministic LP upper bound, and hence of the optimal policy.
--
--   **Formalization Note** $\rho$ is chosen after the instance and before $k$ and the selector (which fixes the DLP solution when there are ties after time 0). The statement is as printed: the printed proof (App. C.6) uses $v = 1/\xi_{\max}$ and $v = 1/\sqrt{k(1-t)}$, which satisfy Theorem 5.3's condition $v \le \min\{1, 1/\xi_{\max}\}$ only if $\xi_{\max} \ge 1$; no such hypothesis is added. The standing hypotheses (`IsValid`) are the disclosed reading of Sec. 2.1, p. 315, Sec. 2.3, p. 317 and Sec. 5.2, p. 327: printed are $\lambda_q \ge 0$, bounded nonnegative consumption and $r_j(0)=0$; read in are $C \ge 0$, consumption laws that are probability measures, $A_{ij} \le \xi_j$ almost surely (the page writes $\xi_j \ge A_{ij}$ on p. 317 and $A_{ij} < \xi_j$ on p. 327; the weaker $\le$ is used), measurable revenue functions, and revenue that is nonnegative and bounded by a common constant (implicit on the page, needed in App. C.4).
-- source:
--   Jasin, Kumar, A Re-Solving Heuristic with Bounded Revenue Loss for Network Revenue Management with Customer Choice, Math. Oper. Res. 37(2), 2012, Theorem 5.2, p. 327, eq. (7)

import Mathlib
import Definitions.Def_ChoicePAC_MidPoint_Model
import Definitions.Def_ChoicePAC_MidPoint_Assumptions

namespace ChoicePAC.MidPoint
theorem midpoint_pac_bounded_loss {NT n m : ℕ} (I : Instance NT n m) (hI : I.IsValid)
    (h21 : I.Assumption21) (h22 : I.Assumption22) :
    ∃ ρ : ℝ, 0 < ρ ∧
      ∀ k : ℕ, 1 ≤ k → ∀ sel, I.IsAdmissibleSelector sel →
        I.dlpValue ((k : ℝ) • I.C) ((k : ℝ) • I.lam) - I.pacValue sel k (midpointSchedule k) ≤ ρ := by sorry
end ChoicePAC.MidPoint
