-- Prove2me | Theorems.Thm_ChoicePAC_MidPoint_theorem_5_3_general_bound
-- name    : ChoicePAC.MidPoint.theorem_5_3_general_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T10:30:54.830345+00:00
-- url     : https://prove2.me/theorems/decaba37-6499-4c3f-a8fe-2a2e2504b931
-- title:
--   Theorem 5.3 — general revenue-loss bound for PAC under any re-solving schedule
-- statement:
--   Consider a valid instance satisfying Assumptions 2.1 and 2.2. There are constants $\rho, \hat\rho, \rho' > 0$, independent of $k$, such that for every $k \ge 1$, every choice of re-solving times $\Gamma^k = \{t^k_l : l = 1,\dots,M^k\}$, every function $v$ with $0 < v(k',t) \le \min\{1, 1/\xi_{\max}\}$ for all $k' \ge 1$ and $t \in [0,1)$ that is integrable in its second argument, and every admissible DLP selector,
--   $$V^k_{\mathrm{DLP}} - \mathbb E[R^k_{\mathrm{PAC}}] \le \rho + \hat\rho k\int_0^1 \min\{1, \rho' F(k,t)\}\,dt, \qquad (8)$$
--   with $F$ and $G$ as in the definition item.
--
--   All the other loss bounds of the paper are obtained from (8) by a choice of $v$.
--
--   **Formalization Note** The constants are chosen after the instance and before $k$, the schedule, $v$ and the selector. The page's condition $v \le 1/\xi_{\max}$ is written $v\,\xi_{\max} \le 1$, which agrees with it for $\xi_{\max} > 0$ and reads $1/0$ as $+\infty$ (instead of Lean's $1/0 = 0$, which would make the hypothesis unsatisfiable). "Integrable in the second argument" is added from Lemma C.1, p. 338, where the same $v$ carries it; the page omits it in Theorem 5.3. The standing hypotheses (`IsValid`) are the disclosed reading of Sec. 2.1, p. 315, Sec. 2.3, p. 317 and Sec. 5.2, p. 327: printed are $\lambda_q \ge 0$, bounded nonnegative consumption and $r_j(0)=0$; read in are $C \ge 0$, consumption laws that are probability measures, $A_{ij} \le \xi_j$ almost surely (the page writes $\xi_j \ge A_{ij}$ on p. 317 and $A_{ij} < \xi_j$ on p. 327; the weaker $\le$ is used), measurable revenue functions, and revenue that is nonnegative and bounded by a common constant (implicit on the page, needed in App. C.4).
-- source:
--   Jasin, Kumar, A Re-Solving Heuristic with Bounded Revenue Loss for Network Revenue Management with Customer Choice, Math. Oper. Res. 37(2), 2012, Theorem 5.3, p. 327, eq. (8)

import Mathlib
import Definitions.Def_ChoicePAC_MidPoint_Model
import Definitions.Def_ChoicePAC_MidPoint_Assumptions
import Definitions.Def_ChoicePAC_MidPoint_GF

namespace ChoicePAC.MidPoint
open MeasureTheory in
theorem theorem_5_3_general_bound {NT n m : ℕ} (I : Instance NT n m) (hI : I.IsValid)
    (h21 : I.Assumption21) (h22 : I.Assumption22) :
    ∃ ρ ρhat ρ' : ℝ, 0 < ρ ∧ 0 < ρhat ∧ 0 < ρ' ∧
      ∀ k : ℕ, 1 ≤ k → ∀ s : Schedule, ∀ v : ℕ → ℝ → ℝ,
        (∀ k' : ℕ, 1 ≤ k' → ∀ t : ℝ, 0 ≤ t → t < 1 →
          0 < v k' t ∧ v k' t ≤ 1 ∧ v k' t * I.ξmax ≤ 1) →
        (∀ k' : ℕ, 1 ≤ k' → IntervalIntegrable (v k') volume 0 1) →
        ∀ sel, I.IsAdmissibleSelector sel →
          I.dlpValue ((k : ℝ) • I.C) ((k : ℝ) • I.lam) - I.pacValue sel k s ≤
            ρ + ρhat * k * ∫ t in (0 : ℝ)..1, min 1 (ρ' * s.F k (v k t) t) := by sorry
end ChoicePAC.MidPoint
