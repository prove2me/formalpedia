-- Prove2me | Theorems.Thm_Arxiv0812_1178_closure_kernel_eq_baseline_range
-- name    : Arxiv0812_1178.closure_kernel_eq_baseline_range
-- status  : Proved
-- author  : @Xeroth
-- created : 2026-11-24T08:48:07.946064+00:00
-- url     : https://prove2.me/theorems/edaa5712-1313-46d0-b3cc-e55529cfba3d
-- title:
--   Appendix A, eq. (43): $\ker C=\operatorname{im}B$, and $N_t-1$ phases are missing
-- statement:
--   Let $N_t\ge3$, and let $B$ and $C$ be the baseline and closure operators of Appendix A. Then:
--
--   1. $CB=0$, so $\operatorname{im}B\subseteq\ker C$.
--   2. $\operatorname{rank}B=N_t-1$.
--   3. $\dim\ker C\le N_t-1$.
--   4. $$\ker C=\operatorname{im}B,$$ and $\dim\ker C=N_t-1$.
--   5. There are $N_b=N_t(N_t-1)/2$ baseline phases and $(N_t-1)(N_t-2)/2$ canonical closure phases, and $\operatorname{rank}C=(N_t-1)(N_t-2)/2$ of them are independent. So at each instant $N_t-1$ phases are missing.
--   6. The proportion $\dim\ker C_{N_t}/N_b$ of missing phase information strictly decreases as $N_t$ grows.
--
--   **Formalization Note** Item 6 compares the array of $N_t$ telescopes with every larger complete array.
-- source:
--   Meimon, Mugnier and Le Besnerais, A self-calibration approach for optical long baseline interferometry imaging, arXiv:0812.1178v1 (2008), claim c003; Sec. 2.D, paragraph after eq. (12), PDF p. 5; Appendix A, eqs. (37)-(43), PDF p. 17

import Mathlib
import Definitions.Def_Arxiv0812_1178_Basic

open MeasureTheory ProbabilityTheory Matrix

namespace Arxiv0812_1178

theorem closure_kernel_eq_baseline_range {n : ℕ} (hn : 3 ≤ n) :
    closureOp n * baselineOp n = 0 ∧
    (baselineOp n).rank = n - 1 ∧
    Module.finrank ℝ (LinearMap.ker (closureOp n).mulVecLin) ≤ n - 1 ∧
    LinearMap.ker (closureOp n).mulVecLin = LinearMap.range (baselineOp n).mulVecLin ∧
    Module.finrank ℝ (LinearMap.ker (closureOp n).mulVecLin) = n - 1 ∧
    Fintype.card (Baseline n) = n * (n - 1) / 2 ∧
    Fintype.card (ClosureIdx n) = (n - 1) * (n - 2) / 2 ∧
    (closureOp n).rank = (n - 1) * (n - 2) / 2 ∧
    (∀ m : ℕ, n < m →
      (Module.finrank ℝ (LinearMap.ker (closureOp m).mulVecLin) : ℝ) / Fintype.card (Baseline m) <
        (Module.finrank ℝ (LinearMap.ker (closureOp n).mulVecLin) : ℝ) /
          Fintype.card (Baseline n)) := by sorry

end Arxiv0812_1178
