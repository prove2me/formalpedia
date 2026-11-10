-- Prove2me | Theorems.Thm_DecrAlmostLinearSSSP_Decremental_toggle_descent
-- name    : DecrAlmostLinearSSSP.Decremental.toggle_descent
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-09T07:54:38.977315+00:00
-- url     : https://prove2.me/theorems/d364251e-bf47-441b-ab0d-a7223e8754ec
-- title:
--   Lemma 3.5 — Potential descent per toggle
-- statement:
--   Consider an actual attained, running repair state with no pending report, nonzero cached gradient and a cut tuple whose stopping test fails, $G/U<-1/(4K)$, where $K\ge32$. The next control-flow step toggles the returned cut by $\tau=1/(K^2U)$. With current core costs held fixed and $p'$ the resulting labels,
--
--   $$\Psi(p)-\Psi(p')\ge\frac1{8K^3}.$$
--
--   The potential includes its clipped branches on all real slacks. No feasibility or positive-intermediate-slack hypothesis is added. This exact per-toggle loss supplies the finite global progress budget.
--
--   Differences from the source:
--   - encoding: the actual §3.2.2 run using the dynamic cut interface → attained states of deterministic repair and refresh semantics with the cut quality guarantee on those states; reason: the interface is a standing algorithmic dependency, while no balance or accuracy conclusion is an input hypothesis
-- source:
--   Bin Cui, Hanqing Li, Xupeng Miao, Haoze Wang, STOC 2027 submission #912 (October 2026), p. 14, Lemma 3.5 and equations (3.28)–(3.29); p. 15, concluding descent inequality; pinned PDF: https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/912.pdf

import Mathlib
import Definitions.Def_DecrAlmostLinearSSSP_Decremental_Algorithm

set_option autoImplicit false
open scoped ENNReal NNReal

namespace DecrAlmostLinearSSSP.Decremental

/-- Lemma 3.5: exactly a toggle selected by the failed stopping test. Clipped and negative
intermediate slacks are included in the potential. -/
theorem toggle_descent (b : Core) (K : ℝ) (hK : 32 ≤ K) (choose : State b → CutReply b)
    (hcut : CutQuality b K choose) (s : State b) (hs : Attained b K choose s)
    (hrunning : s.stopped = false) (hdrain : s.pending = []) (hnonzero : s.nonzeroEntries ≠ 0)
    (htest : (choose s).G / (choose s).U < -1 / (4 * K)) :
    potential b s.active (labels b s) -
      potential b (repairStep b K choose s).active (labels b (repairStep b K choose s)) ≥
        1 / (8 * K ^ 3) := by sorry

end DecrAlmostLinearSSSP.Decremental
