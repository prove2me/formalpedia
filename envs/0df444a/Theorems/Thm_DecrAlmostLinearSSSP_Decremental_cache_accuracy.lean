-- Prove2me | Theorems.Thm_DecrAlmostLinearSSSP_Decremental_cache_accuracy
-- name    : DecrAlmostLinearSSSP.Decremental.cache_accuracy
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-09T07:54:14.024274+00:00
-- url     : https://prove2.me/theorems/93e55bc0-1af7-4b4f-9593-7b7f5965c620
-- title:
--   Lemma 3.4 — Cache accuracy
-- statement:
--   Use the §3.2.2 initialization, refresh, deletion and repair control flow, with cut quality $K\ge32$ and threshold $\xi=K^{-2}$. At any attained state after every pending detector report has been processed, let $f$ denote current exact capacities, $\widetilde f$ the capacities stored at the last refresh, and $g,\widetilde g$ their incoming-minus-outgoing gradients. Then
--
--   $$(1-K^{-2})f_e\le\widetilde f_e\le(1+K^{-2})f_e\quad(e\in\mathcal E),$$
--   $$|(g-\widetilde g)\cdot x|\le K^{-2}\|x\|_f\quad(x\in\mathbb R^V),$$
--   $$(1-K^{-2})\|x\|_f\le\|x\|_{\widetilde f}\le(1+K^{-2})\|x\|_f\quad(x\in\mathbb R^V).$$
--
--   All three comparisons hold at intermediate repair states as well as stable states. The premise concerns the actual drained report queue, so it does not replace detection by an assumed approximation invariant.
--
--   Differences from the source:
--   - encoding: the actual §3.2.2 run using the dynamic cut interface → attained states of deterministic repair and refresh semantics with the cut quality guarantee on those states; reason: the interface is a standing algorithmic dependency, while no balance or accuracy conclusion is an input hypothesis
-- source:
--   Bin Cui, Hanqing Li, Xupeng Miao, Haoze Wang, STOC 2027 submission #912 (October 2026), p. 13, Lemma 3.4, equations (3.24)–(3.26); pp. 7–11, standing construction and operations; pinned PDF: https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/912.pdf

import Mathlib
import Definitions.Def_DecrAlmostLinearSSSP_Decremental_Algorithm

set_option autoImplicit false
open scoped ENNReal NNReal

namespace DecrAlmostLinearSSSP.Decremental

/-- Lemma 3.4: every comparison at actual report-drained prefixes, including intermediate repairs. -/
theorem cache_accuracy (b : Core) (K : ℝ) (hK : 32 ≤ K) (choose : State b → CutReply b)
    (hcut : CutQuality b K choose) (s : State b) (hs : Attained b K choose s)
    (hdrain : s.pending = []) :
    (∀ e, (1 - K ^ (-2 : ℤ)) * capacity b s.active (labels b s) e ≤ s.cache e ∧
      s.cache e ≤ (1 + K ^ (-2 : ℤ)) * capacity b s.active (labels b s) e) ∧
    (∀ x, |dot (fun v => gradient b (capacity b s.active (labels b s)) v - s.cachedGradient v) x| ≤
      K ^ (-2 : ℤ) * norm b (capacity b s.active (labels b s)) x) ∧
    (∀ x, (1 - K ^ (-2 : ℤ)) * norm b (capacity b s.active (labels b s)) x ≤ norm b s.cache x ∧
      norm b s.cache x ≤ (1 + K ^ (-2 : ℤ)) * norm b (capacity b s.active (labels b s)) x)
    := by sorry

end DecrAlmostLinearSSSP.Decremental
