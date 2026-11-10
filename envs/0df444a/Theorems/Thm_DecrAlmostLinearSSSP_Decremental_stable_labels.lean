-- Prove2me | Theorems.Thm_DecrAlmostLinearSSSP_Decremental_stable_labels
-- name    : DecrAlmostLinearSSSP.Decremental.stable_labels
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-09T07:54:04.280563+00:00
-- url     : https://prove2.me/theorems/a0b68624-7d20-4916-8af2-0d829ca7b289
-- title:
--   Lemma 3.7 — Stable labels and all-target consequence
-- statement:
--   In the §3.2.2 algorithm with $K\ge32$, a state is stable when its actual Repair control flow stops. At every attained stable state, with current labels $p$, exact capacities $f$ and gradient $g=-B^\top f$,
--
--   $$|g\cdot x|\le\tfrac13\|x\|_f\quad(x\in\mathbb R^V,\ x_s=0).$$
--
--   Consequently every logical slack strictly exceeds $\kappa$, and simultaneously $p_v\le z_v\le(1+\epsilon/4)p_v$ for every nonsource vertex. The complete all-target consequence is included. Stability is a control-flow property and does not assume the displayed inequality.
--
--   Differences from the source:
--   - encoding: the actual §3.2.2 run using the dynamic cut interface → attained states of deterministic repair and refresh semantics with the cut quality guarantee on those states; reason: the interface is a standing algorithmic dependency, while no balance or accuracy conclusion is an input hypothesis
--   - encoding: the shared §3.1 graph, parameters and all real source-normalized labels → finite labelled edge sets and extended nonnegative core distances; reason: finite reindexing changes no graph; strict return slacks imply positive labels, so the real-distance inequalities retain their meaning
-- source:
--   Bin Cui, Hanqing Li, Xupeng Miao, Haoze Wang, STOC 2027 submission #912 (October 2026), p. 16, Lemma 3.7; p. 11, Lemma 3.3 for its stated consequence; pinned PDF: https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/912.pdf

import Mathlib
import Definitions.Def_DecrAlmostLinearSSSP_Decremental_Algorithm

set_option autoImplicit false
open scoped ENNReal NNReal

namespace DecrAlmostLinearSSSP.Decremental

/-- Lemma 3.7 includes the direction bound and the full consequence of Lemma 3.3. -/
theorem stable_labels (b : Core) (K : ℝ) (hK : 32 ≤ K) (choose : State b → CutReply b)
    (hcut : CutQuality b K choose) (s : State b) (hs : Attained b K choose s)
    (hstable : Stable b s) :
    Balanced b s.active (labels b s) ∧ AllTarget b s.active (labels b s) := by sorry

end DecrAlmostLinearSSSP.Decremental
