-- Prove2me | Theorems.Thm_DecrAlmostLinearSSSP_Decremental_all_target_certificate
-- name    : DecrAlmostLinearSSSP.Decremental.all_target_certificate
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-09T07:52:25.303356+00:00
-- url     : https://prove2.me/theorems/36c36b86-85d4-41d8-bb42-fada7092b61f
-- title:
--   Lemma 3.3 — All-target certificate
-- statement:
--   Let the normalized core and distinct return edges, costs, coefficients and parameters be those of §3.1. Let $p$ be any real label vector with $p_s=0$, define $f_e=\mu_e/\max(\sigma_e,\kappa)$ and $g=-B^\top f$, and suppose
--
--   $$|g\cdot x|\le\tfrac13\|x\|_f\quad\text{for every real direction }x\text{ with }x_s=0.$$
--
--   Then every logical slack satisfies $\sigma_e>\kappa$, and simultaneously at every nonsource vertex,
--
--   $$p_v\le z_v\le(1+\epsilon/4)p_v.$$
--
--   Here $z_v$ is the normalized core distance, even if the vertex has become unreachable in the original graph. The lemma derives feasibility and all-target accuracy from one balance condition; neither feasibility nor positivity of labels is assumed.
--
--   Differences from the source:
--   - encoding: the shared §3.1 graph, parameters and all real source-normalized labels → finite labelled edge sets and extended nonnegative core distances; reason: finite reindexing changes no graph; strict return slacks imply positive labels, so the real-distance inequalities retain their meaning
-- source:
--   Bin Cui, Hanqing Li, Xupeng Miao, Haoze Wang, STOC 2027 submission #912 (October 2026), p. 11, Lemma 3.3, equations (3.16)–(3.17); pp. 7–8, §3.1 standing assumptions; pinned PDF: https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/912.pdf

import Mathlib
import Definitions.Def_DecrAlmostLinearSSSP_Decremental_Potential

set_option autoImplicit false
open scoped ENNReal NNReal

namespace DecrAlmostLinearSSSP.Decremental

/-- Lemma 3.3; feasibility and positive labels are conclusions, not premises. -/
theorem all_target_certificate (b : Core) (active : Finset (Fin b.input.k))
    (p : Fin b.input.n → ℝ) (hs : p b.input.source = 0) (hb : Balanced b active p) :
    AllTarget b active p := by sorry

end DecrAlmostLinearSSSP.Decremental
