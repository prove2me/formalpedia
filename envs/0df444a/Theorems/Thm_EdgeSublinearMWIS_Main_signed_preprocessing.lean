-- Prove2me | Theorems.Thm_EdgeSublinearMWIS_Main_signed_preprocessing
-- name    : EdgeSublinearMWIS.Main.signed_preprocessing
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-09T13:45:40.558684+00:00
-- url     : https://prove2.me/theorems/de6b97f0-fb76-4ce6-b6ef-a94e3d3013a5
-- title:
--   Exact preservation under deletion of negative-weight vertices
-- statement:
--   For every finite graph $G$ and every signed rational vertex-weight vector $w$, retaining the vertices $W=\{v:w_v\ge0\}$ preserves the optimum exactly:
--   $$\alpha_w(G[W])=\alpha_w(G).$$
--   The empty independent set is feasible on both sides, including when all weights are negative. This supporting reduction supplies the full signed rational domain stated in the p.2 target, while the p.20 weighted proof starts with nonnegative weights. It is not an additional mission milestone.
--
--   Differences from the source:
--   - encoding: arbitrary finite simple graphs → graphs labeled by Fin n and finite vertex masks; reason: every finite graph admits such a labeling; induced injections transport class membership
--   - encoding: arbitrary rational weights on p.2; nonnegative proof on p.20 → an explicit exact identity for deleting negative vertices; reason: this supplies the elementary preprocessing implicit in the full stated domain without adding a positivity hypothesis
-- source:
--   Édouard Bonnet, Yeonsu Chang, STOC 2027 submission #1044 (October 2026), Theorem 2 rational-weight domain and §6 nonnegative reduction, p.20 (PDF p.20), https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1044.pdf

import Definitions.Def_EdgeSublinearMWIS_Main_AlgorithmContracts

namespace EdgeSublinearMWIS.Main

/-- The exact identity needed to cover the stated signed domain of Theorem 2. -/
theorem signed_preprocessing {n : ℕ} (G : SimpleGraph (Fin n)) (w : Fin n → ℚ) :
    weightedAlphaOn G (Finset.univ.filter (fun v => 0 ≤ w v)) w = weightedAlpha G w := by sorry

end EdgeSublinearMWIS.Main
