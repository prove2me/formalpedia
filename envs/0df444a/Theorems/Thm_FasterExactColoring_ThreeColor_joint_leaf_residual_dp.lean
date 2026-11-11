-- Prove2me | Theorems.Thm_FasterExactColoring_ThreeColor_joint_leaf_residual_dp
-- name    : FasterExactColoring.ThreeColor.joint_leaf_residual_dp
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T04:12:06.910047+00:00
-- url     : https://prove2.me/theorems/2aa57b30-12d7-4e9a-bf23-11492df285ce
-- title:
--   Lemma 4.9 — joint unmatched-leaf and residual DP
-- statement:
--   For every fixed $\varepsilon>0$, one deterministic program decides 3-colorability of every graph $G$ after preprocessing, in time
--   $$O^*\!\left(B_I3^m3^{(d+t+2r-4m)/6+\varepsilon n}\right).$$
--   Here $B_I=3^p2^q$, $r$ counts leaves, $d+t$ counts residual degree-three vertices, and $m$ is the size of the supplied maximal matching in the leaf graph. These are computed quantities. The program and polynomial constants depend on $\varepsilon$ only; no additional subcubic assumption is imposed on the joint graph of unmatched leaves and residual vertices. The answer is correct on both yes- and no-instances. This is the third algorithmic bound used in the deterministic comparison.
--
--   Differences from the source:
--   - encoding: finite simple graphs and colors labeled 1 through k → SimpleGraph (Fin n) with decidable adjacency and Fin k colors labeled from zero; reason: finite relabeling represents every source instance, including the empty graph
--   - encoding: uniform algorithm with O* runtime suppressing polynomial factors → one finite log-cost RAM program and uniform positive coefficient and natural polynomial exponent, with charged input, steps and output; reason: the source operations have polynomial bit cost; polynomial simulation overhead preserves the exponential bases
--   - encoding: graph after the preprocessing of Section 4.2 → minimum degree three, acyclicity of ambient degree-three vertices, and a modified maximal bushy forest; valid internal roots and a maximal leaf matching where used; reason: these are exactly the source standing conditions, and counts are computed rather than assumed independent
-- source:
--   Ryosuke Yamano, Tetsuo Shibuya, STOC 2027 submission #727 (October 2026), Lemma 4.9, p. 9 (PDF p. 11)

import Mathlib
import Definitions.Def_FasterExactColoring_ThreeColor_RuntimeBounds

namespace FasterExactColoring.ThreeColor

theorem joint_leaf_residual_dp (ε : ℝ) (hε : 0 < ε) :
  ∃ (A : Program) (C : ℝ) (d : ℕ), 0 < C ∧
    solvesPreprocessed A C d (fun a n => jointFactor a n ε) := by sorry

end FasterExactColoring.ThreeColor
