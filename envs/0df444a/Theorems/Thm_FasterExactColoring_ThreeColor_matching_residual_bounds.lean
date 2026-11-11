-- Prove2me | Theorems.Thm_FasterExactColoring_ThreeColor_matching_residual_bounds
-- name    : FasterExactColoring.ThreeColor.matching_residual_bounds
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T04:12:10.837767+00:00
-- url     : https://prove2.me/theorems/5ad98278-d924-4f6b-91e6-6ad8bba8bf52
-- title:
--   Lemma 4.8 — both deterministic and randomized residual bounds
-- statement:
--   For every fixed $\varepsilon>0$, every preprocessed graph $G$ has both a deterministic and a randomized 3-colorability decision algorithm with respective bounds
--   $$O^*(B_IB_R3^{c/6+\varepsilon n}),\qquad O^*(B_IB_R2^{c/6+\varepsilon n}),$$
--   where $B_I=3^p2^q$, $B_R=3^m2^{r-2m}$, $M$ is a maximal matching of the leaf graph, $m=|M|$, and $c$ is the maximum residual-component degree-three count. Every parameter is computed from the supplied valid graph, forest, roots and matching. For each $\varepsilon$, each program and its polynomial constants are uniform in these inputs. The randomized algorithm has no false acceptance and success probability at least $1/2$ on yes-instances. The conjunction retains both alternatives of the printed statement.
--
--   Differences from the source:
--   - encoding: finite simple graphs and colors labeled 1 through k → SimpleGraph (Fin n) with decidable adjacency and Fin k colors labeled from zero; reason: finite relabeling represents every source instance, including the empty graph
--   - encoding: uniform algorithm with O* runtime suppressing polynomial factors → one finite log-cost RAM program and uniform positive coefficient and natural polynomial exponent, with charged input, steps and output; reason: the source operations have polynomial bit cost; polynomial simulation overhead preserves the exponential bases
--   - encoding: graph after the preprocessing of Section 4.2 → minimum degree three, acyclicity of ambient degree-three vertices, and a modified maximal bushy forest; valid internal roots and a maximal leaf matching where used; reason: these are exactly the source standing conditions, and counts are computed rather than assumed independent
--   - encoding: one-sided Monte Carlo success at least a fixed positive constant → success at least one half with worst-case halting on every finite fair coin tape; reason: independent constant repetition and charged amplification give the same O* bound
-- source:
--   Ryosuke Yamano, Tetsuo Shibuya, STOC 2027 submission #727 (October 2026), Lemma 4.8, p. 9 (PDF p. 11)

import Mathlib
import Definitions.Def_FasterExactColoring_ThreeColor_RuntimeBounds

namespace FasterExactColoring.ThreeColor

theorem matching_residual_bounds (ε : ℝ) (hε : 0 < ε) :
  (∃ (A : Program) (C : ℝ) (d : ℕ), 0 < C ∧
    solvesPreprocessed A C d (fun a n => pathFactor a n ε 3)) ∧
  (∃ (A : Program) (C : ℝ) (d : ℕ), 0 < C ∧
    randomSolvesPreprocessed A C d (fun a n => pathFactor a n ε 2)) := by sorry

end FasterExactColoring.ThreeColor
