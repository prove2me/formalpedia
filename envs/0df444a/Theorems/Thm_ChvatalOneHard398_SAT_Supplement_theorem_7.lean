-- Prove2me | Theorems.Thm_ChvatalOneHard398_SAT_Supplement_theorem_7
-- name    : ChvatalOneHard398.SAT.Supplement.theorem_7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T18:26:32.695311+00:00
-- url     : https://prove2.me/theorems/3774a77b-b166-40f8-af18-3ffcec208aec
-- title:
--   Theorem 7 — dimension-preserving decoding
-- statement:
--   For every positive input dimension $n$, rational nonsingular lattice basis $B$ and rational target $t$, under the promise
--   $$\operatorname{dist}(t,B\mathbb Z^n)\le\frac{\lambda_1(B\mathbb Z^n)}{4n^2},$$
--   a uniform deterministic polynomial-time oracle algorithm outputs a closest lattice vector. The oracle decides integer feasibility on thin rational parallelepipeds and may answer arbitrarily on other queries. The algorithm has a fixed polynomial bound on every raw input and every oracle. Every actual query is a rational parallelepiped with positive radius and nonsingular basis in the same $\mathbb R^n$, also on non-promise inputs.
--
--   This companion theorem preserves dimension and has the stronger BDD factor of the parallelepiped result. It is independent of the mission's SAT goal.
--
--   Differences from the source:
--   - encoding: deterministic polynomial-time computations → the published binary TM2 next-step model and finite input records; reason: uniform time bounds charge for writing every query and output on every raw input
--   - encoding: positive-dimensional BDD instances and arbitrary non-promise inputs → an explicit n>0 promise, with raw singular or zero-dimensional inputs permitted; reason: the source approximation factor and first minimum are defined on the promise; total behavior elsewhere is unrestricted
-- source:
--   Alberto Del Pia, 0/1 integer programming over polytopes of Chvátal rank one is as hard as lattice problems, STOC 2027 submission #398 (October 2026), p.12, Theorem 7. https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/398.pdf

import Mathlib
import Definitions.Def_ChvatalOneHard398_SAT_Supplement_Probability

namespace ChvatalOneHard398.SAT.Supplement
open scoped BigOperators
open CombOpt.ChvatalRank

theorem theorem_7 : Reduction7 := by sorry

end ChvatalOneHard398.SAT.Supplement
