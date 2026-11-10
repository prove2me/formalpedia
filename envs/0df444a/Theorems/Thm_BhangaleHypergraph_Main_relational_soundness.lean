-- Prove2me | Theorems.Thm_BhangaleHypergraph_Main_relational_soundness
-- name    : BhangaleHypergraph.Main.relational_soundness
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-09T14:07:55.475205+00:00
-- url     : https://prove2.me/theorems/45d2f927-06f6-4002-812f-3a15b958e36c
-- title:
--   Lemma 3.5 — Relational soundness
-- statement:
--   Let $C\ge2$ and let the outer instance have $C+1$ layers and its actual probability law on chains. If pairwise soundness is bounded by $\varepsilon$ and
--   $$\varepsilon<\frac1{\binom{C+1}{2}d^2},\qquad d=(2C)^C,$$
--   then its §3.4 relational instance has no satisfying $C$-coloring.
--
--   The inequality is strict, all occurrence marginals are preserved, and no selector consistency is assumed of the input.
--
--   Differences from the source:
--   - encoding: one-based finite label and color sets → zero-based Fin types and finite subsets; reason: subtracting one gives a bijection and preserves every instance
--   - encoding: the factor d² with d=(2C)^C → the identical power (2C)^(2C); reason: the two integer powers are equal
-- source:
--   Amey Bhangale, STOC 2027 submission #1052 (October 2026), Lemma 3.5, p. 17 (PDF p. 17); https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1052.pdf

import Definitions.Def_BhangaleHypergraph_Main_Relational

namespace BhangaleHypergraph.Main

theorem relational_soundness (G : Outer) (C : ℕ) (hC : 2 ≤ C)
    (hlayers : G.layers = C + 1) (ε : ℝ) (hsound : PairwiseSound G ε)
    (hε : ε < 1 / ((Nat.choose (C + 1) 2 : ℝ) * ((2 * C : ℕ) : ℝ) ^ (2 * C))) :
    ¬ RelColorable (Relational G.toLayered C) C := by sorry

end BhangaleHypergraph.Main
