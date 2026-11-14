-- Prove2me | Theorems.Thm_ConsistentSubmodular_high_anchor_cubic_nonpositive
-- name    : ConsistentSubmodular.high_anchor_cubic_nonpositive
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-13T16:19:22.825405+00:00
-- url     : https://prove2.me/theorems/58302bd5-fdac-4855-ab10-e559bdb4bbd9
-- title:
--   A cubic inequality on $[0,9/40]$
-- statement:
--   For every real $p$ with $0\le p\le \tfrac{9}{40}$,
--   $$6p^3-13p^2+7p-1\;\le\;0 .$$
--
--   This is a one-variable polynomial inequality used as an auxiliary estimate in the high-anchor scalar analysis of the deterministic certificate construction (Appendix B).
-- source:
--   Balkanski, Dütting, Fusco, Lattanzi, Norouzi-Fard, Svensson, Zadimoghaddam, Consistent Submodular Maximization with Full Foresight, STOC 2027 submission; the authors' Lean formalization, https://github.com/epfl-thl2/project-consistent-submodular-full-foresight/blob/7f6a57204aa7ba76e9adf56af1d4e465368e4d8a/ConsistentSubmodular/Deterministic/Certificates/HighAnchor.lean#L70-L83 (`ConsistentSubmodular.high_anchor_cubic_nonpositive`)

import Mathlib

theorem ConsistentSubmodular.high_anchor_cubic_nonpositive (p : ℝ) (hp : 0 ≤ p) (hp9 : p ≤ 9 / 40) :
    6 * p ^ 3 - 13 * p ^ 2 + 7 * p - 1 ≤ 0 := by sorry
