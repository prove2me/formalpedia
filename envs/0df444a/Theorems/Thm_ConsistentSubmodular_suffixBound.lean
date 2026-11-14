-- Prove2me | Theorems.Thm_ConsistentSubmodular_suffixBound
-- name    : ConsistentSubmodular.suffixBound
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-13T16:25:39.487196+00:00
-- url     : https://prove2.me/theorems/1ffc0371-8b23-4008-8fe8-bb7f1ccb0add
-- title:
--   Lemma B.6 — the suffix bound
-- statement:
--   Let $\lambda,g,u,z\ge0$ and $0\le\gamma\le2$ be real numbers. If
--   $$2g-u\ \le\ \gamma(\lambda+z),$$
--   then
--   $$\lambda+\frac{u+z}{2}-\frac{\min(u,z)}{4}\ \ge\ \frac{2}{2+\gamma}\,(\lambda+g).$$
--
--   Role: Appendix B.2.2, inequality (30); a purely real-analytic inequality used for the suffix $j>c$ in the proof of Theorem B.4.
-- source:
--   Balkanski, Dütting, Fusco, Lattanzi, Norouzi-Fard, Svensson, Zadimoghaddam, Consistent Submodular Maximization with Full Foresight, STOC 2027 submission; the authors' Lean formalization, https://github.com/epfl-thl2/project-consistent-submodular-full-foresight/blob/7f6a57204aa7ba76e9adf56af1d4e465368e4d8a/ConsistentSubmodular/MainResults.lean#L150-L152 (`ConsistentSubmodular.suffixBound`)

import Mathlib
import Definitions.Def_ConsistentSubmodular_MainStatements

open ConsistentSubmodular

theorem ConsistentSubmodular.suffixBound : SuffixBoundGoal := by sorry
