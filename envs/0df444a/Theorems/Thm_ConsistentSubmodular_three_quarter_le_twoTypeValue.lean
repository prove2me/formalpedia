-- Prove2me | Theorems.Thm_ConsistentSubmodular_three_quarter_le_twoTypeValue
-- name    : ConsistentSubmodular.three_quarter_le_twoTypeValue
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-13T16:19:36.977172+00:00
-- url     : https://prove2.me/theorems/af82b498-3d3d-40b3-9d1f-5544dde74e3b
-- title:
--   Lemma B.3 — every edge point has two-type value at least $3w/4$
-- statement:
--   Let $f$ be a nonnegative monotone submodular objective on $[n]$, $Q,A,B\subseteq[n]$ and $w\in\mathbb{R}$ with $w\le f(Q\cup A)$ and $w\le f(Q\cup B)$. Let
--   $$H_Q(A,B;s)=s(1-s)f(Q)+(1-s)^2f(Q\cup A)+s^2f(Q\cup B)+s(1-s)f(Q\cup A\cup B)$$
--   be the two-type value. Then for every $s\in[0,1]$
--
--   $$\tfrac34\,w\;\le\;H_Q(A,B;s).$$
--
--   This is the last claim of Lemma B.3: if both cores have value at least $w$ under the buffer $Q$, every point of the edge has value at least $3w/4$. It is the source of the factor $3/4$ in the deterministic guarantee.
-- source:
--   Balkanski, Dütting, Fusco, Lattanzi, Norouzi-Fard, Svensson, Zadimoghaddam, Consistent Submodular Maximization with Full Foresight, STOC 2027 submission; the authors' Lean formalization, https://github.com/epfl-thl2/project-consistent-submodular-full-foresight/blob/7f6a57204aa7ba76e9adf56af1d4e465368e4d8a/ConsistentSubmodular/Deterministic/Basic/WindowBounds.lean#L332-L349 (`ConsistentSubmodular.three_quarter_le_twoTypeValue`)

import Mathlib
import Definitions.Def_ConsistentSubmodular_MainStatements

open scoped BigOperators
open ConsistentSubmodular
variable {ι : Type*} [DecidableEq ι]
variable {n : ℕ} (f : Objective n) (Q A B : Finset (Fin n))

theorem ConsistentSubmodular.three_quarter_le_twoTypeValue {w : ℝ} (hwA : w ≤ f.value (Q ∪ A))
    (hwB : w ≤ f.value (Q ∪ B)) {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    3 / 4 * w ≤ twoTypeValue f Q A B s := by sorry
