-- Prove2me | Theorems.Thm_ConsistentSubmodular_physical_multilinear_lift
-- name    : ConsistentSubmodular.physical_multilinear_lift
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-13T16:19:34.852418+00:00
-- url     : https://prove2.me/theorems/337b00f1-b5b9-4b85-81fd-c4b747072c0c
-- title:
--   Physical multilinear lift on the type subprobability simplex
-- statement:
--   Let $f$ be a nonnegative monotone submodular objective on $[n]$, $O_0,\dots,O_m\subseteq[n]$ cores (overlaps and repetitions allowed), $B\subseteq[n]$ a buffer, and $p\in\mathbb{R}^{m+1}$ with $p_i\ge0$ for all $i$ and $\sum_ip_i\le1$. Let $z_e=\sum_{i:\,e\in O_i}p_i$ be the physical inclusion probabilities. Then
--
--   $$\sum_{I\subseteq\{0,\dots,m\}}\Big(\prod_{i\in I}p_i\prod_{i\notin I}(1-p_i)\Big)f\Big(B\cup\bigcup_{i\in I}O_i\Big)\;\le\;\sum_{S\subseteq[n]}\Big(\prod_{e\in S}z_e\prod_{e\notin S}(1-z_e)\Big)f(B\cup S).$$
--
--   The left side is the expectation of the contracted type objective $I\mapsto f(B\cup\bigcup_{i\in I}O_i)$ under independent type coins; the right side is the multilinear extension of $S\mapsto f(B\cup S)$ at the physical vector $z(p)$.
--
--   This is the lift of the type-level mixture value to the multilinear extension on the whole type subprobability simplex (inequality (21) of Lemma B.2 in compatible-profile form).
-- source:
--   Balkanski, Dütting, Fusco, Lattanzi, Norouzi-Fard, Svensson, Zadimoghaddam, Consistent Submodular Maximization with Full Foresight, STOC 2027 submission; the authors' Lean formalization, https://github.com/epfl-thl2/project-consistent-submodular-full-foresight/blob/7f6a57204aa7ba76e9adf56af1d4e465368e4d8a/ConsistentSubmodular/Deterministic/Basic/PhysicalSampling.lean#L211-L232 (`ConsistentSubmodular.physical_multilinear_lift`)

import Mathlib
import Definitions.Def_ConsistentSubmodular_Deterministic_Basic_CompatibleProfiles
import Definitions.Def_ConsistentSubmodular_Deterministic_Basic_PhysicalMap

open scoped BigOperators
open ConsistentSubmodular
variable {ι : Type*} [DecidableEq ι]
variable {n : ℕ}

theorem ConsistentSubmodular.physical_multilinear_lift {m : ℕ} (f : Objective n)
    (cores : Fin (m + 1) → Finset (Fin n)) (B : Finset (Fin n)) (p : Point m)
    (hp : ∀ i, 0 ≤ p i) (hmass : (∑ i, p i) ≤ 1) :
    finiteExpectation p (f.onTypes cores B).value ≤
      finiteExpectation (physicalProbability cores p) (fun S => f.value (B ∪ S)) := by sorry
