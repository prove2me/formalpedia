-- Prove2me | Theorems.Thm_ConsistentSubmodular_physical_intersection_lower
-- name    : ConsistentSubmodular.physical_intersection_lower
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-13T16:22:09.239747+00:00
-- url     : https://prove2.me/theorems/d4827c2d-ff0b-4bde-9a07-9af1a7184608
-- title:
--   Loss of the shared-threshold physical intersection is at most $V$ times the type distance
-- statement:
--   Let $f$ be a nonnegative monotone submodular function on subsets of $[n]$, let $\mathrm{cores}_0,\dots,\mathrm{cores}_m\subseteq[n]$ be physical cores (they may overlap or coincide), and let $B\subseteq[n]$ be a buffer. Let $V\ge 0$ with $f(\mathrm{cores}_i)\le V$ for all $i$. Let $p,q\in\mathbb R^{m+1}$ be points of the simplex. Define the type objective $g(I)=f\big(B\cup\bigcup_{i\in I}\mathrm{cores}_i\big)$ on subsets $I\subseteq\{0,\dots,m\}$, and the physical probability $\pi_p(e)=\sum_{i:\,e\in \mathrm{cores}_i}p_i$ of an element $e\in[n]$. Then
--
--   $$\mathbb E_{I\sim p}\big[g(I)\big]\;-\;V\sum_{i=0}^m|p_i-q_i|\;\le\;\mathbb E_{A\sim\min(\pi_p,\pi_q)}\big[f(B\cup A)\big].$$
--
--   Here $\mathbb E_{I\sim p}$ is the expectation over independent inclusion of each type $i$ with probability $p_i$, and $\mathbb E_{A\sim r}$ is the expectation over a random subset $A\subseteq[n]$ containing each element $e$ independently with probability $r(e)=\min\{\pi_p(e),\pi_q(e)\}$ (the finite expectation of the paper's multilinear extension).
--
--   This lemma bounds the value retained when two fractional profiles are intersected through a common threshold on the physical elements, and is used when rounding fractional windows.
--
--   **Formalization Note** Core overlap is allowed, so $\pi_p(e)$ is not assumed to lie in $[0,1]$; the statement is as given for the weighted sum `finiteExpectation` in the Lean definition.
-- source:
--   Balkanski, Dütting, Fusco, Lattanzi, Norouzi-Fard, Svensson, Zadimoghaddam, Consistent Submodular Maximization with Full Foresight, STOC 2027 submission; the authors' Lean formalization, https://github.com/epfl-thl2/project-consistent-submodular-full-foresight/blob/7f6a57204aa7ba76e9adf56af1d4e465368e4d8a/ConsistentSubmodular/Deterministic/Reduction/PhysicalIntersection.lean#L13-L55 (`ConsistentSubmodular.physical_intersection_lower`)

import Mathlib
import Definitions.Def_ConsistentSubmodular_Deterministic_Basic_CompatibleProfiles
import Definitions.Def_ConsistentSubmodular_Deterministic_Basic_PhysicalMap

open scoped BigOperators
open ConsistentSubmodular

theorem ConsistentSubmodular.physical_intersection_lower {n m : ℕ} (f : Objective n)
    (cores : Fin (m + 1) → Finset (Fin n)) (B : Finset (Fin n))
    (V : ℝ) (hV : 0 ≤ V) (hcore : ∀ i, f.value (cores i) ≤ V)
    (p q : Point m) (hp : IsSimplex p) (hq : IsSimplex q) :
    finiteExpectation p (f.onTypes cores B).value - V * (∑ i, |p i - q i|) ≤
      finiteExpectation (fun e => min (physicalProbability cores p e) (physicalProbability cores q e))
        (fun A => f.value (B ∪ A)) := by sorry
