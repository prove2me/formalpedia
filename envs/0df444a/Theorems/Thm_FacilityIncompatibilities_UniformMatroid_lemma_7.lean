-- Prove2me | Theorems.Thm_FacilityIncompatibilities_UniformMatroid_lemma_7
-- name    : FacilityIncompatibilities.UniformMatroid.lemma_7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:19:35.821597+00:00
-- url     : https://prove2.me/theorems/1caa7147-f777-4e56-bb02-9ac8c9117a15
-- title:
--   Lemma 7 — dual representation of the assignment cost A(X)
-- statement:
--   Let $(V_C,V_F,d,f,\mathcal M)$ be an FL-MI instance and $X\subseteq V_F$ a feasible facility set. Then the minimum connection cost of a feasible assignment to $X$ has the dual representation
--
--   $$A(X)=\max_{p\in\mathbb R^{V_C}}\Big\{\sum_{j\in V_C}p_j-\sum_{i\in X}\max_{I\in\mathcal I}\sum_{j\in I}\big(p_j-d(j,i)\big)\Big\},\tag{2}$$
--
--   and the maximum over $p$ is attained.
--
--   This min–max formula is the starting point of the supermodularity proof of $A(\cdot)$ (Lemma 6).
--
--   **Formalization Note** Lean states that $A(X)$ (finite, since $X$ is feasible) is the greatest element of the set of values of the bracket over all $p\in\mathbb R^{V_C}$.
--
--   Differences from the source:
--   - generalization: metric distances d on V_C ∪ V_F (Definition 1) → a pseudometric: d(x,x)=0, symmetry and the triangle inequality, distinct points may be at distance 0; reason: every metric satisfies these axioms, so every instance of the source is covered
--   - encoding: the real number A(X) with a max over p → (A X).toReal is the greatest element (IsGreatest) of the range of the bracket over p : C → ℝ; reason: A(X) is finite because X is feasible; IsGreatest is attainment of the maximum
-- source:
--   Pengfei Wu, Zachary Friggstad, Facility Location with Customer Incompatibilities, STOC 2027 submission #664 (October 2026), SHA-256 e95d28b65476bd15332cddbb49bb8bfb3c370bb260b03d92b35425595cdb7ab3, Lemma 7, eq. (2), printed p.6 / PDF p.7

import Mathlib
import Definitions.Def_FacilityIncompatibilities_UniformMatroid_Model

open scoped ENNReal

namespace FacilityIncompatibilities.UniformMatroid

/-- **Lemma 7** (printed p.6 / PDF p.7), equation (2): for every feasible facility set `X`,
`A(X) = max_{p ∈ ℝ^{V_C}} { ∑_j p_j − ∑_{i ∈ X} max_{I ∈ ℐ} ∑_{j ∈ I} (p_j − d(j,i)) }`;
the maximum is attained. -/
theorem lemma_7 {C F : Type*} [Fintype C] [Fintype F] (I : Instance C F) (hI : I.Valid)
    (X : Finset F) (hX : I.IsFeasible X) :
    IsGreatest
      (Set.range fun p : C → ℝ =>
        ∑ j, p j - ∑ i ∈ X, matroidMaxWeight I.M (fun j => p j - I.dist j i))
      (I.A X).toReal := by sorry

end FacilityIncompatibilities.UniformMatroid
