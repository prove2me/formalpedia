-- Prove2me | Theorems.Thm_FiniteElementarySegmentCutParameterList
-- name    : FiniteElementarySegmentCutParameterList
-- status  : Proved
-- author  : @moona3k
-- created : 2026-10-04T20:25:16.784428+00:00
-- url     : https://prove2.me/theorems/f3290d15-fc1c-470e-86d0-f9cc716b4ee8
-- title:
--   Finite Elementary Segment Cut Parameter List
-- statement:
--   [Finite cut parameters on one elementary segment]
--   Let $A\ne B$ be two points in the Euclidean plane, and let $T$ be a
--   finite set of points.  There is a finite list $L$ of real parameters such
--   that:
--   $$
--     L \text{ has no repetitions and is strictly increasing;}
--   $$
--   $$
--     t\in L
--     \quad\Longleftrightarrow\quad
--     t=0\ \text{or}\ t=1\ \text{or}\
--     \bigl(0\le t\le 1\ \text{and}\ \operatorname{lineMap}(A,B;t)\in T\bigr);
--   $$
--   $$
--     0,1\in L,\qquad
--     t\in L \Rightarrow 0\le t\le 1;
--   $$
--   and if $L_n,L_{n+1}$ are consecutive entries of $L$, then
--   $$
--     L_n<L_{n+1}
--   $$
--   and no parameter $t\in[0,1]$ with
--   $\operatorname{lineMap}(A,B;t)\in T$ satisfies
--   $$
--     L_n<t<L_{n+1}.
--   $$
--
--   **Formalization Note** This node is ported from the Trellis formalization of the crossing lemma and its consequences ([wpegden/crossing-consequences](https://github.com/wpegden/crossing-consequences), commit `8769d142`, W. Pegden, Apache-2.0); the statement is the Trellis node `FiniteElementarySegmentCutParameterList`.
-- source:
--   https://github.com/wpegden/crossing-consequences/blob/8769d142033fce042f502bf2857afb6b1375b5c3/Tablet/FiniteElementarySegmentCutParameterList.lean#L1-L92

import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Set.Finite.Basic
import Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.Basic
import Mathlib.Data.Finset.Sort

open Classical
noncomputable section

lemma FiniteElementarySegmentCutParameterList
    (A B : EuclideanSpace ℝ (Fin 2)) (hAB : A ≠ B)
    (T : Finset (EuclideanSpace ℝ (Fin 2))) :
    ∃ L : List ℝ,
      L.Nodup ∧
        L.SortedLT ∧
          (∀ t : ℝ, t ∈ L ↔
            t = 0 ∨ t = 1 ∨
              (0 ≤ t ∧ t ≤ 1 ∧ AffineMap.lineMap A B t ∈ T)) ∧
            (0 : ℝ) ∈ L ∧
              (1 : ℝ) ∈ L ∧
                (∀ t : ℝ, t ∈ L → 0 ≤ t ∧ t ≤ 1) ∧
                  (∀ n (hn : n + 1 < L.length), L[n] < L[n + 1]) ∧
                    (∀ n (hn : n + 1 < L.length) t,
                      0 ≤ t → t ≤ 1 →
                        AffineMap.lineMap A B t ∈ T →
                          ¬ (L[n] < t ∧ t < L[n + 1])) := by sorry
