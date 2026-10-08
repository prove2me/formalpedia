-- Prove2me | Theorems.Thm_DartSuccessorFromLocalClockwiseNext
-- name    : DartSuccessorFromLocalClockwiseNext
-- status  : Proved
-- author  : @moona3k
-- created : 2026-10-04T20:25:01.810752+00:00
-- url     : https://prove2.me/theorems/7d8d64b0-05cb-4149-a613-be73a5105fc4
-- title:
--   Dart Successor From Local Clockwise Next
-- statement:
--   Let $G$ be a finite simple graph.  Suppose that for every vertex $v$ we
--   are given a permutation $c_v$ of the darts whose tail is $v$, and suppose
--   that $c_v$ fixes a dart exactly when that dart is the only dart with tail
--   $v$.  Then there is a permutation $\operatorname{succ}$ of all darts such
--   that, for every dart $d$, the tail of $\operatorname{succ}(d)$ is the head
--   of $d$, and
--   $$
--     \operatorname{succ}(d)=c_{\operatorname{head}(d)}(\bar d),
--   $$
--   where $\bar d$ is the reversed dart.  Moreover, if the only dart with tail
--   $\operatorname{head}(d)$ is $\bar d$, then
--   $\operatorname{succ}(d)=\bar d$.
--
--   **Formalization Note** This node is ported from the Trellis formalization of the crossing lemma and its consequences ([wpegden/crossing-consequences](https://github.com/wpegden/crossing-consequences), commit `8769d142`, W. Pegden, Apache-2.0); the statement is the Trellis node `DartSuccessorFromLocalClockwiseNext`.
-- source:
--   https://github.com/wpegden/crossing-consequences/blob/8769d142033fce042f502bf2857afb6b1375b5c3/Tablet/DartSuccessorFromLocalClockwiseNext.lean#L1-L83

import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Set.Finite.Basic
import Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.Basic

open Classical
noncomputable section

lemma DartSuccessorFromLocalClockwiseNext {V : Type*} [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (clockwiseNext : ∀ v : V, Equiv.Perm {d : G.Dart // d.toProd.1 = v})
    (clockwiseNext_eq_self_iff_isolated :
      ∀ (v : V) (d : {d : G.Dart // d.toProd.1 = v}),
        clockwiseNext v d = d ↔ ∀ e : {d : G.Dart // d.toProd.1 = v}, e = d) :
    ∃ successor : Equiv.Perm G.Dart,
      (∀ d : G.Dart, (successor d).toProd.1 = d.toProd.2) ∧
        (∀ d : G.Dart,
          successor d =
            (clockwiseNext d.toProd.2
              ⟨d.symm, by simp [SimpleGraph.Dart.symm]⟩).1) ∧
        (∀ d : G.Dart,
          (∀ e : {e : G.Dart // e.toProd.1 = d.toProd.2}, e.1 = d.symm) →
            successor d = d.symm) := by sorry
