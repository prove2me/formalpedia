-- Prove2me | Theorems.Thm_FiniteCyclicAngleSuccessor
-- name    : FiniteCyclicAngleSuccessor
-- status  : Proved
-- author  : @moona3k
-- created : 2026-10-04T20:25:11.399983+00:00
-- url     : https://prove2.me/theorems/12044317-f72d-4dc8-8e3f-8f54692ad9ef
-- title:
--   Finite Cyclic Angle Successor
-- statement:
--   Let $\iota$ be a nonempty finite set, and let
--   $\theta_i\in[0,2\pi)$ be an injective assignment of normalized angles to
--   the elements of $\iota$.  For an angle $\alpha\in[0,2\pi)$, write
--   $$
--     \tau_i(\alpha)=
--     \begin{cases}
--       2\pi, & \alpha=\theta_i,\\
--       \theta_i-\alpha, & \alpha<\theta_i,\\
--       \theta_i-\alpha+2\pi, & \theta_i<\alpha.
--     \end{cases}
--   $$
--   Then there is a permutation $\operatorname{next}$ of $\iota$ and a
--   clockwise turn function $T(i,j)$ such that
--   $$
--     T(i,j)=\tau_i(\theta_j).
--   $$
--   Every $T(i,j)$ is positive and at most $2\pi$, and
--   $$
--     T(i,j)=2\pi \quad\Longleftrightarrow\quad j=i.
--   $$
--   The element $\operatorname{next}(i)$ has minimal positive clockwise turn
--   from $i$; more precisely, if $j\ne i$, then
--   $$
--     T(i,\operatorname{next}(i))\le T(i,j),
--   $$
--   and if also $j\ne\operatorname{next}(i)$, then the inequality is strict.
--   Moreover
--   $$
--     \operatorname{next}(i)=i
--     \quad\Longleftrightarrow\quad
--     \text{$i$ is the only element of $\iota$}.
--   $$
--   The open interval facts are also part of the conclusion: if
--   $$
--     0<\tau_i(\alpha)<T(i,\operatorname{next}(i)),
--   $$
--   then no listed angle equals $\alpha$; conversely, every
--   $\alpha\in[0,2\pi)$ which is not one of the listed angles lies in one of
--   these open clockwise intervals, i.e. for some $i$,
--   $$
--     0<\tau_i(\alpha)<T(i,\operatorname{next}(i)).
--   $$
--
--   **Formalization Note** This node is ported from the Trellis formalization of the crossing lemma and its consequences ([wpegden/crossing-consequences](https://github.com/wpegden/crossing-consequences), commit `8769d142`, W. Pegden, Apache-2.0); the statement is the Trellis node `FiniteCyclicAngleSuccessor`.
-- source:
--   https://github.com/wpegden/crossing-consequences/blob/8769d142033fce042f502bf2857afb6b1375b5c3/Tablet/FiniteCyclicAngleSuccessor.lean#L1-L527

import Mathlib.Tactic
import Mathlib.Algebra.Group.Fin.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Set.Finite.Basic
import Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.Basic

open Classical
open scoped Fin.NatCast
noncomputable section

lemma FiniteCyclicAngleSuccessor {ι : Type*} [Fintype ι] [Nonempty ι]
    [DecidableEq ι]
    (θ : ι → ℝ)
    (hθ_mem : ∀ i : ι, 0 ≤ θ i ∧ θ i < 2 * Real.pi)
    (hθ_inj : Function.Injective θ) :
    ∃ clockwiseNext : Equiv.Perm ι,
      ∃ clockwiseTurn : ι → ι → ℝ,
        (∀ i j : ι,
          clockwiseTurn i j =
            if j = i then 2 * Real.pi
            else if θ j < θ i then θ i - θ j
            else θ i - θ j + 2 * Real.pi) ∧
        (∀ i j : ι, 0 < clockwiseTurn i j) ∧
        (∀ i j : ι, clockwiseTurn i j ≤ 2 * Real.pi) ∧
        (∀ i j : ι, clockwiseTurn i j = 2 * Real.pi ↔ j = i) ∧
        (∀ i j : ι, j ≠ i →
          clockwiseTurn i (clockwiseNext i) ≤ clockwiseTurn i j) ∧
        (∀ i j : ι, j ≠ i → j ≠ clockwiseNext i →
          clockwiseTurn i (clockwiseNext i) < clockwiseTurn i j) ∧
        (∀ i : ι, clockwiseNext i = i ↔ ∀ j : ι, j = i) ∧
        (∀ i : ι, ∀ α : ℝ,
          0 ≤ α → α < 2 * Real.pi →
            0 <
              (if α = θ i then 2 * Real.pi
               else if α < θ i then θ i - α
               else θ i - α + 2 * Real.pi) →
            (if α = θ i then 2 * Real.pi
             else if α < θ i then θ i - α
             else θ i - α + 2 * Real.pi) <
              clockwiseTurn i (clockwiseNext i) →
            ∀ j : ι, θ j ≠ α) ∧
        (∀ α : ℝ,
          0 ≤ α → α < 2 * Real.pi →
            (∀ j : ι, θ j ≠ α) →
              ∃ i : ι,
                0 <
                  (if α = θ i then 2 * Real.pi
                   else if α < θ i then θ i - α
                   else θ i - α + 2 * Real.pi) ∧
                (if α = θ i then 2 * Real.pi
                 else if α < θ i then θ i - α
                 else θ i - α + 2 * Real.pi) <
                  clockwiseTurn i (clockwiseNext i)) := by sorry
