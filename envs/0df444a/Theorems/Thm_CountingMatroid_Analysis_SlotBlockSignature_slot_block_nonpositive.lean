-- Prove2me | Theorems.Thm_CountingMatroid_Analysis_SlotBlockSignature_slot_block_nonpositive
-- name    : CountingMatroid.Analysis.SlotBlockSignature.slot_block_nonpositive
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-24T15:26:19.696998+00:00
-- url     : https://prove2.me/theorems/b3ab8394-02a5-47ad-bd26-fc984ad5dff2
-- title:
--   Nonpositivity of the balanced slot-block quadratic form
-- statement:
--   Let $A$ be a finite index set with decidable equality, let $V:A\times A\to\mathbb R$ be any array, let $s_a,s_b:A\to\mathbb R$, and let $u\in\mathbb R$. With coordinates ordered as $A$, then false, then true, define
--   $$M=\begin{pmatrix}V&s_b&s_a\\s_b^{\mathsf T}&0&u\\s_a^{\mathsf T}&u&0\end{pmatrix},\qquad Q(z)=z^{\mathsf T}Mz.$$
--   For $h:A\to\mathbb R$ and $x,y\in\mathbb R$, write $v=(h,x,y)$.
--   Assume $u>0$ and that the positive index of the real quadratic form $Q$ is at most one; equivalently, its largest positive-definite subspace has dimension at most one. If $h,x,y$ satisfy the balance equation
--   $$\sum_{i\in A}(s_a(i)+s_b(i))h_i+u(x+y)=0,$$
--   then
--   $$\sum_{i,j\in A}V_{ij}h_ih_j+2x\sum_{i\in A}s_b(i)h_i+2y\sum_{i\in A}s_a(i)h_i+2uxy\le0.$$
--   This converts the one-positive-direction signature assumption into the balanced quadratic inequality needed for a slot split.
-- source:
--   https://github.com/meelgroup/counting-matroid/blob/dd16a4628fdb095c58fe0f3dfd8e353c6e97443c/CountingMatroid/Analysis/SlotBlockSignature.lean#L62-L94

import Definitions.Def_CountingMatroid_Analysis_SlotBlockSignature
import Mathlib.LinearAlgebra.QuadraticForm.Signature
import Mathlib.Tactic

namespace CountingMatroid.Analysis.SignatureOrthogonalNonpositive
end CountingMatroid.Analysis.SignatureOrthogonalNonpositive
set_option autoImplicit false

/-!
The block-matrix calculation for the transport Hessian. This module proves
the implication from a one-positive-direction bound to the balanced slot
inequality; it does not assert that operational weights satisfy that bound.
-/

namespace CountingMatroid.Analysis.SlotBlockSignature
end CountingMatroid.Analysis.SlotBlockSignature
open CountingMatroid CountingMatroid.Analysis CountingMatroid.Analysis.SlotBlockSignature

open scoped BigOperators

theorem CountingMatroid.Analysis.SlotBlockSignature.slot_block_nonpositive {α : Type*} [Fintype α] [DecidableEq α]
    (V : α → α → ℝ) (sₐ sᵦ : α → ℝ) (u : ℝ) (hu : 0 < u)
    (hsig : sigPos (slotBlockMatrix V sₐ sᵦ u).toQuadraticForm' ≤ 1)
    (h : α → ℝ) (x y : ℝ)
    (hbalance : (∑ i, (sₐ i + sᵦ i) * h i) + u * (x + y) = 0) :
    (∑ i, ∑ j, V i j * h i * h j) +
      2 * x * (∑ i, sᵦ i * h i) +
      2 * y * (∑ i, sₐ i * h i) + 2 * u * x * y ≤ 0 := by sorry
