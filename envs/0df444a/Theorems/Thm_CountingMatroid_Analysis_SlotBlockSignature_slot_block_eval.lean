-- Prove2me | Theorems.Thm_CountingMatroid_Analysis_SlotBlockSignature_slot_block_eval
-- name    : CountingMatroid.Analysis.SlotBlockSignature.slot_block_eval
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-24T14:42:56.805165+00:00
-- url     : https://prove2.me/theorems/d1ed78ba-92f5-47db-8097-d7cf826e9c0b
-- title:
--   Expansion of the slot-block quadratic form
-- statement:
--   Let $A$ be a finite index set with decidable equality, let $V:A\times A\to\mathbb R$ be any array, let $s_a,s_b:A\to\mathbb R$, and let $u\in\mathbb R$. With coordinates ordered as $A$, then false, then true, define
--   $$M=\begin{pmatrix}V&s_b&s_a\\s_b^{\mathsf T}&0&u\\s_a^{\mathsf T}&u&0\end{pmatrix},\qquad Q(z)=z^{\mathsf T}Mz.$$
--   For $h:A\to\mathbb R$ and $x,y\in\mathbb R$, write $v=(h,x,y)$.
--   Then
--   $$Q(v)=\sum_{i\in A}\sum_{j\in A}V_{ij}h_ih_j+2x\sum_{i\in A}s_b(i)h_i+2y\sum_{i\in A}s_a(i)h_i+2uxy.$$
--   The formula explicitly identifies the old-coordinate block, the two mixed blocks, and the new-coordinate interaction used in the slot signature argument.
-- source:
--   https://github.com/meelgroup/counting-matroid/blob/dd16a4628fdb095c58fe0f3dfd8e353c6e97443c/CountingMatroid/Analysis/SlotBlockSignature.lean#L30-L60

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

theorem CountingMatroid.Analysis.SlotBlockSignature.slot_block_eval {α : Type*} [Fintype α] [DecidableEq α]
    (V : α → α → ℝ) (sₐ sᵦ h : α → ℝ) (u x y : ℝ) :
    (slotBlockMatrix V sₐ sᵦ u).toQuadraticForm' (slotBlockVector h x y) =
      (∑ i, ∑ j, V i j * h i * h j) +
        2 * x * (∑ i, sᵦ i * h i) +
        2 * y * (∑ i, sₐ i * h i) + 2 * u * x * y := by sorry
