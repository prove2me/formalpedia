-- Prove2me | solution 1 for syracuse_word_baseline_budget_of_rotated_baseline
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-07T13:27:56.083224+00:00
-- url     : https://prove2.me/submissions/e09aa586-91be-43cf-9892-2e941919c0d1

import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Definitions.Def_syracuseOffsetMod

set_option autoImplicit false

open scoped BigOperators

namespace SyracuseWordBaselineBudget

/-! Attribution. Helper lemmas `affine_constant_append`,
`affine_constant_append_singleton`, `affine_constant_rotation_balance`,
`affine_constant_rotation` and `affine_constant_cons_pos` are copied verbatim from
accepted Prove2me submission 9675ddf1-ef38-491c-84bd-56455a8a8b7f by user
090844a7-327d-477a-b08e-2937c520007f (FakeMink) (Apache-2.0 via Prove2me terms); the same
lemmas also appear in that user's accepted submissions 8c51a6dd and 26ec230a.
Changes: made `private` and moved from namespace `CollatzAffineWordRotationDraft01`
into namespace `SyracuseWordBaselineBudget`; bodies unchanged.
New: `rotate_shapes`, `rotation_step`, `partial_product`, `rotation_product_identity`
and the final budget argument in `solution`. -/

private theorem affine_constant_append (u v : List ℕ) :
    syracuseAffineConstant (u ++ v) =
      3 ^ v.length * syracuseAffineConstant u +
        2 ^ u.sum * syracuseAffineConstant v := by
  induction u with
  | nil =>
      simp [syracuseAffineConstant]
  | cons a u ih =>
      simp only [List.cons_append, syracuseAffineConstant, List.length_append,
        List.sum_cons, ih, Nat.pow_add]
      ring

private theorem affine_constant_append_singleton (as : List ℕ) (a : ℕ) :
    syracuseAffineConstant (as ++ [a]) =
      3 * syracuseAffineConstant as + 2 ^ as.sum := by
  rw [affine_constant_append]
  simp [syracuseAffineConstant]

private theorem affine_constant_rotation_balance (a : ℕ) (as : List ℕ) :
    2 ^ a * syracuseAffineConstant (as ++ [a]) + 3 ^ (as.length + 1) =
      3 * syracuseAffineConstant (a :: as) + 2 ^ (a + as.sum) := by
  rw [affine_constant_append_singleton]
  simp only [syracuseAffineConstant, Nat.pow_add, Nat.pow_succ]
  ring

private theorem affine_constant_rotation (a : ℕ) (as : List ℕ)
    (hgap : 3 ^ (as.length + 1) ≤ 2 ^ (a + as.sum)) :
    2 ^ a * syracuseAffineConstant (as ++ [a]) =
      3 * syracuseAffineConstant (a :: as) +
        (2 ^ (a + as.sum) - 3 ^ (as.length + 1)) := by
  have hcancel :
      2 ^ a * syracuseAffineConstant (as ++ [a]) + 3 ^ (as.length + 1) =
        (3 * syracuseAffineConstant (a :: as) +
          (2 ^ (a + as.sum) - 3 ^ (as.length + 1))) + 3 ^ (as.length + 1) := by
    calc
      2 ^ a * syracuseAffineConstant (as ++ [a]) + 3 ^ (as.length + 1) =
          3 * syracuseAffineConstant (a :: as) + 2 ^ (a + as.sum) :=
        affine_constant_rotation_balance a as
      _ = 3 * syracuseAffineConstant (a :: as) +
          ((2 ^ (a + as.sum) - 3 ^ (as.length + 1)) + 3 ^ (as.length + 1)) := by
        rw [Nat.sub_add_cancel hgap]
      _ = (3 * syracuseAffineConstant (a :: as) +
          (2 ^ (a + as.sum) - 3 ^ (as.length + 1))) + 3 ^ (as.length + 1) :=
        (Nat.add_assoc _ _ _).symm
  exact Nat.add_right_cancel hcancel

private theorem affine_constant_cons_pos (a : ℕ) (as : List ℕ) :
    0 < syracuseAffineConstant (a :: as) := by
  rw [syracuseAffineConstant]
  have hthree : 0 < (3 : ℕ) ^ as.length :=
    Nat.pow_pos_iff.mpr (Or.inl (by norm_num : 0 < (3 : ℕ)))
  omega

/-! New material. -/

/-- Explicit shape of the `d`-th and `(d+1)`-st rotations. -/
private theorem rotate_shapes (w : List ℕ) (d : ℕ) (hd : d < w.length) :
    w.rotate d = w[d] :: (w.drop (d + 1) ++ w.take d) ∧
      w.rotate (d + 1) = (w.drop (d + 1) ++ w.take d) ++ [w[d]] := by
  have h1 : w.rotate d = w[d] :: (w.drop (d + 1) ++ w.take d) := by
    rw [List.rotate_eq_drop_append_take (Nat.le_of_lt hd), List.drop_eq_getElem_cons hd]
    rfl
  refine ⟨h1, ?_⟩
  rw [← List.rotate_rotate, h1, List.rotate_cons_succ, List.rotate_zero]

/-- One-step rotation balance along the rotation orbit of `w`. -/
private theorem rotation_step (w : List ℕ) (hgap : 3 ^ w.length ≤ 2 ^ w.sum)
    (d : ℕ) (hd : d < w.length) :
    2 ^ w[d] * syracuseAffineConstant (w.rotate (d + 1)) =
      3 * syracuseAffineConstant (w.rotate d) + (2 ^ w.sum - 3 ^ w.length) := by
  obtain ⟨h1, h2⟩ := rotate_shapes w d hd
  set as : List ℕ := w.drop (d + 1) ++ w.take d with has
  have hlen : as.length + 1 = w.length := by
    have := List.length_rotate w d
    rw [h1, List.length_cons] at this
    exact this
  have hsum : w[d] + as.sum = w.sum := by
    have := List.Perm.sum_eq (List.rotate_perm w d)
    rw [h1, List.sum_cons] at this
    exact this
  have key := affine_constant_rotation w[d] as (by rw [hlen, hsum]; exact hgap)
  rw [hlen, hsum] at key
  rw [h1, h2]
  exact key

/-- Partial telescoping of the rotation balances. -/
private theorem partial_product (w : List ℕ) (hgap : 3 ^ w.length ≤ 2 ^ w.sum) :
    ∀ k : ℕ, k ≤ w.length →
      2 ^ (w.take k).sum *
          ∏ d ∈ Finset.range k, syracuseAffineConstant (w.rotate (d + 1)) =
        ∏ d ∈ Finset.range k,
          (3 * syracuseAffineConstant (w.rotate d) + (2 ^ w.sum - 3 ^ w.length)) := by
  intro k
  induction k with
  | zero =>
      intro _
      simp
  | succ k ih =>
      intro hk
      have hk' : k < w.length := hk
      have hih := ih (Nat.le_of_lt hk')
      rw [Finset.prod_range_succ, Finset.prod_range_succ, ← hih,
        ← rotation_step w hgap k hk', List.sum_take_succ _ _ hk', Nat.pow_add]
      ring

/-- Exact rotation product identity. -/
theorem rotation_product_identity (w : List ℕ) (hgap : 3 ^ w.length ≤ 2 ^ w.sum) :
    2 ^ w.sum * ∏ d ∈ Finset.range w.length, syracuseAffineConstant (w.rotate d) =
      ∏ d ∈ Finset.range w.length,
        (3 * syracuseAffineConstant (w.rotate d) + (2 ^ w.sum - 3 ^ w.length)) := by
  have hpart := partial_product w hgap w.length le_rfl
  rw [List.take_length] at hpart
  have hcyc : ∏ d ∈ Finset.range w.length, syracuseAffineConstant (w.rotate (d + 1)) =
      ∏ d ∈ Finset.range w.length, syracuseAffineConstant (w.rotate d) := by
    have hA := Finset.prod_range_succ'
      (fun d => syracuseAffineConstant (w.rotate d)) w.length
    have hB := Finset.prod_range_succ
      (fun d => syracuseAffineConstant (w.rotate d)) w.length
    rw [hA, List.rotate_length, ← List.rotate_zero w] at hB
    simp only [List.rotate_zero] at hB
    by_cases hne : w = []
    · subst hne
      simp
    · have hpos : 0 < syracuseAffineConstant w := by
        cases w with
        | nil => exact absurd rfl hne
        | cons a as => exact affine_constant_cons_pos a as
      exact Nat.eq_of_mul_eq_mul_right hpos hB
  rw [hcyc] at hpart
  exact hpart

end SyracuseWordBaselineBudget

open SyracuseWordBaselineBudget in
theorem solution (w : List ℕ) (B : ℕ)
    (hgap : 3 ^ w.length < 2 ^ w.sum)
    (hbaseline : ∀ d : ℕ, d < w.length →
      B * (2 ^ w.sum - 3 ^ w.length) ≤ syracuseAffineConstant (w.rotate d)) :
    2 ^ w.sum * B ^ w.length ≤ (3 * B + 1) ^ w.length := by
  set D : ℕ := 2 ^ w.sum - 3 ^ w.length with hD
  set x : ℕ → ℕ := fun d => syracuseAffineConstant (w.rotate d) with hx
  have hne : w ≠ [] := by
    intro hnil
    simp [hnil] at hgap
  have hxpos : ∀ d, 0 < x d := by
    intro d
    have hrne : w.rotate d ≠ [] := fun h => hne (List.rotate_eq_nil_iff.mp h)
    obtain ⟨a, as, has⟩ := List.exists_cons_of_ne_nil hrne
    simp only [hx, has]
    exact SyracuseWordBaselineBudget.affine_constant_cons_pos a as
  have hP : 0 < ∏ d ∈ Finset.range w.length, x d :=
    Finset.prod_pos (fun d _ => hxpos d)
  have hid := rotation_product_identity w (Nat.le_of_lt hgap)
  have hterm : ∀ d ∈ Finset.range w.length, (3 * x d + D) * B ≤ (3 * B + 1) * x d := by
    intro d hd
    have h := hbaseline d (Finset.mem_range.mp hd)
    have h' : D * B ≤ x d := by
      simpa only [hx, hD, Nat.mul_comm] using h
    nlinarith [h']
  have hprod := Finset.prod_le_prod' hterm
  rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib, Finset.prod_const,
    Finset.prod_const, Finset.card_range] at hprod
  have hmain : (2 ^ w.sum * B ^ w.length) * ∏ d ∈ Finset.range w.length, x d ≤
      (3 * B + 1) ^ w.length * ∏ d ∈ Finset.range w.length, x d := by
    calc (2 ^ w.sum * B ^ w.length) * ∏ d ∈ Finset.range w.length, x d
        = (2 ^ w.sum * ∏ d ∈ Finset.range w.length, x d) * B ^ w.length := by ring
      _ = (∏ d ∈ Finset.range w.length, (3 * x d + D)) * B ^ w.length := by
          rw [hid]
      _ ≤ (3 * B + 1) ^ w.length * ∏ d ∈ Finset.range w.length, x d := hprod
  exact Nat.le_of_mul_le_mul_right hmain hP
