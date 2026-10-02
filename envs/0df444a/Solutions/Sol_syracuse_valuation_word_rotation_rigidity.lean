-- Prove2me | solution 1 for syracuse_valuation_word_rotation_rigidity
-- status  : ACCEPTED   (prove)
-- author  : @FakeMink
-- created : 2026-10-01T17:26:09.312565+00:00
-- url     : https://prove2.me/submissions/ace603b7-3822-4b56-983c-5fada807728c

import Mathlib
import Definitions.Def_syracuseStep
import Theorems.Thm_syracuse_cycle_pow_two_gt_pow_three

set_option autoImplicit false

namespace CollatzAffineWordRigidityDraft01

-- Source-only draft: no local compilation or platform acceptance is claimed.
-- The strict gap is a hypothesis, not a conclusion about all exponent words.
theorem affine_word_rigidity
    (X Y : ℕ → ℚ) (e : ℕ → ℕ) (p : ℕ)
    (hXend : X p = X 0) (hYend : Y p = Y 0)
    (hX : ∀ i : ℕ, i < p →
      (2 : ℚ) ^ e i * X (i + 1) = 3 * X i + 1)
    (hY : ∀ i : ℕ, i < p →
      (2 : ℚ) ^ e i * Y (i + 1) = 3 * Y i + 1)
    (hgap : (3 : ℕ) ^ p <
      (2 : ℕ) ^ (∑ i ∈ Finset.range p, e i)) :
    Y 0 = X 0 := by
  let delta : ℕ → ℚ := fun i => Y i - X i
  have hstep (i : ℕ) (hi : i < p) :
      (2 : ℚ) ^ e i * delta (i + 1) = 3 * delta i := by
    dsimp [delta]
    linear_combination hY i hi - hX i hi
  have hprefix : ∀ k : ℕ, k ≤ p →
      (2 : ℚ) ^ (∑ i ∈ Finset.range k, e i) * delta k =
        (3 : ℚ) ^ k * delta 0 := by
    intro k
    induction k with
    | zero =>
        intro _
        simp
    | succ k ih =>
        intro hk
        have hkp : k ≤ p := by omega
        have hklt : k < p := by omega
        calc
          (2 : ℚ) ^ (∑ i ∈ Finset.range (k + 1), e i) *
              delta (k + 1) =
              (2 : ℚ) ^ (∑ i ∈ Finset.range k, e i) *
                ((2 : ℚ) ^ e k * delta (k + 1)) := by
            rw [Finset.sum_range_succ, pow_add]
            ring
          _ = (2 : ℚ) ^ (∑ i ∈ Finset.range k, e i) *
                (3 * delta k) := by
            rw [hstep k hklt]
          _ = 3 * ((2 : ℚ) ^ (∑ i ∈ Finset.range k, e i) *
                delta k) := by ring
          _ = 3 * ((3 : ℚ) ^ k * delta 0) := by
            rw [ih hkp]
          _ = (3 : ℚ) ^ (k + 1) * delta 0 := by
            rw [pow_succ]
            ring
  have hdeltaend : delta p = delta 0 := by
    dsimp [delta]
    rw [hYend, hXend]
  have hclosed :
      ((2 : ℚ) ^ (∑ i ∈ Finset.range p, e i) -
        (3 : ℚ) ^ p) * delta 0 = 0 := by
    have h := hprefix p (le_refl p)
    rw [hdeltaend] at h
    rw [sub_mul, h, sub_self]
  have hgapQ : (3 : ℚ) ^ p <
      (2 : ℚ) ^ (∑ i ∈ Finset.range p, e i) := by
    exact_mod_cast hgap
  have hnonzero :
      (2 : ℚ) ^ (∑ i ∈ Finset.range p, e i) -
        (3 : ℚ) ^ p ≠ 0 :=
    ne_of_gt (sub_pos.mpr hgapQ)
  have hdelta0 : delta 0 = 0 :=
    (mul_eq_zero.mp hclosed).resolve_left hnonzero
  change Y 0 - X 0 = 0 at hdelta0
  exact sub_eq_zero.mp hdelta0

end CollatzAffineWordRigidityDraft01

namespace CollatzSyracuseWordRotationDraft01

-- These helper bodies are flattened from fixed5626_solution_v03.lean.
private theorem step_factorization (n : ℕ) :
    2 ^ ((3 * n + 1).factorization 2) * syracuseStep n = 3 * n + 1 := by
  exact Nat.ordProj_mul_ordCompl_eq_self (3 * n + 1) 2

private theorem periodic_iterate {f : ℕ → ℕ} {m p : ℕ}
    (hcyc : f^[p] m = m) (t : ℕ) :
    f^[p] (f^[t] m) = f^[t] m := by
  calc
    f^[p] (f^[t] m) = f^[p + t] m := (Function.iterate_add_apply f p t m).symm
    _ = f^[t + p] m := by rw [Nat.add_comm]
    _ = f^[t] (f^[p] m) := Function.iterate_add_apply f t p m
    _ = f^[t] m := by rw [hcyc]

-- Conditional helper: its gap is supplied by the public cycle theorem below.
-- This structural result does not exclude arbitrary primitive words or the tail.
theorem syracuse_word_rotation_of_gap (m p d : ℕ)
    (hcyc : syracuseStep^[p] m = m)
    (hword : ∀ i : ℕ, i < p →
      (3 * syracuseStep^[i + d] m + 1).factorization 2 =
        (3 * syracuseStep^[i] m + 1).factorization 2)
    (hgap : (3 : ℕ) ^ p <
      (2 : ℕ) ^ (∑ i ∈ Finset.range p,
        (3 * syracuseStep^[i] m + 1).factorization 2)) :
    syracuseStep^[d] m = m := by
  let X : ℕ → ℚ := fun i => (syracuseStep^[i] m : ℚ)
  let Y : ℕ → ℚ := fun i => (syracuseStep^[i + d] m : ℚ)
  let e : ℕ → ℕ := fun i => (3 * syracuseStep^[i] m + 1).factorization 2
  have hXend : X p = X 0 := by
    dsimp [X]
    simpa only [Function.iterate_zero_apply] using
      congrArg (fun n : ℕ => (n : ℚ)) hcyc
  have hYend : Y p = Y 0 := by
    have hshift : syracuseStep^[p + d] m = syracuseStep^[d] m := by
      rw [Function.iterate_add_apply]
      exact periodic_iterate hcyc d
    dsimp [Y]
    simpa only [Nat.zero_add] using
      congrArg (fun n : ℕ => (n : ℚ)) hshift
  have hXedge (i : ℕ) (_hi : i < p) :
      (2 : ℚ) ^ e i * X (i + 1) = 3 * X i + 1 := by
    have hn : (2 : ℕ) ^ ((3 * syracuseStep^[i] m + 1).factorization 2) *
        syracuseStep^[i + 1] m = 3 * syracuseStep^[i] m + 1 := by
      rw [Function.iterate_succ_apply']
      exact step_factorization (syracuseStep^[i] m)
    dsimp [X, e]
    exact_mod_cast hn
  have hYedge (i : ℕ) (hi : i < p) :
      (2 : ℚ) ^ e i * Y (i + 1) = 3 * Y i + 1 := by
    have hn : (2 : ℕ) ^ ((3 * syracuseStep^[i] m + 1).factorization 2) *
        syracuseStep^[(i + 1) + d] m = 3 * syracuseStep^[i + d] m + 1 := by
      rw [show (i + 1) + d = (i + d) + 1 by omega,
        Function.iterate_succ_apply', ← hword i hi]
      exact step_factorization (syracuseStep^[i + d] m)
    dsimp [Y, e]
    exact_mod_cast hn
  have hrigid : Y 0 = X 0 :=
    CollatzAffineWordRigidityDraft01.affine_word_rigidity
      X Y e p hXend hYend hXedge hYedge hgap
  change (syracuseStep^[0 + d] m : ℚ) =
    (syracuseStep^[0] m : ℚ) at hrigid
  simp only [Nat.zero_add, Function.iterate_zero_apply] at hrigid
  exact_mod_cast hrigid

-- Fresh metadata confirms the imported gap theorem is Proved/public at the
-- pinned Mathlib revision. This draft itself remains uncompiled/unaccepted.
theorem syracuse_word_rotation (m p d : ℕ)
    (hm : 0 < m) (hp : 0 < p)
    (hcyc : syracuseStep^[p] m = m)
    (hword : ∀ i : ℕ, i < p →
      (3 * syracuseStep^[i + d] m + 1).factorization 2 =
        (3 * syracuseStep^[i] m + 1).factorization 2) :
    syracuseStep^[d] m = m := by
  exact syracuse_word_rotation_of_gap m p d hcyc hword
    (syracuse_cycle_pow_two_gt_pow_three m p hm hp hcyc)

end CollatzSyracuseWordRotationDraft01

theorem solution (m p d : ℕ)
    (hm : 0 < m) (hp : 0 < p)
    (hcyc : syracuseStep^[p] m = m)
    (hword : ∀ i : ℕ, i < p →
      (3 * syracuseStep^[i + d] m + 1).factorization 2 =
        (3 * syracuseStep^[i] m + 1).factorization 2) :
    syracuseStep^[d] m = m := by
  exact CollatzSyracuseWordRotationDraft01.syracuse_word_rotation
    m p d hm hp hcyc hword

#print axioms solution
