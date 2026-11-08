-- Prove2me | solution 1 for syracuse_primitive_word_ge_6956_rotated_baseline_2786502_of_no_cycle
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-07T13:27:57.306199+00:00
-- url     : https://prove2.me/submissions/03f25fa1-fe7a-4750-99f3-0810270fa813

import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Dynamics.PeriodicPts.Defs
import Mathlib.Tactic.Ring
import Definitions.Def_syracuseStep
import Definitions.Def_syracuseOffsetMod
import Theorems.Thm_syracuse_positive_affine_word_realization

/-
  Attribution.
  Adapted (not verbatim) from accepted Prove2me submissions by user 090844a7-327d-477a-b08e-2937c520007f (FakeMink) (Apache-2.0 via Prove2me terms):
    * the final "m = 1 ⇒ every valuation is 2 ⇒ w.sum = 2 * w.length" block
      (hfixed / hval / hsum, using `decide +kernel`) adapted from
      9675ddf1-ef38-491c-84bd-56455a8a8b7f (`solution`);
    * the rotation-index argument showing `w.rotate q = w` from `T^[q] m = m`
      adapted from `least_positive_return_iff_actual_word_rotation_primitive` in
      50d0932b-ac1c-4a8c-9c0e-d45bf6bb50c1.
  Changes: rewritten for a word realized by syracuse_positive_affine_word_realization
  (78b082d4) and for Mathlib's Function.minimalPeriod.
  New: the least-period identification and the use of the no-cycle hypothesis.
-/

set_option autoImplicit false

open scoped BigOperators

theorem solution
    (hnocycle : ∀ m p : ℕ, 0 < m → 6956 ≤ p →
      Function.minimalPeriod syracuseStep m = p → m = 1)
    (w : List ℕ)
    (hpositive : ∀ a ∈ w, 0 < a)
    (hlength : 6956 ≤ w.length)
    (hprimitive : ∀ d : ℕ, 0 < d → d < w.length → w.rotate d ≠ w)
    (hgap : 3 ^ w.length < 2 ^ w.sum)
    (hlow : 200 * w.sum < 317 * w.length)
    (hlowSharp : 306 * w.sum < 485 * w.length)
    (hbaselineBudget : (2 : ℕ) ^ w.sum * (2310000 : ℕ) ^ w.length ≤
      (3 * 2310000 + 1 : ℕ) ^ w.length)
    (hrotatedBaseline : ∀ d : ℕ, d < w.length →
      (2786502 : ℕ) * (2 ^ w.sum - 3 ^ w.length) ≤
        syracuseAffineConstant (w.rotate d)) :
    ¬(2 ^ w.sum - 3 ^ w.length) ∣ syracuseAffineConstant w := by
  intro hdiv
  obtain ⟨m, hm, hcyc, hword⟩ :=
    syracuse_positive_affine_word_realization w hpositive hgap hdiv
  have hp : 0 < w.length := by omega
  -- the actual valuation sequence of the orbit of `m`
  let e : ℕ → ℕ := fun i => (3 * syracuseStep^[i] m + 1).factorization 2
  have hperiodic : Function.IsPeriodicPt syracuseStep w.length m := hcyc
  have hget : ∀ (i : ℕ) (hi : i < w.length), w[i] = e i := by
    intro i hi
    have h := List.getElem_of_eq hword.symm hi
    rw [h, List.getElem_ofFn]
  have hmod : ∀ j : ℕ, e (j % w.length) = e j := by
    intro j
    change (3 * syracuseStep^[j % w.length] m + 1).factorization 2 =
      (3 * syracuseStep^[j] m + 1).factorization 2
    rw [hperiodic.iterate_mod_apply j]
  -- the least period of `m` equals `w.length`, by primitivity of `w`
  have hmem : m ∈ Function.periodicPts syracuseStep :=
    Function.mk_mem_periodicPts hp hperiodic
  have hqpos : 0 < Function.minimalPeriod syracuseStep m :=
    Function.minimalPeriod_pos_of_mem_periodicPts hmem
  have hqle : Function.minimalPeriod syracuseStep m ≤ w.length :=
    Function.IsPeriodicPt.minimalPeriod_le hp hperiodic
  have hqret : syracuseStep^[Function.minimalPeriod syracuseStep m] m = m :=
    Function.isPeriodicPt_minimalPeriod syracuseStep m
  have hqeq : Function.minimalPeriod syracuseStep m = w.length := by
    by_contra hne
    have hlt : Function.minimalPeriod syracuseStep m < w.length :=
      lt_of_le_of_ne hqle hne
    apply hprimitive _ hqpos hlt
    refine List.ext_getElem (List.length_rotate w _) ?_
    intro i hiRot hiW
    rw [List.getElem_rotate, hget _ (Nat.mod_lt _ hp), hmod, hget i hiW]
    change (3 * syracuseStep^[i + Function.minimalPeriod syracuseStep m] m + 1).factorization 2 =
      (3 * syracuseStep^[i] m + 1).factorization 2
    rw [Function.iterate_add_apply, hqret]
  have hmone : m = 1 := hnocycle m w.length hm hlength hqeq
  -- the trivial cycle has every valuation equal to two
  have hfixed : syracuseStep 1 = 1 := by decide +kernel
  have hval : ∀ i : ℕ, e i = 2 := by
    intro i
    change (3 * syracuseStep^[i] m + 1).factorization 2 = 2
    rw [hmone, Function.iterate_fixed hfixed i]
    decide +kernel
  have hsum : w.sum = 2 * w.length := by
    have h := congrArg List.sum hword
    rw [List.sum_ofFn] at h
    rw [← h]
    change (∑ i : Fin w.length, e i.val) = 2 * w.length
    simp only [hval, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
    ring
  omega
