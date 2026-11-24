-- Prove2me | solution 1 for syracuse_affine_nondivisibility_of_unit_prefix_rotations
-- status  : ACCEPTED   (prove)
-- author  : @immiq
-- created : 2026-11-24T11:11:40.413674+00:00
-- url     : https://prove2.me/submissions/f5242424-3490-4aca-8a9c-8743f50a2107

import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Definitions.Def_syracuseOffsetMod

set_option autoImplicit false

namespace SyracuseUnitPrefix

/- Rotation transport uses FakeMink's accepted submission 26ec230a-e6f3-4394-ab2b-3cc335cd34ad,
   via 0ed7dfeb-d259-47da-a7b6-ab7b55326127, Apache-2.0 under the Prove2Me terms.
   The affine prefix expansion is from submission 14e33d46-bd28-46a7-8d29-8a3deb93bad8. -/
private theorem three_pow_odd (k : ℕ) : Odd ((3 : ℕ) ^ k) := by
  have hthree : Odd (3 : ℕ) := ⟨1, by norm_num⟩
  exact Odd.pow hthree

private theorem two_pow_even (k : ℕ) (hk : 0 < k) : Even ((2 : ℕ) ^ k) := by
  have htwo : Even (2 : ℕ) := ⟨1, by norm_num⟩
  exact Even.pow_of_ne_zero htwo (Nat.ne_of_gt hk)

/-- Canonical affine constants compose by concatenating their exponent words. -/
theorem affine_constant_append (u v : List ℕ) :
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

/-- Appending one exponent adds the final dyadic prefix term. -/
theorem affine_constant_append_singleton (as : List ℕ) (a : ℕ) :
    syracuseAffineConstant (as ++ [a]) =
      3 * syracuseAffineConstant as + 2 ^ as.sum := by
  rw [affine_constant_append]
  simp [syracuseAffineConstant]

/-- Subtraction-free one-position rotation identity, valid for all words. -/
theorem affine_constant_rotation_balance (a : ℕ) (as : List ℕ) :
    2 ^ a * syracuseAffineConstant (as ++ [a]) + 3 ^ (as.length + 1) =
      3 * syracuseAffineConstant (a :: as) + 2 ^ (a + as.sum) := by
  rw [affine_constant_append_singleton]
  simp only [syracuseAffineConstant, Nat.pow_add, Nat.pow_succ]
  ring

/-- Under an explicit arithmetic gap, the balanced identity becomes
2^a*C(rotated word)=3*C(original word)+D, with natural D. -/
theorem affine_constant_rotation (a : ℕ) (as : List ℕ)
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

/-- A positive head exponent makes the canonical numerator odd; positivity
of the other exponents is not required for this fact. -/
theorem affine_constant_odd_of_head_pos (a : ℕ) (as : List ℕ) (ha : 0 < a) :
    Odd (syracuseAffineConstant (a :: as)) := by
  rw [syracuseAffineConstant]
  exact Odd.add_even (three_pow_odd as.length)
    (Even.mul_right (two_pow_even a ha) (syracuseAffineConstant as))

/-- A positive head and positive candidate denominator suffice for odd D.
The needed gap is derived from D>0, never from an unconstructed cycle. -/
theorem affine_denominator_odd_of_pos (a : ℕ) (as : List ℕ) (ha : 0 < a)
    (hD : 0 < 2 ^ (a + as.sum) - 3 ^ (as.length + 1)) :
    Odd (2 ^ (a + as.sum) - 3 ^ (as.length + 1)) := by
  have hK : 0 < a + as.sum := by omega
  have hgap : 3 ^ (as.length + 1) < 2 ^ (a + as.sum) := Nat.sub_pos_iff_lt.mp hD
  exact Nat.Even.sub_odd (Nat.le_of_lt hgap)
    (two_pow_even (a + as.sum) hK) (three_pow_odd (as.length + 1))

/-- One-step divisibility transport with an honest explicit odd-D premise.
Oddness supplies coprimality with the dyadic multiplier. -/
theorem affine_constant_rotation_dvd (a : ℕ) (as : List ℕ)
    (hgap : 3 ^ (as.length + 1) ≤ 2 ^ (a + as.sum))
    (hodd : Odd (2 ^ (a + as.sum) - 3 ^ (as.length + 1)))
    (hdiv : (2 ^ (a + as.sum) - 3 ^ (as.length + 1)) ∣
      syracuseAffineConstant (a :: as)) :
    (2 ^ (a + as.sum) - 3 ^ (as.length + 1)) ∣
      syracuseAffineConstant (as ++ [a]) := by
  let D : ℕ := 2 ^ (a + as.sum) - 3 ^ (as.length + 1)
  have hcop : Nat.Coprime D (2 ^ a) :=
    Nat.Coprime.pow_right a (Nat.coprime_two_right.mpr hodd)
  obtain ⟨k, hk⟩ := hdiv
  have hmul : D ∣ 2 ^ a * syracuseAffineConstant (as ++ [a]) := by
    refine ⟨3 * k + 1, ?_⟩
    calc
      2 ^ a * syracuseAffineConstant (as ++ [a]) =
          3 * syracuseAffineConstant (a :: as) + D := affine_constant_rotation a as hgap
      _ = D * (3 * k + 1) := by
        rw [hk]
        ring
  exact Nat.Coprime.dvd_of_dvd_mul_left hcop hmul

private theorem affine_constant_rotate_one_dvd (w : List ℕ)
    (hgap : 3 ^ w.length ≤ 2 ^ w.sum)
    (hodd : Odd (2 ^ w.sum - 3 ^ w.length))
    (hdiv : (2 ^ w.sum - 3 ^ w.length) ∣ syracuseAffineConstant w) :
    (2 ^ w.sum - 3 ^ w.length) ∣ syracuseAffineConstant (w.rotate 1) := by
  cases w with
  | nil =>
      simp [syracuseAffineConstant]
  | cons a as =>
      have hgap' : 3 ^ (as.length + 1) ≤ 2 ^ (a + as.sum) := by
        simpa only [List.length_cons, List.sum_cons] using hgap
      have hodd' : Odd (2 ^ (a + as.sum) - 3 ^ (as.length + 1)) := by
        simpa only [List.length_cons, List.sum_cons] using hodd
      have hdiv' : (2 ^ (a + as.sum) - 3 ^ (as.length + 1)) ∣
          syracuseAffineConstant (a :: as) := by
        simpa only [List.length_cons, List.sum_cons] using hdiv
      simpa only [List.length_cons, List.sum_cons, List.rotate_cons_succ,
        List.rotate_zero] using affine_constant_rotation_dvd a as hgap' hodd' hdiv'

/-- All rotations preserve the same denominator because length and sum are
invariant. This stronger version needs no positivity assumptions on entries:
the arithmetic gap and odd denominator remain explicit hypotheses. -/
theorem affine_constant_rotate_dvd_of_odd_denominator (w : List ℕ)
    (hgap : 3 ^ w.length ≤ 2 ^ w.sum)
    (hodd : Odd (2 ^ w.sum - 3 ^ w.length))
    (hdiv : (2 ^ w.sum - 3 ^ w.length) ∣ syracuseAffineConstant w) (j : ℕ) :
    (2 ^ w.sum - 3 ^ w.length) ∣ syracuseAffineConstant (w.rotate j) := by
  induction j with
  | zero =>
      simpa only [List.rotate_zero] using hdiv
  | succ j ih =>
      have hsum : (w.rotate j).sum = w.sum :=
        List.Perm.sum_eq (List.rotate_perm w j)
      have hgapR : 3 ^ (w.rotate j).length ≤ 2 ^ (w.rotate j).sum := by
        simpa only [List.length_rotate, hsum] using hgap
      have hoddR : Odd (2 ^ (w.rotate j).sum - 3 ^ (w.rotate j).length) := by
        simpa only [List.length_rotate, hsum] using hodd
      have hdivR : (2 ^ (w.rotate j).sum - 3 ^ (w.rotate j).length) ∣
          syracuseAffineConstant (w.rotate j) := by
        simpa only [List.length_rotate, hsum] using ih
      have hnext := affine_constant_rotate_one_dvd (w.rotate j) hgapR hoddR hdivR
      simpa only [List.length_rotate, hsum, List.rotate_rotate] using hnext

/-- Noncircular positive-word interface: a nonempty positive word with an
explicit strict arithmetic gap and divisibility has divisible canonical
numerator at every rotation. No actual-cycle theorem or realization is used. -/
theorem affine_constant_rotate_dvd (w : List ℕ) (hne : w ≠ [])
    (hpos : ∀ a : ℕ, a ∈ w → 0 < a)
    (hgap : 3 ^ w.length < 2 ^ w.sum)
    (hdiv : (2 ^ w.sum - 3 ^ w.length) ∣ syracuseAffineConstant w) (j : ℕ) :
    (2 ^ w.sum - 3 ^ w.length) ∣ syracuseAffineConstant (w.rotate j) := by
  have hodd : Odd (2 ^ w.sum - 3 ^ w.length) := by
    cases w with
    | nil => exact False.elim (hne rfl)
    | cons a as =>
        have ha : 0 < a := hpos a (by simp)
        have hD : 0 < 2 ^ (a + as.sum) - 3 ^ (as.length + 1) := by
          apply Nat.sub_pos_iff_lt.mpr
          simpa only [List.length_cons, List.sum_cons] using hgap
        simpa only [List.length_cons, List.sum_cons] using
          affine_denominator_odd_of_pos a as ha hD
  exact affine_constant_rotate_dvd_of_odd_denominator w (Nat.le_of_lt hgap) hodd hdiv j

lemma C_eq (w : List ℕ) : syracuseAffineConstant w =
    ∑ j ∈ Finset.range w.length, 3 ^ (w.length - 1 - j) * 2 ^ (w.take j).sum := by
  induction w with
  | nil => simp [syracuseAffineConstant]
  | cons a as ih =>
    rw [syracuseAffineConstant, ih, List.length_cons, Finset.sum_range_succ', Finset.mul_sum,
      add_comm]
    congr 1
    · apply Finset.sum_congr rfl
      intro j _
      rw [List.take_succ_cons, List.sum_cons, pow_add]
      have : as.length + 1 - 1 - (j + 1) = as.length - 1 - j := by omega
      rw [this]; ring
    · simp

private theorem affine_pair (w : List ℕ) (hp : 2 ≤ w.length) (i j : ℕ)
    (h : ∀ n, 0 < n → n < w.length →
      ((w.rotate j).take n).sum = ((w.rotate i).take n).sum + 1) :
    syracuseAffineConstant (w.rotate j) + 3 ^ (w.length - 1) =
      2 * syracuseAffineConstant (w.rotate i) := by
  rw [C_eq, C_eq, List.length_rotate, List.length_rotate]
  let k := w.length - 1
  have ek : w.length = k + 1 := by dsimp [k]; omega
  conv_lhs => lhs; arg 1; rw [ek]
  conv_rhs => rhs; arg 1; rw [ek]
  rw [Finset.sum_range_succ', Finset.sum_range_succ', Nat.mul_add, Finset.mul_sum]
  have es : (∑ n ∈ Finset.range k,
      3 ^ (w.length - 1 - (n+1)) * 2 ^ ((w.rotate j).take (n+1)).sum) =
      ∑ n ∈ Finset.range k, 2 * (3 ^ (w.length - 1 - (n+1)) *
        2 ^ ((w.rotate i).take (n+1)).sum) := by
    apply Finset.sum_congr rfl
    intro n hn
    rw [h (n+1) (by omega) (by have := Finset.mem_range.mp hn; omega), pow_succ]
    ring
  rw [es]
  simp
  omega

private theorem three_mod_eight (p : ℕ) :
    3 ^ p % 8 = 1 ∨ 3 ^ p % 8 = 3 := by
  induction p with
  | zero => decide
  | succ p ih =>
    rw [pow_succ, Nat.mul_mod]
    rcases ih with e | e <;> rw [e] <;> decide

end SyracuseUnitPrefix

open SyracuseUnitPrefix in
theorem solution (w : List ℕ) (hp : 2 ≤ w.length) (hpos : ∀ a ∈ w, 0 < a)
    (hgap : 3 ^ w.length < 2 ^ w.sum)
    (hprefix : ∃ i j : ℕ, ∀ n : ℕ, 0 < n → n < w.length →
      ((w.rotate j).take n).sum = ((w.rotate i).take n).sum + 1) :
    ¬(2 ^ w.sum - 3 ^ w.length) ∣ syracuseAffineConstant w := by
  intro hd
  obtain ⟨i,j,h⟩ := hprefix
  let D := 2 ^ w.sum - 3 ^ w.length
  have rot := affine_constant_rotate_dvd w (by intro e; simp [e] at hp) hpos hgap hd
  have eqn := affine_pair w hp i j h
  have hab : D ∣ syracuseAffineConstant (w.rotate j) + 3 ^ (w.length-1) := by
    rw [eqn]
    exact dvd_mul_of_dvd_right (rot i) _
  have hthree : D ∣ 3 ^ (w.length-1) := (Nat.dvd_add_right (rot j)).mp hab
  have hp3 : D ∣ 3 ^ w.length := hthree.trans (pow_dvd_pow 3 (by omega))
  have eb : D + 3 ^ w.length = 2 ^ w.sum := Nat.sub_add_cancel hgap.le
  have hp2 : D ∣ 2 ^ w.sum := eb ▸ dvd_add (dvd_refl D) hp3
  have hOne : D = 1 := Nat.eq_one_of_dvd_coprimes
    (((by decide : Nat.Coprime 2 3).pow_left w.sum).pow_right w.length) hp2 hp3
  have h9 : (3:ℕ)^2 ≤ 3^w.length := Nat.pow_le_pow_right (by decide) hp
  have hK : 3 ≤ w.sum := by
    by_contra! hh
    have hh' : 2 ^ w.sum ≤ (2:ℕ)^2 := Nat.pow_le_pow_right (by decide) (by omega)
    norm_num at h9 hh'
    omega
  have he : 8 ∣ 2 ^ w.sum := pow_dvd_pow 2 hK
  have hz := Nat.mod_eq_zero_of_dvd he
  have hm := three_mod_eight w.length
  omega
