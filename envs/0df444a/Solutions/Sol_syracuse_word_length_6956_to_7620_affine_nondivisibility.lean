-- Prove2me | solution 1 for syracuse_word_length_6956_to_7620_affine_nondivisibility
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-07T13:45:15.061418+00:00
-- url     : https://prove2.me/submissions/01c8871d-84a7-4261-9171-8eea2753de00

import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_syracuseOffsetMod
import Theorems.Thm_syracuse_affine_constant_some_rotation_le_mechanical_bound
import Theorems.Thm_syracuse_word_affine_nondivisibility_of_some_rotation_lt_2887463

/-
  Attribution:
  1. Repeated-squaring helper `binaryPow`/`binaryPow_eq`, Farey interval certificates
     `budget_margin_4961`/`mean_upper_of_budget` and `block_power_gap_1054_665`/`mean_lower_of_power_gap`,
     and the unimodular Farey difference reconstruction (`7863 * 665 - 4961 * 1054 = 1`) are adapted from
     accepted Prove2me submission 148bed53-8007-4529-90a5-00c1158db5de (theorem
     86d6ebd5-f48c-4488-ad86-577e76e9b0b1, syracuse_power_gap_baseline_budget_period_sparse_6291)
     by user FakeMink (090844a7-327d-477a-b08e-2937c520007f), Apache-2.0 via the Prove2me terms.
  2. The `Finset.sum` to `Nat.rec` kernel evaluation lemma `sum_eq_rec` is adapted from accepted
     Prove2me submission 5e67e1b7-cc46-4084-9654-6621f1460052 (theorem
     ab3539bc-2660-453c-ac0c-d3f902b3d85c, syracuse_mechanical_numerator_6291_9971_strict_baseline_bounds)
     by user a9c5687f-bf1a-4250-b67a-cad2d27a67f1, Apache-2.0 via the Prove2me terms.
-/

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 0
set_option exponentiation.threshold 200000

open scoped BigOperators

namespace CollatzPeriod6956To7620

def binaryPow : Nat → Nat → Nat → Nat
  | _, _, 0 => 1
  | a, n, fuel + 1 =>
      let r := binaryPow a (n / 2) fuel
      if n % 2 = 0 then r * r else r * r * a

theorem binaryPow_eq (a n fuel : Nat) (h : n < 2 ^ fuel) :
    binaryPow a n fuel = a ^ n := by
  induction fuel generalizing n with
  | zero =>
      have hn : n = 0 := by simpa using h
      subst n
      rfl
  | succ fuel ih =>
      have hn : n / 2 < 2 ^ fuel := by
        rw [pow_succ] at h
        omega
      simp only [binaryPow, ih (n / 2) hn]
      split
      · rename_i heven
        have he : n = n / 2 + n / 2 := by omega
        rw [← pow_add, ← he]
      · rename_i hodd
        have he : n = n / 2 + n / 2 + 1 := by omega
        rw [← pow_add, ← pow_succ, ← he]

private theorem budget_margin_certificate :
    binaryPow 6930001 4961 14 <
      binaryPow 2 7863 14 * binaryPow 2310000 4961 14 := by
  decide +kernel

theorem budget_margin_4961 :
    (6930001 : ℕ) ^ 4961 < 2 ^ 7863 * 2310000 ^ 4961 := by
  simpa only [binaryPow_eq 6930001 4961 14 (by decide),
    binaryPow_eq 2 7863 14 (by decide),
    binaryPow_eq 2310000 4961 14 (by decide)] using budget_margin_certificate

theorem mean_upper_of_budget (p K : ℕ) (hp : 0 < p)
    (hbudget : 2 ^ K * 2310000 ^ p ≤ 6930001 ^ p) :
    4961 * K < 7863 * p := by
  have hbudget4961 :
      (2 : ℕ) ^ (4961 * K) * 2310000 ^ (4961 * p) ≤
        6930001 ^ (4961 * p) := by
    simpa only [Nat.mul_pow, ← Nat.pow_mul,
      Nat.mul_comm K 4961, Nat.mul_comm p 4961] using
      Nat.pow_le_pow_left hbudget 4961
  have hmarginp :
      (6930001 : ℕ) ^ (4961 * p) <
        2 ^ (7863 * p) * 2310000 ^ (4961 * p) := by
    simpa only [Nat.mul_pow, ← Nat.pow_mul] using
      Nat.pow_lt_pow_left budget_margin_4961 (ne_of_gt hp)
  have hscaled :
      (2 : ℕ) ^ (4961 * K) * 2310000 ^ (4961 * p) <
        2 ^ (7863 * p) * 2310000 ^ (4961 * p) :=
    hbudget4961.trans_lt hmarginp
  have hpower : (2 : ℕ) ^ (4961 * K) < 2 ^ (7863 * p) :=
    Nat.lt_of_mul_lt_mul_right hscaled
  exact (Nat.pow_lt_pow_iff_right (Nat.lt_succ_self 1)).mp hpower

private theorem block_power_gap_1054_665 :
    (2 : ℕ) ^ 1054 < 3 ^ 665 := by
  decide +kernel

theorem mean_lower_of_power_gap (p K : ℕ) (hp : 0 < p)
    (hgap : 3 ^ p < 2 ^ K) : 1054 * p < 665 * K := by
  have hblockp : ((2 : ℕ) ^ 1054) ^ p < (3 ^ 665) ^ p :=
    Nat.pow_lt_pow_left block_power_gap_1054_665 (ne_of_gt hp)
  have hgap665 : ((3 : ℕ) ^ p) ^ 665 < (2 ^ K) ^ 665 :=
    Nat.pow_lt_pow_left hgap (Nat.succ_ne_zero 664)
  have hpower : (2 : ℕ) ^ (1054 * p) < 2 ^ (665 * K) := by
    calc
      (2 : ℕ) ^ (1054 * p) = ((2 : ℕ) ^ 1054) ^ p :=
        Nat.pow_mul 2 1054 p
      _ < (3 ^ 665) ^ p := hblockp
      _ = ((3 : ℕ) ^ p) ^ 665 := Nat.pow_right_comm 3 665 p
      _ < (2 ^ K) ^ 665 := hgap665
      _ = (2 : ℕ) ^ (665 * K) := (Nat.pow_mul' 2 665 K).symm
  exact (Nat.pow_lt_pow_iff_right (Nat.lt_succ_self 1)).mp hpower

theorem sum_eq_rec (g : ℕ → ℕ) (n : ℕ) :
    (∑ j ∈ Finset.range n, g j) = Nat.rec (motive := fun _ => ℕ) 0 (fun k acc => acc + g k) n := by
  induction n with
  | zero => simp
  | succ k ih => rw [Finset.sum_range_succ, ih]

theorem mech_upper_6956_11025 :
    Nat.rec (motive := fun _ => ℕ) 0
      (fun k acc => acc + (3 : ℕ) ^ (6956 - 1 - k) * 2 ^ ((11025 * k) / 6956)) 6956 <
      2855820 * ((2 : ℕ) ^ 11025 - 3 ^ 6956) := by
  decide +kernel

end CollatzPeriod6956To7620

open CollatzPeriod6956To7620 in
theorem solution (w : List ℕ)
    (hpositive : ∀ a ∈ w, 0 < a)
    (hlarge : 6956 ≤ w.length)
    (hsmall : w.length < 7621)
    (hgap : 3 ^ w.length < 2 ^ w.sum)
    (hlowSharp : 306 * w.sum < 485 * w.length)
    (hbaselineBudget : (2 : ℕ) ^ w.sum * (2310000 : ℕ) ^ w.length ≤
      (3 * 2310000 + 1 : ℕ) ^ w.length) :
    ¬(2 ^ w.sum - 3 ^ w.length) ∣ syracuseAffineConstant w := by
  have hp : 0 < w.length := by omega
  have hlower := mean_lower_of_power_gap w.length w.sum hp hgap
  have hupper := mean_upper_of_budget w.length w.sum hp hbaselineBudget
  let d : ℕ := 665 * w.sum - 1054 * w.length
  let t : ℕ := 7863 * w.length - 4961 * w.sum
  have hd_pos : 1 ≤ d := by dsimp [d]; omega
  have ht_pos : 1 ≤ t := by dsimp [t]; omega
  have hd_exact : 665 * w.sum = 1054 * w.length + d := by dsimp [d]; omega
  have ht_exact : 7863 * w.length = 4961 * w.sum + t := by dsimp [t]; omega
  have hlen_id : w.length = 665 * t + 4961 * d := by omega
  have hsum_id : w.sum = 1054 * t + 7863 * d := by omega
  have hd_one : d = 1 := by omega
  have ht_three : t = 3 := by omega
  have hlength : w.length = 6956 := by omega
  have hsum : w.sum = 11025 := by omega
  obtain ⟨rot, hrot, hmech⟩ :=
    syracuse_affine_constant_some_rotation_le_mechanical_bound w hp
  have hmech_6956 :
      syracuseAffineConstant (w.rotate rot) ≤
        ∑ j ∈ Finset.range 6956,
          (3 : ℕ) ^ (6956 - 1 - j) * 2 ^ ((11025 * j) / 6956) := by
    simpa only [hlength, hsum] using hmech
  have hstrict :
      (∑ j ∈ Finset.range 6956,
        (3 : ℕ) ^ (6956 - 1 - j) * 2 ^ ((11025 * j) / 6956)) <
        2855820 * ((2 : ℕ) ^ 11025 - 3 ^ 6956) := by
    rw [sum_eq_rec (fun j => (3 : ℕ) ^ (6956 - 1 - j) * 2 ^ ((11025 * j) / 6956)) 6956]
    exact mech_upper_6956_11025
  have hlt_2855820 :
      syracuseAffineConstant (w.rotate rot) <
        2855820 * ((2 : ℕ) ^ 11025 - 3 ^ 6956) :=
    lt_of_le_of_lt hmech_6956 hstrict
  have hle_2887463 :
      2855820 * ((2 : ℕ) ^ 11025 - 3 ^ 6956) ≤
        2887463 * ((2 : ℕ) ^ 11025 - 3 ^ 6956) :=
    Nat.mul_le_mul_right _ (by decide : 2855820 ≤ 2887463)
  have hsmallRot :
      syracuseAffineConstant (w.rotate rot) <
        2887463 * (2 ^ w.sum - 3 ^ w.length) := by
    simpa only [hlength, hsum] using lt_of_lt_of_le hlt_2855820 hle_2887463
  exact syracuse_word_affine_nondivisibility_of_some_rotation_lt_2887463
    w hpositive hgap hlowSharp ⟨rot, hrot, hsmallRot⟩
