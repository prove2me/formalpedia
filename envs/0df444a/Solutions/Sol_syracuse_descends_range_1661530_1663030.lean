-- Prove2me | solution 1 for syracuse_descends_range_1661530_1663030
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-10T00:19:19.184846+00:00
-- url     : https://prove2.me/submissions/5bb7c347-4193-4120-b4f0-dc34ac046470

import Mathlib
import Definitions.Def_syracuseStep

set_option maxHeartbeats 1000000

open Nat

/-- Half of all odd numbers descend in a single Syracuse step, uniformly. -/
theorem step_lt_of_one_mod_four (m : ℕ) (h1 : 1 < m) (h4 : m % 4 = 1) : syracuseStep m < m := by
  have hne : 3 * m + 1 ≠ 0 := by omega
  have hdvd : (2:ℕ) ^ 2 ∣ 3 * m + 1 := by
    have : (4:ℕ) ∣ 3 * m + 1 := by omega
    simpa using this
  have hle : 2 ≤ (3 * m + 1).factorization 2 :=
    (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two hne).mp hdvd
  have hpow : (2:ℕ) ^ 2 ≤ 2 ^ ((3 * m + 1).factorization 2) :=
    Nat.pow_le_pow_right (by norm_num) hle
  have h1' : syracuseStep m ≤ (3 * m + 1) / 2 ^ 2 := by
    show ordCompl[2] (3 * m + 1) ≤ _
    exact Nat.div_le_div_left hpow (by positivity)
  have h2' : (3 * m + 1) / 2 ^ 2 < m := by
    apply Nat.div_lt_of_lt_mul
    omega
  omega

/-- `Blo L x` : some Syracuse iterate of `x` drops below `L`. -/
abbrev Blo (L x : ℕ) : Prop := ∃ t : ℕ, syracuseStep^[t] x < L

theorem bbase {L x y : ℕ} (h : syracuseStep x = y) (hy : y < L) : Blo L x :=
  ⟨1, by rw [Function.iterate_one, h]; exact hy⟩

theorem bstep {L x y : ℕ} (h : syracuseStep x = y) (hy : Blo L y) : Blo L x := by
  obtain ⟨t, ht⟩ := hy
  exact ⟨t + 1, by rw [Function.iterate_add_apply, Function.iterate_one, h]; exact ht⟩

theorem se (a : ℕ) {y z : ℕ} (h : 3 * y + 1 = 2 ^ a * z) (hz : Odd z) :
    syracuseStep y = z := by
  have hz0 : z ≠ 0 := by rintro rfl; simp [Nat.odd_iff] at hz
  have hfac : (3 * y + 1).factorization 2 = a := by
    rw [h, Nat.factorization_mul (by positivity) hz0]
    simp [Nat.prime_two,
      Nat.factorization_eq_zero_of_not_dvd (by rwa [Nat.two_dvd_ne_zero, ← Nat.odd_iff])]
  show ordCompl[2] (3 * y + 1) = z
  rw [hfac, h, Nat.mul_div_cancel_left _ (by positivity)]


theorem B4735061 : Blo 1661530 4735061 := bbase (se 8 (by rfl) ⟨27744, by rfl⟩ : syracuseStep 4735061 = 55489) (by norm_num)
theorem B7987301 : Blo 1661530 7987301 := bbase (se 4 (by rfl) ⟨748809, by rfl⟩ : syracuseStep 7987301 = 1497619) (by norm_num)
theorem B2842781 : Blo 1661530 2842781 := bbase (se 3 (by rfl) ⟨533021, by rfl⟩ : syracuseStep 2842781 = 1066043) (by norm_num)
theorem B5611733 : Blo 1661530 5611733 := bbase (se 7 (by rfl) ⟨65762, by rfl⟩ : syracuseStep 5611733 = 131525) (by norm_num)
theorem B5325061 : Blo 1661530 5325061 := bbase (se 4 (by rfl) ⟨499224, by rfl⟩ : syracuseStep 5325061 = 998449) (by norm_num)
theorem B6832421 : Blo 1661530 6832421 := bbase (se 4 (by rfl) ⟨640539, by rfl⟩ : syracuseStep 6832421 = 1281079) (by norm_num)
theorem B2662741 : Blo 1661530 2662741 := bbase (se 10 (by rfl) ⟨3900, by rfl⟩ : syracuseStep 2662741 = 7801) (by norm_num)
theorem B4735493 : Blo 1661530 4735493 := bbase (se 4 (by rfl) ⟨443952, by rfl⟩ : syracuseStep 4735493 = 887905) (by norm_num)
theorem B3154565 : Blo 1661530 3154565 := bbase (se 4 (by rfl) ⟨295740, by rfl⟩ : syracuseStep 3154565 = 591481) (by norm_num)
theorem B5612165 : Blo 1661530 5612165 := bbase (se 4 (by rfl) ⟨526140, by rfl⟩ : syracuseStep 5612165 = 1052281) (by norm_num)
theorem B10650325 : Blo 1661530 10650325 := bbase (se 7 (by rfl) ⟨124808, by rfl⟩ : syracuseStep 10650325 = 249617) (by norm_num)
theorem B3154717 : Blo 1661530 3154717 := bbase (se 3 (by rfl) ⟨591509, by rfl⟩ : syracuseStep 3154717 = 1183019) (by norm_num)
theorem B2597765 : Blo 1661530 2597765 := bbase (se 4 (by rfl) ⟨243540, by rfl⟩ : syracuseStep 2597765 = 487081) (by norm_num)
theorem B8414117 : Blo 1661530 8414117 := bbase (se 4 (by rfl) ⟨788823, by rfl⟩ : syracuseStep 8414117 = 1577647) (by norm_num)
theorem B2532269 : Blo 1661530 2532269 := bbase (se 3 (by rfl) ⟨474800, by rfl⟩ : syracuseStep 2532269 = 949601) (by norm_num)
theorem B12624821 : Blo 1661530 12624821 := bbase (se 5 (by rfl) ⟨591788, by rfl⟩ : syracuseStep 12624821 = 1183577) (by norm_num)
theorem B5612597 : Blo 1661530 5612597 := bbase (se 5 (by rfl) ⟨263090, by rfl⟩ : syracuseStep 5612597 = 526181) (by norm_num)
theorem B3155021 : Blo 1661530 3155021 := bbase (se 3 (by rfl) ⟨591566, by rfl⟩ : syracuseStep 3155021 = 1183133) (by norm_num)
theorem B2663741 : Blo 1661530 2663741 := bbase (se 3 (by rfl) ⟨499451, by rfl⟩ : syracuseStep 2663741 = 998903) (by norm_num)
theorem B2844013 : Blo 1661530 2844013 := bbase (se 3 (by rfl) ⟨533252, by rfl⟩ : syracuseStep 2844013 = 1066505) (by norm_num)
theorem B2024885 : Blo 1661530 2024885 := bbase (se 5 (by rfl) ⟨94916, by rfl⟩ : syracuseStep 2024885 = 189833) (by norm_num)
theorem B1869241 : Blo 1661530 1869241 := bbase (se 2 (by rfl) ⟨700965, by rfl⟩ : syracuseStep 1869241 = 1401931) (by norm_num)
theorem B3548605 : Blo 1661530 3548605 := bbase (se 3 (by rfl) ⟨665363, by rfl⟩ : syracuseStep 3548605 = 1330727) (by norm_num)
theorem B1869277 : Blo 1661530 1869277 := bbase (se 3 (by rfl) ⟨350489, by rfl⟩ : syracuseStep 1869277 = 700979) (by norm_num)
theorem B1869313 : Blo 1661530 1869313 := bbase (se 2 (by rfl) ⟨700992, by rfl⟩ : syracuseStep 1869313 = 1401985) (by norm_num)
theorem B1869349 : Blo 1661530 1869349 := bbase (se 4 (by rfl) ⟨175251, by rfl⟩ : syracuseStep 1869349 = 350503) (by norm_num)
theorem B5121605 : Blo 1661530 5121605 := bbase (se 4 (by rfl) ⟨480150, by rfl⟩ : syracuseStep 5121605 = 960301) (by norm_num)
theorem B1869385 : Blo 1661530 1869385 := bbase (se 2 (by rfl) ⟨701019, by rfl⟩ : syracuseStep 1869385 = 1402039) (by norm_num)
theorem B3368533 : Blo 1661530 3368533 := bbase (se 8 (by rfl) ⟨19737, by rfl⟩ : syracuseStep 3368533 = 39475) (by norm_num)
theorem B3368557 : Blo 1661530 3368557 := bbase (se 3 (by rfl) ⟨631604, by rfl⟩ : syracuseStep 3368557 = 1263209) (by norm_num)
theorem B1869421 : Blo 1661530 1869421 := bbase (se 3 (by rfl) ⟨350516, by rfl⟩ : syracuseStep 1869421 = 701033) (by norm_num)
theorem B1869457 : Blo 1661530 1869457 := bbase (se 2 (by rfl) ⟨701046, by rfl⟩ : syracuseStep 1869457 = 1402093) (by norm_num)
theorem B1869493 : Blo 1661530 1869493 := bbase (se 5 (by rfl) ⟨87632, by rfl⟩ : syracuseStep 1869493 = 175265) (by norm_num)
theorem B1869529 : Blo 1661530 1869529 := bbase (se 2 (by rfl) ⟨701073, by rfl⟩ : syracuseStep 1869529 = 1402147) (by norm_num)
theorem B1869565 : Blo 1661530 1869565 := bbase (se 3 (by rfl) ⟨350543, by rfl⟩ : syracuseStep 1869565 = 701087) (by norm_num)
theorem B1869601 : Blo 1661530 1869601 := bbase (se 2 (by rfl) ⟨701100, by rfl⟩ : syracuseStep 1869601 = 1402201) (by norm_num)
theorem B3155773 : Blo 1661530 3155773 := bbase (se 3 (by rfl) ⟨591707, by rfl⟩ : syracuseStep 3155773 = 1183415) (by norm_num)
theorem B1869637 : Blo 1661530 1869637 := bbase (se 4 (by rfl) ⟨175278, by rfl⟩ : syracuseStep 1869637 = 350557) (by norm_num)
theorem B5326661 : Blo 1661530 5326661 := bbase (se 4 (by rfl) ⟨499374, by rfl⟩ : syracuseStep 5326661 = 998749) (by norm_num)
theorem B17966933 : Blo 1661530 17966933 := bbase (se 9 (by rfl) ⟨52637, by rfl⟩ : syracuseStep 17966933 = 105275) (by norm_num)
theorem B1869673 : Blo 1661530 1869673 := bbase (se 2 (by rfl) ⟨701127, by rfl⟩ : syracuseStep 1869673 = 1402255) (by norm_num)
theorem B1869709 : Blo 1661530 1869709 := bbase (se 3 (by rfl) ⟨350570, by rfl⟩ : syracuseStep 1869709 = 701141) (by norm_num)
theorem B2492309 : Blo 1661530 2492309 := bbase (se 6 (by rfl) ⟨58413, by rfl⟩ : syracuseStep 2492309 = 116827) (by norm_num)
theorem B2492333 : Blo 1661530 2492333 := bbase (se 3 (by rfl) ⟨467312, by rfl⟩ : syracuseStep 2492333 = 934625) (by norm_num)
theorem B1869745 : Blo 1661530 1869745 := bbase (se 2 (by rfl) ⟨701154, by rfl⟩ : syracuseStep 1869745 = 1402309) (by norm_num)
theorem B3549109 : Blo 1661530 3549109 := bbase (se 5 (by rfl) ⟨166364, by rfl⟩ : syracuseStep 3549109 = 332729) (by norm_num)
theorem B2492357 : Blo 1661530 2492357 := bbase (se 4 (by rfl) ⟨233658, by rfl⟩ : syracuseStep 2492357 = 467317) (by norm_num)
theorem B3155917 : Blo 1661530 3155917 := bbase (se 3 (by rfl) ⟨591734, by rfl⟩ : syracuseStep 3155917 = 1183469) (by norm_num)
theorem B6309845 : Blo 1661530 6309845 := bbase (se 7 (by rfl) ⟨73943, by rfl⟩ : syracuseStep 6309845 = 147887) (by norm_num)
theorem B1869781 : Blo 1661530 1869781 := bbase (se 7 (by rfl) ⟨21911, by rfl⟩ : syracuseStep 1869781 = 43823) (by norm_num)
theorem B2492381 : Blo 1661530 2492381 := bbase (se 3 (by rfl) ⟨467321, by rfl⟩ : syracuseStep 2492381 = 934643) (by norm_num)
theorem B2492405 : Blo 1661530 2492405 := bbase (se 5 (by rfl) ⟨116831, by rfl⟩ : syracuseStep 2492405 = 233663) (by norm_num)
theorem B1869817 : Blo 1661530 1869817 := bbase (se 2 (by rfl) ⟨701181, by rfl⟩ : syracuseStep 1869817 = 1402363) (by norm_num)
theorem B2492429 : Blo 1661530 2492429 := bbase (se 3 (by rfl) ⟨467330, by rfl⟩ : syracuseStep 2492429 = 934661) (by norm_num)
theorem B1869853 : Blo 1661530 1869853 := bbase (se 3 (by rfl) ⟨350597, by rfl⟩ : syracuseStep 1869853 = 701195) (by norm_num)
theorem B2492453 : Blo 1661530 2492453 := bbase (se 4 (by rfl) ⟨233667, by rfl⟩ : syracuseStep 2492453 = 467335) (by norm_num)
theorem B3844141 : Blo 1661530 3844141 := bbase (se 3 (by rfl) ⟨720776, by rfl⟩ : syracuseStep 3844141 = 1441553) (by norm_num)
theorem B2492477 : Blo 1661530 2492477 := bbase (se 3 (by rfl) ⟨467339, by rfl⟩ : syracuseStep 2492477 = 934679) (by norm_num)
theorem B1869889 : Blo 1661530 1869889 := bbase (se 2 (by rfl) ⟨701208, by rfl⟩ : syracuseStep 1869889 = 1402417) (by norm_num)
theorem B2492501 : Blo 1661530 2492501 := bbase (se 8 (by rfl) ⟨14604, by rfl⟩ : syracuseStep 2492501 = 29209) (by norm_num)
theorem B115198037 : Blo 1661530 115198037 := bbase (se 8 (by rfl) ⟨674988, by rfl⟩ : syracuseStep 115198037 = 1349977) (by norm_num)
theorem B1869925 : Blo 1661530 1869925 := bbase (se 4 (by rfl) ⟨175305, by rfl⟩ : syracuseStep 1869925 = 350611) (by norm_num)
theorem B2492525 : Blo 1661530 2492525 := bbase (se 3 (by rfl) ⟨467348, by rfl⟩ : syracuseStep 2492525 = 934697) (by norm_num)
theorem B3156077 : Blo 1661530 3156077 := bbase (se 3 (by rfl) ⟨591764, by rfl⟩ : syracuseStep 3156077 = 1183529) (by norm_num)
theorem B2492549 : Blo 1661530 2492549 := bbase (se 4 (by rfl) ⟨233676, by rfl⟩ : syracuseStep 2492549 = 467353) (by norm_num)
theorem B1869961 : Blo 1661530 1869961 := bbase (se 2 (by rfl) ⟨701235, by rfl⟩ : syracuseStep 1869961 = 1402471) (by norm_num)
theorem B10389653 : Blo 1661530 10389653 := bbase (se 6 (by rfl) ⟨243507, by rfl⟩ : syracuseStep 10389653 = 487015) (by norm_num)
theorem B2492573 : Blo 1661530 2492573 := bbase (se 3 (by rfl) ⟨467357, by rfl⟩ : syracuseStep 2492573 = 934715) (by norm_num)
theorem B1869997 : Blo 1661530 1869997 := bbase (se 3 (by rfl) ⟨350624, by rfl⟩ : syracuseStep 1869997 = 701249) (by norm_num)
theorem B2492597 : Blo 1661530 2492597 := bbase (se 5 (by rfl) ⟨116840, by rfl⟩ : syracuseStep 2492597 = 233681) (by norm_num)
theorem B8415413 : Blo 1661530 8415413 := bbase (se 5 (by rfl) ⟨394472, by rfl⟩ : syracuseStep 8415413 = 788945) (by norm_num)
theorem B2803909 : Blo 1661530 2803909 := bbase (se 4 (by rfl) ⟨262866, by rfl⟩ : syracuseStep 2803909 = 525733) (by norm_num)
theorem B2492621 : Blo 1661530 2492621 := bbase (se 3 (by rfl) ⟨467366, by rfl⟩ : syracuseStep 2492621 = 934733) (by norm_num)
theorem B1870033 : Blo 1661530 1870033 := bbase (se 2 (by rfl) ⟨701262, by rfl⟩ : syracuseStep 1870033 = 1402525) (by norm_num)
theorem B2492645 : Blo 1661530 2492645 := bbase (se 4 (by rfl) ⟨233685, by rfl⟩ : syracuseStep 2492645 = 467371) (by norm_num)
theorem B6310133 : Blo 1661530 6310133 := bbase (se 5 (by rfl) ⟨295787, by rfl⟩ : syracuseStep 6310133 = 591575) (by norm_num)
theorem B1870069 : Blo 1661530 1870069 := bbase (se 5 (by rfl) ⟨87659, by rfl⟩ : syracuseStep 1870069 = 175319) (by norm_num)
theorem B2492669 : Blo 1661530 2492669 := bbase (se 3 (by rfl) ⟨467375, by rfl⟩ : syracuseStep 2492669 = 934751) (by norm_num)
theorem B3156221 : Blo 1661530 3156221 := bbase (se 3 (by rfl) ⟨591791, by rfl⟩ : syracuseStep 3156221 = 1183583) (by norm_num)
theorem B2492693 : Blo 1661530 2492693 := bbase (se 6 (by rfl) ⟨58422, by rfl⟩ : syracuseStep 2492693 = 116845) (by norm_num)
theorem B1870105 : Blo 1661530 1870105 := bbase (se 2 (by rfl) ⟨701289, by rfl⟩ : syracuseStep 1870105 = 1402579) (by norm_num)
theorem B2803997 : Blo 1661530 2803997 := bbase (se 3 (by rfl) ⟨525749, by rfl⟩ : syracuseStep 2803997 = 1051499) (by norm_num)
theorem B2492717 : Blo 1661530 2492717 := bbase (se 3 (by rfl) ⟨467384, by rfl⟩ : syracuseStep 2492717 = 934769) (by norm_num)
theorem B1870141 : Blo 1661530 1870141 := bbase (se 3 (by rfl) ⟨350651, by rfl⟩ : syracuseStep 1870141 = 701303) (by norm_num)
theorem B2492741 : Blo 1661530 2492741 := bbase (se 4 (by rfl) ⟨233694, by rfl⟩ : syracuseStep 2492741 = 467389) (by norm_num)
theorem B2492765 : Blo 1661530 2492765 := bbase (se 3 (by rfl) ⟨467393, by rfl⟩ : syracuseStep 2492765 = 934787) (by norm_num)
theorem B1870177 : Blo 1661530 1870177 := bbase (se 2 (by rfl) ⟨701316, by rfl⟩ : syracuseStep 1870177 = 1402633) (by norm_num)
theorem B2492789 : Blo 1661530 2492789 := bbase (se 5 (by rfl) ⟨116849, by rfl⟩ : syracuseStep 2492789 = 233699) (by norm_num)
theorem B1870213 : Blo 1661530 1870213 := bbase (se 4 (by rfl) ⟨175332, by rfl⟩ : syracuseStep 1870213 = 350665) (by norm_num)
theorem B2492813 : Blo 1661530 2492813 := bbase (se 3 (by rfl) ⟨467402, by rfl⟩ : syracuseStep 2492813 = 934805) (by norm_num)
theorem B2804125 : Blo 1661530 2804125 := bbase (se 3 (by rfl) ⟨525773, by rfl⟩ : syracuseStep 2804125 = 1051547) (by norm_num)
theorem B2492837 : Blo 1661530 2492837 := bbase (se 4 (by rfl) ⟨233703, by rfl⟩ : syracuseStep 2492837 = 467407) (by norm_num)
theorem B1870249 : Blo 1661530 1870249 := bbase (se 2 (by rfl) ⟨701343, by rfl⟩ : syracuseStep 1870249 = 1402687) (by norm_num)
theorem B11372981 : Blo 1661530 11372981 := bbase (se 5 (by rfl) ⟨533108, by rfl⟩ : syracuseStep 11372981 = 1066217) (by norm_num)
theorem B2492861 : Blo 1661530 2492861 := bbase (se 3 (by rfl) ⟨467411, by rfl⟩ : syracuseStep 2492861 = 934823) (by norm_num)
theorem B1870285 : Blo 1661530 1870285 := bbase (se 3 (by rfl) ⟨350678, by rfl⟩ : syracuseStep 1870285 = 701357) (by norm_num)
theorem B2492885 : Blo 1661530 2492885 := bbase (se 7 (by rfl) ⟨29213, by rfl⟩ : syracuseStep 2492885 = 58427) (by norm_num)
theorem B2492909 : Blo 1661530 2492909 := bbase (se 3 (by rfl) ⟨467420, by rfl⟩ : syracuseStep 2492909 = 934841) (by norm_num)
theorem B1870321 : Blo 1661530 1870321 := bbase (se 2 (by rfl) ⟨701370, by rfl⟩ : syracuseStep 1870321 = 1402741) (by norm_num)
theorem B2804213 : Blo 1661530 2804213 := bbase (se 5 (by rfl) ⟨131447, by rfl⟩ : syracuseStep 2804213 = 262895) (by norm_num)
theorem B2492933 : Blo 1661530 2492933 := bbase (se 4 (by rfl) ⟨233712, by rfl⟩ : syracuseStep 2492933 = 467425) (by norm_num)
theorem B2132497 : Blo 1661530 2132497 := bbase (se 2 (by rfl) ⟨799686, by rfl⟩ : syracuseStep 2132497 = 1599373) (by norm_num)
theorem B1870357 : Blo 1661530 1870357 := bbase (se 6 (by rfl) ⟨43836, by rfl⟩ : syracuseStep 1870357 = 87673) (by norm_num)
theorem B2492957 : Blo 1661530 2492957 := bbase (se 3 (by rfl) ⟨467429, by rfl⟩ : syracuseStep 2492957 = 934859) (by norm_num)
theorem B3156509 : Blo 1661530 3156509 := bbase (se 3 (by rfl) ⟨591845, by rfl⟩ : syracuseStep 3156509 = 1183691) (by norm_num)
theorem B2492981 : Blo 1661530 2492981 := bbase (se 5 (by rfl) ⟨116858, by rfl⟩ : syracuseStep 2492981 = 233717) (by norm_num)
theorem B1870393 : Blo 1661530 1870393 := bbase (se 2 (by rfl) ⟨701397, by rfl⟩ : syracuseStep 1870393 = 1402795) (by norm_num)
theorem B5057093 : Blo 1661530 5057093 := bbase (se 4 (by rfl) ⟨474102, by rfl⟩ : syracuseStep 5057093 = 948205) (by norm_num)
theorem B2493005 : Blo 1661530 2493005 := bbase (se 3 (by rfl) ⟨467438, by rfl⟩ : syracuseStep 2493005 = 934877) (by norm_num)
theorem B2247245 : Blo 1661530 2247245 := bbase (se 3 (by rfl) ⟨421358, by rfl⟩ : syracuseStep 2247245 = 842717) (by norm_num)
theorem B1870429 : Blo 1661530 1870429 := bbase (se 3 (by rfl) ⟨350705, by rfl⟩ : syracuseStep 1870429 = 701411) (by norm_num)
theorem B2493029 : Blo 1661530 2493029 := bbase (se 4 (by rfl) ⟨233721, by rfl⟩ : syracuseStep 2493029 = 467443) (by norm_num)
theorem B2804341 : Blo 1661530 2804341 := bbase (se 5 (by rfl) ⟨131453, by rfl⟩ : syracuseStep 2804341 = 262907) (by norm_num)
theorem B2493053 : Blo 1661530 2493053 := bbase (se 3 (by rfl) ⟨467447, by rfl⟩ : syracuseStep 2493053 = 934895) (by norm_num)
theorem B1870465 : Blo 1661530 1870465 := bbase (se 2 (by rfl) ⟨701424, by rfl⟩ : syracuseStep 1870465 = 1402849) (by norm_num)
theorem B2493077 : Blo 1661530 2493077 := bbase (se 6 (by rfl) ⟨58431, by rfl⟩ : syracuseStep 2493077 = 116863) (by norm_num)
theorem B2632357 : Blo 1661530 2632357 := bbase (se 4 (by rfl) ⟨246783, by rfl⟩ : syracuseStep 2632357 = 493567) (by norm_num)
theorem B1870501 : Blo 1661530 1870501 := bbase (se 4 (by rfl) ⟨175359, by rfl⟩ : syracuseStep 1870501 = 350719) (by norm_num)
theorem B2493101 : Blo 1661530 2493101 := bbase (se 3 (by rfl) ⟨467456, by rfl⟩ : syracuseStep 2493101 = 934913) (by norm_num)
theorem B3197621 : Blo 1661530 3197621 := bbase (se 5 (by rfl) ⟨149888, by rfl⟩ : syracuseStep 3197621 = 299777) (by norm_num)
theorem B3156661 : Blo 1661530 3156661 := bbase (se 5 (by rfl) ⟨147968, by rfl⟩ : syracuseStep 3156661 = 295937) (by norm_num)
theorem B2493125 : Blo 1661530 2493125 := bbase (se 4 (by rfl) ⟨233730, by rfl⟩ : syracuseStep 2493125 = 467461) (by norm_num)
theorem B1870537 : Blo 1661530 1870537 := bbase (se 2 (by rfl) ⟨701451, by rfl⟩ : syracuseStep 1870537 = 1402903) (by norm_num)
theorem B2804429 : Blo 1661530 2804429 := bbase (se 3 (by rfl) ⟨525830, by rfl⟩ : syracuseStep 2804429 = 1051661) (by norm_num)
theorem B2493149 : Blo 1661530 2493149 := bbase (se 3 (by rfl) ⟨467465, by rfl⟩ : syracuseStep 2493149 = 934931) (by norm_num)
theorem B1870573 : Blo 1661530 1870573 := bbase (se 3 (by rfl) ⟨350732, by rfl⟩ : syracuseStep 1870573 = 701465) (by norm_num)
theorem B2493173 : Blo 1661530 2493173 := bbase (se 5 (by rfl) ⟨116867, by rfl⟩ : syracuseStep 2493173 = 233735) (by norm_num)
theorem B2493197 : Blo 1661530 2493197 := bbase (se 3 (by rfl) ⟨467474, by rfl⟩ : syracuseStep 2493197 = 934949) (by norm_num)
theorem B1870609 : Blo 1661530 1870609 := bbase (se 2 (by rfl) ⟨701478, by rfl⟩ : syracuseStep 1870609 = 1402957) (by norm_num)
theorem B2493221 : Blo 1661530 2493221 := bbase (se 4 (by rfl) ⟨233739, by rfl⟩ : syracuseStep 2493221 = 467479) (by norm_num)
theorem B3549997 : Blo 1661530 3549997 := bbase (se 3 (by rfl) ⟨665624, by rfl⟩ : syracuseStep 3549997 = 1331249) (by norm_num)
theorem B1870645 : Blo 1661530 1870645 := bbase (se 5 (by rfl) ⟨87686, by rfl⟩ : syracuseStep 1870645 = 175373) (by norm_num)
theorem B2493245 : Blo 1661530 2493245 := bbase (se 3 (by rfl) ⟨467483, by rfl⟩ : syracuseStep 2493245 = 934967) (by norm_num)
theorem B2804557 : Blo 1661530 2804557 := bbase (se 3 (by rfl) ⟨525854, by rfl⟩ : syracuseStep 2804557 = 1051709) (by norm_num)
theorem B2493269 : Blo 1661530 2493269 := bbase (se 9 (by rfl) ⟨7304, by rfl⟩ : syracuseStep 2493269 = 14609) (by norm_num)
theorem B2132825 : Blo 1661530 2132825 := bbase (se 2 (by rfl) ⟨799809, by rfl⟩ : syracuseStep 2132825 = 1599619) (by norm_num)
theorem B1870681 : Blo 1661530 1870681 := bbase (se 2 (by rfl) ⟨701505, by rfl⟩ : syracuseStep 1870681 = 1403011) (by norm_num)
theorem B2493293 : Blo 1661530 2493293 := bbase (se 3 (by rfl) ⟨467492, by rfl⟩ : syracuseStep 2493293 = 934985) (by norm_num)
theorem B1870717 : Blo 1661530 1870717 := bbase (se 3 (by rfl) ⟨350759, by rfl⟩ : syracuseStep 1870717 = 701519) (by norm_num)
theorem B4492165 : Blo 1661530 4492165 := bbase (se 4 (by rfl) ⟨421140, by rfl⟩ : syracuseStep 4492165 = 842281) (by norm_num)
theorem B2493317 : Blo 1661530 2493317 := bbase (se 4 (by rfl) ⟨233748, by rfl⟩ : syracuseStep 2493317 = 467497) (by norm_num)
theorem B3738509 : Blo 1661530 3738509 := bbase (se 3 (by rfl) ⟨700970, by rfl⟩ : syracuseStep 3738509 = 1401941) (by norm_num)
theorem B2493341 : Blo 1661530 2493341 := bbase (se 3 (by rfl) ⟨467501, by rfl⟩ : syracuseStep 2493341 = 935003) (by norm_num)
theorem B1870753 : Blo 1661530 1870753 := bbase (se 2 (by rfl) ⟨701532, by rfl⟩ : syracuseStep 1870753 = 1403065) (by norm_num)
theorem B2804645 : Blo 1661530 2804645 := bbase (se 4 (by rfl) ⟨262935, by rfl⟩ : syracuseStep 2804645 = 525871) (by norm_num)
theorem B2493365 : Blo 1661530 2493365 := bbase (se 5 (by rfl) ⟨116876, by rfl⟩ : syracuseStep 2493365 = 233753) (by norm_num)
theorem B1870789 : Blo 1661530 1870789 := bbase (se 4 (by rfl) ⟨175386, by rfl⟩ : syracuseStep 1870789 = 350773) (by norm_num)
theorem B2493389 : Blo 1661530 2493389 := bbase (se 3 (by rfl) ⟨467510, by rfl⟩ : syracuseStep 2493389 = 935021) (by norm_num)
theorem B3738581 : Blo 1661530 3738581 := bbase (se 7 (by rfl) ⟨43811, by rfl⟩ : syracuseStep 3738581 = 87623) (by norm_num)
theorem B9464789 : Blo 1661530 9464789 := bbase (se 7 (by rfl) ⟨110915, by rfl⟩ : syracuseStep 9464789 = 221831) (by norm_num)
theorem B2493413 : Blo 1661530 2493413 := bbase (se 4 (by rfl) ⟨233757, by rfl⟩ : syracuseStep 2493413 = 467515) (by norm_num)
theorem B3156965 : Blo 1661530 3156965 := bbase (se 4 (by rfl) ⟨295965, by rfl⟩ : syracuseStep 3156965 = 591931) (by norm_num)
theorem B1870825 : Blo 1661530 1870825 := bbase (se 2 (by rfl) ⟨701559, by rfl⟩ : syracuseStep 1870825 = 1403119) (by norm_num)
theorem B2493437 : Blo 1661530 2493437 := bbase (se 3 (by rfl) ⟨467519, by rfl⟩ : syracuseStep 2493437 = 935039) (by norm_num)
theorem B1870861 : Blo 1661530 1870861 := bbase (se 3 (by rfl) ⟨350786, by rfl⟩ : syracuseStep 1870861 = 701573) (by norm_num)
theorem B2493461 : Blo 1661530 2493461 := bbase (se 6 (by rfl) ⟨58440, by rfl⟩ : syracuseStep 2493461 = 116881) (by norm_num)
theorem B3738653 : Blo 1661530 3738653 := bbase (se 3 (by rfl) ⟨700997, by rfl⟩ : syracuseStep 3738653 = 1401995) (by norm_num)
theorem B2804773 : Blo 1661530 2804773 := bbase (se 4 (by rfl) ⟨262947, by rfl⟩ : syracuseStep 2804773 = 525895) (by norm_num)
theorem B2493485 : Blo 1661530 2493485 := bbase (se 3 (by rfl) ⟨467528, by rfl⟩ : syracuseStep 2493485 = 935057) (by norm_num)
theorem B1870897 : Blo 1661530 1870897 := bbase (se 2 (by rfl) ⟨701586, by rfl⟩ : syracuseStep 1870897 = 1403173) (by norm_num)
theorem B2493509 : Blo 1661530 2493509 := bbase (se 4 (by rfl) ⟨233766, by rfl⟩ : syracuseStep 2493509 = 467533) (by norm_num)
theorem B2493533 : Blo 1661530 2493533 := bbase (se 3 (by rfl) ⟨467537, by rfl⟩ : syracuseStep 2493533 = 935075) (by norm_num)
theorem B3738725 : Blo 1661530 3738725 := bbase (se 4 (by rfl) ⟨350505, by rfl⟩ : syracuseStep 3738725 = 701011) (by norm_num)
theorem B2493557 : Blo 1661530 2493557 := bbase (se 5 (by rfl) ⟨116885, by rfl⟩ : syracuseStep 2493557 = 233771) (by norm_num)
theorem B2804861 : Blo 1661530 2804861 := bbase (se 3 (by rfl) ⟨525911, by rfl⟩ : syracuseStep 2804861 = 1051823) (by norm_num)
theorem B2493581 : Blo 1661530 2493581 := bbase (se 3 (by rfl) ⟨467546, by rfl⟩ : syracuseStep 2493581 = 935093) (by norm_num)
theorem B2493605 : Blo 1661530 2493605 := bbase (se 4 (by rfl) ⟨233775, by rfl⟩ : syracuseStep 2493605 = 467551) (by norm_num)
theorem B3738797 : Blo 1661530 3738797 := bbase (se 3 (by rfl) ⟨701024, by rfl⟩ : syracuseStep 3738797 = 1402049) (by norm_num)
theorem B2772157 : Blo 1661530 2772157 := bbase (se 3 (by rfl) ⟨519779, by rfl⟩ : syracuseStep 2772157 = 1039559) (by norm_num)
theorem B2493629 : Blo 1661530 2493629 := bbase (se 3 (by rfl) ⟨467555, by rfl⟩ : syracuseStep 2493629 = 935111) (by norm_num)
theorem B19188949 : Blo 1661530 19188949 := bbase (se 7 (by rfl) ⟨224870, by rfl⟩ : syracuseStep 19188949 = 449741) (by norm_num)
theorem B2493653 : Blo 1661530 2493653 := bbase (se 7 (by rfl) ⟨29222, by rfl⟩ : syracuseStep 2493653 = 58445) (by norm_num)
theorem B2493677 : Blo 1661530 2493677 := bbase (se 3 (by rfl) ⟨467564, by rfl⟩ : syracuseStep 2493677 = 935129) (by norm_num)
theorem B3738869 : Blo 1661530 3738869 := bbase (se 5 (by rfl) ⟨175259, by rfl⟩ : syracuseStep 3738869 = 350519) (by norm_num)
theorem B2804989 : Blo 1661530 2804989 := bbase (se 3 (by rfl) ⟨525935, by rfl⟩ : syracuseStep 2804989 = 1051871) (by norm_num)
theorem B2493701 : Blo 1661530 2493701 := bbase (se 4 (by rfl) ⟨233784, by rfl⟩ : syracuseStep 2493701 = 467569) (by norm_num)
theorem B3550493 : Blo 1661530 3550493 := bbase (se 3 (by rfl) ⟨665717, by rfl⟩ : syracuseStep 3550493 = 1331435) (by norm_num)
theorem B2493725 : Blo 1661530 2493725 := bbase (se 3 (by rfl) ⟨467573, by rfl⟩ : syracuseStep 2493725 = 935147) (by norm_num)
theorem B2493749 : Blo 1661530 2493749 := bbase (se 5 (by rfl) ⟨116894, by rfl⟩ : syracuseStep 2493749 = 233789) (by norm_num)
theorem B3738941 : Blo 1661530 3738941 := bbase (se 3 (by rfl) ⟨701051, by rfl⟩ : syracuseStep 3738941 = 1402103) (by norm_num)
theorem B2493773 : Blo 1661530 2493773 := bbase (se 3 (by rfl) ⟨467582, by rfl⟩ : syracuseStep 2493773 = 935165) (by norm_num)
theorem B2805077 : Blo 1661530 2805077 := bbase (se 11 (by rfl) ⟨2054, by rfl⟩ : syracuseStep 2805077 = 4109) (by norm_num)
theorem B2493797 : Blo 1661530 2493797 := bbase (se 4 (by rfl) ⟨233793, by rfl⟩ : syracuseStep 2493797 = 467587) (by norm_num)
theorem B1895789 : Blo 1661530 1895789 := bbase (se 3 (by rfl) ⟨355460, by rfl⟩ : syracuseStep 1895789 = 710921) (by norm_num)
theorem B3370357 : Blo 1661530 3370357 := bbase (se 5 (by rfl) ⟨157985, by rfl⟩ : syracuseStep 3370357 = 315971) (by norm_num)
theorem B2493821 : Blo 1661530 2493821 := bbase (se 3 (by rfl) ⟨467591, by rfl⟩ : syracuseStep 2493821 = 935183) (by norm_num)
theorem B3739013 : Blo 1661530 3739013 := bbase (se 4 (by rfl) ⟨350532, by rfl⟩ : syracuseStep 3739013 = 701065) (by norm_num)
theorem B4205965 : Blo 1661530 4205965 := bbase (se 3 (by rfl) ⟨788618, by rfl⟩ : syracuseStep 4205965 = 1577237) (by norm_num)
theorem B6311317 : Blo 1661530 6311317 := bbase (se 6 (by rfl) ⟨147921, by rfl⟩ : syracuseStep 6311317 = 295843) (by norm_num)
theorem B2493845 : Blo 1661530 2493845 := bbase (se 6 (by rfl) ⟨58449, by rfl⟩ : syracuseStep 2493845 = 116899) (by norm_num)
theorem B2493869 : Blo 1661530 2493869 := bbase (se 3 (by rfl) ⟨467600, by rfl⟩ : syracuseStep 2493869 = 935201) (by norm_num)
theorem B8416709 : Blo 1661530 8416709 := bbase (se 4 (by rfl) ⟨789066, by rfl⟩ : syracuseStep 8416709 = 1578133) (by norm_num)
theorem B2493893 : Blo 1661530 2493893 := bbase (se 4 (by rfl) ⟨233802, by rfl⟩ : syracuseStep 2493893 = 467605) (by norm_num)
theorem B3739085 : Blo 1661530 3739085 := bbase (se 3 (by rfl) ⟨701078, by rfl⟩ : syracuseStep 3739085 = 1402157) (by norm_num)
theorem B2805205 : Blo 1661530 2805205 := bbase (se 7 (by rfl) ⟨32873, by rfl⟩ : syracuseStep 2805205 = 65747) (by norm_num)
theorem B2493917 : Blo 1661530 2493917 := bbase (se 3 (by rfl) ⟨467609, by rfl⟩ : syracuseStep 2493917 = 935219) (by norm_num)
theorem B2493941 : Blo 1661530 2493941 := bbase (se 5 (by rfl) ⟨116903, by rfl⟩ : syracuseStep 2493941 = 233807) (by norm_num)
theorem B4206077 : Blo 1661530 4206077 := bbase (se 3 (by rfl) ⟨788639, by rfl⟩ : syracuseStep 4206077 = 1577279) (by norm_num)
theorem B2493965 : Blo 1661530 2493965 := bbase (se 3 (by rfl) ⟨467618, by rfl⟩ : syracuseStep 2493965 = 935237) (by norm_num)
theorem B3739157 : Blo 1661530 3739157 := bbase (se 6 (by rfl) ⟨87636, by rfl⟩ : syracuseStep 3739157 = 175273) (by norm_num)
theorem B2493989 : Blo 1661530 2493989 := bbase (se 4 (by rfl) ⟨233811, by rfl⟩ : syracuseStep 2493989 = 467623) (by norm_num)
theorem B2805293 : Blo 1661530 2805293 := bbase (se 3 (by rfl) ⟨525992, by rfl⟩ : syracuseStep 2805293 = 1051985) (by norm_num)
theorem B2494013 : Blo 1661530 2494013 := bbase (se 3 (by rfl) ⟨467627, by rfl⟩ : syracuseStep 2494013 = 935255) (by norm_num)
theorem B2494037 : Blo 1661530 2494037 := bbase (se 8 (by rfl) ⟨14613, by rfl⟩ : syracuseStep 2494037 = 29227) (by norm_num)
theorem B3739229 : Blo 1661530 3739229 := bbase (se 3 (by rfl) ⟨701105, by rfl⟩ : syracuseStep 3739229 = 1402211) (by norm_num)
theorem B2494061 : Blo 1661530 2494061 := bbase (se 3 (by rfl) ⟨467636, by rfl⟩ : syracuseStep 2494061 = 935273) (by norm_num)
theorem B2494085 : Blo 1661530 2494085 := bbase (se 4 (by rfl) ⟨233820, by rfl⟩ : syracuseStep 2494085 = 467641) (by norm_num)
theorem B2494109 : Blo 1661530 2494109 := bbase (se 3 (by rfl) ⟨467645, by rfl⟩ : syracuseStep 2494109 = 935291) (by norm_num)
theorem B3739301 : Blo 1661530 3739301 := bbase (se 4 (by rfl) ⟨350559, by rfl⟩ : syracuseStep 3739301 = 701119) (by norm_num)
theorem B2526893 : Blo 1661530 2526893 := bbase (se 3 (by rfl) ⟨473792, by rfl⟩ : syracuseStep 2526893 = 947585) (by norm_num)
theorem B2805421 : Blo 1661530 2805421 := bbase (se 3 (by rfl) ⟨526016, by rfl⟩ : syracuseStep 2805421 = 1052033) (by norm_num)
theorem B2494133 : Blo 1661530 2494133 := bbase (se 5 (by rfl) ⟨116912, by rfl⟩ : syracuseStep 2494133 = 233825) (by norm_num)
theorem B4206269 : Blo 1661530 4206269 := bbase (se 3 (by rfl) ⟨788675, by rfl⟩ : syracuseStep 4206269 = 1577351) (by norm_num)
theorem B6311621 : Blo 1661530 6311621 := bbase (se 4 (by rfl) ⟨591714, by rfl⟩ : syracuseStep 6311621 = 1183429) (by norm_num)
theorem B2494157 : Blo 1661530 2494157 := bbase (se 3 (by rfl) ⟨467654, by rfl⟩ : syracuseStep 2494157 = 935309) (by norm_num)
theorem B2494181 : Blo 1661530 2494181 := bbase (se 4 (by rfl) ⟨233829, by rfl⟩ : syracuseStep 2494181 = 467659) (by norm_num)
theorem B3739373 : Blo 1661530 3739373 := bbase (se 3 (by rfl) ⟨701132, by rfl⟩ : syracuseStep 3739373 = 1402265) (by norm_num)
theorem B2494205 : Blo 1661530 2494205 := bbase (se 3 (by rfl) ⟨467663, by rfl⟩ : syracuseStep 2494205 = 935327) (by norm_num)
theorem B2805509 : Blo 1661530 2805509 := bbase (se 4 (by rfl) ⟨263016, by rfl⟩ : syracuseStep 2805509 = 526033) (by norm_num)
theorem B2494229 : Blo 1661530 2494229 := bbase (se 6 (by rfl) ⟨58458, by rfl⟩ : syracuseStep 2494229 = 116917) (by norm_num)
theorem B2494253 : Blo 1661530 2494253 := bbase (se 3 (by rfl) ⟨467672, by rfl⟩ : syracuseStep 2494253 = 935345) (by norm_num)
theorem B3739445 : Blo 1661530 3739445 := bbase (se 5 (by rfl) ⟨175286, by rfl⟩ : syracuseStep 3739445 = 350573) (by norm_num)
theorem B3370805 : Blo 1661530 3370805 := bbase (se 5 (by rfl) ⟨158006, by rfl⟩ : syracuseStep 3370805 = 316013) (by norm_num)
theorem B2494277 : Blo 1661530 2494277 := bbase (se 4 (by rfl) ⟨233838, by rfl⟩ : syracuseStep 2494277 = 467677) (by norm_num)
theorem B2494301 : Blo 1661530 2494301 := bbase (se 3 (by rfl) ⟨467681, by rfl⟩ : syracuseStep 2494301 = 935363) (by norm_num)
theorem B2494325 : Blo 1661530 2494325 := bbase (se 5 (by rfl) ⟨116921, by rfl⟩ : syracuseStep 2494325 = 233843) (by norm_num)
theorem B3739517 : Blo 1661530 3739517 := bbase (se 3 (by rfl) ⟨701159, by rfl⟩ : syracuseStep 3739517 = 1402319) (by norm_num)
theorem B2805637 : Blo 1661530 2805637 := bbase (se 4 (by rfl) ⟨263028, by rfl⟩ : syracuseStep 2805637 = 526057) (by norm_num)
theorem B2494349 : Blo 1661530 2494349 := bbase (se 3 (by rfl) ⟨467690, by rfl⟩ : syracuseStep 2494349 = 935381) (by norm_num)
theorem B2494373 : Blo 1661530 2494373 := bbase (se 4 (by rfl) ⟨233847, by rfl⟩ : syracuseStep 2494373 = 467695) (by norm_num)
theorem B2494397 : Blo 1661530 2494397 := bbase (se 3 (by rfl) ⟨467699, by rfl⟩ : syracuseStep 2494397 = 935399) (by norm_num)
theorem B3739589 : Blo 1661530 3739589 := bbase (se 4 (by rfl) ⟨350586, by rfl⟩ : syracuseStep 3739589 = 701173) (by norm_num)
theorem B21295061 : Blo 1661530 21295061 := bbase (se 7 (by rfl) ⟨249551, by rfl⟩ : syracuseStep 21295061 = 499103) (by norm_num)
theorem B2494421 : Blo 1661530 2494421 := bbase (se 7 (by rfl) ⟨29231, by rfl⟩ : syracuseStep 2494421 = 58463) (by norm_num)
theorem B3993565 : Blo 1661530 3993565 := bbase (se 3 (by rfl) ⟨748793, by rfl⟩ : syracuseStep 3993565 = 1497587) (by norm_num)
theorem B2805725 : Blo 1661530 2805725 := bbase (se 3 (by rfl) ⟨526073, by rfl⟩ : syracuseStep 2805725 = 1052147) (by norm_num)
theorem B2494445 : Blo 1661530 2494445 := bbase (se 3 (by rfl) ⟨467708, by rfl⟩ : syracuseStep 2494445 = 935417) (by norm_num)
theorem B2494469 : Blo 1661530 2494469 := bbase (se 4 (by rfl) ⟨233856, by rfl⟩ : syracuseStep 2494469 = 467713) (by norm_num)
theorem B3739661 : Blo 1661530 3739661 := bbase (se 3 (by rfl) ⟨701186, by rfl⟩ : syracuseStep 3739661 = 1402373) (by norm_num)
theorem B4206613 : Blo 1661530 4206613 := bbase (se 6 (by rfl) ⟨98592, by rfl⟩ : syracuseStep 4206613 = 197185) (by norm_num)
theorem B2494493 : Blo 1661530 2494493 := bbase (se 3 (by rfl) ⟨467717, by rfl⟩ : syracuseStep 2494493 = 935435) (by norm_num)
theorem B2494517 : Blo 1661530 2494517 := bbase (se 5 (by rfl) ⟨116930, by rfl⟩ : syracuseStep 2494517 = 233861) (by norm_num)
theorem B2494541 : Blo 1661530 2494541 := bbase (se 3 (by rfl) ⟨467726, by rfl⟩ : syracuseStep 2494541 = 935453) (by norm_num)
theorem B3739733 : Blo 1661530 3739733 := bbase (se 8 (by rfl) ⟨21912, by rfl⟩ : syracuseStep 3739733 = 43825) (by norm_num)
theorem B2805853 : Blo 1661530 2805853 := bbase (se 3 (by rfl) ⟨526097, by rfl⟩ : syracuseStep 2805853 = 1052195) (by norm_num)
theorem B4206725 : Blo 1661530 4206725 := bbase (se 4 (by rfl) ⟨394380, by rfl⟩ : syracuseStep 4206725 = 788761) (by norm_num)
theorem B3551381 : Blo 1661530 3551381 := bbase (se 6 (by rfl) ⟨83235, by rfl⟩ : syracuseStep 3551381 = 166471) (by norm_num)
theorem B3739805 : Blo 1661530 3739805 := bbase (se 3 (by rfl) ⟨701213, by rfl⟩ : syracuseStep 3739805 = 1402427) (by norm_num)
theorem B4796581 : Blo 1661530 4796581 := bbase (se 4 (by rfl) ⟨449679, by rfl⟩ : syracuseStep 4796581 = 899359) (by norm_num)
theorem B2805941 : Blo 1661530 2805941 := bbase (se 5 (by rfl) ⟨131528, by rfl⟩ : syracuseStep 2805941 = 263057) (by norm_num)
theorem B3739877 : Blo 1661530 3739877 := bbase (se 4 (by rfl) ⟨350613, by rfl⟩ : syracuseStep 3739877 = 701227) (by norm_num)
theorem B3551501 : Blo 1661530 3551501 := bbase (se 3 (by rfl) ⟨665906, by rfl⟩ : syracuseStep 3551501 = 1331813) (by norm_num)
theorem B3739949 : Blo 1661530 3739949 := bbase (se 3 (by rfl) ⟨701240, by rfl⟩ : syracuseStep 3739949 = 1402481) (by norm_num)
theorem B2806069 : Blo 1661530 2806069 := bbase (se 5 (by rfl) ⟨131534, by rfl⟩ : syracuseStep 2806069 = 263069) (by norm_num)
theorem B4206917 : Blo 1661530 4206917 := bbase (se 4 (by rfl) ⟨394398, by rfl⟩ : syracuseStep 4206917 = 788797) (by norm_num)
theorem B2527573 : Blo 1661530 2527573 := bbase (se 10 (by rfl) ⟨3702, by rfl⟩ : syracuseStep 2527573 = 7405) (by norm_num)
theorem B3740021 : Blo 1661530 3740021 := bbase (se 5 (by rfl) ⟨175313, by rfl⟩ : syracuseStep 3740021 = 350627) (by norm_num)
theorem B2527621 : Blo 1661530 2527621 := bbase (se 4 (by rfl) ⟨236964, by rfl⟩ : syracuseStep 2527621 = 473929) (by norm_num)
theorem B2806157 : Blo 1661530 2806157 := bbase (se 3 (by rfl) ⟨526154, by rfl⟩ : syracuseStep 2806157 = 1052309) (by norm_num)
theorem B5607845 : Blo 1661530 5607845 := bbase (se 4 (by rfl) ⟨525735, by rfl⟩ : syracuseStep 5607845 = 1051471) (by norm_num)
theorem B2699693 : Blo 1661530 2699693 := bbase (se 3 (by rfl) ⟨506192, by rfl⟩ : syracuseStep 2699693 = 1012385) (by norm_num)
theorem B3740093 : Blo 1661530 3740093 := bbase (se 3 (by rfl) ⟨701267, by rfl⟩ : syracuseStep 3740093 = 1402535) (by norm_num)
theorem B2994661 : Blo 1661530 2994661 := bbase (se 4 (by rfl) ⟨280749, by rfl⟩ : syracuseStep 2994661 = 561499) (by norm_num)
theorem B3740165 : Blo 1661530 3740165 := bbase (se 4 (by rfl) ⟨350640, by rfl⟩ : syracuseStep 3740165 = 701281) (by norm_num)
theorem B2806285 : Blo 1661530 2806285 := bbase (se 3 (by rfl) ⟨526178, by rfl⟩ : syracuseStep 2806285 = 1052357) (by norm_num)
theorem B3994181 : Blo 1661530 3994181 := bbase (se 4 (by rfl) ⟨374454, by rfl⟩ : syracuseStep 3994181 = 748909) (by norm_num)
theorem B3740237 : Blo 1661530 3740237 := bbase (se 3 (by rfl) ⟨701294, by rfl⟩ : syracuseStep 3740237 = 1402589) (by norm_num)
theorem B4264541 : Blo 1661530 4264541 := bbase (se 3 (by rfl) ⟨799601, by rfl⟩ : syracuseStep 4264541 = 1599203) (by norm_num)
theorem B6075013 : Blo 1661530 6075013 := bbase (se 4 (by rfl) ⟨569532, by rfl⟩ : syracuseStep 6075013 = 1139065) (by norm_num)
theorem B3740309 : Blo 1661530 3740309 := bbase (se 6 (by rfl) ⟨87663, by rfl⟩ : syracuseStep 3740309 = 175327) (by norm_num)
theorem B4207261 : Blo 1661530 4207261 := bbase (se 3 (by rfl) ⟨788861, by rfl⟩ : syracuseStep 4207261 = 1577723) (by norm_num)
theorem B4494005 : Blo 1661530 4494005 := bbase (se 5 (by rfl) ⟨210656, by rfl⟩ : syracuseStep 4494005 = 421313) (by norm_num)
theorem B4264645 : Blo 1661530 4264645 := bbase (se 4 (by rfl) ⟨399810, by rfl⟩ : syracuseStep 4264645 = 799621) (by norm_num)
theorem B2527957 : Blo 1661530 2527957 := bbase (se 7 (by rfl) ⟨29624, by rfl⟩ : syracuseStep 2527957 = 59249) (by norm_num)
theorem B8418005 : Blo 1661530 8418005 := bbase (se 7 (by rfl) ⟨98648, by rfl⟩ : syracuseStep 8418005 = 197297) (by norm_num)
theorem B3740381 : Blo 1661530 3740381 := bbase (se 3 (by rfl) ⟨701321, by rfl⟩ : syracuseStep 3740381 = 1402643) (by norm_num)
theorem B4207373 : Blo 1661530 4207373 := bbase (se 3 (by rfl) ⟨788882, by rfl⟩ : syracuseStep 4207373 = 1577765) (by norm_num)
theorem B3994381 : Blo 1661530 3994381 := bbase (se 3 (by rfl) ⟨748946, by rfl⟩ : syracuseStep 3994381 = 1497893) (by norm_num)
theorem B3740453 : Blo 1661530 3740453 := bbase (se 4 (by rfl) ⟨350667, by rfl⟩ : syracuseStep 3740453 = 701335) (by norm_num)
theorem B5608277 : Blo 1661530 5608277 := bbase (se 9 (by rfl) ⟨16430, by rfl⟩ : syracuseStep 5608277 = 32861) (by norm_num)
theorem B3740525 : Blo 1661530 3740525 := bbase (se 3 (by rfl) ⟨701348, by rfl⟩ : syracuseStep 3740525 = 1402697) (by norm_num)
theorem B2700157 : Blo 1661530 2700157 := bbase (se 3 (by rfl) ⟨506279, by rfl⟩ : syracuseStep 2700157 = 1012559) (by norm_num)
theorem B10646453 : Blo 1661530 10646453 := bbase (se 5 (by rfl) ⟨499052, by rfl⟩ : syracuseStep 10646453 = 998105) (by norm_num)
theorem B3740597 : Blo 1661530 3740597 := bbase (se 5 (by rfl) ⟨175340, by rfl⟩ : syracuseStep 3740597 = 350681) (by norm_num)
theorem B4207565 : Blo 1661530 4207565 := bbase (se 3 (by rfl) ⟨788918, by rfl⟩ : syracuseStep 4207565 = 1577837) (by norm_num)
theorem B3789821 : Blo 1661530 3789821 := bbase (se 3 (by rfl) ⟨710591, by rfl⟩ : syracuseStep 3789821 = 1421183) (by norm_num)
theorem B3740669 : Blo 1661530 3740669 := bbase (se 3 (by rfl) ⟨701375, by rfl⟩ : syracuseStep 3740669 = 1402751) (by norm_num)
theorem B1774597 : Blo 1661530 1774597 := bbase (se 4 (by rfl) ⟨166368, by rfl⟩ : syracuseStep 1774597 = 332737) (by norm_num)
theorem B7099397 : Blo 1661530 7099397 := bbase (se 4 (by rfl) ⟨665568, by rfl⟩ : syracuseStep 7099397 = 1331137) (by norm_num)
theorem B1774657 : Blo 1661530 1774657 := bbase (se 2 (by rfl) ⟨665496, by rfl⟩ : syracuseStep 1774657 = 1330993) (by norm_num)
theorem B3740741 : Blo 1661530 3740741 := bbase (se 4 (by rfl) ⟨350694, by rfl⟩ : syracuseStep 3740741 = 701389) (by norm_num)
theorem B3740813 : Blo 1661530 3740813 := bbase (se 3 (by rfl) ⟨701402, by rfl⟩ : syracuseStep 3740813 = 1402805) (by norm_num)
theorem B3740885 : Blo 1661530 3740885 := bbase (se 7 (by rfl) ⟨43838, by rfl⟩ : syracuseStep 3740885 = 87677) (by norm_num)
theorem B5608709 : Blo 1661530 5608709 := bbase (se 4 (by rfl) ⟨525816, by rfl⟩ : syracuseStep 5608709 = 1051633) (by norm_num)
theorem B2995469 : Blo 1661530 2995469 := bbase (se 3 (by rfl) ⟨561650, by rfl⟩ : syracuseStep 2995469 = 1123301) (by norm_num)
theorem B3740957 : Blo 1661530 3740957 := bbase (se 3 (by rfl) ⟨701429, by rfl⟩ : syracuseStep 3740957 = 1402859) (by norm_num)
theorem B4207909 : Blo 1661530 4207909 := bbase (se 4 (by rfl) ⟨394491, by rfl⟩ : syracuseStep 4207909 = 788983) (by norm_num)
theorem B1996105 : Blo 1661530 1996105 := bbase (se 2 (by rfl) ⟨748539, by rfl⟩ : syracuseStep 1996105 = 1497079) (by norm_num)
theorem B1996133 : Blo 1661530 1996133 := bbase (se 4 (by rfl) ⟨187137, by rfl⟩ : syracuseStep 1996133 = 374275) (by norm_num)
theorem B3741029 : Blo 1661530 3741029 := bbase (se 4 (by rfl) ⟨350721, by rfl⟩ : syracuseStep 3741029 = 701443) (by norm_num)
theorem B1774973 : Blo 1661530 1774973 := bbase (se 3 (by rfl) ⟨332807, by rfl⟩ : syracuseStep 1774973 = 665615) (by norm_num)
theorem B4208021 : Blo 1661530 4208021 := bbase (se 6 (by rfl) ⟨98625, by rfl⟩ : syracuseStep 4208021 = 197251) (by norm_num)
theorem B3741101 : Blo 1661530 3741101 := bbase (se 3 (by rfl) ⟨701456, by rfl⟩ : syracuseStep 3741101 = 1402913) (by norm_num)
theorem B3741173 : Blo 1661530 3741173 := bbase (se 5 (by rfl) ⟨175367, by rfl⟩ : syracuseStep 3741173 = 350735) (by norm_num)
theorem B3995189 : Blo 1661530 3995189 := bbase (se 5 (by rfl) ⟨187274, by rfl⟩ : syracuseStep 3995189 = 374549) (by norm_num)
theorem B3741245 : Blo 1661530 3741245 := bbase (se 3 (by rfl) ⟨701483, by rfl⟩ : syracuseStep 3741245 = 1402967) (by norm_num)
theorem B3790405 : Blo 1661530 3790405 := bbase (se 4 (by rfl) ⟨355350, by rfl⟩ : syracuseStep 3790405 = 710701) (by norm_num)
theorem B4208213 : Blo 1661530 4208213 := bbase (se 8 (by rfl) ⟨24657, by rfl⟩ : syracuseStep 4208213 = 49315) (by norm_num)
theorem B2102917 : Blo 1661530 2102917 := bbase (se 4 (by rfl) ⟨197148, by rfl⟩ : syracuseStep 2102917 = 394297) (by norm_num)
theorem B3741317 : Blo 1661530 3741317 := bbase (se 4 (by rfl) ⟨350748, by rfl⟩ : syracuseStep 3741317 = 701497) (by norm_num)
theorem B5609141 : Blo 1661530 5609141 := bbase (se 5 (by rfl) ⟨262928, by rfl⟩ : syracuseStep 5609141 = 525857) (by norm_num)
theorem B3741389 : Blo 1661530 3741389 := bbase (se 3 (by rfl) ⟨701510, by rfl⟩ : syracuseStep 3741389 = 1403021) (by norm_num)
theorem B2103013 : Blo 1661530 2103013 := bbase (se 4 (by rfl) ⟨197157, by rfl⟩ : syracuseStep 2103013 = 394315) (by norm_num)
theorem B6313733 : Blo 1661530 6313733 := bbase (se 4 (by rfl) ⟨591912, by rfl⟩ : syracuseStep 6313733 = 1183825) (by norm_num)
theorem B3741461 : Blo 1661530 3741461 := bbase (se 6 (by rfl) ⟨87690, by rfl⟩ : syracuseStep 3741461 = 175381) (by norm_num)
theorem B1775417 : Blo 1661530 1775417 := bbase (se 2 (by rfl) ⟨665781, by rfl⟩ : syracuseStep 1775417 = 1331563) (by norm_num)
theorem B1996633 : Blo 1661530 1996633 := bbase (se 2 (by rfl) ⟨748737, by rfl⟩ : syracuseStep 1996633 = 1497475) (by norm_num)
theorem B3741533 : Blo 1661530 3741533 := bbase (se 3 (by rfl) ⟨701537, by rfl⟩ : syracuseStep 3741533 = 1403075) (by norm_num)
theorem B1775477 : Blo 1661530 1775477 := bbase (se 5 (by rfl) ⟨83225, by rfl⟩ : syracuseStep 1775477 = 166451) (by norm_num)
theorem B4732805 : Blo 1661530 4732805 := bbase (se 4 (by rfl) ⟨443700, by rfl⟩ : syracuseStep 4732805 = 887401) (by norm_num)
theorem B1800073 : Blo 1661530 1800073 := bbase (se 2 (by rfl) ⟨675027, by rfl⟩ : syracuseStep 1800073 = 1350055) (by norm_num)
theorem B2103185 : Blo 1661530 2103185 := bbase (se 2 (by rfl) ⟨788694, by rfl⟩ : syracuseStep 2103185 = 1577389) (by norm_num)
theorem B3741605 : Blo 1661530 3741605 := bbase (se 4 (by rfl) ⟨350775, by rfl⟩ : syracuseStep 3741605 = 701551) (by norm_num)
theorem B4208557 : Blo 1661530 4208557 := bbase (se 3 (by rfl) ⟨789104, by rfl⟩ : syracuseStep 4208557 = 1578209) (by norm_num)
theorem B2103241 : Blo 1661530 2103241 := bbase (se 2 (by rfl) ⟨788715, by rfl⟩ : syracuseStep 2103241 = 1577431) (by norm_num)
theorem B3741677 : Blo 1661530 3741677 := bbase (se 3 (by rfl) ⟨701564, by rfl⟩ : syracuseStep 3741677 = 1403129) (by norm_num)
theorem B7100405 : Blo 1661530 7100405 := bbase (se 5 (by rfl) ⟨332831, by rfl⟩ : syracuseStep 7100405 = 665663) (by norm_num)
theorem B1775605 : Blo 1661530 1775605 := bbase (se 5 (by rfl) ⟨83231, by rfl⟩ : syracuseStep 1775605 = 166463) (by norm_num)
theorem B4208669 : Blo 1661530 4208669 := bbase (se 3 (by rfl) ⟨789125, by rfl⟩ : syracuseStep 4208669 = 1578251) (by norm_num)
theorem B6314021 : Blo 1661530 6314021 := bbase (se 4 (by rfl) ⟨591939, by rfl⟩ : syracuseStep 6314021 = 1183879) (by norm_num)
theorem B2103337 : Blo 1661530 2103337 := bbase (se 2 (by rfl) ⟨788751, by rfl⟩ : syracuseStep 2103337 = 1577503) (by norm_num)
theorem B3741749 : Blo 1661530 3741749 := bbase (se 5 (by rfl) ⟨175394, by rfl⟩ : syracuseStep 3741749 = 350789) (by norm_num)
theorem B6486085 : Blo 1661530 6486085 := bbase (se 4 (by rfl) ⟨608070, by rfl⟩ : syracuseStep 6486085 = 1216141) (by norm_num)
theorem B5609573 : Blo 1661530 5609573 := bbase (se 4 (by rfl) ⟨525897, by rfl⟩ : syracuseStep 5609573 = 1051795) (by norm_num)
theorem B2103509 : Blo 1661530 2103509 := bbase (se 7 (by rfl) ⟨24650, by rfl⟩ : syracuseStep 2103509 = 49301) (by norm_num)
theorem B4208861 : Blo 1661530 4208861 := bbase (se 3 (by rfl) ⟨789161, by rfl⟩ : syracuseStep 4208861 = 1578323) (by norm_num)
theorem B2103565 : Blo 1661530 2103565 := bbase (se 3 (by rfl) ⟨394418, by rfl⟩ : syracuseStep 2103565 = 788837) (by norm_num)
theorem B14194997 : Blo 1661530 14194997 := bbase (se 5 (by rfl) ⟨665390, by rfl⟩ : syracuseStep 14194997 = 1330781) (by norm_num)
theorem B2103661 : Blo 1661530 2103661 := bbase (se 3 (by rfl) ⟨394436, by rfl⟩ : syracuseStep 2103661 = 788873) (by norm_num)
theorem B8411525 : Blo 1661530 8411525 := bbase (se 4 (by rfl) ⟨788580, by rfl⟩ : syracuseStep 8411525 = 1577161) (by norm_num)
theorem B4323797 : Blo 1661530 4323797 := bbase (se 7 (by rfl) ⟨50669, by rfl⟩ : syracuseStep 4323797 = 101339) (by norm_num)
theorem B5610005 : Blo 1661530 5610005 := bbase (se 6 (by rfl) ⟨131484, by rfl⟩ : syracuseStep 5610005 = 262969) (by norm_num)
theorem B2103833 : Blo 1661530 2103833 := bbase (se 2 (by rfl) ⟨788937, by rfl⟩ : syracuseStep 2103833 = 1577875) (by norm_num)
theorem B4209205 : Blo 1661530 4209205 := bbase (se 5 (by rfl) ⟨197306, by rfl⟩ : syracuseStep 4209205 = 394613) (by norm_num)
theorem B2103889 : Blo 1661530 2103889 := bbase (se 2 (by rfl) ⟨788958, by rfl⟩ : syracuseStep 2103889 = 1577917) (by norm_num)
theorem B2366101 : Blo 1661530 2366101 := bbase (se 6 (by rfl) ⟨55455, by rfl⟩ : syracuseStep 2366101 = 110911) (by norm_num)
theorem B4209317 : Blo 1661530 4209317 := bbase (se 4 (by rfl) ⟨394623, by rfl⟩ : syracuseStep 4209317 = 789247) (by norm_num)
theorem B2103985 : Blo 1661530 2103985 := bbase (se 2 (by rfl) ⟨788994, by rfl⟩ : syracuseStep 2103985 = 1577989) (by norm_num)
theorem B2104157 : Blo 1661530 2104157 := bbase (se 3 (by rfl) ⟨394529, by rfl⟩ : syracuseStep 2104157 = 789059) (by norm_num)
theorem B4209509 : Blo 1661530 4209509 := bbase (se 4 (by rfl) ⟨394641, by rfl⟩ : syracuseStep 4209509 = 789283) (by norm_num)
theorem B5323637 : Blo 1661530 5323637 := bbase (se 5 (by rfl) ⟨249545, by rfl⟩ : syracuseStep 5323637 = 499091) (by norm_num)
theorem B3333005 : Blo 1661530 3333005 := bbase (se 3 (by rfl) ⟨624938, by rfl⟩ : syracuseStep 3333005 = 1249877) (by norm_num)
theorem B2104213 : Blo 1661530 2104213 := bbase (se 6 (by rfl) ⟨49317, by rfl⟩ : syracuseStep 2104213 = 98635) (by norm_num)
theorem B5610437 : Blo 1661530 5610437 := bbase (se 4 (by rfl) ⟨525978, by rfl⟩ : syracuseStep 5610437 = 1051957) (by norm_num)
theorem B20216789 : Blo 1661530 20216789 := bbase (se 7 (by rfl) ⟨236915, by rfl⟩ : syracuseStep 20216789 = 473831) (by norm_num)
theorem B2366437 : Blo 1661530 2366437 := bbase (se 4 (by rfl) ⟨221853, by rfl⟩ : syracuseStep 2366437 = 443707) (by norm_num)
theorem B2104309 : Blo 1661530 2104309 := bbase (se 5 (by rfl) ⟨98639, by rfl⟩ : syracuseStep 2104309 = 197279) (by norm_num)
theorem B1997821 : Blo 1661530 1997821 := bbase (se 3 (by rfl) ⟨374591, by rfl⟩ : syracuseStep 1997821 = 749183) (by norm_num)
theorem B8526869 : Blo 1661530 8526869 := bbase (se 6 (by rfl) ⟨199848, by rfl⟩ : syracuseStep 8526869 = 399697) (by norm_num)
theorem B2104481 : Blo 1661530 2104481 := bbase (se 2 (by rfl) ⟨789180, by rfl⟩ : syracuseStep 2104481 = 1578361) (by norm_num)
theorem B2366653 : Blo 1661530 2366653 := bbase (se 3 (by rfl) ⟨443747, by rfl⟩ : syracuseStep 2366653 = 887495) (by norm_num)
theorem B2104537 : Blo 1661530 2104537 := bbase (se 2 (by rfl) ⟨789201, by rfl⟩ : syracuseStep 2104537 = 1578403) (by norm_num)
theorem B2104633 : Blo 1661530 2104633 := bbase (se 2 (by rfl) ⟨789237, by rfl⟩ : syracuseStep 2104633 = 1578475) (by norm_num)
theorem B8985973 : Blo 1661530 8985973 := bbase (se 5 (by rfl) ⟨421217, by rfl⟩ : syracuseStep 8985973 = 842435) (by norm_num)
theorem B5610869 : Blo 1661530 5610869 := bbase (se 5 (by rfl) ⟨263009, by rfl⟩ : syracuseStep 5610869 = 526019) (by norm_num)
theorem B4734389 : Blo 1661530 4734389 := bbase (se 5 (by rfl) ⟨221924, by rfl⟩ : syracuseStep 4734389 = 443849) (by norm_num)
theorem B2367029 : Blo 1661530 2367029 := bbase (se 5 (by rfl) ⟨110954, by rfl⟩ : syracuseStep 2367029 = 221909) (by norm_num)
theorem B2080337 : Blo 1661530 2080337 := bbase (se 2 (by rfl) ⟨780126, by rfl⟩ : syracuseStep 2080337 = 1560253) (by norm_num)
theorem B8412821 : Blo 1661530 8412821 := bbase (se 6 (by rfl) ⟨197175, by rfl⟩ : syracuseStep 8412821 = 394351) (by norm_num)
theorem B7986917 : Blo 1661530 7986917 := bbase (se 4 (by rfl) ⟨748773, by rfl⟩ : syracuseStep 7986917 = 1497547) (by norm_num)
theorem B7102181 : Blo 1661530 7102181 := bbase (se 4 (by rfl) ⟨665829, by rfl⟩ : syracuseStep 7102181 = 1331659) (by norm_num)
theorem B5611301 : Blo 1661530 5611301 := bbase (se 4 (by rfl) ⟨526059, by rfl⟩ : syracuseStep 5611301 = 1052119) (by norm_num)
theorem B2662229 : Blo 1661530 2662229 := bbase (se 9 (by rfl) ⟨7799, by rfl⟩ : syracuseStep 2662229 = 15599) (by norm_num)
theorem B9723797 : Blo 1661530 9723797 := bbase (se 6 (by rfl) ⟨227901, by rfl⟩ : syracuseStep 9723797 = 455803) (by norm_num)
theorem B15974293 : Blo 1661530 15974293 := bbase (se 6 (by rfl) ⟨374397, by rfl⟩ : syracuseStep 15974293 = 748795) (by norm_num)
theorem B1662979 : Blo 1661530 1662979 := bstep (se 1 (by rfl) ⟨1247234, by rfl⟩ : syracuseStep 1662979 = 2494469) B2494469
theorem B1662995 : Blo 1661530 1662995 := bstep (se 1 (by rfl) ⟨1247246, by rfl⟩ : syracuseStep 1662995 = 2494493) B2494493
theorem B1663011 : Blo 1661530 1663011 := bstep (se 1 (by rfl) ⟨1247258, by rfl⟩ : syracuseStep 1663011 = 2494517) B2494517
theorem B1663027 : Blo 1661530 1663027 := bstep (se 1 (by rfl) ⟨1247270, by rfl⟩ : syracuseStep 1663027 = 2494541) B2494541
theorem B5324867 : Blo 1661530 5324867 := bstep (se 1 (by rfl) ⟨3993650, by rfl⟩ : syracuseStep 5324867 = 7987301) B7987301
theorem B2367587 : Blo 1661530 2367587 := bstep (se 1 (by rfl) ⟨1775690, by rfl⟩ : syracuseStep 2367587 = 3551381) B3551381
theorem B2367667 : Blo 1661530 2367667 := bstep (se 1 (by rfl) ⟨1775750, by rfl⟩ : syracuseStep 2367667 = 3551501) B3551501
theorem B4554947 : Blo 1661530 4554947 := bstep (se 1 (by rfl) ⟨3416210, by rfl⟩ : syracuseStep 4554947 = 6832421) B6832421
theorem B2662787 : Blo 1661530 2662787 := bstep (se 1 (by rfl) ⟨1997090, by rfl⟩ : syracuseStep 2662787 = 3994181) B3994181
theorem B2843027 : Blo 1661530 2843027 := bstep (se 1 (by rfl) ⟨2132270, by rfl⟩ : syracuseStep 2843027 = 4264541) B4264541
theorem B5611949 : Blo 1661530 5611949 := bstep (se 3 (by rfl) ⟨1052240, by rfl⟩ : syracuseStep 5611949 = 2104481) B2104481
theorem B5612003 : Blo 1661530 5612003 := bstep (se 1 (by rfl) ⟨4209002, by rfl⟩ : syracuseStep 5612003 = 8418005) B8418005
theorem B17965637 : Blo 1661530 17965637 := bstep (se 4 (by rfl) ⟨1684278, by rfl⟩ : syracuseStep 17965637 = 3368557) B3368557
theorem B5612273 : Blo 1661530 5612273 := bstep (se 2 (by rfl) ⟨2104602, by rfl⟩ : syracuseStep 5612273 = 4209205) B4209205
theorem B23970613 : Blo 1661530 23970613 := bstep (se 5 (by rfl) ⟨1123622, by rfl⟩ : syracuseStep 23970613 = 2247245) B2247245
theorem B3154801 : Blo 1661530 3154801 := bstep (se 2 (by rfl) ⟨1183050, by rfl⟩ : syracuseStep 3154801 = 2366101) B2366101
theorem B5686193 : Blo 1661530 5686193 := bstep (se 2 (by rfl) ⟨2132322, by rfl⟩ : syracuseStep 5686193 = 4264645) B4264645
theorem B5055437 : Blo 1661530 5055437 := bstep (se 3 (by rfl) ⟨947894, by rfl⟩ : syracuseStep 5055437 = 1895789) B1895789
theorem B5325841 : Blo 1661530 5325841 := bstep (se 2 (by rfl) ⟨1997190, by rfl⟩ : syracuseStep 5325841 = 3994381) B3994381
theorem B2663459 : Blo 1661530 2663459 := bstep (se 1 (by rfl) ⟨1997594, by rfl⟩ : syracuseStep 2663459 = 3995189) B3995189
theorem B21292085 : Blo 1661530 21292085 := bstep (se 5 (by rfl) ⟨998066, by rfl⟩ : syracuseStep 21292085 = 1996133) B1996133
theorem B30327949 : Blo 1661530 30327949 := bstep (se 3 (by rfl) ⟨5686490, by rfl⟩ : syracuseStep 30327949 = 11372981) B11372981
theorem B5399693 : Blo 1661530 5399693 := bstep (se 3 (by rfl) ⟨1012442, by rfl⟩ : syracuseStep 5399693 = 2024885) B2024885
theorem B5989553 : Blo 1661530 5989553 := bstep (se 2 (by rfl) ⟨2246082, by rfl⟩ : syracuseStep 5989553 = 4492165) B4492165
theorem B11977955 : Blo 1661530 11977955 := bstep (se 1 (by rfl) ⟨8983466, by rfl⟩ : syracuseStep 11977955 = 17966933) B17966933
theorem B3155203 : Blo 1661530 3155203 := bstep (se 1 (by rfl) ⟨2366402, by rfl⟩ : syracuseStep 3155203 = 4732805) B4732805
theorem B3155249 : Blo 1661530 3155249 := bstep (se 2 (by rfl) ⟨1183218, by rfl⟩ : syracuseStep 3155249 = 2366437) B2366437
theorem B2663761 : Blo 1661530 2663761 := bstep (se 2 (by rfl) ⟨998910, by rfl⟩ : syracuseStep 2663761 = 1997821) B1997821
theorem B1869331 : Blo 1661530 1869331 := bstep (se 1 (by rfl) ⟨1401998, by rfl⟩ : syracuseStep 1869331 = 2803997) B2803997
theorem B9463331 : Blo 1661530 9463331 := bstep (se 1 (by rfl) ⟨7097498, by rfl⟩ : syracuseStep 9463331 = 14194997) B14194997
theorem B5547565 : Blo 1661530 5547565 := bstep (se 3 (by rfl) ⟨1040168, by rfl⟩ : syracuseStep 5547565 = 2080337) B2080337
theorem B3696209 : Blo 1661530 3696209 := bstep (se 2 (by rfl) ⟨1386078, by rfl⟩ : syracuseStep 3696209 = 2772157) B2772157
theorem B3155537 : Blo 1661530 3155537 := bstep (se 2 (by rfl) ⟨1183326, by rfl⟩ : syracuseStep 3155537 = 2366653) B2366653
theorem B25585265 : Blo 1661530 25585265 := bstep (se 2 (by rfl) ⟨9594474, by rfl⟩ : syracuseStep 25585265 = 19188949) B19188949
theorem B1869475 : Blo 1661530 1869475 := bstep (se 1 (by rfl) ⟨1402106, by rfl⟩ : syracuseStep 1869475 = 2804213) B2804213
theorem B2131747 : Blo 1661530 2131747 := bstep (se 1 (by rfl) ⟨1598810, by rfl⟩ : syracuseStep 2131747 = 3197621) B3197621
theorem B1869619 : Blo 1661530 1869619 := bstep (se 1 (by rfl) ⟨1402214, by rfl⟩ : syracuseStep 1869619 = 2804429) B2804429
theorem B28796725 : Blo 1661530 28796725 := bstep (se 5 (by rfl) ⟨1349846, by rfl⟩ : syracuseStep 28796725 = 2699693) B2699693
theorem B8415089 : Blo 1661530 8415089 := bstep (se 2 (by rfl) ⟨3155658, by rfl⟩ : syracuseStep 8415089 = 6311317) B6311317
theorem B2492321 : Blo 1661530 2492321 := bstep (se 2 (by rfl) ⟨934620, by rfl⟩ : syracuseStep 2492321 = 1869241) B1869241
theorem B3549091 : Blo 1661530 3549091 := bstep (se 1 (by rfl) ⟨2661818, by rfl⟩ : syracuseStep 3549091 = 5323637) B5323637
theorem B2492339 : Blo 1661530 2492339 := bstep (se 1 (by rfl) ⟨1869254, by rfl⟩ : syracuseStep 2492339 = 3738509) B3738509
theorem B2222003 : Blo 1661530 2222003 := bstep (se 1 (by rfl) ⟨1666502, by rfl⟩ : syracuseStep 2222003 = 3333005) B3333005
theorem B1869763 : Blo 1661530 1869763 := bstep (se 1 (by rfl) ⟨1402322, by rfl⟩ : syracuseStep 1869763 = 2804645) B2804645
theorem B2492369 : Blo 1661530 2492369 := bstep (se 2 (by rfl) ⟨934638, by rfl⟩ : syracuseStep 2492369 = 1869277) B1869277
theorem B2492387 : Blo 1661530 2492387 := bstep (se 1 (by rfl) ⟨1869290, by rfl⟩ : syracuseStep 2492387 = 3738581) B3738581
theorem B6309859 : Blo 1661530 6309859 := bstep (se 1 (by rfl) ⟨4732394, by rfl⟩ : syracuseStep 6309859 = 9464789) B9464789
theorem B13477859 : Blo 1661530 13477859 := bstep (se 1 (by rfl) ⟨10108394, by rfl⟩ : syracuseStep 13477859 = 20216789) B20216789
theorem B2492417 : Blo 1661530 2492417 := bstep (se 2 (by rfl) ⟨934656, by rfl⟩ : syracuseStep 2492417 = 1869313) B1869313
theorem B2492435 : Blo 1661530 2492435 := bstep (se 1 (by rfl) ⟨1869326, by rfl⟩ : syracuseStep 2492435 = 3738653) B3738653
theorem B2492465 : Blo 1661530 2492465 := bstep (se 2 (by rfl) ⟨934674, by rfl⟩ : syracuseStep 2492465 = 1869349) B1869349
theorem B2492483 : Blo 1661530 2492483 := bstep (se 1 (by rfl) ⟨1869362, by rfl⟩ : syracuseStep 2492483 = 3738725) B3738725
theorem B1869907 : Blo 1661530 1869907 := bstep (se 1 (by rfl) ⟨1402430, by rfl⟩ : syracuseStep 1869907 = 2804861) B2804861
theorem B2492513 : Blo 1661530 2492513 := bstep (se 2 (by rfl) ⟨934692, by rfl⟩ : syracuseStep 2492513 = 1869385) B1869385
theorem B4491377 : Blo 1661530 4491377 := bstep (se 2 (by rfl) ⟨1684266, by rfl⟩ : syracuseStep 4491377 = 3368533) B3368533
theorem B2492531 : Blo 1661530 2492531 := bstep (se 1 (by rfl) ⟨1869398, by rfl⟩ : syracuseStep 2492531 = 3738797) B3738797
theorem B2492561 : Blo 1661530 2492561 := bstep (se 2 (by rfl) ⟨934710, by rfl⟩ : syracuseStep 2492561 = 1869421) B1869421
theorem B2492579 : Blo 1661530 2492579 := bstep (se 1 (by rfl) ⟨1869434, by rfl⟩ : syracuseStep 2492579 = 3738869) B3738869
theorem B2803889 : Blo 1661530 2803889 := bstep (se 2 (by rfl) ⟨1051458, by rfl⟩ : syracuseStep 2803889 = 2102917) B2102917
theorem B2492609 : Blo 1661530 2492609 := bstep (se 2 (by rfl) ⟨934728, by rfl⟩ : syracuseStep 2492609 = 1869457) B1869457
theorem B2492627 : Blo 1661530 2492627 := bstep (se 1 (by rfl) ⟨1869470, by rfl⟩ : syracuseStep 2492627 = 3738941) B3738941
theorem B1870051 : Blo 1661530 1870051 := bstep (se 1 (by rfl) ⟨1402538, by rfl⟩ : syracuseStep 1870051 = 2805077) B2805077
theorem B5687533 : Blo 1661530 5687533 := bstep (se 3 (by rfl) ⟨1066412, by rfl⟩ : syracuseStep 5687533 = 2132825) B2132825
theorem B2492657 : Blo 1661530 2492657 := bstep (se 2 (by rfl) ⟨934746, by rfl⟩ : syracuseStep 2492657 = 1869493) B1869493
theorem B2492675 : Blo 1661530 2492675 := bstep (se 1 (by rfl) ⟨1869506, by rfl⟩ : syracuseStep 2492675 = 3739013) B3739013
theorem B2492705 : Blo 1661530 2492705 := bstep (se 2 (by rfl) ⟨934764, by rfl⟩ : syracuseStep 2492705 = 1869529) B1869529
theorem B3156259 : Blo 1661530 3156259 := bstep (se 1 (by rfl) ⟨2367194, by rfl⟩ : syracuseStep 3156259 = 4734389) B4734389
theorem B2804017 : Blo 1661530 2804017 := bstep (se 2 (by rfl) ⟨1051506, by rfl⟩ : syracuseStep 2804017 = 2103013) B2103013
theorem B2492723 : Blo 1661530 2492723 := bstep (se 1 (by rfl) ⟨1869542, by rfl⟩ : syracuseStep 2492723 = 3739085) B3739085
theorem B2492753 : Blo 1661530 2492753 := bstep (se 2 (by rfl) ⟨934782, by rfl⟩ : syracuseStep 2492753 = 1869565) B1869565
theorem B2804051 : Blo 1661530 2804051 := bstep (se 1 (by rfl) ⟨2103038, by rfl⟩ : syracuseStep 2804051 = 4206077) B4206077
theorem B2492771 : Blo 1661530 2492771 := bstep (se 1 (by rfl) ⟨1869578, by rfl⟩ : syracuseStep 2492771 = 3739157) B3739157
theorem B1870195 : Blo 1661530 1870195 := bstep (se 1 (by rfl) ⟨1402646, by rfl⟩ : syracuseStep 1870195 = 2805293) B2805293
theorem B2492801 : Blo 1661530 2492801 := bstep (se 2 (by rfl) ⟨934800, by rfl⟩ : syracuseStep 2492801 = 1869601) B1869601
theorem B2492819 : Blo 1661530 2492819 := bstep (se 1 (by rfl) ⟨1869614, by rfl⟩ : syracuseStep 2492819 = 3739229) B3739229
theorem B2492849 : Blo 1661530 2492849 := bstep (se 2 (by rfl) ⟨934818, by rfl⟩ : syracuseStep 2492849 = 1869637) B1869637
theorem B2492867 : Blo 1661530 2492867 := bstep (se 1 (by rfl) ⟨1869650, by rfl⟩ : syracuseStep 2492867 = 3739301) B3739301
theorem B6752717 : Blo 1661530 6752717 := bstep (se 3 (by rfl) ⟨1266134, by rfl⟩ : syracuseStep 6752717 = 2532269) B2532269
theorem B2804179 : Blo 1661530 2804179 := bstep (se 1 (by rfl) ⟨2103134, by rfl⟩ : syracuseStep 2804179 = 4206269) B4206269
theorem B2492897 : Blo 1661530 2492897 := bstep (se 2 (by rfl) ⟨934836, by rfl⟩ : syracuseStep 2492897 = 1869673) B1869673
theorem B2492915 : Blo 1661530 2492915 := bstep (se 1 (by rfl) ⟨1869686, by rfl⟩ : syracuseStep 2492915 = 3739373) B3739373
theorem B1870339 : Blo 1661530 1870339 := bstep (se 1 (by rfl) ⟨1402754, by rfl⟩ : syracuseStep 1870339 = 2805509) B2805509
theorem B2492945 : Blo 1661530 2492945 := bstep (se 2 (by rfl) ⟨934854, by rfl⟩ : syracuseStep 2492945 = 1869709) B1869709
theorem B2492963 : Blo 1661530 2492963 := bstep (se 1 (by rfl) ⟨1869722, by rfl⟩ : syracuseStep 2492963 = 3739445) B3739445
theorem B2247203 : Blo 1661530 2247203 := bstep (se 1 (by rfl) ⟨1685402, by rfl⟩ : syracuseStep 2247203 = 3370805) B3370805
theorem B2492993 : Blo 1661530 2492993 := bstep (se 2 (by rfl) ⟨934872, by rfl⟩ : syracuseStep 2492993 = 1869745) B1869745
theorem B2493011 : Blo 1661530 2493011 := bstep (se 1 (by rfl) ⟨1869758, by rfl⟩ : syracuseStep 2493011 = 3739517) B3739517
theorem B2804321 : Blo 1661530 2804321 := bstep (se 2 (by rfl) ⟨1051620, by rfl⟩ : syracuseStep 2804321 = 2103241) B2103241
theorem B6482531 : Blo 1661530 6482531 := bstep (se 1 (by rfl) ⟨4861898, by rfl⟩ : syracuseStep 6482531 = 9723797) B9723797
theorem B2493041 : Blo 1661530 2493041 := bstep (se 2 (by rfl) ⟨934890, by rfl⟩ : syracuseStep 2493041 = 1869781) B1869781
theorem B2493059 : Blo 1661530 2493059 := bstep (se 1 (by rfl) ⟨1869794, by rfl⟩ : syracuseStep 2493059 = 3739589) B3739589
theorem B1870483 : Blo 1661530 1870483 := bstep (se 1 (by rfl) ⟨1402862, by rfl⟩ : syracuseStep 1870483 = 2805725) B2805725
theorem B2493089 : Blo 1661530 2493089 := bstep (se 2 (by rfl) ⟨934908, by rfl⟩ : syracuseStep 2493089 = 1869817) B1869817
theorem B2493107 : Blo 1661530 2493107 := bstep (se 1 (by rfl) ⟨1869830, by rfl⟩ : syracuseStep 2493107 = 3739661) B3739661
theorem B2493137 : Blo 1661530 2493137 := bstep (se 2 (by rfl) ⟨934926, by rfl⟩ : syracuseStep 2493137 = 1869853) B1869853
theorem B2804449 : Blo 1661530 2804449 := bstep (se 2 (by rfl) ⟨1051668, by rfl⟩ : syracuseStep 2804449 = 2103337) B2103337
theorem B2493155 : Blo 1661530 2493155 := bstep (se 1 (by rfl) ⟨1869866, by rfl⟩ : syracuseStep 2493155 = 3739733) B3739733
theorem B3156707 : Blo 1661530 3156707 := bstep (se 1 (by rfl) ⟨2367530, by rfl⟩ : syracuseStep 3156707 = 4735061) B4735061
theorem B2493185 : Blo 1661530 2493185 := bstep (se 2 (by rfl) ⟨934944, by rfl⟩ : syracuseStep 2493185 = 1869889) B1869889
theorem B2804483 : Blo 1661530 2804483 := bstep (se 1 (by rfl) ⟨2103362, by rfl⟩ : syracuseStep 2804483 = 4206725) B4206725
theorem B11373317 : Blo 1661530 11373317 := bstep (se 4 (by rfl) ⟨1066248, by rfl⟩ : syracuseStep 11373317 = 2132497) B2132497
theorem B2493203 : Blo 1661530 2493203 := bstep (se 1 (by rfl) ⟨1869902, by rfl⟩ : syracuseStep 2493203 = 3739805) B3739805
theorem B53922581 : Blo 1661530 53922581 := bstep (se 6 (by rfl) ⟨1263810, by rfl⟩ : syracuseStep 53922581 = 2527621) B2527621
theorem B1870627 : Blo 1661530 1870627 := bstep (se 1 (by rfl) ⟨1402970, by rfl⟩ : syracuseStep 1870627 = 2805941) B2805941
theorem B2493233 : Blo 1661530 2493233 := bstep (se 2 (by rfl) ⟨934962, by rfl⟩ : syracuseStep 2493233 = 1869925) B1869925
theorem B2493251 : Blo 1661530 2493251 := bstep (se 1 (by rfl) ⟨1869938, by rfl⟩ : syracuseStep 2493251 = 3739877) B3739877
theorem B2493281 : Blo 1661530 2493281 := bstep (se 2 (by rfl) ⟨934980, by rfl⟩ : syracuseStep 2493281 = 1869961) B1869961
theorem B2493299 : Blo 1661530 2493299 := bstep (se 1 (by rfl) ⟨1869974, by rfl⟩ : syracuseStep 2493299 = 3739949) B3739949
theorem B2804611 : Blo 1661530 2804611 := bstep (se 1 (by rfl) ⟨2103458, by rfl⟩ : syracuseStep 2804611 = 4206917) B4206917
theorem B2493329 : Blo 1661530 2493329 := bstep (se 2 (by rfl) ⟨934998, by rfl⟩ : syracuseStep 2493329 = 1869997) B1869997
theorem B2493347 : Blo 1661530 2493347 := bstep (se 1 (by rfl) ⟨1870010, by rfl⟩ : syracuseStep 2493347 = 3740021) B3740021
theorem B3738545 : Blo 1661530 3738545 := bstep (se 2 (by rfl) ⟨1401954, by rfl⟩ : syracuseStep 3738545 = 2803909) B2803909
theorem B1870771 : Blo 1661530 1870771 := bstep (se 1 (by rfl) ⟨1403078, by rfl⟩ : syracuseStep 1870771 = 2806157) B2806157
theorem B2493377 : Blo 1661530 2493377 := bstep (se 2 (by rfl) ⟨935016, by rfl⟩ : syracuseStep 2493377 = 1870033) B1870033
theorem B3738563 : Blo 1661530 3738563 := bstep (se 1 (by rfl) ⟨2803922, by rfl⟩ : syracuseStep 3738563 = 5607845) B5607845
theorem B2493395 : Blo 1661530 2493395 := bstep (se 1 (by rfl) ⟨1870046, by rfl⟩ : syracuseStep 2493395 = 3740093) B3740093
theorem B2493425 : Blo 1661530 2493425 := bstep (se 2 (by rfl) ⟨935034, by rfl⟩ : syracuseStep 2493425 = 1870069) B1870069
theorem B2493443 : Blo 1661530 2493443 := bstep (se 1 (by rfl) ⟨1870082, by rfl⟩ : syracuseStep 2493443 = 3740165) B3740165
theorem B3156995 : Blo 1661530 3156995 := bstep (se 1 (by rfl) ⟨2367746, by rfl⟩ : syracuseStep 3156995 = 4735493) B4735493
theorem B2804753 : Blo 1661530 2804753 := bstep (se 2 (by rfl) ⟨1051782, by rfl⟩ : syracuseStep 2804753 = 2103565) B2103565
theorem B2493473 : Blo 1661530 2493473 := bstep (se 2 (by rfl) ⟨935052, by rfl⟩ : syracuseStep 2493473 = 1870105) B1870105
theorem B2493491 : Blo 1661530 2493491 := bstep (se 1 (by rfl) ⟨1870118, by rfl⟩ : syracuseStep 2493491 = 3740237) B3740237
theorem B2493521 : Blo 1661530 2493521 := bstep (se 2 (by rfl) ⟨935070, by rfl⟩ : syracuseStep 2493521 = 1870141) B1870141
theorem B2493539 : Blo 1661530 2493539 := bstep (se 1 (by rfl) ⟨1870154, by rfl⟩ : syracuseStep 2493539 = 3740309) B3740309
theorem B3550321 : Blo 1661530 3550321 := bstep (se 2 (by rfl) ⟨1331370, by rfl⟩ : syracuseStep 3550321 = 2662741) B2662741
theorem B3370097 : Blo 1661530 3370097 := bstep (se 2 (by rfl) ⟨1263786, by rfl⟩ : syracuseStep 3370097 = 2527573) B2527573
theorem B2493569 : Blo 1661530 2493569 := bstep (se 2 (by rfl) ⟨935088, by rfl⟩ : syracuseStep 2493569 = 1870177) B1870177
theorem B2804881 : Blo 1661530 2804881 := bstep (se 2 (by rfl) ⟨1051830, by rfl⟩ : syracuseStep 2804881 = 2103661) B2103661
theorem B2493587 : Blo 1661530 2493587 := bstep (se 1 (by rfl) ⟨1870190, by rfl⟩ : syracuseStep 2493587 = 3740381) B3740381
theorem B2493617 : Blo 1661530 2493617 := bstep (se 2 (by rfl) ⟨935106, by rfl⟩ : syracuseStep 2493617 = 1870213) B1870213
theorem B2804915 : Blo 1661530 2804915 := bstep (se 1 (by rfl) ⟨2103686, by rfl⟩ : syracuseStep 2804915 = 4207373) B4207373
theorem B2493635 : Blo 1661530 2493635 := bstep (se 1 (by rfl) ⟨1870226, by rfl⟩ : syracuseStep 2493635 = 3740453) B3740453
theorem B3738833 : Blo 1661530 3738833 := bstep (se 2 (by rfl) ⟨1402062, by rfl⟩ : syracuseStep 3738833 = 2804125) B2804125
theorem B2493665 : Blo 1661530 2493665 := bstep (se 2 (by rfl) ⟨935124, by rfl⟩ : syracuseStep 2493665 = 1870249) B1870249
theorem B3738851 : Blo 1661530 3738851 := bstep (se 1 (by rfl) ⟨2804138, by rfl⟩ : syracuseStep 3738851 = 5608277) B5608277
theorem B2493683 : Blo 1661530 2493683 := bstep (se 1 (by rfl) ⟨1870262, by rfl⟩ : syracuseStep 2493683 = 3740525) B3740525
theorem B2493713 : Blo 1661530 2493713 := bstep (se 2 (by rfl) ⟨935142, by rfl⟩ : syracuseStep 2493713 = 1870285) B1870285
theorem B7097635 : Blo 1661530 7097635 := bstep (se 1 (by rfl) ⟨5323226, by rfl⟩ : syracuseStep 7097635 = 10646453) B10646453
theorem B2493731 : Blo 1661530 2493731 := bstep (se 1 (by rfl) ⟨1870298, by rfl⟩ : syracuseStep 2493731 = 3740597) B3740597
theorem B8416547 : Blo 1661530 8416547 := bstep (se 1 (by rfl) ⟨6312410, by rfl⟩ : syracuseStep 8416547 = 12624821) B12624821
theorem B2805043 : Blo 1661530 2805043 := bstep (se 1 (by rfl) ⟨2103782, by rfl⟩ : syracuseStep 2805043 = 4207565) B4207565
theorem B2493761 : Blo 1661530 2493761 := bstep (se 2 (by rfl) ⟨935160, by rfl⟩ : syracuseStep 2493761 = 1870321) B1870321
theorem B2526547 : Blo 1661530 2526547 := bstep (se 1 (by rfl) ⟨1894910, by rfl⟩ : syracuseStep 2526547 = 3789821) B3789821
theorem B2493779 : Blo 1661530 2493779 := bstep (se 1 (by rfl) ⟨1870334, by rfl⟩ : syracuseStep 2493779 = 3740669) B3740669
theorem B2493809 : Blo 1661530 2493809 := bstep (se 2 (by rfl) ⟨935178, by rfl⟩ : syracuseStep 2493809 = 1870357) B1870357
theorem B2493827 : Blo 1661530 2493827 := bstep (se 1 (by rfl) ⟨1870370, by rfl⟩ : syracuseStep 2493827 = 3740741) B3740741
theorem B2493857 : Blo 1661530 2493857 := bstep (se 2 (by rfl) ⟨935196, by rfl⟩ : syracuseStep 2493857 = 1870393) B1870393
theorem B2493875 : Blo 1661530 2493875 := bstep (se 1 (by rfl) ⟨1870406, by rfl⟩ : syracuseStep 2493875 = 3740813) B3740813
theorem B2805185 : Blo 1661530 2805185 := bstep (se 2 (by rfl) ⟨1051944, by rfl⟩ : syracuseStep 2805185 = 2103889) B2103889
theorem B2493905 : Blo 1661530 2493905 := bstep (se 2 (by rfl) ⟨935214, by rfl⟩ : syracuseStep 2493905 = 1870429) B1870429
theorem B2493923 : Blo 1661530 2493923 := bstep (se 1 (by rfl) ⟨1870442, by rfl⟩ : syracuseStep 2493923 = 3740885) B3740885
theorem B3739121 : Blo 1661530 3739121 := bstep (se 2 (by rfl) ⟨1402170, by rfl⟩ : syracuseStep 3739121 = 2804341) B2804341
theorem B2493953 : Blo 1661530 2493953 := bstep (se 2 (by rfl) ⟨935232, by rfl⟩ : syracuseStep 2493953 = 1870465) B1870465
theorem B3739139 : Blo 1661530 3739139 := bstep (se 1 (by rfl) ⟨2804354, by rfl⟩ : syracuseStep 3739139 = 5608709) B5608709
theorem B2493971 : Blo 1661530 2493971 := bstep (se 1 (by rfl) ⟨1870478, by rfl⟩ : syracuseStep 2493971 = 3740957) B3740957
theorem B2494001 : Blo 1661530 2494001 := bstep (se 2 (by rfl) ⟨935250, by rfl⟩ : syracuseStep 2494001 = 1870501) B1870501
theorem B2805313 : Blo 1661530 2805313 := bstep (se 2 (by rfl) ⟨1051992, by rfl⟩ : syracuseStep 2805313 = 2103985) B2103985
theorem B2494019 : Blo 1661530 2494019 := bstep (se 1 (by rfl) ⟨1870514, by rfl⟩ : syracuseStep 2494019 = 3741029) B3741029
theorem B2805347 : Blo 1661530 2805347 := bstep (se 1 (by rfl) ⟨2104010, by rfl⟩ : syracuseStep 2805347 = 4208021) B4208021
theorem B2494049 : Blo 1661530 2494049 := bstep (se 2 (by rfl) ⟨935268, by rfl⟩ : syracuseStep 2494049 = 1870537) B1870537
theorem B14200433 : Blo 1661530 14200433 := bstep (se 2 (by rfl) ⟨5325162, by rfl⟩ : syracuseStep 14200433 = 10650325) B10650325
theorem B3370609 : Blo 1661530 3370609 := bstep (se 2 (by rfl) ⟨1263978, by rfl⟩ : syracuseStep 3370609 = 2527957) B2527957
theorem B2494067 : Blo 1661530 2494067 := bstep (se 1 (by rfl) ⟨1870550, by rfl⟩ : syracuseStep 2494067 = 3741101) B3741101
theorem B2494097 : Blo 1661530 2494097 := bstep (se 2 (by rfl) ⟨935286, by rfl⟩ : syracuseStep 2494097 = 1870573) B1870573
theorem B2494115 : Blo 1661530 2494115 := bstep (se 1 (by rfl) ⟨1870586, by rfl⟩ : syracuseStep 2494115 = 3741173) B3741173
theorem B2494145 : Blo 1661530 2494145 := bstep (se 2 (by rfl) ⟨935304, by rfl⟩ : syracuseStep 2494145 = 1870609) B1870609
theorem B4206289 : Blo 1661530 4206289 := bstep (se 2 (by rfl) ⟨1577358, by rfl⟩ : syracuseStep 4206289 = 3154717) B3154717
theorem B2494163 : Blo 1661530 2494163 := bstep (se 1 (by rfl) ⟨1870622, by rfl⟩ : syracuseStep 2494163 = 3741245) B3741245
theorem B2805475 : Blo 1661530 2805475 := bstep (se 1 (by rfl) ⟨2104106, by rfl⟩ : syracuseStep 2805475 = 4208213) B4208213
theorem B2494193 : Blo 1661530 2494193 := bstep (se 2 (by rfl) ⟨935322, by rfl⟩ : syracuseStep 2494193 = 1870645) B1870645
theorem B2494211 : Blo 1661530 2494211 := bstep (se 1 (by rfl) ⟨1870658, by rfl⟩ : syracuseStep 2494211 = 3741317) B3741317
theorem B3739409 : Blo 1661530 3739409 := bstep (se 2 (by rfl) ⟨1402278, by rfl⟩ : syracuseStep 3739409 = 2804557) B2804557
theorem B2494241 : Blo 1661530 2494241 := bstep (se 2 (by rfl) ⟨935340, by rfl⟩ : syracuseStep 2494241 = 1870681) B1870681
theorem B3739427 : Blo 1661530 3739427 := bstep (se 1 (by rfl) ⟨2804570, by rfl⟩ : syracuseStep 3739427 = 5609141) B5609141
theorem B2494259 : Blo 1661530 2494259 := bstep (se 1 (by rfl) ⟨1870694, by rfl⟩ : syracuseStep 2494259 = 3741389) B3741389
theorem B2494289 : Blo 1661530 2494289 := bstep (se 2 (by rfl) ⟨935358, by rfl⟩ : syracuseStep 2494289 = 1870717) B1870717
theorem B3600209 : Blo 1661530 3600209 := bstep (se 2 (by rfl) ⟨1350078, by rfl⟩ : syracuseStep 3600209 = 2700157) B2700157
theorem B2494307 : Blo 1661530 2494307 := bstep (se 1 (by rfl) ⟨1870730, by rfl⟩ : syracuseStep 2494307 = 3741461) B3741461
theorem B2805617 : Blo 1661530 2805617 := bstep (se 2 (by rfl) ⟨1052106, by rfl⟩ : syracuseStep 2805617 = 2104213) B2104213
theorem B2494337 : Blo 1661530 2494337 := bstep (se 2 (by rfl) ⟨935376, by rfl⟩ : syracuseStep 2494337 = 1870753) B1870753
theorem B2494355 : Blo 1661530 2494355 := bstep (se 1 (by rfl) ⟨1870766, by rfl⟩ : syracuseStep 2494355 = 3741533) B3741533
theorem B2494385 : Blo 1661530 2494385 := bstep (se 2 (by rfl) ⟨935394, by rfl⟩ : syracuseStep 2494385 = 1870789) B1870789
theorem B2494403 : Blo 1661530 2494403 := bstep (se 1 (by rfl) ⟨1870802, by rfl⟩ : syracuseStep 2494403 = 3741605) B3741605
theorem B2494433 : Blo 1661530 2494433 := bstep (se 2 (by rfl) ⟨935412, by rfl⟩ : syracuseStep 2494433 = 1870825) B1870825
theorem B4206563 : Blo 1661530 4206563 := bstep (se 1 (by rfl) ⟨3154922, by rfl⟩ : syracuseStep 4206563 = 6309845) B6309845
theorem B2805745 : Blo 1661530 2805745 := bstep (se 2 (by rfl) ⟨1052154, by rfl⟩ : syracuseStep 2805745 = 2104309) B2104309
theorem B2494451 : Blo 1661530 2494451 := bstep (se 1 (by rfl) ⟨1870838, by rfl⟩ : syracuseStep 2494451 = 3741677) B3741677
theorem B2494481 : Blo 1661530 2494481 := bstep (se 2 (by rfl) ⟨935430, by rfl⟩ : syracuseStep 2494481 = 1870861) B1870861
theorem B2805779 : Blo 1661530 2805779 := bstep (se 1 (by rfl) ⟨2104334, by rfl⟩ : syracuseStep 2805779 = 4208669) B4208669
theorem B2494499 : Blo 1661530 2494499 := bstep (se 1 (by rfl) ⟨1870874, by rfl⟩ : syracuseStep 2494499 = 3741749) B3741749
theorem B3739697 : Blo 1661530 3739697 := bstep (se 2 (by rfl) ⟨1402386, by rfl⟩ : syracuseStep 3739697 = 2804773) B2804773
theorem B2494529 : Blo 1661530 2494529 := bstep (se 2 (by rfl) ⟨935448, by rfl⟩ : syracuseStep 2494529 = 1870897) B1870897
theorem B3739715 : Blo 1661530 3739715 := bstep (se 1 (by rfl) ⟨2804786, by rfl⟩ : syracuseStep 3739715 = 5609573) B5609573
theorem B8417357 : Blo 1661530 8417357 := bstep (se 3 (by rfl) ⟨1578254, by rfl⟩ : syracuseStep 8417357 = 3156509) B3156509
theorem B6926435 : Blo 1661530 6926435 := bstep (se 1 (by rfl) ⟨5194826, by rfl⟩ : syracuseStep 6926435 = 10389653) B10389653
theorem B6312077 : Blo 1661530 6312077 := bstep (se 3 (by rfl) ⟨1183514, by rfl⟩ : syracuseStep 6312077 = 2367029) B2367029
theorem B2805907 : Blo 1661530 2805907 := bstep (se 1 (by rfl) ⟨2104430, by rfl⟩ : syracuseStep 2805907 = 4208861) B4208861
theorem B4206755 : Blo 1661530 4206755 := bstep (se 1 (by rfl) ⟨3155066, by rfl⟩ : syracuseStep 4206755 = 6310133) B6310133
theorem B5607683 : Blo 1661530 5607683 := bstep (se 1 (by rfl) ⟨4205762, by rfl⟩ : syracuseStep 5607683 = 8411525) B8411525
theorem B2806049 : Blo 1661530 2806049 := bstep (se 2 (by rfl) ⟨1052268, by rfl⟩ : syracuseStep 2806049 = 2104537) B2104537
theorem B30322997 : Blo 1661530 30322997 := bstep (se 5 (by rfl) ⟨1421390, by rfl⟩ : syracuseStep 30322997 = 2842781) B2842781
theorem B3739985 : Blo 1661530 3739985 := bstep (se 2 (by rfl) ⟨1402494, by rfl⟩ : syracuseStep 3739985 = 2804989) B2804989
theorem B3740003 : Blo 1661530 3740003 := bstep (se 1 (by rfl) ⟨2805002, by rfl⟩ : syracuseStep 3740003 = 5610005) B5610005
theorem B3371395 : Blo 1661530 3371395 := bstep (se 1 (by rfl) ⟨2528546, by rfl⟩ : syracuseStep 3371395 = 5057093) B5057093
theorem B2806177 : Blo 1661530 2806177 := bstep (se 2 (by rfl) ⟨1052316, by rfl⟩ : syracuseStep 2806177 = 2104633) B2104633
theorem B2806211 : Blo 1661530 2806211 := bstep (se 1 (by rfl) ⟨2104658, by rfl⟩ : syracuseStep 2806211 = 4209317) B4209317
theorem B11981297 : Blo 1661530 11981297 := bstep (se 2 (by rfl) ⟨4492986, by rfl⟩ : syracuseStep 11981297 = 8985973) B8985973
theorem B4493809 : Blo 1661530 4493809 := bstep (se 2 (by rfl) ⟨1685178, by rfl⟩ : syracuseStep 4493809 = 3370357) B3370357
theorem B5607953 : Blo 1661530 5607953 := bstep (se 2 (by rfl) ⟨2102982, by rfl⟩ : syracuseStep 5607953 = 4205965) B4205965
theorem B2806339 : Blo 1661530 2806339 := bstep (se 1 (by rfl) ⟨2104754, by rfl⟩ : syracuseStep 2806339 = 4209509) B4209509
theorem B4731473 : Blo 1661530 4731473 := bstep (se 2 (by rfl) ⟨1774302, by rfl⟩ : syracuseStep 4731473 = 3548605) B3548605
theorem B3740273 : Blo 1661530 3740273 := bstep (se 2 (by rfl) ⟨1402602, by rfl⟩ : syracuseStep 3740273 = 2805205) B2805205
theorem B3740291 : Blo 1661530 3740291 := bstep (se 1 (by rfl) ⟨2805218, by rfl⟩ : syracuseStep 3740291 = 5610437) B5610437
theorem B3740561 : Blo 1661530 3740561 := bstep (se 2 (by rfl) ⟨1402710, by rfl⟩ : syracuseStep 3740561 = 2805421) B2805421
theorem B3740579 : Blo 1661530 3740579 := bstep (se 1 (by rfl) ⟨2805434, by rfl⟩ : syracuseStep 3740579 = 5610869) B5610869
theorem B6927373 : Blo 1661530 6927373 := bstep (se 3 (by rfl) ⟨1298882, by rfl⟩ : syracuseStep 6927373 = 2597765) B2597765
theorem B5608493 : Blo 1661530 5608493 := bstep (se 3 (by rfl) ⟨1051592, by rfl⟩ : syracuseStep 5608493 = 2103185) B2103185
theorem B4207697 : Blo 1661530 4207697 := bstep (se 2 (by rfl) ⟨1577886, by rfl⟩ : syracuseStep 4207697 = 3155773) B3155773
theorem B5608547 : Blo 1661530 5608547 := bstep (se 1 (by rfl) ⟨4206410, by rfl⟩ : syracuseStep 5608547 = 8412821) B8412821
theorem B1684595 : Blo 1661530 1684595 := bstep (se 1 (by rfl) ⟨1263446, by rfl⟩ : syracuseStep 1684595 = 2526893) B2526893
theorem B4207747 : Blo 1661530 4207747 := bstep (se 1 (by rfl) ⟨3155810, by rfl⟩ : syracuseStep 4207747 = 6311621) B6311621
theorem B3740849 : Blo 1661530 3740849 := bstep (se 2 (by rfl) ⟨1402818, by rfl⟩ : syracuseStep 3740849 = 2805637) B2805637
theorem B3740867 : Blo 1661530 3740867 := bstep (se 1 (by rfl) ⟨2805650, by rfl⟩ : syracuseStep 3740867 = 5611301) B5611301
theorem B15971525 : Blo 1661530 15971525 := bstep (se 4 (by rfl) ⟨1497330, by rfl⟩ : syracuseStep 15971525 = 2994661) B2994661
theorem B1774819 : Blo 1661530 1774819 := bstep (se 1 (by rfl) ⟨1331114, by rfl⟩ : syracuseStep 1774819 = 2662229) B2662229
theorem B4732145 : Blo 1661530 4732145 := bstep (se 2 (by rfl) ⟨1774554, by rfl⟩ : syracuseStep 4732145 = 3549109) B3549109
theorem B4207889 : Blo 1661530 4207889 := bstep (se 2 (by rfl) ⟨1577958, by rfl⟩ : syracuseStep 4207889 = 3155917) B3155917
theorem B5608817 : Blo 1661530 5608817 := bstep (se 2 (by rfl) ⟨2103306, by rfl⟩ : syracuseStep 5608817 = 4206613) B4206613
theorem B3741137 : Blo 1661530 3741137 := bstep (se 2 (by rfl) ⟨1402926, by rfl⟩ : syracuseStep 3741137 = 2805853) B2805853
theorem B3741155 : Blo 1661530 3741155 := bstep (se 1 (by rfl) ⟨2805866, by rfl⟩ : syracuseStep 3741155 = 5611733) B5611733
theorem B6395441 : Blo 1661530 6395441 := bstep (se 2 (by rfl) ⟨2398290, by rfl⟩ : syracuseStep 6395441 = 4796581) B4796581
theorem B20502085 : Blo 1661530 20502085 := bstep (se 4 (by rfl) ⟨1922070, by rfl⟩ : syracuseStep 20502085 = 3844141) B3844141
theorem B7100081 : Blo 1661530 7100081 := bstep (se 2 (by rfl) ⟨2662530, by rfl⟩ : syracuseStep 7100081 = 5325061) B5325061
theorem B34592453 : Blo 1661530 34592453 := bstep (se 4 (by rfl) ⟨3243042, by rfl⟩ : syracuseStep 34592453 = 6486085) B6486085
theorem B3741425 : Blo 1661530 3741425 := bstep (se 2 (by rfl) ⟨1403034, by rfl⟩ : syracuseStep 3741425 = 2806069) B2806069
theorem B3741443 : Blo 1661530 3741443 := bstep (se 1 (by rfl) ⟨2806082, by rfl⟩ : syracuseStep 3741443 = 5612165) B5612165
theorem B2996003 : Blo 1661530 2996003 := bstep (se 1 (by rfl) ⟨2247002, by rfl⟩ : syracuseStep 2996003 = 4494005) B4494005
theorem B5609357 : Blo 1661530 5609357 := bstep (se 3 (by rfl) ⟨1051754, by rfl⟩ : syracuseStep 5609357 = 2103509) B2103509
theorem B5609411 : Blo 1661530 5609411 := bstep (se 1 (by rfl) ⟨4207058, by rfl⟩ : syracuseStep 5609411 = 8414117) B8414117
theorem B4732931 : Blo 1661530 4732931 := bstep (se 1 (by rfl) ⟨3549698, by rfl⟩ : syracuseStep 4732931 = 7099397) B7099397
theorem B3741713 : Blo 1661530 3741713 := bstep (se 2 (by rfl) ⟨1403142, by rfl⟩ : syracuseStep 3741713 = 2806285) B2806285
theorem B3741731 : Blo 1661530 3741731 := bstep (se 1 (by rfl) ⟨2806298, by rfl⟩ : syracuseStep 3741731 = 5612597) B5612597
theorem B2103347 : Blo 1661530 2103347 := bstep (se 1 (by rfl) ⟨1577510, by rfl⟩ : syracuseStep 2103347 = 3155021) B3155021
theorem B8100017 : Blo 1661530 8100017 := bstep (se 2 (by rfl) ⟨3037506, by rfl⟩ : syracuseStep 8100017 = 6075013) B6075013
theorem B1996979 : Blo 1661530 1996979 := bstep (se 1 (by rfl) ⟨1497734, by rfl⟩ : syracuseStep 1996979 = 2995469) B2995469
theorem B14039237 : Blo 1661530 14039237 := bstep (se 4 (by rfl) ⟨1316178, by rfl⟩ : syracuseStep 14039237 = 2632357) B2632357
theorem B5609681 : Blo 1661530 5609681 := bstep (se 2 (by rfl) ⟨2103630, by rfl⟩ : syracuseStep 5609681 = 4207261) B4207261
theorem B1775827 : Blo 1661530 1775827 := bstep (se 1 (by rfl) ⟨1331870, by rfl⟩ : syracuseStep 1775827 = 2663741) B2663741
theorem B4208881 : Blo 1661530 4208881 := bstep (se 2 (by rfl) ⟨1578330, by rfl⟩ : syracuseStep 4208881 = 3156661) B3156661
theorem B4733261 : Blo 1661530 4733261 := bstep (se 3 (by rfl) ⟨887486, by rfl⟩ : syracuseStep 4733261 = 1774973) B1774973
theorem B3414403 : Blo 1661530 3414403 := bstep (se 1 (by rfl) ⟨2560802, by rfl⟩ : syracuseStep 3414403 = 5121605) B5121605
theorem B4733329 : Blo 1661530 4733329 := bstep (se 2 (by rfl) ⟨1774998, by rfl⟩ : syracuseStep 4733329 = 3549997) B3549997
theorem B4209155 : Blo 1661530 4209155 := bstep (se 1 (by rfl) ⟨3156866, by rfl⟩ : syracuseStep 4209155 = 6313733) B6313733
theorem B1661539 : Blo 1661530 1661539 := bstep (se 1 (by rfl) ⟨1246154, by rfl⟩ : syracuseStep 1661539 = 2492309) B2492309
theorem B1661555 : Blo 1661530 1661555 := bstep (se 1 (by rfl) ⟨1246166, by rfl⟩ : syracuseStep 1661555 = 2492333) B2492333
theorem B1661571 : Blo 1661530 1661571 := bstep (se 1 (by rfl) ⟨1246178, by rfl⟩ : syracuseStep 1661571 = 2492357) B2492357
theorem B1661587 : Blo 1661530 1661587 := bstep (se 1 (by rfl) ⟨1246190, by rfl⟩ : syracuseStep 1661587 = 2492381) B2492381
theorem B1661603 : Blo 1661530 1661603 := bstep (se 1 (by rfl) ⟨1246202, by rfl⟩ : syracuseStep 1661603 = 2492405) B2492405
theorem B4733603 : Blo 1661530 4733603 := bstep (se 1 (by rfl) ⟨3550202, by rfl⟩ : syracuseStep 4733603 = 7100405) B7100405
theorem B2366129 : Blo 1661530 2366129 := bstep (se 2 (by rfl) ⟨887298, by rfl⟩ : syracuseStep 2366129 = 1774597) B1774597
theorem B1661619 : Blo 1661530 1661619 := bstep (se 1 (by rfl) ⟨1246214, by rfl⟩ : syracuseStep 1661619 = 2492429) B2492429
theorem B1661635 : Blo 1661530 1661635 := bstep (se 1 (by rfl) ⟨1246226, by rfl⟩ : syracuseStep 1661635 = 2492453) B2492453
theorem B4209347 : Blo 1661530 4209347 := bstep (se 1 (by rfl) ⟨3157010, by rfl⟩ : syracuseStep 4209347 = 6314021) B6314021
theorem B1661651 : Blo 1661530 1661651 := bstep (se 1 (by rfl) ⟨1246238, by rfl⟩ : syracuseStep 1661651 = 2492477) B2492477
theorem B1661667 : Blo 1661530 1661667 := bstep (se 1 (by rfl) ⟨1246250, by rfl⟩ : syracuseStep 1661667 = 2492501) B2492501
theorem B76798691 : Blo 1661530 76798691 := bstep (se 1 (by rfl) ⟨57599018, by rfl⟩ : syracuseStep 76798691 = 115198037) B115198037
theorem B5610221 : Blo 1661530 5610221 := bstep (se 3 (by rfl) ⟨1051916, by rfl⟩ : syracuseStep 5610221 = 2103833) B2103833
theorem B1661683 : Blo 1661530 1661683 := bstep (se 1 (by rfl) ⟨1246262, by rfl⟩ : syracuseStep 1661683 = 2492525) B2492525
theorem B2104051 : Blo 1661530 2104051 := bstep (se 1 (by rfl) ⟨1578038, by rfl⟩ : syracuseStep 2104051 = 3156077) B3156077
theorem B2366209 : Blo 1661530 2366209 := bstep (se 2 (by rfl) ⟨887328, by rfl⟩ : syracuseStep 2366209 = 1774657) B1774657
theorem B1661699 : Blo 1661530 1661699 := bstep (se 1 (by rfl) ⟨1246274, by rfl⟩ : syracuseStep 1661699 = 2492549) B2492549
theorem B1661715 : Blo 1661530 1661715 := bstep (se 1 (by rfl) ⟨1246286, by rfl⟩ : syracuseStep 1661715 = 2492573) B2492573
theorem B1661731 : Blo 1661530 1661731 := bstep (se 1 (by rfl) ⟨1246298, by rfl⟩ : syracuseStep 1661731 = 2492597) B2492597
theorem B5610275 : Blo 1661530 5610275 := bstep (se 1 (by rfl) ⟨4207706, by rfl⟩ : syracuseStep 5610275 = 8415413) B8415413
theorem B1661747 : Blo 1661530 1661747 := bstep (se 1 (by rfl) ⟨1246310, by rfl⟩ : syracuseStep 1661747 = 2492621) B2492621
theorem B1661763 : Blo 1661530 1661763 := bstep (se 1 (by rfl) ⟨1246322, by rfl⟩ : syracuseStep 1661763 = 2492645) B2492645
theorem B1661779 : Blo 1661530 1661779 := bstep (se 1 (by rfl) ⟨1246334, by rfl⟩ : syracuseStep 1661779 = 2492669) B2492669
theorem B2104147 : Blo 1661530 2104147 := bstep (se 1 (by rfl) ⟨1578110, by rfl⟩ : syracuseStep 2104147 = 3156221) B3156221
theorem B1661795 : Blo 1661530 1661795 := bstep (se 1 (by rfl) ⟨1246346, by rfl⟩ : syracuseStep 1661795 = 2492693) B2492693
theorem B1661811 : Blo 1661530 1661811 := bstep (se 1 (by rfl) ⟨1246358, by rfl⟩ : syracuseStep 1661811 = 2492717) B2492717
theorem B1661827 : Blo 1661530 1661827 := bstep (se 1 (by rfl) ⟨1246370, by rfl⟩ : syracuseStep 1661827 = 2492741) B2492741
theorem B1661843 : Blo 1661530 1661843 := bstep (se 1 (by rfl) ⟨1246382, by rfl⟩ : syracuseStep 1661843 = 2492765) B2492765
theorem B1661859 : Blo 1661530 1661859 := bstep (se 1 (by rfl) ⟨1246394, by rfl⟩ : syracuseStep 1661859 = 2492789) B2492789
theorem B1661875 : Blo 1661530 1661875 := bstep (se 1 (by rfl) ⟨1246406, by rfl⟩ : syracuseStep 1661875 = 2492813) B2492813
theorem B1661891 : Blo 1661530 1661891 := bstep (se 1 (by rfl) ⟨1246418, by rfl⟩ : syracuseStep 1661891 = 2492837) B2492837
theorem B1661907 : Blo 1661530 1661907 := bstep (se 1 (by rfl) ⟨1246430, by rfl⟩ : syracuseStep 1661907 = 2492861) B2492861
theorem B1661923 : Blo 1661530 1661923 := bstep (se 1 (by rfl) ⟨1246442, by rfl⟩ : syracuseStep 1661923 = 2492885) B2492885
theorem B2882531 : Blo 1661530 2882531 := bstep (se 1 (by rfl) ⟨2161898, by rfl⟩ : syracuseStep 2882531 = 4323797) B4323797
theorem B1661939 : Blo 1661530 1661939 := bstep (se 1 (by rfl) ⟨1246454, by rfl⟩ : syracuseStep 1661939 = 2492909) B2492909
theorem B1661955 : Blo 1661530 1661955 := bstep (se 1 (by rfl) ⟨1246466, by rfl⟩ : syracuseStep 1661955 = 2492933) B2492933
theorem B8412173 : Blo 1661530 8412173 := bstep (se 3 (by rfl) ⟨1577282, by rfl⟩ : syracuseStep 8412173 = 3154565) B3154565
theorem B1661971 : Blo 1661530 1661971 := bstep (se 1 (by rfl) ⟨1246478, by rfl⟩ : syracuseStep 1661971 = 2492957) B2492957
theorem B1661987 : Blo 1661530 1661987 := bstep (se 1 (by rfl) ⟨1246490, by rfl⟩ : syracuseStep 1661987 = 2492981) B2492981
theorem B5610545 : Blo 1661530 5610545 := bstep (se 2 (by rfl) ⟨2103954, by rfl⟩ : syracuseStep 5610545 = 4207909) B4207909
theorem B1662003 : Blo 1661530 1662003 := bstep (se 1 (by rfl) ⟨1246502, by rfl⟩ : syracuseStep 1662003 = 2493005) B2493005
theorem B1662019 : Blo 1661530 1662019 := bstep (se 1 (by rfl) ⟨1246514, by rfl⟩ : syracuseStep 1662019 = 2493029) B2493029
theorem B1662035 : Blo 1661530 1662035 := bstep (se 1 (by rfl) ⟨1246526, by rfl⟩ : syracuseStep 1662035 = 2493053) B2493053
theorem B2661473 : Blo 1661530 2661473 := bstep (se 2 (by rfl) ⟨998052, by rfl⟩ : syracuseStep 2661473 = 1996105) B1996105
theorem B1662051 : Blo 1661530 1662051 := bstep (se 1 (by rfl) ⟨1246538, by rfl⟩ : syracuseStep 1662051 = 2493077) B2493077
theorem B1662067 : Blo 1661530 1662067 := bstep (se 1 (by rfl) ⟨1246550, by rfl⟩ : syracuseStep 1662067 = 2493101) B2493101
theorem B1662083 : Blo 1661530 1662083 := bstep (se 1 (by rfl) ⟨1246562, by rfl⟩ : syracuseStep 1662083 = 2493125) B2493125
theorem B10648709 : Blo 1661530 10648709 := bstep (se 4 (by rfl) ⟨998316, by rfl⟩ : syracuseStep 10648709 = 1996633) B1996633
theorem B3792017 : Blo 1661530 3792017 := bstep (se 2 (by rfl) ⟨1422006, by rfl⟩ : syracuseStep 3792017 = 2844013) B2844013
theorem B1662099 : Blo 1661530 1662099 := bstep (se 1 (by rfl) ⟨1246574, by rfl⟩ : syracuseStep 1662099 = 2493149) B2493149
theorem B1662115 : Blo 1661530 1662115 := bstep (se 1 (by rfl) ⟨1246586, by rfl⟩ : syracuseStep 1662115 = 2493173) B2493173
theorem B1662131 : Blo 1661530 1662131 := bstep (se 1 (by rfl) ⟨1246598, by rfl⟩ : syracuseStep 1662131 = 2493197) B2493197
theorem B1662147 : Blo 1661530 1662147 := bstep (se 1 (by rfl) ⟨1246610, by rfl⟩ : syracuseStep 1662147 = 2493221) B2493221
theorem B1662163 : Blo 1661530 1662163 := bstep (se 1 (by rfl) ⟨1246622, by rfl⟩ : syracuseStep 1662163 = 2493245) B2493245
theorem B1662179 : Blo 1661530 1662179 := bstep (se 1 (by rfl) ⟨1246634, by rfl⟩ : syracuseStep 1662179 = 2493269) B2493269
theorem B1662195 : Blo 1661530 1662195 := bstep (se 1 (by rfl) ⟨1246646, by rfl⟩ : syracuseStep 1662195 = 2493293) B2493293
theorem B1662211 : Blo 1661530 1662211 := bstep (se 1 (by rfl) ⟨1246658, by rfl⟩ : syracuseStep 1662211 = 2493317) B2493317
theorem B1662227 : Blo 1661530 1662227 := bstep (se 1 (by rfl) ⟨1246670, by rfl⟩ : syracuseStep 1662227 = 2493341) B2493341
theorem B1662243 : Blo 1661530 1662243 := bstep (se 1 (by rfl) ⟨1246682, by rfl⟩ : syracuseStep 1662243 = 2493365) B2493365
theorem B1662259 : Blo 1661530 1662259 := bstep (se 1 (by rfl) ⟨1246694, by rfl⟩ : syracuseStep 1662259 = 2493389) B2493389
theorem B1662275 : Blo 1661530 1662275 := bstep (se 1 (by rfl) ⟨1246706, by rfl⟩ : syracuseStep 1662275 = 2493413) B2493413
theorem B2104643 : Blo 1661530 2104643 := bstep (se 1 (by rfl) ⟨1578482, by rfl⟩ : syracuseStep 2104643 = 3156965) B3156965
theorem B1662291 : Blo 1661530 1662291 := bstep (se 1 (by rfl) ⟨1246718, by rfl⟩ : syracuseStep 1662291 = 2493437) B2493437
theorem B5684579 : Blo 1661530 5684579 := bstep (se 1 (by rfl) ⟨4263434, by rfl⟩ : syracuseStep 5684579 = 8526869) B8526869
theorem B1662307 : Blo 1661530 1662307 := bstep (se 1 (by rfl) ⟨1246730, by rfl⟩ : syracuseStep 1662307 = 2493461) B2493461
theorem B1662323 : Blo 1661530 1662323 := bstep (se 1 (by rfl) ⟨1246742, by rfl⟩ : syracuseStep 1662323 = 2493485) B2493485
theorem B1662339 : Blo 1661530 1662339 := bstep (se 1 (by rfl) ⟨1246754, by rfl⟩ : syracuseStep 1662339 = 2493509) B2493509
theorem B9600389 : Blo 1661530 9600389 := bstep (se 4 (by rfl) ⟨900036, by rfl⟩ : syracuseStep 9600389 = 1800073) B1800073
theorem B1662355 : Blo 1661530 1662355 := bstep (se 1 (by rfl) ⟨1246766, by rfl⟩ : syracuseStep 1662355 = 2493533) B2493533
theorem B1662371 : Blo 1661530 1662371 := bstep (se 1 (by rfl) ⟨1246778, by rfl⟩ : syracuseStep 1662371 = 2493557) B2493557
theorem B5053873 : Blo 1661530 5053873 := bstep (se 2 (by rfl) ⟨1895202, by rfl⟩ : syracuseStep 5053873 = 3790405) B3790405
theorem B1662387 : Blo 1661530 1662387 := bstep (se 1 (by rfl) ⟨1246790, by rfl⟩ : syracuseStep 1662387 = 2493581) B2493581
theorem B1662403 : Blo 1661530 1662403 := bstep (se 1 (by rfl) ⟨1246802, by rfl⟩ : syracuseStep 1662403 = 2493605) B2493605
theorem B1662419 : Blo 1661530 1662419 := bstep (se 1 (by rfl) ⟨1246814, by rfl⟩ : syracuseStep 1662419 = 2493629) B2493629
theorem B1662435 : Blo 1661530 1662435 := bstep (se 1 (by rfl) ⟨1246826, by rfl⟩ : syracuseStep 1662435 = 2493653) B2493653
theorem B4734445 : Blo 1661530 4734445 := bstep (se 3 (by rfl) ⟨887708, by rfl⟩ : syracuseStep 4734445 = 1775417) B1775417
theorem B1662451 : Blo 1661530 1662451 := bstep (se 1 (by rfl) ⟨1246838, by rfl⟩ : syracuseStep 1662451 = 2493677) B2493677
theorem B1662467 : Blo 1661530 1662467 := bstep (se 1 (by rfl) ⟨1246850, by rfl⟩ : syracuseStep 1662467 = 2493701) B2493701
theorem B14204429 : Blo 1661530 14204429 := bstep (se 3 (by rfl) ⟨2663330, by rfl⟩ : syracuseStep 14204429 = 5326661) B5326661
theorem B2366995 : Blo 1661530 2366995 := bstep (se 1 (by rfl) ⟨1775246, by rfl⟩ : syracuseStep 2366995 = 3550493) B3550493
theorem B1662483 : Blo 1661530 1662483 := bstep (se 1 (by rfl) ⟨1246862, by rfl⟩ : syracuseStep 1662483 = 2493725) B2493725
theorem B1662499 : Blo 1661530 1662499 := bstep (se 1 (by rfl) ⟨1246874, by rfl⟩ : syracuseStep 1662499 = 2493749) B2493749
theorem B1662515 : Blo 1661530 1662515 := bstep (se 1 (by rfl) ⟨1246886, by rfl⟩ : syracuseStep 1662515 = 2493773) B2493773
theorem B1662531 : Blo 1661530 1662531 := bstep (se 1 (by rfl) ⟨1246898, by rfl⟩ : syracuseStep 1662531 = 2493797) B2493797
theorem B5611085 : Blo 1661530 5611085 := bstep (se 3 (by rfl) ⟨1052078, by rfl⟩ : syracuseStep 5611085 = 2104157) B2104157
theorem B1662547 : Blo 1661530 1662547 := bstep (se 1 (by rfl) ⟨1246910, by rfl⟩ : syracuseStep 1662547 = 2493821) B2493821
theorem B1662563 : Blo 1661530 1662563 := bstep (se 1 (by rfl) ⟨1246922, by rfl⟩ : syracuseStep 1662563 = 2493845) B2493845
theorem B1662579 : Blo 1661530 1662579 := bstep (se 1 (by rfl) ⟨1246934, by rfl⟩ : syracuseStep 1662579 = 2493869) B2493869
theorem B5611139 : Blo 1661530 5611139 := bstep (se 1 (by rfl) ⟨4208354, by rfl⟩ : syracuseStep 5611139 = 8416709) B8416709
theorem B1662595 : Blo 1661530 1662595 := bstep (se 1 (by rfl) ⟨1246946, by rfl⟩ : syracuseStep 1662595 = 2493893) B2493893
theorem B4734605 : Blo 1661530 4734605 := bstep (se 3 (by rfl) ⟨887738, by rfl⟩ : syracuseStep 4734605 = 1775477) B1775477
theorem B1662611 : Blo 1661530 1662611 := bstep (se 1 (by rfl) ⟨1246958, by rfl⟩ : syracuseStep 1662611 = 2493917) B2493917
theorem B1662627 : Blo 1661530 1662627 := bstep (se 1 (by rfl) ⟨1246970, by rfl⟩ : syracuseStep 1662627 = 2493941) B2493941
theorem B1662643 : Blo 1661530 1662643 := bstep (se 1 (by rfl) ⟨1246982, by rfl⟩ : syracuseStep 1662643 = 2493965) B2493965
theorem B1662659 : Blo 1661530 1662659 := bstep (se 1 (by rfl) ⟨1246994, by rfl⟩ : syracuseStep 1662659 = 2493989) B2493989
theorem B1662675 : Blo 1661530 1662675 := bstep (se 1 (by rfl) ⟨1247006, by rfl⟩ : syracuseStep 1662675 = 2494013) B2494013
theorem B1662691 : Blo 1661530 1662691 := bstep (se 1 (by rfl) ⟨1247018, by rfl⟩ : syracuseStep 1662691 = 2494037) B2494037
theorem B1662707 : Blo 1661530 1662707 := bstep (se 1 (by rfl) ⟨1247030, by rfl⟩ : syracuseStep 1662707 = 2494061) B2494061
theorem B1662723 : Blo 1661530 1662723 := bstep (se 1 (by rfl) ⟨1247042, by rfl⟩ : syracuseStep 1662723 = 2494085) B2494085
theorem B1662739 : Blo 1661530 1662739 := bstep (se 1 (by rfl) ⟨1247054, by rfl⟩ : syracuseStep 1662739 = 2494109) B2494109
theorem B1662755 : Blo 1661530 1662755 := bstep (se 1 (by rfl) ⟨1247066, by rfl⟩ : syracuseStep 1662755 = 2494133) B2494133
theorem B1662771 : Blo 1661530 1662771 := bstep (se 1 (by rfl) ⟨1247078, by rfl⟩ : syracuseStep 1662771 = 2494157) B2494157
theorem B5324611 : Blo 1661530 5324611 := bstep (se 1 (by rfl) ⟨3993458, by rfl⟩ : syracuseStep 5324611 = 7986917) B7986917
theorem B4734787 : Blo 1661530 4734787 := bstep (se 1 (by rfl) ⟨3551090, by rfl⟩ : syracuseStep 4734787 = 7102181) B7102181
theorem B1662787 : Blo 1661530 1662787 := bstep (se 1 (by rfl) ⟨1247090, by rfl⟩ : syracuseStep 1662787 = 2494181) B2494181
theorem B1662803 : Blo 1661530 1662803 := bstep (se 1 (by rfl) ⟨1247102, by rfl⟩ : syracuseStep 1662803 = 2494205) B2494205
theorem B1662819 : Blo 1661530 1662819 := bstep (se 1 (by rfl) ⟨1247114, by rfl⟩ : syracuseStep 1662819 = 2494229) B2494229
theorem B21299057 : Blo 1661530 21299057 := bstep (se 2 (by rfl) ⟨7987146, by rfl⟩ : syracuseStep 21299057 = 15974293) B15974293
theorem B1662835 : Blo 1661530 1662835 := bstep (se 1 (by rfl) ⟨1247126, by rfl⟩ : syracuseStep 1662835 = 2494253) B2494253
theorem B1662851 : Blo 1661530 1662851 := bstep (se 1 (by rfl) ⟨1247138, by rfl⟩ : syracuseStep 1662851 = 2494277) B2494277
theorem B5611409 : Blo 1661530 5611409 := bstep (se 2 (by rfl) ⟨2104278, by rfl⟩ : syracuseStep 5611409 = 4208557) B4208557
theorem B1662867 : Blo 1661530 1662867 := bstep (se 1 (by rfl) ⟨1247150, by rfl⟩ : syracuseStep 1662867 = 2494301) B2494301
theorem B1662883 : Blo 1661530 1662883 := bstep (se 1 (by rfl) ⟨1247162, by rfl⟩ : syracuseStep 1662883 = 2494325) B2494325
theorem B1662899 : Blo 1661530 1662899 := bstep (se 1 (by rfl) ⟨1247174, by rfl⟩ : syracuseStep 1662899 = 2494349) B2494349
theorem B1662915 : Blo 1661530 1662915 := bstep (se 1 (by rfl) ⟨1247186, by rfl⟩ : syracuseStep 1662915 = 2494373) B2494373
theorem B5324753 : Blo 1661530 5324753 := bstep (se 2 (by rfl) ⟨1996782, by rfl⟩ : syracuseStep 5324753 = 3993565) B3993565
theorem B1662931 : Blo 1661530 1662931 := bstep (se 1 (by rfl) ⟨1247198, by rfl⟩ : syracuseStep 1662931 = 2494397) B2494397
theorem B14196707 : Blo 1661530 14196707 := bstep (se 1 (by rfl) ⟨10647530, by rfl⟩ : syracuseStep 14196707 = 21295061) B21295061
theorem B1662947 : Blo 1661530 1662947 := bstep (se 1 (by rfl) ⟨1247210, by rfl⟩ : syracuseStep 1662947 = 2494421) B2494421
theorem B2367473 : Blo 1661530 2367473 := bstep (se 2 (by rfl) ⟨887802, by rfl⟩ : syracuseStep 2367473 = 1775605) B1775605
theorem B1662963 : Blo 1661530 1662963 := bstep (se 1 (by rfl) ⟨1247222, by rfl⟩ : syracuseStep 1662963 = 2494445) B2494445
theorem B1662987 : Blo 1661530 1662987 := bstep (se 1 (by rfl) ⟨1247240, by rfl⟩ : syracuseStep 1662987 = 2494481) B2494481
theorem B1662999 : Blo 1661530 1662999 := bstep (se 1 (by rfl) ⟨1247249, by rfl⟩ : syracuseStep 1662999 = 2494499) B2494499
theorem B1663019 : Blo 1661530 1663019 := bstep (se 1 (by rfl) ⟨1247264, by rfl⟩ : syracuseStep 1663019 = 2494529) B2494529
theorem B5611571 : Blo 1661530 5611571 := bstep (se 1 (by rfl) ⟨4208678, by rfl⟩ : syracuseStep 5611571 = 8417357) B8417357
theorem B8986925 : Blo 1661530 8986925 := bstep (se 3 (by rfl) ⟨1685048, by rfl⟩ : syracuseStep 8986925 = 3370097) B3370097
theorem B5611841 : Blo 1661530 5611841 := bstep (se 2 (by rfl) ⟨2104440, by rfl⟩ : syracuseStep 5611841 = 4208881) B4208881
theorem B11977091 : Blo 1661530 11977091 := bstep (se 1 (by rfl) ⟨8982818, by rfl⟩ : syracuseStep 11977091 = 17965637) B17965637
theorem B3154315 : Blo 1661530 3154315 := bstep (se 1 (by rfl) ⟨2365736, by rfl⟩ : syracuseStep 3154315 = 4731473) B4731473
theorem B5325277 : Blo 1661530 5325277 := bstep (se 3 (by rfl) ⟨998489, by rfl⟩ : syracuseStep 5325277 = 1996979) B1996979
theorem B3154763 : Blo 1661530 3154763 := bstep (se 1 (by rfl) ⟨2366072, by rfl⟩ : syracuseStep 3154763 = 4732145) B4732145
theorem B5612381 : Blo 1661530 5612381 := bstep (se 3 (by rfl) ⟨1052321, by rfl⟩ : syracuseStep 5612381 = 2104643) B2104643
theorem B3154945 : Blo 1661530 3154945 := bstep (se 2 (by rfl) ⟨1183104, by rfl⟩ : syracuseStep 3154945 = 2366209) B2366209
theorem B6308887 : Blo 1661530 6308887 := bstep (se 1 (by rfl) ⟨4731665, by rfl⟩ : syracuseStep 6308887 = 9463331) B9463331
theorem B9471077 : Blo 1661530 9471077 := bstep (se 4 (by rfl) ⟨887913, by rfl⟩ : syracuseStep 9471077 = 1775827) B1775827
theorem B23061635 : Blo 1661530 23061635 := bstep (se 1 (by rfl) ⟨17296226, by rfl⟩ : syracuseStep 23061635 = 34592453) B34592453
theorem B31950125 : Blo 1661530 31950125 := bstep (se 3 (by rfl) ⟨5990648, by rfl⟩ : syracuseStep 31950125 = 11981297) B11981297
theorem B3155287 : Blo 1661530 3155287 := bstep (se 1 (by rfl) ⟨2366465, by rfl⟩ : syracuseStep 3155287 = 4732931) B4732931
theorem B1869259 : Blo 1661530 1869259 := bstep (se 1 (by rfl) ⟨1401944, by rfl⟩ : syracuseStep 1869259 = 2803889) B2803889
theorem B5400011 : Blo 1661530 5400011 := bstep (se 1 (by rfl) ⟨4050008, by rfl⟩ : syracuseStep 5400011 = 8100017) B8100017
theorem B40437265 : Blo 1661530 40437265 := bstep (se 2 (by rfl) ⟨15163974, by rfl⟩ : syracuseStep 40437265 = 30327949) B30327949
theorem B8414765 : Blo 1661530 8414765 := bstep (se 3 (by rfl) ⟨1577768, by rfl⟩ : syracuseStep 8414765 = 3155537) B3155537
theorem B3155507 : Blo 1661530 3155507 := bstep (se 1 (by rfl) ⟨2366630, by rfl⟩ : syracuseStep 3155507 = 4733261) B4733261
theorem B1869367 : Blo 1661530 1869367 := bstep (se 1 (by rfl) ⟨1402025, by rfl⟩ : syracuseStep 1869367 = 2804051) B2804051
theorem B9463513 : Blo 1661530 9463513 := bstep (se 2 (by rfl) ⟨3548817, by rfl⟩ : syracuseStep 9463513 = 7097635) B7097635
theorem B1869547 : Blo 1661530 1869547 := bstep (se 1 (by rfl) ⟨1402160, by rfl⟩ : syracuseStep 1869547 = 2804321) B2804321
theorem B3155735 : Blo 1661530 3155735 := bstep (se 1 (by rfl) ⟨2366801, by rfl⟩ : syracuseStep 3155735 = 4733603) B4733603
theorem B3368729 : Blo 1661530 3368729 := bstep (se 2 (by rfl) ⟨1263273, by rfl⟩ : syracuseStep 3368729 = 2526547) B2526547
theorem B6309677 : Blo 1661530 6309677 := bstep (se 3 (by rfl) ⟨1183064, by rfl⟩ : syracuseStep 6309677 = 2366129) B2366129
theorem B1869655 : Blo 1661530 1869655 := bstep (se 1 (by rfl) ⟨1402241, by rfl⟩ : syracuseStep 1869655 = 2804483) B2804483
theorem B35948387 : Blo 1661530 35948387 := bstep (se 1 (by rfl) ⟨26961290, by rfl⟩ : syracuseStep 35948387 = 53922581) B53922581
theorem B2492363 : Blo 1661530 2492363 := bstep (se 1 (by rfl) ⟨1869272, by rfl⟩ : syracuseStep 2492363 = 3738545) B3738545
theorem B2492375 : Blo 1661530 2492375 := bstep (se 1 (by rfl) ⟨1869281, by rfl⟩ : syracuseStep 2492375 = 3738563) B3738563
theorem B1869835 : Blo 1661530 1869835 := bstep (se 1 (by rfl) ⟨1402376, by rfl⟩ : syracuseStep 1869835 = 2804753) B2804753
theorem B2492441 : Blo 1661530 2492441 := bstep (se 2 (by rfl) ⟨934665, by rfl⟩ : syracuseStep 2492441 = 1869331) B1869331
theorem B3155993 : Blo 1661530 3155993 := bstep (se 2 (by rfl) ⟨1183497, by rfl⟩ : syracuseStep 3155993 = 2366995) B2366995
theorem B1869943 : Blo 1661530 1869943 := bstep (se 1 (by rfl) ⟨1402457, by rfl⟩ : syracuseStep 1869943 = 2804915) B2804915
theorem B2492555 : Blo 1661530 2492555 := bstep (se 1 (by rfl) ⟨1869416, by rfl⟩ : syracuseStep 2492555 = 3738833) B3738833
theorem B2492567 : Blo 1661530 2492567 := bstep (se 1 (by rfl) ⟨1869425, by rfl⟩ : syracuseStep 2492567 = 3738851) B3738851
theorem B2492633 : Blo 1661530 2492633 := bstep (se 2 (by rfl) ⟨934737, by rfl⟩ : syracuseStep 2492633 = 1869475) B1869475
theorem B6400259 : Blo 1661530 6400259 := bstep (se 1 (by rfl) ⟨4800194, by rfl⟩ : syracuseStep 6400259 = 9600389) B9600389
theorem B1870123 : Blo 1661530 1870123 := bstep (se 1 (by rfl) ⟨1402592, by rfl⟩ : syracuseStep 1870123 = 2805185) B2805185
theorem B2492747 : Blo 1661530 2492747 := bstep (se 1 (by rfl) ⟨1869560, by rfl⟩ : syracuseStep 2492747 = 3739121) B3739121
theorem B2492759 : Blo 1661530 2492759 := bstep (se 1 (by rfl) ⟨1869569, by rfl⟩ : syracuseStep 2492759 = 3739139) B3739139
theorem B1870231 : Blo 1661530 1870231 := bstep (se 1 (by rfl) ⟨1402673, by rfl⟩ : syracuseStep 1870231 = 2805347) B2805347
theorem B2492825 : Blo 1661530 2492825 := bstep (se 2 (by rfl) ⟨934809, by rfl⟩ : syracuseStep 2492825 = 1869619) B1869619
theorem B3156403 : Blo 1661530 3156403 := bstep (se 1 (by rfl) ⟨2367302, by rfl⟩ : syracuseStep 3156403 = 4734605) B4734605
theorem B5925341 : Blo 1661530 5925341 := bstep (se 3 (by rfl) ⟨1111001, by rfl⟩ : syracuseStep 5925341 = 2222003) B2222003
theorem B2492939 : Blo 1661530 2492939 := bstep (se 1 (by rfl) ⟨1869704, by rfl⟩ : syracuseStep 2492939 = 3739409) B3739409
theorem B2492951 : Blo 1661530 2492951 := bstep (se 1 (by rfl) ⟨1869713, by rfl⟩ : syracuseStep 2492951 = 3739427) B3739427
theorem B14199371 : Blo 1661530 14199371 := bstep (se 1 (by rfl) ⟨10649528, by rfl⟩ : syracuseStep 14199371 = 21299057) B21299057
theorem B1870411 : Blo 1661530 1870411 := bstep (se 1 (by rfl) ⟨1402808, by rfl⟩ : syracuseStep 1870411 = 2805617) B2805617
theorem B2493017 : Blo 1661530 2493017 := bstep (se 2 (by rfl) ⟨934881, by rfl⟩ : syracuseStep 2493017 = 1869763) B1869763
theorem B3549835 : Blo 1661530 3549835 := bstep (se 1 (by rfl) ⟨2662376, by rfl⟩ : syracuseStep 3549835 = 5324753) B5324753
theorem B9464471 : Blo 1661530 9464471 := bstep (se 1 (by rfl) ⟨7098353, by rfl⟩ : syracuseStep 9464471 = 14196707) B14196707
theorem B2804375 : Blo 1661530 2804375 := bstep (se 1 (by rfl) ⟨2103281, by rfl⟩ : syracuseStep 2804375 = 4206563) B4206563
theorem B1870519 : Blo 1661530 1870519 := bstep (se 1 (by rfl) ⟨1402889, by rfl⟩ : syracuseStep 1870519 = 2805779) B2805779
theorem B2493131 : Blo 1661530 2493131 := bstep (se 1 (by rfl) ⟨1869848, by rfl⟩ : syracuseStep 2493131 = 3739697) B3739697
theorem B1662967 : Blo 1661530 1662967 := bstep (se 1 (by rfl) ⟨1247225, by rfl⟩ : syracuseStep 1662967 = 2494451) B2494451
theorem B2493143 : Blo 1661530 2493143 := bstep (se 1 (by rfl) ⟨1869857, by rfl⟩ : syracuseStep 2493143 = 3739715) B3739715
theorem B3549911 : Blo 1661530 3549911 := bstep (se 1 (by rfl) ⟨2662433, by rfl⟩ : syracuseStep 3549911 = 5324867) B5324867
theorem B2804503 : Blo 1661530 2804503 := bstep (se 1 (by rfl) ⟨2103377, by rfl⟩ : syracuseStep 2804503 = 4206755) B4206755
theorem B2493209 : Blo 1661530 2493209 := bstep (se 2 (by rfl) ⟨934953, by rfl⟩ : syracuseStep 2493209 = 1869907) B1869907
theorem B3738455 : Blo 1661530 3738455 := bstep (se 1 (by rfl) ⟨2803841, by rfl⟩ : syracuseStep 3738455 = 5607683) B5607683
theorem B1870699 : Blo 1661530 1870699 := bstep (se 1 (by rfl) ⟨1403024, by rfl⟩ : syracuseStep 1870699 = 2806049) B2806049
theorem B2493323 : Blo 1661530 2493323 := bstep (se 1 (by rfl) ⟨1869992, by rfl⟩ : syracuseStep 2493323 = 3739985) B3739985
theorem B2493335 : Blo 1661530 2493335 := bstep (se 1 (by rfl) ⟨1870001, by rfl⟩ : syracuseStep 2493335 = 3740003) B3740003
theorem B3156889 : Blo 1661530 3156889 := bstep (se 2 (by rfl) ⟨1183833, by rfl⟩ : syracuseStep 3156889 = 2367667) B2367667
theorem B1895351 : Blo 1661530 1895351 := bstep (se 1 (by rfl) ⟨1421513, by rfl⟩ : syracuseStep 1895351 = 2843027) B2843027
theorem B1870807 : Blo 1661530 1870807 := bstep (se 1 (by rfl) ⟨1403105, by rfl⟩ : syracuseStep 1870807 = 2806211) B2806211
theorem B2493401 : Blo 1661530 2493401 := bstep (se 2 (by rfl) ⟨935025, by rfl⟩ : syracuseStep 2493401 = 1870051) B1870051
theorem B4492253 : Blo 1661530 4492253 := bstep (se 3 (by rfl) ⟨842297, by rfl⟩ : syracuseStep 4492253 = 1684595) B1684595
theorem B3738635 : Blo 1661530 3738635 := bstep (se 1 (by rfl) ⟨2803976, by rfl⟩ : syracuseStep 3738635 = 5607953) B5607953
theorem B3738689 : Blo 1661530 3738689 := bstep (se 2 (by rfl) ⟨1402008, by rfl⟩ : syracuseStep 3738689 = 2804017) B2804017
theorem B2493515 : Blo 1661530 2493515 := bstep (se 1 (by rfl) ⟨1870136, by rfl⟩ : syracuseStep 2493515 = 3740273) B3740273
theorem B2493527 : Blo 1661530 2493527 := bstep (se 1 (by rfl) ⟨1870145, by rfl⟩ : syracuseStep 2493527 = 3740291) B3740291
theorem B2493593 : Blo 1661530 2493593 := bstep (se 2 (by rfl) ⟨935097, by rfl⟩ : syracuseStep 2493593 = 1870195) B1870195
theorem B6311105 : Blo 1661530 6311105 := bstep (se 2 (by rfl) ⟨2366664, by rfl⟩ : syracuseStep 6311105 = 4733329) B4733329
theorem B18935045 : Blo 1661530 18935045 := bstep (se 4 (by rfl) ⟨1775160, by rfl⟩ : syracuseStep 18935045 = 3550321) B3550321
theorem B2493707 : Blo 1661530 2493707 := bstep (se 1 (by rfl) ⟨1870280, by rfl⟩ : syracuseStep 2493707 = 3740561) B3740561
theorem B2493719 : Blo 1661530 2493719 := bstep (se 1 (by rfl) ⟨1870289, by rfl⟩ : syracuseStep 2493719 = 3740579) B3740579
theorem B3738905 : Blo 1661530 3738905 := bstep (se 2 (by rfl) ⟨1402089, by rfl⟩ : syracuseStep 3738905 = 2804179) B2804179
theorem B3370291 : Blo 1661530 3370291 := bstep (se 1 (by rfl) ⟨2527718, by rfl⟩ : syracuseStep 3370291 = 5055437) B5055437
theorem B5991745 : Blo 1661530 5991745 := bstep (se 2 (by rfl) ⟨2246904, by rfl⟩ : syracuseStep 5991745 = 4493809) B4493809
theorem B2493785 : Blo 1661530 2493785 := bstep (se 2 (by rfl) ⟨935169, by rfl⟩ : syracuseStep 2493785 = 1870339) B1870339
theorem B3738995 : Blo 1661530 3738995 := bstep (se 1 (by rfl) ⟨2804246, by rfl⟩ : syracuseStep 3738995 = 5608493) B5608493
theorem B2805131 : Blo 1661530 2805131 := bstep (se 1 (by rfl) ⟨2103848, by rfl⟩ : syracuseStep 2805131 = 4207697) B4207697
theorem B3739031 : Blo 1661530 3739031 := bstep (se 1 (by rfl) ⟨2804273, by rfl⟩ : syracuseStep 3739031 = 5608547) B5608547
theorem B3599795 : Blo 1661530 3599795 := bstep (se 1 (by rfl) ⟨2699846, by rfl⟩ : syracuseStep 3599795 = 5399693) B5399693
theorem B3993035 : Blo 1661530 3993035 := bstep (se 1 (by rfl) ⟨2994776, by rfl⟩ : syracuseStep 3993035 = 5989553) B5989553
theorem B2493899 : Blo 1661530 2493899 := bstep (se 1 (by rfl) ⟨1870424, by rfl⟩ : syracuseStep 2493899 = 3740849) B3740849
theorem B2493911 : Blo 1661530 2493911 := bstep (se 1 (by rfl) ⟨1870433, by rfl⟩ : syracuseStep 2493911 = 3740867) B3740867
theorem B2805259 : Blo 1661530 2805259 := bstep (se 1 (by rfl) ⟨2103944, by rfl⟩ : syracuseStep 2805259 = 4207889) B4207889
theorem B2493977 : Blo 1661530 2493977 := bstep (se 2 (by rfl) ⟨935241, by rfl⟩ : syracuseStep 2493977 = 1870483) B1870483
theorem B3739211 : Blo 1661530 3739211 := bstep (se 1 (by rfl) ⟨2804408, by rfl⟩ : syracuseStep 3739211 = 5608817) B5608817
theorem B3739265 : Blo 1661530 3739265 := bstep (se 2 (by rfl) ⟨1402224, by rfl⟩ : syracuseStep 3739265 = 2804449) B2804449
theorem B2494091 : Blo 1661530 2494091 := bstep (se 1 (by rfl) ⟨1870568, by rfl⟩ : syracuseStep 2494091 = 3741137) B3741137
theorem B2494103 : Blo 1661530 2494103 := bstep (se 1 (by rfl) ⟨1870577, by rfl⟩ : syracuseStep 2494103 = 3741155) B3741155
theorem B2805401 : Blo 1661530 2805401 := bstep (se 2 (by rfl) ⟨1052025, by rfl⟩ : syracuseStep 2805401 = 2104051) B2104051
theorem B2494169 : Blo 1661530 2494169 := bstep (se 2 (by rfl) ⟨935313, by rfl⟩ : syracuseStep 2494169 = 1870627) B1870627
theorem B31960817 : Blo 1661530 31960817 := bstep (se 2 (by rfl) ⟨11985306, by rfl⟩ : syracuseStep 31960817 = 23970613) B23970613
theorem B2805529 : Blo 1661530 2805529 := bstep (se 2 (by rfl) ⟨1052073, by rfl⟩ : syracuseStep 2805529 = 2104147) B2104147
theorem B4206401 : Blo 1661530 4206401 := bstep (se 2 (by rfl) ⟨1577400, by rfl⟩ : syracuseStep 4206401 = 3154801) B3154801
theorem B2494283 : Blo 1661530 2494283 := bstep (se 1 (by rfl) ⟨1870712, by rfl⟩ : syracuseStep 2494283 = 3741425) B3741425
theorem B2494295 : Blo 1661530 2494295 := bstep (se 1 (by rfl) ⟨1870721, by rfl⟩ : syracuseStep 2494295 = 3741443) B3741443
theorem B3739481 : Blo 1661530 3739481 := bstep (se 2 (by rfl) ⟨1402305, by rfl⟩ : syracuseStep 3739481 = 2804611) B2804611
theorem B2494361 : Blo 1661530 2494361 := bstep (se 2 (by rfl) ⟨935385, by rfl⟩ : syracuseStep 2494361 = 1870771) B1870771
theorem B3739571 : Blo 1661530 3739571 := bstep (se 1 (by rfl) ⟨2804678, by rfl⟩ : syracuseStep 3739571 = 5609357) B5609357
theorem B3739607 : Blo 1661530 3739607 := bstep (se 1 (by rfl) ⟨2804705, by rfl⟩ : syracuseStep 3739607 = 5609411) B5609411
theorem B2494475 : Blo 1661530 2494475 := bstep (se 1 (by rfl) ⟨1870856, by rfl⟩ : syracuseStep 2494475 = 3741713) B3741713
theorem B9236497 : Blo 1661530 9236497 := bstep (se 2 (by rfl) ⟨3463686, by rfl⟩ : syracuseStep 9236497 = 6927373) B6927373
theorem B2494487 : Blo 1661530 2494487 := bstep (se 1 (by rfl) ⟨1870865, by rfl⟩ : syracuseStep 2494487 = 3741731) B3741731
theorem B2994251 : Blo 1661530 2994251 := bstep (se 1 (by rfl) ⟨2245688, by rfl⟩ : syracuseStep 2994251 = 4491377) B4491377
theorem B5992541 : Blo 1661530 5992541 := bstep (se 3 (by rfl) ⟨1123601, by rfl⟩ : syracuseStep 5992541 = 2247203) B2247203
theorem B9359491 : Blo 1661530 9359491 := bstep (se 1 (by rfl) ⟨7019618, by rfl⟩ : syracuseStep 9359491 = 14039237) B14039237
theorem B3739787 : Blo 1661530 3739787 := bstep (se 1 (by rfl) ⟨2804840, by rfl⟩ : syracuseStep 3739787 = 5609681) B5609681
theorem B3739841 : Blo 1661530 3739841 := bstep (se 2 (by rfl) ⟨1402440, by rfl⟩ : syracuseStep 3739841 = 2804881) B2804881
theorem B68227373 : Blo 1661530 68227373 := bstep (se 3 (by rfl) ⟨12792632, by rfl⟩ : syracuseStep 68227373 = 25585265) B25585265
theorem B4501811 : Blo 1661530 4501811 := bstep (se 1 (by rfl) ⟨3376358, by rfl⟩ : syracuseStep 4501811 = 6752717) B6752717
theorem B2806103 : Blo 1661530 2806103 := bstep (se 1 (by rfl) ⟨2104577, by rfl⟩ : syracuseStep 2806103 = 4209155) B4209155
theorem B4206937 : Blo 1661530 4206937 := bstep (se 2 (by rfl) ⟨1577601, by rfl⟩ : syracuseStep 4206937 = 3155203) B3155203
theorem B4321687 : Blo 1661530 4321687 := bstep (se 1 (by rfl) ⟨3241265, by rfl⟩ : syracuseStep 4321687 = 6482531) B6482531
theorem B3740057 : Blo 1661530 3740057 := bstep (se 2 (by rfl) ⟨1402521, by rfl⟩ : syracuseStep 3740057 = 2805043) B2805043
theorem B3551681 : Blo 1661530 3551681 := bstep (se 2 (by rfl) ⟨1331880, by rfl⟩ : syracuseStep 3551681 = 2663761) B2663761
theorem B2806231 : Blo 1661530 2806231 := bstep (se 1 (by rfl) ⟨2104673, by rfl⟩ : syracuseStep 2806231 = 4209347) B4209347
theorem B3740147 : Blo 1661530 3740147 := bstep (se 1 (by rfl) ⟨2805110, by rfl⟩ : syracuseStep 3740147 = 5610221) B5610221
theorem B7582211 : Blo 1661530 7582211 := bstep (se 1 (by rfl) ⟨5686658, by rfl⟩ : syracuseStep 7582211 = 11373317) B11373317
theorem B3740183 : Blo 1661530 3740183 := bstep (se 1 (by rfl) ⟨2805137, by rfl⟩ : syracuseStep 3740183 = 5610275) B5610275
theorem B6738497 : Blo 1661530 6738497 := bstep (se 2 (by rfl) ⟨2526936, by rfl⟩ : syracuseStep 6738497 = 5053873) B5053873
theorem B6312593 : Blo 1661530 6312593 := bstep (se 2 (by rfl) ⟨2367222, by rfl⟩ : syracuseStep 6312593 = 4734445) B4734445
theorem B1921687 : Blo 1661530 1921687 := bstep (se 1 (by rfl) ⟨1441265, by rfl⟩ : syracuseStep 1921687 = 2882531) B2882531
theorem B5608115 : Blo 1661530 5608115 := bstep (se 1 (by rfl) ⟨4206086, by rfl⟩ : syracuseStep 5608115 = 8412173) B8412173
theorem B3740363 : Blo 1661530 3740363 := bstep (se 1 (by rfl) ⟨2805272, by rfl⟩ : syracuseStep 3740363 = 5610545) B5610545
theorem B1774315 : Blo 1661530 1774315 := bstep (se 1 (by rfl) ⟨1330736, by rfl⟩ : syracuseStep 1774315 = 2661473) B2661473
theorem B3740417 : Blo 1661530 3740417 := bstep (se 2 (by rfl) ⟨1402656, by rfl⟩ : syracuseStep 3740417 = 2805313) B2805313
theorem B7099139 : Blo 1661530 7099139 := bstep (se 1 (by rfl) ⟨5324354, by rfl⟩ : syracuseStep 7099139 = 10648709) B10648709
theorem B2528011 : Blo 1661530 2528011 := bstep (se 1 (by rfl) ⟨1896008, by rfl⟩ : syracuseStep 2528011 = 3792017) B3792017
theorem B4494145 : Blo 1661530 4494145 := bstep (se 2 (by rfl) ⟨1685304, by rfl⟩ : syracuseStep 4494145 = 3370609) B3370609
theorem B3789719 : Blo 1661530 3789719 := bstep (se 1 (by rfl) ⟨2842289, by rfl⟩ : syracuseStep 3789719 = 5684579) B5684579
theorem B5608385 : Blo 1661530 5608385 := bstep (se 2 (by rfl) ⟨2103144, by rfl⟩ : syracuseStep 5608385 = 4206289) B4206289
theorem B3740633 : Blo 1661530 3740633 := bstep (se 2 (by rfl) ⟨1402737, by rfl⟩ : syracuseStep 3740633 = 2805475) B2805475
theorem B3740723 : Blo 1661530 3740723 := bstep (se 1 (by rfl) ⟨2805542, by rfl⟩ : syracuseStep 3740723 = 5611085) B5611085
theorem B9466955 : Blo 1661530 9466955 := bstep (se 1 (by rfl) ⟨7100216, by rfl⟩ : syracuseStep 9466955 = 14200433) B14200433
theorem B3740759 : Blo 1661530 3740759 := bstep (se 1 (by rfl) ⟨2805569, by rfl⟩ : syracuseStep 3740759 = 5611139) B5611139
theorem B7099481 : Blo 1661530 7099481 := bstep (se 2 (by rfl) ⟨2662305, by rfl⟩ : syracuseStep 7099481 = 5324611) B5324611
theorem B6313049 : Blo 1661530 6313049 := bstep (se 2 (by rfl) ⟨2367393, by rfl⟩ : syracuseStep 6313049 = 4734787) B4734787
theorem B4732121 : Blo 1661530 4732121 := bstep (se 2 (by rfl) ⟨1774545, by rfl⟩ : syracuseStep 4732121 = 3549091) B3549091
theorem B3740939 : Blo 1661530 3740939 := bstep (se 1 (by rfl) ⟨2805704, by rfl⟩ : syracuseStep 3740939 = 5611409) B5611409
theorem B6313261 : Blo 1661530 6313261 := bstep (se 3 (by rfl) ⟨1183736, by rfl⟩ : syracuseStep 6313261 = 2367473) B2367473
theorem B3740993 : Blo 1661530 3740993 := bstep (se 2 (by rfl) ⟨1402872, by rfl⟩ : syracuseStep 3740993 = 2805745) B2805745
theorem B8418653 : Blo 1661530 8418653 := bstep (se 3 (by rfl) ⟨1578497, by rfl⟩ : syracuseStep 8418653 = 3156995) B3156995
theorem B4617623 : Blo 1661530 4617623 := bstep (se 1 (by rfl) ⟨3463217, by rfl⟩ : syracuseStep 4617623 = 6926435) B6926435
theorem B4208051 : Blo 1661530 4208051 := bstep (se 1 (by rfl) ⟨3156038, by rfl⟩ : syracuseStep 4208051 = 6312077) B6312077
theorem B3036631 : Blo 1661530 3036631 := bstep (se 1 (by rfl) ⟨2277473, by rfl⟩ : syracuseStep 3036631 = 4554947) B4554947
theorem B5608925 : Blo 1661530 5608925 := bstep (se 3 (by rfl) ⟨1051673, by rfl⟩ : syracuseStep 5608925 = 2103347) B2103347
theorem B3741209 : Blo 1661530 3741209 := bstep (se 2 (by rfl) ⟨1402953, by rfl⟩ : syracuseStep 3741209 = 2805907) B2805907
theorem B20215331 : Blo 1661530 20215331 := bstep (se 1 (by rfl) ⟨15161498, by rfl⟩ : syracuseStep 20215331 = 30322997) B30322997
theorem B1775191 : Blo 1661530 1775191 := bstep (se 1 (by rfl) ⟨1331393, by rfl⟩ : syracuseStep 1775191 = 2662787) B2662787
theorem B6313565 : Blo 1661530 6313565 := bstep (se 3 (by rfl) ⟨1183793, by rfl⟩ : syracuseStep 6313565 = 2367587) B2367587
theorem B3741299 : Blo 1661530 3741299 := bstep (se 1 (by rfl) ⟨2805974, by rfl⟩ : syracuseStep 3741299 = 5611949) B5611949
theorem B7583377 : Blo 1661530 7583377 := bstep (se 2 (by rfl) ⟨2843766, by rfl⟩ : syracuseStep 7583377 = 5687533) B5687533
theorem B3741335 : Blo 1661530 3741335 := bstep (se 1 (by rfl) ⟨2806001, by rfl⟩ : syracuseStep 3741335 = 5612003) B5612003
theorem B4208345 : Blo 1661530 4208345 := bstep (se 2 (by rfl) ⟨1578129, by rfl⟩ : syracuseStep 4208345 = 3156259) B3156259
theorem B3741515 : Blo 1661530 3741515 := bstep (se 1 (by rfl) ⟨2806136, by rfl⟩ : syracuseStep 3741515 = 5612273) B5612273
theorem B4552537 : Blo 1661530 4552537 := bstep (se 2 (by rfl) ⟨1707201, by rfl⟩ : syracuseStep 4552537 = 3414403) B3414403
theorem B4495193 : Blo 1661530 4495193 := bstep (se 2 (by rfl) ⟨1685697, by rfl⟩ : syracuseStep 4495193 = 3371395) B3371395
theorem B3741569 : Blo 1661530 3741569 := bstep (se 2 (by rfl) ⟨1403088, by rfl⟩ : syracuseStep 3741569 = 2806177) B2806177
theorem B3790795 : Blo 1661530 3790795 := bstep (se 1 (by rfl) ⟨2843096, by rfl⟩ : syracuseStep 3790795 = 5686193) B5686193
theorem B1775639 : Blo 1661530 1775639 := bstep (se 1 (by rfl) ⟨1331729, by rfl⟩ : syracuseStep 1775639 = 2663459) B2663459
theorem B14194723 : Blo 1661530 14194723 := bstep (se 1 (by rfl) ⟨10646042, by rfl⟩ : syracuseStep 14194723 = 21292085) B21292085
theorem B3741785 : Blo 1661530 3741785 := bstep (se 2 (by rfl) ⟨1403169, by rfl⟩ : syracuseStep 3741785 = 2806339) B2806339
theorem B10647683 : Blo 1661530 10647683 := bstep (se 1 (by rfl) ⟨7985762, by rfl⟩ : syracuseStep 10647683 = 15971525) B15971525
theorem B7985303 : Blo 1661530 7985303 := bstep (se 1 (by rfl) ⟨5988977, by rfl⟩ : syracuseStep 7985303 = 11977955) B11977955
theorem B2103499 : Blo 1661530 2103499 := bstep (se 1 (by rfl) ⟨1577624, by rfl⟩ : syracuseStep 2103499 = 3155249) B3155249
theorem B2464139 : Blo 1661530 2464139 := bstep (se 1 (by rfl) ⟨1848104, by rfl⟩ : syracuseStep 2464139 = 3696209) B3696209
theorem B4733387 : Blo 1661530 4733387 := bstep (se 1 (by rfl) ⟨3550040, by rfl⟩ : syracuseStep 4733387 = 7100081) B7100081
theorem B1997335 : Blo 1661530 1997335 := bstep (se 1 (by rfl) ⟨1498001, by rfl⟩ : syracuseStep 1997335 = 2996003) B2996003
theorem B5610059 : Blo 1661530 5610059 := bstep (se 1 (by rfl) ⟨4207544, by rfl⟩ : syracuseStep 5610059 = 8415089) B8415089
theorem B1661547 : Blo 1661530 1661547 := bstep (se 1 (by rfl) ⟨1246160, by rfl⟩ : syracuseStep 1661547 = 2492321) B2492321
theorem B1661559 : Blo 1661530 1661559 := bstep (se 1 (by rfl) ⟨1246169, by rfl⟩ : syracuseStep 1661559 = 2492339) B2492339
theorem B1661579 : Blo 1661530 1661579 := bstep (se 1 (by rfl) ⟨1246184, by rfl⟩ : syracuseStep 1661579 = 2492369) B2492369
theorem B1661591 : Blo 1661530 1661591 := bstep (se 1 (by rfl) ⟨1246193, by rfl⟩ : syracuseStep 1661591 = 2492387) B2492387
theorem B8985239 : Blo 1661530 8985239 := bstep (se 1 (by rfl) ⟨6738929, by rfl⟩ : syracuseStep 8985239 = 13477859) B13477859
theorem B1661611 : Blo 1661530 1661611 := bstep (se 1 (by rfl) ⟨1246208, by rfl⟩ : syracuseStep 1661611 = 2492417) B2492417
theorem B1661623 : Blo 1661530 1661623 := bstep (se 1 (by rfl) ⟨1246217, by rfl⟩ : syracuseStep 1661623 = 2492435) B2492435
theorem B7101121 : Blo 1661530 7101121 := bstep (se 2 (by rfl) ⟨2662920, by rfl⟩ : syracuseStep 7101121 = 5325841) B5325841
theorem B1661643 : Blo 1661530 1661643 := bstep (se 1 (by rfl) ⟨1246232, by rfl⟩ : syracuseStep 1661643 = 2492465) B2492465
theorem B1661655 : Blo 1661530 1661655 := bstep (se 1 (by rfl) ⟨1246241, by rfl⟩ : syracuseStep 1661655 = 2492483) B2492483
theorem B1661675 : Blo 1661530 1661675 := bstep (se 1 (by rfl) ⟨1246256, by rfl⟩ : syracuseStep 1661675 = 2492513) B2492513
theorem B1661687 : Blo 1661530 1661687 := bstep (se 1 (by rfl) ⟨1246265, by rfl⟩ : syracuseStep 1661687 = 2492531) B2492531
theorem B1661707 : Blo 1661530 1661707 := bstep (se 1 (by rfl) ⟨1246280, by rfl⟩ : syracuseStep 1661707 = 2492561) B2492561
theorem B1661719 : Blo 1661530 1661719 := bstep (se 1 (by rfl) ⟨1246289, by rfl⟩ : syracuseStep 1661719 = 2492579) B2492579
theorem B1661739 : Blo 1661530 1661739 := bstep (se 1 (by rfl) ⟨1246304, by rfl⟩ : syracuseStep 1661739 = 2492609) B2492609
theorem B17054509 : Blo 1661530 17054509 := bstep (se 3 (by rfl) ⟨3197720, by rfl⟩ : syracuseStep 17054509 = 6395441) B6395441
theorem B1661751 : Blo 1661530 1661751 := bstep (se 1 (by rfl) ⟨1246313, by rfl⟩ : syracuseStep 1661751 = 2492627) B2492627
theorem B1661771 : Blo 1661530 1661771 := bstep (se 1 (by rfl) ⟨1246328, by rfl⟩ : syracuseStep 1661771 = 2492657) B2492657
theorem B1661783 : Blo 1661530 1661783 := bstep (se 1 (by rfl) ⟨1246337, by rfl⟩ : syracuseStep 1661783 = 2492675) B2492675
theorem B5610329 : Blo 1661530 5610329 := bstep (se 2 (by rfl) ⟨2103873, by rfl⟩ : syracuseStep 5610329 = 4207747) B4207747
theorem B11369317 : Blo 1661530 11369317 := bstep (se 4 (by rfl) ⟨1065873, by rfl⟩ : syracuseStep 11369317 = 2131747) B2131747
theorem B1661803 : Blo 1661530 1661803 := bstep (se 1 (by rfl) ⟨1246352, by rfl⟩ : syracuseStep 1661803 = 2492705) B2492705
theorem B1661815 : Blo 1661530 1661815 := bstep (se 1 (by rfl) ⟨1246361, by rfl⟩ : syracuseStep 1661815 = 2492723) B2492723
theorem B1661835 : Blo 1661530 1661835 := bstep (se 1 (by rfl) ⟨1246376, by rfl⟩ : syracuseStep 1661835 = 2492753) B2492753
theorem B1661847 : Blo 1661530 1661847 := bstep (se 1 (by rfl) ⟨1246385, by rfl⟩ : syracuseStep 1661847 = 2492771) B2492771
theorem B1661867 : Blo 1661530 1661867 := bstep (se 1 (by rfl) ⟨1246400, by rfl⟩ : syracuseStep 1661867 = 2492801) B2492801
theorem B1661879 : Blo 1661530 1661879 := bstep (se 1 (by rfl) ⟨1246409, by rfl⟩ : syracuseStep 1661879 = 2492819) B2492819
theorem B1661899 : Blo 1661530 1661899 := bstep (se 1 (by rfl) ⟨1246424, by rfl⟩ : syracuseStep 1661899 = 2492849) B2492849
theorem B1661911 : Blo 1661530 1661911 := bstep (se 1 (by rfl) ⟨1246433, by rfl⟩ : syracuseStep 1661911 = 2492867) B2492867
theorem B2366425 : Blo 1661530 2366425 := bstep (se 2 (by rfl) ⟨887409, by rfl⟩ : syracuseStep 2366425 = 1774819) B1774819
theorem B1661931 : Blo 1661530 1661931 := bstep (se 1 (by rfl) ⟨1246448, by rfl⟩ : syracuseStep 1661931 = 2492897) B2492897
theorem B1661943 : Blo 1661530 1661943 := bstep (se 1 (by rfl) ⟨1246457, by rfl⟩ : syracuseStep 1661943 = 2492915) B2492915
theorem B1661963 : Blo 1661530 1661963 := bstep (se 1 (by rfl) ⟨1246472, by rfl⟩ : syracuseStep 1661963 = 2492945) B2492945
theorem B1661975 : Blo 1661530 1661975 := bstep (se 1 (by rfl) ⟨1246481, by rfl⟩ : syracuseStep 1661975 = 2492963) B2492963
theorem B1661995 : Blo 1661530 1661995 := bstep (se 1 (by rfl) ⟨1246496, by rfl⟩ : syracuseStep 1661995 = 2492993) B2492993
theorem B1662007 : Blo 1661530 1662007 := bstep (se 1 (by rfl) ⟨1246505, by rfl⟩ : syracuseStep 1662007 = 2493011) B2493011
theorem B1662027 : Blo 1661530 1662027 := bstep (se 1 (by rfl) ⟨1246520, by rfl⟩ : syracuseStep 1662027 = 2493041) B2493041
theorem B1662039 : Blo 1661530 1662039 := bstep (se 1 (by rfl) ⟨1246529, by rfl⟩ : syracuseStep 1662039 = 2493059) B2493059
theorem B1662059 : Blo 1661530 1662059 := bstep (se 1 (by rfl) ⟨1246544, by rfl⟩ : syracuseStep 1662059 = 2493089) B2493089
theorem B1662071 : Blo 1661530 1662071 := bstep (se 1 (by rfl) ⟨1246553, by rfl⟩ : syracuseStep 1662071 = 2493107) B2493107
theorem B1662091 : Blo 1661530 1662091 := bstep (se 1 (by rfl) ⟨1246568, by rfl⟩ : syracuseStep 1662091 = 2493137) B2493137
theorem B1662103 : Blo 1661530 1662103 := bstep (se 1 (by rfl) ⟨1246577, by rfl⟩ : syracuseStep 1662103 = 2493155) B2493155
theorem B2104471 : Blo 1661530 2104471 := bstep (se 1 (by rfl) ⟨1578353, by rfl⟩ : syracuseStep 2104471 = 3156707) B3156707
theorem B51199127 : Blo 1661530 51199127 := bstep (se 1 (by rfl) ⟨38399345, by rfl⟩ : syracuseStep 51199127 = 76798691) B76798691
theorem B1662123 : Blo 1661530 1662123 := bstep (se 1 (by rfl) ⟨1246592, by rfl⟩ : syracuseStep 1662123 = 2493185) B2493185
theorem B1662135 : Blo 1661530 1662135 := bstep (se 1 (by rfl) ⟨1246601, by rfl⟩ : syracuseStep 1662135 = 2493203) B2493203
theorem B1662155 : Blo 1661530 1662155 := bstep (se 1 (by rfl) ⟨1246616, by rfl⟩ : syracuseStep 1662155 = 2493233) B2493233
theorem B1662167 : Blo 1661530 1662167 := bstep (se 1 (by rfl) ⟨1246625, by rfl⟩ : syracuseStep 1662167 = 2493251) B2493251
theorem B1662187 : Blo 1661530 1662187 := bstep (se 1 (by rfl) ⟨1246640, by rfl⟩ : syracuseStep 1662187 = 2493281) B2493281
theorem B1662199 : Blo 1661530 1662199 := bstep (se 1 (by rfl) ⟨1246649, by rfl⟩ : syracuseStep 1662199 = 2493299) B2493299
theorem B1662219 : Blo 1661530 1662219 := bstep (se 1 (by rfl) ⟨1246664, by rfl⟩ : syracuseStep 1662219 = 2493329) B2493329
theorem B1662231 : Blo 1661530 1662231 := bstep (se 1 (by rfl) ⟨1246673, by rfl⟩ : syracuseStep 1662231 = 2493347) B2493347
theorem B1662251 : Blo 1661530 1662251 := bstep (se 1 (by rfl) ⟨1246688, by rfl⟩ : syracuseStep 1662251 = 2493377) B2493377
theorem B1662263 : Blo 1661530 1662263 := bstep (se 1 (by rfl) ⟨1246697, by rfl⟩ : syracuseStep 1662263 = 2493395) B2493395
theorem B1662283 : Blo 1661530 1662283 := bstep (se 1 (by rfl) ⟨1246712, by rfl⟩ : syracuseStep 1662283 = 2493425) B2493425
theorem B1662295 : Blo 1661530 1662295 := bstep (se 1 (by rfl) ⟨1246721, by rfl⟩ : syracuseStep 1662295 = 2493443) B2493443
theorem B1662315 : Blo 1661530 1662315 := bstep (se 1 (by rfl) ⟨1246736, by rfl⟩ : syracuseStep 1662315 = 2493473) B2493473
theorem B1662327 : Blo 1661530 1662327 := bstep (se 1 (by rfl) ⟨1246745, by rfl⟩ : syracuseStep 1662327 = 2493491) B2493491
theorem B1662347 : Blo 1661530 1662347 := bstep (se 1 (by rfl) ⟨1246760, by rfl⟩ : syracuseStep 1662347 = 2493521) B2493521
theorem B7396753 : Blo 1661530 7396753 := bstep (se 2 (by rfl) ⟨2773782, by rfl⟩ : syracuseStep 7396753 = 5547565) B5547565
theorem B1662359 : Blo 1661530 1662359 := bstep (se 1 (by rfl) ⟨1246769, by rfl⟩ : syracuseStep 1662359 = 2493539) B2493539
theorem B1662379 : Blo 1661530 1662379 := bstep (se 1 (by rfl) ⟨1246784, by rfl⟩ : syracuseStep 1662379 = 2493569) B2493569
theorem B27336113 : Blo 1661530 27336113 := bstep (se 2 (by rfl) ⟨10251042, by rfl⟩ : syracuseStep 27336113 = 20502085) B20502085
theorem B1662391 : Blo 1661530 1662391 := bstep (se 1 (by rfl) ⟨1246793, by rfl⟩ : syracuseStep 1662391 = 2493587) B2493587
theorem B1662411 : Blo 1661530 1662411 := bstep (se 1 (by rfl) ⟨1246808, by rfl⟩ : syracuseStep 1662411 = 2493617) B2493617
theorem B1662423 : Blo 1661530 1662423 := bstep (se 1 (by rfl) ⟨1246817, by rfl⟩ : syracuseStep 1662423 = 2493635) B2493635
theorem B1662443 : Blo 1661530 1662443 := bstep (se 1 (by rfl) ⟨1246832, by rfl⟩ : syracuseStep 1662443 = 2493665) B2493665
theorem B1662455 : Blo 1661530 1662455 := bstep (se 1 (by rfl) ⟨1246841, by rfl⟩ : syracuseStep 1662455 = 2493683) B2493683
theorem B1662475 : Blo 1661530 1662475 := bstep (se 1 (by rfl) ⟨1246856, by rfl⟩ : syracuseStep 1662475 = 2493713) B2493713
theorem B1662487 : Blo 1661530 1662487 := bstep (se 1 (by rfl) ⟨1246865, by rfl⟩ : syracuseStep 1662487 = 2493731) B2493731
theorem B5611031 : Blo 1661530 5611031 := bstep (se 1 (by rfl) ⟨4208273, by rfl⟩ : syracuseStep 5611031 = 8416547) B8416547
theorem B1662507 : Blo 1661530 1662507 := bstep (se 1 (by rfl) ⟨1246880, by rfl⟩ : syracuseStep 1662507 = 2493761) B2493761
theorem B1662519 : Blo 1661530 1662519 := bstep (se 1 (by rfl) ⟨1246889, by rfl⟩ : syracuseStep 1662519 = 2493779) B2493779
theorem B1662539 : Blo 1661530 1662539 := bstep (se 1 (by rfl) ⟨1246904, by rfl⟩ : syracuseStep 1662539 = 2493809) B2493809
theorem B1662551 : Blo 1661530 1662551 := bstep (se 1 (by rfl) ⟨1246913, by rfl⟩ : syracuseStep 1662551 = 2493827) B2493827
theorem B1662571 : Blo 1661530 1662571 := bstep (se 1 (by rfl) ⟨1246928, by rfl⟩ : syracuseStep 1662571 = 2493857) B2493857
theorem B1662583 : Blo 1661530 1662583 := bstep (se 1 (by rfl) ⟨1246937, by rfl⟩ : syracuseStep 1662583 = 2493875) B2493875
theorem B1662603 : Blo 1661530 1662603 := bstep (se 1 (by rfl) ⟨1246952, by rfl⟩ : syracuseStep 1662603 = 2493905) B2493905
theorem B1662615 : Blo 1661530 1662615 := bstep (se 1 (by rfl) ⟨1246961, by rfl⟩ : syracuseStep 1662615 = 2493923) B2493923
theorem B1662635 : Blo 1661530 1662635 := bstep (se 1 (by rfl) ⟨1246976, by rfl⟩ : syracuseStep 1662635 = 2493953) B2493953
theorem B9469619 : Blo 1661530 9469619 := bstep (se 1 (by rfl) ⟨7102214, by rfl⟩ : syracuseStep 9469619 = 14204429) B14204429
theorem B1662647 : Blo 1661530 1662647 := bstep (se 1 (by rfl) ⟨1246985, by rfl⟩ : syracuseStep 1662647 = 2493971) B2493971
theorem B1662667 : Blo 1661530 1662667 := bstep (se 1 (by rfl) ⟨1247000, by rfl⟩ : syracuseStep 1662667 = 2494001) B2494001
theorem B1662679 : Blo 1661530 1662679 := bstep (se 1 (by rfl) ⟨1247009, by rfl⟩ : syracuseStep 1662679 = 2494019) B2494019
theorem B1662699 : Blo 1661530 1662699 := bstep (se 1 (by rfl) ⟨1247024, by rfl⟩ : syracuseStep 1662699 = 2494049) B2494049
theorem B38395633 : Blo 1661530 38395633 := bstep (se 2 (by rfl) ⟨14398362, by rfl⟩ : syracuseStep 38395633 = 28796725) B28796725
theorem B1662711 : Blo 1661530 1662711 := bstep (se 1 (by rfl) ⟨1247033, by rfl⟩ : syracuseStep 1662711 = 2494067) B2494067
theorem B1662731 : Blo 1661530 1662731 := bstep (se 1 (by rfl) ⟨1247048, by rfl⟩ : syracuseStep 1662731 = 2494097) B2494097
theorem B1662743 : Blo 1661530 1662743 := bstep (se 1 (by rfl) ⟨1247057, by rfl⟩ : syracuseStep 1662743 = 2494115) B2494115
theorem B1662763 : Blo 1661530 1662763 := bstep (se 1 (by rfl) ⟨1247072, by rfl⟩ : syracuseStep 1662763 = 2494145) B2494145
theorem B1662775 : Blo 1661530 1662775 := bstep (se 1 (by rfl) ⟨1247081, by rfl⟩ : syracuseStep 1662775 = 2494163) B2494163
theorem B1662795 : Blo 1661530 1662795 := bstep (se 1 (by rfl) ⟨1247096, by rfl⟩ : syracuseStep 1662795 = 2494193) B2494193
theorem B1662807 : Blo 1661530 1662807 := bstep (se 1 (by rfl) ⟨1247105, by rfl⟩ : syracuseStep 1662807 = 2494211) B2494211
theorem B1662827 : Blo 1661530 1662827 := bstep (se 1 (by rfl) ⟨1247120, by rfl⟩ : syracuseStep 1662827 = 2494241) B2494241
theorem B1662839 : Blo 1661530 1662839 := bstep (se 1 (by rfl) ⟨1247129, by rfl⟩ : syracuseStep 1662839 = 2494259) B2494259
theorem B1662859 : Blo 1661530 1662859 := bstep (se 1 (by rfl) ⟨1247144, by rfl⟩ : syracuseStep 1662859 = 2494289) B2494289
theorem B2400139 : Blo 1661530 2400139 := bstep (se 1 (by rfl) ⟨1800104, by rfl⟩ : syracuseStep 2400139 = 3600209) B3600209
theorem B1662871 : Blo 1661530 1662871 := bstep (se 1 (by rfl) ⟨1247153, by rfl⟩ : syracuseStep 1662871 = 2494307) B2494307
theorem B1662891 : Blo 1661530 1662891 := bstep (se 1 (by rfl) ⟨1247168, by rfl⟩ : syracuseStep 1662891 = 2494337) B2494337
theorem B1662903 : Blo 1661530 1662903 := bstep (se 1 (by rfl) ⟨1247177, by rfl⟩ : syracuseStep 1662903 = 2494355) B2494355
theorem B1662923 : Blo 1661530 1662923 := bstep (se 1 (by rfl) ⟨1247192, by rfl⟩ : syracuseStep 1662923 = 2494385) B2494385
theorem B1662935 : Blo 1661530 1662935 := bstep (se 1 (by rfl) ⟨1247201, by rfl⟩ : syracuseStep 1662935 = 2494403) B2494403
theorem B8413145 : Blo 1661530 8413145 := bstep (se 2 (by rfl) ⟨3154929, by rfl⟩ : syracuseStep 8413145 = 6309859) B6309859
theorem B1662955 : Blo 1661530 1662955 := bstep (se 1 (by rfl) ⟨1247216, by rfl⟩ : syracuseStep 1662955 = 2494433) B2494433
theorem B1662983 : Blo 1661530 1662983 := bstep (se 1 (by rfl) ⟨1247237, by rfl⟩ : syracuseStep 1662983 = 2494475) B2494475
theorem B1662991 : Blo 1661530 1662991 := bstep (se 1 (by rfl) ⟨1247243, by rfl⟩ : syracuseStep 1662991 = 2494487) B2494487
theorem B4735037 : Blo 1661530 4735037 := bstep (se 3 (by rfl) ⟨887819, by rfl⟩ : syracuseStep 4735037 = 1775639) B1775639
theorem B2367787 : Blo 1661530 2367787 := bstep (se 1 (by rfl) ⟨1775840, by rfl⟩ : syracuseStep 2367787 = 3551681) B3551681
theorem B5054807 : Blo 1661530 5054807 := bstep (se 1 (by rfl) ⟨3791105, by rfl⟩ : syracuseStep 5054807 = 7582211) B7582211
theorem B2663113 : Blo 1661530 2663113 := bstep (se 2 (by rfl) ⟨998667, by rfl⟩ : syracuseStep 2663113 = 1997335) B1997335
theorem B21300083 : Blo 1661530 21300083 := bstep (se 1 (by rfl) ⟨15975062, by rfl⟩ : syracuseStep 21300083 = 31950125) B31950125
theorem B5612435 : Blo 1661530 5612435 := bstep (se 1 (by rfl) ⟨4209326, by rfl⟩ : syracuseStep 5612435 = 8418653) B8418653
theorem B13476887 : Blo 1661530 13476887 := bstep (se 1 (by rfl) ⟨10107665, by rfl⟩ : syracuseStep 13476887 = 20215331) B20215331
theorem B6571037 : Blo 1661530 6571037 := bstep (se 3 (by rfl) ⟨1232069, by rfl⟩ : syracuseStep 6571037 = 2464139) B2464139
theorem B2245819 : Blo 1661530 2245819 := bstep (se 1 (by rfl) ⟨1684364, by rfl⟩ : syracuseStep 2245819 = 3368729) B3368729
theorem B9463013 : Blo 1661530 9463013 := bstep (se 4 (by rfl) ⟨887157, by rfl⟩ : syracuseStep 9463013 = 1774315) B1774315
theorem B17974885 : Blo 1661530 17974885 := bstep (se 4 (by rfl) ⟨1685145, by rfl⟩ : syracuseStep 17974885 = 3370291) B3370291
theorem B3155591 : Blo 1661530 3155591 := bstep (se 1 (by rfl) ⟨2366693, by rfl⟩ : syracuseStep 3155591 = 4733387) B4733387
theorem B3950227 : Blo 1661530 3950227 := bstep (se 1 (by rfl) ⟨2962670, by rfl⟩ : syracuseStep 3950227 = 5925341) B5925341
theorem B7988993 : Blo 1661530 7988993 := bstep (se 2 (by rfl) ⟨2995872, by rfl⟩ : syracuseStep 7988993 = 5991745) B5991745
theorem B6309647 : Blo 1661530 6309647 := bstep (se 1 (by rfl) ⟨4732235, by rfl⟩ : syracuseStep 6309647 = 9464471) B9464471
theorem B1869583 : Blo 1661530 1869583 := bstep (se 1 (by rfl) ⟨1402187, by rfl⟩ : syracuseStep 1869583 = 2804375) B2804375
theorem B5990159 : Blo 1661530 5990159 := bstep (se 1 (by rfl) ⟨4492619, by rfl⟩ : syracuseStep 5990159 = 8985239) B8985239
theorem B2492303 : Blo 1661530 2492303 := bstep (se 1 (by rfl) ⟨1869227, by rfl⟩ : syracuseStep 2492303 = 3738455) B3738455
theorem B2492345 : Blo 1661530 2492345 := bstep (se 2 (by rfl) ⟨934629, by rfl⟩ : syracuseStep 2492345 = 1869259) B1869259
theorem B4048841 : Blo 1661530 4048841 := bstep (se 2 (by rfl) ⟨1518315, by rfl⟩ : syracuseStep 4048841 = 3036631) B3036631
theorem B2492423 : Blo 1661530 2492423 := bstep (se 1 (by rfl) ⟨1869317, by rfl⟩ : syracuseStep 2492423 = 3738635) B3738635
theorem B2492459 : Blo 1661530 2492459 := bstep (se 1 (by rfl) ⟨1869344, by rfl⟩ : syracuseStep 2492459 = 3738689) B3738689
theorem B2492489 : Blo 1661530 2492489 := bstep (se 2 (by rfl) ⟨934683, by rfl⟩ : syracuseStep 2492489 = 1869367) B1869367
theorem B2492603 : Blo 1661530 2492603 := bstep (se 1 (by rfl) ⟨1869452, by rfl⟩ : syracuseStep 2492603 = 3738905) B3738905
theorem B10111169 : Blo 1661530 10111169 := bstep (se 2 (by rfl) ⟨3791688, by rfl⟩ : syracuseStep 10111169 = 7583377) B7583377
theorem B2492663 : Blo 1661530 2492663 := bstep (se 1 (by rfl) ⟨1869497, by rfl⟩ : syracuseStep 2492663 = 3738995) B3738995
theorem B1870087 : Blo 1661530 1870087 := bstep (se 1 (by rfl) ⟨1402565, by rfl⟩ : syracuseStep 1870087 = 2805131) B2805131
theorem B2492687 : Blo 1661530 2492687 := bstep (se 1 (by rfl) ⟨1869515, by rfl⟩ : syracuseStep 2492687 = 3739031) B3739031
theorem B12618017 : Blo 1661530 12618017 := bstep (se 2 (by rfl) ⟨4731756, by rfl⟩ : syracuseStep 12618017 = 9463513) B9463513
theorem B2492729 : Blo 1661530 2492729 := bstep (se 2 (by rfl) ⟨934773, by rfl⟩ : syracuseStep 2492729 = 1869547) B1869547
theorem B51194177 : Blo 1661530 51194177 := bstep (se 2 (by rfl) ⟨19197816, by rfl⟩ : syracuseStep 51194177 = 38395633) B38395633
theorem B2492807 : Blo 1661530 2492807 := bstep (se 1 (by rfl) ⟨1869605, by rfl⟩ : syracuseStep 2492807 = 3739211) B3739211
theorem B2492843 : Blo 1661530 2492843 := bstep (se 1 (by rfl) ⟨1869632, by rfl⟩ : syracuseStep 2492843 = 3739265) B3739265
theorem B1870267 : Blo 1661530 1870267 := bstep (se 1 (by rfl) ⟨1402700, by rfl⟩ : syracuseStep 1870267 = 2805401) B2805401
theorem B2492873 : Blo 1661530 2492873 := bstep (se 2 (by rfl) ⟨934827, by rfl⟩ : syracuseStep 2492873 = 1869655) B1869655
theorem B2804267 : Blo 1661530 2804267 := bstep (se 1 (by rfl) ⟨2103200, by rfl⟩ : syracuseStep 2804267 = 4206401) B4206401
theorem B2492987 : Blo 1661530 2492987 := bstep (se 1 (by rfl) ⟨1869740, by rfl⟩ : syracuseStep 2492987 = 3739481) B3739481
theorem B2493047 : Blo 1661530 2493047 := bstep (se 1 (by rfl) ⟨1869785, by rfl⟩ : syracuseStep 2493047 = 3739571) B3739571
theorem B2493071 : Blo 1661530 2493071 := bstep (se 1 (by rfl) ⟨1869803, by rfl⟩ : syracuseStep 2493071 = 3739607) B3739607
theorem B2493113 : Blo 1661530 2493113 := bstep (se 2 (by rfl) ⟨934917, by rfl⟩ : syracuseStep 2493113 = 1869835) B1869835
theorem B12315329 : Blo 1661530 12315329 := bstep (se 2 (by rfl) ⟨4618248, by rfl⟩ : syracuseStep 12315329 = 9236497) B9236497
theorem B18926297 : Blo 1661530 18926297 := bstep (se 2 (by rfl) ⟨7097361, by rfl⟩ : syracuseStep 18926297 = 14194723) B14194723
theorem B2493191 : Blo 1661530 2493191 := bstep (se 1 (by rfl) ⟨1869893, by rfl⟩ : syracuseStep 2493191 = 3739787) B3739787
theorem B2493227 : Blo 1661530 2493227 := bstep (se 1 (by rfl) ⟨1869920, by rfl⟩ : syracuseStep 2493227 = 3739841) B3739841
theorem B2493257 : Blo 1661530 2493257 := bstep (se 2 (by rfl) ⟨934971, by rfl⟩ : syracuseStep 2493257 = 1869943) B1869943
theorem B12479321 : Blo 1661530 12479321 := bstep (se 2 (by rfl) ⟨4679745, by rfl⟩ : syracuseStep 12479321 = 9359491) B9359491
theorem B45484915 : Blo 1661530 45484915 := bstep (se 1 (by rfl) ⟨34113686, by rfl⟩ : syracuseStep 45484915 = 68227373) B68227373
theorem B5991283 : Blo 1661530 5991283 := bstep (se 1 (by rfl) ⟨4493462, by rfl⟩ : syracuseStep 5991283 = 8986925) B8986925
theorem B3001207 : Blo 1661530 3001207 := bstep (se 1 (by rfl) ⟨2250905, by rfl⟩ : syracuseStep 3001207 = 4501811) B4501811
theorem B1870735 : Blo 1661530 1870735 := bstep (se 1 (by rfl) ⟨1403051, by rfl⟩ : syracuseStep 1870735 = 2806103) B2806103
theorem B2804665 : Blo 1661530 2804665 := bstep (se 2 (by rfl) ⟨1051749, by rfl⟩ : syracuseStep 2804665 = 2103499) B2103499
theorem B2493371 : Blo 1661530 2493371 := bstep (se 1 (by rfl) ⟨1870028, by rfl⟩ : syracuseStep 2493371 = 3740057) B3740057
theorem B2493431 : Blo 1661530 2493431 := bstep (se 1 (by rfl) ⟨1870073, by rfl⟩ : syracuseStep 2493431 = 3740147) B3740147
theorem B2493455 : Blo 1661530 2493455 := bstep (se 1 (by rfl) ⟨1870091, by rfl⟩ : syracuseStep 2493455 = 3740183) B3740183
theorem B4492331 : Blo 1661530 4492331 := bstep (se 1 (by rfl) ⟨3369248, by rfl⟩ : syracuseStep 4492331 = 6738497) B6738497
theorem B2493497 : Blo 1661530 2493497 := bstep (se 2 (by rfl) ⟨935061, by rfl⟩ : syracuseStep 2493497 = 1870123) B1870123
theorem B3738743 : Blo 1661530 3738743 := bstep (se 1 (by rfl) ⟨2804057, by rfl⟩ : syracuseStep 3738743 = 5608115) B5608115
theorem B2493575 : Blo 1661530 2493575 := bstep (se 1 (by rfl) ⟨1870181, by rfl⟩ : syracuseStep 2493575 = 3740363) B3740363
theorem B40995989 : Blo 1661530 40995989 := bstep (se 6 (by rfl) ⟨960843, by rfl⟩ : syracuseStep 40995989 = 1921687) B1921687
theorem B2493611 : Blo 1661530 2493611 := bstep (se 1 (by rfl) ⟨1870208, by rfl⟩ : syracuseStep 2493611 = 3740417) B3740417
theorem B4205753 : Blo 1661530 4205753 := bstep (se 2 (by rfl) ⟨1577157, by rfl⟩ : syracuseStep 4205753 = 3154315) B3154315
theorem B5762249 : Blo 1661530 5762249 := bstep (se 2 (by rfl) ⟨2160843, by rfl⟩ : syracuseStep 5762249 = 4321687) B4321687
theorem B2493641 : Blo 1661530 2493641 := bstep (se 2 (by rfl) ⟨935115, by rfl⟩ : syracuseStep 2493641 = 1870231) B1870231
theorem B12618989 : Blo 1661530 12618989 := bstep (se 3 (by rfl) ⟨2366060, by rfl⟩ : syracuseStep 12618989 = 4732121) B4732121
theorem B2526479 : Blo 1661530 2526479 := bstep (se 1 (by rfl) ⟨1894859, by rfl⟩ : syracuseStep 2526479 = 3789719) B3789719
theorem B3738923 : Blo 1661530 3738923 := bstep (se 1 (by rfl) ⟨2804192, by rfl⟩ : syracuseStep 3738923 = 5608385) B5608385
theorem B2493755 : Blo 1661530 2493755 := bstep (se 1 (by rfl) ⟨1870316, by rfl⟩ : syracuseStep 2493755 = 3740633) B3740633
theorem B2493815 : Blo 1661530 2493815 := bstep (se 1 (by rfl) ⟨1870361, by rfl⟩ : syracuseStep 2493815 = 3740723) B3740723
theorem B6311303 : Blo 1661530 6311303 := bstep (se 1 (by rfl) ⟨4733477, by rfl⟩ : syracuseStep 6311303 = 9466955) B9466955
theorem B2493839 : Blo 1661530 2493839 := bstep (se 1 (by rfl) ⟨1870379, by rfl⟩ : syracuseStep 2493839 = 3740759) B3740759
theorem B2493881 : Blo 1661530 2493881 := bstep (se 2 (by rfl) ⟨935205, by rfl⟩ : syracuseStep 2493881 = 1870411) B1870411
theorem B2493959 : Blo 1661530 2493959 := bstep (se 1 (by rfl) ⟨1870469, by rfl⟩ : syracuseStep 2493959 = 3740939) B3740939
theorem B2493995 : Blo 1661530 2493995 := bstep (se 1 (by rfl) ⟨1870496, by rfl⟩ : syracuseStep 2493995 = 3740993) B3740993
theorem B2494025 : Blo 1661530 2494025 := bstep (se 2 (by rfl) ⟨935259, by rfl⟩ : syracuseStep 2494025 = 1870519) B1870519
theorem B2805367 : Blo 1661530 2805367 := bstep (se 1 (by rfl) ⟨2104025, by rfl⟩ : syracuseStep 2805367 = 4208051) B4208051
theorem B3600007 : Blo 1661530 3600007 := bstep (se 1 (by rfl) ⟨2700005, by rfl⟩ : syracuseStep 3600007 = 5400011) B5400011
theorem B3739283 : Blo 1661530 3739283 := bstep (se 1 (by rfl) ⟨2804462, by rfl⟩ : syracuseStep 3739283 = 5608925) B5608925
theorem B3370681 : Blo 1661530 3370681 := bstep (se 2 (by rfl) ⟨1264005, by rfl⟩ : syracuseStep 3370681 = 2528011) B2528011
theorem B2494139 : Blo 1661530 2494139 := bstep (se 1 (by rfl) ⟨1870604, by rfl⟩ : syracuseStep 2494139 = 3741209) B3741209
theorem B3739337 : Blo 1661530 3739337 := bstep (se 2 (by rfl) ⟨1402251, by rfl⟩ : syracuseStep 3739337 = 2804503) B2804503
theorem B2494199 : Blo 1661530 2494199 := bstep (se 1 (by rfl) ⟨1870649, by rfl⟩ : syracuseStep 2494199 = 3741299) B3741299
theorem B5992193 : Blo 1661530 5992193 := bstep (se 2 (by rfl) ⟨2247072, by rfl⟩ : syracuseStep 5992193 = 4494145) B4494145
theorem B2494223 : Blo 1661530 2494223 := bstep (se 1 (by rfl) ⟨1870667, by rfl⟩ : syracuseStep 2494223 = 3741335) B3741335
theorem B15159089 : Blo 1661530 15159089 := bstep (se 2 (by rfl) ⟨5684658, by rfl⟩ : syracuseStep 15159089 = 11369317) B11369317
theorem B2494265 : Blo 1661530 2494265 := bstep (se 2 (by rfl) ⟨935349, by rfl⟩ : syracuseStep 2494265 = 1870699) B1870699
theorem B2805563 : Blo 1661530 2805563 := bstep (se 1 (by rfl) ⟨2104172, by rfl⟩ : syracuseStep 2805563 = 4208345) B4208345
theorem B4206451 : Blo 1661530 4206451 := bstep (se 1 (by rfl) ⟨3154838, by rfl⟩ : syracuseStep 4206451 = 6309677) B6309677
theorem B2494343 : Blo 1661530 2494343 := bstep (se 1 (by rfl) ⟨1870757, by rfl⟩ : syracuseStep 2494343 = 3741515) B3741515
theorem B23965591 : Blo 1661530 23965591 := bstep (se 1 (by rfl) ⟨17974193, by rfl⟩ : syracuseStep 23965591 = 35948387) B35948387
theorem B2494379 : Blo 1661530 2494379 := bstep (se 1 (by rfl) ⟨1870784, by rfl⟩ : syracuseStep 2494379 = 3741569) B3741569
theorem B2494409 : Blo 1661530 2494409 := bstep (se 2 (by rfl) ⟨935403, by rfl⟩ : syracuseStep 2494409 = 1870807) B1870807
theorem B4206593 : Blo 1661530 4206593 := bstep (se 2 (by rfl) ⟨1577472, by rfl⟩ : syracuseStep 4206593 = 3154945) B3154945
theorem B2494523 : Blo 1661530 2494523 := bstep (se 1 (by rfl) ⟨1870892, by rfl⟩ : syracuseStep 2494523 = 3741785) B3741785
theorem B7098455 : Blo 1661530 7098455 := bstep (se 1 (by rfl) ⟨5323841, by rfl⟩ : syracuseStep 7098455 = 10647683) B10647683
theorem B2805961 : Blo 1661530 2805961 := bstep (se 2 (by rfl) ⟨1052235, by rfl⟩ : syracuseStep 2805961 = 2104471) B2104471
theorem B9466247 : Blo 1661530 9466247 := bstep (se 1 (by rfl) ⟨7099685, by rfl⟩ : syracuseStep 9466247 = 14199371) B14199371
theorem B3740039 : Blo 1661530 3740039 := bstep (se 1 (by rfl) ⟨2805029, by rfl⟩ : syracuseStep 3740039 = 5610059) B5610059
theorem B8417681 : Blo 1661530 8417681 := bstep (se 2 (by rfl) ⟨3156630, by rfl⟩ : syracuseStep 8417681 = 6313261) B6313261
theorem B4207049 : Blo 1661530 4207049 := bstep (se 2 (by rfl) ⟨1577643, by rfl⟩ : syracuseStep 4207049 = 3155287) B3155287
theorem B3740219 : Blo 1661530 3740219 := bstep (se 1 (by rfl) ⟨2805164, by rfl⟩ : syracuseStep 3740219 = 5610329) B5610329
theorem B9466429 : Blo 1661530 9466429 := bstep (se 3 (by rfl) ⟨1774955, by rfl⟩ : syracuseStep 9466429 = 3549911) B3549911
theorem B2994835 : Blo 1661530 2994835 := bstep (se 1 (by rfl) ⟨2246126, by rfl⟩ : syracuseStep 2994835 = 4492253) B4492253
theorem B3740345 : Blo 1661530 3740345 := bstep (se 2 (by rfl) ⟨1402629, by rfl⟩ : syracuseStep 3740345 = 2805259) B2805259
theorem B53916353 : Blo 1661530 53916353 := bstep (se 2 (by rfl) ⟨20218632, by rfl⟩ : syracuseStep 53916353 = 40437265) B40437265
theorem B34132751 : Blo 1661530 34132751 := bstep (se 1 (by rfl) ⟨25599563, by rfl⟩ : syracuseStep 34132751 = 51199127) B51199127
theorem B4207403 : Blo 1661530 4207403 := bstep (se 1 (by rfl) ⟨3155552, by rfl⟩ : syracuseStep 4207403 = 6311105) B6311105
theorem B18224075 : Blo 1661530 18224075 := bstep (se 1 (by rfl) ⟨13668056, by rfl⟩ : syracuseStep 18224075 = 27336113) B27336113
theorem B3740687 : Blo 1661530 3740687 := bstep (se 1 (by rfl) ⟨2805515, by rfl⟩ : syracuseStep 3740687 = 5611031) B5611031
theorem B3740705 : Blo 1661530 3740705 := bstep (se 2 (by rfl) ⟨1402764, by rfl⟩ : syracuseStep 3740705 = 2805529) B2805529
theorem B6313079 : Blo 1661530 6313079 := bstep (se 1 (by rfl) ⟨4734809, by rfl⟩ : syracuseStep 6313079 = 9469619) B9469619
theorem B12620933 : Blo 1661530 12620933 := bstep (se 4 (by rfl) ⟨1183212, by rfl⟩ : syracuseStep 12620933 = 2366425) B2366425
theorem B3200185 : Blo 1661530 3200185 := bstep (se 2 (by rfl) ⟨1200069, by rfl⟩ : syracuseStep 3200185 = 2400139) B2400139
theorem B5608763 : Blo 1661530 5608763 := bstep (se 1 (by rfl) ⟨4206572, by rfl⟩ : syracuseStep 5608763 = 8413145) B8413145
theorem B3741047 : Blo 1661530 3741047 := bstep (se 1 (by rfl) ⟨2805785, by rfl⟩ : syracuseStep 3741047 = 5611571) B5611571
theorem B3995027 : Blo 1661530 3995027 := bstep (se 1 (by rfl) ⟨2996270, by rfl⟩ : syracuseStep 3995027 = 5992541) B5992541
theorem B7984669 : Blo 1661530 7984669 := bstep (se 3 (by rfl) ⟨1497125, by rfl⟩ : syracuseStep 7984669 = 2994251) B2994251
theorem B3741227 : Blo 1661530 3741227 := bstep (se 1 (by rfl) ⟨2805920, by rfl⟩ : syracuseStep 3741227 = 5611841) B5611841
theorem B7984727 : Blo 1661530 7984727 := bstep (se 1 (by rfl) ⟨5988545, by rfl⟩ : syracuseStep 7984727 = 11977091) B11977091
theorem B4208395 : Blo 1661530 4208395 := bstep (se 1 (by rfl) ⟨3156296, by rfl⟩ : syracuseStep 4208395 = 6312593) B6312593
theorem B5609249 : Blo 1661530 5609249 := bstep (se 2 (by rfl) ⟨2103468, by rfl⟩ : syracuseStep 5609249 = 4206937) B4206937
theorem B4732759 : Blo 1661530 4732759 := bstep (se 1 (by rfl) ⟨3549569, by rfl⟩ : syracuseStep 4732759 = 7099139) B7099139
theorem B2103175 : Blo 1661530 2103175 := bstep (se 1 (by rfl) ⟨1577381, by rfl⟩ : syracuseStep 2103175 = 3154763) B3154763
theorem B3741587 : Blo 1661530 3741587 := bstep (se 1 (by rfl) ⟨2806190, by rfl⟩ : syracuseStep 3741587 = 5612381) B5612381
theorem B4208537 : Blo 1661530 4208537 := bstep (se 2 (by rfl) ⟨1578201, by rfl⟩ : syracuseStep 4208537 = 3156403) B3156403
theorem B3741641 : Blo 1661530 3741641 := bstep (se 2 (by rfl) ⟨1403115, by rfl⟩ : syracuseStep 3741641 = 2806231) B2806231
theorem B7100369 : Blo 1661530 7100369 := bstep (se 2 (by rfl) ⟨2662638, by rfl⟩ : syracuseStep 7100369 = 5325277) B5325277
theorem B4732987 : Blo 1661530 4732987 := bstep (se 1 (by rfl) ⟨3549740, by rfl⟩ : syracuseStep 4732987 = 7099481) B7099481
theorem B4208699 : Blo 1661530 4208699 := bstep (se 1 (by rfl) ⟨3156524, by rfl⟩ : syracuseStep 4208699 = 6313049) B6313049
theorem B6314051 : Blo 1661530 6314051 := bstep (se 1 (by rfl) ⟨4735538, by rfl⟩ : syracuseStep 6314051 = 9471077) B9471077
theorem B15374423 : Blo 1661530 15374423 := bstep (se 1 (by rfl) ⟨11530817, by rfl⟩ : syracuseStep 15374423 = 23061635) B23061635
theorem B4733113 : Blo 1661530 4733113 := bstep (se 2 (by rfl) ⟨1774917, by rfl⟩ : syracuseStep 4733113 = 3549835) B3549835
theorem B9468161 : Blo 1661530 9468161 := bstep (se 2 (by rfl) ⟨3550560, by rfl⟩ : syracuseStep 9468161 = 7101121) B7101121
theorem B3078415 : Blo 1661530 3078415 := bstep (se 1 (by rfl) ⟨2308811, by rfl⟩ : syracuseStep 3078415 = 4617623) B4617623
theorem B5609843 : Blo 1661530 5609843 := bstep (se 1 (by rfl) ⟨4207382, by rfl⟩ : syracuseStep 5609843 = 8414765) B8414765
theorem B2103671 : Blo 1661530 2103671 := bstep (se 1 (by rfl) ⟨1577753, by rfl⟩ : syracuseStep 2103671 = 3155507) B3155507
theorem B22739345 : Blo 1661530 22739345 := bstep (se 2 (by rfl) ⟨8527254, by rfl⟩ : syracuseStep 22739345 = 17054509) B17054509
theorem B4209043 : Blo 1661530 4209043 := bstep (se 1 (by rfl) ⟨3156782, by rfl⟩ : syracuseStep 4209043 = 6313565) B6313565
theorem B2103823 : Blo 1661530 2103823 := bstep (se 1 (by rfl) ⟨1577867, by rfl⟩ : syracuseStep 2103823 = 3155735) B3155735
theorem B10648093 : Blo 1661530 10648093 := bstep (se 3 (by rfl) ⟨1996517, by rfl⟩ : syracuseStep 10648093 = 3993035) B3993035
theorem B4209185 : Blo 1661530 4209185 := bstep (se 2 (by rfl) ⟨1578444, by rfl⟩ : syracuseStep 4209185 = 3156889) B3156889
theorem B2996795 : Blo 1661530 2996795 := bstep (se 1 (by rfl) ⟨2247596, by rfl⟩ : syracuseStep 2996795 = 4495193) B4495193
theorem B1661575 : Blo 1661530 1661575 := bstep (se 1 (by rfl) ⟨1246181, by rfl⟩ : syracuseStep 1661575 = 2492363) B2492363
theorem B1661583 : Blo 1661530 1661583 := bstep (se 1 (by rfl) ⟨1246187, by rfl⟩ : syracuseStep 1661583 = 2492375) B2492375
theorem B1661627 : Blo 1661530 1661627 := bstep (se 1 (by rfl) ⟨1246220, by rfl⟩ : syracuseStep 1661627 = 2492441) B2492441
theorem B2103995 : Blo 1661530 2103995 := bstep (se 1 (by rfl) ⟨1577996, by rfl⟩ : syracuseStep 2103995 = 3155993) B3155993
theorem B8411849 : Blo 1661530 8411849 := bstep (se 2 (by rfl) ⟨3154443, by rfl⟩ : syracuseStep 8411849 = 6308887) B6308887
theorem B1661703 : Blo 1661530 1661703 := bstep (se 1 (by rfl) ⟨1246277, by rfl⟩ : syracuseStep 1661703 = 2492555) B2492555
theorem B1661711 : Blo 1661530 1661711 := bstep (se 1 (by rfl) ⟨1246283, by rfl⟩ : syracuseStep 1661711 = 2492567) B2492567
theorem B5323535 : Blo 1661530 5323535 := bstep (se 1 (by rfl) ⟨3992651, by rfl⟩ : syracuseStep 5323535 = 7985303) B7985303
theorem B1661755 : Blo 1661530 1661755 := bstep (se 1 (by rfl) ⟨1246316, by rfl⟩ : syracuseStep 1661755 = 2492633) B2492633
theorem B4266839 : Blo 1661530 4266839 := bstep (se 1 (by rfl) ⟨3200129, by rfl⟩ : syracuseStep 4266839 = 6400259) B6400259
theorem B1661831 : Blo 1661530 1661831 := bstep (se 1 (by rfl) ⟨1246373, by rfl⟩ : syracuseStep 1661831 = 2492747) B2492747
theorem B1661839 : Blo 1661530 1661839 := bstep (se 1 (by rfl) ⟨1246379, by rfl⟩ : syracuseStep 1661839 = 2492759) B2492759
theorem B1661883 : Blo 1661530 1661883 := bstep (se 1 (by rfl) ⟨1246412, by rfl⟩ : syracuseStep 1661883 = 2492825) B2492825
theorem B1661959 : Blo 1661530 1661959 := bstep (se 1 (by rfl) ⟨1246469, by rfl⟩ : syracuseStep 1661959 = 2492939) B2492939
theorem B1661967 : Blo 1661530 1661967 := bstep (se 1 (by rfl) ⟨1246475, by rfl⟩ : syracuseStep 1661967 = 2492951) B2492951
theorem B1662011 : Blo 1661530 1662011 := bstep (se 1 (by rfl) ⟨1246508, by rfl⟩ : syracuseStep 1662011 = 2493017) B2493017
theorem B1662087 : Blo 1661530 1662087 := bstep (se 1 (by rfl) ⟨1246565, by rfl⟩ : syracuseStep 1662087 = 2493131) B2493131
theorem B1662095 : Blo 1661530 1662095 := bstep (se 1 (by rfl) ⟨1246571, by rfl⟩ : syracuseStep 1662095 = 2493143) B2493143
theorem B1662139 : Blo 1661530 1662139 := bstep (se 1 (by rfl) ⟨1246604, by rfl⟩ : syracuseStep 1662139 = 2493209) B2493209
theorem B9862337 : Blo 1661530 9862337 := bstep (se 2 (by rfl) ⟨3698376, by rfl⟩ : syracuseStep 9862337 = 7396753) B7396753
theorem B20217077 : Blo 1661530 20217077 := bstep (se 5 (by rfl) ⟨947675, by rfl⟩ : syracuseStep 20217077 = 1895351) B1895351
theorem B1662215 : Blo 1661530 1662215 := bstep (se 1 (by rfl) ⟨1246661, by rfl⟩ : syracuseStep 1662215 = 2493323) B2493323
theorem B1662223 : Blo 1661530 1662223 := bstep (se 1 (by rfl) ⟨1246667, by rfl⟩ : syracuseStep 1662223 = 2493335) B2493335
theorem B1662267 : Blo 1661530 1662267 := bstep (se 1 (by rfl) ⟨1246700, by rfl⟩ : syracuseStep 1662267 = 2493401) B2493401
theorem B1662343 : Blo 1661530 1662343 := bstep (se 1 (by rfl) ⟨1246757, by rfl⟩ : syracuseStep 1662343 = 2493515) B2493515
theorem B1662351 : Blo 1661530 1662351 := bstep (se 1 (by rfl) ⟨1246763, by rfl⟩ : syracuseStep 1662351 = 2493527) B2493527
theorem B1662395 : Blo 1661530 1662395 := bstep (se 1 (by rfl) ⟨1246796, by rfl⟩ : syracuseStep 1662395 = 2493593) B2493593
theorem B2366921 : Blo 1661530 2366921 := bstep (se 2 (by rfl) ⟨887595, by rfl⟩ : syracuseStep 2366921 = 1775191) B1775191
theorem B12623363 : Blo 1661530 12623363 := bstep (se 1 (by rfl) ⟨9467522, by rfl⟩ : syracuseStep 12623363 = 18935045) B18935045
theorem B1662471 : Blo 1661530 1662471 := bstep (se 1 (by rfl) ⟨1246853, by rfl⟩ : syracuseStep 1662471 = 2493707) B2493707
theorem B1662479 : Blo 1661530 1662479 := bstep (se 1 (by rfl) ⟨1246859, by rfl⟩ : syracuseStep 1662479 = 2493719) B2493719
theorem B1662523 : Blo 1661530 1662523 := bstep (se 1 (by rfl) ⟨1246892, by rfl⟩ : syracuseStep 1662523 = 2493785) B2493785
theorem B2399863 : Blo 1661530 2399863 := bstep (se 1 (by rfl) ⟨1799897, by rfl⟩ : syracuseStep 2399863 = 3599795) B3599795
theorem B1662599 : Blo 1661530 1662599 := bstep (se 1 (by rfl) ⟨1246949, by rfl⟩ : syracuseStep 1662599 = 2493899) B2493899
theorem B1662607 : Blo 1661530 1662607 := bstep (se 1 (by rfl) ⟨1246955, by rfl⟩ : syracuseStep 1662607 = 2493911) B2493911
theorem B1662651 : Blo 1661530 1662651 := bstep (se 1 (by rfl) ⟨1246988, by rfl⟩ : syracuseStep 1662651 = 2493977) B2493977
theorem B1662727 : Blo 1661530 1662727 := bstep (se 1 (by rfl) ⟨1247045, by rfl⟩ : syracuseStep 1662727 = 2494091) B2494091
theorem B1662735 : Blo 1661530 1662735 := bstep (se 1 (by rfl) ⟨1247051, by rfl⟩ : syracuseStep 1662735 = 2494103) B2494103
theorem B6070049 : Blo 1661530 6070049 := bstep (se 2 (by rfl) ⟨2276268, by rfl⟩ : syracuseStep 6070049 = 4552537) B4552537
theorem B1662779 : Blo 1661530 1662779 := bstep (se 1 (by rfl) ⟨1247084, by rfl⟩ : syracuseStep 1662779 = 2494169) B2494169
theorem B21307211 : Blo 1661530 21307211 := bstep (se 1 (by rfl) ⟨15980408, by rfl⟩ : syracuseStep 21307211 = 31960817) B31960817
theorem B1662855 : Blo 1661530 1662855 := bstep (se 1 (by rfl) ⟨1247141, by rfl⟩ : syracuseStep 1662855 = 2494283) B2494283
theorem B1662863 : Blo 1661530 1662863 := bstep (se 1 (by rfl) ⟨1247147, by rfl⟩ : syracuseStep 1662863 = 2494295) B2494295
theorem B5054393 : Blo 1661530 5054393 := bstep (se 2 (by rfl) ⟨1895397, by rfl⟩ : syracuseStep 5054393 = 3790795) B3790795
theorem B1662907 : Blo 1661530 1662907 := bstep (se 1 (by rfl) ⟨1247180, by rfl⟩ : syracuseStep 1662907 = 2494361) B2494361
theorem B1663015 : Blo 1661530 1663015 := bstep (se 1 (by rfl) ⟨1247261, by rfl⟩ : syracuseStep 1663015 = 2494523) B2494523
theorem B76800149 : Blo 1661530 76800149 := bstep (se 6 (by rfl) ⟨1800003, by rfl⟩ : syracuseStep 76800149 = 3600007) B3600007
theorem B5611787 : Blo 1661530 5611787 := bstep (se 1 (by rfl) ⟨4208840, by rfl⟩ : syracuseStep 5611787 = 8417681) B8417681
theorem B5612057 : Blo 1661530 5612057 := bstep (se 2 (by rfl) ⟨2104521, by rfl⟩ : syracuseStep 5612057 = 4209043) B4209043
theorem B14197457 : Blo 1661530 14197457 := bstep (se 2 (by rfl) ⟨5324046, by rfl⟩ : syracuseStep 14197457 = 10648093) B10648093
theorem B8413955 : Blo 1661530 8413955 := bstep (se 1 (by rfl) ⟨6310466, by rfl⟩ : syracuseStep 8413955 = 12620933) B12620933
theorem B6308675 : Blo 1661530 6308675 := bstep (se 1 (by rfl) ⟨4731506, by rfl⟩ : syracuseStep 6308675 = 9463013) B9463013
theorem B2663351 : Blo 1661530 2663351 := bstep (se 1 (by rfl) ⟨1997513, by rfl⟩ : syracuseStep 2663351 = 3995027) B3995027
theorem B60646553 : Blo 1661530 60646553 := bstep (se 2 (by rfl) ⟨22742457, by rfl⟩ : syracuseStep 60646553 = 45484915) B45484915
theorem B7988377 : Blo 1661530 7988377 := bstep (se 2 (by rfl) ⟨2995641, by rfl⟩ : syracuseStep 7988377 = 5991283) B5991283
theorem B5325995 : Blo 1661530 5325995 := bstep (se 1 (by rfl) ⟨3994496, by rfl⟩ : syracuseStep 5325995 = 7988993) B7988993
theorem B10249615 : Blo 1661530 10249615 := bstep (se 1 (by rfl) ⟨7687211, by rfl⟩ : syracuseStep 10249615 = 15374423) B15374423
theorem B16418213 : Blo 1661530 16418213 := bstep (se 4 (by rfl) ⟨1539207, by rfl⟩ : syracuseStep 16418213 = 3078415) B3078415
theorem B34129451 : Blo 1661530 34129451 := bstep (se 1 (by rfl) ⟨25597088, by rfl⟩ : syracuseStep 34129451 = 51194177) B51194177
theorem B1869511 : Blo 1661530 1869511 := bstep (se 1 (by rfl) ⟨1402133, by rfl⟩ : syracuseStep 1869511 = 2804267) B2804267
theorem B8210219 : Blo 1661530 8210219 := bstep (se 1 (by rfl) ⟨6157664, by rfl⟩ : syracuseStep 8210219 = 12315329) B12315329
theorem B12617531 : Blo 1661530 12617531 := bstep (se 1 (by rfl) ⟨9463148, by rfl⟩ : syracuseStep 12617531 = 18926297) B18926297
theorem B3549023 : Blo 1661530 3549023 := bstep (se 1 (by rfl) ⟨2661767, by rfl⟩ : syracuseStep 3549023 = 5323535) B5323535
theorem B2844559 : Blo 1661530 2844559 := bstep (se 1 (by rfl) ⟨2133419, by rfl⟩ : syracuseStep 2844559 = 4266839) B4266839
theorem B2492495 : Blo 1661530 2492495 := bstep (se 1 (by rfl) ⟨1869371, by rfl⟩ : syracuseStep 2492495 = 3738743) B3738743
theorem B27330659 : Blo 1661530 27330659 := bstep (se 1 (by rfl) ⟨20497994, by rfl⟩ : syracuseStep 27330659 = 40995989) B40995989
theorem B2803835 : Blo 1661530 2803835 := bstep (se 1 (by rfl) ⟨2102876, by rfl⟩ : syracuseStep 2803835 = 4205753) B4205753
theorem B13478051 : Blo 1661530 13478051 := bstep (se 1 (by rfl) ⟨10108538, by rfl⟩ : syracuseStep 13478051 = 20217077) B20217077
theorem B2492615 : Blo 1661530 2492615 := bstep (se 1 (by rfl) ⟨1869461, by rfl⟩ : syracuseStep 2492615 = 3738923) B3738923
theorem B8415575 : Blo 1661530 8415575 := bstep (se 1 (by rfl) ⟨6311681, by rfl⟩ : syracuseStep 8415575 = 12623363) B12623363
theorem B2492777 : Blo 1661530 2492777 := bstep (se 2 (by rfl) ⟨934791, by rfl⟩ : syracuseStep 2492777 = 1869583) B1869583
theorem B2492855 : Blo 1661530 2492855 := bstep (se 1 (by rfl) ⟨1869641, by rfl⟩ : syracuseStep 2492855 = 3739283) B3739283
theorem B6310345 : Blo 1661530 6310345 := bstep (se 2 (by rfl) ⟨2366379, by rfl⟩ : syracuseStep 6310345 = 4732759) B4732759
theorem B2492891 : Blo 1661530 2492891 := bstep (se 1 (by rfl) ⟨1869668, by rfl⟩ : syracuseStep 2492891 = 3739337) B3739337
theorem B2804233 : Blo 1661530 2804233 := bstep (se 2 (by rfl) ⟨1051587, by rfl⟩ : syracuseStep 2804233 = 2103175) B2103175
theorem B48597533 : Blo 1661530 48597533 := bstep (se 3 (by rfl) ⟨9112037, by rfl⟩ : syracuseStep 48597533 = 18224075) B18224075
theorem B1870375 : Blo 1661530 1870375 := bstep (se 1 (by rfl) ⟨1402781, by rfl⟩ : syracuseStep 1870375 = 2805563) B2805563
theorem B3369595 : Blo 1661530 3369595 := bstep (se 1 (by rfl) ⟨2527196, by rfl⟩ : syracuseStep 3369595 = 5054393) B5054393
theorem B2804395 : Blo 1661530 2804395 := bstep (se 1 (by rfl) ⟨2103296, by rfl⟩ : syracuseStep 2804395 = 4206593) B4206593
theorem B6310649 : Blo 1661530 6310649 := bstep (se 2 (by rfl) ⟨2366493, by rfl⟩ : syracuseStep 6310649 = 4732987) B4732987
theorem B12626765 : Blo 1661530 12626765 := bstep (se 3 (by rfl) ⟨2367518, by rfl⟩ : syracuseStep 12626765 = 4735037) B4735037
theorem B3369871 : Blo 1661530 3369871 := bstep (se 1 (by rfl) ⟨2527403, by rfl⟩ : syracuseStep 3369871 = 5054807) B5054807
theorem B6310817 : Blo 1661530 6310817 := bstep (se 2 (by rfl) ⟨2366556, by rfl⟩ : syracuseStep 6310817 = 4733113) B4733113
theorem B6310831 : Blo 1661530 6310831 := bstep (se 1 (by rfl) ⟨4733123, by rfl⟩ : syracuseStep 6310831 = 9466247) B9466247
theorem B2493359 : Blo 1661530 2493359 := bstep (se 1 (by rfl) ⟨1870019, by rfl⟩ : syracuseStep 2493359 = 3740039) B3740039
theorem B2804699 : Blo 1661530 2804699 := bstep (se 1 (by rfl) ⟨2103524, by rfl⟩ : syracuseStep 2804699 = 4207049) B4207049
theorem B2493449 : Blo 1661530 2493449 := bstep (se 2 (by rfl) ⟨935043, by rfl⟩ : syracuseStep 2493449 = 1870087) B1870087
theorem B2493479 : Blo 1661530 2493479 := bstep (se 1 (by rfl) ⟨1870109, by rfl⟩ : syracuseStep 2493479 = 3740219) B3740219
theorem B3157049 : Blo 1661530 3157049 := bstep (se 2 (by rfl) ⟨1183893, by rfl⟩ : syracuseStep 3157049 = 2367787) B2367787
theorem B2493563 : Blo 1661530 2493563 := bstep (se 1 (by rfl) ⟨1870172, by rfl⟩ : syracuseStep 2493563 = 3740345) B3740345
theorem B2804935 : Blo 1661530 2804935 := bstep (se 1 (by rfl) ⟨2103701, by rfl⟩ : syracuseStep 2804935 = 4207403) B4207403
theorem B14200055 : Blo 1661530 14200055 := bstep (se 1 (by rfl) ⟨10650041, by rfl⟩ : syracuseStep 14200055 = 21300083) B21300083
theorem B2493689 : Blo 1661530 2493689 := bstep (se 2 (by rfl) ⟨935133, by rfl⟩ : syracuseStep 2493689 = 1870267) B1870267
theorem B2493791 : Blo 1661530 2493791 := bstep (se 1 (by rfl) ⟨1870343, by rfl⟩ : syracuseStep 2493791 = 3740687) B3740687
theorem B2805097 : Blo 1661530 2805097 := bstep (se 2 (by rfl) ⟨1051911, by rfl⟩ : syracuseStep 2805097 = 2103823) B2103823
theorem B2493803 : Blo 1661530 2493803 := bstep (se 1 (by rfl) ⟨1870352, by rfl⟩ : syracuseStep 2493803 = 3740705) B3740705
theorem B3993113 : Blo 1661530 3993113 := bstep (se 2 (by rfl) ⟨1497417, by rfl⟩ : syracuseStep 3993113 = 2994835) B2994835
theorem B3739175 : Blo 1661530 3739175 := bstep (se 1 (by rfl) ⟨2804381, by rfl⟩ : syracuseStep 3739175 = 5608763) B5608763
theorem B2494031 : Blo 1661530 2494031 := bstep (se 1 (by rfl) ⟨1870523, by rfl⟩ : syracuseStep 2494031 = 3741047) B3741047
theorem B3550817 : Blo 1661530 3550817 := bstep (se 2 (by rfl) ⟨1331556, by rfl⟩ : syracuseStep 3550817 = 2663113) B2663113
theorem B2494151 : Blo 1661530 2494151 := bstep (se 1 (by rfl) ⟨1870613, by rfl⟩ : syracuseStep 2494151 = 3741227) B3741227
theorem B4001609 : Blo 1661530 4001609 := bstep (se 2 (by rfl) ⟨1500603, by rfl⟩ : syracuseStep 4001609 = 3001207) B3001207
theorem B4206431 : Blo 1661530 4206431 := bstep (se 1 (by rfl) ⟨3154823, by rfl⟩ : syracuseStep 4206431 = 6309647) B6309647
theorem B2494313 : Blo 1661530 2494313 := bstep (se 2 (by rfl) ⟨935367, by rfl⟩ : syracuseStep 2494313 = 1870735) B1870735
theorem B3739499 : Blo 1661530 3739499 := bstep (se 1 (by rfl) ⟨2804624, by rfl⟩ : syracuseStep 3739499 = 5609249) B5609249
theorem B6311789 : Blo 1661530 6311789 := bstep (se 3 (by rfl) ⟨1183460, by rfl⟩ : syracuseStep 6311789 = 2366921) B2366921
theorem B3739553 : Blo 1661530 3739553 := bstep (se 2 (by rfl) ⟨1402332, by rfl⟩ : syracuseStep 3739553 = 2804665) B2804665
theorem B2494391 : Blo 1661530 2494391 := bstep (se 1 (by rfl) ⟨1870793, by rfl⟩ : syracuseStep 2494391 = 3741587) B3741587
theorem B2805691 : Blo 1661530 2805691 := bstep (se 1 (by rfl) ⟨2104268, by rfl⟩ : syracuseStep 2805691 = 4208537) B4208537
theorem B2699227 : Blo 1661530 2699227 := bstep (se 1 (by rfl) ⟨2024420, by rfl⟩ : syracuseStep 2699227 = 4048841) B4048841
theorem B2494427 : Blo 1661530 2494427 := bstep (se 1 (by rfl) ⟨1870820, by rfl⟩ : syracuseStep 2494427 = 3741641) B3741641
theorem B2805799 : Blo 1661530 2805799 := bstep (se 1 (by rfl) ⟨2104349, by rfl⟩ : syracuseStep 2805799 = 4208699) B4208699
theorem B7991453 : Blo 1661530 7991453 := bstep (se 3 (by rfl) ⟨1498397, by rfl⟩ : syracuseStep 7991453 = 2996795) B2996795
theorem B6312107 : Blo 1661530 6312107 := bstep (se 1 (by rfl) ⟨4734080, by rfl⟩ : syracuseStep 6312107 = 9468161) B9468161
theorem B3739895 : Blo 1661530 3739895 := bstep (se 1 (by rfl) ⟨2804921, by rfl⟩ : syracuseStep 3739895 = 5609843) B5609843
theorem B2994425 : Blo 1661530 2994425 := bstep (se 2 (by rfl) ⟨1122909, by rfl⟩ : syracuseStep 2994425 = 2245819) B2245819
theorem B15159563 : Blo 1661530 15159563 := bstep (se 1 (by rfl) ⟨11369672, by rfl⟩ : syracuseStep 15159563 = 22739345) B22739345
theorem B2806123 : Blo 1661530 2806123 := bstep (se 1 (by rfl) ⟨2104592, by rfl⟩ : syracuseStep 2806123 = 4209185) B4209185
theorem B5607899 : Blo 1661530 5607899 := bstep (se 1 (by rfl) ⟨4205924, by rfl⟩ : syracuseStep 5607899 = 8411849) B8411849
theorem B8319547 : Blo 1661530 8319547 := bstep (se 1 (by rfl) ⟨6239660, by rfl⟩ : syracuseStep 8319547 = 12479321) B12479321
theorem B2994887 : Blo 1661530 2994887 := bstep (se 1 (by rfl) ⟨2246165, by rfl⟩ : syracuseStep 2994887 = 4492331) B4492331
theorem B10646225 : Blo 1661530 10646225 := bstep (se 2 (by rfl) ⟨3992334, by rfl⟩ : syracuseStep 10646225 = 7984669) B7984669
theorem B6574891 : Blo 1661530 6574891 := bstep (se 1 (by rfl) ⟨4931168, by rfl⟩ : syracuseStep 6574891 = 9862337) B9862337
theorem B23966513 : Blo 1661530 23966513 := bstep (se 2 (by rfl) ⟨8987442, by rfl⟩ : syracuseStep 23966513 = 17974885) B17974885
theorem B3740489 : Blo 1661530 3740489 := bstep (se 2 (by rfl) ⟨1402683, by rfl⟩ : syracuseStep 3740489 = 2805367) B2805367
theorem B3199817 : Blo 1661530 3199817 := bstep (se 2 (by rfl) ⟨1199931, by rfl⟩ : syracuseStep 3199817 = 2399863) B2399863
theorem B1684319 : Blo 1661530 1684319 := bstep (se 1 (by rfl) ⟨1263239, by rfl⟩ : syracuseStep 1684319 = 2526479) B2526479
theorem B4494241 : Blo 1661530 4494241 := bstep (se 2 (by rfl) ⟨1685340, by rfl⟩ : syracuseStep 4494241 = 3370681) B3370681
theorem B4207535 : Blo 1661530 4207535 := bstep (se 1 (by rfl) ⟨3155651, by rfl⟩ : syracuseStep 4207535 = 6311303) B6311303
theorem B5608601 : Blo 1661530 5608601 := bstep (se 2 (by rfl) ⟨2103225, by rfl⟩ : syracuseStep 5608601 = 4206451) B4206451
theorem B3994795 : Blo 1661530 3994795 := bstep (se 1 (by rfl) ⟨2996096, by rfl⟩ : syracuseStep 3994795 = 5992193) B5992193
theorem B31954121 : Blo 1661530 31954121 := bstep (se 2 (by rfl) ⟨11982795, by rfl⟩ : syracuseStep 31954121 = 23965591) B23965591
theorem B10106059 : Blo 1661530 10106059 := bstep (se 1 (by rfl) ⟨7579544, by rfl⟩ : syracuseStep 10106059 = 15159089) B15159089
theorem B18929213 : Blo 1661530 18929213 := bstep (se 3 (by rfl) ⟨3549227, by rfl⟩ : syracuseStep 18929213 = 7098455) B7098455
theorem B3741281 : Blo 1661530 3741281 := bstep (se 2 (by rfl) ⟨1402980, by rfl⟩ : syracuseStep 3741281 = 2805961) B2805961
theorem B35944235 : Blo 1661530 35944235 := bstep (se 1 (by rfl) ⟨26958176, by rfl⟩ : syracuseStep 35944235 = 53916353) B53916353
theorem B22755167 : Blo 1661530 22755167 := bstep (se 1 (by rfl) ⟨17066375, by rfl⟩ : syracuseStep 22755167 = 34132751) B34132751
theorem B3741623 : Blo 1661530 3741623 := bstep (se 1 (by rfl) ⟨2806217, by rfl⟩ : syracuseStep 3741623 = 5612435) B5612435
theorem B8984591 : Blo 1661530 8984591 := bstep (se 1 (by rfl) ⟨6738443, by rfl⟩ : syracuseStep 8984591 = 13476887) B13476887
theorem B4380691 : Blo 1661530 4380691 := bstep (se 1 (by rfl) ⟨3285518, by rfl⟩ : syracuseStep 4380691 = 6571037) B6571037
theorem B4208719 : Blo 1661530 4208719 := bstep (se 1 (by rfl) ⟨3156539, by rfl⟩ : syracuseStep 4208719 = 6313079) B6313079
theorem B12621905 : Blo 1661530 12621905 := bstep (se 2 (by rfl) ⟨4733214, by rfl⟩ : syracuseStep 12621905 = 9466429) B9466429
theorem B21067877 : Blo 1661530 21067877 := bstep (se 4 (by rfl) ⟨1975113, by rfl⟩ : syracuseStep 21067877 = 3950227) B3950227
theorem B5609789 : Blo 1661530 5609789 := bstep (se 3 (by rfl) ⟨1051835, by rfl⟩ : syracuseStep 5609789 = 2103671) B2103671
theorem B5323151 : Blo 1661530 5323151 := bstep (se 1 (by rfl) ⟨3992363, by rfl⟩ : syracuseStep 5323151 = 7984727) B7984727
theorem B2103727 : Blo 1661530 2103727 := bstep (se 1 (by rfl) ⟨1577795, by rfl⟩ : syracuseStep 2103727 = 3155591) B3155591
theorem B1661535 : Blo 1661530 1661535 := bstep (se 1 (by rfl) ⟨1246151, by rfl⟩ : syracuseStep 1661535 = 2492303) B2492303
theorem B1661563 : Blo 1661530 1661563 := bstep (se 1 (by rfl) ⟨1246172, by rfl⟩ : syracuseStep 1661563 = 2492345) B2492345
theorem B4733579 : Blo 1661530 4733579 := bstep (se 1 (by rfl) ⟨3550184, by rfl⟩ : syracuseStep 4733579 = 7100369) B7100369
theorem B1661615 : Blo 1661530 1661615 := bstep (se 1 (by rfl) ⟨1246211, by rfl⟩ : syracuseStep 1661615 = 2492423) B2492423
theorem B1661639 : Blo 1661530 1661639 := bstep (se 1 (by rfl) ⟨1246229, by rfl⟩ : syracuseStep 1661639 = 2492459) B2492459
theorem B4209367 : Blo 1661530 4209367 := bstep (se 1 (by rfl) ⟨3157025, by rfl⟩ : syracuseStep 4209367 = 6314051) B6314051
theorem B1661659 : Blo 1661530 1661659 := bstep (se 1 (by rfl) ⟨1246244, by rfl⟩ : syracuseStep 1661659 = 2492489) B2492489
theorem B1661735 : Blo 1661530 1661735 := bstep (se 1 (by rfl) ⟨1246301, by rfl⟩ : syracuseStep 1661735 = 2492603) B2492603
theorem B6740779 : Blo 1661530 6740779 := bstep (se 1 (by rfl) ⟨5055584, by rfl⟩ : syracuseStep 6740779 = 10111169) B10111169
theorem B1661775 : Blo 1661530 1661775 := bstep (se 1 (by rfl) ⟨1246331, by rfl⟩ : syracuseStep 1661775 = 2492663) B2492663
theorem B1661791 : Blo 1661530 1661791 := bstep (se 1 (by rfl) ⟨1246343, by rfl⟩ : syracuseStep 1661791 = 2492687) B2492687
theorem B8412011 : Blo 1661530 8412011 := bstep (se 1 (by rfl) ⟨6309008, by rfl⟩ : syracuseStep 8412011 = 12618017) B12618017
theorem B1661819 : Blo 1661530 1661819 := bstep (se 1 (by rfl) ⟨1246364, by rfl⟩ : syracuseStep 1661819 = 2492729) B2492729
theorem B4266913 : Blo 1661530 4266913 := bstep (se 2 (by rfl) ⟨1600092, by rfl⟩ : syracuseStep 4266913 = 3200185) B3200185
theorem B1661871 : Blo 1661530 1661871 := bstep (se 1 (by rfl) ⟨1246403, by rfl⟩ : syracuseStep 1661871 = 2492807) B2492807
theorem B1661895 : Blo 1661530 1661895 := bstep (se 1 (by rfl) ⟨1246421, by rfl⟩ : syracuseStep 1661895 = 2492843) B2492843
theorem B1661915 : Blo 1661530 1661915 := bstep (se 1 (by rfl) ⟨1246436, by rfl⟩ : syracuseStep 1661915 = 2492873) B2492873
theorem B1661991 : Blo 1661530 1661991 := bstep (se 1 (by rfl) ⟨1246493, by rfl⟩ : syracuseStep 1661991 = 2492987) B2492987
theorem B1662031 : Blo 1661530 1662031 := bstep (se 1 (by rfl) ⟨1246523, by rfl⟩ : syracuseStep 1662031 = 2493047) B2493047
theorem B1662047 : Blo 1661530 1662047 := bstep (se 1 (by rfl) ⟨1246535, by rfl⟩ : syracuseStep 1662047 = 2493071) B2493071
theorem B1662075 : Blo 1661530 1662075 := bstep (se 1 (by rfl) ⟨1246556, by rfl⟩ : syracuseStep 1662075 = 2493113) B2493113
theorem B5610653 : Blo 1661530 5610653 := bstep (se 3 (by rfl) ⟨1051997, by rfl⟩ : syracuseStep 5610653 = 2103995) B2103995
theorem B1662127 : Blo 1661530 1662127 := bstep (se 1 (by rfl) ⟨1246595, by rfl⟩ : syracuseStep 1662127 = 2493191) B2493191
theorem B1662151 : Blo 1661530 1662151 := bstep (se 1 (by rfl) ⟨1246613, by rfl⟩ : syracuseStep 1662151 = 2493227) B2493227
theorem B1662171 : Blo 1661530 1662171 := bstep (se 1 (by rfl) ⟨1246628, by rfl⟩ : syracuseStep 1662171 = 2493257) B2493257
theorem B1662247 : Blo 1661530 1662247 := bstep (se 1 (by rfl) ⟨1246685, by rfl⟩ : syracuseStep 1662247 = 2493371) B2493371
theorem B1662287 : Blo 1661530 1662287 := bstep (se 1 (by rfl) ⟨1246715, by rfl⟩ : syracuseStep 1662287 = 2493431) B2493431
theorem B1662303 : Blo 1661530 1662303 := bstep (se 1 (by rfl) ⟨1246727, by rfl⟩ : syracuseStep 1662303 = 2493455) B2493455
theorem B1662331 : Blo 1661530 1662331 := bstep (se 1 (by rfl) ⟨1246748, by rfl⟩ : syracuseStep 1662331 = 2493497) B2493497
theorem B15973757 : Blo 1661530 15973757 := bstep (se 3 (by rfl) ⟨2995079, by rfl⟩ : syracuseStep 15973757 = 5990159) B5990159
theorem B1662383 : Blo 1661530 1662383 := bstep (se 1 (by rfl) ⟨1246787, by rfl⟩ : syracuseStep 1662383 = 2493575) B2493575
theorem B1662407 : Blo 1661530 1662407 := bstep (se 1 (by rfl) ⟨1246805, by rfl⟩ : syracuseStep 1662407 = 2493611) B2493611
theorem B3841499 : Blo 1661530 3841499 := bstep (se 1 (by rfl) ⟨2881124, by rfl⟩ : syracuseStep 3841499 = 5762249) B5762249
theorem B1662427 : Blo 1661530 1662427 := bstep (se 1 (by rfl) ⟨1246820, by rfl⟩ : syracuseStep 1662427 = 2493641) B2493641
theorem B8412659 : Blo 1661530 8412659 := bstep (se 1 (by rfl) ⟨6309494, by rfl⟩ : syracuseStep 8412659 = 12618989) B12618989
theorem B1662503 : Blo 1661530 1662503 := bstep (se 1 (by rfl) ⟨1246877, by rfl⟩ : syracuseStep 1662503 = 2493755) B2493755
theorem B1662543 : Blo 1661530 1662543 := bstep (se 1 (by rfl) ⟨1246907, by rfl⟩ : syracuseStep 1662543 = 2493815) B2493815
theorem B1662559 : Blo 1661530 1662559 := bstep (se 1 (by rfl) ⟨1246919, by rfl⟩ : syracuseStep 1662559 = 2493839) B2493839
theorem B1662587 : Blo 1661530 1662587 := bstep (se 1 (by rfl) ⟨1246940, by rfl⟩ : syracuseStep 1662587 = 2493881) B2493881
theorem B1662639 : Blo 1661530 1662639 := bstep (se 1 (by rfl) ⟨1246979, by rfl⟩ : syracuseStep 1662639 = 2493959) B2493959
theorem B5611193 : Blo 1661530 5611193 := bstep (se 2 (by rfl) ⟨2104197, by rfl⟩ : syracuseStep 5611193 = 4208395) B4208395
theorem B1662663 : Blo 1661530 1662663 := bstep (se 1 (by rfl) ⟨1246997, by rfl⟩ : syracuseStep 1662663 = 2493995) B2493995
theorem B1662683 : Blo 1661530 1662683 := bstep (se 1 (by rfl) ⟨1247012, by rfl⟩ : syracuseStep 1662683 = 2494025) B2494025
theorem B1662759 : Blo 1661530 1662759 := bstep (se 1 (by rfl) ⟨1247069, by rfl⟩ : syracuseStep 1662759 = 2494139) B2494139
theorem B1662799 : Blo 1661530 1662799 := bstep (se 1 (by rfl) ⟨1247099, by rfl⟩ : syracuseStep 1662799 = 2494199) B2494199
theorem B1662815 : Blo 1661530 1662815 := bstep (se 1 (by rfl) ⟨1247111, by rfl⟩ : syracuseStep 1662815 = 2494223) B2494223
theorem B4046699 : Blo 1661530 4046699 := bstep (se 1 (by rfl) ⟨3035024, by rfl⟩ : syracuseStep 4046699 = 6070049) B6070049
theorem B1662843 : Blo 1661530 1662843 := bstep (se 1 (by rfl) ⟨1247132, by rfl⟩ : syracuseStep 1662843 = 2494265) B2494265
theorem B14204807 : Blo 1661530 14204807 := bstep (se 1 (by rfl) ⟨10653605, by rfl⟩ : syracuseStep 14204807 = 21307211) B21307211
theorem B1662895 : Blo 1661530 1662895 := bstep (se 1 (by rfl) ⟨1247171, by rfl⟩ : syracuseStep 1662895 = 2494343) B2494343
theorem B1662919 : Blo 1661530 1662919 := bstep (se 1 (by rfl) ⟨1247189, by rfl⟩ : syracuseStep 1662919 = 2494379) B2494379
theorem B1662939 : Blo 1661530 1662939 := bstep (se 1 (by rfl) ⟨1247204, by rfl⟩ : syracuseStep 1662939 = 2494409) B2494409
theorem B5840921 : Blo 1661530 5840921 := bstep (se 2 (by rfl) ⟨2190345, by rfl⟩ : syracuseStep 5840921 = 4380691) B4380691
theorem B51200099 : Blo 1661530 51200099 := bstep (se 1 (by rfl) ⟨38400074, by rfl⟩ : syracuseStep 51200099 = 76800149) B76800149
theorem B5611625 : Blo 1661530 5611625 := bstep (se 2 (by rfl) ⟨2104359, by rfl⟩ : syracuseStep 5611625 = 4208719) B4208719
theorem B8413793 : Blo 1661530 8413793 := bstep (se 2 (by rfl) ⟨3155172, by rfl⟩ : syracuseStep 8413793 = 6310345) B6310345
theorem B11092729 : Blo 1661530 11092729 := bstep (se 2 (by rfl) ⟨4159773, by rfl⟩ : syracuseStep 11092729 = 8319547) B8319547
theorem B10945475 : Blo 1661530 10945475 := bstep (se 1 (by rfl) ⟨8209106, by rfl⟩ : syracuseStep 10945475 = 16418213) B16418213
theorem B5612489 : Blo 1661530 5612489 := bstep (se 2 (by rfl) ⟨2104683, by rfl⟩ : syracuseStep 5612489 = 4209367) B4209367
theorem B17966069 : Blo 1661530 17966069 := bstep (se 5 (by rfl) ⟨842159, by rfl⟩ : syracuseStep 17966069 = 1684319) B1684319
theorem B8987705 : Blo 1661530 8987705 := bstep (se 2 (by rfl) ⟨3370389, by rfl⟩ : syracuseStep 8987705 = 6740779) B6740779
theorem B8766521 : Blo 1661530 8766521 := bstep (se 2 (by rfl) ⟨3287445, by rfl⟩ : syracuseStep 8766521 = 6574891) B6574891
theorem B23962823 : Blo 1661530 23962823 := bstep (se 1 (by rfl) ⟨17972117, by rfl⟩ : syracuseStep 23962823 = 35944235) B35944235
theorem B8414441 : Blo 1661530 8414441 := bstep (se 2 (by rfl) ⟨3155415, by rfl⟩ : syracuseStep 8414441 = 6310831) B6310831
theorem B5989727 : Blo 1661530 5989727 := bstep (se 1 (by rfl) ⟨4492295, by rfl⟩ : syracuseStep 5989727 = 8984591) B8984591
theorem B8414603 : Blo 1661530 8414603 := bstep (se 1 (by rfl) ⟨6310952, by rfl⟩ : syracuseStep 8414603 = 12621905) B12621905
theorem B18220439 : Blo 1661530 18220439 := bstep (se 1 (by rfl) ⟨13665329, by rfl⟩ : syracuseStep 18220439 = 27330659) B27330659
theorem B1869223 : Blo 1661530 1869223 := bstep (se 1 (by rfl) ⟨1401917, by rfl⟩ : syracuseStep 1869223 = 2803835) B2803835
theorem B10651169 : Blo 1661530 10651169 := bstep (se 2 (by rfl) ⟨3994188, by rfl⟩ : syracuseStep 10651169 = 7988377) B7988377
theorem B5326393 : Blo 1661530 5326393 := bstep (se 2 (by rfl) ⟨1997397, by rfl⟩ : syracuseStep 5326393 = 3994795) B3994795
theorem B3548767 : Blo 1661530 3548767 := bstep (se 1 (by rfl) ⟨2661575, by rfl⟩ : syracuseStep 3548767 = 5323151) B5323151
theorem B13666153 : Blo 1661530 13666153 := bstep (se 2 (by rfl) ⟨5124807, by rfl⟩ : syracuseStep 13666153 = 10249615) B10249615
theorem B1869799 : Blo 1661530 1869799 := bstep (se 1 (by rfl) ⟨1402349, by rfl⟩ : syracuseStep 1869799 = 2804699) B2804699
theorem B2492681 : Blo 1661530 2492681 := bstep (se 2 (by rfl) ⟨934755, by rfl⟩ : syracuseStep 2492681 = 1869511) B1869511
theorem B2492783 : Blo 1661530 2492783 := bstep (se 1 (by rfl) ⟨1869587, by rfl⟩ : syracuseStep 2492783 = 3739175) B3739175
theorem B14395877 : Blo 1661530 14395877 := bstep (se 4 (by rfl) ⟨1349613, by rfl⟩ : syracuseStep 14395877 = 2699227) B2699227
theorem B2804287 : Blo 1661530 2804287 := bstep (se 1 (by rfl) ⟨2103215, by rfl⟩ : syracuseStep 2804287 = 4206431) B4206431
theorem B2697799 : Blo 1661530 2697799 := bstep (se 1 (by rfl) ⟨2023349, by rfl⟩ : syracuseStep 2697799 = 4046699) B4046699
theorem B2492999 : Blo 1661530 2492999 := bstep (se 1 (by rfl) ⟨1869749, by rfl⟩ : syracuseStep 2492999 = 3739499) B3739499
theorem B2493035 : Blo 1661530 2493035 := bstep (se 1 (by rfl) ⟨1869776, by rfl⟩ : syracuseStep 2493035 = 3739553) B3739553
theorem B5327635 : Blo 1661530 5327635 := bstep (se 1 (by rfl) ⟨3995726, by rfl⟩ : syracuseStep 5327635 = 7991453) B7991453
theorem B2493263 : Blo 1661530 2493263 := bstep (se 1 (by rfl) ⟨1869947, by rfl⟩ : syracuseStep 2493263 = 3739895) B3739895
theorem B3738599 : Blo 1661530 3738599 := bstep (se 1 (by rfl) ⟨2803949, by rfl⟩ : syracuseStep 3738599 = 5607899) B5607899
theorem B7097483 : Blo 1661530 7097483 := bstep (se 1 (by rfl) ⟨5323112, by rfl⟩ : syracuseStep 7097483 = 10646225) B10646225
theorem B9464971 : Blo 1661530 9464971 := bstep (se 1 (by rfl) ⟨7098728, by rfl⟩ : syracuseStep 9464971 = 14197457) B14197457
theorem B15977675 : Blo 1661530 15977675 := bstep (se 1 (by rfl) ⟨11983256, by rfl⟩ : syracuseStep 15977675 = 23966513) B23966513
theorem B4205783 : Blo 1661530 4205783 := bstep (se 1 (by rfl) ⟨3154337, by rfl⟩ : syracuseStep 4205783 = 6308675) B6308675
theorem B2493659 : Blo 1661530 2493659 := bstep (se 1 (by rfl) ⟨1870244, by rfl⟩ : syracuseStep 2493659 = 3740489) B3740489
theorem B2133211 : Blo 1661530 2133211 := bstep (se 1 (by rfl) ⟨1599908, by rfl⟩ : syracuseStep 2133211 = 3199817) B3199817
theorem B2804969 : Blo 1661530 2804969 := bstep (se 2 (by rfl) ⟨1051863, by rfl⟩ : syracuseStep 2804969 = 2103727) B2103727
theorem B2805023 : Blo 1661530 2805023 := bstep (se 1 (by rfl) ⟨2103767, by rfl⟩ : syracuseStep 2805023 = 4207535) B4207535
theorem B3738977 : Blo 1661530 3738977 := bstep (se 2 (by rfl) ⟨1402116, by rfl⟩ : syracuseStep 3738977 = 2804233) B2804233
theorem B2493833 : Blo 1661530 2493833 := bstep (se 2 (by rfl) ⟨935187, by rfl⟩ : syracuseStep 2493833 = 1870375) B1870375
theorem B3739067 : Blo 1661530 3739067 := bstep (se 1 (by rfl) ⟨2804300, by rfl⟩ : syracuseStep 3739067 = 5608601) B5608601
theorem B40431035 : Blo 1661530 40431035 := bstep (se 1 (by rfl) ⟨30323276, by rfl⟩ : syracuseStep 40431035 = 60646553) B60646553
theorem B3550663 : Blo 1661530 3550663 := bstep (se 1 (by rfl) ⟨2662997, by rfl⟩ : syracuseStep 3550663 = 5325995) B5325995
theorem B21302747 : Blo 1661530 21302747 := bstep (se 1 (by rfl) ⟨15977060, by rfl⟩ : syracuseStep 21302747 = 31954121) B31954121
theorem B4492793 : Blo 1661530 4492793 := bstep (se 2 (by rfl) ⟨1684797, by rfl⟩ : syracuseStep 4492793 = 3369595) B3369595
theorem B3739193 : Blo 1661530 3739193 := bstep (se 2 (by rfl) ⟨1402197, by rfl⟩ : syracuseStep 3739193 = 2804395) B2804395
theorem B12619475 : Blo 1661530 12619475 := bstep (se 1 (by rfl) ⟨9464606, by rfl⟩ : syracuseStep 12619475 = 18929213) B18929213
theorem B2494187 : Blo 1661530 2494187 := bstep (se 1 (by rfl) ⟨1870640, by rfl⟩ : syracuseStep 2494187 = 3741281) B3741281
theorem B4493161 : Blo 1661530 4493161 := bstep (se 2 (by rfl) ⟨1684935, by rfl⟩ : syracuseStep 4493161 = 3369871) B3369871
theorem B5992321 : Blo 1661530 5992321 := bstep (se 2 (by rfl) ⟨2247120, by rfl⟩ : syracuseStep 5992321 = 4494241) B4494241
theorem B5689217 : Blo 1661530 5689217 := bstep (se 2 (by rfl) ⟨2133456, by rfl⟩ : syracuseStep 5689217 = 4266913) B4266913
theorem B2494415 : Blo 1661530 2494415 := bstep (se 1 (by rfl) ⟨1870811, by rfl⟩ : syracuseStep 2494415 = 3741623) B3741623
theorem B14045251 : Blo 1661530 14045251 := bstep (se 1 (by rfl) ⟨10533938, by rfl⟩ : syracuseStep 14045251 = 21067877) B21067877
theorem B3739859 : Blo 1661530 3739859 := bstep (se 1 (by rfl) ⟨2804894, by rfl⟩ : syracuseStep 3739859 = 5609789) B5609789
theorem B3739913 : Blo 1661530 3739913 := bstep (se 2 (by rfl) ⟨1402467, by rfl⟩ : syracuseStep 3739913 = 2804935) B2804935
theorem B3740129 : Blo 1661530 3740129 := bstep (se 2 (by rfl) ⟨1402548, by rfl⟩ : syracuseStep 3740129 = 2805097) B2805097
theorem B4207099 : Blo 1661530 4207099 := bstep (se 1 (by rfl) ⟨3155324, by rfl⟩ : syracuseStep 4207099 = 6310649) B6310649
theorem B8417843 : Blo 1661530 8417843 := bstep (se 1 (by rfl) ⟨6313382, by rfl⟩ : syracuseStep 8417843 = 12626765) B12626765
theorem B5608007 : Blo 1661530 5608007 := bstep (se 1 (by rfl) ⟨4206005, by rfl⟩ : syracuseStep 5608007 = 8412011) B8412011
theorem B4207211 : Blo 1661530 4207211 := bstep (se 1 (by rfl) ⟨3155408, by rfl⟩ : syracuseStep 4207211 = 6310817) B6310817
theorem B3740435 : Blo 1661530 3740435 := bstep (se 1 (by rfl) ⟨2805326, by rfl⟩ : syracuseStep 3740435 = 5610653) B5610653
theorem B21893917 : Blo 1661530 21893917 := bstep (se 3 (by rfl) ⟨4105109, by rfl⟩ : syracuseStep 21893917 = 8210219) B8210219
theorem B9466703 : Blo 1661530 9466703 := bstep (se 1 (by rfl) ⟨7100027, by rfl⟩ : syracuseStep 9466703 = 14200055) B14200055
theorem B2560999 : Blo 1661530 2560999 := bstep (se 1 (by rfl) ⟨1920749, by rfl⟩ : syracuseStep 2560999 = 3841499) B3841499
theorem B5608439 : Blo 1661530 5608439 := bstep (se 1 (by rfl) ⟨4206329, by rfl⟩ : syracuseStep 5608439 = 8412659) B8412659
theorem B3740795 : Blo 1661530 3740795 := bstep (se 1 (by rfl) ⟨2805596, by rfl⟩ : syracuseStep 3740795 = 5611193) B5611193
theorem B2667739 : Blo 1661530 2667739 := bstep (se 1 (by rfl) ⟨2000804, by rfl⟩ : syracuseStep 2667739 = 4001609) B4001609
theorem B4207859 : Blo 1661530 4207859 := bstep (se 1 (by rfl) ⟨3155894, by rfl⟩ : syracuseStep 4207859 = 6311789) B6311789
theorem B3740921 : Blo 1661530 3740921 := bstep (se 2 (by rfl) ⟨1402845, by rfl⟩ : syracuseStep 3740921 = 2805691) B2805691
theorem B3741065 : Blo 1661530 3741065 := bstep (se 2 (by rfl) ⟨1402899, by rfl⟩ : syracuseStep 3741065 = 2805799) B2805799
theorem B4208071 : Blo 1661530 4208071 := bstep (se 1 (by rfl) ⟨3156053, by rfl⟩ : syracuseStep 4208071 = 6312107) B6312107
theorem B1996283 : Blo 1661530 1996283 := bstep (se 1 (by rfl) ⟨1497212, by rfl⟩ : syracuseStep 1996283 = 2994425) B2994425
theorem B10106375 : Blo 1661530 10106375 := bstep (se 1 (by rfl) ⟨7579781, by rfl⟩ : syracuseStep 10106375 = 15159563) B15159563
theorem B3741191 : Blo 1661530 3741191 := bstep (se 1 (by rfl) ⟨2805893, by rfl⟩ : syracuseStep 3741191 = 5611787) B5611787
theorem B3741371 : Blo 1661530 3741371 := bstep (se 1 (by rfl) ⟨2806028, by rfl⟩ : syracuseStep 3741371 = 5612057) B5612057
theorem B1996591 : Blo 1661530 1996591 := bstep (se 1 (by rfl) ⟨1497443, by rfl⟩ : syracuseStep 1996591 = 2994887) B2994887
theorem B3741497 : Blo 1661530 3741497 := bstep (se 2 (by rfl) ⟨1403061, by rfl⟩ : syracuseStep 3741497 = 2806123) B2806123
theorem B5609303 : Blo 1661530 5609303 := bstep (se 1 (by rfl) ⟨4206977, by rfl⟩ : syracuseStep 5609303 = 8413955) B8413955
theorem B1775567 : Blo 1661530 1775567 := bstep (se 1 (by rfl) ⟨1331675, by rfl⟩ : syracuseStep 1775567 = 2663351) B2663351
theorem B8411687 : Blo 1661530 8411687 := bstep (se 1 (by rfl) ⟨6308765, by rfl⟩ : syracuseStep 8411687 = 12617531) B12617531
theorem B2366015 : Blo 1661530 2366015 := bstep (se 1 (by rfl) ⟨1774511, by rfl⟩ : syracuseStep 2366015 = 3549023) B3549023
theorem B15170111 : Blo 1661530 15170111 := bstep (se 1 (by rfl) ⟨11377583, by rfl⟩ : syracuseStep 15170111 = 22755167) B22755167
theorem B1661663 : Blo 1661530 1661663 := bstep (se 1 (by rfl) ⟨1246247, by rfl⟩ : syracuseStep 1661663 = 2492495) B2492495
theorem B8985367 : Blo 1661530 8985367 := bstep (se 1 (by rfl) ⟨6739025, by rfl⟩ : syracuseStep 8985367 = 13478051) B13478051
theorem B91011869 : Blo 1661530 91011869 := bstep (se 3 (by rfl) ⟨17064725, by rfl⟩ : syracuseStep 91011869 = 34129451) B34129451
theorem B1661743 : Blo 1661530 1661743 := bstep (se 1 (by rfl) ⟨1246307, by rfl⟩ : syracuseStep 1661743 = 2492615) B2492615
theorem B5610383 : Blo 1661530 5610383 := bstep (se 1 (by rfl) ⟨4207787, by rfl⟩ : syracuseStep 5610383 = 8415575) B8415575
theorem B1661851 : Blo 1661530 1661851 := bstep (se 1 (by rfl) ⟨1246388, by rfl⟩ : syracuseStep 1661851 = 2492777) B2492777
theorem B9468845 : Blo 1661530 9468845 := bstep (se 3 (by rfl) ⟨1775408, by rfl⟩ : syracuseStep 9468845 = 3550817) B3550817
theorem B13474745 : Blo 1661530 13474745 := bstep (se 2 (by rfl) ⟨5053029, by rfl⟩ : syracuseStep 13474745 = 10106059) B10106059
theorem B1661903 : Blo 1661530 1661903 := bstep (se 1 (by rfl) ⟨1246427, by rfl⟩ : syracuseStep 1661903 = 2492855) B2492855
theorem B1661927 : Blo 1661530 1661927 := bstep (se 1 (by rfl) ⟨1246445, by rfl⟩ : syracuseStep 1661927 = 2492891) B2492891
theorem B32398355 : Blo 1661530 32398355 := bstep (se 1 (by rfl) ⟨24298766, by rfl⟩ : syracuseStep 32398355 = 48597533) B48597533
theorem B12622877 : Blo 1661530 12622877 := bstep (se 3 (by rfl) ⟨2366789, by rfl⟩ : syracuseStep 12622877 = 4733579) B4733579
theorem B1662239 : Blo 1661530 1662239 := bstep (se 1 (by rfl) ⟨1246679, by rfl⟩ : syracuseStep 1662239 = 2493359) B2493359
theorem B1662299 : Blo 1661530 1662299 := bstep (se 1 (by rfl) ⟨1246724, by rfl⟩ : syracuseStep 1662299 = 2493449) B2493449
theorem B1662319 : Blo 1661530 1662319 := bstep (se 1 (by rfl) ⟨1246739, by rfl⟩ : syracuseStep 1662319 = 2493479) B2493479
theorem B2104699 : Blo 1661530 2104699 := bstep (se 1 (by rfl) ⟨1578524, by rfl⟩ : syracuseStep 2104699 = 3157049) B3157049
theorem B1662375 : Blo 1661530 1662375 := bstep (se 1 (by rfl) ⟨1246781, by rfl⟩ : syracuseStep 1662375 = 2493563) B2493563
theorem B1662459 : Blo 1661530 1662459 := bstep (se 1 (by rfl) ⟨1246844, by rfl⟩ : syracuseStep 1662459 = 2493689) B2493689
theorem B1662527 : Blo 1661530 1662527 := bstep (se 1 (by rfl) ⟨1246895, by rfl⟩ : syracuseStep 1662527 = 2493791) B2493791
theorem B1662535 : Blo 1661530 1662535 := bstep (se 1 (by rfl) ⟨1246901, by rfl⟩ : syracuseStep 1662535 = 2493803) B2493803
theorem B10649171 : Blo 1661530 10649171 := bstep (se 1 (by rfl) ⟨7986878, by rfl⟩ : syracuseStep 10649171 = 15973757) B15973757
theorem B2662075 : Blo 1661530 2662075 := bstep (se 1 (by rfl) ⟨1996556, by rfl⟩ : syracuseStep 2662075 = 3993113) B3993113
theorem B1662687 : Blo 1661530 1662687 := bstep (se 1 (by rfl) ⟨1247015, by rfl⟩ : syracuseStep 1662687 = 2494031) B2494031
theorem B1662767 : Blo 1661530 1662767 := bstep (se 1 (by rfl) ⟨1247075, by rfl⟩ : syracuseStep 1662767 = 2494151) B2494151
theorem B3792745 : Blo 1661530 3792745 := bstep (se 2 (by rfl) ⟨1422279, by rfl⟩ : syracuseStep 3792745 = 2844559) B2844559
theorem B1662875 : Blo 1661530 1662875 := bstep (se 1 (by rfl) ⟨1247156, by rfl⟩ : syracuseStep 1662875 = 2494313) B2494313
theorem B9469871 : Blo 1661530 9469871 := bstep (se 1 (by rfl) ⟨7102403, by rfl⟩ : syracuseStep 9469871 = 14204807) B14204807
theorem B1662927 : Blo 1661530 1662927 := bstep (se 1 (by rfl) ⟨1247195, by rfl⟩ : syracuseStep 1662927 = 2494391) B2494391
theorem B1662951 : Blo 1661530 1662951 := bstep (se 1 (by rfl) ⟨1247213, by rfl⟩ : syracuseStep 1662951 = 2494427) B2494427
theorem B18727001 : Blo 1661530 18727001 := bstep (se 2 (by rfl) ⟨7022625, by rfl⟩ : syracuseStep 18727001 = 14045251) B14045251
theorem B5611895 : Blo 1661530 5611895 := bstep (se 1 (by rfl) ⟨4208921, by rfl⟩ : syracuseStep 5611895 = 8417843) B8417843
theorem B42607133 : Blo 1661530 42607133 := bstep (se 3 (by rfl) ⟨7988837, by rfl⟩ : syracuseStep 42607133 = 15977675) B15977675
theorem B11977379 : Blo 1661530 11977379 := bstep (se 1 (by rfl) ⟨8983034, by rfl⟩ : syracuseStep 11977379 = 17966069) B17966069
theorem B3597065 : Blo 1661530 3597065 := bstep (se 2 (by rfl) ⟨1348899, by rfl⟩ : syracuseStep 3597065 = 2697799) B2697799
theorem B15975215 : Blo 1661530 15975215 := bstep (se 1 (by rfl) ⟨11981411, by rfl⟩ : syracuseStep 15975215 = 23962823) B23962823
theorem B7103513 : Blo 1661530 7103513 := bstep (se 2 (by rfl) ⟨2663817, by rfl⟩ : syracuseStep 7103513 = 5327635) B5327635
theorem B107816093 : Blo 1661530 107816093 := bstep (se 3 (by rfl) ⟨20215517, by rfl⟩ : syracuseStep 107816093 = 40431035) B40431035
theorem B6309373 : Blo 1661530 6309373 := bstep (se 3 (by rfl) ⟨1183007, by rfl⟩ : syracuseStep 6309373 = 2366015) B2366015
theorem B3556985 : Blo 1661530 3556985 := bstep (se 2 (by rfl) ⟨1333869, by rfl⟩ : syracuseStep 3556985 = 2667739) B2667739
theorem B2844281 : Blo 1661530 2844281 := bstep (se 2 (by rfl) ⟨1066605, by rfl⟩ : syracuseStep 2844281 = 2133211) B2133211
theorem B20227973 : Blo 1661530 20227973 := bstep (se 4 (by rfl) ⟨1896372, by rfl⟩ : syracuseStep 20227973 = 3792745) B3792745
theorem B2492297 : Blo 1661530 2492297 := bstep (se 2 (by rfl) ⟨934611, by rfl⟩ : syracuseStep 2492297 = 1869223) B1869223
theorem B2492399 : Blo 1661530 2492399 := bstep (se 1 (by rfl) ⟨1869299, by rfl⟩ : syracuseStep 2492399 = 3738599) B3738599
theorem B8415251 : Blo 1661530 8415251 := bstep (se 1 (by rfl) ⟨6311438, by rfl⟩ : syracuseStep 8415251 = 12622877) B12622877
theorem B2803855 : Blo 1661530 2803855 := bstep (se 1 (by rfl) ⟨2102891, by rfl⟩ : syracuseStep 2803855 = 4205783) B4205783
theorem B1869979 : Blo 1661530 1869979 := bstep (se 1 (by rfl) ⟨1402484, by rfl⟩ : syracuseStep 1869979 = 2804969) B2804969
theorem B1870015 : Blo 1661530 1870015 := bstep (se 1 (by rfl) ⟨1402511, by rfl⟩ : syracuseStep 1870015 = 2805023) B2805023
theorem B2492651 : Blo 1661530 2492651 := bstep (se 1 (by rfl) ⟨1869488, by rfl⟩ : syracuseStep 2492651 = 3738977) B3738977
theorem B3549433 : Blo 1661530 3549433 := bstep (se 2 (by rfl) ⟨1331037, by rfl⟩ : syracuseStep 3549433 = 2662075) B2662075
theorem B2492711 : Blo 1661530 2492711 := bstep (se 1 (by rfl) ⟨1869533, by rfl⟩ : syracuseStep 2492711 = 3739067) B3739067
theorem B2492795 : Blo 1661530 2492795 := bstep (se 1 (by rfl) ⟨1869596, by rfl⟩ : syracuseStep 2492795 = 3739193) B3739193
theorem B5990881 : Blo 1661530 5990881 := bstep (se 2 (by rfl) ⟨2246580, by rfl⟩ : syracuseStep 5990881 = 4493161) B4493161
theorem B18221537 : Blo 1661530 18221537 := bstep (se 2 (by rfl) ⟨6833076, by rfl⟩ : syracuseStep 18221537 = 13666153) B13666153
theorem B7989761 : Blo 1661530 7989761 := bstep (se 2 (by rfl) ⟨2996160, by rfl⟩ : syracuseStep 7989761 = 5992321) B5992321
theorem B2493065 : Blo 1661530 2493065 := bstep (se 2 (by rfl) ⟨934899, by rfl⟩ : syracuseStep 2493065 = 1869799) B1869799
theorem B15575789 : Blo 1661530 15575789 := bstep (se 3 (by rfl) ⟨2920460, by rfl⟩ : syracuseStep 15575789 = 5840921) B5840921
theorem B2493239 : Blo 1661530 2493239 := bstep (se 1 (by rfl) ⟨1869929, by rfl⟩ : syracuseStep 2493239 = 3739859) B3739859
theorem B2493275 : Blo 1661530 2493275 := bstep (se 1 (by rfl) ⟨1869956, by rfl⟩ : syracuseStep 2493275 = 3739913) B3739913
theorem B2493419 : Blo 1661530 2493419 := bstep (se 1 (by rfl) ⟨1870064, by rfl⟩ : syracuseStep 2493419 = 3740129) B3740129
theorem B3738671 : Blo 1661530 3738671 := bstep (se 1 (by rfl) ⟨2804003, by rfl⟩ : syracuseStep 3738671 = 5608007) B5608007
theorem B2804807 : Blo 1661530 2804807 := bstep (se 1 (by rfl) ⟨2103605, by rfl⟩ : syracuseStep 2804807 = 4207211) B4207211
theorem B2493623 : Blo 1661530 2493623 := bstep (se 1 (by rfl) ⟨1870217, by rfl⟩ : syracuseStep 2493623 = 3740435) B3740435
theorem B6311135 : Blo 1661530 6311135 := bstep (se 1 (by rfl) ⟨4733351, by rfl⟩ : syracuseStep 6311135 = 9466703) B9466703
theorem B3738959 : Blo 1661530 3738959 := bstep (se 1 (by rfl) ⟨2804219, by rfl⟩ : syracuseStep 3738959 = 5608439) B5608439
theorem B5991803 : Blo 1661530 5991803 := bstep (se 1 (by rfl) ⟨4493852, by rfl⟩ : syracuseStep 5991803 = 8987705) B8987705
theorem B5844347 : Blo 1661530 5844347 := bstep (se 1 (by rfl) ⟨4383260, by rfl⟩ : syracuseStep 5844347 = 8766521) B8766521
theorem B2493863 : Blo 1661530 2493863 := bstep (se 1 (by rfl) ⟨1870397, by rfl⟩ : syracuseStep 2493863 = 3740795) B3740795
theorem B3739049 : Blo 1661530 3739049 := bstep (se 2 (by rfl) ⟨1402143, by rfl⟩ : syracuseStep 3739049 = 2804287) B2804287
theorem B2805239 : Blo 1661530 2805239 := bstep (se 1 (by rfl) ⟨2103929, by rfl⟩ : syracuseStep 2805239 = 4207859) B4207859
theorem B2493947 : Blo 1661530 2493947 := bstep (se 1 (by rfl) ⟨1870460, by rfl⟩ : syracuseStep 2493947 = 3740921) B3740921
theorem B3993151 : Blo 1661530 3993151 := bstep (se 1 (by rfl) ⟨2994863, by rfl⟩ : syracuseStep 3993151 = 5989727) B5989727
theorem B2494043 : Blo 1661530 2494043 := bstep (se 1 (by rfl) ⟨1870532, by rfl⟩ : syracuseStep 2494043 = 3741065) B3741065
theorem B14790305 : Blo 1661530 14790305 := bstep (se 2 (by rfl) ⟨5546364, by rfl⟩ : syracuseStep 14790305 = 11092729) B11092729
theorem B2494127 : Blo 1661530 2494127 := bstep (se 1 (by rfl) ⟨1870595, by rfl⟩ : syracuseStep 2494127 = 3741191) B3741191
theorem B11980489 : Blo 1661530 11980489 := bstep (se 2 (by rfl) ⟨4492683, by rfl⟩ : syracuseStep 11980489 = 8985367) B8985367
theorem B29191889 : Blo 1661530 29191889 := bstep (se 2 (by rfl) ⟨10946958, by rfl⟩ : syracuseStep 29191889 = 21893917) B21893917
theorem B2494247 : Blo 1661530 2494247 := bstep (se 1 (by rfl) ⟨1870685, by rfl⟩ : syracuseStep 2494247 = 3741371) B3741371
theorem B2494331 : Blo 1661530 2494331 := bstep (se 1 (by rfl) ⟨1870748, by rfl⟩ : syracuseStep 2494331 = 3741497) B3741497
theorem B3739535 : Blo 1661530 3739535 := bstep (se 1 (by rfl) ⟨2804651, by rfl⟩ : syracuseStep 3739535 = 5609303) B5609303
theorem B11980781 : Blo 1661530 11980781 := bstep (se 3 (by rfl) ⟨2246396, by rfl⟩ : syracuseStep 11980781 = 4492793) B4492793
theorem B12619961 : Blo 1661530 12619961 := bstep (se 2 (by rfl) ⟨4732485, by rfl⟩ : syracuseStep 12619961 = 9464971) B9464971
theorem B9597251 : Blo 1661530 9597251 := bstep (se 1 (by rfl) ⟨7197938, by rfl⟩ : syracuseStep 9597251 = 14395877) B14395877
theorem B5607791 : Blo 1661530 5607791 := bstep (se 1 (by rfl) ⟨4205843, by rfl⟩ : syracuseStep 5607791 = 8411687) B8411687
theorem B10113407 : Blo 1661530 10113407 := bstep (se 1 (by rfl) ⟨7585055, by rfl⟩ : syracuseStep 10113407 = 15170111) B15170111
theorem B2806265 : Blo 1661530 2806265 := bstep (se 2 (by rfl) ⟨1052349, by rfl⟩ : syracuseStep 2806265 = 2104699) B2104699
theorem B60674579 : Blo 1661530 60674579 := bstep (se 1 (by rfl) ⟨45505934, by rfl⟩ : syracuseStep 60674579 = 91011869) B91011869
theorem B3740255 : Blo 1661530 3740255 := bstep (se 1 (by rfl) ⟨2805191, by rfl⟩ : syracuseStep 3740255 = 5610383) B5610383
theorem B6312563 : Blo 1661530 6312563 := bstep (se 1 (by rfl) ⟨4734422, by rfl⟩ : syracuseStep 6312563 = 9468845) B9468845
theorem B8983163 : Blo 1661530 8983163 := bstep (se 1 (by rfl) ⟨6737372, by rfl⟩ : syracuseStep 8983163 = 13474745) B13474745
theorem B21598903 : Blo 1661530 21598903 := bstep (se 1 (by rfl) ⟨16199177, by rfl⟩ : syracuseStep 21598903 = 32398355) B32398355
theorem B4731655 : Blo 1661530 4731655 := bstep (se 1 (by rfl) ⟨3548741, by rfl⟩ : syracuseStep 4731655 = 7097483) B7097483
theorem B4731689 : Blo 1661530 4731689 := bstep (se 2 (by rfl) ⟨1774383, by rfl⟩ : syracuseStep 4731689 = 3548767) B3548767
theorem B14201831 : Blo 1661530 14201831 := bstep (se 1 (by rfl) ⟨10651373, by rfl⟩ : syracuseStep 14201831 = 21302747) B21302747
theorem B7099447 : Blo 1661530 7099447 := bstep (se 1 (by rfl) ⟨5324585, by rfl⟩ : syracuseStep 7099447 = 10649171) B10649171
theorem B6313247 : Blo 1661530 6313247 := bstep (se 1 (by rfl) ⟨4734935, by rfl⟩ : syracuseStep 6313247 = 9469871) B9469871
theorem B34133399 : Blo 1661530 34133399 := bstep (se 1 (by rfl) ⟨25600049, by rfl⟩ : syracuseStep 34133399 = 51200099) B51200099
theorem B3741083 : Blo 1661530 3741083 := bstep (se 1 (by rfl) ⟨2805812, by rfl⟩ : syracuseStep 3741083 = 5611625) B5611625
theorem B5609195 : Blo 1661530 5609195 := bstep (se 1 (by rfl) ⟨4206896, by rfl⟩ : syracuseStep 5609195 = 8413793) B8413793
theorem B7296983 : Blo 1661530 7296983 := bstep (se 1 (by rfl) ⟨5472737, by rfl⟩ : syracuseStep 7296983 = 10945475) B10945475
theorem B3741659 : Blo 1661530 3741659 := bstep (se 1 (by rfl) ⟨2806244, by rfl⟩ : syracuseStep 3741659 = 5612489) B5612489
theorem B5609465 : Blo 1661530 5609465 := bstep (se 2 (by rfl) ⟨2103549, by rfl⟩ : syracuseStep 5609465 = 4207099) B4207099
theorem B5609627 : Blo 1661530 5609627 := bstep (se 1 (by rfl) ⟨4207220, by rfl⟩ : syracuseStep 5609627 = 8414441) B8414441
theorem B5609735 : Blo 1661530 5609735 := bstep (se 1 (by rfl) ⟨4207301, by rfl⟩ : syracuseStep 5609735 = 8414603) B8414603
theorem B12146959 : Blo 1661530 12146959 := bstep (se 1 (by rfl) ⟨9110219, by rfl⟩ : syracuseStep 12146959 = 18220439) B18220439
theorem B7100779 : Blo 1661530 7100779 := bstep (se 1 (by rfl) ⟨5325584, by rfl⟩ : syracuseStep 7100779 = 10651169) B10651169
theorem B3414665 : Blo 1661530 3414665 := bstep (se 2 (by rfl) ⟨1280499, by rfl⟩ : syracuseStep 3414665 = 2560999) B2560999
theorem B5323421 : Blo 1661530 5323421 := bstep (se 3 (by rfl) ⟨998141, by rfl⟩ : syracuseStep 5323421 = 1996283) B1996283
theorem B26950333 : Blo 1661530 26950333 := bstep (se 3 (by rfl) ⟨5053187, by rfl⟩ : syracuseStep 26950333 = 10106375) B10106375
theorem B1661787 : Blo 1661530 1661787 := bstep (se 1 (by rfl) ⟨1246340, by rfl⟩ : syracuseStep 1661787 = 2492681) B2492681
theorem B1661855 : Blo 1661530 1661855 := bstep (se 1 (by rfl) ⟨1246391, by rfl⟩ : syracuseStep 1661855 = 2492783) B2492783
theorem B1661999 : Blo 1661530 1661999 := bstep (se 1 (by rfl) ⟨1246499, by rfl⟩ : syracuseStep 1661999 = 2492999) B2492999
theorem B1662023 : Blo 1661530 1662023 := bstep (se 1 (by rfl) ⟨1246517, by rfl⟩ : syracuseStep 1662023 = 2493035) B2493035
theorem B1662175 : Blo 1661530 1662175 := bstep (se 1 (by rfl) ⟨1246631, by rfl⟩ : syracuseStep 1662175 = 2493263) B2493263
theorem B5610761 : Blo 1661530 5610761 := bstep (se 2 (by rfl) ⟨2104035, by rfl⟩ : syracuseStep 5610761 = 4208071) B4208071
theorem B4734217 : Blo 1661530 4734217 := bstep (se 2 (by rfl) ⟨1775331, by rfl⟩ : syracuseStep 4734217 = 3550663) B3550663
theorem B7101857 : Blo 1661530 7101857 := bstep (se 2 (by rfl) ⟨2663196, by rfl⟩ : syracuseStep 7101857 = 5326393) B5326393
theorem B1662439 : Blo 1661530 1662439 := bstep (se 1 (by rfl) ⟨1246829, by rfl⟩ : syracuseStep 1662439 = 2493659) B2493659
theorem B1662555 : Blo 1661530 1662555 := bstep (se 1 (by rfl) ⟨1246916, by rfl⟩ : syracuseStep 1662555 = 2493833) B2493833
theorem B2662121 : Blo 1661530 2662121 := bstep (se 2 (by rfl) ⟨998295, by rfl⟩ : syracuseStep 2662121 = 1996591) B1996591
theorem B8412983 : Blo 1661530 8412983 := bstep (se 1 (by rfl) ⟨6309737, by rfl⟩ : syracuseStep 8412983 = 12619475) B12619475
theorem B1662791 : Blo 1661530 1662791 := bstep (se 1 (by rfl) ⟨1247093, by rfl⟩ : syracuseStep 1662791 = 2494187) B2494187
theorem B4734845 : Blo 1661530 4734845 := bstep (se 3 (by rfl) ⟨887783, by rfl⟩ : syracuseStep 4734845 = 1775567) B1775567
theorem B3792811 : Blo 1661530 3792811 := bstep (se 1 (by rfl) ⟨2844608, by rfl⟩ : syracuseStep 3792811 = 5689217) B5689217
theorem B1662943 : Blo 1661530 1662943 := bstep (se 1 (by rfl) ⟨1247207, by rfl⟩ : syracuseStep 1662943 = 2494415) B2494415
theorem B12484667 : Blo 1661530 12484667 := bstep (se 1 (by rfl) ⟨9363500, by rfl⟩ : syracuseStep 12484667 = 18727001) B18727001
theorem B8413307 : Blo 1661530 8413307 := bstep (se 1 (by rfl) ⟨6309980, by rfl⟩ : syracuseStep 8413307 = 12619961) B12619961
theorem B6742271 : Blo 1661530 6742271 := bstep (se 1 (by rfl) ⟨5056703, by rfl⟩ : syracuseStep 6742271 = 10113407) B10113407
theorem B16195945 : Blo 1661530 16195945 := bstep (se 2 (by rfl) ⟨6073479, by rfl⟩ : syracuseStep 16195945 = 12146959) B12146959
theorem B3154459 : Blo 1661530 3154459 := bstep (se 1 (by rfl) ⟨2365844, by rfl⟩ : syracuseStep 3154459 = 4731689) B4731689
theorem B10650143 : Blo 1661530 10650143 := bstep (se 1 (by rfl) ⟨7987607, by rfl⟩ : syracuseStep 10650143 = 15975215) B15975215
theorem B7987841 : Blo 1661530 7987841 := bstep (se 2 (by rfl) ⟨2995440, by rfl⟩ : syracuseStep 7987841 = 5990881) B5990881
theorem B4735675 : Blo 1661530 4735675 := bstep (se 1 (by rfl) ⟨3551756, by rfl⟩ : syracuseStep 4735675 = 7103513) B7103513
theorem B71877395 : Blo 1661530 71877395 := bstep (se 1 (by rfl) ⟨53908046, by rfl⟩ : syracuseStep 71877395 = 107816093) B107816093
theorem B25592669 : Blo 1661530 25592669 := bstep (se 3 (by rfl) ⟨4798625, by rfl⟩ : syracuseStep 25592669 = 9597251) B9597251
theorem B6308873 : Blo 1661530 6308873 := bstep (se 2 (by rfl) ⟨2365827, by rfl⟩ : syracuseStep 6308873 = 4731655) B4731655
theorem B23955101 : Blo 1661530 23955101 := bstep (se 3 (by rfl) ⟨4491581, by rfl⟩ : syracuseStep 23955101 = 8983163) B8983163
theorem B5326507 : Blo 1661530 5326507 := bstep (se 1 (by rfl) ⟨3994880, by rfl⟩ : syracuseStep 5326507 = 7989761) B7989761
theorem B3548947 : Blo 1661530 3548947 := bstep (se 1 (by rfl) ⟨2661710, by rfl⟩ : syracuseStep 3548947 = 5323421) B5323421
theorem B2492447 : Blo 1661530 2492447 := bstep (se 1 (by rfl) ⟨1869335, by rfl⟩ : syracuseStep 2492447 = 3738671) B3738671
theorem B1869871 : Blo 1661530 1869871 := bstep (se 1 (by rfl) ⟨1402403, by rfl⟩ : syracuseStep 1869871 = 2804807) B2804807
theorem B2492639 : Blo 1661530 2492639 := bstep (se 1 (by rfl) ⟨1869479, by rfl⟩ : syracuseStep 2492639 = 3738959) B3738959
theorem B2492699 : Blo 1661530 2492699 := bstep (se 1 (by rfl) ⟨1869524, by rfl⟩ : syracuseStep 2492699 = 3739049) B3739049
theorem B1870159 : Blo 1661530 1870159 := bstep (se 1 (by rfl) ⟨1402619, by rfl⟩ : syracuseStep 1870159 = 2805239) B2805239
theorem B5057081 : Blo 1661530 5057081 := bstep (se 2 (by rfl) ⟨1896405, by rfl⟩ : syracuseStep 5057081 = 3792811) B3792811
theorem B3156563 : Blo 1661530 3156563 := bstep (se 1 (by rfl) ⟨2367422, by rfl⟩ : syracuseStep 3156563 = 4734845) B4734845
theorem B2493023 : Blo 1661530 2493023 := bstep (se 1 (by rfl) ⟨1869767, by rfl⟩ : syracuseStep 2493023 = 3739535) B3739535
theorem B3738473 : Blo 1661530 3738473 := bstep (se 2 (by rfl) ⟨1401927, by rfl⟩ : syracuseStep 3738473 = 2803855) B2803855
theorem B2493305 : Blo 1661530 2493305 := bstep (se 2 (by rfl) ⟨934989, by rfl⟩ : syracuseStep 2493305 = 1869979) B1869979
theorem B3738527 : Blo 1661530 3738527 := bstep (se 1 (by rfl) ⟨2803895, by rfl⟩ : syracuseStep 3738527 = 5607791) B5607791
theorem B2493353 : Blo 1661530 2493353 := bstep (se 2 (by rfl) ⟨935007, by rfl⟩ : syracuseStep 2493353 = 1870015) B1870015
theorem B1870843 : Blo 1661530 1870843 := bstep (se 1 (by rfl) ⟨1403132, by rfl⟩ : syracuseStep 1870843 = 2806265) B2806265
theorem B28404755 : Blo 1661530 28404755 := bstep (se 1 (by rfl) ⟨21303566, by rfl⟩ : syracuseStep 28404755 = 42607133) B42607133
theorem B2493503 : Blo 1661530 2493503 := bstep (se 1 (by rfl) ⟨1870127, by rfl⟩ : syracuseStep 2493503 = 3740255) B3740255
theorem B28798537 : Blo 1661530 28798537 := bstep (se 2 (by rfl) ⟨10799451, by rfl⟩ : syracuseStep 28798537 = 21598903) B21598903
theorem B35933777 : Blo 1661530 35933777 := bstep (se 2 (by rfl) ⟨13475166, by rfl⟩ : syracuseStep 35933777 = 26950333) B26950333
theorem B2494055 : Blo 1661530 2494055 := bstep (se 1 (by rfl) ⟨1870541, by rfl⟩ : syracuseStep 2494055 = 3741083) B3741083
theorem B3739463 : Blo 1661530 3739463 := bstep (se 1 (by rfl) ⟨2804597, by rfl⟩ : syracuseStep 3739463 = 5609195) B5609195
theorem B48590765 : Blo 1661530 48590765 := bstep (se 3 (by rfl) ⟨9110768, by rfl⟩ : syracuseStep 48590765 = 18221537) B18221537
theorem B37941173 : Blo 1661530 37941173 := bstep (se 5 (by rfl) ⟨1778492, by rfl⟩ : syracuseStep 37941173 = 3556985) B3556985
theorem B2494439 : Blo 1661530 2494439 := bstep (se 1 (by rfl) ⟨1870829, by rfl⟩ : syracuseStep 2494439 = 3741659) B3741659
theorem B3739643 : Blo 1661530 3739643 := bstep (se 1 (by rfl) ⟨2804732, by rfl⟩ : syracuseStep 3739643 = 5609465) B5609465
theorem B215765045 : Blo 1661530 215765045 := bstep (se 5 (by rfl) ⟨10113986, by rfl⟩ : syracuseStep 215765045 = 20227973) B20227973
theorem B9465929 : Blo 1661530 9465929 := bstep (se 2 (by rfl) ⟨3549723, by rfl⟩ : syracuseStep 9465929 = 7099447) B7099447
theorem B3739751 : Blo 1661530 3739751 := bstep (se 1 (by rfl) ⟨2804813, by rfl⟩ : syracuseStep 3739751 = 5609627) B5609627
theorem B3739823 : Blo 1661530 3739823 := bstep (se 1 (by rfl) ⟨2804867, by rfl⟩ : syracuseStep 3739823 = 5609735) B5609735
theorem B6312289 : Blo 1661530 6312289 := bstep (se 2 (by rfl) ⟨2367108, by rfl⟩ : syracuseStep 6312289 = 4734217) B4734217
theorem B10383859 : Blo 1661530 10383859 := bstep (se 1 (by rfl) ⟨7787894, by rfl⟩ : syracuseStep 10383859 = 15575789) B15575789
theorem B4207423 : Blo 1661530 4207423 := bstep (se 1 (by rfl) ⟨3155567, by rfl⟩ : syracuseStep 4207423 = 6311135) B6311135
theorem B3740507 : Blo 1661530 3740507 := bstep (se 1 (by rfl) ⟨2805380, by rfl⟩ : syracuseStep 3740507 = 5610761) B5610761
theorem B3994535 : Blo 1661530 3994535 := bstep (se 1 (by rfl) ⟨2995901, by rfl⟩ : syracuseStep 3994535 = 5991803) B5991803
theorem B9860203 : Blo 1661530 9860203 := bstep (se 1 (by rfl) ⟨7395152, by rfl⟩ : syracuseStep 9860203 = 14790305) B14790305
theorem B19461259 : Blo 1661530 19461259 := bstep (se 1 (by rfl) ⟨14595944, by rfl⟩ : syracuseStep 19461259 = 29191889) B29191889
theorem B1774747 : Blo 1661530 1774747 := bstep (se 1 (by rfl) ⟨1331060, by rfl⟩ : syracuseStep 1774747 = 2662121) B2662121
theorem B5608655 : Blo 1661530 5608655 := bstep (se 1 (by rfl) ⟨4206491, by rfl⟩ : syracuseStep 5608655 = 8412983) B8412983
theorem B3741263 : Blo 1661530 3741263 := bstep (se 1 (by rfl) ⟨2805947, by rfl⟩ : syracuseStep 3741263 = 5611895) B5611895
theorem B4732577 : Blo 1661530 4732577 := bstep (se 2 (by rfl) ⟨1774716, by rfl⟩ : syracuseStep 4732577 = 3549433) B3549433
theorem B40449719 : Blo 1661530 40449719 := bstep (se 1 (by rfl) ⟨30337289, by rfl⟩ : syracuseStep 40449719 = 60674579) B60674579
theorem B4208375 : Blo 1661530 4208375 := bstep (se 1 (by rfl) ⟨3156281, by rfl⟩ : syracuseStep 4208375 = 6312563) B6312563
theorem B7984919 : Blo 1661530 7984919 := bstep (se 1 (by rfl) ⟨5988689, by rfl⟩ : syracuseStep 7984919 = 11977379) B11977379
theorem B9467705 : Blo 1661530 9467705 := bstep (se 2 (by rfl) ⟨3550389, by rfl⟩ : syracuseStep 9467705 = 7100779) B7100779
theorem B2398043 : Blo 1661530 2398043 := bstep (se 1 (by rfl) ⟨1798532, by rfl⟩ : syracuseStep 2398043 = 3597065) B3597065
theorem B9467887 : Blo 1661530 9467887 := bstep (se 1 (by rfl) ⟨7100915, by rfl⟩ : syracuseStep 9467887 = 14201831) B14201831
theorem B4208831 : Blo 1661530 4208831 := bstep (se 1 (by rfl) ⟨3156623, by rfl⟩ : syracuseStep 4208831 = 6313247) B6313247
theorem B22755599 : Blo 1661530 22755599 := bstep (se 1 (by rfl) ⟨17066699, by rfl⟩ : syracuseStep 22755599 = 34133399) B34133399
theorem B1661531 : Blo 1661530 1661531 := bstep (se 1 (by rfl) ⟨1246148, by rfl⟩ : syracuseStep 1661531 = 2492297) B2492297
theorem B62339701 : Blo 1661530 62339701 := bstep (se 5 (by rfl) ⟨2922173, by rfl⟩ : syracuseStep 62339701 = 5844347) B5844347
theorem B4864655 : Blo 1661530 4864655 := bstep (se 1 (by rfl) ⟨3648491, by rfl⟩ : syracuseStep 4864655 = 7296983) B7296983
theorem B1661599 : Blo 1661530 1661599 := bstep (se 1 (by rfl) ⟨1246199, by rfl⟩ : syracuseStep 1661599 = 2492399) B2492399
theorem B5610167 : Blo 1661530 5610167 := bstep (se 1 (by rfl) ⟨4207625, by rfl⟩ : syracuseStep 5610167 = 8415251) B8415251
theorem B1661767 : Blo 1661530 1661767 := bstep (se 1 (by rfl) ⟨1246325, by rfl⟩ : syracuseStep 1661767 = 2492651) B2492651
theorem B1661807 : Blo 1661530 1661807 := bstep (se 1 (by rfl) ⟨1246355, by rfl⟩ : syracuseStep 1661807 = 2492711) B2492711
theorem B1661863 : Blo 1661530 1661863 := bstep (se 1 (by rfl) ⟨1246397, by rfl⟩ : syracuseStep 1661863 = 2492795) B2492795
theorem B7584749 : Blo 1661530 7584749 := bstep (se 3 (by rfl) ⟨1422140, by rfl⟩ : syracuseStep 7584749 = 2844281) B2844281
theorem B2276443 : Blo 1661530 2276443 := bstep (se 1 (by rfl) ⟨1707332, by rfl⟩ : syracuseStep 2276443 = 3414665) B3414665
theorem B1662043 : Blo 1661530 1662043 := bstep (se 1 (by rfl) ⟨1246532, by rfl⟩ : syracuseStep 1662043 = 2493065) B2493065
theorem B1662159 : Blo 1661530 1662159 := bstep (se 1 (by rfl) ⟨1246619, by rfl⟩ : syracuseStep 1662159 = 2493239) B2493239
theorem B1662183 : Blo 1661530 1662183 := bstep (se 1 (by rfl) ⟨1246637, by rfl⟩ : syracuseStep 1662183 = 2493275) B2493275
theorem B1662279 : Blo 1661530 1662279 := bstep (se 1 (by rfl) ⟨1246709, by rfl⟩ : syracuseStep 1662279 = 2493419) B2493419
theorem B8412497 : Blo 1661530 8412497 := bstep (se 2 (by rfl) ⟨3154686, by rfl⟩ : syracuseStep 8412497 = 6309373) B6309373
theorem B5324201 : Blo 1661530 5324201 := bstep (se 2 (by rfl) ⟨1996575, by rfl⟩ : syracuseStep 5324201 = 3993151) B3993151
theorem B1662415 : Blo 1661530 1662415 := bstep (se 1 (by rfl) ⟨1246811, by rfl⟩ : syracuseStep 1662415 = 2493623) B2493623
theorem B15973985 : Blo 1661530 15973985 := bstep (se 2 (by rfl) ⟨5990244, by rfl⟩ : syracuseStep 15973985 = 11980489) B11980489
theorem B4734571 : Blo 1661530 4734571 := bstep (se 1 (by rfl) ⟨3550928, by rfl⟩ : syracuseStep 4734571 = 7101857) B7101857
theorem B1662575 : Blo 1661530 1662575 := bstep (se 1 (by rfl) ⟨1246931, by rfl⟩ : syracuseStep 1662575 = 2493863) B2493863
theorem B1662631 : Blo 1661530 1662631 := bstep (se 1 (by rfl) ⟨1246973, by rfl⟩ : syracuseStep 1662631 = 2493947) B2493947
theorem B1662695 : Blo 1661530 1662695 := bstep (se 1 (by rfl) ⟨1247021, by rfl⟩ : syracuseStep 1662695 = 2494043) B2494043
theorem B1662751 : Blo 1661530 1662751 := bstep (se 1 (by rfl) ⟨1247063, by rfl⟩ : syracuseStep 1662751 = 2494127) B2494127
theorem B1662831 : Blo 1661530 1662831 := bstep (se 1 (by rfl) ⟨1247123, by rfl⟩ : syracuseStep 1662831 = 2494247) B2494247
theorem B1662887 : Blo 1661530 1662887 := bstep (se 1 (by rfl) ⟨1247165, by rfl⟩ : syracuseStep 1662887 = 2494331) B2494331
theorem B7987187 : Blo 1661530 7987187 := bstep (se 1 (by rfl) ⟨5990390, by rfl⟩ : syracuseStep 7987187 = 11980781) B11980781
theorem B143843363 : Blo 1661530 143843363 := bstep (se 1 (by rfl) ⟨107882522, by rfl⟩ : syracuseStep 143843363 = 215765045) B215765045
theorem B8323111 : Blo 1661530 8323111 := bstep (se 1 (by rfl) ⟨6242333, by rfl⟩ : syracuseStep 8323111 = 12484667) B12484667
theorem B5325227 : Blo 1661530 5325227 := bstep (se 1 (by rfl) ⟨3993920, by rfl⟩ : syracuseStep 5325227 = 7987841) B7987841
theorem B21594593 : Blo 1661530 21594593 := bstep (se 2 (by rfl) ⟨8097972, by rfl⟩ : syracuseStep 21594593 = 16195945) B16195945
theorem B12141029 : Blo 1661530 12141029 := bstep (se 4 (by rfl) ⟨1138221, by rfl⟩ : syracuseStep 12141029 = 2276443) B2276443
theorem B3155051 : Blo 1661530 3155051 := bstep (se 1 (by rfl) ⟨2366288, by rfl⟩ : syracuseStep 3155051 = 4732577) B4732577
theorem B107865917 : Blo 1661530 107865917 := bstep (se 3 (by rfl) ⟨20224859, by rfl⟩ : syracuseStep 107865917 = 40449719) B40449719
theorem B2492315 : Blo 1661530 2492315 := bstep (se 1 (by rfl) ⟨1869236, by rfl⟩ : syracuseStep 2492315 = 3738473) B3738473
theorem B2492351 : Blo 1661530 2492351 := bstep (se 1 (by rfl) ⟨1869263, by rfl⟩ : syracuseStep 2492351 = 3738527) B3738527
theorem B5056499 : Blo 1661530 5056499 := bstep (se 1 (by rfl) ⟨3792374, by rfl⟩ : syracuseStep 5056499 = 7584749) B7584749
theorem B38398049 : Blo 1661530 38398049 := bstep (se 2 (by rfl) ⟨14399268, by rfl⟩ : syracuseStep 38398049 = 28798537) B28798537
theorem B3549467 : Blo 1661530 3549467 := bstep (se 1 (by rfl) ⟨2662100, by rfl⟩ : syracuseStep 3549467 = 5324201) B5324201
theorem B23955851 : Blo 1661530 23955851 := bstep (se 1 (by rfl) ⟨17966888, by rfl⟩ : syracuseStep 23955851 = 35933777) B35933777
theorem B10652093 : Blo 1661530 10652093 := bstep (se 3 (by rfl) ⟨1997267, by rfl⟩ : syracuseStep 10652093 = 3994535) B3994535
theorem B2492975 : Blo 1661530 2492975 := bstep (se 1 (by rfl) ⟨1869731, by rfl⟩ : syracuseStep 2492975 = 3739463) B3739463
theorem B55380581 : Blo 1661530 55380581 := bstep (se 4 (by rfl) ⟨5191929, by rfl⟩ : syracuseStep 55380581 = 10383859) B10383859
theorem B32393843 : Blo 1661530 32393843 := bstep (se 1 (by rfl) ⟨24295382, by rfl⟩ : syracuseStep 32393843 = 48590765) B48590765
theorem B2493095 : Blo 1661530 2493095 := bstep (se 1 (by rfl) ⟨1869821, by rfl⟩ : syracuseStep 2493095 = 3739643) B3739643
theorem B6310619 : Blo 1661530 6310619 := bstep (se 1 (by rfl) ⟨4732964, by rfl⟩ : syracuseStep 6310619 = 9465929) B9465929
theorem B2493161 : Blo 1661530 2493161 := bstep (se 2 (by rfl) ⟨934935, by rfl⟩ : syracuseStep 2493161 = 1869871) B1869871
theorem B2493167 : Blo 1661530 2493167 := bstep (se 1 (by rfl) ⟨1869875, by rfl⟩ : syracuseStep 2493167 = 3739751) B3739751
theorem B2493215 : Blo 1661530 2493215 := bstep (se 1 (by rfl) ⟨1869911, by rfl⟩ : syracuseStep 2493215 = 3739823) B3739823
theorem B2493545 : Blo 1661530 2493545 := bstep (se 2 (by rfl) ⟨935079, by rfl⟩ : syracuseStep 2493545 = 1870159) B1870159
theorem B8416385 : Blo 1661530 8416385 := bstep (se 2 (by rfl) ⟨3156144, by rfl⟩ : syracuseStep 8416385 = 6312289) B6312289
theorem B47918263 : Blo 1661530 47918263 := bstep (se 1 (by rfl) ⟨35938697, by rfl⟩ : syracuseStep 47918263 = 71877395) B71877395
theorem B2493671 : Blo 1661530 2493671 := bstep (se 1 (by rfl) ⟨1870253, by rfl⟩ : syracuseStep 2493671 = 3740507) B3740507
theorem B4205915 : Blo 1661530 4205915 := bstep (se 1 (by rfl) ⟨3154436, by rfl⟩ : syracuseStep 4205915 = 6308873) B6308873
theorem B4205945 : Blo 1661530 4205945 := bstep (se 2 (by rfl) ⟨1577229, by rfl⟩ : syracuseStep 4205945 = 3154459) B3154459
theorem B3739103 : Blo 1661530 3739103 := bstep (se 1 (by rfl) ⟨2804327, by rfl⟩ : syracuseStep 3739103 = 5608655) B5608655
theorem B83119601 : Blo 1661530 83119601 := bstep (se 2 (by rfl) ⟨31169850, by rfl⟩ : syracuseStep 83119601 = 62339701) B62339701
theorem B2494175 : Blo 1661530 2494175 := bstep (se 1 (by rfl) ⟨1870631, by rfl⟩ : syracuseStep 2494175 = 3741263) B3741263
theorem B15970067 : Blo 1661530 15970067 := bstep (se 1 (by rfl) ⟨11977550, by rfl⟩ : syracuseStep 15970067 = 23955101) B23955101
theorem B2805583 : Blo 1661530 2805583 := bstep (se 1 (by rfl) ⟨2104187, by rfl⟩ : syracuseStep 2805583 = 4208375) B4208375
theorem B6311803 : Blo 1661530 6311803 := bstep (se 1 (by rfl) ⟨4733852, by rfl⟩ : syracuseStep 6311803 = 9467705) B9467705
theorem B2494457 : Blo 1661530 2494457 := bstep (se 2 (by rfl) ⟨935421, by rfl⟩ : syracuseStep 2494457 = 1870843) B1870843
theorem B2805887 : Blo 1661530 2805887 := bstep (se 1 (by rfl) ⟨2104415, by rfl⟩ : syracuseStep 2805887 = 4208831) B4208831
theorem B25948345 : Blo 1661530 25948345 := bstep (se 2 (by rfl) ⟨9730629, by rfl⟩ : syracuseStep 25948345 = 19461259) B19461259
theorem B3371387 : Blo 1661530 3371387 := bstep (se 1 (by rfl) ⟨2528540, by rfl⟩ : syracuseStep 3371387 = 5057081) B5057081
theorem B12972413 : Blo 1661530 12972413 := bstep (se 3 (by rfl) ⟨2432327, by rfl⟩ : syracuseStep 12972413 = 4864655) B4864655
theorem B3740111 : Blo 1661530 3740111 := bstep (se 1 (by rfl) ⟨2805083, by rfl⟩ : syracuseStep 3740111 = 5610167) B5610167
theorem B18936503 : Blo 1661530 18936503 := bstep (se 1 (by rfl) ⟨14202377, by rfl⟩ : syracuseStep 18936503 = 28404755) B28404755
theorem B6312761 : Blo 1661530 6312761 := bstep (se 2 (by rfl) ⟨2367285, by rfl⟩ : syracuseStep 6312761 = 4734571) B4734571
theorem B5608331 : Blo 1661530 5608331 := bstep (se 1 (by rfl) ⟨4206248, by rfl⟩ : syracuseStep 5608331 = 8412497) B8412497
theorem B6394781 : Blo 1661530 6394781 := bstep (se 3 (by rfl) ⟨1199021, by rfl⟩ : syracuseStep 6394781 = 2398043) B2398043
theorem B4731929 : Blo 1661530 4731929 := bstep (se 2 (by rfl) ⟨1774473, by rfl⟩ : syracuseStep 4731929 = 3548947) B3548947
theorem B25294115 : Blo 1661530 25294115 := bstep (se 1 (by rfl) ⟨18970586, by rfl⟩ : syracuseStep 25294115 = 37941173) B37941173
theorem B5608871 : Blo 1661530 5608871 := bstep (se 1 (by rfl) ⟨4206653, by rfl⟩ : syracuseStep 5608871 = 8413307) B8413307
theorem B4494847 : Blo 1661530 4494847 := bstep (se 1 (by rfl) ⟨3371135, by rfl⟩ : syracuseStep 4494847 = 6742271) B6742271
theorem B17061779 : Blo 1661530 17061779 := bstep (se 1 (by rfl) ⟨12796334, by rfl⟩ : syracuseStep 17061779 = 25592669) B25592669
theorem B6314233 : Blo 1661530 6314233 := bstep (se 2 (by rfl) ⟨2367837, by rfl⟩ : syracuseStep 6314233 = 4735675) B4735675
theorem B5609897 : Blo 1661530 5609897 := bstep (se 2 (by rfl) ⟨2103711, by rfl⟩ : syracuseStep 5609897 = 4207423) B4207423
theorem B5323279 : Blo 1661530 5323279 := bstep (se 1 (by rfl) ⟨3992459, by rfl⟩ : syracuseStep 5323279 = 7984919) B7984919
theorem B1661631 : Blo 1661530 1661631 := bstep (se 1 (by rfl) ⟨1246223, by rfl⟩ : syracuseStep 1661631 = 2492447) B2492447
theorem B28400381 : Blo 1661530 28400381 := bstep (se 3 (by rfl) ⟨5325071, by rfl⟩ : syracuseStep 28400381 = 10650143) B10650143
theorem B13146937 : Blo 1661530 13146937 := bstep (se 2 (by rfl) ⟨4930101, by rfl⟩ : syracuseStep 13146937 = 9860203) B9860203
theorem B1661759 : Blo 1661530 1661759 := bstep (se 1 (by rfl) ⟨1246319, by rfl⟩ : syracuseStep 1661759 = 2492639) B2492639
theorem B15170399 : Blo 1661530 15170399 := bstep (se 1 (by rfl) ⟨11377799, by rfl⟩ : syracuseStep 15170399 = 22755599) B22755599
theorem B1661799 : Blo 1661530 1661799 := bstep (se 1 (by rfl) ⟨1246349, by rfl⟩ : syracuseStep 1661799 = 2492699) B2492699
theorem B2366329 : Blo 1661530 2366329 := bstep (se 2 (by rfl) ⟨887373, by rfl⟩ : syracuseStep 2366329 = 1774747) B1774747
theorem B2104375 : Blo 1661530 2104375 := bstep (se 1 (by rfl) ⟨1578281, by rfl⟩ : syracuseStep 2104375 = 3156563) B3156563
theorem B1662015 : Blo 1661530 1662015 := bstep (se 1 (by rfl) ⟨1246511, by rfl⟩ : syracuseStep 1662015 = 2493023) B2493023
theorem B1662203 : Blo 1661530 1662203 := bstep (se 1 (by rfl) ⟨1246652, by rfl⟩ : syracuseStep 1662203 = 2493305) B2493305
theorem B1662235 : Blo 1661530 1662235 := bstep (se 1 (by rfl) ⟨1246676, by rfl⟩ : syracuseStep 1662235 = 2493353) B2493353
theorem B1662335 : Blo 1661530 1662335 := bstep (se 1 (by rfl) ⟨1246751, by rfl⟩ : syracuseStep 1662335 = 2493503) B2493503
theorem B7102009 : Blo 1661530 7102009 := bstep (se 2 (by rfl) ⟨2663253, by rfl⟩ : syracuseStep 7102009 = 5326507) B5326507
theorem B10649323 : Blo 1661530 10649323 := bstep (se 1 (by rfl) ⟨7986992, by rfl⟩ : syracuseStep 10649323 = 15973985) B15973985
theorem B1662703 : Blo 1661530 1662703 := bstep (se 1 (by rfl) ⟨1247027, by rfl⟩ : syracuseStep 1662703 = 2494055) B2494055
theorem B12623849 : Blo 1661530 12623849 := bstep (se 2 (by rfl) ⟨4733943, by rfl⟩ : syracuseStep 12623849 = 9467887) B9467887
theorem B1662959 : Blo 1661530 1662959 := bstep (se 1 (by rfl) ⟨1247219, by rfl⟩ : syracuseStep 1662959 = 2494439) B2494439
theorem B5324791 : Blo 1661530 5324791 := bstep (se 1 (by rfl) ⟨3993593, by rfl⟩ : syracuseStep 5324791 = 7987187) B7987187
theorem B95895575 : Blo 1661530 95895575 := bstep (se 1 (by rfl) ⟨71921681, by rfl⟩ : syracuseStep 95895575 = 143843363) B143843363
theorem B8413469 : Blo 1661530 8413469 := bstep (se 3 (by rfl) ⟨1577525, by rfl⟩ : syracuseStep 8413469 = 3155051) B3155051
theorem B8094019 : Blo 1661530 8094019 := bstep (se 1 (by rfl) ⟨6070514, by rfl⟩ : syracuseStep 8094019 = 12141029) B12141029
theorem B12624335 : Blo 1661530 12624335 := bstep (se 1 (by rfl) ⟨9468251, by rfl⟩ : syracuseStep 12624335 = 18936503) B18936503
theorem B3154619 : Blo 1661530 3154619 := bstep (se 1 (by rfl) ⟨2365964, by rfl⟩ : syracuseStep 3154619 = 4731929) B4731929
theorem B3155105 : Blo 1661530 3155105 := bstep (se 2 (by rfl) ⟨1183164, by rfl⟩ : syracuseStep 3155105 = 2366329) B2366329
theorem B71910611 : Blo 1661530 71910611 := bstep (se 1 (by rfl) ⟨53932958, by rfl⟩ : syracuseStep 71910611 = 107865917) B107865917
theorem B63891017 : Blo 1661530 63891017 := bstep (se 2 (by rfl) ⟨23959131, by rfl⟩ : syracuseStep 63891017 = 47918263) B47918263
theorem B70116997 : Blo 1661530 70116997 := bstep (se 4 (by rfl) ⟨6573468, by rfl⟩ : syracuseStep 70116997 = 13146937) B13146937
theorem B21595895 : Blo 1661530 21595895 := bstep (se 1 (by rfl) ⟨16196921, by rfl⟩ : syracuseStep 21595895 = 32393843) B32393843
theorem B18933587 : Blo 1661530 18933587 := bstep (se 1 (by rfl) ⟨14200190, by rfl⟩ : syracuseStep 18933587 = 28400381) B28400381
theorem B2803943 : Blo 1661530 2803943 := bstep (se 1 (by rfl) ⟨2102957, by rfl⟩ : syracuseStep 2803943 = 4205915) B4205915
theorem B2803963 : Blo 1661530 2803963 := bstep (se 1 (by rfl) ⟨2102972, by rfl⟩ : syracuseStep 2803963 = 4205945) B4205945
theorem B14199097 : Blo 1661530 14199097 := bstep (se 2 (by rfl) ⟨5324661, by rfl⟩ : syracuseStep 14199097 = 10649323) B10649323
theorem B2492735 : Blo 1661530 2492735 := bstep (se 1 (by rfl) ⟨1869551, by rfl⟩ : syracuseStep 2492735 = 3739103) B3739103
theorem B55413067 : Blo 1661530 55413067 := bstep (se 1 (by rfl) ⟨41559800, by rfl⟩ : syracuseStep 55413067 = 83119601) B83119601
theorem B8415737 : Blo 1661530 8415737 := bstep (se 2 (by rfl) ⟨3155901, by rfl⟩ : syracuseStep 8415737 = 6311803) B6311803
theorem B8415899 : Blo 1661530 8415899 := bstep (se 1 (by rfl) ⟨6311924, by rfl⟩ : syracuseStep 8415899 = 12623849) B12623849
theorem B1870591 : Blo 1661530 1870591 := bstep (se 1 (by rfl) ⟨1402943, by rfl⟩ : syracuseStep 1870591 = 2805887) B2805887
theorem B34597793 : Blo 1661530 34597793 := bstep (se 2 (by rfl) ⟨12974172, by rfl⟩ : syracuseStep 34597793 = 25948345) B25948345
theorem B3550151 : Blo 1661530 3550151 := bstep (se 1 (by rfl) ⟨2662613, by rfl⟩ : syracuseStep 3550151 = 5325227) B5325227
theorem B2493407 : Blo 1661530 2493407 := bstep (se 1 (by rfl) ⟨1870055, by rfl⟩ : syracuseStep 2493407 = 3740111) B3740111
theorem B14396395 : Blo 1661530 14396395 := bstep (se 1 (by rfl) ⟨10797296, by rfl⟩ : syracuseStep 14396395 = 21594593) B21594593
theorem B3738887 : Blo 1661530 3738887 := bstep (se 1 (by rfl) ⟨2804165, by rfl⟩ : syracuseStep 3738887 = 5608331) B5608331
theorem B4263187 : Blo 1661530 4263187 := bstep (se 1 (by rfl) ⟨3197390, by rfl⟩ : syracuseStep 4263187 = 6394781) B6394781
theorem B7097705 : Blo 1661530 7097705 := bstep (se 2 (by rfl) ⟨2661639, by rfl⟩ : syracuseStep 7097705 = 5323279) B5323279
theorem B9465245 : Blo 1661530 9465245 := bstep (se 3 (by rfl) ⟨1774733, by rfl⟩ : syracuseStep 9465245 = 3549467) B3549467
theorem B16862743 : Blo 1661530 16862743 := bstep (se 1 (by rfl) ⟨12647057, by rfl⟩ : syracuseStep 16862743 = 25294115) B25294115
theorem B3739247 : Blo 1661530 3739247 := bstep (se 1 (by rfl) ⟨2804435, by rfl⟩ : syracuseStep 3739247 = 5608871) B5608871
theorem B8990365 : Blo 1661530 8990365 := bstep (se 3 (by rfl) ⟨1685693, by rfl⟩ : syracuseStep 8990365 = 3371387) B3371387
theorem B11374519 : Blo 1661530 11374519 := bstep (se 1 (by rfl) ⟨8530889, by rfl⟩ : syracuseStep 11374519 = 17061779) B17061779
theorem B3370999 : Blo 1661530 3370999 := bstep (se 1 (by rfl) ⟨2528249, by rfl⟩ : syracuseStep 3370999 = 5056499) B5056499
theorem B2805833 : Blo 1661530 2805833 := bstep (se 2 (by rfl) ⟨1052187, by rfl⟩ : syracuseStep 2805833 = 2104375) B2104375
theorem B15970567 : Blo 1661530 15970567 := bstep (se 1 (by rfl) ⟨11977925, by rfl⟩ : syracuseStep 15970567 = 23955851) B23955851
theorem B3739931 : Blo 1661530 3739931 := bstep (se 1 (by rfl) ⟨2804948, by rfl⟩ : syracuseStep 3739931 = 5609897) B5609897
theorem B4207079 : Blo 1661530 4207079 := bstep (se 1 (by rfl) ⟨3155309, by rfl⟩ : syracuseStep 4207079 = 6310619) B6310619
theorem B10113599 : Blo 1661530 10113599 := bstep (se 1 (by rfl) ⟨7585199, by rfl⟩ : syracuseStep 10113599 = 15170399) B15170399
theorem B5993129 : Blo 1661530 5993129 := bstep (se 2 (by rfl) ⟨2247423, by rfl⟩ : syracuseStep 5993129 = 4494847) B4494847
theorem B3740777 : Blo 1661530 3740777 := bstep (se 2 (by rfl) ⟨1402791, by rfl⟩ : syracuseStep 3740777 = 2805583) B2805583
theorem B10646711 : Blo 1661530 10646711 := bstep (se 1 (by rfl) ⟨7985033, by rfl⟩ : syracuseStep 10646711 = 15970067) B15970067
theorem B7099721 : Blo 1661530 7099721 := bstep (se 2 (by rfl) ⟨2662395, by rfl⟩ : syracuseStep 7099721 = 5324791) B5324791
theorem B11097481 : Blo 1661530 11097481 := bstep (se 2 (by rfl) ⟨4161555, by rfl⟩ : syracuseStep 11097481 = 8323111) B8323111
theorem B8418977 : Blo 1661530 8418977 := bstep (se 2 (by rfl) ⟨3157116, by rfl⟩ : syracuseStep 8418977 = 6314233) B6314233
theorem B4208507 : Blo 1661530 4208507 := bstep (se 1 (by rfl) ⟨3156380, by rfl⟩ : syracuseStep 4208507 = 6312761) B6312761
theorem B34593101 : Blo 1661530 34593101 := bstep (se 3 (by rfl) ⟨6486206, by rfl⟩ : syracuseStep 34593101 = 12972413) B12972413
theorem B1661543 : Blo 1661530 1661543 := bstep (se 1 (by rfl) ⟨1246157, by rfl⟩ : syracuseStep 1661543 = 2492315) B2492315
theorem B1661567 : Blo 1661530 1661567 := bstep (se 1 (by rfl) ⟨1246175, by rfl⟩ : syracuseStep 1661567 = 2492351) B2492351
theorem B25598699 : Blo 1661530 25598699 := bstep (se 1 (by rfl) ⟨19199024, by rfl⟩ : syracuseStep 25598699 = 38398049) B38398049
theorem B7101395 : Blo 1661530 7101395 := bstep (se 1 (by rfl) ⟨5326046, by rfl⟩ : syracuseStep 7101395 = 10652093) B10652093
theorem B1661983 : Blo 1661530 1661983 := bstep (se 1 (by rfl) ⟨1246487, by rfl⟩ : syracuseStep 1661983 = 2492975) B2492975
theorem B36920387 : Blo 1661530 36920387 := bstep (se 1 (by rfl) ⟨27690290, by rfl⟩ : syracuseStep 36920387 = 55380581) B55380581
theorem B1662063 : Blo 1661530 1662063 := bstep (se 1 (by rfl) ⟨1246547, by rfl⟩ : syracuseStep 1662063 = 2493095) B2493095
theorem B1662107 : Blo 1661530 1662107 := bstep (se 1 (by rfl) ⟨1246580, by rfl⟩ : syracuseStep 1662107 = 2493161) B2493161
theorem B1662111 : Blo 1661530 1662111 := bstep (se 1 (by rfl) ⟨1246583, by rfl⟩ : syracuseStep 1662111 = 2493167) B2493167
theorem B1662143 : Blo 1661530 1662143 := bstep (se 1 (by rfl) ⟨1246607, by rfl⟩ : syracuseStep 1662143 = 2493215) B2493215
theorem B1662363 : Blo 1661530 1662363 := bstep (se 1 (by rfl) ⟨1246772, by rfl⟩ : syracuseStep 1662363 = 2493545) B2493545
theorem B9469345 : Blo 1661530 9469345 := bstep (se 2 (by rfl) ⟨3551004, by rfl⟩ : syracuseStep 9469345 = 7102009) B7102009
theorem B5610923 : Blo 1661530 5610923 := bstep (se 1 (by rfl) ⟨4208192, by rfl⟩ : syracuseStep 5610923 = 8416385) B8416385
theorem B1662447 : Blo 1661530 1662447 := bstep (se 1 (by rfl) ⟨1246835, by rfl⟩ : syracuseStep 1662447 = 2493671) B2493671
theorem B1662783 : Blo 1661530 1662783 := bstep (se 1 (by rfl) ⟨1247087, by rfl⟩ : syracuseStep 1662783 = 2494175) B2494175
theorem B1662971 : Blo 1661530 1662971 := bstep (se 1 (by rfl) ⟨1247228, by rfl⟩ : syracuseStep 1662971 = 2494457) B2494457
theorem B63930383 : Blo 1661530 63930383 := bstep (se 1 (by rfl) ⟨47947787, by rfl⟩ : syracuseStep 63930383 = 95895575) B95895575
theorem B18932129 : Blo 1661530 18932129 := bstep (se 2 (by rfl) ⟨7099548, by rfl⟩ : syracuseStep 18932129 = 14199097) B14199097
theorem B73884089 : Blo 1661530 73884089 := bstep (se 2 (by rfl) ⟨27706533, by rfl⟩ : syracuseStep 73884089 = 55413067) B55413067
theorem B47940407 : Blo 1661530 47940407 := bstep (se 1 (by rfl) ⟨35955305, by rfl⟩ : syracuseStep 47940407 = 71910611) B71910611
theorem B5612651 : Blo 1661530 5612651 := bstep (se 1 (by rfl) ⟨4209488, by rfl⟩ : syracuseStep 5612651 = 8418977) B8418977
theorem B19195193 : Blo 1661530 19195193 := bstep (se 2 (by rfl) ⟨7198197, by rfl⟩ : syracuseStep 19195193 = 14396395) B14396395
theorem B1869295 : Blo 1661530 1869295 := bstep (se 1 (by rfl) ⟨1401971, by rfl⟩ : syracuseStep 1869295 = 2803943) B2803943
theorem B26969597 : Blo 1661530 26969597 := bstep (se 3 (by rfl) ⟨5056799, by rfl⟩ : syracuseStep 26969597 = 10113599) B10113599
theorem B23062067 : Blo 1661530 23062067 := bstep (se 1 (by rfl) ⟨17296550, by rfl⟩ : syracuseStep 23062067 = 34593101) B34593101
theorem B17065799 : Blo 1661530 17065799 := bstep (se 1 (by rfl) ⟨12799349, by rfl⟩ : syracuseStep 17065799 = 25598699) B25598699
theorem B14796641 : Blo 1661530 14796641 := bstep (se 2 (by rfl) ⟨5548740, by rfl⟩ : syracuseStep 14796641 = 11097481) B11097481
theorem B12625793 : Blo 1661530 12625793 := bstep (se 2 (by rfl) ⟨4734672, by rfl⟩ : syracuseStep 12625793 = 9469345) B9469345
theorem B2492591 : Blo 1661530 2492591 := bstep (se 1 (by rfl) ⟨1869443, by rfl⟩ : syracuseStep 2492591 = 3738887) B3738887
theorem B93489329 : Blo 1661530 93489329 := bstep (se 2 (by rfl) ⟨35058498, by rfl⟩ : syracuseStep 93489329 = 70116997) B70116997
theorem B11987153 : Blo 1661530 11987153 := bstep (se 2 (by rfl) ⟨4495182, by rfl⟩ : syracuseStep 11987153 = 8990365) B8990365
theorem B6310163 : Blo 1661530 6310163 := bstep (se 1 (by rfl) ⟨4732622, by rfl⟩ : syracuseStep 6310163 = 9465245) B9465245
theorem B2492831 : Blo 1661530 2492831 := bstep (se 1 (by rfl) ⟨1869623, by rfl⟩ : syracuseStep 2492831 = 3739247) B3739247
theorem B15166025 : Blo 1661530 15166025 := bstep (se 2 (by rfl) ⟨5687259, by rfl⟩ : syracuseStep 15166025 = 11374519) B11374519
theorem B1870555 : Blo 1661530 1870555 := bstep (se 1 (by rfl) ⟨1402916, by rfl⟩ : syracuseStep 1870555 = 2805833) B2805833
theorem B2493287 : Blo 1661530 2493287 := bstep (se 1 (by rfl) ⟨1869965, by rfl⟩ : syracuseStep 2493287 = 3739931) B3739931
theorem B8416223 : Blo 1661530 8416223 := bstep (se 1 (by rfl) ⟨6312167, by rfl⟩ : syracuseStep 8416223 = 12624335) B12624335
theorem B2804719 : Blo 1661530 2804719 := bstep (se 1 (by rfl) ⟨2103539, by rfl⟩ : syracuseStep 2804719 = 4207079) B4207079
theorem B3738617 : Blo 1661530 3738617 := bstep (se 2 (by rfl) ⟨1401981, by rfl⟩ : syracuseStep 3738617 = 2803963) B2803963
theorem B21294089 : Blo 1661530 21294089 := bstep (se 2 (by rfl) ⟨7985283, by rfl⟩ : syracuseStep 21294089 = 15970567) B15970567
theorem B10792025 : Blo 1661530 10792025 := bstep (se 2 (by rfl) ⟨4047009, by rfl⟩ : syracuseStep 10792025 = 8094019) B8094019
theorem B2493851 : Blo 1661530 2493851 := bstep (se 1 (by rfl) ⟨1870388, by rfl⟩ : syracuseStep 2493851 = 3740777) B3740777
theorem B7097807 : Blo 1661530 7097807 := bstep (se 1 (by rfl) ⟨5323355, by rfl⟩ : syracuseStep 7097807 = 10646711) B10646711
theorem B2494121 : Blo 1661530 2494121 := bstep (se 2 (by rfl) ⟨935295, by rfl⟩ : syracuseStep 2494121 = 1870591) B1870591
theorem B42594011 : Blo 1661530 42594011 := bstep (se 1 (by rfl) ⟨31945508, by rfl⟩ : syracuseStep 42594011 = 63891017) B63891017
theorem B14397263 : Blo 1661530 14397263 := bstep (se 1 (by rfl) ⟨10797947, by rfl⟩ : syracuseStep 14397263 = 21595895) B21595895
theorem B2805671 : Blo 1661530 2805671 := bstep (se 1 (by rfl) ⟨2104253, by rfl⟩ : syracuseStep 2805671 = 4208507) B4208507
theorem B23065195 : Blo 1661530 23065195 := bstep (se 1 (by rfl) ⟨17298896, by rfl⟩ : syracuseStep 23065195 = 34597793) B34597793
theorem B22483657 : Blo 1661530 22483657 := bstep (se 2 (by rfl) ⟨8431371, by rfl⟩ : syracuseStep 22483657 = 16862743) B16862743
theorem B24613591 : Blo 1661530 24613591 := bstep (se 1 (by rfl) ⟨18460193, by rfl⟩ : syracuseStep 24613591 = 36920387) B36920387
theorem B4731803 : Blo 1661530 4731803 := bstep (se 1 (by rfl) ⟨3548852, by rfl⟩ : syracuseStep 4731803 = 7097705) B7097705
theorem B3740615 : Blo 1661530 3740615 := bstep (se 1 (by rfl) ⟨2805461, by rfl⟩ : syracuseStep 3740615 = 5610923) B5610923
theorem B4494665 : Blo 1661530 4494665 := bstep (se 2 (by rfl) ⟨1685499, by rfl⟩ : syracuseStep 4494665 = 3370999) B3370999
theorem B5608979 : Blo 1661530 5608979 := bstep (se 1 (by rfl) ⟨4206734, by rfl⟩ : syracuseStep 5608979 = 8413469) B8413469
theorem B3995419 : Blo 1661530 3995419 := bstep (se 1 (by rfl) ⟨2996564, by rfl⟩ : syracuseStep 3995419 = 5993129) B5993129
theorem B2103079 : Blo 1661530 2103079 := bstep (se 1 (by rfl) ⟨1577309, by rfl⟩ : syracuseStep 2103079 = 3154619) B3154619
theorem B2103403 : Blo 1661530 2103403 := bstep (se 1 (by rfl) ⟨1577552, by rfl⟩ : syracuseStep 2103403 = 3155105) B3155105
theorem B4733147 : Blo 1661530 4733147 := bstep (se 1 (by rfl) ⟨3549860, by rfl⟩ : syracuseStep 4733147 = 7099721) B7099721
theorem B12622391 : Blo 1661530 12622391 := bstep (se 1 (by rfl) ⟨9466793, by rfl⟩ : syracuseStep 12622391 = 18933587) B18933587
theorem B1661823 : Blo 1661530 1661823 := bstep (se 1 (by rfl) ⟨1246367, by rfl⟩ : syracuseStep 1661823 = 2492735) B2492735
theorem B5610491 : Blo 1661530 5610491 := bstep (se 1 (by rfl) ⟨4207868, by rfl⟩ : syracuseStep 5610491 = 8415737) B8415737
theorem B5684249 : Blo 1661530 5684249 := bstep (se 2 (by rfl) ⟨2131593, by rfl⟩ : syracuseStep 5684249 = 4263187) B4263187
theorem B5610599 : Blo 1661530 5610599 := bstep (se 1 (by rfl) ⟨4207949, by rfl⟩ : syracuseStep 5610599 = 8415899) B8415899
theorem B2366767 : Blo 1661530 2366767 := bstep (se 1 (by rfl) ⟨1775075, by rfl⟩ : syracuseStep 2366767 = 3550151) B3550151
theorem B4734263 : Blo 1661530 4734263 := bstep (se 1 (by rfl) ⟨3550697, by rfl⟩ : syracuseStep 4734263 = 7101395) B7101395
theorem B1662271 : Blo 1661530 1662271 := bstep (se 1 (by rfl) ⟨1246703, by rfl⟩ : syracuseStep 1662271 = 2493407) B2493407
theorem B3154535 : Blo 1661530 3154535 := bstep (se 1 (by rfl) ⟨2365901, by rfl⟩ : syracuseStep 3154535 = 4731803) B4731803
theorem B30753593 : Blo 1661530 30753593 := bstep (se 2 (by rfl) ⟨11532597, by rfl⟩ : syracuseStep 30753593 = 23065195) B23065195
theorem B12796795 : Blo 1661530 12796795 := bstep (se 1 (by rfl) ⟨9597596, by rfl⟩ : syracuseStep 12796795 = 19195193) B19195193
theorem B32818121 : Blo 1661530 32818121 := bstep (se 2 (by rfl) ⟨12306795, by rfl⟩ : syracuseStep 32818121 = 24613591) B24613591
theorem B9864427 : Blo 1661530 9864427 := bstep (se 1 (by rfl) ⟨7398320, by rfl⟩ : syracuseStep 9864427 = 14796641) B14796641
theorem B62326219 : Blo 1661530 62326219 := bstep (se 1 (by rfl) ⟨46744664, by rfl⟩ : syracuseStep 62326219 = 93489329) B93489329
theorem B3155431 : Blo 1661530 3155431 := bstep (se 1 (by rfl) ⟨2366573, by rfl⟩ : syracuseStep 3155431 = 4733147) B4733147
theorem B8414927 : Blo 1661530 8414927 := bstep (se 1 (by rfl) ⟨6311195, by rfl⟩ : syracuseStep 8414927 = 12622391) B12622391
theorem B10110683 : Blo 1661530 10110683 := bstep (se 1 (by rfl) ⟨7583012, by rfl⟩ : syracuseStep 10110683 = 15166025) B15166025
theorem B3155689 : Blo 1661530 3155689 := bstep (se 2 (by rfl) ⟨1183383, by rfl⟩ : syracuseStep 3155689 = 2366767) B2366767
theorem B2492393 : Blo 1661530 2492393 := bstep (se 2 (by rfl) ⟨934647, by rfl⟩ : syracuseStep 2492393 = 1869295) B1869295
theorem B2492411 : Blo 1661530 2492411 := bstep (se 1 (by rfl) ⟨1869308, by rfl⟩ : syracuseStep 2492411 = 3738617) B3738617
theorem B7194683 : Blo 1661530 7194683 := bstep (se 1 (by rfl) ⟨5396012, by rfl⟩ : syracuseStep 7194683 = 10792025) B10792025
theorem B3156175 : Blo 1661530 3156175 := bstep (se 1 (by rfl) ⟨2367131, by rfl⟩ : syracuseStep 3156175 = 4734263) B4734263
theorem B5327225 : Blo 1661530 5327225 := bstep (se 2 (by rfl) ⟨1997709, by rfl⟩ : syracuseStep 5327225 = 3995419) B3995419
theorem B2804105 : Blo 1661530 2804105 := bstep (se 2 (by rfl) ⟨1051539, by rfl⟩ : syracuseStep 2804105 = 2103079) B2103079
theorem B28396007 : Blo 1661530 28396007 := bstep (se 1 (by rfl) ⟨21297005, by rfl⟩ : syracuseStep 28396007 = 42594011) B42594011
theorem B1870447 : Blo 1661530 1870447 := bstep (se 1 (by rfl) ⟨1402835, by rfl⟩ : syracuseStep 1870447 = 2805671) B2805671
theorem B2804537 : Blo 1661530 2804537 := bstep (se 2 (by rfl) ⟨1051701, by rfl⟩ : syracuseStep 2804537 = 2103403) B2103403
theorem B31960271 : Blo 1661530 31960271 := bstep (se 1 (by rfl) ⟨23970203, by rfl⟩ : syracuseStep 31960271 = 47940407) B47940407
theorem B2493743 : Blo 1661530 2493743 := bstep (se 1 (by rfl) ⟨1870307, by rfl⟩ : syracuseStep 2493743 = 3740615) B3740615
theorem B29978209 : Blo 1661530 29978209 := bstep (se 2 (by rfl) ⟨11241828, by rfl⟩ : syracuseStep 29978209 = 22483657) B22483657
theorem B2494073 : Blo 1661530 2494073 := bstep (se 2 (by rfl) ⟨935277, by rfl⟩ : syracuseStep 2494073 = 1870555) B1870555
theorem B3739319 : Blo 1661530 3739319 := bstep (se 1 (by rfl) ⟨2804489, by rfl⟩ : syracuseStep 3739319 = 5608979) B5608979
theorem B8417195 : Blo 1661530 8417195 := bstep (se 1 (by rfl) ⟨6312896, by rfl⟩ : syracuseStep 8417195 = 12625793) B12625793
theorem B3739625 : Blo 1661530 3739625 := bstep (se 2 (by rfl) ⟨1402359, by rfl⟩ : syracuseStep 3739625 = 2804719) B2804719
theorem B7991435 : Blo 1661530 7991435 := bstep (se 1 (by rfl) ⟨5993576, by rfl⟩ : syracuseStep 7991435 = 11987153) B11987153
theorem B4206775 : Blo 1661530 4206775 := bstep (se 1 (by rfl) ⟨3155081, by rfl⟩ : syracuseStep 4206775 = 6310163) B6310163
theorem B3740327 : Blo 1661530 3740327 := bstep (se 1 (by rfl) ⟨2805245, by rfl⟩ : syracuseStep 3740327 = 5610491) B5610491
theorem B3789499 : Blo 1661530 3789499 := bstep (se 1 (by rfl) ⟨2842124, by rfl⟩ : syracuseStep 3789499 = 5684249) B5684249
theorem B3740399 : Blo 1661530 3740399 := bstep (se 1 (by rfl) ⟨2805299, by rfl⟩ : syracuseStep 3740399 = 5610599) B5610599
theorem B4731871 : Blo 1661530 4731871 := bstep (se 1 (by rfl) ⟨3548903, by rfl⟩ : syracuseStep 4731871 = 7097807) B7097807
theorem B9598175 : Blo 1661530 9598175 := bstep (se 1 (by rfl) ⟨7198631, by rfl⟩ : syracuseStep 9598175 = 14397263) B14397263
theorem B42620255 : Blo 1661530 42620255 := bstep (se 1 (by rfl) ⟨31965191, by rfl⟩ : syracuseStep 42620255 = 63930383) B63930383
theorem B12621419 : Blo 1661530 12621419 := bstep (se 1 (by rfl) ⟨9466064, by rfl⟩ : syracuseStep 12621419 = 18932129) B18932129
theorem B49256059 : Blo 1661530 49256059 := bstep (se 1 (by rfl) ⟨36942044, by rfl⟩ : syracuseStep 49256059 = 73884089) B73884089
theorem B3741767 : Blo 1661530 3741767 := bstep (se 1 (by rfl) ⟨2806325, by rfl⟩ : syracuseStep 3741767 = 5612651) B5612651
theorem B2996443 : Blo 1661530 2996443 := bstep (se 1 (by rfl) ⟨2247332, by rfl⟩ : syracuseStep 2996443 = 4494665) B4494665
theorem B17979731 : Blo 1661530 17979731 := bstep (se 1 (by rfl) ⟨13484798, by rfl⟩ : syracuseStep 17979731 = 26969597) B26969597
theorem B15374711 : Blo 1661530 15374711 := bstep (se 1 (by rfl) ⟨11531033, by rfl⟩ : syracuseStep 15374711 = 23062067) B23062067
theorem B11377199 : Blo 1661530 11377199 := bstep (se 1 (by rfl) ⟨8532899, by rfl⟩ : syracuseStep 11377199 = 17065799) B17065799
theorem B1661727 : Blo 1661530 1661727 := bstep (se 1 (by rfl) ⟨1246295, by rfl⟩ : syracuseStep 1661727 = 2492591) B2492591
theorem B1661887 : Blo 1661530 1661887 := bstep (se 1 (by rfl) ⟨1246415, by rfl⟩ : syracuseStep 1661887 = 2492831) B2492831
theorem B1662191 : Blo 1661530 1662191 := bstep (se 1 (by rfl) ⟨1246643, by rfl⟩ : syracuseStep 1662191 = 2493287) B2493287
theorem B5610815 : Blo 1661530 5610815 := bstep (se 1 (by rfl) ⟨4208111, by rfl⟩ : syracuseStep 5610815 = 8416223) B8416223
theorem B14196059 : Blo 1661530 14196059 := bstep (se 1 (by rfl) ⟨10647044, by rfl⟩ : syracuseStep 14196059 = 21294089) B21294089
theorem B1662567 : Blo 1661530 1662567 := bstep (se 1 (by rfl) ⟨1246925, by rfl⟩ : syracuseStep 1662567 = 2493851) B2493851
theorem B1662747 : Blo 1661530 1662747 := bstep (se 1 (by rfl) ⟨1247060, by rfl⟩ : syracuseStep 1662747 = 2494121) B2494121
theorem B6398783 : Blo 1661530 6398783 := bstep (se 1 (by rfl) ⟨4799087, by rfl⟩ : syracuseStep 6398783 = 9598175) B9598175
theorem B8414279 : Blo 1661530 8414279 := bstep (se 1 (by rfl) ⟨6310709, by rfl⟩ : syracuseStep 8414279 = 12621419) B12621419
theorem B6309161 : Blo 1661530 6309161 := bstep (se 2 (by rfl) ⟨2365935, by rfl⟩ : syracuseStep 6309161 = 4731871) B4731871
theorem B11986487 : Blo 1661530 11986487 := bstep (se 1 (by rfl) ⟨8989865, by rfl⟩ : syracuseStep 11986487 = 17979731) B17979731
theorem B1869403 : Blo 1661530 1869403 := bstep (se 1 (by rfl) ⟨1402052, by rfl⟩ : syracuseStep 1869403 = 2804105) B2804105
theorem B1869691 : Blo 1661530 1869691 := bstep (se 1 (by rfl) ⟨1402268, by rfl⟩ : syracuseStep 1869691 = 2804537) B2804537
theorem B83101625 : Blo 1661530 83101625 := bstep (se 2 (by rfl) ⟨31163109, by rfl⟩ : syracuseStep 83101625 = 62326219) B62326219
theorem B68249573 : Blo 1661530 68249573 := bstep (se 4 (by rfl) ⟨6398397, by rfl⟩ : syracuseStep 68249573 = 12796795) B12796795
theorem B39970945 : Blo 1661530 39970945 := bstep (se 2 (by rfl) ⟨14989104, by rfl⟩ : syracuseStep 39970945 = 29978209) B29978209
theorem B9464039 : Blo 1661530 9464039 := bstep (se 1 (by rfl) ⟨7098029, by rfl⟩ : syracuseStep 9464039 = 14196059) B14196059
theorem B2492879 : Blo 1661530 2492879 := bstep (se 1 (by rfl) ⟨1869659, by rfl⟩ : syracuseStep 2492879 = 3739319) B3739319
theorem B2493083 : Blo 1661530 2493083 := bstep (se 1 (by rfl) ⟨1869812, by rfl⟩ : syracuseStep 2493083 = 3739625) B3739625
theorem B5327623 : Blo 1661530 5327623 := bstep (se 1 (by rfl) ⟨3995717, by rfl⟩ : syracuseStep 5327623 = 7991435) B7991435
theorem B2493551 : Blo 1661530 2493551 := bstep (se 1 (by rfl) ⟨1870163, by rfl⟩ : syracuseStep 2493551 = 3740327) B3740327
theorem B2493599 : Blo 1661530 2493599 := bstep (se 1 (by rfl) ⟨1870199, by rfl⟩ : syracuseStep 2493599 = 3740399) B3740399
theorem B2493929 : Blo 1661530 2493929 := bstep (se 2 (by rfl) ⟨935223, by rfl⟩ : syracuseStep 2493929 = 1870447) B1870447
theorem B28413503 : Blo 1661530 28413503 := bstep (se 1 (by rfl) ⟨21310127, by rfl⟩ : syracuseStep 28413503 = 42620255) B42620255
theorem B4796455 : Blo 1661530 4796455 := bstep (se 1 (by rfl) ⟨3597341, by rfl⟩ : syracuseStep 4796455 = 7194683) B7194683
theorem B2494511 : Blo 1661530 2494511 := bstep (se 1 (by rfl) ⟨1870883, by rfl⟩ : syracuseStep 2494511 = 3741767) B3741767
theorem B3551483 : Blo 1661530 3551483 := bstep (se 1 (by rfl) ⟨2663612, by rfl⟩ : syracuseStep 3551483 = 5327225) B5327225
theorem B13152569 : Blo 1661530 13152569 := bstep (se 2 (by rfl) ⟨4932213, by rfl⟩ : syracuseStep 13152569 = 9864427) B9864427
theorem B4207241 : Blo 1661530 4207241 := bstep (se 2 (by rfl) ⟨1577715, by rfl⟩ : syracuseStep 4207241 = 3155431) B3155431
theorem B3740543 : Blo 1661530 3740543 := bstep (se 1 (by rfl) ⟨2805407, by rfl⟩ : syracuseStep 3740543 = 5610815) B5610815
theorem B4207585 : Blo 1661530 4207585 := bstep (se 2 (by rfl) ⟨1577844, by rfl⟩ : syracuseStep 4207585 = 3155689) B3155689
theorem B5609033 : Blo 1661530 5609033 := bstep (se 2 (by rfl) ⟨2103387, by rfl⟩ : syracuseStep 5609033 = 4206775) B4206775
theorem B4208233 : Blo 1661530 4208233 := bstep (se 2 (by rfl) ⟨1578087, by rfl⟩ : syracuseStep 4208233 = 3156175) B3156175
theorem B3995257 : Blo 1661530 3995257 := bstep (se 2 (by rfl) ⟨1498221, by rfl⟩ : syracuseStep 3995257 = 2996443) B2996443
theorem B2103023 : Blo 1661530 2103023 := bstep (se 1 (by rfl) ⟨1577267, by rfl⟩ : syracuseStep 2103023 = 3154535) B3154535
theorem B20502395 : Blo 1661530 20502395 := bstep (se 1 (by rfl) ⟨15376796, by rfl⟩ : syracuseStep 20502395 = 30753593) B30753593
theorem B21878747 : Blo 1661530 21878747 := bstep (se 1 (by rfl) ⟨16409060, by rfl⟩ : syracuseStep 21878747 = 32818121) B32818121
theorem B5052665 : Blo 1661530 5052665 := bstep (se 2 (by rfl) ⟨1894749, by rfl⟩ : syracuseStep 5052665 = 3789499) B3789499
theorem B40999229 : Blo 1661530 40999229 := bstep (se 3 (by rfl) ⟨7687355, by rfl⟩ : syracuseStep 40999229 = 15374711) B15374711
theorem B5609951 : Blo 1661530 5609951 := bstep (se 1 (by rfl) ⟨4207463, by rfl⟩ : syracuseStep 5609951 = 8414927) B8414927
theorem B6740455 : Blo 1661530 6740455 := bstep (se 1 (by rfl) ⟨5055341, by rfl⟩ : syracuseStep 6740455 = 10110683) B10110683
theorem B1661595 : Blo 1661530 1661595 := bstep (se 1 (by rfl) ⟨1246196, by rfl⟩ : syracuseStep 1661595 = 2492393) B2492393
theorem B1661607 : Blo 1661530 1661607 := bstep (se 1 (by rfl) ⟨1246205, by rfl⟩ : syracuseStep 1661607 = 2492411) B2492411
theorem B18930671 : Blo 1661530 18930671 := bstep (se 1 (by rfl) ⟨14198003, by rfl⟩ : syracuseStep 18930671 = 28396007) B28396007
theorem B7584799 : Blo 1661530 7584799 := bstep (se 1 (by rfl) ⟨5688599, by rfl⟩ : syracuseStep 7584799 = 11377199) B11377199
theorem B21306847 : Blo 1661530 21306847 := bstep (se 1 (by rfl) ⟨15980135, by rfl⟩ : syracuseStep 21306847 = 31960271) B31960271
theorem B65674745 : Blo 1661530 65674745 := bstep (se 2 (by rfl) ⟨24628029, by rfl⟩ : syracuseStep 65674745 = 49256059) B49256059
theorem B1662495 : Blo 1661530 1662495 := bstep (se 1 (by rfl) ⟨1246871, by rfl⟩ : syracuseStep 1662495 = 2493743) B2493743
theorem B1662715 : Blo 1661530 1662715 := bstep (se 1 (by rfl) ⟨1247036, by rfl⟩ : syracuseStep 1662715 = 2494073) B2494073
theorem B5611463 : Blo 1661530 5611463 := bstep (se 1 (by rfl) ⟨4208597, by rfl⟩ : syracuseStep 5611463 = 8417195) B8417195
theorem B1663007 : Blo 1661530 1663007 := bstep (se 1 (by rfl) ⟨1247255, by rfl⟩ : syracuseStep 1663007 = 2494511) B2494511
theorem B8987273 : Blo 1661530 8987273 := bstep (se 2 (by rfl) ⟨3370227, by rfl⟩ : syracuseStep 8987273 = 6740455) B6740455
theorem B9470621 : Blo 1661530 9470621 := bstep (se 3 (by rfl) ⟨1775741, by rfl⟩ : syracuseStep 9470621 = 3551483) B3551483
theorem B7103497 : Blo 1661530 7103497 := bstep (se 2 (by rfl) ⟨2663811, by rfl⟩ : syracuseStep 7103497 = 5327623) B5327623
theorem B45499715 : Blo 1661530 45499715 := bstep (se 1 (by rfl) ⟨34124786, by rfl⟩ : syracuseStep 45499715 = 68249573) B68249573
theorem B6309359 : Blo 1661530 6309359 := bstep (se 1 (by rfl) ⟨4732019, by rfl⟩ : syracuseStep 6309359 = 9464039) B9464039
theorem B2492537 : Blo 1661530 2492537 := bstep (se 2 (by rfl) ⟨934701, by rfl⟩ : syracuseStep 2492537 = 1869403) B1869403
theorem B5327009 : Blo 1661530 5327009 := bstep (se 2 (by rfl) ⟨1997628, by rfl⟩ : syracuseStep 5327009 = 3995257) B3995257
theorem B18942335 : Blo 1661530 18942335 := bstep (se 1 (by rfl) ⟨14206751, by rfl⟩ : syracuseStep 18942335 = 28413503) B28413503
theorem B2492921 : Blo 1661530 2492921 := bstep (se 2 (by rfl) ⟨934845, by rfl⟩ : syracuseStep 2492921 = 1869691) B1869691
theorem B2804827 : Blo 1661530 2804827 := bstep (se 1 (by rfl) ⟨2103620, by rfl⟩ : syracuseStep 2804827 = 4207241) B4207241
theorem B2493695 : Blo 1661530 2493695 := bstep (se 1 (by rfl) ⟨1870271, by rfl⟩ : syracuseStep 2493695 = 3740543) B3740543
theorem B4206107 : Blo 1661530 4206107 := bstep (se 1 (by rfl) ⟨3154580, by rfl⟩ : syracuseStep 4206107 = 6309161) B6309161
theorem B7990991 : Blo 1661530 7990991 := bstep (se 1 (by rfl) ⟨5993243, by rfl⟩ : syracuseStep 7990991 = 11986487) B11986487
theorem B3739355 : Blo 1661530 3739355 := bstep (se 1 (by rfl) ⟨2804516, by rfl⟩ : syracuseStep 3739355 = 5609033) B5609033
theorem B13668263 : Blo 1661530 13668263 := bstep (se 1 (by rfl) ⟨10251197, by rfl⟩ : syracuseStep 13668263 = 20502395) B20502395
theorem B14585831 : Blo 1661530 14585831 := bstep (se 1 (by rfl) ⟨10939373, by rfl⟩ : syracuseStep 14585831 = 21878747) B21878747
theorem B10113065 : Blo 1661530 10113065 := bstep (se 2 (by rfl) ⟨3792399, by rfl⟩ : syracuseStep 10113065 = 7584799) B7584799
theorem B27332819 : Blo 1661530 27332819 := bstep (se 1 (by rfl) ⟨20499614, by rfl⟩ : syracuseStep 27332819 = 40999229) B40999229
theorem B3739967 : Blo 1661530 3739967 := bstep (se 1 (by rfl) ⟨2804975, by rfl⟩ : syracuseStep 3739967 = 5609951) B5609951
theorem B5608061 : Blo 1661530 5608061 := bstep (se 3 (by rfl) ⟨1051511, by rfl⟩ : syracuseStep 5608061 = 2103023) B2103023
theorem B12620447 : Blo 1661530 12620447 := bstep (se 1 (by rfl) ⟨9465335, by rfl⟩ : syracuseStep 12620447 = 18930671) B18930671
theorem B43783163 : Blo 1661530 43783163 := bstep (se 1 (by rfl) ⟨32837372, by rfl⟩ : syracuseStep 43783163 = 65674745) B65674745
theorem B3740975 : Blo 1661530 3740975 := bstep (se 1 (by rfl) ⟨2805731, by rfl⟩ : syracuseStep 3740975 = 5611463) B5611463
theorem B6395273 : Blo 1661530 6395273 := bstep (se 2 (by rfl) ⟨2398227, by rfl⟩ : syracuseStep 6395273 = 4796455) B4796455
theorem B53294593 : Blo 1661530 53294593 := bstep (se 2 (by rfl) ⟨19985472, by rfl⟩ : syracuseStep 53294593 = 39970945) B39970945
theorem B4265855 : Blo 1661530 4265855 := bstep (se 1 (by rfl) ⟨3199391, by rfl⟩ : syracuseStep 4265855 = 6398783) B6398783
theorem B140294069 : Blo 1661530 140294069 := bstep (se 5 (by rfl) ⟨6576284, by rfl⟩ : syracuseStep 140294069 = 13152569) B13152569
theorem B13473773 : Blo 1661530 13473773 := bstep (se 3 (by rfl) ⟨2526332, by rfl⟩ : syracuseStep 13473773 = 5052665) B5052665
theorem B5609519 : Blo 1661530 5609519 := bstep (se 1 (by rfl) ⟨4207139, by rfl⟩ : syracuseStep 5609519 = 8414279) B8414279
theorem B55401083 : Blo 1661530 55401083 := bstep (se 1 (by rfl) ⟨41550812, by rfl⟩ : syracuseStep 55401083 = 83101625) B83101625
theorem B5610113 : Blo 1661530 5610113 := bstep (se 2 (by rfl) ⟨2103792, by rfl⟩ : syracuseStep 5610113 = 4207585) B4207585
theorem B1661919 : Blo 1661530 1661919 := bstep (se 1 (by rfl) ⟨1246439, by rfl⟩ : syracuseStep 1661919 = 2492879) B2492879
theorem B1662055 : Blo 1661530 1662055 := bstep (se 1 (by rfl) ⟨1246541, by rfl⟩ : syracuseStep 1662055 = 2493083) B2493083
theorem B28409129 : Blo 1661530 28409129 := bstep (se 2 (by rfl) ⟨10653423, by rfl⟩ : syracuseStep 28409129 = 21306847) B21306847
theorem B1662367 : Blo 1661530 1662367 := bstep (se 1 (by rfl) ⟨1246775, by rfl⟩ : syracuseStep 1662367 = 2493551) B2493551
theorem B1662399 : Blo 1661530 1662399 := bstep (se 1 (by rfl) ⟨1246799, by rfl⟩ : syracuseStep 1662399 = 2493599) B2493599
theorem B5610977 : Blo 1661530 5610977 := bstep (se 2 (by rfl) ⟨2104116, by rfl⟩ : syracuseStep 5610977 = 4208233) B4208233
theorem B1662619 : Blo 1661530 1662619 := bstep (se 1 (by rfl) ⟨1246964, by rfl⟩ : syracuseStep 1662619 = 2493929) B2493929
theorem B6742043 : Blo 1661530 6742043 := bstep (se 1 (by rfl) ⟨5056532, by rfl⟩ : syracuseStep 6742043 = 10113065) B10113065
theorem B8413631 : Blo 1661530 8413631 := bstep (se 1 (by rfl) ⟨6310223, by rfl⟩ : syracuseStep 8413631 = 12620447) B12620447
theorem B29188775 : Blo 1661530 29188775 := bstep (se 1 (by rfl) ⟨21891581, by rfl⟩ : syracuseStep 29188775 = 43783163) B43783163
theorem B2843903 : Blo 1661530 2843903 := bstep (se 1 (by rfl) ⟨2132927, by rfl⟩ : syracuseStep 2843903 = 4265855) B4265855
theorem B93529379 : Blo 1661530 93529379 := bstep (se 1 (by rfl) ⟨70147034, by rfl⟩ : syracuseStep 93529379 = 140294069) B140294069
theorem B9471329 : Blo 1661530 9471329 := bstep (se 2 (by rfl) ⟨3551748, by rfl⟩ : syracuseStep 9471329 = 7103497) B7103497
theorem B71059457 : Blo 1661530 71059457 := bstep (se 2 (by rfl) ⟨26647296, by rfl⟩ : syracuseStep 71059457 = 53294593) B53294593
theorem B2804071 : Blo 1661530 2804071 := bstep (se 1 (by rfl) ⟨2103053, by rfl⟩ : syracuseStep 2804071 = 4206107) B4206107
theorem B5327327 : Blo 1661530 5327327 := bstep (se 1 (by rfl) ⟨3995495, by rfl⟩ : syracuseStep 5327327 = 7990991) B7990991
theorem B2492903 : Blo 1661530 2492903 := bstep (se 1 (by rfl) ⟨1869677, by rfl⟩ : syracuseStep 2492903 = 3739355) B3739355
theorem B9112175 : Blo 1661530 9112175 := bstep (se 1 (by rfl) ⟨6834131, by rfl⟩ : syracuseStep 9112175 = 13668263) B13668263
theorem B18221879 : Blo 1661530 18221879 := bstep (se 1 (by rfl) ⟨13666409, by rfl⟩ : syracuseStep 18221879 = 27332819) B27332819
theorem B2493311 : Blo 1661530 2493311 := bstep (se 1 (by rfl) ⟨1869983, by rfl⟩ : syracuseStep 2493311 = 3739967) B3739967
theorem B3738707 : Blo 1661530 3738707 := bstep (se 1 (by rfl) ⟨2804030, by rfl⟩ : syracuseStep 3738707 = 5608061) B5608061
theorem B5991515 : Blo 1661530 5991515 := bstep (se 1 (by rfl) ⟨4493636, by rfl⟩ : syracuseStep 5991515 = 8987273) B8987273
theorem B2493983 : Blo 1661530 2493983 := bstep (se 1 (by rfl) ⟨1870487, by rfl⟩ : syracuseStep 2493983 = 3740975) B3740975
theorem B4263515 : Blo 1661530 4263515 := bstep (se 1 (by rfl) ⟨3197636, by rfl⟩ : syracuseStep 4263515 = 6395273) B6395273
theorem B4206239 : Blo 1661530 4206239 := bstep (se 1 (by rfl) ⟨3154679, by rfl⟩ : syracuseStep 4206239 = 6309359) B6309359
theorem B8982515 : Blo 1661530 8982515 := bstep (se 1 (by rfl) ⟨6736886, by rfl⟩ : syracuseStep 8982515 = 13473773) B13473773
theorem B3739679 : Blo 1661530 3739679 := bstep (se 1 (by rfl) ⟨2804759, by rfl⟩ : syracuseStep 3739679 = 5609519) B5609519
theorem B3551339 : Blo 1661530 3551339 := bstep (se 1 (by rfl) ⟨2663504, by rfl⟩ : syracuseStep 3551339 = 5327009) B5327009
theorem B3739769 : Blo 1661530 3739769 := bstep (se 2 (by rfl) ⟨1402413, by rfl⟩ : syracuseStep 3739769 = 2804827) B2804827
theorem B12628223 : Blo 1661530 12628223 := bstep (se 1 (by rfl) ⟨9471167, by rfl⟩ : syracuseStep 12628223 = 18942335) B18942335
theorem B36934055 : Blo 1661530 36934055 := bstep (se 1 (by rfl) ⟨27700541, by rfl⟩ : syracuseStep 36934055 = 55401083) B55401083
theorem B3740075 : Blo 1661530 3740075 := bstep (se 1 (by rfl) ⟨2805056, by rfl⟩ : syracuseStep 3740075 = 5610113) B5610113
theorem B3740651 : Blo 1661530 3740651 := bstep (se 1 (by rfl) ⟨2805488, by rfl⟩ : syracuseStep 3740651 = 5610977) B5610977
theorem B6313747 : Blo 1661530 6313747 := bstep (se 1 (by rfl) ⟨4735310, by rfl⟩ : syracuseStep 6313747 = 9470621) B9470621
theorem B30333143 : Blo 1661530 30333143 := bstep (se 1 (by rfl) ⟨22749857, by rfl⟩ : syracuseStep 30333143 = 45499715) B45499715
theorem B1661691 : Blo 1661530 1661691 := bstep (se 1 (by rfl) ⟨1246268, by rfl⟩ : syracuseStep 1661691 = 2492537) B2492537
theorem B1661947 : Blo 1661530 1661947 := bstep (se 1 (by rfl) ⟨1246460, by rfl⟩ : syracuseStep 1661947 = 2492921) B2492921
theorem B1662463 : Blo 1661530 1662463 := bstep (se 1 (by rfl) ⟨1246847, by rfl⟩ : syracuseStep 1662463 = 2493695) B2493695
theorem B18939419 : Blo 1661530 18939419 := bstep (se 1 (by rfl) ⟨14204564, by rfl⟩ : syracuseStep 18939419 = 28409129) B28409129
theorem B9723887 : Blo 1661530 9723887 := bstep (se 1 (by rfl) ⟨7292915, by rfl⟩ : syracuseStep 9723887 = 14585831) B14585831
theorem B2367559 : Blo 1661530 2367559 := bstep (se 1 (by rfl) ⟨1775669, by rfl⟩ : syracuseStep 2367559 = 3551339) B3551339
theorem B14206205 : Blo 1661530 14206205 := bstep (se 3 (by rfl) ⟨2663663, by rfl⟩ : syracuseStep 14206205 = 5327327) B5327327
theorem B2492471 : Blo 1661530 2492471 := bstep (se 1 (by rfl) ⟨1869353, by rfl⟩ : syracuseStep 2492471 = 3738707) B3738707
theorem B12626279 : Blo 1661530 12626279 := bstep (se 1 (by rfl) ⟨9469709, by rfl⟩ : syracuseStep 12626279 = 18939419) B18939419
theorem B2804159 : Blo 1661530 2804159 := bstep (se 1 (by rfl) ⟨2103119, by rfl⟩ : syracuseStep 2804159 = 4206239) B4206239
theorem B6482591 : Blo 1661530 6482591 := bstep (se 1 (by rfl) ⟨4861943, by rfl⟩ : syracuseStep 6482591 = 9723887) B9723887
theorem B189491885 : Blo 1661530 189491885 := bstep (se 3 (by rfl) ⟨35529728, by rfl⟩ : syracuseStep 189491885 = 71059457) B71059457
theorem B2493119 : Blo 1661530 2493119 := bstep (se 1 (by rfl) ⟨1869839, by rfl⟩ : syracuseStep 2493119 = 3739679) B3739679
theorem B2493179 : Blo 1661530 2493179 := bstep (se 1 (by rfl) ⟨1869884, by rfl⟩ : syracuseStep 2493179 = 3739769) B3739769
theorem B2493383 : Blo 1661530 2493383 := bstep (se 1 (by rfl) ⟨1870037, by rfl⟩ : syracuseStep 2493383 = 3740075) B3740075
theorem B19459183 : Blo 1661530 19459183 := bstep (se 1 (by rfl) ⟨14594387, by rfl⟩ : syracuseStep 19459183 = 29188775) B29188775
theorem B3738761 : Blo 1661530 3738761 := bstep (se 2 (by rfl) ⟨1402035, by rfl⟩ : syracuseStep 3738761 = 2804071) B2804071
theorem B2493767 : Blo 1661530 2493767 := bstep (se 1 (by rfl) ⟨1870325, by rfl⟩ : syracuseStep 2493767 = 3740651) B3740651
theorem B1895935 : Blo 1661530 1895935 := bstep (se 1 (by rfl) ⟨1421951, by rfl⟩ : syracuseStep 1895935 = 2843903) B2843903
theorem B62352919 : Blo 1661530 62352919 := bstep (se 1 (by rfl) ⟨46764689, by rfl⟩ : syracuseStep 62352919 = 93529379) B93529379
theorem B20222095 : Blo 1661530 20222095 := bstep (se 1 (by rfl) ⟨15166571, by rfl⟩ : syracuseStep 20222095 = 30333143) B30333143
theorem B6074783 : Blo 1661530 6074783 := bstep (se 1 (by rfl) ⟨4556087, by rfl⟩ : syracuseStep 6074783 = 9112175) B9112175
theorem B3994343 : Blo 1661530 3994343 := bstep (se 1 (by rfl) ⟨2995757, by rfl⟩ : syracuseStep 3994343 = 5991515) B5991515
theorem B48591677 : Blo 1661530 48591677 := bstep (se 3 (by rfl) ⟨9110939, by rfl⟩ : syracuseStep 48591677 = 18221879) B18221879
theorem B8418329 : Blo 1661530 8418329 := bstep (se 2 (by rfl) ⟨3156873, by rfl⟩ : syracuseStep 8418329 = 6313747) B6313747
theorem B4494695 : Blo 1661530 4494695 := bstep (se 1 (by rfl) ⟨3371021, by rfl⟩ : syracuseStep 4494695 = 6742043) B6742043
theorem B8418815 : Blo 1661530 8418815 := bstep (se 1 (by rfl) ⟨6314111, by rfl⟩ : syracuseStep 8418815 = 12628223) B12628223
theorem B24622703 : Blo 1661530 24622703 := bstep (se 1 (by rfl) ⟨18467027, by rfl⟩ : syracuseStep 24622703 = 36934055) B36934055
theorem B5609087 : Blo 1661530 5609087 := bstep (se 1 (by rfl) ⟨4206815, by rfl⟩ : syracuseStep 5609087 = 8413631) B8413631
theorem B6314219 : Blo 1661530 6314219 := bstep (se 1 (by rfl) ⟨4735664, by rfl⟩ : syracuseStep 6314219 = 9471329) B9471329
theorem B5988343 : Blo 1661530 5988343 := bstep (se 1 (by rfl) ⟨4491257, by rfl⟩ : syracuseStep 5988343 = 8982515) B8982515
theorem B1661935 : Blo 1661530 1661935 := bstep (se 1 (by rfl) ⟨1246451, by rfl⟩ : syracuseStep 1661935 = 2492903) B2492903
theorem B1662207 : Blo 1661530 1662207 := bstep (se 1 (by rfl) ⟨1246655, by rfl⟩ : syracuseStep 1662207 = 2493311) B2493311
theorem B1662655 : Blo 1661530 1662655 := bstep (se 1 (by rfl) ⟨1246991, by rfl⟩ : syracuseStep 1662655 = 2493983) B2493983
theorem B2842343 : Blo 1661530 2842343 := bstep (se 1 (by rfl) ⟨2131757, by rfl⟩ : syracuseStep 2842343 = 4263515) B4263515
theorem B2662895 : Blo 1661530 2662895 := bstep (se 1 (by rfl) ⟨1997171, by rfl⟩ : syracuseStep 2662895 = 3994343) B3994343
theorem B5612219 : Blo 1661530 5612219 := bstep (se 1 (by rfl) ⟨4209164, by rfl⟩ : syracuseStep 5612219 = 8418329) B8418329
theorem B9470803 : Blo 1661530 9470803 := bstep (se 1 (by rfl) ⟨7103102, by rfl⟩ : syracuseStep 9470803 = 14206205) B14206205
theorem B5612543 : Blo 1661530 5612543 := bstep (se 1 (by rfl) ⟨4209407, by rfl⟩ : syracuseStep 5612543 = 8418815) B8418815
theorem B25945577 : Blo 1661530 25945577 := bstep (se 2 (by rfl) ⟨9729591, by rfl⟩ : syracuseStep 25945577 = 19459183) B19459183
theorem B1869439 : Blo 1661530 1869439 := bstep (se 1 (by rfl) ⟨1402079, by rfl⟩ : syracuseStep 1869439 = 2804159) B2804159
theorem B2492507 : Blo 1661530 2492507 := bstep (se 1 (by rfl) ⟨1869380, by rfl⟩ : syracuseStep 2492507 = 3738761) B3738761
theorem B1894895 : Blo 1661530 1894895 := bstep (se 1 (by rfl) ⟨1421171, by rfl⟩ : syracuseStep 1894895 = 2842343) B2842343
theorem B3156745 : Blo 1661530 3156745 := bstep (se 2 (by rfl) ⟨1183779, by rfl⟩ : syracuseStep 3156745 = 2367559) B2367559
theorem B332548901 : Blo 1661530 332548901 := bstep (se 4 (by rfl) ⟨31176459, by rfl⟩ : syracuseStep 332548901 = 62352919) B62352919
theorem B26962793 : Blo 1661530 26962793 := bstep (se 2 (by rfl) ⟨10111047, by rfl⟩ : syracuseStep 26962793 = 20222095) B20222095
theorem B4049855 : Blo 1661530 4049855 := bstep (se 1 (by rfl) ⟨3037391, by rfl⟩ : syracuseStep 4049855 = 6074783) B6074783
theorem B47943413 : Blo 1661530 47943413 := bstep (se 5 (by rfl) ⟨2247347, by rfl⟩ : syracuseStep 47943413 = 4494695) B4494695
theorem B3739391 : Blo 1661530 3739391 := bstep (se 1 (by rfl) ⟨2804543, by rfl⟩ : syracuseStep 3739391 = 5609087) B5609087
theorem B8417519 : Blo 1661530 8417519 := bstep (se 1 (by rfl) ⟨6313139, by rfl⟩ : syracuseStep 8417519 = 12626279) B12626279
theorem B4321727 : Blo 1661530 4321727 := bstep (se 1 (by rfl) ⟨3241295, by rfl⟩ : syracuseStep 4321727 = 6482591) B6482591
theorem B2527913 : Blo 1661530 2527913 := bstep (se 2 (by rfl) ⟨947967, by rfl⟩ : syracuseStep 2527913 = 1895935) B1895935
theorem B129577805 : Blo 1661530 129577805 := bstep (se 3 (by rfl) ⟨24295838, by rfl⟩ : syracuseStep 129577805 = 48591677) B48591677
theorem B7984457 : Blo 1661530 7984457 := bstep (se 2 (by rfl) ⟨2994171, by rfl⟩ : syracuseStep 7984457 = 5988343) B5988343
theorem B16415135 : Blo 1661530 16415135 := bstep (se 1 (by rfl) ⟨12311351, by rfl⟩ : syracuseStep 16415135 = 24622703) B24622703
theorem B1661647 : Blo 1661530 1661647 := bstep (se 1 (by rfl) ⟨1246235, by rfl⟩ : syracuseStep 1661647 = 2492471) B2492471
theorem B4209479 : Blo 1661530 4209479 := bstep (se 1 (by rfl) ⟨3157109, by rfl⟩ : syracuseStep 4209479 = 6314219) B6314219
theorem B126327923 : Blo 1661530 126327923 := bstep (se 1 (by rfl) ⟨94745942, by rfl⟩ : syracuseStep 126327923 = 189491885) B189491885
theorem B1662079 : Blo 1661530 1662079 := bstep (se 1 (by rfl) ⟨1246559, by rfl⟩ : syracuseStep 1662079 = 2493119) B2493119
theorem B1662119 : Blo 1661530 1662119 := bstep (se 1 (by rfl) ⟨1246589, by rfl⟩ : syracuseStep 1662119 = 2493179) B2493179
theorem B1662255 : Blo 1661530 1662255 := bstep (se 1 (by rfl) ⟨1246691, by rfl⟩ : syracuseStep 1662255 = 2493383) B2493383
theorem B1662511 : Blo 1661530 1662511 := bstep (se 1 (by rfl) ⟨1246883, by rfl⟩ : syracuseStep 1662511 = 2493767) B2493767
theorem B5611679 : Blo 1661530 5611679 := bstep (se 1 (by rfl) ⟨4208759, by rfl⟩ : syracuseStep 5611679 = 8417519) B8417519
theorem B86385203 : Blo 1661530 86385203 := bstep (se 1 (by rfl) ⟨64788902, by rfl⟩ : syracuseStep 86385203 = 129577805) B129577805
theorem B17975195 : Blo 1661530 17975195 := bstep (se 1 (by rfl) ⟨13481396, by rfl⟩ : syracuseStep 17975195 = 26962793) B26962793
theorem B2492585 : Blo 1661530 2492585 := bstep (se 2 (by rfl) ⟨934719, by rfl⟩ : syracuseStep 2492585 = 1869439) B1869439
theorem B276752821 : Blo 1661530 276752821 := bstep (se 5 (by rfl) ⟨12972788, by rfl⟩ : syracuseStep 276752821 = 25945577) B25945577
theorem B20212213 : Blo 1661530 20212213 := bstep (se 5 (by rfl) ⟨947447, by rfl⟩ : syracuseStep 20212213 = 1894895) B1894895
theorem B2492927 : Blo 1661530 2492927 := bstep (se 1 (by rfl) ⟨1869695, by rfl⟩ : syracuseStep 2492927 = 3739391) B3739391
theorem B12627737 : Blo 1661530 12627737 := bstep (se 2 (by rfl) ⟨4735401, by rfl⟩ : syracuseStep 12627737 = 9470803) B9470803
theorem B2806319 : Blo 1661530 2806319 := bstep (se 1 (by rfl) ⟨2104739, by rfl⟩ : syracuseStep 2806319 = 4209479) B4209479
theorem B2699903 : Blo 1661530 2699903 := bstep (se 1 (by rfl) ⟨2024927, by rfl⟩ : syracuseStep 2699903 = 4049855) B4049855
theorem B84218615 : Blo 1661530 84218615 := bstep (se 1 (by rfl) ⟨63163961, by rfl⟩ : syracuseStep 84218615 = 126327923) B126327923
theorem B31962275 : Blo 1661530 31962275 := bstep (se 1 (by rfl) ⟨23971706, by rfl⟩ : syracuseStep 31962275 = 47943413) B47943413
theorem B2881151 : Blo 1661530 2881151 := bstep (se 1 (by rfl) ⟨2160863, by rfl⟩ : syracuseStep 2881151 = 4321727) B4321727
theorem B3741479 : Blo 1661530 3741479 := bstep (se 1 (by rfl) ⟨2806109, by rfl⟩ : syracuseStep 3741479 = 5612219) B5612219
theorem B3741695 : Blo 1661530 3741695 := bstep (se 1 (by rfl) ⟨2806271, by rfl⟩ : syracuseStep 3741695 = 5612543) B5612543
theorem B5322971 : Blo 1661530 5322971 := bstep (se 1 (by rfl) ⟨3992228, by rfl⟩ : syracuseStep 5322971 = 7984457) B7984457
theorem B4208993 : Blo 1661530 4208993 := bstep (se 2 (by rfl) ⟨1578372, by rfl⟩ : syracuseStep 4208993 = 3156745) B3156745
theorem B7101053 : Blo 1661530 7101053 := bstep (se 3 (by rfl) ⟨1331447, by rfl⟩ : syracuseStep 7101053 = 2662895) B2662895
theorem B1661671 : Blo 1661530 1661671 := bstep (se 1 (by rfl) ⟨1246253, by rfl⟩ : syracuseStep 1661671 = 2492507) B2492507
theorem B10943423 : Blo 1661530 10943423 := bstep (se 1 (by rfl) ⟨8207567, by rfl⟩ : syracuseStep 10943423 = 16415135) B16415135
theorem B6741101 : Blo 1661530 6741101 := bstep (se 3 (by rfl) ⟨1263956, by rfl⟩ : syracuseStep 6741101 = 2527913) B2527913
theorem B221699267 : Blo 1661530 221699267 := bstep (se 1 (by rfl) ⟨166274450, by rfl⟩ : syracuseStep 221699267 = 332548901) B332548901
theorem B57590135 : Blo 1661530 57590135 := bstep (se 1 (by rfl) ⟨43192601, by rfl⟩ : syracuseStep 57590135 = 86385203) B86385203
theorem B21308183 : Blo 1661530 21308183 := bstep (se 1 (by rfl) ⟨15981137, by rfl⟩ : syracuseStep 21308183 = 31962275) B31962275
theorem B3548647 : Blo 1661530 3548647 := bstep (se 1 (by rfl) ⟨2661485, by rfl⟩ : syracuseStep 3548647 = 5322971) B5322971
theorem B17976269 : Blo 1661530 17976269 := bstep (se 3 (by rfl) ⟨3370550, by rfl⟩ : syracuseStep 17976269 = 6741101) B6741101
theorem B1870879 : Blo 1661530 1870879 := bstep (se 1 (by rfl) ⟨1403159, by rfl⟩ : syracuseStep 1870879 = 2806319) B2806319
theorem B369003761 : Blo 1661530 369003761 := bstep (se 2 (by rfl) ⟨138376410, by rfl⟩ : syracuseStep 369003761 = 276752821) B276752821
theorem B1920767 : Blo 1661530 1920767 := bstep (se 1 (by rfl) ⟨1440575, by rfl⟩ : syracuseStep 1920767 = 2881151) B2881151
theorem B2494319 : Blo 1661530 2494319 := bstep (se 1 (by rfl) ⟨1870739, by rfl⟩ : syracuseStep 2494319 = 3741479) B3741479
theorem B2494463 : Blo 1661530 2494463 := bstep (se 1 (by rfl) ⟨1870847, by rfl⟩ : syracuseStep 2494463 = 3741695) B3741695
theorem B2805995 : Blo 1661530 2805995 := bstep (se 1 (by rfl) ⟨2104496, by rfl⟩ : syracuseStep 2805995 = 4208993) B4208993
theorem B7295615 : Blo 1661530 7295615 := bstep (se 1 (by rfl) ⟨5471711, by rfl⟩ : syracuseStep 7295615 = 10943423) B10943423
theorem B8418491 : Blo 1661530 8418491 := bstep (se 1 (by rfl) ⟨6313868, by rfl⟩ : syracuseStep 8418491 = 12627737) B12627737
theorem B3741119 : Blo 1661530 3741119 := bstep (se 1 (by rfl) ⟨2805839, by rfl⟩ : syracuseStep 3741119 = 5611679) B5611679
theorem B56145743 : Blo 1661530 56145743 := bstep (se 1 (by rfl) ⟨42109307, by rfl⟩ : syracuseStep 56145743 = 84218615) B84218615
theorem B26949617 : Blo 1661530 26949617 := bstep (se 2 (by rfl) ⟨10106106, by rfl⟩ : syracuseStep 26949617 = 20212213) B20212213
theorem B11983463 : Blo 1661530 11983463 := bstep (se 1 (by rfl) ⟨8987597, by rfl⟩ : syracuseStep 11983463 = 17975195) B17975195
theorem B1661723 : Blo 1661530 1661723 := bstep (se 1 (by rfl) ⟨1246292, by rfl⟩ : syracuseStep 1661723 = 2492585) B2492585
theorem B7199741 : Blo 1661530 7199741 := bstep (se 3 (by rfl) ⟨1349951, by rfl⟩ : syracuseStep 7199741 = 2699903) B2699903
theorem B1661951 : Blo 1661530 1661951 := bstep (se 1 (by rfl) ⟨1246463, by rfl⟩ : syracuseStep 1661951 = 2492927) B2492927
theorem B4734035 : Blo 1661530 4734035 := bstep (se 1 (by rfl) ⟨3550526, by rfl⟩ : syracuseStep 4734035 = 7101053) B7101053
theorem B147799511 : Blo 1661530 147799511 := bstep (se 1 (by rfl) ⟨110849633, by rfl⟩ : syracuseStep 147799511 = 221699267) B221699267
theorem B14205455 : Blo 1661530 14205455 := bstep (se 1 (by rfl) ⟨10654091, by rfl⟩ : syracuseStep 14205455 = 21308183) B21308183
theorem B5612327 : Blo 1661530 5612327 := bstep (se 1 (by rfl) ⟨4209245, by rfl⟩ : syracuseStep 5612327 = 8418491) B8418491
theorem B37430495 : Blo 1661530 37430495 := bstep (se 1 (by rfl) ⟨28072871, by rfl⟩ : syracuseStep 37430495 = 56145743) B56145743
theorem B17966411 : Blo 1661530 17966411 := bstep (se 1 (by rfl) ⟨13474808, by rfl⟩ : syracuseStep 17966411 = 26949617) B26949617
theorem B7988975 : Blo 1661530 7988975 := bstep (se 1 (by rfl) ⟨5991731, by rfl⟩ : syracuseStep 7988975 = 11983463) B11983463
theorem B5122045 : Blo 1661530 5122045 := bstep (se 3 (by rfl) ⟨960383, by rfl⟩ : syracuseStep 5122045 = 1920767) B1920767
theorem B3156023 : Blo 1661530 3156023 := bstep (se 1 (by rfl) ⟨2367017, by rfl⟩ : syracuseStep 3156023 = 4734035) B4734035
theorem B1870663 : Blo 1661530 1870663 := bstep (se 1 (by rfl) ⟨1402997, by rfl⟩ : syracuseStep 1870663 = 2805995) B2805995
theorem B2494079 : Blo 1661530 2494079 := bstep (se 1 (by rfl) ⟨1870559, by rfl⟩ : syracuseStep 2494079 = 3741119) B3741119
theorem B2494505 : Blo 1661530 2494505 := bstep (se 2 (by rfl) ⟨935439, by rfl⟩ : syracuseStep 2494505 = 1870879) B1870879
theorem B4731529 : Blo 1661530 4731529 := bstep (se 2 (by rfl) ⟨1774323, by rfl⟩ : syracuseStep 4731529 = 3548647) B3548647
theorem B246002507 : Blo 1661530 246002507 := bstep (se 1 (by rfl) ⟨184501880, by rfl⟩ : syracuseStep 246002507 = 369003761) B369003761
theorem B47936717 : Blo 1661530 47936717 := bstep (se 3 (by rfl) ⟨8988134, by rfl⟩ : syracuseStep 47936717 = 17976269) B17976269
theorem B38393423 : Blo 1661530 38393423 := bstep (se 1 (by rfl) ⟨28795067, by rfl⟩ : syracuseStep 38393423 = 57590135) B57590135
theorem B4863743 : Blo 1661530 4863743 := bstep (se 1 (by rfl) ⟨3647807, by rfl⟩ : syracuseStep 4863743 = 7295615) B7295615
theorem B4799827 : Blo 1661530 4799827 := bstep (se 1 (by rfl) ⟨3599870, by rfl⟩ : syracuseStep 4799827 = 7199741) B7199741
theorem B98533007 : Blo 1661530 98533007 := bstep (se 1 (by rfl) ⟨73899755, by rfl⟩ : syracuseStep 98533007 = 147799511) B147799511
theorem B1662879 : Blo 1661530 1662879 := bstep (se 1 (by rfl) ⟨1247159, by rfl⟩ : syracuseStep 1662879 = 2494319) B2494319
theorem B1662975 : Blo 1661530 1662975 := bstep (se 1 (by rfl) ⟨1247231, by rfl⟩ : syracuseStep 1662975 = 2494463) B2494463
theorem B1663003 : Blo 1661530 1663003 := bstep (se 1 (by rfl) ⟨1247252, by rfl⟩ : syracuseStep 1663003 = 2494505) B2494505
theorem B9470303 : Blo 1661530 9470303 := bstep (se 1 (by rfl) ⟨7102727, by rfl⟩ : syracuseStep 9470303 = 14205455) B14205455
theorem B31957811 : Blo 1661530 31957811 := bstep (se 1 (by rfl) ⟨23968358, by rfl⟩ : syracuseStep 31957811 = 47936717) B47936717
theorem B24953663 : Blo 1661530 24953663 := bstep (se 1 (by rfl) ⟨18715247, by rfl⟩ : syracuseStep 24953663 = 37430495) B37430495
theorem B6308705 : Blo 1661530 6308705 := bstep (se 2 (by rfl) ⟨2365764, by rfl⟩ : syracuseStep 6308705 = 4731529) B4731529
theorem B11977607 : Blo 1661530 11977607 := bstep (se 1 (by rfl) ⟨8983205, by rfl⟩ : syracuseStep 11977607 = 17966411) B17966411
theorem B5325983 : Blo 1661530 5325983 := bstep (se 1 (by rfl) ⟨3994487, by rfl⟩ : syracuseStep 5325983 = 7988975) B7988975
theorem B8416061 : Blo 1661530 8416061 := bstep (se 3 (by rfl) ⟨1578011, by rfl⟩ : syracuseStep 8416061 = 3156023) B3156023
theorem B25595615 : Blo 1661530 25595615 := bstep (se 1 (by rfl) ⟨19196711, by rfl⟩ : syracuseStep 25595615 = 38393423) B38393423
theorem B2494217 : Blo 1661530 2494217 := bstep (se 2 (by rfl) ⟨935331, by rfl⟩ : syracuseStep 2494217 = 1870663) B1870663
theorem B65688671 : Blo 1661530 65688671 := bstep (se 1 (by rfl) ⟨49266503, by rfl⟩ : syracuseStep 65688671 = 98533007) B98533007
theorem B6829393 : Blo 1661530 6829393 := bstep (se 2 (by rfl) ⟨2561022, by rfl⟩ : syracuseStep 6829393 = 5122045) B5122045
theorem B3741551 : Blo 1661530 3741551 := bstep (se 1 (by rfl) ⟨2806163, by rfl⟩ : syracuseStep 3741551 = 5612327) B5612327
theorem B164001671 : Blo 1661530 164001671 := bstep (se 1 (by rfl) ⟨123001253, by rfl⟩ : syracuseStep 164001671 = 246002507) B246002507
theorem B3242495 : Blo 1661530 3242495 := bstep (se 1 (by rfl) ⟨2431871, by rfl⟩ : syracuseStep 3242495 = 4863743) B4863743
theorem B25599077 : Blo 1661530 25599077 := bstep (se 4 (by rfl) ⟨2399913, by rfl⟩ : syracuseStep 25599077 = 4799827) B4799827
theorem B1662719 : Blo 1661530 1662719 := bstep (se 1 (by rfl) ⟨1247039, by rfl⟩ : syracuseStep 1662719 = 2494079) B2494079
theorem B17066051 : Blo 1661530 17066051 := bstep (se 1 (by rfl) ⟨12799538, by rfl⟩ : syracuseStep 17066051 = 25599077) B25599077
theorem B4205803 : Blo 1661530 4205803 := bstep (se 1 (by rfl) ⟨3154352, by rfl⟩ : syracuseStep 4205803 = 6308705) B6308705
theorem B3550655 : Blo 1661530 3550655 := bstep (se 1 (by rfl) ⟨2662991, by rfl⟩ : syracuseStep 3550655 = 5325983) B5325983
theorem B2494367 : Blo 1661530 2494367 := bstep (se 1 (by rfl) ⟨1870775, by rfl⟩ : syracuseStep 2494367 = 3741551) B3741551
theorem B109334447 : Blo 1661530 109334447 := bstep (se 1 (by rfl) ⟨82000835, by rfl⟩ : syracuseStep 109334447 = 164001671) B164001671
theorem B8646653 : Blo 1661530 8646653 := bstep (se 3 (by rfl) ⟨1621247, by rfl⟩ : syracuseStep 8646653 = 3242495) B3242495
theorem B9105857 : Blo 1661530 9105857 := bstep (se 2 (by rfl) ⟨3414696, by rfl⟩ : syracuseStep 9105857 = 6829393) B6829393
theorem B6313535 : Blo 1661530 6313535 := bstep (se 1 (by rfl) ⟨4735151, by rfl⟩ : syracuseStep 6313535 = 9470303) B9470303
theorem B21305207 : Blo 1661530 21305207 := bstep (se 1 (by rfl) ⟨15978905, by rfl⟩ : syracuseStep 21305207 = 31957811) B31957811
theorem B16635775 : Blo 1661530 16635775 := bstep (se 1 (by rfl) ⟨12476831, by rfl⟩ : syracuseStep 16635775 = 24953663) B24953663
theorem B7985071 : Blo 1661530 7985071 := bstep (se 1 (by rfl) ⟨5988803, by rfl⟩ : syracuseStep 7985071 = 11977607) B11977607
theorem B43792447 : Blo 1661530 43792447 := bstep (se 1 (by rfl) ⟨32844335, by rfl⟩ : syracuseStep 43792447 = 65688671) B65688671
theorem B5610707 : Blo 1661530 5610707 := bstep (se 1 (by rfl) ⟨4208030, by rfl⟩ : syracuseStep 5610707 = 8416061) B8416061
theorem B68254973 : Blo 1661530 68254973 := bstep (se 3 (by rfl) ⟨12797807, by rfl⟩ : syracuseStep 68254973 = 25595615) B25595615
theorem B1662811 : Blo 1661530 1662811 := bstep (se 1 (by rfl) ⟨1247108, by rfl⟩ : syracuseStep 1662811 = 2494217) B2494217
theorem B6070571 : Blo 1661530 6070571 := bstep (se 1 (by rfl) ⟨4552928, by rfl⟩ : syracuseStep 6070571 = 9105857) B9105857
theorem B5607737 : Blo 1661530 5607737 := bstep (se 2 (by rfl) ⟨2102901, by rfl⟩ : syracuseStep 5607737 = 4205803) B4205803
theorem B3740471 : Blo 1661530 3740471 := bstep (se 1 (by rfl) ⟨2805353, by rfl⟩ : syracuseStep 3740471 = 5610707) B5610707
theorem B45503315 : Blo 1661530 45503315 := bstep (se 1 (by rfl) ⟨34127486, by rfl⟩ : syracuseStep 45503315 = 68254973) B68254973
theorem B22181033 : Blo 1661530 22181033 := bstep (se 2 (by rfl) ⟨8317887, by rfl⟩ : syracuseStep 22181033 = 16635775) B16635775
theorem B10646761 : Blo 1661530 10646761 := bstep (se 2 (by rfl) ⟨3992535, by rfl⟩ : syracuseStep 10646761 = 7985071) B7985071
theorem B72889631 : Blo 1661530 72889631 := bstep (se 1 (by rfl) ⟨54667223, by rfl⟩ : syracuseStep 72889631 = 109334447) B109334447
theorem B23057741 : Blo 1661530 23057741 := bstep (se 3 (by rfl) ⟨4323326, by rfl⟩ : syracuseStep 23057741 = 8646653) B8646653
theorem B58389929 : Blo 1661530 58389929 := bstep (se 2 (by rfl) ⟨21896223, by rfl⟩ : syracuseStep 58389929 = 43792447) B43792447
theorem B4209023 : Blo 1661530 4209023 := bstep (se 1 (by rfl) ⟨3156767, by rfl⟩ : syracuseStep 4209023 = 6313535) B6313535
theorem B9468413 : Blo 1661530 9468413 := bstep (se 3 (by rfl) ⟨1775327, by rfl⟩ : syracuseStep 9468413 = 3550655) B3550655
theorem B14203471 : Blo 1661530 14203471 := bstep (se 1 (by rfl) ⟨10652603, by rfl⟩ : syracuseStep 14203471 = 21305207) B21305207
theorem B11377367 : Blo 1661530 11377367 := bstep (se 1 (by rfl) ⟨8533025, by rfl⟩ : syracuseStep 11377367 = 17066051) B17066051
theorem B1662911 : Blo 1661530 1662911 := bstep (se 1 (by rfl) ⟨1247183, by rfl⟩ : syracuseStep 1662911 = 2494367) B2494367
theorem B4047047 : Blo 1661530 4047047 := bstep (se 1 (by rfl) ⟨3035285, by rfl⟩ : syracuseStep 4047047 = 6070571) B6070571
theorem B30335543 : Blo 1661530 30335543 := bstep (se 1 (by rfl) ⟨22751657, by rfl⟩ : syracuseStep 30335543 = 45503315) B45503315
theorem B14787355 : Blo 1661530 14787355 := bstep (se 1 (by rfl) ⟨11090516, by rfl⟩ : syracuseStep 14787355 = 22181033) B22181033
theorem B3738491 : Blo 1661530 3738491 := bstep (se 1 (by rfl) ⟨2803868, by rfl⟩ : syracuseStep 3738491 = 5607737) B5607737
theorem B2493647 : Blo 1661530 2493647 := bstep (se 1 (by rfl) ⟨1870235, by rfl⟩ : syracuseStep 2493647 = 3740471) B3740471
theorem B2806015 : Blo 1661530 2806015 := bstep (se 1 (by rfl) ⟨2104511, by rfl⟩ : syracuseStep 2806015 = 4209023) B4209023
theorem B6312275 : Blo 1661530 6312275 := bstep (se 1 (by rfl) ⟨4734206, by rfl⟩ : syracuseStep 6312275 = 9468413) B9468413
theorem B18937961 : Blo 1661530 18937961 := bstep (se 2 (by rfl) ⟨7101735, by rfl⟩ : syracuseStep 18937961 = 14203471) B14203471
theorem B48593087 : Blo 1661530 48593087 := bstep (se 1 (by rfl) ⟨36444815, by rfl⟩ : syracuseStep 48593087 = 72889631) B72889631
theorem B61487309 : Blo 1661530 61487309 := bstep (se 3 (by rfl) ⟨11528870, by rfl⟩ : syracuseStep 61487309 = 23057741) B23057741
theorem B38926619 : Blo 1661530 38926619 := bstep (se 1 (by rfl) ⟨29194964, by rfl⟩ : syracuseStep 38926619 = 58389929) B58389929
theorem B14195681 : Blo 1661530 14195681 := bstep (se 2 (by rfl) ⟨5323380, by rfl⟩ : syracuseStep 14195681 = 10646761) B10646761
theorem B7584911 : Blo 1661530 7584911 := bstep (se 1 (by rfl) ⟨5688683, by rfl⟩ : syracuseStep 7584911 = 11377367) B11377367
theorem B12625307 : Blo 1661530 12625307 := bstep (se 1 (by rfl) ⟨9468980, by rfl⟩ : syracuseStep 12625307 = 18937961) B18937961
theorem B2492327 : Blo 1661530 2492327 := bstep (se 1 (by rfl) ⟨1869245, by rfl⟩ : syracuseStep 2492327 = 3738491) B3738491
theorem B9463787 : Blo 1661530 9463787 := bstep (se 1 (by rfl) ⟨7097840, by rfl⟩ : syracuseStep 9463787 = 14195681) B14195681
theorem B5056607 : Blo 1661530 5056607 := bstep (se 1 (by rfl) ⟨3792455, by rfl⟩ : syracuseStep 5056607 = 7584911) B7584911
theorem B2698031 : Blo 1661530 2698031 := bstep (se 1 (by rfl) ⟨2023523, by rfl⟩ : syracuseStep 2698031 = 4047047) B4047047
theorem B163966157 : Blo 1661530 163966157 := bstep (se 3 (by rfl) ⟨30743654, by rfl⟩ : syracuseStep 163966157 = 61487309) B61487309
theorem B32395391 : Blo 1661530 32395391 := bstep (se 1 (by rfl) ⟨24296543, by rfl⟩ : syracuseStep 32395391 = 48593087) B48593087
theorem B4208183 : Blo 1661530 4208183 := bstep (se 1 (by rfl) ⟨3156137, by rfl⟩ : syracuseStep 4208183 = 6312275) B6312275
theorem B3741353 : Blo 1661530 3741353 := bstep (se 2 (by rfl) ⟨1403007, by rfl⟩ : syracuseStep 3741353 = 2806015) B2806015
theorem B20223695 : Blo 1661530 20223695 := bstep (se 1 (by rfl) ⟨15167771, by rfl⟩ : syracuseStep 20223695 = 30335543) B30335543
theorem B19716473 : Blo 1661530 19716473 := bstep (se 2 (by rfl) ⟨7393677, by rfl⟩ : syracuseStep 19716473 = 14787355) B14787355
theorem B25951079 : Blo 1661530 25951079 := bstep (se 1 (by rfl) ⟨19463309, by rfl⟩ : syracuseStep 25951079 = 38926619) B38926619
theorem B1662431 : Blo 1661530 1662431 := bstep (se 1 (by rfl) ⟨1246823, by rfl⟩ : syracuseStep 1662431 = 2493647) B2493647
theorem B6309191 : Blo 1661530 6309191 := bstep (se 1 (by rfl) ⟨4731893, by rfl⟩ : syracuseStep 6309191 = 9463787) B9463787
theorem B7194749 : Blo 1661530 7194749 := bstep (se 3 (by rfl) ⟨1349015, by rfl⟩ : syracuseStep 7194749 = 2698031) B2698031
theorem B21596927 : Blo 1661530 21596927 := bstep (se 1 (by rfl) ⟨16197695, by rfl⟩ : syracuseStep 21596927 = 32395391) B32395391
theorem B8416871 : Blo 1661530 8416871 := bstep (se 1 (by rfl) ⟨6312653, by rfl⟩ : syracuseStep 8416871 = 12625307) B12625307
theorem B2805455 : Blo 1661530 2805455 := bstep (se 1 (by rfl) ⟨2104091, by rfl⟩ : syracuseStep 2805455 = 4208183) B4208183
theorem B2494235 : Blo 1661530 2494235 := bstep (se 1 (by rfl) ⟨1870676, by rfl⟩ : syracuseStep 2494235 = 3741353) B3741353
theorem B3371071 : Blo 1661530 3371071 := bstep (se 1 (by rfl) ⟨2528303, by rfl⟩ : syracuseStep 3371071 = 5056607) B5056607
theorem B13144315 : Blo 1661530 13144315 := bstep (se 1 (by rfl) ⟨9858236, by rfl⟩ : syracuseStep 13144315 = 19716473) B19716473
theorem B109310771 : Blo 1661530 109310771 := bstep (se 1 (by rfl) ⟨81983078, by rfl⟩ : syracuseStep 109310771 = 163966157) B163966157
theorem B13482463 : Blo 1661530 13482463 := bstep (se 1 (by rfl) ⟨10111847, by rfl⟩ : syracuseStep 13482463 = 20223695) B20223695
theorem B1661551 : Blo 1661530 1661551 := bstep (se 1 (by rfl) ⟨1246163, by rfl⟩ : syracuseStep 1661551 = 2492327) B2492327
theorem B17300719 : Blo 1661530 17300719 := bstep (se 1 (by rfl) ⟨12975539, by rfl⟩ : syracuseStep 17300719 = 25951079) B25951079
theorem B19185997 : Blo 1661530 19185997 := bstep (se 3 (by rfl) ⟨3597374, by rfl⟩ : syracuseStep 19185997 = 7194749) B7194749
theorem B57591805 : Blo 1661530 57591805 := bstep (se 3 (by rfl) ⟨10798463, by rfl⟩ : syracuseStep 57591805 = 21596927) B21596927
theorem B1870303 : Blo 1661530 1870303 := bstep (se 1 (by rfl) ⟨1402727, by rfl⟩ : syracuseStep 1870303 = 2805455) B2805455
theorem B17525753 : Blo 1661530 17525753 := bstep (se 2 (by rfl) ⟨6572157, by rfl⟩ : syracuseStep 17525753 = 13144315) B13144315
theorem B17976617 : Blo 1661530 17976617 := bstep (se 2 (by rfl) ⟨6741231, by rfl⟩ : syracuseStep 17976617 = 13482463) B13482463
theorem B4206127 : Blo 1661530 4206127 := bstep (se 1 (by rfl) ⟨3154595, by rfl⟩ : syracuseStep 4206127 = 6309191) B6309191
theorem B92270501 : Blo 1661530 92270501 := bstep (se 4 (by rfl) ⟨8650359, by rfl⟩ : syracuseStep 92270501 = 17300719) B17300719
theorem B4494761 : Blo 1661530 4494761 := bstep (se 2 (by rfl) ⟨1685535, by rfl⟩ : syracuseStep 4494761 = 3371071) B3371071
theorem B72873847 : Blo 1661530 72873847 := bstep (se 1 (by rfl) ⟨54655385, by rfl⟩ : syracuseStep 72873847 = 109310771) B109310771
theorem B5611247 : Blo 1661530 5611247 := bstep (se 1 (by rfl) ⟨4208435, by rfl⟩ : syracuseStep 5611247 = 8416871) B8416871
theorem B1662823 : Blo 1661530 1662823 := bstep (se 1 (by rfl) ⟨1247117, by rfl⟩ : syracuseStep 1662823 = 2494235) B2494235
theorem B11683835 : Blo 1661530 11683835 := bstep (se 1 (by rfl) ⟨8762876, by rfl⟩ : syracuseStep 11683835 = 17525753) B17525753
theorem B2493737 : Blo 1661530 2493737 := bstep (se 2 (by rfl) ⟨935151, by rfl⟩ : syracuseStep 2493737 = 1870303) B1870303
theorem B5608169 : Blo 1661530 5608169 := bstep (se 2 (by rfl) ⟨2103063, by rfl⟩ : syracuseStep 5608169 = 4206127) B4206127
theorem B3740831 : Blo 1661530 3740831 := bstep (se 1 (by rfl) ⟨2805623, by rfl⟩ : syracuseStep 3740831 = 5611247) B5611247
theorem B76789073 : Blo 1661530 76789073 := bstep (se 2 (by rfl) ⟨28795902, by rfl⟩ : syracuseStep 76789073 = 57591805) B57591805
theorem B25581329 : Blo 1661530 25581329 := bstep (se 2 (by rfl) ⟨9592998, by rfl⟩ : syracuseStep 25581329 = 19185997) B19185997
theorem B2996507 : Blo 1661530 2996507 := bstep (se 1 (by rfl) ⟨2247380, by rfl⟩ : syracuseStep 2996507 = 4494761) B4494761
theorem B388660517 : Blo 1661530 388660517 := bstep (se 4 (by rfl) ⟨36436923, by rfl⟩ : syracuseStep 388660517 = 72873847) B72873847
theorem B11984411 : Blo 1661530 11984411 := bstep (se 1 (by rfl) ⟨8988308, by rfl⟩ : syracuseStep 11984411 = 17976617) B17976617
theorem B61513667 : Blo 1661530 61513667 := bstep (se 1 (by rfl) ⟨46135250, by rfl⟩ : syracuseStep 61513667 = 92270501) B92270501
theorem B259107011 : Blo 1661530 259107011 := bstep (se 1 (by rfl) ⟨194330258, by rfl⟩ : syracuseStep 259107011 = 388660517) B388660517
theorem B7989607 : Blo 1661530 7989607 := bstep (se 1 (by rfl) ⟨5992205, by rfl⟩ : syracuseStep 7989607 = 11984411) B11984411
theorem B3738779 : Blo 1661530 3738779 := bstep (se 1 (by rfl) ⟨2804084, by rfl⟩ : syracuseStep 3738779 = 5608169) B5608169
theorem B2493887 : Blo 1661530 2493887 := bstep (se 1 (by rfl) ⟨1870415, by rfl⟩ : syracuseStep 2493887 = 3740831) B3740831
theorem B204770861 : Blo 1661530 204770861 := bstep (se 3 (by rfl) ⟨38394536, by rfl⟩ : syracuseStep 204770861 = 76789073) B76789073
theorem B17054219 : Blo 1661530 17054219 := bstep (se 1 (by rfl) ⟨12790664, by rfl⟩ : syracuseStep 17054219 = 25581329) B25581329
theorem B7789223 : Blo 1661530 7789223 := bstep (se 1 (by rfl) ⟨5841917, by rfl⟩ : syracuseStep 7789223 = 11683835) B11683835
theorem B1997671 : Blo 1661530 1997671 := bstep (se 1 (by rfl) ⟨1498253, by rfl⟩ : syracuseStep 1997671 = 2996507) B2996507
theorem B1662491 : Blo 1661530 1662491 := bstep (se 1 (by rfl) ⟨1246868, by rfl⟩ : syracuseStep 1662491 = 2493737) B2493737
theorem B41009111 : Blo 1661530 41009111 := bstep (se 1 (by rfl) ⟨30756833, by rfl⟩ : syracuseStep 41009111 = 61513667) B61513667
theorem B2663561 : Blo 1661530 2663561 := bstep (se 2 (by rfl) ⟨998835, by rfl⟩ : syracuseStep 2663561 = 1997671) B1997671
theorem B172738007 : Blo 1661530 172738007 := bstep (se 1 (by rfl) ⟨129553505, by rfl⟩ : syracuseStep 172738007 = 259107011) B259107011
theorem B2492519 : Blo 1661530 2492519 := bstep (se 1 (by rfl) ⟨1869389, by rfl⟩ : syracuseStep 2492519 = 3738779) B3738779
theorem B136513907 : Blo 1661530 136513907 := bstep (se 1 (by rfl) ⟨102385430, by rfl⟩ : syracuseStep 136513907 = 204770861) B204770861
theorem B27339407 : Blo 1661530 27339407 := bstep (se 1 (by rfl) ⟨20504555, by rfl⟩ : syracuseStep 27339407 = 41009111) B41009111
theorem B10652809 : Blo 1661530 10652809 := bstep (se 2 (by rfl) ⟨3994803, by rfl⟩ : syracuseStep 10652809 = 7989607) B7989607
theorem B20771261 : Blo 1661530 20771261 := bstep (se 3 (by rfl) ⟨3894611, by rfl⟩ : syracuseStep 20771261 = 7789223) B7789223
theorem B11369479 : Blo 1661530 11369479 := bstep (se 1 (by rfl) ⟨8527109, by rfl⟩ : syracuseStep 11369479 = 17054219) B17054219
theorem B1662591 : Blo 1661530 1662591 := bstep (se 1 (by rfl) ⟨1246943, by rfl⟩ : syracuseStep 1662591 = 2493887) B2493887
theorem B7102829 : Blo 1661530 7102829 := bstep (se 3 (by rfl) ⟨1331780, by rfl⟩ : syracuseStep 7102829 = 2663561) B2663561
theorem B13847507 : Blo 1661530 13847507 := bstep (se 1 (by rfl) ⟨10385630, by rfl⟩ : syracuseStep 13847507 = 20771261) B20771261
theorem B115158671 : Blo 1661530 115158671 := bstep (se 1 (by rfl) ⟨86369003, by rfl⟩ : syracuseStep 115158671 = 172738007) B172738007
theorem B15159305 : Blo 1661530 15159305 := bstep (se 2 (by rfl) ⟨5684739, by rfl⟩ : syracuseStep 15159305 = 11369479) B11369479
theorem B91009271 : Blo 1661530 91009271 := bstep (se 1 (by rfl) ⟨68256953, by rfl⟩ : syracuseStep 91009271 = 136513907) B136513907
theorem B1661679 : Blo 1661530 1661679 := bstep (se 1 (by rfl) ⟨1246259, by rfl⟩ : syracuseStep 1661679 = 2492519) B2492519
theorem B14203745 : Blo 1661530 14203745 := bstep (se 2 (by rfl) ⟨5326404, by rfl⟩ : syracuseStep 14203745 = 10652809) B10652809
theorem B18226271 : Blo 1661530 18226271 := bstep (se 1 (by rfl) ⟨13669703, by rfl⟩ : syracuseStep 18226271 = 27339407) B27339407
theorem B18940877 : Blo 1661530 18940877 := bstep (se 3 (by rfl) ⟨3551414, by rfl⟩ : syracuseStep 18940877 = 7102829) B7102829
theorem B12150847 : Blo 1661530 12150847 := bstep (se 1 (by rfl) ⟨9113135, by rfl⟩ : syracuseStep 12150847 = 18226271) B18226271
theorem B60672847 : Blo 1661530 60672847 := bstep (se 1 (by rfl) ⟨45504635, by rfl⟩ : syracuseStep 60672847 = 91009271) B91009271
theorem B76772447 : Blo 1661530 76772447 := bstep (se 1 (by rfl) ⟨57579335, by rfl⟩ : syracuseStep 76772447 = 115158671) B115158671
theorem B10106203 : Blo 1661530 10106203 := bstep (se 1 (by rfl) ⟨7579652, by rfl⟩ : syracuseStep 10106203 = 15159305) B15159305
theorem B9469163 : Blo 1661530 9469163 := bstep (se 1 (by rfl) ⟨7101872, by rfl⟩ : syracuseStep 9469163 = 14203745) B14203745
theorem B9231671 : Blo 1661530 9231671 := bstep (se 1 (by rfl) ⟨6923753, by rfl⟩ : syracuseStep 9231671 = 13847507) B13847507
theorem B80897129 : Blo 1661530 80897129 := bstep (se 2 (by rfl) ⟨30336423, by rfl⟩ : syracuseStep 80897129 = 60672847) B60672847
theorem B6154447 : Blo 1661530 6154447 := bstep (se 1 (by rfl) ⟨4615835, by rfl⟩ : syracuseStep 6154447 = 9231671) B9231671
theorem B12627251 : Blo 1661530 12627251 := bstep (se 1 (by rfl) ⟨9470438, by rfl⟩ : syracuseStep 12627251 = 18940877) B18940877
theorem B6312775 : Blo 1661530 6312775 := bstep (se 1 (by rfl) ⟨4734581, by rfl⟩ : syracuseStep 6312775 = 9469163) B9469163
theorem B16201129 : Blo 1661530 16201129 := bstep (se 2 (by rfl) ⟨6075423, by rfl⟩ : syracuseStep 16201129 = 12150847) B12150847
theorem B51181631 : Blo 1661530 51181631 := bstep (se 1 (by rfl) ⟨38386223, by rfl⟩ : syracuseStep 51181631 = 76772447) B76772447
theorem B13474937 : Blo 1661530 13474937 := bstep (se 2 (by rfl) ⟨5053101, by rfl⟩ : syracuseStep 13474937 = 10106203) B10106203
theorem B34121087 : Blo 1661530 34121087 := bstep (se 1 (by rfl) ⟨25590815, by rfl⟩ : syracuseStep 34121087 = 51181631) B51181631
theorem B53931419 : Blo 1661530 53931419 := bstep (se 1 (by rfl) ⟨40448564, by rfl⟩ : syracuseStep 53931419 = 80897129) B80897129
theorem B8417033 : Blo 1661530 8417033 := bstep (se 2 (by rfl) ⟨3156387, by rfl⟩ : syracuseStep 8417033 = 6312775) B6312775
theorem B8983291 : Blo 1661530 8983291 := bstep (se 1 (by rfl) ⟨6737468, by rfl⟩ : syracuseStep 8983291 = 13474937) B13474937
theorem B8418167 : Blo 1661530 8418167 := bstep (se 1 (by rfl) ⟨6313625, by rfl⟩ : syracuseStep 8418167 = 12627251) B12627251
theorem B8205929 : Blo 1661530 8205929 := bstep (se 2 (by rfl) ⟨3077223, by rfl⟩ : syracuseStep 8205929 = 6154447) B6154447
theorem B21601505 : Blo 1661530 21601505 := bstep (se 2 (by rfl) ⟨8100564, by rfl⟩ : syracuseStep 21601505 = 16201129) B16201129
theorem B5612111 : Blo 1661530 5612111 := bstep (se 1 (by rfl) ⟨4209083, by rfl⟩ : syracuseStep 5612111 = 8418167) B8418167
theorem B11977721 : Blo 1661530 11977721 := bstep (se 2 (by rfl) ⟨4491645, by rfl⟩ : syracuseStep 11977721 = 8983291) B8983291
theorem B22747391 : Blo 1661530 22747391 := bstep (se 1 (by rfl) ⟨17060543, by rfl⟩ : syracuseStep 22747391 = 34121087) B34121087
theorem B87529909 : Blo 1661530 87529909 := bstep (se 5 (by rfl) ⟨4102964, by rfl⟩ : syracuseStep 87529909 = 8205929) B8205929
theorem B14401003 : Blo 1661530 14401003 := bstep (se 1 (by rfl) ⟨10800752, by rfl⟩ : syracuseStep 14401003 = 21601505) B21601505
theorem B35954279 : Blo 1661530 35954279 := bstep (se 1 (by rfl) ⟨26965709, by rfl⟩ : syracuseStep 35954279 = 53931419) B53931419
theorem B5611355 : Blo 1661530 5611355 := bstep (se 1 (by rfl) ⟨4208516, by rfl⟩ : syracuseStep 5611355 = 8417033) B8417033
theorem B15164927 : Blo 1661530 15164927 := bstep (se 1 (by rfl) ⟨11373695, by rfl⟩ : syracuseStep 15164927 = 22747391) B22747391
theorem B116706545 : Blo 1661530 116706545 := bstep (se 2 (by rfl) ⟨43764954, by rfl⟩ : syracuseStep 116706545 = 87529909) B87529909
theorem B3740903 : Blo 1661530 3740903 := bstep (se 1 (by rfl) ⟨2805677, by rfl⟩ : syracuseStep 3740903 = 5611355) B5611355
theorem B3741407 : Blo 1661530 3741407 := bstep (se 1 (by rfl) ⟨2806055, by rfl⟩ : syracuseStep 3741407 = 5612111) B5612111
theorem B7985147 : Blo 1661530 7985147 := bstep (se 1 (by rfl) ⟨5988860, by rfl⟩ : syracuseStep 7985147 = 11977721) B11977721
theorem B19201337 : Blo 1661530 19201337 := bstep (se 2 (by rfl) ⟨7200501, by rfl⟩ : syracuseStep 19201337 = 14401003) B14401003
theorem B23969519 : Blo 1661530 23969519 := bstep (se 1 (by rfl) ⟨17977139, by rfl⟩ : syracuseStep 23969519 = 35954279) B35954279
theorem B10109951 : Blo 1661530 10109951 := bstep (se 1 (by rfl) ⟨7582463, by rfl⟩ : syracuseStep 10109951 = 15164927) B15164927
theorem B21293725 : Blo 1661530 21293725 := bstep (se 3 (by rfl) ⟨3992573, by rfl⟩ : syracuseStep 21293725 = 7985147) B7985147
theorem B2493935 : Blo 1661530 2493935 := bstep (se 1 (by rfl) ⟨1870451, by rfl⟩ : syracuseStep 2493935 = 3740903) B3740903
theorem B2494271 : Blo 1661530 2494271 := bstep (se 1 (by rfl) ⟨1870703, by rfl⟩ : syracuseStep 2494271 = 3741407) B3741407
theorem B77804363 : Blo 1661530 77804363 := bstep (se 1 (by rfl) ⟨58353272, by rfl⟩ : syracuseStep 77804363 = 116706545) B116706545
theorem B12800891 : Blo 1661530 12800891 := bstep (se 1 (by rfl) ⟨9600668, by rfl⟩ : syracuseStep 12800891 = 19201337) B19201337
theorem B15979679 : Blo 1661530 15979679 := bstep (se 1 (by rfl) ⟨11984759, by rfl⟩ : syracuseStep 15979679 = 23969519) B23969519
theorem B10653119 : Blo 1661530 10653119 := bstep (se 1 (by rfl) ⟨7989839, by rfl⟩ : syracuseStep 10653119 = 15979679) B15979679
theorem B51869575 : Blo 1661530 51869575 := bstep (se 1 (by rfl) ⟨38902181, by rfl⟩ : syracuseStep 51869575 = 77804363) B77804363
theorem B8533927 : Blo 1661530 8533927 := bstep (se 1 (by rfl) ⟨6400445, by rfl⟩ : syracuseStep 8533927 = 12800891) B12800891
theorem B6739967 : Blo 1661530 6739967 := bstep (se 1 (by rfl) ⟨5054975, by rfl⟩ : syracuseStep 6739967 = 10109951) B10109951
theorem B28391633 : Blo 1661530 28391633 := bstep (se 2 (by rfl) ⟨10646862, by rfl⟩ : syracuseStep 28391633 = 21293725) B21293725
theorem B1662623 : Blo 1661530 1662623 := bstep (se 1 (by rfl) ⟨1246967, by rfl⟩ : syracuseStep 1662623 = 2493935) B2493935
theorem B1662847 : Blo 1661530 1662847 := bstep (se 1 (by rfl) ⟨1247135, by rfl⟩ : syracuseStep 1662847 = 2494271) B2494271
theorem B69159433 : Blo 1661530 69159433 := bstep (se 2 (by rfl) ⟨25934787, by rfl⟩ : syracuseStep 69159433 = 51869575) B51869575
theorem B18927755 : Blo 1661530 18927755 := bstep (se 1 (by rfl) ⟨14195816, by rfl⟩ : syracuseStep 18927755 = 28391633) B28391633
theorem B7102079 : Blo 1661530 7102079 := bstep (se 1 (by rfl) ⟨5326559, by rfl⟩ : syracuseStep 7102079 = 10653119) B10653119
theorem B11378569 : Blo 1661530 11378569 := bstep (se 2 (by rfl) ⟨4266963, by rfl⟩ : syracuseStep 11378569 = 8533927) B8533927
theorem B17973245 : Blo 1661530 17973245 := bstep (se 3 (by rfl) ⟨3369983, by rfl⟩ : syracuseStep 17973245 = 6739967) B6739967
theorem B12618503 : Blo 1661530 12618503 := bstep (se 1 (by rfl) ⟨9463877, by rfl⟩ : syracuseStep 12618503 = 18927755) B18927755
theorem B92212577 : Blo 1661530 92212577 := bstep (se 2 (by rfl) ⟨34579716, by rfl⟩ : syracuseStep 92212577 = 69159433) B69159433
theorem B11982163 : Blo 1661530 11982163 := bstep (se 1 (by rfl) ⟨8986622, by rfl⟩ : syracuseStep 11982163 = 17973245) B17973245
theorem B4734719 : Blo 1661530 4734719 := bstep (se 1 (by rfl) ⟨3551039, by rfl⟩ : syracuseStep 4734719 = 7102079) B7102079
theorem B15171425 : Blo 1661530 15171425 := bstep (se 2 (by rfl) ⟨5689284, by rfl⟩ : syracuseStep 15171425 = 11378569) B11378569
theorem B15976217 : Blo 1661530 15976217 := bstep (se 2 (by rfl) ⟨5991081, by rfl⟩ : syracuseStep 15976217 = 11982163) B11982163
theorem B61475051 : Blo 1661530 61475051 := bstep (se 1 (by rfl) ⟨46106288, by rfl⟩ : syracuseStep 61475051 = 92212577) B92212577
theorem B3156479 : Blo 1661530 3156479 := bstep (se 1 (by rfl) ⟨2367359, by rfl⟩ : syracuseStep 3156479 = 4734719) B4734719
theorem B10114283 : Blo 1661530 10114283 := bstep (se 1 (by rfl) ⟨7585712, by rfl⟩ : syracuseStep 10114283 = 15171425) B15171425
theorem B8412335 : Blo 1661530 8412335 := bstep (se 1 (by rfl) ⟨6309251, by rfl⟩ : syracuseStep 8412335 = 12618503) B12618503
theorem B6742855 : Blo 1661530 6742855 := bstep (se 1 (by rfl) ⟨5057141, by rfl⟩ : syracuseStep 6742855 = 10114283) B10114283
theorem B10650811 : Blo 1661530 10650811 := bstep (se 1 (by rfl) ⟨7988108, by rfl⟩ : syracuseStep 10650811 = 15976217) B15976217
theorem B5608223 : Blo 1661530 5608223 := bstep (se 1 (by rfl) ⟨4206167, by rfl⟩ : syracuseStep 5608223 = 8412335) B8412335
theorem B40983367 : Blo 1661530 40983367 := bstep (se 1 (by rfl) ⟨30737525, by rfl⟩ : syracuseStep 40983367 = 61475051) B61475051
theorem B2104319 : Blo 1661530 2104319 := bstep (se 1 (by rfl) ⟨1578239, by rfl⟩ : syracuseStep 2104319 = 3156479) B3156479
theorem B3738815 : Blo 1661530 3738815 := bstep (se 1 (by rfl) ⟨2804111, by rfl⟩ : syracuseStep 3738815 = 5608223) B5608223
theorem B5611517 : Blo 1661530 5611517 := bstep (se 3 (by rfl) ⟨1052159, by rfl⟩ : syracuseStep 5611517 = 2104319) B2104319
theorem B54644489 : Blo 1661530 54644489 := bstep (se 2 (by rfl) ⟨20491683, by rfl⟩ : syracuseStep 54644489 = 40983367) B40983367
theorem B8990473 : Blo 1661530 8990473 := bstep (se 2 (by rfl) ⟨3371427, by rfl⟩ : syracuseStep 8990473 = 6742855) B6742855
theorem B14201081 : Blo 1661530 14201081 := bstep (se 2 (by rfl) ⟨5325405, by rfl⟩ : syracuseStep 14201081 = 10650811) B10650811
theorem B2492543 : Blo 1661530 2492543 := bstep (se 1 (by rfl) ⟨1869407, by rfl⟩ : syracuseStep 2492543 = 3738815) B3738815
theorem B11987297 : Blo 1661530 11987297 := bstep (se 2 (by rfl) ⟨4495236, by rfl⟩ : syracuseStep 11987297 = 8990473) B8990473
theorem B3741011 : Blo 1661530 3741011 := bstep (se 1 (by rfl) ⟨2805758, by rfl⟩ : syracuseStep 3741011 = 5611517) B5611517
theorem B9467387 : Blo 1661530 9467387 := bstep (se 1 (by rfl) ⟨7100540, by rfl⟩ : syracuseStep 9467387 = 14201081) B14201081
theorem B36429659 : Blo 1661530 36429659 := bstep (se 1 (by rfl) ⟨27322244, by rfl⟩ : syracuseStep 36429659 = 54644489) B54644489
theorem B2494007 : Blo 1661530 2494007 := bstep (se 1 (by rfl) ⟨1870505, by rfl⟩ : syracuseStep 2494007 = 3741011) B3741011
theorem B6311591 : Blo 1661530 6311591 := bstep (se 1 (by rfl) ⟨4733693, by rfl⟩ : syracuseStep 6311591 = 9467387) B9467387
theorem B7991531 : Blo 1661530 7991531 := bstep (se 1 (by rfl) ⟨5993648, by rfl⟩ : syracuseStep 7991531 = 11987297) B11987297
theorem B24286439 : Blo 1661530 24286439 := bstep (se 1 (by rfl) ⟨18214829, by rfl⟩ : syracuseStep 24286439 = 36429659) B36429659
theorem B1661695 : Blo 1661530 1661695 := bstep (se 1 (by rfl) ⟨1246271, by rfl⟩ : syracuseStep 1661695 = 2492543) B2492543
theorem B5327687 : Blo 1661530 5327687 := bstep (se 1 (by rfl) ⟨3995765, by rfl⟩ : syracuseStep 5327687 = 7991531) B7991531
theorem B4207727 : Blo 1661530 4207727 := bstep (se 1 (by rfl) ⟨3155795, by rfl⟩ : syracuseStep 4207727 = 6311591) B6311591
theorem B64763837 : Blo 1661530 64763837 := bstep (se 3 (by rfl) ⟨12143219, by rfl⟩ : syracuseStep 64763837 = 24286439) B24286439
theorem B1662671 : Blo 1661530 1662671 := bstep (se 1 (by rfl) ⟨1247003, by rfl⟩ : syracuseStep 1662671 = 2494007) B2494007
theorem B2805151 : Blo 1661530 2805151 := bstep (se 1 (by rfl) ⟨2103863, by rfl⟩ : syracuseStep 2805151 = 4207727) B4207727
theorem B43175891 : Blo 1661530 43175891 := bstep (se 1 (by rfl) ⟨32381918, by rfl⟩ : syracuseStep 43175891 = 64763837) B64763837
theorem B3551791 : Blo 1661530 3551791 := bstep (se 1 (by rfl) ⟨2663843, by rfl⟩ : syracuseStep 3551791 = 5327687) B5327687
theorem B4735721 : Blo 1661530 4735721 := bstep (se 2 (by rfl) ⟨1775895, by rfl⟩ : syracuseStep 4735721 = 3551791) B3551791
theorem B3740201 : Blo 1661530 3740201 := bstep (se 2 (by rfl) ⟨1402575, by rfl⟩ : syracuseStep 3740201 = 2805151) B2805151
theorem B28783927 : Blo 1661530 28783927 := bstep (se 1 (by rfl) ⟨21587945, by rfl⟩ : syracuseStep 28783927 = 43175891) B43175891
theorem B2493467 : Blo 1661530 2493467 := bstep (se 1 (by rfl) ⟨1870100, by rfl⟩ : syracuseStep 2493467 = 3740201) B3740201
theorem B3157147 : Blo 1661530 3157147 := bstep (se 1 (by rfl) ⟨2367860, by rfl⟩ : syracuseStep 3157147 = 4735721) B4735721
theorem B38378569 : Blo 1661530 38378569 := bstep (se 2 (by rfl) ⟨14391963, by rfl⟩ : syracuseStep 38378569 = 28783927) B28783927
theorem B51171425 : Blo 1661530 51171425 := bstep (se 2 (by rfl) ⟨19189284, by rfl⟩ : syracuseStep 51171425 = 38378569) B38378569
theorem B4209529 : Blo 1661530 4209529 := bstep (se 2 (by rfl) ⟨1578573, by rfl⟩ : syracuseStep 4209529 = 3157147) B3157147
theorem B1662311 : Blo 1661530 1662311 := bstep (se 1 (by rfl) ⟨1246733, by rfl⟩ : syracuseStep 1662311 = 2493467) B2493467
theorem B5612705 : Blo 1661530 5612705 := bstep (se 2 (by rfl) ⟨2104764, by rfl⟩ : syracuseStep 5612705 = 4209529) B4209529
theorem B34114283 : Blo 1661530 34114283 := bstep (se 1 (by rfl) ⟨25585712, by rfl⟩ : syracuseStep 34114283 = 51171425) B51171425
theorem B22742855 : Blo 1661530 22742855 := bstep (se 1 (by rfl) ⟨17057141, by rfl⟩ : syracuseStep 22742855 = 34114283) B34114283
theorem B3741803 : Blo 1661530 3741803 := bstep (se 1 (by rfl) ⟨2806352, by rfl⟩ : syracuseStep 3741803 = 5612705) B5612705
theorem B2494535 : Blo 1661530 2494535 := bstep (se 1 (by rfl) ⟨1870901, by rfl⟩ : syracuseStep 2494535 = 3741803) B3741803
theorem B15161903 : Blo 1661530 15161903 := bstep (se 1 (by rfl) ⟨11371427, by rfl⟩ : syracuseStep 15161903 = 22742855) B22742855
theorem B1663023 : Blo 1661530 1663023 := bstep (se 1 (by rfl) ⟨1247267, by rfl⟩ : syracuseStep 1663023 = 2494535) B2494535
theorem B10107935 : Blo 1661530 10107935 := bstep (se 1 (by rfl) ⟨7580951, by rfl⟩ : syracuseStep 10107935 = 15161903) B15161903
theorem B6738623 : Blo 1661530 6738623 := bstep (se 1 (by rfl) ⟨5053967, by rfl⟩ : syracuseStep 6738623 = 10107935) B10107935
theorem B4492415 : Blo 1661530 4492415 := bstep (se 1 (by rfl) ⟨3369311, by rfl⟩ : syracuseStep 4492415 = 6738623) B6738623
theorem B2994943 : Blo 1661530 2994943 := bstep (se 1 (by rfl) ⟨2246207, by rfl⟩ : syracuseStep 2994943 = 4492415) B4492415
theorem B3993257 : Blo 1661530 3993257 := bstep (se 2 (by rfl) ⟨1497471, by rfl⟩ : syracuseStep 3993257 = 2994943) B2994943
theorem B10648685 : Blo 1661530 10648685 := bstep (se 3 (by rfl) ⟨1996628, by rfl⟩ : syracuseStep 10648685 = 3993257) B3993257
theorem B7099123 : Blo 1661530 7099123 := bstep (se 1 (by rfl) ⟨5324342, by rfl⟩ : syracuseStep 7099123 = 10648685) B10648685
theorem B9465497 : Blo 1661530 9465497 := bstep (se 2 (by rfl) ⟨3549561, by rfl⟩ : syracuseStep 9465497 = 7099123) B7099123
theorem B6310331 : Blo 1661530 6310331 := bstep (se 1 (by rfl) ⟨4732748, by rfl⟩ : syracuseStep 6310331 = 9465497) B9465497
theorem B4206887 : Blo 1661530 4206887 := bstep (se 1 (by rfl) ⟨3155165, by rfl⟩ : syracuseStep 4206887 = 6310331) B6310331
theorem B2804591 : Blo 1661530 2804591 := bstep (se 1 (by rfl) ⟨2103443, by rfl⟩ : syracuseStep 2804591 = 4206887) B4206887
theorem B1869727 : Blo 1661530 1869727 := bstep (se 1 (by rfl) ⟨1402295, by rfl⟩ : syracuseStep 1869727 = 2804591) B2804591
theorem B2492969 : Blo 1661530 2492969 := bstep (se 2 (by rfl) ⟨934863, by rfl⟩ : syracuseStep 2492969 = 1869727) B1869727
theorem B1661979 : Blo 1661530 1661979 := bstep (se 1 (by rfl) ⟨1246484, by rfl⟩ : syracuseStep 1661979 = 2492969) B2492969

theorem C0 (j : ℕ) (h1 : 415382 ≤ j) (h2 : j ≤ 415756) : Blo 1661530 (4 * j + 3) := by
  interval_cases j
  · exact B1661531
  · exact B1661535
  · exact B1661539
  · exact B1661543
  · exact B1661547
  · exact B1661551
  · exact B1661555
  · exact B1661559
  · exact B1661563
  · exact B1661567
  · exact B1661571
  · exact B1661575
  · exact B1661579
  · exact B1661583
  · exact B1661587
  · exact B1661591
  · exact B1661595
  · exact B1661599
  · exact B1661603
  · exact B1661607
  · exact B1661611
  · exact B1661615
  · exact B1661619
  · exact B1661623
  · exact B1661627
  · exact B1661631
  · exact B1661635
  · exact B1661639
  · exact B1661643
  · exact B1661647
  · exact B1661651
  · exact B1661655
  · exact B1661659
  · exact B1661663
  · exact B1661667
  · exact B1661671
  · exact B1661675
  · exact B1661679
  · exact B1661683
  · exact B1661687
  · exact B1661691
  · exact B1661695
  · exact B1661699
  · exact B1661703
  · exact B1661707
  · exact B1661711
  · exact B1661715
  · exact B1661719
  · exact B1661723
  · exact B1661727
  · exact B1661731
  · exact B1661735
  · exact B1661739
  · exact B1661743
  · exact B1661747
  · exact B1661751
  · exact B1661755
  · exact B1661759
  · exact B1661763
  · exact B1661767
  · exact B1661771
  · exact B1661775
  · exact B1661779
  · exact B1661783
  · exact B1661787
  · exact B1661791
  · exact B1661795
  · exact B1661799
  · exact B1661803
  · exact B1661807
  · exact B1661811
  · exact B1661815
  · exact B1661819
  · exact B1661823
  · exact B1661827
  · exact B1661831
  · exact B1661835
  · exact B1661839
  · exact B1661843
  · exact B1661847
  · exact B1661851
  · exact B1661855
  · exact B1661859
  · exact B1661863
  · exact B1661867
  · exact B1661871
  · exact B1661875
  · exact B1661879
  · exact B1661883
  · exact B1661887
  · exact B1661891
  · exact B1661895
  · exact B1661899
  · exact B1661903
  · exact B1661907
  · exact B1661911
  · exact B1661915
  · exact B1661919
  · exact B1661923
  · exact B1661927
  · exact B1661931
  · exact B1661935
  · exact B1661939
  · exact B1661943
  · exact B1661947
  · exact B1661951
  · exact B1661955
  · exact B1661959
  · exact B1661963
  · exact B1661967
  · exact B1661971
  · exact B1661975
  · exact B1661979
  · exact B1661983
  · exact B1661987
  · exact B1661991
  · exact B1661995
  · exact B1661999
  · exact B1662003
  · exact B1662007
  · exact B1662011
  · exact B1662015
  · exact B1662019
  · exact B1662023
  · exact B1662027
  · exact B1662031
  · exact B1662035
  · exact B1662039
  · exact B1662043
  · exact B1662047
  · exact B1662051
  · exact B1662055
  · exact B1662059
  · exact B1662063
  · exact B1662067
  · exact B1662071
  · exact B1662075
  · exact B1662079
  · exact B1662083
  · exact B1662087
  · exact B1662091
  · exact B1662095
  · exact B1662099
  · exact B1662103
  · exact B1662107
  · exact B1662111
  · exact B1662115
  · exact B1662119
  · exact B1662123
  · exact B1662127
  · exact B1662131
  · exact B1662135
  · exact B1662139
  · exact B1662143
  · exact B1662147
  · exact B1662151
  · exact B1662155
  · exact B1662159
  · exact B1662163
  · exact B1662167
  · exact B1662171
  · exact B1662175
  · exact B1662179
  · exact B1662183
  · exact B1662187
  · exact B1662191
  · exact B1662195
  · exact B1662199
  · exact B1662203
  · exact B1662207
  · exact B1662211
  · exact B1662215
  · exact B1662219
  · exact B1662223
  · exact B1662227
  · exact B1662231
  · exact B1662235
  · exact B1662239
  · exact B1662243
  · exact B1662247
  · exact B1662251
  · exact B1662255
  · exact B1662259
  · exact B1662263
  · exact B1662267
  · exact B1662271
  · exact B1662275
  · exact B1662279
  · exact B1662283
  · exact B1662287
  · exact B1662291
  · exact B1662295
  · exact B1662299
  · exact B1662303
  · exact B1662307
  · exact B1662311
  · exact B1662315
  · exact B1662319
  · exact B1662323
  · exact B1662327
  · exact B1662331
  · exact B1662335
  · exact B1662339
  · exact B1662343
  · exact B1662347
  · exact B1662351
  · exact B1662355
  · exact B1662359
  · exact B1662363
  · exact B1662367
  · exact B1662371
  · exact B1662375
  · exact B1662379
  · exact B1662383
  · exact B1662387
  · exact B1662391
  · exact B1662395
  · exact B1662399
  · exact B1662403
  · exact B1662407
  · exact B1662411
  · exact B1662415
  · exact B1662419
  · exact B1662423
  · exact B1662427
  · exact B1662431
  · exact B1662435
  · exact B1662439
  · exact B1662443
  · exact B1662447
  · exact B1662451
  · exact B1662455
  · exact B1662459
  · exact B1662463
  · exact B1662467
  · exact B1662471
  · exact B1662475
  · exact B1662479
  · exact B1662483
  · exact B1662487
  · exact B1662491
  · exact B1662495
  · exact B1662499
  · exact B1662503
  · exact B1662507
  · exact B1662511
  · exact B1662515
  · exact B1662519
  · exact B1662523
  · exact B1662527
  · exact B1662531
  · exact B1662535
  · exact B1662539
  · exact B1662543
  · exact B1662547
  · exact B1662551
  · exact B1662555
  · exact B1662559
  · exact B1662563
  · exact B1662567
  · exact B1662571
  · exact B1662575
  · exact B1662579
  · exact B1662583
  · exact B1662587
  · exact B1662591
  · exact B1662595
  · exact B1662599
  · exact B1662603
  · exact B1662607
  · exact B1662611
  · exact B1662615
  · exact B1662619
  · exact B1662623
  · exact B1662627
  · exact B1662631
  · exact B1662635
  · exact B1662639
  · exact B1662643
  · exact B1662647
  · exact B1662651
  · exact B1662655
  · exact B1662659
  · exact B1662663
  · exact B1662667
  · exact B1662671
  · exact B1662675
  · exact B1662679
  · exact B1662683
  · exact B1662687
  · exact B1662691
  · exact B1662695
  · exact B1662699
  · exact B1662703
  · exact B1662707
  · exact B1662711
  · exact B1662715
  · exact B1662719
  · exact B1662723
  · exact B1662727
  · exact B1662731
  · exact B1662735
  · exact B1662739
  · exact B1662743
  · exact B1662747
  · exact B1662751
  · exact B1662755
  · exact B1662759
  · exact B1662763
  · exact B1662767
  · exact B1662771
  · exact B1662775
  · exact B1662779
  · exact B1662783
  · exact B1662787
  · exact B1662791
  · exact B1662795
  · exact B1662799
  · exact B1662803
  · exact B1662807
  · exact B1662811
  · exact B1662815
  · exact B1662819
  · exact B1662823
  · exact B1662827
  · exact B1662831
  · exact B1662835
  · exact B1662839
  · exact B1662843
  · exact B1662847
  · exact B1662851
  · exact B1662855
  · exact B1662859
  · exact B1662863
  · exact B1662867
  · exact B1662871
  · exact B1662875
  · exact B1662879
  · exact B1662883
  · exact B1662887
  · exact B1662891
  · exact B1662895
  · exact B1662899
  · exact B1662903
  · exact B1662907
  · exact B1662911
  · exact B1662915
  · exact B1662919
  · exact B1662923
  · exact B1662927
  · exact B1662931
  · exact B1662935
  · exact B1662939
  · exact B1662943
  · exact B1662947
  · exact B1662951
  · exact B1662955
  · exact B1662959
  · exact B1662963
  · exact B1662967
  · exact B1662971
  · exact B1662975
  · exact B1662979
  · exact B1662983
  · exact B1662987
  · exact B1662991
  · exact B1662995
  · exact B1662999
  · exact B1663003
  · exact B1663007
  · exact B1663011
  · exact B1663015
  · exact B1663019
  · exact B1663023
  · exact B1663027

theorem solution (m : ℕ) (hlo : 1661530 ≤ m) (hhi : m ≤ 1663030) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 415382 ≤ j := by omega
    have hj2 : j ≤ 415756 := by omega
    have hb : Blo 1661530 (4 * j + 3) := by
      exact C0 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
