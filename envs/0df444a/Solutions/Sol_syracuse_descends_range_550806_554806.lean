-- Prove2me | solution 1 for syracuse_descends_range_550806_554806
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-09T18:22:31.604809+00:00
-- url     : https://prove2.me/submissions/4a47639c-03dd-4eca-bd7a-dec8ece8e975

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


theorem B622597 : Blo 550806 622597 := bbase (se 4 (by rfl) ⟨58368, by rfl⟩ : syracuseStep 622597 = 116737) (by norm_num)
theorem B589837 : Blo 550806 589837 := bbase (se 3 (by rfl) ⟨110594, by rfl⟩ : syracuseStep 589837 = 221189) (by norm_num)
theorem B1245221 : Blo 550806 1245221 := bbase (se 4 (by rfl) ⟨116739, by rfl⟩ : syracuseStep 1245221 = 233479) (by norm_num)
theorem B622633 : Blo 550806 622633 := bbase (se 2 (by rfl) ⟨233487, by rfl⟩ : syracuseStep 622633 = 466975) (by norm_num)
theorem B1048621 : Blo 550806 1048621 := bbase (se 3 (by rfl) ⟨196616, by rfl⟩ : syracuseStep 1048621 = 393233) (by norm_num)
theorem B1998901 : Blo 550806 1998901 := bbase (se 5 (by rfl) ⟨93698, by rfl⟩ : syracuseStep 1998901 = 187397) (by norm_num)
theorem B622669 : Blo 550806 622669 := bbase (se 3 (by rfl) ⟨116750, by rfl⟩ : syracuseStep 622669 = 233501) (by norm_num)
theorem B1245293 : Blo 550806 1245293 := bbase (se 3 (by rfl) ⟨233492, by rfl⟩ : syracuseStep 1245293 = 466985) (by norm_num)
theorem B622705 : Blo 550806 622705 := bbase (se 2 (by rfl) ⟨233514, by rfl⟩ : syracuseStep 622705 = 467029) (by norm_num)
theorem B786557 : Blo 550806 786557 := bbase (se 3 (by rfl) ⟨147479, by rfl⟩ : syracuseStep 786557 = 294959) (by norm_num)
theorem B622741 : Blo 550806 622741 := bbase (se 6 (by rfl) ⟨14595, by rfl⟩ : syracuseStep 622741 = 29191) (by norm_num)
theorem B1245365 : Blo 550806 1245365 := bbase (se 5 (by rfl) ⟨58376, by rfl⟩ : syracuseStep 1245365 = 116753) (by norm_num)
theorem B622777 : Blo 550806 622777 := bbase (se 2 (by rfl) ⟨233541, by rfl⟩ : syracuseStep 622777 = 467083) (by norm_num)
theorem B1048781 : Blo 550806 1048781 := bbase (se 3 (by rfl) ⟨196646, by rfl⟩ : syracuseStep 1048781 = 393293) (by norm_num)
theorem B622813 : Blo 550806 622813 := bbase (se 3 (by rfl) ⟨116777, by rfl⟩ : syracuseStep 622813 = 233555) (by norm_num)
theorem B1868021 : Blo 550806 1868021 := bbase (se 5 (by rfl) ⟨87563, by rfl⟩ : syracuseStep 1868021 = 175127) (by norm_num)
theorem B1245437 : Blo 550806 1245437 := bbase (se 3 (by rfl) ⟨233519, by rfl⟩ : syracuseStep 1245437 = 467039) (by norm_num)
theorem B622849 : Blo 550806 622849 := bbase (se 2 (by rfl) ⟨233568, by rfl⟩ : syracuseStep 622849 = 467137) (by norm_num)
theorem B622885 : Blo 550806 622885 := bbase (se 4 (by rfl) ⟨58395, by rfl⟩ : syracuseStep 622885 = 116791) (by norm_num)
theorem B1245509 : Blo 550806 1245509 := bbase (se 4 (by rfl) ⟨116766, by rfl⟩ : syracuseStep 1245509 = 233533) (by norm_num)
theorem B622921 : Blo 550806 622921 := bbase (se 2 (by rfl) ⟨233595, by rfl⟩ : syracuseStep 622921 = 467191) (by norm_num)
theorem B2359637 : Blo 550806 2359637 := bbase (se 10 (by rfl) ⟨3456, by rfl⟩ : syracuseStep 2359637 = 6913) (by norm_num)
theorem B1048925 : Blo 550806 1048925 := bbase (se 3 (by rfl) ⟨196673, by rfl⟩ : syracuseStep 1048925 = 393347) (by norm_num)
theorem B622957 : Blo 550806 622957 := bbase (se 3 (by rfl) ⟨116804, by rfl⟩ : syracuseStep 622957 = 233609) (by norm_num)
theorem B590213 : Blo 550806 590213 := bbase (se 4 (by rfl) ⟨55332, by rfl⟩ : syracuseStep 590213 = 110665) (by norm_num)
theorem B1245581 : Blo 550806 1245581 := bbase (se 3 (by rfl) ⟨233546, by rfl⟩ : syracuseStep 1245581 = 467093) (by norm_num)
theorem B622993 : Blo 550806 622993 := bbase (se 2 (by rfl) ⟨233622, by rfl⟩ : syracuseStep 622993 = 467245) (by norm_num)
theorem B623029 : Blo 550806 623029 := bbase (se 5 (by rfl) ⟨29204, by rfl⟩ : syracuseStep 623029 = 58409) (by norm_num)
theorem B1180109 : Blo 550806 1180109 := bbase (se 3 (by rfl) ⟨221270, by rfl⟩ : syracuseStep 1180109 = 442541) (by norm_num)
theorem B590285 : Blo 550806 590285 := bbase (se 3 (by rfl) ⟨110678, by rfl⟩ : syracuseStep 590285 = 221357) (by norm_num)
theorem B5374421 : Blo 550806 5374421 := bbase (se 7 (by rfl) ⟨62981, by rfl⟩ : syracuseStep 5374421 = 125963) (by norm_num)
theorem B1245653 : Blo 550806 1245653 := bbase (se 7 (by rfl) ⟨14597, by rfl⟩ : syracuseStep 1245653 = 29195) (by norm_num)
theorem B623065 : Blo 550806 623065 := bbase (se 2 (by rfl) ⟨233649, by rfl⟩ : syracuseStep 623065 = 467299) (by norm_num)
theorem B623101 : Blo 550806 623101 := bbase (se 3 (by rfl) ⟨116831, by rfl⟩ : syracuseStep 623101 = 233663) (by norm_num)
theorem B1245725 : Blo 550806 1245725 := bbase (se 3 (by rfl) ⟨233573, by rfl⟩ : syracuseStep 1245725 = 467147) (by norm_num)
theorem B623137 : Blo 550806 623137 := bbase (se 2 (by rfl) ⟨233676, by rfl⟩ : syracuseStep 623137 = 467353) (by norm_num)
theorem B1573445 : Blo 550806 1573445 := bbase (se 4 (by rfl) ⟨147510, by rfl⟩ : syracuseStep 1573445 = 295021) (by norm_num)
theorem B623173 : Blo 550806 623173 := bbase (se 4 (by rfl) ⟨58422, by rfl⟩ : syracuseStep 623173 = 116845) (by norm_num)
theorem B1245797 : Blo 550806 1245797 := bbase (se 4 (by rfl) ⟨116793, by rfl⟩ : syracuseStep 1245797 = 233587) (by norm_num)
theorem B623209 : Blo 550806 623209 := bbase (se 2 (by rfl) ⟨233703, by rfl⟩ : syracuseStep 623209 = 467407) (by norm_num)
theorem B1049213 : Blo 550806 1049213 := bbase (se 3 (by rfl) ⟨196727, by rfl⟩ : syracuseStep 1049213 = 393455) (by norm_num)
theorem B590473 : Blo 550806 590473 := bbase (se 2 (by rfl) ⟨221427, by rfl⟩ : syracuseStep 590473 = 442855) (by norm_num)
theorem B623245 : Blo 550806 623245 := bbase (se 3 (by rfl) ⟨116858, by rfl⟩ : syracuseStep 623245 = 233717) (by norm_num)
theorem B1868453 : Blo 550806 1868453 := bbase (se 4 (by rfl) ⟨175167, by rfl⟩ : syracuseStep 1868453 = 350335) (by norm_num)
theorem B1245869 : Blo 550806 1245869 := bbase (se 3 (by rfl) ⟨233600, by rfl⟩ : syracuseStep 1245869 = 467201) (by norm_num)
theorem B623281 : Blo 550806 623281 := bbase (se 2 (by rfl) ⟨233730, by rfl⟩ : syracuseStep 623281 = 467461) (by norm_num)
theorem B623317 : Blo 550806 623317 := bbase (se 7 (by rfl) ⟨7304, by rfl⟩ : syracuseStep 623317 = 14609) (by norm_num)
theorem B1245941 : Blo 550806 1245941 := bbase (se 5 (by rfl) ⟨58403, by rfl⟩ : syracuseStep 1245941 = 116807) (by norm_num)
theorem B1442549 : Blo 550806 1442549 := bbase (se 5 (by rfl) ⟨67619, by rfl⟩ : syracuseStep 1442549 = 135239) (by norm_num)
theorem B623353 : Blo 550806 623353 := bbase (se 2 (by rfl) ⟨233757, by rfl⟩ : syracuseStep 623353 = 467515) (by norm_num)
theorem B1049365 : Blo 550806 1049365 := bbase (se 6 (by rfl) ⟨24594, by rfl⟩ : syracuseStep 1049365 = 49189) (by norm_num)
theorem B623389 : Blo 550806 623389 := bbase (se 3 (by rfl) ⟨116885, by rfl⟩ : syracuseStep 623389 = 233771) (by norm_num)
theorem B1246013 : Blo 550806 1246013 := bbase (se 3 (by rfl) ⟨233627, by rfl⟩ : syracuseStep 1246013 = 467255) (by norm_num)
theorem B590657 : Blo 550806 590657 := bbase (se 2 (by rfl) ⟨221496, by rfl⟩ : syracuseStep 590657 = 442993) (by norm_num)
theorem B623425 : Blo 550806 623425 := bbase (se 2 (by rfl) ⟨233784, by rfl⟩ : syracuseStep 623425 = 467569) (by norm_num)
theorem B623461 : Blo 550806 623461 := bbase (se 4 (by rfl) ⟨58449, by rfl⟩ : syracuseStep 623461 = 116899) (by norm_num)
theorem B1246085 : Blo 550806 1246085 := bbase (se 4 (by rfl) ⟨116820, by rfl⟩ : syracuseStep 1246085 = 233641) (by norm_num)
theorem B623497 : Blo 550806 623497 := bbase (se 2 (by rfl) ⟨233811, by rfl⟩ : syracuseStep 623497 = 467623) (by norm_num)
theorem B10617749 : Blo 550806 10617749 := bbase (se 6 (by rfl) ⟨248853, by rfl⟩ : syracuseStep 10617749 = 497707) (by norm_num)
theorem B623533 : Blo 550806 623533 := bbase (se 3 (by rfl) ⟨116912, by rfl⟩ : syracuseStep 623533 = 233825) (by norm_num)
theorem B1246157 : Blo 550806 1246157 := bbase (se 3 (by rfl) ⟨233654, by rfl⟩ : syracuseStep 1246157 = 467309) (by norm_num)
theorem B623569 : Blo 550806 623569 := bbase (se 2 (by rfl) ⟨233838, by rfl⟩ : syracuseStep 623569 = 467677) (by norm_num)
theorem B623605 : Blo 550806 623605 := bbase (se 5 (by rfl) ⟨29231, by rfl⟩ : syracuseStep 623605 = 58463) (by norm_num)
theorem B1246229 : Blo 550806 1246229 := bbase (se 6 (by rfl) ⟨29208, by rfl⟩ : syracuseStep 1246229 = 58417) (by norm_num)
theorem B623641 : Blo 550806 623641 := bbase (se 2 (by rfl) ⟨233865, by rfl⟩ : syracuseStep 623641 = 467731) (by norm_num)
theorem B623677 : Blo 550806 623677 := bbase (se 3 (by rfl) ⟨116939, by rfl⟩ : syracuseStep 623677 = 233879) (by norm_num)
theorem B1049669 : Blo 550806 1049669 := bbase (se 4 (by rfl) ⟨98406, by rfl⟩ : syracuseStep 1049669 = 196813) (by norm_num)
theorem B1868885 : Blo 550806 1868885 := bbase (se 8 (by rfl) ⟨10950, by rfl⟩ : syracuseStep 1868885 = 21901) (by norm_num)
theorem B1246301 : Blo 550806 1246301 := bbase (se 3 (by rfl) ⟨233681, by rfl⟩ : syracuseStep 1246301 = 467363) (by norm_num)
theorem B623713 : Blo 550806 623713 := bbase (se 2 (by rfl) ⟨233892, by rfl⟩ : syracuseStep 623713 = 467785) (by norm_num)
theorem B623749 : Blo 550806 623749 := bbase (se 4 (by rfl) ⟨58476, by rfl⟩ : syracuseStep 623749 = 116953) (by norm_num)
theorem B1246373 : Blo 550806 1246373 := bbase (se 4 (by rfl) ⟨116847, by rfl⟩ : syracuseStep 1246373 = 233695) (by norm_num)
theorem B623785 : Blo 550806 623785 := bbase (se 2 (by rfl) ⟨233919, by rfl⟩ : syracuseStep 623785 = 467839) (by norm_num)
theorem B623821 : Blo 550806 623821 := bbase (se 3 (by rfl) ⟨116966, by rfl⟩ : syracuseStep 623821 = 233933) (by norm_num)
theorem B1574117 : Blo 550806 1574117 := bbase (se 4 (by rfl) ⟨147573, by rfl⟩ : syracuseStep 1574117 = 295147) (by norm_num)
theorem B1246445 : Blo 550806 1246445 := bbase (se 3 (by rfl) ⟨233708, by rfl⟩ : syracuseStep 1246445 = 467417) (by norm_num)
theorem B623857 : Blo 550806 623857 := bbase (se 2 (by rfl) ⟨233946, by rfl⟩ : syracuseStep 623857 = 467893) (by norm_num)
theorem B623893 : Blo 550806 623893 := bbase (se 6 (by rfl) ⟨14622, by rfl⟩ : syracuseStep 623893 = 29245) (by norm_num)
theorem B1180973 : Blo 550806 1180973 := bbase (se 3 (by rfl) ⟨221432, by rfl⟩ : syracuseStep 1180973 = 442865) (by norm_num)
theorem B4195637 : Blo 550806 4195637 := bbase (se 5 (by rfl) ⟨196670, by rfl⟩ : syracuseStep 4195637 = 393341) (by norm_num)
theorem B886069 : Blo 550806 886069 := bbase (se 5 (by rfl) ⟨41534, by rfl⟩ : syracuseStep 886069 = 83069) (by norm_num)
theorem B1246517 : Blo 550806 1246517 := bbase (se 5 (by rfl) ⟨58430, by rfl⟩ : syracuseStep 1246517 = 116861) (by norm_num)
theorem B623929 : Blo 550806 623929 := bbase (se 2 (by rfl) ⟨233973, by rfl⟩ : syracuseStep 623929 = 467947) (by norm_num)
theorem B623965 : Blo 550806 623965 := bbase (se 3 (by rfl) ⟨116993, by rfl⟩ : syracuseStep 623965 = 233987) (by norm_num)
theorem B1246589 : Blo 550806 1246589 := bbase (se 3 (by rfl) ⟨233735, by rfl⟩ : syracuseStep 1246589 = 467471) (by norm_num)
theorem B624001 : Blo 550806 624001 := bbase (se 2 (by rfl) ⟨234000, by rfl⟩ : syracuseStep 624001 = 468001) (by norm_num)
theorem B624037 : Blo 550806 624037 := bbase (se 4 (by rfl) ⟨58503, by rfl⟩ : syracuseStep 624037 = 117007) (by norm_num)
theorem B1181117 : Blo 550806 1181117 := bbase (se 3 (by rfl) ⟨221459, by rfl⟩ : syracuseStep 1181117 = 442919) (by norm_num)
theorem B1246661 : Blo 550806 1246661 := bbase (se 4 (by rfl) ⟨116874, by rfl⟩ : syracuseStep 1246661 = 233749) (by norm_num)
theorem B624073 : Blo 550806 624073 := bbase (se 2 (by rfl) ⟨234027, by rfl⟩ : syracuseStep 624073 = 468055) (by norm_num)
theorem B1705445 : Blo 550806 1705445 := bbase (se 4 (by rfl) ⟨159885, by rfl⟩ : syracuseStep 1705445 = 319771) (by norm_num)
theorem B624109 : Blo 550806 624109 := bbase (se 3 (by rfl) ⟨117020, by rfl⟩ : syracuseStep 624109 = 234041) (by norm_num)
theorem B1869317 : Blo 550806 1869317 := bbase (se 4 (by rfl) ⟨175248, by rfl⟩ : syracuseStep 1869317 = 350497) (by norm_num)
theorem B787981 : Blo 550806 787981 := bbase (se 3 (by rfl) ⟨147746, by rfl⟩ : syracuseStep 787981 = 295493) (by norm_num)
theorem B1246733 : Blo 550806 1246733 := bbase (se 3 (by rfl) ⟨233762, by rfl⟩ : syracuseStep 1246733 = 467525) (by norm_num)
theorem B624145 : Blo 550806 624145 := bbase (se 2 (by rfl) ⟨234054, by rfl⟩ : syracuseStep 624145 = 468109) (by norm_num)
theorem B591409 : Blo 550806 591409 := bbase (se 2 (by rfl) ⟨221778, by rfl⟩ : syracuseStep 591409 = 443557) (by norm_num)
theorem B1246805 : Blo 550806 1246805 := bbase (se 8 (by rfl) ⟨7305, by rfl⟩ : syracuseStep 1246805 = 14611) (by norm_num)
theorem B558685 : Blo 550806 558685 := bbase (se 3 (by rfl) ⟨104753, by rfl⟩ : syracuseStep 558685 = 209507) (by norm_num)
theorem B591481 : Blo 550806 591481 := bbase (se 2 (by rfl) ⟨221805, by rfl⟩ : syracuseStep 591481 = 443611) (by norm_num)
theorem B1574549 : Blo 550806 1574549 := bbase (se 6 (by rfl) ⟨36903, by rfl⟩ : syracuseStep 1574549 = 73807) (by norm_num)
theorem B1246877 : Blo 550806 1246877 := bbase (se 3 (by rfl) ⟨233789, by rfl⟩ : syracuseStep 1246877 = 467579) (by norm_num)
theorem B2393813 : Blo 550806 2393813 := bbase (se 7 (by rfl) ⟨28052, by rfl⟩ : syracuseStep 2393813 = 56105) (by norm_num)
theorem B1246949 : Blo 550806 1246949 := bbase (se 4 (by rfl) ⟨116901, by rfl⟩ : syracuseStep 1246949 = 233803) (by norm_num)
theorem B591661 : Blo 550806 591661 := bbase (se 3 (by rfl) ⟨110936, by rfl⟩ : syracuseStep 591661 = 221873) (by norm_num)
theorem B1247021 : Blo 550806 1247021 := bbase (se 3 (by rfl) ⟨233816, by rfl⟩ : syracuseStep 1247021 = 467633) (by norm_num)
theorem B1050421 : Blo 550806 1050421 := bbase (se 5 (by rfl) ⟨49238, by rfl⟩ : syracuseStep 1050421 = 98477) (by norm_num)
theorem B1247093 : Blo 550806 1247093 := bbase (se 5 (by rfl) ⟨58457, by rfl⟩ : syracuseStep 1247093 = 116915) (by norm_num)
theorem B1869749 : Blo 550806 1869749 := bbase (se 5 (by rfl) ⟨87644, by rfl⟩ : syracuseStep 1869749 = 175289) (by norm_num)
theorem B1247165 : Blo 550806 1247165 := bbase (se 3 (by rfl) ⟨233843, by rfl⟩ : syracuseStep 1247165 = 467687) (by norm_num)
theorem B2295749 : Blo 550806 2295749 := bbase (se 4 (by rfl) ⟨215226, by rfl⟩ : syracuseStep 2295749 = 430453) (by norm_num)
theorem B2099141 : Blo 550806 2099141 := bbase (se 4 (by rfl) ⟨196794, by rfl⟩ : syracuseStep 2099141 = 393589) (by norm_num)
theorem B1050565 : Blo 550806 1050565 := bbase (se 4 (by rfl) ⟨98490, by rfl⟩ : syracuseStep 1050565 = 196981) (by norm_num)
theorem B1247237 : Blo 550806 1247237 := bbase (se 4 (by rfl) ⟨116928, by rfl⟩ : syracuseStep 1247237 = 233857) (by norm_num)
theorem B1771573 : Blo 550806 1771573 := bbase (se 5 (by rfl) ⟨83042, by rfl⟩ : syracuseStep 1771573 = 166085) (by norm_num)
theorem B2361413 : Blo 550806 2361413 := bbase (se 4 (by rfl) ⟨221382, by rfl⟩ : syracuseStep 2361413 = 442765) (by norm_num)
theorem B1247309 : Blo 550806 1247309 := bbase (se 3 (by rfl) ⟨233870, by rfl⟩ : syracuseStep 1247309 = 467741) (by norm_num)
theorem B788573 : Blo 550806 788573 := bbase (se 3 (by rfl) ⟨147857, by rfl⟩ : syracuseStep 788573 = 295715) (by norm_num)
theorem B1050725 : Blo 550806 1050725 := bbase (se 4 (by rfl) ⟨98505, by rfl⟩ : syracuseStep 1050725 = 197011) (by norm_num)
theorem B1247381 : Blo 550806 1247381 := bbase (se 6 (by rfl) ⟨29235, by rfl⟩ : syracuseStep 1247381 = 58471) (by norm_num)
theorem B2656421 : Blo 550806 2656421 := bbase (se 4 (by rfl) ⟨249039, by rfl⟩ : syracuseStep 2656421 = 498079) (by norm_num)
theorem B1181861 : Blo 550806 1181861 := bbase (se 4 (by rfl) ⟨110799, by rfl⟩ : syracuseStep 1181861 = 221599) (by norm_num)
theorem B788653 : Blo 550806 788653 := bbase (se 3 (by rfl) ⟨147872, by rfl⟩ : syracuseStep 788653 = 295745) (by norm_num)
theorem B3770549 : Blo 550806 3770549 := bbase (se 5 (by rfl) ⟨176744, by rfl⟩ : syracuseStep 3770549 = 353489) (by norm_num)
theorem B1247453 : Blo 550806 1247453 := bbase (se 3 (by rfl) ⟨233897, by rfl⟩ : syracuseStep 1247453 = 467795) (by norm_num)
theorem B2099429 : Blo 550806 2099429 := bbase (se 4 (by rfl) ⟨196821, by rfl⟩ : syracuseStep 2099429 = 393643) (by norm_num)
theorem B592105 : Blo 550806 592105 := bbase (se 2 (by rfl) ⟨222039, by rfl⟩ : syracuseStep 592105 = 444079) (by norm_num)
theorem B1050869 : Blo 550806 1050869 := bbase (se 5 (by rfl) ⟨49259, by rfl⟩ : syracuseStep 1050869 = 98519) (by norm_num)
theorem B788773 : Blo 550806 788773 := bbase (se 4 (by rfl) ⟨73947, by rfl⟩ : syracuseStep 788773 = 147895) (by norm_num)
theorem B1247525 : Blo 550806 1247525 := bbase (se 4 (by rfl) ⟨116955, by rfl⟩ : syracuseStep 1247525 = 233911) (by norm_num)
theorem B1870181 : Blo 550806 1870181 := bbase (se 4 (by rfl) ⟨175329, by rfl⟩ : syracuseStep 1870181 = 350659) (by norm_num)
theorem B592229 : Blo 550806 592229 := bbase (se 4 (by rfl) ⟨55521, by rfl⟩ : syracuseStep 592229 = 111043) (by norm_num)
theorem B1247597 : Blo 550806 1247597 := bbase (se 3 (by rfl) ⟨233924, by rfl⟩ : syracuseStep 1247597 = 467849) (by norm_num)
theorem B1575301 : Blo 550806 1575301 := bbase (se 4 (by rfl) ⟨147684, by rfl⟩ : syracuseStep 1575301 = 295369) (by norm_num)
theorem B788869 : Blo 550806 788869 := bbase (se 4 (by rfl) ⟨73956, by rfl⟩ : syracuseStep 788869 = 147913) (by norm_num)
theorem B1247669 : Blo 550806 1247669 := bbase (se 5 (by rfl) ⟨58484, by rfl⟩ : syracuseStep 1247669 = 116969) (by norm_num)
theorem B1247741 : Blo 550806 1247741 := bbase (se 3 (by rfl) ⟨233951, by rfl⟩ : syracuseStep 1247741 = 467903) (by norm_num)
theorem B1051157 : Blo 550806 1051157 := bbase (se 6 (by rfl) ⟨24636, by rfl⟩ : syracuseStep 1051157 = 49273) (by norm_num)
theorem B1247813 : Blo 550806 1247813 := bbase (se 4 (by rfl) ⟨116982, by rfl⟩ : syracuseStep 1247813 = 233965) (by norm_num)
theorem B1247885 : Blo 550806 1247885 := bbase (se 3 (by rfl) ⟨233978, by rfl⟩ : syracuseStep 1247885 = 467957) (by norm_num)
theorem B887453 : Blo 550806 887453 := bbase (se 3 (by rfl) ⟨166397, by rfl⟩ : syracuseStep 887453 = 332795) (by norm_num)
theorem B1051309 : Blo 550806 1051309 := bbase (se 3 (by rfl) ⟨197120, by rfl⟩ : syracuseStep 1051309 = 394241) (by norm_num)
theorem B1247957 : Blo 550806 1247957 := bbase (se 7 (by rfl) ⟨14624, by rfl⟩ : syracuseStep 1247957 = 29249) (by norm_num)
theorem B1870613 : Blo 550806 1870613 := bbase (se 6 (by rfl) ⟨43842, by rfl⟩ : syracuseStep 1870613 = 87685) (by norm_num)
theorem B1248029 : Blo 550806 1248029 := bbase (se 3 (by rfl) ⟨234005, by rfl⟩ : syracuseStep 1248029 = 468011) (by norm_num)
theorem B2394917 : Blo 550806 2394917 := bbase (se 4 (by rfl) ⟨224523, by rfl⟩ : syracuseStep 2394917 = 449047) (by norm_num)
theorem B13405013 : Blo 550806 13405013 := bbase (se 9 (by rfl) ⟨39272, by rfl⟩ : syracuseStep 13405013 = 78545) (by norm_num)
theorem B887645 : Blo 550806 887645 := bbase (se 3 (by rfl) ⟨166433, by rfl⟩ : syracuseStep 887645 = 332867) (by norm_num)
theorem B1248101 : Blo 550806 1248101 := bbase (se 4 (by rfl) ⟨117009, by rfl⟩ : syracuseStep 1248101 = 234019) (by norm_num)
theorem B789365 : Blo 550806 789365 := bbase (se 5 (by rfl) ⟨37001, by rfl⟩ : syracuseStep 789365 = 74003) (by norm_num)
theorem B1182613 : Blo 550806 1182613 := bbase (se 6 (by rfl) ⟨27717, by rfl⟩ : syracuseStep 1182613 = 55435) (by norm_num)
theorem B1248173 : Blo 550806 1248173 := bbase (se 3 (by rfl) ⟨234032, by rfl⟩ : syracuseStep 1248173 = 468065) (by norm_num)
theorem B1051613 : Blo 550806 1051613 := bbase (se 3 (by rfl) ⟨197177, by rfl⟩ : syracuseStep 1051613 = 394355) (by norm_num)
theorem B1248245 : Blo 550806 1248245 := bbase (se 5 (by rfl) ⟨58511, by rfl⟩ : syracuseStep 1248245 = 117023) (by norm_num)
theorem B2362405 : Blo 550806 2362405 := bbase (se 4 (by rfl) ⟨221475, by rfl⟩ : syracuseStep 2362405 = 442951) (by norm_num)
theorem B1182757 : Blo 550806 1182757 := bbase (se 4 (by rfl) ⟨110883, by rfl⟩ : syracuseStep 1182757 = 221767) (by norm_num)
theorem B560197 : Blo 550806 560197 := bbase (se 4 (by rfl) ⟨52518, by rfl⟩ : syracuseStep 560197 = 105037) (by norm_num)
theorem B1871045 : Blo 550806 1871045 := bbase (se 4 (by rfl) ⟨175410, by rfl⟩ : syracuseStep 1871045 = 350821) (by norm_num)
theorem B2100613 : Blo 550806 2100613 := bbase (se 4 (by rfl) ⟨196932, by rfl⟩ : syracuseStep 2100613 = 393865) (by norm_num)
theorem B1183133 : Blo 550806 1183133 := bbase (se 3 (by rfl) ⟨221837, by rfl⟩ : syracuseStep 1183133 = 443675) (by norm_num)
theorem B789917 : Blo 550806 789917 := bbase (se 3 (by rfl) ⟨148109, by rfl⟩ : syracuseStep 789917 = 296219) (by norm_num)
theorem B1347005 : Blo 550806 1347005 := bbase (se 3 (by rfl) ⟨252563, by rfl⟩ : syracuseStep 1347005 = 505127) (by norm_num)
theorem B1379885 : Blo 550806 1379885 := bbase (se 3 (by rfl) ⟨258728, by rfl⟩ : syracuseStep 1379885 = 517457) (by norm_num)
theorem B1117765 : Blo 550806 1117765 := bbase (se 4 (by rfl) ⟨104790, by rfl⟩ : syracuseStep 1117765 = 209581) (by norm_num)
theorem B1871477 : Blo 550806 1871477 := bbase (se 5 (by rfl) ⟨87725, by rfl⟩ : syracuseStep 1871477 = 175451) (by norm_num)
theorem B757405 : Blo 550806 757405 := bbase (se 3 (by rfl) ⟨142013, by rfl⟩ : syracuseStep 757405 = 284027) (by norm_num)
theorem B2100917 : Blo 550806 2100917 := bbase (se 5 (by rfl) ⟨98480, by rfl⟩ : syracuseStep 2100917 = 196961) (by norm_num)
theorem B1052365 : Blo 550806 1052365 := bbase (se 3 (by rfl) ⟨197318, by rfl⟩ : syracuseStep 1052365 = 394637) (by norm_num)
theorem B1347317 : Blo 550806 1347317 := bbase (se 5 (by rfl) ⟨63155, by rfl⟩ : syracuseStep 1347317 = 126311) (by norm_num)
theorem B1183501 : Blo 550806 1183501 := bbase (se 3 (by rfl) ⟨221906, by rfl⟩ : syracuseStep 1183501 = 443813) (by norm_num)
theorem B15109973 : Blo 550806 15109973 := bbase (se 9 (by rfl) ⟨44267, by rfl⟩ : syracuseStep 15109973 = 88535) (by norm_num)
theorem B1052509 : Blo 550806 1052509 := bbase (se 3 (by rfl) ⟨197345, by rfl⟩ : syracuseStep 1052509 = 394691) (by norm_num)
theorem B561053 : Blo 550806 561053 := bbase (se 3 (by rfl) ⟨105197, by rfl⟩ : syracuseStep 561053 = 210395) (by norm_num)
theorem B1052669 : Blo 550806 1052669 := bbase (se 3 (by rfl) ⟨197375, by rfl⟩ : syracuseStep 1052669 = 394751) (by norm_num)
theorem B1871909 : Blo 550806 1871909 := bbase (se 4 (by rfl) ⟨175491, by rfl⟩ : syracuseStep 1871909 = 350983) (by norm_num)
theorem B2789477 : Blo 550806 2789477 := bbase (se 4 (by rfl) ⟨261513, by rfl⟩ : syracuseStep 2789477 = 523027) (by norm_num)
theorem B1052813 : Blo 550806 1052813 := bbase (se 3 (by rfl) ⟨197402, by rfl⟩ : syracuseStep 1052813 = 394805) (by norm_num)
theorem B987349 : Blo 550806 987349 := bbase (se 7 (by rfl) ⟨11570, by rfl⟩ : syracuseStep 987349 = 23141) (by norm_num)
theorem B1347941 : Blo 550806 1347941 := bbase (se 4 (by rfl) ⟨126369, by rfl⟩ : syracuseStep 1347941 = 252739) (by norm_num)
theorem B1053101 : Blo 550806 1053101 := bbase (se 3 (by rfl) ⟨197456, by rfl⟩ : syracuseStep 1053101 = 394913) (by norm_num)
theorem B1872341 : Blo 550806 1872341 := bbase (se 7 (by rfl) ⟨21941, by rfl⟩ : syracuseStep 1872341 = 43883) (by norm_num)
theorem B1053253 : Blo 550806 1053253 := bbase (se 4 (by rfl) ⟨98742, by rfl⟩ : syracuseStep 1053253 = 197485) (by norm_num)
theorem B2659205 : Blo 550806 2659205 := bbase (se 4 (by rfl) ⟨249300, by rfl⟩ : syracuseStep 2659205 = 498601) (by norm_num)
theorem B1414181 : Blo 550806 1414181 := bbase (se 4 (by rfl) ⟨132579, by rfl⟩ : syracuseStep 1414181 = 265159) (by norm_num)
theorem B2135173 : Blo 550806 2135173 := bbase (se 4 (by rfl) ⟨200172, by rfl⟩ : syracuseStep 2135173 = 400345) (by norm_num)
theorem B1578149 : Blo 550806 1578149 := bbase (se 4 (by rfl) ⟨147951, by rfl⟩ : syracuseStep 1578149 = 295903) (by norm_num)
theorem B2790773 : Blo 550806 2790773 := bbase (se 5 (by rfl) ⟨130817, by rfl⟩ : syracuseStep 2790773 = 261635) (by norm_num)
theorem B2103029 : Blo 550806 2103029 := bbase (se 5 (by rfl) ⟨98579, by rfl⟩ : syracuseStep 2103029 = 197159) (by norm_num)
theorem B1677125 : Blo 550806 1677125 := bbase (se 4 (by rfl) ⟨157230, by rfl⟩ : syracuseStep 1677125 = 314461) (by norm_num)
theorem B1120069 : Blo 550806 1120069 := bbase (se 4 (by rfl) ⟨105006, by rfl⟩ : syracuseStep 1120069 = 210013) (by norm_num)
theorem B3545045 : Blo 550806 3545045 := bbase (se 7 (by rfl) ⟨41543, by rfl⟩ : syracuseStep 3545045 = 83087) (by norm_num)
theorem B3774485 : Blo 550806 3774485 := bbase (se 6 (by rfl) ⟨88464, by rfl⟩ : syracuseStep 3774485 = 176929) (by norm_num)
theorem B2103317 : Blo 550806 2103317 := bbase (se 6 (by rfl) ⟨49296, by rfl⟩ : syracuseStep 2103317 = 98593) (by norm_num)
theorem B4725013 : Blo 550806 4725013 := bbase (se 6 (by rfl) ⟨110742, by rfl⟩ : syracuseStep 4725013 = 221485) (by norm_num)
theorem B1579333 : Blo 550806 1579333 := bbase (se 4 (by rfl) ⟨148062, by rfl⟩ : syracuseStep 1579333 = 296125) (by norm_num)
theorem B1579493 : Blo 550806 1579493 := bbase (se 4 (by rfl) ⟨148077, by rfl⟩ : syracuseStep 1579493 = 296155) (by norm_num)
theorem B956981 : Blo 550806 956981 := bbase (se 5 (by rfl) ⟨44858, by rfl⟩ : syracuseStep 956981 = 89717) (by norm_num)
theorem B2792069 : Blo 550806 2792069 := bbase (se 4 (by rfl) ⟨261756, by rfl⟩ : syracuseStep 2792069 = 523513) (by norm_num)
theorem B629437 : Blo 550806 629437 := bbase (se 3 (by rfl) ⟨118019, by rfl⟩ : syracuseStep 629437 = 236039) (by norm_num)
theorem B1579733 : Blo 550806 1579733 := bbase (se 7 (by rfl) ⟨18512, by rfl⟩ : syracuseStep 1579733 = 37025) (by norm_num)
theorem B662341 : Blo 550806 662341 := bbase (se 4 (by rfl) ⟨62094, by rfl⟩ : syracuseStep 662341 = 124189) (by norm_num)
theorem B826229 : Blo 550806 826229 := bbase (se 5 (by rfl) ⟨38729, by rfl⟩ : syracuseStep 826229 = 77459) (by norm_num)
theorem B826253 : Blo 550806 826253 := bbase (se 3 (by rfl) ⟨154922, by rfl⟩ : syracuseStep 826253 = 309845) (by norm_num)
theorem B3152789 : Blo 550806 3152789 := bbase (se 6 (by rfl) ⟨73893, by rfl⟩ : syracuseStep 3152789 = 147787) (by norm_num)
theorem B826277 : Blo 550806 826277 := bbase (se 4 (by rfl) ⟨77463, by rfl⟩ : syracuseStep 826277 = 154927) (by norm_num)
theorem B662437 : Blo 550806 662437 := bbase (se 4 (by rfl) ⟨62103, by rfl⟩ : syracuseStep 662437 = 124207) (by norm_num)
theorem B1121197 : Blo 550806 1121197 := bbase (se 3 (by rfl) ⟨210224, by rfl⟩ : syracuseStep 1121197 = 420449) (by norm_num)
theorem B826301 : Blo 550806 826301 := bbase (se 3 (by rfl) ⟨154931, by rfl⟩ : syracuseStep 826301 = 309863) (by norm_num)
theorem B826325 : Blo 550806 826325 := bbase (se 7 (by rfl) ⟨9683, by rfl⟩ : syracuseStep 826325 = 19367) (by norm_num)
theorem B826349 : Blo 550806 826349 := bbase (se 3 (by rfl) ⟨154940, by rfl⟩ : syracuseStep 826349 = 309881) (by norm_num)
theorem B826373 : Blo 550806 826373 := bbase (se 4 (by rfl) ⟨77472, by rfl⟩ : syracuseStep 826373 = 154945) (by norm_num)
theorem B826397 : Blo 550806 826397 := bbase (se 3 (by rfl) ⟨154949, by rfl⟩ : syracuseStep 826397 = 309899) (by norm_num)
theorem B826421 : Blo 550806 826421 := bbase (se 5 (by rfl) ⟨38738, by rfl⟩ : syracuseStep 826421 = 77477) (by norm_num)
theorem B1121333 : Blo 550806 1121333 := bbase (se 5 (by rfl) ⟨52562, by rfl⟩ : syracuseStep 1121333 = 105125) (by norm_num)
theorem B826445 : Blo 550806 826445 := bbase (se 3 (by rfl) ⟨154958, by rfl⟩ : syracuseStep 826445 = 309917) (by norm_num)
theorem B1776725 : Blo 550806 1776725 := bbase (se 8 (by rfl) ⟨10410, by rfl⟩ : syracuseStep 1776725 = 20821) (by norm_num)
theorem B826469 : Blo 550806 826469 := bbase (se 4 (by rfl) ⟨77481, by rfl⟩ : syracuseStep 826469 = 154963) (by norm_num)
theorem B826493 : Blo 550806 826493 := bbase (se 3 (by rfl) ⟨154967, by rfl⟩ : syracuseStep 826493 = 309935) (by norm_num)
theorem B826517 : Blo 550806 826517 := bbase (se 6 (by rfl) ⟨19371, by rfl⟩ : syracuseStep 826517 = 38743) (by norm_num)
theorem B826541 : Blo 550806 826541 := bbase (se 3 (by rfl) ⟨154976, by rfl⟩ : syracuseStep 826541 = 309953) (by norm_num)
theorem B2104501 : Blo 550806 2104501 := bbase (se 5 (by rfl) ⟨98648, by rfl⟩ : syracuseStep 2104501 = 197297) (by norm_num)
theorem B826565 : Blo 550806 826565 := bbase (se 4 (by rfl) ⟨77490, by rfl⟩ : syracuseStep 826565 = 154981) (by norm_num)
theorem B826589 : Blo 550806 826589 := bbase (se 3 (by rfl) ⟨154985, by rfl⟩ : syracuseStep 826589 = 309971) (by norm_num)
theorem B826613 : Blo 550806 826613 := bbase (se 5 (by rfl) ⟨38747, by rfl⟩ : syracuseStep 826613 = 77495) (by norm_num)
theorem B826637 : Blo 550806 826637 := bbase (se 3 (by rfl) ⟨154994, by rfl⟩ : syracuseStep 826637 = 309989) (by norm_num)
theorem B826661 : Blo 550806 826661 := bbase (se 4 (by rfl) ⟨77499, by rfl⟩ : syracuseStep 826661 = 154999) (by norm_num)
theorem B826685 : Blo 550806 826685 := bbase (se 3 (by rfl) ⟨155003, by rfl⟩ : syracuseStep 826685 = 310007) (by norm_num)
theorem B826709 : Blo 550806 826709 := bbase (se 11 (by rfl) ⟨605, by rfl⟩ : syracuseStep 826709 = 1211) (by norm_num)
theorem B826733 : Blo 550806 826733 := bbase (se 3 (by rfl) ⟨155012, by rfl⟩ : syracuseStep 826733 = 310025) (by norm_num)
theorem B1351037 : Blo 550806 1351037 := bbase (se 3 (by rfl) ⟨253319, by rfl⟩ : syracuseStep 1351037 = 506639) (by norm_num)
theorem B826757 : Blo 550806 826757 := bbase (se 4 (by rfl) ⟨77508, by rfl⟩ : syracuseStep 826757 = 155017) (by norm_num)
theorem B826781 : Blo 550806 826781 := bbase (se 3 (by rfl) ⟨155021, by rfl⟩ : syracuseStep 826781 = 310043) (by norm_num)
theorem B826805 : Blo 550806 826805 := bbase (se 5 (by rfl) ⟨38756, by rfl⟩ : syracuseStep 826805 = 77513) (by norm_num)
theorem B826829 : Blo 550806 826829 := bbase (se 3 (by rfl) ⟨155030, by rfl⟩ : syracuseStep 826829 = 310061) (by norm_num)
theorem B826853 : Blo 550806 826853 := bbase (se 4 (by rfl) ⟨77517, by rfl⟩ : syracuseStep 826853 = 155035) (by norm_num)
theorem B2104805 : Blo 550806 2104805 := bbase (se 4 (by rfl) ⟨197325, by rfl⟩ : syracuseStep 2104805 = 394651) (by norm_num)
theorem B826877 : Blo 550806 826877 := bbase (se 3 (by rfl) ⟨155039, by rfl⟩ : syracuseStep 826877 = 310079) (by norm_num)
theorem B826901 : Blo 550806 826901 := bbase (se 6 (by rfl) ⟨19380, by rfl⟩ : syracuseStep 826901 = 38761) (by norm_num)
theorem B826925 : Blo 550806 826925 := bbase (se 3 (by rfl) ⟨155048, by rfl⟩ : syracuseStep 826925 = 310097) (by norm_num)
theorem B826949 : Blo 550806 826949 := bbase (se 4 (by rfl) ⟨77526, by rfl⟩ : syracuseStep 826949 = 155053) (by norm_num)
theorem B826973 : Blo 550806 826973 := bbase (se 3 (by rfl) ⟨155057, by rfl⟩ : syracuseStep 826973 = 310115) (by norm_num)
theorem B826997 : Blo 550806 826997 := bbase (se 5 (by rfl) ⟨38765, by rfl⟩ : syracuseStep 826997 = 77531) (by norm_num)
theorem B827021 : Blo 550806 827021 := bbase (se 3 (by rfl) ⟨155066, by rfl⟩ : syracuseStep 827021 = 310133) (by norm_num)
theorem B827045 : Blo 550806 827045 := bbase (se 4 (by rfl) ⟨77535, by rfl⟩ : syracuseStep 827045 = 155071) (by norm_num)
theorem B827069 : Blo 550806 827069 := bbase (se 3 (by rfl) ⟨155075, by rfl⟩ : syracuseStep 827069 = 310151) (by norm_num)
theorem B827093 : Blo 550806 827093 := bbase (se 7 (by rfl) ⟨9692, by rfl⟩ : syracuseStep 827093 = 19385) (by norm_num)
theorem B827117 : Blo 550806 827117 := bbase (se 3 (by rfl) ⟨155084, by rfl⟩ : syracuseStep 827117 = 310169) (by norm_num)
theorem B827141 : Blo 550806 827141 := bbase (se 4 (by rfl) ⟨77544, by rfl⟩ : syracuseStep 827141 = 155089) (by norm_num)
theorem B827165 : Blo 550806 827165 := bbase (se 3 (by rfl) ⟨155093, by rfl⟩ : syracuseStep 827165 = 310187) (by norm_num)
theorem B827189 : Blo 550806 827189 := bbase (se 5 (by rfl) ⟨38774, by rfl⟩ : syracuseStep 827189 = 77549) (by norm_num)
theorem B827213 : Blo 550806 827213 := bbase (se 3 (by rfl) ⟨155102, by rfl⟩ : syracuseStep 827213 = 310205) (by norm_num)
theorem B827237 : Blo 550806 827237 := bbase (se 4 (by rfl) ⟨77553, by rfl⟩ : syracuseStep 827237 = 155107) (by norm_num)
theorem B827261 : Blo 550806 827261 := bbase (se 3 (by rfl) ⟨155111, by rfl⟩ : syracuseStep 827261 = 310223) (by norm_num)
theorem B663437 : Blo 550806 663437 := bbase (se 3 (by rfl) ⟨124394, by rfl⟩ : syracuseStep 663437 = 248789) (by norm_num)
theorem B827285 : Blo 550806 827285 := bbase (se 6 (by rfl) ⟨19389, by rfl⟩ : syracuseStep 827285 = 38779) (by norm_num)
theorem B2793365 : Blo 550806 2793365 := bbase (se 6 (by rfl) ⟨65469, by rfl⟩ : syracuseStep 2793365 = 130939) (by norm_num)
theorem B827309 : Blo 550806 827309 := bbase (se 3 (by rfl) ⟨155120, by rfl⟩ : syracuseStep 827309 = 310241) (by norm_num)
theorem B2367413 : Blo 550806 2367413 := bbase (se 5 (by rfl) ⟨110972, by rfl⟩ : syracuseStep 2367413 = 221945) (by norm_num)
theorem B827333 : Blo 550806 827333 := bbase (se 4 (by rfl) ⟨77562, by rfl⟩ : syracuseStep 827333 = 155125) (by norm_num)
theorem B16981973 : Blo 550806 16981973 := bbase (se 7 (by rfl) ⟨199007, by rfl⟩ : syracuseStep 16981973 = 398015) (by norm_num)
theorem B827357 : Blo 550806 827357 := bbase (se 3 (by rfl) ⟨155129, by rfl⟩ : syracuseStep 827357 = 310259) (by norm_num)
theorem B827381 : Blo 550806 827381 := bbase (se 5 (by rfl) ⟨38783, by rfl⟩ : syracuseStep 827381 = 77567) (by norm_num)
theorem B827405 : Blo 550806 827405 := bbase (se 3 (by rfl) ⟨155138, by rfl⟩ : syracuseStep 827405 = 310277) (by norm_num)
theorem B827429 : Blo 550806 827429 := bbase (se 4 (by rfl) ⟨77571, by rfl⟩ : syracuseStep 827429 = 155143) (by norm_num)
theorem B827453 : Blo 550806 827453 := bbase (se 3 (by rfl) ⟨155147, by rfl⟩ : syracuseStep 827453 = 310295) (by norm_num)
theorem B827477 : Blo 550806 827477 := bbase (se 8 (by rfl) ⟨4848, by rfl⟩ : syracuseStep 827477 = 9697) (by norm_num)
theorem B16162901 : Blo 550806 16162901 := bbase (se 8 (by rfl) ⟨94704, by rfl⟩ : syracuseStep 16162901 = 189409) (by norm_num)
theorem B827501 : Blo 550806 827501 := bbase (se 3 (by rfl) ⟨155156, by rfl⟩ : syracuseStep 827501 = 310313) (by norm_num)
theorem B827525 : Blo 550806 827525 := bbase (se 4 (by rfl) ⟨77580, by rfl⟩ : syracuseStep 827525 = 155161) (by norm_num)
theorem B827549 : Blo 550806 827549 := bbase (se 3 (by rfl) ⟨155165, by rfl⟩ : syracuseStep 827549 = 310331) (by norm_num)
theorem B663725 : Blo 550806 663725 := bbase (se 3 (by rfl) ⟨124448, by rfl⟩ : syracuseStep 663725 = 248897) (by norm_num)
theorem B827573 : Blo 550806 827573 := bbase (se 5 (by rfl) ⟨38792, by rfl⟩ : syracuseStep 827573 = 77585) (by norm_num)
theorem B827597 : Blo 550806 827597 := bbase (se 3 (by rfl) ⟨155174, by rfl⟩ : syracuseStep 827597 = 310349) (by norm_num)
theorem B4726997 : Blo 550806 4726997 := bbase (se 7 (by rfl) ⟨55394, by rfl⟩ : syracuseStep 4726997 = 110789) (by norm_num)
theorem B2367701 : Blo 550806 2367701 := bbase (se 7 (by rfl) ⟨27746, by rfl⟩ : syracuseStep 2367701 = 55493) (by norm_num)
theorem B827621 : Blo 550806 827621 := bbase (se 4 (by rfl) ⟨77589, by rfl⟩ : syracuseStep 827621 = 155179) (by norm_num)
theorem B827645 : Blo 550806 827645 := bbase (se 3 (by rfl) ⟨155183, by rfl⟩ : syracuseStep 827645 = 310367) (by norm_num)
theorem B827669 : Blo 550806 827669 := bbase (se 6 (by rfl) ⟨19398, by rfl⟩ : syracuseStep 827669 = 38797) (by norm_num)
theorem B827693 : Blo 550806 827693 := bbase (se 3 (by rfl) ⟨155192, by rfl⟩ : syracuseStep 827693 = 310385) (by norm_num)
theorem B827717 : Blo 550806 827717 := bbase (se 4 (by rfl) ⟨77598, by rfl⟩ : syracuseStep 827717 = 155197) (by norm_num)
theorem B663889 : Blo 550806 663889 := bbase (se 2 (by rfl) ⟨248958, by rfl⟩ : syracuseStep 663889 = 497917) (by norm_num)
theorem B2662741 : Blo 550806 2662741 := bbase (se 10 (by rfl) ⟨3900, by rfl⟩ : syracuseStep 2662741 = 7801) (by norm_num)
theorem B827741 : Blo 550806 827741 := bbase (se 3 (by rfl) ⟨155201, by rfl⟩ : syracuseStep 827741 = 310403) (by norm_num)
theorem B663917 : Blo 550806 663917 := bbase (se 3 (by rfl) ⟨124484, by rfl⟩ : syracuseStep 663917 = 248969) (by norm_num)
theorem B827765 : Blo 550806 827765 := bbase (se 5 (by rfl) ⟨38801, by rfl⟩ : syracuseStep 827765 = 77603) (by norm_num)
theorem B827789 : Blo 550806 827789 := bbase (se 3 (by rfl) ⟨155210, by rfl⟩ : syracuseStep 827789 = 310421) (by norm_num)
theorem B631189 : Blo 550806 631189 := bbase (se 6 (by rfl) ⟨14793, by rfl⟩ : syracuseStep 631189 = 29587) (by norm_num)
theorem B827813 : Blo 550806 827813 := bbase (se 4 (by rfl) ⟨77607, by rfl⟩ : syracuseStep 827813 = 155215) (by norm_num)
theorem B827837 : Blo 550806 827837 := bbase (se 3 (by rfl) ⟨155219, by rfl⟩ : syracuseStep 827837 = 310439) (by norm_num)
theorem B827861 : Blo 550806 827861 := bbase (se 7 (by rfl) ⟨9701, by rfl⟩ : syracuseStep 827861 = 19403) (by norm_num)
theorem B664033 : Blo 550806 664033 := bbase (se 2 (by rfl) ⟨249012, by rfl⟩ : syracuseStep 664033 = 498025) (by norm_num)
theorem B827885 : Blo 550806 827885 := bbase (se 3 (by rfl) ⟨155228, by rfl⟩ : syracuseStep 827885 = 310457) (by norm_num)
theorem B827909 : Blo 550806 827909 := bbase (se 4 (by rfl) ⟨77616, by rfl⟩ : syracuseStep 827909 = 155233) (by norm_num)
theorem B827933 : Blo 550806 827933 := bbase (se 3 (by rfl) ⟨155237, by rfl⟩ : syracuseStep 827933 = 310475) (by norm_num)
theorem B827957 : Blo 550806 827957 := bbase (se 5 (by rfl) ⟨38810, by rfl⟩ : syracuseStep 827957 = 77621) (by norm_num)
theorem B664129 : Blo 550806 664129 := bbase (se 2 (by rfl) ⟨249048, by rfl⟩ : syracuseStep 664129 = 498097) (by norm_num)
theorem B827981 : Blo 550806 827981 := bbase (se 3 (by rfl) ⟨155246, by rfl⟩ : syracuseStep 827981 = 310493) (by norm_num)
theorem B1679957 : Blo 550806 1679957 := bbase (se 8 (by rfl) ⟨9843, by rfl⟩ : syracuseStep 1679957 = 19687) (by norm_num)
theorem B828005 : Blo 550806 828005 := bbase (se 4 (by rfl) ⟨77625, by rfl⟩ : syracuseStep 828005 = 155251) (by norm_num)
theorem B631417 : Blo 550806 631417 := bbase (se 2 (by rfl) ⟨236781, by rfl⟩ : syracuseStep 631417 = 473563) (by norm_num)
theorem B828029 : Blo 550806 828029 := bbase (se 3 (by rfl) ⟨155255, by rfl⟩ : syracuseStep 828029 = 310511) (by norm_num)
theorem B828053 : Blo 550806 828053 := bbase (se 6 (by rfl) ⟨19407, by rfl⟩ : syracuseStep 828053 = 38815) (by norm_num)
theorem B828077 : Blo 550806 828077 := bbase (se 3 (by rfl) ⟨155264, by rfl⟩ : syracuseStep 828077 = 310529) (by norm_num)
theorem B631481 : Blo 550806 631481 := bbase (se 2 (by rfl) ⟨236805, by rfl⟩ : syracuseStep 631481 = 473611) (by norm_num)
theorem B828101 : Blo 550806 828101 := bbase (se 4 (by rfl) ⟨77634, by rfl⟩ : syracuseStep 828101 = 155269) (by norm_num)
theorem B1123021 : Blo 550806 1123021 := bbase (se 3 (by rfl) ⟨210566, by rfl⟩ : syracuseStep 1123021 = 421133) (by norm_num)
theorem B828125 : Blo 550806 828125 := bbase (se 3 (by rfl) ⟨155273, by rfl⟩ : syracuseStep 828125 = 310547) (by norm_num)
theorem B959197 : Blo 550806 959197 := bbase (se 3 (by rfl) ⟨179849, by rfl⟩ : syracuseStep 959197 = 359699) (by norm_num)
theorem B828149 : Blo 550806 828149 := bbase (se 5 (by rfl) ⟨38819, by rfl⟩ : syracuseStep 828149 = 77639) (by norm_num)
theorem B828173 : Blo 550806 828173 := bbase (se 3 (by rfl) ⟨155282, by rfl⟩ : syracuseStep 828173 = 310565) (by norm_num)
theorem B828197 : Blo 550806 828197 := bbase (se 4 (by rfl) ⟨77643, by rfl⟩ : syracuseStep 828197 = 155287) (by norm_num)
theorem B828221 : Blo 550806 828221 := bbase (se 3 (by rfl) ⟨155291, by rfl⟩ : syracuseStep 828221 = 310583) (by norm_num)
theorem B828245 : Blo 550806 828245 := bbase (se 9 (by rfl) ⟨2426, by rfl⟩ : syracuseStep 828245 = 4853) (by norm_num)
theorem B697177 : Blo 550806 697177 := bbase (se 2 (by rfl) ⟨261441, by rfl⟩ : syracuseStep 697177 = 522883) (by norm_num)
theorem B828269 : Blo 550806 828269 := bbase (se 3 (by rfl) ⟨155300, by rfl⟩ : syracuseStep 828269 = 310601) (by norm_num)
theorem B828293 : Blo 550806 828293 := bbase (se 4 (by rfl) ⟨77652, by rfl⟩ : syracuseStep 828293 = 155305) (by norm_num)
theorem B4203413 : Blo 550806 4203413 := bbase (se 6 (by rfl) ⟨98517, by rfl⟩ : syracuseStep 4203413 = 197035) (by norm_num)
theorem B828317 : Blo 550806 828317 := bbase (se 3 (by rfl) ⟨155309, by rfl⟩ : syracuseStep 828317 = 310619) (by norm_num)
theorem B828341 : Blo 550806 828341 := bbase (se 5 (by rfl) ⟨38828, by rfl⟩ : syracuseStep 828341 = 77657) (by norm_num)
theorem B2368453 : Blo 550806 2368453 := bbase (se 4 (by rfl) ⟨222042, by rfl⟩ : syracuseStep 2368453 = 444085) (by norm_num)
theorem B828365 : Blo 550806 828365 := bbase (se 3 (by rfl) ⟨155318, by rfl⟩ : syracuseStep 828365 = 310637) (by norm_num)
theorem B828389 : Blo 550806 828389 := bbase (se 4 (by rfl) ⟨77661, by rfl⟩ : syracuseStep 828389 = 155323) (by norm_num)
theorem B828413 : Blo 550806 828413 := bbase (se 3 (by rfl) ⟨155327, by rfl⟩ : syracuseStep 828413 = 310655) (by norm_num)
theorem B697349 : Blo 550806 697349 := bbase (se 4 (by rfl) ⟨65376, by rfl⟩ : syracuseStep 697349 = 130753) (by norm_num)
theorem B828437 : Blo 550806 828437 := bbase (se 6 (by rfl) ⟨19416, by rfl⟩ : syracuseStep 828437 = 38833) (by norm_num)
theorem B664609 : Blo 550806 664609 := bbase (se 2 (by rfl) ⟨249228, by rfl⟩ : syracuseStep 664609 = 498457) (by norm_num)
theorem B631841 : Blo 550806 631841 := bbase (se 2 (by rfl) ⟨236940, by rfl⟩ : syracuseStep 631841 = 473881) (by norm_num)
theorem B828461 : Blo 550806 828461 := bbase (se 3 (by rfl) ⟨155336, by rfl⟩ : syracuseStep 828461 = 310673) (by norm_num)
theorem B697405 : Blo 550806 697405 := bbase (se 3 (by rfl) ⟨130763, by rfl⟩ : syracuseStep 697405 = 261527) (by norm_num)
theorem B828485 : Blo 550806 828485 := bbase (se 4 (by rfl) ⟨77670, by rfl⟩ : syracuseStep 828485 = 155341) (by norm_num)
theorem B828509 : Blo 550806 828509 := bbase (se 3 (by rfl) ⟨155345, by rfl⟩ : syracuseStep 828509 = 310691) (by norm_num)
theorem B828533 : Blo 550806 828533 := bbase (se 5 (by rfl) ⟨38837, by rfl⟩ : syracuseStep 828533 = 77675) (by norm_num)
theorem B828557 : Blo 550806 828557 := bbase (se 3 (by rfl) ⟨155354, by rfl⟩ : syracuseStep 828557 = 310709) (by norm_num)
theorem B697501 : Blo 550806 697501 := bbase (se 3 (by rfl) ⟨130781, by rfl⟩ : syracuseStep 697501 = 261563) (by norm_num)
theorem B2794661 : Blo 550806 2794661 := bbase (se 4 (by rfl) ⟨261999, by rfl⟩ : syracuseStep 2794661 = 523999) (by norm_num)
theorem B828581 : Blo 550806 828581 := bbase (se 4 (by rfl) ⟨77679, by rfl⟩ : syracuseStep 828581 = 155359) (by norm_num)
theorem B828605 : Blo 550806 828605 := bbase (se 3 (by rfl) ⟨155363, by rfl⟩ : syracuseStep 828605 = 310727) (by norm_num)
theorem B828629 : Blo 550806 828629 := bbase (se 7 (by rfl) ⟨9710, by rfl⟩ : syracuseStep 828629 = 19421) (by norm_num)
theorem B1123541 : Blo 550806 1123541 := bbase (se 7 (by rfl) ⟨13166, by rfl⟩ : syracuseStep 1123541 = 26333) (by norm_num)
theorem B828653 : Blo 550806 828653 := bbase (se 3 (by rfl) ⟨155372, by rfl⟩ : syracuseStep 828653 = 310745) (by norm_num)
theorem B828677 : Blo 550806 828677 := bbase (se 4 (by rfl) ⟨77688, by rfl⟩ : syracuseStep 828677 = 155377) (by norm_num)
theorem B828701 : Blo 550806 828701 := bbase (se 3 (by rfl) ⟨155381, by rfl⟩ : syracuseStep 828701 = 310763) (by norm_num)
theorem B828725 : Blo 550806 828725 := bbase (se 5 (by rfl) ⟨38846, by rfl⟩ : syracuseStep 828725 = 77693) (by norm_num)
theorem B697673 : Blo 550806 697673 := bbase (se 2 (by rfl) ⟨261627, by rfl⟩ : syracuseStep 697673 = 523255) (by norm_num)
theorem B828749 : Blo 550806 828749 := bbase (se 3 (by rfl) ⟨155390, by rfl⟩ : syracuseStep 828749 = 310781) (by norm_num)
theorem B828773 : Blo 550806 828773 := bbase (se 4 (by rfl) ⟨77697, by rfl⟩ : syracuseStep 828773 = 155395) (by norm_num)
theorem B828797 : Blo 550806 828797 := bbase (se 3 (by rfl) ⟨155399, by rfl⟩ : syracuseStep 828797 = 310799) (by norm_num)
theorem B697729 : Blo 550806 697729 := bbase (se 2 (by rfl) ⟨261648, by rfl⟩ : syracuseStep 697729 = 523297) (by norm_num)
theorem B828821 : Blo 550806 828821 := bbase (se 6 (by rfl) ⟨19425, by rfl⟩ : syracuseStep 828821 = 38851) (by norm_num)
theorem B828845 : Blo 550806 828845 := bbase (se 3 (by rfl) ⟨155408, by rfl⟩ : syracuseStep 828845 = 310817) (by norm_num)
theorem B828869 : Blo 550806 828869 := bbase (se 4 (by rfl) ⟨77706, by rfl⟩ : syracuseStep 828869 = 155413) (by norm_num)
theorem B828893 : Blo 550806 828893 := bbase (se 3 (by rfl) ⟨155417, by rfl⟩ : syracuseStep 828893 = 310835) (by norm_num)
theorem B697825 : Blo 550806 697825 := bbase (se 2 (by rfl) ⟨261684, by rfl⟩ : syracuseStep 697825 = 523369) (by norm_num)
theorem B828917 : Blo 550806 828917 := bbase (se 5 (by rfl) ⟨38855, by rfl⟩ : syracuseStep 828917 = 77711) (by norm_num)
theorem B828941 : Blo 550806 828941 := bbase (se 3 (by rfl) ⟨155426, by rfl⟩ : syracuseStep 828941 = 310853) (by norm_num)
theorem B828965 : Blo 550806 828965 := bbase (se 4 (by rfl) ⟨77715, by rfl⟩ : syracuseStep 828965 = 155431) (by norm_num)
theorem B828989 : Blo 550806 828989 := bbase (se 3 (by rfl) ⟨155435, by rfl⟩ : syracuseStep 828989 = 310871) (by norm_num)
theorem B829013 : Blo 550806 829013 := bbase (se 8 (by rfl) ⟨4857, by rfl⟩ : syracuseStep 829013 = 9715) (by norm_num)
theorem B829037 : Blo 550806 829037 := bbase (se 3 (by rfl) ⟨155444, by rfl⟩ : syracuseStep 829037 = 310889) (by norm_num)
theorem B992893 : Blo 550806 992893 := bbase (se 3 (by rfl) ⟨186167, by rfl⟩ : syracuseStep 992893 = 372335) (by norm_num)
theorem B829061 : Blo 550806 829061 := bbase (se 4 (by rfl) ⟨77724, by rfl⟩ : syracuseStep 829061 = 155449) (by norm_num)
theorem B697997 : Blo 550806 697997 := bbase (se 3 (by rfl) ⟨130874, by rfl⟩ : syracuseStep 697997 = 261749) (by norm_num)
theorem B829085 : Blo 550806 829085 := bbase (se 3 (by rfl) ⟨155453, by rfl⟩ : syracuseStep 829085 = 310907) (by norm_num)
theorem B2369189 : Blo 550806 2369189 := bbase (se 4 (by rfl) ⟨222111, by rfl⟩ : syracuseStep 2369189 = 444223) (by norm_num)
theorem B829109 : Blo 550806 829109 := bbase (se 5 (by rfl) ⟨38864, by rfl⟩ : syracuseStep 829109 = 77729) (by norm_num)
theorem B698053 : Blo 550806 698053 := bbase (se 4 (by rfl) ⟨65442, by rfl⟩ : syracuseStep 698053 = 130885) (by norm_num)
theorem B829133 : Blo 550806 829133 := bbase (se 3 (by rfl) ⟨155462, by rfl⟩ : syracuseStep 829133 = 310925) (by norm_num)
theorem B829157 : Blo 550806 829157 := bbase (se 4 (by rfl) ⟨77733, by rfl⟩ : syracuseStep 829157 = 155467) (by norm_num)
theorem B829181 : Blo 550806 829181 := bbase (se 3 (by rfl) ⟨155471, by rfl⟩ : syracuseStep 829181 = 310943) (by norm_num)
theorem B829205 : Blo 550806 829205 := bbase (se 6 (by rfl) ⟨19434, by rfl⟩ : syracuseStep 829205 = 38869) (by norm_num)
theorem B698149 : Blo 550806 698149 := bbase (se 4 (by rfl) ⟨65451, by rfl⟩ : syracuseStep 698149 = 130903) (by norm_num)
theorem B829229 : Blo 550806 829229 := bbase (se 3 (by rfl) ⟨155480, by rfl⟩ : syracuseStep 829229 = 310961) (by norm_num)
theorem B829253 : Blo 550806 829253 := bbase (se 4 (by rfl) ⟨77742, by rfl⟩ : syracuseStep 829253 = 155485) (by norm_num)
theorem B796493 : Blo 550806 796493 := bbase (se 3 (by rfl) ⟨149342, by rfl⟩ : syracuseStep 796493 = 298685) (by norm_num)
theorem B829277 : Blo 550806 829277 := bbase (se 3 (by rfl) ⟨155489, by rfl⟩ : syracuseStep 829277 = 310979) (by norm_num)
theorem B1124189 : Blo 550806 1124189 := bbase (se 3 (by rfl) ⟨210785, by rfl⟩ : syracuseStep 1124189 = 421571) (by norm_num)
theorem B829301 : Blo 550806 829301 := bbase (se 5 (by rfl) ⟨38873, by rfl⟩ : syracuseStep 829301 = 77747) (by norm_num)
theorem B1124221 : Blo 550806 1124221 := bbase (se 3 (by rfl) ⟨210791, by rfl⟩ : syracuseStep 1124221 = 421583) (by norm_num)
theorem B829325 : Blo 550806 829325 := bbase (se 3 (by rfl) ⟨155498, by rfl⟩ : syracuseStep 829325 = 310997) (by norm_num)
theorem B993181 : Blo 550806 993181 := bbase (se 3 (by rfl) ⟨186221, by rfl⟩ : syracuseStep 993181 = 372443) (by norm_num)
theorem B829349 : Blo 550806 829349 := bbase (se 4 (by rfl) ⟨77751, by rfl⟩ : syracuseStep 829349 = 155503) (by norm_num)
theorem B829373 : Blo 550806 829373 := bbase (se 3 (by rfl) ⟨155507, by rfl⟩ : syracuseStep 829373 = 311015) (by norm_num)
theorem B698321 : Blo 550806 698321 := bbase (se 2 (by rfl) ⟨261870, by rfl⟩ : syracuseStep 698321 = 523741) (by norm_num)
theorem B829397 : Blo 550806 829397 := bbase (se 7 (by rfl) ⟨9719, by rfl⟩ : syracuseStep 829397 = 19439) (by norm_num)
theorem B829421 : Blo 550806 829421 := bbase (se 3 (by rfl) ⟨155516, by rfl⟩ : syracuseStep 829421 = 311033) (by norm_num)
theorem B829445 : Blo 550806 829445 := bbase (se 4 (by rfl) ⟨77760, by rfl⟩ : syracuseStep 829445 = 155521) (by norm_num)
theorem B698377 : Blo 550806 698377 := bbase (se 2 (by rfl) ⟨261891, by rfl⟩ : syracuseStep 698377 = 523783) (by norm_num)
theorem B829469 : Blo 550806 829469 := bbase (se 3 (by rfl) ⟨155525, by rfl⟩ : syracuseStep 829469 = 311051) (by norm_num)
theorem B829493 : Blo 550806 829493 := bbase (se 5 (by rfl) ⟨38882, by rfl⟩ : syracuseStep 829493 = 77765) (by norm_num)
theorem B829517 : Blo 550806 829517 := bbase (se 3 (by rfl) ⟨155534, by rfl⟩ : syracuseStep 829517 = 311069) (by norm_num)
theorem B829541 : Blo 550806 829541 := bbase (se 4 (by rfl) ⟨77769, by rfl⟩ : syracuseStep 829541 = 155539) (by norm_num)
theorem B698473 : Blo 550806 698473 := bbase (se 2 (by rfl) ⟨261927, by rfl⟩ : syracuseStep 698473 = 523855) (by norm_num)
theorem B829565 : Blo 550806 829565 := bbase (se 3 (by rfl) ⟨155543, by rfl⟩ : syracuseStep 829565 = 311087) (by norm_num)
theorem B829589 : Blo 550806 829589 := bbase (se 6 (by rfl) ⟨19443, by rfl⟩ : syracuseStep 829589 = 38887) (by norm_num)
theorem B829613 : Blo 550806 829613 := bbase (se 3 (by rfl) ⟨155552, by rfl⟩ : syracuseStep 829613 = 311105) (by norm_num)
theorem B829637 : Blo 550806 829637 := bbase (se 4 (by rfl) ⟨77778, by rfl⟩ : syracuseStep 829637 = 155557) (by norm_num)
theorem B829661 : Blo 550806 829661 := bbase (se 3 (by rfl) ⟨155561, by rfl⟩ : syracuseStep 829661 = 311123) (by norm_num)
theorem B829685 : Blo 550806 829685 := bbase (se 5 (by rfl) ⟨38891, by rfl⟩ : syracuseStep 829685 = 77783) (by norm_num)
theorem B829709 : Blo 550806 829709 := bbase (se 3 (by rfl) ⟨155570, by rfl⟩ : syracuseStep 829709 = 311141) (by norm_num)
theorem B698645 : Blo 550806 698645 := bbase (se 6 (by rfl) ⟨16374, by rfl⟩ : syracuseStep 698645 = 32749) (by norm_num)
theorem B829733 : Blo 550806 829733 := bbase (se 4 (by rfl) ⟨77787, by rfl⟩ : syracuseStep 829733 = 155575) (by norm_num)
theorem B829757 : Blo 550806 829757 := bbase (se 3 (by rfl) ⟨155579, by rfl⟩ : syracuseStep 829757 = 311159) (by norm_num)
theorem B698701 : Blo 550806 698701 := bbase (se 3 (by rfl) ⟨131006, by rfl⟩ : syracuseStep 698701 = 262013) (by norm_num)
theorem B829781 : Blo 550806 829781 := bbase (se 10 (by rfl) ⟨1215, by rfl⟩ : syracuseStep 829781 = 2431) (by norm_num)
theorem B829805 : Blo 550806 829805 := bbase (se 3 (by rfl) ⟨155588, by rfl⟩ : syracuseStep 829805 = 311177) (by norm_num)
theorem B829829 : Blo 550806 829829 := bbase (se 4 (by rfl) ⟨77796, by rfl⟩ : syracuseStep 829829 = 155593) (by norm_num)
theorem B665993 : Blo 550806 665993 := bbase (se 2 (by rfl) ⟨249747, by rfl⟩ : syracuseStep 665993 = 499495) (by norm_num)
theorem B829853 : Blo 550806 829853 := bbase (se 3 (by rfl) ⟨155597, by rfl⟩ : syracuseStep 829853 = 311195) (by norm_num)
theorem B698797 : Blo 550806 698797 := bbase (se 3 (by rfl) ⟨131024, by rfl⟩ : syracuseStep 698797 = 262049) (by norm_num)
theorem B2795957 : Blo 550806 2795957 := bbase (se 5 (by rfl) ⟨131060, by rfl⟩ : syracuseStep 2795957 = 262121) (by norm_num)
theorem B829877 : Blo 550806 829877 := bbase (se 5 (by rfl) ⟨38900, by rfl⟩ : syracuseStep 829877 = 77801) (by norm_num)
theorem B829901 : Blo 550806 829901 := bbase (se 3 (by rfl) ⟨155606, by rfl⟩ : syracuseStep 829901 = 311213) (by norm_num)
theorem B829925 : Blo 550806 829925 := bbase (se 4 (by rfl) ⟨77805, by rfl⟩ : syracuseStep 829925 = 155611) (by norm_num)
theorem B829949 : Blo 550806 829949 := bbase (se 3 (by rfl) ⟨155615, by rfl⟩ : syracuseStep 829949 = 311231) (by norm_num)
theorem B829973 : Blo 550806 829973 := bbase (se 6 (by rfl) ⟨19452, by rfl⟩ : syracuseStep 829973 = 38905) (by norm_num)
theorem B829997 : Blo 550806 829997 := bbase (se 3 (by rfl) ⟨155624, by rfl⟩ : syracuseStep 829997 = 311249) (by norm_num)
theorem B830021 : Blo 550806 830021 := bbase (se 4 (by rfl) ⟨77814, by rfl⟩ : syracuseStep 830021 = 155629) (by norm_num)
theorem B666181 : Blo 550806 666181 := bbase (se 4 (by rfl) ⟨62454, by rfl⟩ : syracuseStep 666181 = 124909) (by norm_num)
theorem B698969 : Blo 550806 698969 := bbase (se 2 (by rfl) ⟨262113, by rfl⟩ : syracuseStep 698969 = 524227) (by norm_num)
theorem B830045 : Blo 550806 830045 := bbase (se 3 (by rfl) ⟨155633, by rfl⟩ : syracuseStep 830045 = 311267) (by norm_num)
theorem B830069 : Blo 550806 830069 := bbase (se 5 (by rfl) ⟨38909, by rfl⟩ : syracuseStep 830069 = 77819) (by norm_num)
theorem B830093 : Blo 550806 830093 := bbase (se 3 (by rfl) ⟨155642, by rfl⟩ : syracuseStep 830093 = 311285) (by norm_num)
theorem B699025 : Blo 550806 699025 := bbase (se 2 (by rfl) ⟨262134, by rfl⟩ : syracuseStep 699025 = 524269) (by norm_num)
theorem B830117 : Blo 550806 830117 := bbase (se 4 (by rfl) ⟨77823, by rfl⟩ : syracuseStep 830117 = 155647) (by norm_num)
theorem B993973 : Blo 550806 993973 := bbase (se 5 (by rfl) ⟨46592, by rfl⟩ : syracuseStep 993973 = 93185) (by norm_num)
theorem B830141 : Blo 550806 830141 := bbase (se 3 (by rfl) ⟨155651, by rfl⟩ : syracuseStep 830141 = 311303) (by norm_num)
theorem B830165 : Blo 550806 830165 := bbase (se 7 (by rfl) ⟨9728, by rfl⟩ : syracuseStep 830165 = 19457) (by norm_num)
theorem B830189 : Blo 550806 830189 := bbase (se 3 (by rfl) ⟨155660, by rfl⟩ : syracuseStep 830189 = 311321) (by norm_num)
theorem B699121 : Blo 550806 699121 := bbase (se 2 (by rfl) ⟨262170, by rfl⟩ : syracuseStep 699121 = 524341) (by norm_num)
theorem B830213 : Blo 550806 830213 := bbase (se 4 (by rfl) ⟨77832, by rfl⟩ : syracuseStep 830213 = 155665) (by norm_num)
theorem B830237 : Blo 550806 830237 := bbase (se 3 (by rfl) ⟨155669, by rfl⟩ : syracuseStep 830237 = 311339) (by norm_num)
theorem B666397 : Blo 550806 666397 := bbase (se 3 (by rfl) ⟨124949, by rfl⟩ : syracuseStep 666397 = 249899) (by norm_num)
theorem B895789 : Blo 550806 895789 := bbase (se 3 (by rfl) ⟨167960, by rfl⟩ : syracuseStep 895789 = 335921) (by norm_num)
theorem B830261 : Blo 550806 830261 := bbase (se 5 (by rfl) ⟨38918, by rfl⟩ : syracuseStep 830261 = 77837) (by norm_num)
theorem B994117 : Blo 550806 994117 := bbase (se 4 (by rfl) ⟨93198, by rfl⟩ : syracuseStep 994117 = 186397) (by norm_num)
theorem B830285 : Blo 550806 830285 := bbase (se 3 (by rfl) ⟨155678, by rfl⟩ : syracuseStep 830285 = 311357) (by norm_num)
theorem B830309 : Blo 550806 830309 := bbase (se 4 (by rfl) ⟨77841, by rfl⟩ : syracuseStep 830309 = 155683) (by norm_num)
theorem B830333 : Blo 550806 830333 := bbase (se 3 (by rfl) ⟨155687, by rfl⟩ : syracuseStep 830333 = 311375) (by norm_num)
theorem B830357 : Blo 550806 830357 := bbase (se 6 (by rfl) ⟨19461, by rfl⟩ : syracuseStep 830357 = 38923) (by norm_num)
theorem B699293 : Blo 550806 699293 := bbase (se 3 (by rfl) ⟨131117, by rfl⟩ : syracuseStep 699293 = 262235) (by norm_num)
theorem B830381 : Blo 550806 830381 := bbase (se 3 (by rfl) ⟨155696, by rfl⟩ : syracuseStep 830381 = 311393) (by norm_num)
theorem B830405 : Blo 550806 830405 := bbase (se 4 (by rfl) ⟨77850, by rfl⟩ : syracuseStep 830405 = 155701) (by norm_num)
theorem B1092557 : Blo 550806 1092557 := bbase (se 3 (by rfl) ⟨204854, by rfl⟩ : syracuseStep 1092557 = 409709) (by norm_num)
theorem B699349 : Blo 550806 699349 := bbase (se 7 (by rfl) ⟨8195, by rfl⟩ : syracuseStep 699349 = 16391) (by norm_num)
theorem B830429 : Blo 550806 830429 := bbase (se 3 (by rfl) ⟨155705, by rfl⟩ : syracuseStep 830429 = 311411) (by norm_num)
theorem B994277 : Blo 550806 994277 := bbase (se 4 (by rfl) ⟨93213, by rfl⟩ : syracuseStep 994277 = 186427) (by norm_num)
theorem B830453 : Blo 550806 830453 := bbase (se 5 (by rfl) ⟨38927, by rfl⟩ : syracuseStep 830453 = 77855) (by norm_num)
theorem B1518581 : Blo 550806 1518581 := bbase (se 5 (by rfl) ⟨71183, by rfl⟩ : syracuseStep 1518581 = 142367) (by norm_num)
theorem B830477 : Blo 550806 830477 := bbase (se 3 (by rfl) ⟨155714, by rfl⟩ : syracuseStep 830477 = 311429) (by norm_num)
theorem B830501 : Blo 550806 830501 := bbase (se 4 (by rfl) ⟨77859, by rfl⟩ : syracuseStep 830501 = 155719) (by norm_num)
theorem B994349 : Blo 550806 994349 := bbase (se 3 (by rfl) ⟨186440, by rfl⟩ : syracuseStep 994349 = 372881) (by norm_num)
theorem B699445 : Blo 550806 699445 := bbase (se 5 (by rfl) ⟨32786, by rfl⟩ : syracuseStep 699445 = 65573) (by norm_num)
theorem B830525 : Blo 550806 830525 := bbase (se 3 (by rfl) ⟨155723, by rfl⟩ : syracuseStep 830525 = 311447) (by norm_num)
theorem B830549 : Blo 550806 830549 := bbase (se 8 (by rfl) ⟨4866, by rfl⟩ : syracuseStep 830549 = 9733) (by norm_num)
theorem B830573 : Blo 550806 830573 := bbase (se 3 (by rfl) ⟨155732, by rfl⟩ : syracuseStep 830573 = 311465) (by norm_num)
theorem B830597 : Blo 550806 830597 := bbase (se 4 (by rfl) ⟨77868, by rfl⟩ : syracuseStep 830597 = 155737) (by norm_num)
theorem B830621 : Blo 550806 830621 := bbase (se 3 (by rfl) ⟨155741, by rfl⟩ : syracuseStep 830621 = 311483) (by norm_num)
theorem B830645 : Blo 550806 830645 := bbase (se 5 (by rfl) ⟨38936, by rfl⟩ : syracuseStep 830645 = 77873) (by norm_num)
theorem B2829509 : Blo 550806 2829509 := bbase (se 4 (by rfl) ⟨265266, by rfl⟩ : syracuseStep 2829509 = 530533) (by norm_num)
theorem B830669 : Blo 550806 830669 := bbase (se 3 (by rfl) ⟨155750, by rfl⟩ : syracuseStep 830669 = 311501) (by norm_num)
theorem B6302933 : Blo 550806 6302933 := bbase (se 7 (by rfl) ⟨73862, by rfl⟩ : syracuseStep 6302933 = 147725) (by norm_num)
theorem B699617 : Blo 550806 699617 := bbase (se 2 (by rfl) ⟨262356, by rfl⟩ : syracuseStep 699617 = 524713) (by norm_num)
theorem B830693 : Blo 550806 830693 := bbase (se 4 (by rfl) ⟨77877, by rfl⟩ : syracuseStep 830693 = 155755) (by norm_num)
theorem B1420525 : Blo 550806 1420525 := bbase (se 3 (by rfl) ⟨266348, by rfl⟩ : syracuseStep 1420525 = 532697) (by norm_num)
theorem B830717 : Blo 550806 830717 := bbase (se 3 (by rfl) ⟨155759, by rfl⟩ : syracuseStep 830717 = 311519) (by norm_num)
theorem B830741 : Blo 550806 830741 := bbase (se 6 (by rfl) ⟨19470, by rfl⟩ : syracuseStep 830741 = 38941) (by norm_num)
theorem B699673 : Blo 550806 699673 := bbase (se 2 (by rfl) ⟨262377, by rfl⟩ : syracuseStep 699673 = 524755) (by norm_num)
theorem B830765 : Blo 550806 830765 := bbase (se 3 (by rfl) ⟨155768, by rfl⟩ : syracuseStep 830765 = 311537) (by norm_num)
theorem B830789 : Blo 550806 830789 := bbase (se 4 (by rfl) ⟨77886, by rfl⟩ : syracuseStep 830789 = 155773) (by norm_num)
theorem B830813 : Blo 550806 830813 := bbase (se 3 (by rfl) ⟨155777, by rfl⟩ : syracuseStep 830813 = 311555) (by norm_num)
theorem B830837 : Blo 550806 830837 := bbase (se 5 (by rfl) ⟨38945, by rfl⟩ : syracuseStep 830837 = 77891) (by norm_num)
theorem B699769 : Blo 550806 699769 := bbase (se 2 (by rfl) ⟨262413, by rfl⟩ : syracuseStep 699769 = 524827) (by norm_num)
theorem B830861 : Blo 550806 830861 := bbase (se 3 (by rfl) ⟨155786, by rfl⟩ : syracuseStep 830861 = 311573) (by norm_num)
theorem B830885 : Blo 550806 830885 := bbase (se 4 (by rfl) ⟨77895, by rfl⟩ : syracuseStep 830885 = 155791) (by norm_num)
theorem B830909 : Blo 550806 830909 := bbase (se 3 (by rfl) ⟨155795, by rfl⟩ : syracuseStep 830909 = 311591) (by norm_num)
theorem B830933 : Blo 550806 830933 := bbase (se 7 (by rfl) ⟨9737, by rfl⟩ : syracuseStep 830933 = 19475) (by norm_num)
theorem B830957 : Blo 550806 830957 := bbase (se 3 (by rfl) ⟨155804, by rfl⟩ : syracuseStep 830957 = 311609) (by norm_num)
theorem B830981 : Blo 550806 830981 := bbase (se 4 (by rfl) ⟨77904, by rfl⟩ : syracuseStep 830981 = 155809) (by norm_num)
theorem B831005 : Blo 550806 831005 := bbase (se 3 (by rfl) ⟨155813, by rfl⟩ : syracuseStep 831005 = 311627) (by norm_num)
theorem B699941 : Blo 550806 699941 := bbase (se 4 (by rfl) ⟨65619, by rfl⟩ : syracuseStep 699941 = 131239) (by norm_num)
theorem B831029 : Blo 550806 831029 := bbase (se 5 (by rfl) ⟨38954, by rfl⟩ : syracuseStep 831029 = 77909) (by norm_num)
theorem B831053 : Blo 550806 831053 := bbase (se 3 (by rfl) ⟨155822, by rfl⟩ : syracuseStep 831053 = 311645) (by norm_num)
theorem B699997 : Blo 550806 699997 := bbase (se 3 (by rfl) ⟨131249, by rfl⟩ : syracuseStep 699997 = 262499) (by norm_num)
theorem B831077 : Blo 550806 831077 := bbase (se 4 (by rfl) ⟨77913, by rfl⟩ : syracuseStep 831077 = 155827) (by norm_num)
theorem B831101 : Blo 550806 831101 := bbase (se 3 (by rfl) ⟨155831, by rfl⟩ : syracuseStep 831101 = 311663) (by norm_num)
theorem B831125 : Blo 550806 831125 := bbase (se 6 (by rfl) ⟨19479, by rfl⟩ : syracuseStep 831125 = 38959) (by norm_num)
theorem B831149 : Blo 550806 831149 := bbase (se 3 (by rfl) ⟨155840, by rfl⟩ : syracuseStep 831149 = 311681) (by norm_num)
theorem B700093 : Blo 550806 700093 := bbase (se 3 (by rfl) ⟨131267, by rfl⟩ : syracuseStep 700093 = 262535) (by norm_num)
theorem B2797253 : Blo 550806 2797253 := bbase (se 4 (by rfl) ⟨262242, by rfl⟩ : syracuseStep 2797253 = 524485) (by norm_num)
theorem B831173 : Blo 550806 831173 := bbase (se 4 (by rfl) ⟨77922, by rfl⟩ : syracuseStep 831173 = 155845) (by norm_num)
theorem B831197 : Blo 550806 831197 := bbase (se 3 (by rfl) ⟨155849, by rfl⟩ : syracuseStep 831197 = 311699) (by norm_num)
theorem B831221 : Blo 550806 831221 := bbase (se 5 (by rfl) ⟨38963, by rfl⟩ : syracuseStep 831221 = 77927) (by norm_num)
theorem B929549 : Blo 550806 929549 := bbase (se 3 (by rfl) ⟨174290, by rfl⟩ : syracuseStep 929549 = 348581) (by norm_num)
theorem B831245 : Blo 550806 831245 := bbase (se 3 (by rfl) ⟨155858, by rfl⟩ : syracuseStep 831245 = 311717) (by norm_num)
theorem B1421077 : Blo 550806 1421077 := bbase (se 6 (by rfl) ⟨33306, by rfl⟩ : syracuseStep 1421077 = 66613) (by norm_num)
theorem B831269 : Blo 550806 831269 := bbase (se 4 (by rfl) ⟨77931, by rfl⟩ : syracuseStep 831269 = 155863) (by norm_num)
theorem B831293 : Blo 550806 831293 := bbase (se 3 (by rfl) ⟨155867, by rfl⟩ : syracuseStep 831293 = 311735) (by norm_num)
theorem B3977045 : Blo 550806 3977045 := bbase (se 9 (by rfl) ⟨11651, by rfl⟩ : syracuseStep 3977045 = 23303) (by norm_num)
theorem B831317 : Blo 550806 831317 := bbase (se 9 (by rfl) ⟨2435, by rfl⟩ : syracuseStep 831317 = 4871) (by norm_num)
theorem B700265 : Blo 550806 700265 := bbase (se 2 (by rfl) ⟨262599, by rfl⟩ : syracuseStep 700265 = 525199) (by norm_num)
theorem B831341 : Blo 550806 831341 := bbase (se 3 (by rfl) ⟨155876, by rfl⟩ : syracuseStep 831341 = 311753) (by norm_num)
theorem B831365 : Blo 550806 831365 := bbase (se 4 (by rfl) ⟨77940, by rfl⟩ : syracuseStep 831365 = 155881) (by norm_num)
theorem B929677 : Blo 550806 929677 := bbase (se 3 (by rfl) ⟨174314, by rfl⟩ : syracuseStep 929677 = 348629) (by norm_num)
theorem B831389 : Blo 550806 831389 := bbase (se 3 (by rfl) ⟨155885, by rfl⟩ : syracuseStep 831389 = 311771) (by norm_num)
theorem B700321 : Blo 550806 700321 := bbase (se 2 (by rfl) ⟨262620, by rfl⟩ : syracuseStep 700321 = 525241) (by norm_num)
theorem B831413 : Blo 550806 831413 := bbase (se 5 (by rfl) ⟨38972, by rfl⟩ : syracuseStep 831413 = 77945) (by norm_num)
theorem B831437 : Blo 550806 831437 := bbase (se 3 (by rfl) ⟨155894, by rfl⟩ : syracuseStep 831437 = 311789) (by norm_num)
theorem B1683413 : Blo 550806 1683413 := bbase (se 7 (by rfl) ⟨19727, by rfl⟩ : syracuseStep 1683413 = 39455) (by norm_num)
theorem B929765 : Blo 550806 929765 := bbase (se 4 (by rfl) ⟨87165, by rfl⟩ : syracuseStep 929765 = 174331) (by norm_num)
theorem B831461 : Blo 550806 831461 := bbase (se 4 (by rfl) ⟨77949, by rfl⟩ : syracuseStep 831461 = 155899) (by norm_num)
theorem B831485 : Blo 550806 831485 := bbase (se 3 (by rfl) ⟨155903, by rfl⟩ : syracuseStep 831485 = 311807) (by norm_num)
theorem B700417 : Blo 550806 700417 := bbase (se 2 (by rfl) ⟨262656, by rfl⟩ : syracuseStep 700417 = 525313) (by norm_num)
theorem B831509 : Blo 550806 831509 := bbase (se 6 (by rfl) ⟨19488, by rfl⟩ : syracuseStep 831509 = 38977) (by norm_num)
theorem B995357 : Blo 550806 995357 := bbase (se 3 (by rfl) ⟨186629, by rfl⟩ : syracuseStep 995357 = 373259) (by norm_num)
theorem B831533 : Blo 550806 831533 := bbase (se 3 (by rfl) ⟨155912, by rfl⟩ : syracuseStep 831533 = 311825) (by norm_num)
theorem B831557 : Blo 550806 831557 := bbase (se 4 (by rfl) ⟨77958, by rfl⟩ : syracuseStep 831557 = 155917) (by norm_num)
theorem B1421405 : Blo 550806 1421405 := bbase (se 3 (by rfl) ⟨266513, by rfl⟩ : syracuseStep 1421405 = 533027) (by norm_num)
theorem B831581 : Blo 550806 831581 := bbase (se 3 (by rfl) ⟨155921, by rfl⟩ : syracuseStep 831581 = 311843) (by norm_num)
theorem B929893 : Blo 550806 929893 := bbase (se 4 (by rfl) ⟨87177, by rfl⟩ : syracuseStep 929893 = 174355) (by norm_num)
theorem B3977333 : Blo 550806 3977333 := bbase (se 5 (by rfl) ⟨186437, by rfl⟩ : syracuseStep 3977333 = 372875) (by norm_num)
theorem B831605 : Blo 550806 831605 := bbase (se 5 (by rfl) ⟨38981, by rfl⟩ : syracuseStep 831605 = 77963) (by norm_num)
theorem B831629 : Blo 550806 831629 := bbase (se 3 (by rfl) ⟨155930, by rfl⟩ : syracuseStep 831629 = 311861) (by norm_num)
theorem B897173 : Blo 550806 897173 := bbase (se 6 (by rfl) ⟨21027, by rfl⟩ : syracuseStep 897173 = 42055) (by norm_num)
theorem B831653 : Blo 550806 831653 := bbase (se 4 (by rfl) ⟨77967, by rfl⟩ : syracuseStep 831653 = 155935) (by norm_num)
theorem B995501 : Blo 550806 995501 := bbase (se 3 (by rfl) ⟨186656, by rfl⟩ : syracuseStep 995501 = 373313) (by norm_num)
theorem B700589 : Blo 550806 700589 := bbase (se 3 (by rfl) ⟨131360, by rfl⟩ : syracuseStep 700589 = 262721) (by norm_num)
theorem B929981 : Blo 550806 929981 := bbase (se 3 (by rfl) ⟨174371, by rfl⟩ : syracuseStep 929981 = 348743) (by norm_num)
theorem B831677 : Blo 550806 831677 := bbase (se 3 (by rfl) ⟨155939, by rfl⟩ : syracuseStep 831677 = 311879) (by norm_num)
theorem B831701 : Blo 550806 831701 := bbase (se 7 (by rfl) ⟨9746, by rfl⟩ : syracuseStep 831701 = 19493) (by norm_num)
theorem B700645 : Blo 550806 700645 := bbase (se 4 (by rfl) ⟨65685, by rfl⟩ : syracuseStep 700645 = 131371) (by norm_num)
theorem B831725 : Blo 550806 831725 := bbase (se 3 (by rfl) ⟨155948, by rfl⟩ : syracuseStep 831725 = 311897) (by norm_num)
theorem B995581 : Blo 550806 995581 := bbase (se 3 (by rfl) ⟨186671, by rfl⟩ : syracuseStep 995581 = 373343) (by norm_num)
theorem B831749 : Blo 550806 831749 := bbase (se 4 (by rfl) ⟨77976, by rfl⟩ : syracuseStep 831749 = 155953) (by norm_num)
theorem B831773 : Blo 550806 831773 := bbase (se 3 (by rfl) ⟨155957, by rfl⟩ : syracuseStep 831773 = 311915) (by norm_num)
theorem B831797 : Blo 550806 831797 := bbase (se 5 (by rfl) ⟨38990, by rfl⟩ : syracuseStep 831797 = 77981) (by norm_num)
theorem B930109 : Blo 550806 930109 := bbase (se 3 (by rfl) ⟨174395, by rfl⟩ : syracuseStep 930109 = 348791) (by norm_num)
theorem B700741 : Blo 550806 700741 := bbase (se 4 (by rfl) ⟨65694, by rfl⟩ : syracuseStep 700741 = 131389) (by norm_num)
theorem B831821 : Blo 550806 831821 := bbase (se 3 (by rfl) ⟨155966, by rfl⟩ : syracuseStep 831821 = 311933) (by norm_num)
theorem B831845 : Blo 550806 831845 := bbase (se 4 (by rfl) ⟨77985, by rfl⟩ : syracuseStep 831845 = 155971) (by norm_num)
theorem B2240885 : Blo 550806 2240885 := bbase (se 5 (by rfl) ⟨105041, by rfl⟩ : syracuseStep 2240885 = 210083) (by norm_num)
theorem B831869 : Blo 550806 831869 := bbase (se 3 (by rfl) ⟨155975, by rfl⟩ : syracuseStep 831869 = 311951) (by norm_num)
theorem B930197 : Blo 550806 930197 := bbase (se 6 (by rfl) ⟨21801, by rfl⟩ : syracuseStep 930197 = 43603) (by norm_num)
theorem B831893 : Blo 550806 831893 := bbase (se 6 (by rfl) ⟨19497, by rfl⟩ : syracuseStep 831893 = 38995) (by norm_num)
theorem B831917 : Blo 550806 831917 := bbase (se 3 (by rfl) ⟨155984, by rfl⟩ : syracuseStep 831917 = 311969) (by norm_num)
theorem B831941 : Blo 550806 831941 := bbase (se 4 (by rfl) ⟨77994, by rfl⟩ : syracuseStep 831941 = 155989) (by norm_num)
theorem B831965 : Blo 550806 831965 := bbase (se 3 (by rfl) ⟨155993, by rfl⟩ : syracuseStep 831965 = 311987) (by norm_num)
theorem B700913 : Blo 550806 700913 := bbase (se 2 (by rfl) ⟨262842, by rfl⟩ : syracuseStep 700913 = 525685) (by norm_num)
theorem B831989 : Blo 550806 831989 := bbase (se 5 (by rfl) ⟨38999, by rfl⟩ : syracuseStep 831989 = 77999) (by norm_num)
theorem B832013 : Blo 550806 832013 := bbase (se 3 (by rfl) ⟨156002, by rfl⟩ : syracuseStep 832013 = 312005) (by norm_num)
theorem B930325 : Blo 550806 930325 := bbase (se 6 (by rfl) ⟨21804, by rfl⟩ : syracuseStep 930325 = 43609) (by norm_num)
theorem B832037 : Blo 550806 832037 := bbase (se 4 (by rfl) ⟨78003, by rfl⟩ : syracuseStep 832037 = 156007) (by norm_num)
theorem B700969 : Blo 550806 700969 := bbase (se 2 (by rfl) ⟨262863, by rfl⟩ : syracuseStep 700969 = 525727) (by norm_num)
theorem B832061 : Blo 550806 832061 := bbase (se 3 (by rfl) ⟨156011, by rfl⟩ : syracuseStep 832061 = 312023) (by norm_num)
theorem B832085 : Blo 550806 832085 := bbase (se 8 (by rfl) ⟨4875, by rfl⟩ : syracuseStep 832085 = 9751) (by norm_num)
theorem B930413 : Blo 550806 930413 := bbase (se 3 (by rfl) ⟨174452, by rfl⟩ : syracuseStep 930413 = 348905) (by norm_num)
theorem B832109 : Blo 550806 832109 := bbase (se 3 (by rfl) ⟨156020, by rfl⟩ : syracuseStep 832109 = 312041) (by norm_num)
theorem B832133 : Blo 550806 832133 := bbase (se 4 (by rfl) ⟨78012, by rfl⟩ : syracuseStep 832133 = 156025) (by norm_num)
theorem B701065 : Blo 550806 701065 := bbase (se 2 (by rfl) ⟨262899, by rfl⟩ : syracuseStep 701065 = 525799) (by norm_num)
theorem B832157 : Blo 550806 832157 := bbase (se 3 (by rfl) ⟨156029, by rfl⟩ : syracuseStep 832157 = 312059) (by norm_num)
theorem B832181 : Blo 550806 832181 := bbase (se 5 (by rfl) ⟨39008, by rfl⟩ : syracuseStep 832181 = 78017) (by norm_num)
theorem B832205 : Blo 550806 832205 := bbase (se 3 (by rfl) ⟨156038, by rfl⟩ : syracuseStep 832205 = 312077) (by norm_num)
theorem B930541 : Blo 550806 930541 := bbase (se 3 (by rfl) ⟨174476, by rfl⟩ : syracuseStep 930541 = 348953) (by norm_num)
theorem B2700053 : Blo 550806 2700053 := bbase (se 6 (by rfl) ⟨63282, by rfl⟩ : syracuseStep 2700053 = 126565) (by norm_num)
theorem B701237 : Blo 550806 701237 := bbase (se 5 (by rfl) ⟨32870, by rfl⟩ : syracuseStep 701237 = 65741) (by norm_num)
theorem B930629 : Blo 550806 930629 := bbase (se 4 (by rfl) ⟨87246, by rfl⟩ : syracuseStep 930629 = 174493) (by norm_num)
theorem B701293 : Blo 550806 701293 := bbase (se 3 (by rfl) ⟨131492, by rfl⟩ : syracuseStep 701293 = 262985) (by norm_num)
theorem B930757 : Blo 550806 930757 := bbase (se 4 (by rfl) ⟨87258, by rfl⟩ : syracuseStep 930757 = 174517) (by norm_num)
theorem B701389 : Blo 550806 701389 := bbase (se 3 (by rfl) ⟨131510, by rfl⟩ : syracuseStep 701389 = 263021) (by norm_num)
theorem B2798549 : Blo 550806 2798549 := bbase (se 7 (by rfl) ⟨32795, by rfl⟩ : syracuseStep 2798549 = 65591) (by norm_num)
theorem B930845 : Blo 550806 930845 := bbase (se 3 (by rfl) ⟨174533, by rfl⟩ : syracuseStep 930845 = 349067) (by norm_num)
theorem B701561 : Blo 550806 701561 := bbase (se 2 (by rfl) ⟨263085, by rfl⟩ : syracuseStep 701561 = 526171) (by norm_num)
theorem B930973 : Blo 550806 930973 := bbase (se 3 (by rfl) ⟨174557, by rfl⟩ : syracuseStep 930973 = 349115) (by norm_num)
theorem B701617 : Blo 550806 701617 := bbase (se 2 (by rfl) ⟨263106, by rfl⟩ : syracuseStep 701617 = 526213) (by norm_num)
theorem B4240565 : Blo 550806 4240565 := bbase (se 5 (by rfl) ⟨198776, by rfl⟩ : syracuseStep 4240565 = 397553) (by norm_num)
theorem B931061 : Blo 550806 931061 := bbase (se 5 (by rfl) ⟨43643, by rfl⟩ : syracuseStep 931061 = 87287) (by norm_num)
theorem B701713 : Blo 550806 701713 := bbase (se 2 (by rfl) ⟨263142, by rfl⟩ : syracuseStep 701713 = 526285) (by norm_num)
theorem B931189 : Blo 550806 931189 := bbase (se 5 (by rfl) ⟨43649, by rfl⟩ : syracuseStep 931189 = 87299) (by norm_num)
theorem B701885 : Blo 550806 701885 := bbase (se 3 (by rfl) ⟨131603, by rfl⟩ : syracuseStep 701885 = 263207) (by norm_num)
theorem B931277 : Blo 550806 931277 := bbase (se 3 (by rfl) ⟨174614, by rfl⟩ : syracuseStep 931277 = 349229) (by norm_num)
theorem B701941 : Blo 550806 701941 := bbase (se 5 (by rfl) ⟨32903, by rfl⟩ : syracuseStep 701941 = 65807) (by norm_num)
theorem B931405 : Blo 550806 931405 := bbase (se 3 (by rfl) ⟨174638, by rfl⟩ : syracuseStep 931405 = 349277) (by norm_num)
theorem B6305365 : Blo 550806 6305365 := bbase (se 8 (by rfl) ⟨36945, by rfl⟩ : syracuseStep 6305365 = 73891) (by norm_num)
theorem B702037 : Blo 550806 702037 := bbase (se 8 (by rfl) ⟨4113, by rfl⟩ : syracuseStep 702037 = 8227) (by norm_num)
theorem B996965 : Blo 550806 996965 := bbase (se 4 (by rfl) ⟨93465, by rfl⟩ : syracuseStep 996965 = 186931) (by norm_num)
theorem B931493 : Blo 550806 931493 := bbase (se 4 (by rfl) ⟨87327, by rfl⟩ : syracuseStep 931493 = 174655) (by norm_num)
theorem B3192533 : Blo 550806 3192533 := bbase (se 7 (by rfl) ⟨37412, by rfl⟩ : syracuseStep 3192533 = 74825) (by norm_num)
theorem B931621 : Blo 550806 931621 := bbase (se 4 (by rfl) ⟨87339, by rfl⟩ : syracuseStep 931621 = 174679) (by norm_num)
theorem B931709 : Blo 550806 931709 := bbase (se 3 (by rfl) ⟨174695, by rfl⟩ : syracuseStep 931709 = 349391) (by norm_num)
theorem B2996149 : Blo 550806 2996149 := bbase (se 5 (by rfl) ⟨140444, by rfl⟩ : syracuseStep 2996149 = 280889) (by norm_num)
theorem B931837 : Blo 550806 931837 := bbase (se 3 (by rfl) ⟨174719, by rfl⟩ : syracuseStep 931837 = 349439) (by norm_num)
theorem B931925 : Blo 550806 931925 := bbase (se 8 (by rfl) ⟨5460, by rfl⟩ : syracuseStep 931925 = 10921) (by norm_num)
theorem B637081 : Blo 550806 637081 := bbase (se 2 (by rfl) ⟨238905, by rfl⟩ : syracuseStep 637081 = 477811) (by norm_num)
theorem B899237 : Blo 550806 899237 := bbase (se 4 (by rfl) ⟨84303, by rfl⟩ : syracuseStep 899237 = 168607) (by norm_num)
theorem B932053 : Blo 550806 932053 := bbase (se 7 (by rfl) ⟨10922, by rfl⟩ : syracuseStep 932053 = 21845) (by norm_num)
theorem B2799845 : Blo 550806 2799845 := bbase (se 4 (by rfl) ⟨262485, by rfl⟩ : syracuseStep 2799845 = 524971) (by norm_num)
theorem B1325317 : Blo 550806 1325317 := bbase (se 4 (by rfl) ⟨124248, by rfl⟩ : syracuseStep 1325317 = 248497) (by norm_num)
theorem B932141 : Blo 550806 932141 := bbase (se 3 (by rfl) ⟨174776, by rfl⟩ : syracuseStep 932141 = 349553) (by norm_num)
theorem B1325413 : Blo 550806 1325413 := bbase (se 4 (by rfl) ⟨124257, by rfl⟩ : syracuseStep 1325413 = 248515) (by norm_num)
theorem B932269 : Blo 550806 932269 := bbase (se 3 (by rfl) ⟨174800, by rfl⟩ : syracuseStep 932269 = 349601) (by norm_num)
theorem B932357 : Blo 550806 932357 := bbase (se 4 (by rfl) ⟨87408, by rfl⟩ : syracuseStep 932357 = 174817) (by norm_num)
theorem B1325605 : Blo 550806 1325605 := bbase (se 4 (by rfl) ⟨124275, by rfl⟩ : syracuseStep 1325605 = 248551) (by norm_num)
theorem B932485 : Blo 550806 932485 := bbase (se 4 (by rfl) ⟨87420, by rfl⟩ : syracuseStep 932485 = 174841) (by norm_num)
theorem B932573 : Blo 550806 932573 := bbase (se 3 (by rfl) ⟨174857, by rfl⟩ : syracuseStep 932573 = 349715) (by norm_num)
theorem B932701 : Blo 550806 932701 := bbase (se 3 (by rfl) ⟨174881, by rfl⟩ : syracuseStep 932701 = 349763) (by norm_num)
theorem B1325933 : Blo 550806 1325933 := bbase (se 3 (by rfl) ⟨248612, by rfl⟩ : syracuseStep 1325933 = 497225) (by norm_num)
theorem B5323637 : Blo 550806 5323637 := bbase (se 5 (by rfl) ⟨249545, by rfl⟩ : syracuseStep 5323637 = 499091) (by norm_num)
theorem B932789 : Blo 550806 932789 := bbase (se 5 (by rfl) ⟨43724, by rfl⟩ : syracuseStep 932789 = 87449) (by norm_num)
theorem B932917 : Blo 550806 932917 := bbase (se 5 (by rfl) ⟨43730, by rfl⟩ : syracuseStep 932917 = 87461) (by norm_num)
theorem B933005 : Blo 550806 933005 := bbase (se 3 (by rfl) ⟨174938, by rfl⟩ : syracuseStep 933005 = 349877) (by norm_num)
theorem B933133 : Blo 550806 933133 := bbase (se 3 (by rfl) ⟨174962, by rfl⟩ : syracuseStep 933133 = 349925) (by norm_num)
theorem B1326365 : Blo 550806 1326365 := bbase (se 3 (by rfl) ⟨248693, by rfl⟩ : syracuseStep 1326365 = 497387) (by norm_num)
theorem B933221 : Blo 550806 933221 := bbase (se 4 (by rfl) ⟨87489, by rfl⟩ : syracuseStep 933221 = 174979) (by norm_num)
theorem B638357 : Blo 550806 638357 := bbase (se 6 (by rfl) ⟨14961, by rfl⟩ : syracuseStep 638357 = 29923) (by norm_num)
theorem B933349 : Blo 550806 933349 := bbase (se 4 (by rfl) ⟨87501, by rfl⟩ : syracuseStep 933349 = 175003) (by norm_num)
theorem B2801141 : Blo 550806 2801141 := bbase (se 5 (by rfl) ⟨131303, by rfl⟩ : syracuseStep 2801141 = 262607) (by norm_num)
theorem B900629 : Blo 550806 900629 := bbase (se 6 (by rfl) ⟨21108, by rfl⟩ : syracuseStep 900629 = 42217) (by norm_num)
theorem B933437 : Blo 550806 933437 := bbase (se 3 (by rfl) ⟨175019, by rfl⟩ : syracuseStep 933437 = 350039) (by norm_num)
theorem B1326701 : Blo 550806 1326701 := bbase (se 3 (by rfl) ⟨248756, by rfl⟩ : syracuseStep 1326701 = 497513) (by norm_num)
theorem B2014901 : Blo 550806 2014901 := bbase (se 5 (by rfl) ⟨94448, by rfl⟩ : syracuseStep 2014901 = 188897) (by norm_num)
theorem B933565 : Blo 550806 933565 := bbase (se 3 (by rfl) ⟨175043, by rfl⟩ : syracuseStep 933565 = 350087) (by norm_num)
theorem B933653 : Blo 550806 933653 := bbase (se 6 (by rfl) ⟨21882, by rfl⟩ : syracuseStep 933653 = 43765) (by norm_num)
theorem B638761 : Blo 550806 638761 := bbase (se 2 (by rfl) ⟨239535, by rfl⟩ : syracuseStep 638761 = 479071) (by norm_num)
theorem B638857 : Blo 550806 638857 := bbase (se 2 (by rfl) ⟨239571, by rfl⟩ : syracuseStep 638857 = 479143) (by norm_num)
theorem B933781 : Blo 550806 933781 := bbase (se 6 (by rfl) ⟨21885, by rfl⟩ : syracuseStep 933781 = 43771) (by norm_num)
theorem B933869 : Blo 550806 933869 := bbase (se 3 (by rfl) ⟨175100, by rfl⟩ : syracuseStep 933869 = 350201) (by norm_num)
theorem B933997 : Blo 550806 933997 := bbase (se 3 (by rfl) ⟨175124, by rfl⟩ : syracuseStep 933997 = 350249) (by norm_num)
theorem B934085 : Blo 550806 934085 := bbase (se 4 (by rfl) ⟨87570, by rfl⟩ : syracuseStep 934085 = 175141) (by norm_num)
theorem B934213 : Blo 550806 934213 := bbase (se 4 (by rfl) ⟨87582, by rfl⟩ : syracuseStep 934213 = 175165) (by norm_num)
theorem B934301 : Blo 550806 934301 := bbase (se 3 (by rfl) ⟨175181, by rfl⟩ : syracuseStep 934301 = 350363) (by norm_num)
theorem B4211189 : Blo 550806 4211189 := bbase (se 5 (by rfl) ⟨197399, by rfl⟩ : syracuseStep 4211189 = 394799) (by norm_num)
theorem B934429 : Blo 550806 934429 := bbase (se 3 (by rfl) ⟨175205, by rfl⟩ : syracuseStep 934429 = 350411) (by norm_num)
theorem B934517 : Blo 550806 934517 := bbase (se 5 (by rfl) ⟨43805, by rfl⟩ : syracuseStep 934517 = 87611) (by norm_num)
theorem B1327757 : Blo 550806 1327757 := bbase (se 3 (by rfl) ⟨248954, by rfl⟩ : syracuseStep 1327757 = 497909) (by norm_num)
theorem B1196765 : Blo 550806 1196765 := bbase (se 3 (by rfl) ⟨224393, by rfl⟩ : syracuseStep 1196765 = 448787) (by norm_num)
theorem B1884917 : Blo 550806 1884917 := bbase (se 5 (by rfl) ⟨88355, by rfl⟩ : syracuseStep 1884917 = 176711) (by norm_num)
theorem B934645 : Blo 550806 934645 := bbase (se 5 (by rfl) ⟨43811, by rfl⟩ : syracuseStep 934645 = 87623) (by norm_num)
theorem B2802437 : Blo 550806 2802437 := bbase (se 4 (by rfl) ⟨262728, by rfl⟩ : syracuseStep 2802437 = 525457) (by norm_num)
theorem B934733 : Blo 550806 934733 := bbase (se 3 (by rfl) ⟨175262, by rfl⟩ : syracuseStep 934733 = 350525) (by norm_num)
theorem B934861 : Blo 550806 934861 := bbase (se 3 (by rfl) ⟨175286, by rfl⟩ : syracuseStep 934861 = 350573) (by norm_num)
theorem B934949 : Blo 550806 934949 := bbase (se 4 (by rfl) ⟨87651, by rfl⟩ : syracuseStep 934949 = 175303) (by norm_num)
theorem B1066117 : Blo 550806 1066117 := bbase (se 4 (by rfl) ⟨99948, by rfl⟩ : syracuseStep 1066117 = 199897) (by norm_num)
theorem B935077 : Blo 550806 935077 := bbase (se 4 (by rfl) ⟨87663, by rfl⟩ : syracuseStep 935077 = 175327) (by norm_num)
theorem B935165 : Blo 550806 935165 := bbase (se 3 (by rfl) ⟨175343, by rfl⟩ : syracuseStep 935165 = 350687) (by norm_num)
theorem B1361197 : Blo 550806 1361197 := bbase (se 3 (by rfl) ⟨255224, by rfl⟩ : syracuseStep 1361197 = 510449) (by norm_num)
theorem B935293 : Blo 550806 935293 := bbase (se 3 (by rfl) ⟨175367, by rfl⟩ : syracuseStep 935293 = 350735) (by norm_num)
theorem B1263053 : Blo 550806 1263053 := bbase (se 3 (by rfl) ⟨236822, by rfl⟩ : syracuseStep 1263053 = 473645) (by norm_num)
theorem B935381 : Blo 550806 935381 := bbase (se 7 (by rfl) ⟨10961, by rfl⟩ : syracuseStep 935381 = 21923) (by norm_num)
theorem B935509 : Blo 550806 935509 := bbase (se 8 (by rfl) ⟨5481, by rfl⟩ : syracuseStep 935509 = 10963) (by norm_num)
theorem B1394293 : Blo 550806 1394293 := bbase (se 5 (by rfl) ⟨65357, by rfl⟩ : syracuseStep 1394293 = 130715) (by norm_num)
theorem B935597 : Blo 550806 935597 := bbase (se 3 (by rfl) ⟨175424, by rfl⟩ : syracuseStep 935597 = 350849) (by norm_num)
theorem B1394405 : Blo 550806 1394405 := bbase (se 4 (by rfl) ⟨130725, by rfl⟩ : syracuseStep 1394405 = 261451) (by norm_num)
theorem B3032821 : Blo 550806 3032821 := bbase (se 5 (by rfl) ⟨142163, by rfl⟩ : syracuseStep 3032821 = 284327) (by norm_num)
theorem B7096085 : Blo 550806 7096085 := bbase (se 6 (by rfl) ⟨166314, by rfl⟩ : syracuseStep 7096085 = 332629) (by norm_num)
theorem B935725 : Blo 550806 935725 := bbase (se 3 (by rfl) ⟨175448, by rfl⟩ : syracuseStep 935725 = 350897) (by norm_num)
theorem B935813 : Blo 550806 935813 := bbase (se 4 (by rfl) ⟨87732, by rfl⟩ : syracuseStep 935813 = 175465) (by norm_num)
theorem B1394597 : Blo 550806 1394597 := bbase (se 4 (by rfl) ⟨130743, by rfl⟩ : syracuseStep 1394597 = 261487) (by norm_num)
theorem B935941 : Blo 550806 935941 := bbase (se 4 (by rfl) ⟨87744, by rfl⟩ : syracuseStep 935941 = 175489) (by norm_num)
theorem B2803733 : Blo 550806 2803733 := bbase (se 6 (by rfl) ⟨65712, by rfl⟩ : syracuseStep 2803733 = 131425) (by norm_num)
theorem B936029 : Blo 550806 936029 := bbase (se 3 (by rfl) ⟨175505, by rfl⟩ : syracuseStep 936029 = 351011) (by norm_num)
theorem B936157 : Blo 550806 936157 := bbase (se 3 (by rfl) ⟨175529, by rfl⟩ : syracuseStep 936157 = 351059) (by norm_num)
theorem B1394941 : Blo 550806 1394941 := bbase (se 3 (by rfl) ⟨261551, by rfl⟩ : syracuseStep 1394941 = 523103) (by norm_num)
theorem B1395053 : Blo 550806 1395053 := bbase (se 3 (by rfl) ⟨261572, by rfl⟩ : syracuseStep 1395053 = 523145) (by norm_num)
theorem B674185 : Blo 550806 674185 := bbase (se 2 (by rfl) ⟨252819, by rfl⟩ : syracuseStep 674185 = 505639) (by norm_num)
theorem B1395245 : Blo 550806 1395245 := bbase (se 3 (by rfl) ⟨261608, by rfl⟩ : syracuseStep 1395245 = 523217) (by norm_num)
theorem B1329949 : Blo 550806 1329949 := bbase (se 3 (by rfl) ⟨249365, by rfl⟩ : syracuseStep 1329949 = 498731) (by norm_num)
theorem B1395589 : Blo 550806 1395589 := bbase (se 4 (by rfl) ⟨130836, by rfl⟩ : syracuseStep 1395589 = 261673) (by norm_num)
theorem B576437 : Blo 550806 576437 := bbase (se 5 (by rfl) ⟨27020, by rfl⟩ : syracuseStep 576437 = 54041) (by norm_num)
theorem B1395701 : Blo 550806 1395701 := bbase (se 5 (by rfl) ⟨65423, by rfl⟩ : syracuseStep 1395701 = 130847) (by norm_num)
theorem B707665 : Blo 550806 707665 := bbase (se 2 (by rfl) ⟨265374, by rfl⟩ : syracuseStep 707665 = 530749) (by norm_num)
theorem B1395893 : Blo 550806 1395893 := bbase (se 5 (by rfl) ⟨65432, by rfl⟩ : syracuseStep 1395893 = 130865) (by norm_num)
theorem B2837701 : Blo 550806 2837701 := bbase (se 4 (by rfl) ⟨266034, by rfl⟩ : syracuseStep 2837701 = 532069) (by norm_num)
theorem B2805029 : Blo 550806 2805029 := bbase (se 4 (by rfl) ⟨262971, by rfl⟩ : syracuseStep 2805029 = 525943) (by norm_num)
theorem B839005 : Blo 550806 839005 := bbase (se 3 (by rfl) ⟨157313, by rfl⟩ : syracuseStep 839005 = 314627) (by norm_num)
theorem B1396237 : Blo 550806 1396237 := bbase (se 3 (by rfl) ⟨261794, by rfl⟩ : syracuseStep 1396237 = 523589) (by norm_num)
theorem B4705877 : Blo 550806 4705877 := bbase (se 8 (by rfl) ⟨27573, by rfl⟩ : syracuseStep 4705877 = 55147) (by norm_num)
theorem B1396349 : Blo 550806 1396349 := bbase (se 3 (by rfl) ⟨261815, by rfl⟩ : syracuseStep 1396349 = 523631) (by norm_num)
theorem B708277 : Blo 550806 708277 := bbase (se 5 (by rfl) ⟨33200, by rfl⟩ : syracuseStep 708277 = 66401) (by norm_num)
theorem B1396541 : Blo 550806 1396541 := bbase (se 3 (by rfl) ⟨261851, by rfl⟩ : syracuseStep 1396541 = 523703) (by norm_num)
theorem B4739093 : Blo 550806 4739093 := bbase (se 6 (by rfl) ⟨111072, by rfl⟩ : syracuseStep 4739093 = 222145) (by norm_num)
theorem B1986677 : Blo 550806 1986677 := bbase (se 5 (by rfl) ⟨93125, by rfl⟩ : syracuseStep 1986677 = 186251) (by norm_num)
theorem B1331333 : Blo 550806 1331333 := bbase (se 4 (by rfl) ⟨124812, by rfl⟩ : syracuseStep 1331333 = 249625) (by norm_num)
theorem B1396885 : Blo 550806 1396885 := bbase (se 6 (by rfl) ⟨32739, by rfl⟩ : syracuseStep 1396885 = 65479) (by norm_num)
theorem B1396997 : Blo 550806 1396997 := bbase (se 4 (by rfl) ⟨130968, by rfl⟩ : syracuseStep 1396997 = 261937) (by norm_num)
theorem B1331525 : Blo 550806 1331525 := bbase (se 4 (by rfl) ⟨124830, by rfl⟩ : syracuseStep 1331525 = 249661) (by norm_num)
theorem B1397189 : Blo 550806 1397189 := bbase (se 4 (by rfl) ⟨130986, by rfl⟩ : syracuseStep 1397189 = 261973) (by norm_num)
theorem B2806325 : Blo 550806 2806325 := bbase (se 5 (by rfl) ⟨131546, by rfl⟩ : syracuseStep 2806325 = 263093) (by norm_num)
theorem B1397533 : Blo 550806 1397533 := bbase (se 3 (by rfl) ⟨262037, by rfl⟩ : syracuseStep 1397533 = 524075) (by norm_num)
theorem B1200973 : Blo 550806 1200973 := bbase (se 3 (by rfl) ⟨225182, by rfl⟩ : syracuseStep 1200973 = 450365) (by norm_num)
theorem B4477781 : Blo 550806 4477781 := bbase (se 9 (by rfl) ⟨13118, by rfl⟩ : syracuseStep 4477781 = 26237) (by norm_num)
theorem B1397645 : Blo 550806 1397645 := bbase (se 3 (by rfl) ⟨262058, by rfl⟩ : syracuseStep 1397645 = 524117) (by norm_num)
theorem B1889173 : Blo 550806 1889173 := bbase (se 6 (by rfl) ⟨44277, by rfl⟩ : syracuseStep 1889173 = 88555) (by norm_num)
theorem B1332293 : Blo 550806 1332293 := bbase (se 4 (by rfl) ⟨124902, by rfl⟩ : syracuseStep 1332293 = 249805) (by norm_num)
theorem B1397837 : Blo 550806 1397837 := bbase (se 3 (by rfl) ⟨262094, by rfl⟩ : syracuseStep 1397837 = 524189) (by norm_num)
theorem B1398181 : Blo 550806 1398181 := bbase (se 4 (by rfl) ⟨131079, by rfl⟩ : syracuseStep 1398181 = 262159) (by norm_num)
theorem B1496485 : Blo 550806 1496485 := bbase (se 4 (by rfl) ⟨140295, by rfl⟩ : syracuseStep 1496485 = 280591) (by norm_num)
theorem B2840021 : Blo 550806 2840021 := bbase (se 7 (by rfl) ⟨33281, by rfl⟩ : syracuseStep 2840021 = 66563) (by norm_num)
theorem B1398293 : Blo 550806 1398293 := bbase (se 6 (by rfl) ⟨32772, by rfl⟩ : syracuseStep 1398293 = 65545) (by norm_num)
theorem B1365581 : Blo 550806 1365581 := bbase (se 3 (by rfl) ⟨256046, by rfl⟩ : syracuseStep 1365581 = 512093) (by norm_num)
theorem B1398485 : Blo 550806 1398485 := bbase (se 7 (by rfl) ⟨16388, by rfl⟩ : syracuseStep 1398485 = 32777) (by norm_num)
theorem B2152213 : Blo 550806 2152213 := bbase (se 6 (by rfl) ⟨50442, by rfl⟩ : syracuseStep 2152213 = 100885) (by norm_num)
theorem B2807621 : Blo 550806 2807621 := bbase (se 4 (by rfl) ⟨263214, by rfl⟩ : syracuseStep 2807621 = 526429) (by norm_num)
theorem B5986325 : Blo 550806 5986325 := bbase (se 6 (by rfl) ⟨140304, by rfl⟩ : syracuseStep 5986325 = 280609) (by norm_num)
theorem B1398829 : Blo 550806 1398829 := bbase (se 3 (by rfl) ⟨262280, by rfl⟩ : syracuseStep 1398829 = 524561) (by norm_num)
theorem B841853 : Blo 550806 841853 := bbase (se 3 (by rfl) ⟨157847, by rfl⟩ : syracuseStep 841853 = 315695) (by norm_num)
theorem B1398941 : Blo 550806 1398941 := bbase (se 3 (by rfl) ⟨262301, by rfl⟩ : syracuseStep 1398941 = 524603) (by norm_num)
theorem B1136933 : Blo 550806 1136933 := bbase (se 4 (by rfl) ⟨106587, by rfl⟩ : syracuseStep 1136933 = 213175) (by norm_num)
theorem B1399133 : Blo 550806 1399133 := bbase (se 3 (by rfl) ⟨262337, by rfl⟩ : syracuseStep 1399133 = 524675) (by norm_num)
theorem B3627413 : Blo 550806 3627413 := bbase (se 6 (by rfl) ⟨85017, by rfl⟩ : syracuseStep 3627413 = 170035) (by norm_num)
theorem B4708853 : Blo 550806 4708853 := bbase (se 5 (by rfl) ⟨220727, by rfl⟩ : syracuseStep 4708853 = 441455) (by norm_num)
theorem B1104389 : Blo 550806 1104389 := bbase (se 4 (by rfl) ⟨103536, by rfl⟩ : syracuseStep 1104389 = 207073) (by norm_num)
theorem B1989157 : Blo 550806 1989157 := bbase (se 4 (by rfl) ⟨186483, by rfl⟩ : syracuseStep 1989157 = 372967) (by norm_num)
theorem B842357 : Blo 550806 842357 := bbase (se 5 (by rfl) ⟨39485, by rfl⟩ : syracuseStep 842357 = 78971) (by norm_num)
theorem B1399477 : Blo 550806 1399477 := bbase (se 5 (by rfl) ⟨65600, by rfl⟩ : syracuseStep 1399477 = 131201) (by norm_num)
theorem B1399589 : Blo 550806 1399589 := bbase (se 4 (by rfl) ⟨131211, by rfl⟩ : syracuseStep 1399589 = 262423) (by norm_num)
theorem B2841413 : Blo 550806 2841413 := bbase (se 4 (by rfl) ⟨266382, by rfl⟩ : syracuseStep 2841413 = 532765) (by norm_num)
theorem B1399781 : Blo 550806 1399781 := bbase (se 4 (by rfl) ⟨131229, by rfl⟩ : syracuseStep 1399781 = 262459) (by norm_num)
theorem B1400125 : Blo 550806 1400125 := bbase (se 3 (by rfl) ⟨262523, by rfl⟩ : syracuseStep 1400125 = 525047) (by norm_num)
theorem B1400237 : Blo 550806 1400237 := bbase (se 3 (by rfl) ⟨262544, by rfl⟩ : syracuseStep 1400237 = 525089) (by norm_num)
theorem B1400429 : Blo 550806 1400429 := bbase (se 3 (by rfl) ⟨262580, by rfl⟩ : syracuseStep 1400429 = 525161) (by norm_num)
theorem B1859381 : Blo 550806 1859381 := bbase (se 5 (by rfl) ⟨87158, by rfl⟩ : syracuseStep 1859381 = 174317) (by norm_num)
theorem B1400773 : Blo 550806 1400773 := bbase (se 4 (by rfl) ⟨131322, by rfl⟩ : syracuseStep 1400773 = 262645) (by norm_num)
theorem B1368029 : Blo 550806 1368029 := bbase (se 3 (by rfl) ⟨256505, by rfl⟩ : syracuseStep 1368029 = 513011) (by norm_num)
theorem B3137525 : Blo 550806 3137525 := bbase (se 5 (by rfl) ⟨147071, by rfl⟩ : syracuseStep 3137525 = 294143) (by norm_num)
theorem B1400885 : Blo 550806 1400885 := bbase (se 5 (by rfl) ⟨65666, by rfl⟩ : syracuseStep 1400885 = 131333) (by norm_num)
theorem B1859813 : Blo 550806 1859813 := bbase (se 4 (by rfl) ⟨174357, by rfl⟩ : syracuseStep 1859813 = 348715) (by norm_num)
theorem B1401077 : Blo 550806 1401077 := bbase (se 5 (by rfl) ⟨65675, by rfl⟩ : syracuseStep 1401077 = 131351) (by norm_num)
theorem B1401421 : Blo 550806 1401421 := bbase (se 3 (by rfl) ⟨262766, by rfl⟩ : syracuseStep 1401421 = 525533) (by norm_num)
theorem B1860245 : Blo 550806 1860245 := bbase (se 6 (by rfl) ⟨43599, by rfl⟩ : syracuseStep 1860245 = 87199) (by norm_num)
theorem B1401533 : Blo 550806 1401533 := bbase (se 3 (by rfl) ⟨262787, by rfl⟩ : syracuseStep 1401533 = 525575) (by norm_num)
theorem B1794901 : Blo 550806 1794901 := bbase (se 9 (by rfl) ⟨5258, by rfl⟩ : syracuseStep 1794901 = 10517) (by norm_num)
theorem B942965 : Blo 550806 942965 := bbase (se 5 (by rfl) ⟨44201, by rfl⟩ : syracuseStep 942965 = 88403) (by norm_num)
theorem B1401725 : Blo 550806 1401725 := bbase (se 3 (by rfl) ⟨262823, by rfl⟩ : syracuseStep 1401725 = 525647) (by norm_num)
theorem B1598341 : Blo 550806 1598341 := bbase (se 4 (by rfl) ⟨149844, by rfl⟩ : syracuseStep 1598341 = 299689) (by norm_num)
theorem B3990421 : Blo 550806 3990421 := bbase (se 6 (by rfl) ⟨93525, by rfl⟩ : syracuseStep 3990421 = 187051) (by norm_num)
theorem B22668245 : Blo 550806 22668245 := bbase (se 7 (by rfl) ⟨265643, by rfl⟩ : syracuseStep 22668245 = 531287) (by norm_num)
theorem B1860677 : Blo 550806 1860677 := bbase (se 4 (by rfl) ⟨174438, by rfl⟩ : syracuseStep 1860677 = 348877) (by norm_num)
theorem B3138709 : Blo 550806 3138709 := bbase (se 6 (by rfl) ⟨73563, by rfl⟩ : syracuseStep 3138709 = 147127) (by norm_num)
theorem B1402069 : Blo 550806 1402069 := bbase (se 7 (by rfl) ⟨16430, by rfl⟩ : syracuseStep 1402069 = 32861) (by norm_num)
theorem B2647349 : Blo 550806 2647349 := bbase (se 5 (by rfl) ⟨124094, by rfl⟩ : syracuseStep 2647349 = 248189) (by norm_num)
theorem B1402181 : Blo 550806 1402181 := bbase (se 4 (by rfl) ⟨131454, by rfl⟩ : syracuseStep 1402181 = 262909) (by norm_num)
theorem B1861109 : Blo 550806 1861109 := bbase (se 5 (by rfl) ⟨87239, by rfl⟩ : syracuseStep 1861109 = 174479) (by norm_num)
theorem B1402373 : Blo 550806 1402373 := bbase (se 4 (by rfl) ⟨131472, by rfl⟩ : syracuseStep 1402373 = 262945) (by norm_num)
theorem B4187861 : Blo 550806 4187861 := bbase (se 7 (by rfl) ⟨49076, by rfl⟩ : syracuseStep 4187861 = 98153) (by norm_num)
theorem B747253 : Blo 550806 747253 := bbase (se 5 (by rfl) ⟨35027, by rfl⟩ : syracuseStep 747253 = 70055) (by norm_num)
theorem B1402717 : Blo 550806 1402717 := bbase (se 3 (by rfl) ⟨263009, by rfl⟩ : syracuseStep 1402717 = 526019) (by norm_num)
theorem B1861541 : Blo 550806 1861541 := bbase (se 4 (by rfl) ⟨174519, by rfl⟩ : syracuseStep 1861541 = 349039) (by norm_num)
theorem B1402829 : Blo 550806 1402829 := bbase (se 3 (by rfl) ⟨263030, by rfl⟩ : syracuseStep 1402829 = 526061) (by norm_num)
theorem B1403021 : Blo 550806 1403021 := bbase (se 3 (by rfl) ⟨263066, by rfl⟩ : syracuseStep 1403021 = 526133) (by norm_num)
theorem B2353333 : Blo 550806 2353333 := bbase (se 5 (by rfl) ⟨110312, by rfl⟩ : syracuseStep 2353333 = 220625) (by norm_num)
theorem B2353349 : Blo 550806 2353349 := bbase (se 4 (by rfl) ⟨220626, by rfl⟩ : syracuseStep 2353349 = 441253) (by norm_num)
theorem B944389 : Blo 550806 944389 := bbase (se 4 (by rfl) ⟨88536, by rfl⟩ : syracuseStep 944389 = 177073) (by norm_num)
theorem B1239317 : Blo 550806 1239317 := bbase (se 6 (by rfl) ⟨29046, by rfl⟩ : syracuseStep 1239317 = 58093) (by norm_num)
theorem B1861973 : Blo 550806 1861973 := bbase (se 10 (by rfl) ⟨2727, by rfl⟩ : syracuseStep 1861973 = 5455) (by norm_num)
theorem B1239389 : Blo 550806 1239389 := bbase (se 3 (by rfl) ⟨232385, by rfl⟩ : syracuseStep 1239389 = 464771) (by norm_num)
theorem B2091365 : Blo 550806 2091365 := bbase (se 4 (by rfl) ⟨196065, by rfl⟩ : syracuseStep 2091365 = 392131) (by norm_num)
theorem B1239461 : Blo 550806 1239461 := bbase (se 4 (by rfl) ⟨116199, by rfl⟩ : syracuseStep 1239461 = 232399) (by norm_num)
theorem B1403365 : Blo 550806 1403365 := bbase (se 4 (by rfl) ⟨131565, by rfl⟩ : syracuseStep 1403365 = 263131) (by norm_num)
theorem B1239533 : Blo 550806 1239533 := bbase (se 3 (by rfl) ⟨232412, by rfl⟩ : syracuseStep 1239533 = 464825) (by norm_num)
theorem B1239605 : Blo 550806 1239605 := bbase (se 5 (by rfl) ⟨58106, by rfl⟩ : syracuseStep 1239605 = 116213) (by norm_num)
theorem B682553 : Blo 550806 682553 := bbase (se 2 (by rfl) ⟨255957, by rfl⟩ : syracuseStep 682553 = 511915) (by norm_num)
theorem B1403477 : Blo 550806 1403477 := bbase (se 8 (by rfl) ⟨8223, by rfl⟩ : syracuseStep 1403477 = 16447) (by norm_num)
theorem B1239677 : Blo 550806 1239677 := bbase (se 3 (by rfl) ⟨232439, by rfl⟩ : syracuseStep 1239677 = 464879) (by norm_num)
theorem B2091653 : Blo 550806 2091653 := bbase (se 4 (by rfl) ⟨196092, by rfl⟩ : syracuseStep 2091653 = 392185) (by norm_num)
theorem B1239749 : Blo 550806 1239749 := bbase (se 4 (by rfl) ⟨116226, by rfl⟩ : syracuseStep 1239749 = 232453) (by norm_num)
theorem B1862405 : Blo 550806 1862405 := bbase (se 4 (by rfl) ⟨174600, by rfl⟩ : syracuseStep 1862405 = 349201) (by norm_num)
theorem B1239821 : Blo 550806 1239821 := bbase (se 3 (by rfl) ⟨232466, by rfl⟩ : syracuseStep 1239821 = 464933) (by norm_num)
theorem B1403669 : Blo 550806 1403669 := bbase (se 6 (by rfl) ⟨32898, by rfl⟩ : syracuseStep 1403669 = 65797) (by norm_num)
theorem B1239893 : Blo 550806 1239893 := bbase (se 9 (by rfl) ⟨3632, by rfl⟩ : syracuseStep 1239893 = 7265) (by norm_num)
theorem B1239965 : Blo 550806 1239965 := bbase (se 3 (by rfl) ⟨232493, by rfl⟩ : syracuseStep 1239965 = 464987) (by norm_num)
theorem B1600469 : Blo 550806 1600469 := bbase (se 7 (by rfl) ⟨18755, by rfl⟩ : syracuseStep 1600469 = 37511) (by norm_num)
theorem B1240037 : Blo 550806 1240037 := bbase (se 4 (by rfl) ⟨116253, by rfl⟩ : syracuseStep 1240037 = 232507) (by norm_num)
theorem B1240109 : Blo 550806 1240109 := bbase (se 3 (by rfl) ⟨232520, by rfl⟩ : syracuseStep 1240109 = 465041) (by norm_num)
theorem B3140693 : Blo 550806 3140693 := bbase (se 8 (by rfl) ⟨18402, by rfl⟩ : syracuseStep 3140693 = 36805) (by norm_num)
theorem B912493 : Blo 550806 912493 := bbase (se 3 (by rfl) ⟨171092, by rfl⟩ : syracuseStep 912493 = 342185) (by norm_num)
theorem B1404013 : Blo 550806 1404013 := bbase (se 3 (by rfl) ⟨263252, by rfl⟩ : syracuseStep 1404013 = 526505) (by norm_num)
theorem B1240181 : Blo 550806 1240181 := bbase (se 5 (by rfl) ⟨58133, by rfl⟩ : syracuseStep 1240181 = 116267) (by norm_num)
theorem B1862837 : Blo 550806 1862837 := bbase (se 5 (by rfl) ⟨87320, by rfl⟩ : syracuseStep 1862837 = 174641) (by norm_num)
theorem B1240253 : Blo 550806 1240253 := bbase (se 3 (by rfl) ⟨232547, by rfl⟩ : syracuseStep 1240253 = 465095) (by norm_num)
theorem B1404125 : Blo 550806 1404125 := bbase (se 3 (by rfl) ⟨263273, by rfl⟩ : syracuseStep 1404125 = 526547) (by norm_num)
theorem B1240325 : Blo 550806 1240325 := bbase (se 4 (by rfl) ⟨116280, by rfl⟩ : syracuseStep 1240325 = 232561) (by norm_num)
theorem B945413 : Blo 550806 945413 := bbase (se 4 (by rfl) ⟨88632, by rfl⟩ : syracuseStep 945413 = 177265) (by norm_num)
theorem B1764629 : Blo 550806 1764629 := bbase (se 6 (by rfl) ⟨41358, by rfl⟩ : syracuseStep 1764629 = 82717) (by norm_num)
theorem B3534101 : Blo 550806 3534101 := bbase (se 6 (by rfl) ⟨82830, by rfl⟩ : syracuseStep 3534101 = 165661) (by norm_num)
theorem B1240397 : Blo 550806 1240397 := bbase (se 3 (by rfl) ⟨232574, by rfl⟩ : syracuseStep 1240397 = 465149) (by norm_num)
theorem B1240469 : Blo 550806 1240469 := bbase (se 6 (by rfl) ⟨29073, by rfl⟩ : syracuseStep 1240469 = 58147) (by norm_num)
theorem B1404317 : Blo 550806 1404317 := bbase (se 3 (by rfl) ⟨263309, by rfl⟩ : syracuseStep 1404317 = 526619) (by norm_num)
theorem B1240541 : Blo 550806 1240541 := bbase (se 3 (by rfl) ⟨232601, by rfl⟩ : syracuseStep 1240541 = 465203) (by norm_num)
theorem B1240613 : Blo 550806 1240613 := bbase (se 4 (by rfl) ⟨116307, by rfl⟩ : syracuseStep 1240613 = 232615) (by norm_num)
theorem B1863269 : Blo 550806 1863269 := bbase (se 4 (by rfl) ⟨174681, by rfl⟩ : syracuseStep 1863269 = 349363) (by norm_num)
theorem B1240685 : Blo 550806 1240685 := bbase (se 3 (by rfl) ⟨232628, by rfl⟩ : syracuseStep 1240685 = 465257) (by norm_num)
theorem B1240757 : Blo 550806 1240757 := bbase (se 5 (by rfl) ⟨58160, by rfl⟩ : syracuseStep 1240757 = 116321) (by norm_num)
theorem B1240829 : Blo 550806 1240829 := bbase (se 3 (by rfl) ⟨232655, by rfl⟩ : syracuseStep 1240829 = 465311) (by norm_num)
theorem B2092837 : Blo 550806 2092837 := bbase (se 4 (by rfl) ⟨196203, by rfl⟩ : syracuseStep 2092837 = 392407) (by norm_num)
theorem B1240901 : Blo 550806 1240901 := bbase (se 4 (by rfl) ⟨116334, by rfl⟩ : syracuseStep 1240901 = 232669) (by norm_num)
theorem B7958357 : Blo 550806 7958357 := bbase (se 9 (by rfl) ⟨23315, by rfl⟩ : syracuseStep 7958357 = 46631) (by norm_num)
theorem B1240973 : Blo 550806 1240973 := bbase (se 3 (by rfl) ⟨232682, by rfl⟩ : syracuseStep 1240973 = 465365) (by norm_num)
theorem B1241045 : Blo 550806 1241045 := bbase (se 7 (by rfl) ⟨14543, by rfl⟩ : syracuseStep 1241045 = 29087) (by norm_num)
theorem B1863701 : Blo 550806 1863701 := bbase (se 6 (by rfl) ⟨43680, by rfl⟩ : syracuseStep 1863701 = 87361) (by norm_num)
theorem B1241117 : Blo 550806 1241117 := bbase (se 3 (by rfl) ⟨232709, by rfl⟩ : syracuseStep 1241117 = 465419) (by norm_num)
theorem B716833 : Blo 550806 716833 := bbase (se 2 (by rfl) ⟨268812, by rfl⟩ : syracuseStep 716833 = 537625) (by norm_num)
theorem B946237 : Blo 550806 946237 := bbase (se 3 (by rfl) ⟨177419, by rfl⟩ : syracuseStep 946237 = 354839) (by norm_num)
theorem B2093141 : Blo 550806 2093141 := bbase (se 8 (by rfl) ⟨12264, by rfl⟩ : syracuseStep 2093141 = 24529) (by norm_num)
theorem B1241189 : Blo 550806 1241189 := bbase (se 4 (by rfl) ⟨116361, by rfl⟩ : syracuseStep 1241189 = 232723) (by norm_num)
theorem B1241261 : Blo 550806 1241261 := bbase (se 3 (by rfl) ⟨232736, by rfl⟩ : syracuseStep 1241261 = 465473) (by norm_num)
theorem B1896629 : Blo 550806 1896629 := bbase (se 5 (by rfl) ⟨88904, by rfl⟩ : syracuseStep 1896629 = 177809) (by norm_num)
theorem B1241333 : Blo 550806 1241333 := bbase (se 5 (by rfl) ⟨58187, by rfl⟩ : syracuseStep 1241333 = 116375) (by norm_num)
theorem B1241405 : Blo 550806 1241405 := bbase (se 3 (by rfl) ⟨232763, by rfl⟩ : syracuseStep 1241405 = 465527) (by norm_num)
theorem B3993941 : Blo 550806 3993941 := bbase (se 10 (by rfl) ⟨5850, by rfl⟩ : syracuseStep 3993941 = 11701) (by norm_num)
theorem B1241477 : Blo 550806 1241477 := bbase (se 4 (by rfl) ⟨116388, by rfl⟩ : syracuseStep 1241477 = 232777) (by norm_num)
theorem B2355605 : Blo 550806 2355605 := bbase (se 6 (by rfl) ⟨55209, by rfl⟩ : syracuseStep 2355605 = 110419) (by norm_num)
theorem B1864133 : Blo 550806 1864133 := bbase (se 4 (by rfl) ⟨174762, by rfl⟩ : syracuseStep 1864133 = 349525) (by norm_num)
theorem B1241549 : Blo 550806 1241549 := bbase (se 3 (by rfl) ⟨232790, by rfl⟩ : syracuseStep 1241549 = 465581) (by norm_num)
theorem B1569253 : Blo 550806 1569253 := bbase (se 4 (by rfl) ⟨147117, by rfl⟩ : syracuseStep 1569253 = 294235) (by norm_num)
theorem B1241621 : Blo 550806 1241621 := bbase (se 6 (by rfl) ⟨29100, by rfl⟩ : syracuseStep 1241621 = 58201) (by norm_num)
theorem B3600949 : Blo 550806 3600949 := bbase (se 5 (by rfl) ⟨168794, by rfl⟩ : syracuseStep 3600949 = 337589) (by norm_num)
theorem B1241693 : Blo 550806 1241693 := bbase (se 3 (by rfl) ⟨232817, by rfl⟩ : syracuseStep 1241693 = 465635) (by norm_num)
theorem B1241765 : Blo 550806 1241765 := bbase (se 4 (by rfl) ⟨116415, by rfl⟩ : syracuseStep 1241765 = 232831) (by norm_num)
theorem B1241837 : Blo 550806 1241837 := bbase (se 3 (by rfl) ⟨232844, by rfl⟩ : syracuseStep 1241837 = 465689) (by norm_num)
theorem B1241909 : Blo 550806 1241909 := bbase (se 5 (by rfl) ⟨58214, by rfl⟩ : syracuseStep 1241909 = 116429) (by norm_num)
theorem B1864565 : Blo 550806 1864565 := bbase (se 5 (by rfl) ⟨87401, by rfl⟩ : syracuseStep 1864565 = 174803) (by norm_num)
theorem B1241981 : Blo 550806 1241981 := bbase (se 3 (by rfl) ⟨232871, by rfl⟩ : syracuseStep 1241981 = 465743) (by norm_num)
theorem B1242053 : Blo 550806 1242053 := bbase (se 4 (by rfl) ⟨116442, by rfl⟩ : syracuseStep 1242053 = 232885) (by norm_num)
theorem B1242125 : Blo 550806 1242125 := bbase (se 3 (by rfl) ⟨232898, by rfl⟩ : syracuseStep 1242125 = 465797) (by norm_num)
theorem B1242197 : Blo 550806 1242197 := bbase (se 8 (by rfl) ⟨7278, by rfl⟩ : syracuseStep 1242197 = 14557) (by norm_num)
theorem B1176709 : Blo 550806 1176709 := bbase (se 4 (by rfl) ⟨110316, by rfl⟩ : syracuseStep 1176709 = 220633) (by norm_num)
theorem B1242269 : Blo 550806 1242269 := bbase (se 3 (by rfl) ⟨232925, by rfl⟩ : syracuseStep 1242269 = 465851) (by norm_num)
theorem B619681 : Blo 550806 619681 := bbase (se 2 (by rfl) ⟨232380, by rfl⟩ : syracuseStep 619681 = 464761) (by norm_num)
theorem B619717 : Blo 550806 619717 := bbase (se 4 (by rfl) ⟨58098, by rfl⟩ : syracuseStep 619717 = 116197) (by norm_num)
theorem B1242341 : Blo 550806 1242341 := bbase (se 4 (by rfl) ⟨116469, by rfl⟩ : syracuseStep 1242341 = 232939) (by norm_num)
theorem B619753 : Blo 550806 619753 := bbase (se 2 (by rfl) ⟨232407, by rfl⟩ : syracuseStep 619753 = 464815) (by norm_num)
theorem B3142901 : Blo 550806 3142901 := bbase (se 5 (by rfl) ⟨147323, by rfl⟩ : syracuseStep 3142901 = 294647) (by norm_num)
theorem B619789 : Blo 550806 619789 := bbase (se 3 (by rfl) ⟨116210, by rfl⟩ : syracuseStep 619789 = 232421) (by norm_num)
theorem B1045781 : Blo 550806 1045781 := bbase (se 6 (by rfl) ⟨24510, by rfl⟩ : syracuseStep 1045781 = 49021) (by norm_num)
theorem B1864997 : Blo 550806 1864997 := bbase (se 4 (by rfl) ⟨174843, by rfl⟩ : syracuseStep 1864997 = 349687) (by norm_num)
theorem B1242413 : Blo 550806 1242413 := bbase (se 3 (by rfl) ⟨232952, by rfl⟩ : syracuseStep 1242413 = 465905) (by norm_num)
theorem B619825 : Blo 550806 619825 := bbase (se 2 (by rfl) ⟨232434, by rfl⟩ : syracuseStep 619825 = 464869) (by norm_num)
theorem B619861 : Blo 550806 619861 := bbase (se 13 (by rfl) ⟨113, by rfl⟩ : syracuseStep 619861 = 227) (by norm_num)
theorem B1242485 : Blo 550806 1242485 := bbase (se 5 (by rfl) ⟨58241, by rfl⟩ : syracuseStep 1242485 = 116483) (by norm_num)
theorem B619897 : Blo 550806 619897 := bbase (se 2 (by rfl) ⟨232461, by rfl⟩ : syracuseStep 619897 = 464923) (by norm_num)
theorem B619933 : Blo 550806 619933 := bbase (se 3 (by rfl) ⟨116237, by rfl⟩ : syracuseStep 619933 = 232475) (by norm_num)
theorem B1242557 : Blo 550806 1242557 := bbase (se 3 (by rfl) ⟨232979, by rfl⟩ : syracuseStep 1242557 = 465959) (by norm_num)
theorem B619969 : Blo 550806 619969 := bbase (se 2 (by rfl) ⟨232488, by rfl⟩ : syracuseStep 619969 = 464977) (by norm_num)
theorem B620005 : Blo 550806 620005 := bbase (se 4 (by rfl) ⟨58125, by rfl⟩ : syracuseStep 620005 = 116251) (by norm_num)
theorem B1177085 : Blo 550806 1177085 := bbase (se 3 (by rfl) ⟨220703, by rfl⟩ : syracuseStep 1177085 = 441407) (by norm_num)
theorem B1242629 : Blo 550806 1242629 := bbase (se 4 (by rfl) ⟨116496, by rfl⟩ : syracuseStep 1242629 = 232993) (by norm_num)
theorem B620041 : Blo 550806 620041 := bbase (se 2 (by rfl) ⟨232515, by rfl⟩ : syracuseStep 620041 = 465031) (by norm_num)
theorem B620077 : Blo 550806 620077 := bbase (se 3 (by rfl) ⟨116264, by rfl⟩ : syracuseStep 620077 = 232529) (by norm_num)
theorem B1570357 : Blo 550806 1570357 := bbase (se 5 (by rfl) ⟨73610, by rfl⟩ : syracuseStep 1570357 = 147221) (by norm_num)
theorem B1242701 : Blo 550806 1242701 := bbase (se 3 (by rfl) ⟨233006, by rfl⟩ : syracuseStep 1242701 = 466013) (by norm_num)
theorem B620113 : Blo 550806 620113 := bbase (se 2 (by rfl) ⟨232542, by rfl⟩ : syracuseStep 620113 = 465085) (by norm_num)
theorem B2979413 : Blo 550806 2979413 := bbase (se 8 (by rfl) ⟨17457, by rfl⟩ : syracuseStep 2979413 = 34915) (by norm_num)
theorem B620149 : Blo 550806 620149 := bbase (se 5 (by rfl) ⟨29069, by rfl⟩ : syracuseStep 620149 = 58139) (by norm_num)
theorem B882301 : Blo 550806 882301 := bbase (se 3 (by rfl) ⟨165431, by rfl⟩ : syracuseStep 882301 = 330863) (by norm_num)
theorem B1242773 : Blo 550806 1242773 := bbase (se 6 (by rfl) ⟨29127, by rfl⟩ : syracuseStep 1242773 = 58255) (by norm_num)
theorem B620185 : Blo 550806 620185 := bbase (se 2 (by rfl) ⟨232569, by rfl⟩ : syracuseStep 620185 = 465139) (by norm_num)
theorem B620221 : Blo 550806 620221 := bbase (se 3 (by rfl) ⟨116291, by rfl⟩ : syracuseStep 620221 = 232583) (by norm_num)
theorem B1865429 : Blo 550806 1865429 := bbase (se 7 (by rfl) ⟨21860, by rfl⟩ : syracuseStep 1865429 = 43721) (by norm_num)
theorem B1242845 : Blo 550806 1242845 := bbase (se 3 (by rfl) ⟨233033, by rfl⟩ : syracuseStep 1242845 = 466067) (by norm_num)
theorem B620257 : Blo 550806 620257 := bbase (se 2 (by rfl) ⟨232596, by rfl⟩ : syracuseStep 620257 = 465193) (by norm_num)
theorem B620293 : Blo 550806 620293 := bbase (se 4 (by rfl) ⟨58152, by rfl⟩ : syracuseStep 620293 = 116305) (by norm_num)
theorem B1242917 : Blo 550806 1242917 := bbase (se 4 (by rfl) ⟨116523, by rfl⟩ : syracuseStep 1242917 = 233047) (by norm_num)
theorem B620329 : Blo 550806 620329 := bbase (se 2 (by rfl) ⟨232623, by rfl⟩ : syracuseStep 620329 = 465247) (by norm_num)
theorem B849709 : Blo 550806 849709 := bbase (se 3 (by rfl) ⟨159320, by rfl⟩ : syracuseStep 849709 = 318641) (by norm_num)
theorem B620365 : Blo 550806 620365 := bbase (se 3 (by rfl) ⟨116318, by rfl⟩ : syracuseStep 620365 = 232637) (by norm_num)
theorem B1242989 : Blo 550806 1242989 := bbase (se 3 (by rfl) ⟨233060, by rfl⟩ : syracuseStep 1242989 = 466121) (by norm_num)
theorem B620401 : Blo 550806 620401 := bbase (se 2 (by rfl) ⟨232650, by rfl⟩ : syracuseStep 620401 = 465301) (by norm_num)
theorem B620437 : Blo 550806 620437 := bbase (se 6 (by rfl) ⟨14541, by rfl⟩ : syracuseStep 620437 = 29083) (by norm_num)
theorem B948125 : Blo 550806 948125 := bbase (se 3 (by rfl) ⟨177773, by rfl⟩ : syracuseStep 948125 = 355547) (by norm_num)
theorem B1243061 : Blo 550806 1243061 := bbase (se 5 (by rfl) ⟨58268, by rfl⟩ : syracuseStep 1243061 = 116537) (by norm_num)
theorem B620473 : Blo 550806 620473 := bbase (se 2 (by rfl) ⟨232677, by rfl⟩ : syracuseStep 620473 = 465355) (by norm_num)
theorem B620509 : Blo 550806 620509 := bbase (se 3 (by rfl) ⟨116345, by rfl⟩ : syracuseStep 620509 = 232691) (by norm_num)
theorem B1243133 : Blo 550806 1243133 := bbase (se 3 (by rfl) ⟨233087, by rfl⟩ : syracuseStep 1243133 = 466175) (by norm_num)
theorem B620545 : Blo 550806 620545 := bbase (se 2 (by rfl) ⟨232704, by rfl⟩ : syracuseStep 620545 = 465409) (by norm_num)
theorem B1046533 : Blo 550806 1046533 := bbase (se 4 (by rfl) ⟨98112, by rfl⟩ : syracuseStep 1046533 = 196225) (by norm_num)
theorem B620581 : Blo 550806 620581 := bbase (se 4 (by rfl) ⟨58179, by rfl⟩ : syracuseStep 620581 = 116359) (by norm_num)
theorem B1243205 : Blo 550806 1243205 := bbase (se 4 (by rfl) ⟨116550, by rfl⟩ : syracuseStep 1243205 = 233101) (by norm_num)
theorem B620617 : Blo 550806 620617 := bbase (se 2 (by rfl) ⟨232731, by rfl⟩ : syracuseStep 620617 = 465463) (by norm_num)
theorem B620653 : Blo 550806 620653 := bbase (se 3 (by rfl) ⟨116372, by rfl⟩ : syracuseStep 620653 = 232745) (by norm_num)
theorem B1865861 : Blo 550806 1865861 := bbase (se 4 (by rfl) ⟨174924, by rfl⟩ : syracuseStep 1865861 = 349849) (by norm_num)
theorem B1243277 : Blo 550806 1243277 := bbase (se 3 (by rfl) ⟨233114, by rfl⟩ : syracuseStep 1243277 = 466229) (by norm_num)
theorem B620689 : Blo 550806 620689 := bbase (se 2 (by rfl) ⟨232758, by rfl⟩ : syracuseStep 620689 = 465517) (by norm_num)
theorem B1046677 : Blo 550806 1046677 := bbase (se 6 (by rfl) ⟨24531, by rfl⟩ : syracuseStep 1046677 = 49063) (by norm_num)
theorem B2095253 : Blo 550806 2095253 := bbase (se 6 (by rfl) ⟨49107, by rfl⟩ : syracuseStep 2095253 = 98215) (by norm_num)
theorem B620725 : Blo 550806 620725 := bbase (se 5 (by rfl) ⟨29096, by rfl⟩ : syracuseStep 620725 = 58193) (by norm_num)
theorem B1243349 : Blo 550806 1243349 := bbase (se 7 (by rfl) ⟨14570, by rfl⟩ : syracuseStep 1243349 = 29141) (by norm_num)
theorem B620761 : Blo 550806 620761 := bbase (se 2 (by rfl) ⟨232785, by rfl⟩ : syracuseStep 620761 = 465571) (by norm_num)
theorem B620797 : Blo 550806 620797 := bbase (se 3 (by rfl) ⟨116399, by rfl⟩ : syracuseStep 620797 = 232799) (by norm_num)
theorem B2652421 : Blo 550806 2652421 := bbase (se 4 (by rfl) ⟨248664, by rfl⟩ : syracuseStep 2652421 = 497329) (by norm_num)
theorem B1243421 : Blo 550806 1243421 := bbase (se 3 (by rfl) ⟨233141, by rfl⟩ : syracuseStep 1243421 = 466283) (by norm_num)
theorem B620833 : Blo 550806 620833 := bbase (se 2 (by rfl) ⟨232812, by rfl⟩ : syracuseStep 620833 = 465625) (by norm_num)
theorem B2390309 : Blo 550806 2390309 := bbase (se 4 (by rfl) ⟨224091, by rfl⟩ : syracuseStep 2390309 = 448183) (by norm_num)
theorem B1046837 : Blo 550806 1046837 := bbase (se 5 (by rfl) ⟨49070, by rfl⟩ : syracuseStep 1046837 = 98141) (by norm_num)
theorem B620869 : Blo 550806 620869 := bbase (se 4 (by rfl) ⟨58206, by rfl⟩ : syracuseStep 620869 = 116413) (by norm_num)
theorem B1243493 : Blo 550806 1243493 := bbase (se 4 (by rfl) ⟨116577, by rfl⟩ : syracuseStep 1243493 = 233155) (by norm_num)
theorem B620905 : Blo 550806 620905 := bbase (se 2 (by rfl) ⟨232839, by rfl⟩ : syracuseStep 620905 = 465679) (by norm_num)
theorem B620941 : Blo 550806 620941 := bbase (se 3 (by rfl) ⟨116426, by rfl⟩ : syracuseStep 620941 = 232853) (by norm_num)
theorem B1243565 : Blo 550806 1243565 := bbase (se 3 (by rfl) ⟨233168, by rfl⟩ : syracuseStep 1243565 = 466337) (by norm_num)
theorem B620977 : Blo 550806 620977 := bbase (se 2 (by rfl) ⟨232866, by rfl⟩ : syracuseStep 620977 = 465733) (by norm_num)
theorem B2095541 : Blo 550806 2095541 := bbase (se 5 (by rfl) ⟨98228, by rfl⟩ : syracuseStep 2095541 = 196457) (by norm_num)
theorem B784837 : Blo 550806 784837 := bbase (se 4 (by rfl) ⟨73578, by rfl⟩ : syracuseStep 784837 = 147157) (by norm_num)
theorem B1046981 : Blo 550806 1046981 := bbase (se 4 (by rfl) ⟨98154, by rfl⟩ : syracuseStep 1046981 = 196309) (by norm_num)
theorem B621013 : Blo 550806 621013 := bbase (se 7 (by rfl) ⟨7277, by rfl⟩ : syracuseStep 621013 = 14555) (by norm_num)
theorem B588269 : Blo 550806 588269 := bbase (se 3 (by rfl) ⟨110300, by rfl⟩ : syracuseStep 588269 = 220601) (by norm_num)
theorem B1243637 : Blo 550806 1243637 := bbase (se 5 (by rfl) ⟨58295, by rfl⟩ : syracuseStep 1243637 = 116591) (by norm_num)
theorem B4487669 : Blo 550806 4487669 := bbase (se 5 (by rfl) ⟨210359, by rfl⟩ : syracuseStep 4487669 = 420719) (by norm_num)
theorem B621049 : Blo 550806 621049 := bbase (se 2 (by rfl) ⟨232893, by rfl⟩ : syracuseStep 621049 = 465787) (by norm_num)
theorem B621085 : Blo 550806 621085 := bbase (se 3 (by rfl) ⟨116453, by rfl⟩ : syracuseStep 621085 = 232907) (by norm_num)
theorem B883237 : Blo 550806 883237 := bbase (se 4 (by rfl) ⟨82803, by rfl⟩ : syracuseStep 883237 = 165607) (by norm_num)
theorem B1866293 : Blo 550806 1866293 := bbase (se 5 (by rfl) ⟨87482, by rfl⟩ : syracuseStep 1866293 = 174965) (by norm_num)
theorem B1243709 : Blo 550806 1243709 := bbase (se 3 (by rfl) ⟨233195, by rfl⟩ : syracuseStep 1243709 = 466391) (by norm_num)
theorem B621121 : Blo 550806 621121 := bbase (se 2 (by rfl) ⟨232920, by rfl⟩ : syracuseStep 621121 = 465841) (by norm_num)
theorem B621157 : Blo 550806 621157 := bbase (se 4 (by rfl) ⟨58233, by rfl⟩ : syracuseStep 621157 = 116467) (by norm_num)
theorem B1243781 : Blo 550806 1243781 := bbase (se 4 (by rfl) ⟨116604, by rfl⟩ : syracuseStep 1243781 = 233209) (by norm_num)
theorem B621193 : Blo 550806 621193 := bbase (se 2 (by rfl) ⟨232947, by rfl⟩ : syracuseStep 621193 = 465895) (by norm_num)
theorem B5307029 : Blo 550806 5307029 := bbase (se 6 (by rfl) ⟨124383, by rfl⟩ : syracuseStep 5307029 = 248767) (by norm_num)
theorem B621229 : Blo 550806 621229 := bbase (se 3 (by rfl) ⟨116480, by rfl⟩ : syracuseStep 621229 = 232961) (by norm_num)
theorem B1243853 : Blo 550806 1243853 := bbase (se 3 (by rfl) ⟨233222, by rfl⟩ : syracuseStep 1243853 = 466445) (by norm_num)
theorem B621265 : Blo 550806 621265 := bbase (se 2 (by rfl) ⟨232974, by rfl⟩ : syracuseStep 621265 = 465949) (by norm_num)
theorem B1047269 : Blo 550806 1047269 := bbase (se 4 (by rfl) ⟨98181, by rfl⟩ : syracuseStep 1047269 = 196363) (by norm_num)
theorem B621301 : Blo 550806 621301 := bbase (se 5 (by rfl) ⟨29123, by rfl⟩ : syracuseStep 621301 = 58247) (by norm_num)
theorem B4193045 : Blo 550806 4193045 := bbase (se 6 (by rfl) ⟨98274, by rfl⟩ : syracuseStep 4193045 = 196549) (by norm_num)
theorem B1243925 : Blo 550806 1243925 := bbase (se 6 (by rfl) ⟨29154, by rfl⟩ : syracuseStep 1243925 = 58309) (by norm_num)
theorem B621337 : Blo 550806 621337 := bbase (se 2 (by rfl) ⟨233001, by rfl⟩ : syracuseStep 621337 = 466003) (by norm_num)
theorem B621373 : Blo 550806 621373 := bbase (se 3 (by rfl) ⟨116507, by rfl⟩ : syracuseStep 621373 = 233015) (by norm_num)
theorem B1243997 : Blo 550806 1243997 := bbase (se 3 (by rfl) ⟨233249, by rfl⟩ : syracuseStep 1243997 = 466499) (by norm_num)
theorem B621409 : Blo 550806 621409 := bbase (se 2 (by rfl) ⟨233028, by rfl⟩ : syracuseStep 621409 = 466057) (by norm_num)
theorem B1047421 : Blo 550806 1047421 := bbase (se 3 (by rfl) ⟨196391, by rfl⟩ : syracuseStep 1047421 = 392783) (by norm_num)
theorem B621445 : Blo 550806 621445 := bbase (se 4 (by rfl) ⟨58260, by rfl⟩ : syracuseStep 621445 = 116521) (by norm_num)
theorem B1244069 : Blo 550806 1244069 := bbase (se 4 (by rfl) ⟨116631, by rfl⟩ : syracuseStep 1244069 = 233263) (by norm_num)
theorem B588713 : Blo 550806 588713 := bbase (se 2 (by rfl) ⟨220767, by rfl⟩ : syracuseStep 588713 = 441535) (by norm_num)
theorem B621481 : Blo 550806 621481 := bbase (se 2 (by rfl) ⟨233055, by rfl⟩ : syracuseStep 621481 = 466111) (by norm_num)
theorem B621517 : Blo 550806 621517 := bbase (se 3 (by rfl) ⟨116534, by rfl⟩ : syracuseStep 621517 = 233069) (by norm_num)
theorem B1866725 : Blo 550806 1866725 := bbase (se 4 (by rfl) ⟨175005, by rfl⟩ : syracuseStep 1866725 = 350011) (by norm_num)
theorem B1244141 : Blo 550806 1244141 := bbase (se 3 (by rfl) ⟨233276, by rfl⟩ : syracuseStep 1244141 = 466553) (by norm_num)
theorem B621553 : Blo 550806 621553 := bbase (se 2 (by rfl) ⟨233082, by rfl⟩ : syracuseStep 621553 = 466165) (by norm_num)
theorem B1571861 : Blo 550806 1571861 := bbase (se 6 (by rfl) ⟨36840, by rfl⟩ : syracuseStep 1571861 = 73681) (by norm_num)
theorem B621589 : Blo 550806 621589 := bbase (se 6 (by rfl) ⟨14568, by rfl⟩ : syracuseStep 621589 = 29137) (by norm_num)
theorem B1244213 : Blo 550806 1244213 := bbase (se 5 (by rfl) ⟨58322, by rfl⟩ : syracuseStep 1244213 = 116645) (by norm_num)
theorem B621625 : Blo 550806 621625 := bbase (se 2 (by rfl) ⟨233109, by rfl⟩ : syracuseStep 621625 = 466219) (by norm_num)
theorem B1997893 : Blo 550806 1997893 := bbase (se 4 (by rfl) ⟨187302, by rfl⟩ : syracuseStep 1997893 = 374605) (by norm_num)
theorem B621661 : Blo 550806 621661 := bbase (se 3 (by rfl) ⟨116561, by rfl⟩ : syracuseStep 621661 = 233123) (by norm_num)
theorem B1178725 : Blo 550806 1178725 := bbase (se 4 (by rfl) ⟨110505, by rfl⟩ : syracuseStep 1178725 = 221011) (by norm_num)
theorem B1768549 : Blo 550806 1768549 := bbase (se 4 (by rfl) ⟨165801, by rfl⟩ : syracuseStep 1768549 = 331603) (by norm_num)
theorem B1244285 : Blo 550806 1244285 := bbase (se 3 (by rfl) ⟨233303, by rfl⟩ : syracuseStep 1244285 = 466607) (by norm_num)
theorem B621697 : Blo 550806 621697 := bbase (se 2 (by rfl) ⟨233136, by rfl⟩ : syracuseStep 621697 = 466273) (by norm_num)
theorem B588961 : Blo 550806 588961 := bbase (se 2 (by rfl) ⟨220860, by rfl⟩ : syracuseStep 588961 = 441721) (by norm_num)
theorem B621733 : Blo 550806 621733 := bbase (se 4 (by rfl) ⟨58287, by rfl⟩ : syracuseStep 621733 = 116575) (by norm_num)
theorem B1047725 : Blo 550806 1047725 := bbase (se 3 (by rfl) ⟨196448, by rfl⟩ : syracuseStep 1047725 = 392897) (by norm_num)
theorem B1244357 : Blo 550806 1244357 := bbase (se 4 (by rfl) ⟨116658, by rfl⟩ : syracuseStep 1244357 = 233317) (by norm_num)
theorem B621769 : Blo 550806 621769 := bbase (se 2 (by rfl) ⟨233163, by rfl⟩ : syracuseStep 621769 = 466327) (by norm_num)
theorem B785629 : Blo 550806 785629 := bbase (se 3 (by rfl) ⟨147305, by rfl⟩ : syracuseStep 785629 = 294611) (by norm_num)
theorem B621805 : Blo 550806 621805 := bbase (se 3 (by rfl) ⟨116588, by rfl⟩ : syracuseStep 621805 = 233177) (by norm_num)
theorem B1244429 : Blo 550806 1244429 := bbase (se 3 (by rfl) ⟨233330, by rfl⟩ : syracuseStep 1244429 = 466661) (by norm_num)
theorem B621841 : Blo 550806 621841 := bbase (se 2 (by rfl) ⟨233190, by rfl⟩ : syracuseStep 621841 = 466381) (by norm_num)
theorem B621877 : Blo 550806 621877 := bbase (se 5 (by rfl) ⟨29150, by rfl⟩ : syracuseStep 621877 = 58301) (by norm_num)
theorem B1244501 : Blo 550806 1244501 := bbase (se 11 (by rfl) ⟨911, by rfl⟩ : syracuseStep 1244501 = 1823) (by norm_num)
theorem B621913 : Blo 550806 621913 := bbase (se 2 (by rfl) ⟨233217, by rfl⟩ : syracuseStep 621913 = 466435) (by norm_num)
theorem B1768805 : Blo 550806 1768805 := bbase (se 4 (by rfl) ⟨165825, by rfl⟩ : syracuseStep 1768805 = 331651) (by norm_num)
theorem B621949 : Blo 550806 621949 := bbase (se 3 (by rfl) ⟨116615, by rfl⟩ : syracuseStep 621949 = 233231) (by norm_num)
theorem B1867157 : Blo 550806 1867157 := bbase (se 6 (by rfl) ⟨43761, by rfl⟩ : syracuseStep 1867157 = 87523) (by norm_num)
theorem B1244573 : Blo 550806 1244573 := bbase (se 3 (by rfl) ⟨233357, by rfl⟩ : syracuseStep 1244573 = 466715) (by norm_num)
theorem B621985 : Blo 550806 621985 := bbase (se 2 (by rfl) ⟨233244, by rfl⟩ : syracuseStep 621985 = 466489) (by norm_num)
theorem B622021 : Blo 550806 622021 := bbase (se 4 (by rfl) ⟨58314, by rfl⟩ : syracuseStep 622021 = 116629) (by norm_num)
theorem B8977877 : Blo 550806 8977877 := bbase (se 7 (by rfl) ⟨105209, by rfl⟩ : syracuseStep 8977877 = 210419) (by norm_num)
theorem B1244645 : Blo 550806 1244645 := bbase (se 4 (by rfl) ⟨116685, by rfl⟩ : syracuseStep 1244645 = 233371) (by norm_num)
theorem B622057 : Blo 550806 622057 := bbase (se 2 (by rfl) ⟨233271, by rfl⟩ : syracuseStep 622057 = 466543) (by norm_num)
theorem B2883077 : Blo 550806 2883077 := bbase (se 4 (by rfl) ⟨270288, by rfl⟩ : syracuseStep 2883077 = 540577) (by norm_num)
theorem B622093 : Blo 550806 622093 := bbase (se 3 (by rfl) ⟨116642, by rfl⟩ : syracuseStep 622093 = 233285) (by norm_num)
theorem B785965 : Blo 550806 785965 := bbase (se 3 (by rfl) ⟨147368, by rfl⟩ : syracuseStep 785965 = 294737) (by norm_num)
theorem B1244717 : Blo 550806 1244717 := bbase (se 3 (by rfl) ⟨233384, by rfl⟩ : syracuseStep 1244717 = 466769) (by norm_num)
theorem B622129 : Blo 550806 622129 := bbase (se 2 (by rfl) ⟨233298, by rfl⟩ : syracuseStep 622129 = 466597) (by norm_num)
theorem B589393 : Blo 550806 589393 := bbase (se 2 (by rfl) ⟨221022, by rfl⟩ : syracuseStep 589393 = 442045) (by norm_num)
theorem B2096725 : Blo 550806 2096725 := bbase (se 8 (by rfl) ⟨12285, by rfl⟩ : syracuseStep 2096725 = 24571) (by norm_num)
theorem B622165 : Blo 550806 622165 := bbase (se 8 (by rfl) ⟨3645, by rfl⟩ : syracuseStep 622165 = 7291) (by norm_num)
theorem B1638005 : Blo 550806 1638005 := bbase (se 5 (by rfl) ⟨76781, by rfl⟩ : syracuseStep 1638005 = 153563) (by norm_num)
theorem B1244789 : Blo 550806 1244789 := bbase (se 5 (by rfl) ⟨58349, by rfl⟩ : syracuseStep 1244789 = 116699) (by norm_num)
theorem B622201 : Blo 550806 622201 := bbase (se 2 (by rfl) ⟨233325, by rfl⟩ : syracuseStep 622201 = 466651) (by norm_num)
theorem B589465 : Blo 550806 589465 := bbase (se 2 (by rfl) ⟨221049, by rfl⟩ : syracuseStep 589465 = 442099) (by norm_num)
theorem B622237 : Blo 550806 622237 := bbase (se 3 (by rfl) ⟨116669, by rfl⟩ : syracuseStep 622237 = 233339) (by norm_num)
theorem B1244861 : Blo 550806 1244861 := bbase (se 3 (by rfl) ⟨233411, by rfl⟩ : syracuseStep 1244861 = 466823) (by norm_num)
theorem B622273 : Blo 550806 622273 := bbase (se 2 (by rfl) ⟨233352, by rfl⟩ : syracuseStep 622273 = 466705) (by norm_num)
theorem B884429 : Blo 550806 884429 := bbase (se 3 (by rfl) ⟨165830, by rfl⟩ : syracuseStep 884429 = 331661) (by norm_num)
theorem B622309 : Blo 550806 622309 := bbase (se 4 (by rfl) ⟨58341, by rfl⟩ : syracuseStep 622309 = 116683) (by norm_num)
theorem B786181 : Blo 550806 786181 := bbase (se 4 (by rfl) ⟨73704, by rfl⟩ : syracuseStep 786181 = 147409) (by norm_num)
theorem B1244933 : Blo 550806 1244933 := bbase (se 4 (by rfl) ⟨116712, by rfl⟩ : syracuseStep 1244933 = 233425) (by norm_num)
theorem B622345 : Blo 550806 622345 := bbase (se 2 (by rfl) ⟨233379, by rfl⟩ : syracuseStep 622345 = 466759) (by norm_num)
theorem B622381 : Blo 550806 622381 := bbase (se 3 (by rfl) ⟨116696, by rfl⟩ : syracuseStep 622381 = 233393) (by norm_num)
theorem B1867589 : Blo 550806 1867589 := bbase (se 4 (by rfl) ⟨175086, by rfl⟩ : syracuseStep 1867589 = 350173) (by norm_num)
theorem B1245005 : Blo 550806 1245005 := bbase (se 3 (by rfl) ⟨233438, by rfl⟩ : syracuseStep 1245005 = 466877) (by norm_num)
theorem B622417 : Blo 550806 622417 := bbase (se 2 (by rfl) ⟨233406, by rfl⟩ : syracuseStep 622417 = 466813) (by norm_num)
theorem B622453 : Blo 550806 622453 := bbase (se 5 (by rfl) ⟨29177, by rfl⟩ : syracuseStep 622453 = 58355) (by norm_num)
theorem B2097029 : Blo 550806 2097029 := bbase (se 4 (by rfl) ⟨196596, by rfl⟩ : syracuseStep 2097029 = 393193) (by norm_num)
theorem B884621 : Blo 550806 884621 := bbase (se 3 (by rfl) ⟨165866, by rfl⟩ : syracuseStep 884621 = 331733) (by norm_num)
theorem B1245077 : Blo 550806 1245077 := bbase (se 6 (by rfl) ⟨29181, by rfl⟩ : syracuseStep 1245077 = 58363) (by norm_num)
theorem B622489 : Blo 550806 622489 := bbase (se 2 (by rfl) ⟨233433, by rfl⟩ : syracuseStep 622489 = 466867) (by norm_num)
theorem B1048477 : Blo 550806 1048477 := bbase (se 3 (by rfl) ⟨196589, by rfl⟩ : syracuseStep 1048477 = 393179) (by norm_num)
theorem B622525 : Blo 550806 622525 := bbase (se 3 (by rfl) ⟨116723, by rfl⟩ : syracuseStep 622525 = 233447) (by norm_num)
theorem B1179613 : Blo 550806 1179613 := bbase (se 3 (by rfl) ⟨221177, by rfl⟩ : syracuseStep 1179613 = 442355) (by norm_num)
theorem B1245149 : Blo 550806 1245149 := bbase (se 3 (by rfl) ⟨233465, by rfl⟩ : syracuseStep 1245149 = 466931) (by norm_num)
theorem B622561 : Blo 550806 622561 := bbase (se 2 (by rfl) ⟨233460, by rfl⟩ : syracuseStep 622561 = 466921) (by norm_num)
theorem B786449 : Blo 550806 786449 := bstep (se 2 (by rfl) ⟨294918, by rfl⟩ : syracuseStep 786449 = 589837) B589837
theorem B622723 : Blo 550806 622723 := bstep (se 1 (by rfl) ⟨467042, by rfl⟩ : syracuseStep 622723 = 934085) B934085
theorem B1245329 : Blo 550806 1245329 := bstep (se 2 (by rfl) ⟨466998, by rfl⟩ : syracuseStep 1245329 = 933997) B933997
theorem B1245347 : Blo 550806 1245347 := bstep (se 1 (by rfl) ⟨934010, by rfl⟩ : syracuseStep 1245347 = 1868021) B1868021
theorem B40337621 : Blo 550806 40337621 := bstep (se 7 (by rfl) ⟨472706, by rfl⟩ : syracuseStep 40337621 = 945413) B945413
theorem B1573091 : Blo 550806 1573091 := bstep (se 1 (by rfl) ⟨1179818, by rfl⟩ : syracuseStep 1573091 = 2359637) B2359637
theorem B622867 : Blo 550806 622867 := bstep (se 1 (by rfl) ⟨467150, by rfl⟩ : syracuseStep 622867 = 934301) B934301
theorem B2097485 : Blo 550806 2097485 := bstep (se 3 (by rfl) ⟨393278, by rfl⟩ : syracuseStep 2097485 = 786557) B786557
theorem B1048963 : Blo 550806 1048963 := bstep (se 1 (by rfl) ⟨786722, by rfl⟩ : syracuseStep 1048963 = 1573445) B1573445
theorem B623011 : Blo 550806 623011 := bstep (se 1 (by rfl) ⟨467258, by rfl⟩ : syracuseStep 623011 = 934517) B934517
theorem B1245617 : Blo 550806 1245617 := bstep (se 2 (by rfl) ⟨467106, by rfl⟩ : syracuseStep 1245617 = 934213) B934213
theorem B885185 : Blo 550806 885185 := bstep (se 2 (by rfl) ⟨331944, by rfl⟩ : syracuseStep 885185 = 663889) B663889
theorem B1245635 : Blo 550806 1245635 := bstep (se 1 (by rfl) ⟨934226, by rfl⟩ : syracuseStep 1245635 = 1868453) B1868453
theorem B2654669 : Blo 550806 2654669 := bstep (se 3 (by rfl) ⟨497750, by rfl⟩ : syracuseStep 2654669 = 995501) B995501
theorem B1769933 : Blo 550806 1769933 := bstep (se 3 (by rfl) ⟨331862, by rfl⟩ : syracuseStep 1769933 = 663725) B663725
theorem B1868237 : Blo 550806 1868237 := bstep (se 3 (by rfl) ⟨350294, by rfl⟩ : syracuseStep 1868237 = 700589) B700589
theorem B1868291 : Blo 550806 1868291 := bstep (se 1 (by rfl) ⟨1401218, by rfl⟩ : syracuseStep 1868291 = 2802437) B2802437
theorem B623155 : Blo 550806 623155 := bstep (se 1 (by rfl) ⟨467366, by rfl⟩ : syracuseStep 623155 = 934733) B934733
theorem B11960885 : Blo 550806 11960885 := bstep (se 5 (by rfl) ⟨560666, by rfl⟩ : syracuseStep 11960885 = 1121333) B1121333
theorem B7078499 : Blo 550806 7078499 := bstep (se 1 (by rfl) ⟨5308874, by rfl⟩ : syracuseStep 7078499 = 10617749) B10617749
theorem B885377 : Blo 550806 885377 := bstep (se 2 (by rfl) ⟨332016, by rfl⟩ : syracuseStep 885377 = 664033) B664033
theorem B623299 : Blo 550806 623299 := bstep (se 1 (by rfl) ⟨467474, by rfl⟩ : syracuseStep 623299 = 934949) B934949
theorem B1245905 : Blo 550806 1245905 := bstep (se 2 (by rfl) ⟨467214, by rfl⟩ : syracuseStep 1245905 = 934429) B934429
theorem B1245923 : Blo 550806 1245923 := bstep (se 1 (by rfl) ⟨934442, by rfl⟩ : syracuseStep 1245923 = 1868885) B1868885
theorem B885505 : Blo 550806 885505 := bstep (se 2 (by rfl) ⟨332064, by rfl⟩ : syracuseStep 885505 = 664129) B664129
theorem B1868561 : Blo 550806 1868561 := bstep (se 2 (by rfl) ⟨700710, by rfl⟩ : syracuseStep 1868561 = 1401421) B1401421
theorem B1049411 : Blo 550806 1049411 := bstep (se 1 (by rfl) ⟨787058, by rfl⟩ : syracuseStep 1049411 = 1574117) B1574117
theorem B623443 : Blo 550806 623443 := bstep (se 1 (by rfl) ⟨467582, by rfl⟩ : syracuseStep 623443 = 935165) B935165
theorem B787315 : Blo 550806 787315 := bstep (se 1 (by rfl) ⟨590486, by rfl⟩ : syracuseStep 787315 = 1180973) B1180973
theorem B1770445 : Blo 550806 1770445 := bstep (se 3 (by rfl) ⟨331958, by rfl⟩ : syracuseStep 1770445 = 663917) B663917
theorem B1278929 : Blo 550806 1278929 := bstep (se 2 (by rfl) ⟨479598, by rfl⟩ : syracuseStep 1278929 = 959197) B959197
theorem B787411 : Blo 550806 787411 := bstep (se 1 (by rfl) ⟨590558, by rfl⟩ : syracuseStep 787411 = 1181117) B1181117
theorem B623587 : Blo 550806 623587 := bstep (se 1 (by rfl) ⟨467690, by rfl⟩ : syracuseStep 623587 = 935381) B935381
theorem B1246193 : Blo 550806 1246193 := bstep (se 2 (by rfl) ⟨467322, by rfl⟩ : syracuseStep 1246193 = 934645) B934645
theorem B1246211 : Blo 550806 1246211 := bstep (se 1 (by rfl) ⟨934658, by rfl⟩ : syracuseStep 1246211 = 1869317) B1869317
theorem B1573901 : Blo 550806 1573901 := bstep (se 3 (by rfl) ⟨295106, by rfl⟩ : syracuseStep 1573901 = 590213) B590213
theorem B1049699 : Blo 550806 1049699 := bstep (se 1 (by rfl) ⟨787274, by rfl⟩ : syracuseStep 1049699 = 1574549) B1574549
theorem B2393201 : Blo 550806 2393201 := bstep (se 2 (by rfl) ⟨897450, by rfl⟩ : syracuseStep 2393201 = 1794901) B1794901
theorem B623731 : Blo 550806 623731 := bstep (se 1 (by rfl) ⟨467798, by rfl⟩ : syracuseStep 623731 = 935597) B935597
theorem B2131121 : Blo 550806 2131121 := bstep (se 2 (by rfl) ⟨799170, by rfl⟩ : syracuseStep 2131121 = 1598341) B1598341
theorem B3146957 : Blo 550806 3146957 := bstep (se 3 (by rfl) ⟨590054, by rfl⟩ : syracuseStep 3146957 = 1180109) B1180109
theorem B1574093 : Blo 550806 1574093 := bstep (se 3 (by rfl) ⟨295142, by rfl⟩ : syracuseStep 1574093 = 590285) B590285
theorem B623875 : Blo 550806 623875 := bstep (se 1 (by rfl) ⟨467906, by rfl⟩ : syracuseStep 623875 = 935813) B935813
theorem B1246481 : Blo 550806 1246481 := bstep (se 2 (by rfl) ⟨467430, by rfl⟩ : syracuseStep 1246481 = 934861) B934861
theorem B1246499 : Blo 550806 1246499 := bstep (se 1 (by rfl) ⟨934874, by rfl⟩ : syracuseStep 1246499 = 1869749) B1869749
theorem B1869101 : Blo 550806 1869101 := bstep (se 3 (by rfl) ⟨350456, by rfl⟩ : syracuseStep 1869101 = 700913) B700913
theorem B1869155 : Blo 550806 1869155 := bstep (se 1 (by rfl) ⟨1401866, by rfl⟩ : syracuseStep 1869155 = 2803733) B2803733
theorem B886145 : Blo 550806 886145 := bstep (se 2 (by rfl) ⟨332304, by rfl⟩ : syracuseStep 886145 = 664609) B664609
theorem B624019 : Blo 550806 624019 := bstep (se 1 (by rfl) ⟨468014, by rfl⟩ : syracuseStep 624019 = 936029) B936029
theorem B1770947 : Blo 550806 1770947 := bstep (se 1 (by rfl) ⟨1328210, by rfl⟩ : syracuseStep 1770947 = 2656421) B2656421
theorem B787907 : Blo 550806 787907 := bstep (se 1 (by rfl) ⟨590930, by rfl⟩ : syracuseStep 787907 = 1181861) B1181861
theorem B1246769 : Blo 550806 1246769 := bstep (se 2 (by rfl) ⟨467538, by rfl⟩ : syracuseStep 1246769 = 935077) B935077
theorem B1246787 : Blo 550806 1246787 := bstep (se 1 (by rfl) ⟨935090, by rfl⟩ : syracuseStep 1246787 = 1870181) B1870181
theorem B1869425 : Blo 550806 1869425 := bstep (se 2 (by rfl) ⟨701034, by rfl⟩ : syracuseStep 1869425 = 1402069) B1402069
theorem B3540685 : Blo 550806 3540685 := bstep (se 3 (by rfl) ⟨663878, by rfl⟩ : syracuseStep 3540685 = 1327757) B1327757
theorem B1181425 : Blo 550806 1181425 := bstep (se 2 (by rfl) ⟨443034, by rfl⟩ : syracuseStep 1181425 = 886069) B886069
theorem B591635 : Blo 550806 591635 := bstep (se 1 (by rfl) ⟨443726, by rfl⟩ : syracuseStep 591635 = 887453) B887453
theorem B1247057 : Blo 550806 1247057 := bstep (se 2 (by rfl) ⟨467646, by rfl⟩ : syracuseStep 1247057 = 935293) B935293
theorem B1247075 : Blo 550806 1247075 := bstep (se 1 (by rfl) ⟨935306, by rfl⟩ : syracuseStep 1247075 = 1870613) B1870613
theorem B1050641 : Blo 550806 1050641 := bstep (se 2 (by rfl) ⟨393990, by rfl⟩ : syracuseStep 1050641 = 787981) B787981
theorem B788545 : Blo 550806 788545 := bstep (se 2 (by rfl) ⟨295704, by rfl⟩ : syracuseStep 788545 = 591409) B591409
theorem B1247345 : Blo 550806 1247345 := bstep (se 2 (by rfl) ⟨467754, by rfl⟩ : syracuseStep 1247345 = 935509) B935509
theorem B1247363 : Blo 550806 1247363 := bstep (se 1 (by rfl) ⟨935522, by rfl⟩ : syracuseStep 1247363 = 1871045) B1871045
theorem B1869965 : Blo 550806 1869965 := bstep (se 3 (by rfl) ⟨350618, by rfl⟩ : syracuseStep 1869965 = 701237) B701237
theorem B1575085 : Blo 550806 1575085 := bstep (se 3 (by rfl) ⟨295328, by rfl⟩ : syracuseStep 1575085 = 590657) B590657
theorem B1870019 : Blo 550806 1870019 := bstep (se 1 (by rfl) ⟨1402514, by rfl⟩ : syracuseStep 1870019 = 2805029) B2805029
theorem B788881 : Blo 550806 788881 := bstep (se 2 (by rfl) ⟨295830, by rfl⟩ : syracuseStep 788881 = 591661) B591661
theorem B1247633 : Blo 550806 1247633 := bstep (se 2 (by rfl) ⟨467862, by rfl⟩ : syracuseStep 1247633 = 935725) B935725
theorem B1247651 : Blo 550806 1247651 := bstep (se 1 (by rfl) ⟨935738, by rfl⟩ : syracuseStep 1247651 = 1871477) B1871477
theorem B1870289 : Blo 550806 1870289 := bstep (se 2 (by rfl) ⟨701358, by rfl⟩ : syracuseStep 1870289 = 1402717) B1402717
theorem B1247921 : Blo 550806 1247921 := bstep (se 2 (by rfl) ⟨467970, by rfl⟩ : syracuseStep 1247921 = 935941) B935941
theorem B1247939 : Blo 550806 1247939 := bstep (se 1 (by rfl) ⟨935954, by rfl⟩ : syracuseStep 1247939 = 1871909) B1871909
theorem B2362097 : Blo 550806 2362097 := bstep (se 2 (by rfl) ⟨885786, by rfl⟩ : syracuseStep 2362097 = 1771573) B1771573
theorem B887555 : Blo 550806 887555 := bstep (se 1 (by rfl) ⟨665666, by rfl⟩ : syracuseStep 887555 = 1331333) B1331333
theorem B887683 : Blo 550806 887683 := bstep (se 1 (by rfl) ⟨665762, by rfl⟩ : syracuseStep 887683 = 1331525) B1331525
theorem B1051537 : Blo 550806 1051537 := bstep (se 2 (by rfl) ⟨394326, by rfl⟩ : syracuseStep 1051537 = 788653) B788653
theorem B1248209 : Blo 550806 1248209 := bstep (se 2 (by rfl) ⟨468078, by rfl⟩ : syracuseStep 1248209 = 936157) B936157
theorem B789473 : Blo 550806 789473 := bstep (se 2 (by rfl) ⟨296052, by rfl⟩ : syracuseStep 789473 = 592105) B592105
theorem B1248227 : Blo 550806 1248227 := bstep (se 1 (by rfl) ⟨936170, by rfl⟩ : syracuseStep 1248227 = 1872341) B1872341
theorem B1870829 : Blo 550806 1870829 := bstep (se 3 (by rfl) ⟨350780, by rfl⟩ : syracuseStep 1870829 = 701561) B701561
theorem B1870883 : Blo 550806 1870883 := bstep (se 1 (by rfl) ⟨1403162, by rfl⟩ : syracuseStep 1870883 = 2806325) B2806325
theorem B1051697 : Blo 550806 1051697 := bstep (se 2 (by rfl) ⟨394386, by rfl⟩ : syracuseStep 1051697 = 788773) B788773
theorem B2100401 : Blo 550806 2100401 := bstep (se 2 (by rfl) ⟨787650, by rfl⟩ : syracuseStep 2100401 = 1575301) B1575301
theorem B2985187 : Blo 550806 2985187 := bstep (se 1 (by rfl) ⟨2238890, by rfl⟩ : syracuseStep 2985187 = 4477781) B4477781
theorem B1772803 : Blo 550806 1772803 := bstep (se 1 (by rfl) ⟨1329602, by rfl⟩ : syracuseStep 1772803 = 2659205) B2659205
theorem B1871153 : Blo 550806 1871153 := bstep (se 2 (by rfl) ⟨701682, by rfl⟩ : syracuseStep 1871153 = 1403365) B1403365
theorem B3149189 : Blo 550806 3149189 := bstep (se 4 (by rfl) ⟨295236, by rfl⟩ : syracuseStep 3149189 = 590473) B590473
theorem B888241 : Blo 550806 888241 := bstep (se 2 (by rfl) ⟨333090, by rfl⟩ : syracuseStep 888241 = 666181) B666181
theorem B1052099 : Blo 550806 1052099 := bstep (se 1 (by rfl) ⟨789074, by rfl⟩ : syracuseStep 1052099 = 1578149) B1578149
theorem B1773265 : Blo 550806 1773265 := bstep (se 2 (by rfl) ⟨664974, by rfl⟩ : syracuseStep 1773265 = 1329949) B1329949
theorem B1871693 : Blo 550806 1871693 := bstep (se 3 (by rfl) ⟨350942, by rfl⟩ : syracuseStep 1871693 = 701885) B701885
theorem B1576817 : Blo 550806 1576817 := bstep (se 2 (by rfl) ⟨591306, by rfl⟩ : syracuseStep 1576817 = 1182613) B1182613
theorem B1871747 : Blo 550806 1871747 := bstep (se 1 (by rfl) ⟨1403810, by rfl⟩ : syracuseStep 1871747 = 2807621) B2807621
theorem B2363363 : Blo 550806 2363363 := bstep (se 1 (by rfl) ⟨1772522, by rfl⟩ : syracuseStep 2363363 = 3545045) B3545045
theorem B3149873 : Blo 550806 3149873 := bstep (se 2 (by rfl) ⟨1181202, by rfl⟩ : syracuseStep 3149873 = 2362405) B2362405
theorem B1577009 : Blo 550806 1577009 := bstep (se 2 (by rfl) ⟨591378, by rfl⟩ : syracuseStep 1577009 = 1182757) B1182757
theorem B1216657 : Blo 550806 1216657 := bstep (se 2 (by rfl) ⟨456246, by rfl⟩ : syracuseStep 1216657 = 912493) B912493
theorem B1872017 : Blo 550806 1872017 := bstep (se 2 (by rfl) ⟨702006, by rfl⟩ : syracuseStep 1872017 = 1404013) B1404013
theorem B757955 : Blo 550806 757955 := bstep (se 1 (by rfl) ⟨568466, by rfl⟩ : syracuseStep 757955 = 1136933) B1136933
theorem B1052995 : Blo 550806 1052995 := bstep (se 1 (by rfl) ⟨789746, by rfl⟩ : syracuseStep 1052995 = 1579493) B1579493
theorem B1053155 : Blo 550806 1053155 := bstep (se 1 (by rfl) ⟨789866, by rfl⟩ : syracuseStep 1053155 = 1579733) B1579733
theorem B2101859 : Blo 550806 2101859 := bstep (se 1 (by rfl) ⟨1576394, by rfl⟩ : syracuseStep 2101859 = 3152789) B3152789
theorem B1184483 : Blo 550806 1184483 := bstep (se 1 (by rfl) ⟨888362, by rfl⟩ : syracuseStep 1184483 = 1776725) B1776725
theorem B1578001 : Blo 550806 1578001 := bstep (se 2 (by rfl) ⟨591750, by rfl⟩ : syracuseStep 1578001 = 1183501) B1183501
theorem B2790449 : Blo 550806 2790449 := bstep (se 2 (by rfl) ⟨1046418, by rfl⟩ : syracuseStep 2790449 = 2092837) B2092837
theorem B2528333 : Blo 550806 2528333 := bstep (se 3 (by rfl) ⟨474062, by rfl⟩ : syracuseStep 2528333 = 948125) B948125
theorem B1578275 : Blo 550806 1578275 := bstep (se 1 (by rfl) ⟨1183706, by rfl⟩ : syracuseStep 1578275 = 2367413) B2367413
theorem B10065293 : Blo 550806 10065293 := bstep (se 3 (by rfl) ⟨1887242, by rfl⟩ : syracuseStep 10065293 = 3774485) B3774485
theorem B3151331 : Blo 550806 3151331 := bstep (se 1 (by rfl) ⟨2363498, by rfl⟩ : syracuseStep 3151331 = 4726997) B4726997
theorem B1578467 : Blo 550806 1578467 := bstep (se 1 (by rfl) ⟨1183850, by rfl⟩ : syracuseStep 1578467 = 2367701) B2367701
theorem B6297101 : Blo 550806 6297101 := bstep (se 3 (by rfl) ⟨1180706, by rfl⟩ : syracuseStep 6297101 = 2361413) B2361413
theorem B2102861 : Blo 550806 2102861 := bstep (se 3 (by rfl) ⟨394286, by rfl⟩ : syracuseStep 2102861 = 788573) B788573
theorem B1316465 : Blo 550806 1316465 := bstep (se 2 (by rfl) ⟨493674, by rfl⟩ : syracuseStep 1316465 = 987349) B987349
theorem B1119971 : Blo 550806 1119971 := bstep (se 1 (by rfl) ⟨839978, by rfl⟩ : syracuseStep 1119971 = 1679957) B1679957
theorem B45913877 : Blo 550806 45913877 := bstep (se 6 (by rfl) ⟨1076106, by rfl⟩ : syracuseStep 45913877 = 2152213) B2152213
theorem B14718773 : Blo 550806 14718773 := bstep (se 5 (by rfl) ⟨689942, by rfl⟩ : syracuseStep 14718773 = 1379885) B1379885
theorem B628643 : Blo 550806 628643 := bstep (se 1 (by rfl) ⟨471482, by rfl⟩ : syracuseStep 628643 = 942965) B942965
theorem B15112163 : Blo 550806 15112163 := bstep (se 1 (by rfl) ⟨11334122, by rfl⟩ : syracuseStep 15112163 = 22668245) B22668245
theorem B1579277 : Blo 550806 1579277 := bstep (se 3 (by rfl) ⟨296114, by rfl⟩ : syracuseStep 1579277 = 592229) B592229
theorem B1775981 : Blo 550806 1775981 := bstep (se 3 (by rfl) ⟨332996, by rfl⟩ : syracuseStep 1775981 = 665993) B665993
theorem B1579459 : Blo 550806 1579459 := bstep (se 1 (by rfl) ⟨1184594, by rfl⟩ : syracuseStep 1579459 = 2369189) B2369189
theorem B2791907 : Blo 550806 2791907 := bstep (se 1 (by rfl) ⟨2093930, by rfl⟩ : syracuseStep 2791907 = 4187861) B4187861
theorem B826211 : Blo 550806 826211 := bstep (se 1 (by rfl) ⟨619658, by rfl⟩ : syracuseStep 826211 = 1239317) B1239317
theorem B826241 : Blo 550806 826241 := bstep (se 2 (by rfl) ⟨309840, by rfl⟩ : syracuseStep 826241 = 619681) B619681
theorem B826259 : Blo 550806 826259 := bstep (se 1 (by rfl) ⟨619694, by rfl⟩ : syracuseStep 826259 = 1239389) B1239389
theorem B826289 : Blo 550806 826289 := bstep (se 2 (by rfl) ⟨309858, by rfl⟩ : syracuseStep 826289 = 619717) B619717
theorem B826307 : Blo 550806 826307 := bstep (se 1 (by rfl) ⟨619730, by rfl⟩ : syracuseStep 826307 = 1239461) B1239461
theorem B826337 : Blo 550806 826337 := bstep (se 2 (by rfl) ⟨309876, by rfl⟩ : syracuseStep 826337 = 619753) B619753
theorem B826355 : Blo 550806 826355 := bstep (se 1 (by rfl) ⟨619766, by rfl⟩ : syracuseStep 826355 = 1239533) B1239533
theorem B826385 : Blo 550806 826385 := bstep (se 2 (by rfl) ⟨309894, by rfl⟩ : syracuseStep 826385 = 619789) B619789
theorem B826403 : Blo 550806 826403 := bstep (se 1 (by rfl) ⟨619802, by rfl⟩ : syracuseStep 826403 = 1239605) B1239605
theorem B826433 : Blo 550806 826433 := bstep (se 2 (by rfl) ⟨309912, by rfl⟩ : syracuseStep 826433 = 619825) B619825
theorem B826451 : Blo 550806 826451 := bstep (se 1 (by rfl) ⟨619838, by rfl⟩ : syracuseStep 826451 = 1239677) B1239677
theorem B826481 : Blo 550806 826481 := bstep (se 2 (by rfl) ⟨309930, by rfl⟩ : syracuseStep 826481 = 619861) B619861
theorem B826499 : Blo 550806 826499 := bstep (se 1 (by rfl) ⟨619874, by rfl⟩ : syracuseStep 826499 = 1239749) B1239749
theorem B826529 : Blo 550806 826529 := bstep (se 2 (by rfl) ⟨309948, by rfl⟩ : syracuseStep 826529 = 619897) B619897
theorem B826547 : Blo 550806 826547 := bstep (se 1 (by rfl) ⟨619910, by rfl⟩ : syracuseStep 826547 = 1239821) B1239821
theorem B826577 : Blo 550806 826577 := bstep (se 2 (by rfl) ⟨309966, by rfl⟩ : syracuseStep 826577 = 619933) B619933
theorem B826595 : Blo 550806 826595 := bstep (se 1 (by rfl) ⟨619946, by rfl⟩ : syracuseStep 826595 = 1239893) B1239893
theorem B826625 : Blo 550806 826625 := bstep (se 2 (by rfl) ⟨309984, by rfl⟩ : syracuseStep 826625 = 619969) B619969
theorem B2792717 : Blo 550806 2792717 := bstep (se 3 (by rfl) ⟨523634, by rfl⟩ : syracuseStep 2792717 = 1047269) B1047269
theorem B826643 : Blo 550806 826643 := bstep (se 1 (by rfl) ⟨619982, by rfl⟩ : syracuseStep 826643 = 1239965) B1239965
theorem B826673 : Blo 550806 826673 := bstep (se 2 (by rfl) ⟨310002, by rfl⟩ : syracuseStep 826673 = 620005) B620005
theorem B728371 : Blo 550806 728371 := bstep (se 1 (by rfl) ⟨546278, by rfl⟩ : syracuseStep 728371 = 1092557) B1092557
theorem B826691 : Blo 550806 826691 := bstep (se 1 (by rfl) ⟨620018, by rfl⟩ : syracuseStep 826691 = 1240037) B1240037
theorem B662851 : Blo 550806 662851 := bstep (se 1 (by rfl) ⟨497138, by rfl⟩ : syracuseStep 662851 = 994277) B994277
theorem B826721 : Blo 550806 826721 := bstep (se 2 (by rfl) ⟨310020, by rfl⟩ : syracuseStep 826721 = 620041) B620041
theorem B826739 : Blo 550806 826739 := bstep (se 1 (by rfl) ⟨620054, by rfl⟩ : syracuseStep 826739 = 1240109) B1240109
theorem B662899 : Blo 550806 662899 := bstep (se 1 (by rfl) ⟨497174, by rfl⟩ : syracuseStep 662899 = 994349) B994349
theorem B826769 : Blo 550806 826769 := bstep (se 2 (by rfl) ⟨310038, by rfl⟩ : syracuseStep 826769 = 620077) B620077
theorem B826787 : Blo 550806 826787 := bstep (se 1 (by rfl) ⟨620090, by rfl⟩ : syracuseStep 826787 = 1240181) B1240181
theorem B826817 : Blo 550806 826817 := bstep (se 2 (by rfl) ⟨310056, by rfl⟩ : syracuseStep 826817 = 620113) B620113
theorem B826835 : Blo 550806 826835 := bstep (se 1 (by rfl) ⟨620126, by rfl⟩ : syracuseStep 826835 = 1240253) B1240253
theorem B4201955 : Blo 550806 4201955 := bstep (se 1 (by rfl) ⟨3151466, by rfl⟩ : syracuseStep 4201955 = 6302933) B6302933
theorem B826865 : Blo 550806 826865 := bstep (se 2 (by rfl) ⟨310074, by rfl⟩ : syracuseStep 826865 = 620149) B620149
theorem B826883 : Blo 550806 826883 := bstep (se 1 (by rfl) ⟨620162, by rfl⟩ : syracuseStep 826883 = 1240325) B1240325
theorem B7577101 : Blo 550806 7577101 := bstep (se 3 (by rfl) ⟨1420706, by rfl⟩ : syracuseStep 7577101 = 2841413) B2841413
theorem B826913 : Blo 550806 826913 := bstep (se 2 (by rfl) ⟨310092, by rfl⟩ : syracuseStep 826913 = 620185) B620185
theorem B826931 : Blo 550806 826931 := bstep (se 1 (by rfl) ⟨620198, by rfl⟩ : syracuseStep 826931 = 1240397) B1240397
theorem B2367053 : Blo 550806 2367053 := bstep (se 3 (by rfl) ⟨443822, by rfl⟩ : syracuseStep 2367053 = 887645) B887645
theorem B826961 : Blo 550806 826961 := bstep (se 2 (by rfl) ⟨310110, by rfl⟩ : syracuseStep 826961 = 620221) B620221
theorem B826979 : Blo 550806 826979 := bstep (se 1 (by rfl) ⟨620234, by rfl⟩ : syracuseStep 826979 = 1240469) B1240469
theorem B827009 : Blo 550806 827009 := bstep (se 2 (by rfl) ⟨310128, by rfl⟩ : syracuseStep 827009 = 620257) B620257
theorem B2104973 : Blo 550806 2104973 := bstep (se 3 (by rfl) ⟨394682, by rfl⟩ : syracuseStep 2104973 = 789365) B789365
theorem B827027 : Blo 550806 827027 := bstep (se 1 (by rfl) ⟨620270, by rfl⟩ : syracuseStep 827027 = 1240541) B1240541
theorem B827057 : Blo 550806 827057 := bstep (se 2 (by rfl) ⟨310146, by rfl⟩ : syracuseStep 827057 = 620293) B620293
theorem B827075 : Blo 550806 827075 := bstep (se 1 (by rfl) ⟨620306, by rfl⟩ : syracuseStep 827075 = 1240613) B1240613
theorem B827105 : Blo 550806 827105 := bstep (se 2 (by rfl) ⟨310164, by rfl⟩ : syracuseStep 827105 = 620329) B620329
theorem B827123 : Blo 550806 827123 := bstep (se 1 (by rfl) ⟨620342, by rfl⟩ : syracuseStep 827123 = 1240685) B1240685
theorem B827153 : Blo 550806 827153 := bstep (se 2 (by rfl) ⟨310182, by rfl⟩ : syracuseStep 827153 = 620365) B620365
theorem B827171 : Blo 550806 827171 := bstep (se 1 (by rfl) ⟨620378, by rfl⟩ : syracuseStep 827171 = 1240757) B1240757
theorem B827201 : Blo 550806 827201 := bstep (se 2 (by rfl) ⟨310200, by rfl⟩ : syracuseStep 827201 = 620401) B620401
theorem B827219 : Blo 550806 827219 := bstep (se 1 (by rfl) ⟨620414, by rfl⟩ : syracuseStep 827219 = 1240829) B1240829
theorem B827249 : Blo 550806 827249 := bstep (se 2 (by rfl) ⟨310218, by rfl⟩ : syracuseStep 827249 = 620437) B620437
theorem B827267 : Blo 550806 827267 := bstep (se 1 (by rfl) ⟨620450, by rfl⟩ : syracuseStep 827267 = 1240901) B1240901
theorem B827297 : Blo 550806 827297 := bstep (se 2 (by rfl) ⟨310236, by rfl⟩ : syracuseStep 827297 = 620473) B620473
theorem B827315 : Blo 550806 827315 := bstep (se 1 (by rfl) ⟨620486, by rfl⟩ : syracuseStep 827315 = 1240973) B1240973
theorem B827345 : Blo 550806 827345 := bstep (se 2 (by rfl) ⟨310254, by rfl⟩ : syracuseStep 827345 = 620509) B620509
theorem B827363 : Blo 550806 827363 := bstep (se 1 (by rfl) ⟨620522, by rfl⟩ : syracuseStep 827363 = 1241045) B1241045
theorem B1122275 : Blo 550806 1122275 := bstep (se 1 (by rfl) ⟨841706, by rfl⟩ : syracuseStep 1122275 = 1683413) B1683413
theorem B827393 : Blo 550806 827393 := bstep (se 2 (by rfl) ⟨310272, by rfl⟩ : syracuseStep 827393 = 620545) B620545
theorem B827411 : Blo 550806 827411 := bstep (se 1 (by rfl) ⟨620558, by rfl⟩ : syracuseStep 827411 = 1241117) B1241117
theorem B663571 : Blo 550806 663571 := bstep (se 1 (by rfl) ⟨497678, by rfl⟩ : syracuseStep 663571 = 995357) B995357
theorem B827441 : Blo 550806 827441 := bstep (se 2 (by rfl) ⟨310290, by rfl⟩ : syracuseStep 827441 = 620581) B620581
theorem B827459 : Blo 550806 827459 := bstep (se 1 (by rfl) ⟨620594, by rfl⟩ : syracuseStep 827459 = 1241189) B1241189
theorem B827489 : Blo 550806 827489 := bstep (se 2 (by rfl) ⟨310308, by rfl⟩ : syracuseStep 827489 = 620617) B620617
theorem B598115 : Blo 550806 598115 := bstep (se 1 (by rfl) ⟨448586, by rfl⟩ : syracuseStep 598115 = 897173) B897173
theorem B827507 : Blo 550806 827507 := bstep (se 1 (by rfl) ⟨620630, by rfl⟩ : syracuseStep 827507 = 1241261) B1241261
theorem B827537 : Blo 550806 827537 := bstep (se 2 (by rfl) ⟨310326, by rfl⟩ : syracuseStep 827537 = 620653) B620653
theorem B827555 : Blo 550806 827555 := bstep (se 1 (by rfl) ⟨620666, by rfl⟩ : syracuseStep 827555 = 1241333) B1241333
theorem B827585 : Blo 550806 827585 := bstep (se 2 (by rfl) ⟨310344, by rfl⟩ : syracuseStep 827585 = 620689) B620689
theorem B827603 : Blo 550806 827603 := bstep (se 1 (by rfl) ⟨620702, by rfl⟩ : syracuseStep 827603 = 1241405) B1241405
theorem B2662627 : Blo 550806 2662627 := bstep (se 1 (by rfl) ⟨1996970, by rfl⟩ : syracuseStep 2662627 = 3993941) B3993941
theorem B827633 : Blo 550806 827633 := bstep (se 2 (by rfl) ⟨310362, by rfl⟩ : syracuseStep 827633 = 620725) B620725
theorem B827651 : Blo 550806 827651 := bstep (se 1 (by rfl) ⟨620738, by rfl⟩ : syracuseStep 827651 = 1241477) B1241477
theorem B827681 : Blo 550806 827681 := bstep (se 2 (by rfl) ⟨310380, by rfl⟩ : syracuseStep 827681 = 620761) B620761
theorem B827699 : Blo 550806 827699 := bstep (se 1 (by rfl) ⟨620774, by rfl⟩ : syracuseStep 827699 = 1241549) B1241549
theorem B827729 : Blo 550806 827729 := bstep (se 2 (by rfl) ⟨310398, by rfl⟩ : syracuseStep 827729 = 620797) B620797
theorem B827747 : Blo 550806 827747 := bstep (se 1 (by rfl) ⟨620810, by rfl⟩ : syracuseStep 827747 = 1241621) B1241621
theorem B6300017 : Blo 550806 6300017 := bstep (se 2 (by rfl) ⟨2362506, by rfl⟩ : syracuseStep 6300017 = 4725013) B4725013
theorem B827777 : Blo 550806 827777 := bstep (se 2 (by rfl) ⟨310416, by rfl⟩ : syracuseStep 827777 = 620833) B620833
theorem B827795 : Blo 550806 827795 := bstep (se 1 (by rfl) ⟨620846, by rfl⟩ : syracuseStep 827795 = 1241693) B1241693
theorem B827825 : Blo 550806 827825 := bstep (se 2 (by rfl) ⟨310434, by rfl⟩ : syracuseStep 827825 = 620869) B620869
theorem B2105777 : Blo 550806 2105777 := bstep (se 2 (by rfl) ⟨789666, by rfl⟩ : syracuseStep 2105777 = 1579333) B1579333
theorem B827843 : Blo 550806 827843 := bstep (se 1 (by rfl) ⟨620882, by rfl⟩ : syracuseStep 827843 = 1241765) B1241765
theorem B827873 : Blo 550806 827873 := bstep (se 2 (by rfl) ⟨310452, by rfl⟩ : syracuseStep 827873 = 620905) B620905
theorem B827891 : Blo 550806 827891 := bstep (se 1 (by rfl) ⟨620918, by rfl⟩ : syracuseStep 827891 = 1241837) B1241837
theorem B827921 : Blo 550806 827921 := bstep (se 2 (by rfl) ⟨310470, by rfl⟩ : syracuseStep 827921 = 620941) B620941
theorem B827939 : Blo 550806 827939 := bstep (se 1 (by rfl) ⟨620954, by rfl⟩ : syracuseStep 827939 = 1241909) B1241909
theorem B827969 : Blo 550806 827969 := bstep (se 2 (by rfl) ⟨310488, by rfl⟩ : syracuseStep 827969 = 620977) B620977
theorem B827987 : Blo 550806 827987 := bstep (se 1 (by rfl) ⟨620990, by rfl⟩ : syracuseStep 827987 = 1241981) B1241981
theorem B828017 : Blo 550806 828017 := bstep (se 2 (by rfl) ⟨310506, by rfl⟩ : syracuseStep 828017 = 621013) B621013
theorem B828035 : Blo 550806 828035 := bstep (se 1 (by rfl) ⟨621026, by rfl⟩ : syracuseStep 828035 = 1242053) B1242053
theorem B3154565 : Blo 550806 3154565 := bstep (se 4 (by rfl) ⟨295740, by rfl⟩ : syracuseStep 3154565 = 591481) B591481
theorem B828065 : Blo 550806 828065 := bstep (se 2 (by rfl) ⟨310524, by rfl⟩ : syracuseStep 828065 = 621049) B621049
theorem B828083 : Blo 550806 828083 := bstep (se 1 (by rfl) ⟨621062, by rfl⟩ : syracuseStep 828083 = 1242125) B1242125
theorem B828113 : Blo 550806 828113 := bstep (se 2 (by rfl) ⟨310542, by rfl⟩ : syracuseStep 828113 = 621085) B621085
theorem B828131 : Blo 550806 828131 := bstep (se 1 (by rfl) ⟨621098, by rfl⟩ : syracuseStep 828131 = 1242197) B1242197
theorem B828161 : Blo 550806 828161 := bstep (se 2 (by rfl) ⟨310560, by rfl⟩ : syracuseStep 828161 = 621121) B621121
theorem B828179 : Blo 550806 828179 := bstep (se 1 (by rfl) ⟨621134, by rfl⟩ : syracuseStep 828179 = 1242269) B1242269
theorem B2827043 : Blo 550806 2827043 := bstep (se 1 (by rfl) ⟨2120282, by rfl⟩ : syracuseStep 2827043 = 4240565) B4240565
theorem B828209 : Blo 550806 828209 := bstep (se 2 (by rfl) ⟨310578, by rfl⟩ : syracuseStep 828209 = 621157) B621157
theorem B828227 : Blo 550806 828227 := bstep (se 1 (by rfl) ⟨621170, by rfl⟩ : syracuseStep 828227 = 1242341) B1242341
theorem B828257 : Blo 550806 828257 := bstep (se 2 (by rfl) ⟨310596, by rfl⟩ : syracuseStep 828257 = 621193) B621193
theorem B697187 : Blo 550806 697187 := bstep (se 1 (by rfl) ⟨522890, by rfl⟩ : syracuseStep 697187 = 1045781) B1045781
theorem B828275 : Blo 550806 828275 := bstep (se 1 (by rfl) ⟨621206, by rfl⟩ : syracuseStep 828275 = 1242413) B1242413
theorem B828305 : Blo 550806 828305 := bstep (se 2 (by rfl) ⟨310614, by rfl⟩ : syracuseStep 828305 = 621229) B621229
theorem B828323 : Blo 550806 828323 := bstep (se 1 (by rfl) ⟨621242, by rfl⟩ : syracuseStep 828323 = 1242485) B1242485
theorem B828353 : Blo 550806 828353 := bstep (se 2 (by rfl) ⟨310632, by rfl⟩ : syracuseStep 828353 = 621265) B621265
theorem B828371 : Blo 550806 828371 := bstep (se 1 (by rfl) ⟨621278, by rfl⟩ : syracuseStep 828371 = 1242557) B1242557
theorem B828401 : Blo 550806 828401 := bstep (se 2 (by rfl) ⟨310650, by rfl⟩ : syracuseStep 828401 = 621301) B621301
theorem B828419 : Blo 550806 828419 := bstep (se 1 (by rfl) ⟨621314, by rfl⟩ : syracuseStep 828419 = 1242629) B1242629
theorem B828449 : Blo 550806 828449 := bstep (se 2 (by rfl) ⟨310668, by rfl⟩ : syracuseStep 828449 = 621337) B621337
theorem B828467 : Blo 550806 828467 := bstep (se 1 (by rfl) ⟨621350, by rfl⟩ : syracuseStep 828467 = 1242701) B1242701
theorem B664643 : Blo 550806 664643 := bstep (se 1 (by rfl) ⟨498482, by rfl⟩ : syracuseStep 664643 = 996965) B996965
theorem B3155021 : Blo 550806 3155021 := bstep (se 3 (by rfl) ⟨591566, by rfl⟩ : syracuseStep 3155021 = 1183133) B1183133
theorem B2106445 : Blo 550806 2106445 := bstep (se 3 (by rfl) ⟨394958, by rfl⟩ : syracuseStep 2106445 = 789917) B789917
theorem B828497 : Blo 550806 828497 := bstep (se 2 (by rfl) ⟨310686, by rfl⟩ : syracuseStep 828497 = 621373) B621373
theorem B828515 : Blo 550806 828515 := bstep (se 1 (by rfl) ⟨621386, by rfl⟩ : syracuseStep 828515 = 1242773) B1242773
theorem B828545 : Blo 550806 828545 := bstep (se 2 (by rfl) ⟨310704, by rfl⟩ : syracuseStep 828545 = 621409) B621409
theorem B828563 : Blo 550806 828563 := bstep (se 1 (by rfl) ⟨621422, by rfl⟩ : syracuseStep 828563 = 1242845) B1242845
theorem B828593 : Blo 550806 828593 := bstep (se 2 (by rfl) ⟨310722, by rfl⟩ : syracuseStep 828593 = 621445) B621445
theorem B828611 : Blo 550806 828611 := bstep (se 1 (by rfl) ⟨621458, by rfl⟩ : syracuseStep 828611 = 1242917) B1242917
theorem B828641 : Blo 550806 828641 := bstep (se 2 (by rfl) ⟨310740, by rfl⟩ : syracuseStep 828641 = 621481) B621481
theorem B828659 : Blo 550806 828659 := bstep (se 1 (by rfl) ⟨621494, by rfl⟩ : syracuseStep 828659 = 1242989) B1242989
theorem B828689 : Blo 550806 828689 := bstep (se 2 (by rfl) ⟨310758, by rfl⟩ : syracuseStep 828689 = 621517) B621517
theorem B828707 : Blo 550806 828707 := bstep (se 1 (by rfl) ⟨621530, by rfl⟩ : syracuseStep 828707 = 1243061) B1243061
theorem B828737 : Blo 550806 828737 := bstep (se 2 (by rfl) ⟨310776, by rfl⟩ : syracuseStep 828737 = 621553) B621553
theorem B828755 : Blo 550806 828755 := bstep (se 1 (by rfl) ⟨621566, by rfl⟩ : syracuseStep 828755 = 1243133) B1243133
theorem B828785 : Blo 550806 828785 := bstep (se 2 (by rfl) ⟨310794, by rfl⟩ : syracuseStep 828785 = 621589) B621589
theorem B828803 : Blo 550806 828803 := bstep (se 1 (by rfl) ⟨621602, by rfl⟩ : syracuseStep 828803 = 1243205) B1243205
theorem B828833 : Blo 550806 828833 := bstep (se 2 (by rfl) ⟨310812, by rfl⟩ : syracuseStep 828833 = 621625) B621625
theorem B2663857 : Blo 550806 2663857 := bstep (se 2 (by rfl) ⟨998946, by rfl⟩ : syracuseStep 2663857 = 1997893) B1997893
theorem B828851 : Blo 550806 828851 := bstep (se 1 (by rfl) ⟨621638, by rfl⟩ : syracuseStep 828851 = 1243277) B1243277
theorem B599491 : Blo 550806 599491 := bstep (se 1 (by rfl) ⟨449618, by rfl⟩ : syracuseStep 599491 = 899237) B899237
theorem B828881 : Blo 550806 828881 := bstep (se 2 (by rfl) ⟨310830, by rfl⟩ : syracuseStep 828881 = 621661) B621661
theorem B828899 : Blo 550806 828899 := bstep (se 1 (by rfl) ⟨621674, by rfl⟩ : syracuseStep 828899 = 1243349) B1243349
theorem B828929 : Blo 550806 828929 := bstep (se 2 (by rfl) ⟨310848, by rfl⟩ : syracuseStep 828929 = 621697) B621697
theorem B828947 : Blo 550806 828947 := bstep (se 1 (by rfl) ⟨621710, by rfl⟩ : syracuseStep 828947 = 1243421) B1243421
theorem B697891 : Blo 550806 697891 := bstep (se 1 (by rfl) ⟨523418, by rfl⟩ : syracuseStep 697891 = 1046837) B1046837
theorem B828977 : Blo 550806 828977 := bstep (se 2 (by rfl) ⟨310866, by rfl⟩ : syracuseStep 828977 = 621733) B621733
theorem B828995 : Blo 550806 828995 := bstep (se 1 (by rfl) ⟨621746, by rfl⟩ : syracuseStep 828995 = 1243493) B1243493
theorem B4531781 : Blo 550806 4531781 := bstep (se 4 (by rfl) ⟨424854, by rfl⟩ : syracuseStep 4531781 = 849709) B849709
theorem B829025 : Blo 550806 829025 := bstep (se 2 (by rfl) ⟨310884, by rfl⟩ : syracuseStep 829025 = 621769) B621769
theorem B829043 : Blo 550806 829043 := bstep (se 1 (by rfl) ⟨621782, by rfl⟩ : syracuseStep 829043 = 1243565) B1243565
theorem B697987 : Blo 550806 697987 := bstep (se 1 (by rfl) ⟨523490, by rfl⟩ : syracuseStep 697987 = 1046981) B1046981
theorem B4368013 : Blo 550806 4368013 := bstep (se 3 (by rfl) ⟨819002, by rfl⟩ : syracuseStep 4368013 = 1638005) B1638005
theorem B829073 : Blo 550806 829073 := bstep (se 2 (by rfl) ⟨310902, by rfl⟩ : syracuseStep 829073 = 621805) B621805
theorem B829091 : Blo 550806 829091 := bstep (se 1 (by rfl) ⟨621818, by rfl⟩ : syracuseStep 829091 = 1243637) B1243637
theorem B2991779 : Blo 550806 2991779 := bstep (se 1 (by rfl) ⟨2243834, by rfl⟩ : syracuseStep 2991779 = 4487669) B4487669
theorem B829121 : Blo 550806 829121 := bstep (se 2 (by rfl) ⟨310920, by rfl⟩ : syracuseStep 829121 = 621841) B621841
theorem B829139 : Blo 550806 829139 := bstep (se 1 (by rfl) ⟨621854, by rfl⟩ : syracuseStep 829139 = 1243709) B1243709
theorem B829169 : Blo 550806 829169 := bstep (se 2 (by rfl) ⟨310938, by rfl⟩ : syracuseStep 829169 = 621877) B621877
theorem B829187 : Blo 550806 829187 := bstep (se 1 (by rfl) ⟨621890, by rfl⟩ : syracuseStep 829187 = 1243781) B1243781
theorem B829217 : Blo 550806 829217 := bstep (se 2 (by rfl) ⟨310956, by rfl⟩ : syracuseStep 829217 = 621913) B621913
theorem B829235 : Blo 550806 829235 := bstep (se 1 (by rfl) ⟨621926, by rfl⟩ : syracuseStep 829235 = 1243853) B1243853
theorem B829265 : Blo 550806 829265 := bstep (se 2 (by rfl) ⟨310974, by rfl⟩ : syracuseStep 829265 = 621949) B621949
theorem B2795363 : Blo 550806 2795363 := bstep (se 1 (by rfl) ⟨2096522, by rfl⟩ : syracuseStep 2795363 = 4193045) B4193045
theorem B829283 : Blo 550806 829283 := bstep (se 1 (by rfl) ⟨621962, by rfl⟩ : syracuseStep 829283 = 1243925) B1243925
theorem B829313 : Blo 550806 829313 := bstep (se 2 (by rfl) ⟨310992, by rfl⟩ : syracuseStep 829313 = 621985) B621985
theorem B829331 : Blo 550806 829331 := bstep (se 1 (by rfl) ⟨621998, by rfl⟩ : syracuseStep 829331 = 1243997) B1243997
theorem B3549091 : Blo 550806 3549091 := bstep (se 1 (by rfl) ⟨2661818, by rfl⟩ : syracuseStep 3549091 = 5323637) B5323637
theorem B829361 : Blo 550806 829361 := bstep (se 2 (by rfl) ⟨311010, by rfl⟩ : syracuseStep 829361 = 622021) B622021
theorem B829379 : Blo 550806 829379 := bstep (se 1 (by rfl) ⟨622034, by rfl⟩ : syracuseStep 829379 = 1244069) B1244069
theorem B829409 : Blo 550806 829409 := bstep (se 2 (by rfl) ⟨311028, by rfl⟩ : syracuseStep 829409 = 622057) B622057
theorem B829427 : Blo 550806 829427 := bstep (se 1 (by rfl) ⟨622070, by rfl⟩ : syracuseStep 829427 = 1244141) B1244141
theorem B829457 : Blo 550806 829457 := bstep (se 2 (by rfl) ⟨311046, by rfl⟩ : syracuseStep 829457 = 622093) B622093
theorem B829475 : Blo 550806 829475 := bstep (se 1 (by rfl) ⟨622106, by rfl⟩ : syracuseStep 829475 = 1244213) B1244213
theorem B829505 : Blo 550806 829505 := bstep (se 2 (by rfl) ⟨311064, by rfl⟩ : syracuseStep 829505 = 622129) B622129
theorem B829523 : Blo 550806 829523 := bstep (se 1 (by rfl) ⟨622142, by rfl⟩ : syracuseStep 829523 = 1244285) B1244285
theorem B2795633 : Blo 550806 2795633 := bstep (se 2 (by rfl) ⟨1048362, by rfl⟩ : syracuseStep 2795633 = 2096725) B2096725
theorem B829553 : Blo 550806 829553 := bstep (se 2 (by rfl) ⟨311082, by rfl⟩ : syracuseStep 829553 = 622165) B622165
theorem B698483 : Blo 550806 698483 := bstep (se 1 (by rfl) ⟨523862, by rfl⟩ : syracuseStep 698483 = 1047725) B1047725
theorem B829571 : Blo 550806 829571 := bstep (se 1 (by rfl) ⟨622178, by rfl⟩ : syracuseStep 829571 = 1244357) B1244357
theorem B829601 : Blo 550806 829601 := bstep (se 2 (by rfl) ⟨311100, by rfl⟩ : syracuseStep 829601 = 622201) B622201
theorem B829619 : Blo 550806 829619 := bstep (se 1 (by rfl) ⟨622214, by rfl⟩ : syracuseStep 829619 = 1244429) B1244429
theorem B829649 : Blo 550806 829649 := bstep (se 2 (by rfl) ⟨311118, by rfl⟩ : syracuseStep 829649 = 622237) B622237
theorem B829667 : Blo 550806 829667 := bstep (se 1 (by rfl) ⟨622250, by rfl⟩ : syracuseStep 829667 = 1244501) B1244501
theorem B829697 : Blo 550806 829697 := bstep (se 2 (by rfl) ⟨311136, by rfl⟩ : syracuseStep 829697 = 622273) B622273
theorem B829715 : Blo 550806 829715 := bstep (se 1 (by rfl) ⟨622286, by rfl⟩ : syracuseStep 829715 = 1244573) B1244573
theorem B829745 : Blo 550806 829745 := bstep (se 2 (by rfl) ⟨311154, by rfl⟩ : syracuseStep 829745 = 622309) B622309
theorem B829763 : Blo 550806 829763 := bstep (se 1 (by rfl) ⟨622322, by rfl⟩ : syracuseStep 829763 = 1244645) B1244645
theorem B829793 : Blo 550806 829793 := bstep (se 2 (by rfl) ⟨311172, by rfl⟩ : syracuseStep 829793 = 622345) B622345
theorem B600419 : Blo 550806 600419 := bstep (se 1 (by rfl) ⟨450314, by rfl⟩ : syracuseStep 600419 = 900629) B900629
theorem B829811 : Blo 550806 829811 := bstep (se 1 (by rfl) ⟨622358, by rfl⟩ : syracuseStep 829811 = 1244717) B1244717
theorem B829841 : Blo 550806 829841 := bstep (se 2 (by rfl) ⟨311190, by rfl⟩ : syracuseStep 829841 = 622381) B622381
theorem B829859 : Blo 550806 829859 := bstep (se 1 (by rfl) ⟨622394, by rfl⟩ : syracuseStep 829859 = 1244789) B1244789
theorem B829889 : Blo 550806 829889 := bstep (se 2 (by rfl) ⟨311208, by rfl⟩ : syracuseStep 829889 = 622417) B622417
theorem B829907 : Blo 550806 829907 := bstep (se 1 (by rfl) ⟨622430, by rfl⟩ : syracuseStep 829907 = 1244861) B1244861
theorem B829937 : Blo 550806 829937 := bstep (se 2 (by rfl) ⟨311226, by rfl⟩ : syracuseStep 829937 = 622453) B622453
theorem B829955 : Blo 550806 829955 := bstep (se 1 (by rfl) ⟨622466, by rfl⟩ : syracuseStep 829955 = 1244933) B1244933
theorem B829985 : Blo 550806 829985 := bstep (se 2 (by rfl) ⟨311244, by rfl⟩ : syracuseStep 829985 = 622489) B622489
theorem B830003 : Blo 550806 830003 := bstep (se 1 (by rfl) ⟨622502, by rfl⟩ : syracuseStep 830003 = 1245005) B1245005
theorem B3648077 : Blo 550806 3648077 := bstep (se 3 (by rfl) ⟨684014, by rfl⟩ : syracuseStep 3648077 = 1368029) B1368029
theorem B830033 : Blo 550806 830033 := bstep (se 2 (by rfl) ⟨311262, by rfl⟩ : syracuseStep 830033 = 622525) B622525
theorem B830051 : Blo 550806 830051 := bstep (se 1 (by rfl) ⟨622538, by rfl⟩ : syracuseStep 830051 = 1245077) B1245077
theorem B830081 : Blo 550806 830081 := bstep (se 2 (by rfl) ⟨311280, by rfl⟩ : syracuseStep 830081 = 622561) B622561
theorem B830099 : Blo 550806 830099 := bstep (se 1 (by rfl) ⟨622574, by rfl⟩ : syracuseStep 830099 = 1245149) B1245149
theorem B830129 : Blo 550806 830129 := bstep (se 2 (by rfl) ⟨311298, by rfl⟩ : syracuseStep 830129 = 622597) B622597
theorem B830147 : Blo 550806 830147 := bstep (se 1 (by rfl) ⟨622610, by rfl⟩ : syracuseStep 830147 = 1245221) B1245221
theorem B830177 : Blo 550806 830177 := bstep (se 2 (by rfl) ⟨311316, by rfl⟩ : syracuseStep 830177 = 622633) B622633
theorem B830195 : Blo 550806 830195 := bstep (se 1 (by rfl) ⟨622646, by rfl⟩ : syracuseStep 830195 = 1245293) B1245293
theorem B830225 : Blo 550806 830225 := bstep (se 2 (by rfl) ⟨311334, by rfl⟩ : syracuseStep 830225 = 622669) B622669
theorem B830243 : Blo 550806 830243 := bstep (se 1 (by rfl) ⟨622682, by rfl⟩ : syracuseStep 830243 = 1245365) B1245365
theorem B699187 : Blo 550806 699187 := bstep (se 1 (by rfl) ⟨524390, by rfl⟩ : syracuseStep 699187 = 1048781) B1048781
theorem B830273 : Blo 550806 830273 := bstep (se 2 (by rfl) ⟨311352, by rfl⟩ : syracuseStep 830273 = 622705) B622705
theorem B830291 : Blo 550806 830291 := bstep (se 1 (by rfl) ⟨622718, by rfl⟩ : syracuseStep 830291 = 1245437) B1245437
theorem B830321 : Blo 550806 830321 := bstep (se 2 (by rfl) ⟨311370, by rfl⟩ : syracuseStep 830321 = 622741) B622741
theorem B830339 : Blo 550806 830339 := bstep (se 1 (by rfl) ⟨622754, by rfl⟩ : syracuseStep 830339 = 1245509) B1245509
theorem B699283 : Blo 550806 699283 := bstep (se 1 (by rfl) ⟨524462, by rfl⟩ : syracuseStep 699283 = 1048925) B1048925
theorem B830369 : Blo 550806 830369 := bstep (se 2 (by rfl) ⟨311388, by rfl⟩ : syracuseStep 830369 = 622777) B622777
theorem B830387 : Blo 550806 830387 := bstep (se 1 (by rfl) ⟨622790, by rfl⟩ : syracuseStep 830387 = 1245581) B1245581
theorem B10660805 : Blo 550806 10660805 := bstep (se 4 (by rfl) ⟨999450, by rfl⟩ : syracuseStep 10660805 = 1998901) B1998901
theorem B830417 : Blo 550806 830417 := bstep (se 2 (by rfl) ⟨311406, by rfl⟩ : syracuseStep 830417 = 622813) B622813
theorem B3582947 : Blo 550806 3582947 := bstep (se 1 (by rfl) ⟨2687210, by rfl⟩ : syracuseStep 3582947 = 5374421) B5374421
theorem B830435 : Blo 550806 830435 := bstep (se 1 (by rfl) ⟨622826, by rfl⟩ : syracuseStep 830435 = 1245653) B1245653
theorem B830465 : Blo 550806 830465 := bstep (se 2 (by rfl) ⟨311424, by rfl⟩ : syracuseStep 830465 = 622849) B622849
theorem B830483 : Blo 550806 830483 := bstep (se 1 (by rfl) ⟨622862, by rfl⟩ : syracuseStep 830483 = 1245725) B1245725
theorem B830513 : Blo 550806 830513 := bstep (se 2 (by rfl) ⟨311442, by rfl⟩ : syracuseStep 830513 = 622885) B622885
theorem B830531 : Blo 550806 830531 := bstep (se 1 (by rfl) ⟨622898, by rfl⟩ : syracuseStep 830531 = 1245797) B1245797
theorem B830561 : Blo 550806 830561 := bstep (se 2 (by rfl) ⟨311460, by rfl⟩ : syracuseStep 830561 = 622921) B622921
theorem B3550321 : Blo 550806 3550321 := bstep (se 2 (by rfl) ⟨1331370, by rfl⟩ : syracuseStep 3550321 = 2662741) B2662741
theorem B830579 : Blo 550806 830579 := bstep (se 1 (by rfl) ⟨622934, by rfl⟩ : syracuseStep 830579 = 1245869) B1245869
theorem B5057677 : Blo 550806 5057677 := bstep (se 3 (by rfl) ⟨948314, by rfl⟩ : syracuseStep 5057677 = 1896629) B1896629
theorem B830609 : Blo 550806 830609 := bstep (se 2 (by rfl) ⟨311478, by rfl⟩ : syracuseStep 830609 = 622957) B622957
theorem B797843 : Blo 550806 797843 := bstep (se 1 (by rfl) ⟨598382, by rfl⟩ : syracuseStep 797843 = 1196765) B1196765
theorem B830627 : Blo 550806 830627 := bstep (se 1 (by rfl) ⟨622970, by rfl⟩ : syracuseStep 830627 = 1245941) B1245941
theorem B830657 : Blo 550806 830657 := bstep (se 2 (by rfl) ⟨311496, by rfl⟩ : syracuseStep 830657 = 622993) B622993
theorem B830675 : Blo 550806 830675 := bstep (se 1 (by rfl) ⟨623006, by rfl⟩ : syracuseStep 830675 = 1246013) B1246013
theorem B830705 : Blo 550806 830705 := bstep (se 2 (by rfl) ⟨311514, by rfl⟩ : syracuseStep 830705 = 623029) B623029
theorem B830723 : Blo 550806 830723 := bstep (se 1 (by rfl) ⟨623042, by rfl⟩ : syracuseStep 830723 = 1246085) B1246085
theorem B830753 : Blo 550806 830753 := bstep (se 2 (by rfl) ⟨311532, by rfl⟩ : syracuseStep 830753 = 623065) B623065
theorem B830771 : Blo 550806 830771 := bstep (se 1 (by rfl) ⟨623078, by rfl⟩ : syracuseStep 830771 = 1246157) B1246157
theorem B830801 : Blo 550806 830801 := bstep (se 2 (by rfl) ⟨311550, by rfl⟩ : syracuseStep 830801 = 623101) B623101
theorem B830819 : Blo 550806 830819 := bstep (se 1 (by rfl) ⟨623114, by rfl⟩ : syracuseStep 830819 = 1246229) B1246229
theorem B830849 : Blo 550806 830849 := bstep (se 2 (by rfl) ⟨311568, by rfl⟩ : syracuseStep 830849 = 623137) B623137
theorem B699779 : Blo 550806 699779 := bstep (se 1 (by rfl) ⟨524834, by rfl⟩ : syracuseStep 699779 = 1049669) B1049669
theorem B830867 : Blo 550806 830867 := bstep (se 1 (by rfl) ⟨623150, by rfl⟩ : syracuseStep 830867 = 1246301) B1246301
theorem B830897 : Blo 550806 830897 := bstep (se 2 (by rfl) ⟨311586, by rfl⟩ : syracuseStep 830897 = 623173) B623173
theorem B830915 : Blo 550806 830915 := bstep (se 1 (by rfl) ⟨623186, by rfl⟩ : syracuseStep 830915 = 1246373) B1246373
theorem B830945 : Blo 550806 830945 := bstep (se 2 (by rfl) ⟨311604, by rfl⟩ : syracuseStep 830945 = 623209) B623209
theorem B830963 : Blo 550806 830963 := bstep (se 1 (by rfl) ⟨623222, by rfl⟩ : syracuseStep 830963 = 1246445) B1246445
theorem B830993 : Blo 550806 830993 := bstep (se 2 (by rfl) ⟨311622, by rfl⟩ : syracuseStep 830993 = 623245) B623245
theorem B2797091 : Blo 550806 2797091 := bstep (se 1 (by rfl) ⟨2097818, by rfl⟩ : syracuseStep 2797091 = 4195637) B4195637
theorem B831011 : Blo 550806 831011 := bstep (se 1 (by rfl) ⟨623258, by rfl⟩ : syracuseStep 831011 = 1246517) B1246517
theorem B831041 : Blo 550806 831041 := bstep (se 2 (by rfl) ⟨311640, by rfl⟩ : syracuseStep 831041 = 623281) B623281
theorem B831059 : Blo 550806 831059 := bstep (se 1 (by rfl) ⟨623294, by rfl⟩ : syracuseStep 831059 = 1246589) B1246589
theorem B831089 : Blo 550806 831089 := bstep (se 2 (by rfl) ⟨311658, by rfl⟩ : syracuseStep 831089 = 623317) B623317
theorem B831107 : Blo 550806 831107 := bstep (se 1 (by rfl) ⟨623330, by rfl⟩ : syracuseStep 831107 = 1246661) B1246661
theorem B831137 : Blo 550806 831137 := bstep (se 2 (by rfl) ⟨311676, by rfl⟩ : syracuseStep 831137 = 623353) B623353
theorem B831155 : Blo 550806 831155 := bstep (se 1 (by rfl) ⟨623366, by rfl⟩ : syracuseStep 831155 = 1246733) B1246733
theorem B831185 : Blo 550806 831185 := bstep (se 2 (by rfl) ⟨311694, by rfl⟩ : syracuseStep 831185 = 623389) B623389
theorem B831203 : Blo 550806 831203 := bstep (se 1 (by rfl) ⟨623402, by rfl⟩ : syracuseStep 831203 = 1246805) B1246805
theorem B831233 : Blo 550806 831233 := bstep (se 2 (by rfl) ⟨311712, by rfl⟩ : syracuseStep 831233 = 623425) B623425
theorem B831251 : Blo 550806 831251 := bstep (se 1 (by rfl) ⟨623438, by rfl⟩ : syracuseStep 831251 = 1246877) B1246877
theorem B929569 : Blo 550806 929569 := bstep (se 2 (by rfl) ⟨348588, by rfl⟩ : syracuseStep 929569 = 697177) B697177
theorem B831281 : Blo 550806 831281 := bstep (se 2 (by rfl) ⟨311730, by rfl⟩ : syracuseStep 831281 = 623461) B623461
theorem B929603 : Blo 550806 929603 := bstep (se 1 (by rfl) ⟨697202, by rfl⟩ : syracuseStep 929603 = 1394405) B1394405
theorem B831299 : Blo 550806 831299 := bstep (se 1 (by rfl) ⟨623474, by rfl⟩ : syracuseStep 831299 = 1246949) B1246949
theorem B831329 : Blo 550806 831329 := bstep (se 2 (by rfl) ⟨311748, by rfl⟩ : syracuseStep 831329 = 623497) B623497
theorem B4730723 : Blo 550806 4730723 := bstep (se 1 (by rfl) ⟨3548042, by rfl⟩ : syracuseStep 4730723 = 7096085) B7096085
theorem B5320561 : Blo 550806 5320561 := bstep (se 2 (by rfl) ⟨1995210, by rfl⟩ : syracuseStep 5320561 = 3990421) B3990421
theorem B831347 : Blo 550806 831347 := bstep (se 1 (by rfl) ⟨623510, by rfl⟩ : syracuseStep 831347 = 1247021) B1247021
theorem B831377 : Blo 550806 831377 := bstep (se 2 (by rfl) ⟨311766, by rfl⟩ : syracuseStep 831377 = 623533) B623533
theorem B831395 : Blo 550806 831395 := bstep (se 1 (by rfl) ⟨623546, by rfl⟩ : syracuseStep 831395 = 1247093) B1247093
theorem B3157937 : Blo 550806 3157937 := bstep (se 2 (by rfl) ⟨1184226, by rfl⟩ : syracuseStep 3157937 = 2368453) B2368453
theorem B831425 : Blo 550806 831425 := bstep (se 2 (by rfl) ⟨311784, by rfl⟩ : syracuseStep 831425 = 623569) B623569
theorem B929731 : Blo 550806 929731 := bstep (se 1 (by rfl) ⟨697298, by rfl⟩ : syracuseStep 929731 = 1394597) B1394597
theorem B831443 : Blo 550806 831443 := bstep (se 1 (by rfl) ⟨623582, by rfl⟩ : syracuseStep 831443 = 1247165) B1247165
theorem B831473 : Blo 550806 831473 := bstep (se 2 (by rfl) ⟨311802, by rfl⟩ : syracuseStep 831473 = 623605) B623605
theorem B831491 : Blo 550806 831491 := bstep (se 1 (by rfl) ⟨623618, by rfl⟩ : syracuseStep 831491 = 1247237) B1247237
theorem B831521 : Blo 550806 831521 := bstep (se 2 (by rfl) ⟨311820, by rfl⟩ : syracuseStep 831521 = 623641) B623641
theorem B831539 : Blo 550806 831539 := bstep (se 1 (by rfl) ⟨623654, by rfl⟩ : syracuseStep 831539 = 1247309) B1247309
theorem B700483 : Blo 550806 700483 := bstep (se 1 (by rfl) ⟨525362, by rfl⟩ : syracuseStep 700483 = 1050725) B1050725
theorem B929873 : Blo 550806 929873 := bstep (se 2 (by rfl) ⟨348702, by rfl⟩ : syracuseStep 929873 = 697405) B697405
theorem B831569 : Blo 550806 831569 := bstep (se 2 (by rfl) ⟨311838, by rfl⟩ : syracuseStep 831569 = 623677) B623677
theorem B831587 : Blo 550806 831587 := bstep (se 1 (by rfl) ⟨623690, by rfl⟩ : syracuseStep 831587 = 1247381) B1247381
theorem B831617 : Blo 550806 831617 := bstep (se 2 (by rfl) ⟨311856, by rfl⟩ : syracuseStep 831617 = 623713) B623713
theorem B831635 : Blo 550806 831635 := bstep (se 1 (by rfl) ⟨623726, by rfl⟩ : syracuseStep 831635 = 1247453) B1247453
theorem B700579 : Blo 550806 700579 := bstep (se 1 (by rfl) ⟨525434, by rfl⟩ : syracuseStep 700579 = 1050869) B1050869
theorem B1421489 : Blo 550806 1421489 := bstep (se 2 (by rfl) ⟨533058, by rfl⟩ : syracuseStep 1421489 = 1066117) B1066117
theorem B831665 : Blo 550806 831665 := bstep (se 2 (by rfl) ⟨311874, by rfl⟩ : syracuseStep 831665 = 623749) B623749
theorem B831683 : Blo 550806 831683 := bstep (se 1 (by rfl) ⟨623762, by rfl⟩ : syracuseStep 831683 = 1247525) B1247525
theorem B930001 : Blo 550806 930001 := bstep (se 2 (by rfl) ⟨348750, by rfl⟩ : syracuseStep 930001 = 697501) B697501
theorem B831713 : Blo 550806 831713 := bstep (se 2 (by rfl) ⟨311892, by rfl⟩ : syracuseStep 831713 = 623785) B623785
theorem B930035 : Blo 550806 930035 := bstep (se 1 (by rfl) ⟨697526, by rfl⟩ : syracuseStep 930035 = 1395053) B1395053
theorem B831731 : Blo 550806 831731 := bstep (se 1 (by rfl) ⟨623798, by rfl⟩ : syracuseStep 831731 = 1247597) B1247597
theorem B831761 : Blo 550806 831761 := bstep (se 2 (by rfl) ⟨311910, by rfl⟩ : syracuseStep 831761 = 623821) B623821
theorem B831779 : Blo 550806 831779 := bstep (se 1 (by rfl) ⟨623834, by rfl⟩ : syracuseStep 831779 = 1247669) B1247669
theorem B831809 : Blo 550806 831809 := bstep (se 2 (by rfl) ⟨311928, by rfl⟩ : syracuseStep 831809 = 623857) B623857
theorem B2797901 : Blo 550806 2797901 := bstep (se 3 (by rfl) ⟨524606, by rfl⟩ : syracuseStep 2797901 = 1049213) B1049213
theorem B831827 : Blo 550806 831827 := bstep (se 1 (by rfl) ⟨623870, by rfl⟩ : syracuseStep 831827 = 1247741) B1247741
theorem B831857 : Blo 550806 831857 := bstep (se 2 (by rfl) ⟨311946, by rfl⟩ : syracuseStep 831857 = 623893) B623893
theorem B930163 : Blo 550806 930163 := bstep (se 1 (by rfl) ⟨697622, by rfl⟩ : syracuseStep 930163 = 1395245) B1395245
theorem B831875 : Blo 550806 831875 := bstep (se 1 (by rfl) ⟨623906, by rfl⟩ : syracuseStep 831875 = 1247813) B1247813
theorem B1814929 : Blo 550806 1814929 := bstep (se 2 (by rfl) ⟨680598, by rfl⟩ : syracuseStep 1814929 = 1361197) B1361197
theorem B831905 : Blo 550806 831905 := bstep (se 2 (by rfl) ⟨311964, by rfl⟩ : syracuseStep 831905 = 623929) B623929
theorem B831923 : Blo 550806 831923 := bstep (se 1 (by rfl) ⟨623942, by rfl⟩ : syracuseStep 831923 = 1247885) B1247885
theorem B831953 : Blo 550806 831953 := bstep (se 2 (by rfl) ⟨311982, by rfl⟩ : syracuseStep 831953 = 623965) B623965
theorem B831971 : Blo 550806 831971 := bstep (se 1 (by rfl) ⟨623978, by rfl⟩ : syracuseStep 831971 = 1247957) B1247957
theorem B1683949 : Blo 550806 1683949 := bstep (se 3 (by rfl) ⟨315740, by rfl⟩ : syracuseStep 1683949 = 631481) B631481
theorem B930305 : Blo 550806 930305 := bstep (se 2 (by rfl) ⟨348864, by rfl⟩ : syracuseStep 930305 = 697729) B697729
theorem B832001 : Blo 550806 832001 := bstep (se 2 (by rfl) ⟨312000, by rfl⟩ : syracuseStep 832001 = 624001) B624001
theorem B832019 : Blo 550806 832019 := bstep (se 1 (by rfl) ⟨624014, by rfl⟩ : syracuseStep 832019 = 1248029) B1248029
theorem B832049 : Blo 550806 832049 := bstep (se 2 (by rfl) ⟨312018, by rfl⟩ : syracuseStep 832049 = 624037) B624037
theorem B832067 : Blo 550806 832067 := bstep (se 1 (by rfl) ⟨624050, by rfl⟩ : syracuseStep 832067 = 1248101) B1248101
theorem B832097 : Blo 550806 832097 := bstep (se 2 (by rfl) ⟨312036, by rfl⟩ : syracuseStep 832097 = 624073) B624073
theorem B832115 : Blo 550806 832115 := bstep (se 1 (by rfl) ⟨624086, by rfl⟩ : syracuseStep 832115 = 1248173) B1248173
theorem B930433 : Blo 550806 930433 := bstep (se 2 (by rfl) ⟨348912, by rfl⟩ : syracuseStep 930433 = 697825) B697825
theorem B5026445 : Blo 550806 5026445 := bstep (se 3 (by rfl) ⟨942458, by rfl⟩ : syracuseStep 5026445 = 1884917) B1884917
theorem B3846797 : Blo 550806 3846797 := bstep (se 3 (by rfl) ⟨721274, by rfl⟩ : syracuseStep 3846797 = 1442549) B1442549
theorem B832145 : Blo 550806 832145 := bstep (se 2 (by rfl) ⟨312054, by rfl⟩ : syracuseStep 832145 = 624109) B624109
theorem B701075 : Blo 550806 701075 := bstep (se 1 (by rfl) ⟨525806, by rfl⟩ : syracuseStep 701075 = 1051613) B1051613
theorem B930467 : Blo 550806 930467 := bstep (se 1 (by rfl) ⟨697850, by rfl⟩ : syracuseStep 930467 = 1395701) B1395701
theorem B832163 : Blo 550806 832163 := bstep (se 1 (by rfl) ⟨624122, by rfl⟩ : syracuseStep 832163 = 1248245) B1248245
theorem B832193 : Blo 550806 832193 := bstep (se 2 (by rfl) ⟨312072, by rfl⟩ : syracuseStep 832193 = 624145) B624145
theorem B4207301 : Blo 550806 4207301 := bstep (se 4 (by rfl) ⟨394434, by rfl⟩ : syracuseStep 4207301 = 788869) B788869
theorem B930595 : Blo 550806 930595 := bstep (se 1 (by rfl) ⟨697946, by rfl⟩ : syracuseStep 930595 = 1395893) B1395893
theorem B1323857 : Blo 550806 1323857 := bstep (se 2 (by rfl) ⟨496446, by rfl⟩ : syracuseStep 1323857 = 992893) B992893
theorem B930737 : Blo 550806 930737 := bstep (se 2 (by rfl) ⟨349026, by rfl⟩ : syracuseStep 930737 = 698053) B698053
theorem B898003 : Blo 550806 898003 := bstep (se 1 (by rfl) ⟨673502, by rfl⟩ : syracuseStep 898003 = 1347005) B1347005
theorem B996337 : Blo 550806 996337 := bstep (se 2 (by rfl) ⟨373626, by rfl⟩ : syracuseStep 996337 = 747253) B747253
theorem B930865 : Blo 550806 930865 := bstep (se 2 (by rfl) ⟨349074, by rfl⟩ : syracuseStep 930865 = 698149) B698149
theorem B930899 : Blo 550806 930899 := bstep (se 1 (by rfl) ⟨698174, by rfl⟩ : syracuseStep 930899 = 1396349) B1396349
theorem B898211 : Blo 550806 898211 := bstep (se 1 (by rfl) ⟨673658, by rfl⟩ : syracuseStep 898211 = 1347317) B1347317
theorem B1324241 : Blo 550806 1324241 := bstep (se 2 (by rfl) ⟨496590, by rfl⟩ : syracuseStep 1324241 = 993181) B993181
theorem B931027 : Blo 550806 931027 := bstep (se 1 (by rfl) ⟨698270, by rfl⟩ : syracuseStep 931027 = 1396541) B1396541
theorem B10073315 : Blo 550806 10073315 := bstep (se 1 (by rfl) ⟨7554986, by rfl⟩ : syracuseStep 10073315 = 15109973) B15109973
theorem B701779 : Blo 550806 701779 := bstep (se 1 (by rfl) ⟨526334, by rfl⟩ : syracuseStep 701779 = 1052669) B1052669
theorem B931169 : Blo 550806 931169 := bstep (se 2 (by rfl) ⟨349188, by rfl⟩ : syracuseStep 931169 = 698377) B698377
theorem B3159395 : Blo 550806 3159395 := bstep (se 1 (by rfl) ⟨2369546, by rfl⟩ : syracuseStep 3159395 = 4739093) B4739093
theorem B1324451 : Blo 550806 1324451 := bstep (se 1 (by rfl) ⟨993338, by rfl⟩ : syracuseStep 1324451 = 1986677) B1986677
theorem B1684909 : Blo 550806 1684909 := bstep (se 3 (by rfl) ⟨315920, by rfl⟩ : syracuseStep 1684909 = 631841) B631841
theorem B701875 : Blo 550806 701875 := bstep (se 1 (by rfl) ⟨526406, by rfl⟩ : syracuseStep 701875 = 1052813) B1052813
theorem B931297 : Blo 550806 931297 := bstep (se 2 (by rfl) ⟨349236, by rfl⟩ : syracuseStep 931297 = 698473) B698473
theorem B931331 : Blo 550806 931331 := bstep (se 1 (by rfl) ⟨698498, by rfl⟩ : syracuseStep 931331 = 1396997) B1396997
theorem B898627 : Blo 550806 898627 := bstep (se 1 (by rfl) ⟨673970, by rfl⟩ : syracuseStep 898627 = 1347941) B1347941
theorem B931459 : Blo 550806 931459 := bstep (se 1 (by rfl) ⟨698594, by rfl⟩ : syracuseStep 931459 = 1397189) B1397189
theorem B1259185 : Blo 550806 1259185 := bstep (se 2 (by rfl) ⟨472194, by rfl⟩ : syracuseStep 1259185 = 944389) B944389
theorem B931601 : Blo 550806 931601 := bstep (se 2 (by rfl) ⟨349350, by rfl⟩ : syracuseStep 931601 = 698701) B698701
theorem B898913 : Blo 550806 898913 := bstep (se 2 (by rfl) ⟨337092, by rfl⟩ : syracuseStep 898913 = 674185) B674185
theorem B931729 : Blo 550806 931729 := bstep (se 2 (by rfl) ⟨349398, by rfl⟩ : syracuseStep 931729 = 698797) B698797
theorem B931763 : Blo 550806 931763 := bstep (se 1 (by rfl) ⟨698822, by rfl⟩ : syracuseStep 931763 = 1397645) B1397645
theorem B931891 : Blo 550806 931891 := bstep (se 1 (by rfl) ⟨698918, by rfl⟩ : syracuseStep 931891 = 1397837) B1397837
theorem B932033 : Blo 550806 932033 := bstep (se 2 (by rfl) ⟨349512, by rfl⟩ : syracuseStep 932033 = 699025) B699025
theorem B1325297 : Blo 550806 1325297 := bstep (se 2 (by rfl) ⟨496986, by rfl⟩ : syracuseStep 1325297 = 993973) B993973
theorem B932161 : Blo 550806 932161 := bstep (se 2 (by rfl) ⟨349560, by rfl⟩ : syracuseStep 932161 = 699121) B699121
theorem B932195 : Blo 550806 932195 := bstep (se 1 (by rfl) ⟨699146, by rfl⟩ : syracuseStep 932195 = 1398293) B1398293
theorem B1194385 : Blo 550806 1194385 := bstep (se 2 (by rfl) ⟨447894, by rfl⟩ : syracuseStep 1194385 = 895789) B895789
theorem B1325489 : Blo 550806 1325489 := bstep (se 2 (by rfl) ⟨497058, by rfl⟩ : syracuseStep 1325489 = 994117) B994117
theorem B932323 : Blo 550806 932323 := bstep (se 1 (by rfl) ⟨699242, by rfl⟩ : syracuseStep 932323 = 1398485) B1398485
theorem B932465 : Blo 550806 932465 := bstep (se 2 (by rfl) ⟨349674, by rfl⟩ : syracuseStep 932465 = 699349) B699349
theorem B932593 : Blo 550806 932593 := bstep (se 2 (by rfl) ⟨349722, by rfl⟩ : syracuseStep 932593 = 699445) B699445
theorem B932627 : Blo 550806 932627 := bstep (se 1 (by rfl) ⟨699470, by rfl⟩ : syracuseStep 932627 = 1398941) B1398941
theorem B3554117 : Blo 550806 3554117 := bstep (se 4 (by rfl) ⟨333198, by rfl⟩ : syracuseStep 3554117 = 666397) B666397
theorem B932755 : Blo 550806 932755 := bstep (se 1 (by rfl) ⟨699566, by rfl⟩ : syracuseStep 932755 = 1399133) B1399133
theorem B3783601 : Blo 550806 3783601 := bstep (se 2 (by rfl) ⟨1418850, by rfl⟩ : syracuseStep 3783601 = 2837701) B2837701
theorem B736259 : Blo 550806 736259 := bstep (se 1 (by rfl) ⟨552194, by rfl⟩ : syracuseStep 736259 = 1104389) B1104389
theorem B932897 : Blo 550806 932897 := bstep (se 2 (by rfl) ⟨349836, by rfl⟩ : syracuseStep 932897 = 699673) B699673
theorem B637987 : Blo 550806 637987 := bstep (se 1 (by rfl) ⟨478490, by rfl⟩ : syracuseStep 637987 = 956981) B956981
theorem B933025 : Blo 550806 933025 := bstep (se 2 (by rfl) ⟨349884, by rfl⟩ : syracuseStep 933025 = 699769) B699769
theorem B2800817 : Blo 550806 2800817 := bstep (se 2 (by rfl) ⟨1050306, by rfl⟩ : syracuseStep 2800817 = 2100613) B2100613
theorem B933059 : Blo 550806 933059 := bstep (se 1 (by rfl) ⟨699794, by rfl⟩ : syracuseStep 933059 = 1399589) B1399589
theorem B933187 : Blo 550806 933187 := bstep (se 1 (by rfl) ⟨699890, by rfl⟩ : syracuseStep 933187 = 1399781) B1399781
theorem B933329 : Blo 550806 933329 := bstep (se 2 (by rfl) ⟨349998, by rfl⟩ : syracuseStep 933329 = 699997) B699997
theorem B4472333 : Blo 550806 4472333 := bstep (se 3 (by rfl) ⟨838562, by rfl⟩ : syracuseStep 4472333 = 1677125) B1677125
theorem B933457 : Blo 550806 933457 := bstep (se 2 (by rfl) ⟨350046, by rfl⟩ : syracuseStep 933457 = 700093) B700093
theorem B933491 : Blo 550806 933491 := bstep (se 1 (by rfl) ⟨700118, by rfl⟩ : syracuseStep 933491 = 1400237) B1400237
theorem B933619 : Blo 550806 933619 := bstep (se 1 (by rfl) ⟨700214, by rfl⟩ : syracuseStep 933619 = 1400429) B1400429
theorem B933761 : Blo 550806 933761 := bstep (se 2 (by rfl) ⟨350160, by rfl⟩ : syracuseStep 933761 = 700321) B700321
theorem B11321315 : Blo 550806 11321315 := bstep (se 1 (by rfl) ⟨8490986, by rfl⟩ : syracuseStep 11321315 = 16981973) B16981973
theorem B933889 : Blo 550806 933889 := bstep (se 2 (by rfl) ⟨350208, by rfl⟩ : syracuseStep 933889 = 700417) B700417
theorem B933923 : Blo 550806 933923 := bstep (se 1 (by rfl) ⟨700442, by rfl⟩ : syracuseStep 933923 = 1400885) B1400885
theorem B1261649 : Blo 550806 1261649 := bstep (se 2 (by rfl) ⟨473118, by rfl⟩ : syracuseStep 1261649 = 946237) B946237
theorem B934051 : Blo 550806 934051 := bstep (se 1 (by rfl) ⟨700538, by rfl⟩ : syracuseStep 934051 = 1401077) B1401077
theorem B934193 : Blo 550806 934193 := bstep (se 2 (by rfl) ⟨350322, by rfl⟩ : syracuseStep 934193 = 700645) B700645
theorem B2244941 : Blo 550806 2244941 := bstep (se 3 (by rfl) ⟨420926, by rfl⟩ : syracuseStep 2244941 = 841853) B841853
theorem B1327441 : Blo 550806 1327441 := bstep (se 2 (by rfl) ⟨497790, by rfl⟩ : syracuseStep 1327441 = 995581) B995581
theorem B934321 : Blo 550806 934321 := bstep (se 2 (by rfl) ⟨350370, by rfl⟩ : syracuseStep 934321 = 700741) B700741
theorem B934355 : Blo 550806 934355 := bstep (se 1 (by rfl) ⟨700766, by rfl⟩ : syracuseStep 934355 = 1401533) B1401533
theorem B934483 : Blo 550806 934483 := bstep (se 1 (by rfl) ⟨700862, by rfl⟩ : syracuseStep 934483 = 1401725) B1401725
theorem B2802275 : Blo 550806 2802275 := bstep (se 1 (by rfl) ⟨2101706, by rfl⟩ : syracuseStep 2802275 = 4203413) B4203413
theorem B934625 : Blo 550806 934625 := bstep (se 2 (by rfl) ⟨350484, by rfl⟩ : syracuseStep 934625 = 700969) B700969
theorem B4801265 : Blo 550806 4801265 := bstep (se 2 (by rfl) ⟨1800474, by rfl⟩ : syracuseStep 4801265 = 3600949) B3600949
theorem B934753 : Blo 550806 934753 := bstep (se 2 (by rfl) ⟨350532, by rfl⟩ : syracuseStep 934753 = 701065) B701065
theorem B934787 : Blo 550806 934787 := bstep (se 1 (by rfl) ⟨701090, by rfl⟩ : syracuseStep 934787 = 1402181) B1402181
theorem B934915 : Blo 550806 934915 := bstep (se 1 (by rfl) ⟨701186, by rfl⟩ : syracuseStep 934915 = 1402373) B1402373
theorem B935057 : Blo 550806 935057 := bstep (se 2 (by rfl) ⟨350646, by rfl⟩ : syracuseStep 935057 = 701293) B701293
theorem B935185 : Blo 550806 935185 := bstep (se 2 (by rfl) ⟨350694, by rfl⟩ : syracuseStep 935185 = 701389) B701389
theorem B935219 : Blo 550806 935219 := bstep (se 1 (by rfl) ⟨701414, by rfl⟩ : syracuseStep 935219 = 1402829) B1402829
theorem B2803085 : Blo 550806 2803085 := bstep (se 3 (by rfl) ⟨525578, by rfl⟩ : syracuseStep 2803085 = 1051157) B1051157
theorem B935347 : Blo 550806 935347 := bstep (se 1 (by rfl) ⟨701510, by rfl⟩ : syracuseStep 935347 = 1403021) B1403021
theorem B1820141 : Blo 550806 1820141 := bstep (se 3 (by rfl) ⟨341276, by rfl⟩ : syracuseStep 1820141 = 682553) B682553
theorem B935489 : Blo 550806 935489 := bstep (se 2 (by rfl) ⟨350808, by rfl⟩ : syracuseStep 935489 = 701617) B701617
theorem B1394243 : Blo 550806 1394243 := bstep (se 1 (by rfl) ⟨1045682, by rfl⟩ : syracuseStep 1394243 = 2091365) B2091365
theorem B2246285 : Blo 550806 2246285 := bstep (se 3 (by rfl) ⟨421178, by rfl⟩ : syracuseStep 2246285 = 842357) B842357
theorem B935617 : Blo 550806 935617 := bstep (se 2 (by rfl) ⟨350856, by rfl⟩ : syracuseStep 935617 = 701713) B701713
theorem B935651 : Blo 550806 935651 := bstep (se 1 (by rfl) ⟨701738, by rfl⟩ : syracuseStep 935651 = 1403477) B1403477
theorem B1394435 : Blo 550806 1394435 := bstep (se 1 (by rfl) ⟨1045826, by rfl⟩ : syracuseStep 1394435 = 2091653) B2091653
theorem B4474693 : Blo 550806 4474693 := bstep (se 4 (by rfl) ⟨419502, by rfl⟩ : syracuseStep 4474693 = 839005) B839005
theorem B935779 : Blo 550806 935779 := bstep (se 1 (by rfl) ⟨701834, by rfl⟩ : syracuseStep 935779 = 1403669) B1403669
theorem B1066979 : Blo 550806 1066979 := bstep (se 1 (by rfl) ⟨800234, by rfl⟩ : syracuseStep 1066979 = 1600469) B1600469
theorem B935921 : Blo 550806 935921 := bstep (se 2 (by rfl) ⟨350970, by rfl⟩ : syracuseStep 935921 = 701941) B701941
theorem B8407153 : Blo 550806 8407153 := bstep (se 2 (by rfl) ⟨3152682, by rfl⟩ : syracuseStep 8407153 = 6305365) B6305365
theorem B936049 : Blo 550806 936049 := bstep (se 2 (by rfl) ⟨351018, by rfl⟩ : syracuseStep 936049 = 702037) B702037
theorem B1886339 : Blo 550806 1886339 := bstep (se 1 (by rfl) ⟨1414754, by rfl⟩ : syracuseStep 1886339 = 2829509) B2829509
theorem B936083 : Blo 550806 936083 := bstep (se 1 (by rfl) ⟨702062, by rfl⟩ : syracuseStep 936083 = 1404125) B1404125
theorem B7981253 : Blo 550806 7981253 := bstep (se 4 (by rfl) ⟨748242, by rfl⟩ : syracuseStep 7981253 = 1496485) B1496485
theorem B936211 : Blo 550806 936211 := bstep (se 1 (by rfl) ⟨702158, by rfl⟩ : syracuseStep 936211 = 1404317) B1404317
theorem B1493425 : Blo 550806 1493425 := bstep (se 2 (by rfl) ⟨560034, by rfl⟩ : syracuseStep 1493425 = 1120069) B1120069
theorem B1395377 : Blo 550806 1395377 := bstep (se 2 (by rfl) ⟨523266, by rfl⟩ : syracuseStep 1395377 = 1046533) B1046533
theorem B1395427 : Blo 550806 1395427 := bstep (se 1 (by rfl) ⟨1046570, by rfl⟩ : syracuseStep 1395427 = 2093141) B2093141
theorem B1395569 : Blo 550806 1395569 := bstep (se 2 (by rfl) ⟨523338, by rfl⟩ : syracuseStep 1395569 = 1046677) B1046677
theorem B1493923 : Blo 550806 1493923 := bstep (se 1 (by rfl) ⟨1120442, by rfl⟩ : syracuseStep 1493923 = 2240885) B2240885
theorem B839249 : Blo 550806 839249 := bstep (se 2 (by rfl) ⟨314718, by rfl⟩ : syracuseStep 839249 = 629437) B629437
theorem B1986275 : Blo 550806 1986275 := bstep (se 1 (by rfl) ⟨1489706, by rfl⟩ : syracuseStep 1986275 = 2979413) B2979413
theorem B1396561 : Blo 550806 1396561 := bstep (se 2 (by rfl) ⟨523710, by rfl⟩ : syracuseStep 1396561 = 1047421) B1047421
theorem B1494929 : Blo 550806 1494929 := bstep (se 2 (by rfl) ⟨560598, by rfl⟩ : syracuseStep 1494929 = 1121197) B1121197
theorem B16175045 : Blo 550806 16175045 := bstep (se 4 (by rfl) ⟨1516410, by rfl⟩ : syracuseStep 16175045 = 3032821) B3032821
theorem B1396835 : Blo 550806 1396835 := bstep (se 1 (by rfl) ⟨1047626, by rfl⟩ : syracuseStep 1396835 = 2095253) B2095253
theorem B1593539 : Blo 550806 1593539 := bstep (se 1 (by rfl) ⟨1195154, by rfl⟩ : syracuseStep 1593539 = 2390309) B2390309
theorem B2806001 : Blo 550806 2806001 := bstep (se 2 (by rfl) ⟨1052250, by rfl⟩ : syracuseStep 2806001 = 2104501) B2104501
theorem B1397027 : Blo 550806 1397027 := bstep (se 1 (by rfl) ⟨1047770, by rfl⟩ : syracuseStep 1397027 = 2095541) B2095541
theorem B6279605 : Blo 550806 6279605 := bstep (se 5 (by rfl) ⟨294356, by rfl⟩ : syracuseStep 6279605 = 588713) B588713
theorem B5985251 : Blo 550806 5985251 := bstep (se 1 (by rfl) ⟨4488938, by rfl⟩ : syracuseStep 5985251 = 8977877) B8977877
theorem B1922051 : Blo 550806 1922051 := bstep (se 1 (by rfl) ⟨1441538, by rfl⟩ : syracuseStep 1922051 = 2883077) B2883077
theorem B1496141 : Blo 550806 1496141 := bstep (se 3 (by rfl) ⟨280526, by rfl⟩ : syracuseStep 1496141 = 561053) B561053
theorem B1397969 : Blo 550806 1397969 := bstep (se 2 (by rfl) ⟨524238, by rfl⟩ : syracuseStep 1397969 = 1048477) B1048477
theorem B1398019 : Blo 550806 1398019 := bstep (se 1 (by rfl) ⟨1048514, by rfl⟩ : syracuseStep 1398019 = 2097029) B2097029
theorem B1398161 : Blo 550806 1398161 := bstep (se 2 (by rfl) ⟨524310, by rfl⟩ : syracuseStep 1398161 = 1048621) B1048621
theorem B3823109 : Blo 550806 3823109 := bstep (se 4 (by rfl) ⟨358416, by rfl⟩ : syracuseStep 3823109 = 716833) B716833
theorem B2807459 : Blo 550806 2807459 := bstep (se 1 (by rfl) ⟨2105594, by rfl⟩ : syracuseStep 2807459 = 4211189) B4211189
theorem B841585 : Blo 550806 841585 := bstep (se 2 (by rfl) ⟨315594, by rfl⟩ : syracuseStep 841585 = 631189) B631189
theorem B14211125 : Blo 550806 14211125 := bstep (se 5 (by rfl) ⟨666146, by rfl⟩ : syracuseStep 14211125 = 1332293) B1332293
theorem B841889 : Blo 550806 841889 := bstep (se 2 (by rfl) ⟨315708, by rfl⟩ : syracuseStep 841889 = 631417) B631417
theorem B1497361 : Blo 550806 1497361 := bstep (se 2 (by rfl) ⟨561510, by rfl⟩ : syracuseStep 1497361 = 1123021) B1123021
theorem B1136963 : Blo 550806 1136963 := bstep (se 1 (by rfl) ⟨852722, by rfl⟩ : syracuseStep 1136963 = 1705445) B1705445
theorem B1399153 : Blo 550806 1399153 := bstep (se 2 (by rfl) ⟨524682, by rfl⟩ : syracuseStep 1399153 = 1049365) B1049365
theorem B2808269 : Blo 550806 2808269 := bstep (se 3 (by rfl) ⟨526550, by rfl⟩ : syracuseStep 2808269 = 1053101) B1053101
theorem B1595875 : Blo 550806 1595875 := bstep (se 1 (by rfl) ⟨1196906, by rfl⟩ : syracuseStep 1595875 = 2393813) B2393813
theorem B1530499 : Blo 550806 1530499 := bstep (se 1 (by rfl) ⟨1147874, by rfl⟩ : syracuseStep 1530499 = 2295749) B2295749
theorem B1399427 : Blo 550806 1399427 := bstep (se 1 (by rfl) ⟨1049570, by rfl⟩ : syracuseStep 1399427 = 2099141) B2099141
theorem B2513699 : Blo 550806 2513699 := bstep (se 1 (by rfl) ⟨1885274, by rfl⟩ : syracuseStep 2513699 = 3770549) B3770549
theorem B1399619 : Blo 550806 1399619 := bstep (se 1 (by rfl) ⟨1049714, by rfl⟩ : syracuseStep 1399619 = 2099429) B2099429
theorem B4184945 : Blo 550806 4184945 := bstep (se 2 (by rfl) ⟨1569354, by rfl⟩ : syracuseStep 4184945 = 3138709) B3138709
theorem B1596611 : Blo 550806 1596611 := bstep (se 1 (by rfl) ⟨1197458, by rfl⟩ : syracuseStep 1596611 = 2394917) B2394917
theorem B8936675 : Blo 550806 8936675 := bstep (se 1 (by rfl) ⟨6702506, by rfl⟩ : syracuseStep 8936675 = 13405013) B13405013
theorem B744913 : Blo 550806 744913 := bstep (se 2 (by rfl) ⟨279342, by rfl⟩ : syracuseStep 744913 = 558685) B558685
theorem B1859057 : Blo 550806 1859057 := bstep (se 2 (by rfl) ⟨697146, by rfl⟩ : syracuseStep 1859057 = 1394293) B1394293
theorem B3137251 : Blo 550806 3137251 := bstep (se 1 (by rfl) ⟨2352938, by rfl⟩ : syracuseStep 3137251 = 4705877) B4705877
theorem B1400561 : Blo 550806 1400561 := bstep (se 2 (by rfl) ⟨525210, by rfl⟩ : syracuseStep 1400561 = 1050421) B1050421
theorem B1400611 : Blo 550806 1400611 := bstep (se 1 (by rfl) ⟨1050458, by rfl⟩ : syracuseStep 1400611 = 2100917) B2100917
theorem B1498961 : Blo 550806 1498961 := bstep (se 2 (by rfl) ⟨562110, by rfl⟩ : syracuseStep 1498961 = 1124221) B1124221
theorem B1400753 : Blo 550806 1400753 := bstep (se 2 (by rfl) ⟨525282, by rfl⟩ : syracuseStep 1400753 = 1050565) B1050565
theorem B1859597 : Blo 550806 1859597 := bstep (se 3 (by rfl) ⟨348674, by rfl⟩ : syracuseStep 1859597 = 697349) B697349
theorem B1859651 : Blo 550806 1859651 := bstep (se 1 (by rfl) ⟨1394738, by rfl⟩ : syracuseStep 1859651 = 2789477) B2789477
theorem B3137777 : Blo 550806 3137777 := bstep (se 2 (by rfl) ⟨1176666, by rfl⟩ : syracuseStep 3137777 = 2353333) B2353333
theorem B1859921 : Blo 550806 1859921 := bstep (se 2 (by rfl) ⟨697470, by rfl⟩ : syracuseStep 1859921 = 1394941) B1394941
theorem B13591061 : Blo 550806 13591061 := bstep (se 6 (by rfl) ⟨318540, by rfl⟩ : syracuseStep 13591061 = 637081) B637081
theorem B942787 : Blo 550806 942787 := bstep (se 1 (by rfl) ⟨707090, by rfl⟩ : syracuseStep 942787 = 1414181) B1414181
theorem B1860461 : Blo 550806 1860461 := bstep (se 3 (by rfl) ⟨348836, by rfl⟩ : syracuseStep 1860461 = 697673) B697673
theorem B1401745 : Blo 550806 1401745 := bstep (se 2 (by rfl) ⟨525654, by rfl⟩ : syracuseStep 1401745 = 1051309) B1051309
theorem B1860515 : Blo 550806 1860515 := bstep (se 1 (by rfl) ⟨1395386, by rfl⟩ : syracuseStep 1860515 = 2790773) B2790773
theorem B1893347 : Blo 550806 1893347 := bstep (se 1 (by rfl) ⟨1420010, by rfl⟩ : syracuseStep 1893347 = 2840021) B2840021
theorem B910387 : Blo 550806 910387 := bstep (se 1 (by rfl) ⟨682790, by rfl⟩ : syracuseStep 910387 = 1365581) B1365581
theorem B1402019 : Blo 550806 1402019 := bstep (se 1 (by rfl) ⟨1051514, by rfl⟩ : syracuseStep 1402019 = 2103029) B2103029
theorem B1860785 : Blo 550806 1860785 := bstep (se 2 (by rfl) ⟨697794, by rfl⟩ : syracuseStep 1860785 = 1395589) B1395589
theorem B3368141 : Blo 550806 3368141 := bstep (se 3 (by rfl) ⟨631526, by rfl⟩ : syracuseStep 3368141 = 1263053) B1263053
theorem B3990883 : Blo 550806 3990883 := bstep (se 1 (by rfl) ⟨2993162, by rfl⟩ : syracuseStep 3990883 = 5986325) B5986325
theorem B1402211 : Blo 550806 1402211 := bstep (se 1 (by rfl) ⟨1051658, by rfl⟩ : syracuseStep 1402211 = 2103317) B2103317
theorem B746929 : Blo 550806 746929 := bstep (se 2 (by rfl) ⟨280098, by rfl⟩ : syracuseStep 746929 = 560197) B560197
theorem B943553 : Blo 550806 943553 := bstep (se 2 (by rfl) ⟨353832, by rfl⟩ : syracuseStep 943553 = 707665) B707665
theorem B6809141 : Blo 550806 6809141 := bstep (se 5 (by rfl) ⟨319178, by rfl⟩ : syracuseStep 6809141 = 638357) B638357
theorem B2418275 : Blo 550806 2418275 := bstep (se 1 (by rfl) ⟨1813706, by rfl⟩ : syracuseStep 2418275 = 3627413) B3627413
theorem B1894033 : Blo 550806 1894033 := bstep (se 2 (by rfl) ⟨710262, by rfl⟩ : syracuseStep 1894033 = 1420525) B1420525
theorem B3139235 : Blo 550806 3139235 := bstep (se 1 (by rfl) ⟨2354426, by rfl⟩ : syracuseStep 3139235 = 4708853) B4708853
theorem B1861325 : Blo 550806 1861325 := bstep (se 3 (by rfl) ⟨348998, by rfl⟩ : syracuseStep 1861325 = 697997) B697997
theorem B1861379 : Blo 550806 1861379 := bstep (se 1 (by rfl) ⟨1396034, by rfl⟩ : syracuseStep 1861379 = 2792069) B2792069
theorem B550819 : Blo 550806 550819 := bstep (se 1 (by rfl) ⟨413114, by rfl⟩ : syracuseStep 550819 = 826229) B826229
theorem B550835 : Blo 550806 550835 := bstep (se 1 (by rfl) ⟨413126, by rfl⟩ : syracuseStep 550835 = 826253) B826253
theorem B550851 : Blo 550806 550851 := bstep (se 1 (by rfl) ⟨413138, by rfl⟩ : syracuseStep 550851 = 826277) B826277
theorem B550867 : Blo 550806 550867 := bstep (se 1 (by rfl) ⟨413150, by rfl⟩ : syracuseStep 550867 = 826301) B826301
theorem B550883 : Blo 550806 550883 := bstep (se 1 (by rfl) ⟨413162, by rfl⟩ : syracuseStep 550883 = 826325) B826325
theorem B550899 : Blo 550806 550899 := bstep (se 1 (by rfl) ⟨413174, by rfl⟩ : syracuseStep 550899 = 826349) B826349
theorem B550915 : Blo 550806 550915 := bstep (se 1 (by rfl) ⟨413186, by rfl⟩ : syracuseStep 550915 = 826373) B826373
theorem B1861649 : Blo 550806 1861649 := bstep (se 2 (by rfl) ⟨698118, by rfl⟩ : syracuseStep 1861649 = 1396237) B1396237
theorem B550931 : Blo 550806 550931 := bstep (se 1 (by rfl) ⟨413198, by rfl⟩ : syracuseStep 550931 = 826397) B826397
theorem B550947 : Blo 550806 550947 := bstep (se 1 (by rfl) ⟨413210, by rfl⟩ : syracuseStep 550947 = 826421) B826421
theorem B550963 : Blo 550806 550963 := bstep (se 1 (by rfl) ⟨413222, by rfl⟩ : syracuseStep 550963 = 826445) B826445
theorem B550979 : Blo 550806 550979 := bstep (se 1 (by rfl) ⟨413234, by rfl⟩ : syracuseStep 550979 = 826469) B826469
theorem B550995 : Blo 550806 550995 := bstep (se 1 (by rfl) ⟨413246, by rfl⟩ : syracuseStep 550995 = 826493) B826493
theorem B551011 : Blo 550806 551011 := bstep (se 1 (by rfl) ⟨413258, by rfl⟩ : syracuseStep 551011 = 826517) B826517
theorem B551027 : Blo 550806 551027 := bstep (se 1 (by rfl) ⟨413270, by rfl⟩ : syracuseStep 551027 = 826541) B826541
theorem B551043 : Blo 550806 551043 := bstep (se 1 (by rfl) ⟨413282, by rfl⟩ : syracuseStep 551043 = 826565) B826565
theorem B551059 : Blo 550806 551059 := bstep (se 1 (by rfl) ⟨413294, by rfl⟩ : syracuseStep 551059 = 826589) B826589
theorem B551075 : Blo 550806 551075 := bstep (se 1 (by rfl) ⟨413306, by rfl⟩ : syracuseStep 551075 = 826613) B826613
theorem B551091 : Blo 550806 551091 := bstep (se 1 (by rfl) ⟨413318, by rfl⟩ : syracuseStep 551091 = 826637) B826637
theorem B551107 : Blo 550806 551107 := bstep (se 1 (by rfl) ⟨413330, by rfl⟩ : syracuseStep 551107 = 826661) B826661
theorem B3532997 : Blo 550806 3532997 := bstep (se 4 (by rfl) ⟨331218, by rfl⟩ : syracuseStep 3532997 = 662437) B662437
theorem B2123981 : Blo 550806 2123981 := bstep (se 3 (by rfl) ⟨398246, by rfl⟩ : syracuseStep 2123981 = 796493) B796493
theorem B1009873 : Blo 550806 1009873 := bstep (se 2 (by rfl) ⟨378702, by rfl⟩ : syracuseStep 1009873 = 757405) B757405
theorem B551123 : Blo 550806 551123 := bstep (se 1 (by rfl) ⟨413342, by rfl⟩ : syracuseStep 551123 = 826685) B826685
theorem B551139 : Blo 550806 551139 := bstep (se 1 (by rfl) ⟨413354, by rfl⟩ : syracuseStep 551139 = 826709) B826709
theorem B944369 : Blo 550806 944369 := bstep (se 2 (by rfl) ⟨354138, by rfl⟩ : syracuseStep 944369 = 708277) B708277
theorem B551155 : Blo 550806 551155 := bstep (se 1 (by rfl) ⟨413366, by rfl⟩ : syracuseStep 551155 = 826733) B826733
theorem B551171 : Blo 550806 551171 := bstep (se 1 (by rfl) ⟨413378, by rfl⟩ : syracuseStep 551171 = 826757) B826757
theorem B1403153 : Blo 550806 1403153 := bstep (se 2 (by rfl) ⟨526182, by rfl⟩ : syracuseStep 1403153 = 1052365) B1052365
theorem B551187 : Blo 550806 551187 := bstep (se 1 (by rfl) ⟨413390, by rfl⟩ : syracuseStep 551187 = 826781) B826781
theorem B551203 : Blo 550806 551203 := bstep (se 1 (by rfl) ⟨413402, by rfl⟩ : syracuseStep 551203 = 826805) B826805
theorem B551219 : Blo 550806 551219 := bstep (se 1 (by rfl) ⟨413414, by rfl⟩ : syracuseStep 551219 = 826829) B826829
theorem B551235 : Blo 550806 551235 := bstep (se 1 (by rfl) ⟨413426, by rfl⟩ : syracuseStep 551235 = 826853) B826853
theorem B1403203 : Blo 550806 1403203 := bstep (se 1 (by rfl) ⟨1052402, by rfl⟩ : syracuseStep 1403203 = 2104805) B2104805
theorem B551251 : Blo 550806 551251 := bstep (se 1 (by rfl) ⟨413438, by rfl⟩ : syracuseStep 551251 = 826877) B826877
theorem B551267 : Blo 550806 551267 := bstep (se 1 (by rfl) ⟨413450, by rfl⟩ : syracuseStep 551267 = 826901) B826901
theorem B1894769 : Blo 550806 1894769 := bstep (se 2 (by rfl) ⟨710538, by rfl⟩ : syracuseStep 1894769 = 1421077) B1421077
theorem B551283 : Blo 550806 551283 := bstep (se 1 (by rfl) ⟨413462, by rfl⟩ : syracuseStep 551283 = 826925) B826925
theorem B551299 : Blo 550806 551299 := bstep (se 1 (by rfl) ⟨413474, by rfl⟩ : syracuseStep 551299 = 826949) B826949
theorem B551315 : Blo 550806 551315 := bstep (se 1 (by rfl) ⟨413486, by rfl⟩ : syracuseStep 551315 = 826973) B826973
theorem B551331 : Blo 550806 551331 := bstep (se 1 (by rfl) ⟨413498, by rfl⟩ : syracuseStep 551331 = 826997) B826997
theorem B551347 : Blo 550806 551347 := bstep (se 1 (by rfl) ⟨413510, by rfl⟩ : syracuseStep 551347 = 827021) B827021
theorem B551363 : Blo 550806 551363 := bstep (se 1 (by rfl) ⟨413522, by rfl⟩ : syracuseStep 551363 = 827045) B827045
theorem B1403345 : Blo 550806 1403345 := bstep (se 2 (by rfl) ⟨526254, by rfl⟩ : syracuseStep 1403345 = 1052509) B1052509
theorem B551379 : Blo 550806 551379 := bstep (se 1 (by rfl) ⟨413534, by rfl⟩ : syracuseStep 551379 = 827069) B827069
theorem B551395 : Blo 550806 551395 := bstep (se 1 (by rfl) ⟨413546, by rfl⟩ : syracuseStep 551395 = 827093) B827093
theorem B551411 : Blo 550806 551411 := bstep (se 1 (by rfl) ⟨413558, by rfl⟩ : syracuseStep 551411 = 827117) B827117
theorem B551427 : Blo 550806 551427 := bstep (se 1 (by rfl) ⟨413570, by rfl⟩ : syracuseStep 551427 = 827141) B827141
theorem B1239569 : Blo 550806 1239569 := bstep (se 2 (by rfl) ⟨464838, by rfl⟩ : syracuseStep 1239569 = 929677) B929677
theorem B551443 : Blo 550806 551443 := bstep (se 1 (by rfl) ⟨413582, by rfl⟩ : syracuseStep 551443 = 827165) B827165
theorem B1239587 : Blo 550806 1239587 := bstep (se 1 (by rfl) ⟨929690, by rfl⟩ : syracuseStep 1239587 = 1859381) B1859381
theorem B551459 : Blo 550806 551459 := bstep (se 1 (by rfl) ⟨413594, by rfl⟩ : syracuseStep 551459 = 827189) B827189
theorem B1862189 : Blo 550806 1862189 := bstep (se 3 (by rfl) ⟨349160, by rfl⟩ : syracuseStep 1862189 = 698321) B698321
theorem B551475 : Blo 550806 551475 := bstep (se 1 (by rfl) ⟨413606, by rfl⟩ : syracuseStep 551475 = 827213) B827213
theorem B551491 : Blo 550806 551491 := bstep (se 1 (by rfl) ⟨413618, by rfl⟩ : syracuseStep 551491 = 827237) B827237
theorem B551507 : Blo 550806 551507 := bstep (se 1 (by rfl) ⟨413630, by rfl⟩ : syracuseStep 551507 = 827261) B827261
theorem B551523 : Blo 550806 551523 := bstep (se 1 (by rfl) ⟨413642, by rfl⟩ : syracuseStep 551523 = 827285) B827285
theorem B1862243 : Blo 550806 1862243 := bstep (se 1 (by rfl) ⟨1396682, by rfl⟩ : syracuseStep 1862243 = 2793365) B2793365
theorem B551539 : Blo 550806 551539 := bstep (se 1 (by rfl) ⟨413654, by rfl⟩ : syracuseStep 551539 = 827309) B827309
theorem B551555 : Blo 550806 551555 := bstep (se 1 (by rfl) ⟨413666, by rfl⟩ : syracuseStep 551555 = 827333) B827333
theorem B551571 : Blo 550806 551571 := bstep (se 1 (by rfl) ⟨413678, by rfl⟩ : syracuseStep 551571 = 827357) B827357
theorem B2091683 : Blo 550806 2091683 := bstep (se 1 (by rfl) ⟨1568762, by rfl⟩ : syracuseStep 2091683 = 3137525) B3137525
theorem B551587 : Blo 550806 551587 := bstep (se 1 (by rfl) ⟨413690, by rfl⟩ : syracuseStep 551587 = 827381) B827381
theorem B551603 : Blo 550806 551603 := bstep (se 1 (by rfl) ⟨413702, by rfl⟩ : syracuseStep 551603 = 827405) B827405
theorem B551619 : Blo 550806 551619 := bstep (se 1 (by rfl) ⟨413714, by rfl⟩ : syracuseStep 551619 = 827429) B827429
theorem B551635 : Blo 550806 551635 := bstep (se 1 (by rfl) ⟨413726, by rfl⟩ : syracuseStep 551635 = 827453) B827453
theorem B551651 : Blo 550806 551651 := bstep (se 1 (by rfl) ⟨413738, by rfl⟩ : syracuseStep 551651 = 827477) B827477
theorem B10775267 : Blo 550806 10775267 := bstep (se 1 (by rfl) ⟨8081450, by rfl⟩ : syracuseStep 10775267 = 16162901) B16162901
theorem B551667 : Blo 550806 551667 := bstep (se 1 (by rfl) ⟨413750, by rfl⟩ : syracuseStep 551667 = 827501) B827501
theorem B551683 : Blo 550806 551683 := bstep (se 1 (by rfl) ⟨413762, by rfl⟩ : syracuseStep 551683 = 827525) B827525
theorem B551699 : Blo 550806 551699 := bstep (se 1 (by rfl) ⟨413774, by rfl⟩ : syracuseStep 551699 = 827549) B827549
theorem B551715 : Blo 550806 551715 := bstep (se 1 (by rfl) ⟨413786, by rfl⟩ : syracuseStep 551715 = 827573) B827573
theorem B1239857 : Blo 550806 1239857 := bstep (se 2 (by rfl) ⟨464946, by rfl⟩ : syracuseStep 1239857 = 929893) B929893
theorem B551731 : Blo 550806 551731 := bstep (se 1 (by rfl) ⟨413798, by rfl⟩ : syracuseStep 551731 = 827597) B827597
theorem B1239875 : Blo 550806 1239875 := bstep (se 1 (by rfl) ⟨929906, by rfl⟩ : syracuseStep 1239875 = 1859813) B1859813
theorem B551747 : Blo 550806 551747 := bstep (se 1 (by rfl) ⟨413810, by rfl⟩ : syracuseStep 551747 = 827621) B827621
theorem B551763 : Blo 550806 551763 := bstep (se 1 (by rfl) ⟨413822, by rfl⟩ : syracuseStep 551763 = 827645) B827645
theorem B551779 : Blo 550806 551779 := bstep (se 1 (by rfl) ⟨413834, by rfl⟩ : syracuseStep 551779 = 827669) B827669
theorem B1862513 : Blo 550806 1862513 := bstep (se 2 (by rfl) ⟨698442, by rfl⟩ : syracuseStep 1862513 = 1396885) B1396885
theorem B551795 : Blo 550806 551795 := bstep (se 1 (by rfl) ⟨413846, by rfl⟩ : syracuseStep 551795 = 827693) B827693
theorem B551811 : Blo 550806 551811 := bstep (se 1 (by rfl) ⟨413858, by rfl⟩ : syracuseStep 551811 = 827717) B827717
theorem B551827 : Blo 550806 551827 := bstep (se 1 (by rfl) ⟨413870, by rfl⟩ : syracuseStep 551827 = 827741) B827741
theorem B551843 : Blo 550806 551843 := bstep (se 1 (by rfl) ⟨413882, by rfl⟩ : syracuseStep 551843 = 827765) B827765
theorem B551859 : Blo 550806 551859 := bstep (se 1 (by rfl) ⟨413894, by rfl⟩ : syracuseStep 551859 = 827789) B827789
theorem B551875 : Blo 550806 551875 := bstep (se 1 (by rfl) ⟨413906, by rfl⟩ : syracuseStep 551875 = 827813) B827813
theorem B551891 : Blo 550806 551891 := bstep (se 1 (by rfl) ⟨413918, by rfl⟩ : syracuseStep 551891 = 827837) B827837
theorem B551907 : Blo 550806 551907 := bstep (se 1 (by rfl) ⟨413930, by rfl⟩ : syracuseStep 551907 = 827861) B827861
theorem B551923 : Blo 550806 551923 := bstep (se 1 (by rfl) ⟨413942, by rfl⟩ : syracuseStep 551923 = 827885) B827885
theorem B551939 : Blo 550806 551939 := bstep (se 1 (by rfl) ⟨413954, by rfl⟩ : syracuseStep 551939 = 827909) B827909
theorem B551955 : Blo 550806 551955 := bstep (se 1 (by rfl) ⟨413966, by rfl⟩ : syracuseStep 551955 = 827933) B827933
theorem B551971 : Blo 550806 551971 := bstep (se 1 (by rfl) ⟨413978, by rfl⟩ : syracuseStep 551971 = 827957) B827957
theorem B551987 : Blo 550806 551987 := bstep (se 1 (by rfl) ⟨413990, by rfl⟩ : syracuseStep 551987 = 827981) B827981
theorem B552003 : Blo 550806 552003 := bstep (se 1 (by rfl) ⟨414002, by rfl⟩ : syracuseStep 552003 = 828005) B828005
theorem B1240145 : Blo 550806 1240145 := bstep (se 2 (by rfl) ⟨465054, by rfl⟩ : syracuseStep 1240145 = 930109) B930109
theorem B552019 : Blo 550806 552019 := bstep (se 1 (by rfl) ⟨414014, by rfl⟩ : syracuseStep 552019 = 828029) B828029
theorem B1240163 : Blo 550806 1240163 := bstep (se 1 (by rfl) ⟨930122, by rfl⟩ : syracuseStep 1240163 = 1860245) B1860245
theorem B552035 : Blo 550806 552035 := bstep (se 1 (by rfl) ⟨414026, by rfl⟩ : syracuseStep 552035 = 828053) B828053
theorem B552051 : Blo 550806 552051 := bstep (se 1 (by rfl) ⟨414038, by rfl⟩ : syracuseStep 552051 = 828077) B828077
theorem B552067 : Blo 550806 552067 := bstep (se 1 (by rfl) ⟨414050, by rfl⟩ : syracuseStep 552067 = 828101) B828101
theorem B552083 : Blo 550806 552083 := bstep (se 1 (by rfl) ⟨414062, by rfl⟩ : syracuseStep 552083 = 828125) B828125
theorem B552099 : Blo 550806 552099 := bstep (se 1 (by rfl) ⟨414074, by rfl⟩ : syracuseStep 552099 = 828149) B828149
theorem B552115 : Blo 550806 552115 := bstep (se 1 (by rfl) ⟨414086, by rfl⟩ : syracuseStep 552115 = 828173) B828173
theorem B552131 : Blo 550806 552131 := bstep (se 1 (by rfl) ⟨414098, by rfl⟩ : syracuseStep 552131 = 828197) B828197
theorem B552147 : Blo 550806 552147 := bstep (se 1 (by rfl) ⟨414110, by rfl⟩ : syracuseStep 552147 = 828221) B828221
theorem B552163 : Blo 550806 552163 := bstep (se 1 (by rfl) ⟨414122, by rfl⟩ : syracuseStep 552163 = 828245) B828245
theorem B552179 : Blo 550806 552179 := bstep (se 1 (by rfl) ⟨414134, by rfl⟩ : syracuseStep 552179 = 828269) B828269
theorem B552195 : Blo 550806 552195 := bstep (se 1 (by rfl) ⟨414146, by rfl⟩ : syracuseStep 552195 = 828293) B828293
theorem B552211 : Blo 550806 552211 := bstep (se 1 (by rfl) ⟨414158, by rfl⟩ : syracuseStep 552211 = 828317) B828317
theorem B552227 : Blo 550806 552227 := bstep (se 1 (by rfl) ⟨414170, by rfl⟩ : syracuseStep 552227 = 828341) B828341
theorem B2092337 : Blo 550806 2092337 := bstep (se 2 (by rfl) ⟨784626, by rfl⟩ : syracuseStep 2092337 = 1569253) B1569253
theorem B552243 : Blo 550806 552243 := bstep (se 1 (by rfl) ⟨414182, by rfl⟩ : syracuseStep 552243 = 828365) B828365
theorem B552259 : Blo 550806 552259 := bstep (se 1 (by rfl) ⟨414194, by rfl⟩ : syracuseStep 552259 = 828389) B828389
theorem B552275 : Blo 550806 552275 := bstep (se 1 (by rfl) ⟨414206, by rfl⟩ : syracuseStep 552275 = 828413) B828413
theorem B552291 : Blo 550806 552291 := bstep (se 1 (by rfl) ⟨414218, by rfl⟩ : syracuseStep 552291 = 828437) B828437
theorem B1240433 : Blo 550806 1240433 := bstep (se 2 (by rfl) ⟨465162, by rfl⟩ : syracuseStep 1240433 = 930325) B930325
theorem B552307 : Blo 550806 552307 := bstep (se 1 (by rfl) ⟨414230, by rfl⟩ : syracuseStep 552307 = 828461) B828461
theorem B1240451 : Blo 550806 1240451 := bstep (se 1 (by rfl) ⟨930338, by rfl⟩ : syracuseStep 1240451 = 1860677) B1860677
theorem B552323 : Blo 550806 552323 := bstep (se 1 (by rfl) ⟨414242, by rfl⟩ : syracuseStep 552323 = 828485) B828485
theorem B1863053 : Blo 550806 1863053 := bstep (se 3 (by rfl) ⟨349322, by rfl⟩ : syracuseStep 1863053 = 698645) B698645
theorem B552339 : Blo 550806 552339 := bstep (se 1 (by rfl) ⟨414254, by rfl⟩ : syracuseStep 552339 = 828509) B828509
theorem B552355 : Blo 550806 552355 := bstep (se 1 (by rfl) ⟨414266, by rfl⟩ : syracuseStep 552355 = 828533) B828533
theorem B1404337 : Blo 550806 1404337 := bstep (se 2 (by rfl) ⟨526626, by rfl⟩ : syracuseStep 1404337 = 1053253) B1053253
theorem B552371 : Blo 550806 552371 := bstep (se 1 (by rfl) ⟨414278, by rfl⟩ : syracuseStep 552371 = 828557) B828557
theorem B1863107 : Blo 550806 1863107 := bstep (se 1 (by rfl) ⟨1397330, by rfl⟩ : syracuseStep 1863107 = 2794661) B2794661
theorem B552387 : Blo 550806 552387 := bstep (se 1 (by rfl) ⟨414290, by rfl⟩ : syracuseStep 552387 = 828581) B828581
theorem B552403 : Blo 550806 552403 := bstep (se 1 (by rfl) ⟨414302, by rfl⟩ : syracuseStep 552403 = 828605) B828605
theorem B552419 : Blo 550806 552419 := bstep (se 1 (by rfl) ⟨414314, by rfl⟩ : syracuseStep 552419 = 828629) B828629
theorem B749027 : Blo 550806 749027 := bstep (se 1 (by rfl) ⟨561770, by rfl⟩ : syracuseStep 749027 = 1123541) B1123541
theorem B552435 : Blo 550806 552435 := bstep (se 1 (by rfl) ⟨414326, by rfl⟩ : syracuseStep 552435 = 828653) B828653
theorem B552451 : Blo 550806 552451 := bstep (se 1 (by rfl) ⟨414338, by rfl⟩ : syracuseStep 552451 = 828677) B828677
theorem B3141125 : Blo 550806 3141125 := bstep (se 4 (by rfl) ⟨294480, by rfl⟩ : syracuseStep 3141125 = 588961) B588961
theorem B552467 : Blo 550806 552467 := bstep (se 1 (by rfl) ⟨414350, by rfl⟩ : syracuseStep 552467 = 828701) B828701
theorem B1764899 : Blo 550806 1764899 := bstep (se 1 (by rfl) ⟨1323674, by rfl⟩ : syracuseStep 1764899 = 2647349) B2647349
theorem B552483 : Blo 550806 552483 := bstep (se 1 (by rfl) ⟨414362, by rfl⟩ : syracuseStep 552483 = 828725) B828725
theorem B552499 : Blo 550806 552499 := bstep (se 1 (by rfl) ⟨414374, by rfl⟩ : syracuseStep 552499 = 828749) B828749
theorem B552515 : Blo 550806 552515 := bstep (se 1 (by rfl) ⟨414386, by rfl⟩ : syracuseStep 552515 = 828773) B828773
theorem B552531 : Blo 550806 552531 := bstep (se 1 (by rfl) ⟨414398, by rfl⟩ : syracuseStep 552531 = 828797) B828797
theorem B552547 : Blo 550806 552547 := bstep (se 1 (by rfl) ⟨414410, by rfl⟩ : syracuseStep 552547 = 828821) B828821
theorem B552563 : Blo 550806 552563 := bstep (se 1 (by rfl) ⟨414422, by rfl⟩ : syracuseStep 552563 = 828845) B828845
theorem B552579 : Blo 550806 552579 := bstep (se 1 (by rfl) ⟨414434, by rfl⟩ : syracuseStep 552579 = 828869) B828869
theorem B1240721 : Blo 550806 1240721 := bstep (se 2 (by rfl) ⟨465270, by rfl⟩ : syracuseStep 1240721 = 930541) B930541
theorem B552595 : Blo 550806 552595 := bstep (se 1 (by rfl) ⟨414446, by rfl⟩ : syracuseStep 552595 = 828893) B828893
theorem B1240739 : Blo 550806 1240739 := bstep (se 1 (by rfl) ⟨930554, by rfl⟩ : syracuseStep 1240739 = 1861109) B1861109
theorem B552611 : Blo 550806 552611 := bstep (se 1 (by rfl) ⟨414458, by rfl⟩ : syracuseStep 552611 = 828917) B828917
theorem B552627 : Blo 550806 552627 := bstep (se 1 (by rfl) ⟨414470, by rfl⟩ : syracuseStep 552627 = 828941) B828941
theorem B552643 : Blo 550806 552643 := bstep (se 1 (by rfl) ⟨414482, by rfl⟩ : syracuseStep 552643 = 828965) B828965
theorem B1863377 : Blo 550806 1863377 := bstep (se 2 (by rfl) ⟨698766, by rfl⟩ : syracuseStep 1863377 = 1397533) B1397533
theorem B552659 : Blo 550806 552659 := bstep (se 1 (by rfl) ⟨414494, by rfl⟩ : syracuseStep 552659 = 828989) B828989
theorem B552675 : Blo 550806 552675 := bstep (se 1 (by rfl) ⟨414506, by rfl⟩ : syracuseStep 552675 = 829013) B829013
theorem B552691 : Blo 550806 552691 := bstep (se 1 (by rfl) ⟨414518, by rfl⟩ : syracuseStep 552691 = 829037) B829037
theorem B552707 : Blo 550806 552707 := bstep (se 1 (by rfl) ⟨414530, by rfl⟩ : syracuseStep 552707 = 829061) B829061
theorem B1601297 : Blo 550806 1601297 := bstep (se 2 (by rfl) ⟨600486, by rfl⟩ : syracuseStep 1601297 = 1200973) B1200973
theorem B552723 : Blo 550806 552723 := bstep (se 1 (by rfl) ⟨414542, by rfl⟩ : syracuseStep 552723 = 829085) B829085
theorem B552739 : Blo 550806 552739 := bstep (se 1 (by rfl) ⟨414554, by rfl⟩ : syracuseStep 552739 = 829109) B829109
theorem B552755 : Blo 550806 552755 := bstep (se 1 (by rfl) ⟨414566, by rfl⟩ : syracuseStep 552755 = 829133) B829133
theorem B552771 : Blo 550806 552771 := bstep (se 1 (by rfl) ⟨414578, by rfl⟩ : syracuseStep 552771 = 829157) B829157
theorem B552787 : Blo 550806 552787 := bstep (se 1 (by rfl) ⟨414590, by rfl⟩ : syracuseStep 552787 = 829181) B829181
theorem B552803 : Blo 550806 552803 := bstep (se 1 (by rfl) ⟨414602, by rfl⟩ : syracuseStep 552803 = 829205) B829205
theorem B2518897 : Blo 550806 2518897 := bstep (se 2 (by rfl) ⟨944586, by rfl⟩ : syracuseStep 2518897 = 1889173) B1889173
theorem B552819 : Blo 550806 552819 := bstep (se 1 (by rfl) ⟨414614, by rfl⟩ : syracuseStep 552819 = 829229) B829229
theorem B552835 : Blo 550806 552835 := bstep (se 1 (by rfl) ⟨414626, by rfl⟩ : syracuseStep 552835 = 829253) B829253
theorem B552851 : Blo 550806 552851 := bstep (se 1 (by rfl) ⟨414638, by rfl⟩ : syracuseStep 552851 = 829277) B829277
theorem B749459 : Blo 550806 749459 := bstep (se 1 (by rfl) ⟨562094, by rfl⟩ : syracuseStep 749459 = 1124189) B1124189
theorem B552867 : Blo 550806 552867 := bstep (se 1 (by rfl) ⟨414650, by rfl⟩ : syracuseStep 552867 = 829301) B829301
theorem B1241009 : Blo 550806 1241009 := bstep (se 2 (by rfl) ⟨465378, by rfl⟩ : syracuseStep 1241009 = 930757) B930757
theorem B552883 : Blo 550806 552883 := bstep (se 1 (by rfl) ⟨414662, by rfl⟩ : syracuseStep 552883 = 829325) B829325
theorem B1241027 : Blo 550806 1241027 := bstep (se 1 (by rfl) ⟨930770, by rfl⟩ : syracuseStep 1241027 = 1861541) B1861541
theorem B552899 : Blo 550806 552899 := bstep (se 1 (by rfl) ⟨414674, by rfl⟩ : syracuseStep 552899 = 829349) B829349
theorem B1568717 : Blo 550806 1568717 := bstep (se 3 (by rfl) ⟨294134, by rfl⟩ : syracuseStep 1568717 = 588269) B588269
theorem B552915 : Blo 550806 552915 := bstep (se 1 (by rfl) ⟨414686, by rfl⟩ : syracuseStep 552915 = 829373) B829373
theorem B552931 : Blo 550806 552931 := bstep (se 1 (by rfl) ⟨414698, by rfl⟩ : syracuseStep 552931 = 829397) B829397
theorem B552947 : Blo 550806 552947 := bstep (se 1 (by rfl) ⟨414710, by rfl⟩ : syracuseStep 552947 = 829421) B829421
theorem B552963 : Blo 550806 552963 := bstep (se 1 (by rfl) ⟨414722, by rfl⟩ : syracuseStep 552963 = 829445) B829445
theorem B552979 : Blo 550806 552979 := bstep (se 1 (by rfl) ⟨414734, by rfl⟩ : syracuseStep 552979 = 829469) B829469
theorem B552995 : Blo 550806 552995 := bstep (se 1 (by rfl) ⟨414746, by rfl⟩ : syracuseStep 552995 = 829493) B829493
theorem B553011 : Blo 550806 553011 := bstep (se 1 (by rfl) ⟨414758, by rfl⟩ : syracuseStep 553011 = 829517) B829517
theorem B553027 : Blo 550806 553027 := bstep (se 1 (by rfl) ⟨414770, by rfl⟩ : syracuseStep 553027 = 829541) B829541
theorem B553043 : Blo 550806 553043 := bstep (se 1 (by rfl) ⟨414782, by rfl⟩ : syracuseStep 553043 = 829565) B829565
theorem B553059 : Blo 550806 553059 := bstep (se 1 (by rfl) ⟨414794, by rfl⟩ : syracuseStep 553059 = 829589) B829589
theorem B553075 : Blo 550806 553075 := bstep (se 1 (by rfl) ⟨414806, by rfl⟩ : syracuseStep 553075 = 829613) B829613
theorem B1568899 : Blo 550806 1568899 := bstep (se 1 (by rfl) ⟨1176674, by rfl⟩ : syracuseStep 1568899 = 2353349) B2353349
theorem B553091 : Blo 550806 553091 := bstep (se 1 (by rfl) ⟨414818, by rfl⟩ : syracuseStep 553091 = 829637) B829637
theorem B553107 : Blo 550806 553107 := bstep (se 1 (by rfl) ⟨414830, by rfl⟩ : syracuseStep 553107 = 829661) B829661
theorem B553123 : Blo 550806 553123 := bstep (se 1 (by rfl) ⟨414842, by rfl⟩ : syracuseStep 553123 = 829685) B829685
theorem B1568945 : Blo 550806 1568945 := bstep (se 2 (by rfl) ⟨588354, by rfl⟩ : syracuseStep 1568945 = 1176709) B1176709
theorem B2846897 : Blo 550806 2846897 := bstep (se 2 (by rfl) ⟨1067586, by rfl⟩ : syracuseStep 2846897 = 2135173) B2135173
theorem B553139 : Blo 550806 553139 := bstep (se 1 (by rfl) ⟨414854, by rfl⟩ : syracuseStep 553139 = 829709) B829709
theorem B553155 : Blo 550806 553155 := bstep (se 1 (by rfl) ⟨414866, by rfl⟩ : syracuseStep 553155 = 829733) B829733
theorem B1241297 : Blo 550806 1241297 := bstep (se 2 (by rfl) ⟨465486, by rfl⟩ : syracuseStep 1241297 = 930973) B930973
theorem B553171 : Blo 550806 553171 := bstep (se 1 (by rfl) ⟨414878, by rfl⟩ : syracuseStep 553171 = 829757) B829757
theorem B1241315 : Blo 550806 1241315 := bstep (se 1 (by rfl) ⟨930986, by rfl⟩ : syracuseStep 1241315 = 1861973) B1861973
theorem B553187 : Blo 550806 553187 := bstep (se 1 (by rfl) ⟨414890, by rfl⟩ : syracuseStep 553187 = 829781) B829781
theorem B1863917 : Blo 550806 1863917 := bstep (se 3 (by rfl) ⟨349484, by rfl⟩ : syracuseStep 1863917 = 698969) B698969
theorem B553203 : Blo 550806 553203 := bstep (se 1 (by rfl) ⟨414902, by rfl⟩ : syracuseStep 553203 = 829805) B829805
theorem B553219 : Blo 550806 553219 := bstep (se 1 (by rfl) ⟨414914, by rfl⟩ : syracuseStep 553219 = 829829) B829829
theorem B553235 : Blo 550806 553235 := bstep (se 1 (by rfl) ⟨414926, by rfl⟩ : syracuseStep 553235 = 829853) B829853
theorem B1863971 : Blo 550806 1863971 := bstep (se 1 (by rfl) ⟨1397978, by rfl⟩ : syracuseStep 1863971 = 2795957) B2795957
theorem B553251 : Blo 550806 553251 := bstep (se 1 (by rfl) ⟨414938, by rfl⟩ : syracuseStep 553251 = 829877) B829877
theorem B553267 : Blo 550806 553267 := bstep (se 1 (by rfl) ⟨414950, by rfl⟩ : syracuseStep 553267 = 829901) B829901
theorem B553283 : Blo 550806 553283 := bstep (se 1 (by rfl) ⟨414962, by rfl⟩ : syracuseStep 553283 = 829925) B829925
theorem B553299 : Blo 550806 553299 := bstep (se 1 (by rfl) ⟨414974, by rfl⟩ : syracuseStep 553299 = 829949) B829949
theorem B553315 : Blo 550806 553315 := bstep (se 1 (by rfl) ⟨414986, by rfl⟩ : syracuseStep 553315 = 829973) B829973
theorem B553331 : Blo 550806 553331 := bstep (se 1 (by rfl) ⟨414998, by rfl⟩ : syracuseStep 553331 = 829997) B829997
theorem B553347 : Blo 550806 553347 := bstep (se 1 (by rfl) ⟨415010, by rfl⟩ : syracuseStep 553347 = 830021) B830021
theorem B553363 : Blo 550806 553363 := bstep (se 1 (by rfl) ⟨415022, by rfl⟩ : syracuseStep 553363 = 830045) B830045
theorem B553379 : Blo 550806 553379 := bstep (se 1 (by rfl) ⟨415034, by rfl⟩ : syracuseStep 553379 = 830069) B830069
theorem B553395 : Blo 550806 553395 := bstep (se 1 (by rfl) ⟨415046, by rfl⟩ : syracuseStep 553395 = 830093) B830093
theorem B553411 : Blo 550806 553411 := bstep (se 1 (by rfl) ⟨415058, by rfl⟩ : syracuseStep 553411 = 830117) B830117
theorem B553427 : Blo 550806 553427 := bstep (se 1 (by rfl) ⟨415070, by rfl⟩ : syracuseStep 553427 = 830141) B830141
theorem B553443 : Blo 550806 553443 := bstep (se 1 (by rfl) ⟨415082, by rfl⟩ : syracuseStep 553443 = 830165) B830165
theorem B1241585 : Blo 550806 1241585 := bstep (se 2 (by rfl) ⟨465594, by rfl⟩ : syracuseStep 1241585 = 931189) B931189
theorem B553459 : Blo 550806 553459 := bstep (se 1 (by rfl) ⟨415094, by rfl⟩ : syracuseStep 553459 = 830189) B830189
theorem B1241603 : Blo 550806 1241603 := bstep (se 1 (by rfl) ⟨931202, by rfl⟩ : syracuseStep 1241603 = 1862405) B1862405
theorem B553475 : Blo 550806 553475 := bstep (se 1 (by rfl) ⟨415106, by rfl⟩ : syracuseStep 553475 = 830213) B830213
theorem B553491 : Blo 550806 553491 := bstep (se 1 (by rfl) ⟨415118, by rfl⟩ : syracuseStep 553491 = 830237) B830237
theorem B553507 : Blo 550806 553507 := bstep (se 1 (by rfl) ⟨415130, by rfl⟩ : syracuseStep 553507 = 830261) B830261
theorem B1864241 : Blo 550806 1864241 := bstep (se 2 (by rfl) ⟨699090, by rfl⟩ : syracuseStep 1864241 = 1398181) B1398181
theorem B553523 : Blo 550806 553523 := bstep (se 1 (by rfl) ⟨415142, by rfl⟩ : syracuseStep 553523 = 830285) B830285
theorem B553539 : Blo 550806 553539 := bstep (se 1 (by rfl) ⟨415154, by rfl⟩ : syracuseStep 553539 = 830309) B830309
theorem B553555 : Blo 550806 553555 := bstep (se 1 (by rfl) ⟨415166, by rfl⟩ : syracuseStep 553555 = 830333) B830333
theorem B553571 : Blo 550806 553571 := bstep (se 1 (by rfl) ⟨415178, by rfl⟩ : syracuseStep 553571 = 830357) B830357
theorem B553587 : Blo 550806 553587 := bstep (se 1 (by rfl) ⟨415190, by rfl⟩ : syracuseStep 553587 = 830381) B830381
theorem B553603 : Blo 550806 553603 := bstep (se 1 (by rfl) ⟨415202, by rfl⟩ : syracuseStep 553603 = 830405) B830405
theorem B553619 : Blo 550806 553619 := bstep (se 1 (by rfl) ⟨415214, by rfl⟩ : syracuseStep 553619 = 830429) B830429
theorem B553635 : Blo 550806 553635 := bstep (se 1 (by rfl) ⟨415226, by rfl⟩ : syracuseStep 553635 = 830453) B830453
theorem B1012387 : Blo 550806 1012387 := bstep (se 1 (by rfl) ⟨759290, by rfl⟩ : syracuseStep 1012387 = 1518581) B1518581
theorem B553651 : Blo 550806 553651 := bstep (se 1 (by rfl) ⟨415238, by rfl⟩ : syracuseStep 553651 = 830477) B830477
theorem B553667 : Blo 550806 553667 := bstep (se 1 (by rfl) ⟨415250, by rfl⟩ : syracuseStep 553667 = 830501) B830501
theorem B553683 : Blo 550806 553683 := bstep (se 1 (by rfl) ⟨415262, by rfl⟩ : syracuseStep 553683 = 830525) B830525
theorem B2093795 : Blo 550806 2093795 := bstep (se 1 (by rfl) ⟨1570346, by rfl⟩ : syracuseStep 2093795 = 3140693) B3140693
theorem B553699 : Blo 550806 553699 := bstep (se 1 (by rfl) ⟨415274, by rfl⟩ : syracuseStep 553699 = 830549) B830549
theorem B2093809 : Blo 550806 2093809 := bstep (se 2 (by rfl) ⟨785178, by rfl⟩ : syracuseStep 2093809 = 1570357) B1570357
theorem B553715 : Blo 550806 553715 := bstep (se 1 (by rfl) ⟨415286, by rfl⟩ : syracuseStep 553715 = 830573) B830573
theorem B553731 : Blo 550806 553731 := bstep (se 1 (by rfl) ⟨415298, by rfl⟩ : syracuseStep 553731 = 830597) B830597
theorem B1241873 : Blo 550806 1241873 := bstep (se 2 (by rfl) ⟨465702, by rfl⟩ : syracuseStep 1241873 = 931405) B931405
theorem B553747 : Blo 550806 553747 := bstep (se 1 (by rfl) ⟨415310, by rfl⟩ : syracuseStep 553747 = 830621) B830621
theorem B1241891 : Blo 550806 1241891 := bstep (se 1 (by rfl) ⟨931418, by rfl⟩ : syracuseStep 1241891 = 1862837) B1862837
theorem B553763 : Blo 550806 553763 := bstep (se 1 (by rfl) ⟨415322, by rfl⟩ : syracuseStep 553763 = 830645) B830645
theorem B553779 : Blo 550806 553779 := bstep (se 1 (by rfl) ⟨415334, by rfl⟩ : syracuseStep 553779 = 830669) B830669
theorem B553795 : Blo 550806 553795 := bstep (se 1 (by rfl) ⟨415346, by rfl⟩ : syracuseStep 553795 = 830693) B830693
theorem B1176401 : Blo 550806 1176401 := bstep (se 2 (by rfl) ⟨441150, by rfl⟩ : syracuseStep 1176401 = 882301) B882301
theorem B553811 : Blo 550806 553811 := bstep (se 1 (by rfl) ⟨415358, by rfl⟩ : syracuseStep 553811 = 830717) B830717
theorem B1176419 : Blo 550806 1176419 := bstep (se 1 (by rfl) ⟨882314, by rfl⟩ : syracuseStep 1176419 = 1764629) B1764629
theorem B2356067 : Blo 550806 2356067 := bstep (se 1 (by rfl) ⟨1767050, by rfl⟩ : syracuseStep 2356067 = 3534101) B3534101
theorem B553827 : Blo 550806 553827 := bstep (se 1 (by rfl) ⟨415370, by rfl⟩ : syracuseStep 553827 = 830741) B830741
theorem B553843 : Blo 550806 553843 := bstep (se 1 (by rfl) ⟨415382, by rfl⟩ : syracuseStep 553843 = 830765) B830765
theorem B553859 : Blo 550806 553859 := bstep (se 1 (by rfl) ⟨415394, by rfl⟩ : syracuseStep 553859 = 830789) B830789
theorem B553875 : Blo 550806 553875 := bstep (se 1 (by rfl) ⟨415406, by rfl⟩ : syracuseStep 553875 = 830813) B830813
theorem B553891 : Blo 550806 553891 := bstep (se 1 (by rfl) ⟨415418, by rfl⟩ : syracuseStep 553891 = 830837) B830837
theorem B553907 : Blo 550806 553907 := bstep (se 1 (by rfl) ⟨415430, by rfl⟩ : syracuseStep 553907 = 830861) B830861
theorem B553923 : Blo 550806 553923 := bstep (se 1 (by rfl) ⟨415442, by rfl⟩ : syracuseStep 553923 = 830885) B830885
theorem B553939 : Blo 550806 553939 := bstep (se 1 (by rfl) ⟨415454, by rfl⟩ : syracuseStep 553939 = 830909) B830909
theorem B553955 : Blo 550806 553955 := bstep (se 1 (by rfl) ⟨415466, by rfl⟩ : syracuseStep 553955 = 830933) B830933
theorem B553971 : Blo 550806 553971 := bstep (se 1 (by rfl) ⟨415478, by rfl⟩ : syracuseStep 553971 = 830957) B830957
theorem B553987 : Blo 550806 553987 := bstep (se 1 (by rfl) ⟨415490, by rfl⟩ : syracuseStep 553987 = 830981) B830981
theorem B554003 : Blo 550806 554003 := bstep (se 1 (by rfl) ⟨415502, by rfl⟩ : syracuseStep 554003 = 831005) B831005
theorem B554019 : Blo 550806 554019 := bstep (se 1 (by rfl) ⟨415514, by rfl⟩ : syracuseStep 554019 = 831029) B831029
theorem B1242161 : Blo 550806 1242161 := bstep (se 2 (by rfl) ⟨465810, by rfl⟩ : syracuseStep 1242161 = 931621) B931621
theorem B554035 : Blo 550806 554035 := bstep (se 1 (by rfl) ⟨415526, by rfl⟩ : syracuseStep 554035 = 831053) B831053
theorem B1242179 : Blo 550806 1242179 := bstep (se 1 (by rfl) ⟨931634, by rfl⟩ : syracuseStep 1242179 = 1863269) B1863269
theorem B554051 : Blo 550806 554051 := bstep (se 1 (by rfl) ⟨415538, by rfl⟩ : syracuseStep 554051 = 831077) B831077
theorem B1864781 : Blo 550806 1864781 := bstep (se 3 (by rfl) ⟨349646, by rfl⟩ : syracuseStep 1864781 = 699293) B699293
theorem B554067 : Blo 550806 554067 := bstep (se 1 (by rfl) ⟨415550, by rfl⟩ : syracuseStep 554067 = 831101) B831101
theorem B554083 : Blo 550806 554083 := bstep (se 1 (by rfl) ⟨415562, by rfl⟩ : syracuseStep 554083 = 831125) B831125
theorem B554099 : Blo 550806 554099 := bstep (se 1 (by rfl) ⟨415574, by rfl⟩ : syracuseStep 554099 = 831149) B831149
theorem B1864835 : Blo 550806 1864835 := bstep (se 1 (by rfl) ⟨1398626, by rfl⟩ : syracuseStep 1864835 = 2797253) B2797253
theorem B554115 : Blo 550806 554115 := bstep (se 1 (by rfl) ⟨415586, by rfl⟩ : syracuseStep 554115 = 831173) B831173
theorem B1537165 : Blo 550806 1537165 := bstep (se 3 (by rfl) ⟨288218, by rfl⟩ : syracuseStep 1537165 = 576437) B576437
theorem B554131 : Blo 550806 554131 := bstep (se 1 (by rfl) ⟨415598, by rfl⟩ : syracuseStep 554131 = 831197) B831197
theorem B554147 : Blo 550806 554147 := bstep (se 1 (by rfl) ⟨415610, by rfl⟩ : syracuseStep 554147 = 831221) B831221
theorem B619699 : Blo 550806 619699 := bstep (se 1 (by rfl) ⟨464774, by rfl⟩ : syracuseStep 619699 = 929549) B929549
theorem B554163 : Blo 550806 554163 := bstep (se 1 (by rfl) ⟨415622, by rfl⟩ : syracuseStep 554163 = 831245) B831245
theorem B554179 : Blo 550806 554179 := bstep (se 1 (by rfl) ⟨415634, by rfl⟩ : syracuseStep 554179 = 831269) B831269
theorem B554195 : Blo 550806 554195 := bstep (se 1 (by rfl) ⟨415646, by rfl⟩ : syracuseStep 554195 = 831293) B831293
theorem B2651363 : Blo 550806 2651363 := bstep (se 1 (by rfl) ⟨1988522, by rfl⟩ : syracuseStep 2651363 = 3977045) B3977045
theorem B5305571 : Blo 550806 5305571 := bstep (se 1 (by rfl) ⟨3979178, by rfl⟩ : syracuseStep 5305571 = 7958357) B7958357
theorem B554211 : Blo 550806 554211 := bstep (se 1 (by rfl) ⟨415658, by rfl⟩ : syracuseStep 554211 = 831317) B831317
theorem B3994865 : Blo 550806 3994865 := bstep (se 2 (by rfl) ⟨1498074, by rfl⟩ : syracuseStep 3994865 = 2996149) B2996149
theorem B554227 : Blo 550806 554227 := bstep (se 1 (by rfl) ⟨415670, by rfl⟩ : syracuseStep 554227 = 831341) B831341
theorem B554243 : Blo 550806 554243 := bstep (se 1 (by rfl) ⟨415682, by rfl⟩ : syracuseStep 554243 = 831365) B831365
theorem B554259 : Blo 550806 554259 := bstep (se 1 (by rfl) ⟨415694, by rfl⟩ : syracuseStep 554259 = 831389) B831389
theorem B554275 : Blo 550806 554275 := bstep (se 1 (by rfl) ⟨415706, by rfl⟩ : syracuseStep 554275 = 831413) B831413
theorem B554291 : Blo 550806 554291 := bstep (se 1 (by rfl) ⟨415718, by rfl⟩ : syracuseStep 554291 = 831437) B831437
theorem B619843 : Blo 550806 619843 := bstep (se 1 (by rfl) ⟨464882, by rfl⟩ : syracuseStep 619843 = 929765) B929765
theorem B554307 : Blo 550806 554307 := bstep (se 1 (by rfl) ⟨415730, by rfl⟩ : syracuseStep 554307 = 831461) B831461
theorem B1242449 : Blo 550806 1242449 := bstep (se 2 (by rfl) ⟨465918, by rfl⟩ : syracuseStep 1242449 = 931837) B931837
theorem B554323 : Blo 550806 554323 := bstep (se 1 (by rfl) ⟨415742, by rfl⟩ : syracuseStep 554323 = 831485) B831485
theorem B1242467 : Blo 550806 1242467 := bstep (se 1 (by rfl) ⟨931850, by rfl⟩ : syracuseStep 1242467 = 1863701) B1863701
theorem B554339 : Blo 550806 554339 := bstep (se 1 (by rfl) ⟨415754, by rfl⟩ : syracuseStep 554339 = 831509) B831509
theorem B554355 : Blo 550806 554355 := bstep (se 1 (by rfl) ⟨415766, by rfl⟩ : syracuseStep 554355 = 831533) B831533
theorem B554371 : Blo 550806 554371 := bstep (se 1 (by rfl) ⟨415778, by rfl⟩ : syracuseStep 554371 = 831557) B831557
theorem B1865105 : Blo 550806 1865105 := bstep (se 2 (by rfl) ⟨699414, by rfl⟩ : syracuseStep 1865105 = 1398829) B1398829
theorem B947603 : Blo 550806 947603 := bstep (se 1 (by rfl) ⟨710702, by rfl⟩ : syracuseStep 947603 = 1421405) B1421405
theorem B554387 : Blo 550806 554387 := bstep (se 1 (by rfl) ⟨415790, by rfl⟩ : syracuseStep 554387 = 831581) B831581
theorem B2651555 : Blo 550806 2651555 := bstep (se 1 (by rfl) ⟨1988666, by rfl⟩ : syracuseStep 2651555 = 3977333) B3977333
theorem B554403 : Blo 550806 554403 := bstep (se 1 (by rfl) ⟨415802, by rfl⟩ : syracuseStep 554403 = 831605) B831605
theorem B554419 : Blo 550806 554419 := bstep (se 1 (by rfl) ⟨415814, by rfl⟩ : syracuseStep 554419 = 831629) B831629
theorem B554435 : Blo 550806 554435 := bstep (se 1 (by rfl) ⟨415826, by rfl⟩ : syracuseStep 554435 = 831653) B831653
theorem B619987 : Blo 550806 619987 := bstep (se 1 (by rfl) ⟨464990, by rfl⟩ : syracuseStep 619987 = 929981) B929981
theorem B554451 : Blo 550806 554451 := bstep (se 1 (by rfl) ⟨415838, by rfl⟩ : syracuseStep 554451 = 831677) B831677
theorem B554467 : Blo 550806 554467 := bstep (se 1 (by rfl) ⟨415850, by rfl⟩ : syracuseStep 554467 = 831701) B831701
theorem B554483 : Blo 550806 554483 := bstep (se 1 (by rfl) ⟨415862, by rfl⟩ : syracuseStep 554483 = 831725) B831725
theorem B554499 : Blo 550806 554499 := bstep (se 1 (by rfl) ⟨415874, by rfl⟩ : syracuseStep 554499 = 831749) B831749
theorem B554515 : Blo 550806 554515 := bstep (se 1 (by rfl) ⟨415886, by rfl⟩ : syracuseStep 554515 = 831773) B831773
theorem B554531 : Blo 550806 554531 := bstep (se 1 (by rfl) ⟨415898, by rfl⟩ : syracuseStep 554531 = 831797) B831797
theorem B554547 : Blo 550806 554547 := bstep (se 1 (by rfl) ⟨415910, by rfl⟩ : syracuseStep 554547 = 831821) B831821
theorem B554563 : Blo 550806 554563 := bstep (se 1 (by rfl) ⟨415922, by rfl⟩ : syracuseStep 554563 = 831845) B831845
theorem B554579 : Blo 550806 554579 := bstep (se 1 (by rfl) ⟨415934, by rfl⟩ : syracuseStep 554579 = 831869) B831869
theorem B620131 : Blo 550806 620131 := bstep (se 1 (by rfl) ⟨465098, by rfl⟩ : syracuseStep 620131 = 930197) B930197
theorem B1570403 : Blo 550806 1570403 := bstep (se 1 (by rfl) ⟨1177802, by rfl⟩ : syracuseStep 1570403 = 2355605) B2355605
theorem B554595 : Blo 550806 554595 := bstep (se 1 (by rfl) ⟨415946, by rfl⟩ : syracuseStep 554595 = 831893) B831893
theorem B1242737 : Blo 550806 1242737 := bstep (se 2 (by rfl) ⟨466026, by rfl⟩ : syracuseStep 1242737 = 932053) B932053
theorem B554611 : Blo 550806 554611 := bstep (se 1 (by rfl) ⟨415958, by rfl⟩ : syracuseStep 554611 = 831917) B831917
theorem B1242755 : Blo 550806 1242755 := bstep (se 1 (by rfl) ⟨932066, by rfl⟩ : syracuseStep 1242755 = 1864133) B1864133
theorem B554627 : Blo 550806 554627 := bstep (se 1 (by rfl) ⟨415970, by rfl⟩ : syracuseStep 554627 = 831941) B831941
theorem B554643 : Blo 550806 554643 := bstep (se 1 (by rfl) ⟨415982, by rfl⟩ : syracuseStep 554643 = 831965) B831965
theorem B554659 : Blo 550806 554659 := bstep (se 1 (by rfl) ⟨415994, by rfl⟩ : syracuseStep 554659 = 831989) B831989
theorem B1767089 : Blo 550806 1767089 := bstep (se 2 (by rfl) ⟨662658, by rfl⟩ : syracuseStep 1767089 = 1325317) B1325317
theorem B3536561 : Blo 550806 3536561 := bstep (se 2 (by rfl) ⟨1326210, by rfl⟩ : syracuseStep 3536561 = 2652421) B2652421
theorem B554675 : Blo 550806 554675 := bstep (se 1 (by rfl) ⟨416006, by rfl⟩ : syracuseStep 554675 = 832013) B832013
theorem B554691 : Blo 550806 554691 := bstep (se 1 (by rfl) ⟨416018, by rfl⟩ : syracuseStep 554691 = 832037) B832037
theorem B5961413 : Blo 550806 5961413 := bstep (se 4 (by rfl) ⟨558882, by rfl⟩ : syracuseStep 5961413 = 1117765) B1117765
theorem B554707 : Blo 550806 554707 := bstep (se 1 (by rfl) ⟨416030, by rfl⟩ : syracuseStep 554707 = 832061) B832061
theorem B554723 : Blo 550806 554723 := bstep (se 1 (by rfl) ⟨416042, by rfl⟩ : syracuseStep 554723 = 832085) B832085
theorem B620275 : Blo 550806 620275 := bstep (se 1 (by rfl) ⟨465206, by rfl⟩ : syracuseStep 620275 = 930413) B930413
theorem B554739 : Blo 550806 554739 := bstep (se 1 (by rfl) ⟨416054, by rfl⟩ : syracuseStep 554739 = 832109) B832109
theorem B554755 : Blo 550806 554755 := bstep (se 1 (by rfl) ⟨416066, by rfl⟩ : syracuseStep 554755 = 832133) B832133
theorem B554771 : Blo 550806 554771 := bstep (se 1 (by rfl) ⟨416078, by rfl⟩ : syracuseStep 554771 = 832157) B832157
theorem B554787 : Blo 550806 554787 := bstep (se 1 (by rfl) ⟨416090, by rfl⟩ : syracuseStep 554787 = 832181) B832181
theorem B1767217 : Blo 550806 1767217 := bstep (se 2 (by rfl) ⟨662706, by rfl⟩ : syracuseStep 1767217 = 1325413) B1325413
theorem B554803 : Blo 550806 554803 := bstep (se 1 (by rfl) ⟨416102, by rfl⟩ : syracuseStep 554803 = 832205) B832205
theorem B1800035 : Blo 550806 1800035 := bstep (se 1 (by rfl) ⟨1350026, by rfl⟩ : syracuseStep 1800035 = 2700053) B2700053
theorem B620419 : Blo 550806 620419 := bstep (se 1 (by rfl) ⟨465314, by rfl⟩ : syracuseStep 620419 = 930629) B930629
theorem B1243025 : Blo 550806 1243025 := bstep (se 2 (by rfl) ⟨466134, by rfl⟩ : syracuseStep 1243025 = 932269) B932269
theorem B1243043 : Blo 550806 1243043 := bstep (se 1 (by rfl) ⟨932282, by rfl⟩ : syracuseStep 1243043 = 1864565) B1864565
theorem B1865645 : Blo 550806 1865645 := bstep (se 3 (by rfl) ⟨349808, by rfl⟩ : syracuseStep 1865645 = 699617) B699617
theorem B1046449 : Blo 550806 1046449 := bstep (se 2 (by rfl) ⟨392418, by rfl⟩ : syracuseStep 1046449 = 784837) B784837
theorem B1865699 : Blo 550806 1865699 := bstep (se 1 (by rfl) ⟨1399274, by rfl⟩ : syracuseStep 1865699 = 2798549) B2798549
theorem B620563 : Blo 550806 620563 := bstep (se 1 (by rfl) ⟨465422, by rfl⟩ : syracuseStep 620563 = 930845) B930845
theorem B1177649 : Blo 550806 1177649 := bstep (se 2 (by rfl) ⟨441618, by rfl⟩ : syracuseStep 1177649 = 883237) B883237
theorem B1767473 : Blo 550806 1767473 := bstep (se 2 (by rfl) ⟨662802, by rfl⟩ : syracuseStep 1767473 = 1325605) B1325605
theorem B2652209 : Blo 550806 2652209 := bstep (se 2 (by rfl) ⟨994578, by rfl⟩ : syracuseStep 2652209 = 1989157) B1989157
theorem B620707 : Blo 550806 620707 := bstep (se 1 (by rfl) ⟨465530, by rfl⟩ : syracuseStep 620707 = 931061) B931061
theorem B2095267 : Blo 550806 2095267 := bstep (se 1 (by rfl) ⟨1571450, by rfl⟩ : syracuseStep 2095267 = 3142901) B3142901
theorem B1243313 : Blo 550806 1243313 := bstep (se 2 (by rfl) ⟨466242, by rfl⟩ : syracuseStep 1243313 = 932485) B932485
theorem B1243331 : Blo 550806 1243331 := bstep (se 1 (by rfl) ⟨932498, by rfl⟩ : syracuseStep 1243331 = 1864997) B1864997
theorem B1865969 : Blo 550806 1865969 := bstep (se 2 (by rfl) ⟨699738, by rfl⟩ : syracuseStep 1865969 = 1399477) B1399477
theorem B620851 : Blo 550806 620851 := bstep (se 1 (by rfl) ⟨465638, by rfl⟩ : syracuseStep 620851 = 931277) B931277
theorem B3602765 : Blo 550806 3602765 := bstep (se 3 (by rfl) ⟨675518, by rfl⟩ : syracuseStep 3602765 = 1351037) B1351037
theorem B784723 : Blo 550806 784723 := bstep (se 1 (by rfl) ⟨588542, by rfl⟩ : syracuseStep 784723 = 1177085) B1177085
theorem B883121 : Blo 550806 883121 := bstep (se 2 (by rfl) ⟨331170, by rfl⟩ : syracuseStep 883121 = 662341) B662341
theorem B620995 : Blo 550806 620995 := bstep (se 1 (by rfl) ⟨465746, by rfl⟩ : syracuseStep 620995 = 931493) B931493
theorem B1243601 : Blo 550806 1243601 := bstep (se 2 (by rfl) ⟨466350, by rfl⟩ : syracuseStep 1243601 = 932701) B932701
theorem B1243619 : Blo 550806 1243619 := bstep (se 1 (by rfl) ⟨932714, by rfl⟩ : syracuseStep 1243619 = 1865429) B1865429
theorem B2128355 : Blo 550806 2128355 := bstep (se 1 (by rfl) ⟨1596266, by rfl⟩ : syracuseStep 2128355 = 3192533) B3192533
theorem B621139 : Blo 550806 621139 := bstep (se 1 (by rfl) ⟨465854, by rfl⟩ : syracuseStep 621139 = 931709) B931709
theorem B621283 : Blo 550806 621283 := bstep (se 1 (by rfl) ⟨465962, by rfl⟩ : syracuseStep 621283 = 931925) B931925
theorem B1243889 : Blo 550806 1243889 := bstep (se 2 (by rfl) ⟨466458, by rfl⟩ : syracuseStep 1243889 = 932917) B932917
theorem B1243907 : Blo 550806 1243907 := bstep (se 1 (by rfl) ⟨932930, by rfl⟩ : syracuseStep 1243907 = 1865861) B1865861
theorem B1866509 : Blo 550806 1866509 := bstep (se 3 (by rfl) ⟨349970, by rfl⟩ : syracuseStep 1866509 = 699941) B699941
theorem B1571633 : Blo 550806 1571633 := bstep (se 2 (by rfl) ⟨589362, by rfl⟩ : syracuseStep 1571633 = 1178725) B1178725
theorem B2358065 : Blo 550806 2358065 := bstep (se 2 (by rfl) ⟨884274, by rfl⟩ : syracuseStep 2358065 = 1768549) B1768549
theorem B1866563 : Blo 550806 1866563 := bstep (se 1 (by rfl) ⟨1399922, by rfl⟩ : syracuseStep 1866563 = 2799845) B2799845
theorem B621427 : Blo 550806 621427 := bstep (se 1 (by rfl) ⟨466070, by rfl⟩ : syracuseStep 621427 = 932141) B932141
theorem B1047505 : Blo 550806 1047505 := bstep (se 2 (by rfl) ⟨392814, by rfl⟩ : syracuseStep 1047505 = 785629) B785629
theorem B621571 : Blo 550806 621571 := bstep (se 1 (by rfl) ⟨466178, by rfl⟩ : syracuseStep 621571 = 932357) B932357
theorem B1244177 : Blo 550806 1244177 := bstep (se 2 (by rfl) ⟨466566, by rfl⟩ : syracuseStep 1244177 = 933133) B933133
theorem B1244195 : Blo 550806 1244195 := bstep (se 1 (by rfl) ⟨933146, by rfl⟩ : syracuseStep 1244195 = 1866293) B1866293
theorem B1866833 : Blo 550806 1866833 := bstep (se 2 (by rfl) ⟨700062, by rfl⟩ : syracuseStep 1866833 = 1400125) B1400125
theorem B3538019 : Blo 550806 3538019 := bstep (se 1 (by rfl) ⟨2653514, by rfl⟩ : syracuseStep 3538019 = 5307029) B5307029
theorem B621715 : Blo 550806 621715 := bstep (se 1 (by rfl) ⟨466286, by rfl⟩ : syracuseStep 621715 = 932573) B932573
theorem B883955 : Blo 550806 883955 := bstep (se 1 (by rfl) ⟨662966, by rfl⟩ : syracuseStep 883955 = 1325933) B1325933
theorem B621859 : Blo 550806 621859 := bstep (se 1 (by rfl) ⟨466394, by rfl⟩ : syracuseStep 621859 = 932789) B932789
theorem B1244465 : Blo 550806 1244465 := bstep (se 2 (by rfl) ⟨466674, by rfl⟩ : syracuseStep 1244465 = 933349) B933349
theorem B1244483 : Blo 550806 1244483 := bstep (se 1 (by rfl) ⟨933362, by rfl⟩ : syracuseStep 1244483 = 1866725) B1866725
theorem B1047907 : Blo 550806 1047907 := bstep (se 1 (by rfl) ⟨785930, by rfl⟩ : syracuseStep 1047907 = 1571861) B1571861
theorem B1047953 : Blo 550806 1047953 := bstep (se 2 (by rfl) ⟨392982, by rfl⟩ : syracuseStep 1047953 = 785965) B785965
theorem B622003 : Blo 550806 622003 := bstep (se 1 (by rfl) ⟨466502, by rfl⟩ : syracuseStep 622003 = 933005) B933005
theorem B785857 : Blo 550806 785857 := bstep (se 2 (by rfl) ⟨294696, by rfl⟩ : syracuseStep 785857 = 589393) B589393
theorem B884243 : Blo 550806 884243 := bstep (se 1 (by rfl) ⟨663182, by rfl⟩ : syracuseStep 884243 = 1326365) B1326365
theorem B785953 : Blo 550806 785953 := bstep (se 2 (by rfl) ⟨294732, by rfl⟩ : syracuseStep 785953 = 589465) B589465
theorem B1179203 : Blo 550806 1179203 := bstep (se 1 (by rfl) ⟨884402, by rfl⟩ : syracuseStep 1179203 = 1768805) B1768805
theorem B622147 : Blo 550806 622147 := bstep (se 1 (by rfl) ⟨466610, by rfl⟩ : syracuseStep 622147 = 933221) B933221
theorem B1244753 : Blo 550806 1244753 := bstep (se 2 (by rfl) ⟨466782, by rfl⟩ : syracuseStep 1244753 = 933565) B933565
theorem B1244771 : Blo 550806 1244771 := bstep (se 1 (by rfl) ⟨933578, by rfl⟩ : syracuseStep 1244771 = 1867157) B1867157
theorem B1867373 : Blo 550806 1867373 := bstep (se 3 (by rfl) ⟨350132, by rfl⟩ : syracuseStep 1867373 = 700265) B700265
theorem B1867427 : Blo 550806 1867427 := bstep (se 1 (by rfl) ⟨1400570, by rfl⟩ : syracuseStep 1867427 = 2801141) B2801141
theorem B1048241 : Blo 550806 1048241 := bstep (se 2 (by rfl) ⟨393090, by rfl⟩ : syracuseStep 1048241 = 786181) B786181
theorem B1769165 : Blo 550806 1769165 := bstep (se 3 (by rfl) ⟨331718, by rfl⟩ : syracuseStep 1769165 = 663437) B663437
theorem B2358989 : Blo 550806 2358989 := bstep (se 3 (by rfl) ⟨442310, by rfl⟩ : syracuseStep 2358989 = 884621) B884621
theorem B622291 : Blo 550806 622291 := bstep (se 1 (by rfl) ⟨466718, by rfl⟩ : syracuseStep 622291 = 933437) B933437
theorem B851681 : Blo 550806 851681 := bstep (se 2 (by rfl) ⟨319380, by rfl⟩ : syracuseStep 851681 = 638761) B638761
theorem B884467 : Blo 550806 884467 := bstep (se 1 (by rfl) ⟨663350, by rfl⟩ : syracuseStep 884467 = 1326701) B1326701
theorem B1343267 : Blo 550806 1343267 := bstep (se 1 (by rfl) ⟨1007450, by rfl⟩ : syracuseStep 1343267 = 2014901) B2014901
theorem B589619 : Blo 550806 589619 := bstep (se 1 (by rfl) ⟨442214, by rfl⟩ : syracuseStep 589619 = 884429) B884429
theorem B6291269 : Blo 550806 6291269 := bstep (se 4 (by rfl) ⟨589806, by rfl⟩ : syracuseStep 6291269 = 1179613) B1179613
theorem B851809 : Blo 550806 851809 := bstep (se 2 (by rfl) ⟨319428, by rfl⟩ : syracuseStep 851809 = 638857) B638857
theorem B622435 : Blo 550806 622435 := bstep (se 1 (by rfl) ⟨466826, by rfl⟩ : syracuseStep 622435 = 933653) B933653
theorem B1245041 : Blo 550806 1245041 := bstep (se 2 (by rfl) ⟨466890, by rfl⟩ : syracuseStep 1245041 = 933781) B933781
theorem B1245059 : Blo 550806 1245059 := bstep (se 1 (by rfl) ⟨933794, by rfl⟩ : syracuseStep 1245059 = 1867589) B1867589
theorem B1867697 : Blo 550806 1867697 := bstep (se 2 (by rfl) ⟨700386, by rfl⟩ : syracuseStep 1867697 = 1400773) B1400773
theorem B622579 : Blo 550806 622579 := bstep (se 1 (by rfl) ⟨466934, by rfl⟩ : syracuseStep 622579 = 933869) B933869
theorem B1245185 : Blo 550806 1245185 := bstep (se 2 (by rfl) ⟨466944, by rfl⟩ : syracuseStep 1245185 = 933889) B933889
theorem B622615 : Blo 550806 622615 := bstep (se 1 (by rfl) ⟨466961, by rfl⟩ : syracuseStep 622615 = 933923) B933923
theorem B2097197 : Blo 550806 2097197 := bstep (se 3 (by rfl) ⟨393224, by rfl⟩ : syracuseStep 2097197 = 786449) B786449
theorem B3539045 : Blo 550806 3539045 := bstep (se 4 (by rfl) ⟨331785, by rfl⟩ : syracuseStep 3539045 = 663571) B663571
theorem B1048727 : Blo 550806 1048727 := bstep (se 1 (by rfl) ⟨786545, by rfl⟩ : syracuseStep 1048727 = 1573091) B1573091
theorem B622795 : Blo 550806 622795 := bstep (se 1 (by rfl) ⟨467096, by rfl⟩ : syracuseStep 622795 = 934193) B934193
theorem B1245401 : Blo 550806 1245401 := bstep (se 2 (by rfl) ⟨467025, by rfl⟩ : syracuseStep 1245401 = 934051) B934051
theorem B590123 : Blo 550806 590123 := bstep (se 1 (by rfl) ⟨442592, by rfl⟩ : syracuseStep 590123 = 885185) B885185
theorem B1769779 : Blo 550806 1769779 := bstep (se 1 (by rfl) ⟨1327334, by rfl⟩ : syracuseStep 1769779 = 2654669) B2654669
theorem B1179955 : Blo 550806 1179955 := bstep (se 1 (by rfl) ⟨884966, by rfl⟩ : syracuseStep 1179955 = 1769933) B1769933
theorem B1245491 : Blo 550806 1245491 := bstep (se 1 (by rfl) ⟨934118, by rfl⟩ : syracuseStep 1245491 = 1868237) B1868237
theorem B622903 : Blo 550806 622903 := bstep (se 1 (by rfl) ⟨467177, by rfl⟩ : syracuseStep 622903 = 934355) B934355
theorem B1245527 : Blo 550806 1245527 := bstep (se 1 (by rfl) ⟨934145, by rfl⟩ : syracuseStep 1245527 = 1868291) B1868291
theorem B4718999 : Blo 550806 4718999 := bstep (se 1 (by rfl) ⟨3539249, by rfl⟩ : syracuseStep 4718999 = 7078499) B7078499
theorem B1868183 : Blo 550806 1868183 := bstep (se 1 (by rfl) ⟨1401137, by rfl⟩ : syracuseStep 1868183 = 2802275) B2802275
theorem B590251 : Blo 550806 590251 := bstep (se 1 (by rfl) ⟨442688, by rfl⟩ : syracuseStep 590251 = 885377) B885377
theorem B1769921 : Blo 550806 1769921 := bstep (se 2 (by rfl) ⟨663720, by rfl⟩ : syracuseStep 1769921 = 1327441) B1327441
theorem B623083 : Blo 550806 623083 := bstep (se 1 (by rfl) ⟨467312, by rfl⟩ : syracuseStep 623083 = 934625) B934625
theorem B1245707 : Blo 550806 1245707 := bstep (se 1 (by rfl) ⟨934280, by rfl⟩ : syracuseStep 1245707 = 1868561) B1868561
theorem B1245761 : Blo 550806 1245761 := bstep (se 2 (by rfl) ⟨467160, by rfl⟩ : syracuseStep 1245761 = 934321) B934321
theorem B623191 : Blo 550806 623191 := bstep (se 1 (by rfl) ⟨467393, by rfl⟩ : syracuseStep 623191 = 934787) B934787
theorem B852619 : Blo 550806 852619 := bstep (se 1 (by rfl) ⟨639464, by rfl⟩ : syracuseStep 852619 = 1278929) B1278929
theorem B1049267 : Blo 550806 1049267 := bstep (se 1 (by rfl) ⟨786950, by rfl⟩ : syracuseStep 1049267 = 1573901) B1573901
theorem B623371 : Blo 550806 623371 := bstep (se 1 (by rfl) ⟨467528, by rfl⟩ : syracuseStep 623371 = 935057) B935057
theorem B1245977 : Blo 550806 1245977 := bstep (se 2 (by rfl) ⟨467241, by rfl⟩ : syracuseStep 1245977 = 934483) B934483
theorem B2097971 : Blo 550806 2097971 := bstep (se 1 (by rfl) ⟨1573478, by rfl⟩ : syracuseStep 2097971 = 3146957) B3146957
theorem B1246067 : Blo 550806 1246067 := bstep (se 1 (by rfl) ⟨934550, by rfl⟩ : syracuseStep 1246067 = 1869101) B1869101
theorem B623479 : Blo 550806 623479 := bstep (se 1 (by rfl) ⟨467609, by rfl⟩ : syracuseStep 623479 = 935219) B935219
theorem B1246103 : Blo 550806 1246103 := bstep (se 1 (by rfl) ⟨934577, by rfl⟩ : syracuseStep 1246103 = 1869155) B1869155
theorem B1868723 : Blo 550806 1868723 := bstep (se 1 (by rfl) ⟨1401542, by rfl⟩ : syracuseStep 1868723 = 2803085) B2803085
theorem B1180631 : Blo 550806 1180631 := bstep (se 1 (by rfl) ⟨885473, by rfl⟩ : syracuseStep 1180631 = 1770947) B1770947
theorem B1213427 : Blo 550806 1213427 := bstep (se 1 (by rfl) ⟨910070, by rfl⟩ : syracuseStep 1213427 = 1820141) B1820141
theorem B1180673 : Blo 550806 1180673 := bstep (se 2 (by rfl) ⟨442752, by rfl⟩ : syracuseStep 1180673 = 885505) B885505
theorem B623659 : Blo 550806 623659 := bstep (se 1 (by rfl) ⟨467744, by rfl⟩ : syracuseStep 623659 = 935489) B935489
theorem B1246283 : Blo 550806 1246283 := bstep (se 1 (by rfl) ⟨934712, by rfl⟩ : syracuseStep 1246283 = 1869425) B1869425
theorem B1246337 : Blo 550806 1246337 := bstep (se 2 (by rfl) ⟨467376, by rfl⟩ : syracuseStep 1246337 = 934753) B934753
theorem B623767 : Blo 550806 623767 := bstep (se 1 (by rfl) ⟨467825, by rfl⟩ : syracuseStep 623767 = 935651) B935651
theorem B1049753 : Blo 550806 1049753 := bstep (se 2 (by rfl) ⟨393657, by rfl⟩ : syracuseStep 1049753 = 787315) B787315
theorem B1868993 : Blo 550806 1868993 := bstep (se 2 (by rfl) ⟨700872, by rfl⟩ : syracuseStep 1868993 = 1401745) B1401745
theorem B2360593 : Blo 550806 2360593 := bstep (se 2 (by rfl) ⟨885222, by rfl⟩ : syracuseStep 2360593 = 1770445) B1770445
theorem B623947 : Blo 550806 623947 := bstep (se 1 (by rfl) ⟨467960, by rfl⟩ : syracuseStep 623947 = 935921) B935921
theorem B1246553 : Blo 550806 1246553 := bstep (se 2 (by rfl) ⟨467457, by rfl⟩ : syracuseStep 1246553 = 934915) B934915
theorem B1213849 : Blo 550806 1213849 := bstep (se 2 (by rfl) ⟨455193, by rfl⟩ : syracuseStep 1213849 = 910387) B910387
theorem B1246643 : Blo 550806 1246643 := bstep (se 1 (by rfl) ⟨934982, by rfl⟩ : syracuseStep 1246643 = 1869965) B1869965
theorem B624055 : Blo 550806 624055 := bstep (se 1 (by rfl) ⟨468041, by rfl⟩ : syracuseStep 624055 = 936083) B936083
theorem B120620501 : Blo 550806 120620501 := bstep (se 7 (by rfl) ⟨1413521, by rfl⟩ : syracuseStep 120620501 = 2827043) B2827043
theorem B1246679 : Blo 550806 1246679 := bstep (se 1 (by rfl) ⟨935009, by rfl⟩ : syracuseStep 1246679 = 1870019) B1870019
theorem B1246859 : Blo 550806 1246859 := bstep (se 1 (by rfl) ⟨935144, by rfl⟩ : syracuseStep 1246859 = 1870289) B1870289
theorem B1246913 : Blo 550806 1246913 := bstep (se 2 (by rfl) ⟨467592, by rfl⟩ : syracuseStep 1246913 = 935185) B935185
theorem B1869533 : Blo 550806 1869533 := bstep (se 3 (by rfl) ⟨350537, by rfl⟩ : syracuseStep 1869533 = 701075) B701075
theorem B1574731 : Blo 550806 1574731 := bstep (se 1 (by rfl) ⟨1181048, by rfl⟩ : syracuseStep 1574731 = 2362097) B2362097
theorem B1247129 : Blo 550806 1247129 := bstep (se 2 (by rfl) ⟨467673, by rfl⟩ : syracuseStep 1247129 = 935347) B935347
theorem B1247219 : Blo 550806 1247219 := bstep (se 1 (by rfl) ⟨935414, by rfl⟩ : syracuseStep 1247219 = 1870829) B1870829
theorem B1247255 : Blo 550806 1247255 := bstep (se 1 (by rfl) ⟨935441, by rfl⟩ : syracuseStep 1247255 = 1870883) B1870883
theorem B2525377 : Blo 550806 2525377 := bstep (se 2 (by rfl) ⟨947016, by rfl⟩ : syracuseStep 2525377 = 1894033) B1894033
theorem B1247435 : Blo 550806 1247435 := bstep (se 1 (by rfl) ⟨935576, by rfl⟩ : syracuseStep 1247435 = 1871153) B1871153
theorem B1247489 : Blo 550806 1247489 := bstep (se 2 (by rfl) ⟨467808, by rfl⟩ : syracuseStep 1247489 = 935617) B935617
theorem B2099459 : Blo 550806 2099459 := bstep (se 1 (by rfl) ⟨1574594, by rfl⟩ : syracuseStep 2099459 = 3149189) B3149189
theorem B4720913 : Blo 550806 4720913 := bstep (se 2 (by rfl) ⟨1770342, by rfl⟩ : syracuseStep 4720913 = 3540685) B3540685
theorem B1575233 : Blo 550806 1575233 := bstep (se 2 (by rfl) ⟨590712, by rfl⟩ : syracuseStep 1575233 = 1181425) B1181425
theorem B559499 : Blo 550806 559499 := bstep (se 1 (by rfl) ⟨419624, by rfl⟩ : syracuseStep 559499 = 839249) B839249
theorem B5966257 : Blo 550806 5966257 := bstep (se 2 (by rfl) ⟨2237346, by rfl⟩ : syracuseStep 5966257 = 4474693) B4474693
theorem B1247705 : Blo 550806 1247705 := bstep (se 2 (by rfl) ⟨467889, by rfl⟩ : syracuseStep 1247705 = 935779) B935779
theorem B1247795 : Blo 550806 1247795 := bstep (se 1 (by rfl) ⟨935846, by rfl⟩ : syracuseStep 1247795 = 1871693) B1871693
theorem B1051211 : Blo 550806 1051211 := bstep (se 1 (by rfl) ⟨788408, by rfl⟩ : syracuseStep 1051211 = 1576817) B1576817
theorem B1247831 : Blo 550806 1247831 := bstep (se 1 (by rfl) ⟨935873, by rfl⟩ : syracuseStep 1247831 = 1871747) B1871747
theorem B10783363 : Blo 550806 10783363 := bstep (se 1 (by rfl) ⟨8087522, by rfl⟩ : syracuseStep 10783363 = 16175045) B16175045
theorem B1575575 : Blo 550806 1575575 := bstep (se 1 (by rfl) ⟨1181681, by rfl⟩ : syracuseStep 1575575 = 2363363) B2363363
theorem B2099915 : Blo 550806 2099915 := bstep (se 1 (by rfl) ⟨1574936, by rfl⟩ : syracuseStep 2099915 = 3149873) B3149873
theorem B1051393 : Blo 550806 1051393 := bstep (se 2 (by rfl) ⟨394272, by rfl⟩ : syracuseStep 1051393 = 788545) B788545
theorem B1248011 : Blo 550806 1248011 := bstep (se 1 (by rfl) ⟨936008, by rfl⟩ : syracuseStep 1248011 = 1872017) B1872017
theorem B11209537 : Blo 550806 11209537 := bstep (se 2 (by rfl) ⟨4203576, by rfl⟩ : syracuseStep 11209537 = 8407153) B8407153
theorem B1248065 : Blo 550806 1248065 := bstep (se 2 (by rfl) ⟨468024, by rfl⟩ : syracuseStep 1248065 = 936049) B936049
theorem B1870667 : Blo 550806 1870667 := bstep (se 1 (by rfl) ⟨1403000, by rfl⟩ : syracuseStep 1870667 = 2806001) B2806001
theorem B1772381 : Blo 550806 1772381 := bstep (se 3 (by rfl) ⟨332321, by rfl⟩ : syracuseStep 1772381 = 664643) B664643
theorem B2100113 : Blo 550806 2100113 := bstep (se 2 (by rfl) ⟨787542, by rfl⟩ : syracuseStep 2100113 = 1575085) B1575085
theorem B1248281 : Blo 550806 1248281 := bstep (se 2 (by rfl) ⟨468105, by rfl⟩ : syracuseStep 1248281 = 936211) B936211
theorem B1870937 : Blo 550806 1870937 := bstep (se 2 (by rfl) ⟨701601, by rfl⟩ : syracuseStep 1870937 = 1403203) B1403203
theorem B1051841 : Blo 550806 1051841 := bstep (se 2 (by rfl) ⟨394440, by rfl⟩ : syracuseStep 1051841 = 788881) B788881
theorem B4197581 : Blo 550806 4197581 := bstep (se 3 (by rfl) ⟨787046, by rfl⟩ : syracuseStep 4197581 = 1574093) B1574093
theorem B1281367 : Blo 550806 1281367 := bstep (se 1 (by rfl) ⟨961025, by rfl⟩ : syracuseStep 1281367 = 1922051) B1922051
theorem B1052183 : Blo 550806 1052183 := bstep (se 1 (by rfl) ⟨789137, by rfl⟩ : syracuseStep 1052183 = 1578275) B1578275
theorem B2100887 : Blo 550806 2100887 := bstep (se 1 (by rfl) ⟨1575665, by rfl⟩ : syracuseStep 2100887 = 3151331) B3151331
theorem B4198067 : Blo 550806 4198067 := bstep (se 1 (by rfl) ⟨3148550, by rfl⟩ : syracuseStep 4198067 = 6297101) B6297101
theorem B1871639 : Blo 550806 1871639 := bstep (se 1 (by rfl) ⟨1403729, by rfl⟩ : syracuseStep 1871639 = 2807459) B2807459
theorem B1183577 : Blo 550806 1183577 := bstep (se 2 (by rfl) ⟨443841, by rfl⟩ : syracuseStep 1183577 = 887683) B887683
theorem B2101085 : Blo 550806 2101085 := bstep (se 3 (by rfl) ⟨393953, by rfl⟩ : syracuseStep 2101085 = 787907) B787907
theorem B30609251 : Blo 550806 30609251 := bstep (se 1 (by rfl) ⟨22956938, by rfl⟩ : syracuseStep 30609251 = 45913877) B45913877
theorem B9474083 : Blo 550806 9474083 := bstep (se 1 (by rfl) ⟨7105562, by rfl⟩ : syracuseStep 9474083 = 14211125) B14211125
theorem B561259 : Blo 550806 561259 := bstep (se 1 (by rfl) ⟨420944, by rfl⟩ : syracuseStep 561259 = 841889) B841889
theorem B18157709 : Blo 550806 18157709 := bstep (se 3 (by rfl) ⟨3404570, by rfl⟩ : syracuseStep 18157709 = 6809141) B6809141
theorem B1052851 : Blo 550806 1052851 := bstep (se 1 (by rfl) ⟨789638, by rfl⟩ : syracuseStep 1052851 = 1579277) B1579277
theorem B1183987 : Blo 550806 1183987 := bstep (se 1 (by rfl) ⟨887990, by rfl⟩ : syracuseStep 1183987 = 1775981) B1775981
theorem B1872179 : Blo 550806 1872179 := bstep (se 1 (by rfl) ⟨1404134, by rfl⟩ : syracuseStep 1872179 = 2808269) B2808269
theorem B2363737 : Blo 550806 2363737 := bstep (se 2 (by rfl) ⟨886401, by rfl⟩ : syracuseStep 2363737 = 1772803) B1772803
theorem B1675799 : Blo 550806 1675799 := bstep (se 1 (by rfl) ⟨1256849, by rfl⟩ : syracuseStep 1675799 = 2513699) B2513699
theorem B1184321 : Blo 550806 1184321 := bstep (se 2 (by rfl) ⟨444120, by rfl⟩ : syracuseStep 1184321 = 888241) B888241
theorem B1872449 : Blo 550806 1872449 := bstep (se 2 (by rfl) ⟨702168, by rfl⟩ : syracuseStep 1872449 = 1404337) B1404337
theorem B2789963 : Blo 550806 2789963 := bstep (se 1 (by rfl) ⟨2092472, by rfl⟩ : syracuseStep 2789963 = 4184945) B4184945
theorem B1577693 : Blo 550806 1577693 := bstep (se 3 (by rfl) ⟨295817, by rfl⟩ : syracuseStep 1577693 = 591635) B591635
theorem B2364353 : Blo 550806 2364353 := bstep (se 2 (by rfl) ⟨886632, by rfl⟩ : syracuseStep 2364353 = 1773265) B1773265
theorem B1578035 : Blo 550806 1578035 := bstep (se 1 (by rfl) ⟨1183526, by rfl⟩ : syracuseStep 1578035 = 2367053) B2367053
theorem B1676381 : Blo 550806 1676381 := bstep (se 3 (by rfl) ⟨314321, by rfl⟩ : syracuseStep 1676381 = 628643) B628643
theorem B4199525 : Blo 550806 4199525 := bstep (se 4 (by rfl) ⟨393705, by rfl⟩ : syracuseStep 4199525 = 787411) B787411
theorem B4200011 : Blo 550806 4200011 := bstep (se 1 (by rfl) ⟨3150008, by rfl⟩ : syracuseStep 4200011 = 6300017) B6300017
theorem B2103043 : Blo 550806 2103043 := bstep (se 1 (by rfl) ⟨1577282, by rfl⟩ : syracuseStep 2103043 = 3154565) B3154565
theorem B2103347 : Blo 550806 2103347 := bstep (se 1 (by rfl) ⟨1577510, by rfl⟩ : syracuseStep 2103347 = 3155021) B3155021
theorem B8198213 : Blo 550806 8198213 := bstep (se 4 (by rfl) ⟨768582, by rfl⟩ : syracuseStep 8198213 = 1537165) B1537165
theorem B9607373 : Blo 550806 9607373 := bstep (se 3 (by rfl) ⟨1801382, by rfl⟩ : syracuseStep 9607373 = 3602765) B3602765
theorem B1349849 : Blo 550806 1349849 := bstep (se 2 (by rfl) ⟨506193, by rfl⟩ : syracuseStep 1349849 = 1012387) B1012387
theorem B629035 : Blo 550806 629035 := bstep (se 1 (by rfl) ⟨471776, by rfl⟩ : syracuseStep 629035 = 943553) B943553
theorem B2791745 : Blo 550806 2791745 := bstep (se 2 (by rfl) ⟨1046904, by rfl⟩ : syracuseStep 2791745 = 2093809) B2093809
theorem B3021187 : Blo 550806 3021187 := bstep (se 1 (by rfl) ⟨2265890, by rfl⟩ : syracuseStep 3021187 = 4531781) B4531781
theorem B2104001 : Blo 550806 2104001 := bstep (se 2 (by rfl) ⟨789000, by rfl⟩ : syracuseStep 2104001 = 1578001) B1578001
theorem B1415987 : Blo 550806 1415987 := bstep (se 1 (by rfl) ⟨1061990, by rfl⟩ : syracuseStep 1415987 = 2123981) B2123981
theorem B629579 : Blo 550806 629579 := bstep (se 1 (by rfl) ⟨472184, by rfl⟩ : syracuseStep 629579 = 944369) B944369
theorem B826265 : Blo 550806 826265 := bstep (se 2 (by rfl) ⟨309849, by rfl⟩ : syracuseStep 826265 = 619699) B619699
theorem B826379 : Blo 550806 826379 := bstep (se 1 (by rfl) ⟨619784, by rfl⟩ : syracuseStep 826379 = 1239569) B1239569
theorem B826391 : Blo 550806 826391 := bstep (se 1 (by rfl) ⟨619793, by rfl⟩ : syracuseStep 826391 = 1239587) B1239587
theorem B2432051 : Blo 550806 2432051 := bstep (se 1 (by rfl) ⟨1824038, by rfl⟩ : syracuseStep 2432051 = 3648077) B3648077
theorem B826457 : Blo 550806 826457 := bstep (se 2 (by rfl) ⟨309921, by rfl⟩ : syracuseStep 826457 = 619843) B619843
theorem B7183511 : Blo 550806 7183511 := bstep (se 1 (by rfl) ⟨5387633, by rfl⟩ : syracuseStep 7183511 = 10775267) B10775267
theorem B826571 : Blo 550806 826571 := bstep (se 1 (by rfl) ⟨619928, by rfl⟩ : syracuseStep 826571 = 1239857) B1239857
theorem B826583 : Blo 550806 826583 := bstep (se 1 (by rfl) ⟨619937, by rfl⟩ : syracuseStep 826583 = 1239875) B1239875
theorem B826649 : Blo 550806 826649 := bstep (se 2 (by rfl) ⟨309993, by rfl⟩ : syracuseStep 826649 = 619987) B619987
theorem B2366813 : Blo 550806 2366813 := bstep (se 3 (by rfl) ⟨443777, by rfl⟩ : syracuseStep 2366813 = 887555) B887555
theorem B826763 : Blo 550806 826763 := bstep (se 1 (by rfl) ⟨620072, by rfl⟩ : syracuseStep 826763 = 1240145) B1240145
theorem B826775 : Blo 550806 826775 := bstep (se 1 (by rfl) ⟨620081, by rfl⟩ : syracuseStep 826775 = 1240163) B1240163
theorem B826841 : Blo 550806 826841 := bstep (se 2 (by rfl) ⟨310065, by rfl⟩ : syracuseStep 826841 = 620131) B620131
theorem B1678913 : Blo 550806 1678913 := bstep (se 2 (by rfl) ⟨629592, by rfl⟩ : syracuseStep 1678913 = 1259185) B1259185
theorem B826955 : Blo 550806 826955 := bstep (se 1 (by rfl) ⟨620216, by rfl⟩ : syracuseStep 826955 = 1240433) B1240433
theorem B826967 : Blo 550806 826967 := bstep (se 1 (by rfl) ⟨620225, by rfl⟩ : syracuseStep 826967 = 1240451) B1240451
theorem B827033 : Blo 550806 827033 := bstep (se 2 (by rfl) ⟨310137, by rfl⟩ : syracuseStep 827033 = 620275) B620275
theorem B827147 : Blo 550806 827147 := bstep (se 1 (by rfl) ⟨620360, by rfl⟩ : syracuseStep 827147 = 1240721) B1240721
theorem B827159 : Blo 550806 827159 := bstep (se 1 (by rfl) ⟨620369, by rfl⟩ : syracuseStep 827159 = 1240739) B1240739
theorem B1122113 : Blo 550806 1122113 := bstep (se 2 (by rfl) ⟨420792, by rfl⟩ : syracuseStep 1122113 = 841585) B841585
theorem B827225 : Blo 550806 827225 := bstep (se 2 (by rfl) ⟨310209, by rfl⟩ : syracuseStep 827225 = 620419) B620419
theorem B3153815 : Blo 550806 3153815 := bstep (se 1 (by rfl) ⟨2365361, by rfl⟩ : syracuseStep 3153815 = 4730723) B4730723
theorem B2105261 : Blo 550806 2105261 := bstep (se 3 (by rfl) ⟨394736, by rfl⟩ : syracuseStep 2105261 = 789473) B789473
theorem B827339 : Blo 550806 827339 := bstep (se 1 (by rfl) ⟨620504, by rfl⟩ : syracuseStep 827339 = 1241009) B1241009
theorem B2105291 : Blo 550806 2105291 := bstep (se 1 (by rfl) ⟨1578968, by rfl⟩ : syracuseStep 2105291 = 3157937) B3157937
theorem B827351 : Blo 550806 827351 := bstep (se 1 (by rfl) ⟨620513, by rfl⟩ : syracuseStep 827351 = 1241027) B1241027
theorem B827417 : Blo 550806 827417 := bstep (se 2 (by rfl) ⟨310281, by rfl⟩ : syracuseStep 827417 = 620563) B620563
theorem B827531 : Blo 550806 827531 := bstep (se 1 (by rfl) ⟨620648, by rfl⟩ : syracuseStep 827531 = 1241297) B1241297
theorem B827543 : Blo 550806 827543 := bstep (se 1 (by rfl) ⟨620657, by rfl⟩ : syracuseStep 827543 = 1241315) B1241315
theorem B827609 : Blo 550806 827609 := bstep (se 2 (by rfl) ⟨310353, by rfl⟩ : syracuseStep 827609 = 620707) B620707
theorem B2793689 : Blo 550806 2793689 := bstep (se 2 (by rfl) ⟨1047633, by rfl⟩ : syracuseStep 2793689 = 2095267) B2095267
theorem B827723 : Blo 550806 827723 := bstep (se 1 (by rfl) ⟨620792, by rfl⟩ : syracuseStep 827723 = 1241585) B1241585
theorem B827735 : Blo 550806 827735 := bstep (se 1 (by rfl) ⟨620801, by rfl⟩ : syracuseStep 827735 = 1241603) B1241603
theorem B827801 : Blo 550806 827801 := bstep (se 2 (by rfl) ⟨310425, by rfl⟩ : syracuseStep 827801 = 620851) B620851
theorem B3350963 : Blo 550806 3350963 := bstep (se 1 (by rfl) ⟨2513222, by rfl⟩ : syracuseStep 3350963 = 5026445) B5026445
theorem B2564531 : Blo 550806 2564531 := bstep (se 1 (by rfl) ⟨1923398, by rfl⟩ : syracuseStep 2564531 = 3846797) B3846797
theorem B827915 : Blo 550806 827915 := bstep (se 1 (by rfl) ⟨620936, by rfl⟩ : syracuseStep 827915 = 1241873) B1241873
theorem B827927 : Blo 550806 827927 := bstep (se 1 (by rfl) ⟨620945, by rfl⟩ : syracuseStep 827927 = 1241891) B1241891
theorem B827993 : Blo 550806 827993 := bstep (se 2 (by rfl) ⟨310497, by rfl⟩ : syracuseStep 827993 = 620995) B620995
theorem B2105945 : Blo 550806 2105945 := bstep (se 2 (by rfl) ⟨789729, by rfl⟩ : syracuseStep 2105945 = 1579459) B1579459
theorem B828107 : Blo 550806 828107 := bstep (se 1 (by rfl) ⟨621080, by rfl⟩ : syracuseStep 828107 = 1242161) B1242161
theorem B828119 : Blo 550806 828119 := bstep (se 1 (by rfl) ⟨621089, by rfl⟩ : syracuseStep 828119 = 1242179) B1242179
theorem B598807 : Blo 550806 598807 := bstep (se 1 (by rfl) ⟨449105, by rfl⟩ : syracuseStep 598807 = 898211) B898211
theorem B828185 : Blo 550806 828185 := bstep (se 2 (by rfl) ⟨310569, by rfl⟩ : syracuseStep 828185 = 621139) B621139
theorem B2663243 : Blo 550806 2663243 := bstep (se 1 (by rfl) ⟨1997432, by rfl⟩ : syracuseStep 2663243 = 3994865) B3994865
theorem B2040665 : Blo 550806 2040665 := bstep (se 2 (by rfl) ⟨765249, by rfl⟩ : syracuseStep 2040665 = 1530499) B1530499
theorem B828299 : Blo 550806 828299 := bstep (se 1 (by rfl) ⟨621224, by rfl⟩ : syracuseStep 828299 = 1242449) B1242449
theorem B828311 : Blo 550806 828311 := bstep (se 1 (by rfl) ⟨621233, by rfl⟩ : syracuseStep 828311 = 1242467) B1242467
theorem B2106263 : Blo 550806 2106263 := bstep (se 1 (by rfl) ⟨1579697, by rfl⟩ : syracuseStep 2106263 = 3159395) B3159395
theorem B631735 : Blo 550806 631735 := bstep (se 1 (by rfl) ⟨473801, by rfl⟩ : syracuseStep 631735 = 947603) B947603
theorem B828377 : Blo 550806 828377 := bstep (se 2 (by rfl) ⟨310641, by rfl⟩ : syracuseStep 828377 = 621283) B621283
theorem B828491 : Blo 550806 828491 := bstep (se 1 (by rfl) ⟨621368, by rfl⟩ : syracuseStep 828491 = 1242737) B1242737
theorem B828503 : Blo 550806 828503 := bstep (se 1 (by rfl) ⟨621377, by rfl⟩ : syracuseStep 828503 = 1242755) B1242755
theorem B3974275 : Blo 550806 3974275 := bstep (se 1 (by rfl) ⟨2980706, by rfl⟩ : syracuseStep 3974275 = 5961413) B5961413
theorem B828569 : Blo 550806 828569 := bstep (se 2 (by rfl) ⟨310713, by rfl⟩ : syracuseStep 828569 = 621427) B621427
theorem B599275 : Blo 550806 599275 := bstep (se 1 (by rfl) ⟨449456, by rfl⟩ : syracuseStep 599275 = 898913) B898913
theorem B828683 : Blo 550806 828683 := bstep (se 1 (by rfl) ⟨621512, by rfl⟩ : syracuseStep 828683 = 1243025) B1243025
theorem B828695 : Blo 550806 828695 := bstep (se 1 (by rfl) ⟨621521, by rfl⟩ : syracuseStep 828695 = 1243043) B1243043
theorem B828761 : Blo 550806 828761 := bstep (se 2 (by rfl) ⟨310785, by rfl⟩ : syracuseStep 828761 = 621571) B621571
theorem B828875 : Blo 550806 828875 := bstep (se 1 (by rfl) ⟨621656, by rfl⟩ : syracuseStep 828875 = 1243313) B1243313
theorem B828887 : Blo 550806 828887 := bstep (se 1 (by rfl) ⟨621665, by rfl⟩ : syracuseStep 828887 = 1243331) B1243331
theorem B828953 : Blo 550806 828953 := bstep (se 2 (by rfl) ⟨310857, by rfl⟩ : syracuseStep 828953 = 621715) B621715
theorem B829067 : Blo 550806 829067 := bstep (se 1 (by rfl) ⟨621800, by rfl⟩ : syracuseStep 829067 = 1243601) B1243601
theorem B829079 : Blo 550806 829079 := bstep (se 1 (by rfl) ⟨621809, by rfl⟩ : syracuseStep 829079 = 1243619) B1243619
theorem B1418903 : Blo 550806 1418903 := bstep (se 1 (by rfl) ⟨1064177, by rfl⟩ : syracuseStep 1418903 = 2128355) B2128355
theorem B829145 : Blo 550806 829145 := bstep (se 2 (by rfl) ⟨310929, by rfl⟩ : syracuseStep 829145 = 621859) B621859
theorem B2795309 : Blo 550806 2795309 := bstep (se 3 (by rfl) ⟨524120, by rfl⟩ : syracuseStep 2795309 = 1048241) B1048241
theorem B829259 : Blo 550806 829259 := bstep (se 1 (by rfl) ⟨621944, by rfl⟩ : syracuseStep 829259 = 1243889) B1243889
theorem B829271 : Blo 550806 829271 := bstep (se 1 (by rfl) ⟨621953, by rfl⟩ : syracuseStep 829271 = 1243907) B1243907
theorem B2369411 : Blo 550806 2369411 := bstep (se 1 (by rfl) ⟨1777058, by rfl⟩ : syracuseStep 2369411 = 3554117) B3554117
theorem B829337 : Blo 550806 829337 := bstep (se 2 (by rfl) ⟨311001, by rfl⟩ : syracuseStep 829337 = 622003) B622003
theorem B2271149 : Blo 550806 2271149 := bstep (se 3 (by rfl) ⟨425840, by rfl⟩ : syracuseStep 2271149 = 851681) B851681
theorem B993217 : Blo 550806 993217 := bstep (se 2 (by rfl) ⟨372456, by rfl⟩ : syracuseStep 993217 = 744913) B744913
theorem B829451 : Blo 550806 829451 := bstep (se 1 (by rfl) ⟨622088, by rfl⟩ : syracuseStep 829451 = 1244177) B1244177
theorem B10102801 : Blo 550806 10102801 := bstep (se 2 (by rfl) ⟨3788550, by rfl⟩ : syracuseStep 10102801 = 7577101) B7577101
theorem B829463 : Blo 550806 829463 := bstep (se 1 (by rfl) ⟨622097, by rfl⟩ : syracuseStep 829463 = 1244195) B1244195
theorem B829529 : Blo 550806 829529 := bstep (se 2 (by rfl) ⟨311073, by rfl⟩ : syracuseStep 829529 = 622147) B622147
theorem B829643 : Blo 550806 829643 := bstep (se 1 (by rfl) ⟨622232, by rfl⟩ : syracuseStep 829643 = 1244465) B1244465
theorem B829655 : Blo 550806 829655 := bstep (se 1 (by rfl) ⟨622241, by rfl⟩ : syracuseStep 829655 = 1244483) B1244483
theorem B698635 : Blo 550806 698635 := bstep (se 1 (by rfl) ⟨523976, by rfl⟩ : syracuseStep 698635 = 1047953) B1047953
theorem B829721 : Blo 550806 829721 := bstep (se 2 (by rfl) ⟨311145, by rfl⟩ : syracuseStep 829721 = 622291) B622291
theorem B829835 : Blo 550806 829835 := bstep (se 1 (by rfl) ⟨622376, by rfl⟩ : syracuseStep 829835 = 1244753) B1244753
theorem B829847 : Blo 550806 829847 := bstep (se 1 (by rfl) ⟨622385, by rfl⟩ : syracuseStep 829847 = 1244771) B1244771
theorem B829913 : Blo 550806 829913 := bstep (se 2 (by rfl) ⟨311217, by rfl⟩ : syracuseStep 829913 = 622435) B622435
theorem B895511 : Blo 550806 895511 := bstep (se 1 (by rfl) ⟨671633, by rfl⟩ : syracuseStep 895511 = 1343267) B1343267
theorem B830027 : Blo 550806 830027 := bstep (se 1 (by rfl) ⟨622520, by rfl⟩ : syracuseStep 830027 = 1245041) B1245041
theorem B830039 : Blo 550806 830039 := bstep (se 1 (by rfl) ⟨622529, by rfl⟩ : syracuseStep 830039 = 1245059) B1245059
theorem B2992733 : Blo 550806 2992733 := bstep (se 3 (by rfl) ⟨561137, by rfl⟩ : syracuseStep 2992733 = 1122275) B1122275
theorem B7547543 : Blo 550806 7547543 := bstep (se 1 (by rfl) ⟨5660657, by rfl⟩ : syracuseStep 7547543 = 11321315) B11321315
theorem B830105 : Blo 550806 830105 := bstep (se 2 (by rfl) ⟨311289, by rfl⟩ : syracuseStep 830105 = 622579) B622579
theorem B830219 : Blo 550806 830219 := bstep (se 1 (by rfl) ⟨622664, by rfl⟩ : syracuseStep 830219 = 1245329) B1245329
theorem B830231 : Blo 550806 830231 := bstep (se 1 (by rfl) ⟨622673, by rfl⟩ : syracuseStep 830231 = 1245347) B1245347
theorem B4205357 : Blo 550806 4205357 := bstep (se 3 (by rfl) ⟨788504, by rfl⟩ : syracuseStep 4205357 = 1577009) B1577009
theorem B830297 : Blo 550806 830297 := bstep (se 2 (by rfl) ⟨311361, by rfl⟩ : syracuseStep 830297 = 622723) B622723
theorem B830411 : Blo 550806 830411 := bstep (se 1 (by rfl) ⟨622808, by rfl⟩ : syracuseStep 830411 = 1245617) B1245617
theorem B830423 : Blo 550806 830423 := bstep (se 1 (by rfl) ⟨622817, by rfl⟩ : syracuseStep 830423 = 1245635) B1245635
theorem B3550169 : Blo 550806 3550169 := bstep (se 2 (by rfl) ⟨1331313, by rfl⟩ : syracuseStep 3550169 = 2662627) B2662627
theorem B830489 : Blo 550806 830489 := bstep (se 2 (by rfl) ⟨311433, by rfl⟩ : syracuseStep 830489 = 622867) B622867
theorem B7973923 : Blo 550806 7973923 := bstep (se 1 (by rfl) ⟨5980442, by rfl⟩ : syracuseStep 7973923 = 11960885) B11960885
theorem B830603 : Blo 550806 830603 := bstep (se 1 (by rfl) ⟨622952, by rfl⟩ : syracuseStep 830603 = 1245905) B1245905
theorem B830615 : Blo 550806 830615 := bstep (se 1 (by rfl) ⟨622961, by rfl⟩ : syracuseStep 830615 = 1245923) B1245923
theorem B699607 : Blo 550806 699607 := bstep (se 1 (by rfl) ⟨524705, by rfl⟩ : syracuseStep 699607 = 1049411) B1049411
theorem B830681 : Blo 550806 830681 := bstep (se 2 (by rfl) ⟨311505, by rfl⟩ : syracuseStep 830681 = 623011) B623011
theorem B830795 : Blo 550806 830795 := bstep (se 1 (by rfl) ⟨623096, by rfl⟩ : syracuseStep 830795 = 1246193) B1246193
theorem B830807 : Blo 550806 830807 := bstep (se 1 (by rfl) ⟨623105, by rfl⟩ : syracuseStep 830807 = 1246211) B1246211
theorem B830873 : Blo 550806 830873 := bstep (se 2 (by rfl) ⟨311577, by rfl⟩ : syracuseStep 830873 = 623155) B623155
theorem B1420747 : Blo 550806 1420747 := bstep (se 1 (by rfl) ⟨1065560, by rfl⟩ : syracuseStep 1420747 = 2131121) B2131121
theorem B830987 : Blo 550806 830987 := bstep (se 1 (by rfl) ⟨623240, by rfl⟩ : syracuseStep 830987 = 1246481) B1246481
theorem B830999 : Blo 550806 830999 := bstep (se 1 (by rfl) ⟨623249, by rfl⟩ : syracuseStep 830999 = 1246499) B1246499
theorem B1257049 : Blo 550806 1257049 := bstep (se 2 (by rfl) ⟨471393, by rfl⟩ : syracuseStep 1257049 = 942787) B942787
theorem B831065 : Blo 550806 831065 := bstep (se 2 (by rfl) ⟨311649, by rfl⟩ : syracuseStep 831065 = 623299) B623299
theorem B831179 : Blo 550806 831179 := bstep (se 1 (by rfl) ⟨623384, by rfl⟩ : syracuseStep 831179 = 1246769) B1246769
theorem B929495 : Blo 550806 929495 := bstep (se 1 (by rfl) ⟨697121, by rfl⟩ : syracuseStep 929495 = 1394243) B1394243
theorem B831191 : Blo 550806 831191 := bstep (se 1 (by rfl) ⟨623393, by rfl⟩ : syracuseStep 831191 = 1246787) B1246787
theorem B5385989 : Blo 550806 5385989 := bstep (se 4 (by rfl) ⟨504936, by rfl⟩ : syracuseStep 5385989 = 1009873) B1009873
theorem B831257 : Blo 550806 831257 := bstep (se 2 (by rfl) ⟨311721, by rfl⟩ : syracuseStep 831257 = 623443) B623443
theorem B929623 : Blo 550806 929623 := bstep (se 1 (by rfl) ⟨697217, by rfl⟩ : syracuseStep 929623 = 1394435) B1394435
theorem B831371 : Blo 550806 831371 := bstep (se 1 (by rfl) ⟨623528, by rfl⟩ : syracuseStep 831371 = 1247057) B1247057
theorem B831383 : Blo 550806 831383 := bstep (se 1 (by rfl) ⟨623537, by rfl⟩ : syracuseStep 831383 = 1247075) B1247075
theorem B831449 : Blo 550806 831449 := bstep (se 2 (by rfl) ⟨311793, by rfl⟩ : syracuseStep 831449 = 623587) B623587
theorem B700427 : Blo 550806 700427 := bstep (se 1 (by rfl) ⟨525320, by rfl⟩ : syracuseStep 700427 = 1050641) B1050641
theorem B831563 : Blo 550806 831563 := bstep (se 1 (by rfl) ⟨623672, by rfl⟩ : syracuseStep 831563 = 1247345) B1247345
theorem B831575 : Blo 550806 831575 := bstep (se 1 (by rfl) ⟨623681, by rfl⟩ : syracuseStep 831575 = 1247363) B1247363
theorem B5320835 : Blo 550806 5320835 := bstep (se 1 (by rfl) ⟨3990626, by rfl⟩ : syracuseStep 5320835 = 7981253) B7981253
theorem B831641 : Blo 550806 831641 := bstep (se 2 (by rfl) ⟨311865, by rfl⟩ : syracuseStep 831641 = 623731) B623731
theorem B831755 : Blo 550806 831755 := bstep (se 1 (by rfl) ⟨623816, by rfl⟩ : syracuseStep 831755 = 1247633) B1247633
theorem B831767 : Blo 550806 831767 := bstep (se 1 (by rfl) ⟨623825, by rfl⟩ : syracuseStep 831767 = 1247651) B1247651
theorem B831833 : Blo 550806 831833 := bstep (se 2 (by rfl) ⟨311937, by rfl⟩ : syracuseStep 831833 = 623875) B623875
theorem B930251 : Blo 550806 930251 := bstep (se 1 (by rfl) ⟨697688, by rfl⟩ : syracuseStep 930251 = 1395377) B1395377
theorem B831947 : Blo 550806 831947 := bstep (se 1 (by rfl) ⟨623960, by rfl⟩ : syracuseStep 831947 = 1247921) B1247921
theorem B831959 : Blo 550806 831959 := bstep (se 1 (by rfl) ⟨623969, by rfl⟩ : syracuseStep 831959 = 1247939) B1247939
theorem B5321177 : Blo 550806 5321177 := bstep (se 2 (by rfl) ⟨1995441, by rfl⟩ : syracuseStep 5321177 = 3990883) B3990883
theorem B832025 : Blo 550806 832025 := bstep (se 2 (by rfl) ⟨312009, by rfl⟩ : syracuseStep 832025 = 624019) B624019
theorem B995905 : Blo 550806 995905 := bstep (se 2 (by rfl) ⟨373464, by rfl⟩ : syracuseStep 995905 = 746929) B746929
theorem B3551809 : Blo 550806 3551809 := bstep (se 2 (by rfl) ⟨1331928, by rfl⟩ : syracuseStep 3551809 = 2663857) B2663857
theorem B930379 : Blo 550806 930379 := bstep (se 1 (by rfl) ⟨697784, by rfl⟩ : syracuseStep 930379 = 1395569) B1395569
theorem B799321 : Blo 550806 799321 := bstep (se 2 (by rfl) ⟨299745, by rfl⟩ : syracuseStep 799321 = 599491) B599491
theorem B3158621 : Blo 550806 3158621 := bstep (se 3 (by rfl) ⟨592241, by rfl⟩ : syracuseStep 3158621 = 1184483) B1184483
theorem B832139 : Blo 550806 832139 := bstep (se 1 (by rfl) ⟨624104, by rfl⟩ : syracuseStep 832139 = 1248209) B1248209
theorem B832151 : Blo 550806 832151 := bstep (se 1 (by rfl) ⟨624113, by rfl⟩ : syracuseStep 832151 = 1248227) B1248227
theorem B701131 : Blo 550806 701131 := bstep (se 1 (by rfl) ⟨525848, by rfl⟩ : syracuseStep 701131 = 1051697) B1051697
theorem B930521 : Blo 550806 930521 := bstep (se 2 (by rfl) ⟨348945, by rfl⟩ : syracuseStep 930521 = 697891) B697891
theorem B9679621 : Blo 550806 9679621 := bstep (se 4 (by rfl) ⟨907464, by rfl⟩ : syracuseStep 9679621 = 1814929) B1814929
theorem B930649 : Blo 550806 930649 := bstep (se 2 (by rfl) ⟨348993, by rfl⟩ : syracuseStep 930649 = 697987) B697987
theorem B701399 : Blo 550806 701399 := bstep (se 1 (by rfl) ⟨526049, by rfl⟩ : syracuseStep 701399 = 1052099) B1052099
theorem B1324183 : Blo 550806 1324183 := bstep (se 1 (by rfl) ⟨993137, by rfl⟩ : syracuseStep 1324183 = 1986275) B1986275
theorem B4732121 : Blo 550806 4732121 := bstep (se 2 (by rfl) ⟨1774545, by rfl⟩ : syracuseStep 4732121 = 3549091) B3549091
theorem B996619 : Blo 550806 996619 := bstep (se 1 (by rfl) ⟨747464, by rfl⟩ : syracuseStep 996619 = 1494929) B1494929
theorem B931223 : Blo 550806 931223 := bstep (se 1 (by rfl) ⟨698417, by rfl⟩ : syracuseStep 931223 = 1396835) B1396835
theorem B1062359 : Blo 550806 1062359 := bstep (se 1 (by rfl) ⟨796769, by rfl⟩ : syracuseStep 1062359 = 1593539) B1593539
theorem B931351 : Blo 550806 931351 := bstep (se 1 (by rfl) ⟨698513, by rfl⟩ : syracuseStep 931351 = 1397027) B1397027
theorem B2799197 : Blo 550806 2799197 := bstep (se 3 (by rfl) ⟨524849, by rfl⟩ : syracuseStep 2799197 = 1049699) B1049699
theorem B702103 : Blo 550806 702103 := bstep (se 1 (by rfl) ⟨526577, by rfl⟩ : syracuseStep 702103 = 1053155) B1053155
theorem B997427 : Blo 550806 997427 := bstep (se 1 (by rfl) ⟨748070, by rfl⟩ : syracuseStep 997427 = 1496141) B1496141
theorem B1685555 : Blo 550806 1685555 := bstep (se 1 (by rfl) ⟨1264166, by rfl⟩ : syracuseStep 1685555 = 2528333) B2528333
theorem B931979 : Blo 550806 931979 := bstep (se 1 (by rfl) ⟨698984, by rfl⟩ : syracuseStep 931979 = 1397969) B1397969
theorem B932107 : Blo 550806 932107 := bstep (se 1 (by rfl) ⟨699080, by rfl⟩ : syracuseStep 932107 = 1398161) B1398161
theorem B932249 : Blo 550806 932249 := bstep (se 2 (by rfl) ⟨349593, by rfl⟩ : syracuseStep 932249 = 699187) B699187
theorem B932377 : Blo 550806 932377 := bstep (se 2 (by rfl) ⟨349641, by rfl⟩ : syracuseStep 932377 = 699283) B699283
theorem B9812515 : Blo 550806 9812515 := bstep (se 1 (by rfl) ⟨7359386, by rfl⟩ : syracuseStep 9812515 = 14718773) B14718773
theorem B4209245 : Blo 550806 4209245 := bstep (se 3 (by rfl) ⟨789233, by rfl⟩ : syracuseStep 4209245 = 1578467) B1578467
theorem B10074775 : Blo 550806 10074775 := bstep (se 1 (by rfl) ⟨7556081, by rfl⟩ : syracuseStep 10074775 = 15112163) B15112163
theorem B9452213 : Blo 550806 9452213 := bstep (se 5 (by rfl) ⟨443072, by rfl⟩ : syracuseStep 9452213 = 886145) B886145
theorem B4733761 : Blo 550806 4733761 := bstep (se 2 (by rfl) ⟨1775160, by rfl⟩ : syracuseStep 4733761 = 3550321) B3550321
theorem B3980249 : Blo 550806 3980249 := bstep (se 2 (by rfl) ⟨1492593, by rfl⟩ : syracuseStep 3980249 = 2985187) B2985187
theorem B932951 : Blo 550806 932951 := bstep (se 1 (by rfl) ⟨699713, by rfl⟩ : syracuseStep 932951 = 1399427) B1399427
theorem B933079 : Blo 550806 933079 := bstep (se 1 (by rfl) ⟨699809, by rfl⟩ : syracuseStep 933079 = 1399619) B1399619
theorem B2801303 : Blo 550806 2801303 := bstep (se 1 (by rfl) ⟨2100977, by rfl⟩ : syracuseStep 2801303 = 4201955) B4201955
theorem B3358529 : Blo 550806 3358529 := bstep (se 2 (by rfl) ⟨1259448, by rfl⟩ : syracuseStep 3358529 = 2518897) B2518897
theorem B7094081 : Blo 550806 7094081 := bstep (se 2 (by rfl) ⟨2660280, by rfl⟩ : syracuseStep 7094081 = 5320561) B5320561
theorem B933707 : Blo 550806 933707 := bstep (se 1 (by rfl) ⟨700280, by rfl⟩ : syracuseStep 933707 = 1400561) B1400561
theorem B999307 : Blo 550806 999307 := bstep (se 1 (by rfl) ⟨749480, by rfl⟩ : syracuseStep 999307 = 1498961) B1498961
theorem B933835 : Blo 550806 933835 := bstep (se 1 (by rfl) ⟨700376, by rfl⟩ : syracuseStep 933835 = 1400753) B1400753
theorem B933977 : Blo 550806 933977 := bstep (se 2 (by rfl) ⟨350241, by rfl⟩ : syracuseStep 933977 = 700483) B700483
theorem B1622209 : Blo 550806 1622209 := bstep (se 2 (by rfl) ⟨608328, by rfl⟩ : syracuseStep 1622209 = 1216657) B1216657
theorem B934105 : Blo 550806 934105 := bstep (se 2 (by rfl) ⟨350289, by rfl⟩ : syracuseStep 934105 = 700579) B700579
theorem B5030237 : Blo 550806 5030237 := bstep (se 3 (by rfl) ⟨943169, by rfl⟩ : syracuseStep 5030237 = 1886339) B1886339
theorem B9060707 : Blo 550806 9060707 := bstep (se 1 (by rfl) ⟨6795530, by rfl⟩ : syracuseStep 9060707 = 13591061) B13591061
theorem B2245265 : Blo 550806 2245265 := bstep (se 2 (by rfl) ⟨841974, by rfl⟩ : syracuseStep 2245265 = 1683949) B1683949
theorem B1262231 : Blo 550806 1262231 := bstep (se 1 (by rfl) ⟨946673, by rfl⟩ : syracuseStep 1262231 = 1893347) B1893347
theorem B934679 : Blo 550806 934679 := bstep (se 1 (by rfl) ⟨701009, by rfl⟩ : syracuseStep 934679 = 1402019) B1402019
theorem B2245427 : Blo 550806 2245427 := bstep (se 1 (by rfl) ⟨1684070, by rfl⟩ : syracuseStep 2245427 = 3368141) B3368141
theorem B3031901 : Blo 550806 3031901 := bstep (se 3 (by rfl) ⟨568481, by rfl⟩ : syracuseStep 3031901 = 1136963) B1136963
theorem B934807 : Blo 550806 934807 := bstep (se 1 (by rfl) ⟨701105, by rfl⟩ : syracuseStep 934807 = 1402211) B1402211
theorem B1197337 : Blo 550806 1197337 := bstep (se 2 (by rfl) ⟨449001, by rfl⟩ : syracuseStep 1197337 = 898003) B898003
theorem B1328449 : Blo 550806 1328449 := bstep (se 2 (by rfl) ⟨498168, by rfl⟩ : syracuseStep 1328449 = 996337) B996337
theorem B935435 : Blo 550806 935435 := bstep (se 1 (by rfl) ⟨701576, by rfl⟩ : syracuseStep 935435 = 1403153) B1403153
theorem B1263179 : Blo 550806 1263179 := bstep (se 1 (by rfl) ⟨947384, by rfl⟩ : syracuseStep 1263179 = 1894769) B1894769
theorem B3884645 : Blo 550806 3884645 := bstep (se 4 (by rfl) ⟨364185, by rfl⟩ : syracuseStep 3884645 = 728371) B728371
theorem B935563 : Blo 550806 935563 := bstep (se 1 (by rfl) ⟨701672, by rfl⟩ : syracuseStep 935563 = 1403345) B1403345
theorem B1394455 : Blo 550806 1394455 := bstep (se 1 (by rfl) ⟨1045841, by rfl⟩ : syracuseStep 1394455 = 2091683) B2091683
theorem B935705 : Blo 550806 935705 := bstep (se 2 (by rfl) ⟨350889, by rfl⟩ : syracuseStep 935705 = 701779) B701779
theorem B2246545 : Blo 550806 2246545 := bstep (se 2 (by rfl) ⟨842454, by rfl⟩ : syracuseStep 2246545 = 1684909) B1684909
theorem B935833 : Blo 550806 935833 := bstep (se 2 (by rfl) ⟨350937, by rfl⟩ : syracuseStep 935833 = 701875) B701875
theorem B1198169 : Blo 550806 1198169 := bstep (se 2 (by rfl) ⟨449313, by rfl⟩ : syracuseStep 1198169 = 898627) B898627
theorem B1394891 : Blo 550806 1394891 := bstep (se 1 (by rfl) ⟨1046168, by rfl⟩ : syracuseStep 1394891 = 2092337) B2092337
theorem B1067531 : Blo 550806 1067531 := bstep (se 1 (by rfl) ⟨800648, by rfl⟩ : syracuseStep 1067531 = 1601297) B1601297
theorem B1395265 : Blo 550806 1395265 := bstep (se 2 (by rfl) ⟨523224, by rfl⟩ : syracuseStep 1395265 = 1046449) B1046449
theorem B2804867 : Blo 550806 2804867 := bstep (se 1 (by rfl) ⟨2103650, by rfl⟩ : syracuseStep 2804867 = 4207301) B4207301
theorem B1395863 : Blo 550806 1395863 := bstep (se 1 (by rfl) ⟨1046897, by rfl⟩ : syracuseStep 1395863 = 2093795) B2093795
theorem B1592513 : Blo 550806 1592513 := bstep (se 2 (by rfl) ⟨597192, by rfl⟩ : syracuseStep 1592513 = 1194385) B1194385
theorem B1200023 : Blo 550806 1200023 := bstep (se 1 (by rfl) ⟨900017, by rfl⟩ : syracuseStep 1200023 = 1800035) B1800035
theorem B1396673 : Blo 550806 1396673 := bstep (se 2 (by rfl) ⟨523752, by rfl⟩ : syracuseStep 1396673 = 1047505) B1047505
theorem B1397209 : Blo 550806 1397209 := bstep (se 2 (by rfl) ⟨523953, by rfl⟩ : syracuseStep 1397209 = 1047907) B1047907
theorem B4183001 : Blo 550806 4183001 := bstep (se 2 (by rfl) ⟨1568625, by rfl⟩ : syracuseStep 4183001 = 3137251) B3137251
theorem B1135745 : Blo 550806 1135745 := bstep (se 2 (by rfl) ⟨425904, by rfl⟩ : syracuseStep 1135745 = 851809) B851809
theorem B7853429 : Blo 550806 7853429 := bstep (se 5 (by rfl) ⟨368129, by rfl⟩ : syracuseStep 7853429 = 736259) B736259
theorem B841099 : Blo 550806 841099 := bstep (se 1 (by rfl) ⟨630824, by rfl⟩ : syracuseStep 841099 = 1261649) B1261649
theorem B26891747 : Blo 550806 26891747 := bstep (se 1 (by rfl) ⟨20168810, by rfl⟩ : syracuseStep 26891747 = 40337621) B40337621
theorem B1398323 : Blo 550806 1398323 := bstep (se 1 (by rfl) ⟨1048742, by rfl⟩ : syracuseStep 1398323 = 2097485) B2097485
theorem B1496627 : Blo 550806 1496627 := bstep (se 1 (by rfl) ⟨1122470, by rfl⟩ : syracuseStep 1496627 = 2244941) B2244941
theorem B1594973 : Blo 550806 1594973 := bstep (se 3 (by rfl) ⟨299057, by rfl⟩ : syracuseStep 1594973 = 598115) B598115
theorem B3200843 : Blo 550806 3200843 := bstep (se 1 (by rfl) ⟨2400632, by rfl⟩ : syracuseStep 3200843 = 4801265) B4801265
theorem B1398617 : Blo 550806 1398617 := bstep (se 2 (by rfl) ⟨524481, by rfl⟩ : syracuseStep 1398617 = 1048963) B1048963
theorem B2021213 : Blo 550806 2021213 := bstep (se 3 (by rfl) ⟨378977, by rfl⟩ : syracuseStep 2021213 = 757955) B757955
theorem B1595467 : Blo 550806 1595467 := bstep (se 1 (by rfl) ⟨1196600, by rfl⟩ : syracuseStep 1595467 = 2393201) B2393201
theorem B1497523 : Blo 550806 1497523 := bstep (se 1 (by rfl) ⟨1123142, by rfl⟩ : syracuseStep 1497523 = 2246285) B2246285
theorem B2808593 : Blo 550806 2808593 := bstep (se 2 (by rfl) ⟨1053222, by rfl⟩ : syracuseStep 2808593 = 2106445) B2106445
theorem B1400267 : Blo 550806 1400267 := bstep (se 1 (by rfl) ⟨1050200, by rfl⟩ : syracuseStep 1400267 = 2100401) B2100401
theorem B3137069 : Blo 550806 3137069 := bstep (se 3 (by rfl) ⟨588200, by rfl⟩ : syracuseStep 3137069 = 1176401) B1176401
theorem B1859165 : Blo 550806 1859165 := bstep (se 3 (by rfl) ⟨348593, by rfl⟩ : syracuseStep 1859165 = 697187) B697187
theorem B93184277 : Blo 550806 93184277 := bstep (se 6 (by rfl) ⟨2184006, by rfl⟩ : syracuseStep 93184277 = 4368013) B4368013
theorem B4186403 : Blo 550806 4186403 := bstep (se 1 (by rfl) ⟨3139802, by rfl⟩ : syracuseStep 4186403 = 6279605) B6279605
theorem B1401239 : Blo 550806 1401239 := bstep (se 1 (by rfl) ⟨1050929, by rfl⟩ : syracuseStep 1401239 = 2101859) B2101859
theorem B1991233 : Blo 550806 1991233 := bstep (se 2 (by rfl) ⟨746712, by rfl⟩ : syracuseStep 1991233 = 1493425) B1493425
theorem B3990167 : Blo 550806 3990167 := bstep (se 1 (by rfl) ⟨2992625, by rfl⟩ : syracuseStep 3990167 = 5985251) B5985251
theorem B1860299 : Blo 550806 1860299 := bstep (se 1 (by rfl) ⟨1395224, by rfl⟩ : syracuseStep 1860299 = 2790449) B2790449
theorem B6710195 : Blo 550806 6710195 := bstep (se 1 (by rfl) ⟨5032646, by rfl⟩ : syracuseStep 6710195 = 10065293) B10065293
theorem B1860569 : Blo 550806 1860569 := bstep (se 2 (by rfl) ⟨697713, by rfl⟩ : syracuseStep 1860569 = 1395427) B1395427
theorem B2548739 : Blo 550806 2548739 := bstep (se 1 (by rfl) ⟨1911554, by rfl⟩ : syracuseStep 2548739 = 3823109) B3823109
theorem B1401907 : Blo 550806 1401907 := bstep (se 1 (by rfl) ⟨1051430, by rfl⟩ : syracuseStep 1401907 = 2102861) B2102861
theorem B877643 : Blo 550806 877643 := bstep (se 1 (by rfl) ⟨658232, by rfl⟩ : syracuseStep 877643 = 1316465) B1316465
theorem B3531869 : Blo 550806 3531869 := bstep (se 3 (by rfl) ⟨662225, by rfl⟩ : syracuseStep 3531869 = 1324451) B1324451
theorem B7070813 : Blo 550806 7070813 := bstep (se 3 (by rfl) ⟨1325777, by rfl⟩ : syracuseStep 7070813 = 2651555) B2651555
theorem B746647 : Blo 550806 746647 := bstep (se 1 (by rfl) ⟨559985, by rfl⟩ : syracuseStep 746647 = 1119971) B1119971
theorem B1402049 : Blo 550806 1402049 := bstep (se 2 (by rfl) ⟨525768, by rfl⟩ : syracuseStep 1402049 = 1051537) B1051537
theorem B1991897 : Blo 550806 1991897 := bstep (se 2 (by rfl) ⟨746961, by rfl⟩ : syracuseStep 1991897 = 1493923) B1493923
theorem B6743569 : Blo 550806 6743569 := bstep (se 2 (by rfl) ⟨2528838, by rfl⟩ : syracuseStep 6743569 = 5057677) B5057677
theorem B6448733 : Blo 550806 6448733 := bstep (se 3 (by rfl) ⟨1209137, by rfl⟩ : syracuseStep 6448733 = 2418275) B2418275
theorem B1861271 : Blo 550806 1861271 := bstep (se 1 (by rfl) ⟨1395953, by rfl⟩ : syracuseStep 1861271 = 2791907) B2791907
theorem B550807 : Blo 550806 550807 := bstep (se 1 (by rfl) ⟨413105, by rfl⟩ : syracuseStep 550807 = 826211) B826211
theorem B550827 : Blo 550806 550827 := bstep (se 1 (by rfl) ⟨413120, by rfl⟩ : syracuseStep 550827 = 826241) B826241
theorem B550839 : Blo 550806 550839 := bstep (se 1 (by rfl) ⟨413129, by rfl⟩ : syracuseStep 550839 = 826259) B826259
theorem B550859 : Blo 550806 550859 := bstep (se 1 (by rfl) ⟨413144, by rfl⟩ : syracuseStep 550859 = 826289) B826289
theorem B550871 : Blo 550806 550871 := bstep (se 1 (by rfl) ⟨413153, by rfl⟩ : syracuseStep 550871 = 826307) B826307
theorem B550891 : Blo 550806 550891 := bstep (se 1 (by rfl) ⟨413168, by rfl⟩ : syracuseStep 550891 = 826337) B826337
theorem B550903 : Blo 550806 550903 := bstep (se 1 (by rfl) ⟨413177, by rfl⟩ : syracuseStep 550903 = 826355) B826355
theorem B550923 : Blo 550806 550923 := bstep (se 1 (by rfl) ⟨413192, by rfl⟩ : syracuseStep 550923 = 826385) B826385
theorem B550935 : Blo 550806 550935 := bstep (se 1 (by rfl) ⟨413201, by rfl⟩ : syracuseStep 550935 = 826403) B826403
theorem B550955 : Blo 550806 550955 := bstep (se 1 (by rfl) ⟨413216, by rfl⟩ : syracuseStep 550955 = 826433) B826433
theorem B550967 : Blo 550806 550967 := bstep (se 1 (by rfl) ⟨413225, by rfl⟩ : syracuseStep 550967 = 826451) B826451
theorem B550987 : Blo 550806 550987 := bstep (se 1 (by rfl) ⟨413240, by rfl⟩ : syracuseStep 550987 = 826481) B826481
theorem B550999 : Blo 550806 550999 := bstep (se 1 (by rfl) ⟨413249, by rfl⟩ : syracuseStep 550999 = 826499) B826499
theorem B551019 : Blo 550806 551019 := bstep (se 1 (by rfl) ⟨413264, by rfl⟩ : syracuseStep 551019 = 826529) B826529
theorem B551031 : Blo 550806 551031 := bstep (se 1 (by rfl) ⟨413273, by rfl⟩ : syracuseStep 551031 = 826547) B826547
theorem B551051 : Blo 550806 551051 := bstep (se 1 (by rfl) ⟨413288, by rfl⟩ : syracuseStep 551051 = 826577) B826577
theorem B5957783 : Blo 550806 5957783 := bstep (se 1 (by rfl) ⟨4468337, by rfl⟩ : syracuseStep 5957783 = 8936675) B8936675
theorem B551063 : Blo 550806 551063 := bstep (se 1 (by rfl) ⟨413297, by rfl⟩ : syracuseStep 551063 = 826595) B826595
theorem B551083 : Blo 550806 551083 := bstep (se 1 (by rfl) ⟨413312, by rfl⟩ : syracuseStep 551083 = 826625) B826625
theorem B1861811 : Blo 550806 1861811 := bstep (se 1 (by rfl) ⟨1396358, by rfl⟩ : syracuseStep 1861811 = 2792717) B2792717
theorem B551095 : Blo 550806 551095 := bstep (se 1 (by rfl) ⟨413321, by rfl⟩ : syracuseStep 551095 = 826643) B826643
theorem B551115 : Blo 550806 551115 := bstep (se 1 (by rfl) ⟨413336, by rfl⟩ : syracuseStep 551115 = 826673) B826673
theorem B551127 : Blo 550806 551127 := bstep (se 1 (by rfl) ⟨413345, by rfl⟩ : syracuseStep 551127 = 826691) B826691
theorem B551147 : Blo 550806 551147 := bstep (se 1 (by rfl) ⟨413360, by rfl⟩ : syracuseStep 551147 = 826721) B826721
theorem B551159 : Blo 550806 551159 := bstep (se 1 (by rfl) ⟨413369, by rfl⟩ : syracuseStep 551159 = 826739) B826739
theorem B551179 : Blo 550806 551179 := bstep (se 1 (by rfl) ⟨413384, by rfl⟩ : syracuseStep 551179 = 826769) B826769
theorem B551191 : Blo 550806 551191 := bstep (se 1 (by rfl) ⟨413393, by rfl⟩ : syracuseStep 551191 = 826787) B826787
theorem B551211 : Blo 550806 551211 := bstep (se 1 (by rfl) ⟨413408, by rfl⟩ : syracuseStep 551211 = 826817) B826817
theorem B551223 : Blo 550806 551223 := bstep (se 1 (by rfl) ⟨413417, by rfl⟩ : syracuseStep 551223 = 826835) B826835
theorem B1239371 : Blo 550806 1239371 := bstep (se 1 (by rfl) ⟨929528, by rfl⟩ : syracuseStep 1239371 = 1859057) B1859057
theorem B551243 : Blo 550806 551243 := bstep (se 1 (by rfl) ⟨413432, by rfl⟩ : syracuseStep 551243 = 826865) B826865
theorem B551255 : Blo 550806 551255 := bstep (se 1 (by rfl) ⟨413441, by rfl⟩ : syracuseStep 551255 = 826883) B826883
theorem B551275 : Blo 550806 551275 := bstep (se 1 (by rfl) ⟨413456, by rfl⟩ : syracuseStep 551275 = 826913) B826913
theorem B551287 : Blo 550806 551287 := bstep (se 1 (by rfl) ⟨413465, by rfl⟩ : syracuseStep 551287 = 826931) B826931
theorem B1239425 : Blo 550806 1239425 := bstep (se 2 (by rfl) ⟨464784, by rfl⟩ : syracuseStep 1239425 = 929569) B929569
theorem B551307 : Blo 550806 551307 := bstep (se 1 (by rfl) ⟨413480, by rfl⟩ : syracuseStep 551307 = 826961) B826961
theorem B551319 : Blo 550806 551319 := bstep (se 1 (by rfl) ⟨413489, by rfl⟩ : syracuseStep 551319 = 826979) B826979
theorem B551339 : Blo 550806 551339 := bstep (se 1 (by rfl) ⟨413504, by rfl⟩ : syracuseStep 551339 = 827009) B827009
theorem B1403315 : Blo 550806 1403315 := bstep (se 1 (by rfl) ⟨1052486, by rfl⟩ : syracuseStep 1403315 = 2104973) B2104973
theorem B551351 : Blo 550806 551351 := bstep (se 1 (by rfl) ⟨413513, by rfl⟩ : syracuseStep 551351 = 827027) B827027
theorem B1862081 : Blo 550806 1862081 := bstep (se 2 (by rfl) ⟨698280, by rfl⟩ : syracuseStep 1862081 = 1396561) B1396561
theorem B551371 : Blo 550806 551371 := bstep (se 1 (by rfl) ⟨413528, by rfl⟩ : syracuseStep 551371 = 827057) B827057
theorem B551383 : Blo 550806 551383 := bstep (se 1 (by rfl) ⟨413537, by rfl⟩ : syracuseStep 551383 = 827075) B827075
theorem B551403 : Blo 550806 551403 := bstep (se 1 (by rfl) ⟨413552, by rfl⟩ : syracuseStep 551403 = 827105) B827105
theorem B551415 : Blo 550806 551415 := bstep (se 1 (by rfl) ⟨413561, by rfl⟩ : syracuseStep 551415 = 827123) B827123
theorem B551435 : Blo 550806 551435 := bstep (se 1 (by rfl) ⟨413576, by rfl⟩ : syracuseStep 551435 = 827153) B827153
theorem B551447 : Blo 550806 551447 := bstep (se 1 (by rfl) ⟨413585, by rfl⟩ : syracuseStep 551447 = 827171) B827171
theorem B551467 : Blo 550806 551467 := bstep (se 1 (by rfl) ⟨413600, by rfl⟩ : syracuseStep 551467 = 827201) B827201
theorem B551479 : Blo 550806 551479 := bstep (se 1 (by rfl) ⟨413609, by rfl⟩ : syracuseStep 551479 = 827219) B827219
theorem B551499 : Blo 550806 551499 := bstep (se 1 (by rfl) ⟨413624, by rfl⟩ : syracuseStep 551499 = 827249) B827249
theorem B551511 : Blo 550806 551511 := bstep (se 1 (by rfl) ⟨413633, by rfl⟩ : syracuseStep 551511 = 827267) B827267
theorem B1239641 : Blo 550806 1239641 := bstep (se 2 (by rfl) ⟨464865, by rfl⟩ : syracuseStep 1239641 = 929731) B929731
theorem B2845277 : Blo 550806 2845277 := bstep (se 3 (by rfl) ⟨533489, by rfl⟩ : syracuseStep 2845277 = 1066979) B1066979
theorem B551531 : Blo 550806 551531 := bstep (se 1 (by rfl) ⟨413648, by rfl⟩ : syracuseStep 551531 = 827297) B827297
theorem B551543 : Blo 550806 551543 := bstep (se 1 (by rfl) ⟨413657, by rfl⟩ : syracuseStep 551543 = 827315) B827315
theorem B551563 : Blo 550806 551563 := bstep (se 1 (by rfl) ⟨413672, by rfl⟩ : syracuseStep 551563 = 827345) B827345
theorem B551575 : Blo 550806 551575 := bstep (se 1 (by rfl) ⟨413681, by rfl⟩ : syracuseStep 551575 = 827363) B827363
theorem B551595 : Blo 550806 551595 := bstep (se 1 (by rfl) ⟨413696, by rfl⟩ : syracuseStep 551595 = 827393) B827393
theorem B1239731 : Blo 550806 1239731 := bstep (se 1 (by rfl) ⟨929798, by rfl⟩ : syracuseStep 1239731 = 1859597) B1859597
theorem B551607 : Blo 550806 551607 := bstep (se 1 (by rfl) ⟨413705, by rfl⟩ : syracuseStep 551607 = 827411) B827411
theorem B551627 : Blo 550806 551627 := bstep (se 1 (by rfl) ⟨413720, by rfl⟩ : syracuseStep 551627 = 827441) B827441
theorem B1239767 : Blo 550806 1239767 := bstep (se 1 (by rfl) ⟨929825, by rfl⟩ : syracuseStep 1239767 = 1859651) B1859651
theorem B551639 : Blo 550806 551639 := bstep (se 1 (by rfl) ⟨413729, by rfl⟩ : syracuseStep 551639 = 827459) B827459
theorem B551659 : Blo 550806 551659 := bstep (se 1 (by rfl) ⟨413744, by rfl⟩ : syracuseStep 551659 = 827489) B827489
theorem B551671 : Blo 550806 551671 := bstep (se 1 (by rfl) ⟨413753, by rfl⟩ : syracuseStep 551671 = 827507) B827507
theorem B551691 : Blo 550806 551691 := bstep (se 1 (by rfl) ⟨413768, by rfl⟩ : syracuseStep 551691 = 827537) B827537
theorem B551703 : Blo 550806 551703 := bstep (se 1 (by rfl) ⟨413777, by rfl⟩ : syracuseStep 551703 = 827555) B827555
theorem B551723 : Blo 550806 551723 := bstep (se 1 (by rfl) ⟨413792, by rfl⟩ : syracuseStep 551723 = 827585) B827585
theorem B551735 : Blo 550806 551735 := bstep (se 1 (by rfl) ⟨413801, by rfl⟩ : syracuseStep 551735 = 827603) B827603
theorem B2091851 : Blo 550806 2091851 := bstep (se 1 (by rfl) ⟨1568888, by rfl⟩ : syracuseStep 2091851 = 3137777) B3137777
theorem B551755 : Blo 550806 551755 := bstep (se 1 (by rfl) ⟨413816, by rfl⟩ : syracuseStep 551755 = 827633) B827633
theorem B551767 : Blo 550806 551767 := bstep (se 1 (by rfl) ⟨413825, by rfl⟩ : syracuseStep 551767 = 827651) B827651
theorem B2091865 : Blo 550806 2091865 := bstep (se 2 (by rfl) ⟨784449, by rfl⟩ : syracuseStep 2091865 = 1568899) B1568899
theorem B551787 : Blo 550806 551787 := bstep (se 1 (by rfl) ⟨413840, by rfl⟩ : syracuseStep 551787 = 827681) B827681
theorem B551799 : Blo 550806 551799 := bstep (se 1 (by rfl) ⟨413849, by rfl⟩ : syracuseStep 551799 = 827699) B827699
theorem B1239947 : Blo 550806 1239947 := bstep (se 1 (by rfl) ⟨929960, by rfl⟩ : syracuseStep 1239947 = 1859921) B1859921
theorem B551819 : Blo 550806 551819 := bstep (se 1 (by rfl) ⟨413864, by rfl⟩ : syracuseStep 551819 = 827729) B827729
theorem B551831 : Blo 550806 551831 := bstep (se 1 (by rfl) ⟨413873, by rfl⟩ : syracuseStep 551831 = 827747) B827747
theorem B551851 : Blo 550806 551851 := bstep (se 1 (by rfl) ⟨413888, by rfl⟩ : syracuseStep 551851 = 827777) B827777
theorem B551863 : Blo 550806 551863 := bstep (se 1 (by rfl) ⟨413897, by rfl⟩ : syracuseStep 551863 = 827795) B827795
theorem B1240001 : Blo 550806 1240001 := bstep (se 2 (by rfl) ⟨465000, by rfl⟩ : syracuseStep 1240001 = 930001) B930001
theorem B551883 : Blo 550806 551883 := bstep (se 1 (by rfl) ⟨413912, by rfl⟩ : syracuseStep 551883 = 827825) B827825
theorem B1403851 : Blo 550806 1403851 := bstep (se 1 (by rfl) ⟨1052888, by rfl⟩ : syracuseStep 1403851 = 2105777) B2105777
theorem B551895 : Blo 550806 551895 := bstep (se 1 (by rfl) ⟨413921, by rfl⟩ : syracuseStep 551895 = 827843) B827843
theorem B1862621 : Blo 550806 1862621 := bstep (se 3 (by rfl) ⟨349241, by rfl⟩ : syracuseStep 1862621 = 698483) B698483
theorem B551915 : Blo 550806 551915 := bstep (se 1 (by rfl) ⟨413936, by rfl⟩ : syracuseStep 551915 = 827873) B827873
theorem B551927 : Blo 550806 551927 := bstep (se 1 (by rfl) ⟨413945, by rfl⟩ : syracuseStep 551927 = 827891) B827891
theorem B551947 : Blo 550806 551947 := bstep (se 1 (by rfl) ⟨413960, by rfl⟩ : syracuseStep 551947 = 827921) B827921
theorem B551959 : Blo 550806 551959 := bstep (se 1 (by rfl) ⟨413969, by rfl⟩ : syracuseStep 551959 = 827939) B827939
theorem B551979 : Blo 550806 551979 := bstep (se 1 (by rfl) ⟨413984, by rfl⟩ : syracuseStep 551979 = 827969) B827969
theorem B551991 : Blo 550806 551991 := bstep (se 1 (by rfl) ⟨413993, by rfl⟩ : syracuseStep 551991 = 827987) B827987
theorem B552011 : Blo 550806 552011 := bstep (se 1 (by rfl) ⟨414008, by rfl⟩ : syracuseStep 552011 = 828017) B828017
theorem B552023 : Blo 550806 552023 := bstep (se 1 (by rfl) ⟨414017, by rfl⟩ : syracuseStep 552023 = 828035) B828035
theorem B1403993 : Blo 550806 1403993 := bstep (se 2 (by rfl) ⟨526497, by rfl⟩ : syracuseStep 1403993 = 1052995) B1052995
theorem B552043 : Blo 550806 552043 := bstep (se 1 (by rfl) ⟨414032, by rfl⟩ : syracuseStep 552043 = 828065) B828065
theorem B552055 : Blo 550806 552055 := bstep (se 1 (by rfl) ⟨414041, by rfl⟩ : syracuseStep 552055 = 828083) B828083
theorem B552075 : Blo 550806 552075 := bstep (se 1 (by rfl) ⟨414056, by rfl⟩ : syracuseStep 552075 = 828113) B828113
theorem B552087 : Blo 550806 552087 := bstep (se 1 (by rfl) ⟨414065, by rfl⟩ : syracuseStep 552087 = 828131) B828131
theorem B1240217 : Blo 550806 1240217 := bstep (se 2 (by rfl) ⟨465081, by rfl⟩ : syracuseStep 1240217 = 930163) B930163
theorem B552107 : Blo 550806 552107 := bstep (se 1 (by rfl) ⟨414080, by rfl⟩ : syracuseStep 552107 = 828161) B828161
theorem B552119 : Blo 550806 552119 := bstep (se 1 (by rfl) ⟨414089, by rfl⟩ : syracuseStep 552119 = 828179) B828179
theorem B552139 : Blo 550806 552139 := bstep (se 1 (by rfl) ⟨414104, by rfl⟩ : syracuseStep 552139 = 828209) B828209
theorem B552151 : Blo 550806 552151 := bstep (se 1 (by rfl) ⟨414113, by rfl⟩ : syracuseStep 552151 = 828227) B828227
theorem B552171 : Blo 550806 552171 := bstep (se 1 (by rfl) ⟨414128, by rfl⟩ : syracuseStep 552171 = 828257) B828257
theorem B1240307 : Blo 550806 1240307 := bstep (se 1 (by rfl) ⟨930230, by rfl⟩ : syracuseStep 1240307 = 1860461) B1860461
theorem B552183 : Blo 550806 552183 := bstep (se 1 (by rfl) ⟨414137, by rfl⟩ : syracuseStep 552183 = 828275) B828275
theorem B552203 : Blo 550806 552203 := bstep (se 1 (by rfl) ⟨414152, by rfl⟩ : syracuseStep 552203 = 828305) B828305
theorem B1240343 : Blo 550806 1240343 := bstep (se 1 (by rfl) ⟨930257, by rfl⟩ : syracuseStep 1240343 = 1860515) B1860515
theorem B552215 : Blo 550806 552215 := bstep (se 1 (by rfl) ⟨414161, by rfl⟩ : syracuseStep 552215 = 828323) B828323
theorem B552235 : Blo 550806 552235 := bstep (se 1 (by rfl) ⟨414176, by rfl⟩ : syracuseStep 552235 = 828353) B828353
theorem B552247 : Blo 550806 552247 := bstep (se 1 (by rfl) ⟨414185, by rfl⟩ : syracuseStep 552247 = 828371) B828371
theorem B552267 : Blo 550806 552267 := bstep (se 1 (by rfl) ⟨414200, by rfl⟩ : syracuseStep 552267 = 828401) B828401
theorem B552279 : Blo 550806 552279 := bstep (se 1 (by rfl) ⟨414209, by rfl⟩ : syracuseStep 552279 = 828419) B828419
theorem B552299 : Blo 550806 552299 := bstep (se 1 (by rfl) ⟨414224, by rfl⟩ : syracuseStep 552299 = 828449) B828449
theorem B552311 : Blo 550806 552311 := bstep (se 1 (by rfl) ⟨414233, by rfl⟩ : syracuseStep 552311 = 828467) B828467
theorem B552331 : Blo 550806 552331 := bstep (se 1 (by rfl) ⟨414248, by rfl⟩ : syracuseStep 552331 = 828497) B828497
theorem B552343 : Blo 550806 552343 := bstep (se 1 (by rfl) ⟨414257, by rfl⟩ : syracuseStep 552343 = 828515) B828515
theorem B552363 : Blo 550806 552363 := bstep (se 1 (by rfl) ⟨414272, by rfl⟩ : syracuseStep 552363 = 828545) B828545
theorem B552375 : Blo 550806 552375 := bstep (se 1 (by rfl) ⟨414281, by rfl⟩ : syracuseStep 552375 = 828563) B828563
theorem B1240523 : Blo 550806 1240523 := bstep (se 1 (by rfl) ⟨930392, by rfl⟩ : syracuseStep 1240523 = 1860785) B1860785
theorem B552395 : Blo 550806 552395 := bstep (se 1 (by rfl) ⟨414296, by rfl⟩ : syracuseStep 552395 = 828593) B828593
theorem B552407 : Blo 550806 552407 := bstep (se 1 (by rfl) ⟨414305, by rfl⟩ : syracuseStep 552407 = 828611) B828611
theorem B552427 : Blo 550806 552427 := bstep (se 1 (by rfl) ⟨414320, by rfl⟩ : syracuseStep 552427 = 828641) B828641
theorem B552439 : Blo 550806 552439 := bstep (se 1 (by rfl) ⟨414329, by rfl⟩ : syracuseStep 552439 = 828659) B828659
theorem B1240577 : Blo 550806 1240577 := bstep (se 2 (by rfl) ⟨465216, by rfl⟩ : syracuseStep 1240577 = 930433) B930433
theorem B552459 : Blo 550806 552459 := bstep (se 1 (by rfl) ⟨414344, by rfl⟩ : syracuseStep 552459 = 828689) B828689
theorem B552471 : Blo 550806 552471 := bstep (se 1 (by rfl) ⟨414353, by rfl⟩ : syracuseStep 552471 = 828707) B828707
theorem B552491 : Blo 550806 552491 := bstep (se 1 (by rfl) ⟨414368, by rfl⟩ : syracuseStep 552491 = 828737) B828737
theorem B552503 : Blo 550806 552503 := bstep (se 1 (by rfl) ⟨414377, by rfl⟩ : syracuseStep 552503 = 828755) B828755
theorem B552523 : Blo 550806 552523 := bstep (se 1 (by rfl) ⟨414392, by rfl⟩ : syracuseStep 552523 = 828785) B828785
theorem B552535 : Blo 550806 552535 := bstep (se 1 (by rfl) ⟨414401, by rfl⟩ : syracuseStep 552535 = 828803) B828803
theorem B1601117 : Blo 550806 1601117 := bstep (se 3 (by rfl) ⟨300209, by rfl⟩ : syracuseStep 1601117 = 600419) B600419
theorem B552555 : Blo 550806 552555 := bstep (se 1 (by rfl) ⟨414416, by rfl⟩ : syracuseStep 552555 = 828833) B828833
theorem B552567 : Blo 550806 552567 := bstep (se 1 (by rfl) ⟨414425, by rfl⟩ : syracuseStep 552567 = 828851) B828851
theorem B552587 : Blo 550806 552587 := bstep (se 1 (by rfl) ⟨414440, by rfl⟩ : syracuseStep 552587 = 828881) B828881
theorem B552599 : Blo 550806 552599 := bstep (se 1 (by rfl) ⟨414449, by rfl⟩ : syracuseStep 552599 = 828899) B828899
theorem B552619 : Blo 550806 552619 := bstep (se 1 (by rfl) ⟨414464, by rfl⟩ : syracuseStep 552619 = 828929) B828929
theorem B552631 : Blo 550806 552631 := bstep (se 1 (by rfl) ⟨414473, by rfl⟩ : syracuseStep 552631 = 828947) B828947
theorem B552651 : Blo 550806 552651 := bstep (se 1 (by rfl) ⟨414488, by rfl⟩ : syracuseStep 552651 = 828977) B828977
theorem B552663 : Blo 550806 552663 := bstep (se 1 (by rfl) ⟨414497, by rfl⟩ : syracuseStep 552663 = 828995) B828995
theorem B1240793 : Blo 550806 1240793 := bstep (se 2 (by rfl) ⟨465297, by rfl⟩ : syracuseStep 1240793 = 930595) B930595
theorem B552683 : Blo 550806 552683 := bstep (se 1 (by rfl) ⟨414512, by rfl⟩ : syracuseStep 552683 = 829025) B829025
theorem B552695 : Blo 550806 552695 := bstep (se 1 (by rfl) ⟨414521, by rfl⟩ : syracuseStep 552695 = 829043) B829043
theorem B552715 : Blo 550806 552715 := bstep (se 1 (by rfl) ⟨414536, by rfl⟩ : syracuseStep 552715 = 829073) B829073
theorem B2092823 : Blo 550806 2092823 := bstep (se 1 (by rfl) ⟨1569617, by rfl⟩ : syracuseStep 2092823 = 3139235) B3139235
theorem B552727 : Blo 550806 552727 := bstep (se 1 (by rfl) ⟨414545, by rfl⟩ : syracuseStep 552727 = 829091) B829091
theorem B1994519 : Blo 550806 1994519 := bstep (se 1 (by rfl) ⟨1495889, by rfl⟩ : syracuseStep 1994519 = 2991779) B2991779
theorem B552747 : Blo 550806 552747 := bstep (se 1 (by rfl) ⟨414560, by rfl⟩ : syracuseStep 552747 = 829121) B829121
theorem B2354989 : Blo 550806 2354989 := bstep (se 3 (by rfl) ⟨441560, by rfl⟩ : syracuseStep 2354989 = 883121) B883121
theorem B3534637 : Blo 550806 3534637 := bstep (se 3 (by rfl) ⟨662744, by rfl⟩ : syracuseStep 3534637 = 1325489) B1325489
theorem B1240883 : Blo 550806 1240883 := bstep (se 1 (by rfl) ⟨930662, by rfl⟩ : syracuseStep 1240883 = 1861325) B1861325
theorem B552759 : Blo 550806 552759 := bstep (se 1 (by rfl) ⟨414569, by rfl⟩ : syracuseStep 552759 = 829139) B829139
theorem B552779 : Blo 550806 552779 := bstep (se 1 (by rfl) ⟨414584, by rfl⟩ : syracuseStep 552779 = 829169) B829169
theorem B1240919 : Blo 550806 1240919 := bstep (se 1 (by rfl) ⟨930689, by rfl⟩ : syracuseStep 1240919 = 1861379) B1861379
theorem B552791 : Blo 550806 552791 := bstep (se 1 (by rfl) ⟨414593, by rfl⟩ : syracuseStep 552791 = 829187) B829187
theorem B552811 : Blo 550806 552811 := bstep (se 1 (by rfl) ⟨414608, by rfl⟩ : syracuseStep 552811 = 829217) B829217
theorem B552823 : Blo 550806 552823 := bstep (se 1 (by rfl) ⟨414617, by rfl⟩ : syracuseStep 552823 = 829235) B829235
theorem B552843 : Blo 550806 552843 := bstep (se 1 (by rfl) ⟨414632, by rfl⟩ : syracuseStep 552843 = 829265) B829265
theorem B1863575 : Blo 550806 1863575 := bstep (se 1 (by rfl) ⟨1397681, by rfl⟩ : syracuseStep 1863575 = 2795363) B2795363
theorem B552855 : Blo 550806 552855 := bstep (se 1 (by rfl) ⟨414641, by rfl⟩ : syracuseStep 552855 = 829283) B829283
theorem B552875 : Blo 550806 552875 := bstep (se 1 (by rfl) ⟨414656, by rfl⟩ : syracuseStep 552875 = 829313) B829313
theorem B552887 : Blo 550806 552887 := bstep (se 1 (by rfl) ⟨414665, by rfl⟩ : syracuseStep 552887 = 829331) B829331
theorem B552907 : Blo 550806 552907 := bstep (se 1 (by rfl) ⟨414680, by rfl⟩ : syracuseStep 552907 = 829361) B829361
theorem B552919 : Blo 550806 552919 := bstep (se 1 (by rfl) ⟨414689, by rfl⟩ : syracuseStep 552919 = 829379) B829379
theorem B552939 : Blo 550806 552939 := bstep (se 1 (by rfl) ⟨414704, by rfl⟩ : syracuseStep 552939 = 829409) B829409
theorem B552951 : Blo 550806 552951 := bstep (se 1 (by rfl) ⟨414713, by rfl⟩ : syracuseStep 552951 = 829427) B829427
theorem B1241099 : Blo 550806 1241099 := bstep (se 1 (by rfl) ⟨930824, by rfl⟩ : syracuseStep 1241099 = 1861649) B1861649
theorem B552971 : Blo 550806 552971 := bstep (se 1 (by rfl) ⟨414728, by rfl⟩ : syracuseStep 552971 = 829457) B829457
theorem B552983 : Blo 550806 552983 := bstep (se 1 (by rfl) ⟨414737, by rfl⟩ : syracuseStep 552983 = 829475) B829475
theorem B553003 : Blo 550806 553003 := bstep (se 1 (by rfl) ⟨414752, by rfl⟩ : syracuseStep 553003 = 829505) B829505
theorem B553015 : Blo 550806 553015 := bstep (se 1 (by rfl) ⟨414761, by rfl⟩ : syracuseStep 553015 = 829523) B829523
theorem B1241153 : Blo 550806 1241153 := bstep (se 2 (by rfl) ⟨465432, by rfl⟩ : syracuseStep 1241153 = 930865) B930865
theorem B1863755 : Blo 550806 1863755 := bstep (se 1 (by rfl) ⟨1397816, by rfl⟩ : syracuseStep 1863755 = 2795633) B2795633
theorem B553035 : Blo 550806 553035 := bstep (se 1 (by rfl) ⟨414776, by rfl⟩ : syracuseStep 553035 = 829553) B829553
theorem B553047 : Blo 550806 553047 := bstep (se 1 (by rfl) ⟨414785, by rfl⟩ : syracuseStep 553047 = 829571) B829571
theorem B553067 : Blo 550806 553067 := bstep (se 1 (by rfl) ⟨414800, by rfl⟩ : syracuseStep 553067 = 829601) B829601
theorem B553079 : Blo 550806 553079 := bstep (se 1 (by rfl) ⟨414809, by rfl⟩ : syracuseStep 553079 = 829619) B829619
theorem B2355331 : Blo 550806 2355331 := bstep (se 1 (by rfl) ⟨1766498, by rfl⟩ : syracuseStep 2355331 = 3532997) B3532997
theorem B553099 : Blo 550806 553099 := bstep (se 1 (by rfl) ⟨414824, by rfl⟩ : syracuseStep 553099 = 829649) B829649
theorem B553111 : Blo 550806 553111 := bstep (se 1 (by rfl) ⟨414833, by rfl⟩ : syracuseStep 553111 = 829667) B829667
theorem B553131 : Blo 550806 553131 := bstep (se 1 (by rfl) ⟨414848, by rfl⟩ : syracuseStep 553131 = 829697) B829697
theorem B553143 : Blo 550806 553143 := bstep (se 1 (by rfl) ⟨414857, by rfl⟩ : syracuseStep 553143 = 829715) B829715
theorem B553163 : Blo 550806 553163 := bstep (se 1 (by rfl) ⟨414872, by rfl⟩ : syracuseStep 553163 = 829745) B829745
theorem B553175 : Blo 550806 553175 := bstep (se 1 (by rfl) ⟨414881, by rfl⟩ : syracuseStep 553175 = 829763) B829763
theorem B553195 : Blo 550806 553195 := bstep (se 1 (by rfl) ⟨414896, by rfl⟩ : syracuseStep 553195 = 829793) B829793
theorem B553207 : Blo 550806 553207 := bstep (se 1 (by rfl) ⟨414905, by rfl⟩ : syracuseStep 553207 = 829811) B829811
theorem B553227 : Blo 550806 553227 := bstep (se 1 (by rfl) ⟨414920, by rfl⟩ : syracuseStep 553227 = 829841) B829841
theorem B553239 : Blo 550806 553239 := bstep (se 1 (by rfl) ⟨414929, by rfl⟩ : syracuseStep 553239 = 829859) B829859
theorem B1241369 : Blo 550806 1241369 := bstep (se 2 (by rfl) ⟨465513, by rfl⟩ : syracuseStep 1241369 = 931027) B931027
theorem B553259 : Blo 550806 553259 := bstep (se 1 (by rfl) ⟨414944, by rfl⟩ : syracuseStep 553259 = 829889) B829889
theorem B553271 : Blo 550806 553271 := bstep (se 1 (by rfl) ⟨414953, by rfl⟩ : syracuseStep 553271 = 829907) B829907
theorem B553291 : Blo 550806 553291 := bstep (se 1 (by rfl) ⟨414968, by rfl⟩ : syracuseStep 553291 = 829937) B829937
theorem B553303 : Blo 550806 553303 := bstep (se 1 (by rfl) ⟨414977, by rfl⟩ : syracuseStep 553303 = 829955) B829955
theorem B1864025 : Blo 550806 1864025 := bstep (se 2 (by rfl) ⟨699009, by rfl⟩ : syracuseStep 1864025 = 1398019) B1398019
theorem B553323 : Blo 550806 553323 := bstep (se 1 (by rfl) ⟨414992, by rfl⟩ : syracuseStep 553323 = 829985) B829985
theorem B1241459 : Blo 550806 1241459 := bstep (se 1 (by rfl) ⟨931094, by rfl⟩ : syracuseStep 1241459 = 1862189) B1862189
theorem B553335 : Blo 550806 553335 := bstep (se 1 (by rfl) ⟨415001, by rfl⟩ : syracuseStep 553335 = 830003) B830003
theorem B553355 : Blo 550806 553355 := bstep (se 1 (by rfl) ⟨415016, by rfl⟩ : syracuseStep 553355 = 830033) B830033
theorem B1241495 : Blo 550806 1241495 := bstep (se 1 (by rfl) ⟨931121, by rfl⟩ : syracuseStep 1241495 = 1862243) B1862243
theorem B553367 : Blo 550806 553367 := bstep (se 1 (by rfl) ⟨415025, by rfl⟩ : syracuseStep 553367 = 830051) B830051
theorem B553387 : Blo 550806 553387 := bstep (se 1 (by rfl) ⟨415040, by rfl⟩ : syracuseStep 553387 = 830081) B830081
theorem B553399 : Blo 550806 553399 := bstep (se 1 (by rfl) ⟨415049, by rfl⟩ : syracuseStep 553399 = 830099) B830099
theorem B553419 : Blo 550806 553419 := bstep (se 1 (by rfl) ⟨415064, by rfl⟩ : syracuseStep 553419 = 830129) B830129
theorem B553431 : Blo 550806 553431 := bstep (se 1 (by rfl) ⟨415073, by rfl⟩ : syracuseStep 553431 = 830147) B830147
theorem B553451 : Blo 550806 553451 := bstep (se 1 (by rfl) ⟨415088, by rfl⟩ : syracuseStep 553451 = 830177) B830177
theorem B553463 : Blo 550806 553463 := bstep (se 1 (by rfl) ⟨415097, by rfl⟩ : syracuseStep 553463 = 830195) B830195
theorem B553483 : Blo 550806 553483 := bstep (se 1 (by rfl) ⟨415112, by rfl⟩ : syracuseStep 553483 = 830225) B830225
theorem B553495 : Blo 550806 553495 := bstep (se 1 (by rfl) ⟨415121, by rfl⟩ : syracuseStep 553495 = 830243) B830243
theorem B553515 : Blo 550806 553515 := bstep (se 1 (by rfl) ⟨415136, by rfl⟩ : syracuseStep 553515 = 830273) B830273
theorem B553527 : Blo 550806 553527 := bstep (se 1 (by rfl) ⟨415145, by rfl⟩ : syracuseStep 553527 = 830291) B830291
theorem B1241675 : Blo 550806 1241675 := bstep (se 1 (by rfl) ⟨931256, by rfl⟩ : syracuseStep 1241675 = 1862513) B1862513
theorem B553547 : Blo 550806 553547 := bstep (se 1 (by rfl) ⟨415160, by rfl⟩ : syracuseStep 553547 = 830321) B830321
theorem B553559 : Blo 550806 553559 := bstep (se 1 (by rfl) ⟨415169, by rfl⟩ : syracuseStep 553559 = 830339) B830339
theorem B553579 : Blo 550806 553579 := bstep (se 1 (by rfl) ⟨415184, by rfl⟩ : syracuseStep 553579 = 830369) B830369
theorem B553591 : Blo 550806 553591 := bstep (se 1 (by rfl) ⟨415193, by rfl⟩ : syracuseStep 553591 = 830387) B830387
theorem B1241729 : Blo 550806 1241729 := bstep (se 2 (by rfl) ⟨465648, by rfl⟩ : syracuseStep 1241729 = 931297) B931297
theorem B7107203 : Blo 550806 7107203 := bstep (se 1 (by rfl) ⟨5330402, by rfl⟩ : syracuseStep 7107203 = 10660805) B10660805
theorem B553611 : Blo 550806 553611 := bstep (se 1 (by rfl) ⟨415208, by rfl⟩ : syracuseStep 553611 = 830417) B830417
theorem B2388631 : Blo 550806 2388631 := bstep (se 1 (by rfl) ⟨1791473, by rfl⟩ : syracuseStep 2388631 = 3582947) B3582947
theorem B553623 : Blo 550806 553623 := bstep (se 1 (by rfl) ⟨415217, by rfl⟩ : syracuseStep 553623 = 830435) B830435
theorem B553643 : Blo 550806 553643 := bstep (se 1 (by rfl) ⟨415232, by rfl⟩ : syracuseStep 553643 = 830465) B830465
theorem B553655 : Blo 550806 553655 := bstep (se 1 (by rfl) ⟨415241, by rfl⟩ : syracuseStep 553655 = 830483) B830483
theorem B553675 : Blo 550806 553675 := bstep (se 1 (by rfl) ⟨415256, by rfl⟩ : syracuseStep 553675 = 830513) B830513
theorem B553687 : Blo 550806 553687 := bstep (se 1 (by rfl) ⟨415265, by rfl⟩ : syracuseStep 553687 = 830531) B830531
theorem B553707 : Blo 550806 553707 := bstep (se 1 (by rfl) ⟨415280, by rfl⟩ : syracuseStep 553707 = 830561) B830561
theorem B553719 : Blo 550806 553719 := bstep (se 1 (by rfl) ⟨415289, by rfl⟩ : syracuseStep 553719 = 830579) B830579
theorem B553739 : Blo 550806 553739 := bstep (se 1 (by rfl) ⟨415304, by rfl⟩ : syracuseStep 553739 = 830609) B830609
theorem B553751 : Blo 550806 553751 := bstep (se 1 (by rfl) ⟨415313, by rfl⟩ : syracuseStep 553751 = 830627) B830627
theorem B553771 : Blo 550806 553771 := bstep (se 1 (by rfl) ⟨415328, by rfl⟩ : syracuseStep 553771 = 830657) B830657
theorem B553783 : Blo 550806 553783 := bstep (se 1 (by rfl) ⟨415337, by rfl⟩ : syracuseStep 553783 = 830675) B830675
theorem B553803 : Blo 550806 553803 := bstep (se 1 (by rfl) ⟨415352, by rfl⟩ : syracuseStep 553803 = 830705) B830705
theorem B553815 : Blo 550806 553815 := bstep (se 1 (by rfl) ⟨415361, by rfl⟩ : syracuseStep 553815 = 830723) B830723
theorem B1241945 : Blo 550806 1241945 := bstep (se 2 (by rfl) ⟨465729, by rfl⟩ : syracuseStep 1241945 = 931459) B931459
theorem B553835 : Blo 550806 553835 := bstep (se 1 (by rfl) ⟨415376, by rfl⟩ : syracuseStep 553835 = 830753) B830753
theorem B553847 : Blo 550806 553847 := bstep (se 1 (by rfl) ⟨415385, by rfl⟩ : syracuseStep 553847 = 830771) B830771
theorem B553867 : Blo 550806 553867 := bstep (se 1 (by rfl) ⟨415400, by rfl⟩ : syracuseStep 553867 = 830801) B830801
theorem B553879 : Blo 550806 553879 := bstep (se 1 (by rfl) ⟨415409, by rfl⟩ : syracuseStep 553879 = 830819) B830819
theorem B553899 : Blo 550806 553899 := bstep (se 1 (by rfl) ⟨415424, by rfl⟩ : syracuseStep 553899 = 830849) B830849
theorem B1242035 : Blo 550806 1242035 := bstep (se 1 (by rfl) ⟨931526, by rfl⟩ : syracuseStep 1242035 = 1863053) B1863053
theorem B553911 : Blo 550806 553911 := bstep (se 1 (by rfl) ⟨415433, by rfl⟩ : syracuseStep 553911 = 830867) B830867
theorem B553931 : Blo 550806 553931 := bstep (se 1 (by rfl) ⟨415448, by rfl⟩ : syracuseStep 553931 = 830897) B830897
theorem B1242071 : Blo 550806 1242071 := bstep (se 1 (by rfl) ⟨931553, by rfl⟩ : syracuseStep 1242071 = 1863107) B1863107
theorem B553943 : Blo 550806 553943 := bstep (se 1 (by rfl) ⟨415457, by rfl⟩ : syracuseStep 553943 = 830915) B830915
theorem B553963 : Blo 550806 553963 := bstep (se 1 (by rfl) ⟨415472, by rfl⟩ : syracuseStep 553963 = 830945) B830945
theorem B553975 : Blo 550806 553975 := bstep (se 1 (by rfl) ⟨415481, by rfl⟩ : syracuseStep 553975 = 830963) B830963
theorem B2094083 : Blo 550806 2094083 := bstep (se 1 (by rfl) ⟨1570562, by rfl⟩ : syracuseStep 2094083 = 3141125) B3141125
theorem B553995 : Blo 550806 553995 := bstep (se 1 (by rfl) ⟨415496, by rfl⟩ : syracuseStep 553995 = 830993) B830993
theorem B1176599 : Blo 550806 1176599 := bstep (se 1 (by rfl) ⟨882449, by rfl⟩ : syracuseStep 1176599 = 1764899) B1764899
theorem B1864727 : Blo 550806 1864727 := bstep (se 1 (by rfl) ⟨1398545, by rfl⟩ : syracuseStep 1864727 = 2797091) B2797091
theorem B554007 : Blo 550806 554007 := bstep (se 1 (by rfl) ⟨415505, by rfl⟩ : syracuseStep 554007 = 831011) B831011
theorem B554027 : Blo 550806 554027 := bstep (se 1 (by rfl) ⟨415520, by rfl⟩ : syracuseStep 554027 = 831041) B831041
theorem B554039 : Blo 550806 554039 := bstep (se 1 (by rfl) ⟨415529, by rfl⟩ : syracuseStep 554039 = 831059) B831059
theorem B2356289 : Blo 550806 2356289 := bstep (se 2 (by rfl) ⟨883608, by rfl⟩ : syracuseStep 2356289 = 1767217) B1767217
theorem B554059 : Blo 550806 554059 := bstep (se 1 (by rfl) ⟨415544, by rfl⟩ : syracuseStep 554059 = 831089) B831089
theorem B554071 : Blo 550806 554071 := bstep (se 1 (by rfl) ⟨415553, by rfl⟩ : syracuseStep 554071 = 831107) B831107
theorem B554091 : Blo 550806 554091 := bstep (se 1 (by rfl) ⟨415568, by rfl⟩ : syracuseStep 554091 = 831137) B831137
theorem B554103 : Blo 550806 554103 := bstep (se 1 (by rfl) ⟨415577, by rfl⟩ : syracuseStep 554103 = 831155) B831155
theorem B1242251 : Blo 550806 1242251 := bstep (se 1 (by rfl) ⟨931688, by rfl⟩ : syracuseStep 1242251 = 1863377) B1863377
theorem B554123 : Blo 550806 554123 := bstep (se 1 (by rfl) ⟨415592, by rfl⟩ : syracuseStep 554123 = 831185) B831185
theorem B554135 : Blo 550806 554135 := bstep (se 1 (by rfl) ⟨415601, by rfl⟩ : syracuseStep 554135 = 831203) B831203
theorem B554155 : Blo 550806 554155 := bstep (se 1 (by rfl) ⟨415616, by rfl⟩ : syracuseStep 554155 = 831233) B831233
theorem B554167 : Blo 550806 554167 := bstep (se 1 (by rfl) ⟨415625, by rfl⟩ : syracuseStep 554167 = 831251) B831251
theorem B1242305 : Blo 550806 1242305 := bstep (se 2 (by rfl) ⟨465864, by rfl⟩ : syracuseStep 1242305 = 931729) B931729
theorem B554187 : Blo 550806 554187 := bstep (se 1 (by rfl) ⟨415640, by rfl⟩ : syracuseStep 554187 = 831281) B831281
theorem B619735 : Blo 550806 619735 := bstep (se 1 (by rfl) ⟨464801, by rfl⟩ : syracuseStep 619735 = 929603) B929603
theorem B554199 : Blo 550806 554199 := bstep (se 1 (by rfl) ⟨415649, by rfl⟩ : syracuseStep 554199 = 831299) B831299
theorem B554219 : Blo 550806 554219 := bstep (se 1 (by rfl) ⟨415664, by rfl⟩ : syracuseStep 554219 = 831329) B831329
theorem B554231 : Blo 550806 554231 := bstep (se 1 (by rfl) ⟨415673, by rfl⟩ : syracuseStep 554231 = 831347) B831347
theorem B554251 : Blo 550806 554251 := bstep (se 1 (by rfl) ⟨415688, by rfl⟩ : syracuseStep 554251 = 831377) B831377
theorem B554263 : Blo 550806 554263 := bstep (se 1 (by rfl) ⟨415697, by rfl⟩ : syracuseStep 554263 = 831395) B831395
theorem B554283 : Blo 550806 554283 := bstep (se 1 (by rfl) ⟨415712, by rfl⟩ : syracuseStep 554283 = 831425) B831425
theorem B1045811 : Blo 550806 1045811 := bstep (se 1 (by rfl) ⟨784358, by rfl⟩ : syracuseStep 1045811 = 1568717) B1568717
theorem B554295 : Blo 550806 554295 := bstep (se 1 (by rfl) ⟨415721, by rfl⟩ : syracuseStep 554295 = 831443) B831443
theorem B554315 : Blo 550806 554315 := bstep (se 1 (by rfl) ⟨415736, by rfl⟩ : syracuseStep 554315 = 831473) B831473
theorem B554327 : Blo 550806 554327 := bstep (se 1 (by rfl) ⟨415745, by rfl⟩ : syracuseStep 554327 = 831491) B831491
theorem B554347 : Blo 550806 554347 := bstep (se 1 (by rfl) ⟨415760, by rfl⟩ : syracuseStep 554347 = 831521) B831521
theorem B554359 : Blo 550806 554359 := bstep (se 1 (by rfl) ⟨415769, by rfl⟩ : syracuseStep 554359 = 831539) B831539
theorem B619915 : Blo 550806 619915 := bstep (se 1 (by rfl) ⟨464936, by rfl⟩ : syracuseStep 619915 = 929873) B929873
theorem B554379 : Blo 550806 554379 := bstep (se 1 (by rfl) ⟨415784, by rfl⟩ : syracuseStep 554379 = 831569) B831569
theorem B554391 : Blo 550806 554391 := bstep (se 1 (by rfl) ⟨415793, by rfl⟩ : syracuseStep 554391 = 831587) B831587
theorem B1242521 : Blo 550806 1242521 := bstep (se 2 (by rfl) ⟨465945, by rfl⟩ : syracuseStep 1242521 = 931891) B931891
theorem B554411 : Blo 550806 554411 := bstep (se 1 (by rfl) ⟨415808, by rfl⟩ : syracuseStep 554411 = 831617) B831617
theorem B554423 : Blo 550806 554423 := bstep (se 1 (by rfl) ⟨415817, by rfl⟩ : syracuseStep 554423 = 831635) B831635
theorem B1045963 : Blo 550806 1045963 := bstep (se 1 (by rfl) ⟨784472, by rfl⟩ : syracuseStep 1045963 = 1568945) B1568945
theorem B947659 : Blo 550806 947659 := bstep (se 1 (by rfl) ⟨710744, by rfl⟩ : syracuseStep 947659 = 1421489) B1421489
theorem B554443 : Blo 550806 554443 := bstep (se 1 (by rfl) ⟨415832, by rfl⟩ : syracuseStep 554443 = 831665) B831665
theorem B1897931 : Blo 550806 1897931 := bstep (se 1 (by rfl) ⟨1423448, by rfl⟩ : syracuseStep 1897931 = 2846897) B2846897
theorem B554455 : Blo 550806 554455 := bstep (se 1 (by rfl) ⟨415841, by rfl⟩ : syracuseStep 554455 = 831683) B831683
theorem B554475 : Blo 550806 554475 := bstep (se 1 (by rfl) ⟨415856, by rfl⟩ : syracuseStep 554475 = 831713) B831713
theorem B1242611 : Blo 550806 1242611 := bstep (se 1 (by rfl) ⟨931958, by rfl⟩ : syracuseStep 1242611 = 1863917) B1863917
theorem B620023 : Blo 550806 620023 := bstep (se 1 (by rfl) ⟨465017, by rfl⟩ : syracuseStep 620023 = 930035) B930035
theorem B554487 : Blo 550806 554487 := bstep (se 1 (by rfl) ⟨415865, by rfl⟩ : syracuseStep 554487 = 831731) B831731
theorem B4191749 : Blo 550806 4191749 := bstep (se 4 (by rfl) ⟨392976, by rfl⟩ : syracuseStep 4191749 = 785953) B785953
theorem B554507 : Blo 550806 554507 := bstep (se 1 (by rfl) ⟨415880, by rfl⟩ : syracuseStep 554507 = 831761) B831761
theorem B1242647 : Blo 550806 1242647 := bstep (se 1 (by rfl) ⟨931985, by rfl⟩ : syracuseStep 1242647 = 1863971) B1863971
theorem B554519 : Blo 550806 554519 := bstep (se 1 (by rfl) ⟨415889, by rfl⟩ : syracuseStep 554519 = 831779) B831779
theorem B554539 : Blo 550806 554539 := bstep (se 1 (by rfl) ⟨415904, by rfl⟩ : syracuseStep 554539 = 831809) B831809
theorem B1865267 : Blo 550806 1865267 := bstep (se 1 (by rfl) ⟨1398950, by rfl⟩ : syracuseStep 1865267 = 2797901) B2797901
theorem B554551 : Blo 550806 554551 := bstep (se 1 (by rfl) ⟨415913, by rfl⟩ : syracuseStep 554551 = 831827) B831827
theorem B554571 : Blo 550806 554571 := bstep (se 1 (by rfl) ⟨415928, by rfl⟩ : syracuseStep 554571 = 831857) B831857
theorem B554583 : Blo 550806 554583 := bstep (se 1 (by rfl) ⟨415937, by rfl⟩ : syracuseStep 554583 = 831875) B831875
theorem B9434717 : Blo 550806 9434717 := bstep (se 3 (by rfl) ⟨1769009, by rfl⟩ : syracuseStep 9434717 = 3538019) B3538019
theorem B554603 : Blo 550806 554603 := bstep (se 1 (by rfl) ⟨415952, by rfl⟩ : syracuseStep 554603 = 831905) B831905
theorem B554615 : Blo 550806 554615 := bstep (se 1 (by rfl) ⟨415961, by rfl⟩ : syracuseStep 554615 = 831923) B831923
theorem B554635 : Blo 550806 554635 := bstep (se 1 (by rfl) ⟨415976, by rfl⟩ : syracuseStep 554635 = 831953) B831953
theorem B554647 : Blo 550806 554647 := bstep (se 1 (by rfl) ⟨415985, by rfl⟩ : syracuseStep 554647 = 831971) B831971
theorem B620203 : Blo 550806 620203 := bstep (se 1 (by rfl) ⟨465152, by rfl⟩ : syracuseStep 620203 = 930305) B930305
theorem B554667 : Blo 550806 554667 := bstep (se 1 (by rfl) ⟨416000, by rfl⟩ : syracuseStep 554667 = 832001) B832001
theorem B554679 : Blo 550806 554679 := bstep (se 1 (by rfl) ⟨416009, by rfl⟩ : syracuseStep 554679 = 832019) B832019
theorem B1996481 : Blo 550806 1996481 := bstep (se 2 (by rfl) ⟨748680, by rfl⟩ : syracuseStep 1996481 = 1497361) B1497361
theorem B1242827 : Blo 550806 1242827 := bstep (se 1 (by rfl) ⟨932120, by rfl⟩ : syracuseStep 1242827 = 1864241) B1864241
theorem B554699 : Blo 550806 554699 := bstep (se 1 (by rfl) ⟨416024, by rfl⟩ : syracuseStep 554699 = 832049) B832049
theorem B554711 : Blo 550806 554711 := bstep (se 1 (by rfl) ⟨416033, by rfl⟩ : syracuseStep 554711 = 832067) B832067
theorem B2127581 : Blo 550806 2127581 := bstep (se 3 (by rfl) ⟨398921, by rfl⟩ : syracuseStep 2127581 = 797843) B797843
theorem B554731 : Blo 550806 554731 := bstep (se 1 (by rfl) ⟨416048, by rfl⟩ : syracuseStep 554731 = 832097) B832097
theorem B554743 : Blo 550806 554743 := bstep (se 1 (by rfl) ⟨416057, by rfl⟩ : syracuseStep 554743 = 832115) B832115
theorem B1242881 : Blo 550806 1242881 := bstep (se 2 (by rfl) ⟨466080, by rfl⟩ : syracuseStep 1242881 = 932161) B932161
theorem B554763 : Blo 550806 554763 := bstep (se 1 (by rfl) ⟨416072, by rfl⟩ : syracuseStep 554763 = 832145) B832145
theorem B620311 : Blo 550806 620311 := bstep (se 1 (by rfl) ⟨465233, by rfl⟩ : syracuseStep 620311 = 930467) B930467
theorem B554775 : Blo 550806 554775 := bstep (se 1 (by rfl) ⟨416081, by rfl⟩ : syracuseStep 554775 = 832163) B832163
theorem B1046297 : Blo 550806 1046297 := bstep (se 2 (by rfl) ⟨392361, by rfl⟩ : syracuseStep 1046297 = 784723) B784723
theorem B554795 : Blo 550806 554795 := bstep (se 1 (by rfl) ⟨416096, by rfl⟩ : syracuseStep 554795 = 832193) B832193
theorem B1865537 : Blo 550806 1865537 := bstep (se 2 (by rfl) ⟨699576, by rfl⟩ : syracuseStep 1865537 = 1399153) B1399153
theorem B4257629 : Blo 550806 4257629 := bstep (se 3 (by rfl) ⟨798305, by rfl⟩ : syracuseStep 4257629 = 1596611) B1596611
theorem B882571 : Blo 550806 882571 := bstep (se 1 (by rfl) ⟨661928, by rfl⟩ : syracuseStep 882571 = 1323857) B1323857
theorem B784279 : Blo 550806 784279 := bstep (se 1 (by rfl) ⟨588209, by rfl⟩ : syracuseStep 784279 = 1176419) B1176419
theorem B1570711 : Blo 550806 1570711 := bstep (se 1 (by rfl) ⟨1178033, by rfl⟩ : syracuseStep 1570711 = 2356067) B2356067
theorem B620491 : Blo 550806 620491 := bstep (se 1 (by rfl) ⟨465368, by rfl⟩ : syracuseStep 620491 = 930737) B930737
theorem B1243097 : Blo 550806 1243097 := bstep (se 2 (by rfl) ⟨466161, by rfl⟩ : syracuseStep 1243097 = 932323) B932323
theorem B2127833 : Blo 550806 2127833 := bstep (se 2 (by rfl) ⟨797937, by rfl⟩ : syracuseStep 2127833 = 1595875) B1595875
theorem B1243187 : Blo 550806 1243187 := bstep (se 1 (by rfl) ⟨932390, by rfl⟩ : syracuseStep 1243187 = 1864781) B1864781
theorem B620599 : Blo 550806 620599 := bstep (se 1 (by rfl) ⟨465449, by rfl⟩ : syracuseStep 620599 = 930899) B930899
theorem B1243223 : Blo 550806 1243223 := bstep (se 1 (by rfl) ⟨932417, by rfl⟩ : syracuseStep 1243223 = 1864835) B1864835
theorem B882827 : Blo 550806 882827 := bstep (se 1 (by rfl) ⟨662120, by rfl⟩ : syracuseStep 882827 = 1324241) B1324241
theorem B1767575 : Blo 550806 1767575 := bstep (se 1 (by rfl) ⟨1325681, by rfl⟩ : syracuseStep 1767575 = 2651363) B2651363
theorem B3537047 : Blo 550806 3537047 := bstep (se 1 (by rfl) ⟨2652785, by rfl⟩ : syracuseStep 3537047 = 5305571) B5305571
theorem B6715543 : Blo 550806 6715543 := bstep (se 1 (by rfl) ⟨5036657, by rfl⟩ : syracuseStep 6715543 = 10073315) B10073315
theorem B620779 : Blo 550806 620779 := bstep (se 1 (by rfl) ⟨465584, by rfl⟩ : syracuseStep 620779 = 931169) B931169
theorem B1243403 : Blo 550806 1243403 := bstep (se 1 (by rfl) ⟨932552, by rfl⟩ : syracuseStep 1243403 = 1865105) B1865105
theorem B1243457 : Blo 550806 1243457 := bstep (se 2 (by rfl) ⟨466296, by rfl⟩ : syracuseStep 1243457 = 932593) B932593
theorem B620887 : Blo 550806 620887 := bstep (se 1 (by rfl) ⟨465665, by rfl⟩ : syracuseStep 620887 = 931331) B931331
theorem B1866077 : Blo 550806 1866077 := bstep (se 3 (by rfl) ⟨349889, by rfl⟩ : syracuseStep 1866077 = 699779) B699779
theorem B1046935 : Blo 550806 1046935 := bstep (se 1 (by rfl) ⟨785201, by rfl⟩ : syracuseStep 1046935 = 1570403) B1570403
theorem B1178059 : Blo 550806 1178059 := bstep (se 1 (by rfl) ⟨883544, by rfl⟩ : syracuseStep 1178059 = 1767089) B1767089
theorem B2357707 : Blo 550806 2357707 := bstep (se 1 (by rfl) ⟨1768280, by rfl⟩ : syracuseStep 2357707 = 3536561) B3536561
theorem B621067 : Blo 550806 621067 := bstep (se 1 (by rfl) ⟨465800, by rfl⟩ : syracuseStep 621067 = 931601) B931601
theorem B1243673 : Blo 550806 1243673 := bstep (se 2 (by rfl) ⟨466377, by rfl⟩ : syracuseStep 1243673 = 932755) B932755
theorem B5044801 : Blo 550806 5044801 := bstep (se 2 (by rfl) ⟨1891800, by rfl⟩ : syracuseStep 5044801 = 3783601) B3783601
theorem B1997405 : Blo 550806 1997405 := bstep (se 3 (by rfl) ⟨374513, by rfl⟩ : syracuseStep 1997405 = 749027) B749027
theorem B1243763 : Blo 550806 1243763 := bstep (se 1 (by rfl) ⟨932822, by rfl⟩ : syracuseStep 1243763 = 1865645) B1865645
theorem B621175 : Blo 550806 621175 := bstep (se 1 (by rfl) ⟨465881, by rfl⟩ : syracuseStep 621175 = 931763) B931763
theorem B1243799 : Blo 550806 1243799 := bstep (se 1 (by rfl) ⟨932849, by rfl⟩ : syracuseStep 1243799 = 1865699) B1865699
theorem B785099 : Blo 550806 785099 := bstep (se 1 (by rfl) ⟨588824, by rfl⟩ : syracuseStep 785099 = 1177649) B1177649
theorem B1178315 : Blo 550806 1178315 := bstep (se 1 (by rfl) ⟨883736, by rfl⟩ : syracuseStep 1178315 = 1767473) B1767473
theorem B1768139 : Blo 550806 1768139 := bstep (se 1 (by rfl) ⟨1326104, by rfl⟩ : syracuseStep 1768139 = 2652209) B2652209
theorem B850649 : Blo 550806 850649 := bstep (se 2 (by rfl) ⟨318993, by rfl⟩ : syracuseStep 850649 = 637987) B637987
theorem B2357981 : Blo 550806 2357981 := bstep (se 3 (by rfl) ⟨442121, by rfl⟩ : syracuseStep 2357981 = 884243) B884243
theorem B621355 : Blo 550806 621355 := bstep (se 1 (by rfl) ⟨466016, by rfl⟩ : syracuseStep 621355 = 932033) B932033
theorem B883531 : Blo 550806 883531 := bstep (se 1 (by rfl) ⟨662648, by rfl⟩ : syracuseStep 883531 = 1325297) B1325297
theorem B1243979 : Blo 550806 1243979 := bstep (se 1 (by rfl) ⟨932984, by rfl⟩ : syracuseStep 1243979 = 1865969) B1865969
theorem B3144541 : Blo 550806 3144541 := bstep (se 3 (by rfl) ⟨589601, by rfl⟩ : syracuseStep 3144541 = 1179203) B1179203
theorem B1244033 : Blo 550806 1244033 := bstep (se 2 (by rfl) ⟨466512, by rfl⟩ : syracuseStep 1244033 = 933025) B933025
theorem B621463 : Blo 550806 621463 := bstep (se 1 (by rfl) ⟨466097, by rfl⟩ : syracuseStep 621463 = 932195) B932195
theorem B621643 : Blo 550806 621643 := bstep (se 1 (by rfl) ⟨466232, by rfl⟩ : syracuseStep 621643 = 932465) B932465
theorem B883801 : Blo 550806 883801 := bstep (se 2 (by rfl) ⟨331425, by rfl⟩ : syracuseStep 883801 = 662851) B662851
theorem B1244249 : Blo 550806 1244249 := bstep (se 2 (by rfl) ⟨466593, by rfl⟩ : syracuseStep 1244249 = 933187) B933187
theorem B883865 : Blo 550806 883865 := bstep (se 2 (by rfl) ⟨331449, by rfl⟩ : syracuseStep 883865 = 662899) B662899
theorem B1244339 : Blo 550806 1244339 := bstep (se 1 (by rfl) ⟨933254, by rfl⟩ : syracuseStep 1244339 = 1866509) B1866509
theorem B621751 : Blo 550806 621751 := bstep (se 1 (by rfl) ⟨466313, by rfl⟩ : syracuseStep 621751 = 932627) B932627
theorem B1047755 : Blo 550806 1047755 := bstep (se 1 (by rfl) ⟨785816, by rfl⟩ : syracuseStep 1047755 = 1571633) B1571633
theorem B1572043 : Blo 550806 1572043 := bstep (se 1 (by rfl) ⟨1179032, by rfl⟩ : syracuseStep 1572043 = 2358065) B2358065
theorem B1244375 : Blo 550806 1244375 := bstep (se 1 (by rfl) ⟨933281, by rfl⟩ : syracuseStep 1244375 = 1866563) B1866563
theorem B1047809 : Blo 550806 1047809 := bstep (se 2 (by rfl) ⟨392928, by rfl⟩ : syracuseStep 1047809 = 785857) B785857
theorem B621931 : Blo 550806 621931 := bstep (se 1 (by rfl) ⟨466448, by rfl⟩ : syracuseStep 621931 = 932897) B932897
theorem B1244555 : Blo 550806 1244555 := bstep (se 1 (by rfl) ⟨933416, by rfl⟩ : syracuseStep 1244555 = 1866833) B1866833
theorem B1244609 : Blo 550806 1244609 := bstep (se 2 (by rfl) ⟨466728, by rfl⟩ : syracuseStep 1244609 = 933457) B933457
theorem B1867211 : Blo 550806 1867211 := bstep (se 1 (by rfl) ⟨1400408, by rfl⟩ : syracuseStep 1867211 = 2800817) B2800817
theorem B622039 : Blo 550806 622039 := bstep (se 1 (by rfl) ⟨466529, by rfl⟩ : syracuseStep 622039 = 933059) B933059
theorem B1572317 : Blo 550806 1572317 := bstep (se 3 (by rfl) ⟨294809, by rfl⟩ : syracuseStep 1572317 = 589619) B589619
theorem B589303 : Blo 550806 589303 := bstep (se 1 (by rfl) ⟨441977, by rfl⟩ : syracuseStep 589303 = 883955) B883955
theorem B622219 : Blo 550806 622219 := bstep (se 1 (by rfl) ⟨466664, by rfl⟩ : syracuseStep 622219 = 933329) B933329
theorem B1179289 : Blo 550806 1179289 := bstep (se 2 (by rfl) ⟨442233, by rfl⟩ : syracuseStep 1179289 = 884467) B884467
theorem B1244825 : Blo 550806 1244825 := bstep (se 2 (by rfl) ⟨466809, by rfl⟩ : syracuseStep 1244825 = 933619) B933619
theorem B2981555 : Blo 550806 2981555 := bstep (se 1 (by rfl) ⟨2236166, by rfl⟩ : syracuseStep 2981555 = 4472333) B4472333
theorem B1867481 : Blo 550806 1867481 := bstep (se 2 (by rfl) ⟨700305, by rfl⟩ : syracuseStep 1867481 = 1400611) B1400611
theorem B1998557 : Blo 550806 1998557 := bstep (se 3 (by rfl) ⟨374729, by rfl⟩ : syracuseStep 1998557 = 749459) B749459
theorem B1244915 : Blo 550806 1244915 := bstep (se 1 (by rfl) ⟨933686, by rfl⟩ : syracuseStep 1244915 = 1867373) B1867373
theorem B622327 : Blo 550806 622327 := bstep (se 1 (by rfl) ⟨466745, by rfl⟩ : syracuseStep 622327 = 933491) B933491
theorem B1244951 : Blo 550806 1244951 := bstep (se 1 (by rfl) ⟨933713, by rfl⟩ : syracuseStep 1244951 = 1867427) B1867427
theorem B1179443 : Blo 550806 1179443 := bstep (se 1 (by rfl) ⟨884582, by rfl⟩ : syracuseStep 1179443 = 1769165) B1769165
theorem B1572659 : Blo 550806 1572659 := bstep (se 1 (by rfl) ⟨1179494, by rfl⟩ : syracuseStep 1572659 = 2358989) B2358989
theorem B4194179 : Blo 550806 4194179 := bstep (se 1 (by rfl) ⟨3145634, by rfl⟩ : syracuseStep 4194179 = 6291269) B6291269
theorem B622507 : Blo 550806 622507 := bstep (se 1 (by rfl) ⟨466880, by rfl⟩ : syracuseStep 622507 = 933761) B933761
theorem B1245131 : Blo 550806 1245131 := bstep (se 1 (by rfl) ⟨933848, by rfl⟩ : syracuseStep 1245131 = 1867697) B1867697
theorem B1867805 : Blo 550806 1867805 := bstep (se 3 (by rfl) ⟨350213, by rfl⟩ : syracuseStep 1867805 = 700427) B700427
theorem B622651 : Blo 550806 622651 := bstep (se 1 (by rfl) ⟨466988, by rfl⟩ : syracuseStep 622651 = 933977) B933977
theorem B2359363 : Blo 550806 2359363 := bstep (se 1 (by rfl) ⟨1769522, by rfl⟩ : syracuseStep 2359363 = 3539045) B3539045
theorem B2162945 : Blo 550806 2162945 := bstep (se 2 (by rfl) ⟨811104, by rfl⟩ : syracuseStep 2162945 = 1622209) B1622209
theorem B3145999 : Blo 550806 3145999 := bstep (se 1 (by rfl) ⟨2359499, by rfl⟩ : syracuseStep 3145999 = 4718999) B4718999
theorem B1245455 : Blo 550806 1245455 := bstep (se 1 (by rfl) ⟨934091, by rfl⟩ : syracuseStep 1245455 = 1868183) B1868183
theorem B1245473 : Blo 550806 1245473 := bstep (se 2 (by rfl) ⟨467052, by rfl⟩ : syracuseStep 1245473 = 934105) B934105
theorem B1179947 : Blo 550806 1179947 := bstep (se 1 (by rfl) ⟨884960, by rfl⟩ : syracuseStep 1179947 = 1769921) B1769921
theorem B2359705 : Blo 550806 2359705 := bstep (se 2 (by rfl) ⟨884889, by rfl⟩ : syracuseStep 2359705 = 1769779) B1769779
theorem B1573273 : Blo 550806 1573273 := bstep (se 2 (by rfl) ⟨589977, by rfl⟩ : syracuseStep 1573273 = 1179955) B1179955
theorem B623119 : Blo 550806 623119 := bstep (se 1 (by rfl) ⟨467339, by rfl⟩ : syracuseStep 623119 = 934679) B934679
theorem B787001 : Blo 550806 787001 := bstep (se 2 (by rfl) ⟨295125, by rfl⟩ : syracuseStep 787001 = 590251) B590251
theorem B1245815 : Blo 550806 1245815 := bstep (se 1 (by rfl) ⟨934361, by rfl⟩ : syracuseStep 1245815 = 1868723) B1868723
theorem B787087 : Blo 550806 787087 := bstep (se 1 (by rfl) ⟨590315, by rfl⟩ : syracuseStep 787087 = 1180631) B1180631
theorem B787115 : Blo 550806 787115 := bstep (se 1 (by rfl) ⟨590336, by rfl⟩ : syracuseStep 787115 = 1180673) B1180673
theorem B2654977 : Blo 550806 2654977 := bstep (se 2 (by rfl) ⟨995616, by rfl⟩ : syracuseStep 2654977 = 1991233) B1991233
theorem B1573661 : Blo 550806 1573661 := bstep (se 3 (by rfl) ⟨295061, by rfl⟩ : syracuseStep 1573661 = 590123) B590123
theorem B1245995 : Blo 550806 1245995 := bstep (se 1 (by rfl) ⟨934496, by rfl⟩ : syracuseStep 1245995 = 1868993) B1868993
theorem B80413667 : Blo 550806 80413667 := bstep (se 1 (by rfl) ⟨60310250, by rfl⟩ : syracuseStep 80413667 = 120620501) B120620501
theorem B623623 : Blo 550806 623623 := bstep (se 1 (by rfl) ⟨467717, by rfl⟩ : syracuseStep 623623 = 935435) B935435
theorem B2589763 : Blo 550806 2589763 := bstep (se 1 (by rfl) ⟨1942322, by rfl⟩ : syracuseStep 2589763 = 3884645) B3884645
theorem B1246355 : Blo 550806 1246355 := bstep (se 1 (by rfl) ⟨934766, by rfl⟩ : syracuseStep 1246355 = 1869533) B1869533
theorem B623803 : Blo 550806 623803 := bstep (se 1 (by rfl) ⟨467852, by rfl⟩ : syracuseStep 623803 = 935705) B935705
theorem B1246409 : Blo 550806 1246409 := bstep (se 2 (by rfl) ⟨467403, by rfl⟩ : syracuseStep 1246409 = 934807) B934807
theorem B1869209 : Blo 550806 1869209 := bstep (se 2 (by rfl) ⟨700953, by rfl⟩ : syracuseStep 1869209 = 1401907) B1401907
theorem B3147275 : Blo 550806 3147275 := bstep (se 1 (by rfl) ⟨2360456, by rfl⟩ : syracuseStep 3147275 = 4720913) B4720913
theorem B1050155 : Blo 550806 1050155 := bstep (se 1 (by rfl) ⟨787616, by rfl⟩ : syracuseStep 1050155 = 1575233) B1575233
theorem B3147457 : Blo 550806 3147457 := bstep (se 2 (by rfl) ⟨1180296, by rfl⟩ : syracuseStep 3147457 = 2360593) B2360593
theorem B1771265 : Blo 550806 1771265 := bstep (se 2 (by rfl) ⟨664224, by rfl⟩ : syracuseStep 1771265 = 1328449) B1328449
theorem B1050383 : Blo 550806 1050383 := bstep (se 1 (by rfl) ⟨787787, by rfl⟩ : syracuseStep 1050383 = 1575575) B1575575
theorem B1247111 : Blo 550806 1247111 := bstep (se 1 (by rfl) ⟨935333, by rfl⟩ : syracuseStep 1247111 = 1870667) B1870667
theorem B1247291 : Blo 550806 1247291 := bstep (se 1 (by rfl) ⟨935468, by rfl⟩ : syracuseStep 1247291 = 1870937) B1870937
theorem B1869911 : Blo 550806 1869911 := bstep (se 1 (by rfl) ⟨1402433, by rfl⟩ : syracuseStep 1869911 = 2804867) B2804867
theorem B1247417 : Blo 550806 1247417 := bstep (se 2 (by rfl) ⟨467781, by rfl⟩ : syracuseStep 1247417 = 935563) B935563
theorem B2099641 : Blo 550806 2099641 := bstep (se 2 (by rfl) ⟨787365, by rfl⟩ : syracuseStep 2099641 = 1574731) B1574731
theorem B1247759 : Blo 550806 1247759 := bstep (se 1 (by rfl) ⟨935819, by rfl⟩ : syracuseStep 1247759 = 1871639) B1871639
theorem B1247777 : Blo 550806 1247777 := bstep (se 2 (by rfl) ⟨467916, by rfl⟩ : syracuseStep 1247777 = 935833) B935833
theorem B1870397 : Blo 550806 1870397 := bstep (se 3 (by rfl) ⟨350699, by rfl⟩ : syracuseStep 1870397 = 701399) B701399
theorem B13470401 : Blo 550806 13470401 := bstep (se 2 (by rfl) ⟨5051400, by rfl⟩ : syracuseStep 13470401 = 10102801) B10102801
theorem B1248119 : Blo 550806 1248119 := bstep (se 1 (by rfl) ⟨936089, by rfl⟩ : syracuseStep 1248119 = 1872179) B1872179
theorem B5311493 : Blo 550806 5311493 := bstep (se 4 (by rfl) ⟨497952, by rfl⟩ : syracuseStep 5311493 = 995905) B995905
theorem B1117199 : Blo 550806 1117199 := bstep (se 1 (by rfl) ⟨837899, by rfl⟩ : syracuseStep 1117199 = 1675799) B1675799
theorem B1248299 : Blo 550806 1248299 := bstep (se 1 (by rfl) ⟨936224, by rfl⟩ : syracuseStep 1248299 = 1872449) B1872449
theorem B1051795 : Blo 550806 1051795 := bstep (se 1 (by rfl) ⟨788846, by rfl⟩ : syracuseStep 1051795 = 1577693) B1577693
theorem B1576235 : Blo 550806 1576235 := bstep (se 1 (by rfl) ⟨1182176, by rfl⟩ : syracuseStep 1576235 = 2364353) B2364353
theorem B2788667 : Blo 550806 2788667 := bstep (se 1 (by rfl) ⟨2091500, by rfl⟩ : syracuseStep 2788667 = 4183001) B4183001
theorem B1052023 : Blo 550806 1052023 := bstep (se 1 (by rfl) ⟨789017, by rfl⟩ : syracuseStep 1052023 = 1578035) B1578035
theorem B2788829 : Blo 550806 2788829 := bstep (se 3 (by rfl) ⟨522905, by rfl⟩ : syracuseStep 2788829 = 1045811) B1045811
theorem B17927831 : Blo 550806 17927831 := bstep (se 1 (by rfl) ⟨13445873, by rfl⟩ : syracuseStep 17927831 = 26891747) B26891747
theorem B14946049 : Blo 550806 14946049 := bstep (se 2 (by rfl) ⟨5604768, by rfl⟩ : syracuseStep 14946049 = 11209537) B11209537
theorem B2789153 : Blo 550806 2789153 := bstep (se 2 (by rfl) ⟨1045932, by rfl⟩ : syracuseStep 2789153 = 2091865) B2091865
theorem B1347475 : Blo 550806 1347475 := bstep (se 1 (by rfl) ⟨1010606, by rfl⟩ : syracuseStep 1347475 = 2021213) B2021213
theorem B1871801 : Blo 550806 1871801 := bstep (se 2 (by rfl) ⟨701925, by rfl⟩ : syracuseStep 1871801 = 1403851) B1403851
theorem B5967989 : Blo 550806 5967989 := bstep (se 5 (by rfl) ⟨279749, by rfl⟩ : syracuseStep 5967989 = 559499) B559499
theorem B1708489 : Blo 550806 1708489 := bstep (se 2 (by rfl) ⟨640683, by rfl⟩ : syracuseStep 1708489 = 1281367) B1281367
theorem B1872395 : Blo 550806 1872395 := bstep (se 1 (by rfl) ⟨1404296, by rfl⟩ : syracuseStep 1872395 = 2808593) B2808593
theorem B2790125 : Blo 550806 2790125 := bstep (se 3 (by rfl) ⟨523148, by rfl⟩ : syracuseStep 2790125 = 1046297) B1046297
theorem B4789007 : Blo 550806 4789007 := bstep (se 1 (by rfl) ⟨3591755, by rfl⟩ : syracuseStep 4789007 = 7183511) B7183511
theorem B1676065 : Blo 550806 1676065 := bstep (se 2 (by rfl) ⟨628524, by rfl⟩ : syracuseStep 1676065 = 1257049) B1257049
theorem B1577875 : Blo 550806 1577875 := bstep (se 1 (by rfl) ⟨1183406, by rfl⟩ : syracuseStep 1577875 = 2366813) B2366813
theorem B1119275 : Blo 550806 1119275 := bstep (se 1 (by rfl) ⟨839456, by rfl⟩ : syracuseStep 1119275 = 1678913) B1678913
theorem B2102543 : Blo 550806 2102543 := bstep (se 1 (by rfl) ⟨1576907, by rfl⟩ : syracuseStep 2102543 = 3153815) B3153815
theorem B2790935 : Blo 550806 2790935 := bstep (se 1 (by rfl) ⟨2093201, by rfl⟩ : syracuseStep 2790935 = 4186403) B4186403
theorem B2233975 : Blo 550806 2233975 := bstep (se 1 (by rfl) ⟨1675481, by rfl⟩ : syracuseStep 2233975 = 3350963) B3350963
theorem B1709687 : Blo 550806 1709687 := bstep (se 1 (by rfl) ⟨1282265, by rfl⟩ : syracuseStep 1709687 = 2564531) B2564531
theorem B2660111 : Blo 550806 2660111 := bstep (se 1 (by rfl) ⟨1995083, by rfl⟩ : syracuseStep 2660111 = 3990167) B3990167
theorem B3151649 : Blo 550806 3151649 := bstep (se 2 (by rfl) ⟨1181868, by rfl⟩ : syracuseStep 3151649 = 2363737) B2363737
theorem B1775495 : Blo 550806 1775495 := bstep (se 1 (by rfl) ⟨1331621, by rfl⟩ : syracuseStep 1775495 = 2663243) B2663243
theorem B3184841 : Blo 550806 3184841 := bstep (se 2 (by rfl) ⟨1194315, by rfl⟩ : syracuseStep 3184841 = 2388631) B2388631
theorem B4299155 : Blo 550806 4299155 := bstep (se 1 (by rfl) ⟨3224366, by rfl⟩ : syracuseStep 4299155 = 6448733) B6448733
theorem B1579607 : Blo 550806 1579607 := bstep (se 1 (by rfl) ⟨1184705, by rfl⟩ : syracuseStep 1579607 = 2369411) B2369411
theorem B1514099 : Blo 550806 1514099 := bstep (se 1 (by rfl) ⟨1135574, by rfl⟩ : syracuseStep 1514099 = 2271149) B2271149
theorem B3971855 : Blo 550806 3971855 := bstep (se 1 (by rfl) ⟨2978891, by rfl⟩ : syracuseStep 3971855 = 5957783) B5957783
theorem B826247 : Blo 550806 826247 := bstep (se 1 (by rfl) ⟨619685, by rfl⟩ : syracuseStep 826247 = 1239371) B1239371
theorem B826283 : Blo 550806 826283 := bstep (se 1 (by rfl) ⟨619712, by rfl⟩ : syracuseStep 826283 = 1239425) B1239425
theorem B826313 : Blo 550806 826313 := bstep (se 2 (by rfl) ⟨309867, by rfl⟩ : syracuseStep 826313 = 619735) B619735
theorem B597007 : Blo 550806 597007 := bstep (se 1 (by rfl) ⟨447755, by rfl⟩ : syracuseStep 597007 = 895511) B895511
theorem B826427 : Blo 550806 826427 := bstep (se 1 (by rfl) ⟨619820, by rfl⟩ : syracuseStep 826427 = 1239641) B1239641
theorem B826487 : Blo 550806 826487 := bstep (se 1 (by rfl) ⟨619865, by rfl⟩ : syracuseStep 826487 = 1239731) B1239731
theorem B826511 : Blo 550806 826511 := bstep (se 1 (by rfl) ⟨619883, by rfl⟩ : syracuseStep 826511 = 1239767) B1239767
theorem B826553 : Blo 550806 826553 := bstep (se 2 (by rfl) ⟨309957, by rfl⟩ : syracuseStep 826553 = 619915) B619915
theorem B1121465 : Blo 550806 1121465 := bstep (se 2 (by rfl) ⟨420549, by rfl⟩ : syracuseStep 1121465 = 841099) B841099
theorem B2268397 : Blo 550806 2268397 := bstep (se 3 (by rfl) ⟨425324, by rfl⟩ : syracuseStep 2268397 = 850649) B850649
theorem B826631 : Blo 550806 826631 := bstep (se 1 (by rfl) ⟨619973, by rfl⟩ : syracuseStep 826631 = 1239947) B1239947
theorem B826667 : Blo 550806 826667 := bstep (se 1 (by rfl) ⟨620000, by rfl⟩ : syracuseStep 826667 = 1240001) B1240001
theorem B2366779 : Blo 550806 2366779 := bstep (se 1 (by rfl) ⟨1775084, by rfl⟩ : syracuseStep 2366779 = 3550169) B3550169
theorem B826697 : Blo 550806 826697 := bstep (se 2 (by rfl) ⟨310011, by rfl⟩ : syracuseStep 826697 = 620023) B620023
theorem B826811 : Blo 550806 826811 := bstep (se 1 (by rfl) ⟨620108, by rfl⟩ : syracuseStep 826811 = 1240217) B1240217
theorem B826871 : Blo 550806 826871 := bstep (se 1 (by rfl) ⟨620153, by rfl⟩ : syracuseStep 826871 = 1240307) B1240307
theorem B826895 : Blo 550806 826895 := bstep (se 1 (by rfl) ⟨620171, by rfl⟩ : syracuseStep 826895 = 1240343) B1240343
theorem B1678877 : Blo 550806 1678877 := bstep (se 3 (by rfl) ⟨314789, by rfl⟩ : syracuseStep 1678877 = 629579) B629579
theorem B826937 : Blo 550806 826937 := bstep (se 2 (by rfl) ⟨310101, by rfl⟩ : syracuseStep 826937 = 620203) B620203
theorem B4726349 : Blo 550806 4726349 := bstep (se 3 (by rfl) ⟨886190, by rfl⟩ : syracuseStep 4726349 = 1772381) B1772381
theorem B827015 : Blo 550806 827015 := bstep (se 1 (by rfl) ⟨620261, by rfl⟩ : syracuseStep 827015 = 1240523) B1240523
theorem B827051 : Blo 550806 827051 := bstep (se 1 (by rfl) ⟨620288, by rfl⟩ : syracuseStep 827051 = 1240577) B1240577
theorem B827081 : Blo 550806 827081 := bstep (se 2 (by rfl) ⟨310155, by rfl⟩ : syracuseStep 827081 = 620311) B620311
theorem B7577317 : Blo 550806 7577317 := bstep (se 4 (by rfl) ⟨710373, by rfl⟩ : syracuseStep 7577317 = 1420747) B1420747
theorem B827195 : Blo 550806 827195 := bstep (se 1 (by rfl) ⟨620396, by rfl⟩ : syracuseStep 827195 = 1240793) B1240793
theorem B827255 : Blo 550806 827255 := bstep (se 1 (by rfl) ⟨620441, by rfl⟩ : syracuseStep 827255 = 1240883) B1240883
theorem B827279 : Blo 550806 827279 := bstep (se 1 (by rfl) ⟨620459, by rfl⟩ : syracuseStep 827279 = 1240919) B1240919
theorem B827321 : Blo 550806 827321 := bstep (se 2 (by rfl) ⟨310245, by rfl⟩ : syracuseStep 827321 = 620491) B620491
theorem B827399 : Blo 550806 827399 := bstep (se 1 (by rfl) ⟨620549, by rfl⟩ : syracuseStep 827399 = 1241099) B1241099
theorem B827435 : Blo 550806 827435 := bstep (se 1 (by rfl) ⟨620576, by rfl⟩ : syracuseStep 827435 = 1241153) B1241153
theorem B827465 : Blo 550806 827465 := bstep (se 2 (by rfl) ⟨310299, by rfl⟩ : syracuseStep 827465 = 620599) B620599
theorem B3547223 : Blo 550806 3547223 := bstep (se 1 (by rfl) ⟨2660417, by rfl⟩ : syracuseStep 3547223 = 5320835) B5320835
theorem B827579 : Blo 550806 827579 := bstep (se 1 (by rfl) ⟨620684, by rfl⟩ : syracuseStep 827579 = 1241369) B1241369
theorem B8954057 : Blo 550806 8954057 := bstep (se 2 (by rfl) ⟨3357771, by rfl⟩ : syracuseStep 8954057 = 6715543) B6715543
theorem B827639 : Blo 550806 827639 := bstep (se 1 (by rfl) ⟨620729, by rfl⟩ : syracuseStep 827639 = 1241459) B1241459
theorem B827663 : Blo 550806 827663 := bstep (se 1 (by rfl) ⟨620747, by rfl⟩ : syracuseStep 827663 = 1241495) B1241495
theorem B827705 : Blo 550806 827705 := bstep (se 2 (by rfl) ⟨310389, by rfl⟩ : syracuseStep 827705 = 620779) B620779
theorem B3547451 : Blo 550806 3547451 := bstep (se 1 (by rfl) ⟨2660588, by rfl⟩ : syracuseStep 3547451 = 5321177) B5321177
theorem B827783 : Blo 550806 827783 := bstep (se 1 (by rfl) ⟨620837, by rfl⟩ : syracuseStep 827783 = 1241675) B1241675
theorem B2105747 : Blo 550806 2105747 := bstep (se 1 (by rfl) ⟨1579310, by rfl⟩ : syracuseStep 2105747 = 3158621) B3158621
theorem B827819 : Blo 550806 827819 := bstep (se 1 (by rfl) ⟨620864, by rfl⟩ : syracuseStep 827819 = 1241729) B1241729
theorem B827849 : Blo 550806 827849 := bstep (se 2 (by rfl) ⟨310443, by rfl⟩ : syracuseStep 827849 = 620887) B620887
theorem B2794013 : Blo 550806 2794013 := bstep (se 3 (by rfl) ⟨523877, by rfl⟩ : syracuseStep 2794013 = 1047755) B1047755
theorem B827963 : Blo 550806 827963 := bstep (se 1 (by rfl) ⟨620972, by rfl⟩ : syracuseStep 827963 = 1241945) B1241945
theorem B828023 : Blo 550806 828023 := bstep (se 1 (by rfl) ⟨621017, by rfl⟩ : syracuseStep 828023 = 1242035) B1242035
theorem B828047 : Blo 550806 828047 := bstep (se 1 (by rfl) ⟨621035, by rfl⟩ : syracuseStep 828047 = 1242071) B1242071
theorem B828089 : Blo 550806 828089 := bstep (se 2 (by rfl) ⟨310533, by rfl⟩ : syracuseStep 828089 = 621067) B621067
theorem B13083353 : Blo 550806 13083353 := bstep (se 2 (by rfl) ⟨4906257, by rfl⟩ : syracuseStep 13083353 = 9812515) B9812515
theorem B6726401 : Blo 550806 6726401 := bstep (se 2 (by rfl) ⟨2522400, by rfl⟩ : syracuseStep 6726401 = 5044801) B5044801
theorem B828167 : Blo 550806 828167 := bstep (se 1 (by rfl) ⟨621125, by rfl⟩ : syracuseStep 828167 = 1242251) B1242251
theorem B828203 : Blo 550806 828203 := bstep (se 1 (by rfl) ⟨621152, by rfl⟩ : syracuseStep 828203 = 1242305) B1242305
theorem B3154747 : Blo 550806 3154747 := bstep (se 1 (by rfl) ⟨2366060, by rfl⟩ : syracuseStep 3154747 = 4732121) B4732121
theorem B828233 : Blo 550806 828233 := bstep (se 2 (by rfl) ⟨310587, by rfl⟩ : syracuseStep 828233 = 621175) B621175
theorem B21767093 : Blo 550806 21767093 := bstep (se 5 (by rfl) ⟨1020332, by rfl⟩ : syracuseStep 21767093 = 2040665) B2040665
theorem B828347 : Blo 550806 828347 := bstep (se 1 (by rfl) ⟨621260, by rfl⟩ : syracuseStep 828347 = 1242521) B1242521
theorem B828407 : Blo 550806 828407 := bstep (se 1 (by rfl) ⟨621305, by rfl⟩ : syracuseStep 828407 = 1242611) B1242611
theorem B2794499 : Blo 550806 2794499 := bstep (se 1 (by rfl) ⟨2095874, by rfl⟩ : syracuseStep 2794499 = 4191749) B4191749
theorem B828431 : Blo 550806 828431 := bstep (se 1 (by rfl) ⟨621323, by rfl⟩ : syracuseStep 828431 = 1242647) B1242647
theorem B828473 : Blo 550806 828473 := bstep (se 2 (by rfl) ⟨310677, by rfl⟩ : syracuseStep 828473 = 621355) B621355
theorem B828551 : Blo 550806 828551 := bstep (se 1 (by rfl) ⟨621413, by rfl⟩ : syracuseStep 828551 = 1242827) B1242827
theorem B1418387 : Blo 550806 1418387 := bstep (se 1 (by rfl) ⟨1063790, by rfl⟩ : syracuseStep 1418387 = 2127581) B2127581
theorem B13477013 : Blo 550806 13477013 := bstep (se 6 (by rfl) ⟨315867, by rfl⟩ : syracuseStep 13477013 = 631735) B631735
theorem B828587 : Blo 550806 828587 := bstep (se 1 (by rfl) ⟨621440, by rfl⟩ : syracuseStep 828587 = 1242881) B1242881
theorem B828617 : Blo 550806 828617 := bstep (se 2 (by rfl) ⟨310731, by rfl⟩ : syracuseStep 828617 = 621463) B621463
theorem B828731 : Blo 550806 828731 := bstep (se 1 (by rfl) ⟨621548, by rfl⟩ : syracuseStep 828731 = 1243097) B1243097
theorem B1418555 : Blo 550806 1418555 := bstep (se 1 (by rfl) ⟨1063916, by rfl⟩ : syracuseStep 1418555 = 2127833) B2127833
theorem B828791 : Blo 550806 828791 := bstep (se 1 (by rfl) ⟨621593, by rfl⟩ : syracuseStep 828791 = 1243187) B1243187
theorem B664951 : Blo 550806 664951 := bstep (se 1 (by rfl) ⟨498713, by rfl⟩ : syracuseStep 664951 = 997427) B997427
theorem B1123703 : Blo 550806 1123703 := bstep (se 1 (by rfl) ⟨842777, by rfl⟩ : syracuseStep 1123703 = 1685555) B1685555
theorem B828815 : Blo 550806 828815 := bstep (se 1 (by rfl) ⟨621611, by rfl⟩ : syracuseStep 828815 = 1243223) B1243223
theorem B828857 : Blo 550806 828857 := bstep (se 2 (by rfl) ⟨310821, by rfl⟩ : syracuseStep 828857 = 621643) B621643
theorem B828935 : Blo 550806 828935 := bstep (se 1 (by rfl) ⟨621701, by rfl⟩ : syracuseStep 828935 = 1243403) B1243403
theorem B828971 : Blo 550806 828971 := bstep (se 1 (by rfl) ⟨621728, by rfl⟩ : syracuseStep 828971 = 1243457) B1243457
theorem B829001 : Blo 550806 829001 := bstep (se 2 (by rfl) ⟨310875, by rfl⟩ : syracuseStep 829001 = 621751) B621751
theorem B829115 : Blo 550806 829115 := bstep (se 1 (by rfl) ⟨621836, by rfl⟩ : syracuseStep 829115 = 1243673) B1243673
theorem B829175 : Blo 550806 829175 := bstep (se 1 (by rfl) ⟨621881, by rfl⟩ : syracuseStep 829175 = 1243763) B1243763
theorem B829199 : Blo 550806 829199 := bstep (se 1 (by rfl) ⟨621899, by rfl⟩ : syracuseStep 829199 = 1243799) B1243799
theorem B6301475 : Blo 550806 6301475 := bstep (se 1 (by rfl) ⟨4726106, by rfl⟩ : syracuseStep 6301475 = 9452213) B9452213
theorem B829241 : Blo 550806 829241 := bstep (se 2 (by rfl) ⟨310965, by rfl⟩ : syracuseStep 829241 = 621931) B621931
theorem B829319 : Blo 550806 829319 := bstep (se 1 (by rfl) ⟨621989, by rfl⟩ : syracuseStep 829319 = 1243979) B1243979
theorem B829355 : Blo 550806 829355 := bstep (se 1 (by rfl) ⟨622016, by rfl⟩ : syracuseStep 829355 = 1244033) B1244033
theorem B829385 : Blo 550806 829385 := bstep (se 2 (by rfl) ⟨311019, by rfl⟩ : syracuseStep 829385 = 622039) B622039
theorem B829499 : Blo 550806 829499 := bstep (se 1 (by rfl) ⟨622124, by rfl⟩ : syracuseStep 829499 = 1244249) B1244249
theorem B829559 : Blo 550806 829559 := bstep (se 1 (by rfl) ⟨622169, by rfl⟩ : syracuseStep 829559 = 1244339) B1244339
theorem B829583 : Blo 550806 829583 := bstep (se 1 (by rfl) ⟨622187, by rfl⟩ : syracuseStep 829583 = 1244375) B1244375
theorem B698539 : Blo 550806 698539 := bstep (se 1 (by rfl) ⟨523904, by rfl⟩ : syracuseStep 698539 = 1047809) B1047809
theorem B2992301 : Blo 550806 2992301 := bstep (se 3 (by rfl) ⟨561056, by rfl⟩ : syracuseStep 2992301 = 1122113) B1122113
theorem B829625 : Blo 550806 829625 := bstep (se 2 (by rfl) ⟨311109, by rfl⟩ : syracuseStep 829625 = 622219) B622219
theorem B3156205 : Blo 550806 3156205 := bstep (se 3 (by rfl) ⟨591788, by rfl⟩ : syracuseStep 3156205 = 1183577) B1183577
theorem B829703 : Blo 550806 829703 := bstep (se 1 (by rfl) ⟨622277, by rfl⟩ : syracuseStep 829703 = 1244555) B1244555
theorem B829739 : Blo 550806 829739 := bstep (se 1 (by rfl) ⟨622304, by rfl⟩ : syracuseStep 829739 = 1244609) B1244609
theorem B829769 : Blo 550806 829769 := bstep (se 2 (by rfl) ⟨311163, by rfl⟩ : syracuseStep 829769 = 622327) B622327
theorem B829883 : Blo 550806 829883 := bstep (se 1 (by rfl) ⟨622412, by rfl⟩ : syracuseStep 829883 = 1244825) B1244825
theorem B829943 : Blo 550806 829943 := bstep (se 1 (by rfl) ⟨622457, by rfl⟩ : syracuseStep 829943 = 1244915) B1244915
theorem B829967 : Blo 550806 829967 := bstep (se 1 (by rfl) ⟨622475, by rfl⟩ : syracuseStep 829967 = 1244951) B1244951
theorem B2239019 : Blo 550806 2239019 := bstep (se 1 (by rfl) ⟨1679264, by rfl⟩ : syracuseStep 2239019 = 3358529) B3358529
theorem B4729387 : Blo 550806 4729387 := bstep (se 1 (by rfl) ⟨3547040, by rfl⟩ : syracuseStep 4729387 = 7094081) B7094081
theorem B830009 : Blo 550806 830009 := bstep (se 2 (by rfl) ⟨311253, by rfl⟩ : syracuseStep 830009 = 622507) B622507
theorem B2796119 : Blo 550806 2796119 := bstep (se 1 (by rfl) ⟨2097089, by rfl⟩ : syracuseStep 2796119 = 4194179) B4194179
theorem B830087 : Blo 550806 830087 := bstep (se 1 (by rfl) ⟨622565, by rfl⟩ : syracuseStep 830087 = 1245131) B1245131
theorem B830123 : Blo 550806 830123 := bstep (se 1 (by rfl) ⟨622592, by rfl⟩ : syracuseStep 830123 = 1245185) B1245185
theorem B830153 : Blo 550806 830153 := bstep (se 2 (by rfl) ⟨311307, by rfl⟩ : syracuseStep 830153 = 622615) B622615
theorem B830267 : Blo 550806 830267 := bstep (se 1 (by rfl) ⟨622700, by rfl⟩ : syracuseStep 830267 = 1245401) B1245401
theorem B830327 : Blo 550806 830327 := bstep (se 1 (by rfl) ⟨622745, by rfl⟩ : syracuseStep 830327 = 1245491) B1245491
theorem B830351 : Blo 550806 830351 := bstep (se 1 (by rfl) ⟨622763, by rfl⟩ : syracuseStep 830351 = 1245527) B1245527
theorem B3353491 : Blo 550806 3353491 := bstep (se 1 (by rfl) ⟨2515118, by rfl⟩ : syracuseStep 3353491 = 5030237) B5030237
theorem B830393 : Blo 550806 830393 := bstep (se 2 (by rfl) ⟨311397, by rfl⟩ : syracuseStep 830393 = 622795) B622795
theorem B830471 : Blo 550806 830471 := bstep (se 1 (by rfl) ⟨622853, by rfl⟩ : syracuseStep 830471 = 1245707) B1245707
theorem B830507 : Blo 550806 830507 := bstep (se 1 (by rfl) ⟨622880, by rfl⟩ : syracuseStep 830507 = 1245761) B1245761
theorem B2796605 : Blo 550806 2796605 := bstep (se 3 (by rfl) ⟨524363, by rfl⟩ : syracuseStep 2796605 = 1048727) B1048727
theorem B830537 : Blo 550806 830537 := bstep (se 2 (by rfl) ⟨311451, by rfl⟩ : syracuseStep 830537 = 622903) B622903
theorem B699511 : Blo 550806 699511 := bstep (se 1 (by rfl) ⟨524633, by rfl⟩ : syracuseStep 699511 = 1049267) B1049267
theorem B830651 : Blo 550806 830651 := bstep (se 1 (by rfl) ⟨622988, by rfl⟩ : syracuseStep 830651 = 1245977) B1245977
theorem B2993381 : Blo 550806 2993381 := bstep (se 4 (by rfl) ⟨280629, by rfl⟩ : syracuseStep 2993381 = 561259) B561259
theorem B830711 : Blo 550806 830711 := bstep (se 1 (by rfl) ⟨623033, by rfl⟩ : syracuseStep 830711 = 1246067) B1246067
theorem B830735 : Blo 550806 830735 := bstep (se 1 (by rfl) ⟨623051, by rfl⟩ : syracuseStep 830735 = 1246103) B1246103
theorem B830777 : Blo 550806 830777 := bstep (se 2 (by rfl) ⟨311541, by rfl⟩ : syracuseStep 830777 = 623083) B623083
theorem B830855 : Blo 550806 830855 := bstep (se 1 (by rfl) ⟨623141, by rfl⟩ : syracuseStep 830855 = 1246283) B1246283
theorem B248491405 : Blo 550806 248491405 := bstep (se 3 (by rfl) ⟨46592138, by rfl⟩ : syracuseStep 248491405 = 93184277) B93184277
theorem B830891 : Blo 550806 830891 := bstep (se 1 (by rfl) ⟨623168, by rfl⟩ : syracuseStep 830891 = 1246337) B1246337
theorem B699835 : Blo 550806 699835 := bstep (se 1 (by rfl) ⟨524876, by rfl⟩ : syracuseStep 699835 = 1049753) B1049753
theorem B830921 : Blo 550806 830921 := bstep (se 2 (by rfl) ⟨311595, by rfl⟩ : syracuseStep 830921 = 623191) B623191
theorem B831035 : Blo 550806 831035 := bstep (se 1 (by rfl) ⟨623276, by rfl⟩ : syracuseStep 831035 = 1246553) B1246553
theorem B24161885 : Blo 550806 24161885 := bstep (se 3 (by rfl) ⟨4530353, by rfl⟩ : syracuseStep 24161885 = 9060707) B9060707
theorem B831095 : Blo 550806 831095 := bstep (se 1 (by rfl) ⟨623321, by rfl⟩ : syracuseStep 831095 = 1246643) B1246643
theorem B831119 : Blo 550806 831119 := bstep (se 1 (by rfl) ⟨623339, by rfl⟩ : syracuseStep 831119 = 1246679) B1246679
theorem B831161 : Blo 550806 831161 := bstep (se 2 (by rfl) ⟨311685, by rfl⟩ : syracuseStep 831161 = 623371) B623371
theorem B798409 : Blo 550806 798409 := bstep (se 2 (by rfl) ⟨299403, by rfl⟩ : syracuseStep 798409 = 598807) B598807
theorem B831239 : Blo 550806 831239 := bstep (se 1 (by rfl) ⟨623429, by rfl⟩ : syracuseStep 831239 = 1246859) B1246859
theorem B831275 : Blo 550806 831275 := bstep (se 1 (by rfl) ⟨623456, by rfl⟩ : syracuseStep 831275 = 1246913) B1246913
theorem B831305 : Blo 550806 831305 := bstep (se 2 (by rfl) ⟨311739, by rfl⟩ : syracuseStep 831305 = 623479) B623479
theorem B831419 : Blo 550806 831419 := bstep (se 1 (by rfl) ⟨623564, by rfl⟩ : syracuseStep 831419 = 1247129) B1247129
theorem B831479 : Blo 550806 831479 := bstep (se 1 (by rfl) ⟨623609, by rfl⟩ : syracuseStep 831479 = 1247219) B1247219
theorem B831503 : Blo 550806 831503 := bstep (se 1 (by rfl) ⟨623627, by rfl⟩ : syracuseStep 831503 = 1247255) B1247255
theorem B831545 : Blo 550806 831545 := bstep (se 2 (by rfl) ⟨311829, by rfl⟩ : syracuseStep 831545 = 623659) B623659
theorem B798779 : Blo 550806 798779 := bstep (se 1 (by rfl) ⟨599084, by rfl⟩ : syracuseStep 798779 = 1198169) B1198169
theorem B929927 : Blo 550806 929927 := bstep (se 1 (by rfl) ⟨697445, by rfl⟩ : syracuseStep 929927 = 1394891) B1394891
theorem B831623 : Blo 550806 831623 := bstep (se 1 (by rfl) ⟨623717, by rfl⟩ : syracuseStep 831623 = 1247435) B1247435
theorem B831659 : Blo 550806 831659 := bstep (se 1 (by rfl) ⟨623744, by rfl⟩ : syracuseStep 831659 = 1247489) B1247489
theorem B3158189 : Blo 550806 3158189 := bstep (se 3 (by rfl) ⟨592160, by rfl⟩ : syracuseStep 3158189 = 1184321) B1184321
theorem B831689 : Blo 550806 831689 := bstep (se 2 (by rfl) ⟨311883, by rfl⟩ : syracuseStep 831689 = 623767) B623767
theorem B3354853 : Blo 550806 3354853 := bstep (se 4 (by rfl) ⟨314517, by rfl⟩ : syracuseStep 3354853 = 629035) B629035
theorem B799033 : Blo 550806 799033 := bstep (se 2 (by rfl) ⟨299637, by rfl⟩ : syracuseStep 799033 = 599275) B599275
theorem B831803 : Blo 550806 831803 := bstep (se 1 (by rfl) ⟨623852, by rfl⟩ : syracuseStep 831803 = 1247705) B1247705
theorem B831863 : Blo 550806 831863 := bstep (se 1 (by rfl) ⟨623897, by rfl⟩ : syracuseStep 831863 = 1247795) B1247795
theorem B700807 : Blo 550806 700807 := bstep (se 1 (by rfl) ⟨525605, by rfl⟩ : syracuseStep 700807 = 1051211) B1051211
theorem B831887 : Blo 550806 831887 := bstep (se 1 (by rfl) ⟨623915, by rfl⟩ : syracuseStep 831887 = 1247831) B1247831
theorem B831929 : Blo 550806 831929 := bstep (se 2 (by rfl) ⟨311973, by rfl⟩ : syracuseStep 831929 = 623947) B623947
theorem B832007 : Blo 550806 832007 := bstep (se 1 (by rfl) ⟨624005, by rfl⟩ : syracuseStep 832007 = 1248011) B1248011
theorem B832043 : Blo 550806 832043 := bstep (se 1 (by rfl) ⟨624032, by rfl⟩ : syracuseStep 832043 = 1248065) B1248065
theorem B832073 : Blo 550806 832073 := bstep (se 2 (by rfl) ⟨312027, by rfl⟩ : syracuseStep 832073 = 624055) B624055
theorem B832187 : Blo 550806 832187 := bstep (se 1 (by rfl) ⟨624140, by rfl⟩ : syracuseStep 832187 = 1248281) B1248281
theorem B8991425 : Blo 550806 8991425 := bstep (se 2 (by rfl) ⟨3371784, by rfl⟩ : syracuseStep 8991425 = 6743569) B6743569
theorem B930575 : Blo 550806 930575 := bstep (se 1 (by rfl) ⟨697931, by rfl⟩ : syracuseStep 930575 = 1395863) B1395863
theorem B1061675 : Blo 550806 1061675 := bstep (se 1 (by rfl) ⟨796256, by rfl⟩ : syracuseStep 1061675 = 1592513) B1592513
theorem B701227 : Blo 550806 701227 := bstep (se 1 (by rfl) ⟨525920, by rfl⟩ : syracuseStep 701227 = 1051841) B1051841
theorem B2798387 : Blo 550806 2798387 := bstep (se 1 (by rfl) ⟨2098790, by rfl⟩ : syracuseStep 2798387 = 4197581) B4197581
theorem B701455 : Blo 550806 701455 := bstep (se 1 (by rfl) ⟨526091, by rfl⟩ : syracuseStep 701455 = 1052183) B1052183
theorem B2798711 : Blo 550806 2798711 := bstep (se 1 (by rfl) ⟨2099033, by rfl⟩ : syracuseStep 2798711 = 4198067) B4198067
theorem B2995393 : Blo 550806 2995393 := bstep (se 2 (by rfl) ⟨1123272, by rfl⟩ : syracuseStep 2995393 = 2246545) B2246545
theorem B1324289 : Blo 550806 1324289 := bstep (se 2 (by rfl) ⟨496608, by rfl⟩ : syracuseStep 1324289 = 993217) B993217
theorem B800015 : Blo 550806 800015 := bstep (se 1 (by rfl) ⟨600011, by rfl⟩ : syracuseStep 800015 = 1200023) B1200023
theorem B931115 : Blo 550806 931115 := bstep (se 1 (by rfl) ⟨698336, by rfl⟩ : syracuseStep 931115 = 1396673) B1396673
theorem B4470349 : Blo 550806 4470349 := bstep (se 3 (by rfl) ⟨838190, by rfl⟩ : syracuseStep 4470349 = 1676381) B1676381
theorem B931513 : Blo 550806 931513 := bstep (se 2 (by rfl) ⟨349317, by rfl⟩ : syracuseStep 931513 = 698635) B698635
theorem B2799683 : Blo 550806 2799683 := bstep (se 1 (by rfl) ⟨2099762, by rfl⟩ : syracuseStep 2799683 = 4199525) B4199525
theorem B932215 : Blo 550806 932215 := bstep (se 1 (by rfl) ⟨699161, by rfl⟩ : syracuseStep 932215 = 1398323) B1398323
theorem B997751 : Blo 550806 997751 := bstep (se 1 (by rfl) ⟨748313, by rfl⟩ : syracuseStep 997751 = 1496627) B1496627
theorem B2800007 : Blo 550806 2800007 := bstep (se 1 (by rfl) ⟨2100005, by rfl⟩ : syracuseStep 2800007 = 4200011) B4200011
theorem B1063315 : Blo 550806 1063315 := bstep (se 1 (by rfl) ⟨797486, by rfl⟩ : syracuseStep 1063315 = 1594973) B1594973
theorem B932411 : Blo 550806 932411 := bstep (se 1 (by rfl) ⟨699308, by rfl⟩ : syracuseStep 932411 = 1398617) B1398617
theorem B10631897 : Blo 550806 10631897 := bstep (se 2 (by rfl) ⟨3986961, by rfl⟩ : syracuseStep 10631897 = 7973923) B7973923
theorem B6404915 : Blo 550806 6404915 := bstep (se 1 (by rfl) ⟨4803686, by rfl⟩ : syracuseStep 6404915 = 9607373) B9607373
theorem B932809 : Blo 550806 932809 := bstep (se 2 (by rfl) ⟨349803, by rfl⟩ : syracuseStep 932809 = 699607) B699607
theorem B1621367 : Blo 550806 1621367 := bstep (se 1 (by rfl) ⟨1216025, by rfl⟩ : syracuseStep 1621367 = 2432051) B2432051
theorem B8535581 : Blo 550806 8535581 := bstep (se 3 (by rfl) ⟨1600421, by rfl⟩ : syracuseStep 8535581 = 3200843) B3200843
theorem B933511 : Blo 550806 933511 := bstep (se 1 (by rfl) ⟨700133, by rfl⟩ : syracuseStep 933511 = 1400267) B1400267
theorem B934159 : Blo 550806 934159 := bstep (se 1 (by rfl) ⟨700619, by rfl⟩ : syracuseStep 934159 = 1401239) B1401239
theorem B4473463 : Blo 550806 4473463 := bstep (se 1 (by rfl) ⟨3355097, by rfl⟩ : syracuseStep 4473463 = 6710195) B6710195
theorem B4735745 : Blo 550806 4735745 := bstep (se 2 (by rfl) ⟨1775904, by rfl⟩ : syracuseStep 4735745 = 3551809) B3551809
theorem B1065761 : Blo 550806 1065761 := bstep (se 2 (by rfl) ⟨399660, by rfl⟩ : syracuseStep 1065761 = 799321) B799321
theorem B3982117 : Blo 550806 3982117 := bstep (se 4 (by rfl) ⟨373323, by rfl⟩ : syracuseStep 3982117 = 746647) B746647
theorem B934699 : Blo 550806 934699 := bstep (se 1 (by rfl) ⟨701024, by rfl⟩ : syracuseStep 934699 = 1402049) B1402049
theorem B1327931 : Blo 550806 1327931 := bstep (se 1 (by rfl) ⟨995948, by rfl⟩ : syracuseStep 1327931 = 1991897) B1991897
theorem B934841 : Blo 550806 934841 := bstep (se 2 (by rfl) ⟨350565, by rfl⟩ : syracuseStep 934841 = 701131) B701131
theorem B935543 : Blo 550806 935543 := bstep (se 1 (by rfl) ⟨701657, by rfl⟩ : syracuseStep 935543 = 1403315) B1403315
theorem B1328825 : Blo 550806 1328825 := bstep (se 2 (by rfl) ⟨498309, by rfl⟩ : syracuseStep 1328825 = 996619) B996619
theorem B5031695 : Blo 550806 5031695 := bstep (se 1 (by rfl) ⟨3773771, by rfl⟩ : syracuseStep 5031695 = 7547543) B7547543
theorem B2803571 : Blo 550806 2803571 := bstep (se 1 (by rfl) ⟨2102678, by rfl⟩ : syracuseStep 2803571 = 4205357) B4205357
theorem B1394567 : Blo 550806 1394567 := bstep (se 1 (by rfl) ⟨1045925, by rfl⟩ : syracuseStep 1394567 = 2091851) B2091851
theorem B1394617 : Blo 550806 1394617 := bstep (se 2 (by rfl) ⟨522981, by rfl⟩ : syracuseStep 1394617 = 1045963) B1045963
theorem B1263545 : Blo 550806 1263545 := bstep (se 2 (by rfl) ⟨473829, by rfl⟩ : syracuseStep 1263545 = 947659) B947659
theorem B935995 : Blo 550806 935995 := bstep (se 1 (by rfl) ⟨701996, by rfl⟩ : syracuseStep 935995 = 1403993) B1403993
theorem B6473861 : Blo 550806 6473861 := bstep (se 4 (by rfl) ⟨606924, by rfl⟩ : syracuseStep 6473861 = 1213849) B1213849
theorem B936137 : Blo 550806 936137 := bstep (se 2 (by rfl) ⟨351051, by rfl⟩ : syracuseStep 936137 = 702103) B702103
theorem B2804057 : Blo 550806 2804057 := bstep (se 2 (by rfl) ⟨1051521, by rfl⟩ : syracuseStep 2804057 = 2103043) B2103043
theorem B1067411 : Blo 550806 1067411 := bstep (se 1 (by rfl) ⟨800558, by rfl⟩ : syracuseStep 1067411 = 1601117) B1601117
theorem B3590659 : Blo 550806 3590659 := bstep (se 1 (by rfl) ⟨2692994, by rfl⟩ : syracuseStep 3590659 = 5385989) B5385989
theorem B1395215 : Blo 550806 1395215 := bstep (se 1 (by rfl) ⟨1046411, by rfl⟩ : syracuseStep 1395215 = 2092823) B2092823
theorem B1329679 : Blo 550806 1329679 := bstep (se 1 (by rfl) ⟨997259, by rfl⟩ : syracuseStep 1329679 = 1994519) B1994519
theorem B4738135 : Blo 550806 4738135 := bstep (se 1 (by rfl) ⟨3553601, by rfl⟩ : syracuseStep 4738135 = 7107203) B7107203
theorem B1395913 : Blo 550806 1395913 := bstep (se 2 (by rfl) ⟨523467, by rfl⟩ : syracuseStep 1395913 = 1046935) B1046935
theorem B1396055 : Blo 550806 1396055 := bstep (se 1 (by rfl) ⟨1047041, by rfl⟩ : syracuseStep 1396055 = 2094083) B2094083
theorem B1265287 : Blo 550806 1265287 := bstep (se 1 (by rfl) ⟨948965, by rfl⟩ : syracuseStep 1265287 = 1897931) B1897931
theorem B708239 : Blo 550806 708239 := bstep (se 1 (by rfl) ⟨531179, by rfl⟩ : syracuseStep 708239 = 1062359) B1062359
theorem B6311681 : Blo 550806 6311681 := bstep (se 2 (by rfl) ⟨2366880, by rfl⟩ : syracuseStep 6311681 = 4733761) B4733761
theorem B1330987 : Blo 550806 1330987 := bstep (se 1 (by rfl) ⟨998240, by rfl⟩ : syracuseStep 1330987 = 1996481) B1996481
theorem B2838419 : Blo 550806 2838419 := bstep (se 1 (by rfl) ⟨2128814, by rfl⟩ : syracuseStep 2838419 = 4257629) B4257629
theorem B1331603 : Blo 550806 1331603 := bstep (se 1 (by rfl) ⟨998702, by rfl⟩ : syracuseStep 1331603 = 1997405) B1997405
theorem B2806163 : Blo 550806 2806163 := bstep (se 1 (by rfl) ⟨2104622, by rfl⟩ : syracuseStep 2806163 = 4209245) B4209245
theorem B5329637 : Blo 550806 5329637 := bstep (se 4 (by rfl) ⟨499653, by rfl⟩ : syracuseStep 5329637 = 999307) B999307
theorem B1987703 : Blo 550806 1987703 := bstep (se 1 (by rfl) ⟨1490777, by rfl⟩ : syracuseStep 1987703 = 2981555) B2981555
theorem B1332371 : Blo 550806 1332371 := bstep (se 1 (by rfl) ⟨999278, by rfl⟩ : syracuseStep 1332371 = 1998557) B1998557
theorem B1398131 : Blo 550806 1398131 := bstep (se 1 (by rfl) ⟨1048598, by rfl⟩ : syracuseStep 1398131 = 2097197) B2097197
theorem B48420557 : Blo 550806 48420557 := bstep (se 3 (by rfl) ⟨9078854, by rfl⟩ : syracuseStep 48420557 = 18157709) B18157709
theorem B8509157 : Blo 550806 8509157 := bstep (se 4 (by rfl) ⟨797733, by rfl⟩ : syracuseStep 8509157 = 1595467) B1595467
theorem B1496843 : Blo 550806 1496843 := bstep (se 1 (by rfl) ⟨1122632, by rfl⟩ : syracuseStep 1496843 = 2245265) B2245265
theorem B841487 : Blo 550806 841487 := bstep (se 1 (by rfl) ⟨631115, by rfl⟩ : syracuseStep 841487 = 1262231) B1262231
theorem B1398647 : Blo 550806 1398647 := bstep (se 1 (by rfl) ⟨1048985, by rfl⟩ : syracuseStep 1398647 = 2097971) B2097971
theorem B1496951 : Blo 550806 1496951 := bstep (se 1 (by rfl) ⟨1122713, by rfl⟩ : syracuseStep 1496951 = 2245427) B2245427
theorem B2021267 : Blo 550806 2021267 := bstep (se 1 (by rfl) ⟨1515950, by rfl⟩ : syracuseStep 2021267 = 3031901) B3031901
theorem B808951 : Blo 550806 808951 := bstep (se 1 (by rfl) ⟨606713, by rfl⟩ : syracuseStep 808951 = 1213427) B1213427
theorem B87447605 : Blo 550806 87447605 := bstep (se 5 (by rfl) ⟨4099106, by rfl⟩ : syracuseStep 87447605 = 8198213) B8198213
theorem B1136825 : Blo 550806 1136825 := bstep (se 2 (by rfl) ⟨426309, by rfl⟩ : syracuseStep 1136825 = 852619) B852619
theorem B842119 : Blo 550806 842119 := bstep (se 1 (by rfl) ⟨631589, by rfl⟩ : syracuseStep 842119 = 1263179) B1263179
theorem B6314597 : Blo 550806 6314597 := bstep (se 4 (by rfl) ⟨591993, by rfl⟩ : syracuseStep 6314597 = 1183987) B1183987
theorem B12114613 : Blo 550806 12114613 := bstep (se 5 (by rfl) ⟨567872, by rfl⟩ : syracuseStep 12114613 = 1135745) B1135745
theorem B1399639 : Blo 550806 1399639 := bstep (se 1 (by rfl) ⟨1049729, by rfl⟩ : syracuseStep 1399639 = 2099459) B2099459
theorem B5299033 : Blo 550806 5299033 := bstep (se 2 (by rfl) ⟨1987137, by rfl⟩ : syracuseStep 5299033 = 3974275) B3974275
theorem B1596449 : Blo 550806 1596449 := bstep (se 2 (by rfl) ⟨598668, by rfl⟩ : syracuseStep 1596449 = 1197337) B1197337
theorem B1399943 : Blo 550806 1399943 := bstep (se 1 (by rfl) ⟨1049957, by rfl⟩ : syracuseStep 1399943 = 2099915) B2099915
theorem B1400075 : Blo 550806 1400075 := bstep (se 1 (by rfl) ⟨1050056, by rfl⟩ : syracuseStep 1400075 = 2100113) B2100113
theorem B1859273 : Blo 550806 1859273 := bstep (se 2 (by rfl) ⟨697227, by rfl⟩ : syracuseStep 1859273 = 1394455) B1394455
theorem B1400591 : Blo 550806 1400591 := bstep (se 1 (by rfl) ⟨1050443, by rfl⟩ : syracuseStep 1400591 = 2100887) B2100887
theorem B1400723 : Blo 550806 1400723 := bstep (se 1 (by rfl) ⟨1050542, by rfl⟩ : syracuseStep 1400723 = 2101085) B2101085
theorem B20406167 : Blo 550806 20406167 := bstep (se 1 (by rfl) ⟨15304625, by rfl⟩ : syracuseStep 20406167 = 30609251) B30609251
theorem B6316055 : Blo 550806 6316055 := bstep (se 1 (by rfl) ⟨4737041, by rfl⟩ : syracuseStep 6316055 = 9474083) B9474083
theorem B3367169 : Blo 550806 3367169 := bstep (se 2 (by rfl) ⟨1262688, by rfl⟩ : syracuseStep 3367169 = 2525377) B2525377
theorem B1859975 : Blo 550806 1859975 := bstep (se 1 (by rfl) ⟨1394981, by rfl⟩ : syracuseStep 1859975 = 2789963) B2789963
theorem B7955009 : Blo 550806 7955009 := bstep (se 2 (by rfl) ⟨2983128, by rfl⟩ : syracuseStep 7955009 = 5966257) B5966257
theorem B1860353 : Blo 550806 1860353 := bstep (se 2 (by rfl) ⟨697632, by rfl⟩ : syracuseStep 1860353 = 1395265) B1395265
theorem B14377817 : Blo 550806 14377817 := bstep (se 2 (by rfl) ⟨5391681, by rfl⟩ : syracuseStep 14377817 = 10783363) B10783363
theorem B5235619 : Blo 550806 5235619 := bstep (se 1 (by rfl) ⟨3926714, by rfl⟩ : syracuseStep 5235619 = 7853429) B7853429
theorem B1401857 : Blo 550806 1401857 := bstep (se 2 (by rfl) ⟨525696, by rfl⟩ : syracuseStep 1401857 = 1051393) B1051393
theorem B1402231 : Blo 550806 1402231 := bstep (se 1 (by rfl) ⟨1051673, by rfl⟩ : syracuseStep 1402231 = 2103347) B2103347
theorem B1861163 : Blo 550806 1861163 := bstep (se 1 (by rfl) ⟨1395872, by rfl⟩ : syracuseStep 1861163 = 2791745) B2791745
theorem B4712165 : Blo 550806 4712165 := bstep (se 4 (by rfl) ⟨441765, by rfl⟩ : syracuseStep 4712165 = 883531) B883531
theorem B1402667 : Blo 550806 1402667 := bstep (se 1 (by rfl) ⟨1052000, by rfl⟩ : syracuseStep 1402667 = 2104001) B2104001
theorem B943991 : Blo 550806 943991 := bstep (se 1 (by rfl) ⟨707993, by rfl⟩ : syracuseStep 943991 = 1415987) B1415987
theorem B550843 : Blo 550806 550843 := bstep (se 1 (by rfl) ⟨413132, by rfl⟩ : syracuseStep 550843 = 826265) B826265
theorem B550919 : Blo 550806 550919 := bstep (se 1 (by rfl) ⟨413189, by rfl⟩ : syracuseStep 550919 = 826379) B826379
theorem B550927 : Blo 550806 550927 := bstep (se 1 (by rfl) ⟨413195, by rfl⟩ : syracuseStep 550927 = 826391) B826391
theorem B550971 : Blo 550806 550971 := bstep (se 1 (by rfl) ⟨413228, by rfl⟩ : syracuseStep 550971 = 826457) B826457
theorem B551047 : Blo 550806 551047 := bstep (se 1 (by rfl) ⟨413285, by rfl⟩ : syracuseStep 551047 = 826571) B826571
theorem B551055 : Blo 550806 551055 := bstep (se 1 (by rfl) ⟨413291, by rfl⟩ : syracuseStep 551055 = 826583) B826583
theorem B551099 : Blo 550806 551099 := bstep (se 1 (by rfl) ⟨413324, by rfl⟩ : syracuseStep 551099 = 826649) B826649
theorem B551175 : Blo 550806 551175 := bstep (se 1 (by rfl) ⟨413381, by rfl⟩ : syracuseStep 551175 = 826763) B826763
theorem B551183 : Blo 550806 551183 := bstep (se 1 (by rfl) ⟨413387, by rfl⟩ : syracuseStep 551183 = 826775) B826775
theorem B551227 : Blo 550806 551227 := bstep (se 1 (by rfl) ⟨413420, by rfl⟩ : syracuseStep 551227 = 826841) B826841
theorem B2091379 : Blo 550806 2091379 := bstep (se 1 (by rfl) ⟨1568534, by rfl⟩ : syracuseStep 2091379 = 3137069) B3137069
theorem B551303 : Blo 550806 551303 := bstep (se 1 (by rfl) ⟨413477, by rfl⟩ : syracuseStep 551303 = 826955) B826955
theorem B551311 : Blo 550806 551311 := bstep (se 1 (by rfl) ⟨413483, by rfl⟩ : syracuseStep 551311 = 826967) B826967
theorem B3139985 : Blo 550806 3139985 := bstep (se 2 (by rfl) ⟨1177494, by rfl⟩ : syracuseStep 3139985 = 2354989) B2354989
theorem B4712849 : Blo 550806 4712849 := bstep (se 2 (by rfl) ⟨1767318, by rfl⟩ : syracuseStep 4712849 = 3534637) B3534637
theorem B1239443 : Blo 550806 1239443 := bstep (se 1 (by rfl) ⟨929582, by rfl⟩ : syracuseStep 1239443 = 1859165) B1859165
theorem B551355 : Blo 550806 551355 := bstep (se 1 (by rfl) ⟨413516, by rfl⟩ : syracuseStep 551355 = 827033) B827033
theorem B1239497 : Blo 550806 1239497 := bstep (se 2 (by rfl) ⟨464811, by rfl⟩ : syracuseStep 1239497 = 929623) B929623
theorem B551431 : Blo 550806 551431 := bstep (se 1 (by rfl) ⟨413573, by rfl⟩ : syracuseStep 551431 = 827147) B827147
theorem B551439 : Blo 550806 551439 := bstep (se 1 (by rfl) ⟨413579, by rfl⟩ : syracuseStep 551439 = 827159) B827159
theorem B551483 : Blo 550806 551483 := bstep (se 1 (by rfl) ⟨413612, by rfl⟩ : syracuseStep 551483 = 827225) B827225
theorem B1403507 : Blo 550806 1403507 := bstep (se 1 (by rfl) ⟨1052630, by rfl⟩ : syracuseStep 1403507 = 2105261) B2105261
theorem B551559 : Blo 550806 551559 := bstep (se 1 (by rfl) ⟨413669, by rfl⟩ : syracuseStep 551559 = 827339) B827339
theorem B1403527 : Blo 550806 1403527 := bstep (se 1 (by rfl) ⟨1052645, by rfl⟩ : syracuseStep 1403527 = 2105291) B2105291
theorem B551567 : Blo 550806 551567 := bstep (se 1 (by rfl) ⟨413675, by rfl⟩ : syracuseStep 551567 = 827351) B827351
theorem B551611 : Blo 550806 551611 := bstep (se 1 (by rfl) ⟨413708, by rfl⟩ : syracuseStep 551611 = 827417) B827417
theorem B551687 : Blo 550806 551687 := bstep (se 1 (by rfl) ⟨413765, by rfl⟩ : syracuseStep 551687 = 827531) B827531
theorem B551695 : Blo 550806 551695 := bstep (se 1 (by rfl) ⟨413771, by rfl⟩ : syracuseStep 551695 = 827543) B827543
theorem B551739 : Blo 550806 551739 := bstep (se 1 (by rfl) ⟨413804, by rfl⟩ : syracuseStep 551739 = 827609) B827609
theorem B1862459 : Blo 550806 1862459 := bstep (se 1 (by rfl) ⟨1396844, by rfl⟩ : syracuseStep 1862459 = 2793689) B2793689
theorem B3140441 : Blo 550806 3140441 := bstep (se 2 (by rfl) ⟨1177665, by rfl⟩ : syracuseStep 3140441 = 2355331) B2355331
theorem B551815 : Blo 550806 551815 := bstep (se 1 (by rfl) ⟨413861, by rfl⟩ : syracuseStep 551815 = 827723) B827723
theorem B551823 : Blo 550806 551823 := bstep (se 1 (by rfl) ⟨413867, by rfl⟩ : syracuseStep 551823 = 827735) B827735
theorem B1403801 : Blo 550806 1403801 := bstep (se 2 (by rfl) ⟨526425, by rfl⟩ : syracuseStep 1403801 = 1052851) B1052851
theorem B551867 : Blo 550806 551867 := bstep (se 1 (by rfl) ⟨413900, by rfl⟩ : syracuseStep 551867 = 827801) B827801
theorem B551943 : Blo 550806 551943 := bstep (se 1 (by rfl) ⟨413957, by rfl⟩ : syracuseStep 551943 = 827915) B827915
theorem B551951 : Blo 550806 551951 := bstep (se 1 (by rfl) ⟨413963, by rfl⟩ : syracuseStep 551951 = 827927) B827927
theorem B551995 : Blo 550806 551995 := bstep (se 1 (by rfl) ⟨413996, by rfl⟩ : syracuseStep 551995 = 827993) B827993
theorem B1403963 : Blo 550806 1403963 := bstep (se 1 (by rfl) ⟨1052972, by rfl⟩ : syracuseStep 1403963 = 2105945) B2105945
theorem B1240199 : Blo 550806 1240199 := bstep (se 1 (by rfl) ⟨930149, by rfl⟩ : syracuseStep 1240199 = 1860299) B1860299
theorem B552071 : Blo 550806 552071 := bstep (se 1 (by rfl) ⟨414053, by rfl⟩ : syracuseStep 552071 = 828107) B828107
theorem B552079 : Blo 550806 552079 := bstep (se 1 (by rfl) ⟨414059, by rfl⟩ : syracuseStep 552079 = 828119) B828119
theorem B552123 : Blo 550806 552123 := bstep (se 1 (by rfl) ⟨414092, by rfl⟩ : syracuseStep 552123 = 828185) B828185
theorem B3599597 : Blo 550806 3599597 := bstep (se 3 (by rfl) ⟨674924, by rfl⟩ : syracuseStep 3599597 = 1349849) B1349849
theorem B552199 : Blo 550806 552199 := bstep (se 1 (by rfl) ⟨414149, by rfl⟩ : syracuseStep 552199 = 828299) B828299
theorem B552207 : Blo 550806 552207 := bstep (se 1 (by rfl) ⟨414155, by rfl⟩ : syracuseStep 552207 = 828311) B828311
theorem B1404175 : Blo 550806 1404175 := bstep (se 1 (by rfl) ⟨1053131, by rfl⟩ : syracuseStep 1404175 = 2106263) B2106263
theorem B1862945 : Blo 550806 1862945 := bstep (se 2 (by rfl) ⟨698604, by rfl⟩ : syracuseStep 1862945 = 1397209) B1397209
theorem B1240379 : Blo 550806 1240379 := bstep (se 1 (by rfl) ⟨930284, by rfl⟩ : syracuseStep 1240379 = 1860569) B1860569
theorem B552251 : Blo 550806 552251 := bstep (se 1 (by rfl) ⟨414188, by rfl⟩ : syracuseStep 552251 = 828377) B828377
theorem B1699159 : Blo 550806 1699159 := bstep (se 1 (by rfl) ⟨1274369, by rfl⟩ : syracuseStep 1699159 = 2548739) B2548739
theorem B552327 : Blo 550806 552327 := bstep (se 1 (by rfl) ⟨414245, by rfl⟩ : syracuseStep 552327 = 828491) B828491
theorem B585095 : Blo 550806 585095 := bstep (se 1 (by rfl) ⟨438821, by rfl⟩ : syracuseStep 585095 = 877643) B877643
theorem B552335 : Blo 550806 552335 := bstep (se 1 (by rfl) ⟨414251, by rfl⟩ : syracuseStep 552335 = 828503) B828503
theorem B2354579 : Blo 550806 2354579 := bstep (se 1 (by rfl) ⟨1765934, by rfl⟩ : syracuseStep 2354579 = 3531869) B3531869
theorem B4713875 : Blo 550806 4713875 := bstep (se 1 (by rfl) ⟨3535406, by rfl⟩ : syracuseStep 4713875 = 7070813) B7070813
theorem B1240505 : Blo 550806 1240505 := bstep (se 2 (by rfl) ⟨465189, by rfl⟩ : syracuseStep 1240505 = 930379) B930379
theorem B552379 : Blo 550806 552379 := bstep (se 1 (by rfl) ⟨414284, by rfl⟩ : syracuseStep 552379 = 828569) B828569
theorem B552455 : Blo 550806 552455 := bstep (se 1 (by rfl) ⟨414341, by rfl⟩ : syracuseStep 552455 = 828683) B828683
theorem B552463 : Blo 550806 552463 := bstep (se 1 (by rfl) ⟨414347, by rfl⟩ : syracuseStep 552463 = 828695) B828695
theorem B552507 : Blo 550806 552507 := bstep (se 1 (by rfl) ⟨414380, by rfl⟩ : syracuseStep 552507 = 828761) B828761
theorem B552583 : Blo 550806 552583 := bstep (se 1 (by rfl) ⟨414437, by rfl⟩ : syracuseStep 552583 = 828875) B828875
theorem B552591 : Blo 550806 552591 := bstep (se 1 (by rfl) ⟨414443, by rfl⟩ : syracuseStep 552591 = 828887) B828887
theorem B12906161 : Blo 550806 12906161 := bstep (se 2 (by rfl) ⟨4839810, by rfl⟩ : syracuseStep 12906161 = 9679621) B9679621
theorem B552635 : Blo 550806 552635 := bstep (se 1 (by rfl) ⟨414476, by rfl⟩ : syracuseStep 552635 = 828953) B828953
theorem B552711 : Blo 550806 552711 := bstep (se 1 (by rfl) ⟨414533, by rfl⟩ : syracuseStep 552711 = 829067) B829067
theorem B1240847 : Blo 550806 1240847 := bstep (se 1 (by rfl) ⟨930635, by rfl⟩ : syracuseStep 1240847 = 1861271) B1861271
theorem B552719 : Blo 550806 552719 := bstep (se 1 (by rfl) ⟨414539, by rfl⟩ : syracuseStep 552719 = 829079) B829079
theorem B945935 : Blo 550806 945935 := bstep (se 1 (by rfl) ⟨709451, by rfl⟩ : syracuseStep 945935 = 1418903) B1418903
theorem B1240865 : Blo 550806 1240865 := bstep (se 2 (by rfl) ⟨465324, by rfl⟩ : syracuseStep 1240865 = 930649) B930649
theorem B552763 : Blo 550806 552763 := bstep (se 1 (by rfl) ⟨414572, by rfl⟩ : syracuseStep 552763 = 829145) B829145
theorem B1863539 : Blo 550806 1863539 := bstep (se 1 (by rfl) ⟨1397654, by rfl⟩ : syracuseStep 1863539 = 2795309) B2795309
theorem B552839 : Blo 550806 552839 := bstep (se 1 (by rfl) ⟨414629, by rfl⟩ : syracuseStep 552839 = 829259) B829259
theorem B552847 : Blo 550806 552847 := bstep (se 1 (by rfl) ⟨414635, by rfl⟩ : syracuseStep 552847 = 829271) B829271
theorem B552891 : Blo 550806 552891 := bstep (se 1 (by rfl) ⟨414668, by rfl⟩ : syracuseStep 552891 = 829337) B829337
theorem B552967 : Blo 550806 552967 := bstep (se 1 (by rfl) ⟨414725, by rfl⟩ : syracuseStep 552967 = 829451) B829451
theorem B552975 : Blo 550806 552975 := bstep (se 1 (by rfl) ⟨414731, by rfl⟩ : syracuseStep 552975 = 829463) B829463
theorem B2846749 : Blo 550806 2846749 := bstep (se 3 (by rfl) ⟨533765, by rfl⟩ : syracuseStep 2846749 = 1067531) B1067531
theorem B553019 : Blo 550806 553019 := bstep (se 1 (by rfl) ⟨414764, by rfl⟩ : syracuseStep 553019 = 829529) B829529
theorem B1241207 : Blo 550806 1241207 := bstep (se 1 (by rfl) ⟨930905, by rfl⟩ : syracuseStep 1241207 = 1861811) B1861811
theorem B553095 : Blo 550806 553095 := bstep (se 1 (by rfl) ⟨414821, by rfl⟩ : syracuseStep 553095 = 829643) B829643
theorem B553103 : Blo 550806 553103 := bstep (se 1 (by rfl) ⟨414827, by rfl⟩ : syracuseStep 553103 = 829655) B829655
theorem B553147 : Blo 550806 553147 := bstep (se 1 (by rfl) ⟨414860, by rfl⟩ : syracuseStep 553147 = 829721) B829721
theorem B1765577 : Blo 550806 1765577 := bstep (se 2 (by rfl) ⟨662091, by rfl⟩ : syracuseStep 1765577 = 1324183) B1324183
theorem B553223 : Blo 550806 553223 := bstep (se 1 (by rfl) ⟨414917, by rfl⟩ : syracuseStep 553223 = 829835) B829835
theorem B553231 : Blo 550806 553231 := bstep (se 1 (by rfl) ⟨414923, by rfl⟩ : syracuseStep 553231 = 829847) B829847
theorem B1241387 : Blo 550806 1241387 := bstep (se 1 (by rfl) ⟨931040, by rfl⟩ : syracuseStep 1241387 = 1862081) B1862081
theorem B553275 : Blo 550806 553275 := bstep (se 1 (by rfl) ⟨414956, by rfl⟩ : syracuseStep 553275 = 829913) B829913
theorem B553351 : Blo 550806 553351 := bstep (se 1 (by rfl) ⟨415013, by rfl⟩ : syracuseStep 553351 = 830027) B830027
theorem B553359 : Blo 550806 553359 := bstep (se 1 (by rfl) ⟨415019, by rfl⟩ : syracuseStep 553359 = 830039) B830039
theorem B1995155 : Blo 550806 1995155 := bstep (se 1 (by rfl) ⟨1496366, by rfl⟩ : syracuseStep 1995155 = 2992733) B2992733
theorem B1896851 : Blo 550806 1896851 := bstep (se 1 (by rfl) ⟨1422638, by rfl⟩ : syracuseStep 1896851 = 2845277) B2845277
theorem B553403 : Blo 550806 553403 := bstep (se 1 (by rfl) ⟨415052, by rfl⟩ : syracuseStep 553403 = 830105) B830105
theorem B553479 : Blo 550806 553479 := bstep (se 1 (by rfl) ⟨415109, by rfl⟩ : syracuseStep 553479 = 830219) B830219
theorem B553487 : Blo 550806 553487 := bstep (se 1 (by rfl) ⟨415115, by rfl⟩ : syracuseStep 553487 = 830231) B830231
theorem B2093597 : Blo 550806 2093597 := bstep (se 3 (by rfl) ⟨392549, by rfl⟩ : syracuseStep 2093597 = 785099) B785099
theorem B553531 : Blo 550806 553531 := bstep (se 1 (by rfl) ⟨415148, by rfl⟩ : syracuseStep 553531 = 830297) B830297
theorem B553607 : Blo 550806 553607 := bstep (se 1 (by rfl) ⟨415205, by rfl⟩ : syracuseStep 553607 = 830411) B830411
theorem B553615 : Blo 550806 553615 := bstep (se 1 (by rfl) ⟨415211, by rfl⟩ : syracuseStep 553615 = 830423) B830423
theorem B1241747 : Blo 550806 1241747 := bstep (se 1 (by rfl) ⟨931310, by rfl⟩ : syracuseStep 1241747 = 1862621) B1862621
theorem B553659 : Blo 550806 553659 := bstep (se 1 (by rfl) ⟨415244, by rfl⟩ : syracuseStep 553659 = 830489) B830489
theorem B1241801 : Blo 550806 1241801 := bstep (se 2 (by rfl) ⟨465675, by rfl⟩ : syracuseStep 1241801 = 931351) B931351
theorem B553735 : Blo 550806 553735 := bstep (se 1 (by rfl) ⟨415301, by rfl⟩ : syracuseStep 553735 = 830603) B830603
theorem B553743 : Blo 550806 553743 := bstep (se 1 (by rfl) ⟨415307, by rfl⟩ : syracuseStep 553743 = 830615) B830615
theorem B553787 : Blo 550806 553787 := bstep (se 1 (by rfl) ⟨415340, by rfl⟩ : syracuseStep 553787 = 830681) B830681
theorem B553863 : Blo 550806 553863 := bstep (se 1 (by rfl) ⟨415397, by rfl⟩ : syracuseStep 553863 = 830795) B830795
theorem B553871 : Blo 550806 553871 := bstep (se 1 (by rfl) ⟨415403, by rfl⟩ : syracuseStep 553871 = 830807) B830807
theorem B553915 : Blo 550806 553915 := bstep (se 1 (by rfl) ⟨415436, by rfl⟩ : syracuseStep 553915 = 830873) B830873
theorem B553991 : Blo 550806 553991 := bstep (se 1 (by rfl) ⟨415493, by rfl⟩ : syracuseStep 553991 = 830987) B830987
theorem B553999 : Blo 550806 553999 := bstep (se 1 (by rfl) ⟨415499, by rfl⟩ : syracuseStep 553999 = 830999) B830999
theorem B554043 : Blo 550806 554043 := bstep (se 1 (by rfl) ⟨415532, by rfl⟩ : syracuseStep 554043 = 831065) B831065
theorem B554119 : Blo 550806 554119 := bstep (se 1 (by rfl) ⟨415589, by rfl⟩ : syracuseStep 554119 = 831179) B831179
theorem B619663 : Blo 550806 619663 := bstep (se 1 (by rfl) ⟨464747, by rfl⟩ : syracuseStep 619663 = 929495) B929495
theorem B554127 : Blo 550806 554127 := bstep (se 1 (by rfl) ⟨415595, by rfl⟩ : syracuseStep 554127 = 831191) B831191
theorem B1176761 : Blo 550806 1176761 := bstep (se 2 (by rfl) ⟨441285, by rfl⟩ : syracuseStep 1176761 = 882571) B882571
theorem B554171 : Blo 550806 554171 := bstep (se 1 (by rfl) ⟨415628, by rfl⟩ : syracuseStep 554171 = 831257) B831257
theorem B1045705 : Blo 550806 1045705 := bstep (se 2 (by rfl) ⟨392139, by rfl⟩ : syracuseStep 1045705 = 784279) B784279
theorem B2094281 : Blo 550806 2094281 := bstep (se 2 (by rfl) ⟨785355, by rfl⟩ : syracuseStep 2094281 = 1570711) B1570711
theorem B554247 : Blo 550806 554247 := bstep (se 1 (by rfl) ⟨415685, by rfl⟩ : syracuseStep 554247 = 831371) B831371
theorem B1242383 : Blo 550806 1242383 := bstep (se 1 (by rfl) ⟨931787, by rfl⟩ : syracuseStep 1242383 = 1863575) B1863575
theorem B554255 : Blo 550806 554255 := bstep (se 1 (by rfl) ⟨415691, by rfl⟩ : syracuseStep 554255 = 831383) B831383
theorem B554299 : Blo 550806 554299 := bstep (se 1 (by rfl) ⟨415724, by rfl⟩ : syracuseStep 554299 = 831449) B831449
theorem B1242503 : Blo 550806 1242503 := bstep (se 1 (by rfl) ⟨931877, by rfl⟩ : syracuseStep 1242503 = 1863755) B1863755
theorem B554375 : Blo 550806 554375 := bstep (se 1 (by rfl) ⟨415781, by rfl⟩ : syracuseStep 554375 = 831563) B831563
theorem B554383 : Blo 550806 554383 := bstep (se 1 (by rfl) ⟨415787, by rfl⟩ : syracuseStep 554383 = 831575) B831575
theorem B554427 : Blo 550806 554427 := bstep (se 1 (by rfl) ⟨415820, by rfl⟩ : syracuseStep 554427 = 831641) B831641
theorem B554503 : Blo 550806 554503 := bstep (se 1 (by rfl) ⟨415877, by rfl⟩ : syracuseStep 554503 = 831755) B831755
theorem B554511 : Blo 550806 554511 := bstep (se 1 (by rfl) ⟨415883, by rfl⟩ : syracuseStep 554511 = 831767) B831767
theorem B1242683 : Blo 550806 1242683 := bstep (se 1 (by rfl) ⟨932012, by rfl⟩ : syracuseStep 1242683 = 1864025) B1864025
theorem B554555 : Blo 550806 554555 := bstep (se 1 (by rfl) ⟨415916, by rfl⟩ : syracuseStep 554555 = 831833) B831833
theorem B620167 : Blo 550806 620167 := bstep (se 1 (by rfl) ⟨465125, by rfl⟩ : syracuseStep 620167 = 930251) B930251
theorem B554631 : Blo 550806 554631 := bstep (se 1 (by rfl) ⟨415973, by rfl⟩ : syracuseStep 554631 = 831947) B831947
theorem B554639 : Blo 550806 554639 := bstep (se 1 (by rfl) ⟨415979, by rfl⟩ : syracuseStep 554639 = 831959) B831959
theorem B1242809 : Blo 550806 1242809 := bstep (se 2 (by rfl) ⟨466053, by rfl⟩ : syracuseStep 1242809 = 932107) B932107
theorem B554683 : Blo 550806 554683 := bstep (se 1 (by rfl) ⟨416012, by rfl⟩ : syracuseStep 554683 = 832025) B832025
theorem B554759 : Blo 550806 554759 := bstep (se 1 (by rfl) ⟨416069, by rfl⟩ : syracuseStep 554759 = 832139) B832139
theorem B554767 : Blo 550806 554767 := bstep (se 1 (by rfl) ⟨416075, by rfl⟩ : syracuseStep 554767 = 832151) B832151
theorem B620347 : Blo 550806 620347 := bstep (se 1 (by rfl) ⟨465260, by rfl⟩ : syracuseStep 620347 = 930521) B930521
theorem B4028249 : Blo 550806 4028249 := bstep (se 2 (by rfl) ⟨1510593, by rfl⟩ : syracuseStep 4028249 = 3021187) B3021187
theorem B1996697 : Blo 550806 1996697 := bstep (se 2 (by rfl) ⟨748761, by rfl⟩ : syracuseStep 1996697 = 1497523) B1497523
theorem B1570745 : Blo 550806 1570745 := bstep (se 2 (by rfl) ⟨589029, by rfl⟩ : syracuseStep 1570745 = 1178059) B1178059
theorem B3143609 : Blo 550806 3143609 := bstep (se 2 (by rfl) ⟨1178853, by rfl⟩ : syracuseStep 3143609 = 2357707) B2357707
theorem B784399 : Blo 550806 784399 := bstep (se 1 (by rfl) ⟨588299, by rfl⟩ : syracuseStep 784399 = 1176599) B1176599
theorem B1243151 : Blo 550806 1243151 := bstep (se 1 (by rfl) ⟨932363, by rfl⟩ : syracuseStep 1243151 = 1864727) B1864727
theorem B1243169 : Blo 550806 1243169 := bstep (se 2 (by rfl) ⟨466188, by rfl⟩ : syracuseStep 1243169 = 932377) B932377
theorem B1570859 : Blo 550806 1570859 := bstep (se 1 (by rfl) ⟨1178144, by rfl⟩ : syracuseStep 1570859 = 2356289) B2356289
theorem B13433033 : Blo 550806 13433033 := bstep (se 2 (by rfl) ⟨5037387, by rfl⟩ : syracuseStep 13433033 = 10074775) B10074775
theorem B620815 : Blo 550806 620815 := bstep (se 1 (by rfl) ⟨465611, by rfl⟩ : syracuseStep 620815 = 931223) B931223
theorem B1243511 : Blo 550806 1243511 := bstep (se 1 (by rfl) ⟨932633, by rfl⟩ : syracuseStep 1243511 = 1865267) B1865267
theorem B6289811 : Blo 550806 6289811 := bstep (se 1 (by rfl) ⟨4717358, by rfl⟩ : syracuseStep 6289811 = 9434717) B9434717
theorem B1866131 : Blo 550806 1866131 := bstep (se 1 (by rfl) ⟨1399598, by rfl⟩ : syracuseStep 1866131 = 2799197) B2799197
theorem B4192721 : Blo 550806 4192721 := bstep (se 2 (by rfl) ⟨1572270, by rfl⟩ : syracuseStep 4192721 = 3144541) B3144541
theorem B1243691 : Blo 550806 1243691 := bstep (se 1 (by rfl) ⟨932768, by rfl⟩ : syracuseStep 1243691 = 1865537) B1865537
theorem B588551 : Blo 550806 588551 := bstep (se 1 (by rfl) ⟨441413, by rfl⟩ : syracuseStep 588551 = 882827) B882827
theorem B621319 : Blo 550806 621319 := bstep (se 1 (by rfl) ⟨465989, by rfl⟩ : syracuseStep 621319 = 931979) B931979
theorem B1178383 : Blo 550806 1178383 := bstep (se 1 (by rfl) ⟨883787, by rfl⟩ : syracuseStep 1178383 = 1767575) B1767575
theorem B2358031 : Blo 550806 2358031 := bstep (se 1 (by rfl) ⟨1768523, by rfl⟩ : syracuseStep 2358031 = 3537047) B3537047
theorem B1178401 : Blo 550806 1178401 := bstep (se 2 (by rfl) ⟨441900, by rfl⟩ : syracuseStep 1178401 = 883801) B883801
theorem B1244051 : Blo 550806 1244051 := bstep (se 1 (by rfl) ⟨933038, by rfl⟩ : syracuseStep 1244051 = 1866077) B1866077
theorem B2096057 : Blo 550806 2096057 := bstep (se 2 (by rfl) ⟨786021, by rfl⟩ : syracuseStep 2096057 = 1572043) B1572043
theorem B621499 : Blo 550806 621499 := bstep (se 1 (by rfl) ⟨466124, by rfl⟩ : syracuseStep 621499 = 932249) B932249
theorem B1244105 : Blo 550806 1244105 := bstep (se 2 (by rfl) ⟨466539, by rfl⟩ : syracuseStep 1244105 = 933079) B933079
theorem B785543 : Blo 550806 785543 := bstep (se 1 (by rfl) ⟨589157, by rfl⟩ : syracuseStep 785543 = 1178315) B1178315
theorem B1178759 : Blo 550806 1178759 := bstep (se 1 (by rfl) ⟨884069, by rfl⟩ : syracuseStep 1178759 = 1768139) B1768139
theorem B1571987 : Blo 550806 1571987 := bstep (se 1 (by rfl) ⟨1178990, by rfl⟩ : syracuseStep 1571987 = 2357981) B2357981
theorem B2653499 : Blo 550806 2653499 := bstep (se 1 (by rfl) ⟨1990124, by rfl⟩ : syracuseStep 2653499 = 3980249) B3980249
theorem B785737 : Blo 550806 785737 := bstep (se 2 (by rfl) ⟨294651, by rfl⟩ : syracuseStep 785737 = 589303) B589303
theorem B621967 : Blo 550806 621967 := bstep (se 1 (by rfl) ⟨466475, by rfl⟩ : syracuseStep 621967 = 932951) B932951
theorem B589243 : Blo 550806 589243 := bstep (se 1 (by rfl) ⟨441932, by rfl⟩ : syracuseStep 589243 = 883865) B883865
theorem B1572385 : Blo 550806 1572385 := bstep (se 2 (by rfl) ⟨589644, by rfl⟩ : syracuseStep 1572385 = 1179289) B1179289
theorem B1244807 : Blo 550806 1244807 := bstep (se 1 (by rfl) ⟨933605, by rfl⟩ : syracuseStep 1244807 = 1867211) B1867211
theorem B1048211 : Blo 550806 1048211 := bstep (se 1 (by rfl) ⟨786158, by rfl⟩ : syracuseStep 1048211 = 1572317) B1572317
theorem B1867535 : Blo 550806 1867535 := bstep (se 1 (by rfl) ⟨1400651, by rfl⟩ : syracuseStep 1867535 = 2801303) B2801303
theorem B1244987 : Blo 550806 1244987 := bstep (se 1 (by rfl) ⟨933740, by rfl⟩ : syracuseStep 1244987 = 1867481) B1867481
theorem B786295 : Blo 550806 786295 := bstep (se 1 (by rfl) ⟨589721, by rfl⟩ : syracuseStep 786295 = 1179443) B1179443
theorem B1048439 : Blo 550806 1048439 := bstep (se 1 (by rfl) ⟨786329, by rfl⟩ : syracuseStep 1048439 = 1572659) B1572659
theorem B622471 : Blo 550806 622471 := bstep (se 1 (by rfl) ⟨466853, by rfl⟩ : syracuseStep 622471 = 933707) B933707
theorem B1245113 : Blo 550806 1245113 := bstep (se 2 (by rfl) ⟨466917, by rfl⟩ : syracuseStep 1245113 = 933835) B933835
theorem B1245203 : Blo 550806 1245203 := bstep (se 1 (by rfl) ⟨933902, by rfl⟩ : syracuseStep 1245203 = 1867805) B1867805
theorem B3145817 : Blo 550806 3145817 := bstep (se 2 (by rfl) ⟨1179681, by rfl⟩ : syracuseStep 3145817 = 2359363) B2359363
theorem B2130077 : Blo 550806 2130077 := bstep (se 3 (by rfl) ⟨399389, by rfl⟩ : syracuseStep 2130077 = 798779) B798779
theorem B1441963 : Blo 550806 1441963 := bstep (se 1 (by rfl) ⟨1081472, by rfl⟩ : syracuseStep 1441963 = 2162945) B2162945
theorem B4194665 : Blo 550806 4194665 := bstep (se 2 (by rfl) ⟨1572999, by rfl⟩ : syracuseStep 4194665 = 3145999) B3145999
theorem B1245545 : Blo 550806 1245545 := bstep (se 2 (by rfl) ⟨467079, by rfl⟩ : syracuseStep 1245545 = 934159) B934159
theorem B1049107 : Blo 550806 1049107 := bstep (se 1 (by rfl) ⟨786830, by rfl⟩ : syracuseStep 1049107 = 1573661) B1573661
theorem B3146273 : Blo 550806 3146273 := bstep (se 2 (by rfl) ⟨1179852, by rfl⟩ : syracuseStep 3146273 = 2359705) B2359705
theorem B2097697 : Blo 550806 2097697 := bstep (se 2 (by rfl) ⟨786636, by rfl⟩ : syracuseStep 2097697 = 1573273) B1573273
theorem B885287 : Blo 550806 885287 := bstep (se 1 (by rfl) ⟨663965, by rfl⟩ : syracuseStep 885287 = 1327931) B1327931
theorem B932774453 : Blo 550806 932774453 := bstep (se 5 (by rfl) ⟨43723802, by rfl⟩ : syracuseStep 932774453 = 87447605) B87447605
theorem B623227 : Blo 550806 623227 := bstep (se 1 (by rfl) ⟨467420, by rfl⟩ : syracuseStep 623227 = 934841) B934841
theorem B53609111 : Blo 550806 53609111 := bstep (se 1 (by rfl) ⟨40206833, by rfl⟩ : syracuseStep 53609111 = 80413667) B80413667
theorem B3146525 : Blo 550806 3146525 := bstep (se 3 (by rfl) ⟨589973, by rfl⟩ : syracuseStep 3146525 = 1179947) B1179947
theorem B5964617 : Blo 550806 5964617 := bstep (se 2 (by rfl) ⟨2236731, by rfl⟩ : syracuseStep 5964617 = 4473463) B4473463
theorem B1049449 : Blo 550806 1049449 := bstep (se 2 (by rfl) ⟨393543, by rfl⟩ : syracuseStep 1049449 = 787087) B787087
theorem B1246139 : Blo 550806 1246139 := bstep (se 1 (by rfl) ⟨934604, by rfl⟩ : syracuseStep 1246139 = 1869209) B1869209
theorem B3539969 : Blo 550806 3539969 := bstep (se 2 (by rfl) ⟨1327488, by rfl⟩ : syracuseStep 3539969 = 2654977) B2654977
theorem B2098183 : Blo 550806 2098183 := bstep (se 1 (by rfl) ⟨1573637, by rfl⟩ : syracuseStep 2098183 = 3147275) B3147275
theorem B5309489 : Blo 550806 5309489 := bstep (se 2 (by rfl) ⟨1991058, by rfl⟩ : syracuseStep 5309489 = 3982117) B3982117
theorem B1246265 : Blo 550806 1246265 := bstep (se 2 (by rfl) ⟨467349, by rfl⟩ : syracuseStep 1246265 = 934699) B934699
theorem B623695 : Blo 550806 623695 := bstep (se 1 (by rfl) ⟨467771, by rfl⟩ : syracuseStep 623695 = 935543) B935543
theorem B6980825 : Blo 550806 6980825 := bstep (se 2 (by rfl) ⟨2617809, by rfl⟩ : syracuseStep 6980825 = 5235619) B5235619
theorem B1869047 : Blo 550806 1869047 := bstep (se 1 (by rfl) ⟨1401785, by rfl⟩ : syracuseStep 1869047 = 2803571) B2803571
theorem B1246607 : Blo 550806 1246607 := bstep (se 1 (by rfl) ⟨934955, by rfl⟩ : syracuseStep 1246607 = 1869911) B1869911
theorem B55248277 : Blo 550806 55248277 := bstep (se 6 (by rfl) ⟨1294881, by rfl⟩ : syracuseStep 55248277 = 2589763) B2589763
theorem B624091 : Blo 550806 624091 := bstep (se 1 (by rfl) ⟨468068, by rfl⟩ : syracuseStep 624091 = 936137) B936137
theorem B2098669 : Blo 550806 2098669 := bstep (se 3 (by rfl) ⟨393500, by rfl⟩ : syracuseStep 2098669 = 787001) B787001
theorem B1869371 : Blo 550806 1869371 := bstep (se 1 (by rfl) ⟨1402028, by rfl⟩ : syracuseStep 1869371 = 2804057) B2804057
theorem B1246931 : Blo 550806 1246931 := bstep (se 1 (by rfl) ⟨935198, by rfl⟩ : syracuseStep 1246931 = 1870397) B1870397
theorem B2098973 : Blo 550806 2098973 := bstep (se 3 (by rfl) ⟨393557, by rfl⟩ : syracuseStep 2098973 = 787115) B787115
theorem B8980267 : Blo 550806 8980267 := bstep (se 1 (by rfl) ⟨6735200, by rfl⟩ : syracuseStep 8980267 = 13470401) B13470401
theorem B886601 : Blo 550806 886601 := bstep (se 2 (by rfl) ⟨332475, by rfl⟩ : syracuseStep 886601 = 664951) B664951
theorem B1869641 : Blo 550806 1869641 := bstep (se 2 (by rfl) ⟨701115, by rfl⟩ : syracuseStep 1869641 = 1402231) B1402231
theorem B3540995 : Blo 550806 3540995 := bstep (se 1 (by rfl) ⟨2655746, by rfl⟩ : syracuseStep 3540995 = 5311493) B5311493
theorem B4491301 : Blo 550806 4491301 := bstep (se 4 (by rfl) ⟨421059, by rfl⟩ : syracuseStep 4491301 = 842119) B842119
theorem B1050823 : Blo 550806 1050823 := bstep (se 1 (by rfl) ⟨788117, by rfl⟩ : syracuseStep 1050823 = 1576235) B1576235
theorem B4196609 : Blo 550806 4196609 := bstep (se 2 (by rfl) ⟨1573728, by rfl⟩ : syracuseStep 4196609 = 3147457) B3147457
theorem B1247867 : Blo 550806 1247867 := bstep (se 1 (by rfl) ⟨935900, by rfl⟩ : syracuseStep 1247867 = 1871801) B1871801
theorem B1247993 : Blo 550806 1247993 := bstep (se 2 (by rfl) ⟨467997, by rfl⟩ : syracuseStep 1247993 = 935995) B935995
theorem B887735 : Blo 550806 887735 := bstep (se 1 (by rfl) ⟨665801, by rfl⟩ : syracuseStep 887735 = 1331603) B1331603
theorem B1870775 : Blo 550806 1870775 := bstep (se 1 (by rfl) ⟨1403081, by rfl⟩ : syracuseStep 1870775 = 2806163) B2806163
theorem B1248263 : Blo 550806 1248263 := bstep (se 1 (by rfl) ⟨936197, by rfl⟩ : syracuseStep 1248263 = 1872395) B1872395
theorem B2788505 : Blo 550806 2788505 := bstep (se 2 (by rfl) ⟨1045689, by rfl⟩ : syracuseStep 2788505 = 2091379) B2091379
theorem B4787545 : Blo 550806 4787545 := bstep (se 2 (by rfl) ⟨1795329, by rfl⟩ : syracuseStep 4787545 = 3590659) B3590659
theorem B3313021 : Blo 550806 3313021 := bstep (se 3 (by rfl) ⟨621191, by rfl⟩ : syracuseStep 3313021 = 1242383) B1242383
theorem B2133373 : Blo 550806 2133373 := bstep (se 3 (by rfl) ⟨400007, by rfl⟩ : syracuseStep 2133373 = 800015) B800015
theorem B888247 : Blo 550806 888247 := bstep (se 1 (by rfl) ⟨666185, by rfl⟩ : syracuseStep 888247 = 1332371) B1332371
theorem B1871369 : Blo 550806 1871369 := bstep (se 2 (by rfl) ⟨701763, by rfl⟩ : syracuseStep 1871369 = 1403527) B1403527
theorem B32280371 : Blo 550806 32280371 := bstep (se 1 (by rfl) ⟨24210278, by rfl⟩ : syracuseStep 32280371 = 48420557) B48420557
theorem B5672771 : Blo 550806 5672771 := bstep (se 1 (by rfl) ⟨4254578, by rfl⟩ : syracuseStep 5672771 = 8509157) B8509157
theorem B1773407 : Blo 550806 1773407 := bstep (se 1 (by rfl) ⟨1330055, by rfl⟩ : syracuseStep 1773407 = 2660111) B2660111
theorem B2101099 : Blo 550806 2101099 := bstep (se 1 (by rfl) ⟨1575824, by rfl⟩ : syracuseStep 2101099 = 3151649) B3151649
theorem B1183663 : Blo 550806 1183663 := bstep (se 1 (by rfl) ⟨887747, by rfl⟩ : syracuseStep 1183663 = 1775495) B1775495
theorem B1347511 : Blo 550806 1347511 := bstep (se 1 (by rfl) ⟨1010633, by rfl⟩ : syracuseStep 1347511 = 2021267) B2021267
theorem B757883 : Blo 550806 757883 := bstep (se 1 (by rfl) ⟨568412, by rfl⟩ : syracuseStep 757883 = 1136825) B1136825
theorem B4559165 : Blo 550806 4559165 := bstep (se 3 (by rfl) ⟨854843, by rfl⟩ : syracuseStep 4559165 = 1709687) B1709687
theorem B1872233 : Blo 550806 1872233 := bstep (se 2 (by rfl) ⟨702087, by rfl⟩ : syracuseStep 1872233 = 1404175) B1404175
theorem B1053071 : Blo 550806 1053071 := bstep (se 1 (by rfl) ⟨789803, by rfl⟩ : syracuseStep 1053071 = 1579607) B1579607
theorem B2265545 : Blo 550806 2265545 := bstep (se 2 (by rfl) ⟨849579, by rfl⟩ : syracuseStep 2265545 = 1699159) B1699159
theorem B3543533 : Blo 550806 3543533 := bstep (se 3 (by rfl) ⟨664412, by rfl⟩ : syracuseStep 3543533 = 1328825) B1328825
theorem B331321873 : Blo 550806 331321873 := bstep (se 2 (by rfl) ⟨124245702, by rfl⟩ : syracuseStep 331321873 = 248491405) B248491405
theorem B4723373 : Blo 550806 4723373 := bstep (se 3 (by rfl) ⟨885632, by rfl⟩ : syracuseStep 4723373 = 1771265) B1771265
theorem B19928065 : Blo 550806 19928065 := bstep (se 2 (by rfl) ⟨7473024, by rfl⟩ : syracuseStep 19928065 = 14946049) B14946049
theorem B1119251 : Blo 550806 1119251 := bstep (se 1 (by rfl) ⟨839438, by rfl⟩ : syracuseStep 1119251 = 1678877) B1678877
theorem B3150899 : Blo 550806 3150899 := bstep (se 1 (by rfl) ⟨2363174, by rfl⟩ : syracuseStep 3150899 = 4726349) B4726349
theorem B1774649 : Blo 550806 1774649 := bstep (se 2 (by rfl) ⟨665493, by rfl⟩ : syracuseStep 1774649 = 1330987) B1330987
theorem B13604111 : Blo 550806 13604111 := bstep (se 1 (by rfl) ⟨10203083, by rfl⟩ : syracuseStep 13604111 = 20406167) B20406167
theorem B2364815 : Blo 550806 2364815 := bstep (se 1 (by rfl) ⟨1773611, by rfl⟩ : syracuseStep 2364815 = 3547223) B3547223
theorem B5969371 : Blo 550806 5969371 := bstep (se 1 (by rfl) ⟨4477028, by rfl⟩ : syracuseStep 5969371 = 8954057) B8954057
theorem B2364967 : Blo 550806 2364967 := bstep (se 1 (by rfl) ⟨1773725, by rfl⟩ : syracuseStep 2364967 = 3547451) B3547451
theorem B8722235 : Blo 550806 8722235 := bstep (se 1 (by rfl) ⟨6541676, by rfl⟩ : syracuseStep 8722235 = 13083353) B13083353
theorem B8984675 : Blo 550806 8984675 := bstep (se 1 (by rfl) ⟨6738506, by rfl⟩ : syracuseStep 8984675 = 13477013) B13477013
theorem B2234753 : Blo 550806 2234753 := bstep (se 2 (by rfl) ⟨838032, by rfl⟩ : syracuseStep 2234753 = 1676065) B1676065
theorem B4200983 : Blo 550806 4200983 := bstep (se 1 (by rfl) ⟨3150737, by rfl⟩ : syracuseStep 4200983 = 6301475) B6301475
theorem B2103833 : Blo 550806 2103833 := bstep (se 2 (by rfl) ⟨788937, by rfl⟩ : syracuseStep 2103833 = 1577875) B1577875
theorem B12098117 : Blo 550806 12098117 := bstep (se 4 (by rfl) ⟨1134198, by rfl⟩ : syracuseStep 12098117 = 2268397) B2268397
theorem B629327 : Blo 550806 629327 := bstep (se 1 (by rfl) ⟨471995, by rfl⟩ : syracuseStep 629327 = 943991) B943991
theorem B826217 : Blo 550806 826217 := bstep (se 2 (by rfl) ⟨309831, by rfl⟩ : syracuseStep 826217 = 619663) B619663
theorem B826295 : Blo 550806 826295 := bstep (se 1 (by rfl) ⟨619721, by rfl⟩ : syracuseStep 826295 = 1239443) B1239443
theorem B826331 : Blo 550806 826331 := bstep (se 1 (by rfl) ⟨619748, by rfl⟩ : syracuseStep 826331 = 1239497) B1239497
theorem B4037597 : Blo 550806 4037597 := bstep (se 3 (by rfl) ⟨757049, by rfl⟩ : syracuseStep 4037597 = 1514099) B1514099
theorem B826799 : Blo 550806 826799 := bstep (se 1 (by rfl) ⟨620099, by rfl⟩ : syracuseStep 826799 = 1240199) B1240199
theorem B826889 : Blo 550806 826889 := bstep (se 2 (by rfl) ⟨310083, by rfl⟩ : syracuseStep 826889 = 620167) B620167
theorem B826919 : Blo 550806 826919 := bstep (se 1 (by rfl) ⟨620189, by rfl⟩ : syracuseStep 826919 = 1240379) B1240379
theorem B827003 : Blo 550806 827003 := bstep (se 1 (by rfl) ⟨620252, by rfl⟩ : syracuseStep 827003 = 1240505) B1240505
theorem B827129 : Blo 550806 827129 := bstep (se 2 (by rfl) ⟨310173, by rfl⟩ : syracuseStep 827129 = 620347) B620347
theorem B827231 : Blo 550806 827231 := bstep (se 1 (by rfl) ⟨620423, by rfl⟩ : syracuseStep 827231 = 1240847) B1240847
theorem B630623 : Blo 550806 630623 := bstep (se 1 (by rfl) ⟨472967, by rfl⟩ : syracuseStep 630623 = 945935) B945935
theorem B827243 : Blo 550806 827243 := bstep (se 1 (by rfl) ⟨620432, by rfl⟩ : syracuseStep 827243 = 1240865) B1240865
theorem B827471 : Blo 550806 827471 := bstep (se 1 (by rfl) ⟨620603, by rfl⟩ : syracuseStep 827471 = 1241207) B1241207
theorem B2105459 : Blo 550806 2105459 := bstep (se 1 (by rfl) ⟨1579094, by rfl⟩ : syracuseStep 2105459 = 3158189) B3158189
theorem B827591 : Blo 550806 827591 := bstep (se 1 (by rfl) ⟨620693, by rfl⟩ : syracuseStep 827591 = 1241387) B1241387
theorem B827753 : Blo 550806 827753 := bstep (se 2 (by rfl) ⟨310407, by rfl⟩ : syracuseStep 827753 = 620815) B620815
theorem B827831 : Blo 550806 827831 := bstep (se 1 (by rfl) ⟨620873, by rfl⟩ : syracuseStep 827831 = 1241747) B1241747
theorem B827867 : Blo 550806 827867 := bstep (se 1 (by rfl) ⟨620900, by rfl⟩ : syracuseStep 827867 = 1241801) B1241801
theorem B1417753 : Blo 550806 1417753 := bstep (se 2 (by rfl) ⟨531657, by rfl⟩ : syracuseStep 1417753 = 1063315) B1063315
theorem B828335 : Blo 550806 828335 := bstep (se 1 (by rfl) ⟨621251, by rfl⟩ : syracuseStep 828335 = 1242503) B1242503
theorem B828425 : Blo 550806 828425 := bstep (se 2 (by rfl) ⟨310659, by rfl⟩ : syracuseStep 828425 = 621319) B621319
theorem B828455 : Blo 550806 828455 := bstep (se 1 (by rfl) ⟨621341, by rfl⟩ : syracuseStep 828455 = 1242683) B1242683
theorem B828539 : Blo 550806 828539 := bstep (se 1 (by rfl) ⟨621404, by rfl⟩ : syracuseStep 828539 = 1242809) B1242809
theorem B40412357 : Blo 550806 40412357 := bstep (se 4 (by rfl) ⟨3788658, by rfl⟩ : syracuseStep 40412357 = 7577317) B7577317
theorem B828665 : Blo 550806 828665 := bstep (se 2 (by rfl) ⟨310749, by rfl⟩ : syracuseStep 828665 = 621499) B621499
theorem B828767 : Blo 550806 828767 := bstep (se 1 (by rfl) ⟨621575, by rfl⟩ : syracuseStep 828767 = 1243151) B1243151
theorem B796009 : Blo 550806 796009 := bstep (se 2 (by rfl) ⟨298503, by rfl⟩ : syracuseStep 796009 = 597007) B597007
theorem B828779 : Blo 550806 828779 := bstep (se 1 (by rfl) ⟨621584, by rfl⟩ : syracuseStep 828779 = 1243169) B1243169
theorem B8955355 : Blo 550806 8955355 := bstep (se 1 (by rfl) ⟨6716516, by rfl⟩ : syracuseStep 8955355 = 13433033) B13433033
theorem B829007 : Blo 550806 829007 := bstep (se 1 (by rfl) ⟨621755, by rfl⟩ : syracuseStep 829007 = 1243511) B1243511
theorem B665167 : Blo 550806 665167 := bstep (se 1 (by rfl) ⟨498875, by rfl⟩ : syracuseStep 665167 = 997751) B997751
theorem B2795147 : Blo 550806 2795147 := bstep (se 1 (by rfl) ⟨2096360, by rfl⟩ : syracuseStep 2795147 = 4192721) B4192721
theorem B829127 : Blo 550806 829127 := bstep (se 1 (by rfl) ⟨621845, by rfl⟩ : syracuseStep 829127 = 1243691) B1243691
theorem B3155705 : Blo 550806 3155705 := bstep (se 2 (by rfl) ⟨1183389, by rfl⟩ : syracuseStep 3155705 = 2366779) B2366779
theorem B7087931 : Blo 550806 7087931 := bstep (se 1 (by rfl) ⟨5315948, by rfl⟩ : syracuseStep 7087931 = 10631897) B10631897
theorem B829289 : Blo 550806 829289 := bstep (se 2 (by rfl) ⟨310983, by rfl⟩ : syracuseStep 829289 = 621967) B621967
theorem B4269943 : Blo 550806 4269943 := bstep (se 1 (by rfl) ⟨3202457, by rfl⟩ : syracuseStep 4269943 = 6404915) B6404915
theorem B829367 : Blo 550806 829367 := bstep (se 1 (by rfl) ⟨622025, by rfl⟩ : syracuseStep 829367 = 1244051) B1244051
theorem B829403 : Blo 550806 829403 := bstep (se 1 (by rfl) ⟨622052, by rfl⟩ : syracuseStep 829403 = 1244105) B1244105
theorem B829871 : Blo 550806 829871 := bstep (se 1 (by rfl) ⟨622403, by rfl⟩ : syracuseStep 829871 = 1244807) B1244807
theorem B698807 : Blo 550806 698807 := bstep (se 1 (by rfl) ⟨524105, by rfl⟩ : syracuseStep 698807 = 1048211) B1048211
theorem B829961 : Blo 550806 829961 := bstep (se 2 (by rfl) ⟨311235, by rfl⟩ : syracuseStep 829961 = 622471) B622471
theorem B829991 : Blo 550806 829991 := bstep (se 1 (by rfl) ⟨622493, by rfl⟩ : syracuseStep 829991 = 1244987) B1244987
theorem B698959 : Blo 550806 698959 := bstep (se 1 (by rfl) ⟨524219, by rfl⟩ : syracuseStep 698959 = 1048439) B1048439
theorem B830075 : Blo 550806 830075 := bstep (se 1 (by rfl) ⟨622556, by rfl⟩ : syracuseStep 830075 = 1245113) B1245113
theorem B830201 : Blo 550806 830201 := bstep (se 2 (by rfl) ⟨311325, by rfl⟩ : syracuseStep 830201 = 622651) B622651
theorem B830303 : Blo 550806 830303 := bstep (se 1 (by rfl) ⟨622727, by rfl⟩ : syracuseStep 830303 = 1245455) B1245455
theorem B830315 : Blo 550806 830315 := bstep (se 1 (by rfl) ⟨622736, by rfl⟩ : syracuseStep 830315 = 1245473) B1245473
theorem B830543 : Blo 550806 830543 := bstep (se 1 (by rfl) ⟨622907, by rfl⟩ : syracuseStep 830543 = 1245815) B1245815
theorem B3157163 : Blo 550806 3157163 := bstep (se 1 (by rfl) ⟨2367872, by rfl⟩ : syracuseStep 3157163 = 4735745) B4735745
theorem B830663 : Blo 550806 830663 := bstep (se 1 (by rfl) ⟨622997, by rfl⟩ : syracuseStep 830663 = 1245995) B1245995
theorem B830825 : Blo 550806 830825 := bstep (se 2 (by rfl) ⟨311559, by rfl⟩ : syracuseStep 830825 = 623119) B623119
theorem B830903 : Blo 550806 830903 := bstep (se 1 (by rfl) ⟨623177, by rfl⟩ : syracuseStep 830903 = 1246355) B1246355
theorem B830939 : Blo 550806 830939 := bstep (se 1 (by rfl) ⟨623204, by rfl⟩ : syracuseStep 830939 = 1246409) B1246409
theorem B700103 : Blo 550806 700103 := bstep (se 1 (by rfl) ⟨525077, by rfl⟩ : syracuseStep 700103 = 1050155) B1050155
theorem B4206329 : Blo 550806 4206329 := bstep (se 2 (by rfl) ⟨1577373, by rfl⟩ : syracuseStep 4206329 = 3154747) B3154747
theorem B3354463 : Blo 550806 3354463 := bstep (se 1 (by rfl) ⟨2515847, by rfl⟩ : syracuseStep 3354463 = 5031695) B5031695
theorem B700255 : Blo 550806 700255 := bstep (se 1 (by rfl) ⟨525191, by rfl⟩ : syracuseStep 700255 = 1050383) B1050383
theorem B929711 : Blo 550806 929711 := bstep (se 1 (by rfl) ⟨697283, by rfl⟩ : syracuseStep 929711 = 1394567) B1394567
theorem B831407 : Blo 550806 831407 := bstep (se 1 (by rfl) ⟨623555, by rfl⟩ : syracuseStep 831407 = 1247111) B1247111
theorem B831497 : Blo 550806 831497 := bstep (se 2 (by rfl) ⟨311811, by rfl⟩ : syracuseStep 831497 = 623623) B623623
theorem B831527 : Blo 550806 831527 := bstep (se 1 (by rfl) ⟨623645, by rfl⟩ : syracuseStep 831527 = 1247291) B1247291
theorem B831611 : Blo 550806 831611 := bstep (se 1 (by rfl) ⟨623708, by rfl⟩ : syracuseStep 831611 = 1247417) B1247417
theorem B831737 : Blo 550806 831737 := bstep (se 2 (by rfl) ⟨311901, by rfl⟩ : syracuseStep 831737 = 623803) B623803
theorem B930143 : Blo 550806 930143 := bstep (se 1 (by rfl) ⟨697607, by rfl⟩ : syracuseStep 930143 = 1395215) B1395215
theorem B831839 : Blo 550806 831839 := bstep (se 1 (by rfl) ⟨623879, by rfl⟩ : syracuseStep 831839 = 1247759) B1247759
theorem B831851 : Blo 550806 831851 := bstep (se 1 (by rfl) ⟨623888, by rfl⟩ : syracuseStep 831851 = 1247777) B1247777
theorem B832079 : Blo 550806 832079 := bstep (se 1 (by rfl) ⟨624059, by rfl⟩ : syracuseStep 832079 = 1248119) B1248119
theorem B832199 : Blo 550806 832199 := bstep (se 1 (by rfl) ⟨624149, by rfl⟩ : syracuseStep 832199 = 1248299) B1248299
theorem B930703 : Blo 550806 930703 := bstep (se 1 (by rfl) ⟨698027, by rfl⟩ : syracuseStep 930703 = 1396055) B1396055
theorem B4207787 : Blo 550806 4207787 := bstep (se 1 (by rfl) ⟨3155840, by rfl⟩ : syracuseStep 4207787 = 6311681) B6311681
theorem B3978659 : Blo 550806 3978659 := bstep (se 1 (by rfl) ⟨2983994, by rfl⟩ : syracuseStep 3978659 = 5967989) B5967989
theorem B7091621 : Blo 550806 7091621 := bstep (se 4 (by rfl) ⟨664839, by rfl⟩ : syracuseStep 7091621 = 1329679) B1329679
theorem B931385 : Blo 550806 931385 := bstep (se 2 (by rfl) ⟨349269, by rfl⟩ : syracuseStep 931385 = 698539) B698539
theorem B4208273 : Blo 550806 4208273 := bstep (se 2 (by rfl) ⟨1578102, by rfl⟩ : syracuseStep 4208273 = 3156205) B3156205
theorem B3553091 : Blo 550806 3553091 := bstep (se 1 (by rfl) ⟨2664818, by rfl⟩ : syracuseStep 3553091 = 5329637) B5329637
theorem B3192671 : Blo 550806 3192671 := bstep (se 1 (by rfl) ⟨2394503, by rfl⟩ : syracuseStep 3192671 = 4789007) B4789007
theorem B2799521 : Blo 550806 2799521 := bstep (se 2 (by rfl) ⟨1049820, by rfl⟩ : syracuseStep 2799521 = 2099641) B2099641
theorem B6305849 : Blo 550806 6305849 := bstep (se 2 (by rfl) ⟨2364693, by rfl⟩ : syracuseStep 6305849 = 4729387) B4729387
theorem B1325135 : Blo 550806 1325135 := bstep (se 1 (by rfl) ⟨993851, by rfl⟩ : syracuseStep 1325135 = 1987703) B1987703
theorem B932087 : Blo 550806 932087 := bstep (se 1 (by rfl) ⟨699065, by rfl⟩ : syracuseStep 932087 = 1398131) B1398131
theorem B997895 : Blo 550806 997895 := bstep (se 1 (by rfl) ⟨748421, by rfl⟩ : syracuseStep 997895 = 1496843) B1496843
theorem B932431 : Blo 550806 932431 := bstep (se 1 (by rfl) ⟨699323, by rfl⟩ : syracuseStep 932431 = 1398647) B1398647
theorem B997967 : Blo 550806 997967 := bstep (se 1 (by rfl) ⟨748475, by rfl⟩ : syracuseStep 997967 = 1496951) B1496951
theorem B932681 : Blo 550806 932681 := bstep (se 2 (by rfl) ⟨349755, by rfl⟩ : syracuseStep 932681 = 699511) B699511
theorem B2866103 : Blo 550806 2866103 := bstep (se 1 (by rfl) ⟨2149577, by rfl⟩ : syracuseStep 2866103 = 4299155) B4299155
theorem B4209731 : Blo 550806 4209731 := bstep (se 1 (by rfl) ⟨3157298, by rfl⟩ : syracuseStep 4209731 = 6314597) B6314597
theorem B933113 : Blo 550806 933113 := bstep (se 2 (by rfl) ⟨349917, by rfl⟩ : syracuseStep 933113 = 699835) B699835
theorem B2243965 : Blo 550806 2243965 := bstep (se 3 (by rfl) ⟨420743, by rfl⟩ : syracuseStep 2243965 = 841487) B841487
theorem B933295 : Blo 550806 933295 := bstep (se 1 (by rfl) ⟨699971, by rfl⟩ : syracuseStep 933295 = 1399943) B1399943
theorem B933383 : Blo 550806 933383 := bstep (se 1 (by rfl) ⟨700037, by rfl⟩ : syracuseStep 933383 = 1400075) B1400075
theorem B1687049 : Blo 550806 1687049 := bstep (se 2 (by rfl) ⟨632643, by rfl⟩ : syracuseStep 1687049 = 1265287) B1265287
theorem B1064545 : Blo 550806 1064545 := bstep (se 2 (by rfl) ⟨399204, by rfl⟩ : syracuseStep 1064545 = 798409) B798409
theorem B5324525 : Blo 550806 5324525 := bstep (se 3 (by rfl) ⟨998348, by rfl⟩ : syracuseStep 5324525 = 1996697) B1996697
theorem B933727 : Blo 550806 933727 := bstep (se 1 (by rfl) ⟨700295, by rfl⟩ : syracuseStep 933727 = 1400591) B1400591
theorem B933815 : Blo 550806 933815 := bstep (se 1 (by rfl) ⟨700361, by rfl⟩ : syracuseStep 933815 = 1400723) B1400723
theorem B4210703 : Blo 550806 4210703 := bstep (se 1 (by rfl) ⟨3158027, by rfl⟩ : syracuseStep 4210703 = 6316055) B6316055
theorem B2244779 : Blo 550806 2244779 := bstep (se 1 (by rfl) ⟨1683584, by rfl⟩ : syracuseStep 2244779 = 3367169) B3367169
theorem B4473137 : Blo 550806 4473137 := bstep (se 2 (by rfl) ⟨1677426, by rfl⟩ : syracuseStep 4473137 = 3354853) B3354853
theorem B1065377 : Blo 550806 1065377 := bstep (se 2 (by rfl) ⟨399516, by rfl⟩ : syracuseStep 1065377 = 799033) B799033
theorem B934409 : Blo 550806 934409 := bstep (se 2 (by rfl) ⟨350403, by rfl⟩ : syracuseStep 934409 = 700807) B700807
theorem B9585211 : Blo 550806 9585211 := bstep (se 1 (by rfl) ⟨7188908, by rfl⟩ : syracuseStep 9585211 = 14377817) B14377817
theorem B2277985 : Blo 550806 2277985 := bstep (se 2 (by rfl) ⟨854244, by rfl⟩ : syracuseStep 2277985 = 1708489) B1708489
theorem B934571 : Blo 550806 934571 := bstep (se 1 (by rfl) ⟨700928, by rfl⟩ : syracuseStep 934571 = 1401857) B1401857
theorem B934969 : Blo 550806 934969 := bstep (se 2 (by rfl) ⟨350613, by rfl⟩ : syracuseStep 934969 = 701227) B701227
theorem B935111 : Blo 550806 935111 := bstep (se 1 (by rfl) ⟨701333, by rfl⟩ : syracuseStep 935111 = 1402667) B1402667
theorem B935273 : Blo 550806 935273 := bstep (se 2 (by rfl) ⟨350727, by rfl⟩ : syracuseStep 935273 = 701455) B701455
theorem B1394273 : Blo 550806 1394273 := bstep (se 2 (by rfl) ⟨522852, by rfl⟩ : syracuseStep 1394273 = 1045705) B1045705
theorem B1492679 : Blo 550806 1492679 := bstep (se 1 (by rfl) ⟨1119509, by rfl⟩ : syracuseStep 1492679 = 2239019) B2239019
theorem B935671 : Blo 550806 935671 := bstep (se 1 (by rfl) ⟨701753, by rfl⟩ : syracuseStep 935671 = 1403507) B1403507
theorem B935867 : Blo 550806 935867 := bstep (se 1 (by rfl) ⟨701900, by rfl⟩ : syracuseStep 935867 = 1403801) B1403801
theorem B935975 : Blo 550806 935975 := bstep (se 1 (by rfl) ⟨701981, by rfl⟩ : syracuseStep 935975 = 1403963) B1403963
theorem B16107923 : Blo 550806 16107923 := bstep (se 1 (by rfl) ⟨12080942, by rfl⟩ : syracuseStep 16107923 = 24161885) B24161885
theorem B8604107 : Blo 550806 8604107 := bstep (se 1 (by rfl) ⟨6453080, by rfl⟩ : syracuseStep 8604107 = 12906161) B12906161
theorem B1330103 : Blo 550806 1330103 := bstep (se 1 (by rfl) ⟨997577, by rfl⟩ : syracuseStep 1330103 = 1995155) B1995155
theorem B1264567 : Blo 550806 1264567 := bstep (se 1 (by rfl) ⟨948425, by rfl⟩ : syracuseStep 1264567 = 1896851) B1896851
theorem B1395731 : Blo 550806 1395731 := bstep (se 1 (by rfl) ⟨1046798, by rfl⟩ : syracuseStep 1395731 = 2093597) B2093597
theorem B707783 : Blo 550806 707783 := bstep (se 1 (by rfl) ⟨530837, by rfl⟩ : syracuseStep 707783 = 1061675) B1061675
theorem B1396187 : Blo 550806 1396187 := bstep (se 1 (by rfl) ⟨1047140, by rfl⟩ : syracuseStep 1396187 = 2094281) B2094281
theorem B1560253 : Blo 550806 1560253 := bstep (se 3 (by rfl) ⟨292547, by rfl⟩ : syracuseStep 1560253 = 585095) B585095
theorem B7065377 : Blo 550806 7065377 := bstep (se 2 (by rfl) ⟨2649516, by rfl⟩ : syracuseStep 7065377 = 5299033) B5299033
theorem B1888637 : Blo 550806 1888637 := bstep (se 3 (by rfl) ⟨354119, by rfl⟩ : syracuseStep 1888637 = 708239) B708239
theorem B1397371 : Blo 550806 1397371 := bstep (se 1 (by rfl) ⟨1048028, by rfl⟩ : syracuseStep 1397371 = 2096057) B2096057
theorem B5690387 : Blo 550806 5690387 := bstep (se 1 (by rfl) ⟨4267790, by rfl⟩ : syracuseStep 5690387 = 8535581) B8535581
theorem B842363 : Blo 550806 842363 := bstep (se 1 (by rfl) ⟨631772, by rfl⟩ : syracuseStep 842363 = 1263545) B1263545
theorem B4315907 : Blo 550806 4315907 := bstep (se 1 (by rfl) ⟨3236930, by rfl⟩ : syracuseStep 4315907 = 6473861) B6473861
theorem B15129461 : Blo 550806 15129461 := bstep (se 5 (by rfl) ⟨709193, by rfl⟩ : syracuseStep 15129461 = 1418387) B1418387
theorem B711607 : Blo 550806 711607 := bstep (se 1 (by rfl) ⟨533705, by rfl⟩ : syracuseStep 711607 = 1067411) B1067411
theorem B744799 : Blo 550806 744799 := bstep (se 1 (by rfl) ⟨558599, by rfl⟩ : syracuseStep 744799 = 1117199) B1117199
theorem B1859111 : Blo 550806 1859111 := bstep (se 1 (by rfl) ⟨1394333, by rfl⟩ : syracuseStep 1859111 = 2788667) B2788667
theorem B1859219 : Blo 550806 1859219 := bstep (se 1 (by rfl) ⟨1394414, by rfl⟩ : syracuseStep 1859219 = 2788829) B2788829
theorem B11951887 : Blo 550806 11951887 := bstep (se 1 (by rfl) ⟨8963915, by rfl⟩ : syracuseStep 11951887 = 17927831) B17927831
theorem B1859435 : Blo 550806 1859435 := bstep (se 1 (by rfl) ⟨1394576, by rfl⟩ : syracuseStep 1859435 = 2789153) B2789153
theorem B1859489 : Blo 550806 1859489 := bstep (se 2 (by rfl) ⟨697308, by rfl⟩ : syracuseStep 1859489 = 1394617) B1394617
theorem B1892279 : Blo 550806 1892279 := bstep (se 1 (by rfl) ⟨1419209, by rfl⟩ : syracuseStep 1892279 = 2838419) B2838419
theorem B1860083 : Blo 550806 1860083 := bstep (se 1 (by rfl) ⟨1395062, by rfl⟩ : syracuseStep 1860083 = 2790125) B2790125
theorem B3531437 : Blo 550806 3531437 := bstep (se 3 (by rfl) ⟨662144, by rfl⟩ : syracuseStep 3531437 = 1324289) B1324289
theorem B746183 : Blo 550806 746183 := bstep (se 1 (by rfl) ⟨559637, by rfl⟩ : syracuseStep 746183 = 1119275) B1119275
theorem B1401695 : Blo 550806 1401695 := bstep (se 1 (by rfl) ⟨1051271, by rfl⟩ : syracuseStep 1401695 = 2102543) B2102543
theorem B1860623 : Blo 550806 1860623 := bstep (se 1 (by rfl) ⟨1395467, by rfl⟩ : syracuseStep 1860623 = 2790935) B2790935
theorem B6317513 : Blo 550806 6317513 := bstep (se 2 (by rfl) ⟨2369067, by rfl⟩ : syracuseStep 6317513 = 4738135) B4738135
theorem B2123227 : Blo 550806 2123227 := bstep (se 1 (by rfl) ⟨1592420, by rfl⟩ : syracuseStep 2123227 = 3184841) B3184841
theorem B1402393 : Blo 550806 1402393 := bstep (se 2 (by rfl) ⟨525897, by rfl⟩ : syracuseStep 1402393 = 1051795) B1051795
theorem B1861217 : Blo 550806 1861217 := bstep (se 2 (by rfl) ⟨697956, by rfl⟩ : syracuseStep 1861217 = 1395913) B1395913
theorem B1402697 : Blo 550806 1402697 := bstep (se 2 (by rfl) ⟨526011, by rfl⟩ : syracuseStep 1402697 = 1052023) B1052023
theorem B2647903 : Blo 550806 2647903 := bstep (se 1 (by rfl) ⟨1985927, by rfl⟩ : syracuseStep 2647903 = 3971855) B3971855
theorem B550831 : Blo 550806 550831 := bstep (se 1 (by rfl) ⟨413123, by rfl⟩ : syracuseStep 550831 = 826247) B826247
theorem B550855 : Blo 550806 550855 := bstep (se 1 (by rfl) ⟨413141, by rfl⟩ : syracuseStep 550855 = 826283) B826283
theorem B550875 : Blo 550806 550875 := bstep (se 1 (by rfl) ⟨413156, by rfl⟩ : syracuseStep 550875 = 826313) B826313
theorem B550951 : Blo 550806 550951 := bstep (se 1 (by rfl) ⟨413213, by rfl⟩ : syracuseStep 550951 = 826427) B826427
theorem B550991 : Blo 550806 550991 := bstep (se 1 (by rfl) ⟨413243, by rfl⟩ : syracuseStep 550991 = 826487) B826487
theorem B551007 : Blo 550806 551007 := bstep (se 1 (by rfl) ⟨413255, by rfl⟩ : syracuseStep 551007 = 826511) B826511
theorem B17885285 : Blo 550806 17885285 := bstep (se 4 (by rfl) ⟨1676745, by rfl⟩ : syracuseStep 17885285 = 3353491) B3353491
theorem B551035 : Blo 550806 551035 := bstep (se 1 (by rfl) ⟨413276, by rfl⟩ : syracuseStep 551035 = 826553) B826553
theorem B747643 : Blo 550806 747643 := bstep (se 1 (by rfl) ⟨560732, by rfl⟩ : syracuseStep 747643 = 1121465) B1121465
theorem B551087 : Blo 550806 551087 := bstep (se 1 (by rfl) ⟨413315, by rfl⟩ : syracuseStep 551087 = 826631) B826631
theorem B551111 : Blo 550806 551111 := bstep (se 1 (by rfl) ⟨413333, by rfl⟩ : syracuseStep 551111 = 826667) B826667
theorem B551131 : Blo 550806 551131 := bstep (se 1 (by rfl) ⟨413348, by rfl⟩ : syracuseStep 551131 = 826697) B826697
theorem B10741997 : Blo 550806 10741997 := bstep (se 3 (by rfl) ⟨2014124, by rfl⟩ : syracuseStep 10741997 = 4028249) B4028249
theorem B551207 : Blo 550806 551207 := bstep (se 1 (by rfl) ⟨413405, by rfl⟩ : syracuseStep 551207 = 826811) B826811
theorem B551247 : Blo 550806 551247 := bstep (se 1 (by rfl) ⟨413435, by rfl⟩ : syracuseStep 551247 = 826871) B826871
theorem B551263 : Blo 550806 551263 := bstep (se 1 (by rfl) ⟨413447, by rfl⟩ : syracuseStep 551263 = 826895) B826895
theorem B551291 : Blo 550806 551291 := bstep (se 1 (by rfl) ⟨413468, by rfl⟩ : syracuseStep 551291 = 826937) B826937
theorem B551343 : Blo 550806 551343 := bstep (se 1 (by rfl) ⟨413507, by rfl⟩ : syracuseStep 551343 = 827015) B827015
theorem B551367 : Blo 550806 551367 := bstep (se 1 (by rfl) ⟨413525, by rfl⟩ : syracuseStep 551367 = 827051) B827051
theorem B1239515 : Blo 550806 1239515 := bstep (se 1 (by rfl) ⟨929636, by rfl⟩ : syracuseStep 1239515 = 1859273) B1859273
theorem B551387 : Blo 550806 551387 := bstep (se 1 (by rfl) ⟨413540, by rfl⟩ : syracuseStep 551387 = 827081) B827081
theorem B1796633 : Blo 550806 1796633 := bstep (se 2 (by rfl) ⟨673737, by rfl⟩ : syracuseStep 1796633 = 1347475) B1347475
theorem B551463 : Blo 550806 551463 := bstep (se 1 (by rfl) ⟨413597, by rfl⟩ : syracuseStep 551463 = 827195) B827195
theorem B551503 : Blo 550806 551503 := bstep (se 1 (by rfl) ⟨413627, by rfl⟩ : syracuseStep 551503 = 827255) B827255
theorem B551519 : Blo 550806 551519 := bstep (se 1 (by rfl) ⟨413639, by rfl⟩ : syracuseStep 551519 = 827279) B827279
theorem B551547 : Blo 550806 551547 := bstep (se 1 (by rfl) ⟨413660, by rfl⟩ : syracuseStep 551547 = 827321) B827321
theorem B551599 : Blo 550806 551599 := bstep (se 1 (by rfl) ⟨413699, by rfl⟩ : syracuseStep 551599 = 827399) B827399
theorem B551623 : Blo 550806 551623 := bstep (se 1 (by rfl) ⟨413717, by rfl⟩ : syracuseStep 551623 = 827435) B827435
theorem B3795665 : Blo 550806 3795665 := bstep (se 2 (by rfl) ⟨1423374, by rfl⟩ : syracuseStep 3795665 = 2846749) B2846749
theorem B551643 : Blo 550806 551643 := bstep (se 1 (by rfl) ⟨413732, by rfl⟩ : syracuseStep 551643 = 827465) B827465
theorem B551719 : Blo 550806 551719 := bstep (se 1 (by rfl) ⟨413789, by rfl⟩ : syracuseStep 551719 = 827579) B827579
theorem B551759 : Blo 550806 551759 := bstep (se 1 (by rfl) ⟨413819, by rfl⟩ : syracuseStep 551759 = 827639) B827639
theorem B551775 : Blo 550806 551775 := bstep (se 1 (by rfl) ⟨413831, by rfl⟩ : syracuseStep 551775 = 827663) B827663
theorem B551803 : Blo 550806 551803 := bstep (se 1 (by rfl) ⟨413852, by rfl⟩ : syracuseStep 551803 = 827705) B827705
theorem B1239983 : Blo 550806 1239983 := bstep (se 1 (by rfl) ⟨929987, by rfl⟩ : syracuseStep 1239983 = 1859975) B1859975
theorem B551855 : Blo 550806 551855 := bstep (se 1 (by rfl) ⟨413891, by rfl⟩ : syracuseStep 551855 = 827783) B827783
theorem B1403831 : Blo 550806 1403831 := bstep (se 1 (by rfl) ⟨1052873, by rfl⟩ : syracuseStep 1403831 = 2105747) B2105747
theorem B551879 : Blo 550806 551879 := bstep (se 1 (by rfl) ⟨413909, by rfl⟩ : syracuseStep 551879 = 827819) B827819
theorem B551899 : Blo 550806 551899 := bstep (se 1 (by rfl) ⟨413924, by rfl⟩ : syracuseStep 551899 = 827849) B827849
theorem B1862675 : Blo 550806 1862675 := bstep (se 1 (by rfl) ⟨1397006, by rfl⟩ : syracuseStep 1862675 = 2794013) B2794013
theorem B551975 : Blo 550806 551975 := bstep (se 1 (by rfl) ⟨413981, by rfl⟩ : syracuseStep 551975 = 827963) B827963
theorem B5303339 : Blo 550806 5303339 := bstep (se 1 (by rfl) ⟨3977504, by rfl⟩ : syracuseStep 5303339 = 7955009) B7955009
theorem B552015 : Blo 550806 552015 := bstep (se 1 (by rfl) ⟨414011, by rfl⟩ : syracuseStep 552015 = 828023) B828023
theorem B552031 : Blo 550806 552031 := bstep (se 1 (by rfl) ⟨414023, by rfl⟩ : syracuseStep 552031 = 828047) B828047
theorem B552059 : Blo 550806 552059 := bstep (se 1 (by rfl) ⟨414044, by rfl⟩ : syracuseStep 552059 = 828089) B828089
theorem B1240235 : Blo 550806 1240235 := bstep (se 1 (by rfl) ⟨930176, by rfl⟩ : syracuseStep 1240235 = 1860353) B1860353
theorem B4484267 : Blo 550806 4484267 := bstep (se 1 (by rfl) ⟨3363200, by rfl⟩ : syracuseStep 4484267 = 6726401) B6726401
theorem B552111 : Blo 550806 552111 := bstep (se 1 (by rfl) ⟨414083, by rfl⟩ : syracuseStep 552111 = 828167) B828167
theorem B552135 : Blo 550806 552135 := bstep (se 1 (by rfl) ⟨414101, by rfl⟩ : syracuseStep 552135 = 828203) B828203
theorem B552155 : Blo 550806 552155 := bstep (se 1 (by rfl) ⟨414116, by rfl⟩ : syracuseStep 552155 = 828233) B828233
theorem B14511395 : Blo 550806 14511395 := bstep (se 1 (by rfl) ⟨10883546, by rfl⟩ : syracuseStep 14511395 = 21767093) B21767093
theorem B552231 : Blo 550806 552231 := bstep (se 1 (by rfl) ⟨414173, by rfl⟩ : syracuseStep 552231 = 828347) B828347
theorem B552271 : Blo 550806 552271 := bstep (se 1 (by rfl) ⟨414203, by rfl⟩ : syracuseStep 552271 = 828407) B828407
theorem B1862999 : Blo 550806 1862999 := bstep (se 1 (by rfl) ⟨1397249, by rfl⟩ : syracuseStep 1862999 = 2794499) B2794499
theorem B552287 : Blo 550806 552287 := bstep (se 1 (by rfl) ⟨414215, by rfl⟩ : syracuseStep 552287 = 828431) B828431
theorem B552315 : Blo 550806 552315 := bstep (se 1 (by rfl) ⟨414236, by rfl⟩ : syracuseStep 552315 = 828473) B828473
theorem B552367 : Blo 550806 552367 := bstep (se 1 (by rfl) ⟨414275, by rfl⟩ : syracuseStep 552367 = 828551) B828551
theorem B552391 : Blo 550806 552391 := bstep (se 1 (by rfl) ⟨414293, by rfl⟩ : syracuseStep 552391 = 828587) B828587
theorem B552411 : Blo 550806 552411 := bstep (se 1 (by rfl) ⟨414308, by rfl⟩ : syracuseStep 552411 = 828617) B828617
theorem B552487 : Blo 550806 552487 := bstep (se 1 (by rfl) ⟨414365, by rfl⟩ : syracuseStep 552487 = 828731) B828731
theorem B945703 : Blo 550806 945703 := bstep (se 1 (by rfl) ⟨709277, by rfl⟩ : syracuseStep 945703 = 1418555) B1418555
theorem B552527 : Blo 550806 552527 := bstep (se 1 (by rfl) ⟨414395, by rfl⟩ : syracuseStep 552527 = 828791) B828791
theorem B749135 : Blo 550806 749135 := bstep (se 1 (by rfl) ⟨561851, by rfl⟩ : syracuseStep 749135 = 1123703) B1123703
theorem B552543 : Blo 550806 552543 := bstep (se 1 (by rfl) ⟨414407, by rfl⟩ : syracuseStep 552543 = 828815) B828815
theorem B552571 : Blo 550806 552571 := bstep (se 1 (by rfl) ⟨414428, by rfl⟩ : syracuseStep 552571 = 828857) B828857
theorem B552623 : Blo 550806 552623 := bstep (se 1 (by rfl) ⟨414467, by rfl⟩ : syracuseStep 552623 = 828935) B828935
theorem B1240775 : Blo 550806 1240775 := bstep (se 1 (by rfl) ⟨930581, by rfl⟩ : syracuseStep 1240775 = 1861163) B1861163
theorem B552647 : Blo 550806 552647 := bstep (se 1 (by rfl) ⟨414485, by rfl⟩ : syracuseStep 552647 = 828971) B828971
theorem B552667 : Blo 550806 552667 := bstep (se 1 (by rfl) ⟨414500, by rfl⟩ : syracuseStep 552667 = 829001) B829001
theorem B552743 : Blo 550806 552743 := bstep (se 1 (by rfl) ⟨414557, by rfl⟩ : syracuseStep 552743 = 829115) B829115
theorem B3141443 : Blo 550806 3141443 := bstep (se 1 (by rfl) ⟨2356082, by rfl⟩ : syracuseStep 3141443 = 4712165) B4712165
theorem B552783 : Blo 550806 552783 := bstep (se 1 (by rfl) ⟨414587, by rfl⟩ : syracuseStep 552783 = 829175) B829175
theorem B552799 : Blo 550806 552799 := bstep (se 1 (by rfl) ⟨414599, by rfl⟩ : syracuseStep 552799 = 829199) B829199
theorem B552827 : Blo 550806 552827 := bstep (se 1 (by rfl) ⟨414620, by rfl⟩ : syracuseStep 552827 = 829241) B829241
theorem B552879 : Blo 550806 552879 := bstep (se 1 (by rfl) ⟨414659, by rfl⟩ : syracuseStep 552879 = 829319) B829319
theorem B552903 : Blo 550806 552903 := bstep (se 1 (by rfl) ⟨414677, by rfl⟩ : syracuseStep 552903 = 829355) B829355
theorem B552923 : Blo 550806 552923 := bstep (se 1 (by rfl) ⟨414692, by rfl⟩ : syracuseStep 552923 = 829385) B829385
theorem B552999 : Blo 550806 552999 := bstep (se 1 (by rfl) ⟨414749, by rfl⟩ : syracuseStep 552999 = 829499) B829499
theorem B553039 : Blo 550806 553039 := bstep (se 1 (by rfl) ⟨414779, by rfl⟩ : syracuseStep 553039 = 829559) B829559
theorem B553055 : Blo 550806 553055 := bstep (se 1 (by rfl) ⟨414791, by rfl⟩ : syracuseStep 553055 = 829583) B829583
theorem B1994867 : Blo 550806 1994867 := bstep (se 1 (by rfl) ⟨1496150, by rfl⟩ : syracuseStep 1994867 = 2992301) B2992301
theorem B553083 : Blo 550806 553083 := bstep (se 1 (by rfl) ⟨414812, by rfl⟩ : syracuseStep 553083 = 829625) B829625
theorem B553135 : Blo 550806 553135 := bstep (se 1 (by rfl) ⟨414851, by rfl⟩ : syracuseStep 553135 = 829703) B829703
theorem B553159 : Blo 550806 553159 := bstep (se 1 (by rfl) ⟨414869, by rfl⟩ : syracuseStep 553159 = 829739) B829739
theorem B553179 : Blo 550806 553179 := bstep (se 1 (by rfl) ⟨414884, by rfl⟩ : syracuseStep 553179 = 829769) B829769
theorem B3993857 : Blo 550806 3993857 := bstep (se 2 (by rfl) ⟨1497696, by rfl⟩ : syracuseStep 3993857 = 2995393) B2995393
theorem B2093323 : Blo 550806 2093323 := bstep (se 1 (by rfl) ⟨1569992, by rfl⟩ : syracuseStep 2093323 = 3139985) B3139985
theorem B3141899 : Blo 550806 3141899 := bstep (se 1 (by rfl) ⟨2356424, by rfl⟩ : syracuseStep 3141899 = 4712849) B4712849
theorem B553255 : Blo 550806 553255 := bstep (se 1 (by rfl) ⟨414941, by rfl⟩ : syracuseStep 553255 = 829883) B829883
theorem B553295 : Blo 550806 553295 := bstep (se 1 (by rfl) ⟨414971, by rfl⟩ : syracuseStep 553295 = 829943) B829943
theorem B553311 : Blo 550806 553311 := bstep (se 1 (by rfl) ⟨414983, by rfl⟩ : syracuseStep 553311 = 829967) B829967
theorem B553339 : Blo 550806 553339 := bstep (se 1 (by rfl) ⟨415004, by rfl⟩ : syracuseStep 553339 = 830009) B830009
theorem B1864079 : Blo 550806 1864079 := bstep (se 1 (by rfl) ⟨1398059, by rfl⟩ : syracuseStep 1864079 = 2796119) B2796119
theorem B553391 : Blo 550806 553391 := bstep (se 1 (by rfl) ⟨415043, by rfl⟩ : syracuseStep 553391 = 830087) B830087
theorem B553415 : Blo 550806 553415 := bstep (se 1 (by rfl) ⟨415061, by rfl⟩ : syracuseStep 553415 = 830123) B830123
theorem B553435 : Blo 550806 553435 := bstep (se 1 (by rfl) ⟨415076, by rfl⟩ : syracuseStep 553435 = 830153) B830153
theorem B1241639 : Blo 550806 1241639 := bstep (se 1 (by rfl) ⟨931229, by rfl⟩ : syracuseStep 1241639 = 1862459) B1862459
theorem B553511 : Blo 550806 553511 := bstep (se 1 (by rfl) ⟨415133, by rfl⟩ : syracuseStep 553511 = 830267) B830267
theorem B2093627 : Blo 550806 2093627 := bstep (se 1 (by rfl) ⟨1570220, by rfl⟩ : syracuseStep 2093627 = 3140441) B3140441
theorem B553551 : Blo 550806 553551 := bstep (se 1 (by rfl) ⟨415163, by rfl⟩ : syracuseStep 553551 = 830327) B830327
theorem B553567 : Blo 550806 553567 := bstep (se 1 (by rfl) ⟨415175, by rfl⟩ : syracuseStep 553567 = 830351) B830351
theorem B553595 : Blo 550806 553595 := bstep (se 1 (by rfl) ⟨415196, by rfl⟩ : syracuseStep 553595 = 830393) B830393
theorem B553647 : Blo 550806 553647 := bstep (se 1 (by rfl) ⟨415235, by rfl⟩ : syracuseStep 553647 = 830471) B830471
theorem B1569469 : Blo 550806 1569469 := bstep (se 3 (by rfl) ⟨294275, by rfl⟩ : syracuseStep 1569469 = 588551) B588551
theorem B553671 : Blo 550806 553671 := bstep (se 1 (by rfl) ⟨415253, by rfl⟩ : syracuseStep 553671 = 830507) B830507
theorem B1864403 : Blo 550806 1864403 := bstep (se 1 (by rfl) ⟨1398302, by rfl⟩ : syracuseStep 1864403 = 2796605) B2796605
theorem B553691 : Blo 550806 553691 := bstep (se 1 (by rfl) ⟨415268, by rfl⟩ : syracuseStep 553691 = 830537) B830537
theorem B5960465 : Blo 550806 5960465 := bstep (se 2 (by rfl) ⟨2235174, by rfl⟩ : syracuseStep 5960465 = 4470349) B4470349
theorem B553767 : Blo 550806 553767 := bstep (se 1 (by rfl) ⟨415325, by rfl⟩ : syracuseStep 553767 = 830651) B830651
theorem B1995587 : Blo 550806 1995587 := bstep (se 1 (by rfl) ⟨1496690, by rfl⟩ : syracuseStep 1995587 = 2993381) B2993381
theorem B2978633 : Blo 550806 2978633 := bstep (se 2 (by rfl) ⟨1116987, by rfl⟩ : syracuseStep 2978633 = 2233975) B2233975
theorem B553807 : Blo 550806 553807 := bstep (se 1 (by rfl) ⟨415355, by rfl⟩ : syracuseStep 553807 = 830711) B830711
theorem B553823 : Blo 550806 553823 := bstep (se 1 (by rfl) ⟨415367, by rfl⟩ : syracuseStep 553823 = 830735) B830735
theorem B1241963 : Blo 550806 1241963 := bstep (se 1 (by rfl) ⟨931472, by rfl⟩ : syracuseStep 1241963 = 1862945) B1862945
theorem B553851 : Blo 550806 553851 := bstep (se 1 (by rfl) ⟨415388, by rfl⟩ : syracuseStep 553851 = 830777) B830777
theorem B1242017 : Blo 550806 1242017 := bstep (se 2 (by rfl) ⟨465756, by rfl⟩ : syracuseStep 1242017 = 931513) B931513
theorem B553903 : Blo 550806 553903 := bstep (se 1 (by rfl) ⟨415427, by rfl⟩ : syracuseStep 553903 = 830855) B830855
theorem B1569719 : Blo 550806 1569719 := bstep (se 1 (by rfl) ⟨1177289, by rfl⟩ : syracuseStep 1569719 = 2354579) B2354579
theorem B3142583 : Blo 550806 3142583 := bstep (se 1 (by rfl) ⟨2356937, by rfl⟩ : syracuseStep 3142583 = 4713875) B4713875
theorem B553927 : Blo 550806 553927 := bstep (se 1 (by rfl) ⟨415445, by rfl⟩ : syracuseStep 553927 = 830891) B830891
theorem B553947 : Blo 550806 553947 := bstep (se 1 (by rfl) ⟨415460, by rfl⟩ : syracuseStep 553947 = 830921) B830921
theorem B554023 : Blo 550806 554023 := bstep (se 1 (by rfl) ⟨415517, by rfl⟩ : syracuseStep 554023 = 831035) B831035
theorem B554063 : Blo 550806 554063 := bstep (se 1 (by rfl) ⟨415547, by rfl⟩ : syracuseStep 554063 = 831095) B831095
theorem B554079 : Blo 550806 554079 := bstep (se 1 (by rfl) ⟨415559, by rfl⟩ : syracuseStep 554079 = 831119) B831119
theorem B554107 : Blo 550806 554107 := bstep (se 1 (by rfl) ⟨415580, by rfl⟩ : syracuseStep 554107 = 831161) B831161
theorem B554159 : Blo 550806 554159 := bstep (se 1 (by rfl) ⟨415619, by rfl⟩ : syracuseStep 554159 = 831239) B831239
theorem B554183 : Blo 550806 554183 := bstep (se 1 (by rfl) ⟨415637, by rfl⟩ : syracuseStep 554183 = 831275) B831275
theorem B554203 : Blo 550806 554203 := bstep (se 1 (by rfl) ⟨415652, by rfl⟩ : syracuseStep 554203 = 831305) B831305
theorem B1242359 : Blo 550806 1242359 := bstep (se 1 (by rfl) ⟨931769, by rfl⟩ : syracuseStep 1242359 = 1863539) B1863539
theorem B554279 : Blo 550806 554279 := bstep (se 1 (by rfl) ⟨415709, by rfl⟩ : syracuseStep 554279 = 831419) B831419
theorem B1078601 : Blo 550806 1078601 := bstep (se 2 (by rfl) ⟨404475, by rfl⟩ : syracuseStep 1078601 = 808951) B808951
theorem B554319 : Blo 550806 554319 := bstep (se 1 (by rfl) ⟨415739, by rfl⟩ : syracuseStep 554319 = 831479) B831479
theorem B554335 : Blo 550806 554335 := bstep (se 1 (by rfl) ⟨415751, by rfl⟩ : syracuseStep 554335 = 831503) B831503
theorem B1045865 : Blo 550806 1045865 := bstep (se 2 (by rfl) ⟨392199, by rfl⟩ : syracuseStep 1045865 = 784399) B784399
theorem B554363 : Blo 550806 554363 := bstep (se 1 (by rfl) ⟨415772, by rfl⟩ : syracuseStep 554363 = 831545) B831545
theorem B4257197 : Blo 550806 4257197 := bstep (se 3 (by rfl) ⟨798224, by rfl⟩ : syracuseStep 4257197 = 1596449) B1596449
theorem B619951 : Blo 550806 619951 := bstep (se 1 (by rfl) ⟨464963, by rfl⟩ : syracuseStep 619951 = 929927) B929927
theorem B554415 : Blo 550806 554415 := bstep (se 1 (by rfl) ⟨415811, by rfl⟩ : syracuseStep 554415 = 831623) B831623
theorem B554439 : Blo 550806 554439 := bstep (se 1 (by rfl) ⟨415829, by rfl⟩ : syracuseStep 554439 = 831659) B831659
theorem B1177051 : Blo 550806 1177051 := bstep (se 1 (by rfl) ⟨882788, by rfl⟩ : syracuseStep 1177051 = 1765577) B1765577
theorem B554459 : Blo 550806 554459 := bstep (se 1 (by rfl) ⟨415844, by rfl⟩ : syracuseStep 554459 = 831689) B831689
theorem B554535 : Blo 550806 554535 := bstep (se 1 (by rfl) ⟨415901, by rfl⟩ : syracuseStep 554535 = 831803) B831803
theorem B554575 : Blo 550806 554575 := bstep (se 1 (by rfl) ⟨415931, by rfl⟩ : syracuseStep 554575 = 831863) B831863
theorem B554591 : Blo 550806 554591 := bstep (se 1 (by rfl) ⟨415943, by rfl⟩ : syracuseStep 554591 = 831887) B831887
theorem B554619 : Blo 550806 554619 := bstep (se 1 (by rfl) ⟨415964, by rfl⟩ : syracuseStep 554619 = 831929) B831929
theorem B554671 : Blo 550806 554671 := bstep (se 1 (by rfl) ⟨416003, by rfl⟩ : syracuseStep 554671 = 832007) B832007
theorem B11368117 : Blo 550806 11368117 := bstep (se 5 (by rfl) ⟨532880, by rfl⟩ : syracuseStep 11368117 = 1065761) B1065761
theorem B2094781 : Blo 550806 2094781 := bstep (se 3 (by rfl) ⟨392771, by rfl⟩ : syracuseStep 2094781 = 785543) B785543
theorem B3143357 : Blo 550806 3143357 := bstep (se 3 (by rfl) ⟨589379, by rfl⟩ : syracuseStep 3143357 = 1178759) B1178759
theorem B554695 : Blo 550806 554695 := bstep (se 1 (by rfl) ⟨416021, by rfl⟩ : syracuseStep 554695 = 832043) B832043
theorem B554715 : Blo 550806 554715 := bstep (se 1 (by rfl) ⟨416036, by rfl⟩ : syracuseStep 554715 = 832073) B832073
theorem B554791 : Blo 550806 554791 := bstep (se 1 (by rfl) ⟨416093, by rfl⟩ : syracuseStep 554791 = 832187) B832187
theorem B5994283 : Blo 550806 5994283 := bstep (se 1 (by rfl) ⟨4495712, by rfl⟩ : syracuseStep 5994283 = 8991425) B8991425
theorem B1242953 : Blo 550806 1242953 := bstep (se 2 (by rfl) ⟨466107, by rfl⟩ : syracuseStep 1242953 = 932215) B932215
theorem B620383 : Blo 550806 620383 := bstep (se 1 (by rfl) ⟨465287, by rfl⟩ : syracuseStep 620383 = 930575) B930575
theorem B1865591 : Blo 550806 1865591 := bstep (se 1 (by rfl) ⟨1399193, by rfl⟩ : syracuseStep 1865591 = 2798387) B2798387
theorem B9598925 : Blo 550806 9598925 := bstep (se 3 (by rfl) ⟨1799798, by rfl⟩ : syracuseStep 9598925 = 3599597) B3599597
theorem B1865807 : Blo 550806 1865807 := bstep (se 1 (by rfl) ⟨1399355, by rfl⟩ : syracuseStep 1865807 = 2798711) B2798711
theorem B784507 : Blo 550806 784507 := bstep (se 1 (by rfl) ⟨588380, by rfl⟩ : syracuseStep 784507 = 1176761) B1176761
theorem B620743 : Blo 550806 620743 := bstep (se 1 (by rfl) ⟨465557, by rfl⟩ : syracuseStep 620743 = 931115) B931115
theorem B16152817 : Blo 550806 16152817 := bstep (se 2 (by rfl) ⟨6057306, by rfl⟩ : syracuseStep 16152817 = 12114613) B12114613
theorem B1571177 : Blo 550806 1571177 := bstep (se 2 (by rfl) ⟨589191, by rfl⟩ : syracuseStep 1571177 = 1178383) B1178383
theorem B3144041 : Blo 550806 3144041 := bstep (se 2 (by rfl) ⟨1179015, by rfl⟩ : syracuseStep 3144041 = 2358031) B2358031
theorem B1571201 : Blo 550806 1571201 := bstep (se 2 (by rfl) ⟨589200, by rfl⟩ : syracuseStep 1571201 = 1178401) B1178401
theorem B1866185 : Blo 550806 1866185 := bstep (se 2 (by rfl) ⟨699819, by rfl⟩ : syracuseStep 1866185 = 1399639) B1399639
theorem B1243745 : Blo 550806 1243745 := bstep (se 2 (by rfl) ⟨466404, by rfl⟩ : syracuseStep 1243745 = 932809) B932809
theorem B1047163 : Blo 550806 1047163 := bstep (se 1 (by rfl) ⟨785372, by rfl⟩ : syracuseStep 1047163 = 1570745) B1570745
theorem B2095739 : Blo 550806 2095739 := bstep (se 1 (by rfl) ⟨1571804, by rfl⟩ : syracuseStep 2095739 = 3143609) B3143609
theorem B1047239 : Blo 550806 1047239 := bstep (se 1 (by rfl) ⟨785429, by rfl⟩ : syracuseStep 1047239 = 1570859) B1570859
theorem B1866455 : Blo 550806 1866455 := bstep (se 1 (by rfl) ⟨1399841, by rfl⟩ : syracuseStep 1866455 = 2799683) B2799683
theorem B1866671 : Blo 550806 1866671 := bstep (se 1 (by rfl) ⟨1400003, by rfl⟩ : syracuseStep 1866671 = 2800007) B2800007
theorem B1244087 : Blo 550806 1244087 := bstep (se 1 (by rfl) ⟨933065, by rfl⟩ : syracuseStep 1244087 = 1866131) B1866131
theorem B4193207 : Blo 550806 4193207 := bstep (se 1 (by rfl) ⟨3144905, by rfl⟩ : syracuseStep 4193207 = 6289811) B6289811
theorem B621607 : Blo 550806 621607 := bstep (se 1 (by rfl) ⟨466205, by rfl⟩ : syracuseStep 621607 = 932411) B932411
theorem B1047649 : Blo 550806 1047649 := bstep (se 2 (by rfl) ⟨392868, by rfl⟩ : syracuseStep 1047649 = 785737) B785737
theorem B785657 : Blo 550806 785657 := bstep (se 2 (by rfl) ⟨294621, by rfl⟩ : syracuseStep 785657 = 589243) B589243
theorem B2096513 : Blo 550806 2096513 := bstep (se 2 (by rfl) ⟨786192, by rfl⟩ : syracuseStep 2096513 = 1572385) B1572385
theorem B1047991 : Blo 550806 1047991 := bstep (se 1 (by rfl) ⟨785993, by rfl⟩ : syracuseStep 1047991 = 1571987) B1571987
theorem B1244681 : Blo 550806 1244681 := bstep (se 2 (by rfl) ⟨466755, by rfl⟩ : syracuseStep 1244681 = 933511) B933511
theorem B1768999 : Blo 550806 1768999 := bstep (se 1 (by rfl) ⟨1326749, by rfl⟩ : syracuseStep 1768999 = 2653499) B2653499
theorem B1080911 : Blo 550806 1080911 := bstep (se 1 (by rfl) ⟨810683, by rfl⟩ : syracuseStep 1080911 = 1621367) B1621367
theorem B1048393 : Blo 550806 1048393 := bstep (se 2 (by rfl) ⟨393147, by rfl⟩ : syracuseStep 1048393 = 786295) B786295
theorem B1245023 : Blo 550806 1245023 := bstep (se 1 (by rfl) ⟨933767, by rfl⟩ : syracuseStep 1245023 = 1867535) B1867535
theorem B2097211 : Blo 550806 2097211 := bstep (se 1 (by rfl) ⟨1572908, by rfl⟩ : syracuseStep 2097211 = 3145817) B3145817
theorem B2982091 : Blo 550806 2982091 := bstep (se 1 (by rfl) ⟨2236568, by rfl⟩ : syracuseStep 2982091 = 4473137) B4473137
theorem B622939 : Blo 550806 622939 := bstep (se 1 (by rfl) ⟨467204, by rfl⟩ : syracuseStep 622939 = 934409) B934409
theorem B2097515 : Blo 550806 2097515 := bstep (se 1 (by rfl) ⟨1573136, by rfl⟩ : syracuseStep 2097515 = 3146273) B3146273
theorem B623047 : Blo 550806 623047 := bstep (se 1 (by rfl) ⟨467285, by rfl⟩ : syracuseStep 623047 = 934571) B934571
theorem B2097683 : Blo 550806 2097683 := bstep (se 1 (by rfl) ⟨1573262, by rfl⟩ : syracuseStep 2097683 = 3146525) B3146525
theorem B2359979 : Blo 550806 2359979 := bstep (se 1 (by rfl) ⟨1769984, by rfl⟩ : syracuseStep 2359979 = 3539969) B3539969
theorem B12780281 : Blo 550806 12780281 := bstep (se 2 (by rfl) ⟨4792605, by rfl⟩ : syracuseStep 12780281 = 9585211) B9585211
theorem B623407 : Blo 550806 623407 := bstep (se 1 (by rfl) ⟨467555, by rfl⟩ : syracuseStep 623407 = 935111) B935111
theorem B4653883 : Blo 550806 4653883 := bstep (se 1 (by rfl) ⟨3490412, by rfl⟩ : syracuseStep 4653883 = 6980825) B6980825
theorem B1246031 : Blo 550806 1246031 := bstep (se 1 (by rfl) ⟨934523, by rfl⟩ : syracuseStep 1246031 = 1869047) B1869047
theorem B623515 : Blo 550806 623515 := bstep (se 1 (by rfl) ⟨467636, by rfl⟩ : syracuseStep 623515 = 935273) B935273
theorem B1246247 : Blo 550806 1246247 := bstep (se 1 (by rfl) ⟨934685, by rfl⟩ : syracuseStep 1246247 = 1869371) B1869371
theorem B591067 : Blo 550806 591067 := bstep (se 1 (by rfl) ⟨443300, by rfl⟩ : syracuseStep 591067 = 886601) B886601
theorem B1246427 : Blo 550806 1246427 := bstep (se 1 (by rfl) ⟨934820, by rfl⟩ : syracuseStep 1246427 = 1869641) B1869641
theorem B623911 : Blo 550806 623911 := bstep (se 1 (by rfl) ⟨467933, by rfl⟩ : syracuseStep 623911 = 935867) B935867
theorem B2360663 : Blo 550806 2360663 := bstep (se 1 (by rfl) ⟨1770497, by rfl⟩ : syracuseStep 2360663 = 3540995) B3540995
theorem B623983 : Blo 550806 623983 := bstep (se 1 (by rfl) ⟨467987, by rfl⟩ : syracuseStep 623983 = 935975) B935975
theorem B1246625 : Blo 550806 1246625 := bstep (se 2 (by rfl) ⟨467484, by rfl⟩ : syracuseStep 1246625 = 934969) B934969
theorem B2360765 : Blo 550806 2360765 := bstep (se 3 (by rfl) ⟨442643, by rfl⟩ : syracuseStep 2360765 = 885287) B885287
theorem B5736071 : Blo 550806 5736071 := bstep (se 1 (by rfl) ⟨4302053, by rfl⟩ : syracuseStep 5736071 = 8604107) B8604107
theorem B73664369 : Blo 550806 73664369 := bstep (se 2 (by rfl) ⟨27624138, by rfl⟩ : syracuseStep 73664369 = 55248277) B55248277
theorem B886735 : Blo 550806 886735 := bstep (se 1 (by rfl) ⟨665051, by rfl⟩ : syracuseStep 886735 = 1330103) B1330103
theorem B591823 : Blo 550806 591823 := bstep (se 1 (by rfl) ⟨443867, by rfl⟩ : syracuseStep 591823 = 887735) B887735
theorem B1247183 : Blo 550806 1247183 := bstep (se 1 (by rfl) ⟨935387, by rfl⟩ : syracuseStep 1247183 = 1870775) B1870775
theorem B1869857 : Blo 550806 1869857 := bstep (se 2 (by rfl) ⟨701196, by rfl⟩ : syracuseStep 1869857 = 1402393) B1402393
theorem B886889 : Blo 550806 886889 := bstep (se 2 (by rfl) ⟨332583, by rfl⟩ : syracuseStep 886889 = 665167) B665167
theorem B1247561 : Blo 550806 1247561 := bstep (se 2 (by rfl) ⟨467835, by rfl⟩ : syracuseStep 1247561 = 935671) B935671
theorem B1247579 : Blo 550806 1247579 := bstep (se 1 (by rfl) ⟨935684, by rfl⟩ : syracuseStep 1247579 = 1871369) B1871369
theorem B1182271 : Blo 550806 1182271 := bstep (se 1 (by rfl) ⟨886703, by rfl⟩ : syracuseStep 1182271 = 1773407) B1773407
theorem B14158637 : Blo 550806 14158637 := bstep (se 3 (by rfl) ⟨2654744, by rfl⟩ : syracuseStep 14158637 = 5309489) B5309489
theorem B1248155 : Blo 550806 1248155 := bstep (se 1 (by rfl) ⟨936116, by rfl⟩ : syracuseStep 1248155 = 1872233) B1872233
theorem B1510363 : Blo 550806 1510363 := bstep (se 1 (by rfl) ⟨1132772, by rfl⟩ : syracuseStep 1510363 = 2265545) B2265545
theorem B2362355 : Blo 550806 2362355 := bstep (se 1 (by rfl) ⟨1771766, by rfl⟩ : syracuseStep 2362355 = 3543533) B3543533
theorem B3148915 : Blo 550806 3148915 := bstep (se 1 (by rfl) ⟨2361686, by rfl⟩ : syracuseStep 3148915 = 4723373) B4723373
theorem B2100599 : Blo 550806 2100599 := bstep (se 1 (by rfl) ⟨1575449, by rfl⟩ : syracuseStep 2100599 = 3150899) B3150899
theorem B1183099 : Blo 550806 1183099 := bstep (se 1 (by rfl) ⟨887324, by rfl⟩ : syracuseStep 1183099 = 1774649) B1774649
theorem B11505077 : Blo 550806 11505077 := bstep (se 5 (by rfl) ⟨539300, by rfl⟩ : syracuseStep 11505077 = 1078601) B1078601
theorem B1576543 : Blo 550806 1576543 := bstep (se 1 (by rfl) ⟨1182407, by rfl⟩ : syracuseStep 1576543 = 2364815) B2364815
theorem B561575 : Blo 550806 561575 := bstep (se 1 (by rfl) ⟨421181, by rfl⟩ : syracuseStep 561575 = 842363) B842363
theorem B1184329 : Blo 550806 1184329 := bstep (se 2 (by rfl) ⟨444123, by rfl⟩ : syracuseStep 1184329 = 888247) B888247
theorem B2691731 : Blo 550806 2691731 := bstep (se 1 (by rfl) ⟨2018798, by rfl⟩ : syracuseStep 2691731 = 4037597) B4037597
theorem B1578217 : Blo 550806 1578217 := bstep (se 2 (by rfl) ⟨591831, by rfl⟩ : syracuseStep 1578217 = 1183663) B1183663
theorem B2791097 : Blo 550806 2791097 := bstep (se 2 (by rfl) ⟨1046661, by rfl⟩ : syracuseStep 2791097 = 2093323) B2093323
theorem B26941571 : Blo 550806 26941571 := bstep (se 1 (by rfl) ⟨20206178, by rfl⟩ : syracuseStep 26941571 = 40412357) B40412357
theorem B2103803 : Blo 550806 2103803 := bstep (se 1 (by rfl) ⟨1577852, by rfl⟩ : syracuseStep 2103803 = 3155705) B3155705
theorem B4725287 : Blo 550806 4725287 := bstep (se 1 (by rfl) ⟨3543965, by rfl⟩ : syracuseStep 4725287 = 7087931) B7087931
theorem B1678205 : Blo 550806 1678205 := bstep (se 3 (by rfl) ⟨314663, by rfl⟩ : syracuseStep 1678205 = 629327) B629327
theorem B2661245 : Blo 550806 2661245 := bstep (se 3 (by rfl) ⟨498983, by rfl⟩ : syracuseStep 2661245 = 997967) B997967
theorem B826343 : Blo 550806 826343 := bstep (se 1 (by rfl) ⟨619757, by rfl⟩ : syracuseStep 826343 = 1239515) B1239515
theorem B826601 : Blo 550806 826601 := bstep (se 2 (by rfl) ⟨309975, by rfl⟩ : syracuseStep 826601 = 619951) B619951
theorem B826655 : Blo 550806 826655 := bstep (se 1 (by rfl) ⟨619991, by rfl⟩ : syracuseStep 826655 = 1239983) B1239983
theorem B11509085 : Blo 550806 11509085 := bstep (se 3 (by rfl) ⟨2157953, by rfl⟩ : syracuseStep 11509085 = 4315907) B4315907
theorem B3153289 : Blo 550806 3153289 := bstep (se 2 (by rfl) ⟨1182483, by rfl⟩ : syracuseStep 3153289 = 2364967) B2364967
theorem B826823 : Blo 550806 826823 := bstep (se 1 (by rfl) ⟨620117, by rfl⟩ : syracuseStep 826823 = 1240235) B1240235
theorem B2989511 : Blo 550806 2989511 := bstep (se 1 (by rfl) ⟨2242133, by rfl⟩ : syracuseStep 2989511 = 4484267) B4484267
theorem B2104775 : Blo 550806 2104775 := bstep (se 1 (by rfl) ⟨1578581, by rfl⟩ : syracuseStep 2104775 = 3157163) B3157163
theorem B9674263 : Blo 550806 9674263 := bstep (se 1 (by rfl) ⟨7255697, by rfl⟩ : syracuseStep 9674263 = 14511395) B14511395
theorem B2793041 : Blo 550806 2793041 := bstep (se 2 (by rfl) ⟨1047390, by rfl⟩ : syracuseStep 2793041 = 2094781) B2094781
theorem B40345229 : Blo 550806 40345229 := bstep (se 3 (by rfl) ⟨7564730, by rfl⟩ : syracuseStep 40345229 = 15129461) B15129461
theorem B827177 : Blo 550806 827177 := bstep (se 2 (by rfl) ⟨310191, by rfl⟩ : syracuseStep 827177 = 620383) B620383
theorem B827183 : Blo 550806 827183 := bstep (se 1 (by rfl) ⟨620387, by rfl⟩ : syracuseStep 827183 = 1240775) B1240775
theorem B2662571 : Blo 550806 2662571 := bstep (se 1 (by rfl) ⟨1996928, by rfl⟩ : syracuseStep 2662571 = 3993857) B3993857
theorem B827657 : Blo 550806 827657 := bstep (se 2 (by rfl) ⟨310371, by rfl⟩ : syracuseStep 827657 = 620743) B620743
theorem B21537089 : Blo 550806 21537089 := bstep (se 2 (by rfl) ⟨8076408, by rfl⟩ : syracuseStep 21537089 = 16152817) B16152817
theorem B827759 : Blo 550806 827759 := bstep (se 1 (by rfl) ⟨620819, by rfl⟩ : syracuseStep 827759 = 1241639) B1241639
theorem B5677573 : Blo 550806 5677573 := bstep (se 4 (by rfl) ⟨532272, by rfl⟩ : syracuseStep 5677573 = 1064545) B1064545
theorem B3973643 : Blo 550806 3973643 := bstep (se 1 (by rfl) ⟨2980232, by rfl⟩ : syracuseStep 3973643 = 5960465) B5960465
theorem B827975 : Blo 550806 827975 := bstep (se 1 (by rfl) ⟨620981, by rfl⟩ : syracuseStep 827975 = 1241963) B1241963
theorem B828011 : Blo 550806 828011 := bstep (se 1 (by rfl) ⟨621008, by rfl⟩ : syracuseStep 828011 = 1242017) B1242017
theorem B828239 : Blo 550806 828239 := bstep (se 1 (by rfl) ⟨621179, by rfl⟩ : syracuseStep 828239 = 1242359) B1242359
theorem B697243 : Blo 550806 697243 := bstep (se 1 (by rfl) ⟨522932, by rfl⟩ : syracuseStep 697243 = 1045865) B1045865
theorem B4727747 : Blo 550806 4727747 := bstep (se 1 (by rfl) ⟨3545810, by rfl⟩ : syracuseStep 4727747 = 7091621) B7091621
theorem B2368727 : Blo 550806 2368727 := bstep (se 1 (by rfl) ⟨1776545, by rfl⟩ : syracuseStep 2368727 = 3553091) B3553091
theorem B828635 : Blo 550806 828635 := bstep (se 1 (by rfl) ⟨621476, by rfl⟩ : syracuseStep 828635 = 1242953) B1242953
theorem B6399283 : Blo 550806 6399283 := bstep (se 1 (by rfl) ⟨4799462, by rfl⟩ : syracuseStep 6399283 = 9598925) B9598925
theorem B4203899 : Blo 550806 4203899 := bstep (se 1 (by rfl) ⟨3152924, by rfl⟩ : syracuseStep 4203899 = 6305849) B6305849
theorem B828809 : Blo 550806 828809 := bstep (se 2 (by rfl) ⟨310803, by rfl⟩ : syracuseStep 828809 = 621607) B621607
theorem B665263 : Blo 550806 665263 := bstep (se 1 (by rfl) ⟨498947, by rfl⟩ : syracuseStep 665263 = 997895) B997895
theorem B829163 : Blo 550806 829163 := bstep (se 1 (by rfl) ⟨621872, by rfl⟩ : syracuseStep 829163 = 1243745) B1243745
theorem B993065 : Blo 550806 993065 := bstep (se 2 (by rfl) ⟨372399, by rfl⟩ : syracuseStep 993065 = 744799) B744799
theorem B698159 : Blo 550806 698159 := bstep (se 1 (by rfl) ⟨523619, by rfl⟩ : syracuseStep 698159 = 1047239) B1047239
theorem B2991953 : Blo 550806 2991953 := bstep (se 2 (by rfl) ⟨1121982, by rfl⟩ : syracuseStep 2991953 = 2243965) B2243965
theorem B1910735 : Blo 550806 1910735 := bstep (se 1 (by rfl) ⟨1433051, by rfl⟩ : syracuseStep 1910735 = 2866103) B2866103
theorem B2795471 : Blo 550806 2795471 := bstep (se 1 (by rfl) ⟨2096603, by rfl⟩ : syracuseStep 2795471 = 4193207) B4193207
theorem B829391 : Blo 550806 829391 := bstep (se 1 (by rfl) ⟨622043, by rfl⟩ : syracuseStep 829391 = 1244087) B1244087
theorem B1681661 : Blo 550806 1681661 := bstep (se 3 (by rfl) ⟨315311, by rfl⟩ : syracuseStep 1681661 = 630623) B630623
theorem B829787 : Blo 550806 829787 := bstep (se 1 (by rfl) ⟨622340, by rfl⟩ : syracuseStep 829787 = 1244681) B1244681
theorem B1124699 : Blo 550806 1124699 := bstep (se 1 (by rfl) ⟨843524, by rfl⟩ : syracuseStep 1124699 = 1687049) B1687049
theorem B15935849 : Blo 550806 15935849 := bstep (se 2 (by rfl) ⟨5975943, by rfl⟩ : syracuseStep 15935849 = 11951887) B11951887
theorem B3549683 : Blo 550806 3549683 := bstep (se 1 (by rfl) ⟨2662262, by rfl⟩ : syracuseStep 3549683 = 5324525) B5324525
theorem B830015 : Blo 550806 830015 := bstep (se 1 (by rfl) ⟨622511, by rfl⟩ : syracuseStep 830015 = 1245023) B1245023
theorem B830135 : Blo 550806 830135 := bstep (se 1 (by rfl) ⟨622601, by rfl⟩ : syracuseStep 830135 = 1245203) B1245203
theorem B1420051 : Blo 550806 1420051 := bstep (se 1 (by rfl) ⟨1065038, by rfl⟩ : syracuseStep 1420051 = 2130077) B2130077
theorem B2796443 : Blo 550806 2796443 := bstep (se 1 (by rfl) ⟨2097332, by rfl⟩ : syracuseStep 2796443 = 4194665) B4194665
theorem B830363 : Blo 550806 830363 := bstep (se 1 (by rfl) ⟨622772, by rfl⟩ : syracuseStep 830363 = 1245545) B1245545
theorem B621849635 : Blo 550806 621849635 := bstep (se 1 (by rfl) ⟨466387226, by rfl⟩ : syracuseStep 621849635 = 932774453) B932774453
theorem B3976411 : Blo 550806 3976411 := bstep (se 1 (by rfl) ⟨2982308, by rfl⟩ : syracuseStep 3976411 = 5964617) B5964617
theorem B830759 : Blo 550806 830759 := bstep (se 1 (by rfl) ⟨623069, by rfl⟩ : syracuseStep 830759 = 1246139) B1246139
theorem B830843 : Blo 550806 830843 := bstep (se 1 (by rfl) ⟨623132, by rfl⟩ : syracuseStep 830843 = 1246265) B1246265
theorem B2796929 : Blo 550806 2796929 := bstep (se 2 (by rfl) ⟨1048848, by rfl⟩ : syracuseStep 2796929 = 2097697) B2097697
theorem B830969 : Blo 550806 830969 := bstep (se 2 (by rfl) ⟨311613, by rfl⟩ : syracuseStep 830969 = 623227) B623227
theorem B831071 : Blo 550806 831071 := bstep (se 1 (by rfl) ⟨623303, by rfl⟩ : syracuseStep 831071 = 1246607) B1246607
theorem B929515 : Blo 550806 929515 := bstep (se 1 (by rfl) ⟨697136, by rfl⟩ : syracuseStep 929515 = 1394273) B1394273
theorem B831287 : Blo 550806 831287 := bstep (se 1 (by rfl) ⟨623465, by rfl⟩ : syracuseStep 831287 = 1246931) B1246931
theorem B2797577 : Blo 550806 2797577 := bstep (se 2 (by rfl) ⟨1049091, by rfl⟩ : syracuseStep 2797577 = 2098183) B2098183
theorem B831593 : Blo 550806 831593 := bstep (se 2 (by rfl) ⟨311847, by rfl⟩ : syracuseStep 831593 = 623695) B623695
theorem B2797739 : Blo 550806 2797739 := bstep (se 1 (by rfl) ⟨2098304, by rfl⟩ : syracuseStep 2797739 = 4196609) B4196609
theorem B831911 : Blo 550806 831911 := bstep (se 1 (by rfl) ⟨623933, by rfl⟩ : syracuseStep 831911 = 1247867) B1247867
theorem B1061345 : Blo 550806 1061345 := bstep (se 2 (by rfl) ⟨398004, by rfl⟩ : syracuseStep 1061345 = 796009) B796009
theorem B831995 : Blo 550806 831995 := bstep (se 1 (by rfl) ⟨623996, by rfl⟩ : syracuseStep 831995 = 1247993) B1247993
theorem B2830969 : Blo 550806 2830969 := bstep (se 2 (by rfl) ⟨1061613, by rfl⟩ : syracuseStep 2830969 = 2123227) B2123227
theorem B11940473 : Blo 550806 11940473 := bstep (se 2 (by rfl) ⟨4477677, by rfl⟩ : syracuseStep 11940473 = 8955355) B8955355
theorem B832121 : Blo 550806 832121 := bstep (se 2 (by rfl) ⟨312045, by rfl⟩ : syracuseStep 832121 = 624091) B624091
theorem B2798225 : Blo 550806 2798225 := bstep (se 2 (by rfl) ⟨1049334, by rfl⟩ : syracuseStep 2798225 = 2098669) B2098669
theorem B832175 : Blo 550806 832175 := bstep (se 1 (by rfl) ⟨624131, by rfl⟩ : syracuseStep 832175 = 1248263) B1248263
theorem B930487 : Blo 550806 930487 := bstep (se 1 (by rfl) ⟨697865, by rfl⟩ : syracuseStep 930487 = 1395731) B1395731
theorem B7549685 : Blo 550806 7549685 := bstep (se 5 (by rfl) ⟨353891, by rfl⟩ : syracuseStep 7549685 = 707783) B707783
theorem B930791 : Blo 550806 930791 := bstep (se 1 (by rfl) ⟨698093, by rfl⟩ : syracuseStep 930791 = 1396187) B1396187
theorem B11973689 : Blo 550806 11973689 := bstep (se 2 (by rfl) ⟨4490133, by rfl⟩ : syracuseStep 11973689 = 8980267) B8980267
theorem B3781847 : Blo 550806 3781847 := bstep (se 1 (by rfl) ⟨2836385, by rfl⟩ : syracuseStep 3781847 = 5672771) B5672771
theorem B996857 : Blo 550806 996857 := bstep (se 2 (by rfl) ⟨373821, by rfl⟩ : syracuseStep 996857 = 747643) B747643
theorem B702047 : Blo 550806 702047 := bstep (se 1 (by rfl) ⟨526535, by rfl⟩ : syracuseStep 702047 = 1053071) B1053071
theorem B931945 : Blo 550806 931945 := bstep (se 2 (by rfl) ⟨349479, by rfl⟩ : syracuseStep 931945 = 698959) B698959
theorem B5814823 : Blo 550806 5814823 := bstep (se 1 (by rfl) ⟨4361117, by rfl⟩ : syracuseStep 5814823 = 8722235) B8722235
theorem B1686089 : Blo 550806 1686089 := bstep (se 2 (by rfl) ⟨632283, by rfl⟩ : syracuseStep 1686089 = 1264567) B1264567
theorem B1489835 : Blo 550806 1489835 := bstep (se 1 (by rfl) ⟨1117376, by rfl⟩ : syracuseStep 1489835 = 2234753) B2234753
theorem B2800655 : Blo 550806 2800655 := bstep (se 1 (by rfl) ⟨2100491, by rfl⟩ : syracuseStep 2800655 = 4200983) B4200983
theorem B3980477 : Blo 550806 3980477 := bstep (se 3 (by rfl) ⟨746339, by rfl⟩ : syracuseStep 3980477 = 1492679) B1492679
theorem B1260937 : Blo 550806 1260937 := bstep (se 2 (by rfl) ⟨472851, by rfl⟩ : syracuseStep 1260937 = 945703) B945703
theorem B2080337 : Blo 550806 2080337 := bstep (se 2 (by rfl) ⟨780126, by rfl⟩ : syracuseStep 2080337 = 1560253) B1560253
theorem B4472617 : Blo 550806 4472617 := bstep (se 2 (by rfl) ⟨1677231, by rfl⟩ : syracuseStep 4472617 = 3354463) B3354463
theorem B933673 : Blo 550806 933673 := bstep (se 2 (by rfl) ⟨350127, by rfl⟩ : syracuseStep 933673 = 700255) B700255
theorem B2801465 : Blo 550806 2801465 := bstep (se 2 (by rfl) ⟨1050549, by rfl⟩ : syracuseStep 2801465 = 2101099) B2101099
theorem B934463 : Blo 550806 934463 := bstep (se 1 (by rfl) ⟨700847, by rfl⟩ : syracuseStep 934463 = 1401695) B1401695
theorem B441762497 : Blo 550806 441762497 := bstep (se 2 (by rfl) ⟨165660936, by rfl⟩ : syracuseStep 441762497 = 331321873) B331321873
theorem B4211675 : Blo 550806 4211675 := bstep (se 1 (by rfl) ⟨3158756, by rfl⟩ : syracuseStep 4211675 = 6317513) B6317513
theorem B935131 : Blo 550806 935131 := bstep (se 1 (by rfl) ⟨701348, by rfl⟩ : syracuseStep 935131 = 1402697) B1402697
theorem B7161331 : Blo 550806 7161331 := bstep (se 1 (by rfl) ⟨5370998, by rfl⟩ : syracuseStep 7161331 = 10741997) B10741997
theorem B32261645 : Blo 550806 32261645 := bstep (se 3 (by rfl) ⟨6049058, by rfl⟩ : syracuseStep 32261645 = 12098117) B12098117
theorem B1197755 : Blo 550806 1197755 := bstep (se 1 (by rfl) ⟨898316, by rfl⟩ : syracuseStep 1197755 = 1796633) B1796633
theorem B935887 : Blo 550806 935887 := bstep (se 1 (by rfl) ⟨701915, by rfl⟩ : syracuseStep 935887 = 1403831) B1403831
theorem B15157489 : Blo 550806 15157489 := bstep (se 2 (by rfl) ⟨5684058, by rfl⟩ : syracuseStep 15157489 = 11368117) B11368117
theorem B2804219 : Blo 550806 2804219 := bstep (se 1 (by rfl) ⟨2103164, by rfl⟩ : syracuseStep 2804219 = 4206329) B4206329
theorem B1329911 : Blo 550806 1329911 := bstep (se 1 (by rfl) ⟨997433, by rfl⟩ : syracuseStep 1329911 = 1994867) B1994867
theorem B1395751 : Blo 550806 1395751 := bstep (se 1 (by rfl) ⟨1046813, by rfl⟩ : syracuseStep 1395751 = 2093627) B2093627
theorem B1330391 : Blo 550806 1330391 := bstep (se 1 (by rfl) ⟨997793, by rfl⟩ : syracuseStep 1330391 = 1995587) B1995587
theorem B1985755 : Blo 550806 1985755 := bstep (se 1 (by rfl) ⟨1489316, by rfl⟩ : syracuseStep 1985755 = 2978633) B2978633
theorem B2805191 : Blo 550806 2805191 := bstep (se 1 (by rfl) ⟨2103893, by rfl⟩ : syracuseStep 2805191 = 4207787) B4207787
theorem B1396217 : Blo 550806 1396217 := bstep (se 2 (by rfl) ⟨523581, by rfl⟩ : syracuseStep 1396217 = 1047163) B1047163
theorem B2838131 : Blo 550806 2838131 := bstep (se 1 (by rfl) ⟨2128598, by rfl⟩ : syracuseStep 2838131 = 4257197) B4257197
theorem B2805515 : Blo 550806 2805515 := bstep (se 1 (by rfl) ⟨2104136, by rfl⟩ : syracuseStep 2805515 = 4208273) B4208273
theorem B1396865 : Blo 550806 1396865 := bstep (se 2 (by rfl) ⟨523824, by rfl⟩ : syracuseStep 1396865 = 1047649) B1047649
theorem B1397159 : Blo 550806 1397159 := bstep (se 1 (by rfl) ⟨1047869, by rfl⟩ : syracuseStep 1397159 = 2095739) B2095739
theorem B1397321 : Blo 550806 1397321 := bstep (se 2 (by rfl) ⟨523995, by rfl⟩ : syracuseStep 1397321 = 1047991) B1047991
theorem B2806487 : Blo 550806 2806487 := bstep (se 1 (by rfl) ⟨2104865, by rfl⟩ : syracuseStep 2806487 = 4209731) B4209731
theorem B1397675 : Blo 550806 1397675 := bstep (se 1 (by rfl) ⟨1048256, by rfl⟩ : syracuseStep 1397675 = 2096513) B2096513
theorem B1397857 : Blo 550806 1397857 := bstep (se 2 (by rfl) ⟨524196, by rfl⟩ : syracuseStep 1397857 = 1048393) B1048393
theorem B2807135 : Blo 550806 2807135 := bstep (se 1 (by rfl) ⟨2105351, by rfl⟩ : syracuseStep 2807135 = 4210703) B4210703
theorem B1496519 : Blo 550806 1496519 := bstep (se 1 (by rfl) ⟨1122389, by rfl⟩ : syracuseStep 1496519 = 2244779) B2244779
theorem B1922617 : Blo 550806 1922617 := bstep (se 2 (by rfl) ⟨720981, by rfl⟩ : syracuseStep 1922617 = 1441963) B1441963
theorem B710251 : Blo 550806 710251 := bstep (se 1 (by rfl) ⟨532688, by rfl⟩ : syracuseStep 710251 = 1065377) B1065377
theorem B2021021 : Blo 550806 2021021 := bstep (se 3 (by rfl) ⟨378941, by rfl⟩ : syracuseStep 2021021 = 757883) B757883
theorem B35739407 : Blo 550806 35739407 := bstep (se 1 (by rfl) ⟨26804555, by rfl⟩ : syracuseStep 35739407 = 53609111) B53609111
theorem B1398809 : Blo 550806 1398809 := bstep (se 2 (by rfl) ⟨524553, by rfl⟩ : syracuseStep 1398809 = 1049107) B1049107
theorem B3037313 : Blo 550806 3037313 := bstep (se 2 (by rfl) ⟨1138992, by rfl⟩ : syracuseStep 3037313 = 2277985) B2277985
theorem B5036365 : Blo 550806 5036365 := bstep (se 3 (by rfl) ⟨944318, by rfl⟩ : syracuseStep 5036365 = 1888637) B1888637
theorem B1399265 : Blo 550806 1399265 := bstep (se 2 (by rfl) ⟨524724, by rfl⟩ : syracuseStep 1399265 = 1049449) B1049449
theorem B1399315 : Blo 550806 1399315 := bstep (se 1 (by rfl) ⟨1049486, by rfl⟩ : syracuseStep 1399315 = 2098973) B2098973
theorem B10738615 : Blo 550806 10738615 := bstep (se 1 (by rfl) ⟨8053961, by rfl⟩ : syracuseStep 10738615 = 16107923) B16107923
theorem B1989821 : Blo 550806 1989821 := bstep (se 3 (by rfl) ⟨373091, by rfl⟩ : syracuseStep 1989821 = 746183) B746183
theorem B1859003 : Blo 550806 1859003 := bstep (se 1 (by rfl) ⟨1394252, by rfl⟩ : syracuseStep 1859003 = 2788505) B2788505
theorem B3530537 : Blo 550806 3530537 := bstep (se 2 (by rfl) ⟨1323951, by rfl⟩ : syracuseStep 3530537 = 2647903) B2647903
theorem B4185917 : Blo 550806 4185917 := bstep (se 3 (by rfl) ⟨784859, by rfl⟩ : syracuseStep 4185917 = 1569719) B1569719
theorem B5693257 : Blo 550806 5693257 := bstep (se 2 (by rfl) ⟨2134971, by rfl⟩ : syracuseStep 5693257 = 4269943) B4269943
theorem B4710251 : Blo 550806 4710251 := bstep (se 1 (by rfl) ⟨3532688, by rfl⟩ : syracuseStep 4710251 = 7065377) B7065377
theorem B21520247 : Blo 550806 21520247 := bstep (se 1 (by rfl) ⟨16140185, by rfl⟩ : syracuseStep 21520247 = 32280371) B32280371
theorem B5988401 : Blo 550806 5988401 := bstep (se 2 (by rfl) ⟨2245650, by rfl⟩ : syracuseStep 5988401 = 4491301) B4491301
theorem B7561349 : Blo 550806 7561349 := bstep (se 4 (by rfl) ⟨708876, by rfl⟩ : syracuseStep 7561349 = 1417753) B1417753
theorem B3039443 : Blo 550806 3039443 := bstep (se 1 (by rfl) ⟨2279582, by rfl⟩ : syracuseStep 3039443 = 4559165) B4559165
theorem B1401097 : Blo 550806 1401097 := bstep (se 2 (by rfl) ⟨525411, by rfl⟩ : syracuseStep 1401097 = 1050823) B1050823
theorem B746167 : Blo 550806 746167 := bstep (se 1 (by rfl) ⟨559625, by rfl⟩ : syracuseStep 746167 = 1119251) B1119251
theorem B3793591 : Blo 550806 3793591 := bstep (se 1 (by rfl) ⟨2845193, by rfl⟩ : syracuseStep 3793591 = 5690387) B5690387
theorem B9069407 : Blo 550806 9069407 := bstep (se 1 (by rfl) ⟨6802055, by rfl⟩ : syracuseStep 9069407 = 13604111) B13604111
theorem B5989783 : Blo 550806 5989783 := bstep (se 1 (by rfl) ⟨4492337, by rfl⟩ : syracuseStep 5989783 = 8984675) B8984675
theorem B1402555 : Blo 550806 1402555 := bstep (se 1 (by rfl) ⟨1051916, by rfl⟩ : syracuseStep 1402555 = 2103833) B2103833
theorem B6383393 : Blo 550806 6383393 := bstep (se 2 (by rfl) ⟨2393772, by rfl⟩ : syracuseStep 6383393 = 4787545) B4787545
theorem B4417361 : Blo 550806 4417361 := bstep (se 2 (by rfl) ⟨1656510, by rfl⟩ : syracuseStep 4417361 = 3313021) B3313021
theorem B2844497 : Blo 550806 2844497 := bstep (se 2 (by rfl) ⟨1066686, by rfl⟩ : syracuseStep 2844497 = 2133373) B2133373
theorem B550811 : Blo 550806 550811 := bstep (se 1 (by rfl) ⟨413108, by rfl⟩ : syracuseStep 550811 = 826217) B826217
theorem B550863 : Blo 550806 550863 := bstep (se 1 (by rfl) ⟨413147, by rfl⟩ : syracuseStep 550863 = 826295) B826295
theorem B550887 : Blo 550806 550887 := bstep (se 1 (by rfl) ⟨413165, by rfl⟩ : syracuseStep 550887 = 826331) B826331
theorem B551199 : Blo 550806 551199 := bstep (se 1 (by rfl) ⟨413399, by rfl⟩ : syracuseStep 551199 = 826799) B826799
theorem B551259 : Blo 550806 551259 := bstep (se 1 (by rfl) ⟨413444, by rfl⟩ : syracuseStep 551259 = 826889) B826889
theorem B1239407 : Blo 550806 1239407 := bstep (se 1 (by rfl) ⟨929555, by rfl⟩ : syracuseStep 1239407 = 1859111) B1859111
theorem B551279 : Blo 550806 551279 := bstep (se 1 (by rfl) ⟨413459, by rfl⟩ : syracuseStep 551279 = 826919) B826919
theorem B551335 : Blo 550806 551335 := bstep (se 1 (by rfl) ⟨413501, by rfl⟩ : syracuseStep 551335 = 827003) B827003
theorem B1239479 : Blo 550806 1239479 := bstep (se 1 (by rfl) ⟨929609, by rfl⟩ : syracuseStep 1239479 = 1859219) B1859219
theorem B551419 : Blo 550806 551419 := bstep (se 1 (by rfl) ⟨413564, by rfl⟩ : syracuseStep 551419 = 827129) B827129
theorem B551487 : Blo 550806 551487 := bstep (se 1 (by rfl) ⟨413615, by rfl⟩ : syracuseStep 551487 = 827231) B827231
theorem B1239623 : Blo 550806 1239623 := bstep (se 1 (by rfl) ⟨929717, by rfl⟩ : syracuseStep 1239623 = 1859435) B1859435
theorem B551495 : Blo 550806 551495 := bstep (se 1 (by rfl) ⟨413621, by rfl⟩ : syracuseStep 551495 = 827243) B827243
theorem B1796681 : Blo 550806 1796681 := bstep (se 2 (by rfl) ⟨673755, by rfl⟩ : syracuseStep 1796681 = 1347511) B1347511
theorem B1239659 : Blo 550806 1239659 := bstep (se 1 (by rfl) ⟨929744, by rfl⟩ : syracuseStep 1239659 = 1859489) B1859489
theorem B551647 : Blo 550806 551647 := bstep (se 1 (by rfl) ⟨413735, by rfl⟩ : syracuseStep 551647 = 827471) B827471
theorem B1403639 : Blo 550806 1403639 := bstep (se 1 (by rfl) ⟨1052729, by rfl⟩ : syracuseStep 1403639 = 2105459) B2105459
theorem B551727 : Blo 550806 551727 := bstep (se 1 (by rfl) ⟨413795, by rfl⟩ : syracuseStep 551727 = 827591) B827591
theorem B551835 : Blo 550806 551835 := bstep (se 1 (by rfl) ⟨413876, by rfl⟩ : syracuseStep 551835 = 827753) B827753
theorem B551887 : Blo 550806 551887 := bstep (se 1 (by rfl) ⟨413915, by rfl⟩ : syracuseStep 551887 = 827831) B827831
theorem B551911 : Blo 550806 551911 := bstep (se 1 (by rfl) ⟨413933, by rfl⟩ : syracuseStep 551911 = 827867) B827867
theorem B1240055 : Blo 550806 1240055 := bstep (se 1 (by rfl) ⟨930041, by rfl⟩ : syracuseStep 1240055 = 1860083) B1860083
theorem B2354291 : Blo 550806 2354291 := bstep (se 1 (by rfl) ⟨1765718, by rfl⟩ : syracuseStep 2354291 = 3531437) B3531437
theorem B552223 : Blo 550806 552223 := bstep (se 1 (by rfl) ⟨414167, by rfl⟩ : syracuseStep 552223 = 828335) B828335
theorem B552283 : Blo 550806 552283 := bstep (se 1 (by rfl) ⟨414212, by rfl⟩ : syracuseStep 552283 = 828425) B828425
theorem B1240415 : Blo 550806 1240415 := bstep (se 1 (by rfl) ⟨930311, by rfl⟩ : syracuseStep 1240415 = 1860623) B1860623
theorem B552303 : Blo 550806 552303 := bstep (se 1 (by rfl) ⟨414227, by rfl⟩ : syracuseStep 552303 = 828455) B828455
theorem B552359 : Blo 550806 552359 := bstep (se 1 (by rfl) ⟨414269, by rfl⟩ : syracuseStep 552359 = 828539) B828539
theorem B1863161 : Blo 550806 1863161 := bstep (se 2 (by rfl) ⟨698685, by rfl⟩ : syracuseStep 1863161 = 1397371) B1397371
theorem B552443 : Blo 550806 552443 := bstep (se 1 (by rfl) ⟨414332, by rfl⟩ : syracuseStep 552443 = 828665) B828665
theorem B552511 : Blo 550806 552511 := bstep (se 1 (by rfl) ⟨414383, by rfl⟩ : syracuseStep 552511 = 828767) B828767
theorem B552519 : Blo 550806 552519 := bstep (se 1 (by rfl) ⟨414389, by rfl⟩ : syracuseStep 552519 = 828779) B828779
theorem B2092625 : Blo 550806 2092625 := bstep (se 2 (by rfl) ⟨784734, by rfl⟩ : syracuseStep 2092625 = 1569469) B1569469
theorem B4189805 : Blo 550806 4189805 := bstep (se 3 (by rfl) ⟨785588, by rfl⟩ : syracuseStep 4189805 = 1571177) B1571177
theorem B552671 : Blo 550806 552671 := bstep (se 1 (by rfl) ⟨414503, by rfl⟩ : syracuseStep 552671 = 829007) B829007
theorem B1240811 : Blo 550806 1240811 := bstep (se 1 (by rfl) ⟨930608, by rfl⟩ : syracuseStep 1240811 = 1861217) B1861217
theorem B1863431 : Blo 550806 1863431 := bstep (se 1 (by rfl) ⟨1397573, by rfl⟩ : syracuseStep 1863431 = 2795147) B2795147
theorem B552751 : Blo 550806 552751 := bstep (se 1 (by rfl) ⟨414563, by rfl⟩ : syracuseStep 552751 = 829127) B829127
theorem B1863485 : Blo 550806 1863485 := bstep (se 3 (by rfl) ⟨349403, by rfl⟩ : syracuseStep 1863485 = 698807) B698807
theorem B1240937 : Blo 550806 1240937 := bstep (se 2 (by rfl) ⟨465351, by rfl⟩ : syracuseStep 1240937 = 930703) B930703
theorem B552859 : Blo 550806 552859 := bstep (se 1 (by rfl) ⟨414644, by rfl⟩ : syracuseStep 552859 = 829289) B829289
theorem B552911 : Blo 550806 552911 := bstep (se 1 (by rfl) ⟨414683, by rfl⟩ : syracuseStep 552911 = 829367) B829367
theorem B552935 : Blo 550806 552935 := bstep (se 1 (by rfl) ⟨414701, by rfl⟩ : syracuseStep 552935 = 829403) B829403
theorem B26570753 : Blo 550806 26570753 := bstep (se 2 (by rfl) ⟨9964032, by rfl⟩ : syracuseStep 26570753 = 19928065) B19928065
theorem B11923523 : Blo 550806 11923523 := bstep (se 1 (by rfl) ⟨8942642, by rfl⟩ : syracuseStep 11923523 = 17885285) B17885285
theorem B553247 : Blo 550806 553247 := bstep (se 1 (by rfl) ⟨414935, by rfl⟩ : syracuseStep 553247 = 829871) B829871
theorem B553307 : Blo 550806 553307 := bstep (se 1 (by rfl) ⟨414980, by rfl⟩ : syracuseStep 553307 = 829961) B829961
theorem B553327 : Blo 550806 553327 := bstep (se 1 (by rfl) ⟨414995, by rfl⟩ : syracuseStep 553327 = 829991) B829991
theorem B553383 : Blo 550806 553383 := bstep (se 1 (by rfl) ⟨415037, by rfl⟩ : syracuseStep 553383 = 830075) B830075
theorem B553467 : Blo 550806 553467 := bstep (se 1 (by rfl) ⟨415100, by rfl⟩ : syracuseStep 553467 = 830201) B830201
theorem B10121773 : Blo 550806 10121773 := bstep (se 3 (by rfl) ⟨1897832, by rfl⟩ : syracuseStep 10121773 = 3795665) B3795665
theorem B553535 : Blo 550806 553535 := bstep (se 1 (by rfl) ⟨415151, by rfl⟩ : syracuseStep 553535 = 830303) B830303
theorem B553543 : Blo 550806 553543 := bstep (se 1 (by rfl) ⟨415157, by rfl⟩ : syracuseStep 553543 = 830315) B830315
theorem B1569401 : Blo 550806 1569401 := bstep (se 2 (by rfl) ⟨588525, by rfl⟩ : syracuseStep 1569401 = 1177051) B1177051
theorem B7959161 : Blo 550806 7959161 := bstep (se 2 (by rfl) ⟨2984685, by rfl⟩ : syracuseStep 7959161 = 5969371) B5969371
theorem B1241783 : Blo 550806 1241783 := bstep (se 1 (by rfl) ⟨931337, by rfl⟩ : syracuseStep 1241783 = 1862675) B1862675
theorem B3535559 : Blo 550806 3535559 := bstep (se 1 (by rfl) ⟨2651669, by rfl⟩ : syracuseStep 3535559 = 5303339) B5303339
theorem B553695 : Blo 550806 553695 := bstep (se 1 (by rfl) ⟨415271, by rfl⟩ : syracuseStep 553695 = 830543) B830543
theorem B553775 : Blo 550806 553775 := bstep (se 1 (by rfl) ⟨415331, by rfl⟩ : syracuseStep 553775 = 830663) B830663
theorem B1241999 : Blo 550806 1241999 := bstep (se 1 (by rfl) ⟨931499, by rfl⟩ : syracuseStep 1241999 = 1862999) B1862999
theorem B553883 : Blo 550806 553883 := bstep (se 1 (by rfl) ⟨415412, by rfl⟩ : syracuseStep 553883 = 830825) B830825
theorem B553935 : Blo 550806 553935 := bstep (se 1 (by rfl) ⟨415451, by rfl⟩ : syracuseStep 553935 = 830903) B830903
theorem B553959 : Blo 550806 553959 := bstep (se 1 (by rfl) ⟨415469, by rfl⟩ : syracuseStep 553959 = 830939) B830939
theorem B7992377 : Blo 550806 7992377 := bstep (se 2 (by rfl) ⟨2997141, by rfl⟩ : syracuseStep 7992377 = 5994283) B5994283
theorem B2094295 : Blo 550806 2094295 := bstep (se 1 (by rfl) ⟨1570721, by rfl⟩ : syracuseStep 2094295 = 3141443) B3141443
theorem B619807 : Blo 550806 619807 := bstep (se 1 (by rfl) ⟨464855, by rfl⟩ : syracuseStep 619807 = 929711) B929711
theorem B554271 : Blo 550806 554271 := bstep (se 1 (by rfl) ⟨415703, by rfl⟩ : syracuseStep 554271 = 831407) B831407
theorem B554331 : Blo 550806 554331 := bstep (se 1 (by rfl) ⟨415748, by rfl⟩ : syracuseStep 554331 = 831497) B831497
theorem B554351 : Blo 550806 554351 := bstep (se 1 (by rfl) ⟨415763, by rfl⟩ : syracuseStep 554351 = 831527) B831527
theorem B554407 : Blo 550806 554407 := bstep (se 1 (by rfl) ⟨415805, by rfl⟩ : syracuseStep 554407 = 831611) B831611
theorem B1046009 : Blo 550806 1046009 := bstep (se 2 (by rfl) ⟨392253, by rfl⟩ : syracuseStep 1046009 = 784507) B784507
theorem B554491 : Blo 550806 554491 := bstep (se 1 (by rfl) ⟨415868, by rfl⟩ : syracuseStep 554491 = 831737) B831737
theorem B2094599 : Blo 550806 2094599 := bstep (se 1 (by rfl) ⟨1570949, by rfl⟩ : syracuseStep 2094599 = 3141899) B3141899
theorem B620095 : Blo 550806 620095 := bstep (se 1 (by rfl) ⟨465071, by rfl⟩ : syracuseStep 620095 = 930143) B930143
theorem B554559 : Blo 550806 554559 := bstep (se 1 (by rfl) ⟨415919, by rfl⟩ : syracuseStep 554559 = 831839) B831839
theorem B554567 : Blo 550806 554567 := bstep (se 1 (by rfl) ⟨415925, by rfl⟩ : syracuseStep 554567 = 831851) B831851
theorem B1242719 : Blo 550806 1242719 := bstep (se 1 (by rfl) ⟨932039, by rfl⟩ : syracuseStep 1242719 = 1864079) B1864079
theorem B554719 : Blo 550806 554719 := bstep (se 1 (by rfl) ⟨416039, by rfl⟩ : syracuseStep 554719 = 832079) B832079
theorem B554799 : Blo 550806 554799 := bstep (se 1 (by rfl) ⟨416099, by rfl⟩ : syracuseStep 554799 = 832199) B832199
theorem B1242935 : Blo 550806 1242935 := bstep (se 1 (by rfl) ⟨932201, by rfl⟩ : syracuseStep 1242935 = 1864403) B1864403
theorem B2095055 : Blo 550806 2095055 := bstep (se 1 (by rfl) ⟨1571291, by rfl⟩ : syracuseStep 2095055 = 3142583) B3142583
theorem B2095085 : Blo 550806 2095085 := bstep (se 3 (by rfl) ⟨392828, by rfl⟩ : syracuseStep 2095085 = 785657) B785657
theorem B1243241 : Blo 550806 1243241 := bstep (se 2 (by rfl) ⟨466215, by rfl⟩ : syracuseStep 1243241 = 932431) B932431
theorem B2652439 : Blo 550806 2652439 := bstep (se 1 (by rfl) ⟨1989329, by rfl⟩ : syracuseStep 2652439 = 3978659) B3978659
theorem B620923 : Blo 550806 620923 := bstep (se 1 (by rfl) ⟨465692, by rfl⟩ : syracuseStep 620923 = 931385) B931385
theorem B2095571 : Blo 550806 2095571 := bstep (se 1 (by rfl) ⟨1571678, by rfl⟩ : syracuseStep 2095571 = 3143357) B3143357
theorem B2128447 : Blo 550806 2128447 := bstep (se 1 (by rfl) ⟨1596335, by rfl⟩ : syracuseStep 2128447 = 3192671) B3192671
theorem B948809 : Blo 550806 948809 := bstep (se 2 (by rfl) ⟨355803, by rfl⟩ : syracuseStep 948809 = 711607) B711607
theorem B1243727 : Blo 550806 1243727 := bstep (se 1 (by rfl) ⟨932795, by rfl⟩ : syracuseStep 1243727 = 1865591) B1865591
theorem B1866347 : Blo 550806 1866347 := bstep (se 1 (by rfl) ⟨1399760, by rfl⟩ : syracuseStep 1866347 = 2799521) B2799521
theorem B883423 : Blo 550806 883423 := bstep (se 1 (by rfl) ⟨662567, by rfl⟩ : syracuseStep 883423 = 1325135) B1325135
theorem B1243871 : Blo 550806 1243871 := bstep (se 1 (by rfl) ⟨932903, by rfl⟩ : syracuseStep 1243871 = 1865807) B1865807
theorem B621391 : Blo 550806 621391 := bstep (se 1 (by rfl) ⟨466043, by rfl⟩ : syracuseStep 621391 = 932087) B932087
theorem B2882429 : Blo 550806 2882429 := bstep (se 3 (by rfl) ⟨540455, by rfl⟩ : syracuseStep 2882429 = 1080911) B1080911
theorem B1997693 : Blo 550806 1997693 := bstep (se 3 (by rfl) ⟨374567, by rfl⟩ : syracuseStep 1997693 = 749135) B749135
theorem B2096027 : Blo 550806 2096027 := bstep (se 1 (by rfl) ⟨1572020, by rfl⟩ : syracuseStep 2096027 = 3144041) B3144041
theorem B1047467 : Blo 550806 1047467 := bstep (se 1 (by rfl) ⟨785600, by rfl⟩ : syracuseStep 1047467 = 1571201) B1571201
theorem B1244123 : Blo 550806 1244123 := bstep (se 1 (by rfl) ⟨933092, by rfl⟩ : syracuseStep 1244123 = 1866185) B1866185
theorem B1244303 : Blo 550806 1244303 := bstep (se 1 (by rfl) ⟨933227, by rfl⟩ : syracuseStep 1244303 = 1866455) B1866455
theorem B1866941 : Blo 550806 1866941 := bstep (se 3 (by rfl) ⟨350051, by rfl⟩ : syracuseStep 1866941 = 700103) B700103
theorem B621787 : Blo 550806 621787 := bstep (se 1 (by rfl) ⟨466340, by rfl⟩ : syracuseStep 621787 = 932681) B932681
theorem B1244393 : Blo 550806 1244393 := bstep (se 2 (by rfl) ⟨466647, by rfl⟩ : syracuseStep 1244393 = 933295) B933295
theorem B1244447 : Blo 550806 1244447 := bstep (se 1 (by rfl) ⟨933335, by rfl⟩ : syracuseStep 1244447 = 1866671) B1866671
theorem B2358665 : Blo 550806 2358665 := bstep (se 2 (by rfl) ⟨884499, by rfl⟩ : syracuseStep 2358665 = 1768999) B1768999
theorem B622075 : Blo 550806 622075 := bstep (se 1 (by rfl) ⟨466556, by rfl⟩ : syracuseStep 622075 = 933113) B933113
theorem B622255 : Blo 550806 622255 := bstep (se 1 (by rfl) ⟨466691, by rfl⟩ : syracuseStep 622255 = 933383) B933383
theorem B1244969 : Blo 550806 1244969 := bstep (se 2 (by rfl) ⟨466863, by rfl⟩ : syracuseStep 1244969 = 933727) B933727
theorem B5046077 : Blo 550806 5046077 := bstep (se 3 (by rfl) ⟨946139, by rfl⟩ : syracuseStep 5046077 = 1892279) B1892279
theorem B622543 : Blo 550806 622543 := bstep (se 1 (by rfl) ⟨466907, by rfl⟩ : syracuseStep 622543 = 933815) B933815
theorem B1868129 : Blo 550806 1868129 := bstep (se 2 (by rfl) ⟨700548, by rfl⟩ : syracuseStep 1868129 = 1401097) B1401097
theorem B622975 : Blo 550806 622975 := bstep (se 1 (by rfl) ⟨467231, by rfl⟩ : syracuseStep 622975 = 934463) B934463
theorem B1573319 : Blo 550806 1573319 := bstep (se 1 (by rfl) ⟨1179989, by rfl⟩ : syracuseStep 1573319 = 2359979) B2359979
theorem B8520187 : Blo 550806 8520187 := bstep (se 1 (by rfl) ⟨6390140, by rfl⟩ : syracuseStep 8520187 = 12780281) B12780281
theorem B7570097 : Blo 550806 7570097 := bstep (se 2 (by rfl) ⟨2838786, by rfl⟩ : syracuseStep 7570097 = 5677573) B5677573
theorem B1573775 : Blo 550806 1573775 := bstep (se 1 (by rfl) ⟨1180331, by rfl⟩ : syracuseStep 1573775 = 2360663) B2360663
theorem B1573843 : Blo 550806 1573843 := bstep (se 1 (by rfl) ⟨1180382, by rfl⟩ : syracuseStep 1573843 = 2360765) B2360765
theorem B1246571 : Blo 550806 1246571 := bstep (se 1 (by rfl) ⟨934928, by rfl⟩ : syracuseStep 1246571 = 1869857) B1869857
theorem B1246841 : Blo 550806 1246841 := bstep (se 2 (by rfl) ⟨467565, by rfl⟩ : syracuseStep 1246841 = 935131) B935131
theorem B1869479 : Blo 550806 1869479 := bstep (se 1 (by rfl) ⟨1402109, by rfl⟩ : syracuseStep 1869479 = 2804219) B2804219
theorem B886607 : Blo 550806 886607 := bstep (se 1 (by rfl) ⟨664955, by rfl⟩ : syracuseStep 886607 = 1329911) B1329911
theorem B9439091 : Blo 550806 9439091 := bstep (se 1 (by rfl) ⟨7079318, by rfl⟩ : syracuseStep 9439091 = 14158637) B14158637
theorem B1574903 : Blo 550806 1574903 := bstep (se 1 (by rfl) ⟨1181177, by rfl⟩ : syracuseStep 1574903 = 2362355) B2362355
theorem B887017 : Blo 550806 887017 := bstep (se 2 (by rfl) ⟨332631, by rfl⟩ : syracuseStep 887017 = 665263) B665263
theorem B1870073 : Blo 550806 1870073 := bstep (se 2 (by rfl) ⟨701277, by rfl⟩ : syracuseStep 1870073 = 1402555) B1402555
theorem B7670051 : Blo 550806 7670051 := bstep (se 1 (by rfl) ⟨5752538, by rfl⟩ : syracuseStep 7670051 = 11505077) B11505077
theorem B1870127 : Blo 550806 1870127 := bstep (se 1 (by rfl) ⟨1402595, by rfl⟩ : syracuseStep 1870127 = 2805191) B2805191
theorem B1870343 : Blo 550806 1870343 := bstep (se 1 (by rfl) ⟨1402757, by rfl⟩ : syracuseStep 1870343 = 2805515) B2805515
theorem B1182313 : Blo 550806 1182313 := bstep (se 2 (by rfl) ⟨443367, by rfl⟩ : syracuseStep 1182313 = 886735) B886735
theorem B789097 : Blo 550806 789097 := bstep (se 2 (by rfl) ⟨295911, by rfl⟩ : syracuseStep 789097 = 591823) B591823
theorem B1247849 : Blo 550806 1247849 := bstep (se 2 (by rfl) ⟨467943, by rfl⟩ : syracuseStep 1247849 = 935887) B935887
theorem B1870991 : Blo 550806 1870991 := bstep (se 1 (by rfl) ⟨1403243, by rfl⟩ : syracuseStep 1870991 = 2806487) B2806487
theorem B1576361 : Blo 550806 1576361 := bstep (se 2 (by rfl) ⟨591135, by rfl⟩ : syracuseStep 1576361 = 1182271) B1182271
theorem B1871423 : Blo 550806 1871423 := bstep (se 1 (by rfl) ⟨1403567, by rfl⟩ : syracuseStep 1871423 = 2807135) B2807135
theorem B1347347 : Blo 550806 1347347 := bstep (se 1 (by rfl) ⟨1010510, by rfl⟩ : syracuseStep 1347347 = 2021021) B2021021
theorem B23826271 : Blo 550806 23826271 := bstep (se 1 (by rfl) ⟨17869703, by rfl⟩ : syracuseStep 23826271 = 35739407) B35739407
theorem B17961047 : Blo 550806 17961047 := bstep (se 1 (by rfl) ⟨13470785, by rfl⟩ : syracuseStep 17961047 = 26941571) B26941571
theorem B4198553 : Blo 550806 4198553 := bstep (se 2 (by rfl) ⟨1574457, by rfl⟩ : syracuseStep 4198553 = 3148915) B3148915
theorem B1872125 : Blo 550806 1872125 := bstep (se 3 (by rfl) ⟨351023, by rfl⟩ : syracuseStep 1872125 = 702047) B702047
theorem B3150191 : Blo 550806 3150191 := bstep (se 1 (by rfl) ⟨2362643, by rfl⟩ : syracuseStep 3150191 = 4725287) B4725287
theorem B1577465 : Blo 550806 1577465 := bstep (se 2 (by rfl) ⟨591549, by rfl⟩ : syracuseStep 1577465 = 1183099) B1183099
theorem B1774163 : Blo 550806 1774163 := bstep (se 1 (by rfl) ⟨1330622, by rfl⟩ : syracuseStep 1774163 = 2661245) B2661245
theorem B2102057 : Blo 550806 2102057 := bstep (se 2 (by rfl) ⟨788271, by rfl⟩ : syracuseStep 2102057 = 1576543) B1576543
theorem B2790611 : Blo 550806 2790611 := bstep (se 1 (by rfl) ⟨2092958, by rfl⟩ : syracuseStep 2790611 = 4185917) B4185917
theorem B1775047 : Blo 550806 1775047 := bstep (se 1 (by rfl) ⟨1331285, by rfl⟩ : syracuseStep 1775047 = 2662571) B2662571
theorem B14358059 : Blo 550806 14358059 := bstep (se 1 (by rfl) ⟨10768544, by rfl⟩ : syracuseStep 14358059 = 21537089) B21537089
theorem B2365037 : Blo 550806 2365037 := bstep (se 3 (by rfl) ⟨443444, by rfl⟩ : syracuseStep 2365037 = 886889) B886889
theorem B3151831 : Blo 550806 3151831 := bstep (se 1 (by rfl) ⟨2363873, by rfl⟩ : syracuseStep 3151831 = 4727747) B4727747
theorem B1579105 : Blo 550806 1579105 := bstep (se 2 (by rfl) ⟨592164, by rfl⟩ : syracuseStep 1579105 = 1184329) B1184329
theorem B1579151 : Blo 550806 1579151 := bstep (se 1 (by rfl) ⟨1184363, by rfl⟩ : syracuseStep 1579151 = 2368727) B2368727
theorem B3152357 : Blo 550806 3152357 := bstep (se 4 (by rfl) ⟨295533, by rfl⟩ : syracuseStep 3152357 = 591067) B591067
theorem B10623899 : Blo 550806 10623899 := bstep (se 1 (by rfl) ⟨7967924, by rfl⟩ : syracuseStep 10623899 = 15935849) B15935849
theorem B826271 : Blo 550806 826271 := bstep (se 1 (by rfl) ⟨619703, by rfl⟩ : syracuseStep 826271 = 1239407) B1239407
theorem B2792393 : Blo 550806 2792393 := bstep (se 2 (by rfl) ⟨1047147, by rfl⟩ : syracuseStep 2792393 = 2094295) B2094295
theorem B826319 : Blo 550806 826319 := bstep (se 1 (by rfl) ⟨619739, by rfl⟩ : syracuseStep 826319 = 1239479) B1239479
theorem B2104289 : Blo 550806 2104289 := bstep (se 2 (by rfl) ⟨789108, by rfl⟩ : syracuseStep 2104289 = 1578217) B1578217
theorem B2366455 : Blo 550806 2366455 := bstep (se 1 (by rfl) ⟨1774841, by rfl⟩ : syracuseStep 2366455 = 3549683) B3549683
theorem B826409 : Blo 550806 826409 := bstep (se 2 (by rfl) ⟨309903, by rfl⟩ : syracuseStep 826409 = 619807) B619807
theorem B826415 : Blo 550806 826415 := bstep (se 1 (by rfl) ⟨619811, by rfl⟩ : syracuseStep 826415 = 1239623) B1239623
theorem B826439 : Blo 550806 826439 := bstep (se 1 (by rfl) ⟨619829, by rfl⟩ : syracuseStep 826439 = 1239659) B1239659
theorem B826703 : Blo 550806 826703 := bstep (se 1 (by rfl) ⟨620027, by rfl⟩ : syracuseStep 826703 = 1240055) B1240055
theorem B2563489 : Blo 550806 2563489 := bstep (se 2 (by rfl) ⟨961308, by rfl⟩ : syracuseStep 2563489 = 1922617) B1922617
theorem B826793 : Blo 550806 826793 := bstep (se 2 (by rfl) ⟨310047, by rfl⟩ : syracuseStep 826793 = 620095) B620095
theorem B826943 : Blo 550806 826943 := bstep (se 1 (by rfl) ⟨620207, by rfl⟩ : syracuseStep 826943 = 1240415) B1240415
theorem B2793203 : Blo 550806 2793203 := bstep (se 1 (by rfl) ⟨2094902, by rfl⟩ : syracuseStep 2793203 = 4189805) B4189805
theorem B827207 : Blo 550806 827207 := bstep (se 1 (by rfl) ⟨620405, by rfl⟩ : syracuseStep 827207 = 1240811) B1240811
theorem B827291 : Blo 550806 827291 := bstep (se 1 (by rfl) ⟨620468, by rfl⟩ : syracuseStep 827291 = 1240937) B1240937
theorem B827855 : Blo 550806 827855 := bstep (se 1 (by rfl) ⟨620891, by rfl⟩ : syracuseStep 827855 = 1241783) B1241783
theorem B827897 : Blo 550806 827897 := bstep (se 2 (by rfl) ⟨310461, by rfl⟩ : syracuseStep 827897 = 620923) B620923
theorem B3547709 : Blo 550806 3547709 := bstep (se 3 (by rfl) ⟨665195, by rfl⟩ : syracuseStep 3547709 = 1330391) B1330391
theorem B827999 : Blo 550806 827999 := bstep (se 1 (by rfl) ⟨620999, by rfl⟩ : syracuseStep 827999 = 1241999) B1241999
theorem B697339 : Blo 550806 697339 := bstep (se 1 (by rfl) ⟨523004, by rfl⟩ : syracuseStep 697339 = 1046009) B1046009
theorem B664571 : Blo 550806 664571 := bstep (se 1 (by rfl) ⟨498428, by rfl⟩ : syracuseStep 664571 = 996857) B996857
theorem B828479 : Blo 550806 828479 := bstep (se 1 (by rfl) ⟨621359, by rfl⟩ : syracuseStep 828479 = 1242719) B1242719
theorem B828521 : Blo 550806 828521 := bstep (se 2 (by rfl) ⟨310695, by rfl⟩ : syracuseStep 828521 = 621391) B621391
theorem B828623 : Blo 550806 828623 := bstep (se 1 (by rfl) ⟨621467, by rfl⟩ : syracuseStep 828623 = 1242935) B1242935
theorem B828827 : Blo 550806 828827 := bstep (se 1 (by rfl) ⟨621620, by rfl⟩ : syracuseStep 828827 = 1243241) B1243241
theorem B5547565 : Blo 550806 5547565 := bstep (se 3 (by rfl) ⟨1040168, by rfl⟩ : syracuseStep 5547565 = 2080337) B2080337
theorem B829049 : Blo 550806 829049 := bstep (se 2 (by rfl) ⟨310893, by rfl⟩ : syracuseStep 829049 = 621787) B621787
theorem B1124059 : Blo 550806 1124059 := bstep (se 1 (by rfl) ⟨843044, by rfl⟩ : syracuseStep 1124059 = 1686089) B1686089
theorem B632539 : Blo 550806 632539 := bstep (se 1 (by rfl) ⟨474404, by rfl⟩ : syracuseStep 632539 = 948809) B948809
theorem B829151 : Blo 550806 829151 := bstep (se 1 (by rfl) ⟨621863, by rfl⟩ : syracuseStep 829151 = 1243727) B1243727
theorem B829247 : Blo 550806 829247 := bstep (se 1 (by rfl) ⟨621935, by rfl⟩ : syracuseStep 829247 = 1243871) B1243871
theorem B1681249 : Blo 550806 1681249 := bstep (se 2 (by rfl) ⟨630468, by rfl⟩ : syracuseStep 1681249 = 1260937) B1260937
theorem B4204385 : Blo 550806 4204385 := bstep (se 2 (by rfl) ⟨1576644, by rfl⟩ : syracuseStep 4204385 = 3153289) B3153289
theorem B993223 : Blo 550806 993223 := bstep (se 1 (by rfl) ⟨744917, by rfl⟩ : syracuseStep 993223 = 1489835) B1489835
theorem B698311 : Blo 550806 698311 := bstep (se 1 (by rfl) ⟨523733, by rfl⟩ : syracuseStep 698311 = 1047467) B1047467
theorem B829415 : Blo 550806 829415 := bstep (se 1 (by rfl) ⟨622061, by rfl⟩ : syracuseStep 829415 = 1244123) B1244123
theorem B829433 : Blo 550806 829433 := bstep (se 2 (by rfl) ⟨311037, by rfl⟩ : syracuseStep 829433 = 622075) B622075
theorem B829535 : Blo 550806 829535 := bstep (se 1 (by rfl) ⟨622151, by rfl⟩ : syracuseStep 829535 = 1244303) B1244303
theorem B829595 : Blo 550806 829595 := bstep (se 1 (by rfl) ⟨622196, by rfl⟩ : syracuseStep 829595 = 1244393) B1244393
theorem B829631 : Blo 550806 829631 := bstep (se 1 (by rfl) ⟨622223, by rfl⟩ : syracuseStep 829631 = 1244447) B1244447
theorem B829673 : Blo 550806 829673 := bstep (se 2 (by rfl) ⟨311127, by rfl⟩ : syracuseStep 829673 = 622255) B622255
theorem B57387325 : Blo 550806 57387325 := bstep (se 3 (by rfl) ⟨10760123, by rfl⟩ : syracuseStep 57387325 = 21520247) B21520247
theorem B829979 : Blo 550806 829979 := bstep (se 1 (by rfl) ⟨622484, by rfl⟩ : syracuseStep 829979 = 1244969) B1244969
theorem B830057 : Blo 550806 830057 := bstep (se 2 (by rfl) ⟨311271, by rfl⟩ : syracuseStep 830057 = 622543) B622543
theorem B2796281 : Blo 550806 2796281 := bstep (se 2 (by rfl) ⟨1048605, by rfl⟩ : syracuseStep 2796281 = 2097211) B2097211
theorem B3976121 : Blo 550806 3976121 := bstep (se 2 (by rfl) ⟨1491045, by rfl⟩ : syracuseStep 3976121 = 2982091) B2982091
theorem B830585 : Blo 550806 830585 := bstep (se 2 (by rfl) ⟨311469, by rfl⟩ : syracuseStep 830585 = 622939) B622939
theorem B830687 : Blo 550806 830687 := bstep (se 1 (by rfl) ⟨623015, by rfl⟩ : syracuseStep 830687 = 1246031) B1246031
theorem B830729 : Blo 550806 830729 := bstep (se 2 (by rfl) ⟨311523, by rfl⟩ : syracuseStep 830729 = 623047) B623047
theorem B830831 : Blo 550806 830831 := bstep (se 1 (by rfl) ⟨623123, by rfl⟩ : syracuseStep 830831 = 1246247) B1246247
theorem B830951 : Blo 550806 830951 := bstep (se 1 (by rfl) ⟨623213, by rfl⟩ : syracuseStep 830951 = 1246427) B1246427
theorem B994889 : Blo 550806 994889 := bstep (se 2 (by rfl) ⟨373083, by rfl⟩ : syracuseStep 994889 = 746167) B746167
theorem B5058121 : Blo 550806 5058121 := bstep (se 2 (by rfl) ⟨1896795, by rfl⟩ : syracuseStep 5058121 = 3793591) B3793591
theorem B831083 : Blo 550806 831083 := bstep (se 1 (by rfl) ⟨623312, by rfl⟩ : syracuseStep 831083 = 1246625) B1246625
theorem B21507763 : Blo 550806 21507763 := bstep (se 1 (by rfl) ⟨16130822, by rfl⟩ : syracuseStep 21507763 = 32261645) B32261645
theorem B831209 : Blo 550806 831209 := bstep (se 2 (by rfl) ⟨311703, by rfl⟩ : syracuseStep 831209 = 623407) B623407
theorem B6205177 : Blo 550806 6205177 := bstep (se 2 (by rfl) ⟨2326941, by rfl⟩ : syracuseStep 6205177 = 4653883) B4653883
theorem B798503 : Blo 550806 798503 := bstep (se 1 (by rfl) ⟨598877, by rfl⟩ : syracuseStep 798503 = 1197755) B1197755
theorem B929657 : Blo 550806 929657 := bstep (se 2 (by rfl) ⟨348621, by rfl⟩ : syracuseStep 929657 = 697243) B697243
theorem B831353 : Blo 550806 831353 := bstep (se 2 (by rfl) ⟨311757, by rfl⟩ : syracuseStep 831353 = 623515) B623515
theorem B831455 : Blo 550806 831455 := bstep (se 1 (by rfl) ⟨623591, by rfl⟩ : syracuseStep 831455 = 1247183) B1247183
theorem B831707 : Blo 550806 831707 := bstep (se 1 (by rfl) ⟨623780, by rfl⟩ : syracuseStep 831707 = 1247561) B1247561
theorem B831719 : Blo 550806 831719 := bstep (se 1 (by rfl) ⟨623789, by rfl⟩ : syracuseStep 831719 = 1247579) B1247579
theorem B831881 : Blo 550806 831881 := bstep (se 2 (by rfl) ⟨311955, by rfl⟩ : syracuseStep 831881 = 623911) B623911
theorem B8532377 : Blo 550806 8532377 := bstep (se 2 (by rfl) ⟨3199641, by rfl⟩ : syracuseStep 8532377 = 6399283) B6399283
theorem B831977 : Blo 550806 831977 := bstep (se 2 (by rfl) ⟨311991, by rfl⟩ : syracuseStep 831977 = 623983) B623983
theorem B832103 : Blo 550806 832103 := bstep (se 1 (by rfl) ⟨624077, by rfl⟩ : syracuseStep 832103 = 1248155) B1248155
theorem B9548441 : Blo 550806 9548441 := bstep (se 2 (by rfl) ⟨3580665, by rfl⟩ : syracuseStep 9548441 = 7161331) B7161331
theorem B930811 : Blo 550806 930811 := bstep (se 1 (by rfl) ⟨698108, by rfl⟩ : syracuseStep 930811 = 1396217) B1396217
theorem B931243 : Blo 550806 931243 := bstep (se 1 (by rfl) ⟨698432, by rfl⟩ : syracuseStep 931243 = 1396865) B1396865
theorem B931439 : Blo 550806 931439 := bstep (se 1 (by rfl) ⟨698579, by rfl⟩ : syracuseStep 931439 = 1397159) B1397159
theorem B931547 : Blo 550806 931547 := bstep (se 1 (by rfl) ⟨698660, by rfl⟩ : syracuseStep 931547 = 1397321) B1397321
theorem B931783 : Blo 550806 931783 := bstep (se 1 (by rfl) ⟨698837, by rfl⟩ : syracuseStep 931783 = 1397675) B1397675
theorem B997679 : Blo 550806 997679 := bstep (se 1 (by rfl) ⟨748259, by rfl⟩ : syracuseStep 997679 = 1496519) B1496519
theorem B2013817 : Blo 550806 2013817 := bstep (se 2 (by rfl) ⟨755181, by rfl⟩ : syracuseStep 2013817 = 1510363) B1510363
theorem B932539 : Blo 550806 932539 := bstep (se 1 (by rfl) ⟨699404, by rfl⟩ : syracuseStep 932539 = 1398809) B1398809
theorem B932843 : Blo 550806 932843 := bstep (se 1 (by rfl) ⟨699632, by rfl⟩ : syracuseStep 932843 = 1399265) B1399265
theorem B1326547 : Blo 550806 1326547 := bstep (se 1 (by rfl) ⟨994910, by rfl⟩ : syracuseStep 1326547 = 1989821) B1989821
theorem B6046271 : Blo 550806 6046271 := bstep (se 1 (by rfl) ⟨4534703, by rfl⟩ : syracuseStep 6046271 = 9069407) B9069407
theorem B2999197 : Blo 550806 2999197 := bstep (se 3 (by rfl) ⟨562349, by rfl⟩ : syracuseStep 2999197 = 1124699) B1124699
theorem B2802599 : Blo 550806 2802599 := bstep (se 1 (by rfl) ⟨2101949, by rfl⟩ : syracuseStep 2802599 = 4203899) B4203899
theorem B1197787 : Blo 550806 1197787 := bstep (se 1 (by rfl) ⟨898340, by rfl⟩ : syracuseStep 1197787 = 1796681) B1796681
theorem B935759 : Blo 550806 935759 := bstep (se 1 (by rfl) ⟨701819, by rfl⟩ : syracuseStep 935759 = 1403639) B1403639
theorem B414566423 : Blo 550806 414566423 := bstep (se 1 (by rfl) ⟨310924817, by rfl⟩ : syracuseStep 414566423 = 621849635) B621849635
theorem B4475213 : Blo 550806 4475213 := bstep (se 3 (by rfl) ⟨839102, by rfl⟩ : syracuseStep 4475213 = 1678205) B1678205
theorem B1395083 : Blo 550806 1395083 := bstep (se 1 (by rfl) ⟨1046312, by rfl⟩ : syracuseStep 1395083 = 2092625) B2092625
theorem B17713835 : Blo 550806 17713835 := bstep (se 1 (by rfl) ⟨13285376, by rfl⟩ : syracuseStep 17713835 = 26570753) B26570753
theorem B7949015 : Blo 550806 7949015 := bstep (se 1 (by rfl) ⟨5961761, by rfl⟩ : syracuseStep 7949015 = 11923523) B11923523
theorem B707563 : Blo 550806 707563 := bstep (se 1 (by rfl) ⟨530672, by rfl⟩ : syracuseStep 707563 = 1061345) B1061345
theorem B5033123 : Blo 550806 5033123 := bstep (se 1 (by rfl) ⟨3774842, by rfl⟩ : syracuseStep 5033123 = 7549685) B7549685
theorem B3788005 : Blo 550806 3788005 := bstep (se 4 (by rfl) ⟨355125, by rfl⟩ : syracuseStep 3788005 = 710251) B710251
theorem B7982459 : Blo 550806 7982459 := bstep (se 1 (by rfl) ⟨5986844, by rfl⟩ : syracuseStep 7982459 = 11973689) B11973689
theorem B5328251 : Blo 550806 5328251 := bstep (se 1 (by rfl) ⟨3996188, by rfl⟩ : syracuseStep 5328251 = 7992377) B7992377
theorem B7753097 : Blo 550806 7753097 := bstep (se 2 (by rfl) ⟨2907411, by rfl⟩ : syracuseStep 7753097 = 5814823) B5814823
theorem B2837929 : Blo 550806 2837929 := bstep (se 2 (by rfl) ⟨1064223, by rfl⟩ : syracuseStep 2837929 = 2128447) B2128447
theorem B30690893 : Blo 550806 30690893 := bstep (se 3 (by rfl) ⟨5754542, by rfl⟩ : syracuseStep 30690893 = 11509085) B11509085
theorem B1396399 : Blo 550806 1396399 := bstep (se 1 (by rfl) ⟨1047299, by rfl⟩ : syracuseStep 1396399 = 2094599) B2094599
theorem B1396703 : Blo 550806 1396703 := bstep (se 1 (by rfl) ⟨1047527, by rfl⟩ : syracuseStep 1396703 = 2095055) B2095055
theorem B1396723 : Blo 550806 1396723 := bstep (se 1 (by rfl) ⟨1047542, by rfl⟩ : syracuseStep 1396723 = 2095085) B2095085
theorem B1397047 : Blo 550806 1397047 := bstep (se 1 (by rfl) ⟨1047785, by rfl⟩ : syracuseStep 1397047 = 2095571) B2095571
theorem B1921619 : Blo 550806 1921619 := bstep (se 1 (by rfl) ⟨1441214, by rfl⟩ : syracuseStep 1921619 = 2882429) B2882429
theorem B1331795 : Blo 550806 1331795 := bstep (se 1 (by rfl) ⟨998846, by rfl⟩ : syracuseStep 1331795 = 1997693) B1997693
theorem B1397351 : Blo 550806 1397351 := bstep (se 1 (by rfl) ⟨1048013, by rfl⟩ : syracuseStep 1397351 = 2096027) B2096027
theorem B12899017 : Blo 550806 12899017 := bstep (se 2 (by rfl) ⟨4837131, by rfl⟩ : syracuseStep 12899017 = 9674263) B9674263
theorem B7591009 : Blo 550806 7591009 := bstep (se 2 (by rfl) ⟨2846628, by rfl⟩ : syracuseStep 7591009 = 5693257) B5693257
theorem B3364051 : Blo 550806 3364051 := bstep (se 1 (by rfl) ⟨2523038, by rfl⟩ : syracuseStep 3364051 = 5046077) B5046077
theorem B1398343 : Blo 550806 1398343 := bstep (se 1 (by rfl) ⟨1048757, by rfl⟩ : syracuseStep 1398343 = 2097515) B2097515
theorem B1398455 : Blo 550806 1398455 := bstep (se 1 (by rfl) ⟨1048841, by rfl⟩ : syracuseStep 1398455 = 2097683) B2097683
theorem B294508331 : Blo 550806 294508331 := bstep (se 1 (by rfl) ⟨220881248, by rfl⟩ : syracuseStep 294508331 = 441762497) B441762497
theorem B2807783 : Blo 550806 2807783 := bstep (se 1 (by rfl) ⟨2105837, by rfl⟩ : syracuseStep 2807783 = 4211675) B4211675
theorem B3824047 : Blo 550806 3824047 := bstep (se 1 (by rfl) ⟨2868035, by rfl⟩ : syracuseStep 3824047 = 5736071) B5736071
theorem B1497533 : Blo 550806 1497533 := bstep (se 3 (by rfl) ⟨280787, by rfl⟩ : syracuseStep 1497533 = 561575) B561575
theorem B49109579 : Blo 550806 49109579 := bstep (se 1 (by rfl) ⟨36832184, by rfl⟩ : syracuseStep 49109579 = 73664369) B73664369
theorem B7986377 : Blo 550806 7986377 := bstep (se 2 (by rfl) ⟨2994891, by rfl⟩ : syracuseStep 7986377 = 5989783) B5989783
theorem B1400399 : Blo 550806 1400399 := bstep (se 1 (by rfl) ⟨1050299, by rfl⟩ : syracuseStep 1400399 = 2100599) B2100599
theorem B1892087 : Blo 550806 1892087 := bstep (se 1 (by rfl) ⟨1419065, by rfl⟩ : syracuseStep 1892087 = 2838131) B2838131
theorem B20209985 : Blo 550806 20209985 := bstep (se 2 (by rfl) ⟨7578744, by rfl⟩ : syracuseStep 20209985 = 15157489) B15157489
theorem B1794487 : Blo 550806 1794487 := bstep (se 1 (by rfl) ⟨1345865, by rfl⟩ : syracuseStep 1794487 = 2691731) B2691731
theorem B10084925 : Blo 550806 10084925 := bstep (se 3 (by rfl) ⟨1890923, by rfl⟩ : syracuseStep 10084925 = 3781847) B3781847
theorem B15098501 : Blo 550806 15098501 := bstep (se 4 (by rfl) ⟨1415484, by rfl⟩ : syracuseStep 15098501 = 2830969) B2830969
theorem B1893401 : Blo 550806 1893401 := bstep (se 2 (by rfl) ⟨710025, by rfl⟩ : syracuseStep 1893401 = 1420051) B1420051
theorem B1860731 : Blo 550806 1860731 := bstep (se 1 (by rfl) ⟨1395548, by rfl⟩ : syracuseStep 1860731 = 2791097) B2791097
theorem B1861001 : Blo 550806 1861001 := bstep (se 2 (by rfl) ⟨697875, by rfl⟩ : syracuseStep 1861001 = 1395751) B1395751
theorem B2024875 : Blo 550806 2024875 := bstep (se 1 (by rfl) ⟨1518656, by rfl⟩ : syracuseStep 2024875 = 3037313) B3037313
theorem B2647673 : Blo 550806 2647673 := bstep (se 2 (by rfl) ⟨992877, by rfl⟩ : syracuseStep 2647673 = 1985755) B1985755
theorem B5301881 : Blo 550806 5301881 := bstep (se 2 (by rfl) ⟨1988205, by rfl⟩ : syracuseStep 5301881 = 3976411) B3976411
theorem B1402535 : Blo 550806 1402535 := bstep (se 1 (by rfl) ⟨1051901, by rfl⟩ : syracuseStep 1402535 = 2103803) B2103803
theorem B550895 : Blo 550806 550895 := bstep (se 1 (by rfl) ⟨413171, by rfl⟩ : syracuseStep 550895 = 826343) B826343
theorem B2648173 : Blo 550806 2648173 := bstep (se 3 (by rfl) ⟨496532, by rfl⟩ : syracuseStep 2648173 = 993065) B993065
theorem B1861757 : Blo 550806 1861757 := bstep (se 3 (by rfl) ⟨349079, by rfl⟩ : syracuseStep 1861757 = 698159) B698159
theorem B551067 : Blo 550806 551067 := bstep (se 1 (by rfl) ⟨413300, by rfl⟩ : syracuseStep 551067 = 826601) B826601
theorem B551103 : Blo 550806 551103 := bstep (se 1 (by rfl) ⟨413327, by rfl⟩ : syracuseStep 551103 = 826655) B826655
theorem B1239335 : Blo 550806 1239335 := bstep (se 1 (by rfl) ⟨929501, by rfl⟩ : syracuseStep 1239335 = 1859003) B1859003
theorem B551215 : Blo 550806 551215 := bstep (se 1 (by rfl) ⟨413411, by rfl⟩ : syracuseStep 551215 = 826823) B826823
theorem B1993007 : Blo 550806 1993007 := bstep (se 1 (by rfl) ⟨1494755, by rfl⟩ : syracuseStep 1993007 = 2989511) B2989511
theorem B1403183 : Blo 550806 1403183 := bstep (se 1 (by rfl) ⟨1052387, by rfl⟩ : syracuseStep 1403183 = 2104775) B2104775
theorem B1239353 : Blo 550806 1239353 := bstep (se 2 (by rfl) ⟨464757, by rfl⟩ : syracuseStep 1239353 = 929515) B929515
theorem B1862027 : Blo 550806 1862027 := bstep (se 1 (by rfl) ⟨1396520, by rfl⟩ : syracuseStep 1862027 = 2793041) B2793041
theorem B26896819 : Blo 550806 26896819 := bstep (se 1 (by rfl) ⟨20172614, by rfl⟩ : syracuseStep 26896819 = 40345229) B40345229
theorem B2353691 : Blo 550806 2353691 := bstep (se 1 (by rfl) ⟨1765268, by rfl⟩ : syracuseStep 2353691 = 3530537) B3530537
theorem B551451 : Blo 550806 551451 := bstep (se 1 (by rfl) ⟨413588, by rfl⟩ : syracuseStep 551451 = 827177) B827177
theorem B551455 : Blo 550806 551455 := bstep (se 1 (by rfl) ⟨413591, by rfl⟩ : syracuseStep 551455 = 827183) B827183
theorem B3140167 : Blo 550806 3140167 := bstep (se 1 (by rfl) ⟨2355125, by rfl⟩ : syracuseStep 3140167 = 4710251) B4710251
theorem B3992267 : Blo 550806 3992267 := bstep (se 1 (by rfl) ⟨2994200, by rfl⟩ : syracuseStep 3992267 = 5988401) B5988401
theorem B5040899 : Blo 550806 5040899 := bstep (se 1 (by rfl) ⟨3780674, by rfl⟩ : syracuseStep 5040899 = 7561349) B7561349
theorem B2026295 : Blo 550806 2026295 := bstep (se 1 (by rfl) ⟨1519721, by rfl⟩ : syracuseStep 2026295 = 3039443) B3039443
theorem B551771 : Blo 550806 551771 := bstep (se 1 (by rfl) ⟨413828, by rfl⟩ : syracuseStep 551771 = 827657) B827657
theorem B551839 : Blo 550806 551839 := bstep (se 1 (by rfl) ⟨413879, by rfl⟩ : syracuseStep 551839 = 827759) B827759
theorem B2649095 : Blo 550806 2649095 := bstep (se 1 (by rfl) ⟨1986821, by rfl⟩ : syracuseStep 2649095 = 3973643) B3973643
theorem B551983 : Blo 550806 551983 := bstep (se 1 (by rfl) ⟨413987, by rfl⟩ : syracuseStep 551983 = 827975) B827975
theorem B552007 : Blo 550806 552007 := bstep (se 1 (by rfl) ⟨414005, by rfl⟩ : syracuseStep 552007 = 828011) B828011
theorem B552159 : Blo 550806 552159 := bstep (se 1 (by rfl) ⟨414119, by rfl⟩ : syracuseStep 552159 = 828239) B828239
theorem B4484429 : Blo 550806 4484429 := bstep (se 3 (by rfl) ⟨840830, by rfl⟩ : syracuseStep 4484429 = 1681661) B1681661
theorem B13495697 : Blo 550806 13495697 := bstep (se 2 (by rfl) ⟨5060886, by rfl⟩ : syracuseStep 13495697 = 10121773) B10121773
theorem B552423 : Blo 550806 552423 := bstep (se 1 (by rfl) ⟨414317, by rfl⟩ : syracuseStep 552423 = 828635) B828635
theorem B1240649 : Blo 550806 1240649 := bstep (se 2 (by rfl) ⟨465243, by rfl⟩ : syracuseStep 1240649 = 930487) B930487
theorem B552539 : Blo 550806 552539 := bstep (se 1 (by rfl) ⟨414404, by rfl⟩ : syracuseStep 552539 = 828809) B828809
theorem B552775 : Blo 550806 552775 := bstep (se 1 (by rfl) ⟨414581, by rfl⟩ : syracuseStep 552775 = 829163) B829163
theorem B4255595 : Blo 550806 4255595 := bstep (se 1 (by rfl) ⟨3191696, by rfl⟩ : syracuseStep 4255595 = 6383393) B6383393
theorem B2944907 : Blo 550806 2944907 := bstep (se 1 (by rfl) ⟨2208680, by rfl⟩ : syracuseStep 2944907 = 4417361) B4417361
theorem B1994635 : Blo 550806 1994635 := bstep (se 1 (by rfl) ⟨1495976, by rfl⟩ : syracuseStep 1994635 = 2991953) B2991953
theorem B1896331 : Blo 550806 1896331 := bstep (se 1 (by rfl) ⟨1422248, by rfl⟩ : syracuseStep 1896331 = 2844497) B2844497
theorem B1273823 : Blo 550806 1273823 := bstep (se 1 (by rfl) ⟨955367, by rfl⟩ : syracuseStep 1273823 = 1910735) B1910735
theorem B1863647 : Blo 550806 1863647 := bstep (se 1 (by rfl) ⟨1397735, by rfl⟩ : syracuseStep 1863647 = 2795471) B2795471
theorem B552927 : Blo 550806 552927 := bstep (se 1 (by rfl) ⟨414695, by rfl⟩ : syracuseStep 552927 = 829391) B829391
theorem B1863809 : Blo 550806 1863809 := bstep (se 2 (by rfl) ⟨698928, by rfl⟩ : syracuseStep 1863809 = 1397857) B1397857
theorem B553191 : Blo 550806 553191 := bstep (se 1 (by rfl) ⟨414893, by rfl⟩ : syracuseStep 553191 = 829787) B829787
theorem B553343 : Blo 550806 553343 := bstep (se 1 (by rfl) ⟨415007, by rfl⟩ : syracuseStep 553343 = 830015) B830015
theorem B553423 : Blo 550806 553423 := bstep (se 1 (by rfl) ⟨415067, by rfl⟩ : syracuseStep 553423 = 830135) B830135
theorem B1864295 : Blo 550806 1864295 := bstep (se 1 (by rfl) ⟨1398221, by rfl⟩ : syracuseStep 1864295 = 2796443) B2796443
theorem B553575 : Blo 550806 553575 := bstep (se 1 (by rfl) ⟨415181, by rfl⟩ : syracuseStep 553575 = 830363) B830363
theorem B1569527 : Blo 550806 1569527 := bstep (se 1 (by rfl) ⟨1177145, by rfl⟩ : syracuseStep 1569527 = 2354291) B2354291
theorem B553839 : Blo 550806 553839 := bstep (se 1 (by rfl) ⟨415379, by rfl⟩ : syracuseStep 553839 = 830759) B830759
theorem B553895 : Blo 550806 553895 := bstep (se 1 (by rfl) ⟨415421, by rfl⟩ : syracuseStep 553895 = 830843) B830843
theorem B1864619 : Blo 550806 1864619 := bstep (se 1 (by rfl) ⟨1398464, by rfl⟩ : syracuseStep 1864619 = 2796929) B2796929
theorem B1242107 : Blo 550806 1242107 := bstep (se 1 (by rfl) ⟨931580, by rfl⟩ : syracuseStep 1242107 = 1863161) B1863161
theorem B553979 : Blo 550806 553979 := bstep (se 1 (by rfl) ⟨415484, by rfl⟩ : syracuseStep 553979 = 830969) B830969
theorem B554047 : Blo 550806 554047 := bstep (se 1 (by rfl) ⟨415535, by rfl⟩ : syracuseStep 554047 = 831071) B831071
theorem B1242287 : Blo 550806 1242287 := bstep (se 1 (by rfl) ⟨931715, by rfl⟩ : syracuseStep 1242287 = 1863431) B1863431
theorem B554191 : Blo 550806 554191 := bstep (se 1 (by rfl) ⟨415643, by rfl⟩ : syracuseStep 554191 = 831287) B831287
theorem B1242323 : Blo 550806 1242323 := bstep (se 1 (by rfl) ⟨931742, by rfl⟩ : syracuseStep 1242323 = 1863485) B1863485
theorem B1865051 : Blo 550806 1865051 := bstep (se 1 (by rfl) ⟨1398788, by rfl⟩ : syracuseStep 1865051 = 2797577) B2797577
theorem B554395 : Blo 550806 554395 := bstep (se 1 (by rfl) ⟨415796, by rfl⟩ : syracuseStep 554395 = 831593) B831593
theorem B1865159 : Blo 550806 1865159 := bstep (se 1 (by rfl) ⟨1398869, by rfl⟩ : syracuseStep 1865159 = 2797739) B2797739
theorem B1242593 : Blo 550806 1242593 := bstep (se 2 (by rfl) ⟨465972, by rfl⟩ : syracuseStep 1242593 = 931945) B931945
theorem B554607 : Blo 550806 554607 := bstep (se 1 (by rfl) ⟨415955, by rfl⟩ : syracuseStep 554607 = 831911) B831911
theorem B554663 : Blo 550806 554663 := bstep (se 1 (by rfl) ⟨415997, by rfl⟩ : syracuseStep 554663 = 831995) B831995
theorem B3536585 : Blo 550806 3536585 := bstep (se 2 (by rfl) ⟨1326219, by rfl⟩ : syracuseStep 3536585 = 2652439) B2652439
theorem B1046267 : Blo 550806 1046267 := bstep (se 1 (by rfl) ⟨784700, by rfl⟩ : syracuseStep 1046267 = 1569401) B1569401
theorem B5306107 : Blo 550806 5306107 := bstep (se 1 (by rfl) ⟨3979580, by rfl⟩ : syracuseStep 5306107 = 7959161) B7959161
theorem B7960315 : Blo 550806 7960315 := bstep (se 1 (by rfl) ⟨5970236, by rfl⟩ : syracuseStep 7960315 = 11940473) B11940473
theorem B554747 : Blo 550806 554747 := bstep (se 1 (by rfl) ⟨416060, by rfl⟩ : syracuseStep 554747 = 832121) B832121
theorem B1865483 : Blo 550806 1865483 := bstep (se 1 (by rfl) ⟨1399112, by rfl⟩ : syracuseStep 1865483 = 2798225) B2798225
theorem B6715153 : Blo 550806 6715153 := bstep (se 2 (by rfl) ⟨2518182, by rfl⟩ : syracuseStep 6715153 = 5036365) B5036365
theorem B554783 : Blo 550806 554783 := bstep (se 1 (by rfl) ⟨416087, by rfl⟩ : syracuseStep 554783 = 832175) B832175
theorem B2357039 : Blo 550806 2357039 := bstep (se 1 (by rfl) ⟨1767779, by rfl⟩ : syracuseStep 2357039 = 3535559) B3535559
theorem B620527 : Blo 550806 620527 := bstep (se 1 (by rfl) ⟨465395, by rfl⟩ : syracuseStep 620527 = 930791) B930791
theorem B1865753 : Blo 550806 1865753 := bstep (se 2 (by rfl) ⟨699657, by rfl⟩ : syracuseStep 1865753 = 1399315) B1399315
theorem B1177897 : Blo 550806 1177897 := bstep (se 2 (by rfl) ⟨441711, by rfl⟩ : syracuseStep 1177897 = 883423) B883423
theorem B14318153 : Blo 550806 14318153 := bstep (se 2 (by rfl) ⟨5369307, by rfl⟩ : syracuseStep 14318153 = 10738615) B10738615
theorem B1244231 : Blo 550806 1244231 := bstep (se 1 (by rfl) ⟨933173, by rfl⟩ : syracuseStep 1244231 = 1866347) B1866347
theorem B1867103 : Blo 550806 1867103 := bstep (se 1 (by rfl) ⟨1400327, by rfl⟩ : syracuseStep 1867103 = 2800655) B2800655
theorem B2653651 : Blo 550806 2653651 := bstep (se 1 (by rfl) ⟨1990238, by rfl⟩ : syracuseStep 2653651 = 3980477) B3980477
theorem B1244627 : Blo 550806 1244627 := bstep (se 1 (by rfl) ⟨933470, by rfl⟩ : syracuseStep 1244627 = 1866941) B1866941
theorem B1572443 : Blo 550806 1572443 := bstep (se 1 (by rfl) ⟨1179332, by rfl⟩ : syracuseStep 1572443 = 2358665) B2358665
theorem B5963489 : Blo 550806 5963489 := bstep (se 2 (by rfl) ⟨2236308, by rfl⟩ : syracuseStep 5963489 = 4472617) B4472617
theorem B1244897 : Blo 550806 1244897 := bstep (se 2 (by rfl) ⟨466836, by rfl⟩ : syracuseStep 1244897 = 933673) B933673
theorem B1867643 : Blo 550806 1867643 := bstep (se 1 (by rfl) ⟨1400732, by rfl⟩ : syracuseStep 1867643 = 2801465) B2801465
theorem B1245419 : Blo 550806 1245419 := bstep (se 1 (by rfl) ⟨934064, by rfl⟩ : syracuseStep 1245419 = 1868129) B1868129
theorem B1048879 : Blo 550806 1048879 := bstep (se 1 (by rfl) ⟨786659, by rfl⟩ : syracuseStep 1048879 = 1573319) B1573319
theorem B4030847 : Blo 550806 4030847 := bstep (se 1 (by rfl) ⟨3023135, by rfl⟩ : syracuseStep 4030847 = 6046271) B6046271
theorem B5046731 : Blo 550806 5046731 := bstep (se 1 (by rfl) ⟨3785048, by rfl⟩ : syracuseStep 5046731 = 7570097) B7570097
theorem B2392649 : Blo 550806 2392649 := bstep (se 2 (by rfl) ⟨897243, by rfl⟩ : syracuseStep 2392649 = 1794487) B1794487
theorem B1049183 : Blo 550806 1049183 := bstep (se 1 (by rfl) ⟨786887, by rfl⟩ : syracuseStep 1049183 = 1573775) B1573775
theorem B1868399 : Blo 550806 1868399 := bstep (se 1 (by rfl) ⟨1401299, by rfl⟩ : syracuseStep 1868399 = 2802599) B2802599
theorem B1246319 : Blo 550806 1246319 := bstep (se 1 (by rfl) ⟨934739, by rfl⟩ : syracuseStep 1246319 = 1869479) B1869479
theorem B591071 : Blo 550806 591071 := bstep (se 1 (by rfl) ⟨443303, by rfl⟩ : syracuseStep 591071 = 886607) B886607
theorem B623839 : Blo 550806 623839 := bstep (se 1 (by rfl) ⟨467879, by rfl⟩ : syracuseStep 623839 = 935759) B935759
theorem B6292727 : Blo 550806 6292727 := bstep (se 1 (by rfl) ⟨4719545, by rfl⟩ : syracuseStep 6292727 = 9439091) B9439091
theorem B2098457 : Blo 550806 2098457 := bstep (se 2 (by rfl) ⟨786921, by rfl⟩ : syracuseStep 2098457 = 1573843) B1573843
theorem B1049935 : Blo 550806 1049935 := bstep (se 1 (by rfl) ⟨787451, by rfl⟩ : syracuseStep 1049935 = 1574903) B1574903
theorem B1246715 : Blo 550806 1246715 := bstep (se 1 (by rfl) ⟨935036, by rfl⟩ : syracuseStep 1246715 = 1870073) B1870073
theorem B5113367 : Blo 550806 5113367 := bstep (se 1 (by rfl) ⟨3835025, by rfl⟩ : syracuseStep 5113367 = 7670051) B7670051
theorem B1246751 : Blo 550806 1246751 := bstep (se 1 (by rfl) ⟨935063, by rfl⟩ : syracuseStep 1246751 = 1870127) B1870127
theorem B2983475 : Blo 550806 2983475 := bstep (se 1 (by rfl) ⟨2237606, by rfl⟩ : syracuseStep 2983475 = 4475213) B4475213
theorem B1246895 : Blo 550806 1246895 := bstep (se 1 (by rfl) ⟨935171, by rfl⟩ : syracuseStep 1246895 = 1870343) B1870343
theorem B1247327 : Blo 550806 1247327 := bstep (se 1 (by rfl) ⟨935495, by rfl⟩ : syracuseStep 1247327 = 1870991) B1870991
theorem B1050907 : Blo 550806 1050907 := bstep (se 1 (by rfl) ⟨788180, by rfl⟩ : syracuseStep 1050907 = 1576361) B1576361
theorem B1247615 : Blo 550806 1247615 := bstep (se 1 (by rfl) ⟨935711, by rfl⟩ : syracuseStep 1247615 = 1871423) B1871423
theorem B1772189 : Blo 550806 1772189 := bstep (se 3 (by rfl) ⟨332285, by rfl⟩ : syracuseStep 1772189 = 664571) B664571
theorem B1248083 : Blo 550806 1248083 := bstep (se 1 (by rfl) ⟨936062, by rfl⟩ : syracuseStep 1248083 = 1872125) B1872125
theorem B2100127 : Blo 550806 2100127 := bstep (se 1 (by rfl) ⟨1575095, by rfl⟩ : syracuseStep 2100127 = 3150191) B3150191
theorem B1182689 : Blo 550806 1182689 := bstep (se 2 (by rfl) ⟨443508, by rfl⟩ : syracuseStep 1182689 = 887017) B887017
theorem B1051643 : Blo 550806 1051643 := bstep (se 1 (by rfl) ⟨788732, by rfl⟩ : syracuseStep 1051643 = 1577465) B1577465
theorem B1182775 : Blo 550806 1182775 := bstep (se 1 (by rfl) ⟨887081, by rfl⟩ : syracuseStep 1182775 = 1774163) B1774163
theorem B1281079 : Blo 550806 1281079 := bstep (se 1 (by rfl) ⟨960809, by rfl⟩ : syracuseStep 1281079 = 1921619) B1921619
theorem B887863 : Blo 550806 887863 := bstep (se 1 (by rfl) ⟨665897, by rfl⟩ : syracuseStep 887863 = 1331795) B1331795
theorem B76516433 : Blo 550806 76516433 := bstep (se 2 (by rfl) ⟨28693662, by rfl⟩ : syracuseStep 76516433 = 57387325) B57387325
theorem B1576417 : Blo 550806 1576417 := bstep (se 2 (by rfl) ⟨591156, by rfl⟩ : syracuseStep 1576417 = 1182313) B1182313
theorem B1052129 : Blo 550806 1052129 := bstep (se 2 (by rfl) ⟨394548, by rfl⟩ : syracuseStep 1052129 = 789097) B789097
theorem B9572039 : Blo 550806 9572039 := bstep (se 1 (by rfl) ⟨7179029, by rfl⟩ : syracuseStep 9572039 = 14358059) B14358059
theorem B1576691 : Blo 550806 1576691 := bstep (se 1 (by rfl) ⟨1182518, by rfl⟩ : syracuseStep 1576691 = 2365037) B2365037
theorem B1871855 : Blo 550806 1871855 := bstep (se 1 (by rfl) ⟨1403891, by rfl⟩ : syracuseStep 1871855 = 2807783) B2807783
theorem B1052767 : Blo 550806 1052767 := bstep (se 1 (by rfl) ⟨789575, by rfl⟩ : syracuseStep 1052767 = 1579151) B1579151
theorem B5050673 : Blo 550806 5050673 := bstep (se 2 (by rfl) ⟨1894002, by rfl⟩ : syracuseStep 5050673 = 3788005) B3788005
theorem B2101571 : Blo 550806 2101571 := bstep (se 1 (by rfl) ⟨1576178, by rfl⟩ : syracuseStep 2101571 = 3152357) B3152357
theorem B32739719 : Blo 550806 32739719 := bstep (se 1 (by rfl) ⟨24554789, by rfl⟩ : syracuseStep 32739719 = 49109579) B49109579
theorem B7082599 : Blo 550806 7082599 := bstep (se 1 (by rfl) ⟨5311949, by rfl⟩ : syracuseStep 7082599 = 10623899) B10623899
theorem B15995717 : Blo 550806 15995717 := bstep (se 4 (by rfl) ⟨1499598, by rfl⟩ : syracuseStep 15995717 = 2999197) B2999197
theorem B28677017 : Blo 550806 28677017 := bstep (se 2 (by rfl) ⟨10753881, by rfl⟩ : syracuseStep 28677017 = 21507763) B21507763
theorem B2659513 : Blo 550806 2659513 := bstep (se 2 (by rfl) ⟨997317, by rfl⟩ : syracuseStep 2659513 = 1994635) B1994635
theorem B2528441 : Blo 550806 2528441 := bstep (se 2 (by rfl) ⟨948165, by rfl⟩ : syracuseStep 2528441 = 1896331) B1896331
theorem B13473323 : Blo 550806 13473323 := bstep (se 1 (by rfl) ⟨10104992, by rfl⟩ : syracuseStep 13473323 = 20209985) B20209985
theorem B6723283 : Blo 550806 6723283 := bstep (se 1 (by rfl) ⟨5042462, by rfl⟩ : syracuseStep 6723283 = 10084925) B10084925
theorem B2365139 : Blo 550806 2365139 := bstep (se 1 (by rfl) ⟨1773854, by rfl⟩ : syracuseStep 2365139 = 3547709) B3547709
theorem B10065667 : Blo 550806 10065667 := bstep (se 1 (by rfl) ⟨7549250, by rfl⟩ : syracuseStep 10065667 = 15098501) B15098501
theorem B826223 : Blo 550806 826223 := bstep (se 1 (by rfl) ⟨619667, by rfl⟩ : syracuseStep 826223 = 1239335) B1239335
theorem B826235 : Blo 550806 826235 := bstep (se 1 (by rfl) ⟨619676, by rfl⟩ : syracuseStep 826235 = 1239353) B1239353
theorem B2661511 : Blo 550806 2661511 := bstep (se 1 (by rfl) ⟨1996133, by rfl⟩ : syracuseStep 2661511 = 3992267) B3992267
theorem B1350863 : Blo 550806 1350863 := bstep (se 1 (by rfl) ⟨1013147, by rfl⟩ : syracuseStep 1350863 = 2026295) B2026295
theorem B2366729 : Blo 550806 2366729 := bstep (se 2 (by rfl) ⟨887523, by rfl⟩ : syracuseStep 2366729 = 1775047) B1775047
theorem B2989619 : Blo 550806 2989619 := bstep (se 1 (by rfl) ⟨2242214, by rfl⟩ : syracuseStep 2989619 = 4484429) B4484429
theorem B8953537 : Blo 550806 8953537 := bstep (se 2 (by rfl) ⟨3357576, by rfl⟩ : syracuseStep 8953537 = 6715153) B6715153
theorem B827099 : Blo 550806 827099 := bstep (se 1 (by rfl) ⟨620324, by rfl⟩ : syracuseStep 827099 = 1240649) B1240649
theorem B4202441 : Blo 550806 4202441 := bstep (se 2 (by rfl) ⟨1575915, by rfl⟩ : syracuseStep 4202441 = 3151831) B3151831
theorem B827369 : Blo 550806 827369 := bstep (se 2 (by rfl) ⟨310263, by rfl⟩ : syracuseStep 827369 = 620527) B620527
theorem B2105473 : Blo 550806 2105473 := bstep (se 2 (by rfl) ⟨789552, by rfl⟩ : syracuseStep 2105473 = 1579105) B1579105
theorem B6365627 : Blo 550806 6365627 := bstep (se 1 (by rfl) ⟨4774220, by rfl⟩ : syracuseStep 6365627 = 9548441) B9548441
theorem B828071 : Blo 550806 828071 := bstep (se 1 (by rfl) ⟨621053, by rfl⟩ : syracuseStep 828071 = 1242107) B1242107
theorem B828191 : Blo 550806 828191 := bstep (se 1 (by rfl) ⟨621143, by rfl⟩ : syracuseStep 828191 = 1242287) B1242287
theorem B828215 : Blo 550806 828215 := bstep (se 1 (by rfl) ⟨621161, by rfl⟩ : syracuseStep 828215 = 1242323) B1242323
theorem B828395 : Blo 550806 828395 := bstep (se 1 (by rfl) ⟨621296, by rfl⟩ : syracuseStep 828395 = 1242593) B1242593
theorem B697511 : Blo 550806 697511 := bstep (se 1 (by rfl) ⟨523133, by rfl⟩ : syracuseStep 697511 = 1046267) B1046267
theorem B3155273 : Blo 550806 3155273 := bstep (se 2 (by rfl) ⟨1183227, by rfl⟩ : syracuseStep 3155273 = 2366455) B2366455
theorem B665119 : Blo 550806 665119 := bstep (se 1 (by rfl) ⟨498839, by rfl⟩ : syracuseStep 665119 = 997679) B997679
theorem B9545435 : Blo 550806 9545435 := bstep (se 1 (by rfl) ⟨7159076, by rfl⟩ : syracuseStep 9545435 = 14318153) B14318153
theorem B3417985 : Blo 550806 3417985 := bstep (se 2 (by rfl) ⟨1281744, by rfl⟩ : syracuseStep 3417985 = 2563489) B2563489
theorem B829487 : Blo 550806 829487 := bstep (se 1 (by rfl) ⟨622115, by rfl⟩ : syracuseStep 829487 = 1244231) B1244231
theorem B829751 : Blo 550806 829751 := bstep (se 1 (by rfl) ⟨622313, by rfl⟩ : syracuseStep 829751 = 1244627) B1244627
theorem B3975659 : Blo 550806 3975659 := bstep (se 1 (by rfl) ⟨2981744, by rfl⟩ : syracuseStep 3975659 = 5963489) B5963489
theorem B829931 : Blo 550806 829931 := bstep (se 1 (by rfl) ⟨622448, by rfl⟩ : syracuseStep 829931 = 1244897) B1244897
theorem B830633 : Blo 550806 830633 := bstep (se 2 (by rfl) ⟨311487, by rfl⟩ : syracuseStep 830633 = 622975) B622975
theorem B831047 : Blo 550806 831047 := bstep (se 1 (by rfl) ⟨623285, by rfl⟩ : syracuseStep 831047 = 1246571) B1246571
theorem B831227 : Blo 550806 831227 := bstep (se 1 (by rfl) ⟨623420, by rfl⟩ : syracuseStep 831227 = 1246841) B1246841
theorem B929785 : Blo 550806 929785 := bstep (se 2 (by rfl) ⟨348669, by rfl⟩ : syracuseStep 929785 = 697339) B697339
theorem B276377615 : Blo 550806 276377615 := bstep (se 1 (by rfl) ⟨207283211, by rfl⟩ : syracuseStep 276377615 = 414566423) B414566423
theorem B930055 : Blo 550806 930055 := bstep (se 1 (by rfl) ⟨697541, by rfl⟩ : syracuseStep 930055 = 1395083) B1395083
theorem B831899 : Blo 550806 831899 := bstep (se 1 (by rfl) ⟨623924, by rfl⟩ : syracuseStep 831899 = 1247849) B1247849
theorem B11809223 : Blo 550806 11809223 := bstep (se 1 (by rfl) ⟨8856917, by rfl⟩ : syracuseStep 11809223 = 17713835) B17713835
theorem B2699833 : Blo 550806 2699833 := bstep (se 2 (by rfl) ⟨1012437, by rfl⟩ : syracuseStep 2699833 = 2024875) B2024875
theorem B3355415 : Blo 550806 3355415 := bstep (se 1 (by rfl) ⟨2516561, by rfl⟩ : syracuseStep 3355415 = 5033123) B5033123
theorem B5321639 : Blo 550806 5321639 := bstep (se 1 (by rfl) ⟨3991229, by rfl⟩ : syracuseStep 5321639 = 7982459) B7982459
theorem B3552167 : Blo 550806 3552167 := bstep (se 1 (by rfl) ⟨2664125, by rfl⟩ : syracuseStep 3552167 = 5328251) B5328251
theorem B20460595 : Blo 550806 20460595 := bstep (se 1 (by rfl) ⟨15345446, by rfl⟩ : syracuseStep 20460595 = 30690893) B30690893
theorem B2241665 : Blo 550806 2241665 := bstep (se 2 (by rfl) ⟨840624, by rfl⟩ : syracuseStep 2241665 = 1681249) B1681249
theorem B898231 : Blo 550806 898231 := bstep (se 1 (by rfl) ⟨673673, by rfl⟩ : syracuseStep 898231 = 1347347) B1347347
theorem B1324297 : Blo 550806 1324297 := bstep (se 2 (by rfl) ⟨496611, by rfl⟩ : syracuseStep 1324297 = 993223) B993223
theorem B931081 : Blo 550806 931081 := bstep (se 2 (by rfl) ⟨349155, by rfl⟩ : syracuseStep 931081 = 698311) B698311
theorem B931135 : Blo 550806 931135 := bstep (se 1 (by rfl) ⟨698351, by rfl⟩ : syracuseStep 931135 = 1396703) B1396703
theorem B11974031 : Blo 550806 11974031 := bstep (se 1 (by rfl) ⟨8980523, by rfl⟩ : syracuseStep 11974031 = 17961047) B17961047
theorem B2799035 : Blo 550806 2799035 := bstep (se 1 (by rfl) ⟨2099276, by rfl⟩ : syracuseStep 2799035 = 4198553) B4198553
theorem B931567 : Blo 550806 931567 := bstep (se 1 (by rfl) ⟨698675, by rfl⟩ : syracuseStep 931567 = 1397351) B1397351
theorem B35862425 : Blo 550806 35862425 := bstep (se 2 (by rfl) ⟨13448409, by rfl⟩ : syracuseStep 35862425 = 26896819) B26896819
theorem B932303 : Blo 550806 932303 := bstep (se 1 (by rfl) ⟨699227, by rfl⟩ : syracuseStep 932303 = 1398455) B1398455
theorem B3783905 : Blo 550806 3783905 := bstep (se 2 (by rfl) ⟨1418964, by rfl⟩ : syracuseStep 3783905 = 2837929) B2837929
theorem B933599 : Blo 550806 933599 := bstep (se 1 (by rfl) ⟨700199, by rfl⟩ : syracuseStep 933599 = 1400399) B1400399
theorem B31768361 : Blo 550806 31768361 := bstep (se 2 (by rfl) ⟨11913135, by rfl⟩ : syracuseStep 31768361 = 23826271) B23826271
theorem B1261391 : Blo 550806 1261391 := bstep (se 1 (by rfl) ⟨946043, by rfl⟩ : syracuseStep 1261391 = 1892087) B1892087
theorem B1262267 : Blo 550806 1262267 := bstep (se 1 (by rfl) ⟨946700, by rfl⟩ : syracuseStep 1262267 = 1893401) B1893401
theorem B935023 : Blo 550806 935023 := bstep (se 1 (by rfl) ⟨701267, by rfl⟩ : syracuseStep 935023 = 1402535) B1402535
theorem B2802923 : Blo 550806 2802923 := bstep (se 1 (by rfl) ⟨2102192, by rfl⟩ : syracuseStep 2802923 = 4204385) B4204385
theorem B1328671 : Blo 550806 1328671 := bstep (se 1 (by rfl) ⟨996503, by rfl⟩ : syracuseStep 1328671 = 1993007) B1993007
theorem B935455 : Blo 550806 935455 := bstep (se 1 (by rfl) ⟨701591, by rfl⟩ : syracuseStep 935455 = 1403183) B1403183
theorem B3360599 : Blo 550806 3360599 := bstep (se 1 (by rfl) ⟨2520449, by rfl⟩ : syracuseStep 3360599 = 5040899) B5040899
theorem B8997131 : Blo 550806 8997131 := bstep (se 1 (by rfl) ⟨6747848, by rfl⟩ : syracuseStep 8997131 = 13495697) B13495697
theorem B2837063 : Blo 550806 2837063 := bstep (se 1 (by rfl) ⟨2127797, by rfl⟩ : syracuseStep 2837063 = 4255595) B4255595
theorem B5688251 : Blo 550806 5688251 := bstep (se 1 (by rfl) ⟨4266188, by rfl⟩ : syracuseStep 5688251 = 8532377) B8532377
theorem B5098729 : Blo 550806 5098729 := bstep (se 2 (by rfl) ⟨1912023, by rfl⟩ : syracuseStep 5098729 = 3824047) B3824047
theorem B11360249 : Blo 550806 11360249 := bstep (se 2 (by rfl) ⟨4260093, by rfl⟩ : syracuseStep 11360249 = 8520187) B8520187
theorem B5299343 : Blo 550806 5299343 := bstep (se 1 (by rfl) ⟨3974507, by rfl⟩ : syracuseStep 5299343 = 7949015) B7949015
theorem B7396753 : Blo 550806 7396753 := bstep (se 2 (by rfl) ⟨2773782, by rfl⟩ : syracuseStep 7396753 = 5547565) B5547565
theorem B5168731 : Blo 550806 5168731 := bstep (se 1 (by rfl) ⟨3876548, by rfl⟩ : syracuseStep 5168731 = 7753097) B7753097
theorem B1597049 : Blo 550806 1597049 := bstep (se 2 (by rfl) ⟨598893, by rfl⟩ : syracuseStep 1597049 = 1197787) B1197787
theorem B1498745 : Blo 550806 1498745 := bstep (se 2 (by rfl) ⟨562029, by rfl⟩ : syracuseStep 1498745 = 1124059) B1124059
theorem B843385 : Blo 550806 843385 := bstep (se 2 (by rfl) ⟨316269, by rfl⟩ : syracuseStep 843385 = 632539) B632539
theorem B3530897 : Blo 550806 3530897 := bstep (se 2 (by rfl) ⟨1324086, by rfl⟩ : syracuseStep 3530897 = 2648173) B2648173
theorem B1401371 : Blo 550806 1401371 := bstep (se 1 (by rfl) ⟨1051028, by rfl⟩ : syracuseStep 1401371 = 2102057) B2102057
theorem B4186889 : Blo 550806 4186889 := bstep (se 2 (by rfl) ⟨1570083, by rfl⟩ : syracuseStep 4186889 = 3140167) B3140167
theorem B1860407 : Blo 550806 1860407 := bstep (se 1 (by rfl) ⟨1395305, by rfl⟩ : syracuseStep 1860407 = 2790611) B2790611
theorem B196338887 : Blo 550806 196338887 := bstep (se 1 (by rfl) ⟨147254165, by rfl⟩ : syracuseStep 196338887 = 294508331) B294508331
theorem B943417 : Blo 550806 943417 := bstep (se 2 (by rfl) ⟨353781, by rfl⟩ : syracuseStep 943417 = 707563) B707563
theorem B550847 : Blo 550806 550847 := bstep (se 1 (by rfl) ⟨413135, by rfl⟩ : syracuseStep 550847 = 826271) B826271
theorem B1861595 : Blo 550806 1861595 := bstep (se 1 (by rfl) ⟨1396196, by rfl⟩ : syracuseStep 1861595 = 2792393) B2792393
theorem B550879 : Blo 550806 550879 := bstep (se 1 (by rfl) ⟨413159, by rfl⟩ : syracuseStep 550879 = 826319) B826319
theorem B1402859 : Blo 550806 1402859 := bstep (se 1 (by rfl) ⟨1052144, by rfl⟩ : syracuseStep 1402859 = 2104289) B2104289
theorem B550939 : Blo 550806 550939 := bstep (se 1 (by rfl) ⟨413204, by rfl⟩ : syracuseStep 550939 = 826409) B826409
theorem B550943 : Blo 550806 550943 := bstep (se 1 (by rfl) ⟨413207, by rfl⟩ : syracuseStep 550943 = 826415) B826415
theorem B550959 : Blo 550806 550959 := bstep (se 1 (by rfl) ⟨413219, by rfl⟩ : syracuseStep 550959 = 826439) B826439
theorem B6744161 : Blo 550806 6744161 := bstep (se 2 (by rfl) ⟨2529060, by rfl⟩ : syracuseStep 6744161 = 5058121) B5058121
theorem B6285437 : Blo 550806 6285437 := bstep (se 3 (by rfl) ⟨1178519, by rfl⟩ : syracuseStep 6285437 = 2357039) B2357039
theorem B551135 : Blo 550806 551135 := bstep (se 1 (by rfl) ⟨413351, by rfl⟩ : syracuseStep 551135 = 826703) B826703
theorem B1861865 : Blo 550806 1861865 := bstep (se 2 (by rfl) ⟨698199, by rfl⟩ : syracuseStep 1861865 = 1396399) B1396399
theorem B551195 : Blo 550806 551195 := bstep (se 1 (by rfl) ⟨413396, by rfl⟩ : syracuseStep 551195 = 826793) B826793
theorem B551295 : Blo 550806 551295 := bstep (se 1 (by rfl) ⟨413471, by rfl⟩ : syracuseStep 551295 = 826943) B826943
theorem B1862135 : Blo 550806 1862135 := bstep (se 1 (by rfl) ⟨1396601, by rfl⟩ : syracuseStep 1862135 = 2793203) B2793203
theorem B551471 : Blo 550806 551471 := bstep (se 1 (by rfl) ⟨413603, by rfl⟩ : syracuseStep 551471 = 827207) B827207
theorem B551527 : Blo 550806 551527 := bstep (se 1 (by rfl) ⟨413645, by rfl⟩ : syracuseStep 551527 = 827291) B827291
theorem B1862297 : Blo 550806 1862297 := bstep (se 2 (by rfl) ⟨698361, by rfl⟩ : syracuseStep 1862297 = 1396723) B1396723
theorem B551903 : Blo 550806 551903 := bstep (se 1 (by rfl) ⟨413927, by rfl⟩ : syracuseStep 551903 = 827855) B827855
theorem B551931 : Blo 550806 551931 := bstep (se 1 (by rfl) ⟨413948, by rfl⟩ : syracuseStep 551931 = 827897) B827897
theorem B551999 : Blo 550806 551999 := bstep (se 1 (by rfl) ⟨413999, by rfl⟩ : syracuseStep 551999 = 827999) B827999
theorem B1862729 : Blo 550806 1862729 := bstep (se 2 (by rfl) ⟨698523, by rfl⟩ : syracuseStep 1862729 = 1397047) B1397047
theorem B552319 : Blo 550806 552319 := bstep (se 1 (by rfl) ⟨414239, by rfl⟩ : syracuseStep 552319 = 828479) B828479
theorem B552347 : Blo 550806 552347 := bstep (se 1 (by rfl) ⟨414260, by rfl⟩ : syracuseStep 552347 = 828521) B828521
theorem B1240487 : Blo 550806 1240487 := bstep (se 1 (by rfl) ⟨930365, by rfl⟩ : syracuseStep 1240487 = 1860731) B1860731
theorem B552415 : Blo 550806 552415 := bstep (se 1 (by rfl) ⟨414311, by rfl⟩ : syracuseStep 552415 = 828623) B828623
theorem B1240667 : Blo 550806 1240667 := bstep (se 1 (by rfl) ⟨930500, by rfl⟩ : syracuseStep 1240667 = 1861001) B1861001
theorem B17198689 : Blo 550806 17198689 := bstep (se 2 (by rfl) ⟨6449508, by rfl⟩ : syracuseStep 17198689 = 12899017) B12899017
theorem B552551 : Blo 550806 552551 := bstep (se 1 (by rfl) ⟨414413, by rfl⟩ : syracuseStep 552551 = 828827) B828827
theorem B1765115 : Blo 550806 1765115 := bstep (se 1 (by rfl) ⟨1323836, by rfl⟩ : syracuseStep 1765115 = 2647673) B2647673
theorem B3534587 : Blo 550806 3534587 := bstep (se 1 (by rfl) ⟨2650940, by rfl⟩ : syracuseStep 3534587 = 5301881) B5301881
theorem B552699 : Blo 550806 552699 := bstep (se 1 (by rfl) ⟨414524, by rfl⟩ : syracuseStep 552699 = 829049) B829049
theorem B552767 : Blo 550806 552767 := bstep (se 1 (by rfl) ⟨414575, by rfl⟩ : syracuseStep 552767 = 829151) B829151
theorem B3993421 : Blo 550806 3993421 := bstep (se 3 (by rfl) ⟨748766, by rfl⟩ : syracuseStep 3993421 = 1497533) B1497533
theorem B552831 : Blo 550806 552831 := bstep (se 1 (by rfl) ⟨414623, by rfl⟩ : syracuseStep 552831 = 829247) B829247
theorem B552943 : Blo 550806 552943 := bstep (se 1 (by rfl) ⟨414707, by rfl⟩ : syracuseStep 552943 = 829415) B829415
theorem B1241081 : Blo 550806 1241081 := bstep (se 2 (by rfl) ⟨465405, by rfl⟩ : syracuseStep 1241081 = 930811) B930811
theorem B552955 : Blo 550806 552955 := bstep (se 1 (by rfl) ⟨414716, by rfl⟩ : syracuseStep 552955 = 829433) B829433
theorem B553023 : Blo 550806 553023 := bstep (se 1 (by rfl) ⟨414767, by rfl⟩ : syracuseStep 553023 = 829535) B829535
theorem B1241171 : Blo 550806 1241171 := bstep (se 1 (by rfl) ⟨930878, by rfl⟩ : syracuseStep 1241171 = 1861757) B1861757
theorem B553063 : Blo 550806 553063 := bstep (se 1 (by rfl) ⟨414797, by rfl⟩ : syracuseStep 553063 = 829595) B829595
theorem B553087 : Blo 550806 553087 := bstep (se 1 (by rfl) ⟨414815, by rfl⟩ : syracuseStep 553087 = 829631) B829631
theorem B10121345 : Blo 550806 10121345 := bstep (se 2 (by rfl) ⟨3795504, by rfl⟩ : syracuseStep 10121345 = 7591009) B7591009
theorem B553115 : Blo 550806 553115 := bstep (se 1 (by rfl) ⟨414836, by rfl⟩ : syracuseStep 553115 = 829673) B829673
theorem B1241351 : Blo 550806 1241351 := bstep (se 1 (by rfl) ⟨931013, by rfl⟩ : syracuseStep 1241351 = 1862027) B1862027
theorem B4485401 : Blo 550806 4485401 := bstep (se 2 (by rfl) ⟨1682025, by rfl⟩ : syracuseStep 4485401 = 3364051) B3364051
theorem B1569127 : Blo 550806 1569127 := bstep (se 1 (by rfl) ⟨1176845, by rfl⟩ : syracuseStep 1569127 = 2353691) B2353691
theorem B553319 : Blo 550806 553319 := bstep (se 1 (by rfl) ⟨414989, by rfl⟩ : syracuseStep 553319 = 829979) B829979
theorem B553371 : Blo 550806 553371 := bstep (se 1 (by rfl) ⟨415028, by rfl⟩ : syracuseStep 553371 = 830057) B830057
theorem B1864187 : Blo 550806 1864187 := bstep (se 1 (by rfl) ⟨1398140, by rfl⟩ : syracuseStep 1864187 = 2796281) B2796281
theorem B1241657 : Blo 550806 1241657 := bstep (se 2 (by rfl) ⟨465621, by rfl⟩ : syracuseStep 1241657 = 931243) B931243
theorem B2650747 : Blo 550806 2650747 := bstep (se 1 (by rfl) ⟨1988060, by rfl⟩ : syracuseStep 2650747 = 3976121) B3976121
theorem B1766063 : Blo 550806 1766063 := bstep (se 1 (by rfl) ⟨1324547, by rfl⟩ : syracuseStep 1766063 = 2649095) B2649095
theorem B553723 : Blo 550806 553723 := bstep (se 1 (by rfl) ⟨415292, by rfl⟩ : syracuseStep 553723 = 830585) B830585
theorem B1864457 : Blo 550806 1864457 := bstep (se 2 (by rfl) ⟨699171, by rfl⟩ : syracuseStep 1864457 = 1398343) B1398343
theorem B553791 : Blo 550806 553791 := bstep (se 1 (by rfl) ⟨415343, by rfl⟩ : syracuseStep 553791 = 830687) B830687
theorem B553819 : Blo 550806 553819 := bstep (se 1 (by rfl) ⟨415364, by rfl⟩ : syracuseStep 553819 = 830729) B830729
theorem B553887 : Blo 550806 553887 := bstep (se 1 (by rfl) ⟨415415, by rfl⟩ : syracuseStep 553887 = 830831) B830831
theorem B553967 : Blo 550806 553967 := bstep (se 1 (by rfl) ⟨415475, by rfl⟩ : syracuseStep 553967 = 830951) B830951
theorem B7074809 : Blo 550806 7074809 := bstep (se 2 (by rfl) ⟨2653053, by rfl⟩ : syracuseStep 7074809 = 5306107) B5306107
theorem B10613753 : Blo 550806 10613753 := bstep (se 2 (by rfl) ⟨3980157, by rfl⟩ : syracuseStep 10613753 = 7960315) B7960315
theorem B554055 : Blo 550806 554055 := bstep (se 1 (by rfl) ⟨415541, by rfl⟩ : syracuseStep 554055 = 831083) B831083
theorem B554139 : Blo 550806 554139 := bstep (se 1 (by rfl) ⟨415604, by rfl⟩ : syracuseStep 554139 = 831209) B831209
theorem B619771 : Blo 550806 619771 := bstep (se 1 (by rfl) ⟨464828, by rfl⟩ : syracuseStep 619771 = 929657) B929657
theorem B554235 : Blo 550806 554235 := bstep (se 1 (by rfl) ⟨415676, by rfl⟩ : syracuseStep 554235 = 831353) B831353
theorem B1963271 : Blo 550806 1963271 := bstep (se 1 (by rfl) ⟨1472453, by rfl⟩ : syracuseStep 1963271 = 2944907) B2944907
theorem B1242377 : Blo 550806 1242377 := bstep (se 2 (by rfl) ⟨465891, by rfl⟩ : syracuseStep 1242377 = 931783) B931783
theorem B849215 : Blo 550806 849215 := bstep (se 1 (by rfl) ⟨636911, by rfl⟩ : syracuseStep 849215 = 1273823) B1273823
theorem B1242431 : Blo 550806 1242431 := bstep (se 1 (by rfl) ⟨931823, by rfl⟩ : syracuseStep 1242431 = 1863647) B1863647
theorem B554303 : Blo 550806 554303 := bstep (se 1 (by rfl) ⟨415727, by rfl⟩ : syracuseStep 554303 = 831455) B831455
theorem B1242539 : Blo 550806 1242539 := bstep (se 1 (by rfl) ⟨931904, by rfl⟩ : syracuseStep 1242539 = 1863809) B1863809
theorem B554471 : Blo 550806 554471 := bstep (se 1 (by rfl) ⟨415853, by rfl⟩ : syracuseStep 554471 = 831707) B831707
theorem B554479 : Blo 550806 554479 := bstep (se 1 (by rfl) ⟨415859, by rfl⟩ : syracuseStep 554479 = 831719) B831719
theorem B554587 : Blo 550806 554587 := bstep (se 1 (by rfl) ⟨415940, by rfl⟩ : syracuseStep 554587 = 831881) B831881
theorem B554651 : Blo 550806 554651 := bstep (se 1 (by rfl) ⟨415988, by rfl⟩ : syracuseStep 554651 = 831977) B831977
theorem B1570529 : Blo 550806 1570529 := bstep (se 2 (by rfl) ⟨588948, by rfl⟩ : syracuseStep 1570529 = 1177897) B1177897
theorem B1242863 : Blo 550806 1242863 := bstep (se 1 (by rfl) ⟨932147, by rfl⟩ : syracuseStep 1242863 = 1864295) B1864295
theorem B554735 : Blo 550806 554735 := bstep (se 1 (by rfl) ⟨416051, by rfl⟩ : syracuseStep 554735 = 832103) B832103
theorem B1046351 : Blo 550806 1046351 := bstep (se 1 (by rfl) ⟨784763, by rfl⟩ : syracuseStep 1046351 = 1569527) B1569527
theorem B21297005 : Blo 550806 21297005 := bstep (se 3 (by rfl) ⟨3993188, by rfl⟩ : syracuseStep 21297005 = 7986377) B7986377
theorem B1243079 : Blo 550806 1243079 := bstep (se 1 (by rfl) ⟨932309, by rfl⟩ : syracuseStep 1243079 = 1864619) B1864619
theorem B2685089 : Blo 550806 2685089 := bstep (se 2 (by rfl) ⟨1006908, by rfl⟩ : syracuseStep 2685089 = 2013817) B2013817
theorem B1243367 : Blo 550806 1243367 := bstep (se 1 (by rfl) ⟨932525, by rfl⟩ : syracuseStep 1243367 = 1865051) B1865051
theorem B1243385 : Blo 550806 1243385 := bstep (se 2 (by rfl) ⟨466269, by rfl⟩ : syracuseStep 1243385 = 932539) B932539
theorem B1243439 : Blo 550806 1243439 := bstep (se 1 (by rfl) ⟨932579, by rfl⟩ : syracuseStep 1243439 = 1865159) B1865159
theorem B620959 : Blo 550806 620959 := bstep (se 1 (by rfl) ⟨465719, by rfl⟩ : syracuseStep 620959 = 931439) B931439
theorem B2357723 : Blo 550806 2357723 := bstep (se 1 (by rfl) ⟨1768292, by rfl⟩ : syracuseStep 2357723 = 3536585) B3536585
theorem B621031 : Blo 550806 621031 := bstep (se 1 (by rfl) ⟨465773, by rfl⟩ : syracuseStep 621031 = 931547) B931547
theorem B1243655 : Blo 550806 1243655 := bstep (se 1 (by rfl) ⟨932741, by rfl⟩ : syracuseStep 1243655 = 1865483) B1865483
theorem B33094277 : Blo 550806 33094277 := bstep (se 4 (by rfl) ⟨3102588, by rfl⟩ : syracuseStep 33094277 = 6205177) B6205177
theorem B1243835 : Blo 550806 1243835 := bstep (se 1 (by rfl) ⟨932876, by rfl⟩ : syracuseStep 1243835 = 1865753) B1865753
theorem B2653037 : Blo 550806 2653037 := bstep (se 3 (by rfl) ⟨497444, by rfl⟩ : syracuseStep 2653037 = 994889) B994889
theorem B1768729 : Blo 550806 1768729 := bstep (se 2 (by rfl) ⟨663273, by rfl⟩ : syracuseStep 1768729 = 1326547) B1326547
theorem B3538201 : Blo 550806 3538201 := bstep (se 2 (by rfl) ⟨1326825, by rfl⟩ : syracuseStep 3538201 = 2653651) B2653651
theorem B621895 : Blo 550806 621895 := bstep (se 1 (by rfl) ⟨466421, by rfl⟩ : syracuseStep 621895 = 932843) B932843
theorem B2129341 : Blo 550806 2129341 := bstep (se 3 (by rfl) ⟨399251, by rfl⟩ : syracuseStep 2129341 = 798503) B798503
theorem B1244735 : Blo 550806 1244735 := bstep (se 1 (by rfl) ⟨933551, by rfl⟩ : syracuseStep 1244735 = 1867103) B1867103
theorem B1048295 : Blo 550806 1048295 := bstep (se 1 (by rfl) ⟨786221, by rfl⟩ : syracuseStep 1048295 = 1572443) B1572443
theorem B1245095 : Blo 550806 1245095 := bstep (se 1 (by rfl) ⟨933821, by rfl⟩ : syracuseStep 1245095 = 1867643) B1867643
theorem B2687231 : Blo 550806 2687231 := bstep (se 1 (by rfl) ⟨2015423, by rfl⟩ : syracuseStep 2687231 = 4030847) B4030847
theorem B1245599 : Blo 550806 1245599 := bstep (se 1 (by rfl) ⟨934199, by rfl⟩ : syracuseStep 1245599 = 1868399) B1868399
theorem B1868615 : Blo 550806 1868615 := bstep (se 1 (by rfl) ⟨1401461, by rfl⟩ : syracuseStep 1868615 = 2802923) B2802923
theorem B4195151 : Blo 550806 4195151 := bstep (se 1 (by rfl) ⟨3146363, by rfl⟩ : syracuseStep 4195151 = 6292727) B6292727
theorem B3408911 : Blo 550806 3408911 := bstep (se 1 (by rfl) ⟨2556683, by rfl⟩ : syracuseStep 3408911 = 5113367) B5113367
theorem B1246697 : Blo 550806 1246697 := bstep (se 2 (by rfl) ⟨467511, by rfl⟩ : syracuseStep 1246697 = 935023) B935023
theorem B5998087 : Blo 550806 5998087 := bstep (se 1 (by rfl) ⟨4498565, by rfl⟩ : syracuseStep 5998087 = 8997131) B8997131
theorem B1181459 : Blo 550806 1181459 := bstep (se 1 (by rfl) ⟨886094, by rfl⟩ : syracuseStep 1181459 = 1772189) B1772189
theorem B788459 : Blo 550806 788459 := bstep (se 1 (by rfl) ⟨591344, by rfl⟩ : syracuseStep 788459 = 1182689) B1182689
theorem B1771561 : Blo 550806 1771561 := bstep (se 2 (by rfl) ⟨664335, by rfl⟩ : syracuseStep 1771561 = 1328671) B1328671
theorem B886825 : Blo 550806 886825 := bstep (se 2 (by rfl) ⟨332559, by rfl⟩ : syracuseStep 886825 = 665119) B665119
theorem B1247273 : Blo 550806 1247273 := bstep (se 2 (by rfl) ⟨467727, by rfl⟩ : syracuseStep 1247273 = 935455) B935455
theorem B1051127 : Blo 550806 1051127 := bstep (se 1 (by rfl) ⟨788345, by rfl⟩ : syracuseStep 1051127 = 1576691) B1576691
theorem B4557313 : Blo 550806 4557313 := bstep (se 2 (by rfl) ⟨1708992, by rfl⟩ : syracuseStep 4557313 = 3417985) B3417985
theorem B1247903 : Blo 550806 1247903 := bstep (se 1 (by rfl) ⟨935927, by rfl⟩ : syracuseStep 1247903 = 1871855) B1871855
theorem B1576189 : Blo 550806 1576189 := bstep (se 3 (by rfl) ⟨295535, by rfl⟩ : syracuseStep 1576189 = 591071) B591071
theorem B2264573 : Blo 550806 2264573 := bstep (se 3 (by rfl) ⟨424607, by rfl⟩ : syracuseStep 2264573 = 849215) B849215
theorem B8982215 : Blo 550806 8982215 := bstep (se 1 (by rfl) ⟨6736661, by rfl⟩ : syracuseStep 8982215 = 13473323) B13473323
theorem B1576759 : Blo 550806 1576759 := bstep (se 1 (by rfl) ⟨1182569, by rfl⟩ : syracuseStep 1576759 = 2365139) B2365139
theorem B7573499 : Blo 550806 7573499 := bstep (se 1 (by rfl) ⟨5680124, by rfl⟩ : syracuseStep 7573499 = 11360249) B11360249
theorem B1577033 : Blo 550806 1577033 := bstep (se 2 (by rfl) ⟨591387, by rfl⟩ : syracuseStep 1577033 = 1182775) B1182775
theorem B1183817 : Blo 550806 1183817 := bstep (se 2 (by rfl) ⟨443931, by rfl⟩ : syracuseStep 1183817 = 887863) B887863
theorem B2101889 : Blo 550806 2101889 := bstep (se 2 (by rfl) ⟨788208, by rfl⟩ : syracuseStep 2101889 = 1576417) B1576417
theorem B1577819 : Blo 550806 1577819 := bstep (se 1 (by rfl) ⟨1183364, by rfl⟩ : syracuseStep 1577819 = 2366729) B2366729
theorem B2791259 : Blo 550806 2791259 := bstep (se 1 (by rfl) ⟨2093444, by rfl⟩ : syracuseStep 2791259 = 4186889) B4186889
theorem B9443465 : Blo 550806 9443465 := bstep (se 2 (by rfl) ⟨3541299, by rfl⟩ : syracuseStep 9443465 = 7082599) B7082599
theorem B2103515 : Blo 550806 2103515 := bstep (se 1 (by rfl) ⟨1577636, by rfl⟩ : syracuseStep 2103515 = 3155273) B3155273
theorem B6363623 : Blo 550806 6363623 := bstep (se 1 (by rfl) ⟨4772717, by rfl⟩ : syracuseStep 6363623 = 9545435) B9545435
theorem B4496107 : Blo 550806 4496107 := bstep (se 1 (by rfl) ⟨3372080, by rfl⟩ : syracuseStep 4496107 = 6744161) B6744161
theorem B3546017 : Blo 550806 3546017 := bstep (se 2 (by rfl) ⟨1329756, by rfl⟩ : syracuseStep 3546017 = 2659513) B2659513
theorem B826361 : Blo 550806 826361 := bstep (se 2 (by rfl) ⟨309885, by rfl⟩ : syracuseStep 826361 = 619771) B619771
theorem B826991 : Blo 550806 826991 := bstep (se 1 (by rfl) ⟨620243, by rfl⟩ : syracuseStep 826991 = 1240487) B1240487
theorem B827111 : Blo 550806 827111 := bstep (se 1 (by rfl) ⟨620333, by rfl⟩ : syracuseStep 827111 = 1240667) B1240667
theorem B827387 : Blo 550806 827387 := bstep (se 1 (by rfl) ⟨620540, by rfl⟩ : syracuseStep 827387 = 1241081) B1241081
theorem B827447 : Blo 550806 827447 := bstep (se 1 (by rfl) ⟨620585, by rfl⟩ : syracuseStep 827447 = 1241171) B1241171
theorem B827567 : Blo 550806 827567 := bstep (se 1 (by rfl) ⟨620675, by rfl⟩ : syracuseStep 827567 = 1241351) B1241351
theorem B2990267 : Blo 550806 2990267 := bstep (se 1 (by rfl) ⟨2242700, by rfl⟩ : syracuseStep 2990267 = 4485401) B4485401
theorem B7872815 : Blo 550806 7872815 := bstep (se 1 (by rfl) ⟨5904611, by rfl⟩ : syracuseStep 7872815 = 11809223) B11809223
theorem B827771 : Blo 550806 827771 := bstep (se 1 (by rfl) ⟨620828, by rfl⟩ : syracuseStep 827771 = 1241657) B1241657
theorem B2236943 : Blo 550806 2236943 := bstep (se 1 (by rfl) ⟨1677707, by rfl⟩ : syracuseStep 2236943 = 3355415) B3355415
theorem B827945 : Blo 550806 827945 := bstep (se 2 (by rfl) ⟨310479, by rfl⟩ : syracuseStep 827945 = 620959) B620959
theorem B3547759 : Blo 550806 3547759 := bstep (se 1 (by rfl) ⟨2660819, by rfl⟩ : syracuseStep 3547759 = 5321639) B5321639
theorem B2368111 : Blo 550806 2368111 := bstep (se 1 (by rfl) ⟨1776083, by rfl⟩ : syracuseStep 2368111 = 3552167) B3552167
theorem B828041 : Blo 550806 828041 := bstep (se 2 (by rfl) ⟨310515, by rfl⟩ : syracuseStep 828041 = 621031) B621031
theorem B828251 : Blo 550806 828251 := bstep (se 1 (by rfl) ⟨621188, by rfl⟩ : syracuseStep 828251 = 1242377) B1242377
theorem B828287 : Blo 550806 828287 := bstep (se 1 (by rfl) ⟨621215, by rfl⟩ : syracuseStep 828287 = 1242431) B1242431
theorem B828359 : Blo 550806 828359 := bstep (se 1 (by rfl) ⟨621269, by rfl⟩ : syracuseStep 828359 = 1242539) B1242539
theorem B828575 : Blo 550806 828575 := bstep (se 1 (by rfl) ⟨621431, by rfl⟩ : syracuseStep 828575 = 1242863) B1242863
theorem B697567 : Blo 550806 697567 := bstep (se 1 (by rfl) ⟨523175, by rfl⟩ : syracuseStep 697567 = 1046351) B1046351
theorem B14198003 : Blo 550806 14198003 := bstep (se 1 (by rfl) ⟨10648502, by rfl⟩ : syracuseStep 14198003 = 21297005) B21297005
theorem B828719 : Blo 550806 828719 := bstep (se 1 (by rfl) ⟨621539, by rfl⟩ : syracuseStep 828719 = 1243079) B1243079
theorem B828911 : Blo 550806 828911 := bstep (se 1 (by rfl) ⟨621683, by rfl⟩ : syracuseStep 828911 = 1243367) B1243367
theorem B828923 : Blo 550806 828923 := bstep (se 1 (by rfl) ⟨621692, by rfl⟩ : syracuseStep 828923 = 1243385) B1243385
theorem B3548681 : Blo 550806 3548681 := bstep (se 2 (by rfl) ⟨1330755, by rfl⟩ : syracuseStep 3548681 = 2661511) B2661511
theorem B828959 : Blo 550806 828959 := bstep (se 1 (by rfl) ⟨621719, by rfl⟩ : syracuseStep 828959 = 1243439) B1243439
theorem B829103 : Blo 550806 829103 := bstep (se 1 (by rfl) ⟨621827, by rfl⟩ : syracuseStep 829103 = 1243655) B1243655
theorem B22062851 : Blo 550806 22062851 := bstep (se 1 (by rfl) ⟨16547138, by rfl⟩ : syracuseStep 22062851 = 33094277) B33094277
theorem B829193 : Blo 550806 829193 := bstep (se 2 (by rfl) ⟨310947, by rfl⟩ : syracuseStep 829193 = 621895) B621895
theorem B829223 : Blo 550806 829223 := bstep (se 1 (by rfl) ⟨621917, by rfl⟩ : syracuseStep 829223 = 1243835) B1243835
theorem B6891641 : Blo 550806 6891641 := bstep (se 2 (by rfl) ⟨2584365, by rfl⟩ : syracuseStep 6891641 = 5168731) B5168731
theorem B1124513 : Blo 550806 1124513 := bstep (se 2 (by rfl) ⟨421692, by rfl⟩ : syracuseStep 1124513 = 843385) B843385
theorem B11938049 : Blo 550806 11938049 := bstep (se 2 (by rfl) ⟨4476768, by rfl⟩ : syracuseStep 11938049 = 8953537) B8953537
theorem B829823 : Blo 550806 829823 := bstep (se 1 (by rfl) ⟨622367, by rfl⟩ : syracuseStep 829823 = 1244735) B1244735
theorem B698863 : Blo 550806 698863 := bstep (se 1 (by rfl) ⟨524147, by rfl⟩ : syracuseStep 698863 = 1048295) B1048295
theorem B21178907 : Blo 550806 21178907 := bstep (se 1 (by rfl) ⟨15884180, by rfl⟩ : syracuseStep 21178907 = 31768361) B31768361
theorem B830063 : Blo 550806 830063 := bstep (se 1 (by rfl) ⟨622547, by rfl⟩ : syracuseStep 830063 = 1245095) B1245095
theorem B830279 : Blo 550806 830279 := bstep (se 1 (by rfl) ⟨622709, by rfl⟩ : syracuseStep 830279 = 1245419) B1245419
theorem B699455 : Blo 550806 699455 := bstep (se 1 (by rfl) ⟨524591, by rfl⟩ : syracuseStep 699455 = 1049183) B1049183
theorem B830879 : Blo 550806 830879 := bstep (se 1 (by rfl) ⟨623159, by rfl⟩ : syracuseStep 830879 = 1246319) B1246319
theorem B831143 : Blo 550806 831143 := bstep (se 1 (by rfl) ⟨623357, by rfl⟩ : syracuseStep 831143 = 1246715) B1246715
theorem B831167 : Blo 550806 831167 := bstep (se 1 (by rfl) ⟨623375, by rfl⟩ : syracuseStep 831167 = 1246751) B1246751
theorem B831263 : Blo 550806 831263 := bstep (se 1 (by rfl) ⟨623447, by rfl⟩ : syracuseStep 831263 = 1246895) B1246895
theorem B2240399 : Blo 550806 2240399 := bstep (se 1 (by rfl) ⟨1680299, by rfl⟩ : syracuseStep 2240399 = 3360599) B3360599
theorem B831551 : Blo 550806 831551 := bstep (se 1 (by rfl) ⟨623663, by rfl⟩ : syracuseStep 831551 = 1247327) B1247327
theorem B831743 : Blo 550806 831743 := bstep (se 1 (by rfl) ⟨623807, by rfl⟩ : syracuseStep 831743 = 1247615) B1247615
theorem B831785 : Blo 550806 831785 := bstep (se 2 (by rfl) ⟨311919, by rfl⟩ : syracuseStep 831785 = 623839) B623839
theorem B832055 : Blo 550806 832055 := bstep (se 1 (by rfl) ⟨624041, by rfl⟩ : syracuseStep 832055 = 1248083) B1248083
theorem B10663811 : Blo 550806 10663811 := bstep (se 1 (by rfl) ⟨7997858, by rfl⟩ : syracuseStep 10663811 = 15995717) B15995717
theorem B1685627 : Blo 550806 1685627 := bstep (se 1 (by rfl) ⟨1264220, by rfl⟩ : syracuseStep 1685627 = 2528441) B2528441
theorem B2800169 : Blo 550806 2800169 := bstep (se 2 (by rfl) ⟨1050063, by rfl⟩ : syracuseStep 2800169 = 2100127) B2100127
theorem B349223669 : Blo 550806 349223669 := bstep (se 5 (by rfl) ⟨16369859, by rfl⟩ : syracuseStep 349223669 = 32739719) B32739719
theorem B6798305 : Blo 550806 6798305 := bstep (se 2 (by rfl) ⟨2549364, by rfl⟩ : syracuseStep 6798305 = 5098729) B5098729
theorem B900575 : Blo 550806 900575 := bstep (se 1 (by rfl) ⟨675431, by rfl⟩ : syracuseStep 900575 = 1350863) B1350863
theorem B1064699 : Blo 550806 1064699 := bstep (se 1 (by rfl) ⟨798524, by rfl⟩ : syracuseStep 1064699 = 1597049) B1597049
theorem B999163 : Blo 550806 999163 := bstep (se 1 (by rfl) ⟨749372, by rfl⟩ : syracuseStep 999163 = 1498745) B1498745
theorem B5324561 : Blo 550806 5324561 := bstep (se 2 (by rfl) ⟨1996710, by rfl⟩ : syracuseStep 5324561 = 3993421) B3993421
theorem B2801627 : Blo 550806 2801627 := bstep (se 1 (by rfl) ⟨2101220, by rfl⟩ : syracuseStep 2801627 = 4202441) B4202441
theorem B6832421 : Blo 550806 6832421 := bstep (se 4 (by rfl) ⟨640539, by rfl⟩ : syracuseStep 6832421 = 1281079) B1281079
theorem B4243751 : Blo 550806 4243751 := bstep (se 1 (by rfl) ⟨3182813, by rfl⟩ : syracuseStep 4243751 = 6365627) B6365627
theorem B934247 : Blo 550806 934247 := bstep (se 1 (by rfl) ⟨700685, by rfl⟩ : syracuseStep 934247 = 1401371) B1401371
theorem B7160237 : Blo 550806 7160237 := bstep (se 3 (by rfl) ⟨1342544, by rfl⟩ : syracuseStep 7160237 = 2685089) B2685089
theorem B130892591 : Blo 550806 130892591 := bstep (se 1 (by rfl) ⟨98169443, by rfl⟩ : syracuseStep 130892591 = 196338887) B196338887
theorem B935239 : Blo 550806 935239 := bstep (se 1 (by rfl) ⟨701429, by rfl⟩ : syracuseStep 935239 = 1402859) B1402859
theorem B27280793 : Blo 550806 27280793 := bstep (se 2 (by rfl) ⟨10230297, by rfl⟩ : syracuseStep 27280793 = 20460595) B20460595
theorem B1197641 : Blo 550806 1197641 := bstep (se 2 (by rfl) ⟨449115, by rfl⟩ : syracuseStep 1197641 = 898231) B898231
theorem B5031557 : Blo 550806 5031557 := bstep (se 4 (by rfl) ⟨471708, by rfl⟩ : syracuseStep 5031557 = 943417) B943417
theorem B8964377 : Blo 550806 8964377 := bstep (se 2 (by rfl) ⟨3361641, by rfl⟩ : syracuseStep 8964377 = 6723283) B6723283
theorem B13420889 : Blo 550806 13420889 := bstep (se 2 (by rfl) ⟨5032833, by rfl⟩ : syracuseStep 13420889 = 10065667) B10065667
theorem B2804381 : Blo 550806 2804381 := bstep (se 3 (by rfl) ⟨525821, by rfl⟩ : syracuseStep 2804381 = 1051643) B1051643
theorem B1494443 : Blo 550806 1494443 := bstep (se 1 (by rfl) ⟨1120832, by rfl⟩ : syracuseStep 1494443 = 2241665) B2241665
theorem B7982687 : Blo 550806 7982687 := bstep (se 1 (by rfl) ⟨5987015, by rfl⟩ : syracuseStep 7982687 = 11974031) B11974031
theorem B2805677 : Blo 550806 2805677 := bstep (se 3 (by rfl) ⟨526064, by rfl⟩ : syracuseStep 2805677 = 1052129) B1052129
theorem B23908283 : Blo 550806 23908283 := bstep (se 1 (by rfl) ⟨17931212, by rfl⟩ : syracuseStep 23908283 = 35862425) B35862425
theorem B2839121 : Blo 550806 2839121 := bstep (se 2 (by rfl) ⟨1064670, by rfl⟩ : syracuseStep 2839121 = 2129341) B2129341
theorem B3363709 : Blo 550806 3363709 := bstep (se 3 (by rfl) ⟨630695, by rfl⟩ : syracuseStep 3363709 = 1261391) B1261391
theorem B2807297 : Blo 550806 2807297 := bstep (se 2 (by rfl) ⟨1052736, by rfl⟩ : syracuseStep 2807297 = 2105473) B2105473
theorem B3364487 : Blo 550806 3364487 := bstep (se 1 (by rfl) ⟨2523365, by rfl⟩ : syracuseStep 3364487 = 5046731) B5046731
theorem B1595099 : Blo 550806 1595099 := bstep (se 1 (by rfl) ⟨1196324, by rfl⟩ : syracuseStep 1595099 = 2392649) B2392649
theorem B1398505 : Blo 550806 1398505 := bstep (se 2 (by rfl) ⟨524439, by rfl⟩ : syracuseStep 1398505 = 1048879) B1048879
theorem B841511 : Blo 550806 841511 := bstep (se 1 (by rfl) ⟨631133, by rfl⟩ : syracuseStep 841511 = 1262267) B1262267
theorem B1398971 : Blo 550806 1398971 := bstep (se 1 (by rfl) ⟨1049228, by rfl⟩ : syracuseStep 1398971 = 2098457) B2098457
theorem B1988983 : Blo 550806 1988983 := bstep (se 1 (by rfl) ⟨1491737, by rfl⟩ : syracuseStep 1988983 = 2983475) B2983475
theorem B1399913 : Blo 550806 1399913 := bstep (se 2 (by rfl) ⟨524967, by rfl⟩ : syracuseStep 1399913 = 1049935) B1049935
theorem B4709501 : Blo 550806 4709501 := bstep (se 3 (by rfl) ⟨883031, by rfl⟩ : syracuseStep 4709501 = 1766063) B1766063
theorem B3792167 : Blo 550806 3792167 := bstep (se 1 (by rfl) ⟨2844125, by rfl⟩ : syracuseStep 3792167 = 5688251) B5688251
theorem B51010955 : Blo 550806 51010955 := bstep (se 1 (by rfl) ⟨38258216, by rfl⟩ : syracuseStep 51010955 = 76516433) B76516433
theorem B76472045 : Blo 550806 76472045 := bstep (se 3 (by rfl) ⟨14338508, by rfl⟩ : syracuseStep 76472045 = 28677017) B28677017
theorem B6381359 : Blo 550806 6381359 := bstep (se 1 (by rfl) ⟨4786019, by rfl⟩ : syracuseStep 6381359 = 9572039) B9572039
theorem B3367115 : Blo 550806 3367115 := bstep (se 1 (by rfl) ⟨2525336, by rfl⟩ : syracuseStep 3367115 = 5050673) B5050673
theorem B1401047 : Blo 550806 1401047 := bstep (se 1 (by rfl) ⟨1050785, by rfl⟩ : syracuseStep 1401047 = 2101571) B2101571
theorem B1401209 : Blo 550806 1401209 := bstep (se 2 (by rfl) ⟨525453, by rfl⟩ : syracuseStep 1401209 = 1050907) B1050907
theorem B1860029 : Blo 550806 1860029 := bstep (se 3 (by rfl) ⟨348755, by rfl⟩ : syracuseStep 1860029 = 697511) B697511
theorem B550815 : Blo 550806 550815 := bstep (se 1 (by rfl) ⟨413111, by rfl⟩ : syracuseStep 550815 = 826223) B826223
theorem B550823 : Blo 550806 550823 := bstep (se 1 (by rfl) ⟨413117, by rfl⟩ : syracuseStep 550823 = 826235) B826235
theorem B3532895 : Blo 550806 3532895 := bstep (se 1 (by rfl) ⟨2649671, by rfl⟩ : syracuseStep 3532895 = 5299343) B5299343
theorem B22931585 : Blo 550806 22931585 := bstep (se 2 (by rfl) ⟨8599344, by rfl⟩ : syracuseStep 22931585 = 17198689) B17198689
theorem B1993079 : Blo 550806 1993079 := bstep (se 1 (by rfl) ⟨1494809, by rfl⟩ : syracuseStep 1993079 = 2989619) B2989619
theorem B551399 : Blo 550806 551399 := bstep (se 1 (by rfl) ⟨413549, by rfl⟩ : syracuseStep 551399 = 827099) B827099
theorem B551579 : Blo 550806 551579 := bstep (se 1 (by rfl) ⟨413684, by rfl⟩ : syracuseStep 551579 = 827369) B827369
theorem B1239713 : Blo 550806 1239713 := bstep (se 2 (by rfl) ⟨464892, by rfl⟩ : syracuseStep 1239713 = 929785) B929785
theorem B2353931 : Blo 550806 2353931 := bstep (se 1 (by rfl) ⟨1765448, by rfl⟩ : syracuseStep 2353931 = 3530897) B3530897
theorem B1403689 : Blo 550806 1403689 := bstep (se 2 (by rfl) ⟨526383, by rfl⟩ : syracuseStep 1403689 = 1052767) B1052767
theorem B1240073 : Blo 550806 1240073 := bstep (se 2 (by rfl) ⟨465027, by rfl⟩ : syracuseStep 1240073 = 930055) B930055
theorem B552047 : Blo 550806 552047 := bstep (se 1 (by rfl) ⟨414035, by rfl⟩ : syracuseStep 552047 = 828071) B828071
theorem B2092169 : Blo 550806 2092169 := bstep (se 2 (by rfl) ⟨784563, by rfl⟩ : syracuseStep 2092169 = 1569127) B1569127
theorem B552127 : Blo 550806 552127 := bstep (se 1 (by rfl) ⟨414095, by rfl⟩ : syracuseStep 552127 = 828191) B828191
theorem B1240271 : Blo 550806 1240271 := bstep (se 1 (by rfl) ⟨930203, by rfl⟩ : syracuseStep 1240271 = 1860407) B1860407
theorem B552143 : Blo 550806 552143 := bstep (se 1 (by rfl) ⟨414107, by rfl⟩ : syracuseStep 552143 = 828215) B828215
theorem B552263 : Blo 550806 552263 := bstep (se 1 (by rfl) ⟨414197, by rfl⟩ : syracuseStep 552263 = 828395) B828395
theorem B3599777 : Blo 550806 3599777 := bstep (se 2 (by rfl) ⟨1349916, by rfl⟩ : syracuseStep 3599777 = 2699833) B2699833
theorem B3534329 : Blo 550806 3534329 := bstep (se 2 (by rfl) ⟨1325373, by rfl⟩ : syracuseStep 3534329 = 2650747) B2650747
theorem B1241063 : Blo 550806 1241063 := bstep (se 1 (by rfl) ⟨930797, by rfl⟩ : syracuseStep 1241063 = 1861595) B1861595
theorem B552991 : Blo 550806 552991 := bstep (se 1 (by rfl) ⟨414743, by rfl⟩ : syracuseStep 552991 = 829487) B829487
theorem B4190291 : Blo 550806 4190291 := bstep (se 1 (by rfl) ⟨3142718, by rfl⟩ : syracuseStep 4190291 = 6285437) B6285437
theorem B1241243 : Blo 550806 1241243 := bstep (se 1 (by rfl) ⟨930932, by rfl⟩ : syracuseStep 1241243 = 1861865) B1861865
theorem B7565501 : Blo 550806 7565501 := bstep (se 3 (by rfl) ⟨1418531, by rfl⟩ : syracuseStep 7565501 = 2837063) B2837063
theorem B553167 : Blo 550806 553167 := bstep (se 1 (by rfl) ⟨414875, by rfl⟩ : syracuseStep 553167 = 829751) B829751
theorem B2650439 : Blo 550806 2650439 := bstep (se 1 (by rfl) ⟨1987829, by rfl⟩ : syracuseStep 2650439 = 3975659) B3975659
theorem B553287 : Blo 550806 553287 := bstep (se 1 (by rfl) ⟨414965, by rfl⟩ : syracuseStep 553287 = 829931) B829931
theorem B1241423 : Blo 550806 1241423 := bstep (se 1 (by rfl) ⟨931067, by rfl⟩ : syracuseStep 1241423 = 1862135) B1862135
theorem B1765729 : Blo 550806 1765729 := bstep (se 2 (by rfl) ⟨662148, by rfl⟩ : syracuseStep 1765729 = 1324297) B1324297
theorem B1241441 : Blo 550806 1241441 := bstep (se 2 (by rfl) ⟨465540, by rfl⟩ : syracuseStep 1241441 = 931081) B931081
theorem B1241513 : Blo 550806 1241513 := bstep (se 2 (by rfl) ⟨465567, by rfl⟩ : syracuseStep 1241513 = 931135) B931135
theorem B1241531 : Blo 550806 1241531 := bstep (se 1 (by rfl) ⟨931148, by rfl⟩ : syracuseStep 1241531 = 1862297) B1862297
theorem B1241819 : Blo 550806 1241819 := bstep (se 1 (by rfl) ⟨931364, by rfl⟩ : syracuseStep 1241819 = 1862729) B1862729
theorem B553755 : Blo 550806 553755 := bstep (se 1 (by rfl) ⟨415316, by rfl⟩ : syracuseStep 553755 = 830633) B830633
theorem B1242089 : Blo 550806 1242089 := bstep (se 2 (by rfl) ⟨465783, by rfl⟩ : syracuseStep 1242089 = 931567) B931567
theorem B554031 : Blo 550806 554031 := bstep (se 1 (by rfl) ⟨415523, by rfl⟩ : syracuseStep 554031 = 831047) B831047
theorem B1176743 : Blo 550806 1176743 := bstep (se 1 (by rfl) ⟨882557, by rfl⟩ : syracuseStep 1176743 = 1765115) B1765115
theorem B2356391 : Blo 550806 2356391 := bstep (se 1 (by rfl) ⟨1767293, by rfl⟩ : syracuseStep 2356391 = 3534587) B3534587
theorem B554151 : Blo 550806 554151 := bstep (se 1 (by rfl) ⟨415613, by rfl⟩ : syracuseStep 554151 = 831227) B831227
theorem B184251743 : Blo 550806 184251743 := bstep (se 1 (by rfl) ⟨138188807, by rfl⟩ : syracuseStep 184251743 = 276377615) B276377615
theorem B6747563 : Blo 550806 6747563 := bstep (se 1 (by rfl) ⟨5060672, by rfl⟩ : syracuseStep 6747563 = 10121345) B10121345
theorem B554599 : Blo 550806 554599 := bstep (se 1 (by rfl) ⟨415949, by rfl⟩ : syracuseStep 554599 = 831899) B831899
theorem B1242791 : Blo 550806 1242791 := bstep (se 1 (by rfl) ⟨932093, by rfl⟩ : syracuseStep 1242791 = 1864187) B1864187
theorem B1242971 : Blo 550806 1242971 := bstep (se 1 (by rfl) ⟨932228, by rfl⟩ : syracuseStep 1242971 = 1864457) B1864457
theorem B4716539 : Blo 550806 4716539 := bstep (se 1 (by rfl) ⟨3537404, by rfl⟩ : syracuseStep 4716539 = 7074809) B7074809
theorem B7075835 : Blo 550806 7075835 := bstep (se 1 (by rfl) ⟨5306876, by rfl⟩ : syracuseStep 7075835 = 10613753) B10613753
theorem B1308847 : Blo 550806 1308847 := bstep (se 1 (by rfl) ⟨981635, by rfl⟩ : syracuseStep 1308847 = 1963271) B1963271
theorem B1866023 : Blo 550806 1866023 := bstep (se 1 (by rfl) ⟨1399517, by rfl⟩ : syracuseStep 1866023 = 2799035) B2799035
theorem B1047019 : Blo 550806 1047019 := bstep (se 1 (by rfl) ⟨785264, by rfl⟩ : syracuseStep 1047019 = 1570529) B1570529
theorem B621535 : Blo 550806 621535 := bstep (se 1 (by rfl) ⟨466151, by rfl⟩ : syracuseStep 621535 = 932303) B932303
theorem B1571815 : Blo 550806 1571815 := bstep (se 1 (by rfl) ⟨1178861, by rfl⟩ : syracuseStep 1571815 = 2357723) B2357723
theorem B2358305 : Blo 550806 2358305 := bstep (se 2 (by rfl) ⟨884364, by rfl⟩ : syracuseStep 2358305 = 1768729) B1768729
theorem B4717601 : Blo 550806 4717601 := bstep (se 2 (by rfl) ⟨1769100, by rfl⟩ : syracuseStep 4717601 = 3538201) B3538201
theorem B9862337 : Blo 550806 9862337 := bstep (se 2 (by rfl) ⟨3698376, by rfl⟩ : syracuseStep 9862337 = 7396753) B7396753
theorem B1768691 : Blo 550806 1768691 := bstep (se 1 (by rfl) ⟨1326518, by rfl⟩ : syracuseStep 1768691 = 2653037) B2653037
theorem B2522603 : Blo 550806 2522603 := bstep (se 1 (by rfl) ⟨1891952, by rfl⟩ : syracuseStep 2522603 = 3783905) B3783905
theorem B622399 : Blo 550806 622399 := bstep (se 1 (by rfl) ⟨466799, by rfl⟩ : syracuseStep 622399 = 933599) B933599
theorem B4554947 : Blo 550806 4554947 := bstep (se 1 (by rfl) ⟨3416210, by rfl⟩ : syracuseStep 4554947 = 6832421) B6832421
theorem B622831 : Blo 550806 622831 := bstep (se 1 (by rfl) ⟨467123, by rfl⟩ : syracuseStep 622831 = 934247) B934247
theorem B1245743 : Blo 550806 1245743 := bstep (se 1 (by rfl) ⟨934307, by rfl⟩ : syracuseStep 1245743 = 1868615) B1868615
theorem B18187195 : Blo 550806 18187195 := bstep (se 1 (by rfl) ⟨13640396, by rfl⟩ : syracuseStep 18187195 = 27280793) B27280793
theorem B787639 : Blo 550806 787639 := bstep (se 1 (by rfl) ⟨590729, by rfl⟩ : syracuseStep 787639 = 1181459) B1181459
theorem B8947259 : Blo 550806 8947259 := bstep (se 1 (by rfl) ⟨6710444, by rfl⟩ : syracuseStep 8947259 = 13420889) B13420889
theorem B1246985 : Blo 550806 1246985 := bstep (se 2 (by rfl) ⟨467619, by rfl⟩ : syracuseStep 1246985 = 935239) B935239
theorem B1869587 : Blo 550806 1869587 := bstep (se 1 (by rfl) ⟨1402190, by rfl⟩ : syracuseStep 1869587 = 2804381) B2804381
theorem B7997449 : Blo 550806 7997449 := bstep (se 2 (by rfl) ⟨2999043, by rfl⟩ : syracuseStep 7997449 = 5998087) B5998087
theorem B349046909 : Blo 550806 349046909 := bstep (se 3 (by rfl) ⟨65446295, by rfl⟩ : syracuseStep 349046909 = 130892591) B130892591
theorem B1509715 : Blo 550806 1509715 := bstep (se 1 (by rfl) ⟨1132286, by rfl⟩ : syracuseStep 1509715 = 2264573) B2264573
theorem B1870451 : Blo 550806 1870451 := bstep (se 1 (by rfl) ⟨1402838, by rfl⟩ : syracuseStep 1870451 = 2805677) B2805677
theorem B5048999 : Blo 550806 5048999 := bstep (se 1 (by rfl) ⟨3786749, by rfl⟩ : syracuseStep 5048999 = 7573499) B7573499
theorem B1051355 : Blo 550806 1051355 := bstep (se 1 (by rfl) ⟨788516, by rfl⟩ : syracuseStep 1051355 = 1577033) B1577033
theorem B789211 : Blo 550806 789211 := bstep (se 1 (by rfl) ⟨591908, by rfl⟩ : syracuseStep 789211 = 1183817) B1183817
theorem B2362081 : Blo 550806 2362081 := bstep (se 2 (by rfl) ⟨885780, by rfl⟩ : syracuseStep 2362081 = 1771561) B1771561
theorem B1182433 : Blo 550806 1182433 := bstep (se 2 (by rfl) ⟨443412, by rfl⟩ : syracuseStep 1182433 = 886825) B886825
theorem B1051879 : Blo 550806 1051879 := bstep (se 1 (by rfl) ⟨788909, by rfl⟩ : syracuseStep 1051879 = 1577819) B1577819
theorem B1871531 : Blo 550806 1871531 := bstep (se 1 (by rfl) ⟨1403648, by rfl⟩ : syracuseStep 1871531 = 2807297) B2807297
theorem B1871585 : Blo 550806 1871585 := bstep (se 2 (by rfl) ⟨701844, by rfl⟩ : syracuseStep 1871585 = 1403689) B1403689
theorem B6295643 : Blo 550806 6295643 := bstep (se 1 (by rfl) ⟨4721732, by rfl⟩ : syracuseStep 6295643 = 9443465) B9443465
theorem B2101585 : Blo 550806 2101585 := bstep (se 2 (by rfl) ⟨788094, by rfl⟩ : syracuseStep 2101585 = 1576189) B1576189
theorem B2364011 : Blo 550806 2364011 := bstep (se 1 (by rfl) ⟨1773008, by rfl⟩ : syracuseStep 2364011 = 3546017) B3546017
theorem B2528111 : Blo 550806 2528111 := bstep (se 1 (by rfl) ⟨1896083, by rfl⟩ : syracuseStep 2528111 = 3792167) B3792167
theorem B2102345 : Blo 550806 2102345 := bstep (se 2 (by rfl) ⟨788379, by rfl⟩ : syracuseStep 2102345 = 1576759) B1576759
theorem B2102557 : Blo 550806 2102557 := bstep (se 3 (by rfl) ⟨394229, by rfl⟩ : syracuseStep 2102557 = 788459) B788459
theorem B5248543 : Blo 550806 5248543 := bstep (se 1 (by rfl) ⟨3936407, by rfl⟩ : syracuseStep 5248543 = 7872815) B7872815
theorem B2365787 : Blo 550806 2365787 := bstep (se 1 (by rfl) ⟨1774340, by rfl⟩ : syracuseStep 2365787 = 3548681) B3548681
theorem B4594427 : Blo 550806 4594427 := bstep (se 1 (by rfl) ⟨3445820, by rfl⟩ : syracuseStep 4594427 = 6891641) B6891641
theorem B826475 : Blo 550806 826475 := bstep (se 1 (by rfl) ⟨619856, by rfl⟩ : syracuseStep 826475 = 1239713) B1239713
theorem B826715 : Blo 550806 826715 := bstep (se 1 (by rfl) ⟨620036, by rfl⟩ : syracuseStep 826715 = 1240073) B1240073
theorem B826847 : Blo 550806 826847 := bstep (se 1 (by rfl) ⟨620135, by rfl⟩ : syracuseStep 826847 = 1240271) B1240271
theorem B2399851 : Blo 550806 2399851 := bstep (se 1 (by rfl) ⟨1799888, by rfl⟩ : syracuseStep 2399851 = 3599777) B3599777
theorem B827375 : Blo 550806 827375 := bstep (se 1 (by rfl) ⟨620531, by rfl⟩ : syracuseStep 827375 = 1241063) B1241063
theorem B2793527 : Blo 550806 2793527 := bstep (se 1 (by rfl) ⟨2095145, by rfl⟩ : syracuseStep 2793527 = 4190291) B4190291
theorem B827495 : Blo 550806 827495 := bstep (se 1 (by rfl) ⟨620621, by rfl⟩ : syracuseStep 827495 = 1241243) B1241243
theorem B827615 : Blo 550806 827615 := bstep (se 1 (by rfl) ⟨620711, by rfl⟩ : syracuseStep 827615 = 1241423) B1241423
theorem B1745129 : Blo 550806 1745129 := bstep (se 2 (by rfl) ⟨654423, by rfl⟩ : syracuseStep 1745129 = 1308847) B1308847
theorem B827627 : Blo 550806 827627 := bstep (se 1 (by rfl) ⟨620720, by rfl⟩ : syracuseStep 827627 = 1241441) B1241441
theorem B827675 : Blo 550806 827675 := bstep (se 1 (by rfl) ⟨620756, by rfl⟩ : syracuseStep 827675 = 1241513) B1241513
theorem B827687 : Blo 550806 827687 := bstep (se 1 (by rfl) ⟨620765, by rfl⟩ : syracuseStep 827687 = 1241531) B1241531
theorem B827879 : Blo 550806 827879 := bstep (se 1 (by rfl) ⟨620909, by rfl⟩ : syracuseStep 827879 = 1241819) B1241819
theorem B828059 : Blo 550806 828059 := bstep (se 1 (by rfl) ⟨621044, by rfl⟩ : syracuseStep 828059 = 1242089) B1242089
theorem B4498375 : Blo 550806 4498375 := bstep (se 1 (by rfl) ⟨3373781, by rfl⟩ : syracuseStep 4498375 = 6747563) B6747563
theorem B828527 : Blo 550806 828527 := bstep (se 1 (by rfl) ⟨621395, by rfl⟩ : syracuseStep 828527 = 1242791) B1242791
theorem B828647 : Blo 550806 828647 := bstep (se 1 (by rfl) ⟨621485, by rfl⟩ : syracuseStep 828647 = 1242971) B1242971
theorem B828713 : Blo 550806 828713 := bstep (se 2 (by rfl) ⟨310767, by rfl⟩ : syracuseStep 828713 = 621535) B621535
theorem B1123751 : Blo 550806 1123751 := bstep (se 1 (by rfl) ⟨842813, by rfl⟩ : syracuseStep 1123751 = 1685627) B1685627
theorem B4532203 : Blo 550806 4532203 := bstep (se 1 (by rfl) ⟨3399152, by rfl⟩ : syracuseStep 4532203 = 6798305) B6798305
theorem B600383 : Blo 550806 600383 := bstep (se 1 (by rfl) ⟨450287, by rfl⟩ : syracuseStep 600383 = 900575) B900575
theorem B1681735 : Blo 550806 1681735 := bstep (se 1 (by rfl) ⟨1261301, by rfl⟩ : syracuseStep 1681735 = 2522603) B2522603
theorem B829865 : Blo 550806 829865 := bstep (se 2 (by rfl) ⟨311199, by rfl⟩ : syracuseStep 829865 = 622399) B622399
theorem B3549707 : Blo 550806 3549707 := bstep (se 1 (by rfl) ⟨2662280, by rfl⟩ : syracuseStep 3549707 = 5324561) B5324561
theorem B2829167 : Blo 550806 2829167 := bstep (se 1 (by rfl) ⟨2121875, by rfl⟩ : syracuseStep 2829167 = 4243751) B4243751
theorem B830399 : Blo 550806 830399 := bstep (se 1 (by rfl) ⟨622799, by rfl⟩ : syracuseStep 830399 = 1245599) B1245599
theorem B2796767 : Blo 550806 2796767 := bstep (se 1 (by rfl) ⟨2097575, by rfl⟩ : syracuseStep 2796767 = 4195151) B4195151
theorem B2272607 : Blo 550806 2272607 := bstep (se 1 (by rfl) ⟨1704455, by rfl⟩ : syracuseStep 2272607 = 3408911) B3408911
theorem B4730345 : Blo 550806 4730345 := bstep (se 2 (by rfl) ⟨1773879, by rfl⟩ : syracuseStep 4730345 = 3547759) B3547759
theorem B3157481 : Blo 550806 3157481 := bstep (se 2 (by rfl) ⟨1184055, by rfl⟩ : syracuseStep 3157481 = 2368111) B2368111
theorem B831131 : Blo 550806 831131 := bstep (se 1 (by rfl) ⟨623348, by rfl⟩ : syracuseStep 831131 = 1246697) B1246697
theorem B798427 : Blo 550806 798427 := bstep (se 1 (by rfl) ⟨598820, by rfl⟩ : syracuseStep 798427 = 1197641) B1197641
theorem B3354371 : Blo 550806 3354371 := bstep (se 1 (by rfl) ⟨2515778, by rfl⟩ : syracuseStep 3354371 = 5031557) B5031557
theorem B831515 : Blo 550806 831515 := bstep (se 1 (by rfl) ⟨623636, by rfl⟩ : syracuseStep 831515 = 1247273) B1247273
theorem B5976251 : Blo 550806 5976251 := bstep (se 1 (by rfl) ⟨4482188, by rfl⟩ : syracuseStep 5976251 = 8964377) B8964377
theorem B930089 : Blo 550806 930089 := bstep (se 2 (by rfl) ⟨348783, by rfl⟩ : syracuseStep 930089 = 697567) B697567
theorem B700751 : Blo 550806 700751 := bstep (se 1 (by rfl) ⟨525563, by rfl⟩ : syracuseStep 700751 = 1051127) B1051127
theorem B831935 : Blo 550806 831935 := bstep (se 1 (by rfl) ⟨623951, by rfl⟩ : syracuseStep 831935 = 1247903) B1247903
theorem B9417221 : Blo 550806 9417221 := bstep (se 4 (by rfl) ⟨882864, by rfl⟩ : syracuseStep 9417221 = 1765729) B1765729
theorem B996295 : Blo 550806 996295 := bstep (se 1 (by rfl) ⟨747221, by rfl⟩ : syracuseStep 996295 = 1494443) B1494443
theorem B5321791 : Blo 550806 5321791 := bstep (se 1 (by rfl) ⟨3991343, by rfl⟩ : syracuseStep 5321791 = 7982687) B7982687
theorem B15938855 : Blo 550806 15938855 := bstep (se 1 (by rfl) ⟨11954141, by rfl⟩ : syracuseStep 15938855 = 23908283) B23908283
theorem B931817 : Blo 550806 931817 := bstep (se 2 (by rfl) ⟨349431, by rfl⟩ : syracuseStep 931817 = 698863) B698863
theorem B6076417 : Blo 550806 6076417 := bstep (se 2 (by rfl) ⟨2278656, by rfl⟩ : syracuseStep 6076417 = 4557313) B4557313
theorem B2242991 : Blo 550806 2242991 := bstep (se 1 (by rfl) ⟨1682243, by rfl⟩ : syracuseStep 2242991 = 3364487) B3364487
theorem B932647 : Blo 550806 932647 := bstep (se 1 (by rfl) ⟨699485, by rfl⟩ : syracuseStep 932647 = 1398971) B1398971
theorem B933275 : Blo 550806 933275 := bstep (se 1 (by rfl) ⟨699956, by rfl⟩ : syracuseStep 933275 = 1399913) B1399913
theorem B2244029 : Blo 550806 2244029 := bstep (se 3 (by rfl) ⟨420755, by rfl⟩ : syracuseStep 2244029 = 841511) B841511
theorem B2244743 : Blo 550806 2244743 := bstep (se 1 (by rfl) ⟨1683557, by rfl⟩ : syracuseStep 2244743 = 3367115) B3367115
theorem B934031 : Blo 550806 934031 := bstep (se 1 (by rfl) ⟨700523, by rfl⟩ : syracuseStep 934031 = 1401047) B1401047
theorem B934139 : Blo 550806 934139 := bstep (se 1 (by rfl) ⟨700604, by rfl⟩ : syracuseStep 934139 = 1401209) B1401209
theorem B1491295 : Blo 550806 1491295 := bstep (se 1 (by rfl) ⟨1118471, by rfl⟩ : syracuseStep 1491295 = 2236943) B2236943
theorem B15287723 : Blo 550806 15287723 := bstep (se 1 (by rfl) ⟨11465792, by rfl⟩ : syracuseStep 15287723 = 22931585) B22931585
theorem B1328719 : Blo 550806 1328719 := bstep (se 1 (by rfl) ⟨996539, by rfl⟩ : syracuseStep 1328719 = 1993079) B1993079
theorem B1394779 : Blo 550806 1394779 := bstep (se 1 (by rfl) ⟨1046084, by rfl⟩ : syracuseStep 1394779 = 2092169) B2092169
theorem B1493599 : Blo 550806 1493599 := bstep (se 1 (by rfl) ⟨1120199, by rfl⟩ : syracuseStep 1493599 = 2240399) B2240399
theorem B1396025 : Blo 550806 1396025 := bstep (se 2 (by rfl) ⟨523509, by rfl⟩ : syracuseStep 1396025 = 1047019) B1047019
theorem B122834495 : Blo 550806 122834495 := bstep (se 1 (by rfl) ⟨92125871, by rfl⟩ : syracuseStep 122834495 = 184251743) B184251743
theorem B6574891 : Blo 550806 6574891 := bstep (se 1 (by rfl) ⟨4931168, by rfl⟩ : syracuseStep 6574891 = 9862337) B9862337
theorem B1332217 : Blo 550806 1332217 := bstep (se 2 (by rfl) ⟨499581, by rfl⟩ : syracuseStep 1332217 = 999163) B999163
theorem B709799 : Blo 550806 709799 := bstep (se 1 (by rfl) ⟨532349, by rfl⟩ : syracuseStep 709799 = 1064699) B1064699
theorem B1791487 : Blo 550806 1791487 := bstep (se 1 (by rfl) ⟨1343615, by rfl⟩ : syracuseStep 1791487 = 2687231) B2687231
theorem B4773491 : Blo 550806 4773491 := bstep (se 1 (by rfl) ⟨3580118, by rfl⟩ : syracuseStep 4773491 = 7160237) B7160237
theorem B7067837 : Blo 550806 7067837 := bstep (se 3 (by rfl) ⟨1325219, by rfl⟩ : syracuseStep 7067837 = 2650439) B2650439
theorem B5988143 : Blo 550806 5988143 := bstep (se 1 (by rfl) ⟨4491107, by rfl⟩ : syracuseStep 5988143 = 8982215) B8982215
theorem B1892747 : Blo 550806 1892747 := bstep (se 1 (by rfl) ⟨1419560, by rfl⟩ : syracuseStep 1892747 = 2839121) B2839121
theorem B1401259 : Blo 550806 1401259 := bstep (se 1 (by rfl) ⟨1050944, by rfl⟩ : syracuseStep 1401259 = 2101889) B2101889
theorem B1860839 : Blo 550806 1860839 := bstep (se 1 (by rfl) ⟨1395629, by rfl⟩ : syracuseStep 1860839 = 2791259) B2791259
theorem B1402343 : Blo 550806 1402343 := bstep (se 1 (by rfl) ⟨1051757, by rfl⟩ : syracuseStep 1402343 = 2103515) B2103515
theorem B4253597 : Blo 550806 4253597 := bstep (se 3 (by rfl) ⟨797549, by rfl⟩ : syracuseStep 4253597 = 1595099) B1595099
theorem B550907 : Blo 550806 550907 := bstep (se 1 (by rfl) ⟨413180, by rfl⟩ : syracuseStep 550907 = 826361) B826361
theorem B3139667 : Blo 550806 3139667 := bstep (se 1 (by rfl) ⟨2354750, by rfl⟩ : syracuseStep 3139667 = 4709501) B4709501
theorem B34007303 : Blo 550806 34007303 := bstep (se 1 (by rfl) ⟨25505477, by rfl⟩ : syracuseStep 34007303 = 51010955) B51010955
theorem B551327 : Blo 550806 551327 := bstep (se 1 (by rfl) ⟨413495, by rfl⟩ : syracuseStep 551327 = 826991) B826991
theorem B551407 : Blo 550806 551407 := bstep (se 1 (by rfl) ⟨413555, by rfl⟩ : syracuseStep 551407 = 827111) B827111
theorem B50981363 : Blo 550806 50981363 := bstep (se 1 (by rfl) ⟨38236022, by rfl⟩ : syracuseStep 50981363 = 76472045) B76472045
theorem B4254239 : Blo 550806 4254239 := bstep (se 1 (by rfl) ⟨3190679, by rfl⟩ : syracuseStep 4254239 = 6381359) B6381359
theorem B551591 : Blo 550806 551591 := bstep (se 1 (by rfl) ⟨413693, by rfl⟩ : syracuseStep 551591 = 827387) B827387
theorem B551631 : Blo 550806 551631 := bstep (se 1 (by rfl) ⟨413723, by rfl⟩ : syracuseStep 551631 = 827447) B827447
theorem B551711 : Blo 550806 551711 := bstep (se 1 (by rfl) ⟨413783, by rfl⟩ : syracuseStep 551711 = 827567) B827567
theorem B1993511 : Blo 550806 1993511 := bstep (se 1 (by rfl) ⟨1495133, by rfl⟩ : syracuseStep 1993511 = 2990267) B2990267
theorem B551847 : Blo 550806 551847 := bstep (se 1 (by rfl) ⟨413885, by rfl⟩ : syracuseStep 551847 = 827771) B827771
theorem B1240019 : Blo 550806 1240019 := bstep (se 1 (by rfl) ⟨930014, by rfl⟩ : syracuseStep 1240019 = 1860029) B1860029
theorem B551963 : Blo 550806 551963 := bstep (se 1 (by rfl) ⟨413972, by rfl⟩ : syracuseStep 551963 = 827945) B827945
theorem B552027 : Blo 550806 552027 := bstep (se 1 (by rfl) ⟨414020, by rfl⟩ : syracuseStep 552027 = 828041) B828041
theorem B552167 : Blo 550806 552167 := bstep (se 1 (by rfl) ⟨414125, by rfl⟩ : syracuseStep 552167 = 828251) B828251
theorem B552191 : Blo 550806 552191 := bstep (se 1 (by rfl) ⟨414143, by rfl⟩ : syracuseStep 552191 = 828287) B828287
theorem B552239 : Blo 550806 552239 := bstep (se 1 (by rfl) ⟨414179, by rfl⟩ : syracuseStep 552239 = 828359) B828359
theorem B552383 : Blo 550806 552383 := bstep (se 1 (by rfl) ⟨414287, by rfl⟩ : syracuseStep 552383 = 828575) B828575
theorem B9465335 : Blo 550806 9465335 := bstep (se 1 (by rfl) ⟨7099001, by rfl⟩ : syracuseStep 9465335 = 14198003) B14198003
theorem B552479 : Blo 550806 552479 := bstep (se 1 (by rfl) ⟨414359, by rfl⟩ : syracuseStep 552479 = 828719) B828719
theorem B552607 : Blo 550806 552607 := bstep (se 1 (by rfl) ⟨414455, by rfl⟩ : syracuseStep 552607 = 828911) B828911
theorem B552615 : Blo 550806 552615 := bstep (se 1 (by rfl) ⟨414461, by rfl⟩ : syracuseStep 552615 = 828923) B828923
theorem B552639 : Blo 550806 552639 := bstep (se 1 (by rfl) ⟨414479, by rfl⟩ : syracuseStep 552639 = 828959) B828959
theorem B552735 : Blo 550806 552735 := bstep (se 1 (by rfl) ⟨414551, by rfl⟩ : syracuseStep 552735 = 829103) B829103
theorem B4484945 : Blo 550806 4484945 := bstep (se 2 (by rfl) ⟨1681854, by rfl⟩ : syracuseStep 4484945 = 3363709) B3363709
theorem B14708567 : Blo 550806 14708567 := bstep (se 1 (by rfl) ⟨11031425, by rfl⟩ : syracuseStep 14708567 = 22062851) B22062851
theorem B552795 : Blo 550806 552795 := bstep (se 1 (by rfl) ⟨414596, by rfl⟩ : syracuseStep 552795 = 829193) B829193
theorem B552815 : Blo 550806 552815 := bstep (se 1 (by rfl) ⟨414611, by rfl⟩ : syracuseStep 552815 = 829223) B829223
theorem B16969661 : Blo 550806 16969661 := bstep (se 3 (by rfl) ⟨3181811, by rfl⟩ : syracuseStep 16969661 = 6363623) B6363623
theorem B2355263 : Blo 550806 2355263 := bstep (se 1 (by rfl) ⟨1766447, by rfl⟩ : syracuseStep 2355263 = 3532895) B3532895
theorem B749675 : Blo 550806 749675 := bstep (se 1 (by rfl) ⟨562256, by rfl⟩ : syracuseStep 749675 = 1124513) B1124513
theorem B7958699 : Blo 550806 7958699 := bstep (se 1 (by rfl) ⟨5969024, by rfl⟩ : syracuseStep 7958699 = 11938049) B11938049
theorem B553215 : Blo 550806 553215 := bstep (se 1 (by rfl) ⟨414911, by rfl⟩ : syracuseStep 553215 = 829823) B829823
theorem B14119271 : Blo 550806 14119271 := bstep (se 1 (by rfl) ⟨10589453, by rfl⟩ : syracuseStep 14119271 = 21178907) B21178907
theorem B553375 : Blo 550806 553375 := bstep (se 1 (by rfl) ⟨415031, by rfl⟩ : syracuseStep 553375 = 830063) B830063
theorem B1569287 : Blo 550806 1569287 := bstep (se 1 (by rfl) ⟨1176965, by rfl⟩ : syracuseStep 1569287 = 2353931) B2353931
theorem B553519 : Blo 550806 553519 := bstep (se 1 (by rfl) ⟨415139, by rfl⟩ : syracuseStep 553519 = 830279) B830279
theorem B553919 : Blo 550806 553919 := bstep (se 1 (by rfl) ⟨415439, by rfl⟩ : syracuseStep 553919 = 830879) B830879
theorem B1864673 : Blo 550806 1864673 := bstep (se 2 (by rfl) ⟨699252, by rfl⟩ : syracuseStep 1864673 = 1398505) B1398505
theorem B2356219 : Blo 550806 2356219 := bstep (se 1 (by rfl) ⟨1767164, by rfl⟩ : syracuseStep 2356219 = 3534329) B3534329
theorem B554095 : Blo 550806 554095 := bstep (se 1 (by rfl) ⟨415571, by rfl⟩ : syracuseStep 554095 = 831143) B831143
theorem B554111 : Blo 550806 554111 := bstep (se 1 (by rfl) ⟨415583, by rfl⟩ : syracuseStep 554111 = 831167) B831167
theorem B554175 : Blo 550806 554175 := bstep (se 1 (by rfl) ⟨415631, by rfl⟩ : syracuseStep 554175 = 831263) B831263
theorem B554367 : Blo 550806 554367 := bstep (se 1 (by rfl) ⟨415775, by rfl⟩ : syracuseStep 554367 = 831551) B831551
theorem B5043667 : Blo 550806 5043667 := bstep (se 1 (by rfl) ⟨3782750, by rfl⟩ : syracuseStep 5043667 = 7565501) B7565501
theorem B1865213 : Blo 550806 1865213 := bstep (se 3 (by rfl) ⟨349727, by rfl⟩ : syracuseStep 1865213 = 699455) B699455
theorem B554495 : Blo 550806 554495 := bstep (se 1 (by rfl) ⟨415871, by rfl⟩ : syracuseStep 554495 = 831743) B831743
theorem B554523 : Blo 550806 554523 := bstep (se 1 (by rfl) ⟨415892, by rfl⟩ : syracuseStep 554523 = 831785) B831785
theorem B554703 : Blo 550806 554703 := bstep (se 1 (by rfl) ⟨416027, by rfl⟩ : syracuseStep 554703 = 832055) B832055
theorem B2651977 : Blo 550806 2651977 := bstep (se 2 (by rfl) ⟨994491, by rfl⟩ : syracuseStep 2651977 = 1988983) B1988983
theorem B784495 : Blo 550806 784495 := bstep (se 1 (by rfl) ⟨588371, by rfl⟩ : syracuseStep 784495 = 1176743) B1176743
theorem B1570927 : Blo 550806 1570927 := bstep (se 1 (by rfl) ⟨1178195, by rfl⟩ : syracuseStep 1570927 = 2356391) B2356391
theorem B5994809 : Blo 550806 5994809 := bstep (se 2 (by rfl) ⟨2248053, by rfl⟩ : syracuseStep 5994809 = 4496107) B4496107
theorem B7109207 : Blo 550806 7109207 := bstep (se 1 (by rfl) ⟨5331905, by rfl⟩ : syracuseStep 7109207 = 10663811) B10663811
theorem B2095753 : Blo 550806 2095753 := bstep (se 2 (by rfl) ⟨785907, by rfl⟩ : syracuseStep 2095753 = 1571815) B1571815
theorem B3144359 : Blo 550806 3144359 := bstep (se 1 (by rfl) ⟨2358269, by rfl⟩ : syracuseStep 3144359 = 4716539) B4716539
theorem B4717223 : Blo 550806 4717223 := bstep (se 1 (by rfl) ⟨3537917, by rfl⟩ : syracuseStep 4717223 = 7075835) B7075835
theorem B1244015 : Blo 550806 1244015 := bstep (se 1 (by rfl) ⟨933011, by rfl⟩ : syracuseStep 1244015 = 1866023) B1866023
theorem B1866779 : Blo 550806 1866779 := bstep (se 1 (by rfl) ⟨1400084, by rfl⟩ : syracuseStep 1866779 = 2800169) B2800169
theorem B232815779 : Blo 550806 232815779 := bstep (se 1 (by rfl) ⟨174611834, by rfl⟩ : syracuseStep 232815779 = 349223669) B349223669
theorem B1572203 : Blo 550806 1572203 := bstep (se 1 (by rfl) ⟨1179152, by rfl⟩ : syracuseStep 1572203 = 2358305) B2358305
theorem B3145067 : Blo 550806 3145067 := bstep (se 1 (by rfl) ⟨2358800, by rfl⟩ : syracuseStep 3145067 = 4717601) B4717601
theorem B1179127 : Blo 550806 1179127 := bstep (se 1 (by rfl) ⟨884345, by rfl⟩ : syracuseStep 1179127 = 1768691) B1768691
theorem B1867751 : Blo 550806 1867751 := bstep (se 1 (by rfl) ⟨1400813, by rfl⟩ : syracuseStep 1867751 = 2801627) B2801627
theorem B622687 : Blo 550806 622687 := bstep (se 1 (by rfl) ⟨467015, by rfl⟩ : syracuseStep 622687 = 934031) B934031
theorem B622759 : Blo 550806 622759 := bstep (se 1 (by rfl) ⟨467069, by rfl⟩ : syracuseStep 622759 = 934139) B934139
theorem B1999133 : Blo 550806 1999133 := bstep (se 3 (by rfl) ⟨374837, by rfl⟩ : syracuseStep 1999133 = 749675) B749675
theorem B1868345 : Blo 550806 1868345 := bstep (se 2 (by rfl) ⟨700629, by rfl⟩ : syracuseStep 1868345 = 1401259) B1401259
theorem B4653677 : Blo 550806 4653677 := bstep (se 3 (by rfl) ⟨872564, by rfl⟩ : syracuseStep 4653677 = 1745129) B1745129
theorem B1868669 : Blo 550806 1868669 := bstep (se 3 (by rfl) ⟨350375, by rfl⟩ : syracuseStep 1868669 = 700751) B700751
theorem B10191815 : Blo 550806 10191815 := bstep (se 1 (by rfl) ⟨7643861, by rfl⟩ : syracuseStep 10191815 = 15287723) B15287723
theorem B5964839 : Blo 550806 5964839 := bstep (se 1 (by rfl) ⟨4473629, by rfl⟩ : syracuseStep 5964839 = 8947259) B8947259
theorem B1246391 : Blo 550806 1246391 := bstep (se 1 (by rfl) ⟨934793, by rfl⟩ : syracuseStep 1246391 = 1869587) B1869587
theorem B24249593 : Blo 550806 24249593 := bstep (se 2 (by rfl) ⟨9093597, by rfl⟩ : syracuseStep 24249593 = 18187195) B18187195
theorem B5997833 : Blo 550806 5997833 := bstep (se 2 (by rfl) ⟨2249187, by rfl⟩ : syracuseStep 5997833 = 4498375) B4498375
theorem B1050185 : Blo 550806 1050185 := bstep (se 2 (by rfl) ⟨393819, by rfl⟩ : syracuseStep 1050185 = 787639) B787639
theorem B7571189 : Blo 550806 7571189 := bstep (se 5 (by rfl) ⟨354899, by rfl⟩ : syracuseStep 7571189 = 709799) B709799
theorem B1246967 : Blo 550806 1246967 := bstep (se 1 (by rfl) ⟨935225, by rfl⟩ : syracuseStep 1246967 = 1870451) B1870451
theorem B1771625 : Blo 550806 1771625 := bstep (se 2 (by rfl) ⟨664359, by rfl⟩ : syracuseStep 1771625 = 1328719) B1328719
theorem B81889663 : Blo 550806 81889663 := bstep (se 1 (by rfl) ⟨61417247, by rfl⟩ : syracuseStep 81889663 = 122834495) B122834495
theorem B1247687 : Blo 550806 1247687 := bstep (se 1 (by rfl) ⟨935765, by rfl⟩ : syracuseStep 1247687 = 1871531) B1871531
theorem B1247723 : Blo 550806 1247723 := bstep (se 1 (by rfl) ⟨935792, by rfl⟩ : syracuseStep 1247723 = 1871585) B1871585
theorem B4197095 : Blo 550806 4197095 := bstep (se 1 (by rfl) ⟨3147821, by rfl⟩ : syracuseStep 4197095 = 6295643) B6295643
theorem B1576007 : Blo 550806 1576007 := bstep (se 1 (by rfl) ⟨1182005, by rfl⟩ : syracuseStep 1576007 = 2364011) B2364011
theorem B1052281 : Blo 550806 1052281 := bstep (se 2 (by rfl) ⟨394605, by rfl⟩ : syracuseStep 1052281 = 789211) B789211
theorem B3149441 : Blo 550806 3149441 := bstep (se 2 (by rfl) ⟨1181040, by rfl⟩ : syracuseStep 3149441 = 2362081) B2362081
theorem B1576577 : Blo 550806 1576577 := bstep (se 2 (by rfl) ⟨591216, by rfl⟩ : syracuseStep 1576577 = 1182433) B1182433
theorem B3182327 : Blo 550806 3182327 := bstep (se 1 (by rfl) ⟨2386745, by rfl⟩ : syracuseStep 3182327 = 4773491) B4773491
theorem B1776289 : Blo 550806 1776289 := bstep (se 2 (by rfl) ⟨666108, by rfl⟩ : syracuseStep 1776289 = 1332217) B1332217
theorem B11344637 : Blo 550806 11344637 := bstep (se 3 (by rfl) ⟨2127119, by rfl⟩ : syracuseStep 11344637 = 4254239) B4254239
theorem B33987575 : Blo 550806 33987575 := bstep (se 1 (by rfl) ⟨25490681, by rfl⟩ : syracuseStep 33987575 = 50981363) B50981363
theorem B2366471 : Blo 550806 2366471 := bstep (se 1 (by rfl) ⟨1774853, by rfl⟩ : syracuseStep 2366471 = 3549707) B3549707
theorem B6724889 : Blo 550806 6724889 := bstep (se 2 (by rfl) ⟨2521833, by rfl⟩ : syracuseStep 6724889 = 5043667) B5043667
theorem B826679 : Blo 550806 826679 := bstep (se 1 (by rfl) ⟨620009, by rfl⟩ : syracuseStep 826679 = 1240019) B1240019
theorem B5316029 : Blo 550806 5316029 := bstep (se 3 (by rfl) ⟨996755, by rfl⟩ : syracuseStep 5316029 = 1993511) B1993511
theorem B1515071 : Blo 550806 1515071 := bstep (se 1 (by rfl) ⟨1136303, by rfl⟩ : syracuseStep 1515071 = 2272607) B2272607
theorem B3153563 : Blo 550806 3153563 := bstep (se 1 (by rfl) ⟨2365172, by rfl⟩ : syracuseStep 3153563 = 4730345) B4730345
theorem B2104987 : Blo 550806 2104987 := bstep (se 1 (by rfl) ⟨1578740, by rfl⟩ : syracuseStep 2104987 = 3157481) B3157481
theorem B2236247 : Blo 550806 2236247 := bstep (se 1 (by rfl) ⟨1677185, by rfl⟩ : syracuseStep 2236247 = 3354371) B3354371
theorem B2989963 : Blo 550806 2989963 := bstep (se 1 (by rfl) ⟨2242472, by rfl⟩ : syracuseStep 2989963 = 4484945) B4484945
theorem B9805711 : Blo 550806 9805711 := bstep (se 1 (by rfl) ⟨7354283, by rfl⟩ : syracuseStep 9805711 = 14708567) B14708567
theorem B11313107 : Blo 550806 11313107 := bstep (se 1 (by rfl) ⟨8484830, by rfl⟩ : syracuseStep 11313107 = 16969661) B16969661
theorem B8101889 : Blo 550806 8101889 := bstep (se 2 (by rfl) ⟨3038208, by rfl⟩ : syracuseStep 8101889 = 6076417) B6076417
theorem B9412847 : Blo 550806 9412847 := bstep (se 1 (by rfl) ⟨7059635, by rfl⟩ : syracuseStep 9412847 = 14119271) B14119271
theorem B2794337 : Blo 550806 2794337 := bstep (se 2 (by rfl) ⟨1047876, by rfl⟩ : syracuseStep 2794337 = 2095753) B2095753
theorem B10625903 : Blo 550806 10625903 := bstep (se 1 (by rfl) ⟨7969427, by rfl⟩ : syracuseStep 10625903 = 15938855) B15938855
theorem B829343 : Blo 550806 829343 := bstep (se 1 (by rfl) ⟨622007, by rfl⟩ : syracuseStep 829343 = 1244015) B1244015
theorem B830441 : Blo 550806 830441 := bstep (se 2 (by rfl) ⟨311415, by rfl⟩ : syracuseStep 830441 = 622831) B622831
theorem B830495 : Blo 550806 830495 := bstep (se 1 (by rfl) ⟨622871, by rfl⟩ : syracuseStep 830495 = 1245743) B1245743
theorem B831323 : Blo 550806 831323 := bstep (se 1 (by rfl) ⟨623492, by rfl⟩ : syracuseStep 831323 = 1246985) B1246985
theorem B232697939 : Blo 550806 232697939 := bstep (se 1 (by rfl) ⟨174523454, by rfl⟩ : syracuseStep 232697939 = 349046909) B349046909
theorem B700903 : Blo 550806 700903 := bstep (se 1 (by rfl) ⟨525677, by rfl⟩ : syracuseStep 700903 = 1051355) B1051355
theorem B930683 : Blo 550806 930683 := bstep (se 1 (by rfl) ⟨698012, by rfl⟩ : syracuseStep 930683 = 1396025) B1396025
theorem B6042937 : Blo 550806 6042937 := bstep (se 2 (by rfl) ⟨2266101, by rfl⟩ : syracuseStep 6042937 = 4532203) B4532203
theorem B10663265 : Blo 550806 10663265 := bstep (se 2 (by rfl) ⟨3998724, by rfl⟩ : syracuseStep 10663265 = 7997449) B7997449
theorem B2242313 : Blo 550806 2242313 := bstep (se 2 (by rfl) ⟨840867, by rfl⟩ : syracuseStep 2242313 = 1681735) B1681735
theorem B2012953 : Blo 550806 2012953 := bstep (se 2 (by rfl) ⟨754857, by rfl⟩ : syracuseStep 2012953 = 1509715) B1509715
theorem B1685407 : Blo 550806 1685407 := bstep (se 1 (by rfl) ⟨1264055, by rfl⟩ : syracuseStep 1685407 = 2528111) B2528111
theorem B2996669 : Blo 550806 2996669 := bstep (se 3 (by rfl) ⟨561875, by rfl⟩ : syracuseStep 2996669 = 1123751) B1123751
theorem B3062951 : Blo 550806 3062951 := bstep (se 1 (by rfl) ⟨2297213, by rfl⟩ : syracuseStep 3062951 = 4594427) B4594427
theorem B1064569 : Blo 550806 1064569 := bstep (se 2 (by rfl) ⟨399213, by rfl⟩ : syracuseStep 1064569 = 798427) B798427
theorem B1261831 : Blo 550806 1261831 := bstep (se 1 (by rfl) ⟨946373, by rfl⟩ : syracuseStep 1261831 = 1892747) B1892747
theorem B2802113 : Blo 550806 2802113 := bstep (se 2 (by rfl) ⟨1050792, by rfl⟩ : syracuseStep 2802113 = 2101585) B2101585
theorem B6308765 : Blo 550806 6308765 := bstep (se 3 (by rfl) ⟨1182893, by rfl⟩ : syracuseStep 6308765 = 2365787) B2365787
theorem B934895 : Blo 550806 934895 := bstep (se 1 (by rfl) ⟨701171, by rfl⟩ : syracuseStep 934895 = 1402343) B1402343
theorem B8766521 : Blo 550806 8766521 := bstep (se 2 (by rfl) ⟨3287445, by rfl⟩ : syracuseStep 8766521 = 6574891) B6574891
theorem B5981309 : Blo 550806 5981309 := bstep (se 3 (by rfl) ⟨1121495, by rfl⟩ : syracuseStep 5981309 = 2242991) B2242991
theorem B1328393 : Blo 550806 1328393 := bstep (se 2 (by rfl) ⟨498147, by rfl⟩ : syracuseStep 1328393 = 996295) B996295
theorem B2835731 : Blo 550806 2835731 := bstep (se 1 (by rfl) ⟨2126798, by rfl⟩ : syracuseStep 2835731 = 4253597) B4253597
theorem B7095721 : Blo 550806 7095721 := bstep (se 2 (by rfl) ⟨2660895, by rfl⟩ : syracuseStep 7095721 = 5321791) B5321791
theorem B2803409 : Blo 550806 2803409 := bstep (se 2 (by rfl) ⟨1051278, by rfl⟩ : syracuseStep 2803409 = 2102557) B2102557
theorem B1886111 : Blo 550806 1886111 := bstep (se 1 (by rfl) ⟨1414583, by rfl⟩ : syracuseStep 1886111 = 2829167) B2829167
theorem B6998057 : Blo 550806 6998057 := bstep (se 2 (by rfl) ⟨2624271, by rfl⟩ : syracuseStep 6998057 = 5248543) B5248543
theorem B6310223 : Blo 550806 6310223 := bstep (se 1 (by rfl) ⟨4732667, by rfl⟩ : syracuseStep 6310223 = 9465335) B9465335
theorem B3984167 : Blo 550806 3984167 := bstep (se 1 (by rfl) ⟨2988125, by rfl⟩ : syracuseStep 3984167 = 5976251) B5976251
theorem B6278147 : Blo 550806 6278147 := bstep (se 1 (by rfl) ⟨4708610, by rfl⟩ : syracuseStep 6278147 = 9417221) B9417221
theorem B12799205 : Blo 550806 12799205 := bstep (se 4 (by rfl) ⟨1199925, by rfl⟩ : syracuseStep 12799205 = 2399851) B2399851
theorem B5984077 : Blo 550806 5984077 := bstep (se 3 (by rfl) ⟨1122014, by rfl⟩ : syracuseStep 5984077 = 2244029) B2244029
theorem B4739471 : Blo 550806 4739471 := bstep (se 1 (by rfl) ⟨3554603, by rfl⟩ : syracuseStep 4739471 = 7109207) B7109207
theorem B155210519 : Blo 550806 155210519 := bstep (se 1 (by rfl) ⟨116407889, by rfl⟩ : syracuseStep 155210519 = 232815779) B232815779
theorem B1496495 : Blo 550806 1496495 := bstep (se 1 (by rfl) ⟨1122371, by rfl⟩ : syracuseStep 1496495 = 2244743) B2244743
theorem B3036631 : Blo 550806 3036631 := bstep (se 1 (by rfl) ⟨2277473, by rfl⟩ : syracuseStep 3036631 = 4554947) B4554947
theorem B1988393 : Blo 550806 1988393 := bstep (se 2 (by rfl) ⟨745647, by rfl⟩ : syracuseStep 1988393 = 1491295) B1491295
theorem B4183973 : Blo 550806 4183973 := bstep (se 4 (by rfl) ⟨392247, by rfl⟩ : syracuseStep 4183973 = 784495) B784495
theorem B3365999 : Blo 550806 3365999 := bstep (se 1 (by rfl) ⟨2524499, by rfl⟩ : syracuseStep 3365999 = 5048999) B5048999
theorem B1859705 : Blo 550806 1859705 := bstep (se 2 (by rfl) ⟨697389, by rfl⟩ : syracuseStep 1859705 = 1394779) B1394779
theorem B1401563 : Blo 550806 1401563 := bstep (se 1 (by rfl) ⟨1051172, by rfl⟩ : syracuseStep 1401563 = 2102345) B2102345
theorem B1991465 : Blo 550806 1991465 := bstep (se 2 (by rfl) ⟨746799, by rfl⟩ : syracuseStep 1991465 = 1493599) B1493599
theorem B4711891 : Blo 550806 4711891 := bstep (se 1 (by rfl) ⟨3533918, by rfl⟩ : syracuseStep 4711891 = 7067837) B7067837
theorem B1402505 : Blo 550806 1402505 := bstep (se 2 (by rfl) ⟨525939, by rfl⟩ : syracuseStep 1402505 = 1051879) B1051879
theorem B550983 : Blo 550806 550983 := bstep (se 1 (by rfl) ⟨413237, by rfl⟩ : syracuseStep 550983 = 826475) B826475
theorem B551143 : Blo 550806 551143 := bstep (se 1 (by rfl) ⟨413357, by rfl⟩ : syracuseStep 551143 = 826715) B826715
theorem B551231 : Blo 550806 551231 := bstep (se 1 (by rfl) ⟨413423, by rfl⟩ : syracuseStep 551231 = 826847) B826847
theorem B3992095 : Blo 550806 3992095 := bstep (se 1 (by rfl) ⟨2994071, by rfl⟩ : syracuseStep 3992095 = 5988143) B5988143
theorem B551583 : Blo 550806 551583 := bstep (se 1 (by rfl) ⟨413687, by rfl⟩ : syracuseStep 551583 = 827375) B827375
theorem B1862351 : Blo 550806 1862351 := bstep (se 1 (by rfl) ⟨1396763, by rfl⟩ : syracuseStep 1862351 = 2793527) B2793527
theorem B551663 : Blo 550806 551663 := bstep (se 1 (by rfl) ⟨413747, by rfl⟩ : syracuseStep 551663 = 827495) B827495
theorem B551743 : Blo 550806 551743 := bstep (se 1 (by rfl) ⟨413807, by rfl⟩ : syracuseStep 551743 = 827615) B827615
theorem B551751 : Blo 550806 551751 := bstep (se 1 (by rfl) ⟨413813, by rfl⟩ : syracuseStep 551751 = 827627) B827627
theorem B551783 : Blo 550806 551783 := bstep (se 1 (by rfl) ⟨413837, by rfl⟩ : syracuseStep 551783 = 827675) B827675
theorem B551791 : Blo 550806 551791 := bstep (se 1 (by rfl) ⟨413843, by rfl⟩ : syracuseStep 551791 = 827687) B827687
theorem B551919 : Blo 550806 551919 := bstep (se 1 (by rfl) ⟨413939, by rfl⟩ : syracuseStep 551919 = 827879) B827879
theorem B552039 : Blo 550806 552039 := bstep (se 1 (by rfl) ⟨414029, by rfl⟩ : syracuseStep 552039 = 828059) B828059
theorem B552351 : Blo 550806 552351 := bstep (se 1 (by rfl) ⟨414263, by rfl⟩ : syracuseStep 552351 = 828527) B828527
theorem B1240559 : Blo 550806 1240559 := bstep (se 1 (by rfl) ⟨930419, by rfl⟩ : syracuseStep 1240559 = 1860839) B1860839
theorem B552431 : Blo 550806 552431 := bstep (se 1 (by rfl) ⟨414323, by rfl⟩ : syracuseStep 552431 = 828647) B828647
theorem B1601021 : Blo 550806 1601021 := bstep (se 3 (by rfl) ⟨300191, by rfl⟩ : syracuseStep 1601021 = 600383) B600383
theorem B552475 : Blo 550806 552475 := bstep (se 1 (by rfl) ⟨414356, by rfl⟩ : syracuseStep 552475 = 828713) B828713
theorem B3141625 : Blo 550806 3141625 := bstep (se 2 (by rfl) ⟨1178109, by rfl⟩ : syracuseStep 3141625 = 2356219) B2356219
theorem B2093111 : Blo 550806 2093111 := bstep (se 1 (by rfl) ⟨1569833, by rfl⟩ : syracuseStep 2093111 = 3139667) B3139667
theorem B22671535 : Blo 550806 22671535 := bstep (se 1 (by rfl) ⟨17003651, by rfl⟩ : syracuseStep 22671535 = 34007303) B34007303
theorem B553243 : Blo 550806 553243 := bstep (se 1 (by rfl) ⟨414932, by rfl⟩ : syracuseStep 553243 = 829865) B829865
theorem B553599 : Blo 550806 553599 := bstep (se 1 (by rfl) ⟨415199, by rfl⟩ : syracuseStep 553599 = 830399) B830399
theorem B2388649 : Blo 550806 2388649 := bstep (se 2 (by rfl) ⟨895743, by rfl⟩ : syracuseStep 2388649 = 1791487) B1791487
theorem B1864511 : Blo 550806 1864511 := bstep (se 1 (by rfl) ⟨1398383, by rfl⟩ : syracuseStep 1864511 = 2796767) B2796767
theorem B3535969 : Blo 550806 3535969 := bstep (se 2 (by rfl) ⟨1325988, by rfl⟩ : syracuseStep 3535969 = 2651977) B2651977
theorem B554087 : Blo 550806 554087 := bstep (se 1 (by rfl) ⟨415565, by rfl⟩ : syracuseStep 554087 = 831131) B831131
theorem B554343 : Blo 550806 554343 := bstep (se 1 (by rfl) ⟨415757, by rfl⟩ : syracuseStep 554343 = 831515) B831515
theorem B1570175 : Blo 550806 1570175 := bstep (se 1 (by rfl) ⟨1177631, by rfl⟩ : syracuseStep 1570175 = 2355263) B2355263
theorem B5305799 : Blo 550806 5305799 := bstep (se 1 (by rfl) ⟨3979349, by rfl⟩ : syracuseStep 5305799 = 7958699) B7958699
theorem B2094569 : Blo 550806 2094569 := bstep (se 2 (by rfl) ⟨785463, by rfl⟩ : syracuseStep 2094569 = 1570927) B1570927
theorem B620059 : Blo 550806 620059 := bstep (se 1 (by rfl) ⟨465044, by rfl⟩ : syracuseStep 620059 = 930089) B930089
theorem B554623 : Blo 550806 554623 := bstep (se 1 (by rfl) ⟨415967, by rfl⟩ : syracuseStep 554623 = 831935) B831935
theorem B1046191 : Blo 550806 1046191 := bstep (se 1 (by rfl) ⟨784643, by rfl⟩ : syracuseStep 1046191 = 1569287) B1569287
theorem B1243115 : Blo 550806 1243115 := bstep (se 1 (by rfl) ⟨932336, by rfl⟩ : syracuseStep 1243115 = 1864673) B1864673
theorem B1243475 : Blo 550806 1243475 := bstep (se 1 (by rfl) ⟨932606, by rfl⟩ : syracuseStep 1243475 = 1865213) B1865213
theorem B1243529 : Blo 550806 1243529 := bstep (se 2 (by rfl) ⟨466323, by rfl⟩ : syracuseStep 1243529 = 932647) B932647
theorem B621211 : Blo 550806 621211 := bstep (se 1 (by rfl) ⟨465908, by rfl⟩ : syracuseStep 621211 = 931817) B931817
theorem B3996539 : Blo 550806 3996539 := bstep (se 1 (by rfl) ⟨2997404, by rfl⟩ : syracuseStep 3996539 = 5994809) B5994809
theorem B2096239 : Blo 550806 2096239 := bstep (se 1 (by rfl) ⟨1572179, by rfl⟩ : syracuseStep 2096239 = 3144359) B3144359
theorem B3144815 : Blo 550806 3144815 := bstep (se 1 (by rfl) ⟨2358611, by rfl⟩ : syracuseStep 3144815 = 4717223) B4717223
theorem B1572169 : Blo 550806 1572169 := bstep (se 2 (by rfl) ⟨589563, by rfl⟩ : syracuseStep 1572169 = 1179127) B1179127
theorem B1244519 : Blo 550806 1244519 := bstep (se 1 (by rfl) ⟨933389, by rfl⟩ : syracuseStep 1244519 = 1866779) B1866779
theorem B1048135 : Blo 550806 1048135 := bstep (se 1 (by rfl) ⟨786101, by rfl⟩ : syracuseStep 1048135 = 1572203) B1572203
theorem B2096711 : Blo 550806 2096711 := bstep (se 1 (by rfl) ⟨1572533, by rfl⟩ : syracuseStep 2096711 = 3145067) B3145067
theorem B622183 : Blo 550806 622183 := bstep (se 1 (by rfl) ⟨466637, by rfl⟩ : syracuseStep 622183 = 933275) B933275
theorem B1245167 : Blo 550806 1245167 := bstep (se 1 (by rfl) ⟨933875, by rfl⟩ : syracuseStep 1245167 = 1867751) B1867751
theorem B620527837 : Blo 550806 620527837 := bstep (se 3 (by rfl) ⟨116348969, by rfl⟩ : syracuseStep 620527837 = 232697939) B232697939
theorem B1868075 : Blo 550806 1868075 := bstep (se 1 (by rfl) ⟨1401056, by rfl⟩ : syracuseStep 1868075 = 2802113) B2802113
theorem B1245563 : Blo 550806 1245563 := bstep (se 1 (by rfl) ⟨934172, by rfl⟩ : syracuseStep 1245563 = 1868345) B1868345
theorem B1245779 : Blo 550806 1245779 := bstep (se 1 (by rfl) ⟨934334, by rfl⟩ : syracuseStep 1245779 = 1868669) B1868669
theorem B623263 : Blo 550806 623263 := bstep (se 1 (by rfl) ⟨467447, by rfl⟩ : syracuseStep 623263 = 934895) B934895
theorem B885595 : Blo 550806 885595 := bstep (se 1 (by rfl) ⟨664196, by rfl⟩ : syracuseStep 885595 = 1328393) B1328393
theorem B3998555 : Blo 550806 3998555 := bstep (se 1 (by rfl) ⟨2998916, by rfl⟩ : syracuseStep 3998555 = 5997833) B5997833
theorem B1868939 : Blo 550806 1868939 := bstep (se 1 (by rfl) ⟨1401704, by rfl⟩ : syracuseStep 1868939 = 2803409) B2803409
theorem B1181083 : Blo 550806 1181083 := bstep (se 1 (by rfl) ⟨885812, by rfl⟩ : syracuseStep 1181083 = 1771625) B1771625
theorem B1050671 : Blo 550806 1050671 := bstep (se 1 (by rfl) ⟨788003, by rfl⟩ : syracuseStep 1050671 = 1576007) B1576007
theorem B413894717 : Blo 550806 413894717 := bstep (se 3 (by rfl) ⟨77605259, by rfl⟩ : syracuseStep 413894717 = 155210519) B155210519
theorem B2099627 : Blo 550806 2099627 := bstep (se 1 (by rfl) ⟨1574720, by rfl⟩ : syracuseStep 2099627 = 3149441) B3149441
theorem B1051051 : Blo 550806 1051051 := bstep (se 1 (by rfl) ⟨788288, by rfl⟩ : syracuseStep 1051051 = 1576577) B1576577
theorem B109186217 : Blo 550806 109186217 := bstep (se 2 (by rfl) ⟨40944831, by rfl⟩ : syracuseStep 109186217 = 81889663) B81889663
theorem B2789315 : Blo 550806 2789315 := bstep (se 1 (by rfl) ⟨2091986, by rfl⟩ : syracuseStep 2789315 = 4183973) B4183973
theorem B20189837 : Blo 550806 20189837 := bstep (se 3 (by rfl) ⟨3785594, by rfl⟩ : syracuseStep 20189837 = 7571189) B7571189
theorem B1577647 : Blo 550806 1577647 := bstep (se 1 (by rfl) ⟨1183235, by rfl⟩ : syracuseStep 1577647 = 2366471) B2366471
theorem B3544019 : Blo 550806 3544019 := bstep (se 1 (by rfl) ⟨2658014, by rfl⟩ : syracuseStep 3544019 = 5316029) B5316029
theorem B2102375 : Blo 550806 2102375 := bstep (se 1 (by rfl) ⟨1576781, by rfl⟩ : syracuseStep 2102375 = 3153563) B3153563
theorem B7542071 : Blo 550806 7542071 := bstep (se 1 (by rfl) ⟨5656553, by rfl⟩ : syracuseStep 7542071 = 11313107) B11313107
theorem B7083935 : Blo 550806 7083935 := bstep (se 1 (by rfl) ⟨5312951, by rfl⟩ : syracuseStep 7083935 = 10625903) B10625903
theorem B3184865 : Blo 550806 3184865 := bstep (se 2 (by rfl) ⟨1194324, by rfl⟩ : syracuseStep 3184865 = 2388649) B2388649
theorem B826745 : Blo 550806 826745 := bstep (se 2 (by rfl) ⟨310029, by rfl⟩ : syracuseStep 826745 = 620059) B620059
theorem B10624445 : Blo 550806 10624445 := bstep (se 3 (by rfl) ⟨1992083, by rfl⟩ : syracuseStep 10624445 = 3984167) B3984167
theorem B827039 : Blo 550806 827039 := bstep (se 1 (by rfl) ⟨620279, by rfl⟩ : syracuseStep 827039 = 1240559) B1240559
theorem B828281 : Blo 550806 828281 := bstep (se 2 (by rfl) ⟨310605, by rfl⟩ : syracuseStep 828281 = 621211) B621211
theorem B2368385 : Blo 550806 2368385 := bstep (se 2 (by rfl) ⟨888144, by rfl⟩ : syracuseStep 2368385 = 1776289) B1776289
theorem B828743 : Blo 550806 828743 := bstep (se 1 (by rfl) ⟨621557, by rfl⟩ : syracuseStep 828743 = 1243115) B1243115
theorem B2794985 : Blo 550806 2794985 := bstep (se 2 (by rfl) ⟨1048119, by rfl⟩ : syracuseStep 2794985 = 2096239) B2096239
theorem B4040189 : Blo 550806 4040189 := bstep (se 3 (by rfl) ⟨757535, by rfl⟩ : syracuseStep 4040189 = 1515071) B1515071
theorem B828983 : Blo 550806 828983 := bstep (se 1 (by rfl) ⟨621737, by rfl⟩ : syracuseStep 828983 = 1243475) B1243475
theorem B829019 : Blo 550806 829019 := bstep (se 1 (by rfl) ⟨621764, by rfl⟩ : syracuseStep 829019 = 1243529) B1243529
theorem B2664359 : Blo 550806 2664359 := bstep (se 1 (by rfl) ⟨1998269, by rfl⟩ : syracuseStep 2664359 = 3996539) B3996539
theorem B2041967 : Blo 550806 2041967 := bstep (se 1 (by rfl) ⟨1531475, by rfl⟩ : syracuseStep 2041967 = 3062951) B3062951
theorem B829577 : Blo 550806 829577 := bstep (se 2 (by rfl) ⟨311091, by rfl⟩ : syracuseStep 829577 = 622183) B622183
theorem B1419425 : Blo 550806 1419425 := bstep (se 2 (by rfl) ⟨532284, by rfl⟩ : syracuseStep 1419425 = 1064569) B1064569
theorem B829679 : Blo 550806 829679 := bstep (se 1 (by rfl) ⟨622259, by rfl⟩ : syracuseStep 829679 = 1244519) B1244519
theorem B830111 : Blo 550806 830111 := bstep (se 1 (by rfl) ⟨622583, by rfl⟩ : syracuseStep 830111 = 1245167) B1245167
theorem B830249 : Blo 550806 830249 := bstep (se 2 (by rfl) ⟨311343, by rfl⟩ : syracuseStep 830249 = 622687) B622687
theorem B830345 : Blo 550806 830345 := bstep (se 2 (by rfl) ⟨311379, by rfl⟩ : syracuseStep 830345 = 622759) B622759
theorem B1682441 : Blo 550806 1682441 := bstep (se 2 (by rfl) ⟨630915, by rfl⟩ : syracuseStep 1682441 = 1261831) B1261831
theorem B4205843 : Blo 550806 4205843 := bstep (se 1 (by rfl) ⟨3154382, by rfl⟩ : syracuseStep 4205843 = 6308765) B6308765
theorem B6794543 : Blo 550806 6794543 := bstep (se 1 (by rfl) ⟨5095907, by rfl⟩ : syracuseStep 6794543 = 10191815) B10191815
theorem B3976559 : Blo 550806 3976559 := bstep (se 1 (by rfl) ⟨2982419, by rfl⟩ : syracuseStep 3976559 = 5964839) B5964839
theorem B5844347 : Blo 550806 5844347 := bstep (se 1 (by rfl) ⟨4383260, by rfl⟩ : syracuseStep 5844347 = 8766521) B8766521
theorem B830927 : Blo 550806 830927 := bstep (se 1 (by rfl) ⟨623195, by rfl⟩ : syracuseStep 830927 = 1246391) B1246391
theorem B16166395 : Blo 550806 16166395 := bstep (se 1 (by rfl) ⟨12124796, by rfl⟩ : syracuseStep 16166395 = 24249593) B24249593
theorem B831311 : Blo 550806 831311 := bstep (se 1 (by rfl) ⟨623483, by rfl⟩ : syracuseStep 831311 = 1246967) B1246967
theorem B1257407 : Blo 550806 1257407 := bstep (se 1 (by rfl) ⟨943055, by rfl⟩ : syracuseStep 1257407 = 1886111) B1886111
theorem B4665371 : Blo 550806 4665371 := bstep (se 1 (by rfl) ⟨3499028, by rfl⟩ : syracuseStep 4665371 = 6998057) B6998057
theorem B4206815 : Blo 550806 4206815 := bstep (se 1 (by rfl) ⟨3155111, by rfl⟩ : syracuseStep 4206815 = 6310223) B6310223
theorem B831791 : Blo 550806 831791 := bstep (se 1 (by rfl) ⟨623843, by rfl⟩ : syracuseStep 831791 = 1247687) B1247687
theorem B831815 : Blo 550806 831815 := bstep (se 1 (by rfl) ⟨623861, by rfl⟩ : syracuseStep 831815 = 1247723) B1247723
theorem B2798063 : Blo 550806 2798063 := bstep (se 1 (by rfl) ⟨2098547, by rfl⟩ : syracuseStep 2798063 = 4197095) B4197095
theorem B8532803 : Blo 550806 8532803 := bstep (se 1 (by rfl) ⟨6399602, by rfl⟩ : syracuseStep 8532803 = 12799205) B12799205
theorem B3159647 : Blo 550806 3159647 := bstep (se 1 (by rfl) ⟨2369735, by rfl⟩ : syracuseStep 3159647 = 4739471) B4739471
theorem B5322793 : Blo 550806 5322793 := bstep (se 2 (by rfl) ⟨1996047, by rfl⟩ : syracuseStep 5322793 = 3992095) B3992095
theorem B2800493 : Blo 550806 2800493 := bstep (se 3 (by rfl) ⟨525092, by rfl⟩ : syracuseStep 2800493 = 1050185) B1050185
theorem B22658383 : Blo 550806 22658383 := bstep (se 1 (by rfl) ⟨16993787, by rfl⟩ : syracuseStep 22658383 = 33987575) B33987575
theorem B2243999 : Blo 550806 2243999 := bstep (se 1 (by rfl) ⟨1682999, by rfl⟩ : syracuseStep 2243999 = 3365999) B3365999
theorem B7978769 : Blo 550806 7978769 := bstep (se 2 (by rfl) ⟨2992038, by rfl⟩ : syracuseStep 7978769 = 5984077) B5984077
theorem B1490831 : Blo 550806 1490831 := bstep (se 1 (by rfl) ⟨1118123, by rfl⟩ : syracuseStep 1490831 = 2236247) B2236247
theorem B6275231 : Blo 550806 6275231 := bstep (se 1 (by rfl) ⟨4706423, by rfl⟩ : syracuseStep 6275231 = 9412847) B9412847
theorem B30228713 : Blo 550806 30228713 := bstep (se 2 (by rfl) ⟨11335767, by rfl⟩ : syracuseStep 30228713 = 22671535) B22671535
theorem B934375 : Blo 550806 934375 := bstep (se 1 (by rfl) ⟨700781, by rfl⟩ : syracuseStep 934375 = 1401563) B1401563
theorem B1327643 : Blo 550806 1327643 := bstep (se 1 (by rfl) ⟨995732, by rfl⟩ : syracuseStep 1327643 = 1991465) B1991465
theorem B934537 : Blo 550806 934537 := bstep (se 2 (by rfl) ⟨350451, by rfl⟩ : syracuseStep 934537 = 700903) B700903
theorem B935003 : Blo 550806 935003 := bstep (se 1 (by rfl) ⟨701252, by rfl⟩ : syracuseStep 935003 = 1402505) B1402505
theorem B4048841 : Blo 550806 4048841 := bstep (se 2 (by rfl) ⟨1518315, by rfl⟩ : syracuseStep 4048841 = 3036631) B3036631
theorem B1394921 : Blo 550806 1394921 := bstep (se 2 (by rfl) ⟨523095, by rfl⟩ : syracuseStep 1394921 = 1046191) B1046191
theorem B1067347 : Blo 550806 1067347 := bstep (se 1 (by rfl) ⟨800510, by rfl⟩ : syracuseStep 1067347 = 1601021) B1601021
theorem B2247209 : Blo 550806 2247209 := bstep (se 2 (by rfl) ⟨842703, by rfl⟩ : syracuseStep 2247209 = 1685407) B1685407
theorem B1395407 : Blo 550806 1395407 := bstep (se 1 (by rfl) ⟨1046555, by rfl⟩ : syracuseStep 1395407 = 2093111) B2093111
theorem B1396379 : Blo 550806 1396379 := bstep (se 1 (by rfl) ⟨1047284, by rfl⟩ : syracuseStep 1396379 = 2094569) B2094569
theorem B1494875 : Blo 550806 1494875 := bstep (se 1 (by rfl) ⟨1121156, by rfl⟩ : syracuseStep 1494875 = 2242313) B2242313
theorem B1397513 : Blo 550806 1397513 := bstep (se 2 (by rfl) ⟨524067, by rfl⟩ : syracuseStep 1397513 = 1048135) B1048135
theorem B2806649 : Blo 550806 2806649 := bstep (se 2 (by rfl) ⟨1052493, by rfl⟩ : syracuseStep 2806649 = 2104987) B2104987
theorem B1397807 : Blo 550806 1397807 := bstep (se 1 (by rfl) ⟨1048355, by rfl⟩ : syracuseStep 1397807 = 2096711) B2096711
theorem B3986617 : Blo 550806 3986617 := bstep (se 2 (by rfl) ⟨1494981, by rfl⟩ : syracuseStep 3986617 = 2989963) B2989963
theorem B1332755 : Blo 550806 1332755 := bstep (se 1 (by rfl) ⟨999566, by rfl⟩ : syracuseStep 1332755 = 1999133) B1999133
theorem B3987539 : Blo 550806 3987539 := bstep (se 1 (by rfl) ⟨2990654, by rfl⟩ : syracuseStep 3987539 = 5981309) B5981309
theorem B1890487 : Blo 550806 1890487 := bstep (se 1 (by rfl) ⟨1417865, by rfl⟩ : syracuseStep 1890487 = 2835731) B2835731
theorem B12409805 : Blo 550806 12409805 := bstep (se 3 (by rfl) ⟨2326838, by rfl⟩ : syracuseStep 12409805 = 4653677) B4653677
theorem B9460961 : Blo 550806 9460961 := bstep (se 2 (by rfl) ⟨3547860, by rfl⟩ : syracuseStep 9460961 = 7095721) B7095721
theorem B6282521 : Blo 550806 6282521 := bstep (se 2 (by rfl) ⟨2355945, by rfl⟩ : syracuseStep 6282521 = 4711891) B4711891
theorem B4185431 : Blo 550806 4185431 := bstep (se 1 (by rfl) ⟨3139073, by rfl⟩ : syracuseStep 4185431 = 6278147) B6278147
theorem B2121551 : Blo 550806 2121551 := bstep (se 1 (by rfl) ⟨1591163, by rfl⟩ : syracuseStep 2121551 = 3182327) B3182327
theorem B3990653 : Blo 550806 3990653 := bstep (se 3 (by rfl) ⟨748247, by rfl⟩ : syracuseStep 3990653 = 1496495) B1496495
theorem B7563091 : Blo 550806 7563091 := bstep (se 1 (by rfl) ⟨5672318, by rfl⟩ : syracuseStep 7563091 = 11344637) B11344637
theorem B5302381 : Blo 550806 5302381 := bstep (se 3 (by rfl) ⟨994196, by rfl⟩ : syracuseStep 5302381 = 1988393) B1988393
theorem B1403041 : Blo 550806 1403041 := bstep (se 2 (by rfl) ⟨526140, by rfl⟩ : syracuseStep 1403041 = 1052281) B1052281
theorem B4483259 : Blo 550806 4483259 := bstep (se 1 (by rfl) ⟨3362444, by rfl⟩ : syracuseStep 4483259 = 6724889) B6724889
theorem B551119 : Blo 550806 551119 := bstep (se 1 (by rfl) ⟨413339, by rfl⟩ : syracuseStep 551119 = 826679) B826679
theorem B4188833 : Blo 550806 4188833 := bstep (se 2 (by rfl) ⟨1570812, by rfl⟩ : syracuseStep 4188833 = 3141625) B3141625
theorem B5401259 : Blo 550806 5401259 := bstep (se 1 (by rfl) ⟨4050944, by rfl⟩ : syracuseStep 5401259 = 8101889) B8101889
theorem B1239803 : Blo 550806 1239803 := bstep (se 1 (by rfl) ⟨929852, by rfl⟩ : syracuseStep 1239803 = 1859705) B1859705
theorem B1862891 : Blo 550806 1862891 := bstep (se 1 (by rfl) ⟨1397168, by rfl⟩ : syracuseStep 1862891 = 2794337) B2794337
theorem B552895 : Blo 550806 552895 := bstep (se 1 (by rfl) ⟨414671, by rfl⟩ : syracuseStep 552895 = 829343) B829343
theorem B4714625 : Blo 550806 4714625 := bstep (se 2 (by rfl) ⟨1767984, by rfl⟩ : syracuseStep 4714625 = 3535969) B3535969
theorem B8057249 : Blo 550806 8057249 := bstep (se 2 (by rfl) ⟨3021468, by rfl⟩ : syracuseStep 8057249 = 6042937) B6042937
theorem B1241567 : Blo 550806 1241567 := bstep (se 1 (by rfl) ⟨931175, by rfl⟩ : syracuseStep 1241567 = 1862351) B1862351
theorem B553627 : Blo 550806 553627 := bstep (se 1 (by rfl) ⟨415220, by rfl⟩ : syracuseStep 553627 = 830441) B830441
theorem B553663 : Blo 550806 553663 := bstep (se 1 (by rfl) ⟨415247, by rfl⟩ : syracuseStep 553663 = 830495) B830495
theorem B2683937 : Blo 550806 2683937 := bstep (se 2 (by rfl) ⟨1006476, by rfl⟩ : syracuseStep 2683937 = 2012953) B2012953
theorem B554215 : Blo 550806 554215 := bstep (se 1 (by rfl) ⟨415661, by rfl⟩ : syracuseStep 554215 = 831323) B831323
theorem B1243007 : Blo 550806 1243007 := bstep (se 1 (by rfl) ⟨932255, by rfl⟩ : syracuseStep 1243007 = 1864511) B1864511
theorem B620455 : Blo 550806 620455 := bstep (se 1 (by rfl) ⟨465341, by rfl⟩ : syracuseStep 620455 = 930683) B930683
theorem B7108843 : Blo 550806 7108843 := bstep (se 1 (by rfl) ⟨5331632, by rfl⟩ : syracuseStep 7108843 = 10663265) B10663265
theorem B1046783 : Blo 550806 1046783 := bstep (se 1 (by rfl) ⟨785087, by rfl⟩ : syracuseStep 1046783 = 1570175) B1570175
theorem B3537199 : Blo 550806 3537199 := bstep (se 1 (by rfl) ⟨2652899, by rfl⟩ : syracuseStep 3537199 = 5305799) B5305799
theorem B1997779 : Blo 550806 1997779 := bstep (se 1 (by rfl) ⟨1498334, by rfl⟩ : syracuseStep 1997779 = 2996669) B2996669
theorem B2096225 : Blo 550806 2096225 := bstep (se 2 (by rfl) ⟨786084, by rfl⟩ : syracuseStep 2096225 = 1572169) B1572169
theorem B2096543 : Blo 550806 2096543 := bstep (se 1 (by rfl) ⟨1572407, by rfl⟩ : syracuseStep 2096543 = 3144815) B3144815
theorem B13074281 : Blo 550806 13074281 := bstep (se 2 (by rfl) ⟨4902855, by rfl⟩ : syracuseStep 13074281 = 9805711) B9805711
theorem B20152475 : Blo 550806 20152475 := bstep (se 1 (by rfl) ⟨15114356, by rfl⟩ : syracuseStep 20152475 = 30228713) B30228713
theorem B1245383 : Blo 550806 1245383 := bstep (se 1 (by rfl) ⟨934037, by rfl⟩ : syracuseStep 1245383 = 1868075) B1868075
theorem B885095 : Blo 550806 885095 := bstep (se 1 (by rfl) ⟨663821, by rfl⟩ : syracuseStep 885095 = 1327643) B1327643
theorem B1245833 : Blo 550806 1245833 := bstep (se 2 (by rfl) ⟨467187, by rfl⟩ : syracuseStep 1245833 = 934375) B934375
theorem B623335 : Blo 550806 623335 := bstep (se 1 (by rfl) ⟨467501, by rfl⟩ : syracuseStep 623335 = 935003) B935003
theorem B1245959 : Blo 550806 1245959 := bstep (se 1 (by rfl) ⟨934469, by rfl⟩ : syracuseStep 1245959 = 1868939) B1868939
theorem B1246049 : Blo 550806 1246049 := bstep (se 2 (by rfl) ⟨467268, by rfl⟩ : syracuseStep 1246049 = 934537) B934537
theorem B1180793 : Blo 550806 1180793 := bstep (se 2 (by rfl) ⟨442797, by rfl⟩ : syracuseStep 1180793 = 885595) B885595
theorem B15140533 : Blo 550806 15140533 := bstep (se 5 (by rfl) ⟨709712, by rfl⟩ : syracuseStep 15140533 = 1419425) B1419425
theorem B1574777 : Blo 550806 1574777 := bstep (se 2 (by rfl) ⟨590541, by rfl⟩ : syracuseStep 1574777 = 1181083) B1181083
theorem B1870721 : Blo 550806 1870721 := bstep (se 2 (by rfl) ⟨701520, by rfl⟩ : syracuseStep 1870721 = 1403041) B1403041
theorem B1871099 : Blo 550806 1871099 := bstep (se 1 (by rfl) ⟨1403324, by rfl⟩ : syracuseStep 1871099 = 2806649) B2806649
theorem B2362679 : Blo 550806 2362679 := bstep (se 1 (by rfl) ⟨1772009, by rfl⟩ : syracuseStep 2362679 = 3544019) B3544019
theorem B888503 : Blo 550806 888503 := bstep (se 1 (by rfl) ⟨666377, by rfl⟩ : syracuseStep 888503 = 1332755) B1332755
theorem B4722623 : Blo 550806 4722623 := bstep (se 1 (by rfl) ⟨3541967, by rfl⟩ : syracuseStep 4722623 = 7083935) B7083935
theorem B2658359 : Blo 550806 2658359 := bstep (se 1 (by rfl) ⟨1993769, by rfl⟩ : syracuseStep 2658359 = 3987539) B3987539
theorem B2790287 : Blo 550806 2790287 := bstep (se 1 (by rfl) ⟨2092715, by rfl⟩ : syracuseStep 2790287 = 4185431) B4185431
theorem B7082963 : Blo 550806 7082963 := bstep (se 1 (by rfl) ⟨5312222, by rfl⟩ : syracuseStep 7082963 = 10624445) B10624445
theorem B1414367 : Blo 550806 1414367 := bstep (se 1 (by rfl) ⟨1060775, by rfl⟩ : syracuseStep 1414367 = 2121551) B2121551
theorem B5445245 : Blo 550806 5445245 := bstep (se 3 (by rfl) ⟨1020983, by rfl⟩ : syracuseStep 5445245 = 2041967) B2041967
theorem B1578923 : Blo 550806 1578923 := bstep (se 1 (by rfl) ⟨1184192, by rfl⟩ : syracuseStep 1578923 = 2368385) B2368385
theorem B2791421 : Blo 550806 2791421 := bstep (se 3 (by rfl) ⟨523391, by rfl⟩ : syracuseStep 2791421 = 1046783) B1046783
theorem B2660435 : Blo 550806 2660435 := bstep (se 1 (by rfl) ⟨1995326, by rfl⟩ : syracuseStep 2660435 = 3990653) B3990653
theorem B2103529 : Blo 550806 2103529 := bstep (se 2 (by rfl) ⟨788823, by rfl⟩ : syracuseStep 2103529 = 1577647) B1577647
theorem B2693459 : Blo 550806 2693459 := bstep (se 1 (by rfl) ⟨2020094, by rfl⟩ : syracuseStep 2693459 = 4040189) B4040189
theorem B1776239 : Blo 550806 1776239 := bstep (se 1 (by rfl) ⟨1332179, by rfl⟩ : syracuseStep 1776239 = 2664359) B2664359
theorem B2988839 : Blo 550806 2988839 := bstep (se 1 (by rfl) ⟨2241629, by rfl⟩ : syracuseStep 2988839 = 4483259) B4483259
theorem B5315489 : Blo 550806 5315489 := bstep (se 2 (by rfl) ⟨1993308, by rfl⟩ : syracuseStep 5315489 = 3986617) B3986617
theorem B2792555 : Blo 550806 2792555 := bstep (se 1 (by rfl) ⟨2094416, by rfl⟩ : syracuseStep 2792555 = 4188833) B4188833
theorem B826535 : Blo 550806 826535 := bstep (se 1 (by rfl) ⟨619901, by rfl⟩ : syracuseStep 826535 = 1239803) B1239803
theorem B1121627 : Blo 550806 1121627 := bstep (se 1 (by rfl) ⟨841220, by rfl⟩ : syracuseStep 1121627 = 1682441) B1682441
theorem B4529695 : Blo 550806 4529695 := bstep (se 1 (by rfl) ⟨3397271, by rfl⟩ : syracuseStep 4529695 = 6794543) B6794543
theorem B827273 : Blo 550806 827273 := bstep (se 2 (by rfl) ⟨310227, by rfl⟩ : syracuseStep 827273 = 620455) B620455
theorem B9478457 : Blo 550806 9478457 := bstep (se 2 (by rfl) ⟨3554421, by rfl⟩ : syracuseStep 9478457 = 7108843) B7108843
theorem B827711 : Blo 550806 827711 := bstep (se 1 (by rfl) ⟨620783, by rfl⟩ : syracuseStep 827711 = 1241567) B1241567
theorem B2106431 : Blo 550806 2106431 := bstep (se 1 (by rfl) ⟨1579823, by rfl⟩ : syracuseStep 2106431 = 3159647) B3159647
theorem B828671 : Blo 550806 828671 := bstep (se 1 (by rfl) ⟨621503, by rfl⟩ : syracuseStep 828671 = 1243007) B1243007
theorem B2663705 : Blo 550806 2663705 := bstep (se 2 (by rfl) ⟨998889, by rfl⟩ : syracuseStep 2663705 = 1997779) B1997779
theorem B5319179 : Blo 550806 5319179 := bstep (se 1 (by rfl) ⟨3989384, by rfl⟩ : syracuseStep 5319179 = 7978769) B7978769
theorem B993887 : Blo 550806 993887 := bstep (se 1 (by rfl) ⟨745415, by rfl⟩ : syracuseStep 993887 = 1490831) B1490831
theorem B830375 : Blo 550806 830375 := bstep (se 1 (by rfl) ⟨622781, by rfl⟩ : syracuseStep 830375 = 1245563) B1245563
theorem B827370449 : Blo 550806 827370449 := bstep (se 2 (by rfl) ⟨310263918, by rfl⟩ : syracuseStep 827370449 = 620527837) B620527837
theorem B830519 : Blo 550806 830519 := bstep (se 1 (by rfl) ⟨622889, by rfl⟩ : syracuseStep 830519 = 1245779) B1245779
theorem B2665703 : Blo 550806 2665703 := bstep (se 1 (by rfl) ⟨1999277, by rfl⟩ : syracuseStep 2665703 = 3998555) B3998555
theorem B831017 : Blo 550806 831017 := bstep (se 2 (by rfl) ⟨311631, by rfl⟩ : syracuseStep 831017 = 623263) B623263
theorem B2699227 : Blo 550806 2699227 := bstep (se 1 (by rfl) ⟨2024420, by rfl⟩ : syracuseStep 2699227 = 4048841) B4048841
theorem B929947 : Blo 550806 929947 := bstep (se 1 (by rfl) ⟨697460, by rfl⟩ : syracuseStep 929947 = 1394921) B1394921
theorem B930271 : Blo 550806 930271 := bstep (se 1 (by rfl) ⟨697703, by rfl⟩ : syracuseStep 930271 = 1395407) B1395407
theorem B72790811 : Blo 550806 72790811 := bstep (se 1 (by rfl) ⟨54593108, by rfl⟩ : syracuseStep 72790811 = 109186217) B109186217
theorem B22754141 : Blo 550806 22754141 := bstep (se 3 (by rfl) ⟨4266401, by rfl⟩ : syracuseStep 22754141 = 8532803) B8532803
theorem B930919 : Blo 550806 930919 := bstep (se 1 (by rfl) ⟨698189, by rfl⟩ : syracuseStep 930919 = 1396379) B1396379
theorem B931675 : Blo 550806 931675 := bstep (se 1 (by rfl) ⟨698756, by rfl⟩ : syracuseStep 931675 = 1397513) B1397513
theorem B931871 : Blo 550806 931871 := bstep (se 1 (by rfl) ⟨698903, by rfl⟩ : syracuseStep 931871 = 1397807) B1397807
theorem B5028047 : Blo 550806 5028047 := bstep (se 1 (by rfl) ⟨3771035, by rfl⟩ : syracuseStep 5028047 = 7542071) B7542071
theorem B62339701 : Blo 550806 62339701 := bstep (se 5 (by rfl) ⟨2922173, by rfl⟩ : syracuseStep 62339701 = 5844347) B5844347
theorem B6307307 : Blo 550806 6307307 := bstep (se 1 (by rfl) ⟨4730480, by rfl⟩ : syracuseStep 6307307 = 9460961) B9460961
theorem B2801789 : Blo 550806 2801789 := bstep (se 3 (by rfl) ⟨525335, by rfl⟩ : syracuseStep 2801789 = 1050671) B1050671
theorem B2803895 : Blo 550806 2803895 := bstep (se 1 (by rfl) ⟨2102921, by rfl⟩ : syracuseStep 2803895 = 4205843) B4205843
theorem B838271 : Blo 550806 838271 := bstep (se 1 (by rfl) ⟨628703, by rfl⟩ : syracuseStep 838271 = 1257407) B1257407
theorem B7097057 : Blo 550806 7097057 := bstep (se 2 (by rfl) ⟨2661396, by rfl⟩ : syracuseStep 7097057 = 5322793) B5322793
theorem B2804543 : Blo 550806 2804543 := bstep (se 1 (by rfl) ⟨2103407, by rfl⟩ : syracuseStep 2804543 = 4206815) B4206815
theorem B1789291 : Blo 550806 1789291 := bstep (se 1 (by rfl) ⟨1341968, by rfl⟩ : syracuseStep 1789291 = 2683937) B2683937
theorem B1397483 : Blo 550806 1397483 := bstep (se 1 (by rfl) ⟨1048112, by rfl⟩ : syracuseStep 1397483 = 2096225) B2096225
theorem B3986333 : Blo 550806 3986333 := bstep (se 3 (by rfl) ⟨747437, by rfl⟩ : syracuseStep 3986333 = 1494875) B1494875
theorem B1397695 : Blo 550806 1397695 := bstep (se 1 (by rfl) ⟨1048271, by rfl⟩ : syracuseStep 1397695 = 2096543) B2096543
theorem B1495999 : Blo 550806 1495999 := bstep (se 1 (by rfl) ⟨1121999, by rfl⟩ : syracuseStep 1495999 = 2243999) B2243999
theorem B12440989 : Blo 550806 12440989 := bstep (se 3 (by rfl) ⟨2332685, by rfl⟩ : syracuseStep 12440989 = 4665371) B4665371
theorem B4183487 : Blo 550806 4183487 := bstep (se 1 (by rfl) ⟨3137615, by rfl⟩ : syracuseStep 4183487 = 6275231) B6275231
theorem B275929811 : Blo 550806 275929811 := bstep (se 1 (by rfl) ⟨206947358, by rfl⟩ : syracuseStep 275929811 = 413894717) B413894717
theorem B1399751 : Blo 550806 1399751 := bstep (se 1 (by rfl) ⟨1049813, by rfl⟩ : syracuseStep 1399751 = 2099627) B2099627
theorem B1498139 : Blo 550806 1498139 := bstep (se 1 (by rfl) ⟨1123604, by rfl⟩ : syracuseStep 1498139 = 2247209) B2247209
theorem B5692517 : Blo 550806 5692517 := bstep (se 4 (by rfl) ⟨533673, by rfl⟩ : syracuseStep 5692517 = 1067347) B1067347
theorem B10084121 : Blo 550806 10084121 := bstep (se 2 (by rfl) ⟨3781545, by rfl⟩ : syracuseStep 10084121 = 7563091) B7563091
theorem B1859543 : Blo 550806 1859543 := bstep (se 1 (by rfl) ⟨1394657, by rfl⟩ : syracuseStep 1859543 = 2789315) B2789315
theorem B7069841 : Blo 550806 7069841 := bstep (se 2 (by rfl) ⟨2651190, by rfl⟩ : syracuseStep 7069841 = 5302381) B5302381
theorem B13459891 : Blo 550806 13459891 := bstep (se 1 (by rfl) ⟨10094918, by rfl⟩ : syracuseStep 13459891 = 20189837) B20189837
theorem B1401401 : Blo 550806 1401401 := bstep (se 2 (by rfl) ⟨525525, by rfl⟩ : syracuseStep 1401401 = 1051051) B1051051
theorem B1401583 : Blo 550806 1401583 := bstep (se 1 (by rfl) ⟨1051187, by rfl⟩ : syracuseStep 1401583 = 2102375) B2102375
theorem B2123243 : Blo 550806 2123243 := bstep (se 1 (by rfl) ⟨1592432, by rfl⟩ : syracuseStep 2123243 = 3184865) B3184865
theorem B21555193 : Blo 550806 21555193 := bstep (se 2 (by rfl) ⟨8083197, by rfl⟩ : syracuseStep 21555193 = 16166395) B16166395
theorem B4188347 : Blo 550806 4188347 := bstep (se 1 (by rfl) ⟨3141260, by rfl⟩ : syracuseStep 4188347 = 6282521) B6282521
theorem B551163 : Blo 550806 551163 := bstep (se 1 (by rfl) ⟨413372, by rfl⟩ : syracuseStep 551163 = 826745) B826745
theorem B551359 : Blo 550806 551359 := bstep (se 1 (by rfl) ⟨413519, by rfl⟩ : syracuseStep 551359 = 827039) B827039
theorem B552187 : Blo 550806 552187 := bstep (se 1 (by rfl) ⟨414140, by rfl⟩ : syracuseStep 552187 = 828281) B828281
theorem B552495 : Blo 550806 552495 := bstep (se 1 (by rfl) ⟨414371, by rfl⟩ : syracuseStep 552495 = 828743) B828743
theorem B1863323 : Blo 550806 1863323 := bstep (se 1 (by rfl) ⟨1397492, by rfl⟩ : syracuseStep 1863323 = 2794985) B2794985
theorem B552655 : Blo 550806 552655 := bstep (se 1 (by rfl) ⟨414491, by rfl⟩ : syracuseStep 552655 = 828983) B828983
theorem B552679 : Blo 550806 552679 := bstep (se 1 (by rfl) ⟨414509, by rfl⟩ : syracuseStep 552679 = 829019) B829019
theorem B553051 : Blo 550806 553051 := bstep (se 1 (by rfl) ⟨414788, by rfl⟩ : syracuseStep 553051 = 829577) B829577
theorem B553119 : Blo 550806 553119 := bstep (se 1 (by rfl) ⟨414839, by rfl⟩ : syracuseStep 553119 = 829679) B829679
theorem B553407 : Blo 550806 553407 := bstep (se 1 (by rfl) ⟨415055, by rfl⟩ : syracuseStep 553407 = 830111) B830111
theorem B3600839 : Blo 550806 3600839 := bstep (se 1 (by rfl) ⟨2700629, by rfl⟩ : syracuseStep 3600839 = 5401259) B5401259
theorem B553499 : Blo 550806 553499 := bstep (se 1 (by rfl) ⟨415124, by rfl⟩ : syracuseStep 553499 = 830249) B830249
theorem B553563 : Blo 550806 553563 := bstep (se 1 (by rfl) ⟨415172, by rfl⟩ : syracuseStep 553563 = 830345) B830345
theorem B1241927 : Blo 550806 1241927 := bstep (se 1 (by rfl) ⟨931445, by rfl⟩ : syracuseStep 1241927 = 1862891) B1862891
theorem B2651039 : Blo 550806 2651039 := bstep (se 1 (by rfl) ⟨1988279, by rfl⟩ : syracuseStep 2651039 = 3976559) B3976559
theorem B553951 : Blo 550806 553951 := bstep (se 1 (by rfl) ⟨415463, by rfl⟩ : syracuseStep 553951 = 830927) B830927
theorem B33092813 : Blo 550806 33092813 := bstep (se 3 (by rfl) ⟨6204902, by rfl⟩ : syracuseStep 33092813 = 12409805) B12409805
theorem B554207 : Blo 550806 554207 := bstep (se 1 (by rfl) ⟨415655, by rfl⟩ : syracuseStep 554207 = 831311) B831311
theorem B3143083 : Blo 550806 3143083 := bstep (se 1 (by rfl) ⟨2357312, by rfl⟩ : syracuseStep 3143083 = 4714625) B4714625
theorem B554527 : Blo 550806 554527 := bstep (se 1 (by rfl) ⟨415895, by rfl⟩ : syracuseStep 554527 = 831791) B831791
theorem B554543 : Blo 550806 554543 := bstep (se 1 (by rfl) ⟨415907, by rfl⟩ : syracuseStep 554543 = 831815) B831815
theorem B2520649 : Blo 550806 2520649 := bstep (se 2 (by rfl) ⟨945243, by rfl⟩ : syracuseStep 2520649 = 1890487) B1890487
theorem B5371499 : Blo 550806 5371499 := bstep (se 1 (by rfl) ⟨4028624, by rfl⟩ : syracuseStep 5371499 = 8057249) B8057249
theorem B1865375 : Blo 550806 1865375 := bstep (se 1 (by rfl) ⟨1399031, by rfl⟩ : syracuseStep 1865375 = 2798063) B2798063
theorem B4716265 : Blo 550806 4716265 := bstep (se 2 (by rfl) ⟨1768599, by rfl⟩ : syracuseStep 4716265 = 3537199) B3537199
theorem B30211177 : Blo 550806 30211177 := bstep (se 2 (by rfl) ⟨11329191, by rfl⟩ : syracuseStep 30211177 = 22658383) B22658383
theorem B1866995 : Blo 550806 1866995 := bstep (se 1 (by rfl) ⟨1400246, by rfl⟩ : syracuseStep 1866995 = 2800493) B2800493
theorem B8716187 : Blo 550806 8716187 := bstep (se 1 (by rfl) ⟨6537140, by rfl⟩ : syracuseStep 8716187 = 13074281) B13074281
theorem B1867859 : Blo 550806 1867859 := bstep (se 1 (by rfl) ⟨1400894, by rfl⟩ : syracuseStep 1867859 = 2801789) B2801789
theorem B13434983 : Blo 550806 13434983 := bstep (se 1 (by rfl) ⟨10076237, by rfl⟩ : syracuseStep 13434983 = 20152475) B20152475
theorem B590063 : Blo 550806 590063 := bstep (se 1 (by rfl) ⟨442547, by rfl⟩ : syracuseStep 590063 = 885095) B885095
theorem B787195 : Blo 550806 787195 := bstep (se 1 (by rfl) ⟨590396, by rfl⟩ : syracuseStep 787195 = 1180793) B1180793
theorem B1868777 : Blo 550806 1868777 := bstep (se 2 (by rfl) ⟨700791, by rfl⟩ : syracuseStep 1868777 = 1401583) B1401583
theorem B1049851 : Blo 550806 1049851 := bstep (se 1 (by rfl) ⟨787388, by rfl⟩ : syracuseStep 1049851 = 1574777) B1574777
theorem B1869263 : Blo 550806 1869263 := bstep (se 1 (by rfl) ⟨1401947, by rfl⟩ : syracuseStep 1869263 = 2803895) B2803895
theorem B558847 : Blo 550806 558847 := bstep (se 1 (by rfl) ⟨419135, by rfl⟩ : syracuseStep 558847 = 838271) B838271
theorem B1869695 : Blo 550806 1869695 := bstep (se 1 (by rfl) ⟨1402271, by rfl⟩ : syracuseStep 1869695 = 2804543) B2804543
theorem B1247147 : Blo 550806 1247147 := bstep (se 1 (by rfl) ⟨935360, by rfl⟩ : syracuseStep 1247147 = 1870721) B1870721
theorem B1247399 : Blo 550806 1247399 := bstep (se 1 (by rfl) ⟨935549, by rfl⟩ : syracuseStep 1247399 = 1871099) B1871099
theorem B1575119 : Blo 550806 1575119 := bstep (se 1 (by rfl) ⟨1181339, by rfl⟩ : syracuseStep 1575119 = 2362679) B2362679
theorem B20187377 : Blo 550806 20187377 := bstep (se 2 (by rfl) ⟨7570266, by rfl⟩ : syracuseStep 20187377 = 15140533) B15140533
theorem B3148415 : Blo 550806 3148415 := bstep (se 1 (by rfl) ⟨2361311, by rfl⟩ : syracuseStep 3148415 = 4722623) B4722623
theorem B28740257 : Blo 550806 28740257 := bstep (se 2 (by rfl) ⟨10777596, by rfl⟩ : syracuseStep 28740257 = 21555193) B21555193
theorem B88247501 : Blo 550806 88247501 := bstep (se 3 (by rfl) ⟨16546406, by rfl⟩ : syracuseStep 88247501 = 33092813) B33092813
theorem B2657555 : Blo 550806 2657555 := bstep (se 1 (by rfl) ⟨1993166, by rfl⟩ : syracuseStep 2657555 = 3986333) B3986333
theorem B4721975 : Blo 550806 4721975 := bstep (se 1 (by rfl) ⟨3541481, by rfl⟩ : syracuseStep 4721975 = 7082963) B7082963
theorem B2788991 : Blo 550806 2788991 := bstep (se 1 (by rfl) ⟨2091743, by rfl⟩ : syracuseStep 2788991 = 4183487) B4183487
theorem B1052615 : Blo 550806 1052615 := bstep (se 1 (by rfl) ⟨789461, by rfl⟩ : syracuseStep 1052615 = 1578923) B1578923
theorem B1773623 : Blo 550806 1773623 := bstep (se 1 (by rfl) ⟨1330217, by rfl⟩ : syracuseStep 1773623 = 2660435) B2660435
theorem B14520653 : Blo 550806 14520653 := bstep (se 3 (by rfl) ⟨2722622, by rfl⟩ : syracuseStep 14520653 = 5445245) B5445245
theorem B1184159 : Blo 550806 1184159 := bstep (se 1 (by rfl) ⟨888119, by rfl⟩ : syracuseStep 1184159 = 1776239) B1776239
theorem B3543659 : Blo 550806 3543659 := bstep (se 1 (by rfl) ⟨2657744, by rfl⟩ : syracuseStep 3543659 = 5315489) B5315489
theorem B6722747 : Blo 550806 6722747 := bstep (se 1 (by rfl) ⟨5042060, by rfl⟩ : syracuseStep 6722747 = 10084121) B10084121
theorem B1775803 : Blo 550806 1775803 := bstep (se 1 (by rfl) ⟨1331852, by rfl⟩ : syracuseStep 1775803 = 2663705) B2663705
theorem B7182557 : Blo 550806 7182557 := bstep (se 3 (by rfl) ⟨1346729, by rfl⟩ : syracuseStep 7182557 = 2693459) B2693459
theorem B1415495 : Blo 550806 1415495 := bstep (se 1 (by rfl) ⟨1061621, by rfl⟩ : syracuseStep 1415495 = 2123243) B2123243
theorem B2792231 : Blo 550806 2792231 := bstep (se 1 (by rfl) ⟨2094173, by rfl⟩ : syracuseStep 2792231 = 4188347) B4188347
theorem B3546119 : Blo 550806 3546119 := bstep (se 1 (by rfl) ⟨2659589, by rfl⟩ : syracuseStep 3546119 = 5319179) B5319179
theorem B662591 : Blo 550806 662591 := bstep (se 1 (by rfl) ⟨496943, by rfl⟩ : syracuseStep 662591 = 993887) B993887
theorem B16587985 : Blo 550806 16587985 := bstep (se 2 (by rfl) ⟨6220494, by rfl⟩ : syracuseStep 16587985 = 12440989) B12440989
theorem B1777135 : Blo 550806 1777135 := bstep (se 1 (by rfl) ⟨1332851, by rfl⟩ : syracuseStep 1777135 = 2665703) B2665703
theorem B2400559 : Blo 550806 2400559 := bstep (se 1 (by rfl) ⟨1800419, by rfl⟩ : syracuseStep 2400559 = 3600839) B3600839
theorem B827951 : Blo 550806 827951 := bstep (se 1 (by rfl) ⟨620963, by rfl⟩ : syracuseStep 827951 = 1241927) B1241927
theorem B2991005 : Blo 550806 2991005 := bstep (se 3 (by rfl) ⟨560813, by rfl⟩ : syracuseStep 2991005 = 1121627) B1121627
theorem B3580999 : Blo 550806 3580999 := bstep (se 1 (by rfl) ⟨2685749, by rfl⟩ : syracuseStep 3580999 = 5371499) B5371499
theorem B3352031 : Blo 550806 3352031 := bstep (se 1 (by rfl) ⟨2514023, by rfl⟩ : syracuseStep 3352031 = 5028047) B5028047
theorem B40281569 : Blo 550806 40281569 := bstep (se 2 (by rfl) ⟨15105588, by rfl⟩ : syracuseStep 40281569 = 30211177) B30211177
theorem B2369341 : Blo 550806 2369341 := bstep (se 3 (by rfl) ⟨444251, by rfl⟩ : syracuseStep 2369341 = 888503) B888503
theorem B6039593 : Blo 550806 6039593 := bstep (se 2 (by rfl) ⟨2264847, by rfl⟩ : syracuseStep 6039593 = 4529695) B4529695
theorem B4204871 : Blo 550806 4204871 := bstep (se 1 (by rfl) ⟨3153653, by rfl⟩ : syracuseStep 4204871 = 6307307) B6307307
theorem B14395877 : Blo 550806 14395877 := bstep (se 4 (by rfl) ⟨1349613, by rfl⟩ : syracuseStep 14395877 = 2699227) B2699227
theorem B5810791 : Blo 550806 5810791 := bstep (se 1 (by rfl) ⟨4358093, by rfl⟩ : syracuseStep 5810791 = 8716187) B8716187
theorem B830255 : Blo 550806 830255 := bstep (se 1 (by rfl) ⟨622691, by rfl⟩ : syracuseStep 830255 = 1245383) B1245383
theorem B7088957 : Blo 550806 7088957 := bstep (se 3 (by rfl) ⟨1329179, by rfl⟩ : syracuseStep 7088957 = 2658359) B2658359
theorem B830555 : Blo 550806 830555 := bstep (se 1 (by rfl) ⟨622916, by rfl⟩ : syracuseStep 830555 = 1245833) B1245833
theorem B830639 : Blo 550806 830639 := bstep (se 1 (by rfl) ⟨622979, by rfl⟩ : syracuseStep 830639 = 1245959) B1245959
theorem B830699 : Blo 550806 830699 := bstep (se 1 (by rfl) ⟨623024, by rfl⟩ : syracuseStep 830699 = 1246049) B1246049
theorem B831113 : Blo 550806 831113 := bstep (se 2 (by rfl) ⟨311667, by rfl⟩ : syracuseStep 831113 = 623335) B623335
theorem B4731371 : Blo 550806 4731371 := bstep (se 1 (by rfl) ⟨3548528, by rfl⟩ : syracuseStep 4731371 = 7097057) B7097057
theorem B931655 : Blo 550806 931655 := bstep (se 1 (by rfl) ⟨698741, by rfl⟩ : syracuseStep 931655 = 1397483) B1397483
theorem B933167 : Blo 550806 933167 := bstep (se 1 (by rfl) ⟨699875, by rfl⟩ : syracuseStep 933167 = 1399751) B1399751
theorem B998759 : Blo 550806 998759 := bstep (se 1 (by rfl) ⟨749069, by rfl⟩ : syracuseStep 998759 = 1498139) B1498139
theorem B934267 : Blo 550806 934267 := bstep (se 1 (by rfl) ⟨700700, by rfl⟩ : syracuseStep 934267 = 1401401) B1401401
theorem B3360865 : Blo 550806 3360865 := bstep (se 2 (by rfl) ⟨1260324, by rfl⟩ : syracuseStep 3360865 = 2520649) B2520649
theorem B2804705 : Blo 550806 2804705 := bstep (se 2 (by rfl) ⟨1051764, by rfl⟩ : syracuseStep 2804705 = 2103529) B2103529
theorem B83119601 : Blo 550806 83119601 := bstep (se 2 (by rfl) ⟨31169850, by rfl⟩ : syracuseStep 83119601 = 62339701) B62339701
theorem B17946521 : Blo 550806 17946521 := bstep (se 2 (by rfl) ⟨6729945, by rfl⟩ : syracuseStep 17946521 = 13459891) B13459891
theorem B1860191 : Blo 550806 1860191 := bstep (se 1 (by rfl) ⟨1395143, by rfl⟩ : syracuseStep 1860191 = 2790287) B2790287
theorem B942911 : Blo 550806 942911 := bstep (se 1 (by rfl) ⟨707183, by rfl⟩ : syracuseStep 942911 = 1414367) B1414367
theorem B1860947 : Blo 550806 1860947 := bstep (se 1 (by rfl) ⟨1395710, by rfl⟩ : syracuseStep 1860947 = 2791421) B2791421
theorem B183953207 : Blo 550806 183953207 := bstep (se 1 (by rfl) ⟨137964905, by rfl⟩ : syracuseStep 183953207 = 275929811) B275929811
theorem B2385721 : Blo 550806 2385721 := bstep (se 2 (by rfl) ⟨894645, by rfl⟩ : syracuseStep 2385721 = 1789291) B1789291
theorem B1992559 : Blo 550806 1992559 := bstep (se 1 (by rfl) ⟨1494419, by rfl⟩ : syracuseStep 1992559 = 2988839) B2988839
theorem B3795011 : Blo 550806 3795011 := bstep (se 1 (by rfl) ⟨2846258, by rfl⟩ : syracuseStep 3795011 = 5692517) B5692517
theorem B1861703 : Blo 550806 1861703 := bstep (se 1 (by rfl) ⟨1396277, by rfl⟩ : syracuseStep 1861703 = 2792555) B2792555
theorem B551023 : Blo 550806 551023 := bstep (se 1 (by rfl) ⟨413267, by rfl⟩ : syracuseStep 551023 = 826535) B826535
theorem B551515 : Blo 550806 551515 := bstep (se 1 (by rfl) ⟨413636, by rfl⟩ : syracuseStep 551515 = 827273) B827273
theorem B1239695 : Blo 550806 1239695 := bstep (se 1 (by rfl) ⟨929771, by rfl⟩ : syracuseStep 1239695 = 1859543) B1859543
theorem B4713227 : Blo 550806 4713227 := bstep (se 1 (by rfl) ⟨3534920, by rfl⟩ : syracuseStep 4713227 = 7069841) B7069841
theorem B1239929 : Blo 550806 1239929 := bstep (se 2 (by rfl) ⟨464973, by rfl⟩ : syracuseStep 1239929 = 929947) B929947
theorem B6318971 : Blo 550806 6318971 := bstep (se 1 (by rfl) ⟨4739228, by rfl⟩ : syracuseStep 6318971 = 9478457) B9478457
theorem B551807 : Blo 550806 551807 := bstep (se 1 (by rfl) ⟨413855, by rfl⟩ : syracuseStep 551807 = 827711) B827711
theorem B1240361 : Blo 550806 1240361 := bstep (se 2 (by rfl) ⟨465135, by rfl⟩ : syracuseStep 1240361 = 930271) B930271
theorem B1404287 : Blo 550806 1404287 := bstep (se 1 (by rfl) ⟨1053215, by rfl⟩ : syracuseStep 1404287 = 2106431) B2106431
theorem B552447 : Blo 550806 552447 := bstep (se 1 (by rfl) ⟨414335, by rfl⟩ : syracuseStep 552447 = 828671) B828671
theorem B1863593 : Blo 550806 1863593 := bstep (se 2 (by rfl) ⟨698847, by rfl⟩ : syracuseStep 1863593 = 1397695) B1397695
theorem B1994665 : Blo 550806 1994665 := bstep (se 2 (by rfl) ⟨747999, by rfl⟩ : syracuseStep 1994665 = 1495999) B1495999
theorem B1241225 : Blo 550806 1241225 := bstep (se 2 (by rfl) ⟨465459, by rfl⟩ : syracuseStep 1241225 = 930919) B930919
theorem B4190777 : Blo 550806 4190777 := bstep (se 2 (by rfl) ⟨1571541, by rfl⟩ : syracuseStep 4190777 = 3143083) B3143083
theorem B553583 : Blo 550806 553583 := bstep (se 1 (by rfl) ⟨415187, by rfl⟩ : syracuseStep 553583 = 830375) B830375
theorem B551580299 : Blo 550806 551580299 := bstep (se 1 (by rfl) ⟨413685224, by rfl⟩ : syracuseStep 551580299 = 827370449) B827370449
theorem B553679 : Blo 550806 553679 := bstep (se 1 (by rfl) ⟨415259, by rfl⟩ : syracuseStep 553679 = 830519) B830519
theorem B6288353 : Blo 550806 6288353 := bstep (se 2 (by rfl) ⟨2358132, by rfl⟩ : syracuseStep 6288353 = 4716265) B4716265
theorem B554011 : Blo 550806 554011 := bstep (se 1 (by rfl) ⟨415508, by rfl⟩ : syracuseStep 554011 = 831017) B831017
theorem B1242215 : Blo 550806 1242215 := bstep (se 1 (by rfl) ⟨931661, by rfl⟩ : syracuseStep 1242215 = 1863323) B1863323
theorem B1242233 : Blo 550806 1242233 := bstep (se 2 (by rfl) ⟨465837, by rfl⟩ : syracuseStep 1242233 = 931675) B931675
theorem B48527207 : Blo 550806 48527207 := bstep (se 1 (by rfl) ⟨36395405, by rfl⟩ : syracuseStep 48527207 = 72790811) B72790811
theorem B15169427 : Blo 550806 15169427 := bstep (se 1 (by rfl) ⟨11377070, by rfl⟩ : syracuseStep 15169427 = 22754141) B22754141
theorem B1767359 : Blo 550806 1767359 := bstep (se 1 (by rfl) ⟨1325519, by rfl⟩ : syracuseStep 1767359 = 2651039) B2651039
theorem B1243583 : Blo 550806 1243583 := bstep (se 1 (by rfl) ⟨932687, by rfl⟩ : syracuseStep 1243583 = 1865375) B1865375
theorem B621247 : Blo 550806 621247 := bstep (se 1 (by rfl) ⟨465935, by rfl⟩ : syracuseStep 621247 = 931871) B931871
theorem B1244663 : Blo 550806 1244663 := bstep (se 1 (by rfl) ⟨933497, by rfl⟩ : syracuseStep 1244663 = 1866995) B1866995
theorem B1245239 : Blo 550806 1245239 := bstep (se 1 (by rfl) ⟨933929, by rfl⟩ : syracuseStep 1245239 = 1867859) B1867859
theorem B1245689 : Blo 550806 1245689 := bstep (se 2 (by rfl) ⟨467133, by rfl⟩ : syracuseStep 1245689 = 934267) B934267
theorem B1573501 : Blo 550806 1573501 := bstep (se 3 (by rfl) ⟨295031, by rfl⟩ : syracuseStep 1573501 = 590063) B590063
theorem B1245851 : Blo 550806 1245851 := bstep (se 1 (by rfl) ⟨934388, by rfl⟩ : syracuseStep 1245851 = 1868777) B1868777
theorem B1246175 : Blo 550806 1246175 := bstep (se 1 (by rfl) ⟨934631, by rfl⟩ : syracuseStep 1246175 = 1869263) B1869263
theorem B1049593 : Blo 550806 1049593 := bstep (se 2 (by rfl) ⟨393597, by rfl⟩ : syracuseStep 1049593 = 787195) B787195
theorem B1246463 : Blo 550806 1246463 := bstep (se 1 (by rfl) ⟨934847, by rfl⟩ : syracuseStep 1246463 = 1869695) B1869695
theorem B1050079 : Blo 550806 1050079 := bstep (se 1 (by rfl) ⟨787559, by rfl⟩ : syracuseStep 1050079 = 1575119) B1575119
theorem B2098943 : Blo 550806 2098943 := bstep (se 1 (by rfl) ⟨1574207, by rfl⟩ : syracuseStep 2098943 = 3148415) B3148415
theorem B1869803 : Blo 550806 1869803 := bstep (se 1 (by rfl) ⟨1402352, by rfl⟩ : syracuseStep 1869803 = 2804705) B2804705
theorem B1771703 : Blo 550806 1771703 := bstep (se 1 (by rfl) ⟨1328777, by rfl⟩ : syracuseStep 1771703 = 2657555) B2657555
theorem B3147983 : Blo 550806 3147983 := bstep (se 1 (by rfl) ⟨2360987, by rfl⟩ : syracuseStep 3147983 = 4721975) B4721975
theorem B55413067 : Blo 550806 55413067 := bstep (se 1 (by rfl) ⟨41559800, by rfl⟩ : syracuseStep 55413067 = 83119601) B83119601
theorem B3180961 : Blo 550806 3180961 := bstep (se 2 (by rfl) ⟨1192860, by rfl⟩ : syracuseStep 3180961 = 2385721) B2385721
theorem B2656745 : Blo 550806 2656745 := bstep (se 2 (by rfl) ⟨996279, by rfl⟩ : syracuseStep 2656745 = 1992559) B1992559
theorem B789439 : Blo 550806 789439 := bstep (se 1 (by rfl) ⟨592079, by rfl⟩ : syracuseStep 789439 = 1184159) B1184159
theorem B2362439 : Blo 550806 2362439 := bstep (se 1 (by rfl) ⟨1771829, by rfl⟩ : syracuseStep 2362439 = 3543659) B3543659
theorem B11964347 : Blo 550806 11964347 := bstep (se 1 (by rfl) ⟨8973260, by rfl⟩ : syracuseStep 11964347 = 17946521) B17946521
theorem B4788371 : Blo 550806 4788371 := bstep (se 1 (by rfl) ⟨3591278, by rfl⟩ : syracuseStep 4788371 = 7182557) B7182557
theorem B2364079 : Blo 550806 2364079 := bstep (se 1 (by rfl) ⟨1773059, by rfl⟩ : syracuseStep 2364079 = 3546119) B3546119
theorem B2659553 : Blo 550806 2659553 := bstep (se 2 (by rfl) ⟨997332, by rfl⟩ : syracuseStep 2659553 = 1994665) B1994665
theorem B628607 : Blo 550806 628607 := bstep (se 1 (by rfl) ⟨471455, by rfl⟩ : syracuseStep 628607 = 942911) B942911
theorem B2234687 : Blo 550806 2234687 := bstep (se 1 (by rfl) ⟨1676015, by rfl⟩ : syracuseStep 2234687 = 3352031) B3352031
theorem B2530007 : Blo 550806 2530007 := bstep (se 1 (by rfl) ⟨1897505, by rfl⟩ : syracuseStep 2530007 = 3795011) B3795011
theorem B826463 : Blo 550806 826463 := bstep (se 1 (by rfl) ⟨619847, by rfl⟩ : syracuseStep 826463 = 1239695) B1239695
theorem B4725971 : Blo 550806 4725971 := bstep (se 1 (by rfl) ⟨3544478, by rfl⟩ : syracuseStep 4725971 = 7088957) B7088957
theorem B826619 : Blo 550806 826619 := bstep (se 1 (by rfl) ⟨619964, by rfl⟩ : syracuseStep 826619 = 1239929) B1239929
theorem B826907 : Blo 550806 826907 := bstep (se 1 (by rfl) ⟨620180, by rfl⟩ : syracuseStep 826907 = 1240361) B1240361
theorem B827483 : Blo 550806 827483 := bstep (se 1 (by rfl) ⟨620612, by rfl⟩ : syracuseStep 827483 = 1241225) B1241225
theorem B2367737 : Blo 550806 2367737 := bstep (se 2 (by rfl) ⟨887901, by rfl⟩ : syracuseStep 2367737 = 1775803) B1775803
theorem B3154247 : Blo 550806 3154247 := bstep (se 1 (by rfl) ⟨2365685, by rfl⟩ : syracuseStep 3154247 = 4731371) B4731371
theorem B2793851 : Blo 550806 2793851 := bstep (se 1 (by rfl) ⟨2095388, by rfl⟩ : syracuseStep 2793851 = 4190777) B4190777
theorem B828143 : Blo 550806 828143 := bstep (se 1 (by rfl) ⟨621107, by rfl⟩ : syracuseStep 828143 = 1242215) B1242215
theorem B828155 : Blo 550806 828155 := bstep (se 1 (by rfl) ⟨621116, by rfl⟩ : syracuseStep 828155 = 1242233) B1242233
theorem B828329 : Blo 550806 828329 := bstep (se 2 (by rfl) ⟨310623, by rfl⟩ : syracuseStep 828329 = 621247) B621247
theorem B32351471 : Blo 550806 32351471 := bstep (se 1 (by rfl) ⟨24263603, by rfl⟩ : syracuseStep 32351471 = 48527207) B48527207
theorem B829055 : Blo 550806 829055 := bstep (se 1 (by rfl) ⟨621791, by rfl⟩ : syracuseStep 829055 = 1243583) B1243583
theorem B2369513 : Blo 550806 2369513 := bstep (se 2 (by rfl) ⟨888567, by rfl⟩ : syracuseStep 2369513 = 1777135) B1777135
theorem B665839 : Blo 550806 665839 := bstep (se 1 (by rfl) ⟨499379, by rfl⟩ : syracuseStep 665839 = 998759) B998759
theorem B829775 : Blo 550806 829775 := bstep (se 1 (by rfl) ⟨622331, by rfl⟩ : syracuseStep 829775 = 1244663) B1244663
theorem B8956655 : Blo 550806 8956655 := bstep (se 1 (by rfl) ⟨6717491, by rfl⟩ : syracuseStep 8956655 = 13434983) B13434983
theorem B4729661 : Blo 550806 4729661 := bstep (se 3 (by rfl) ⟨886811, by rfl⟩ : syracuseStep 4729661 = 1773623) B1773623
theorem B831431 : Blo 550806 831431 := bstep (se 1 (by rfl) ⟨623573, by rfl⟩ : syracuseStep 831431 = 1247147) B1247147
theorem B831599 : Blo 550806 831599 := bstep (se 1 (by rfl) ⟨623699, by rfl⟩ : syracuseStep 831599 = 1247399) B1247399
theorem B58831667 : Blo 550806 58831667 := bstep (se 1 (by rfl) ⟨44123750, by rfl⟩ : syracuseStep 58831667 = 88247501) B88247501
theorem B3159121 : Blo 550806 3159121 := bstep (se 2 (by rfl) ⟨1184670, by rfl⟩ : syracuseStep 3159121 = 2369341) B2369341
theorem B9680435 : Blo 550806 9680435 := bstep (se 1 (by rfl) ⟨7260326, by rfl⟩ : syracuseStep 9680435 = 14520653) B14520653
theorem B7747721 : Blo 550806 7747721 := bstep (se 2 (by rfl) ⟨2905395, by rfl⟩ : syracuseStep 7747721 = 5810791) B5810791
theorem B26854379 : Blo 550806 26854379 := bstep (se 1 (by rfl) ⟨20140784, by rfl⟩ : syracuseStep 26854379 = 40281569) B40281569
theorem B122635471 : Blo 550806 122635471 := bstep (se 1 (by rfl) ⟨91976603, by rfl⟩ : syracuseStep 122635471 = 183953207) B183953207
theorem B2803247 : Blo 550806 2803247 := bstep (se 1 (by rfl) ⟨2102435, by rfl⟩ : syracuseStep 2803247 = 4204871) B4204871
theorem B4212647 : Blo 550806 4212647 := bstep (se 1 (by rfl) ⟨3159485, by rfl⟩ : syracuseStep 4212647 = 6318971) B6318971
theorem B936191 : Blo 550806 936191 := bstep (se 1 (by rfl) ⟨702143, by rfl⟩ : syracuseStep 936191 = 1404287) B1404287
theorem B10112951 : Blo 550806 10112951 := bstep (se 1 (by rfl) ⟨7584713, by rfl⟩ : syracuseStep 10112951 = 15169427) B15169427
theorem B2806973 : Blo 550806 2806973 := bstep (se 3 (by rfl) ⟨526307, by rfl⟩ : syracuseStep 2806973 = 1052615) B1052615
theorem B13458251 : Blo 550806 13458251 := bstep (se 1 (by rfl) ⟨10093688, by rfl⟩ : syracuseStep 13458251 = 20187377) B20187377
theorem B12802981 : Blo 550806 12802981 := bstep (se 4 (by rfl) ⟨1200279, by rfl⟩ : syracuseStep 12802981 = 2400559) B2400559
theorem B1399801 : Blo 550806 1399801 := bstep (se 2 (by rfl) ⟨524925, by rfl⟩ : syracuseStep 1399801 = 1049851) B1049851
theorem B19160171 : Blo 550806 19160171 := bstep (se 1 (by rfl) ⟨14370128, by rfl⟩ : syracuseStep 19160171 = 28740257) B28740257
theorem B745129 : Blo 550806 745129 := bstep (se 2 (by rfl) ⟨279423, by rfl⟩ : syracuseStep 745129 = 558847) B558847
theorem B1859327 : Blo 550806 1859327 := bstep (se 1 (by rfl) ⟨1394495, by rfl⟩ : syracuseStep 1859327 = 2788991) B2788991
theorem B4481153 : Blo 550806 4481153 := bstep (se 2 (by rfl) ⟨1680432, by rfl⟩ : syracuseStep 4481153 = 3360865) B3360865
theorem B4481831 : Blo 550806 4481831 := bstep (se 1 (by rfl) ⟨3361373, by rfl⟩ : syracuseStep 4481831 = 6722747) B6722747
theorem B943663 : Blo 550806 943663 := bstep (se 1 (by rfl) ⟨707747, by rfl⟩ : syracuseStep 943663 = 1415495) B1415495
theorem B1861487 : Blo 550806 1861487 := bstep (se 1 (by rfl) ⟨1396115, by rfl⟩ : syracuseStep 1861487 = 2792231) B2792231
theorem B551967 : Blo 550806 551967 := bstep (se 1 (by rfl) ⟨413975, by rfl⟩ : syracuseStep 551967 = 827951) B827951
theorem B19098661 : Blo 550806 19098661 := bstep (se 4 (by rfl) ⟨1790499, by rfl⟩ : syracuseStep 19098661 = 3580999) B3580999
theorem B1240127 : Blo 550806 1240127 := bstep (se 1 (by rfl) ⟨930095, by rfl⟩ : syracuseStep 1240127 = 1860191) B1860191
theorem B1994003 : Blo 550806 1994003 := bstep (se 1 (by rfl) ⟨1495502, by rfl⟩ : syracuseStep 1994003 = 2991005) B2991005
theorem B1240631 : Blo 550806 1240631 := bstep (se 1 (by rfl) ⟨930473, by rfl⟩ : syracuseStep 1240631 = 1860947) B1860947
theorem B4026395 : Blo 550806 4026395 := bstep (se 1 (by rfl) ⟨3019796, by rfl⟩ : syracuseStep 4026395 = 6039593) B6039593
theorem B1241135 : Blo 550806 1241135 := bstep (se 1 (by rfl) ⟨930851, by rfl⟩ : syracuseStep 1241135 = 1861703) B1861703
theorem B9597251 : Blo 550806 9597251 := bstep (se 1 (by rfl) ⟨7197938, by rfl⟩ : syracuseStep 9597251 = 14395877) B14395877
theorem B3142151 : Blo 550806 3142151 := bstep (se 1 (by rfl) ⟨2356613, by rfl⟩ : syracuseStep 3142151 = 4713227) B4713227
theorem B553503 : Blo 550806 553503 := bstep (se 1 (by rfl) ⟨415127, by rfl⟩ : syracuseStep 553503 = 830255) B830255
theorem B553703 : Blo 550806 553703 := bstep (se 1 (by rfl) ⟨415277, by rfl⟩ : syracuseStep 553703 = 830555) B830555
theorem B553759 : Blo 550806 553759 := bstep (se 1 (by rfl) ⟨415319, by rfl⟩ : syracuseStep 553759 = 830639) B830639
theorem B553799 : Blo 550806 553799 := bstep (se 1 (by rfl) ⟨415349, by rfl⟩ : syracuseStep 553799 = 830699) B830699
theorem B554075 : Blo 550806 554075 := bstep (se 1 (by rfl) ⟨415556, by rfl⟩ : syracuseStep 554075 = 831113) B831113
theorem B1242395 : Blo 550806 1242395 := bstep (se 1 (by rfl) ⟨931796, by rfl⟩ : syracuseStep 1242395 = 1863593) B1863593
theorem B1766909 : Blo 550806 1766909 := bstep (se 3 (by rfl) ⟨331295, by rfl⟩ : syracuseStep 1766909 = 662591) B662591
theorem B367720199 : Blo 550806 367720199 := bstep (se 1 (by rfl) ⟨275790149, by rfl⟩ : syracuseStep 367720199 = 551580299) B551580299
theorem B4192235 : Blo 550806 4192235 := bstep (se 1 (by rfl) ⟨3144176, by rfl⟩ : syracuseStep 4192235 = 6288353) B6288353
theorem B621103 : Blo 550806 621103 := bstep (se 1 (by rfl) ⟨465827, by rfl⟩ : syracuseStep 621103 = 931655) B931655
theorem B1178239 : Blo 550806 1178239 := bstep (se 1 (by rfl) ⟨883679, by rfl⟩ : syracuseStep 1178239 = 1767359) B1767359
theorem B22117313 : Blo 550806 22117313 := bstep (se 2 (by rfl) ⟨8293992, by rfl⟩ : syracuseStep 22117313 = 16587985) B16587985
theorem B622111 : Blo 550806 622111 := bstep (se 1 (by rfl) ⟨466583, by rfl⟩ : syracuseStep 622111 = 933167) B933167
theorem B2098001 : Blo 550806 2098001 := bstep (se 2 (by rfl) ⟨786750, by rfl⟩ : syracuseStep 2098001 = 1573501) B1573501
theorem B25592669 : Blo 550806 25592669 := bstep (se 3 (by rfl) ⟨4798625, by rfl⟩ : syracuseStep 25592669 = 9597251) B9597251
theorem B1868831 : Blo 550806 1868831 := bstep (se 1 (by rfl) ⟨1401623, by rfl⟩ : syracuseStep 1868831 = 2803247) B2803247
theorem B1246535 : Blo 550806 1246535 := bstep (se 1 (by rfl) ⟨934901, by rfl⟩ : syracuseStep 1246535 = 1869803) B1869803
theorem B1181135 : Blo 550806 1181135 := bstep (se 1 (by rfl) ⟨885851, by rfl⟩ : syracuseStep 1181135 = 1771703) B1771703
theorem B2098655 : Blo 550806 2098655 := bstep (se 1 (by rfl) ⟨1573991, by rfl⟩ : syracuseStep 2098655 = 3147983) B3147983
theorem B624127 : Blo 550806 624127 := bstep (se 1 (by rfl) ⟨468095, by rfl⟩ : syracuseStep 624127 = 936191) B936191
theorem B163513961 : Blo 550806 163513961 := bstep (se 2 (by rfl) ⟨61317735, by rfl⟩ : syracuseStep 163513961 = 122635471) B122635471
theorem B1771163 : Blo 550806 1771163 := bstep (se 1 (by rfl) ⟨1328372, by rfl⟩ : syracuseStep 1771163 = 2656745) B2656745
theorem B1574959 : Blo 550806 1574959 := bstep (se 1 (by rfl) ⟨1181219, by rfl⟩ : syracuseStep 1574959 = 2362439) B2362439
theorem B1871315 : Blo 550806 1871315 := bstep (se 1 (by rfl) ⟨1403486, by rfl⟩ : syracuseStep 1871315 = 2806973) B2806973
theorem B1773035 : Blo 550806 1773035 := bstep (se 1 (by rfl) ⟨1329776, by rfl⟩ : syracuseStep 1773035 = 2659553) B2659553
theorem B1052585 : Blo 550806 1052585 := bstep (se 2 (by rfl) ⟨394719, by rfl⟩ : syracuseStep 1052585 = 789439) B789439
theorem B25464881 : Blo 550806 25464881 := bstep (se 2 (by rfl) ⟨9549330, by rfl⟩ : syracuseStep 25464881 = 19098661) B19098661
theorem B3150647 : Blo 550806 3150647 := bstep (se 1 (by rfl) ⟨2362985, by rfl⟩ : syracuseStep 3150647 = 4725971) B4725971
theorem B1676285 : Blo 550806 1676285 := bstep (se 3 (by rfl) ⟨314303, by rfl⟩ : syracuseStep 1676285 = 628607) B628607
theorem B2987435 : Blo 550806 2987435 := bstep (se 1 (by rfl) ⟨2240576, by rfl⟩ : syracuseStep 2987435 = 4481153) B4481153
theorem B1578491 : Blo 550806 1578491 := bstep (se 1 (by rfl) ⟨1183868, by rfl⟩ : syracuseStep 1578491 = 2367737) B2367737
theorem B2102831 : Blo 550806 2102831 := bstep (se 1 (by rfl) ⟨1577123, by rfl⟩ : syracuseStep 2102831 = 3154247) B3154247
theorem B2987887 : Blo 550806 2987887 := bstep (se 1 (by rfl) ⟨2240915, by rfl⟩ : syracuseStep 2987887 = 4481831) B4481831
theorem B21567647 : Blo 550806 21567647 := bstep (se 1 (by rfl) ⟨16175735, by rfl⟩ : syracuseStep 21567647 = 32351471) B32351471
theorem B3152105 : Blo 550806 3152105 := bstep (se 2 (by rfl) ⟨1182039, by rfl⟩ : syracuseStep 3152105 = 2364079) B2364079
theorem B1579675 : Blo 550806 1579675 := bstep (se 1 (by rfl) ⟨1184756, by rfl⟩ : syracuseStep 1579675 = 2369513) B2369513
theorem B5971103 : Blo 550806 5971103 := bstep (se 1 (by rfl) ⟨4478327, by rfl⟩ : syracuseStep 5971103 = 8956655) B8956655
theorem B3153107 : Blo 550806 3153107 := bstep (se 1 (by rfl) ⟨2364830, by rfl⟩ : syracuseStep 3153107 = 4729661) B4729661
theorem B826751 : Blo 550806 826751 := bstep (se 1 (by rfl) ⟨620063, by rfl⟩ : syracuseStep 826751 = 1240127) B1240127
theorem B827087 : Blo 550806 827087 := bstep (se 1 (by rfl) ⟨620315, by rfl⟩ : syracuseStep 827087 = 1240631) B1240631
theorem B827423 : Blo 550806 827423 := bstep (se 1 (by rfl) ⟨620567, by rfl⟩ : syracuseStep 827423 = 1241135) B1241135
theorem B828137 : Blo 550806 828137 := bstep (se 2 (by rfl) ⟨310551, by rfl⟩ : syracuseStep 828137 = 621103) B621103
theorem B828263 : Blo 550806 828263 := bstep (se 1 (by rfl) ⟨621197, by rfl⟩ : syracuseStep 828263 = 1242395) B1242395
theorem B3974021 : Blo 550806 3974021 := bstep (se 4 (by rfl) ⟨372564, by rfl⟩ : syracuseStep 3974021 = 745129) B745129
theorem B245146799 : Blo 550806 245146799 := bstep (se 1 (by rfl) ⟨183860099, by rfl⟩ : syracuseStep 245146799 = 367720199) B367720199
theorem B2794823 : Blo 550806 2794823 := bstep (se 1 (by rfl) ⟨2096117, by rfl⟩ : syracuseStep 2794823 = 4192235) B4192235
theorem B829481 : Blo 550806 829481 := bstep (se 2 (by rfl) ⟨311055, by rfl⟩ : syracuseStep 829481 = 622111) B622111
theorem B830159 : Blo 550806 830159 := bstep (se 1 (by rfl) ⟨622619, by rfl⟩ : syracuseStep 830159 = 1245239) B1245239
theorem B830459 : Blo 550806 830459 := bstep (se 1 (by rfl) ⟨622844, by rfl⟩ : syracuseStep 830459 = 1245689) B1245689
theorem B830567 : Blo 550806 830567 := bstep (se 1 (by rfl) ⟨622925, by rfl⟩ : syracuseStep 830567 = 1245851) B1245851
theorem B830783 : Blo 550806 830783 := bstep (se 1 (by rfl) ⟨623087, by rfl⟩ : syracuseStep 830783 = 1246175) B1246175
theorem B17902919 : Blo 550806 17902919 := bstep (se 1 (by rfl) ⟨13427189, by rfl⟩ : syracuseStep 17902919 = 26854379) B26854379
theorem B830975 : Blo 550806 830975 := bstep (se 1 (by rfl) ⟨623231, by rfl⟩ : syracuseStep 830975 = 1246463) B1246463
theorem B3551141 : Blo 550806 3551141 := bstep (se 4 (by rfl) ⟨332919, by rfl⟩ : syracuseStep 3551141 = 665839) B665839
theorem B1258217 : Blo 550806 1258217 := bstep (se 2 (by rfl) ⟨471831, by rfl⟩ : syracuseStep 1258217 = 943663) B943663
theorem B7976231 : Blo 550806 7976231 := bstep (se 1 (by rfl) ⟨5982173, by rfl⟩ : syracuseStep 7976231 = 11964347) B11964347
theorem B3192247 : Blo 550806 3192247 := bstep (se 1 (by rfl) ⟨2394185, by rfl⟩ : syracuseStep 3192247 = 4788371) B4788371
theorem B4241281 : Blo 550806 4241281 := bstep (se 2 (by rfl) ⟨1590480, by rfl⟩ : syracuseStep 4241281 = 3180961) B3180961
theorem B1686671 : Blo 550806 1686671 := bstep (se 1 (by rfl) ⟨1265003, by rfl⟩ : syracuseStep 1686671 = 2530007) B2530007
theorem B4212161 : Blo 550806 4212161 := bstep (se 2 (by rfl) ⟨1579560, by rfl⟩ : syracuseStep 4212161 = 3159121) B3159121
theorem B1329335 : Blo 550806 1329335 := bstep (se 1 (by rfl) ⟨997001, by rfl⟩ : syracuseStep 1329335 = 1994003) B1994003
theorem B5165147 : Blo 550806 5165147 := bstep (se 1 (by rfl) ⟨3873860, by rfl⟩ : syracuseStep 5165147 = 7747721) B7747721
theorem B1399295 : Blo 550806 1399295 := bstep (se 1 (by rfl) ⟨1049471, by rfl⟩ : syracuseStep 1399295 = 2098943) B2098943
theorem B2808431 : Blo 550806 2808431 := bstep (se 1 (by rfl) ⟨2106323, by rfl⟩ : syracuseStep 2808431 = 4212647) B4212647
theorem B1399457 : Blo 550806 1399457 := bstep (se 2 (by rfl) ⟨524796, by rfl⟩ : syracuseStep 1399457 = 1049593) B1049593
theorem B1400105 : Blo 550806 1400105 := bstep (se 2 (by rfl) ⟨525039, by rfl⟩ : syracuseStep 1400105 = 1050079) B1050079
theorem B6741967 : Blo 550806 6741967 := bstep (se 1 (by rfl) ⟨5056475, by rfl⟩ : syracuseStep 6741967 = 10112951) B10112951
theorem B73884089 : Blo 550806 73884089 := bstep (se 2 (by rfl) ⟨27706533, by rfl⟩ : syracuseStep 73884089 = 55413067) B55413067
theorem B8972167 : Blo 550806 8972167 := bstep (se 1 (by rfl) ⟨6729125, by rfl⟩ : syracuseStep 8972167 = 13458251) B13458251
theorem B550975 : Blo 550806 550975 := bstep (se 1 (by rfl) ⟨413231, by rfl⟩ : syracuseStep 550975 = 826463) B826463
theorem B12773447 : Blo 550806 12773447 := bstep (se 1 (by rfl) ⟨9580085, by rfl⟩ : syracuseStep 12773447 = 19160171) B19160171
theorem B551079 : Blo 550806 551079 := bstep (se 1 (by rfl) ⟨413309, by rfl⟩ : syracuseStep 551079 = 826619) B826619
theorem B551271 : Blo 550806 551271 := bstep (se 1 (by rfl) ⟨413453, by rfl⟩ : syracuseStep 551271 = 826907) B826907
theorem B1239551 : Blo 550806 1239551 := bstep (se 1 (by rfl) ⟨929663, by rfl⟩ : syracuseStep 1239551 = 1859327) B1859327
theorem B551655 : Blo 550806 551655 := bstep (se 1 (by rfl) ⟨413741, by rfl⟩ : syracuseStep 551655 = 827483) B827483
theorem B1862567 : Blo 550806 1862567 := bstep (se 1 (by rfl) ⟨1396925, by rfl⟩ : syracuseStep 1862567 = 2793851) B2793851
theorem B552095 : Blo 550806 552095 := bstep (se 1 (by rfl) ⟨414071, by rfl⟩ : syracuseStep 552095 = 828143) B828143
theorem B552103 : Blo 550806 552103 := bstep (se 1 (by rfl) ⟨414077, by rfl⟩ : syracuseStep 552103 = 828155) B828155
theorem B552219 : Blo 550806 552219 := bstep (se 1 (by rfl) ⟨414164, by rfl⟩ : syracuseStep 552219 = 828329) B828329
theorem B5959165 : Blo 550806 5959165 := bstep (se 3 (by rfl) ⟨1117343, by rfl⟩ : syracuseStep 5959165 = 2234687) B2234687
theorem B552703 : Blo 550806 552703 := bstep (se 1 (by rfl) ⟨414527, by rfl⟩ : syracuseStep 552703 = 829055) B829055
theorem B1240991 : Blo 550806 1240991 := bstep (se 1 (by rfl) ⟨930743, by rfl⟩ : syracuseStep 1240991 = 1861487) B1861487
theorem B553183 : Blo 550806 553183 := bstep (se 1 (by rfl) ⟨414887, by rfl⟩ : syracuseStep 553183 = 829775) B829775
theorem B554287 : Blo 550806 554287 := bstep (se 1 (by rfl) ⟨415715, by rfl⟩ : syracuseStep 554287 = 831431) B831431
theorem B2684263 : Blo 550806 2684263 := bstep (se 1 (by rfl) ⟨2013197, by rfl⟩ : syracuseStep 2684263 = 4026395) B4026395
theorem B554399 : Blo 550806 554399 := bstep (se 1 (by rfl) ⟨415799, by rfl⟩ : syracuseStep 554399 = 831599) B831599
theorem B2094767 : Blo 550806 2094767 := bstep (se 1 (by rfl) ⟨1571075, by rfl⟩ : syracuseStep 2094767 = 3142151) B3142151
theorem B39221111 : Blo 550806 39221111 := bstep (se 1 (by rfl) ⟨29415833, by rfl⟩ : syracuseStep 39221111 = 58831667) B58831667
theorem B1570985 : Blo 550806 1570985 := bstep (se 2 (by rfl) ⟨589119, by rfl⟩ : syracuseStep 1570985 = 1178239) B1178239
theorem B1177939 : Blo 550806 1177939 := bstep (se 1 (by rfl) ⟨883454, by rfl⟩ : syracuseStep 1177939 = 1766909) B1766909
theorem B6453623 : Blo 550806 6453623 := bstep (se 1 (by rfl) ⟨4840217, by rfl⟩ : syracuseStep 6453623 = 9680435) B9680435
theorem B17070641 : Blo 550806 17070641 := bstep (se 2 (by rfl) ⟨6401490, by rfl⟩ : syracuseStep 17070641 = 12802981) B12802981
theorem B1866401 : Blo 550806 1866401 := bstep (se 2 (by rfl) ⟨699900, by rfl⟩ : syracuseStep 1866401 = 1399801) B1399801
theorem B14744875 : Blo 550806 14744875 := bstep (se 1 (by rfl) ⟨11058656, by rfl⟩ : syracuseStep 14744875 = 22117313) B22117313
theorem B1245887 : Blo 550806 1245887 := bstep (se 1 (by rfl) ⟨934415, by rfl⟩ : syracuseStep 1245887 = 1868831) B1868831
theorem B787423 : Blo 550806 787423 := bstep (se 1 (by rfl) ⟨590567, by rfl⟩ : syracuseStep 787423 = 1181135) B1181135
theorem B1180775 : Blo 550806 1180775 := bstep (se 1 (by rfl) ⟨885581, by rfl⟩ : syracuseStep 1180775 = 1771163) B1771163
theorem B886223 : Blo 550806 886223 := bstep (se 1 (by rfl) ⟨664667, by rfl⟩ : syracuseStep 886223 = 1329335) B1329335
theorem B1247543 : Blo 550806 1247543 := bstep (se 1 (by rfl) ⟨935657, by rfl⟩ : syracuseStep 1247543 = 1871315) B1871315
theorem B1182023 : Blo 550806 1182023 := bstep (se 1 (by rfl) ⟨886517, by rfl⟩ : syracuseStep 1182023 = 1773035) B1773035
theorem B11962889 : Blo 550806 11962889 := bstep (se 2 (by rfl) ⟨4486083, by rfl⟩ : syracuseStep 11962889 = 8972167) B8972167
theorem B16976587 : Blo 550806 16976587 := bstep (se 1 (by rfl) ⟨12732440, by rfl⟩ : syracuseStep 16976587 = 25464881) B25464881
theorem B2099945 : Blo 550806 2099945 := bstep (se 2 (by rfl) ⟨787479, by rfl⟩ : syracuseStep 2099945 = 1574959) B1574959
theorem B2100431 : Blo 550806 2100431 := bstep (se 1 (by rfl) ⟨1575323, by rfl⟩ : syracuseStep 2100431 = 3150647) B3150647
theorem B1117523 : Blo 550806 1117523 := bstep (se 1 (by rfl) ⟨838142, by rfl⟩ : syracuseStep 1117523 = 1676285) B1676285
theorem B1052327 : Blo 550806 1052327 := bstep (se 1 (by rfl) ⟨789245, by rfl⟩ : syracuseStep 1052327 = 1578491) B1578491
theorem B2101403 : Blo 550806 2101403 := bstep (se 1 (by rfl) ⟨1576052, by rfl⟩ : syracuseStep 2101403 = 3152105) B3152105
theorem B1872287 : Blo 550806 1872287 := bstep (se 1 (by rfl) ⟨1404215, by rfl⟩ : syracuseStep 1872287 = 2808431) B2808431
theorem B2102071 : Blo 550806 2102071 := bstep (se 1 (by rfl) ⟨1576553, by rfl⟩ : syracuseStep 2102071 = 3153107) B3153107
theorem B49256059 : Blo 550806 49256059 := bstep (se 1 (by rfl) ⟨36942044, by rfl⟩ : syracuseStep 49256059 = 73884089) B73884089
theorem B826367 : Blo 550806 826367 := bstep (se 1 (by rfl) ⟨619775, by rfl⟩ : syracuseStep 826367 = 1239551) B1239551
theorem B3579017 : Blo 550806 3579017 := bstep (se 2 (by rfl) ⟨1342131, by rfl⟩ : syracuseStep 3579017 = 2684263) B2684263
theorem B11935279 : Blo 550806 11935279 := bstep (se 1 (by rfl) ⟨8951459, by rfl⟩ : syracuseStep 11935279 = 17902919) B17902919
theorem B827327 : Blo 550806 827327 := bstep (se 1 (by rfl) ⟨620495, by rfl⟩ : syracuseStep 827327 = 1240991) B1240991
theorem B5317487 : Blo 550806 5317487 := bstep (se 1 (by rfl) ⟨3988115, by rfl⟩ : syracuseStep 5317487 = 7976231) B7976231
theorem B2106233 : Blo 550806 2106233 := bstep (se 2 (by rfl) ⟨789837, by rfl⟩ : syracuseStep 2106233 = 1579675) B1579675
theorem B4302415 : Blo 550806 4302415 := bstep (se 1 (by rfl) ⟨3226811, by rfl⟩ : syracuseStep 4302415 = 6453623) B6453623
theorem B11380427 : Blo 550806 11380427 := bstep (se 1 (by rfl) ⟨8535320, by rfl⟩ : syracuseStep 11380427 = 17070641) B17070641
theorem B1124447 : Blo 550806 1124447 := bstep (se 1 (by rfl) ⟨843335, by rfl⟩ : syracuseStep 1124447 = 1686671) B1686671
theorem B8989289 : Blo 550806 8989289 := bstep (se 2 (by rfl) ⟨3370983, by rfl⟩ : syracuseStep 8989289 = 6741967) B6741967
theorem B13773725 : Blo 550806 13773725 := bstep (se 3 (by rfl) ⟨2582573, by rfl⟩ : syracuseStep 13773725 = 5165147) B5165147
theorem B831023 : Blo 550806 831023 := bstep (se 1 (by rfl) ⟨623267, by rfl⟩ : syracuseStep 831023 = 1246535) B1246535
theorem B832169 : Blo 550806 832169 := bstep (se 2 (by rfl) ⟨312063, by rfl⟩ : syracuseStep 832169 = 624127) B624127
theorem B701723 : Blo 550806 701723 := bstep (se 1 (by rfl) ⟨526292, by rfl⟩ : syracuseStep 701723 = 1052585) B1052585
theorem B932863 : Blo 550806 932863 := bstep (se 1 (by rfl) ⟨699647, by rfl⟩ : syracuseStep 932863 = 1399295) B1399295
theorem B932971 : Blo 550806 932971 := bstep (se 1 (by rfl) ⟨699728, by rfl⟩ : syracuseStep 932971 = 1399457) B1399457
theorem B7945553 : Blo 550806 7945553 := bstep (se 2 (by rfl) ⟨2979582, by rfl⟩ : syracuseStep 7945553 = 5959165) B5959165
theorem B3980735 : Blo 550806 3980735 := bstep (se 1 (by rfl) ⟨2985551, by rfl⟩ : syracuseStep 3980735 = 5971103) B5971103
theorem B933403 : Blo 550806 933403 := bstep (se 1 (by rfl) ⟨700052, by rfl⟩ : syracuseStep 933403 = 1400105) B1400105
theorem B163431199 : Blo 550806 163431199 := bstep (se 1 (by rfl) ⟨122573399, by rfl⟩ : syracuseStep 163431199 = 245146799) B245146799
theorem B3983849 : Blo 550806 3983849 := bstep (se 2 (by rfl) ⟨1493943, by rfl⟩ : syracuseStep 3983849 = 2987887) B2987887
theorem B5655041 : Blo 550806 5655041 := bstep (se 2 (by rfl) ⟨2120640, by rfl⟩ : syracuseStep 5655041 = 4241281) B4241281
theorem B838811 : Blo 550806 838811 := bstep (se 1 (by rfl) ⟨629108, by rfl⟩ : syracuseStep 838811 = 1258217) B1258217
theorem B1396511 : Blo 550806 1396511 := bstep (se 1 (by rfl) ⟨1047383, by rfl⟩ : syracuseStep 1396511 = 2094767) B2094767
theorem B1398667 : Blo 550806 1398667 := bstep (se 1 (by rfl) ⟨1049000, by rfl⟩ : syracuseStep 1398667 = 2098001) B2098001
theorem B17061779 : Blo 550806 17061779 := bstep (se 1 (by rfl) ⟨12796334, by rfl⟩ : syracuseStep 17061779 = 25592669) B25592669
theorem B2808107 : Blo 550806 2808107 := bstep (se 1 (by rfl) ⟨2106080, by rfl⟩ : syracuseStep 2808107 = 4212161) B4212161
theorem B1399103 : Blo 550806 1399103 := bstep (se 1 (by rfl) ⟨1049327, by rfl⟩ : syracuseStep 1399103 = 2098655) B2098655
theorem B109009307 : Blo 550806 109009307 := bstep (se 1 (by rfl) ⟨81756980, by rfl⟩ : syracuseStep 109009307 = 163513961) B163513961
theorem B1991623 : Blo 550806 1991623 := bstep (se 1 (by rfl) ⟨1493717, by rfl⟩ : syracuseStep 1991623 = 2987435) B2987435
theorem B1401887 : Blo 550806 1401887 := bstep (se 1 (by rfl) ⟨1051415, by rfl⟩ : syracuseStep 1401887 = 2102831) B2102831
theorem B14378431 : Blo 550806 14378431 := bstep (se 1 (by rfl) ⟨10783823, by rfl⟩ : syracuseStep 14378431 = 21567647) B21567647
theorem B551167 : Blo 550806 551167 := bstep (se 1 (by rfl) ⟨413375, by rfl⟩ : syracuseStep 551167 = 826751) B826751
theorem B551391 : Blo 550806 551391 := bstep (se 1 (by rfl) ⟨413543, by rfl⟩ : syracuseStep 551391 = 827087) B827087
theorem B551615 : Blo 550806 551615 := bstep (se 1 (by rfl) ⟨413711, by rfl⟩ : syracuseStep 551615 = 827423) B827423
theorem B552091 : Blo 550806 552091 := bstep (se 1 (by rfl) ⟨414068, by rfl⟩ : syracuseStep 552091 = 828137) B828137
theorem B552175 : Blo 550806 552175 := bstep (se 1 (by rfl) ⟨414131, by rfl⟩ : syracuseStep 552175 = 828263) B828263
theorem B2649347 : Blo 550806 2649347 := bstep (se 1 (by rfl) ⟨1987010, by rfl⟩ : syracuseStep 2649347 = 3974021) B3974021
theorem B1863215 : Blo 550806 1863215 := bstep (se 1 (by rfl) ⟨1397411, by rfl⟩ : syracuseStep 1863215 = 2794823) B2794823
theorem B552987 : Blo 550806 552987 := bstep (se 1 (by rfl) ⟨414740, by rfl⟩ : syracuseStep 552987 = 829481) B829481
theorem B8515631 : Blo 550806 8515631 := bstep (se 1 (by rfl) ⟨6386723, by rfl⟩ : syracuseStep 8515631 = 12773447) B12773447
theorem B553439 : Blo 550806 553439 := bstep (se 1 (by rfl) ⟨415079, by rfl⟩ : syracuseStep 553439 = 830159) B830159
theorem B4256329 : Blo 550806 4256329 := bstep (se 2 (by rfl) ⟨1596123, by rfl⟩ : syracuseStep 4256329 = 3192247) B3192247
theorem B1241711 : Blo 550806 1241711 := bstep (se 1 (by rfl) ⟨931283, by rfl⟩ : syracuseStep 1241711 = 1862567) B1862567
theorem B553639 : Blo 550806 553639 := bstep (se 1 (by rfl) ⟨415229, by rfl⟩ : syracuseStep 553639 = 830459) B830459
theorem B553711 : Blo 550806 553711 := bstep (se 1 (by rfl) ⟨415283, by rfl⟩ : syracuseStep 553711 = 830567) B830567
theorem B553855 : Blo 550806 553855 := bstep (se 1 (by rfl) ⟨415391, by rfl⟩ : syracuseStep 553855 = 830783) B830783
theorem B553983 : Blo 550806 553983 := bstep (se 1 (by rfl) ⟨415487, by rfl⟩ : syracuseStep 553983 = 830975) B830975
theorem B1570585 : Blo 550806 1570585 := bstep (se 2 (by rfl) ⟨588969, by rfl⟩ : syracuseStep 1570585 = 1177939) B1177939
theorem B26147407 : Blo 550806 26147407 := bstep (se 1 (by rfl) ⟨19610555, by rfl⟩ : syracuseStep 26147407 = 39221111) B39221111
theorem B1047323 : Blo 550806 1047323 := bstep (se 1 (by rfl) ⟨785492, by rfl⟩ : syracuseStep 1047323 = 1570985) B1570985
theorem B19659833 : Blo 550806 19659833 := bstep (se 2 (by rfl) ⟨7372437, by rfl⟩ : syracuseStep 19659833 = 14744875) B14744875
theorem B1244267 : Blo 550806 1244267 := bstep (se 1 (by rfl) ⟨933200, by rfl⟩ : syracuseStep 1244267 = 1866401) B1866401
theorem B9469709 : Blo 550806 9469709 := bstep (se 3 (by rfl) ⟨1775570, by rfl⟩ : syracuseStep 9469709 = 3551141) B3551141
theorem B590815 : Blo 550806 590815 := bstep (se 1 (by rfl) ⟨443111, by rfl⟩ : syracuseStep 590815 = 886223) B886223
theorem B11994101 : Blo 550806 11994101 := bstep (se 5 (by rfl) ⟨562223, by rfl⟩ : syracuseStep 11994101 = 1124447) B1124447
theorem B217908265 : Blo 550806 217908265 := bstep (se 2 (by rfl) ⟨81715599, by rfl⟩ : syracuseStep 217908265 = 163431199) B163431199
theorem B2655497 : Blo 550806 2655497 := bstep (se 2 (by rfl) ⟨995811, by rfl⟩ : syracuseStep 2655497 = 1991623) B1991623
theorem B1049897 : Blo 550806 1049897 := bstep (se 2 (by rfl) ⟨393711, by rfl⟩ : syracuseStep 1049897 = 787423) B787423
theorem B38176181 : Blo 550806 38176181 := bstep (se 5 (by rfl) ⟨1789508, by rfl⟩ : syracuseStep 38176181 = 3579017) B3579017
theorem B788015 : Blo 550806 788015 := bstep (se 1 (by rfl) ⟨591011, by rfl⟩ : syracuseStep 788015 = 1182023) B1182023
theorem B2655899 : Blo 550806 2655899 := bstep (se 1 (by rfl) ⟨1991924, by rfl⟩ : syracuseStep 2655899 = 3983849) B3983849
theorem B3770027 : Blo 550806 3770027 := bstep (se 1 (by rfl) ⟨2827520, by rfl⟩ : syracuseStep 3770027 = 5655041) B5655041
theorem B19171241 : Blo 550806 19171241 := bstep (se 2 (by rfl) ⟨7189215, by rfl⟩ : syracuseStep 19171241 = 14378431) B14378431
theorem B559207 : Blo 550806 559207 := bstep (se 1 (by rfl) ⟨419405, by rfl⟩ : syracuseStep 559207 = 838811) B838811
theorem B5736553 : Blo 550806 5736553 := bstep (se 2 (by rfl) ⟨2151207, by rfl⟩ : syracuseStep 5736553 = 4302415) B4302415
theorem B3148733 : Blo 550806 3148733 := bstep (se 3 (by rfl) ⟨590387, by rfl⟩ : syracuseStep 3148733 = 1180775) B1180775
theorem B1248191 : Blo 550806 1248191 := bstep (se 1 (by rfl) ⟨936143, by rfl⟩ : syracuseStep 1248191 = 1872287) B1872287
theorem B1871261 : Blo 550806 1871261 := bstep (se 3 (by rfl) ⟨350861, by rfl⟩ : syracuseStep 1871261 = 701723) B701723
theorem B11374519 : Blo 550806 11374519 := bstep (se 1 (by rfl) ⟨8530889, by rfl⟩ : syracuseStep 11374519 = 17061779) B17061779
theorem B1872071 : Blo 550806 1872071 := bstep (se 1 (by rfl) ⟨1404053, by rfl⟩ : syracuseStep 1872071 = 2808107) B2808107
theorem B3544991 : Blo 550806 3544991 := bstep (se 1 (by rfl) ⟨2658743, by rfl⟩ : syracuseStep 3544991 = 5317487) B5317487
theorem B5675105 : Blo 550806 5675105 := bstep (se 2 (by rfl) ⟨2128164, by rfl⟩ : syracuseStep 5675105 = 4256329) B4256329
theorem B9182483 : Blo 550806 9182483 := bstep (se 1 (by rfl) ⟨6886862, by rfl⟩ : syracuseStep 9182483 = 13773725) B13773725
theorem B65674745 : Blo 550806 65674745 := bstep (se 2 (by rfl) ⟨24628029, by rfl⟩ : syracuseStep 65674745 = 49256059) B49256059
theorem B5677087 : Blo 550806 5677087 := bstep (se 1 (by rfl) ⟨4257815, by rfl⟩ : syracuseStep 5677087 = 8515631) B8515631
theorem B827807 : Blo 550806 827807 := bstep (se 1 (by rfl) ⟨620855, by rfl⟩ : syracuseStep 827807 = 1241711) B1241711
theorem B698215 : Blo 550806 698215 := bstep (se 1 (by rfl) ⟨523661, by rfl⟩ : syracuseStep 698215 = 1047323) B1047323
theorem B829511 : Blo 550806 829511 := bstep (se 1 (by rfl) ⟨622133, by rfl⟩ : syracuseStep 829511 = 1244267) B1244267
theorem B830591 : Blo 550806 830591 := bstep (se 1 (by rfl) ⟨622943, by rfl⟩ : syracuseStep 830591 = 1245887) B1245887
theorem B831695 : Blo 550806 831695 := bstep (se 1 (by rfl) ⟨623771, by rfl⟩ : syracuseStep 831695 = 1247543) B1247543
theorem B7975259 : Blo 550806 7975259 := bstep (se 1 (by rfl) ⟨5981444, by rfl⟩ : syracuseStep 7975259 = 11962889) B11962889
theorem B701551 : Blo 550806 701551 := bstep (se 1 (by rfl) ⟨526163, by rfl⟩ : syracuseStep 701551 = 1052327) B1052327
theorem B931007 : Blo 550806 931007 := bstep (se 1 (by rfl) ⟨698255, by rfl⟩ : syracuseStep 931007 = 1396511) B1396511
theorem B932735 : Blo 550806 932735 := bstep (se 1 (by rfl) ⟨699551, by rfl⟩ : syracuseStep 932735 = 1399103) B1399103
theorem B934591 : Blo 550806 934591 := bstep (se 1 (by rfl) ⟨700943, by rfl⟩ : syracuseStep 934591 = 1401887) B1401887
theorem B2802761 : Blo 550806 2802761 := bstep (se 2 (by rfl) ⟨1051035, by rfl⟩ : syracuseStep 2802761 = 2102071) B2102071
theorem B7586951 : Blo 550806 7586951 := bstep (se 1 (by rfl) ⟨5690213, by rfl⟩ : syracuseStep 7586951 = 11380427) B11380427
theorem B15913705 : Blo 550806 15913705 := bstep (se 2 (by rfl) ⟨5967639, by rfl⟩ : syracuseStep 15913705 = 11935279) B11935279
theorem B5297035 : Blo 550806 5297035 := bstep (se 1 (by rfl) ⟨3972776, by rfl⟩ : syracuseStep 5297035 = 7945553) B7945553
theorem B6313139 : Blo 550806 6313139 := bstep (se 1 (by rfl) ⟨4734854, by rfl⟩ : syracuseStep 6313139 = 9469709) B9469709
theorem B1399963 : Blo 550806 1399963 := bstep (se 1 (by rfl) ⟨1049972, by rfl⟩ : syracuseStep 1399963 = 2099945) B2099945
theorem B1400287 : Blo 550806 1400287 := bstep (se 1 (by rfl) ⟨1050215, by rfl⟩ : syracuseStep 1400287 = 2100431) B2100431
theorem B1400935 : Blo 550806 1400935 := bstep (se 1 (by rfl) ⟨1050701, by rfl⟩ : syracuseStep 1400935 = 2101403) B2101403
theorem B22635449 : Blo 550806 22635449 := bstep (se 2 (by rfl) ⟨8488293, by rfl⟩ : syracuseStep 22635449 = 16976587) B16976587
theorem B72672871 : Blo 550806 72672871 := bstep (se 1 (by rfl) ⟨54504653, by rfl⟩ : syracuseStep 72672871 = 109009307) B109009307
theorem B550911 : Blo 550806 550911 := bstep (se 1 (by rfl) ⟨413183, by rfl⟩ : syracuseStep 550911 = 826367) B826367
theorem B551551 : Blo 550806 551551 := bstep (se 1 (by rfl) ⟨413663, by rfl⟩ : syracuseStep 551551 = 827327) B827327
theorem B1404155 : Blo 550806 1404155 := bstep (se 1 (by rfl) ⟨1053116, by rfl⟩ : syracuseStep 1404155 = 2106233) B2106233
theorem B5992859 : Blo 550806 5992859 := bstep (se 1 (by rfl) ⟨4494644, by rfl⟩ : syracuseStep 5992859 = 8989289) B8989289
theorem B1766231 : Blo 550806 1766231 := bstep (se 1 (by rfl) ⟨1324673, by rfl⟩ : syracuseStep 1766231 = 2649347) B2649347
theorem B1242143 : Blo 550806 1242143 := bstep (se 1 (by rfl) ⟨931607, by rfl⟩ : syracuseStep 1242143 = 1863215) B1863215
theorem B2094113 : Blo 550806 2094113 := bstep (se 2 (by rfl) ⟨785292, by rfl⟩ : syracuseStep 2094113 = 1570585) B1570585
theorem B554015 : Blo 550806 554015 := bstep (se 1 (by rfl) ⟨415511, by rfl⟩ : syracuseStep 554015 = 831023) B831023
theorem B1864889 : Blo 550806 1864889 := bstep (se 2 (by rfl) ⟨699333, by rfl⟩ : syracuseStep 1864889 = 1398667) B1398667
theorem B554779 : Blo 550806 554779 := bstep (se 1 (by rfl) ⟨416084, by rfl⟩ : syracuseStep 554779 = 832169) B832169
theorem B34863209 : Blo 550806 34863209 := bstep (se 2 (by rfl) ⟨13073703, by rfl⟩ : syracuseStep 34863209 = 26147407) B26147407
theorem B2980061 : Blo 550806 2980061 := bstep (se 3 (by rfl) ⟨558761, by rfl⟩ : syracuseStep 2980061 = 1117523) B1117523
theorem B1243817 : Blo 550806 1243817 := bstep (se 2 (by rfl) ⟨466431, by rfl⟩ : syracuseStep 1243817 = 932863) B932863
theorem B1243961 : Blo 550806 1243961 := bstep (se 2 (by rfl) ⟨466485, by rfl⟩ : syracuseStep 1243961 = 932971) B932971
theorem B1244537 : Blo 550806 1244537 := bstep (se 2 (by rfl) ⟨466701, by rfl⟩ : syracuseStep 1244537 = 933403) B933403
theorem B13106555 : Blo 550806 13106555 := bstep (se 1 (by rfl) ⟨9829916, by rfl⟩ : syracuseStep 13106555 = 19659833) B19659833
theorem B2653823 : Blo 550806 2653823 := bstep (se 1 (by rfl) ⟨1990367, by rfl⟩ : syracuseStep 2653823 = 3980735) B3980735
theorem B7569449 : Blo 550806 7569449 := bstep (se 2 (by rfl) ⟨2838543, by rfl⟩ : syracuseStep 7569449 = 5677087) B5677087
theorem B1867913 : Blo 550806 1867913 := bstep (se 2 (by rfl) ⟨700467, by rfl⟩ : syracuseStep 1867913 = 1400935) B1400935
theorem B2982437 : Blo 550806 2982437 := bstep (se 4 (by rfl) ⟨279603, by rfl⟩ : syracuseStep 2982437 = 559207) B559207
theorem B7996067 : Blo 550806 7996067 := bstep (se 1 (by rfl) ⟨5997050, by rfl⟩ : syracuseStep 7996067 = 11994101) B11994101
theorem B1868507 : Blo 550806 1868507 := bstep (se 1 (by rfl) ⟨1401380, by rfl⟩ : syracuseStep 1868507 = 2802761) B2802761
theorem B1770331 : Blo 550806 1770331 := bstep (se 1 (by rfl) ⟨1327748, by rfl⟩ : syracuseStep 1770331 = 2655497) B2655497
theorem B1246121 : Blo 550806 1246121 := bstep (se 2 (by rfl) ⟨467295, by rfl⟩ : syracuseStep 1246121 = 934591) B934591
theorem B1770599 : Blo 550806 1770599 := bstep (se 1 (by rfl) ⟨1327949, by rfl⟩ : syracuseStep 1770599 = 2655899) B2655899
theorem B12780827 : Blo 550806 12780827 := bstep (se 1 (by rfl) ⟨9585620, by rfl⟩ : syracuseStep 12780827 = 19171241) B19171241
theorem B787753 : Blo 550806 787753 := bstep (se 2 (by rfl) ⟨295407, by rfl⟩ : syracuseStep 787753 = 590815) B590815
theorem B2099155 : Blo 550806 2099155 := bstep (se 1 (by rfl) ⟨1574366, by rfl⟩ : syracuseStep 2099155 = 3148733) B3148733
theorem B96897161 : Blo 550806 96897161 := bstep (se 2 (by rfl) ⟨36336435, by rfl⟩ : syracuseStep 96897161 = 72672871) B72672871
theorem B1247507 : Blo 550806 1247507 := bstep (se 1 (by rfl) ⟨935630, by rfl⟩ : syracuseStep 1247507 = 1871261) B1871261
theorem B1248047 : Blo 550806 1248047 := bstep (se 1 (by rfl) ⟨936035, by rfl⟩ : syracuseStep 1248047 = 1872071) B1872071
theorem B2363327 : Blo 550806 2363327 := bstep (se 1 (by rfl) ⟨1772495, by rfl⟩ : syracuseStep 2363327 = 3544991) B3544991
theorem B2101373 : Blo 550806 2101373 := bstep (se 3 (by rfl) ⟨394007, by rfl⟩ : syracuseStep 2101373 = 788015) B788015
theorem B43783163 : Blo 550806 43783163 := bstep (se 1 (by rfl) ⟨32837372, by rfl⟩ : syracuseStep 43783163 = 65674745) B65674745
theorem B5316839 : Blo 550806 5316839 := bstep (se 1 (by rfl) ⟨3987629, by rfl⟩ : syracuseStep 5316839 = 7975259) B7975259
theorem B828095 : Blo 550806 828095 := bstep (se 1 (by rfl) ⟨621071, by rfl⟩ : syracuseStep 828095 = 1242143) B1242143
theorem B23242139 : Blo 550806 23242139 := bstep (se 1 (by rfl) ⟨17431604, by rfl⟩ : syracuseStep 23242139 = 34863209) B34863209
theorem B829211 : Blo 550806 829211 := bstep (se 1 (by rfl) ⟨621908, by rfl⟩ : syracuseStep 829211 = 1243817) B1243817
theorem B829307 : Blo 550806 829307 := bstep (se 1 (by rfl) ⟨621980, by rfl⟩ : syracuseStep 829307 = 1243961) B1243961
theorem B829691 : Blo 550806 829691 := bstep (se 1 (by rfl) ⟨622268, by rfl⟩ : syracuseStep 829691 = 1244537) B1244537
theorem B699931 : Blo 550806 699931 := bstep (se 1 (by rfl) ⟨524948, by rfl⟩ : syracuseStep 699931 = 1049897) B1049897
theorem B832127 : Blo 550806 832127 := bstep (se 1 (by rfl) ⟨624095, by rfl⟩ : syracuseStep 832127 = 1248191) B1248191
theorem B930953 : Blo 550806 930953 := bstep (se 2 (by rfl) ⟨349107, by rfl⟩ : syracuseStep 930953 = 698215) B698215
theorem B20231869 : Blo 550806 20231869 := bstep (se 3 (by rfl) ⟨3793475, by rfl⟩ : syracuseStep 20231869 = 7586951) B7586951
theorem B4208759 : Blo 550806 4208759 := bstep (se 1 (by rfl) ⟨3156569, by rfl⟩ : syracuseStep 4208759 = 6313139) B6313139
theorem B15090299 : Blo 550806 15090299 := bstep (se 1 (by rfl) ⟨11317724, by rfl⟩ : syracuseStep 15090299 = 22635449) B22635449
theorem B21218273 : Blo 550806 21218273 := bstep (se 2 (by rfl) ⟨7956852, by rfl⟩ : syracuseStep 21218273 = 15913705) B15913705
theorem B7062713 : Blo 550806 7062713 := bstep (se 2 (by rfl) ⟨2648517, by rfl⟩ : syracuseStep 7062713 = 5297035) B5297035
theorem B935401 : Blo 550806 935401 := bstep (se 2 (by rfl) ⟨350775, by rfl⟩ : syracuseStep 935401 = 701551) B701551
theorem B936103 : Blo 550806 936103 := bstep (se 1 (by rfl) ⟨702077, by rfl⟩ : syracuseStep 936103 = 1404155) B1404155
theorem B1396075 : Blo 550806 1396075 := bstep (se 1 (by rfl) ⟨1047056, by rfl⟩ : syracuseStep 1396075 = 2094113) B2094113
theorem B1986707 : Blo 550806 1986707 := bstep (se 1 (by rfl) ⟨1490030, by rfl⟩ : syracuseStep 1986707 = 2980061) B2980061
theorem B8737703 : Blo 550806 8737703 := bstep (se 1 (by rfl) ⟨6553277, by rfl⟩ : syracuseStep 8737703 = 13106555) B13106555
theorem B25450787 : Blo 550806 25450787 := bstep (se 1 (by rfl) ⟨19088090, by rfl⟩ : syracuseStep 25450787 = 38176181) B38176181
theorem B2513351 : Blo 550806 2513351 := bstep (se 1 (by rfl) ⟨1885013, by rfl⟩ : syracuseStep 2513351 = 3770027) B3770027
theorem B290544353 : Blo 550806 290544353 := bstep (se 2 (by rfl) ⟨108954132, by rfl⟩ : syracuseStep 290544353 = 217908265) B217908265
theorem B122379797 : Blo 550806 122379797 := bstep (se 6 (by rfl) ⟨2868276, by rfl⟩ : syracuseStep 122379797 = 5736553) B5736553
theorem B6121655 : Blo 550806 6121655 := bstep (se 1 (by rfl) ⟨4591241, by rfl⟩ : syracuseStep 6121655 = 9182483) B9182483
theorem B15166025 : Blo 550806 15166025 := bstep (se 2 (by rfl) ⟨5687259, by rfl⟩ : syracuseStep 15166025 = 11374519) B11374519
theorem B15133613 : Blo 550806 15133613 := bstep (se 3 (by rfl) ⟨2837552, by rfl⟩ : syracuseStep 15133613 = 5675105) B5675105
theorem B551871 : Blo 550806 551871 := bstep (se 1 (by rfl) ⟨413903, by rfl⟩ : syracuseStep 551871 = 827807) B827807
theorem B553007 : Blo 550806 553007 := bstep (se 1 (by rfl) ⟨414755, by rfl⟩ : syracuseStep 553007 = 829511) B829511
theorem B553727 : Blo 550806 553727 := bstep (se 1 (by rfl) ⟨415295, by rfl⟩ : syracuseStep 553727 = 830591) B830591
theorem B554463 : Blo 550806 554463 := bstep (se 1 (by rfl) ⟨415847, by rfl⟩ : syracuseStep 554463 = 831695) B831695
theorem B3995239 : Blo 550806 3995239 := bstep (se 1 (by rfl) ⟨2996429, by rfl⟩ : syracuseStep 3995239 = 5992859) B5992859
theorem B1177487 : Blo 550806 1177487 := bstep (se 1 (by rfl) ⟨883115, by rfl⟩ : syracuseStep 1177487 = 1766231) B1766231
theorem B1243259 : Blo 550806 1243259 := bstep (se 1 (by rfl) ⟨932444, by rfl⟩ : syracuseStep 1243259 = 1864889) B1864889
theorem B620671 : Blo 550806 620671 := bstep (se 1 (by rfl) ⟨465503, by rfl⟩ : syracuseStep 620671 = 931007) B931007
theorem B1866617 : Blo 550806 1866617 := bstep (se 2 (by rfl) ⟨699981, by rfl⟩ : syracuseStep 1866617 = 1399963) B1399963
theorem B621823 : Blo 550806 621823 := bstep (se 1 (by rfl) ⟨466367, by rfl⟩ : syracuseStep 621823 = 932735) B932735
theorem B1867049 : Blo 550806 1867049 := bstep (se 2 (by rfl) ⟨700143, by rfl⟩ : syracuseStep 1867049 = 1400287) B1400287
theorem B1769215 : Blo 550806 1769215 := bstep (se 1 (by rfl) ⟨1326911, by rfl⟩ : syracuseStep 1769215 = 2653823) B2653823
theorem B5046299 : Blo 550806 5046299 := bstep (se 1 (by rfl) ⟨3784724, by rfl⟩ : syracuseStep 5046299 = 7569449) B7569449
theorem B1245275 : Blo 550806 1245275 := bstep (se 1 (by rfl) ⟨933956, by rfl⟩ : syracuseStep 1245275 = 1867913) B1867913
theorem B10060199 : Blo 550806 10060199 := bstep (se 1 (by rfl) ⟨7545149, by rfl⟩ : syracuseStep 10060199 = 15090299) B15090299
theorem B1245671 : Blo 550806 1245671 := bstep (se 1 (by rfl) ⟨934253, by rfl⟩ : syracuseStep 1245671 = 1868507) B1868507
theorem B8520551 : Blo 550806 8520551 := bstep (se 1 (by rfl) ⟨6390413, by rfl⟩ : syracuseStep 8520551 = 12780827) B12780827
theorem B2360441 : Blo 550806 2360441 := bstep (se 2 (by rfl) ⟨885165, by rfl⟩ : syracuseStep 2360441 = 1770331) B1770331
theorem B1050337 : Blo 550806 1050337 := bstep (se 2 (by rfl) ⟨393876, by rfl⟩ : syracuseStep 1050337 = 787753) B787753
theorem B1247201 : Blo 550806 1247201 := bstep (se 2 (by rfl) ⟨467700, by rfl⟩ : syracuseStep 1247201 = 935401) B935401
theorem B1575551 : Blo 550806 1575551 := bstep (se 1 (by rfl) ⟨1181663, by rfl⟩ : syracuseStep 1575551 = 2363327) B2363327
theorem B1248137 : Blo 550806 1248137 := bstep (se 2 (by rfl) ⟨468051, by rfl⟩ : syracuseStep 1248137 = 936103) B936103
theorem B4721597 : Blo 550806 4721597 := bstep (se 3 (by rfl) ⟨885299, by rfl⟩ : syracuseStep 4721597 = 1770599) B1770599
theorem B1675567 : Blo 550806 1675567 := bstep (se 1 (by rfl) ⟨1256675, by rfl⟩ : syracuseStep 1675567 = 2513351) B2513351
theorem B193696235 : Blo 550806 193696235 := bstep (se 1 (by rfl) ⟨145272176, by rfl⟩ : syracuseStep 193696235 = 290544353) B290544353
theorem B3544559 : Blo 550806 3544559 := bstep (se 1 (by rfl) ⟨2658419, by rfl⟩ : syracuseStep 3544559 = 5316839) B5316839
theorem B26975825 : Blo 550806 26975825 := bstep (se 2 (by rfl) ⟨10115934, by rfl⟩ : syracuseStep 26975825 = 20231869) B20231869
theorem B827561 : Blo 550806 827561 := bstep (se 2 (by rfl) ⟨310335, by rfl⟩ : syracuseStep 827561 = 620671) B620671
theorem B828839 : Blo 550806 828839 := bstep (se 1 (by rfl) ⟨621629, by rfl⟩ : syracuseStep 828839 = 1243259) B1243259
theorem B829097 : Blo 550806 829097 := bstep (se 2 (by rfl) ⟨310911, by rfl⟩ : syracuseStep 829097 = 621823) B621823
theorem B830747 : Blo 550806 830747 := bstep (se 1 (by rfl) ⟨623060, by rfl⟩ : syracuseStep 830747 = 1246121) B1246121
theorem B831671 : Blo 550806 831671 := bstep (se 1 (by rfl) ⟨623753, by rfl⟩ : syracuseStep 831671 = 1247507) B1247507
theorem B832031 : Blo 550806 832031 := bstep (se 1 (by rfl) ⟨624023, by rfl⟩ : syracuseStep 832031 = 1248047) B1248047
theorem B2798873 : Blo 550806 2798873 := bstep (se 2 (by rfl) ⟨1049577, by rfl⟩ : syracuseStep 2798873 = 2099155) B2099155
theorem B933241 : Blo 550806 933241 := bstep (se 2 (by rfl) ⟨349965, by rfl⟩ : syracuseStep 933241 = 699931) B699931
theorem B258392429 : Blo 550806 258392429 := bstep (se 3 (by rfl) ⟨48448580, by rfl⟩ : syracuseStep 258392429 = 96897161) B96897161
theorem B4081103 : Blo 550806 4081103 := bstep (se 1 (by rfl) ⟨3060827, by rfl⟩ : syracuseStep 4081103 = 6121655) B6121655
theorem B10110683 : Blo 550806 10110683 := bstep (se 1 (by rfl) ⟨7583012, by rfl⟩ : syracuseStep 10110683 = 15166025) B15166025
theorem B5326985 : Blo 550806 5326985 := bstep (se 2 (by rfl) ⟨1997619, by rfl⟩ : syracuseStep 5326985 = 3995239) B3995239
theorem B40356301 : Blo 550806 40356301 := bstep (se 3 (by rfl) ⟨7566806, by rfl⟩ : syracuseStep 40356301 = 15133613) B15133613
theorem B2805839 : Blo 550806 2805839 := bstep (se 1 (by rfl) ⟨2104379, by rfl⟩ : syracuseStep 2805839 = 4208759) B4208759
theorem B1988291 : Blo 550806 1988291 := bstep (se 1 (by rfl) ⟨1491218, by rfl⟩ : syracuseStep 1988291 = 2982437) B2982437
theorem B5297885 : Blo 550806 5297885 := bstep (se 3 (by rfl) ⟨993353, by rfl⟩ : syracuseStep 5297885 = 1986707) B1986707
theorem B5330711 : Blo 550806 5330711 := bstep (se 1 (by rfl) ⟨3998033, by rfl⟩ : syracuseStep 5330711 = 7996067) B7996067
theorem B14145515 : Blo 550806 14145515 := bstep (se 1 (by rfl) ⟨10609136, by rfl⟩ : syracuseStep 14145515 = 21218273) B21218273
theorem B4708475 : Blo 550806 4708475 := bstep (se 1 (by rfl) ⟨3531356, by rfl⟩ : syracuseStep 4708475 = 7062713) B7062713
theorem B1400915 : Blo 550806 1400915 := bstep (se 1 (by rfl) ⟨1050686, by rfl⟩ : syracuseStep 1400915 = 2101373) B2101373
theorem B5825135 : Blo 550806 5825135 := bstep (se 1 (by rfl) ⟨4368851, by rfl⟩ : syracuseStep 5825135 = 8737703) B8737703
theorem B29188775 : Blo 550806 29188775 := bstep (se 1 (by rfl) ⟨21891581, by rfl⟩ : syracuseStep 29188775 = 43783163) B43783163
theorem B16967191 : Blo 550806 16967191 := bstep (se 1 (by rfl) ⟨12725393, by rfl⟩ : syracuseStep 16967191 = 25450787) B25450787
theorem B1861433 : Blo 550806 1861433 := bstep (se 2 (by rfl) ⟨698037, by rfl⟩ : syracuseStep 1861433 = 1396075) B1396075
theorem B81586531 : Blo 550806 81586531 := bstep (se 1 (by rfl) ⟨61189898, by rfl⟩ : syracuseStep 81586531 = 122379797) B122379797
theorem B552063 : Blo 550806 552063 := bstep (se 1 (by rfl) ⟨414047, by rfl⟩ : syracuseStep 552063 = 828095) B828095
theorem B15494759 : Blo 550806 15494759 := bstep (se 1 (by rfl) ⟨11621069, by rfl⟩ : syracuseStep 15494759 = 23242139) B23242139
theorem B552807 : Blo 550806 552807 := bstep (se 1 (by rfl) ⟨414605, by rfl⟩ : syracuseStep 552807 = 829211) B829211
theorem B552871 : Blo 550806 552871 := bstep (se 1 (by rfl) ⟨414653, by rfl⟩ : syracuseStep 552871 = 829307) B829307
theorem B553127 : Blo 550806 553127 := bstep (se 1 (by rfl) ⟨414845, by rfl⟩ : syracuseStep 553127 = 829691) B829691
theorem B554751 : Blo 550806 554751 := bstep (se 1 (by rfl) ⟨416063, by rfl⟩ : syracuseStep 554751 = 832127) B832127
theorem B620635 : Blo 550806 620635 := bstep (se 1 (by rfl) ⟨465476, by rfl⟩ : syracuseStep 620635 = 930953) B930953
theorem B784991 : Blo 550806 784991 := bstep (se 1 (by rfl) ⟨588743, by rfl⟩ : syracuseStep 784991 = 1177487) B1177487
theorem B1244411 : Blo 550806 1244411 := bstep (se 1 (by rfl) ⟨933308, by rfl⟩ : syracuseStep 1244411 = 1866617) B1866617
theorem B1244699 : Blo 550806 1244699 := bstep (se 1 (by rfl) ⟨933524, by rfl⟩ : syracuseStep 1244699 = 1867049) B1867049
theorem B2358953 : Blo 550806 2358953 := bstep (se 2 (by rfl) ⟨884607, by rfl⟩ : syracuseStep 2358953 = 1769215) B1769215
theorem B172261619 : Blo 550806 172261619 := bstep (se 1 (by rfl) ⟨129196214, by rfl⟩ : syracuseStep 172261619 = 258392429) B258392429
theorem B1573627 : Blo 550806 1573627 := bstep (se 1 (by rfl) ⟨1180220, by rfl⟩ : syracuseStep 1573627 = 2360441) B2360441
theorem B2720735 : Blo 550806 2720735 := bstep (se 1 (by rfl) ⟨2040551, by rfl⟩ : syracuseStep 2720735 = 4081103) B4081103
theorem B15533693 : Blo 550806 15533693 := bstep (se 3 (by rfl) ⟨2912567, by rfl⟩ : syracuseStep 15533693 = 5825135) B5825135
theorem B3147731 : Blo 550806 3147731 := bstep (se 1 (by rfl) ⟨2360798, by rfl⟩ : syracuseStep 3147731 = 4721597) B4721597
theorem B1870559 : Blo 550806 1870559 := bstep (se 1 (by rfl) ⟨1402919, by rfl⟩ : syracuseStep 1870559 = 2805839) B2805839
theorem B53808401 : Blo 550806 53808401 := bstep (se 2 (by rfl) ⟨20178150, by rfl⟩ : syracuseStep 53808401 = 40356301) B40356301
theorem B2363039 : Blo 550806 2363039 := bstep (se 1 (by rfl) ⟨1772279, by rfl⟩ : syracuseStep 2363039 = 3544559) B3544559
theorem B2234089 : Blo 550806 2234089 := bstep (se 2 (by rfl) ⟨837783, by rfl⟩ : syracuseStep 2234089 = 1675567) B1675567
theorem B4201469 : Blo 550806 4201469 := bstep (se 3 (by rfl) ⟨787775, by rfl⟩ : syracuseStep 4201469 = 1575551) B1575551
theorem B10329839 : Blo 550806 10329839 := bstep (se 1 (by rfl) ⟨7747379, by rfl⟩ : syracuseStep 10329839 = 15494759) B15494759
theorem B827513 : Blo 550806 827513 := bstep (se 2 (by rfl) ⟨310317, by rfl⟩ : syracuseStep 827513 = 620635) B620635
theorem B829607 : Blo 550806 829607 := bstep (se 1 (by rfl) ⟨622205, by rfl⟩ : syracuseStep 829607 = 1244411) B1244411
theorem B829799 : Blo 550806 829799 := bstep (se 1 (by rfl) ⟨622349, by rfl⟩ : syracuseStep 829799 = 1244699) B1244699
theorem B830183 : Blo 550806 830183 := bstep (se 1 (by rfl) ⟨622637, by rfl⟩ : syracuseStep 830183 = 1245275) B1245275
theorem B830447 : Blo 550806 830447 := bstep (se 1 (by rfl) ⟨622835, by rfl⟩ : syracuseStep 830447 = 1245671) B1245671
theorem B5680367 : Blo 550806 5680367 := bstep (se 1 (by rfl) ⟨4260275, by rfl⟩ : syracuseStep 5680367 = 8520551) B8520551
theorem B831467 : Blo 550806 831467 := bstep (se 1 (by rfl) ⟨623600, by rfl⟩ : syracuseStep 831467 = 1247201) B1247201
theorem B3551323 : Blo 550806 3551323 := bstep (se 1 (by rfl) ⟨2663492, by rfl⟩ : syracuseStep 3551323 = 5326985) B5326985
theorem B832091 : Blo 550806 832091 := bstep (se 1 (by rfl) ⟨624068, by rfl⟩ : syracuseStep 832091 = 1248137) B1248137
theorem B22622921 : Blo 550806 22622921 := bstep (se 2 (by rfl) ⟨8483595, by rfl⟩ : syracuseStep 22622921 = 16967191) B16967191
theorem B1325527 : Blo 550806 1325527 := bstep (se 1 (by rfl) ⟨994145, by rfl⟩ : syracuseStep 1325527 = 1988291) B1988291
theorem B3553807 : Blo 550806 3553807 := bstep (se 1 (by rfl) ⟨2665355, by rfl⟩ : syracuseStep 3553807 = 5330711) B5330711
theorem B933943 : Blo 550806 933943 := bstep (se 1 (by rfl) ⟨700457, by rfl⟩ : syracuseStep 933943 = 1400915) B1400915
theorem B3364199 : Blo 550806 3364199 := bstep (se 1 (by rfl) ⟨2523149, by rfl⟩ : syracuseStep 3364199 = 5046299) B5046299
theorem B6706799 : Blo 550806 6706799 := bstep (se 1 (by rfl) ⟨5030099, by rfl⟩ : syracuseStep 6706799 = 10060199) B10060199
theorem B6740455 : Blo 550806 6740455 := bstep (se 1 (by rfl) ⟨5055341, by rfl⟩ : syracuseStep 6740455 = 10110683) B10110683
theorem B1400449 : Blo 550806 1400449 := bstep (se 2 (by rfl) ⟨525168, by rfl⟩ : syracuseStep 1400449 = 1050337) B1050337
theorem B129130823 : Blo 550806 129130823 := bstep (se 1 (by rfl) ⟨96848117, by rfl⟩ : syracuseStep 129130823 = 193696235) B193696235
theorem B108782041 : Blo 550806 108782041 := bstep (se 2 (by rfl) ⟨40793265, by rfl⟩ : syracuseStep 108782041 = 81586531) B81586531
theorem B3531923 : Blo 550806 3531923 := bstep (se 1 (by rfl) ⟨2648942, by rfl⟩ : syracuseStep 3531923 = 5297885) B5297885
theorem B9430343 : Blo 550806 9430343 := bstep (se 1 (by rfl) ⟨7072757, by rfl⟩ : syracuseStep 9430343 = 14145515) B14145515
theorem B3138983 : Blo 550806 3138983 := bstep (se 1 (by rfl) ⟨2354237, by rfl⟩ : syracuseStep 3138983 = 4708475) B4708475
theorem B17983883 : Blo 550806 17983883 := bstep (se 1 (by rfl) ⟨13487912, by rfl⟩ : syracuseStep 17983883 = 26975825) B26975825
theorem B551707 : Blo 550806 551707 := bstep (se 1 (by rfl) ⟨413780, by rfl⟩ : syracuseStep 551707 = 827561) B827561
theorem B19459183 : Blo 550806 19459183 := bstep (se 1 (by rfl) ⟨14594387, by rfl⟩ : syracuseStep 19459183 = 29188775) B29188775
theorem B552559 : Blo 550806 552559 := bstep (se 1 (by rfl) ⟨414419, by rfl⟩ : syracuseStep 552559 = 828839) B828839
theorem B552731 : Blo 550806 552731 := bstep (se 1 (by rfl) ⟨414548, by rfl⟩ : syracuseStep 552731 = 829097) B829097
theorem B1240955 : Blo 550806 1240955 := bstep (se 1 (by rfl) ⟨930716, by rfl⟩ : syracuseStep 1240955 = 1861433) B1861433
theorem B2093309 : Blo 550806 2093309 := bstep (se 3 (by rfl) ⟨392495, by rfl⟩ : syracuseStep 2093309 = 784991) B784991
theorem B553831 : Blo 550806 553831 := bstep (se 1 (by rfl) ⟨415373, by rfl⟩ : syracuseStep 553831 = 830747) B830747
theorem B554447 : Blo 550806 554447 := bstep (se 1 (by rfl) ⟨415835, by rfl⟩ : syracuseStep 554447 = 831671) B831671
theorem B554687 : Blo 550806 554687 := bstep (se 1 (by rfl) ⟨416015, by rfl⟩ : syracuseStep 554687 = 832031) B832031
theorem B1865915 : Blo 550806 1865915 := bstep (se 1 (by rfl) ⟨1399436, by rfl⟩ : syracuseStep 1865915 = 2798873) B2798873
theorem B1244321 : Blo 550806 1244321 := bstep (se 2 (by rfl) ⟨466620, by rfl⟩ : syracuseStep 1244321 = 933241) B933241
theorem B1572635 : Blo 550806 1572635 := bstep (se 1 (by rfl) ⟨1179476, by rfl⟩ : syracuseStep 1572635 = 2358953) B2358953
theorem B1245257 : Blo 550806 1245257 := bstep (se 2 (by rfl) ⟨466971, by rfl⟩ : syracuseStep 1245257 = 933943) B933943
theorem B2098169 : Blo 550806 2098169 := bstep (se 2 (by rfl) ⟨786813, by rfl⟩ : syracuseStep 2098169 = 1573627) B1573627
theorem B10355795 : Blo 550806 10355795 := bstep (se 1 (by rfl) ⟨7766846, by rfl⟩ : syracuseStep 10355795 = 15533693) B15533693
theorem B2098487 : Blo 550806 2098487 := bstep (se 1 (by rfl) ⟨1573865, by rfl⟩ : syracuseStep 2098487 = 3147731) B3147731
theorem B1247039 : Blo 550806 1247039 := bstep (se 1 (by rfl) ⟨935279, by rfl⟩ : syracuseStep 1247039 = 1870559) B1870559
theorem B1575359 : Blo 550806 1575359 := bstep (se 1 (by rfl) ⟨1181519, by rfl⟩ : syracuseStep 1575359 = 2363039) B2363039
theorem B6886559 : Blo 550806 6886559 := bstep (se 1 (by rfl) ⟨5164919, by rfl⟩ : syracuseStep 6886559 = 10329839) B10329839
theorem B86087215 : Blo 550806 86087215 := bstep (se 1 (by rfl) ⟨64565411, by rfl⟩ : syracuseStep 86087215 = 129130823) B129130823
theorem B827303 : Blo 550806 827303 := bstep (se 1 (by rfl) ⟨620477, by rfl⟩ : syracuseStep 827303 = 1240955) B1240955
theorem B15081947 : Blo 550806 15081947 := bstep (se 1 (by rfl) ⟨11311460, by rfl⟩ : syracuseStep 15081947 = 22622921) B22622921
theorem B8987273 : Blo 550806 8987273 := bstep (se 2 (by rfl) ⟨3370227, by rfl⟩ : syracuseStep 8987273 = 6740455) B6740455
theorem B829547 : Blo 550806 829547 := bstep (se 1 (by rfl) ⟨622160, by rfl⟩ : syracuseStep 829547 = 1244321) B1244321
theorem B145042721 : Blo 550806 145042721 := bstep (se 2 (by rfl) ⟨54391020, by rfl⟩ : syracuseStep 145042721 = 108782041) B108782041
theorem B1813823 : Blo 550806 1813823 := bstep (se 1 (by rfl) ⟨1360367, by rfl⟩ : syracuseStep 1813823 = 2720735) B2720735
theorem B2242799 : Blo 550806 2242799 := bstep (se 1 (by rfl) ⟨1682099, by rfl⟩ : syracuseStep 2242799 = 3364199) B3364199
theorem B4471199 : Blo 550806 4471199 := bstep (se 1 (by rfl) ⟨3353399, by rfl⟩ : syracuseStep 4471199 = 6706799) B6706799
theorem B2800979 : Blo 550806 2800979 := bstep (se 1 (by rfl) ⟨2100734, by rfl⟩ : syracuseStep 2800979 = 4201469) B4201469
theorem B4735097 : Blo 550806 4735097 := bstep (se 2 (by rfl) ⟨1775661, by rfl⟩ : syracuseStep 4735097 = 3551323) B3551323
theorem B3786911 : Blo 550806 3786911 := bstep (se 1 (by rfl) ⟨2840183, by rfl⟩ : syracuseStep 3786911 = 5680367) B5680367
theorem B1395539 : Blo 550806 1395539 := bstep (se 1 (by rfl) ⟨1046654, by rfl⟩ : syracuseStep 1395539 = 2093309) B2093309
theorem B4738409 : Blo 550806 4738409 := bstep (se 2 (by rfl) ⟨1776903, by rfl⟩ : syracuseStep 4738409 = 3553807) B3553807
theorem B114841079 : Blo 550806 114841079 := bstep (se 1 (by rfl) ⟨86130809, by rfl⟩ : syracuseStep 114841079 = 172261619) B172261619
theorem B35872267 : Blo 550806 35872267 := bstep (se 1 (by rfl) ⟨26904200, by rfl⟩ : syracuseStep 35872267 = 53808401) B53808401
theorem B7069477 : Blo 550806 7069477 := bstep (se 4 (by rfl) ⟨662763, by rfl⟩ : syracuseStep 7069477 = 1325527) B1325527
theorem B25945577 : Blo 550806 25945577 := bstep (se 2 (by rfl) ⟨9729591, by rfl⟩ : syracuseStep 25945577 = 19459183) B19459183
theorem B551675 : Blo 550806 551675 := bstep (se 1 (by rfl) ⟨413756, by rfl⟩ : syracuseStep 551675 = 827513) B827513
theorem B2354615 : Blo 550806 2354615 := bstep (se 1 (by rfl) ⟨1765961, by rfl⟩ : syracuseStep 2354615 = 3531923) B3531923
theorem B6286895 : Blo 550806 6286895 := bstep (se 1 (by rfl) ⟨4715171, by rfl⟩ : syracuseStep 6286895 = 9430343) B9430343
theorem B2092655 : Blo 550806 2092655 := bstep (se 1 (by rfl) ⟨1569491, by rfl⟩ : syracuseStep 2092655 = 3138983) B3138983
theorem B553071 : Blo 550806 553071 := bstep (se 1 (by rfl) ⟨414803, by rfl⟩ : syracuseStep 553071 = 829607) B829607
theorem B553199 : Blo 550806 553199 := bstep (se 1 (by rfl) ⟨414899, by rfl⟩ : syracuseStep 553199 = 829799) B829799
theorem B11989255 : Blo 550806 11989255 := bstep (se 1 (by rfl) ⟨8991941, by rfl⟩ : syracuseStep 11989255 = 17983883) B17983883
theorem B553455 : Blo 550806 553455 := bstep (se 1 (by rfl) ⟨415091, by rfl⟩ : syracuseStep 553455 = 830183) B830183
theorem B553631 : Blo 550806 553631 := bstep (se 1 (by rfl) ⟨415223, by rfl⟩ : syracuseStep 553631 = 830447) B830447
theorem B2978785 : Blo 550806 2978785 := bstep (se 2 (by rfl) ⟨1117044, by rfl⟩ : syracuseStep 2978785 = 2234089) B2234089
theorem B554311 : Blo 550806 554311 := bstep (se 1 (by rfl) ⟨415733, by rfl⟩ : syracuseStep 554311 = 831467) B831467
theorem B554727 : Blo 550806 554727 := bstep (se 1 (by rfl) ⟨416045, by rfl⟩ : syracuseStep 554727 = 832091) B832091
theorem B1243943 : Blo 550806 1243943 := bstep (se 1 (by rfl) ⟨932957, by rfl⟩ : syracuseStep 1243943 = 1865915) B1865915
theorem B4193693 : Blo 550806 4193693 := bstep (se 3 (by rfl) ⟨786317, by rfl⟩ : syracuseStep 4193693 = 1572635) B1572635
theorem B1867265 : Blo 550806 1867265 := bstep (se 2 (by rfl) ⟨700224, by rfl⟩ : syracuseStep 1867265 = 1400449) B1400449
theorem B2524607 : Blo 550806 2524607 := bstep (se 1 (by rfl) ⟨1893455, by rfl⟩ : syracuseStep 2524607 = 3786911) B3786911
theorem B1050239 : Blo 550806 1050239 := bstep (se 1 (by rfl) ⟨787679, by rfl⟩ : syracuseStep 1050239 = 1575359) B1575359
theorem B3971713 : Blo 550806 3971713 := bstep (se 2 (by rfl) ⟨1489392, by rfl⟩ : syracuseStep 3971713 = 2978785) B2978785
theorem B829295 : Blo 550806 829295 := bstep (se 1 (by rfl) ⟨621971, by rfl⟩ : syracuseStep 829295 = 1243943) B1243943
theorem B2795795 : Blo 550806 2795795 := bstep (se 1 (by rfl) ⟨2096846, by rfl⟩ : syracuseStep 2795795 = 4193693) B4193693
theorem B830171 : Blo 550806 830171 := bstep (se 1 (by rfl) ⟨622628, by rfl⟩ : syracuseStep 830171 = 1245257) B1245257
theorem B3156731 : Blo 550806 3156731 := bstep (se 1 (by rfl) ⟨2367548, by rfl⟩ : syracuseStep 3156731 = 4735097) B4735097
theorem B831359 : Blo 550806 831359 := bstep (se 1 (by rfl) ⟨623519, by rfl⟩ : syracuseStep 831359 = 1247039) B1247039
theorem B930359 : Blo 550806 930359 := bstep (se 1 (by rfl) ⟨697769, by rfl⟩ : syracuseStep 930359 = 1395539) B1395539
theorem B3158939 : Blo 550806 3158939 := bstep (se 1 (by rfl) ⟨2369204, by rfl⟩ : syracuseStep 3158939 = 4738409) B4738409
theorem B18364157 : Blo 550806 18364157 := bstep (se 3 (by rfl) ⟨3443279, by rfl⟩ : syracuseStep 18364157 = 6886559) B6886559
theorem B76560719 : Blo 550806 76560719 := bstep (se 1 (by rfl) ⟨57420539, by rfl⟩ : syracuseStep 76560719 = 114841079) B114841079
theorem B1395103 : Blo 550806 1395103 := bstep (se 1 (by rfl) ⟨1046327, by rfl⟩ : syracuseStep 1395103 = 2092655) B2092655
theorem B1495199 : Blo 550806 1495199 := bstep (se 1 (by rfl) ⟨1121399, by rfl⟩ : syracuseStep 1495199 = 2242799) B2242799
theorem B47829689 : Blo 550806 47829689 := bstep (se 2 (by rfl) ⟨17936133, by rfl⟩ : syracuseStep 47829689 = 35872267) B35872267
theorem B9425969 : Blo 550806 9425969 := bstep (se 2 (by rfl) ⟨3534738, by rfl⟩ : syracuseStep 9425969 = 7069477) B7069477
theorem B1398779 : Blo 550806 1398779 := bstep (se 1 (by rfl) ⟨1049084, by rfl⟩ : syracuseStep 1398779 = 2098169) B2098169
theorem B6903863 : Blo 550806 6903863 := bstep (se 1 (by rfl) ⟨5177897, by rfl⟩ : syracuseStep 6903863 = 10355795) B10355795
theorem B1398991 : Blo 550806 1398991 := bstep (se 1 (by rfl) ⟨1049243, by rfl⟩ : syracuseStep 1398991 = 2098487) B2098487
theorem B276752821 : Blo 550806 276752821 := bstep (se 5 (by rfl) ⟨12972788, by rfl⟩ : syracuseStep 276752821 = 25945577) B25945577
theorem B551535 : Blo 550806 551535 := bstep (se 1 (by rfl) ⟨413651, by rfl⟩ : syracuseStep 551535 = 827303) B827303
theorem B10054631 : Blo 550806 10054631 := bstep (se 1 (by rfl) ⟨7540973, by rfl⟩ : syracuseStep 10054631 = 15081947) B15081947
theorem B15985673 : Blo 550806 15985673 := bstep (se 2 (by rfl) ⟨5994627, by rfl⟩ : syracuseStep 15985673 = 11989255) B11989255
theorem B5991515 : Blo 550806 5991515 := bstep (se 1 (by rfl) ⟨4493636, by rfl⟩ : syracuseStep 5991515 = 8987273) B8987273
theorem B553031 : Blo 550806 553031 := bstep (se 1 (by rfl) ⟨414773, by rfl⟩ : syracuseStep 553031 = 829547) B829547
theorem B114782953 : Blo 550806 114782953 := bstep (se 2 (by rfl) ⟨43043607, by rfl⟩ : syracuseStep 114782953 = 86087215) B86087215
theorem B96695147 : Blo 550806 96695147 := bstep (se 1 (by rfl) ⟨72521360, by rfl⟩ : syracuseStep 96695147 = 145042721) B145042721
theorem B1209215 : Blo 550806 1209215 := bstep (se 1 (by rfl) ⟨906911, by rfl⟩ : syracuseStep 1209215 = 1813823) B1813823
theorem B1569743 : Blo 550806 1569743 := bstep (se 1 (by rfl) ⟨1177307, by rfl⟩ : syracuseStep 1569743 = 2354615) B2354615
theorem B4191263 : Blo 550806 4191263 := bstep (se 1 (by rfl) ⟨3143447, by rfl⟩ : syracuseStep 4191263 = 6286895) B6286895
theorem B2980799 : Blo 550806 2980799 := bstep (se 1 (by rfl) ⟨2235599, by rfl⟩ : syracuseStep 2980799 = 4471199) B4471199
theorem B1867319 : Blo 550806 1867319 := bstep (se 1 (by rfl) ⟨1400489, by rfl⟩ : syracuseStep 1867319 = 2800979) B2800979
theorem B1244843 : Blo 550806 1244843 := bstep (se 1 (by rfl) ⟨933632, by rfl⟩ : syracuseStep 1244843 = 1867265) B1867265
theorem B257853725 : Blo 550806 257853725 := bstep (se 3 (by rfl) ⟨48347573, by rfl⟩ : syracuseStep 257853725 = 96695147) B96695147
theorem B31886459 : Blo 550806 31886459 := bstep (se 1 (by rfl) ⟨23914844, by rfl⟩ : syracuseStep 31886459 = 47829689) B47829689
theorem B369003761 : Blo 550806 369003761 := bstep (se 2 (by rfl) ⟨138376410, by rfl⟩ : syracuseStep 369003761 = 276752821) B276752821
theorem B2104487 : Blo 550806 2104487 := bstep (se 1 (by rfl) ⟨1578365, by rfl⟩ : syracuseStep 2104487 = 3156731) B3156731
theorem B10657115 : Blo 550806 10657115 := bstep (se 1 (by rfl) ⟨7992836, by rfl⟩ : syracuseStep 10657115 = 15985673) B15985673
theorem B2105959 : Blo 550806 2105959 := bstep (se 1 (by rfl) ⟨1579469, by rfl⟩ : syracuseStep 2105959 = 3158939) B3158939
theorem B2794175 : Blo 550806 2794175 := bstep (se 1 (by rfl) ⟨2095631, by rfl⟩ : syracuseStep 2794175 = 4191263) B4191263
theorem B829895 : Blo 550806 829895 := bstep (se 1 (by rfl) ⟨622421, by rfl⟩ : syracuseStep 829895 = 1244843) B1244843
theorem B1683071 : Blo 550806 1683071 := bstep (se 1 (by rfl) ⟨1262303, by rfl⟩ : syracuseStep 1683071 = 2524607) B2524607
theorem B700159 : Blo 550806 700159 := bstep (se 1 (by rfl) ⟨525119, by rfl⟩ : syracuseStep 700159 = 1050239) B1050239
theorem B3224573 : Blo 550806 3224573 := bstep (se 3 (by rfl) ⟨604607, by rfl⟩ : syracuseStep 3224573 = 1209215) B1209215
theorem B996799 : Blo 550806 996799 := bstep (se 1 (by rfl) ⟨747599, by rfl⟩ : syracuseStep 996799 = 1495199) B1495199
theorem B932519 : Blo 550806 932519 := bstep (se 1 (by rfl) ⟨699389, by rfl⟩ : syracuseStep 932519 = 1398779) B1398779
theorem B4602575 : Blo 550806 4602575 := bstep (se 1 (by rfl) ⟨3451931, by rfl⟩ : syracuseStep 4602575 = 6903863) B6903863
theorem B204161917 : Blo 550806 204161917 := bstep (se 3 (by rfl) ⟨38280359, by rfl⟩ : syracuseStep 204161917 = 76560719) B76560719
theorem B153043937 : Blo 550806 153043937 := bstep (se 2 (by rfl) ⟨57391476, by rfl⟩ : syracuseStep 153043937 = 114782953) B114782953
theorem B6703087 : Blo 550806 6703087 := bstep (se 1 (by rfl) ⟨5027315, by rfl⟩ : syracuseStep 6703087 = 10054631) B10054631
theorem B5295617 : Blo 550806 5295617 := bstep (se 2 (by rfl) ⟨1985856, by rfl⟩ : syracuseStep 5295617 = 3971713) B3971713
theorem B12242771 : Blo 550806 12242771 := bstep (se 1 (by rfl) ⟨9182078, by rfl⟩ : syracuseStep 12242771 = 18364157) B18364157
theorem B1987199 : Blo 550806 1987199 := bstep (se 1 (by rfl) ⟨1490399, by rfl⟩ : syracuseStep 1987199 = 2980799) B2980799
theorem B1860137 : Blo 550806 1860137 := bstep (se 2 (by rfl) ⟨697551, by rfl⟩ : syracuseStep 1860137 = 1395103) B1395103
theorem B6283979 : Blo 550806 6283979 := bstep (se 1 (by rfl) ⟨4712984, by rfl⟩ : syracuseStep 6283979 = 9425969) B9425969
theorem B552863 : Blo 550806 552863 := bstep (se 1 (by rfl) ⟨414647, by rfl⟩ : syracuseStep 552863 = 829295) B829295
theorem B1863863 : Blo 550806 1863863 := bstep (se 1 (by rfl) ⟨1397897, by rfl⟩ : syracuseStep 1863863 = 2795795) B2795795
theorem B553447 : Blo 550806 553447 := bstep (se 1 (by rfl) ⟨415085, by rfl⟩ : syracuseStep 553447 = 830171) B830171
theorem B3994343 : Blo 550806 3994343 := bstep (se 1 (by rfl) ⟨2995757, by rfl⟩ : syracuseStep 3994343 = 5991515) B5991515
theorem B554239 : Blo 550806 554239 := bstep (se 1 (by rfl) ⟨415679, by rfl⟩ : syracuseStep 554239 = 831359) B831359
theorem B1865321 : Blo 550806 1865321 := bstep (se 2 (by rfl) ⟨699495, by rfl⟩ : syracuseStep 1865321 = 1398991) B1398991
theorem B620239 : Blo 550806 620239 := bstep (se 1 (by rfl) ⟨465179, by rfl⟩ : syracuseStep 620239 = 930359) B930359
theorem B1046495 : Blo 550806 1046495 := bstep (se 1 (by rfl) ⟨784871, by rfl⟩ : syracuseStep 1046495 = 1569743) B1569743
theorem B1244879 : Blo 550806 1244879 := bstep (se 1 (by rfl) ⟨933659, by rfl⟩ : syracuseStep 1244879 = 1867319) B1867319
theorem B171902483 : Blo 550806 171902483 := bstep (se 1 (by rfl) ⟨128926862, by rfl⟩ : syracuseStep 171902483 = 257853725) B257853725
theorem B8161847 : Blo 550806 8161847 := bstep (se 1 (by rfl) ⟨6121385, by rfl⟩ : syracuseStep 8161847 = 12242771) B12242771
theorem B826985 : Blo 550806 826985 := bstep (se 2 (by rfl) ⟨310119, by rfl⟩ : syracuseStep 826985 = 620239) B620239
theorem B1122047 : Blo 550806 1122047 := bstep (se 1 (by rfl) ⟨841535, by rfl⟩ : syracuseStep 1122047 = 1683071) B1683071
theorem B2662895 : Blo 550806 2662895 := bstep (se 1 (by rfl) ⟨1997171, by rfl⟩ : syracuseStep 2662895 = 3994343) B3994343
theorem B697663 : Blo 550806 697663 := bstep (se 1 (by rfl) ⟨523247, by rfl⟩ : syracuseStep 697663 = 1046495) B1046495
theorem B829919 : Blo 550806 829919 := bstep (se 1 (by rfl) ⟨622439, by rfl⟩ : syracuseStep 829919 = 1244879) B1244879
theorem B272215889 : Blo 550806 272215889 := bstep (se 2 (by rfl) ⟨102080958, by rfl⟩ : syracuseStep 272215889 = 204161917) B204161917
theorem B246002507 : Blo 550806 246002507 := bstep (se 1 (by rfl) ⟨184501880, by rfl⟩ : syracuseStep 246002507 = 369003761) B369003761
theorem B1324799 : Blo 550806 1324799 := bstep (se 1 (by rfl) ⟨993599, by rfl⟩ : syracuseStep 1324799 = 1987199) B1987199
theorem B933545 : Blo 550806 933545 := bstep (se 2 (by rfl) ⟨350079, by rfl⟩ : syracuseStep 933545 = 700159) B700159
theorem B1329065 : Blo 550806 1329065 := bstep (se 2 (by rfl) ⟨498399, by rfl⟩ : syracuseStep 1329065 = 996799) B996799
theorem B2149715 : Blo 550806 2149715 := bstep (se 1 (by rfl) ⟨1612286, by rfl⟩ : syracuseStep 2149715 = 3224573) B3224573
theorem B3068383 : Blo 550806 3068383 := bstep (se 1 (by rfl) ⟨2301287, by rfl⟩ : syracuseStep 3068383 = 4602575) B4602575
theorem B102029291 : Blo 550806 102029291 := bstep (se 1 (by rfl) ⟨76521968, by rfl⟩ : syracuseStep 102029291 = 153043937) B153043937
theorem B2807945 : Blo 550806 2807945 := bstep (se 2 (by rfl) ⟨1052979, by rfl⟩ : syracuseStep 2807945 = 2105959) B2105959
theorem B21257639 : Blo 550806 21257639 := bstep (se 1 (by rfl) ⟨15943229, by rfl⟩ : syracuseStep 21257639 = 31886459) B31886459
theorem B3530411 : Blo 550806 3530411 := bstep (se 1 (by rfl) ⟨2647808, by rfl⟩ : syracuseStep 3530411 = 5295617) B5295617
theorem B8937449 : Blo 550806 8937449 := bstep (se 2 (by rfl) ⟨3351543, by rfl⟩ : syracuseStep 8937449 = 6703087) B6703087
theorem B1402991 : Blo 550806 1402991 := bstep (se 1 (by rfl) ⟨1052243, by rfl⟩ : syracuseStep 1402991 = 2104487) B2104487
theorem B7104743 : Blo 550806 7104743 := bstep (se 1 (by rfl) ⟨5328557, by rfl⟩ : syracuseStep 7104743 = 10657115) B10657115
theorem B1240091 : Blo 550806 1240091 := bstep (se 1 (by rfl) ⟨930068, by rfl⟩ : syracuseStep 1240091 = 1860137) B1860137
theorem B1862783 : Blo 550806 1862783 := bstep (se 1 (by rfl) ⟨1397087, by rfl⟩ : syracuseStep 1862783 = 2794175) B2794175
theorem B4189319 : Blo 550806 4189319 := bstep (se 1 (by rfl) ⟨3141989, by rfl⟩ : syracuseStep 4189319 = 6283979) B6283979
theorem B553263 : Blo 550806 553263 := bstep (se 1 (by rfl) ⟨414947, by rfl⟩ : syracuseStep 553263 = 829895) B829895
theorem B1242575 : Blo 550806 1242575 := bstep (se 1 (by rfl) ⟨931931, by rfl⟩ : syracuseStep 1242575 = 1863863) B1863863
theorem B1243547 : Blo 550806 1243547 := bstep (se 1 (by rfl) ⟨932660, by rfl⟩ : syracuseStep 1243547 = 1865321) B1865321
theorem B621679 : Blo 550806 621679 := bstep (se 1 (by rfl) ⟨466259, by rfl⟩ : syracuseStep 621679 = 932519) B932519
theorem B886043 : Blo 550806 886043 := bstep (se 1 (by rfl) ⟨664532, by rfl⟩ : syracuseStep 886043 = 1329065) B1329065
theorem B5441231 : Blo 550806 5441231 := bstep (se 1 (by rfl) ⟨4080923, by rfl⟩ : syracuseStep 5441231 = 8161847) B8161847
theorem B1871963 : Blo 550806 1871963 := bstep (se 1 (by rfl) ⟨1403972, by rfl⟩ : syracuseStep 1871963 = 2807945) B2807945
theorem B826727 : Blo 550806 826727 := bstep (se 1 (by rfl) ⟨620045, by rfl⟩ : syracuseStep 826727 = 1240091) B1240091
theorem B2792879 : Blo 550806 2792879 := bstep (se 1 (by rfl) ⟨2094659, by rfl⟩ : syracuseStep 2792879 = 4189319) B4189319
theorem B181477259 : Blo 550806 181477259 := bstep (se 1 (by rfl) ⟨136107944, by rfl⟩ : syracuseStep 181477259 = 272215889) B272215889
theorem B828383 : Blo 550806 828383 := bstep (se 1 (by rfl) ⟨621287, by rfl⟩ : syracuseStep 828383 = 1242575) B1242575
theorem B828905 : Blo 550806 828905 := bstep (se 2 (by rfl) ⟨310839, by rfl⟩ : syracuseStep 828905 = 621679) B621679
theorem B829031 : Blo 550806 829031 := bstep (se 1 (by rfl) ⟨621773, by rfl⟩ : syracuseStep 829031 = 1243547) B1243547
theorem B114601655 : Blo 550806 114601655 := bstep (se 1 (by rfl) ⟨85951241, by rfl⟩ : syracuseStep 114601655 = 171902483) B171902483
theorem B930217 : Blo 550806 930217 := bstep (se 2 (by rfl) ⟨348831, by rfl⟩ : syracuseStep 930217 = 697663) B697663
theorem B14171759 : Blo 550806 14171759 := bstep (se 1 (by rfl) ⟨10628819, by rfl⟩ : syracuseStep 14171759 = 21257639) B21257639
theorem B935327 : Blo 550806 935327 := bstep (se 1 (by rfl) ⟨701495, by rfl⟩ : syracuseStep 935327 = 1402991) B1402991
theorem B4736495 : Blo 550806 4736495 := bstep (se 1 (by rfl) ⟨3552371, by rfl⟩ : syracuseStep 4736495 = 7104743) B7104743
theorem B7101053 : Blo 550806 7101053 := bstep (se 3 (by rfl) ⟨1331447, by rfl⟩ : syracuseStep 7101053 = 2662895) B2662895
theorem B1433143 : Blo 550806 1433143 := bstep (se 1 (by rfl) ⟨1074857, by rfl⟩ : syracuseStep 1433143 = 2149715) B2149715
theorem B68019527 : Blo 550806 68019527 := bstep (se 1 (by rfl) ⟨51014645, by rfl⟩ : syracuseStep 68019527 = 102029291) B102029291
theorem B551323 : Blo 550806 551323 := bstep (se 1 (by rfl) ⟨413492, by rfl⟩ : syracuseStep 551323 = 826985) B826985
theorem B2353607 : Blo 550806 2353607 := bstep (se 1 (by rfl) ⟨1765205, by rfl⟩ : syracuseStep 2353607 = 3530411) B3530411
theorem B748031 : Blo 550806 748031 := bstep (se 1 (by rfl) ⟨561023, by rfl⟩ : syracuseStep 748031 = 1122047) B1122047
theorem B5958299 : Blo 550806 5958299 := bstep (se 1 (by rfl) ⟨4468724, by rfl⟩ : syracuseStep 5958299 = 8937449) B8937449
theorem B4091177 : Blo 550806 4091177 := bstep (se 2 (by rfl) ⟨1534191, by rfl⟩ : syracuseStep 4091177 = 3068383) B3068383
theorem B553279 : Blo 550806 553279 := bstep (se 1 (by rfl) ⟨414959, by rfl⟩ : syracuseStep 553279 = 829919) B829919
theorem B1241855 : Blo 550806 1241855 := bstep (se 1 (by rfl) ⟨931391, by rfl⟩ : syracuseStep 1241855 = 1862783) B1862783
theorem B164001671 : Blo 550806 164001671 := bstep (se 1 (by rfl) ⟨123001253, by rfl⟩ : syracuseStep 164001671 = 246002507) B246002507
theorem B883199 : Blo 550806 883199 := bstep (se 1 (by rfl) ⟨662399, by rfl⟩ : syracuseStep 883199 = 1324799) B1324799
theorem B622363 : Blo 550806 622363 := bstep (se 1 (by rfl) ⟨466772, by rfl⟩ : syracuseStep 622363 = 933545) B933545
theorem B590695 : Blo 550806 590695 := bstep (se 1 (by rfl) ⟨443021, by rfl⟩ : syracuseStep 590695 = 886043) B886043
theorem B623551 : Blo 550806 623551 := bstep (se 1 (by rfl) ⟨467663, by rfl⟩ : syracuseStep 623551 = 935327) B935327
theorem B1247975 : Blo 550806 1247975 := bstep (se 1 (by rfl) ⟨935981, by rfl⟩ : syracuseStep 1247975 = 1871963) B1871963
theorem B120984839 : Blo 550806 120984839 := bstep (se 1 (by rfl) ⟨90738629, by rfl⟩ : syracuseStep 120984839 = 181477259) B181477259
theorem B2727451 : Blo 550806 2727451 := bstep (se 1 (by rfl) ⟨2045588, by rfl⟩ : syracuseStep 2727451 = 4091177) B4091177
theorem B7643429 : Blo 550806 7643429 := bstep (se 4 (by rfl) ⟨716571, by rfl⟩ : syracuseStep 7643429 = 1433143) B1433143
theorem B827903 : Blo 550806 827903 := bstep (se 1 (by rfl) ⟨620927, by rfl⟩ : syracuseStep 827903 = 1241855) B1241855
theorem B829817 : Blo 550806 829817 := bstep (se 2 (by rfl) ⟨311181, by rfl⟩ : syracuseStep 829817 = 622363) B622363
theorem B9447839 : Blo 550806 9447839 := bstep (se 1 (by rfl) ⟨7085879, by rfl⟩ : syracuseStep 9447839 = 14171759) B14171759
theorem B3157663 : Blo 550806 3157663 := bstep (se 1 (by rfl) ⟨2368247, by rfl⟩ : syracuseStep 3157663 = 4736495) B4736495
theorem B4734035 : Blo 550806 4734035 := bstep (se 1 (by rfl) ⟨3550526, by rfl⟩ : syracuseStep 4734035 = 7101053) B7101053
theorem B76401103 : Blo 550806 76401103 := bstep (se 1 (by rfl) ⟨57300827, by rfl⟩ : syracuseStep 76401103 = 114601655) B114601655
theorem B109334447 : Blo 550806 109334447 := bstep (se 1 (by rfl) ⟨82000835, by rfl⟩ : syracuseStep 109334447 = 164001671) B164001671
theorem B3627487 : Blo 550806 3627487 := bstep (se 1 (by rfl) ⟨2720615, by rfl⟩ : syracuseStep 3627487 = 5441231) B5441231
theorem B551151 : Blo 550806 551151 := bstep (se 1 (by rfl) ⟨413363, by rfl⟩ : syracuseStep 551151 = 826727) B826727
theorem B1861919 : Blo 550806 1861919 := bstep (se 1 (by rfl) ⟨1396439, by rfl⟩ : syracuseStep 1861919 = 2792879) B2792879
theorem B1240289 : Blo 550806 1240289 := bstep (se 2 (by rfl) ⟨465108, by rfl⟩ : syracuseStep 1240289 = 930217) B930217
theorem B552255 : Blo 550806 552255 := bstep (se 1 (by rfl) ⟨414191, by rfl⟩ : syracuseStep 552255 = 828383) B828383
theorem B45346351 : Blo 550806 45346351 := bstep (se 1 (by rfl) ⟨34009763, by rfl⟩ : syracuseStep 45346351 = 68019527) B68019527
theorem B552603 : Blo 550806 552603 := bstep (se 1 (by rfl) ⟨414452, by rfl⟩ : syracuseStep 552603 = 828905) B828905
theorem B552687 : Blo 550806 552687 := bstep (se 1 (by rfl) ⟨414515, by rfl⟩ : syracuseStep 552687 = 829031) B829031
theorem B1994749 : Blo 550806 1994749 := bstep (se 3 (by rfl) ⟨374015, by rfl⟩ : syracuseStep 1994749 = 748031) B748031
theorem B1569071 : Blo 550806 1569071 := bstep (se 1 (by rfl) ⟨1176803, by rfl⟩ : syracuseStep 1569071 = 2353607) B2353607
theorem B15888797 : Blo 550806 15888797 := bstep (se 3 (by rfl) ⟨2979149, by rfl⟩ : syracuseStep 15888797 = 5958299) B5958299
theorem B588799 : Blo 550806 588799 := bstep (se 1 (by rfl) ⟨441599, by rfl⟩ : syracuseStep 588799 = 883199) B883199
theorem B3150373 : Blo 550806 3150373 := bstep (se 4 (by rfl) ⟨295347, by rfl⟩ : syracuseStep 3150373 = 590695) B590695
theorem B60461801 : Blo 550806 60461801 := bstep (se 2 (by rfl) ⟨22673175, by rfl⟩ : syracuseStep 60461801 = 45346351) B45346351
theorem B6298559 : Blo 550806 6298559 := bstep (se 1 (by rfl) ⟨4723919, by rfl⟩ : syracuseStep 6298559 = 9447839) B9447839
theorem B826859 : Blo 550806 826859 := bstep (se 1 (by rfl) ⟨620144, by rfl⟩ : syracuseStep 826859 = 1240289) B1240289
theorem B10592531 : Blo 550806 10592531 := bstep (se 1 (by rfl) ⟨7944398, by rfl⟩ : syracuseStep 10592531 = 15888797) B15888797
theorem B3156023 : Blo 550806 3156023 := bstep (se 1 (by rfl) ⟨2367017, by rfl⟩ : syracuseStep 3156023 = 4734035) B4734035
theorem B831401 : Blo 550806 831401 := bstep (se 2 (by rfl) ⟨311775, by rfl⟩ : syracuseStep 831401 = 623551) B623551
theorem B831983 : Blo 550806 831983 := bstep (se 1 (by rfl) ⟨623987, by rfl⟩ : syracuseStep 831983 = 1247975) B1247975
theorem B19346597 : Blo 550806 19346597 := bstep (se 4 (by rfl) ⟨1813743, by rfl⟩ : syracuseStep 19346597 = 3627487) B3627487
theorem B72889631 : Blo 550806 72889631 := bstep (se 1 (by rfl) ⟨54667223, by rfl⟩ : syracuseStep 72889631 = 109334447) B109334447
theorem B80656559 : Blo 550806 80656559 := bstep (se 1 (by rfl) ⟨60492419, by rfl⟩ : syracuseStep 80656559 = 120984839) B120984839
theorem B4210217 : Blo 550806 4210217 := bstep (se 2 (by rfl) ⟨1578831, by rfl⟩ : syracuseStep 4210217 = 3157663) B3157663
theorem B5095619 : Blo 550806 5095619 := bstep (se 1 (by rfl) ⟨3821714, by rfl⟩ : syracuseStep 5095619 = 7643429) B7643429
theorem B10638661 : Blo 550806 10638661 := bstep (se 4 (by rfl) ⟨997374, by rfl⟩ : syracuseStep 10638661 = 1994749) B1994749
theorem B101868137 : Blo 550806 101868137 := bstep (se 2 (by rfl) ⟨38200551, by rfl⟩ : syracuseStep 101868137 = 76401103) B76401103
theorem B551935 : Blo 550806 551935 := bstep (se 1 (by rfl) ⟨413951, by rfl⟩ : syracuseStep 551935 = 827903) B827903
theorem B1241279 : Blo 550806 1241279 := bstep (se 1 (by rfl) ⟨930959, by rfl⟩ : syracuseStep 1241279 = 1861919) B1861919
theorem B553211 : Blo 550806 553211 := bstep (se 1 (by rfl) ⟨414908, by rfl⟩ : syracuseStep 553211 = 829817) B829817
theorem B14546405 : Blo 550806 14546405 := bstep (se 4 (by rfl) ⟨1363725, by rfl⟩ : syracuseStep 14546405 = 2727451) B2727451
theorem B1046047 : Blo 550806 1046047 := bstep (se 1 (by rfl) ⟨784535, by rfl⟩ : syracuseStep 1046047 = 1569071) B1569071
theorem B785065 : Blo 550806 785065 := bstep (se 2 (by rfl) ⟨294399, by rfl⟩ : syracuseStep 785065 = 588799) B588799
theorem B40307867 : Blo 550806 40307867 := bstep (se 1 (by rfl) ⟨30230900, by rfl⟩ : syracuseStep 40307867 = 60461801) B60461801
theorem B4199039 : Blo 550806 4199039 := bstep (se 1 (by rfl) ⟨3149279, by rfl⟩ : syracuseStep 4199039 = 6298559) B6298559
theorem B4200497 : Blo 550806 4200497 := bstep (se 2 (by rfl) ⟨1575186, by rfl⟩ : syracuseStep 4200497 = 3150373) B3150373
theorem B2104015 : Blo 550806 2104015 := bstep (se 1 (by rfl) ⟨1578011, by rfl⟩ : syracuseStep 2104015 = 3156023) B3156023
theorem B827519 : Blo 550806 827519 := bstep (se 1 (by rfl) ⟨620639, by rfl⟩ : syracuseStep 827519 = 1241279) B1241279
theorem B7061687 : Blo 550806 7061687 := bstep (se 1 (by rfl) ⟨5296265, by rfl⟩ : syracuseStep 7061687 = 10592531) B10592531
theorem B67912091 : Blo 550806 67912091 := bstep (se 1 (by rfl) ⟨50934068, by rfl⟩ : syracuseStep 67912091 = 101868137) B101868137
theorem B1394729 : Blo 550806 1394729 := bstep (se 2 (by rfl) ⟨523023, by rfl⟩ : syracuseStep 1394729 = 1046047) B1046047
theorem B12897731 : Blo 550806 12897731 := bstep (se 1 (by rfl) ⟨9673298, by rfl⟩ : syracuseStep 12897731 = 19346597) B19346597
theorem B2806811 : Blo 550806 2806811 := bstep (se 1 (by rfl) ⟨2105108, by rfl⟩ : syracuseStep 2806811 = 4210217) B4210217
theorem B3397079 : Blo 550806 3397079 := bstep (se 1 (by rfl) ⟨2547809, by rfl⟩ : syracuseStep 3397079 = 5095619) B5095619
theorem B551239 : Blo 550806 551239 := bstep (se 1 (by rfl) ⟨413429, by rfl⟩ : syracuseStep 551239 = 826859) B826859
theorem B14184881 : Blo 550806 14184881 := bstep (se 2 (by rfl) ⟨5319330, by rfl⟩ : syracuseStep 14184881 = 10638661) B10638661
theorem B554267 : Blo 550806 554267 := bstep (se 1 (by rfl) ⟨415700, by rfl⟩ : syracuseStep 554267 = 831401) B831401
theorem B554655 : Blo 550806 554655 := bstep (se 1 (by rfl) ⟨415991, by rfl⟩ : syracuseStep 554655 = 831983) B831983
theorem B48593087 : Blo 550806 48593087 := bstep (se 1 (by rfl) ⟨36444815, by rfl⟩ : syracuseStep 48593087 = 72889631) B72889631
theorem B1046753 : Blo 550806 1046753 := bstep (se 2 (by rfl) ⟨392532, by rfl⟩ : syracuseStep 1046753 = 785065) B785065
theorem B9697603 : Blo 550806 9697603 := bstep (se 1 (by rfl) ⟨7273202, by rfl⟩ : syracuseStep 9697603 = 14546405) B14546405
theorem B53771039 : Blo 550806 53771039 := bstep (se 1 (by rfl) ⟨40328279, by rfl⟩ : syracuseStep 53771039 = 80656559) B80656559
theorem B26871911 : Blo 550806 26871911 := bstep (se 1 (by rfl) ⟨20153933, by rfl⟩ : syracuseStep 26871911 = 40307867) B40307867
theorem B1871207 : Blo 550806 1871207 := bstep (se 1 (by rfl) ⟨1403405, by rfl⟩ : syracuseStep 1871207 = 2806811) B2806811
theorem B2264719 : Blo 550806 2264719 := bstep (se 1 (by rfl) ⟨1698539, by rfl⟩ : syracuseStep 2264719 = 3397079) B3397079
theorem B697835 : Blo 550806 697835 := bstep (se 1 (by rfl) ⟨523376, by rfl⟩ : syracuseStep 697835 = 1046753) B1046753
theorem B929819 : Blo 550806 929819 := bstep (se 1 (by rfl) ⟨697364, by rfl⟩ : syracuseStep 929819 = 1394729) B1394729
theorem B8598487 : Blo 550806 8598487 := bstep (se 1 (by rfl) ⟨6448865, by rfl⟩ : syracuseStep 8598487 = 12897731) B12897731
theorem B2799359 : Blo 550806 2799359 := bstep (se 1 (by rfl) ⟨2099519, by rfl⟩ : syracuseStep 2799359 = 4199039) B4199039
theorem B2800331 : Blo 550806 2800331 := bstep (se 1 (by rfl) ⟨2100248, by rfl⟩ : syracuseStep 2800331 = 4200497) B4200497
theorem B9456587 : Blo 550806 9456587 := bstep (se 1 (by rfl) ⟨7092440, by rfl⟩ : syracuseStep 9456587 = 14184881) B14184881
theorem B12930137 : Blo 550806 12930137 := bstep (se 2 (by rfl) ⟨4848801, by rfl⟩ : syracuseStep 12930137 = 9697603) B9697603
theorem B2805353 : Blo 550806 2805353 := bstep (se 2 (by rfl) ⟨1052007, by rfl⟩ : syracuseStep 2805353 = 2104015) B2104015
theorem B32395391 : Blo 550806 32395391 := bstep (se 1 (by rfl) ⟨24296543, by rfl⟩ : syracuseStep 32395391 = 48593087) B48593087
theorem B4707791 : Blo 550806 4707791 := bstep (se 1 (by rfl) ⟨3530843, by rfl⟩ : syracuseStep 4707791 = 7061687) B7061687
theorem B45274727 : Blo 550806 45274727 := bstep (se 1 (by rfl) ⟨33956045, by rfl⟩ : syracuseStep 45274727 = 67912091) B67912091
theorem B551679 : Blo 550806 551679 := bstep (se 1 (by rfl) ⟨413759, by rfl⟩ : syracuseStep 551679 = 827519) B827519
theorem B35847359 : Blo 550806 35847359 := bstep (se 1 (by rfl) ⟨26885519, by rfl⟩ : syracuseStep 35847359 = 53771039) B53771039
theorem B8620091 : Blo 550806 8620091 := bstep (se 1 (by rfl) ⟨6465068, by rfl⟩ : syracuseStep 8620091 = 12930137) B12930137
theorem B1247471 : Blo 550806 1247471 := bstep (se 1 (by rfl) ⟨935603, by rfl⟩ : syracuseStep 1247471 = 1871207) B1871207
theorem B1870235 : Blo 550806 1870235 := bstep (se 1 (by rfl) ⟨1402676, by rfl⟩ : syracuseStep 1870235 = 2805353) B2805353
theorem B21596927 : Blo 550806 21596927 := bstep (se 1 (by rfl) ⟨16197695, by rfl⟩ : syracuseStep 21596927 = 32395391) B32395391
theorem B3019625 : Blo 550806 3019625 := bstep (se 2 (by rfl) ⟨1132359, by rfl⟩ : syracuseStep 3019625 = 2264719) B2264719
theorem B23898239 : Blo 550806 23898239 := bstep (se 1 (by rfl) ⟨17923679, by rfl⟩ : syracuseStep 23898239 = 35847359) B35847359
theorem B6304391 : Blo 550806 6304391 := bstep (se 1 (by rfl) ⟨4728293, by rfl⟩ : syracuseStep 6304391 = 9456587) B9456587
theorem B120732605 : Blo 550806 120732605 := bstep (se 3 (by rfl) ⟨22637363, by rfl⟩ : syracuseStep 120732605 = 45274727) B45274727
theorem B17914607 : Blo 550806 17914607 := bstep (se 1 (by rfl) ⟨13435955, by rfl⟩ : syracuseStep 17914607 = 26871911) B26871911
theorem B3138527 : Blo 550806 3138527 := bstep (se 1 (by rfl) ⟨2353895, by rfl⟩ : syracuseStep 3138527 = 4707791) B4707791
theorem B1860893 : Blo 550806 1860893 := bstep (se 3 (by rfl) ⟨348917, by rfl⟩ : syracuseStep 1860893 = 697835) B697835
theorem B11464649 : Blo 550806 11464649 := bstep (se 2 (by rfl) ⟨4299243, by rfl⟩ : syracuseStep 11464649 = 8598487) B8598487
theorem B619879 : Blo 550806 619879 := bstep (se 1 (by rfl) ⟨464909, by rfl⟩ : syracuseStep 619879 = 929819) B929819
theorem B1866239 : Blo 550806 1866239 := bstep (se 1 (by rfl) ⟨1399679, by rfl⟩ : syracuseStep 1866239 = 2799359) B2799359
theorem B1866887 : Blo 550806 1866887 := bstep (se 1 (by rfl) ⟨1400165, by rfl⟩ : syracuseStep 1866887 = 2800331) B2800331
theorem B1246823 : Blo 550806 1246823 := bstep (se 1 (by rfl) ⟨935117, by rfl⟩ : syracuseStep 1246823 = 1870235) B1870235
theorem B15932159 : Blo 550806 15932159 := bstep (se 1 (by rfl) ⟨11949119, by rfl⟩ : syracuseStep 15932159 = 23898239) B23898239
theorem B826505 : Blo 550806 826505 := bstep (se 2 (by rfl) ⟨309939, by rfl⟩ : syracuseStep 826505 = 619879) B619879
theorem B7643099 : Blo 550806 7643099 := bstep (se 1 (by rfl) ⟨5732324, by rfl⟩ : syracuseStep 7643099 = 11464649) B11464649
theorem B4202927 : Blo 550806 4202927 := bstep (se 1 (by rfl) ⟨3152195, by rfl⟩ : syracuseStep 4202927 = 6304391) B6304391
theorem B80488403 : Blo 550806 80488403 := bstep (se 1 (by rfl) ⟨60366302, by rfl⟩ : syracuseStep 80488403 = 120732605) B120732605
theorem B5746727 : Blo 550806 5746727 := bstep (se 1 (by rfl) ⟨4310045, by rfl⟩ : syracuseStep 5746727 = 8620091) B8620091
theorem B831647 : Blo 550806 831647 := bstep (se 1 (by rfl) ⟨623735, by rfl⟩ : syracuseStep 831647 = 1247471) B1247471
theorem B2013083 : Blo 550806 2013083 := bstep (se 1 (by rfl) ⟨1509812, by rfl⟩ : syracuseStep 2013083 = 3019625) B3019625
theorem B11943071 : Blo 550806 11943071 := bstep (se 1 (by rfl) ⟨8957303, by rfl⟩ : syracuseStep 11943071 = 17914607) B17914607
theorem B57591805 : Blo 550806 57591805 := bstep (se 3 (by rfl) ⟨10798463, by rfl⟩ : syracuseStep 57591805 = 21596927) B21596927
theorem B2092351 : Blo 550806 2092351 := bstep (se 1 (by rfl) ⟨1569263, by rfl⟩ : syracuseStep 2092351 = 3138527) B3138527
theorem B1240595 : Blo 550806 1240595 := bstep (se 1 (by rfl) ⟨930446, by rfl⟩ : syracuseStep 1240595 = 1860893) B1860893
theorem B1244159 : Blo 550806 1244159 := bstep (se 1 (by rfl) ⟨933119, by rfl⟩ : syracuseStep 1244159 = 1866239) B1866239
theorem B1244591 : Blo 550806 1244591 := bstep (se 1 (by rfl) ⟨933443, by rfl⟩ : syracuseStep 1244591 = 1866887) B1866887
theorem B2789801 : Blo 550806 2789801 := bstep (se 2 (by rfl) ⟨1046175, by rfl⟩ : syracuseStep 2789801 = 2092351) B2092351
theorem B10621439 : Blo 550806 10621439 := bstep (se 1 (by rfl) ⟨7966079, by rfl⟩ : syracuseStep 10621439 = 15932159) B15932159
theorem B827063 : Blo 550806 827063 := bstep (se 1 (by rfl) ⟨620297, by rfl⟩ : syracuseStep 827063 = 1240595) B1240595
theorem B829439 : Blo 550806 829439 := bstep (se 1 (by rfl) ⟨622079, by rfl⟩ : syracuseStep 829439 = 1244159) B1244159
theorem B829727 : Blo 550806 829727 := bstep (se 1 (by rfl) ⟨622295, by rfl⟩ : syracuseStep 829727 = 1244591) B1244591
theorem B831215 : Blo 550806 831215 := bstep (se 1 (by rfl) ⟨623411, by rfl⟩ : syracuseStep 831215 = 1246823) B1246823
theorem B76789073 : Blo 550806 76789073 := bstep (se 2 (by rfl) ⟨28795902, by rfl⟩ : syracuseStep 76789073 = 57591805) B57591805
theorem B5095399 : Blo 550806 5095399 := bstep (se 1 (by rfl) ⟨3821549, by rfl⟩ : syracuseStep 5095399 = 7643099) B7643099
theorem B2801951 : Blo 550806 2801951 := bstep (se 1 (by rfl) ⟨2101463, by rfl⟩ : syracuseStep 2801951 = 4202927) B4202927
theorem B53658935 : Blo 550806 53658935 := bstep (se 1 (by rfl) ⟨40244201, by rfl⟩ : syracuseStep 53658935 = 80488403) B80488403
theorem B551003 : Blo 550806 551003 := bstep (se 1 (by rfl) ⟨413252, by rfl⟩ : syracuseStep 551003 = 826505) B826505
theorem B3831151 : Blo 550806 3831151 := bstep (se 1 (by rfl) ⟨2873363, by rfl⟩ : syracuseStep 3831151 = 5746727) B5746727
theorem B554431 : Blo 550806 554431 := bstep (se 1 (by rfl) ⟨415823, by rfl⟩ : syracuseStep 554431 = 831647) B831647
theorem B1342055 : Blo 550806 1342055 := bstep (se 1 (by rfl) ⟨1006541, by rfl⟩ : syracuseStep 1342055 = 2013083) B2013083
theorem B7962047 : Blo 550806 7962047 := bstep (se 1 (by rfl) ⟨5971535, by rfl⟩ : syracuseStep 7962047 = 11943071) B11943071
theorem B1867967 : Blo 550806 1867967 := bstep (se 1 (by rfl) ⟨1400975, by rfl⟩ : syracuseStep 1867967 = 2801951) B2801951
theorem B7080959 : Blo 550806 7080959 := bstep (se 1 (by rfl) ⟨5310719, by rfl⟩ : syracuseStep 7080959 = 10621439) B10621439
theorem B204770861 : Blo 550806 204770861 := bstep (se 3 (by rfl) ⟨38394536, by rfl⟩ : syracuseStep 204770861 = 76789073) B76789073
theorem B3578813 : Blo 550806 3578813 := bstep (se 3 (by rfl) ⟨671027, by rfl⟩ : syracuseStep 3578813 = 1342055) B1342055
theorem B6793865 : Blo 550806 6793865 := bstep (se 2 (by rfl) ⟨2547699, by rfl⟩ : syracuseStep 6793865 = 5095399) B5095399
theorem B35772623 : Blo 550806 35772623 := bstep (se 1 (by rfl) ⟨26829467, by rfl⟩ : syracuseStep 35772623 = 53658935) B53658935
theorem B1859867 : Blo 550806 1859867 := bstep (se 1 (by rfl) ⟨1394900, by rfl⟩ : syracuseStep 1859867 = 2789801) B2789801
theorem B551375 : Blo 550806 551375 := bstep (se 1 (by rfl) ⟨413531, by rfl⟩ : syracuseStep 551375 = 827063) B827063
theorem B552959 : Blo 550806 552959 := bstep (se 1 (by rfl) ⟨414719, by rfl⟩ : syracuseStep 552959 = 829439) B829439
theorem B553151 : Blo 550806 553151 := bstep (se 1 (by rfl) ⟨414863, by rfl⟩ : syracuseStep 553151 = 829727) B829727
theorem B5108201 : Blo 550806 5108201 := bstep (se 2 (by rfl) ⟨1915575, by rfl⟩ : syracuseStep 5108201 = 3831151) B3831151
theorem B554143 : Blo 550806 554143 := bstep (se 1 (by rfl) ⟨415607, by rfl⟩ : syracuseStep 554143 = 831215) B831215
theorem B5308031 : Blo 550806 5308031 := bstep (se 1 (by rfl) ⟨3981023, by rfl⟩ : syracuseStep 5308031 = 7962047) B7962047
theorem B1245311 : Blo 550806 1245311 := bstep (se 1 (by rfl) ⟨933983, by rfl⟩ : syracuseStep 1245311 = 1867967) B1867967
theorem B4720639 : Blo 550806 4720639 := bstep (se 1 (by rfl) ⟨3540479, by rfl⟩ : syracuseStep 4720639 = 7080959) B7080959
theorem B136513907 : Blo 550806 136513907 := bstep (se 1 (by rfl) ⟨102385430, by rfl⟩ : syracuseStep 136513907 = 204770861) B204770861
theorem B4529243 : Blo 550806 4529243 := bstep (se 1 (by rfl) ⟨3396932, by rfl⟩ : syracuseStep 4529243 = 6793865) B6793865
theorem B23848415 : Blo 550806 23848415 := bstep (se 1 (by rfl) ⟨17886311, by rfl⟩ : syracuseStep 23848415 = 35772623) B35772623
theorem B2385875 : Blo 550806 2385875 := bstep (se 1 (by rfl) ⟨1789406, by rfl⟩ : syracuseStep 2385875 = 3578813) B3578813
theorem B1239911 : Blo 550806 1239911 := bstep (se 1 (by rfl) ⟨929933, by rfl⟩ : syracuseStep 1239911 = 1859867) B1859867
theorem B3405467 : Blo 550806 3405467 := bstep (se 1 (by rfl) ⟨2554100, by rfl⟩ : syracuseStep 3405467 = 5108201) B5108201
theorem B3538687 : Blo 550806 3538687 := bstep (se 1 (by rfl) ⟨2654015, by rfl⟩ : syracuseStep 3538687 = 5308031) B5308031
theorem B6294185 : Blo 550806 6294185 := bstep (se 2 (by rfl) ⟨2360319, by rfl⟩ : syracuseStep 6294185 = 4720639) B4720639
theorem B6362333 : Blo 550806 6362333 := bstep (se 3 (by rfl) ⟨1192937, by rfl⟩ : syracuseStep 6362333 = 2385875) B2385875
theorem B15898943 : Blo 550806 15898943 := bstep (se 1 (by rfl) ⟨11924207, by rfl⟩ : syracuseStep 15898943 = 23848415) B23848415
theorem B826607 : Blo 550806 826607 := bstep (se 1 (by rfl) ⟨619955, by rfl⟩ : syracuseStep 826607 = 1239911) B1239911
theorem B2270311 : Blo 550806 2270311 := bstep (se 1 (by rfl) ⟨1702733, by rfl⟩ : syracuseStep 2270311 = 3405467) B3405467
theorem B830207 : Blo 550806 830207 := bstep (se 1 (by rfl) ⟨622655, by rfl⟩ : syracuseStep 830207 = 1245311) B1245311
theorem B91009271 : Blo 550806 91009271 := bstep (se 1 (by rfl) ⟨68256953, by rfl⟩ : syracuseStep 91009271 = 136513907) B136513907
theorem B12077981 : Blo 550806 12077981 := bstep (se 3 (by rfl) ⟨2264621, by rfl⟩ : syracuseStep 12077981 = 4529243) B4529243
theorem B4718249 : Blo 550806 4718249 := bstep (se 2 (by rfl) ⟨1769343, by rfl⟩ : syracuseStep 4718249 = 3538687) B3538687
theorem B4196123 : Blo 550806 4196123 := bstep (se 1 (by rfl) ⟨3147092, by rfl⟩ : syracuseStep 4196123 = 6294185) B6294185
theorem B4241555 : Blo 550806 4241555 := bstep (se 1 (by rfl) ⟨3181166, by rfl⟩ : syracuseStep 4241555 = 6362333) B6362333
theorem B10599295 : Blo 550806 10599295 := bstep (se 1 (by rfl) ⟨7949471, by rfl⟩ : syracuseStep 10599295 = 15898943) B15898943
theorem B12108325 : Blo 550806 12108325 := bstep (se 4 (by rfl) ⟨1135155, by rfl⟩ : syracuseStep 12108325 = 2270311) B2270311
theorem B60672847 : Blo 550806 60672847 := bstep (se 1 (by rfl) ⟨45504635, by rfl⟩ : syracuseStep 60672847 = 91009271) B91009271
theorem B8051987 : Blo 550806 8051987 := bstep (se 1 (by rfl) ⟨6038990, by rfl⟩ : syracuseStep 8051987 = 12077981) B12077981
theorem B551071 : Blo 550806 551071 := bstep (se 1 (by rfl) ⟨413303, by rfl⟩ : syracuseStep 551071 = 826607) B826607
theorem B553471 : Blo 550806 553471 := bstep (se 1 (by rfl) ⟨415103, by rfl⟩ : syracuseStep 553471 = 830207) B830207
theorem B3145499 : Blo 550806 3145499 := bstep (se 1 (by rfl) ⟨2359124, by rfl⟩ : syracuseStep 3145499 = 4718249) B4718249
theorem B14132393 : Blo 550806 14132393 := bstep (se 2 (by rfl) ⟨5299647, by rfl⟩ : syracuseStep 14132393 = 10599295) B10599295
theorem B2827703 : Blo 550806 2827703 := bstep (se 1 (by rfl) ⟨2120777, by rfl⟩ : syracuseStep 2827703 = 4241555) B4241555
theorem B2797415 : Blo 550806 2797415 := bstep (se 1 (by rfl) ⟨2098061, by rfl⟩ : syracuseStep 2797415 = 4196123) B4196123
theorem B16144433 : Blo 550806 16144433 := bstep (se 2 (by rfl) ⟨6054162, by rfl⟩ : syracuseStep 16144433 = 12108325) B12108325
theorem B80897129 : Blo 550806 80897129 := bstep (se 2 (by rfl) ⟨30336423, by rfl⟩ : syracuseStep 80897129 = 60672847) B60672847
theorem B5367991 : Blo 550806 5367991 := bstep (se 1 (by rfl) ⟨4025993, by rfl⟩ : syracuseStep 5367991 = 8051987) B8051987
theorem B2096999 : Blo 550806 2096999 := bstep (se 1 (by rfl) ⟨1572749, by rfl⟩ : syracuseStep 2096999 = 3145499) B3145499
theorem B7157321 : Blo 550806 7157321 := bstep (se 2 (by rfl) ⟨2683995, by rfl⟩ : syracuseStep 7157321 = 5367991) B5367991
theorem B10762955 : Blo 550806 10762955 := bstep (se 1 (by rfl) ⟨8072216, by rfl⟩ : syracuseStep 10762955 = 16144433) B16144433
theorem B9421595 : Blo 550806 9421595 := bstep (se 1 (by rfl) ⟨7066196, by rfl⟩ : syracuseStep 9421595 = 14132393) B14132393
theorem B1885135 : Blo 550806 1885135 := bstep (se 1 (by rfl) ⟨1413851, by rfl⟩ : syracuseStep 1885135 = 2827703) B2827703
theorem B1397999 : Blo 550806 1397999 := bstep (se 1 (by rfl) ⟨1048499, by rfl⟩ : syracuseStep 1397999 = 2096999) B2096999
theorem B53931419 : Blo 550806 53931419 := bstep (se 1 (by rfl) ⟨40448564, by rfl⟩ : syracuseStep 53931419 = 80897129) B80897129
theorem B1864943 : Blo 550806 1864943 := bstep (se 1 (by rfl) ⟨1398707, by rfl⟩ : syracuseStep 1864943 = 2797415) B2797415
theorem B35954279 : Blo 550806 35954279 := bstep (se 1 (by rfl) ⟨26965709, by rfl⟩ : syracuseStep 35954279 = 53931419) B53931419
theorem B931999 : Blo 550806 931999 := bstep (se 1 (by rfl) ⟨698999, by rfl⟩ : syracuseStep 931999 = 1397999) B1397999
theorem B4771547 : Blo 550806 4771547 := bstep (se 1 (by rfl) ⟨3578660, by rfl⟩ : syracuseStep 4771547 = 7157321) B7157321
theorem B6281063 : Blo 550806 6281063 := bstep (se 1 (by rfl) ⟨4710797, by rfl⟩ : syracuseStep 6281063 = 9421595) B9421595
theorem B2513513 : Blo 550806 2513513 := bstep (se 2 (by rfl) ⟨942567, by rfl⟩ : syracuseStep 2513513 = 1885135) B1885135
theorem B1243295 : Blo 550806 1243295 := bstep (se 1 (by rfl) ⟨932471, by rfl⟩ : syracuseStep 1243295 = 1864943) B1864943
theorem B7175303 : Blo 550806 7175303 := bstep (se 1 (by rfl) ⟨5381477, by rfl⟩ : syracuseStep 7175303 = 10762955) B10762955
theorem B3181031 : Blo 550806 3181031 := bstep (se 1 (by rfl) ⟨2385773, by rfl⟩ : syracuseStep 3181031 = 4771547) B4771547
theorem B1675675 : Blo 550806 1675675 := bstep (se 1 (by rfl) ⟨1256756, by rfl⟩ : syracuseStep 1675675 = 2513513) B2513513
theorem B828863 : Blo 550806 828863 := bstep (se 1 (by rfl) ⟨621647, by rfl⟩ : syracuseStep 828863 = 1243295) B1243295
theorem B23969519 : Blo 550806 23969519 := bstep (se 1 (by rfl) ⟨17977139, by rfl⟩ : syracuseStep 23969519 = 35954279) B35954279
theorem B4187375 : Blo 550806 4187375 := bstep (se 1 (by rfl) ⟨3140531, by rfl⟩ : syracuseStep 4187375 = 6281063) B6281063
theorem B1242665 : Blo 550806 1242665 := bstep (se 2 (by rfl) ⟨465999, by rfl⟩ : syracuseStep 1242665 = 931999) B931999
theorem B4783535 : Blo 550806 4783535 := bstep (se 1 (by rfl) ⟨3587651, by rfl⟩ : syracuseStep 4783535 = 7175303) B7175303
theorem B2234233 : Blo 550806 2234233 := bstep (se 2 (by rfl) ⟨837837, by rfl⟩ : syracuseStep 2234233 = 1675675) B1675675
theorem B2791583 : Blo 550806 2791583 := bstep (se 1 (by rfl) ⟨2093687, by rfl⟩ : syracuseStep 2791583 = 4187375) B4187375
theorem B828443 : Blo 550806 828443 := bstep (se 1 (by rfl) ⟨621332, by rfl⟩ : syracuseStep 828443 = 1242665) B1242665
theorem B3189023 : Blo 550806 3189023 := bstep (se 1 (by rfl) ⟨2391767, by rfl⟩ : syracuseStep 3189023 = 4783535) B4783535
theorem B15979679 : Blo 550806 15979679 := bstep (se 1 (by rfl) ⟨11984759, by rfl⟩ : syracuseStep 15979679 = 23969519) B23969519
theorem B2120687 : Blo 550806 2120687 := bstep (se 1 (by rfl) ⟨1590515, by rfl⟩ : syracuseStep 2120687 = 3181031) B3181031
theorem B552575 : Blo 550806 552575 := bstep (se 1 (by rfl) ⟨414431, by rfl⟩ : syracuseStep 552575 = 828863) B828863
theorem B10653119 : Blo 550806 10653119 := bstep (se 1 (by rfl) ⟨7989839, by rfl⟩ : syracuseStep 10653119 = 15979679) B15979679
theorem B1413791 : Blo 550806 1413791 := bstep (se 1 (by rfl) ⟨1060343, by rfl⟩ : syracuseStep 1413791 = 2120687) B2120687
theorem B1861055 : Blo 550806 1861055 := bstep (se 1 (by rfl) ⟨1395791, by rfl⟩ : syracuseStep 1861055 = 2791583) B2791583
theorem B552295 : Blo 550806 552295 := bstep (se 1 (by rfl) ⟨414221, by rfl⟩ : syracuseStep 552295 = 828443) B828443
theorem B2126015 : Blo 550806 2126015 := bstep (se 1 (by rfl) ⟨1594511, by rfl⟩ : syracuseStep 2126015 = 3189023) B3189023
theorem B2978977 : Blo 550806 2978977 := bstep (se 2 (by rfl) ⟨1117116, by rfl⟩ : syracuseStep 2978977 = 2234233) B2234233
theorem B3971969 : Blo 550806 3971969 := bstep (se 2 (by rfl) ⟨1489488, by rfl⟩ : syracuseStep 3971969 = 2978977) B2978977
theorem B1417343 : Blo 550806 1417343 := bstep (se 1 (by rfl) ⟨1063007, by rfl⟩ : syracuseStep 1417343 = 2126015) B2126015
theorem B7102079 : Blo 550806 7102079 := bstep (se 1 (by rfl) ⟨5326559, by rfl⟩ : syracuseStep 7102079 = 10653119) B10653119
theorem B942527 : Blo 550806 942527 := bstep (se 1 (by rfl) ⟨706895, by rfl⟩ : syracuseStep 942527 = 1413791) B1413791
theorem B1240703 : Blo 550806 1240703 := bstep (se 1 (by rfl) ⟨930527, by rfl⟩ : syracuseStep 1240703 = 1861055) B1861055
theorem B827135 : Blo 550806 827135 := bstep (se 1 (by rfl) ⟨620351, by rfl⟩ : syracuseStep 827135 = 1240703) B1240703
theorem B3779581 : Blo 550806 3779581 := bstep (se 3 (by rfl) ⟨708671, by rfl⟩ : syracuseStep 3779581 = 1417343) B1417343
theorem B4734719 : Blo 550806 4734719 := bstep (se 1 (by rfl) ⟨3551039, by rfl⟩ : syracuseStep 4734719 = 7102079) B7102079
theorem B2513405 : Blo 550806 2513405 := bstep (se 3 (by rfl) ⟨471263, by rfl⟩ : syracuseStep 2513405 = 942527) B942527
theorem B2647979 : Blo 550806 2647979 := bstep (se 1 (by rfl) ⟨1985984, by rfl⟩ : syracuseStep 2647979 = 3971969) B3971969
theorem B1675603 : Blo 550806 1675603 := bstep (se 1 (by rfl) ⟨1256702, by rfl⟩ : syracuseStep 1675603 = 2513405) B2513405
theorem B3156479 : Blo 550806 3156479 := bstep (se 1 (by rfl) ⟨2367359, by rfl⟩ : syracuseStep 3156479 = 4734719) B4734719
theorem B5039441 : Blo 550806 5039441 := bstep (se 2 (by rfl) ⟨1889790, by rfl⟩ : syracuseStep 5039441 = 3779581) B3779581
theorem B551423 : Blo 550806 551423 := bstep (se 1 (by rfl) ⟨413567, by rfl⟩ : syracuseStep 551423 = 827135) B827135
theorem B1765319 : Blo 550806 1765319 := bstep (se 1 (by rfl) ⟨1323989, by rfl⟩ : syracuseStep 1765319 = 2647979) B2647979
theorem B2234137 : Blo 550806 2234137 := bstep (se 2 (by rfl) ⟨837801, by rfl⟩ : syracuseStep 2234137 = 1675603) B1675603
theorem B2104319 : Blo 550806 2104319 := bstep (se 1 (by rfl) ⟨1578239, by rfl⟩ : syracuseStep 2104319 = 3156479) B3156479
theorem B3359627 : Blo 550806 3359627 := bstep (se 1 (by rfl) ⟨2519720, by rfl⟩ : syracuseStep 3359627 = 5039441) B5039441
theorem B4707517 : Blo 550806 4707517 := bstep (se 3 (by rfl) ⟨882659, by rfl⟩ : syracuseStep 4707517 = 1765319) B1765319
theorem B2239751 : Blo 550806 2239751 := bstep (se 1 (by rfl) ⟨1679813, by rfl⟩ : syracuseStep 2239751 = 3359627) B3359627
theorem B6276689 : Blo 550806 6276689 := bstep (se 2 (by rfl) ⟨2353758, by rfl⟩ : syracuseStep 6276689 = 4707517) B4707517
theorem B1402879 : Blo 550806 1402879 := bstep (se 1 (by rfl) ⟨1052159, by rfl⟩ : syracuseStep 1402879 = 2104319) B2104319
theorem B2978849 : Blo 550806 2978849 := bstep (se 2 (by rfl) ⟨1117068, by rfl⟩ : syracuseStep 2978849 = 2234137) B2234137
theorem B1870505 : Blo 550806 1870505 := bstep (se 2 (by rfl) ⟨701439, by rfl⟩ : syracuseStep 1870505 = 1402879) B1402879
theorem B1493167 : Blo 550806 1493167 := bstep (se 1 (by rfl) ⟨1119875, by rfl⟩ : syracuseStep 1493167 = 2239751) B2239751
theorem B1985899 : Blo 550806 1985899 := bstep (se 1 (by rfl) ⟨1489424, by rfl⟩ : syracuseStep 1985899 = 2978849) B2978849
theorem B4184459 : Blo 550806 4184459 := bstep (se 1 (by rfl) ⟨3138344, by rfl⟩ : syracuseStep 4184459 = 6276689) B6276689
theorem B1247003 : Blo 550806 1247003 := bstep (se 1 (by rfl) ⟨935252, by rfl⟩ : syracuseStep 1247003 = 1870505) B1870505
theorem B2789639 : Blo 550806 2789639 := bstep (se 1 (by rfl) ⟨2092229, by rfl⟩ : syracuseStep 2789639 = 4184459) B4184459
theorem B1990889 : Blo 550806 1990889 := bstep (se 2 (by rfl) ⟨746583, by rfl⟩ : syracuseStep 1990889 = 1493167) B1493167
theorem B2647865 : Blo 550806 2647865 := bstep (se 2 (by rfl) ⟨992949, by rfl⟩ : syracuseStep 2647865 = 1985899) B1985899
theorem B831335 : Blo 550806 831335 := bstep (se 1 (by rfl) ⟨623501, by rfl⟩ : syracuseStep 831335 = 1247003) B1247003
theorem B1327259 : Blo 550806 1327259 := bstep (se 1 (by rfl) ⟨995444, by rfl⟩ : syracuseStep 1327259 = 1990889) B1990889
theorem B1859759 : Blo 550806 1859759 := bstep (se 1 (by rfl) ⟨1394819, by rfl⟩ : syracuseStep 1859759 = 2789639) B2789639
theorem B1765243 : Blo 550806 1765243 := bstep (se 1 (by rfl) ⟨1323932, by rfl⟩ : syracuseStep 1765243 = 2647865) B2647865
theorem B884839 : Blo 550806 884839 := bstep (se 1 (by rfl) ⟨663629, by rfl⟩ : syracuseStep 884839 = 1327259) B1327259
theorem B2353657 : Blo 550806 2353657 := bstep (se 2 (by rfl) ⟨882621, by rfl⟩ : syracuseStep 2353657 = 1765243) B1765243
theorem B1239839 : Blo 550806 1239839 := bstep (se 1 (by rfl) ⟨929879, by rfl⟩ : syracuseStep 1239839 = 1859759) B1859759
theorem B554223 : Blo 550806 554223 := bstep (se 1 (by rfl) ⟨415667, by rfl⟩ : syracuseStep 554223 = 831335) B831335
theorem B1179785 : Blo 550806 1179785 := bstep (se 2 (by rfl) ⟨442419, by rfl⟩ : syracuseStep 1179785 = 884839) B884839
theorem B826559 : Blo 550806 826559 := bstep (se 1 (by rfl) ⟨619919, by rfl⟩ : syracuseStep 826559 = 1239839) B1239839
theorem B3138209 : Blo 550806 3138209 := bstep (se 2 (by rfl) ⟨1176828, by rfl⟩ : syracuseStep 3138209 = 2353657) B2353657
theorem B786523 : Blo 550806 786523 := bstep (se 1 (by rfl) ⟨589892, by rfl⟩ : syracuseStep 786523 = 1179785) B1179785
theorem B551039 : Blo 550806 551039 := bstep (se 1 (by rfl) ⟨413279, by rfl⟩ : syracuseStep 551039 = 826559) B826559
theorem B2092139 : Blo 550806 2092139 := bstep (se 1 (by rfl) ⟨1569104, by rfl⟩ : syracuseStep 2092139 = 3138209) B3138209
theorem B1048697 : Blo 550806 1048697 := bstep (se 2 (by rfl) ⟨393261, by rfl⟩ : syracuseStep 1048697 = 786523) B786523
theorem B1394759 : Blo 550806 1394759 := bstep (se 1 (by rfl) ⟨1046069, by rfl⟩ : syracuseStep 1394759 = 2092139) B2092139
theorem B699131 : Blo 550806 699131 := bstep (se 1 (by rfl) ⟨524348, by rfl⟩ : syracuseStep 699131 = 1048697) B1048697
theorem B929839 : Blo 550806 929839 := bstep (se 1 (by rfl) ⟨697379, by rfl⟩ : syracuseStep 929839 = 1394759) B1394759
theorem B1239785 : Blo 550806 1239785 := bstep (se 2 (by rfl) ⟨464919, by rfl⟩ : syracuseStep 1239785 = 929839) B929839
theorem B1864349 : Blo 550806 1864349 := bstep (se 3 (by rfl) ⟨349565, by rfl⟩ : syracuseStep 1864349 = 699131) B699131
theorem B826523 : Blo 550806 826523 := bstep (se 1 (by rfl) ⟨619892, by rfl⟩ : syracuseStep 826523 = 1239785) B1239785
theorem B1242899 : Blo 550806 1242899 := bstep (se 1 (by rfl) ⟨932174, by rfl⟩ : syracuseStep 1242899 = 1864349) B1864349
theorem B828599 : Blo 550806 828599 := bstep (se 1 (by rfl) ⟨621449, by rfl⟩ : syracuseStep 828599 = 1242899) B1242899
theorem B551015 : Blo 550806 551015 := bstep (se 1 (by rfl) ⟨413261, by rfl⟩ : syracuseStep 551015 = 826523) B826523
theorem B552399 : Blo 550806 552399 := bstep (se 1 (by rfl) ⟨414299, by rfl⟩ : syracuseStep 552399 = 828599) B828599

theorem C0 (j : ℕ) (h1 : 137701 ≤ j) (h2 : j ≤ 138400) : Blo 550806 (4 * j + 3) := by
  interval_cases j
  · exact B550807
  · exact B550811
  · exact B550815
  · exact B550819
  · exact B550823
  · exact B550827
  · exact B550831
  · exact B550835
  · exact B550839
  · exact B550843
  · exact B550847
  · exact B550851
  · exact B550855
  · exact B550859
  · exact B550863
  · exact B550867
  · exact B550871
  · exact B550875
  · exact B550879
  · exact B550883
  · exact B550887
  · exact B550891
  · exact B550895
  · exact B550899
  · exact B550903
  · exact B550907
  · exact B550911
  · exact B550915
  · exact B550919
  · exact B550923
  · exact B550927
  · exact B550931
  · exact B550935
  · exact B550939
  · exact B550943
  · exact B550947
  · exact B550951
  · exact B550955
  · exact B550959
  · exact B550963
  · exact B550967
  · exact B550971
  · exact B550975
  · exact B550979
  · exact B550983
  · exact B550987
  · exact B550991
  · exact B550995
  · exact B550999
  · exact B551003
  · exact B551007
  · exact B551011
  · exact B551015
  · exact B551019
  · exact B551023
  · exact B551027
  · exact B551031
  · exact B551035
  · exact B551039
  · exact B551043
  · exact B551047
  · exact B551051
  · exact B551055
  · exact B551059
  · exact B551063
  · exact B551067
  · exact B551071
  · exact B551075
  · exact B551079
  · exact B551083
  · exact B551087
  · exact B551091
  · exact B551095
  · exact B551099
  · exact B551103
  · exact B551107
  · exact B551111
  · exact B551115
  · exact B551119
  · exact B551123
  · exact B551127
  · exact B551131
  · exact B551135
  · exact B551139
  · exact B551143
  · exact B551147
  · exact B551151
  · exact B551155
  · exact B551159
  · exact B551163
  · exact B551167
  · exact B551171
  · exact B551175
  · exact B551179
  · exact B551183
  · exact B551187
  · exact B551191
  · exact B551195
  · exact B551199
  · exact B551203
  · exact B551207
  · exact B551211
  · exact B551215
  · exact B551219
  · exact B551223
  · exact B551227
  · exact B551231
  · exact B551235
  · exact B551239
  · exact B551243
  · exact B551247
  · exact B551251
  · exact B551255
  · exact B551259
  · exact B551263
  · exact B551267
  · exact B551271
  · exact B551275
  · exact B551279
  · exact B551283
  · exact B551287
  · exact B551291
  · exact B551295
  · exact B551299
  · exact B551303
  · exact B551307
  · exact B551311
  · exact B551315
  · exact B551319
  · exact B551323
  · exact B551327
  · exact B551331
  · exact B551335
  · exact B551339
  · exact B551343
  · exact B551347
  · exact B551351
  · exact B551355
  · exact B551359
  · exact B551363
  · exact B551367
  · exact B551371
  · exact B551375
  · exact B551379
  · exact B551383
  · exact B551387
  · exact B551391
  · exact B551395
  · exact B551399
  · exact B551403
  · exact B551407
  · exact B551411
  · exact B551415
  · exact B551419
  · exact B551423
  · exact B551427
  · exact B551431
  · exact B551435
  · exact B551439
  · exact B551443
  · exact B551447
  · exact B551451
  · exact B551455
  · exact B551459
  · exact B551463
  · exact B551467
  · exact B551471
  · exact B551475
  · exact B551479
  · exact B551483
  · exact B551487
  · exact B551491
  · exact B551495
  · exact B551499
  · exact B551503
  · exact B551507
  · exact B551511
  · exact B551515
  · exact B551519
  · exact B551523
  · exact B551527
  · exact B551531
  · exact B551535
  · exact B551539
  · exact B551543
  · exact B551547
  · exact B551551
  · exact B551555
  · exact B551559
  · exact B551563
  · exact B551567
  · exact B551571
  · exact B551575
  · exact B551579
  · exact B551583
  · exact B551587
  · exact B551591
  · exact B551595
  · exact B551599
  · exact B551603
  · exact B551607
  · exact B551611
  · exact B551615
  · exact B551619
  · exact B551623
  · exact B551627
  · exact B551631
  · exact B551635
  · exact B551639
  · exact B551643
  · exact B551647
  · exact B551651
  · exact B551655
  · exact B551659
  · exact B551663
  · exact B551667
  · exact B551671
  · exact B551675
  · exact B551679
  · exact B551683
  · exact B551687
  · exact B551691
  · exact B551695
  · exact B551699
  · exact B551703
  · exact B551707
  · exact B551711
  · exact B551715
  · exact B551719
  · exact B551723
  · exact B551727
  · exact B551731
  · exact B551735
  · exact B551739
  · exact B551743
  · exact B551747
  · exact B551751
  · exact B551755
  · exact B551759
  · exact B551763
  · exact B551767
  · exact B551771
  · exact B551775
  · exact B551779
  · exact B551783
  · exact B551787
  · exact B551791
  · exact B551795
  · exact B551799
  · exact B551803
  · exact B551807
  · exact B551811
  · exact B551815
  · exact B551819
  · exact B551823
  · exact B551827
  · exact B551831
  · exact B551835
  · exact B551839
  · exact B551843
  · exact B551847
  · exact B551851
  · exact B551855
  · exact B551859
  · exact B551863
  · exact B551867
  · exact B551871
  · exact B551875
  · exact B551879
  · exact B551883
  · exact B551887
  · exact B551891
  · exact B551895
  · exact B551899
  · exact B551903
  · exact B551907
  · exact B551911
  · exact B551915
  · exact B551919
  · exact B551923
  · exact B551927
  · exact B551931
  · exact B551935
  · exact B551939
  · exact B551943
  · exact B551947
  · exact B551951
  · exact B551955
  · exact B551959
  · exact B551963
  · exact B551967
  · exact B551971
  · exact B551975
  · exact B551979
  · exact B551983
  · exact B551987
  · exact B551991
  · exact B551995
  · exact B551999
  · exact B552003
  · exact B552007
  · exact B552011
  · exact B552015
  · exact B552019
  · exact B552023
  · exact B552027
  · exact B552031
  · exact B552035
  · exact B552039
  · exact B552043
  · exact B552047
  · exact B552051
  · exact B552055
  · exact B552059
  · exact B552063
  · exact B552067
  · exact B552071
  · exact B552075
  · exact B552079
  · exact B552083
  · exact B552087
  · exact B552091
  · exact B552095
  · exact B552099
  · exact B552103
  · exact B552107
  · exact B552111
  · exact B552115
  · exact B552119
  · exact B552123
  · exact B552127
  · exact B552131
  · exact B552135
  · exact B552139
  · exact B552143
  · exact B552147
  · exact B552151
  · exact B552155
  · exact B552159
  · exact B552163
  · exact B552167
  · exact B552171
  · exact B552175
  · exact B552179
  · exact B552183
  · exact B552187
  · exact B552191
  · exact B552195
  · exact B552199
  · exact B552203
  · exact B552207
  · exact B552211
  · exact B552215
  · exact B552219
  · exact B552223
  · exact B552227
  · exact B552231
  · exact B552235
  · exact B552239
  · exact B552243
  · exact B552247
  · exact B552251
  · exact B552255
  · exact B552259
  · exact B552263
  · exact B552267
  · exact B552271
  · exact B552275
  · exact B552279
  · exact B552283
  · exact B552287
  · exact B552291
  · exact B552295
  · exact B552299
  · exact B552303
  · exact B552307
  · exact B552311
  · exact B552315
  · exact B552319
  · exact B552323
  · exact B552327
  · exact B552331
  · exact B552335
  · exact B552339
  · exact B552343
  · exact B552347
  · exact B552351
  · exact B552355
  · exact B552359
  · exact B552363
  · exact B552367
  · exact B552371
  · exact B552375
  · exact B552379
  · exact B552383
  · exact B552387
  · exact B552391
  · exact B552395
  · exact B552399
  · exact B552403
  · exact B552407
  · exact B552411
  · exact B552415
  · exact B552419
  · exact B552423
  · exact B552427
  · exact B552431
  · exact B552435
  · exact B552439
  · exact B552443
  · exact B552447
  · exact B552451
  · exact B552455
  · exact B552459
  · exact B552463
  · exact B552467
  · exact B552471
  · exact B552475
  · exact B552479
  · exact B552483
  · exact B552487
  · exact B552491
  · exact B552495
  · exact B552499
  · exact B552503
  · exact B552507
  · exact B552511
  · exact B552515
  · exact B552519
  · exact B552523
  · exact B552527
  · exact B552531
  · exact B552535
  · exact B552539
  · exact B552543
  · exact B552547
  · exact B552551
  · exact B552555
  · exact B552559
  · exact B552563
  · exact B552567
  · exact B552571
  · exact B552575
  · exact B552579
  · exact B552583
  · exact B552587
  · exact B552591
  · exact B552595
  · exact B552599
  · exact B552603
  · exact B552607
  · exact B552611
  · exact B552615
  · exact B552619
  · exact B552623
  · exact B552627
  · exact B552631
  · exact B552635
  · exact B552639
  · exact B552643
  · exact B552647
  · exact B552651
  · exact B552655
  · exact B552659
  · exact B552663
  · exact B552667
  · exact B552671
  · exact B552675
  · exact B552679
  · exact B552683
  · exact B552687
  · exact B552691
  · exact B552695
  · exact B552699
  · exact B552703
  · exact B552707
  · exact B552711
  · exact B552715
  · exact B552719
  · exact B552723
  · exact B552727
  · exact B552731
  · exact B552735
  · exact B552739
  · exact B552743
  · exact B552747
  · exact B552751
  · exact B552755
  · exact B552759
  · exact B552763
  · exact B552767
  · exact B552771
  · exact B552775
  · exact B552779
  · exact B552783
  · exact B552787
  · exact B552791
  · exact B552795
  · exact B552799
  · exact B552803
  · exact B552807
  · exact B552811
  · exact B552815
  · exact B552819
  · exact B552823
  · exact B552827
  · exact B552831
  · exact B552835
  · exact B552839
  · exact B552843
  · exact B552847
  · exact B552851
  · exact B552855
  · exact B552859
  · exact B552863
  · exact B552867
  · exact B552871
  · exact B552875
  · exact B552879
  · exact B552883
  · exact B552887
  · exact B552891
  · exact B552895
  · exact B552899
  · exact B552903
  · exact B552907
  · exact B552911
  · exact B552915
  · exact B552919
  · exact B552923
  · exact B552927
  · exact B552931
  · exact B552935
  · exact B552939
  · exact B552943
  · exact B552947
  · exact B552951
  · exact B552955
  · exact B552959
  · exact B552963
  · exact B552967
  · exact B552971
  · exact B552975
  · exact B552979
  · exact B552983
  · exact B552987
  · exact B552991
  · exact B552995
  · exact B552999
  · exact B553003
  · exact B553007
  · exact B553011
  · exact B553015
  · exact B553019
  · exact B553023
  · exact B553027
  · exact B553031
  · exact B553035
  · exact B553039
  · exact B553043
  · exact B553047
  · exact B553051
  · exact B553055
  · exact B553059
  · exact B553063
  · exact B553067
  · exact B553071
  · exact B553075
  · exact B553079
  · exact B553083
  · exact B553087
  · exact B553091
  · exact B553095
  · exact B553099
  · exact B553103
  · exact B553107
  · exact B553111
  · exact B553115
  · exact B553119
  · exact B553123
  · exact B553127
  · exact B553131
  · exact B553135
  · exact B553139
  · exact B553143
  · exact B553147
  · exact B553151
  · exact B553155
  · exact B553159
  · exact B553163
  · exact B553167
  · exact B553171
  · exact B553175
  · exact B553179
  · exact B553183
  · exact B553187
  · exact B553191
  · exact B553195
  · exact B553199
  · exact B553203
  · exact B553207
  · exact B553211
  · exact B553215
  · exact B553219
  · exact B553223
  · exact B553227
  · exact B553231
  · exact B553235
  · exact B553239
  · exact B553243
  · exact B553247
  · exact B553251
  · exact B553255
  · exact B553259
  · exact B553263
  · exact B553267
  · exact B553271
  · exact B553275
  · exact B553279
  · exact B553283
  · exact B553287
  · exact B553291
  · exact B553295
  · exact B553299
  · exact B553303
  · exact B553307
  · exact B553311
  · exact B553315
  · exact B553319
  · exact B553323
  · exact B553327
  · exact B553331
  · exact B553335
  · exact B553339
  · exact B553343
  · exact B553347
  · exact B553351
  · exact B553355
  · exact B553359
  · exact B553363
  · exact B553367
  · exact B553371
  · exact B553375
  · exact B553379
  · exact B553383
  · exact B553387
  · exact B553391
  · exact B553395
  · exact B553399
  · exact B553403
  · exact B553407
  · exact B553411
  · exact B553415
  · exact B553419
  · exact B553423
  · exact B553427
  · exact B553431
  · exact B553435
  · exact B553439
  · exact B553443
  · exact B553447
  · exact B553451
  · exact B553455
  · exact B553459
  · exact B553463
  · exact B553467
  · exact B553471
  · exact B553475
  · exact B553479
  · exact B553483
  · exact B553487
  · exact B553491
  · exact B553495
  · exact B553499
  · exact B553503
  · exact B553507
  · exact B553511
  · exact B553515
  · exact B553519
  · exact B553523
  · exact B553527
  · exact B553531
  · exact B553535
  · exact B553539
  · exact B553543
  · exact B553547
  · exact B553551
  · exact B553555
  · exact B553559
  · exact B553563
  · exact B553567
  · exact B553571
  · exact B553575
  · exact B553579
  · exact B553583
  · exact B553587
  · exact B553591
  · exact B553595
  · exact B553599
  · exact B553603

theorem C1 (j : ℕ) (h1 : 138401 ≤ j) (h2 : j ≤ 138700) : Blo 550806 (4 * j + 3) := by
  interval_cases j
  · exact B553607
  · exact B553611
  · exact B553615
  · exact B553619
  · exact B553623
  · exact B553627
  · exact B553631
  · exact B553635
  · exact B553639
  · exact B553643
  · exact B553647
  · exact B553651
  · exact B553655
  · exact B553659
  · exact B553663
  · exact B553667
  · exact B553671
  · exact B553675
  · exact B553679
  · exact B553683
  · exact B553687
  · exact B553691
  · exact B553695
  · exact B553699
  · exact B553703
  · exact B553707
  · exact B553711
  · exact B553715
  · exact B553719
  · exact B553723
  · exact B553727
  · exact B553731
  · exact B553735
  · exact B553739
  · exact B553743
  · exact B553747
  · exact B553751
  · exact B553755
  · exact B553759
  · exact B553763
  · exact B553767
  · exact B553771
  · exact B553775
  · exact B553779
  · exact B553783
  · exact B553787
  · exact B553791
  · exact B553795
  · exact B553799
  · exact B553803
  · exact B553807
  · exact B553811
  · exact B553815
  · exact B553819
  · exact B553823
  · exact B553827
  · exact B553831
  · exact B553835
  · exact B553839
  · exact B553843
  · exact B553847
  · exact B553851
  · exact B553855
  · exact B553859
  · exact B553863
  · exact B553867
  · exact B553871
  · exact B553875
  · exact B553879
  · exact B553883
  · exact B553887
  · exact B553891
  · exact B553895
  · exact B553899
  · exact B553903
  · exact B553907
  · exact B553911
  · exact B553915
  · exact B553919
  · exact B553923
  · exact B553927
  · exact B553931
  · exact B553935
  · exact B553939
  · exact B553943
  · exact B553947
  · exact B553951
  · exact B553955
  · exact B553959
  · exact B553963
  · exact B553967
  · exact B553971
  · exact B553975
  · exact B553979
  · exact B553983
  · exact B553987
  · exact B553991
  · exact B553995
  · exact B553999
  · exact B554003
  · exact B554007
  · exact B554011
  · exact B554015
  · exact B554019
  · exact B554023
  · exact B554027
  · exact B554031
  · exact B554035
  · exact B554039
  · exact B554043
  · exact B554047
  · exact B554051
  · exact B554055
  · exact B554059
  · exact B554063
  · exact B554067
  · exact B554071
  · exact B554075
  · exact B554079
  · exact B554083
  · exact B554087
  · exact B554091
  · exact B554095
  · exact B554099
  · exact B554103
  · exact B554107
  · exact B554111
  · exact B554115
  · exact B554119
  · exact B554123
  · exact B554127
  · exact B554131
  · exact B554135
  · exact B554139
  · exact B554143
  · exact B554147
  · exact B554151
  · exact B554155
  · exact B554159
  · exact B554163
  · exact B554167
  · exact B554171
  · exact B554175
  · exact B554179
  · exact B554183
  · exact B554187
  · exact B554191
  · exact B554195
  · exact B554199
  · exact B554203
  · exact B554207
  · exact B554211
  · exact B554215
  · exact B554219
  · exact B554223
  · exact B554227
  · exact B554231
  · exact B554235
  · exact B554239
  · exact B554243
  · exact B554247
  · exact B554251
  · exact B554255
  · exact B554259
  · exact B554263
  · exact B554267
  · exact B554271
  · exact B554275
  · exact B554279
  · exact B554283
  · exact B554287
  · exact B554291
  · exact B554295
  · exact B554299
  · exact B554303
  · exact B554307
  · exact B554311
  · exact B554315
  · exact B554319
  · exact B554323
  · exact B554327
  · exact B554331
  · exact B554335
  · exact B554339
  · exact B554343
  · exact B554347
  · exact B554351
  · exact B554355
  · exact B554359
  · exact B554363
  · exact B554367
  · exact B554371
  · exact B554375
  · exact B554379
  · exact B554383
  · exact B554387
  · exact B554391
  · exact B554395
  · exact B554399
  · exact B554403
  · exact B554407
  · exact B554411
  · exact B554415
  · exact B554419
  · exact B554423
  · exact B554427
  · exact B554431
  · exact B554435
  · exact B554439
  · exact B554443
  · exact B554447
  · exact B554451
  · exact B554455
  · exact B554459
  · exact B554463
  · exact B554467
  · exact B554471
  · exact B554475
  · exact B554479
  · exact B554483
  · exact B554487
  · exact B554491
  · exact B554495
  · exact B554499
  · exact B554503
  · exact B554507
  · exact B554511
  · exact B554515
  · exact B554519
  · exact B554523
  · exact B554527
  · exact B554531
  · exact B554535
  · exact B554539
  · exact B554543
  · exact B554547
  · exact B554551
  · exact B554555
  · exact B554559
  · exact B554563
  · exact B554567
  · exact B554571
  · exact B554575
  · exact B554579
  · exact B554583
  · exact B554587
  · exact B554591
  · exact B554595
  · exact B554599
  · exact B554603
  · exact B554607
  · exact B554611
  · exact B554615
  · exact B554619
  · exact B554623
  · exact B554627
  · exact B554631
  · exact B554635
  · exact B554639
  · exact B554643
  · exact B554647
  · exact B554651
  · exact B554655
  · exact B554659
  · exact B554663
  · exact B554667
  · exact B554671
  · exact B554675
  · exact B554679
  · exact B554683
  · exact B554687
  · exact B554691
  · exact B554695
  · exact B554699
  · exact B554703
  · exact B554707
  · exact B554711
  · exact B554715
  · exact B554719
  · exact B554723
  · exact B554727
  · exact B554731
  · exact B554735
  · exact B554739
  · exact B554743
  · exact B554747
  · exact B554751
  · exact B554755
  · exact B554759
  · exact B554763
  · exact B554767
  · exact B554771
  · exact B554775
  · exact B554779
  · exact B554783
  · exact B554787
  · exact B554791
  · exact B554795
  · exact B554799
  · exact B554803

theorem solution (m : ℕ) (hlo : 550806 ≤ m) (hhi : m ≤ 554806) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 137701 ≤ j := by omega
    have hj2 : j ≤ 138700 := by omega
    have hb : Blo 550806 (4 * j + 3) := by
      rcases Nat.lt_or_ge j 138401 with hc0 | hc0
      · exact C0 j (by omega) (by omega)
      exact C1 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
