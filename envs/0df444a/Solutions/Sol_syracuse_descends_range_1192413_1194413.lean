-- Prove2me | solution 1 for syracuse_descends_range_1192413_1194413
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-09T22:10:40.735656+00:00
-- url     : https://prove2.me/submissions/86bb22c5-7b42-4273-830a-48df8e0a85ec

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


theorem B5734405 : Blo 1192413 5734405 := bbase (se 4 (by rfl) ⟨537600, by rfl⟩ : syracuseStep 5734405 = 1075201) (by norm_num)
theorem B1343497 : Blo 1192413 1343497 := bbase (se 2 (by rfl) ⟨503811, by rfl⟩ : syracuseStep 1343497 = 1007623) (by norm_num)
theorem B2687021 : Blo 1192413 2687021 := bbase (se 3 (by rfl) ⟨503816, by rfl⟩ : syracuseStep 2687021 = 1007633) (by norm_num)
theorem B1343533 : Blo 1192413 1343533 := bbase (se 3 (by rfl) ⟨251912, by rfl⟩ : syracuseStep 1343533 = 503825) (by norm_num)
theorem B3227701 : Blo 1192413 3227701 := bbase (se 5 (by rfl) ⟨151298, by rfl⟩ : syracuseStep 3227701 = 302597) (by norm_num)
theorem B2015293 : Blo 1192413 2015293 := bbase (se 3 (by rfl) ⟨377867, by rfl⟩ : syracuseStep 2015293 = 755735) (by norm_num)
theorem B1343569 : Blo 1192413 1343569 := bbase (se 2 (by rfl) ⟨503838, by rfl⟩ : syracuseStep 1343569 = 1007677) (by norm_num)
theorem B2547821 : Blo 1192413 2547821 := bbase (se 3 (by rfl) ⟨477716, by rfl⟩ : syracuseStep 2547821 = 955433) (by norm_num)
theorem B2687093 : Blo 1192413 2687093 := bbase (se 5 (by rfl) ⟨125957, by rfl⟩ : syracuseStep 2687093 = 251915) (by norm_num)
theorem B1343605 : Blo 1192413 1343605 := bbase (se 5 (by rfl) ⟨62981, by rfl⟩ : syracuseStep 1343605 = 125963) (by norm_num)
theorem B4030613 : Blo 1192413 4030613 := bbase (se 6 (by rfl) ⟨94467, by rfl⟩ : syracuseStep 4030613 = 188935) (by norm_num)
theorem B2015381 : Blo 1192413 2015381 := bbase (se 6 (by rfl) ⟨47235, by rfl⟩ : syracuseStep 2015381 = 94471) (by norm_num)
theorem B1343641 : Blo 1192413 1343641 := bbase (se 2 (by rfl) ⟨503865, by rfl⟩ : syracuseStep 1343641 = 1007731) (by norm_num)
theorem B3023021 : Blo 1192413 3023021 := bbase (se 3 (by rfl) ⟨566816, by rfl⟩ : syracuseStep 3023021 = 1133633) (by norm_num)
theorem B2687165 : Blo 1192413 2687165 := bbase (se 3 (by rfl) ⟨503843, by rfl⟩ : syracuseStep 2687165 = 1007687) (by norm_num)
theorem B1343677 : Blo 1192413 1343677 := bbase (se 3 (by rfl) ⟨251939, by rfl⟩ : syracuseStep 1343677 = 503879) (by norm_num)
theorem B1343713 : Blo 1192413 1343713 := bbase (se 2 (by rfl) ⟨503892, by rfl⟩ : syracuseStep 1343713 = 1007785) (by norm_num)
theorem B2687237 : Blo 1192413 2687237 := bbase (se 4 (by rfl) ⟨251928, by rfl⟩ : syracuseStep 2687237 = 503857) (by norm_num)
theorem B2015509 : Blo 1192413 2015509 := bbase (se 6 (by rfl) ⟨47238, by rfl⟩ : syracuseStep 2015509 = 94477) (by norm_num)
theorem B1433909 : Blo 1192413 1433909 := bbase (se 5 (by rfl) ⟨67214, by rfl⟩ : syracuseStep 1433909 = 134429) (by norm_num)
theorem B2687309 : Blo 1192413 2687309 := bbase (se 3 (by rfl) ⟨503870, by rfl⟩ : syracuseStep 2687309 = 1007741) (by norm_num)
theorem B3228005 : Blo 1192413 3228005 := bbase (se 4 (by rfl) ⟨302625, by rfl⟩ : syracuseStep 3228005 = 605251) (by norm_num)
theorem B4358549 : Blo 1192413 4358549 := bbase (se 6 (by rfl) ⟨102153, by rfl⟩ : syracuseStep 4358549 = 204307) (by norm_num)
theorem B2687381 : Blo 1192413 2687381 := bbase (se 6 (by rfl) ⟨62985, by rfl⟩ : syracuseStep 2687381 = 125971) (by norm_num)
theorem B4530613 : Blo 1192413 4530613 := bbase (se 5 (by rfl) ⟨212372, by rfl⟩ : syracuseStep 4530613 = 424745) (by norm_num)
theorem B4301237 : Blo 1192413 4301237 := bbase (se 5 (by rfl) ⟨201620, by rfl⟩ : syracuseStep 4301237 = 403241) (by norm_num)
theorem B2867645 : Blo 1192413 2867645 := bbase (se 3 (by rfl) ⟨537683, by rfl⟩ : syracuseStep 2867645 = 1075367) (by norm_num)
theorem B5439941 : Blo 1192413 5439941 := bbase (se 4 (by rfl) ⟨509994, by rfl⟩ : syracuseStep 5439941 = 1019989) (by norm_num)
theorem B2548189 : Blo 1192413 2548189 := bbase (se 3 (by rfl) ⟨477785, by rfl⟩ : syracuseStep 2548189 = 955571) (by norm_num)
theorem B3875381 : Blo 1192413 3875381 := bbase (se 5 (by rfl) ⟨181658, by rfl⟩ : syracuseStep 3875381 = 363317) (by norm_num)
theorem B4031045 : Blo 1192413 4031045 := bbase (se 4 (by rfl) ⟨377910, by rfl⟩ : syracuseStep 4031045 = 755821) (by norm_num)
theorem B10887797 : Blo 1192413 10887797 := bbase (se 5 (by rfl) ⟨510365, by rfl⟩ : syracuseStep 10887797 = 1020731) (by norm_num)
theorem B6128245 : Blo 1192413 6128245 := bbase (se 5 (by rfl) ⟨287261, by rfl⟩ : syracuseStep 6128245 = 574523) (by norm_num)
theorem B6046325 : Blo 1192413 6046325 := bbase (se 5 (by rfl) ⟨283421, by rfl⟩ : syracuseStep 6046325 = 566843) (by norm_num)
theorem B1434245 : Blo 1192413 1434245 := bbase (se 4 (by rfl) ⟨134460, by rfl⟩ : syracuseStep 1434245 = 268921) (by norm_num)
theorem B6800021 : Blo 1192413 6800021 := bbase (se 6 (by rfl) ⟨159375, by rfl⟩ : syracuseStep 6800021 = 318751) (by norm_num)
theorem B4301525 : Blo 1192413 4301525 := bbase (se 7 (by rfl) ⟨50408, by rfl⟩ : syracuseStep 4301525 = 100817) (by norm_num)
theorem B4530917 : Blo 1192413 4530917 := bbase (se 4 (by rfl) ⟨424773, by rfl⟩ : syracuseStep 4530917 = 849547) (by norm_num)
theorem B1434361 : Blo 1192413 1434361 := bbase (se 2 (by rfl) ⟨537885, by rfl⟩ : syracuseStep 1434361 = 1075771) (by norm_num)
theorem B6791957 : Blo 1192413 6791957 := bbase (se 6 (by rfl) ⟨159186, by rfl⟩ : syracuseStep 6791957 = 318373) (by norm_num)
theorem B5817109 : Blo 1192413 5817109 := bbase (se 6 (by rfl) ⟨136338, by rfl⟩ : syracuseStep 5817109 = 272677) (by norm_num)
theorem B3228437 : Blo 1192413 3228437 := bbase (se 6 (by rfl) ⟨75666, by rfl⟩ : syracuseStep 3228437 = 151333) (by norm_num)
theorem B3400501 : Blo 1192413 3400501 := bbase (se 5 (by rfl) ⟨159398, by rfl⟩ : syracuseStep 3400501 = 318797) (by norm_num)
theorem B2868029 : Blo 1192413 2868029 := bbase (se 3 (by rfl) ⟨537755, by rfl⟩ : syracuseStep 2868029 = 1075511) (by norm_num)
theorem B1434433 : Blo 1192413 1434433 := bbase (se 2 (by rfl) ⟨537912, by rfl⟩ : syracuseStep 1434433 = 1075825) (by norm_num)
theorem B1434457 : Blo 1192413 1434457 := bbase (se 2 (by rfl) ⟨537921, by rfl⟩ : syracuseStep 1434457 = 1075843) (by norm_num)
theorem B2417501 : Blo 1192413 2417501 := bbase (se 3 (by rfl) ⟨453281, by rfl⟩ : syracuseStep 2417501 = 906563) (by norm_num)
theorem B1434601 : Blo 1192413 1434601 := bbase (se 2 (by rfl) ⟨537975, by rfl⟩ : syracuseStep 1434601 = 1075951) (by norm_num)
theorem B6038549 : Blo 1192413 6038549 := bbase (se 6 (by rfl) ⟨141528, by rfl⟩ : syracuseStep 6038549 = 283057) (by norm_num)
theorem B2040997 : Blo 1192413 2040997 := bbase (se 4 (by rfl) ⟨191343, by rfl⟩ : syracuseStep 2040997 = 382687) (by norm_num)
theorem B5096789 : Blo 1192413 5096789 := bbase (se 12 (by rfl) ⟨1866, by rfl⟩ : syracuseStep 5096789 = 3733) (by norm_num)
theorem B1910117 : Blo 1192413 1910117 := bbase (se 4 (by rfl) ⟨179073, by rfl⟩ : syracuseStep 1910117 = 358147) (by norm_num)
theorem B2418101 : Blo 1192413 2418101 := bbase (se 5 (by rfl) ⟨113348, by rfl⟩ : syracuseStep 2418101 = 226697) (by norm_num)
theorem B2041381 : Blo 1192413 2041381 := bbase (se 4 (by rfl) ⟨191379, by rfl⟩ : syracuseStep 2041381 = 382759) (by norm_num)
theorem B1910341 : Blo 1192413 1910341 := bbase (se 4 (by rfl) ⟨179094, by rfl⟩ : syracuseStep 1910341 = 358189) (by norm_num)
theorem B19613269 : Blo 1192413 19613269 := bbase (se 8 (by rfl) ⟨114921, by rfl⟩ : syracuseStep 19613269 = 229843) (by norm_num)
theorem B5097077 : Blo 1192413 5097077 := bbase (se 5 (by rfl) ⟨238925, by rfl⟩ : syracuseStep 5097077 = 477851) (by norm_num)
theorem B1910405 : Blo 1192413 1910405 := bbase (se 4 (by rfl) ⟨179100, by rfl⟩ : syracuseStep 1910405 = 358201) (by norm_num)
theorem B1910533 : Blo 1192413 1910533 := bbase (se 4 (by rfl) ⟨179112, by rfl⟩ : syracuseStep 1910533 = 358225) (by norm_num)
theorem B6801205 : Blo 1192413 6801205 := bbase (se 5 (by rfl) ⟨318806, by rfl⟩ : syracuseStep 6801205 = 637613) (by norm_num)
theorem B5973893 : Blo 1192413 5973893 := bbase (se 4 (by rfl) ⟨560052, by rfl⟩ : syracuseStep 5973893 = 1120105) (by norm_num)
theorem B1509293 : Blo 1192413 1509293 := bbase (se 3 (by rfl) ⟨282992, by rfl⟩ : syracuseStep 1509293 = 565985) (by norm_num)
theorem B2549693 : Blo 1192413 2549693 := bbase (se 3 (by rfl) ⟨478067, by rfl⟩ : syracuseStep 2549693 = 956135) (by norm_num)
theorem B1509349 : Blo 1192413 1509349 := bbase (se 4 (by rfl) ⟨141501, by rfl⟩ : syracuseStep 1509349 = 283003) (by norm_num)
theorem B7645205 : Blo 1192413 7645205 := bbase (se 6 (by rfl) ⟨179184, by rfl⟩ : syracuseStep 7645205 = 358369) (by norm_num)
theorem B1509445 : Blo 1192413 1509445 := bbase (se 4 (by rfl) ⟨141510, by rfl⟩ : syracuseStep 1509445 = 283021) (by norm_num)
theorem B2295877 : Blo 1192413 2295877 := bbase (se 4 (by rfl) ⟨215238, by rfl⟩ : syracuseStep 2295877 = 430477) (by norm_num)
theorem B2549837 : Blo 1192413 2549837 := bbase (se 3 (by rfl) ⟨478094, by rfl⟩ : syracuseStep 2549837 = 956189) (by norm_num)
theorem B2418797 : Blo 1192413 2418797 := bbase (se 3 (by rfl) ⟨453524, by rfl⟩ : syracuseStep 2418797 = 907049) (by norm_num)
theorem B2042093 : Blo 1192413 2042093 := bbase (se 3 (by rfl) ⟨382892, by rfl⟩ : syracuseStep 2042093 = 765785) (by norm_num)
theorem B1509617 : Blo 1192413 1509617 := bbase (se 2 (by rfl) ⟨566106, by rfl⟩ : syracuseStep 1509617 = 1132213) (by norm_num)
theorem B4024565 : Blo 1192413 4024565 := bbase (se 5 (by rfl) ⟨188651, by rfl⟩ : syracuseStep 4024565 = 377303) (by norm_num)
theorem B6039845 : Blo 1192413 6039845 := bbase (se 4 (by rfl) ⟨566235, by rfl⟩ : syracuseStep 6039845 = 1132471) (by norm_num)
theorem B1509673 : Blo 1192413 1509673 := bbase (se 2 (by rfl) ⟨566127, by rfl⟩ : syracuseStep 1509673 = 1132255) (by norm_num)
theorem B3148093 : Blo 1192413 3148093 := bbase (se 3 (by rfl) ⟨590267, by rfl⟩ : syracuseStep 3148093 = 1180535) (by norm_num)
theorem B2042189 : Blo 1192413 2042189 := bbase (se 3 (by rfl) ⟨382910, by rfl⟩ : syracuseStep 2042189 = 765821) (by norm_num)
theorem B5097829 : Blo 1192413 5097829 := bbase (se 4 (by rfl) ⟨477921, by rfl⟩ : syracuseStep 5097829 = 955843) (by norm_num)
theorem B1509769 : Blo 1192413 1509769 := bbase (se 2 (by rfl) ⟨566163, by rfl⟩ : syracuseStep 1509769 = 1132327) (by norm_num)
theorem B2148773 : Blo 1192413 2148773 := bbase (se 4 (by rfl) ⟨201447, by rfl⟩ : syracuseStep 2148773 = 402895) (by norm_num)
theorem B2550197 : Blo 1192413 2550197 := bbase (se 5 (by rfl) ⟨119540, by rfl⟩ : syracuseStep 2550197 = 239081) (by norm_num)
theorem B6121925 : Blo 1192413 6121925 := bbase (se 4 (by rfl) ⟨573930, by rfl⟩ : syracuseStep 6121925 = 1147861) (by norm_num)
theorem B8595989 : Blo 1192413 8595989 := bbase (se 6 (by rfl) ⟨201468, by rfl⟩ : syracuseStep 8595989 = 402937) (by norm_num)
theorem B2869789 : Blo 1192413 2869789 := bbase (se 3 (by rfl) ⟨538085, by rfl⟩ : syracuseStep 2869789 = 1076171) (by norm_num)
theorem B1509941 : Blo 1192413 1509941 := bbase (se 5 (by rfl) ⟨70778, by rfl⟩ : syracuseStep 1509941 = 141557) (by norm_num)
theorem B1698365 : Blo 1192413 1698365 := bbase (se 3 (by rfl) ⟨318443, by rfl⟩ : syracuseStep 1698365 = 636887) (by norm_num)
theorem B1509997 : Blo 1192413 1509997 := bbase (se 3 (by rfl) ⟨283124, by rfl⟩ : syracuseStep 1509997 = 566249) (by norm_num)
theorem B1698445 : Blo 1192413 1698445 := bbase (se 3 (by rfl) ⟨318458, by rfl⟩ : syracuseStep 1698445 = 636917) (by norm_num)
theorem B4024997 : Blo 1192413 4024997 := bbase (se 4 (by rfl) ⟨377343, by rfl⟩ : syracuseStep 4024997 = 754687) (by norm_num)
theorem B1510093 : Blo 1192413 1510093 := bbase (se 3 (by rfl) ⟨283142, by rfl⟩ : syracuseStep 1510093 = 566285) (by norm_num)
theorem B1788629 : Blo 1192413 1788629 := bbase (se 7 (by rfl) ⟨20960, by rfl⟩ : syracuseStep 1788629 = 41921) (by norm_num)
theorem B2263781 : Blo 1192413 2263781 := bbase (se 4 (by rfl) ⟨212229, by rfl⟩ : syracuseStep 2263781 = 424459) (by norm_num)
theorem B1788653 : Blo 1192413 1788653 := bbase (se 3 (by rfl) ⟨335372, by rfl⟩ : syracuseStep 1788653 = 670745) (by norm_num)
theorem B1788677 : Blo 1192413 1788677 := bbase (se 4 (by rfl) ⟨167688, by rfl⟩ : syracuseStep 1788677 = 335377) (by norm_num)
theorem B1698565 : Blo 1192413 1698565 := bbase (se 4 (by rfl) ⟨159240, by rfl⟩ : syracuseStep 1698565 = 318481) (by norm_num)
theorem B1788701 : Blo 1192413 1788701 := bbase (se 3 (by rfl) ⟨335381, by rfl⟩ : syracuseStep 1788701 = 670763) (by norm_num)
theorem B4533029 : Blo 1192413 4533029 := bbase (se 4 (by rfl) ⟨424971, by rfl⟩ : syracuseStep 4533029 = 849943) (by norm_num)
theorem B1788725 : Blo 1192413 1788725 := bbase (se 5 (by rfl) ⟨83846, by rfl⟩ : syracuseStep 1788725 = 167693) (by norm_num)
theorem B1788749 : Blo 1192413 1788749 := bbase (se 3 (by rfl) ⟨335390, by rfl⟩ : syracuseStep 1788749 = 670781) (by norm_num)
theorem B1788773 : Blo 1192413 1788773 := bbase (se 4 (by rfl) ⟨167697, by rfl⟩ : syracuseStep 1788773 = 335395) (by norm_num)
theorem B1698661 : Blo 1192413 1698661 := bbase (se 4 (by rfl) ⟨159249, by rfl⟩ : syracuseStep 1698661 = 318499) (by norm_num)
theorem B2263925 : Blo 1192413 2263925 := bbase (se 5 (by rfl) ⟨106121, by rfl⟩ : syracuseStep 2263925 = 212243) (by norm_num)
theorem B1510265 : Blo 1192413 1510265 := bbase (se 2 (by rfl) ⟨566349, by rfl⟩ : syracuseStep 1510265 = 1132699) (by norm_num)
theorem B1788797 : Blo 1192413 1788797 := bbase (se 3 (by rfl) ⟨335399, by rfl⟩ : syracuseStep 1788797 = 670799) (by norm_num)
theorem B1788821 : Blo 1192413 1788821 := bbase (se 6 (by rfl) ⟨41925, by rfl⟩ : syracuseStep 1788821 = 83851) (by norm_num)
theorem B1788845 : Blo 1192413 1788845 := bbase (se 3 (by rfl) ⟨335408, by rfl⟩ : syracuseStep 1788845 = 670817) (by norm_num)
theorem B1510321 : Blo 1192413 1510321 := bbase (se 2 (by rfl) ⟨566370, by rfl⟩ : syracuseStep 1510321 = 1132741) (by norm_num)
theorem B1788869 : Blo 1192413 1788869 := bbase (se 4 (by rfl) ⟨167706, by rfl⟩ : syracuseStep 1788869 = 335413) (by norm_num)
theorem B1911757 : Blo 1192413 1911757 := bbase (se 3 (by rfl) ⟨358454, by rfl⟩ : syracuseStep 1911757 = 716909) (by norm_num)
theorem B1788893 : Blo 1192413 1788893 := bbase (se 3 (by rfl) ⟨335417, by rfl⟩ : syracuseStep 1788893 = 670835) (by norm_num)
theorem B1788917 : Blo 1192413 1788917 := bbase (se 5 (by rfl) ⟨83855, by rfl⟩ : syracuseStep 1788917 = 167711) (by norm_num)
theorem B9063413 : Blo 1192413 9063413 := bbase (se 5 (by rfl) ⟨424847, by rfl⟩ : syracuseStep 9063413 = 849695) (by norm_num)
theorem B1788941 : Blo 1192413 1788941 := bbase (se 3 (by rfl) ⟨335426, by rfl⟩ : syracuseStep 1788941 = 670853) (by norm_num)
theorem B1510417 : Blo 1192413 1510417 := bbase (se 2 (by rfl) ⟨566406, by rfl⟩ : syracuseStep 1510417 = 1132813) (by norm_num)
theorem B1788965 : Blo 1192413 1788965 := bbase (se 4 (by rfl) ⟨167715, by rfl⟩ : syracuseStep 1788965 = 335431) (by norm_num)
theorem B1788989 : Blo 1192413 1788989 := bbase (se 3 (by rfl) ⟨335435, by rfl⟩ : syracuseStep 1788989 = 670871) (by norm_num)
theorem B5098565 : Blo 1192413 5098565 := bbase (se 4 (by rfl) ⟨477990, by rfl⟩ : syracuseStep 5098565 = 955981) (by norm_num)
theorem B4533317 : Blo 1192413 4533317 := bbase (se 4 (by rfl) ⟨424998, by rfl⟩ : syracuseStep 4533317 = 849997) (by norm_num)
theorem B1789013 : Blo 1192413 1789013 := bbase (se 8 (by rfl) ⟨10482, by rfl⟩ : syracuseStep 1789013 = 20965) (by norm_num)
theorem B4025429 : Blo 1192413 4025429 := bbase (se 8 (by rfl) ⟨23586, by rfl⟩ : syracuseStep 4025429 = 47173) (by norm_num)
theorem B1789037 : Blo 1192413 1789037 := bbase (se 3 (by rfl) ⟨335444, by rfl⟩ : syracuseStep 1789037 = 670889) (by norm_num)
theorem B1789061 : Blo 1192413 1789061 := bbase (se 4 (by rfl) ⟨167724, by rfl⟩ : syracuseStep 1789061 = 335449) (by norm_num)
theorem B2264213 : Blo 1192413 2264213 := bbase (se 6 (by rfl) ⟨53067, by rfl⟩ : syracuseStep 2264213 = 106135) (by norm_num)
theorem B10890389 : Blo 1192413 10890389 := bbase (se 6 (by rfl) ⟨255243, by rfl⟩ : syracuseStep 10890389 = 510487) (by norm_num)
theorem B1789085 : Blo 1192413 1789085 := bbase (se 3 (by rfl) ⟨335453, by rfl⟩ : syracuseStep 1789085 = 670907) (by norm_num)
theorem B1789109 : Blo 1192413 1789109 := bbase (se 5 (by rfl) ⟨83864, by rfl⟩ : syracuseStep 1789109 = 167729) (by norm_num)
theorem B1510589 : Blo 1192413 1510589 := bbase (se 3 (by rfl) ⟨283235, by rfl⟩ : syracuseStep 1510589 = 566471) (by norm_num)
theorem B1789133 : Blo 1192413 1789133 := bbase (se 3 (by rfl) ⟨335462, by rfl⟩ : syracuseStep 1789133 = 670925) (by norm_num)
theorem B1789157 : Blo 1192413 1789157 := bbase (se 4 (by rfl) ⟨167733, by rfl⟩ : syracuseStep 1789157 = 335467) (by norm_num)
theorem B1510645 : Blo 1192413 1510645 := bbase (se 5 (by rfl) ⟨70811, by rfl⟩ : syracuseStep 1510645 = 141623) (by norm_num)
theorem B1789181 : Blo 1192413 1789181 := bbase (se 3 (by rfl) ⟨335471, by rfl⟩ : syracuseStep 1789181 = 670943) (by norm_num)
theorem B1813757 : Blo 1192413 1813757 := bbase (se 3 (by rfl) ⟨340079, by rfl⟩ : syracuseStep 1813757 = 680159) (by norm_num)
theorem B1789205 : Blo 1192413 1789205 := bbase (se 6 (by rfl) ⟨41934, by rfl⟩ : syracuseStep 1789205 = 83869) (by norm_num)
theorem B1723685 : Blo 1192413 1723685 := bbase (se 4 (by rfl) ⟨161595, by rfl⟩ : syracuseStep 1723685 = 323191) (by norm_num)
theorem B2264365 : Blo 1192413 2264365 := bbase (se 3 (by rfl) ⟨424568, by rfl⟩ : syracuseStep 2264365 = 849137) (by norm_num)
theorem B1789229 : Blo 1192413 1789229 := bbase (se 3 (by rfl) ⟨335480, by rfl⟩ : syracuseStep 1789229 = 670961) (by norm_num)
theorem B2420029 : Blo 1192413 2420029 := bbase (se 3 (by rfl) ⟨453755, by rfl⟩ : syracuseStep 2420029 = 907511) (by norm_num)
theorem B1789253 : Blo 1192413 1789253 := bbase (se 4 (by rfl) ⟨167742, by rfl⟩ : syracuseStep 1789253 = 335485) (by norm_num)
theorem B1699157 : Blo 1192413 1699157 := bbase (se 11 (by rfl) ⟨1244, by rfl⟩ : syracuseStep 1699157 = 2489) (by norm_num)
theorem B1510741 : Blo 1192413 1510741 := bbase (se 11 (by rfl) ⟨1106, by rfl⟩ : syracuseStep 1510741 = 2213) (by norm_num)
theorem B1789277 : Blo 1192413 1789277 := bbase (se 3 (by rfl) ⟨335489, by rfl⟩ : syracuseStep 1789277 = 670979) (by norm_num)
theorem B1789301 : Blo 1192413 1789301 := bbase (se 5 (by rfl) ⟨83873, by rfl⟩ : syracuseStep 1789301 = 167747) (by norm_num)
theorem B1789325 : Blo 1192413 1789325 := bbase (se 3 (by rfl) ⟨335498, by rfl⟩ : syracuseStep 1789325 = 670997) (by norm_num)
theorem B9055637 : Blo 1192413 9055637 := bbase (se 6 (by rfl) ⟨212241, by rfl⟩ : syracuseStep 9055637 = 424483) (by norm_num)
theorem B1789349 : Blo 1192413 1789349 := bbase (se 4 (by rfl) ⟨167751, by rfl⟩ : syracuseStep 1789349 = 335503) (by norm_num)
theorem B1789373 : Blo 1192413 1789373 := bbase (se 3 (by rfl) ⟨335507, by rfl⟩ : syracuseStep 1789373 = 671015) (by norm_num)
theorem B1789397 : Blo 1192413 1789397 := bbase (se 7 (by rfl) ⟨20969, by rfl⟩ : syracuseStep 1789397 = 41939) (by norm_num)
theorem B16141781 : Blo 1192413 16141781 := bbase (se 7 (by rfl) ⟨189161, by rfl⟩ : syracuseStep 16141781 = 378323) (by norm_num)
theorem B1789421 : Blo 1192413 1789421 := bbase (se 3 (by rfl) ⟨335516, by rfl⟩ : syracuseStep 1789421 = 671033) (by norm_num)
theorem B1510913 : Blo 1192413 1510913 := bbase (se 2 (by rfl) ⟨566592, by rfl⟩ : syracuseStep 1510913 = 1133185) (by norm_num)
theorem B4025861 : Blo 1192413 4025861 := bbase (se 4 (by rfl) ⟨377424, by rfl⟩ : syracuseStep 4025861 = 754849) (by norm_num)
theorem B1789445 : Blo 1192413 1789445 := bbase (se 4 (by rfl) ⟨167760, by rfl⟩ : syracuseStep 1789445 = 335521) (by norm_num)
theorem B1789469 : Blo 1192413 1789469 := bbase (se 3 (by rfl) ⟨335525, by rfl⟩ : syracuseStep 1789469 = 671051) (by norm_num)
theorem B1789493 : Blo 1192413 1789493 := bbase (se 5 (by rfl) ⟨83882, by rfl⟩ : syracuseStep 1789493 = 167765) (by norm_num)
theorem B6041141 : Blo 1192413 6041141 := bbase (se 5 (by rfl) ⟨283178, by rfl⟩ : syracuseStep 6041141 = 566357) (by norm_num)
theorem B1510969 : Blo 1192413 1510969 := bbase (se 2 (by rfl) ⟨566613, by rfl⟩ : syracuseStep 1510969 = 1133227) (by norm_num)
theorem B1789517 : Blo 1192413 1789517 := bbase (se 3 (by rfl) ⟨335534, by rfl⟩ : syracuseStep 1789517 = 671069) (by norm_num)
theorem B2264669 : Blo 1192413 2264669 := bbase (se 3 (by rfl) ⟨424625, by rfl⟩ : syracuseStep 2264669 = 849251) (by norm_num)
theorem B1789541 : Blo 1192413 1789541 := bbase (se 4 (by rfl) ⟨167769, by rfl⟩ : syracuseStep 1789541 = 335539) (by norm_num)
theorem B1912429 : Blo 1192413 1912429 := bbase (se 3 (by rfl) ⟨358580, by rfl⟩ : syracuseStep 1912429 = 717161) (by norm_num)
theorem B1789565 : Blo 1192413 1789565 := bbase (se 3 (by rfl) ⟨335543, by rfl⟩ : syracuseStep 1789565 = 671087) (by norm_num)
theorem B1789589 : Blo 1192413 1789589 := bbase (se 6 (by rfl) ⟨41943, by rfl⟩ : syracuseStep 1789589 = 83887) (by norm_num)
theorem B1511065 : Blo 1192413 1511065 := bbase (se 2 (by rfl) ⟨566649, by rfl⟩ : syracuseStep 1511065 = 1133299) (by norm_num)
theorem B1789613 : Blo 1192413 1789613 := bbase (se 3 (by rfl) ⟨335552, by rfl⟩ : syracuseStep 1789613 = 671105) (by norm_num)
theorem B2617013 : Blo 1192413 2617013 := bbase (se 5 (by rfl) ⟨122672, by rfl⟩ : syracuseStep 2617013 = 245345) (by norm_num)
theorem B1789637 : Blo 1192413 1789637 := bbase (se 4 (by rfl) ⟨167778, by rfl⟩ : syracuseStep 1789637 = 335557) (by norm_num)
theorem B6123221 : Blo 1192413 6123221 := bbase (se 7 (by rfl) ⟨71756, by rfl⟩ : syracuseStep 6123221 = 143513) (by norm_num)
theorem B1789661 : Blo 1192413 1789661 := bbase (se 3 (by rfl) ⟨335561, by rfl⟩ : syracuseStep 1789661 = 671123) (by norm_num)
theorem B3018485 : Blo 1192413 3018485 := bbase (se 5 (by rfl) ⟨141491, by rfl⟩ : syracuseStep 3018485 = 282983) (by norm_num)
theorem B1789685 : Blo 1192413 1789685 := bbase (se 5 (by rfl) ⟨83891, by rfl⟩ : syracuseStep 1789685 = 167783) (by norm_num)
theorem B1789709 : Blo 1192413 1789709 := bbase (se 3 (by rfl) ⟨335570, by rfl⟩ : syracuseStep 1789709 = 671141) (by norm_num)
theorem B1789733 : Blo 1192413 1789733 := bbase (se 4 (by rfl) ⟨167787, by rfl⟩ : syracuseStep 1789733 = 335575) (by norm_num)
theorem B5730101 : Blo 1192413 5730101 := bbase (se 5 (by rfl) ⟨268598, by rfl⟩ : syracuseStep 5730101 = 537197) (by norm_num)
theorem B1789757 : Blo 1192413 1789757 := bbase (se 3 (by rfl) ⟨335579, by rfl⟩ : syracuseStep 1789757 = 671159) (by norm_num)
theorem B1511237 : Blo 1192413 1511237 := bbase (se 4 (by rfl) ⟨141678, by rfl⟩ : syracuseStep 1511237 = 283357) (by norm_num)
theorem B1789781 : Blo 1192413 1789781 := bbase (se 9 (by rfl) ⟨5243, by rfl⟩ : syracuseStep 1789781 = 10487) (by norm_num)
theorem B1789805 : Blo 1192413 1789805 := bbase (se 3 (by rfl) ⟨335588, by rfl⟩ : syracuseStep 1789805 = 671177) (by norm_num)
theorem B2723701 : Blo 1192413 2723701 := bbase (se 5 (by rfl) ⟨127673, by rfl⟩ : syracuseStep 2723701 = 255347) (by norm_num)
theorem B1699709 : Blo 1192413 1699709 := bbase (se 3 (by rfl) ⟨318695, by rfl⟩ : syracuseStep 1699709 = 637391) (by norm_num)
theorem B1511293 : Blo 1192413 1511293 := bbase (se 3 (by rfl) ⟨283367, by rfl⟩ : syracuseStep 1511293 = 566735) (by norm_num)
theorem B1789829 : Blo 1192413 1789829 := bbase (se 4 (by rfl) ⟨167796, by rfl⟩ : syracuseStep 1789829 = 335593) (by norm_num)
theorem B1273753 : Blo 1192413 1273753 := bbase (se 2 (by rfl) ⟨477657, by rfl⟩ : syracuseStep 1273753 = 955315) (by norm_num)
theorem B1789853 : Blo 1192413 1789853 := bbase (se 3 (by rfl) ⟨335597, by rfl⟩ : syracuseStep 1789853 = 671195) (by norm_num)
theorem B4026293 : Blo 1192413 4026293 := bbase (se 5 (by rfl) ⟨188732, by rfl⟩ : syracuseStep 4026293 = 377465) (by norm_num)
theorem B1789877 : Blo 1192413 1789877 := bbase (se 5 (by rfl) ⟨83900, by rfl⟩ : syracuseStep 1789877 = 167801) (by norm_num)
theorem B1789901 : Blo 1192413 1789901 := bbase (se 3 (by rfl) ⟨335606, by rfl⟩ : syracuseStep 1789901 = 671213) (by norm_num)
theorem B1511389 : Blo 1192413 1511389 := bbase (se 3 (by rfl) ⟨283385, by rfl⟩ : syracuseStep 1511389 = 566771) (by norm_num)
theorem B1273825 : Blo 1192413 1273825 := bbase (se 2 (by rfl) ⟨477684, by rfl⟩ : syracuseStep 1273825 = 955369) (by norm_num)
theorem B1789925 : Blo 1192413 1789925 := bbase (se 4 (by rfl) ⟨167805, by rfl⟩ : syracuseStep 1789925 = 335611) (by norm_num)
theorem B1789949 : Blo 1192413 1789949 := bbase (se 3 (by rfl) ⟨335615, by rfl⟩ : syracuseStep 1789949 = 671231) (by norm_num)
theorem B5451781 : Blo 1192413 5451781 := bbase (se 4 (by rfl) ⟨511104, by rfl⟩ : syracuseStep 5451781 = 1022209) (by norm_num)
theorem B1789973 : Blo 1192413 1789973 := bbase (se 6 (by rfl) ⟨41952, by rfl⟩ : syracuseStep 1789973 = 83905) (by norm_num)
theorem B1789997 : Blo 1192413 1789997 := bbase (se 3 (by rfl) ⟨335624, by rfl⟩ : syracuseStep 1789997 = 671249) (by norm_num)
theorem B1790021 : Blo 1192413 1790021 := bbase (se 4 (by rfl) ⟨167814, by rfl⟩ : syracuseStep 1790021 = 335629) (by norm_num)
theorem B3018829 : Blo 1192413 3018829 := bbase (se 3 (by rfl) ⟨566030, by rfl⟩ : syracuseStep 3018829 = 1132061) (by norm_num)
theorem B1790045 : Blo 1192413 1790045 := bbase (se 3 (by rfl) ⟨335633, by rfl⟩ : syracuseStep 1790045 = 671267) (by norm_num)
theorem B5738597 : Blo 1192413 5738597 := bbase (se 4 (by rfl) ⟨537993, by rfl⟩ : syracuseStep 5738597 = 1075987) (by norm_num)
theorem B2682989 : Blo 1192413 2682989 := bbase (se 3 (by rfl) ⟨503060, by rfl⟩ : syracuseStep 2682989 = 1006121) (by norm_num)
theorem B1790069 : Blo 1192413 1790069 := bbase (se 5 (by rfl) ⟨83909, by rfl⟩ : syracuseStep 1790069 = 167819) (by norm_num)
theorem B1511561 : Blo 1192413 1511561 := bbase (se 2 (by rfl) ⟨566835, by rfl⟩ : syracuseStep 1511561 = 1133671) (by norm_num)
theorem B1790093 : Blo 1192413 1790093 := bbase (se 3 (by rfl) ⟨335642, by rfl⟩ : syracuseStep 1790093 = 671285) (by norm_num)
theorem B1274005 : Blo 1192413 1274005 := bbase (se 6 (by rfl) ⟨29859, by rfl⟩ : syracuseStep 1274005 = 59719) (by norm_num)
theorem B1790117 : Blo 1192413 1790117 := bbase (se 4 (by rfl) ⟨167823, by rfl⟩ : syracuseStep 1790117 = 335647) (by norm_num)
theorem B2683061 : Blo 1192413 2683061 := bbase (se 5 (by rfl) ⟨125768, by rfl⟩ : syracuseStep 2683061 = 251537) (by norm_num)
theorem B3018941 : Blo 1192413 3018941 := bbase (se 3 (by rfl) ⟨566051, by rfl⟩ : syracuseStep 3018941 = 1132103) (by norm_num)
theorem B1790141 : Blo 1192413 1790141 := bbase (se 3 (by rfl) ⟨335651, by rfl⟩ : syracuseStep 1790141 = 671303) (by norm_num)
theorem B1511617 : Blo 1192413 1511617 := bbase (se 2 (by rfl) ⟨566856, by rfl⟩ : syracuseStep 1511617 = 1133713) (by norm_num)
theorem B1790165 : Blo 1192413 1790165 := bbase (se 7 (by rfl) ⟨20978, by rfl⟩ : syracuseStep 1790165 = 41957) (by norm_num)
theorem B4534501 : Blo 1192413 4534501 := bbase (se 4 (by rfl) ⟨425109, by rfl⟩ : syracuseStep 4534501 = 850219) (by norm_num)
theorem B1790189 : Blo 1192413 1790189 := bbase (se 3 (by rfl) ⟨335660, by rfl⟩ : syracuseStep 1790189 = 671321) (by norm_num)
theorem B2683133 : Blo 1192413 2683133 := bbase (se 3 (by rfl) ⟨503087, by rfl⟩ : syracuseStep 2683133 = 1006175) (by norm_num)
theorem B2584829 : Blo 1192413 2584829 := bbase (se 3 (by rfl) ⟨484655, by rfl⟩ : syracuseStep 2584829 = 969311) (by norm_num)
theorem B1790213 : Blo 1192413 1790213 := bbase (se 4 (by rfl) ⟨167832, by rfl⟩ : syracuseStep 1790213 = 335665) (by norm_num)
theorem B1790237 : Blo 1192413 1790237 := bbase (se 3 (by rfl) ⟨335669, by rfl⟩ : syracuseStep 1790237 = 671339) (by norm_num)
theorem B1790261 : Blo 1192413 1790261 := bbase (se 5 (by rfl) ⟨83918, by rfl⟩ : syracuseStep 1790261 = 167837) (by norm_num)
theorem B2683205 : Blo 1192413 2683205 := bbase (se 4 (by rfl) ⟨251550, by rfl⟩ : syracuseStep 2683205 = 503101) (by norm_num)
theorem B2265421 : Blo 1192413 2265421 := bbase (se 3 (by rfl) ⟨424766, by rfl⟩ : syracuseStep 2265421 = 849533) (by norm_num)
theorem B1790285 : Blo 1192413 1790285 := bbase (se 3 (by rfl) ⟨335678, by rfl⟩ : syracuseStep 1790285 = 671357) (by norm_num)
theorem B4026725 : Blo 1192413 4026725 := bbase (se 4 (by rfl) ⟨377505, by rfl⟩ : syracuseStep 4026725 = 755011) (by norm_num)
theorem B1790309 : Blo 1192413 1790309 := bbase (se 4 (by rfl) ⟨167841, by rfl⟩ : syracuseStep 1790309 = 335683) (by norm_num)
theorem B1208701 : Blo 1192413 1208701 := bbase (se 3 (by rfl) ⟨226631, by rfl⟩ : syracuseStep 1208701 = 453263) (by norm_num)
theorem B3019133 : Blo 1192413 3019133 := bbase (se 3 (by rfl) ⟨566087, by rfl⟩ : syracuseStep 3019133 = 1132175) (by norm_num)
theorem B1790333 : Blo 1192413 1790333 := bbase (se 3 (by rfl) ⟨335687, by rfl⟩ : syracuseStep 1790333 = 671375) (by norm_num)
theorem B2683277 : Blo 1192413 2683277 := bbase (se 3 (by rfl) ⟨503114, by rfl⟩ : syracuseStep 2683277 = 1006229) (by norm_num)
theorem B1790357 : Blo 1192413 1790357 := bbase (se 6 (by rfl) ⟨41961, by rfl⟩ : syracuseStep 1790357 = 83923) (by norm_num)
theorem B1790381 : Blo 1192413 1790381 := bbase (se 3 (by rfl) ⟨335696, by rfl⟩ : syracuseStep 1790381 = 671393) (by norm_num)
theorem B1790405 : Blo 1192413 1790405 := bbase (se 4 (by rfl) ⟨167850, by rfl⟩ : syracuseStep 1790405 = 335701) (by norm_num)
theorem B2683349 : Blo 1192413 2683349 := bbase (se 7 (by rfl) ⟨31445, by rfl⟩ : syracuseStep 2683349 = 62891) (by norm_num)
theorem B2265565 : Blo 1192413 2265565 := bbase (se 3 (by rfl) ⟨424793, by rfl⟩ : syracuseStep 2265565 = 849587) (by norm_num)
theorem B1790429 : Blo 1192413 1790429 := bbase (se 3 (by rfl) ⟨335705, by rfl⟩ : syracuseStep 1790429 = 671411) (by norm_num)
theorem B1790453 : Blo 1192413 1790453 := bbase (se 5 (by rfl) ⟨83927, by rfl⟩ : syracuseStep 1790453 = 167855) (by norm_num)
theorem B1790477 : Blo 1192413 1790477 := bbase (se 3 (by rfl) ⟨335714, by rfl⟩ : syracuseStep 1790477 = 671429) (by norm_num)
theorem B4534805 : Blo 1192413 4534805 := bbase (se 6 (by rfl) ⟨106284, by rfl⟩ : syracuseStep 4534805 = 212569) (by norm_num)
theorem B2683421 : Blo 1192413 2683421 := bbase (se 3 (by rfl) ⟨503141, by rfl⟩ : syracuseStep 2683421 = 1006283) (by norm_num)
theorem B1790501 : Blo 1192413 1790501 := bbase (se 4 (by rfl) ⟨167859, by rfl⟩ : syracuseStep 1790501 = 335719) (by norm_num)
theorem B1790525 : Blo 1192413 1790525 := bbase (se 3 (by rfl) ⟨335723, by rfl⟩ : syracuseStep 1790525 = 671447) (by norm_num)
theorem B1274449 : Blo 1192413 1274449 := bbase (se 2 (by rfl) ⟨477918, by rfl⟩ : syracuseStep 1274449 = 955837) (by norm_num)
theorem B1790549 : Blo 1192413 1790549 := bbase (se 8 (by rfl) ⟨10491, by rfl⟩ : syracuseStep 1790549 = 20983) (by norm_num)
theorem B2683493 : Blo 1192413 2683493 := bbase (se 4 (by rfl) ⟨251577, by rfl⟩ : syracuseStep 2683493 = 503155) (by norm_num)
theorem B1790573 : Blo 1192413 1790573 := bbase (se 3 (by rfl) ⟨335732, by rfl⟩ : syracuseStep 1790573 = 671465) (by norm_num)
theorem B1700461 : Blo 1192413 1700461 := bbase (se 3 (by rfl) ⟨318836, by rfl⟩ : syracuseStep 1700461 = 637673) (by norm_num)
theorem B1208953 : Blo 1192413 1208953 := bbase (se 2 (by rfl) ⟨453357, by rfl⟩ : syracuseStep 1208953 = 906715) (by norm_num)
theorem B2265725 : Blo 1192413 2265725 := bbase (se 3 (by rfl) ⟨424823, by rfl⟩ : syracuseStep 2265725 = 849647) (by norm_num)
theorem B1790597 : Blo 1192413 1790597 := bbase (se 4 (by rfl) ⟨167868, by rfl⟩ : syracuseStep 1790597 = 335737) (by norm_num)
theorem B1225373 : Blo 1192413 1225373 := bbase (se 3 (by rfl) ⟨229757, by rfl⟩ : syracuseStep 1225373 = 459515) (by norm_num)
theorem B1790621 : Blo 1192413 1790621 := bbase (se 3 (by rfl) ⟨335741, by rfl⟩ : syracuseStep 1790621 = 671483) (by norm_num)
theorem B2683565 : Blo 1192413 2683565 := bbase (se 3 (by rfl) ⟨503168, by rfl⟩ : syracuseStep 2683565 = 1006337) (by norm_num)
theorem B1790645 : Blo 1192413 1790645 := bbase (se 5 (by rfl) ⟨83936, by rfl⟩ : syracuseStep 1790645 = 167873) (by norm_num)
theorem B1274573 : Blo 1192413 1274573 := bbase (se 3 (by rfl) ⟨238982, by rfl⟩ : syracuseStep 1274573 = 477965) (by norm_num)
theorem B1790669 : Blo 1192413 1790669 := bbase (se 3 (by rfl) ⟨335750, by rfl⟩ : syracuseStep 1790669 = 671501) (by norm_num)
theorem B3019477 : Blo 1192413 3019477 := bbase (se 7 (by rfl) ⟨35384, by rfl⟩ : syracuseStep 3019477 = 70769) (by norm_num)
theorem B6206165 : Blo 1192413 6206165 := bbase (se 7 (by rfl) ⟨72728, by rfl⟩ : syracuseStep 6206165 = 145457) (by norm_num)
theorem B1790693 : Blo 1192413 1790693 := bbase (se 4 (by rfl) ⟨167877, by rfl⟩ : syracuseStep 1790693 = 335755) (by norm_num)
theorem B2683637 : Blo 1192413 2683637 := bbase (se 5 (by rfl) ⟨125795, by rfl⟩ : syracuseStep 2683637 = 251591) (by norm_num)
theorem B1790717 : Blo 1192413 1790717 := bbase (se 3 (by rfl) ⟨335759, by rfl⟩ : syracuseStep 1790717 = 671519) (by norm_num)
theorem B2265869 : Blo 1192413 2265869 := bbase (se 3 (by rfl) ⟨424850, by rfl⟩ : syracuseStep 2265869 = 849701) (by norm_num)
theorem B4027157 : Blo 1192413 4027157 := bbase (se 6 (by rfl) ⟨94386, by rfl⟩ : syracuseStep 4027157 = 188773) (by norm_num)
theorem B1790741 : Blo 1192413 1790741 := bbase (se 6 (by rfl) ⟨41970, by rfl⟩ : syracuseStep 1790741 = 83941) (by norm_num)
theorem B1790765 : Blo 1192413 1790765 := bbase (se 3 (by rfl) ⟨335768, by rfl⟩ : syracuseStep 1790765 = 671537) (by norm_num)
theorem B2904893 : Blo 1192413 2904893 := bbase (se 3 (by rfl) ⟨544667, by rfl⟩ : syracuseStep 2904893 = 1089335) (by norm_num)
theorem B2683709 : Blo 1192413 2683709 := bbase (se 3 (by rfl) ⟨503195, by rfl⟩ : syracuseStep 2683709 = 1006391) (by norm_num)
theorem B3019589 : Blo 1192413 3019589 := bbase (se 4 (by rfl) ⟨283086, by rfl⟩ : syracuseStep 3019589 = 566173) (by norm_num)
theorem B6042437 : Blo 1192413 6042437 := bbase (se 4 (by rfl) ⟨566478, by rfl⟩ : syracuseStep 6042437 = 1132957) (by norm_num)
theorem B1790789 : Blo 1192413 1790789 := bbase (se 4 (by rfl) ⟨167886, by rfl⟩ : syracuseStep 1790789 = 335773) (by norm_num)
theorem B1790813 : Blo 1192413 1790813 := bbase (se 3 (by rfl) ⟨335777, by rfl⟩ : syracuseStep 1790813 = 671555) (by norm_num)
theorem B1790837 : Blo 1192413 1790837 := bbase (se 5 (by rfl) ⟨83945, by rfl⟩ : syracuseStep 1790837 = 167891) (by norm_num)
theorem B2683781 : Blo 1192413 2683781 := bbase (se 4 (by rfl) ⟨251604, by rfl⟩ : syracuseStep 2683781 = 503209) (by norm_num)
theorem B1790861 : Blo 1192413 1790861 := bbase (se 3 (by rfl) ⟨335786, by rfl⟩ : syracuseStep 1790861 = 671573) (by norm_num)
theorem B11465621 : Blo 1192413 11465621 := bbase (se 6 (by rfl) ⟨268725, by rfl⟩ : syracuseStep 11465621 = 537451) (by norm_num)
theorem B1790885 : Blo 1192413 1790885 := bbase (se 4 (by rfl) ⟨167895, by rfl⟩ : syracuseStep 1790885 = 335791) (by norm_num)
theorem B1815461 : Blo 1192413 1815461 := bbase (se 4 (by rfl) ⟨170199, by rfl⟩ : syracuseStep 1815461 = 340399) (by norm_num)
theorem B7648181 : Blo 1192413 7648181 := bbase (se 5 (by rfl) ⟨358508, by rfl⟩ : syracuseStep 7648181 = 717017) (by norm_num)
theorem B1790909 : Blo 1192413 1790909 := bbase (se 3 (by rfl) ⟨335795, by rfl⟩ : syracuseStep 1790909 = 671591) (by norm_num)
theorem B1274825 : Blo 1192413 1274825 := bbase (se 2 (by rfl) ⟨478059, by rfl⟩ : syracuseStep 1274825 = 956119) (by norm_num)
theorem B2683853 : Blo 1192413 2683853 := bbase (se 3 (by rfl) ⟨503222, by rfl⟩ : syracuseStep 2683853 = 1006445) (by norm_num)
theorem B1790933 : Blo 1192413 1790933 := bbase (se 7 (by rfl) ⟨20987, by rfl⟩ : syracuseStep 1790933 = 41975) (by norm_num)
theorem B1790957 : Blo 1192413 1790957 := bbase (se 3 (by rfl) ⟨335804, by rfl⟩ : syracuseStep 1790957 = 671609) (by norm_num)
theorem B3019781 : Blo 1192413 3019781 := bbase (se 4 (by rfl) ⟨283104, by rfl⟩ : syracuseStep 3019781 = 566209) (by norm_num)
theorem B1790981 : Blo 1192413 1790981 := bbase (se 4 (by rfl) ⟨167904, by rfl⟩ : syracuseStep 1790981 = 335809) (by norm_num)
theorem B2683925 : Blo 1192413 2683925 := bbase (se 6 (by rfl) ⟨62904, by rfl⟩ : syracuseStep 2683925 = 125809) (by norm_num)
theorem B1791005 : Blo 1192413 1791005 := bbase (se 3 (by rfl) ⟨335813, by rfl⟩ : syracuseStep 1791005 = 671627) (by norm_num)
theorem B2266157 : Blo 1192413 2266157 := bbase (se 3 (by rfl) ⟨424904, by rfl⟩ : syracuseStep 2266157 = 849809) (by norm_num)
theorem B3224629 : Blo 1192413 3224629 := bbase (se 5 (by rfl) ⟨151154, by rfl⟩ : syracuseStep 3224629 = 302309) (by norm_num)
theorem B9679925 : Blo 1192413 9679925 := bbase (se 5 (by rfl) ⟨453746, by rfl⟩ : syracuseStep 9679925 = 907493) (by norm_num)
theorem B1791029 : Blo 1192413 1791029 := bbase (se 5 (by rfl) ⟨83954, by rfl⟩ : syracuseStep 1791029 = 167909) (by norm_num)
theorem B1791053 : Blo 1192413 1791053 := bbase (se 3 (by rfl) ⟨335822, by rfl⟩ : syracuseStep 1791053 = 671645) (by norm_num)
theorem B2683997 : Blo 1192413 2683997 := bbase (se 3 (by rfl) ⟨503249, by rfl⟩ : syracuseStep 2683997 = 1006499) (by norm_num)
theorem B1791077 : Blo 1192413 1791077 := bbase (se 4 (by rfl) ⟨167913, by rfl⟩ : syracuseStep 1791077 = 335827) (by norm_num)
theorem B2012269 : Blo 1192413 2012269 := bbase (se 3 (by rfl) ⟨377300, by rfl⟩ : syracuseStep 2012269 = 754601) (by norm_num)
theorem B1791101 : Blo 1192413 1791101 := bbase (se 3 (by rfl) ⟨335831, by rfl⟩ : syracuseStep 1791101 = 671663) (by norm_num)
theorem B1791125 : Blo 1192413 1791125 := bbase (se 6 (by rfl) ⟨41979, by rfl⟩ : syracuseStep 1791125 = 83959) (by norm_num)
theorem B2684069 : Blo 1192413 2684069 := bbase (se 4 (by rfl) ⟨251631, by rfl⟩ : syracuseStep 2684069 = 503263) (by norm_num)
theorem B1791149 : Blo 1192413 1791149 := bbase (se 3 (by rfl) ⟨335840, by rfl⟩ : syracuseStep 1791149 = 671681) (by norm_num)
theorem B1635509 : Blo 1192413 1635509 := bbase (se 5 (by rfl) ⟨76664, by rfl⟩ : syracuseStep 1635509 = 153329) (by norm_num)
theorem B2012357 : Blo 1192413 2012357 := bbase (se 4 (by rfl) ⟨188658, by rfl⟩ : syracuseStep 2012357 = 377317) (by norm_num)
theorem B4027589 : Blo 1192413 4027589 := bbase (se 4 (by rfl) ⟨377586, by rfl⟩ : syracuseStep 4027589 = 755173) (by norm_num)
theorem B2266309 : Blo 1192413 2266309 := bbase (se 4 (by rfl) ⟨212466, by rfl⟩ : syracuseStep 2266309 = 424933) (by norm_num)
theorem B1791173 : Blo 1192413 1791173 := bbase (se 4 (by rfl) ⟨167922, by rfl⟩ : syracuseStep 1791173 = 335845) (by norm_num)
theorem B1791197 : Blo 1192413 1791197 := bbase (se 3 (by rfl) ⟨335849, by rfl⟩ : syracuseStep 1791197 = 671699) (by norm_num)
theorem B2684141 : Blo 1192413 2684141 := bbase (se 3 (by rfl) ⟨503276, by rfl⟩ : syracuseStep 2684141 = 1006553) (by norm_num)
theorem B1791221 : Blo 1192413 1791221 := bbase (se 5 (by rfl) ⟨83963, by rfl⟩ : syracuseStep 1791221 = 167927) (by norm_num)
theorem B1791245 : Blo 1192413 1791245 := bbase (se 3 (by rfl) ⟨335858, by rfl⟩ : syracuseStep 1791245 = 671717) (by norm_num)
theorem B22942997 : Blo 1192413 22942997 := bbase (se 6 (by rfl) ⟨537726, by rfl⟩ : syracuseStep 22942997 = 1075453) (by norm_num)
theorem B1791269 : Blo 1192413 1791269 := bbase (se 4 (by rfl) ⟨167931, by rfl⟩ : syracuseStep 1791269 = 335863) (by norm_num)
theorem B2684213 : Blo 1192413 2684213 := bbase (se 5 (by rfl) ⟨125822, by rfl⟩ : syracuseStep 2684213 = 251645) (by norm_num)
theorem B1791293 : Blo 1192413 1791293 := bbase (se 3 (by rfl) ⟨335867, by rfl⟩ : syracuseStep 1791293 = 671735) (by norm_num)
theorem B2012485 : Blo 1192413 2012485 := bbase (se 4 (by rfl) ⟨188670, by rfl⟩ : syracuseStep 2012485 = 377341) (by norm_num)
theorem B1791317 : Blo 1192413 1791317 := bbase (se 17 (by rfl) ⟨20, by rfl⟩ : syracuseStep 1791317 = 41) (by norm_num)
theorem B3020125 : Blo 1192413 3020125 := bbase (se 3 (by rfl) ⟨566273, by rfl⟩ : syracuseStep 3020125 = 1132547) (by norm_num)
theorem B1791341 : Blo 1192413 1791341 := bbase (se 3 (by rfl) ⟨335876, by rfl⟩ : syracuseStep 1791341 = 671753) (by norm_num)
theorem B2684285 : Blo 1192413 2684285 := bbase (se 3 (by rfl) ⟨503303, by rfl⟩ : syracuseStep 2684285 = 1006607) (by norm_num)
theorem B1275269 : Blo 1192413 1275269 := bbase (se 4 (by rfl) ⟨119556, by rfl⟩ : syracuseStep 1275269 = 239113) (by norm_num)
theorem B1791365 : Blo 1192413 1791365 := bbase (se 4 (by rfl) ⟨167940, by rfl⟩ : syracuseStep 1791365 = 335881) (by norm_num)
theorem B2151829 : Blo 1192413 2151829 := bbase (se 6 (by rfl) ⟨50433, by rfl⟩ : syracuseStep 2151829 = 100867) (by norm_num)
theorem B2012573 : Blo 1192413 2012573 := bbase (se 3 (by rfl) ⟨377357, by rfl⟩ : syracuseStep 2012573 = 754715) (by norm_num)
theorem B1791389 : Blo 1192413 1791389 := bbase (se 3 (by rfl) ⟨335885, by rfl⟩ : syracuseStep 1791389 = 671771) (by norm_num)
theorem B3823013 : Blo 1192413 3823013 := bbase (se 4 (by rfl) ⟨358407, by rfl⟩ : syracuseStep 3823013 = 716815) (by norm_num)
theorem B1791413 : Blo 1192413 1791413 := bbase (se 5 (by rfl) ⟨83972, by rfl⟩ : syracuseStep 1791413 = 167945) (by norm_num)
theorem B2684357 : Blo 1192413 2684357 := bbase (se 4 (by rfl) ⟨251658, by rfl⟩ : syracuseStep 2684357 = 503317) (by norm_num)
theorem B3020237 : Blo 1192413 3020237 := bbase (se 3 (by rfl) ⟨566294, by rfl⟩ : syracuseStep 3020237 = 1132589) (by norm_num)
theorem B1791437 : Blo 1192413 1791437 := bbase (se 3 (by rfl) ⟨335894, by rfl⟩ : syracuseStep 1791437 = 671789) (by norm_num)
theorem B1791461 : Blo 1192413 1791461 := bbase (se 4 (by rfl) ⟨167949, by rfl⟩ : syracuseStep 1791461 = 335899) (by norm_num)
theorem B2266613 : Blo 1192413 2266613 := bbase (se 5 (by rfl) ⟨106247, by rfl⟩ : syracuseStep 2266613 = 212495) (by norm_num)
theorem B1791485 : Blo 1192413 1791485 := bbase (se 3 (by rfl) ⟨335903, by rfl⟩ : syracuseStep 1791485 = 671807) (by norm_num)
theorem B2684429 : Blo 1192413 2684429 := bbase (se 3 (by rfl) ⟨503330, by rfl⟩ : syracuseStep 2684429 = 1006661) (by norm_num)
theorem B1791509 : Blo 1192413 1791509 := bbase (se 6 (by rfl) ⟨41988, by rfl⟩ : syracuseStep 1791509 = 83977) (by norm_num)
theorem B2012701 : Blo 1192413 2012701 := bbase (se 3 (by rfl) ⟨377381, by rfl⟩ : syracuseStep 2012701 = 754763) (by norm_num)
theorem B1791533 : Blo 1192413 1791533 := bbase (se 3 (by rfl) ⟨335912, by rfl⟩ : syracuseStep 1791533 = 671825) (by norm_num)
theorem B1791557 : Blo 1192413 1791557 := bbase (se 4 (by rfl) ⟨167958, by rfl⟩ : syracuseStep 1791557 = 335917) (by norm_num)
theorem B2684501 : Blo 1192413 2684501 := bbase (se 8 (by rfl) ⟨15729, by rfl⟩ : syracuseStep 2684501 = 31459) (by norm_num)
theorem B1791581 : Blo 1192413 1791581 := bbase (se 3 (by rfl) ⟨335921, by rfl⟩ : syracuseStep 1791581 = 671843) (by norm_num)
theorem B2012789 : Blo 1192413 2012789 := bbase (se 5 (by rfl) ⟨94349, by rfl⟩ : syracuseStep 2012789 = 188699) (by norm_num)
theorem B4028021 : Blo 1192413 4028021 := bbase (se 5 (by rfl) ⟨188813, by rfl⟩ : syracuseStep 4028021 = 377627) (by norm_num)
theorem B1791605 : Blo 1192413 1791605 := bbase (se 5 (by rfl) ⟨83981, by rfl⟩ : syracuseStep 1791605 = 167963) (by norm_num)
theorem B3061373 : Blo 1192413 3061373 := bbase (se 3 (by rfl) ⟨574007, by rfl⟩ : syracuseStep 3061373 = 1148015) (by norm_num)
theorem B3020429 : Blo 1192413 3020429 := bbase (se 3 (by rfl) ⟨566330, by rfl⟩ : syracuseStep 3020429 = 1132661) (by norm_num)
theorem B2684573 : Blo 1192413 2684573 := bbase (se 3 (by rfl) ⟨503357, by rfl⟩ : syracuseStep 2684573 = 1006715) (by norm_num)
theorem B2684645 : Blo 1192413 2684645 := bbase (se 4 (by rfl) ⟨251685, by rfl⟩ : syracuseStep 2684645 = 503371) (by norm_num)
theorem B2012917 : Blo 1192413 2012917 := bbase (se 5 (by rfl) ⟨94355, by rfl⟩ : syracuseStep 2012917 = 188711) (by norm_num)
theorem B2684717 : Blo 1192413 2684717 := bbase (se 3 (by rfl) ⟨503384, by rfl⟩ : syracuseStep 2684717 = 1006769) (by norm_num)
theorem B2013005 : Blo 1192413 2013005 := bbase (se 3 (by rfl) ⟨377438, by rfl⟩ : syracuseStep 2013005 = 754877) (by norm_num)
theorem B2684789 : Blo 1192413 2684789 := bbase (se 5 (by rfl) ⟨125849, by rfl⟩ : syracuseStep 2684789 = 251699) (by norm_num)
theorem B2684861 : Blo 1192413 2684861 := bbase (se 3 (by rfl) ⟨503411, by rfl⟩ : syracuseStep 2684861 = 1006823) (by norm_num)
theorem B2013133 : Blo 1192413 2013133 := bbase (se 3 (by rfl) ⟨377462, by rfl⟩ : syracuseStep 2013133 = 754925) (by norm_num)
theorem B3020773 : Blo 1192413 3020773 := bbase (se 4 (by rfl) ⟨283197, by rfl⟩ : syracuseStep 3020773 = 566395) (by norm_num)
theorem B2684933 : Blo 1192413 2684933 := bbase (se 4 (by rfl) ⟨251712, by rfl⟩ : syracuseStep 2684933 = 503425) (by norm_num)
theorem B2013221 : Blo 1192413 2013221 := bbase (se 4 (by rfl) ⟨188739, by rfl⟩ : syracuseStep 2013221 = 377479) (by norm_num)
theorem B4028453 : Blo 1192413 4028453 := bbase (se 4 (by rfl) ⟨377667, by rfl⟩ : syracuseStep 4028453 = 755335) (by norm_num)
theorem B1341481 : Blo 1192413 1341481 := bbase (se 2 (by rfl) ⟨503055, by rfl⟩ : syracuseStep 1341481 = 1006111) (by norm_num)
theorem B1341517 : Blo 1192413 1341517 := bbase (se 3 (by rfl) ⟨251534, by rfl⟩ : syracuseStep 1341517 = 503069) (by norm_num)
theorem B2685005 : Blo 1192413 2685005 := bbase (se 3 (by rfl) ⟨503438, by rfl⟩ : syracuseStep 2685005 = 1006877) (by norm_num)
theorem B3020885 : Blo 1192413 3020885 := bbase (se 8 (by rfl) ⟨17700, by rfl⟩ : syracuseStep 3020885 = 35401) (by norm_num)
theorem B6043733 : Blo 1192413 6043733 := bbase (se 8 (by rfl) ⟨35412, by rfl⟩ : syracuseStep 6043733 = 70825) (by norm_num)
theorem B3397733 : Blo 1192413 3397733 := bbase (se 4 (by rfl) ⟨318537, by rfl⟩ : syracuseStep 3397733 = 637075) (by norm_num)
theorem B1341553 : Blo 1192413 1341553 := bbase (se 2 (by rfl) ⟨503082, by rfl⟩ : syracuseStep 1341553 = 1006165) (by norm_num)
theorem B1341589 : Blo 1192413 1341589 := bbase (se 6 (by rfl) ⟨31443, by rfl⟩ : syracuseStep 1341589 = 62887) (by norm_num)
theorem B15497365 : Blo 1192413 15497365 := bbase (se 6 (by rfl) ⟨363219, by rfl⟩ : syracuseStep 15497365 = 726439) (by norm_num)
theorem B2685077 : Blo 1192413 2685077 := bbase (se 6 (by rfl) ⟨62931, by rfl⟩ : syracuseStep 2685077 = 125863) (by norm_num)
theorem B2013349 : Blo 1192413 2013349 := bbase (se 4 (by rfl) ⟨188751, by rfl⟩ : syracuseStep 2013349 = 377503) (by norm_num)
theorem B1341625 : Blo 1192413 1341625 := bbase (se 2 (by rfl) ⟨503109, by rfl⟩ : syracuseStep 1341625 = 1006219) (by norm_num)
theorem B1341661 : Blo 1192413 1341661 := bbase (se 3 (by rfl) ⟨251561, by rfl⟩ : syracuseStep 1341661 = 503123) (by norm_num)
theorem B2685149 : Blo 1192413 2685149 := bbase (se 3 (by rfl) ⟨503465, by rfl⟩ : syracuseStep 2685149 = 1006931) (by norm_num)
theorem B2267365 : Blo 1192413 2267365 := bbase (se 4 (by rfl) ⟨212565, by rfl⟩ : syracuseStep 2267365 = 425131) (by norm_num)
theorem B2013437 : Blo 1192413 2013437 := bbase (se 3 (by rfl) ⟨377519, by rfl⟩ : syracuseStep 2013437 = 755039) (by norm_num)
theorem B1341697 : Blo 1192413 1341697 := bbase (se 2 (by rfl) ⟨503136, by rfl⟩ : syracuseStep 1341697 = 1006273) (by norm_num)
theorem B3021077 : Blo 1192413 3021077 := bbase (se 6 (by rfl) ⟨70806, by rfl⟩ : syracuseStep 3021077 = 141613) (by norm_num)
theorem B1341733 : Blo 1192413 1341733 := bbase (se 4 (by rfl) ⟨125787, by rfl⟩ : syracuseStep 1341733 = 251575) (by norm_num)
theorem B2685221 : Blo 1192413 2685221 := bbase (se 4 (by rfl) ⟨251739, by rfl⟩ : syracuseStep 2685221 = 503479) (by norm_num)
theorem B5101861 : Blo 1192413 5101861 := bbase (se 4 (by rfl) ⟨478299, by rfl⟩ : syracuseStep 5101861 = 956599) (by norm_num)
theorem B1341769 : Blo 1192413 1341769 := bbase (se 2 (by rfl) ⟨503163, by rfl⟩ : syracuseStep 1341769 = 1006327) (by norm_num)
theorem B1341805 : Blo 1192413 1341805 := bbase (se 3 (by rfl) ⟨251588, by rfl⟩ : syracuseStep 1341805 = 503177) (by norm_num)
theorem B2685293 : Blo 1192413 2685293 := bbase (se 3 (by rfl) ⟨503492, by rfl⟩ : syracuseStep 2685293 = 1006985) (by norm_num)
theorem B1227125 : Blo 1192413 1227125 := bbase (se 5 (by rfl) ⟨57521, by rfl⟩ : syracuseStep 1227125 = 115043) (by norm_num)
theorem B2267509 : Blo 1192413 2267509 := bbase (se 5 (by rfl) ⟨106289, by rfl⟩ : syracuseStep 2267509 = 212579) (by norm_num)
theorem B2013565 : Blo 1192413 2013565 := bbase (se 3 (by rfl) ⟨377543, by rfl⟩ : syracuseStep 2013565 = 755087) (by norm_num)
theorem B1341841 : Blo 1192413 1341841 := bbase (se 2 (by rfl) ⟨503190, by rfl⟩ : syracuseStep 1341841 = 1006381) (by norm_num)
theorem B1227157 : Blo 1192413 1227157 := bbase (se 6 (by rfl) ⟨28761, by rfl⟩ : syracuseStep 1227157 = 57523) (by norm_num)
theorem B1341877 : Blo 1192413 1341877 := bbase (se 5 (by rfl) ⟨62900, by rfl⟩ : syracuseStep 1341877 = 125801) (by norm_num)
theorem B2685365 : Blo 1192413 2685365 := bbase (se 5 (by rfl) ⟨125876, by rfl⟩ : syracuseStep 2685365 = 251753) (by norm_num)
theorem B2013653 : Blo 1192413 2013653 := bbase (se 7 (by rfl) ⟨23597, by rfl⟩ : syracuseStep 2013653 = 47195) (by norm_num)
theorem B4028885 : Blo 1192413 4028885 := bbase (se 7 (by rfl) ⟨47213, by rfl⟩ : syracuseStep 4028885 = 94427) (by norm_num)
theorem B1341913 : Blo 1192413 1341913 := bbase (se 2 (by rfl) ⟨503217, by rfl⟩ : syracuseStep 1341913 = 1006435) (by norm_num)
theorem B3447269 : Blo 1192413 3447269 := bbase (se 4 (by rfl) ⟨323181, by rfl⟩ : syracuseStep 3447269 = 646363) (by norm_num)
theorem B1341949 : Blo 1192413 1341949 := bbase (se 3 (by rfl) ⟨251615, by rfl⟩ : syracuseStep 1341949 = 503231) (by norm_num)
theorem B2685437 : Blo 1192413 2685437 := bbase (se 3 (by rfl) ⟨503519, by rfl⟩ : syracuseStep 2685437 = 1007039) (by norm_num)
theorem B1341985 : Blo 1192413 1341985 := bbase (se 2 (by rfl) ⟨503244, by rfl⟩ : syracuseStep 1341985 = 1006489) (by norm_num)
theorem B1342021 : Blo 1192413 1342021 := bbase (se 4 (by rfl) ⟨125814, by rfl⟩ : syracuseStep 1342021 = 251629) (by norm_num)
theorem B2685509 : Blo 1192413 2685509 := bbase (se 4 (by rfl) ⟨251766, by rfl⟩ : syracuseStep 2685509 = 503533) (by norm_num)
theorem B2013781 : Blo 1192413 2013781 := bbase (se 8 (by rfl) ⟨11799, by rfl⟩ : syracuseStep 2013781 = 23599) (by norm_num)
theorem B1612381 : Blo 1192413 1612381 := bbase (se 3 (by rfl) ⟨302321, by rfl⟩ : syracuseStep 1612381 = 604643) (by norm_num)
theorem B4356709 : Blo 1192413 4356709 := bbase (se 4 (by rfl) ⟨408441, by rfl⟩ : syracuseStep 4356709 = 816883) (by norm_num)
theorem B1342057 : Blo 1192413 1342057 := bbase (se 2 (by rfl) ⟨503271, by rfl⟩ : syracuseStep 1342057 = 1006543) (by norm_num)
theorem B3021421 : Blo 1192413 3021421 := bbase (se 3 (by rfl) ⟨566516, by rfl⟩ : syracuseStep 3021421 = 1133033) (by norm_num)
theorem B1342093 : Blo 1192413 1342093 := bbase (se 3 (by rfl) ⟨251642, by rfl⟩ : syracuseStep 1342093 = 503285) (by norm_num)
theorem B2685581 : Blo 1192413 2685581 := bbase (se 3 (by rfl) ⟨503546, by rfl⟩ : syracuseStep 2685581 = 1007093) (by norm_num)
theorem B2013869 : Blo 1192413 2013869 := bbase (se 3 (by rfl) ⟨377600, by rfl⟩ : syracuseStep 2013869 = 755201) (by norm_num)
theorem B1342129 : Blo 1192413 1342129 := bbase (se 2 (by rfl) ⟨503298, by rfl⟩ : syracuseStep 1342129 = 1006597) (by norm_num)
theorem B1342165 : Blo 1192413 1342165 := bbase (se 7 (by rfl) ⟨15728, by rfl⟩ : syracuseStep 1342165 = 31457) (by norm_num)
theorem B2685653 : Blo 1192413 2685653 := bbase (se 7 (by rfl) ⟨31472, by rfl⟩ : syracuseStep 2685653 = 62945) (by norm_num)
theorem B3021533 : Blo 1192413 3021533 := bbase (se 3 (by rfl) ⟨566537, by rfl⟩ : syracuseStep 3021533 = 1133075) (by norm_num)
theorem B1342201 : Blo 1192413 1342201 := bbase (se 2 (by rfl) ⟨503325, by rfl⟩ : syracuseStep 1342201 = 1006651) (by norm_num)
theorem B1342237 : Blo 1192413 1342237 := bbase (se 3 (by rfl) ⟨251669, by rfl⟩ : syracuseStep 1342237 = 503339) (by norm_num)
theorem B2685725 : Blo 1192413 2685725 := bbase (se 3 (by rfl) ⟨503573, by rfl⟩ : syracuseStep 2685725 = 1007147) (by norm_num)
theorem B2013997 : Blo 1192413 2013997 := bbase (se 3 (by rfl) ⟨377624, by rfl⟩ : syracuseStep 2013997 = 755249) (by norm_num)
theorem B1342273 : Blo 1192413 1342273 := bbase (se 2 (by rfl) ⟨503352, by rfl⟩ : syracuseStep 1342273 = 1006705) (by norm_num)
theorem B9804629 : Blo 1192413 9804629 := bbase (se 9 (by rfl) ⟨28724, by rfl⟩ : syracuseStep 9804629 = 57449) (by norm_num)
theorem B10197845 : Blo 1192413 10197845 := bbase (se 9 (by rfl) ⟨29876, by rfl⟩ : syracuseStep 10197845 = 59753) (by norm_num)
theorem B1342309 : Blo 1192413 1342309 := bbase (se 4 (by rfl) ⟨125841, by rfl⟩ : syracuseStep 1342309 = 251683) (by norm_num)
theorem B2685797 : Blo 1192413 2685797 := bbase (se 4 (by rfl) ⟨251793, by rfl⟩ : syracuseStep 2685797 = 503587) (by norm_num)
theorem B2014085 : Blo 1192413 2014085 := bbase (se 4 (by rfl) ⟨188820, by rfl⟩ : syracuseStep 2014085 = 377641) (by norm_num)
theorem B4029317 : Blo 1192413 4029317 := bbase (se 4 (by rfl) ⟨377748, by rfl⟩ : syracuseStep 4029317 = 755497) (by norm_num)
theorem B1342345 : Blo 1192413 1342345 := bbase (se 2 (by rfl) ⟨503379, by rfl⟩ : syracuseStep 1342345 = 1006759) (by norm_num)
theorem B3021725 : Blo 1192413 3021725 := bbase (se 3 (by rfl) ⟨566573, by rfl⟩ : syracuseStep 3021725 = 1133147) (by norm_num)
theorem B1342381 : Blo 1192413 1342381 := bbase (se 3 (by rfl) ⟨251696, by rfl⟩ : syracuseStep 1342381 = 503393) (by norm_num)
theorem B2685869 : Blo 1192413 2685869 := bbase (se 3 (by rfl) ⟨503600, by rfl⟩ : syracuseStep 2685869 = 1007201) (by norm_num)
theorem B1342417 : Blo 1192413 1342417 := bbase (se 2 (by rfl) ⟨503406, by rfl⟩ : syracuseStep 1342417 = 1006813) (by norm_num)
theorem B4529141 : Blo 1192413 4529141 := bbase (se 5 (by rfl) ⟨212303, by rfl⟩ : syracuseStep 4529141 = 424607) (by norm_num)
theorem B1342453 : Blo 1192413 1342453 := bbase (se 5 (by rfl) ⟨62927, by rfl⟩ : syracuseStep 1342453 = 125855) (by norm_num)
theorem B2685941 : Blo 1192413 2685941 := bbase (se 5 (by rfl) ⟨125903, by rfl⟩ : syracuseStep 2685941 = 251807) (by norm_num)
theorem B2014213 : Blo 1192413 2014213 := bbase (se 4 (by rfl) ⟨188832, by rfl⟩ : syracuseStep 2014213 = 377665) (by norm_num)
theorem B1342489 : Blo 1192413 1342489 := bbase (se 2 (by rfl) ⟨503433, by rfl⟩ : syracuseStep 1342489 = 1006867) (by norm_num)
theorem B1342525 : Blo 1192413 1342525 := bbase (se 3 (by rfl) ⟨251723, by rfl⟩ : syracuseStep 1342525 = 503447) (by norm_num)
theorem B2686013 : Blo 1192413 2686013 := bbase (se 3 (by rfl) ⟨503627, by rfl⟩ : syracuseStep 2686013 = 1007255) (by norm_num)
theorem B1612877 : Blo 1192413 1612877 := bbase (se 3 (by rfl) ⟨302414, by rfl⟩ : syracuseStep 1612877 = 604829) (by norm_num)
theorem B2866261 : Blo 1192413 2866261 := bbase (se 8 (by rfl) ⟨16794, by rfl⟩ : syracuseStep 2866261 = 33589) (by norm_num)
theorem B2014301 : Blo 1192413 2014301 := bbase (se 3 (by rfl) ⟨377681, by rfl⟩ : syracuseStep 2014301 = 755363) (by norm_num)
theorem B1342561 : Blo 1192413 1342561 := bbase (se 2 (by rfl) ⟨503460, by rfl⟩ : syracuseStep 1342561 = 1006921) (by norm_num)
theorem B1342597 : Blo 1192413 1342597 := bbase (se 4 (by rfl) ⟨125868, by rfl⟩ : syracuseStep 1342597 = 251737) (by norm_num)
theorem B2686085 : Blo 1192413 2686085 := bbase (se 4 (by rfl) ⟨251820, by rfl⟩ : syracuseStep 2686085 = 503641) (by norm_num)
theorem B3267749 : Blo 1192413 3267749 := bbase (se 4 (by rfl) ⟨306351, by rfl⟩ : syracuseStep 3267749 = 612703) (by norm_num)
theorem B1342633 : Blo 1192413 1342633 := bbase (se 2 (by rfl) ⟨503487, by rfl⟩ : syracuseStep 1342633 = 1006975) (by norm_num)
theorem B1342669 : Blo 1192413 1342669 := bbase (se 3 (by rfl) ⟨251750, by rfl⟩ : syracuseStep 1342669 = 503501) (by norm_num)
theorem B2686157 : Blo 1192413 2686157 := bbase (se 3 (by rfl) ⟨503654, by rfl⟩ : syracuseStep 2686157 = 1007309) (by norm_num)
theorem B2014429 : Blo 1192413 2014429 := bbase (se 3 (by rfl) ⟨377705, by rfl⟩ : syracuseStep 2014429 = 755411) (by norm_num)
theorem B1342705 : Blo 1192413 1342705 := bbase (se 2 (by rfl) ⟨503514, by rfl⟩ : syracuseStep 1342705 = 1007029) (by norm_num)
theorem B3022069 : Blo 1192413 3022069 := bbase (se 5 (by rfl) ⟨141659, by rfl⟩ : syracuseStep 3022069 = 283319) (by norm_num)
theorem B3398917 : Blo 1192413 3398917 := bbase (se 4 (by rfl) ⟨318648, by rfl⟩ : syracuseStep 3398917 = 637297) (by norm_num)
theorem B4529429 : Blo 1192413 4529429 := bbase (se 6 (by rfl) ⟨106158, by rfl⟩ : syracuseStep 4529429 = 212317) (by norm_num)
theorem B1342741 : Blo 1192413 1342741 := bbase (se 6 (by rfl) ⟨31470, by rfl⟩ : syracuseStep 1342741 = 62941) (by norm_num)
theorem B2686229 : Blo 1192413 2686229 := bbase (se 6 (by rfl) ⟨62958, by rfl⟩ : syracuseStep 2686229 = 125917) (by norm_num)
theorem B2014517 : Blo 1192413 2014517 := bbase (se 5 (by rfl) ⟨94430, by rfl⟩ : syracuseStep 2014517 = 188861) (by norm_num)
theorem B4029749 : Blo 1192413 4029749 := bbase (se 5 (by rfl) ⟨188894, by rfl⟩ : syracuseStep 4029749 = 377789) (by norm_num)
theorem B1342777 : Blo 1192413 1342777 := bbase (se 2 (by rfl) ⟨503541, by rfl⟩ : syracuseStep 1342777 = 1007083) (by norm_num)
theorem B1989965 : Blo 1192413 1989965 := bbase (se 3 (by rfl) ⟨373118, by rfl⟩ : syracuseStep 1989965 = 746237) (by norm_num)
theorem B1342813 : Blo 1192413 1342813 := bbase (se 3 (by rfl) ⟨251777, by rfl⟩ : syracuseStep 1342813 = 503555) (by norm_num)
theorem B2686301 : Blo 1192413 2686301 := bbase (se 3 (by rfl) ⟨503681, by rfl⟩ : syracuseStep 2686301 = 1007363) (by norm_num)
theorem B3022181 : Blo 1192413 3022181 := bbase (se 4 (by rfl) ⟨283329, by rfl⟩ : syracuseStep 3022181 = 566659) (by norm_num)
theorem B6045029 : Blo 1192413 6045029 := bbase (se 4 (by rfl) ⟨566721, by rfl⟩ : syracuseStep 6045029 = 1133443) (by norm_num)
theorem B1342849 : Blo 1192413 1342849 := bbase (se 2 (by rfl) ⟨503568, by rfl⟩ : syracuseStep 1342849 = 1007137) (by norm_num)
theorem B3399077 : Blo 1192413 3399077 := bbase (se 4 (by rfl) ⟨318663, by rfl⟩ : syracuseStep 3399077 = 637327) (by norm_num)
theorem B1342885 : Blo 1192413 1342885 := bbase (se 4 (by rfl) ⟨125895, by rfl⟩ : syracuseStep 1342885 = 251791) (by norm_num)
theorem B2686373 : Blo 1192413 2686373 := bbase (se 4 (by rfl) ⟨251847, by rfl⟩ : syracuseStep 2686373 = 503695) (by norm_num)
theorem B2014645 : Blo 1192413 2014645 := bbase (se 5 (by rfl) ⟨94436, by rfl⟩ : syracuseStep 2014645 = 188873) (by norm_num)
theorem B1342921 : Blo 1192413 1342921 := bbase (se 2 (by rfl) ⟨503595, by rfl⟩ : syracuseStep 1342921 = 1007191) (by norm_num)
theorem B1342957 : Blo 1192413 1342957 := bbase (se 3 (by rfl) ⟨251804, by rfl⟩ : syracuseStep 1342957 = 503609) (by norm_num)
theorem B2686445 : Blo 1192413 2686445 := bbase (se 3 (by rfl) ⟨503708, by rfl⟩ : syracuseStep 2686445 = 1007417) (by norm_num)
theorem B2014733 : Blo 1192413 2014733 := bbase (se 3 (by rfl) ⟨377762, by rfl⟩ : syracuseStep 2014733 = 755525) (by norm_num)
theorem B1342993 : Blo 1192413 1342993 := bbase (se 2 (by rfl) ⟨503622, by rfl⟩ : syracuseStep 1342993 = 1007245) (by norm_num)
theorem B2178589 : Blo 1192413 2178589 := bbase (se 3 (by rfl) ⟨408485, by rfl⟩ : syracuseStep 2178589 = 816971) (by norm_num)
theorem B3022373 : Blo 1192413 3022373 := bbase (se 4 (by rfl) ⟨283347, by rfl⟩ : syracuseStep 3022373 = 566695) (by norm_num)
theorem B1343029 : Blo 1192413 1343029 := bbase (se 5 (by rfl) ⟨62954, by rfl⟩ : syracuseStep 1343029 = 125909) (by norm_num)
theorem B2686517 : Blo 1192413 2686517 := bbase (se 5 (by rfl) ⟨125930, by rfl⟩ : syracuseStep 2686517 = 251861) (by norm_num)
theorem B2760269 : Blo 1192413 2760269 := bbase (se 3 (by rfl) ⟨517550, by rfl⟩ : syracuseStep 2760269 = 1035101) (by norm_num)
theorem B1343065 : Blo 1192413 1343065 := bbase (se 2 (by rfl) ⟨503649, by rfl⟩ : syracuseStep 1343065 = 1007299) (by norm_num)
theorem B2547301 : Blo 1192413 2547301 := bbase (se 4 (by rfl) ⟨238809, by rfl⟩ : syracuseStep 2547301 = 477619) (by norm_num)
theorem B3825269 : Blo 1192413 3825269 := bbase (se 5 (by rfl) ⟨179309, by rfl⟩ : syracuseStep 3825269 = 358619) (by norm_num)
theorem B1343101 : Blo 1192413 1343101 := bbase (se 3 (by rfl) ⟨251831, by rfl⟩ : syracuseStep 1343101 = 503663) (by norm_num)
theorem B2686589 : Blo 1192413 2686589 := bbase (se 3 (by rfl) ⟨503735, by rfl⟩ : syracuseStep 2686589 = 1007471) (by norm_num)
theorem B2014861 : Blo 1192413 2014861 := bbase (se 3 (by rfl) ⟨377786, by rfl⟩ : syracuseStep 2014861 = 755573) (by norm_num)
theorem B22920853 : Blo 1192413 22920853 := bbase (se 6 (by rfl) ⟨537207, by rfl⟩ : syracuseStep 22920853 = 1074415) (by norm_num)
theorem B3399317 : Blo 1192413 3399317 := bbase (se 6 (by rfl) ⟨79671, by rfl⟩ : syracuseStep 3399317 = 159343) (by norm_num)
theorem B1343137 : Blo 1192413 1343137 := bbase (se 2 (by rfl) ⟨503676, by rfl⟩ : syracuseStep 1343137 = 1007353) (by norm_num)
theorem B3628709 : Blo 1192413 3628709 := bbase (se 4 (by rfl) ⟨340191, by rfl⟩ : syracuseStep 3628709 = 680383) (by norm_num)
theorem B2866877 : Blo 1192413 2866877 := bbase (se 3 (by rfl) ⟨537539, by rfl⟩ : syracuseStep 2866877 = 1075079) (by norm_num)
theorem B1343173 : Blo 1192413 1343173 := bbase (se 4 (by rfl) ⟨125922, by rfl⟩ : syracuseStep 1343173 = 251845) (by norm_num)
theorem B2686661 : Blo 1192413 2686661 := bbase (se 4 (by rfl) ⟨251874, by rfl⟩ : syracuseStep 2686661 = 503749) (by norm_num)
theorem B2014949 : Blo 1192413 2014949 := bbase (se 4 (by rfl) ⟨188901, by rfl⟩ : syracuseStep 2014949 = 377803) (by norm_num)
theorem B4030181 : Blo 1192413 4030181 := bbase (se 4 (by rfl) ⟨377829, by rfl⟩ : syracuseStep 4030181 = 755659) (by norm_num)
theorem B1343209 : Blo 1192413 1343209 := bbase (se 2 (by rfl) ⟨503703, by rfl⟩ : syracuseStep 1343209 = 1007407) (by norm_num)
theorem B2547445 : Blo 1192413 2547445 := bbase (se 5 (by rfl) ⟨119411, by rfl⟩ : syracuseStep 2547445 = 238823) (by norm_num)
theorem B3825397 : Blo 1192413 3825397 := bbase (se 5 (by rfl) ⟨179315, by rfl⟩ : syracuseStep 3825397 = 358631) (by norm_num)
theorem B6037253 : Blo 1192413 6037253 := bbase (se 4 (by rfl) ⟨565992, by rfl⟩ : syracuseStep 6037253 = 1131985) (by norm_num)
theorem B1343245 : Blo 1192413 1343245 := bbase (se 3 (by rfl) ⟨251858, by rfl⟩ : syracuseStep 1343245 = 503717) (by norm_num)
theorem B2686733 : Blo 1192413 2686733 := bbase (se 3 (by rfl) ⟨503762, by rfl⟩ : syracuseStep 2686733 = 1007525) (by norm_num)
theorem B4038437 : Blo 1192413 4038437 := bbase (se 4 (by rfl) ⟨378603, by rfl⟩ : syracuseStep 4038437 = 757207) (by norm_num)
theorem B1343281 : Blo 1192413 1343281 := bbase (se 2 (by rfl) ⟨503730, by rfl⟩ : syracuseStep 1343281 = 1007461) (by norm_num)
theorem B3399509 : Blo 1192413 3399509 := bbase (se 9 (by rfl) ⟨9959, by rfl⟩ : syracuseStep 3399509 = 19919) (by norm_num)
theorem B1343317 : Blo 1192413 1343317 := bbase (se 9 (by rfl) ⟨3935, by rfl⟩ : syracuseStep 1343317 = 7871) (by norm_num)
theorem B2686805 : Blo 1192413 2686805 := bbase (se 9 (by rfl) ⟨7871, by rfl⟩ : syracuseStep 2686805 = 15743) (by norm_num)
theorem B2015077 : Blo 1192413 2015077 := bbase (se 4 (by rfl) ⟨188913, by rfl⟩ : syracuseStep 2015077 = 377827) (by norm_num)
theorem B1343353 : Blo 1192413 1343353 := bbase (se 2 (by rfl) ⟨503757, by rfl⟩ : syracuseStep 1343353 = 1007515) (by norm_num)
theorem B2867069 : Blo 1192413 2867069 := bbase (se 3 (by rfl) ⟨537575, by rfl⟩ : syracuseStep 2867069 = 1075151) (by norm_num)
theorem B3022717 : Blo 1192413 3022717 := bbase (se 3 (by rfl) ⟨566759, by rfl⟩ : syracuseStep 3022717 = 1133519) (by norm_num)
theorem B1343389 : Blo 1192413 1343389 := bbase (se 3 (by rfl) ⟨251885, by rfl⟩ : syracuseStep 1343389 = 503771) (by norm_num)
theorem B2686877 : Blo 1192413 2686877 := bbase (se 3 (by rfl) ⟨503789, by rfl⟩ : syracuseStep 2686877 = 1007579) (by norm_num)
theorem B2015165 : Blo 1192413 2015165 := bbase (se 3 (by rfl) ⟨377843, by rfl⟩ : syracuseStep 2015165 = 755687) (by norm_num)
theorem B1343425 : Blo 1192413 1343425 := bbase (se 2 (by rfl) ⟨503784, by rfl⟩ : syracuseStep 1343425 = 1007569) (by norm_num)
theorem B6119381 : Blo 1192413 6119381 := bbase (se 7 (by rfl) ⟨71711, by rfl⟩ : syracuseStep 6119381 = 143423) (by norm_num)
theorem B1343461 : Blo 1192413 1343461 := bbase (se 4 (by rfl) ⟨125949, by rfl⟩ : syracuseStep 1343461 = 251899) (by norm_num)
theorem B2686949 : Blo 1192413 2686949 := bbase (se 4 (by rfl) ⟨251901, by rfl⟩ : syracuseStep 2686949 = 503803) (by norm_num)
theorem B3022829 : Blo 1192413 3022829 := bbase (se 3 (by rfl) ⟨566780, by rfl⟩ : syracuseStep 3022829 = 1133561) (by norm_num)
theorem B3825731 : Blo 1192413 3825731 := bstep (se 1 (by rfl) ⟨2869298, by rfl⟩ : syracuseStep 3825731 = 5738597) B5738597
theorem B2687057 : Blo 1192413 2687057 := bstep (se 2 (by rfl) ⟨1007646, by rfl⟩ : syracuseStep 2687057 = 2015293) B2015293
theorem B2687075 : Blo 1192413 2687075 := bstep (se 1 (by rfl) ⟨2015306, by rfl⟩ : syracuseStep 2687075 = 4030613) B4030613
theorem B1343587 : Blo 1192413 1343587 := bstep (se 1 (by rfl) ⟨1007690, by rfl⟩ : syracuseStep 1343587 = 2015381) B2015381
theorem B2015347 : Blo 1192413 2015347 := bstep (se 1 (by rfl) ⟨1511510, by rfl⟩ : syracuseStep 2015347 = 3023021) B3023021
theorem B10887365 : Blo 1192413 10887365 := bstep (se 4 (by rfl) ⟨1020690, by rfl⟩ : syracuseStep 10887365 = 2041381) B2041381
theorem B6799565 : Blo 1192413 6799565 := bstep (se 3 (by rfl) ⟨1274918, by rfl⟩ : syracuseStep 6799565 = 2549837) B2549837
theorem B2015489 : Blo 1192413 2015489 := bstep (se 2 (by rfl) ⟨755808, by rfl⟩ : syracuseStep 2015489 = 1511617) B1511617
theorem B2867491 : Blo 1192413 2867491 := bstep (se 1 (by rfl) ⟨2150618, by rfl⟩ : syracuseStep 2867491 = 4301237) B4301237
theorem B6046001 : Blo 1192413 6046001 := bstep (se 2 (by rfl) ⟨2267250, by rfl⟩ : syracuseStep 6046001 = 4534501) B4534501
theorem B3023153 : Blo 1192413 3023153 := bstep (se 2 (by rfl) ⟨1133682, by rfl⟩ : syracuseStep 3023153 = 2267365) B2267365
theorem B3023203 : Blo 1192413 3023203 := bstep (se 1 (by rfl) ⟨2267402, by rfl⟩ : syracuseStep 3023203 = 4534805) B4534805
theorem B4030829 : Blo 1192413 4030829 := bstep (se 3 (by rfl) ⟨755780, by rfl⟩ : syracuseStep 4030829 = 1511561) B1511561
theorem B2687345 : Blo 1192413 2687345 := bstep (se 2 (by rfl) ⟨1007754, by rfl⟩ : syracuseStep 2687345 = 2015509) B2015509
theorem B2687363 : Blo 1192413 2687363 := bstep (se 1 (by rfl) ⟨2015522, by rfl⟩ : syracuseStep 2687363 = 4031045) B4031045
theorem B6037901 : Blo 1192413 6037901 := bstep (se 3 (by rfl) ⟨1132106, by rfl⟩ : syracuseStep 6037901 = 2264213) B2264213
theorem B29041037 : Blo 1192413 29041037 := bstep (se 3 (by rfl) ⟨5445194, by rfl⟩ : syracuseStep 29041037 = 10890389) B10890389
theorem B7258531 : Blo 1192413 7258531 := bstep (se 1 (by rfl) ⟨5443898, by rfl⟩ : syracuseStep 7258531 = 10887797) B10887797
theorem B4030883 : Blo 1192413 4030883 := bstep (se 1 (by rfl) ⟨3023162, by rfl⟩ : syracuseStep 4030883 = 6046325) B6046325
theorem B4137443 : Blo 1192413 4137443 := bstep (se 1 (by rfl) ⟨3103082, by rfl⟩ : syracuseStep 4137443 = 6206165) B6206165
theorem B3023345 : Blo 1192413 3023345 := bstep (se 2 (by rfl) ⟨1133754, by rfl⟩ : syracuseStep 3023345 = 2267509) B2267509
theorem B10199621 : Blo 1192413 10199621 := bstep (se 4 (by rfl) ⟨956214, by rfl⟩ : syracuseStep 10199621 = 1912429) B1912429
theorem B7643747 : Blo 1192413 7643747 := bstep (se 1 (by rfl) ⟨5732810, by rfl⟩ : syracuseStep 7643747 = 11465621) B11465621
theorem B3826385 : Blo 1192413 3826385 := bstep (se 2 (by rfl) ⟨1434894, by rfl⟩ : syracuseStep 3826385 = 2869789) B2869789
theorem B17204021 : Blo 1192413 17204021 := bstep (se 5 (by rfl) ⟨806438, by rfl⟩ : syracuseStep 17204021 = 1612877) B1612877
theorem B15295331 : Blo 1192413 15295331 := bstep (se 1 (by rfl) ⟨11471498, by rfl⟩ : syracuseStep 15295331 = 22942997) B22942997
theorem B4531085 : Blo 1192413 4531085 := bstep (se 3 (by rfl) ⟨849578, by rfl⟩ : syracuseStep 4531085 = 1699157) B1699157
theorem B2548675 : Blo 1192413 2548675 := bstep (se 1 (by rfl) ⟨1911506, by rfl⟩ : syracuseStep 2548675 = 3823013) B3823013
theorem B3400717 : Blo 1192413 3400717 := bstep (se 3 (by rfl) ⟨637634, by rfl⟩ : syracuseStep 3400717 = 1275269) B1275269
theorem B2549009 : Blo 1192413 2549009 := bstep (se 2 (by rfl) ⟨955878, by rfl⟩ : syracuseStep 2549009 = 1911757) B1911757
theorem B1361395 : Blo 1192413 1361395 := bstep (se 1 (by rfl) ⟨1021046, by rfl⟩ : syracuseStep 1361395 = 2042093) B2042093
theorem B2721329 : Blo 1192413 2721329 := bstep (se 2 (by rfl) ⟨1020498, by rfl⟩ : syracuseStep 2721329 = 2040997) B2040997
theorem B1361459 : Blo 1192413 1361459 := bstep (se 1 (by rfl) ⟨1021094, by rfl⟩ : syracuseStep 1361459 = 2042189) B2042189
theorem B4081283 : Blo 1192413 4081283 := bstep (se 1 (by rfl) ⟨3060962, by rfl⟩ : syracuseStep 4081283 = 6121925) B6121925
theorem B4531889 : Blo 1192413 4531889 := bstep (se 2 (by rfl) ⟨1699458, by rfl⟩ : syracuseStep 4531889 = 3398917) B3398917
theorem B1509187 : Blo 1192413 1509187 := bstep (se 1 (by rfl) ⟨1131890, by rfl⟩ : syracuseStep 1509187 = 2263781) B2263781
theorem B2869105 : Blo 1192413 2869105 := bstep (se 2 (by rfl) ⟨1075914, by rfl⟩ : syracuseStep 2869105 = 2151829) B2151829
theorem B11470733 : Blo 1192413 11470733 := bstep (se 3 (by rfl) ⟨2150762, by rfl⟩ : syracuseStep 11470733 = 4301525) B4301525
theorem B1509283 : Blo 1192413 1509283 := bstep (se 1 (by rfl) ⟨1131962, by rfl⟩ : syracuseStep 1509283 = 2263925) B2263925
theorem B26151025 : Blo 1192413 26151025 := bstep (se 2 (by rfl) ⟨9806634, by rfl⟩ : syracuseStep 26151025 = 19613269) B19613269
theorem B4532557 : Blo 1192413 4532557 := bstep (se 3 (by rfl) ⟨849854, by rfl⟩ : syracuseStep 4532557 = 1699709) B1699709
theorem B1509779 : Blo 1192413 1509779 := bstep (se 1 (by rfl) ⟨1132334, by rfl⟩ : syracuseStep 1509779 = 2264669) B2264669
theorem B2550179 : Blo 1192413 2550179 := bstep (se 1 (by rfl) ⟨1912634, by rfl⟩ : syracuseStep 2550179 = 3825269) B3825269
theorem B2419139 : Blo 1192413 2419139 := bstep (se 1 (by rfl) ⟨1814354, by rfl⟩ : syracuseStep 2419139 = 3628709) B3628709
theorem B4024781 : Blo 1192413 4024781 := bstep (se 3 (by rfl) ⟨754646, by rfl⟩ : syracuseStep 4024781 = 1509293) B1509293
theorem B1911251 : Blo 1192413 1911251 := bstep (se 1 (by rfl) ⟨1433438, by rfl⟩ : syracuseStep 1911251 = 2866877) B2866877
theorem B4082147 : Blo 1192413 4082147 := bstep (se 1 (by rfl) ⟨3061610, by rfl⟩ : syracuseStep 4082147 = 6123221) B6123221
theorem B3631601 : Blo 1192413 3631601 := bstep (se 2 (by rfl) ⟨1361850, by rfl⟩ : syracuseStep 3631601 = 2723701) B2723701
theorem B4024835 : Blo 1192413 4024835 := bstep (se 1 (by rfl) ⟨3018626, by rfl⟩ : syracuseStep 4024835 = 6037253) B6037253
theorem B6793733 : Blo 1192413 6793733 := bstep (se 4 (by rfl) ⟨636912, by rfl⟩ : syracuseStep 6793733 = 1273825) B1273825
theorem B1698337 : Blo 1192413 1698337 := bstep (se 2 (by rfl) ⟨636876, by rfl⟩ : syracuseStep 1698337 = 1273753) B1273753
theorem B3820067 : Blo 1192413 3820067 := bstep (se 1 (by rfl) ⟨2865050, by rfl⟩ : syracuseStep 3820067 = 5730101) B5730101
theorem B1911379 : Blo 1192413 1911379 := bstep (se 1 (by rfl) ⟨1433534, by rfl⟩ : syracuseStep 1911379 = 2867069) B2867069
theorem B7269041 : Blo 1192413 7269041 := bstep (se 2 (by rfl) ⟨2725890, by rfl⟩ : syracuseStep 7269041 = 5451781) B5451781
theorem B7645873 : Blo 1192413 7645873 := bstep (se 2 (by rfl) ⟨2867202, by rfl⟩ : syracuseStep 7645873 = 5734405) B5734405
theorem B1788641 : Blo 1192413 1788641 := bstep (se 2 (by rfl) ⟨670740, by rfl⟩ : syracuseStep 1788641 = 1341481) B1341481
theorem B4303601 : Blo 1192413 4303601 := bstep (se 2 (by rfl) ⟨1613850, by rfl⟩ : syracuseStep 4303601 = 3227701) B3227701
theorem B1788659 : Blo 1192413 1788659 := bstep (se 1 (by rfl) ⟨1341494, by rfl⟩ : syracuseStep 1788659 = 2682989) B2682989
theorem B1788689 : Blo 1192413 1788689 := bstep (se 2 (by rfl) ⟨670758, by rfl⟩ : syracuseStep 1788689 = 1341517) B1341517
theorem B4025105 : Blo 1192413 4025105 := bstep (se 2 (by rfl) ⟨1509414, by rfl⟩ : syracuseStep 4025105 = 3018829) B3018829
theorem B1788707 : Blo 1192413 1788707 := bstep (se 1 (by rfl) ⟨1341530, by rfl⟩ : syracuseStep 1788707 = 2683061) B2683061
theorem B1788737 : Blo 1192413 1788737 := bstep (se 2 (by rfl) ⟨670776, by rfl⟩ : syracuseStep 1788737 = 1341553) B1341553
theorem B1788755 : Blo 1192413 1788755 := bstep (se 1 (by rfl) ⟨1341566, by rfl⟩ : syracuseStep 1788755 = 2683133) B2683133
theorem B1788785 : Blo 1192413 1788785 := bstep (se 2 (by rfl) ⟨670794, by rfl⟩ : syracuseStep 1788785 = 1341589) B1341589
theorem B1698673 : Blo 1192413 1698673 := bstep (se 2 (by rfl) ⟨637002, by rfl⟩ : syracuseStep 1698673 = 1274005) B1274005
theorem B20663153 : Blo 1192413 20663153 := bstep (se 2 (by rfl) ⟨7748682, by rfl⟩ : syracuseStep 20663153 = 15497365) B15497365
theorem B1788803 : Blo 1192413 1788803 := bstep (se 1 (by rfl) ⟨1341602, by rfl⟩ : syracuseStep 1788803 = 2683205) B2683205
theorem B1788833 : Blo 1192413 1788833 := bstep (se 2 (by rfl) ⟨670812, by rfl⟩ : syracuseStep 1788833 = 1341625) B1341625
theorem B1788851 : Blo 1192413 1788851 := bstep (se 1 (by rfl) ⟨1341638, by rfl⟩ : syracuseStep 1788851 = 2683277) B2683277
theorem B17198021 : Blo 1192413 17198021 := bstep (se 4 (by rfl) ⟨1612314, by rfl⟩ : syracuseStep 17198021 = 3224629) B3224629
theorem B6794189 : Blo 1192413 6794189 := bstep (se 3 (by rfl) ⟨1273910, by rfl⟩ : syracuseStep 6794189 = 2547821) B2547821
theorem B1788881 : Blo 1192413 1788881 := bstep (se 2 (by rfl) ⟨670830, by rfl⟩ : syracuseStep 1788881 = 1341661) B1341661
theorem B1911763 : Blo 1192413 1911763 := bstep (se 1 (by rfl) ⟨1433822, by rfl⟩ : syracuseStep 1911763 = 2867645) B2867645
theorem B1788899 : Blo 1192413 1788899 := bstep (se 1 (by rfl) ⟨1341674, by rfl⟩ : syracuseStep 1788899 = 2683349) B2683349
theorem B1788929 : Blo 1192413 1788929 := bstep (se 2 (by rfl) ⟨670848, by rfl⟩ : syracuseStep 1788929 = 1341697) B1341697
theorem B1788947 : Blo 1192413 1788947 := bstep (se 1 (by rfl) ⟨1341710, by rfl⟩ : syracuseStep 1788947 = 2683421) B2683421
theorem B2583587 : Blo 1192413 2583587 := bstep (se 1 (by rfl) ⟨1937690, by rfl⟩ : syracuseStep 2583587 = 3875381) B3875381
theorem B1788977 : Blo 1192413 1788977 := bstep (se 2 (by rfl) ⟨670866, by rfl⟩ : syracuseStep 1788977 = 1341733) B1341733
theorem B6802481 : Blo 1192413 6802481 := bstep (se 2 (by rfl) ⟨2550930, by rfl⟩ : syracuseStep 6802481 = 5101861) B5101861
theorem B18385973 : Blo 1192413 18385973 := bstep (se 5 (by rfl) ⟨861842, by rfl⟩ : syracuseStep 18385973 = 1723685) B1723685
theorem B1788995 : Blo 1192413 1788995 := bstep (se 1 (by rfl) ⟨1341746, by rfl⟩ : syracuseStep 1788995 = 2683493) B2683493
theorem B4197457 : Blo 1192413 4197457 := bstep (se 2 (by rfl) ⟨1574046, by rfl⟩ : syracuseStep 4197457 = 3148093) B3148093
theorem B1510483 : Blo 1192413 1510483 := bstep (se 1 (by rfl) ⟨1132862, by rfl⟩ : syracuseStep 1510483 = 2265725) B2265725
theorem B1789025 : Blo 1192413 1789025 := bstep (se 2 (by rfl) ⟨670884, by rfl⟩ : syracuseStep 1789025 = 1341769) B1341769
theorem B4533347 : Blo 1192413 4533347 := bstep (se 1 (by rfl) ⟨3400010, by rfl⟩ : syracuseStep 4533347 = 6800021) B6800021
theorem B1789043 : Blo 1192413 1789043 := bstep (se 1 (by rfl) ⟨1341782, by rfl⟩ : syracuseStep 1789043 = 2683565) B2683565
theorem B4361357 : Blo 1192413 4361357 := bstep (se 3 (by rfl) ⟨817754, by rfl⟩ : syracuseStep 4361357 = 1635509) B1635509
theorem B1789073 : Blo 1192413 1789073 := bstep (se 2 (by rfl) ⟨670902, by rfl⟩ : syracuseStep 1789073 = 1341805) B1341805
theorem B1789091 : Blo 1192413 1789091 := bstep (se 1 (by rfl) ⟨1341818, by rfl⟩ : syracuseStep 1789091 = 2683637) B2683637
theorem B1510579 : Blo 1192413 1510579 := bstep (se 1 (by rfl) ⟨1132934, by rfl⟩ : syracuseStep 1510579 = 2265869) B2265869
theorem B1789121 : Blo 1192413 1789121 := bstep (se 2 (by rfl) ⟨670920, by rfl⟩ : syracuseStep 1789121 = 1341841) B1341841
theorem B1936595 : Blo 1192413 1936595 := bstep (se 1 (by rfl) ⟨1452446, by rfl⟩ : syracuseStep 1936595 = 2904893) B2904893
theorem B1789139 : Blo 1192413 1789139 := bstep (se 1 (by rfl) ⟨1341854, by rfl⟩ : syracuseStep 1789139 = 2683709) B2683709
theorem B1912019 : Blo 1192413 1912019 := bstep (se 1 (by rfl) ⟨1434014, by rfl⟩ : syracuseStep 1912019 = 2868029) B2868029
theorem B1789169 : Blo 1192413 1789169 := bstep (se 2 (by rfl) ⟨670938, by rfl⟩ : syracuseStep 1789169 = 1341877) B1341877
theorem B6040817 : Blo 1192413 6040817 := bstep (se 2 (by rfl) ⟨2265306, by rfl⟩ : syracuseStep 6040817 = 4530613) B4530613
theorem B1789187 : Blo 1192413 1789187 := bstep (se 1 (by rfl) ⟨1341890, by rfl⟩ : syracuseStep 1789187 = 2683781) B2683781
theorem B1789217 : Blo 1192413 1789217 := bstep (se 2 (by rfl) ⟨670956, by rfl⟩ : syracuseStep 1789217 = 1341913) B1341913
theorem B5098787 : Blo 1192413 5098787 := bstep (se 1 (by rfl) ⟨3824090, by rfl⟩ : syracuseStep 5098787 = 7648181) B7648181
theorem B4025645 : Blo 1192413 4025645 := bstep (se 3 (by rfl) ⟨754808, by rfl⟩ : syracuseStep 4025645 = 1509617) B1509617
theorem B1789235 : Blo 1192413 1789235 := bstep (se 1 (by rfl) ⟨1341926, by rfl⟩ : syracuseStep 1789235 = 2683853) B2683853
theorem B4836685 : Blo 1192413 4836685 := bstep (se 3 (by rfl) ⟨906878, by rfl⟩ : syracuseStep 4836685 = 1813757) B1813757
theorem B6892877 : Blo 1192413 6892877 := bstep (se 3 (by rfl) ⟨1292414, by rfl⟩ : syracuseStep 6892877 = 2584829) B2584829
theorem B1789265 : Blo 1192413 1789265 := bstep (se 2 (by rfl) ⟨670974, by rfl⟩ : syracuseStep 1789265 = 1341949) B1341949
theorem B4025699 : Blo 1192413 4025699 := bstep (se 1 (by rfl) ⟨3019274, by rfl⟩ : syracuseStep 4025699 = 6038549) B6038549
theorem B1789283 : Blo 1192413 1789283 := bstep (se 1 (by rfl) ⟨1341962, by rfl⟩ : syracuseStep 1789283 = 2683925) B2683925
theorem B1789313 : Blo 1192413 1789313 := bstep (se 2 (by rfl) ⟨670992, by rfl⟩ : syracuseStep 1789313 = 1341985) B1341985
theorem B1789331 : Blo 1192413 1789331 := bstep (se 1 (by rfl) ⟨1341998, by rfl⟩ : syracuseStep 1789331 = 2683997) B2683997
theorem B1789361 : Blo 1192413 1789361 := bstep (se 2 (by rfl) ⟨671010, by rfl⟩ : syracuseStep 1789361 = 1342021) B1342021
theorem B1699265 : Blo 1192413 1699265 := bstep (se 2 (by rfl) ⟨637224, by rfl⟩ : syracuseStep 1699265 = 1274449) B1274449
theorem B1789379 : Blo 1192413 1789379 := bstep (se 1 (by rfl) ⟨1342034, by rfl⟩ : syracuseStep 1789379 = 2684069) B2684069
theorem B2149841 : Blo 1192413 2149841 := bstep (se 2 (by rfl) ⟨806190, by rfl⟩ : syracuseStep 2149841 = 1612381) B1612381
theorem B1789409 : Blo 1192413 1789409 := bstep (se 2 (by rfl) ⟨671028, by rfl⟩ : syracuseStep 1789409 = 1342057) B1342057
theorem B8170993 : Blo 1192413 8170993 := bstep (se 2 (by rfl) ⟨3064122, by rfl⟩ : syracuseStep 8170993 = 6128245) B6128245
theorem B1789427 : Blo 1192413 1789427 := bstep (se 1 (by rfl) ⟨1342070, by rfl⟩ : syracuseStep 1789427 = 2684141) B2684141
theorem B2264593 : Blo 1192413 2264593 := bstep (se 2 (by rfl) ⟨849222, by rfl⟩ : syracuseStep 2264593 = 1698445) B1698445
theorem B1789457 : Blo 1192413 1789457 := bstep (se 2 (by rfl) ⟨671046, by rfl⟩ : syracuseStep 1789457 = 1342093) B1342093
theorem B1789475 : Blo 1192413 1789475 := bstep (se 1 (by rfl) ⟨1342106, by rfl⟩ : syracuseStep 1789475 = 2684213) B2684213
theorem B1789505 : Blo 1192413 1789505 := bstep (se 2 (by rfl) ⟨671064, by rfl⟩ : syracuseStep 1789505 = 1342129) B1342129
theorem B1273411 : Blo 1192413 1273411 := bstep (se 1 (by rfl) ⟨955058, by rfl⟩ : syracuseStep 1273411 = 1910117) B1910117
theorem B1789523 : Blo 1192413 1789523 := bstep (se 1 (by rfl) ⟨1342142, by rfl⟩ : syracuseStep 1789523 = 2684285) B2684285
theorem B4025969 : Blo 1192413 4025969 := bstep (se 2 (by rfl) ⟨1509738, by rfl⟩ : syracuseStep 4025969 = 3019477) B3019477
theorem B1789553 : Blo 1192413 1789553 := bstep (se 2 (by rfl) ⟨671082, by rfl⟩ : syracuseStep 1789553 = 1342165) B1342165
theorem B1789571 : Blo 1192413 1789571 := bstep (se 1 (by rfl) ⟨1342178, by rfl⟩ : syracuseStep 1789571 = 2684357) B2684357
theorem B3272333 : Blo 1192413 3272333 := bstep (se 3 (by rfl) ⟨613562, by rfl⟩ : syracuseStep 3272333 = 1227125) B1227125
theorem B1789601 : Blo 1192413 1789601 := bstep (se 2 (by rfl) ⟨671100, by rfl⟩ : syracuseStep 1789601 = 1342201) B1342201
theorem B1912481 : Blo 1192413 1912481 := bstep (se 2 (by rfl) ⟨717180, by rfl⟩ : syracuseStep 1912481 = 1434361) B1434361
theorem B1511075 : Blo 1192413 1511075 := bstep (se 1 (by rfl) ⟨1133306, by rfl⟩ : syracuseStep 1511075 = 2266613) B2266613
theorem B2264753 : Blo 1192413 2264753 := bstep (se 2 (by rfl) ⟨849282, by rfl⟩ : syracuseStep 2264753 = 1698565) B1698565
theorem B1789619 : Blo 1192413 1789619 := bstep (se 1 (by rfl) ⟨1342214, by rfl⟩ : syracuseStep 1789619 = 2684429) B2684429
theorem B1789649 : Blo 1192413 1789649 := bstep (se 2 (by rfl) ⟨671118, by rfl⟩ : syracuseStep 1789649 = 1342237) B1342237
theorem B1789667 : Blo 1192413 1789667 := bstep (se 1 (by rfl) ⟨1342250, by rfl⟩ : syracuseStep 1789667 = 2684501) B2684501
theorem B4534001 : Blo 1192413 4534001 := bstep (se 2 (by rfl) ⟨1700250, by rfl⟩ : syracuseStep 4534001 = 3400501) B3400501
theorem B1789697 : Blo 1192413 1789697 := bstep (se 2 (by rfl) ⟨671136, by rfl⟩ : syracuseStep 1789697 = 1342273) B1342273
theorem B1912577 : Blo 1192413 1912577 := bstep (se 2 (by rfl) ⟨717216, by rfl⟩ : syracuseStep 1912577 = 1434433) B1434433
theorem B5730061 : Blo 1192413 5730061 := bstep (se 3 (by rfl) ⟨1074386, by rfl⟩ : syracuseStep 5730061 = 2148773) B2148773
theorem B1789715 : Blo 1192413 1789715 := bstep (se 1 (by rfl) ⟨1342286, by rfl⟩ : syracuseStep 1789715 = 2684573) B2684573
theorem B1912609 : Blo 1192413 1912609 := bstep (se 2 (by rfl) ⟨717228, by rfl⟩ : syracuseStep 1912609 = 1434457) B1434457
theorem B1789745 : Blo 1192413 1789745 := bstep (se 2 (by rfl) ⟨671154, by rfl⟩ : syracuseStep 1789745 = 1342309) B1342309
theorem B1789763 : Blo 1192413 1789763 := bstep (se 1 (by rfl) ⟨1342322, by rfl⟩ : syracuseStep 1789763 = 2684645) B2684645
theorem B1789793 : Blo 1192413 1789793 := bstep (se 2 (by rfl) ⟨671172, by rfl⟩ : syracuseStep 1789793 = 1342345) B1342345
theorem B1789811 : Blo 1192413 1789811 := bstep (se 1 (by rfl) ⟨1342358, by rfl⟩ : syracuseStep 1789811 = 2684717) B2684717
theorem B1789841 : Blo 1192413 1789841 := bstep (se 2 (by rfl) ⟨671190, by rfl⟩ : syracuseStep 1789841 = 1342381) B1342381
theorem B1789859 : Blo 1192413 1789859 := bstep (se 1 (by rfl) ⟨1342394, by rfl⟩ : syracuseStep 1789859 = 2684789) B2684789
theorem B1789889 : Blo 1192413 1789889 := bstep (se 2 (by rfl) ⟨671208, by rfl⟩ : syracuseStep 1789889 = 1342417) B1342417
theorem B1789907 : Blo 1192413 1789907 := bstep (se 1 (by rfl) ⟨1342430, by rfl⟩ : syracuseStep 1789907 = 2684861) B2684861
theorem B1699795 : Blo 1192413 1699795 := bstep (se 1 (by rfl) ⟨1274846, by rfl⟩ : syracuseStep 1699795 = 2549693) B2549693
theorem B1789937 : Blo 1192413 1789937 := bstep (se 2 (by rfl) ⟨671226, by rfl⟩ : syracuseStep 1789937 = 1342453) B1342453
theorem B1789955 : Blo 1192413 1789955 := bstep (se 1 (by rfl) ⟨1342466, by rfl⟩ : syracuseStep 1789955 = 2684933) B2684933
theorem B1789985 : Blo 1192413 1789985 := bstep (se 2 (by rfl) ⟨671244, by rfl⟩ : syracuseStep 1789985 = 1342489) B1342489
theorem B1790003 : Blo 1192413 1790003 := bstep (se 1 (by rfl) ⟨1342502, by rfl⟩ : syracuseStep 1790003 = 2685005) B2685005
theorem B63721525 : Blo 1192413 63721525 := bstep (se 5 (by rfl) ⟨2986946, by rfl⟩ : syracuseStep 63721525 = 5973893) B5973893
theorem B2265155 : Blo 1192413 2265155 := bstep (se 1 (by rfl) ⟨1698866, by rfl⟩ : syracuseStep 2265155 = 3397733) B3397733
theorem B1790033 : Blo 1192413 1790033 := bstep (se 2 (by rfl) ⟨671262, by rfl⟩ : syracuseStep 1790033 = 1342525) B1342525
theorem B1790051 : Blo 1192413 1790051 := bstep (se 1 (by rfl) ⟨1342538, by rfl⟩ : syracuseStep 1790051 = 2685077) B2685077
theorem B3821681 : Blo 1192413 3821681 := bstep (se 2 (by rfl) ⟨1433130, by rfl⟩ : syracuseStep 3821681 = 2866261) B2866261
theorem B1790081 : Blo 1192413 1790081 := bstep (se 2 (by rfl) ⟨671280, by rfl⟩ : syracuseStep 1790081 = 1342561) B1342561
theorem B4026509 : Blo 1192413 4026509 := bstep (se 3 (by rfl) ⟨754970, by rfl⟩ : syracuseStep 4026509 = 1509941) B1509941
theorem B2683025 : Blo 1192413 2683025 := bstep (se 2 (by rfl) ⟨1006134, by rfl⟩ : syracuseStep 2683025 = 2012269) B2012269
theorem B1790099 : Blo 1192413 1790099 := bstep (se 1 (by rfl) ⟨1342574, by rfl⟩ : syracuseStep 1790099 = 2685149) B2685149
theorem B2683043 : Blo 1192413 2683043 := bstep (se 1 (by rfl) ⟨2012282, by rfl⟩ : syracuseStep 2683043 = 4024565) B4024565
theorem B1790129 : Blo 1192413 1790129 := bstep (se 2 (by rfl) ⟨671298, by rfl⟩ : syracuseStep 1790129 = 1342597) B1342597
theorem B4026563 : Blo 1192413 4026563 := bstep (se 1 (by rfl) ⟨3019922, by rfl⟩ : syracuseStep 4026563 = 6039845) B6039845
theorem B1790147 : Blo 1192413 1790147 := bstep (se 1 (by rfl) ⟨1342610, by rfl⟩ : syracuseStep 1790147 = 2685221) B2685221
theorem B7360717 : Blo 1192413 7360717 := bstep (se 3 (by rfl) ⟨1380134, by rfl⟩ : syracuseStep 7360717 = 2760269) B2760269
theorem B1790177 : Blo 1192413 1790177 := bstep (se 2 (by rfl) ⟨671316, by rfl⟩ : syracuseStep 1790177 = 1342633) B1342633
theorem B1790195 : Blo 1192413 1790195 := bstep (se 1 (by rfl) ⟨1342646, by rfl⟩ : syracuseStep 1790195 = 2685293) B2685293
theorem B1790225 : Blo 1192413 1790225 := bstep (se 2 (by rfl) ⟨671334, by rfl⟩ : syracuseStep 1790225 = 1342669) B1342669
theorem B1790243 : Blo 1192413 1790243 := bstep (se 1 (by rfl) ⟨1342682, by rfl⟩ : syracuseStep 1790243 = 2685365) B2685365
theorem B1700131 : Blo 1192413 1700131 := bstep (se 1 (by rfl) ⟨1275098, by rfl⟩ : syracuseStep 1700131 = 2550197) B2550197
theorem B13070645 : Blo 1192413 13070645 := bstep (se 5 (by rfl) ⟨612686, by rfl⟩ : syracuseStep 13070645 = 1225373) B1225373
theorem B1790273 : Blo 1192413 1790273 := bstep (se 2 (by rfl) ⟨671352, by rfl⟩ : syracuseStep 1790273 = 1342705) B1342705
theorem B2298179 : Blo 1192413 2298179 := bstep (se 1 (by rfl) ⟨1723634, by rfl⟩ : syracuseStep 2298179 = 3447269) B3447269
theorem B8163661 : Blo 1192413 8163661 := bstep (se 3 (by rfl) ⟨1530686, by rfl⟩ : syracuseStep 8163661 = 3061373) B3061373
theorem B1790291 : Blo 1192413 1790291 := bstep (se 1 (by rfl) ⟨1342718, by rfl⟩ : syracuseStep 1790291 = 2685437) B2685437
theorem B5730659 : Blo 1192413 5730659 := bstep (se 1 (by rfl) ⟨4297994, by rfl⟩ : syracuseStep 5730659 = 8595989) B8595989
theorem B1790321 : Blo 1192413 1790321 := bstep (se 2 (by rfl) ⟨671370, by rfl⟩ : syracuseStep 1790321 = 1342741) B1342741
theorem B1790339 : Blo 1192413 1790339 := bstep (se 1 (by rfl) ⟨1342754, by rfl⟩ : syracuseStep 1790339 = 2685509) B2685509
theorem B3019153 : Blo 1192413 3019153 := bstep (se 2 (by rfl) ⟨1132182, by rfl⟩ : syracuseStep 3019153 = 2264365) B2264365
theorem B1790369 : Blo 1192413 1790369 := bstep (se 2 (by rfl) ⟨671388, by rfl⟩ : syracuseStep 1790369 = 1342777) B1342777
theorem B2683313 : Blo 1192413 2683313 := bstep (se 2 (by rfl) ⟨1006242, by rfl⟩ : syracuseStep 2683313 = 2012485) B2012485
theorem B1790387 : Blo 1192413 1790387 := bstep (se 1 (by rfl) ⟨1342790, by rfl⟩ : syracuseStep 1790387 = 2685581) B2685581
theorem B2683331 : Blo 1192413 2683331 := bstep (se 1 (by rfl) ⟨2012498, by rfl⟩ : syracuseStep 2683331 = 4024997) B4024997
theorem B4026833 : Blo 1192413 4026833 := bstep (se 2 (by rfl) ⟨1510062, by rfl⟩ : syracuseStep 4026833 = 3020125) B3020125
theorem B1790417 : Blo 1192413 1790417 := bstep (se 2 (by rfl) ⟨671406, by rfl⟩ : syracuseStep 1790417 = 1342813) B1342813
theorem B1192419 : Blo 1192413 1192419 := bstep (se 1 (by rfl) ⟨894314, by rfl⟩ : syracuseStep 1192419 = 1788629) B1788629
theorem B1790435 : Blo 1192413 1790435 := bstep (se 1 (by rfl) ⟨1342826, by rfl⟩ : syracuseStep 1790435 = 2685653) B2685653
theorem B1192435 : Blo 1192413 1192435 := bstep (se 1 (by rfl) ⟨894326, by rfl⟩ : syracuseStep 1192435 = 1788653) B1788653
theorem B1192451 : Blo 1192413 1192451 := bstep (se 1 (by rfl) ⟨894338, by rfl⟩ : syracuseStep 1192451 = 1788677) B1788677
theorem B1790465 : Blo 1192413 1790465 := bstep (se 2 (by rfl) ⟨671424, by rfl⟩ : syracuseStep 1790465 = 1342849) B1342849
theorem B1192467 : Blo 1192413 1192467 := bstep (se 1 (by rfl) ⟨894350, by rfl⟩ : syracuseStep 1192467 = 1788701) B1788701
theorem B1790483 : Blo 1192413 1790483 := bstep (se 1 (by rfl) ⟨1342862, by rfl⟩ : syracuseStep 1790483 = 2685725) B2685725
theorem B1192483 : Blo 1192413 1192483 := bstep (se 1 (by rfl) ⟨894362, by rfl⟩ : syracuseStep 1192483 = 1788725) B1788725
theorem B1790513 : Blo 1192413 1790513 := bstep (se 2 (by rfl) ⟨671442, by rfl⟩ : syracuseStep 1790513 = 1342885) B1342885
theorem B1192499 : Blo 1192413 1192499 := bstep (se 1 (by rfl) ⟨894374, by rfl⟩ : syracuseStep 1192499 = 1788749) B1788749
theorem B1192515 : Blo 1192413 1192515 := bstep (se 1 (by rfl) ⟨894386, by rfl⟩ : syracuseStep 1192515 = 1788773) B1788773
theorem B1790531 : Blo 1192413 1790531 := bstep (se 1 (by rfl) ⟨1342898, by rfl⟩ : syracuseStep 1790531 = 2685797) B2685797
theorem B1192531 : Blo 1192413 1192531 := bstep (se 1 (by rfl) ⟨894398, by rfl⟩ : syracuseStep 1192531 = 1788797) B1788797
theorem B1790561 : Blo 1192413 1790561 := bstep (se 2 (by rfl) ⟨671460, by rfl⟩ : syracuseStep 1790561 = 1342921) B1342921
theorem B1192547 : Blo 1192413 1192547 := bstep (se 1 (by rfl) ⟨894410, by rfl⟩ : syracuseStep 1192547 = 1788821) B1788821
theorem B1192563 : Blo 1192413 1192563 := bstep (se 1 (by rfl) ⟨894422, by rfl⟩ : syracuseStep 1192563 = 1788845) B1788845
theorem B1790579 : Blo 1192413 1790579 := bstep (se 1 (by rfl) ⟨1342934, by rfl⟩ : syracuseStep 1790579 = 2685869) B2685869
theorem B1192579 : Blo 1192413 1192579 := bstep (se 1 (by rfl) ⟨894434, by rfl⟩ : syracuseStep 1192579 = 1788869) B1788869
theorem B1790609 : Blo 1192413 1790609 := bstep (se 2 (by rfl) ⟨671478, by rfl⟩ : syracuseStep 1790609 = 1342957) B1342957
theorem B1192595 : Blo 1192413 1192595 := bstep (se 1 (by rfl) ⟨894446, by rfl⟩ : syracuseStep 1192595 = 1788893) B1788893
theorem B1192611 : Blo 1192413 1192611 := bstep (se 1 (by rfl) ⟨894458, by rfl⟩ : syracuseStep 1192611 = 1788917) B1788917
theorem B3019427 : Blo 1192413 3019427 := bstep (se 1 (by rfl) ⟨2264570, by rfl⟩ : syracuseStep 3019427 = 4529141) B4529141
theorem B6042275 : Blo 1192413 6042275 := bstep (se 1 (by rfl) ⟨4531706, by rfl⟩ : syracuseStep 6042275 = 9063413) B9063413
theorem B1790627 : Blo 1192413 1790627 := bstep (se 1 (by rfl) ⟨1342970, by rfl⟩ : syracuseStep 1790627 = 2685941) B2685941
theorem B1192627 : Blo 1192413 1192627 := bstep (se 1 (by rfl) ⟨894470, by rfl⟩ : syracuseStep 1192627 = 1788941) B1788941
theorem B1192643 : Blo 1192413 1192643 := bstep (se 1 (by rfl) ⟨894482, by rfl⟩ : syracuseStep 1192643 = 1788965) B1788965
theorem B1790657 : Blo 1192413 1790657 := bstep (se 2 (by rfl) ⟨671496, by rfl⟩ : syracuseStep 1790657 = 1342993) B1342993
theorem B2904785 : Blo 1192413 2904785 := bstep (se 2 (by rfl) ⟨1089294, by rfl⟩ : syracuseStep 2904785 = 2178589) B2178589
theorem B2683601 : Blo 1192413 2683601 := bstep (se 2 (by rfl) ⟨1006350, by rfl⟩ : syracuseStep 2683601 = 2012701) B2012701
theorem B1192659 : Blo 1192413 1192659 := bstep (se 1 (by rfl) ⟨894494, by rfl⟩ : syracuseStep 1192659 = 1788989) B1788989
theorem B1790675 : Blo 1192413 1790675 := bstep (se 1 (by rfl) ⟨1343006, by rfl⟩ : syracuseStep 1790675 = 2686013) B2686013
theorem B1192675 : Blo 1192413 1192675 := bstep (se 1 (by rfl) ⟨894506, by rfl⟩ : syracuseStep 1192675 = 1789013) B1789013
theorem B2683619 : Blo 1192413 2683619 := bstep (se 1 (by rfl) ⟨2012714, by rfl⟩ : syracuseStep 2683619 = 4025429) B4025429
theorem B1790705 : Blo 1192413 1790705 := bstep (se 2 (by rfl) ⟨671514, by rfl⟩ : syracuseStep 1790705 = 1343029) B1343029
theorem B1192691 : Blo 1192413 1192691 := bstep (se 1 (by rfl) ⟨894518, by rfl⟩ : syracuseStep 1192691 = 1789037) B1789037
theorem B1192707 : Blo 1192413 1192707 := bstep (se 1 (by rfl) ⟨894530, by rfl⟩ : syracuseStep 1192707 = 1789061) B1789061
theorem B1790723 : Blo 1192413 1790723 := bstep (se 1 (by rfl) ⟨1343042, by rfl⟩ : syracuseStep 1790723 = 2686085) B2686085
theorem B1192723 : Blo 1192413 1192723 := bstep (se 1 (by rfl) ⟨894542, by rfl⟩ : syracuseStep 1192723 = 1789085) B1789085
theorem B92943125 : Blo 1192413 92943125 := bstep (se 6 (by rfl) ⟨2178354, by rfl⟩ : syracuseStep 92943125 = 4356709) B4356709
theorem B1790753 : Blo 1192413 1790753 := bstep (se 2 (by rfl) ⟨671532, by rfl⟩ : syracuseStep 1790753 = 1343065) B1343065
theorem B1192739 : Blo 1192413 1192739 := bstep (se 1 (by rfl) ⟨894554, by rfl⟩ : syracuseStep 1192739 = 1789109) B1789109
theorem B3396401 : Blo 1192413 3396401 := bstep (se 2 (by rfl) ⟨1273650, by rfl⟩ : syracuseStep 3396401 = 2547301) B2547301
theorem B1192755 : Blo 1192413 1192755 := bstep (se 1 (by rfl) ⟨894566, by rfl⟩ : syracuseStep 1192755 = 1789133) B1789133
theorem B1790771 : Blo 1192413 1790771 := bstep (se 1 (by rfl) ⟨1343078, by rfl⟩ : syracuseStep 1790771 = 2686157) B2686157
theorem B1192771 : Blo 1192413 1192771 := bstep (se 1 (by rfl) ⟨894578, by rfl⟩ : syracuseStep 1192771 = 1789157) B1789157
theorem B1790801 : Blo 1192413 1790801 := bstep (se 2 (by rfl) ⟨671550, by rfl⟩ : syracuseStep 1790801 = 1343101) B1343101
theorem B1192787 : Blo 1192413 1192787 := bstep (se 1 (by rfl) ⟨894590, by rfl⟩ : syracuseStep 1192787 = 1789181) B1789181
theorem B1192803 : Blo 1192413 1192803 := bstep (se 1 (by rfl) ⟨894602, by rfl⟩ : syracuseStep 1192803 = 1789205) B1789205
theorem B3019619 : Blo 1192413 3019619 := bstep (se 1 (by rfl) ⟨2264714, by rfl⟩ : syracuseStep 3019619 = 4529429) B4529429
theorem B1790819 : Blo 1192413 1790819 := bstep (se 1 (by rfl) ⟨1343114, by rfl⟩ : syracuseStep 1790819 = 2686229) B2686229
theorem B30561137 : Blo 1192413 30561137 := bstep (se 2 (by rfl) ⟨11460426, by rfl⟩ : syracuseStep 30561137 = 22920853) B22920853
theorem B1192819 : Blo 1192413 1192819 := bstep (se 1 (by rfl) ⟨894614, by rfl⟩ : syracuseStep 1192819 = 1789229) B1789229
theorem B1790849 : Blo 1192413 1790849 := bstep (se 2 (by rfl) ⟨671568, by rfl⟩ : syracuseStep 1790849 = 1343137) B1343137
theorem B1192835 : Blo 1192413 1192835 := bstep (se 1 (by rfl) ⟨894626, by rfl⟩ : syracuseStep 1192835 = 1789253) B1789253
theorem B9065357 : Blo 1192413 9065357 := bstep (se 3 (by rfl) ⟨1699754, by rfl⟩ : syracuseStep 9065357 = 3399509) B3399509
theorem B1192851 : Blo 1192413 1192851 := bstep (se 1 (by rfl) ⟨894638, by rfl⟩ : syracuseStep 1192851 = 1789277) B1789277
theorem B1790867 : Blo 1192413 1790867 := bstep (se 1 (by rfl) ⟨1343150, by rfl⟩ : syracuseStep 1790867 = 2686301) B2686301
theorem B1192867 : Blo 1192413 1192867 := bstep (se 1 (by rfl) ⟨894650, by rfl⟩ : syracuseStep 1192867 = 1789301) B1789301
theorem B1790897 : Blo 1192413 1790897 := bstep (se 2 (by rfl) ⟨671586, by rfl⟩ : syracuseStep 1790897 = 1343173) B1343173
theorem B1192883 : Blo 1192413 1192883 := bstep (se 1 (by rfl) ⟨894662, by rfl⟩ : syracuseStep 1192883 = 1789325) B1789325
theorem B1192899 : Blo 1192413 1192899 := bstep (se 1 (by rfl) ⟨894674, by rfl⟩ : syracuseStep 1192899 = 1789349) B1789349
theorem B2266051 : Blo 1192413 2266051 := bstep (se 1 (by rfl) ⟨1699538, by rfl⟩ : syracuseStep 2266051 = 3399077) B3399077
theorem B1790915 : Blo 1192413 1790915 := bstep (se 1 (by rfl) ⟨1343186, by rfl⟩ : syracuseStep 1790915 = 2686373) B2686373
theorem B1192915 : Blo 1192413 1192915 := bstep (se 1 (by rfl) ⟨894686, by rfl⟩ : syracuseStep 1192915 = 1789373) B1789373
theorem B1790945 : Blo 1192413 1790945 := bstep (se 2 (by rfl) ⟨671604, by rfl⟩ : syracuseStep 1790945 = 1343209) B1343209
theorem B1192931 : Blo 1192413 1192931 := bstep (se 1 (by rfl) ⟨894698, by rfl⟩ : syracuseStep 1192931 = 1789397) B1789397
theorem B10761187 : Blo 1192413 10761187 := bstep (se 1 (by rfl) ⟨8070890, by rfl⟩ : syracuseStep 10761187 = 16141781) B16141781
theorem B4027373 : Blo 1192413 4027373 := bstep (se 3 (by rfl) ⟨755132, by rfl⟩ : syracuseStep 4027373 = 1510265) B1510265
theorem B3396593 : Blo 1192413 3396593 := bstep (se 2 (by rfl) ⟨1273722, by rfl⟩ : syracuseStep 3396593 = 2547445) B2547445
theorem B2683889 : Blo 1192413 2683889 := bstep (se 2 (by rfl) ⟨1006458, by rfl⟩ : syracuseStep 2683889 = 2012917) B2012917
theorem B1192947 : Blo 1192413 1192947 := bstep (se 1 (by rfl) ⟨894710, by rfl⟩ : syracuseStep 1192947 = 1789421) B1789421
theorem B1790963 : Blo 1192413 1790963 := bstep (se 1 (by rfl) ⟨1343222, by rfl⟩ : syracuseStep 1790963 = 2686445) B2686445
theorem B5100529 : Blo 1192413 5100529 := bstep (se 2 (by rfl) ⟨1912698, by rfl⟩ : syracuseStep 5100529 = 3825397) B3825397
theorem B2683907 : Blo 1192413 2683907 := bstep (se 1 (by rfl) ⟨2012930, by rfl⟩ : syracuseStep 2683907 = 4025861) B4025861
theorem B1192963 : Blo 1192413 1192963 := bstep (se 1 (by rfl) ⟨894722, by rfl⟩ : syracuseStep 1192963 = 1789445) B1789445
theorem B1790993 : Blo 1192413 1790993 := bstep (se 2 (by rfl) ⟨671622, by rfl⟩ : syracuseStep 1790993 = 1343245) B1343245
theorem B1192979 : Blo 1192413 1192979 := bstep (se 1 (by rfl) ⟨894734, by rfl⟩ : syracuseStep 1192979 = 1789469) B1789469
theorem B1192995 : Blo 1192413 1192995 := bstep (se 1 (by rfl) ⟨894746, by rfl⟩ : syracuseStep 1192995 = 1789493) B1789493
theorem B4027427 : Blo 1192413 4027427 := bstep (se 1 (by rfl) ⟨3020570, by rfl⟩ : syracuseStep 4027427 = 6041141) B6041141
theorem B1791011 : Blo 1192413 1791011 := bstep (se 1 (by rfl) ⟨1343258, by rfl⟩ : syracuseStep 1791011 = 2686517) B2686517
theorem B1193011 : Blo 1192413 1193011 := bstep (se 1 (by rfl) ⟨894758, by rfl⟩ : syracuseStep 1193011 = 1789517) B1789517
theorem B1791041 : Blo 1192413 1791041 := bstep (se 2 (by rfl) ⟨671640, by rfl⟩ : syracuseStep 1791041 = 1343281) B1343281
theorem B1193027 : Blo 1192413 1193027 := bstep (se 1 (by rfl) ⟨894770, by rfl⟩ : syracuseStep 1193027 = 1789541) B1789541
theorem B1193043 : Blo 1192413 1193043 := bstep (se 1 (by rfl) ⟨894782, by rfl⟩ : syracuseStep 1193043 = 1789565) B1789565
theorem B1791059 : Blo 1192413 1791059 := bstep (se 1 (by rfl) ⟨1343294, by rfl⟩ : syracuseStep 1791059 = 2686589) B2686589
theorem B1193059 : Blo 1192413 1193059 := bstep (se 1 (by rfl) ⟨894794, by rfl⟩ : syracuseStep 1193059 = 1789589) B1789589
theorem B2266211 : Blo 1192413 2266211 := bstep (se 1 (by rfl) ⟨1699658, by rfl⟩ : syracuseStep 2266211 = 3399317) B3399317
theorem B1791089 : Blo 1192413 1791089 := bstep (se 2 (by rfl) ⟨671658, by rfl⟩ : syracuseStep 1791089 = 1343317) B1343317
theorem B1193075 : Blo 1192413 1193075 := bstep (se 1 (by rfl) ⟨894806, by rfl⟩ : syracuseStep 1193075 = 1789613) B1789613
theorem B1193091 : Blo 1192413 1193091 := bstep (se 1 (by rfl) ⟨894818, by rfl⟩ : syracuseStep 1193091 = 1789637) B1789637
theorem B1791107 : Blo 1192413 1791107 := bstep (se 1 (by rfl) ⟨1343330, by rfl⟩ : syracuseStep 1791107 = 2686661) B2686661
theorem B1193107 : Blo 1192413 1193107 := bstep (se 1 (by rfl) ⟨894830, by rfl⟩ : syracuseStep 1193107 = 1789661) B1789661
theorem B1791137 : Blo 1192413 1791137 := bstep (se 2 (by rfl) ⟨671676, by rfl⟩ : syracuseStep 1791137 = 1343353) B1343353
theorem B2012323 : Blo 1192413 2012323 := bstep (se 1 (by rfl) ⟨1509242, by rfl⟩ : syracuseStep 2012323 = 3018485) B3018485
theorem B1193123 : Blo 1192413 1193123 := bstep (se 1 (by rfl) ⟨894842, by rfl⟩ : syracuseStep 1193123 = 1789685) B1789685
theorem B1193139 : Blo 1192413 1193139 := bstep (se 1 (by rfl) ⟨894854, by rfl⟩ : syracuseStep 1193139 = 1789709) B1789709
theorem B1791155 : Blo 1192413 1791155 := bstep (se 1 (by rfl) ⟨1343366, by rfl⟩ : syracuseStep 1791155 = 2686733) B2686733
theorem B1193155 : Blo 1192413 1193155 := bstep (se 1 (by rfl) ⟨894866, by rfl⟩ : syracuseStep 1193155 = 1789733) B1789733
theorem B2692291 : Blo 1192413 2692291 := bstep (se 1 (by rfl) ⟨2019218, by rfl⟩ : syracuseStep 2692291 = 4038437) B4038437
theorem B1791185 : Blo 1192413 1791185 := bstep (se 2 (by rfl) ⟨671694, by rfl⟩ : syracuseStep 1791185 = 1343389) B1343389
theorem B1193171 : Blo 1192413 1193171 := bstep (se 1 (by rfl) ⟨894878, by rfl⟩ : syracuseStep 1193171 = 1789757) B1789757
theorem B1193187 : Blo 1192413 1193187 := bstep (se 1 (by rfl) ⟨894890, by rfl⟩ : syracuseStep 1193187 = 1789781) B1789781
theorem B1791203 : Blo 1192413 1791203 := bstep (se 1 (by rfl) ⟨1343402, by rfl⟩ : syracuseStep 1791203 = 2686805) B2686805
theorem B1193203 : Blo 1192413 1193203 := bstep (se 1 (by rfl) ⟨894902, by rfl⟩ : syracuseStep 1193203 = 1789805) B1789805
theorem B1791233 : Blo 1192413 1791233 := bstep (se 2 (by rfl) ⟨671712, by rfl⟩ : syracuseStep 1791233 = 1343425) B1343425
theorem B1193219 : Blo 1192413 1193219 := bstep (se 1 (by rfl) ⟨894914, by rfl⟩ : syracuseStep 1193219 = 1789829) B1789829
theorem B2684177 : Blo 1192413 2684177 := bstep (se 2 (by rfl) ⟨1006566, by rfl⟩ : syracuseStep 2684177 = 2013133) B2013133
theorem B1193235 : Blo 1192413 1193235 := bstep (se 1 (by rfl) ⟨894926, by rfl⟩ : syracuseStep 1193235 = 1789853) B1789853
theorem B1791251 : Blo 1192413 1791251 := bstep (se 1 (by rfl) ⟨1343438, by rfl⟩ : syracuseStep 1791251 = 2686877) B2686877
theorem B2684195 : Blo 1192413 2684195 := bstep (se 1 (by rfl) ⟨2013146, by rfl⟩ : syracuseStep 2684195 = 4026293) B4026293
theorem B1193251 : Blo 1192413 1193251 := bstep (se 1 (by rfl) ⟨894938, by rfl⟩ : syracuseStep 1193251 = 1789877) B1789877
theorem B2012465 : Blo 1192413 2012465 := bstep (se 2 (by rfl) ⟨754674, by rfl⟩ : syracuseStep 2012465 = 1509349) B1509349
theorem B4027697 : Blo 1192413 4027697 := bstep (se 2 (by rfl) ⟨1510386, by rfl⟩ : syracuseStep 4027697 = 3020773) B3020773
theorem B1193267 : Blo 1192413 1193267 := bstep (se 1 (by rfl) ⟨894950, by rfl⟩ : syracuseStep 1193267 = 1789901) B1789901
theorem B1791281 : Blo 1192413 1791281 := bstep (se 2 (by rfl) ⟨671730, by rfl⟩ : syracuseStep 1791281 = 1343461) B1343461
theorem B1193283 : Blo 1192413 1193283 := bstep (se 1 (by rfl) ⟨894962, by rfl⟩ : syracuseStep 1193283 = 1789925) B1789925
theorem B1791299 : Blo 1192413 1791299 := bstep (se 1 (by rfl) ⟨1343474, by rfl⟩ : syracuseStep 1791299 = 2686949) B2686949
theorem B1193299 : Blo 1192413 1193299 := bstep (se 1 (by rfl) ⟨894974, by rfl⟩ : syracuseStep 1193299 = 1789949) B1789949
theorem B1791329 : Blo 1192413 1791329 := bstep (se 2 (by rfl) ⟨671748, by rfl⟩ : syracuseStep 1791329 = 1343497) B1343497
theorem B1193315 : Blo 1192413 1193315 := bstep (se 1 (by rfl) ⟨894986, by rfl⟩ : syracuseStep 1193315 = 1789973) B1789973
theorem B1193331 : Blo 1192413 1193331 := bstep (se 1 (by rfl) ⟨894998, by rfl⟩ : syracuseStep 1193331 = 1789997) B1789997
theorem B1791347 : Blo 1192413 1791347 := bstep (se 1 (by rfl) ⟨1343510, by rfl⟩ : syracuseStep 1791347 = 2687021) B2687021
theorem B1193347 : Blo 1192413 1193347 := bstep (se 1 (by rfl) ⟨895010, by rfl⟩ : syracuseStep 1193347 = 1790021) B1790021
theorem B20387213 : Blo 1192413 20387213 := bstep (se 3 (by rfl) ⟨3822602, by rfl⟩ : syracuseStep 20387213 = 7645205) B7645205
theorem B1791377 : Blo 1192413 1791377 := bstep (se 2 (by rfl) ⟨671766, by rfl⟩ : syracuseStep 1791377 = 1343533) B1343533
theorem B1193363 : Blo 1192413 1193363 := bstep (se 1 (by rfl) ⟨895022, by rfl⟩ : syracuseStep 1193363 = 1790045) B1790045
theorem B1193379 : Blo 1192413 1193379 := bstep (se 1 (by rfl) ⟨895034, by rfl⟩ : syracuseStep 1193379 = 1790069) B1790069
theorem B1791395 : Blo 1192413 1791395 := bstep (se 1 (by rfl) ⟨1343546, by rfl⟩ : syracuseStep 1791395 = 2687093) B2687093
theorem B2012593 : Blo 1192413 2012593 := bstep (se 2 (by rfl) ⟨754722, by rfl⟩ : syracuseStep 2012593 = 1509445) B1509445
theorem B3061169 : Blo 1192413 3061169 := bstep (se 2 (by rfl) ⟨1147938, by rfl⟩ : syracuseStep 3061169 = 2295877) B2295877
theorem B1193395 : Blo 1192413 1193395 := bstep (se 1 (by rfl) ⟨895046, by rfl⟩ : syracuseStep 1193395 = 1790093) B1790093
theorem B1791425 : Blo 1192413 1791425 := bstep (se 2 (by rfl) ⟨671784, by rfl⟩ : syracuseStep 1791425 = 1343569) B1343569
theorem B1193411 : Blo 1192413 1193411 := bstep (se 1 (by rfl) ⟨895058, by rfl⟩ : syracuseStep 1193411 = 1790117) B1790117
theorem B6043085 : Blo 1192413 6043085 := bstep (se 3 (by rfl) ⟨1133078, by rfl⟩ : syracuseStep 6043085 = 2266157) B2266157
theorem B2012627 : Blo 1192413 2012627 := bstep (se 1 (by rfl) ⟨1509470, by rfl⟩ : syracuseStep 2012627 = 3018941) B3018941
theorem B1193427 : Blo 1192413 1193427 := bstep (se 1 (by rfl) ⟨895070, by rfl⟩ : syracuseStep 1193427 = 1790141) B1790141
theorem B1791443 : Blo 1192413 1791443 := bstep (se 1 (by rfl) ⟨1343582, by rfl⟩ : syracuseStep 1791443 = 2687165) B2687165
theorem B1193443 : Blo 1192413 1193443 := bstep (se 1 (by rfl) ⟨895082, by rfl⟩ : syracuseStep 1193443 = 1790165) B1790165
theorem B1791473 : Blo 1192413 1791473 := bstep (se 2 (by rfl) ⟨671802, by rfl⟩ : syracuseStep 1791473 = 1343605) B1343605
theorem B1193459 : Blo 1192413 1193459 := bstep (se 1 (by rfl) ⟨895094, by rfl⟩ : syracuseStep 1193459 = 1790189) B1790189
theorem B1193475 : Blo 1192413 1193475 := bstep (se 1 (by rfl) ⟨895106, by rfl⟩ : syracuseStep 1193475 = 1790213) B1790213
theorem B1791491 : Blo 1192413 1791491 := bstep (se 1 (by rfl) ⟨1343618, by rfl⟩ : syracuseStep 1791491 = 2687237) B2687237
theorem B1193491 : Blo 1192413 1193491 := bstep (se 1 (by rfl) ⟨895118, by rfl⟩ : syracuseStep 1193491 = 1790237) B1790237
theorem B1791521 : Blo 1192413 1791521 := bstep (se 2 (by rfl) ⟨671820, by rfl⟩ : syracuseStep 1791521 = 1343641) B1343641
theorem B1193507 : Blo 1192413 1193507 := bstep (se 1 (by rfl) ⟨895130, by rfl⟩ : syracuseStep 1193507 = 1790261) B1790261
theorem B2684465 : Blo 1192413 2684465 := bstep (se 2 (by rfl) ⟨1006674, by rfl⟩ : syracuseStep 2684465 = 2013349) B2013349
theorem B1193523 : Blo 1192413 1193523 := bstep (se 1 (by rfl) ⟨895142, by rfl⟩ : syracuseStep 1193523 = 1790285) B1790285
theorem B1791539 : Blo 1192413 1791539 := bstep (se 1 (by rfl) ⟨1343654, by rfl⟩ : syracuseStep 1791539 = 2687309) B2687309
theorem B2684483 : Blo 1192413 2684483 := bstep (se 1 (by rfl) ⟨2013362, by rfl⟩ : syracuseStep 2684483 = 4026725) B4026725
theorem B1193539 : Blo 1192413 1193539 := bstep (se 1 (by rfl) ⟨895154, by rfl⟩ : syracuseStep 1193539 = 1790309) B1790309
theorem B2152003 : Blo 1192413 2152003 := bstep (se 1 (by rfl) ⟨1614002, by rfl⟩ : syracuseStep 2152003 = 3228005) B3228005
theorem B1791569 : Blo 1192413 1791569 := bstep (se 2 (by rfl) ⟨671838, by rfl⟩ : syracuseStep 1791569 = 1343677) B1343677
theorem B2012755 : Blo 1192413 2012755 := bstep (se 1 (by rfl) ⟨1509566, by rfl⟩ : syracuseStep 2012755 = 3019133) B3019133
theorem B1193555 : Blo 1192413 1193555 := bstep (se 1 (by rfl) ⟨895166, by rfl⟩ : syracuseStep 1193555 = 1790333) B1790333
theorem B1193571 : Blo 1192413 1193571 := bstep (se 1 (by rfl) ⟨895178, by rfl⟩ : syracuseStep 1193571 = 1790357) B1790357
theorem B1791587 : Blo 1192413 1791587 := bstep (se 1 (by rfl) ⟨1343690, by rfl⟩ : syracuseStep 1791587 = 2687381) B2687381
theorem B1193587 : Blo 1192413 1193587 := bstep (se 1 (by rfl) ⟨895190, by rfl⟩ : syracuseStep 1193587 = 1790381) B1790381
theorem B1791617 : Blo 1192413 1791617 := bstep (se 2 (by rfl) ⟨671856, by rfl⟩ : syracuseStep 1791617 = 1343713) B1343713
theorem B3626627 : Blo 1192413 3626627 := bstep (se 1 (by rfl) ⟨2719970, by rfl⟩ : syracuseStep 3626627 = 5439941) B5439941
theorem B1193603 : Blo 1192413 1193603 := bstep (se 1 (by rfl) ⟨895202, by rfl⟩ : syracuseStep 1193603 = 1790405) B1790405
theorem B1193619 : Blo 1192413 1193619 := bstep (se 1 (by rfl) ⟨895214, by rfl⟩ : syracuseStep 1193619 = 1790429) B1790429
theorem B1193635 : Blo 1192413 1193635 := bstep (se 1 (by rfl) ⟨895226, by rfl⟩ : syracuseStep 1193635 = 1790453) B1790453
theorem B1193651 : Blo 1192413 1193651 := bstep (se 1 (by rfl) ⟨895238, by rfl⟩ : syracuseStep 1193651 = 1790477) B1790477
theorem B1193667 : Blo 1192413 1193667 := bstep (se 1 (by rfl) ⟨895250, by rfl⟩ : syracuseStep 1193667 = 1790501) B1790501
theorem B1193683 : Blo 1192413 1193683 := bstep (se 1 (by rfl) ⟨895262, by rfl⟩ : syracuseStep 1193683 = 1790525) B1790525
theorem B2012897 : Blo 1192413 2012897 := bstep (se 2 (by rfl) ⟨754836, by rfl⟩ : syracuseStep 2012897 = 1509673) B1509673
theorem B1193699 : Blo 1192413 1193699 := bstep (se 1 (by rfl) ⟨895274, by rfl⟩ : syracuseStep 1193699 = 1790549) B1790549
theorem B1193715 : Blo 1192413 1193715 := bstep (se 1 (by rfl) ⟨895286, by rfl⟩ : syracuseStep 1193715 = 1790573) B1790573
theorem B1193731 : Blo 1192413 1193731 := bstep (se 1 (by rfl) ⟨895298, by rfl⟩ : syracuseStep 1193731 = 1790597) B1790597
theorem B3020561 : Blo 1192413 3020561 := bstep (se 2 (by rfl) ⟨1132710, by rfl⟩ : syracuseStep 3020561 = 2265421) B2265421
theorem B1193747 : Blo 1192413 1193747 := bstep (se 1 (by rfl) ⟨895310, by rfl⟩ : syracuseStep 1193747 = 1790621) B1790621
theorem B1193763 : Blo 1192413 1193763 := bstep (se 1 (by rfl) ⟨895322, by rfl⟩ : syracuseStep 1193763 = 1790645) B1790645
theorem B6797105 : Blo 1192413 6797105 := bstep (se 2 (by rfl) ⟨2548914, by rfl⟩ : syracuseStep 6797105 = 5097829) B5097829
theorem B1193779 : Blo 1192413 1193779 := bstep (se 1 (by rfl) ⟨895334, by rfl⟩ : syracuseStep 1193779 = 1790669) B1790669
theorem B3020611 : Blo 1192413 3020611 := bstep (se 1 (by rfl) ⟨2265458, by rfl⟩ : syracuseStep 3020611 = 4530917) B4530917
theorem B1193795 : Blo 1192413 1193795 := bstep (se 1 (by rfl) ⟨895346, by rfl⟩ : syracuseStep 1193795 = 1790693) B1790693
theorem B4028237 : Blo 1192413 4028237 := bstep (se 3 (by rfl) ⟨755294, by rfl⟩ : syracuseStep 4028237 = 1510589) B1510589
theorem B2684753 : Blo 1192413 2684753 := bstep (se 2 (by rfl) ⟨1006782, by rfl⟩ : syracuseStep 2684753 = 2013565) B2013565
theorem B1193811 : Blo 1192413 1193811 := bstep (se 1 (by rfl) ⟨895358, by rfl⟩ : syracuseStep 1193811 = 1790717) B1790717
theorem B2013025 : Blo 1192413 2013025 := bstep (se 2 (by rfl) ⟨754884, by rfl⟩ : syracuseStep 2013025 = 1509769) B1509769
theorem B4527971 : Blo 1192413 4527971 := bstep (se 1 (by rfl) ⟨3395978, by rfl⟩ : syracuseStep 4527971 = 6791957) B6791957
theorem B2684771 : Blo 1192413 2684771 := bstep (se 1 (by rfl) ⟨2013578, by rfl⟩ : syracuseStep 2684771 = 4027157) B4027157
theorem B1193827 : Blo 1192413 1193827 := bstep (se 1 (by rfl) ⟨895370, by rfl⟩ : syracuseStep 1193827 = 1790741) B1790741
theorem B2152291 : Blo 1192413 2152291 := bstep (se 1 (by rfl) ⟨1614218, by rfl⟩ : syracuseStep 2152291 = 3228437) B3228437
theorem B1193843 : Blo 1192413 1193843 := bstep (se 1 (by rfl) ⟨895382, by rfl⟩ : syracuseStep 1193843 = 1790765) B1790765
theorem B2013059 : Blo 1192413 2013059 := bstep (se 1 (by rfl) ⟨1509794, by rfl⟩ : syracuseStep 2013059 = 3019589) B3019589
theorem B4028291 : Blo 1192413 4028291 := bstep (se 1 (by rfl) ⟨3021218, by rfl⟩ : syracuseStep 4028291 = 6042437) B6042437
theorem B1193859 : Blo 1192413 1193859 := bstep (se 1 (by rfl) ⟨895394, by rfl⟩ : syracuseStep 1193859 = 1790789) B1790789
theorem B1611667 : Blo 1192413 1611667 := bstep (se 1 (by rfl) ⟨1208750, by rfl⟩ : syracuseStep 1611667 = 2417501) B2417501
theorem B1193875 : Blo 1192413 1193875 := bstep (se 1 (by rfl) ⟨895406, by rfl⟩ : syracuseStep 1193875 = 1790813) B1790813
theorem B1193891 : Blo 1192413 1193891 := bstep (se 1 (by rfl) ⟨895418, by rfl⟩ : syracuseStep 1193891 = 1790837) B1790837
theorem B1193907 : Blo 1192413 1193907 := bstep (se 1 (by rfl) ⟨895430, by rfl⟩ : syracuseStep 1193907 = 1790861) B1790861
theorem B1193923 : Blo 1192413 1193923 := bstep (se 1 (by rfl) ⟨895442, by rfl⟩ : syracuseStep 1193923 = 1790885) B1790885
theorem B1210307 : Blo 1192413 1210307 := bstep (se 1 (by rfl) ⟨907730, by rfl⟩ : syracuseStep 1210307 = 1815461) B1815461
theorem B3397585 : Blo 1192413 3397585 := bstep (se 2 (by rfl) ⟨1274094, by rfl⟩ : syracuseStep 3397585 = 2548189) B2548189
theorem B3020753 : Blo 1192413 3020753 := bstep (se 2 (by rfl) ⟨1132782, by rfl⟩ : syracuseStep 3020753 = 2265565) B2265565
theorem B1193939 : Blo 1192413 1193939 := bstep (se 1 (by rfl) ⟨895454, by rfl⟩ : syracuseStep 1193939 = 1790909) B1790909
theorem B1193955 : Blo 1192413 1193955 := bstep (se 1 (by rfl) ⟨895466, by rfl⟩ : syracuseStep 1193955 = 1790933) B1790933
theorem B1193971 : Blo 1192413 1193971 := bstep (se 1 (by rfl) ⟨895478, by rfl⟩ : syracuseStep 1193971 = 1790957) B1790957
theorem B2013187 : Blo 1192413 2013187 := bstep (se 1 (by rfl) ⟨1509890, by rfl⟩ : syracuseStep 2013187 = 3019781) B3019781
theorem B1193987 : Blo 1192413 1193987 := bstep (se 1 (by rfl) ⟨895490, by rfl⟩ : syracuseStep 1193987 = 1790981) B1790981
theorem B1194003 : Blo 1192413 1194003 := bstep (se 1 (by rfl) ⟨895502, by rfl⟩ : syracuseStep 1194003 = 1791005) B1791005
theorem B6453283 : Blo 1192413 6453283 := bstep (se 1 (by rfl) ⟨4839962, by rfl⟩ : syracuseStep 6453283 = 9679925) B9679925
theorem B1194019 : Blo 1192413 1194019 := bstep (se 1 (by rfl) ⟨895514, by rfl⟩ : syracuseStep 1194019 = 1791029) B1791029
theorem B1194035 : Blo 1192413 1194035 := bstep (se 1 (by rfl) ⟨895526, by rfl⟩ : syracuseStep 1194035 = 1791053) B1791053
theorem B1194051 : Blo 1192413 1194051 := bstep (se 1 (by rfl) ⟨895538, by rfl⟩ : syracuseStep 1194051 = 1791077) B1791077
theorem B1194067 : Blo 1192413 1194067 := bstep (se 1 (by rfl) ⟨895550, by rfl⟩ : syracuseStep 1194067 = 1791101) B1791101
theorem B1194083 : Blo 1192413 1194083 := bstep (se 1 (by rfl) ⟨895562, by rfl⟩ : syracuseStep 1194083 = 1791125) B1791125
theorem B2685041 : Blo 1192413 2685041 := bstep (se 2 (by rfl) ⟨1006890, by rfl⟩ : syracuseStep 2685041 = 2013781) B2013781
theorem B1194099 : Blo 1192413 1194099 := bstep (se 1 (by rfl) ⟨895574, by rfl⟩ : syracuseStep 1194099 = 1791149) B1791149
theorem B1341571 : Blo 1192413 1341571 := bstep (se 1 (by rfl) ⟨1006178, by rfl⟩ : syracuseStep 1341571 = 2012357) B2012357
theorem B2685059 : Blo 1192413 2685059 := bstep (se 1 (by rfl) ⟨2013794, by rfl⟩ : syracuseStep 2685059 = 4027589) B4027589
theorem B1194115 : Blo 1192413 1194115 := bstep (se 1 (by rfl) ⟨895586, by rfl⟩ : syracuseStep 1194115 = 1791173) B1791173
theorem B3823757 : Blo 1192413 3823757 := bstep (se 3 (by rfl) ⟨716954, by rfl⟩ : syracuseStep 3823757 = 1433909) B1433909
theorem B2013329 : Blo 1192413 2013329 := bstep (se 2 (by rfl) ⟨754998, by rfl⟩ : syracuseStep 2013329 = 1509997) B1509997
theorem B4028561 : Blo 1192413 4028561 := bstep (se 2 (by rfl) ⟨1510710, by rfl⟩ : syracuseStep 4028561 = 3021421) B3021421
theorem B1194131 : Blo 1192413 1194131 := bstep (se 1 (by rfl) ⟨895598, by rfl⟩ : syracuseStep 1194131 = 1791197) B1791197
theorem B2267281 : Blo 1192413 2267281 := bstep (se 2 (by rfl) ⟨850230, by rfl⟩ : syracuseStep 2267281 = 1700461) B1700461
theorem B1611937 : Blo 1192413 1611937 := bstep (se 2 (by rfl) ⟨604476, by rfl⟩ : syracuseStep 1611937 = 1208953) B1208953
theorem B1194147 : Blo 1192413 1194147 := bstep (se 1 (by rfl) ⟨895610, by rfl⟩ : syracuseStep 1194147 = 1791221) B1791221
theorem B1194163 : Blo 1192413 1194163 := bstep (se 1 (by rfl) ⟨895622, by rfl⟩ : syracuseStep 1194163 = 1791245) B1791245
theorem B1194179 : Blo 1192413 1194179 := bstep (se 1 (by rfl) ⟨895634, by rfl⟩ : syracuseStep 1194179 = 1791269) B1791269
theorem B5306573 : Blo 1192413 5306573 := bstep (se 3 (by rfl) ⟨994982, by rfl⟩ : syracuseStep 5306573 = 1989965) B1989965
theorem B1194195 : Blo 1192413 1194195 := bstep (se 1 (by rfl) ⟨895646, by rfl⟩ : syracuseStep 1194195 = 1791293) B1791293
theorem B3397859 : Blo 1192413 3397859 := bstep (se 1 (by rfl) ⟨2548394, by rfl⟩ : syracuseStep 3397859 = 5096789) B5096789
theorem B1194211 : Blo 1192413 1194211 := bstep (se 1 (by rfl) ⟨895658, by rfl⟩ : syracuseStep 1194211 = 1791317) B1791317
theorem B1194227 : Blo 1192413 1194227 := bstep (se 1 (by rfl) ⟨895670, by rfl⟩ : syracuseStep 1194227 = 1791341) B1791341
theorem B1194243 : Blo 1192413 1194243 := bstep (se 1 (by rfl) ⟨895682, by rfl⟩ : syracuseStep 1194243 = 1791365) B1791365
theorem B2013457 : Blo 1192413 2013457 := bstep (se 2 (by rfl) ⟨755046, by rfl⟩ : syracuseStep 2013457 = 1510093) B1510093
theorem B1341715 : Blo 1192413 1341715 := bstep (se 1 (by rfl) ⟨1006286, by rfl⟩ : syracuseStep 1341715 = 2012573) B2012573
theorem B1194259 : Blo 1192413 1194259 := bstep (se 1 (by rfl) ⟨895694, by rfl⟩ : syracuseStep 1194259 = 1791389) B1791389
theorem B1612067 : Blo 1192413 1612067 := bstep (se 1 (by rfl) ⟨1209050, by rfl⟩ : syracuseStep 1612067 = 2418101) B2418101
theorem B1194275 : Blo 1192413 1194275 := bstep (se 1 (by rfl) ⟨895706, by rfl⟩ : syracuseStep 1194275 = 1791413) B1791413
theorem B2013491 : Blo 1192413 2013491 := bstep (se 1 (by rfl) ⟨1510118, by rfl⟩ : syracuseStep 2013491 = 3020237) B3020237
theorem B1194291 : Blo 1192413 1194291 := bstep (se 1 (by rfl) ⟨895718, by rfl⟩ : syracuseStep 1194291 = 1791437) B1791437
theorem B1194307 : Blo 1192413 1194307 := bstep (se 1 (by rfl) ⟨895730, by rfl⟩ : syracuseStep 1194307 = 1791461) B1791461
theorem B1194323 : Blo 1192413 1194323 := bstep (se 1 (by rfl) ⟨895742, by rfl⟩ : syracuseStep 1194323 = 1791485) B1791485
theorem B1194339 : Blo 1192413 1194339 := bstep (se 1 (by rfl) ⟨895754, by rfl⟩ : syracuseStep 1194339 = 1791509) B1791509
theorem B7756145 : Blo 1192413 7756145 := bstep (se 2 (by rfl) ⟨2908554, by rfl⟩ : syracuseStep 7756145 = 5817109) B5817109
theorem B1194355 : Blo 1192413 1194355 := bstep (se 1 (by rfl) ⟨895766, by rfl⟩ : syracuseStep 1194355 = 1791533) B1791533
theorem B1194371 : Blo 1192413 1194371 := bstep (se 1 (by rfl) ⟨895778, by rfl⟩ : syracuseStep 1194371 = 1791557) B1791557
theorem B11622797 : Blo 1192413 11622797 := bstep (se 3 (by rfl) ⟨2179274, by rfl⟩ : syracuseStep 11622797 = 4358549) B4358549
theorem B2685329 : Blo 1192413 2685329 := bstep (se 2 (by rfl) ⟨1006998, by rfl⟩ : syracuseStep 2685329 = 2013997) B2013997
theorem B1194387 : Blo 1192413 1194387 := bstep (se 1 (by rfl) ⟨895790, by rfl⟩ : syracuseStep 1194387 = 1791581) B1791581
theorem B1341859 : Blo 1192413 1341859 := bstep (se 1 (by rfl) ⟨1006394, by rfl⟩ : syracuseStep 1341859 = 2012789) B2012789
theorem B3398051 : Blo 1192413 3398051 := bstep (se 1 (by rfl) ⟨2548538, by rfl⟩ : syracuseStep 3398051 = 5097077) B5097077
theorem B2685347 : Blo 1192413 2685347 := bstep (se 1 (by rfl) ⟨2014010, by rfl⟩ : syracuseStep 2685347 = 4028021) B4028021
theorem B1194403 : Blo 1192413 1194403 := bstep (se 1 (by rfl) ⟨895802, by rfl⟩ : syracuseStep 1194403 = 1791605) B1791605
theorem B2013619 : Blo 1192413 2013619 := bstep (se 1 (by rfl) ⟨1510214, by rfl⟩ : syracuseStep 2013619 = 3020429) B3020429
theorem B1342003 : Blo 1192413 1342003 := bstep (se 1 (by rfl) ⟨1006502, by rfl⟩ : syracuseStep 1342003 = 2013005) B2013005
theorem B2013761 : Blo 1192413 2013761 := bstep (se 2 (by rfl) ⟨755160, by rfl⟩ : syracuseStep 2013761 = 1510321) B1510321
theorem B4029101 : Blo 1192413 4029101 := bstep (se 3 (by rfl) ⟨755456, by rfl⟩ : syracuseStep 4029101 = 1510913) B1510913
theorem B2685617 : Blo 1192413 2685617 := bstep (se 2 (by rfl) ⟨1007106, by rfl⟩ : syracuseStep 2685617 = 2014213) B2014213
theorem B2013889 : Blo 1192413 2013889 := bstep (se 2 (by rfl) ⟨755208, by rfl⟩ : syracuseStep 2013889 = 1510417) B1510417
theorem B1342147 : Blo 1192413 1342147 := bstep (se 1 (by rfl) ⟨1006610, by rfl⟩ : syracuseStep 1342147 = 2013221) B2013221
theorem B2685635 : Blo 1192413 2685635 := bstep (se 1 (by rfl) ⟨2014226, by rfl⟩ : syracuseStep 2685635 = 4028453) B4028453
theorem B2013923 : Blo 1192413 2013923 := bstep (se 1 (by rfl) ⟨1510442, by rfl⟩ : syracuseStep 2013923 = 3020885) B3020885
theorem B4029155 : Blo 1192413 4029155 := bstep (se 1 (by rfl) ⟨3021866, by rfl⟩ : syracuseStep 4029155 = 6043733) B6043733
theorem B1612531 : Blo 1192413 1612531 := bstep (se 1 (by rfl) ⟨1209398, by rfl⟩ : syracuseStep 1612531 = 2418797) B2418797
theorem B4528973 : Blo 1192413 4528973 := bstep (se 3 (by rfl) ⟨849182, by rfl⟩ : syracuseStep 4528973 = 1698365) B1698365
theorem B1342291 : Blo 1192413 1342291 := bstep (se 1 (by rfl) ⟨1006718, by rfl⟩ : syracuseStep 1342291 = 2013437) B2013437
theorem B2014051 : Blo 1192413 2014051 := bstep (se 1 (by rfl) ⟨1510538, by rfl⟩ : syracuseStep 2014051 = 3021077) B3021077
theorem B3021745 : Blo 1192413 3021745 := bstep (se 2 (by rfl) ⟨1133154, by rfl⟩ : syracuseStep 3021745 = 2266309) B2266309
theorem B2685905 : Blo 1192413 2685905 := bstep (se 2 (by rfl) ⟨1007214, by rfl⟩ : syracuseStep 2685905 = 2014429) B2014429
theorem B1342435 : Blo 1192413 1342435 := bstep (se 1 (by rfl) ⟨1006826, by rfl⟩ : syracuseStep 1342435 = 2013653) B2013653
theorem B2685923 : Blo 1192413 2685923 := bstep (se 1 (by rfl) ⟨2014442, by rfl⟩ : syracuseStep 2685923 = 4028885) B4028885
theorem B2014193 : Blo 1192413 2014193 := bstep (se 2 (by rfl) ⟨755322, by rfl⟩ : syracuseStep 2014193 = 1510645) B1510645
theorem B4029425 : Blo 1192413 4029425 := bstep (se 2 (by rfl) ⟨1511034, by rfl⟩ : syracuseStep 4029425 = 3022069) B3022069
theorem B5094413 : Blo 1192413 5094413 := bstep (se 3 (by rfl) ⟨955202, by rfl⟩ : syracuseStep 5094413 = 1910405) B1910405
theorem B3824653 : Blo 1192413 3824653 := bstep (se 3 (by rfl) ⟨717122, by rfl⟩ : syracuseStep 3824653 = 1434245) B1434245
theorem B3226705 : Blo 1192413 3226705 := bstep (se 2 (by rfl) ⟨1210014, by rfl⟩ : syracuseStep 3226705 = 2420029) B2420029
theorem B2014321 : Blo 1192413 2014321 := bstep (se 2 (by rfl) ⟨755370, by rfl⟩ : syracuseStep 2014321 = 1510741) B1510741
theorem B1342579 : Blo 1192413 1342579 := bstep (se 1 (by rfl) ⟨1006934, by rfl⟩ : syracuseStep 1342579 = 2013869) B2013869
theorem B2014355 : Blo 1192413 2014355 := bstep (se 1 (by rfl) ⟨1510766, by rfl⟩ : syracuseStep 2014355 = 3021533) B3021533
theorem B3022019 : Blo 1192413 3022019 := bstep (se 1 (by rfl) ⟨2266514, by rfl⟩ : syracuseStep 3022019 = 4533029) B4533029
theorem B9059525 : Blo 1192413 9059525 := bstep (se 4 (by rfl) ⟨849330, by rfl⟩ : syracuseStep 9059525 = 1698661) B1698661
theorem B3398861 : Blo 1192413 3398861 := bstep (se 3 (by rfl) ⟨637286, by rfl⟩ : syracuseStep 3398861 = 1274573) B1274573
theorem B6536419 : Blo 1192413 6536419 := bstep (se 1 (by rfl) ⟨4902314, by rfl⟩ : syracuseStep 6536419 = 9804629) B9804629
theorem B6798563 : Blo 1192413 6798563 := bstep (se 1 (by rfl) ⟨5098922, by rfl⟩ : syracuseStep 6798563 = 10197845) B10197845
theorem B2686193 : Blo 1192413 2686193 := bstep (se 2 (by rfl) ⟨1007322, by rfl⟩ : syracuseStep 2686193 = 2014645) B2014645
theorem B1342723 : Blo 1192413 1342723 := bstep (se 1 (by rfl) ⟨1007042, by rfl⟩ : syracuseStep 1342723 = 2014085) B2014085
theorem B2686211 : Blo 1192413 2686211 := bstep (se 1 (by rfl) ⟨2014658, by rfl⟩ : syracuseStep 2686211 = 4029317) B4029317
theorem B2014483 : Blo 1192413 2014483 := bstep (se 1 (by rfl) ⟨1510862, by rfl⟩ : syracuseStep 2014483 = 3021725) B3021725
theorem B6446405 : Blo 1192413 6446405 := bstep (se 4 (by rfl) ⟨604350, by rfl⟩ : syracuseStep 6446405 = 1208701) B1208701
theorem B3399043 : Blo 1192413 3399043 := bstep (se 1 (by rfl) ⟨2549282, by rfl⟩ : syracuseStep 3399043 = 5098565) B5098565
theorem B3022211 : Blo 1192413 3022211 := bstep (se 1 (by rfl) ⟨2266658, by rfl⟩ : syracuseStep 3022211 = 4533317) B4533317
theorem B1342867 : Blo 1192413 1342867 := bstep (se 1 (by rfl) ⟨1007150, by rfl⟩ : syracuseStep 1342867 = 2014301) B2014301
theorem B2014625 : Blo 1192413 2014625 := bstep (se 2 (by rfl) ⟨755484, by rfl⟩ : syracuseStep 2014625 = 1510969) B1510969
theorem B2547121 : Blo 1192413 2547121 := bstep (se 2 (by rfl) ⟨955170, by rfl⟩ : syracuseStep 2547121 = 1910341) B1910341
theorem B2178499 : Blo 1192413 2178499 := bstep (se 1 (by rfl) ⟨1633874, by rfl⟩ : syracuseStep 2178499 = 3267749) B3267749
theorem B6544837 : Blo 1192413 6544837 := bstep (se 4 (by rfl) ⟨613578, by rfl⟩ : syracuseStep 6544837 = 1227157) B1227157
theorem B4029965 : Blo 1192413 4029965 := bstep (se 3 (by rfl) ⟨755618, by rfl⟩ : syracuseStep 4029965 = 1511237) B1511237
theorem B2686481 : Blo 1192413 2686481 := bstep (se 2 (by rfl) ⟨1007430, by rfl⟩ : syracuseStep 2686481 = 2014861) B2014861
theorem B2014753 : Blo 1192413 2014753 := bstep (se 2 (by rfl) ⟨755532, by rfl⟩ : syracuseStep 2014753 = 1511065) B1511065
theorem B1343011 : Blo 1192413 1343011 := bstep (se 1 (by rfl) ⟨1007258, by rfl⟩ : syracuseStep 1343011 = 2014517) B2014517
theorem B2686499 : Blo 1192413 2686499 := bstep (se 1 (by rfl) ⟨2014874, by rfl⟩ : syracuseStep 2686499 = 4029749) B4029749
theorem B2014787 : Blo 1192413 2014787 := bstep (se 1 (by rfl) ⟨1511090, by rfl⟩ : syracuseStep 2014787 = 3022181) B3022181
theorem B4030019 : Blo 1192413 4030019 := bstep (se 1 (by rfl) ⟨3022514, by rfl⟩ : syracuseStep 4030019 = 6045029) B6045029
theorem B6037091 : Blo 1192413 6037091 := bstep (se 1 (by rfl) ⟨4527818, by rfl⟩ : syracuseStep 6037091 = 9055637) B9055637
theorem B2547377 : Blo 1192413 2547377 := bstep (se 2 (by rfl) ⟨955266, by rfl⟩ : syracuseStep 2547377 = 1910533) B1910533
theorem B1343155 : Blo 1192413 1343155 := bstep (se 1 (by rfl) ⟨1007366, by rfl⟩ : syracuseStep 1343155 = 2014733) B2014733
theorem B2014915 : Blo 1192413 2014915 := bstep (se 1 (by rfl) ⟨1511186, by rfl⟩ : syracuseStep 2014915 = 3022373) B3022373
theorem B9068273 : Blo 1192413 9068273 := bstep (se 2 (by rfl) ⟨3400602, by rfl⟩ : syracuseStep 9068273 = 6801205) B6801205
theorem B1744675 : Blo 1192413 1744675 := bstep (se 1 (by rfl) ⟨1308506, by rfl⟩ : syracuseStep 1744675 = 2617013) B2617013
theorem B2686769 : Blo 1192413 2686769 := bstep (se 2 (by rfl) ⟨1007538, by rfl⟩ : syracuseStep 2686769 = 2015077) B2015077
theorem B1343299 : Blo 1192413 1343299 := bstep (se 1 (by rfl) ⟨1007474, by rfl⟩ : syracuseStep 1343299 = 2014949) B2014949
theorem B2686787 : Blo 1192413 2686787 := bstep (se 1 (by rfl) ⟨2015090, by rfl⟩ : syracuseStep 2686787 = 4030181) B4030181
theorem B2015057 : Blo 1192413 2015057 := bstep (se 2 (by rfl) ⟨755646, by rfl⟩ : syracuseStep 2015057 = 1511293) B1511293
theorem B4030289 : Blo 1192413 4030289 := bstep (se 2 (by rfl) ⟨1511358, by rfl⟩ : syracuseStep 4030289 = 3022717) B3022717
theorem B3399533 : Blo 1192413 3399533 := bstep (se 3 (by rfl) ⟨637412, by rfl⟩ : syracuseStep 3399533 = 1274825) B1274825
theorem B7651205 : Blo 1192413 7651205 := bstep (se 4 (by rfl) ⟨717300, by rfl⟩ : syracuseStep 7651205 = 1434601) B1434601
theorem B2015185 : Blo 1192413 2015185 := bstep (se 2 (by rfl) ⟨755694, by rfl⟩ : syracuseStep 2015185 = 1511389) B1511389
theorem B1343443 : Blo 1192413 1343443 := bstep (se 1 (by rfl) ⟨1007582, by rfl⟩ : syracuseStep 1343443 = 2015165) B2015165
theorem B4079587 : Blo 1192413 4079587 := bstep (se 1 (by rfl) ⟨3059690, by rfl⟩ : syracuseStep 4079587 = 6119381) B6119381
theorem B2015219 : Blo 1192413 2015219 := bstep (se 1 (by rfl) ⟨1511414, by rfl⟩ : syracuseStep 2015219 = 3022829) B3022829
theorem B2547787 : Blo 1192413 2547787 := bstep (se 1 (by rfl) ⟨1910840, by rfl⟩ : syracuseStep 2547787 = 3821681) B3821681
theorem B7258243 : Blo 1192413 7258243 := bstep (se 1 (by rfl) ⟨5443682, by rfl⟩ : syracuseStep 7258243 = 10887365) B10887365
theorem B2687129 : Blo 1192413 2687129 := bstep (se 2 (by rfl) ⟨1007673, by rfl⟩ : syracuseStep 2687129 = 2015347) B2015347
theorem B1343659 : Blo 1192413 1343659 := bstep (se 1 (by rfl) ⟨1007744, by rfl⟩ : syracuseStep 1343659 = 2015489) B2015489
theorem B3023041 : Blo 1192413 3023041 := bstep (se 2 (by rfl) ⟨1133640, by rfl⟩ : syracuseStep 3023041 = 2267281) B2267281
theorem B4030667 : Blo 1192413 4030667 := bstep (se 1 (by rfl) ⟨3023000, by rfl⟩ : syracuseStep 4030667 = 6046001) B6046001
theorem B2015435 : Blo 1192413 2015435 := bstep (se 1 (by rfl) ⟨1511576, by rfl⟩ : syracuseStep 2015435 = 3023153) B3023153
theorem B1532119 : Blo 1192413 1532119 := bstep (se 1 (by rfl) ⟨1149089, by rfl⟩ : syracuseStep 1532119 = 2298179) B2298179
theorem B2687219 : Blo 1192413 2687219 := bstep (se 1 (by rfl) ⟨2015414, by rfl⟩ : syracuseStep 2687219 = 4030829) B4030829
theorem B9814289 : Blo 1192413 9814289 := bstep (se 2 (by rfl) ⟨3680358, by rfl⟩ : syracuseStep 9814289 = 7360717) B7360717
theorem B2687255 : Blo 1192413 2687255 := bstep (se 1 (by rfl) ⟨2015441, by rfl⟩ : syracuseStep 2687255 = 4030883) B4030883
theorem B2015563 : Blo 1192413 2015563 := bstep (se 1 (by rfl) ⟨1511672, by rfl⟩ : syracuseStep 2015563 = 3023345) B3023345
theorem B6791525 : Blo 1192413 6791525 := bstep (se 4 (by rfl) ⟨636705, by rfl⟩ : syracuseStep 6791525 = 1273411) B1273411
theorem B6799747 : Blo 1192413 6799747 := bstep (se 1 (by rfl) ⟨5099810, by rfl⟩ : syracuseStep 6799747 = 10199621) B10199621
theorem B5095831 : Blo 1192413 5095831 := bstep (se 1 (by rfl) ⟨3821873, by rfl⟩ : syracuseStep 5095831 = 7643747) B7643747
theorem B4030937 : Blo 1192413 4030937 := bstep (se 2 (by rfl) ⟨1511601, by rfl⟩ : syracuseStep 4030937 = 3023203) B3023203
theorem B11469347 : Blo 1192413 11469347 := bstep (se 1 (by rfl) ⟨8602010, by rfl⟩ : syracuseStep 11469347 = 17204021) B17204021
theorem B20374091 : Blo 1192413 20374091 := bstep (se 1 (by rfl) ⟨15280568, by rfl⟩ : syracuseStep 20374091 = 30561137) B30561137
theorem B2548505 : Blo 1192413 2548505 := bstep (se 2 (by rfl) ⟨955689, by rfl⟩ : syracuseStep 2548505 = 1911379) B1911379
theorem B13591475 : Blo 1192413 13591475 := bstep (se 1 (by rfl) ⟨10193606, by rfl⟩ : syracuseStep 13591475 = 20387213) B20387213
theorem B2040779 : Blo 1192413 2040779 := bstep (se 1 (by rfl) ⟨1530584, by rfl⟩ : syracuseStep 2040779 = 3061169) B3061169
theorem B2720855 : Blo 1192413 2720855 := bstep (se 1 (by rfl) ⟨2040641, by rfl⟩ : syracuseStep 2720855 = 4081283) B4081283
theorem B9061469 : Blo 1192413 9061469 := bstep (se 3 (by rfl) ⟨1699025, by rfl⟩ : syracuseStep 9061469 = 3398051) B3398051
theorem B4531373 : Blo 1192413 4531373 := bstep (se 3 (by rfl) ⟨849632, by rfl⟩ : syracuseStep 4531373 = 1699265) B1699265
theorem B4531403 : Blo 1192413 4531403 := bstep (se 1 (by rfl) ⟨3398552, by rfl⟩ : syracuseStep 4531403 = 6797105) B6797105
theorem B2549017 : Blo 1192413 2549017 := bstep (se 2 (by rfl) ⟨955881, by rfl⟩ : syracuseStep 2549017 = 1911763) B1911763
theorem B9684269 : Blo 1192413 9684269 := bstep (se 3 (by rfl) ⟨1815800, by rfl⟩ : syracuseStep 9684269 = 3631601) B3631601
theorem B6800705 : Blo 1192413 6800705 := bstep (se 2 (by rfl) ⟨2550264, by rfl⟩ : syracuseStep 6800705 = 5100529) B5100529
theorem B2549171 : Blo 1192413 2549171 := bstep (se 1 (by rfl) ⟨1911878, by rfl⟩ : syracuseStep 2549171 = 3823757) B3823757
theorem B5596609 : Blo 1192413 5596609 := bstep (se 2 (by rfl) ⟨2098728, by rfl⟩ : syracuseStep 5596609 = 4197457) B4197457
theorem B3630557 : Blo 1192413 3630557 := bstep (se 3 (by rfl) ⟨680729, by rfl⟩ : syracuseStep 3630557 = 1361459) B1361459
theorem B5170763 : Blo 1192413 5170763 := bstep (se 1 (by rfl) ⟨3878072, by rfl⟩ : syracuseStep 5170763 = 7756145) B7756145
theorem B3589721 : Blo 1192413 3589721 := bstep (se 2 (by rfl) ⟨1346145, by rfl⟩ : syracuseStep 3589721 = 2692291) B2692291
theorem B2721431 : Blo 1192413 2721431 := bstep (se 1 (by rfl) ⟨2041073, by rfl⟩ : syracuseStep 2721431 = 4082147) B4082147
theorem B8726221 : Blo 1192413 8726221 := bstep (se 3 (by rfl) ⟨1636166, by rfl⟩ : syracuseStep 8726221 = 3272333) B3272333
theorem B6448913 : Blo 1192413 6448913 := bstep (se 2 (by rfl) ⟨2418342, by rfl⟩ : syracuseStep 6448913 = 4836685) B4836685
theorem B19384109 : Blo 1192413 19384109 := bstep (se 3 (by rfl) ⟨3634520, by rfl⟩ : syracuseStep 19384109 = 7269041) B7269041
theorem B2869067 : Blo 1192413 2869067 := bstep (se 1 (by rfl) ⟨2151800, by rfl⟩ : syracuseStep 2869067 = 4303601) B4303601
theorem B4532057 : Blo 1192413 4532057 := bstep (se 2 (by rfl) ⟨1699521, by rfl⟩ : syracuseStep 4532057 = 3399043) B3399043
theorem B8726449 : Blo 1192413 8726449 := bstep (se 2 (by rfl) ⟨3272418, by rfl⟩ : syracuseStep 8726449 = 6544837) B6544837
theorem B1722391 : Blo 1192413 1722391 := bstep (se 1 (by rfl) ⟨1291793, by rfl⟩ : syracuseStep 1722391 = 2583587) B2583587
theorem B12257315 : Blo 1192413 12257315 := bstep (se 1 (by rfl) ⟨9192986, by rfl⟩ : syracuseStep 12257315 = 18385973) B18385973
theorem B2869337 : Blo 1192413 2869337 := bstep (se 2 (by rfl) ⟨1076001, by rfl⟩ : syracuseStep 2869337 = 2152003) B2152003
theorem B6039683 : Blo 1192413 6039683 := bstep (se 1 (by rfl) ⟨4529762, by rfl⟩ : syracuseStep 6039683 = 9059525) B9059525
theorem B4532375 : Blo 1192413 4532375 := bstep (se 1 (by rfl) ⟨3399281, by rfl⟩ : syracuseStep 4532375 = 6798563) B6798563
theorem B13592933 : Blo 1192413 13592933 := bstep (se 4 (by rfl) ⟨1274337, by rfl⟩ : syracuseStep 13592933 = 2548675) B2548675
theorem B2550145 : Blo 1192413 2550145 := bstep (se 2 (by rfl) ⟨956304, by rfl⟩ : syracuseStep 2550145 = 1912609) B1912609
theorem B4024727 : Blo 1192413 4024727 := bstep (se 1 (by rfl) ⟨3018545, by rfl⟩ : syracuseStep 4024727 = 6037091) B6037091
theorem B1698251 : Blo 1192413 1698251 := bstep (se 1 (by rfl) ⟨1273688, by rfl⟩ : syracuseStep 1698251 = 2547377) B2547377
theorem B1509835 : Blo 1192413 1509835 := bstep (se 1 (by rfl) ⟨1132376, by rfl⟩ : syracuseStep 1509835 = 2264753) B2264753
theorem B2869721 : Blo 1192413 2869721 := bstep (se 2 (by rfl) ⟨1076145, by rfl⟩ : syracuseStep 2869721 = 2152291) B2152291
theorem B45861389 : Blo 1192413 45861389 := bstep (se 3 (by rfl) ⟨8599010, by rfl⟩ : syracuseStep 45861389 = 17198021) B17198021
theorem B2148889 : Blo 1192413 2148889 := bstep (se 2 (by rfl) ⟨805833, by rfl⟩ : syracuseStep 2148889 = 1611667) B1611667
theorem B1510103 : Blo 1192413 1510103 := bstep (se 1 (by rfl) ⟨1132577, by rfl⟩ : syracuseStep 1510103 = 2265155) B2265155
theorem B8604377 : Blo 1192413 8604377 := bstep (se 2 (by rfl) ⟨3226641, by rfl⟩ : syracuseStep 8604377 = 6453283) B6453283
theorem B2550487 : Blo 1192413 2550487 := bstep (se 1 (by rfl) ⟨1912865, by rfl⟩ : syracuseStep 2550487 = 3825731) B3825731
theorem B84962033 : Blo 1192413 84962033 := bstep (se 2 (by rfl) ⟨31860762, by rfl⟩ : syracuseStep 84962033 = 63721525) B63721525
theorem B1788683 : Blo 1192413 1788683 := bstep (se 1 (by rfl) ⟨1341512, by rfl⟩ : syracuseStep 1788683 = 2683025) B2683025
theorem B1788695 : Blo 1192413 1788695 := bstep (se 1 (by rfl) ⟨1341521, by rfl⟩ : syracuseStep 1788695 = 2683043) B2683043
theorem B4533043 : Blo 1192413 4533043 := bstep (se 1 (by rfl) ⟨3399782, by rfl⟩ : syracuseStep 4533043 = 6799565) B6799565
theorem B34868033 : Blo 1192413 34868033 := bstep (se 2 (by rfl) ⟨13075512, by rfl⟩ : syracuseStep 34868033 = 26151025) B26151025
theorem B1788761 : Blo 1192413 1788761 := bstep (se 2 (by rfl) ⟨670785, by rfl⟩ : syracuseStep 1788761 = 1341571) B1341571
theorem B2149249 : Blo 1192413 2149249 := bstep (se 2 (by rfl) ⟨805968, by rfl⟩ : syracuseStep 2149249 = 1611937) B1611937
theorem B3820439 : Blo 1192413 3820439 := bstep (se 1 (by rfl) ⟨2865329, by rfl⟩ : syracuseStep 3820439 = 5730659) B5730659
theorem B4025267 : Blo 1192413 4025267 := bstep (se 1 (by rfl) ⟨3018950, by rfl⟩ : syracuseStep 4025267 = 6037901) B6037901
theorem B19360691 : Blo 1192413 19360691 := bstep (se 1 (by rfl) ⟨14520518, by rfl⟩ : syracuseStep 19360691 = 29041037) B29041037
theorem B1788875 : Blo 1192413 1788875 := bstep (se 1 (by rfl) ⟨1341656, by rfl⟩ : syracuseStep 1788875 = 2683313) B2683313
theorem B1788887 : Blo 1192413 1788887 := bstep (se 1 (by rfl) ⟨1341665, by rfl⟩ : syracuseStep 1788887 = 2683331) B2683331
theorem B1788953 : Blo 1192413 1788953 := bstep (se 2 (by rfl) ⟨670857, by rfl⟩ : syracuseStep 1788953 = 1341715) B1341715
theorem B1936523 : Blo 1192413 1936523 := bstep (se 1 (by rfl) ⟨1452392, by rfl⟩ : syracuseStep 1936523 = 2904785) B2904785
theorem B1789067 : Blo 1192413 1789067 := bstep (se 1 (by rfl) ⟨1341800, by rfl⟩ : syracuseStep 1789067 = 2683601) B2683601
theorem B2550923 : Blo 1192413 2550923 := bstep (se 1 (by rfl) ⟨1913192, by rfl⟩ : syracuseStep 2550923 = 3826385) B3826385
theorem B1789079 : Blo 1192413 1789079 := bstep (se 1 (by rfl) ⟨1341809, by rfl⟩ : syracuseStep 1789079 = 2683619) B2683619
theorem B4025537 : Blo 1192413 4025537 := bstep (se 2 (by rfl) ⟨1509576, by rfl⟩ : syracuseStep 4025537 = 3019153) B3019153
theorem B2264267 : Blo 1192413 2264267 := bstep (se 1 (by rfl) ⟨1698200, by rfl⟩ : syracuseStep 2264267 = 3396401) B3396401
theorem B14150861 : Blo 1192413 14150861 := bstep (se 3 (by rfl) ⟨2653286, by rfl⟩ : syracuseStep 14150861 = 5306573) B5306573
theorem B1789145 : Blo 1192413 1789145 := bstep (se 2 (by rfl) ⟨670929, by rfl⟩ : syracuseStep 1789145 = 1341859) B1341859
theorem B9678041 : Blo 1192413 9678041 := bstep (se 2 (by rfl) ⟨3629265, by rfl⟩ : syracuseStep 9678041 = 7258531) B7258531
theorem B5098717 : Blo 1192413 5098717 := bstep (se 3 (by rfl) ⟨956009, by rfl⟩ : syracuseStep 5098717 = 1912019) B1912019
theorem B1789259 : Blo 1192413 1789259 := bstep (se 1 (by rfl) ⟨1341944, by rfl⟩ : syracuseStep 1789259 = 2683889) B2683889
theorem B1789271 : Blo 1192413 1789271 := bstep (se 1 (by rfl) ⟨1341953, by rfl⟩ : syracuseStep 1789271 = 2683907) B2683907
theorem B2264449 : Blo 1192413 2264449 := bstep (se 2 (by rfl) ⟨849168, by rfl⟩ : syracuseStep 2264449 = 1698337) B1698337
theorem B37219733 : Blo 1192413 37219733 := bstep (se 6 (by rfl) ⟨872337, by rfl⟩ : syracuseStep 37219733 = 1744675) B1744675
theorem B1510807 : Blo 1192413 1510807 := bstep (se 1 (by rfl) ⟨1133105, by rfl⟩ : syracuseStep 1510807 = 2266211) B2266211
theorem B1789337 : Blo 1192413 1789337 := bstep (se 2 (by rfl) ⟨671001, by rfl⟩ : syracuseStep 1789337 = 1342003) B1342003
theorem B1789451 : Blo 1192413 1789451 := bstep (se 1 (by rfl) ⟨1342088, by rfl⟩ : syracuseStep 1789451 = 2684177) B2684177
theorem B17190413 : Blo 1192413 17190413 := bstep (se 3 (by rfl) ⟨3223202, by rfl⟩ : syracuseStep 17190413 = 6446405) B6446405
theorem B1789463 : Blo 1192413 1789463 := bstep (se 1 (by rfl) ⟨1342097, by rfl⟩ : syracuseStep 1789463 = 2684195) B2684195
theorem B10194497 : Blo 1192413 10194497 := bstep (se 2 (by rfl) ⟨3822936, by rfl⟩ : syracuseStep 10194497 = 7645873) B7645873
theorem B1789529 : Blo 1192413 1789529 := bstep (se 2 (by rfl) ⟨671073, by rfl⟩ : syracuseStep 1789529 = 1342147) B1342147
theorem B1789643 : Blo 1192413 1789643 := bstep (se 1 (by rfl) ⟨1342232, by rfl⟩ : syracuseStep 1789643 = 2684465) B2684465
theorem B1814219 : Blo 1192413 1814219 := bstep (se 1 (by rfl) ⟨1360664, by rfl⟩ : syracuseStep 1814219 = 2721329) B2721329
theorem B1789655 : Blo 1192413 1789655 := bstep (se 1 (by rfl) ⟨1342241, by rfl⟩ : syracuseStep 1789655 = 2684483) B2684483
theorem B4026077 : Blo 1192413 4026077 := bstep (se 3 (by rfl) ⟨754889, by rfl⟩ : syracuseStep 4026077 = 1509779) B1509779
theorem B1789721 : Blo 1192413 1789721 := bstep (se 2 (by rfl) ⟨671145, by rfl⟩ : syracuseStep 1789721 = 1342291) B1342291
theorem B2264897 : Blo 1192413 2264897 := bstep (se 2 (by rfl) ⟨849336, by rfl⟩ : syracuseStep 2264897 = 1698673) B1698673
theorem B34860901 : Blo 1192413 34860901 := bstep (se 4 (by rfl) ⟨3268209, by rfl⟩ : syracuseStep 34860901 = 6536419) B6536419
theorem B1789835 : Blo 1192413 1789835 := bstep (se 1 (by rfl) ⟨1342376, by rfl⟩ : syracuseStep 1789835 = 2684753) B2684753
theorem B3018647 : Blo 1192413 3018647 := bstep (se 1 (by rfl) ⟨2263985, by rfl⟩ : syracuseStep 3018647 = 4527971) B4527971
theorem B1789847 : Blo 1192413 1789847 := bstep (se 1 (by rfl) ⟨1342385, by rfl⟩ : syracuseStep 1789847 = 2684771) B2684771
theorem B7647155 : Blo 1192413 7647155 := bstep (se 1 (by rfl) ⟨5735366, by rfl⟩ : syracuseStep 7647155 = 11470733) B11470733
theorem B14348249 : Blo 1192413 14348249 := bstep (se 2 (by rfl) ⟨5380593, by rfl⟩ : syracuseStep 14348249 = 10761187) B10761187
theorem B1789913 : Blo 1192413 1789913 := bstep (se 2 (by rfl) ⟨671217, by rfl⟩ : syracuseStep 1789913 = 1342435) B1342435
theorem B5099537 : Blo 1192413 5099537 := bstep (se 2 (by rfl) ⟨1912326, by rfl⟩ : syracuseStep 5099537 = 3824653) B3824653
theorem B4534289 : Blo 1192413 4534289 := bstep (se 2 (by rfl) ⟨1700358, by rfl⟩ : syracuseStep 4534289 = 3400717) B3400717
theorem B1790027 : Blo 1192413 1790027 := bstep (se 1 (by rfl) ⟨1342520, by rfl⟩ : syracuseStep 1790027 = 2685041) B2685041
theorem B1790039 : Blo 1192413 1790039 := bstep (se 1 (by rfl) ⟨1342529, by rfl⟩ : syracuseStep 1790039 = 2685059) B2685059
theorem B2265239 : Blo 1192413 2265239 := bstep (se 1 (by rfl) ⟨1698929, by rfl⟩ : syracuseStep 2265239 = 3397859) B3397859
theorem B1790105 : Blo 1192413 1790105 := bstep (se 2 (by rfl) ⟨671289, by rfl⟩ : syracuseStep 1790105 = 1342579) B1342579
theorem B2683097 : Blo 1192413 2683097 := bstep (se 2 (by rfl) ⟨1006161, by rfl⟩ : syracuseStep 2683097 = 2012323) B2012323
theorem B1790219 : Blo 1192413 1790219 := bstep (se 1 (by rfl) ⟨1342664, by rfl⟩ : syracuseStep 1790219 = 2685329) B2685329
theorem B1790231 : Blo 1192413 1790231 := bstep (se 1 (by rfl) ⟨1342673, by rfl⟩ : syracuseStep 1790231 = 2685347) B2685347
theorem B1700119 : Blo 1192413 1700119 := bstep (se 1 (by rfl) ⟨1275089, by rfl⟩ : syracuseStep 1700119 = 2550179) B2550179
theorem B2683187 : Blo 1192413 2683187 := bstep (se 1 (by rfl) ⟨2012390, by rfl⟩ : syracuseStep 2683187 = 4024781) B4024781
theorem B1274167 : Blo 1192413 1274167 := bstep (se 1 (by rfl) ⟨955625, by rfl⟩ : syracuseStep 1274167 = 1911251) B1911251
theorem B2683223 : Blo 1192413 2683223 := bstep (se 1 (by rfl) ⟨2012417, by rfl⟩ : syracuseStep 2683223 = 4024835) B4024835
theorem B1790297 : Blo 1192413 1790297 := bstep (se 2 (by rfl) ⟨671361, by rfl⟩ : syracuseStep 1790297 = 1342723) B1342723
theorem B9671005 : Blo 1192413 9671005 := bstep (se 3 (by rfl) ⟨1813313, by rfl⟩ : syracuseStep 9671005 = 3626627) B3626627
theorem B1790411 : Blo 1192413 1790411 := bstep (se 1 (by rfl) ⟨1342808, by rfl⟩ : syracuseStep 1790411 = 2685617) B2685617
theorem B1790423 : Blo 1192413 1790423 := bstep (se 1 (by rfl) ⟨1342817, by rfl⟩ : syracuseStep 1790423 = 2685635) B2685635
theorem B1192427 : Blo 1192413 1192427 := bstep (se 1 (by rfl) ⟨894320, by rfl⟩ : syracuseStep 1192427 = 1788641) B1788641
theorem B1192439 : Blo 1192413 1192439 := bstep (se 1 (by rfl) ⟨894329, by rfl⟩ : syracuseStep 1192439 = 1788659) B1788659
theorem B1192459 : Blo 1192413 1192459 := bstep (se 1 (by rfl) ⟨894344, by rfl⟩ : syracuseStep 1192459 = 1788689) B1788689
theorem B2683403 : Blo 1192413 2683403 := bstep (se 1 (by rfl) ⟨2012552, by rfl⟩ : syracuseStep 2683403 = 4025105) B4025105
theorem B1192471 : Blo 1192413 1192471 := bstep (se 1 (by rfl) ⟨894353, by rfl⟩ : syracuseStep 1192471 = 1788707) B1788707
theorem B1790489 : Blo 1192413 1790489 := bstep (se 2 (by rfl) ⟨671433, by rfl⟩ : syracuseStep 1790489 = 1342867) B1342867
theorem B1192491 : Blo 1192413 1192491 := bstep (se 1 (by rfl) ⟨894368, by rfl⟩ : syracuseStep 1192491 = 1788737) B1788737
theorem B3019315 : Blo 1192413 3019315 := bstep (se 1 (by rfl) ⟨2264486, by rfl⟩ : syracuseStep 3019315 = 4528973) B4528973
theorem B1192503 : Blo 1192413 1192503 := bstep (se 1 (by rfl) ⟨894377, by rfl⟩ : syracuseStep 1192503 = 1788755) B1788755
theorem B3396161 : Blo 1192413 3396161 := bstep (se 2 (by rfl) ⟨1273560, by rfl⟩ : syracuseStep 3396161 = 2547121) B2547121
theorem B2683457 : Blo 1192413 2683457 := bstep (se 2 (by rfl) ⟨1006296, by rfl⟩ : syracuseStep 2683457 = 2012593) B2012593
theorem B1192523 : Blo 1192413 1192523 := bstep (se 1 (by rfl) ⟨894392, by rfl⟩ : syracuseStep 1192523 = 1788785) B1788785
theorem B13775435 : Blo 1192413 13775435 := bstep (se 1 (by rfl) ⟨10331576, by rfl⟩ : syracuseStep 13775435 = 20663153) B20663153
theorem B1192535 : Blo 1192413 1192535 := bstep (se 1 (by rfl) ⟨894401, by rfl⟩ : syracuseStep 1192535 = 1788803) B1788803
theorem B2904665 : Blo 1192413 2904665 := bstep (se 2 (by rfl) ⟨1089249, by rfl⟩ : syracuseStep 2904665 = 2178499) B2178499
theorem B1192555 : Blo 1192413 1192555 := bstep (se 1 (by rfl) ⟨894416, by rfl⟩ : syracuseStep 1192555 = 1788833) B1788833
theorem B1192567 : Blo 1192413 1192567 := bstep (se 1 (by rfl) ⟨894425, by rfl⟩ : syracuseStep 1192567 = 1788851) B1788851
theorem B1192587 : Blo 1192413 1192587 := bstep (se 1 (by rfl) ⟨894440, by rfl⟩ : syracuseStep 1192587 = 1788881) B1788881
theorem B1790603 : Blo 1192413 1790603 := bstep (se 1 (by rfl) ⟨1342952, by rfl⟩ : syracuseStep 1790603 = 2685905) B2685905
theorem B1192599 : Blo 1192413 1192599 := bstep (se 1 (by rfl) ⟨894449, by rfl⟩ : syracuseStep 1192599 = 1788899) B1788899
theorem B1790615 : Blo 1192413 1790615 := bstep (se 1 (by rfl) ⟨1342961, by rfl⟩ : syracuseStep 1790615 = 2685923) B2685923
theorem B1815193 : Blo 1192413 1815193 := bstep (se 2 (by rfl) ⟨680697, by rfl⟩ : syracuseStep 1815193 = 1361395) B1361395
theorem B1192619 : Blo 1192413 1192619 := bstep (se 1 (by rfl) ⟨894464, by rfl⟩ : syracuseStep 1192619 = 1788929) B1788929
theorem B5100205 : Blo 1192413 5100205 := bstep (se 3 (by rfl) ⟨956288, by rfl⟩ : syracuseStep 5100205 = 1912577) B1912577
theorem B3396275 : Blo 1192413 3396275 := bstep (se 1 (by rfl) ⟨2547206, by rfl⟩ : syracuseStep 3396275 = 5094413) B5094413
theorem B1192631 : Blo 1192413 1192631 := bstep (se 1 (by rfl) ⟨894473, by rfl⟩ : syracuseStep 1192631 = 1788947) B1788947
theorem B3019457 : Blo 1192413 3019457 := bstep (se 2 (by rfl) ⟨1132296, by rfl⟩ : syracuseStep 3019457 = 2264593) B2264593
theorem B1192651 : Blo 1192413 1192651 := bstep (se 1 (by rfl) ⟨894488, by rfl⟩ : syracuseStep 1192651 = 1788977) B1788977
theorem B4534987 : Blo 1192413 4534987 := bstep (se 1 (by rfl) ⟨3401240, by rfl⟩ : syracuseStep 4534987 = 6802481) B6802481
theorem B1192663 : Blo 1192413 1192663 := bstep (se 1 (by rfl) ⟨894497, by rfl⟩ : syracuseStep 1192663 = 1788995) B1788995
theorem B1790681 : Blo 1192413 1790681 := bstep (se 2 (by rfl) ⟨671505, by rfl⟩ : syracuseStep 1790681 = 1343011) B1343011
theorem B1192683 : Blo 1192413 1192683 := bstep (se 1 (by rfl) ⟨894512, by rfl⟩ : syracuseStep 1192683 = 1789025) B1789025
theorem B1192695 : Blo 1192413 1192695 := bstep (se 1 (by rfl) ⟨894521, by rfl⟩ : syracuseStep 1192695 = 1789043) B1789043
theorem B1192715 : Blo 1192413 1192715 := bstep (se 1 (by rfl) ⟨894536, by rfl⟩ : syracuseStep 1192715 = 1789073) B1789073
theorem B1192727 : Blo 1192413 1192727 := bstep (se 1 (by rfl) ⟨894545, by rfl⟩ : syracuseStep 1192727 = 1789091) B1789091
theorem B2683673 : Blo 1192413 2683673 := bstep (se 2 (by rfl) ⟨1006377, by rfl⟩ : syracuseStep 2683673 = 2012755) B2012755
theorem B1192747 : Blo 1192413 1192747 := bstep (se 1 (by rfl) ⟨894560, by rfl⟩ : syracuseStep 1192747 = 1789121) B1789121
theorem B2265907 : Blo 1192413 2265907 := bstep (se 1 (by rfl) ⟨1699430, by rfl⟩ : syracuseStep 2265907 = 3398861) B3398861
theorem B1291063 : Blo 1192413 1291063 := bstep (se 1 (by rfl) ⟨968297, by rfl⟩ : syracuseStep 1291063 = 1936595) B1936595
theorem B1192759 : Blo 1192413 1192759 := bstep (se 1 (by rfl) ⟨894569, by rfl⟩ : syracuseStep 1192759 = 1789139) B1789139
theorem B1192779 : Blo 1192413 1192779 := bstep (se 1 (by rfl) ⟨894584, by rfl⟩ : syracuseStep 1192779 = 1789169) B1789169
theorem B4027211 : Blo 1192413 4027211 := bstep (se 1 (by rfl) ⟨3020408, by rfl⟩ : syracuseStep 4027211 = 6040817) B6040817
theorem B1790795 : Blo 1192413 1790795 := bstep (se 1 (by rfl) ⟨1343096, by rfl⟩ : syracuseStep 1790795 = 2686193) B2686193
theorem B1192791 : Blo 1192413 1192791 := bstep (se 1 (by rfl) ⟨894593, by rfl⟩ : syracuseStep 1192791 = 1789187) B1789187
theorem B1790807 : Blo 1192413 1790807 := bstep (se 1 (by rfl) ⟨1343105, by rfl⟩ : syracuseStep 1790807 = 2686211) B2686211
theorem B1192811 : Blo 1192413 1192811 := bstep (se 1 (by rfl) ⟨894608, by rfl⟩ : syracuseStep 1192811 = 1789217) B1789217
theorem B2683763 : Blo 1192413 2683763 := bstep (se 1 (by rfl) ⟨2012822, by rfl⟩ : syracuseStep 2683763 = 4025645) B4025645
theorem B1192823 : Blo 1192413 1192823 := bstep (se 1 (by rfl) ⟨894617, by rfl⟩ : syracuseStep 1192823 = 1789235) B1789235
theorem B1192843 : Blo 1192413 1192843 := bstep (se 1 (by rfl) ⟨894632, by rfl⟩ : syracuseStep 1192843 = 1789265) B1789265
theorem B2683799 : Blo 1192413 2683799 := bstep (se 1 (by rfl) ⟨2012849, by rfl⟩ : syracuseStep 2683799 = 4025699) B4025699
theorem B1192855 : Blo 1192413 1192855 := bstep (se 1 (by rfl) ⟨894641, by rfl⟩ : syracuseStep 1192855 = 1789283) B1789283
theorem B1790873 : Blo 1192413 1790873 := bstep (se 2 (by rfl) ⟨671577, by rfl⟩ : syracuseStep 1790873 = 1343155) B1343155
theorem B1192875 : Blo 1192413 1192875 := bstep (se 1 (by rfl) ⟨894656, by rfl⟩ : syracuseStep 1192875 = 1789313) B1789313
theorem B1192887 : Blo 1192413 1192887 := bstep (se 1 (by rfl) ⟨894665, by rfl⟩ : syracuseStep 1192887 = 1789331) B1789331
theorem B1192907 : Blo 1192413 1192907 := bstep (se 1 (by rfl) ⟨894680, by rfl⟩ : syracuseStep 1192907 = 1789361) B1789361
theorem B1192919 : Blo 1192413 1192919 := bstep (se 1 (by rfl) ⟨894689, by rfl⟩ : syracuseStep 1192919 = 1789379) B1789379
theorem B1192939 : Blo 1192413 1192939 := bstep (se 1 (by rfl) ⟨894704, by rfl⟩ : syracuseStep 1192939 = 1789409) B1789409
theorem B1192951 : Blo 1192413 1192951 := bstep (se 1 (by rfl) ⟨894713, by rfl⟩ : syracuseStep 1192951 = 1789427) B1789427
theorem B1192971 : Blo 1192413 1192971 := bstep (se 1 (by rfl) ⟨894728, by rfl⟩ : syracuseStep 1192971 = 1789457) B1789457
theorem B1790987 : Blo 1192413 1790987 := bstep (se 1 (by rfl) ⟨1343240, by rfl⟩ : syracuseStep 1790987 = 2686481) B2686481
theorem B7640081 : Blo 1192413 7640081 := bstep (se 2 (by rfl) ⟨2865030, by rfl⟩ : syracuseStep 7640081 = 5730061) B5730061
theorem B1192983 : Blo 1192413 1192983 := bstep (se 1 (by rfl) ⟨894737, by rfl⟩ : syracuseStep 1192983 = 1789475) B1789475
theorem B1790999 : Blo 1192413 1790999 := bstep (se 1 (by rfl) ⟨1343249, by rfl⟩ : syracuseStep 1790999 = 2686499) B2686499
theorem B1193003 : Blo 1192413 1193003 := bstep (se 1 (by rfl) ⟨894752, by rfl⟩ : syracuseStep 1193003 = 1789505) B1789505
theorem B1193015 : Blo 1192413 1193015 := bstep (se 1 (by rfl) ⟨894761, by rfl⟩ : syracuseStep 1193015 = 1789523) B1789523
theorem B2683979 : Blo 1192413 2683979 := bstep (se 1 (by rfl) ⟨2012984, by rfl⟩ : syracuseStep 2683979 = 4025969) B4025969
theorem B1193035 : Blo 1192413 1193035 := bstep (se 1 (by rfl) ⟨894776, by rfl⟩ : syracuseStep 1193035 = 1789553) B1789553
theorem B1193047 : Blo 1192413 1193047 := bstep (se 1 (by rfl) ⟨894785, by rfl⟩ : syracuseStep 1193047 = 1789571) B1789571
theorem B2012249 : Blo 1192413 2012249 := bstep (se 2 (by rfl) ⟨754593, by rfl⟩ : syracuseStep 2012249 = 1509187) B1509187
theorem B4027481 : Blo 1192413 4027481 := bstep (se 2 (by rfl) ⟨1510305, by rfl⟩ : syracuseStep 4027481 = 3020611) B3020611
theorem B1791065 : Blo 1192413 1791065 := bstep (se 2 (by rfl) ⟨671649, by rfl⟩ : syracuseStep 1791065 = 1343299) B1343299
theorem B1193067 : Blo 1192413 1193067 := bstep (se 1 (by rfl) ⟨894800, by rfl⟩ : syracuseStep 1193067 = 1789601) B1789601
theorem B1274987 : Blo 1192413 1274987 := bstep (se 1 (by rfl) ⟨956240, by rfl⟩ : syracuseStep 1274987 = 1912481) B1912481
theorem B1193079 : Blo 1192413 1193079 := bstep (se 1 (by rfl) ⟨894809, by rfl⟩ : syracuseStep 1193079 = 1789619) B1789619
theorem B2684033 : Blo 1192413 2684033 := bstep (se 2 (by rfl) ⟨1006512, by rfl⟩ : syracuseStep 2684033 = 2013025) B2013025
theorem B1193099 : Blo 1192413 1193099 := bstep (se 1 (by rfl) ⟨894824, by rfl⟩ : syracuseStep 1193099 = 1789649) B1789649
theorem B1193111 : Blo 1192413 1193111 := bstep (se 1 (by rfl) ⟨894833, by rfl⟩ : syracuseStep 1193111 = 1789667) B1789667
theorem B1193131 : Blo 1192413 1193131 := bstep (se 1 (by rfl) ⟨894848, by rfl⟩ : syracuseStep 1193131 = 1789697) B1789697
theorem B1193143 : Blo 1192413 1193143 := bstep (se 1 (by rfl) ⟨894857, by rfl⟩ : syracuseStep 1193143 = 1789715) B1789715
theorem B1193163 : Blo 1192413 1193163 := bstep (se 1 (by rfl) ⟨894872, by rfl⟩ : syracuseStep 1193163 = 1789745) B1789745
theorem B1791179 : Blo 1192413 1791179 := bstep (se 1 (by rfl) ⟨1343384, by rfl⟩ : syracuseStep 1791179 = 2686769) B2686769
theorem B1193175 : Blo 1192413 1193175 := bstep (se 1 (by rfl) ⟨894881, by rfl⟩ : syracuseStep 1193175 = 1789763) B1789763
theorem B1791191 : Blo 1192413 1791191 := bstep (se 1 (by rfl) ⟨1343393, by rfl⟩ : syracuseStep 1791191 = 2686787) B2686787
theorem B2012377 : Blo 1192413 2012377 := bstep (se 2 (by rfl) ⟨754641, by rfl⟩ : syracuseStep 2012377 = 1509283) B1509283
theorem B1193195 : Blo 1192413 1193195 := bstep (se 1 (by rfl) ⟨894896, by rfl⟩ : syracuseStep 1193195 = 1789793) B1789793
theorem B2266355 : Blo 1192413 2266355 := bstep (se 1 (by rfl) ⟨1699766, by rfl⟩ : syracuseStep 2266355 = 3399533) B3399533
theorem B1193207 : Blo 1192413 1193207 := bstep (se 1 (by rfl) ⟨894905, by rfl⟩ : syracuseStep 1193207 = 1789811) B1789811
theorem B5100803 : Blo 1192413 5100803 := bstep (se 1 (by rfl) ⟨3825602, by rfl⟩ : syracuseStep 5100803 = 7651205) B7651205
theorem B1193227 : Blo 1192413 1193227 := bstep (se 1 (by rfl) ⟨894920, by rfl⟩ : syracuseStep 1193227 = 1789841) B1789841
theorem B6043409 : Blo 1192413 6043409 := bstep (se 2 (by rfl) ⟨2266278, by rfl⟩ : syracuseStep 6043409 = 4532557) B4532557
theorem B1193239 : Blo 1192413 1193239 := bstep (se 1 (by rfl) ⟨894929, by rfl⟩ : syracuseStep 1193239 = 1789859) B1789859
theorem B2266393 : Blo 1192413 2266393 := bstep (se 2 (by rfl) ⟨849897, by rfl⟩ : syracuseStep 2266393 = 1699795) B1699795
theorem B1791257 : Blo 1192413 1791257 := bstep (se 2 (by rfl) ⟨671721, by rfl⟩ : syracuseStep 1791257 = 1343443) B1343443
theorem B1193259 : Blo 1192413 1193259 := bstep (se 1 (by rfl) ⟨894944, by rfl⟩ : syracuseStep 1193259 = 1789889) B1789889
theorem B9057581 : Blo 1192413 9057581 := bstep (se 3 (by rfl) ⟨1698296, by rfl⟩ : syracuseStep 9057581 = 3396593) B3396593
theorem B1193271 : Blo 1192413 1193271 := bstep (se 1 (by rfl) ⟨894953, by rfl⟩ : syracuseStep 1193271 = 1789907) B1789907
theorem B1193291 : Blo 1192413 1193291 := bstep (se 1 (by rfl) ⟨894968, by rfl⟩ : syracuseStep 1193291 = 1789937) B1789937
theorem B1193303 : Blo 1192413 1193303 := bstep (se 1 (by rfl) ⟨894977, by rfl⟩ : syracuseStep 1193303 = 1789955) B1789955
theorem B2684249 : Blo 1192413 2684249 := bstep (se 2 (by rfl) ⟨1006593, by rfl⟩ : syracuseStep 2684249 = 2013187) B2013187
theorem B1193323 : Blo 1192413 1193323 := bstep (se 1 (by rfl) ⟨894992, by rfl⟩ : syracuseStep 1193323 = 1789985) B1789985
theorem B1193335 : Blo 1192413 1193335 := bstep (se 1 (by rfl) ⟨895001, by rfl⟩ : syracuseStep 1193335 = 1790003) B1790003
theorem B1193355 : Blo 1192413 1193355 := bstep (se 1 (by rfl) ⟨895016, by rfl⟩ : syracuseStep 1193355 = 1790033) B1790033
theorem B1791371 : Blo 1192413 1791371 := bstep (se 1 (by rfl) ⟨1343528, by rfl⟩ : syracuseStep 1791371 = 2687057) B2687057
theorem B1193367 : Blo 1192413 1193367 := bstep (se 1 (by rfl) ⟨895025, by rfl⟩ : syracuseStep 1193367 = 1790051) B1790051
theorem B1791383 : Blo 1192413 1791383 := bstep (se 1 (by rfl) ⟨1343537, by rfl⟩ : syracuseStep 1791383 = 2687075) B2687075
theorem B1193387 : Blo 1192413 1193387 := bstep (se 1 (by rfl) ⟨895040, by rfl⟩ : syracuseStep 1193387 = 1790081) B1790081
theorem B2684339 : Blo 1192413 2684339 := bstep (se 1 (by rfl) ⟨2013254, by rfl⟩ : syracuseStep 2684339 = 4026509) B4026509
theorem B1193399 : Blo 1192413 1193399 := bstep (se 1 (by rfl) ⟨895049, by rfl⟩ : syracuseStep 1193399 = 1790099) B1790099
theorem B1193419 : Blo 1192413 1193419 := bstep (se 1 (by rfl) ⟨895064, by rfl⟩ : syracuseStep 1193419 = 1790129) B1790129
theorem B2684375 : Blo 1192413 2684375 := bstep (se 1 (by rfl) ⟨2013281, by rfl⟩ : syracuseStep 2684375 = 4026563) B4026563
theorem B1193431 : Blo 1192413 1193431 := bstep (se 1 (by rfl) ⟨895073, by rfl⟩ : syracuseStep 1193431 = 1790147) B1790147
theorem B1791449 : Blo 1192413 1791449 := bstep (se 2 (by rfl) ⟨671793, by rfl⟩ : syracuseStep 1791449 = 1343587) B1343587
theorem B1193451 : Blo 1192413 1193451 := bstep (se 1 (by rfl) ⟨895088, by rfl⟩ : syracuseStep 1193451 = 1790177) B1790177
theorem B1193463 : Blo 1192413 1193463 := bstep (se 1 (by rfl) ⟨895097, by rfl⟩ : syracuseStep 1193463 = 1790195) B1790195
theorem B1193483 : Blo 1192413 1193483 := bstep (se 1 (by rfl) ⟨895112, by rfl⟩ : syracuseStep 1193483 = 1790225) B1790225
theorem B1193495 : Blo 1192413 1193495 := bstep (se 1 (by rfl) ⟨895121, by rfl⟩ : syracuseStep 1193495 = 1790243) B1790243
theorem B8713763 : Blo 1192413 8713763 := bstep (se 1 (by rfl) ⟨6535322, by rfl⟩ : syracuseStep 8713763 = 13070645) B13070645
theorem B1193515 : Blo 1192413 1193515 := bstep (se 1 (by rfl) ⟨895136, by rfl⟩ : syracuseStep 1193515 = 1790273) B1790273
theorem B1193527 : Blo 1192413 1193527 := bstep (se 1 (by rfl) ⟨895145, by rfl⟩ : syracuseStep 1193527 = 1790291) B1790291
theorem B1193547 : Blo 1192413 1193547 := bstep (se 1 (by rfl) ⟨895160, by rfl⟩ : syracuseStep 1193547 = 1790321) B1790321
theorem B1791563 : Blo 1192413 1791563 := bstep (se 1 (by rfl) ⟨1343672, by rfl⟩ : syracuseStep 1791563 = 2687345) B2687345
theorem B1193559 : Blo 1192413 1193559 := bstep (se 1 (by rfl) ⟨895169, by rfl⟩ : syracuseStep 1193559 = 1790339) B1790339
theorem B1791575 : Blo 1192413 1791575 := bstep (se 1 (by rfl) ⟨1343681, by rfl⟩ : syracuseStep 1791575 = 2687363) B2687363
theorem B1193579 : Blo 1192413 1193579 := bstep (se 1 (by rfl) ⟨895184, by rfl⟩ : syracuseStep 1193579 = 1790369) B1790369
theorem B1193591 : Blo 1192413 1193591 := bstep (se 1 (by rfl) ⟨895193, by rfl⟩ : syracuseStep 1193591 = 1790387) B1790387
theorem B2684555 : Blo 1192413 2684555 := bstep (se 1 (by rfl) ⟨2013416, by rfl⟩ : syracuseStep 2684555 = 4026833) B4026833
theorem B1193611 : Blo 1192413 1193611 := bstep (se 1 (by rfl) ⟨895208, by rfl⟩ : syracuseStep 1193611 = 1790417) B1790417
theorem B2758295 : Blo 1192413 2758295 := bstep (se 1 (by rfl) ⟨2068721, by rfl⟩ : syracuseStep 2758295 = 4137443) B4137443
theorem B1193623 : Blo 1192413 1193623 := bstep (se 1 (by rfl) ⟨895217, by rfl⟩ : syracuseStep 1193623 = 1790435) B1790435
theorem B1193643 : Blo 1192413 1193643 := bstep (se 1 (by rfl) ⟨895232, by rfl⟩ : syracuseStep 1193643 = 1790465) B1790465
theorem B1193655 : Blo 1192413 1193655 := bstep (se 1 (by rfl) ⟨895241, by rfl⟩ : syracuseStep 1193655 = 1790483) B1790483
theorem B2684609 : Blo 1192413 2684609 := bstep (se 2 (by rfl) ⟨1006728, by rfl⟩ : syracuseStep 2684609 = 2013457) B2013457
theorem B1193675 : Blo 1192413 1193675 := bstep (se 1 (by rfl) ⟨895256, by rfl⟩ : syracuseStep 1193675 = 1790513) B1790513
theorem B1193687 : Blo 1192413 1193687 := bstep (se 1 (by rfl) ⟨895265, by rfl⟩ : syracuseStep 1193687 = 1790531) B1790531
theorem B3823321 : Blo 1192413 3823321 := bstep (se 2 (by rfl) ⟨1433745, by rfl⟩ : syracuseStep 3823321 = 2867491) B2867491
theorem B2266841 : Blo 1192413 2266841 := bstep (se 2 (by rfl) ⟨850065, by rfl⟩ : syracuseStep 2266841 = 1700131) B1700131
theorem B1193707 : Blo 1192413 1193707 := bstep (se 1 (by rfl) ⟨895280, by rfl⟩ : syracuseStep 1193707 = 1790561) B1790561
theorem B1193719 : Blo 1192413 1193719 := bstep (se 1 (by rfl) ⟨895289, by rfl⟩ : syracuseStep 1193719 = 1790579) B1790579
theorem B17209093 : Blo 1192413 17209093 := bstep (se 4 (by rfl) ⟨1613352, by rfl⟩ : syracuseStep 17209093 = 3226705) B3226705
theorem B1193739 : Blo 1192413 1193739 := bstep (se 1 (by rfl) ⟨895304, by rfl⟩ : syracuseStep 1193739 = 1790609) B1790609
theorem B10884881 : Blo 1192413 10884881 := bstep (se 2 (by rfl) ⟨4081830, by rfl⟩ : syracuseStep 10884881 = 8163661) B8163661
theorem B2012951 : Blo 1192413 2012951 := bstep (se 1 (by rfl) ⟨1509713, by rfl⟩ : syracuseStep 2012951 = 3019427) B3019427
theorem B4028183 : Blo 1192413 4028183 := bstep (se 1 (by rfl) ⟨3021137, by rfl⟩ : syracuseStep 4028183 = 6042275) B6042275
theorem B1193751 : Blo 1192413 1193751 := bstep (se 1 (by rfl) ⟨895313, by rfl⟩ : syracuseStep 1193751 = 1790627) B1790627
theorem B1193771 : Blo 1192413 1193771 := bstep (se 1 (by rfl) ⟨895328, by rfl⟩ : syracuseStep 1193771 = 1790657) B1790657
theorem B1193783 : Blo 1192413 1193783 := bstep (se 1 (by rfl) ⟨895337, by rfl⟩ : syracuseStep 1193783 = 1790675) B1790675
theorem B1193803 : Blo 1192413 1193803 := bstep (se 1 (by rfl) ⟨895352, by rfl⟩ : syracuseStep 1193803 = 1790705) B1790705
theorem B1193815 : Blo 1192413 1193815 := bstep (se 1 (by rfl) ⟨895361, by rfl⟩ : syracuseStep 1193815 = 1790723) B1790723
theorem B61962083 : Blo 1192413 61962083 := bstep (se 1 (by rfl) ⟨46471562, by rfl⟩ : syracuseStep 61962083 = 92943125) B92943125
theorem B1193835 : Blo 1192413 1193835 := bstep (se 1 (by rfl) ⟨895376, by rfl⟩ : syracuseStep 1193835 = 1790753) B1790753
theorem B1193847 : Blo 1192413 1193847 := bstep (se 1 (by rfl) ⟨895385, by rfl⟩ : syracuseStep 1193847 = 1790771) B1790771
theorem B1193867 : Blo 1192413 1193867 := bstep (se 1 (by rfl) ⟨895400, by rfl⟩ : syracuseStep 1193867 = 1790801) B1790801
theorem B2013079 : Blo 1192413 2013079 := bstep (se 1 (by rfl) ⟨1509809, by rfl⟩ : syracuseStep 2013079 = 3019619) B3019619
theorem B10196887 : Blo 1192413 10196887 := bstep (se 1 (by rfl) ⟨7647665, by rfl⟩ : syracuseStep 10196887 = 15295331) B15295331
theorem B2684825 : Blo 1192413 2684825 := bstep (se 2 (by rfl) ⟨1006809, by rfl⟩ : syracuseStep 2684825 = 2013619) B2013619
theorem B1193879 : Blo 1192413 1193879 := bstep (se 1 (by rfl) ⟨895409, by rfl⟩ : syracuseStep 1193879 = 1790819) B1790819
theorem B1193899 : Blo 1192413 1193899 := bstep (se 1 (by rfl) ⟨895424, by rfl⟩ : syracuseStep 1193899 = 1790849) B1790849
theorem B3020723 : Blo 1192413 3020723 := bstep (se 1 (by rfl) ⟨2265542, by rfl⟩ : syracuseStep 3020723 = 4531085) B4531085
theorem B6043571 : Blo 1192413 6043571 := bstep (se 1 (by rfl) ⟨4532678, by rfl⟩ : syracuseStep 6043571 = 9065357) B9065357
theorem B1193911 : Blo 1192413 1193911 := bstep (se 1 (by rfl) ⟨895433, by rfl⟩ : syracuseStep 1193911 = 1790867) B1790867
theorem B1193931 : Blo 1192413 1193931 := bstep (se 1 (by rfl) ⟨895448, by rfl⟩ : syracuseStep 1193931 = 1790897) B1790897
theorem B1193943 : Blo 1192413 1193943 := bstep (se 1 (by rfl) ⟨895457, by rfl⟩ : syracuseStep 1193943 = 1790915) B1790915
theorem B1193963 : Blo 1192413 1193963 := bstep (se 1 (by rfl) ⟨895472, by rfl⟩ : syracuseStep 1193963 = 1790945) B1790945
theorem B2684915 : Blo 1192413 2684915 := bstep (se 1 (by rfl) ⟨2013686, by rfl⟩ : syracuseStep 2684915 = 4027373) B4027373
theorem B1193975 : Blo 1192413 1193975 := bstep (se 1 (by rfl) ⟨895481, by rfl⟩ : syracuseStep 1193975 = 1790963) B1790963
theorem B1193995 : Blo 1192413 1193995 := bstep (se 1 (by rfl) ⟨895496, by rfl⟩ : syracuseStep 1193995 = 1790993) B1790993
theorem B2684951 : Blo 1192413 2684951 := bstep (se 1 (by rfl) ⟨2013713, by rfl⟩ : syracuseStep 2684951 = 4027427) B4027427
theorem B1194007 : Blo 1192413 1194007 := bstep (se 1 (by rfl) ⟨895505, by rfl⟩ : syracuseStep 1194007 = 1791011) B1791011
theorem B6797357 : Blo 1192413 6797357 := bstep (se 3 (by rfl) ⟨1274504, by rfl⟩ : syracuseStep 6797357 = 2549009) B2549009
theorem B1194027 : Blo 1192413 1194027 := bstep (se 1 (by rfl) ⟨895520, by rfl⟩ : syracuseStep 1194027 = 1791041) B1791041
theorem B1194039 : Blo 1192413 1194039 := bstep (se 1 (by rfl) ⟨895529, by rfl⟩ : syracuseStep 1194039 = 1791059) B1791059
theorem B1194059 : Blo 1192413 1194059 := bstep (se 1 (by rfl) ⟨895544, by rfl⟩ : syracuseStep 1194059 = 1791089) B1791089
theorem B1194071 : Blo 1192413 1194071 := bstep (se 1 (by rfl) ⟨895553, by rfl⟩ : syracuseStep 1194071 = 1791107) B1791107
theorem B4298845 : Blo 1192413 4298845 := bstep (se 3 (by rfl) ⟨806033, by rfl⟩ : syracuseStep 4298845 = 1612067) B1612067
theorem B1194091 : Blo 1192413 1194091 := bstep (se 1 (by rfl) ⟨895568, by rfl⟩ : syracuseStep 1194091 = 1791137) B1791137
theorem B1194103 : Blo 1192413 1194103 := bstep (se 1 (by rfl) ⟨895577, by rfl⟩ : syracuseStep 1194103 = 1791155) B1791155
theorem B1194123 : Blo 1192413 1194123 := bstep (se 1 (by rfl) ⟨895592, by rfl⟩ : syracuseStep 1194123 = 1791185) B1791185
theorem B1194135 : Blo 1192413 1194135 := bstep (se 1 (by rfl) ⟨895601, by rfl⟩ : syracuseStep 1194135 = 1791203) B1791203
theorem B1194155 : Blo 1192413 1194155 := bstep (se 1 (by rfl) ⟨895616, by rfl⟩ : syracuseStep 1194155 = 1791233) B1791233
theorem B1194167 : Blo 1192413 1194167 := bstep (se 1 (by rfl) ⟨895625, by rfl⟩ : syracuseStep 1194167 = 1791251) B1791251
theorem B1341643 : Blo 1192413 1341643 := bstep (se 1 (by rfl) ⟨1006232, by rfl⟩ : syracuseStep 1341643 = 2012465) B2012465
theorem B2685131 : Blo 1192413 2685131 := bstep (se 1 (by rfl) ⟨2013848, by rfl⟩ : syracuseStep 2685131 = 4027697) B4027697
theorem B18381005 : Blo 1192413 18381005 := bstep (se 3 (by rfl) ⟨3446438, by rfl⟩ : syracuseStep 18381005 = 6892877) B6892877
theorem B1194187 : Blo 1192413 1194187 := bstep (se 1 (by rfl) ⟨895640, by rfl⟩ : syracuseStep 1194187 = 1791281) B1791281
theorem B1194199 : Blo 1192413 1194199 := bstep (se 1 (by rfl) ⟨895649, by rfl⟩ : syracuseStep 1194199 = 1791299) B1791299
theorem B1194219 : Blo 1192413 1194219 := bstep (se 1 (by rfl) ⟨895664, by rfl⟩ : syracuseStep 1194219 = 1791329) B1791329
theorem B1194231 : Blo 1192413 1194231 := bstep (se 1 (by rfl) ⟨895673, by rfl⟩ : syracuseStep 1194231 = 1791347) B1791347
theorem B2685185 : Blo 1192413 2685185 := bstep (se 2 (by rfl) ⟨1006944, by rfl⟩ : syracuseStep 2685185 = 2013889) B2013889
theorem B1194251 : Blo 1192413 1194251 := bstep (se 1 (by rfl) ⟨895688, by rfl⟩ : syracuseStep 1194251 = 1791377) B1791377
theorem B1194263 : Blo 1192413 1194263 := bstep (se 1 (by rfl) ⟨895697, by rfl⟩ : syracuseStep 1194263 = 1791395) B1791395
theorem B1194283 : Blo 1192413 1194283 := bstep (se 1 (by rfl) ⟨895712, by rfl⟩ : syracuseStep 1194283 = 1791425) B1791425
theorem B4028723 : Blo 1192413 4028723 := bstep (se 1 (by rfl) ⟨3021542, by rfl⟩ : syracuseStep 4028723 = 6043085) B6043085
theorem B1341751 : Blo 1192413 1341751 := bstep (se 1 (by rfl) ⟨1006313, by rfl⟩ : syracuseStep 1341751 = 2012627) B2012627
theorem B1194295 : Blo 1192413 1194295 := bstep (se 1 (by rfl) ⟨895721, by rfl⟩ : syracuseStep 1194295 = 1791443) B1791443
theorem B1194315 : Blo 1192413 1194315 := bstep (se 1 (by rfl) ⟨895736, by rfl⟩ : syracuseStep 1194315 = 1791473) B1791473
theorem B1194327 : Blo 1192413 1194327 := bstep (se 1 (by rfl) ⟨895745, by rfl⟩ : syracuseStep 1194327 = 1791491) B1791491
theorem B1194347 : Blo 1192413 1194347 := bstep (se 1 (by rfl) ⟨895760, by rfl⟩ : syracuseStep 1194347 = 1791521) B1791521
theorem B1194359 : Blo 1192413 1194359 := bstep (se 1 (by rfl) ⟨895769, by rfl⟩ : syracuseStep 1194359 = 1791539) B1791539
theorem B1194379 : Blo 1192413 1194379 := bstep (se 1 (by rfl) ⟨895784, by rfl⟩ : syracuseStep 1194379 = 1791569) B1791569
theorem B1194391 : Blo 1192413 1194391 := bstep (se 1 (by rfl) ⟨895793, by rfl⟩ : syracuseStep 1194391 = 1791587) B1791587
theorem B1194411 : Blo 1192413 1194411 := bstep (se 1 (by rfl) ⟨895808, by rfl⟩ : syracuseStep 1194411 = 1791617) B1791617
theorem B3021259 : Blo 1192413 3021259 := bstep (se 1 (by rfl) ⟨2265944, by rfl⟩ : syracuseStep 3021259 = 4531889) B4531889
theorem B2685401 : Blo 1192413 2685401 := bstep (se 2 (by rfl) ⟨1007025, by rfl⟩ : syracuseStep 2685401 = 2014051) B2014051
theorem B1341931 : Blo 1192413 1341931 := bstep (se 1 (by rfl) ⟨1006448, by rfl⟩ : syracuseStep 1341931 = 2012897) B2012897
theorem B2013707 : Blo 1192413 2013707 := bstep (se 1 (by rfl) ⟨1510280, by rfl⟩ : syracuseStep 2013707 = 3020561) B3020561
theorem B2685491 : Blo 1192413 2685491 := bstep (se 1 (by rfl) ⟨2014118, by rfl⟩ : syracuseStep 2685491 = 4028237) B4028237
theorem B4028993 : Blo 1192413 4028993 := bstep (se 2 (by rfl) ⟨1510872, by rfl⟩ : syracuseStep 4028993 = 3021745) B3021745
theorem B1342039 : Blo 1192413 1342039 := bstep (se 1 (by rfl) ⟨1006529, by rfl⟩ : syracuseStep 1342039 = 2013059) B2013059
theorem B2685527 : Blo 1192413 2685527 := bstep (se 1 (by rfl) ⟨2014145, by rfl⟩ : syracuseStep 2685527 = 4028291) B4028291
theorem B3021401 : Blo 1192413 3021401 := bstep (se 2 (by rfl) ⟨1133025, by rfl⟩ : syracuseStep 3021401 = 2266051) B2266051
theorem B8600165 : Blo 1192413 8600165 := bstep (se 4 (by rfl) ⟨806265, by rfl⟩ : syracuseStep 8600165 = 1612531) B1612531
theorem B2013835 : Blo 1192413 2013835 := bstep (se 1 (by rfl) ⟨1510376, by rfl⟩ : syracuseStep 2013835 = 3020753) B3020753
theorem B1342219 : Blo 1192413 1342219 := bstep (se 1 (by rfl) ⟨1006664, by rfl⟩ : syracuseStep 1342219 = 2013329) B2013329
theorem B2685707 : Blo 1192413 2685707 := bstep (se 1 (by rfl) ⟨2014280, by rfl⟩ : syracuseStep 2685707 = 4028561) B4028561
theorem B2013977 : Blo 1192413 2013977 := bstep (se 2 (by rfl) ⟨755241, by rfl⟩ : syracuseStep 2013977 = 1510483) B1510483
theorem B2685761 : Blo 1192413 2685761 := bstep (se 2 (by rfl) ⟨1007160, by rfl⟩ : syracuseStep 2685761 = 2014321) B2014321
theorem B1342327 : Blo 1192413 1342327 := bstep (se 1 (by rfl) ⟨1006745, by rfl⟩ : syracuseStep 1342327 = 2013491) B2013491
theorem B2014105 : Blo 1192413 2014105 := bstep (se 2 (by rfl) ⟨755289, by rfl⟩ : syracuseStep 2014105 = 1510579) B1510579
theorem B7748531 : Blo 1192413 7748531 := bstep (se 1 (by rfl) ⟨5811398, by rfl⟩ : syracuseStep 7748531 = 11622797) B11622797
theorem B1612759 : Blo 1192413 1612759 := bstep (se 1 (by rfl) ⟨1209569, by rfl⟩ : syracuseStep 1612759 = 2419139) B2419139
theorem B4529155 : Blo 1192413 4529155 := bstep (se 1 (by rfl) ⟨3396866, by rfl⟩ : syracuseStep 4529155 = 6793733) B6793733
theorem B2546711 : Blo 1192413 2546711 := bstep (se 1 (by rfl) ⟨1910033, by rfl⟩ : syracuseStep 2546711 = 3820067) B3820067
theorem B2685977 : Blo 1192413 2685977 := bstep (se 2 (by rfl) ⟨1007241, by rfl⟩ : syracuseStep 2685977 = 2014483) B2014483
theorem B1342507 : Blo 1192413 1342507 := bstep (se 1 (by rfl) ⟨1006880, by rfl⟩ : syracuseStep 1342507 = 2013761) B2013761
theorem B4029533 : Blo 1192413 4029533 := bstep (se 3 (by rfl) ⟨755537, by rfl⟩ : syracuseStep 4029533 = 1511075) B1511075
theorem B2686067 : Blo 1192413 2686067 := bstep (se 1 (by rfl) ⟨2014550, by rfl⟩ : syracuseStep 2686067 = 4029101) B4029101
theorem B1342615 : Blo 1192413 1342615 := bstep (se 1 (by rfl) ⟨1006961, by rfl⟩ : syracuseStep 1342615 = 2013923) B2013923
theorem B2686103 : Blo 1192413 2686103 := bstep (se 1 (by rfl) ⟨2014577, by rfl⟩ : syracuseStep 2686103 = 4029155) B4029155
theorem B4529459 : Blo 1192413 4529459 := bstep (se 1 (by rfl) ⟨3397094, by rfl⟩ : syracuseStep 4529459 = 6794189) B6794189
theorem B10894657 : Blo 1192413 10894657 := bstep (se 2 (by rfl) ⟨4085496, by rfl⟩ : syracuseStep 10894657 = 8170993) B8170993
theorem B1342795 : Blo 1192413 1342795 := bstep (se 1 (by rfl) ⟨1007096, by rfl⟩ : syracuseStep 1342795 = 2014193) B2014193
theorem B2686283 : Blo 1192413 2686283 := bstep (se 1 (by rfl) ⟨2014712, by rfl⟩ : syracuseStep 2686283 = 4029425) B4029425
theorem B2686337 : Blo 1192413 2686337 := bstep (se 2 (by rfl) ⟨1007376, by rfl⟩ : syracuseStep 2686337 = 2014753) B2014753
theorem B3022231 : Blo 1192413 3022231 := bstep (se 1 (by rfl) ⟨2266673, by rfl⟩ : syracuseStep 3022231 = 4533347) B4533347
theorem B2907571 : Blo 1192413 2907571 := bstep (se 1 (by rfl) ⟨2180678, by rfl⟩ : syracuseStep 2907571 = 4361357) B4361357
theorem B1342903 : Blo 1192413 1342903 := bstep (se 1 (by rfl) ⟨1007177, by rfl⟩ : syracuseStep 1342903 = 2014355) B2014355
theorem B2014679 : Blo 1192413 2014679 := bstep (se 1 (by rfl) ⟨1511009, by rfl⟩ : syracuseStep 2014679 = 3022019) B3022019
theorem B3399191 : Blo 1192413 3399191 := bstep (se 1 (by rfl) ⟨2549393, by rfl⟩ : syracuseStep 3399191 = 5098787) B5098787
theorem B2014807 : Blo 1192413 2014807 := bstep (se 1 (by rfl) ⟨1511105, by rfl⟩ : syracuseStep 2014807 = 3022211) B3022211
theorem B2686553 : Blo 1192413 2686553 := bstep (se 2 (by rfl) ⟨1007457, by rfl⟩ : syracuseStep 2686553 = 2014915) B2014915
theorem B1343083 : Blo 1192413 1343083 := bstep (se 1 (by rfl) ⟨1007312, by rfl⟩ : syracuseStep 1343083 = 2014625) B2014625
theorem B1433227 : Blo 1192413 1433227 := bstep (se 1 (by rfl) ⟨1074920, by rfl⟩ : syracuseStep 1433227 = 2149841) B2149841
theorem B2686643 : Blo 1192413 2686643 := bstep (se 1 (by rfl) ⟨2014982, by rfl⟩ : syracuseStep 2686643 = 4029965) B4029965
theorem B1343191 : Blo 1192413 1343191 := bstep (se 1 (by rfl) ⟨1007393, by rfl⟩ : syracuseStep 1343191 = 2014787) B2014787
theorem B2686679 : Blo 1192413 2686679 := bstep (se 1 (by rfl) ⟨2015009, by rfl⟩ : syracuseStep 2686679 = 4030019) B4030019
theorem B3825473 : Blo 1192413 3825473 := bstep (se 2 (by rfl) ⟨1434552, by rfl⟩ : syracuseStep 3825473 = 2869105) B2869105
theorem B3022667 : Blo 1192413 3022667 := bstep (se 1 (by rfl) ⟨2267000, by rfl⟩ : syracuseStep 3022667 = 4534001) B4534001
theorem B6045515 : Blo 1192413 6045515 := bstep (se 1 (by rfl) ⟨4534136, by rfl⟩ : syracuseStep 6045515 = 9068273) B9068273
theorem B3227485 : Blo 1192413 3227485 := bstep (se 3 (by rfl) ⟨605153, by rfl⟩ : syracuseStep 3227485 = 1210307) B1210307
theorem B1343371 : Blo 1192413 1343371 := bstep (se 1 (by rfl) ⟨1007528, by rfl⟩ : syracuseStep 1343371 = 2015057) B2015057
theorem B2686859 : Blo 1192413 2686859 := bstep (se 1 (by rfl) ⟨2015144, by rfl⟩ : syracuseStep 2686859 = 4030289) B4030289
theorem B4530113 : Blo 1192413 4530113 := bstep (se 2 (by rfl) ⟨1698792, by rfl⟩ : syracuseStep 4530113 = 3397585) B3397585
theorem B2686913 : Blo 1192413 2686913 := bstep (se 2 (by rfl) ⟨1007592, by rfl⟩ : syracuseStep 2686913 = 2015185) B2015185
theorem B5439449 : Blo 1192413 5439449 := bstep (se 2 (by rfl) ⟨2039793, by rfl⟩ : syracuseStep 5439449 = 4079587) B4079587
theorem B1343479 : Blo 1192413 1343479 := bstep (se 1 (by rfl) ⟨1007609, by rfl⟩ : syracuseStep 1343479 = 2015219) B2015219
theorem B3022859 : Blo 1192413 3022859 := bstep (se 1 (by rfl) ⟨2267144, by rfl⟩ : syracuseStep 3022859 = 4534289) B4534289
theorem B13598765 : Blo 1192413 13598765 := bstep (se 3 (by rfl) ⟨2549768, by rfl⟩ : syracuseStep 13598765 = 5099537) B5099537
theorem B2687111 : Blo 1192413 2687111 := bstep (se 1 (by rfl) ⟨2015333, by rfl⟩ : syracuseStep 2687111 = 4030667) B4030667
theorem B1343623 : Blo 1192413 1343623 := bstep (se 1 (by rfl) ⟨1007717, by rfl⟩ : syracuseStep 1343623 = 2015435) B2015435
theorem B4030721 : Blo 1192413 4030721 := bstep (se 2 (by rfl) ⟨1511520, by rfl⟩ : syracuseStep 4030721 = 3023041) B3023041
theorem B3399965 : Blo 1192413 3399965 := bstep (se 3 (by rfl) ⟨637493, by rfl⟩ : syracuseStep 3399965 = 1274987) B1274987
theorem B2687291 : Blo 1192413 2687291 := bstep (se 1 (by rfl) ⟨2015468, by rfl⟩ : syracuseStep 2687291 = 4030937) B4030937
theorem B13582727 : Blo 1192413 13582727 := bstep (se 1 (by rfl) ⟨10187045, by rfl⟩ : syracuseStep 13582727 = 20374091) B20374091
theorem B9183623 : Blo 1192413 9183623 := bstep (se 1 (by rfl) ⟨6887717, by rfl⟩ : syracuseStep 9183623 = 13775435) B13775435
theorem B2687417 : Blo 1192413 2687417 := bstep (se 2 (by rfl) ⟨1007781, by rfl⟩ : syracuseStep 2687417 = 2015563) B2015563
theorem B12894673 : Blo 1192413 12894673 := bstep (se 2 (by rfl) ⟨4835502, by rfl⟩ : syracuseStep 12894673 = 9671005) B9671005
theorem B77406677 : Blo 1192413 77406677 := bstep (se 7 (by rfl) ⟨907109, by rfl⟩ : syracuseStep 77406677 = 1814219) B1814219
theorem B3400193 : Blo 1192413 3400193 := bstep (se 2 (by rfl) ⟨1275072, by rfl⟩ : syracuseStep 3400193 = 2550145) B2550145
theorem B9060983 : Blo 1192413 9060983 := bstep (se 1 (by rfl) ⟨6795737, by rfl⟩ : syracuseStep 9060983 = 13591475) B13591475
theorem B1360519 : Blo 1192413 1360519 := bstep (se 1 (by rfl) ⟨1020389, by rfl⟩ : syracuseStep 1360519 = 2040779) B2040779
theorem B3400535 : Blo 1192413 3400535 := bstep (se 1 (by rfl) ⟨2550401, by rfl⟩ : syracuseStep 3400535 = 5100803) B5100803
theorem B6038387 : Blo 1192413 6038387 := bstep (se 1 (by rfl) ⟨4528790, by rfl⟩ : syracuseStep 6038387 = 9057581) B9057581
theorem B6456179 : Blo 1192413 6456179 := bstep (se 1 (by rfl) ⟨4842134, by rfl⟩ : syracuseStep 6456179 = 9684269) B9684269
theorem B6800273 : Blo 1192413 6800273 := bstep (se 2 (by rfl) ⟨2550102, by rfl⟩ : syracuseStep 6800273 = 5100205) B5100205
theorem B30983093 : Blo 1192413 30983093 := bstep (se 5 (by rfl) ⟨1452332, by rfl⟩ : syracuseStep 30983093 = 2904665) B2904665
theorem B6046649 : Blo 1192413 6046649 := bstep (se 2 (by rfl) ⟨2267493, by rfl⟩ : syracuseStep 6046649 = 4534987) B4534987
theorem B3400649 : Blo 1192413 3400649 := bstep (se 2 (by rfl) ⟨1275243, by rfl⟩ : syracuseStep 3400649 = 2550487) B2550487
theorem B12907127 : Blo 1192413 12907127 := bstep (se 1 (by rfl) ⟨9680345, by rfl⟩ : syracuseStep 12907127 = 19360691) B19360691
theorem B5809175 : Blo 1192413 5809175 := bstep (se 1 (by rfl) ⟨4356881, by rfl⟩ : syracuseStep 5809175 = 8713763) B8713763
theorem B2393147 : Blo 1192413 2393147 := bstep (se 1 (by rfl) ⟨1794860, by rfl⟩ : syracuseStep 2393147 = 3589721) B3589721
theorem B1721417 : Blo 1192413 1721417 := bstep (se 2 (by rfl) ⟨645531, by rfl⟩ : syracuseStep 1721417 = 1291063) B1291063
theorem B6038873 : Blo 1192413 6038873 := bstep (se 2 (by rfl) ⟨2264577, by rfl⟩ : syracuseStep 6038873 = 4529155) B4529155
theorem B4531571 : Blo 1192413 4531571 := bstep (se 1 (by rfl) ⟨3398678, by rfl⟩ : syracuseStep 4531571 = 6797357) B6797357
theorem B13788701 : Blo 1192413 13788701 := bstep (se 3 (by rfl) ⟨2585381, by rfl⟩ : syracuseStep 13788701 = 5170763) B5170763
theorem B9061955 : Blo 1192413 9061955 := bstep (se 1 (by rfl) ⟨6796466, by rfl⟩ : syracuseStep 9061955 = 13592933) B13592933
theorem B30574259 : Blo 1192413 30574259 := bstep (se 1 (by rfl) ⟨22930694, by rfl⟩ : syracuseStep 30574259 = 45861389) B45861389
theorem B14526209 : Blo 1192413 14526209 := bstep (se 2 (by rfl) ⟨5447328, by rfl⟩ : syracuseStep 14526209 = 10894657) B10894657
theorem B5736251 : Blo 1192413 5736251 := bstep (se 1 (by rfl) ⟨4302188, by rfl⟩ : syracuseStep 5736251 = 8604377) B8604377
theorem B56641355 : Blo 1192413 56641355 := bstep (se 1 (by rfl) ⟨42481016, by rfl⟩ : syracuseStep 56641355 = 84962033) B84962033
theorem B3876761 : Blo 1192413 3876761 := bstep (se 2 (by rfl) ⟨1453785, by rfl⟩ : syracuseStep 3876761 = 2907571) B2907571
theorem B1697807 : Blo 1192413 1697807 := bstep (se 1 (by rfl) ⟨1273355, by rfl⟩ : syracuseStep 1697807 = 2546711) B2546711
theorem B1509511 : Blo 1192413 1509511 := bstep (se 1 (by rfl) ⟨1132133, by rfl⟩ : syracuseStep 1509511 = 2264267) B2264267
theorem B10201261 : Blo 1192413 10201261 := bstep (se 3 (by rfl) ⟨1912736, by rfl⟩ : syracuseStep 10201261 = 3825473) B3825473
theorem B1910969 : Blo 1192413 1910969 := bstep (se 2 (by rfl) ⟨716613, by rfl⟩ : syracuseStep 1910969 = 1433227) B1433227
theorem B11634961 : Blo 1192413 11634961 := bstep (se 2 (by rfl) ⟨4363110, by rfl⟩ : syracuseStep 11634961 = 8726221) B8726221
theorem B5097761 : Blo 1192413 5097761 := bstep (se 2 (by rfl) ⟨1911660, by rfl⟩ : syracuseStep 5097761 = 3823321) B3823321
theorem B4303313 : Blo 1192413 4303313 := bstep (se 2 (by rfl) ⟨1613742, by rfl⟩ : syracuseStep 4303313 = 3227485) B3227485
theorem B1509931 : Blo 1192413 1509931 := bstep (se 1 (by rfl) ⟨1132448, by rfl⟩ : syracuseStep 1509931 = 2264897) B2264897
theorem B11635265 : Blo 1192413 11635265 := bstep (se 2 (by rfl) ⟨4363224, by rfl⟩ : syracuseStep 11635265 = 8726449) B8726449
theorem B5098103 : Blo 1192413 5098103 := bstep (se 1 (by rfl) ⟨3823577, by rfl⟩ : syracuseStep 5098103 = 7647155) B7647155
theorem B1510159 : Blo 1192413 1510159 := bstep (se 1 (by rfl) ⟨1132619, by rfl⟩ : syracuseStep 1510159 = 2265239) B2265239
theorem B9186085 : Blo 1192413 9186085 := bstep (se 4 (by rfl) ⟨861195, by rfl⟩ : syracuseStep 9186085 = 1722391) B1722391
theorem B1788731 : Blo 1192413 1788731 := bstep (se 1 (by rfl) ⟨1341548, by rfl⟩ : syracuseStep 1788731 = 2683097) B2683097
theorem B9677657 : Blo 1192413 9677657 := bstep (se 2 (by rfl) ⟨3629121, by rfl⟩ : syracuseStep 9677657 = 7258243) B7258243
theorem B1788791 : Blo 1192413 1788791 := bstep (se 1 (by rfl) ⟨1341593, by rfl⟩ : syracuseStep 1788791 = 2683187) B2683187
theorem B1788815 : Blo 1192413 1788815 := bstep (se 1 (by rfl) ⟨1341611, by rfl⟩ : syracuseStep 1788815 = 2683223) B2683223
theorem B1788857 : Blo 1192413 1788857 := bstep (se 2 (by rfl) ⟨670821, by rfl⟩ : syracuseStep 1788857 = 1341643) B1341643
theorem B2042825 : Blo 1192413 2042825 := bstep (se 2 (by rfl) ⟨766059, by rfl⟩ : syracuseStep 2042825 = 1532119) B1532119
theorem B1788935 : Blo 1192413 1788935 := bstep (se 1 (by rfl) ⟨1341701, by rfl⟩ : syracuseStep 1788935 = 2683403) B2683403
theorem B7646231 : Blo 1192413 7646231 := bstep (se 1 (by rfl) ⟨5734673, by rfl⟩ : syracuseStep 7646231 = 11469347) B11469347
theorem B2264107 : Blo 1192413 2264107 := bstep (se 1 (by rfl) ⟨1698080, by rfl⟩ : syracuseStep 2264107 = 3396161) B3396161
theorem B1788971 : Blo 1192413 1788971 := bstep (se 1 (by rfl) ⟨1341728, by rfl⟩ : syracuseStep 1788971 = 2683457) B2683457
theorem B1789001 : Blo 1192413 1789001 := bstep (se 2 (by rfl) ⟨670875, by rfl⟩ : syracuseStep 1789001 = 1341751) B1341751
theorem B1698889 : Blo 1192413 1698889 := bstep (se 2 (by rfl) ⟨637083, by rfl⟩ : syracuseStep 1698889 = 1274167) B1274167
theorem B2264183 : Blo 1192413 2264183 := bstep (se 1 (by rfl) ⟨1698137, by rfl⟩ : syracuseStep 2264183 = 3396275) B3396275
theorem B1789115 : Blo 1192413 1789115 := bstep (se 1 (by rfl) ⟨1341836, by rfl⟩ : syracuseStep 1789115 = 2683673) B2683673
theorem B1699003 : Blo 1192413 1699003 := bstep (se 1 (by rfl) ⟨1274252, by rfl⟩ : syracuseStep 1699003 = 2548505) B2548505
theorem B6794441 : Blo 1192413 6794441 := bstep (se 2 (by rfl) ⟨2547915, by rfl⟩ : syracuseStep 6794441 = 5095831) B5095831
theorem B1789175 : Blo 1192413 1789175 := bstep (se 1 (by rfl) ⟨1341881, by rfl⟩ : syracuseStep 1789175 = 2683763) B2683763
theorem B1789199 : Blo 1192413 1789199 := bstep (se 1 (by rfl) ⟨1341899, by rfl⟩ : syracuseStep 1789199 = 2683799) B2683799
theorem B1789241 : Blo 1192413 1789241 := bstep (se 2 (by rfl) ⟨670965, by rfl⟩ : syracuseStep 1789241 = 1341931) B1341931
theorem B1789319 : Blo 1192413 1789319 := bstep (se 1 (by rfl) ⟨1341989, by rfl⟩ : syracuseStep 1789319 = 2683979) B2683979
theorem B1813903 : Blo 1192413 1813903 := bstep (se 1 (by rfl) ⟨1360427, by rfl⟩ : syracuseStep 1813903 = 2720855) B2720855
theorem B6040979 : Blo 1192413 6040979 := bstep (se 1 (by rfl) ⟨4530734, by rfl⟩ : syracuseStep 6040979 = 9061469) B9061469
theorem B4025753 : Blo 1192413 4025753 := bstep (se 2 (by rfl) ⟨1509657, by rfl⟩ : syracuseStep 4025753 = 3019315) B3019315
theorem B1789355 : Blo 1192413 1789355 := bstep (se 1 (by rfl) ⟨1342016, by rfl⟩ : syracuseStep 1789355 = 2684033) B2684033
theorem B1789385 : Blo 1192413 1789385 := bstep (se 2 (by rfl) ⟨671019, by rfl⟩ : syracuseStep 1789385 = 1342039) B1342039
theorem B1510903 : Blo 1192413 1510903 := bstep (se 1 (by rfl) ⟨1133177, by rfl⟩ : syracuseStep 1510903 = 2266355) B2266355
theorem B4533803 : Blo 1192413 4533803 := bstep (se 1 (by rfl) ⟨3400352, by rfl⟩ : syracuseStep 4533803 = 6800705) B6800705
theorem B1789499 : Blo 1192413 1789499 := bstep (se 1 (by rfl) ⟨1342124, by rfl⟩ : syracuseStep 1789499 = 2684249) B2684249
theorem B1789559 : Blo 1192413 1789559 := bstep (se 1 (by rfl) ⟨1342169, by rfl⟩ : syracuseStep 1789559 = 2684339) B2684339
theorem B1789583 : Blo 1192413 1789583 := bstep (se 1 (by rfl) ⟨1342187, by rfl⟩ : syracuseStep 1789583 = 2684375) B2684375
theorem B2420371 : Blo 1192413 2420371 := bstep (se 1 (by rfl) ⟨1815278, by rfl⟩ : syracuseStep 2420371 = 3630557) B3630557
theorem B1789625 : Blo 1192413 1789625 := bstep (se 2 (by rfl) ⟨671109, by rfl⟩ : syracuseStep 1789625 = 1342219) B1342219
theorem B1789703 : Blo 1192413 1789703 := bstep (se 1 (by rfl) ⟨1342277, by rfl⟩ : syracuseStep 1789703 = 2684555) B2684555
theorem B1838863 : Blo 1192413 1838863 := bstep (se 1 (by rfl) ⟨1379147, by rfl⟩ : syracuseStep 1838863 = 2758295) B2758295
theorem B1814287 : Blo 1192413 1814287 := bstep (se 1 (by rfl) ⟨1360715, by rfl⟩ : syracuseStep 1814287 = 2721431) B2721431
theorem B1789739 : Blo 1192413 1789739 := bstep (se 1 (by rfl) ⟨1342304, by rfl⟩ : syracuseStep 1789739 = 2684609) B2684609
theorem B1511227 : Blo 1192413 1511227 := bstep (se 1 (by rfl) ⟨1133420, by rfl⟩ : syracuseStep 1511227 = 2266841) B2266841
theorem B1789769 : Blo 1192413 1789769 := bstep (se 2 (by rfl) ⟨671163, by rfl⟩ : syracuseStep 1789769 = 1342327) B1342327
theorem B12922739 : Blo 1192413 12922739 := bstep (se 1 (by rfl) ⟨9692054, by rfl⟩ : syracuseStep 12922739 = 19384109) B19384109
theorem B41308055 : Blo 1192413 41308055 := bstep (se 1 (by rfl) ⟨30981041, by rfl⟩ : syracuseStep 41308055 = 61962083) B61962083
theorem B1789883 : Blo 1192413 1789883 := bstep (se 1 (by rfl) ⟨1342412, by rfl⟩ : syracuseStep 1789883 = 2684825) B2684825
theorem B2150345 : Blo 1192413 2150345 := bstep (se 2 (by rfl) ⟨806379, by rfl⟩ : syracuseStep 2150345 = 1612759) B1612759
theorem B1789943 : Blo 1192413 1789943 := bstep (se 1 (by rfl) ⟨1342457, by rfl⟩ : syracuseStep 1789943 = 2684915) B2684915
theorem B1789967 : Blo 1192413 1789967 := bstep (se 1 (by rfl) ⟨1342475, by rfl⟩ : syracuseStep 1789967 = 2684951) B2684951
theorem B8171543 : Blo 1192413 8171543 := bstep (se 1 (by rfl) ⟨6128657, by rfl⟩ : syracuseStep 8171543 = 12257315) B12257315
theorem B1790009 : Blo 1192413 1790009 := bstep (se 2 (by rfl) ⟨671253, by rfl⟩ : syracuseStep 1790009 = 1342507) B1342507
theorem B1912891 : Blo 1192413 1912891 := bstep (se 1 (by rfl) ⟨1434668, by rfl⟩ : syracuseStep 1912891 = 2869337) B2869337
theorem B4026455 : Blo 1192413 4026455 := bstep (se 1 (by rfl) ⟨3019841, by rfl⟩ : syracuseStep 4026455 = 6039683) B6039683
theorem B1790087 : Blo 1192413 1790087 := bstep (se 1 (by rfl) ⟨1342565, by rfl⟩ : syracuseStep 1790087 = 2685131) B2685131
theorem B1790123 : Blo 1192413 1790123 := bstep (se 1 (by rfl) ⟨1342592, by rfl⟩ : syracuseStep 1790123 = 2685185) B2685185
theorem B1790153 : Blo 1192413 1790153 := bstep (se 2 (by rfl) ⟨671307, by rfl⟩ : syracuseStep 1790153 = 1342615) B1342615
theorem B2683151 : Blo 1192413 2683151 := bstep (se 1 (by rfl) ⟨2012363, by rfl⟩ : syracuseStep 2683151 = 4024727) B4024727
theorem B2683169 : Blo 1192413 2683169 := bstep (se 2 (by rfl) ⟨1006188, by rfl⟩ : syracuseStep 2683169 = 2012377) B2012377
theorem B1790267 : Blo 1192413 1790267 := bstep (se 1 (by rfl) ⟨1342700, by rfl⟩ : syracuseStep 1790267 = 2685401) B2685401
theorem B1913147 : Blo 1192413 1913147 := bstep (se 1 (by rfl) ⟨1434860, by rfl⟩ : syracuseStep 1913147 = 2869721) B2869721
theorem B1790327 : Blo 1192413 1790327 := bstep (se 1 (by rfl) ⟨1342745, by rfl⟩ : syracuseStep 1790327 = 2685491) B2685491
theorem B1790351 : Blo 1192413 1790351 := bstep (se 1 (by rfl) ⟨1342763, by rfl⟩ : syracuseStep 1790351 = 2685527) B2685527
theorem B1790393 : Blo 1192413 1790393 := bstep (se 2 (by rfl) ⟨671397, by rfl⟩ : syracuseStep 1790393 = 1342795) B1342795
theorem B3019265 : Blo 1192413 3019265 := bstep (se 2 (by rfl) ⟨1132224, by rfl⟩ : syracuseStep 3019265 = 2264449) B2264449
theorem B1192455 : Blo 1192413 1192455 := bstep (se 1 (by rfl) ⟨894341, by rfl⟩ : syracuseStep 1192455 = 1788683) B1788683
theorem B1790471 : Blo 1192413 1790471 := bstep (se 1 (by rfl) ⟨1342853, by rfl⟩ : syracuseStep 1790471 = 2685707) B2685707
theorem B1192463 : Blo 1192413 1192463 := bstep (se 1 (by rfl) ⟨894347, by rfl⟩ : syracuseStep 1192463 = 1788695) B1788695
theorem B23245355 : Blo 1192413 23245355 := bstep (se 1 (by rfl) ⟨17434016, by rfl⟩ : syracuseStep 23245355 = 34868033) B34868033
theorem B1790507 : Blo 1192413 1790507 := bstep (se 1 (by rfl) ⟨1342880, by rfl⟩ : syracuseStep 1790507 = 2685761) B2685761
theorem B1192507 : Blo 1192413 1192507 := bstep (se 1 (by rfl) ⟨894380, by rfl⟩ : syracuseStep 1192507 = 1788761) B1788761
theorem B4026941 : Blo 1192413 4026941 := bstep (se 3 (by rfl) ⟨755051, by rfl⟩ : syracuseStep 4026941 = 1510103) B1510103
theorem B1790537 : Blo 1192413 1790537 := bstep (se 2 (by rfl) ⟨671451, by rfl⟩ : syracuseStep 1790537 = 1342903) B1342903
theorem B2683511 : Blo 1192413 2683511 := bstep (se 1 (by rfl) ⟨2012633, by rfl⟩ : syracuseStep 2683511 = 4025267) B4025267
theorem B5165687 : Blo 1192413 5165687 := bstep (se 1 (by rfl) ⟨3874265, by rfl⟩ : syracuseStep 5165687 = 7748531) B7748531
theorem B1192583 : Blo 1192413 1192583 := bstep (se 1 (by rfl) ⟨894437, by rfl⟩ : syracuseStep 1192583 = 1788875) B1788875
theorem B1192591 : Blo 1192413 1192591 := bstep (se 1 (by rfl) ⟨894443, by rfl⟩ : syracuseStep 1192591 = 1788887) B1788887
theorem B1192635 : Blo 1192413 1192635 := bstep (se 1 (by rfl) ⟨894476, by rfl⟩ : syracuseStep 1192635 = 1788953) B1788953
theorem B1790651 : Blo 1192413 1790651 := bstep (se 1 (by rfl) ⟨1342988, by rfl⟩ : syracuseStep 1790651 = 2685977) B2685977
theorem B1790711 : Blo 1192413 1790711 := bstep (se 1 (by rfl) ⟨1343033, by rfl⟩ : syracuseStep 1790711 = 2686067) B2686067
theorem B1291015 : Blo 1192413 1291015 := bstep (se 1 (by rfl) ⟨968261, by rfl⟩ : syracuseStep 1291015 = 1936523) B1936523
theorem B1192711 : Blo 1192413 1192711 := bstep (se 1 (by rfl) ⟨894533, by rfl⟩ : syracuseStep 1192711 = 1789067) B1789067
theorem B1700615 : Blo 1192413 1700615 := bstep (se 1 (by rfl) ⟨1275461, by rfl⟩ : syracuseStep 1700615 = 2550923) B2550923
theorem B1192719 : Blo 1192413 1192719 := bstep (se 1 (by rfl) ⟨894539, by rfl⟩ : syracuseStep 1192719 = 1789079) B1789079
theorem B1790735 : Blo 1192413 1790735 := bstep (se 1 (by rfl) ⟨1343051, by rfl⟩ : syracuseStep 1790735 = 2686103) B2686103
theorem B2683691 : Blo 1192413 2683691 := bstep (se 1 (by rfl) ⟨2012768, by rfl⟩ : syracuseStep 2683691 = 4025537) B4025537
theorem B9433907 : Blo 1192413 9433907 := bstep (se 1 (by rfl) ⟨7075430, by rfl⟩ : syracuseStep 9433907 = 14150861) B14150861
theorem B1790777 : Blo 1192413 1790777 := bstep (se 2 (by rfl) ⟨671541, by rfl⟩ : syracuseStep 1790777 = 1343083) B1343083
theorem B1192763 : Blo 1192413 1192763 := bstep (se 1 (by rfl) ⟨894572, by rfl⟩ : syracuseStep 1192763 = 1789145) B1789145
theorem B6452027 : Blo 1192413 6452027 := bstep (se 1 (by rfl) ⟨4839020, by rfl⟩ : syracuseStep 6452027 = 9678041) B9678041
theorem B3019639 : Blo 1192413 3019639 := bstep (se 1 (by rfl) ⟨2264729, by rfl⟩ : syracuseStep 3019639 = 4529459) B4529459
theorem B1192839 : Blo 1192413 1192839 := bstep (se 1 (by rfl) ⟨894629, by rfl⟩ : syracuseStep 1192839 = 1789259) B1789259
theorem B1790855 : Blo 1192413 1790855 := bstep (se 1 (by rfl) ⟨1343141, by rfl⟩ : syracuseStep 1790855 = 2686283) B2686283
theorem B1192847 : Blo 1192413 1192847 := bstep (se 1 (by rfl) ⟨894635, by rfl⟩ : syracuseStep 1192847 = 1789271) B1789271
theorem B1790891 : Blo 1192413 1790891 := bstep (se 1 (by rfl) ⟨1343168, by rfl⟩ : syracuseStep 1790891 = 2686337) B2686337
theorem B1192891 : Blo 1192413 1192891 := bstep (se 1 (by rfl) ⟨894668, by rfl⟩ : syracuseStep 1192891 = 1789337) B1789337
theorem B1790921 : Blo 1192413 1790921 := bstep (se 2 (by rfl) ⟨671595, by rfl⟩ : syracuseStep 1790921 = 1343191) B1343191
theorem B1192967 : Blo 1192413 1192967 := bstep (se 1 (by rfl) ⟨894725, by rfl⟩ : syracuseStep 1192967 = 1789451) B1789451
theorem B1192975 : Blo 1192413 1192975 := bstep (se 1 (by rfl) ⟨894731, by rfl⟩ : syracuseStep 1192975 = 1789463) B1789463
theorem B2266127 : Blo 1192413 2266127 := bstep (se 1 (by rfl) ⟨1699595, by rfl⟩ : syracuseStep 2266127 = 3399191) B3399191
theorem B6796331 : Blo 1192413 6796331 := bstep (se 1 (by rfl) ⟨5097248, by rfl⟩ : syracuseStep 6796331 = 10194497) B10194497
theorem B1193019 : Blo 1192413 1193019 := bstep (se 1 (by rfl) ⟨894764, by rfl⟩ : syracuseStep 1193019 = 1789529) B1789529
theorem B1791035 : Blo 1192413 1791035 := bstep (se 1 (by rfl) ⟨1343276, by rfl⟩ : syracuseStep 1791035 = 2686553) B2686553
theorem B1791095 : Blo 1192413 1791095 := bstep (se 1 (by rfl) ⟨1343321, by rfl⟩ : syracuseStep 1791095 = 2686643) B2686643
theorem B1193095 : Blo 1192413 1193095 := bstep (se 1 (by rfl) ⟨894821, by rfl⟩ : syracuseStep 1193095 = 1789643) B1789643
theorem B1193103 : Blo 1192413 1193103 := bstep (se 1 (by rfl) ⟨894827, by rfl⟩ : syracuseStep 1193103 = 1789655) B1789655
theorem B1791119 : Blo 1192413 1791119 := bstep (se 1 (by rfl) ⟨1343339, by rfl⟩ : syracuseStep 1791119 = 2686679) B2686679
theorem B2684051 : Blo 1192413 2684051 := bstep (se 1 (by rfl) ⟨2013038, by rfl⟩ : syracuseStep 2684051 = 4026077) B4026077
theorem B1791161 : Blo 1192413 1791161 := bstep (se 2 (by rfl) ⟨671685, by rfl⟩ : syracuseStep 1791161 = 1343371) B1343371
theorem B1193147 : Blo 1192413 1193147 := bstep (se 1 (by rfl) ⟨894860, by rfl⟩ : syracuseStep 1193147 = 1789721) B1789721
theorem B2684105 : Blo 1192413 2684105 := bstep (se 2 (by rfl) ⟨1006539, by rfl⟩ : syracuseStep 2684105 = 2013079) B2013079
theorem B13595849 : Blo 1192413 13595849 := bstep (se 2 (by rfl) ⟨5098443, by rfl⟩ : syracuseStep 13595849 = 10196887) B10196887
theorem B1193223 : Blo 1192413 1193223 := bstep (se 1 (by rfl) ⟨894917, by rfl⟩ : syracuseStep 1193223 = 1789835) B1789835
theorem B1791239 : Blo 1192413 1791239 := bstep (se 1 (by rfl) ⟨1343429, by rfl⟩ : syracuseStep 1791239 = 2686859) B2686859
theorem B2012431 : Blo 1192413 2012431 := bstep (se 1 (by rfl) ⟨1509323, by rfl⟩ : syracuseStep 2012431 = 3018647) B3018647
theorem B1193231 : Blo 1192413 1193231 := bstep (se 1 (by rfl) ⟨894923, by rfl⟩ : syracuseStep 1193231 = 1789847) B1789847
theorem B3020075 : Blo 1192413 3020075 := bstep (se 1 (by rfl) ⟨2265056, by rfl⟩ : syracuseStep 3020075 = 4530113) B4530113
theorem B1791275 : Blo 1192413 1791275 := bstep (se 1 (by rfl) ⟨1343456, by rfl⟩ : syracuseStep 1791275 = 2686913) B2686913
theorem B3626299 : Blo 1192413 3626299 := bstep (se 1 (by rfl) ⟨2719724, by rfl⟩ : syracuseStep 3626299 = 5439449) B5439449
theorem B9565499 : Blo 1192413 9565499 := bstep (se 1 (by rfl) ⟨7174124, by rfl⟩ : syracuseStep 9565499 = 14348249) B14348249
theorem B1193275 : Blo 1192413 1193275 := bstep (se 1 (by rfl) ⟨894956, by rfl⟩ : syracuseStep 1193275 = 1789913) B1789913
theorem B1791305 : Blo 1192413 1791305 := bstep (se 2 (by rfl) ⟨671739, by rfl⟩ : syracuseStep 1791305 = 1343479) B1343479
theorem B1193351 : Blo 1192413 1193351 := bstep (se 1 (by rfl) ⟨895013, by rfl⟩ : syracuseStep 1193351 = 1790027) B1790027
theorem B1193359 : Blo 1192413 1193359 := bstep (se 1 (by rfl) ⟨895019, by rfl⟩ : syracuseStep 1193359 = 1790039) B1790039
theorem B3397049 : Blo 1192413 3397049 := bstep (se 2 (by rfl) ⟨1273893, by rfl⟩ : syracuseStep 3397049 = 2547787) B2547787
theorem B1193403 : Blo 1192413 1193403 := bstep (se 1 (by rfl) ⟨895052, by rfl⟩ : syracuseStep 1193403 = 1790105) B1790105
theorem B1791419 : Blo 1192413 1791419 := bstep (se 1 (by rfl) ⟨1343564, by rfl⟩ : syracuseStep 1791419 = 2687129) B2687129
theorem B5731793 : Blo 1192413 5731793 := bstep (se 2 (by rfl) ⟨2149422, by rfl⟩ : syracuseStep 5731793 = 4298845) B4298845
theorem B1791479 : Blo 1192413 1791479 := bstep (se 1 (by rfl) ⟨1343609, by rfl⟩ : syracuseStep 1791479 = 2687219) B2687219
theorem B1193479 : Blo 1192413 1193479 := bstep (se 1 (by rfl) ⟨895109, by rfl⟩ : syracuseStep 1193479 = 1790219) B1790219
theorem B1193487 : Blo 1192413 1193487 := bstep (se 1 (by rfl) ⟨895115, by rfl⟩ : syracuseStep 1193487 = 1790231) B1790231
theorem B1791503 : Blo 1192413 1791503 := bstep (se 1 (by rfl) ⟨1343627, by rfl⟩ : syracuseStep 1791503 = 2687255) B2687255
theorem B1791545 : Blo 1192413 1791545 := bstep (se 2 (by rfl) ⟨671829, by rfl⟩ : syracuseStep 1791545 = 1343659) B1343659
theorem B1193531 : Blo 1192413 1193531 := bstep (se 1 (by rfl) ⟨895148, by rfl⟩ : syracuseStep 1193531 = 1790297) B1790297
theorem B4527683 : Blo 1192413 4527683 := bstep (se 1 (by rfl) ⟨3395762, by rfl⟩ : syracuseStep 4527683 = 6791525) B6791525
theorem B1193607 : Blo 1192413 1193607 := bstep (se 1 (by rfl) ⟨895205, by rfl⟩ : syracuseStep 1193607 = 1790411) B1790411
theorem B1193615 : Blo 1192413 1193615 := bstep (se 1 (by rfl) ⟨895211, by rfl⟩ : syracuseStep 1193615 = 1790423) B1790423
theorem B1193659 : Blo 1192413 1193659 := bstep (se 1 (by rfl) ⟨895244, by rfl⟩ : syracuseStep 1193659 = 1790489) B1790489
theorem B1193735 : Blo 1192413 1193735 := bstep (se 1 (by rfl) ⟨895301, by rfl⟩ : syracuseStep 1193735 = 1790603) B1790603
theorem B1193743 : Blo 1192413 1193743 := bstep (se 1 (by rfl) ⟨895307, by rfl⟩ : syracuseStep 1193743 = 1790615) B1790615
theorem B2012971 : Blo 1192413 2012971 := bstep (se 1 (by rfl) ⟨1509728, by rfl⟩ : syracuseStep 2012971 = 3019457) B3019457
theorem B1193787 : Blo 1192413 1193787 := bstep (se 1 (by rfl) ⟨895340, by rfl⟩ : syracuseStep 1193787 = 1790681) B1790681
theorem B9066329 : Blo 1192413 9066329 := bstep (se 2 (by rfl) ⟨3399873, by rfl⟩ : syracuseStep 9066329 = 6799747) B6799747
theorem B2684807 : Blo 1192413 2684807 := bstep (se 1 (by rfl) ⟨2013605, by rfl⟩ : syracuseStep 2684807 = 4027211) B4027211
theorem B1193863 : Blo 1192413 1193863 := bstep (se 1 (by rfl) ⟨895397, by rfl⟩ : syracuseStep 1193863 = 1790795) B1790795
theorem B1193871 : Blo 1192413 1193871 := bstep (se 1 (by rfl) ⟨895403, by rfl⟩ : syracuseStep 1193871 = 1790807) B1790807
theorem B2013113 : Blo 1192413 2013113 := bstep (se 2 (by rfl) ⟨754917, by rfl⟩ : syracuseStep 2013113 = 1509835) B1509835
theorem B4028345 : Blo 1192413 4028345 := bstep (se 2 (by rfl) ⟨1510629, by rfl⟩ : syracuseStep 4028345 = 3021259) B3021259
theorem B1193915 : Blo 1192413 1193915 := bstep (se 1 (by rfl) ⟨895436, by rfl⟩ : syracuseStep 1193915 = 1790873) B1790873
theorem B1193991 : Blo 1192413 1193991 := bstep (se 1 (by rfl) ⟨895493, by rfl⟩ : syracuseStep 1193991 = 1790987) B1790987
theorem B5093387 : Blo 1192413 5093387 := bstep (se 1 (by rfl) ⟨3820040, by rfl⟩ : syracuseStep 5093387 = 7640081) B7640081
theorem B1193999 : Blo 1192413 1193999 := bstep (se 1 (by rfl) ⟨895499, by rfl⟩ : syracuseStep 1193999 = 1790999) B1790999
theorem B2865185 : Blo 1192413 2865185 := bstep (se 2 (by rfl) ⟨1074444, by rfl⟩ : syracuseStep 2865185 = 2148889) B2148889
theorem B26171437 : Blo 1192413 26171437 := bstep (se 3 (by rfl) ⟨4907144, by rfl⟩ : syracuseStep 26171437 = 9814289) B9814289
theorem B1341499 : Blo 1192413 1341499 := bstep (se 1 (by rfl) ⟨1006124, by rfl⟩ : syracuseStep 1341499 = 2012249) B2012249
theorem B2684987 : Blo 1192413 2684987 := bstep (se 1 (by rfl) ⟨2013740, by rfl⟩ : syracuseStep 2684987 = 4027481) B4027481
theorem B1194043 : Blo 1192413 1194043 := bstep (se 1 (by rfl) ⟨895532, by rfl⟩ : syracuseStep 1194043 = 1791065) B1791065
theorem B3020915 : Blo 1192413 3020915 := bstep (se 1 (by rfl) ⟨2265686, by rfl⟩ : syracuseStep 3020915 = 4531373) B4531373
theorem B9681029 : Blo 1192413 9681029 := bstep (se 4 (by rfl) ⟨907596, by rfl⟩ : syracuseStep 9681029 = 1815193) B1815193
theorem B3020935 : Blo 1192413 3020935 := bstep (se 1 (by rfl) ⟨2265701, by rfl⟩ : syracuseStep 3020935 = 4531403) B4531403
theorem B1194119 : Blo 1192413 1194119 := bstep (se 1 (by rfl) ⟨895589, by rfl⟩ : syracuseStep 1194119 = 1791179) B1791179
theorem B1194127 : Blo 1192413 1194127 := bstep (se 1 (by rfl) ⟨895595, by rfl⟩ : syracuseStep 1194127 = 1791191) B1791191
theorem B2685113 : Blo 1192413 2685113 := bstep (se 2 (by rfl) ⟨1006917, by rfl⟩ : syracuseStep 2685113 = 2013835) B2013835
theorem B1194171 : Blo 1192413 1194171 := bstep (se 1 (by rfl) ⟨895628, by rfl⟩ : syracuseStep 1194171 = 1791257) B1791257
theorem B1194247 : Blo 1192413 1194247 := bstep (se 1 (by rfl) ⟨895685, by rfl⟩ : syracuseStep 1194247 = 1791371) B1791371
theorem B1194255 : Blo 1192413 1194255 := bstep (se 1 (by rfl) ⟨895691, by rfl⟩ : syracuseStep 1194255 = 1791383) B1791383
theorem B1194299 : Blo 1192413 1194299 := bstep (se 1 (by rfl) ⟨895724, by rfl⟩ : syracuseStep 1194299 = 1791449) B1791449
theorem B1194375 : Blo 1192413 1194375 := bstep (se 1 (by rfl) ⟨895781, by rfl⟩ : syracuseStep 1194375 = 1791563) B1791563
theorem B1194383 : Blo 1192413 1194383 := bstep (se 1 (by rfl) ⟨895787, by rfl⟩ : syracuseStep 1194383 = 1791575) B1791575
theorem B3021209 : Blo 1192413 3021209 := bstep (se 2 (by rfl) ⟨1132953, by rfl⟩ : syracuseStep 3021209 = 2265907) B2265907
theorem B6044057 : Blo 1192413 6044057 := bstep (se 2 (by rfl) ⟨2266521, by rfl⟩ : syracuseStep 6044057 = 4533043) B4533043
theorem B6797789 : Blo 1192413 6797789 := bstep (se 3 (by rfl) ⟨1274585, by rfl⟩ : syracuseStep 6797789 = 2549171) B2549171
theorem B2865665 : Blo 1192413 2865665 := bstep (se 2 (by rfl) ⟨1074624, by rfl⟩ : syracuseStep 2865665 = 2149249) B2149249
theorem B4299275 : Blo 1192413 4299275 := bstep (se 1 (by rfl) ⟨3224456, by rfl⟩ : syracuseStep 4299275 = 6448913) B6448913
theorem B7256587 : Blo 1192413 7256587 := bstep (se 1 (by rfl) ⟨5442440, by rfl⟩ : syracuseStep 7256587 = 10884881) B10884881
theorem B4028939 : Blo 1192413 4028939 := bstep (se 1 (by rfl) ⟨3021704, by rfl⟩ : syracuseStep 4028939 = 6043409) B6043409
theorem B1341967 : Blo 1192413 1341967 := bstep (se 1 (by rfl) ⟨1006475, by rfl⟩ : syracuseStep 1341967 = 2012951) B2012951
theorem B2685455 : Blo 1192413 2685455 := bstep (se 1 (by rfl) ⟨2014091, by rfl⟩ : syracuseStep 2685455 = 4028183) B4028183
theorem B4528669 : Blo 1192413 4528669 := bstep (se 3 (by rfl) ⟨849125, by rfl⟩ : syracuseStep 4528669 = 1698251) B1698251
theorem B2685473 : Blo 1192413 2685473 := bstep (se 2 (by rfl) ⟨1007052, by rfl⟩ : syracuseStep 2685473 = 2014105) B2014105
theorem B3021371 : Blo 1192413 3021371 := bstep (se 1 (by rfl) ⟨2266028, by rfl⟩ : syracuseStep 3021371 = 4532057) B4532057
theorem B2013815 : Blo 1192413 2013815 := bstep (se 1 (by rfl) ⟨1510361, by rfl⟩ : syracuseStep 2013815 = 3020723) B3020723
theorem B4029047 : Blo 1192413 4029047 := bstep (se 1 (by rfl) ⟨3021785, by rfl⟩ : syracuseStep 4029047 = 6043571) B6043571
theorem B3021583 : Blo 1192413 3021583 := bstep (se 1 (by rfl) ⟨2266187, by rfl⟩ : syracuseStep 3021583 = 4532375) B4532375
theorem B9067301 : Blo 1192413 9067301 := bstep (se 4 (by rfl) ⟨850059, by rfl⟩ : syracuseStep 9067301 = 1700119) B1700119
theorem B12254003 : Blo 1192413 12254003 := bstep (se 1 (by rfl) ⟨9190502, by rfl⟩ : syracuseStep 12254003 = 18381005) B18381005
theorem B2685815 : Blo 1192413 2685815 := bstep (se 1 (by rfl) ⟨2014361, by rfl⟩ : syracuseStep 2685815 = 4028723) B4028723
theorem B6798289 : Blo 1192413 6798289 := bstep (se 2 (by rfl) ⟨2549358, by rfl⟩ : syracuseStep 6798289 = 5098717) B5098717
theorem B1342471 : Blo 1192413 1342471 := bstep (se 1 (by rfl) ⟨1006853, by rfl⟩ : syracuseStep 1342471 = 2013707) B2013707
theorem B3398689 : Blo 1192413 3398689 := bstep (se 2 (by rfl) ⟨1274508, by rfl⟩ : syracuseStep 3398689 = 2549017) B2549017
theorem B3021857 : Blo 1192413 3021857 := bstep (se 2 (by rfl) ⟨1133196, by rfl⟩ : syracuseStep 3021857 = 2266393) B2266393
theorem B2685995 : Blo 1192413 2685995 := bstep (se 1 (by rfl) ⟨2014496, by rfl⟩ : syracuseStep 2685995 = 4028993) B4028993
theorem B2014267 : Blo 1192413 2014267 := bstep (se 1 (by rfl) ⟨1510700, by rfl⟩ : syracuseStep 2014267 = 3021401) B3021401
theorem B5733443 : Blo 1192413 5733443 := bstep (se 1 (by rfl) ⟨4300082, by rfl⟩ : syracuseStep 5733443 = 8600165) B8600165
theorem B1342651 : Blo 1192413 1342651 := bstep (se 1 (by rfl) ⟨1006988, by rfl⟩ : syracuseStep 1342651 = 2013977) B2013977
theorem B2014409 : Blo 1192413 2014409 := bstep (se 2 (by rfl) ⟨755403, by rfl⟩ : syracuseStep 2014409 = 1510807) B1510807
theorem B4029641 : Blo 1192413 4029641 := bstep (se 2 (by rfl) ⟨1511115, by rfl⟩ : syracuseStep 4029641 = 3022231) B3022231
theorem B7462145 : Blo 1192413 7462145 := bstep (se 2 (by rfl) ⟨2798304, by rfl⟩ : syracuseStep 7462145 = 5596609) B5596609
theorem B2546959 : Blo 1192413 2546959 := bstep (se 1 (by rfl) ⟨1910219, by rfl⟩ : syracuseStep 2546959 = 3820439) B3820439
theorem B2686355 : Blo 1192413 2686355 := bstep (se 1 (by rfl) ⟨2014766, by rfl⟩ : syracuseStep 2686355 = 4029533) B4029533
theorem B2686409 : Blo 1192413 2686409 := bstep (se 2 (by rfl) ⟨1007403, by rfl⟩ : syracuseStep 2686409 = 2014807) B2014807
theorem B7650845 : Blo 1192413 7650845 := bstep (se 3 (by rfl) ⟨1434533, by rfl⟩ : syracuseStep 7650845 = 2869067) B2869067
theorem B24813155 : Blo 1192413 24813155 := bstep (se 1 (by rfl) ⟨18609866, by rfl⟩ : syracuseStep 24813155 = 37219733) B37219733
theorem B1343119 : Blo 1192413 1343119 := bstep (se 1 (by rfl) ⟨1007339, by rfl⟩ : syracuseStep 1343119 = 2014679) B2014679
theorem B22945457 : Blo 1192413 22945457 := bstep (se 2 (by rfl) ⟨8604546, by rfl⟩ : syracuseStep 22945457 = 17209093) B17209093
theorem B11460275 : Blo 1192413 11460275 := bstep (se 1 (by rfl) ⟨8595206, by rfl⟩ : syracuseStep 11460275 = 17190413) B17190413
theorem B46481201 : Blo 1192413 46481201 := bstep (se 2 (by rfl) ⟨17430450, by rfl⟩ : syracuseStep 46481201 = 34860901) B34860901
theorem B2015111 : Blo 1192413 2015111 := bstep (se 1 (by rfl) ⟨1511333, by rfl⟩ : syracuseStep 2015111 = 3022667) B3022667
theorem B4030343 : Blo 1192413 4030343 := bstep (se 1 (by rfl) ⟨3022757, by rfl⟩ : syracuseStep 4030343 = 6045515) B6045515
theorem B2015239 : Blo 1192413 2015239 := bstep (se 1 (by rfl) ⟨1511429, by rfl⟩ : syracuseStep 2015239 = 3022859) B3022859
theorem B5447695 : Blo 1192413 5447695 := bstep (se 1 (by rfl) ⟨4085771, by rfl⟩ : syracuseStep 5447695 = 8171543) B8171543
theorem B2687147 : Blo 1192413 2687147 := bstep (se 1 (by rfl) ⟨2015360, by rfl⟩ : syracuseStep 2687147 = 4030721) B4030721
theorem B4301351 : Blo 1192413 4301351 := bstep (se 1 (by rfl) ⟨3226013, by rfl⟩ : syracuseStep 4301351 = 6452027) B6452027
theorem B4031099 : Blo 1192413 4031099 := bstep (se 1 (by rfl) ⟨3023324, by rfl⟩ : syracuseStep 4031099 = 6046649) B6046649
theorem B19899053 : Blo 1192413 19899053 := bstep (se 3 (by rfl) ⟨3731072, by rfl⟩ : syracuseStep 19899053 = 7462145) B7462145
theorem B9675449 : Blo 1192413 9675449 := bstep (se 2 (by rfl) ⟨3628293, by rfl⟩ : syracuseStep 9675449 = 7256587) B7256587
theorem B4530887 : Blo 1192413 4530887 := bstep (se 1 (by rfl) ⟨3398165, by rfl⟩ : syracuseStep 4530887 = 6796331) B6796331
theorem B6038225 : Blo 1192413 6038225 := bstep (se 2 (by rfl) ⟨2264334, by rfl⟩ : syracuseStep 6038225 = 4528669) B4528669
theorem B1721353 : Blo 1192413 1721353 := bstep (se 2 (by rfl) ⟨645507, by rfl⟩ : syracuseStep 1721353 = 1291015) B1291015
theorem B9192467 : Blo 1192413 9192467 := bstep (se 1 (by rfl) ⟨6894350, by rfl⟩ : syracuseStep 9192467 = 13788701) B13788701
theorem B12248113 : Blo 1192413 12248113 := bstep (se 2 (by rfl) ⟨4593042, by rfl⟩ : syracuseStep 12248113 = 9186085) B9186085
theorem B20382839 : Blo 1192413 20382839 := bstep (se 1 (by rfl) ⟨15287129, by rfl⟩ : syracuseStep 20382839 = 30574259) B30574259
theorem B9684139 : Blo 1192413 9684139 := bstep (se 1 (by rfl) ⟨7263104, by rfl⟩ : syracuseStep 9684139 = 14526209) B14526209
theorem B1910123 : Blo 1192413 1910123 := bstep (se 1 (by rfl) ⟨1432592, by rfl⟩ : syracuseStep 1910123 = 2865185) B2865185
theorem B4531585 : Blo 1192413 4531585 := bstep (se 2 (by rfl) ⟨1699344, by rfl⟩ : syracuseStep 4531585 = 3398689) B3398689
theorem B2868875 : Blo 1192413 2868875 := bstep (se 1 (by rfl) ⟨2151656, by rfl⟩ : syracuseStep 2868875 = 4303313) B4303313
theorem B4531859 : Blo 1192413 4531859 := bstep (se 1 (by rfl) ⟨3398894, by rfl⟩ : syracuseStep 4531859 = 6797789) B6797789
theorem B4835065 : Blo 1192413 4835065 := bstep (se 2 (by rfl) ⟨1813149, by rfl⟩ : syracuseStep 4835065 = 3626299) B3626299
theorem B8169335 : Blo 1192413 8169335 := bstep (se 1 (by rfl) ⟨6127001, by rfl⟩ : syracuseStep 8169335 = 12254003) B12254003
theorem B5097487 : Blo 1192413 5097487 := bstep (se 1 (by rfl) ⟨3823115, by rfl⟩ : syracuseStep 5097487 = 7646231) B7646231
theorem B1509455 : Blo 1192413 1509455 := bstep (se 1 (by rfl) ⟨1132091, by rfl⟩ : syracuseStep 1509455 = 2264183) B2264183
theorem B2451817 : Blo 1192413 2451817 := bstep (se 2 (by rfl) ⟨919431, by rfl⟩ : syracuseStep 2451817 = 1838863) B1838863
theorem B2419049 : Blo 1192413 2419049 := bstep (se 2 (by rfl) ⟨907143, by rfl⟩ : syracuseStep 2419049 = 1814287) B1814287
theorem B16542103 : Blo 1192413 16542103 := bstep (se 1 (by rfl) ⟨12406577, by rfl⟩ : syracuseStep 16542103 = 24813155) B24813155
theorem B15296971 : Blo 1192413 15296971 := bstep (se 1 (by rfl) ⟨11472728, by rfl⟩ : syracuseStep 15296971 = 22945457) B22945457
theorem B1788665 : Blo 1192413 1788665 := bstep (se 2 (by rfl) ⟨670749, by rfl⟩ : syracuseStep 1788665 = 1341499) B1341499
theorem B2550521 : Blo 1192413 2550521 := bstep (se 2 (by rfl) ⟨956445, by rfl⟩ : syracuseStep 2550521 = 1912891) B1912891
theorem B15289181 : Blo 1192413 15289181 := bstep (se 3 (by rfl) ⟨2866721, by rfl⟩ : syracuseStep 15289181 = 5733443) B5733443
theorem B1788767 : Blo 1192413 1788767 := bstep (se 1 (by rfl) ⟨1341575, by rfl⟩ : syracuseStep 1788767 = 2683151) B2683151
theorem B1788779 : Blo 1192413 1788779 := bstep (se 1 (by rfl) ⟨1341584, by rfl⟩ : syracuseStep 1788779 = 2683169) B2683169
theorem B4590445 : Blo 1192413 4590445 := bstep (se 3 (by rfl) ⟨860708, by rfl⟩ : syracuseStep 4590445 = 1721417) B1721417
theorem B13601681 : Blo 1192413 13601681 := bstep (se 2 (by rfl) ⟨5100630, by rfl⟩ : syracuseStep 13601681 = 10201261) B10201261
theorem B9055151 : Blo 1192413 9055151 := bstep (se 1 (by rfl) ⟨6791363, by rfl⟩ : syracuseStep 9055151 = 13582727) B13582727
theorem B51604451 : Blo 1192413 51604451 := bstep (se 1 (by rfl) ⟨38703338, by rfl⟩ : syracuseStep 51604451 = 77406677) B77406677
theorem B1789007 : Blo 1192413 1789007 := bstep (se 1 (by rfl) ⟨1341755, by rfl⟩ : syracuseStep 1789007 = 2683511) B2683511
theorem B3443791 : Blo 1192413 3443791 := bstep (se 1 (by rfl) ⟨2582843, by rfl⟩ : syracuseStep 3443791 = 5165687) B5165687
theorem B6040655 : Blo 1192413 6040655 := bstep (se 1 (by rfl) ⟨4530491, by rfl⟩ : syracuseStep 6040655 = 9060983) B9060983
theorem B1789127 : Blo 1192413 1789127 := bstep (se 1 (by rfl) ⟨1341845, by rfl⟩ : syracuseStep 1789127 = 2683691) B2683691
theorem B4025591 : Blo 1192413 4025591 := bstep (se 1 (by rfl) ⟨3019193, by rfl⟩ : syracuseStep 4025591 = 6038387) B6038387
theorem B4304119 : Blo 1192413 4304119 := bstep (se 1 (by rfl) ⟨3228089, by rfl⟩ : syracuseStep 4304119 = 6456179) B6456179
theorem B4533515 : Blo 1192413 4533515 := bstep (se 1 (by rfl) ⟨3400136, by rfl⟩ : syracuseStep 4533515 = 6800273) B6800273
theorem B20655395 : Blo 1192413 20655395 := bstep (se 1 (by rfl) ⟨15491546, by rfl⟩ : syracuseStep 20655395 = 30983093) B30983093
theorem B1510751 : Blo 1192413 1510751 := bstep (se 1 (by rfl) ⟨1133063, by rfl⟩ : syracuseStep 1510751 = 2266127) B2266127
theorem B1789289 : Blo 1192413 1789289 := bstep (se 2 (by rfl) ⟨670983, by rfl⟩ : syracuseStep 1789289 = 1341967) B1341967
theorem B1789367 : Blo 1192413 1789367 := bstep (se 1 (by rfl) ⟨1342025, by rfl⟩ : syracuseStep 1789367 = 2684051) B2684051
theorem B1789403 : Blo 1192413 1789403 := bstep (se 1 (by rfl) ⟨1342052, by rfl⟩ : syracuseStep 1789403 = 2684105) B2684105
theorem B9063899 : Blo 1192413 9063899 := bstep (se 1 (by rfl) ⟨6797924, by rfl⟩ : syracuseStep 9063899 = 13595849) B13595849
theorem B4025915 : Blo 1192413 4025915 := bstep (se 1 (by rfl) ⟨3019436, by rfl⟩ : syracuseStep 4025915 = 6038873) B6038873
theorem B2264699 : Blo 1192413 2264699 := bstep (se 1 (by rfl) ⟨1698524, by rfl⟩ : syracuseStep 2264699 = 3397049) B3397049
theorem B3821195 : Blo 1192413 3821195 := bstep (se 1 (by rfl) ⟨2865896, by rfl⟩ : syracuseStep 3821195 = 5731793) B5731793
theorem B24489661 : Blo 1192413 24489661 := bstep (se 3 (by rfl) ⟨4591811, by rfl⟩ : syracuseStep 24489661 = 9183623) B9183623
theorem B3018455 : Blo 1192413 3018455 := bstep (se 1 (by rfl) ⟨2263841, by rfl⟩ : syracuseStep 3018455 = 4527683) B4527683
theorem B6041303 : Blo 1192413 6041303 := bstep (se 1 (by rfl) ⟨4530977, by rfl⟩ : syracuseStep 6041303 = 9061955) B9061955
theorem B4026185 : Blo 1192413 4026185 := bstep (se 2 (by rfl) ⟨1509819, by rfl⟩ : syracuseStep 4026185 = 3019639) B3019639
theorem B37760903 : Blo 1192413 37760903 := bstep (se 1 (by rfl) ⟨28320677, by rfl⟩ : syracuseStep 37760903 = 56641355) B56641355
theorem B1789871 : Blo 1192413 1789871 := bstep (se 1 (by rfl) ⟨1342403, by rfl⟩ : syracuseStep 1789871 = 2684807) B2684807
theorem B2584507 : Blo 1192413 2584507 := bstep (se 1 (by rfl) ⟨1938380, by rfl⟩ : syracuseStep 2584507 = 3876761) B3876761
theorem B9064385 : Blo 1192413 9064385 := bstep (se 2 (by rfl) ⟨3399144, by rfl⟩ : syracuseStep 9064385 = 6798289) B6798289
theorem B3395591 : Blo 1192413 3395591 := bstep (se 1 (by rfl) ⟨2546693, by rfl⟩ : syracuseStep 3395591 = 5093387) B5093387
theorem B1789961 : Blo 1192413 1789961 := bstep (se 2 (by rfl) ⟨671235, by rfl⟩ : syracuseStep 1789961 = 1342471) B1342471
theorem B11464733 : Blo 1192413 11464733 := bstep (se 3 (by rfl) ⟨2149637, by rfl⟩ : syracuseStep 11464733 = 4299275) B4299275
theorem B1789991 : Blo 1192413 1789991 := bstep (se 1 (by rfl) ⟨1342493, by rfl⟩ : syracuseStep 1789991 = 2684987) B2684987
theorem B3018809 : Blo 1192413 3018809 := bstep (se 2 (by rfl) ⟨1132053, by rfl⟩ : syracuseStep 3018809 = 2264107) B2264107
theorem B2265185 : Blo 1192413 2265185 := bstep (se 2 (by rfl) ⟨849444, by rfl⟩ : syracuseStep 2265185 = 1698889) B1698889
theorem B1273979 : Blo 1192413 1273979 := bstep (se 1 (by rfl) ⟨955484, by rfl⟩ : syracuseStep 1273979 = 1910969) B1910969
theorem B1790075 : Blo 1192413 1790075 := bstep (se 1 (by rfl) ⟨1342556, by rfl⟩ : syracuseStep 1790075 = 2685113) B2685113
theorem B2265337 : Blo 1192413 2265337 := bstep (se 2 (by rfl) ⟨849501, by rfl⟩ : syracuseStep 2265337 = 1699003) B1699003
theorem B1790201 : Blo 1192413 1790201 := bstep (se 2 (by rfl) ⟨671325, by rfl⟩ : syracuseStep 1790201 = 1342651) B1342651
theorem B34419005 : Blo 1192413 34419005 := bstep (se 3 (by rfl) ⟨6453563, by rfl⟩ : syracuseStep 34419005 = 12907127) B12907127
theorem B1790303 : Blo 1192413 1790303 := bstep (se 1 (by rfl) ⟨1342727, by rfl⟩ : syracuseStep 1790303 = 2685455) B2685455
theorem B3395945 : Blo 1192413 3395945 := bstep (se 2 (by rfl) ⟨1273479, by rfl⟩ : syracuseStep 3395945 = 2546959) B2546959
theorem B2683241 : Blo 1192413 2683241 := bstep (se 2 (by rfl) ⟨1006215, by rfl⟩ : syracuseStep 2683241 = 2012431) B2012431
theorem B1790315 : Blo 1192413 1790315 := bstep (se 1 (by rfl) ⟨1342736, by rfl⟩ : syracuseStep 1790315 = 2685473) B2685473
theorem B1192487 : Blo 1192413 1192487 := bstep (se 1 (by rfl) ⟨894365, by rfl⟩ : syracuseStep 1192487 = 1788731) B1788731
theorem B6451771 : Blo 1192413 6451771 := bstep (se 1 (by rfl) ⟨4838828, by rfl⟩ : syracuseStep 6451771 = 9677657) B9677657
theorem B1192527 : Blo 1192413 1192527 := bstep (se 1 (by rfl) ⟨894395, by rfl⟩ : syracuseStep 1192527 = 1788791) B1788791
theorem B1790543 : Blo 1192413 1790543 := bstep (se 1 (by rfl) ⟨1342907, by rfl⟩ : syracuseStep 1790543 = 2685815) B2685815
theorem B1192543 : Blo 1192413 1192543 := bstep (se 1 (by rfl) ⟨894407, by rfl⟩ : syracuseStep 1192543 = 1788815) B1788815
theorem B1192571 : Blo 1192413 1192571 := bstep (se 1 (by rfl) ⟨894428, by rfl⟩ : syracuseStep 1192571 = 1788857) B1788857
theorem B1192623 : Blo 1192413 1192623 := bstep (se 1 (by rfl) ⟨894467, by rfl⟩ : syracuseStep 1192623 = 1788935) B1788935
theorem B4534973 : Blo 1192413 4534973 := bstep (se 3 (by rfl) ⟨850307, by rfl⟩ : syracuseStep 4534973 = 1700615) B1700615
theorem B1192647 : Blo 1192413 1192647 := bstep (se 1 (by rfl) ⟨894485, by rfl⟩ : syracuseStep 1192647 = 1788971) B1788971
theorem B1790663 : Blo 1192413 1790663 := bstep (se 1 (by rfl) ⟨1342997, by rfl⟩ : syracuseStep 1790663 = 2685995) B2685995
theorem B1192667 : Blo 1192413 1192667 := bstep (se 1 (by rfl) ⟨894500, by rfl⟩ : syracuseStep 1192667 = 1789001) B1789001
theorem B1192743 : Blo 1192413 1192743 := bstep (se 1 (by rfl) ⟨894557, by rfl⟩ : syracuseStep 1192743 = 1789115) B1789115
theorem B1192783 : Blo 1192413 1192783 := bstep (se 1 (by rfl) ⟨894587, by rfl⟩ : syracuseStep 1192783 = 1789175) B1789175
theorem B1192799 : Blo 1192413 1192799 := bstep (se 1 (by rfl) ⟨894599, by rfl⟩ : syracuseStep 1192799 = 1789199) B1789199
theorem B1790825 : Blo 1192413 1790825 := bstep (se 2 (by rfl) ⟨671559, by rfl⟩ : syracuseStep 1790825 = 1343119) B1343119
theorem B1192827 : Blo 1192413 1192827 := bstep (se 1 (by rfl) ⟨894620, by rfl⟩ : syracuseStep 1192827 = 1789241) B1789241
theorem B1192879 : Blo 1192413 1192879 := bstep (se 1 (by rfl) ⟨894659, by rfl⟩ : syracuseStep 1192879 = 1789319) B1789319
theorem B4027319 : Blo 1192413 4027319 := bstep (se 1 (by rfl) ⟨3020489, by rfl⟩ : syracuseStep 4027319 = 6040979) B6040979
theorem B1790903 : Blo 1192413 1790903 := bstep (se 1 (by rfl) ⟨1343177, by rfl⟩ : syracuseStep 1790903 = 2686355) B2686355
theorem B2683835 : Blo 1192413 2683835 := bstep (se 1 (by rfl) ⟨2012876, by rfl⟩ : syracuseStep 2683835 = 4025753) B4025753
theorem B1192903 : Blo 1192413 1192903 := bstep (se 1 (by rfl) ⟨894677, by rfl⟩ : syracuseStep 1192903 = 1789355) B1789355
theorem B1192923 : Blo 1192413 1192923 := bstep (se 1 (by rfl) ⟨894692, by rfl⟩ : syracuseStep 1192923 = 1789385) B1789385
theorem B1790939 : Blo 1192413 1790939 := bstep (se 1 (by rfl) ⟨1343204, by rfl⟩ : syracuseStep 1790939 = 2686409) B2686409
theorem B5100563 : Blo 1192413 5100563 := bstep (se 1 (by rfl) ⟨3825422, by rfl⟩ : syracuseStep 5100563 = 7650845) B7650845
theorem B1192999 : Blo 1192413 1192999 := bstep (se 1 (by rfl) ⟨894749, by rfl⟩ : syracuseStep 1192999 = 1789499) B1789499
theorem B2683961 : Blo 1192413 2683961 := bstep (se 2 (by rfl) ⟨1006485, by rfl⟩ : syracuseStep 2683961 = 2012971) B2012971
theorem B1193039 : Blo 1192413 1193039 := bstep (se 1 (by rfl) ⟨894779, by rfl⟩ : syracuseStep 1193039 = 1789559) B1789559
theorem B1193055 : Blo 1192413 1193055 := bstep (se 1 (by rfl) ⟨894791, by rfl⟩ : syracuseStep 1193055 = 1789583) B1789583
theorem B7640183 : Blo 1192413 7640183 := bstep (se 1 (by rfl) ⟨5730137, by rfl⟩ : syracuseStep 7640183 = 11460275) B11460275
theorem B1193083 : Blo 1192413 1193083 := bstep (se 1 (by rfl) ⟨894812, by rfl⟩ : syracuseStep 1193083 = 1789625) B1789625
theorem B1193135 : Blo 1192413 1193135 := bstep (se 1 (by rfl) ⟨894851, by rfl⟩ : syracuseStep 1193135 = 1789703) B1789703
theorem B1193159 : Blo 1192413 1193159 := bstep (se 1 (by rfl) ⟨894869, by rfl⟩ : syracuseStep 1193159 = 1789739) B1789739
theorem B30987467 : Blo 1192413 30987467 := bstep (se 1 (by rfl) ⟨23240600, by rfl⟩ : syracuseStep 30987467 = 46481201) B46481201
theorem B1193179 : Blo 1192413 1193179 := bstep (se 1 (by rfl) ⟨894884, by rfl⟩ : syracuseStep 1193179 = 1789769) B1789769
theorem B8615159 : Blo 1192413 8615159 := bstep (se 1 (by rfl) ⟨6461369, by rfl⟩ : syracuseStep 8615159 = 12922739) B12922739
theorem B27538703 : Blo 1192413 27538703 := bstep (se 1 (by rfl) ⟨20654027, by rfl⟩ : syracuseStep 27538703 = 41308055) B41308055
theorem B1193255 : Blo 1192413 1193255 := bstep (se 1 (by rfl) ⟨894941, by rfl⟩ : syracuseStep 1193255 = 1789883) B1789883
theorem B1193295 : Blo 1192413 1193295 := bstep (se 1 (by rfl) ⟨894971, by rfl⟩ : syracuseStep 1193295 = 1789943) B1789943
theorem B1193311 : Blo 1192413 1193311 := bstep (se 1 (by rfl) ⟨894983, by rfl⟩ : syracuseStep 1193311 = 1789967) B1789967
theorem B9065843 : Blo 1192413 9065843 := bstep (se 1 (by rfl) ⟨6799382, by rfl⟩ : syracuseStep 9065843 = 13598765) B13598765
theorem B1193339 : Blo 1192413 1193339 := bstep (se 1 (by rfl) ⟨895004, by rfl⟩ : syracuseStep 1193339 = 1790009) B1790009
theorem B4527485 : Blo 1192413 4527485 := bstep (se 3 (by rfl) ⟨848903, by rfl⟩ : syracuseStep 4527485 = 1697807) B1697807
theorem B2684303 : Blo 1192413 2684303 := bstep (se 1 (by rfl) ⟨2013227, by rfl⟩ : syracuseStep 2684303 = 4026455) B4026455
theorem B34895249 : Blo 1192413 34895249 := bstep (se 2 (by rfl) ⟨13085718, by rfl⟩ : syracuseStep 34895249 = 26171437) B26171437
theorem B1193391 : Blo 1192413 1193391 := bstep (se 1 (by rfl) ⟨895043, by rfl⟩ : syracuseStep 1193391 = 1790087) B1790087
theorem B1791407 : Blo 1192413 1791407 := bstep (se 1 (by rfl) ⟨1343555, by rfl⟩ : syracuseStep 1791407 = 2687111) B2687111
theorem B1193415 : Blo 1192413 1193415 := bstep (se 1 (by rfl) ⟨895061, by rfl⟩ : syracuseStep 1193415 = 1790123) B1790123
theorem B1193435 : Blo 1192413 1193435 := bstep (se 1 (by rfl) ⟨895076, by rfl⟩ : syracuseStep 1193435 = 1790153) B1790153
theorem B2012681 : Blo 1192413 2012681 := bstep (se 2 (by rfl) ⟨754755, by rfl⟩ : syracuseStep 2012681 = 1509511) B1509511
theorem B4027913 : Blo 1192413 4027913 := bstep (se 2 (by rfl) ⟨1510467, by rfl⟩ : syracuseStep 4027913 = 3020935) B3020935
theorem B1791497 : Blo 1192413 1791497 := bstep (se 2 (by rfl) ⟨671811, by rfl⟩ : syracuseStep 1791497 = 1343623) B1343623
theorem B2266643 : Blo 1192413 2266643 := bstep (se 1 (by rfl) ⟨1699982, by rfl⟩ : syracuseStep 2266643 = 3399965) B3399965
theorem B1193511 : Blo 1192413 1193511 := bstep (se 1 (by rfl) ⟨895133, by rfl⟩ : syracuseStep 1193511 = 1790267) B1790267
theorem B1791527 : Blo 1192413 1791527 := bstep (se 1 (by rfl) ⟨1343645, by rfl⟩ : syracuseStep 1791527 = 2687291) B2687291
theorem B1275431 : Blo 1192413 1275431 := bstep (se 1 (by rfl) ⟨956573, by rfl⟩ : syracuseStep 1275431 = 1913147) B1913147
theorem B1193551 : Blo 1192413 1193551 := bstep (se 1 (by rfl) ⟨895163, by rfl⟩ : syracuseStep 1193551 = 1790327) B1790327
theorem B1193567 : Blo 1192413 1193567 := bstep (se 1 (by rfl) ⟨895175, by rfl⟩ : syracuseStep 1193567 = 1790351) B1790351
theorem B1193595 : Blo 1192413 1193595 := bstep (se 1 (by rfl) ⟨895196, by rfl⟩ : syracuseStep 1193595 = 1790393) B1790393
theorem B1791611 : Blo 1192413 1791611 := bstep (se 1 (by rfl) ⟨1343708, by rfl⟩ : syracuseStep 1791611 = 2687417) B2687417
theorem B2012843 : Blo 1192413 2012843 := bstep (se 1 (by rfl) ⟨1509632, by rfl⟩ : syracuseStep 2012843 = 3019265) B3019265
theorem B2266795 : Blo 1192413 2266795 := bstep (se 1 (by rfl) ⟨1700096, by rfl⟩ : syracuseStep 2266795 = 3400193) B3400193
theorem B1193647 : Blo 1192413 1193647 := bstep (se 1 (by rfl) ⟨895235, by rfl⟩ : syracuseStep 1193647 = 1790471) B1790471
theorem B15513281 : Blo 1192413 15513281 := bstep (se 2 (by rfl) ⟨5817480, by rfl⟩ : syracuseStep 15513281 = 11634961) B11634961
theorem B15496903 : Blo 1192413 15496903 := bstep (se 1 (by rfl) ⟨11622677, by rfl⟩ : syracuseStep 15496903 = 23245355) B23245355
theorem B1193671 : Blo 1192413 1193671 := bstep (se 1 (by rfl) ⟨895253, by rfl⟩ : syracuseStep 1193671 = 1790507) B1790507
theorem B2684627 : Blo 1192413 2684627 := bstep (se 1 (by rfl) ⟨2013470, by rfl⟩ : syracuseStep 2684627 = 4026941) B4026941
theorem B1193691 : Blo 1192413 1193691 := bstep (se 1 (by rfl) ⟨895268, by rfl⟩ : syracuseStep 1193691 = 1790537) B1790537
theorem B1193767 : Blo 1192413 1193767 := bstep (se 1 (by rfl) ⟨895325, by rfl⟩ : syracuseStep 1193767 = 1790651) B1790651
theorem B1193807 : Blo 1192413 1193807 := bstep (se 1 (by rfl) ⟨895355, by rfl⟩ : syracuseStep 1193807 = 1790711) B1790711
theorem B1193823 : Blo 1192413 1193823 := bstep (se 1 (by rfl) ⟨895367, by rfl⟩ : syracuseStep 1193823 = 1790735) B1790735
theorem B6289271 : Blo 1192413 6289271 := bstep (se 1 (by rfl) ⟨4716953, by rfl⟩ : syracuseStep 6289271 = 9433907) B9433907
theorem B1193851 : Blo 1192413 1193851 := bstep (se 1 (by rfl) ⟨895388, by rfl⟩ : syracuseStep 1193851 = 1790777) B1790777
theorem B2267023 : Blo 1192413 2267023 := bstep (se 1 (by rfl) ⟨1700267, by rfl⟩ : syracuseStep 2267023 = 3400535) B3400535
theorem B1193903 : Blo 1192413 1193903 := bstep (se 1 (by rfl) ⟨895427, by rfl⟩ : syracuseStep 1193903 = 1790855) B1790855
theorem B17192897 : Blo 1192413 17192897 := bstep (se 2 (by rfl) ⟨6447336, by rfl⟩ : syracuseStep 17192897 = 12894673) B12894673
theorem B1193927 : Blo 1192413 1193927 := bstep (se 1 (by rfl) ⟨895445, by rfl⟩ : syracuseStep 1193927 = 1790891) B1790891
theorem B1193947 : Blo 1192413 1193947 := bstep (se 1 (by rfl) ⟨895460, by rfl⟩ : syracuseStep 1193947 = 1790921) B1790921
theorem B2267099 : Blo 1192413 2267099 := bstep (se 1 (by rfl) ⟨1700324, by rfl⟩ : syracuseStep 2267099 = 3400649) B3400649
theorem B3872783 : Blo 1192413 3872783 := bstep (se 1 (by rfl) ⟨2904587, by rfl⟩ : syracuseStep 3872783 = 5809175) B5809175
theorem B7256101 : Blo 1192413 7256101 := bstep (se 4 (by rfl) ⟨680259, by rfl⟩ : syracuseStep 7256101 = 1360519) B1360519
theorem B1194023 : Blo 1192413 1194023 := bstep (se 1 (by rfl) ⟨895517, by rfl⟩ : syracuseStep 1194023 = 1791035) B1791035
theorem B2013241 : Blo 1192413 2013241 := bstep (se 2 (by rfl) ⟨754965, by rfl⟩ : syracuseStep 2013241 = 1509931) B1509931
theorem B1194063 : Blo 1192413 1194063 := bstep (se 1 (by rfl) ⟨895547, by rfl⟩ : syracuseStep 1194063 = 1791095) B1791095
theorem B1194079 : Blo 1192413 1194079 := bstep (se 1 (by rfl) ⟨895559, by rfl⟩ : syracuseStep 1194079 = 1791119) B1791119
theorem B12908645 : Blo 1192413 12908645 := bstep (se 4 (by rfl) ⟨1210185, by rfl⟩ : syracuseStep 12908645 = 2420371) B2420371
theorem B1194107 : Blo 1192413 1194107 := bstep (se 1 (by rfl) ⟨895580, by rfl⟩ : syracuseStep 1194107 = 1791161) B1791161
theorem B25507997 : Blo 1192413 25507997 := bstep (se 3 (by rfl) ⟨4782749, by rfl⟩ : syracuseStep 25507997 = 9565499) B9565499
theorem B1194159 : Blo 1192413 1194159 := bstep (se 1 (by rfl) ⟨895619, by rfl⟩ : syracuseStep 1194159 = 1791239) B1791239
theorem B2013383 : Blo 1192413 2013383 := bstep (se 1 (by rfl) ⟨1510037, by rfl⟩ : syracuseStep 2013383 = 3020075) B3020075
theorem B1194183 : Blo 1192413 1194183 := bstep (se 1 (by rfl) ⟨895637, by rfl⟩ : syracuseStep 1194183 = 1791275) B1791275
theorem B1194203 : Blo 1192413 1194203 := bstep (se 1 (by rfl) ⟨895652, by rfl⟩ : syracuseStep 1194203 = 1791305) B1791305
theorem B3021047 : Blo 1192413 3021047 := bstep (se 1 (by rfl) ⟨2265785, by rfl⟩ : syracuseStep 3021047 = 4531571) B4531571
theorem B1194279 : Blo 1192413 1194279 := bstep (se 1 (by rfl) ⟨895709, by rfl⟩ : syracuseStep 1194279 = 1791419) B1791419
theorem B1194319 : Blo 1192413 1194319 := bstep (se 1 (by rfl) ⟨895739, by rfl⟩ : syracuseStep 1194319 = 1791479) B1791479
theorem B1194335 : Blo 1192413 1194335 := bstep (se 1 (by rfl) ⟨895751, by rfl⟩ : syracuseStep 1194335 = 1791503) B1791503
theorem B2013545 : Blo 1192413 2013545 := bstep (se 2 (by rfl) ⟨755079, by rfl⟩ : syracuseStep 2013545 = 1510159) B1510159
theorem B4028777 : Blo 1192413 4028777 := bstep (se 2 (by rfl) ⟨1510791, by rfl⟩ : syracuseStep 4028777 = 3021583) B3021583
theorem B1194363 : Blo 1192413 1194363 := bstep (se 1 (by rfl) ⟨895772, by rfl⟩ : syracuseStep 1194363 = 1791545) B1791545
theorem B3824167 : Blo 1192413 3824167 := bstep (se 1 (by rfl) ⟨2868125, by rfl⟩ : syracuseStep 3824167 = 5736251) B5736251
theorem B6044219 : Blo 1192413 6044219 := bstep (se 1 (by rfl) ⟨4533164, by rfl⟩ : syracuseStep 6044219 = 9066329) B9066329
theorem B1342075 : Blo 1192413 1342075 := bstep (se 1 (by rfl) ⟨1006556, by rfl⟩ : syracuseStep 1342075 = 2013113) B2013113
theorem B2685563 : Blo 1192413 2685563 := bstep (se 1 (by rfl) ⟨2014172, by rfl⟩ : syracuseStep 2685563 = 4028345) B4028345
theorem B7641773 : Blo 1192413 7641773 := bstep (se 3 (by rfl) ⟨1432832, by rfl⟩ : syracuseStep 7641773 = 2865665) B2865665
theorem B2013943 : Blo 1192413 2013943 := bstep (se 1 (by rfl) ⟨1510457, by rfl⟩ : syracuseStep 2013943 = 3020915) B3020915
theorem B2685689 : Blo 1192413 2685689 := bstep (se 2 (by rfl) ⟨1007133, by rfl⟩ : syracuseStep 2685689 = 2014267) B2014267
theorem B6454019 : Blo 1192413 6454019 := bstep (se 1 (by rfl) ⟨4840514, by rfl⟩ : syracuseStep 6454019 = 9681029) B9681029
theorem B3398507 : Blo 1192413 3398507 := bstep (se 1 (by rfl) ⟨2548880, by rfl⟩ : syracuseStep 3398507 = 5097761) B5097761
theorem B1595431 : Blo 1192413 1595431 := bstep (se 1 (by rfl) ⟨1196573, by rfl⟩ : syracuseStep 1595431 = 2393147) B2393147
theorem B2014139 : Blo 1192413 2014139 := bstep (se 1 (by rfl) ⟨1510604, by rfl⟩ : syracuseStep 2014139 = 3021209) B3021209
theorem B4029371 : Blo 1192413 4029371 := bstep (se 1 (by rfl) ⟨3022028, by rfl⟩ : syracuseStep 4029371 = 6044057) B6044057
theorem B2685959 : Blo 1192413 2685959 := bstep (se 1 (by rfl) ⟨2014469, by rfl⟩ : syracuseStep 2685959 = 4028939) B4028939
theorem B2014247 : Blo 1192413 2014247 := bstep (se 1 (by rfl) ⟨1510685, by rfl⟩ : syracuseStep 2014247 = 3021371) B3021371
theorem B7756843 : Blo 1192413 7756843 := bstep (se 1 (by rfl) ⟨5817632, by rfl⟩ : syracuseStep 7756843 = 11635265) B11635265
theorem B1342543 : Blo 1192413 1342543 := bstep (se 1 (by rfl) ⟨1006907, by rfl⟩ : syracuseStep 1342543 = 2013815) B2013815
theorem B3398735 : Blo 1192413 3398735 := bstep (se 1 (by rfl) ⟨2549051, by rfl⟩ : syracuseStep 3398735 = 5098103) B5098103
theorem B2686031 : Blo 1192413 2686031 := bstep (se 1 (by rfl) ⟨2014523, by rfl⟩ : syracuseStep 2686031 = 4029047) B4029047
theorem B6044867 : Blo 1192413 6044867 := bstep (se 1 (by rfl) ⟨4533650, by rfl⟩ : syracuseStep 6044867 = 9067301) B9067301
theorem B2014537 : Blo 1192413 2014537 := bstep (se 2 (by rfl) ⟨755451, by rfl⟩ : syracuseStep 2014537 = 1510903) B1510903
theorem B2014571 : Blo 1192413 2014571 := bstep (se 1 (by rfl) ⟨1510928, by rfl⟩ : syracuseStep 2014571 = 3021857) B3021857
theorem B9674149 : Blo 1192413 9674149 := bstep (se 4 (by rfl) ⟨906951, by rfl⟩ : syracuseStep 9674149 = 1813903) B1813903
theorem B4529627 : Blo 1192413 4529627 := bstep (se 1 (by rfl) ⟨3397220, by rfl⟩ : syracuseStep 4529627 = 6794441) B6794441
theorem B1342939 : Blo 1192413 1342939 := bstep (se 1 (by rfl) ⟨1007204, by rfl⟩ : syracuseStep 1342939 = 2014409) B2014409
theorem B2686427 : Blo 1192413 2686427 := bstep (se 1 (by rfl) ⟨2014820, by rfl⟩ : syracuseStep 2686427 = 4029641) B4029641
theorem B3022535 : Blo 1192413 3022535 := bstep (se 1 (by rfl) ⟨2266901, by rfl⟩ : syracuseStep 3022535 = 4533803) B4533803
theorem B2014969 : Blo 1192413 2014969 := bstep (se 2 (by rfl) ⟨755613, by rfl⟩ : syracuseStep 2014969 = 1511227) B1511227
theorem B5734253 : Blo 1192413 5734253 := bstep (se 3 (by rfl) ⟨1075172, by rfl⟩ : syracuseStep 5734253 = 2150345) B2150345
theorem B5447533 : Blo 1192413 5447533 := bstep (se 3 (by rfl) ⟨1021412, by rfl⟩ : syracuseStep 5447533 = 2042825) B2042825
theorem B1343407 : Blo 1192413 1343407 := bstep (se 1 (by rfl) ⟨1007555, by rfl⟩ : syracuseStep 1343407 = 2015111) B2015111
theorem B2686895 : Blo 1192413 2686895 := bstep (se 1 (by rfl) ⟨2015171, by rfl⟩ : syracuseStep 2686895 = 4030343) B4030343
theorem B2686985 : Blo 1192413 2686985 := bstep (se 2 (by rfl) ⟨1007619, by rfl⟩ : syracuseStep 2686985 = 2015239) B2015239
theorem B7643155 : Blo 1192413 7643155 := bstep (se 1 (by rfl) ⟨5732366, by rfl⟩ : syracuseStep 7643155 = 11464733) B11464733
theorem B9674801 : Blo 1192413 9674801 := bstep (se 2 (by rfl) ⟨3628050, by rfl⟩ : syracuseStep 9674801 = 7256101) B7256101
theorem B22946003 : Blo 1192413 22946003 := bstep (se 1 (by rfl) ⟨17209502, by rfl⟩ : syracuseStep 22946003 = 34419005) B34419005
theorem B2867567 : Blo 1192413 2867567 := bstep (se 1 (by rfl) ⟨2150675, by rfl⟩ : syracuseStep 2867567 = 4301351) B4301351
theorem B2687399 : Blo 1192413 2687399 := bstep (se 1 (by rfl) ⟨2015549, by rfl⟩ : syracuseStep 2687399 = 4031099) B4031099
theorem B3023315 : Blo 1192413 3023315 := bstep (se 1 (by rfl) ⟨2267486, by rfl⟩ : syracuseStep 3023315 = 4534973) B4534973
theorem B3269089 : Blo 1192413 3269089 := bstep (se 2 (by rfl) ⟨1225908, by rfl⟩ : syracuseStep 3269089 = 2451817) B2451817
theorem B3400375 : Blo 1192413 3400375 := bstep (se 1 (by rfl) ⟨2550281, by rfl⟩ : syracuseStep 3400375 = 5100563) B5100563
theorem B6128311 : Blo 1192413 6128311 := bstep (se 1 (by rfl) ⟨4596233, by rfl⟩ : syracuseStep 6128311 = 9192467) B9192467
theorem B8602361 : Blo 1192413 8602361 := bstep (se 2 (by rfl) ⟨3225885, by rfl⟩ : syracuseStep 8602361 = 6451771) B6451771
theorem B5743439 : Blo 1192413 5743439 := bstep (se 1 (by rfl) ⟨4307579, by rfl⟩ : syracuseStep 5743439 = 8615159) B8615159
theorem B18359135 : Blo 1192413 18359135 := bstep (se 1 (by rfl) ⟨13769351, by rfl⟩ : syracuseStep 18359135 = 27538703) B27538703
theorem B6120593 : Blo 1192413 6120593 := bstep (se 2 (by rfl) ⟨2295222, by rfl⟩ : syracuseStep 6120593 = 4590445) B4590445
theorem B11461931 : Blo 1192413 11461931 := bstep (se 1 (by rfl) ⟨8596448, by rfl⟩ : syracuseStep 11461931 = 17192897) B17192897
theorem B2295137 : Blo 1192413 2295137 := bstep (se 2 (by rfl) ⟨860676, by rfl⟩ : syracuseStep 2295137 = 1721353) B1721353
theorem B12912185 : Blo 1192413 12912185 := bstep (se 2 (by rfl) ⟨4842069, by rfl⟩ : syracuseStep 12912185 = 9684139) B9684139
theorem B6039197 : Blo 1192413 6039197 := bstep (se 3 (by rfl) ⟨1132349, by rfl⟩ : syracuseStep 6039197 = 2264699) B2264699
theorem B4302679 : Blo 1192413 4302679 := bstep (se 1 (by rfl) ⟨3227009, by rfl⟩ : syracuseStep 4302679 = 6454019) B6454019
theorem B10192787 : Blo 1192413 10192787 := bstep (se 1 (by rfl) ⟨7644590, by rfl⟩ : syracuseStep 10192787 = 15289181) B15289181
theorem B20662537 : Blo 1192413 20662537 := bstep (se 2 (by rfl) ⟨7748451, by rfl⟩ : syracuseStep 20662537 = 15496903) B15496903
theorem B2263727 : Blo 1192413 2263727 := bstep (se 1 (by rfl) ⟨1697795, by rfl⟩ : syracuseStep 2263727 = 3395591) B3395591
theorem B4025213 : Blo 1192413 4025213 := bstep (se 3 (by rfl) ⟨754727, by rfl⟩ : syracuseStep 4025213 = 1509455) B1509455
theorem B2263963 : Blo 1192413 2263963 := bstep (se 1 (by rfl) ⟨1697972, by rfl⟩ : syracuseStep 2263963 = 3395945) B3395945
theorem B1788827 : Blo 1192413 1788827 := bstep (se 1 (by rfl) ⟨1341620, by rfl⟩ : syracuseStep 1788827 = 2683241) B2683241
theorem B6040493 : Blo 1192413 6040493 := bstep (se 3 (by rfl) ⟨1132592, by rfl⟩ : syracuseStep 6040493 = 2265185) B2265185
theorem B13266035 : Blo 1192413 13266035 := bstep (se 1 (by rfl) ⟨9949526, by rfl⟩ : syracuseStep 13266035 = 19899053) B19899053
theorem B6450299 : Blo 1192413 6450299 := bstep (se 1 (by rfl) ⟨4837724, by rfl⟩ : syracuseStep 6450299 = 9675449) B9675449
theorem B4025483 : Blo 1192413 4025483 := bstep (se 1 (by rfl) ⟨3019112, by rfl⟩ : syracuseStep 4025483 = 6038225) B6038225
theorem B22056137 : Blo 1192413 22056137 := bstep (se 2 (by rfl) ⟨8271051, by rfl⟩ : syracuseStep 22056137 = 16542103) B16542103
theorem B1789223 : Blo 1192413 1789223 := bstep (se 1 (by rfl) ⟨1341917, by rfl⟩ : syracuseStep 1789223 = 2683835) B2683835
theorem B1789307 : Blo 1192413 1789307 := bstep (se 1 (by rfl) ⟨1341980, by rfl⟩ : syracuseStep 1789307 = 2683961) B2683961
theorem B5098889 : Blo 1192413 5098889 := bstep (se 2 (by rfl) ⟨1912083, by rfl⟩ : syracuseStep 5098889 = 3824167) B3824167
theorem B1789433 : Blo 1192413 1789433 := bstep (se 2 (by rfl) ⟨671037, by rfl⟩ : syracuseStep 1789433 = 1342075) B1342075
theorem B1273415 : Blo 1192413 1273415 := bstep (se 1 (by rfl) ⟨955061, by rfl⟩ : syracuseStep 1273415 = 1910123) B1910123
theorem B3018323 : Blo 1192413 3018323 := bstep (se 1 (by rfl) ⟨2263742, by rfl⟩ : syracuseStep 3018323 = 4527485) B4527485
theorem B1789535 : Blo 1192413 1789535 := bstep (se 1 (by rfl) ⟨1342151, by rfl⟩ : syracuseStep 1789535 = 2684303) B2684303
theorem B1912583 : Blo 1192413 1912583 := bstep (se 1 (by rfl) ⟨1434437, by rfl⟩ : syracuseStep 1912583 = 2868875) B2868875
theorem B10342187 : Blo 1192413 10342187 := bstep (se 1 (by rfl) ⟨7756640, by rfl⟩ : syracuseStep 10342187 = 15513281) B15513281
theorem B1789751 : Blo 1192413 1789751 := bstep (se 1 (by rfl) ⟨1342313, by rfl⟩ : syracuseStep 1789751 = 2684627) B2684627
theorem B1511399 : Blo 1192413 1511399 := bstep (se 1 (by rfl) ⟨1133549, by rfl⟩ : syracuseStep 1511399 = 2267099) B2267099
theorem B10342457 : Blo 1192413 10342457 := bstep (se 2 (by rfl) ⟨3878421, by rfl⟩ : syracuseStep 10342457 = 7756843) B7756843
theorem B16330817 : Blo 1192413 16330817 := bstep (se 2 (by rfl) ⟨6124056, by rfl⟩ : syracuseStep 16330817 = 12248113) B12248113
theorem B8605763 : Blo 1192413 8605763 := bstep (se 1 (by rfl) ⟨6454322, by rfl⟩ : syracuseStep 8605763 = 12908645) B12908645
theorem B4591721 : Blo 1192413 4591721 := bstep (se 2 (by rfl) ⟨1721895, by rfl⟩ : syracuseStep 4591721 = 3443791) B3443791
theorem B1790057 : Blo 1192413 1790057 := bstep (se 2 (by rfl) ⟨671271, by rfl⟩ : syracuseStep 1790057 = 1342543) B1342543
theorem B5738825 : Blo 1192413 5738825 := bstep (se 2 (by rfl) ⟨2152059, by rfl⟩ : syracuseStep 5738825 = 4304119) B4304119
theorem B1790375 : Blo 1192413 1790375 := bstep (se 1 (by rfl) ⟨1342781, by rfl⟩ : syracuseStep 1790375 = 2685563) B2685563
theorem B1192443 : Blo 1192413 1192443 := bstep (se 1 (by rfl) ⟨894332, by rfl⟩ : syracuseStep 1192443 = 1788665) B1788665
theorem B1790459 : Blo 1192413 1790459 := bstep (se 1 (by rfl) ⟨1342844, by rfl⟩ : syracuseStep 1790459 = 2685689) B2685689
theorem B1700347 : Blo 1192413 1700347 := bstep (se 1 (by rfl) ⟨1275260, by rfl⟩ : syracuseStep 1700347 = 2550521) B2550521
theorem B6042113 : Blo 1192413 6042113 := bstep (se 2 (by rfl) ⟨2265792, by rfl⟩ : syracuseStep 6042113 = 4531585) B4531585
theorem B12898865 : Blo 1192413 12898865 := bstep (se 2 (by rfl) ⟨4837074, by rfl⟩ : syracuseStep 12898865 = 9674149) B9674149
theorem B1192511 : Blo 1192413 1192511 := bstep (se 1 (by rfl) ⟨894383, by rfl⟩ : syracuseStep 1192511 = 1788767) B1788767
theorem B1192519 : Blo 1192413 1192519 := bstep (se 1 (by rfl) ⟨894389, by rfl⟩ : syracuseStep 1192519 = 1788779) B1788779
theorem B2265671 : Blo 1192413 2265671 := bstep (se 1 (by rfl) ⟨1699253, by rfl⟩ : syracuseStep 2265671 = 3398507) B3398507
theorem B1790585 : Blo 1192413 1790585 := bstep (se 2 (by rfl) ⟨671469, by rfl⟩ : syracuseStep 1790585 = 1342939) B1342939
theorem B34402967 : Blo 1192413 34402967 := bstep (se 1 (by rfl) ⟨25802225, by rfl⟩ : syracuseStep 34402967 = 51604451) B51604451
theorem B1790639 : Blo 1192413 1790639 := bstep (se 1 (by rfl) ⟨1342979, by rfl⟩ : syracuseStep 1790639 = 2685959) B2685959
theorem B1192671 : Blo 1192413 1192671 := bstep (se 1 (by rfl) ⟨894503, by rfl⟩ : syracuseStep 1192671 = 1789007) B1789007
theorem B4027103 : Blo 1192413 4027103 := bstep (se 1 (by rfl) ⟨3020327, by rfl⟩ : syracuseStep 4027103 = 6040655) B6040655
theorem B2265823 : Blo 1192413 2265823 := bstep (se 1 (by rfl) ⟨1699367, by rfl⟩ : syracuseStep 2265823 = 3398735) B3398735
theorem B1790687 : Blo 1192413 1790687 := bstep (se 1 (by rfl) ⟨1343015, by rfl⟩ : syracuseStep 1790687 = 2686031) B2686031
theorem B1192751 : Blo 1192413 1192751 := bstep (se 1 (by rfl) ⟨894563, by rfl⟩ : syracuseStep 1192751 = 1789127) B1789127
theorem B2683727 : Blo 1192413 2683727 := bstep (se 1 (by rfl) ⟨2012795, by rfl⟩ : syracuseStep 2683727 = 4025591) B4025591
theorem B1192859 : Blo 1192413 1192859 := bstep (se 1 (by rfl) ⟨894644, by rfl⟩ : syracuseStep 1192859 = 1789289) B1789289
theorem B1192911 : Blo 1192413 1192911 := bstep (se 1 (by rfl) ⟨894683, by rfl⟩ : syracuseStep 1192911 = 1789367) B1789367
theorem B1192935 : Blo 1192413 1192935 := bstep (se 1 (by rfl) ⟨894701, by rfl⟩ : syracuseStep 1192935 = 1789403) B1789403
theorem B3019751 : Blo 1192413 3019751 := bstep (se 1 (by rfl) ⟨2264813, by rfl⟩ : syracuseStep 3019751 = 4529627) B4529627
theorem B6042599 : Blo 1192413 6042599 := bstep (se 1 (by rfl) ⟨4531949, by rfl⟩ : syracuseStep 6042599 = 9063899) B9063899
theorem B1790951 : Blo 1192413 1790951 := bstep (se 1 (by rfl) ⟨1343213, by rfl⟩ : syracuseStep 1790951 = 2686427) B2686427
theorem B2683943 : Blo 1192413 2683943 := bstep (se 1 (by rfl) ⟨2012957, by rfl⟩ : syracuseStep 2683943 = 4025915) B4025915
theorem B2012303 : Blo 1192413 2012303 := bstep (se 1 (by rfl) ⟨1509227, by rfl⟩ : syracuseStep 2012303 = 3018455) B3018455
theorem B4027535 : Blo 1192413 4027535 := bstep (se 1 (by rfl) ⟨3020651, by rfl⟩ : syracuseStep 4027535 = 6041303) B6041303
theorem B7263377 : Blo 1192413 7263377 := bstep (se 2 (by rfl) ⟨2723766, by rfl⟩ : syracuseStep 7263377 = 5447533) B5447533
theorem B2684123 : Blo 1192413 2684123 := bstep (se 1 (by rfl) ⟨2013092, by rfl⟩ : syracuseStep 2684123 = 4026185) B4026185
theorem B1791209 : Blo 1192413 1791209 := bstep (se 2 (by rfl) ⟨671703, by rfl⟩ : syracuseStep 1791209 = 1343407) B1343407
theorem B3822835 : Blo 1192413 3822835 := bstep (se 1 (by rfl) ⟨2867126, by rfl⟩ : syracuseStep 3822835 = 5734253) B5734253
theorem B3446009 : Blo 1192413 3446009 := bstep (se 2 (by rfl) ⟨1292253, by rfl⟩ : syracuseStep 3446009 = 2584507) B2584507
theorem B1193247 : Blo 1192413 1193247 := bstep (se 1 (by rfl) ⟨894935, by rfl⟩ : syracuseStep 1193247 = 1789871) B1789871
theorem B1791263 : Blo 1192413 1791263 := bstep (se 1 (by rfl) ⟨1343447, by rfl⟩ : syracuseStep 1791263 = 2686895) B2686895
theorem B6042923 : Blo 1192413 6042923 := bstep (se 1 (by rfl) ⟨4532192, by rfl⟩ : syracuseStep 6042923 = 9064385) B9064385
theorem B1193307 : Blo 1192413 1193307 := bstep (se 1 (by rfl) ⟨894980, by rfl⟩ : syracuseStep 1193307 = 1789961) B1789961
theorem B6796649 : Blo 1192413 6796649 := bstep (se 2 (by rfl) ⟨2548743, by rfl⟩ : syracuseStep 6796649 = 5097487) B5097487
theorem B1193327 : Blo 1192413 1193327 := bstep (se 1 (by rfl) ⟨894995, by rfl⟩ : syracuseStep 1193327 = 1789991) B1789991
theorem B7263593 : Blo 1192413 7263593 := bstep (se 2 (by rfl) ⟨2723847, by rfl⟩ : syracuseStep 7263593 = 5447695) B5447695
theorem B2012539 : Blo 1192413 2012539 := bstep (se 1 (by rfl) ⟨1509404, by rfl⟩ : syracuseStep 2012539 = 3018809) B3018809
theorem B10327421 : Blo 1192413 10327421 := bstep (se 3 (by rfl) ⟨1936391, by rfl⟩ : syracuseStep 10327421 = 3872783) B3872783
theorem B2127241 : Blo 1192413 2127241 := bstep (se 2 (by rfl) ⟨797715, by rfl⟩ : syracuseStep 2127241 = 1595431) B1595431
theorem B2684321 : Blo 1192413 2684321 := bstep (se 2 (by rfl) ⟨1006620, by rfl⟩ : syracuseStep 2684321 = 2013241) B2013241
theorem B1193383 : Blo 1192413 1193383 := bstep (se 1 (by rfl) ⟨895037, by rfl⟩ : syracuseStep 1193383 = 1790075) B1790075
theorem B1791431 : Blo 1192413 1791431 := bstep (se 1 (by rfl) ⟨1343573, by rfl⟩ : syracuseStep 1791431 = 2687147) B2687147
theorem B1193467 : Blo 1192413 1193467 := bstep (se 1 (by rfl) ⟨895100, by rfl⟩ : syracuseStep 1193467 = 1790201) B1790201
theorem B1193535 : Blo 1192413 1193535 := bstep (se 1 (by rfl) ⟨895151, by rfl⟩ : syracuseStep 1193535 = 1790303) B1790303
theorem B1193543 : Blo 1192413 1193543 := bstep (se 1 (by rfl) ⟨895157, by rfl⟩ : syracuseStep 1193543 = 1790315) B1790315
theorem B3397277 : Blo 1192413 3397277 := bstep (se 3 (by rfl) ⟨636989, by rfl⟩ : syracuseStep 3397277 = 1273979) B1273979
theorem B3020449 : Blo 1192413 3020449 := bstep (se 2 (by rfl) ⟨1132668, by rfl⟩ : syracuseStep 3020449 = 2265337) B2265337
theorem B1193695 : Blo 1192413 1193695 := bstep (se 1 (by rfl) ⟨895271, by rfl⟩ : syracuseStep 1193695 = 1790543) B1790543
theorem B13604597 : Blo 1192413 13604597 := bstep (se 5 (by rfl) ⟨637715, by rfl⟩ : syracuseStep 13604597 = 1275431) B1275431
theorem B3020591 : Blo 1192413 3020591 := bstep (se 1 (by rfl) ⟨2265443, by rfl⟩ : syracuseStep 3020591 = 4530887) B4530887
theorem B1193775 : Blo 1192413 1193775 := bstep (se 1 (by rfl) ⟨895331, by rfl⟩ : syracuseStep 1193775 = 1790663) B1790663
theorem B1193883 : Blo 1192413 1193883 := bstep (se 1 (by rfl) ⟨895412, by rfl⟩ : syracuseStep 1193883 = 1790825) B1790825
theorem B20395961 : Blo 1192413 20395961 := bstep (se 2 (by rfl) ⟨7648485, by rfl⟩ : syracuseStep 20395961 = 15296971) B15296971
theorem B2684879 : Blo 1192413 2684879 := bstep (se 1 (by rfl) ⟨2013659, by rfl⟩ : syracuseStep 2684879 = 4027319) B4027319
theorem B1193935 : Blo 1192413 1193935 := bstep (se 1 (by rfl) ⟨895451, by rfl⟩ : syracuseStep 1193935 = 1790903) B1790903
theorem B1193959 : Blo 1192413 1193959 := bstep (se 1 (by rfl) ⟨895469, by rfl⟩ : syracuseStep 1193959 = 1790939) B1790939
theorem B5093455 : Blo 1192413 5093455 := bstep (se 1 (by rfl) ⟨3820091, by rfl⟩ : syracuseStep 5093455 = 7640183) B7640183
theorem B13588559 : Blo 1192413 13588559 := bstep (se 1 (by rfl) ⟨10191419, by rfl⟩ : syracuseStep 13588559 = 20382839) B20382839
theorem B20658311 : Blo 1192413 20658311 := bstep (se 1 (by rfl) ⟨15493733, by rfl⟩ : syracuseStep 20658311 = 30987467) B30987467
theorem B6043895 : Blo 1192413 6043895 := bstep (se 1 (by rfl) ⟨4532921, by rfl⟩ : syracuseStep 6043895 = 9065843) B9065843
theorem B4028669 : Blo 1192413 4028669 := bstep (se 3 (by rfl) ⟨755375, by rfl⟩ : syracuseStep 4028669 = 1510751) B1510751
theorem B23263499 : Blo 1192413 23263499 := bstep (se 1 (by rfl) ⟨17447624, by rfl⟩ : syracuseStep 23263499 = 34895249) B34895249
theorem B1194271 : Blo 1192413 1194271 := bstep (se 1 (by rfl) ⟨895703, by rfl⟩ : syracuseStep 1194271 = 1791407) B1791407
theorem B2685257 : Blo 1192413 2685257 := bstep (se 2 (by rfl) ⟨1006971, by rfl⟩ : syracuseStep 2685257 = 2013943) B2013943
theorem B1341787 : Blo 1192413 1341787 := bstep (se 1 (by rfl) ⟨1006340, by rfl⟩ : syracuseStep 1341787 = 2012681) B2012681
theorem B2685275 : Blo 1192413 2685275 := bstep (se 1 (by rfl) ⟨2013956, by rfl⟩ : syracuseStep 2685275 = 4027913) B4027913
theorem B1194331 : Blo 1192413 1194331 := bstep (se 1 (by rfl) ⟨895748, by rfl⟩ : syracuseStep 1194331 = 1791497) B1791497
theorem B1194351 : Blo 1192413 1194351 := bstep (se 1 (by rfl) ⟨895763, by rfl⟩ : syracuseStep 1194351 = 1791527) B1791527
theorem B1194407 : Blo 1192413 1194407 := bstep (se 1 (by rfl) ⟨895805, by rfl⟩ : syracuseStep 1194407 = 1791611) B1791611
theorem B3021239 : Blo 1192413 3021239 := bstep (se 1 (by rfl) ⟨2265929, by rfl⟩ : syracuseStep 3021239 = 4531859) B4531859
theorem B1341895 : Blo 1192413 1341895 := bstep (se 1 (by rfl) ⟨1006421, by rfl⟩ : syracuseStep 1341895 = 2012843) B2012843
theorem B4192847 : Blo 1192413 4192847 := bstep (se 1 (by rfl) ⟨3144635, by rfl⟩ : syracuseStep 4192847 = 6289271) B6289271
theorem B5446223 : Blo 1192413 5446223 := bstep (se 1 (by rfl) ⟨4084667, by rfl⟩ : syracuseStep 5446223 = 8169335) B8169335
theorem B6044381 : Blo 1192413 6044381 := bstep (se 3 (by rfl) ⟨1133321, by rfl⟩ : syracuseStep 6044381 = 2266643) B2266643
theorem B17005331 : Blo 1192413 17005331 := bstep (se 1 (by rfl) ⟨12753998, by rfl⟩ : syracuseStep 17005331 = 25507997) B25507997
theorem B1342255 : Blo 1192413 1342255 := bstep (se 1 (by rfl) ⟨1006691, by rfl⟩ : syracuseStep 1342255 = 2013383) B2013383
theorem B2014031 : Blo 1192413 2014031 := bstep (se 1 (by rfl) ⟨1510523, by rfl⟩ : syracuseStep 2014031 = 3021047) B3021047
theorem B1342363 : Blo 1192413 1342363 := bstep (se 1 (by rfl) ⟨1006772, by rfl⟩ : syracuseStep 1342363 = 2013545) B2013545
theorem B1612699 : Blo 1192413 1612699 := bstep (se 1 (by rfl) ⟨1209524, by rfl⟩ : syracuseStep 1612699 = 2419049) B2419049
theorem B2685851 : Blo 1192413 2685851 := bstep (se 1 (by rfl) ⟨2014388, by rfl⟩ : syracuseStep 2685851 = 4028777) B4028777
theorem B4029479 : Blo 1192413 4029479 := bstep (se 1 (by rfl) ⟨3022109, by rfl⟩ : syracuseStep 4029479 = 6044219) B6044219
theorem B2686049 : Blo 1192413 2686049 := bstep (se 2 (by rfl) ⟨1007268, by rfl⟩ : syracuseStep 2686049 = 2014537) B2014537
theorem B5094515 : Blo 1192413 5094515 := bstep (se 1 (by rfl) ⟨3820886, by rfl⟩ : syracuseStep 5094515 = 7641773) B7641773
theorem B9067787 : Blo 1192413 9067787 := bstep (se 1 (by rfl) ⟨6800840, by rfl⟩ : syracuseStep 9067787 = 13601681) B13601681
theorem B6036767 : Blo 1192413 6036767 := bstep (se 1 (by rfl) ⟨4527575, by rfl⟩ : syracuseStep 6036767 = 9055151) B9055151
theorem B1342759 : Blo 1192413 1342759 := bstep (se 1 (by rfl) ⟨1007069, by rfl⟩ : syracuseStep 1342759 = 2014139) B2014139
theorem B2686247 : Blo 1192413 2686247 := bstep (se 1 (by rfl) ⟨2014685, by rfl⟩ : syracuseStep 2686247 = 4029371) B4029371
theorem B1342831 : Blo 1192413 1342831 := bstep (se 1 (by rfl) ⟨1007123, by rfl⟩ : syracuseStep 1342831 = 2014247) B2014247
theorem B4029911 : Blo 1192413 4029911 := bstep (se 1 (by rfl) ⟨3022433, by rfl⟩ : syracuseStep 4029911 = 6044867) B6044867
theorem B3022343 : Blo 1192413 3022343 := bstep (se 1 (by rfl) ⟨2266757, by rfl⟩ : syracuseStep 3022343 = 4533515) B4533515
theorem B13770263 : Blo 1192413 13770263 := bstep (se 1 (by rfl) ⟨10327697, by rfl⟩ : syracuseStep 13770263 = 20655395) B20655395
theorem B3022393 : Blo 1192413 3022393 := bstep (se 2 (by rfl) ⟨1133397, by rfl⟩ : syracuseStep 3022393 = 2266795) B2266795
theorem B1343047 : Blo 1192413 1343047 := bstep (se 1 (by rfl) ⟨1007285, by rfl⟩ : syracuseStep 1343047 = 2014571) B2014571
theorem B32652881 : Blo 1192413 32652881 := bstep (se 2 (by rfl) ⟨12244830, by rfl⟩ : syracuseStep 32652881 = 24489661) B24489661
theorem B6446753 : Blo 1192413 6446753 := bstep (se 2 (by rfl) ⟨2417532, by rfl⟩ : syracuseStep 6446753 = 4835065) B4835065
theorem B2686625 : Blo 1192413 2686625 := bstep (se 2 (by rfl) ⟨1007484, by rfl⟩ : syracuseStep 2686625 = 2014969) B2014969
theorem B2547463 : Blo 1192413 2547463 := bstep (se 1 (by rfl) ⟨1910597, by rfl⟩ : syracuseStep 2547463 = 3821195) B3821195
theorem B2015023 : Blo 1192413 2015023 := bstep (se 1 (by rfl) ⟨1511267, by rfl⟩ : syracuseStep 2015023 = 3022535) B3022535
theorem B3022697 : Blo 1192413 3022697 := bstep (se 2 (by rfl) ⟨1133511, by rfl⟩ : syracuseStep 3022697 = 2267023) B2267023
theorem B25173935 : Blo 1192413 25173935 := bstep (se 1 (by rfl) ⟨18880451, by rfl⟩ : syracuseStep 25173935 = 37760903) B37760903
theorem B10190873 : Blo 1192413 10190873 := bstep (se 2 (by rfl) ⟨3821577, by rfl⟩ : syracuseStep 10190873 = 7643155) B7643155
theorem B10887211 : Blo 1192413 10887211 := bstep (se 1 (by rfl) ⟨8165408, by rfl⟩ : syracuseStep 10887211 = 16330817) B16330817
theorem B6791273 : Blo 1192413 6791273 := bstep (se 2 (by rfl) ⟨2546727, by rfl⟩ : syracuseStep 6791273 = 5093455) B5093455
theorem B3825883 : Blo 1192413 3825883 := bstep (se 1 (by rfl) ⟨2869412, by rfl⟩ : syracuseStep 3825883 = 5738825) B5738825
theorem B2015543 : Blo 1192413 2015543 := bstep (se 1 (by rfl) ⟨1511657, by rfl⟩ : syracuseStep 2015543 = 3023315) B3023315
theorem B27550049 : Blo 1192413 27550049 := bstep (se 2 (by rfl) ⟨10331268, by rfl⟩ : syracuseStep 27550049 = 20662537) B20662537
theorem B5734907 : Blo 1192413 5734907 := bstep (se 1 (by rfl) ⟨4301180, by rfl⟩ : syracuseStep 5734907 = 8602361) B8602361
theorem B12239423 : Blo 1192413 12239423 := bstep (se 1 (by rfl) ⟨9179567, by rfl⟩ : syracuseStep 12239423 = 18359135) B18359135
theorem B4080395 : Blo 1192413 4080395 := bstep (se 1 (by rfl) ⟨3060296, by rfl⟩ : syracuseStep 4080395 = 6120593) B6120593
theorem B4842251 : Blo 1192413 4842251 := bstep (se 1 (by rfl) ⟨3631688, by rfl⟩ : syracuseStep 4842251 = 7263377) B7263377
theorem B4531099 : Blo 1192413 4531099 := bstep (se 1 (by rfl) ⟨3398324, by rfl⟩ : syracuseStep 4531099 = 6796649) B6796649
theorem B4842395 : Blo 1192413 4842395 := bstep (se 1 (by rfl) ⟨3631796, by rfl⟩ : syracuseStep 4842395 = 7263593) B7263593
theorem B9069731 : Blo 1192413 9069731 := bstep (se 1 (by rfl) ⟨6802298, by rfl⟩ : syracuseStep 9069731 = 13604597) B13604597
theorem B13772207 : Blo 1192413 13772207 := bstep (se 1 (by rfl) ⟨10329155, by rfl⟩ : syracuseStep 13772207 = 20658311) B20658311
theorem B15508999 : Blo 1192413 15508999 := bstep (se 1 (by rfl) ⟨11631749, by rfl⟩ : syracuseStep 15508999 = 23263499) B23263499
theorem B5097113 : Blo 1192413 5097113 := bstep (se 2 (by rfl) ⟨1911417, by rfl⟩ : syracuseStep 5097113 = 3822835) B3822835
theorem B2795231 : Blo 1192413 2795231 := bstep (se 1 (by rfl) ⟨2096423, by rfl⟩ : syracuseStep 2795231 = 4192847) B4192847
theorem B3630815 : Blo 1192413 3630815 := bstep (se 1 (by rfl) ⟨2723111, by rfl⟩ : syracuseStep 3630815 = 5446223) B5446223
theorem B4024511 : Blo 1192413 4024511 := bstep (se 1 (by rfl) ⟨3018383, by rfl⟩ : syracuseStep 4024511 = 6036767) B6036767
theorem B21768587 : Blo 1192413 21768587 := bstep (se 1 (by rfl) ⟨16326440, by rfl⟩ : syracuseStep 21768587 = 32652881) B32652881
theorem B5736905 : Blo 1192413 5736905 := bstep (se 2 (by rfl) ⟨2151339, by rfl⟩ : syracuseStep 5736905 = 4302679) B4302679
theorem B17435141 : Blo 1192413 17435141 := bstep (se 4 (by rfl) ⟨1634544, by rfl⟩ : syracuseStep 17435141 = 3269089) B3269089
theorem B6449867 : Blo 1192413 6449867 := bstep (se 1 (by rfl) ⟨4837400, by rfl⟩ : syracuseStep 6449867 = 9674801) B9674801
theorem B5737175 : Blo 1192413 5737175 := bstep (se 1 (by rfl) ⟨4302881, by rfl⟩ : syracuseStep 5737175 = 8605763) B8605763
theorem B15297335 : Blo 1192413 15297335 := bstep (se 1 (by rfl) ⟨11473001, by rfl⟩ : syracuseStep 15297335 = 22946003) B22946003
theorem B1789049 : Blo 1192413 1789049 := bstep (se 2 (by rfl) ⟨670893, by rfl⟩ : syracuseStep 1789049 = 1341787) B1341787
theorem B3828959 : Blo 1192413 3828959 := bstep (se 1 (by rfl) ⟨2871719, by rfl⟩ : syracuseStep 3828959 = 5743439) B5743439
theorem B1789151 : Blo 1192413 1789151 := bstep (se 1 (by rfl) ⟨1341863, by rfl⟩ : syracuseStep 1789151 = 2683727) B2683727
theorem B1789193 : Blo 1192413 1789193 := bstep (se 2 (by rfl) ⟨670947, by rfl⟩ : syracuseStep 1789193 = 1341895) B1341895
theorem B1789295 : Blo 1192413 1789295 := bstep (se 1 (by rfl) ⟨1341971, by rfl⟩ : syracuseStep 1789295 = 2683943) B2683943
theorem B1789415 : Blo 1192413 1789415 := bstep (se 1 (by rfl) ⟨1342061, by rfl⟩ : syracuseStep 1789415 = 2684123) B2684123
theorem B2297339 : Blo 1192413 2297339 := bstep (se 1 (by rfl) ⟨1723004, by rfl⟩ : syracuseStep 2297339 = 3446009) B3446009
theorem B4533833 : Blo 1192413 4533833 := bstep (se 2 (by rfl) ⟨1700187, by rfl⟩ : syracuseStep 4533833 = 3400375) B3400375
theorem B8171081 : Blo 1192413 8171081 := bstep (se 2 (by rfl) ⟨3064155, by rfl⟩ : syracuseStep 8171081 = 6128311) B6128311
theorem B6884947 : Blo 1192413 6884947 := bstep (se 1 (by rfl) ⟨5163710, by rfl⟩ : syracuseStep 6884947 = 10327421) B10327421
theorem B1789547 : Blo 1192413 1789547 := bstep (se 1 (by rfl) ⟨1342160, by rfl⟩ : syracuseStep 1789547 = 2684321) B2684321
theorem B1789673 : Blo 1192413 1789673 := bstep (se 2 (by rfl) ⟨671127, by rfl⟩ : syracuseStep 1789673 = 1342255) B1342255
theorem B4026131 : Blo 1192413 4026131 := bstep (se 1 (by rfl) ⟨3019598, by rfl⟩ : syracuseStep 4026131 = 6039197) B6039197
theorem B2264851 : Blo 1192413 2264851 := bstep (se 1 (by rfl) ⟨1698638, by rfl⟩ : syracuseStep 2264851 = 3397277) B3397277
theorem B3018617 : Blo 1192413 3018617 := bstep (se 2 (by rfl) ⟨1131981, by rfl⟩ : syracuseStep 3018617 = 2263963) B2263963
theorem B1789817 : Blo 1192413 1789817 := bstep (se 2 (by rfl) ⟨671181, by rfl⟩ : syracuseStep 1789817 = 1342363) B1342363
theorem B6795191 : Blo 1192413 6795191 := bstep (se 1 (by rfl) ⟨5096393, by rfl⟩ : syracuseStep 6795191 = 10192787) B10192787
theorem B1789919 : Blo 1192413 1789919 := bstep (se 1 (by rfl) ⟨1342439, by rfl⟩ : syracuseStep 1789919 = 2684879) B2684879
theorem B36720701 : Blo 1192413 36720701 := bstep (se 3 (by rfl) ⟨6885131, by rfl⟩ : syracuseStep 36720701 = 13770263) B13770263
theorem B3395773 : Blo 1192413 3395773 := bstep (se 3 (by rfl) ⟨636707, by rfl⟩ : syracuseStep 3395773 = 1273415) B1273415
theorem B6041789 : Blo 1192413 6041789 := bstep (se 3 (by rfl) ⟨1132835, by rfl⟩ : syracuseStep 6041789 = 2265671) B2265671
theorem B1790171 : Blo 1192413 1790171 := bstep (se 1 (by rfl) ⟨1342628, by rfl⟩ : syracuseStep 1790171 = 2685257) B2685257
theorem B1790183 : Blo 1192413 1790183 := bstep (se 1 (by rfl) ⟨1342637, by rfl⟩ : syracuseStep 1790183 = 2685275) B2685275
theorem B1790345 : Blo 1192413 1790345 := bstep (se 2 (by rfl) ⟨671379, by rfl⟩ : syracuseStep 1790345 = 1342759) B1342759
theorem B1790441 : Blo 1192413 1790441 := bstep (se 2 (by rfl) ⟨671415, by rfl⟩ : syracuseStep 1790441 = 1342831) B1342831
theorem B2683385 : Blo 1192413 2683385 := bstep (se 2 (by rfl) ⟨1006269, by rfl⟩ : syracuseStep 2683385 = 2012539) B2012539
theorem B2683475 : Blo 1192413 2683475 := bstep (se 1 (by rfl) ⟨2012606, by rfl⟩ : syracuseStep 2683475 = 4025213) B4025213
theorem B1192551 : Blo 1192413 1192551 := bstep (se 1 (by rfl) ⟨894413, by rfl⟩ : syracuseStep 1192551 = 1788827) B1788827
theorem B1790567 : Blo 1192413 1790567 := bstep (se 1 (by rfl) ⟨1342925, by rfl⟩ : syracuseStep 1790567 = 2685851) B2685851
theorem B4026995 : Blo 1192413 4026995 := bstep (se 1 (by rfl) ⟨3020246, by rfl⟩ : syracuseStep 4026995 = 6040493) B6040493
theorem B5100221 : Blo 1192413 5100221 := bstep (se 3 (by rfl) ⟨956291, by rfl⟩ : syracuseStep 5100221 = 1912583) B1912583
theorem B1790699 : Blo 1192413 1790699 := bstep (se 1 (by rfl) ⟨1343024, by rfl⟩ : syracuseStep 1790699 = 2686049) B2686049
theorem B3396343 : Blo 1192413 3396343 := bstep (se 1 (by rfl) ⟨2547257, by rfl⟩ : syracuseStep 3396343 = 5094515) B5094515
theorem B8844023 : Blo 1192413 8844023 := bstep (se 1 (by rfl) ⟨6633017, by rfl⟩ : syracuseStep 8844023 = 13266035) B13266035
theorem B2683655 : Blo 1192413 2683655 := bstep (se 1 (by rfl) ⟨2012741, by rfl⟩ : syracuseStep 2683655 = 4025483) B4025483
theorem B1790729 : Blo 1192413 1790729 := bstep (se 2 (by rfl) ⟨671523, by rfl⟩ : syracuseStep 1790729 = 1343047) B1343047
theorem B1192815 : Blo 1192413 1192815 := bstep (se 1 (by rfl) ⟨894611, by rfl⟩ : syracuseStep 1192815 = 1789223) B1789223
theorem B1790831 : Blo 1192413 1790831 := bstep (se 1 (by rfl) ⟨1343123, by rfl⟩ : syracuseStep 1790831 = 2686247) B2686247
theorem B4027265 : Blo 1192413 4027265 := bstep (se 2 (by rfl) ⟨1510224, by rfl⟩ : syracuseStep 4027265 = 3020449) B3020449
theorem B1192871 : Blo 1192413 1192871 := bstep (se 1 (by rfl) ⟨894653, by rfl⟩ : syracuseStep 1192871 = 1789307) B1789307
theorem B1192955 : Blo 1192413 1192955 := bstep (se 1 (by rfl) ⟨894716, by rfl⟩ : syracuseStep 1192955 = 1789433) B1789433
theorem B3396617 : Blo 1192413 3396617 := bstep (se 2 (by rfl) ⟨1273731, by rfl⟩ : syracuseStep 3396617 = 2547463) B2547463
theorem B2012215 : Blo 1192413 2012215 := bstep (se 1 (by rfl) ⟨1509161, by rfl⟩ : syracuseStep 2012215 = 3018323) B3018323
theorem B1193023 : Blo 1192413 1193023 := bstep (se 1 (by rfl) ⟨894767, by rfl⟩ : syracuseStep 1193023 = 1789535) B1789535
theorem B4297835 : Blo 1192413 4297835 := bstep (se 1 (by rfl) ⟨3223376, by rfl⟩ : syracuseStep 4297835 = 6446753) B6446753
theorem B1791083 : Blo 1192413 1791083 := bstep (se 1 (by rfl) ⟨1343312, by rfl⟩ : syracuseStep 1791083 = 2686625) B2686625
theorem B1193167 : Blo 1192413 1193167 := bstep (se 1 (by rfl) ⟨894875, by rfl⟩ : syracuseStep 1193167 = 1789751) B1789751
theorem B6894791 : Blo 1192413 6894791 := bstep (se 1 (by rfl) ⟨5171093, by rfl⟩ : syracuseStep 6894791 = 10342187) B10342187
theorem B16782623 : Blo 1192413 16782623 := bstep (se 1 (by rfl) ⟨12586967, by rfl⟩ : syracuseStep 16782623 = 25173935) B25173935
theorem B1791323 : Blo 1192413 1791323 := bstep (se 1 (by rfl) ⟨1343492, by rfl⟩ : syracuseStep 1791323 = 2686985) B2686985
theorem B6894971 : Blo 1192413 6894971 := bstep (se 1 (by rfl) ⟨5171228, by rfl⟩ : syracuseStep 6894971 = 10342457) B10342457
theorem B3061147 : Blo 1192413 3061147 := bstep (se 1 (by rfl) ⟨2295860, by rfl⟩ : syracuseStep 3061147 = 4591721) B4591721
theorem B1193371 : Blo 1192413 1193371 := bstep (se 1 (by rfl) ⟨895028, by rfl⟩ : syracuseStep 1193371 = 1790057) B1790057
theorem B1193583 : Blo 1192413 1193583 := bstep (se 1 (by rfl) ⟨895187, by rfl⟩ : syracuseStep 1193583 = 1790375) B1790375
theorem B1791599 : Blo 1192413 1791599 := bstep (se 1 (by rfl) ⟨1343699, by rfl⟩ : syracuseStep 1791599 = 2687399) B2687399
theorem B1193639 : Blo 1192413 1193639 := bstep (se 1 (by rfl) ⟨895229, by rfl⟩ : syracuseStep 1193639 = 1790459) B1790459
theorem B4028075 : Blo 1192413 4028075 := bstep (se 1 (by rfl) ⟨3021056, by rfl⟩ : syracuseStep 4028075 = 6042113) B6042113
theorem B8599243 : Blo 1192413 8599243 := bstep (se 1 (by rfl) ⟨6449432, by rfl⟩ : syracuseStep 8599243 = 12898865) B12898865
theorem B1193723 : Blo 1192413 1193723 := bstep (se 1 (by rfl) ⟨895292, by rfl⟩ : syracuseStep 1193723 = 1790585) B1790585
theorem B22935311 : Blo 1192413 22935311 := bstep (se 1 (by rfl) ⟨17201483, by rfl⟩ : syracuseStep 22935311 = 34402967) B34402967
theorem B1193759 : Blo 1192413 1193759 := bstep (se 1 (by rfl) ⟨895319, by rfl⟩ : syracuseStep 1193759 = 1790639) B1790639
theorem B2684735 : Blo 1192413 2684735 := bstep (se 1 (by rfl) ⟨2013551, by rfl⟩ : syracuseStep 2684735 = 4027103) B4027103
theorem B1193791 : Blo 1192413 1193791 := bstep (se 1 (by rfl) ⟨895343, by rfl⟩ : syracuseStep 1193791 = 1790687) B1790687
theorem B2013167 : Blo 1192413 2013167 := bstep (se 1 (by rfl) ⟨1509875, by rfl⟩ : syracuseStep 2013167 = 3019751) B3019751
theorem B4028399 : Blo 1192413 4028399 := bstep (se 1 (by rfl) ⟨3021299, by rfl⟩ : syracuseStep 4028399 = 6042599) B6042599
theorem B1193967 : Blo 1192413 1193967 := bstep (se 1 (by rfl) ⟨895475, by rfl⟩ : syracuseStep 1193967 = 1790951) B1790951
theorem B2267129 : Blo 1192413 2267129 := bstep (se 2 (by rfl) ⟨850173, by rfl⟩ : syracuseStep 2267129 = 1700347) B1700347
theorem B1341535 : Blo 1192413 1341535 := bstep (se 1 (by rfl) ⟨1006151, by rfl⟩ : syracuseStep 1341535 = 2012303) B2012303
theorem B2685023 : Blo 1192413 2685023 := bstep (se 1 (by rfl) ⟨2013767, by rfl⟩ : syracuseStep 2685023 = 4027535) B4027535
theorem B1194139 : Blo 1192413 1194139 := bstep (se 1 (by rfl) ⟨895604, by rfl⟩ : syracuseStep 1194139 = 1791209) B1791209
theorem B1194175 : Blo 1192413 1194175 := bstep (se 1 (by rfl) ⟨895631, by rfl⟩ : syracuseStep 1194175 = 1791263) B1791263
theorem B7641287 : Blo 1192413 7641287 := bstep (se 1 (by rfl) ⟨5730965, by rfl⟩ : syracuseStep 7641287 = 11461931) B11461931
theorem B4028615 : Blo 1192413 4028615 := bstep (se 1 (by rfl) ⟨3021461, by rfl⟩ : syracuseStep 4028615 = 6042923) B6042923
theorem B1530091 : Blo 1192413 1530091 := bstep (se 1 (by rfl) ⟨1147568, by rfl⟩ : syracuseStep 1530091 = 2295137) B2295137
theorem B3021097 : Blo 1192413 3021097 := bstep (se 2 (by rfl) ⟨1132911, by rfl⟩ : syracuseStep 3021097 = 2265823) B2265823
theorem B1194287 : Blo 1192413 1194287 := bstep (se 1 (by rfl) ⟨895715, by rfl⟩ : syracuseStep 1194287 = 1791431) B1791431
theorem B8608123 : Blo 1192413 8608123 := bstep (se 1 (by rfl) ⟨6456092, by rfl⟩ : syracuseStep 8608123 = 12912185) B12912185
theorem B30587381 : Blo 1192413 30587381 := bstep (se 5 (by rfl) ⟨1433783, by rfl⟩ : syracuseStep 30587381 = 2867567) B2867567
theorem B2013727 : Blo 1192413 2013727 := bstep (se 1 (by rfl) ⟨1510295, by rfl⟩ : syracuseStep 2013727 = 3020591) B3020591
theorem B13597307 : Blo 1192413 13597307 := bstep (se 1 (by rfl) ⟨10197980, by rfl⟩ : syracuseStep 13597307 = 20395961) B20395961
theorem B9059039 : Blo 1192413 9059039 := bstep (se 1 (by rfl) ⟨6794279, by rfl⟩ : syracuseStep 9059039 = 13588559) B13588559
theorem B4029263 : Blo 1192413 4029263 := bstep (se 1 (by rfl) ⟨3021947, by rfl⟩ : syracuseStep 4029263 = 6043895) B6043895
theorem B2685779 : Blo 1192413 2685779 := bstep (se 1 (by rfl) ⟨2014334, by rfl⟩ : syracuseStep 2685779 = 4028669) B4028669
theorem B2014159 : Blo 1192413 2014159 := bstep (se 1 (by rfl) ⟨1510619, by rfl⟩ : syracuseStep 2014159 = 3021239) B3021239
theorem B6036605 : Blo 1192413 6036605 := bstep (se 3 (by rfl) ⟨1131863, by rfl⟩ : syracuseStep 6036605 = 2263727) B2263727
theorem B4029587 : Blo 1192413 4029587 := bstep (se 1 (by rfl) ⟨3022190, by rfl⟩ : syracuseStep 4029587 = 6044381) B6044381
theorem B11336887 : Blo 1192413 11336887 := bstep (se 1 (by rfl) ⟨8502665, by rfl⟩ : syracuseStep 11336887 = 17005331) B17005331
theorem B1342687 : Blo 1192413 1342687 := bstep (se 1 (by rfl) ⟨1007015, by rfl⟩ : syracuseStep 1342687 = 2014031) B2014031
theorem B2686319 : Blo 1192413 2686319 := bstep (se 1 (by rfl) ⟨2014739, by rfl⟩ : syracuseStep 2686319 = 4029479) B4029479
theorem B11345285 : Blo 1192413 11345285 := bstep (se 4 (by rfl) ⟨1063620, by rfl⟩ : syracuseStep 11345285 = 2127241) B2127241
theorem B4029857 : Blo 1192413 4029857 := bstep (se 2 (by rfl) ⟨1511196, by rfl⟩ : syracuseStep 4029857 = 3022393) B3022393
theorem B4300199 : Blo 1192413 4300199 := bstep (se 1 (by rfl) ⟨3225149, by rfl⟩ : syracuseStep 4300199 = 6450299) B6450299
theorem B14704091 : Blo 1192413 14704091 := bstep (se 1 (by rfl) ⟨11028068, by rfl⟩ : syracuseStep 14704091 = 22056137) B22056137
theorem B8601061 : Blo 1192413 8601061 := bstep (se 4 (by rfl) ⟨806349, by rfl⟩ : syracuseStep 8601061 = 1612699) B1612699
theorem B6045191 : Blo 1192413 6045191 := bstep (se 1 (by rfl) ⟨4533893, by rfl⟩ : syracuseStep 6045191 = 9067787) B9067787
theorem B3399259 : Blo 1192413 3399259 := bstep (se 1 (by rfl) ⟨2549444, by rfl⟩ : syracuseStep 3399259 = 5098889) B5098889
theorem B2686607 : Blo 1192413 2686607 := bstep (se 1 (by rfl) ⟨2014955, by rfl⟩ : syracuseStep 2686607 = 4029911) B4029911
theorem B2014895 : Blo 1192413 2014895 := bstep (se 1 (by rfl) ⟨1511171, by rfl⟩ : syracuseStep 2014895 = 3022343) B3022343
theorem B2686697 : Blo 1192413 2686697 := bstep (se 2 (by rfl) ⟨1007511, by rfl⟩ : syracuseStep 2686697 = 2015023) B2015023
theorem B2015131 : Blo 1192413 2015131 := bstep (se 1 (by rfl) ⟨1511348, by rfl⟩ : syracuseStep 2015131 = 3022697) B3022697
theorem B4030397 : Blo 1192413 4030397 := bstep (se 3 (by rfl) ⟨755699, by rfl⟩ : syracuseStep 4030397 = 1511399) B1511399
theorem B14516281 : Blo 1192413 14516281 := bstep (se 2 (by rfl) ⟨5443605, by rfl⟩ : syracuseStep 14516281 = 10887211) B10887211
theorem B1343695 : Blo 1192413 1343695 := bstep (se 1 (by rfl) ⟨1007771, by rfl⟩ : syracuseStep 1343695 = 2015543) B2015543
theorem B2040121 : Blo 1192413 2040121 := bstep (se 2 (by rfl) ⟨765045, by rfl⟩ : syracuseStep 2040121 = 1530091) B1530091
theorem B8159615 : Blo 1192413 8159615 := bstep (se 1 (by rfl) ⟨6119711, by rfl⟩ : syracuseStep 8159615 = 12239423) B12239423
theorem B3400147 : Blo 1192413 3400147 := bstep (se 1 (by rfl) ⟨2550110, by rfl⟩ : syracuseStep 3400147 = 5100221) B5100221
theorem B11477497 : Blo 1192413 11477497 := bstep (se 2 (by rfl) ⟨4304061, by rfl⟩ : syracuseStep 11477497 = 8608123) B8608123
theorem B3228167 : Blo 1192413 3228167 := bstep (se 1 (by rfl) ⟨2421125, by rfl⟩ : syracuseStep 3228167 = 4842251) B4842251
theorem B3228263 : Blo 1192413 3228263 := bstep (se 1 (by rfl) ⟨2421197, by rfl⟩ : syracuseStep 3228263 = 4842395) B4842395
theorem B6046487 : Blo 1192413 6046487 := bstep (se 1 (by rfl) ⟨4534865, by rfl⟩ : syracuseStep 6046487 = 9069731) B9069731
theorem B4596527 : Blo 1192413 4596527 := bstep (se 1 (by rfl) ⟨3447395, by rfl⟩ : syracuseStep 4596527 = 6894791) B6894791
theorem B4596647 : Blo 1192413 4596647 := bstep (se 1 (by rfl) ⟨3447485, by rfl⟩ : syracuseStep 4596647 = 6894971) B6894971
theorem B73466797 : Blo 1192413 73466797 := bstep (se 3 (by rfl) ⟨13775024, by rfl⟩ : syracuseStep 73466797 = 27550049) B27550049
theorem B20391587 : Blo 1192413 20391587 := bstep (se 1 (by rfl) ⟨15293690, by rfl⟩ : syracuseStep 20391587 = 30587381) B30587381
theorem B6039359 : Blo 1192413 6039359 := bstep (se 1 (by rfl) ⟨4529519, by rfl⟩ : syracuseStep 6039359 = 9059039) B9059039
theorem B4081529 : Blo 1192413 4081529 := bstep (se 2 (by rfl) ⟨1530573, by rfl⟩ : syracuseStep 4081529 = 3061147) B3061147
theorem B20678665 : Blo 1192413 20678665 := bstep (se 2 (by rfl) ⟨7754499, by rfl⟩ : syracuseStep 20678665 = 15508999) B15508999
theorem B10881053 : Blo 1192413 10881053 := bstep (se 3 (by rfl) ⟨2040197, by rfl⟩ : syracuseStep 10881053 = 4080395) B4080395
theorem B4024403 : Blo 1192413 4024403 := bstep (se 1 (by rfl) ⟨3018302, by rfl⟩ : syracuseStep 4024403 = 6036605) B6036605
theorem B4532345 : Blo 1192413 4532345 := bstep (se 2 (by rfl) ⟨1699629, by rfl⟩ : syracuseStep 4532345 = 3399259) B3399259
theorem B7563523 : Blo 1192413 7563523 := bstep (se 1 (by rfl) ⟨5672642, by rfl⟩ : syracuseStep 7563523 = 11345285) B11345285
theorem B6793915 : Blo 1192413 6793915 := bstep (se 1 (by rfl) ⟨5095436, by rfl⟩ : syracuseStep 6793915 = 10190873) B10190873
theorem B24480467 : Blo 1192413 24480467 := bstep (se 1 (by rfl) ⟨18360350, by rfl⟩ : syracuseStep 24480467 = 36720701) B36720701
theorem B1788713 : Blo 1192413 1788713 := bstep (se 2 (by rfl) ⟨670767, by rfl⟩ : syracuseStep 1788713 = 1341535) B1341535
theorem B1788923 : Blo 1192413 1788923 := bstep (se 1 (by rfl) ⟨1341692, by rfl⟩ : syracuseStep 1788923 = 2683385) B2683385
theorem B1788983 : Blo 1192413 1788983 := bstep (se 1 (by rfl) ⟨1341737, by rfl⟩ : syracuseStep 1788983 = 2683475) B2683475
theorem B1789103 : Blo 1192413 1789103 := bstep (se 1 (by rfl) ⟨1341827, by rfl⟩ : syracuseStep 1789103 = 2683655) B2683655
theorem B2264411 : Blo 1192413 2264411 := bstep (se 1 (by rfl) ⟨1698308, by rfl⟩ : syracuseStep 2264411 = 3396617) B3396617
theorem B2420543 : Blo 1192413 2420543 := bstep (se 1 (by rfl) ⟨1815407, by rfl⟩ : syracuseStep 2420543 = 3630815) B3630815
theorem B15290207 : Blo 1192413 15290207 := bstep (se 1 (by rfl) ⟨11467655, by rfl⟩ : syracuseStep 15290207 = 22935311) B22935311
theorem B6041465 : Blo 1192413 6041465 := bstep (se 2 (by rfl) ⟨2265549, by rfl⟩ : syracuseStep 6041465 = 4531099) B4531099
theorem B1789823 : Blo 1192413 1789823 := bstep (se 1 (by rfl) ⟨1342367, by rfl⟩ : syracuseStep 1789823 = 2684735) B2684735
theorem B1790015 : Blo 1192413 1790015 := bstep (se 1 (by rfl) ⟨1342511, by rfl⟩ : syracuseStep 1790015 = 2685023) B2685023
theorem B2682953 : Blo 1192413 2682953 := bstep (se 2 (by rfl) ⟨1006107, by rfl⟩ : syracuseStep 2682953 = 2012215) B2012215
theorem B2683007 : Blo 1192413 2683007 := bstep (se 1 (by rfl) ⟨2012255, by rfl⟩ : syracuseStep 2683007 = 4024511) B4024511
theorem B14512391 : Blo 1192413 14512391 := bstep (se 1 (by rfl) ⟨10884293, by rfl⟩ : syracuseStep 14512391 = 21768587) B21768587
theorem B1790249 : Blo 1192413 1790249 := bstep (se 2 (by rfl) ⟨671343, by rfl⟩ : syracuseStep 1790249 = 1342687) B1342687
theorem B9064871 : Blo 1192413 9064871 := bstep (se 1 (by rfl) ⟨6798653, by rfl⟩ : syracuseStep 9064871 = 13597307) B13597307
theorem B1790519 : Blo 1192413 1790519 := bstep (se 1 (by rfl) ⟨1342889, by rfl⟩ : syracuseStep 1790519 = 2685779) B2685779
theorem B1192699 : Blo 1192413 1192699 := bstep (se 1 (by rfl) ⟨894524, by rfl⟩ : syracuseStep 1192699 = 1789049) B1789049
theorem B9179929 : Blo 1192413 9179929 := bstep (se 2 (by rfl) ⟨3442473, by rfl⟩ : syracuseStep 9179929 = 6884947) B6884947
theorem B2552639 : Blo 1192413 2552639 := bstep (se 1 (by rfl) ⟨1914479, by rfl⟩ : syracuseStep 2552639 = 3828959) B3828959
theorem B1192767 : Blo 1192413 1192767 := bstep (se 1 (by rfl) ⟨894575, by rfl⟩ : syracuseStep 1192767 = 1789151) B1789151
theorem B1192795 : Blo 1192413 1192795 := bstep (se 1 (by rfl) ⟨894596, by rfl⟩ : syracuseStep 1192795 = 1789193) B1789193
theorem B1192863 : Blo 1192413 1192863 := bstep (se 1 (by rfl) ⟨894647, by rfl⟩ : syracuseStep 1192863 = 1789295) B1789295
theorem B1790879 : Blo 1192413 1790879 := bstep (se 1 (by rfl) ⟨1343159, by rfl⟩ : syracuseStep 1790879 = 2686319) B2686319
theorem B11465657 : Blo 1192413 11465657 := bstep (se 2 (by rfl) ⟨4299621, by rfl⟩ : syracuseStep 11465657 = 8599243) B8599243
theorem B9802727 : Blo 1192413 9802727 := bstep (se 1 (by rfl) ⟨7352045, by rfl⟩ : syracuseStep 9802727 = 14704091) B14704091
theorem B1192943 : Blo 1192413 1192943 := bstep (se 1 (by rfl) ⟨894707, by rfl⟩ : syracuseStep 1192943 = 1789415) B1789415
theorem B3019801 : Blo 1192413 3019801 := bstep (se 2 (by rfl) ⟨1132425, by rfl⟩ : syracuseStep 3019801 = 2264851) B2264851
theorem B1193031 : Blo 1192413 1193031 := bstep (se 1 (by rfl) ⟨894773, by rfl⟩ : syracuseStep 1193031 = 1789547) B1789547
theorem B1791071 : Blo 1192413 1791071 := bstep (se 1 (by rfl) ⟨1343303, by rfl⟩ : syracuseStep 1791071 = 2686607) B2686607
theorem B1193115 : Blo 1192413 1193115 := bstep (se 1 (by rfl) ⟨894836, by rfl⟩ : syracuseStep 1193115 = 1789673) B1789673
theorem B1791131 : Blo 1192413 1791131 := bstep (se 1 (by rfl) ⟨1343348, by rfl⟩ : syracuseStep 1791131 = 2686697) B2686697
theorem B2684087 : Blo 1192413 2684087 := bstep (se 1 (by rfl) ⟨2013065, by rfl⟩ : syracuseStep 2684087 = 4026131) B4026131
theorem B2012411 : Blo 1192413 2012411 := bstep (se 1 (by rfl) ⟨1509308, by rfl⟩ : syracuseStep 2012411 = 3018617) B3018617
theorem B1193211 : Blo 1192413 1193211 := bstep (se 1 (by rfl) ⟨894908, by rfl⟩ : syracuseStep 1193211 = 1789817) B1789817
theorem B1193279 : Blo 1192413 1193279 := bstep (se 1 (by rfl) ⟨894959, by rfl⟩ : syracuseStep 1193279 = 1789919) B1789919
theorem B4527515 : Blo 1192413 4527515 := bstep (se 1 (by rfl) ⟨3395636, by rfl⟩ : syracuseStep 4527515 = 6791273) B6791273
theorem B4027859 : Blo 1192413 4027859 := bstep (se 1 (by rfl) ⟨3020894, by rfl⟩ : syracuseStep 4027859 = 6041789) B6041789
theorem B1193447 : Blo 1192413 1193447 := bstep (se 1 (by rfl) ⟨895085, by rfl⟩ : syracuseStep 1193447 = 1790171) B1790171
theorem B1193455 : Blo 1192413 1193455 := bstep (se 1 (by rfl) ⟨895091, by rfl⟩ : syracuseStep 1193455 = 1790183) B1790183
theorem B4527697 : Blo 1192413 4527697 := bstep (se 2 (by rfl) ⟨1697886, by rfl⟩ : syracuseStep 4527697 = 3395773) B3395773
theorem B1193563 : Blo 1192413 1193563 := bstep (se 1 (by rfl) ⟨895172, by rfl⟩ : syracuseStep 1193563 = 1790345) B1790345
theorem B1193627 : Blo 1192413 1193627 := bstep (se 1 (by rfl) ⟨895220, by rfl⟩ : syracuseStep 1193627 = 1790441) B1790441
theorem B3823271 : Blo 1192413 3823271 := bstep (se 1 (by rfl) ⟨2867453, by rfl⟩ : syracuseStep 3823271 = 5734907) B5734907
theorem B4028129 : Blo 1192413 4028129 := bstep (se 2 (by rfl) ⟨1510548, by rfl⟩ : syracuseStep 4028129 = 3021097) B3021097
theorem B1193711 : Blo 1192413 1193711 := bstep (se 1 (by rfl) ⟨895283, by rfl⟩ : syracuseStep 1193711 = 1790567) B1790567
theorem B2684663 : Blo 1192413 2684663 := bstep (se 1 (by rfl) ⟨2013497, by rfl⟩ : syracuseStep 2684663 = 4026995) B4026995
theorem B1193799 : Blo 1192413 1193799 := bstep (se 1 (by rfl) ⟨895349, by rfl⟩ : syracuseStep 1193799 = 1790699) B1790699
theorem B1193819 : Blo 1192413 1193819 := bstep (se 1 (by rfl) ⟨895364, by rfl⟩ : syracuseStep 1193819 = 1790729) B1790729
theorem B1193887 : Blo 1192413 1193887 := bstep (se 1 (by rfl) ⟨895415, by rfl⟩ : syracuseStep 1193887 = 1790831) B1790831
theorem B2684843 : Blo 1192413 2684843 := bstep (se 1 (by rfl) ⟨2013632, by rfl⟩ : syracuseStep 2684843 = 4027265) B4027265
theorem B2684969 : Blo 1192413 2684969 := bstep (se 2 (by rfl) ⟨1006863, by rfl⟩ : syracuseStep 2684969 = 2013727) B2013727
theorem B2865223 : Blo 1192413 2865223 := bstep (se 1 (by rfl) ⟨2148917, by rfl⟩ : syracuseStep 2865223 = 4297835) B4297835
theorem B1194055 : Blo 1192413 1194055 := bstep (se 1 (by rfl) ⟨895541, by rfl⟩ : syracuseStep 1194055 = 1791083) B1791083
theorem B11188415 : Blo 1192413 11188415 := bstep (se 1 (by rfl) ⟨8391311, by rfl⟩ : syracuseStep 11188415 = 16782623) B16782623
theorem B1194215 : Blo 1192413 1194215 := bstep (se 1 (by rfl) ⟨895661, by rfl⟩ : syracuseStep 1194215 = 1791323) B1791323
theorem B9181471 : Blo 1192413 9181471 := bstep (se 1 (by rfl) ⟨6886103, by rfl⟩ : syracuseStep 9181471 = 13772207) B13772207
theorem B60463397 : Blo 1192413 60463397 := bstep (se 4 (by rfl) ⟨5668443, by rfl⟩ : syracuseStep 60463397 = 11336887) B11336887
theorem B4528457 : Blo 1192413 4528457 := bstep (se 2 (by rfl) ⟨1698171, by rfl⟩ : syracuseStep 4528457 = 3396343) B3396343
theorem B1194399 : Blo 1192413 1194399 := bstep (se 1 (by rfl) ⟨895799, by rfl⟩ : syracuseStep 1194399 = 1791599) B1791599
theorem B3398075 : Blo 1192413 3398075 := bstep (se 1 (by rfl) ⟨2548556, by rfl⟩ : syracuseStep 3398075 = 5097113) B5097113
theorem B2685383 : Blo 1192413 2685383 := bstep (se 1 (by rfl) ⟨2014037, by rfl⟩ : syracuseStep 2685383 = 4028075) B4028075
theorem B20404709 : Blo 1192413 20404709 := bstep (se 4 (by rfl) ⟨1912941, by rfl⟩ : syracuseStep 20404709 = 3825883) B3825883
theorem B2685545 : Blo 1192413 2685545 := bstep (se 2 (by rfl) ⟨1007079, by rfl⟩ : syracuseStep 2685545 = 2014159) B2014159
theorem B1342111 : Blo 1192413 1342111 := bstep (se 1 (by rfl) ⟨1006583, by rfl⟩ : syracuseStep 1342111 = 2013167) B2013167
theorem B2685599 : Blo 1192413 2685599 := bstep (se 1 (by rfl) ⟨2014199, by rfl⟩ : syracuseStep 2685599 = 4028399) B4028399
theorem B5094191 : Blo 1192413 5094191 := bstep (se 1 (by rfl) ⟨3820643, by rfl⟩ : syracuseStep 5094191 = 7641287) B7641287
theorem B2685743 : Blo 1192413 2685743 := bstep (se 1 (by rfl) ⟨2014307, by rfl⟩ : syracuseStep 2685743 = 4028615) B4028615
theorem B3824603 : Blo 1192413 3824603 := bstep (se 1 (by rfl) ⟨2868452, by rfl⟩ : syracuseStep 3824603 = 5736905) B5736905
theorem B11623427 : Blo 1192413 11623427 := bstep (se 1 (by rfl) ⟨8717570, by rfl⟩ : syracuseStep 11623427 = 17435141) B17435141
theorem B4299911 : Blo 1192413 4299911 := bstep (se 1 (by rfl) ⟨3224933, by rfl⟩ : syracuseStep 4299911 = 6449867) B6449867
theorem B3824783 : Blo 1192413 3824783 := bstep (se 1 (by rfl) ⟨2868587, by rfl⟩ : syracuseStep 3824783 = 5737175) B5737175
theorem B10198223 : Blo 1192413 10198223 := bstep (se 1 (by rfl) ⟨7648667, by rfl⟩ : syracuseStep 10198223 = 15297335) B15297335
theorem B2686175 : Blo 1192413 2686175 := bstep (se 1 (by rfl) ⟨2014631, by rfl⟩ : syracuseStep 2686175 = 4029263) B4029263
theorem B7453949 : Blo 1192413 7453949 := bstep (se 3 (by rfl) ⟨1397615, by rfl⟩ : syracuseStep 7453949 = 2795231) B2795231
theorem B11468081 : Blo 1192413 11468081 := bstep (se 2 (by rfl) ⟨4300530, by rfl⟩ : syracuseStep 11468081 = 8601061) B8601061
theorem B23584061 : Blo 1192413 23584061 := bstep (se 3 (by rfl) ⟨4422011, by rfl⟩ : syracuseStep 23584061 = 8844023) B8844023
theorem B2686391 : Blo 1192413 2686391 := bstep (se 1 (by rfl) ⟨2014793, by rfl⟩ : syracuseStep 2686391 = 4029587) B4029587
theorem B2686571 : Blo 1192413 2686571 := bstep (se 1 (by rfl) ⟨2014928, by rfl⟩ : syracuseStep 2686571 = 4029857) B4029857
theorem B2866799 : Blo 1192413 2866799 := bstep (se 1 (by rfl) ⟨2150099, by rfl⟩ : syracuseStep 2866799 = 4300199) B4300199
theorem B1531559 : Blo 1192413 1531559 := bstep (se 1 (by rfl) ⟨1148669, by rfl⟩ : syracuseStep 1531559 = 2297339) B2297339
theorem B4030127 : Blo 1192413 4030127 := bstep (se 1 (by rfl) ⟨3022595, by rfl⟩ : syracuseStep 4030127 = 6045191) B6045191
theorem B3022555 : Blo 1192413 3022555 := bstep (se 1 (by rfl) ⟨2266916, by rfl⟩ : syracuseStep 3022555 = 4533833) B4533833
theorem B5447387 : Blo 1192413 5447387 := bstep (se 1 (by rfl) ⟨4085540, by rfl⟩ : syracuseStep 5447387 = 8171081) B8171081
theorem B1343263 : Blo 1192413 1343263 := bstep (se 1 (by rfl) ⟨1007447, by rfl⟩ : syracuseStep 1343263 = 2014895) B2014895
theorem B2686841 : Blo 1192413 2686841 := bstep (se 2 (by rfl) ⟨1007565, by rfl⟩ : syracuseStep 2686841 = 2015131) B2015131
theorem B4530127 : Blo 1192413 4530127 := bstep (se 1 (by rfl) ⟨3397595, by rfl⟩ : syracuseStep 4530127 = 6795191) B6795191
theorem B2686931 : Blo 1192413 2686931 := bstep (se 1 (by rfl) ⟨2015198, by rfl⟩ : syracuseStep 2686931 = 4030397) B4030397
theorem B6045677 : Blo 1192413 6045677 := bstep (se 3 (by rfl) ⟨1133564, by rfl⟩ : syracuseStep 6045677 = 2267129) B2267129
theorem B9674927 : Blo 1192413 9674927 := bstep (se 1 (by rfl) ⟨7256195, by rfl⟩ : syracuseStep 9674927 = 14512391) B14512391
theorem B5439743 : Blo 1192413 5439743 := bstep (se 1 (by rfl) ⟨4079807, by rfl⟩ : syracuseStep 5439743 = 8159615) B8159615
theorem B10084697 : Blo 1192413 10084697 := bstep (se 2 (by rfl) ⟨3781761, by rfl⟩ : syracuseStep 10084697 = 7563523) B7563523
theorem B2720161 : Blo 1192413 2720161 := bstep (se 2 (by rfl) ⟨1020060, by rfl⟩ : syracuseStep 2720161 = 2040121) B2040121
theorem B29835773 : Blo 1192413 29835773 := bstep (se 3 (by rfl) ⟨5594207, by rfl⟩ : syracuseStep 29835773 = 11188415) B11188415
theorem B4030991 : Blo 1192413 4030991 := bstep (se 1 (by rfl) ⟨3023243, by rfl⟩ : syracuseStep 4030991 = 6046487) B6046487
theorem B3064351 : Blo 1192413 3064351 := bstep (se 1 (by rfl) ⟨2298263, by rfl⟩ : syracuseStep 3064351 = 4596527) B4596527
theorem B7643771 : Blo 1192413 7643771 := bstep (se 1 (by rfl) ⟨5732828, by rfl⟩ : syracuseStep 7643771 = 11465657) B11465657
theorem B15303329 : Blo 1192413 15303329 := bstep (se 2 (by rfl) ⟨5738748, by rfl⟩ : syracuseStep 15303329 = 11477497) B11477497
theorem B62890829 : Blo 1192413 62890829 := bstep (se 3 (by rfl) ⟨11792030, by rfl⟩ : syracuseStep 62890829 = 23584061) B23584061
theorem B12239905 : Blo 1192413 12239905 := bstep (se 2 (by rfl) ⟨4589964, by rfl⟩ : syracuseStep 12239905 = 9179929) B9179929
theorem B2548847 : Blo 1192413 2548847 := bstep (se 1 (by rfl) ⟨1911635, by rfl⟩ : syracuseStep 2548847 = 3823271) B3823271
theorem B16320311 : Blo 1192413 16320311 := bstep (se 1 (by rfl) ⟨12240233, by rfl⟩ : syracuseStep 16320311 = 24480467) B24480467
theorem B2549735 : Blo 1192413 2549735 := bstep (se 1 (by rfl) ⟨1912301, by rfl⟩ : syracuseStep 2549735 = 3824603) B3824603
theorem B2549855 : Blo 1192413 2549855 := bstep (se 1 (by rfl) ⟨1912391, by rfl⟩ : syracuseStep 2549855 = 3824783) B3824783
theorem B7645387 : Blo 1192413 7645387 := bstep (se 1 (by rfl) ⟨5734040, by rfl⟩ : syracuseStep 7645387 = 11468081) B11468081
theorem B1509607 : Blo 1192413 1509607 := bstep (se 1 (by rfl) ⟨1132205, by rfl⟩ : syracuseStep 1509607 = 2264411) B2264411
theorem B1911199 : Blo 1192413 1911199 := bstep (se 1 (by rfl) ⟨1433399, by rfl⟩ : syracuseStep 1911199 = 2866799) B2866799
theorem B12257725 : Blo 1192413 12257725 := bstep (se 3 (by rfl) ⟨2298323, by rfl⟩ : syracuseStep 12257725 = 4596647) B4596647
theorem B3631591 : Blo 1192413 3631591 := bstep (se 1 (by rfl) ⟨2723693, by rfl⟩ : syracuseStep 3631591 = 5447387) B5447387
theorem B10193471 : Blo 1192413 10193471 := bstep (se 1 (by rfl) ⟨7645103, by rfl⟩ : syracuseStep 10193471 = 15290207) B15290207
theorem B6040169 : Blo 1192413 6040169 := bstep (se 2 (by rfl) ⟨2265063, by rfl⟩ : syracuseStep 6040169 = 4530127) B4530127
theorem B1788635 : Blo 1192413 1788635 := bstep (se 1 (by rfl) ⟨1341476, by rfl⟩ : syracuseStep 1788635 = 2682953) B2682953
theorem B1788671 : Blo 1192413 1788671 := bstep (se 1 (by rfl) ⟨1341503, by rfl⟩ : syracuseStep 1788671 = 2683007) B2683007
theorem B3820297 : Blo 1192413 3820297 := bstep (se 2 (by rfl) ⟨1432611, by rfl⟩ : syracuseStep 3820297 = 2865223) B2865223
theorem B12241961 : Blo 1192413 12241961 := bstep (se 2 (by rfl) ⟨4590735, by rfl⟩ : syracuseStep 12241961 = 9181471) B9181471
theorem B4533529 : Blo 1192413 4533529 := bstep (se 2 (by rfl) ⟨1700073, by rfl⟩ : syracuseStep 4533529 = 3400147) B3400147
theorem B1789391 : Blo 1192413 1789391 := bstep (se 1 (by rfl) ⟨1342043, by rfl⟩ : syracuseStep 1789391 = 2684087) B2684087
theorem B1789481 : Blo 1192413 1789481 := bstep (se 2 (by rfl) ⟨671055, by rfl⟩ : syracuseStep 1789481 = 1342111) B1342111
theorem B3018343 : Blo 1192413 3018343 := bstep (se 1 (by rfl) ⟨2263757, by rfl⟩ : syracuseStep 3018343 = 4527515) B4527515
theorem B13594391 : Blo 1192413 13594391 := bstep (se 1 (by rfl) ⟨10195793, by rfl⟩ : syracuseStep 13594391 = 20391587) B20391587
theorem B1789775 : Blo 1192413 1789775 := bstep (se 1 (by rfl) ⟨1342331, by rfl⟩ : syracuseStep 1789775 = 2684663) B2684663
theorem B4026239 : Blo 1192413 4026239 := bstep (se 1 (by rfl) ⟨3019679, by rfl⟩ : syracuseStep 4026239 = 6039359) B6039359
theorem B97955729 : Blo 1192413 97955729 := bstep (se 2 (by rfl) ⟨36733398, by rfl⟩ : syracuseStep 97955729 = 73466797) B73466797
theorem B1789895 : Blo 1192413 1789895 := bstep (se 1 (by rfl) ⟨1342421, by rfl⟩ : syracuseStep 1789895 = 2684843) B2684843
theorem B7254035 : Blo 1192413 7254035 := bstep (se 1 (by rfl) ⟨5440526, by rfl⟩ : syracuseStep 7254035 = 10881053) B10881053
theorem B1789979 : Blo 1192413 1789979 := bstep (se 1 (by rfl) ⟨1342484, by rfl⟩ : syracuseStep 1789979 = 2684969) B2684969
theorem B4026401 : Blo 1192413 4026401 := bstep (se 2 (by rfl) ⟨1509900, by rfl⟩ : syracuseStep 4026401 = 3019801) B3019801
theorem B2682935 : Blo 1192413 2682935 := bstep (se 1 (by rfl) ⟨2012201, by rfl⟩ : syracuseStep 2682935 = 4024403) B4024403
theorem B40308931 : Blo 1192413 40308931 := bstep (se 1 (by rfl) ⟨30231698, by rfl⟩ : syracuseStep 40308931 = 60463397) B60463397
theorem B3018971 : Blo 1192413 3018971 := bstep (se 1 (by rfl) ⟨2264228, by rfl⟩ : syracuseStep 3018971 = 4528457) B4528457
theorem B2265383 : Blo 1192413 2265383 := bstep (se 1 (by rfl) ⟨1699037, by rfl⟩ : syracuseStep 2265383 = 3398075) B3398075
theorem B1790255 : Blo 1192413 1790255 := bstep (se 1 (by rfl) ⟨1342691, by rfl⟩ : syracuseStep 1790255 = 2685383) B2685383
theorem B13603139 : Blo 1192413 13603139 := bstep (se 1 (by rfl) ⟨10202354, by rfl⟩ : syracuseStep 13603139 = 20404709) B20404709
theorem B1790363 : Blo 1192413 1790363 := bstep (se 1 (by rfl) ⟨1342772, by rfl⟩ : syracuseStep 1790363 = 2685545) B2685545
theorem B4084157 : Blo 1192413 4084157 := bstep (se 3 (by rfl) ⟨765779, by rfl⟩ : syracuseStep 4084157 = 1531559) B1531559
theorem B1790399 : Blo 1192413 1790399 := bstep (se 1 (by rfl) ⟨1342799, by rfl⟩ : syracuseStep 1790399 = 2685599) B2685599
theorem B1192475 : Blo 1192413 1192475 := bstep (se 1 (by rfl) ⟨894356, by rfl⟩ : syracuseStep 1192475 = 1788713) B1788713
theorem B3396127 : Blo 1192413 3396127 := bstep (se 1 (by rfl) ⟨2547095, by rfl⟩ : syracuseStep 3396127 = 5094191) B5094191
theorem B1790495 : Blo 1192413 1790495 := bstep (se 1 (by rfl) ⟨1342871, by rfl⟩ : syracuseStep 1790495 = 2685743) B2685743
theorem B1192615 : Blo 1192413 1192615 := bstep (se 1 (by rfl) ⟨894461, by rfl⟩ : syracuseStep 1192615 = 1788923) B1788923
theorem B1192655 : Blo 1192413 1192655 := bstep (se 1 (by rfl) ⟨894491, by rfl⟩ : syracuseStep 1192655 = 1788983) B1788983
theorem B1192735 : Blo 1192413 1192735 := bstep (se 1 (by rfl) ⟨894551, by rfl⟩ : syracuseStep 1192735 = 1789103) B1789103
theorem B1790783 : Blo 1192413 1790783 := bstep (se 1 (by rfl) ⟨1343087, by rfl⟩ : syracuseStep 1790783 = 2686175) B2686175
theorem B1790927 : Blo 1192413 1790927 := bstep (se 1 (by rfl) ⟨1343195, by rfl⟩ : syracuseStep 1790927 = 2686391) B2686391
theorem B10884077 : Blo 1192413 10884077 := bstep (se 3 (by rfl) ⟨2040764, by rfl⟩ : syracuseStep 10884077 = 4081529) B4081529
theorem B1791017 : Blo 1192413 1791017 := bstep (se 2 (by rfl) ⟨671631, by rfl⟩ : syracuseStep 1791017 = 1343263) B1343263
theorem B1791047 : Blo 1192413 1791047 := bstep (se 1 (by rfl) ⟨1343285, by rfl⟩ : syracuseStep 1791047 = 2686571) B2686571
theorem B4027643 : Blo 1192413 4027643 := bstep (se 1 (by rfl) ⟨3020732, by rfl⟩ : syracuseStep 4027643 = 6041465) B6041465
theorem B1791227 : Blo 1192413 1791227 := bstep (se 1 (by rfl) ⟨1343420, by rfl⟩ : syracuseStep 1791227 = 2686841) B2686841
theorem B1193215 : Blo 1192413 1193215 := bstep (se 1 (by rfl) ⟨894911, by rfl⟩ : syracuseStep 1193215 = 1789823) B1789823
theorem B79508789 : Blo 1192413 79508789 := bstep (se 5 (by rfl) ⟨3726974, by rfl⟩ : syracuseStep 79508789 = 7453949) B7453949
theorem B1791287 : Blo 1192413 1791287 := bstep (se 1 (by rfl) ⟨1343465, by rfl⟩ : syracuseStep 1791287 = 2686931) B2686931
theorem B27571553 : Blo 1192413 27571553 := bstep (se 2 (by rfl) ⟨10339332, by rfl⟩ : syracuseStep 27571553 = 20678665) B20678665
theorem B1193343 : Blo 1192413 1193343 := bstep (se 1 (by rfl) ⟨895007, by rfl⟩ : syracuseStep 1193343 = 1790015) B1790015
theorem B19355041 : Blo 1192413 19355041 := bstep (se 2 (by rfl) ⟨7258140, by rfl⟩ : syracuseStep 19355041 = 14516281) B14516281
theorem B1193499 : Blo 1192413 1193499 := bstep (se 1 (by rfl) ⟨895124, by rfl⟩ : syracuseStep 1193499 = 1790249) B1790249
theorem B1791593 : Blo 1192413 1791593 := bstep (se 2 (by rfl) ⟨671847, by rfl⟩ : syracuseStep 1791593 = 1343695) B1343695
theorem B6043247 : Blo 1192413 6043247 := bstep (se 1 (by rfl) ⟨4532435, by rfl⟩ : syracuseStep 6043247 = 9064871) B9064871
theorem B2152111 : Blo 1192413 2152111 := bstep (se 1 (by rfl) ⟨1614083, by rfl⟩ : syracuseStep 2152111 = 3228167) B3228167
theorem B1193679 : Blo 1192413 1193679 := bstep (se 1 (by rfl) ⟨895259, by rfl⟩ : syracuseStep 1193679 = 1790519) B1790519
theorem B2152175 : Blo 1192413 2152175 := bstep (se 1 (by rfl) ⟨1614131, by rfl⟩ : syracuseStep 2152175 = 3228263) B3228263
theorem B1193919 : Blo 1192413 1193919 := bstep (se 1 (by rfl) ⟨895439, by rfl⟩ : syracuseStep 1193919 = 1790879) B1790879
theorem B6535151 : Blo 1192413 6535151 := bstep (se 1 (by rfl) ⟨4901363, by rfl⟩ : syracuseStep 6535151 = 9802727) B9802727
theorem B27228149 : Blo 1192413 27228149 := bstep (se 5 (by rfl) ⟨1276319, by rfl⟩ : syracuseStep 27228149 = 2552639) B2552639
theorem B1194047 : Blo 1192413 1194047 := bstep (se 1 (by rfl) ⟨895535, by rfl⟩ : syracuseStep 1194047 = 1791071) B1791071
theorem B1194087 : Blo 1192413 1194087 := bstep (se 1 (by rfl) ⟨895565, by rfl⟩ : syracuseStep 1194087 = 1791131) B1791131
theorem B1341607 : Blo 1192413 1341607 := bstep (se 1 (by rfl) ⟨1006205, by rfl⟩ : syracuseStep 1341607 = 2012411) B2012411
theorem B9058553 : Blo 1192413 9058553 := bstep (se 2 (by rfl) ⟨3396957, by rfl⟩ : syracuseStep 9058553 = 6793915) B6793915
theorem B2685239 : Blo 1192413 2685239 := bstep (se 1 (by rfl) ⟨2013929, by rfl⟩ : syracuseStep 2685239 = 4027859) B4027859
theorem B2685419 : Blo 1192413 2685419 := bstep (se 1 (by rfl) ⟨2014064, by rfl⟩ : syracuseStep 2685419 = 4028129) B4028129
theorem B3021563 : Blo 1192413 3021563 := bstep (se 1 (by rfl) ⟨2266172, by rfl⟩ : syracuseStep 3021563 = 4532345) B4532345
theorem B7748951 : Blo 1192413 7748951 := bstep (se 1 (by rfl) ⟨5811713, by rfl⟩ : syracuseStep 7748951 = 11623427) B11623427
theorem B2866607 : Blo 1192413 2866607 := bstep (se 1 (by rfl) ⟨2149955, by rfl⟩ : syracuseStep 2866607 = 4299911) B4299911
theorem B6036929 : Blo 1192413 6036929 := bstep (se 2 (by rfl) ⟨2263848, by rfl⟩ : syracuseStep 6036929 = 4527697) B4527697
theorem B6798815 : Blo 1192413 6798815 := bstep (se 1 (by rfl) ⟨5099111, by rfl⟩ : syracuseStep 6798815 = 10198223) B10198223
theorem B4030073 : Blo 1192413 4030073 := bstep (se 2 (by rfl) ⟨1511277, by rfl⟩ : syracuseStep 4030073 = 3022555) B3022555
theorem B2686751 : Blo 1192413 2686751 := bstep (se 1 (by rfl) ⟨2015063, by rfl⟩ : syracuseStep 2686751 = 4030127) B4030127
theorem B1613695 : Blo 1192413 1613695 := bstep (se 1 (by rfl) ⟨1210271, by rfl⟩ : syracuseStep 1613695 = 2420543) B2420543
theorem B4030451 : Blo 1192413 4030451 := bstep (se 1 (by rfl) ⟨3022838, by rfl⟩ : syracuseStep 4030451 = 6045677) B6045677
theorem B9068759 : Blo 1192413 9068759 := bstep (se 1 (by rfl) ⟨6801569, by rfl⟩ : syracuseStep 9068759 = 13603139) B13603139
theorem B19890515 : Blo 1192413 19890515 := bstep (se 1 (by rfl) ⟨14917886, by rfl⟩ : syracuseStep 19890515 = 29835773) B29835773
theorem B2687327 : Blo 1192413 2687327 := bstep (se 1 (by rfl) ⟨2015495, by rfl⟩ : syracuseStep 2687327 = 4030991) B4030991
theorem B5095847 : Blo 1192413 5095847 := bstep (se 1 (by rfl) ⟨3821885, by rfl⟩ : syracuseStep 5095847 = 7643771) B7643771
theorem B2548265 : Blo 1192413 2548265 := bstep (se 2 (by rfl) ⟨955599, by rfl⟩ : syracuseStep 2548265 = 1911199) B1911199
theorem B41927219 : Blo 1192413 41927219 := bstep (se 1 (by rfl) ⟨31445414, by rfl⟩ : syracuseStep 41927219 = 62890829) B62890829
theorem B16343633 : Blo 1192413 16343633 := bstep (se 2 (by rfl) ⟨6128862, by rfl⟩ : syracuseStep 16343633 = 12257725) B12257725
theorem B4842121 : Blo 1192413 4842121 := bstep (se 2 (by rfl) ⟨1815795, by rfl⟩ : syracuseStep 4842121 = 3631591) B3631591
theorem B10880207 : Blo 1192413 10880207 := bstep (se 1 (by rfl) ⟨8160155, by rfl⟩ : syracuseStep 10880207 = 16320311) B16320311
theorem B16319873 : Blo 1192413 16319873 := bstep (se 2 (by rfl) ⟨6119952, by rfl⟩ : syracuseStep 16319873 = 12239905) B12239905
theorem B6039035 : Blo 1192413 6039035 := bstep (se 1 (by rfl) ⟨4529276, by rfl⟩ : syracuseStep 6039035 = 9058553) B9058553
theorem B25806721 : Blo 1192413 25806721 := bstep (se 2 (by rfl) ⟨9677520, by rfl⟩ : syracuseStep 25806721 = 19355041) B19355041
theorem B2686967 : Blo 1192413 2686967 := bstep (se 1 (by rfl) ⟨2015225, by rfl⟩ : syracuseStep 2686967 = 4030451) B4030451
theorem B8161307 : Blo 1192413 8161307 := bstep (se 1 (by rfl) ⟨6120980, by rfl⟩ : syracuseStep 8161307 = 12241961) B12241961
theorem B4024457 : Blo 1192413 4024457 := bstep (se 2 (by rfl) ⟨1509171, by rfl⟩ : syracuseStep 4024457 = 3018343) B3018343
theorem B2869481 : Blo 1192413 2869481 := bstep (se 2 (by rfl) ⟨1076055, by rfl⟩ : syracuseStep 2869481 = 2152111) B2152111
theorem B1911071 : Blo 1192413 1911071 := bstep (se 1 (by rfl) ⟨1433303, by rfl⟩ : syracuseStep 1911071 = 2866607) B2866607
theorem B4024619 : Blo 1192413 4024619 := bstep (se 1 (by rfl) ⟨3018464, by rfl⟩ : syracuseStep 4024619 = 6036929) B6036929
theorem B4532543 : Blo 1192413 4532543 := bstep (se 1 (by rfl) ⟨3399407, by rfl⟩ : syracuseStep 4532543 = 6798815) B6798815
theorem B9062927 : Blo 1192413 9062927 := bstep (se 1 (by rfl) ⟨6797195, by rfl⟩ : syracuseStep 9062927 = 13594391) B13594391
theorem B4836023 : Blo 1192413 4836023 := bstep (se 1 (by rfl) ⟨3627017, by rfl⟩ : syracuseStep 4836023 = 7254035) B7254035
theorem B1788623 : Blo 1192413 1788623 := bstep (se 1 (by rfl) ⟨1341467, by rfl⟩ : syracuseStep 1788623 = 2682935) B2682935
theorem B6449951 : Blo 1192413 6449951 := bstep (se 1 (by rfl) ⟨4837463, by rfl⟩ : syracuseStep 6449951 = 9674927) B9674927
theorem B1510255 : Blo 1192413 1510255 := bstep (se 1 (by rfl) ⟨1132691, by rfl⟩ : syracuseStep 1510255 = 2265383) B2265383
theorem B1788809 : Blo 1192413 1788809 := bstep (se 2 (by rfl) ⟨670803, by rfl⟩ : syracuseStep 1788809 = 1341607) B1341607
theorem B10193849 : Blo 1192413 10193849 := bstep (se 2 (by rfl) ⟨3822693, by rfl⟩ : syracuseStep 10193849 = 7645387) B7645387
theorem B2722771 : Blo 1192413 2722771 := bstep (se 1 (by rfl) ⟨2042078, by rfl⟩ : syracuseStep 2722771 = 4084157) B4084157
theorem B10202219 : Blo 1192413 10202219 := bstep (se 1 (by rfl) ⟨7651664, by rfl⟩ : syracuseStep 10202219 = 15303329) B15303329
theorem B1699231 : Blo 1192413 1699231 := bstep (se 1 (by rfl) ⟨1274423, by rfl⟩ : syracuseStep 1699231 = 2548847) B2548847
theorem B53005859 : Blo 1192413 53005859 := bstep (se 1 (by rfl) ⟨39754394, by rfl⟩ : syracuseStep 53005859 = 79508789) B79508789
theorem B20663869 : Blo 1192413 20663869 := bstep (se 3 (by rfl) ⟨3874475, by rfl⟩ : syracuseStep 20663869 = 7748951) B7748951
theorem B1699823 : Blo 1192413 1699823 := bstep (se 1 (by rfl) ⟨1274867, by rfl⟩ : syracuseStep 1699823 = 2549735) B2549735
theorem B1699903 : Blo 1192413 1699903 := bstep (se 1 (by rfl) ⟨1274927, by rfl⟩ : syracuseStep 1699903 = 2549855) B2549855
theorem B1790159 : Blo 1192413 1790159 := bstep (se 1 (by rfl) ⟨1342619, by rfl⟩ : syracuseStep 1790159 = 2685239) B2685239
theorem B1790279 : Blo 1192413 1790279 := bstep (se 1 (by rfl) ⟨1342709, by rfl⟩ : syracuseStep 1790279 = 2685419) B2685419
theorem B6795647 : Blo 1192413 6795647 := bstep (se 1 (by rfl) ⟨5096735, by rfl⟩ : syracuseStep 6795647 = 10193471) B10193471
theorem B4026779 : Blo 1192413 4026779 := bstep (se 1 (by rfl) ⟨3020084, by rfl⟩ : syracuseStep 4026779 = 6040169) B6040169
theorem B1192423 : Blo 1192413 1192423 := bstep (se 1 (by rfl) ⟨894317, by rfl⟩ : syracuseStep 1192423 = 1788635) B1788635
theorem B1192447 : Blo 1192413 1192447 := bstep (se 1 (by rfl) ⟨894335, by rfl⟩ : syracuseStep 1192447 = 1788671) B1788671
theorem B5739133 : Blo 1192413 5739133 := bstep (se 3 (by rfl) ⟨1076087, by rfl⟩ : syracuseStep 5739133 = 2152175) B2152175
theorem B1192927 : Blo 1192413 1192927 := bstep (se 1 (by rfl) ⟨894695, by rfl⟩ : syracuseStep 1192927 = 1789391) B1789391
theorem B1192987 : Blo 1192413 1192987 := bstep (se 1 (by rfl) ⟨894740, by rfl⟩ : syracuseStep 1192987 = 1789481) B1789481
theorem B2151593 : Blo 1192413 2151593 := bstep (se 2 (by rfl) ⟨806847, by rfl⟩ : syracuseStep 2151593 = 1613695) B1613695
theorem B1791167 : Blo 1192413 1791167 := bstep (se 1 (by rfl) ⟨1343375, by rfl⟩ : syracuseStep 1791167 = 2686751) B2686751
theorem B1193183 : Blo 1192413 1193183 := bstep (se 1 (by rfl) ⟨894887, by rfl⟩ : syracuseStep 1193183 = 1789775) B1789775
theorem B2684159 : Blo 1192413 2684159 := bstep (se 1 (by rfl) ⟨2013119, by rfl⟩ : syracuseStep 2684159 = 4026239) B4026239
theorem B65303819 : Blo 1192413 65303819 := bstep (se 1 (by rfl) ⟨48977864, by rfl⟩ : syracuseStep 65303819 = 97955729) B97955729
theorem B1193263 : Blo 1192413 1193263 := bstep (se 1 (by rfl) ⟨894947, by rfl⟩ : syracuseStep 1193263 = 1789895) B1789895
theorem B1193319 : Blo 1192413 1193319 := bstep (se 1 (by rfl) ⟨894989, by rfl⟩ : syracuseStep 1193319 = 1789979) B1789979
theorem B2684267 : Blo 1192413 2684267 := bstep (se 1 (by rfl) ⟨2013200, by rfl⟩ : syracuseStep 2684267 = 4026401) B4026401
theorem B2012647 : Blo 1192413 2012647 := bstep (se 1 (by rfl) ⟨1509485, by rfl⟩ : syracuseStep 2012647 = 3018971) B3018971
theorem B3626495 : Blo 1192413 3626495 := bstep (se 1 (by rfl) ⟨2719871, by rfl⟩ : syracuseStep 3626495 = 5439743) B5439743
theorem B1193503 : Blo 1192413 1193503 := bstep (se 1 (by rfl) ⟨895127, by rfl⟩ : syracuseStep 1193503 = 1790255) B1790255
theorem B6723131 : Blo 1192413 6723131 := bstep (se 1 (by rfl) ⟨5042348, by rfl⟩ : syracuseStep 6723131 = 10084697) B10084697
theorem B53745241 : Blo 1192413 53745241 := bstep (se 2 (by rfl) ⟨20154465, by rfl⟩ : syracuseStep 53745241 = 40308931) B40308931
theorem B1193575 : Blo 1192413 1193575 := bstep (se 1 (by rfl) ⟨895181, by rfl⟩ : syracuseStep 1193575 = 1790363) B1790363
theorem B1193599 : Blo 1192413 1193599 := bstep (se 1 (by rfl) ⟨895199, by rfl⟩ : syracuseStep 1193599 = 1790399) B1790399
theorem B2012809 : Blo 1192413 2012809 := bstep (se 2 (by rfl) ⟨754803, by rfl⟩ : syracuseStep 2012809 = 1509607) B1509607
theorem B1193663 : Blo 1192413 1193663 := bstep (se 1 (by rfl) ⟨895247, by rfl⟩ : syracuseStep 1193663 = 1790495) B1790495
theorem B1193855 : Blo 1192413 1193855 := bstep (se 1 (by rfl) ⟨895391, by rfl⟩ : syracuseStep 1193855 = 1790783) B1790783
theorem B1193951 : Blo 1192413 1193951 := bstep (se 1 (by rfl) ⟨895463, by rfl⟩ : syracuseStep 1193951 = 1790927) B1790927
theorem B7256051 : Blo 1192413 7256051 := bstep (se 1 (by rfl) ⟨5442038, by rfl⟩ : syracuseStep 7256051 = 10884077) B10884077
theorem B1194011 : Blo 1192413 1194011 := bstep (se 1 (by rfl) ⟨895508, by rfl⟩ : syracuseStep 1194011 = 1791017) B1791017
theorem B4528169 : Blo 1192413 4528169 := bstep (se 2 (by rfl) ⟨1698063, by rfl⟩ : syracuseStep 4528169 = 3396127) B3396127
theorem B1194031 : Blo 1192413 1194031 := bstep (se 1 (by rfl) ⟨895523, by rfl⟩ : syracuseStep 1194031 = 1791047) B1791047
theorem B4085801 : Blo 1192413 4085801 := bstep (se 2 (by rfl) ⟨1532175, by rfl⟩ : syracuseStep 4085801 = 3064351) B3064351
theorem B2685095 : Blo 1192413 2685095 := bstep (se 1 (by rfl) ⟨2013821, by rfl⟩ : syracuseStep 2685095 = 4027643) B4027643
theorem B1194151 : Blo 1192413 1194151 := bstep (se 1 (by rfl) ⟨895613, by rfl⟩ : syracuseStep 1194151 = 1791227) B1791227
theorem B1194191 : Blo 1192413 1194191 := bstep (se 1 (by rfl) ⟨895643, by rfl⟩ : syracuseStep 1194191 = 1791287) B1791287
theorem B18381035 : Blo 1192413 18381035 := bstep (se 1 (by rfl) ⟨13785776, by rfl⟩ : syracuseStep 18381035 = 27571553) B27571553
theorem B5093729 : Blo 1192413 5093729 := bstep (se 2 (by rfl) ⟨1910148, by rfl⟩ : syracuseStep 5093729 = 3820297) B3820297
theorem B1194395 : Blo 1192413 1194395 := bstep (se 1 (by rfl) ⟨895796, by rfl⟩ : syracuseStep 1194395 = 1791593) B1791593
theorem B4028831 : Blo 1192413 4028831 := bstep (se 1 (by rfl) ⟨3021623, by rfl⟩ : syracuseStep 4028831 = 6043247) B6043247
theorem B4356767 : Blo 1192413 4356767 := bstep (se 1 (by rfl) ⟨3267575, by rfl⟩ : syracuseStep 4356767 = 6535151) B6535151
theorem B18152099 : Blo 1192413 18152099 := bstep (se 1 (by rfl) ⟨13614074, by rfl⟩ : syracuseStep 18152099 = 27228149) B27228149
theorem B6044705 : Blo 1192413 6044705 := bstep (se 2 (by rfl) ⟨2266764, by rfl⟩ : syracuseStep 6044705 = 4533529) B4533529
theorem B2014375 : Blo 1192413 2014375 := bstep (se 1 (by rfl) ⟨1510781, by rfl⟩ : syracuseStep 2014375 = 3021563) B3021563
theorem B14507525 : Blo 1192413 14507525 := bstep (se 4 (by rfl) ⟨1360080, by rfl⟩ : syracuseStep 14507525 = 2720161) B2720161
theorem B2686715 : Blo 1192413 2686715 := bstep (se 1 (by rfl) ⟨2015036, by rfl⟩ : syracuseStep 2686715 = 4030073) B4030073
theorem B6045839 : Blo 1192413 6045839 := bstep (se 1 (by rfl) ⟨4534379, by rfl⟩ : syracuseStep 6045839 = 9068759) B9068759
theorem B4530431 : Blo 1192413 4530431 := bstep (se 1 (by rfl) ⟨3397823, by rfl⟩ : syracuseStep 4530431 = 6795647) B6795647
theorem B27951479 : Blo 1192413 27951479 := bstep (se 1 (by rfl) ⟨20963609, by rfl⟩ : syracuseStep 27951479 = 41927219) B41927219
theorem B10895755 : Blo 1192413 10895755 := bstep (se 1 (by rfl) ⟨8171816, by rfl⟩ : syracuseStep 10895755 = 16343633) B16343633
theorem B5096189 : Blo 1192413 5096189 := bstep (se 3 (by rfl) ⟨955535, by rfl⟩ : syracuseStep 5096189 = 1911071) B1911071
theorem B1434395 : Blo 1192413 1434395 := bstep (se 1 (by rfl) ⟨1075796, by rfl⟩ : syracuseStep 1434395 = 2151593) B2151593
theorem B7652177 : Blo 1192413 7652177 := bstep (se 2 (by rfl) ⟨2869566, by rfl⟩ : syracuseStep 7652177 = 5739133) B5739133
theorem B6456161 : Blo 1192413 6456161 := bstep (se 2 (by rfl) ⟨2421060, by rfl⟩ : syracuseStep 6456161 = 4842121) B4842121
theorem B10879915 : Blo 1192413 10879915 := bstep (se 1 (by rfl) ⟨8159936, by rfl⟩ : syracuseStep 10879915 = 16319873) B16319873
theorem B2417663 : Blo 1192413 2417663 := bstep (se 1 (by rfl) ⟨1813247, by rfl⟩ : syracuseStep 2417663 = 3626495) B3626495
theorem B3630361 : Blo 1192413 3630361 := bstep (se 2 (by rfl) ⟨1361385, by rfl⟩ : syracuseStep 3630361 = 2722771) B2722771
theorem B5440871 : Blo 1192413 5440871 := bstep (se 1 (by rfl) ⟨4080653, by rfl⟩ : syracuseStep 5440871 = 8161307) B8161307
theorem B12101399 : Blo 1192413 12101399 := bstep (se 1 (by rfl) ⟨9076049, by rfl⟩ : syracuseStep 12101399 = 18152099) B18152099
theorem B6801479 : Blo 1192413 6801479 := bstep (se 1 (by rfl) ⟨5101109, by rfl⟩ : syracuseStep 6801479 = 10202219) B10202219
theorem B27551825 : Blo 1192413 27551825 := bstep (se 2 (by rfl) ⟨10331934, by rfl⟩ : syracuseStep 27551825 = 20663869) B20663869
theorem B34408961 : Blo 1192413 34408961 := bstep (se 2 (by rfl) ⟨12903360, by rfl⟩ : syracuseStep 34408961 = 25806721) B25806721
theorem B4532861 : Blo 1192413 4532861 := bstep (se 3 (by rfl) ⟨849911, by rfl⟩ : syracuseStep 4532861 = 1699823) B1699823
theorem B7253471 : Blo 1192413 7253471 := bstep (se 1 (by rfl) ⟨5440103, by rfl⟩ : syracuseStep 7253471 = 10880207) B10880207
theorem B1789439 : Blo 1192413 1789439 := bstep (se 1 (by rfl) ⟨1342079, by rfl⟩ : syracuseStep 1789439 = 2684159) B2684159
theorem B43535879 : Blo 1192413 43535879 := bstep (se 1 (by rfl) ⟨32651909, by rfl⟩ : syracuseStep 43535879 = 65303819) B65303819
theorem B1789511 : Blo 1192413 1789511 := bstep (se 1 (by rfl) ⟨1342133, by rfl⟩ : syracuseStep 1789511 = 2684267) B2684267
theorem B4026023 : Blo 1192413 4026023 := bstep (se 1 (by rfl) ⟨3019517, by rfl⟩ : syracuseStep 4026023 = 6039035) B6039035
theorem B4837367 : Blo 1192413 4837367 := bstep (se 1 (by rfl) ⟨3628025, by rfl⟩ : syracuseStep 4837367 = 7256051) B7256051
theorem B38686733 : Blo 1192413 38686733 := bstep (se 3 (by rfl) ⟨7253762, by rfl⟩ : syracuseStep 38686733 = 14507525) B14507525
theorem B3018779 : Blo 1192413 3018779 := bstep (se 1 (by rfl) ⟨2264084, by rfl⟩ : syracuseStep 3018779 = 4528169) B4528169
theorem B2723867 : Blo 1192413 2723867 := bstep (se 1 (by rfl) ⟨2042900, by rfl⟩ : syracuseStep 2723867 = 4085801) B4085801
theorem B2682971 : Blo 1192413 2682971 := bstep (se 1 (by rfl) ⟨2012228, by rfl⟩ : syracuseStep 2682971 = 4024457) B4024457
theorem B6795373 : Blo 1192413 6795373 := bstep (se 3 (by rfl) ⟨1274132, by rfl⟩ : syracuseStep 6795373 = 2548265) B2548265
theorem B1790063 : Blo 1192413 1790063 := bstep (se 1 (by rfl) ⟨1342547, by rfl⟩ : syracuseStep 1790063 = 2685095) B2685095
theorem B1912987 : Blo 1192413 1912987 := bstep (se 1 (by rfl) ⟨1434740, by rfl⟩ : syracuseStep 1912987 = 2869481) B2869481
theorem B17928349 : Blo 1192413 17928349 := bstep (se 3 (by rfl) ⟨3361565, by rfl⟩ : syracuseStep 17928349 = 6723131) B6723131
theorem B2683079 : Blo 1192413 2683079 := bstep (se 1 (by rfl) ⟨2012309, by rfl⟩ : syracuseStep 2683079 = 4024619) B4024619
theorem B3395819 : Blo 1192413 3395819 := bstep (se 1 (by rfl) ⟨2546864, by rfl⟩ : syracuseStep 3395819 = 5093729) B5093729
theorem B6041951 : Blo 1192413 6041951 := bstep (se 1 (by rfl) ⟨4531463, by rfl⟩ : syracuseStep 6041951 = 9062927) B9062927
theorem B2904511 : Blo 1192413 2904511 := bstep (se 1 (by rfl) ⟨2178383, by rfl⟩ : syracuseStep 2904511 = 4356767) B4356767
theorem B3224015 : Blo 1192413 3224015 := bstep (se 1 (by rfl) ⟨2418011, by rfl⟩ : syracuseStep 3224015 = 4836023) B4836023
theorem B1192415 : Blo 1192413 1192415 := bstep (se 1 (by rfl) ⟨894311, by rfl⟩ : syracuseStep 1192415 = 1788623) B1788623
theorem B2265641 : Blo 1192413 2265641 := bstep (se 2 (by rfl) ⟨849615, by rfl⟩ : syracuseStep 2265641 = 1699231) B1699231
theorem B1192539 : Blo 1192413 1192539 := bstep (se 1 (by rfl) ⟨894404, by rfl⟩ : syracuseStep 1192539 = 1788809) B1788809
theorem B6795899 : Blo 1192413 6795899 := bstep (se 1 (by rfl) ⟨5096924, by rfl⟩ : syracuseStep 6795899 = 10193849) B10193849
theorem B2683529 : Blo 1192413 2683529 := bstep (se 2 (by rfl) ⟨1006323, by rfl⟩ : syracuseStep 2683529 = 2012647) B2012647
theorem B71660321 : Blo 1192413 71660321 := bstep (se 2 (by rfl) ⟨26872620, by rfl⟩ : syracuseStep 71660321 = 53745241) B53745241
theorem B2683745 : Blo 1192413 2683745 := bstep (se 2 (by rfl) ⟨1006404, by rfl⟩ : syracuseStep 2683745 = 2012809) B2012809
theorem B35337239 : Blo 1192413 35337239 := bstep (se 1 (by rfl) ⟨26502929, by rfl⟩ : syracuseStep 35337239 = 53005859) B53005859
theorem B1791143 : Blo 1192413 1791143 := bstep (se 1 (by rfl) ⟨1343357, by rfl⟩ : syracuseStep 1791143 = 2686715) B2686715
theorem B1791311 : Blo 1192413 1791311 := bstep (se 1 (by rfl) ⟨1343483, by rfl⟩ : syracuseStep 1791311 = 2686967) B2686967
theorem B2266537 : Blo 1192413 2266537 := bstep (se 2 (by rfl) ⟨849951, by rfl⟩ : syracuseStep 2266537 = 1699903) B1699903
theorem B1193439 : Blo 1192413 1193439 := bstep (se 1 (by rfl) ⟨895079, by rfl⟩ : syracuseStep 1193439 = 1790159) B1790159
theorem B1193519 : Blo 1192413 1193519 := bstep (se 1 (by rfl) ⟨895139, by rfl⟩ : syracuseStep 1193519 = 1790279) B1790279
theorem B13260343 : Blo 1192413 13260343 := bstep (se 1 (by rfl) ⟨9945257, by rfl⟩ : syracuseStep 13260343 = 19890515) B19890515
theorem B1791551 : Blo 1192413 1791551 := bstep (se 1 (by rfl) ⟨1343663, by rfl⟩ : syracuseStep 1791551 = 2687327) B2687327
theorem B2684519 : Blo 1192413 2684519 := bstep (se 1 (by rfl) ⟨2013389, by rfl⟩ : syracuseStep 2684519 = 4026779) B4026779
theorem B3397231 : Blo 1192413 3397231 := bstep (se 1 (by rfl) ⟨2547923, by rfl⟩ : syracuseStep 3397231 = 5095847) B5095847
theorem B1194111 : Blo 1192413 1194111 := bstep (se 1 (by rfl) ⟨895583, by rfl⟩ : syracuseStep 1194111 = 1791167) B1791167
theorem B2013673 : Blo 1192413 2013673 := bstep (se 2 (by rfl) ⟨755127, by rfl⟩ : syracuseStep 2013673 = 1510255) B1510255
theorem B12254023 : Blo 1192413 12254023 := bstep (se 1 (by rfl) ⟨9190517, by rfl⟩ : syracuseStep 12254023 = 18381035) B18381035
theorem B3021695 : Blo 1192413 3021695 := bstep (se 1 (by rfl) ⟨2266271, by rfl⟩ : syracuseStep 3021695 = 4532543) B4532543
theorem B2685833 : Blo 1192413 2685833 := bstep (se 2 (by rfl) ⟨1007187, by rfl⟩ : syracuseStep 2685833 = 2014375) B2014375
theorem B2685887 : Blo 1192413 2685887 := bstep (se 1 (by rfl) ⟨2014415, by rfl⟩ : syracuseStep 2685887 = 4028831) B4028831
theorem B4299967 : Blo 1192413 4299967 := bstep (se 1 (by rfl) ⟨3224975, by rfl⟩ : syracuseStep 4299967 = 6449951) B6449951
theorem B4029803 : Blo 1192413 4029803 := bstep (se 1 (by rfl) ⟨3022352, by rfl⟩ : syracuseStep 4029803 = 6044705) B6044705
theorem B4030559 : Blo 1192413 4030559 := bstep (se 1 (by rfl) ⟨3022919, by rfl⟩ : syracuseStep 4030559 = 6045839) B6045839
theorem B9060497 : Blo 1192413 9060497 := bstep (se 2 (by rfl) ⟨3397686, by rfl⟩ : syracuseStep 9060497 = 6795373) B6795373
theorem B4530599 : Blo 1192413 4530599 := bstep (se 1 (by rfl) ⟨3397949, by rfl⟩ : syracuseStep 4530599 = 6795899) B6795899
theorem B18367883 : Blo 1192413 18367883 := bstep (se 1 (by rfl) ⟨13775912, by rfl⟩ : syracuseStep 18367883 = 27551825) B27551825
theorem B22939307 : Blo 1192413 22939307 := bstep (se 1 (by rfl) ⟨17204480, by rfl⟩ : syracuseStep 22939307 = 34408961) B34408961
theorem B17680457 : Blo 1192413 17680457 := bstep (se 2 (by rfl) ⟨6630171, by rfl⟩ : syracuseStep 17680457 = 13260343) B13260343
theorem B1815911 : Blo 1192413 1815911 := bstep (se 1 (by rfl) ⟨1361933, by rfl⟩ : syracuseStep 1815911 = 2723867) B2723867
theorem B4835647 : Blo 1192413 4835647 := bstep (se 1 (by rfl) ⟨3626735, by rfl⟩ : syracuseStep 4835647 = 7253471) B7253471
theorem B25791155 : Blo 1192413 25791155 := bstep (se 1 (by rfl) ⟨19343366, by rfl⟩ : syracuseStep 25791155 = 38686733) B38686733
theorem B1788647 : Blo 1192413 1788647 := bstep (se 1 (by rfl) ⟨1341485, by rfl⟩ : syracuseStep 1788647 = 2682971) B2682971
theorem B1788719 : Blo 1192413 1788719 := bstep (se 1 (by rfl) ⟨1341539, by rfl⟩ : syracuseStep 1788719 = 2683079) B2683079
theorem B2263879 : Blo 1192413 2263879 := bstep (se 1 (by rfl) ⟨1697909, by rfl⟩ : syracuseStep 2263879 = 3395819) B3395819
theorem B2149343 : Blo 1192413 2149343 := bstep (se 1 (by rfl) ⟨1612007, by rfl⟩ : syracuseStep 2149343 = 3224015) B3224015
theorem B1510427 : Blo 1192413 1510427 := bstep (se 1 (by rfl) ⟨1132820, by rfl⟩ : syracuseStep 1510427 = 2265641) B2265641
theorem B1789019 : Blo 1192413 1789019 := bstep (se 1 (by rfl) ⟨1341764, by rfl⟩ : syracuseStep 1789019 = 2683529) B2683529
theorem B14527673 : Blo 1192413 14527673 := bstep (se 2 (by rfl) ⟨5447877, by rfl⟩ : syracuseStep 14527673 = 10895755) B10895755
theorem B1789163 : Blo 1192413 1789163 := bstep (se 1 (by rfl) ⟨1341872, by rfl⟩ : syracuseStep 1789163 = 2683745) B2683745
theorem B4304107 : Blo 1192413 4304107 := bstep (se 1 (by rfl) ⟨3228080, by rfl⟩ : syracuseStep 4304107 = 6456161) B6456161
theorem B382471445 : Blo 1192413 382471445 := bstep (se 6 (by rfl) ⟨8964174, by rfl⟩ : syracuseStep 382471445 = 17928349) B17928349
theorem B10202597 : Blo 1192413 10202597 := bstep (se 4 (by rfl) ⟨956493, by rfl⟩ : syracuseStep 10202597 = 1912987) B1912987
theorem B1789679 : Blo 1192413 1789679 := bstep (se 1 (by rfl) ⟨1342259, by rfl⟩ : syracuseStep 1789679 = 2684519) B2684519
theorem B4534319 : Blo 1192413 4534319 := bstep (se 1 (by rfl) ⟨3400739, by rfl⟩ : syracuseStep 4534319 = 6801479) B6801479
theorem B1790555 : Blo 1192413 1790555 := bstep (se 1 (by rfl) ⟨1342916, by rfl⟩ : syracuseStep 1790555 = 2685833) B2685833
theorem B1790591 : Blo 1192413 1790591 := bstep (se 1 (by rfl) ⟨1342943, by rfl⟩ : syracuseStep 1790591 = 2685887) B2685887
theorem B1192959 : Blo 1192413 1192959 := bstep (se 1 (by rfl) ⟨894719, by rfl⟩ : syracuseStep 1192959 = 1789439) B1789439
theorem B1193007 : Blo 1192413 1193007 := bstep (se 1 (by rfl) ⟨894755, by rfl⟩ : syracuseStep 1193007 = 1789511) B1789511
theorem B2684015 : Blo 1192413 2684015 := bstep (se 1 (by rfl) ⟨2013011, by rfl⟩ : syracuseStep 2684015 = 4026023) B4026023
theorem B12899645 : Blo 1192413 12899645 := bstep (se 3 (by rfl) ⟨2418683, by rfl⟩ : syracuseStep 12899645 = 4837367) B4837367
theorem B2012519 : Blo 1192413 2012519 := bstep (se 1 (by rfl) ⟨1509389, by rfl⟩ : syracuseStep 2012519 = 3018779) B3018779
theorem B1193375 : Blo 1192413 1193375 := bstep (se 1 (by rfl) ⟨895031, by rfl⟩ : syracuseStep 1193375 = 1790063) B1790063
theorem B3020287 : Blo 1192413 3020287 := bstep (se 1 (by rfl) ⟨2265215, by rfl⟩ : syracuseStep 3020287 = 4530431) B4530431
theorem B4027967 : Blo 1192413 4027967 := bstep (se 1 (by rfl) ⟨3020975, by rfl⟩ : syracuseStep 4027967 = 6041951) B6041951
theorem B18634319 : Blo 1192413 18634319 := bstep (se 1 (by rfl) ⟨13975739, by rfl⟩ : syracuseStep 18634319 = 27951479) B27951479
theorem B3397459 : Blo 1192413 3397459 := bstep (se 1 (by rfl) ⟨2548094, by rfl⟩ : syracuseStep 3397459 = 5096189) B5096189
theorem B47773547 : Blo 1192413 47773547 := bstep (se 1 (by rfl) ⟨35830160, by rfl⟩ : syracuseStep 47773547 = 71660321) B71660321
theorem B5101451 : Blo 1192413 5101451 := bstep (se 1 (by rfl) ⟨3826088, by rfl⟩ : syracuseStep 5101451 = 7652177) B7652177
theorem B3872681 : Blo 1192413 3872681 := bstep (se 2 (by rfl) ⟨1452255, by rfl⟩ : syracuseStep 3872681 = 2904511) B2904511
theorem B2684897 : Blo 1192413 2684897 := bstep (se 2 (by rfl) ⟨1006836, by rfl⟩ : syracuseStep 2684897 = 2013673) B2013673
theorem B1611775 : Blo 1192413 1611775 := bstep (se 1 (by rfl) ⟨1208831, by rfl⟩ : syracuseStep 1611775 = 2417663) B2417663
theorem B23558159 : Blo 1192413 23558159 := bstep (se 1 (by rfl) ⟨17668619, by rfl⟩ : syracuseStep 23558159 = 35337239) B35337239
theorem B1194095 : Blo 1192413 1194095 := bstep (se 1 (by rfl) ⟨895571, by rfl⟩ : syracuseStep 1194095 = 1791143) B1791143
theorem B1194207 : Blo 1192413 1194207 := bstep (se 1 (by rfl) ⟨895655, by rfl⟩ : syracuseStep 1194207 = 1791311) B1791311
theorem B3627247 : Blo 1192413 3627247 := bstep (se 1 (by rfl) ⟨2720435, by rfl⟩ : syracuseStep 3627247 = 5440871) B5440871
theorem B1194367 : Blo 1192413 1194367 := bstep (se 1 (by rfl) ⟨895775, by rfl⟩ : syracuseStep 1194367 = 1791551) B1791551
theorem B8067599 : Blo 1192413 8067599 := bstep (se 1 (by rfl) ⟨6050699, by rfl⟩ : syracuseStep 8067599 = 12101399) B12101399
theorem B14506553 : Blo 1192413 14506553 := bstep (se 2 (by rfl) ⟨5439957, by rfl⟩ : syracuseStep 14506553 = 10879915) B10879915
theorem B5733289 : Blo 1192413 5733289 := bstep (se 2 (by rfl) ⟨2149983, by rfl⟩ : syracuseStep 5733289 = 4299967) B4299967
theorem B4840481 : Blo 1192413 4840481 := bstep (se 2 (by rfl) ⟨1815180, by rfl⟩ : syracuseStep 4840481 = 3630361) B3630361
theorem B65354789 : Blo 1192413 65354789 := bstep (se 4 (by rfl) ⟨6127011, by rfl⟩ : syracuseStep 65354789 = 12254023) B12254023
theorem B3021907 : Blo 1192413 3021907 := bstep (se 1 (by rfl) ⟨2266430, by rfl⟩ : syracuseStep 3021907 = 4532861) B4532861
theorem B3022049 : Blo 1192413 3022049 := bstep (se 2 (by rfl) ⟨1133268, by rfl⟩ : syracuseStep 3022049 = 2266537) B2266537
theorem B2014463 : Blo 1192413 2014463 := bstep (se 1 (by rfl) ⟨1510847, by rfl⟩ : syracuseStep 2014463 = 3021695) B3021695
theorem B3825053 : Blo 1192413 3825053 := bstep (se 3 (by rfl) ⟨717197, by rfl⟩ : syracuseStep 3825053 = 1434395) B1434395
theorem B4529641 : Blo 1192413 4529641 := bstep (se 2 (by rfl) ⟨1698615, by rfl⟩ : syracuseStep 4529641 = 3397231) B3397231
theorem B2686535 : Blo 1192413 2686535 := bstep (se 1 (by rfl) ⟨2014901, by rfl⟩ : syracuseStep 2686535 = 4029803) B4029803
theorem B29023919 : Blo 1192413 29023919 := bstep (se 1 (by rfl) ⟨21767939, by rfl⟩ : syracuseStep 29023919 = 43535879) B43535879
theorem B3022879 : Blo 1192413 3022879 := bstep (se 1 (by rfl) ⟨2267159, by rfl⟩ : syracuseStep 3022879 = 4534319) B4534319
theorem B2687039 : Blo 1192413 2687039 := bstep (se 1 (by rfl) ⟨2015279, by rfl⟩ : syracuseStep 2687039 = 4030559) B4030559
theorem B6447529 : Blo 1192413 6447529 := bstep (se 2 (by rfl) ⟨2417823, by rfl⟩ : syracuseStep 6447529 = 4835647) B4835647
theorem B7644385 : Blo 1192413 7644385 := bstep (se 2 (by rfl) ⟨2866644, by rfl⟩ : syracuseStep 7644385 = 5733289) B5733289
theorem B3400967 : Blo 1192413 3400967 := bstep (se 1 (by rfl) ⟨2550725, by rfl⟩ : syracuseStep 3400967 = 5101451) B5101451
theorem B2581787 : Blo 1192413 2581787 := bstep (se 1 (by rfl) ⟨1936340, by rfl⟩ : syracuseStep 2581787 = 3872681) B3872681
theorem B6039521 : Blo 1192413 6039521 := bstep (se 2 (by rfl) ⟨2264820, by rfl⟩ : syracuseStep 6039521 = 4529641) B4529641
theorem B9685115 : Blo 1192413 9685115 := bstep (se 1 (by rfl) ⟨7263836, by rfl⟩ : syracuseStep 9685115 = 14527673) B14527673
theorem B2550035 : Blo 1192413 2550035 := bstep (se 1 (by rfl) ⟨1912526, by rfl⟩ : syracuseStep 2550035 = 3825053) B3825053
theorem B6801731 : Blo 1192413 6801731 := bstep (se 1 (by rfl) ⟨5101298, by rfl⟩ : syracuseStep 6801731 = 10202597) B10202597
theorem B2149033 : Blo 1192413 2149033 := bstep (se 2 (by rfl) ⟨805887, by rfl⟩ : syracuseStep 2149033 = 1611775) B1611775
theorem B6040331 : Blo 1192413 6040331 := bstep (se 1 (by rfl) ⟨4530248, by rfl⟩ : syracuseStep 6040331 = 9060497) B9060497
theorem B4836329 : Blo 1192413 4836329 := bstep (se 2 (by rfl) ⟨1813623, by rfl⟩ : syracuseStep 4836329 = 3627247) B3627247
theorem B1789343 : Blo 1192413 1789343 := bstep (se 1 (by rfl) ⟨1342007, by rfl⟩ : syracuseStep 1789343 = 2684015) B2684015
theorem B12422879 : Blo 1192413 12422879 := bstep (se 1 (by rfl) ⟨9317159, by rfl⟩ : syracuseStep 12422879 = 18634319) B18634319
theorem B3018505 : Blo 1192413 3018505 := bstep (se 2 (by rfl) ⟨1131939, by rfl⟩ : syracuseStep 3018505 = 2263879) B2263879
theorem B1789931 : Blo 1192413 1789931 := bstep (se 1 (by rfl) ⟨1342448, by rfl⟩ : syracuseStep 1789931 = 2684897) B2684897
theorem B5738809 : Blo 1192413 5738809 := bstep (se 2 (by rfl) ⟨2152053, by rfl⟩ : syracuseStep 5738809 = 4304107) B4304107
theorem B5378399 : Blo 1192413 5378399 := bstep (se 1 (by rfl) ⟨4033799, by rfl⟩ : syracuseStep 5378399 = 8067599) B8067599
theorem B9671035 : Blo 1192413 9671035 := bstep (se 1 (by rfl) ⟨7253276, by rfl⟩ : syracuseStep 9671035 = 14506553) B14506553
theorem B1192431 : Blo 1192413 1192431 := bstep (se 1 (by rfl) ⟨894323, by rfl⟩ : syracuseStep 1192431 = 1788647) B1788647
theorem B1192479 : Blo 1192413 1192479 := bstep (se 1 (by rfl) ⟨894359, by rfl⟩ : syracuseStep 1192479 = 1788719) B1788719
theorem B4027049 : Blo 1192413 4027049 := bstep (se 2 (by rfl) ⟨1510143, by rfl⟩ : syracuseStep 4027049 = 3020287) B3020287
theorem B43569859 : Blo 1192413 43569859 := bstep (se 1 (by rfl) ⟨32677394, by rfl⟩ : syracuseStep 43569859 = 65354789) B65354789
theorem B1192679 : Blo 1192413 1192679 := bstep (se 1 (by rfl) ⟨894509, by rfl⟩ : syracuseStep 1192679 = 1789019) B1789019
theorem B1192775 : Blo 1192413 1192775 := bstep (se 1 (by rfl) ⟨894581, by rfl⟩ : syracuseStep 1192775 = 1789163) B1789163
theorem B254980963 : Blo 1192413 254980963 := bstep (se 1 (by rfl) ⟨191235722, by rfl⟩ : syracuseStep 254980963 = 382471445) B382471445
theorem B1791023 : Blo 1192413 1791023 := bstep (se 1 (by rfl) ⟨1343267, by rfl⟩ : syracuseStep 1791023 = 2686535) B2686535
theorem B1193119 : Blo 1192413 1193119 := bstep (se 1 (by rfl) ⟨894839, by rfl⟩ : syracuseStep 1193119 = 1789679) B1789679
theorem B62821757 : Blo 1192413 62821757 := bstep (se 3 (by rfl) ⟨11779079, by rfl⟩ : syracuseStep 62821757 = 23558159) B23558159
theorem B4027805 : Blo 1192413 4027805 := bstep (se 3 (by rfl) ⟨755213, by rfl⟩ : syracuseStep 4027805 = 1510427) B1510427
theorem B3020399 : Blo 1192413 3020399 := bstep (se 1 (by rfl) ⟨2265299, by rfl⟩ : syracuseStep 3020399 = 4530599) B4530599
theorem B1193703 : Blo 1192413 1193703 := bstep (se 1 (by rfl) ⟨895277, by rfl⟩ : syracuseStep 1193703 = 1790555) B1790555
theorem B1193727 : Blo 1192413 1193727 := bstep (se 1 (by rfl) ⟨895295, by rfl⟩ : syracuseStep 1193727 = 1790591) B1790591
theorem B8599763 : Blo 1192413 8599763 := bstep (se 1 (by rfl) ⟨6449822, by rfl⟩ : syracuseStep 8599763 = 12899645) B12899645
theorem B1341679 : Blo 1192413 1341679 := bstep (se 1 (by rfl) ⟨1006259, by rfl⟩ : syracuseStep 1341679 = 2012519) B2012519
theorem B1210607 : Blo 1192413 1210607 := bstep (se 1 (by rfl) ⟨907955, by rfl⟩ : syracuseStep 1210607 = 1815911) B1815911
theorem B12245255 : Blo 1192413 12245255 := bstep (se 1 (by rfl) ⟨9183941, by rfl⟩ : syracuseStep 12245255 = 18367883) B18367883
theorem B2685311 : Blo 1192413 2685311 := bstep (se 1 (by rfl) ⟨2013983, by rfl⟩ : syracuseStep 2685311 = 4027967) B4027967
theorem B15292871 : Blo 1192413 15292871 := bstep (se 1 (by rfl) ⟨11469653, by rfl⟩ : syracuseStep 15292871 = 22939307) B22939307
theorem B31849031 : Blo 1192413 31849031 := bstep (se 1 (by rfl) ⟨23886773, by rfl⟩ : syracuseStep 31849031 = 47773547) B47773547
theorem B11786971 : Blo 1192413 11786971 := bstep (se 1 (by rfl) ⟨8840228, by rfl⟩ : syracuseStep 11786971 = 17680457) B17680457
theorem B4029209 : Blo 1192413 4029209 := bstep (se 2 (by rfl) ⟨1510953, by rfl⟩ : syracuseStep 4029209 = 3021907) B3021907
theorem B17194103 : Blo 1192413 17194103 := bstep (se 1 (by rfl) ⟨12895577, by rfl⟩ : syracuseStep 17194103 = 25791155) B25791155
theorem B1432895 : Blo 1192413 1432895 := bstep (se 1 (by rfl) ⟨1074671, by rfl⟩ : syracuseStep 1432895 = 2149343) B2149343
theorem B3226987 : Blo 1192413 3226987 := bstep (se 1 (by rfl) ⟨2420240, by rfl⟩ : syracuseStep 3226987 = 4840481) B4840481
theorem B2014699 : Blo 1192413 2014699 := bstep (se 1 (by rfl) ⟨1511024, by rfl⟩ : syracuseStep 2014699 = 3022049) B3022049
theorem B1342975 : Blo 1192413 1342975 := bstep (se 1 (by rfl) ⟨1007231, by rfl⟩ : syracuseStep 1342975 = 2014463) B2014463
theorem B4529945 : Blo 1192413 4529945 := bstep (se 2 (by rfl) ⟨1698729, by rfl⟩ : syracuseStep 4529945 = 3397459) B3397459
theorem B19349279 : Blo 1192413 19349279 := bstep (se 1 (by rfl) ⟨14511959, by rfl⟩ : syracuseStep 19349279 = 29023919) B29023919
theorem B4030505 : Blo 1192413 4030505 := bstep (se 2 (by rfl) ⟨1511439, by rfl⟩ : syracuseStep 4030505 = 3022879) B3022879
theorem B7651745 : Blo 1192413 7651745 := bstep (se 2 (by rfl) ⟨2869404, by rfl⟩ : syracuseStep 7651745 = 5738809) B5738809
theorem B12894713 : Blo 1192413 12894713 := bstep (se 2 (by rfl) ⟨4835517, by rfl⟩ : syracuseStep 12894713 = 9671035) B9671035
theorem B9069245 : Blo 1192413 9069245 := bstep (se 3 (by rfl) ⟨1700483, by rfl⟩ : syracuseStep 9069245 = 3400967) B3400967
theorem B1721191 : Blo 1192413 1721191 := bstep (se 1 (by rfl) ⟨1290893, by rfl⟩ : syracuseStep 1721191 = 2581787) B2581787
theorem B6456743 : Blo 1192413 6456743 := bstep (se 1 (by rfl) ⟨4842557, by rfl⟩ : syracuseStep 6456743 = 9685115) B9685115
theorem B10192513 : Blo 1192413 10192513 := bstep (se 2 (by rfl) ⟨3822192, by rfl⟩ : syracuseStep 10192513 = 7644385) B7644385
theorem B4302649 : Blo 1192413 4302649 := bstep (se 2 (by rfl) ⟨1613493, by rfl⟩ : syracuseStep 4302649 = 3226987) B3226987
theorem B11462735 : Blo 1192413 11462735 := bstep (se 1 (by rfl) ⟨8597051, by rfl⟩ : syracuseStep 11462735 = 17194103) B17194103
theorem B4024673 : Blo 1192413 4024673 := bstep (se 2 (by rfl) ⟨1509252, by rfl⟩ : syracuseStep 4024673 = 3018505) B3018505
theorem B12913141 : Blo 1192413 12913141 := bstep (se 5 (by rfl) ⟨605303, by rfl⟩ : syracuseStep 12913141 = 1210607) B1210607
theorem B1788905 : Blo 1192413 1788905 := bstep (se 2 (by rfl) ⟨670839, by rfl⟩ : syracuseStep 1788905 = 1341679) B1341679
theorem B8596705 : Blo 1192413 8596705 := bstep (se 2 (by rfl) ⟨3223764, by rfl⟩ : syracuseStep 8596705 = 6447529) B6447529
theorem B41881171 : Blo 1192413 41881171 := bstep (se 1 (by rfl) ⟨31410878, by rfl⟩ : syracuseStep 41881171 = 62821757) B62821757
theorem B58093145 : Blo 1192413 58093145 := bstep (se 2 (by rfl) ⟨21784929, by rfl⟩ : syracuseStep 58093145 = 43569859) B43569859
theorem B15715961 : Blo 1192413 15715961 := bstep (se 2 (by rfl) ⟨5893485, by rfl⟩ : syracuseStep 15715961 = 11786971) B11786971
theorem B4026347 : Blo 1192413 4026347 := bstep (se 1 (by rfl) ⟨3019760, by rfl⟩ : syracuseStep 4026347 = 6039521) B6039521
theorem B8163503 : Blo 1192413 8163503 := bstep (se 1 (by rfl) ⟨6122627, by rfl⟩ : syracuseStep 8163503 = 12245255) B12245255
theorem B1700023 : Blo 1192413 1700023 := bstep (se 1 (by rfl) ⟨1275017, by rfl⟩ : syracuseStep 1700023 = 2550035) B2550035
theorem B4534487 : Blo 1192413 4534487 := bstep (se 1 (by rfl) ⟨3400865, by rfl⟩ : syracuseStep 4534487 = 6801731) B6801731
theorem B1790207 : Blo 1192413 1790207 := bstep (se 1 (by rfl) ⟨1342655, by rfl⟩ : syracuseStep 1790207 = 2685311) B2685311
theorem B10195247 : Blo 1192413 10195247 := bstep (se 1 (by rfl) ⟨7646435, by rfl⟩ : syracuseStep 10195247 = 15292871) B15292871
theorem B4026887 : Blo 1192413 4026887 := bstep (se 1 (by rfl) ⟨3020165, by rfl⟩ : syracuseStep 4026887 = 6040331) B6040331
theorem B3224219 : Blo 1192413 3224219 := bstep (se 1 (by rfl) ⟨2418164, by rfl⟩ : syracuseStep 3224219 = 4836329) B4836329
theorem B1790633 : Blo 1192413 1790633 := bstep (se 2 (by rfl) ⟨671487, by rfl⟩ : syracuseStep 1790633 = 1342975) B1342975
theorem B1192895 : Blo 1192413 1192895 := bstep (se 1 (by rfl) ⟨894671, by rfl⟩ : syracuseStep 1192895 = 1789343) B1789343
theorem B3019963 : Blo 1192413 3019963 := bstep (se 1 (by rfl) ⟨2264972, by rfl⟩ : syracuseStep 3019963 = 4529945) B4529945
theorem B12899519 : Blo 1192413 12899519 := bstep (se 1 (by rfl) ⟨9674639, by rfl⟩ : syracuseStep 12899519 = 19349279) B19349279
theorem B1193287 : Blo 1192413 1193287 := bstep (se 1 (by rfl) ⟨894965, by rfl⟩ : syracuseStep 1193287 = 1789931) B1789931
theorem B1791359 : Blo 1192413 1791359 := bstep (se 1 (by rfl) ⟨1343519, by rfl⟩ : syracuseStep 1791359 = 2687039) B2687039
theorem B3585599 : Blo 1192413 3585599 := bstep (se 1 (by rfl) ⟨2689199, by rfl⟩ : syracuseStep 3585599 = 5378399) B5378399
theorem B2684699 : Blo 1192413 2684699 := bstep (se 1 (by rfl) ⟨2013524, by rfl⟩ : syracuseStep 2684699 = 4027049) B4027049
theorem B15284213 : Blo 1192413 15284213 := bstep (se 5 (by rfl) ⟨716447, by rfl⟩ : syracuseStep 15284213 = 1432895) B1432895
theorem B1194015 : Blo 1192413 1194015 := bstep (se 1 (by rfl) ⟨895511, by rfl⟩ : syracuseStep 1194015 = 1791023) B1791023
theorem B2865377 : Blo 1192413 2865377 := bstep (se 2 (by rfl) ⟨1074516, by rfl⟩ : syracuseStep 2865377 = 2149033) B2149033
theorem B2685203 : Blo 1192413 2685203 := bstep (se 1 (by rfl) ⟨2013902, by rfl⟩ : syracuseStep 2685203 = 4027805) B4027805
theorem B2013599 : Blo 1192413 2013599 := bstep (se 1 (by rfl) ⟨1510199, by rfl⟩ : syracuseStep 2013599 = 3020399) B3020399
theorem B339974617 : Blo 1192413 339974617 := bstep (se 2 (by rfl) ⟨127490481, by rfl⟩ : syracuseStep 339974617 = 254980963) B254980963
theorem B5733175 : Blo 1192413 5733175 := bstep (se 1 (by rfl) ⟨4299881, by rfl⟩ : syracuseStep 5733175 = 8599763) B8599763
theorem B21232687 : Blo 1192413 21232687 := bstep (se 1 (by rfl) ⟨15924515, by rfl⟩ : syracuseStep 21232687 = 31849031) B31849031
theorem B2686139 : Blo 1192413 2686139 := bstep (se 1 (by rfl) ⟨2014604, by rfl⟩ : syracuseStep 2686139 = 4029209) B4029209
theorem B2686265 : Blo 1192413 2686265 := bstep (se 2 (by rfl) ⟨1007349, by rfl⟩ : syracuseStep 2686265 = 2014699) B2014699
theorem B8281919 : Blo 1192413 8281919 := bstep (se 1 (by rfl) ⟨6211439, by rfl⟩ : syracuseStep 8281919 = 12422879) B12422879
theorem B2687003 : Blo 1192413 2687003 := bstep (se 1 (by rfl) ⟨2015252, by rfl⟩ : syracuseStep 2687003 = 4030505) B4030505
theorem B3022991 : Blo 1192413 3022991 := bstep (se 1 (by rfl) ⟨2267243, by rfl⟩ : syracuseStep 3022991 = 4534487) B4534487
theorem B6046163 : Blo 1192413 6046163 := bstep (se 1 (by rfl) ⟨4534622, by rfl⟩ : syracuseStep 6046163 = 9069245) B9069245
theorem B7644233 : Blo 1192413 7644233 := bstep (se 2 (by rfl) ⟨2866587, by rfl⟩ : syracuseStep 7644233 = 5733175) B5733175
theorem B2294921 : Blo 1192413 2294921 := bstep (se 2 (by rfl) ⟨860595, by rfl⟩ : syracuseStep 2294921 = 1721191) B1721191
theorem B1910251 : Blo 1192413 1910251 := bstep (se 1 (by rfl) ⟨1432688, by rfl⟩ : syracuseStep 1910251 = 2865377) B2865377
theorem B11462273 : Blo 1192413 11462273 := bstep (se 2 (by rfl) ⟨4298352, by rfl⟩ : syracuseStep 11462273 = 8596705) B8596705
theorem B22947461 : Blo 1192413 22947461 := bstep (se 4 (by rfl) ⟨2151324, by rfl⟩ : syracuseStep 22947461 = 4302649) B4302649
theorem B5442335 : Blo 1192413 5442335 := bstep (se 1 (by rfl) ⟨4081751, by rfl⟩ : syracuseStep 5442335 = 8163503) B8163503
theorem B8596475 : Blo 1192413 8596475 := bstep (se 1 (by rfl) ⟨6447356, by rfl⟩ : syracuseStep 8596475 = 12894713) B12894713
theorem B453299489 : Blo 1192413 453299489 := bstep (se 2 (by rfl) ⟨169987308, by rfl⟩ : syracuseStep 453299489 = 339974617) B339974617
theorem B17217521 : Blo 1192413 17217521 := bstep (se 2 (by rfl) ⟨6456570, by rfl⟩ : syracuseStep 17217521 = 12913141) B12913141
theorem B4304495 : Blo 1192413 4304495 := bstep (se 1 (by rfl) ⟨3228371, by rfl⟩ : syracuseStep 4304495 = 6456743) B6456743
theorem B1789799 : Blo 1192413 1789799 := bstep (se 1 (by rfl) ⟨1342349, by rfl⟩ : syracuseStep 1789799 = 2684699) B2684699
theorem B1790135 : Blo 1192413 1790135 := bstep (se 1 (by rfl) ⟨1342601, by rfl⟩ : syracuseStep 1790135 = 2685203) B2685203
theorem B2683115 : Blo 1192413 2683115 := bstep (se 1 (by rfl) ⟨2012336, by rfl⟩ : syracuseStep 2683115 = 4024673) B4024673
theorem B4026617 : Blo 1192413 4026617 := bstep (se 2 (by rfl) ⟨1509981, by rfl⟩ : syracuseStep 4026617 = 3019963) B3019963
theorem B8597917 : Blo 1192413 8597917 := bstep (se 3 (by rfl) ⟨1612109, by rfl⟩ : syracuseStep 8597917 = 3224219) B3224219
theorem B1192603 : Blo 1192413 1192603 := bstep (se 1 (by rfl) ⟨894452, by rfl⟩ : syracuseStep 1192603 = 1788905) B1788905
theorem B55841561 : Blo 1192413 55841561 := bstep (se 2 (by rfl) ⟨20940585, by rfl⟩ : syracuseStep 55841561 = 41881171) B41881171
theorem B1790759 : Blo 1192413 1790759 := bstep (se 1 (by rfl) ⟨1343069, by rfl⟩ : syracuseStep 1790759 = 2686139) B2686139
theorem B1790843 : Blo 1192413 1790843 := bstep (se 1 (by rfl) ⟨1343132, by rfl⟩ : syracuseStep 1790843 = 2686265) B2686265
theorem B38728763 : Blo 1192413 38728763 := bstep (se 1 (by rfl) ⟨29046572, by rfl⟩ : syracuseStep 38728763 = 58093145) B58093145
theorem B2684231 : Blo 1192413 2684231 := bstep (se 1 (by rfl) ⟨2013173, by rfl⟩ : syracuseStep 2684231 = 4026347) B4026347
theorem B1193471 : Blo 1192413 1193471 := bstep (se 1 (by rfl) ⟨895103, by rfl⟩ : syracuseStep 1193471 = 1790207) B1790207
theorem B6796831 : Blo 1192413 6796831 := bstep (se 1 (by rfl) ⟨5097623, by rfl⟩ : syracuseStep 6796831 = 10195247) B10195247
theorem B2266697 : Blo 1192413 2266697 := bstep (se 2 (by rfl) ⟨850011, by rfl⟩ : syracuseStep 2266697 = 1700023) B1700023
theorem B5101163 : Blo 1192413 5101163 := bstep (se 1 (by rfl) ⟨3825872, by rfl⟩ : syracuseStep 5101163 = 7651745) B7651745
theorem B2684591 : Blo 1192413 2684591 := bstep (se 1 (by rfl) ⟨2013443, by rfl⟩ : syracuseStep 2684591 = 4026887) B4026887
theorem B1193755 : Blo 1192413 1193755 := bstep (se 1 (by rfl) ⟨895316, by rfl⟩ : syracuseStep 1193755 = 1790633) B1790633
theorem B8599679 : Blo 1192413 8599679 := bstep (se 1 (by rfl) ⟨6449759, by rfl⟩ : syracuseStep 8599679 = 12899519) B12899519
theorem B1194239 : Blo 1192413 1194239 := bstep (se 1 (by rfl) ⟨895679, by rfl⟩ : syracuseStep 1194239 = 1791359) B1791359
theorem B2390399 : Blo 1192413 2390399 := bstep (se 1 (by rfl) ⟨1792799, by rfl⟩ : syracuseStep 2390399 = 3585599) B3585599
theorem B10189475 : Blo 1192413 10189475 := bstep (se 1 (by rfl) ⟨7642106, by rfl⟩ : syracuseStep 10189475 = 15284213) B15284213
theorem B7641823 : Blo 1192413 7641823 := bstep (se 1 (by rfl) ⟨5731367, by rfl⟩ : syracuseStep 7641823 = 11462735) B11462735
theorem B28310249 : Blo 1192413 28310249 := bstep (se 2 (by rfl) ⟨10616343, by rfl⟩ : syracuseStep 28310249 = 21232687) B21232687
theorem B1342399 : Blo 1192413 1342399 := bstep (se 1 (by rfl) ⟨1006799, by rfl⟩ : syracuseStep 1342399 = 2013599) B2013599
theorem B13590017 : Blo 1192413 13590017 := bstep (se 2 (by rfl) ⟨5096256, by rfl⟩ : syracuseStep 13590017 = 10192513) B10192513
theorem B10477307 : Blo 1192413 10477307 := bstep (se 1 (by rfl) ⟨7857980, by rfl⟩ : syracuseStep 10477307 = 15715961) B15715961
theorem B5521279 : Blo 1192413 5521279 := bstep (se 1 (by rfl) ⟨4140959, by rfl⟩ : syracuseStep 5521279 = 8281919) B8281919
theorem B2015327 : Blo 1192413 2015327 := bstep (se 1 (by rfl) ⟨1511495, by rfl⟩ : syracuseStep 2015327 = 3022991) B3022991
theorem B4030775 : Blo 1192413 4030775 := bstep (se 1 (by rfl) ⟨3023081, by rfl⟩ : syracuseStep 4030775 = 6046163) B6046163
theorem B5096155 : Blo 1192413 5096155 := bstep (se 1 (by rfl) ⟨3822116, by rfl⟩ : syracuseStep 5096155 = 7644233) B7644233
theorem B3400775 : Blo 1192413 3400775 := bstep (se 1 (by rfl) ⟨2550581, by rfl⟩ : syracuseStep 3400775 = 5101163) B5101163
theorem B11478347 : Blo 1192413 11478347 := bstep (se 1 (by rfl) ⟨8608760, by rfl⟩ : syracuseStep 11478347 = 17217521) B17217521
theorem B6792983 : Blo 1192413 6792983 := bstep (se 1 (by rfl) ⟨5094737, by rfl⟩ : syracuseStep 6792983 = 10189475) B10189475
theorem B9062441 : Blo 1192413 9062441 := bstep (se 2 (by rfl) ⟨3398415, by rfl⟩ : syracuseStep 9062441 = 6796831) B6796831
theorem B2869663 : Blo 1192413 2869663 := bstep (se 1 (by rfl) ⟨2152247, by rfl⟩ : syracuseStep 2869663 = 4304495) B4304495
theorem B1788743 : Blo 1192413 1788743 := bstep (se 1 (by rfl) ⟨1341557, by rfl⟩ : syracuseStep 1788743 = 2683115) B2683115
theorem B37227707 : Blo 1192413 37227707 := bstep (se 1 (by rfl) ⟨27920780, by rfl⟩ : syracuseStep 37227707 = 55841561) B55841561
theorem B11463889 : Blo 1192413 11463889 := bstep (se 2 (by rfl) ⟨4298958, by rfl⟩ : syracuseStep 11463889 = 8597917) B8597917
theorem B1789487 : Blo 1192413 1789487 := bstep (se 1 (by rfl) ⟨1342115, by rfl⟩ : syracuseStep 1789487 = 2684231) B2684231
theorem B1511131 : Blo 1192413 1511131 := bstep (se 1 (by rfl) ⟨1133348, by rfl⟩ : syracuseStep 1511131 = 2266697) B2266697
theorem B15298307 : Blo 1192413 15298307 := bstep (se 1 (by rfl) ⟨11473730, by rfl⟩ : syracuseStep 15298307 = 22947461) B22947461
theorem B1789727 : Blo 1192413 1789727 := bstep (se 1 (by rfl) ⟨1342295, by rfl⟩ : syracuseStep 1789727 = 2684591) B2684591
theorem B1789865 : Blo 1192413 1789865 := bstep (se 2 (by rfl) ⟨671199, by rfl⟩ : syracuseStep 1789865 = 1342399) B1342399
theorem B1593599 : Blo 1192413 1593599 := bstep (se 1 (by rfl) ⟨1195199, by rfl⟩ : syracuseStep 1593599 = 2390399) B2390399
theorem B27939485 : Blo 1192413 27939485 := bstep (se 3 (by rfl) ⟨5238653, by rfl⟩ : syracuseStep 27939485 = 10477307) B10477307
theorem B5730983 : Blo 1192413 5730983 := bstep (se 1 (by rfl) ⟨4298237, by rfl⟩ : syracuseStep 5730983 = 8596475) B8596475
theorem B302199659 : Blo 1192413 302199659 := bstep (se 1 (by rfl) ⟨226649744, by rfl⟩ : syracuseStep 302199659 = 453299489) B453299489
theorem B7361705 : Blo 1192413 7361705 := bstep (se 2 (by rfl) ⟨2760639, by rfl⟩ : syracuseStep 7361705 = 5521279) B5521279
theorem B1193199 : Blo 1192413 1193199 := bstep (se 1 (by rfl) ⟨894899, by rfl⟩ : syracuseStep 1193199 = 1789799) B1789799
theorem B1791335 : Blo 1192413 1791335 := bstep (se 1 (by rfl) ⟨1343501, by rfl⟩ : syracuseStep 1791335 = 2687003) B2687003
theorem B1193423 : Blo 1192413 1193423 := bstep (se 1 (by rfl) ⟨895067, by rfl⟩ : syracuseStep 1193423 = 1790135) B1790135
theorem B2684411 : Blo 1192413 2684411 := bstep (se 1 (by rfl) ⟨2013308, by rfl⟩ : syracuseStep 2684411 = 4026617) B4026617
theorem B1193839 : Blo 1192413 1193839 := bstep (se 1 (by rfl) ⟨895379, by rfl⟩ : syracuseStep 1193839 = 1790759) B1790759
theorem B1193895 : Blo 1192413 1193895 := bstep (se 1 (by rfl) ⟨895421, by rfl⟩ : syracuseStep 1193895 = 1790843) B1790843
theorem B25819175 : Blo 1192413 25819175 := bstep (se 1 (by rfl) ⟨19364381, by rfl⟩ : syracuseStep 25819175 = 38728763) B38728763
theorem B1529947 : Blo 1192413 1529947 := bstep (se 1 (by rfl) ⟨1147460, by rfl⟩ : syracuseStep 1529947 = 2294921) B2294921
theorem B10189097 : Blo 1192413 10189097 := bstep (se 2 (by rfl) ⟨3820911, by rfl⟩ : syracuseStep 10189097 = 7641823) B7641823
theorem B7641515 : Blo 1192413 7641515 := bstep (se 1 (by rfl) ⟨5731136, by rfl⟩ : syracuseStep 7641515 = 11462273) B11462273
theorem B5733119 : Blo 1192413 5733119 := bstep (se 1 (by rfl) ⟨4299839, by rfl⟩ : syracuseStep 5733119 = 8599679) B8599679
theorem B18873499 : Blo 1192413 18873499 := bstep (se 1 (by rfl) ⟨14155124, by rfl⟩ : syracuseStep 18873499 = 28310249) B28310249
theorem B3628223 : Blo 1192413 3628223 := bstep (se 1 (by rfl) ⟨2721167, by rfl⟩ : syracuseStep 3628223 = 5442335) B5442335
theorem B2547001 : Blo 1192413 2547001 := bstep (se 2 (by rfl) ⟨955125, by rfl⟩ : syracuseStep 2547001 = 1910251) B1910251
theorem B9060011 : Blo 1192413 9060011 := bstep (se 1 (by rfl) ⟨6795008, by rfl⟩ : syracuseStep 9060011 = 13590017) B13590017
theorem B1343551 : Blo 1192413 1343551 := bstep (se 1 (by rfl) ⟨1007663, by rfl⟩ : syracuseStep 1343551 = 2015327) B2015327
theorem B2687183 : Blo 1192413 2687183 := bstep (se 1 (by rfl) ⟨2015387, by rfl⟩ : syracuseStep 2687183 = 4030775) B4030775
theorem B8159717 : Blo 1192413 8159717 := bstep (se 4 (by rfl) ⟨764973, by rfl⟩ : syracuseStep 8159717 = 1529947) B1529947
theorem B3826217 : Blo 1192413 3826217 := bstep (se 2 (by rfl) ⟨1434831, by rfl⟩ : syracuseStep 3826217 = 2869663) B2869663
theorem B201466439 : Blo 1192413 201466439 := bstep (se 1 (by rfl) ⟨151099829, by rfl⟩ : syracuseStep 201466439 = 302199659) B302199659
theorem B4907803 : Blo 1192413 4907803 := bstep (se 1 (by rfl) ⟨3680852, by rfl⟩ : syracuseStep 4907803 = 7361705) B7361705
theorem B7652231 : Blo 1192413 7652231 := bstep (se 1 (by rfl) ⟨5739173, by rfl⟩ : syracuseStep 7652231 = 11478347) B11478347
theorem B6792731 : Blo 1192413 6792731 := bstep (se 1 (by rfl) ⟨5094548, by rfl⟩ : syracuseStep 6792731 = 10189097) B10189097
theorem B2418815 : Blo 1192413 2418815 := bstep (se 1 (by rfl) ⟨1814111, by rfl⟩ : syracuseStep 2418815 = 3628223) B3628223
theorem B6040007 : Blo 1192413 6040007 := bstep (se 1 (by rfl) ⟨4530005, by rfl⟩ : syracuseStep 6040007 = 9060011) B9060011
theorem B3820655 : Blo 1192413 3820655 := bstep (se 1 (by rfl) ⟨2865491, by rfl⟩ : syracuseStep 3820655 = 5730983) B5730983
theorem B6794873 : Blo 1192413 6794873 := bstep (se 2 (by rfl) ⟨2548077, by rfl⟩ : syracuseStep 6794873 = 5096155) B5096155
theorem B1789607 : Blo 1192413 1789607 := bstep (se 1 (by rfl) ⟨1342205, by rfl⟩ : syracuseStep 1789607 = 2684411) B2684411
theorem B6041627 : Blo 1192413 6041627 := bstep (se 1 (by rfl) ⟨4531220, by rfl⟩ : syracuseStep 6041627 = 9062441) B9062441
theorem B3396001 : Blo 1192413 3396001 := bstep (se 2 (by rfl) ⟨1273500, by rfl⟩ : syracuseStep 3396001 = 2547001) B2547001
theorem B3822079 : Blo 1192413 3822079 := bstep (se 1 (by rfl) ⟨2866559, by rfl⟩ : syracuseStep 3822079 = 5733119) B5733119
theorem B1192495 : Blo 1192413 1192495 := bstep (se 1 (by rfl) ⟨894371, by rfl⟩ : syracuseStep 1192495 = 1788743) B1788743
theorem B24818471 : Blo 1192413 24818471 := bstep (se 1 (by rfl) ⟨18613853, by rfl⟩ : syracuseStep 24818471 = 37227707) B37227707
theorem B1192991 : Blo 1192413 1192991 := bstep (se 1 (by rfl) ⟨894743, by rfl⟩ : syracuseStep 1192991 = 1789487) B1789487
theorem B1193151 : Blo 1192413 1193151 := bstep (se 1 (by rfl) ⟨894863, by rfl⟩ : syracuseStep 1193151 = 1789727) B1789727
theorem B1193243 : Blo 1192413 1193243 := bstep (se 1 (by rfl) ⟨894932, by rfl⟩ : syracuseStep 1193243 = 1789865) B1789865
theorem B68851133 : Blo 1192413 68851133 := bstep (se 3 (by rfl) ⟨12909587, by rfl⟩ : syracuseStep 68851133 = 25819175) B25819175
theorem B18626323 : Blo 1192413 18626323 := bstep (se 1 (by rfl) ⟨13969742, by rfl⟩ : syracuseStep 18626323 = 27939485) B27939485
theorem B4249597 : Blo 1192413 4249597 := bstep (se 3 (by rfl) ⟨796799, by rfl⟩ : syracuseStep 4249597 = 1593599) B1593599
theorem B2267183 : Blo 1192413 2267183 := bstep (se 1 (by rfl) ⟨1700387, by rfl⟩ : syracuseStep 2267183 = 3400775) B3400775
theorem B1194223 : Blo 1192413 1194223 := bstep (se 1 (by rfl) ⟨895667, by rfl⟩ : syracuseStep 1194223 = 1791335) B1791335
theorem B4528655 : Blo 1192413 4528655 := bstep (se 1 (by rfl) ⟨3396491, by rfl⟩ : syracuseStep 4528655 = 6792983) B6792983
theorem B25164665 : Blo 1192413 25164665 := bstep (se 2 (by rfl) ⟨9436749, by rfl⟩ : syracuseStep 25164665 = 18873499) B18873499
theorem B15285185 : Blo 1192413 15285185 := bstep (se 2 (by rfl) ⟨5731944, by rfl⟩ : syracuseStep 15285185 = 11463889) B11463889
theorem B5094343 : Blo 1192413 5094343 := bstep (se 1 (by rfl) ⟨3820757, by rfl⟩ : syracuseStep 5094343 = 7641515) B7641515
theorem B2014841 : Blo 1192413 2014841 := bstep (se 2 (by rfl) ⟨755565, by rfl⟩ : syracuseStep 2014841 = 1511131) B1511131
theorem B10198871 : Blo 1192413 10198871 := bstep (se 1 (by rfl) ⟨7649153, by rfl⟩ : syracuseStep 10198871 = 15298307) B15298307
theorem B5439811 : Blo 1192413 5439811 := bstep (se 1 (by rfl) ⟨4079858, by rfl⟩ : syracuseStep 5439811 = 8159717) B8159717
theorem B5096105 : Blo 1192413 5096105 := bstep (se 2 (by rfl) ⟨1911039, by rfl⟩ : syracuseStep 5096105 = 3822079) B3822079
theorem B45900755 : Blo 1192413 45900755 := bstep (se 1 (by rfl) ⟨34425566, by rfl⟩ : syracuseStep 45900755 = 68851133) B68851133
theorem B6792457 : Blo 1192413 6792457 := bstep (se 2 (by rfl) ⟨2547171, by rfl⟩ : syracuseStep 6792457 = 5094343) B5094343
theorem B134310959 : Blo 1192413 134310959 := bstep (se 1 (by rfl) ⟨100733219, by rfl⟩ : syracuseStep 134310959 = 201466439) B201466439
theorem B1511455 : Blo 1192413 1511455 := bstep (se 1 (by rfl) ⟨1133591, by rfl⟩ : syracuseStep 1511455 = 2267183) B2267183
theorem B10203245 : Blo 1192413 10203245 := bstep (se 3 (by rfl) ⟨1913108, by rfl⟩ : syracuseStep 10203245 = 3826217) B3826217
theorem B4026671 : Blo 1192413 4026671 := bstep (se 1 (by rfl) ⟨3020003, by rfl⟩ : syracuseStep 4026671 = 6040007) B6040007
theorem B3019103 : Blo 1192413 3019103 := bstep (se 1 (by rfl) ⟨2264327, by rfl⟩ : syracuseStep 3019103 = 4528655) B4528655
theorem B24835097 : Blo 1192413 24835097 := bstep (se 2 (by rfl) ⟨9313161, by rfl⟩ : syracuseStep 24835097 = 18626323) B18626323
theorem B1193071 : Blo 1192413 1193071 := bstep (se 1 (by rfl) ⟨894803, by rfl⟩ : syracuseStep 1193071 = 1789607) B1789607
theorem B5666129 : Blo 1192413 5666129 := bstep (se 2 (by rfl) ⟨2124798, by rfl⟩ : syracuseStep 5666129 = 4249597) B4249597
theorem B4027751 : Blo 1192413 4027751 := bstep (se 1 (by rfl) ⟨3020813, by rfl⟩ : syracuseStep 4027751 = 6041627) B6041627
theorem B1791401 : Blo 1192413 1791401 := bstep (se 2 (by rfl) ⟨671775, by rfl⟩ : syracuseStep 1791401 = 1343551) B1343551
theorem B1791455 : Blo 1192413 1791455 := bstep (se 1 (by rfl) ⟨1343591, by rfl⟩ : syracuseStep 1791455 = 2687183) B2687183
theorem B10188413 : Blo 1192413 10188413 := bstep (se 3 (by rfl) ⟨1910327, by rfl⟩ : syracuseStep 10188413 = 3820655) B3820655
theorem B16545647 : Blo 1192413 16545647 := bstep (se 1 (by rfl) ⟨12409235, by rfl⟩ : syracuseStep 16545647 = 24818471) B24818471
theorem B4528001 : Blo 1192413 4528001 := bstep (se 2 (by rfl) ⟨1698000, by rfl⟩ : syracuseStep 4528001 = 3396001) B3396001
theorem B5101487 : Blo 1192413 5101487 := bstep (se 1 (by rfl) ⟨3826115, by rfl⟩ : syracuseStep 5101487 = 7652231) B7652231
theorem B4528487 : Blo 1192413 4528487 := bstep (se 1 (by rfl) ⟨3396365, by rfl⟩ : syracuseStep 4528487 = 6792731) B6792731
theorem B6543737 : Blo 1192413 6543737 := bstep (se 2 (by rfl) ⟨2453901, by rfl⟩ : syracuseStep 6543737 = 4907803) B4907803
theorem B1612543 : Blo 1192413 1612543 := bstep (se 1 (by rfl) ⟨1209407, by rfl⟩ : syracuseStep 1612543 = 2418815) B2418815
theorem B16776443 : Blo 1192413 16776443 := bstep (se 1 (by rfl) ⟨12582332, by rfl⟩ : syracuseStep 16776443 = 25164665) B25164665
theorem B10190123 : Blo 1192413 10190123 := bstep (se 1 (by rfl) ⟨7642592, by rfl⟩ : syracuseStep 10190123 = 15285185) B15285185
theorem B4529915 : Blo 1192413 4529915 := bstep (se 1 (by rfl) ⟨3397436, by rfl⟩ : syracuseStep 4529915 = 6794873) B6794873
theorem B1343227 : Blo 1192413 1343227 := bstep (se 1 (by rfl) ⟨1007420, by rfl⟩ : syracuseStep 1343227 = 2014841) B2014841
theorem B6799247 : Blo 1192413 6799247 := bstep (se 1 (by rfl) ⟨5099435, by rfl⟩ : syracuseStep 6799247 = 10198871) B10198871
theorem B2015273 : Blo 1192413 2015273 := bstep (se 2 (by rfl) ⟨755727, by rfl⟩ : syracuseStep 2015273 = 1511455) B1511455
theorem B44737181 : Blo 1192413 44737181 := bstep (se 3 (by rfl) ⟨8388221, by rfl⟩ : syracuseStep 44737181 = 16776443) B16776443
theorem B16556731 : Blo 1192413 16556731 := bstep (se 1 (by rfl) ⟨12417548, by rfl⟩ : syracuseStep 16556731 = 24835097) B24835097
theorem B3777419 : Blo 1192413 3777419 := bstep (se 1 (by rfl) ⟨2833064, by rfl⟩ : syracuseStep 3777419 = 5666129) B5666129
theorem B6792275 : Blo 1192413 6792275 := bstep (se 1 (by rfl) ⟨5094206, by rfl⟩ : syracuseStep 6792275 = 10188413) B10188413
theorem B3400991 : Blo 1192413 3400991 := bstep (se 1 (by rfl) ⟨2550743, by rfl⟩ : syracuseStep 3400991 = 5101487) B5101487
theorem B89540639 : Blo 1192413 89540639 := bstep (se 1 (by rfl) ⟨67155479, by rfl⟩ : syracuseStep 89540639 = 134310959) B134310959
theorem B6793415 : Blo 1192413 6793415 := bstep (se 1 (by rfl) ⟨5095061, by rfl⟩ : syracuseStep 6793415 = 10190123) B10190123
theorem B4532831 : Blo 1192413 4532831 := bstep (se 1 (by rfl) ⟨3399623, by rfl⟩ : syracuseStep 4532831 = 6799247) B6799247
theorem B6802163 : Blo 1192413 6802163 := bstep (se 1 (by rfl) ⟨5101622, by rfl⟩ : syracuseStep 6802163 = 10203245) B10203245
theorem B7253081 : Blo 1192413 7253081 := bstep (se 2 (by rfl) ⟨2719905, by rfl⟩ : syracuseStep 7253081 = 5439811) B5439811
theorem B30600503 : Blo 1192413 30600503 := bstep (se 1 (by rfl) ⟨22950377, by rfl⟩ : syracuseStep 30600503 = 45900755) B45900755
theorem B2150057 : Blo 1192413 2150057 := bstep (se 2 (by rfl) ⟨806271, by rfl⟩ : syracuseStep 2150057 = 1612543) B1612543
theorem B11030431 : Blo 1192413 11030431 := bstep (se 1 (by rfl) ⟨8272823, by rfl⟩ : syracuseStep 11030431 = 16545647) B16545647
theorem B3018667 : Blo 1192413 3018667 := bstep (se 1 (by rfl) ⟨2264000, by rfl⟩ : syracuseStep 3018667 = 4528001) B4528001
theorem B3018991 : Blo 1192413 3018991 := bstep (se 1 (by rfl) ⟨2264243, by rfl⟩ : syracuseStep 3018991 = 4528487) B4528487
theorem B4362491 : Blo 1192413 4362491 := bstep (se 1 (by rfl) ⟨3271868, by rfl⟩ : syracuseStep 4362491 = 6543737) B6543737
theorem B9056609 : Blo 1192413 9056609 := bstep (se 2 (by rfl) ⟨3396228, by rfl⟩ : syracuseStep 9056609 = 6792457) B6792457
theorem B1790969 : Blo 1192413 1790969 := bstep (se 2 (by rfl) ⟨671613, by rfl⟩ : syracuseStep 1790969 = 1343227) B1343227
theorem B3019943 : Blo 1192413 3019943 := bstep (se 1 (by rfl) ⟨2264957, by rfl⟩ : syracuseStep 3019943 = 4529915) B4529915
theorem B2684447 : Blo 1192413 2684447 := bstep (se 1 (by rfl) ⟨2013335, by rfl⟩ : syracuseStep 2684447 = 4026671) B4026671
theorem B2012735 : Blo 1192413 2012735 := bstep (se 1 (by rfl) ⟨1509551, by rfl⟩ : syracuseStep 2012735 = 3019103) B3019103
theorem B3397403 : Blo 1192413 3397403 := bstep (se 1 (by rfl) ⟨2548052, by rfl⟩ : syracuseStep 3397403 = 5096105) B5096105
theorem B2685167 : Blo 1192413 2685167 := bstep (se 1 (by rfl) ⟨2013875, by rfl⟩ : syracuseStep 2685167 = 4027751) B4027751
theorem B1194267 : Blo 1192413 1194267 := bstep (se 1 (by rfl) ⟨895700, by rfl⟩ : syracuseStep 1194267 = 1791401) B1791401
theorem B1194303 : Blo 1192413 1194303 := bstep (se 1 (by rfl) ⟨895727, by rfl⟩ : syracuseStep 1194303 = 1791455) B1791455
theorem B1343515 : Blo 1192413 1343515 := bstep (se 1 (by rfl) ⟨1007636, by rfl⟩ : syracuseStep 1343515 = 2015273) B2015273
theorem B6037739 : Blo 1192413 6037739 := bstep (se 1 (by rfl) ⟨4528304, by rfl⟩ : syracuseStep 6037739 = 9056609) B9056609
theorem B11633309 : Blo 1192413 11633309 := bstep (se 3 (by rfl) ⟨2181245, by rfl⟩ : syracuseStep 11633309 = 4362491) B4362491
theorem B88302565 : Blo 1192413 88302565 := bstep (se 4 (by rfl) ⟨8278365, by rfl⟩ : syracuseStep 88302565 = 16556731) B16556731
theorem B4835387 : Blo 1192413 4835387 := bstep (se 1 (by rfl) ⟨3626540, by rfl⟩ : syracuseStep 4835387 = 7253081) B7253081
theorem B20400335 : Blo 1192413 20400335 := bstep (se 1 (by rfl) ⟨15300251, by rfl⟩ : syracuseStep 20400335 = 30600503) B30600503
theorem B14707241 : Blo 1192413 14707241 := bstep (se 2 (by rfl) ⟨5515215, by rfl⟩ : syracuseStep 14707241 = 11030431) B11030431
theorem B4024889 : Blo 1192413 4024889 := bstep (se 2 (by rfl) ⟨1509333, by rfl⟩ : syracuseStep 4024889 = 3018667) B3018667
theorem B4025321 : Blo 1192413 4025321 := bstep (se 2 (by rfl) ⟨1509495, by rfl⟩ : syracuseStep 4025321 = 3018991) B3018991
theorem B1789631 : Blo 1192413 1789631 := bstep (se 1 (by rfl) ⟨1342223, by rfl⟩ : syracuseStep 1789631 = 2684447) B2684447
theorem B2264935 : Blo 1192413 2264935 := bstep (se 1 (by rfl) ⟨1698701, by rfl⟩ : syracuseStep 2264935 = 3397403) B3397403
theorem B1790111 : Blo 1192413 1790111 := bstep (se 1 (by rfl) ⟨1342583, by rfl⟩ : syracuseStep 1790111 = 2685167) B2685167
theorem B4534775 : Blo 1192413 4534775 := bstep (se 1 (by rfl) ⟨3401081, by rfl⟩ : syracuseStep 4534775 = 6802163) B6802163
theorem B10073117 : Blo 1192413 10073117 := bstep (se 3 (by rfl) ⟨1888709, by rfl⟩ : syracuseStep 10073117 = 3777419) B3777419
theorem B29824787 : Blo 1192413 29824787 := bstep (se 1 (by rfl) ⟨22368590, by rfl⟩ : syracuseStep 29824787 = 44737181) B44737181
theorem B1193979 : Blo 1192413 1193979 := bstep (se 1 (by rfl) ⟨895484, by rfl⟩ : syracuseStep 1193979 = 1790969) B1790969
theorem B4528183 : Blo 1192413 4528183 := bstep (se 1 (by rfl) ⟨3396137, by rfl⟩ : syracuseStep 4528183 = 6792275) B6792275
theorem B2013295 : Blo 1192413 2013295 := bstep (se 1 (by rfl) ⟨1509971, by rfl⟩ : syracuseStep 2013295 = 3019943) B3019943
theorem B2267327 : Blo 1192413 2267327 := bstep (se 1 (by rfl) ⟨1700495, by rfl⟩ : syracuseStep 2267327 = 3400991) B3400991
theorem B1341823 : Blo 1192413 1341823 := bstep (se 1 (by rfl) ⟨1006367, by rfl⟩ : syracuseStep 1341823 = 2012735) B2012735
theorem B59693759 : Blo 1192413 59693759 := bstep (se 1 (by rfl) ⟨44770319, by rfl⟩ : syracuseStep 59693759 = 89540639) B89540639
theorem B4528943 : Blo 1192413 4528943 := bstep (se 1 (by rfl) ⟨3396707, by rfl⟩ : syracuseStep 4528943 = 6793415) B6793415
theorem B3021887 : Blo 1192413 3021887 := bstep (se 1 (by rfl) ⟨2266415, by rfl⟩ : syracuseStep 3021887 = 4532831) B4532831
theorem B1433371 : Blo 1192413 1433371 := bstep (se 1 (by rfl) ⟨1075028, by rfl⟩ : syracuseStep 1433371 = 2150057) B2150057
theorem B6037577 : Blo 1192413 6037577 := bstep (se 2 (by rfl) ⟨2264091, by rfl⟩ : syracuseStep 6037577 = 4528183) B4528183
theorem B26861645 : Blo 1192413 26861645 := bstep (se 3 (by rfl) ⟨5036558, by rfl⟩ : syracuseStep 26861645 = 10073117) B10073117
theorem B12894365 : Blo 1192413 12894365 := bstep (se 3 (by rfl) ⟨2417693, by rfl⟩ : syracuseStep 12894365 = 4835387) B4835387
theorem B3023183 : Blo 1192413 3023183 := bstep (se 1 (by rfl) ⟨2267387, by rfl⟩ : syracuseStep 3023183 = 4534775) B4534775
theorem B19883191 : Blo 1192413 19883191 := bstep (se 1 (by rfl) ⟨14912393, by rfl⟩ : syracuseStep 19883191 = 29824787) B29824787
theorem B117736753 : Blo 1192413 117736753 := bstep (se 2 (by rfl) ⟨44151282, by rfl⟩ : syracuseStep 117736753 = 88302565) B88302565
theorem B13600223 : Blo 1192413 13600223 := bstep (se 1 (by rfl) ⟨10200167, by rfl⟩ : syracuseStep 13600223 = 20400335) B20400335
theorem B7755539 : Blo 1192413 7755539 := bstep (se 1 (by rfl) ⟨5816654, by rfl⟩ : syracuseStep 7755539 = 11633309) B11633309
theorem B1911161 : Blo 1192413 1911161 := bstep (se 2 (by rfl) ⟨716685, by rfl⟩ : syracuseStep 1911161 = 1433371) B1433371
theorem B4025159 : Blo 1192413 4025159 := bstep (se 1 (by rfl) ⟨3018869, by rfl⟩ : syracuseStep 4025159 = 6037739) B6037739
theorem B1789097 : Blo 1192413 1789097 := bstep (se 2 (by rfl) ⟨670911, by rfl⟩ : syracuseStep 1789097 = 1341823) B1341823
theorem B1511551 : Blo 1192413 1511551 := bstep (se 1 (by rfl) ⟨1133663, by rfl⟩ : syracuseStep 1511551 = 2267327) B2267327
theorem B2683259 : Blo 1192413 2683259 := bstep (se 1 (by rfl) ⟨2012444, by rfl⟩ : syracuseStep 2683259 = 4024889) B4024889
theorem B3019295 : Blo 1192413 3019295 := bstep (se 1 (by rfl) ⟨2264471, by rfl⟩ : syracuseStep 3019295 = 4528943) B4528943
theorem B2683547 : Blo 1192413 2683547 := bstep (se 1 (by rfl) ⟨2012660, by rfl⟩ : syracuseStep 2683547 = 4025321) B4025321
theorem B1193087 : Blo 1192413 1193087 := bstep (se 1 (by rfl) ⟨894815, by rfl⟩ : syracuseStep 1193087 = 1789631) B1789631
theorem B3019913 : Blo 1192413 3019913 := bstep (se 2 (by rfl) ⟨1132467, by rfl⟩ : syracuseStep 3019913 = 2264935) B2264935
theorem B1791353 : Blo 1192413 1791353 := bstep (se 2 (by rfl) ⟨671757, by rfl⟩ : syracuseStep 1791353 = 1343515) B1343515
theorem B1193407 : Blo 1192413 1193407 := bstep (se 1 (by rfl) ⟨895055, by rfl⟩ : syracuseStep 1193407 = 1790111) B1790111
theorem B2684393 : Blo 1192413 2684393 := bstep (se 2 (by rfl) ⟨1006647, by rfl⟩ : syracuseStep 2684393 = 2013295) B2013295
theorem B9804827 : Blo 1192413 9804827 := bstep (se 1 (by rfl) ⟨7353620, by rfl⟩ : syracuseStep 9804827 = 14707241) B14707241
theorem B39795839 : Blo 1192413 39795839 := bstep (se 1 (by rfl) ⟨29846879, by rfl⟩ : syracuseStep 39795839 = 59693759) B59693759
theorem B2014591 : Blo 1192413 2014591 := bstep (se 1 (by rfl) ⟨1510943, by rfl⟩ : syracuseStep 2014591 = 3021887) B3021887
theorem B2015401 : Blo 1192413 2015401 := bstep (se 2 (by rfl) ⟨755775, by rfl⟩ : syracuseStep 2015401 = 1511551) B1511551
theorem B71631053 : Blo 1192413 71631053 := bstep (se 3 (by rfl) ⟨13430822, by rfl⟩ : syracuseStep 71631053 = 26861645) B26861645
theorem B2015455 : Blo 1192413 2015455 := bstep (se 1 (by rfl) ⟨1511591, by rfl⟩ : syracuseStep 2015455 = 3023183) B3023183
theorem B5096429 : Blo 1192413 5096429 := bstep (se 3 (by rfl) ⟨955580, by rfl⟩ : syracuseStep 5096429 = 1911161) B1911161
theorem B26510921 : Blo 1192413 26510921 := bstep (se 2 (by rfl) ⟨9941595, by rfl⟩ : syracuseStep 26510921 = 19883191) B19883191
theorem B4025051 : Blo 1192413 4025051 := bstep (se 1 (by rfl) ⟨3018788, by rfl⟩ : syracuseStep 4025051 = 6037577) B6037577
theorem B8596243 : Blo 1192413 8596243 := bstep (se 1 (by rfl) ⟨6447182, by rfl⟩ : syracuseStep 8596243 = 12894365) B12894365
theorem B1788839 : Blo 1192413 1788839 := bstep (se 1 (by rfl) ⟨1341629, by rfl⟩ : syracuseStep 1788839 = 2683259) B2683259
theorem B1789031 : Blo 1192413 1789031 := bstep (se 1 (by rfl) ⟨1341773, by rfl⟩ : syracuseStep 1789031 = 2683547) B2683547
theorem B1789595 : Blo 1192413 1789595 := bstep (se 1 (by rfl) ⟨1342196, by rfl⟩ : syracuseStep 1789595 = 2684393) B2684393
theorem B2683439 : Blo 1192413 2683439 := bstep (se 1 (by rfl) ⟨2012579, by rfl⟩ : syracuseStep 2683439 = 4025159) B4025159
theorem B20681437 : Blo 1192413 20681437 := bstep (se 3 (by rfl) ⟨3877769, by rfl⟩ : syracuseStep 20681437 = 7755539) B7755539
theorem B26530559 : Blo 1192413 26530559 := bstep (se 1 (by rfl) ⟨19897919, by rfl⟩ : syracuseStep 26530559 = 39795839) B39795839
theorem B1192731 : Blo 1192413 1192731 := bstep (se 1 (by rfl) ⟨894548, by rfl⟩ : syracuseStep 1192731 = 1789097) B1789097
theorem B2012863 : Blo 1192413 2012863 := bstep (se 1 (by rfl) ⟨1509647, by rfl⟩ : syracuseStep 2012863 = 3019295) B3019295
theorem B2013275 : Blo 1192413 2013275 := bstep (se 1 (by rfl) ⟨1509956, by rfl⟩ : syracuseStep 2013275 = 3019913) B3019913
theorem B1194235 : Blo 1192413 1194235 := bstep (se 1 (by rfl) ⟨895676, by rfl⟩ : syracuseStep 1194235 = 1791353) B1791353
theorem B9066815 : Blo 1192413 9066815 := bstep (se 1 (by rfl) ⟨6800111, by rfl⟩ : syracuseStep 9066815 = 13600223) B13600223
theorem B156982337 : Blo 1192413 156982337 := bstep (se 2 (by rfl) ⟨58868376, by rfl⟩ : syracuseStep 156982337 = 117736753) B117736753
theorem B2686121 : Blo 1192413 2686121 := bstep (se 2 (by rfl) ⟨1007295, by rfl⟩ : syracuseStep 2686121 = 2014591) B2014591
theorem B6536551 : Blo 1192413 6536551 := bstep (se 1 (by rfl) ⟨4902413, by rfl⟩ : syracuseStep 6536551 = 9804827) B9804827
theorem B2687201 : Blo 1192413 2687201 := bstep (se 2 (by rfl) ⟨1007700, by rfl⟩ : syracuseStep 2687201 = 2015401) B2015401
theorem B2687273 : Blo 1192413 2687273 := bstep (se 2 (by rfl) ⟨1007727, by rfl⟩ : syracuseStep 2687273 = 2015455) B2015455
theorem B27575249 : Blo 1192413 27575249 := bstep (se 2 (by rfl) ⟨10340718, by rfl⟩ : syracuseStep 27575249 = 20681437) B20681437
theorem B11461657 : Blo 1192413 11461657 := bstep (se 2 (by rfl) ⟨4298121, by rfl⟩ : syracuseStep 11461657 = 8596243) B8596243
theorem B104654891 : Blo 1192413 104654891 := bstep (se 1 (by rfl) ⟨78491168, by rfl⟩ : syracuseStep 104654891 = 156982337) B156982337
theorem B47754035 : Blo 1192413 47754035 := bstep (se 1 (by rfl) ⟨35815526, by rfl⟩ : syracuseStep 47754035 = 71631053) B71631053
theorem B1788959 : Blo 1192413 1788959 := bstep (se 1 (by rfl) ⟨1341719, by rfl⟩ : syracuseStep 1788959 = 2683439) B2683439
theorem B17673947 : Blo 1192413 17673947 := bstep (se 1 (by rfl) ⟨13255460, by rfl⟩ : syracuseStep 17673947 = 26510921) B26510921
theorem B2683367 : Blo 1192413 2683367 := bstep (se 1 (by rfl) ⟨2012525, by rfl⟩ : syracuseStep 2683367 = 4025051) B4025051
theorem B1192559 : Blo 1192413 1192559 := bstep (se 1 (by rfl) ⟨894419, by rfl⟩ : syracuseStep 1192559 = 1788839) B1788839
theorem B1192687 : Blo 1192413 1192687 := bstep (se 1 (by rfl) ⟨894515, by rfl⟩ : syracuseStep 1192687 = 1789031) B1789031
theorem B1790747 : Blo 1192413 1790747 := bstep (se 1 (by rfl) ⟨1343060, by rfl⟩ : syracuseStep 1790747 = 2686121) B2686121
theorem B2683817 : Blo 1192413 2683817 := bstep (se 2 (by rfl) ⟨1006431, by rfl⟩ : syracuseStep 2683817 = 2012863) B2012863
theorem B1193063 : Blo 1192413 1193063 := bstep (se 1 (by rfl) ⟨894797, by rfl⟩ : syracuseStep 1193063 = 1789595) B1789595
theorem B3397619 : Blo 1192413 3397619 := bstep (se 1 (by rfl) ⟨2548214, by rfl⟩ : syracuseStep 3397619 = 5096429) B5096429
theorem B1342183 : Blo 1192413 1342183 := bstep (se 1 (by rfl) ⟨1006637, by rfl⟩ : syracuseStep 1342183 = 2013275) B2013275
theorem B6044543 : Blo 1192413 6044543 := bstep (se 1 (by rfl) ⟨4533407, by rfl⟩ : syracuseStep 6044543 = 9066815) B9066815
theorem B8715401 : Blo 1192413 8715401 := bstep (se 2 (by rfl) ⟨3268275, by rfl⟩ : syracuseStep 8715401 = 6536551) B6536551
theorem B282992629 : Blo 1192413 282992629 := bstep (se 5 (by rfl) ⟨13265279, by rfl⟩ : syracuseStep 282992629 = 26530559) B26530559
theorem B31836023 : Blo 1192413 31836023 := bstep (se 1 (by rfl) ⟨23877017, by rfl⟩ : syracuseStep 31836023 = 47754035) B47754035
theorem B5810267 : Blo 1192413 5810267 := bstep (se 1 (by rfl) ⟨4357700, by rfl⟩ : syracuseStep 5810267 = 8715401) B8715401
theorem B11782631 : Blo 1192413 11782631 := bstep (se 1 (by rfl) ⟨8836973, by rfl⟩ : syracuseStep 11782631 = 17673947) B17673947
theorem B73533997 : Blo 1192413 73533997 := bstep (se 3 (by rfl) ⟨13787624, by rfl⟩ : syracuseStep 73533997 = 27575249) B27575249
theorem B1788911 : Blo 1192413 1788911 := bstep (se 1 (by rfl) ⟨1341683, by rfl⟩ : syracuseStep 1788911 = 2683367) B2683367
theorem B1789211 : Blo 1192413 1789211 := bstep (se 1 (by rfl) ⟨1341908, by rfl⟩ : syracuseStep 1789211 = 2683817) B2683817
theorem B1789577 : Blo 1192413 1789577 := bstep (se 2 (by rfl) ⟨671091, by rfl⟩ : syracuseStep 1789577 = 1342183) B1342183
theorem B2265079 : Blo 1192413 2265079 := bstep (se 1 (by rfl) ⟨1698809, by rfl⟩ : syracuseStep 2265079 = 3397619) B3397619
theorem B15282209 : Blo 1192413 15282209 := bstep (se 2 (by rfl) ⟨5730828, by rfl⟩ : syracuseStep 15282209 = 11461657) B11461657
theorem B1192639 : Blo 1192413 1192639 := bstep (se 1 (by rfl) ⟨894479, by rfl⟩ : syracuseStep 1192639 = 1788959) B1788959
theorem B1791467 : Blo 1192413 1791467 := bstep (se 1 (by rfl) ⟨1343600, by rfl⟩ : syracuseStep 1791467 = 2687201) B2687201
theorem B1791515 : Blo 1192413 1791515 := bstep (se 1 (by rfl) ⟨1343636, by rfl⟩ : syracuseStep 1791515 = 2687273) B2687273
theorem B1193831 : Blo 1192413 1193831 := bstep (se 1 (by rfl) ⟨895373, by rfl⟩ : syracuseStep 1193831 = 1790747) B1790747
theorem B69769927 : Blo 1192413 69769927 := bstep (se 1 (by rfl) ⟨52327445, by rfl⟩ : syracuseStep 69769927 = 104654891) B104654891
theorem B4029695 : Blo 1192413 4029695 := bstep (se 1 (by rfl) ⟨3022271, by rfl⟩ : syracuseStep 4029695 = 6044543) B6044543
theorem B377323505 : Blo 1192413 377323505 := bstep (se 2 (by rfl) ⟨141496314, by rfl⟩ : syracuseStep 377323505 = 282992629) B282992629
theorem B98045329 : Blo 1192413 98045329 := bstep (se 2 (by rfl) ⟨36766998, by rfl⟩ : syracuseStep 98045329 = 73533997) B73533997
theorem B1192607 : Blo 1192413 1192607 := bstep (se 1 (by rfl) ⟨894455, by rfl⟩ : syracuseStep 1192607 = 1788911) B1788911
theorem B1192807 : Blo 1192413 1192807 := bstep (se 1 (by rfl) ⟨894605, by rfl⟩ : syracuseStep 1192807 = 1789211) B1789211
theorem B1193051 : Blo 1192413 1193051 := bstep (se 1 (by rfl) ⟨894788, by rfl⟩ : syracuseStep 1193051 = 1789577) B1789577
theorem B3020105 : Blo 1192413 3020105 := bstep (se 2 (by rfl) ⟨1132539, by rfl⟩ : syracuseStep 3020105 = 2265079) B2265079
theorem B251549003 : Blo 1192413 251549003 := bstep (se 1 (by rfl) ⟨188661752, by rfl⟩ : syracuseStep 251549003 = 377323505) B377323505
theorem B10188139 : Blo 1192413 10188139 := bstep (se 1 (by rfl) ⟨7641104, by rfl⟩ : syracuseStep 10188139 = 15282209) B15282209
theorem B93026569 : Blo 1192413 93026569 := bstep (se 2 (by rfl) ⟨34884963, by rfl⟩ : syracuseStep 93026569 = 69769927) B69769927
theorem B1194311 : Blo 1192413 1194311 := bstep (se 1 (by rfl) ⟨895733, by rfl⟩ : syracuseStep 1194311 = 1791467) B1791467
theorem B1194343 : Blo 1192413 1194343 := bstep (se 1 (by rfl) ⟨895757, by rfl⟩ : syracuseStep 1194343 = 1791515) B1791515
theorem B21224015 : Blo 1192413 21224015 := bstep (se 1 (by rfl) ⟨15918011, by rfl⟩ : syracuseStep 21224015 = 31836023) B31836023
theorem B3873511 : Blo 1192413 3873511 := bstep (se 1 (by rfl) ⟨2905133, by rfl⟩ : syracuseStep 3873511 = 5810267) B5810267
theorem B7855087 : Blo 1192413 7855087 := bstep (se 1 (by rfl) ⟨5891315, by rfl⟩ : syracuseStep 7855087 = 11782631) B11782631
theorem B2686463 : Blo 1192413 2686463 := bstep (se 1 (by rfl) ⟨2014847, by rfl⟩ : syracuseStep 2686463 = 4029695) B4029695
theorem B124035425 : Blo 1192413 124035425 := bstep (se 2 (by rfl) ⟨46513284, by rfl⟩ : syracuseStep 124035425 = 93026569) B93026569
theorem B167699335 : Blo 1192413 167699335 := bstep (se 1 (by rfl) ⟨125774501, by rfl⟩ : syracuseStep 167699335 = 251549003) B251549003
theorem B14149343 : Blo 1192413 14149343 := bstep (se 1 (by rfl) ⟨10612007, by rfl⟩ : syracuseStep 14149343 = 21224015) B21224015
theorem B13584185 : Blo 1192413 13584185 := bstep (se 2 (by rfl) ⟨5094069, by rfl⟩ : syracuseStep 13584185 = 10188139) B10188139
theorem B5164681 : Blo 1192413 5164681 := bstep (se 2 (by rfl) ⟨1936755, by rfl⟩ : syracuseStep 5164681 = 3873511) B3873511
theorem B10473449 : Blo 1192413 10473449 := bstep (se 2 (by rfl) ⟨3927543, by rfl⟩ : syracuseStep 10473449 = 7855087) B7855087
theorem B1790975 : Blo 1192413 1790975 := bstep (se 1 (by rfl) ⟨1343231, by rfl⟩ : syracuseStep 1790975 = 2686463) B2686463
theorem B2013403 : Blo 1192413 2013403 := bstep (se 1 (by rfl) ⟨1510052, by rfl⟩ : syracuseStep 2013403 = 3020105) B3020105
theorem B130727105 : Blo 1192413 130727105 := bstep (se 2 (by rfl) ⟨49022664, by rfl⟩ : syracuseStep 130727105 = 98045329) B98045329
theorem B82690283 : Blo 1192413 82690283 := bstep (se 1 (by rfl) ⟨62017712, by rfl⟩ : syracuseStep 82690283 = 124035425) B124035425
theorem B27929197 : Blo 1192413 27929197 := bstep (se 3 (by rfl) ⟨5236724, by rfl⟩ : syracuseStep 27929197 = 10473449) B10473449
theorem B9432895 : Blo 1192413 9432895 := bstep (se 1 (by rfl) ⟨7074671, by rfl⟩ : syracuseStep 9432895 = 14149343) B14149343
theorem B9056123 : Blo 1192413 9056123 := bstep (se 1 (by rfl) ⟨6792092, by rfl⟩ : syracuseStep 9056123 = 13584185) B13584185
theorem B87151403 : Blo 1192413 87151403 := bstep (se 1 (by rfl) ⟨65363552, by rfl⟩ : syracuseStep 87151403 = 130727105) B130727105
theorem B6886241 : Blo 1192413 6886241 := bstep (se 2 (by rfl) ⟨2582340, by rfl⟩ : syracuseStep 6886241 = 5164681) B5164681
theorem B2684537 : Blo 1192413 2684537 := bstep (se 2 (by rfl) ⟨1006701, by rfl⟩ : syracuseStep 2684537 = 2013403) B2013403
theorem B1193983 : Blo 1192413 1193983 := bstep (se 1 (by rfl) ⟨895487, by rfl⟩ : syracuseStep 1193983 = 1790975) B1790975
theorem B223599113 : Blo 1192413 223599113 := bstep (se 2 (by rfl) ⟨83849667, by rfl⟩ : syracuseStep 223599113 = 167699335) B167699335
theorem B12577193 : Blo 1192413 12577193 := bstep (se 2 (by rfl) ⟨4716447, by rfl⟩ : syracuseStep 12577193 = 9432895) B9432895
theorem B55126855 : Blo 1192413 55126855 := bstep (se 1 (by rfl) ⟨41345141, by rfl⟩ : syracuseStep 55126855 = 82690283) B82690283
theorem B58100935 : Blo 1192413 58100935 := bstep (se 1 (by rfl) ⟨43575701, by rfl⟩ : syracuseStep 58100935 = 87151403) B87151403
theorem B4590827 : Blo 1192413 4590827 := bstep (se 1 (by rfl) ⟨3443120, by rfl⟩ : syracuseStep 4590827 = 6886241) B6886241
theorem B1789691 : Blo 1192413 1789691 := bstep (se 1 (by rfl) ⟨1342268, by rfl⟩ : syracuseStep 1789691 = 2684537) B2684537
theorem B149066075 : Blo 1192413 149066075 := bstep (se 1 (by rfl) ⟨111799556, by rfl⟩ : syracuseStep 149066075 = 223599113) B223599113
theorem B37238929 : Blo 1192413 37238929 := bstep (se 2 (by rfl) ⟨13964598, by rfl⟩ : syracuseStep 37238929 = 27929197) B27929197
theorem B6037415 : Blo 1192413 6037415 := bstep (se 1 (by rfl) ⟨4528061, by rfl⟩ : syracuseStep 6037415 = 9056123) B9056123
theorem B99377383 : Blo 1192413 99377383 := bstep (se 1 (by rfl) ⟨74533037, by rfl⟩ : syracuseStep 99377383 = 149066075) B149066075
theorem B198607621 : Blo 1192413 198607621 := bstep (se 4 (by rfl) ⟨18619464, by rfl⟩ : syracuseStep 198607621 = 37238929) B37238929
theorem B4024943 : Blo 1192413 4024943 := bstep (se 1 (by rfl) ⟨3018707, by rfl⟩ : syracuseStep 4024943 = 6037415) B6037415
theorem B73502473 : Blo 1192413 73502473 := bstep (se 2 (by rfl) ⟨27563427, by rfl⟩ : syracuseStep 73502473 = 55126855) B55126855
theorem B77467913 : Blo 1192413 77467913 := bstep (se 2 (by rfl) ⟨29050467, by rfl⟩ : syracuseStep 77467913 = 58100935) B58100935
theorem B8384795 : Blo 1192413 8384795 := bstep (se 1 (by rfl) ⟨6288596, by rfl⟩ : syracuseStep 8384795 = 12577193) B12577193
theorem B3060551 : Blo 1192413 3060551 := bstep (se 1 (by rfl) ⟨2295413, by rfl⟩ : syracuseStep 3060551 = 4590827) B4590827
theorem B1193127 : Blo 1192413 1193127 := bstep (se 1 (by rfl) ⟨894845, by rfl⟩ : syracuseStep 1193127 = 1789691) B1789691
theorem B8161469 : Blo 1192413 8161469 := bstep (se 3 (by rfl) ⟨1530275, by rfl⟩ : syracuseStep 8161469 = 3060551) B3060551
theorem B98003297 : Blo 1192413 98003297 := bstep (se 2 (by rfl) ⟨36751236, by rfl⟩ : syracuseStep 98003297 = 73502473) B73502473
theorem B51645275 : Blo 1192413 51645275 := bstep (se 1 (by rfl) ⟨38733956, by rfl⟩ : syracuseStep 51645275 = 77467913) B77467913
theorem B5589863 : Blo 1192413 5589863 := bstep (se 1 (by rfl) ⟨4192397, by rfl⟩ : syracuseStep 5589863 = 8384795) B8384795
theorem B264810161 : Blo 1192413 264810161 := bstep (se 2 (by rfl) ⟨99303810, by rfl⟩ : syracuseStep 264810161 = 198607621) B198607621
theorem B2683295 : Blo 1192413 2683295 := bstep (se 1 (by rfl) ⟨2012471, by rfl⟩ : syracuseStep 2683295 = 4024943) B4024943
theorem B132503177 : Blo 1192413 132503177 := bstep (se 2 (by rfl) ⟨49688691, by rfl⟩ : syracuseStep 132503177 = 99377383) B99377383
theorem B88335451 : Blo 1192413 88335451 := bstep (se 1 (by rfl) ⟨66251588, by rfl⟩ : syracuseStep 88335451 = 132503177) B132503177
theorem B5440979 : Blo 1192413 5440979 := bstep (se 1 (by rfl) ⟨4080734, by rfl⟩ : syracuseStep 5440979 = 8161469) B8161469
theorem B706160429 : Blo 1192413 706160429 := bstep (se 3 (by rfl) ⟨132405080, by rfl⟩ : syracuseStep 706160429 = 264810161) B264810161
theorem B1788863 : Blo 1192413 1788863 := bstep (se 1 (by rfl) ⟨1341647, by rfl⟩ : syracuseStep 1788863 = 2683295) B2683295
theorem B65335531 : Blo 1192413 65335531 := bstep (se 1 (by rfl) ⟨49001648, by rfl⟩ : syracuseStep 65335531 = 98003297) B98003297
theorem B34430183 : Blo 1192413 34430183 := bstep (se 1 (by rfl) ⟨25822637, by rfl⟩ : syracuseStep 34430183 = 51645275) B51645275
theorem B3726575 : Blo 1192413 3726575 := bstep (se 1 (by rfl) ⟨2794931, by rfl⟩ : syracuseStep 3726575 = 5589863) B5589863
theorem B87114041 : Blo 1192413 87114041 := bstep (se 2 (by rfl) ⟨32667765, by rfl⟩ : syracuseStep 87114041 = 65335531) B65335531
theorem B14509277 : Blo 1192413 14509277 := bstep (se 3 (by rfl) ⟨2720489, by rfl⟩ : syracuseStep 14509277 = 5440979) B5440979
theorem B2484383 : Blo 1192413 2484383 := bstep (se 1 (by rfl) ⟨1863287, by rfl⟩ : syracuseStep 2484383 = 3726575) B3726575
theorem B470773619 : Blo 1192413 470773619 := bstep (se 1 (by rfl) ⟨353080214, by rfl⟩ : syracuseStep 470773619 = 706160429) B706160429
theorem B117780601 : Blo 1192413 117780601 := bstep (se 2 (by rfl) ⟨44167725, by rfl⟩ : syracuseStep 117780601 = 88335451) B88335451
theorem B1192575 : Blo 1192413 1192575 := bstep (se 1 (by rfl) ⟨894431, by rfl⟩ : syracuseStep 1192575 = 1788863) B1788863
theorem B22953455 : Blo 1192413 22953455 := bstep (se 1 (by rfl) ⟨17215091, by rfl⟩ : syracuseStep 22953455 = 34430183) B34430183
theorem B157040801 : Blo 1192413 157040801 := bstep (se 2 (by rfl) ⟨58890300, by rfl⟩ : syracuseStep 157040801 = 117780601) B117780601
theorem B58076027 : Blo 1192413 58076027 := bstep (se 1 (by rfl) ⟨43557020, by rfl⟩ : syracuseStep 58076027 = 87114041) B87114041
theorem B313849079 : Blo 1192413 313849079 := bstep (se 1 (by rfl) ⟨235386809, by rfl⟩ : syracuseStep 313849079 = 470773619) B470773619
theorem B9672851 : Blo 1192413 9672851 := bstep (se 1 (by rfl) ⟨7254638, by rfl⟩ : syracuseStep 9672851 = 14509277) B14509277
theorem B26500085 : Blo 1192413 26500085 := bstep (se 5 (by rfl) ⟨1242191, by rfl⟩ : syracuseStep 26500085 = 2484383) B2484383
theorem B15302303 : Blo 1192413 15302303 := bstep (se 1 (by rfl) ⟨11476727, by rfl⟩ : syracuseStep 15302303 = 22953455) B22953455
theorem B104693867 : Blo 1192413 104693867 := bstep (se 1 (by rfl) ⟨78520400, by rfl⟩ : syracuseStep 104693867 = 157040801) B157040801
theorem B209232719 : Blo 1192413 209232719 := bstep (se 1 (by rfl) ⟨156924539, by rfl⟩ : syracuseStep 209232719 = 313849079) B313849079
theorem B6448567 : Blo 1192413 6448567 := bstep (se 1 (by rfl) ⟨4836425, by rfl⟩ : syracuseStep 6448567 = 9672851) B9672851
theorem B38717351 : Blo 1192413 38717351 := bstep (se 1 (by rfl) ⟨29038013, by rfl⟩ : syracuseStep 38717351 = 58076027) B58076027
theorem B10201535 : Blo 1192413 10201535 := bstep (se 1 (by rfl) ⟨7651151, by rfl⟩ : syracuseStep 10201535 = 15302303) B15302303
theorem B17666723 : Blo 1192413 17666723 := bstep (se 1 (by rfl) ⟨13250042, by rfl⟩ : syracuseStep 17666723 = 26500085) B26500085
theorem B69795911 : Blo 1192413 69795911 := bstep (se 1 (by rfl) ⟨52346933, by rfl⟩ : syracuseStep 69795911 = 104693867) B104693867
theorem B6801023 : Blo 1192413 6801023 := bstep (se 1 (by rfl) ⟨5100767, by rfl⟩ : syracuseStep 6801023 = 10201535) B10201535
theorem B139488479 : Blo 1192413 139488479 := bstep (se 1 (by rfl) ⟨104616359, by rfl⟩ : syracuseStep 139488479 = 209232719) B209232719
theorem B8598089 : Blo 1192413 8598089 := bstep (se 2 (by rfl) ⟨3224283, by rfl⟩ : syracuseStep 8598089 = 6448567) B6448567
theorem B11777815 : Blo 1192413 11777815 := bstep (se 1 (by rfl) ⟨8833361, by rfl⟩ : syracuseStep 11777815 = 17666723) B17666723
theorem B25811567 : Blo 1192413 25811567 := bstep (se 1 (by rfl) ⟨19358675, by rfl⟩ : syracuseStep 25811567 = 38717351) B38717351
theorem B46530607 : Blo 1192413 46530607 := bstep (se 1 (by rfl) ⟨34897955, by rfl⟩ : syracuseStep 46530607 = 69795911) B69795911
theorem B4534015 : Blo 1192413 4534015 := bstep (se 1 (by rfl) ⟨3400511, by rfl⟩ : syracuseStep 4534015 = 6801023) B6801023
theorem B17207711 : Blo 1192413 17207711 := bstep (se 1 (by rfl) ⟨12905783, by rfl⟩ : syracuseStep 17207711 = 25811567) B25811567
theorem B92992319 : Blo 1192413 92992319 := bstep (se 1 (by rfl) ⟨69744239, by rfl⟩ : syracuseStep 92992319 = 139488479) B139488479
theorem B5732059 : Blo 1192413 5732059 := bstep (se 1 (by rfl) ⟨4299044, by rfl⟩ : syracuseStep 5732059 = 8598089) B8598089
theorem B15703753 : Blo 1192413 15703753 := bstep (se 2 (by rfl) ⟨5888907, by rfl⟩ : syracuseStep 15703753 = 11777815) B11777815
theorem B62040809 : Blo 1192413 62040809 := bstep (se 2 (by rfl) ⟨23265303, by rfl⟩ : syracuseStep 62040809 = 46530607) B46530607
theorem B11471807 : Blo 1192413 11471807 := bstep (se 1 (by rfl) ⟨8603855, by rfl⟩ : syracuseStep 11471807 = 17207711) B17207711
theorem B61994879 : Blo 1192413 61994879 := bstep (se 1 (by rfl) ⟨46496159, by rfl⟩ : syracuseStep 61994879 = 92992319) B92992319
theorem B20938337 : Blo 1192413 20938337 := bstep (se 2 (by rfl) ⟨7851876, by rfl⟩ : syracuseStep 20938337 = 15703753) B15703753
theorem B7642745 : Blo 1192413 7642745 := bstep (se 2 (by rfl) ⟨2866029, by rfl⟩ : syracuseStep 7642745 = 5732059) B5732059
theorem B6045353 : Blo 1192413 6045353 := bstep (se 2 (by rfl) ⟨2267007, by rfl⟩ : syracuseStep 6045353 = 4534015) B4534015
theorem B41329919 : Blo 1192413 41329919 := bstep (se 1 (by rfl) ⟨30997439, by rfl⟩ : syracuseStep 41329919 = 61994879) B61994879
theorem B7647871 : Blo 1192413 7647871 := bstep (se 1 (by rfl) ⟨5735903, by rfl⟩ : syracuseStep 7647871 = 11471807) B11471807
theorem B41360539 : Blo 1192413 41360539 := bstep (se 1 (by rfl) ⟨31020404, by rfl⟩ : syracuseStep 41360539 = 62040809) B62040809
theorem B13958891 : Blo 1192413 13958891 := bstep (se 1 (by rfl) ⟨10469168, by rfl⟩ : syracuseStep 13958891 = 20938337) B20938337
theorem B5095163 : Blo 1192413 5095163 := bstep (se 1 (by rfl) ⟨3821372, by rfl⟩ : syracuseStep 5095163 = 7642745) B7642745
theorem B4030235 : Blo 1192413 4030235 := bstep (se 1 (by rfl) ⟨3022676, by rfl⟩ : syracuseStep 4030235 = 6045353) B6045353
theorem B27553279 : Blo 1192413 27553279 := bstep (se 1 (by rfl) ⟨20664959, by rfl⟩ : syracuseStep 27553279 = 41329919) B41329919
theorem B13587101 : Blo 1192413 13587101 := bstep (se 3 (by rfl) ⟨2547581, by rfl⟩ : syracuseStep 13587101 = 5095163) B5095163
theorem B10197161 : Blo 1192413 10197161 := bstep (se 2 (by rfl) ⟨3823935, by rfl⟩ : syracuseStep 10197161 = 7647871) B7647871
theorem B55147385 : Blo 1192413 55147385 := bstep (se 2 (by rfl) ⟨20680269, by rfl⟩ : syracuseStep 55147385 = 41360539) B41360539
theorem B9305927 : Blo 1192413 9305927 := bstep (se 1 (by rfl) ⟨6979445, by rfl⟩ : syracuseStep 9305927 = 13958891) B13958891
theorem B2686823 : Blo 1192413 2686823 := bstep (se 1 (by rfl) ⟨2015117, by rfl⟩ : syracuseStep 2686823 = 4030235) B4030235
theorem B6203951 : Blo 1192413 6203951 := bstep (se 1 (by rfl) ⟨4652963, by rfl⟩ : syracuseStep 6203951 = 9305927) B9305927
theorem B36737705 : Blo 1192413 36737705 := bstep (se 2 (by rfl) ⟨13776639, by rfl⟩ : syracuseStep 36737705 = 27553279) B27553279
theorem B1791215 : Blo 1192413 1791215 := bstep (se 1 (by rfl) ⟨1343411, by rfl⟩ : syracuseStep 1791215 = 2686823) B2686823
theorem B9058067 : Blo 1192413 9058067 := bstep (se 1 (by rfl) ⟨6793550, by rfl⟩ : syracuseStep 9058067 = 13587101) B13587101
theorem B6798107 : Blo 1192413 6798107 := bstep (se 1 (by rfl) ⟨5098580, by rfl⟩ : syracuseStep 6798107 = 10197161) B10197161
theorem B36764923 : Blo 1192413 36764923 := bstep (se 1 (by rfl) ⟨27573692, by rfl⟩ : syracuseStep 36764923 = 55147385) B55147385
theorem B6038711 : Blo 1192413 6038711 := bstep (se 1 (by rfl) ⟨4529033, by rfl⟩ : syracuseStep 6038711 = 9058067) B9058067
theorem B4532071 : Blo 1192413 4532071 := bstep (se 1 (by rfl) ⟨3399053, by rfl⟩ : syracuseStep 4532071 = 6798107) B6798107
theorem B24491803 : Blo 1192413 24491803 := bstep (se 1 (by rfl) ⟨18368852, by rfl⟩ : syracuseStep 24491803 = 36737705) B36737705
theorem B1194143 : Blo 1192413 1194143 := bstep (se 1 (by rfl) ⟨895607, by rfl⟩ : syracuseStep 1194143 = 1791215) B1791215
theorem B49019897 : Blo 1192413 49019897 := bstep (se 2 (by rfl) ⟨18382461, by rfl⟩ : syracuseStep 49019897 = 36764923) B36764923
theorem B4135967 : Blo 1192413 4135967 := bstep (se 1 (by rfl) ⟨3101975, by rfl⟩ : syracuseStep 4135967 = 6203951) B6203951
theorem B32679931 : Blo 1192413 32679931 := bstep (se 1 (by rfl) ⟨24509948, by rfl⟩ : syracuseStep 32679931 = 49019897) B49019897
theorem B32655737 : Blo 1192413 32655737 := bstep (se 2 (by rfl) ⟨12245901, by rfl⟩ : syracuseStep 32655737 = 24491803) B24491803
theorem B4025807 : Blo 1192413 4025807 := bstep (se 1 (by rfl) ⟨3019355, by rfl⟩ : syracuseStep 4025807 = 6038711) B6038711
theorem B2757311 : Blo 1192413 2757311 := bstep (se 1 (by rfl) ⟨2067983, by rfl⟩ : syracuseStep 2757311 = 4135967) B4135967
theorem B6042761 : Blo 1192413 6042761 := bstep (se 2 (by rfl) ⟨2266035, by rfl⟩ : syracuseStep 6042761 = 4532071) B4532071
theorem B43573241 : Blo 1192413 43573241 := bstep (se 2 (by rfl) ⟨16339965, by rfl⟩ : syracuseStep 43573241 = 32679931) B32679931
theorem B1838207 : Blo 1192413 1838207 := bstep (se 1 (by rfl) ⟨1378655, by rfl⟩ : syracuseStep 1838207 = 2757311) B2757311
theorem B21770491 : Blo 1192413 21770491 := bstep (se 1 (by rfl) ⟨16327868, by rfl⟩ : syracuseStep 21770491 = 32655737) B32655737
theorem B2683871 : Blo 1192413 2683871 := bstep (se 1 (by rfl) ⟨2012903, by rfl⟩ : syracuseStep 2683871 = 4025807) B4025807
theorem B4028507 : Blo 1192413 4028507 := bstep (se 1 (by rfl) ⟨3021380, by rfl⟩ : syracuseStep 4028507 = 6042761) B6042761
theorem B29027321 : Blo 1192413 29027321 := bstep (se 2 (by rfl) ⟨10885245, by rfl⟩ : syracuseStep 29027321 = 21770491) B21770491
theorem B4901885 : Blo 1192413 4901885 := bstep (se 3 (by rfl) ⟨919103, by rfl⟩ : syracuseStep 4901885 = 1838207) B1838207
theorem B1789247 : Blo 1192413 1789247 := bstep (se 1 (by rfl) ⟨1341935, by rfl⟩ : syracuseStep 1789247 = 2683871) B2683871
theorem B29048827 : Blo 1192413 29048827 := bstep (se 1 (by rfl) ⟨21786620, by rfl⟩ : syracuseStep 29048827 = 43573241) B43573241
theorem B2685671 : Blo 1192413 2685671 := bstep (se 1 (by rfl) ⟨2014253, by rfl⟩ : syracuseStep 2685671 = 4028507) B4028507
theorem B19351547 : Blo 1192413 19351547 := bstep (se 1 (by rfl) ⟨14513660, by rfl⟩ : syracuseStep 19351547 = 29027321) B29027321
theorem B1790447 : Blo 1192413 1790447 := bstep (se 1 (by rfl) ⟨1342835, by rfl⟩ : syracuseStep 1790447 = 2685671) B2685671
theorem B1192831 : Blo 1192413 1192831 := bstep (se 1 (by rfl) ⟨894623, by rfl⟩ : syracuseStep 1192831 = 1789247) B1789247
theorem B3267923 : Blo 1192413 3267923 := bstep (se 1 (by rfl) ⟨2450942, by rfl⟩ : syracuseStep 3267923 = 4901885) B4901885
theorem B38731769 : Blo 1192413 38731769 := bstep (se 2 (by rfl) ⟨14524413, by rfl⟩ : syracuseStep 38731769 = 29048827) B29048827
theorem B1193631 : Blo 1192413 1193631 := bstep (se 1 (by rfl) ⟨895223, by rfl⟩ : syracuseStep 1193631 = 1790447) B1790447
theorem B8714461 : Blo 1192413 8714461 := bstep (se 3 (by rfl) ⟨1633961, by rfl⟩ : syracuseStep 8714461 = 3267923) B3267923
theorem B12901031 : Blo 1192413 12901031 := bstep (se 1 (by rfl) ⟨9675773, by rfl⟩ : syracuseStep 12901031 = 19351547) B19351547
theorem B25821179 : Blo 1192413 25821179 := bstep (se 1 (by rfl) ⟨19365884, by rfl⟩ : syracuseStep 25821179 = 38731769) B38731769
theorem B17214119 : Blo 1192413 17214119 := bstep (se 1 (by rfl) ⟨12910589, by rfl⟩ : syracuseStep 17214119 = 25821179) B25821179
theorem B11619281 : Blo 1192413 11619281 := bstep (se 2 (by rfl) ⟨4357230, by rfl⟩ : syracuseStep 11619281 = 8714461) B8714461
theorem B8600687 : Blo 1192413 8600687 := bstep (se 1 (by rfl) ⟨6450515, by rfl⟩ : syracuseStep 8600687 = 12901031) B12901031
theorem B7746187 : Blo 1192413 7746187 := bstep (se 1 (by rfl) ⟨5809640, by rfl⟩ : syracuseStep 7746187 = 11619281) B11619281
theorem B11476079 : Blo 1192413 11476079 := bstep (se 1 (by rfl) ⟨8607059, by rfl⟩ : syracuseStep 11476079 = 17214119) B17214119
theorem B5733791 : Blo 1192413 5733791 := bstep (se 1 (by rfl) ⟨4300343, by rfl⟩ : syracuseStep 5733791 = 8600687) B8600687
theorem B3822527 : Blo 1192413 3822527 := bstep (se 1 (by rfl) ⟨2866895, by rfl⟩ : syracuseStep 3822527 = 5733791) B5733791
theorem B10328249 : Blo 1192413 10328249 := bstep (se 2 (by rfl) ⟨3873093, by rfl⟩ : syracuseStep 10328249 = 7746187) B7746187
theorem B7650719 : Blo 1192413 7650719 := bstep (se 1 (by rfl) ⟨5738039, by rfl⟩ : syracuseStep 7650719 = 11476079) B11476079
theorem B27541997 : Blo 1192413 27541997 := bstep (se 3 (by rfl) ⟨5164124, by rfl⟩ : syracuseStep 27541997 = 10328249) B10328249
theorem B2548351 : Blo 1192413 2548351 := bstep (se 1 (by rfl) ⟨1911263, by rfl⟩ : syracuseStep 2548351 = 3822527) B3822527
theorem B5100479 : Blo 1192413 5100479 := bstep (se 1 (by rfl) ⟨3825359, by rfl⟩ : syracuseStep 5100479 = 7650719) B7650719
theorem B3400319 : Blo 1192413 3400319 := bstep (se 1 (by rfl) ⟨2550239, by rfl⟩ : syracuseStep 3400319 = 5100479) B5100479
theorem B18361331 : Blo 1192413 18361331 := bstep (se 1 (by rfl) ⟨13770998, by rfl⟩ : syracuseStep 18361331 = 27541997) B27541997
theorem B3397801 : Blo 1192413 3397801 := bstep (se 2 (by rfl) ⟨1274175, by rfl⟩ : syracuseStep 3397801 = 2548351) B2548351
theorem B4530401 : Blo 1192413 4530401 := bstep (se 2 (by rfl) ⟨1698900, by rfl⟩ : syracuseStep 4530401 = 3397801) B3397801
theorem B12240887 : Blo 1192413 12240887 := bstep (se 1 (by rfl) ⟨9180665, by rfl⟩ : syracuseStep 12240887 = 18361331) B18361331
theorem B2266879 : Blo 1192413 2266879 := bstep (se 1 (by rfl) ⟨1700159, by rfl⟩ : syracuseStep 2266879 = 3400319) B3400319
theorem B32642365 : Blo 1192413 32642365 := bstep (se 3 (by rfl) ⟨6120443, by rfl⟩ : syracuseStep 32642365 = 12240887) B12240887
theorem B3020267 : Blo 1192413 3020267 := bstep (se 1 (by rfl) ⟨2265200, by rfl⟩ : syracuseStep 3020267 = 4530401) B4530401
theorem B3022505 : Blo 1192413 3022505 := bstep (se 2 (by rfl) ⟨1133439, by rfl⟩ : syracuseStep 3022505 = 2266879) B2266879
theorem B2013511 : Blo 1192413 2013511 := bstep (se 1 (by rfl) ⟨1510133, by rfl⟩ : syracuseStep 2013511 = 3020267) B3020267
theorem B43523153 : Blo 1192413 43523153 := bstep (se 2 (by rfl) ⟨16321182, by rfl⟩ : syracuseStep 43523153 = 32642365) B32642365
theorem B2015003 : Blo 1192413 2015003 := bstep (se 1 (by rfl) ⟨1511252, by rfl⟩ : syracuseStep 2015003 = 3022505) B3022505
theorem B2684681 : Blo 1192413 2684681 := bstep (se 2 (by rfl) ⟨1006755, by rfl⟩ : syracuseStep 2684681 = 2013511) B2013511
theorem B29015435 : Blo 1192413 29015435 := bstep (se 1 (by rfl) ⟨21761576, by rfl⟩ : syracuseStep 29015435 = 43523153) B43523153
theorem B1343335 : Blo 1192413 1343335 := bstep (se 1 (by rfl) ⟨1007501, by rfl⟩ : syracuseStep 1343335 = 2015003) B2015003
theorem B19343623 : Blo 1192413 19343623 := bstep (se 1 (by rfl) ⟨14507717, by rfl⟩ : syracuseStep 19343623 = 29015435) B29015435
theorem B1789787 : Blo 1192413 1789787 := bstep (se 1 (by rfl) ⟨1342340, by rfl⟩ : syracuseStep 1789787 = 2684681) B2684681
theorem B1791113 : Blo 1192413 1791113 := bstep (se 2 (by rfl) ⟨671667, by rfl⟩ : syracuseStep 1791113 = 1343335) B1343335
theorem B25791497 : Blo 1192413 25791497 := bstep (se 2 (by rfl) ⟨9671811, by rfl⟩ : syracuseStep 25791497 = 19343623) B19343623
theorem B1193191 : Blo 1192413 1193191 := bstep (se 1 (by rfl) ⟨894893, by rfl⟩ : syracuseStep 1193191 = 1789787) B1789787
theorem B1194075 : Blo 1192413 1194075 := bstep (se 1 (by rfl) ⟨895556, by rfl⟩ : syracuseStep 1194075 = 1791113) B1791113
theorem B17194331 : Blo 1192413 17194331 := bstep (se 1 (by rfl) ⟨12895748, by rfl⟩ : syracuseStep 17194331 = 25791497) B25791497
theorem B11462887 : Blo 1192413 11462887 := bstep (se 1 (by rfl) ⟨8597165, by rfl⟩ : syracuseStep 11462887 = 17194331) B17194331
theorem B15283849 : Blo 1192413 15283849 := bstep (se 2 (by rfl) ⟨5731443, by rfl⟩ : syracuseStep 15283849 = 11462887) B11462887
theorem B20378465 : Blo 1192413 20378465 := bstep (se 2 (by rfl) ⟨7641924, by rfl⟩ : syracuseStep 20378465 = 15283849) B15283849
theorem B13585643 : Blo 1192413 13585643 := bstep (se 1 (by rfl) ⟨10189232, by rfl⟩ : syracuseStep 13585643 = 20378465) B20378465
theorem B9057095 : Blo 1192413 9057095 := bstep (se 1 (by rfl) ⟨6792821, by rfl⟩ : syracuseStep 9057095 = 13585643) B13585643
theorem B6038063 : Blo 1192413 6038063 := bstep (se 1 (by rfl) ⟨4528547, by rfl⟩ : syracuseStep 6038063 = 9057095) B9057095
theorem B4025375 : Blo 1192413 4025375 := bstep (se 1 (by rfl) ⟨3019031, by rfl⟩ : syracuseStep 4025375 = 6038063) B6038063
theorem B2683583 : Blo 1192413 2683583 := bstep (se 1 (by rfl) ⟨2012687, by rfl⟩ : syracuseStep 2683583 = 4025375) B4025375
theorem B1789055 : Blo 1192413 1789055 := bstep (se 1 (by rfl) ⟨1341791, by rfl⟩ : syracuseStep 1789055 = 2683583) B2683583
theorem B1192703 : Blo 1192413 1192703 := bstep (se 1 (by rfl) ⟨894527, by rfl⟩ : syracuseStep 1192703 = 1789055) B1789055

theorem C0 (j : ℕ) (h1 : 298103 ≤ j) (h2 : j ≤ 298602) : Blo 1192413 (4 * j + 3) := by
  interval_cases j
  · exact B1192415
  · exact B1192419
  · exact B1192423
  · exact B1192427
  · exact B1192431
  · exact B1192435
  · exact B1192439
  · exact B1192443
  · exact B1192447
  · exact B1192451
  · exact B1192455
  · exact B1192459
  · exact B1192463
  · exact B1192467
  · exact B1192471
  · exact B1192475
  · exact B1192479
  · exact B1192483
  · exact B1192487
  · exact B1192491
  · exact B1192495
  · exact B1192499
  · exact B1192503
  · exact B1192507
  · exact B1192511
  · exact B1192515
  · exact B1192519
  · exact B1192523
  · exact B1192527
  · exact B1192531
  · exact B1192535
  · exact B1192539
  · exact B1192543
  · exact B1192547
  · exact B1192551
  · exact B1192555
  · exact B1192559
  · exact B1192563
  · exact B1192567
  · exact B1192571
  · exact B1192575
  · exact B1192579
  · exact B1192583
  · exact B1192587
  · exact B1192591
  · exact B1192595
  · exact B1192599
  · exact B1192603
  · exact B1192607
  · exact B1192611
  · exact B1192615
  · exact B1192619
  · exact B1192623
  · exact B1192627
  · exact B1192631
  · exact B1192635
  · exact B1192639
  · exact B1192643
  · exact B1192647
  · exact B1192651
  · exact B1192655
  · exact B1192659
  · exact B1192663
  · exact B1192667
  · exact B1192671
  · exact B1192675
  · exact B1192679
  · exact B1192683
  · exact B1192687
  · exact B1192691
  · exact B1192695
  · exact B1192699
  · exact B1192703
  · exact B1192707
  · exact B1192711
  · exact B1192715
  · exact B1192719
  · exact B1192723
  · exact B1192727
  · exact B1192731
  · exact B1192735
  · exact B1192739
  · exact B1192743
  · exact B1192747
  · exact B1192751
  · exact B1192755
  · exact B1192759
  · exact B1192763
  · exact B1192767
  · exact B1192771
  · exact B1192775
  · exact B1192779
  · exact B1192783
  · exact B1192787
  · exact B1192791
  · exact B1192795
  · exact B1192799
  · exact B1192803
  · exact B1192807
  · exact B1192811
  · exact B1192815
  · exact B1192819
  · exact B1192823
  · exact B1192827
  · exact B1192831
  · exact B1192835
  · exact B1192839
  · exact B1192843
  · exact B1192847
  · exact B1192851
  · exact B1192855
  · exact B1192859
  · exact B1192863
  · exact B1192867
  · exact B1192871
  · exact B1192875
  · exact B1192879
  · exact B1192883
  · exact B1192887
  · exact B1192891
  · exact B1192895
  · exact B1192899
  · exact B1192903
  · exact B1192907
  · exact B1192911
  · exact B1192915
  · exact B1192919
  · exact B1192923
  · exact B1192927
  · exact B1192931
  · exact B1192935
  · exact B1192939
  · exact B1192943
  · exact B1192947
  · exact B1192951
  · exact B1192955
  · exact B1192959
  · exact B1192963
  · exact B1192967
  · exact B1192971
  · exact B1192975
  · exact B1192979
  · exact B1192983
  · exact B1192987
  · exact B1192991
  · exact B1192995
  · exact B1192999
  · exact B1193003
  · exact B1193007
  · exact B1193011
  · exact B1193015
  · exact B1193019
  · exact B1193023
  · exact B1193027
  · exact B1193031
  · exact B1193035
  · exact B1193039
  · exact B1193043
  · exact B1193047
  · exact B1193051
  · exact B1193055
  · exact B1193059
  · exact B1193063
  · exact B1193067
  · exact B1193071
  · exact B1193075
  · exact B1193079
  · exact B1193083
  · exact B1193087
  · exact B1193091
  · exact B1193095
  · exact B1193099
  · exact B1193103
  · exact B1193107
  · exact B1193111
  · exact B1193115
  · exact B1193119
  · exact B1193123
  · exact B1193127
  · exact B1193131
  · exact B1193135
  · exact B1193139
  · exact B1193143
  · exact B1193147
  · exact B1193151
  · exact B1193155
  · exact B1193159
  · exact B1193163
  · exact B1193167
  · exact B1193171
  · exact B1193175
  · exact B1193179
  · exact B1193183
  · exact B1193187
  · exact B1193191
  · exact B1193195
  · exact B1193199
  · exact B1193203
  · exact B1193207
  · exact B1193211
  · exact B1193215
  · exact B1193219
  · exact B1193223
  · exact B1193227
  · exact B1193231
  · exact B1193235
  · exact B1193239
  · exact B1193243
  · exact B1193247
  · exact B1193251
  · exact B1193255
  · exact B1193259
  · exact B1193263
  · exact B1193267
  · exact B1193271
  · exact B1193275
  · exact B1193279
  · exact B1193283
  · exact B1193287
  · exact B1193291
  · exact B1193295
  · exact B1193299
  · exact B1193303
  · exact B1193307
  · exact B1193311
  · exact B1193315
  · exact B1193319
  · exact B1193323
  · exact B1193327
  · exact B1193331
  · exact B1193335
  · exact B1193339
  · exact B1193343
  · exact B1193347
  · exact B1193351
  · exact B1193355
  · exact B1193359
  · exact B1193363
  · exact B1193367
  · exact B1193371
  · exact B1193375
  · exact B1193379
  · exact B1193383
  · exact B1193387
  · exact B1193391
  · exact B1193395
  · exact B1193399
  · exact B1193403
  · exact B1193407
  · exact B1193411
  · exact B1193415
  · exact B1193419
  · exact B1193423
  · exact B1193427
  · exact B1193431
  · exact B1193435
  · exact B1193439
  · exact B1193443
  · exact B1193447
  · exact B1193451
  · exact B1193455
  · exact B1193459
  · exact B1193463
  · exact B1193467
  · exact B1193471
  · exact B1193475
  · exact B1193479
  · exact B1193483
  · exact B1193487
  · exact B1193491
  · exact B1193495
  · exact B1193499
  · exact B1193503
  · exact B1193507
  · exact B1193511
  · exact B1193515
  · exact B1193519
  · exact B1193523
  · exact B1193527
  · exact B1193531
  · exact B1193535
  · exact B1193539
  · exact B1193543
  · exact B1193547
  · exact B1193551
  · exact B1193555
  · exact B1193559
  · exact B1193563
  · exact B1193567
  · exact B1193571
  · exact B1193575
  · exact B1193579
  · exact B1193583
  · exact B1193587
  · exact B1193591
  · exact B1193595
  · exact B1193599
  · exact B1193603
  · exact B1193607
  · exact B1193611
  · exact B1193615
  · exact B1193619
  · exact B1193623
  · exact B1193627
  · exact B1193631
  · exact B1193635
  · exact B1193639
  · exact B1193643
  · exact B1193647
  · exact B1193651
  · exact B1193655
  · exact B1193659
  · exact B1193663
  · exact B1193667
  · exact B1193671
  · exact B1193675
  · exact B1193679
  · exact B1193683
  · exact B1193687
  · exact B1193691
  · exact B1193695
  · exact B1193699
  · exact B1193703
  · exact B1193707
  · exact B1193711
  · exact B1193715
  · exact B1193719
  · exact B1193723
  · exact B1193727
  · exact B1193731
  · exact B1193735
  · exact B1193739
  · exact B1193743
  · exact B1193747
  · exact B1193751
  · exact B1193755
  · exact B1193759
  · exact B1193763
  · exact B1193767
  · exact B1193771
  · exact B1193775
  · exact B1193779
  · exact B1193783
  · exact B1193787
  · exact B1193791
  · exact B1193795
  · exact B1193799
  · exact B1193803
  · exact B1193807
  · exact B1193811
  · exact B1193815
  · exact B1193819
  · exact B1193823
  · exact B1193827
  · exact B1193831
  · exact B1193835
  · exact B1193839
  · exact B1193843
  · exact B1193847
  · exact B1193851
  · exact B1193855
  · exact B1193859
  · exact B1193863
  · exact B1193867
  · exact B1193871
  · exact B1193875
  · exact B1193879
  · exact B1193883
  · exact B1193887
  · exact B1193891
  · exact B1193895
  · exact B1193899
  · exact B1193903
  · exact B1193907
  · exact B1193911
  · exact B1193915
  · exact B1193919
  · exact B1193923
  · exact B1193927
  · exact B1193931
  · exact B1193935
  · exact B1193939
  · exact B1193943
  · exact B1193947
  · exact B1193951
  · exact B1193955
  · exact B1193959
  · exact B1193963
  · exact B1193967
  · exact B1193971
  · exact B1193975
  · exact B1193979
  · exact B1193983
  · exact B1193987
  · exact B1193991
  · exact B1193995
  · exact B1193999
  · exact B1194003
  · exact B1194007
  · exact B1194011
  · exact B1194015
  · exact B1194019
  · exact B1194023
  · exact B1194027
  · exact B1194031
  · exact B1194035
  · exact B1194039
  · exact B1194043
  · exact B1194047
  · exact B1194051
  · exact B1194055
  · exact B1194059
  · exact B1194063
  · exact B1194067
  · exact B1194071
  · exact B1194075
  · exact B1194079
  · exact B1194083
  · exact B1194087
  · exact B1194091
  · exact B1194095
  · exact B1194099
  · exact B1194103
  · exact B1194107
  · exact B1194111
  · exact B1194115
  · exact B1194119
  · exact B1194123
  · exact B1194127
  · exact B1194131
  · exact B1194135
  · exact B1194139
  · exact B1194143
  · exact B1194147
  · exact B1194151
  · exact B1194155
  · exact B1194159
  · exact B1194163
  · exact B1194167
  · exact B1194171
  · exact B1194175
  · exact B1194179
  · exact B1194183
  · exact B1194187
  · exact B1194191
  · exact B1194195
  · exact B1194199
  · exact B1194203
  · exact B1194207
  · exact B1194211
  · exact B1194215
  · exact B1194219
  · exact B1194223
  · exact B1194227
  · exact B1194231
  · exact B1194235
  · exact B1194239
  · exact B1194243
  · exact B1194247
  · exact B1194251
  · exact B1194255
  · exact B1194259
  · exact B1194263
  · exact B1194267
  · exact B1194271
  · exact B1194275
  · exact B1194279
  · exact B1194283
  · exact B1194287
  · exact B1194291
  · exact B1194295
  · exact B1194299
  · exact B1194303
  · exact B1194307
  · exact B1194311
  · exact B1194315
  · exact B1194319
  · exact B1194323
  · exact B1194327
  · exact B1194331
  · exact B1194335
  · exact B1194339
  · exact B1194343
  · exact B1194347
  · exact B1194351
  · exact B1194355
  · exact B1194359
  · exact B1194363
  · exact B1194367
  · exact B1194371
  · exact B1194375
  · exact B1194379
  · exact B1194383
  · exact B1194387
  · exact B1194391
  · exact B1194395
  · exact B1194399
  · exact B1194403
  · exact B1194407
  · exact B1194411

theorem solution (m : ℕ) (hlo : 1192413 ≤ m) (hhi : m ≤ 1194413) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 298103 ≤ j := by omega
    have hj2 : j ≤ 298602 := by omega
    have hb : Blo 1192413 (4 * j + 3) := by
      exact C0 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
