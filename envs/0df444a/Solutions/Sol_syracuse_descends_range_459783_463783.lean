-- Prove2me | solution 1 for syracuse_descends_range_459783_463783
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-09T17:48:01.515883+00:00
-- url     : https://prove2.me/submissions/ea09d6e7-2ee6-4bd1-bff0-bacba77a81fa

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


theorem B983117 : Blo 459783 983117 := bbase (se 3 (by rfl) ⟨184334, by rfl⟩ : syracuseStep 983117 = 368669) (by norm_num)
theorem B983125 : Blo 459783 983125 := bbase (se 8 (by rfl) ⟨5760, by rfl⟩ : syracuseStep 983125 = 11521) (by norm_num)
theorem B4259957 : Blo 459783 4259957 := bbase (se 5 (by rfl) ⟨199685, by rfl⟩ : syracuseStep 4259957 = 399371) (by norm_num)
theorem B2228485 : Blo 459783 2228485 := bbase (se 4 (by rfl) ⟨208920, by rfl⟩ : syracuseStep 2228485 = 417841) (by norm_num)
theorem B1311061 : Blo 459783 1311061 := bbase (se 10 (by rfl) ⟨1920, by rfl⟩ : syracuseStep 1311061 = 3841) (by norm_num)
theorem B1245557 : Blo 459783 1245557 := bbase (se 5 (by rfl) ⟨58385, by rfl⟩ : syracuseStep 1245557 = 116771) (by norm_num)
theorem B655781 : Blo 459783 655781 := bbase (se 4 (by rfl) ⟨61479, by rfl⟩ : syracuseStep 655781 = 122959) (by norm_num)
theorem B786869 : Blo 459783 786869 := bbase (se 5 (by rfl) ⟨36884, by rfl⟩ : syracuseStep 786869 = 73769) (by norm_num)
theorem B3735989 : Blo 459783 3735989 := bbase (se 5 (by rfl) ⟨175124, by rfl⟩ : syracuseStep 3735989 = 350249) (by norm_num)
theorem B1311221 : Blo 459783 1311221 := bbase (se 5 (by rfl) ⟨61463, by rfl⟩ : syracuseStep 1311221 = 122927) (by norm_num)
theorem B492041 : Blo 459783 492041 := bbase (se 2 (by rfl) ⟨184515, by rfl⟩ : syracuseStep 492041 = 369031) (by norm_num)
theorem B7111253 : Blo 459783 7111253 := bbase (se 8 (by rfl) ⟨41667, by rfl⟩ : syracuseStep 7111253 = 83335) (by norm_num)
theorem B950933 : Blo 459783 950933 := bbase (se 6 (by rfl) ⟨22287, by rfl⟩ : syracuseStep 950933 = 44575) (by norm_num)
theorem B1311461 : Blo 459783 1311461 := bbase (se 4 (by rfl) ⟨122949, by rfl⟩ : syracuseStep 1311461 = 245899) (by norm_num)
theorem B1966933 : Blo 459783 1966933 := bbase (se 9 (by rfl) ⟨5762, by rfl⟩ : syracuseStep 1966933 = 11525) (by norm_num)
theorem B5276501 : Blo 459783 5276501 := bbase (se 9 (by rfl) ⟨15458, by rfl⟩ : syracuseStep 5276501 = 30917) (by norm_num)
theorem B1311653 : Blo 459783 1311653 := bbase (se 4 (by rfl) ⟨122967, by rfl⟩ : syracuseStep 1311653 = 245935) (by norm_num)
theorem B492485 : Blo 459783 492485 := bbase (se 4 (by rfl) ⟨46170, by rfl⟩ : syracuseStep 492485 = 92341) (by norm_num)
theorem B1180757 : Blo 459783 1180757 := bbase (se 8 (by rfl) ⟨6918, by rfl⟩ : syracuseStep 1180757 = 13837) (by norm_num)
theorem B656533 : Blo 459783 656533 := bbase (se 6 (by rfl) ⟨15387, by rfl⟩ : syracuseStep 656533 = 30775) (by norm_num)
theorem B1475765 : Blo 459783 1475765 := bbase (se 5 (by rfl) ⟨69176, by rfl⟩ : syracuseStep 1475765 = 138353) (by norm_num)
theorem B984253 : Blo 459783 984253 := bbase (se 3 (by rfl) ⟨184547, by rfl⟩ : syracuseStep 984253 = 369095) (by norm_num)
theorem B492733 : Blo 459783 492733 := bbase (se 3 (by rfl) ⟨92387, by rfl⟩ : syracuseStep 492733 = 184775) (by norm_num)
theorem B623821 : Blo 459783 623821 := bbase (se 3 (by rfl) ⟨116966, by rfl⟩ : syracuseStep 623821 = 233933) (by norm_num)
theorem B885997 : Blo 459783 885997 := bbase (se 3 (by rfl) ⟨166124, by rfl⟩ : syracuseStep 885997 = 332249) (by norm_num)
theorem B591157 : Blo 459783 591157 := bbase (se 5 (by rfl) ⟨27710, by rfl⟩ : syracuseStep 591157 = 55421) (by norm_num)
theorem B689693 : Blo 459783 689693 := bbase (se 3 (by rfl) ⟨129317, by rfl⟩ : syracuseStep 689693 = 258635) (by norm_num)
theorem B2328101 : Blo 459783 2328101 := bbase (se 4 (by rfl) ⟨218259, by rfl⟩ : syracuseStep 2328101 = 436519) (by norm_num)
theorem B689717 : Blo 459783 689717 := bbase (se 5 (by rfl) ⟨32330, by rfl⟩ : syracuseStep 689717 = 64661) (by norm_num)
theorem B984629 : Blo 459783 984629 := bbase (se 5 (by rfl) ⟨46154, by rfl⟩ : syracuseStep 984629 = 92309) (by norm_num)
theorem B689741 : Blo 459783 689741 := bbase (se 3 (by rfl) ⟨129326, by rfl⟩ : syracuseStep 689741 = 258653) (by norm_num)
theorem B624205 : Blo 459783 624205 := bbase (se 3 (by rfl) ⟨117038, by rfl⟩ : syracuseStep 624205 = 234077) (by norm_num)
theorem B689765 : Blo 459783 689765 := bbase (se 4 (by rfl) ⟨64665, by rfl⟩ : syracuseStep 689765 = 129331) (by norm_num)
theorem B493165 : Blo 459783 493165 := bbase (se 3 (by rfl) ⟨92468, by rfl⟩ : syracuseStep 493165 = 184937) (by norm_num)
theorem B689789 : Blo 459783 689789 := bbase (se 3 (by rfl) ⟨129335, by rfl⟩ : syracuseStep 689789 = 258671) (by norm_num)
theorem B689813 : Blo 459783 689813 := bbase (se 6 (by rfl) ⟨16167, by rfl⟩ : syracuseStep 689813 = 32335) (by norm_num)
theorem B689837 : Blo 459783 689837 := bbase (se 3 (by rfl) ⟨129344, by rfl⟩ : syracuseStep 689837 = 258689) (by norm_num)
theorem B493237 : Blo 459783 493237 := bbase (se 5 (by rfl) ⟨23120, by rfl⟩ : syracuseStep 493237 = 46241) (by norm_num)
theorem B689861 : Blo 459783 689861 := bbase (se 4 (by rfl) ⟨64674, by rfl⟩ : syracuseStep 689861 = 129349) (by norm_num)
theorem B689885 : Blo 459783 689885 := bbase (se 3 (by rfl) ⟨129353, by rfl⟩ : syracuseStep 689885 = 258707) (by norm_num)
theorem B1181405 : Blo 459783 1181405 := bbase (se 3 (by rfl) ⟨221513, by rfl⟩ : syracuseStep 1181405 = 443027) (by norm_num)
theorem B689909 : Blo 459783 689909 := bbase (se 5 (by rfl) ⟨32339, by rfl⟩ : syracuseStep 689909 = 64679) (by norm_num)
theorem B689933 : Blo 459783 689933 := bbase (se 3 (by rfl) ⟨129362, by rfl⟩ : syracuseStep 689933 = 258725) (by norm_num)
theorem B689957 : Blo 459783 689957 := bbase (se 4 (by rfl) ⟨64683, by rfl⟩ : syracuseStep 689957 = 129367) (by norm_num)
theorem B689981 : Blo 459783 689981 := bbase (se 3 (by rfl) ⟨129371, by rfl⟩ : syracuseStep 689981 = 258743) (by norm_num)
theorem B690005 : Blo 459783 690005 := bbase (se 9 (by rfl) ⟨2021, by rfl⟩ : syracuseStep 690005 = 4043) (by norm_num)
theorem B690029 : Blo 459783 690029 := bbase (se 3 (by rfl) ⟨129380, by rfl⟩ : syracuseStep 690029 = 258761) (by norm_num)
theorem B690053 : Blo 459783 690053 := bbase (se 4 (by rfl) ⟨64692, by rfl⟩ : syracuseStep 690053 = 129385) (by norm_num)
theorem B1312645 : Blo 459783 1312645 := bbase (se 4 (by rfl) ⟨123060, by rfl⟩ : syracuseStep 1312645 = 246121) (by norm_num)
theorem B690077 : Blo 459783 690077 := bbase (se 3 (by rfl) ⟨129389, by rfl⟩ : syracuseStep 690077 = 258779) (by norm_num)
theorem B657325 : Blo 459783 657325 := bbase (se 3 (by rfl) ⟨123248, by rfl⟩ : syracuseStep 657325 = 246497) (by norm_num)
theorem B690101 : Blo 459783 690101 := bbase (se 5 (by rfl) ⟨32348, by rfl⟩ : syracuseStep 690101 = 64697) (by norm_num)
theorem B690125 : Blo 459783 690125 := bbase (se 3 (by rfl) ⟨129398, by rfl⟩ : syracuseStep 690125 = 258797) (by norm_num)
theorem B690149 : Blo 459783 690149 := bbase (se 4 (by rfl) ⟨64701, by rfl⟩ : syracuseStep 690149 = 129403) (by norm_num)
theorem B690173 : Blo 459783 690173 := bbase (se 3 (by rfl) ⟨129407, by rfl⟩ : syracuseStep 690173 = 258815) (by norm_num)
theorem B690197 : Blo 459783 690197 := bbase (se 6 (by rfl) ⟨16176, by rfl⟩ : syracuseStep 690197 = 32353) (by norm_num)
theorem B493609 : Blo 459783 493609 := bbase (se 2 (by rfl) ⟨185103, by rfl⟩ : syracuseStep 493609 = 370207) (by norm_num)
theorem B690221 : Blo 459783 690221 := bbase (se 3 (by rfl) ⟨129416, by rfl⟩ : syracuseStep 690221 = 258833) (by norm_num)
theorem B526381 : Blo 459783 526381 := bbase (se 3 (by rfl) ⟨98696, by rfl⟩ : syracuseStep 526381 = 197393) (by norm_num)
theorem B690245 : Blo 459783 690245 := bbase (se 4 (by rfl) ⟨64710, by rfl⟩ : syracuseStep 690245 = 129421) (by norm_num)
theorem B690269 : Blo 459783 690269 := bbase (se 3 (by rfl) ⟨129425, by rfl⟩ : syracuseStep 690269 = 258851) (by norm_num)
theorem B690293 : Blo 459783 690293 := bbase (se 5 (by rfl) ⟨32357, by rfl⟩ : syracuseStep 690293 = 64715) (by norm_num)
theorem B952445 : Blo 459783 952445 := bbase (se 3 (by rfl) ⟨178583, by rfl⟩ : syracuseStep 952445 = 357167) (by norm_num)
theorem B690317 : Blo 459783 690317 := bbase (se 3 (by rfl) ⟨129434, by rfl⟩ : syracuseStep 690317 = 258869) (by norm_num)
theorem B690341 : Blo 459783 690341 := bbase (se 4 (by rfl) ⟨64719, by rfl⟩ : syracuseStep 690341 = 129439) (by norm_num)
theorem B690365 : Blo 459783 690365 := bbase (se 3 (by rfl) ⟨129443, by rfl⟩ : syracuseStep 690365 = 258887) (by norm_num)
theorem B690389 : Blo 459783 690389 := bbase (se 7 (by rfl) ⟨8090, by rfl⟩ : syracuseStep 690389 = 16181) (by norm_num)
theorem B1870037 : Blo 459783 1870037 := bbase (se 7 (by rfl) ⟨21914, by rfl⟩ : syracuseStep 1870037 = 43829) (by norm_num)
theorem B690413 : Blo 459783 690413 := bbase (se 3 (by rfl) ⟨129452, by rfl⟩ : syracuseStep 690413 = 258905) (by norm_num)
theorem B657661 : Blo 459783 657661 := bbase (se 3 (by rfl) ⟨123311, by rfl⟩ : syracuseStep 657661 = 246623) (by norm_num)
theorem B690437 : Blo 459783 690437 := bbase (se 4 (by rfl) ⟨64728, by rfl⟩ : syracuseStep 690437 = 129457) (by norm_num)
theorem B690461 : Blo 459783 690461 := bbase (se 3 (by rfl) ⟨129461, by rfl⟩ : syracuseStep 690461 = 258923) (by norm_num)
theorem B1968421 : Blo 459783 1968421 := bbase (se 4 (by rfl) ⟨184539, by rfl⟩ : syracuseStep 1968421 = 369079) (by norm_num)
theorem B690485 : Blo 459783 690485 := bbase (se 5 (by rfl) ⟨32366, by rfl⟩ : syracuseStep 690485 = 64733) (by norm_num)
theorem B1968437 : Blo 459783 1968437 := bbase (se 5 (by rfl) ⟨92270, by rfl⟩ : syracuseStep 1968437 = 184541) (by norm_num)
theorem B690509 : Blo 459783 690509 := bbase (se 3 (by rfl) ⟨129470, by rfl⟩ : syracuseStep 690509 = 258941) (by norm_num)
theorem B690533 : Blo 459783 690533 := bbase (se 4 (by rfl) ⟨64737, by rfl⟩ : syracuseStep 690533 = 129475) (by norm_num)
theorem B2394485 : Blo 459783 2394485 := bbase (se 5 (by rfl) ⟨112241, by rfl⟩ : syracuseStep 2394485 = 224483) (by norm_num)
theorem B690557 : Blo 459783 690557 := bbase (se 3 (by rfl) ⟨129479, by rfl⟩ : syracuseStep 690557 = 258959) (by norm_num)
theorem B690581 : Blo 459783 690581 := bbase (se 6 (by rfl) ⟨16185, by rfl⟩ : syracuseStep 690581 = 32371) (by norm_num)
theorem B493985 : Blo 459783 493985 := bbase (se 2 (by rfl) ⟨185244, by rfl⟩ : syracuseStep 493985 = 370489) (by norm_num)
theorem B690605 : Blo 459783 690605 := bbase (se 3 (by rfl) ⟨129488, by rfl⟩ : syracuseStep 690605 = 258977) (by norm_num)
theorem B1477045 : Blo 459783 1477045 := bbase (se 5 (by rfl) ⟨69236, by rfl⟩ : syracuseStep 1477045 = 138473) (by norm_num)
theorem B690629 : Blo 459783 690629 := bbase (se 4 (by rfl) ⟨64746, by rfl⟩ : syracuseStep 690629 = 129493) (by norm_num)
theorem B1051093 : Blo 459783 1051093 := bbase (se 7 (by rfl) ⟨12317, by rfl⟩ : syracuseStep 1051093 = 24635) (by norm_num)
theorem B657877 : Blo 459783 657877 := bbase (se 7 (by rfl) ⟨7709, by rfl⟩ : syracuseStep 657877 = 15419) (by norm_num)
theorem B690653 : Blo 459783 690653 := bbase (se 3 (by rfl) ⟨129497, by rfl⟩ : syracuseStep 690653 = 258995) (by norm_num)
theorem B494057 : Blo 459783 494057 := bbase (se 2 (by rfl) ⟨185271, by rfl⟩ : syracuseStep 494057 = 370543) (by norm_num)
theorem B690677 : Blo 459783 690677 := bbase (se 5 (by rfl) ⟨32375, by rfl⟩ : syracuseStep 690677 = 64751) (by norm_num)
theorem B690701 : Blo 459783 690701 := bbase (se 3 (by rfl) ⟨129506, by rfl⟩ : syracuseStep 690701 = 259013) (by norm_num)
theorem B690725 : Blo 459783 690725 := bbase (se 4 (by rfl) ⟨64755, by rfl⟩ : syracuseStep 690725 = 129511) (by norm_num)
theorem B690749 : Blo 459783 690749 := bbase (se 3 (by rfl) ⟨129515, by rfl⟩ : syracuseStep 690749 = 259031) (by norm_num)
theorem B690773 : Blo 459783 690773 := bbase (se 8 (by rfl) ⟨4047, by rfl⟩ : syracuseStep 690773 = 8095) (by norm_num)
theorem B526933 : Blo 459783 526933 := bbase (se 8 (by rfl) ⟨3087, by rfl⟩ : syracuseStep 526933 = 6175) (by norm_num)
theorem B789085 : Blo 459783 789085 := bbase (se 3 (by rfl) ⟨147953, by rfl⟩ : syracuseStep 789085 = 295907) (by norm_num)
theorem B690797 : Blo 459783 690797 := bbase (se 3 (by rfl) ⟨129524, by rfl⟩ : syracuseStep 690797 = 259049) (by norm_num)
theorem B690821 : Blo 459783 690821 := bbase (se 4 (by rfl) ⟨64764, by rfl⟩ : syracuseStep 690821 = 129529) (by norm_num)
theorem B690845 : Blo 459783 690845 := bbase (se 3 (by rfl) ⟨129533, by rfl⟩ : syracuseStep 690845 = 259067) (by norm_num)
theorem B494245 : Blo 459783 494245 := bbase (se 4 (by rfl) ⟨46335, by rfl⟩ : syracuseStep 494245 = 92671) (by norm_num)
theorem B690869 : Blo 459783 690869 := bbase (se 5 (by rfl) ⟨32384, by rfl⟩ : syracuseStep 690869 = 64769) (by norm_num)
theorem B690893 : Blo 459783 690893 := bbase (se 3 (by rfl) ⟨129542, by rfl⟩ : syracuseStep 690893 = 259085) (by norm_num)
theorem B625357 : Blo 459783 625357 := bbase (se 3 (by rfl) ⟨117254, by rfl⟩ : syracuseStep 625357 = 234509) (by norm_num)
theorem B690917 : Blo 459783 690917 := bbase (se 4 (by rfl) ⟨64773, by rfl⟩ : syracuseStep 690917 = 129547) (by norm_num)
theorem B690941 : Blo 459783 690941 := bbase (se 3 (by rfl) ⟨129551, by rfl⟩ : syracuseStep 690941 = 259103) (by norm_num)
theorem B690965 : Blo 459783 690965 := bbase (se 6 (by rfl) ⟨16194, by rfl⟩ : syracuseStep 690965 = 32389) (by norm_num)
theorem B690989 : Blo 459783 690989 := bbase (se 3 (by rfl) ⟨129560, by rfl⟩ : syracuseStep 690989 = 259121) (by norm_num)
theorem B2329397 : Blo 459783 2329397 := bbase (se 5 (by rfl) ⟨109190, by rfl⟩ : syracuseStep 2329397 = 218381) (by norm_num)
theorem B2624309 : Blo 459783 2624309 := bbase (se 5 (by rfl) ⟨123014, by rfl⟩ : syracuseStep 2624309 = 246029) (by norm_num)
theorem B4000565 : Blo 459783 4000565 := bbase (se 5 (by rfl) ⟨187526, by rfl⟩ : syracuseStep 4000565 = 375053) (by norm_num)
theorem B691013 : Blo 459783 691013 := bbase (se 4 (by rfl) ⟨64782, by rfl⟩ : syracuseStep 691013 = 129565) (by norm_num)
theorem B658253 : Blo 459783 658253 := bbase (se 3 (by rfl) ⟨123422, by rfl⟩ : syracuseStep 658253 = 246845) (by norm_num)
theorem B691037 : Blo 459783 691037 := bbase (se 3 (by rfl) ⟨129569, by rfl⟩ : syracuseStep 691037 = 259139) (by norm_num)
theorem B494429 : Blo 459783 494429 := bbase (se 3 (by rfl) ⟨92705, by rfl⟩ : syracuseStep 494429 = 185411) (by norm_num)
theorem B691061 : Blo 459783 691061 := bbase (se 5 (by rfl) ⟨32393, by rfl⟩ : syracuseStep 691061 = 64787) (by norm_num)
theorem B691085 : Blo 459783 691085 := bbase (se 3 (by rfl) ⟨129578, by rfl⟩ : syracuseStep 691085 = 259157) (by norm_num)
theorem B691109 : Blo 459783 691109 := bbase (se 4 (by rfl) ⟨64791, by rfl⟩ : syracuseStep 691109 = 129583) (by norm_num)
theorem B691133 : Blo 459783 691133 := bbase (se 3 (by rfl) ⟨129587, by rfl⟩ : syracuseStep 691133 = 259175) (by norm_num)
theorem B691157 : Blo 459783 691157 := bbase (se 7 (by rfl) ⟨8099, by rfl⟩ : syracuseStep 691157 = 16199) (by norm_num)
theorem B1313749 : Blo 459783 1313749 := bbase (se 7 (by rfl) ⟨15395, by rfl⟩ : syracuseStep 1313749 = 30791) (by norm_num)
theorem B691181 : Blo 459783 691181 := bbase (se 3 (by rfl) ⟨129596, by rfl⟩ : syracuseStep 691181 = 259193) (by norm_num)
theorem B691205 : Blo 459783 691205 := bbase (se 4 (by rfl) ⟨64800, by rfl⟩ : syracuseStep 691205 = 129601) (by norm_num)
theorem B691229 : Blo 459783 691229 := bbase (se 3 (by rfl) ⟨129605, by rfl⟩ : syracuseStep 691229 = 259211) (by norm_num)
theorem B691253 : Blo 459783 691253 := bbase (se 5 (by rfl) ⟨32402, by rfl⟩ : syracuseStep 691253 = 64805) (by norm_num)
theorem B691277 : Blo 459783 691277 := bbase (se 3 (by rfl) ⟨129614, by rfl⟩ : syracuseStep 691277 = 259229) (by norm_num)
theorem B691301 : Blo 459783 691301 := bbase (se 4 (by rfl) ⟨64809, by rfl⟩ : syracuseStep 691301 = 129619) (by norm_num)
theorem B691325 : Blo 459783 691325 := bbase (se 3 (by rfl) ⟨129623, by rfl⟩ : syracuseStep 691325 = 259247) (by norm_num)
theorem B691349 : Blo 459783 691349 := bbase (se 6 (by rfl) ⟨16203, by rfl⟩ : syracuseStep 691349 = 32407) (by norm_num)
theorem B986269 : Blo 459783 986269 := bbase (se 3 (by rfl) ⟨184925, by rfl⟩ : syracuseStep 986269 = 369851) (by norm_num)
theorem B691373 : Blo 459783 691373 := bbase (se 3 (by rfl) ⟨129632, by rfl⟩ : syracuseStep 691373 = 259265) (by norm_num)
theorem B691397 : Blo 459783 691397 := bbase (se 4 (by rfl) ⟨64818, by rfl⟩ : syracuseStep 691397 = 129637) (by norm_num)
theorem B691421 : Blo 459783 691421 := bbase (se 3 (by rfl) ⟨129641, by rfl⟩ : syracuseStep 691421 = 259283) (by norm_num)
theorem B691445 : Blo 459783 691445 := bbase (se 5 (by rfl) ⟨32411, by rfl⟩ : syracuseStep 691445 = 64823) (by norm_num)
theorem B691469 : Blo 459783 691469 := bbase (se 3 (by rfl) ⟨129650, by rfl⟩ : syracuseStep 691469 = 259301) (by norm_num)
theorem B691493 : Blo 459783 691493 := bbase (se 4 (by rfl) ⟨64827, by rfl⟩ : syracuseStep 691493 = 129655) (by norm_num)
theorem B691517 : Blo 459783 691517 := bbase (se 3 (by rfl) ⟨129659, by rfl⟩ : syracuseStep 691517 = 259319) (by norm_num)
theorem B691541 : Blo 459783 691541 := bbase (se 11 (by rfl) ⟨506, by rfl⟩ : syracuseStep 691541 = 1013) (by norm_num)
theorem B691565 : Blo 459783 691565 := bbase (se 3 (by rfl) ⟨129668, by rfl⟩ : syracuseStep 691565 = 259337) (by norm_num)
theorem B691589 : Blo 459783 691589 := bbase (se 4 (by rfl) ⟨64836, by rfl⟩ : syracuseStep 691589 = 129673) (by norm_num)
theorem B691613 : Blo 459783 691613 := bbase (se 3 (by rfl) ⟨129677, by rfl⟩ : syracuseStep 691613 = 259355) (by norm_num)
theorem B691637 : Blo 459783 691637 := bbase (se 5 (by rfl) ⟨32420, by rfl⟩ : syracuseStep 691637 = 64841) (by norm_num)
theorem B691661 : Blo 459783 691661 := bbase (se 3 (by rfl) ⟨129686, by rfl⟩ : syracuseStep 691661 = 259373) (by norm_num)
theorem B691685 : Blo 459783 691685 := bbase (se 4 (by rfl) ⟨64845, by rfl⟩ : syracuseStep 691685 = 129691) (by norm_num)
theorem B2100725 : Blo 459783 2100725 := bbase (se 5 (by rfl) ⟨98471, by rfl⟩ : syracuseStep 2100725 = 196943) (by norm_num)
theorem B691709 : Blo 459783 691709 := bbase (se 3 (by rfl) ⟨129695, by rfl⟩ : syracuseStep 691709 = 259391) (by norm_num)
theorem B691733 : Blo 459783 691733 := bbase (se 6 (by rfl) ⟨16212, by rfl⟩ : syracuseStep 691733 = 32425) (by norm_num)
theorem B691757 : Blo 459783 691757 := bbase (se 3 (by rfl) ⟨129704, by rfl⟩ : syracuseStep 691757 = 259409) (by norm_num)
theorem B691781 : Blo 459783 691781 := bbase (se 4 (by rfl) ⟨64854, by rfl⟩ : syracuseStep 691781 = 129709) (by norm_num)
theorem B495181 : Blo 459783 495181 := bbase (se 3 (by rfl) ⟨92846, by rfl⟩ : syracuseStep 495181 = 185693) (by norm_num)
theorem B1248853 : Blo 459783 1248853 := bbase (se 8 (by rfl) ⟨7317, by rfl⟩ : syracuseStep 1248853 = 14635) (by norm_num)
theorem B691805 : Blo 459783 691805 := bbase (se 3 (by rfl) ⟨129713, by rfl⟩ : syracuseStep 691805 = 259427) (by norm_num)
theorem B691829 : Blo 459783 691829 := bbase (se 5 (by rfl) ⟨32429, by rfl⟩ : syracuseStep 691829 = 64859) (by norm_num)
theorem B691853 : Blo 459783 691853 := bbase (se 3 (by rfl) ⟨129722, by rfl⟩ : syracuseStep 691853 = 259445) (by norm_num)
theorem B495253 : Blo 459783 495253 := bbase (se 6 (by rfl) ⟨11607, by rfl⟩ : syracuseStep 495253 = 23215) (by norm_num)
theorem B691877 : Blo 459783 691877 := bbase (se 4 (by rfl) ⟨64863, by rfl⟩ : syracuseStep 691877 = 129727) (by norm_num)
theorem B691901 : Blo 459783 691901 := bbase (se 3 (by rfl) ⟨129731, by rfl⟩ : syracuseStep 691901 = 259463) (by norm_num)
theorem B691925 : Blo 459783 691925 := bbase (se 7 (by rfl) ⟨8108, by rfl⟩ : syracuseStep 691925 = 16217) (by norm_num)
theorem B691949 : Blo 459783 691949 := bbase (se 3 (by rfl) ⟨129740, by rfl⟩ : syracuseStep 691949 = 259481) (by norm_num)
theorem B691973 : Blo 459783 691973 := bbase (se 4 (by rfl) ⟨64872, by rfl⟩ : syracuseStep 691973 = 129745) (by norm_num)
theorem B1478405 : Blo 459783 1478405 := bbase (se 4 (by rfl) ⟨138600, by rfl⟩ : syracuseStep 1478405 = 277201) (by norm_num)
theorem B691997 : Blo 459783 691997 := bbase (se 3 (by rfl) ⟨129749, by rfl⟩ : syracuseStep 691997 = 259499) (by norm_num)
theorem B528157 : Blo 459783 528157 := bbase (se 3 (by rfl) ⟨99029, by rfl⟩ : syracuseStep 528157 = 198059) (by norm_num)
theorem B3936053 : Blo 459783 3936053 := bbase (se 5 (by rfl) ⟨184502, by rfl⟩ : syracuseStep 3936053 = 369005) (by norm_num)
theorem B692021 : Blo 459783 692021 := bbase (se 5 (by rfl) ⟨32438, by rfl⟩ : syracuseStep 692021 = 64877) (by norm_num)
theorem B560953 : Blo 459783 560953 := bbase (se 2 (by rfl) ⟨210357, by rfl⟩ : syracuseStep 560953 = 420715) (by norm_num)
theorem B692045 : Blo 459783 692045 := bbase (se 3 (by rfl) ⟨129758, by rfl⟩ : syracuseStep 692045 = 259517) (by norm_num)
theorem B1740629 : Blo 459783 1740629 := bbase (se 9 (by rfl) ⟨5099, by rfl⟩ : syracuseStep 1740629 = 10199) (by norm_num)
theorem B1183589 : Blo 459783 1183589 := bbase (se 4 (by rfl) ⟨110961, by rfl⟩ : syracuseStep 1183589 = 221923) (by norm_num)
theorem B692069 : Blo 459783 692069 := bbase (se 4 (by rfl) ⟨64881, by rfl⟩ : syracuseStep 692069 = 129763) (by norm_num)
theorem B790373 : Blo 459783 790373 := bbase (se 4 (by rfl) ⟨74097, by rfl⟩ : syracuseStep 790373 = 148195) (by norm_num)
theorem B692093 : Blo 459783 692093 := bbase (se 3 (by rfl) ⟨129767, by rfl⟩ : syracuseStep 692093 = 259535) (by norm_num)
theorem B626557 : Blo 459783 626557 := bbase (se 3 (by rfl) ⟨117479, by rfl⟩ : syracuseStep 626557 = 234959) (by norm_num)
theorem B1478533 : Blo 459783 1478533 := bbase (se 4 (by rfl) ⟨138612, by rfl⟩ : syracuseStep 1478533 = 277225) (by norm_num)
theorem B1249157 : Blo 459783 1249157 := bbase (se 4 (by rfl) ⟨117108, by rfl⟩ : syracuseStep 1249157 = 234217) (by norm_num)
theorem B692117 : Blo 459783 692117 := bbase (se 6 (by rfl) ⟨16221, by rfl⟩ : syracuseStep 692117 = 32443) (by norm_num)
theorem B692141 : Blo 459783 692141 := bbase (se 3 (by rfl) ⟨129776, by rfl⟩ : syracuseStep 692141 = 259553) (by norm_num)
theorem B692165 : Blo 459783 692165 := bbase (se 4 (by rfl) ⟨64890, by rfl⟩ : syracuseStep 692165 = 129781) (by norm_num)
theorem B2625493 : Blo 459783 2625493 := bbase (se 7 (by rfl) ⟨30767, by rfl⟩ : syracuseStep 2625493 = 61535) (by norm_num)
theorem B692189 : Blo 459783 692189 := bbase (se 3 (by rfl) ⟨129785, by rfl⟩ : syracuseStep 692189 = 259571) (by norm_num)
theorem B692213 : Blo 459783 692213 := bbase (se 5 (by rfl) ⟨32447, by rfl⟩ : syracuseStep 692213 = 64895) (by norm_num)
theorem B593929 : Blo 459783 593929 := bbase (se 2 (by rfl) ⟨222723, by rfl⟩ : syracuseStep 593929 = 445447) (by norm_num)
theorem B692237 : Blo 459783 692237 := bbase (se 3 (by rfl) ⟨129794, by rfl⟩ : syracuseStep 692237 = 259589) (by norm_num)
theorem B987157 : Blo 459783 987157 := bbase (se 6 (by rfl) ⟨23136, by rfl⟩ : syracuseStep 987157 = 46273) (by norm_num)
theorem B692261 : Blo 459783 692261 := bbase (se 4 (by rfl) ⟨64899, by rfl⟩ : syracuseStep 692261 = 129799) (by norm_num)
theorem B692285 : Blo 459783 692285 := bbase (se 3 (by rfl) ⟨129803, by rfl⟩ : syracuseStep 692285 = 259607) (by norm_num)
theorem B2330693 : Blo 459783 2330693 := bbase (se 4 (by rfl) ⟨218502, by rfl⟩ : syracuseStep 2330693 = 437005) (by norm_num)
theorem B594001 : Blo 459783 594001 := bbase (se 2 (by rfl) ⟨222750, by rfl⟩ : syracuseStep 594001 = 445501) (by norm_num)
theorem B692309 : Blo 459783 692309 := bbase (se 8 (by rfl) ⟨4056, by rfl⟩ : syracuseStep 692309 = 8113) (by norm_num)
theorem B692333 : Blo 459783 692333 := bbase (se 3 (by rfl) ⟨129812, by rfl⟩ : syracuseStep 692333 = 259625) (by norm_num)
theorem B692357 : Blo 459783 692357 := bbase (se 4 (by rfl) ⟨64908, by rfl⟩ : syracuseStep 692357 = 129817) (by norm_num)
theorem B1478789 : Blo 459783 1478789 := bbase (se 4 (by rfl) ⟨138636, by rfl⟩ : syracuseStep 1478789 = 277273) (by norm_num)
theorem B692381 : Blo 459783 692381 := bbase (se 3 (by rfl) ⟨129821, by rfl⟩ : syracuseStep 692381 = 259643) (by norm_num)
theorem B692405 : Blo 459783 692405 := bbase (se 5 (by rfl) ⟨32456, by rfl⟩ : syracuseStep 692405 = 64913) (by norm_num)
theorem B692429 : Blo 459783 692429 := bbase (se 3 (by rfl) ⟨129830, by rfl⟩ : syracuseStep 692429 = 259661) (by norm_num)
theorem B8523989 : Blo 459783 8523989 := bbase (se 7 (by rfl) ⟨99890, by rfl⟩ : syracuseStep 8523989 = 199781) (by norm_num)
theorem B659677 : Blo 459783 659677 := bbase (se 3 (by rfl) ⟨123689, by rfl⟩ : syracuseStep 659677 = 247379) (by norm_num)
theorem B692453 : Blo 459783 692453 := bbase (se 4 (by rfl) ⟨64917, by rfl⟩ : syracuseStep 692453 = 129835) (by norm_num)
theorem B692477 : Blo 459783 692477 := bbase (se 3 (by rfl) ⟨129839, by rfl⟩ : syracuseStep 692477 = 259679) (by norm_num)
theorem B692501 : Blo 459783 692501 := bbase (se 6 (by rfl) ⟨16230, by rfl⟩ : syracuseStep 692501 = 32461) (by norm_num)
theorem B692525 : Blo 459783 692525 := bbase (se 3 (by rfl) ⟨129848, by rfl⟩ : syracuseStep 692525 = 259697) (by norm_num)
theorem B692549 : Blo 459783 692549 := bbase (se 4 (by rfl) ⟨64926, by rfl⟩ : syracuseStep 692549 = 129853) (by norm_num)
theorem B692573 : Blo 459783 692573 := bbase (se 3 (by rfl) ⟨129857, by rfl⟩ : syracuseStep 692573 = 259715) (by norm_num)
theorem B692597 : Blo 459783 692597 := bbase (se 5 (by rfl) ⟨32465, by rfl⟩ : syracuseStep 692597 = 64931) (by norm_num)
theorem B692621 : Blo 459783 692621 := bbase (se 3 (by rfl) ⟨129866, by rfl⟩ : syracuseStep 692621 = 259733) (by norm_num)
theorem B692645 : Blo 459783 692645 := bbase (se 4 (by rfl) ⟨64935, by rfl⟩ : syracuseStep 692645 = 129871) (by norm_num)
theorem B1315253 : Blo 459783 1315253 := bbase (se 5 (by rfl) ⟨61652, by rfl⟩ : syracuseStep 1315253 = 123305) (by norm_num)
theorem B1249717 : Blo 459783 1249717 := bbase (se 5 (by rfl) ⟨58580, by rfl⟩ : syracuseStep 1249717 = 117161) (by norm_num)
theorem B692669 : Blo 459783 692669 := bbase (se 3 (by rfl) ⟨129875, by rfl⟩ : syracuseStep 692669 = 259751) (by norm_num)
theorem B692693 : Blo 459783 692693 := bbase (se 7 (by rfl) ⟨8117, by rfl⟩ : syracuseStep 692693 = 16235) (by norm_num)
theorem B692717 : Blo 459783 692717 := bbase (se 3 (by rfl) ⟨129884, by rfl⟩ : syracuseStep 692717 = 259769) (by norm_num)
theorem B594421 : Blo 459783 594421 := bbase (se 5 (by rfl) ⟨27863, by rfl⟩ : syracuseStep 594421 = 55727) (by norm_num)
theorem B1970693 : Blo 459783 1970693 := bbase (se 4 (by rfl) ⟨184752, by rfl⟩ : syracuseStep 1970693 = 369505) (by norm_num)
theorem B692741 : Blo 459783 692741 := bbase (se 4 (by rfl) ⟨64944, by rfl⟩ : syracuseStep 692741 = 129889) (by norm_num)
theorem B987653 : Blo 459783 987653 := bbase (se 4 (by rfl) ⟨92592, by rfl⟩ : syracuseStep 987653 = 185185) (by norm_num)
theorem B692765 : Blo 459783 692765 := bbase (se 3 (by rfl) ⟨129893, by rfl⟩ : syracuseStep 692765 = 259787) (by norm_num)
theorem B692789 : Blo 459783 692789 := bbase (se 5 (by rfl) ⟨32474, by rfl⟩ : syracuseStep 692789 = 64949) (by norm_num)
theorem B692813 : Blo 459783 692813 := bbase (se 3 (by rfl) ⟨129902, by rfl⟩ : syracuseStep 692813 = 259805) (by norm_num)
theorem B692837 : Blo 459783 692837 := bbase (se 4 (by rfl) ⟨64953, by rfl⟩ : syracuseStep 692837 = 129907) (by norm_num)
theorem B692861 : Blo 459783 692861 := bbase (se 3 (by rfl) ⟨129911, by rfl⟩ : syracuseStep 692861 = 259823) (by norm_num)
theorem B692885 : Blo 459783 692885 := bbase (se 6 (by rfl) ⟨16239, by rfl⟩ : syracuseStep 692885 = 32479) (by norm_num)
theorem B692909 : Blo 459783 692909 := bbase (se 3 (by rfl) ⟨129920, by rfl⟩ : syracuseStep 692909 = 259841) (by norm_num)
theorem B692933 : Blo 459783 692933 := bbase (se 4 (by rfl) ⟨64962, by rfl⟩ : syracuseStep 692933 = 129925) (by norm_num)
theorem B692957 : Blo 459783 692957 := bbase (se 3 (by rfl) ⟨129929, by rfl⟩ : syracuseStep 692957 = 259859) (by norm_num)
theorem B692981 : Blo 459783 692981 := bbase (se 5 (by rfl) ⟨32483, by rfl⟩ : syracuseStep 692981 = 64967) (by norm_num)
theorem B693005 : Blo 459783 693005 := bbase (se 3 (by rfl) ⟨129938, by rfl⟩ : syracuseStep 693005 = 259877) (by norm_num)
theorem B693029 : Blo 459783 693029 := bbase (se 4 (by rfl) ⟨64971, by rfl⟩ : syracuseStep 693029 = 129943) (by norm_num)
theorem B660269 : Blo 459783 660269 := bbase (se 3 (by rfl) ⟨123800, by rfl⟩ : syracuseStep 660269 = 247601) (by norm_num)
theorem B693053 : Blo 459783 693053 := bbase (se 3 (by rfl) ⟨129947, by rfl⟩ : syracuseStep 693053 = 259895) (by norm_num)
theorem B2954069 : Blo 459783 2954069 := bbase (se 9 (by rfl) ⟨8654, by rfl⟩ : syracuseStep 2954069 = 17309) (by norm_num)
theorem B693077 : Blo 459783 693077 := bbase (se 9 (by rfl) ⟨2030, by rfl⟩ : syracuseStep 693077 = 4061) (by norm_num)
theorem B693101 : Blo 459783 693101 := bbase (se 3 (by rfl) ⟨129956, by rfl⟩ : syracuseStep 693101 = 259913) (by norm_num)
theorem B660349 : Blo 459783 660349 := bbase (se 3 (by rfl) ⟨123815, by rfl⟩ : syracuseStep 660349 = 247631) (by norm_num)
theorem B693125 : Blo 459783 693125 := bbase (se 4 (by rfl) ⟨64980, by rfl⟩ : syracuseStep 693125 = 129961) (by norm_num)
theorem B693149 : Blo 459783 693149 := bbase (se 3 (by rfl) ⟨129965, by rfl⟩ : syracuseStep 693149 = 259931) (by norm_num)
theorem B693173 : Blo 459783 693173 := bbase (se 5 (by rfl) ⟨32492, by rfl⟩ : syracuseStep 693173 = 64985) (by norm_num)
theorem B693197 : Blo 459783 693197 := bbase (se 3 (by rfl) ⟨129974, by rfl⟩ : syracuseStep 693197 = 259949) (by norm_num)
theorem B4985813 : Blo 459783 4985813 := bbase (se 7 (by rfl) ⟨58427, by rfl⟩ : syracuseStep 4985813 = 116855) (by norm_num)
theorem B693221 : Blo 459783 693221 := bbase (se 4 (by rfl) ⟨64989, by rfl⟩ : syracuseStep 693221 = 129979) (by norm_num)
theorem B693245 : Blo 459783 693245 := bbase (se 3 (by rfl) ⟨129983, by rfl⟩ : syracuseStep 693245 = 259967) (by norm_num)
theorem B693269 : Blo 459783 693269 := bbase (se 6 (by rfl) ⟨16248, by rfl⟩ : syracuseStep 693269 = 32497) (by norm_num)
theorem B693293 : Blo 459783 693293 := bbase (se 3 (by rfl) ⟨129992, by rfl⟩ : syracuseStep 693293 = 259985) (by norm_num)
theorem B3511349 : Blo 459783 3511349 := bbase (se 5 (by rfl) ⟨164594, by rfl⟩ : syracuseStep 3511349 = 329189) (by norm_num)
theorem B693317 : Blo 459783 693317 := bbase (se 4 (by rfl) ⟨64998, by rfl⟩ : syracuseStep 693317 = 129997) (by norm_num)
theorem B693341 : Blo 459783 693341 := bbase (se 3 (by rfl) ⟨130001, by rfl⟩ : syracuseStep 693341 = 260003) (by norm_num)
theorem B693365 : Blo 459783 693365 := bbase (se 5 (by rfl) ⟨32501, by rfl⟩ : syracuseStep 693365 = 65003) (by norm_num)
theorem B693389 : Blo 459783 693389 := bbase (se 3 (by rfl) ⟨130010, by rfl⟩ : syracuseStep 693389 = 260021) (by norm_num)
theorem B693413 : Blo 459783 693413 := bbase (se 4 (by rfl) ⟨65007, by rfl⟩ : syracuseStep 693413 = 130015) (by norm_num)
theorem B693437 : Blo 459783 693437 := bbase (se 3 (by rfl) ⟨130019, by rfl⟩ : syracuseStep 693437 = 260039) (by norm_num)
theorem B693461 : Blo 459783 693461 := bbase (se 7 (by rfl) ⟨8126, by rfl⟩ : syracuseStep 693461 = 16253) (by norm_num)
theorem B693485 : Blo 459783 693485 := bbase (se 3 (by rfl) ⟨130028, by rfl⟩ : syracuseStep 693485 = 260057) (by norm_num)
theorem B791797 : Blo 459783 791797 := bbase (se 5 (by rfl) ⟨37115, by rfl⟩ : syracuseStep 791797 = 74231) (by norm_num)
theorem B693509 : Blo 459783 693509 := bbase (se 4 (by rfl) ⟨65016, by rfl⟩ : syracuseStep 693509 = 130033) (by norm_num)
theorem B693533 : Blo 459783 693533 := bbase (se 3 (by rfl) ⟨130037, by rfl⟩ : syracuseStep 693533 = 260075) (by norm_num)
theorem B693557 : Blo 459783 693557 := bbase (se 5 (by rfl) ⟨32510, by rfl⟩ : syracuseStep 693557 = 65021) (by norm_num)
theorem B693581 : Blo 459783 693581 := bbase (se 3 (by rfl) ⟨130046, by rfl⟩ : syracuseStep 693581 = 260093) (by norm_num)
theorem B2331989 : Blo 459783 2331989 := bbase (se 14 (by rfl) ⟨213, by rfl⟩ : syracuseStep 2331989 = 427) (by norm_num)
theorem B693605 : Blo 459783 693605 := bbase (se 4 (by rfl) ⟨65025, by rfl⟩ : syracuseStep 693605 = 130051) (by norm_num)
theorem B988517 : Blo 459783 988517 := bbase (se 4 (by rfl) ⟨92673, by rfl⟩ : syracuseStep 988517 = 185347) (by norm_num)
theorem B693629 : Blo 459783 693629 := bbase (se 3 (by rfl) ⟨130055, by rfl⟩ : syracuseStep 693629 = 260111) (by norm_num)
theorem B693653 : Blo 459783 693653 := bbase (se 6 (by rfl) ⟨16257, by rfl⟩ : syracuseStep 693653 = 32515) (by norm_num)
theorem B693677 : Blo 459783 693677 := bbase (se 3 (by rfl) ⟨130064, by rfl⟩ : syracuseStep 693677 = 260129) (by norm_num)
theorem B693701 : Blo 459783 693701 := bbase (se 4 (by rfl) ⟨65034, by rfl⟩ : syracuseStep 693701 = 130069) (by norm_num)
theorem B693725 : Blo 459783 693725 := bbase (se 3 (by rfl) ⟨130073, by rfl⟩ : syracuseStep 693725 = 260147) (by norm_num)
theorem B693749 : Blo 459783 693749 := bbase (se 5 (by rfl) ⟨32519, by rfl⟩ : syracuseStep 693749 = 65039) (by norm_num)
theorem B988661 : Blo 459783 988661 := bbase (se 5 (by rfl) ⟨46343, by rfl⟩ : syracuseStep 988661 = 92687) (by norm_num)
theorem B693773 : Blo 459783 693773 := bbase (se 3 (by rfl) ⟨130082, by rfl⟩ : syracuseStep 693773 = 260165) (by norm_num)
theorem B693797 : Blo 459783 693797 := bbase (se 4 (by rfl) ⟨65043, by rfl⟩ : syracuseStep 693797 = 130087) (by norm_num)
theorem B693821 : Blo 459783 693821 := bbase (se 3 (by rfl) ⟨130091, by rfl⟩ : syracuseStep 693821 = 260183) (by norm_num)
theorem B693845 : Blo 459783 693845 := bbase (se 8 (by rfl) ⟨4065, by rfl⟩ : syracuseStep 693845 = 8131) (by norm_num)
theorem B693869 : Blo 459783 693869 := bbase (se 3 (by rfl) ⟨130100, by rfl⟩ : syracuseStep 693869 = 260201) (by norm_num)
theorem B1873525 : Blo 459783 1873525 := bbase (se 5 (by rfl) ⟨87821, by rfl⟩ : syracuseStep 1873525 = 175643) (by norm_num)
theorem B693893 : Blo 459783 693893 := bbase (se 4 (by rfl) ⟨65052, by rfl⟩ : syracuseStep 693893 = 130105) (by norm_num)
theorem B693917 : Blo 459783 693917 := bbase (se 3 (by rfl) ⟨130109, by rfl⟩ : syracuseStep 693917 = 260219) (by norm_num)
theorem B693941 : Blo 459783 693941 := bbase (se 5 (by rfl) ⟨32528, by rfl⟩ : syracuseStep 693941 = 65057) (by norm_num)
theorem B693965 : Blo 459783 693965 := bbase (se 3 (by rfl) ⟨130118, by rfl⟩ : syracuseStep 693965 = 260237) (by norm_num)
theorem B693989 : Blo 459783 693989 := bbase (se 4 (by rfl) ⟨65061, by rfl⟩ : syracuseStep 693989 = 130123) (by norm_num)
theorem B694013 : Blo 459783 694013 := bbase (se 3 (by rfl) ⟨130127, by rfl⟩ : syracuseStep 694013 = 260255) (by norm_num)
theorem B694037 : Blo 459783 694037 := bbase (se 6 (by rfl) ⟨16266, by rfl⟩ : syracuseStep 694037 = 32533) (by norm_num)
theorem B694061 : Blo 459783 694061 := bbase (se 3 (by rfl) ⟨130136, by rfl⟩ : syracuseStep 694061 = 260273) (by norm_num)
theorem B890677 : Blo 459783 890677 := bbase (se 5 (by rfl) ⟨41750, by rfl⟩ : syracuseStep 890677 = 83501) (by norm_num)
theorem B694085 : Blo 459783 694085 := bbase (se 4 (by rfl) ⟨65070, by rfl⟩ : syracuseStep 694085 = 130141) (by norm_num)
theorem B694109 : Blo 459783 694109 := bbase (se 3 (by rfl) ⟨130145, by rfl⟩ : syracuseStep 694109 = 260291) (by norm_num)
theorem B694133 : Blo 459783 694133 := bbase (se 5 (by rfl) ⟨32537, by rfl⟩ : syracuseStep 694133 = 65075) (by norm_num)
theorem B694157 : Blo 459783 694157 := bbase (se 3 (by rfl) ⟨130154, by rfl⟩ : syracuseStep 694157 = 260309) (by norm_num)
theorem B2627477 : Blo 459783 2627477 := bbase (se 6 (by rfl) ⟨61581, by rfl⟩ : syracuseStep 2627477 = 123163) (by norm_num)
theorem B694181 : Blo 459783 694181 := bbase (se 4 (by rfl) ⟨65079, by rfl⟩ : syracuseStep 694181 = 130159) (by norm_num)
theorem B694205 : Blo 459783 694205 := bbase (se 3 (by rfl) ⟨130163, by rfl⟩ : syracuseStep 694205 = 260327) (by norm_num)
theorem B694229 : Blo 459783 694229 := bbase (se 7 (by rfl) ⟨8135, by rfl⟩ : syracuseStep 694229 = 16271) (by norm_num)
theorem B1316837 : Blo 459783 1316837 := bbase (se 4 (by rfl) ⟨123453, by rfl⟩ : syracuseStep 1316837 = 246907) (by norm_num)
theorem B694253 : Blo 459783 694253 := bbase (se 3 (by rfl) ⟨130172, by rfl⟩ : syracuseStep 694253 = 260345) (by norm_num)
theorem B694277 : Blo 459783 694277 := bbase (se 4 (by rfl) ⟨65088, by rfl⟩ : syracuseStep 694277 = 130177) (by norm_num)
theorem B694301 : Blo 459783 694301 := bbase (se 3 (by rfl) ⟨130181, by rfl⟩ : syracuseStep 694301 = 260363) (by norm_num)
theorem B694325 : Blo 459783 694325 := bbase (se 5 (by rfl) ⟨32546, by rfl⟩ : syracuseStep 694325 = 65093) (by norm_num)
theorem B694349 : Blo 459783 694349 := bbase (se 3 (by rfl) ⟨130190, by rfl⟩ : syracuseStep 694349 = 260381) (by norm_num)
theorem B694373 : Blo 459783 694373 := bbase (se 4 (by rfl) ⟨65097, by rfl⟩ : syracuseStep 694373 = 130195) (by norm_num)
theorem B563321 : Blo 459783 563321 := bbase (se 2 (by rfl) ⟨211245, by rfl⟩ : syracuseStep 563321 = 422491) (by norm_num)
theorem B694397 : Blo 459783 694397 := bbase (se 3 (by rfl) ⟨130199, by rfl⟩ : syracuseStep 694397 = 260399) (by norm_num)
theorem B694421 : Blo 459783 694421 := bbase (se 6 (by rfl) ⟨16275, by rfl⟩ : syracuseStep 694421 = 32551) (by norm_num)
theorem B694445 : Blo 459783 694445 := bbase (se 3 (by rfl) ⟨130208, by rfl⟩ : syracuseStep 694445 = 260417) (by norm_num)
theorem B694469 : Blo 459783 694469 := bbase (se 4 (by rfl) ⟨65106, by rfl⟩ : syracuseStep 694469 = 130213) (by norm_num)
theorem B1054925 : Blo 459783 1054925 := bbase (se 3 (by rfl) ⟨197798, by rfl⟩ : syracuseStep 1054925 = 395597) (by norm_num)
theorem B694493 : Blo 459783 694493 := bbase (se 3 (by rfl) ⟨130217, by rfl⟩ : syracuseStep 694493 = 260435) (by norm_num)
theorem B989405 : Blo 459783 989405 := bbase (se 3 (by rfl) ⟨185513, by rfl⟩ : syracuseStep 989405 = 371027) (by norm_num)
theorem B694517 : Blo 459783 694517 := bbase (se 5 (by rfl) ⟨32555, by rfl⟩ : syracuseStep 694517 = 65111) (by norm_num)
theorem B694541 : Blo 459783 694541 := bbase (se 3 (by rfl) ⟨130226, by rfl⟩ : syracuseStep 694541 = 260453) (by norm_num)
theorem B694565 : Blo 459783 694565 := bbase (se 4 (by rfl) ⟨65115, by rfl⟩ : syracuseStep 694565 = 130231) (by norm_num)
theorem B694589 : Blo 459783 694589 := bbase (se 3 (by rfl) ⟨130235, by rfl⟩ : syracuseStep 694589 = 260471) (by norm_num)
theorem B694613 : Blo 459783 694613 := bbase (se 10 (by rfl) ⟨1017, by rfl⟩ : syracuseStep 694613 = 2035) (by norm_num)
theorem B694637 : Blo 459783 694637 := bbase (se 3 (by rfl) ⟨130244, by rfl⟩ : syracuseStep 694637 = 260489) (by norm_num)
theorem B694661 : Blo 459783 694661 := bbase (se 4 (by rfl) ⟨65124, by rfl⟩ : syracuseStep 694661 = 130249) (by norm_num)
theorem B694685 : Blo 459783 694685 := bbase (se 3 (by rfl) ⟨130253, by rfl⟩ : syracuseStep 694685 = 260507) (by norm_num)
theorem B2365861 : Blo 459783 2365861 := bbase (se 4 (by rfl) ⟨221799, by rfl⟩ : syracuseStep 2365861 = 443599) (by norm_num)
theorem B694709 : Blo 459783 694709 := bbase (se 5 (by rfl) ⟨32564, by rfl⟩ : syracuseStep 694709 = 65129) (by norm_num)
theorem B694733 : Blo 459783 694733 := bbase (se 3 (by rfl) ⟨130262, by rfl⟩ : syracuseStep 694733 = 260525) (by norm_num)
theorem B694757 : Blo 459783 694757 := bbase (se 4 (by rfl) ⟨65133, by rfl⟩ : syracuseStep 694757 = 130267) (by norm_num)
theorem B694781 : Blo 459783 694781 := bbase (se 3 (by rfl) ⟨130271, by rfl⟩ : syracuseStep 694781 = 260543) (by norm_num)
theorem B1481237 : Blo 459783 1481237 := bbase (se 6 (by rfl) ⟨34716, by rfl⟩ : syracuseStep 1481237 = 69433) (by norm_num)
theorem B694805 : Blo 459783 694805 := bbase (se 6 (by rfl) ⟨16284, by rfl⟩ : syracuseStep 694805 = 32569) (by norm_num)
theorem B694829 : Blo 459783 694829 := bbase (se 3 (by rfl) ⟨130280, by rfl⟩ : syracuseStep 694829 = 260561) (by norm_num)
theorem B694853 : Blo 459783 694853 := bbase (se 4 (by rfl) ⟨65142, by rfl⟩ : syracuseStep 694853 = 130285) (by norm_num)
theorem B694877 : Blo 459783 694877 := bbase (se 3 (by rfl) ⟨130289, by rfl⟩ : syracuseStep 694877 = 260579) (by norm_num)
theorem B2333285 : Blo 459783 2333285 := bbase (se 4 (by rfl) ⟨218745, by rfl⟩ : syracuseStep 2333285 = 437491) (by norm_num)
theorem B694901 : Blo 459783 694901 := bbase (se 5 (by rfl) ⟨32573, by rfl⟩ : syracuseStep 694901 = 65147) (by norm_num)
theorem B1317509 : Blo 459783 1317509 := bbase (se 4 (by rfl) ⟨123516, by rfl⟩ : syracuseStep 1317509 = 247033) (by norm_num)
theorem B694925 : Blo 459783 694925 := bbase (se 3 (by rfl) ⟨130298, by rfl⟩ : syracuseStep 694925 = 260597) (by norm_num)
theorem B694949 : Blo 459783 694949 := bbase (se 4 (by rfl) ⟨65151, by rfl⟩ : syracuseStep 694949 = 130303) (by norm_num)
theorem B694973 : Blo 459783 694973 := bbase (se 3 (by rfl) ⟨130307, by rfl⟩ : syracuseStep 694973 = 260615) (by norm_num)
theorem B3939029 : Blo 459783 3939029 := bbase (se 7 (by rfl) ⟨46160, by rfl⟩ : syracuseStep 3939029 = 92321) (by norm_num)
theorem B694997 : Blo 459783 694997 := bbase (se 7 (by rfl) ⟨8144, by rfl⟩ : syracuseStep 694997 = 16289) (by norm_num)
theorem B695021 : Blo 459783 695021 := bbase (se 3 (by rfl) ⟨130316, by rfl⟩ : syracuseStep 695021 = 260633) (by norm_num)
theorem B695045 : Blo 459783 695045 := bbase (se 4 (by rfl) ⟨65160, by rfl⟩ : syracuseStep 695045 = 130321) (by norm_num)
theorem B695069 : Blo 459783 695069 := bbase (se 3 (by rfl) ⟨130325, by rfl⟩ : syracuseStep 695069 = 260651) (by norm_num)
theorem B695093 : Blo 459783 695093 := bbase (se 5 (by rfl) ⟨32582, by rfl⟩ : syracuseStep 695093 = 65165) (by norm_num)
theorem B695117 : Blo 459783 695117 := bbase (se 3 (by rfl) ⟨130334, by rfl⟩ : syracuseStep 695117 = 260669) (by norm_num)
theorem B695141 : Blo 459783 695141 := bbase (se 4 (by rfl) ⟨65169, by rfl⟩ : syracuseStep 695141 = 130339) (by norm_num)
theorem B695165 : Blo 459783 695165 := bbase (se 3 (by rfl) ⟨130343, by rfl⟩ : syracuseStep 695165 = 260687) (by norm_num)
theorem B695189 : Blo 459783 695189 := bbase (se 6 (by rfl) ⟨16293, by rfl⟩ : syracuseStep 695189 = 32587) (by norm_num)
theorem B695213 : Blo 459783 695213 := bbase (se 3 (by rfl) ⟨130352, by rfl⟩ : syracuseStep 695213 = 260705) (by norm_num)
theorem B695237 : Blo 459783 695237 := bbase (se 4 (by rfl) ⟨65178, by rfl⟩ : syracuseStep 695237 = 130357) (by norm_num)
theorem B990157 : Blo 459783 990157 := bbase (se 3 (by rfl) ⟨185654, by rfl⟩ : syracuseStep 990157 = 371309) (by norm_num)
theorem B695261 : Blo 459783 695261 := bbase (se 3 (by rfl) ⟨130361, by rfl⟩ : syracuseStep 695261 = 260723) (by norm_num)
theorem B695285 : Blo 459783 695285 := bbase (se 5 (by rfl) ⟨32591, by rfl⟩ : syracuseStep 695285 = 65183) (by norm_num)
theorem B695309 : Blo 459783 695309 := bbase (se 3 (by rfl) ⟨130370, by rfl⟩ : syracuseStep 695309 = 260741) (by norm_num)
theorem B695333 : Blo 459783 695333 := bbase (se 4 (by rfl) ⟨65187, by rfl⟩ : syracuseStep 695333 = 130375) (by norm_num)
theorem B1317941 : Blo 459783 1317941 := bbase (se 5 (by rfl) ⟨61778, by rfl⟩ : syracuseStep 1317941 = 123557) (by norm_num)
theorem B695357 : Blo 459783 695357 := bbase (se 3 (by rfl) ⟨130379, by rfl⟩ : syracuseStep 695357 = 260759) (by norm_num)
theorem B695381 : Blo 459783 695381 := bbase (se 8 (by rfl) ⟨4074, by rfl⟩ : syracuseStep 695381 = 8149) (by norm_num)
theorem B990301 : Blo 459783 990301 := bbase (se 3 (by rfl) ⟨185681, by rfl⟩ : syracuseStep 990301 = 371363) (by norm_num)
theorem B695405 : Blo 459783 695405 := bbase (se 3 (by rfl) ⟨130388, by rfl⟩ : syracuseStep 695405 = 260777) (by norm_num)
theorem B695429 : Blo 459783 695429 := bbase (se 4 (by rfl) ⟨65196, by rfl⟩ : syracuseStep 695429 = 130393) (by norm_num)
theorem B695453 : Blo 459783 695453 := bbase (se 3 (by rfl) ⟨130397, by rfl⟩ : syracuseStep 695453 = 260795) (by norm_num)
theorem B695477 : Blo 459783 695477 := bbase (se 5 (by rfl) ⟨32600, by rfl⟩ : syracuseStep 695477 = 65201) (by norm_num)
theorem B695501 : Blo 459783 695501 := bbase (se 3 (by rfl) ⟨130406, by rfl⟩ : syracuseStep 695501 = 260813) (by norm_num)
theorem B695525 : Blo 459783 695525 := bbase (se 4 (by rfl) ⟨65205, by rfl⟩ : syracuseStep 695525 = 130411) (by norm_num)
theorem B695549 : Blo 459783 695549 := bbase (se 3 (by rfl) ⟨130415, by rfl⟩ : syracuseStep 695549 = 260831) (by norm_num)
theorem B1580309 : Blo 459783 1580309 := bbase (se 6 (by rfl) ⟨37038, by rfl⟩ : syracuseStep 1580309 = 74077) (by norm_num)
theorem B695573 : Blo 459783 695573 := bbase (se 6 (by rfl) ⟨16302, by rfl⟩ : syracuseStep 695573 = 32605) (by norm_num)
theorem B695597 : Blo 459783 695597 := bbase (se 3 (by rfl) ⟨130424, by rfl⟩ : syracuseStep 695597 = 260849) (by norm_num)
theorem B695621 : Blo 459783 695621 := bbase (se 4 (by rfl) ⟨65214, by rfl⟩ : syracuseStep 695621 = 130429) (by norm_num)
theorem B695645 : Blo 459783 695645 := bbase (se 3 (by rfl) ⟨130433, by rfl⟩ : syracuseStep 695645 = 260867) (by norm_num)
theorem B466285 : Blo 459783 466285 := bbase (se 3 (by rfl) ⟨87428, by rfl⟩ : syracuseStep 466285 = 174857) (by norm_num)
theorem B695669 : Blo 459783 695669 := bbase (se 5 (by rfl) ⟨32609, by rfl⟩ : syracuseStep 695669 = 65219) (by norm_num)
theorem B1318693 : Blo 459783 1318693 := bbase (se 4 (by rfl) ⟨123627, by rfl⟩ : syracuseStep 1318693 = 247255) (by norm_num)
theorem B1482581 : Blo 459783 1482581 := bbase (se 9 (by rfl) ⟨4343, by rfl⟩ : syracuseStep 1482581 = 8687) (by norm_num)
theorem B2334581 : Blo 459783 2334581 := bbase (se 5 (by rfl) ⟨109433, by rfl⟩ : syracuseStep 2334581 = 218867) (by norm_num)
theorem B2957269 : Blo 459783 2957269 := bbase (se 7 (by rfl) ⟨34655, by rfl⟩ : syracuseStep 2957269 = 69311) (by norm_num)
theorem B2629685 : Blo 459783 2629685 := bbase (se 5 (by rfl) ⟨123266, by rfl⟩ : syracuseStep 2629685 = 246533) (by norm_num)
theorem B663725 : Blo 459783 663725 := bbase (se 3 (by rfl) ⟨124448, by rfl⟩ : syracuseStep 663725 = 248897) (by norm_num)
theorem B467201 : Blo 459783 467201 := bbase (se 2 (by rfl) ⟨175200, by rfl⟩ : syracuseStep 467201 = 350401) (by norm_num)
theorem B1188229 : Blo 459783 1188229 := bbase (se 4 (by rfl) ⟨111396, by rfl⟩ : syracuseStep 1188229 = 222793) (by norm_num)
theorem B1974725 : Blo 459783 1974725 := bbase (se 4 (by rfl) ⟨185130, by rfl⟩ : syracuseStep 1974725 = 370261) (by norm_num)
theorem B1057333 : Blo 459783 1057333 := bbase (se 5 (by rfl) ⟨49562, by rfl⟩ : syracuseStep 1057333 = 99125) (by norm_num)
theorem B1188413 : Blo 459783 1188413 := bbase (se 3 (by rfl) ⟨222827, by rfl⟩ : syracuseStep 1188413 = 445655) (by norm_num)
theorem B2499349 : Blo 459783 2499349 := bbase (se 6 (by rfl) ⟨58578, by rfl⟩ : syracuseStep 2499349 = 117157) (by norm_num)
theorem B4432981 : Blo 459783 4432981 := bbase (se 8 (by rfl) ⟨25974, by rfl⟩ : syracuseStep 4432981 = 51949) (by norm_num)
theorem B2335877 : Blo 459783 2335877 := bbase (se 4 (by rfl) ⟨218988, by rfl⟩ : syracuseStep 2335877 = 437977) (by norm_num)
theorem B664789 : Blo 459783 664789 := bbase (se 7 (by rfl) ⟨7790, by rfl⟩ : syracuseStep 664789 = 15581) (by norm_num)
theorem B501041 : Blo 459783 501041 := bbase (se 2 (by rfl) ⟨187890, by rfl⟩ : syracuseStep 501041 = 375781) (by norm_num)
theorem B468337 : Blo 459783 468337 := bbase (se 2 (by rfl) ⟨175626, by rfl⟩ : syracuseStep 468337 = 351253) (by norm_num)
theorem B2368901 : Blo 459783 2368901 := bbase (se 4 (by rfl) ⟨222084, by rfl⟩ : syracuseStep 2368901 = 444169) (by norm_num)
theorem B665237 : Blo 459783 665237 := bbase (se 6 (by rfl) ⟨15591, by rfl⟩ : syracuseStep 665237 = 31183) (by norm_num)
theorem B829109 : Blo 459783 829109 := bbase (se 5 (by rfl) ⟨38864, by rfl⟩ : syracuseStep 829109 = 77729) (by norm_num)
theorem B468677 : Blo 459783 468677 := bbase (se 4 (by rfl) ⟨43938, by rfl⟩ : syracuseStep 468677 = 87877) (by norm_num)
theorem B829181 : Blo 459783 829181 := bbase (se 3 (by rfl) ⟨155471, by rfl⟩ : syracuseStep 829181 = 310943) (by norm_num)
theorem B1484581 : Blo 459783 1484581 := bbase (se 4 (by rfl) ⟨139179, by rfl⟩ : syracuseStep 1484581 = 278359) (by norm_num)
theorem B1746805 : Blo 459783 1746805 := bbase (se 5 (by rfl) ⟨81881, by rfl⟩ : syracuseStep 1746805 = 163763) (by norm_num)
theorem B468937 : Blo 459783 468937 := bbase (se 2 (by rfl) ⟨175851, by rfl⟩ : syracuseStep 468937 = 351703) (by norm_num)
theorem B829397 : Blo 459783 829397 := bbase (se 7 (by rfl) ⟨9719, by rfl⟩ : syracuseStep 829397 = 19439) (by norm_num)
theorem B1747109 : Blo 459783 1747109 := bbase (se 4 (by rfl) ⟨163791, by rfl⟩ : syracuseStep 1747109 = 327583) (by norm_num)
theorem B1976501 : Blo 459783 1976501 := bbase (se 5 (by rfl) ⟨92648, by rfl⟩ : syracuseStep 1976501 = 185297) (by norm_num)
theorem B469237 : Blo 459783 469237 := bbase (se 5 (by rfl) ⟨21995, by rfl⟩ : syracuseStep 469237 = 43991) (by norm_num)
theorem B2337173 : Blo 459783 2337173 := bbase (se 6 (by rfl) ⟨54777, by rfl⟩ : syracuseStep 2337173 = 109555) (by norm_num)
theorem B1583525 : Blo 459783 1583525 := bbase (se 4 (by rfl) ⟨148455, by rfl⟩ : syracuseStep 1583525 = 296911) (by norm_num)
theorem B797245 : Blo 459783 797245 := bbase (se 3 (by rfl) ⟨149483, by rfl⟩ : syracuseStep 797245 = 298967) (by norm_num)
theorem B469585 : Blo 459783 469585 := bbase (se 2 (by rfl) ⟨176094, by rfl⟩ : syracuseStep 469585 = 352189) (by norm_num)
theorem B1780309 : Blo 459783 1780309 := bbase (se 8 (by rfl) ⟨10431, by rfl⟩ : syracuseStep 1780309 = 20863) (by norm_num)
theorem B1682309 : Blo 459783 1682309 := bbase (se 4 (by rfl) ⟨157716, by rfl⟩ : syracuseStep 1682309 = 315433) (by norm_num)
theorem B1977493 : Blo 459783 1977493 := bbase (se 6 (by rfl) ⟨46347, by rfl⟩ : syracuseStep 1977493 = 92695) (by norm_num)
theorem B699781 : Blo 459783 699781 := bbase (se 4 (by rfl) ⟨65604, by rfl⟩ : syracuseStep 699781 = 131209) (by norm_num)
theorem B1551797 : Blo 459783 1551797 := bbase (se 5 (by rfl) ⟨72740, by rfl⟩ : syracuseStep 1551797 = 145481) (by norm_num)
theorem B2338469 : Blo 459783 2338469 := bbase (se 4 (by rfl) ⟨219231, by rfl⟩ : syracuseStep 2338469 = 438463) (by norm_num)
theorem B1552229 : Blo 459783 1552229 := bbase (se 4 (by rfl) ⟨145521, by rfl⟩ : syracuseStep 1552229 = 291043) (by norm_num)
theorem B4435829 : Blo 459783 4435829 := bbase (se 5 (by rfl) ⟨207929, by rfl⟩ : syracuseStep 4435829 = 415859) (by norm_num)
theorem B1126429 : Blo 459783 1126429 := bbase (se 3 (by rfl) ⟨211205, by rfl⟩ : syracuseStep 1126429 = 422411) (by norm_num)
theorem B2535509 : Blo 459783 2535509 := bbase (se 8 (by rfl) ⟨14856, by rfl⟩ : syracuseStep 2535509 = 29713) (by norm_num)
theorem B1749221 : Blo 459783 1749221 := bbase (se 4 (by rfl) ⟨163989, by rfl⟩ : syracuseStep 1749221 = 327979) (by norm_num)
theorem B1552661 : Blo 459783 1552661 := bbase (se 6 (by rfl) ⟨36390, by rfl⟩ : syracuseStep 1552661 = 72781) (by norm_num)
theorem B1749509 : Blo 459783 1749509 := bbase (se 4 (by rfl) ⟨164016, by rfl⟩ : syracuseStep 1749509 = 328033) (by norm_num)
theorem B700949 : Blo 459783 700949 := bbase (se 6 (by rfl) ⟨16428, by rfl⟩ : syracuseStep 700949 = 32857) (by norm_num)
theorem B995917 : Blo 459783 995917 := bbase (se 3 (by rfl) ⟨186734, by rfl⟩ : syracuseStep 995917 = 373469) (by norm_num)
theorem B3519125 : Blo 459783 3519125 := bbase (se 6 (by rfl) ⟨82479, by rfl⟩ : syracuseStep 3519125 = 164959) (by norm_num)
theorem B1553093 : Blo 459783 1553093 := bbase (se 4 (by rfl) ⟨145602, by rfl⟩ : syracuseStep 1553093 = 291205) (by norm_num)
theorem B2700053 : Blo 459783 2700053 := bbase (se 6 (by rfl) ⟨63282, by rfl⟩ : syracuseStep 2700053 = 126565) (by norm_num)
theorem B2339765 : Blo 459783 2339765 := bbase (se 5 (by rfl) ⟨109676, by rfl⟩ : syracuseStep 2339765 = 219353) (by norm_num)
theorem B668701 : Blo 459783 668701 := bbase (se 3 (by rfl) ⟨125381, by rfl⟩ : syracuseStep 668701 = 250763) (by norm_num)
theorem B1553525 : Blo 459783 1553525 := bbase (se 5 (by rfl) ⟨72821, by rfl⟩ : syracuseStep 1553525 = 145643) (by norm_num)
theorem B701957 : Blo 459783 701957 := bbase (se 4 (by rfl) ⟨65808, by rfl⟩ : syracuseStep 701957 = 131617) (by norm_num)
theorem B1553957 : Blo 459783 1553957 := bbase (se 4 (by rfl) ⟨145683, by rfl⟩ : syracuseStep 1553957 = 291367) (by norm_num)
theorem B1750693 : Blo 459783 1750693 := bbase (se 4 (by rfl) ⟨164127, by rfl⟩ : syracuseStep 1750693 = 328255) (by norm_num)
theorem B997085 : Blo 459783 997085 := bbase (se 3 (by rfl) ⟨186953, by rfl⟩ : syracuseStep 997085 = 373907) (by norm_num)
theorem B2963317 : Blo 459783 2963317 := bbase (se 5 (by rfl) ⟨138905, by rfl⟩ : syracuseStep 2963317 = 277811) (by norm_num)
theorem B1554389 : Blo 459783 1554389 := bbase (se 7 (by rfl) ⟨18215, by rfl⟩ : syracuseStep 1554389 = 36431) (by norm_num)
theorem B1750997 : Blo 459783 1750997 := bbase (se 7 (by rfl) ⟨20519, by rfl⟩ : syracuseStep 1750997 = 41039) (by norm_num)
theorem B997373 : Blo 459783 997373 := bbase (se 3 (by rfl) ⟨187007, by rfl⟩ : syracuseStep 997373 = 374015) (by norm_num)
theorem B2341061 : Blo 459783 2341061 := bbase (se 4 (by rfl) ⟨219474, by rfl⟩ : syracuseStep 2341061 = 438949) (by norm_num)
theorem B1554821 : Blo 459783 1554821 := bbase (se 4 (by rfl) ⟨145764, by rfl⟩ : syracuseStep 1554821 = 291529) (by norm_num)
theorem B3750421 : Blo 459783 3750421 := bbase (se 6 (by rfl) ⟨87900, by rfl⟩ : syracuseStep 3750421 = 175801) (by norm_num)
theorem B1555253 : Blo 459783 1555253 := bbase (se 5 (by rfl) ⟨72902, by rfl⟩ : syracuseStep 1555253 = 145805) (by norm_num)
theorem B7519061 : Blo 459783 7519061 := bbase (se 9 (by rfl) ⟨22028, by rfl⟩ : syracuseStep 7519061 = 44057) (by norm_num)
theorem B1260533 : Blo 459783 1260533 := bbase (se 5 (by rfl) ⟨59087, by rfl⟩ : syracuseStep 1260533 = 118175) (by norm_num)
theorem B1555685 : Blo 459783 1555685 := bbase (se 4 (by rfl) ⟨145845, by rfl⟩ : syracuseStep 1555685 = 291691) (by norm_num)
theorem B736589 : Blo 459783 736589 := bbase (se 3 (by rfl) ⟨138110, by rfl⟩ : syracuseStep 736589 = 276221) (by norm_num)
theorem B2342357 : Blo 459783 2342357 := bbase (se 7 (by rfl) ⟨27449, by rfl⟩ : syracuseStep 2342357 = 54899) (by norm_num)
theorem B769517 : Blo 459783 769517 := bbase (se 3 (by rfl) ⟨144284, by rfl⟩ : syracuseStep 769517 = 288569) (by norm_num)
theorem B4439573 : Blo 459783 4439573 := bbase (se 6 (by rfl) ⟨104052, by rfl⟩ : syracuseStep 4439573 = 208105) (by norm_num)
theorem B933461 : Blo 459783 933461 := bbase (se 8 (by rfl) ⟨5469, by rfl⟩ : syracuseStep 933461 = 10939) (by norm_num)
theorem B835157 : Blo 459783 835157 := bbase (se 8 (by rfl) ⟨4893, by rfl⟩ : syracuseStep 835157 = 9787) (by norm_num)
theorem B736877 : Blo 459783 736877 := bbase (se 3 (by rfl) ⟨138164, by rfl⟩ : syracuseStep 736877 = 276329) (by norm_num)
theorem B1556117 : Blo 459783 1556117 := bbase (se 6 (by rfl) ⟨36471, by rfl⟩ : syracuseStep 1556117 = 72943) (by norm_num)
theorem B2703253 : Blo 459783 2703253 := bbase (se 6 (by rfl) ⟨63357, by rfl⟩ : syracuseStep 2703253 = 126715) (by norm_num)
theorem B3162037 : Blo 459783 3162037 := bbase (se 5 (by rfl) ⟨148220, by rfl⟩ : syracuseStep 3162037 = 296441) (by norm_num)
theorem B1753109 : Blo 459783 1753109 := bbase (se 6 (by rfl) ⟨41088, by rfl⟩ : syracuseStep 1753109 = 82177) (by norm_num)
theorem B2211877 : Blo 459783 2211877 := bbase (se 4 (by rfl) ⟨207363, by rfl⟩ : syracuseStep 2211877 = 414727) (by norm_num)
theorem B1556549 : Blo 459783 1556549 := bbase (se 4 (by rfl) ⟨145926, by rfl⟩ : syracuseStep 1556549 = 291853) (by norm_num)
theorem B1753397 : Blo 459783 1753397 := bbase (se 5 (by rfl) ⟨82190, by rfl⟩ : syracuseStep 1753397 = 164381) (by norm_num)
theorem B737677 : Blo 459783 737677 := bbase (se 3 (by rfl) ⟨138314, by rfl⟩ : syracuseStep 737677 = 276629) (by norm_num)
theorem B1556981 : Blo 459783 1556981 := bbase (se 5 (by rfl) ⟨72983, by rfl⟩ : syracuseStep 1556981 = 145967) (by norm_num)
theorem B1163909 : Blo 459783 1163909 := bbase (se 4 (by rfl) ⟨109116, by rfl⟩ : syracuseStep 1163909 = 218233) (by norm_num)
theorem B1688197 : Blo 459783 1688197 := bbase (se 4 (by rfl) ⟨158268, by rfl⟩ : syracuseStep 1688197 = 316537) (by norm_num)
theorem B2966165 : Blo 459783 2966165 := bbase (se 6 (by rfl) ⟨69519, by rfl⟩ : syracuseStep 2966165 = 139039) (by norm_num)
theorem B2343653 : Blo 459783 2343653 := bbase (se 4 (by rfl) ⟨219717, by rfl⟩ : syracuseStep 2343653 = 439435) (by norm_num)
theorem B1557413 : Blo 459783 1557413 := bbase (se 4 (by rfl) ⟨146007, by rfl⟩ : syracuseStep 1557413 = 292015) (by norm_num)
theorem B738229 : Blo 459783 738229 := bbase (se 5 (by rfl) ⟨34604, by rfl⟩ : syracuseStep 738229 = 69209) (by norm_num)
theorem B1164253 : Blo 459783 1164253 := bbase (se 3 (by rfl) ⟨218297, by rfl⟩ : syracuseStep 1164253 = 436595) (by norm_num)
theorem B1164365 : Blo 459783 1164365 := bbase (se 3 (by rfl) ⟨218318, by rfl⟩ : syracuseStep 1164365 = 436637) (by norm_num)
theorem B738485 : Blo 459783 738485 := bbase (se 5 (by rfl) ⟨34616, by rfl⟩ : syracuseStep 738485 = 69233) (by norm_num)
theorem B4211957 : Blo 459783 4211957 := bbase (se 5 (by rfl) ⟨197435, by rfl⟩ : syracuseStep 4211957 = 394871) (by norm_num)
theorem B935165 : Blo 459783 935165 := bbase (se 3 (by rfl) ⟨175343, by rfl⟩ : syracuseStep 935165 = 350687) (by norm_num)
theorem B1164557 : Blo 459783 1164557 := bbase (se 3 (by rfl) ⟨218354, by rfl⟩ : syracuseStep 1164557 = 436709) (by norm_num)
theorem B1557845 : Blo 459783 1557845 := bbase (se 12 (by rfl) ⟨570, by rfl⟩ : syracuseStep 1557845 = 1141) (by norm_num)
theorem B2803157 : Blo 459783 2803157 := bbase (se 7 (by rfl) ⟨32849, by rfl⟩ : syracuseStep 2803157 = 65699) (by norm_num)
theorem B1754581 : Blo 459783 1754581 := bbase (se 7 (by rfl) ⟨20561, by rfl⟩ : syracuseStep 1754581 = 41123) (by norm_num)
theorem B1164901 : Blo 459783 1164901 := bbase (se 4 (by rfl) ⟨109209, by rfl⟩ : syracuseStep 1164901 = 218419) (by norm_num)
theorem B1165013 : Blo 459783 1165013 := bbase (se 7 (by rfl) ⟨13652, by rfl⟩ : syracuseStep 1165013 = 27305) (by norm_num)
theorem B2639573 : Blo 459783 2639573 := bbase (se 7 (by rfl) ⟨30932, by rfl⟩ : syracuseStep 2639573 = 61865) (by norm_num)
theorem B1558277 : Blo 459783 1558277 := bbase (se 4 (by rfl) ⟨146088, by rfl⟩ : syracuseStep 1558277 = 292177) (by norm_num)
theorem B1754885 : Blo 459783 1754885 := bbase (se 4 (by rfl) ⟨164520, by rfl⟩ : syracuseStep 1754885 = 329041) (by norm_num)
theorem B935725 : Blo 459783 935725 := bbase (se 3 (by rfl) ⟨175448, by rfl⟩ : syracuseStep 935725 = 350897) (by norm_num)
theorem B739189 : Blo 459783 739189 := bbase (se 5 (by rfl) ⟨34649, by rfl⟩ : syracuseStep 739189 = 69299) (by norm_num)
theorem B1165205 : Blo 459783 1165205 := bbase (se 6 (by rfl) ⟨27309, by rfl⟩ : syracuseStep 1165205 = 54619) (by norm_num)
theorem B2344949 : Blo 459783 2344949 := bbase (se 5 (by rfl) ⟨109919, by rfl⟩ : syracuseStep 2344949 = 219839) (by norm_num)
theorem B2377765 : Blo 459783 2377765 := bbase (se 4 (by rfl) ⟨222915, by rfl⟩ : syracuseStep 2377765 = 445831) (by norm_num)
theorem B1558709 : Blo 459783 1558709 := bbase (se 5 (by rfl) ⟨73064, by rfl⟩ : syracuseStep 1558709 = 146129) (by norm_num)
theorem B1165549 : Blo 459783 1165549 := bbase (se 3 (by rfl) ⟨218540, by rfl⟩ : syracuseStep 1165549 = 437081) (by norm_num)
theorem B739613 : Blo 459783 739613 := bbase (se 3 (by rfl) ⟨138677, by rfl⟩ : syracuseStep 739613 = 277355) (by norm_num)
theorem B1034549 : Blo 459783 1034549 := bbase (se 5 (by rfl) ⟨48494, by rfl⟩ : syracuseStep 1034549 = 96989) (by norm_num)
theorem B1165661 : Blo 459783 1165661 := bbase (se 3 (by rfl) ⟨218561, by rfl⟩ : syracuseStep 1165661 = 437123) (by norm_num)
theorem B1034621 : Blo 459783 1034621 := bbase (se 3 (by rfl) ⟨193991, by rfl⟩ : syracuseStep 1034621 = 387983) (by norm_num)
theorem B1034693 : Blo 459783 1034693 := bbase (se 4 (by rfl) ⟨97002, by rfl⟩ : syracuseStep 1034693 = 194005) (by norm_num)
theorem B1034765 : Blo 459783 1034765 := bbase (se 3 (by rfl) ⟨194018, by rfl⟩ : syracuseStep 1034765 = 388037) (by norm_num)
theorem B1526293 : Blo 459783 1526293 := bbase (se 6 (by rfl) ⟨35772, by rfl⟩ : syracuseStep 1526293 = 71545) (by norm_num)
theorem B1165853 : Blo 459783 1165853 := bbase (se 3 (by rfl) ⟨218597, by rfl⟩ : syracuseStep 1165853 = 437195) (by norm_num)
theorem B1657397 : Blo 459783 1657397 := bbase (se 5 (by rfl) ⟨77690, by rfl⟩ : syracuseStep 1657397 = 155381) (by norm_num)
theorem B739901 : Blo 459783 739901 := bbase (se 3 (by rfl) ⟨138731, by rfl⟩ : syracuseStep 739901 = 277463) (by norm_num)
theorem B1034837 : Blo 459783 1034837 := bbase (se 8 (by rfl) ⟨6063, by rfl⟩ : syracuseStep 1034837 = 12127) (by norm_num)
theorem B1559141 : Blo 459783 1559141 := bbase (se 4 (by rfl) ⟨146169, by rfl⟩ : syracuseStep 1559141 = 292339) (by norm_num)
theorem B1034909 : Blo 459783 1034909 := bbase (se 3 (by rfl) ⟨194045, by rfl⟩ : syracuseStep 1034909 = 388091) (by norm_num)
theorem B1034981 : Blo 459783 1034981 := bbase (se 4 (by rfl) ⟨97029, by rfl⟩ : syracuseStep 1034981 = 194059) (by norm_num)
theorem B740125 : Blo 459783 740125 := bbase (se 3 (by rfl) ⟨138773, by rfl⟩ : syracuseStep 740125 = 277547) (by norm_num)
theorem B1035053 : Blo 459783 1035053 := bbase (se 3 (by rfl) ⟨194072, by rfl⟩ : syracuseStep 1035053 = 388145) (by norm_num)
theorem B1035125 : Blo 459783 1035125 := bbase (se 5 (by rfl) ⟨48521, by rfl⟩ : syracuseStep 1035125 = 97043) (by norm_num)
theorem B1166197 : Blo 459783 1166197 := bbase (se 5 (by rfl) ⟨54665, by rfl⟩ : syracuseStep 1166197 = 109331) (by norm_num)
theorem B1035197 : Blo 459783 1035197 := bbase (se 3 (by rfl) ⟨194099, by rfl⟩ : syracuseStep 1035197 = 388199) (by norm_num)
theorem B904133 : Blo 459783 904133 := bbase (se 4 (by rfl) ⟨84762, by rfl⟩ : syracuseStep 904133 = 169525) (by norm_num)
theorem B936917 : Blo 459783 936917 := bbase (se 7 (by rfl) ⟨10979, by rfl⟩ : syracuseStep 936917 = 21959) (by norm_num)
theorem B1166309 : Blo 459783 1166309 := bbase (se 4 (by rfl) ⟨109341, by rfl⟩ : syracuseStep 1166309 = 218683) (by norm_num)
theorem B3754997 : Blo 459783 3754997 := bbase (se 5 (by rfl) ⟨176015, by rfl⟩ : syracuseStep 3754997 = 352031) (by norm_num)
theorem B1035269 : Blo 459783 1035269 := bbase (se 4 (by rfl) ⟨97056, by rfl⟩ : syracuseStep 1035269 = 194113) (by norm_num)
theorem B1559573 : Blo 459783 1559573 := bbase (se 6 (by rfl) ⟨36552, by rfl⟩ : syracuseStep 1559573 = 73105) (by norm_num)
theorem B1035341 : Blo 459783 1035341 := bbase (se 3 (by rfl) ⟨194126, by rfl⟩ : syracuseStep 1035341 = 388253) (by norm_num)
theorem B1035413 : Blo 459783 1035413 := bbase (se 6 (by rfl) ⟨24267, by rfl⟩ : syracuseStep 1035413 = 48535) (by norm_num)
theorem B1166501 : Blo 459783 1166501 := bbase (se 4 (by rfl) ⟨109359, by rfl⟩ : syracuseStep 1166501 = 218719) (by norm_num)
theorem B1035485 : Blo 459783 1035485 := bbase (se 3 (by rfl) ⟨194153, by rfl⟩ : syracuseStep 1035485 = 388307) (by norm_num)
theorem B2346245 : Blo 459783 2346245 := bbase (se 4 (by rfl) ⟨219960, by rfl⟩ : syracuseStep 2346245 = 439921) (by norm_num)
theorem B1035557 : Blo 459783 1035557 := bbase (se 4 (by rfl) ⟨97083, by rfl⟩ : syracuseStep 1035557 = 194167) (by norm_num)
theorem B1035629 : Blo 459783 1035629 := bbase (se 3 (by rfl) ⟨194180, by rfl⟩ : syracuseStep 1035629 = 388361) (by norm_num)
theorem B1035701 : Blo 459783 1035701 := bbase (se 5 (by rfl) ⟨48548, by rfl⟩ : syracuseStep 1035701 = 97097) (by norm_num)
theorem B1068485 : Blo 459783 1068485 := bbase (se 4 (by rfl) ⟨100170, by rfl⟩ : syracuseStep 1068485 = 200341) (by norm_num)
theorem B1560005 : Blo 459783 1560005 := bbase (se 4 (by rfl) ⟨146250, by rfl⟩ : syracuseStep 1560005 = 292501) (by norm_num)
theorem B1035773 : Blo 459783 1035773 := bbase (se 3 (by rfl) ⟨194207, by rfl⟩ : syracuseStep 1035773 = 388415) (by norm_num)
theorem B1166845 : Blo 459783 1166845 := bbase (se 3 (by rfl) ⟨218783, by rfl⟩ : syracuseStep 1166845 = 437567) (by norm_num)
theorem B1035845 : Blo 459783 1035845 := bbase (se 4 (by rfl) ⟨97110, by rfl⟩ : syracuseStep 1035845 = 194221) (by norm_num)
theorem B1166957 : Blo 459783 1166957 := bbase (se 3 (by rfl) ⟨218804, by rfl⟩ : syracuseStep 1166957 = 437609) (by norm_num)
theorem B1035917 : Blo 459783 1035917 := bbase (se 3 (by rfl) ⟨194234, by rfl⟩ : syracuseStep 1035917 = 388469) (by norm_num)
theorem B1035989 : Blo 459783 1035989 := bbase (se 7 (by rfl) ⟨12140, by rfl⟩ : syracuseStep 1035989 = 24281) (by norm_num)
theorem B1036061 : Blo 459783 1036061 := bbase (se 3 (by rfl) ⟨194261, by rfl⟩ : syracuseStep 1036061 = 388523) (by norm_num)
theorem B1167149 : Blo 459783 1167149 := bbase (se 3 (by rfl) ⟨218840, by rfl⟩ : syracuseStep 1167149 = 437681) (by norm_num)
theorem B1756997 : Blo 459783 1756997 := bbase (se 4 (by rfl) ⟨164718, by rfl⟩ : syracuseStep 1756997 = 329437) (by norm_num)
theorem B1036133 : Blo 459783 1036133 := bbase (se 4 (by rfl) ⟨97137, by rfl⟩ : syracuseStep 1036133 = 194275) (by norm_num)
theorem B1560437 : Blo 459783 1560437 := bbase (se 5 (by rfl) ⟨73145, by rfl⟩ : syracuseStep 1560437 = 146291) (by norm_num)
theorem B741253 : Blo 459783 741253 := bbase (se 4 (by rfl) ⟨69492, by rfl⟩ : syracuseStep 741253 = 138985) (by norm_num)
theorem B1036205 : Blo 459783 1036205 := bbase (se 3 (by rfl) ⟨194288, by rfl⟩ : syracuseStep 1036205 = 388577) (by norm_num)
theorem B1036277 : Blo 459783 1036277 := bbase (se 5 (by rfl) ⟨48575, by rfl⟩ : syracuseStep 1036277 = 97151) (by norm_num)
theorem B1036349 : Blo 459783 1036349 := bbase (se 3 (by rfl) ⟨194315, by rfl⟩ : syracuseStep 1036349 = 388631) (by norm_num)
theorem B1757285 : Blo 459783 1757285 := bbase (se 4 (by rfl) ⟨164745, by rfl⟩ : syracuseStep 1757285 = 329491) (by norm_num)
theorem B1036421 : Blo 459783 1036421 := bbase (se 4 (by rfl) ⟨97164, by rfl⟩ : syracuseStep 1036421 = 194329) (by norm_num)
theorem B2216069 : Blo 459783 2216069 := bbase (se 4 (by rfl) ⟨207756, by rfl⟩ : syracuseStep 2216069 = 415513) (by norm_num)
theorem B1167493 : Blo 459783 1167493 := bbase (se 4 (by rfl) ⟨109452, by rfl⟩ : syracuseStep 1167493 = 218905) (by norm_num)
theorem B1036493 : Blo 459783 1036493 := bbase (se 3 (by rfl) ⟨194342, by rfl⟩ : syracuseStep 1036493 = 388685) (by norm_num)
theorem B1167605 : Blo 459783 1167605 := bbase (se 5 (by rfl) ⟨54731, by rfl⟩ : syracuseStep 1167605 = 109463) (by norm_num)
theorem B3985685 : Blo 459783 3985685 := bbase (se 6 (by rfl) ⟨93414, by rfl⟩ : syracuseStep 3985685 = 186829) (by norm_num)
theorem B1036565 : Blo 459783 1036565 := bbase (se 6 (by rfl) ⟨24294, by rfl⟩ : syracuseStep 1036565 = 48589) (by norm_num)
theorem B1560869 : Blo 459783 1560869 := bbase (se 4 (by rfl) ⟨146331, by rfl⟩ : syracuseStep 1560869 = 292663) (by norm_num)
theorem B741701 : Blo 459783 741701 := bbase (se 4 (by rfl) ⟨69534, by rfl⟩ : syracuseStep 741701 = 139069) (by norm_num)
theorem B1036637 : Blo 459783 1036637 := bbase (se 3 (by rfl) ⟨194369, by rfl⟩ : syracuseStep 1036637 = 388739) (by norm_num)
theorem B1036709 : Blo 459783 1036709 := bbase (se 4 (by rfl) ⟨97191, by rfl⟩ : syracuseStep 1036709 = 194383) (by norm_num)
theorem B1167797 : Blo 459783 1167797 := bbase (se 5 (by rfl) ⟨54740, by rfl⟩ : syracuseStep 1167797 = 109481) (by norm_num)
theorem B1036781 : Blo 459783 1036781 := bbase (se 3 (by rfl) ⟨194396, by rfl⟩ : syracuseStep 1036781 = 388793) (by norm_num)
theorem B2347541 : Blo 459783 2347541 := bbase (se 6 (by rfl) ⟨55020, by rfl⟩ : syracuseStep 2347541 = 110041) (by norm_num)
theorem B1036853 : Blo 459783 1036853 := bbase (se 5 (by rfl) ⟨48602, by rfl⟩ : syracuseStep 1036853 = 97205) (by norm_num)
theorem B1036925 : Blo 459783 1036925 := bbase (se 3 (by rfl) ⟨194423, by rfl⟩ : syracuseStep 1036925 = 388847) (by norm_num)
theorem B1036997 : Blo 459783 1036997 := bbase (se 4 (by rfl) ⟨97218, by rfl⟩ : syracuseStep 1036997 = 194437) (by norm_num)
theorem B1561301 : Blo 459783 1561301 := bbase (se 7 (by rfl) ⟨18296, by rfl⟩ : syracuseStep 1561301 = 36593) (by norm_num)
theorem B1037069 : Blo 459783 1037069 := bbase (se 3 (by rfl) ⟨194450, by rfl⟩ : syracuseStep 1037069 = 388901) (by norm_num)
theorem B1168141 : Blo 459783 1168141 := bbase (se 3 (by rfl) ⟨219026, by rfl⟩ : syracuseStep 1168141 = 438053) (by norm_num)
theorem B1037141 : Blo 459783 1037141 := bbase (se 9 (by rfl) ⟨3038, by rfl⟩ : syracuseStep 1037141 = 6077) (by norm_num)
theorem B1168253 : Blo 459783 1168253 := bbase (se 3 (by rfl) ⟨219047, by rfl⟩ : syracuseStep 1168253 = 438095) (by norm_num)
theorem B1037213 : Blo 459783 1037213 := bbase (se 3 (by rfl) ⟨194477, by rfl⟩ : syracuseStep 1037213 = 388955) (by norm_num)
theorem B1037285 : Blo 459783 1037285 := bbase (se 4 (by rfl) ⟨97245, by rfl⟩ : syracuseStep 1037285 = 194491) (by norm_num)
theorem B2806805 : Blo 459783 2806805 := bbase (se 6 (by rfl) ⟨65784, by rfl⟩ : syracuseStep 2806805 = 131569) (by norm_num)
theorem B873517 : Blo 459783 873517 := bbase (se 3 (by rfl) ⟨163784, by rfl⟩ : syracuseStep 873517 = 327569) (by norm_num)
theorem B1037357 : Blo 459783 1037357 := bbase (se 3 (by rfl) ⟨194504, by rfl⟩ : syracuseStep 1037357 = 389009) (by norm_num)
theorem B1168445 : Blo 459783 1168445 := bbase (se 3 (by rfl) ⟨219083, by rfl⟩ : syracuseStep 1168445 = 438167) (by norm_num)
theorem B1037429 : Blo 459783 1037429 := bbase (se 5 (by rfl) ⟨48629, by rfl⟩ : syracuseStep 1037429 = 97259) (by norm_num)
theorem B1561733 : Blo 459783 1561733 := bbase (se 4 (by rfl) ⟨146412, by rfl⟩ : syracuseStep 1561733 = 292825) (by norm_num)
theorem B873661 : Blo 459783 873661 := bbase (se 3 (by rfl) ⟨163811, by rfl⟩ : syracuseStep 873661 = 327623) (by norm_num)
theorem B1037501 : Blo 459783 1037501 := bbase (se 3 (by rfl) ⟨194531, by rfl⟩ : syracuseStep 1037501 = 389063) (by norm_num)
theorem B1037573 : Blo 459783 1037573 := bbase (se 4 (by rfl) ⟨97272, by rfl⟩ : syracuseStep 1037573 = 194545) (by norm_num)
theorem B1758469 : Blo 459783 1758469 := bbase (se 4 (by rfl) ⟨164856, by rfl⟩ : syracuseStep 1758469 = 329713) (by norm_num)
theorem B1037645 : Blo 459783 1037645 := bbase (se 3 (by rfl) ⟨194558, by rfl⟩ : syracuseStep 1037645 = 389117) (by norm_num)
theorem B873821 : Blo 459783 873821 := bbase (se 3 (by rfl) ⟨163841, by rfl⟩ : syracuseStep 873821 = 327683) (by norm_num)
theorem B1037717 : Blo 459783 1037717 := bbase (se 6 (by rfl) ⟨24321, by rfl⟩ : syracuseStep 1037717 = 48643) (by norm_num)
theorem B1168789 : Blo 459783 1168789 := bbase (se 6 (by rfl) ⟨27393, by rfl⟩ : syracuseStep 1168789 = 54787) (by norm_num)
theorem B2217413 : Blo 459783 2217413 := bbase (se 4 (by rfl) ⟨207882, by rfl⟩ : syracuseStep 2217413 = 415765) (by norm_num)
theorem B1037789 : Blo 459783 1037789 := bbase (se 3 (by rfl) ⟨194585, by rfl⟩ : syracuseStep 1037789 = 389171) (by norm_num)
theorem B873965 : Blo 459783 873965 := bbase (se 3 (by rfl) ⟨163868, by rfl⟩ : syracuseStep 873965 = 327737) (by norm_num)
theorem B1168901 : Blo 459783 1168901 := bbase (se 4 (by rfl) ⟨109584, by rfl⟩ : syracuseStep 1168901 = 219169) (by norm_num)
theorem B1037861 : Blo 459783 1037861 := bbase (se 4 (by rfl) ⟨97299, by rfl⟩ : syracuseStep 1037861 = 194599) (by norm_num)
theorem B1562165 : Blo 459783 1562165 := bbase (se 5 (by rfl) ⟨73226, by rfl⟩ : syracuseStep 1562165 = 146453) (by norm_num)
theorem B1758773 : Blo 459783 1758773 := bbase (se 5 (by rfl) ⟨82442, by rfl⟩ : syracuseStep 1758773 = 164885) (by norm_num)
theorem B1037933 : Blo 459783 1037933 := bbase (se 3 (by rfl) ⟨194612, by rfl⟩ : syracuseStep 1037933 = 389225) (by norm_num)
theorem B1038005 : Blo 459783 1038005 := bbase (se 5 (by rfl) ⟨48656, by rfl⟩ : syracuseStep 1038005 = 97313) (by norm_num)
theorem B1169093 : Blo 459783 1169093 := bbase (se 4 (by rfl) ⟨109602, by rfl⟩ : syracuseStep 1169093 = 219205) (by norm_num)
theorem B775885 : Blo 459783 775885 := bbase (se 3 (by rfl) ⟨145478, by rfl⟩ : syracuseStep 775885 = 290957) (by norm_num)
theorem B1038077 : Blo 459783 1038077 := bbase (se 3 (by rfl) ⟨194639, by rfl⟩ : syracuseStep 1038077 = 389279) (by norm_num)
theorem B874253 : Blo 459783 874253 := bbase (se 3 (by rfl) ⟨163922, by rfl⟩ : syracuseStep 874253 = 327845) (by norm_num)
theorem B775973 : Blo 459783 775973 := bbase (se 4 (by rfl) ⟨72747, by rfl⟩ : syracuseStep 775973 = 145495) (by norm_num)
theorem B1038149 : Blo 459783 1038149 := bbase (se 4 (by rfl) ⟨97326, by rfl⟩ : syracuseStep 1038149 = 194653) (by norm_num)
theorem B1333061 : Blo 459783 1333061 := bbase (se 4 (by rfl) ⟨124974, by rfl⟩ : syracuseStep 1333061 = 249949) (by norm_num)
theorem B3495797 : Blo 459783 3495797 := bbase (se 5 (by rfl) ⟨163865, by rfl⟩ : syracuseStep 3495797 = 327731) (by norm_num)
theorem B1038221 : Blo 459783 1038221 := bbase (se 3 (by rfl) ⟨194666, by rfl⟩ : syracuseStep 1038221 = 389333) (by norm_num)
theorem B776101 : Blo 459783 776101 := bbase (se 4 (by rfl) ⟨72759, by rfl⟩ : syracuseStep 776101 = 145519) (by norm_num)
theorem B874405 : Blo 459783 874405 := bbase (se 4 (by rfl) ⟨81975, by rfl⟩ : syracuseStep 874405 = 163951) (by norm_num)
theorem B939941 : Blo 459783 939941 := bbase (se 4 (by rfl) ⟨88119, by rfl⟩ : syracuseStep 939941 = 176239) (by norm_num)
theorem B1038293 : Blo 459783 1038293 := bbase (se 7 (by rfl) ⟨12167, by rfl⟩ : syracuseStep 1038293 = 24335) (by norm_num)
theorem B1562597 : Blo 459783 1562597 := bbase (se 4 (by rfl) ⟨146493, by rfl⟩ : syracuseStep 1562597 = 292987) (by norm_num)
theorem B776189 : Blo 459783 776189 := bbase (se 3 (by rfl) ⟨145535, by rfl⟩ : syracuseStep 776189 = 291071) (by norm_num)
theorem B3332117 : Blo 459783 3332117 := bbase (se 6 (by rfl) ⟨78096, by rfl⟩ : syracuseStep 3332117 = 156193) (by norm_num)
theorem B1038365 : Blo 459783 1038365 := bbase (se 3 (by rfl) ⟨194693, by rfl⟩ : syracuseStep 1038365 = 389387) (by norm_num)
theorem B1169437 : Blo 459783 1169437 := bbase (se 3 (by rfl) ⟨219269, by rfl⟩ : syracuseStep 1169437 = 438539) (by norm_num)
theorem B1038437 : Blo 459783 1038437 := bbase (se 4 (by rfl) ⟨97353, by rfl⟩ : syracuseStep 1038437 = 194707) (by norm_num)
theorem B776317 : Blo 459783 776317 := bbase (se 3 (by rfl) ⟨145559, by rfl⟩ : syracuseStep 776317 = 291119) (by norm_num)
theorem B1169549 : Blo 459783 1169549 := bbase (se 3 (by rfl) ⟨219290, by rfl⟩ : syracuseStep 1169549 = 438581) (by norm_num)
theorem B1038509 : Blo 459783 1038509 := bbase (se 3 (by rfl) ⟨194720, by rfl⟩ : syracuseStep 1038509 = 389441) (by norm_num)
theorem B776405 : Blo 459783 776405 := bbase (se 7 (by rfl) ⟨9098, by rfl⟩ : syracuseStep 776405 = 18197) (by norm_num)
theorem B874709 : Blo 459783 874709 := bbase (se 7 (by rfl) ⟨10250, by rfl⟩ : syracuseStep 874709 = 20501) (by norm_num)
theorem B1038581 : Blo 459783 1038581 := bbase (se 5 (by rfl) ⟨48683, by rfl⟩ : syracuseStep 1038581 = 97367) (by norm_num)
theorem B1038653 : Blo 459783 1038653 := bbase (se 3 (by rfl) ⟨194747, by rfl⟩ : syracuseStep 1038653 = 389495) (by norm_num)
theorem B1169741 : Blo 459783 1169741 := bbase (se 3 (by rfl) ⟨219326, by rfl⟩ : syracuseStep 1169741 = 438653) (by norm_num)
theorem B776533 : Blo 459783 776533 := bbase (se 10 (by rfl) ⟨1137, by rfl⟩ : syracuseStep 776533 = 2275) (by norm_num)
theorem B1038725 : Blo 459783 1038725 := bbase (se 4 (by rfl) ⟨97380, by rfl⟩ : syracuseStep 1038725 = 194761) (by norm_num)
theorem B1563029 : Blo 459783 1563029 := bbase (se 6 (by rfl) ⟨36633, by rfl⟩ : syracuseStep 1563029 = 73267) (by norm_num)
theorem B776621 : Blo 459783 776621 := bbase (se 3 (by rfl) ⟨145616, by rfl⟩ : syracuseStep 776621 = 291233) (by norm_num)
theorem B1038797 : Blo 459783 1038797 := bbase (se 3 (by rfl) ⟨194774, by rfl⟩ : syracuseStep 1038797 = 389549) (by norm_num)
theorem B3955189 : Blo 459783 3955189 := bbase (se 5 (by rfl) ⟨185399, by rfl⟩ : syracuseStep 3955189 = 370799) (by norm_num)
theorem B1038869 : Blo 459783 1038869 := bbase (se 6 (by rfl) ⟨24348, by rfl⟩ : syracuseStep 1038869 = 48697) (by norm_num)
theorem B776749 : Blo 459783 776749 := bbase (se 3 (by rfl) ⟨145640, by rfl⟩ : syracuseStep 776749 = 291281) (by norm_num)
theorem B1038941 : Blo 459783 1038941 := bbase (se 3 (by rfl) ⟨194801, by rfl⟩ : syracuseStep 1038941 = 389603) (by norm_num)
theorem B776837 : Blo 459783 776837 := bbase (se 4 (by rfl) ⟨72828, by rfl⟩ : syracuseStep 776837 = 145657) (by norm_num)
theorem B1039013 : Blo 459783 1039013 := bbase (se 4 (by rfl) ⟨97407, by rfl⟩ : syracuseStep 1039013 = 194815) (by norm_num)
theorem B1170085 : Blo 459783 1170085 := bbase (se 4 (by rfl) ⟨109695, by rfl⟩ : syracuseStep 1170085 = 219391) (by norm_num)
theorem B1039085 : Blo 459783 1039085 := bbase (se 3 (by rfl) ⟨194828, by rfl⟩ : syracuseStep 1039085 = 389657) (by norm_num)
theorem B776965 : Blo 459783 776965 := bbase (se 4 (by rfl) ⟨72840, by rfl⟩ : syracuseStep 776965 = 145681) (by norm_num)
theorem B1170197 : Blo 459783 1170197 := bbase (se 6 (by rfl) ⟨27426, by rfl⟩ : syracuseStep 1170197 = 54853) (by norm_num)
theorem B1039157 : Blo 459783 1039157 := bbase (se 5 (by rfl) ⟨48710, by rfl⟩ : syracuseStep 1039157 = 97421) (by norm_num)
theorem B1563461 : Blo 459783 1563461 := bbase (se 4 (by rfl) ⟨146574, by rfl⟩ : syracuseStep 1563461 = 293149) (by norm_num)
theorem B777053 : Blo 459783 777053 := bbase (se 3 (by rfl) ⟨145697, by rfl⟩ : syracuseStep 777053 = 291395) (by norm_num)
theorem B1039229 : Blo 459783 1039229 := bbase (se 3 (by rfl) ⟨194855, by rfl⟩ : syracuseStep 1039229 = 389711) (by norm_num)
theorem B875461 : Blo 459783 875461 := bbase (se 4 (by rfl) ⟨82074, by rfl⟩ : syracuseStep 875461 = 164149) (by norm_num)
theorem B1039301 : Blo 459783 1039301 := bbase (se 4 (by rfl) ⟨97434, by rfl⟩ : syracuseStep 1039301 = 194869) (by norm_num)
theorem B1170389 : Blo 459783 1170389 := bbase (se 7 (by rfl) ⟨13715, by rfl⟩ : syracuseStep 1170389 = 27431) (by norm_num)
theorem B777181 : Blo 459783 777181 := bbase (se 3 (by rfl) ⟨145721, by rfl⟩ : syracuseStep 777181 = 291443) (by norm_num)
theorem B1039373 : Blo 459783 1039373 := bbase (se 3 (by rfl) ⟨194882, by rfl⟩ : syracuseStep 1039373 = 389765) (by norm_num)
theorem B777269 : Blo 459783 777269 := bbase (se 5 (by rfl) ⟨36434, by rfl⟩ : syracuseStep 777269 = 72869) (by norm_num)
theorem B875605 : Blo 459783 875605 := bbase (se 8 (by rfl) ⟨5130, by rfl⟩ : syracuseStep 875605 = 10261) (by norm_num)
theorem B1039445 : Blo 459783 1039445 := bbase (se 8 (by rfl) ⟨6090, by rfl⟩ : syracuseStep 1039445 = 12181) (by norm_num)
theorem B2841749 : Blo 459783 2841749 := bbase (se 6 (by rfl) ⟨66603, by rfl⟩ : syracuseStep 2841749 = 133207) (by norm_num)
theorem B1039517 : Blo 459783 1039517 := bbase (se 3 (by rfl) ⟨194909, by rfl⟩ : syracuseStep 1039517 = 389819) (by norm_num)
theorem B777397 : Blo 459783 777397 := bbase (se 5 (by rfl) ⟨36440, by rfl⟩ : syracuseStep 777397 = 72881) (by norm_num)
theorem B1105085 : Blo 459783 1105085 := bbase (se 3 (by rfl) ⟨207203, by rfl⟩ : syracuseStep 1105085 = 414407) (by norm_num)
theorem B1105093 : Blo 459783 1105093 := bbase (se 4 (by rfl) ⟨103602, by rfl⟩ : syracuseStep 1105093 = 207205) (by norm_num)
theorem B1039589 : Blo 459783 1039589 := bbase (se 4 (by rfl) ⟨97461, by rfl⟩ : syracuseStep 1039589 = 194923) (by norm_num)
theorem B875765 : Blo 459783 875765 := bbase (se 5 (by rfl) ⟨41051, by rfl⟩ : syracuseStep 875765 = 82103) (by norm_num)
theorem B1563893 : Blo 459783 1563893 := bbase (se 5 (by rfl) ⟨73307, by rfl⟩ : syracuseStep 1563893 = 146615) (by norm_num)
theorem B777485 : Blo 459783 777485 := bbase (se 3 (by rfl) ⟨145778, by rfl⟩ : syracuseStep 777485 = 291557) (by norm_num)
theorem B1039661 : Blo 459783 1039661 := bbase (se 3 (by rfl) ⟨194936, by rfl⟩ : syracuseStep 1039661 = 389873) (by norm_num)
theorem B1170733 : Blo 459783 1170733 := bbase (se 3 (by rfl) ⟨219512, by rfl⟩ : syracuseStep 1170733 = 439025) (by norm_num)
theorem B1039733 : Blo 459783 1039733 := bbase (se 5 (by rfl) ⟨48737, by rfl⟩ : syracuseStep 1039733 = 97475) (by norm_num)
theorem B875909 : Blo 459783 875909 := bbase (se 4 (by rfl) ⟨82116, by rfl⟩ : syracuseStep 875909 = 164233) (by norm_num)
theorem B777613 : Blo 459783 777613 := bbase (se 3 (by rfl) ⟨145802, by rfl⟩ : syracuseStep 777613 = 291605) (by norm_num)
theorem B2219413 : Blo 459783 2219413 := bbase (se 6 (by rfl) ⟨52017, by rfl⟩ : syracuseStep 2219413 = 104035) (by norm_num)
theorem B1170845 : Blo 459783 1170845 := bbase (se 3 (by rfl) ⟨219533, by rfl⟩ : syracuseStep 1170845 = 439067) (by norm_num)
theorem B1039805 : Blo 459783 1039805 := bbase (se 3 (by rfl) ⟨194963, by rfl⟩ : syracuseStep 1039805 = 389927) (by norm_num)
theorem B777701 : Blo 459783 777701 := bbase (se 4 (by rfl) ⟨72909, by rfl⟩ : syracuseStep 777701 = 145819) (by norm_num)
theorem B1924597 : Blo 459783 1924597 := bbase (se 5 (by rfl) ⟨90215, by rfl⟩ : syracuseStep 1924597 = 180431) (by norm_num)
theorem B1039877 : Blo 459783 1039877 := bbase (se 4 (by rfl) ⟨97488, by rfl⟩ : syracuseStep 1039877 = 194977) (by norm_num)
theorem B1039949 : Blo 459783 1039949 := bbase (se 3 (by rfl) ⟨194990, by rfl⟩ : syracuseStep 1039949 = 389981) (by norm_num)
theorem B1171037 : Blo 459783 1171037 := bbase (se 3 (by rfl) ⟨219569, by rfl⟩ : syracuseStep 1171037 = 439139) (by norm_num)
theorem B777829 : Blo 459783 777829 := bbase (se 4 (by rfl) ⟨72921, by rfl⟩ : syracuseStep 777829 = 145843) (by norm_num)
theorem B1760885 : Blo 459783 1760885 := bbase (se 5 (by rfl) ⟨82541, by rfl⟩ : syracuseStep 1760885 = 165083) (by norm_num)
theorem B1040021 : Blo 459783 1040021 := bbase (se 6 (by rfl) ⟨24375, by rfl⟩ : syracuseStep 1040021 = 48751) (by norm_num)
theorem B876197 : Blo 459783 876197 := bbase (se 4 (by rfl) ⟨82143, by rfl⟩ : syracuseStep 876197 = 164287) (by norm_num)
theorem B1564325 : Blo 459783 1564325 := bbase (se 4 (by rfl) ⟨146655, by rfl⟩ : syracuseStep 1564325 = 293311) (by norm_num)
theorem B2088629 : Blo 459783 2088629 := bbase (se 5 (by rfl) ⟨97904, by rfl⟩ : syracuseStep 2088629 = 195809) (by norm_num)
theorem B777917 : Blo 459783 777917 := bbase (se 3 (by rfl) ⟨145859, by rfl⟩ : syracuseStep 777917 = 291719) (by norm_num)
theorem B6676181 : Blo 459783 6676181 := bbase (se 7 (by rfl) ⟨78236, by rfl⟩ : syracuseStep 6676181 = 156473) (by norm_num)
theorem B1040093 : Blo 459783 1040093 := bbase (se 3 (by rfl) ⟨195017, by rfl⟩ : syracuseStep 1040093 = 390035) (by norm_num)
theorem B1040165 : Blo 459783 1040165 := bbase (se 4 (by rfl) ⟨97515, by rfl⟩ : syracuseStep 1040165 = 195031) (by norm_num)
theorem B778045 : Blo 459783 778045 := bbase (se 3 (by rfl) ⟨145883, by rfl⟩ : syracuseStep 778045 = 291767) (by norm_num)
theorem B876349 : Blo 459783 876349 := bbase (se 3 (by rfl) ⟨164315, by rfl⟩ : syracuseStep 876349 = 328631) (by norm_num)
theorem B1892165 : Blo 459783 1892165 := bbase (se 4 (by rfl) ⟨177390, by rfl⟩ : syracuseStep 1892165 = 354781) (by norm_num)
theorem B1040237 : Blo 459783 1040237 := bbase (se 3 (by rfl) ⟨195044, by rfl⟩ : syracuseStep 1040237 = 390089) (by norm_num)
theorem B778133 : Blo 459783 778133 := bbase (se 6 (by rfl) ⟨18237, by rfl⟩ : syracuseStep 778133 = 36475) (by norm_num)
theorem B1040309 : Blo 459783 1040309 := bbase (se 5 (by rfl) ⟨48764, by rfl⟩ : syracuseStep 1040309 = 97529) (by norm_num)
theorem B1171381 : Blo 459783 1171381 := bbase (se 5 (by rfl) ⟨54908, by rfl⟩ : syracuseStep 1171381 = 109817) (by norm_num)
theorem B1105901 : Blo 459783 1105901 := bbase (se 3 (by rfl) ⟨207356, by rfl⟩ : syracuseStep 1105901 = 414713) (by norm_num)
theorem B1040381 : Blo 459783 1040381 := bbase (se 3 (by rfl) ⟨195071, by rfl⟩ : syracuseStep 1040381 = 390143) (by norm_num)
theorem B778261 : Blo 459783 778261 := bbase (se 6 (by rfl) ⟨18240, by rfl⟩ : syracuseStep 778261 = 36481) (by norm_num)
theorem B1171493 : Blo 459783 1171493 := bbase (se 4 (by rfl) ⟨109827, by rfl⟩ : syracuseStep 1171493 = 219655) (by norm_num)
theorem B1040453 : Blo 459783 1040453 := bbase (se 4 (by rfl) ⟨97542, by rfl⟩ : syracuseStep 1040453 = 195085) (by norm_num)
theorem B1564757 : Blo 459783 1564757 := bbase (se 8 (by rfl) ⟨9168, by rfl⟩ : syracuseStep 1564757 = 18337) (by norm_num)
theorem B778349 : Blo 459783 778349 := bbase (se 3 (by rfl) ⟨145940, by rfl⟩ : syracuseStep 778349 = 291881) (by norm_num)
theorem B876653 : Blo 459783 876653 := bbase (se 3 (by rfl) ⟨164372, by rfl⟩ : syracuseStep 876653 = 328745) (by norm_num)
theorem B1040525 : Blo 459783 1040525 := bbase (se 3 (by rfl) ⟨195098, by rfl⟩ : syracuseStep 1040525 = 390197) (by norm_num)
theorem B1040597 : Blo 459783 1040597 := bbase (se 7 (by rfl) ⟨12194, by rfl⟩ : syracuseStep 1040597 = 24389) (by norm_num)
theorem B1171685 : Blo 459783 1171685 := bbase (se 4 (by rfl) ⟨109845, by rfl⟩ : syracuseStep 1171685 = 219691) (by norm_num)
theorem B778477 : Blo 459783 778477 := bbase (se 3 (by rfl) ⟨145964, by rfl⟩ : syracuseStep 778477 = 291929) (by norm_num)
theorem B1040669 : Blo 459783 1040669 := bbase (se 3 (by rfl) ⟨195125, by rfl⟩ : syracuseStep 1040669 = 390251) (by norm_num)
theorem B778565 : Blo 459783 778565 := bbase (se 4 (by rfl) ⟨72990, by rfl⟩ : syracuseStep 778565 = 145981) (by norm_num)
theorem B1040741 : Blo 459783 1040741 := bbase (se 4 (by rfl) ⟨97569, by rfl⟩ : syracuseStep 1040741 = 195139) (by norm_num)
theorem B582005 : Blo 459783 582005 := bbase (se 5 (by rfl) ⟨27281, by rfl⟩ : syracuseStep 582005 = 54563) (by norm_num)
theorem B582061 : Blo 459783 582061 := bbase (se 3 (by rfl) ⟨109136, by rfl⟩ : syracuseStep 582061 = 218273) (by norm_num)
theorem B1040813 : Blo 459783 1040813 := bbase (se 3 (by rfl) ⟨195152, by rfl⟩ : syracuseStep 1040813 = 390305) (by norm_num)
theorem B3957173 : Blo 459783 3957173 := bbase (se 5 (by rfl) ⟨185492, by rfl⟩ : syracuseStep 3957173 = 370985) (by norm_num)
theorem B778693 : Blo 459783 778693 := bbase (se 4 (by rfl) ⟨73002, by rfl⟩ : syracuseStep 778693 = 146005) (by norm_num)
theorem B1040885 : Blo 459783 1040885 := bbase (se 5 (by rfl) ⟨48791, by rfl⟩ : syracuseStep 1040885 = 97583) (by norm_num)
theorem B1565189 : Blo 459783 1565189 := bbase (se 4 (by rfl) ⟨146736, by rfl⟩ : syracuseStep 1565189 = 293473) (by norm_num)
theorem B582157 : Blo 459783 582157 := bbase (se 3 (by rfl) ⟨109154, by rfl⟩ : syracuseStep 582157 = 218309) (by norm_num)
theorem B778781 : Blo 459783 778781 := bbase (se 3 (by rfl) ⟨146021, by rfl⟩ : syracuseStep 778781 = 292043) (by norm_num)
theorem B1040957 : Blo 459783 1040957 := bbase (se 3 (by rfl) ⟨195179, by rfl⟩ : syracuseStep 1040957 = 390359) (by norm_num)
theorem B1172029 : Blo 459783 1172029 := bbase (se 3 (by rfl) ⟨219755, by rfl⟩ : syracuseStep 1172029 = 439511) (by norm_num)
theorem B1041029 : Blo 459783 1041029 := bbase (se 4 (by rfl) ⟨97596, by rfl⟩ : syracuseStep 1041029 = 195193) (by norm_num)
theorem B778909 : Blo 459783 778909 := bbase (se 3 (by rfl) ⟨146045, by rfl⟩ : syracuseStep 778909 = 292091) (by norm_num)
theorem B1172141 : Blo 459783 1172141 := bbase (se 3 (by rfl) ⟨219776, by rfl⟩ : syracuseStep 1172141 = 439553) (by norm_num)
theorem B582329 : Blo 459783 582329 := bbase (se 2 (by rfl) ⟨218373, by rfl⟩ : syracuseStep 582329 = 436747) (by norm_num)
theorem B1041101 : Blo 459783 1041101 := bbase (se 3 (by rfl) ⟨195206, by rfl⟩ : syracuseStep 1041101 = 390413) (by norm_num)
theorem B582385 : Blo 459783 582385 := bbase (se 2 (by rfl) ⟨218394, by rfl⟩ : syracuseStep 582385 = 436789) (by norm_num)
theorem B778997 : Blo 459783 778997 := bbase (se 5 (by rfl) ⟨36515, by rfl⟩ : syracuseStep 778997 = 73031) (by norm_num)
theorem B1041173 : Blo 459783 1041173 := bbase (se 6 (by rfl) ⟨24402, by rfl⟩ : syracuseStep 1041173 = 48805) (by norm_num)
theorem B582481 : Blo 459783 582481 := bbase (se 2 (by rfl) ⟨218430, by rfl⟩ : syracuseStep 582481 = 436861) (by norm_num)
theorem B877405 : Blo 459783 877405 := bbase (se 3 (by rfl) ⟨164513, by rfl⟩ : syracuseStep 877405 = 329027) (by norm_num)
theorem B1041245 : Blo 459783 1041245 := bbase (se 3 (by rfl) ⟨195233, by rfl⟩ : syracuseStep 1041245 = 390467) (by norm_num)
theorem B1172333 : Blo 459783 1172333 := bbase (se 3 (by rfl) ⟨219812, by rfl⟩ : syracuseStep 1172333 = 439625) (by norm_num)
theorem B779125 : Blo 459783 779125 := bbase (se 5 (by rfl) ⟨36521, by rfl⟩ : syracuseStep 779125 = 73043) (by norm_num)
theorem B1041317 : Blo 459783 1041317 := bbase (se 4 (by rfl) ⟨97623, by rfl⟩ : syracuseStep 1041317 = 195247) (by norm_num)
theorem B3335093 : Blo 459783 3335093 := bbase (se 5 (by rfl) ⟨156332, by rfl⟩ : syracuseStep 3335093 = 312665) (by norm_num)
theorem B779213 : Blo 459783 779213 := bbase (se 3 (by rfl) ⟨146102, by rfl⟩ : syracuseStep 779213 = 292205) (by norm_num)
theorem B877549 : Blo 459783 877549 := bbase (se 3 (by rfl) ⟨164540, by rfl⟩ : syracuseStep 877549 = 329081) (by norm_num)
theorem B1041389 : Blo 459783 1041389 := bbase (se 3 (by rfl) ⟨195260, by rfl⟩ : syracuseStep 1041389 = 390521) (by norm_num)
theorem B582653 : Blo 459783 582653 := bbase (se 3 (by rfl) ⟨109247, by rfl⟩ : syracuseStep 582653 = 218495) (by norm_num)
theorem B582709 : Blo 459783 582709 := bbase (se 5 (by rfl) ⟨27314, by rfl⟩ : syracuseStep 582709 = 54629) (by norm_num)
theorem B1041461 : Blo 459783 1041461 := bbase (se 5 (by rfl) ⟨48818, by rfl⟩ : syracuseStep 1041461 = 97637) (by norm_num)
theorem B779341 : Blo 459783 779341 := bbase (se 3 (by rfl) ⟨146126, by rfl⟩ : syracuseStep 779341 = 292253) (by norm_num)
theorem B1041533 : Blo 459783 1041533 := bbase (se 3 (by rfl) ⟨195287, by rfl⟩ : syracuseStep 1041533 = 390575) (by norm_num)
theorem B517261 : Blo 459783 517261 := bbase (se 3 (by rfl) ⟨96986, by rfl⟩ : syracuseStep 517261 = 193973) (by norm_num)
theorem B877709 : Blo 459783 877709 := bbase (se 3 (by rfl) ⟨164570, by rfl⟩ : syracuseStep 877709 = 329141) (by norm_num)
theorem B582805 : Blo 459783 582805 := bbase (se 6 (by rfl) ⟨13659, by rfl⟩ : syracuseStep 582805 = 27319) (by norm_num)
theorem B779429 : Blo 459783 779429 := bbase (se 4 (by rfl) ⟨73071, by rfl⟩ : syracuseStep 779429 = 146143) (by norm_num)
theorem B517297 : Blo 459783 517297 := bbase (se 2 (by rfl) ⟨193986, by rfl⟩ : syracuseStep 517297 = 387973) (by norm_num)
theorem B1041605 : Blo 459783 1041605 := bbase (se 4 (by rfl) ⟨97650, by rfl⟩ : syracuseStep 1041605 = 195301) (by norm_num)
theorem B1172677 : Blo 459783 1172677 := bbase (se 4 (by rfl) ⟨109938, by rfl⟩ : syracuseStep 1172677 = 219877) (by norm_num)
theorem B517333 : Blo 459783 517333 := bbase (se 7 (by rfl) ⟨6062, by rfl⟩ : syracuseStep 517333 = 12125) (by norm_num)
theorem B517369 : Blo 459783 517369 := bbase (se 2 (by rfl) ⟨194013, by rfl⟩ : syracuseStep 517369 = 388027) (by norm_num)
theorem B1041677 : Blo 459783 1041677 := bbase (se 3 (by rfl) ⟨195314, by rfl⟩ : syracuseStep 1041677 = 390629) (by norm_num)
theorem B517405 : Blo 459783 517405 := bbase (se 3 (by rfl) ⟨97013, by rfl⟩ : syracuseStep 517405 = 194027) (by norm_num)
theorem B877853 : Blo 459783 877853 := bbase (se 3 (by rfl) ⟨164597, by rfl⟩ : syracuseStep 877853 = 329195) (by norm_num)
theorem B779557 : Blo 459783 779557 := bbase (se 4 (by rfl) ⟨73083, by rfl⟩ : syracuseStep 779557 = 146167) (by norm_num)
theorem B1172789 : Blo 459783 1172789 := bbase (se 5 (by rfl) ⟨54974, by rfl⟩ : syracuseStep 1172789 = 109949) (by norm_num)
theorem B517441 : Blo 459783 517441 := bbase (se 2 (by rfl) ⟨194040, by rfl⟩ : syracuseStep 517441 = 388081) (by norm_num)
theorem B582977 : Blo 459783 582977 := bbase (se 2 (by rfl) ⟨218616, by rfl⟩ : syracuseStep 582977 = 437233) (by norm_num)
theorem B1041749 : Blo 459783 1041749 := bbase (se 12 (by rfl) ⟨381, by rfl⟩ : syracuseStep 1041749 = 763) (by norm_num)
theorem B517477 : Blo 459783 517477 := bbase (se 4 (by rfl) ⟨48513, by rfl⟩ : syracuseStep 517477 = 97027) (by norm_num)
theorem B714101 : Blo 459783 714101 := bbase (se 5 (by rfl) ⟨33473, by rfl⟩ : syracuseStep 714101 = 66947) (by norm_num)
theorem B583033 : Blo 459783 583033 := bbase (se 2 (by rfl) ⟨218637, by rfl⟩ : syracuseStep 583033 = 437275) (by norm_num)
theorem B779645 : Blo 459783 779645 := bbase (se 3 (by rfl) ⟨146183, by rfl⟩ : syracuseStep 779645 = 292367) (by norm_num)
theorem B517513 : Blo 459783 517513 := bbase (se 2 (by rfl) ⟨194067, by rfl⟩ : syracuseStep 517513 = 388135) (by norm_num)
theorem B1041821 : Blo 459783 1041821 := bbase (se 3 (by rfl) ⟨195341, by rfl⟩ : syracuseStep 1041821 = 390683) (by norm_num)
theorem B517549 : Blo 459783 517549 := bbase (se 3 (by rfl) ⟨97040, by rfl⟩ : syracuseStep 517549 = 194081) (by norm_num)
theorem B517585 : Blo 459783 517585 := bbase (se 2 (by rfl) ⟨194094, by rfl⟩ : syracuseStep 517585 = 388189) (by norm_num)
theorem B583129 : Blo 459783 583129 := bbase (se 2 (by rfl) ⟨218673, by rfl⟩ : syracuseStep 583129 = 437347) (by norm_num)
theorem B1041893 : Blo 459783 1041893 := bbase (se 4 (by rfl) ⟨97677, by rfl⟩ : syracuseStep 1041893 = 195355) (by norm_num)
theorem B517621 : Blo 459783 517621 := bbase (se 5 (by rfl) ⟨24263, by rfl⟩ : syracuseStep 517621 = 48527) (by norm_num)
theorem B1172981 : Blo 459783 1172981 := bbase (se 5 (by rfl) ⟨54983, by rfl⟩ : syracuseStep 1172981 = 109967) (by norm_num)
theorem B779773 : Blo 459783 779773 := bbase (se 3 (by rfl) ⟨146207, by rfl⟩ : syracuseStep 779773 = 292415) (by norm_num)
theorem B517657 : Blo 459783 517657 := bbase (se 2 (by rfl) ⟨194121, by rfl⟩ : syracuseStep 517657 = 388243) (by norm_num)
theorem B1041965 : Blo 459783 1041965 := bbase (se 3 (by rfl) ⟨195368, by rfl⟩ : syracuseStep 1041965 = 390737) (by norm_num)
theorem B517693 : Blo 459783 517693 := bbase (se 3 (by rfl) ⟨97067, by rfl⟩ : syracuseStep 517693 = 194135) (by norm_num)
theorem B878141 : Blo 459783 878141 := bbase (se 3 (by rfl) ⟨164651, by rfl⟩ : syracuseStep 878141 = 329303) (by norm_num)
theorem B779861 : Blo 459783 779861 := bbase (se 8 (by rfl) ⟨4569, by rfl⟩ : syracuseStep 779861 = 9139) (by norm_num)
theorem B517729 : Blo 459783 517729 := bbase (se 2 (by rfl) ⟨194148, by rfl⟩ : syracuseStep 517729 = 388297) (by norm_num)
theorem B1042037 : Blo 459783 1042037 := bbase (se 5 (by rfl) ⟨48845, by rfl⟩ : syracuseStep 1042037 = 97691) (by norm_num)
theorem B517765 : Blo 459783 517765 := bbase (se 4 (by rfl) ⟨48540, by rfl⟩ : syracuseStep 517765 = 97081) (by norm_num)
theorem B583301 : Blo 459783 583301 := bbase (se 4 (by rfl) ⟨54684, by rfl⟩ : syracuseStep 583301 = 109369) (by norm_num)
theorem B1402517 : Blo 459783 1402517 := bbase (se 6 (by rfl) ⟨32871, by rfl⟩ : syracuseStep 1402517 = 65743) (by norm_num)
theorem B517801 : Blo 459783 517801 := bbase (se 2 (by rfl) ⟨194175, by rfl⟩ : syracuseStep 517801 = 388351) (by norm_num)
theorem B583357 : Blo 459783 583357 := bbase (se 3 (by rfl) ⟨109379, by rfl⟩ : syracuseStep 583357 = 218759) (by norm_num)
theorem B1042109 : Blo 459783 1042109 := bbase (se 3 (by rfl) ⟨195395, by rfl⟩ : syracuseStep 1042109 = 390791) (by norm_num)
theorem B517837 : Blo 459783 517837 := bbase (se 3 (by rfl) ⟨97094, by rfl⟩ : syracuseStep 517837 = 194189) (by norm_num)
theorem B779989 : Blo 459783 779989 := bbase (se 7 (by rfl) ⟨9140, by rfl⟩ : syracuseStep 779989 = 18281) (by norm_num)
theorem B878293 : Blo 459783 878293 := bbase (se 7 (by rfl) ⟨10292, by rfl⟩ : syracuseStep 878293 = 20585) (by norm_num)
theorem B517873 : Blo 459783 517873 := bbase (se 2 (by rfl) ⟨194202, by rfl⟩ : syracuseStep 517873 = 388405) (by norm_num)
theorem B1042181 : Blo 459783 1042181 := bbase (se 4 (by rfl) ⟨97704, by rfl⟩ : syracuseStep 1042181 = 195409) (by norm_num)
theorem B517909 : Blo 459783 517909 := bbase (se 6 (by rfl) ⟨12138, by rfl⟩ : syracuseStep 517909 = 24277) (by norm_num)
theorem B583453 : Blo 459783 583453 := bbase (se 3 (by rfl) ⟨109397, by rfl⟩ : syracuseStep 583453 = 218795) (by norm_num)
theorem B780077 : Blo 459783 780077 := bbase (se 3 (by rfl) ⟨146264, by rfl⟩ : syracuseStep 780077 = 292529) (by norm_num)
theorem B517945 : Blo 459783 517945 := bbase (se 2 (by rfl) ⟨194229, by rfl⟩ : syracuseStep 517945 = 388459) (by norm_num)
theorem B1042253 : Blo 459783 1042253 := bbase (se 3 (by rfl) ⟨195422, by rfl⟩ : syracuseStep 1042253 = 390845) (by norm_num)
theorem B1173325 : Blo 459783 1173325 := bbase (se 3 (by rfl) ⟨219998, by rfl⟩ : syracuseStep 1173325 = 439997) (by norm_num)
theorem B517981 : Blo 459783 517981 := bbase (se 3 (by rfl) ⟨97121, by rfl⟩ : syracuseStep 517981 = 194243) (by norm_num)
theorem B518017 : Blo 459783 518017 := bbase (se 2 (by rfl) ⟨194256, by rfl⟩ : syracuseStep 518017 = 388513) (by norm_num)
theorem B1042325 : Blo 459783 1042325 := bbase (se 6 (by rfl) ⟨24429, by rfl⟩ : syracuseStep 1042325 = 48859) (by norm_num)
theorem B518053 : Blo 459783 518053 := bbase (se 4 (by rfl) ⟨48567, by rfl⟩ : syracuseStep 518053 = 97135) (by norm_num)
theorem B780205 : Blo 459783 780205 := bbase (se 3 (by rfl) ⟨146288, by rfl⟩ : syracuseStep 780205 = 292577) (by norm_num)
theorem B845741 : Blo 459783 845741 := bbase (se 3 (by rfl) ⟨158576, by rfl⟩ : syracuseStep 845741 = 317153) (by norm_num)
theorem B1173437 : Blo 459783 1173437 := bbase (se 3 (by rfl) ⟨220019, by rfl⟩ : syracuseStep 1173437 = 440039) (by norm_num)
theorem B518089 : Blo 459783 518089 := bbase (se 2 (by rfl) ⟨194283, by rfl⟩ : syracuseStep 518089 = 388567) (by norm_num)
theorem B583625 : Blo 459783 583625 := bbase (se 2 (by rfl) ⟨218859, by rfl⟩ : syracuseStep 583625 = 437719) (by norm_num)
theorem B1042397 : Blo 459783 1042397 := bbase (se 3 (by rfl) ⟨195449, by rfl⟩ : syracuseStep 1042397 = 390899) (by norm_num)
theorem B518125 : Blo 459783 518125 := bbase (se 3 (by rfl) ⟨97148, by rfl⟩ : syracuseStep 518125 = 194297) (by norm_num)
theorem B583681 : Blo 459783 583681 := bbase (se 2 (by rfl) ⟨218880, by rfl⟩ : syracuseStep 583681 = 437761) (by norm_num)
theorem B780293 : Blo 459783 780293 := bbase (se 4 (by rfl) ⟨73152, by rfl⟩ : syracuseStep 780293 = 146305) (by norm_num)
theorem B878597 : Blo 459783 878597 := bbase (se 4 (by rfl) ⟨82368, by rfl⟩ : syracuseStep 878597 = 164737) (by norm_num)
theorem B518161 : Blo 459783 518161 := bbase (se 2 (by rfl) ⟨194310, by rfl⟩ : syracuseStep 518161 = 388621) (by norm_num)
theorem B1042469 : Blo 459783 1042469 := bbase (se 4 (by rfl) ⟨97731, by rfl⟩ : syracuseStep 1042469 = 195463) (by norm_num)
theorem B518197 : Blo 459783 518197 := bbase (se 5 (by rfl) ⟨24290, by rfl⟩ : syracuseStep 518197 = 48581) (by norm_num)
theorem B518233 : Blo 459783 518233 := bbase (se 2 (by rfl) ⟨194337, by rfl⟩ : syracuseStep 518233 = 388675) (by norm_num)
theorem B583777 : Blo 459783 583777 := bbase (se 2 (by rfl) ⟨218916, by rfl⟩ : syracuseStep 583777 = 437833) (by norm_num)
theorem B1042541 : Blo 459783 1042541 := bbase (se 3 (by rfl) ⟨195476, by rfl⟩ : syracuseStep 1042541 = 390953) (by norm_num)
theorem B518269 : Blo 459783 518269 := bbase (se 3 (by rfl) ⟨97175, by rfl⟩ : syracuseStep 518269 = 194351) (by norm_num)
theorem B1173629 : Blo 459783 1173629 := bbase (se 3 (by rfl) ⟨220055, by rfl⟩ : syracuseStep 1173629 = 440111) (by norm_num)
theorem B780421 : Blo 459783 780421 := bbase (se 4 (by rfl) ⟨73164, by rfl⟩ : syracuseStep 780421 = 146329) (by norm_num)
theorem B518305 : Blo 459783 518305 := bbase (se 2 (by rfl) ⟨194364, by rfl⟩ : syracuseStep 518305 = 388729) (by norm_num)
theorem B1042613 : Blo 459783 1042613 := bbase (se 5 (by rfl) ⟨48872, by rfl⟩ : syracuseStep 1042613 = 97745) (by norm_num)
theorem B518341 : Blo 459783 518341 := bbase (se 4 (by rfl) ⟨48594, by rfl⟩ : syracuseStep 518341 = 97189) (by norm_num)
theorem B780509 : Blo 459783 780509 := bbase (se 3 (by rfl) ⟨146345, by rfl⟩ : syracuseStep 780509 = 292691) (by norm_num)
theorem B518377 : Blo 459783 518377 := bbase (se 2 (by rfl) ⟨194391, by rfl⟩ : syracuseStep 518377 = 388783) (by norm_num)
theorem B1042685 : Blo 459783 1042685 := bbase (se 3 (by rfl) ⟨195503, by rfl⟩ : syracuseStep 1042685 = 391007) (by norm_num)
theorem B1009925 : Blo 459783 1009925 := bbase (se 4 (by rfl) ⟨94680, by rfl⟩ : syracuseStep 1009925 = 189361) (by norm_num)
theorem B518413 : Blo 459783 518413 := bbase (se 3 (by rfl) ⟨97202, by rfl⟩ : syracuseStep 518413 = 194405) (by norm_num)
theorem B583949 : Blo 459783 583949 := bbase (se 3 (by rfl) ⟨109490, by rfl⟩ : syracuseStep 583949 = 218981) (by norm_num)
theorem B518449 : Blo 459783 518449 := bbase (se 2 (by rfl) ⟨194418, by rfl⟩ : syracuseStep 518449 = 388837) (by norm_num)
theorem B584005 : Blo 459783 584005 := bbase (se 4 (by rfl) ⟨54750, by rfl⟩ : syracuseStep 584005 = 109501) (by norm_num)
theorem B1042757 : Blo 459783 1042757 := bbase (se 4 (by rfl) ⟨97758, by rfl⟩ : syracuseStep 1042757 = 195517) (by norm_num)
theorem B518485 : Blo 459783 518485 := bbase (se 10 (by rfl) ⟨759, by rfl⟩ : syracuseStep 518485 = 1519) (by norm_num)
theorem B4811093 : Blo 459783 4811093 := bbase (se 10 (by rfl) ⟨7047, by rfl⟩ : syracuseStep 4811093 = 14095) (by norm_num)
theorem B780637 : Blo 459783 780637 := bbase (se 3 (by rfl) ⟨146369, by rfl⟩ : syracuseStep 780637 = 292739) (by norm_num)
theorem B518521 : Blo 459783 518521 := bbase (se 2 (by rfl) ⟨194445, by rfl⟩ : syracuseStep 518521 = 388891) (by norm_num)
theorem B1042829 : Blo 459783 1042829 := bbase (se 3 (by rfl) ⟨195530, by rfl⟩ : syracuseStep 1042829 = 391061) (by norm_num)
theorem B518557 : Blo 459783 518557 := bbase (se 3 (by rfl) ⟨97229, by rfl⟩ : syracuseStep 518557 = 194459) (by norm_num)
theorem B584101 : Blo 459783 584101 := bbase (se 4 (by rfl) ⟨54759, by rfl⟩ : syracuseStep 584101 = 109519) (by norm_num)
theorem B780725 : Blo 459783 780725 := bbase (se 5 (by rfl) ⟨36596, by rfl⟩ : syracuseStep 780725 = 73193) (by norm_num)
theorem B518593 : Blo 459783 518593 := bbase (se 2 (by rfl) ⟨194472, by rfl⟩ : syracuseStep 518593 = 388945) (by norm_num)
theorem B1042901 : Blo 459783 1042901 := bbase (se 7 (by rfl) ⟨12221, by rfl⟩ : syracuseStep 1042901 = 24443) (by norm_num)
theorem B518629 : Blo 459783 518629 := bbase (se 4 (by rfl) ⟨48621, by rfl⟩ : syracuseStep 518629 = 97243) (by norm_num)
theorem B518665 : Blo 459783 518665 := bbase (se 2 (by rfl) ⟨194499, by rfl⟩ : syracuseStep 518665 = 388999) (by norm_num)
theorem B1042973 : Blo 459783 1042973 := bbase (se 3 (by rfl) ⟨195557, by rfl⟩ : syracuseStep 1042973 = 391115) (by norm_num)
theorem B518701 : Blo 459783 518701 := bbase (se 3 (by rfl) ⟨97256, by rfl⟩ : syracuseStep 518701 = 194513) (by norm_num)
theorem B780853 : Blo 459783 780853 := bbase (se 5 (by rfl) ⟨36602, by rfl⟩ : syracuseStep 780853 = 73205) (by norm_num)
theorem B518737 : Blo 459783 518737 := bbase (se 2 (by rfl) ⟨194526, by rfl⟩ : syracuseStep 518737 = 389053) (by norm_num)
theorem B584273 : Blo 459783 584273 := bbase (se 2 (by rfl) ⟨219102, by rfl⟩ : syracuseStep 584273 = 438205) (by norm_num)
theorem B1043045 : Blo 459783 1043045 := bbase (se 4 (by rfl) ⟨97785, by rfl⟩ : syracuseStep 1043045 = 195571) (by norm_num)
theorem B846445 : Blo 459783 846445 := bbase (se 3 (by rfl) ⟨158708, by rfl⟩ : syracuseStep 846445 = 317417) (by norm_num)
theorem B518773 : Blo 459783 518773 := bbase (se 5 (by rfl) ⟨24317, by rfl⟩ : syracuseStep 518773 = 48635) (by norm_num)
theorem B584329 : Blo 459783 584329 := bbase (se 2 (by rfl) ⟨219123, by rfl⟩ : syracuseStep 584329 = 438247) (by norm_num)
theorem B780941 : Blo 459783 780941 := bbase (se 3 (by rfl) ⟨146426, by rfl⟩ : syracuseStep 780941 = 292853) (by norm_num)
theorem B518809 : Blo 459783 518809 := bbase (se 2 (by rfl) ⟨194553, by rfl⟩ : syracuseStep 518809 = 389107) (by norm_num)
theorem B1043117 : Blo 459783 1043117 := bbase (se 3 (by rfl) ⟨195584, by rfl⟩ : syracuseStep 1043117 = 391169) (by norm_num)
theorem B518845 : Blo 459783 518845 := bbase (se 3 (by rfl) ⟨97283, by rfl⟩ : syracuseStep 518845 = 194567) (by norm_num)
theorem B1108669 : Blo 459783 1108669 := bbase (se 3 (by rfl) ⟨207875, by rfl⟩ : syracuseStep 1108669 = 415751) (by norm_num)
theorem B518881 : Blo 459783 518881 := bbase (se 2 (by rfl) ⟨194580, by rfl⟩ : syracuseStep 518881 = 389161) (by norm_num)
theorem B584425 : Blo 459783 584425 := bbase (se 2 (by rfl) ⟨219159, by rfl⟩ : syracuseStep 584425 = 438319) (by norm_num)
theorem B879349 : Blo 459783 879349 := bbase (se 5 (by rfl) ⟨41219, by rfl⟩ : syracuseStep 879349 = 82439) (by norm_num)
theorem B1043189 : Blo 459783 1043189 := bbase (se 5 (by rfl) ⟨48899, by rfl⟩ : syracuseStep 1043189 = 97799) (by norm_num)
theorem B518917 : Blo 459783 518917 := bbase (se 4 (by rfl) ⟨48648, by rfl⟩ : syracuseStep 518917 = 97297) (by norm_num)
theorem B781069 : Blo 459783 781069 := bbase (se 3 (by rfl) ⟨146450, by rfl⟩ : syracuseStep 781069 = 292901) (by norm_num)
theorem B518953 : Blo 459783 518953 := bbase (se 2 (by rfl) ⟨194607, by rfl⟩ : syracuseStep 518953 = 389215) (by norm_num)
theorem B1043261 : Blo 459783 1043261 := bbase (se 3 (by rfl) ⟨195611, by rfl⟩ : syracuseStep 1043261 = 391223) (by norm_num)
theorem B518989 : Blo 459783 518989 := bbase (se 3 (by rfl) ⟨97310, by rfl⟩ : syracuseStep 518989 = 194621) (by norm_num)
theorem B846677 : Blo 459783 846677 := bbase (se 9 (by rfl) ⟨2480, by rfl⟩ : syracuseStep 846677 = 4961) (by norm_num)
theorem B781157 : Blo 459783 781157 := bbase (se 4 (by rfl) ⟨73233, by rfl⟩ : syracuseStep 781157 = 146467) (by norm_num)
theorem B519025 : Blo 459783 519025 := bbase (se 2 (by rfl) ⟨194634, by rfl⟩ : syracuseStep 519025 = 389269) (by norm_num)
theorem B879493 : Blo 459783 879493 := bbase (se 4 (by rfl) ⟨82452, by rfl⟩ : syracuseStep 879493 = 164905) (by norm_num)
theorem B1043333 : Blo 459783 1043333 := bbase (se 4 (by rfl) ⟨97812, by rfl⟩ : syracuseStep 1043333 = 195625) (by norm_num)
theorem B519061 : Blo 459783 519061 := bbase (se 6 (by rfl) ⟨12165, by rfl⟩ : syracuseStep 519061 = 24331) (by norm_num)
theorem B584597 : Blo 459783 584597 := bbase (se 6 (by rfl) ⟨13701, by rfl⟩ : syracuseStep 584597 = 27403) (by norm_num)
theorem B519097 : Blo 459783 519097 := bbase (se 2 (by rfl) ⟨194661, by rfl⟩ : syracuseStep 519097 = 389323) (by norm_num)
theorem B584653 : Blo 459783 584653 := bbase (se 3 (by rfl) ⟨109622, by rfl⟩ : syracuseStep 584653 = 219245) (by norm_num)
theorem B1043405 : Blo 459783 1043405 := bbase (se 3 (by rfl) ⟨195638, by rfl⟩ : syracuseStep 1043405 = 391277) (by norm_num)
theorem B519133 : Blo 459783 519133 := bbase (se 3 (by rfl) ⟨97337, by rfl⟩ : syracuseStep 519133 = 194675) (by norm_num)
theorem B781285 : Blo 459783 781285 := bbase (se 4 (by rfl) ⟨73245, by rfl⟩ : syracuseStep 781285 = 146491) (by norm_num)
theorem B519169 : Blo 459783 519169 := bbase (se 2 (by rfl) ⟨194688, by rfl⟩ : syracuseStep 519169 = 389377) (by norm_num)
theorem B1043477 : Blo 459783 1043477 := bbase (se 6 (by rfl) ⟨24456, by rfl⟩ : syracuseStep 1043477 = 48913) (by norm_num)
theorem B519205 : Blo 459783 519205 := bbase (se 4 (by rfl) ⟨48675, by rfl⟩ : syracuseStep 519205 = 97351) (by norm_num)
theorem B879653 : Blo 459783 879653 := bbase (se 4 (by rfl) ⟨82467, by rfl⟩ : syracuseStep 879653 = 164935) (by norm_num)
theorem B584749 : Blo 459783 584749 := bbase (se 3 (by rfl) ⟨109640, by rfl⟩ : syracuseStep 584749 = 219281) (by norm_num)
theorem B781373 : Blo 459783 781373 := bbase (se 3 (by rfl) ⟨146507, by rfl⟩ : syracuseStep 781373 = 293015) (by norm_num)
theorem B519241 : Blo 459783 519241 := bbase (se 2 (by rfl) ⟨194715, by rfl⟩ : syracuseStep 519241 = 389431) (by norm_num)
theorem B519277 : Blo 459783 519277 := bbase (se 3 (by rfl) ⟨97364, by rfl⟩ : syracuseStep 519277 = 194729) (by norm_num)
theorem B519313 : Blo 459783 519313 := bbase (se 2 (by rfl) ⟨194742, by rfl⟩ : syracuseStep 519313 = 389485) (by norm_num)
theorem B519349 : Blo 459783 519349 := bbase (se 5 (by rfl) ⟨24344, by rfl⟩ : syracuseStep 519349 = 48689) (by norm_num)
theorem B879797 : Blo 459783 879797 := bbase (se 5 (by rfl) ⟨41240, by rfl⟩ : syracuseStep 879797 = 82481) (by norm_num)
theorem B781501 : Blo 459783 781501 := bbase (se 3 (by rfl) ⟨146531, by rfl⟩ : syracuseStep 781501 = 293063) (by norm_num)
theorem B1109189 : Blo 459783 1109189 := bbase (se 4 (by rfl) ⟨103986, by rfl⟩ : syracuseStep 1109189 = 207973) (by norm_num)
theorem B519385 : Blo 459783 519385 := bbase (se 2 (by rfl) ⟨194769, by rfl⟩ : syracuseStep 519385 = 389539) (by norm_num)
theorem B584921 : Blo 459783 584921 := bbase (se 2 (by rfl) ⟨219345, by rfl⟩ : syracuseStep 584921 = 438691) (by norm_num)
theorem B519421 : Blo 459783 519421 := bbase (se 3 (by rfl) ⟨97391, by rfl⟩ : syracuseStep 519421 = 194783) (by norm_num)
theorem B584977 : Blo 459783 584977 := bbase (se 2 (by rfl) ⟨219366, by rfl⟩ : syracuseStep 584977 = 438733) (by norm_num)
theorem B781589 : Blo 459783 781589 := bbase (se 6 (by rfl) ⟨18318, by rfl⟩ : syracuseStep 781589 = 36637) (by norm_num)
theorem B519457 : Blo 459783 519457 := bbase (se 2 (by rfl) ⟨194796, by rfl⟩ : syracuseStep 519457 = 389593) (by norm_num)
theorem B1109285 : Blo 459783 1109285 := bbase (se 4 (by rfl) ⟨103995, by rfl⟩ : syracuseStep 1109285 = 207991) (by norm_num)
theorem B519493 : Blo 459783 519493 := bbase (se 4 (by rfl) ⟨48702, by rfl⟩ : syracuseStep 519493 = 97405) (by norm_num)
theorem B519529 : Blo 459783 519529 := bbase (se 2 (by rfl) ⟨194823, by rfl⟩ : syracuseStep 519529 = 389647) (by norm_num)
theorem B585073 : Blo 459783 585073 := bbase (se 2 (by rfl) ⟨219402, by rfl⟩ : syracuseStep 585073 = 438805) (by norm_num)
theorem B519565 : Blo 459783 519565 := bbase (se 3 (by rfl) ⟨97418, by rfl⟩ : syracuseStep 519565 = 194837) (by norm_num)
theorem B781717 : Blo 459783 781717 := bbase (se 6 (by rfl) ⟨18321, by rfl⟩ : syracuseStep 781717 = 36643) (by norm_num)
theorem B519601 : Blo 459783 519601 := bbase (se 2 (by rfl) ⟨194850, by rfl⟩ : syracuseStep 519601 = 389701) (by norm_num)
theorem B945605 : Blo 459783 945605 := bbase (se 4 (by rfl) ⟨88650, by rfl⟩ : syracuseStep 945605 = 177301) (by norm_num)
theorem B519637 : Blo 459783 519637 := bbase (se 7 (by rfl) ⟨6089, by rfl⟩ : syracuseStep 519637 = 12179) (by norm_num)
theorem B880085 : Blo 459783 880085 := bbase (se 7 (by rfl) ⟨10313, by rfl⟩ : syracuseStep 880085 = 20627) (by norm_num)
theorem B781805 : Blo 459783 781805 := bbase (se 3 (by rfl) ⟨146588, by rfl⟩ : syracuseStep 781805 = 293177) (by norm_num)
theorem B519673 : Blo 459783 519673 := bbase (se 2 (by rfl) ⟨194877, by rfl⟩ : syracuseStep 519673 = 389755) (by norm_num)
theorem B519709 : Blo 459783 519709 := bbase (se 3 (by rfl) ⟨97445, by rfl⟩ : syracuseStep 519709 = 194891) (by norm_num)
theorem B585245 : Blo 459783 585245 := bbase (se 3 (by rfl) ⟨109733, by rfl⟩ : syracuseStep 585245 = 219467) (by norm_num)
theorem B519745 : Blo 459783 519745 := bbase (se 2 (by rfl) ⟨194904, by rfl⟩ : syracuseStep 519745 = 389809) (by norm_num)
theorem B585301 : Blo 459783 585301 := bbase (se 8 (by rfl) ⟨3429, by rfl⟩ : syracuseStep 585301 = 6859) (by norm_num)
theorem B519781 : Blo 459783 519781 := bbase (se 4 (by rfl) ⟨48729, by rfl⟩ : syracuseStep 519781 = 97459) (by norm_num)
theorem B781933 : Blo 459783 781933 := bbase (se 3 (by rfl) ⟨146612, by rfl⟩ : syracuseStep 781933 = 293225) (by norm_num)
theorem B880237 : Blo 459783 880237 := bbase (se 3 (by rfl) ⟨165044, by rfl⟩ : syracuseStep 880237 = 330089) (by norm_num)
theorem B519817 : Blo 459783 519817 := bbase (se 2 (by rfl) ⟨194931, by rfl⟩ : syracuseStep 519817 = 389863) (by norm_num)
theorem B519853 : Blo 459783 519853 := bbase (se 3 (by rfl) ⟨97472, by rfl⟩ : syracuseStep 519853 = 194945) (by norm_num)
theorem B585397 : Blo 459783 585397 := bbase (se 5 (by rfl) ⟨27440, by rfl⟩ : syracuseStep 585397 = 54881) (by norm_num)
theorem B782021 : Blo 459783 782021 := bbase (se 4 (by rfl) ⟨73314, by rfl⟩ : syracuseStep 782021 = 146629) (by norm_num)
theorem B519889 : Blo 459783 519889 := bbase (se 2 (by rfl) ⟨194958, by rfl⟩ : syracuseStep 519889 = 389917) (by norm_num)
theorem B519925 : Blo 459783 519925 := bbase (se 5 (by rfl) ⟨24371, by rfl⟩ : syracuseStep 519925 = 48743) (by norm_num)
theorem B519961 : Blo 459783 519961 := bbase (se 2 (by rfl) ⟨194985, by rfl⟩ : syracuseStep 519961 = 389971) (by norm_num)
theorem B552749 : Blo 459783 552749 := bbase (se 3 (by rfl) ⟨103640, by rfl⟩ : syracuseStep 552749 = 207281) (by norm_num)
theorem B519997 : Blo 459783 519997 := bbase (se 3 (by rfl) ⟨97499, by rfl⟩ : syracuseStep 519997 = 194999) (by norm_num)
theorem B782149 : Blo 459783 782149 := bbase (se 4 (by rfl) ⟨73326, by rfl⟩ : syracuseStep 782149 = 146653) (by norm_num)
theorem B520033 : Blo 459783 520033 := bbase (se 2 (by rfl) ⟨195012, by rfl⟩ : syracuseStep 520033 = 390025) (by norm_num)
theorem B585569 : Blo 459783 585569 := bbase (se 2 (by rfl) ⟨219588, by rfl⟩ : syracuseStep 585569 = 439177) (by norm_num)
theorem B520069 : Blo 459783 520069 := bbase (se 4 (by rfl) ⟨48756, by rfl⟩ : syracuseStep 520069 = 97513) (by norm_num)
theorem B585625 : Blo 459783 585625 := bbase (se 2 (by rfl) ⟨219609, by rfl⟩ : syracuseStep 585625 = 439219) (by norm_num)
theorem B782237 : Blo 459783 782237 := bbase (se 3 (by rfl) ⟨146669, by rfl⟩ : syracuseStep 782237 = 293339) (by norm_num)
theorem B520105 : Blo 459783 520105 := bbase (se 2 (by rfl) ⟨195039, by rfl⟩ : syracuseStep 520105 = 390079) (by norm_num)
theorem B520141 : Blo 459783 520141 := bbase (se 3 (by rfl) ⟨97526, by rfl⟩ : syracuseStep 520141 = 195053) (by norm_num)
theorem B520177 : Blo 459783 520177 := bbase (se 2 (by rfl) ⟨195066, by rfl⟩ : syracuseStep 520177 = 390133) (by norm_num)
theorem B585721 : Blo 459783 585721 := bbase (se 2 (by rfl) ⟨219645, by rfl⟩ : syracuseStep 585721 = 439291) (by norm_num)
theorem B520213 : Blo 459783 520213 := bbase (se 6 (by rfl) ⟨12192, by rfl⟩ : syracuseStep 520213 = 24385) (by norm_num)
theorem B782365 : Blo 459783 782365 := bbase (se 3 (by rfl) ⟨146693, by rfl⟩ : syracuseStep 782365 = 293387) (by norm_num)
theorem B520249 : Blo 459783 520249 := bbase (se 2 (by rfl) ⟨195093, by rfl⟩ : syracuseStep 520249 = 390187) (by norm_num)
theorem B520285 : Blo 459783 520285 := bbase (se 3 (by rfl) ⟨97553, by rfl⟩ : syracuseStep 520285 = 195107) (by norm_num)
theorem B782453 : Blo 459783 782453 := bbase (se 5 (by rfl) ⟨36677, by rfl⟩ : syracuseStep 782453 = 73355) (by norm_num)
theorem B553081 : Blo 459783 553081 := bbase (se 2 (by rfl) ⟨207405, by rfl⟩ : syracuseStep 553081 = 414811) (by norm_num)
theorem B520321 : Blo 459783 520321 := bbase (se 2 (by rfl) ⟨195120, by rfl⟩ : syracuseStep 520321 = 390241) (by norm_num)
theorem B520357 : Blo 459783 520357 := bbase (se 4 (by rfl) ⟨48783, by rfl⟩ : syracuseStep 520357 = 97567) (by norm_num)
theorem B585893 : Blo 459783 585893 := bbase (se 4 (by rfl) ⟨54927, by rfl⟩ : syracuseStep 585893 = 109855) (by norm_num)
theorem B520393 : Blo 459783 520393 := bbase (se 2 (by rfl) ⟨195147, by rfl⟩ : syracuseStep 520393 = 390295) (by norm_num)
theorem B585949 : Blo 459783 585949 := bbase (se 3 (by rfl) ⟨109865, by rfl⟩ : syracuseStep 585949 = 219731) (by norm_num)
theorem B520429 : Blo 459783 520429 := bbase (se 3 (by rfl) ⟨97580, by rfl⟩ : syracuseStep 520429 = 195161) (by norm_num)
theorem B782581 : Blo 459783 782581 := bbase (se 5 (by rfl) ⟨36683, by rfl⟩ : syracuseStep 782581 = 73367) (by norm_num)
theorem B749821 : Blo 459783 749821 := bbase (se 3 (by rfl) ⟨140591, by rfl⟩ : syracuseStep 749821 = 281183) (by norm_num)
theorem B520465 : Blo 459783 520465 := bbase (se 2 (by rfl) ⟨195174, by rfl⟩ : syracuseStep 520465 = 390349) (by norm_num)
theorem B520501 : Blo 459783 520501 := bbase (se 5 (by rfl) ⟨24398, by rfl⟩ : syracuseStep 520501 = 48797) (by norm_num)
theorem B586045 : Blo 459783 586045 := bbase (se 3 (by rfl) ⟨109883, by rfl⟩ : syracuseStep 586045 = 219767) (by norm_num)
theorem B520537 : Blo 459783 520537 := bbase (se 2 (by rfl) ⟨195201, by rfl⟩ : syracuseStep 520537 = 390403) (by norm_num)
theorem B520573 : Blo 459783 520573 := bbase (se 3 (by rfl) ⟨97607, by rfl⟩ : syracuseStep 520573 = 195215) (by norm_num)
theorem B520609 : Blo 459783 520609 := bbase (se 2 (by rfl) ⟨195228, by rfl⟩ : syracuseStep 520609 = 390457) (by norm_num)
theorem B520645 : Blo 459783 520645 := bbase (se 4 (by rfl) ⟨48810, by rfl⟩ : syracuseStep 520645 = 97621) (by norm_num)
theorem B520681 : Blo 459783 520681 := bbase (se 2 (by rfl) ⟨195255, by rfl⟩ : syracuseStep 520681 = 390511) (by norm_num)
theorem B586217 : Blo 459783 586217 := bbase (se 2 (by rfl) ⟨219831, by rfl⟩ : syracuseStep 586217 = 439663) (by norm_num)
theorem B520717 : Blo 459783 520717 := bbase (se 3 (by rfl) ⟨97634, by rfl⟩ : syracuseStep 520717 = 195269) (by norm_num)
theorem B586273 : Blo 459783 586273 := bbase (se 2 (by rfl) ⟨219852, by rfl⟩ : syracuseStep 586273 = 439705) (by norm_num)
theorem B520753 : Blo 459783 520753 := bbase (se 2 (by rfl) ⟨195282, by rfl⟩ : syracuseStep 520753 = 390565) (by norm_num)
theorem B520789 : Blo 459783 520789 := bbase (se 8 (by rfl) ⟨3051, by rfl⟩ : syracuseStep 520789 = 6103) (by norm_num)
theorem B1110629 : Blo 459783 1110629 := bbase (se 4 (by rfl) ⟨104121, by rfl⟩ : syracuseStep 1110629 = 208243) (by norm_num)
theorem B520825 : Blo 459783 520825 := bbase (se 2 (by rfl) ⟨195309, by rfl⟩ : syracuseStep 520825 = 390619) (by norm_num)
theorem B586369 : Blo 459783 586369 := bbase (se 2 (by rfl) ⟨219888, by rfl⟩ : syracuseStep 586369 = 439777) (by norm_num)
theorem B520861 : Blo 459783 520861 := bbase (se 3 (by rfl) ⟨97661, by rfl⟩ : syracuseStep 520861 = 195323) (by norm_num)
theorem B520897 : Blo 459783 520897 := bbase (se 2 (by rfl) ⟨195336, by rfl⟩ : syracuseStep 520897 = 390673) (by norm_num)
theorem B488141 : Blo 459783 488141 := bbase (se 3 (by rfl) ⟨91526, by rfl⟩ : syracuseStep 488141 = 183053) (by norm_num)
theorem B520933 : Blo 459783 520933 := bbase (se 4 (by rfl) ⟨48837, by rfl⟩ : syracuseStep 520933 = 97675) (by norm_num)
theorem B520969 : Blo 459783 520969 := bbase (se 2 (by rfl) ⟨195363, by rfl⟩ : syracuseStep 520969 = 390727) (by norm_num)
theorem B521005 : Blo 459783 521005 := bbase (se 3 (by rfl) ⟨97688, by rfl⟩ : syracuseStep 521005 = 195377) (by norm_num)
theorem B586541 : Blo 459783 586541 := bbase (se 3 (by rfl) ⟨109976, by rfl⟩ : syracuseStep 586541 = 219953) (by norm_num)
theorem B521041 : Blo 459783 521041 := bbase (se 2 (by rfl) ⟨195390, by rfl⟩ : syracuseStep 521041 = 390781) (by norm_num)
theorem B586597 : Blo 459783 586597 := bbase (se 4 (by rfl) ⟨54993, by rfl⟩ : syracuseStep 586597 = 109987) (by norm_num)
theorem B521077 : Blo 459783 521077 := bbase (se 5 (by rfl) ⟨24425, by rfl⟩ : syracuseStep 521077 = 48851) (by norm_num)
theorem B521113 : Blo 459783 521113 := bbase (se 2 (by rfl) ⟨195417, by rfl⟩ : syracuseStep 521113 = 390835) (by norm_num)
theorem B521149 : Blo 459783 521149 := bbase (se 3 (by rfl) ⟨97715, by rfl⟩ : syracuseStep 521149 = 195431) (by norm_num)
theorem B586693 : Blo 459783 586693 := bbase (se 4 (by rfl) ⟨55002, by rfl⟩ : syracuseStep 586693 = 110005) (by norm_num)
theorem B521185 : Blo 459783 521185 := bbase (se 2 (by rfl) ⟨195444, by rfl⟩ : syracuseStep 521185 = 390889) (by norm_num)
theorem B553969 : Blo 459783 553969 := bbase (se 2 (by rfl) ⟨207738, by rfl⟩ : syracuseStep 553969 = 415477) (by norm_num)
theorem B521221 : Blo 459783 521221 := bbase (se 4 (by rfl) ⟨48864, by rfl⟩ : syracuseStep 521221 = 97729) (by norm_num)
theorem B521257 : Blo 459783 521257 := bbase (se 2 (by rfl) ⟨195471, by rfl⟩ : syracuseStep 521257 = 390943) (by norm_num)
theorem B521293 : Blo 459783 521293 := bbase (se 3 (by rfl) ⟨97742, by rfl⟩ : syracuseStep 521293 = 195485) (by norm_num)
theorem B521329 : Blo 459783 521329 := bbase (se 2 (by rfl) ⟨195498, by rfl⟩ : syracuseStep 521329 = 390997) (by norm_num)
theorem B586865 : Blo 459783 586865 := bbase (se 2 (by rfl) ⟨220074, by rfl⟩ : syracuseStep 586865 = 440149) (by norm_num)
theorem B521365 : Blo 459783 521365 := bbase (se 6 (by rfl) ⟨12219, by rfl⟩ : syracuseStep 521365 = 24439) (by norm_num)
theorem B586921 : Blo 459783 586921 := bbase (se 2 (by rfl) ⟨220095, by rfl⟩ : syracuseStep 586921 = 440191) (by norm_num)
theorem B2225333 : Blo 459783 2225333 := bbase (se 5 (by rfl) ⟨104312, by rfl⟩ : syracuseStep 2225333 = 208625) (by norm_num)
theorem B521401 : Blo 459783 521401 := bbase (se 2 (by rfl) ⟨195525, by rfl⟩ : syracuseStep 521401 = 391051) (by norm_num)
theorem B521437 : Blo 459783 521437 := bbase (se 3 (by rfl) ⟨97769, by rfl⟩ : syracuseStep 521437 = 195539) (by norm_num)
theorem B521473 : Blo 459783 521473 := bbase (se 2 (by rfl) ⟨195552, by rfl⟩ : syracuseStep 521473 = 391105) (by norm_num)
theorem B521509 : Blo 459783 521509 := bbase (se 4 (by rfl) ⟨48891, by rfl⟩ : syracuseStep 521509 = 97783) (by norm_num)
theorem B521545 : Blo 459783 521545 := bbase (se 2 (by rfl) ⟨195579, by rfl⟩ : syracuseStep 521545 = 391159) (by norm_num)
theorem B521581 : Blo 459783 521581 := bbase (se 3 (by rfl) ⟨97796, by rfl⟩ : syracuseStep 521581 = 195593) (by norm_num)
theorem B521617 : Blo 459783 521617 := bbase (se 2 (by rfl) ⟨195606, by rfl⟩ : syracuseStep 521617 = 391213) (by norm_num)
theorem B521653 : Blo 459783 521653 := bbase (se 5 (by rfl) ⟨24452, by rfl⟩ : syracuseStep 521653 = 48905) (by norm_num)
theorem B3503573 : Blo 459783 3503573 := bbase (se 7 (by rfl) ⟨41057, by rfl⟩ : syracuseStep 3503573 = 82115) (by norm_num)
theorem B521689 : Blo 459783 521689 := bbase (se 2 (by rfl) ⟨195633, by rfl⟩ : syracuseStep 521689 = 391267) (by norm_num)
theorem B521725 : Blo 459783 521725 := bbase (se 3 (by rfl) ⟨97823, by rfl⟩ : syracuseStep 521725 = 195647) (by norm_num)
theorem B751141 : Blo 459783 751141 := bbase (se 4 (by rfl) ⟨70419, by rfl⟩ : syracuseStep 751141 = 140839) (by norm_num)
theorem B2946709 : Blo 459783 2946709 := bbase (se 6 (by rfl) ⟨69063, by rfl⟩ : syracuseStep 2946709 = 138127) (by norm_num)
theorem B555017 : Blo 459783 555017 := bbase (se 2 (by rfl) ⟨208131, by rfl⟩ : syracuseStep 555017 = 416263) (by norm_num)
theorem B1603925 : Blo 459783 1603925 := bbase (se 10 (by rfl) ⟨2349, by rfl⟩ : syracuseStep 1603925 = 4699) (by norm_num)
theorem B555373 : Blo 459783 555373 := bbase (se 3 (by rfl) ⟨104132, by rfl⟩ : syracuseStep 555373 = 208265) (by norm_num)
theorem B1964405 : Blo 459783 1964405 := bbase (se 5 (by rfl) ⟨92081, by rfl⟩ : syracuseStep 1964405 = 184163) (by norm_num)
theorem B1374581 : Blo 459783 1374581 := bbase (se 5 (by rfl) ⟨64433, by rfl⟩ : syracuseStep 1374581 = 128867) (by norm_num)
theorem B1997237 : Blo 459783 1997237 := bbase (se 5 (by rfl) ⟨93620, by rfl⟩ : syracuseStep 1997237 = 187241) (by norm_num)
theorem B555565 : Blo 459783 555565 := bbase (se 3 (by rfl) ⟨104168, by rfl⟩ : syracuseStep 555565 = 208337) (by norm_num)
theorem B1112629 : Blo 459783 1112629 := bbase (se 5 (by rfl) ⟨52154, by rfl⟩ : syracuseStep 1112629 = 104309) (by norm_num)
theorem B1964645 : Blo 459783 1964645 := bbase (se 4 (by rfl) ⟨184185, by rfl⟩ : syracuseStep 1964645 = 368371) (by norm_num)
theorem B948893 : Blo 459783 948893 := bbase (se 3 (by rfl) ⟨177917, by rfl⟩ : syracuseStep 948893 = 355835) (by norm_num)
theorem B555709 : Blo 459783 555709 := bbase (se 3 (by rfl) ⟨104195, by rfl⟩ : syracuseStep 555709 = 208391) (by norm_num)
theorem B1112773 : Blo 459783 1112773 := bbase (se 4 (by rfl) ⟨104322, by rfl⟩ : syracuseStep 1112773 = 208645) (by norm_num)
theorem B4455125 : Blo 459783 4455125 := bbase (se 7 (by rfl) ⟨52208, by rfl⟩ : syracuseStep 4455125 = 104417) (by norm_num)
theorem B621437 : Blo 459783 621437 := bbase (se 3 (by rfl) ⟨116519, by rfl⟩ : syracuseStep 621437 = 233039) (by norm_num)
theorem B1309877 : Blo 459783 1309877 := bbase (se 5 (by rfl) ⟨61400, by rfl⟩ : syracuseStep 1309877 = 122801) (by norm_num)
theorem B1998053 : Blo 459783 1998053 := bbase (se 4 (by rfl) ⟨187317, by rfl⟩ : syracuseStep 1998053 = 374635) (by norm_num)
theorem B1113389 : Blo 459783 1113389 := bbase (se 3 (by rfl) ⟨208760, by rfl⟩ : syracuseStep 1113389 = 417521) (by norm_num)
theorem B982373 : Blo 459783 982373 := bbase (se 4 (by rfl) ⟨92097, by rfl⟩ : syracuseStep 982373 = 184195) (by norm_num)
theorem B654733 : Blo 459783 654733 := bbase (se 3 (by rfl) ⟨122762, by rfl⟩ : syracuseStep 654733 = 245525) (by norm_num)
theorem B491033 : Blo 459783 491033 := bbase (se 2 (by rfl) ⟨184137, by rfl⟩ : syracuseStep 491033 = 368275) (by norm_num)
theorem B982613 : Blo 459783 982613 := bbase (se 8 (by rfl) ⟨5757, by rfl⟩ : syracuseStep 982613 = 11515) (by norm_num)
theorem B1113725 : Blo 459783 1113725 := bbase (se 3 (by rfl) ⟨208823, by rfl⟩ : syracuseStep 1113725 = 417647) (by norm_num)
theorem B491221 : Blo 459783 491221 := bbase (se 7 (by rfl) ⟨5756, by rfl⟩ : syracuseStep 491221 = 11513) (by norm_num)
theorem B1113821 : Blo 459783 1113821 := bbase (se 3 (by rfl) ⟨208841, by rfl⟩ : syracuseStep 1113821 = 417683) (by norm_num)
theorem B622405 : Blo 459783 622405 := bbase (se 4 (by rfl) ⟨58350, by rfl⟩ : syracuseStep 622405 = 116701) (by norm_num)
theorem B1408853 : Blo 459783 1408853 := bbase (se 9 (by rfl) ⟨4127, by rfl⟩ : syracuseStep 1408853 = 8255) (by norm_num)
theorem B655229 : Blo 459783 655229 := bbase (se 3 (by rfl) ⟨122855, by rfl⟩ : syracuseStep 655229 = 245711) (by norm_num)
theorem B1114013 : Blo 459783 1114013 := bbase (se 3 (by rfl) ⟨208877, by rfl⟩ : syracuseStep 1114013 = 417755) (by norm_num)
theorem B1245125 : Blo 459783 1245125 := bbase (se 4 (by rfl) ⟨116730, by rfl⟩ : syracuseStep 1245125 = 233461) (by norm_num)
theorem B1310833 : Blo 459783 1310833 := bstep (se 2 (by rfl) ⟨491562, by rfl⟩ : syracuseStep 1310833 = 983125) B983125
theorem B11796677 : Blo 459783 11796677 := bstep (se 4 (by rfl) ⟨1105938, by rfl⟩ : syracuseStep 11796677 = 2211877) B2211877
theorem B2621645 : Blo 459783 2621645 := bstep (se 3 (by rfl) ⟨491558, by rfl⟩ : syracuseStep 2621645 = 983117) B983117
theorem B524579 : Blo 459783 524579 := bstep (se 1 (by rfl) ⟨393434, by rfl⟩ : syracuseStep 524579 = 786869) B786869
theorem B2490659 : Blo 459783 2490659 := bstep (se 1 (by rfl) ⟨1867994, by rfl⟩ : syracuseStep 2490659 = 3735989) B3735989
theorem B1769933 : Blo 459783 1769933 := bstep (se 3 (by rfl) ⟨331862, by rfl⟩ : syracuseStep 1769933 = 663725) B663725
theorem B1245869 : Blo 459783 1245869 := bstep (se 3 (by rfl) ⟨233600, by rfl⟩ : syracuseStep 1245869 = 467201) B467201
theorem B787171 : Blo 459783 787171 := bstep (se 1 (by rfl) ⟨590378, by rfl⟩ : syracuseStep 787171 = 1180757) B1180757
theorem B1409777 : Blo 459783 1409777 := bstep (se 2 (by rfl) ⟨528666, by rfl⟩ : syracuseStep 1409777 = 1057333) B1057333
theorem B983843 : Blo 459783 983843 := bstep (se 1 (by rfl) ⟨737882, by rfl⟩ : syracuseStep 983843 = 1475765) B1475765
theorem B492323 : Blo 459783 492323 := bstep (se 1 (by rfl) ⟨369242, by rfl⟩ : syracuseStep 492323 = 738485) B738485
theorem B1868771 : Blo 459783 1868771 := bstep (se 1 (by rfl) ⟨1401578, by rfl⟩ : syracuseStep 1868771 = 2803157) B2803157
theorem B459795 : Blo 459783 459795 := bstep (se 1 (by rfl) ⟨344846, by rfl⟩ : syracuseStep 459795 = 689693) B689693
theorem B459811 : Blo 459783 459811 := bstep (se 1 (by rfl) ⟨344858, by rfl⟩ : syracuseStep 459811 = 689717) B689717
theorem B656419 : Blo 459783 656419 := bstep (se 1 (by rfl) ⟨492314, by rfl⟩ : syracuseStep 656419 = 984629) B984629
theorem B459827 : Blo 459783 459827 := bstep (se 1 (by rfl) ⟨344870, by rfl⟩ : syracuseStep 459827 = 689741) B689741
theorem B459843 : Blo 459783 459843 := bstep (se 1 (by rfl) ⟨344882, by rfl⟩ : syracuseStep 459843 = 689765) B689765
theorem B459859 : Blo 459783 459859 := bstep (se 1 (by rfl) ⟨344894, by rfl⟩ : syracuseStep 459859 = 689789) B689789
theorem B459875 : Blo 459783 459875 := bstep (se 1 (by rfl) ⟨344906, by rfl⟩ : syracuseStep 459875 = 689813) B689813
theorem B2622577 : Blo 459783 2622577 := bstep (se 2 (by rfl) ⟨983466, by rfl⟩ : syracuseStep 2622577 = 1966933) B1966933
theorem B459891 : Blo 459783 459891 := bstep (se 1 (by rfl) ⟨344918, by rfl⟩ : syracuseStep 459891 = 689837) B689837
theorem B459907 : Blo 459783 459907 := bstep (se 1 (by rfl) ⟨344930, by rfl⟩ : syracuseStep 459907 = 689861) B689861
theorem B459923 : Blo 459783 459923 := bstep (se 1 (by rfl) ⟨344942, by rfl⟩ : syracuseStep 459923 = 689885) B689885
theorem B787603 : Blo 459783 787603 := bstep (se 1 (by rfl) ⟨590702, by rfl⟩ : syracuseStep 787603 = 1181405) B1181405
theorem B459939 : Blo 459783 459939 := bstep (se 1 (by rfl) ⟨344954, by rfl⟩ : syracuseStep 459939 = 689909) B689909
theorem B459955 : Blo 459783 459955 := bstep (se 1 (by rfl) ⟨344966, by rfl⟩ : syracuseStep 459955 = 689933) B689933
theorem B459971 : Blo 459783 459971 := bstep (se 1 (by rfl) ⟨344978, by rfl⟩ : syracuseStep 459971 = 689957) B689957
theorem B459987 : Blo 459783 459987 := bstep (se 1 (by rfl) ⟨344990, by rfl⟩ : syracuseStep 459987 = 689981) B689981
theorem B460003 : Blo 459783 460003 := bstep (se 1 (by rfl) ⟨345002, by rfl⟩ : syracuseStep 460003 = 690005) B690005
theorem B984305 : Blo 459783 984305 := bstep (se 2 (by rfl) ⟨369114, by rfl⟩ : syracuseStep 984305 = 738229) B738229
theorem B460019 : Blo 459783 460019 := bstep (se 1 (by rfl) ⟨345014, by rfl⟩ : syracuseStep 460019 = 690029) B690029
theorem B460035 : Blo 459783 460035 := bstep (se 1 (by rfl) ⟨345026, by rfl⟩ : syracuseStep 460035 = 690053) B690053
theorem B460051 : Blo 459783 460051 := bstep (se 1 (by rfl) ⟨345038, by rfl⟩ : syracuseStep 460051 = 690077) B690077
theorem B460067 : Blo 459783 460067 := bstep (se 1 (by rfl) ⟨345050, by rfl⟩ : syracuseStep 460067 = 690101) B690101
theorem B460083 : Blo 459783 460083 := bstep (se 1 (by rfl) ⟨345062, by rfl⟩ : syracuseStep 460083 = 690125) B690125
theorem B460099 : Blo 459783 460099 := bstep (se 1 (by rfl) ⟨345074, by rfl⟩ : syracuseStep 460099 = 690149) B690149
theorem B460115 : Blo 459783 460115 := bstep (se 1 (by rfl) ⟨345086, by rfl⟩ : syracuseStep 460115 = 690173) B690173
theorem B460131 : Blo 459783 460131 := bstep (se 1 (by rfl) ⟨345098, by rfl⟩ : syracuseStep 460131 = 690197) B690197
theorem B1312109 : Blo 459783 1312109 := bstep (se 3 (by rfl) ⟨246020, by rfl⟩ : syracuseStep 1312109 = 492041) B492041
theorem B460147 : Blo 459783 460147 := bstep (se 1 (by rfl) ⟨345110, by rfl⟩ : syracuseStep 460147 = 690221) B690221
theorem B460163 : Blo 459783 460163 := bstep (se 1 (by rfl) ⟨345122, by rfl⟩ : syracuseStep 460163 = 690245) B690245
theorem B460179 : Blo 459783 460179 := bstep (se 1 (by rfl) ⟨345134, by rfl⟩ : syracuseStep 460179 = 690269) B690269
theorem B460195 : Blo 459783 460195 := bstep (se 1 (by rfl) ⟨345146, by rfl⟩ : syracuseStep 460195 = 690293) B690293
theorem B460211 : Blo 459783 460211 := bstep (se 1 (by rfl) ⟨345158, by rfl⟩ : syracuseStep 460211 = 690317) B690317
theorem B460227 : Blo 459783 460227 := bstep (se 1 (by rfl) ⟨345170, by rfl⟩ : syracuseStep 460227 = 690341) B690341
theorem B460243 : Blo 459783 460243 := bstep (se 1 (by rfl) ⟨345182, by rfl⟩ : syracuseStep 460243 = 690365) B690365
theorem B460259 : Blo 459783 460259 := bstep (se 1 (by rfl) ⟨345194, by rfl⟩ : syracuseStep 460259 = 690389) B690389
theorem B1246691 : Blo 459783 1246691 := bstep (se 1 (by rfl) ⟨935018, by rfl⟩ : syracuseStep 1246691 = 1870037) B1870037
theorem B460275 : Blo 459783 460275 := bstep (se 1 (by rfl) ⟨345206, by rfl⟩ : syracuseStep 460275 = 690413) B690413
theorem B460291 : Blo 459783 460291 := bstep (se 1 (by rfl) ⟨345218, by rfl⟩ : syracuseStep 460291 = 690437) B690437
theorem B689681 : Blo 459783 689681 := bstep (se 2 (by rfl) ⟨258630, by rfl⟩ : syracuseStep 689681 = 517261) B517261
theorem B460307 : Blo 459783 460307 := bstep (se 1 (by rfl) ⟨345230, by rfl⟩ : syracuseStep 460307 = 690461) B690461
theorem B493075 : Blo 459783 493075 := bstep (se 1 (by rfl) ⟨369806, by rfl⟩ : syracuseStep 493075 = 739613) B739613
theorem B689699 : Blo 459783 689699 := bstep (se 1 (by rfl) ⟨517274, by rfl⟩ : syracuseStep 689699 = 1034549) B1034549
theorem B460323 : Blo 459783 460323 := bstep (se 1 (by rfl) ⟨345242, by rfl⟩ : syracuseStep 460323 = 690485) B690485
theorem B1312291 : Blo 459783 1312291 := bstep (se 1 (by rfl) ⟨984218, by rfl⟩ : syracuseStep 1312291 = 1968437) B1968437
theorem B460339 : Blo 459783 460339 := bstep (se 1 (by rfl) ⟨345254, by rfl⟩ : syracuseStep 460339 = 690509) B690509
theorem B689729 : Blo 459783 689729 := bstep (se 2 (by rfl) ⟨258648, by rfl⟩ : syracuseStep 689729 = 517297) B517297
theorem B460355 : Blo 459783 460355 := bstep (se 1 (by rfl) ⟨345266, by rfl⟩ : syracuseStep 460355 = 690533) B690533
theorem B1312337 : Blo 459783 1312337 := bstep (se 2 (by rfl) ⟨492126, by rfl⟩ : syracuseStep 1312337 = 984253) B984253
theorem B689747 : Blo 459783 689747 := bstep (se 1 (by rfl) ⟨517310, by rfl⟩ : syracuseStep 689747 = 1034621) B1034621
theorem B460371 : Blo 459783 460371 := bstep (se 1 (by rfl) ⟨345278, by rfl⟩ : syracuseStep 460371 = 690557) B690557
theorem B460387 : Blo 459783 460387 := bstep (se 1 (by rfl) ⟨345290, by rfl⟩ : syracuseStep 460387 = 690581) B690581
theorem B689777 : Blo 459783 689777 := bstep (se 2 (by rfl) ⟨258666, by rfl⟩ : syracuseStep 689777 = 517333) B517333
theorem B886385 : Blo 459783 886385 := bstep (se 2 (by rfl) ⟨332394, by rfl⟩ : syracuseStep 886385 = 664789) B664789
theorem B460403 : Blo 459783 460403 := bstep (se 1 (by rfl) ⟨345302, by rfl⟩ : syracuseStep 460403 = 690605) B690605
theorem B689795 : Blo 459783 689795 := bstep (se 1 (by rfl) ⟨517346, by rfl⟩ : syracuseStep 689795 = 1034693) B1034693
theorem B460419 : Blo 459783 460419 := bstep (se 1 (by rfl) ⟨345314, by rfl⟩ : syracuseStep 460419 = 690629) B690629
theorem B460435 : Blo 459783 460435 := bstep (se 1 (by rfl) ⟨345326, by rfl⟩ : syracuseStep 460435 = 690653) B690653
theorem B689825 : Blo 459783 689825 := bstep (se 2 (by rfl) ⟨258684, by rfl⟩ : syracuseStep 689825 = 517369) B517369
theorem B460451 : Blo 459783 460451 := bstep (se 1 (by rfl) ⟨345338, by rfl⟩ : syracuseStep 460451 = 690677) B690677
theorem B689843 : Blo 459783 689843 := bstep (se 1 (by rfl) ⟨517382, by rfl⟩ : syracuseStep 689843 = 1034765) B1034765
theorem B460467 : Blo 459783 460467 := bstep (se 1 (by rfl) ⟨345350, by rfl⟩ : syracuseStep 460467 = 690701) B690701
theorem B460483 : Blo 459783 460483 := bstep (se 1 (by rfl) ⟨345362, by rfl⟩ : syracuseStep 460483 = 690725) B690725
theorem B689873 : Blo 459783 689873 := bstep (se 2 (by rfl) ⟨258702, by rfl⟩ : syracuseStep 689873 = 517405) B517405
theorem B460499 : Blo 459783 460499 := bstep (se 1 (by rfl) ⟨345374, by rfl⟩ : syracuseStep 460499 = 690749) B690749
theorem B689891 : Blo 459783 689891 := bstep (se 1 (by rfl) ⟨517418, by rfl⟩ : syracuseStep 689891 = 1034837) B1034837
theorem B460515 : Blo 459783 460515 := bstep (se 1 (by rfl) ⟨345386, by rfl⟩ : syracuseStep 460515 = 690773) B690773
theorem B460531 : Blo 459783 460531 := bstep (se 1 (by rfl) ⟨345398, by rfl⟩ : syracuseStep 460531 = 690797) B690797
theorem B689921 : Blo 459783 689921 := bstep (se 2 (by rfl) ⟨258720, by rfl⟩ : syracuseStep 689921 = 517441) B517441
theorem B460547 : Blo 459783 460547 := bstep (se 1 (by rfl) ⟨345410, by rfl⟩ : syracuseStep 460547 = 690821) B690821
theorem B689939 : Blo 459783 689939 := bstep (se 1 (by rfl) ⟨517454, by rfl⟩ : syracuseStep 689939 = 1034909) B1034909
theorem B460563 : Blo 459783 460563 := bstep (se 1 (by rfl) ⟨345422, by rfl⟩ : syracuseStep 460563 = 690845) B690845
theorem B460579 : Blo 459783 460579 := bstep (se 1 (by rfl) ⟨345434, by rfl⟩ : syracuseStep 460579 = 690869) B690869
theorem B689969 : Blo 459783 689969 := bstep (se 2 (by rfl) ⟨258738, by rfl⟩ : syracuseStep 689969 = 517477) B517477
theorem B460595 : Blo 459783 460595 := bstep (se 1 (by rfl) ⟨345446, by rfl⟩ : syracuseStep 460595 = 690893) B690893
theorem B624449 : Blo 459783 624449 := bstep (se 2 (by rfl) ⟨234168, by rfl⟩ : syracuseStep 624449 = 468337) B468337
theorem B689987 : Blo 459783 689987 := bstep (se 1 (by rfl) ⟨517490, by rfl⟩ : syracuseStep 689987 = 1034981) B1034981
theorem B460611 : Blo 459783 460611 := bstep (se 1 (by rfl) ⟨345458, by rfl⟩ : syracuseStep 460611 = 690917) B690917
theorem B460627 : Blo 459783 460627 := bstep (se 1 (by rfl) ⟨345470, by rfl⟩ : syracuseStep 460627 = 690941) B690941
theorem B690017 : Blo 459783 690017 := bstep (se 2 (by rfl) ⟨258756, by rfl⟩ : syracuseStep 690017 = 517513) B517513
theorem B460643 : Blo 459783 460643 := bstep (se 1 (by rfl) ⟨345482, by rfl⟩ : syracuseStep 460643 = 690965) B690965
theorem B690035 : Blo 459783 690035 := bstep (se 1 (by rfl) ⟨517526, by rfl⟩ : syracuseStep 690035 = 1035053) B1035053
theorem B460659 : Blo 459783 460659 := bstep (se 1 (by rfl) ⟨345494, by rfl⟩ : syracuseStep 460659 = 690989) B690989
theorem B460675 : Blo 459783 460675 := bstep (se 1 (by rfl) ⟨345506, by rfl⟩ : syracuseStep 460675 = 691013) B691013
theorem B690065 : Blo 459783 690065 := bstep (se 2 (by rfl) ⟨258774, by rfl⟩ : syracuseStep 690065 = 517549) B517549
theorem B460691 : Blo 459783 460691 := bstep (se 1 (by rfl) ⟨345518, by rfl⟩ : syracuseStep 460691 = 691037) B691037
theorem B690083 : Blo 459783 690083 := bstep (se 1 (by rfl) ⟨517562, by rfl⟩ : syracuseStep 690083 = 1035125) B1035125
theorem B460707 : Blo 459783 460707 := bstep (se 1 (by rfl) ⟨345530, by rfl⟩ : syracuseStep 460707 = 691061) B691061
theorem B460723 : Blo 459783 460723 := bstep (se 1 (by rfl) ⟨345542, by rfl⟩ : syracuseStep 460723 = 691085) B691085
theorem B690113 : Blo 459783 690113 := bstep (se 2 (by rfl) ⟨258792, by rfl⟩ : syracuseStep 690113 = 517585) B517585
theorem B460739 : Blo 459783 460739 := bstep (se 1 (by rfl) ⟨345554, by rfl⟩ : syracuseStep 460739 = 691109) B691109
theorem B690131 : Blo 459783 690131 := bstep (se 1 (by rfl) ⟨517598, by rfl⟩ : syracuseStep 690131 = 1035197) B1035197
theorem B460755 : Blo 459783 460755 := bstep (se 1 (by rfl) ⟨345566, by rfl⟩ : syracuseStep 460755 = 691133) B691133
theorem B460771 : Blo 459783 460771 := bstep (se 1 (by rfl) ⟨345578, by rfl⟩ : syracuseStep 460771 = 691157) B691157
theorem B624611 : Blo 459783 624611 := bstep (se 1 (by rfl) ⟨468458, by rfl⟩ : syracuseStep 624611 = 936917) B936917
theorem B690161 : Blo 459783 690161 := bstep (se 2 (by rfl) ⟨258810, by rfl⟩ : syracuseStep 690161 = 517621) B517621
theorem B460787 : Blo 459783 460787 := bstep (se 1 (by rfl) ⟨345590, by rfl⟩ : syracuseStep 460787 = 691181) B691181
theorem B690179 : Blo 459783 690179 := bstep (se 1 (by rfl) ⟨517634, by rfl⟩ : syracuseStep 690179 = 1035269) B1035269
theorem B460803 : Blo 459783 460803 := bstep (se 1 (by rfl) ⟨345602, by rfl⟩ : syracuseStep 460803 = 691205) B691205
theorem B460819 : Blo 459783 460819 := bstep (se 1 (by rfl) ⟨345614, by rfl⟩ : syracuseStep 460819 = 691229) B691229
theorem B690209 : Blo 459783 690209 := bstep (se 2 (by rfl) ⟨258828, by rfl⟩ : syracuseStep 690209 = 517657) B517657
theorem B460835 : Blo 459783 460835 := bstep (se 1 (by rfl) ⟨345626, by rfl⟩ : syracuseStep 460835 = 691253) B691253
theorem B690227 : Blo 459783 690227 := bstep (se 1 (by rfl) ⟨517670, by rfl⟩ : syracuseStep 690227 = 1035341) B1035341
theorem B460851 : Blo 459783 460851 := bstep (se 1 (by rfl) ⟨345638, by rfl⟩ : syracuseStep 460851 = 691277) B691277
theorem B460867 : Blo 459783 460867 := bstep (se 1 (by rfl) ⟨345650, by rfl⟩ : syracuseStep 460867 = 691301) B691301
theorem B3934277 : Blo 459783 3934277 := bstep (se 4 (by rfl) ⟨368838, by rfl⟩ : syracuseStep 3934277 = 737677) B737677
theorem B690257 : Blo 459783 690257 := bstep (se 2 (by rfl) ⟨258846, by rfl⟩ : syracuseStep 690257 = 517693) B517693
theorem B460883 : Blo 459783 460883 := bstep (se 1 (by rfl) ⟨345662, by rfl⟩ : syracuseStep 460883 = 691325) B691325
theorem B690275 : Blo 459783 690275 := bstep (se 1 (by rfl) ⟨517706, by rfl⟩ : syracuseStep 690275 = 1035413) B1035413
theorem B460899 : Blo 459783 460899 := bstep (se 1 (by rfl) ⟨345674, by rfl⟩ : syracuseStep 460899 = 691349) B691349
theorem B460915 : Blo 459783 460915 := bstep (se 1 (by rfl) ⟨345686, by rfl⟩ : syracuseStep 460915 = 691373) B691373
theorem B690305 : Blo 459783 690305 := bstep (se 2 (by rfl) ⟨258864, by rfl⟩ : syracuseStep 690305 = 517729) B517729
theorem B460931 : Blo 459783 460931 := bstep (se 1 (by rfl) ⟨345698, by rfl⟩ : syracuseStep 460931 = 691397) B691397
theorem B657553 : Blo 459783 657553 := bstep (se 2 (by rfl) ⟨246582, by rfl⟩ : syracuseStep 657553 = 493165) B493165
theorem B690323 : Blo 459783 690323 := bstep (se 1 (by rfl) ⟨517742, by rfl⟩ : syracuseStep 690323 = 1035485) B1035485
theorem B460947 : Blo 459783 460947 := bstep (se 1 (by rfl) ⟨345710, by rfl⟩ : syracuseStep 460947 = 691421) B691421
theorem B460963 : Blo 459783 460963 := bstep (se 1 (by rfl) ⟨345722, by rfl⟩ : syracuseStep 460963 = 691445) B691445
theorem B690353 : Blo 459783 690353 := bstep (se 2 (by rfl) ⟨258882, by rfl⟩ : syracuseStep 690353 = 517765) B517765
theorem B460979 : Blo 459783 460979 := bstep (se 1 (by rfl) ⟨345734, by rfl⟩ : syracuseStep 460979 = 691469) B691469
theorem B690371 : Blo 459783 690371 := bstep (se 1 (by rfl) ⟨517778, by rfl⟩ : syracuseStep 690371 = 1035557) B1035557
theorem B460995 : Blo 459783 460995 := bstep (se 1 (by rfl) ⟨345746, by rfl⟩ : syracuseStep 460995 = 691493) B691493
theorem B461011 : Blo 459783 461011 := bstep (se 1 (by rfl) ⟨345758, by rfl⟩ : syracuseStep 461011 = 691517) B691517
theorem B690401 : Blo 459783 690401 := bstep (se 2 (by rfl) ⟨258900, by rfl⟩ : syracuseStep 690401 = 517801) B517801
theorem B461027 : Blo 459783 461027 := bstep (se 1 (by rfl) ⟨345770, by rfl⟩ : syracuseStep 461027 = 691541) B691541
theorem B657649 : Blo 459783 657649 := bstep (se 2 (by rfl) ⟨246618, by rfl⟩ : syracuseStep 657649 = 493237) B493237
theorem B690419 : Blo 459783 690419 := bstep (se 1 (by rfl) ⟨517814, by rfl⟩ : syracuseStep 690419 = 1035629) B1035629
theorem B461043 : Blo 459783 461043 := bstep (se 1 (by rfl) ⟨345782, by rfl⟩ : syracuseStep 461043 = 691565) B691565
theorem B461059 : Blo 459783 461059 := bstep (se 1 (by rfl) ⟨345794, by rfl⟩ : syracuseStep 461059 = 691589) B691589
theorem B690449 : Blo 459783 690449 := bstep (se 2 (by rfl) ⟨258918, by rfl⟩ : syracuseStep 690449 = 517837) B517837
theorem B461075 : Blo 459783 461075 := bstep (se 1 (by rfl) ⟨345806, by rfl⟩ : syracuseStep 461075 = 691613) B691613
theorem B690467 : Blo 459783 690467 := bstep (se 1 (by rfl) ⟨517850, by rfl⟩ : syracuseStep 690467 = 1035701) B1035701
theorem B461091 : Blo 459783 461091 := bstep (se 1 (by rfl) ⟨345818, by rfl⟩ : syracuseStep 461091 = 691637) B691637
theorem B461107 : Blo 459783 461107 := bstep (se 1 (by rfl) ⟨345830, by rfl⟩ : syracuseStep 461107 = 691661) B691661
theorem B690497 : Blo 459783 690497 := bstep (se 2 (by rfl) ⟨258936, by rfl⟩ : syracuseStep 690497 = 517873) B517873
theorem B461123 : Blo 459783 461123 := bstep (se 1 (by rfl) ⟨345842, by rfl⟩ : syracuseStep 461123 = 691685) B691685
theorem B690515 : Blo 459783 690515 := bstep (se 1 (by rfl) ⟨517886, by rfl⟩ : syracuseStep 690515 = 1035773) B1035773
theorem B461139 : Blo 459783 461139 := bstep (se 1 (by rfl) ⟨345854, by rfl⟩ : syracuseStep 461139 = 691709) B691709
theorem B461155 : Blo 459783 461155 := bstep (se 1 (by rfl) ⟨345866, by rfl⟩ : syracuseStep 461155 = 691733) B691733
theorem B690545 : Blo 459783 690545 := bstep (se 2 (by rfl) ⟨258954, by rfl⟩ : syracuseStep 690545 = 517909) B517909
theorem B461171 : Blo 459783 461171 := bstep (se 1 (by rfl) ⟨345878, by rfl⟩ : syracuseStep 461171 = 691757) B691757
theorem B690563 : Blo 459783 690563 := bstep (se 1 (by rfl) ⟨517922, by rfl⟩ : syracuseStep 690563 = 1035845) B1035845
theorem B461187 : Blo 459783 461187 := bstep (se 1 (by rfl) ⟨345890, by rfl⟩ : syracuseStep 461187 = 691781) B691781
theorem B1247633 : Blo 459783 1247633 := bstep (se 2 (by rfl) ⟨467862, by rfl⟩ : syracuseStep 1247633 = 935725) B935725
theorem B461203 : Blo 459783 461203 := bstep (se 1 (by rfl) ⟨345902, by rfl⟩ : syracuseStep 461203 = 691805) B691805
theorem B690593 : Blo 459783 690593 := bstep (se 2 (by rfl) ⟨258972, by rfl⟩ : syracuseStep 690593 = 517945) B517945
theorem B461219 : Blo 459783 461219 := bstep (se 1 (by rfl) ⟨345914, by rfl⟩ : syracuseStep 461219 = 691829) B691829
theorem B690611 : Blo 459783 690611 := bstep (se 1 (by rfl) ⟨517958, by rfl⟩ : syracuseStep 690611 = 1035917) B1035917
theorem B461235 : Blo 459783 461235 := bstep (se 1 (by rfl) ⟨345926, by rfl⟩ : syracuseStep 461235 = 691853) B691853
theorem B461251 : Blo 459783 461251 := bstep (se 1 (by rfl) ⟨345938, by rfl⟩ : syracuseStep 461251 = 691877) B691877
theorem B690641 : Blo 459783 690641 := bstep (se 2 (by rfl) ⟨258990, by rfl⟩ : syracuseStep 690641 = 517981) B517981
theorem B461267 : Blo 459783 461267 := bstep (se 1 (by rfl) ⟨345950, by rfl⟩ : syracuseStep 461267 = 691901) B691901
theorem B690659 : Blo 459783 690659 := bstep (se 1 (by rfl) ⟨517994, by rfl⟩ : syracuseStep 690659 = 1035989) B1035989
theorem B461283 : Blo 459783 461283 := bstep (se 1 (by rfl) ⟨345962, by rfl⟩ : syracuseStep 461283 = 691925) B691925
theorem B2329073 : Blo 459783 2329073 := bstep (se 2 (by rfl) ⟨873402, by rfl⟩ : syracuseStep 2329073 = 1746805) B1746805
theorem B461299 : Blo 459783 461299 := bstep (se 1 (by rfl) ⟨345974, by rfl⟩ : syracuseStep 461299 = 691949) B691949
theorem B690689 : Blo 459783 690689 := bstep (se 2 (by rfl) ⟨259008, by rfl⟩ : syracuseStep 690689 = 518017) B518017
theorem B461315 : Blo 459783 461315 := bstep (se 1 (by rfl) ⟨345986, by rfl⟩ : syracuseStep 461315 = 691973) B691973
theorem B985603 : Blo 459783 985603 := bstep (se 1 (by rfl) ⟨739202, by rfl⟩ : syracuseStep 985603 = 1478405) B1478405
theorem B690707 : Blo 459783 690707 := bstep (se 1 (by rfl) ⟨518030, by rfl⟩ : syracuseStep 690707 = 1036061) B1036061
theorem B461331 : Blo 459783 461331 := bstep (se 1 (by rfl) ⟨345998, by rfl⟩ : syracuseStep 461331 = 691997) B691997
theorem B2624035 : Blo 459783 2624035 := bstep (se 1 (by rfl) ⟨1968026, by rfl⟩ : syracuseStep 2624035 = 3936053) B3936053
theorem B461347 : Blo 459783 461347 := bstep (se 1 (by rfl) ⟨346010, by rfl⟩ : syracuseStep 461347 = 692021) B692021
theorem B690737 : Blo 459783 690737 := bstep (se 2 (by rfl) ⟨259026, by rfl⟩ : syracuseStep 690737 = 518053) B518053
theorem B461363 : Blo 459783 461363 := bstep (se 1 (by rfl) ⟨346022, by rfl⟩ : syracuseStep 461363 = 692045) B692045
theorem B690755 : Blo 459783 690755 := bstep (se 1 (by rfl) ⟨518066, by rfl⟩ : syracuseStep 690755 = 1036133) B1036133
theorem B789059 : Blo 459783 789059 := bstep (se 1 (by rfl) ⟨591794, by rfl⟩ : syracuseStep 789059 = 1183589) B1183589
theorem B461379 : Blo 459783 461379 := bstep (se 1 (by rfl) ⟨346034, by rfl⟩ : syracuseStep 461379 = 692069) B692069
theorem B526915 : Blo 459783 526915 := bstep (se 1 (by rfl) ⟨395186, by rfl⟩ : syracuseStep 526915 = 790373) B790373
theorem B461395 : Blo 459783 461395 := bstep (se 1 (by rfl) ⟨346046, by rfl⟩ : syracuseStep 461395 = 692093) B692093
theorem B625249 : Blo 459783 625249 := bstep (se 2 (by rfl) ⟨234468, by rfl⟩ : syracuseStep 625249 = 468937) B468937
theorem B690785 : Blo 459783 690785 := bstep (se 2 (by rfl) ⟨259044, by rfl⟩ : syracuseStep 690785 = 518089) B518089
theorem B461411 : Blo 459783 461411 := bstep (se 1 (by rfl) ⟨346058, by rfl⟩ : syracuseStep 461411 = 692117) B692117
theorem B690803 : Blo 459783 690803 := bstep (se 1 (by rfl) ⟨518102, by rfl⟩ : syracuseStep 690803 = 1036205) B1036205
theorem B461427 : Blo 459783 461427 := bstep (se 1 (by rfl) ⟨346070, by rfl⟩ : syracuseStep 461427 = 692141) B692141
theorem B461443 : Blo 459783 461443 := bstep (se 1 (by rfl) ⟨346082, by rfl⟩ : syracuseStep 461443 = 692165) B692165
theorem B690833 : Blo 459783 690833 := bstep (se 2 (by rfl) ⟨259062, by rfl⟩ : syracuseStep 690833 = 518125) B518125
theorem B461459 : Blo 459783 461459 := bstep (se 1 (by rfl) ⟨346094, by rfl⟩ : syracuseStep 461459 = 692189) B692189
theorem B690851 : Blo 459783 690851 := bstep (se 1 (by rfl) ⟨518138, by rfl⟩ : syracuseStep 690851 = 1036277) B1036277
theorem B461475 : Blo 459783 461475 := bstep (se 1 (by rfl) ⟨346106, by rfl⟩ : syracuseStep 461475 = 692213) B692213
theorem B461491 : Blo 459783 461491 := bstep (se 1 (by rfl) ⟨346118, by rfl⟩ : syracuseStep 461491 = 692237) B692237
theorem B690881 : Blo 459783 690881 := bstep (se 2 (by rfl) ⟨259080, by rfl⟩ : syracuseStep 690881 = 518161) B518161
theorem B461507 : Blo 459783 461507 := bstep (se 1 (by rfl) ⟨346130, by rfl⟩ : syracuseStep 461507 = 692261) B692261
theorem B690899 : Blo 459783 690899 := bstep (se 1 (by rfl) ⟨518174, by rfl⟩ : syracuseStep 690899 = 1036349) B1036349
theorem B461523 : Blo 459783 461523 := bstep (se 1 (by rfl) ⟨346142, by rfl⟩ : syracuseStep 461523 = 692285) B692285
theorem B658145 : Blo 459783 658145 := bstep (se 2 (by rfl) ⟨246804, by rfl⟩ : syracuseStep 658145 = 493609) B493609
theorem B461539 : Blo 459783 461539 := bstep (se 1 (by rfl) ⟨346154, by rfl⟩ : syracuseStep 461539 = 692309) B692309
theorem B690929 : Blo 459783 690929 := bstep (se 2 (by rfl) ⟨259098, by rfl⟩ : syracuseStep 690929 = 518197) B518197
theorem B461555 : Blo 459783 461555 := bstep (se 1 (by rfl) ⟨346166, by rfl⟩ : syracuseStep 461555 = 692333) B692333
theorem B690947 : Blo 459783 690947 := bstep (se 1 (by rfl) ⟨518210, by rfl⟩ : syracuseStep 690947 = 1036421) B1036421
theorem B1477379 : Blo 459783 1477379 := bstep (se 1 (by rfl) ⟨1108034, by rfl⟩ : syracuseStep 1477379 = 2216069) B2216069
theorem B461571 : Blo 459783 461571 := bstep (se 1 (by rfl) ⟨346178, by rfl⟩ : syracuseStep 461571 = 692357) B692357
theorem B985859 : Blo 459783 985859 := bstep (se 1 (by rfl) ⟨739394, by rfl⟩ : syracuseStep 985859 = 1478789) B1478789
theorem B461587 : Blo 459783 461587 := bstep (se 1 (by rfl) ⟨346190, by rfl⟩ : syracuseStep 461587 = 692381) B692381
theorem B690977 : Blo 459783 690977 := bstep (se 2 (by rfl) ⟨259116, by rfl⟩ : syracuseStep 690977 = 518233) B518233
theorem B461603 : Blo 459783 461603 := bstep (se 1 (by rfl) ⟨346202, by rfl⟩ : syracuseStep 461603 = 692405) B692405
theorem B690995 : Blo 459783 690995 := bstep (se 1 (by rfl) ⟨518246, by rfl⟩ : syracuseStep 690995 = 1036493) B1036493
theorem B461619 : Blo 459783 461619 := bstep (se 1 (by rfl) ⟨346214, by rfl⟩ : syracuseStep 461619 = 692429) B692429
theorem B461635 : Blo 459783 461635 := bstep (se 1 (by rfl) ⟨346226, by rfl⟩ : syracuseStep 461635 = 692453) B692453
theorem B691025 : Blo 459783 691025 := bstep (se 2 (by rfl) ⟨259134, by rfl⟩ : syracuseStep 691025 = 518269) B518269
theorem B461651 : Blo 459783 461651 := bstep (se 1 (by rfl) ⟨346238, by rfl⟩ : syracuseStep 461651 = 692477) B692477
theorem B2657123 : Blo 459783 2657123 := bstep (se 1 (by rfl) ⟨1992842, by rfl⟩ : syracuseStep 2657123 = 3985685) B3985685
theorem B691043 : Blo 459783 691043 := bstep (se 1 (by rfl) ⟨518282, by rfl⟩ : syracuseStep 691043 = 1036565) B1036565
theorem B461667 : Blo 459783 461667 := bstep (se 1 (by rfl) ⟨346250, by rfl⟩ : syracuseStep 461667 = 692501) B692501
theorem B461683 : Blo 459783 461683 := bstep (se 1 (by rfl) ⟨346262, by rfl⟩ : syracuseStep 461683 = 692525) B692525
theorem B691073 : Blo 459783 691073 := bstep (se 2 (by rfl) ⟨259152, by rfl⟩ : syracuseStep 691073 = 518305) B518305
theorem B461699 : Blo 459783 461699 := bstep (se 1 (by rfl) ⟨346274, by rfl⟩ : syracuseStep 461699 = 692549) B692549
theorem B494467 : Blo 459783 494467 := bstep (se 1 (by rfl) ⟨370850, by rfl⟩ : syracuseStep 494467 = 741701) B741701
theorem B691091 : Blo 459783 691091 := bstep (se 1 (by rfl) ⟨518318, by rfl⟩ : syracuseStep 691091 = 1036637) B1036637
theorem B461715 : Blo 459783 461715 := bstep (se 1 (by rfl) ⟨346286, by rfl⟩ : syracuseStep 461715 = 692573) B692573
theorem B461731 : Blo 459783 461731 := bstep (se 1 (by rfl) ⟨346298, by rfl⟩ : syracuseStep 461731 = 692597) B692597
theorem B691121 : Blo 459783 691121 := bstep (se 2 (by rfl) ⟨259170, by rfl⟩ : syracuseStep 691121 = 518341) B518341
theorem B461747 : Blo 459783 461747 := bstep (se 1 (by rfl) ⟨346310, by rfl⟩ : syracuseStep 461747 = 692621) B692621
theorem B691139 : Blo 459783 691139 := bstep (se 1 (by rfl) ⟨518354, by rfl⟩ : syracuseStep 691139 = 1036709) B1036709
theorem B461763 : Blo 459783 461763 := bstep (se 1 (by rfl) ⟨346322, by rfl⟩ : syracuseStep 461763 = 692645) B692645
theorem B461779 : Blo 459783 461779 := bstep (se 1 (by rfl) ⟨346334, by rfl⟩ : syracuseStep 461779 = 692669) B692669
theorem B691169 : Blo 459783 691169 := bstep (se 2 (by rfl) ⟨259188, by rfl⟩ : syracuseStep 691169 = 518377) B518377
theorem B461795 : Blo 459783 461795 := bstep (se 1 (by rfl) ⟨346346, by rfl⟩ : syracuseStep 461795 = 692693) B692693
theorem B625649 : Blo 459783 625649 := bstep (se 2 (by rfl) ⟨234618, by rfl⟩ : syracuseStep 625649 = 469237) B469237
theorem B691187 : Blo 459783 691187 := bstep (se 1 (by rfl) ⟨518390, by rfl⟩ : syracuseStep 691187 = 1036781) B1036781
theorem B461811 : Blo 459783 461811 := bstep (se 1 (by rfl) ⟨346358, by rfl⟩ : syracuseStep 461811 = 692717) B692717
theorem B1313795 : Blo 459783 1313795 := bstep (se 1 (by rfl) ⟨985346, by rfl⟩ : syracuseStep 1313795 = 1970693) B1970693
theorem B461827 : Blo 459783 461827 := bstep (se 1 (by rfl) ⟨346370, by rfl⟩ : syracuseStep 461827 = 692741) B692741
theorem B691217 : Blo 459783 691217 := bstep (se 2 (by rfl) ⟨259206, by rfl⟩ : syracuseStep 691217 = 518413) B518413
theorem B461843 : Blo 459783 461843 := bstep (se 1 (by rfl) ⟨346382, by rfl⟩ : syracuseStep 461843 = 692765) B692765
theorem B691235 : Blo 459783 691235 := bstep (se 1 (by rfl) ⟨518426, by rfl⟩ : syracuseStep 691235 = 1036853) B1036853
theorem B461859 : Blo 459783 461859 := bstep (se 1 (by rfl) ⟨346394, by rfl⟩ : syracuseStep 461859 = 692789) B692789
theorem B2624561 : Blo 459783 2624561 := bstep (se 2 (by rfl) ⟨984210, by rfl⟩ : syracuseStep 2624561 = 1968421) B1968421
theorem B461875 : Blo 459783 461875 := bstep (se 1 (by rfl) ⟨346406, by rfl⟩ : syracuseStep 461875 = 692813) B692813
theorem B691265 : Blo 459783 691265 := bstep (se 2 (by rfl) ⟨259224, by rfl⟩ : syracuseStep 691265 = 518449) B518449
theorem B461891 : Blo 459783 461891 := bstep (se 1 (by rfl) ⟨346418, by rfl⟩ : syracuseStep 461891 = 692837) B692837
theorem B691283 : Blo 459783 691283 := bstep (se 1 (by rfl) ⟨518462, by rfl⟩ : syracuseStep 691283 = 1036925) B1036925
theorem B461907 : Blo 459783 461907 := bstep (se 1 (by rfl) ⟨346430, by rfl⟩ : syracuseStep 461907 = 692861) B692861
theorem B461923 : Blo 459783 461923 := bstep (se 1 (by rfl) ⟨346442, by rfl⟩ : syracuseStep 461923 = 692885) B692885
theorem B691313 : Blo 459783 691313 := bstep (se 2 (by rfl) ⟨259242, by rfl⟩ : syracuseStep 691313 = 518485) B518485
theorem B461939 : Blo 459783 461939 := bstep (se 1 (by rfl) ⟨346454, by rfl⟩ : syracuseStep 461939 = 692909) B692909
theorem B691331 : Blo 459783 691331 := bstep (se 1 (by rfl) ⟨518498, by rfl⟩ : syracuseStep 691331 = 1036997) B1036997
theorem B461955 : Blo 459783 461955 := bstep (se 1 (by rfl) ⟨346466, by rfl⟩ : syracuseStep 461955 = 692933) B692933
theorem B5934221 : Blo 459783 5934221 := bstep (se 3 (by rfl) ⟨1112666, by rfl⟩ : syracuseStep 5934221 = 2225333) B2225333
theorem B461971 : Blo 459783 461971 := bstep (se 1 (by rfl) ⟨346478, by rfl⟩ : syracuseStep 461971 = 692957) B692957
theorem B691361 : Blo 459783 691361 := bstep (se 2 (by rfl) ⟨259260, by rfl⟩ : syracuseStep 691361 = 518521) B518521
theorem B461987 : Blo 459783 461987 := bstep (se 1 (by rfl) ⟨346490, by rfl⟩ : syracuseStep 461987 = 692981) B692981
theorem B691379 : Blo 459783 691379 := bstep (se 1 (by rfl) ⟨518534, by rfl⟩ : syracuseStep 691379 = 1037069) B1037069
theorem B462003 : Blo 459783 462003 := bstep (se 1 (by rfl) ⟨346502, by rfl⟩ : syracuseStep 462003 = 693005) B693005
theorem B462019 : Blo 459783 462019 := bstep (se 1 (by rfl) ⟨346514, by rfl⟩ : syracuseStep 462019 = 693029) B693029
theorem B691409 : Blo 459783 691409 := bstep (se 2 (by rfl) ⟨259278, by rfl⟩ : syracuseStep 691409 = 518557) B518557
theorem B462035 : Blo 459783 462035 := bstep (se 1 (by rfl) ⟨346526, by rfl⟩ : syracuseStep 462035 = 693053) B693053
theorem B691427 : Blo 459783 691427 := bstep (se 1 (by rfl) ⟨518570, by rfl⟩ : syracuseStep 691427 = 1037141) B1037141
theorem B1969379 : Blo 459783 1969379 := bstep (se 1 (by rfl) ⟨1477034, by rfl⟩ : syracuseStep 1969379 = 2954069) B2954069
theorem B462051 : Blo 459783 462051 := bstep (se 1 (by rfl) ⟨346538, by rfl⟩ : syracuseStep 462051 = 693077) B693077
theorem B462067 : Blo 459783 462067 := bstep (se 1 (by rfl) ⟨346550, by rfl⟩ : syracuseStep 462067 = 693101) B693101
theorem B691457 : Blo 459783 691457 := bstep (se 2 (by rfl) ⟨259296, by rfl⟩ : syracuseStep 691457 = 518593) B518593
theorem B462083 : Blo 459783 462083 := bstep (se 1 (by rfl) ⟨346562, by rfl⟩ : syracuseStep 462083 = 693125) B693125
theorem B691475 : Blo 459783 691475 := bstep (se 1 (by rfl) ⟨518606, by rfl⟩ : syracuseStep 691475 = 1037213) B1037213
theorem B462099 : Blo 459783 462099 := bstep (se 1 (by rfl) ⟨346574, by rfl⟩ : syracuseStep 462099 = 693149) B693149
theorem B462115 : Blo 459783 462115 := bstep (se 1 (by rfl) ⟨346586, by rfl⟩ : syracuseStep 462115 = 693173) B693173
theorem B691505 : Blo 459783 691505 := bstep (se 2 (by rfl) ⟨259314, by rfl⟩ : syracuseStep 691505 = 518629) B518629
theorem B462131 : Blo 459783 462131 := bstep (se 1 (by rfl) ⟨346598, by rfl⟩ : syracuseStep 462131 = 693197) B693197
theorem B691523 : Blo 459783 691523 := bstep (se 1 (by rfl) ⟨518642, by rfl⟩ : syracuseStep 691523 = 1037285) B1037285
theorem B462147 : Blo 459783 462147 := bstep (se 1 (by rfl) ⟨346610, by rfl⟩ : syracuseStep 462147 = 693221) B693221
theorem B2493773 : Blo 459783 2493773 := bstep (se 3 (by rfl) ⟨467582, by rfl⟩ : syracuseStep 2493773 = 935165) B935165
theorem B462163 : Blo 459783 462163 := bstep (se 1 (by rfl) ⟨346622, by rfl⟩ : syracuseStep 462163 = 693245) B693245
theorem B691553 : Blo 459783 691553 := bstep (se 2 (by rfl) ⟨259332, by rfl⟩ : syracuseStep 691553 = 518665) B518665
theorem B1871203 : Blo 459783 1871203 := bstep (se 1 (by rfl) ⟨1403402, by rfl⟩ : syracuseStep 1871203 = 2806805) B2806805
theorem B462179 : Blo 459783 462179 := bstep (se 1 (by rfl) ⟨346634, by rfl⟩ : syracuseStep 462179 = 693269) B693269
theorem B2035057 : Blo 459783 2035057 := bstep (se 2 (by rfl) ⟨763146, by rfl⟩ : syracuseStep 2035057 = 1526293) B1526293
theorem B691571 : Blo 459783 691571 := bstep (se 1 (by rfl) ⟨518678, by rfl⟩ : syracuseStep 691571 = 1037357) B1037357
theorem B462195 : Blo 459783 462195 := bstep (se 1 (by rfl) ⟨346646, by rfl⟩ : syracuseStep 462195 = 693293) B693293
theorem B462211 : Blo 459783 462211 := bstep (se 1 (by rfl) ⟨346658, by rfl⟩ : syracuseStep 462211 = 693317) B693317
theorem B691601 : Blo 459783 691601 := bstep (se 2 (by rfl) ⟨259350, by rfl⟩ : syracuseStep 691601 = 518701) B518701
theorem B462227 : Blo 459783 462227 := bstep (se 1 (by rfl) ⟨346670, by rfl⟩ : syracuseStep 462227 = 693341) B693341
theorem B691619 : Blo 459783 691619 := bstep (se 1 (by rfl) ⟨518714, by rfl⟩ : syracuseStep 691619 = 1037429) B1037429
theorem B462243 : Blo 459783 462243 := bstep (se 1 (by rfl) ⟨346682, by rfl⟩ : syracuseStep 462243 = 693365) B693365
theorem B462259 : Blo 459783 462259 := bstep (se 1 (by rfl) ⟨346694, by rfl⟩ : syracuseStep 462259 = 693389) B693389
theorem B691649 : Blo 459783 691649 := bstep (se 2 (by rfl) ⟨259368, by rfl⟩ : syracuseStep 691649 = 518737) B518737
theorem B626113 : Blo 459783 626113 := bstep (se 2 (by rfl) ⟨234792, by rfl⟩ : syracuseStep 626113 = 469585) B469585
theorem B462275 : Blo 459783 462275 := bstep (se 1 (by rfl) ⟨346706, by rfl⟩ : syracuseStep 462275 = 693413) B693413
theorem B691667 : Blo 459783 691667 := bstep (se 1 (by rfl) ⟨518750, by rfl⟩ : syracuseStep 691667 = 1037501) B1037501
theorem B462291 : Blo 459783 462291 := bstep (se 1 (by rfl) ⟨346718, by rfl⟩ : syracuseStep 462291 = 693437) B693437
theorem B462307 : Blo 459783 462307 := bstep (se 1 (by rfl) ⟨346730, by rfl⟩ : syracuseStep 462307 = 693461) B693461
theorem B691697 : Blo 459783 691697 := bstep (se 2 (by rfl) ⟨259386, by rfl⟩ : syracuseStep 691697 = 518773) B518773
theorem B462323 : Blo 459783 462323 := bstep (se 1 (by rfl) ⟨346742, by rfl⟩ : syracuseStep 462323 = 693485) B693485
theorem B691715 : Blo 459783 691715 := bstep (se 1 (by rfl) ⟨518786, by rfl⟩ : syracuseStep 691715 = 1037573) B1037573
theorem B462339 : Blo 459783 462339 := bstep (se 1 (by rfl) ⟨346754, by rfl⟩ : syracuseStep 462339 = 693509) B693509
theorem B462355 : Blo 459783 462355 := bstep (se 1 (by rfl) ⟨346766, by rfl⟩ : syracuseStep 462355 = 693533) B693533
theorem B691745 : Blo 459783 691745 := bstep (se 2 (by rfl) ⟨259404, by rfl⟩ : syracuseStep 691745 = 518809) B518809
theorem B462371 : Blo 459783 462371 := bstep (se 1 (by rfl) ⟨346778, by rfl⟩ : syracuseStep 462371 = 693557) B693557
theorem B691763 : Blo 459783 691763 := bstep (se 1 (by rfl) ⟨518822, by rfl⟩ : syracuseStep 691763 = 1037645) B1037645
theorem B462387 : Blo 459783 462387 := bstep (se 1 (by rfl) ⟨346790, by rfl⟩ : syracuseStep 462387 = 693581) B693581
theorem B462403 : Blo 459783 462403 := bstep (se 1 (by rfl) ⟨346802, by rfl⟩ : syracuseStep 462403 = 693605) B693605
theorem B659011 : Blo 459783 659011 := bstep (se 1 (by rfl) ⟨494258, by rfl⟩ : syracuseStep 659011 = 988517) B988517
theorem B691793 : Blo 459783 691793 := bstep (se 2 (by rfl) ⟨259422, by rfl⟩ : syracuseStep 691793 = 518845) B518845
theorem B1478225 : Blo 459783 1478225 := bstep (se 2 (by rfl) ⟨554334, by rfl⟩ : syracuseStep 1478225 = 1108669) B1108669
theorem B462419 : Blo 459783 462419 := bstep (se 1 (by rfl) ⟨346814, by rfl⟩ : syracuseStep 462419 = 693629) B693629
theorem B691811 : Blo 459783 691811 := bstep (se 1 (by rfl) ⟨518858, by rfl⟩ : syracuseStep 691811 = 1037717) B1037717
theorem B462435 : Blo 459783 462435 := bstep (se 1 (by rfl) ⟨346826, by rfl⟩ : syracuseStep 462435 = 693653) B693653
theorem B462451 : Blo 459783 462451 := bstep (se 1 (by rfl) ⟨346838, by rfl⟩ : syracuseStep 462451 = 693677) B693677
theorem B691841 : Blo 459783 691841 := bstep (se 2 (by rfl) ⟨259440, by rfl⟩ : syracuseStep 691841 = 518881) B518881
theorem B462467 : Blo 459783 462467 := bstep (se 1 (by rfl) ⟨346850, by rfl⟩ : syracuseStep 462467 = 693701) B693701
theorem B1904269 : Blo 459783 1904269 := bstep (se 3 (by rfl) ⟨357050, by rfl⟩ : syracuseStep 1904269 = 714101) B714101
theorem B691859 : Blo 459783 691859 := bstep (se 1 (by rfl) ⟨518894, by rfl⟩ : syracuseStep 691859 = 1037789) B1037789
theorem B462483 : Blo 459783 462483 := bstep (se 1 (by rfl) ⟨346862, by rfl⟩ : syracuseStep 462483 = 693725) B693725
theorem B462499 : Blo 459783 462499 := bstep (se 1 (by rfl) ⟨346874, by rfl⟩ : syracuseStep 462499 = 693749) B693749
theorem B659107 : Blo 459783 659107 := bstep (se 1 (by rfl) ⟨494330, by rfl⟩ : syracuseStep 659107 = 988661) B988661
theorem B691889 : Blo 459783 691889 := bstep (se 2 (by rfl) ⟨259458, by rfl⟩ : syracuseStep 691889 = 518917) B518917
theorem B462515 : Blo 459783 462515 := bstep (se 1 (by rfl) ⟨346886, by rfl⟩ : syracuseStep 462515 = 693773) B693773
theorem B691907 : Blo 459783 691907 := bstep (se 1 (by rfl) ⟨518930, by rfl⟩ : syracuseStep 691907 = 1037861) B1037861
theorem B462531 : Blo 459783 462531 := bstep (se 1 (by rfl) ⟨346898, by rfl⟩ : syracuseStep 462531 = 693797) B693797
theorem B986833 : Blo 459783 986833 := bstep (se 2 (by rfl) ⟨370062, by rfl⟩ : syracuseStep 986833 = 740125) B740125
theorem B462547 : Blo 459783 462547 := bstep (se 1 (by rfl) ⟨346910, by rfl⟩ : syracuseStep 462547 = 693821) B693821
theorem B691937 : Blo 459783 691937 := bstep (se 2 (by rfl) ⟨259476, by rfl⟩ : syracuseStep 691937 = 518953) B518953
theorem B462563 : Blo 459783 462563 := bstep (se 1 (by rfl) ⟨346922, by rfl⟩ : syracuseStep 462563 = 693845) B693845
theorem B691955 : Blo 459783 691955 := bstep (se 1 (by rfl) ⟨518966, by rfl⟩ : syracuseStep 691955 = 1037933) B1037933
theorem B462579 : Blo 459783 462579 := bstep (se 1 (by rfl) ⟨346934, by rfl⟩ : syracuseStep 462579 = 693869) B693869
theorem B462595 : Blo 459783 462595 := bstep (se 1 (by rfl) ⟨346946, by rfl⟩ : syracuseStep 462595 = 693893) B693893
theorem B691985 : Blo 459783 691985 := bstep (se 2 (by rfl) ⟨259494, by rfl⟩ : syracuseStep 691985 = 518989) B518989
theorem B462611 : Blo 459783 462611 := bstep (se 1 (by rfl) ⟨346958, by rfl⟩ : syracuseStep 462611 = 693917) B693917
theorem B692003 : Blo 459783 692003 := bstep (se 1 (by rfl) ⟨519002, by rfl⟩ : syracuseStep 692003 = 1038005) B1038005
theorem B462627 : Blo 459783 462627 := bstep (se 1 (by rfl) ⟨346970, by rfl⟩ : syracuseStep 462627 = 693941) B693941
theorem B462643 : Blo 459783 462643 := bstep (se 1 (by rfl) ⟨346982, by rfl⟩ : syracuseStep 462643 = 693965) B693965
theorem B692033 : Blo 459783 692033 := bstep (se 2 (by rfl) ⟨259512, by rfl⟩ : syracuseStep 692033 = 519025) B519025
theorem B462659 : Blo 459783 462659 := bstep (se 1 (by rfl) ⟨346994, by rfl⟩ : syracuseStep 462659 = 693989) B693989
theorem B692051 : Blo 459783 692051 := bstep (se 1 (by rfl) ⟨519038, by rfl⟩ : syracuseStep 692051 = 1038077) B1038077
theorem B462675 : Blo 459783 462675 := bstep (se 1 (by rfl) ⟨347006, by rfl⟩ : syracuseStep 462675 = 694013) B694013
theorem B462691 : Blo 459783 462691 := bstep (se 1 (by rfl) ⟨347018, by rfl⟩ : syracuseStep 462691 = 694037) B694037
theorem B692081 : Blo 459783 692081 := bstep (se 2 (by rfl) ⟨259530, by rfl⟩ : syracuseStep 692081 = 519061) B519061
theorem B462707 : Blo 459783 462707 := bstep (se 1 (by rfl) ⟨347030, by rfl⟩ : syracuseStep 462707 = 694061) B694061
theorem B462723 : Blo 459783 462723 := bstep (se 1 (by rfl) ⟨347042, by rfl⟩ : syracuseStep 462723 = 694085) B694085
theorem B692099 : Blo 459783 692099 := bstep (se 1 (by rfl) ⟨519074, by rfl⟩ : syracuseStep 692099 = 1038149) B1038149
theorem B888707 : Blo 459783 888707 := bstep (se 1 (by rfl) ⟨666530, by rfl⟩ : syracuseStep 888707 = 1333061) B1333061
theorem B462739 : Blo 459783 462739 := bstep (se 1 (by rfl) ⟨347054, by rfl⟩ : syracuseStep 462739 = 694109) B694109
theorem B692129 : Blo 459783 692129 := bstep (se 2 (by rfl) ⟨259548, by rfl⟩ : syracuseStep 692129 = 519097) B519097
theorem B2330531 : Blo 459783 2330531 := bstep (se 1 (by rfl) ⟨1747898, by rfl⟩ : syracuseStep 2330531 = 3495797) B3495797
theorem B462755 : Blo 459783 462755 := bstep (se 1 (by rfl) ⟨347066, by rfl⟩ : syracuseStep 462755 = 694133) B694133
theorem B692147 : Blo 459783 692147 := bstep (se 1 (by rfl) ⟨519110, by rfl⟩ : syracuseStep 692147 = 1038221) B1038221
theorem B462771 : Blo 459783 462771 := bstep (se 1 (by rfl) ⟨347078, by rfl⟩ : syracuseStep 462771 = 694157) B694157
theorem B462787 : Blo 459783 462787 := bstep (se 1 (by rfl) ⟨347090, by rfl⟩ : syracuseStep 462787 = 694181) B694181
theorem B626627 : Blo 459783 626627 := bstep (se 1 (by rfl) ⟨469970, by rfl⟩ : syracuseStep 626627 = 939941) B939941
theorem B692177 : Blo 459783 692177 := bstep (se 2 (by rfl) ⟨259566, by rfl⟩ : syracuseStep 692177 = 519133) B519133
theorem B462803 : Blo 459783 462803 := bstep (se 1 (by rfl) ⟨347102, by rfl⟩ : syracuseStep 462803 = 694205) B694205
theorem B692195 : Blo 459783 692195 := bstep (se 1 (by rfl) ⟨519146, by rfl⟩ : syracuseStep 692195 = 1038293) B1038293
theorem B462819 : Blo 459783 462819 := bstep (se 1 (by rfl) ⟨347114, by rfl⟩ : syracuseStep 462819 = 694229) B694229
theorem B462835 : Blo 459783 462835 := bstep (se 1 (by rfl) ⟨347126, by rfl⟩ : syracuseStep 462835 = 694253) B694253
theorem B692225 : Blo 459783 692225 := bstep (se 2 (by rfl) ⟨259584, by rfl⟩ : syracuseStep 692225 = 519169) B519169
theorem B462851 : Blo 459783 462851 := bstep (se 1 (by rfl) ⟨347138, by rfl⟩ : syracuseStep 462851 = 694277) B694277
theorem B1871885 : Blo 459783 1871885 := bstep (se 3 (by rfl) ⟨350978, by rfl⟩ : syracuseStep 1871885 = 701957) B701957
theorem B462867 : Blo 459783 462867 := bstep (se 1 (by rfl) ⟨347150, by rfl⟩ : syracuseStep 462867 = 694301) B694301
theorem B692243 : Blo 459783 692243 := bstep (se 1 (by rfl) ⟨519182, by rfl⟩ : syracuseStep 692243 = 1038365) B1038365
theorem B462883 : Blo 459783 462883 := bstep (se 1 (by rfl) ⟨347162, by rfl⟩ : syracuseStep 462883 = 694325) B694325
theorem B692273 : Blo 459783 692273 := bstep (se 2 (by rfl) ⟨259602, by rfl⟩ : syracuseStep 692273 = 519205) B519205
theorem B462899 : Blo 459783 462899 := bstep (se 1 (by rfl) ⟨347174, by rfl⟩ : syracuseStep 462899 = 694349) B694349
theorem B692291 : Blo 459783 692291 := bstep (se 1 (by rfl) ⟨519218, by rfl⟩ : syracuseStep 692291 = 1038437) B1038437
theorem B462915 : Blo 459783 462915 := bstep (se 1 (by rfl) ⟨347186, by rfl⟩ : syracuseStep 462915 = 694373) B694373
theorem B462931 : Blo 459783 462931 := bstep (se 1 (by rfl) ⟨347198, by rfl⟩ : syracuseStep 462931 = 694397) B694397
theorem B692321 : Blo 459783 692321 := bstep (se 2 (by rfl) ⟨259620, by rfl⟩ : syracuseStep 692321 = 519241) B519241
theorem B462947 : Blo 459783 462947 := bstep (se 1 (by rfl) ⟨347210, by rfl⟩ : syracuseStep 462947 = 694421) B694421
theorem B692339 : Blo 459783 692339 := bstep (se 1 (by rfl) ⟨519254, by rfl⟩ : syracuseStep 692339 = 1038509) B1038509
theorem B462963 : Blo 459783 462963 := bstep (se 1 (by rfl) ⟨347222, by rfl⟩ : syracuseStep 462963 = 694445) B694445
theorem B462979 : Blo 459783 462979 := bstep (se 1 (by rfl) ⟨347234, by rfl⟩ : syracuseStep 462979 = 694469) B694469
theorem B692369 : Blo 459783 692369 := bstep (se 2 (by rfl) ⟨259638, by rfl⟩ : syracuseStep 692369 = 519277) B519277
theorem B462995 : Blo 459783 462995 := bstep (se 1 (by rfl) ⟨347246, by rfl⟩ : syracuseStep 462995 = 694493) B694493
theorem B659603 : Blo 459783 659603 := bstep (se 1 (by rfl) ⟨494702, by rfl⟩ : syracuseStep 659603 = 989405) B989405
theorem B692387 : Blo 459783 692387 := bstep (se 1 (by rfl) ⟨519290, by rfl⟩ : syracuseStep 692387 = 1038581) B1038581
theorem B463011 : Blo 459783 463011 := bstep (se 1 (by rfl) ⟨347258, by rfl⟩ : syracuseStep 463011 = 694517) B694517
theorem B463027 : Blo 459783 463027 := bstep (se 1 (by rfl) ⟨347270, by rfl⟩ : syracuseStep 463027 = 694541) B694541
theorem B692417 : Blo 459783 692417 := bstep (se 2 (by rfl) ⟨259656, by rfl⟩ : syracuseStep 692417 = 519313) B519313
theorem B463043 : Blo 459783 463043 := bstep (se 1 (by rfl) ⟨347282, by rfl⟩ : syracuseStep 463043 = 694565) B694565
theorem B1315025 : Blo 459783 1315025 := bstep (se 2 (by rfl) ⟨493134, by rfl⟩ : syracuseStep 1315025 = 986269) B986269
theorem B692435 : Blo 459783 692435 := bstep (se 1 (by rfl) ⟨519326, by rfl⟩ : syracuseStep 692435 = 1038653) B1038653
theorem B463059 : Blo 459783 463059 := bstep (se 1 (by rfl) ⟨347294, by rfl⟩ : syracuseStep 463059 = 694589) B694589
theorem B463075 : Blo 459783 463075 := bstep (se 1 (by rfl) ⟨347306, by rfl⟩ : syracuseStep 463075 = 694613) B694613
theorem B692465 : Blo 459783 692465 := bstep (se 2 (by rfl) ⟨259674, by rfl⟩ : syracuseStep 692465 = 519349) B519349
theorem B463091 : Blo 459783 463091 := bstep (se 1 (by rfl) ⟨347318, by rfl⟩ : syracuseStep 463091 = 694637) B694637
theorem B692483 : Blo 459783 692483 := bstep (se 1 (by rfl) ⟨519362, by rfl⟩ : syracuseStep 692483 = 1038725) B1038725
theorem B463107 : Blo 459783 463107 := bstep (se 1 (by rfl) ⟨347330, by rfl⟩ : syracuseStep 463107 = 694661) B694661
theorem B463123 : Blo 459783 463123 := bstep (se 1 (by rfl) ⟨347342, by rfl⟩ : syracuseStep 463123 = 694685) B694685
theorem B692513 : Blo 459783 692513 := bstep (se 2 (by rfl) ⟨259692, by rfl⟩ : syracuseStep 692513 = 519385) B519385
theorem B463139 : Blo 459783 463139 := bstep (se 1 (by rfl) ⟨347354, by rfl⟩ : syracuseStep 463139 = 694709) B694709
theorem B692531 : Blo 459783 692531 := bstep (se 1 (by rfl) ⟨519398, by rfl⟩ : syracuseStep 692531 = 1038797) B1038797
theorem B463155 : Blo 459783 463155 := bstep (se 1 (by rfl) ⟨347366, by rfl⟩ : syracuseStep 463155 = 694733) B694733
theorem B463171 : Blo 459783 463171 := bstep (se 1 (by rfl) ⟨347378, by rfl⟩ : syracuseStep 463171 = 694757) B694757
theorem B692561 : Blo 459783 692561 := bstep (se 2 (by rfl) ⟨259710, by rfl⟩ : syracuseStep 692561 = 519421) B519421
theorem B463187 : Blo 459783 463187 := bstep (se 1 (by rfl) ⟨347390, by rfl⟩ : syracuseStep 463187 = 694781) B694781
theorem B692579 : Blo 459783 692579 := bstep (se 1 (by rfl) ⟨519434, by rfl⟩ : syracuseStep 692579 = 1038869) B1038869
theorem B987491 : Blo 459783 987491 := bstep (se 1 (by rfl) ⟨740618, by rfl⟩ : syracuseStep 987491 = 1481237) B1481237
theorem B463203 : Blo 459783 463203 := bstep (se 1 (by rfl) ⟨347402, by rfl⟩ : syracuseStep 463203 = 694805) B694805
theorem B463219 : Blo 459783 463219 := bstep (se 1 (by rfl) ⟨347414, by rfl⟩ : syracuseStep 463219 = 694829) B694829
theorem B692609 : Blo 459783 692609 := bstep (se 2 (by rfl) ⟨259728, by rfl⟩ : syracuseStep 692609 = 519457) B519457
theorem B463235 : Blo 459783 463235 := bstep (se 1 (by rfl) ⟨347426, by rfl⟩ : syracuseStep 463235 = 694853) B694853
theorem B1773965 : Blo 459783 1773965 := bstep (se 3 (by rfl) ⟨332618, by rfl⟩ : syracuseStep 1773965 = 665237) B665237
theorem B692627 : Blo 459783 692627 := bstep (se 1 (by rfl) ⟨519470, by rfl⟩ : syracuseStep 692627 = 1038941) B1038941
theorem B463251 : Blo 459783 463251 := bstep (se 1 (by rfl) ⟨347438, by rfl⟩ : syracuseStep 463251 = 694877) B694877
theorem B463267 : Blo 459783 463267 := bstep (se 1 (by rfl) ⟨347450, by rfl⟩ : syracuseStep 463267 = 694901) B694901
theorem B692657 : Blo 459783 692657 := bstep (se 2 (by rfl) ⟨259746, by rfl⟩ : syracuseStep 692657 = 519493) B519493
theorem B463283 : Blo 459783 463283 := bstep (se 1 (by rfl) ⟨347462, by rfl⟩ : syracuseStep 463283 = 694925) B694925
theorem B692675 : Blo 459783 692675 := bstep (se 1 (by rfl) ⟨519506, by rfl⟩ : syracuseStep 692675 = 1039013) B1039013
theorem B463299 : Blo 459783 463299 := bstep (se 1 (by rfl) ⟨347474, by rfl⟩ : syracuseStep 463299 = 694949) B694949
theorem B463315 : Blo 459783 463315 := bstep (se 1 (by rfl) ⟨347486, by rfl⟩ : syracuseStep 463315 = 694973) B694973
theorem B692705 : Blo 459783 692705 := bstep (se 2 (by rfl) ⟨259764, by rfl⟩ : syracuseStep 692705 = 519529) B519529
theorem B2626019 : Blo 459783 2626019 := bstep (se 1 (by rfl) ⟨1969514, by rfl⟩ : syracuseStep 2626019 = 3939029) B3939029
theorem B463331 : Blo 459783 463331 := bstep (se 1 (by rfl) ⟨347498, by rfl⟩ : syracuseStep 463331 = 694997) B694997
theorem B692723 : Blo 459783 692723 := bstep (se 1 (by rfl) ⟨519542, by rfl⟩ : syracuseStep 692723 = 1039085) B1039085
theorem B463347 : Blo 459783 463347 := bstep (se 1 (by rfl) ⟨347510, by rfl⟩ : syracuseStep 463347 = 695021) B695021
theorem B463363 : Blo 459783 463363 := bstep (se 1 (by rfl) ⟨347522, by rfl⟩ : syracuseStep 463363 = 695045) B695045
theorem B1249805 : Blo 459783 1249805 := bstep (se 3 (by rfl) ⟨234338, by rfl⟩ : syracuseStep 1249805 = 468677) B468677
theorem B692753 : Blo 459783 692753 := bstep (se 2 (by rfl) ⟨259782, by rfl⟩ : syracuseStep 692753 = 519565) B519565
theorem B463379 : Blo 459783 463379 := bstep (se 1 (by rfl) ⟨347534, by rfl⟩ : syracuseStep 463379 = 695069) B695069
theorem B692771 : Blo 459783 692771 := bstep (se 1 (by rfl) ⟨519578, by rfl⟩ : syracuseStep 692771 = 1039157) B1039157
theorem B463395 : Blo 459783 463395 := bstep (se 1 (by rfl) ⟨347546, by rfl⟩ : syracuseStep 463395 = 695093) B695093
theorem B463411 : Blo 459783 463411 := bstep (se 1 (by rfl) ⟨347558, by rfl⟩ : syracuseStep 463411 = 695117) B695117
theorem B692801 : Blo 459783 692801 := bstep (se 2 (by rfl) ⟨259800, by rfl⟩ : syracuseStep 692801 = 519601) B519601
theorem B463427 : Blo 459783 463427 := bstep (se 1 (by rfl) ⟨347570, by rfl⟩ : syracuseStep 463427 = 695141) B695141
theorem B692819 : Blo 459783 692819 := bstep (se 1 (by rfl) ⟨519614, by rfl⟩ : syracuseStep 692819 = 1039229) B1039229
theorem B463443 : Blo 459783 463443 := bstep (se 1 (by rfl) ⟨347582, by rfl⟩ : syracuseStep 463443 = 695165) B695165
theorem B463459 : Blo 459783 463459 := bstep (se 1 (by rfl) ⟨347594, by rfl⟩ : syracuseStep 463459 = 695189) B695189
theorem B692849 : Blo 459783 692849 := bstep (se 2 (by rfl) ⟨259818, by rfl⟩ : syracuseStep 692849 = 519637) B519637
theorem B463475 : Blo 459783 463475 := bstep (se 1 (by rfl) ⟨347606, by rfl⟩ : syracuseStep 463475 = 695213) B695213
theorem B692867 : Blo 459783 692867 := bstep (se 1 (by rfl) ⟨519650, by rfl⟩ : syracuseStep 692867 = 1039301) B1039301
theorem B463491 : Blo 459783 463491 := bstep (se 1 (by rfl) ⟨347618, by rfl⟩ : syracuseStep 463491 = 695237) B695237
theorem B463507 : Blo 459783 463507 := bstep (se 1 (by rfl) ⟨347630, by rfl⟩ : syracuseStep 463507 = 695261) B695261
theorem B692897 : Blo 459783 692897 := bstep (se 2 (by rfl) ⟨259836, by rfl⟩ : syracuseStep 692897 = 519673) B519673
theorem B463523 : Blo 459783 463523 := bstep (se 1 (by rfl) ⟨347642, by rfl⟩ : syracuseStep 463523 = 695285) B695285
theorem B692915 : Blo 459783 692915 := bstep (se 1 (by rfl) ⟨519686, by rfl⟩ : syracuseStep 692915 = 1039373) B1039373
theorem B463539 : Blo 459783 463539 := bstep (se 1 (by rfl) ⟨347654, by rfl⟩ : syracuseStep 463539 = 695309) B695309
theorem B463555 : Blo 459783 463555 := bstep (se 1 (by rfl) ⟨347666, by rfl⟩ : syracuseStep 463555 = 695333) B695333
theorem B2331341 : Blo 459783 2331341 := bstep (se 3 (by rfl) ⟨437126, by rfl⟩ : syracuseStep 2331341 = 874253) B874253
theorem B692945 : Blo 459783 692945 := bstep (se 2 (by rfl) ⟨259854, by rfl⟩ : syracuseStep 692945 = 519709) B519709
theorem B463571 : Blo 459783 463571 := bstep (se 1 (by rfl) ⟨347678, by rfl⟩ : syracuseStep 463571 = 695357) B695357
theorem B692963 : Blo 459783 692963 := bstep (se 1 (by rfl) ⟨519722, by rfl⟩ : syracuseStep 692963 = 1039445) B1039445
theorem B463587 : Blo 459783 463587 := bstep (se 1 (by rfl) ⟨347690, by rfl⟩ : syracuseStep 463587 = 695381) B695381
theorem B463603 : Blo 459783 463603 := bstep (se 1 (by rfl) ⟨347702, by rfl⟩ : syracuseStep 463603 = 695405) B695405
theorem B692993 : Blo 459783 692993 := bstep (se 2 (by rfl) ⟨259872, by rfl⟩ : syracuseStep 692993 = 519745) B519745
theorem B463619 : Blo 459783 463619 := bstep (se 1 (by rfl) ⟨347714, by rfl⟩ : syracuseStep 463619 = 695429) B695429
theorem B660241 : Blo 459783 660241 := bstep (se 2 (by rfl) ⟨247590, by rfl⟩ : syracuseStep 660241 = 495181) B495181
theorem B693011 : Blo 459783 693011 := bstep (se 1 (by rfl) ⟨519758, by rfl⟩ : syracuseStep 693011 = 1039517) B1039517
theorem B463635 : Blo 459783 463635 := bstep (se 1 (by rfl) ⟨347726, by rfl⟩ : syracuseStep 463635 = 695453) B695453
theorem B463651 : Blo 459783 463651 := bstep (se 1 (by rfl) ⟨347738, by rfl⟩ : syracuseStep 463651 = 695477) B695477
theorem B693041 : Blo 459783 693041 := bstep (se 2 (by rfl) ⟨259890, by rfl⟩ : syracuseStep 693041 = 519781) B519781
theorem B463667 : Blo 459783 463667 := bstep (se 1 (by rfl) ⟨347750, by rfl⟩ : syracuseStep 463667 = 695501) B695501
theorem B693059 : Blo 459783 693059 := bstep (se 1 (by rfl) ⟨519794, by rfl⟩ : syracuseStep 693059 = 1039589) B1039589
theorem B463683 : Blo 459783 463683 := bstep (se 1 (by rfl) ⟨347762, by rfl⟩ : syracuseStep 463683 = 695525) B695525
theorem B463699 : Blo 459783 463699 := bstep (se 1 (by rfl) ⟨347774, by rfl⟩ : syracuseStep 463699 = 695549) B695549
theorem B693089 : Blo 459783 693089 := bstep (se 2 (by rfl) ⟨259908, by rfl⟩ : syracuseStep 693089 = 519817) B519817
theorem B1053539 : Blo 459783 1053539 := bstep (se 1 (by rfl) ⟨790154, by rfl⟩ : syracuseStep 1053539 = 1580309) B1580309
theorem B463715 : Blo 459783 463715 := bstep (se 1 (by rfl) ⟨347786, by rfl⟩ : syracuseStep 463715 = 695573) B695573
theorem B693107 : Blo 459783 693107 := bstep (se 1 (by rfl) ⟨519830, by rfl⟩ : syracuseStep 693107 = 1039661) B1039661
theorem B463731 : Blo 459783 463731 := bstep (se 1 (by rfl) ⟨347798, by rfl⟩ : syracuseStep 463731 = 695597) B695597
theorem B463747 : Blo 459783 463747 := bstep (se 1 (by rfl) ⟨347810, by rfl⟩ : syracuseStep 463747 = 695621) B695621
theorem B693137 : Blo 459783 693137 := bstep (se 2 (by rfl) ⟨259926, by rfl⟩ : syracuseStep 693137 = 519853) B519853
theorem B463763 : Blo 459783 463763 := bstep (se 1 (by rfl) ⟨347822, by rfl⟩ : syracuseStep 463763 = 695645) B695645
theorem B693155 : Blo 459783 693155 := bstep (se 1 (by rfl) ⟨519866, by rfl⟩ : syracuseStep 693155 = 1039733) B1039733
theorem B463779 : Blo 459783 463779 := bstep (se 1 (by rfl) ⟨347834, by rfl⟩ : syracuseStep 463779 = 695669) B695669
theorem B693185 : Blo 459783 693185 := bstep (se 2 (by rfl) ⟨259944, by rfl⟩ : syracuseStep 693185 = 519889) B519889
theorem B693203 : Blo 459783 693203 := bstep (se 1 (by rfl) ⟨519902, by rfl⟩ : syracuseStep 693203 = 1039805) B1039805
theorem B693233 : Blo 459783 693233 := bstep (se 2 (by rfl) ⟨259962, by rfl⟩ : syracuseStep 693233 = 519925) B519925
theorem B693251 : Blo 459783 693251 := bstep (se 1 (by rfl) ⟨519938, by rfl⟩ : syracuseStep 693251 = 1039877) B1039877
theorem B693281 : Blo 459783 693281 := bstep (se 2 (by rfl) ⟨259980, by rfl⟩ : syracuseStep 693281 = 519961) B519961
theorem B693299 : Blo 459783 693299 := bstep (se 1 (by rfl) ⟨519974, by rfl⟩ : syracuseStep 693299 = 1039949) B1039949
theorem B693329 : Blo 459783 693329 := bstep (se 2 (by rfl) ⟨259998, by rfl⟩ : syracuseStep 693329 = 519997) B519997
theorem B693347 : Blo 459783 693347 := bstep (se 1 (by rfl) ⟨520010, by rfl⟩ : syracuseStep 693347 = 1040021) B1040021
theorem B693377 : Blo 459783 693377 := bstep (se 2 (by rfl) ⟨260016, by rfl⟩ : syracuseStep 693377 = 520033) B520033
theorem B693395 : Blo 459783 693395 := bstep (se 1 (by rfl) ⟨520046, by rfl⟩ : syracuseStep 693395 = 1040093) B1040093
theorem B1971377 : Blo 459783 1971377 := bstep (se 2 (by rfl) ⟨739266, by rfl⟩ : syracuseStep 1971377 = 1478533) B1478533
theorem B693425 : Blo 459783 693425 := bstep (se 2 (by rfl) ⟨260034, by rfl⟩ : syracuseStep 693425 = 520069) B520069
theorem B988337 : Blo 459783 988337 := bstep (se 2 (by rfl) ⟨370626, by rfl⟩ : syracuseStep 988337 = 741253) B741253
theorem B693443 : Blo 459783 693443 := bstep (se 1 (by rfl) ⟨520082, by rfl⟩ : syracuseStep 693443 = 1040165) B1040165
theorem B693473 : Blo 459783 693473 := bstep (se 2 (by rfl) ⟨260052, by rfl⟩ : syracuseStep 693473 = 520105) B520105
theorem B693491 : Blo 459783 693491 := bstep (se 1 (by rfl) ⟨520118, by rfl⟩ : syracuseStep 693491 = 1040237) B1040237
theorem B2954501 : Blo 459783 2954501 := bstep (se 4 (by rfl) ⟨276984, by rfl⟩ : syracuseStep 2954501 = 553969) B553969
theorem B693521 : Blo 459783 693521 := bstep (se 2 (by rfl) ⟨260070, by rfl⟩ : syracuseStep 693521 = 520141) B520141
theorem B693539 : Blo 459783 693539 := bstep (se 1 (by rfl) ⟨520154, by rfl⟩ : syracuseStep 693539 = 1040309) B1040309
theorem B693569 : Blo 459783 693569 := bstep (se 2 (by rfl) ⟨260088, by rfl⟩ : syracuseStep 693569 = 520177) B520177
theorem B693587 : Blo 459783 693587 := bstep (se 1 (by rfl) ⟨520190, by rfl⟩ : syracuseStep 693587 = 1040381) B1040381
theorem B791905 : Blo 459783 791905 := bstep (se 2 (by rfl) ⟨296964, by rfl⟩ : syracuseStep 791905 = 593929) B593929
theorem B1480045 : Blo 459783 1480045 := bstep (se 3 (by rfl) ⟨277508, by rfl⟩ : syracuseStep 1480045 = 555017) B555017
theorem B693617 : Blo 459783 693617 := bstep (se 2 (by rfl) ⟨260106, by rfl⟩ : syracuseStep 693617 = 520213) B520213
theorem B693635 : Blo 459783 693635 := bstep (se 1 (by rfl) ⟨520226, by rfl⟩ : syracuseStep 693635 = 1040453) B1040453
theorem B8885645 : Blo 459783 8885645 := bstep (se 3 (by rfl) ⟨1666058, by rfl⟩ : syracuseStep 8885645 = 3332117) B3332117
theorem B693665 : Blo 459783 693665 := bstep (se 2 (by rfl) ⟨260124, by rfl⟩ : syracuseStep 693665 = 520249) B520249
theorem B693683 : Blo 459783 693683 := bstep (se 1 (by rfl) ⟨520262, by rfl⟩ : syracuseStep 693683 = 1040525) B1040525
theorem B792001 : Blo 459783 792001 := bstep (se 2 (by rfl) ⟨297000, by rfl⟩ : syracuseStep 792001 = 594001) B594001
theorem B693713 : Blo 459783 693713 := bstep (se 2 (by rfl) ⟨260142, by rfl⟩ : syracuseStep 693713 = 520285) B520285
theorem B693731 : Blo 459783 693731 := bstep (se 1 (by rfl) ⟨520298, by rfl⟩ : syracuseStep 693731 = 1040597) B1040597
theorem B693761 : Blo 459783 693761 := bstep (se 2 (by rfl) ⟨260160, by rfl⟩ : syracuseStep 693761 = 520321) B520321
theorem B693779 : Blo 459783 693779 := bstep (se 1 (by rfl) ⟨520334, by rfl⟩ : syracuseStep 693779 = 1040669) B1040669
theorem B693809 : Blo 459783 693809 := bstep (se 2 (by rfl) ⟨260178, by rfl⟩ : syracuseStep 693809 = 520357) B520357
theorem B693827 : Blo 459783 693827 := bstep (se 1 (by rfl) ⟨520370, by rfl⟩ : syracuseStep 693827 = 1040741) B1040741
theorem B693857 : Blo 459783 693857 := bstep (se 2 (by rfl) ⟨260196, by rfl⟩ : syracuseStep 693857 = 520393) B520393
theorem B693875 : Blo 459783 693875 := bstep (se 1 (by rfl) ⟨520406, by rfl⟩ : syracuseStep 693875 = 1040813) B1040813
theorem B1316483 : Blo 459783 1316483 := bstep (se 1 (by rfl) ⟨987362, by rfl⟩ : syracuseStep 1316483 = 1974725) B1974725
theorem B693905 : Blo 459783 693905 := bstep (se 2 (by rfl) ⟨260214, by rfl⟩ : syracuseStep 693905 = 520429) B520429
theorem B693923 : Blo 459783 693923 := bstep (se 1 (by rfl) ⟨520442, by rfl⟩ : syracuseStep 693923 = 1040885) B1040885
theorem B693953 : Blo 459783 693953 := bstep (se 2 (by rfl) ⟨260232, by rfl⟩ : syracuseStep 693953 = 520465) B520465
theorem B693971 : Blo 459783 693971 := bstep (se 1 (by rfl) ⟨520478, by rfl⟩ : syracuseStep 693971 = 1040957) B1040957
theorem B792275 : Blo 459783 792275 := bstep (se 1 (by rfl) ⟨594206, by rfl⟩ : syracuseStep 792275 = 1188413) B1188413
theorem B694001 : Blo 459783 694001 := bstep (se 2 (by rfl) ⟨260250, by rfl⟩ : syracuseStep 694001 = 520501) B520501
theorem B694019 : Blo 459783 694019 := bstep (se 1 (by rfl) ⟨520514, by rfl⟩ : syracuseStep 694019 = 1041029) B1041029
theorem B694049 : Blo 459783 694049 := bstep (se 2 (by rfl) ⟨260268, by rfl⟩ : syracuseStep 694049 = 520537) B520537
theorem B694067 : Blo 459783 694067 := bstep (se 1 (by rfl) ⟨520550, by rfl⟩ : syracuseStep 694067 = 1041101) B1041101
theorem B694097 : Blo 459783 694097 := bstep (se 2 (by rfl) ⟨260286, by rfl⟩ : syracuseStep 694097 = 520573) B520573
theorem B694115 : Blo 459783 694115 := bstep (se 1 (by rfl) ⟨520586, by rfl⟩ : syracuseStep 694115 = 1041173) B1041173
theorem B694145 : Blo 459783 694145 := bstep (se 2 (by rfl) ⟨260304, by rfl⟩ : syracuseStep 694145 = 520609) B520609
theorem B694163 : Blo 459783 694163 := bstep (se 1 (by rfl) ⟨520622, by rfl⟩ : syracuseStep 694163 = 1041245) B1041245
theorem B694193 : Blo 459783 694193 := bstep (se 2 (by rfl) ⟨260322, by rfl⟩ : syracuseStep 694193 = 520645) B520645
theorem B694211 : Blo 459783 694211 := bstep (se 1 (by rfl) ⟨520658, by rfl⟩ : syracuseStep 694211 = 1041317) B1041317
theorem B694241 : Blo 459783 694241 := bstep (se 2 (by rfl) ⟨260340, by rfl⟩ : syracuseStep 694241 = 520681) B520681
theorem B694259 : Blo 459783 694259 := bstep (se 1 (by rfl) ⟨520694, by rfl⟩ : syracuseStep 694259 = 1041389) B1041389
theorem B694289 : Blo 459783 694289 := bstep (se 2 (by rfl) ⟨260358, by rfl⟩ : syracuseStep 694289 = 520717) B520717
theorem B694307 : Blo 459783 694307 := bstep (se 1 (by rfl) ⟨520730, by rfl⟩ : syracuseStep 694307 = 1041461) B1041461
theorem B694337 : Blo 459783 694337 := bstep (se 2 (by rfl) ⟨260376, by rfl⟩ : syracuseStep 694337 = 520753) B520753
theorem B694355 : Blo 459783 694355 := bstep (se 1 (by rfl) ⟨520766, by rfl⟩ : syracuseStep 694355 = 1041533) B1041533
theorem B694385 : Blo 459783 694385 := bstep (se 2 (by rfl) ⟨260394, by rfl⟩ : syracuseStep 694385 = 520789) B520789
theorem B694403 : Blo 459783 694403 := bstep (se 1 (by rfl) ⟨520802, by rfl⟩ : syracuseStep 694403 = 1041605) B1041605
theorem B694433 : Blo 459783 694433 := bstep (se 2 (by rfl) ⟨260412, by rfl⟩ : syracuseStep 694433 = 520825) B520825
theorem B694451 : Blo 459783 694451 := bstep (se 1 (by rfl) ⟨520838, by rfl⟩ : syracuseStep 694451 = 1041677) B1041677
theorem B694481 : Blo 459783 694481 := bstep (se 2 (by rfl) ⟨260430, by rfl⟩ : syracuseStep 694481 = 520861) B520861
theorem B694499 : Blo 459783 694499 := bstep (se 1 (by rfl) ⟨520874, by rfl⟩ : syracuseStep 694499 = 1041749) B1041749
theorem B694529 : Blo 459783 694529 := bstep (se 2 (by rfl) ⟨260448, by rfl⟩ : syracuseStep 694529 = 520897) B520897
theorem B1579267 : Blo 459783 1579267 := bstep (se 1 (by rfl) ⟨1184450, by rfl⟩ : syracuseStep 1579267 = 2368901) B2368901
theorem B694547 : Blo 459783 694547 := bstep (se 1 (by rfl) ⟨520910, by rfl⟩ : syracuseStep 694547 = 1041821) B1041821
theorem B694577 : Blo 459783 694577 := bstep (se 2 (by rfl) ⟨260466, by rfl⟩ : syracuseStep 694577 = 520933) B520933
theorem B694595 : Blo 459783 694595 := bstep (se 1 (by rfl) ⟨520946, by rfl⟩ : syracuseStep 694595 = 1041893) B1041893
theorem B2627909 : Blo 459783 2627909 := bstep (se 4 (by rfl) ⟨246366, by rfl⟩ : syracuseStep 2627909 = 492733) B492733
theorem B694625 : Blo 459783 694625 := bstep (se 2 (by rfl) ⟨260484, by rfl⟩ : syracuseStep 694625 = 520969) B520969
theorem B694643 : Blo 459783 694643 := bstep (se 1 (by rfl) ⟨520982, by rfl⟩ : syracuseStep 694643 = 1041965) B1041965
theorem B694673 : Blo 459783 694673 := bstep (se 2 (by rfl) ⟨260502, by rfl⟩ : syracuseStep 694673 = 521005) B521005
theorem B694691 : Blo 459783 694691 := bstep (se 1 (by rfl) ⟨521018, by rfl⟩ : syracuseStep 694691 = 1042037) B1042037
theorem B1317293 : Blo 459783 1317293 := bstep (se 3 (by rfl) ⟨246992, by rfl⟩ : syracuseStep 1317293 = 493985) B493985
theorem B694721 : Blo 459783 694721 := bstep (se 2 (by rfl) ⟨260520, by rfl⟩ : syracuseStep 694721 = 521041) B521041
theorem B694739 : Blo 459783 694739 := bstep (se 1 (by rfl) ⟨521054, by rfl⟩ : syracuseStep 694739 = 1042109) B1042109
theorem B694769 : Blo 459783 694769 := bstep (se 2 (by rfl) ⟨260538, by rfl⟩ : syracuseStep 694769 = 521077) B521077
theorem B694787 : Blo 459783 694787 := bstep (se 1 (by rfl) ⟨521090, by rfl⟩ : syracuseStep 694787 = 1042181) B1042181
theorem B694817 : Blo 459783 694817 := bstep (se 2 (by rfl) ⟨260556, by rfl⟩ : syracuseStep 694817 = 521113) B521113
theorem B694835 : Blo 459783 694835 := bstep (se 1 (by rfl) ⟨521126, by rfl⟩ : syracuseStep 694835 = 1042253) B1042253
theorem B4725317 : Blo 459783 4725317 := bstep (se 4 (by rfl) ⟨442998, by rfl⟩ : syracuseStep 4725317 = 885997) B885997
theorem B694865 : Blo 459783 694865 := bstep (se 2 (by rfl) ⟨260574, by rfl⟩ : syracuseStep 694865 = 521149) B521149
theorem B694883 : Blo 459783 694883 := bstep (se 1 (by rfl) ⟨521162, by rfl⟩ : syracuseStep 694883 = 1042325) B1042325
theorem B1317485 : Blo 459783 1317485 := bstep (se 3 (by rfl) ⟨247028, by rfl⟩ : syracuseStep 1317485 = 494057) B494057
theorem B563827 : Blo 459783 563827 := bstep (se 1 (by rfl) ⟨422870, by rfl⟩ : syracuseStep 563827 = 845741) B845741
theorem B694913 : Blo 459783 694913 := bstep (se 2 (by rfl) ⟨260592, by rfl⟩ : syracuseStep 694913 = 521185) B521185
theorem B694931 : Blo 459783 694931 := bstep (se 1 (by rfl) ⟨521198, by rfl⟩ : syracuseStep 694931 = 1042397) B1042397
theorem B694961 : Blo 459783 694961 := bstep (se 2 (by rfl) ⟨260610, by rfl⟩ : syracuseStep 694961 = 521221) B521221
theorem B694979 : Blo 459783 694979 := bstep (se 1 (by rfl) ⟨521234, by rfl⟩ : syracuseStep 694979 = 1042469) B1042469
theorem B695009 : Blo 459783 695009 := bstep (se 2 (by rfl) ⟨260628, by rfl⟩ : syracuseStep 695009 = 521257) B521257
theorem B695027 : Blo 459783 695027 := bstep (se 1 (by rfl) ⟨521270, by rfl⟩ : syracuseStep 695027 = 1042541) B1042541
theorem B695057 : Blo 459783 695057 := bstep (se 2 (by rfl) ⟨260646, by rfl⟩ : syracuseStep 695057 = 521293) B521293
theorem B695075 : Blo 459783 695075 := bstep (se 1 (by rfl) ⟨521306, by rfl⟩ : syracuseStep 695075 = 1042613) B1042613
theorem B695105 : Blo 459783 695105 := bstep (se 2 (by rfl) ⟨260664, by rfl⟩ : syracuseStep 695105 = 521329) B521329
theorem B1973069 : Blo 459783 1973069 := bstep (se 3 (by rfl) ⟨369950, by rfl⟩ : syracuseStep 1973069 = 739901) B739901
theorem B695123 : Blo 459783 695123 := bstep (se 1 (by rfl) ⟨521342, by rfl⟩ : syracuseStep 695123 = 1042685) B1042685
theorem B695153 : Blo 459783 695153 := bstep (se 2 (by rfl) ⟨260682, by rfl⟩ : syracuseStep 695153 = 521365) B521365
theorem B695171 : Blo 459783 695171 := bstep (se 1 (by rfl) ⟨521378, by rfl⟩ : syracuseStep 695171 = 1042757) B1042757
theorem B695201 : Blo 459783 695201 := bstep (se 2 (by rfl) ⟨260700, by rfl⟩ : syracuseStep 695201 = 521401) B521401
theorem B695219 : Blo 459783 695219 := bstep (se 1 (by rfl) ⟨521414, by rfl⟩ : syracuseStep 695219 = 1042829) B1042829
theorem B1055683 : Blo 459783 1055683 := bstep (se 1 (by rfl) ⟨791762, by rfl⟩ : syracuseStep 1055683 = 1583525) B1583525
theorem B3152837 : Blo 459783 3152837 := bstep (se 4 (by rfl) ⟨295578, by rfl⟩ : syracuseStep 3152837 = 591157) B591157
theorem B695249 : Blo 459783 695249 := bstep (se 2 (by rfl) ⟨260718, by rfl⟩ : syracuseStep 695249 = 521437) B521437
theorem B695267 : Blo 459783 695267 := bstep (se 1 (by rfl) ⟨521450, by rfl⟩ : syracuseStep 695267 = 1042901) B1042901
theorem B1055729 : Blo 459783 1055729 := bstep (se 2 (by rfl) ⟨395898, by rfl⟩ : syracuseStep 1055729 = 791797) B791797
theorem B695297 : Blo 459783 695297 := bstep (se 2 (by rfl) ⟨260736, by rfl⟩ : syracuseStep 695297 = 521473) B521473
theorem B695315 : Blo 459783 695315 := bstep (se 1 (by rfl) ⟨521486, by rfl⟩ : syracuseStep 695315 = 1042973) B1042973
theorem B695345 : Blo 459783 695345 := bstep (se 2 (by rfl) ⟨260754, by rfl⟩ : syracuseStep 695345 = 521509) B521509
theorem B695363 : Blo 459783 695363 := bstep (se 1 (by rfl) ⟨521522, by rfl⟩ : syracuseStep 695363 = 1043045) B1043045
theorem B2530381 : Blo 459783 2530381 := bstep (se 3 (by rfl) ⟨474446, by rfl⟩ : syracuseStep 2530381 = 948893) B948893
theorem B695393 : Blo 459783 695393 := bstep (se 2 (by rfl) ⟨260772, by rfl⟩ : syracuseStep 695393 = 521545) B521545
theorem B695411 : Blo 459783 695411 := bstep (se 1 (by rfl) ⟨521558, by rfl⟩ : syracuseStep 695411 = 1043117) B1043117
theorem B695441 : Blo 459783 695441 := bstep (se 2 (by rfl) ⟨260790, by rfl⟩ : syracuseStep 695441 = 521581) B521581
theorem B695459 : Blo 459783 695459 := bstep (se 1 (by rfl) ⟨521594, by rfl⟩ : syracuseStep 695459 = 1043189) B1043189
theorem B695489 : Blo 459783 695489 := bstep (se 2 (by rfl) ⟨260808, by rfl⟩ : syracuseStep 695489 = 521617) B521617
theorem B695507 : Blo 459783 695507 := bstep (se 1 (by rfl) ⟨521630, by rfl⟩ : syracuseStep 695507 = 1043261) B1043261
theorem B564451 : Blo 459783 564451 := bstep (se 1 (by rfl) ⟨423338, by rfl⟩ : syracuseStep 564451 = 846677) B846677
theorem B695537 : Blo 459783 695537 := bstep (se 2 (by rfl) ⟨260826, by rfl⟩ : syracuseStep 695537 = 521653) B521653
theorem B1121539 : Blo 459783 1121539 := bstep (se 1 (by rfl) ⟨841154, by rfl⟩ : syracuseStep 1121539 = 1682309) B1682309
theorem B695555 : Blo 459783 695555 := bstep (se 1 (by rfl) ⟨521666, by rfl⟩ : syracuseStep 695555 = 1043333) B1043333
theorem B695585 : Blo 459783 695585 := bstep (se 2 (by rfl) ⟨260844, by rfl⟩ : syracuseStep 695585 = 521689) B521689
theorem B695603 : Blo 459783 695603 := bstep (se 1 (by rfl) ⟨521702, by rfl⟩ : syracuseStep 695603 = 1043405) B1043405
theorem B695633 : Blo 459783 695633 := bstep (se 2 (by rfl) ⟨260862, by rfl⟩ : syracuseStep 695633 = 521725) B521725
theorem B695651 : Blo 459783 695651 := bstep (se 1 (by rfl) ⟨521738, by rfl⟩ : syracuseStep 695651 = 1043477) B1043477
theorem B2498033 : Blo 459783 2498033 := bstep (se 2 (by rfl) ⟨936762, by rfl⟩ : syracuseStep 2498033 = 1873525) B1873525
theorem B2334257 : Blo 459783 2334257 := bstep (se 2 (by rfl) ⟨875346, by rfl⟩ : syracuseStep 2334257 = 1750693) B1750693
theorem B1318477 : Blo 459783 1318477 := bstep (se 3 (by rfl) ⟨247214, by rfl⟩ : syracuseStep 1318477 = 494429) B494429
theorem B1187569 : Blo 459783 1187569 := bstep (se 2 (by rfl) ⟨445338, by rfl⟩ : syracuseStep 1187569 = 890677) B890677
theorem B2957219 : Blo 459783 2957219 := bstep (se 1 (by rfl) ⟨2217914, by rfl⟩ : syracuseStep 2957219 = 4435829) B4435829
theorem B467299 : Blo 459783 467299 := bstep (se 1 (by rfl) ⟨350474, by rfl⟩ : syracuseStep 467299 = 700949) B700949
theorem B3154481 : Blo 459783 3154481 := bstep (se 2 (by rfl) ⟨1182930, by rfl⟩ : syracuseStep 3154481 = 2365861) B2365861
theorem B1483505 : Blo 459783 1483505 := bstep (se 2 (by rfl) ⟨556314, by rfl⟩ : syracuseStep 1483505 = 1112629) B1112629
theorem B1483697 : Blo 459783 1483697 := bstep (se 2 (by rfl) ⟨556386, by rfl⟩ : syracuseStep 1483697 = 1112773) B1112773
theorem B2335715 : Blo 459783 2335715 := bstep (se 1 (by rfl) ⟨1751786, by rfl⟩ : syracuseStep 2335715 = 3503573) B3503573
theorem B664723 : Blo 459783 664723 := bstep (se 1 (by rfl) ⟨498542, by rfl⟩ : syracuseStep 664723 = 997085) B997085
theorem B1320209 : Blo 459783 1320209 := bstep (se 2 (by rfl) ⟨495078, by rfl⟩ : syracuseStep 1320209 = 990157) B990157
theorem B6628661 : Blo 459783 6628661 := bstep (se 5 (by rfl) ⟨310718, by rfl⟩ : syracuseStep 6628661 = 621437) B621437
theorem B664915 : Blo 459783 664915 := bstep (se 1 (by rfl) ⟨498686, by rfl⟩ : syracuseStep 664915 = 997373) B997373
theorem B1320401 : Blo 459783 1320401 := bstep (se 2 (by rfl) ⟨495150, by rfl⟩ : syracuseStep 1320401 = 990301) B990301
theorem B2336525 : Blo 459783 2336525 := bstep (se 3 (by rfl) ⟨438098, by rfl⟩ : syracuseStep 2336525 = 876197) B876197
theorem B2959217 : Blo 459783 2959217 := bstep (se 2 (by rfl) ⟨1109706, by rfl⟩ : syracuseStep 2959217 = 2219413) B2219413
theorem B3942341 : Blo 459783 3942341 := bstep (se 4 (by rfl) ⟨369594, by rfl⟩ : syracuseStep 3942341 = 739189) B739189
theorem B2566129 : Blo 459783 2566129 := bstep (se 2 (by rfl) ⟨962298, by rfl⟩ : syracuseStep 2566129 = 1924597) B1924597
theorem B5253173 : Blo 459783 5253173 := bstep (se 5 (by rfl) ⟨246242, by rfl⟩ : syracuseStep 5253173 = 492485) B492485
theorem B1747277 : Blo 459783 1747277 := bstep (se 3 (by rfl) ⟨327614, by rfl⟩ : syracuseStep 1747277 = 655229) B655229
theorem B2959715 : Blo 459783 2959715 := bstep (se 1 (by rfl) ⟨2219786, by rfl⟩ : syracuseStep 2959715 = 4439573) B4439573
theorem B829873 : Blo 459783 829873 := bstep (se 2 (by rfl) ⟨311202, by rfl⟩ : syracuseStep 829873 = 622405) B622405
theorem B3943025 : Blo 459783 3943025 := bstep (se 2 (by rfl) ⟨1478634, by rfl⟩ : syracuseStep 3943025 = 2957269) B2957269
theorem B830083 : Blo 459783 830083 := bstep (se 1 (by rfl) ⟨622562, by rfl⟩ : syracuseStep 830083 = 1245125) B1245125
theorem B6007621 : Blo 459783 6007621 := bstep (se 4 (by rfl) ⟨563214, by rfl⟩ : syracuseStep 6007621 = 1126429) B1126429
theorem B6761357 : Blo 459783 6761357 := bstep (se 3 (by rfl) ⟨1267754, by rfl⟩ : syracuseStep 6761357 = 2535509) B2535509
theorem B633955 : Blo 459783 633955 := bstep (se 1 (by rfl) ⟨475466, by rfl⟩ : syracuseStep 633955 = 950933) B950933
theorem B1977443 : Blo 459783 1977443 := bstep (se 1 (by rfl) ⟨1483082, by rfl⟩ : syracuseStep 1977443 = 2966165) B2966165
theorem B1748081 : Blo 459783 1748081 := bstep (se 2 (by rfl) ⟨655530, by rfl⟩ : syracuseStep 1748081 = 1311061) B1311061
theorem B1584305 : Blo 459783 1584305 := bstep (se 2 (by rfl) ⟨594114, by rfl⟩ : syracuseStep 1584305 = 1188229) B1188229
theorem B3517667 : Blo 459783 3517667 := bstep (se 1 (by rfl) ⟨2638250, by rfl⟩ : syracuseStep 3517667 = 5276501) B5276501
theorem B1552013 : Blo 459783 1552013 := bstep (se 3 (by rfl) ⟨291002, by rfl⟩ : syracuseStep 1552013 = 582005) B582005
theorem B3321485 : Blo 459783 3321485 := bstep (se 3 (by rfl) ⟨622778, by rfl⟩ : syracuseStep 3321485 = 1245557) B1245557
theorem B1552067 : Blo 459783 1552067 := bstep (se 1 (by rfl) ⟨1164050, by rfl⟩ : syracuseStep 1552067 = 2328101) B2328101
theorem B1748749 : Blo 459783 1748749 := bstep (se 3 (by rfl) ⟨327890, by rfl⟩ : syracuseStep 1748749 = 655781) B655781
theorem B1552337 : Blo 459783 1552337 := bstep (se 2 (by rfl) ⟨582126, by rfl⟩ : syracuseStep 1552337 = 1164253) B1164253
theorem B2633741 : Blo 459783 2633741 := bstep (se 3 (by rfl) ⟨493826, by rfl⟩ : syracuseStep 2633741 = 987653) B987653
theorem B634963 : Blo 459783 634963 := bstep (se 1 (by rfl) ⟨476222, by rfl⟩ : syracuseStep 634963 = 952445) B952445
theorem B5910641 : Blo 459783 5910641 := bstep (se 2 (by rfl) ⟨2216490, by rfl⟩ : syracuseStep 5910641 = 4432981) B4432981
theorem B2961677 : Blo 459783 2961677 := bstep (se 3 (by rfl) ⟨555314, by rfl⟩ : syracuseStep 2961677 = 1110629) B1110629
theorem B831761 : Blo 459783 831761 := bstep (se 2 (by rfl) ⟨311910, by rfl⟩ : syracuseStep 831761 = 623821) B623821
theorem B1552877 : Blo 459783 1552877 := bstep (se 3 (by rfl) ⟨291164, by rfl⟩ : syracuseStep 1552877 = 582329) B582329
theorem B1552931 : Blo 459783 1552931 := bstep (se 1 (by rfl) ⟨1164698, by rfl⟩ : syracuseStep 1552931 = 2329397) B2329397
theorem B1749539 : Blo 459783 1749539 := bstep (se 1 (by rfl) ⟨1312154, by rfl⟩ : syracuseStep 1749539 = 2624309) B2624309
theorem B2667043 : Blo 459783 2667043 := bstep (se 1 (by rfl) ⟨2000282, by rfl⟩ : syracuseStep 2667043 = 4000565) B4000565
theorem B2339441 : Blo 459783 2339441 := bstep (se 2 (by rfl) ⟨877290, by rfl⟩ : syracuseStep 2339441 = 1754581) B1754581
theorem B2503331 : Blo 459783 2503331 := bstep (se 1 (by rfl) ⟨1877498, by rfl⟩ : syracuseStep 2503331 = 3754997) B3754997
theorem B1553201 : Blo 459783 1553201 := bstep (se 2 (by rfl) ⟨582450, by rfl⟩ : syracuseStep 1553201 = 1164901) B1164901
theorem B7877573 : Blo 459783 7877573 := bstep (se 4 (by rfl) ⟨738522, by rfl⟩ : syracuseStep 7877573 = 1477045) B1477045
theorem B1979441 : Blo 459783 1979441 := bstep (se 2 (by rfl) ⟨742290, by rfl⟩ : syracuseStep 1979441 = 1484581) B1484581
theorem B1750193 : Blo 459783 1750193 := bstep (se 2 (by rfl) ⟨656322, by rfl⟩ : syracuseStep 1750193 = 1312645) B1312645
theorem B832771 : Blo 459783 832771 := bstep (se 1 (by rfl) ⟨624578, by rfl⟩ : syracuseStep 832771 = 1249157) B1249157
theorem B1553741 : Blo 459783 1553741 := bstep (se 3 (by rfl) ⟨291326, by rfl⟩ : syracuseStep 1553741 = 582653) B582653
theorem B1553795 : Blo 459783 1553795 := bstep (se 1 (by rfl) ⟨1165346, by rfl⟩ : syracuseStep 1553795 = 2330693) B2330693
theorem B5682659 : Blo 459783 5682659 := bstep (se 1 (by rfl) ⟨4261994, by rfl⟩ : syracuseStep 5682659 = 8523989) B8523989
theorem B1554065 : Blo 459783 1554065 := bstep (se 2 (by rfl) ⟨582774, by rfl⟩ : syracuseStep 1554065 = 1165549) B1165549
theorem B4208453 : Blo 459783 4208453 := bstep (se 4 (by rfl) ⟨394542, by rfl⟩ : syracuseStep 4208453 = 789085) B789085
theorem B3323875 : Blo 459783 3323875 := bstep (se 1 (by rfl) ⟨2492906, by rfl⟩ : syracuseStep 3323875 = 4985813) B4985813
theorem B2340899 : Blo 459783 2340899 := bstep (se 1 (by rfl) ⟨1755674, by rfl⟩ : syracuseStep 2340899 = 3511349) B3511349
theorem B702577 : Blo 459783 702577 := bstep (se 2 (by rfl) ⟨263466, by rfl⟩ : syracuseStep 702577 = 526933) B526933
theorem B2373745 : Blo 459783 2373745 := bstep (se 2 (by rfl) ⟨890154, by rfl⟩ : syracuseStep 2373745 = 1780309) B1780309
theorem B1128593 : Blo 459783 1128593 := bstep (se 2 (by rfl) ⟨423222, by rfl⟩ : syracuseStep 1128593 = 846445) B846445
theorem B1554605 : Blo 459783 1554605 := bstep (se 3 (by rfl) ⟨291488, by rfl⟩ : syracuseStep 1554605 = 582977) B582977
theorem B2635973 : Blo 459783 2635973 := bstep (se 4 (by rfl) ⟨247122, by rfl⟩ : syracuseStep 2635973 = 494245) B494245
theorem B1554659 : Blo 459783 1554659 := bstep (se 1 (by rfl) ⟨1165994, by rfl⟩ : syracuseStep 1554659 = 2331989) B2331989
theorem B833809 : Blo 459783 833809 := bstep (se 2 (by rfl) ⟨312678, by rfl⟩ : syracuseStep 833809 = 625357) B625357
theorem B1554929 : Blo 459783 1554929 := bstep (se 2 (by rfl) ⟨583098, by rfl⟩ : syracuseStep 1554929 = 1166197) B1166197
theorem B5913101 : Blo 459783 5913101 := bstep (se 3 (by rfl) ⟨1108706, by rfl⟩ : syracuseStep 5913101 = 2217413) B2217413
theorem B1751651 : Blo 459783 1751651 := bstep (se 1 (by rfl) ⟨1313738, by rfl⟩ : syracuseStep 1751651 = 2627477) B2627477
theorem B1751665 : Blo 459783 1751665 := bstep (se 2 (by rfl) ⟨656874, by rfl⟩ : syracuseStep 1751665 = 1313749) B1313749
theorem B703283 : Blo 459783 703283 := bstep (se 1 (by rfl) ⟨527462, by rfl⟩ : syracuseStep 703283 = 1054925) B1054925
theorem B2341709 : Blo 459783 2341709 := bstep (se 3 (by rfl) ⟨439070, by rfl⟩ : syracuseStep 2341709 = 878141) B878141
theorem B2636657 : Blo 459783 2636657 := bstep (se 2 (by rfl) ⟨988746, by rfl⟩ : syracuseStep 2636657 = 1977493) B1977493
theorem B1555469 : Blo 459783 1555469 := bstep (se 3 (by rfl) ⟨291650, by rfl⟩ : syracuseStep 1555469 = 583301) B583301
theorem B1555523 : Blo 459783 1555523 := bstep (se 1 (by rfl) ⟨1166642, by rfl⟩ : syracuseStep 1555523 = 2333285) B2333285
theorem B933041 : Blo 459783 933041 := bstep (se 2 (by rfl) ⟨349890, by rfl⟩ : syracuseStep 933041 = 699781) B699781
theorem B1555793 : Blo 459783 1555793 := bstep (se 2 (by rfl) ⟨583422, by rfl⟩ : syracuseStep 1555793 = 1166845) B1166845
theorem B736723 : Blo 459783 736723 := bstep (se 1 (by rfl) ⟨552542, by rfl⟩ : syracuseStep 736723 = 1105085) B1105085
theorem B704209 : Blo 459783 704209 := bstep (se 2 (by rfl) ⟨264078, by rfl⟩ : syracuseStep 704209 = 528157) B528157
theorem B1392419 : Blo 459783 1392419 := bstep (se 1 (by rfl) ⟨1044314, by rfl⟩ : syracuseStep 1392419 = 2088629) B2088629
theorem B835409 : Blo 459783 835409 := bstep (se 2 (by rfl) ⟨313278, by rfl⟩ : syracuseStep 835409 = 626557) B626557
theorem B1556333 : Blo 459783 1556333 := bstep (se 3 (by rfl) ⟨291812, by rfl⟩ : syracuseStep 1556333 = 583625) B583625
theorem B2211725 : Blo 459783 2211725 := bstep (se 3 (by rfl) ⟨414698, by rfl⟩ : syracuseStep 2211725 = 829397) B829397
theorem B1556387 : Blo 459783 1556387 := bstep (se 1 (by rfl) ⟨1167290, by rfl⟩ : syracuseStep 1556387 = 2334581) B2334581
theorem B737267 : Blo 459783 737267 := bstep (se 1 (by rfl) ⟨552950, by rfl⟩ : syracuseStep 737267 = 1105901) B1105901
theorem B1753123 : Blo 459783 1753123 := bstep (se 1 (by rfl) ⟨1314842, by rfl⟩ : syracuseStep 1753123 = 2629685) B2629685
theorem B737441 : Blo 459783 737441 := bstep (se 2 (by rfl) ⟨276540, by rfl⟩ : syracuseStep 737441 = 553081) B553081
theorem B1556657 : Blo 459783 1556657 := bstep (se 2 (by rfl) ⟨583746, by rfl⟩ : syracuseStep 1556657 = 1167493) B1167493
theorem B2638115 : Blo 459783 2638115 := bstep (se 1 (by rfl) ⟨1978586, by rfl⟩ : syracuseStep 2638115 = 3957173) B3957173
theorem B999761 : Blo 459783 999761 := bstep (se 2 (by rfl) ⟨374910, by rfl⟩ : syracuseStep 999761 = 749821) B749821
theorem B1557197 : Blo 459783 1557197 := bstep (se 3 (by rfl) ⟨291974, by rfl⟩ : syracuseStep 1557197 = 583949) B583949
theorem B1557251 : Blo 459783 1557251 := bstep (se 1 (by rfl) ⟨1167938, by rfl⟩ : syracuseStep 1557251 = 2335877) B2335877
theorem B1327889 : Blo 459783 1327889 := bstep (se 2 (by rfl) ⟨497958, by rfl⟩ : syracuseStep 1327889 = 995917) B995917
theorem B1557521 : Blo 459783 1557521 := bstep (se 2 (by rfl) ⟨584070, by rfl⟩ : syracuseStep 1557521 = 1168141) B1168141
theorem B935011 : Blo 459783 935011 := bstep (se 1 (by rfl) ⟨701258, by rfl⟩ : syracuseStep 935011 = 1402517) B1402517
theorem B1164689 : Blo 459783 1164689 := bstep (se 2 (by rfl) ⟨436758, by rfl⟩ : syracuseStep 1164689 = 873517) B873517
theorem B1164739 : Blo 459783 1164739 := bstep (se 1 (by rfl) ⟨873554, by rfl⟩ : syracuseStep 1164739 = 1747109) B1747109
theorem B673283 : Blo 459783 673283 := bstep (se 1 (by rfl) ⟨504962, by rfl⟩ : syracuseStep 673283 = 1009925) B1009925
theorem B1558061 : Blo 459783 1558061 := bstep (se 3 (by rfl) ⟨292136, by rfl⟩ : syracuseStep 1558061 = 584273) B584273
theorem B1164881 : Blo 459783 1164881 := bstep (se 2 (by rfl) ⟨436830, by rfl⟩ : syracuseStep 1164881 = 873661) B873661
theorem B1558115 : Blo 459783 1558115 := bstep (se 1 (by rfl) ⟨1168586, by rfl⟩ : syracuseStep 1558115 = 2337173) B2337173
theorem B2344625 : Blo 459783 2344625 := bstep (se 2 (by rfl) ⟨879234, by rfl⟩ : syracuseStep 2344625 = 1758469) B1758469
theorem B1558385 : Blo 459783 1558385 := bstep (se 2 (by rfl) ⟨584394, by rfl⟩ : syracuseStep 1558385 = 1168789) B1168789
theorem B1001521 : Blo 459783 1001521 := bstep (se 2 (by rfl) ⟨375570, by rfl⟩ : syracuseStep 1001521 = 751141) B751141
theorem B3491909 : Blo 459783 3491909 := bstep (se 4 (by rfl) ⟨327366, by rfl⟩ : syracuseStep 3491909 = 654733) B654733
theorem B739459 : Blo 459783 739459 := bstep (se 1 (by rfl) ⟨554594, by rfl⟩ : syracuseStep 739459 = 1109189) B1109189
theorem B739523 : Blo 459783 739523 := bstep (se 1 (by rfl) ⟨554642, by rfl⟩ : syracuseStep 739523 = 1109285) B1109285
theorem B1755341 : Blo 459783 1755341 := bstep (se 3 (by rfl) ⟨329126, by rfl⟩ : syracuseStep 1755341 = 658253) B658253
theorem B1034513 : Blo 459783 1034513 := bstep (se 2 (by rfl) ⟨387942, by rfl⟩ : syracuseStep 1034513 = 775885) B775885
theorem B1034531 : Blo 459783 1034531 := bstep (se 1 (by rfl) ⟨775898, by rfl⟩ : syracuseStep 1034531 = 1551797) B1551797
theorem B1558925 : Blo 459783 1558925 := bstep (se 3 (by rfl) ⟨292298, by rfl⟩ : syracuseStep 1558925 = 584597) B584597
theorem B1558979 : Blo 459783 1558979 := bstep (se 1 (by rfl) ⟨1169234, by rfl⟩ : syracuseStep 1558979 = 2338469) B2338469
theorem B3951089 : Blo 459783 3951089 := bstep (se 2 (by rfl) ⟨1481658, by rfl⟩ : syracuseStep 3951089 = 2963317) B2963317
theorem B2411021 : Blo 459783 2411021 := bstep (se 3 (by rfl) ⟨452066, by rfl⟩ : syracuseStep 2411021 = 904133) B904133
theorem B1034801 : Blo 459783 1034801 := bstep (se 2 (by rfl) ⟨388050, by rfl⟩ : syracuseStep 1034801 = 776101) B776101
theorem B1165873 : Blo 459783 1165873 := bstep (se 2 (by rfl) ⟨437202, by rfl⟩ : syracuseStep 1165873 = 874405) B874405
theorem B1034819 : Blo 459783 1034819 := bstep (se 1 (by rfl) ⟨776114, by rfl⟩ : syracuseStep 1034819 = 1552229) B1552229
theorem B3361421 : Blo 459783 3361421 := bstep (se 3 (by rfl) ⟨630266, by rfl⟩ : syracuseStep 3361421 = 1260533) B1260533
theorem B1559249 : Blo 459783 1559249 := bstep (se 2 (by rfl) ⟨584718, by rfl⟩ : syracuseStep 1559249 = 1169437) B1169437
theorem B1166147 : Blo 459783 1166147 := bstep (se 1 (by rfl) ⟨874610, by rfl⟩ : syracuseStep 1166147 = 1749221) B1749221
theorem B1035089 : Blo 459783 1035089 := bstep (se 2 (by rfl) ⟨388158, by rfl⟩ : syracuseStep 1035089 = 776317) B776317
theorem B1035107 : Blo 459783 1035107 := bstep (se 1 (by rfl) ⟨776330, by rfl⟩ : syracuseStep 1035107 = 1552661) B1552661
theorem B1166339 : Blo 459783 1166339 := bstep (se 1 (by rfl) ⟨874754, by rfl⟩ : syracuseStep 1166339 = 1749509) B1749509
theorem B3329093 : Blo 459783 3329093 := bstep (se 4 (by rfl) ⟨312102, by rfl⟩ : syracuseStep 3329093 = 624205) B624205
theorem B2346083 : Blo 459783 2346083 := bstep (se 1 (by rfl) ⟨1759562, by rfl⟩ : syracuseStep 2346083 = 3519125) B3519125
theorem B1035377 : Blo 459783 1035377 := bstep (se 2 (by rfl) ⟨388266, by rfl⟩ : syracuseStep 1035377 = 776533) B776533
theorem B1035395 : Blo 459783 1035395 := bstep (se 1 (by rfl) ⟨776546, by rfl⟩ : syracuseStep 1035395 = 1553093) B1553093
theorem B740497 : Blo 459783 740497 := bstep (se 2 (by rfl) ⟨277686, by rfl⟩ : syracuseStep 740497 = 555373) B555373
theorem B1559789 : Blo 459783 1559789 := bstep (se 3 (by rfl) ⟨292460, by rfl⟩ : syracuseStep 1559789 = 584921) B584921
theorem B1559843 : Blo 459783 1559843 := bstep (se 1 (by rfl) ⟨1169882, by rfl⟩ : syracuseStep 1559843 = 2339765) B2339765
theorem B5000561 : Blo 459783 5000561 := bstep (se 2 (by rfl) ⟨1875210, by rfl⟩ : syracuseStep 5000561 = 3750421) B3750421
theorem B1035665 : Blo 459783 1035665 := bstep (se 2 (by rfl) ⟨388374, by rfl⟩ : syracuseStep 1035665 = 776749) B776749
theorem B740753 : Blo 459783 740753 := bstep (se 2 (by rfl) ⟨277782, by rfl⟩ : syracuseStep 740753 = 555565) B555565
theorem B1035683 : Blo 459783 1035683 := bstep (se 1 (by rfl) ⟨776762, by rfl⟩ : syracuseStep 1035683 = 1553525) B1553525
theorem B2641349 : Blo 459783 2641349 := bstep (se 4 (by rfl) ⟨247626, by rfl⟩ : syracuseStep 2641349 = 495253) B495253
theorem B1560113 : Blo 459783 1560113 := bstep (se 2 (by rfl) ⟨585042, by rfl⟩ : syracuseStep 1560113 = 1170085) B1170085
theorem B740945 : Blo 459783 740945 := bstep (se 2 (by rfl) ⟨277854, by rfl⟩ : syracuseStep 740945 = 555709) B555709
theorem B1035953 : Blo 459783 1035953 := bstep (se 2 (by rfl) ⟨388482, by rfl⟩ : syracuseStep 1035953 = 776965) B776965
theorem B1035971 : Blo 459783 1035971 := bstep (se 1 (by rfl) ⟨776978, by rfl⟩ : syracuseStep 1035971 = 1553957) B1553957
theorem B2346893 : Blo 459783 2346893 := bstep (se 3 (by rfl) ⟨440042, by rfl⟩ : syracuseStep 2346893 = 880085) B880085
theorem B1167281 : Blo 459783 1167281 := bstep (se 2 (by rfl) ⟨437730, by rfl⟩ : syracuseStep 1167281 = 875461) B875461
theorem B1036241 : Blo 459783 1036241 := bstep (se 2 (by rfl) ⟨388590, by rfl⟩ : syracuseStep 1036241 = 777181) B777181
theorem B1036259 : Blo 459783 1036259 := bstep (se 1 (by rfl) ⟨777194, by rfl⟩ : syracuseStep 1036259 = 1554389) B1554389
theorem B1167331 : Blo 459783 1167331 := bstep (se 1 (by rfl) ⟨875498, by rfl⟩ : syracuseStep 1167331 = 1750997) B1750997
theorem B1560653 : Blo 459783 1560653 := bstep (se 3 (by rfl) ⟨292622, by rfl⟩ : syracuseStep 1560653 = 585245) B585245
theorem B1167473 : Blo 459783 1167473 := bstep (se 2 (by rfl) ⟨437802, by rfl⟩ : syracuseStep 1167473 = 875605) B875605
theorem B1560707 : Blo 459783 1560707 := bstep (se 1 (by rfl) ⟨1170530, by rfl⟩ : syracuseStep 1560707 = 2341061) B2341061
theorem B1069283 : Blo 459783 1069283 := bstep (se 1 (by rfl) ⟨801962, by rfl⟩ : syracuseStep 1069283 = 1603925) B1603925
theorem B1036529 : Blo 459783 1036529 := bstep (se 2 (by rfl) ⟨388698, by rfl⟩ : syracuseStep 1036529 = 777397) B777397
theorem B1036547 : Blo 459783 1036547 := bstep (se 1 (by rfl) ⟨777410, by rfl⟩ : syracuseStep 1036547 = 1554821) B1554821
theorem B1331491 : Blo 459783 1331491 := bstep (se 1 (by rfl) ⟨998618, by rfl⟩ : syracuseStep 1331491 = 1997237) B1997237
theorem B1560977 : Blo 459783 1560977 := bstep (se 2 (by rfl) ⟨585366, by rfl⟩ : syracuseStep 1560977 = 1170733) B1170733
theorem B2970083 : Blo 459783 2970083 := bstep (se 1 (by rfl) ⟨2227562, by rfl⟩ : syracuseStep 2970083 = 4455125) B4455125
theorem B1036817 : Blo 459783 1036817 := bstep (se 2 (by rfl) ⟨388806, by rfl⟩ : syracuseStep 1036817 = 777613) B777613
theorem B1036835 : Blo 459783 1036835 := bstep (se 1 (by rfl) ⟨777626, by rfl⟩ : syracuseStep 1036835 = 1555253) B1555253
theorem B873251 : Blo 459783 873251 := bstep (se 1 (by rfl) ⟨654938, by rfl⟩ : syracuseStep 873251 = 1309877) B1309877
theorem B1037105 : Blo 459783 1037105 := bstep (se 2 (by rfl) ⟨388914, by rfl⟩ : syracuseStep 1037105 = 777829) B777829
theorem B1037123 : Blo 459783 1037123 := bstep (se 1 (by rfl) ⟨777842, by rfl⟩ : syracuseStep 1037123 = 1555685) B1555685
theorem B1332035 : Blo 459783 1332035 := bstep (se 1 (by rfl) ⟨999026, by rfl⟩ : syracuseStep 1332035 = 1998053) B1998053
theorem B742259 : Blo 459783 742259 := bstep (se 1 (by rfl) ⟨556694, by rfl⟩ : syracuseStep 742259 = 1113389) B1113389
theorem B3953549 : Blo 459783 3953549 := bstep (se 3 (by rfl) ⟨741290, by rfl⟩ : syracuseStep 3953549 = 1482581) B1482581
theorem B4641677 : Blo 459783 4641677 := bstep (se 3 (by rfl) ⟨870314, by rfl⟩ : syracuseStep 4641677 = 1740629) B1740629
theorem B1561517 : Blo 459783 1561517 := bstep (se 3 (by rfl) ⟨292784, by rfl⟩ : syracuseStep 1561517 = 585569) B585569
theorem B1561571 : Blo 459783 1561571 := bstep (se 1 (by rfl) ⟨1171178, by rfl⟩ : syracuseStep 1561571 = 2342357) B2342357
theorem B513011 : Blo 459783 513011 := bstep (se 1 (by rfl) ⟨384758, by rfl⟩ : syracuseStep 513011 = 769517) B769517
theorem B1758257 : Blo 459783 1758257 := bstep (se 2 (by rfl) ⟨659346, by rfl⟩ : syracuseStep 1758257 = 1318693) B1318693
theorem B1037393 : Blo 459783 1037393 := bstep (se 2 (by rfl) ⟨389022, by rfl⟩ : syracuseStep 1037393 = 778045) B778045
theorem B1168465 : Blo 459783 1168465 := bstep (se 2 (by rfl) ⟨438174, by rfl⟩ : syracuseStep 1168465 = 876349) B876349
theorem B742483 : Blo 459783 742483 := bstep (se 1 (by rfl) ⟨556862, by rfl⟩ : syracuseStep 742483 = 1113725) B1113725
theorem B1037411 : Blo 459783 1037411 := bstep (se 1 (by rfl) ⟨778058, by rfl⟩ : syracuseStep 1037411 = 1556117) B1556117
theorem B742547 : Blo 459783 742547 := bstep (se 1 (by rfl) ⟨556910, by rfl⟩ : syracuseStep 742547 = 1113821) B1113821
theorem B939235 : Blo 459783 939235 := bstep (se 1 (by rfl) ⟨704426, by rfl⟩ : syracuseStep 939235 = 1408853) B1408853
theorem B4216049 : Blo 459783 4216049 := bstep (se 2 (by rfl) ⟨1581018, by rfl⟩ : syracuseStep 4216049 = 3162037) B3162037
theorem B1561841 : Blo 459783 1561841 := bstep (se 2 (by rfl) ⟨585690, by rfl⟩ : syracuseStep 1561841 = 1171381) B1171381
theorem B742675 : Blo 459783 742675 := bstep (se 1 (by rfl) ⟨557006, by rfl⟩ : syracuseStep 742675 = 1114013) B1114013
theorem B1168739 : Blo 459783 1168739 := bstep (se 1 (by rfl) ⟨876554, by rfl⟩ : syracuseStep 1168739 = 1753109) B1753109
theorem B1037681 : Blo 459783 1037681 := bstep (se 2 (by rfl) ⟨389130, by rfl⟩ : syracuseStep 1037681 = 778261) B778261
theorem B1037699 : Blo 459783 1037699 := bstep (se 1 (by rfl) ⟨778274, by rfl⟩ : syracuseStep 1037699 = 1556549) B1556549
theorem B5264837 : Blo 459783 5264837 := bstep (se 4 (by rfl) ⟨493578, by rfl⟩ : syracuseStep 5264837 = 987157) B987157
theorem B1168931 : Blo 459783 1168931 := bstep (se 1 (by rfl) ⟨876698, by rfl⟩ : syracuseStep 1168931 = 1753397) B1753397
theorem B1037969 : Blo 459783 1037969 := bstep (se 2 (by rfl) ⟨389238, by rfl⟩ : syracuseStep 1037969 = 778477) B778477
theorem B874147 : Blo 459783 874147 := bstep (se 1 (by rfl) ⟨655610, by rfl⟩ : syracuseStep 874147 = 1311221) B1311221
theorem B1037987 : Blo 459783 1037987 := bstep (se 1 (by rfl) ⟨778490, by rfl⟩ : syracuseStep 1037987 = 1556981) B1556981
theorem B2971313 : Blo 459783 2971313 := bstep (se 2 (by rfl) ⟨1114242, by rfl⟩ : syracuseStep 2971313 = 2228485) B2228485
theorem B775939 : Blo 459783 775939 := bstep (se 1 (by rfl) ⟨581954, by rfl⟩ : syracuseStep 775939 = 1163909) B1163909
theorem B1562381 : Blo 459783 1562381 := bstep (se 3 (by rfl) ⟨292946, by rfl⟩ : syracuseStep 1562381 = 585893) B585893
theorem B874307 : Blo 459783 874307 := bstep (se 1 (by rfl) ⟨655730, by rfl⟩ : syracuseStep 874307 = 1311461) B1311461
theorem B1562435 : Blo 459783 1562435 := bstep (se 1 (by rfl) ⟨1171826, by rfl⟩ : syracuseStep 1562435 = 2343653) B2343653
theorem B776081 : Blo 459783 776081 := bstep (se 2 (by rfl) ⟨291030, by rfl⟩ : syracuseStep 776081 = 582061) B582061
theorem B1038257 : Blo 459783 1038257 := bstep (se 2 (by rfl) ⟨389346, by rfl⟩ : syracuseStep 1038257 = 778693) B778693
theorem B1038275 : Blo 459783 1038275 := bstep (se 1 (by rfl) ⟨778706, by rfl⟩ : syracuseStep 1038275 = 1557413) B1557413
theorem B776209 : Blo 459783 776209 := bstep (se 2 (by rfl) ⟨291078, by rfl⟩ : syracuseStep 776209 = 582157) B582157
theorem B776243 : Blo 459783 776243 := bstep (se 1 (by rfl) ⟨582182, by rfl⟩ : syracuseStep 776243 = 1164365) B1164365
theorem B1562705 : Blo 459783 1562705 := bstep (se 2 (by rfl) ⟨586014, by rfl⟩ : syracuseStep 1562705 = 1172029) B1172029
theorem B2250929 : Blo 459783 2250929 := bstep (se 2 (by rfl) ⟨844098, by rfl⟩ : syracuseStep 2250929 = 1688197) B1688197
theorem B776371 : Blo 459783 776371 := bstep (se 1 (by rfl) ⟨582278, by rfl⟩ : syracuseStep 776371 = 1164557) B1164557
theorem B1038545 : Blo 459783 1038545 := bstep (se 2 (by rfl) ⟨389454, by rfl⟩ : syracuseStep 1038545 = 778909) B778909
theorem B1038563 : Blo 459783 1038563 := bstep (se 1 (by rfl) ⟨778922, by rfl⟩ : syracuseStep 1038563 = 1557845) B1557845
theorem B11229461 : Blo 459783 11229461 := bstep (se 6 (by rfl) ⟨263190, by rfl⟩ : syracuseStep 11229461 = 526381) B526381
theorem B776513 : Blo 459783 776513 := bstep (se 2 (by rfl) ⟨291192, by rfl⟩ : syracuseStep 776513 = 582385) B582385
theorem B3332465 : Blo 459783 3332465 := bstep (se 2 (by rfl) ⟨1249674, by rfl⟩ : syracuseStep 3332465 = 2499349) B2499349
theorem B776641 : Blo 459783 776641 := bstep (se 2 (by rfl) ⟨291240, by rfl⟩ : syracuseStep 776641 = 582481) B582481
theorem B1169873 : Blo 459783 1169873 := bstep (se 2 (by rfl) ⟨438702, by rfl⟩ : syracuseStep 1169873 = 877405) B877405
theorem B776675 : Blo 459783 776675 := bstep (se 1 (by rfl) ⟨582506, by rfl⟩ : syracuseStep 776675 = 1165013) B1165013
theorem B1759715 : Blo 459783 1759715 := bstep (se 1 (by rfl) ⟨1319786, by rfl⟩ : syracuseStep 1759715 = 2639573) B2639573
theorem B1038833 : Blo 459783 1038833 := bstep (se 2 (by rfl) ⟨389562, by rfl⟩ : syracuseStep 1038833 = 779125) B779125
theorem B1038851 : Blo 459783 1038851 := bstep (se 1 (by rfl) ⟨779138, by rfl⟩ : syracuseStep 1038851 = 1558277) B1558277
theorem B1169923 : Blo 459783 1169923 := bstep (se 1 (by rfl) ⟨877442, by rfl⟩ : syracuseStep 1169923 = 1754885) B1754885
theorem B45439541 : Blo 459783 45439541 := bstep (se 5 (by rfl) ⟨2129978, by rfl⟩ : syracuseStep 45439541 = 4259957) B4259957
theorem B776803 : Blo 459783 776803 := bstep (se 1 (by rfl) ⟨582602, by rfl⟩ : syracuseStep 776803 = 1165205) B1165205
theorem B1563245 : Blo 459783 1563245 := bstep (se 3 (by rfl) ⟨293108, by rfl⟩ : syracuseStep 1563245 = 586217) B586217
theorem B1170065 : Blo 459783 1170065 := bstep (se 2 (by rfl) ⟨438774, by rfl⟩ : syracuseStep 1170065 = 877549) B877549
theorem B1563299 : Blo 459783 1563299 := bstep (se 1 (by rfl) ⟨1172474, by rfl⟩ : syracuseStep 1563299 = 2344949) B2344949
theorem B776945 : Blo 459783 776945 := bstep (se 2 (by rfl) ⟨291354, by rfl⟩ : syracuseStep 776945 = 582709) B582709
theorem B1039121 : Blo 459783 1039121 := bstep (se 2 (by rfl) ⟨389670, by rfl⟩ : syracuseStep 1039121 = 779341) B779341
theorem B1039139 : Blo 459783 1039139 := bstep (se 1 (by rfl) ⟨779354, by rfl⟩ : syracuseStep 1039139 = 1558709) B1558709
theorem B777073 : Blo 459783 777073 := bstep (se 2 (by rfl) ⟨291402, by rfl⟩ : syracuseStep 777073 = 582805) B582805
theorem B875377 : Blo 459783 875377 := bstep (se 2 (by rfl) ⟨328266, by rfl⟩ : syracuseStep 875377 = 656533) B656533
theorem B18963341 : Blo 459783 18963341 := bstep (se 3 (by rfl) ⟨3555626, by rfl⟩ : syracuseStep 18963341 = 7111253) B7111253
theorem B777107 : Blo 459783 777107 := bstep (se 1 (by rfl) ⟨582830, by rfl⟩ : syracuseStep 777107 = 1165661) B1165661
theorem B1596323 : Blo 459783 1596323 := bstep (se 1 (by rfl) ⟨1197242, by rfl⟩ : syracuseStep 1596323 = 2394485) B2394485
theorem B1563569 : Blo 459783 1563569 := bstep (se 2 (by rfl) ⟨586338, by rfl⟩ : syracuseStep 1563569 = 1172677) B1172677
theorem B777235 : Blo 459783 777235 := bstep (se 1 (by rfl) ⟨582926, by rfl⟩ : syracuseStep 777235 = 1165853) B1165853
theorem B1104931 : Blo 459783 1104931 := bstep (se 1 (by rfl) ⟨828698, by rfl⟩ : syracuseStep 1104931 = 1657397) B1657397
theorem B1039409 : Blo 459783 1039409 := bstep (se 2 (by rfl) ⟨389778, by rfl⟩ : syracuseStep 1039409 = 779557) B779557
theorem B1039427 : Blo 459783 1039427 := bstep (se 1 (by rfl) ⟨779570, by rfl⟩ : syracuseStep 1039427 = 1559141) B1559141
theorem B777377 : Blo 459783 777377 := bstep (se 2 (by rfl) ⟨291516, by rfl⟩ : syracuseStep 777377 = 583033) B583033
theorem B777505 : Blo 459783 777505 := bstep (se 2 (by rfl) ⟨291564, by rfl⟩ : syracuseStep 777505 = 583129) B583129
theorem B777539 : Blo 459783 777539 := bstep (se 1 (by rfl) ⟨583154, by rfl⟩ : syracuseStep 777539 = 1166309) B1166309
theorem B1039697 : Blo 459783 1039697 := bstep (se 2 (by rfl) ⟨389886, by rfl⟩ : syracuseStep 1039697 = 779773) B779773
theorem B1039715 : Blo 459783 1039715 := bstep (se 1 (by rfl) ⟨779786, by rfl⟩ : syracuseStep 1039715 = 1559573) B1559573
theorem B777667 : Blo 459783 777667 := bstep (se 1 (by rfl) ⟨583250, by rfl⟩ : syracuseStep 777667 = 1166501) B1166501
theorem B1564109 : Blo 459783 1564109 := bstep (se 3 (by rfl) ⟨293270, by rfl⟩ : syracuseStep 1564109 = 586541) B586541
theorem B1760717 : Blo 459783 1760717 := bstep (se 3 (by rfl) ⟨330134, by rfl⟩ : syracuseStep 1760717 = 660269) B660269
theorem B1564163 : Blo 459783 1564163 := bstep (se 1 (by rfl) ⟨1173122, by rfl⟩ : syracuseStep 1564163 = 2346245) B2346245
theorem B777809 : Blo 459783 777809 := bstep (se 2 (by rfl) ⟨291678, by rfl⟩ : syracuseStep 777809 = 583357) B583357
theorem B1039985 : Blo 459783 1039985 := bstep (se 2 (by rfl) ⟨389994, by rfl⟩ : syracuseStep 1039985 = 779989) B779989
theorem B1171057 : Blo 459783 1171057 := bstep (se 2 (by rfl) ⟨439146, by rfl⟩ : syracuseStep 1171057 = 878293) B878293
theorem B1040003 : Blo 459783 1040003 := bstep (se 1 (by rfl) ⟨780002, by rfl⟩ : syracuseStep 1040003 = 1560005) B1560005
theorem B1400483 : Blo 459783 1400483 := bstep (se 1 (by rfl) ⟨1050362, by rfl⟩ : syracuseStep 1400483 = 2100725) B2100725
theorem B777937 : Blo 459783 777937 := bstep (se 2 (by rfl) ⟨291726, by rfl⟩ : syracuseStep 777937 = 583453) B583453
theorem B777971 : Blo 459783 777971 := bstep (se 1 (by rfl) ⟨583478, by rfl⟩ : syracuseStep 777971 = 1166957) B1166957
theorem B3497741 : Blo 459783 3497741 := bstep (se 3 (by rfl) ⟨655826, by rfl⟩ : syracuseStep 3497741 = 1311653) B1311653
theorem B1564433 : Blo 459783 1564433 := bstep (se 2 (by rfl) ⟨586662, by rfl⟩ : syracuseStep 1564433 = 1173325) B1173325
theorem B778099 : Blo 459783 778099 := bstep (se 1 (by rfl) ⟨583574, by rfl⟩ : syracuseStep 778099 = 1167149) B1167149
theorem B1171331 : Blo 459783 1171331 := bstep (se 1 (by rfl) ⟨878498, by rfl⟩ : syracuseStep 1171331 = 1756997) B1756997
theorem B876433 : Blo 459783 876433 := bstep (se 2 (by rfl) ⟨328662, by rfl⟩ : syracuseStep 876433 = 657325) B657325
theorem B1040273 : Blo 459783 1040273 := bstep (se 2 (by rfl) ⟨390102, by rfl⟩ : syracuseStep 1040273 = 780205) B780205
theorem B1040291 : Blo 459783 1040291 := bstep (se 1 (by rfl) ⟨780218, by rfl⟩ : syracuseStep 1040291 = 1560437) B1560437
theorem B3170245 : Blo 459783 3170245 := bstep (se 4 (by rfl) ⟨297210, by rfl⟩ : syracuseStep 3170245 = 594421) B594421
theorem B778241 : Blo 459783 778241 := bstep (se 2 (by rfl) ⟨291840, by rfl⟩ : syracuseStep 778241 = 583681) B583681
theorem B3170353 : Blo 459783 3170353 := bstep (se 2 (by rfl) ⟨1188882, by rfl⟩ : syracuseStep 3170353 = 2377765) B2377765
theorem B1171523 : Blo 459783 1171523 := bstep (se 1 (by rfl) ⟨878642, by rfl⟩ : syracuseStep 1171523 = 1757285) B1757285
theorem B778369 : Blo 459783 778369 := bstep (se 2 (by rfl) ⟨291888, by rfl⟩ : syracuseStep 778369 = 583777) B583777
theorem B778403 : Blo 459783 778403 := bstep (se 1 (by rfl) ⟨583802, by rfl⟩ : syracuseStep 778403 = 1167605) B1167605
theorem B1040561 : Blo 459783 1040561 := bstep (se 2 (by rfl) ⟨390210, by rfl⟩ : syracuseStep 1040561 = 780421) B780421
theorem B1040579 : Blo 459783 1040579 := bstep (se 1 (by rfl) ⟨780434, by rfl⟩ : syracuseStep 1040579 = 1560869) B1560869
theorem B778531 : Blo 459783 778531 := bstep (se 1 (by rfl) ⟨583898, by rfl⟩ : syracuseStep 778531 = 1167797) B1167797
theorem B876835 : Blo 459783 876835 := bstep (se 1 (by rfl) ⟨657626, by rfl⟩ : syracuseStep 876835 = 1315253) B1315253
theorem B1564973 : Blo 459783 1564973 := bstep (se 3 (by rfl) ⟨293432, by rfl⟩ : syracuseStep 1564973 = 586865) B586865
theorem B4251973 : Blo 459783 4251973 := bstep (se 4 (by rfl) ⟨398622, by rfl⟩ : syracuseStep 4251973 = 797245) B797245
theorem B876881 : Blo 459783 876881 := bstep (se 2 (by rfl) ⟨328830, by rfl⟩ : syracuseStep 876881 = 657661) B657661
theorem B1565027 : Blo 459783 1565027 := bstep (se 1 (by rfl) ⟨1173770, by rfl⟩ : syracuseStep 1565027 = 2347541) B2347541
theorem B778673 : Blo 459783 778673 := bstep (se 2 (by rfl) ⟨292002, by rfl⟩ : syracuseStep 778673 = 584005) B584005
theorem B1040849 : Blo 459783 1040849 := bstep (se 2 (by rfl) ⟨390318, by rfl⟩ : syracuseStep 1040849 = 780637) B780637
theorem B1040867 : Blo 459783 1040867 := bstep (se 1 (by rfl) ⟨780650, by rfl⟩ : syracuseStep 1040867 = 1561301) B1561301
theorem B778801 : Blo 459783 778801 := bstep (se 2 (by rfl) ⟨292050, by rfl⟩ : syracuseStep 778801 = 584101) B584101
theorem B778835 : Blo 459783 778835 := bstep (se 1 (by rfl) ⟨584126, by rfl⟩ : syracuseStep 778835 = 1168253) B1168253
theorem B1401457 : Blo 459783 1401457 := bstep (se 2 (by rfl) ⟨525546, by rfl⟩ : syracuseStep 1401457 = 1051093) B1051093
theorem B877169 : Blo 459783 877169 := bstep (se 2 (by rfl) ⟨328938, by rfl⟩ : syracuseStep 877169 = 657877) B657877
theorem B11231885 : Blo 459783 11231885 := bstep (se 3 (by rfl) ⟨2105978, by rfl⟩ : syracuseStep 11231885 = 4211957) B4211957
theorem B778963 : Blo 459783 778963 := bstep (se 1 (by rfl) ⟨584222, by rfl⟩ : syracuseStep 778963 = 1168445) B1168445
theorem B1041137 : Blo 459783 1041137 := bstep (se 2 (by rfl) ⟨390426, by rfl⟩ : syracuseStep 1041137 = 780853) B780853
theorem B1041155 : Blo 459783 1041155 := bstep (se 1 (by rfl) ⟨780866, by rfl⟩ : syracuseStep 1041155 = 1561733) B1561733
theorem B1336109 : Blo 459783 1336109 := bstep (se 3 (by rfl) ⟨250520, by rfl⟩ : syracuseStep 1336109 = 501041) B501041
theorem B779105 : Blo 459783 779105 := bstep (se 2 (by rfl) ⟨292164, by rfl⟩ : syracuseStep 779105 = 584329) B584329
theorem B582547 : Blo 459783 582547 := bstep (se 1 (by rfl) ⟨436910, by rfl⟩ : syracuseStep 582547 = 873821) B873821
theorem B779233 : Blo 459783 779233 := bstep (se 2 (by rfl) ⟨292212, by rfl⟩ : syracuseStep 779233 = 584425) B584425
theorem B1172465 : Blo 459783 1172465 := bstep (se 2 (by rfl) ⟨439674, by rfl⟩ : syracuseStep 1172465 = 879349) B879349
theorem B582643 : Blo 459783 582643 := bstep (se 1 (by rfl) ⟨436982, by rfl⟩ : syracuseStep 582643 = 873965) B873965
theorem B779267 : Blo 459783 779267 := bstep (se 1 (by rfl) ⟨584450, by rfl⟩ : syracuseStep 779267 = 1168901) B1168901
theorem B1041425 : Blo 459783 1041425 := bstep (se 2 (by rfl) ⟨390534, by rfl⟩ : syracuseStep 1041425 = 781069) B781069
theorem B1041443 : Blo 459783 1041443 := bstep (se 1 (by rfl) ⟨781082, by rfl⟩ : syracuseStep 1041443 = 1562165) B1562165
theorem B1172515 : Blo 459783 1172515 := bstep (se 1 (by rfl) ⟨879386, by rfl⟩ : syracuseStep 1172515 = 1758773) B1758773
theorem B779395 : Blo 459783 779395 := bstep (se 1 (by rfl) ⟨584546, by rfl⟩ : syracuseStep 779395 = 1169093) B1169093
theorem B1172657 : Blo 459783 1172657 := bstep (se 2 (by rfl) ⟨439746, by rfl⟩ : syracuseStep 1172657 = 879493) B879493
theorem B517315 : Blo 459783 517315 := bstep (se 1 (by rfl) ⟨387986, by rfl⟩ : syracuseStep 517315 = 775973) B775973
theorem B779537 : Blo 459783 779537 := bstep (se 2 (by rfl) ⟨292326, by rfl⟩ : syracuseStep 779537 = 584653) B584653
theorem B1041713 : Blo 459783 1041713 := bstep (se 2 (by rfl) ⟨390642, by rfl⟩ : syracuseStep 1041713 = 781285) B781285
theorem B877891 : Blo 459783 877891 := bstep (se 1 (by rfl) ⟨658418, by rfl⟩ : syracuseStep 877891 = 1316837) B1316837
theorem B1041731 : Blo 459783 1041731 := bstep (se 1 (by rfl) ⟨781298, by rfl⟩ : syracuseStep 1041731 = 1562597) B1562597
theorem B517459 : Blo 459783 517459 := bstep (se 1 (by rfl) ⟨388094, by rfl⟩ : syracuseStep 517459 = 776189) B776189
theorem B779665 : Blo 459783 779665 := bstep (se 2 (by rfl) ⟨292374, by rfl⟩ : syracuseStep 779665 = 584749) B584749
theorem B779699 : Blo 459783 779699 := bstep (se 1 (by rfl) ⟨584774, by rfl⟩ : syracuseStep 779699 = 1169549) B1169549
theorem B517603 : Blo 459783 517603 := bstep (se 1 (by rfl) ⟨388202, by rfl⟩ : syracuseStep 517603 = 776405) B776405
theorem B583139 : Blo 459783 583139 := bstep (se 1 (by rfl) ⟨437354, by rfl⟩ : syracuseStep 583139 = 874709) B874709
theorem B779827 : Blo 459783 779827 := bstep (se 1 (by rfl) ⟨584870, by rfl⟩ : syracuseStep 779827 = 1169741) B1169741
theorem B1042001 : Blo 459783 1042001 := bstep (se 2 (by rfl) ⟨390750, by rfl⟩ : syracuseStep 1042001 = 781501) B781501
theorem B1042019 : Blo 459783 1042019 := bstep (se 1 (by rfl) ⟨781514, by rfl⟩ : syracuseStep 1042019 = 1563029) B1563029
theorem B517747 : Blo 459783 517747 := bstep (se 1 (by rfl) ⟨388310, by rfl⟩ : syracuseStep 517747 = 776621) B776621
theorem B779969 : Blo 459783 779969 := bstep (se 2 (by rfl) ⟨292488, by rfl⟩ : syracuseStep 779969 = 584977) B584977
theorem B517891 : Blo 459783 517891 := bstep (se 1 (by rfl) ⟨388418, by rfl⟩ : syracuseStep 517891 = 776837) B776837
theorem B878339 : Blo 459783 878339 := bstep (se 1 (by rfl) ⟨658754, by rfl⟩ : syracuseStep 878339 = 1317509) B1317509
theorem B780097 : Blo 459783 780097 := bstep (se 2 (by rfl) ⟨292536, by rfl⟩ : syracuseStep 780097 = 585073) B585073
theorem B780131 : Blo 459783 780131 := bstep (se 1 (by rfl) ⟨585098, by rfl⟩ : syracuseStep 780131 = 1170197) B1170197
theorem B1042289 : Blo 459783 1042289 := bstep (se 2 (by rfl) ⟨390858, by rfl⟩ : syracuseStep 1042289 = 781717) B781717
theorem B1042307 : Blo 459783 1042307 := bstep (se 1 (by rfl) ⟨781730, by rfl⟩ : syracuseStep 1042307 = 1563461) B1563461
theorem B518035 : Blo 459783 518035 := bstep (se 1 (by rfl) ⟨388526, by rfl⟩ : syracuseStep 518035 = 777053) B777053
theorem B780259 : Blo 459783 780259 := bstep (se 1 (by rfl) ⟨585194, by rfl⟩ : syracuseStep 780259 = 1170389) B1170389
theorem B518179 : Blo 459783 518179 := bstep (se 1 (by rfl) ⟨388634, by rfl⟩ : syracuseStep 518179 = 777269) B777269
theorem B878627 : Blo 459783 878627 := bstep (se 1 (by rfl) ⟨658970, by rfl⟩ : syracuseStep 878627 = 1317941) B1317941
theorem B1894499 : Blo 459783 1894499 := bstep (se 1 (by rfl) ⟨1420874, by rfl⟩ : syracuseStep 1894499 = 2841749) B2841749
theorem B1665137 : Blo 459783 1665137 := bstep (se 2 (by rfl) ⟨624426, by rfl⟩ : syracuseStep 1665137 = 1248853) B1248853
theorem B780401 : Blo 459783 780401 := bstep (se 2 (by rfl) ⟨292650, by rfl⟩ : syracuseStep 780401 = 585301) B585301
theorem B1042577 : Blo 459783 1042577 := bstep (se 2 (by rfl) ⟨390966, by rfl⟩ : syracuseStep 1042577 = 781933) B781933
theorem B1173649 : Blo 459783 1173649 := bstep (se 2 (by rfl) ⟨440118, by rfl⟩ : syracuseStep 1173649 = 880237) B880237
theorem B583843 : Blo 459783 583843 := bstep (se 1 (by rfl) ⟨437882, by rfl⟩ : syracuseStep 583843 = 875765) B875765
theorem B1042595 : Blo 459783 1042595 := bstep (se 1 (by rfl) ⟨781946, by rfl⟩ : syracuseStep 1042595 = 1563893) B1563893
theorem B518323 : Blo 459783 518323 := bstep (se 1 (by rfl) ⟨388742, by rfl⟩ : syracuseStep 518323 = 777485) B777485
theorem B780529 : Blo 459783 780529 := bstep (se 2 (by rfl) ⟨292698, by rfl⟩ : syracuseStep 780529 = 585397) B585397
theorem B583939 : Blo 459783 583939 := bstep (se 1 (by rfl) ⟨437954, by rfl⟩ : syracuseStep 583939 = 875909) B875909
theorem B780563 : Blo 459783 780563 := bstep (se 1 (by rfl) ⟨585422, by rfl⟩ : syracuseStep 780563 = 1170845) B1170845
theorem B518467 : Blo 459783 518467 := bstep (se 1 (by rfl) ⟨388850, by rfl⟩ : syracuseStep 518467 = 777701) B777701
theorem B780691 : Blo 459783 780691 := bstep (se 1 (by rfl) ⟨585518, by rfl⟩ : syracuseStep 780691 = 1171037) B1171037
theorem B747937 : Blo 459783 747937 := bstep (se 2 (by rfl) ⟨280476, by rfl⟩ : syracuseStep 747937 = 560953) B560953
theorem B1173923 : Blo 459783 1173923 := bstep (se 1 (by rfl) ⟨880442, by rfl⟩ : syracuseStep 1173923 = 1760885) B1760885
theorem B1042865 : Blo 459783 1042865 := bstep (se 2 (by rfl) ⟨391074, by rfl⟩ : syracuseStep 1042865 = 782149) B782149
theorem B1042883 : Blo 459783 1042883 := bstep (se 1 (by rfl) ⟨782162, by rfl⟩ : syracuseStep 1042883 = 1564325) B1564325
theorem B518611 : Blo 459783 518611 := bstep (se 1 (by rfl) ⟨388958, by rfl⟩ : syracuseStep 518611 = 777917) B777917
theorem B4450787 : Blo 459783 4450787 := bstep (se 1 (by rfl) ⟨3338090, by rfl⟩ : syracuseStep 4450787 = 6676181) B6676181
theorem B780833 : Blo 459783 780833 := bstep (se 2 (by rfl) ⟨292812, by rfl⟩ : syracuseStep 780833 = 585625) B585625
theorem B518755 : Blo 459783 518755 := bstep (se 1 (by rfl) ⟨389066, by rfl⟩ : syracuseStep 518755 = 778133) B778133
theorem B3500657 : Blo 459783 3500657 := bstep (se 2 (by rfl) ⟨1312746, by rfl⟩ : syracuseStep 3500657 = 2625493) B2625493
theorem B780961 : Blo 459783 780961 := bstep (se 2 (by rfl) ⟨292860, by rfl⟩ : syracuseStep 780961 = 585721) B585721
theorem B780995 : Blo 459783 780995 := bstep (se 1 (by rfl) ⟨585746, by rfl⟩ : syracuseStep 780995 = 1171493) B1171493
theorem B1043153 : Blo 459783 1043153 := bstep (se 2 (by rfl) ⟨391182, by rfl⟩ : syracuseStep 1043153 = 782365) B782365
theorem B1043171 : Blo 459783 1043171 := bstep (se 1 (by rfl) ⟨782378, by rfl⟩ : syracuseStep 1043171 = 1564757) B1564757
theorem B518899 : Blo 459783 518899 := bstep (se 1 (by rfl) ⟨389174, by rfl⟩ : syracuseStep 518899 = 778349) B778349
theorem B584435 : Blo 459783 584435 := bstep (se 1 (by rfl) ⟨438326, by rfl⟩ : syracuseStep 584435 = 876653) B876653
theorem B781123 : Blo 459783 781123 := bstep (se 1 (by rfl) ⟨585842, by rfl⟩ : syracuseStep 781123 = 1171685) B1171685
theorem B3566405 : Blo 459783 3566405 := bstep (se 4 (by rfl) ⟨334350, by rfl⟩ : syracuseStep 3566405 = 668701) B668701
theorem B519043 : Blo 459783 519043 := bstep (se 1 (by rfl) ⟨389282, by rfl⟩ : syracuseStep 519043 = 778565) B778565
theorem B781265 : Blo 459783 781265 := bstep (se 2 (by rfl) ⟨292974, by rfl⟩ : syracuseStep 781265 = 585949) B585949
theorem B879569 : Blo 459783 879569 := bstep (se 2 (by rfl) ⟨329838, by rfl⟩ : syracuseStep 879569 = 659677) B659677
theorem B1502189 : Blo 459783 1502189 := bstep (se 3 (by rfl) ⟨281660, by rfl⟩ : syracuseStep 1502189 = 563321) B563321
theorem B1043441 : Blo 459783 1043441 := bstep (se 2 (by rfl) ⟨391290, by rfl⟩ : syracuseStep 1043441 = 782581) B782581
theorem B1043459 : Blo 459783 1043459 := bstep (se 1 (by rfl) ⟨782594, by rfl⟩ : syracuseStep 1043459 = 1565189) B1565189
theorem B519187 : Blo 459783 519187 := bstep (se 1 (by rfl) ⟨389390, by rfl⟩ : syracuseStep 519187 = 778781) B778781
theorem B781393 : Blo 459783 781393 := bstep (se 2 (by rfl) ⟨293022, by rfl⟩ : syracuseStep 781393 = 586045) B586045
theorem B781427 : Blo 459783 781427 := bstep (se 1 (by rfl) ⟨586070, by rfl⟩ : syracuseStep 781427 = 1172141) B1172141
theorem B5270669 : Blo 459783 5270669 := bstep (se 3 (by rfl) ⟨988250, by rfl⟩ : syracuseStep 5270669 = 1976501) B1976501
theorem B519331 : Blo 459783 519331 := bstep (se 1 (by rfl) ⟨389498, by rfl⟩ : syracuseStep 519331 = 778997) B778997
theorem B1666289 : Blo 459783 1666289 := bstep (se 2 (by rfl) ⟨624858, by rfl⟩ : syracuseStep 1666289 = 1249717) B1249717
theorem B781555 : Blo 459783 781555 := bstep (se 1 (by rfl) ⟨586166, by rfl⟩ : syracuseStep 781555 = 1172333) B1172333
theorem B2223395 : Blo 459783 2223395 := bstep (se 1 (by rfl) ⟨1667546, by rfl⟩ : syracuseStep 2223395 = 3335093) B3335093
theorem B519475 : Blo 459783 519475 := bstep (se 1 (by rfl) ⟨389606, by rfl⟩ : syracuseStep 519475 = 779213) B779213
theorem B781697 : Blo 459783 781697 := bstep (se 2 (by rfl) ⟨293136, by rfl⟩ : syracuseStep 781697 = 586273) B586273
theorem B585139 : Blo 459783 585139 := bstep (se 1 (by rfl) ⟨438854, by rfl⟩ : syracuseStep 585139 = 877709) B877709
theorem B519619 : Blo 459783 519619 := bstep (se 1 (by rfl) ⟨389714, by rfl⟩ : syracuseStep 519619 = 779429) B779429
theorem B781825 : Blo 459783 781825 := bstep (se 2 (by rfl) ⟨293184, by rfl⟩ : syracuseStep 781825 = 586369) B586369
theorem B585235 : Blo 459783 585235 := bstep (se 1 (by rfl) ⟨438926, by rfl⟩ : syracuseStep 585235 = 877853) B877853
theorem B781859 : Blo 459783 781859 := bstep (se 1 (by rfl) ⟨586394, by rfl⟩ : syracuseStep 781859 = 1172789) B1172789
theorem B519763 : Blo 459783 519763 := bstep (se 1 (by rfl) ⟨389822, by rfl⟩ : syracuseStep 519763 = 779645) B779645
theorem B3665549 : Blo 459783 3665549 := bstep (se 3 (by rfl) ⟨687290, by rfl⟩ : syracuseStep 3665549 = 1374581) B1374581
theorem B781987 : Blo 459783 781987 := bstep (se 1 (by rfl) ⟨586490, by rfl⟩ : syracuseStep 781987 = 1172981) B1172981
theorem B5893829 : Blo 459783 5893829 := bstep (se 4 (by rfl) ⟨552546, by rfl⟩ : syracuseStep 5893829 = 1105093) B1105093
theorem B519907 : Blo 459783 519907 := bstep (se 1 (by rfl) ⟨389930, by rfl⟩ : syracuseStep 519907 = 779861) B779861
theorem B552739 : Blo 459783 552739 := bstep (se 1 (by rfl) ⟨414554, by rfl⟩ : syracuseStep 552739 = 829109) B829109
theorem B782129 : Blo 459783 782129 := bstep (se 2 (by rfl) ⟨293298, by rfl⟩ : syracuseStep 782129 = 586597) B586597
theorem B880465 : Blo 459783 880465 := bstep (se 2 (by rfl) ⟨330174, by rfl⟩ : syracuseStep 880465 = 660349) B660349
theorem B552787 : Blo 459783 552787 := bstep (se 1 (by rfl) ⟨414590, by rfl⟩ : syracuseStep 552787 = 829181) B829181
theorem B520051 : Blo 459783 520051 := bstep (se 1 (by rfl) ⟨390038, by rfl⟩ : syracuseStep 520051 = 780077) B780077
theorem B782257 : Blo 459783 782257 := bstep (se 2 (by rfl) ⟨293346, by rfl⟩ : syracuseStep 782257 = 586693) B586693
theorem B782291 : Blo 459783 782291 := bstep (se 1 (by rfl) ⟨586718, by rfl⟩ : syracuseStep 782291 = 1173437) B1173437
theorem B520195 : Blo 459783 520195 := bstep (se 1 (by rfl) ⟨390146, by rfl⟩ : syracuseStep 520195 = 780293) B780293
theorem B585731 : Blo 459783 585731 := bstep (se 1 (by rfl) ⟨439298, by rfl⟩ : syracuseStep 585731 = 878597) B878597
theorem B782419 : Blo 459783 782419 := bstep (se 1 (by rfl) ⟨586814, by rfl⟩ : syracuseStep 782419 = 1173629) B1173629
theorem B520339 : Blo 459783 520339 := bstep (se 1 (by rfl) ⟨390254, by rfl⟩ : syracuseStep 520339 = 780509) B780509
theorem B782561 : Blo 459783 782561 := bstep (se 2 (by rfl) ⟨293460, by rfl⟩ : syracuseStep 782561 = 586921) B586921
theorem B3207395 : Blo 459783 3207395 := bstep (se 1 (by rfl) ⟨2405546, by rfl⟩ : syracuseStep 3207395 = 4811093) B4811093
theorem B520483 : Blo 459783 520483 := bstep (se 1 (by rfl) ⟨390362, by rfl⟩ : syracuseStep 520483 = 780725) B780725
theorem B520627 : Blo 459783 520627 := bstep (se 1 (by rfl) ⟨390470, by rfl⟩ : syracuseStep 520627 = 780941) B780941
theorem B520771 : Blo 459783 520771 := bstep (se 1 (by rfl) ⟨390578, by rfl⟩ : syracuseStep 520771 = 781157) B781157
theorem B586435 : Blo 459783 586435 := bstep (se 1 (by rfl) ⟨439826, by rfl⟩ : syracuseStep 586435 = 879653) B879653
theorem B520915 : Blo 459783 520915 := bstep (se 1 (by rfl) ⟨390686, by rfl⟩ : syracuseStep 520915 = 781373) B781373
theorem B586531 : Blo 459783 586531 := bstep (se 1 (by rfl) ⟨439898, by rfl⟩ : syracuseStep 586531 = 879797) B879797
theorem B5206837 : Blo 459783 5206837 := bstep (se 5 (by rfl) ⟨244070, by rfl⟩ : syracuseStep 5206837 = 488141) B488141
theorem B521059 : Blo 459783 521059 := bstep (se 1 (by rfl) ⟨390794, by rfl⟩ : syracuseStep 521059 = 781589) B781589
theorem B3928945 : Blo 459783 3928945 := bstep (se 2 (by rfl) ⟨1473354, by rfl⟩ : syracuseStep 3928945 = 2946709) B2946709
theorem B521203 : Blo 459783 521203 := bstep (se 1 (by rfl) ⟨390902, by rfl⟩ : syracuseStep 521203 = 781805) B781805
theorem B521347 : Blo 459783 521347 := bstep (se 1 (by rfl) ⟨391010, by rfl⟩ : syracuseStep 521347 = 782021) B782021
theorem B521491 : Blo 459783 521491 := bstep (se 1 (by rfl) ⟨391118, by rfl⟩ : syracuseStep 521491 = 782237) B782237
theorem B521635 : Blo 459783 521635 := bstep (se 1 (by rfl) ⟨391226, by rfl⟩ : syracuseStep 521635 = 782453) B782453
theorem B1800035 : Blo 459783 1800035 := bstep (se 1 (by rfl) ⟨1350026, by rfl⟩ : syracuseStep 1800035 = 2700053) B2700053
theorem B5273585 : Blo 459783 5273585 := bstep (se 2 (by rfl) ⟨1977594, by rfl⟩ : syracuseStep 5273585 = 3955189) B3955189
theorem B20183093 : Blo 459783 20183093 := bstep (se 5 (by rfl) ⟨946082, by rfl⟩ : syracuseStep 20183093 = 1892165) B1892165
theorem B2619661 : Blo 459783 2619661 := bstep (se 3 (by rfl) ⟨491186, by rfl⟩ : syracuseStep 2619661 = 982373) B982373
theorem B2521613 : Blo 459783 2521613 := bstep (se 3 (by rfl) ⟨472802, by rfl⟩ : syracuseStep 2521613 = 945605) B945605
theorem B2849293 : Blo 459783 2849293 := bstep (se 3 (by rfl) ⟨534242, by rfl⟩ : syracuseStep 2849293 = 1068485) B1068485
theorem B1309421 : Blo 459783 1309421 := bstep (se 3 (by rfl) ⟨245516, by rfl⟩ : syracuseStep 1309421 = 491033) B491033
theorem B2227085 : Blo 459783 2227085 := bstep (se 3 (by rfl) ⟨417578, by rfl⟩ : syracuseStep 2227085 = 835157) B835157
theorem B1309603 : Blo 459783 1309603 := bstep (se 1 (by rfl) ⟨982202, by rfl⟩ : syracuseStep 1309603 = 1964405) B1964405
theorem B1965005 : Blo 459783 1965005 := bstep (se 3 (by rfl) ⟨368438, by rfl⟩ : syracuseStep 1965005 = 736877) B736877
theorem B1309763 : Blo 459783 1309763 := bstep (se 1 (by rfl) ⟨982322, by rfl⟩ : syracuseStep 1309763 = 1964645) B1964645
theorem B621713 : Blo 459783 621713 := bstep (se 2 (by rfl) ⟨233142, by rfl⟩ : syracuseStep 621713 = 466285) B466285
theorem B5012707 : Blo 459783 5012707 := bstep (se 1 (by rfl) ⟨3759530, by rfl⟩ : syracuseStep 5012707 = 7519061) B7519061
theorem B1473997 : Blo 459783 1473997 := bstep (se 3 (by rfl) ⟨276374, by rfl⟩ : syracuseStep 1473997 = 552749) B552749
theorem B491059 : Blo 459783 491059 := bstep (se 1 (by rfl) ⟨368294, by rfl⟩ : syracuseStep 491059 = 736589) B736589
theorem B654961 : Blo 459783 654961 := bstep (se 2 (by rfl) ⟨245610, by rfl⟩ : syracuseStep 654961 = 491221) B491221
theorem B655075 : Blo 459783 655075 := bstep (se 1 (by rfl) ⟨491306, by rfl⟩ : syracuseStep 655075 = 982613) B982613
theorem B622307 : Blo 459783 622307 := bstep (se 1 (by rfl) ⟨466730, by rfl⟩ : syracuseStep 622307 = 933461) B933461
theorem B3604337 : Blo 459783 3604337 := bstep (se 2 (by rfl) ⟨1351626, by rfl⟩ : syracuseStep 3604337 = 2703253) B2703253
theorem B4227137 : Blo 459783 4227137 := bstep (se 2 (by rfl) ⟨1585176, by rfl⟩ : syracuseStep 4227137 = 3170353) B3170353
theorem B491627 : Blo 459783 491627 := bstep (se 1 (by rfl) ⟨368720, by rfl⟩ : syracuseStep 491627 = 737441) B737441
theorem B7864451 : Blo 459783 7864451 := bstep (se 1 (by rfl) ⟨5898338, by rfl⟩ : syracuseStep 7864451 = 11796677) B11796677
theorem B1179955 : Blo 459783 1179955 := bstep (se 1 (by rfl) ⟨884966, by rfl⟩ : syracuseStep 1179955 = 1769933) B1769933
theorem B5669297 : Blo 459783 5669297 := bstep (se 2 (by rfl) ⟨2125986, by rfl⟩ : syracuseStep 5669297 = 4251973) B4251973
theorem B623065 : Blo 459783 623065 := bstep (se 2 (by rfl) ⟨233649, by rfl⟩ : syracuseStep 623065 = 467299) B467299
theorem B885259 : Blo 459783 885259 := bstep (se 1 (by rfl) ⟨663944, by rfl⟩ : syracuseStep 885259 = 1327889) B1327889
theorem B655895 : Blo 459783 655895 := bstep (se 1 (by rfl) ⟨491921, by rfl⟩ : syracuseStep 655895 = 983843) B983843
theorem B8553053 : Blo 459783 8553053 := bstep (se 3 (by rfl) ⟨1603697, by rfl⟩ : syracuseStep 8553053 = 3207395) B3207395
theorem B2851421 : Blo 459783 2851421 := bstep (se 3 (by rfl) ⟨534641, by rfl⟩ : syracuseStep 2851421 = 1069283) B1069283
theorem B1868609 : Blo 459783 1868609 := bstep (se 2 (by rfl) ⟨700728, by rfl⟩ : syracuseStep 1868609 = 1401457) B1401457
theorem B656203 : Blo 459783 656203 := bstep (se 1 (by rfl) ⟨492152, by rfl⟩ : syracuseStep 656203 = 984305) B984305
theorem B1049561 : Blo 459783 1049561 := bstep (se 2 (by rfl) ⟨393585, by rfl⟩ : syracuseStep 1049561 = 787171) B787171
theorem B459787 : Blo 459783 459787 := bstep (se 1 (by rfl) ⟨344840, by rfl⟩ : syracuseStep 459787 = 689681) B689681
theorem B459799 : Blo 459783 459799 := bstep (se 1 (by rfl) ⟨344849, by rfl⟩ : syracuseStep 459799 = 689699) B689699
theorem B459819 : Blo 459783 459819 := bstep (se 1 (by rfl) ⟨344864, by rfl⟩ : syracuseStep 459819 = 689729) B689729
theorem B459831 : Blo 459783 459831 := bstep (se 1 (by rfl) ⟨344873, by rfl⟩ : syracuseStep 459831 = 689747) B689747
theorem B459851 : Blo 459783 459851 := bstep (se 1 (by rfl) ⟨344888, by rfl⟩ : syracuseStep 459851 = 689777) B689777
theorem B590923 : Blo 459783 590923 := bstep (se 1 (by rfl) ⟨443192, by rfl⟩ : syracuseStep 590923 = 886385) B886385
theorem B459863 : Blo 459783 459863 := bstep (se 1 (by rfl) ⟨344897, by rfl⟩ : syracuseStep 459863 = 689795) B689795
theorem B459883 : Blo 459783 459883 := bstep (se 1 (by rfl) ⟨344912, by rfl⟩ : syracuseStep 459883 = 689825) B689825
theorem B459895 : Blo 459783 459895 := bstep (se 1 (by rfl) ⟨344921, by rfl⟩ : syracuseStep 459895 = 689843) B689843
theorem B459915 : Blo 459783 459915 := bstep (se 1 (by rfl) ⟨344936, by rfl⟩ : syracuseStep 459915 = 689873) B689873
theorem B459927 : Blo 459783 459927 := bstep (se 1 (by rfl) ⟨344945, by rfl⟩ : syracuseStep 459927 = 689891) B689891
theorem B459947 : Blo 459783 459947 := bstep (se 1 (by rfl) ⟨344960, by rfl⟩ : syracuseStep 459947 = 689921) B689921
theorem B459959 : Blo 459783 459959 := bstep (se 1 (by rfl) ⟨344969, by rfl⟩ : syracuseStep 459959 = 689939) B689939
theorem B459979 : Blo 459783 459979 := bstep (se 1 (by rfl) ⟨344984, by rfl⟩ : syracuseStep 459979 = 689969) B689969
theorem B459991 : Blo 459783 459991 := bstep (se 1 (by rfl) ⟨344993, by rfl⟩ : syracuseStep 459991 = 689987) B689987
theorem B460011 : Blo 459783 460011 := bstep (se 1 (by rfl) ⟨345008, by rfl⟩ : syracuseStep 460011 = 690017) B690017
theorem B460023 : Blo 459783 460023 := bstep (se 1 (by rfl) ⟨345017, by rfl⟩ : syracuseStep 460023 = 690035) B690035
theorem B3507461 : Blo 459783 3507461 := bstep (se 4 (by rfl) ⟨328824, by rfl⟩ : syracuseStep 3507461 = 657649) B657649
theorem B460043 : Blo 459783 460043 := bstep (se 1 (by rfl) ⟨345032, by rfl⟩ : syracuseStep 460043 = 690065) B690065
theorem B460055 : Blo 459783 460055 := bstep (se 1 (by rfl) ⟨345041, by rfl⟩ : syracuseStep 460055 = 690083) B690083
theorem B460075 : Blo 459783 460075 := bstep (se 1 (by rfl) ⟨345056, by rfl⟩ : syracuseStep 460075 = 690113) B690113
theorem B460087 : Blo 459783 460087 := bstep (se 1 (by rfl) ⟨345065, by rfl⟩ : syracuseStep 460087 = 690131) B690131
theorem B460107 : Blo 459783 460107 := bstep (se 1 (by rfl) ⟨345080, by rfl⟩ : syracuseStep 460107 = 690161) B690161
theorem B460119 : Blo 459783 460119 := bstep (se 1 (by rfl) ⟨345089, by rfl⟩ : syracuseStep 460119 = 690179) B690179
theorem B460139 : Blo 459783 460139 := bstep (se 1 (by rfl) ⟨345104, by rfl⟩ : syracuseStep 460139 = 690209) B690209
theorem B460151 : Blo 459783 460151 := bstep (se 1 (by rfl) ⟨345113, by rfl⟩ : syracuseStep 460151 = 690227) B690227
theorem B2622851 : Blo 459783 2622851 := bstep (se 1 (by rfl) ⟨1967138, by rfl⟩ : syracuseStep 2622851 = 3934277) B3934277
theorem B2327939 : Blo 459783 2327939 := bstep (se 1 (by rfl) ⟨1745954, by rfl⟩ : syracuseStep 2327939 = 3491909) B3491909
theorem B460171 : Blo 459783 460171 := bstep (se 1 (by rfl) ⟨345128, by rfl⟩ : syracuseStep 460171 = 690257) B690257
theorem B460183 : Blo 459783 460183 := bstep (se 1 (by rfl) ⟨345137, by rfl⟩ : syracuseStep 460183 = 690275) B690275
theorem B460203 : Blo 459783 460203 := bstep (se 1 (by rfl) ⟨345152, by rfl⟩ : syracuseStep 460203 = 690305) B690305
theorem B460215 : Blo 459783 460215 := bstep (se 1 (by rfl) ⟨345161, by rfl⟩ : syracuseStep 460215 = 690323) B690323
theorem B460235 : Blo 459783 460235 := bstep (se 1 (by rfl) ⟨345176, by rfl⟩ : syracuseStep 460235 = 690353) B690353
theorem B460247 : Blo 459783 460247 := bstep (se 1 (by rfl) ⟨345185, by rfl⟩ : syracuseStep 460247 = 690371) B690371
theorem B493015 : Blo 459783 493015 := bstep (se 1 (by rfl) ⟨369761, by rfl⟩ : syracuseStep 493015 = 739523) B739523
theorem B1246681 : Blo 459783 1246681 := bstep (se 2 (by rfl) ⟨467505, by rfl⟩ : syracuseStep 1246681 = 935011) B935011
theorem B460267 : Blo 459783 460267 := bstep (se 1 (by rfl) ⟨345200, by rfl⟩ : syracuseStep 460267 = 690401) B690401
theorem B460279 : Blo 459783 460279 := bstep (se 1 (by rfl) ⟨345209, by rfl⟩ : syracuseStep 460279 = 690419) B690419
theorem B689675 : Blo 459783 689675 := bstep (se 1 (by rfl) ⟨517256, by rfl⟩ : syracuseStep 689675 = 1034513) B1034513
theorem B460299 : Blo 459783 460299 := bstep (se 1 (by rfl) ⟨345224, by rfl⟩ : syracuseStep 460299 = 690449) B690449
theorem B689687 : Blo 459783 689687 := bstep (se 1 (by rfl) ⟨517265, by rfl⟩ : syracuseStep 689687 = 1034531) B1034531
theorem B460311 : Blo 459783 460311 := bstep (se 1 (by rfl) ⟨345233, by rfl⟩ : syracuseStep 460311 = 690467) B690467
theorem B1050137 : Blo 459783 1050137 := bstep (se 2 (by rfl) ⟨393801, by rfl⟩ : syracuseStep 1050137 = 787603) B787603
theorem B460331 : Blo 459783 460331 := bstep (se 1 (by rfl) ⟨345248, by rfl⟩ : syracuseStep 460331 = 690497) B690497
theorem B460343 : Blo 459783 460343 := bstep (se 1 (by rfl) ⟨345257, by rfl⟩ : syracuseStep 460343 = 690515) B690515
theorem B460363 : Blo 459783 460363 := bstep (se 1 (by rfl) ⟨345272, by rfl⟩ : syracuseStep 460363 = 690545) B690545
theorem B460375 : Blo 459783 460375 := bstep (se 1 (by rfl) ⟨345281, by rfl⟩ : syracuseStep 460375 = 690563) B690563
theorem B689753 : Blo 459783 689753 := bstep (se 2 (by rfl) ⟨258657, by rfl⟩ : syracuseStep 689753 = 517315) B517315
theorem B460395 : Blo 459783 460395 := bstep (se 1 (by rfl) ⟨345296, by rfl⟩ : syracuseStep 460395 = 690593) B690593
theorem B460407 : Blo 459783 460407 := bstep (se 1 (by rfl) ⟨345305, by rfl⟩ : syracuseStep 460407 = 690611) B690611
theorem B460427 : Blo 459783 460427 := bstep (se 1 (by rfl) ⟨345320, by rfl⟩ : syracuseStep 460427 = 690641) B690641
theorem B460439 : Blo 459783 460439 := bstep (se 1 (by rfl) ⟨345329, by rfl⟩ : syracuseStep 460439 = 690659) B690659
theorem B460459 : Blo 459783 460459 := bstep (se 1 (by rfl) ⟨345344, by rfl⟩ : syracuseStep 460459 = 690689) B690689
theorem B1607347 : Blo 459783 1607347 := bstep (se 1 (by rfl) ⟨1205510, by rfl⟩ : syracuseStep 1607347 = 2411021) B2411021
theorem B460471 : Blo 459783 460471 := bstep (se 1 (by rfl) ⟨345353, by rfl⟩ : syracuseStep 460471 = 690707) B690707
theorem B689867 : Blo 459783 689867 := bstep (se 1 (by rfl) ⟨517400, by rfl⟩ : syracuseStep 689867 = 1034801) B1034801
theorem B460491 : Blo 459783 460491 := bstep (se 1 (by rfl) ⟨345368, by rfl⟩ : syracuseStep 460491 = 690737) B690737
theorem B689879 : Blo 459783 689879 := bstep (se 1 (by rfl) ⟨517409, by rfl⟩ : syracuseStep 689879 = 1034819) B1034819
theorem B460503 : Blo 459783 460503 := bstep (se 1 (by rfl) ⟨345377, by rfl⟩ : syracuseStep 460503 = 690755) B690755
theorem B460523 : Blo 459783 460523 := bstep (se 1 (by rfl) ⟨345392, by rfl⟩ : syracuseStep 460523 = 690785) B690785
theorem B460535 : Blo 459783 460535 := bstep (se 1 (by rfl) ⟨345401, by rfl⟩ : syracuseStep 460535 = 690803) B690803
theorem B460555 : Blo 459783 460555 := bstep (se 1 (by rfl) ⟨345416, by rfl⟩ : syracuseStep 460555 = 690833) B690833
theorem B460567 : Blo 459783 460567 := bstep (se 1 (by rfl) ⟨345425, by rfl⟩ : syracuseStep 460567 = 690851) B690851
theorem B689945 : Blo 459783 689945 := bstep (se 2 (by rfl) ⟨258729, by rfl⟩ : syracuseStep 689945 = 517459) B517459
theorem B886553 : Blo 459783 886553 := bstep (se 2 (by rfl) ⟨332457, by rfl⟩ : syracuseStep 886553 = 664915) B664915
theorem B460587 : Blo 459783 460587 := bstep (se 1 (by rfl) ⟨345440, by rfl⟩ : syracuseStep 460587 = 690881) B690881
theorem B460599 : Blo 459783 460599 := bstep (se 1 (by rfl) ⟨345449, by rfl⟩ : syracuseStep 460599 = 690899) B690899
theorem B460619 : Blo 459783 460619 := bstep (se 1 (by rfl) ⟨345464, by rfl⟩ : syracuseStep 460619 = 690929) B690929
theorem B460631 : Blo 459783 460631 := bstep (se 1 (by rfl) ⟨345473, by rfl⟩ : syracuseStep 460631 = 690947) B690947
theorem B657239 : Blo 459783 657239 := bstep (se 1 (by rfl) ⟨492929, by rfl⟩ : syracuseStep 657239 = 985859) B985859
theorem B460651 : Blo 459783 460651 := bstep (se 1 (by rfl) ⟨345488, by rfl⟩ : syracuseStep 460651 = 690977) B690977
theorem B460663 : Blo 459783 460663 := bstep (se 1 (by rfl) ⟨345497, by rfl⟩ : syracuseStep 460663 = 690995) B690995
theorem B690059 : Blo 459783 690059 := bstep (se 1 (by rfl) ⟨517544, by rfl⟩ : syracuseStep 690059 = 1035089) B1035089
theorem B460683 : Blo 459783 460683 := bstep (se 1 (by rfl) ⟨345512, by rfl⟩ : syracuseStep 460683 = 691025) B691025
theorem B690071 : Blo 459783 690071 := bstep (se 1 (by rfl) ⟨517553, by rfl⟩ : syracuseStep 690071 = 1035107) B1035107
theorem B1771415 : Blo 459783 1771415 := bstep (se 1 (by rfl) ⟨1328561, by rfl⟩ : syracuseStep 1771415 = 2657123) B2657123
theorem B460695 : Blo 459783 460695 := bstep (se 1 (by rfl) ⟨345521, by rfl⟩ : syracuseStep 460695 = 691043) B691043
theorem B460715 : Blo 459783 460715 := bstep (se 1 (by rfl) ⟨345536, by rfl⟩ : syracuseStep 460715 = 691073) B691073
theorem B460727 : Blo 459783 460727 := bstep (se 1 (by rfl) ⟨345545, by rfl⟩ : syracuseStep 460727 = 691091) B691091
theorem B460747 : Blo 459783 460747 := bstep (se 1 (by rfl) ⟨345560, by rfl⟩ : syracuseStep 460747 = 691121) B691121
theorem B460759 : Blo 459783 460759 := bstep (se 1 (by rfl) ⟨345569, by rfl⟩ : syracuseStep 460759 = 691139) B691139
theorem B690137 : Blo 459783 690137 := bstep (se 2 (by rfl) ⟨258801, by rfl⟩ : syracuseStep 690137 = 517603) B517603
theorem B460779 : Blo 459783 460779 := bstep (se 1 (by rfl) ⟨345584, by rfl⟩ : syracuseStep 460779 = 691169) B691169
theorem B460791 : Blo 459783 460791 := bstep (se 1 (by rfl) ⟨345593, by rfl⟩ : syracuseStep 460791 = 691187) B691187
theorem B460811 : Blo 459783 460811 := bstep (se 1 (by rfl) ⟨345608, by rfl⟩ : syracuseStep 460811 = 691217) B691217
theorem B460823 : Blo 459783 460823 := bstep (se 1 (by rfl) ⟨345617, by rfl⟩ : syracuseStep 460823 = 691235) B691235
theorem B657433 : Blo 459783 657433 := bstep (se 2 (by rfl) ⟨246537, by rfl⟩ : syracuseStep 657433 = 493075) B493075
theorem B460843 : Blo 459783 460843 := bstep (se 1 (by rfl) ⟨345632, by rfl⟩ : syracuseStep 460843 = 691265) B691265
theorem B460855 : Blo 459783 460855 := bstep (se 1 (by rfl) ⟨345641, by rfl⟩ : syracuseStep 460855 = 691283) B691283
theorem B690251 : Blo 459783 690251 := bstep (se 1 (by rfl) ⟨517688, by rfl⟩ : syracuseStep 690251 = 1035377) B1035377
theorem B460875 : Blo 459783 460875 := bstep (se 1 (by rfl) ⟨345656, by rfl⟩ : syracuseStep 460875 = 691313) B691313
theorem B690263 : Blo 459783 690263 := bstep (se 1 (by rfl) ⟨517697, by rfl⟩ : syracuseStep 690263 = 1035395) B1035395
theorem B460887 : Blo 459783 460887 := bstep (se 1 (by rfl) ⟨345665, by rfl⟩ : syracuseStep 460887 = 691331) B691331
theorem B1312861 : Blo 459783 1312861 := bstep (se 3 (by rfl) ⟨246161, by rfl⟩ : syracuseStep 1312861 = 492323) B492323
theorem B460907 : Blo 459783 460907 := bstep (se 1 (by rfl) ⟨345680, by rfl⟩ : syracuseStep 460907 = 691361) B691361
theorem B460919 : Blo 459783 460919 := bstep (se 1 (by rfl) ⟨345689, by rfl⟩ : syracuseStep 460919 = 691379) B691379
theorem B460939 : Blo 459783 460939 := bstep (se 1 (by rfl) ⟨345704, by rfl⟩ : syracuseStep 460939 = 691409) B691409
theorem B460951 : Blo 459783 460951 := bstep (se 1 (by rfl) ⟨345713, by rfl⟩ : syracuseStep 460951 = 691427) B691427
theorem B1312919 : Blo 459783 1312919 := bstep (se 1 (by rfl) ⟨984689, by rfl⟩ : syracuseStep 1312919 = 1969379) B1969379
theorem B690329 : Blo 459783 690329 := bstep (se 2 (by rfl) ⟨258873, by rfl⟩ : syracuseStep 690329 = 517747) B517747
theorem B460971 : Blo 459783 460971 := bstep (se 1 (by rfl) ⟨345728, by rfl⟩ : syracuseStep 460971 = 691457) B691457
theorem B460983 : Blo 459783 460983 := bstep (se 1 (by rfl) ⟨345737, by rfl⟩ : syracuseStep 460983 = 691475) B691475
theorem B461003 : Blo 459783 461003 := bstep (se 1 (by rfl) ⟨345752, by rfl⟩ : syracuseStep 461003 = 691505) B691505
theorem B461015 : Blo 459783 461015 := bstep (se 1 (by rfl) ⟨345761, by rfl⟩ : syracuseStep 461015 = 691523) B691523
theorem B461035 : Blo 459783 461035 := bstep (se 1 (by rfl) ⟨345776, by rfl⟩ : syracuseStep 461035 = 691553) B691553
theorem B461047 : Blo 459783 461047 := bstep (se 1 (by rfl) ⟨345785, by rfl⟩ : syracuseStep 461047 = 691571) B691571
theorem B690443 : Blo 459783 690443 := bstep (se 1 (by rfl) ⟨517832, by rfl⟩ : syracuseStep 690443 = 1035665) B1035665
theorem B461067 : Blo 459783 461067 := bstep (se 1 (by rfl) ⟨345800, by rfl⟩ : syracuseStep 461067 = 691601) B691601
theorem B493835 : Blo 459783 493835 := bstep (se 1 (by rfl) ⟨370376, by rfl⟩ : syracuseStep 493835 = 740753) B740753
theorem B690455 : Blo 459783 690455 := bstep (se 1 (by rfl) ⟨517841, by rfl⟩ : syracuseStep 690455 = 1035683) B1035683
theorem B461079 : Blo 459783 461079 := bstep (se 1 (by rfl) ⟨345809, by rfl⟩ : syracuseStep 461079 = 691619) B691619
theorem B461099 : Blo 459783 461099 := bstep (se 1 (by rfl) ⟨345824, by rfl⟩ : syracuseStep 461099 = 691649) B691649
theorem B461111 : Blo 459783 461111 := bstep (se 1 (by rfl) ⟨345833, by rfl⟩ : syracuseStep 461111 = 691667) B691667
theorem B461131 : Blo 459783 461131 := bstep (se 1 (by rfl) ⟨345848, by rfl⟩ : syracuseStep 461131 = 691697) B691697
theorem B461143 : Blo 459783 461143 := bstep (se 1 (by rfl) ⟨345857, by rfl⟩ : syracuseStep 461143 = 691715) B691715
theorem B690521 : Blo 459783 690521 := bstep (se 2 (by rfl) ⟨258945, by rfl⟩ : syracuseStep 690521 = 517891) B517891
theorem B461163 : Blo 459783 461163 := bstep (se 1 (by rfl) ⟨345872, by rfl⟩ : syracuseStep 461163 = 691745) B691745
theorem B461175 : Blo 459783 461175 := bstep (se 1 (by rfl) ⟨345881, by rfl⟩ : syracuseStep 461175 = 691763) B691763
theorem B461195 : Blo 459783 461195 := bstep (se 1 (by rfl) ⟨345896, by rfl⟩ : syracuseStep 461195 = 691793) B691793
theorem B985483 : Blo 459783 985483 := bstep (se 1 (by rfl) ⟨739112, by rfl⟩ : syracuseStep 985483 = 1478225) B1478225
theorem B461207 : Blo 459783 461207 := bstep (se 1 (by rfl) ⟨345905, by rfl⟩ : syracuseStep 461207 = 691811) B691811
theorem B461227 : Blo 459783 461227 := bstep (se 1 (by rfl) ⟨345920, by rfl⟩ : syracuseStep 461227 = 691841) B691841
theorem B461239 : Blo 459783 461239 := bstep (se 1 (by rfl) ⟨345929, by rfl⟩ : syracuseStep 461239 = 691859) B691859
theorem B690635 : Blo 459783 690635 := bstep (se 1 (by rfl) ⟨517976, by rfl⟩ : syracuseStep 690635 = 1035953) B1035953
theorem B461259 : Blo 459783 461259 := bstep (se 1 (by rfl) ⟨345944, by rfl⟩ : syracuseStep 461259 = 691889) B691889
theorem B690647 : Blo 459783 690647 := bstep (se 1 (by rfl) ⟨517985, by rfl⟩ : syracuseStep 690647 = 1035971) B1035971
theorem B461271 : Blo 459783 461271 := bstep (se 1 (by rfl) ⟨345953, by rfl⟩ : syracuseStep 461271 = 691907) B691907
theorem B461291 : Blo 459783 461291 := bstep (se 1 (by rfl) ⟨345968, by rfl⟩ : syracuseStep 461291 = 691937) B691937
theorem B461303 : Blo 459783 461303 := bstep (se 1 (by rfl) ⟨345977, by rfl⟩ : syracuseStep 461303 = 691955) B691955
theorem B461323 : Blo 459783 461323 := bstep (se 1 (by rfl) ⟨345992, by rfl⟩ : syracuseStep 461323 = 691985) B691985
theorem B461335 : Blo 459783 461335 := bstep (se 1 (by rfl) ⟨346001, by rfl⟩ : syracuseStep 461335 = 692003) B692003
theorem B690713 : Blo 459783 690713 := bstep (se 2 (by rfl) ⟨259017, by rfl⟩ : syracuseStep 690713 = 518035) B518035
theorem B461355 : Blo 459783 461355 := bstep (se 1 (by rfl) ⟨346016, by rfl⟩ : syracuseStep 461355 = 692033) B692033
theorem B461367 : Blo 459783 461367 := bstep (se 1 (by rfl) ⟨346025, by rfl⟩ : syracuseStep 461367 = 692051) B692051
theorem B461387 : Blo 459783 461387 := bstep (se 1 (by rfl) ⟨346040, by rfl⟩ : syracuseStep 461387 = 692081) B692081
theorem B461399 : Blo 459783 461399 := bstep (se 1 (by rfl) ⟨346049, by rfl⟩ : syracuseStep 461399 = 692099) B692099
theorem B592471 : Blo 459783 592471 := bstep (se 1 (by rfl) ⟨444353, by rfl⟩ : syracuseStep 592471 = 888707) B888707
theorem B4983389 : Blo 459783 4983389 := bstep (se 3 (by rfl) ⟨934385, by rfl⟩ : syracuseStep 4983389 = 1868771) B1868771
theorem B461419 : Blo 459783 461419 := bstep (se 1 (by rfl) ⟨346064, by rfl⟩ : syracuseStep 461419 = 692129) B692129
theorem B461431 : Blo 459783 461431 := bstep (se 1 (by rfl) ⟨346073, by rfl⟩ : syracuseStep 461431 = 692147) B692147
theorem B690827 : Blo 459783 690827 := bstep (se 1 (by rfl) ⟨518120, by rfl⟩ : syracuseStep 690827 = 1036241) B1036241
theorem B461451 : Blo 459783 461451 := bstep (se 1 (by rfl) ⟨346088, by rfl⟩ : syracuseStep 461451 = 692177) B692177
theorem B690839 : Blo 459783 690839 := bstep (se 1 (by rfl) ⟨518129, by rfl⟩ : syracuseStep 690839 = 1036259) B1036259
theorem B461463 : Blo 459783 461463 := bstep (se 1 (by rfl) ⟨346097, by rfl⟩ : syracuseStep 461463 = 692195) B692195
theorem B461483 : Blo 459783 461483 := bstep (se 1 (by rfl) ⟨346112, by rfl⟩ : syracuseStep 461483 = 692225) B692225
theorem B1247923 : Blo 459783 1247923 := bstep (se 1 (by rfl) ⟨935942, by rfl⟩ : syracuseStep 1247923 = 1871885) B1871885
theorem B461495 : Blo 459783 461495 := bstep (se 1 (by rfl) ⟨346121, by rfl⟩ : syracuseStep 461495 = 692243) B692243
theorem B461515 : Blo 459783 461515 := bstep (se 1 (by rfl) ⟨346136, by rfl⟩ : syracuseStep 461515 = 692273) B692273
theorem B461527 : Blo 459783 461527 := bstep (se 1 (by rfl) ⟨346145, by rfl⟩ : syracuseStep 461527 = 692291) B692291
theorem B690905 : Blo 459783 690905 := bstep (se 2 (by rfl) ⟨259089, by rfl⟩ : syracuseStep 690905 = 518179) B518179
theorem B461547 : Blo 459783 461547 := bstep (se 1 (by rfl) ⟨346160, by rfl⟩ : syracuseStep 461547 = 692321) B692321
theorem B461559 : Blo 459783 461559 := bstep (se 1 (by rfl) ⟨346169, by rfl⟩ : syracuseStep 461559 = 692339) B692339
theorem B461579 : Blo 459783 461579 := bstep (se 1 (by rfl) ⟨346184, by rfl⟩ : syracuseStep 461579 = 692369) B692369
theorem B461591 : Blo 459783 461591 := bstep (se 1 (by rfl) ⟨346193, by rfl⟩ : syracuseStep 461591 = 692387) B692387
theorem B461611 : Blo 459783 461611 := bstep (se 1 (by rfl) ⟨346208, by rfl⟩ : syracuseStep 461611 = 692417) B692417
theorem B461623 : Blo 459783 461623 := bstep (se 1 (by rfl) ⟨346217, by rfl⟩ : syracuseStep 461623 = 692435) B692435
theorem B691019 : Blo 459783 691019 := bstep (se 1 (by rfl) ⟨518264, by rfl⟩ : syracuseStep 691019 = 1036529) B1036529
theorem B461643 : Blo 459783 461643 := bstep (se 1 (by rfl) ⟨346232, by rfl⟩ : syracuseStep 461643 = 692465) B692465
theorem B691031 : Blo 459783 691031 := bstep (se 1 (by rfl) ⟨518273, by rfl⟩ : syracuseStep 691031 = 1036547) B1036547
theorem B461655 : Blo 459783 461655 := bstep (se 1 (by rfl) ⟨346241, by rfl⟩ : syracuseStep 461655 = 692483) B692483
theorem B985945 : Blo 459783 985945 := bstep (se 2 (by rfl) ⟨369729, by rfl⟩ : syracuseStep 985945 = 739459) B739459
theorem B461675 : Blo 459783 461675 := bstep (se 1 (by rfl) ⟨346256, by rfl⟩ : syracuseStep 461675 = 692513) B692513
theorem B461687 : Blo 459783 461687 := bstep (se 1 (by rfl) ⟨346265, by rfl⟩ : syracuseStep 461687 = 692531) B692531
theorem B461707 : Blo 459783 461707 := bstep (se 1 (by rfl) ⟨346280, by rfl⟩ : syracuseStep 461707 = 692561) B692561
theorem B461719 : Blo 459783 461719 := bstep (se 1 (by rfl) ⟨346289, by rfl⟩ : syracuseStep 461719 = 692579) B692579
theorem B691097 : Blo 459783 691097 := bstep (se 2 (by rfl) ⟨259161, by rfl⟩ : syracuseStep 691097 = 518323) B518323
theorem B461739 : Blo 459783 461739 := bstep (se 1 (by rfl) ⟨346304, by rfl⟩ : syracuseStep 461739 = 692609) B692609
theorem B1182643 : Blo 459783 1182643 := bstep (se 1 (by rfl) ⟨886982, by rfl⟩ : syracuseStep 1182643 = 1773965) B1773965
theorem B461751 : Blo 459783 461751 := bstep (se 1 (by rfl) ⟨346313, by rfl⟩ : syracuseStep 461751 = 692627) B692627
theorem B461771 : Blo 459783 461771 := bstep (se 1 (by rfl) ⟨346328, by rfl⟩ : syracuseStep 461771 = 692657) B692657
theorem B461783 : Blo 459783 461783 := bstep (se 1 (by rfl) ⟨346337, by rfl⟩ : syracuseStep 461783 = 692675) B692675
theorem B461803 : Blo 459783 461803 := bstep (se 1 (by rfl) ⟨346352, by rfl⟩ : syracuseStep 461803 = 692705) B692705
theorem B461815 : Blo 459783 461815 := bstep (se 1 (by rfl) ⟨346361, by rfl⟩ : syracuseStep 461815 = 692723) B692723
theorem B691211 : Blo 459783 691211 := bstep (se 1 (by rfl) ⟨518408, by rfl⟩ : syracuseStep 691211 = 1036817) B1036817
theorem B461835 : Blo 459783 461835 := bstep (se 1 (by rfl) ⟨346376, by rfl⟩ : syracuseStep 461835 = 692753) B692753
theorem B691223 : Blo 459783 691223 := bstep (se 1 (by rfl) ⟨518417, by rfl⟩ : syracuseStep 691223 = 1036835) B1036835
theorem B461847 : Blo 459783 461847 := bstep (se 1 (by rfl) ⟨346385, by rfl⟩ : syracuseStep 461847 = 692771) B692771
theorem B461867 : Blo 459783 461867 := bstep (se 1 (by rfl) ⟨346400, by rfl⟩ : syracuseStep 461867 = 692801) B692801
theorem B461879 : Blo 459783 461879 := bstep (se 1 (by rfl) ⟨346409, by rfl⟩ : syracuseStep 461879 = 692819) B692819
theorem B461899 : Blo 459783 461899 := bstep (se 1 (by rfl) ⟨346424, by rfl⟩ : syracuseStep 461899 = 692849) B692849
theorem B461911 : Blo 459783 461911 := bstep (se 1 (by rfl) ⟨346433, by rfl⟩ : syracuseStep 461911 = 692867) B692867
theorem B691289 : Blo 459783 691289 := bstep (se 2 (by rfl) ⟨259233, by rfl⟩ : syracuseStep 691289 = 518467) B518467
theorem B461931 : Blo 459783 461931 := bstep (se 1 (by rfl) ⟨346448, by rfl⟩ : syracuseStep 461931 = 692897) B692897
theorem B461943 : Blo 459783 461943 := bstep (se 1 (by rfl) ⟨346457, by rfl⟩ : syracuseStep 461943 = 692915) B692915
theorem B461963 : Blo 459783 461963 := bstep (se 1 (by rfl) ⟨346472, by rfl⟩ : syracuseStep 461963 = 692945) B692945
theorem B461975 : Blo 459783 461975 := bstep (se 1 (by rfl) ⟨346481, by rfl⟩ : syracuseStep 461975 = 692963) B692963
theorem B461995 : Blo 459783 461995 := bstep (se 1 (by rfl) ⟨346496, by rfl⟩ : syracuseStep 461995 = 692993) B692993
theorem B462007 : Blo 459783 462007 := bstep (se 1 (by rfl) ⟨346505, by rfl⟩ : syracuseStep 462007 = 693011) B693011
theorem B691403 : Blo 459783 691403 := bstep (se 1 (by rfl) ⟨518552, by rfl⟩ : syracuseStep 691403 = 1037105) B1037105
theorem B462027 : Blo 459783 462027 := bstep (se 1 (by rfl) ⟨346520, by rfl⟩ : syracuseStep 462027 = 693041) B693041
theorem B691415 : Blo 459783 691415 := bstep (se 1 (by rfl) ⟨518561, by rfl⟩ : syracuseStep 691415 = 1037123) B1037123
theorem B888023 : Blo 459783 888023 := bstep (se 1 (by rfl) ⟨666017, by rfl⟩ : syracuseStep 888023 = 1332035) B1332035
theorem B462039 : Blo 459783 462039 := bstep (se 1 (by rfl) ⟨346529, by rfl⟩ : syracuseStep 462039 = 693059) B693059
theorem B462059 : Blo 459783 462059 := bstep (se 1 (by rfl) ⟨346544, by rfl⟩ : syracuseStep 462059 = 693089) B693089
theorem B462071 : Blo 459783 462071 := bstep (se 1 (by rfl) ⟨346553, by rfl⟩ : syracuseStep 462071 = 693107) B693107
theorem B494839 : Blo 459783 494839 := bstep (se 1 (by rfl) ⟨371129, by rfl⟩ : syracuseStep 494839 = 742259) B742259
theorem B462091 : Blo 459783 462091 := bstep (se 1 (by rfl) ⟨346568, by rfl⟩ : syracuseStep 462091 = 693137) B693137
theorem B462103 : Blo 459783 462103 := bstep (se 1 (by rfl) ⟨346577, by rfl⟩ : syracuseStep 462103 = 693155) B693155
theorem B691481 : Blo 459783 691481 := bstep (se 2 (by rfl) ⟨259305, by rfl⟩ : syracuseStep 691481 = 518611) B518611
theorem B462123 : Blo 459783 462123 := bstep (se 1 (by rfl) ⟨346592, by rfl⟩ : syracuseStep 462123 = 693185) B693185
theorem B462135 : Blo 459783 462135 := bstep (se 1 (by rfl) ⟨346601, by rfl⟩ : syracuseStep 462135 = 693203) B693203
theorem B462155 : Blo 459783 462155 := bstep (se 1 (by rfl) ⟨346616, by rfl⟩ : syracuseStep 462155 = 693233) B693233
theorem B462167 : Blo 459783 462167 := bstep (se 1 (by rfl) ⟨346625, by rfl⟩ : syracuseStep 462167 = 693251) B693251
theorem B1314137 : Blo 459783 1314137 := bstep (se 2 (by rfl) ⟨492801, by rfl⟩ : syracuseStep 1314137 = 985603) B985603
theorem B462187 : Blo 459783 462187 := bstep (se 1 (by rfl) ⟨346640, by rfl⟩ : syracuseStep 462187 = 693281) B693281
theorem B462199 : Blo 459783 462199 := bstep (se 1 (by rfl) ⟨346649, by rfl⟩ : syracuseStep 462199 = 693299) B693299
theorem B691595 : Blo 459783 691595 := bstep (se 1 (by rfl) ⟨518696, by rfl⟩ : syracuseStep 691595 = 1037393) B1037393
theorem B462219 : Blo 459783 462219 := bstep (se 1 (by rfl) ⟨346664, by rfl⟩ : syracuseStep 462219 = 693329) B693329
theorem B691607 : Blo 459783 691607 := bstep (se 1 (by rfl) ⟨518705, by rfl⟩ : syracuseStep 691607 = 1037411) B1037411
theorem B462231 : Blo 459783 462231 := bstep (se 1 (by rfl) ⟨346673, by rfl⟩ : syracuseStep 462231 = 693347) B693347
theorem B462251 : Blo 459783 462251 := bstep (se 1 (by rfl) ⟨346688, by rfl⟩ : syracuseStep 462251 = 693377) B693377
theorem B462263 : Blo 459783 462263 := bstep (se 1 (by rfl) ⟨346697, by rfl⟩ : syracuseStep 462263 = 693395) B693395
theorem B1314251 : Blo 459783 1314251 := bstep (se 1 (by rfl) ⟨985688, by rfl⟩ : syracuseStep 1314251 = 1971377) B1971377
theorem B462283 : Blo 459783 462283 := bstep (se 1 (by rfl) ⟨346712, by rfl⟩ : syracuseStep 462283 = 693425) B693425
theorem B658891 : Blo 459783 658891 := bstep (se 1 (by rfl) ⟨494168, by rfl⟩ : syracuseStep 658891 = 988337) B988337
theorem B462295 : Blo 459783 462295 := bstep (se 1 (by rfl) ⟨346721, by rfl⟩ : syracuseStep 462295 = 693443) B693443
theorem B691673 : Blo 459783 691673 := bstep (se 2 (by rfl) ⟨259377, by rfl⟩ : syracuseStep 691673 = 518755) B518755
theorem B462315 : Blo 459783 462315 := bstep (se 1 (by rfl) ⟨346736, by rfl⟩ : syracuseStep 462315 = 693473) B693473
theorem B462327 : Blo 459783 462327 := bstep (se 1 (by rfl) ⟨346745, by rfl⟩ : syracuseStep 462327 = 693491) B693491
theorem B1969667 : Blo 459783 1969667 := bstep (se 1 (by rfl) ⟨1477250, by rfl⟩ : syracuseStep 1969667 = 2954501) B2954501
theorem B462347 : Blo 459783 462347 := bstep (se 1 (by rfl) ⟨346760, by rfl⟩ : syracuseStep 462347 = 693521) B693521
theorem B462359 : Blo 459783 462359 := bstep (se 1 (by rfl) ⟨346769, by rfl⟩ : syracuseStep 462359 = 693539) B693539
theorem B462379 : Blo 459783 462379 := bstep (se 1 (by rfl) ⟨346784, by rfl⟩ : syracuseStep 462379 = 693569) B693569
theorem B462391 : Blo 459783 462391 := bstep (se 1 (by rfl) ⟨346793, by rfl⟩ : syracuseStep 462391 = 693587) B693587
theorem B691787 : Blo 459783 691787 := bstep (se 1 (by rfl) ⟨518840, by rfl⟩ : syracuseStep 691787 = 1037681) B1037681
theorem B462411 : Blo 459783 462411 := bstep (se 1 (by rfl) ⟨346808, by rfl⟩ : syracuseStep 462411 = 693617) B693617
theorem B691799 : Blo 459783 691799 := bstep (se 1 (by rfl) ⟨518849, by rfl⟩ : syracuseStep 691799 = 1037699) B1037699
theorem B462423 : Blo 459783 462423 := bstep (se 1 (by rfl) ⟨346817, by rfl⟩ : syracuseStep 462423 = 693635) B693635
theorem B462443 : Blo 459783 462443 := bstep (se 1 (by rfl) ⟨346832, by rfl⟩ : syracuseStep 462443 = 693665) B693665
theorem B462455 : Blo 459783 462455 := bstep (se 1 (by rfl) ⟨346841, by rfl⟩ : syracuseStep 462455 = 693683) B693683
theorem B3509891 : Blo 459783 3509891 := bstep (se 1 (by rfl) ⟨2632418, by rfl⟩ : syracuseStep 3509891 = 5264837) B5264837
theorem B462475 : Blo 459783 462475 := bstep (se 1 (by rfl) ⟨346856, by rfl⟩ : syracuseStep 462475 = 693713) B693713
theorem B462487 : Blo 459783 462487 := bstep (se 1 (by rfl) ⟨346865, by rfl⟩ : syracuseStep 462487 = 693731) B693731
theorem B691865 : Blo 459783 691865 := bstep (se 2 (by rfl) ⟨259449, by rfl⟩ : syracuseStep 691865 = 518899) B518899
theorem B462507 : Blo 459783 462507 := bstep (se 1 (by rfl) ⟨346880, by rfl⟩ : syracuseStep 462507 = 693761) B693761
theorem B462519 : Blo 459783 462519 := bstep (se 1 (by rfl) ⟨346889, by rfl⟩ : syracuseStep 462519 = 693779) B693779
theorem B462539 : Blo 459783 462539 := bstep (se 1 (by rfl) ⟨346904, by rfl⟩ : syracuseStep 462539 = 693809) B693809
theorem B462551 : Blo 459783 462551 := bstep (se 1 (by rfl) ⟨346913, by rfl⟩ : syracuseStep 462551 = 693827) B693827
theorem B462571 : Blo 459783 462571 := bstep (se 1 (by rfl) ⟨346928, by rfl⟩ : syracuseStep 462571 = 693857) B693857
theorem B462583 : Blo 459783 462583 := bstep (se 1 (by rfl) ⟨346937, by rfl⟩ : syracuseStep 462583 = 693875) B693875
theorem B691979 : Blo 459783 691979 := bstep (se 1 (by rfl) ⟨518984, by rfl⟩ : syracuseStep 691979 = 1037969) B1037969
theorem B462603 : Blo 459783 462603 := bstep (se 1 (by rfl) ⟨346952, by rfl⟩ : syracuseStep 462603 = 693905) B693905
theorem B691991 : Blo 459783 691991 := bstep (se 1 (by rfl) ⟨518993, by rfl⟩ : syracuseStep 691991 = 1037987) B1037987
theorem B462615 : Blo 459783 462615 := bstep (se 1 (by rfl) ⟨346961, by rfl⟩ : syracuseStep 462615 = 693923) B693923
theorem B462635 : Blo 459783 462635 := bstep (se 1 (by rfl) ⟨346976, by rfl⟩ : syracuseStep 462635 = 693953) B693953
theorem B462647 : Blo 459783 462647 := bstep (se 1 (by rfl) ⟨346985, by rfl⟩ : syracuseStep 462647 = 693971) B693971
theorem B462667 : Blo 459783 462667 := bstep (se 1 (by rfl) ⟨347000, by rfl⟩ : syracuseStep 462667 = 694001) B694001
theorem B462679 : Blo 459783 462679 := bstep (se 1 (by rfl) ⟨347009, by rfl⟩ : syracuseStep 462679 = 694019) B694019
theorem B692057 : Blo 459783 692057 := bstep (se 2 (by rfl) ⟨259521, by rfl⟩ : syracuseStep 692057 = 519043) B519043
theorem B462699 : Blo 459783 462699 := bstep (se 1 (by rfl) ⟨347024, by rfl⟩ : syracuseStep 462699 = 694049) B694049
theorem B462711 : Blo 459783 462711 := bstep (se 1 (by rfl) ⟨347033, by rfl⟩ : syracuseStep 462711 = 694067) B694067
theorem B462731 : Blo 459783 462731 := bstep (se 1 (by rfl) ⟨347048, by rfl⟩ : syracuseStep 462731 = 694097) B694097
theorem B462743 : Blo 459783 462743 := bstep (se 1 (by rfl) ⟨347057, by rfl⟩ : syracuseStep 462743 = 694115) B694115
theorem B462763 : Blo 459783 462763 := bstep (se 1 (by rfl) ⟨347072, by rfl⟩ : syracuseStep 462763 = 694145) B694145
theorem B462775 : Blo 459783 462775 := bstep (se 1 (by rfl) ⟨347081, by rfl⟩ : syracuseStep 462775 = 694163) B694163
theorem B692171 : Blo 459783 692171 := bstep (se 1 (by rfl) ⟨519128, by rfl⟩ : syracuseStep 692171 = 1038257) B1038257
theorem B462795 : Blo 459783 462795 := bstep (se 1 (by rfl) ⟨347096, by rfl⟩ : syracuseStep 462795 = 694193) B694193
theorem B692183 : Blo 459783 692183 := bstep (se 1 (by rfl) ⟨519137, by rfl⟩ : syracuseStep 692183 = 1038275) B1038275
theorem B462807 : Blo 459783 462807 := bstep (se 1 (by rfl) ⟨347105, by rfl⟩ : syracuseStep 462807 = 694211) B694211
theorem B462827 : Blo 459783 462827 := bstep (se 1 (by rfl) ⟨347120, by rfl⟩ : syracuseStep 462827 = 694241) B694241
theorem B462839 : Blo 459783 462839 := bstep (se 1 (by rfl) ⟨347129, by rfl⟩ : syracuseStep 462839 = 694259) B694259
theorem B462859 : Blo 459783 462859 := bstep (se 1 (by rfl) ⟨347144, by rfl⟩ : syracuseStep 462859 = 694289) B694289
theorem B462871 : Blo 459783 462871 := bstep (se 1 (by rfl) ⟨347153, by rfl⟩ : syracuseStep 462871 = 694307) B694307
theorem B692249 : Blo 459783 692249 := bstep (se 2 (by rfl) ⟨259593, by rfl⟩ : syracuseStep 692249 = 519187) B519187
theorem B462891 : Blo 459783 462891 := bstep (se 1 (by rfl) ⟨347168, by rfl⟩ : syracuseStep 462891 = 694337) B694337
theorem B462903 : Blo 459783 462903 := bstep (se 1 (by rfl) ⟨347177, by rfl⟩ : syracuseStep 462903 = 694355) B694355
theorem B462923 : Blo 459783 462923 := bstep (se 1 (by rfl) ⟨347192, by rfl⟩ : syracuseStep 462923 = 694385) B694385
theorem B462935 : Blo 459783 462935 := bstep (se 1 (by rfl) ⟨347201, by rfl⟩ : syracuseStep 462935 = 694403) B694403
theorem B462955 : Blo 459783 462955 := bstep (se 1 (by rfl) ⟨347216, by rfl⟩ : syracuseStep 462955 = 694433) B694433
theorem B462967 : Blo 459783 462967 := bstep (se 1 (by rfl) ⟨347225, by rfl⟩ : syracuseStep 462967 = 694451) B694451
theorem B692363 : Blo 459783 692363 := bstep (se 1 (by rfl) ⟨519272, by rfl⟩ : syracuseStep 692363 = 1038545) B1038545
theorem B462987 : Blo 459783 462987 := bstep (se 1 (by rfl) ⟨347240, by rfl⟩ : syracuseStep 462987 = 694481) B694481
theorem B692375 : Blo 459783 692375 := bstep (se 1 (by rfl) ⟨519281, by rfl⟩ : syracuseStep 692375 = 1038563) B1038563
theorem B462999 : Blo 459783 462999 := bstep (se 1 (by rfl) ⟨347249, by rfl⟩ : syracuseStep 462999 = 694499) B694499
theorem B463019 : Blo 459783 463019 := bstep (se 1 (by rfl) ⟨347264, by rfl⟩ : syracuseStep 463019 = 694529) B694529
theorem B463031 : Blo 459783 463031 := bstep (se 1 (by rfl) ⟨347273, by rfl⟩ : syracuseStep 463031 = 694547) B694547
theorem B987329 : Blo 459783 987329 := bstep (se 2 (by rfl) ⟨370248, by rfl⟩ : syracuseStep 987329 = 740497) B740497
theorem B463051 : Blo 459783 463051 := bstep (se 1 (by rfl) ⟨347288, by rfl⟩ : syracuseStep 463051 = 694577) B694577
theorem B463063 : Blo 459783 463063 := bstep (se 1 (by rfl) ⟨347297, by rfl⟩ : syracuseStep 463063 = 694595) B694595
theorem B692441 : Blo 459783 692441 := bstep (se 2 (by rfl) ⟨259665, by rfl⟩ : syracuseStep 692441 = 519331) B519331
theorem B463083 : Blo 459783 463083 := bstep (se 1 (by rfl) ⟨347312, by rfl⟩ : syracuseStep 463083 = 694625) B694625
theorem B463095 : Blo 459783 463095 := bstep (se 1 (by rfl) ⟨347321, by rfl⟩ : syracuseStep 463095 = 694643) B694643
theorem B463115 : Blo 459783 463115 := bstep (se 1 (by rfl) ⟨347336, by rfl⟩ : syracuseStep 463115 = 694673) B694673
theorem B463127 : Blo 459783 463127 := bstep (se 1 (by rfl) ⟨347345, by rfl⟩ : syracuseStep 463127 = 694691) B694691
theorem B463147 : Blo 459783 463147 := bstep (se 1 (by rfl) ⟨347360, by rfl⟩ : syracuseStep 463147 = 694721) B694721
theorem B463159 : Blo 459783 463159 := bstep (se 1 (by rfl) ⟨347369, by rfl⟩ : syracuseStep 463159 = 694739) B694739
theorem B692555 : Blo 459783 692555 := bstep (se 1 (by rfl) ⟨519416, by rfl⟩ : syracuseStep 692555 = 1038833) B1038833
theorem B463179 : Blo 459783 463179 := bstep (se 1 (by rfl) ⟨347384, by rfl⟩ : syracuseStep 463179 = 694769) B694769
theorem B692567 : Blo 459783 692567 := bstep (se 1 (by rfl) ⟨519425, by rfl⟩ : syracuseStep 692567 = 1038851) B1038851
theorem B463191 : Blo 459783 463191 := bstep (se 1 (by rfl) ⟨347393, by rfl⟩ : syracuseStep 463191 = 694787) B694787
theorem B463211 : Blo 459783 463211 := bstep (se 1 (by rfl) ⟨347408, by rfl⟩ : syracuseStep 463211 = 694817) B694817
theorem B463223 : Blo 459783 463223 := bstep (se 1 (by rfl) ⟨347417, by rfl⟩ : syracuseStep 463223 = 694835) B694835
theorem B3150211 : Blo 459783 3150211 := bstep (se 1 (by rfl) ⟨2362658, by rfl⟩ : syracuseStep 3150211 = 4725317) B4725317
theorem B463243 : Blo 459783 463243 := bstep (se 1 (by rfl) ⟨347432, by rfl⟩ : syracuseStep 463243 = 694865) B694865
theorem B463255 : Blo 459783 463255 := bstep (se 1 (by rfl) ⟨347441, by rfl⟩ : syracuseStep 463255 = 694883) B694883
theorem B692633 : Blo 459783 692633 := bstep (se 2 (by rfl) ⟨259737, by rfl⟩ : syracuseStep 692633 = 519475) B519475
theorem B463275 : Blo 459783 463275 := bstep (se 1 (by rfl) ⟨347456, by rfl⟩ : syracuseStep 463275 = 694913) B694913
theorem B463287 : Blo 459783 463287 := bstep (se 1 (by rfl) ⟨347465, by rfl⟩ : syracuseStep 463287 = 694931) B694931
theorem B463307 : Blo 459783 463307 := bstep (se 1 (by rfl) ⟨347480, by rfl⟩ : syracuseStep 463307 = 694961) B694961
theorem B463319 : Blo 459783 463319 := bstep (se 1 (by rfl) ⟨347489, by rfl⟩ : syracuseStep 463319 = 694979) B694979
theorem B2494937 : Blo 459783 2494937 := bstep (se 2 (by rfl) ⟨935601, by rfl⟩ : syracuseStep 2494937 = 1871203) B1871203
theorem B463339 : Blo 459783 463339 := bstep (se 1 (by rfl) ⟨347504, by rfl⟩ : syracuseStep 463339 = 695009) B695009
theorem B463351 : Blo 459783 463351 := bstep (se 1 (by rfl) ⟨347513, by rfl⟩ : syracuseStep 463351 = 695027) B695027
theorem B692747 : Blo 459783 692747 := bstep (se 1 (by rfl) ⟨519560, by rfl⟩ : syracuseStep 692747 = 1039121) B1039121
theorem B463371 : Blo 459783 463371 := bstep (se 1 (by rfl) ⟨347528, by rfl⟩ : syracuseStep 463371 = 695057) B695057
theorem B692759 : Blo 459783 692759 := bstep (se 1 (by rfl) ⟨519569, by rfl⟩ : syracuseStep 692759 = 1039139) B1039139
theorem B463383 : Blo 459783 463383 := bstep (se 1 (by rfl) ⟨347537, by rfl⟩ : syracuseStep 463383 = 695075) B695075
theorem B463403 : Blo 459783 463403 := bstep (se 1 (by rfl) ⟨347552, by rfl⟩ : syracuseStep 463403 = 695105) B695105
theorem B1315379 : Blo 459783 1315379 := bstep (se 1 (by rfl) ⟨986534, by rfl⟩ : syracuseStep 1315379 = 1973069) B1973069
theorem B463415 : Blo 459783 463415 := bstep (se 1 (by rfl) ⟨347561, by rfl⟩ : syracuseStep 463415 = 695123) B695123
theorem B463435 : Blo 459783 463435 := bstep (se 1 (by rfl) ⟨347576, by rfl⟩ : syracuseStep 463435 = 695153) B695153
theorem B463447 : Blo 459783 463447 := bstep (se 1 (by rfl) ⟨347585, by rfl⟩ : syracuseStep 463447 = 695171) B695171
theorem B692825 : Blo 459783 692825 := bstep (se 2 (by rfl) ⟨259809, by rfl⟩ : syracuseStep 692825 = 519619) B519619
theorem B463467 : Blo 459783 463467 := bstep (se 1 (by rfl) ⟨347600, by rfl⟩ : syracuseStep 463467 = 695201) B695201
theorem B463479 : Blo 459783 463479 := bstep (se 1 (by rfl) ⟨347609, by rfl⟩ : syracuseStep 463479 = 695219) B695219
theorem B2101891 : Blo 459783 2101891 := bstep (se 1 (by rfl) ⟨1576418, by rfl⟩ : syracuseStep 2101891 = 3152837) B3152837
theorem B463499 : Blo 459783 463499 := bstep (se 1 (by rfl) ⟨347624, by rfl⟩ : syracuseStep 463499 = 695249) B695249
theorem B463511 : Blo 459783 463511 := bstep (se 1 (by rfl) ⟨347633, by rfl⟩ : syracuseStep 463511 = 695267) B695267
theorem B463531 : Blo 459783 463531 := bstep (se 1 (by rfl) ⟨347648, by rfl⟩ : syracuseStep 463531 = 695297) B695297
theorem B463543 : Blo 459783 463543 := bstep (se 1 (by rfl) ⟨347657, by rfl⟩ : syracuseStep 463543 = 695315) B695315
theorem B692939 : Blo 459783 692939 := bstep (se 1 (by rfl) ⟨519704, by rfl⟩ : syracuseStep 692939 = 1039409) B1039409
theorem B463563 : Blo 459783 463563 := bstep (se 1 (by rfl) ⟨347672, by rfl⟩ : syracuseStep 463563 = 695345) B695345
theorem B692951 : Blo 459783 692951 := bstep (se 1 (by rfl) ⟨519713, by rfl⟩ : syracuseStep 692951 = 1039427) B1039427
theorem B463575 : Blo 459783 463575 := bstep (se 1 (by rfl) ⟨347681, by rfl⟩ : syracuseStep 463575 = 695363) B695363
theorem B463595 : Blo 459783 463595 := bstep (se 1 (by rfl) ⟨347696, by rfl⟩ : syracuseStep 463595 = 695393) B695393
theorem B463607 : Blo 459783 463607 := bstep (se 1 (by rfl) ⟨347705, by rfl⟩ : syracuseStep 463607 = 695411) B695411
theorem B463627 : Blo 459783 463627 := bstep (se 1 (by rfl) ⟨347720, by rfl⟩ : syracuseStep 463627 = 695441) B695441
theorem B463639 : Blo 459783 463639 := bstep (se 1 (by rfl) ⟨347729, by rfl⟩ : syracuseStep 463639 = 695459) B695459
theorem B693017 : Blo 459783 693017 := bstep (se 2 (by rfl) ⟨259881, by rfl⟩ : syracuseStep 693017 = 519763) B519763
theorem B463659 : Blo 459783 463659 := bstep (se 1 (by rfl) ⟨347744, by rfl⟩ : syracuseStep 463659 = 695489) B695489
theorem B463671 : Blo 459783 463671 := bstep (se 1 (by rfl) ⟨347753, by rfl⟩ : syracuseStep 463671 = 695507) B695507
theorem B463691 : Blo 459783 463691 := bstep (se 1 (by rfl) ⟨347768, by rfl⟩ : syracuseStep 463691 = 695537) B695537
theorem B463703 : Blo 459783 463703 := bstep (se 1 (by rfl) ⟨347777, by rfl⟩ : syracuseStep 463703 = 695555) B695555
theorem B463723 : Blo 459783 463723 := bstep (se 1 (by rfl) ⟨347792, by rfl⟩ : syracuseStep 463723 = 695585) B695585
theorem B463735 : Blo 459783 463735 := bstep (se 1 (by rfl) ⟨347801, by rfl⟩ : syracuseStep 463735 = 695603) B695603
theorem B693131 : Blo 459783 693131 := bstep (se 1 (by rfl) ⟨519848, by rfl⟩ : syracuseStep 693131 = 1039697) B1039697
theorem B463755 : Blo 459783 463755 := bstep (se 1 (by rfl) ⟨347816, by rfl⟩ : syracuseStep 463755 = 695633) B695633
theorem B693143 : Blo 459783 693143 := bstep (se 1 (by rfl) ⟨519857, by rfl⟩ : syracuseStep 693143 = 1039715) B1039715
theorem B463767 : Blo 459783 463767 := bstep (se 1 (by rfl) ⟨347825, by rfl⟩ : syracuseStep 463767 = 695651) B695651
theorem B1315777 : Blo 459783 1315777 := bstep (se 2 (by rfl) ⟨493416, by rfl⟩ : syracuseStep 1315777 = 986833) B986833
theorem B693209 : Blo 459783 693209 := bstep (se 2 (by rfl) ⟨259953, by rfl⟩ : syracuseStep 693209 = 519907) B519907
theorem B2331665 : Blo 459783 2331665 := bstep (se 2 (by rfl) ⟨874374, by rfl⟩ : syracuseStep 2331665 = 1748749) B1748749
theorem B693323 : Blo 459783 693323 := bstep (se 1 (by rfl) ⟨519992, by rfl⟩ : syracuseStep 693323 = 1039985) B1039985
theorem B693335 : Blo 459783 693335 := bstep (se 1 (by rfl) ⟨520001, by rfl⟩ : syracuseStep 693335 = 1040003) B1040003
theorem B693401 : Blo 459783 693401 := bstep (se 2 (by rfl) ⟨260025, by rfl⟩ : syracuseStep 693401 = 520051) B520051
theorem B2331827 : Blo 459783 2331827 := bstep (se 1 (by rfl) ⟨1748870, by rfl⟩ : syracuseStep 2331827 = 3497741) B3497741
theorem B693515 : Blo 459783 693515 := bstep (se 1 (by rfl) ⟨520136, by rfl⟩ : syracuseStep 693515 = 1040273) B1040273
theorem B1971479 : Blo 459783 1971479 := bstep (se 1 (by rfl) ⟨1478609, by rfl⟩ : syracuseStep 1971479 = 2957219) B2957219
theorem B693527 : Blo 459783 693527 := bstep (se 1 (by rfl) ⟨520145, by rfl⟩ : syracuseStep 693527 = 1040291) B1040291
theorem B693593 : Blo 459783 693593 := bstep (se 2 (by rfl) ⟨260097, by rfl⟩ : syracuseStep 693593 = 520195) B520195
theorem B693707 : Blo 459783 693707 := bstep (se 1 (by rfl) ⟨520280, by rfl⟩ : syracuseStep 693707 = 1040561) B1040561
theorem B693719 : Blo 459783 693719 := bstep (se 1 (by rfl) ⟨520289, by rfl⟩ : syracuseStep 693719 = 1040579) B1040579
theorem B693785 : Blo 459783 693785 := bstep (se 2 (by rfl) ⟨260169, by rfl⟩ : syracuseStep 693785 = 520339) B520339
theorem B693899 : Blo 459783 693899 := bstep (se 1 (by rfl) ⟨520424, by rfl⟩ : syracuseStep 693899 = 1040849) B1040849
theorem B693911 : Blo 459783 693911 := bstep (se 1 (by rfl) ⟨520433, by rfl⟩ : syracuseStep 693911 = 1040867) B1040867
theorem B2102987 : Blo 459783 2102987 := bstep (se 1 (by rfl) ⟨1577240, by rfl⟩ : syracuseStep 2102987 = 3154481) B3154481
theorem B1775321 : Blo 459783 1775321 := bstep (se 2 (by rfl) ⟨665745, by rfl⟩ : syracuseStep 1775321 = 1331491) B1331491
theorem B693977 : Blo 459783 693977 := bstep (se 2 (by rfl) ⟨260241, by rfl⟩ : syracuseStep 693977 = 520483) B520483
theorem B694091 : Blo 459783 694091 := bstep (se 1 (by rfl) ⟨520568, by rfl⟩ : syracuseStep 694091 = 1041137) B1041137
theorem B989003 : Blo 459783 989003 := bstep (se 1 (by rfl) ⟨741752, by rfl⟩ : syracuseStep 989003 = 1483505) B1483505
theorem B694103 : Blo 459783 694103 := bstep (se 1 (by rfl) ⟨520577, by rfl⟩ : syracuseStep 694103 = 1041155) B1041155
theorem B694169 : Blo 459783 694169 := bstep (se 2 (by rfl) ⟨260313, by rfl⟩ : syracuseStep 694169 = 520627) B520627
theorem B694283 : Blo 459783 694283 := bstep (se 1 (by rfl) ⟨520712, by rfl⟩ : syracuseStep 694283 = 1041425) B1041425
theorem B694295 : Blo 459783 694295 := bstep (se 1 (by rfl) ⟨520721, by rfl⟩ : syracuseStep 694295 = 1041443) B1041443
theorem B694361 : Blo 459783 694361 := bstep (se 2 (by rfl) ⟨260385, by rfl⟩ : syracuseStep 694361 = 520771) B520771
theorem B3545189 : Blo 459783 3545189 := bstep (se 4 (by rfl) ⟨332361, by rfl⟩ : syracuseStep 3545189 = 664723) B664723
theorem B694475 : Blo 459783 694475 := bstep (se 1 (by rfl) ⟨520856, by rfl⟩ : syracuseStep 694475 = 1041713) B1041713
theorem B694487 : Blo 459783 694487 := bstep (se 1 (by rfl) ⟨520865, by rfl⟩ : syracuseStep 694487 = 1041731) B1041731
theorem B694553 : Blo 459783 694553 := bstep (se 2 (by rfl) ⟨260457, by rfl⟩ : syracuseStep 694553 = 520915) B520915
theorem B694667 : Blo 459783 694667 := bstep (se 1 (by rfl) ⟨521000, by rfl⟩ : syracuseStep 694667 = 1042001) B1042001
theorem B694679 : Blo 459783 694679 := bstep (se 1 (by rfl) ⟨521009, by rfl⟩ : syracuseStep 694679 = 1042019) B1042019
theorem B694745 : Blo 459783 694745 := bstep (se 2 (by rfl) ⟨260529, by rfl⟩ : syracuseStep 694745 = 521059) B521059
theorem B1972811 : Blo 459783 1972811 := bstep (se 1 (by rfl) ⟨1479608, by rfl⟩ : syracuseStep 1972811 = 2959217) B2959217
theorem B694859 : Blo 459783 694859 := bstep (se 1 (by rfl) ⟨521144, by rfl⟩ : syracuseStep 694859 = 1042289) B1042289
theorem B694871 : Blo 459783 694871 := bstep (se 1 (by rfl) ⟨521153, by rfl⟩ : syracuseStep 694871 = 1042307) B1042307
theorem B2628227 : Blo 459783 2628227 := bstep (se 1 (by rfl) ⟨1971170, by rfl⟩ : syracuseStep 2628227 = 3942341) B3942341
theorem B694937 : Blo 459783 694937 := bstep (se 2 (by rfl) ⟨260601, by rfl⟩ : syracuseStep 694937 = 521203) B521203
theorem B695051 : Blo 459783 695051 := bstep (se 1 (by rfl) ⟨521288, by rfl⟩ : syracuseStep 695051 = 1042577) B1042577
theorem B695063 : Blo 459783 695063 := bstep (se 1 (by rfl) ⟨521297, by rfl⟩ : syracuseStep 695063 = 1042595) B1042595
theorem B989977 : Blo 459783 989977 := bstep (se 2 (by rfl) ⟨371241, by rfl⟩ : syracuseStep 989977 = 742483) B742483
theorem B695129 : Blo 459783 695129 := bstep (se 2 (by rfl) ⟨260673, by rfl⟩ : syracuseStep 695129 = 521347) B521347
theorem B2104157 : Blo 459783 2104157 := bstep (se 3 (by rfl) ⟨394529, by rfl⟩ : syracuseStep 2104157 = 789059) B789059
theorem B1973143 : Blo 459783 1973143 := bstep (se 1 (by rfl) ⟨1479857, by rfl⟩ : syracuseStep 1973143 = 2959715) B2959715
theorem B695243 : Blo 459783 695243 := bstep (se 1 (by rfl) ⟨521432, by rfl⟩ : syracuseStep 695243 = 1042865) B1042865
theorem B3513293 : Blo 459783 3513293 := bstep (se 3 (by rfl) ⟨658742, by rfl⟩ : syracuseStep 3513293 = 1317485) B1317485
theorem B695255 : Blo 459783 695255 := bstep (se 1 (by rfl) ⟨521441, by rfl⟩ : syracuseStep 695255 = 1042883) B1042883
theorem B1252313 : Blo 459783 1252313 := bstep (se 2 (by rfl) ⟨469617, by rfl⟩ : syracuseStep 1252313 = 939235) B939235
theorem B695321 : Blo 459783 695321 := bstep (se 2 (by rfl) ⟨260745, by rfl⟩ : syracuseStep 695321 = 521491) B521491
theorem B990233 : Blo 459783 990233 := bstep (se 2 (by rfl) ⟨371337, by rfl⟩ : syracuseStep 990233 = 742675) B742675
theorem B2333771 : Blo 459783 2333771 := bstep (se 1 (by rfl) ⟨1750328, by rfl⟩ : syracuseStep 2333771 = 3500657) B3500657
theorem B2628683 : Blo 459783 2628683 := bstep (se 1 (by rfl) ⟨1971512, by rfl⟩ : syracuseStep 2628683 = 3943025) B3943025
theorem B1055873 : Blo 459783 1055873 := bstep (se 2 (by rfl) ⟨395952, by rfl⟩ : syracuseStep 1055873 = 791905) B791905
theorem B695435 : Blo 459783 695435 := bstep (se 1 (by rfl) ⟨521576, by rfl⟩ : syracuseStep 695435 = 1043153) B1043153
theorem B1973393 : Blo 459783 1973393 := bstep (se 2 (by rfl) ⟨740022, by rfl⟩ : syracuseStep 1973393 = 1480045) B1480045
theorem B695447 : Blo 459783 695447 := bstep (se 1 (by rfl) ⟨521585, by rfl⟩ : syracuseStep 695447 = 1043171) B1043171
theorem B695513 : Blo 459783 695513 := bstep (se 2 (by rfl) ⟨260817, by rfl⟩ : syracuseStep 695513 = 521635) B521635
theorem B1056001 : Blo 459783 1056001 := bstep (se 2 (by rfl) ⟨396000, by rfl⟩ : syracuseStep 1056001 = 792001) B792001
theorem B695627 : Blo 459783 695627 := bstep (se 1 (by rfl) ⟨521720, by rfl⟩ : syracuseStep 695627 = 1043441) B1043441
theorem B695639 : Blo 459783 695639 := bstep (se 1 (by rfl) ⟨521729, by rfl⟩ : syracuseStep 695639 = 1043459) B1043459
theorem B3939677 : Blo 459783 3939677 := bstep (se 3 (by rfl) ⟨738689, by rfl⟩ : syracuseStep 3939677 = 1477379) B1477379
theorem B1318295 : Blo 459783 1318295 := bstep (se 1 (by rfl) ⟨988721, by rfl⟩ : syracuseStep 1318295 = 1977443) B1977443
theorem B3513779 : Blo 459783 3513779 := bstep (se 1 (by rfl) ⟨2635334, by rfl⟩ : syracuseStep 3513779 = 5270669) B5270669
theorem B1056203 : Blo 459783 1056203 := bstep (se 1 (by rfl) ⟨792152, by rfl⟩ : syracuseStep 1056203 = 1584305) B1584305
theorem B1875421 : Blo 459783 1875421 := bstep (se 3 (by rfl) ⟨351641, by rfl⟩ : syracuseStep 1875421 = 703283) B703283
theorem B1482263 : Blo 459783 1482263 := bstep (se 1 (by rfl) ⟨1111697, by rfl⟩ : syracuseStep 1482263 = 2223395) B2223395
theorem B4431833 : Blo 459783 4431833 := bstep (se 2 (by rfl) ⟨1661937, by rfl⟩ : syracuseStep 4431833 = 3323875) B3323875
theorem B3940427 : Blo 459783 3940427 := bstep (se 1 (by rfl) ⟨2955320, by rfl⟩ : syracuseStep 3940427 = 5910641) B5910641
theorem B1974451 : Blo 459783 1974451 := bstep (se 1 (by rfl) ⟨1480838, by rfl⟩ : syracuseStep 1974451 = 2961677) B2961677
theorem B2105689 : Blo 459783 2105689 := bstep (se 2 (by rfl) ⟨789633, by rfl⟩ : syracuseStep 2105689 = 1579267) B1579267
theorem B5251715 : Blo 459783 5251715 := bstep (se 1 (by rfl) ⟨3938786, by rfl⟩ : syracuseStep 5251715 = 7877573) B7877573
theorem B1319627 : Blo 459783 1319627 := bstep (se 1 (by rfl) ⟨989720, by rfl⟩ : syracuseStep 1319627 = 1979441) B1979441
theorem B2335553 : Blo 459783 2335553 := bstep (se 2 (by rfl) ⟨875832, by rfl⟩ : syracuseStep 2335553 = 1751665) B1751665
theorem B3515237 : Blo 459783 3515237 := bstep (se 4 (by rfl) ⟨329553, by rfl⟩ : syracuseStep 3515237 = 659107) B659107
theorem B1746137 : Blo 459783 1746137 := bstep (se 2 (by rfl) ⟨654801, by rfl⟩ : syracuseStep 1746137 = 1309603) B1309603
theorem B3515723 : Blo 459783 3515723 := bstep (se 1 (by rfl) ⟨2636792, by rfl⟩ : syracuseStep 3515723 = 5273585) B5273585
theorem B1975853 : Blo 459783 1975853 := bstep (se 3 (by rfl) ⟨370472, by rfl⟩ : syracuseStep 1975853 = 740945) B740945
theorem B1681075 : Blo 459783 1681075 := bstep (se 1 (by rfl) ⟨1260806, by rfl⟩ : syracuseStep 1681075 = 2521613) B2521613
theorem B3942067 : Blo 459783 3942067 := bstep (se 1 (by rfl) ⟨2956550, by rfl⟩ : syracuseStep 3942067 = 5913101) B5913101
theorem B1484723 : Blo 459783 1484723 := bstep (se 1 (by rfl) ⟨1113542, by rfl⟩ : syracuseStep 1484723 = 2227085) B2227085
theorem B1583425 : Blo 459783 1583425 := bstep (se 2 (by rfl) ⟨593784, by rfl⟩ : syracuseStep 1583425 = 1187569) B1187569
theorem B928279 : Blo 459783 928279 := bstep (se 1 (by rfl) ⟨696209, by rfl⟩ : syracuseStep 928279 = 1392419) B1392419
theorem B2402891 : Blo 459783 2402891 := bstep (se 1 (by rfl) ⟨1802168, by rfl⟩ : syracuseStep 2402891 = 3604337) B3604337
theorem B2337497 : Blo 459783 2337497 := bstep (se 2 (by rfl) ⟨876561, by rfl⟩ : syracuseStep 2337497 = 1753123) B1753123
theorem B1747763 : Blo 459783 1747763 := bstep (se 1 (by rfl) ⟨1310822, by rfl⟩ : syracuseStep 1747763 = 2621645) B2621645
theorem B1747777 : Blo 459783 1747777 := bstep (se 2 (by rfl) ⟨655416, by rfl⟩ : syracuseStep 1747777 = 1310833) B1310833
theorem B830579 : Blo 459783 830579 := bstep (se 1 (by rfl) ⟨622934, by rfl⟩ : syracuseStep 830579 = 1245869) B1245869
theorem B2666029 : Blo 459783 2666029 := bstep (se 3 (by rfl) ⟨499880, by rfl⟩ : syracuseStep 2666029 = 999761) B999761
theorem B2633309 : Blo 459783 2633309 := bstep (se 3 (by rfl) ⟨493745, by rfl⟩ : syracuseStep 2633309 = 987491) B987491
theorem B831127 : Blo 459783 831127 := bstep (se 1 (by rfl) ⟨623345, by rfl⟩ : syracuseStep 831127 = 1246691) B1246691
theorem B831755 : Blo 459783 831755 := bstep (se 1 (by rfl) ⟨623816, by rfl⟩ : syracuseStep 831755 = 1247633) B1247633
theorem B2339117 : Blo 459783 2339117 := bstep (se 3 (by rfl) ⟨438584, by rfl⟩ : syracuseStep 2339117 = 877169) B877169
theorem B1552715 : Blo 459783 1552715 := bstep (se 1 (by rfl) ⟨1164536, by rfl⟩ : syracuseStep 1552715 = 2329073) B2329073
theorem B2634059 : Blo 459783 2634059 := bstep (se 1 (by rfl) ⟨1975544, by rfl⟩ : syracuseStep 2634059 = 3951089) B3951089
theorem B2240947 : Blo 459783 2240947 := bstep (se 1 (by rfl) ⟨1680710, by rfl⟩ : syracuseStep 2240947 = 3361421) B3361421
theorem B1552985 : Blo 459783 1552985 := bstep (se 2 (by rfl) ⟨582369, by rfl⟩ : syracuseStep 1552985 = 1164739) B1164739
theorem B1749707 : Blo 459783 1749707 := bstep (se 1 (by rfl) ⟨1312280, by rfl⟩ : syracuseStep 1749707 = 2624561) B2624561
theorem B1749721 : Blo 459783 1749721 := bstep (se 2 (by rfl) ⟨656145, by rfl⟩ : syracuseStep 1749721 = 1312291) B1312291
theorem B1553687 : Blo 459783 1553687 := bstep (se 1 (by rfl) ⟨1165265, by rfl⟩ : syracuseStep 1553687 = 2330531) B2330531
theorem B3421505 : Blo 459783 3421505 := bstep (se 2 (by rfl) ⟨1283064, by rfl⟩ : syracuseStep 3421505 = 2566129) B2566129
theorem B1750679 : Blo 459783 1750679 := bstep (se 1 (by rfl) ⟨1313009, by rfl⟩ : syracuseStep 1750679 = 2626019) B2626019
theorem B1980055 : Blo 459783 1980055 := bstep (se 1 (by rfl) ⟨1485041, by rfl⟩ : syracuseStep 1980055 = 2970083) B2970083
theorem B833203 : Blo 459783 833203 := bstep (se 1 (by rfl) ⟨624902, by rfl⟩ : syracuseStep 833203 = 1249805) B1249805
theorem B1980125 : Blo 459783 1980125 := bstep (se 3 (by rfl) ⟨371273, by rfl⟩ : syracuseStep 1980125 = 742547) B742547
theorem B1554227 : Blo 459783 1554227 := bstep (se 1 (by rfl) ⟨1165670, by rfl⟩ : syracuseStep 1554227 = 2331341) B2331341
theorem B702359 : Blo 459783 702359 := bstep (se 1 (by rfl) ⟨526769, by rfl⟩ : syracuseStep 702359 = 1053539) B1053539
theorem B2635699 : Blo 459783 2635699 := bstep (se 1 (by rfl) ⟨1976774, by rfl⟩ : syracuseStep 2635699 = 3953549) B3953549
theorem B3094451 : Blo 459783 3094451 := bstep (se 1 (by rfl) ⟨2320838, by rfl⟩ : syracuseStep 3094451 = 4641677) B4641677
theorem B1554497 : Blo 459783 1554497 := bstep (se 2 (by rfl) ⟨582936, by rfl⟩ : syracuseStep 1554497 = 1165873) B1165873
theorem B702553 : Blo 459783 702553 := bstep (se 2 (by rfl) ⟨263457, by rfl⟩ : syracuseStep 702553 = 526915) B526915
theorem B833665 : Blo 459783 833665 := bstep (se 2 (by rfl) ⟨312624, by rfl⟩ : syracuseStep 833665 = 625249) B625249
theorem B8010161 : Blo 459783 8010161 := bstep (se 2 (by rfl) ⟨3003810, by rfl⟩ : syracuseStep 8010161 = 6007621) B6007621
theorem B1980875 : Blo 459783 1980875 := bstep (se 1 (by rfl) ⟨1485656, by rfl⟩ : syracuseStep 1980875 = 2971313) B2971313
theorem B3521069 : Blo 459783 3521069 := bstep (se 3 (by rfl) ⟨660200, by rfl⟩ : syracuseStep 3521069 = 1320401) B1320401
theorem B1555037 : Blo 459783 1555037 := bstep (se 3 (by rfl) ⟨291569, by rfl⟩ : syracuseStep 1555037 = 583139) B583139
theorem B7486307 : Blo 459783 7486307 := bstep (se 1 (by rfl) ⟨5614730, by rfl⟩ : syracuseStep 7486307 = 11229461) B11229461
theorem B1751939 : Blo 459783 1751939 := bstep (se 1 (by rfl) ⟨1313954, by rfl⟩ : syracuseStep 1751939 = 2627909) B2627909
theorem B30293027 : Blo 459783 30293027 := bstep (se 1 (by rfl) ⟨22719770, by rfl⟩ : syracuseStep 30293027 = 45439541) B45439541
theorem B2112733 : Blo 459783 2112733 := bstep (se 3 (by rfl) ⟨396137, by rfl⟩ : syracuseStep 2112733 = 792275) B792275
theorem B1064215 : Blo 459783 1064215 := bstep (se 1 (by rfl) ⟨798161, by rfl⟩ : syracuseStep 1064215 = 1596323) B1596323
theorem B703819 : Blo 459783 703819 := bstep (se 1 (by rfl) ⟨527864, by rfl⟩ : syracuseStep 703819 = 1055729) B1055729
theorem B2637157 : Blo 459783 2637157 := bstep (se 4 (by rfl) ⟨247233, by rfl⟩ : syracuseStep 2637157 = 494467) B494467
theorem B12041621 : Blo 459783 12041621 := bstep (se 6 (by rfl) ⟨282225, by rfl⟩ : syracuseStep 12041621 = 564451) B564451
theorem B2539025 : Blo 459783 2539025 := bstep (se 2 (by rfl) ⟨952134, by rfl⟩ : syracuseStep 2539025 = 1904269) B1904269
theorem B1556171 : Blo 459783 1556171 := bstep (se 1 (by rfl) ⟨1167128, by rfl⟩ : syracuseStep 1556171 = 2334257) B2334257
theorem B736985 : Blo 459783 736985 := bstep (se 2 (by rfl) ⟨276369, by rfl⟩ : syracuseStep 736985 = 552739) B552739
theorem B933655 : Blo 459783 933655 := bstep (se 1 (by rfl) ⟨700241, by rfl⟩ : syracuseStep 933655 = 1400483) B1400483
theorem B1556441 : Blo 459783 1556441 := bstep (se 2 (by rfl) ⟨583665, by rfl⟩ : syracuseStep 1556441 = 1167331) B1167331
theorem B2343005 : Blo 459783 2343005 := bstep (se 3 (by rfl) ⟨439313, by rfl⟩ : syracuseStep 2343005 = 878627) B878627
theorem B7487923 : Blo 459783 7487923 := bstep (se 1 (by rfl) ⟨5615942, by rfl⟩ : syracuseStep 7487923 = 11231885) B11231885
theorem B1557143 : Blo 459783 1557143 := bstep (se 1 (by rfl) ⟨1167857, by rfl⟩ : syracuseStep 1557143 = 2335715) B2335715
theorem B3556057 : Blo 459783 3556057 := bstep (se 2 (by rfl) ⟨1333521, by rfl⟩ : syracuseStep 3556057 = 2667043) B2667043
theorem B1557683 : Blo 459783 1557683 := bstep (se 1 (by rfl) ⟨1168262, by rfl⟩ : syracuseStep 1557683 = 2336525) B2336525
theorem B1262999 : Blo 459783 1262999 := bstep (se 1 (by rfl) ⟨947249, by rfl⟩ : syracuseStep 1262999 = 1894499) B1894499
theorem B1557953 : Blo 459783 1557953 := bstep (se 2 (by rfl) ⟨584232, by rfl⟩ : syracuseStep 1557953 = 1168465) B1168465
theorem B1164851 : Blo 459783 1164851 := bstep (se 1 (by rfl) ⟨873638, by rfl⟩ : syracuseStep 1164851 = 1747277) B1747277
theorem B2967191 : Blo 459783 2967191 := bstep (se 1 (by rfl) ⟨2225393, by rfl⟩ : syracuseStep 2967191 = 4450787) B4450787
theorem B2377603 : Blo 459783 2377603 := bstep (se 1 (by rfl) ⟨1783202, by rfl⟩ : syracuseStep 2377603 = 3566405) B3566405
theorem B1755053 : Blo 459783 1755053 := bstep (se 3 (by rfl) ⟨329072, by rfl⟩ : syracuseStep 1755053 = 658145) B658145
theorem B4507571 : Blo 459783 4507571 := bstep (se 1 (by rfl) ⟨3380678, by rfl⟩ : syracuseStep 4507571 = 6761357) B6761357
theorem B1558493 : Blo 459783 1558493 := bstep (se 3 (by rfl) ⟨292217, by rfl⟩ : syracuseStep 1558493 = 584435) B584435
theorem B1001459 : Blo 459783 1001459 := bstep (se 1 (by rfl) ⟨751094, by rfl⟩ : syracuseStep 1001459 = 1502189) B1502189
theorem B1165387 : Blo 459783 1165387 := bstep (se 1 (by rfl) ⟨874040, by rfl⟩ : syracuseStep 1165387 = 1748081) B1748081
theorem B2345111 : Blo 459783 2345111 := bstep (se 1 (by rfl) ⟨1758833, by rfl⟩ : syracuseStep 2345111 = 3517667) B3517667
theorem B1165529 : Blo 459783 1165529 := bstep (se 2 (by rfl) ⟨437073, by rfl⟩ : syracuseStep 1165529 = 874147) B874147
theorem B1034585 : Blo 459783 1034585 := bstep (se 2 (by rfl) ⟨387969, by rfl⟩ : syracuseStep 1034585 = 775939) B775939
theorem B1034675 : Blo 459783 1034675 := bstep (se 1 (by rfl) ⟨776006, by rfl⟩ : syracuseStep 1034675 = 1552013) B1552013
theorem B2214323 : Blo 459783 2214323 := bstep (se 1 (by rfl) ⟨1660742, by rfl⟩ : syracuseStep 2214323 = 3321485) B3321485
theorem B2443699 : Blo 459783 2443699 := bstep (se 1 (by rfl) ⟨1832774, by rfl⟩ : syracuseStep 2443699 = 3665549) B3665549
theorem B1034711 : Blo 459783 1034711 := bstep (se 1 (by rfl) ⟨776033, by rfl⟩ : syracuseStep 1034711 = 1552067) B1552067
theorem B1034891 : Blo 459783 1034891 := bstep (se 1 (by rfl) ⟨776168, by rfl⟩ : syracuseStep 1034891 = 1552337) B1552337
theorem B1755827 : Blo 459783 1755827 := bstep (se 1 (by rfl) ⟨1316870, by rfl⟩ : syracuseStep 1755827 = 2633741) B2633741
theorem B1034945 : Blo 459783 1034945 := bstep (se 2 (by rfl) ⟨388104, by rfl⟩ : syracuseStep 1034945 = 776209) B776209
theorem B936769 : Blo 459783 936769 := bstep (se 2 (by rfl) ⟨351288, by rfl⟩ : syracuseStep 936769 = 702577) B702577
theorem B3164993 : Blo 459783 3164993 := bstep (se 2 (by rfl) ⟨1186872, by rfl⟩ : syracuseStep 3164993 = 2373745) B2373745
theorem B1035161 : Blo 459783 1035161 := bstep (se 2 (by rfl) ⟨388185, by rfl⟩ : syracuseStep 1035161 = 776371) B776371
theorem B1035251 : Blo 459783 1035251 := bstep (se 1 (by rfl) ⟨776438, by rfl⟩ : syracuseStep 1035251 = 1552877) B1552877
theorem B3492881 : Blo 459783 3492881 := bstep (se 2 (by rfl) ⟨1309830, by rfl⟩ : syracuseStep 3492881 = 2619661) B2619661
theorem B1035287 : Blo 459783 1035287 := bstep (se 1 (by rfl) ⟨776465, by rfl⟩ : syracuseStep 1035287 = 1552931) B1552931
theorem B1166359 : Blo 459783 1166359 := bstep (se 1 (by rfl) ⟨874769, by rfl⟩ : syracuseStep 1166359 = 1749539) B1749539
theorem B1657901 : Blo 459783 1657901 := bstep (se 3 (by rfl) ⟨310856, by rfl⟩ : syracuseStep 1657901 = 621713) B621713
theorem B1559627 : Blo 459783 1559627 := bstep (se 1 (by rfl) ⟨1169720, by rfl⟩ : syracuseStep 1559627 = 2339441) B2339441
theorem B1035467 : Blo 459783 1035467 := bstep (se 1 (by rfl) ⟨776600, by rfl⟩ : syracuseStep 1035467 = 1553201) B1553201
theorem B1035521 : Blo 459783 1035521 := bstep (se 2 (by rfl) ⟨388320, by rfl⟩ : syracuseStep 1035521 = 776641) B776641
theorem B4443437 : Blo 459783 4443437 := bstep (se 3 (by rfl) ⟨833144, by rfl⟩ : syracuseStep 4443437 = 1666289) B1666289
theorem B1559897 : Blo 459783 1559897 := bstep (se 2 (by rfl) ⟨584961, by rfl⟩ : syracuseStep 1559897 = 1169923) B1169923
theorem B1166795 : Blo 459783 1166795 := bstep (se 1 (by rfl) ⟨875096, by rfl⟩ : syracuseStep 1166795 = 1750193) B1750193
theorem B1035737 : Blo 459783 1035737 := bstep (se 2 (by rfl) ⟨388401, by rfl⟩ : syracuseStep 1035737 = 776803) B776803
theorem B1035827 : Blo 459783 1035827 := bstep (se 1 (by rfl) ⟨776870, by rfl⟩ : syracuseStep 1035827 = 1553741) B1553741
theorem B1035863 : Blo 459783 1035863 := bstep (se 1 (by rfl) ⟨776897, by rfl⟩ : syracuseStep 1035863 = 1553795) B1553795
theorem B1036043 : Blo 459783 1036043 := bstep (se 1 (by rfl) ⟨777032, by rfl⟩ : syracuseStep 1036043 = 1554065) B1554065
theorem B1036097 : Blo 459783 1036097 := bstep (se 2 (by rfl) ⟨388536, by rfl⟩ : syracuseStep 1036097 = 777073) B777073
theorem B1167169 : Blo 459783 1167169 := bstep (se 2 (by rfl) ⟨437688, by rfl⟩ : syracuseStep 1167169 = 875377) B875377
theorem B2805635 : Blo 459783 2805635 := bstep (se 1 (by rfl) ⟨2104226, by rfl⟩ : syracuseStep 2805635 = 4208453) B4208453
theorem B1200023 : Blo 459783 1200023 := bstep (se 1 (by rfl) ⟨900017, by rfl⟩ : syracuseStep 1200023 = 1800035) B1800035
theorem B1560599 : Blo 459783 1560599 := bstep (se 1 (by rfl) ⟨1170449, by rfl⟩ : syracuseStep 1560599 = 2340899) B2340899
theorem B1036313 : Blo 459783 1036313 := bstep (se 2 (by rfl) ⟨388617, by rfl⟩ : syracuseStep 1036313 = 777235) B777235
theorem B13455395 : Blo 459783 13455395 := bstep (se 1 (by rfl) ⟨10091546, by rfl⟩ : syracuseStep 13455395 = 20183093) B20183093
theorem B1036403 : Blo 459783 1036403 := bstep (se 1 (by rfl) ⟨777302, by rfl⟩ : syracuseStep 1036403 = 1554605) B1554605
theorem B1757315 : Blo 459783 1757315 := bstep (se 1 (by rfl) ⟨1317986, by rfl⟩ : syracuseStep 1757315 = 2635973) B2635973
theorem B1036439 : Blo 459783 1036439 := bstep (se 1 (by rfl) ⟨777329, by rfl⟩ : syracuseStep 1036439 = 1554659) B1554659
theorem B1036619 : Blo 459783 1036619 := bstep (se 1 (by rfl) ⟨777464, by rfl⟩ : syracuseStep 1036619 = 1554929) B1554929
theorem B1495385 : Blo 459783 1495385 := bstep (se 2 (by rfl) ⟨560769, by rfl⟩ : syracuseStep 1495385 = 1121539) B1121539
theorem B1036673 : Blo 459783 1036673 := bstep (se 2 (by rfl) ⟨388752, by rfl⟩ : syracuseStep 1036673 = 777505) B777505
theorem B1167767 : Blo 459783 1167767 := bstep (se 1 (by rfl) ⟨875825, by rfl⟩ : syracuseStep 1167767 = 1751651) B1751651
theorem B872947 : Blo 459783 872947 := bstep (se 1 (by rfl) ⟨654710, by rfl⟩ : syracuseStep 872947 = 1309421) B1309421
theorem B1561139 : Blo 459783 1561139 := bstep (se 1 (by rfl) ⟨1170854, by rfl⟩ : syracuseStep 1561139 = 2341709) B2341709
theorem B1757771 : Blo 459783 1757771 := bstep (se 1 (by rfl) ⟨1318328, by rfl⟩ : syracuseStep 1757771 = 2636657) B2636657
theorem B1036889 : Blo 459783 1036889 := bstep (se 2 (by rfl) ⟨388833, by rfl⟩ : syracuseStep 1036889 = 777667) B777667
theorem B1659485 : Blo 459783 1659485 := bstep (se 3 (by rfl) ⟨311153, by rfl⟩ : syracuseStep 1659485 = 622307) B622307
theorem B1036979 : Blo 459783 1036979 := bstep (se 1 (by rfl) ⟨777734, by rfl⟩ : syracuseStep 1036979 = 1555469) B1555469
theorem B873175 : Blo 459783 873175 := bstep (se 1 (by rfl) ⟨654881, by rfl⟩ : syracuseStep 873175 = 1309763) B1309763
theorem B1037015 : Blo 459783 1037015 := bstep (se 1 (by rfl) ⟨777761, by rfl⟩ : syracuseStep 1037015 = 1555523) B1555523
theorem B1757969 : Blo 459783 1757969 := bstep (se 2 (by rfl) ⟨659238, by rfl⟩ : syracuseStep 1757969 = 1318477) B1318477
theorem B873281 : Blo 459783 873281 := bstep (se 2 (by rfl) ⟨327480, by rfl⟩ : syracuseStep 873281 = 654961) B654961
theorem B1561409 : Blo 459783 1561409 := bstep (se 2 (by rfl) ⟨585528, by rfl⟩ : syracuseStep 1561409 = 1171057) B1171057
theorem B1037195 : Blo 459783 1037195 := bstep (se 1 (by rfl) ⟨777896, by rfl⟩ : syracuseStep 1037195 = 1555793) B1555793
theorem B1037249 : Blo 459783 1037249 := bstep (se 2 (by rfl) ⟨388968, by rfl⟩ : syracuseStep 1037249 = 777937) B777937
theorem B938945 : Blo 459783 938945 := bstep (se 2 (by rfl) ⟨352104, by rfl⟩ : syracuseStep 938945 = 704209) B704209
theorem B873433 : Blo 459783 873433 := bstep (se 2 (by rfl) ⟨327537, by rfl⟩ : syracuseStep 873433 = 655075) B655075
theorem B1037465 : Blo 459783 1037465 := bstep (se 2 (by rfl) ⟨389049, by rfl⟩ : syracuseStep 1037465 = 778099) B778099
theorem B1168577 : Blo 459783 1168577 := bstep (se 2 (by rfl) ⟨438216, by rfl⟩ : syracuseStep 1168577 = 876433) B876433
theorem B1037555 : Blo 459783 1037555 := bstep (se 1 (by rfl) ⟨778166, by rfl⟩ : syracuseStep 1037555 = 1556333) B1556333
theorem B1037591 : Blo 459783 1037591 := bstep (se 1 (by rfl) ⟨778193, by rfl⟩ : syracuseStep 1037591 = 1556387) B1556387
theorem B1561949 : Blo 459783 1561949 := bstep (se 3 (by rfl) ⟨292865, by rfl⟩ : syracuseStep 1561949 = 585731) B585731
theorem B1037771 : Blo 459783 1037771 := bstep (se 1 (by rfl) ⟨778328, by rfl⟩ : syracuseStep 1037771 = 1556657) B1556657
theorem B1037825 : Blo 459783 1037825 := bstep (se 2 (by rfl) ⟨389184, by rfl⟩ : syracuseStep 1037825 = 778369) B778369
theorem B1660439 : Blo 459783 1660439 := bstep (se 1 (by rfl) ⟨1245329, by rfl⟩ : syracuseStep 1660439 = 2490659) B2490659
theorem B1758743 : Blo 459783 1758743 := bstep (se 1 (by rfl) ⟨1319057, by rfl⟩ : syracuseStep 1758743 = 2638115) B2638115
theorem B1038041 : Blo 459783 1038041 := bstep (se 2 (by rfl) ⟨389265, by rfl⟩ : syracuseStep 1038041 = 778531) B778531
theorem B1169113 : Blo 459783 1169113 := bstep (se 2 (by rfl) ⟨438417, by rfl⟩ : syracuseStep 1169113 = 876835) B876835
theorem B1758941 : Blo 459783 1758941 := bstep (se 3 (by rfl) ⟨329801, by rfl⟩ : syracuseStep 1758941 = 659603) B659603
theorem B1038131 : Blo 459783 1038131 := bstep (se 1 (by rfl) ⟨778598, by rfl⟩ : syracuseStep 1038131 = 1557197) B1557197
theorem B939851 : Blo 459783 939851 := bstep (se 1 (by rfl) ⟨704888, by rfl⟩ : syracuseStep 939851 = 1409777) B1409777
theorem B1038167 : Blo 459783 1038167 := bstep (se 1 (by rfl) ⟨778625, by rfl⟩ : syracuseStep 1038167 = 1557251) B1557251
theorem B1038347 : Blo 459783 1038347 := bstep (se 1 (by rfl) ⟨778760, by rfl⟩ : syracuseStep 1038347 = 1557521) B1557521
theorem B1038401 : Blo 459783 1038401 := bstep (se 2 (by rfl) ⟨389400, by rfl⟩ : syracuseStep 1038401 = 778801) B778801
theorem B1398877 : Blo 459783 1398877 := bstep (se 3 (by rfl) ⟨262289, by rfl⟩ : syracuseStep 1398877 = 524579) B524579
theorem B874739 : Blo 459783 874739 := bstep (se 1 (by rfl) ⟨656054, by rfl⟩ : syracuseStep 874739 = 1312109) B1312109
theorem B776459 : Blo 459783 776459 := bstep (se 1 (by rfl) ⟨582344, by rfl⟩ : syracuseStep 776459 = 1164689) B1164689
theorem B1038617 : Blo 459783 1038617 := bstep (se 2 (by rfl) ⟨389481, by rfl⟩ : syracuseStep 1038617 = 778963) B778963
theorem B1038707 : Blo 459783 1038707 := bstep (se 1 (by rfl) ⟨779030, by rfl⟩ : syracuseStep 1038707 = 1558061) B1558061
theorem B776587 : Blo 459783 776587 := bstep (se 1 (by rfl) ⟨582440, by rfl⟩ : syracuseStep 776587 = 1164881) B1164881
theorem B874891 : Blo 459783 874891 := bstep (se 1 (by rfl) ⟨656168, by rfl⟩ : syracuseStep 874891 = 1312337) B1312337
theorem B1038743 : Blo 459783 1038743 := bstep (se 1 (by rfl) ⟨779057, by rfl⟩ : syracuseStep 1038743 = 1558115) B1558115
theorem B1563083 : Blo 459783 1563083 := bstep (se 1 (by rfl) ⟨1172312, by rfl⟩ : syracuseStep 1563083 = 2344625) B2344625
theorem B776729 : Blo 459783 776729 := bstep (se 2 (by rfl) ⟨291273, by rfl⟩ : syracuseStep 776729 = 582547) B582547
theorem B1038923 : Blo 459783 1038923 := bstep (se 1 (by rfl) ⟨779192, by rfl⟩ : syracuseStep 1038923 = 1558385) B1558385
theorem B1038977 : Blo 459783 1038977 := bstep (se 2 (by rfl) ⟨389616, by rfl⟩ : syracuseStep 1038977 = 779233) B779233
theorem B776857 : Blo 459783 776857 := bstep (se 2 (by rfl) ⟨291321, by rfl⟩ : syracuseStep 776857 = 582643) B582643
theorem B875225 : Blo 459783 875225 := bstep (se 2 (by rfl) ⟨328209, by rfl⟩ : syracuseStep 875225 = 656419) B656419
theorem B1563353 : Blo 459783 1563353 := bstep (se 2 (by rfl) ⟨586257, by rfl⟩ : syracuseStep 1563353 = 1172515) B1172515
theorem B1170227 : Blo 459783 1170227 := bstep (se 1 (by rfl) ⟨877670, by rfl⟩ : syracuseStep 1170227 = 1755341) B1755341
theorem B3496769 : Blo 459783 3496769 := bstep (se 2 (by rfl) ⟨1311288, by rfl⟩ : syracuseStep 3496769 = 2622577) B2622577
theorem B1039193 : Blo 459783 1039193 := bstep (se 2 (by rfl) ⟨389697, by rfl⟩ : syracuseStep 1039193 = 779395) B779395
theorem B1039283 : Blo 459783 1039283 := bstep (se 1 (by rfl) ⟨779462, by rfl⟩ : syracuseStep 1039283 = 1558925) B1558925
theorem B1039319 : Blo 459783 1039319 := bstep (se 1 (by rfl) ⟨779489, by rfl⟩ : syracuseStep 1039319 = 1558979) B1558979
theorem B1170521 : Blo 459783 1170521 := bstep (se 2 (by rfl) ⟨438945, by rfl⟩ : syracuseStep 1170521 = 877891) B877891
theorem B1039499 : Blo 459783 1039499 := bstep (se 1 (by rfl) ⟨779624, by rfl⟩ : syracuseStep 1039499 = 1559249) B1559249
theorem B1039553 : Blo 459783 1039553 := bstep (se 2 (by rfl) ⟨389832, by rfl⟩ : syracuseStep 1039553 = 779665) B779665
theorem B777431 : Blo 459783 777431 := bstep (se 1 (by rfl) ⟨583073, by rfl⟩ : syracuseStep 777431 = 1166147) B1166147
theorem B777559 : Blo 459783 777559 := bstep (se 1 (by rfl) ⟨583169, by rfl⟩ : syracuseStep 777559 = 1166339) B1166339
theorem B875863 : Blo 459783 875863 := bstep (se 1 (by rfl) ⟨656897, by rfl⟩ : syracuseStep 875863 = 1313795) B1313795
theorem B2219395 : Blo 459783 2219395 := bstep (se 1 (by rfl) ⟨1664546, by rfl⟩ : syracuseStep 2219395 = 3329093) B3329093
theorem B1564055 : Blo 459783 1564055 := bstep (se 1 (by rfl) ⟨1173041, by rfl⟩ : syracuseStep 1564055 = 2346083) B2346083
theorem B1039769 : Blo 459783 1039769 := bstep (se 2 (by rfl) ⟨389913, by rfl⟩ : syracuseStep 1039769 = 779827) B779827
theorem B3956147 : Blo 459783 3956147 := bstep (se 1 (by rfl) ⟨2967110, by rfl⟩ : syracuseStep 3956147 = 5934221) B5934221
theorem B3562957 : Blo 459783 3562957 := bstep (se 3 (by rfl) ⟨668054, by rfl⟩ : syracuseStep 3562957 = 1336109) B1336109
theorem B1039859 : Blo 459783 1039859 := bstep (se 1 (by rfl) ⟨779894, by rfl⟩ : syracuseStep 1039859 = 1559789) B1559789
theorem B3988997 : Blo 459783 3988997 := bstep (se 4 (by rfl) ⟨373968, by rfl⟩ : syracuseStep 3988997 = 747937) B747937
theorem B1039895 : Blo 459783 1039895 := bstep (se 1 (by rfl) ⟨779921, by rfl⟩ : syracuseStep 1039895 = 1559843) B1559843
theorem B1662515 : Blo 459783 1662515 := bstep (se 1 (by rfl) ⟨1246886, by rfl⟩ : syracuseStep 1662515 = 2493773) B2493773
theorem B3333707 : Blo 459783 3333707 := bstep (se 1 (by rfl) ⟨2500280, by rfl⟩ : syracuseStep 3333707 = 5000561) B5000561
theorem B1760899 : Blo 459783 1760899 := bstep (se 1 (by rfl) ⟨1320674, by rfl⟩ : syracuseStep 1760899 = 2641349) B2641349
theorem B1040075 : Blo 459783 1040075 := bstep (se 1 (by rfl) ⟨780056, by rfl⟩ : syracuseStep 1040075 = 1560113) B1560113
theorem B1040129 : Blo 459783 1040129 := bstep (se 2 (by rfl) ⟨390048, by rfl⟩ : syracuseStep 1040129 = 780097) B780097
theorem B3956525 : Blo 459783 3956525 := bstep (se 3 (by rfl) ⟨741848, by rfl⟩ : syracuseStep 3956525 = 1483697) B1483697
theorem B1564595 : Blo 459783 1564595 := bstep (se 1 (by rfl) ⟨1173446, by rfl⟩ : syracuseStep 1564595 = 2346893) B2346893
theorem B778187 : Blo 459783 778187 := bstep (se 1 (by rfl) ⟨583640, by rfl⟩ : syracuseStep 778187 = 1167281) B1167281
theorem B1040345 : Blo 459783 1040345 := bstep (se 2 (by rfl) ⟨390129, by rfl⟩ : syracuseStep 1040345 = 780259) B780259
theorem B1368029 : Blo 459783 1368029 := bstep (se 3 (by rfl) ⟨256505, by rfl⟩ : syracuseStep 1368029 = 513011) B513011
theorem B1040435 : Blo 459783 1040435 := bstep (se 1 (by rfl) ⟨780326, by rfl⟩ : syracuseStep 1040435 = 1560653) B1560653
theorem B1335361 : Blo 459783 1335361 := bstep (se 2 (by rfl) ⟨500760, by rfl⟩ : syracuseStep 1335361 = 1001521) B1001521
theorem B778315 : Blo 459783 778315 := bstep (se 1 (by rfl) ⟨583736, by rfl⟩ : syracuseStep 778315 = 1167473) B1167473
theorem B1040471 : Blo 459783 1040471 := bstep (se 1 (by rfl) ⟨780353, by rfl⟩ : syracuseStep 1040471 = 1560707) B1560707
theorem B876683 : Blo 459783 876683 := bstep (se 1 (by rfl) ⟨657512, by rfl⟩ : syracuseStep 876683 = 1315025) B1315025
theorem B876737 : Blo 459783 876737 := bstep (se 2 (by rfl) ⟨328776, by rfl⟩ : syracuseStep 876737 = 657553) B657553
theorem B1564865 : Blo 459783 1564865 := bstep (se 2 (by rfl) ⟨586824, by rfl⟩ : syracuseStep 1564865 = 1173649) B1173649
theorem B778457 : Blo 459783 778457 := bstep (se 2 (by rfl) ⟨291921, by rfl⟩ : syracuseStep 778457 = 583843) B583843
theorem B1040651 : Blo 459783 1040651 := bstep (se 1 (by rfl) ⟨780488, by rfl⟩ : syracuseStep 1040651 = 1560977) B1560977
theorem B1040705 : Blo 459783 1040705 := bstep (se 2 (by rfl) ⟨390264, by rfl⟩ : syracuseStep 1040705 = 780529) B780529
theorem B778585 : Blo 459783 778585 := bstep (se 2 (by rfl) ⟨291969, by rfl⟩ : syracuseStep 778585 = 583939) B583939
theorem B582167 : Blo 459783 582167 := bstep (se 1 (by rfl) ⟨436625, by rfl⟩ : syracuseStep 582167 = 873251) B873251
theorem B1040921 : Blo 459783 1040921 := bstep (se 2 (by rfl) ⟨390345, by rfl⟩ : syracuseStep 1040921 = 780691) B780691
theorem B1106497 : Blo 459783 1106497 := bstep (se 2 (by rfl) ⟨414936, by rfl⟩ : syracuseStep 1106497 = 829873) B829873
theorem B1041011 : Blo 459783 1041011 := bstep (se 1 (by rfl) ⟨780758, by rfl⟩ : syracuseStep 1041011 = 1561517) B1561517
theorem B1041047 : Blo 459783 1041047 := bstep (se 1 (by rfl) ⟨780785, by rfl⟩ : syracuseStep 1041047 = 1561571) B1561571
theorem B1172171 : Blo 459783 1172171 := bstep (se 1 (by rfl) ⟨879128, by rfl⟩ : syracuseStep 1172171 = 1758257) B1758257
theorem B3498713 : Blo 459783 3498713 := bstep (se 2 (by rfl) ⟨1312017, by rfl⟩ : syracuseStep 3498713 = 2624035) B2624035
theorem B2810699 : Blo 459783 2810699 := bstep (se 1 (by rfl) ⟨2108024, by rfl⟩ : syracuseStep 2810699 = 4216049) B4216049
theorem B1041227 : Blo 459783 1041227 := bstep (se 1 (by rfl) ⟨780920, by rfl⟩ : syracuseStep 1041227 = 1561841) B1561841
theorem B1106777 : Blo 459783 1106777 := bstep (se 2 (by rfl) ⟨415041, by rfl⟩ : syracuseStep 1106777 = 830083) B830083
theorem B1041281 : Blo 459783 1041281 := bstep (se 2 (by rfl) ⟨390480, by rfl⟩ : syracuseStep 1041281 = 780961) B780961
theorem B779159 : Blo 459783 779159 := bstep (se 1 (by rfl) ⟨584369, by rfl⟩ : syracuseStep 779159 = 1168739) B1168739
theorem B5923763 : Blo 459783 5923763 := bstep (se 1 (by rfl) ⟨4442822, by rfl⟩ : syracuseStep 5923763 = 8885645) B8885645
theorem B779287 : Blo 459783 779287 := bstep (se 1 (by rfl) ⟨584465, by rfl⟩ : syracuseStep 779287 = 1168931) B1168931
theorem B877655 : Blo 459783 877655 := bstep (se 1 (by rfl) ⟨658241, by rfl⟩ : syracuseStep 877655 = 1316483) B1316483
theorem B1041497 : Blo 459783 1041497 := bstep (se 2 (by rfl) ⟨390561, by rfl⟩ : syracuseStep 1041497 = 781123) B781123
theorem B1041587 : Blo 459783 1041587 := bstep (se 1 (by rfl) ⟨781190, by rfl⟩ : syracuseStep 1041587 = 1562381) B1562381
theorem B582871 : Blo 459783 582871 := bstep (se 1 (by rfl) ⟨437153, by rfl⟩ : syracuseStep 582871 = 874307) B874307
theorem B1041623 : Blo 459783 1041623 := bstep (se 1 (by rfl) ⟨781217, by rfl⟩ : syracuseStep 1041623 = 1562435) B1562435
theorem B517387 : Blo 459783 517387 := bstep (se 1 (by rfl) ⟨388040, by rfl⟩ : syracuseStep 517387 = 776081) B776081
theorem B1795421 : Blo 459783 1795421 := bstep (se 3 (by rfl) ⟨336641, by rfl⟩ : syracuseStep 1795421 = 673283) B673283
theorem B517495 : Blo 459783 517495 := bstep (se 1 (by rfl) ⟨388121, by rfl⟩ : syracuseStep 517495 = 776243) B776243
theorem B1041803 : Blo 459783 1041803 := bstep (se 1 (by rfl) ⟨781352, by rfl⟩ : syracuseStep 1041803 = 1562705) B1562705
theorem B1041857 : Blo 459783 1041857 := bstep (se 2 (by rfl) ⟨390696, by rfl⟩ : syracuseStep 1041857 = 781393) B781393
theorem B1500619 : Blo 459783 1500619 := bstep (se 1 (by rfl) ⟨1125464, by rfl⟩ : syracuseStep 1500619 = 2250929) B2250929
theorem B845273 : Blo 459783 845273 := bstep (se 2 (by rfl) ⟨316977, by rfl⟩ : syracuseStep 845273 = 633955) B633955
theorem B517675 : Blo 459783 517675 := bstep (se 1 (by rfl) ⟨388256, by rfl⟩ : syracuseStep 517675 = 776513) B776513
theorem B2221643 : Blo 459783 2221643 := bstep (se 1 (by rfl) ⟨1666232, by rfl⟩ : syracuseStep 2221643 = 3332465) B3332465
theorem B878195 : Blo 459783 878195 := bstep (se 1 (by rfl) ⟨658646, by rfl⟩ : syracuseStep 878195 = 1317293) B1317293
theorem B779915 : Blo 459783 779915 := bstep (se 1 (by rfl) ⟨584936, by rfl⟩ : syracuseStep 779915 = 1169873) B1169873
theorem B517783 : Blo 459783 517783 := bstep (se 1 (by rfl) ⟨388337, by rfl⟩ : syracuseStep 517783 = 776675) B776675
theorem B1173143 : Blo 459783 1173143 := bstep (se 1 (by rfl) ⟨879857, by rfl⟩ : syracuseStep 1173143 = 1759715) B1759715
theorem B1042073 : Blo 459783 1042073 := bstep (se 2 (by rfl) ⟨390777, by rfl⟩ : syracuseStep 1042073 = 781555) B781555
theorem B1042163 : Blo 459783 1042163 := bstep (se 1 (by rfl) ⟨781622, by rfl⟩ : syracuseStep 1042163 = 1563245) B1563245
theorem B780043 : Blo 459783 780043 := bstep (se 1 (by rfl) ⟨585032, by rfl⟩ : syracuseStep 780043 = 1170065) B1170065
theorem B1042199 : Blo 459783 1042199 := bstep (se 1 (by rfl) ⟨781649, by rfl⟩ : syracuseStep 1042199 = 1563299) B1563299
theorem B2713409 : Blo 459783 2713409 := bstep (se 2 (by rfl) ⟨1017528, by rfl⟩ : syracuseStep 2713409 = 2035057) B2035057
theorem B517963 : Blo 459783 517963 := bstep (se 1 (by rfl) ⟨388472, by rfl⟩ : syracuseStep 517963 = 776945) B776945
theorem B780185 : Blo 459783 780185 := bstep (se 2 (by rfl) ⟨292569, by rfl⟩ : syracuseStep 780185 = 585139) B585139
theorem B12642227 : Blo 459783 12642227 := bstep (se 1 (by rfl) ⟨9481670, by rfl⟩ : syracuseStep 12642227 = 18963341) B18963341
theorem B518071 : Blo 459783 518071 := bstep (se 1 (by rfl) ⟨388553, by rfl⟩ : syracuseStep 518071 = 777107) B777107
theorem B1042379 : Blo 459783 1042379 := bstep (se 1 (by rfl) ⟨781784, by rfl⟩ : syracuseStep 1042379 = 1563569) B1563569
theorem B1042433 : Blo 459783 1042433 := bstep (se 2 (by rfl) ⟨390912, by rfl⟩ : syracuseStep 1042433 = 781825) B781825
theorem B780313 : Blo 459783 780313 := bstep (se 2 (by rfl) ⟨292617, by rfl⟩ : syracuseStep 780313 = 585235) B585235
theorem B878681 : Blo 459783 878681 := bstep (se 2 (by rfl) ⟨329505, by rfl⟩ : syracuseStep 878681 = 659011) B659011
theorem B518251 : Blo 459783 518251 := bstep (se 1 (by rfl) ⟨388688, by rfl⟩ : syracuseStep 518251 = 777377) B777377
theorem B1665197 : Blo 459783 1665197 := bstep (se 3 (by rfl) ⟨312224, by rfl⟩ : syracuseStep 1665197 = 624449) B624449
theorem B518359 : Blo 459783 518359 := bstep (se 1 (by rfl) ⟨388769, by rfl⟩ : syracuseStep 518359 = 777539) B777539
theorem B1042649 : Blo 459783 1042649 := bstep (se 2 (by rfl) ⟨390993, by rfl⟩ : syracuseStep 1042649 = 781987) B781987
theorem B1042739 : Blo 459783 1042739 := bstep (se 1 (by rfl) ⟨782054, by rfl⟩ : syracuseStep 1042739 = 1564109) B1564109
theorem B1173811 : Blo 459783 1173811 := bstep (se 1 (by rfl) ⟨880358, by rfl⟩ : syracuseStep 1173811 = 1760717) B1760717
theorem B1665355 : Blo 459783 1665355 := bstep (se 1 (by rfl) ⟨1249016, by rfl⟩ : syracuseStep 1665355 = 2498033) B2498033
theorem B1042775 : Blo 459783 1042775 := bstep (se 1 (by rfl) ⟨782081, by rfl⟩ : syracuseStep 1042775 = 1564163) B1564163
theorem B60615029 : Blo 459783 60615029 := bstep (se 5 (by rfl) ⟨2841329, by rfl⟩ : syracuseStep 60615029 = 5682659) B5682659
theorem B518539 : Blo 459783 518539 := bstep (se 1 (by rfl) ⟨388904, by rfl⟩ : syracuseStep 518539 = 777809) B777809
theorem B1173953 : Blo 459783 1173953 := bstep (se 2 (by rfl) ⟨440232, by rfl⟩ : syracuseStep 1173953 = 880465) B880465
theorem B518647 : Blo 459783 518647 := bstep (se 1 (by rfl) ⟨388985, by rfl⟩ : syracuseStep 518647 = 777971) B777971
theorem B1042955 : Blo 459783 1042955 := bstep (se 1 (by rfl) ⟨782216, by rfl⟩ : syracuseStep 1042955 = 1564433) B1564433
theorem B1043009 : Blo 459783 1043009 := bstep (se 2 (by rfl) ⟨391128, by rfl⟩ : syracuseStep 1043009 = 782257) B782257
theorem B780887 : Blo 459783 780887 := bstep (se 1 (by rfl) ⟨585665, by rfl⟩ : syracuseStep 780887 = 1171331) B1171331
theorem B1665629 : Blo 459783 1665629 := bstep (se 3 (by rfl) ⟨312305, by rfl⟩ : syracuseStep 1665629 = 624611) B624611
theorem B518827 : Blo 459783 518827 := bstep (se 1 (by rfl) ⟨389120, by rfl⟩ : syracuseStep 518827 = 778241) B778241
theorem B781015 : Blo 459783 781015 := bstep (se 1 (by rfl) ⟨585761, by rfl⟩ : syracuseStep 781015 = 1171523) B1171523
theorem B518935 : Blo 459783 518935 := bstep (se 1 (by rfl) ⟨389201, by rfl⟩ : syracuseStep 518935 = 778403) B778403
theorem B846617 : Blo 459783 846617 := bstep (se 2 (by rfl) ⟨317481, by rfl⟩ : syracuseStep 846617 = 634963) B634963
theorem B1043225 : Blo 459783 1043225 := bstep (se 2 (by rfl) ⟨391209, by rfl⟩ : syracuseStep 1043225 = 782419) B782419
theorem B1043315 : Blo 459783 1043315 := bstep (se 1 (by rfl) ⟨782486, by rfl⟩ : syracuseStep 1043315 = 1564973) B1564973
theorem B584587 : Blo 459783 584587 := bstep (se 1 (by rfl) ⟨438440, by rfl⟩ : syracuseStep 584587 = 876881) B876881
theorem B1043351 : Blo 459783 1043351 := bstep (se 1 (by rfl) ⟨782513, by rfl⟩ : syracuseStep 1043351 = 1565027) B1565027
theorem B519115 : Blo 459783 519115 := bstep (se 1 (by rfl) ⟨389336, by rfl⟩ : syracuseStep 519115 = 778673) B778673
theorem B519223 : Blo 459783 519223 := bstep (se 1 (by rfl) ⟨389417, by rfl⟩ : syracuseStep 519223 = 778835) B778835
theorem B519403 : Blo 459783 519403 := bstep (se 1 (by rfl) ⟨389552, by rfl⟩ : syracuseStep 519403 = 779105) B779105
theorem B781643 : Blo 459783 781643 := bstep (se 1 (by rfl) ⟨586232, by rfl⟩ : syracuseStep 781643 = 1172465) B1172465
theorem B519511 : Blo 459783 519511 := bstep (se 1 (by rfl) ⟨389633, by rfl⟩ : syracuseStep 519511 = 779267) B779267
theorem B781771 : Blo 459783 781771 := bstep (se 1 (by rfl) ⟨586328, by rfl⟩ : syracuseStep 781771 = 1172657) B1172657
theorem B519691 : Blo 459783 519691 := bstep (se 1 (by rfl) ⟨389768, by rfl⟩ : syracuseStep 519691 = 779537) B779537
theorem B880139 : Blo 459783 880139 := bstep (se 1 (by rfl) ⟨660104, by rfl⟩ : syracuseStep 880139 = 1320209) B1320209
theorem B4419107 : Blo 459783 4419107 := bstep (se 1 (by rfl) ⟨3314330, by rfl⟩ : syracuseStep 4419107 = 6628661) B6628661
theorem B781913 : Blo 459783 781913 := bstep (se 2 (by rfl) ⟨293217, by rfl⟩ : syracuseStep 781913 = 586435) B586435
theorem B519799 : Blo 459783 519799 := bstep (se 1 (by rfl) ⟨389849, by rfl⟩ : syracuseStep 519799 = 779699) B779699
theorem B880321 : Blo 459783 880321 := bstep (se 2 (by rfl) ⟨330120, by rfl⟩ : syracuseStep 880321 = 660241) B660241
theorem B782041 : Blo 459783 782041 := bstep (se 2 (by rfl) ⟨293265, by rfl⟩ : syracuseStep 782041 = 586531) B586531
theorem B6942449 : Blo 459783 6942449 := bstep (se 2 (by rfl) ⟨2603418, by rfl⟩ : syracuseStep 6942449 = 5206837) B5206837
theorem B519979 : Blo 459783 519979 := bstep (se 1 (by rfl) ⟨389984, by rfl⟩ : syracuseStep 519979 = 779969) B779969
theorem B5238593 : Blo 459783 5238593 := bstep (se 2 (by rfl) ⟨1964472, by rfl⟩ : syracuseStep 5238593 = 3928945) B3928945
theorem B585559 : Blo 459783 585559 := bstep (se 1 (by rfl) ⟨439169, by rfl⟩ : syracuseStep 585559 = 878339) B878339
theorem B520087 : Blo 459783 520087 := bstep (se 1 (by rfl) ⟨390065, by rfl⟩ : syracuseStep 520087 = 780131) B780131
theorem B3502115 : Blo 459783 3502115 := bstep (se 1 (by rfl) ⟨2626586, by rfl⟩ : syracuseStep 3502115 = 5253173) B5253173
theorem B1110091 : Blo 459783 1110091 := bstep (se 1 (by rfl) ⟨832568, by rfl⟩ : syracuseStep 1110091 = 1665137) B1665137
theorem B520267 : Blo 459783 520267 := bstep (se 1 (by rfl) ⟨390200, by rfl⟩ : syracuseStep 520267 = 780401) B780401
theorem B520375 : Blo 459783 520375 := bstep (se 1 (by rfl) ⟨390281, by rfl⟩ : syracuseStep 520375 = 780563) B780563
theorem B782615 : Blo 459783 782615 := bstep (se 1 (by rfl) ⟨586961, by rfl⟩ : syracuseStep 782615 = 1173923) B1173923
theorem B1110361 : Blo 459783 1110361 := bstep (se 2 (by rfl) ⟨416385, by rfl⟩ : syracuseStep 1110361 = 832771) B832771
theorem B520555 : Blo 459783 520555 := bstep (se 1 (by rfl) ⟨390416, by rfl⟩ : syracuseStep 520555 = 780833) B780833
theorem B520663 : Blo 459783 520663 := bstep (se 1 (by rfl) ⟨390497, by rfl⟩ : syracuseStep 520663 = 780995) B780995
theorem B520843 : Blo 459783 520843 := bstep (se 1 (by rfl) ⟨390632, by rfl⟩ : syracuseStep 520843 = 781265) B781265
theorem B586379 : Blo 459783 586379 := bstep (se 1 (by rfl) ⟨439784, by rfl⟩ : syracuseStep 586379 = 879569) B879569
theorem B520951 : Blo 459783 520951 := bstep (se 1 (by rfl) ⟨390713, by rfl⟩ : syracuseStep 520951 = 781427) B781427
theorem B521131 : Blo 459783 521131 := bstep (se 1 (by rfl) ⟨390848, by rfl⟩ : syracuseStep 521131 = 781697) B781697
theorem B3339269 : Blo 459783 3339269 := bstep (se 4 (by rfl) ⟨313056, by rfl⟩ : syracuseStep 3339269 = 626113) B626113
theorem B521239 : Blo 459783 521239 := bstep (se 1 (by rfl) ⟨390929, by rfl⟩ : syracuseStep 521239 = 781859) B781859
theorem B3929219 : Blo 459783 3929219 := bstep (se 1 (by rfl) ⟨2946914, by rfl⟩ : syracuseStep 3929219 = 5893829) B5893829
theorem B521419 : Blo 459783 521419 := bstep (se 1 (by rfl) ⟨391064, by rfl⟩ : syracuseStep 521419 = 782129) B782129
theorem B1668397 : Blo 459783 1668397 := bstep (se 3 (by rfl) ⟨312824, by rfl⟩ : syracuseStep 1668397 = 625649) B625649
theorem B521527 : Blo 459783 521527 := bstep (se 1 (by rfl) ⟨391145, by rfl⟩ : syracuseStep 521527 = 782291) B782291
theorem B521707 : Blo 459783 521707 := bstep (se 1 (by rfl) ⟨391280, by rfl⟩ : syracuseStep 521707 = 782561) B782561
theorem B554507 : Blo 459783 554507 := bstep (se 1 (by rfl) ⟨415880, by rfl⟩ : syracuseStep 554507 = 831761) B831761
theorem B1111745 : Blo 459783 1111745 := bstep (se 2 (by rfl) ⟨416904, by rfl⟩ : syracuseStep 1111745 = 833809) B833809
theorem B1668887 : Blo 459783 1668887 := bstep (se 1 (by rfl) ⟨1251665, by rfl⟩ : syracuseStep 1668887 = 2503331) B2503331
theorem B3799057 : Blo 459783 3799057 := bstep (se 2 (by rfl) ⟨1424646, by rfl⟩ : syracuseStep 3799057 = 2849293) B2849293
theorem B751769 : Blo 459783 751769 := bstep (se 2 (by rfl) ⟨281913, by rfl⟩ : syracuseStep 751769 = 563827) B563827
theorem B1407577 : Blo 459783 1407577 := bstep (se 2 (by rfl) ⟨527841, by rfl⟩ : syracuseStep 1407577 = 1055683) B1055683
theorem B1473241 : Blo 459783 1473241 := bstep (se 2 (by rfl) ⟨552465, by rfl⟩ : syracuseStep 1473241 = 1104931) B1104931
theorem B752395 : Blo 459783 752395 := bstep (se 1 (by rfl) ⟨564296, by rfl⟩ : syracuseStep 752395 = 1128593) B1128593
theorem B3373841 : Blo 459783 3373841 := bstep (se 2 (by rfl) ⟨1265190, by rfl⟩ : syracuseStep 3373841 = 2530381) B2530381
theorem B6683609 : Blo 459783 6683609 := bstep (se 2 (by rfl) ⟨2506353, by rfl⟩ : syracuseStep 6683609 = 5012707) B5012707
theorem B2948197 : Blo 459783 2948197 := bstep (se 4 (by rfl) ⟨276393, by rfl⟩ : syracuseStep 2948197 = 552787) B552787
theorem B1965329 : Blo 459783 1965329 := bstep (se 2 (by rfl) ⟨736998, by rfl⟩ : syracuseStep 1965329 = 1473997) B1473997
theorem B982297 : Blo 459783 982297 := bstep (se 2 (by rfl) ⟨368361, by rfl⟩ : syracuseStep 982297 = 736723) B736723
theorem B1310003 : Blo 459783 1310003 := bstep (se 1 (by rfl) ⟨982502, by rfl⟩ : syracuseStep 1310003 = 1965005) B1965005
theorem B654745 : Blo 459783 654745 := bstep (se 2 (by rfl) ⟨245529, by rfl⟩ : syracuseStep 654745 = 491059) B491059
theorem B622027 : Blo 459783 622027 := bstep (se 1 (by rfl) ⟨466520, by rfl⟩ : syracuseStep 622027 = 933041) B933041
theorem B1671005 : Blo 459783 1671005 := bstep (se 3 (by rfl) ⟨313313, by rfl⟩ : syracuseStep 1671005 = 626627) B626627
theorem B556939 : Blo 459783 556939 := bstep (se 1 (by rfl) ⟨417704, by rfl⟩ : syracuseStep 556939 = 835409) B835409
theorem B4226993 : Blo 459783 4226993 := bstep (se 2 (by rfl) ⟨1585122, by rfl⟩ : syracuseStep 4226993 = 3170245) B3170245
theorem B1474483 : Blo 459783 1474483 := bstep (se 1 (by rfl) ⟨1105862, by rfl⟩ : syracuseStep 1474483 = 2211725) B2211725
theorem B1966045 : Blo 459783 1966045 := bstep (se 3 (by rfl) ⟨368633, by rfl⟩ : syracuseStep 1966045 = 737267) B737267
theorem B2818091 : Blo 459783 2818091 := bstep (se 1 (by rfl) ⟨2113568, by rfl⟩ : syracuseStep 2818091 = 4227137) B4227137
theorem B5242967 : Blo 459783 5242967 := bstep (se 1 (by rfl) ⟨3932225, by rfl⟩ : syracuseStep 5242967 = 7864451) B7864451
theorem B1311005 : Blo 459783 1311005 := bstep (se 3 (by rfl) ⟨245813, by rfl⟩ : syracuseStep 1311005 = 491627) B491627
theorem B1573273 : Blo 459783 1573273 := bstep (se 2 (by rfl) ⟨589977, by rfl⟩ : syracuseStep 1573273 = 1179955) B1179955
theorem B1180345 : Blo 459783 1180345 := bstep (se 2 (by rfl) ⟨442629, by rfl⟩ : syracuseStep 1180345 = 885259) B885259
theorem B1475329 : Blo 459783 1475329 := bstep (se 2 (by rfl) ⟨553248, by rfl⟩ : syracuseStep 1475329 = 1106497) B1106497
theorem B459783 : Blo 459783 459783 := bstep (se 1 (by rfl) ⟨344837, by rfl⟩ : syracuseStep 459783 = 689675) B689675
theorem B459791 : Blo 459783 459791 := bstep (se 1 (by rfl) ⟨344843, by rfl⟩ : syracuseStep 459791 = 689687) B689687
theorem B37815349 : Blo 459783 37815349 := bstep (se 5 (by rfl) ⟨1772594, by rfl⟩ : syracuseStep 37815349 = 3545189) B3545189
theorem B459835 : Blo 459783 459835 := bstep (se 1 (by rfl) ⟨344876, by rfl⟩ : syracuseStep 459835 = 689753) B689753
theorem B459911 : Blo 459783 459911 := bstep (se 1 (by rfl) ⟨344933, by rfl⟩ : syracuseStep 459911 = 689867) B689867
theorem B459919 : Blo 459783 459919 := bstep (se 1 (by rfl) ⟨344939, by rfl⟩ : syracuseStep 459919 = 689879) B689879
theorem B459963 : Blo 459783 459963 := bstep (se 1 (by rfl) ⟨344972, by rfl⟩ : syracuseStep 459963 = 689945) B689945
theorem B591035 : Blo 459783 591035 := bstep (se 1 (by rfl) ⟨443276, by rfl⟩ : syracuseStep 591035 = 886553) B886553
theorem B460039 : Blo 459783 460039 := bstep (se 1 (by rfl) ⟨345029, by rfl⟩ : syracuseStep 460039 = 690059) B690059
theorem B460047 : Blo 459783 460047 := bstep (se 1 (by rfl) ⟨345035, by rfl⟩ : syracuseStep 460047 = 690071) B690071
theorem B1180943 : Blo 459783 1180943 := bstep (se 1 (by rfl) ⟨885707, by rfl⟩ : syracuseStep 1180943 = 1771415) B1771415
theorem B460091 : Blo 459783 460091 := bstep (se 1 (by rfl) ⟨345068, by rfl⟩ : syracuseStep 460091 = 690137) B690137
theorem B460167 : Blo 459783 460167 := bstep (se 1 (by rfl) ⟨345125, by rfl⟩ : syracuseStep 460167 = 690251) B690251
theorem B460175 : Blo 459783 460175 := bstep (se 1 (by rfl) ⟨345131, by rfl⟩ : syracuseStep 460175 = 690263) B690263
theorem B787897 : Blo 459783 787897 := bstep (se 2 (by rfl) ⟨295461, by rfl⟩ : syracuseStep 787897 = 590923) B590923
theorem B460219 : Blo 459783 460219 := bstep (se 1 (by rfl) ⟨345164, by rfl⟩ : syracuseStep 460219 = 690329) B690329
theorem B460295 : Blo 459783 460295 := bstep (se 1 (by rfl) ⟨345221, by rfl⟩ : syracuseStep 460295 = 690443) B690443
theorem B460303 : Blo 459783 460303 := bstep (se 1 (by rfl) ⟨345227, by rfl⟩ : syracuseStep 460303 = 690455) B690455
theorem B689723 : Blo 459783 689723 := bstep (se 1 (by rfl) ⟨517292, by rfl⟩ : syracuseStep 689723 = 1034585) B1034585
theorem B460347 : Blo 459783 460347 := bstep (se 1 (by rfl) ⟨345260, by rfl⟩ : syracuseStep 460347 = 690521) B690521
theorem B4425293 : Blo 459783 4425293 := bstep (se 3 (by rfl) ⟨829742, by rfl⟩ : syracuseStep 4425293 = 1659485) B1659485
theorem B22808141 : Blo 459783 22808141 := bstep (se 3 (by rfl) ⟨4276526, by rfl⟩ : syracuseStep 22808141 = 8553053) B8553053
theorem B7603789 : Blo 459783 7603789 := bstep (se 3 (by rfl) ⟨1425710, by rfl⟩ : syracuseStep 7603789 = 2851421) B2851421
theorem B689783 : Blo 459783 689783 := bstep (se 1 (by rfl) ⟨517337, by rfl⟩ : syracuseStep 689783 = 1034675) B1034675
theorem B1476215 : Blo 459783 1476215 := bstep (se 1 (by rfl) ⟨1107161, by rfl⟩ : syracuseStep 1476215 = 2214323) B2214323
theorem B460423 : Blo 459783 460423 := bstep (se 1 (by rfl) ⟨345317, by rfl⟩ : syracuseStep 460423 = 690635) B690635
theorem B689807 : Blo 459783 689807 := bstep (se 1 (by rfl) ⟨517355, by rfl⟩ : syracuseStep 689807 = 1034711) B1034711
theorem B460431 : Blo 459783 460431 := bstep (se 1 (by rfl) ⟨345323, by rfl⟩ : syracuseStep 460431 = 690647) B690647
theorem B689849 : Blo 459783 689849 := bstep (se 2 (by rfl) ⟨258693, by rfl⟩ : syracuseStep 689849 = 517387) B517387
theorem B460475 : Blo 459783 460475 := bstep (se 1 (by rfl) ⟨345356, by rfl⟩ : syracuseStep 460475 = 690713) B690713
theorem B689927 : Blo 459783 689927 := bstep (se 1 (by rfl) ⟨517445, by rfl⟩ : syracuseStep 689927 = 1034891) B1034891
theorem B460551 : Blo 459783 460551 := bstep (se 1 (by rfl) ⟨345413, by rfl⟩ : syracuseStep 460551 = 690827) B690827
theorem B460559 : Blo 459783 460559 := bstep (se 1 (by rfl) ⟨345419, by rfl⟩ : syracuseStep 460559 = 690839) B690839
theorem B689963 : Blo 459783 689963 := bstep (se 1 (by rfl) ⟨517472, by rfl⟩ : syracuseStep 689963 = 1034945) B1034945
theorem B460603 : Blo 459783 460603 := bstep (se 1 (by rfl) ⟨345452, by rfl⟩ : syracuseStep 460603 = 690905) B690905
theorem B689993 : Blo 459783 689993 := bstep (se 2 (by rfl) ⟨258747, by rfl⟩ : syracuseStep 689993 = 517495) B517495
theorem B460679 : Blo 459783 460679 := bstep (se 1 (by rfl) ⟨345509, by rfl⟩ : syracuseStep 460679 = 691019) B691019
theorem B460687 : Blo 459783 460687 := bstep (se 1 (by rfl) ⟨345515, by rfl⟩ : syracuseStep 460687 = 691031) B691031
theorem B2000825 : Blo 459783 2000825 := bstep (se 2 (by rfl) ⟨750309, by rfl⟩ : syracuseStep 2000825 = 1500619) B1500619
theorem B690107 : Blo 459783 690107 := bstep (se 1 (by rfl) ⟨517580, by rfl⟩ : syracuseStep 690107 = 1035161) B1035161
theorem B460731 : Blo 459783 460731 := bstep (se 1 (by rfl) ⟨345548, by rfl⟩ : syracuseStep 460731 = 691097) B691097
theorem B657353 : Blo 459783 657353 := bstep (se 2 (by rfl) ⟨246507, by rfl⟩ : syracuseStep 657353 = 493015) B493015
theorem B690167 : Blo 459783 690167 := bstep (se 1 (by rfl) ⟨517625, by rfl⟩ : syracuseStep 690167 = 1035251) B1035251
theorem B460807 : Blo 459783 460807 := bstep (se 1 (by rfl) ⟨345605, by rfl⟩ : syracuseStep 460807 = 691211) B691211
theorem B2328587 : Blo 459783 2328587 := bstep (se 1 (by rfl) ⟨1746440, by rfl⟩ : syracuseStep 2328587 = 3492881) B3492881
theorem B690191 : Blo 459783 690191 := bstep (se 1 (by rfl) ⟨517643, by rfl⟩ : syracuseStep 690191 = 1035287) B1035287
theorem B460815 : Blo 459783 460815 := bstep (se 1 (by rfl) ⟨345611, by rfl⟩ : syracuseStep 460815 = 691223) B691223
theorem B690233 : Blo 459783 690233 := bstep (se 2 (by rfl) ⟨258837, by rfl⟩ : syracuseStep 690233 = 517675) B517675
theorem B460859 : Blo 459783 460859 := bstep (se 1 (by rfl) ⟨345644, by rfl⟩ : syracuseStep 460859 = 691289) B691289
theorem B690311 : Blo 459783 690311 := bstep (se 1 (by rfl) ⟨517733, by rfl⟩ : syracuseStep 690311 = 1035467) B1035467
theorem B460935 : Blo 459783 460935 := bstep (se 1 (by rfl) ⟨345701, by rfl⟩ : syracuseStep 460935 = 691403) B691403
theorem B460943 : Blo 459783 460943 := bstep (se 1 (by rfl) ⟨345707, by rfl⟩ : syracuseStep 460943 = 691415) B691415
theorem B690347 : Blo 459783 690347 := bstep (se 1 (by rfl) ⟨517760, by rfl⟩ : syracuseStep 690347 = 1035521) B1035521
theorem B2328749 : Blo 459783 2328749 := bstep (se 3 (by rfl) ⟨436640, by rfl⟩ : syracuseStep 2328749 = 873281) B873281
theorem B4982957 : Blo 459783 4982957 := bstep (se 3 (by rfl) ⟨934304, by rfl⟩ : syracuseStep 4982957 = 1868609) B1868609
theorem B460987 : Blo 459783 460987 := bstep (se 1 (by rfl) ⟨345740, by rfl⟩ : syracuseStep 460987 = 691481) B691481
theorem B690377 : Blo 459783 690377 := bstep (se 2 (by rfl) ⟨258891, by rfl⟩ : syracuseStep 690377 = 517783) B517783
theorem B461063 : Blo 459783 461063 := bstep (se 1 (by rfl) ⟨345797, by rfl⟩ : syracuseStep 461063 = 691595) B691595
theorem B461071 : Blo 459783 461071 := bstep (se 1 (by rfl) ⟨345803, by rfl⟩ : syracuseStep 461071 = 691607) B691607
theorem B690491 : Blo 459783 690491 := bstep (se 1 (by rfl) ⟨517868, by rfl⟩ : syracuseStep 690491 = 1035737) B1035737
theorem B461115 : Blo 459783 461115 := bstep (se 1 (by rfl) ⟨345836, by rfl⟩ : syracuseStep 461115 = 691673) B691673
theorem B1313111 : Blo 459783 1313111 := bstep (se 1 (by rfl) ⟨984833, by rfl⟩ : syracuseStep 1313111 = 1969667) B1969667
theorem B690551 : Blo 459783 690551 := bstep (se 1 (by rfl) ⟨517913, by rfl⟩ : syracuseStep 690551 = 1035827) B1035827
theorem B461191 : Blo 459783 461191 := bstep (se 1 (by rfl) ⟨345893, by rfl⟩ : syracuseStep 461191 = 691787) B691787
theorem B690575 : Blo 459783 690575 := bstep (se 1 (by rfl) ⟨517931, by rfl⟩ : syracuseStep 690575 = 1035863) B1035863
theorem B461199 : Blo 459783 461199 := bstep (se 1 (by rfl) ⟨345899, by rfl⟩ : syracuseStep 461199 = 691799) B691799
theorem B690617 : Blo 459783 690617 := bstep (se 2 (by rfl) ⟨258981, by rfl⟩ : syracuseStep 690617 = 517963) B517963
theorem B461243 : Blo 459783 461243 := bstep (se 1 (by rfl) ⟨345932, by rfl⟩ : syracuseStep 461243 = 691865) B691865
theorem B690695 : Blo 459783 690695 := bstep (se 1 (by rfl) ⟨518021, by rfl⟩ : syracuseStep 690695 = 1036043) B1036043
theorem B461319 : Blo 459783 461319 := bstep (se 1 (by rfl) ⟨345989, by rfl⟩ : syracuseStep 461319 = 691979) B691979
theorem B461327 : Blo 459783 461327 := bstep (se 1 (by rfl) ⟨345995, by rfl⟩ : syracuseStep 461327 = 691991) B691991
theorem B690731 : Blo 459783 690731 := bstep (se 1 (by rfl) ⟨518048, by rfl⟩ : syracuseStep 690731 = 1036097) B1036097
theorem B461371 : Blo 459783 461371 := bstep (se 1 (by rfl) ⟨346028, by rfl⟩ : syracuseStep 461371 = 692057) B692057
theorem B690761 : Blo 459783 690761 := bstep (se 2 (by rfl) ⟨259035, by rfl⟩ : syracuseStep 690761 = 518071) B518071
theorem B461447 : Blo 459783 461447 := bstep (se 1 (by rfl) ⟨346085, by rfl⟩ : syracuseStep 461447 = 692171) B692171
theorem B461455 : Blo 459783 461455 := bstep (se 1 (by rfl) ⟨346091, by rfl⟩ : syracuseStep 461455 = 692183) B692183
theorem B690875 : Blo 459783 690875 := bstep (se 1 (by rfl) ⟨518156, by rfl⟩ : syracuseStep 690875 = 1036313) B1036313
theorem B461499 : Blo 459783 461499 := bstep (se 1 (by rfl) ⟨346124, by rfl⟩ : syracuseStep 461499 = 692249) B692249
theorem B690935 : Blo 459783 690935 := bstep (se 1 (by rfl) ⟨518201, by rfl⟩ : syracuseStep 690935 = 1036403) B1036403
theorem B461575 : Blo 459783 461575 := bstep (se 1 (by rfl) ⟨346181, by rfl⟩ : syracuseStep 461575 = 692363) B692363
theorem B690959 : Blo 459783 690959 := bstep (se 1 (by rfl) ⟨518219, by rfl⟩ : syracuseStep 690959 = 1036439) B1036439
theorem B461583 : Blo 459783 461583 := bstep (se 1 (by rfl) ⟨346187, by rfl⟩ : syracuseStep 461583 = 692375) B692375
theorem B4950821 : Blo 459783 4950821 := bstep (se 4 (by rfl) ⟨464139, by rfl⟩ : syracuseStep 4950821 = 928279) B928279
theorem B658219 : Blo 459783 658219 := bstep (se 1 (by rfl) ⟨493664, by rfl⟩ : syracuseStep 658219 = 987329) B987329
theorem B691001 : Blo 459783 691001 := bstep (se 2 (by rfl) ⟨259125, by rfl⟩ : syracuseStep 691001 = 518251) B518251
theorem B461627 : Blo 459783 461627 := bstep (se 1 (by rfl) ⟨346220, by rfl⟩ : syracuseStep 461627 = 692441) B692441
theorem B691079 : Blo 459783 691079 := bstep (se 1 (by rfl) ⟨518309, by rfl⟩ : syracuseStep 691079 = 1036619) B1036619
theorem B461703 : Blo 459783 461703 := bstep (se 1 (by rfl) ⟨346277, by rfl⟩ : syracuseStep 461703 = 692555) B692555
theorem B461711 : Blo 459783 461711 := bstep (se 1 (by rfl) ⟨346283, by rfl⟩ : syracuseStep 461711 = 692567) B692567
theorem B691115 : Blo 459783 691115 := bstep (se 1 (by rfl) ⟨518336, by rfl⟩ : syracuseStep 691115 = 1036673) B1036673
theorem B461755 : Blo 459783 461755 := bstep (se 1 (by rfl) ⟨346316, by rfl⟩ : syracuseStep 461755 = 692633) B692633
theorem B691145 : Blo 459783 691145 := bstep (se 2 (by rfl) ⟨259179, by rfl⟩ : syracuseStep 691145 = 518359) B518359
theorem B461831 : Blo 459783 461831 := bstep (se 1 (by rfl) ⟨346373, by rfl⟩ : syracuseStep 461831 = 692747) B692747
theorem B461839 : Blo 459783 461839 := bstep (se 1 (by rfl) ⟨346379, by rfl⟩ : syracuseStep 461839 = 692759) B692759
theorem B691259 : Blo 459783 691259 := bstep (se 1 (by rfl) ⟨518444, by rfl⟩ : syracuseStep 691259 = 1036889) B1036889
theorem B461883 : Blo 459783 461883 := bstep (se 1 (by rfl) ⟨346412, by rfl⟩ : syracuseStep 461883 = 692825) B692825
theorem B691319 : Blo 459783 691319 := bstep (se 1 (by rfl) ⟨518489, by rfl⟩ : syracuseStep 691319 = 1036979) B1036979
theorem B461959 : Blo 459783 461959 := bstep (se 1 (by rfl) ⟨346469, by rfl⟩ : syracuseStep 461959 = 692939) B692939
theorem B691343 : Blo 459783 691343 := bstep (se 1 (by rfl) ⟨518507, by rfl⟩ : syracuseStep 691343 = 1037015) B1037015
theorem B461967 : Blo 459783 461967 := bstep (se 1 (by rfl) ⟨346475, by rfl⟩ : syracuseStep 461967 = 692951) B692951
theorem B691385 : Blo 459783 691385 := bstep (se 2 (by rfl) ⟨259269, by rfl⟩ : syracuseStep 691385 = 518539) B518539
theorem B1313977 : Blo 459783 1313977 := bstep (se 2 (by rfl) ⟨492741, by rfl⟩ : syracuseStep 1313977 = 985483) B985483
theorem B462011 : Blo 459783 462011 := bstep (se 1 (by rfl) ⟨346508, by rfl⟩ : syracuseStep 462011 = 693017) B693017
theorem B691463 : Blo 459783 691463 := bstep (se 1 (by rfl) ⟨518597, by rfl⟩ : syracuseStep 691463 = 1037195) B1037195
theorem B462087 : Blo 459783 462087 := bstep (se 1 (by rfl) ⟨346565, by rfl⟩ : syracuseStep 462087 = 693131) B693131
theorem B462095 : Blo 459783 462095 := bstep (se 1 (by rfl) ⟨346571, by rfl⟩ : syracuseStep 462095 = 693143) B693143
theorem B691499 : Blo 459783 691499 := bstep (se 1 (by rfl) ⟨518624, by rfl⟩ : syracuseStep 691499 = 1037249) B1037249
theorem B625963 : Blo 459783 625963 := bstep (se 1 (by rfl) ⟨469472, by rfl⟩ : syracuseStep 625963 = 938945) B938945
theorem B462139 : Blo 459783 462139 := bstep (se 1 (by rfl) ⟨346604, by rfl⟩ : syracuseStep 462139 = 693209) B693209
theorem B691529 : Blo 459783 691529 := bstep (se 2 (by rfl) ⟨259323, by rfl⟩ : syracuseStep 691529 = 518647) B518647
theorem B462215 : Blo 459783 462215 := bstep (se 1 (by rfl) ⟨346661, by rfl⟩ : syracuseStep 462215 = 693323) B693323
theorem B462223 : Blo 459783 462223 := bstep (se 1 (by rfl) ⟨346667, by rfl⟩ : syracuseStep 462223 = 693335) B693335
theorem B691643 : Blo 459783 691643 := bstep (se 1 (by rfl) ⟨518732, by rfl⟩ : syracuseStep 691643 = 1037465) B1037465
theorem B462267 : Blo 459783 462267 := bstep (se 1 (by rfl) ⟨346700, by rfl⟩ : syracuseStep 462267 = 693401) B693401
theorem B789961 : Blo 459783 789961 := bstep (se 2 (by rfl) ⟨296235, by rfl⟩ : syracuseStep 789961 = 592471) B592471
theorem B691703 : Blo 459783 691703 := bstep (se 1 (by rfl) ⟨518777, by rfl⟩ : syracuseStep 691703 = 1037555) B1037555
theorem B462343 : Blo 459783 462343 := bstep (se 1 (by rfl) ⟨346757, by rfl⟩ : syracuseStep 462343 = 693515) B693515
theorem B691727 : Blo 459783 691727 := bstep (se 1 (by rfl) ⟨518795, by rfl⟩ : syracuseStep 691727 = 1037591) B1037591
theorem B1314319 : Blo 459783 1314319 := bstep (se 1 (by rfl) ⟨985739, by rfl⟩ : syracuseStep 1314319 = 1971479) B1971479
theorem B462351 : Blo 459783 462351 := bstep (se 1 (by rfl) ⟨346763, by rfl⟩ : syracuseStep 462351 = 693527) B693527
theorem B691769 : Blo 459783 691769 := bstep (se 2 (by rfl) ⟨259413, by rfl⟩ : syracuseStep 691769 = 518827) B518827
theorem B462395 : Blo 459783 462395 := bstep (se 1 (by rfl) ⟨346796, by rfl⟩ : syracuseStep 462395 = 693593) B693593
theorem B691847 : Blo 459783 691847 := bstep (se 1 (by rfl) ⟨518885, by rfl⟩ : syracuseStep 691847 = 1037771) B1037771
theorem B462471 : Blo 459783 462471 := bstep (se 1 (by rfl) ⟨346853, by rfl⟩ : syracuseStep 462471 = 693707) B693707
theorem B462479 : Blo 459783 462479 := bstep (se 1 (by rfl) ⟨346859, by rfl⟩ : syracuseStep 462479 = 693719) B693719
theorem B691883 : Blo 459783 691883 := bstep (se 1 (by rfl) ⟨518912, by rfl⟩ : syracuseStep 691883 = 1037825) B1037825
theorem B462523 : Blo 459783 462523 := bstep (se 1 (by rfl) ⟨346892, by rfl⟩ : syracuseStep 462523 = 693785) B693785
theorem B691913 : Blo 459783 691913 := bstep (se 2 (by rfl) ⟨259467, by rfl⟩ : syracuseStep 691913 = 518935) B518935
theorem B2330369 : Blo 459783 2330369 := bstep (se 2 (by rfl) ⟨873888, by rfl⟩ : syracuseStep 2330369 = 1747777) B1747777
theorem B1249025 : Blo 459783 1249025 := bstep (se 2 (by rfl) ⟨468384, by rfl⟩ : syracuseStep 1249025 = 936769) B936769
theorem B462599 : Blo 459783 462599 := bstep (se 1 (by rfl) ⟨346949, by rfl⟩ : syracuseStep 462599 = 693899) B693899
theorem B462607 : Blo 459783 462607 := bstep (se 1 (by rfl) ⟨346955, by rfl⟩ : syracuseStep 462607 = 693911) B693911
theorem B1314593 : Blo 459783 1314593 := bstep (se 2 (by rfl) ⟨492972, by rfl⟩ : syracuseStep 1314593 = 985945) B985945
theorem B1183547 : Blo 459783 1183547 := bstep (se 1 (by rfl) ⟨887660, by rfl⟩ : syracuseStep 1183547 = 1775321) B1775321
theorem B692027 : Blo 459783 692027 := bstep (se 1 (by rfl) ⟨519020, by rfl⟩ : syracuseStep 692027 = 1038041) B1038041
theorem B462651 : Blo 459783 462651 := bstep (se 1 (by rfl) ⟨346988, by rfl⟩ : syracuseStep 462651 = 693977) B693977
theorem B692087 : Blo 459783 692087 := bstep (se 1 (by rfl) ⟨519065, by rfl⟩ : syracuseStep 692087 = 1038131) B1038131
theorem B462727 : Blo 459783 462727 := bstep (se 1 (by rfl) ⟨347045, by rfl⟩ : syracuseStep 462727 = 694091) B694091
theorem B659335 : Blo 459783 659335 := bstep (se 1 (by rfl) ⟨494501, by rfl⟩ : syracuseStep 659335 = 989003) B989003
theorem B626567 : Blo 459783 626567 := bstep (se 1 (by rfl) ⟨469925, by rfl⟩ : syracuseStep 626567 = 939851) B939851
theorem B692111 : Blo 459783 692111 := bstep (se 1 (by rfl) ⟨519083, by rfl⟩ : syracuseStep 692111 = 1038167) B1038167
theorem B462735 : Blo 459783 462735 := bstep (se 1 (by rfl) ⟨347051, by rfl⟩ : syracuseStep 462735 = 694103) B694103
theorem B692153 : Blo 459783 692153 := bstep (se 2 (by rfl) ⟨259557, by rfl⟩ : syracuseStep 692153 = 519115) B519115
theorem B462779 : Blo 459783 462779 := bstep (se 1 (by rfl) ⟨347084, by rfl⟩ : syracuseStep 462779 = 694169) B694169
theorem B692231 : Blo 459783 692231 := bstep (se 1 (by rfl) ⟨519173, by rfl⟩ : syracuseStep 692231 = 1038347) B1038347
theorem B462855 : Blo 459783 462855 := bstep (se 1 (by rfl) ⟨347141, by rfl⟩ : syracuseStep 462855 = 694283) B694283
theorem B462863 : Blo 459783 462863 := bstep (se 1 (by rfl) ⟨347147, by rfl⟩ : syracuseStep 462863 = 694295) B694295
theorem B692267 : Blo 459783 692267 := bstep (se 1 (by rfl) ⟨519200, by rfl⟩ : syracuseStep 692267 = 1038401) B1038401
theorem B462907 : Blo 459783 462907 := bstep (se 1 (by rfl) ⟨347180, by rfl⟩ : syracuseStep 462907 = 694361) B694361
theorem B692297 : Blo 459783 692297 := bstep (se 2 (by rfl) ⟨259611, by rfl⟩ : syracuseStep 692297 = 519223) B519223
theorem B462983 : Blo 459783 462983 := bstep (se 1 (by rfl) ⟨347237, by rfl⟩ : syracuseStep 462983 = 694475) B694475
theorem B462991 : Blo 459783 462991 := bstep (se 1 (by rfl) ⟨347243, by rfl⟩ : syracuseStep 462991 = 694487) B694487
theorem B692411 : Blo 459783 692411 := bstep (se 1 (by rfl) ⟨519308, by rfl⟩ : syracuseStep 692411 = 1038617) B1038617
theorem B463035 : Blo 459783 463035 := bstep (se 1 (by rfl) ⟨347276, by rfl⟩ : syracuseStep 463035 = 694553) B694553
theorem B692471 : Blo 459783 692471 := bstep (se 1 (by rfl) ⟨519353, by rfl⟩ : syracuseStep 692471 = 1038707) B1038707
theorem B463111 : Blo 459783 463111 := bstep (se 1 (by rfl) ⟨347333, by rfl⟩ : syracuseStep 463111 = 694667) B694667
theorem B692495 : Blo 459783 692495 := bstep (se 1 (by rfl) ⟨519371, by rfl⟩ : syracuseStep 692495 = 1038743) B1038743
theorem B463119 : Blo 459783 463119 := bstep (se 1 (by rfl) ⟨347339, by rfl⟩ : syracuseStep 463119 = 694679) B694679
theorem B692537 : Blo 459783 692537 := bstep (se 2 (by rfl) ⟨259701, by rfl⟩ : syracuseStep 692537 = 519403) B519403
theorem B463163 : Blo 459783 463163 := bstep (se 1 (by rfl) ⟨347372, by rfl⟩ : syracuseStep 463163 = 694745) B694745
theorem B692615 : Blo 459783 692615 := bstep (se 1 (by rfl) ⟨519461, by rfl⟩ : syracuseStep 692615 = 1038923) B1038923
theorem B1315207 : Blo 459783 1315207 := bstep (se 1 (by rfl) ⟨986405, by rfl⟩ : syracuseStep 1315207 = 1972811) B1972811
theorem B463239 : Blo 459783 463239 := bstep (se 1 (by rfl) ⟨347429, by rfl⟩ : syracuseStep 463239 = 694859) B694859
theorem B463247 : Blo 459783 463247 := bstep (se 1 (by rfl) ⟨347435, by rfl⟩ : syracuseStep 463247 = 694871) B694871
theorem B692651 : Blo 459783 692651 := bstep (se 1 (by rfl) ⟨519488, by rfl⟩ : syracuseStep 692651 = 1038977) B1038977
theorem B463291 : Blo 459783 463291 := bstep (se 1 (by rfl) ⟨347468, by rfl⟩ : syracuseStep 463291 = 694937) B694937
theorem B692681 : Blo 459783 692681 := bstep (se 2 (by rfl) ⟨259755, by rfl⟩ : syracuseStep 692681 = 519511) B519511
theorem B463367 : Blo 459783 463367 := bstep (se 1 (by rfl) ⟨347525, by rfl⟩ : syracuseStep 463367 = 695051) B695051
theorem B463375 : Blo 459783 463375 := bstep (se 1 (by rfl) ⟨347531, by rfl⟩ : syracuseStep 463375 = 695063) B695063
theorem B2331179 : Blo 459783 2331179 := bstep (se 1 (by rfl) ⟨1748384, by rfl⟩ : syracuseStep 2331179 = 3496769) B3496769
theorem B692795 : Blo 459783 692795 := bstep (se 1 (by rfl) ⟨519596, by rfl⟩ : syracuseStep 692795 = 1039193) B1039193
theorem B463419 : Blo 459783 463419 := bstep (se 1 (by rfl) ⟨347564, by rfl⟩ : syracuseStep 463419 = 695129) B695129
theorem B692855 : Blo 459783 692855 := bstep (se 1 (by rfl) ⟨519641, by rfl⟩ : syracuseStep 692855 = 1039283) B1039283
theorem B463495 : Blo 459783 463495 := bstep (se 1 (by rfl) ⟨347621, by rfl⟩ : syracuseStep 463495 = 695243) B695243
theorem B692879 : Blo 459783 692879 := bstep (se 1 (by rfl) ⟨519659, by rfl⟩ : syracuseStep 692879 = 1039319) B1039319
theorem B463503 : Blo 459783 463503 := bstep (se 1 (by rfl) ⟨347627, by rfl⟩ : syracuseStep 463503 = 695255) B695255
theorem B692921 : Blo 459783 692921 := bstep (se 2 (by rfl) ⟨259845, by rfl⟩ : syracuseStep 692921 = 519691) B519691
theorem B463547 : Blo 459783 463547 := bstep (se 1 (by rfl) ⟨347660, by rfl⟩ : syracuseStep 463547 = 695321) B695321
theorem B660155 : Blo 459783 660155 := bstep (se 1 (by rfl) ⟨495116, by rfl⟩ : syracuseStep 660155 = 990233) B990233
theorem B692999 : Blo 459783 692999 := bstep (se 1 (by rfl) ⟨519749, by rfl⟩ : syracuseStep 692999 = 1039499) B1039499
theorem B463623 : Blo 459783 463623 := bstep (se 1 (by rfl) ⟨347717, by rfl⟩ : syracuseStep 463623 = 695435) B695435
theorem B1315595 : Blo 459783 1315595 := bstep (se 1 (by rfl) ⟨986696, by rfl⟩ : syracuseStep 1315595 = 1973393) B1973393
theorem B463631 : Blo 459783 463631 := bstep (se 1 (by rfl) ⟨347723, by rfl⟩ : syracuseStep 463631 = 695447) B695447
theorem B10523429 : Blo 459783 10523429 := bstep (se 4 (by rfl) ⟨986571, by rfl⟩ : syracuseStep 10523429 = 1973143) B1973143
theorem B693035 : Blo 459783 693035 := bstep (se 1 (by rfl) ⟨519776, by rfl⟩ : syracuseStep 693035 = 1039553) B1039553
theorem B463675 : Blo 459783 463675 := bstep (se 1 (by rfl) ⟨347756, by rfl⟩ : syracuseStep 463675 = 695513) B695513
theorem B693065 : Blo 459783 693065 := bstep (se 2 (by rfl) ⟨259899, by rfl⟩ : syracuseStep 693065 = 519799) B519799
theorem B463751 : Blo 459783 463751 := bstep (se 1 (by rfl) ⟨347813, by rfl⟩ : syracuseStep 463751 = 695627) B695627
theorem B463759 : Blo 459783 463759 := bstep (se 1 (by rfl) ⟨347819, by rfl⟩ : syracuseStep 463759 = 695639) B695639
theorem B2626451 : Blo 459783 2626451 := bstep (se 1 (by rfl) ⟨1969838, by rfl⟩ : syracuseStep 2626451 = 3939677) B3939677
theorem B693179 : Blo 459783 693179 := bstep (se 1 (by rfl) ⟨519884, by rfl⟩ : syracuseStep 693179 = 1039769) B1039769
theorem B693239 : Blo 459783 693239 := bstep (se 1 (by rfl) ⟨519929, by rfl⟩ : syracuseStep 693239 = 1039859) B1039859
theorem B2659331 : Blo 459783 2659331 := bstep (se 1 (by rfl) ⟨1994498, by rfl⟩ : syracuseStep 2659331 = 3988997) B3988997
theorem B693263 : Blo 459783 693263 := bstep (se 1 (by rfl) ⟨519947, by rfl⟩ : syracuseStep 693263 = 1039895) B1039895
theorem B988175 : Blo 459783 988175 := bstep (se 1 (by rfl) ⟨741131, by rfl⟩ : syracuseStep 988175 = 1482263) B1482263
theorem B693305 : Blo 459783 693305 := bstep (se 2 (by rfl) ⟨259989, by rfl⟩ : syracuseStep 693305 = 519979) B519979
theorem B693383 : Blo 459783 693383 := bstep (se 1 (by rfl) ⟨520037, by rfl⟩ : syracuseStep 693383 = 1040075) B1040075
theorem B693419 : Blo 459783 693419 := bstep (se 1 (by rfl) ⟨520064, by rfl⟩ : syracuseStep 693419 = 1040129) B1040129
theorem B693449 : Blo 459783 693449 := bstep (se 2 (by rfl) ⟨260043, by rfl⟩ : syracuseStep 693449 = 520087) B520087
theorem B2954555 : Blo 459783 2954555 := bstep (se 1 (by rfl) ⟨2215916, by rfl⟩ : syracuseStep 2954555 = 4431833) B4431833
theorem B693563 : Blo 459783 693563 := bstep (se 1 (by rfl) ⟨520172, by rfl⟩ : syracuseStep 693563 = 1040345) B1040345
theorem B693623 : Blo 459783 693623 := bstep (se 1 (by rfl) ⟨520217, by rfl⟩ : syracuseStep 693623 = 1040435) B1040435
theorem B2626951 : Blo 459783 2626951 := bstep (se 1 (by rfl) ⟨1970213, by rfl⟩ : syracuseStep 2626951 = 3940427) B3940427
theorem B693647 : Blo 459783 693647 := bstep (se 1 (by rfl) ⟨520235, by rfl⟩ : syracuseStep 693647 = 1040471) B1040471
theorem B1480121 : Blo 459783 1480121 := bstep (se 2 (by rfl) ⟨555045, by rfl⟩ : syracuseStep 1480121 = 1110091) B1110091
theorem B693689 : Blo 459783 693689 := bstep (se 2 (by rfl) ⟨260133, by rfl⟩ : syracuseStep 693689 = 520267) B520267
theorem B693767 : Blo 459783 693767 := bstep (se 1 (by rfl) ⟨520325, by rfl⟩ : syracuseStep 693767 = 1040651) B1040651
theorem B693803 : Blo 459783 693803 := bstep (se 1 (by rfl) ⟨520352, by rfl⟩ : syracuseStep 693803 = 1040705) B1040705
theorem B693833 : Blo 459783 693833 := bstep (se 2 (by rfl) ⟨260187, by rfl⟩ : syracuseStep 693833 = 520375) B520375
theorem B693947 : Blo 459783 693947 := bstep (se 1 (by rfl) ⟨520460, by rfl⟩ : syracuseStep 693947 = 1040921) B1040921
theorem B694007 : Blo 459783 694007 := bstep (se 1 (by rfl) ⟨520505, by rfl⟩ : syracuseStep 694007 = 1041011) B1041011
theorem B694031 : Blo 459783 694031 := bstep (se 1 (by rfl) ⟨520523, by rfl⟩ : syracuseStep 694031 = 1041047) B1041047
theorem B1480481 : Blo 459783 1480481 := bstep (se 2 (by rfl) ⟨555180, by rfl⟩ : syracuseStep 1480481 = 1110361) B1110361
theorem B694073 : Blo 459783 694073 := bstep (se 2 (by rfl) ⟨260277, by rfl⟩ : syracuseStep 694073 = 520555) B520555
theorem B2332475 : Blo 459783 2332475 := bstep (se 1 (by rfl) ⟨1749356, by rfl⟩ : syracuseStep 2332475 = 3498713) B3498713
theorem B4200281 : Blo 459783 4200281 := bstep (se 2 (by rfl) ⟨1575105, by rfl⟩ : syracuseStep 4200281 = 3150211) B3150211
theorem B1873799 : Blo 459783 1873799 := bstep (se 1 (by rfl) ⟨1405349, by rfl⟩ : syracuseStep 1873799 = 2810699) B2810699
theorem B694151 : Blo 459783 694151 := bstep (se 1 (by rfl) ⟨520613, by rfl⟩ : syracuseStep 694151 = 1041227) B1041227
theorem B2987929 : Blo 459783 2987929 := bstep (se 2 (by rfl) ⟨1120473, by rfl⟩ : syracuseStep 2987929 = 2240947) B2240947
theorem B694187 : Blo 459783 694187 := bstep (se 1 (by rfl) ⟨520640, by rfl⟩ : syracuseStep 694187 = 1041281) B1041281
theorem B694217 : Blo 459783 694217 := bstep (se 2 (by rfl) ⟨260331, by rfl⟩ : syracuseStep 694217 = 520663) B520663
theorem B2332637 : Blo 459783 2332637 := bstep (se 3 (by rfl) ⟨437369, by rfl⟩ : syracuseStep 2332637 = 874739) B874739
theorem B1316893 : Blo 459783 1316893 := bstep (se 3 (by rfl) ⟨246917, by rfl⟩ : syracuseStep 1316893 = 493835) B493835
theorem B694331 : Blo 459783 694331 := bstep (se 1 (by rfl) ⟨520748, by rfl⟩ : syracuseStep 694331 = 1041497) B1041497
theorem B694391 : Blo 459783 694391 := bstep (se 1 (by rfl) ⟨520793, by rfl⟩ : syracuseStep 694391 = 1041587) B1041587
theorem B694415 : Blo 459783 694415 := bstep (se 1 (by rfl) ⟨520811, by rfl⟩ : syracuseStep 694415 = 1041623) B1041623
theorem B694457 : Blo 459783 694457 := bstep (se 2 (by rfl) ⟨260421, by rfl⟩ : syracuseStep 694457 = 520843) B520843
theorem B694535 : Blo 459783 694535 := bstep (se 1 (by rfl) ⟨520901, by rfl⟩ : syracuseStep 694535 = 1041803) B1041803
theorem B2332961 : Blo 459783 2332961 := bstep (se 2 (by rfl) ⟨874860, by rfl⟩ : syracuseStep 2332961 = 1749721) B1749721
theorem B694571 : Blo 459783 694571 := bstep (se 1 (by rfl) ⟨520928, by rfl⟩ : syracuseStep 694571 = 1041857) B1041857
theorem B694601 : Blo 459783 694601 := bstep (se 2 (by rfl) ⟨260475, by rfl⟩ : syracuseStep 694601 = 520951) B520951
theorem B1317235 : Blo 459783 1317235 := bstep (se 1 (by rfl) ⟨987926, by rfl⟩ : syracuseStep 1317235 = 1975853) B1975853
theorem B1481095 : Blo 459783 1481095 := bstep (se 1 (by rfl) ⟨1110821, by rfl⟩ : syracuseStep 1481095 = 2221643) B2221643
theorem B694715 : Blo 459783 694715 := bstep (se 1 (by rfl) ⟨521036, by rfl⟩ : syracuseStep 694715 = 1042073) B1042073
theorem B694775 : Blo 459783 694775 := bstep (se 1 (by rfl) ⟨521081, by rfl⟩ : syracuseStep 694775 = 1042163) B1042163
theorem B694799 : Blo 459783 694799 := bstep (se 1 (by rfl) ⟨521099, by rfl⟩ : syracuseStep 694799 = 1042199) B1042199
theorem B5282333 : Blo 459783 5282333 := bstep (se 3 (by rfl) ⟨990437, by rfl⟩ : syracuseStep 5282333 = 1980875) B1980875
theorem B1808939 : Blo 459783 1808939 := bstep (se 1 (by rfl) ⟨1356704, by rfl⟩ : syracuseStep 1808939 = 2713409) B2713409
theorem B694841 : Blo 459783 694841 := bstep (se 2 (by rfl) ⟨260565, by rfl⟩ : syracuseStep 694841 = 521131) B521131
theorem B8428151 : Blo 459783 8428151 := bstep (se 1 (by rfl) ⟨6321113, by rfl⟩ : syracuseStep 8428151 = 12642227) B12642227
theorem B989815 : Blo 459783 989815 := bstep (se 1 (by rfl) ⟨742361, by rfl⟩ : syracuseStep 989815 = 1484723) B1484723
theorem B694919 : Blo 459783 694919 := bstep (se 1 (by rfl) ⟨521189, by rfl⟩ : syracuseStep 694919 = 1042379) B1042379
theorem B694955 : Blo 459783 694955 := bstep (se 1 (by rfl) ⟨521216, by rfl⟩ : syracuseStep 694955 = 1042433) B1042433
theorem B694985 : Blo 459783 694985 := bstep (se 2 (by rfl) ⟨260619, by rfl⟩ : syracuseStep 694985 = 521239) B521239
theorem B695099 : Blo 459783 695099 := bstep (se 1 (by rfl) ⟨521324, by rfl⟩ : syracuseStep 695099 = 1042649) B1042649
theorem B695159 : Blo 459783 695159 := bstep (se 1 (by rfl) ⟨521369, by rfl⟩ : syracuseStep 695159 = 1042739) B1042739
theorem B695183 : Blo 459783 695183 := bstep (se 1 (by rfl) ⟨521387, by rfl⟩ : syracuseStep 695183 = 1042775) B1042775
theorem B40410019 : Blo 459783 40410019 := bstep (se 1 (by rfl) ⟨30307514, by rfl⟩ : syracuseStep 40410019 = 60615029) B60615029
theorem B695225 : Blo 459783 695225 := bstep (se 2 (by rfl) ⟨260709, by rfl⟩ : syracuseStep 695225 = 521419) B521419
theorem B695303 : Blo 459783 695303 := bstep (se 1 (by rfl) ⟨521477, by rfl⟩ : syracuseStep 695303 = 1042955) B1042955
theorem B695339 : Blo 459783 695339 := bstep (se 1 (by rfl) ⟨521504, by rfl⟩ : syracuseStep 695339 = 1043009) B1043009
theorem B695369 : Blo 459783 695369 := bstep (se 2 (by rfl) ⟨260763, by rfl⟩ : syracuseStep 695369 = 521527) B521527
theorem B695483 : Blo 459783 695483 := bstep (se 1 (by rfl) ⟨521612, by rfl⟩ : syracuseStep 695483 = 1043225) B1043225
theorem B2333933 : Blo 459783 2333933 := bstep (se 3 (by rfl) ⟨437612, by rfl⟩ : syracuseStep 2333933 = 875225) B875225
theorem B695543 : Blo 459783 695543 := bstep (se 1 (by rfl) ⟨521657, by rfl⟩ : syracuseStep 695543 = 1043315) B1043315
theorem B695567 : Blo 459783 695567 := bstep (se 1 (by rfl) ⟨521675, by rfl⟩ : syracuseStep 695567 = 1043351) B1043351
theorem B695609 : Blo 459783 695609 := bstep (se 2 (by rfl) ⟨260853, by rfl⟩ : syracuseStep 695609 = 521707) B521707
theorem B3514265 : Blo 459783 3514265 := bstep (se 2 (by rfl) ⟨1317849, by rfl⟩ : syracuseStep 3514265 = 2635699) B2635699
theorem B2334743 : Blo 459783 2334743 := bstep (se 1 (by rfl) ⟨1751057, by rfl⟩ : syracuseStep 2334743 = 3502115) B3502115
theorem B2368061 : Blo 459783 2368061 := bstep (se 3 (by rfl) ⟨444011, by rfl⟩ : syracuseStep 2368061 = 888023) B888023
theorem B1876769 : Blo 459783 1876769 := bstep (se 2 (by rfl) ⟨703788, by rfl⟩ : syracuseStep 1876769 = 1407577) B1407577
theorem B1319969 : Blo 459783 1319969 := bstep (se 2 (by rfl) ⟨494988, by rfl⟩ : syracuseStep 1319969 = 989977) B989977
theorem B1320083 : Blo 459783 1320083 := bstep (se 1 (by rfl) ⟨990062, by rfl⟩ : syracuseStep 1320083 = 1980125) B1980125
theorem B468239 : Blo 459783 468239 := bstep (se 1 (by rfl) ⟨351179, by rfl⟩ : syracuseStep 468239 = 702359) B702359
theorem B501179 : Blo 459783 501179 := bstep (se 1 (by rfl) ⟨375884, by rfl⟩ : syracuseStep 501179 = 751769) B751769
theorem B1418953 : Blo 459783 1418953 := bstep (se 2 (by rfl) ⟨532107, by rfl⟩ : syracuseStep 1418953 = 1064215) B1064215
theorem B3516209 : Blo 459783 3516209 := bstep (se 2 (by rfl) ⟨1318578, by rfl⟩ : syracuseStep 3516209 = 2637157) B2637157
theorem B2959193 : Blo 459783 2959193 := bstep (se 2 (by rfl) ⟨1109697, by rfl⟩ : syracuseStep 2959193 = 2219395) B2219395
theorem B4990871 : Blo 459783 4990871 := bstep (se 1 (by rfl) ⟨3743153, by rfl⟩ : syracuseStep 4990871 = 7486307) B7486307
theorem B829369 : Blo 459783 829369 := bstep (se 2 (by rfl) ⟨311013, by rfl⟩ : syracuseStep 829369 = 622027) B622027
theorem B2500561 : Blo 459783 2500561 := bstep (se 2 (by rfl) ⟨937710, by rfl⟩ : syracuseStep 2500561 = 1875421) B1875421
theorem B20195351 : Blo 459783 20195351 := bstep (se 1 (by rfl) ⟨15146513, by rfl⟩ : syracuseStep 20195351 = 30293027) B30293027
theorem B7481693 : Blo 459783 7481693 := bstep (se 3 (by rfl) ⟨1402817, by rfl⟩ : syracuseStep 7481693 = 2805635) B2805635
theorem B3648077 : Blo 459783 3648077 := bstep (se 3 (by rfl) ⟨684014, by rfl⟩ : syracuseStep 3648077 = 1368029) B1368029
theorem B1780481 : Blo 459783 1780481 := bstep (se 2 (by rfl) ⟨667680, by rfl⟩ : syracuseStep 1780481 = 1335361) B1335361
theorem B2632601 : Blo 459783 2632601 := bstep (se 2 (by rfl) ⟨987225, by rfl⟩ : syracuseStep 2632601 = 1974451) B1974451
theorem B3779531 : Blo 459783 3779531 := bstep (se 1 (by rfl) ⟨2834648, by rfl⟩ : syracuseStep 3779531 = 5669297) B5669297
theorem B2337821 : Blo 459783 2337821 := bstep (se 3 (by rfl) ⟨438341, by rfl⟩ : syracuseStep 2337821 = 876683) B876683
theorem B830753 : Blo 459783 830753 := bstep (se 2 (by rfl) ⟨311532, by rfl⟩ : syracuseStep 830753 = 623065) B623065
theorem B699707 : Blo 459783 699707 := bstep (se 1 (by rfl) ⟨524780, by rfl⟩ : syracuseStep 699707 = 1049561) B1049561
theorem B2338307 : Blo 459783 2338307 := bstep (se 1 (by rfl) ⟨1753730, by rfl⟩ : syracuseStep 2338307 = 3507461) B3507461
theorem B1551959 : Blo 459783 1551959 := bstep (se 1 (by rfl) ⟨1163969, by rfl⟩ : syracuseStep 1551959 = 2327939) B2327939
theorem B1748567 : Blo 459783 1748567 := bstep (se 1 (by rfl) ⟨1311425, by rfl⟩ : syracuseStep 1748567 = 2622851) B2622851
theorem B700091 : Blo 459783 700091 := bstep (se 1 (by rfl) ⟨525068, by rfl⟩ : syracuseStep 700091 = 1050137) B1050137
theorem B1978127 : Blo 459783 1978127 := bstep (se 1 (by rfl) ⟨1483595, by rfl⟩ : syracuseStep 1978127 = 2967191) B2967191
theorem B667639 : Blo 459783 667639 := bstep (se 1 (by rfl) ⟨500729, by rfl⟩ : syracuseStep 667639 = 1001459) B1001459
theorem B1552445 : Blo 459783 1552445 := bstep (se 3 (by rfl) ⟨291083, by rfl⟩ : syracuseStep 1552445 = 582167) B582167
theorem B1749053 : Blo 459783 1749053 := bstep (se 3 (by rfl) ⟨327947, by rfl⟩ : syracuseStep 1749053 = 655895) B655895
theorem B3322259 : Blo 459783 3322259 := bstep (se 1 (by rfl) ⟨2491694, by rfl⟩ : syracuseStep 3322259 = 4983389) B4983389
theorem B2109995 : Blo 459783 2109995 := bstep (se 1 (by rfl) ⟨1582496, by rfl⟩ : syracuseStep 2109995 = 3164993) B3164993
theorem B2241433 : Blo 459783 2241433 := bstep (se 2 (by rfl) ⟨840537, by rfl⟩ : syracuseStep 2241433 = 1681075) B1681075
theorem B5256089 : Blo 459783 5256089 := bstep (se 2 (by rfl) ⟨1971033, by rfl⟩ : syracuseStep 5256089 = 3942067) B3942067
theorem B2339927 : Blo 459783 2339927 := bstep (se 1 (by rfl) ⟨1754945, by rfl⟩ : syracuseStep 2339927 = 3509891) B3509891
theorem B800015 : Blo 459783 800015 := bstep (se 1 (by rfl) ⟨600011, by rfl⟩ : syracuseStep 800015 = 1200023) B1200023
theorem B1553849 : Blo 459783 1553849 := bstep (se 2 (by rfl) ⟨582693, by rfl⟩ : syracuseStep 1553849 = 1165387) B1165387
theorem B1750481 : Blo 459783 1750481 := bstep (se 2 (by rfl) ⟨656430, by rfl⟩ : syracuseStep 1750481 = 1312861) B1312861
theorem B996923 : Blo 459783 996923 := bstep (se 1 (by rfl) ⟨747692, by rfl⟩ : syracuseStep 996923 = 1495385) B1495385
theorem B2340413 : Blo 459783 2340413 := bstep (se 3 (by rfl) ⟨438827, by rfl⟩ : syracuseStep 2340413 = 877655) B877655
theorem B2111233 : Blo 459783 2111233 := bstep (se 2 (by rfl) ⟨791712, by rfl⟩ : syracuseStep 2111233 = 1583425) B1583425
theorem B3258265 : Blo 459783 3258265 := bstep (se 2 (by rfl) ⟨1221849, by rfl⟩ : syracuseStep 3258265 = 2443699) B2443699
theorem B1554443 : Blo 459783 1554443 := bstep (se 1 (by rfl) ⟨1165832, by rfl⟩ : syracuseStep 1554443 = 2331665) B2331665
theorem B1554551 : Blo 459783 1554551 := bstep (se 1 (by rfl) ⟨1165913, by rfl⟩ : syracuseStep 1554551 = 2331827) B2331827
theorem B9124013 : Blo 459783 9124013 := bstep (se 3 (by rfl) ⟨1710752, by rfl⟩ : syracuseStep 9124013 = 3421505) B3421505
theorem B1555145 : Blo 459783 1555145 := bstep (se 2 (by rfl) ⟨583179, by rfl⟩ : syracuseStep 1555145 = 1166359) B1166359
theorem B1752151 : Blo 459783 1752151 := bstep (se 1 (by rfl) ⟨1314113, by rfl⟩ : syracuseStep 1752151 = 2628227) B2628227
theorem B2342195 : Blo 459783 2342195 := bstep (se 1 (by rfl) ⟨1756646, by rfl⟩ : syracuseStep 2342195 = 3513293) B3513293
theorem B834875 : Blo 459783 834875 := bstep (se 1 (by rfl) ⟨626156, by rfl⟩ : syracuseStep 834875 = 1252313) B1252313
theorem B1555847 : Blo 459783 1555847 := bstep (se 1 (by rfl) ⟨1166885, by rfl⟩ : syracuseStep 1555847 = 2333771) B2333771
theorem B1752455 : Blo 459783 1752455 := bstep (se 1 (by rfl) ⟨1314341, by rfl⟩ : syracuseStep 1752455 = 2628683) B2628683
theorem B3554705 : Blo 459783 3554705 := bstep (se 2 (by rfl) ⟨1333014, by rfl⟩ : syracuseStep 3554705 = 2666029) B2666029
theorem B1752637 : Blo 459783 1752637 := bstep (se 3 (by rfl) ⟨328619, by rfl⟩ : syracuseStep 1752637 = 657239) B657239
theorem B6307429 : Blo 459783 6307429 := bstep (se 4 (by rfl) ⟨591321, by rfl⟩ : syracuseStep 6307429 = 1182643) B1182643
theorem B2342519 : Blo 459783 2342519 := bstep (se 1 (by rfl) ⟨1756889, by rfl⟩ : syracuseStep 2342519 = 3513779) B3513779
theorem B2637431 : Blo 459783 2637431 := bstep (se 1 (by rfl) ⟨1978073, by rfl⟩ : syracuseStep 2637431 = 3956147) B3956147
theorem B704135 : Blo 459783 704135 := bstep (se 1 (by rfl) ⟨528101, by rfl⟩ : syracuseStep 704135 = 1056203) B1056203
theorem B1556225 : Blo 459783 1556225 := bstep (se 2 (by rfl) ⟨583584, by rfl⟩ : syracuseStep 1556225 = 1167169) B1167169
theorem B2637683 : Blo 459783 2637683 := bstep (se 1 (by rfl) ⟨1978262, by rfl⟩ : syracuseStep 2637683 = 3956525) B3956525
theorem B5914741 : Blo 459783 5914741 := bstep (se 5 (by rfl) ⟨277253, by rfl⟩ : syracuseStep 5914741 = 554507) B554507
theorem B1557035 : Blo 459783 1557035 := bstep (se 1 (by rfl) ⟨1167776, by rfl⟩ : syracuseStep 1557035 = 2335553) B2335553
theorem B737851 : Blo 459783 737851 := bstep (se 1 (by rfl) ⟨553388, by rfl⟩ : syracuseStep 737851 = 1106777) B1106777
theorem B2343491 : Blo 459783 2343491 := bstep (se 1 (by rfl) ⟨1757618, by rfl⟩ : syracuseStep 2343491 = 3515237) B3515237
theorem B3949175 : Blo 459783 3949175 := bstep (se 1 (by rfl) ⟨2961881, by rfl⟩ : syracuseStep 3949175 = 5923763) B5923763
theorem B1163929 : Blo 459783 1163929 := bstep (se 2 (by rfl) ⟨436473, by rfl⟩ : syracuseStep 1163929 = 872947) B872947
theorem B1164091 : Blo 459783 1164091 := bstep (se 1 (by rfl) ⟨873068, by rfl⟩ : syracuseStep 1164091 = 1746137) B1746137
theorem B2802521 : Blo 459783 2802521 := bstep (se 2 (by rfl) ⟨1050945, by rfl⟩ : syracuseStep 2802521 = 2101891) B2101891
theorem B2343815 : Blo 459783 2343815 := bstep (se 1 (by rfl) ⟨1757861, by rfl⟩ : syracuseStep 2343815 = 3515723) B3515723
theorem B1196947 : Blo 459783 1196947 := bstep (se 1 (by rfl) ⟨897710, by rfl⟩ : syracuseStep 1196947 = 1795421) B1795421
theorem B1164233 : Blo 459783 1164233 := bstep (se 2 (by rfl) ⟨436587, by rfl⟩ : syracuseStep 1164233 = 873175) B873175
theorem B1754369 : Blo 459783 1754369 := bstep (se 2 (by rfl) ⟨657888, by rfl⟩ : syracuseStep 1754369 = 1315777) B1315777
theorem B1164577 : Blo 459783 1164577 := bstep (se 2 (by rfl) ⟨436716, by rfl⟩ : syracuseStep 1164577 = 873433) B873433
theorem B2639141 : Blo 459783 2639141 := bstep (se 4 (by rfl) ⟨247419, by rfl⟩ : syracuseStep 2639141 = 494839) B494839
theorem B1558331 : Blo 459783 1558331 := bstep (se 1 (by rfl) ⟨1168748, by rfl⟩ : syracuseStep 1558331 = 2337497) B2337497
theorem B1165175 : Blo 459783 1165175 := bstep (se 1 (by rfl) ⟨873881, by rfl⟩ : syracuseStep 1165175 = 1747763) B1747763
theorem B2640073 : Blo 459783 2640073 := bstep (se 2 (by rfl) ⟨990027, by rfl⟩ : syracuseStep 2640073 = 1980055) B1980055
theorem B1558817 : Blo 459783 1558817 := bstep (se 2 (by rfl) ⟨584556, by rfl⟩ : syracuseStep 1558817 = 1169113) B1169113
theorem B1755539 : Blo 459783 1755539 := bstep (se 1 (by rfl) ⟨1316654, by rfl⟩ : syracuseStep 1755539 = 2633309) B2633309
theorem B3492395 : Blo 459783 3492395 := bstep (se 1 (by rfl) ⟨2619296, by rfl⟩ : syracuseStep 3492395 = 5238593) B5238593
theorem B5065409 : Blo 459783 5065409 := bstep (se 2 (by rfl) ⟨1899528, by rfl⟩ : syracuseStep 5065409 = 3799057) B3799057
theorem B936737 : Blo 459783 936737 := bstep (se 2 (by rfl) ⟨351276, by rfl⟩ : syracuseStep 936737 = 702553) B702553
theorem B1559411 : Blo 459783 1559411 := bstep (se 1 (by rfl) ⟨1169558, by rfl⟩ : syracuseStep 1559411 = 2339117) B2339117
theorem B1035143 : Blo 459783 1035143 := bstep (se 1 (by rfl) ⟨776357, by rfl⟩ : syracuseStep 1035143 = 1552715) B1552715
theorem B1756039 : Blo 459783 1756039 := bstep (se 1 (by rfl) ⟨1317029, by rfl⟩ : syracuseStep 1756039 = 2634059) B2634059
theorem B2214877 : Blo 459783 2214877 := bstep (se 3 (by rfl) ⟨415289, by rfl⟩ : syracuseStep 2214877 = 830579) B830579
theorem B1035323 : Blo 459783 1035323 := bstep (se 1 (by rfl) ⟨776492, by rfl⟩ : syracuseStep 1035323 = 1552985) B1552985
theorem B1166471 : Blo 459783 1166471 := bstep (se 1 (by rfl) ⟨874853, by rfl⟩ : syracuseStep 1166471 = 1749707) B1749707
theorem B1035449 : Blo 459783 1035449 := bstep (se 2 (by rfl) ⟨388293, by rfl⟩ : syracuseStep 1035449 = 776587) B776587
theorem B1166521 : Blo 459783 1166521 := bstep (se 2 (by rfl) ⟨437445, by rfl⟩ : syracuseStep 1166521 = 874891) B874891
theorem B11849165 : Blo 459783 11849165 := bstep (se 3 (by rfl) ⟨2221718, by rfl⟩ : syracuseStep 11849165 = 4443437) B4443437
theorem B1035791 : Blo 459783 1035791 := bstep (se 1 (by rfl) ⟨776843, by rfl⟩ : syracuseStep 1035791 = 1553687) B1553687
theorem B1035809 : Blo 459783 1035809 := bstep (se 2 (by rfl) ⟨388428, by rfl⟩ : syracuseStep 1035809 = 776857) B776857
theorem B8572517 : Blo 459783 8572517 := bstep (se 4 (by rfl) ⟨803673, by rfl⟩ : syracuseStep 8572517 = 1607347) B1607347
theorem B1003193 : Blo 459783 1003193 := bstep (se 2 (by rfl) ⟨376197, by rfl⟩ : syracuseStep 1003193 = 752395) B752395
theorem B1167119 : Blo 459783 1167119 := bstep (se 1 (by rfl) ⟨875339, by rfl⟩ : syracuseStep 1167119 = 1750679) B1750679
theorem B741163 : Blo 459783 741163 := bstep (se 1 (by rfl) ⟨555872, by rfl⟩ : syracuseStep 741163 = 1111745) B1111745
theorem B1036151 : Blo 459783 1036151 := bstep (se 1 (by rfl) ⟨777113, by rfl⟩ : syracuseStep 1036151 = 1554227) B1554227
theorem B1036331 : Blo 459783 1036331 := bstep (se 1 (by rfl) ⟨777248, by rfl⟩ : syracuseStep 1036331 = 1554497) B1554497
theorem B2347379 : Blo 459783 2347379 := bstep (se 1 (by rfl) ⟨1760534, by rfl⟩ : syracuseStep 2347379 = 3521069) B3521069
theorem B1036691 : Blo 459783 1036691 := bstep (se 1 (by rfl) ⟨777518, by rfl⟩ : syracuseStep 1036691 = 1555037) B1555037
theorem B938425 : Blo 459783 938425 := bstep (se 2 (by rfl) ⟨351909, by rfl⟩ : syracuseStep 938425 = 703819) B703819
theorem B1036745 : Blo 459783 1036745 := bstep (se 2 (by rfl) ⟨388779, by rfl⟩ : syracuseStep 1036745 = 777559) B777559
theorem B1167817 : Blo 459783 1167817 := bstep (se 2 (by rfl) ⟨437931, by rfl⟩ : syracuseStep 1167817 = 875863) B875863
theorem B2249227 : Blo 459783 2249227 := bstep (se 1 (by rfl) ⟨1686920, by rfl⟩ : syracuseStep 2249227 = 3373841) B3373841
theorem B872993 : Blo 459783 872993 := bstep (se 2 (by rfl) ⟨327372, by rfl⟩ : syracuseStep 872993 = 654745) B654745
theorem B1167959 : Blo 459783 1167959 := bstep (se 1 (by rfl) ⟨875969, by rfl⟩ : syracuseStep 1167959 = 1751939) B1751939
theorem B2970341 : Blo 459783 2970341 := bstep (se 4 (by rfl) ⟨278469, by rfl⟩ : syracuseStep 2970341 = 556939) B556939
theorem B2347865 : Blo 459783 2347865 := bstep (se 2 (by rfl) ⟨880449, by rfl⟩ : syracuseStep 2347865 = 1760899) B1760899
theorem B873335 : Blo 459783 873335 := bstep (se 1 (by rfl) ⟨655001, by rfl⟩ : syracuseStep 873335 = 1310003) B1310003
theorem B1692683 : Blo 459783 1692683 := bstep (se 1 (by rfl) ⟨1269512, by rfl⟩ : syracuseStep 1692683 = 2539025) B2539025
theorem B1037447 : Blo 459783 1037447 := bstep (se 1 (by rfl) ⟨778085, by rfl⟩ : syracuseStep 1037447 = 1556171) B1556171
theorem B1037627 : Blo 459783 1037627 := bstep (se 1 (by rfl) ⟨778220, by rfl⟩ : syracuseStep 1037627 = 1556441) B1556441
theorem B1562003 : Blo 459783 1562003 := bstep (se 1 (by rfl) ⟨1171502, by rfl⟩ : syracuseStep 1562003 = 2343005) B2343005
theorem B1037753 : Blo 459783 1037753 := bstep (se 2 (by rfl) ⟨389157, by rfl⟩ : syracuseStep 1037753 = 778315) B778315
theorem B1038095 : Blo 459783 1038095 := bstep (se 1 (by rfl) ⟨778571, by rfl⟩ : syracuseStep 1038095 = 1557143) B1557143
theorem B1038113 : Blo 459783 1038113 := bstep (se 2 (by rfl) ⟨389292, by rfl⟩ : syracuseStep 1038113 = 778585) B778585
theorem B2807585 : Blo 459783 2807585 := bstep (se 2 (by rfl) ⟨1052844, by rfl⟩ : syracuseStep 2807585 = 2105689) B2105689
theorem B7460677 : Blo 459783 7460677 := bstep (se 4 (by rfl) ⟨699438, by rfl⟩ : syracuseStep 7460677 = 1398877) B1398877
theorem B9983897 : Blo 459783 9983897 := bstep (se 2 (by rfl) ⟨3743961, by rfl⟩ : syracuseStep 9983897 = 7487923) B7487923
theorem B2218013 : Blo 459783 2218013 := bstep (se 3 (by rfl) ⟨415877, by rfl⟩ : syracuseStep 2218013 = 831755) B831755
theorem B1038455 : Blo 459783 1038455 := bstep (se 1 (by rfl) ⟨778841, by rfl⟩ : syracuseStep 1038455 = 1557683) B1557683
theorem B841999 : Blo 459783 841999 := bstep (se 1 (by rfl) ⟨631499, by rfl⟩ : syracuseStep 841999 = 1262999) B1262999
theorem B4741409 : Blo 459783 4741409 := bstep (se 2 (by rfl) ⟨1778028, by rfl⟩ : syracuseStep 4741409 = 3556057) B3556057
theorem B1038635 : Blo 459783 1038635 := bstep (se 1 (by rfl) ⟨778976, by rfl⟩ : syracuseStep 1038635 = 1557953) B1557953
theorem B776567 : Blo 459783 776567 := bstep (se 1 (by rfl) ⟨582425, by rfl⟩ : syracuseStep 776567 = 1164851) B1164851
theorem B874937 : Blo 459783 874937 := bstep (se 2 (by rfl) ⟨328101, by rfl⟩ : syracuseStep 874937 = 656203) B656203
theorem B1170035 : Blo 459783 1170035 := bstep (se 1 (by rfl) ⟨877526, by rfl⟩ : syracuseStep 1170035 = 1755053) B1755053
theorem B3005047 : Blo 459783 3005047 := bstep (se 1 (by rfl) ⟨2253785, by rfl⟩ : syracuseStep 3005047 = 4507571) B4507571
theorem B1038995 : Blo 459783 1038995 := bstep (se 1 (by rfl) ⟨779246, by rfl⟩ : syracuseStep 1038995 = 1558493) B1558493
theorem B1039049 : Blo 459783 1039049 := bstep (se 2 (by rfl) ⟨389643, by rfl⟩ : syracuseStep 1039049 = 779287) B779287
theorem B875279 : Blo 459783 875279 := bstep (se 1 (by rfl) ⟨656459, by rfl⟩ : syracuseStep 875279 = 1312919) B1312919
theorem B1563407 : Blo 459783 1563407 := bstep (se 1 (by rfl) ⟨1172555, by rfl⟩ : syracuseStep 1563407 = 2345111) B2345111
theorem B777019 : Blo 459783 777019 := bstep (se 1 (by rfl) ⟨582764, by rfl⟩ : syracuseStep 777019 = 1165529) B1165529
theorem B777161 : Blo 459783 777161 := bstep (se 2 (by rfl) ⟨291435, by rfl⟩ : syracuseStep 777161 = 582871) B582871
theorem B1563677 : Blo 459783 1563677 := bstep (se 3 (by rfl) ⟨293189, by rfl⟩ : syracuseStep 1563677 = 586379) B586379
theorem B1170551 : Blo 459783 1170551 := bstep (se 1 (by rfl) ⟨877913, by rfl⟩ : syracuseStep 1170551 = 1755827) B1755827
theorem B1662241 : Blo 459783 1662241 := bstep (se 2 (by rfl) ⟨623340, by rfl⟩ : syracuseStep 1662241 = 1246681) B1246681
theorem B1105267 : Blo 459783 1105267 := bstep (se 1 (by rfl) ⟨828950, by rfl⟩ : syracuseStep 1105267 = 1657901) B1657901
theorem B1039751 : Blo 459783 1039751 := bstep (se 1 (by rfl) ⟨779813, by rfl⟩ : syracuseStep 1039751 = 1559627) B1559627
theorem B876091 : Blo 459783 876091 := bstep (se 1 (by rfl) ⟨657068, by rfl⟩ : syracuseStep 876091 = 1314137) B1314137
theorem B1039931 : Blo 459783 1039931 := bstep (se 1 (by rfl) ⟨779948, by rfl⟩ : syracuseStep 1039931 = 1559897) B1559897
theorem B777863 : Blo 459783 777863 := bstep (se 1 (by rfl) ⟨583397, by rfl⟩ : syracuseStep 777863 = 1166795) B1166795
theorem B876167 : Blo 459783 876167 := bstep (se 1 (by rfl) ⟨657125, by rfl⟩ : syracuseStep 876167 = 1314251) B1314251
theorem B1040057 : Blo 459783 1040057 := bstep (se 2 (by rfl) ⟨390021, by rfl⟩ : syracuseStep 1040057 = 780043) B780043
theorem B3170137 : Blo 459783 3170137 := bstep (se 2 (by rfl) ⟨1188801, by rfl⟩ : syracuseStep 3170137 = 2377603) B2377603
theorem B1040399 : Blo 459783 1040399 := bstep (se 1 (by rfl) ⟨780299, by rfl⟩ : syracuseStep 1040399 = 1560599) B1560599
theorem B8970263 : Blo 459783 8970263 := bstep (se 1 (by rfl) ⟨6727697, by rfl⟩ : syracuseStep 8970263 = 13455395) B13455395
theorem B876577 : Blo 459783 876577 := bstep (se 2 (by rfl) ⟨328716, by rfl⟩ : syracuseStep 876577 = 657433) B657433
theorem B1040417 : Blo 459783 1040417 := bstep (se 2 (by rfl) ⟨390156, by rfl⟩ : syracuseStep 1040417 = 780313) B780313
theorem B1171543 : Blo 459783 1171543 := bstep (se 1 (by rfl) ⟨878657, by rfl⟩ : syracuseStep 1171543 = 1757315) B1757315
theorem B778511 : Blo 459783 778511 := bstep (se 1 (by rfl) ⟨583883, by rfl⟩ : syracuseStep 778511 = 1167767) B1167767
theorem B1663291 : Blo 459783 1663291 := bstep (se 1 (by rfl) ⟨1247468, by rfl⟩ : syracuseStep 1663291 = 2494937) B2494937
theorem B876919 : Blo 459783 876919 := bstep (se 1 (by rfl) ⟨657689, by rfl⟩ : syracuseStep 876919 = 1315379) B1315379
theorem B1040759 : Blo 459783 1040759 := bstep (se 1 (by rfl) ⟨780569, by rfl⟩ : syracuseStep 1040759 = 1561139) B1561139
theorem B1171847 : Blo 459783 1171847 := bstep (se 1 (by rfl) ⟨878885, by rfl⟩ : syracuseStep 1171847 = 1757771) B1757771
theorem B1565081 : Blo 459783 1565081 := bstep (se 2 (by rfl) ⟨586905, by rfl⟩ : syracuseStep 1565081 = 1173811) B1173811
theorem B2220473 : Blo 459783 2220473 := bstep (se 2 (by rfl) ⟨832677, by rfl⟩ : syracuseStep 2220473 = 1665355) B1665355
theorem B1171979 : Blo 459783 1171979 := bstep (se 1 (by rfl) ⟨878984, by rfl⟩ : syracuseStep 1171979 = 1757969) B1757969
theorem B1040939 : Blo 459783 1040939 := bstep (se 1 (by rfl) ⟨780704, by rfl⟩ : syracuseStep 1040939 = 1561409) B1561409
theorem B779051 : Blo 459783 779051 := bstep (se 1 (by rfl) ⟨584288, by rfl⟩ : syracuseStep 779051 = 1168577) B1168577
theorem B1041299 : Blo 459783 1041299 := bstep (se 1 (by rfl) ⟨780974, by rfl⟩ : syracuseStep 1041299 = 1561949) B1561949
theorem B1663897 : Blo 459783 1663897 := bstep (se 2 (by rfl) ⟨623961, by rfl⟩ : syracuseStep 1663897 = 1247923) B1247923
theorem B1041353 : Blo 459783 1041353 := bstep (se 2 (by rfl) ⟨390507, by rfl⟩ : syracuseStep 1041353 = 781015) B781015
theorem B1106959 : Blo 459783 1106959 := bstep (se 1 (by rfl) ⟨830219, by rfl⟩ : syracuseStep 1106959 = 1660439) B1660439
theorem B1172495 : Blo 459783 1172495 := bstep (se 1 (by rfl) ⟨879371, by rfl⟩ : syracuseStep 1172495 = 1758743) B1758743
theorem B1401991 : Blo 459783 1401991 := bstep (se 1 (by rfl) ⟨1051493, by rfl⟩ : syracuseStep 1401991 = 2102987) B2102987
theorem B1172627 : Blo 459783 1172627 := bstep (se 1 (by rfl) ⟨879470, by rfl⟩ : syracuseStep 1172627 = 1758941) B1758941
theorem B779449 : Blo 459783 779449 := bstep (se 2 (by rfl) ⟨292293, by rfl⟩ : syracuseStep 779449 = 584587) B584587
theorem B2254061 : Blo 459783 2254061 := bstep (se 3 (by rfl) ⟨422636, by rfl⟩ : syracuseStep 2254061 = 845273) B845273
theorem B517639 : Blo 459783 517639 := bstep (se 1 (by rfl) ⟨388229, by rfl⟩ : syracuseStep 517639 = 776459) B776459
theorem B1042055 : Blo 459783 1042055 := bstep (se 1 (by rfl) ⟨781541, by rfl⟩ : syracuseStep 1042055 = 1563083) B1563083
theorem B517819 : Blo 459783 517819 := bstep (se 1 (by rfl) ⟨388364, by rfl⟩ : syracuseStep 517819 = 776729) B776729
theorem B1042235 : Blo 459783 1042235 := bstep (se 1 (by rfl) ⟨781676, by rfl⟩ : syracuseStep 1042235 = 1563353) B1563353
theorem B780151 : Blo 459783 780151 := bstep (se 1 (by rfl) ⟨585113, by rfl⟩ : syracuseStep 780151 = 1170227) B1170227
theorem B1402771 : Blo 459783 1402771 := bstep (se 1 (by rfl) ⟨1052078, by rfl⟩ : syracuseStep 1402771 = 2104157) B2104157
theorem B878521 : Blo 459783 878521 := bstep (se 2 (by rfl) ⟨329445, by rfl⟩ : syracuseStep 878521 = 658891) B658891
theorem B1042361 : Blo 459783 1042361 := bstep (se 2 (by rfl) ⟨390885, by rfl⟩ : syracuseStep 1042361 = 781771) B781771
theorem B780347 : Blo 459783 780347 := bstep (se 1 (by rfl) ⟨585260, by rfl⟩ : syracuseStep 780347 = 1170521) B1170521
theorem B518287 : Blo 459783 518287 := bstep (se 1 (by rfl) ⟨388715, by rfl⟩ : syracuseStep 518287 = 777431) B777431
theorem B1108169 : Blo 459783 1108169 := bstep (se 2 (by rfl) ⟨415563, by rfl⟩ : syracuseStep 1108169 = 831127) B831127
theorem B1173761 : Blo 459783 1173761 := bstep (se 2 (by rfl) ⟨440160, by rfl⟩ : syracuseStep 1173761 = 880321) B880321
theorem B878863 : Blo 459783 878863 := bstep (se 1 (by rfl) ⟨659147, by rfl⟩ : syracuseStep 878863 = 1318295) B1318295
theorem B1042703 : Blo 459783 1042703 := bstep (se 1 (by rfl) ⟨782027, by rfl⟩ : syracuseStep 1042703 = 1564055) B1564055
theorem B1042721 : Blo 459783 1042721 := bstep (se 2 (by rfl) ⟨391020, by rfl⟩ : syracuseStep 1042721 = 782041) B782041
theorem B1108343 : Blo 459783 1108343 := bstep (se 1 (by rfl) ⟨831257, by rfl⟩ : syracuseStep 1108343 = 1662515) B1662515
theorem B2222471 : Blo 459783 2222471 := bstep (se 1 (by rfl) ⟨1666853, by rfl⟩ : syracuseStep 2222471 = 3333707) B3333707
theorem B780745 : Blo 459783 780745 := bstep (se 2 (by rfl) ⟨292779, by rfl⟩ : syracuseStep 780745 = 585559) B585559
theorem B1043063 : Blo 459783 1043063 := bstep (se 1 (by rfl) ⟨782297, by rfl⟩ : syracuseStep 1043063 = 1564595) B1564595
theorem B518791 : Blo 459783 518791 := bstep (se 1 (by rfl) ⟨389093, by rfl⟩ : syracuseStep 518791 = 778187) B778187
theorem B584491 : Blo 459783 584491 := bstep (se 1 (by rfl) ⟨438368, by rfl⟩ : syracuseStep 584491 = 876737) B876737
theorem B1043243 : Blo 459783 1043243 := bstep (se 1 (by rfl) ⟨782432, by rfl⟩ : syracuseStep 1043243 = 1564865) B1564865
theorem B518971 : Blo 459783 518971 := bstep (se 1 (by rfl) ⟨389228, by rfl⟩ : syracuseStep 518971 = 778457) B778457
theorem B3501143 : Blo 459783 3501143 := bstep (se 1 (by rfl) ⟨2625857, by rfl⟩ : syracuseStep 3501143 = 5251715) B5251715
theorem B781447 : Blo 459783 781447 := bstep (se 1 (by rfl) ⟨586085, by rfl⟩ : syracuseStep 781447 = 1172171) B1172171
theorem B879751 : Blo 459783 879751 := bstep (se 1 (by rfl) ⟨659813, by rfl⟩ : syracuseStep 879751 = 1319627) B1319627
theorem B519439 : Blo 459783 519439 := bstep (se 1 (by rfl) ⟨389579, by rfl⟩ : syracuseStep 519439 = 779159) B779159
theorem B585463 : Blo 459783 585463 := bstep (se 1 (by rfl) ⟨439097, by rfl⟩ : syracuseStep 585463 = 878195) B878195
theorem B519943 : Blo 459783 519943 := bstep (se 1 (by rfl) ⟨389957, by rfl⟩ : syracuseStep 519943 = 779915) B779915
theorem B782095 : Blo 459783 782095 := bstep (se 1 (by rfl) ⟨586571, by rfl⟩ : syracuseStep 782095 = 1173143) B1173143
theorem B520123 : Blo 459783 520123 := bstep (se 1 (by rfl) ⟨390092, by rfl⟩ : syracuseStep 520123 = 780185) B780185
theorem B585787 : Blo 459783 585787 := bstep (se 1 (by rfl) ⟨439340, by rfl⟩ : syracuseStep 585787 = 878681) B878681
theorem B1110131 : Blo 459783 1110131 := bstep (se 1 (by rfl) ⟨832598, by rfl⟩ : syracuseStep 1110131 = 1665197) B1665197
theorem B782635 : Blo 459783 782635 := bstep (se 1 (by rfl) ⟨586976, by rfl⟩ : syracuseStep 782635 = 1173953) B1173953
theorem B1601927 : Blo 459783 1601927 := bstep (se 1 (by rfl) ⟨1201445, by rfl⟩ : syracuseStep 1601927 = 2402891) B2402891
theorem B520591 : Blo 459783 520591 := bstep (se 1 (by rfl) ⟨390443, by rfl⟩ : syracuseStep 520591 = 780887) B780887
theorem B2224529 : Blo 459783 2224529 := bstep (se 2 (by rfl) ⟨834198, by rfl⟩ : syracuseStep 2224529 = 1668397) B1668397
theorem B1110419 : Blo 459783 1110419 := bstep (se 1 (by rfl) ⟨832814, by rfl⟩ : syracuseStep 1110419 = 1665629) B1665629
theorem B2257645 : Blo 459783 2257645 := bstep (se 3 (by rfl) ⟨423308, by rfl⟩ : syracuseStep 2257645 = 846617) B846617
theorem B521095 : Blo 459783 521095 := bstep (se 1 (by rfl) ⟨390821, by rfl⟩ : syracuseStep 521095 = 781643) B781643
theorem B1110937 : Blo 459783 1110937 := bstep (se 2 (by rfl) ⟨416601, by rfl⟩ : syracuseStep 1110937 = 833203) B833203
theorem B586759 : Blo 459783 586759 := bstep (se 1 (by rfl) ⟨440069, by rfl⟩ : syracuseStep 586759 = 880139) B880139
theorem B2946071 : Blo 459783 2946071 := bstep (se 1 (by rfl) ⟨2209553, by rfl⟩ : syracuseStep 2946071 = 4419107) B4419107
theorem B521275 : Blo 459783 521275 := bstep (se 1 (by rfl) ⟨390956, by rfl⟩ : syracuseStep 521275 = 781913) B781913
theorem B1111553 : Blo 459783 1111553 := bstep (se 2 (by rfl) ⟨416832, by rfl⟩ : syracuseStep 1111553 = 833665) B833665
theorem B521743 : Blo 459783 521743 := bstep (se 1 (by rfl) ⟨391307, by rfl⟩ : syracuseStep 521743 = 782615) B782615
theorem B2815661 : Blo 459783 2815661 := bstep (se 3 (by rfl) ⟨527936, by rfl⟩ : syracuseStep 2815661 = 1055873) B1055873
theorem B2226179 : Blo 459783 2226179 := bstep (se 1 (by rfl) ⟨1669634, by rfl⟩ : syracuseStep 2226179 = 3339269) B3339269
theorem B2619479 : Blo 459783 2619479 := bstep (se 1 (by rfl) ⟨1964609, by rfl⟩ : syracuseStep 2619479 = 3929219) B3929219
theorem B1964321 : Blo 459783 1964321 := bstep (se 2 (by rfl) ⟨736620, by rfl⟩ : syracuseStep 1964321 = 1473241) B1473241
theorem B1112591 : Blo 459783 1112591 := bstep (se 1 (by rfl) ⟨834443, by rfl⟩ : syracuseStep 1112591 = 1668887) B1668887
theorem B2062967 : Blo 459783 2062967 := bstep (se 1 (by rfl) ⟨1547225, by rfl⟩ : syracuseStep 2062967 = 3094451) B3094451
theorem B3930929 : Blo 459783 3930929 := bstep (se 2 (by rfl) ⟨1474098, by rfl⟩ : syracuseStep 3930929 = 2948197) B2948197
theorem B5340107 : Blo 459783 5340107 := bstep (se 1 (by rfl) ⟨4005080, by rfl⟩ : syracuseStep 5340107 = 8010161) B8010161
theorem B2816977 : Blo 459783 2816977 := bstep (se 2 (by rfl) ⟨1056366, by rfl⟩ : syracuseStep 2816977 = 2112733) B2112733
theorem B1408001 : Blo 459783 1408001 := bstep (se 2 (by rfl) ⟨528000, by rfl⟩ : syracuseStep 1408001 = 1056001) B1056001
theorem B1309729 : Blo 459783 1309729 := bstep (se 2 (by rfl) ⟨491148, by rfl⟩ : syracuseStep 1309729 = 982297) B982297
theorem B1965293 : Blo 459783 1965293 := bstep (se 3 (by rfl) ⟨368492, by rfl⟩ : syracuseStep 1965293 = 736985) B736985
theorem B4750609 : Blo 459783 4750609 := bstep (se 2 (by rfl) ⟨1781478, by rfl⟩ : syracuseStep 4750609 = 3562957) B3562957
theorem B18513197 : Blo 459783 18513197 := bstep (se 3 (by rfl) ⟨3471224, by rfl⟩ : syracuseStep 18513197 = 6942449) B6942449
theorem B4455739 : Blo 459783 4455739 := bstep (se 1 (by rfl) ⟨3341804, by rfl⟩ : syracuseStep 4455739 = 6683609) B6683609
theorem B1310219 : Blo 459783 1310219 := bstep (se 1 (by rfl) ⟨982664, by rfl⟩ : syracuseStep 1310219 = 1965329) B1965329
theorem B8027747 : Blo 459783 8027747 := bstep (se 1 (by rfl) ⟨6020810, by rfl⟩ : syracuseStep 8027747 = 12041621) B12041621
theorem B1244873 : Blo 459783 1244873 := bstep (se 2 (by rfl) ⟨466827, by rfl⟩ : syracuseStep 1244873 = 933655) B933655
theorem B1114003 : Blo 459783 1114003 := bstep (se 1 (by rfl) ⟨835502, by rfl⟩ : syracuseStep 1114003 = 1671005) B1671005
theorem B1965977 : Blo 459783 1965977 := bstep (se 2 (by rfl) ⟨737241, by rfl⟩ : syracuseStep 1965977 = 1474483) B1474483
theorem B2817995 : Blo 459783 2817995 := bstep (se 1 (by rfl) ⟨2113496, by rfl⟩ : syracuseStep 2817995 = 4226993) B4226993
theorem B2621393 : Blo 459783 2621393 := bstep (se 2 (by rfl) ⟨983022, by rfl⟩ : syracuseStep 2621393 = 1966045) B1966045
theorem B983801 : Blo 459783 983801 := bstep (se 2 (by rfl) ⟨368925, by rfl⟩ : syracuseStep 983801 = 737851) B737851
theorem B787295 : Blo 459783 787295 := bstep (se 1 (by rfl) ⟨590471, by rfl⟩ : syracuseStep 787295 = 1180943) B1180943
theorem B1573793 : Blo 459783 1573793 := bstep (se 2 (by rfl) ⟨590172, by rfl⟩ : syracuseStep 1573793 = 1180345) B1180345
theorem B1967105 : Blo 459783 1967105 := bstep (se 2 (by rfl) ⟨737664, by rfl⟩ : syracuseStep 1967105 = 1475329) B1475329
theorem B459815 : Blo 459783 459815 := bstep (se 1 (by rfl) ⟨344861, by rfl⟩ : syracuseStep 459815 = 689723) B689723
theorem B2950195 : Blo 459783 2950195 := bstep (se 1 (by rfl) ⟨2212646, by rfl⟩ : syracuseStep 2950195 = 4425293) B4425293
theorem B15205427 : Blo 459783 15205427 := bstep (se 1 (by rfl) ⟨11404070, by rfl⟩ : syracuseStep 15205427 = 22808141) B22808141
theorem B459855 : Blo 459783 459855 := bstep (se 1 (by rfl) ⟨344891, by rfl⟩ : syracuseStep 459855 = 689783) B689783
theorem B984143 : Blo 459783 984143 := bstep (se 1 (by rfl) ⟨738107, by rfl⟩ : syracuseStep 984143 = 1476215) B1476215
theorem B459871 : Blo 459783 459871 := bstep (se 1 (by rfl) ⟨344903, by rfl⟩ : syracuseStep 459871 = 689807) B689807
theorem B459899 : Blo 459783 459899 := bstep (se 1 (by rfl) ⟨344924, by rfl⟩ : syracuseStep 459899 = 689849) B689849
theorem B459951 : Blo 459783 459951 := bstep (se 1 (by rfl) ⟨344963, by rfl⟩ : syracuseStep 459951 = 689927) B689927
theorem B459975 : Blo 459783 459975 := bstep (se 1 (by rfl) ⟨344981, by rfl⟩ : syracuseStep 459975 = 689963) B689963
theorem B459995 : Blo 459783 459995 := bstep (se 1 (by rfl) ⟨344996, by rfl⟩ : syracuseStep 459995 = 689993) B689993
theorem B460071 : Blo 459783 460071 := bstep (se 1 (by rfl) ⟨345053, by rfl⟩ : syracuseStep 460071 = 690107) B690107
theorem B460111 : Blo 459783 460111 := bstep (se 1 (by rfl) ⟨345083, by rfl⟩ : syracuseStep 460111 = 690167) B690167
theorem B460127 : Blo 459783 460127 := bstep (se 1 (by rfl) ⟨345095, by rfl⟩ : syracuseStep 460127 = 690191) B690191
theorem B1475945 : Blo 459783 1475945 := bstep (se 2 (by rfl) ⟨553479, by rfl⟩ : syracuseStep 1475945 = 1106959) B1106959
theorem B460155 : Blo 459783 460155 := bstep (se 1 (by rfl) ⟨345116, by rfl⟩ : syracuseStep 460155 = 690233) B690233
theorem B460207 : Blo 459783 460207 := bstep (se 1 (by rfl) ⟨345155, by rfl⟩ : syracuseStep 460207 = 690311) B690311
theorem B460231 : Blo 459783 460231 := bstep (se 1 (by rfl) ⟨345173, by rfl⟩ : syracuseStep 460231 = 690347) B690347
theorem B460251 : Blo 459783 460251 := bstep (se 1 (by rfl) ⟨345188, by rfl⟩ : syracuseStep 460251 = 690377) B690377
theorem B460327 : Blo 459783 460327 := bstep (se 1 (by rfl) ⟨345245, by rfl⟩ : syracuseStep 460327 = 690491) B690491
theorem B460367 : Blo 459783 460367 := bstep (se 1 (by rfl) ⟨345275, by rfl⟩ : syracuseStep 460367 = 690551) B690551
theorem B460383 : Blo 459783 460383 := bstep (se 1 (by rfl) ⟨345287, by rfl⟩ : syracuseStep 460383 = 690575) B690575
theorem B460411 : Blo 459783 460411 := bstep (se 1 (by rfl) ⟨345308, by rfl⟩ : syracuseStep 460411 = 690617) B690617
theorem B460463 : Blo 459783 460463 := bstep (se 1 (by rfl) ⟨345347, by rfl⟩ : syracuseStep 460463 = 690695) B690695
theorem B2328263 : Blo 459783 2328263 := bstep (se 1 (by rfl) ⟨1746197, by rfl⟩ : syracuseStep 2328263 = 3492395) B3492395
theorem B460487 : Blo 459783 460487 := bstep (se 1 (by rfl) ⟨345365, by rfl⟩ : syracuseStep 460487 = 690731) B690731
theorem B460507 : Blo 459783 460507 := bstep (se 1 (by rfl) ⟨345380, by rfl⟩ : syracuseStep 460507 = 690761) B690761
theorem B460583 : Blo 459783 460583 := bstep (se 1 (by rfl) ⟨345437, by rfl⟩ : syracuseStep 460583 = 690875) B690875
theorem B3376939 : Blo 459783 3376939 := bstep (se 1 (by rfl) ⟨2532704, by rfl⟩ : syracuseStep 3376939 = 5065409) B5065409
theorem B460623 : Blo 459783 460623 := bstep (se 1 (by rfl) ⟨345467, by rfl⟩ : syracuseStep 460623 = 690935) B690935
theorem B460639 : Blo 459783 460639 := bstep (se 1 (by rfl) ⟨345479, by rfl⟩ : syracuseStep 460639 = 690959) B690959
theorem B624491 : Blo 459783 624491 := bstep (se 1 (by rfl) ⟨468368, by rfl⟩ : syracuseStep 624491 = 936737) B936737
theorem B460667 : Blo 459783 460667 := bstep (se 1 (by rfl) ⟨345500, by rfl⟩ : syracuseStep 460667 = 691001) B691001
theorem B690095 : Blo 459783 690095 := bstep (se 1 (by rfl) ⟨517571, by rfl⟩ : syracuseStep 690095 = 1035143) B1035143
theorem B460719 : Blo 459783 460719 := bstep (se 1 (by rfl) ⟨345539, by rfl⟩ : syracuseStep 460719 = 691079) B691079
theorem B460743 : Blo 459783 460743 := bstep (se 1 (by rfl) ⟨345557, by rfl⟩ : syracuseStep 460743 = 691115) B691115
theorem B460763 : Blo 459783 460763 := bstep (se 1 (by rfl) ⟨345572, by rfl⟩ : syracuseStep 460763 = 691145) B691145
theorem B690185 : Blo 459783 690185 := bstep (se 2 (by rfl) ⟨258819, by rfl⟩ : syracuseStep 690185 = 517639) B517639
theorem B690215 : Blo 459783 690215 := bstep (se 1 (by rfl) ⟨517661, by rfl⟩ : syracuseStep 690215 = 1035323) B1035323
theorem B460839 : Blo 459783 460839 := bstep (se 1 (by rfl) ⟨345629, by rfl⟩ : syracuseStep 460839 = 691259) B691259
theorem B460879 : Blo 459783 460879 := bstep (se 1 (by rfl) ⟨345659, by rfl⟩ : syracuseStep 460879 = 691319) B691319
theorem B460895 : Blo 459783 460895 := bstep (se 1 (by rfl) ⟨345671, by rfl⟩ : syracuseStep 460895 = 691343) B691343
theorem B690299 : Blo 459783 690299 := bstep (se 1 (by rfl) ⟨517724, by rfl⟩ : syracuseStep 690299 = 1035449) B1035449
theorem B460923 : Blo 459783 460923 := bstep (se 1 (by rfl) ⟨345692, by rfl⟩ : syracuseStep 460923 = 691385) B691385
theorem B8390789 : Blo 459783 8390789 := bstep (se 4 (by rfl) ⟨786636, by rfl⟩ : syracuseStep 8390789 = 1573273) B1573273
theorem B460975 : Blo 459783 460975 := bstep (se 1 (by rfl) ⟨345731, by rfl⟩ : syracuseStep 460975 = 691463) B691463
theorem B460999 : Blo 459783 460999 := bstep (se 1 (by rfl) ⟨345749, by rfl⟩ : syracuseStep 460999 = 691499) B691499
theorem B461019 : Blo 459783 461019 := bstep (se 1 (by rfl) ⟨345764, by rfl⟩ : syracuseStep 461019 = 691529) B691529
theorem B7473389 : Blo 459783 7473389 := bstep (se 3 (by rfl) ⟨1401260, by rfl⟩ : syracuseStep 7473389 = 2802521) B2802521
theorem B690425 : Blo 459783 690425 := bstep (se 2 (by rfl) ⟨258909, by rfl⟩ : syracuseStep 690425 = 517819) B517819
theorem B461095 : Blo 459783 461095 := bstep (se 1 (by rfl) ⟨345821, by rfl⟩ : syracuseStep 461095 = 691643) B691643
theorem B7899443 : Blo 459783 7899443 := bstep (se 1 (by rfl) ⟨5924582, by rfl⟩ : syracuseStep 7899443 = 11849165) B11849165
theorem B461135 : Blo 459783 461135 := bstep (se 1 (by rfl) ⟨345851, by rfl⟩ : syracuseStep 461135 = 691703) B691703
theorem B690527 : Blo 459783 690527 := bstep (se 1 (by rfl) ⟨517895, by rfl⟩ : syracuseStep 690527 = 1035791) B1035791
theorem B461151 : Blo 459783 461151 := bstep (se 1 (by rfl) ⟨345863, by rfl⟩ : syracuseStep 461151 = 691727) B691727
theorem B690539 : Blo 459783 690539 := bstep (se 1 (by rfl) ⟨517904, by rfl⟩ : syracuseStep 690539 = 1035809) B1035809
theorem B461179 : Blo 459783 461179 := bstep (se 1 (by rfl) ⟨345884, by rfl⟩ : syracuseStep 461179 = 691769) B691769
theorem B461231 : Blo 459783 461231 := bstep (se 1 (by rfl) ⟨345923, by rfl⟩ : syracuseStep 461231 = 691847) B691847
theorem B461255 : Blo 459783 461255 := bstep (se 1 (by rfl) ⟨345941, by rfl⟩ : syracuseStep 461255 = 691883) B691883
theorem B461275 : Blo 459783 461275 := bstep (se 1 (by rfl) ⟨345956, by rfl⟩ : syracuseStep 461275 = 691913) B691913
theorem B1870361 : Blo 459783 1870361 := bstep (se 2 (by rfl) ⟨701385, by rfl⟩ : syracuseStep 1870361 = 1402771) B1402771
theorem B789031 : Blo 459783 789031 := bstep (se 1 (by rfl) ⟨591773, by rfl⟩ : syracuseStep 789031 = 1183547) B1183547
theorem B461351 : Blo 459783 461351 := bstep (se 1 (by rfl) ⟨346013, by rfl⟩ : syracuseStep 461351 = 692027) B692027
theorem B690767 : Blo 459783 690767 := bstep (se 1 (by rfl) ⟨518075, by rfl⟩ : syracuseStep 690767 = 1036151) B1036151
theorem B461391 : Blo 459783 461391 := bstep (se 1 (by rfl) ⟨346043, by rfl⟩ : syracuseStep 461391 = 692087) B692087
theorem B461407 : Blo 459783 461407 := bstep (se 1 (by rfl) ⟨346055, by rfl⟩ : syracuseStep 461407 = 692111) B692111
theorem B461435 : Blo 459783 461435 := bstep (se 1 (by rfl) ⟨346076, by rfl⟩ : syracuseStep 461435 = 692153) B692153
theorem B461487 : Blo 459783 461487 := bstep (se 1 (by rfl) ⟨346115, by rfl⟩ : syracuseStep 461487 = 692231) B692231
theorem B690887 : Blo 459783 690887 := bstep (se 1 (by rfl) ⟨518165, by rfl⟩ : syracuseStep 690887 = 1036331) B1036331
theorem B461511 : Blo 459783 461511 := bstep (se 1 (by rfl) ⟨346133, by rfl⟩ : syracuseStep 461511 = 692267) B692267
theorem B461531 : Blo 459783 461531 := bstep (se 1 (by rfl) ⟨346148, by rfl⟩ : syracuseStep 461531 = 692297) B692297
theorem B11995877 : Blo 459783 11995877 := bstep (se 4 (by rfl) ⟨1124613, by rfl⟩ : syracuseStep 11995877 = 2249227) B2249227
theorem B461607 : Blo 459783 461607 := bstep (se 1 (by rfl) ⟨346205, by rfl⟩ : syracuseStep 461607 = 692411) B692411
theorem B461647 : Blo 459783 461647 := bstep (se 1 (by rfl) ⟨346235, by rfl⟩ : syracuseStep 461647 = 692471) B692471
theorem B461663 : Blo 459783 461663 := bstep (se 1 (by rfl) ⟨346247, by rfl⟩ : syracuseStep 461663 = 692495) B692495
theorem B691049 : Blo 459783 691049 := bstep (se 2 (by rfl) ⟨259143, by rfl⟩ : syracuseStep 691049 = 518287) B518287
theorem B461691 : Blo 459783 461691 := bstep (se 1 (by rfl) ⟨346268, by rfl⟩ : syracuseStep 461691 = 692537) B692537
theorem B461743 : Blo 459783 461743 := bstep (se 1 (by rfl) ⟨346307, by rfl⟩ : syracuseStep 461743 = 692615) B692615
theorem B691127 : Blo 459783 691127 := bstep (se 1 (by rfl) ⟨518345, by rfl⟩ : syracuseStep 691127 = 1036691) B1036691
theorem B461767 : Blo 459783 461767 := bstep (se 1 (by rfl) ⟨346325, by rfl⟩ : syracuseStep 461767 = 692651) B692651
theorem B691163 : Blo 459783 691163 := bstep (se 1 (by rfl) ⟨518372, by rfl⟩ : syracuseStep 691163 = 1036745) B1036745
theorem B461787 : Blo 459783 461787 := bstep (se 1 (by rfl) ⟨346340, by rfl⟩ : syracuseStep 461787 = 692681) B692681
theorem B461863 : Blo 459783 461863 := bstep (se 1 (by rfl) ⟨346397, by rfl⟩ : syracuseStep 461863 = 692795) B692795
theorem B461903 : Blo 459783 461903 := bstep (se 1 (by rfl) ⟨346427, by rfl⟩ : syracuseStep 461903 = 692855) B692855
theorem B461919 : Blo 459783 461919 := bstep (se 1 (by rfl) ⟨346439, by rfl⟩ : syracuseStep 461919 = 692879) B692879
theorem B461947 : Blo 459783 461947 := bstep (se 1 (by rfl) ⟨346460, by rfl⟩ : syracuseStep 461947 = 692921) B692921
theorem B1576093 : Blo 459783 1576093 := bstep (se 3 (by rfl) ⟨295517, by rfl⟩ : syracuseStep 1576093 = 591035) B591035
theorem B461999 : Blo 459783 461999 := bstep (se 1 (by rfl) ⟨346499, by rfl⟩ : syracuseStep 461999 = 692999) B692999
theorem B7015619 : Blo 459783 7015619 := bstep (se 1 (by rfl) ⟨5261714, by rfl⟩ : syracuseStep 7015619 = 10523429) B10523429
theorem B462023 : Blo 459783 462023 := bstep (se 1 (by rfl) ⟨346517, by rfl⟩ : syracuseStep 462023 = 693035) B693035
theorem B462043 : Blo 459783 462043 := bstep (se 1 (by rfl) ⟨346532, by rfl⟩ : syracuseStep 462043 = 693065) B693065
theorem B16026917 : Blo 459783 16026917 := bstep (se 4 (by rfl) ⟨1502523, by rfl⟩ : syracuseStep 16026917 = 3005047) B3005047
theorem B462119 : Blo 459783 462119 := bstep (se 1 (by rfl) ⟨346589, by rfl⟩ : syracuseStep 462119 = 693179) B693179
theorem B462159 : Blo 459783 462159 := bstep (se 1 (by rfl) ⟨346619, by rfl⟩ : syracuseStep 462159 = 693239) B693239
theorem B462175 : Blo 459783 462175 := bstep (se 1 (by rfl) ⟨346631, by rfl⟩ : syracuseStep 462175 = 693263) B693263
theorem B658783 : Blo 459783 658783 := bstep (se 1 (by rfl) ⟨494087, by rfl⟩ : syracuseStep 658783 = 988175) B988175
theorem B462203 : Blo 459783 462203 := bstep (se 1 (by rfl) ⟨346652, by rfl⟩ : syracuseStep 462203 = 693305) B693305
theorem B2133373 : Blo 459783 2133373 := bstep (se 3 (by rfl) ⟨400007, by rfl⟩ : syracuseStep 2133373 = 800015) B800015
theorem B1248637 : Blo 459783 1248637 := bstep (se 3 (by rfl) ⟨234119, by rfl⟩ : syracuseStep 1248637 = 468239) B468239
theorem B691631 : Blo 459783 691631 := bstep (se 1 (by rfl) ⟨518723, by rfl⟩ : syracuseStep 691631 = 1037447) B1037447
theorem B462255 : Blo 459783 462255 := bstep (se 1 (by rfl) ⟨346691, by rfl⟩ : syracuseStep 462255 = 693383) B693383
theorem B462279 : Blo 459783 462279 := bstep (se 1 (by rfl) ⟨346709, by rfl⟩ : syracuseStep 462279 = 693419) B693419
theorem B462299 : Blo 459783 462299 := bstep (se 1 (by rfl) ⟨346724, by rfl⟩ : syracuseStep 462299 = 693449) B693449
theorem B691721 : Blo 459783 691721 := bstep (se 2 (by rfl) ⟨259395, by rfl⟩ : syracuseStep 691721 = 518791) B518791
theorem B1969703 : Blo 459783 1969703 := bstep (se 1 (by rfl) ⟨1477277, by rfl⟩ : syracuseStep 1969703 = 2954555) B2954555
theorem B691751 : Blo 459783 691751 := bstep (se 1 (by rfl) ⟨518813, by rfl⟩ : syracuseStep 691751 = 1037627) B1037627
theorem B462375 : Blo 459783 462375 := bstep (se 1 (by rfl) ⟨346781, by rfl⟩ : syracuseStep 462375 = 693563) B693563
theorem B462415 : Blo 459783 462415 := bstep (se 1 (by rfl) ⟨346811, by rfl⟩ : syracuseStep 462415 = 693623) B693623
theorem B462431 : Blo 459783 462431 := bstep (se 1 (by rfl) ⟨346823, by rfl⟩ : syracuseStep 462431 = 693647) B693647
theorem B691835 : Blo 459783 691835 := bstep (se 1 (by rfl) ⟨518876, by rfl⟩ : syracuseStep 691835 = 1037753) B1037753
theorem B986747 : Blo 459783 986747 := bstep (se 1 (by rfl) ⟨740060, by rfl⟩ : syracuseStep 986747 = 1480121) B1480121
theorem B462459 : Blo 459783 462459 := bstep (se 1 (by rfl) ⟨346844, by rfl⟩ : syracuseStep 462459 = 693689) B693689
theorem B462511 : Blo 459783 462511 := bstep (se 1 (by rfl) ⟨346883, by rfl⟩ : syracuseStep 462511 = 693767) B693767
theorem B462535 : Blo 459783 462535 := bstep (se 1 (by rfl) ⟨346901, by rfl⟩ : syracuseStep 462535 = 693803) B693803
theorem B462555 : Blo 459783 462555 := bstep (se 1 (by rfl) ⟨346916, by rfl⟩ : syracuseStep 462555 = 693833) B693833
theorem B691961 : Blo 459783 691961 := bstep (se 2 (by rfl) ⟨259485, by rfl⟩ : syracuseStep 691961 = 518971) B518971
theorem B462631 : Blo 459783 462631 := bstep (se 1 (by rfl) ⟨346973, by rfl⟩ : syracuseStep 462631 = 693947) B693947
theorem B462671 : Blo 459783 462671 := bstep (se 1 (by rfl) ⟨347003, by rfl⟩ : syracuseStep 462671 = 694007) B694007
theorem B692063 : Blo 459783 692063 := bstep (se 1 (by rfl) ⟨519047, by rfl⟩ : syracuseStep 692063 = 1038095) B1038095
theorem B462687 : Blo 459783 462687 := bstep (se 1 (by rfl) ⟨347015, by rfl⟩ : syracuseStep 462687 = 694031) B694031
theorem B692075 : Blo 459783 692075 := bstep (se 1 (by rfl) ⟨519056, by rfl⟩ : syracuseStep 692075 = 1038113) B1038113
theorem B1871723 : Blo 459783 1871723 := bstep (se 1 (by rfl) ⟨1403792, by rfl⟩ : syracuseStep 1871723 = 2807585) B2807585
theorem B986987 : Blo 459783 986987 := bstep (se 1 (by rfl) ⟨740240, by rfl⟩ : syracuseStep 986987 = 1480481) B1480481
theorem B462715 : Blo 459783 462715 := bstep (se 1 (by rfl) ⟨347036, by rfl⟩ : syracuseStep 462715 = 694073) B694073
theorem B1249199 : Blo 459783 1249199 := bstep (se 1 (by rfl) ⟨936899, by rfl⟩ : syracuseStep 1249199 = 1873799) B1873799
theorem B462767 : Blo 459783 462767 := bstep (se 1 (by rfl) ⟨347075, by rfl⟩ : syracuseStep 462767 = 694151) B694151
theorem B6655931 : Blo 459783 6655931 := bstep (se 1 (by rfl) ⟨4991948, by rfl⟩ : syracuseStep 6655931 = 9983897) B9983897
theorem B462791 : Blo 459783 462791 := bstep (se 1 (by rfl) ⟨347093, by rfl⟩ : syracuseStep 462791 = 694187) B694187
theorem B2953169 : Blo 459783 2953169 := bstep (se 2 (by rfl) ⟨1107438, by rfl⟩ : syracuseStep 2953169 = 2214877) B2214877
theorem B462811 : Blo 459783 462811 := bstep (se 1 (by rfl) ⟨347108, by rfl⟩ : syracuseStep 462811 = 694217) B694217
theorem B1478675 : Blo 459783 1478675 := bstep (se 1 (by rfl) ⟨1109006, by rfl⟩ : syracuseStep 1478675 = 2218013) B2218013
theorem B462887 : Blo 459783 462887 := bstep (se 1 (by rfl) ⟨347165, by rfl⟩ : syracuseStep 462887 = 694331) B694331
theorem B692303 : Blo 459783 692303 := bstep (se 1 (by rfl) ⟨519227, by rfl⟩ : syracuseStep 692303 = 1038455) B1038455
theorem B462927 : Blo 459783 462927 := bstep (se 1 (by rfl) ⟨347195, by rfl⟩ : syracuseStep 462927 = 694391) B694391
theorem B462943 : Blo 459783 462943 := bstep (se 1 (by rfl) ⟨347207, by rfl⟩ : syracuseStep 462943 = 694415) B694415
theorem B462971 : Blo 459783 462971 := bstep (se 1 (by rfl) ⟨347228, by rfl⟩ : syracuseStep 462971 = 694457) B694457
theorem B463023 : Blo 459783 463023 := bstep (se 1 (by rfl) ⟨347267, by rfl⟩ : syracuseStep 463023 = 694535) B694535
theorem B692423 : Blo 459783 692423 := bstep (se 1 (by rfl) ⟨519317, by rfl⟩ : syracuseStep 692423 = 1038635) B1038635
theorem B463047 : Blo 459783 463047 := bstep (se 1 (by rfl) ⟨347285, by rfl⟩ : syracuseStep 463047 = 694571) B694571
theorem B463067 : Blo 459783 463067 := bstep (se 1 (by rfl) ⟨347300, by rfl⟩ : syracuseStep 463067 = 694601) B694601
theorem B463143 : Blo 459783 463143 := bstep (se 1 (by rfl) ⟨347357, by rfl⟩ : syracuseStep 463143 = 694715) B694715
theorem B463183 : Blo 459783 463183 := bstep (se 1 (by rfl) ⟨347387, by rfl⟩ : syracuseStep 463183 = 694775) B694775
theorem B463199 : Blo 459783 463199 := bstep (se 1 (by rfl) ⟨347399, by rfl⟩ : syracuseStep 463199 = 694799) B694799
theorem B692585 : Blo 459783 692585 := bstep (se 2 (by rfl) ⟨259719, by rfl⟩ : syracuseStep 692585 = 519439) B519439
theorem B463227 : Blo 459783 463227 := bstep (se 1 (by rfl) ⟨347420, by rfl⟩ : syracuseStep 463227 = 694841) B694841
theorem B463279 : Blo 459783 463279 := bstep (se 1 (by rfl) ⟨347459, by rfl⟩ : syracuseStep 463279 = 694919) B694919
theorem B692663 : Blo 459783 692663 := bstep (se 1 (by rfl) ⟨519497, by rfl⟩ : syracuseStep 692663 = 1038995) B1038995
theorem B463303 : Blo 459783 463303 := bstep (se 1 (by rfl) ⟨347477, by rfl⟩ : syracuseStep 463303 = 694955) B694955
theorem B692699 : Blo 459783 692699 := bstep (se 1 (by rfl) ⟨519524, by rfl⟩ : syracuseStep 692699 = 1039049) B1039049
theorem B463323 : Blo 459783 463323 := bstep (se 1 (by rfl) ⟨347492, by rfl⟩ : syracuseStep 463323 = 694985) B694985
theorem B463399 : Blo 459783 463399 := bstep (se 1 (by rfl) ⟨347549, by rfl⟩ : syracuseStep 463399 = 695099) B695099
theorem B463439 : Blo 459783 463439 := bstep (se 1 (by rfl) ⟨347579, by rfl⟩ : syracuseStep 463439 = 695159) B695159
theorem B463455 : Blo 459783 463455 := bstep (se 1 (by rfl) ⟨347591, by rfl⟩ : syracuseStep 463455 = 695183) B695183
theorem B1053281 : Blo 459783 1053281 := bstep (se 2 (by rfl) ⟨394980, by rfl⟩ : syracuseStep 1053281 = 789961) B789961
theorem B5345909 : Blo 459783 5345909 := bstep (se 5 (by rfl) ⟨250589, by rfl⟩ : syracuseStep 5345909 = 501179) B501179
theorem B463483 : Blo 459783 463483 := bstep (se 1 (by rfl) ⟨347612, by rfl⟩ : syracuseStep 463483 = 695225) B695225
theorem B463535 : Blo 459783 463535 := bstep (se 1 (by rfl) ⟨347651, by rfl⟩ : syracuseStep 463535 = 695303) B695303
theorem B463559 : Blo 459783 463559 := bstep (se 1 (by rfl) ⟨347669, by rfl⟩ : syracuseStep 463559 = 695339) B695339
theorem B463579 : Blo 459783 463579 := bstep (se 1 (by rfl) ⟨347684, by rfl⟩ : syracuseStep 463579 = 695369) B695369
theorem B463655 : Blo 459783 463655 := bstep (se 1 (by rfl) ⟨347741, by rfl⟩ : syracuseStep 463655 = 695483) B695483
theorem B463695 : Blo 459783 463695 := bstep (se 1 (by rfl) ⟨347771, by rfl⟩ : syracuseStep 463695 = 695543) B695543
theorem B463711 : Blo 459783 463711 := bstep (se 1 (by rfl) ⟨347783, by rfl⟩ : syracuseStep 463711 = 695567) B695567
theorem B463739 : Blo 459783 463739 := bstep (se 1 (by rfl) ⟨347804, by rfl⟩ : syracuseStep 463739 = 695609) B695609
theorem B693167 : Blo 459783 693167 := bstep (se 1 (by rfl) ⟨519875, by rfl⟩ : syracuseStep 693167 = 1039751) B1039751
theorem B693257 : Blo 459783 693257 := bstep (se 2 (by rfl) ⟨259971, by rfl⟩ : syracuseStep 693257 = 519943) B519943
theorem B693287 : Blo 459783 693287 := bstep (se 1 (by rfl) ⟨519965, by rfl⟩ : syracuseStep 693287 = 1039931) B1039931
theorem B988217 : Blo 459783 988217 := bstep (se 2 (by rfl) ⟨370581, by rfl⟩ : syracuseStep 988217 = 741163) B741163
theorem B693371 : Blo 459783 693371 := bstep (se 1 (by rfl) ⟨520028, by rfl⟩ : syracuseStep 693371 = 1040057) B1040057
theorem B693497 : Blo 459783 693497 := bstep (se 2 (by rfl) ⟨260061, by rfl⟩ : syracuseStep 693497 = 520123) B520123
theorem B890185 : Blo 459783 890185 := bstep (se 2 (by rfl) ⟨333819, by rfl⟩ : syracuseStep 890185 = 667639) B667639
theorem B693599 : Blo 459783 693599 := bstep (se 1 (by rfl) ⟨520199, by rfl⟩ : syracuseStep 693599 = 1040399) B1040399
theorem B693611 : Blo 459783 693611 := bstep (se 1 (by rfl) ⟨520208, by rfl⟩ : syracuseStep 693611 = 1040417) B1040417
theorem B693839 : Blo 459783 693839 := bstep (se 1 (by rfl) ⟨520379, by rfl⟩ : syracuseStep 693839 = 1040759) B1040759
theorem B1480315 : Blo 459783 1480315 := bstep (se 1 (by rfl) ⟨1110236, by rfl⟩ : syracuseStep 1480315 = 2220473) B2220473
theorem B693959 : Blo 459783 693959 := bstep (se 1 (by rfl) ⟨520469, by rfl⟩ : syracuseStep 693959 = 1040939) B1040939
theorem B1578707 : Blo 459783 1578707 := bstep (se 1 (by rfl) ⟨1184030, by rfl⟩ : syracuseStep 1578707 = 2368061) B2368061
theorem B694121 : Blo 459783 694121 := bstep (se 2 (by rfl) ⟨260295, by rfl⟩ : syracuseStep 694121 = 520591) B520591
theorem B1251179 : Blo 459783 1251179 := bstep (se 1 (by rfl) ⟨938384, by rfl⟩ : syracuseStep 1251179 = 1876769) B1876769
theorem B1251233 : Blo 459783 1251233 := bstep (se 2 (by rfl) ⟨469212, by rfl⟩ : syracuseStep 1251233 = 938425) B938425
theorem B694199 : Blo 459783 694199 := bstep (se 1 (by rfl) ⟨520649, by rfl⟩ : syracuseStep 694199 = 1041299) B1041299
theorem B694235 : Blo 459783 694235 := bstep (se 1 (by rfl) ⟨520676, by rfl⟩ : syracuseStep 694235 = 1041353) B1041353
theorem B7477285 : Blo 459783 7477285 := bstep (se 4 (by rfl) ⟨700995, by rfl⟩ : syracuseStep 7477285 = 1401991) B1401991
theorem B694703 : Blo 459783 694703 := bstep (se 1 (by rfl) ⟨521027, by rfl⟩ : syracuseStep 694703 = 1042055) B1042055
theorem B694793 : Blo 459783 694793 := bstep (se 2 (by rfl) ⟨260547, by rfl⟩ : syracuseStep 694793 = 521095) B521095
theorem B1481249 : Blo 459783 1481249 := bstep (se 2 (by rfl) ⟨555468, by rfl⟩ : syracuseStep 1481249 = 1110937) B1110937
theorem B694823 : Blo 459783 694823 := bstep (se 1 (by rfl) ⟨521117, by rfl⟩ : syracuseStep 694823 = 1042235) B1042235
theorem B1972795 : Blo 459783 1972795 := bstep (se 1 (by rfl) ⟨1479596, by rfl⟩ : syracuseStep 1972795 = 2959193) B2959193
theorem B694907 : Blo 459783 694907 := bstep (se 1 (by rfl) ⟨521180, by rfl⟩ : syracuseStep 694907 = 1042361) B1042361
theorem B695033 : Blo 459783 695033 := bstep (se 2 (by rfl) ⟨260637, by rfl⟩ : syracuseStep 695033 = 521275) B521275
theorem B695135 : Blo 459783 695135 := bstep (se 1 (by rfl) ⟨521351, by rfl⟩ : syracuseStep 695135 = 1042703) B1042703
theorem B695147 : Blo 459783 695147 := bstep (se 1 (by rfl) ⟨521360, by rfl⟩ : syracuseStep 695147 = 1042721) B1042721
theorem B1481647 : Blo 459783 1481647 := bstep (se 1 (by rfl) ⟨1111235, by rfl⟩ : syracuseStep 1481647 = 2222471) B2222471
theorem B2432051 : Blo 459783 2432051 := bstep (se 1 (by rfl) ⟨1824038, by rfl⟩ : syracuseStep 2432051 = 3648077) B3648077
theorem B695375 : Blo 459783 695375 := bstep (se 1 (by rfl) ⟨521531, by rfl⟩ : syracuseStep 695375 = 1043063) B1043063
theorem B1186987 : Blo 459783 1186987 := bstep (se 1 (by rfl) ⟨890240, by rfl⟩ : syracuseStep 1186987 = 1780481) B1780481
theorem B695495 : Blo 459783 695495 := bstep (se 1 (by rfl) ⟨521621, by rfl⟩ : syracuseStep 695495 = 1043243) B1043243
theorem B695657 : Blo 459783 695657 := bstep (se 2 (by rfl) ⟨260871, by rfl⟩ : syracuseStep 695657 = 521743) B521743
theorem B2334095 : Blo 459783 2334095 := bstep (se 1 (by rfl) ⟨1750571, by rfl⟩ : syracuseStep 2334095 = 3501143) B3501143
theorem B466471 : Blo 459783 466471 := bstep (se 1 (by rfl) ⟨349853, by rfl⟩ : syracuseStep 466471 = 699707) B699707
theorem B4202117 : Blo 459783 4202117 := bstep (se 4 (by rfl) ⟨393948, by rfl⟩ : syracuseStep 4202117 = 787897) B787897
theorem B466727 : Blo 459783 466727 := bstep (se 1 (by rfl) ⟨350045, by rfl⟩ : syracuseStep 466727 = 700091) B700091
theorem B1318751 : Blo 459783 1318751 := bstep (se 1 (by rfl) ⟨989063, by rfl⟩ : syracuseStep 1318751 = 1978127) B1978127
theorem B1483019 : Blo 459783 1483019 := bstep (se 1 (by rfl) ⟨1112264, by rfl⟩ : syracuseStep 1483019 = 2224529) B2224529
theorem B1122665 : Blo 459783 1122665 := bstep (se 2 (by rfl) ⟨420999, by rfl⟩ : syracuseStep 1122665 = 841999) B841999
theorem B1974793 : Blo 459783 1974793 := bstep (se 2 (by rfl) ⟨740547, by rfl⟩ : syracuseStep 1974793 = 1481095) B1481095
theorem B1319753 : Blo 459783 1319753 := bstep (se 2 (by rfl) ⟨494907, by rfl⟩ : syracuseStep 1319753 = 989815) B989815
theorem B664615 : Blo 459783 664615 := bstep (se 1 (by rfl) ⟨498461, by rfl⟩ : syracuseStep 664615 = 996923) B996923
theorem B1877107 : Blo 459783 1877107 := bstep (se 1 (by rfl) ⟨1407830, by rfl⟩ : syracuseStep 1877107 = 2815661) B2815661
theorem B53880025 : Blo 459783 53880025 := bstep (se 2 (by rfl) ⟨20205009, by rfl⟩ : syracuseStep 53880025 = 40410019) B40410019
theorem B1484119 : Blo 459783 1484119 := bstep (se 1 (by rfl) ⟨1113089, by rfl⟩ : syracuseStep 1484119 = 2226179) B2226179
theorem B1746305 : Blo 459783 1746305 := bstep (se 2 (by rfl) ⟨654864, by rfl⟩ : syracuseStep 1746305 = 1309729) B1309729
theorem B1746319 : Blo 459783 1746319 := bstep (se 1 (by rfl) ⟨1309739, by rfl⟩ : syracuseStep 1746319 = 2619479) B2619479
theorem B2336201 : Blo 459783 2336201 := bstep (se 2 (by rfl) ⟨876075, by rfl⟩ : syracuseStep 2336201 = 1752151) B1752151
theorem B6334145 : Blo 459783 6334145 := bstep (se 2 (by rfl) ⟨2375304, by rfl⟩ : syracuseStep 6334145 = 4750609) B4750609
theorem B5940985 : Blo 459783 5940985 := bstep (se 2 (by rfl) ⟨2227869, by rfl⟩ : syracuseStep 5940985 = 4455739) B4455739
theorem B3319661 : Blo 459783 3319661 := bstep (se 3 (by rfl) ⟨622436, by rfl⟩ : syracuseStep 3319661 = 1244873) B1244873
theorem B2336849 : Blo 459783 2336849 := bstep (se 2 (by rfl) ⟨876318, by rfl⟩ : syracuseStep 2336849 = 1752637) B1752637
theorem B5941349 : Blo 459783 5941349 := bstep (se 4 (by rfl) ⟨557001, by rfl⟩ : syracuseStep 5941349 = 1114003) B1114003
theorem B2369803 : Blo 459783 2369803 := bstep (se 1 (by rfl) ⟨1777352, by rfl⟩ : syracuseStep 2369803 = 3554705) B3554705
theorem B5351831 : Blo 459783 5351831 := bstep (se 1 (by rfl) ⟨4013873, by rfl⟩ : syracuseStep 5351831 = 8027747) B8027747
theorem B469423 : Blo 459783 469423 := bstep (se 1 (by rfl) ⟨352067, by rfl⟩ : syracuseStep 469423 = 704135) B704135
theorem B7514653 : Blo 459783 7514653 := bstep (se 3 (by rfl) ⟨1408997, by rfl⟩ : syracuseStep 7514653 = 2817995) B2817995
theorem B1747595 : Blo 459783 1747595 := bstep (se 1 (by rfl) ⟨1310696, by rfl⟩ : syracuseStep 1747595 = 2621393) B2621393
theorem B7514909 : Blo 459783 7514909 := bstep (se 3 (by rfl) ⟨1409045, by rfl⟩ : syracuseStep 7514909 = 2818091) B2818091
theorem B2632783 : Blo 459783 2632783 := bstep (se 1 (by rfl) ⟨1974587, by rfl⟩ : syracuseStep 2632783 = 3949175) B3949175
theorem B1551905 : Blo 459783 1551905 := bstep (se 2 (by rfl) ⟨581964, by rfl⟩ : syracuseStep 1551905 = 1163929) B1163929
theorem B1552121 : Blo 459783 1552121 := bstep (se 2 (by rfl) ⟨582045, by rfl⟩ : syracuseStep 1552121 = 1164091) B1164091
theorem B1552391 : Blo 459783 1552391 := bstep (se 1 (by rfl) ⟨1164293, by rfl⟩ : syracuseStep 1552391 = 2328587) B2328587
theorem B1552499 : Blo 459783 1552499 := bstep (se 1 (by rfl) ⟨1164374, by rfl⟩ : syracuseStep 1552499 = 2328749) B2328749
theorem B3321971 : Blo 459783 3321971 := bstep (se 1 (by rfl) ⟨2491478, by rfl⟩ : syracuseStep 3321971 = 4982957) B4982957
theorem B1552769 : Blo 459783 1552769 := bstep (se 2 (by rfl) ⟨582288, by rfl⟩ : syracuseStep 1552769 = 1164577) B1164577
theorem B10138385 : Blo 459783 10138385 := bstep (se 2 (by rfl) ⟨3801894, by rfl⟩ : syracuseStep 10138385 = 7603789) B7603789
theorem B5715011 : Blo 459783 5715011 := bstep (se 1 (by rfl) ⟨4286258, by rfl⟩ : syracuseStep 5715011 = 8572517) B8572517
theorem B668795 : Blo 459783 668795 := bstep (se 1 (by rfl) ⟨501596, by rfl⟩ : syracuseStep 668795 = 1003193) B1003193
theorem B1553579 : Blo 459783 1553579 := bstep (se 1 (by rfl) ⟨1165184, by rfl⟩ : syracuseStep 1553579 = 2330369) B2330369
theorem B7091549 : Blo 459783 7091549 := bstep (se 3 (by rfl) ⟨1329665, by rfl⟩ : syracuseStep 7091549 = 2659331) B2659331
theorem B3520097 : Blo 459783 3520097 := bstep (se 2 (by rfl) ⟨1320036, by rfl⟩ : syracuseStep 3520097 = 2640073) B2640073
theorem B1554119 : Blo 459783 1554119 := bstep (se 1 (by rfl) ⟨1165589, by rfl⟩ : syracuseStep 1554119 = 2331179) B2331179
theorem B1980227 : Blo 459783 1980227 := bstep (se 1 (by rfl) ⟨1485170, by rfl⟩ : syracuseStep 1980227 = 2970341) B2970341
theorem B1750967 : Blo 459783 1750967 := bstep (se 1 (by rfl) ⟨1313225, by rfl⟩ : syracuseStep 1750967 = 2626451) B2626451
theorem B1128455 : Blo 459783 1128455 := bstep (se 1 (by rfl) ⟨846341, by rfl⟩ : syracuseStep 1128455 = 1692683) B1692683
theorem B2341385 : Blo 459783 2341385 := bstep (se 2 (by rfl) ⟨878019, by rfl⟩ : syracuseStep 2341385 = 1756039) B1756039
theorem B1554983 : Blo 459783 1554983 := bstep (se 1 (by rfl) ⟨1166237, by rfl⟩ : syracuseStep 1554983 = 2332475) B2332475
theorem B2800187 : Blo 459783 2800187 := bstep (se 1 (by rfl) ⟨2100140, by rfl⟩ : syracuseStep 2800187 = 4200281) B4200281
theorem B1555091 : Blo 459783 1555091 := bstep (se 1 (by rfl) ⟨1166318, by rfl⟩ : syracuseStep 1555091 = 2332637) B2332637
theorem B1555307 : Blo 459783 1555307 := bstep (se 1 (by rfl) ⟨1166480, by rfl⟩ : syracuseStep 1555307 = 2332961) B2332961
theorem B3160939 : Blo 459783 3160939 := bstep (se 1 (by rfl) ⟨2370704, by rfl⟩ : syracuseStep 3160939 = 4741409) B4741409
theorem B1555361 : Blo 459783 1555361 := bstep (se 2 (by rfl) ⟨583260, by rfl⟩ : syracuseStep 1555361 = 1166521) B1166521
theorem B1751969 : Blo 459783 1751969 := bstep (se 2 (by rfl) ⟨656988, by rfl⟩ : syracuseStep 1751969 = 1313977) B1313977
theorem B3521555 : Blo 459783 3521555 := bstep (se 1 (by rfl) ⟨2641166, by rfl⟩ : syracuseStep 3521555 = 5282333) B5282333
theorem B834617 : Blo 459783 834617 := bstep (se 2 (by rfl) ⟨312981, by rfl⟩ : syracuseStep 834617 = 625963) B625963
theorem B1752425 : Blo 459783 1752425 := bstep (se 2 (by rfl) ⟨657159, by rfl⟩ : syracuseStep 1752425 = 1314319) B1314319
theorem B1555955 : Blo 459783 1555955 := bstep (se 1 (by rfl) ⟨1166966, by rfl⟩ : syracuseStep 1555955 = 2333933) B2333933
theorem B1752941 : Blo 459783 1752941 := bstep (se 3 (by rfl) ⟨328676, by rfl⟩ : syracuseStep 1752941 = 657353) B657353
theorem B2342843 : Blo 459783 2342843 := bstep (se 1 (by rfl) ⟨1757132, by rfl⟩ : syracuseStep 2342843 = 3514265) B3514265
theorem B5980175 : Blo 459783 5980175 := bstep (se 1 (by rfl) ⟨4485131, by rfl⟩ : syracuseStep 5980175 = 8970263) B8970263
theorem B1556495 : Blo 459783 1556495 := bstep (se 1 (by rfl) ⟨1167371, by rfl⟩ : syracuseStep 1556495 = 2334743) B2334743
theorem B1753609 : Blo 459783 1753609 := bstep (se 2 (by rfl) ⟨657603, by rfl⟩ : syracuseStep 1753609 = 1315207) B1315207
theorem B1557089 : Blo 459783 1557089 := bstep (se 2 (by rfl) ⟨583908, by rfl⟩ : syracuseStep 1557089 = 1167817) B1167817
theorem B2344139 : Blo 459783 2344139 := bstep (se 1 (by rfl) ⟨1758104, by rfl⟩ : syracuseStep 2344139 = 3516209) B3516209
theorem B3327247 : Blo 459783 3327247 := bstep (se 1 (by rfl) ⟨2495435, by rfl⟩ : syracuseStep 3327247 = 4990871) B4990871
theorem B738779 : Blo 459783 738779 := bstep (se 1 (by rfl) ⟨554084, by rfl⟩ : syracuseStep 738779 = 1108169) B1108169
theorem B738895 : Blo 459783 738895 := bstep (se 1 (by rfl) ⟨554171, by rfl⟩ : syracuseStep 738895 = 1108343) B1108343
theorem B1755067 : Blo 459783 1755067 := bstep (se 1 (by rfl) ⟨1316300, by rfl⟩ : syracuseStep 1755067 = 2632601) B2632601
theorem B1558547 : Blo 459783 1558547 := bstep (se 1 (by rfl) ⟨1168910, by rfl⟩ : syracuseStep 1558547 = 2337821) B2337821
theorem B1558871 : Blo 459783 1558871 := bstep (se 1 (by rfl) ⟨1169153, by rfl⟩ : syracuseStep 1558871 = 2338307) B2338307
theorem B1034639 : Blo 459783 1034639 := bstep (se 1 (by rfl) ⟨775979, by rfl⟩ : syracuseStep 1034639 = 1551959) B1551959
theorem B1165711 : Blo 459783 1165711 := bstep (se 1 (by rfl) ⟨874283, by rfl⟩ : syracuseStep 1165711 = 1748567) B1748567
theorem B9947569 : Blo 459783 9947569 := bstep (se 2 (by rfl) ⟨3730338, by rfl⟩ : syracuseStep 9947569 = 7460677) B7460677
theorem B3983905 : Blo 459783 3983905 := bstep (se 2 (by rfl) ⟨1493964, by rfl⟩ : syracuseStep 3983905 = 2987929) B2987929
theorem B4344353 : Blo 459783 4344353 := bstep (se 2 (by rfl) ⟨1629132, by rfl⟩ : syracuseStep 4344353 = 3258265) B3258265
theorem B3754669 : Blo 459783 3754669 := bstep (se 3 (by rfl) ⟨704000, by rfl⟩ : syracuseStep 3754669 = 1408001) B1408001
theorem B1755857 : Blo 459783 1755857 := bstep (se 2 (by rfl) ⟨658446, by rfl⟩ : syracuseStep 1755857 = 1316893) B1316893
theorem B1034963 : Blo 459783 1034963 := bstep (se 1 (by rfl) ⟨776222, by rfl⟩ : syracuseStep 1034963 = 1552445) B1552445
theorem B1166035 : Blo 459783 1166035 := bstep (se 1 (by rfl) ⟨874526, by rfl⟩ : syracuseStep 1166035 = 1749053) B1749053
theorem B740087 : Blo 459783 740087 := bstep (se 1 (by rfl) ⟨555065, by rfl⟩ : syracuseStep 740087 = 1110131) B1110131
theorem B1067951 : Blo 459783 1067951 := bstep (se 1 (by rfl) ⟨800963, by rfl⟩ : syracuseStep 1067951 = 1601927) B1601927
theorem B2214839 : Blo 459783 2214839 := bstep (se 1 (by rfl) ⟨1661129, by rfl⟩ : syracuseStep 2214839 = 3322259) B3322259
theorem B740279 : Blo 459783 740279 := bstep (se 1 (by rfl) ⟨555209, by rfl⟩ : syracuseStep 740279 = 1110419) B1110419
theorem B1756313 : Blo 459783 1756313 := bstep (se 2 (by rfl) ⟨658617, by rfl⟩ : syracuseStep 1756313 = 1317235) B1317235
theorem B1559951 : Blo 459783 1559951 := bstep (se 1 (by rfl) ⟨1169963, by rfl⟩ : syracuseStep 1559951 = 2339927) B2339927
theorem B1035899 : Blo 459783 1035899 := bstep (se 1 (by rfl) ⟨776924, by rfl⟩ : syracuseStep 1035899 = 1553849) B1553849
theorem B1166987 : Blo 459783 1166987 := bstep (se 1 (by rfl) ⟨875240, by rfl⟩ : syracuseStep 1166987 = 1750481) B1750481
theorem B741035 : Blo 459783 741035 := bstep (se 1 (by rfl) ⟨555776, by rfl⟩ : syracuseStep 741035 = 1111553) B1111553
theorem B1560275 : Blo 459783 1560275 := bstep (se 1 (by rfl) ⟨1170206, by rfl⟩ : syracuseStep 1560275 = 2340413) B2340413
theorem B1036025 : Blo 459783 1036025 := bstep (se 2 (by rfl) ⟨388509, by rfl⟩ : syracuseStep 1036025 = 777019) B777019
theorem B3755969 : Blo 459783 3755969 := bstep (se 2 (by rfl) ⟨1408488, by rfl⟩ : syracuseStep 3755969 = 2816977) B2816977
theorem B1036295 : Blo 459783 1036295 := bstep (se 1 (by rfl) ⟨777221, by rfl⟩ : syracuseStep 1036295 = 1554443) B1554443
theorem B1036367 : Blo 459783 1036367 := bstep (se 1 (by rfl) ⟨777275, by rfl⟩ : syracuseStep 1036367 = 1554551) B1554551
theorem B6082675 : Blo 459783 6082675 := bstep (se 1 (by rfl) ⟨4562006, by rfl⟩ : syracuseStep 6082675 = 9124013) B9124013
theorem B741727 : Blo 459783 741727 := bstep (se 1 (by rfl) ⟨556295, by rfl⟩ : syracuseStep 741727 = 1112591) B1112591
theorem B2216321 : Blo 459783 2216321 := bstep (se 2 (by rfl) ⟨831120, by rfl⟩ : syracuseStep 2216321 = 1662241) B1662241
theorem B1036763 : Blo 459783 1036763 := bstep (se 1 (by rfl) ⟨777572, by rfl⟩ : syracuseStep 1036763 = 1555145) B1555145
theorem B3560071 : Blo 459783 3560071 := bstep (se 1 (by rfl) ⟨2670053, by rfl⟩ : syracuseStep 3560071 = 5340107) B5340107
theorem B3330733 : Blo 459783 3330733 := bstep (se 3 (by rfl) ⟨624512, by rfl⟩ : syracuseStep 3330733 = 1249025) B1249025
theorem B1168121 : Blo 459783 1168121 := bstep (se 2 (by rfl) ⟨438045, by rfl⟩ : syracuseStep 1168121 = 876091) B876091
theorem B8409905 : Blo 459783 8409905 := bstep (se 2 (by rfl) ⟨3153714, by rfl⟩ : syracuseStep 8409905 = 6307429) B6307429
theorem B12342131 : Blo 459783 12342131 := bstep (se 1 (by rfl) ⟨9256598, by rfl⟩ : syracuseStep 12342131 = 18513197) B18513197
theorem B1561463 : Blo 459783 1561463 := bstep (se 1 (by rfl) ⟨1171097, by rfl⟩ : syracuseStep 1561463 = 2342195) B2342195
theorem B1037231 : Blo 459783 1037231 := bstep (se 1 (by rfl) ⟨777923, by rfl⟩ : syracuseStep 1037231 = 1555847) B1555847
theorem B1168303 : Blo 459783 1168303 := bstep (se 1 (by rfl) ⟨876227, by rfl⟩ : syracuseStep 1168303 = 1752455) B1752455
theorem B873479 : Blo 459783 873479 := bstep (se 1 (by rfl) ⟨655109, by rfl⟩ : syracuseStep 873479 = 1310219) B1310219
theorem B1561679 : Blo 459783 1561679 := bstep (se 1 (by rfl) ⟨1171259, by rfl⟩ : syracuseStep 1561679 = 2342519) B2342519
theorem B1758287 : Blo 459783 1758287 := bstep (se 1 (by rfl) ⟨1318715, by rfl⟩ : syracuseStep 1758287 = 2637431) B2637431
theorem B1037483 : Blo 459783 1037483 := bstep (se 1 (by rfl) ⟨778112, by rfl⟩ : syracuseStep 1037483 = 1556225) B1556225
theorem B1758455 : Blo 459783 1758455 := bstep (se 1 (by rfl) ⟨1318841, by rfl⟩ : syracuseStep 1758455 = 2637683) B2637683
theorem B1168769 : Blo 459783 1168769 := bstep (se 2 (by rfl) ⟨438288, by rfl⟩ : syracuseStep 1168769 = 876577) B876577
theorem B3495311 : Blo 459783 3495311 := bstep (se 1 (by rfl) ⟨2621483, by rfl⟩ : syracuseStep 3495311 = 5242967) B5242967
theorem B1562057 : Blo 459783 1562057 := bstep (se 2 (by rfl) ⟨585771, by rfl⟩ : syracuseStep 1562057 = 1171543) B1171543
theorem B7886321 : Blo 459783 7886321 := bstep (se 2 (by rfl) ⟨2957370, by rfl⟩ : syracuseStep 7886321 = 5914741) B5914741
theorem B874003 : Blo 459783 874003 := bstep (se 1 (by rfl) ⟨655502, by rfl⟩ : syracuseStep 874003 = 1311005) B1311005
theorem B1038023 : Blo 459783 1038023 := bstep (se 1 (by rfl) ⟨778517, by rfl⟩ : syracuseStep 1038023 = 1557035) B1557035
theorem B1562327 : Blo 459783 1562327 := bstep (se 1 (by rfl) ⟨1171745, by rfl⟩ : syracuseStep 1562327 = 2343491) B2343491
theorem B2217721 : Blo 459783 2217721 := bstep (se 2 (by rfl) ⟨831645, by rfl⟩ : syracuseStep 2217721 = 1663291) B1663291
theorem B1169225 : Blo 459783 1169225 := bstep (se 2 (by rfl) ⟨438459, by rfl⟩ : syracuseStep 1169225 = 876919) B876919
theorem B1562543 : Blo 459783 1562543 := bstep (se 1 (by rfl) ⟨1171907, by rfl⟩ : syracuseStep 1562543 = 2343815) B2343815
theorem B776155 : Blo 459783 776155 := bstep (se 1 (by rfl) ⟨582116, by rfl⟩ : syracuseStep 776155 = 1164233) B1164233
theorem B1169579 : Blo 459783 1169579 := bstep (se 1 (by rfl) ⟨877184, by rfl⟩ : syracuseStep 1169579 = 1754369) B1754369
theorem B1759427 : Blo 459783 1759427 := bstep (se 1 (by rfl) ⟨1319570, by rfl⟩ : syracuseStep 1759427 = 2639141) B2639141
theorem B2218529 : Blo 459783 2218529 := bstep (se 2 (by rfl) ⟨831948, by rfl⟩ : syracuseStep 2218529 = 1663897) B1663897
theorem B1038887 : Blo 459783 1038887 := bstep (se 1 (by rfl) ⟨779165, by rfl⟩ : syracuseStep 1038887 = 1558331) B1558331
theorem B776783 : Blo 459783 776783 := bstep (se 1 (by rfl) ⟨582587, by rfl⟩ : syracuseStep 776783 = 1165175) B1165175
theorem B1333883 : Blo 459783 1333883 := bstep (se 1 (by rfl) ⟨1000412, by rfl⟩ : syracuseStep 1333883 = 2000825) B2000825
theorem B50420465 : Blo 459783 50420465 := bstep (se 2 (by rfl) ⟨18907674, by rfl⟩ : syracuseStep 50420465 = 37815349) B37815349
theorem B1039211 : Blo 459783 1039211 := bstep (se 1 (by rfl) ⟨779408, by rfl⟩ : syracuseStep 1039211 = 1558817) B1558817
theorem B1039265 : Blo 459783 1039265 := bstep (se 2 (by rfl) ⟨389724, by rfl⟩ : syracuseStep 1039265 = 779449) B779449
theorem B1170359 : Blo 459783 1170359 := bstep (se 1 (by rfl) ⟨877769, by rfl⟩ : syracuseStep 1170359 = 1755539) B1755539
theorem B1760413 : Blo 459783 1760413 := bstep (se 3 (by rfl) ⟨330077, by rfl⟩ : syracuseStep 1760413 = 660155) B660155
theorem B1039607 : Blo 459783 1039607 := bstep (se 1 (by rfl) ⟨779705, by rfl⟩ : syracuseStep 1039607 = 1559411) B1559411
theorem B777647 : Blo 459783 777647 := bstep (se 1 (by rfl) ⟨583235, by rfl⟩ : syracuseStep 777647 = 1166471) B1166471
theorem B1891937 : Blo 459783 1891937 := bstep (se 2 (by rfl) ⟨709476, by rfl⟩ : syracuseStep 1891937 = 1418953) B1418953
theorem B1040201 : Blo 459783 1040201 := bstep (se 2 (by rfl) ⟨390075, by rfl⟩ : syracuseStep 1040201 = 780151) B780151
theorem B778079 : Blo 459783 778079 := bstep (se 1 (by rfl) ⟨583559, by rfl⟩ : syracuseStep 778079 = 1167119) B1167119
theorem B876395 : Blo 459783 876395 := bstep (se 1 (by rfl) ⟨657296, by rfl⟩ : syracuseStep 876395 = 1314593) B1314593
theorem B1105825 : Blo 459783 1105825 := bstep (se 2 (by rfl) ⟨414684, by rfl⟩ : syracuseStep 1105825 = 829369) B829369
theorem B1171361 : Blo 459783 1171361 := bstep (se 2 (by rfl) ⟨439260, by rfl⟩ : syracuseStep 1171361 = 878521) B878521
theorem B3334081 : Blo 459783 3334081 := bstep (se 2 (by rfl) ⟨1250280, by rfl⟩ : syracuseStep 3334081 = 2500561) B2500561
theorem B1564919 : Blo 459783 1564919 := bstep (se 1 (by rfl) ⟨1173689, by rfl⟩ : syracuseStep 1564919 = 2347379) B2347379
theorem B1171817 : Blo 459783 1171817 := bstep (se 2 (by rfl) ⟨439431, by rfl⟩ : syracuseStep 1171817 = 878863) B878863
theorem B581995 : Blo 459783 581995 := bstep (se 1 (by rfl) ⟨436496, by rfl⟩ : syracuseStep 581995 = 872993) B872993
theorem B778639 : Blo 459783 778639 := bstep (se 1 (by rfl) ⟨583979, by rfl⟩ : syracuseStep 778639 = 1167959) B1167959
theorem B877063 : Blo 459783 877063 := bstep (se 1 (by rfl) ⟨657797, by rfl⟩ : syracuseStep 877063 = 1315595) B1315595
theorem B1565243 : Blo 459783 1565243 := bstep (se 1 (by rfl) ⟨1173932, by rfl⟩ : syracuseStep 1565243 = 2347865) B2347865
theorem B582223 : Blo 459783 582223 := bstep (se 1 (by rfl) ⟨436667, by rfl⟩ : syracuseStep 582223 = 873335) B873335
theorem B1040993 : Blo 459783 1040993 := bstep (se 2 (by rfl) ⟨390372, by rfl⟩ : syracuseStep 1040993 = 780745) B780745
theorem B1041335 : Blo 459783 1041335 := bstep (se 1 (by rfl) ⟨781001, by rfl⟩ : syracuseStep 1041335 = 1562003) B1562003
theorem B779321 : Blo 459783 779321 := bstep (se 2 (by rfl) ⟨292245, by rfl⟩ : syracuseStep 779321 = 584491) B584491
theorem B877625 : Blo 459783 877625 := bstep (se 2 (by rfl) ⟨329109, by rfl⟩ : syracuseStep 877625 = 658219) B658219
theorem B1041929 : Blo 459783 1041929 := bstep (se 2 (by rfl) ⟨390723, by rfl⟩ : syracuseStep 1041929 = 781447) B781447
theorem B1173001 : Blo 459783 1173001 := bstep (se 2 (by rfl) ⟨439875, by rfl⟩ : syracuseStep 1173001 = 879751) B879751
theorem B517711 : Blo 459783 517711 := bstep (se 1 (by rfl) ⟨388283, by rfl⟩ : syracuseStep 517711 = 776567) B776567
theorem B583291 : Blo 459783 583291 := bstep (se 1 (by rfl) ⟨437468, by rfl⟩ : syracuseStep 583291 = 874937) B874937
theorem B1205959 : Blo 459783 1205959 := bstep (se 1 (by rfl) ⟨904469, by rfl⟩ : syracuseStep 1205959 = 1808939) B1808939
theorem B780023 : Blo 459783 780023 := bstep (se 1 (by rfl) ⟨585017, by rfl⟩ : syracuseStep 780023 = 1170035) B1170035
theorem B583519 : Blo 459783 583519 := bstep (se 1 (by rfl) ⟨437639, by rfl⟩ : syracuseStep 583519 = 875279) B875279
theorem B1042271 : Blo 459783 1042271 := bstep (se 1 (by rfl) ⟨781703, by rfl⟩ : syracuseStep 1042271 = 1563407) B1563407
theorem B518107 : Blo 459783 518107 := bstep (se 1 (by rfl) ⟨388580, by rfl⟩ : syracuseStep 518107 = 777161) B777161
theorem B1042451 : Blo 459783 1042451 := bstep (se 1 (by rfl) ⟨781838, by rfl⟩ : syracuseStep 1042451 = 1563677) B1563677
theorem B780367 : Blo 459783 780367 := bstep (se 1 (by rfl) ⟨585275, by rfl⟩ : syracuseStep 780367 = 1170551) B1170551
theorem B6383717 : Blo 459783 6383717 := bstep (se 4 (by rfl) ⟨598473, by rfl⟩ : syracuseStep 6383717 = 1196947) B1196947
theorem B11954309 : Blo 459783 11954309 := bstep (se 4 (by rfl) ⟨1120716, by rfl⟩ : syracuseStep 11954309 = 2241433) B2241433
theorem B780617 : Blo 459783 780617 := bstep (se 2 (by rfl) ⟨292731, by rfl⟩ : syracuseStep 780617 = 585463) B585463
theorem B1042793 : Blo 459783 1042793 := bstep (se 2 (by rfl) ⟨391047, by rfl⟩ : syracuseStep 1042793 = 782095) B782095
theorem B518575 : Blo 459783 518575 := bstep (se 1 (by rfl) ⟨388931, by rfl⟩ : syracuseStep 518575 = 777863) B777863
theorem B584111 : Blo 459783 584111 := bstep (se 1 (by rfl) ⟨438083, by rfl⟩ : syracuseStep 584111 = 876167) B876167
theorem B879113 : Blo 459783 879113 := bstep (se 2 (by rfl) ⟨329667, by rfl⟩ : syracuseStep 879113 = 659335) B659335
theorem B781049 : Blo 459783 781049 := bstep (se 2 (by rfl) ⟨292893, by rfl⟩ : syracuseStep 781049 = 585787) B585787
theorem B519007 : Blo 459783 519007 := bstep (se 1 (by rfl) ⟨389255, by rfl⟩ : syracuseStep 519007 = 778511) B778511
theorem B781231 : Blo 459783 781231 := bstep (se 1 (by rfl) ⟨585923, by rfl⟩ : syracuseStep 781231 = 1171847) B1171847
theorem B1043387 : Blo 459783 1043387 := bstep (se 1 (by rfl) ⟨782540, by rfl⟩ : syracuseStep 1043387 = 1565081) B1565081
theorem B781319 : Blo 459783 781319 := bstep (se 1 (by rfl) ⟨585989, by rfl⟩ : syracuseStep 781319 = 1171979) B1171979
theorem B1043513 : Blo 459783 1043513 := bstep (se 2 (by rfl) ⟨391317, by rfl⟩ : syracuseStep 1043513 = 782635) B782635
theorem B519367 : Blo 459783 519367 := bstep (se 1 (by rfl) ⟨389525, by rfl⟩ : syracuseStep 519367 = 779051) B779051
theorem B781663 : Blo 459783 781663 := bstep (se 1 (by rfl) ⟨586247, by rfl⟩ : syracuseStep 781663 = 1172495) B1172495
theorem B879979 : Blo 459783 879979 := bstep (se 1 (by rfl) ⟨659984, by rfl⟩ : syracuseStep 879979 = 1319969) B1319969
theorem B781751 : Blo 459783 781751 := bstep (se 1 (by rfl) ⟨586313, by rfl⟩ : syracuseStep 781751 = 1172627) B1172627
theorem B880055 : Blo 459783 880055 := bstep (se 1 (by rfl) ⟨660041, by rfl⟩ : syracuseStep 880055 = 1320083) B1320083
theorem B1502707 : Blo 459783 1502707 := bstep (se 1 (by rfl) ⟨1127030, by rfl⟩ : syracuseStep 1502707 = 2254061) B2254061
theorem B3501629 : Blo 459783 3501629 := bstep (se 3 (by rfl) ⟨656555, by rfl⟩ : syracuseStep 3501629 = 1313111) B1313111
theorem B19951181 : Blo 459783 19951181 := bstep (se 3 (by rfl) ⟨3740846, by rfl⟩ : syracuseStep 19951181 = 7481693) B7481693
theorem B3010193 : Blo 459783 3010193 := bstep (se 2 (by rfl) ⟨1128822, by rfl⟩ : syracuseStep 3010193 = 2257645) B2257645
theorem B782345 : Blo 459783 782345 := bstep (se 2 (by rfl) ⟨293379, by rfl⟩ : syracuseStep 782345 = 586759) B586759
theorem B13463567 : Blo 459783 13463567 := bstep (se 1 (by rfl) ⟨10097675, by rfl⟩ : syracuseStep 13463567 = 20195351) B20195351
theorem B520231 : Blo 459783 520231 := bstep (se 1 (by rfl) ⟨390173, by rfl⟩ : syracuseStep 520231 = 780347) B780347
theorem B782507 : Blo 459783 782507 := bstep (se 1 (by rfl) ⟨586880, by rfl⟩ : syracuseStep 782507 = 1173761) B1173761
theorem B22475069 : Blo 459783 22475069 := bstep (se 3 (by rfl) ⟨4214075, by rfl⟩ : syracuseStep 22475069 = 8428151) B8428151
theorem B5501245 : Blo 459783 5501245 := bstep (se 3 (by rfl) ⟨1031483, by rfl⟩ : syracuseStep 5501245 = 2062967) B2062967
theorem B3502601 : Blo 459783 3502601 := bstep (se 2 (by rfl) ⟨1313475, by rfl⟩ : syracuseStep 3502601 = 2626951) B2626951
theorem B2519687 : Blo 459783 2519687 := bstep (se 1 (by rfl) ⟨1889765, by rfl⟩ : syracuseStep 2519687 = 3779531) B3779531
theorem B13202189 : Blo 459783 13202189 := bstep (se 3 (by rfl) ⟨2475410, by rfl⟩ : syracuseStep 13202189 = 4950821) B4950821
theorem B553835 : Blo 459783 553835 := bstep (se 1 (by rfl) ⟨415376, by rfl⟩ : syracuseStep 553835 = 830753) B830753
theorem B2814977 : Blo 459783 2814977 := bstep (se 2 (by rfl) ⟨1055616, by rfl⟩ : syracuseStep 2814977 = 2111233) B2111233
theorem B1406663 : Blo 459783 1406663 := bstep (se 1 (by rfl) ⟨1054997, by rfl⟩ : syracuseStep 1406663 = 2109995) B2109995
theorem B3504059 : Blo 459783 3504059 := bstep (se 1 (by rfl) ⟨2628044, by rfl⟩ : syracuseStep 3504059 = 5256089) B5256089
theorem B1964047 : Blo 459783 1964047 := bstep (se 1 (by rfl) ⟨1473035, by rfl⟩ : syracuseStep 1964047 = 2946071) B2946071
theorem B6683381 : Blo 459783 6683381 := bstep (se 5 (by rfl) ⟨313283, by rfl⟩ : syracuseStep 6683381 = 626567) B626567
theorem B1309547 : Blo 459783 1309547 := bstep (se 1 (by rfl) ⟨982160, by rfl⟩ : syracuseStep 1309547 = 1964321) B1964321
theorem B1473689 : Blo 459783 1473689 := bstep (se 2 (by rfl) ⟨552633, by rfl⟩ : syracuseStep 1473689 = 1105267) B1105267
theorem B2620619 : Blo 459783 2620619 := bstep (se 1 (by rfl) ⟨1965464, by rfl⟩ : syracuseStep 2620619 = 3930929) B3930929
theorem B1310195 : Blo 459783 1310195 := bstep (se 1 (by rfl) ⟨982646, by rfl⟩ : syracuseStep 1310195 = 1965293) B1965293
theorem B556583 : Blo 459783 556583 := bstep (se 1 (by rfl) ⟨417437, by rfl⟩ : syracuseStep 556583 = 834875) B834875
theorem B4226849 : Blo 459783 4226849 := bstep (se 2 (by rfl) ⟨1585068, by rfl⟩ : syracuseStep 4226849 = 3170137) B3170137
theorem B1310651 : Blo 459783 1310651 := bstep (se 1 (by rfl) ⟨982988, by rfl⟩ : syracuseStep 1310651 = 1965977) B1965977
theorem B655867 : Blo 459783 655867 := bstep (se 1 (by rfl) ⟨491900, by rfl⟩ : syracuseStep 655867 = 983801) B983801
theorem B524863 : Blo 459783 524863 := bstep (se 1 (by rfl) ⟨393647, by rfl⟩ : syracuseStep 524863 = 787295) B787295
theorem B32440933 : Blo 459783 32440933 := bstep (se 4 (by rfl) ⟨3041337, by rfl⟩ : syracuseStep 32440933 = 6082675) B6082675
theorem B1049195 : Blo 459783 1049195 := bstep (se 1 (by rfl) ⟨786896, by rfl⟩ : syracuseStep 1049195 = 1573793) B1573793
theorem B1311403 : Blo 459783 1311403 := bstep (se 1 (by rfl) ⟨983552, by rfl⟩ : syracuseStep 1311403 = 1967105) B1967105
theorem B656095 : Blo 459783 656095 := bstep (se 1 (by rfl) ⟨492071, by rfl⟩ : syracuseStep 656095 = 984143) B984143
theorem B983963 : Blo 459783 983963 := bstep (se 1 (by rfl) ⟨737972, by rfl⟩ : syracuseStep 983963 = 1475945) B1475945
theorem B460063 : Blo 459783 460063 := bstep (se 1 (by rfl) ⟨345047, by rfl⟩ : syracuseStep 460063 = 690095) B690095
theorem B460123 : Blo 459783 460123 := bstep (se 1 (by rfl) ⟨345092, by rfl⟩ : syracuseStep 460123 = 690185) B690185
theorem B460143 : Blo 459783 460143 := bstep (se 1 (by rfl) ⟨345107, by rfl⟩ : syracuseStep 460143 = 690215) B690215
theorem B886153 : Blo 459783 886153 := bstep (se 2 (by rfl) ⟨332307, by rfl⟩ : syracuseStep 886153 = 664615) B664615
theorem B3933593 : Blo 459783 3933593 := bstep (se 2 (by rfl) ⟨1475097, by rfl⟩ : syracuseStep 3933593 = 2950195) B2950195
theorem B460199 : Blo 459783 460199 := bstep (se 1 (by rfl) ⟨345149, by rfl⟩ : syracuseStep 460199 = 690299) B690299
theorem B460283 : Blo 459783 460283 := bstep (se 1 (by rfl) ⟨345212, by rfl⟩ : syracuseStep 460283 = 690425) B690425
theorem B460351 : Blo 459783 460351 := bstep (se 1 (by rfl) ⟨345263, by rfl⟩ : syracuseStep 460351 = 690527) B690527
theorem B460359 : Blo 459783 460359 := bstep (se 1 (by rfl) ⟨345269, by rfl⟩ : syracuseStep 460359 = 690539) B690539
theorem B689759 : Blo 459783 689759 := bstep (se 1 (by rfl) ⟨517319, by rfl⟩ : syracuseStep 689759 = 1034639) B1034639
theorem B1246907 : Blo 459783 1246907 := bstep (se 1 (by rfl) ⟨935180, by rfl⟩ : syracuseStep 1246907 = 1870361) B1870361
theorem B460511 : Blo 459783 460511 := bstep (se 1 (by rfl) ⟨345383, by rfl⟩ : syracuseStep 460511 = 690767) B690767
theorem B460591 : Blo 459783 460591 := bstep (se 1 (by rfl) ⟨345443, by rfl⟩ : syracuseStep 460591 = 690887) B690887
theorem B689975 : Blo 459783 689975 := bstep (se 1 (by rfl) ⟨517481, by rfl⟩ : syracuseStep 689975 = 1034963) B1034963
theorem B7997251 : Blo 459783 7997251 := bstep (se 1 (by rfl) ⟨5997938, by rfl⟩ : syracuseStep 7997251 = 11995877) B11995877
theorem B493391 : Blo 459783 493391 := bstep (se 1 (by rfl) ⟨370043, by rfl⟩ : syracuseStep 493391 = 740087) B740087
theorem B2328425 : Blo 459783 2328425 := bstep (se 2 (by rfl) ⟨873159, by rfl⟩ : syracuseStep 2328425 = 1746319) B1746319
theorem B460699 : Blo 459783 460699 := bstep (se 1 (by rfl) ⟨345524, by rfl⟩ : syracuseStep 460699 = 691049) B691049
theorem B460751 : Blo 459783 460751 := bstep (se 1 (by rfl) ⟨345563, by rfl⟩ : syracuseStep 460751 = 691127) B691127
theorem B1476559 : Blo 459783 1476559 := bstep (se 1 (by rfl) ⟨1107419, by rfl⟩ : syracuseStep 1476559 = 2214839) B2214839
theorem B460775 : Blo 459783 460775 := bstep (se 1 (by rfl) ⟨345581, by rfl⟩ : syracuseStep 460775 = 691163) B691163
theorem B690281 : Blo 459783 690281 := bstep (se 2 (by rfl) ⟨258855, by rfl⟩ : syracuseStep 690281 = 517711) B517711
theorem B985193 : Blo 459783 985193 := bstep (se 2 (by rfl) ⟨369447, by rfl⟩ : syracuseStep 985193 = 738895) B738895
theorem B1607945 : Blo 459783 1607945 := bstep (se 2 (by rfl) ⟨602979, by rfl⟩ : syracuseStep 1607945 = 1205959) B1205959
theorem B1476893 : Blo 459783 1476893 := bstep (se 3 (by rfl) ⟨276917, by rfl⟩ : syracuseStep 1476893 = 553835) B553835
theorem B461087 : Blo 459783 461087 := bstep (se 1 (by rfl) ⟨345815, by rfl⟩ : syracuseStep 461087 = 691631) B691631
theorem B461147 : Blo 459783 461147 := bstep (se 1 (by rfl) ⟨345860, by rfl⟩ : syracuseStep 461147 = 691721) B691721
theorem B1313135 : Blo 459783 1313135 := bstep (se 1 (by rfl) ⟨984851, by rfl⟩ : syracuseStep 1313135 = 1969703) B1969703
theorem B461167 : Blo 459783 461167 := bstep (se 1 (by rfl) ⟨345875, by rfl⟩ : syracuseStep 461167 = 691751) B691751
theorem B690599 : Blo 459783 690599 := bstep (se 1 (by rfl) ⟨517949, by rfl⟩ : syracuseStep 690599 = 1035899) B1035899
theorem B461223 : Blo 459783 461223 := bstep (se 1 (by rfl) ⟨345917, by rfl⟩ : syracuseStep 461223 = 691835) B691835
theorem B494023 : Blo 459783 494023 := bstep (se 1 (by rfl) ⟨370517, by rfl⟩ : syracuseStep 494023 = 741035) B741035
theorem B690683 : Blo 459783 690683 := bstep (se 1 (by rfl) ⟨518012, by rfl⟩ : syracuseStep 690683 = 1036025) B1036025
theorem B461307 : Blo 459783 461307 := bstep (se 1 (by rfl) ⟨345980, by rfl⟩ : syracuseStep 461307 = 691961) B691961
theorem B461375 : Blo 459783 461375 := bstep (se 1 (by rfl) ⟨346031, by rfl⟩ : syracuseStep 461375 = 692063) B692063
theorem B657991 : Blo 459783 657991 := bstep (se 1 (by rfl) ⟨493493, by rfl⟩ : syracuseStep 657991 = 986987) B986987
theorem B461383 : Blo 459783 461383 := bstep (se 1 (by rfl) ⟨346037, by rfl⟩ : syracuseStep 461383 = 692075) B692075
theorem B1247815 : Blo 459783 1247815 := bstep (se 1 (by rfl) ⟨935861, by rfl⟩ : syracuseStep 1247815 = 1871723) B1871723
theorem B690809 : Blo 459783 690809 := bstep (se 2 (by rfl) ⟨259053, by rfl⟩ : syracuseStep 690809 = 518107) B518107
theorem B1968779 : Blo 459783 1968779 := bstep (se 1 (by rfl) ⟨1476584, by rfl⟩ : syracuseStep 1968779 = 2953169) B2953169
theorem B690863 : Blo 459783 690863 := bstep (se 1 (by rfl) ⟨518147, by rfl⟩ : syracuseStep 690863 = 1036295) B1036295
theorem B985783 : Blo 459783 985783 := bstep (se 1 (by rfl) ⟨739337, by rfl⟩ : syracuseStep 985783 = 1478675) B1478675
theorem B690911 : Blo 459783 690911 := bstep (se 1 (by rfl) ⟨518183, by rfl⟩ : syracuseStep 690911 = 1036367) B1036367
theorem B461535 : Blo 459783 461535 := bstep (se 1 (by rfl) ⟨346151, by rfl⟩ : syracuseStep 461535 = 692303) B692303
theorem B461615 : Blo 459783 461615 := bstep (se 1 (by rfl) ⟨346211, by rfl⟩ : syracuseStep 461615 = 692423) B692423
theorem B461723 : Blo 459783 461723 := bstep (se 1 (by rfl) ⟨346292, by rfl⟩ : syracuseStep 461723 = 692585) B692585
theorem B1477547 : Blo 459783 1477547 := bstep (se 1 (by rfl) ⟨1108160, by rfl⟩ : syracuseStep 1477547 = 2216321) B2216321
theorem B461775 : Blo 459783 461775 := bstep (se 1 (by rfl) ⟨346331, by rfl⟩ : syracuseStep 461775 = 692663) B692663
theorem B691175 : Blo 459783 691175 := bstep (se 1 (by rfl) ⟨518381, by rfl⟩ : syracuseStep 691175 = 1036763) B1036763
theorem B461799 : Blo 459783 461799 := bstep (se 1 (by rfl) ⟨346349, by rfl⟩ : syracuseStep 461799 = 692699) B692699
theorem B5606603 : Blo 459783 5606603 := bstep (se 1 (by rfl) ⟨4204952, by rfl⟩ : syracuseStep 5606603 = 8409905) B8409905
theorem B691433 : Blo 459783 691433 := bstep (se 2 (by rfl) ⟨259287, by rfl⟩ : syracuseStep 691433 = 518575) B518575
theorem B625897 : Blo 459783 625897 := bstep (se 2 (by rfl) ⟨234711, by rfl⟩ : syracuseStep 625897 = 469423) B469423
theorem B8228087 : Blo 459783 8228087 := bstep (se 1 (by rfl) ⟨6171065, by rfl⟩ : syracuseStep 8228087 = 12342131) B12342131
theorem B691487 : Blo 459783 691487 := bstep (se 1 (by rfl) ⟨518615, by rfl⟩ : syracuseStep 691487 = 1037231) B1037231
theorem B462111 : Blo 459783 462111 := bstep (se 1 (by rfl) ⟨346583, by rfl⟩ : syracuseStep 462111 = 693167) B693167
theorem B462171 : Blo 459783 462171 := bstep (se 1 (by rfl) ⟨346628, by rfl⟩ : syracuseStep 462171 = 693257) B693257
theorem B462191 : Blo 459783 462191 := bstep (se 1 (by rfl) ⟨346643, by rfl⟩ : syracuseStep 462191 = 693287) B693287
theorem B658811 : Blo 459783 658811 := bstep (se 1 (by rfl) ⟨494108, by rfl⟩ : syracuseStep 658811 = 988217) B988217
theorem B5311873 : Blo 459783 5311873 := bstep (se 2 (by rfl) ⟨1991952, by rfl⟩ : syracuseStep 5311873 = 3983905) B3983905
theorem B462247 : Blo 459783 462247 := bstep (se 1 (by rfl) ⟨346685, by rfl⟩ : syracuseStep 462247 = 693371) B693371
theorem B691655 : Blo 459783 691655 := bstep (se 1 (by rfl) ⟨518741, by rfl⟩ : syracuseStep 691655 = 1037483) B1037483
theorem B462331 : Blo 459783 462331 := bstep (se 1 (by rfl) ⟨346748, by rfl⟩ : syracuseStep 462331 = 693497) B693497
theorem B462399 : Blo 459783 462399 := bstep (se 1 (by rfl) ⟨346799, by rfl⟩ : syracuseStep 462399 = 693599) B693599
theorem B462407 : Blo 459783 462407 := bstep (se 1 (by rfl) ⟨346805, by rfl⟩ : syracuseStep 462407 = 693611) B693611
theorem B2330207 : Blo 459783 2330207 := bstep (se 1 (by rfl) ⟨1747655, by rfl⟩ : syracuseStep 2330207 = 3495311) B3495311
theorem B462559 : Blo 459783 462559 := bstep (se 1 (by rfl) ⟨346919, by rfl⟩ : syracuseStep 462559 = 693839) B693839
theorem B692009 : Blo 459783 692009 := bstep (se 2 (by rfl) ⟨259503, by rfl⟩ : syracuseStep 692009 = 519007) B519007
theorem B692015 : Blo 459783 692015 := bstep (se 1 (by rfl) ⟨519011, by rfl⟩ : syracuseStep 692015 = 1038023) B1038023
theorem B462639 : Blo 459783 462639 := bstep (se 1 (by rfl) ⟨346979, by rfl⟩ : syracuseStep 462639 = 693959) B693959
theorem B1052471 : Blo 459783 1052471 := bstep (se 1 (by rfl) ⟨789353, by rfl⟩ : syracuseStep 1052471 = 1578707) B1578707
theorem B462747 : Blo 459783 462747 := bstep (se 1 (by rfl) ⟨347060, by rfl⟩ : syracuseStep 462747 = 694121) B694121
theorem B1970077 : Blo 459783 1970077 := bstep (se 3 (by rfl) ⟨369389, by rfl⟩ : syracuseStep 1970077 = 738779) B738779
theorem B462799 : Blo 459783 462799 := bstep (se 1 (by rfl) ⟨347099, by rfl⟩ : syracuseStep 462799 = 694199) B694199
theorem B462823 : Blo 459783 462823 := bstep (se 1 (by rfl) ⟨347117, by rfl⟩ : syracuseStep 462823 = 694235) B694235
theorem B3510377 : Blo 459783 3510377 := bstep (se 2 (by rfl) ⟨1316391, by rfl⟩ : syracuseStep 3510377 = 2632783) B2632783
theorem B2101457 : Blo 459783 2101457 := bstep (se 2 (by rfl) ⟨788046, by rfl⟩ : syracuseStep 2101457 = 1576093) B1576093
theorem B692489 : Blo 459783 692489 := bstep (se 2 (by rfl) ⟨259683, by rfl⟩ : syracuseStep 692489 = 519367) B519367
theorem B463135 : Blo 459783 463135 := bstep (se 1 (by rfl) ⟨347351, by rfl⟩ : syracuseStep 463135 = 694703) B694703
theorem B463195 : Blo 459783 463195 := bstep (se 1 (by rfl) ⟨347396, by rfl⟩ : syracuseStep 463195 = 694793) B694793
theorem B987499 : Blo 459783 987499 := bstep (se 1 (by rfl) ⟨740624, by rfl⟩ : syracuseStep 987499 = 1481249) B1481249
theorem B692591 : Blo 459783 692591 := bstep (se 1 (by rfl) ⟨519443, by rfl⟩ : syracuseStep 692591 = 1038887) B1038887
theorem B463215 : Blo 459783 463215 := bstep (se 1 (by rfl) ⟨347411, by rfl⟩ : syracuseStep 463215 = 694823) B694823
theorem B889255 : Blo 459783 889255 := bstep (se 1 (by rfl) ⟨666941, by rfl⟩ : syracuseStep 889255 = 1333883) B1333883
theorem B463271 : Blo 459783 463271 := bstep (se 1 (by rfl) ⟨347453, by rfl⟩ : syracuseStep 463271 = 694907) B694907
theorem B463355 : Blo 459783 463355 := bstep (se 1 (by rfl) ⟨347516, by rfl⟩ : syracuseStep 463355 = 695033) B695033
theorem B463423 : Blo 459783 463423 := bstep (se 1 (by rfl) ⟨347567, by rfl⟩ : syracuseStep 463423 = 695135) B695135
theorem B692807 : Blo 459783 692807 := bstep (se 1 (by rfl) ⟨519605, by rfl⟩ : syracuseStep 692807 = 1039211) B1039211
theorem B463431 : Blo 459783 463431 := bstep (se 1 (by rfl) ⟨347573, by rfl⟩ : syracuseStep 463431 = 695147) B695147
theorem B692843 : Blo 459783 692843 := bstep (se 1 (by rfl) ⟨519632, by rfl⟩ : syracuseStep 692843 = 1039265) B1039265
theorem B2003609 : Blo 459783 2003609 := bstep (se 2 (by rfl) ⟨751353, by rfl⟩ : syracuseStep 2003609 = 1502707) B1502707
theorem B463583 : Blo 459783 463583 := bstep (se 1 (by rfl) ⟨347687, by rfl⟩ : syracuseStep 463583 = 695375) B695375
theorem B463663 : Blo 459783 463663 := bstep (se 1 (by rfl) ⟨347747, by rfl⟩ : syracuseStep 463663 = 695495) B695495
theorem B693071 : Blo 459783 693071 := bstep (se 1 (by rfl) ⟨519803, by rfl⟩ : syracuseStep 693071 = 1039607) B1039607
theorem B463771 : Blo 459783 463771 := bstep (se 1 (by rfl) ⟨347828, by rfl⟩ : syracuseStep 463771 = 695657) B695657
theorem B8852429 : Blo 459783 8852429 := bstep (se 3 (by rfl) ⟨1659830, by rfl⟩ : syracuseStep 8852429 = 3319661) B3319661
theorem B693467 : Blo 459783 693467 := bstep (se 1 (by rfl) ⟨520100, by rfl⟩ : syracuseStep 693467 = 1040201) B1040201
theorem B693641 : Blo 459783 693641 := bstep (se 2 (by rfl) ⟨260115, by rfl⟩ : syracuseStep 693641 = 520231) B520231
theorem B988679 : Blo 459783 988679 := bstep (se 1 (by rfl) ⟨741509, by rfl⟩ : syracuseStep 988679 = 1483019) B1483019
theorem B693995 : Blo 459783 693995 := bstep (se 1 (by rfl) ⟨520496, by rfl⟩ : syracuseStep 693995 = 1040993) B1040993
theorem B5936885 : Blo 459783 5936885 := bstep (se 5 (by rfl) ⟨278291, by rfl⟩ : syracuseStep 5936885 = 556583) B556583
theorem B988969 : Blo 459783 988969 := bstep (se 2 (by rfl) ⟨370863, by rfl⟩ : syracuseStep 988969 = 741727) B741727
theorem B19929037 : Blo 459783 19929037 := bstep (se 3 (by rfl) ⟨3736694, by rfl⟩ : syracuseStep 19929037 = 7473389) B7473389
theorem B694223 : Blo 459783 694223 := bstep (se 1 (by rfl) ⟨520667, by rfl⟩ : syracuseStep 694223 = 1041335) B1041335
theorem B694619 : Blo 459783 694619 := bstep (se 1 (by rfl) ⟨520964, by rfl⟩ : syracuseStep 694619 = 1041929) B1041929
theorem B694847 : Blo 459783 694847 := bstep (se 1 (by rfl) ⟨521135, by rfl⟩ : syracuseStep 694847 = 1042271) B1042271
theorem B694967 : Blo 459783 694967 := bstep (se 1 (by rfl) ⟨521225, by rfl⟩ : syracuseStep 694967 = 1042451) B1042451
theorem B695195 : Blo 459783 695195 := bstep (se 1 (by rfl) ⟨521396, by rfl⟩ : syracuseStep 695195 = 1042793) B1042793
theorem B1186913 : Blo 459783 1186913 := bstep (se 2 (by rfl) ⟨445092, by rfl⟩ : syracuseStep 1186913 = 890185) B890185
theorem B695591 : Blo 459783 695591 := bstep (se 1 (by rfl) ⟨521693, by rfl⟩ : syracuseStep 695591 = 1043387) B1043387
theorem B695675 : Blo 459783 695675 := bstep (se 1 (by rfl) ⟨521756, by rfl⟩ : syracuseStep 695675 = 1043513) B1043513
theorem B1973753 : Blo 459783 1973753 := bstep (se 2 (by rfl) ⟨740157, by rfl⟩ : syracuseStep 1973753 = 1480315) B1480315
theorem B2956961 : Blo 459783 2956961 := bstep (se 2 (by rfl) ⟨1108860, by rfl⟩ : syracuseStep 2956961 = 2217721) B2217721
theorem B2334419 : Blo 459783 2334419 := bstep (se 1 (by rfl) ⟨1750814, by rfl⟩ : syracuseStep 2334419 = 3501629) B3501629
theorem B2006795 : Blo 459783 2006795 := bstep (se 1 (by rfl) ⟨1505096, by rfl⟩ : syracuseStep 2006795 = 3010193) B3010193
theorem B1974077 : Blo 459783 1974077 := bstep (se 3 (by rfl) ⟨370139, by rfl⟩ : syracuseStep 1974077 = 740279) B740279
theorem B9969713 : Blo 459783 9969713 := bstep (se 2 (by rfl) ⟨3738642, by rfl⟩ : syracuseStep 9969713 = 7477285) B7477285
theorem B14983379 : Blo 459783 14983379 := bstep (se 1 (by rfl) ⟨11237534, by rfl⟩ : syracuseStep 14983379 = 22475069) B22475069
theorem B2335067 : Blo 459783 2335067 := bstep (se 1 (by rfl) ⟨1751300, by rfl⟩ : syracuseStep 2335067 = 3502601) B3502601
theorem B1679791 : Blo 459783 1679791 := bstep (se 1 (by rfl) ⟨1259843, by rfl⟩ : syracuseStep 1679791 = 2519687) B2519687
theorem B6758923 : Blo 459783 6758923 := bstep (se 1 (by rfl) ⟨5069192, by rfl⟩ : syracuseStep 6758923 = 10138385) B10138385
theorem B1876651 : Blo 459783 1876651 := bstep (se 1 (by rfl) ⟨1407488, by rfl⟩ : syracuseStep 1876651 = 2814977) B2814977
theorem B3810007 : Blo 459783 3810007 := bstep (se 1 (by rfl) ⟨2857505, by rfl⟩ : syracuseStep 3810007 = 5715011) B5715011
theorem B2630393 : Blo 459783 2630393 := bstep (se 2 (by rfl) ⟨986397, by rfl⟩ : syracuseStep 2630393 = 1972795) B1972795
theorem B42738445 : Blo 459783 42738445 := bstep (se 3 (by rfl) ⟨8013458, by rfl⟩ : syracuseStep 42738445 = 16026917) B16026917
theorem B4727699 : Blo 459783 4727699 := bstep (se 1 (by rfl) ⟨3545774, by rfl⟩ : syracuseStep 4727699 = 7091549) B7091549
theorem B6661237 : Blo 459783 6661237 := bstep (se 5 (by rfl) ⟨312245, by rfl⟩ : syracuseStep 6661237 = 624491) B624491
theorem B1320151 : Blo 459783 1320151 := bstep (se 1 (by rfl) ⟨990113, by rfl⟩ : syracuseStep 1320151 = 1980227) B1980227
theorem B1975529 : Blo 459783 1975529 := bstep (se 2 (by rfl) ⟨740823, by rfl⟩ : syracuseStep 1975529 = 1481647) B1481647
theorem B2336039 : Blo 459783 2336039 := bstep (se 1 (by rfl) ⟨1752029, by rfl⟩ : syracuseStep 2336039 = 3504059) B3504059
theorem B1582649 : Blo 459783 1582649 := bstep (se 2 (by rfl) ⟨593493, by rfl⟩ : syracuseStep 1582649 = 1186987) B1186987
theorem B2631325 : Blo 459783 2631325 := bstep (se 3 (by rfl) ⟨493373, by rfl⟩ : syracuseStep 2631325 = 986747) B986747
theorem B1747079 : Blo 459783 1747079 := bstep (se 1 (by rfl) ⟨1310309, by rfl⟩ : syracuseStep 1747079 = 2620619) B2620619
theorem B2338145 : Blo 459783 2338145 := bstep (se 2 (by rfl) ⟨876804, by rfl⟩ : syracuseStep 2338145 = 1753609) B1753609
theorem B2633057 : Blo 459783 2633057 := bstep (se 2 (by rfl) ⟨987396, by rfl⟩ : syracuseStep 2633057 = 1974793) B1974793
theorem B10136951 : Blo 459783 10136951 := bstep (se 1 (by rfl) ⟨7602713, by rfl⟩ : syracuseStep 10136951 = 15205427) B15205427
theorem B2993773 : Blo 459783 2993773 := bstep (se 3 (by rfl) ⟨561332, by rfl⟩ : syracuseStep 2993773 = 1122665) B1122665
theorem B1552175 : Blo 459783 1552175 := bstep (se 1 (by rfl) ⟨1164131, by rfl⟩ : syracuseStep 1552175 = 2328263) B2328263
theorem B2502809 : Blo 459783 2502809 := bstep (se 2 (by rfl) ⟨938553, by rfl⟩ : syracuseStep 2502809 = 1877107) B1877107
theorem B71840033 : Blo 459783 71840033 := bstep (se 2 (by rfl) ⟨26940012, by rfl⟩ : syracuseStep 71840033 = 53880025) B53880025
theorem B4436329 : Blo 459783 4436329 := bstep (se 2 (by rfl) ⟨1663623, by rfl⟩ : syracuseStep 4436329 = 3327247) B3327247
theorem B2896235 : Blo 459783 2896235 := bstep (se 1 (by rfl) ⟨2172176, by rfl⟩ : syracuseStep 2896235 = 4344353) B4344353
theorem B1978825 : Blo 459783 1978825 := bstep (se 2 (by rfl) ⟨742059, by rfl⟩ : syracuseStep 1978825 = 1484119) B1484119
theorem B4502585 : Blo 459783 4502585 := bstep (se 2 (by rfl) ⟨1688469, by rfl⟩ : syracuseStep 4502585 = 3376939) B3376939
theorem B2340089 : Blo 459783 2340089 := bstep (se 2 (by rfl) ⟨877533, by rfl⟩ : syracuseStep 2340089 = 1755067) B1755067
theorem B832799 : Blo 459783 832799 := bstep (se 1 (by rfl) ⟨624599, by rfl⟩ : syracuseStep 832799 = 1249199) B1249199
theorem B4437287 : Blo 459783 4437287 := bstep (se 1 (by rfl) ⟨3327965, by rfl⟩ : syracuseStep 4437287 = 6655931) B6655931
theorem B2503979 : Blo 459783 2503979 := bstep (se 1 (by rfl) ⟨1877984, by rfl⟩ : syracuseStep 2503979 = 3755969) B3755969
theorem B4208165 : Blo 459783 4208165 := bstep (se 4 (by rfl) ⟨394515, by rfl⟩ : syracuseStep 4208165 = 789031) B789031
theorem B1783453 : Blo 459783 1783453 := bstep (se 3 (by rfl) ⟨334397, by rfl⟩ : syracuseStep 1783453 = 668795) B668795
theorem B3159737 : Blo 459783 3159737 := bstep (se 2 (by rfl) ⟨1184901, by rfl⟩ : syracuseStep 3159737 = 2369803) B2369803
theorem B1554281 : Blo 459783 1554281 := bstep (se 2 (by rfl) ⟨582855, by rfl⟩ : syracuseStep 1554281 = 1165711) B1165711
theorem B1554713 : Blo 459783 1554713 := bstep (se 2 (by rfl) ⟨583017, by rfl⟩ : syracuseStep 1554713 = 1166035) B1166035
theorem B5257547 : Blo 459783 5257547 := bstep (se 1 (by rfl) ⟨3943160, by rfl⟩ : syracuseStep 5257547 = 7886321) B7886321
theorem B834119 : Blo 459783 834119 := bstep (se 1 (by rfl) ⟨625589, by rfl⟩ : syracuseStep 834119 = 1251179) B1251179
theorem B834155 : Blo 459783 834155 := bstep (se 1 (by rfl) ⟨625616, by rfl⟩ : syracuseStep 834155 = 1251233) B1251233
theorem B1621367 : Blo 459783 1621367 := bstep (se 1 (by rfl) ⟨1216025, by rfl⟩ : syracuseStep 1621367 = 2432051) B2432051
theorem B1556063 : Blo 459783 1556063 := bstep (se 1 (by rfl) ⟨1167047, by rfl⟩ : syracuseStep 1556063 = 2334095) B2334095
theorem B1261291 : Blo 459783 1261291 := bstep (se 1 (by rfl) ⟨945968, by rfl⟩ : syracuseStep 1261291 = 1891937) B1891937
theorem B2801411 : Blo 459783 2801411 := bstep (se 1 (by rfl) ⟨2101058, by rfl⟩ : syracuseStep 2801411 = 4202117) B4202117
theorem B4440977 : Blo 459783 4440977 := bstep (se 2 (by rfl) ⟨1665366, by rfl⟩ : syracuseStep 4440977 = 3330733) B3330733
theorem B1164203 : Blo 459783 1164203 := bstep (se 1 (by rfl) ⟨873152, by rfl⟩ : syracuseStep 1164203 = 1746305) B1746305
theorem B1557467 : Blo 459783 1557467 := bstep (se 1 (by rfl) ⟨1168100, by rfl⟩ : syracuseStep 1557467 = 2336201) B2336201
theorem B1557629 : Blo 459783 1557629 := bstep (se 3 (by rfl) ⟨292055, by rfl⟩ : syracuseStep 1557629 = 584111) B584111
theorem B1557737 : Blo 459783 1557737 := bstep (se 2 (by rfl) ⟨584151, by rfl⟩ : syracuseStep 1557737 = 1168303) B1168303
theorem B2344301 : Blo 459783 2344301 := bstep (se 3 (by rfl) ⟨439556, by rfl⟩ : syracuseStep 2344301 = 879113) B879113
theorem B1557899 : Blo 459783 1557899 := bstep (se 1 (by rfl) ⟨1168424, by rfl⟩ : syracuseStep 1557899 = 2336849) B2336849
theorem B5916077 : Blo 459783 5916077 := bstep (se 3 (by rfl) ⟨1109264, by rfl⟩ : syracuseStep 5916077 = 2218529) B2218529
theorem B1165063 : Blo 459783 1165063 := bstep (se 1 (by rfl) ⟨873797, by rfl⟩ : syracuseStep 1165063 = 1747595) B1747595
theorem B1165337 : Blo 459783 1165337 := bstep (se 2 (by rfl) ⟨437001, by rfl⟩ : syracuseStep 1165337 = 874003) B874003
theorem B1034603 : Blo 459783 1034603 := bstep (se 1 (by rfl) ⟨775952, by rfl⟩ : syracuseStep 1034603 = 1551905) B1551905
theorem B1034747 : Blo 459783 1034747 := bstep (se 1 (by rfl) ⟨776060, by rfl⟩ : syracuseStep 1034747 = 1552121) B1552121
theorem B1034873 : Blo 459783 1034873 := bstep (se 2 (by rfl) ⟨388077, by rfl⟩ : syracuseStep 1034873 = 776155) B776155
theorem B1034927 : Blo 459783 1034927 := bstep (se 1 (by rfl) ⟨776195, by rfl⟩ : syracuseStep 1034927 = 1552391) B1552391
theorem B1034999 : Blo 459783 1034999 := bstep (se 1 (by rfl) ⟨776249, by rfl⟩ : syracuseStep 1034999 = 1552499) B1552499
theorem B2214647 : Blo 459783 2214647 := bstep (se 1 (by rfl) ⟨1660985, by rfl⟩ : syracuseStep 2214647 = 3321971) B3321971
theorem B1035179 : Blo 459783 1035179 := bstep (se 1 (by rfl) ⟨776384, by rfl⟩ : syracuseStep 1035179 = 1552769) B1552769
theorem B8801459 : Blo 459783 8801459 := bstep (se 1 (by rfl) ⟨6601094, by rfl⟩ : syracuseStep 8801459 = 13202189) B13202189
theorem B1035719 : Blo 459783 1035719 := bstep (se 1 (by rfl) ⟨776789, by rfl⟩ : syracuseStep 1035719 = 1553579) B1553579
theorem B2346731 : Blo 459783 2346731 := bstep (se 1 (by rfl) ⟨1760048, by rfl⟩ : syracuseStep 2346731 = 3520097) B3520097
theorem B1036079 : Blo 459783 1036079 := bstep (se 1 (by rfl) ⟨777059, by rfl⟩ : syracuseStep 1036079 = 1554119) B1554119
theorem B937775 : Blo 459783 937775 := bstep (se 1 (by rfl) ⟨703331, by rfl⟩ : syracuseStep 937775 = 1406663) B1406663
theorem B4214585 : Blo 459783 4214585 := bstep (se 2 (by rfl) ⟨1580469, by rfl⟩ : syracuseStep 4214585 = 3160939) B3160939
theorem B1167311 : Blo 459783 1167311 := bstep (se 1 (by rfl) ⟨875483, by rfl⟩ : syracuseStep 1167311 = 1750967) B1750967
theorem B3493853 : Blo 459783 3493853 := bstep (se 3 (by rfl) ⟨655097, by rfl⟩ : syracuseStep 3493853 = 1310195) B1310195
theorem B2347217 : Blo 459783 2347217 := bstep (se 2 (by rfl) ⟨880206, by rfl⟩ : syracuseStep 2347217 = 1760413) B1760413
theorem B1560923 : Blo 459783 1560923 := bstep (se 1 (by rfl) ⟨1170692, by rfl⟩ : syracuseStep 1560923 = 2341385) B2341385
theorem B1036655 : Blo 459783 1036655 := bstep (se 1 (by rfl) ⟨777491, by rfl⟩ : syracuseStep 1036655 = 1554983) B1554983
theorem B1036727 : Blo 459783 1036727 := bstep (se 1 (by rfl) ⟨777545, by rfl⟩ : syracuseStep 1036727 = 1555091) B1555091
theorem B873031 : Blo 459783 873031 := bstep (se 1 (by rfl) ⟨654773, by rfl⟩ : syracuseStep 873031 = 1309547) B1309547
theorem B1036871 : Blo 459783 1036871 := bstep (se 1 (by rfl) ⟨777653, by rfl⟩ : syracuseStep 1036871 = 1555307) B1555307
theorem B1036907 : Blo 459783 1036907 := bstep (se 1 (by rfl) ⟨777680, by rfl⟩ : syracuseStep 1036907 = 1555361) B1555361
theorem B1167979 : Blo 459783 1167979 := bstep (se 1 (by rfl) ⟨875984, by rfl⟩ : syracuseStep 1167979 = 1751969) B1751969
theorem B2347703 : Blo 459783 2347703 := bstep (se 1 (by rfl) ⟨1760777, by rfl⟩ : syracuseStep 2347703 = 3521555) B3521555
theorem B1168283 : Blo 459783 1168283 := bstep (se 1 (by rfl) ⟨876212, by rfl⟩ : syracuseStep 1168283 = 1752425) B1752425
theorem B1037303 : Blo 459783 1037303 := bstep (se 1 (by rfl) ⟨777977, by rfl⟩ : syracuseStep 1037303 = 1555955) B1555955
theorem B1168627 : Blo 459783 1168627 := bstep (se 1 (by rfl) ⟨876470, by rfl⟩ : syracuseStep 1168627 = 1752941) B1752941
theorem B4445441 : Blo 459783 4445441 := bstep (se 2 (by rfl) ⟨1667040, by rfl⟩ : syracuseStep 4445441 = 3334081) B3334081
theorem B873767 : Blo 459783 873767 := bstep (se 1 (by rfl) ⟨655325, by rfl⟩ : syracuseStep 873767 = 1310651) B1310651
theorem B1561895 : Blo 459783 1561895 := bstep (se 1 (by rfl) ⟨1171421, by rfl⟩ : syracuseStep 1561895 = 2342843) B2342843
theorem B3986783 : Blo 459783 3986783 := bstep (se 1 (by rfl) ⟨2990087, by rfl⟩ : syracuseStep 3986783 = 5980175) B5980175
theorem B1037663 : Blo 459783 1037663 := bstep (se 1 (by rfl) ⟨778247, by rfl⟩ : syracuseStep 1037663 = 1556495) B1556495
theorem B1038059 : Blo 459783 1038059 := bstep (se 1 (by rfl) ⟨778544, by rfl⟩ : syracuseStep 1038059 = 1557089) B1557089
theorem B775993 : Blo 459783 775993 := bstep (se 2 (by rfl) ⟨290997, by rfl⟩ : syracuseStep 775993 = 581995) B581995
theorem B1038185 : Blo 459783 1038185 := bstep (se 2 (by rfl) ⟨389319, by rfl⟩ : syracuseStep 1038185 = 778639) B778639
theorem B1169417 : Blo 459783 1169417 := bstep (se 2 (by rfl) ⟨438531, by rfl⟩ : syracuseStep 1169417 = 877063) B877063
theorem B776297 : Blo 459783 776297 := bstep (se 2 (by rfl) ⟨291111, by rfl⟩ : syracuseStep 776297 = 582223) B582223
theorem B1562759 : Blo 459783 1562759 := bstep (se 1 (by rfl) ⟨1172069, by rfl⟩ : syracuseStep 1562759 = 2344139) B2344139
theorem B1039031 : Blo 459783 1039031 := bstep (se 1 (by rfl) ⟨779273, by rfl⟩ : syracuseStep 1039031 = 1558547) B1558547
theorem B5593859 : Blo 459783 5593859 := bstep (se 1 (by rfl) ⟨4195394, by rfl⟩ : syracuseStep 5593859 = 8390789) B8390789
theorem B5266295 : Blo 459783 5266295 := bstep (se 1 (by rfl) ⟨3949721, by rfl⟩ : syracuseStep 5266295 = 7899443) B7899443
theorem B1039247 : Blo 459783 1039247 := bstep (se 1 (by rfl) ⟨779435, by rfl⟩ : syracuseStep 1039247 = 1558871) B1558871
theorem B2808749 : Blo 459783 2808749 := bstep (se 3 (by rfl) ⟨526640, by rfl⟩ : syracuseStep 2808749 = 1053281) B1053281
theorem B1170571 : Blo 459783 1170571 := bstep (se 1 (by rfl) ⟨877928, by rfl⟩ : syracuseStep 1170571 = 1755857) B1755857
theorem B1564001 : Blo 459783 1564001 := bstep (se 2 (by rfl) ⟨586500, by rfl⟩ : syracuseStep 1564001 = 1173001) B1173001
theorem B1170875 : Blo 459783 1170875 := bstep (se 1 (by rfl) ⟨878156, by rfl⟩ : syracuseStep 1170875 = 1756313) B1756313
theorem B777721 : Blo 459783 777721 := bstep (se 2 (by rfl) ⟨291645, by rfl⟩ : syracuseStep 777721 = 583291) B583291
theorem B1039967 : Blo 459783 1039967 := bstep (se 1 (by rfl) ⟨779975, by rfl⟩ : syracuseStep 1039967 = 1559951) B1559951
theorem B7921313 : Blo 459783 7921313 := bstep (se 2 (by rfl) ⟨2970492, by rfl⟩ : syracuseStep 7921313 = 5940985) B5940985
theorem B777991 : Blo 459783 777991 := bstep (se 1 (by rfl) ⟨583493, by rfl⟩ : syracuseStep 777991 = 1166987) B1166987
theorem B778025 : Blo 459783 778025 := bstep (se 2 (by rfl) ⟨291759, by rfl⟩ : syracuseStep 778025 = 583519) B583519
theorem B1040183 : Blo 459783 1040183 := bstep (se 1 (by rfl) ⟨780137, by rfl⟩ : syracuseStep 1040183 = 1560275) B1560275
theorem B1040489 : Blo 459783 1040489 := bstep (se 2 (by rfl) ⟨390183, by rfl⟩ : syracuseStep 1040489 = 780367) B780367
theorem B3563939 : Blo 459783 3563939 := bstep (se 1 (by rfl) ⟨2672954, by rfl⟩ : syracuseStep 3563939 = 5345909) B5345909
theorem B778747 : Blo 459783 778747 := bstep (se 1 (by rfl) ⟨584060, by rfl⟩ : syracuseStep 778747 = 1168121) B1168121
theorem B13263425 : Blo 459783 13263425 := bstep (se 2 (by rfl) ⟨4973784, by rfl⟩ : syracuseStep 13263425 = 9947569) B9947569
theorem B1040975 : Blo 459783 1040975 := bstep (se 1 (by rfl) ⟨780731, by rfl⟩ : syracuseStep 1040975 = 1561463) B1561463
theorem B582319 : Blo 459783 582319 := bstep (se 1 (by rfl) ⟨436739, by rfl⟩ : syracuseStep 582319 = 873479) B873479
theorem B10019537 : Blo 459783 10019537 := bstep (se 2 (by rfl) ⟨3757326, by rfl⟩ : syracuseStep 10019537 = 7514653) B7514653
theorem B1041119 : Blo 459783 1041119 := bstep (se 1 (by rfl) ⟨780839, by rfl⟩ : syracuseStep 1041119 = 1561679) B1561679
theorem B1172191 : Blo 459783 1172191 := bstep (se 1 (by rfl) ⟨879143, by rfl⟩ : syracuseStep 1172191 = 1758287) B1758287
theorem B1172303 : Blo 459783 1172303 := bstep (se 1 (by rfl) ⟨879227, by rfl⟩ : syracuseStep 1172303 = 1758455) B1758455
theorem B5006225 : Blo 459783 5006225 := bstep (se 2 (by rfl) ⟨1877334, by rfl⟩ : syracuseStep 5006225 = 3754669) B3754669
theorem B779179 : Blo 459783 779179 := bstep (se 1 (by rfl) ⟨584384, by rfl⟩ : syracuseStep 779179 = 1168769) B1168769
theorem B1041371 : Blo 459783 1041371 := bstep (se 1 (by rfl) ⟨781028, by rfl⟩ : syracuseStep 1041371 = 1562057) B1562057
theorem B1041551 : Blo 459783 1041551 := bstep (se 1 (by rfl) ⟨781163, by rfl⟩ : syracuseStep 1041551 = 1562327) B1562327
theorem B779483 : Blo 459783 779483 := bstep (se 1 (by rfl) ⟨584612, by rfl⟩ : syracuseStep 779483 = 1169225) B1169225
theorem B1041641 : Blo 459783 1041641 := bstep (se 2 (by rfl) ⟨390615, by rfl⟩ : syracuseStep 1041641 = 781231) B781231
theorem B1041695 : Blo 459783 1041695 := bstep (se 1 (by rfl) ⟨781271, by rfl⟩ : syracuseStep 1041695 = 1562543) B1562543
theorem B779719 : Blo 459783 779719 := bstep (se 1 (by rfl) ⟨584789, by rfl⟩ : syracuseStep 779719 = 1169579) B1169579
theorem B1172951 : Blo 459783 1172951 := bstep (se 1 (by rfl) ⟨879713, by rfl⟩ : syracuseStep 1172951 = 1759427) B1759427
theorem B517855 : Blo 459783 517855 := bstep (se 1 (by rfl) ⟨388391, by rfl⟩ : syracuseStep 517855 = 776783) B776783
theorem B878377 : Blo 459783 878377 := bstep (se 2 (by rfl) ⟨329391, by rfl⟩ : syracuseStep 878377 = 658783) B658783
theorem B1042217 : Blo 459783 1042217 := bstep (se 2 (by rfl) ⟨390831, by rfl⟩ : syracuseStep 1042217 = 781663) B781663
theorem B1173305 : Blo 459783 1173305 := bstep (se 2 (by rfl) ⟨439989, by rfl⟩ : syracuseStep 1173305 = 879979) B879979
theorem B33613643 : Blo 459783 33613643 := bstep (se 1 (by rfl) ⟨25210232, by rfl⟩ : syracuseStep 33613643 = 50420465) B50420465
theorem B2844497 : Blo 459783 2844497 := bstep (se 2 (by rfl) ⟨1066686, by rfl⟩ : syracuseStep 2844497 = 2133373) B2133373
theorem B1664849 : Blo 459783 1664849 := bstep (se 2 (by rfl) ⟨624318, by rfl⟩ : syracuseStep 1664849 = 1248637) B1248637
theorem B780239 : Blo 459783 780239 := bstep (se 1 (by rfl) ⟨585179, by rfl⟩ : syracuseStep 780239 = 1170359) B1170359
theorem B518431 : Blo 459783 518431 := bstep (se 1 (by rfl) ⟨388823, by rfl⟩ : syracuseStep 518431 = 777647) B777647
theorem B518719 : Blo 459783 518719 := bstep (se 1 (by rfl) ⟨389039, by rfl⟩ : syracuseStep 518719 = 778079) B778079
theorem B879167 : Blo 459783 879167 := bstep (se 1 (by rfl) ⟨659375, by rfl⟩ : syracuseStep 879167 = 1318751) B1318751
theorem B584263 : Blo 459783 584263 := bstep (se 1 (by rfl) ⟨438197, by rfl⟩ : syracuseStep 584263 = 876395) B876395
theorem B780907 : Blo 459783 780907 := bstep (se 1 (by rfl) ⟨585680, by rfl⟩ : syracuseStep 780907 = 1171361) B1171361
theorem B1043279 : Blo 459783 1043279 := bstep (se 1 (by rfl) ⟨782459, by rfl⟩ : syracuseStep 1043279 = 1564919) B1564919
theorem B781211 : Blo 459783 781211 := bstep (se 1 (by rfl) ⟨585908, by rfl⟩ : syracuseStep 781211 = 1171817) B1171817
theorem B31878157 : Blo 459783 31878157 := bstep (se 3 (by rfl) ⟨5977154, by rfl⟩ : syracuseStep 31878157 = 11954309) B11954309
theorem B1043495 : Blo 459783 1043495 := bstep (se 1 (by rfl) ⟨782621, by rfl⟩ : syracuseStep 1043495 = 1565243) B1565243
theorem B7334993 : Blo 459783 7334993 := bstep (se 2 (by rfl) ⟨2750622, by rfl⟩ : syracuseStep 7334993 = 5501245) B5501245
theorem B879835 : Blo 459783 879835 := bstep (se 1 (by rfl) ⟨659876, by rfl⟩ : syracuseStep 879835 = 1319753) B1319753
theorem B519547 : Blo 459783 519547 := bstep (se 1 (by rfl) ⟨389660, by rfl⟩ : syracuseStep 519547 = 779321) B779321
theorem B585083 : Blo 459783 585083 := bstep (se 1 (by rfl) ⟨438812, by rfl⟩ : syracuseStep 585083 = 877625) B877625
theorem B4746761 : Blo 459783 4746761 := bstep (se 2 (by rfl) ⟨1780035, by rfl⟩ : syracuseStep 4746761 = 3560071) B3560071
theorem B4222763 : Blo 459783 4222763 := bstep (se 1 (by rfl) ⟨3167072, by rfl⟩ : syracuseStep 4222763 = 6334145) B6334145
theorem B520015 : Blo 459783 520015 := bstep (se 1 (by rfl) ⟨390011, by rfl⟩ : syracuseStep 520015 = 780023) B780023
theorem B4255811 : Blo 459783 4255811 := bstep (se 1 (by rfl) ⟨3191858, by rfl⟩ : syracuseStep 4255811 = 6383717) B6383717
theorem B3960899 : Blo 459783 3960899 := bstep (se 1 (by rfl) ⟨2970674, by rfl⟩ : syracuseStep 3960899 = 5941349) B5941349
theorem B520411 : Blo 459783 520411 := bstep (se 1 (by rfl) ⟨390308, by rfl⟩ : syracuseStep 520411 = 780617) B780617
theorem B3567887 : Blo 459783 3567887 := bstep (se 1 (by rfl) ⟨2675915, by rfl⟩ : syracuseStep 3567887 = 5351831) B5351831
theorem B520699 : Blo 459783 520699 := bstep (se 1 (by rfl) ⟨390524, by rfl⟩ : syracuseStep 520699 = 781049) B781049
theorem B5009939 : Blo 459783 5009939 := bstep (se 1 (by rfl) ⟨3757454, by rfl⟩ : syracuseStep 5009939 = 7514909) B7514909
theorem B520879 : Blo 459783 520879 := bstep (se 1 (by rfl) ⟨390659, by rfl⟩ : syracuseStep 520879 = 781319) B781319
theorem B521167 : Blo 459783 521167 := bstep (se 1 (by rfl) ⟨390875, by rfl⟩ : syracuseStep 521167 = 781751) B781751
theorem B586703 : Blo 459783 586703 := bstep (se 1 (by rfl) ⟨440027, by rfl⟩ : syracuseStep 586703 = 880055) B880055
theorem B13300787 : Blo 459783 13300787 := bstep (se 1 (by rfl) ⟨9975590, by rfl⟩ : syracuseStep 13300787 = 19951181) B19951181
theorem B2847869 : Blo 459783 2847869 := bstep (se 3 (by rfl) ⟨533975, by rfl⟩ : syracuseStep 2847869 = 1067951) B1067951
theorem B521563 : Blo 459783 521563 := bstep (se 1 (by rfl) ⟨391172, by rfl⟩ : syracuseStep 521563 = 782345) B782345
theorem B8975711 : Blo 459783 8975711 := bstep (se 1 (by rfl) ⟨6731783, by rfl⟩ : syracuseStep 8975711 = 13463567) B13463567
theorem B2618729 : Blo 459783 2618729 := bstep (se 2 (by rfl) ⟨982023, by rfl⟩ : syracuseStep 2618729 = 1964047) B1964047
theorem B521671 : Blo 459783 521671 := bstep (se 1 (by rfl) ⟨391253, by rfl⟩ : syracuseStep 521671 = 782507) B782507
theorem B18708317 : Blo 459783 18708317 := bstep (se 3 (by rfl) ⟨3507809, by rfl⟩ : syracuseStep 18708317 = 7015619) B7015619
theorem B752303 : Blo 459783 752303 := bstep (se 1 (by rfl) ⟨564227, by rfl⟩ : syracuseStep 752303 = 1128455) B1128455
theorem B1866791 : Blo 459783 1866791 := bstep (se 1 (by rfl) ⟨1400093, by rfl⟩ : syracuseStep 1866791 = 2800187) B2800187
theorem B4455587 : Blo 459783 4455587 := bstep (se 1 (by rfl) ⟨3341690, by rfl⟩ : syracuseStep 4455587 = 6683381) B6683381
theorem B556411 : Blo 459783 556411 := bstep (se 1 (by rfl) ⟨417308, by rfl⟩ : syracuseStep 556411 = 834617) B834617
theorem B621961 : Blo 459783 621961 := bstep (se 2 (by rfl) ⟨233235, by rfl⟩ : syracuseStep 621961 = 466471) B466471
theorem B982459 : Blo 459783 982459 := bstep (se 1 (by rfl) ⟨736844, by rfl⟩ : syracuseStep 982459 = 1473689) B1473689
theorem B1244605 : Blo 459783 1244605 := bstep (se 3 (by rfl) ⟨233363, by rfl⟩ : syracuseStep 1244605 = 466727) B466727
theorem B2817899 : Blo 459783 2817899 := bstep (se 1 (by rfl) ⟨2113424, by rfl⟩ : syracuseStep 2817899 = 4226849) B4226849
theorem B1474433 : Blo 459783 1474433 := bstep (se 2 (by rfl) ⟨552912, by rfl⟩ : syracuseStep 1474433 = 1105825) B1105825
theorem B655975 : Blo 459783 655975 := bstep (se 1 (by rfl) ⟨491981, by rfl⟩ : syracuseStep 655975 = 983963) B983963
theorem B9011897 : Blo 459783 9011897 := bstep (se 2 (by rfl) ⟨3379461, by rfl⟩ : syracuseStep 9011897 = 6758923) B6758923
theorem B43254577 : Blo 459783 43254577 := bstep (se 2 (by rfl) ⟨16220466, by rfl⟩ : syracuseStep 43254577 = 32440933) B32440933
theorem B2622395 : Blo 459783 2622395 := bstep (se 1 (by rfl) ⟨1966796, by rfl⟩ : syracuseStep 2622395 = 3933593) B3933593
theorem B5080009 : Blo 459783 5080009 := bstep (se 2 (by rfl) ⟨1905003, by rfl⟩ : syracuseStep 5080009 = 3810007) B3810007
theorem B56984593 : Blo 459783 56984593 := bstep (se 2 (by rfl) ⟨21369222, by rfl⟩ : syracuseStep 56984593 = 42738445) B42738445
theorem B459839 : Blo 459783 459839 := bstep (se 1 (by rfl) ⟨344879, by rfl⟩ : syracuseStep 459839 = 689759) B689759
theorem B9503837 : Blo 459783 9503837 := bstep (se 3 (by rfl) ⟨1781969, by rfl⟩ : syracuseStep 9503837 = 3563939) B3563939
theorem B459983 : Blo 459783 459983 := bstep (se 1 (by rfl) ⟨344987, by rfl⟩ : syracuseStep 459983 = 689975) B689975
theorem B460187 : Blo 459783 460187 := bstep (se 1 (by rfl) ⟨345140, by rfl⟩ : syracuseStep 460187 = 690281) B690281
theorem B656795 : Blo 459783 656795 := bstep (se 1 (by rfl) ⟨492596, by rfl⟩ : syracuseStep 656795 = 985193) B985193
theorem B8881649 : Blo 459783 8881649 := bstep (se 2 (by rfl) ⟨3330618, by rfl⟩ : syracuseStep 8881649 = 6661237) B6661237
theorem B984595 : Blo 459783 984595 := bstep (se 1 (by rfl) ⟨738446, by rfl⟩ : syracuseStep 984595 = 1476893) B1476893
theorem B689735 : Blo 459783 689735 := bstep (se 1 (by rfl) ⟨517301, by rfl⟩ : syracuseStep 689735 = 1034603) B1034603
theorem B460399 : Blo 459783 460399 := bstep (se 1 (by rfl) ⟨345299, by rfl⟩ : syracuseStep 460399 = 690599) B690599
theorem B689831 : Blo 459783 689831 := bstep (se 1 (by rfl) ⟨517373, by rfl⟩ : syracuseStep 689831 = 1034747) B1034747
theorem B460455 : Blo 459783 460455 := bstep (se 1 (by rfl) ⟨345341, by rfl⟩ : syracuseStep 460455 = 690683) B690683
theorem B689915 : Blo 459783 689915 := bstep (se 1 (by rfl) ⟨517436, by rfl⟩ : syracuseStep 689915 = 1034873) B1034873
theorem B460539 : Blo 459783 460539 := bstep (se 1 (by rfl) ⟨345404, by rfl⟩ : syracuseStep 460539 = 690809) B690809
theorem B1312519 : Blo 459783 1312519 := bstep (se 1 (by rfl) ⟨984389, by rfl⟩ : syracuseStep 1312519 = 1968779) B1968779
theorem B689951 : Blo 459783 689951 := bstep (se 1 (by rfl) ⟨517463, by rfl⟩ : syracuseStep 689951 = 1034927) B1034927
theorem B460575 : Blo 459783 460575 := bstep (se 1 (by rfl) ⟨345431, by rfl⟩ : syracuseStep 460575 = 690863) B690863
theorem B460607 : Blo 459783 460607 := bstep (se 1 (by rfl) ⟨345455, by rfl⟩ : syracuseStep 460607 = 690911) B690911
theorem B689999 : Blo 459783 689999 := bstep (se 1 (by rfl) ⟨517499, by rfl⟩ : syracuseStep 689999 = 1034999) B1034999
theorem B1476431 : Blo 459783 1476431 := bstep (se 1 (by rfl) ⟨1107323, by rfl⟩ : syracuseStep 1476431 = 2214647) B2214647
theorem B1181537 : Blo 459783 1181537 := bstep (se 2 (by rfl) ⟨443076, by rfl⟩ : syracuseStep 1181537 = 886153) B886153
theorem B690119 : Blo 459783 690119 := bstep (se 1 (by rfl) ⟨517589, by rfl⟩ : syracuseStep 690119 = 1035179) B1035179
theorem B985031 : Blo 459783 985031 := bstep (se 1 (by rfl) ⟨738773, by rfl⟩ : syracuseStep 985031 = 1477547) B1477547
theorem B460783 : Blo 459783 460783 := bstep (se 1 (by rfl) ⟨345587, by rfl⟩ : syracuseStep 460783 = 691175) B691175
theorem B5867639 : Blo 459783 5867639 := bstep (se 1 (by rfl) ⟨4400729, by rfl⟩ : syracuseStep 5867639 = 8801459) B8801459
theorem B3737735 : Blo 459783 3737735 := bstep (se 1 (by rfl) ⟨2803301, by rfl⟩ : syracuseStep 3737735 = 5606603) B5606603
theorem B460955 : Blo 459783 460955 := bstep (se 1 (by rfl) ⟨345716, by rfl⟩ : syracuseStep 460955 = 691433) B691433
theorem B460991 : Blo 459783 460991 := bstep (se 1 (by rfl) ⟨345743, by rfl⟩ : syracuseStep 460991 = 691487) B691487
theorem B3508433 : Blo 459783 3508433 := bstep (se 2 (by rfl) ⟨1315662, by rfl⟩ : syracuseStep 3508433 = 2631325) B2631325
theorem B690473 : Blo 459783 690473 := bstep (se 2 (by rfl) ⟨258927, by rfl⟩ : syracuseStep 690473 = 517855) B517855
theorem B690479 : Blo 459783 690479 := bstep (se 1 (by rfl) ⟨517859, by rfl⟩ : syracuseStep 690479 = 1035719) B1035719
theorem B461103 : Blo 459783 461103 := bstep (se 1 (by rfl) ⟨345827, by rfl⟩ : syracuseStep 461103 = 691655) B691655
theorem B461339 : Blo 459783 461339 := bstep (se 1 (by rfl) ⟨346004, by rfl⟩ : syracuseStep 461339 = 692009) B692009
theorem B690719 : Blo 459783 690719 := bstep (se 1 (by rfl) ⟨518039, by rfl⟩ : syracuseStep 690719 = 1036079) B1036079
theorem B461343 : Blo 459783 461343 := bstep (se 1 (by rfl) ⟨346007, by rfl⟩ : syracuseStep 461343 = 692015) B692015
theorem B1968745 : Blo 459783 1968745 := bstep (se 2 (by rfl) ⟨738279, by rfl⟩ : syracuseStep 1968745 = 1476559) B1476559
theorem B2329235 : Blo 459783 2329235 := bstep (se 1 (by rfl) ⟨1746926, by rfl⟩ : syracuseStep 2329235 = 3493853) B3493853
theorem B461659 : Blo 459783 461659 := bstep (se 1 (by rfl) ⟨346244, by rfl⟩ : syracuseStep 461659 = 692489) B692489
theorem B691103 : Blo 459783 691103 := bstep (se 1 (by rfl) ⟨518327, by rfl⟩ : syracuseStep 691103 = 1036655) B1036655
theorem B461727 : Blo 459783 461727 := bstep (se 1 (by rfl) ⟨346295, by rfl⟩ : syracuseStep 461727 = 692591) B692591
theorem B691151 : Blo 459783 691151 := bstep (se 1 (by rfl) ⟨518363, by rfl⟩ : syracuseStep 691151 = 1036727) B1036727
theorem B691241 : Blo 459783 691241 := bstep (se 2 (by rfl) ⟨259215, by rfl⟩ : syracuseStep 691241 = 518431) B518431
theorem B691247 : Blo 459783 691247 := bstep (se 1 (by rfl) ⟨518435, by rfl⟩ : syracuseStep 691247 = 1036871) B1036871
theorem B461871 : Blo 459783 461871 := bstep (se 1 (by rfl) ⟨346403, by rfl⟩ : syracuseStep 461871 = 692807) B692807
theorem B691271 : Blo 459783 691271 := bstep (se 1 (by rfl) ⟨518453, by rfl⟩ : syracuseStep 691271 = 1036907) B1036907
theorem B461895 : Blo 459783 461895 := bstep (se 1 (by rfl) ⟨346421, by rfl⟩ : syracuseStep 461895 = 692843) B692843
theorem B462047 : Blo 459783 462047 := bstep (se 1 (by rfl) ⟨346535, by rfl⟩ : syracuseStep 462047 = 693071) B693071
theorem B658697 : Blo 459783 658697 := bstep (se 2 (by rfl) ⟨247011, by rfl⟩ : syracuseStep 658697 = 494023) B494023
theorem B5901619 : Blo 459783 5901619 := bstep (se 1 (by rfl) ⟨4426214, by rfl⟩ : syracuseStep 5901619 = 8852429) B8852429
theorem B691535 : Blo 459783 691535 := bstep (se 1 (by rfl) ⟨518651, by rfl⟩ : syracuseStep 691535 = 1037303) B1037303
theorem B691625 : Blo 459783 691625 := bstep (se 2 (by rfl) ⟨259359, by rfl⟩ : syracuseStep 691625 = 518719) B518719
theorem B2330045 : Blo 459783 2330045 := bstep (se 3 (by rfl) ⟨436883, by rfl⟩ : syracuseStep 2330045 = 873767) B873767
theorem B462311 : Blo 459783 462311 := bstep (se 1 (by rfl) ⟨346733, by rfl⟩ : syracuseStep 462311 = 693467) B693467
theorem B2657855 : Blo 459783 2657855 := bstep (se 1 (by rfl) ⟨1993391, by rfl⟩ : syracuseStep 2657855 = 3986783) B3986783
theorem B691775 : Blo 459783 691775 := bstep (se 1 (by rfl) ⟨518831, by rfl⟩ : syracuseStep 691775 = 1037663) B1037663
theorem B1314377 : Blo 459783 1314377 := bstep (se 2 (by rfl) ⟨492891, by rfl⟩ : syracuseStep 1314377 = 985783) B985783
theorem B462427 : Blo 459783 462427 := bstep (se 1 (by rfl) ⟨346820, by rfl⟩ : syracuseStep 462427 = 693641) B693641
theorem B659119 : Blo 459783 659119 := bstep (se 1 (by rfl) ⟨494339, by rfl⟩ : syracuseStep 659119 = 988679) B988679
theorem B692039 : Blo 459783 692039 := bstep (se 1 (by rfl) ⟨519029, by rfl⟩ : syracuseStep 692039 = 1038059) B1038059
theorem B462663 : Blo 459783 462663 := bstep (se 1 (by rfl) ⟨346997, by rfl⟩ : syracuseStep 462663 = 693995) B693995
theorem B692123 : Blo 459783 692123 := bstep (se 1 (by rfl) ⟨519092, by rfl⟩ : syracuseStep 692123 = 1038185) B1038185
theorem B462815 : Blo 459783 462815 := bstep (se 1 (by rfl) ⟨347111, by rfl⟩ : syracuseStep 462815 = 694223) B694223
theorem B42504209 : Blo 459783 42504209 := bstep (se 2 (by rfl) ⟨15939078, by rfl⟩ : syracuseStep 42504209 = 31878157) B31878157
theorem B463079 : Blo 459783 463079 := bstep (se 1 (by rfl) ⟨347309, by rfl⟩ : syracuseStep 463079 = 694619) B694619
theorem B463231 : Blo 459783 463231 := bstep (se 1 (by rfl) ⟨347423, by rfl⟩ : syracuseStep 463231 = 694847) B694847
theorem B692687 : Blo 459783 692687 := bstep (se 1 (by rfl) ⟨519515, by rfl⟩ : syracuseStep 692687 = 1039031) B1039031
theorem B463311 : Blo 459783 463311 := bstep (se 1 (by rfl) ⟨347483, by rfl⟩ : syracuseStep 463311 = 694967) B694967
theorem B692729 : Blo 459783 692729 := bstep (se 2 (by rfl) ⟨259773, by rfl⟩ : syracuseStep 692729 = 519547) B519547
theorem B7082497 : Blo 459783 7082497 := bstep (se 2 (by rfl) ⟨2655936, by rfl⟩ : syracuseStep 7082497 = 5311873) B5311873
theorem B3510863 : Blo 459783 3510863 := bstep (se 1 (by rfl) ⟨2633147, by rfl⟩ : syracuseStep 3510863 = 5266295) B5266295
theorem B692831 : Blo 459783 692831 := bstep (se 1 (by rfl) ⟨519623, by rfl⟩ : syracuseStep 692831 = 1039247) B1039247
theorem B463463 : Blo 459783 463463 := bstep (se 1 (by rfl) ⟨347597, by rfl⟩ : syracuseStep 463463 = 695195) B695195
theorem B791275 : Blo 459783 791275 := bstep (se 1 (by rfl) ⟨593456, by rfl⟩ : syracuseStep 791275 = 1186913) B1186913
theorem B463727 : Blo 459783 463727 := bstep (se 1 (by rfl) ⟨347795, by rfl⟩ : syracuseStep 463727 = 695591) B695591
theorem B1315709 : Blo 459783 1315709 := bstep (se 3 (by rfl) ⟨246695, by rfl⟩ : syracuseStep 1315709 = 493391) B493391
theorem B463783 : Blo 459783 463783 := bstep (se 1 (by rfl) ⟨347837, by rfl⟩ : syracuseStep 463783 = 695675) B695675
theorem B1315835 : Blo 459783 1315835 := bstep (se 1 (by rfl) ⟨986876, by rfl⟩ : syracuseStep 1315835 = 1973753) B1973753
theorem B693311 : Blo 459783 693311 := bstep (se 1 (by rfl) ⟨519983, by rfl⟩ : syracuseStep 693311 = 1039967) B1039967
theorem B693353 : Blo 459783 693353 := bstep (se 2 (by rfl) ⟨260007, by rfl⟩ : syracuseStep 693353 = 520015) B520015
theorem B1971307 : Blo 459783 1971307 := bstep (se 1 (by rfl) ⟨1478480, by rfl⟩ : syracuseStep 1971307 = 2956961) B2956961
theorem B5280875 : Blo 459783 5280875 := bstep (se 1 (by rfl) ⟨3960656, by rfl⟩ : syracuseStep 5280875 = 7921313) B7921313
theorem B693455 : Blo 459783 693455 := bstep (se 1 (by rfl) ⟨520091, by rfl⟩ : syracuseStep 693455 = 1040183) B1040183
theorem B2626769 : Blo 459783 2626769 := bstep (se 2 (by rfl) ⟨985038, by rfl⟩ : syracuseStep 2626769 = 1970077) B1970077
theorem B1316051 : Blo 459783 1316051 := bstep (se 1 (by rfl) ⟨987038, by rfl⟩ : syracuseStep 1316051 = 1974077) B1974077
theorem B693659 : Blo 459783 693659 := bstep (se 1 (by rfl) ⟨520244, by rfl⟩ : syracuseStep 693659 = 1040489) B1040489
theorem B693881 : Blo 459783 693881 := bstep (se 2 (by rfl) ⟨260205, by rfl⟩ : syracuseStep 693881 = 520411) B520411
theorem B693983 : Blo 459783 693983 := bstep (se 1 (by rfl) ⟨520487, by rfl⟩ : syracuseStep 693983 = 1040975) B1040975
theorem B1316665 : Blo 459783 1316665 := bstep (se 2 (by rfl) ⟨493749, by rfl⟩ : syracuseStep 1316665 = 987499) B987499
theorem B694079 : Blo 459783 694079 := bstep (se 1 (by rfl) ⟨520559, by rfl⟩ : syracuseStep 694079 = 1041119) B1041119
theorem B1185673 : Blo 459783 1185673 := bstep (se 2 (by rfl) ⟨444627, by rfl⟩ : syracuseStep 1185673 = 889255) B889255
theorem B3151799 : Blo 459783 3151799 := bstep (se 1 (by rfl) ⟨2363849, by rfl⟩ : syracuseStep 3151799 = 4727699) B4727699
theorem B694247 : Blo 459783 694247 := bstep (se 1 (by rfl) ⟨520685, by rfl⟩ : syracuseStep 694247 = 1041371) B1041371
theorem B694265 : Blo 459783 694265 := bstep (se 2 (by rfl) ⟨260349, by rfl⟩ : syracuseStep 694265 = 520699) B520699
theorem B694367 : Blo 459783 694367 := bstep (se 1 (by rfl) ⟨520775, by rfl⟩ : syracuseStep 694367 = 1041551) B1041551
theorem B1317019 : Blo 459783 1317019 := bstep (se 1 (by rfl) ⟨987764, by rfl⟩ : syracuseStep 1317019 = 1975529) B1975529
theorem B694427 : Blo 459783 694427 := bstep (se 1 (by rfl) ⟨520820, by rfl⟩ : syracuseStep 694427 = 1041641) B1041641
theorem B694463 : Blo 459783 694463 := bstep (se 1 (by rfl) ⟨520847, by rfl⟩ : syracuseStep 694463 = 1041695) B1041695
theorem B694505 : Blo 459783 694505 := bstep (se 2 (by rfl) ⟨260439, by rfl⟩ : syracuseStep 694505 = 520879) B520879
theorem B1055099 : Blo 459783 1055099 := bstep (se 1 (by rfl) ⟨791324, by rfl⟩ : syracuseStep 1055099 = 1582649) B1582649
theorem B694811 : Blo 459783 694811 := bstep (se 1 (by rfl) ⟨521108, by rfl⟩ : syracuseStep 694811 = 1042217) B1042217
theorem B694889 : Blo 459783 694889 := bstep (se 2 (by rfl) ⟨260583, by rfl⟩ : syracuseStep 694889 = 521167) B521167
theorem B695417 : Blo 459783 695417 := bstep (se 2 (by rfl) ⟨260781, by rfl⟩ : syracuseStep 695417 = 521563) B521563
theorem B695519 : Blo 459783 695519 := bstep (se 1 (by rfl) ⟨521639, by rfl⟩ : syracuseStep 695519 = 1043279) B1043279
theorem B695561 : Blo 459783 695561 := bstep (se 2 (by rfl) ⟨260835, by rfl⟩ : syracuseStep 695561 = 521671) B521671
theorem B695663 : Blo 459783 695663 := bstep (se 1 (by rfl) ⟨521747, by rfl⟩ : syracuseStep 695663 = 1043495) B1043495
theorem B3317125 : Blo 459783 3317125 := bstep (se 4 (by rfl) ⟨310980, by rfl⟩ : syracuseStep 3317125 = 621961) B621961
theorem B6757967 : Blo 459783 6757967 := bstep (se 1 (by rfl) ⟨5068475, by rfl⟩ : syracuseStep 6757967 = 10136951) B10136951
theorem B1318625 : Blo 459783 1318625 := bstep (se 2 (by rfl) ⟨494484, by rfl⟩ : syracuseStep 1318625 = 988969) B988969
theorem B2958191 : Blo 459783 2958191 := bstep (se 1 (by rfl) ⟨2218643, by rfl⟩ : syracuseStep 2958191 = 4437287) B4437287
theorem B1745819 : Blo 459783 1745819 := bstep (se 1 (by rfl) ⟨1309364, by rfl⟩ : syracuseStep 1745819 = 2618729) B2618729
theorem B2106491 : Blo 459783 2106491 := bstep (se 1 (by rfl) ⟨1579868, by rfl⟩ : syracuseStep 2106491 = 3159737) B3159737
theorem B501535 : Blo 459783 501535 := bstep (se 1 (by rfl) ⟨376151, by rfl⟩ : syracuseStep 501535 = 752303) B752303
theorem B5351453 : Blo 459783 5351453 := bstep (se 3 (by rfl) ⟨1003397, by rfl⟩ : syracuseStep 5351453 = 2006795) B2006795
theorem B2500733 : Blo 459783 2500733 := bstep (se 3 (by rfl) ⟨468887, by rfl⟩ : syracuseStep 2500733 = 937775) B937775
theorem B1681721 : Blo 459783 1681721 := bstep (se 2 (by rfl) ⟨630645, by rfl⟩ : syracuseStep 1681721 = 1261291) B1261291
theorem B1878599 : Blo 459783 1878599 := bstep (se 1 (by rfl) ⟨1408949, by rfl⟩ : syracuseStep 1878599 = 2817899) B2817899
theorem B699463 : Blo 459783 699463 := bstep (se 1 (by rfl) ⟨524597, by rfl⟩ : syracuseStep 699463 = 1049195) B1049195
theorem B2239721 : Blo 459783 2239721 := bstep (se 2 (by rfl) ⟨839895, by rfl⟩ : syracuseStep 2239721 = 1679791) B1679791
theorem B2960651 : Blo 459783 2960651 := bstep (se 1 (by rfl) ⟨2220488, by rfl⟩ : syracuseStep 2960651 = 4440977) B4440977
theorem B1748537 : Blo 459783 1748537 := bstep (se 2 (by rfl) ⟨655701, by rfl⟩ : syracuseStep 1748537 = 1311403) B1311403
theorem B3944051 : Blo 459783 3944051 := bstep (se 1 (by rfl) ⟨2958038, by rfl⟩ : syracuseStep 3944051 = 5916077) B5916077
theorem B831271 : Blo 459783 831271 := bstep (se 1 (by rfl) ⟨623453, by rfl⟩ : syracuseStep 831271 = 1246907) B1246907
theorem B1552283 : Blo 459783 1552283 := bstep (se 1 (by rfl) ⟨1164212, by rfl⟩ : syracuseStep 1552283 = 2328425) B2328425
theorem B5485391 : Blo 459783 5485391 := bstep (se 1 (by rfl) ⟨4114043, by rfl⟩ : syracuseStep 5485391 = 8228087) B8228087
theorem B1553417 : Blo 459783 1553417 := bstep (se 2 (by rfl) ⟨582531, by rfl⟩ : syracuseStep 1553417 = 1165063) B1165063
theorem B1553471 : Blo 459783 1553471 := bstep (se 1 (by rfl) ⟨1165103, by rfl⟩ : syracuseStep 1553471 = 2330207) B2330207
theorem B10663001 : Blo 459783 10663001 := bstep (se 2 (by rfl) ⟨3998625, by rfl⟩ : syracuseStep 10663001 = 7997251) B7997251
theorem B2340251 : Blo 459783 2340251 := bstep (se 1 (by rfl) ⟨1755188, by rfl⟩ : syracuseStep 2340251 = 3510377) B3510377
theorem B12006893 : Blo 459783 12006893 := bstep (se 3 (by rfl) ⟨2251292, by rfl⟩ : syracuseStep 12006893 = 4502585) B4502585
theorem B2799269 : Blo 459783 2799269 := bstep (se 4 (by rfl) ⟨262431, by rfl⟩ : syracuseStep 2799269 = 524863) B524863
theorem B2963627 : Blo 459783 2963627 := bstep (se 1 (by rfl) ⟨2222720, by rfl⟩ : syracuseStep 2963627 = 4445441) B4445441
theorem B834529 : Blo 459783 834529 := bstep (se 2 (by rfl) ⟨312948, by rfl⟩ : syracuseStep 834529 = 625897) B625897
theorem B1556279 : Blo 459783 1556279 := bstep (se 1 (by rfl) ⟨1167209, by rfl⟩ : syracuseStep 1556279 = 2334419) B2334419
theorem B1556711 : Blo 459783 1556711 := bstep (se 1 (by rfl) ⟨1167533, by rfl⟩ : syracuseStep 1556711 = 2335067) B2335067
theorem B5915105 : Blo 459783 5915105 := bstep (se 2 (by rfl) ⟨2218164, by rfl⟩ : syracuseStep 5915105 = 4436329) B4436329
theorem B1753595 : Blo 459783 1753595 := bstep (se 1 (by rfl) ⟨1315196, by rfl⟩ : syracuseStep 1753595 = 2630393) B2630393
theorem B2638433 : Blo 459783 2638433 := bstep (se 2 (by rfl) ⟨989412, by rfl⟩ : syracuseStep 2638433 = 1978825) B1978825
theorem B1164041 : Blo 459783 1164041 := bstep (se 2 (by rfl) ⟨436515, by rfl⟩ : syracuseStep 1164041 = 873031) B873031
theorem B1557305 : Blo 459783 1557305 := bstep (se 2 (by rfl) ⟨583989, by rfl⟩ : syracuseStep 1557305 = 1167979) B1167979
theorem B1557359 : Blo 459783 1557359 := bstep (se 1 (by rfl) ⟨1168019, by rfl⟩ : syracuseStep 1557359 = 2336039) B2336039
theorem B1164719 : Blo 459783 1164719 := bstep (se 1 (by rfl) ⟨873539, by rfl⟩ : syracuseStep 1164719 = 1747079) B1747079
theorem B1558169 : Blo 459783 1558169 := bstep (se 2 (by rfl) ⟨584313, by rfl⟩ : syracuseStep 1558169 = 1168627) B1168627
theorem B2377937 : Blo 459783 2377937 := bstep (se 2 (by rfl) ⟨891726, by rfl⟩ : syracuseStep 2377937 = 1783453) B1783453
theorem B1558763 : Blo 459783 1558763 := bstep (se 1 (by rfl) ⟨1169072, by rfl⟩ : syracuseStep 1558763 = 2338145) B2338145
theorem B1755371 : Blo 459783 1755371 := bstep (se 1 (by rfl) ⟨1316528, by rfl⟩ : syracuseStep 1755371 = 2633057) B2633057
theorem B3164507 : Blo 459783 3164507 := bstep (se 1 (by rfl) ⟨2373380, by rfl⟩ : syracuseStep 3164507 = 4746761) B4746761
theorem B1034657 : Blo 459783 1034657 := bstep (se 2 (by rfl) ⟨387996, by rfl⟩ : syracuseStep 1034657 = 775993) B775993
theorem B7489997 : Blo 459783 7489997 := bstep (se 3 (by rfl) ⟨1404374, by rfl⟩ : syracuseStep 7489997 = 2808749) B2808749
theorem B1034783 : Blo 459783 1034783 := bstep (se 1 (by rfl) ⟨776087, by rfl⟩ : syracuseStep 1034783 = 1552175) B1552175
theorem B2837207 : Blo 459783 2837207 := bstep (se 1 (by rfl) ⟨2127905, by rfl⟩ : syracuseStep 2837207 = 4255811) B4255811
theorem B2640599 : Blo 459783 2640599 := bstep (se 1 (by rfl) ⟨1980449, by rfl⟩ : syracuseStep 2640599 = 3960899) B3960899
theorem B2378591 : Blo 459783 2378591 := bstep (se 1 (by rfl) ⟨1783943, by rfl⟩ : syracuseStep 2378591 = 3567887) B3567887
theorem B47893355 : Blo 459783 47893355 := bstep (se 1 (by rfl) ⟨35920016, by rfl⟩ : syracuseStep 47893355 = 71840033) B71840033
theorem B8867191 : Blo 459783 8867191 := bstep (se 1 (by rfl) ⟨6650393, by rfl⟩ : syracuseStep 8867191 = 13300787) B13300787
theorem B1560059 : Blo 459783 1560059 := bstep (se 1 (by rfl) ⟨1170044, by rfl⟩ : syracuseStep 1560059 = 2340089) B2340089
theorem B5983807 : Blo 459783 5983807 := bstep (se 1 (by rfl) ⟨4487855, by rfl⟩ : syracuseStep 5983807 = 8975711) B8975711
theorem B1560221 : Blo 459783 1560221 := bstep (se 3 (by rfl) ⟨292541, by rfl⟩ : syracuseStep 1560221 = 585083) B585083
theorem B1756829 : Blo 459783 1756829 := bstep (se 3 (by rfl) ⟨329405, by rfl⟩ : syracuseStep 1756829 = 658811) B658811
theorem B2805443 : Blo 459783 2805443 := bstep (se 1 (by rfl) ⟨2104082, by rfl⟩ : syracuseStep 2805443 = 4208165) B4208165
theorem B12472211 : Blo 459783 12472211 := bstep (se 1 (by rfl) ⟨9354158, by rfl⟩ : syracuseStep 12472211 = 18708317) B18708317
theorem B1036187 : Blo 459783 1036187 := bstep (se 1 (by rfl) ⟨777140, by rfl⟩ : syracuseStep 1036187 = 1554281) B1554281
theorem B1560761 : Blo 459783 1560761 := bstep (se 2 (by rfl) ⟨585285, by rfl⟩ : syracuseStep 1560761 = 1170571) B1170571
theorem B1036475 : Blo 459783 1036475 := bstep (se 1 (by rfl) ⟨777356, by rfl⟩ : syracuseStep 1036475 = 1554713) B1554713
theorem B741881 : Blo 459783 741881 := bstep (se 2 (by rfl) ⟨278205, by rfl⟩ : syracuseStep 741881 = 556411) B556411
theorem B1659473 : Blo 459783 1659473 := bstep (se 2 (by rfl) ⟨622302, by rfl⟩ : syracuseStep 1659473 = 1244605) B1244605
theorem B1036961 : Blo 459783 1036961 := bstep (se 2 (by rfl) ⟨388860, by rfl⟩ : syracuseStep 1036961 = 777721) B777721
theorem B2970391 : Blo 459783 2970391 := bstep (se 1 (by rfl) ⟨2227793, by rfl⟩ : syracuseStep 2970391 = 4455587) B4455587
theorem B2806589 : Blo 459783 2806589 := bstep (se 3 (by rfl) ⟨526235, by rfl⟩ : syracuseStep 2806589 = 1052471) B1052471
theorem B1037321 : Blo 459783 1037321 := bstep (se 2 (by rfl) ⟨388995, by rfl⟩ : syracuseStep 1037321 = 777991) B777991
theorem B1037375 : Blo 459783 1037375 := bstep (se 1 (by rfl) ⟨778031, by rfl⟩ : syracuseStep 1037375 = 1556063) B1556063
theorem B776135 : Blo 459783 776135 := bstep (se 1 (by rfl) ⟨582101, by rfl⟩ : syracuseStep 776135 = 1164203) B1164203
theorem B1038311 : Blo 459783 1038311 := bstep (se 1 (by rfl) ⟨778733, by rfl⟩ : syracuseStep 1038311 = 1557467) B1557467
theorem B874489 : Blo 459783 874489 := bstep (se 2 (by rfl) ⟨327933, by rfl⟩ : syracuseStep 874489 = 655867) B655867
theorem B1038329 : Blo 459783 1038329 := bstep (se 2 (by rfl) ⟨389373, by rfl⟩ : syracuseStep 1038329 = 778747) B778747
theorem B1038419 : Blo 459783 1038419 := bstep (se 1 (by rfl) ⟨778814, by rfl⟩ : syracuseStep 1038419 = 1557629) B1557629
theorem B1038491 : Blo 459783 1038491 := bstep (se 1 (by rfl) ⟨778868, by rfl⟩ : syracuseStep 1038491 = 1557737) B1557737
theorem B776425 : Blo 459783 776425 := bstep (se 2 (by rfl) ⟨291159, by rfl⟩ : syracuseStep 776425 = 582319) B582319
theorem B1562867 : Blo 459783 1562867 := bstep (se 1 (by rfl) ⟨1172150, by rfl⟩ : syracuseStep 1562867 = 2344301) B2344301
theorem B1038599 : Blo 459783 1038599 := bstep (se 1 (by rfl) ⟨778949, by rfl⟩ : syracuseStep 1038599 = 1557899) B1557899
theorem B874793 : Blo 459783 874793 := bstep (se 2 (by rfl) ⟨328047, by rfl⟩ : syracuseStep 874793 = 656095) B656095
theorem B1562921 : Blo 459783 1562921 := bstep (se 2 (by rfl) ⟨586095, by rfl⟩ : syracuseStep 1562921 = 1172191) B1172191
theorem B1038905 : Blo 459783 1038905 := bstep (se 2 (by rfl) ⟨389589, by rfl⟩ : syracuseStep 1038905 = 779179) B779179
theorem B776891 : Blo 459783 776891 := bstep (se 1 (by rfl) ⟨582668, by rfl⟩ : syracuseStep 776891 = 1165337) B1165337
theorem B875423 : Blo 459783 875423 := bstep (se 1 (by rfl) ⟨656567, by rfl⟩ : syracuseStep 875423 = 1313135) B1313135
theorem B1760201 : Blo 459783 1760201 := bstep (se 2 (by rfl) ⟨660075, by rfl⟩ : syracuseStep 1760201 = 1320151) B1320151
theorem B1039625 : Blo 459783 1039625 := bstep (se 2 (by rfl) ⟨389859, by rfl⟩ : syracuseStep 1039625 = 779719) B779719
theorem B1171169 : Blo 459783 1171169 := bstep (se 2 (by rfl) ⟨439188, by rfl⟩ : syracuseStep 1171169 = 878377) B878377
theorem B1564487 : Blo 459783 1564487 := bstep (se 1 (by rfl) ⟨1173365, by rfl⟩ : syracuseStep 1564487 = 2346731) B2346731
theorem B2809723 : Blo 459783 2809723 := bstep (se 1 (by rfl) ⟨2107292, by rfl⟩ : syracuseStep 2809723 = 4214585) B4214585
theorem B1564541 : Blo 459783 1564541 := bstep (se 3 (by rfl) ⟨293351, by rfl⟩ : syracuseStep 1564541 = 586703) B586703
theorem B778207 : Blo 459783 778207 := bstep (se 1 (by rfl) ⟨583655, by rfl⟩ : syracuseStep 778207 = 1167311) B1167311
theorem B1400971 : Blo 459783 1400971 := bstep (se 1 (by rfl) ⟨1050728, by rfl⟩ : syracuseStep 1400971 = 2101457) B2101457
theorem B1564811 : Blo 459783 1564811 := bstep (se 1 (by rfl) ⟨1173608, by rfl⟩ : syracuseStep 1564811 = 2347217) B2347217
theorem B1040615 : Blo 459783 1040615 := bstep (se 1 (by rfl) ⟨780461, by rfl⟩ : syracuseStep 1040615 = 1560923) B1560923
theorem B1335739 : Blo 459783 1335739 := bstep (se 1 (by rfl) ⟨1001804, by rfl⟩ : syracuseStep 1335739 = 2003609) B2003609
theorem B1565135 : Blo 459783 1565135 := bstep (se 1 (by rfl) ⟨1173851, by rfl⟩ : syracuseStep 1565135 = 2347703) B2347703
theorem B778855 : Blo 459783 778855 := bstep (se 1 (by rfl) ⟨584141, by rfl⟩ : syracuseStep 778855 = 1168283) B1168283
theorem B2220797 : Blo 459783 2220797 := bstep (se 3 (by rfl) ⟨416399, by rfl⟩ : syracuseStep 2220797 = 832799) B832799
theorem B1663753 : Blo 459783 1663753 := bstep (se 2 (by rfl) ⟨623907, by rfl⟩ : syracuseStep 1663753 = 1247815) B1247815
theorem B779017 : Blo 459783 779017 := bstep (se 2 (by rfl) ⟨292131, by rfl⟩ : syracuseStep 779017 = 584263) B584263
theorem B877321 : Blo 459783 877321 := bstep (se 2 (by rfl) ⟨328995, by rfl⟩ : syracuseStep 877321 = 657991) B657991
theorem B1041209 : Blo 459783 1041209 := bstep (se 2 (by rfl) ⟨390453, by rfl⟩ : syracuseStep 1041209 = 780907) B780907
theorem B1041263 : Blo 459783 1041263 := bstep (se 1 (by rfl) ⟨780947, by rfl⟩ : syracuseStep 1041263 = 1561895) B1561895
theorem B40035221 : Blo 459783 40035221 := bstep (se 6 (by rfl) ⟨938325, by rfl⟩ : syracuseStep 40035221 = 1876651) B1876651
theorem B3957923 : Blo 459783 3957923 := bstep (se 1 (by rfl) ⟨2968442, by rfl⟩ : syracuseStep 3957923 = 5936885) B5936885
theorem B779611 : Blo 459783 779611 := bstep (se 1 (by rfl) ⟨584708, by rfl⟩ : syracuseStep 779611 = 1169417) B1169417
theorem B517531 : Blo 459783 517531 := bstep (se 1 (by rfl) ⟨388148, by rfl⟩ : syracuseStep 517531 = 776297) B776297
theorem B1041839 : Blo 459783 1041839 := bstep (se 1 (by rfl) ⟨781379, by rfl⟩ : syracuseStep 1041839 = 1562759) B1562759
theorem B1173113 : Blo 459783 1173113 := bstep (se 2 (by rfl) ⟨439917, by rfl⟩ : syracuseStep 1173113 = 879835) B879835
theorem B3729239 : Blo 459783 3729239 := bstep (se 1 (by rfl) ⟨2796929, by rfl⟩ : syracuseStep 3729239 = 5593859) B5593859
theorem B3991697 : Blo 459783 3991697 := bstep (se 2 (by rfl) ⟨1496886, by rfl⟩ : syracuseStep 3991697 = 2993773) B2993773
theorem B1042667 : Blo 459783 1042667 := bstep (se 1 (by rfl) ⟨782000, by rfl⟩ : syracuseStep 1042667 = 1564001) B1564001
theorem B780583 : Blo 459783 780583 := bstep (se 1 (by rfl) ⟨585437, by rfl⟩ : syracuseStep 780583 = 1170875) B1170875
theorem B518683 : Blo 459783 518683 := bstep (se 1 (by rfl) ⟨389012, by rfl⟩ : syracuseStep 518683 = 778025) B778025
theorem B6646475 : Blo 459783 6646475 := bstep (se 1 (by rfl) ⟨4984856, by rfl⟩ : syracuseStep 6646475 = 9969713) B9969713
theorem B9988919 : Blo 459783 9988919 := bstep (se 1 (by rfl) ⟨7491689, by rfl⟩ : syracuseStep 9988919 = 14983379) B14983379
theorem B8842283 : Blo 459783 8842283 := bstep (se 1 (by rfl) ⟨6631712, by rfl⟩ : syracuseStep 8842283 = 13263425) B13263425
theorem B6679691 : Blo 459783 6679691 := bstep (se 1 (by rfl) ⟨5009768, by rfl⟩ : syracuseStep 6679691 = 10019537) B10019537
theorem B781535 : Blo 459783 781535 := bstep (se 1 (by rfl) ⟨586151, by rfl⟩ : syracuseStep 781535 = 1172303) B1172303
theorem B3337483 : Blo 459783 3337483 := bstep (se 1 (by rfl) ⟨2503112, by rfl⟩ : syracuseStep 3337483 = 5006225) B5006225
theorem B4287853 : Blo 459783 4287853 := bstep (se 3 (by rfl) ⟨803972, by rfl⟩ : syracuseStep 4287853 = 1607945) B1607945
theorem B519655 : Blo 459783 519655 := bstep (se 1 (by rfl) ⟨389741, by rfl⟩ : syracuseStep 519655 = 779483) B779483
theorem B781967 : Blo 459783 781967 := bstep (se 1 (by rfl) ⟨586475, by rfl⟩ : syracuseStep 781967 = 1172951) B1172951
theorem B782203 : Blo 459783 782203 := bstep (se 1 (by rfl) ⟨586652, by rfl⟩ : syracuseStep 782203 = 1173305) B1173305
theorem B22409095 : Blo 459783 22409095 := bstep (se 1 (by rfl) ⟨16806821, by rfl⟩ : syracuseStep 22409095 = 33613643) B33613643
theorem B1896331 : Blo 459783 1896331 := bstep (se 1 (by rfl) ⟨1422248, by rfl⟩ : syracuseStep 1896331 = 2844497) B2844497
theorem B1109899 : Blo 459783 1109899 := bstep (se 1 (by rfl) ⟨832424, by rfl⟩ : syracuseStep 1109899 = 1664849) B1664849
theorem B520159 : Blo 459783 520159 := bstep (se 1 (by rfl) ⟨390119, by rfl⟩ : syracuseStep 520159 = 780239) B780239
theorem B586111 : Blo 459783 586111 := bstep (se 1 (by rfl) ⟨439583, by rfl⟩ : syracuseStep 586111 = 879167) B879167
theorem B520807 : Blo 459783 520807 := bstep (se 1 (by rfl) ⟨390605, by rfl⟩ : syracuseStep 520807 = 781211) B781211
theorem B2815175 : Blo 459783 2815175 := bstep (se 1 (by rfl) ⟨2111381, by rfl⟩ : syracuseStep 2815175 = 4222763) B4222763
theorem B26572049 : Blo 459783 26572049 := bstep (se 2 (by rfl) ⟨9964518, by rfl⟩ : syracuseStep 26572049 = 19929037) B19929037
theorem B1668539 : Blo 459783 1668539 := bstep (se 1 (by rfl) ⟨1251404, by rfl⟩ : syracuseStep 1668539 = 2502809) B2502809
theorem B19559981 : Blo 459783 19559981 := bstep (se 3 (by rfl) ⟨3667496, by rfl⟩ : syracuseStep 19559981 = 7334993) B7334993
theorem B1930823 : Blo 459783 1930823 := bstep (se 1 (by rfl) ⟨1448117, by rfl⟩ : syracuseStep 1930823 = 2896235) B2896235
theorem B3339959 : Blo 459783 3339959 := bstep (se 1 (by rfl) ⟨2504969, by rfl⟩ : syracuseStep 3339959 = 5009939) B5009939
theorem B1898579 : Blo 459783 1898579 := bstep (se 1 (by rfl) ⟨1423934, by rfl⟩ : syracuseStep 1898579 = 2847869) B2847869
theorem B1669319 : Blo 459783 1669319 := bstep (se 1 (by rfl) ⟨1251989, by rfl⟩ : syracuseStep 1669319 = 2503979) B2503979
theorem B3505031 : Blo 459783 3505031 := bstep (se 1 (by rfl) ⟨2628773, by rfl⟩ : syracuseStep 3505031 = 5257547) B5257547
theorem B556079 : Blo 459783 556079 := bstep (se 1 (by rfl) ⟨417059, by rfl⟩ : syracuseStep 556079 = 834119) B834119
theorem B556103 : Blo 459783 556103 := bstep (se 1 (by rfl) ⟨417077, by rfl⟩ : syracuseStep 556103 = 834155) B834155
theorem B1309945 : Blo 459783 1309945 := bstep (se 2 (by rfl) ⟨491229, by rfl⟩ : syracuseStep 1309945 = 982459) B982459
theorem B1244527 : Blo 459783 1244527 := bstep (se 1 (by rfl) ⟨933395, by rfl⟩ : syracuseStep 1244527 = 1866791) B1866791
theorem B1080911 : Blo 459783 1080911 := bstep (se 1 (by rfl) ⟨810683, by rfl⟩ : syracuseStep 1080911 = 1621367) B1621367
theorem B1867607 : Blo 459783 1867607 := bstep (se 1 (by rfl) ⟨1400705, by rfl⟩ : syracuseStep 1867607 = 2801411) B2801411
theorem B982955 : Blo 459783 982955 := bstep (se 1 (by rfl) ⟨737216, by rfl⟩ : syracuseStep 982955 = 1474433) B1474433
theorem B1867961 : Blo 459783 1867961 := bstep (se 2 (by rfl) ⟨700485, by rfl⟩ : syracuseStep 1867961 = 1400971) B1400971
theorem B459823 : Blo 459783 459823 := bstep (se 1 (by rfl) ⟨344867, by rfl⟩ : syracuseStep 459823 = 689735) B689735
theorem B57672769 : Blo 459783 57672769 := bstep (se 2 (by rfl) ⟨21627288, by rfl⟩ : syracuseStep 57672769 = 43254577) B43254577
theorem B459887 : Blo 459783 459887 := bstep (se 1 (by rfl) ⟨344915, by rfl⟩ : syracuseStep 459887 = 689831) B689831
theorem B459943 : Blo 459783 459943 := bstep (se 1 (by rfl) ⟨344957, by rfl⟩ : syracuseStep 459943 = 689915) B689915
theorem B459967 : Blo 459783 459967 := bstep (se 1 (by rfl) ⟨344975, by rfl⟩ : syracuseStep 459967 = 689951) B689951
theorem B459999 : Blo 459783 459999 := bstep (se 1 (by rfl) ⟨344999, by rfl⟩ : syracuseStep 459999 = 689999) B689999
theorem B984287 : Blo 459783 984287 := bstep (se 1 (by rfl) ⟨738215, by rfl⟩ : syracuseStep 984287 = 1476431) B1476431
theorem B787691 : Blo 459783 787691 := bstep (se 1 (by rfl) ⟨590768, by rfl⟩ : syracuseStep 787691 = 1181537) B1181537
theorem B460079 : Blo 459783 460079 := bstep (se 1 (by rfl) ⟨345059, by rfl⟩ : syracuseStep 460079 = 690119) B690119
theorem B656687 : Blo 459783 656687 := bstep (se 1 (by rfl) ⟨492515, by rfl⟩ : syracuseStep 656687 = 985031) B985031
theorem B2491823 : Blo 459783 2491823 := bstep (se 1 (by rfl) ⟨1868867, by rfl⟩ : syracuseStep 2491823 = 3737735) B3737735
theorem B460315 : Blo 459783 460315 := bstep (se 1 (by rfl) ⟨345236, by rfl⟩ : syracuseStep 460315 = 690473) B690473
theorem B460319 : Blo 459783 460319 := bstep (se 1 (by rfl) ⟨345239, by rfl⟩ : syracuseStep 460319 = 690479) B690479
theorem B689771 : Blo 459783 689771 := bstep (se 1 (by rfl) ⟨517328, by rfl⟩ : syracuseStep 689771 = 1034657) B1034657
theorem B689855 : Blo 459783 689855 := bstep (se 1 (by rfl) ⟨517391, by rfl⟩ : syracuseStep 689855 = 1034783) B1034783
theorem B460479 : Blo 459783 460479 := bstep (se 1 (by rfl) ⟨345359, by rfl⟩ : syracuseStep 460479 = 690719) B690719
theorem B690041 : Blo 459783 690041 := bstep (se 2 (by rfl) ⟨258765, by rfl⟩ : syracuseStep 690041 = 517531) B517531
theorem B460735 : Blo 459783 460735 := bstep (se 1 (by rfl) ⟨345551, by rfl⟩ : syracuseStep 460735 = 691103) B691103
theorem B460767 : Blo 459783 460767 := bstep (se 1 (by rfl) ⟨345575, by rfl⟩ : syracuseStep 460767 = 691151) B691151
theorem B1312793 : Blo 459783 1312793 := bstep (se 2 (by rfl) ⟨492297, by rfl⟩ : syracuseStep 1312793 = 984595) B984595
theorem B460827 : Blo 459783 460827 := bstep (se 1 (by rfl) ⟨345620, by rfl⟩ : syracuseStep 460827 = 691241) B691241
theorem B460831 : Blo 459783 460831 := bstep (se 1 (by rfl) ⟨345623, by rfl⟩ : syracuseStep 460831 = 691247) B691247
theorem B460847 : Blo 459783 460847 := bstep (se 1 (by rfl) ⟨345635, by rfl⟩ : syracuseStep 460847 = 691271) B691271
theorem B461023 : Blo 459783 461023 := bstep (se 1 (by rfl) ⟨345767, by rfl⟩ : syracuseStep 461023 = 691535) B691535
theorem B461083 : Blo 459783 461083 := bstep (se 1 (by rfl) ⟨345812, by rfl⟩ : syracuseStep 461083 = 691625) B691625
theorem B1771903 : Blo 459783 1771903 := bstep (se 1 (by rfl) ⟨1328927, by rfl⟩ : syracuseStep 1771903 = 2657855) B2657855
theorem B461183 : Blo 459783 461183 := bstep (se 1 (by rfl) ⟨345887, by rfl⟩ : syracuseStep 461183 = 691775) B691775
theorem B1870295 : Blo 459783 1870295 := bstep (se 1 (by rfl) ⟨1402721, by rfl⟩ : syracuseStep 1870295 = 2805443) B2805443
theorem B461359 : Blo 459783 461359 := bstep (se 1 (by rfl) ⟨346019, by rfl⟩ : syracuseStep 461359 = 692039) B692039
theorem B690791 : Blo 459783 690791 := bstep (se 1 (by rfl) ⟨518093, by rfl⟩ : syracuseStep 690791 = 1036187) B1036187
theorem B461415 : Blo 459783 461415 := bstep (se 1 (by rfl) ⟨346061, by rfl⟩ : syracuseStep 461415 = 692123) B692123
theorem B690983 : Blo 459783 690983 := bstep (se 1 (by rfl) ⟨518237, by rfl⟩ : syracuseStep 690983 = 1036475) B1036475
theorem B461791 : Blo 459783 461791 := bstep (se 1 (by rfl) ⟨346343, by rfl⟩ : syracuseStep 461791 = 692687) B692687
theorem B461819 : Blo 459783 461819 := bstep (se 1 (by rfl) ⟨346364, by rfl⟩ : syracuseStep 461819 = 692729) B692729
theorem B494587 : Blo 459783 494587 := bstep (se 1 (by rfl) ⟨370940, by rfl⟩ : syracuseStep 494587 = 741881) B741881
theorem B461887 : Blo 459783 461887 := bstep (se 1 (by rfl) ⟨346415, by rfl⟩ : syracuseStep 461887 = 692831) B692831
theorem B691307 : Blo 459783 691307 := bstep (se 1 (by rfl) ⟨518480, by rfl⟩ : syracuseStep 691307 = 1036961) B1036961
theorem B1871059 : Blo 459783 1871059 := bstep (se 1 (by rfl) ⟨1403294, by rfl⟩ : syracuseStep 1871059 = 2806589) B2806589
theorem B691547 : Blo 459783 691547 := bstep (se 1 (by rfl) ⟨518660, by rfl⟩ : syracuseStep 691547 = 1037321) B1037321
theorem B691577 : Blo 459783 691577 := bstep (se 2 (by rfl) ⟨259341, by rfl⟩ : syracuseStep 691577 = 518683) B518683
theorem B691583 : Blo 459783 691583 := bstep (se 1 (by rfl) ⟨518687, by rfl⟩ : syracuseStep 691583 = 1037375) B1037375
theorem B462207 : Blo 459783 462207 := bstep (se 1 (by rfl) ⟨346655, by rfl⟩ : syracuseStep 462207 = 693311) B693311
theorem B462235 : Blo 459783 462235 := bstep (se 1 (by rfl) ⟨346676, by rfl⟩ : syracuseStep 462235 = 693353) B693353
theorem B462303 : Blo 459783 462303 := bstep (se 1 (by rfl) ⟨346727, by rfl⟩ : syracuseStep 462303 = 693455) B693455
theorem B2624993 : Blo 459783 2624993 := bstep (se 2 (by rfl) ⟨984372, by rfl⟩ : syracuseStep 2624993 = 1968745) B1968745
theorem B462439 : Blo 459783 462439 := bstep (se 1 (by rfl) ⟨346829, by rfl⟩ : syracuseStep 462439 = 693659) B693659
theorem B462587 : Blo 459783 462587 := bstep (se 1 (by rfl) ⟨346940, by rfl⟩ : syracuseStep 462587 = 693881) B693881
theorem B462655 : Blo 459783 462655 := bstep (se 1 (by rfl) ⟨346991, by rfl⟩ : syracuseStep 462655 = 693983) B693983
theorem B462719 : Blo 459783 462719 := bstep (se 1 (by rfl) ⟨347039, by rfl⟩ : syracuseStep 462719 = 694079) B694079
theorem B2101199 : Blo 459783 2101199 := bstep (se 1 (by rfl) ⟨1575899, by rfl⟩ : syracuseStep 2101199 = 3151799) B3151799
theorem B692207 : Blo 459783 692207 := bstep (se 1 (by rfl) ⟨519155, by rfl⟩ : syracuseStep 692207 = 1038311) B1038311
theorem B462831 : Blo 459783 462831 := bstep (se 1 (by rfl) ⟨347123, by rfl⟩ : syracuseStep 462831 = 694247) B694247
theorem B692219 : Blo 459783 692219 := bstep (se 1 (by rfl) ⟨519164, by rfl⟩ : syracuseStep 692219 = 1038329) B1038329
theorem B462843 : Blo 459783 462843 := bstep (se 1 (by rfl) ⟨347132, by rfl⟩ : syracuseStep 462843 = 694265) B694265
theorem B692279 : Blo 459783 692279 := bstep (se 1 (by rfl) ⟨519209, by rfl⟩ : syracuseStep 692279 = 1038419) B1038419
theorem B462911 : Blo 459783 462911 := bstep (se 1 (by rfl) ⟨347183, by rfl⟩ : syracuseStep 462911 = 694367) B694367
theorem B692327 : Blo 459783 692327 := bstep (se 1 (by rfl) ⟨519245, by rfl⟩ : syracuseStep 692327 = 1038491) B1038491
theorem B462951 : Blo 459783 462951 := bstep (se 1 (by rfl) ⟨347213, by rfl⟩ : syracuseStep 462951 = 694427) B694427
theorem B462975 : Blo 459783 462975 := bstep (se 1 (by rfl) ⟨347231, by rfl⟩ : syracuseStep 462975 = 694463) B694463
theorem B463003 : Blo 459783 463003 := bstep (se 1 (by rfl) ⟨347252, by rfl⟩ : syracuseStep 463003 = 694505) B694505
theorem B692399 : Blo 459783 692399 := bstep (se 1 (by rfl) ⟨519299, by rfl⟩ : syracuseStep 692399 = 1038599) B1038599
theorem B463207 : Blo 459783 463207 := bstep (se 1 (by rfl) ⟨347405, by rfl⟩ : syracuseStep 463207 = 694811) B694811
theorem B692603 : Blo 459783 692603 := bstep (se 1 (by rfl) ⟨519452, by rfl⟩ : syracuseStep 692603 = 1038905) B1038905
theorem B7868825 : Blo 459783 7868825 := bstep (se 2 (by rfl) ⟨2950809, by rfl⟩ : syracuseStep 7868825 = 5901619) B5901619
theorem B463259 : Blo 459783 463259 := bstep (se 1 (by rfl) ⟨347444, by rfl⟩ : syracuseStep 463259 = 694889) B694889
theorem B692873 : Blo 459783 692873 := bstep (se 2 (by rfl) ⟨259827, by rfl⟩ : syracuseStep 692873 = 519655) B519655
theorem B463611 : Blo 459783 463611 := bstep (se 1 (by rfl) ⟨347708, by rfl⟩ : syracuseStep 463611 = 695417) B695417
theorem B463679 : Blo 459783 463679 := bstep (se 1 (by rfl) ⟨347759, by rfl⟩ : syracuseStep 463679 = 695519) B695519
theorem B693083 : Blo 459783 693083 := bstep (se 1 (by rfl) ⟨519812, by rfl⟩ : syracuseStep 693083 = 1039625) B1039625
theorem B463707 : Blo 459783 463707 := bstep (se 1 (by rfl) ⟨347780, by rfl⟩ : syracuseStep 463707 = 695561) B695561
theorem B463775 : Blo 459783 463775 := bstep (se 1 (by rfl) ⟨347831, by rfl⟩ : syracuseStep 463775 = 695663) B695663
theorem B2528441 : Blo 459783 2528441 := bstep (se 2 (by rfl) ⟨948165, by rfl⟩ : syracuseStep 2528441 = 1896331) B1896331
theorem B1479865 : Blo 459783 1479865 := bstep (se 2 (by rfl) ⟨554949, by rfl⟩ : syracuseStep 1479865 = 1109899) B1109899
theorem B693545 : Blo 459783 693545 := bstep (se 2 (by rfl) ⟨260079, by rfl⟩ : syracuseStep 693545 = 520159) B520159
theorem B693743 : Blo 459783 693743 := bstep (se 1 (by rfl) ⟨520307, by rfl⟩ : syracuseStep 693743 = 1040615) B1040615
theorem B1480531 : Blo 459783 1480531 := bstep (se 1 (by rfl) ⟨1110398, by rfl⟩ : syracuseStep 1480531 = 2220797) B2220797
theorem B694139 : Blo 459783 694139 := bstep (se 1 (by rfl) ⟨520604, by rfl⟩ : syracuseStep 694139 = 1041209) B1041209
theorem B1972127 : Blo 459783 1972127 := bstep (se 1 (by rfl) ⟨1479095, by rfl⟩ : syracuseStep 1972127 = 2958191) B2958191
theorem B694175 : Blo 459783 694175 := bstep (se 1 (by rfl) ⟨520631, by rfl⟩ : syracuseStep 694175 = 1041263) B1041263
theorem B694409 : Blo 459783 694409 := bstep (se 2 (by rfl) ⟨260403, by rfl⟩ : syracuseStep 694409 = 520807) B520807
theorem B694559 : Blo 459783 694559 := bstep (se 1 (by rfl) ⟨520919, by rfl⟩ : syracuseStep 694559 = 1041839) B1041839
theorem B1055033 : Blo 459783 1055033 := bstep (se 2 (by rfl) ⟨395637, by rfl⟩ : syracuseStep 1055033 = 791275) B791275
theorem B2661131 : Blo 459783 2661131 := bstep (se 1 (by rfl) ⟨1995848, by rfl⟩ : syracuseStep 2661131 = 3991697) B3991697
theorem B2628409 : Blo 459783 2628409 := bstep (se 2 (by rfl) ⟨985653, by rfl⟩ : syracuseStep 2628409 = 1971307) B1971307
theorem B695111 : Blo 459783 695111 := bstep (se 1 (by rfl) ⟨521333, by rfl⟩ : syracuseStep 695111 = 1042667) B1042667
theorem B1121147 : Blo 459783 1121147 := bstep (se 1 (by rfl) ⟨840860, by rfl⟩ : syracuseStep 1121147 = 1681721) B1681721
theorem B4430983 : Blo 459783 4430983 := bstep (se 1 (by rfl) ⟨3323237, by rfl⟩ : syracuseStep 4430983 = 6646475) B6646475
theorem B6659279 : Blo 459783 6659279 := bstep (se 1 (by rfl) ⟨4994459, by rfl⟩ : syracuseStep 6659279 = 9988919) B9988919
theorem B2629367 : Blo 459783 2629367 := bstep (se 1 (by rfl) ⟨1972025, by rfl⟩ : syracuseStep 2629367 = 3944051) B3944051
theorem B1580897 : Blo 459783 1580897 := bstep (se 2 (by rfl) ⟨592836, by rfl⟩ : syracuseStep 1580897 = 1185673) B1185673
theorem B1482877 : Blo 459783 1482877 := bstep (se 3 (by rfl) ⟨278039, by rfl⟩ : syracuseStep 1482877 = 556079) B556079
theorem B1482941 : Blo 459783 1482941 := bstep (se 3 (by rfl) ⟨278051, by rfl⟩ : syracuseStep 1482941 = 556103) B556103
theorem B1876783 : Blo 459783 1876783 := bstep (se 1 (by rfl) ⟨1407587, by rfl⟩ : syracuseStep 1876783 = 2815175) B2815175
theorem B8004595 : Blo 459783 8004595 := bstep (se 1 (by rfl) ⟨6003446, by rfl⟩ : syracuseStep 8004595 = 12006893) B12006893
theorem B1287215 : Blo 459783 1287215 := bstep (se 1 (by rfl) ⟨965411, by rfl⟩ : syracuseStep 1287215 = 1930823) B1930823
theorem B1975751 : Blo 459783 1975751 := bstep (se 1 (by rfl) ⟨1481813, by rfl⟩ : syracuseStep 1975751 = 2963627) B2963627
theorem B1746593 : Blo 459783 1746593 := bstep (se 2 (by rfl) ⟨654972, by rfl⟩ : syracuseStep 1746593 = 1309945) B1309945
theorem B2336687 : Blo 459783 2336687 := bstep (se 1 (by rfl) ⟨1752515, by rfl⟩ : syracuseStep 2336687 = 3505031) B3505031
theorem B3746297 : Blo 459783 3746297 := bstep (se 2 (by rfl) ⟨1404861, by rfl⟩ : syracuseStep 3746297 = 2809723) B2809723
theorem B3943403 : Blo 459783 3943403 := bstep (se 1 (by rfl) ⟨2957552, by rfl⟩ : syracuseStep 3943403 = 5915105) B5915105
theorem B6007931 : Blo 459783 6007931 := bstep (se 1 (by rfl) ⟨4505948, by rfl⟩ : syracuseStep 6007931 = 9011897) B9011897
theorem B1780985 : Blo 459783 1780985 := bstep (se 2 (by rfl) ⟨667869, by rfl⟩ : syracuseStep 1780985 = 1335739) B1335739
theorem B1748263 : Blo 459783 1748263 := bstep (se 1 (by rfl) ⟨1311197, by rfl⟩ : syracuseStep 1748263 = 2622395) B2622395
theorem B6335891 : Blo 459783 6335891 := bstep (se 1 (by rfl) ⟨4751918, by rfl⟩ : syracuseStep 6335891 = 9503837) B9503837
theorem B3911759 : Blo 459783 3911759 := bstep (se 1 (by rfl) ⟨2933819, by rfl⟩ : syracuseStep 3911759 = 5867639) B5867639
theorem B2338955 : Blo 459783 2338955 := bstep (se 1 (by rfl) ⟨1754216, by rfl⟩ : syracuseStep 2338955 = 3508433) B3508433
theorem B1585291 : Blo 459783 1585291 := bstep (se 1 (by rfl) ⟨1188968, by rfl⟩ : syracuseStep 1585291 = 2377937) B2377937
theorem B2109671 : Blo 459783 2109671 := bstep (se 1 (by rfl) ⟨1582253, by rfl⟩ : syracuseStep 2109671 = 3164507) B3164507
theorem B4993331 : Blo 459783 4993331 := bstep (se 1 (by rfl) ⟨3744998, by rfl⟩ : syracuseStep 4993331 = 7489997) B7489997
theorem B1552823 : Blo 459783 1552823 := bstep (se 1 (by rfl) ⟨1164617, by rfl⟩ : syracuseStep 1552823 = 2329235) B2329235
theorem B1585727 : Blo 459783 1585727 := bstep (se 1 (by rfl) ⟨1189295, by rfl⟩ : syracuseStep 1585727 = 2378591) B2378591
theorem B31928903 : Blo 459783 31928903 := bstep (se 1 (by rfl) ⟨23946677, by rfl⟩ : syracuseStep 31928903 = 47893355) B47893355
theorem B1553363 : Blo 459783 1553363 := bstep (se 1 (by rfl) ⟨1165022, by rfl⟩ : syracuseStep 1553363 = 2330045) B2330045
theorem B1750025 : Blo 459783 1750025 := bstep (se 2 (by rfl) ⟨656259, by rfl⟩ : syracuseStep 1750025 = 1312519) B1312519
theorem B5617309 : Blo 459783 5617309 := bstep (se 3 (by rfl) ⟨1053245, by rfl⟩ : syracuseStep 5617309 = 2106491) B2106491
theorem B2340575 : Blo 459783 2340575 := bstep (se 1 (by rfl) ⟨1755431, by rfl⟩ : syracuseStep 2340575 = 3510863) B3510863
theorem B3520583 : Blo 459783 3520583 := bstep (se 1 (by rfl) ⟨2640437, by rfl⟩ : syracuseStep 3520583 = 5280875) B5280875
theorem B1751179 : Blo 459783 1751179 := bstep (se 1 (by rfl) ⟨1313384, by rfl⟩ : syracuseStep 1751179 = 2626769) B2626769
theorem B1751453 : Blo 459783 1751453 := bstep (se 3 (by rfl) ⟨328397, by rfl⟩ : syracuseStep 1751453 = 656795) B656795
theorem B932617 : Blo 459783 932617 := bstep (se 2 (by rfl) ⟨349731, by rfl⟩ : syracuseStep 932617 = 699463) B699463
theorem B703399 : Blo 459783 703399 := bstep (se 1 (by rfl) ⟨527549, by rfl⟩ : syracuseStep 703399 = 1055099) B1055099
theorem B5717137 : Blo 459783 5717137 := bstep (se 2 (by rfl) ⟨2143926, by rfl⟩ : syracuseStep 5717137 = 4287853) B4287853
theorem B7978409 : Blo 459783 7978409 := bstep (se 2 (by rfl) ⟨2991903, by rfl⟩ : syracuseStep 7978409 = 5983807) B5983807
theorem B4505311 : Blo 459783 4505311 := bstep (se 1 (by rfl) ⟨3378983, by rfl⟩ : syracuseStep 4505311 = 6757967) B6757967
theorem B26690147 : Blo 459783 26690147 := bstep (se 1 (by rfl) ⟨20017610, by rfl⟩ : syracuseStep 26690147 = 40035221) B40035221
theorem B1163879 : Blo 459783 1163879 := bstep (se 1 (by rfl) ⟨872909, by rfl⟩ : syracuseStep 1163879 = 1745819) B1745819
theorem B2638615 : Blo 459783 2638615 := bstep (se 1 (by rfl) ⟨1978961, by rfl⟩ : syracuseStep 2638615 = 3957923) B3957923
theorem B6637477 : Blo 459783 6637477 := bstep (se 4 (by rfl) ⟨622263, by rfl⟩ : syracuseStep 6637477 = 1244527) B1244527
theorem B1493147 : Blo 459783 1493147 := bstep (se 1 (by rfl) ⟨1119860, by rfl⟩ : syracuseStep 1493147 = 2239721) B2239721
theorem B1165691 : Blo 459783 1165691 := bstep (se 1 (by rfl) ⟨874268, by rfl⟩ : syracuseStep 1165691 = 1748537) B1748537
theorem B1755553 : Blo 459783 1755553 := bstep (se 2 (by rfl) ⟨658332, by rfl⟩ : syracuseStep 1755553 = 1316665) B1316665
theorem B1034855 : Blo 459783 1034855 := bstep (se 1 (by rfl) ⟨776141, by rfl⟩ : syracuseStep 1034855 = 1552283) B1552283
theorem B1165985 : Blo 459783 1165985 := bstep (se 2 (by rfl) ⟨437244, by rfl⟩ : syracuseStep 1165985 = 874489) B874489
theorem B1756025 : Blo 459783 1756025 := bstep (se 2 (by rfl) ⟨658509, by rfl⟩ : syracuseStep 1756025 = 1317019) B1317019
theorem B1035233 : Blo 459783 1035233 := bstep (se 2 (by rfl) ⟨388212, by rfl⟩ : syracuseStep 1035233 = 776425) B776425
theorem B3656927 : Blo 459783 3656927 := bstep (se 1 (by rfl) ⟨2742695, by rfl⟩ : syracuseStep 3656927 = 5485391) B5485391
theorem B1035611 : Blo 459783 1035611 := bstep (se 1 (by rfl) ⟨776708, by rfl⟩ : syracuseStep 1035611 = 1553417) B1553417
theorem B1756525 : Blo 459783 1756525 := bstep (se 3 (by rfl) ⟨329348, by rfl⟩ : syracuseStep 1756525 = 658697) B658697
theorem B1035647 : Blo 459783 1035647 := bstep (se 1 (by rfl) ⟨776735, by rfl⟩ : syracuseStep 1035647 = 1553471) B1553471
theorem B17714699 : Blo 459783 17714699 := bstep (se 1 (by rfl) ⟨13286024, by rfl⟩ : syracuseStep 17714699 = 26572049) B26572049
theorem B1560167 : Blo 459783 1560167 := bstep (se 1 (by rfl) ⟨1170125, by rfl⟩ : syracuseStep 1560167 = 2340251) B2340251
theorem B1265719 : Blo 459783 1265719 := bstep (se 1 (by rfl) ⟨949289, by rfl⟩ : syracuseStep 1265719 = 1898579) B1898579
theorem B2674853 : Blo 459783 2674853 := bstep (se 4 (by rfl) ⟨250767, by rfl⟩ : syracuseStep 2674853 = 501535) B501535
theorem B1037519 : Blo 459783 1037519 := bstep (se 1 (by rfl) ⟨778139, by rfl⟩ : syracuseStep 1037519 = 1556279) B1556279
theorem B1037609 : Blo 459783 1037609 := bstep (se 2 (by rfl) ⟨389103, by rfl⟩ : syracuseStep 1037609 = 778207) B778207
theorem B1037807 : Blo 459783 1037807 := bstep (se 1 (by rfl) ⟨778355, by rfl⟩ : syracuseStep 1037807 = 1556711) B1556711
theorem B1169063 : Blo 459783 1169063 := bstep (se 1 (by rfl) ⟨876797, by rfl⟩ : syracuseStep 1169063 = 1753595) B1753595
theorem B1758955 : Blo 459783 1758955 := bstep (se 1 (by rfl) ⟨1319216, by rfl⟩ : syracuseStep 1758955 = 2638433) B2638433
theorem B776027 : Blo 459783 776027 := bstep (se 1 (by rfl) ⟨582020, by rfl⟩ : syracuseStep 776027 = 1164041) B1164041
theorem B1038203 : Blo 459783 1038203 := bstep (se 1 (by rfl) ⟨778652, by rfl⟩ : syracuseStep 1038203 = 1557305) B1557305
theorem B1038239 : Blo 459783 1038239 := bstep (se 1 (by rfl) ⟨778679, by rfl⟩ : syracuseStep 1038239 = 1557359) B1557359
theorem B874633 : Blo 459783 874633 := bstep (se 2 (by rfl) ⟨327987, by rfl⟩ : syracuseStep 874633 = 655975) B655975
theorem B1038473 : Blo 459783 1038473 := bstep (se 2 (by rfl) ⟨389427, by rfl⟩ : syracuseStep 1038473 = 778855) B778855
theorem B776479 : Blo 459783 776479 := bstep (se 1 (by rfl) ⟨582359, by rfl⟩ : syracuseStep 776479 = 1164719) B1164719
theorem B5921099 : Blo 459783 5921099 := bstep (se 1 (by rfl) ⟨4440824, by rfl⟩ : syracuseStep 5921099 = 8881649) B8881649
theorem B2218337 : Blo 459783 2218337 := bstep (se 2 (by rfl) ⟨831876, by rfl⟩ : syracuseStep 2218337 = 1663753) B1663753
theorem B1038689 : Blo 459783 1038689 := bstep (se 2 (by rfl) ⟨389508, by rfl⟩ : syracuseStep 1038689 = 779017) B779017
theorem B1169761 : Blo 459783 1169761 := bstep (se 2 (by rfl) ⟨438660, by rfl⟩ : syracuseStep 1169761 = 877321) B877321
theorem B1038779 : Blo 459783 1038779 := bstep (se 1 (by rfl) ⟨779084, by rfl⟩ : syracuseStep 1038779 = 1558169) B1558169
theorem B6773345 : Blo 459783 6773345 := bstep (se 2 (by rfl) ⟨2540004, by rfl⟩ : syracuseStep 6773345 = 5080009) B5080009
theorem B75979457 : Blo 459783 75979457 := bstep (se 2 (by rfl) ⟨28492296, by rfl⟩ : syracuseStep 75979457 = 56984593) B56984593
theorem B1039175 : Blo 459783 1039175 := bstep (se 1 (by rfl) ⟨779381, by rfl⟩ : syracuseStep 1039175 = 1558763) B1558763
theorem B1170247 : Blo 459783 1170247 := bstep (se 1 (by rfl) ⟨877685, by rfl⟩ : syracuseStep 1170247 = 1755371) B1755371
theorem B1039481 : Blo 459783 1039481 := bstep (se 2 (by rfl) ⟨389805, by rfl⟩ : syracuseStep 1039481 = 779611) B779611
theorem B1760399 : Blo 459783 1760399 := bstep (se 1 (by rfl) ⟨1320299, by rfl⟩ : syracuseStep 1760399 = 2640599) B2640599
theorem B1040039 : Blo 459783 1040039 := bstep (se 1 (by rfl) ⟨780029, by rfl⟩ : syracuseStep 1040039 = 1560059) B1560059
theorem B876251 : Blo 459783 876251 := bstep (se 1 (by rfl) ⟨657188, by rfl⟩ : syracuseStep 876251 = 1314377) B1314377
theorem B1040147 : Blo 459783 1040147 := bstep (se 1 (by rfl) ⟨780110, by rfl⟩ : syracuseStep 1040147 = 1560221) B1560221
theorem B1171219 : Blo 459783 1171219 := bstep (se 1 (by rfl) ⟨878414, by rfl⟩ : syracuseStep 1171219 = 1756829) B1756829
theorem B8314807 : Blo 459783 8314807 := bstep (se 1 (by rfl) ⟨6236105, by rfl⟩ : syracuseStep 8314807 = 12472211) B12472211
theorem B37773317 : Blo 459783 37773317 := bstep (se 4 (by rfl) ⟨3541248, by rfl⟩ : syracuseStep 37773317 = 7082497) B7082497
theorem B28336139 : Blo 459783 28336139 := bstep (se 1 (by rfl) ⟨21252104, by rfl⟩ : syracuseStep 28336139 = 42504209) B42504209
theorem B1040507 : Blo 459783 1040507 := bstep (se 1 (by rfl) ⟨780380, by rfl⟩ : syracuseStep 1040507 = 1560761) B1560761
theorem B1040777 : Blo 459783 1040777 := bstep (se 2 (by rfl) ⟨390291, by rfl⟩ : syracuseStep 1040777 = 780583) B780583
theorem B1106315 : Blo 459783 1106315 := bstep (se 1 (by rfl) ⟨829736, by rfl⟩ : syracuseStep 1106315 = 1659473) B1659473
theorem B877139 : Blo 459783 877139 := bstep (se 1 (by rfl) ⟨657854, by rfl⟩ : syracuseStep 877139 = 1315709) B1315709
theorem B877223 : Blo 459783 877223 := bstep (se 1 (by rfl) ⟨657917, by rfl⟩ : syracuseStep 877223 = 1315835) B1315835
theorem B877367 : Blo 459783 877367 := bstep (se 1 (by rfl) ⟨658025, by rfl⟩ : syracuseStep 877367 = 1316051) B1316051
theorem B4449437 : Blo 459783 4449437 := bstep (se 3 (by rfl) ⟨834269, by rfl⟩ : syracuseStep 4449437 = 1668539) B1668539
theorem B517423 : Blo 459783 517423 := bstep (se 1 (by rfl) ⟨388067, by rfl⟩ : syracuseStep 517423 = 776135) B776135
theorem B52159949 : Blo 459783 52159949 := bstep (se 3 (by rfl) ⟨9779990, by rfl⟩ : syracuseStep 52159949 = 19559981) B19559981
theorem B1041911 : Blo 459783 1041911 := bstep (se 1 (by rfl) ⟨781433, by rfl⟩ : syracuseStep 1041911 = 1562867) B1562867
theorem B583195 : Blo 459783 583195 := bstep (se 1 (by rfl) ⟨437396, by rfl⟩ : syracuseStep 583195 = 874793) B874793
theorem B1041947 : Blo 459783 1041947 := bstep (se 1 (by rfl) ⟨781460, by rfl⟩ : syracuseStep 1041947 = 1562921) B1562921
theorem B4449977 : Blo 459783 4449977 := bstep (se 2 (by rfl) ⟨1668741, by rfl⟩ : syracuseStep 4449977 = 3337483) B3337483
theorem B517927 : Blo 459783 517927 := bstep (se 1 (by rfl) ⟨388445, by rfl⟩ : syracuseStep 517927 = 776891) B776891
theorem B8906557 : Blo 459783 8906557 := bstep (se 3 (by rfl) ⟨1669979, by rfl⟩ : syracuseStep 8906557 = 3339959) B3339959
theorem B11822921 : Blo 459783 11822921 := bstep (se 2 (by rfl) ⟨4433595, by rfl⟩ : syracuseStep 11822921 = 8867191) B8867191
theorem B583615 : Blo 459783 583615 := bstep (se 1 (by rfl) ⟨437711, by rfl⟩ : syracuseStep 583615 = 875423) B875423
theorem B1173467 : Blo 459783 1173467 := bstep (se 1 (by rfl) ⟨880100, by rfl⟩ : syracuseStep 1173467 = 1760201) B1760201
theorem B878825 : Blo 459783 878825 := bstep (se 2 (by rfl) ⟨329559, by rfl⟩ : syracuseStep 878825 = 659119) B659119
theorem B1108361 : Blo 459783 1108361 := bstep (se 2 (by rfl) ⟨415635, by rfl⟩ : syracuseStep 1108361 = 831271) B831271
theorem B780779 : Blo 459783 780779 := bstep (se 1 (by rfl) ⟨585584, by rfl⟩ : syracuseStep 780779 = 1171169) B1171169
theorem B879083 : Blo 459783 879083 := bstep (se 1 (by rfl) ⟨659312, by rfl⟩ : syracuseStep 879083 = 1318625) B1318625
theorem B1042937 : Blo 459783 1042937 := bstep (se 2 (by rfl) ⟨391101, by rfl⟩ : syracuseStep 1042937 = 782203) B782203
theorem B29878793 : Blo 459783 29878793 := bstep (se 2 (by rfl) ⟨11204547, by rfl⟩ : syracuseStep 29878793 = 22409095) B22409095
theorem B1042991 : Blo 459783 1042991 := bstep (se 1 (by rfl) ⟨782243, by rfl⟩ : syracuseStep 1042991 = 1564487) B1564487
theorem B1043027 : Blo 459783 1043027 := bstep (se 1 (by rfl) ⟨782270, by rfl⟩ : syracuseStep 1043027 = 1564541) B1564541
theorem B1043207 : Blo 459783 1043207 := bstep (se 1 (by rfl) ⟨782405, by rfl⟩ : syracuseStep 1043207 = 1564811) B1564811
theorem B1043423 : Blo 459783 1043423 := bstep (se 1 (by rfl) ⟨782567, by rfl⟩ : syracuseStep 1043423 = 1565135) B1565135
theorem B781481 : Blo 459783 781481 := bstep (se 2 (by rfl) ⟨293055, by rfl⟩ : syracuseStep 781481 = 586111) B586111
theorem B3960521 : Blo 459783 3960521 := bstep (se 2 (by rfl) ⟨1485195, by rfl⟩ : syracuseStep 3960521 = 2970391) B2970391
theorem B782075 : Blo 459783 782075 := bstep (se 1 (by rfl) ⟨586556, by rfl⟩ : syracuseStep 782075 = 1173113) B1173113
theorem B2486159 : Blo 459783 2486159 := bstep (se 1 (by rfl) ⟨1864619, by rfl⟩ : syracuseStep 2486159 = 3729239) B3729239
theorem B3567635 : Blo 459783 3567635 := bstep (se 1 (by rfl) ⟨2675726, by rfl⟩ : syracuseStep 3567635 = 5351453) B5351453
theorem B1667155 : Blo 459783 1667155 := bstep (se 1 (by rfl) ⟨1250366, by rfl⟩ : syracuseStep 1667155 = 2500733) B2500733
theorem B5009597 : Blo 459783 5009597 := bstep (se 3 (by rfl) ⟨939299, by rfl⟩ : syracuseStep 5009597 = 1878599) B1878599
theorem B7565885 : Blo 459783 7565885 := bstep (se 3 (by rfl) ⟨1418603, by rfl⟩ : syracuseStep 7565885 = 2837207) B2837207
theorem B5894855 : Blo 459783 5894855 := bstep (se 1 (by rfl) ⟨4421141, by rfl⟩ : syracuseStep 5894855 = 8842283) B8842283
theorem B4453127 : Blo 459783 4453127 := bstep (se 1 (by rfl) ⟨3339845, by rfl⟩ : syracuseStep 4453127 = 6679691) B6679691
theorem B521023 : Blo 459783 521023 := bstep (se 1 (by rfl) ⟨390767, by rfl⟩ : syracuseStep 521023 = 781535) B781535
theorem B521311 : Blo 459783 521311 := bstep (se 1 (by rfl) ⟨390983, by rfl⟩ : syracuseStep 521311 = 781967) B781967
theorem B7895069 : Blo 459783 7895069 := bstep (se 3 (by rfl) ⟨1480325, by rfl⟩ : syracuseStep 7895069 = 2960651) B2960651
theorem B7108667 : Blo 459783 7108667 := bstep (se 1 (by rfl) ⟨5331500, by rfl⟩ : syracuseStep 7108667 = 10663001) B10663001
theorem B1866179 : Blo 459783 1866179 := bstep (se 1 (by rfl) ⟨1399634, by rfl⟩ : syracuseStep 1866179 = 2799269) B2799269
theorem B1112705 : Blo 459783 1112705 := bstep (se 2 (by rfl) ⟨417264, by rfl⟩ : syracuseStep 1112705 = 834529) B834529
theorem B1112879 : Blo 459783 1112879 := bstep (se 1 (by rfl) ⟨834659, by rfl⟩ : syracuseStep 1112879 = 1669319) B1669319
theorem B2882429 : Blo 459783 2882429 := bstep (se 3 (by rfl) ⟨540455, by rfl⟩ : syracuseStep 2882429 = 1080911) B1080911
theorem B4422833 : Blo 459783 4422833 := bstep (se 2 (by rfl) ⟨1658562, by rfl⟩ : syracuseStep 4422833 = 3317125) B3317125
theorem B1245071 : Blo 459783 1245071 := bstep (se 1 (by rfl) ⟨933803, by rfl⟩ : syracuseStep 1245071 = 1867607) B1867607
theorem B655303 : Blo 459783 655303 := bstep (se 1 (by rfl) ⟨491477, by rfl⟩ : syracuseStep 655303 = 982955) B982955
theorem B1245307 : Blo 459783 1245307 := bstep (se 1 (by rfl) ⟨933980, by rfl⟩ : syracuseStep 1245307 = 1867961) B1867961
theorem B17793431 : Blo 459783 17793431 := bstep (se 1 (by rfl) ⟨13345073, by rfl⟩ : syracuseStep 17793431 = 26690147) B26690147
theorem B656191 : Blo 459783 656191 := bstep (se 1 (by rfl) ⟨492143, by rfl⟩ : syracuseStep 656191 = 984287) B984287
theorem B525127 : Blo 459783 525127 := bstep (se 1 (by rfl) ⟨393845, by rfl⟩ : syracuseStep 525127 = 787691) B787691
theorem B459847 : Blo 459783 459847 := bstep (se 1 (by rfl) ⟨344885, by rfl⟩ : syracuseStep 459847 = 689771) B689771
theorem B459903 : Blo 459783 459903 := bstep (se 1 (by rfl) ⟨344927, by rfl⟩ : syracuseStep 459903 = 689855) B689855
theorem B460027 : Blo 459783 460027 := bstep (se 1 (by rfl) ⟨345020, by rfl⟩ : syracuseStep 460027 = 690041) B690041
theorem B689897 : Blo 459783 689897 := bstep (se 2 (by rfl) ⟨258711, by rfl⟩ : syracuseStep 689897 = 517423) B517423
theorem B689903 : Blo 459783 689903 := bstep (se 1 (by rfl) ⟨517427, by rfl⟩ : syracuseStep 689903 = 1034855) B1034855
theorem B460527 : Blo 459783 460527 := bstep (se 1 (by rfl) ⟨345395, by rfl⟩ : syracuseStep 460527 = 690791) B690791
theorem B460655 : Blo 459783 460655 := bstep (se 1 (by rfl) ⟨345491, by rfl⟩ : syracuseStep 460655 = 690983) B690983
theorem B690155 : Blo 459783 690155 := bstep (se 1 (by rfl) ⟨517616, by rfl⟩ : syracuseStep 690155 = 1035233) B1035233
theorem B460871 : Blo 459783 460871 := bstep (se 1 (by rfl) ⟨345653, by rfl⟩ : syracuseStep 460871 = 691307) B691307
theorem B690407 : Blo 459783 690407 := bstep (se 1 (by rfl) ⟨517805, by rfl⟩ : syracuseStep 690407 = 1035611) B1035611
theorem B461031 : Blo 459783 461031 := bstep (se 1 (by rfl) ⟨345773, by rfl⟩ : syracuseStep 461031 = 691547) B691547
theorem B461051 : Blo 459783 461051 := bstep (se 1 (by rfl) ⟨345788, by rfl⟩ : syracuseStep 461051 = 691577) B691577
theorem B690431 : Blo 459783 690431 := bstep (se 1 (by rfl) ⟨517823, by rfl⟩ : syracuseStep 690431 = 1035647) B1035647
theorem B461055 : Blo 459783 461055 := bstep (se 1 (by rfl) ⟨345791, by rfl⟩ : syracuseStep 461055 = 691583) B691583
theorem B690569 : Blo 459783 690569 := bstep (se 2 (by rfl) ⟨258963, by rfl⟩ : syracuseStep 690569 = 517927) B517927
theorem B8849969 : Blo 459783 8849969 := bstep (se 2 (by rfl) ⟨3318738, by rfl⟩ : syracuseStep 8849969 = 6637477) B6637477
theorem B461471 : Blo 459783 461471 := bstep (se 1 (by rfl) ⟨346103, by rfl⟩ : syracuseStep 461471 = 692207) B692207
theorem B461479 : Blo 459783 461479 := bstep (se 1 (by rfl) ⟨346109, by rfl⟩ : syracuseStep 461479 = 692219) B692219
theorem B461519 : Blo 459783 461519 := bstep (se 1 (by rfl) ⟨346139, by rfl⟩ : syracuseStep 461519 = 692279) B692279
theorem B461551 : Blo 459783 461551 := bstep (se 1 (by rfl) ⟨346163, by rfl⟩ : syracuseStep 461551 = 692327) B692327
theorem B461599 : Blo 459783 461599 := bstep (se 1 (by rfl) ⟨346199, by rfl⟩ : syracuseStep 461599 = 692399) B692399
theorem B461735 : Blo 459783 461735 := bstep (se 1 (by rfl) ⟨346301, by rfl⟩ : syracuseStep 461735 = 692603) B692603
theorem B5245883 : Blo 459783 5245883 := bstep (se 1 (by rfl) ⟨3934412, by rfl⟩ : syracuseStep 5245883 = 7868825) B7868825
theorem B461915 : Blo 459783 461915 := bstep (se 1 (by rfl) ⟨346436, by rfl⟩ : syracuseStep 461915 = 692873) B692873
theorem B2362537 : Blo 459783 2362537 := bstep (se 2 (by rfl) ⟨885951, by rfl⟩ : syracuseStep 2362537 = 1771903) B1771903
theorem B462055 : Blo 459783 462055 := bstep (se 1 (by rfl) ⟨346541, by rfl⟩ : syracuseStep 462055 = 693083) B693083
theorem B691679 : Blo 459783 691679 := bstep (se 1 (by rfl) ⟨518759, by rfl⟩ : syracuseStep 691679 = 1037519) B1037519
theorem B691739 : Blo 459783 691739 := bstep (se 1 (by rfl) ⟨518804, by rfl⟩ : syracuseStep 691739 = 1037609) B1037609
theorem B462363 : Blo 459783 462363 := bstep (se 1 (by rfl) ⟨346772, by rfl⟩ : syracuseStep 462363 = 693545) B693545
theorem B691871 : Blo 459783 691871 := bstep (se 1 (by rfl) ⟨518903, by rfl⟩ : syracuseStep 691871 = 1037807) B1037807
theorem B462495 : Blo 459783 462495 := bstep (se 1 (by rfl) ⟨346871, by rfl⟩ : syracuseStep 462495 = 693743) B693743
theorem B692135 : Blo 459783 692135 := bstep (se 1 (by rfl) ⟨519101, by rfl⟩ : syracuseStep 692135 = 1038203) B1038203
theorem B462759 : Blo 459783 462759 := bstep (se 1 (by rfl) ⟨347069, by rfl⟩ : syracuseStep 462759 = 694139) B694139
theorem B692159 : Blo 459783 692159 := bstep (se 1 (by rfl) ⟨519119, by rfl⟩ : syracuseStep 692159 = 1038239) B1038239
theorem B462783 : Blo 459783 462783 := bstep (se 1 (by rfl) ⟨347087, by rfl⟩ : syracuseStep 462783 = 694175) B694175
theorem B659449 : Blo 459783 659449 := bstep (se 2 (by rfl) ⟨247293, by rfl⟩ : syracuseStep 659449 = 494587) B494587
theorem B692315 : Blo 459783 692315 := bstep (se 1 (by rfl) ⟨519236, by rfl⟩ : syracuseStep 692315 = 1038473) B1038473
theorem B462939 : Blo 459783 462939 := bstep (se 1 (by rfl) ⟨347204, by rfl⟩ : syracuseStep 462939 = 694409) B694409
theorem B463039 : Blo 459783 463039 := bstep (se 1 (by rfl) ⟨347279, by rfl⟩ : syracuseStep 463039 = 694559) B694559
theorem B1478891 : Blo 459783 1478891 := bstep (se 1 (by rfl) ⟨1109168, by rfl⟩ : syracuseStep 1478891 = 2218337) B2218337
theorem B692459 : Blo 459783 692459 := bstep (se 1 (by rfl) ⟨519344, by rfl⟩ : syracuseStep 692459 = 1038689) B1038689
theorem B2494745 : Blo 459783 2494745 := bstep (se 2 (by rfl) ⟨935529, by rfl⟩ : syracuseStep 2494745 = 1871059) B1871059
theorem B692519 : Blo 459783 692519 := bstep (se 1 (by rfl) ⟨519389, by rfl⟩ : syracuseStep 692519 = 1038779) B1038779
theorem B2331017 : Blo 459783 2331017 := bstep (se 2 (by rfl) ⟨874131, by rfl⟩ : syracuseStep 2331017 = 1748263) B1748263
theorem B692783 : Blo 459783 692783 := bstep (se 1 (by rfl) ⟨519587, by rfl⟩ : syracuseStep 692783 = 1039175) B1039175
theorem B463407 : Blo 459783 463407 := bstep (se 1 (by rfl) ⟨347555, by rfl⟩ : syracuseStep 463407 = 695111) B695111
theorem B692987 : Blo 459783 692987 := bstep (se 1 (by rfl) ⟨519740, by rfl⟩ : syracuseStep 692987 = 1039481) B1039481
theorem B693359 : Blo 459783 693359 := bstep (se 1 (by rfl) ⟨520019, by rfl⟩ : syracuseStep 693359 = 1040039) B1040039
theorem B693431 : Blo 459783 693431 := bstep (se 1 (by rfl) ⟨520073, by rfl⟩ : syracuseStep 693431 = 1040147) B1040147
theorem B1053931 : Blo 459783 1053931 := bstep (se 1 (by rfl) ⟨790448, by rfl⟩ : syracuseStep 1053931 = 1580897) B1580897
theorem B693671 : Blo 459783 693671 := bstep (se 1 (by rfl) ⟨520253, by rfl⟩ : syracuseStep 693671 = 1040507) B1040507
theorem B988627 : Blo 459783 988627 := bstep (se 1 (by rfl) ⟨741470, by rfl⟩ : syracuseStep 988627 = 1482941) B1482941
theorem B693851 : Blo 459783 693851 := bstep (se 1 (by rfl) ⟨520388, by rfl⟩ : syracuseStep 693851 = 1040777) B1040777
theorem B858143 : Blo 459783 858143 := bstep (se 1 (by rfl) ⟨643607, by rfl⟩ : syracuseStep 858143 = 1287215) B1287215
theorem B1317167 : Blo 459783 1317167 := bstep (se 1 (by rfl) ⟨987875, by rfl⟩ : syracuseStep 1317167 = 1975751) B1975751
theorem B34773299 : Blo 459783 34773299 := bstep (se 1 (by rfl) ⟨26079974, by rfl⟩ : syracuseStep 34773299 = 52159949) B52159949
theorem B694607 : Blo 459783 694607 := bstep (se 1 (by rfl) ⟨520955, by rfl⟩ : syracuseStep 694607 = 1041911) B1041911
theorem B694631 : Blo 459783 694631 := bstep (se 1 (by rfl) ⟨520973, by rfl⟩ : syracuseStep 694631 = 1041947) B1041947
theorem B2955629 : Blo 459783 2955629 := bstep (se 3 (by rfl) ⟨554180, by rfl⟩ : syracuseStep 2955629 = 1108361) B1108361
theorem B694697 : Blo 459783 694697 := bstep (se 2 (by rfl) ⟨260511, by rfl⟩ : syracuseStep 694697 = 521023) B521023
theorem B4987453 : Blo 459783 4987453 := bstep (se 3 (by rfl) ⟨935147, by rfl⟩ : syracuseStep 4987453 = 1870295) B1870295
theorem B695081 : Blo 459783 695081 := bstep (se 2 (by rfl) ⟨260655, by rfl⟩ : syracuseStep 695081 = 521311) B521311
theorem B1973153 : Blo 459783 1973153 := bstep (se 2 (by rfl) ⟨739932, by rfl⟩ : syracuseStep 1973153 = 1479865) B1479865
theorem B695291 : Blo 459783 695291 := bstep (se 1 (by rfl) ⟨521468, by rfl⟩ : syracuseStep 695291 = 1042937) B1042937
theorem B695327 : Blo 459783 695327 := bstep (se 1 (by rfl) ⟨521495, by rfl⟩ : syracuseStep 695327 = 1042991) B1042991
theorem B695351 : Blo 459783 695351 := bstep (se 1 (by rfl) ⟨521513, by rfl⟩ : syracuseStep 695351 = 1043027) B1043027
theorem B695471 : Blo 459783 695471 := bstep (se 1 (by rfl) ⟨521603, by rfl⟩ : syracuseStep 695471 = 1043207) B1043207
theorem B695615 : Blo 459783 695615 := bstep (se 1 (by rfl) ⟨521711, by rfl⟩ : syracuseStep 695615 = 1043423) B1043423
theorem B2628935 : Blo 459783 2628935 := bstep (se 1 (by rfl) ⟨1971701, by rfl⟩ : syracuseStep 2628935 = 3943403) B3943403
theorem B4005287 : Blo 459783 4005287 := bstep (se 1 (by rfl) ⟨3003965, by rfl⟩ : syracuseStep 4005287 = 6007931) B6007931
theorem B1974041 : Blo 459783 1974041 := bstep (se 2 (by rfl) ⟨740265, by rfl⟩ : syracuseStep 1974041 = 1480531) B1480531
theorem B2334905 : Blo 459783 2334905 := bstep (se 2 (by rfl) ⟨875589, by rfl⟩ : syracuseStep 2334905 = 1751179) B1751179
theorem B1057151 : Blo 459783 1057151 := bstep (se 1 (by rfl) ⟨792863, by rfl⟩ : syracuseStep 1057151 = 1585727) B1585727
theorem B5907977 : Blo 459783 5907977 := bstep (se 2 (by rfl) ⟨2215491, by rfl⟩ : syracuseStep 5907977 = 4430983) B4430983
theorem B5318939 : Blo 459783 5318939 := bstep (se 1 (by rfl) ⟨3989204, by rfl⟩ : syracuseStep 5318939 = 7978409) B7978409
theorem B6007081 : Blo 459783 6007081 := bstep (se 2 (by rfl) ⟨2252655, by rfl⟩ : syracuseStep 6007081 = 4505311) B4505311
theorem B11086409 : Blo 459783 11086409 := bstep (se 2 (by rfl) ⟨4157403, by rfl⟩ : syracuseStep 11086409 = 8314807) B8314807
theorem B830047 : Blo 459783 830047 := bstep (se 1 (by rfl) ⟨622535, by rfl⟩ : syracuseStep 830047 = 1245071) B1245071
theorem B1977169 : Blo 459783 1977169 := bstep (se 2 (by rfl) ⟨741438, by rfl⟩ : syracuseStep 1977169 = 1482877) B1482877
theorem B13315549 : Blo 459783 13315549 := bstep (se 3 (by rfl) ⟨2496665, by rfl⟩ : syracuseStep 13315549 = 4993331) B4993331
theorem B3518153 : Blo 459783 3518153 := bstep (se 2 (by rfl) ⟨1319307, by rfl⟩ : syracuseStep 3518153 = 2638615) B2638615
theorem B2502377 : Blo 459783 2502377 := bstep (se 2 (by rfl) ⟨938391, by rfl⟩ : syracuseStep 2502377 = 1876783) B1876783
theorem B995431 : Blo 459783 995431 := bstep (se 1 (by rfl) ⟨746573, by rfl⟩ : syracuseStep 995431 = 1493147) B1493147
theorem B2437951 : Blo 459783 2437951 := bstep (se 1 (by rfl) ⟨1828463, by rfl⟩ : syracuseStep 2437951 = 3656927) B3656927
theorem B1749995 : Blo 459783 1749995 := bstep (se 1 (by rfl) ⟨1312496, by rfl⟩ : syracuseStep 1749995 = 2624993) B2624993
theorem B11809799 : Blo 459783 11809799 := bstep (se 1 (by rfl) ⟨8857349, by rfl⟩ : syracuseStep 11809799 = 17714699) B17714699
theorem B11875409 : Blo 459783 11875409 := bstep (se 2 (by rfl) ⟨4453278, by rfl⟩ : syracuseStep 11875409 = 8906557) B8906557
theorem B1783235 : Blo 459783 1783235 := bstep (se 1 (by rfl) ⟨1337426, by rfl⟩ : syracuseStep 1783235 = 2674853) B2674853
theorem B2340737 : Blo 459783 2340737 := bstep (se 2 (by rfl) ⟨877776, by rfl⟩ : syracuseStep 2340737 = 1755553) B1755553
theorem B1685627 : Blo 459783 1685627 := bstep (se 1 (by rfl) ⟨1264220, by rfl⟩ : syracuseStep 1685627 = 2528441) B2528441
theorem B1751165 : Blo 459783 1751165 := bstep (se 3 (by rfl) ⟨328343, by rfl⟩ : syracuseStep 1751165 = 656687) B656687
theorem B703355 : Blo 459783 703355 := bstep (se 1 (by rfl) ⟨527516, by rfl⟩ : syracuseStep 703355 = 1055033) B1055033
theorem B3947399 : Blo 459783 3947399 := bstep (se 1 (by rfl) ⟨2960549, by rfl⟩ : syracuseStep 3947399 = 5921099) B5921099
theorem B2342033 : Blo 459783 2342033 := bstep (se 2 (by rfl) ⟨878262, by rfl⟩ : syracuseStep 2342033 = 1756525) B1756525
theorem B4439519 : Blo 459783 4439519 := bstep (se 1 (by rfl) ⟨3329639, by rfl⟩ : syracuseStep 4439519 = 6659279) B6659279
theorem B5259005 : Blo 459783 5259005 := bstep (se 3 (by rfl) ⟨986063, by rfl⟩ : syracuseStep 5259005 = 1972127) B1972127
theorem B1752911 : Blo 459783 1752911 := bstep (se 1 (by rfl) ⟨1314683, by rfl⟩ : syracuseStep 1752911 = 2629367) B2629367
theorem B25182211 : Blo 459783 25182211 := bstep (se 1 (by rfl) ⟨18886658, by rfl⟩ : syracuseStep 25182211 = 37773317) B37773317
theorem B18890759 : Blo 459783 18890759 := bstep (se 1 (by rfl) ⟨14168069, by rfl⟩ : syracuseStep 18890759 = 28336139) B28336139
theorem B1687625 : Blo 459783 1687625 := bstep (se 2 (by rfl) ⟨632859, by rfl⟩ : syracuseStep 1687625 = 1265719) B1265719
theorem B2113721 : Blo 459783 2113721 := bstep (se 2 (by rfl) ⟨792645, by rfl⟩ : syracuseStep 2113721 = 1585291) B1585291
theorem B737543 : Blo 459783 737543 := bstep (se 1 (by rfl) ⟨553157, by rfl⟩ : syracuseStep 737543 = 1106315) B1106315
theorem B2966291 : Blo 459783 2966291 := bstep (se 1 (by rfl) ⟨2224718, by rfl⟩ : syracuseStep 2966291 = 4449437) B4449437
theorem B1164395 : Blo 459783 1164395 := bstep (se 1 (by rfl) ⟨873296, by rfl⟩ : syracuseStep 1164395 = 1746593) B1746593
theorem B2966651 : Blo 459783 2966651 := bstep (se 1 (by rfl) ⟨2224988, by rfl⟩ : syracuseStep 2966651 = 4449977) B4449977
theorem B7881947 : Blo 459783 7881947 := bstep (se 1 (by rfl) ⟨5911460, by rfl⟩ : syracuseStep 7881947 = 11822921) B11822921
theorem B1557791 : Blo 459783 1557791 := bstep (se 1 (by rfl) ⟨1168343, by rfl⟩ : syracuseStep 1557791 = 2336687) B2336687
theorem B7096349 : Blo 459783 7096349 := bstep (se 3 (by rfl) ⟨1330565, by rfl⟩ : syracuseStep 7096349 = 2661131) B2661131
theorem B2967677 : Blo 459783 2967677 := bstep (se 3 (by rfl) ⟨556439, by rfl⟩ : syracuseStep 2967677 = 1112879) B1112879
theorem B7489745 : Blo 459783 7489745 := bstep (se 2 (by rfl) ⟨2808654, by rfl⟩ : syracuseStep 7489745 = 5617309) B5617309
theorem B2345273 : Blo 459783 2345273 := bstep (se 2 (by rfl) ⟨879477, by rfl⟩ : syracuseStep 2345273 = 1758955) B1758955
theorem B2640347 : Blo 459783 2640347 := bstep (se 1 (by rfl) ⟨1980260, by rfl⟩ : syracuseStep 2640347 = 3960521) B3960521
theorem B1657439 : Blo 459783 1657439 := bstep (se 1 (by rfl) ⟨1243079, by rfl⟩ : syracuseStep 1657439 = 2486159) B2486159
theorem B2378423 : Blo 459783 2378423 := bstep (se 1 (by rfl) ⟨1783817, by rfl⟩ : syracuseStep 2378423 = 3567635) B3567635
theorem B2607839 : Blo 459783 2607839 := bstep (se 1 (by rfl) ⟨1955879, by rfl⟩ : syracuseStep 2607839 = 3911759) B3911759
theorem B1559303 : Blo 459783 1559303 := bstep (se 1 (by rfl) ⟨1169477, by rfl⟩ : syracuseStep 1559303 = 2338955) B2338955
theorem B1166177 : Blo 459783 1166177 := bstep (se 2 (by rfl) ⟨437316, by rfl⟩ : syracuseStep 1166177 = 874633) B874633
theorem B1035215 : Blo 459783 1035215 := bstep (se 1 (by rfl) ⟨776411, by rfl⟩ : syracuseStep 1035215 = 1552823) B1552823
theorem B1035305 : Blo 459783 1035305 := bstep (se 2 (by rfl) ⟨388239, by rfl⟩ : syracuseStep 1035305 = 776479) B776479
theorem B21285935 : Blo 459783 21285935 := bstep (se 1 (by rfl) ⟨15964451, by rfl⟩ : syracuseStep 21285935 = 31928903) B31928903
theorem B1559681 : Blo 459783 1559681 := bstep (se 2 (by rfl) ⟨584880, by rfl⟩ : syracuseStep 1559681 = 1169761) B1169761
theorem B2968751 : Blo 459783 2968751 := bstep (se 1 (by rfl) ⟨2226563, by rfl⟩ : syracuseStep 2968751 = 4453127) B4453127
theorem B1035575 : Blo 459783 1035575 := bstep (se 1 (by rfl) ⟨776681, by rfl⟩ : syracuseStep 1035575 = 1553363) B1553363
theorem B1166683 : Blo 459783 1166683 := bstep (se 1 (by rfl) ⟨875012, by rfl⟩ : syracuseStep 1166683 = 1750025) B1750025
theorem B1560329 : Blo 459783 1560329 := bstep (se 2 (by rfl) ⟨585123, by rfl⟩ : syracuseStep 1560329 = 1170247) B1170247
theorem B1560383 : Blo 459783 1560383 := bstep (se 1 (by rfl) ⟨1170287, by rfl⟩ : syracuseStep 1560383 = 2340575) B2340575
theorem B937865 : Blo 459783 937865 := bstep (se 2 (by rfl) ⟨351699, by rfl⟩ : syracuseStep 937865 = 703399) B703399
theorem B5263379 : Blo 459783 5263379 := bstep (se 1 (by rfl) ⟨3947534, by rfl⟩ : syracuseStep 5263379 = 7895069) B7895069
theorem B4739111 : Blo 459783 4739111 := bstep (se 1 (by rfl) ⟨3554333, by rfl⟩ : syracuseStep 4739111 = 7108667) B7108667
theorem B2347055 : Blo 459783 2347055 := bstep (se 1 (by rfl) ⟨1760291, by rfl⟩ : syracuseStep 2347055 = 3520583) B3520583
theorem B7622849 : Blo 459783 7622849 := bstep (se 2 (by rfl) ⟨2858568, by rfl⟩ : syracuseStep 7622849 = 5717137) B5717137
theorem B1167635 : Blo 459783 1167635 := bstep (se 1 (by rfl) ⟨875726, by rfl⟩ : syracuseStep 1167635 = 1751453) B1751453
theorem B741803 : Blo 459783 741803 := bstep (se 1 (by rfl) ⟨556352, by rfl⟩ : syracuseStep 741803 = 1112705) B1112705
theorem B1921619 : Blo 459783 1921619 := bstep (se 1 (by rfl) ⟨1441214, by rfl⟩ : syracuseStep 1921619 = 2882429) B2882429
theorem B1561625 : Blo 459783 1561625 := bstep (se 2 (by rfl) ⟨585609, by rfl⟩ : syracuseStep 1561625 = 1171219) B1171219
theorem B873737 : Blo 459783 873737 := bstep (se 2 (by rfl) ⟨327651, by rfl⟩ : syracuseStep 873737 = 655303) B655303
theorem B775919 : Blo 459783 775919 := bstep (se 1 (by rfl) ⟨581939, by rfl⟩ : syracuseStep 775919 = 1163879) B1163879
theorem B1661215 : Blo 459783 1661215 := bstep (se 1 (by rfl) ⟨1245911, by rfl⟩ : syracuseStep 1661215 = 2491823) B2491823
theorem B10672793 : Blo 459783 10672793 := bstep (se 2 (by rfl) ⟨4002297, by rfl⟩ : syracuseStep 10672793 = 8004595) B8004595
theorem B875195 : Blo 459783 875195 := bstep (se 1 (by rfl) ⟨656396, by rfl⟩ : syracuseStep 875195 = 1312793) B1312793
theorem B76897025 : Blo 459783 76897025 := bstep (se 2 (by rfl) ⟨28836384, by rfl⟩ : syracuseStep 76897025 = 57672769) B57672769
theorem B777127 : Blo 459783 777127 := bstep (se 1 (by rfl) ⟨582845, by rfl⟩ : syracuseStep 777127 = 1165691) B1165691
theorem B777323 : Blo 459783 777323 := bstep (se 1 (by rfl) ⟨582992, by rfl⟩ : syracuseStep 777323 = 1165985) B1165985
theorem B1170683 : Blo 459783 1170683 := bstep (se 1 (by rfl) ⟨878012, by rfl⟩ : syracuseStep 1170683 = 1756025) B1756025
theorem B777593 : Blo 459783 777593 := bstep (se 2 (by rfl) ⟨291597, by rfl⟩ : syracuseStep 777593 = 583195) B583195
theorem B1040111 : Blo 459783 1040111 := bstep (se 1 (by rfl) ⟨780083, by rfl⟩ : syracuseStep 1040111 = 1560167) B1560167
theorem B778153 : Blo 459783 778153 := bstep (se 2 (by rfl) ⟨291807, by rfl⟩ : syracuseStep 778153 = 583615) B583615
theorem B779375 : Blo 459783 779375 := bstep (se 1 (by rfl) ⟨584531, by rfl⟩ : syracuseStep 779375 = 1169063) B1169063
theorem B517351 : Blo 459783 517351 := bstep (se 1 (by rfl) ⟨388013, by rfl⟩ : syracuseStep 517351 = 776027) B776027
theorem B4973957 : Blo 459783 4973957 := bstep (se 4 (by rfl) ⟨466308, by rfl⟩ : syracuseStep 4973957 = 932617) B932617
theorem B4515563 : Blo 459783 4515563 := bstep (se 1 (by rfl) ⟨3386672, by rfl⟩ : syracuseStep 4515563 = 6773345) B6773345
theorem B50652971 : Blo 459783 50652971 := bstep (se 1 (by rfl) ⟨37989728, by rfl⟩ : syracuseStep 50652971 = 75979457) B75979457
theorem B747431 : Blo 459783 747431 := bstep (se 1 (by rfl) ⟨560573, by rfl⟩ : syracuseStep 747431 = 1121147) B1121147
theorem B1173599 : Blo 459783 1173599 := bstep (se 1 (by rfl) ⟨880199, by rfl⟩ : syracuseStep 1173599 = 1760399) B1760399
theorem B584167 : Blo 459783 584167 := bstep (se 1 (by rfl) ⟨438125, by rfl⟩ : syracuseStep 584167 = 876251) B876251
theorem B2222873 : Blo 459783 2222873 := bstep (se 2 (by rfl) ⟨833577, by rfl⟩ : syracuseStep 2222873 = 1667155) B1667155
theorem B584759 : Blo 459783 584759 := bstep (se 1 (by rfl) ⟨438569, by rfl⟩ : syracuseStep 584759 = 877139) B877139
theorem B584815 : Blo 459783 584815 := bstep (se 1 (by rfl) ⟨438611, by rfl⟩ : syracuseStep 584815 = 877223) B877223
theorem B584911 : Blo 459783 584911 := bstep (se 1 (by rfl) ⟨438683, by rfl⟩ : syracuseStep 584911 = 877367) B877367
theorem B782311 : Blo 459783 782311 := bstep (se 1 (by rfl) ⟨586733, by rfl⟩ : syracuseStep 782311 = 1173467) B1173467
theorem B9990125 : Blo 459783 9990125 := bstep (se 3 (by rfl) ⟨1873148, by rfl⟩ : syracuseStep 9990125 = 3746297) B3746297
theorem B585883 : Blo 459783 585883 := bstep (se 1 (by rfl) ⟨439412, by rfl⟩ : syracuseStep 585883 = 878825) B878825
theorem B520519 : Blo 459783 520519 := bstep (se 1 (by rfl) ⟨390389, by rfl⟩ : syracuseStep 520519 = 780779) B780779
theorem B586055 : Blo 459783 586055 := bstep (se 1 (by rfl) ⟨439541, by rfl⟩ : syracuseStep 586055 = 879083) B879083
theorem B19919195 : Blo 459783 19919195 := bstep (se 1 (by rfl) ⟨14939396, by rfl⟩ : syracuseStep 19919195 = 29878793) B29878793
theorem B520987 : Blo 459783 520987 := bstep (se 1 (by rfl) ⟨390740, by rfl⟩ : syracuseStep 520987 = 781481) B781481
theorem B4223927 : Blo 459783 4223927 := bstep (se 1 (by rfl) ⟨3167945, by rfl⟩ : syracuseStep 4223927 = 6335891) B6335891
theorem B521383 : Blo 459783 521383 := bstep (se 1 (by rfl) ⟨391037, by rfl⟩ : syracuseStep 521383 = 782075) B782075
theorem B3339731 : Blo 459783 3339731 := bstep (se 1 (by rfl) ⟨2504798, by rfl⟩ : syracuseStep 3339731 = 5009597) B5009597
theorem B1406447 : Blo 459783 1406447 := bstep (se 1 (by rfl) ⟨1054835, by rfl⟩ : syracuseStep 1406447 = 2109671) B2109671
theorem B5043923 : Blo 459783 5043923 := bstep (se 1 (by rfl) ⟨3782942, by rfl⟩ : syracuseStep 5043923 = 7565885) B7565885
theorem B3929903 : Blo 459783 3929903 := bstep (se 1 (by rfl) ⟨2947427, by rfl⟩ : syracuseStep 3929903 = 5894855) B5894855
theorem B4749293 : Blo 459783 4749293 := bstep (se 3 (by rfl) ⟨890492, by rfl⟩ : syracuseStep 4749293 = 1780985) B1780985
theorem B3504545 : Blo 459783 3504545 := bstep (se 2 (by rfl) ⟨1314204, by rfl⟩ : syracuseStep 3504545 = 2628409) B2628409
theorem B1244119 : Blo 459783 1244119 := bstep (se 1 (by rfl) ⟨933089, by rfl⟩ : syracuseStep 1244119 = 1866179) B1866179
theorem B2948555 : Blo 459783 2948555 := bstep (se 1 (by rfl) ⟨2211416, by rfl⟩ : syracuseStep 2948555 = 4422833) B4422833
theorem B5603197 : Blo 459783 5603197 := bstep (se 3 (by rfl) ⟨1050599, by rfl⟩ : syracuseStep 5603197 = 2101199) B2101199
theorem B1409147 : Blo 459783 1409147 := bstep (se 1 (by rfl) ⟨1056860, by rfl⟩ : syracuseStep 1409147 = 2113721) B2113721
theorem B11862287 : Blo 459783 11862287 := bstep (se 1 (by rfl) ⟨8896715, by rfl⟩ : syracuseStep 11862287 = 17793431) B17793431
theorem B1966781 : Blo 459783 1966781 := bstep (se 3 (by rfl) ⟨368771, by rfl⟩ : syracuseStep 1966781 = 737543) B737543
theorem B459931 : Blo 459783 459931 := bstep (se 1 (by rfl) ⟨344948, by rfl⟩ : syracuseStep 459931 = 689897) B689897
theorem B459935 : Blo 459783 459935 := bstep (se 1 (by rfl) ⟨344951, by rfl⟩ : syracuseStep 459935 = 689903) B689903
theorem B460103 : Blo 459783 460103 := bstep (se 1 (by rfl) ⟨345077, by rfl⟩ : syracuseStep 460103 = 690155) B690155
theorem B460271 : Blo 459783 460271 := bstep (se 1 (by rfl) ⟨345203, by rfl⟩ : syracuseStep 460271 = 690407) B690407
theorem B460287 : Blo 459783 460287 := bstep (se 1 (by rfl) ⟨345215, by rfl⟩ : syracuseStep 460287 = 690431) B690431
theorem B460379 : Blo 459783 460379 := bstep (se 1 (by rfl) ⟨345284, by rfl⟩ : syracuseStep 460379 = 690569) B690569
theorem B689801 : Blo 459783 689801 := bstep (se 2 (by rfl) ⟨258675, by rfl⟩ : syracuseStep 689801 = 517351) B517351
theorem B5899979 : Blo 459783 5899979 := bstep (se 1 (by rfl) ⟨4424984, by rfl⟩ : syracuseStep 5899979 = 8849969) B8849969
theorem B1738559 : Blo 459783 1738559 := bstep (se 1 (by rfl) ⟨1303919, by rfl⟩ : syracuseStep 1738559 = 2607839) B2607839
theorem B690143 : Blo 459783 690143 := bstep (se 1 (by rfl) ⟨517607, by rfl⟩ : syracuseStep 690143 = 1035215) B1035215
theorem B690203 : Blo 459783 690203 := bstep (se 1 (by rfl) ⟨517652, by rfl⟩ : syracuseStep 690203 = 1035305) B1035305
theorem B14190623 : Blo 459783 14190623 := bstep (se 1 (by rfl) ⟨10642967, by rfl⟩ : syracuseStep 14190623 = 21285935) B21285935
theorem B690383 : Blo 459783 690383 := bstep (se 1 (by rfl) ⟨517787, by rfl⟩ : syracuseStep 690383 = 1035575) B1035575
theorem B461119 : Blo 459783 461119 := bstep (se 1 (by rfl) ⟨345839, by rfl⟩ : syracuseStep 461119 = 691679) B691679
theorem B461159 : Blo 459783 461159 := bstep (se 1 (by rfl) ⟨345869, by rfl⟩ : syracuseStep 461159 = 691739) B691739
theorem B461247 : Blo 459783 461247 := bstep (se 1 (by rfl) ⟨345935, by rfl⟩ : syracuseStep 461247 = 691871) B691871
theorem B625243 : Blo 459783 625243 := bstep (se 1 (by rfl) ⟨468932, by rfl⟩ : syracuseStep 625243 = 937865) B937865
theorem B461423 : Blo 459783 461423 := bstep (se 1 (by rfl) ⟨346067, by rfl⟩ : syracuseStep 461423 = 692135) B692135
theorem B461439 : Blo 459783 461439 := bstep (se 1 (by rfl) ⟨346079, by rfl⟩ : syracuseStep 461439 = 692159) B692159
theorem B3508919 : Blo 459783 3508919 := bstep (se 1 (by rfl) ⟨2631689, by rfl⟩ : syracuseStep 3508919 = 5263379) B5263379
theorem B461543 : Blo 459783 461543 := bstep (se 1 (by rfl) ⟨346157, by rfl⟩ : syracuseStep 461543 = 692315) B692315
theorem B985927 : Blo 459783 985927 := bstep (se 1 (by rfl) ⟨739445, by rfl⟩ : syracuseStep 985927 = 1478891) B1478891
theorem B461639 : Blo 459783 461639 := bstep (se 1 (by rfl) ⟨346229, by rfl⟩ : syracuseStep 461639 = 692459) B692459
theorem B461679 : Blo 459783 461679 := bstep (se 1 (by rfl) ⟨346259, by rfl⟩ : syracuseStep 461679 = 692519) B692519
theorem B461855 : Blo 459783 461855 := bstep (se 1 (by rfl) ⟨346391, by rfl⟩ : syracuseStep 461855 = 692783) B692783
theorem B1281079 : Blo 459783 1281079 := bstep (se 1 (by rfl) ⟨960809, by rfl⟩ : syracuseStep 1281079 = 1921619) B1921619
theorem B461991 : Blo 459783 461991 := bstep (se 1 (by rfl) ⟨346493, by rfl⟩ : syracuseStep 461991 = 692987) B692987
theorem B462239 : Blo 459783 462239 := bstep (se 1 (by rfl) ⟨346679, by rfl⟩ : syracuseStep 462239 = 693359) B693359
theorem B462287 : Blo 459783 462287 := bstep (se 1 (by rfl) ⟨346715, by rfl⟩ : syracuseStep 462287 = 693431) B693431
theorem B462447 : Blo 459783 462447 := bstep (se 1 (by rfl) ⟨346835, by rfl⟩ : syracuseStep 462447 = 693671) B693671
theorem B462567 : Blo 459783 462567 := bstep (se 1 (by rfl) ⟨346925, by rfl⟩ : syracuseStep 462567 = 693851) B693851
theorem B463071 : Blo 459783 463071 := bstep (se 1 (by rfl) ⟨347303, by rfl⟩ : syracuseStep 463071 = 694607) B694607
theorem B463087 : Blo 459783 463087 := bstep (se 1 (by rfl) ⟨347315, by rfl⟩ : syracuseStep 463087 = 694631) B694631
theorem B1970419 : Blo 459783 1970419 := bstep (se 1 (by rfl) ⟨1477814, by rfl⟩ : syracuseStep 1970419 = 2955629) B2955629
theorem B463131 : Blo 459783 463131 := bstep (se 1 (by rfl) ⟨347348, by rfl⟩ : syracuseStep 463131 = 694697) B694697
theorem B7115195 : Blo 459783 7115195 := bstep (se 1 (by rfl) ⟨5336396, by rfl⟩ : syracuseStep 7115195 = 10672793) B10672793
theorem B463387 : Blo 459783 463387 := bstep (se 1 (by rfl) ⟨347540, by rfl⟩ : syracuseStep 463387 = 695081) B695081
theorem B1315435 : Blo 459783 1315435 := bstep (se 1 (by rfl) ⟨986576, by rfl⟩ : syracuseStep 1315435 = 1973153) B1973153
theorem B463527 : Blo 459783 463527 := bstep (se 1 (by rfl) ⟨347645, by rfl⟩ : syracuseStep 463527 = 695291) B695291
theorem B463551 : Blo 459783 463551 := bstep (se 1 (by rfl) ⟨347663, by rfl⟩ : syracuseStep 463551 = 695327) B695327
theorem B463567 : Blo 459783 463567 := bstep (se 1 (by rfl) ⟨347675, by rfl⟩ : syracuseStep 463567 = 695351) B695351
theorem B463647 : Blo 459783 463647 := bstep (se 1 (by rfl) ⟨347735, by rfl⟩ : syracuseStep 463647 = 695471) B695471
theorem B463743 : Blo 459783 463743 := bstep (se 1 (by rfl) ⟨347807, by rfl⟩ : syracuseStep 463743 = 695615) B695615
theorem B693407 : Blo 459783 693407 := bstep (se 1 (by rfl) ⟨520055, by rfl⟩ : syracuseStep 693407 = 1040111) B1040111
theorem B1316027 : Blo 459783 1316027 := bstep (se 1 (by rfl) ⟨987020, by rfl⟩ : syracuseStep 1316027 = 1974041) B1974041
theorem B694025 : Blo 459783 694025 := bstep (se 2 (by rfl) ⟨260259, by rfl⟩ : syracuseStep 694025 = 520519) B520519
theorem B3315971 : Blo 459783 3315971 := bstep (se 1 (by rfl) ⟨2486978, by rfl⟩ : syracuseStep 3315971 = 4973957) B4973957
theorem B3938651 : Blo 459783 3938651 := bstep (se 1 (by rfl) ⟨2953988, by rfl⟩ : syracuseStep 3938651 = 5907977) B5907977
theorem B694649 : Blo 459783 694649 := bstep (se 2 (by rfl) ⟨260493, by rfl⟩ : syracuseStep 694649 = 520987) B520987
theorem B3250601 : Blo 459783 3250601 := bstep (se 2 (by rfl) ⟨1218975, by rfl⟩ : syracuseStep 3250601 = 2437951) B2437951
theorem B498287 : Blo 459783 498287 := bstep (se 1 (by rfl) ⟨373715, by rfl⟩ : syracuseStep 498287 = 747431) B747431
theorem B3545959 : Blo 459783 3545959 := bstep (se 1 (by rfl) ⟨2659469, by rfl⟩ : syracuseStep 3545959 = 5318939) B5318939
theorem B695177 : Blo 459783 695177 := bstep (se 2 (by rfl) ⟨260691, by rfl⟩ : syracuseStep 695177 = 521383) B521383
theorem B1481915 : Blo 459783 1481915 := bstep (se 1 (by rfl) ⟨1111436, by rfl⟩ : syracuseStep 1481915 = 2222873) B2222873
theorem B1318169 : Blo 459783 1318169 := bstep (se 2 (by rfl) ⟨494313, by rfl⟩ : syracuseStep 1318169 = 988627) B988627
theorem B6660083 : Blo 459783 6660083 := bstep (se 1 (by rfl) ⟨4995062, by rfl⟩ : syracuseStep 6660083 = 9990125) B9990125
theorem B13279463 : Blo 459783 13279463 := bstep (se 1 (by rfl) ⟨9959597, by rfl⟩ : syracuseStep 13279463 = 19919195) B19919195
theorem B7873199 : Blo 459783 7873199 := bstep (se 1 (by rfl) ⟨5904899, by rfl⟩ : syracuseStep 7873199 = 11809799) B11809799
theorem B1188823 : Blo 459783 1188823 := bstep (se 1 (by rfl) ⟨891617, by rfl⟩ : syracuseStep 1188823 = 1783235) B1783235
theorem B1123751 : Blo 459783 1123751 := bstep (se 1 (by rfl) ⟨842813, by rfl⟩ : syracuseStep 1123751 = 1685627) B1685627
theorem B2336363 : Blo 459783 2336363 := bstep (se 1 (by rfl) ⟨1752272, by rfl⟩ : syracuseStep 2336363 = 3504545) B3504545
theorem B2631599 : Blo 459783 2631599 := bstep (se 1 (by rfl) ⟨1973699, by rfl⟩ : syracuseStep 2631599 = 3947399) B3947399
theorem B2959679 : Blo 459783 2959679 := bstep (se 1 (by rfl) ⟨2219759, by rfl⟩ : syracuseStep 2959679 = 4439519) B4439519
theorem B12593839 : Blo 459783 12593839 := bstep (se 1 (by rfl) ⟨9445379, by rfl⟩ : syracuseStep 12593839 = 18890759) B18890759
theorem B1125083 : Blo 459783 1125083 := bstep (se 1 (by rfl) ⟨843812, by rfl⟩ : syracuseStep 1125083 = 1687625) B1687625
theorem B20327597 : Blo 459783 20327597 := bstep (se 3 (by rfl) ⟨3811424, by rfl⟩ : syracuseStep 20327597 = 7622849) B7622849
theorem B1977527 : Blo 459783 1977527 := bstep (se 1 (by rfl) ⟨1483145, by rfl⟩ : syracuseStep 1977527 = 2966291) B2966291
theorem B1977767 : Blo 459783 1977767 := bstep (se 1 (by rfl) ⟨1483325, by rfl⟩ : syracuseStep 1977767 = 2966651) B2966651
theorem B5254631 : Blo 459783 5254631 := bstep (se 1 (by rfl) ⟨3940973, by rfl⟩ : syracuseStep 5254631 = 7881947) B7881947
theorem B700169 : Blo 459783 700169 := bstep (se 2 (by rfl) ⟨262563, by rfl⟩ : syracuseStep 700169 = 525127) B525127
theorem B4730899 : Blo 459783 4730899 := bstep (se 1 (by rfl) ⟨3548174, by rfl⟩ : syracuseStep 4730899 = 7096349) B7096349
theorem B1978451 : Blo 459783 1978451 := bstep (se 1 (by rfl) ⟨1483838, by rfl⟩ : syracuseStep 1978451 = 2967677) B2967677
theorem B4993163 : Blo 459783 4993163 := bstep (se 1 (by rfl) ⟨3744872, by rfl⟩ : syracuseStep 4993163 = 7489745) B7489745
theorem B1979167 : Blo 459783 1979167 := bstep (se 1 (by rfl) ⟨1484375, by rfl⟩ : syracuseStep 1979167 = 2968751) B2968751
theorem B3159407 : Blo 459783 3159407 := bstep (se 1 (by rfl) ⟨2369555, by rfl⟩ : syracuseStep 3159407 = 4739111) B4739111
theorem B1554011 : Blo 459783 1554011 := bstep (se 1 (by rfl) ⟨1165508, by rfl⟩ : syracuseStep 1554011 = 2331017) B2331017
theorem B8009441 : Blo 459783 8009441 := bstep (se 2 (by rfl) ⟨3003540, by rfl⟩ : syracuseStep 8009441 = 6007081) B6007081
theorem B2636225 : Blo 459783 2636225 := bstep (se 2 (by rfl) ⟨988584, by rfl⟩ : syracuseStep 2636225 = 1977169) B1977169
theorem B572095 : Blo 459783 572095 := bstep (se 1 (by rfl) ⟨429071, by rfl⟩ : syracuseStep 572095 = 858143) B858143
theorem B23182199 : Blo 459783 23182199 := bstep (se 1 (by rfl) ⟨17386649, by rfl⟩ : syracuseStep 23182199 = 34773299) B34773299
theorem B7912565 : Blo 459783 7912565 := bstep (se 5 (by rfl) ⟨370901, by rfl⟩ : syracuseStep 7912565 = 741803) B741803
theorem B1555577 : Blo 459783 1555577 := bstep (se 2 (by rfl) ⟨583341, by rfl⟩ : syracuseStep 1555577 = 1166683) B1166683
theorem B51264683 : Blo 459783 51264683 := bstep (se 1 (by rfl) ⟨38448512, by rfl⟩ : syracuseStep 51264683 = 76897025) B76897025
theorem B1752623 : Blo 459783 1752623 := bstep (se 1 (by rfl) ⟨1314467, by rfl⟩ : syracuseStep 1752623 = 2628935) B2628935
theorem B2670191 : Blo 459783 2670191 := bstep (se 1 (by rfl) ⟨2002643, by rfl⟩ : syracuseStep 2670191 = 4005287) B4005287
theorem B12664781 : Blo 459783 12664781 := bstep (se 3 (by rfl) ⟨2374646, by rfl⟩ : syracuseStep 12664781 = 4749293) B4749293
theorem B1556603 : Blo 459783 1556603 := bstep (se 1 (by rfl) ⟨1167452, by rfl⟩ : syracuseStep 1556603 = 2334905) B2334905
theorem B1327241 : Blo 459783 1327241 := bstep (se 2 (by rfl) ⟨497715, by rfl⟩ : syracuseStep 1327241 = 995431) B995431
theorem B704767 : Blo 459783 704767 := bstep (se 1 (by rfl) ⟨528575, by rfl⟩ : syracuseStep 704767 = 1057151) B1057151
theorem B12600197 : Blo 459783 12600197 := bstep (se 4 (by rfl) ⟨1181268, by rfl⟩ : syracuseStep 12600197 = 2362537) B2362537
theorem B33768647 : Blo 459783 33768647 := bstep (se 1 (by rfl) ⟨25326485, by rfl⟩ : syracuseStep 33768647 = 50652971) B50652971
theorem B7390939 : Blo 459783 7390939 := bstep (se 1 (by rfl) ⟨5543204, by rfl⟩ : syracuseStep 7390939 = 11086409) B11086409
theorem B6342461 : Blo 459783 6342461 := bstep (se 3 (by rfl) ⟨1189211, by rfl⟩ : syracuseStep 6342461 = 2378423) B2378423
theorem B2345435 : Blo 459783 2345435 := bstep (se 1 (by rfl) ⟨1759076, by rfl⟩ : syracuseStep 2345435 = 3518153) B3518153
theorem B1559357 : Blo 459783 1559357 := bstep (se 3 (by rfl) ⟨292379, by rfl⟩ : syracuseStep 1559357 = 584759) B584759
theorem B2214953 : Blo 459783 2214953 := bstep (se 2 (by rfl) ⟨830607, by rfl⟩ : syracuseStep 2214953 = 1661215) B1661215
theorem B1166663 : Blo 459783 1166663 := bstep (se 1 (by rfl) ⟨874997, by rfl⟩ : syracuseStep 1166663 = 1749995) B1749995
theorem B7916939 : Blo 459783 7916939 := bstep (se 1 (by rfl) ⟨5937704, by rfl⟩ : syracuseStep 7916939 = 11875409) B11875409
theorem B937631 : Blo 459783 937631 := bstep (se 1 (by rfl) ⟨703223, by rfl⟩ : syracuseStep 937631 = 1406447) B1406447
theorem B3362615 : Blo 459783 3362615 := bstep (se 1 (by rfl) ⟨2521961, by rfl⟩ : syracuseStep 3362615 = 5043923) B5043923
theorem B1036169 : Blo 459783 1036169 := bstep (se 2 (by rfl) ⟨388563, by rfl⟩ : syracuseStep 1036169 = 777127) B777127
theorem B1560491 : Blo 459783 1560491 := bstep (se 1 (by rfl) ⟨1170368, by rfl⟩ : syracuseStep 1560491 = 2340737) B2340737
theorem B1658825 : Blo 459783 1658825 := bstep (se 2 (by rfl) ⟨622059, by rfl⟩ : syracuseStep 1658825 = 1244119) B1244119
theorem B1167443 : Blo 459783 1167443 := bstep (se 1 (by rfl) ⟨875582, by rfl⟩ : syracuseStep 1167443 = 1751165) B1751165
theorem B1561355 : Blo 459783 1561355 := bstep (se 1 (by rfl) ⟨1171016, by rfl⟩ : syracuseStep 1561355 = 2342033) B2342033
theorem B1168607 : Blo 459783 1168607 := bstep (se 1 (by rfl) ⟨876455, by rfl⟩ : syracuseStep 1168607 = 1752911) B1752911
theorem B1037537 : Blo 459783 1037537 := bstep (se 2 (by rfl) ⟨389076, by rfl⟩ : syracuseStep 1037537 = 778153) B778153
theorem B33576281 : Blo 459783 33576281 := bstep (se 2 (by rfl) ⟨12591105, by rfl⟩ : syracuseStep 33576281 = 25182211) B25182211
theorem B1660409 : Blo 459783 1660409 := bstep (se 2 (by rfl) ⟨622653, by rfl⟩ : syracuseStep 1660409 = 1245307) B1245307
theorem B776263 : Blo 459783 776263 := bstep (se 1 (by rfl) ⟨582197, by rfl⟩ : syracuseStep 776263 = 1164395) B1164395
theorem B1562813 : Blo 459783 1562813 := bstep (se 3 (by rfl) ⟨293027, by rfl⟩ : syracuseStep 1562813 = 586055) B586055
theorem B1038527 : Blo 459783 1038527 := bstep (se 1 (by rfl) ⟨778895, by rfl⟩ : syracuseStep 1038527 = 1557791) B1557791
theorem B1563515 : Blo 459783 1563515 := bstep (se 1 (by rfl) ⟨1172636, by rfl⟩ : syracuseStep 1563515 = 2345273) B2345273
theorem B1760231 : Blo 459783 1760231 := bstep (se 1 (by rfl) ⟨1320173, by rfl⟩ : syracuseStep 1760231 = 2640347) B2640347
theorem B1104959 : Blo 459783 1104959 := bstep (se 1 (by rfl) ⟨828719, by rfl⟩ : syracuseStep 1104959 = 1657439) B1657439
theorem B1039535 : Blo 459783 1039535 := bstep (se 1 (by rfl) ⟨779651, by rfl⟩ : syracuseStep 1039535 = 1559303) B1559303
theorem B777451 : Blo 459783 777451 := bstep (se 1 (by rfl) ⟨583088, by rfl⟩ : syracuseStep 777451 = 1166177) B1166177
theorem B3497255 : Blo 459783 3497255 := bstep (se 1 (by rfl) ⟨2622941, by rfl⟩ : syracuseStep 3497255 = 5245883) B5245883
theorem B1039787 : Blo 459783 1039787 := bstep (se 1 (by rfl) ⟨779840, by rfl⟩ : syracuseStep 1039787 = 1559681) B1559681
theorem B1040219 : Blo 459783 1040219 := bstep (se 1 (by rfl) ⟨780164, by rfl⟩ : syracuseStep 1040219 = 1560329) B1560329
theorem B1040255 : Blo 459783 1040255 := bstep (se 1 (by rfl) ⟨780191, by rfl⟩ : syracuseStep 1040255 = 1560383) B1560383
theorem B1564703 : Blo 459783 1564703 := bstep (se 1 (by rfl) ⟨1173527, by rfl⟩ : syracuseStep 1564703 = 2347055) B2347055
theorem B778423 : Blo 459783 778423 := bstep (se 1 (by rfl) ⟨583817, by rfl⟩ : syracuseStep 778423 = 1167635) B1167635
theorem B1663163 : Blo 459783 1663163 := bstep (se 1 (by rfl) ⟨1247372, by rfl⟩ : syracuseStep 1663163 = 2494745) B2494745
theorem B778889 : Blo 459783 778889 := bstep (se 2 (by rfl) ⟨292083, by rfl⟩ : syracuseStep 778889 = 584167) B584167
theorem B1041083 : Blo 459783 1041083 := bstep (se 1 (by rfl) ⟨780812, by rfl⟩ : syracuseStep 1041083 = 1561625) B1561625
theorem B1106729 : Blo 459783 1106729 := bstep (se 2 (by rfl) ⟨415023, by rfl⟩ : syracuseStep 1106729 = 830047) B830047
theorem B582491 : Blo 459783 582491 := bstep (se 1 (by rfl) ⟨436868, by rfl⟩ : syracuseStep 582491 = 873737) B873737
theorem B517279 : Blo 459783 517279 := bstep (se 1 (by rfl) ⟨387959, by rfl⟩ : syracuseStep 517279 = 775919) B775919
theorem B779753 : Blo 459783 779753 := bstep (se 2 (by rfl) ⟨292407, by rfl⟩ : syracuseStep 779753 = 584815) B584815
theorem B878111 : Blo 459783 878111 := bstep (se 1 (by rfl) ⟨658583, by rfl⟩ : syracuseStep 878111 = 1317167) B1317167
theorem B779881 : Blo 459783 779881 := bstep (se 2 (by rfl) ⟨292455, by rfl⟩ : syracuseStep 779881 = 584911) B584911
theorem B3499685 : Blo 459783 3499685 := bstep (se 4 (by rfl) ⟨328095, by rfl⟩ : syracuseStep 3499685 = 656191) B656191
theorem B583463 : Blo 459783 583463 := bstep (se 1 (by rfl) ⟨437597, by rfl⟩ : syracuseStep 583463 = 875195) B875195
theorem B17754065 : Blo 459783 17754065 := bstep (se 2 (by rfl) ⟨6657774, by rfl⟩ : syracuseStep 17754065 = 13315549) B13315549
theorem B518215 : Blo 459783 518215 := bstep (se 1 (by rfl) ⟨388661, by rfl⟩ : syracuseStep 518215 = 777323) B777323
theorem B780455 : Blo 459783 780455 := bstep (se 1 (by rfl) ⟨585341, by rfl⟩ : syracuseStep 780455 = 1170683) B1170683
theorem B518395 : Blo 459783 518395 := bstep (se 1 (by rfl) ⟨388796, by rfl⟩ : syracuseStep 518395 = 777593) B777593
theorem B1043081 : Blo 459783 1043081 := bstep (se 2 (by rfl) ⟨391155, by rfl⟩ : syracuseStep 1043081 = 782311) B782311
theorem B879265 : Blo 459783 879265 := bstep (se 2 (by rfl) ⟨329724, by rfl⟩ : syracuseStep 879265 = 659449) B659449
theorem B781177 : Blo 459783 781177 := bstep (se 2 (by rfl) ⟨292941, by rfl⟩ : syracuseStep 781177 = 585883) B585883
theorem B519583 : Blo 459783 519583 := bstep (se 1 (by rfl) ⟨389687, by rfl⟩ : syracuseStep 519583 = 779375) B779375
theorem B3010375 : Blo 459783 3010375 := bstep (se 1 (by rfl) ⟨2257781, by rfl⟩ : syracuseStep 3010375 = 4515563) B4515563
theorem B782399 : Blo 459783 782399 := bstep (se 1 (by rfl) ⟨586799, by rfl⟩ : syracuseStep 782399 = 1173599) B1173599
theorem B1405241 : Blo 459783 1405241 := bstep (se 2 (by rfl) ⟨526965, by rfl⟩ : syracuseStep 1405241 = 1053931) B1053931
theorem B1668251 : Blo 459783 1668251 := bstep (se 1 (by rfl) ⟨1251188, by rfl⟩ : syracuseStep 1668251 = 2502377) B2502377
theorem B2815951 : Blo 459783 2815951 := bstep (se 1 (by rfl) ⟨2111963, by rfl⟩ : syracuseStep 2815951 = 4223927) B4223927
theorem B6649937 : Blo 459783 6649937 := bstep (se 2 (by rfl) ⟨2493726, by rfl⟩ : syracuseStep 6649937 = 4987453) B4987453
theorem B2226487 : Blo 459783 2226487 := bstep (se 1 (by rfl) ⟨1669865, by rfl⟩ : syracuseStep 2226487 = 3339731) B3339731
theorem B2619935 : Blo 459783 2619935 := bstep (se 1 (by rfl) ⟨1964951, by rfl⟩ : syracuseStep 2619935 = 3929903) B3929903
theorem B7502453 : Blo 459783 7502453 := bstep (se 5 (by rfl) ⟨351677, by rfl⟩ : syracuseStep 7502453 = 703355) B703355
theorem B1965703 : Blo 459783 1965703 := bstep (se 1 (by rfl) ⟨1474277, by rfl⟩ : syracuseStep 1965703 = 2948555) B2948555
theorem B7470929 : Blo 459783 7470929 := bstep (se 2 (by rfl) ⟨2801598, by rfl⟩ : syracuseStep 7470929 = 5603197) B5603197
theorem B3506003 : Blo 459783 3506003 := bstep (se 1 (by rfl) ⟨2629502, by rfl⟩ : syracuseStep 3506003 = 5259005) B5259005
theorem B884827 : Blo 459783 884827 := bstep (se 1 (by rfl) ⟨663620, by rfl⟩ : syracuseStep 884827 = 1327241) B1327241
theorem B1311187 : Blo 459783 1311187 := bstep (se 1 (by rfl) ⟨983390, by rfl⟩ : syracuseStep 1311187 = 1966781) B1966781
theorem B22512431 : Blo 459783 22512431 := bstep (se 1 (by rfl) ⟨16884323, by rfl⟩ : syracuseStep 22512431 = 33768647) B33768647
theorem B459867 : Blo 459783 459867 := bstep (se 1 (by rfl) ⟨344900, by rfl⟩ : syracuseStep 459867 = 689801) B689801
theorem B3933319 : Blo 459783 3933319 := bstep (se 1 (by rfl) ⟨2949989, by rfl⟩ : syracuseStep 3933319 = 5899979) B5899979
theorem B4228307 : Blo 459783 4228307 := bstep (se 1 (by rfl) ⟨3171230, by rfl⟩ : syracuseStep 4228307 = 6342461) B6342461
theorem B460095 : Blo 459783 460095 := bstep (se 1 (by rfl) ⟨345071, by rfl⟩ : syracuseStep 460095 = 690143) B690143
theorem B460135 : Blo 459783 460135 := bstep (se 1 (by rfl) ⟨345101, by rfl⟩ : syracuseStep 460135 = 690203) B690203
theorem B460255 : Blo 459783 460255 := bstep (se 1 (by rfl) ⟨345191, by rfl⟩ : syracuseStep 460255 = 690383) B690383
theorem B689705 : Blo 459783 689705 := bstep (se 2 (by rfl) ⟨258639, by rfl⟩ : syracuseStep 689705 = 517279) B517279
theorem B1476635 : Blo 459783 1476635 := bstep (se 1 (by rfl) ⟨1107476, by rfl⟩ : syracuseStep 1476635 = 2214953) B2214953
theorem B5277959 : Blo 459783 5277959 := bstep (se 1 (by rfl) ⟨3958469, by rfl⟩ : syracuseStep 5277959 = 7916939) B7916939
theorem B625087 : Blo 459783 625087 := bstep (se 1 (by rfl) ⟨468815, by rfl⟩ : syracuseStep 625087 = 937631) B937631
theorem B690779 : Blo 459783 690779 := bstep (se 1 (by rfl) ⟨518084, by rfl⟩ : syracuseStep 690779 = 1036169) B1036169
theorem B690953 : Blo 459783 690953 := bstep (se 2 (by rfl) ⟨259107, by rfl⟩ : syracuseStep 690953 = 518215) B518215
theorem B691193 : Blo 459783 691193 := bstep (se 2 (by rfl) ⟨259197, by rfl⟩ : syracuseStep 691193 = 518395) B518395
theorem B3509405 : Blo 459783 3509405 := bstep (se 3 (by rfl) ⟨658013, by rfl⟩ : syracuseStep 3509405 = 1316027) B1316027
theorem B462271 : Blo 459783 462271 := bstep (se 1 (by rfl) ⟨346703, by rfl⟩ : syracuseStep 462271 = 693407) B693407
theorem B691691 : Blo 459783 691691 := bstep (se 1 (by rfl) ⟨518768, by rfl⟩ : syracuseStep 691691 = 1037537) B1037537
theorem B22384187 : Blo 459783 22384187 := bstep (se 1 (by rfl) ⟨16788140, by rfl⟩ : syracuseStep 22384187 = 33576281) B33576281
theorem B3051173 : Blo 459783 3051173 := bstep (se 4 (by rfl) ⟨286047, by rfl⟩ : syracuseStep 3051173 = 572095) B572095
theorem B1314569 : Blo 459783 1314569 := bstep (se 2 (by rfl) ⟨492963, by rfl⟩ : syracuseStep 1314569 = 985927) B985927
theorem B462683 : Blo 459783 462683 := bstep (se 1 (by rfl) ⟨347012, by rfl⟩ : syracuseStep 462683 = 694025) B694025
theorem B692351 : Blo 459783 692351 := bstep (se 1 (by rfl) ⟨519263, by rfl⟩ : syracuseStep 692351 = 1038527) B1038527
theorem B2625767 : Blo 459783 2625767 := bstep (se 1 (by rfl) ⟨1969325, by rfl⟩ : syracuseStep 2625767 = 3938651) B3938651
theorem B463099 : Blo 459783 463099 := bstep (se 1 (by rfl) ⟨347324, by rfl⟩ : syracuseStep 463099 = 694649) B694649
theorem B2167067 : Blo 459783 2167067 := bstep (se 1 (by rfl) ⟨1625300, by rfl⟩ : syracuseStep 2167067 = 3250601) B3250601
theorem B692777 : Blo 459783 692777 := bstep (se 2 (by rfl) ⟨259791, by rfl⟩ : syracuseStep 692777 = 519583) B519583
theorem B463451 : Blo 459783 463451 := bstep (se 1 (by rfl) ⟨347588, by rfl⟩ : syracuseStep 463451 = 695177) B695177
theorem B693023 : Blo 459783 693023 := bstep (se 1 (by rfl) ⟨519767, by rfl⟩ : syracuseStep 693023 = 1039535) B1039535
theorem B2331503 : Blo 459783 2331503 := bstep (se 1 (by rfl) ⟨1748627, by rfl⟩ : syracuseStep 2331503 = 3497255) B3497255
theorem B693191 : Blo 459783 693191 := bstep (se 1 (by rfl) ⟨519893, by rfl⟩ : syracuseStep 693191 = 1039787) B1039787
theorem B693479 : Blo 459783 693479 := bstep (se 1 (by rfl) ⟨520109, by rfl⟩ : syracuseStep 693479 = 1040219) B1040219
theorem B693503 : Blo 459783 693503 := bstep (se 1 (by rfl) ⟨520127, by rfl⟩ : syracuseStep 693503 = 1040255) B1040255
theorem B8852975 : Blo 459783 8852975 := bstep (se 1 (by rfl) ⟨6639731, by rfl⟩ : syracuseStep 8852975 = 13279463) B13279463
theorem B2627225 : Blo 459783 2627225 := bstep (se 2 (by rfl) ⟨985209, by rfl⟩ : syracuseStep 2627225 = 1970419) B1970419
theorem B5248799 : Blo 459783 5248799 := bstep (se 1 (by rfl) ⟨3936599, by rfl⟩ : syracuseStep 5248799 = 7873199) B7873199
theorem B694055 : Blo 459783 694055 := bstep (se 1 (by rfl) ⟨520541, by rfl⟩ : syracuseStep 694055 = 1041083) B1041083
theorem B2333123 : Blo 459783 2333123 := bstep (se 1 (by rfl) ⟨1749842, by rfl⟩ : syracuseStep 2333123 = 3499685) B3499685
theorem B11836043 : Blo 459783 11836043 := bstep (se 1 (by rfl) ⟨8877032, by rfl⟩ : syracuseStep 11836043 = 17754065) B17754065
theorem B1973119 : Blo 459783 1973119 := bstep (se 1 (by rfl) ⟨1479839, by rfl⟩ : syracuseStep 1973119 = 2959679) B2959679
theorem B695387 : Blo 459783 695387 := bstep (se 1 (by rfl) ⟨521540, by rfl⟩ : syracuseStep 695387 = 1043081) B1043081
theorem B1318351 : Blo 459783 1318351 := bstep (se 1 (by rfl) ⟨988763, by rfl⟩ : syracuseStep 1318351 = 1977527) B1977527
theorem B1318511 : Blo 459783 1318511 := bstep (se 1 (by rfl) ⟨988883, by rfl⟩ : syracuseStep 1318511 = 1977767) B1977767
theorem B1318967 : Blo 459783 1318967 := bstep (se 1 (by rfl) ⟨989225, by rfl⟩ : syracuseStep 1318967 = 1978451) B1978451
theorem B2106271 : Blo 459783 2106271 := bstep (se 1 (by rfl) ⟨1579703, by rfl⟩ : syracuseStep 2106271 = 3159407) B3159407
theorem B4727945 : Blo 459783 4727945 := bstep (se 2 (by rfl) ⟨1772979, by rfl⟩ : syracuseStep 4727945 = 3545959) B3545959
theorem B4433291 : Blo 459783 4433291 := bstep (se 1 (by rfl) ⟨3324968, by rfl⟩ : syracuseStep 4433291 = 6649937) B6649937
theorem B1746623 : Blo 459783 1746623 := bstep (se 1 (by rfl) ⟨1309967, by rfl⟩ : syracuseStep 1746623 = 2619935) B2619935
theorem B1780127 : Blo 459783 1780127 := bstep (se 1 (by rfl) ⟨1335095, by rfl⟩ : syracuseStep 1780127 = 2670191) B2670191
theorem B2337335 : Blo 459783 2337335 := bstep (se 1 (by rfl) ⟨1753001, by rfl⟩ : syracuseStep 2337335 = 3506003) B3506003
theorem B7908191 : Blo 459783 7908191 := bstep (se 1 (by rfl) ⟨5931143, by rfl⟩ : syracuseStep 7908191 = 11862287) B11862287
theorem B8400131 : Blo 459783 8400131 := bstep (se 1 (by rfl) ⟨6300098, by rfl⟩ : syracuseStep 8400131 = 12600197) B12600197
theorem B1159039 : Blo 459783 1159039 := bstep (se 1 (by rfl) ⟨869279, by rfl⟩ : syracuseStep 1159039 = 1738559) B1738559
theorem B1585097 : Blo 459783 1585097 := bstep (se 2 (by rfl) ⟨594411, by rfl⟩ : syracuseStep 1585097 = 1188823) B1188823
theorem B2339279 : Blo 459783 2339279 := bstep (se 1 (by rfl) ⟨1754459, by rfl⟩ : syracuseStep 2339279 = 3508919) B3508919
theorem B1553309 : Blo 459783 1553309 := bstep (se 3 (by rfl) ⟨291245, by rfl⟩ : syracuseStep 1553309 = 582491) B582491
theorem B143471573 : Blo 459783 143471573 := bstep (se 7 (by rfl) ⟨1681307, by rfl⟩ : syracuseStep 143471573 = 3362615) B3362615
theorem B833657 : Blo 459783 833657 := bstep (se 2 (by rfl) ⟨312621, by rfl⟩ : syracuseStep 833657 = 625243) B625243
theorem B16791785 : Blo 459783 16791785 := bstep (se 2 (by rfl) ⟨6296919, by rfl⟩ : syracuseStep 16791785 = 12593839) B12593839
theorem B2996669 : Blo 459783 2996669 := bstep (se 3 (by rfl) ⟨561875, by rfl⟩ : syracuseStep 2996669 = 1123751) B1123751
theorem B2210647 : Blo 459783 2210647 := bstep (se 1 (by rfl) ⟨1657985, by rfl⟩ : syracuseStep 2210647 = 3315971) B3315971
theorem B1555901 : Blo 459783 1555901 := bstep (se 3 (by rfl) ⟨291731, by rfl⟩ : syracuseStep 1555901 = 583463) B583463
theorem B4440055 : Blo 459783 4440055 := bstep (se 1 (by rfl) ⟨3330041, by rfl⟩ : syracuseStep 4440055 = 6660083) B6660083
theorem B6307865 : Blo 459783 6307865 := bstep (se 2 (by rfl) ⟨2365449, by rfl⟩ : syracuseStep 6307865 = 4730899) B4730899
theorem B6832421 : Blo 459783 6832421 := bstep (se 4 (by rfl) ⟨640539, by rfl⟩ : syracuseStep 6832421 = 1281079) B1281079
theorem B737819 : Blo 459783 737819 := bstep (se 1 (by rfl) ⟨553364, by rfl⟩ : syracuseStep 737819 = 1106729) B1106729
theorem B1753913 : Blo 459783 1753913 := bstep (se 2 (by rfl) ⟨657717, by rfl⟩ : syracuseStep 1753913 = 1315435) B1315435
theorem B2638889 : Blo 459783 2638889 := bstep (se 2 (by rfl) ⟨989583, by rfl⟩ : syracuseStep 2638889 = 1979167) B1979167
theorem B1557575 : Blo 459783 1557575 := bstep (se 1 (by rfl) ⟨1168181, by rfl⟩ : syracuseStep 1557575 = 2336363) B2336363
theorem B1754399 : Blo 459783 1754399 := bstep (se 1 (by rfl) ⟨1315799, by rfl⟩ : syracuseStep 1754399 = 2631599) B2631599
theorem B1328765 : Blo 459783 1328765 := bstep (se 3 (by rfl) ⟨249143, by rfl⟩ : syracuseStep 1328765 = 498287) B498287
theorem B13551731 : Blo 459783 13551731 := bstep (se 1 (by rfl) ⟨10163798, by rfl⟩ : syracuseStep 13551731 = 20327597) B20327597
theorem B3754601 : Blo 459783 3754601 := bstep (se 2 (by rfl) ⟨1407975, by rfl⟩ : syracuseStep 3754601 = 2815951) B2815951
theorem B3328775 : Blo 459783 3328775 := bstep (se 1 (by rfl) ⟨2496581, by rfl⟩ : syracuseStep 3328775 = 4993163) B4993163
theorem B1035017 : Blo 459783 1035017 := bstep (se 2 (by rfl) ⟨388131, by rfl⟩ : syracuseStep 1035017 = 776263) B776263
theorem B936827 : Blo 459783 936827 := bstep (se 1 (by rfl) ⟨702620, by rfl⟩ : syracuseStep 936827 = 1405241) B1405241
theorem B2968649 : Blo 459783 2968649 := bstep (se 2 (by rfl) ⟨1113243, by rfl⟩ : syracuseStep 2968649 = 2226487) B2226487
theorem B3951773 : Blo 459783 3951773 := bstep (se 3 (by rfl) ⟨740957, by rfl⟩ : syracuseStep 3951773 = 1481915) B1481915
theorem B1036007 : Blo 459783 1036007 := bstep (se 1 (by rfl) ⟨777005, by rfl⟩ : syracuseStep 1036007 = 1554011) B1554011
theorem B1757483 : Blo 459783 1757483 := bstep (se 1 (by rfl) ⟨1318112, by rfl⟩ : syracuseStep 1757483 = 2636225) B2636225
theorem B1036601 : Blo 459783 1036601 := bstep (se 2 (by rfl) ⟨388725, by rfl⟩ : syracuseStep 1036601 = 777451) B777451
theorem B5001635 : Blo 459783 5001635 := bstep (se 1 (by rfl) ⟨3751226, by rfl⟩ : syracuseStep 5001635 = 7502453) B7502453
theorem B15454799 : Blo 459783 15454799 := bstep (se 1 (by rfl) ⟨11591099, by rfl⟩ : syracuseStep 15454799 = 23182199) B23182199
theorem B1037051 : Blo 459783 1037051 := bstep (se 1 (by rfl) ⟨777788, by rfl⟩ : syracuseStep 1037051 = 1555577) B1555577
theorem B1168415 : Blo 459783 1168415 := bstep (se 1 (by rfl) ⟨876311, by rfl⟩ : syracuseStep 1168415 = 1752623) B1752623
theorem B8443187 : Blo 459783 8443187 := bstep (se 1 (by rfl) ⟨6332390, by rfl⟩ : syracuseStep 8443187 = 12664781) B12664781
theorem B1037735 : Blo 459783 1037735 := bstep (se 1 (by rfl) ⟨778301, by rfl⟩ : syracuseStep 1037735 = 1556603) B1556603
theorem B939431 : Blo 459783 939431 := bstep (se 1 (by rfl) ⟨704573, by rfl⟩ : syracuseStep 939431 = 1409147) B1409147
theorem B1037897 : Blo 459783 1037897 := bstep (se 2 (by rfl) ⟨389211, by rfl⟩ : syracuseStep 1037897 = 778423) B778423
theorem B939689 : Blo 459783 939689 := bstep (se 2 (by rfl) ⟨352383, by rfl⟩ : syracuseStep 939689 = 704767) B704767
theorem B9460415 : Blo 459783 9460415 := bstep (se 1 (by rfl) ⟨7095311, by rfl⟩ : syracuseStep 9460415 = 14190623) B14190623
theorem B1563623 : Blo 459783 1563623 := bstep (se 1 (by rfl) ⟨1172717, by rfl⟩ : syracuseStep 1563623 = 2345435) B2345435
theorem B1039571 : Blo 459783 1039571 := bstep (se 1 (by rfl) ⟨779678, by rfl⟩ : syracuseStep 1039571 = 1559357) B1559357
theorem B1039841 : Blo 459783 1039841 := bstep (se 2 (by rfl) ⟨389940, by rfl⟩ : syracuseStep 1039841 = 779881) B779881
theorem B777775 : Blo 459783 777775 := bstep (se 1 (by rfl) ⟨583331, by rfl⟩ : syracuseStep 777775 = 1166663) B1166663
theorem B9854585 : Blo 459783 9854585 := bstep (se 2 (by rfl) ⟨3695469, by rfl⟩ : syracuseStep 9854585 = 7390939) B7390939
theorem B1040327 : Blo 459783 1040327 := bstep (se 1 (by rfl) ⟨780245, by rfl⟩ : syracuseStep 1040327 = 1560491) B1560491
theorem B1105883 : Blo 459783 1105883 := bstep (se 1 (by rfl) ⟨829412, by rfl⟩ : syracuseStep 1105883 = 1658825) B1658825
theorem B778295 : Blo 459783 778295 := bstep (se 1 (by rfl) ⟨583721, by rfl⟩ : syracuseStep 778295 = 1167443) B1167443
theorem B4743463 : Blo 459783 4743463 := bstep (se 1 (by rfl) ⟨3557597, by rfl⟩ : syracuseStep 4743463 = 7115195) B7115195
theorem B1040903 : Blo 459783 1040903 := bstep (se 1 (by rfl) ⟨780677, by rfl⟩ : syracuseStep 1040903 = 1561355) B1561355
theorem B779071 : Blo 459783 779071 := bstep (se 1 (by rfl) ⟨584303, by rfl⟩ : syracuseStep 779071 = 1168607) B1168607
theorem B1172353 : Blo 459783 1172353 := bstep (se 2 (by rfl) ⟨439632, by rfl⟩ : syracuseStep 1172353 = 879265) B879265
theorem B1106939 : Blo 459783 1106939 := bstep (se 1 (by rfl) ⟨830204, by rfl⟩ : syracuseStep 1106939 = 1660409) B1660409
theorem B1041569 : Blo 459783 1041569 := bstep (se 2 (by rfl) ⟨390588, by rfl⟩ : syracuseStep 1041569 = 781177) B781177
theorem B1041875 : Blo 459783 1041875 := bstep (se 1 (by rfl) ⟨781406, by rfl⟩ : syracuseStep 1041875 = 1562813) B1562813
theorem B1042343 : Blo 459783 1042343 := bstep (se 1 (by rfl) ⟨781757, by rfl⟩ : syracuseStep 1042343 = 1563515) B1563515
theorem B1173487 : Blo 459783 1173487 := bstep (se 1 (by rfl) ⟨880115, by rfl⟩ : syracuseStep 1173487 = 1760231) B1760231
theorem B878779 : Blo 459783 878779 := bstep (se 1 (by rfl) ⟨659084, by rfl⟩ : syracuseStep 878779 = 1318169) B1318169
theorem B1043135 : Blo 459783 1043135 := bstep (se 1 (by rfl) ⟨782351, by rfl⟩ : syracuseStep 1043135 = 1564703) B1564703
theorem B1108775 : Blo 459783 1108775 := bstep (se 1 (by rfl) ⟨831581, by rfl⟩ : syracuseStep 1108775 = 1663163) B1663163
theorem B519259 : Blo 459783 519259 := bstep (se 1 (by rfl) ⟨389444, by rfl⟩ : syracuseStep 519259 = 778889) B778889
theorem B519835 : Blo 459783 519835 := bstep (se 1 (by rfl) ⟨389876, by rfl⟩ : syracuseStep 519835 = 779753) B779753
theorem B585407 : Blo 459783 585407 := bstep (se 1 (by rfl) ⟨439055, by rfl⟩ : syracuseStep 585407 = 878111) B878111
theorem B520303 : Blo 459783 520303 := bstep (se 1 (by rfl) ⟨390227, by rfl⟩ : syracuseStep 520303 = 780455) B780455
theorem B750055 : Blo 459783 750055 := bstep (se 1 (by rfl) ⟨562541, by rfl⟩ : syracuseStep 750055 = 1125083) B1125083
theorem B3503087 : Blo 459783 3503087 := bstep (se 1 (by rfl) ⟨2627315, by rfl⟩ : syracuseStep 3503087 = 5254631) B5254631
theorem B521599 : Blo 459783 521599 := bstep (se 1 (by rfl) ⟨391199, by rfl⟩ : syracuseStep 521599 = 782399) B782399
theorem B7468469 : Blo 459783 7468469 := bstep (se 5 (by rfl) ⟨350084, by rfl⟩ : syracuseStep 7468469 = 700169) B700169
theorem B2946557 : Blo 459783 2946557 := bstep (se 3 (by rfl) ⟨552479, by rfl⟩ : syracuseStep 2946557 = 1104959) B1104959
theorem B1112167 : Blo 459783 1112167 := bstep (se 1 (by rfl) ⟨834125, by rfl⟩ : syracuseStep 1112167 = 1668251) B1668251
theorem B5339627 : Blo 459783 5339627 := bstep (se 1 (by rfl) ⟨4004720, by rfl⟩ : syracuseStep 5339627 = 8009441) B8009441
theorem B16055333 : Blo 459783 16055333 := bstep (se 4 (by rfl) ⟨1505187, by rfl⟩ : syracuseStep 16055333 = 3010375) B3010375
theorem B5275043 : Blo 459783 5275043 := bstep (se 1 (by rfl) ⟨3956282, by rfl⟩ : syracuseStep 5275043 = 7912565) B7912565
theorem B34176455 : Blo 459783 34176455 := bstep (se 1 (by rfl) ⟨25632341, by rfl⟩ : syracuseStep 34176455 = 51264683) B51264683
theorem B2620937 : Blo 459783 2620937 := bstep (se 2 (by rfl) ⟨982851, by rfl⟩ : syracuseStep 2620937 = 1965703) B1965703
theorem B4980619 : Blo 459783 4980619 := bstep (se 1 (by rfl) ⟨3735464, by rfl⟩ : syracuseStep 4980619 = 7470929) B7470929
theorem B4554947 : Blo 459783 4554947 := bstep (se 1 (by rfl) ⟨3416210, by rfl⟩ : syracuseStep 4554947 = 6832421) B6832421
theorem B491879 : Blo 459783 491879 := bstep (se 1 (by rfl) ⟨368909, by rfl⟩ : syracuseStep 491879 = 737819) B737819
theorem B6324617 : Blo 459783 6324617 := bstep (se 2 (by rfl) ⟨2371731, by rfl⟩ : syracuseStep 6324617 = 4743463) B4743463
theorem B4719077 : Blo 459783 4719077 := bstep (se 4 (by rfl) ⟨442413, by rfl⟩ : syracuseStep 4719077 = 884827) B884827
theorem B15008287 : Blo 459783 15008287 := bstep (se 1 (by rfl) ⟨11256215, by rfl⟩ : syracuseStep 15008287 = 22512431) B22512431
theorem B2818871 : Blo 459783 2818871 := bstep (se 1 (by rfl) ⟨2114153, by rfl⟩ : syracuseStep 2818871 = 4228307) B4228307
theorem B459803 : Blo 459783 459803 := bstep (se 1 (by rfl) ⟨344852, by rfl⟩ : syracuseStep 459803 = 689705) B689705
theorem B13337693 : Blo 459783 13337693 := bstep (se 3 (by rfl) ⟨2500817, by rfl⟩ : syracuseStep 13337693 = 5001635) B5001635
theorem B5244425 : Blo 459783 5244425 := bstep (se 2 (by rfl) ⟨1966659, by rfl⟩ : syracuseStep 5244425 = 3933319) B3933319
theorem B460519 : Blo 459783 460519 := bstep (se 1 (by rfl) ⟨345389, by rfl⟩ : syracuseStep 460519 = 690779) B690779
theorem B690011 : Blo 459783 690011 := bstep (se 1 (by rfl) ⟨517508, by rfl⟩ : syracuseStep 690011 = 1035017) B1035017
theorem B460635 : Blo 459783 460635 := bstep (se 1 (by rfl) ⟨345476, by rfl⟩ : syracuseStep 460635 = 690953) B690953
theorem B624551 : Blo 459783 624551 := bstep (se 1 (by rfl) ⟨468413, by rfl⟩ : syracuseStep 624551 = 936827) B936827
theorem B460795 : Blo 459783 460795 := bstep (se 1 (by rfl) ⟨345596, by rfl⟩ : syracuseStep 460795 = 691193) B691193
theorem B461127 : Blo 459783 461127 := bstep (se 1 (by rfl) ⟨345845, by rfl⟩ : syracuseStep 461127 = 691691) B691691
theorem B2034115 : Blo 459783 2034115 := bstep (se 1 (by rfl) ⟨1525586, by rfl⟩ : syracuseStep 2034115 = 3051173) B3051173
theorem B690671 : Blo 459783 690671 := bstep (se 1 (by rfl) ⟨518003, by rfl⟩ : syracuseStep 690671 = 1036007) B1036007
theorem B461567 : Blo 459783 461567 := bstep (se 1 (by rfl) ⟨346175, by rfl⟩ : syracuseStep 461567 = 692351) B692351
theorem B1444711 : Blo 459783 1444711 := bstep (se 1 (by rfl) ⟨1083533, by rfl⟩ : syracuseStep 1444711 = 2167067) B2167067
theorem B691067 : Blo 459783 691067 := bstep (se 1 (by rfl) ⟨518300, by rfl⟩ : syracuseStep 691067 = 1036601) B1036601
theorem B461851 : Blo 459783 461851 := bstep (se 1 (by rfl) ⟨346388, by rfl⟩ : syracuseStep 461851 = 692777) B692777
theorem B691367 : Blo 459783 691367 := bstep (se 1 (by rfl) ⟨518525, by rfl⟩ : syracuseStep 691367 = 1037051) B1037051
theorem B462015 : Blo 459783 462015 := bstep (se 1 (by rfl) ⟨346511, by rfl⟩ : syracuseStep 462015 = 693023) B693023
theorem B462127 : Blo 459783 462127 := bstep (se 1 (by rfl) ⟨346595, by rfl⟩ : syracuseStep 462127 = 693191) B693191
theorem B462319 : Blo 459783 462319 := bstep (se 1 (by rfl) ⟨346739, by rfl⟩ : syracuseStep 462319 = 693479) B693479
theorem B462335 : Blo 459783 462335 := bstep (se 1 (by rfl) ⟨346751, by rfl⟩ : syracuseStep 462335 = 693503) B693503
theorem B691823 : Blo 459783 691823 := bstep (se 1 (by rfl) ⟨518867, by rfl⟩ : syracuseStep 691823 = 1037735) B1037735
theorem B626287 : Blo 459783 626287 := bstep (se 1 (by rfl) ⟨469715, by rfl⟩ : syracuseStep 626287 = 939431) B939431
theorem B5901983 : Blo 459783 5901983 := bstep (se 1 (by rfl) ⟨4426487, by rfl⟩ : syracuseStep 5901983 = 8852975) B8852975
theorem B691931 : Blo 459783 691931 := bstep (se 1 (by rfl) ⟨518948, by rfl⟩ : syracuseStep 691931 = 1037897) B1037897
theorem B626459 : Blo 459783 626459 := bstep (se 1 (by rfl) ⟨469844, by rfl⟩ : syracuseStep 626459 = 939689) B939689
theorem B462703 : Blo 459783 462703 := bstep (se 1 (by rfl) ⟨347027, by rfl⟩ : syracuseStep 462703 = 694055) B694055
theorem B692345 : Blo 459783 692345 := bstep (se 2 (by rfl) ⟨259629, by rfl⟩ : syracuseStep 692345 = 519259) B519259
theorem B3543373 : Blo 459783 3543373 := bstep (se 3 (by rfl) ⟨664382, by rfl⟩ : syracuseStep 3543373 = 1328765) B1328765
theorem B463591 : Blo 459783 463591 := bstep (se 1 (by rfl) ⟨347693, by rfl⟩ : syracuseStep 463591 = 695387) B695387
theorem B693047 : Blo 459783 693047 := bstep (se 1 (by rfl) ⟨519785, by rfl⟩ : syracuseStep 693047 = 1039571) B1039571
theorem B693113 : Blo 459783 693113 := bstep (se 2 (by rfl) ⟨259917, by rfl⟩ : syracuseStep 693113 = 519835) B519835
theorem B693227 : Blo 459783 693227 := bstep (se 1 (by rfl) ⟨519920, by rfl⟩ : syracuseStep 693227 = 1039841) B1039841
theorem B693551 : Blo 459783 693551 := bstep (se 1 (by rfl) ⟨520163, by rfl⟩ : syracuseStep 693551 = 1040327) B1040327
theorem B3937693 : Blo 459783 3937693 := bstep (se 3 (by rfl) ⟨738317, by rfl⟩ : syracuseStep 3937693 = 1476635) B1476635
theorem B693737 : Blo 459783 693737 := bstep (se 2 (by rfl) ⟨260151, by rfl⟩ : syracuseStep 693737 = 520303) B520303
theorem B693935 : Blo 459783 693935 := bstep (se 1 (by rfl) ⟨520451, by rfl⟩ : syracuseStep 693935 = 1040903) B1040903
theorem B3151963 : Blo 459783 3151963 := bstep (se 1 (by rfl) ⟨2363972, by rfl⟩ : syracuseStep 3151963 = 4727945) B4727945
theorem B694379 : Blo 459783 694379 := bstep (se 1 (by rfl) ⟨520784, by rfl⟩ : syracuseStep 694379 = 1041569) B1041569
theorem B2955527 : Blo 459783 2955527 := bstep (se 1 (by rfl) ⟨2216645, by rfl⟩ : syracuseStep 2955527 = 4433291) B4433291
theorem B694583 : Blo 459783 694583 := bstep (se 1 (by rfl) ⟨520937, by rfl⟩ : syracuseStep 694583 = 1041875) B1041875
theorem B694895 : Blo 459783 694895 := bstep (se 1 (by rfl) ⟨521171, by rfl⟩ : syracuseStep 694895 = 1042343) B1042343
theorem B1186751 : Blo 459783 1186751 := bstep (se 1 (by rfl) ⟨890063, by rfl⟩ : syracuseStep 1186751 = 1780127) B1780127
theorem B695423 : Blo 459783 695423 := bstep (se 1 (by rfl) ⟨521567, by rfl⟩ : syracuseStep 695423 = 1043135) B1043135
theorem B695465 : Blo 459783 695465 := bstep (se 2 (by rfl) ⟨260799, by rfl⟩ : syracuseStep 695465 = 521599) B521599
theorem B2956733 : Blo 459783 2956733 := bstep (se 3 (by rfl) ⟨554387, by rfl⟩ : syracuseStep 2956733 = 1108775) B1108775
theorem B1056731 : Blo 459783 1056731 := bstep (se 1 (by rfl) ⟨792548, by rfl⟩ : syracuseStep 1056731 = 1585097) B1585097
theorem B1482889 : Blo 459783 1482889 := bstep (se 2 (by rfl) ⟨556083, by rfl⟩ : syracuseStep 1482889 = 1112167) B1112167
theorem B2335391 : Blo 459783 2335391 := bstep (se 1 (by rfl) ⟨1751543, by rfl⟩ : syracuseStep 2335391 = 3503087) B3503087
theorem B2630825 : Blo 459783 2630825 := bstep (se 2 (by rfl) ⟨986559, by rfl⟩ : syracuseStep 2630825 = 1973119) B1973119
theorem B3516695 : Blo 459783 3516695 := bstep (se 1 (by rfl) ⟨2637521, by rfl⟩ : syracuseStep 3516695 = 5275043) B5275043
theorem B22784303 : Blo 459783 22784303 := bstep (se 1 (by rfl) ⟨17088227, by rfl⟩ : syracuseStep 22784303 = 34176455) B34176455
theorem B1747291 : Blo 459783 1747291 := bstep (se 1 (by rfl) ⟨1310468, by rfl⟩ : syracuseStep 1747291 = 2620937) B2620937
theorem B4205243 : Blo 459783 4205243 := bstep (se 1 (by rfl) ⟨3153932, by rfl⟩ : syracuseStep 4205243 = 6307865) B6307865
theorem B1748249 : Blo 459783 1748249 := bstep (se 2 (by rfl) ⟨655593, by rfl⟩ : syracuseStep 1748249 = 1311187) B1311187
theorem B8892341 : Blo 459783 8892341 := bstep (se 5 (by rfl) ⟨416828, by rfl⟩ : syracuseStep 8892341 = 833657) B833657
theorem B3518639 : Blo 459783 3518639 := bstep (se 1 (by rfl) ⟨2638979, by rfl⟩ : syracuseStep 3518639 = 5277959) B5277959
theorem B2503067 : Blo 459783 2503067 := bstep (se 1 (by rfl) ⟨1877300, by rfl⟩ : syracuseStep 2503067 = 3754601) B3754601
theorem B1979099 : Blo 459783 1979099 := bstep (se 1 (by rfl) ⟨1484324, by rfl⟩ : syracuseStep 1979099 = 2968649) B2968649
theorem B2339603 : Blo 459783 2339603 := bstep (se 1 (by rfl) ⟨1754702, by rfl⟩ : syracuseStep 2339603 = 3509405) B3509405
theorem B2634515 : Blo 459783 2634515 := bstep (se 1 (by rfl) ⟨1975886, by rfl⟩ : syracuseStep 2634515 = 3951773) B3951773
theorem B14922791 : Blo 459783 14922791 := bstep (se 1 (by rfl) ⟨11192093, by rfl⟩ : syracuseStep 14922791 = 22384187) B22384187
theorem B1750511 : Blo 459783 1750511 := bstep (se 1 (by rfl) ⟨1312883, by rfl⟩ : syracuseStep 1750511 = 2625767) B2625767
theorem B10303199 : Blo 459783 10303199 := bstep (se 1 (by rfl) ⟨7727399, by rfl⟩ : syracuseStep 10303199 = 15454799) B15454799
theorem B1554335 : Blo 459783 1554335 := bstep (se 1 (by rfl) ⟨1165751, by rfl⟩ : syracuseStep 1554335 = 2331503) B2331503
theorem B833449 : Blo 459783 833449 := bstep (se 2 (by rfl) ⟨312543, by rfl⟩ : syracuseStep 833449 = 625087) B625087
theorem B1751483 : Blo 459783 1751483 := bstep (se 1 (by rfl) ⟨1313612, by rfl⟩ : syracuseStep 1751483 = 2627225) B2627225
theorem B1555415 : Blo 459783 1555415 := bstep (se 1 (by rfl) ⟨1166561, by rfl⟩ : syracuseStep 1555415 = 2333123) B2333123
theorem B6306943 : Blo 459783 6306943 := bstep (se 1 (by rfl) ⟨4730207, by rfl⟩ : syracuseStep 6306943 = 9460415) B9460415
theorem B6569723 : Blo 459783 6569723 := bstep (se 1 (by rfl) ⟨4927292, by rfl⟩ : syracuseStep 6569723 = 9854585) B9854585
theorem B737255 : Blo 459783 737255 := bstep (se 1 (by rfl) ⟨552941, by rfl⟩ : syracuseStep 737255 = 1105883) B1105883
theorem B1000073 : Blo 459783 1000073 := bstep (se 2 (by rfl) ⟨375027, by rfl⟩ : syracuseStep 1000073 = 750055) B750055
theorem B737959 : Blo 459783 737959 := bstep (se 1 (by rfl) ⟨553469, by rfl⟩ : syracuseStep 737959 = 1106939) B1106939
theorem B1164415 : Blo 459783 1164415 := bstep (se 1 (by rfl) ⟨873311, by rfl⟩ : syracuseStep 1164415 = 1746623) B1746623
theorem B1558223 : Blo 459783 1558223 := bstep (se 1 (by rfl) ⟨1168667, by rfl⟩ : syracuseStep 1558223 = 2337335) B2337335
theorem B1559519 : Blo 459783 1559519 := bstep (se 1 (by rfl) ⟨1169639, by rfl⟩ : syracuseStep 1559519 = 2339279) B2339279
theorem B1035539 : Blo 459783 1035539 := bstep (se 1 (by rfl) ⟨776654, by rfl⟩ : syracuseStep 1035539 = 1553309) B1553309
theorem B11194523 : Blo 459783 11194523 := bstep (se 1 (by rfl) ⟨8395892, by rfl⟩ : syracuseStep 11194523 = 16791785) B16791785
theorem B3559751 : Blo 459783 3559751 := bstep (se 1 (by rfl) ⟨2669813, by rfl⟩ : syracuseStep 3559751 = 5339627) B5339627
theorem B1561085 : Blo 459783 1561085 := bstep (se 3 (by rfl) ⟨292703, by rfl⟩ : syracuseStep 1561085 = 585407) B585407
theorem B1757801 : Blo 459783 1757801 := bstep (se 2 (by rfl) ⟨659175, by rfl⟩ : syracuseStep 1757801 = 1318351) B1318351
theorem B6181541 : Blo 459783 6181541 := bstep (se 4 (by rfl) ⟨579519, by rfl⟩ : syracuseStep 6181541 = 1159039) B1159039
theorem B10703555 : Blo 459783 10703555 := bstep (se 1 (by rfl) ⟨8027666, by rfl⟩ : syracuseStep 10703555 = 16055333) B16055333
theorem B1037033 : Blo 459783 1037033 := bstep (se 2 (by rfl) ⟨388887, by rfl⟩ : syracuseStep 1037033 = 777775) B777775
theorem B1037267 : Blo 459783 1037267 := bstep (se 1 (by rfl) ⟨777950, by rfl⟩ : syracuseStep 1037267 = 1555901) B1555901
theorem B6640825 : Blo 459783 6640825 := bstep (se 2 (by rfl) ⟨2490309, by rfl⟩ : syracuseStep 6640825 = 4980619) B4980619
theorem B5920073 : Blo 459783 5920073 := bstep (se 2 (by rfl) ⟨2220027, by rfl⟩ : syracuseStep 5920073 = 4440055) B4440055
theorem B1169275 : Blo 459783 1169275 := bstep (se 1 (by rfl) ⟨876956, by rfl⟩ : syracuseStep 1169275 = 1753913) B1753913
theorem B1759259 : Blo 459783 1759259 := bstep (se 1 (by rfl) ⟨1319444, by rfl⟩ : syracuseStep 1759259 = 2638889) B2638889
theorem B1038383 : Blo 459783 1038383 := bstep (se 1 (by rfl) ⟨778787, by rfl⟩ : syracuseStep 1038383 = 1557575) B1557575
theorem B1169599 : Blo 459783 1169599 := bstep (se 1 (by rfl) ⟨877199, by rfl⟩ : syracuseStep 1169599 = 1754399) B1754399
theorem B1038761 : Blo 459783 1038761 := bstep (se 2 (by rfl) ⟨389535, by rfl⟩ : syracuseStep 1038761 = 779071) B779071
theorem B1563137 : Blo 459783 1563137 := bstep (se 2 (by rfl) ⟨586176, by rfl⟩ : syracuseStep 1563137 = 1172353) B1172353
theorem B2808361 : Blo 459783 2808361 := bstep (se 2 (by rfl) ⟨1053135, by rfl⟩ : syracuseStep 2808361 = 2106271) B2106271
theorem B9034487 : Blo 459783 9034487 := bstep (se 1 (by rfl) ⟨6775865, by rfl⟩ : syracuseStep 9034487 = 13551731) B13551731
theorem B2219183 : Blo 459783 2219183 := bstep (se 1 (by rfl) ⟨1664387, by rfl⟩ : syracuseStep 2219183 = 3328775) B3328775
theorem B1564649 : Blo 459783 1564649 := bstep (se 2 (by rfl) ⟨586743, by rfl⟩ : syracuseStep 1564649 = 1173487) B1173487
theorem B1171655 : Blo 459783 1171655 := bstep (se 1 (by rfl) ⟨878741, by rfl⟩ : syracuseStep 1171655 = 1757483) B1757483
theorem B1171705 : Blo 459783 1171705 := bstep (se 2 (by rfl) ⟨439389, by rfl⟩ : syracuseStep 1171705 = 878779) B878779
theorem B778943 : Blo 459783 778943 := bstep (se 1 (by rfl) ⟨584207, by rfl⟩ : syracuseStep 778943 = 1168415) B1168415
theorem B5628791 : Blo 459783 5628791 := bstep (se 1 (by rfl) ⟨4221593, by rfl⟩ : syracuseStep 5628791 = 8443187) B8443187
theorem B3499199 : Blo 459783 3499199 := bstep (se 1 (by rfl) ⟨2624399, by rfl⟩ : syracuseStep 3499199 = 5248799) B5248799
theorem B7890695 : Blo 459783 7890695 := bstep (se 1 (by rfl) ⟨5918021, by rfl⟩ : syracuseStep 7890695 = 11836043) B11836043
theorem B1042415 : Blo 459783 1042415 := bstep (se 1 (by rfl) ⟨781811, by rfl⟩ : syracuseStep 1042415 = 1563623) B1563623
theorem B879007 : Blo 459783 879007 := bstep (se 1 (by rfl) ⟨659255, by rfl⟩ : syracuseStep 879007 = 1318511) B1318511
theorem B518863 : Blo 459783 518863 := bstep (se 1 (by rfl) ⟨389147, by rfl⟩ : syracuseStep 518863 = 778295) B778295
theorem B879311 : Blo 459783 879311 := bstep (se 1 (by rfl) ⟨659483, by rfl⟩ : syracuseStep 879311 = 1318967) B1318967
theorem B5272127 : Blo 459783 5272127 := bstep (se 1 (by rfl) ⟨3954095, by rfl⟩ : syracuseStep 5272127 = 7908191) B7908191
theorem B5600087 : Blo 459783 5600087 := bstep (se 1 (by rfl) ⟨4200065, by rfl⟩ : syracuseStep 5600087 = 8400131) B8400131
theorem B95647715 : Blo 459783 95647715 := bstep (se 1 (by rfl) ⟨71735786, by rfl⟩ : syracuseStep 95647715 = 143471573) B143471573
theorem B4978979 : Blo 459783 4978979 := bstep (se 1 (by rfl) ⟨3734234, by rfl⟩ : syracuseStep 4978979 = 7468469) B7468469
theorem B1964371 : Blo 459783 1964371 := bstep (se 1 (by rfl) ⟨1473278, by rfl⟩ : syracuseStep 1964371 = 2946557) B2946557
theorem B2947529 : Blo 459783 2947529 := bstep (se 2 (by rfl) ⟨1105323, by rfl⟩ : syracuseStep 2947529 = 2210647) B2210647
theorem B1997779 : Blo 459783 1997779 := bstep (se 1 (by rfl) ⟨1498334, by rfl⟩ : syracuseStep 1997779 = 2996669) B2996669
theorem B3505517 : Blo 459783 3505517 := bstep (se 3 (by rfl) ⟨657284, by rfl⟩ : syracuseStep 3505517 = 1314569) B1314569
theorem B3146051 : Blo 459783 3146051 := bstep (se 1 (by rfl) ⟨2359538, by rfl⟩ : syracuseStep 3146051 = 4719077) B4719077
theorem B983945 : Blo 459783 983945 := bstep (se 2 (by rfl) ⟨368979, by rfl⟩ : syracuseStep 983945 = 737959) B737959
theorem B1311677 : Blo 459783 1311677 := bstep (se 3 (by rfl) ⟨245939, by rfl⟩ : syracuseStep 1311677 = 491879) B491879
theorem B460007 : Blo 459783 460007 := bstep (se 1 (by rfl) ⟨345005, by rfl⟩ : syracuseStep 460007 = 690011) B690011
theorem B460447 : Blo 459783 460447 := bstep (se 1 (by rfl) ⟨345335, by rfl⟩ : syracuseStep 460447 = 690671) B690671
theorem B460711 : Blo 459783 460711 := bstep (se 1 (by rfl) ⟨345533, by rfl⟩ : syracuseStep 460711 = 691067) B691067
theorem B460911 : Blo 459783 460911 := bstep (se 1 (by rfl) ⟨345683, by rfl⟩ : syracuseStep 460911 = 691367) B691367
theorem B690359 : Blo 459783 690359 := bstep (se 1 (by rfl) ⟨517769, by rfl⟩ : syracuseStep 690359 = 1035539) B1035539
theorem B461215 : Blo 459783 461215 := bstep (se 1 (by rfl) ⟨345911, by rfl⟩ : syracuseStep 461215 = 691823) B691823
theorem B3934655 : Blo 459783 3934655 := bstep (se 1 (by rfl) ⟨2950991, by rfl⟩ : syracuseStep 3934655 = 5901983) B5901983
theorem B461287 : Blo 459783 461287 := bstep (se 1 (by rfl) ⟨345965, by rfl⟩ : syracuseStep 461287 = 691931) B691931
theorem B461563 : Blo 459783 461563 := bstep (se 1 (by rfl) ⟨346172, by rfl⟩ : syracuseStep 461563 = 692345) B692345
theorem B2329721 : Blo 459783 2329721 := bstep (se 2 (by rfl) ⟨873645, by rfl⟩ : syracuseStep 2329721 = 1747291) B1747291
theorem B691355 : Blo 459783 691355 := bstep (se 1 (by rfl) ⟨518516, by rfl⟩ : syracuseStep 691355 = 1037033) B1037033
theorem B462031 : Blo 459783 462031 := bstep (se 1 (by rfl) ⟨346523, by rfl⟩ : syracuseStep 462031 = 693047) B693047
theorem B462075 : Blo 459783 462075 := bstep (se 1 (by rfl) ⟨346556, by rfl⟩ : syracuseStep 462075 = 693113) B693113
theorem B691511 : Blo 459783 691511 := bstep (se 1 (by rfl) ⟨518633, by rfl⟩ : syracuseStep 691511 = 1037267) B1037267
theorem B462151 : Blo 459783 462151 := bstep (se 1 (by rfl) ⟨346613, by rfl⟩ : syracuseStep 462151 = 693227) B693227
theorem B462367 : Blo 459783 462367 := bstep (se 1 (by rfl) ⟨346775, by rfl⟩ : syracuseStep 462367 = 693551) B693551
theorem B691817 : Blo 459783 691817 := bstep (se 2 (by rfl) ⟨259431, by rfl⟩ : syracuseStep 691817 = 518863) B518863
theorem B462491 : Blo 459783 462491 := bstep (se 1 (by rfl) ⟨346868, by rfl⟩ : syracuseStep 462491 = 693737) B693737
theorem B462623 : Blo 459783 462623 := bstep (se 1 (by rfl) ⟨346967, by rfl⟩ : syracuseStep 462623 = 693935) B693935
theorem B692255 : Blo 459783 692255 := bstep (se 1 (by rfl) ⟨519191, by rfl⟩ : syracuseStep 692255 = 1038383) B1038383
theorem B462919 : Blo 459783 462919 := bstep (se 1 (by rfl) ⟨347189, by rfl⟩ : syracuseStep 462919 = 694379) B694379
theorem B1970351 : Blo 459783 1970351 := bstep (se 1 (by rfl) ⟨1477763, by rfl⟩ : syracuseStep 1970351 = 2955527) B2955527
theorem B463055 : Blo 459783 463055 := bstep (se 1 (by rfl) ⟨347291, by rfl⟩ : syracuseStep 463055 = 694583) B694583
theorem B692507 : Blo 459783 692507 := bstep (se 1 (by rfl) ⟨519380, by rfl⟩ : syracuseStep 692507 = 1038761) B1038761
theorem B463263 : Blo 459783 463263 := bstep (se 1 (by rfl) ⟨347447, by rfl⟩ : syracuseStep 463263 = 694895) B694895
theorem B791167 : Blo 459783 791167 := bstep (se 1 (by rfl) ⟨593375, by rfl⟩ : syracuseStep 791167 = 1186751) B1186751
theorem B463615 : Blo 459783 463615 := bstep (se 1 (by rfl) ⟨347711, by rfl⟩ : syracuseStep 463615 = 695423) B695423
theorem B463643 : Blo 459783 463643 := bstep (se 1 (by rfl) ⟨347732, by rfl⟩ : syracuseStep 463643 = 695465) B695465
theorem B1479455 : Blo 459783 1479455 := bstep (se 1 (by rfl) ⟨1109591, by rfl⟩ : syracuseStep 1479455 = 2219183) B2219183
theorem B1971155 : Blo 459783 1971155 := bstep (se 1 (by rfl) ⟨1478366, by rfl⟩ : syracuseStep 1971155 = 2956733) B2956733
theorem B4724497 : Blo 459783 4724497 := bstep (se 2 (by rfl) ⟨1771686, by rfl⟩ : syracuseStep 4724497 = 3543373) B3543373
theorem B2332799 : Blo 459783 2332799 := bstep (se 1 (by rfl) ⟨1749599, by rfl⟩ : syracuseStep 2332799 = 3499199) B3499199
theorem B694943 : Blo 459783 694943 := bstep (se 1 (by rfl) ⟨521207, by rfl⟩ : syracuseStep 694943 = 1042415) B1042415
theorem B8854433 : Blo 459783 8854433 := bstep (se 2 (by rfl) ⟨3320412, by rfl⟩ : syracuseStep 8854433 = 6640825) B6640825
theorem B5250257 : Blo 459783 5250257 := bstep (se 2 (by rfl) ⟨1968846, by rfl⟩ : syracuseStep 5250257 = 3937693) B3937693
theorem B4202617 : Blo 459783 4202617 := bstep (se 2 (by rfl) ⟨1575981, by rfl⟩ : syracuseStep 4202617 = 3151963) B3151963
theorem B3514751 : Blo 459783 3514751 := bstep (se 1 (by rfl) ⟨2636063, by rfl⟩ : syracuseStep 3514751 = 5272127) B5272127
theorem B1319399 : Blo 459783 1319399 := bstep (se 1 (by rfl) ⟨989549, by rfl⟩ : syracuseStep 1319399 = 1979099) B1979099
theorem B3744481 : Blo 459783 3744481 := bstep (se 2 (by rfl) ⟨1404180, by rfl⟩ : syracuseStep 3744481 = 2808361) B2808361
theorem B2663705 : Blo 459783 2663705 := bstep (se 2 (by rfl) ⟨998889, by rfl⟩ : syracuseStep 2663705 = 1997779) B1997779
theorem B43394453 : Blo 459783 43394453 := bstep (se 6 (by rfl) ⟨1017057, by rfl⟩ : syracuseStep 43394453 = 2034115) B2034115
theorem B3319319 : Blo 459783 3319319 := bstep (se 1 (by rfl) ⟨2489489, by rfl⟩ : syracuseStep 3319319 = 4978979) B4978979
theorem B2337011 : Blo 459783 2337011 := bstep (se 1 (by rfl) ⟨1752758, by rfl⟩ : syracuseStep 2337011 = 3505517) B3505517
theorem B1977185 : Blo 459783 1977185 := bstep (se 2 (by rfl) ⟨741444, by rfl⟩ : syracuseStep 1977185 = 1482889) B1482889
theorem B666715 : Blo 459783 666715 := bstep (se 1 (by rfl) ⟨500036, by rfl⟩ : syracuseStep 666715 = 1000073) B1000073
theorem B1879247 : Blo 459783 1879247 := bstep (se 1 (by rfl) ⟨1409435, by rfl⟩ : syracuseStep 1879247 = 2818871) B2818871
theorem B8891795 : Blo 459783 8891795 := bstep (se 1 (by rfl) ⟨6668846, by rfl⟩ : syracuseStep 8891795 = 13337693) B13337693
theorem B1552553 : Blo 459783 1552553 := bstep (se 2 (by rfl) ⟨582207, by rfl⟩ : syracuseStep 1552553 = 1164415) B1164415
theorem B2373167 : Blo 459783 2373167 := bstep (se 1 (by rfl) ⟨1779875, by rfl⟩ : syracuseStep 2373167 = 3559751) B3559751
theorem B3946715 : Blo 459783 3946715 := bstep (se 1 (by rfl) ⟨2960036, by rfl⟩ : syracuseStep 3946715 = 5920073) B5920073
theorem B835049 : Blo 459783 835049 := bstep (se 2 (by rfl) ⟨313143, by rfl⟩ : syracuseStep 835049 = 626287) B626287
theorem B1556927 : Blo 459783 1556927 := bstep (se 1 (by rfl) ⟨1167695, by rfl⟩ : syracuseStep 1556927 = 2335391) B2335391
theorem B3752527 : Blo 459783 3752527 := bstep (se 1 (by rfl) ⟨2814395, by rfl⟩ : syracuseStep 3752527 = 5628791) B5628791
theorem B1753883 : Blo 459783 1753883 := bstep (se 1 (by rfl) ⟨1315412, by rfl⟩ : syracuseStep 1753883 = 2630825) B2630825
theorem B5260463 : Blo 459783 5260463 := bstep (se 1 (by rfl) ⟨3945347, by rfl⟩ : syracuseStep 5260463 = 7890695) B7890695
theorem B2344463 : Blo 459783 2344463 := bstep (se 1 (by rfl) ⟨1758347, by rfl⟩ : syracuseStep 2344463 = 3516695) B3516695
theorem B15189535 : Blo 459783 15189535 := bstep (se 1 (by rfl) ⟨11392151, by rfl⟩ : syracuseStep 15189535 = 22784303) B22784303
theorem B2803495 : Blo 459783 2803495 := bstep (se 1 (by rfl) ⟨2102621, by rfl⟩ : syracuseStep 2803495 = 4205243) B4205243
theorem B1165499 : Blo 459783 1165499 := bstep (se 1 (by rfl) ⟨874124, by rfl⟩ : syracuseStep 1165499 = 1748249) B1748249
theorem B1559033 : Blo 459783 1559033 := bstep (se 2 (by rfl) ⟨584637, by rfl⟩ : syracuseStep 1559033 = 1169275) B1169275
theorem B2345759 : Blo 459783 2345759 := bstep (se 1 (by rfl) ⟨1759319, by rfl⟩ : syracuseStep 2345759 = 3518639) B3518639
theorem B1559465 : Blo 459783 1559465 := bstep (se 2 (by rfl) ⟨584799, by rfl⟩ : syracuseStep 1559465 = 1169599) B1169599
theorem B1559735 : Blo 459783 1559735 := bstep (se 1 (by rfl) ⟨1169801, by rfl⟩ : syracuseStep 1559735 = 2339603) B2339603
theorem B1756343 : Blo 459783 1756343 := bstep (se 1 (by rfl) ⟨1317257, by rfl⟩ : syracuseStep 1756343 = 2634515) B2634515
theorem B9948527 : Blo 459783 9948527 := bstep (se 1 (by rfl) ⟨7461395, by rfl⟩ : syracuseStep 9948527 = 14922791) B14922791
theorem B1167007 : Blo 459783 1167007 := bstep (se 1 (by rfl) ⟨875255, by rfl⟩ : syracuseStep 1167007 = 1750511) B1750511
theorem B6868799 : Blo 459783 6868799 := bstep (se 1 (by rfl) ⟨5151599, by rfl⟩ : syracuseStep 6868799 = 10303199) B10303199
theorem B1036223 : Blo 459783 1036223 := bstep (se 1 (by rfl) ⟨777167, by rfl⟩ : syracuseStep 1036223 = 1554335) B1554335
theorem B8409257 : Blo 459783 8409257 := bstep (se 2 (by rfl) ⟨3153471, by rfl⟩ : syracuseStep 8409257 = 6306943) B6306943
theorem B1167655 : Blo 459783 1167655 := bstep (se 1 (by rfl) ⟨875741, by rfl⟩ : syracuseStep 1167655 = 1751483) B1751483
theorem B1036943 : Blo 459783 1036943 := bstep (se 1 (by rfl) ⟨777707, by rfl⟩ : syracuseStep 1036943 = 1555415) B1555415
theorem B4379815 : Blo 459783 4379815 := bstep (se 1 (by rfl) ⟨3284861, by rfl⟩ : syracuseStep 4379815 = 6569723) B6569723
theorem B3036631 : Blo 459783 3036631 := bstep (se 1 (by rfl) ⟨2277473, by rfl⟩ : syracuseStep 3036631 = 4554947) B4554947
theorem B4216411 : Blo 459783 4216411 := bstep (se 1 (by rfl) ⟨3162308, by rfl⟩ : syracuseStep 4216411 = 6324617) B6324617
theorem B1562273 : Blo 459783 1562273 := bstep (se 2 (by rfl) ⟨585852, by rfl⟩ : syracuseStep 1562273 = 1171705) B1171705
theorem B20011049 : Blo 459783 20011049 := bstep (se 2 (by rfl) ⟨7504143, by rfl⟩ : syracuseStep 20011049 = 15008287) B15008287
theorem B3496283 : Blo 459783 3496283 := bstep (se 1 (by rfl) ⟨2622212, by rfl⟩ : syracuseStep 3496283 = 5244425) B5244425
theorem B6674845 : Blo 459783 6674845 := bstep (se 3 (by rfl) ⟨1251533, by rfl⟩ : syracuseStep 6674845 = 2503067) B2503067
theorem B1038815 : Blo 459783 1038815 := bstep (se 1 (by rfl) ⟨779111, by rfl⟩ : syracuseStep 1038815 = 1558223) B1558223
theorem B1039679 : Blo 459783 1039679 := bstep (se 1 (by rfl) ⟨779759, by rfl⟩ : syracuseStep 1039679 = 1559519) B1559519
theorem B7463015 : Blo 459783 7463015 := bstep (se 1 (by rfl) ⟨5597261, by rfl⟩ : syracuseStep 7463015 = 11194523) B11194523
theorem B1040723 : Blo 459783 1040723 := bstep (se 1 (by rfl) ⟨780542, by rfl⟩ : syracuseStep 1040723 = 1561085) B1561085
theorem B1171867 : Blo 459783 1171867 := bstep (se 1 (by rfl) ⟨878900, by rfl⟩ : syracuseStep 1171867 = 1757801) B1757801
theorem B4121027 : Blo 459783 4121027 := bstep (se 1 (by rfl) ⟨3090770, by rfl⟩ : syracuseStep 4121027 = 6181541) B6181541
theorem B7135703 : Blo 459783 7135703 := bstep (se 1 (by rfl) ⟨5351777, by rfl⟩ : syracuseStep 7135703 = 10703555) B10703555
theorem B1172009 : Blo 459783 1172009 := bstep (se 2 (by rfl) ⟨439503, by rfl⟩ : syracuseStep 1172009 = 879007) B879007
theorem B1926281 : Blo 459783 1926281 := bstep (se 2 (by rfl) ⟨722355, by rfl⟩ : syracuseStep 1926281 = 1444711) B1444711
theorem B1172839 : Blo 459783 1172839 := bstep (se 1 (by rfl) ⟨879629, by rfl⟩ : syracuseStep 1172839 = 1759259) B1759259
theorem B1042091 : Blo 459783 1042091 := bstep (se 1 (by rfl) ⟨781568, by rfl⟩ : syracuseStep 1042091 = 1563137) B1563137
theorem B6022991 : Blo 459783 6022991 := bstep (se 1 (by rfl) ⟨4517243, by rfl⟩ : syracuseStep 6022991 = 9034487) B9034487
theorem B1665469 : Blo 459783 1665469 := bstep (se 3 (by rfl) ⟨312275, by rfl⟩ : syracuseStep 1665469 = 624551) B624551
theorem B1043099 : Blo 459783 1043099 := bstep (se 1 (by rfl) ⟨782324, by rfl⟩ : syracuseStep 1043099 = 1564649) B1564649
theorem B781103 : Blo 459783 781103 := bstep (se 1 (by rfl) ⟨585827, by rfl⟩ : syracuseStep 781103 = 1171655) B1171655
theorem B519295 : Blo 459783 519295 := bstep (se 1 (by rfl) ⟨389471, by rfl⟩ : syracuseStep 519295 = 778943) B778943
theorem B7860077 : Blo 459783 7860077 := bstep (se 3 (by rfl) ⟨1473764, by rfl⟩ : syracuseStep 7860077 = 2947529) B2947529
theorem B586207 : Blo 459783 586207 := bstep (se 1 (by rfl) ⟨439655, by rfl⟩ : syracuseStep 586207 = 879311) B879311
theorem B1111265 : Blo 459783 1111265 := bstep (se 2 (by rfl) ⟨416724, by rfl⟩ : syracuseStep 1111265 = 833449) B833449
theorem B5928227 : Blo 459783 5928227 := bstep (se 1 (by rfl) ⟨4446170, by rfl⟩ : syracuseStep 5928227 = 8892341) B8892341
theorem B2619161 : Blo 459783 2619161 := bstep (se 2 (by rfl) ⟨982185, by rfl⟩ : syracuseStep 2619161 = 1964371) B1964371
theorem B3733391 : Blo 459783 3733391 := bstep (se 1 (by rfl) ⟨2800043, by rfl⟩ : syracuseStep 3733391 = 5600087) B5600087
theorem B63765143 : Blo 459783 63765143 := bstep (se 1 (by rfl) ⟨47823857, by rfl⟩ : syracuseStep 63765143 = 95647715) B95647715
theorem B1670557 : Blo 459783 1670557 := bstep (se 3 (by rfl) ⟨313229, by rfl⟩ : syracuseStep 1670557 = 626459) B626459
theorem B11271797 : Blo 459783 11271797 := bstep (se 5 (by rfl) ⟨528365, by rfl⟩ : syracuseStep 11271797 = 1056731) B1056731
theorem B491503 : Blo 459783 491503 := bstep (se 1 (by rfl) ⟨368627, by rfl⟩ : syracuseStep 491503 = 737255) B737255
theorem B5603489 : Blo 459783 5603489 := bstep (se 2 (by rfl) ⟨2101308, by rfl⟩ : syracuseStep 5603489 = 4202617) B4202617
theorem B3506975 : Blo 459783 3506975 := bstep (se 1 (by rfl) ⟨2630231, by rfl⟩ : syracuseStep 3506975 = 5260463) B5260463
theorem B8389469 : Blo 459783 8389469 := bstep (se 3 (by rfl) ⟨1573025, by rfl⟩ : syracuseStep 8389469 = 3146051) B3146051
theorem B460239 : Blo 459783 460239 := bstep (se 1 (by rfl) ⟨345179, by rfl⟩ : syracuseStep 460239 = 690359) B690359
theorem B2623103 : Blo 459783 2623103 := bstep (se 1 (by rfl) ⟨1967327, by rfl⟩ : syracuseStep 2623103 = 3934655) B3934655
theorem B460903 : Blo 459783 460903 := bstep (se 1 (by rfl) ⟨345677, by rfl⟩ : syracuseStep 460903 = 691355) B691355
theorem B461007 : Blo 459783 461007 := bstep (se 1 (by rfl) ⟨345755, by rfl⟩ : syracuseStep 461007 = 691511) B691511
theorem B2623853 : Blo 459783 2623853 := bstep (se 3 (by rfl) ⟨491972, by rfl⟩ : syracuseStep 2623853 = 983945) B983945
theorem B3737993 : Blo 459783 3737993 := bstep (se 2 (by rfl) ⟨1401747, by rfl⟩ : syracuseStep 3737993 = 2803495) B2803495
theorem B461211 : Blo 459783 461211 := bstep (se 1 (by rfl) ⟨345908, by rfl⟩ : syracuseStep 461211 = 691817) B691817
theorem B690815 : Blo 459783 690815 := bstep (se 1 (by rfl) ⟨518111, by rfl⟩ : syracuseStep 690815 = 1036223) B1036223
theorem B461503 : Blo 459783 461503 := bstep (se 1 (by rfl) ⟨346127, by rfl⟩ : syracuseStep 461503 = 692255) B692255
theorem B5606171 : Blo 459783 5606171 := bstep (se 1 (by rfl) ⟨4204628, by rfl⟩ : syracuseStep 5606171 = 8409257) B8409257
theorem B1313567 : Blo 459783 1313567 := bstep (se 1 (by rfl) ⟨985175, by rfl⟩ : syracuseStep 1313567 = 1970351) B1970351
theorem B461671 : Blo 459783 461671 := bstep (se 1 (by rfl) ⟨346253, by rfl⟩ : syracuseStep 461671 = 692507) B692507
theorem B691295 : Blo 459783 691295 := bstep (se 1 (by rfl) ⟨518471, by rfl⟩ : syracuseStep 691295 = 1036943) B1036943
theorem B986303 : Blo 459783 986303 := bstep (se 1 (by rfl) ⟨739727, by rfl⟩ : syracuseStep 986303 = 1479455) B1479455
theorem B1314103 : Blo 459783 1314103 := bstep (se 1 (by rfl) ⟨985577, by rfl⟩ : syracuseStep 1314103 = 1971155) B1971155
theorem B13340699 : Blo 459783 13340699 := bstep (se 1 (by rfl) ⟨10005524, by rfl⟩ : syracuseStep 13340699 = 20011049) B20011049
theorem B888953 : Blo 459783 888953 := bstep (se 2 (by rfl) ⟨333357, by rfl⟩ : syracuseStep 888953 = 666715) B666715
theorem B692393 : Blo 459783 692393 := bstep (se 2 (by rfl) ⟨259647, by rfl⟩ : syracuseStep 692393 = 519295) B519295
theorem B2330855 : Blo 459783 2330855 := bstep (se 1 (by rfl) ⟨1748141, by rfl⟩ : syracuseStep 2330855 = 3496283) B3496283
theorem B692543 : Blo 459783 692543 := bstep (se 1 (by rfl) ⟨519407, by rfl⟩ : syracuseStep 692543 = 1038815) B1038815
theorem B463295 : Blo 459783 463295 := bstep (se 1 (by rfl) ⟨347471, by rfl⟩ : syracuseStep 463295 = 694943) B694943
theorem B5902955 : Blo 459783 5902955 := bstep (se 1 (by rfl) ⟨4427216, by rfl⟩ : syracuseStep 5902955 = 8854433) B8854433
theorem B693119 : Blo 459783 693119 := bstep (se 1 (by rfl) ⟨519839, by rfl⟩ : syracuseStep 693119 = 1039679) B1039679
theorem B693815 : Blo 459783 693815 := bstep (se 1 (by rfl) ⟨520361, by rfl⟩ : syracuseStep 693815 = 1040723) B1040723
theorem B4757135 : Blo 459783 4757135 := bstep (se 1 (by rfl) ⟨3567851, by rfl⟩ : syracuseStep 4757135 = 7135703) B7135703
theorem B1284187 : Blo 459783 1284187 := bstep (se 1 (by rfl) ⟨963140, by rfl⟩ : syracuseStep 1284187 = 1926281) B1926281
theorem B1054889 : Blo 459783 1054889 := bstep (se 2 (by rfl) ⟨395583, by rfl⟩ : syracuseStep 1054889 = 791167) B791167
theorem B1775803 : Blo 459783 1775803 := bstep (se 1 (by rfl) ⟨1331852, by rfl⟩ : syracuseStep 1775803 = 2663705) B2663705
theorem B694727 : Blo 459783 694727 := bstep (se 1 (by rfl) ⟨521045, by rfl⟩ : syracuseStep 694727 = 1042091) B1042091
theorem B695399 : Blo 459783 695399 := bstep (se 1 (by rfl) ⟨521549, by rfl⟩ : syracuseStep 695399 = 1043099) B1043099
theorem B1318123 : Blo 459783 1318123 := bstep (se 1 (by rfl) ⟨988592, by rfl⟩ : syracuseStep 1318123 = 1977185) B1977185
theorem B1252831 : Blo 459783 1252831 := bstep (se 1 (by rfl) ⟨939623, by rfl⟩ : syracuseStep 1252831 = 1879247) B1879247
theorem B81010853 : Blo 459783 81010853 := bstep (se 4 (by rfl) ⟨7594767, by rfl⟩ : syracuseStep 81010853 = 15189535) B15189535
theorem B1582111 : Blo 459783 1582111 := bstep (se 1 (by rfl) ⟨1186583, by rfl⟩ : syracuseStep 1582111 = 2373167) B2373167
theorem B1746107 : Blo 459783 1746107 := bstep (se 1 (by rfl) ⟨1309580, by rfl⟩ : syracuseStep 1746107 = 2619161) B2619161
theorem B2631143 : Blo 459783 2631143 := bstep (se 1 (by rfl) ⟨1973357, by rfl⟩ : syracuseStep 2631143 = 3946715) B3946715
theorem B42510095 : Blo 459783 42510095 := bstep (se 1 (by rfl) ⟨31882571, by rfl⟩ : syracuseStep 42510095 = 63765143) B63765143
theorem B7514531 : Blo 459783 7514531 := bstep (se 1 (by rfl) ⟨5635898, by rfl⟩ : syracuseStep 7514531 = 11271797) B11271797
theorem B4992641 : Blo 459783 4992641 := bstep (se 2 (by rfl) ⟨1872240, by rfl⟩ : syracuseStep 4992641 = 3744481) B3744481
theorem B1553147 : Blo 459783 1553147 := bstep (se 1 (by rfl) ⟨1164860, by rfl⟩ : syracuseStep 1553147 = 2329721) B2329721
theorem B6632351 : Blo 459783 6632351 := bstep (se 1 (by rfl) ⟨4974263, by rfl⟩ : syracuseStep 6632351 = 9948527) B9948527
theorem B1555199 : Blo 459783 1555199 := bstep (se 1 (by rfl) ⟨1166399, by rfl⟩ : syracuseStep 1555199 = 2332799) B2332799
theorem B1556009 : Blo 459783 1556009 := bstep (se 2 (by rfl) ⟨583503, by rfl⟩ : syracuseStep 1556009 = 1167007) B1167007
theorem B2343167 : Blo 459783 2343167 := bstep (se 1 (by rfl) ⟨1757375, by rfl⟩ : syracuseStep 2343167 = 3514751) B3514751
theorem B1556873 : Blo 459783 1556873 := bstep (se 2 (by rfl) ⟨583827, by rfl⟩ : syracuseStep 1556873 = 1167655) B1167655
theorem B2212879 : Blo 459783 2212879 := bstep (se 1 (by rfl) ⟨1659659, by rfl⟩ : syracuseStep 2212879 = 3319319) B3319319
theorem B4015327 : Blo 459783 4015327 := bstep (se 1 (by rfl) ⟨3011495, by rfl⟩ : syracuseStep 4015327 = 6022991) B6022991
theorem B1558007 : Blo 459783 1558007 := bstep (se 1 (by rfl) ⟨1168505, by rfl⟩ : syracuseStep 1558007 = 2337011) B2337011
theorem B4048841 : Blo 459783 4048841 := bstep (se 2 (by rfl) ⟨1518315, by rfl⟩ : syracuseStep 4048841 = 3036631) B3036631
theorem B5621881 : Blo 459783 5621881 := bstep (se 2 (by rfl) ⟨2108205, by rfl⟩ : syracuseStep 5621881 = 4216411) B4216411
theorem B1035035 : Blo 459783 1035035 := bstep (se 1 (by rfl) ⟨776276, by rfl⟩ : syracuseStep 1035035 = 1552553) B1552553
theorem B8899793 : Blo 459783 8899793 := bstep (se 2 (by rfl) ⟨3337422, by rfl⟩ : syracuseStep 8899793 = 6674845) B6674845
theorem B740843 : Blo 459783 740843 := bstep (se 1 (by rfl) ⟨555632, by rfl⟩ : syracuseStep 740843 = 1111265) B1111265
theorem B3952151 : Blo 459783 3952151 := bstep (se 1 (by rfl) ⟨2964113, by rfl⟩ : syracuseStep 3952151 = 5928227) B5928227
theorem B1037951 : Blo 459783 1037951 := bstep (se 1 (by rfl) ⟨778463, by rfl⟩ : syracuseStep 1037951 = 1556927) B1556927
theorem B1169255 : Blo 459783 1169255 := bstep (se 1 (by rfl) ⟨876941, by rfl⟩ : syracuseStep 1169255 = 1753883) B1753883
theorem B1562489 : Blo 459783 1562489 := bstep (se 2 (by rfl) ⟨585933, by rfl⟩ : syracuseStep 1562489 = 1171867) B1171867
theorem B874451 : Blo 459783 874451 := bstep (se 1 (by rfl) ⟨655838, by rfl⟩ : syracuseStep 874451 = 1311677) B1311677
theorem B5003369 : Blo 459783 5003369 := bstep (se 2 (by rfl) ⟨1876263, by rfl⟩ : syracuseStep 5003369 = 3752527) B3752527
theorem B1562975 : Blo 459783 1562975 := bstep (se 1 (by rfl) ⟨1172231, by rfl⟩ : syracuseStep 1562975 = 2344463) B2344463
theorem B776999 : Blo 459783 776999 := bstep (se 1 (by rfl) ⟨582749, by rfl⟩ : syracuseStep 776999 = 1165499) B1165499
theorem B1039355 : Blo 459783 1039355 := bstep (se 1 (by rfl) ⟨779516, by rfl⟩ : syracuseStep 1039355 = 1559033) B1559033
theorem B1563785 : Blo 459783 1563785 := bstep (se 2 (by rfl) ⟨586419, by rfl⟩ : syracuseStep 1563785 = 1172839) B1172839
theorem B1563839 : Blo 459783 1563839 := bstep (se 1 (by rfl) ⟨1172879, by rfl⟩ : syracuseStep 1563839 = 2345759) B2345759
theorem B1039643 : Blo 459783 1039643 := bstep (se 1 (by rfl) ⟨779732, by rfl⟩ : syracuseStep 1039643 = 1559465) B1559465
theorem B1039823 : Blo 459783 1039823 := bstep (se 1 (by rfl) ⟨779867, by rfl⟩ : syracuseStep 1039823 = 1559735) B1559735
theorem B1170895 : Blo 459783 1170895 := bstep (se 1 (by rfl) ⟨878171, by rfl⟩ : syracuseStep 1170895 = 1756343) B1756343
theorem B4579199 : Blo 459783 4579199 := bstep (se 1 (by rfl) ⟨3434399, by rfl⟩ : syracuseStep 4579199 = 6868799) B6868799
theorem B2220625 : Blo 459783 2220625 := bstep (se 2 (by rfl) ⟨832734, by rfl⟩ : syracuseStep 2220625 = 1665469) B1665469
theorem B1041515 : Blo 459783 1041515 := bstep (se 1 (by rfl) ⟨781136, by rfl⟩ : syracuseStep 1041515 = 1562273) B1562273
theorem B3500171 : Blo 459783 3500171 := bstep (se 1 (by rfl) ⟨2625128, by rfl⟩ : syracuseStep 3500171 = 5250257) B5250257
theorem B4975343 : Blo 459783 4975343 := bstep (se 1 (by rfl) ⟨3731507, by rfl⟩ : syracuseStep 4975343 = 7463015) B7463015
theorem B2747351 : Blo 459783 2747351 := bstep (se 1 (by rfl) ⟨2060513, by rfl⟩ : syracuseStep 2747351 = 4121027) B4121027
theorem B879599 : Blo 459783 879599 := bstep (se 1 (by rfl) ⟨659699, by rfl⟩ : syracuseStep 879599 = 1319399) B1319399
theorem B781339 : Blo 459783 781339 := bstep (se 1 (by rfl) ⟨586004, by rfl⟩ : syracuseStep 781339 = 1172009) B1172009
theorem B781609 : Blo 459783 781609 := bstep (se 2 (by rfl) ⟨293103, by rfl⟩ : syracuseStep 781609 = 586207) B586207
theorem B23359013 : Blo 459783 23359013 := bstep (se 4 (by rfl) ⟨2189907, by rfl⟩ : syracuseStep 23359013 = 4379815) B4379815
theorem B28929635 : Blo 459783 28929635 := bstep (se 1 (by rfl) ⟨21697226, by rfl⟩ : syracuseStep 28929635 = 43394453) B43394453
theorem B520735 : Blo 459783 520735 := bstep (se 1 (by rfl) ⟨390551, by rfl⟩ : syracuseStep 520735 = 781103) B781103
theorem B5927863 : Blo 459783 5927863 := bstep (se 1 (by rfl) ⟨4445897, by rfl⟩ : syracuseStep 5927863 = 8891795) B8891795
theorem B5240051 : Blo 459783 5240051 := bstep (se 1 (by rfl) ⟨3930038, by rfl⟩ : syracuseStep 5240051 = 7860077) B7860077
theorem B2488927 : Blo 459783 2488927 := bstep (se 1 (by rfl) ⟨1866695, by rfl⟩ : syracuseStep 2488927 = 3733391) B3733391
theorem B25197317 : Blo 459783 25197317 := bstep (se 4 (by rfl) ⟨2362248, by rfl⟩ : syracuseStep 25197317 = 4724497) B4724497
theorem B2227409 : Blo 459783 2227409 := bstep (se 2 (by rfl) ⟨835278, by rfl⟩ : syracuseStep 2227409 = 1670557) B1670557
theorem B556699 : Blo 459783 556699 := bstep (se 1 (by rfl) ⟨417524, by rfl⟩ : syracuseStep 556699 = 835049) B835049
theorem B655337 : Blo 459783 655337 := bstep (se 2 (by rfl) ⟨245751, by rfl⟩ : syracuseStep 655337 = 491503) B491503
theorem B3735659 : Blo 459783 3735659 := bstep (se 1 (by rfl) ⟨2801744, by rfl⟩ : syracuseStep 3735659 = 5603489) B5603489
theorem B2950505 : Blo 459783 2950505 := bstep (se 2 (by rfl) ⟨1106439, by rfl⟩ : syracuseStep 2950505 = 2212879) B2212879
theorem B460543 : Blo 459783 460543 := bstep (se 1 (by rfl) ⟨345407, by rfl⟩ : syracuseStep 460543 = 690815) B690815
theorem B690023 : Blo 459783 690023 := bstep (se 1 (by rfl) ⟨517517, by rfl⟩ : syracuseStep 690023 = 1035035) B1035035
theorem B3737447 : Blo 459783 3737447 := bstep (se 1 (by rfl) ⟨2803085, by rfl⟩ : syracuseStep 3737447 = 5606171) B5606171
theorem B460863 : Blo 459783 460863 := bstep (se 1 (by rfl) ⟨345647, by rfl⟩ : syracuseStep 460863 = 691295) B691295
theorem B5933195 : Blo 459783 5933195 := bstep (se 1 (by rfl) ⟨4449896, by rfl⟩ : syracuseStep 5933195 = 8899793) B8899793
theorem B493895 : Blo 459783 493895 := bstep (se 1 (by rfl) ⟨370421, by rfl⟩ : syracuseStep 493895 = 740843) B740843
theorem B461595 : Blo 459783 461595 := bstep (se 1 (by rfl) ⟨346196, by rfl⟩ : syracuseStep 461595 = 692393) B692393
theorem B461695 : Blo 459783 461695 := bstep (se 1 (by rfl) ⟨346271, by rfl⟩ : syracuseStep 461695 = 692543) B692543
theorem B3935303 : Blo 459783 3935303 := bstep (se 1 (by rfl) ⟨2951477, by rfl⟩ : syracuseStep 3935303 = 5902955) B5902955
theorem B462079 : Blo 459783 462079 := bstep (se 1 (by rfl) ⟨346559, by rfl⟩ : syracuseStep 462079 = 693119) B693119
theorem B462543 : Blo 459783 462543 := bstep (se 1 (by rfl) ⟨346907, by rfl⟩ : syracuseStep 462543 = 693815) B693815
theorem B691967 : Blo 459783 691967 := bstep (se 1 (by rfl) ⟨518975, by rfl⟩ : syracuseStep 691967 = 1037951) B1037951
theorem B463151 : Blo 459783 463151 := bstep (se 1 (by rfl) ⟨347363, by rfl⟩ : syracuseStep 463151 = 694727) B694727
theorem B692903 : Blo 459783 692903 := bstep (se 1 (by rfl) ⟨519677, by rfl⟩ : syracuseStep 692903 = 1039355) B1039355
theorem B463599 : Blo 459783 463599 := bstep (se 1 (by rfl) ⟨347699, by rfl⟩ : syracuseStep 463599 = 695399) B695399
theorem B693095 : Blo 459783 693095 := bstep (se 1 (by rfl) ⟨519821, by rfl⟩ : syracuseStep 693095 = 1039643) B1039643
theorem B693215 : Blo 459783 693215 := bstep (se 1 (by rfl) ⟨519911, by rfl⟩ : syracuseStep 693215 = 1039823) B1039823
theorem B3052799 : Blo 459783 3052799 := bstep (se 1 (by rfl) ⟨2289599, by rfl⟩ : syracuseStep 3052799 = 4579199) B4579199
theorem B54007235 : Blo 459783 54007235 := bstep (se 1 (by rfl) ⟨40505426, by rfl⟩ : syracuseStep 54007235 = 81010853) B81010853
theorem B694313 : Blo 459783 694313 := bstep (se 2 (by rfl) ⟨260367, by rfl⟩ : syracuseStep 694313 = 520735) B520735
theorem B694343 : Blo 459783 694343 := bstep (se 1 (by rfl) ⟨520757, by rfl⟩ : syracuseStep 694343 = 1041515) B1041515
theorem B9967981 : Blo 459783 9967981 := bstep (se 3 (by rfl) ⟨1868996, by rfl⟩ : syracuseStep 9967981 = 3737993) B3737993
theorem B7903817 : Blo 459783 7903817 := bstep (se 2 (by rfl) ⟨2963931, by rfl⟩ : syracuseStep 7903817 = 5927863) B5927863
theorem B2333447 : Blo 459783 2333447 := bstep (se 1 (by rfl) ⟨1750085, by rfl⟩ : syracuseStep 2333447 = 3500171) B3500171
theorem B3316895 : Blo 459783 3316895 := bstep (se 1 (by rfl) ⟨2487671, by rfl⟩ : syracuseStep 3316895 = 4975343) B4975343
theorem B15572675 : Blo 459783 15572675 := bstep (se 1 (by rfl) ⟨11679506, by rfl⟩ : syracuseStep 15572675 = 23359013) B23359013
theorem B1712249 : Blo 459783 1712249 := bstep (se 2 (by rfl) ⟨642093, by rfl⟩ : syracuseStep 1712249 = 1284187) B1284187
theorem B2367737 : Blo 459783 2367737 := bstep (se 2 (by rfl) ⟨887901, by rfl⟩ : syracuseStep 2367737 = 1775803) B1775803
theorem B2630141 : Blo 459783 2630141 := bstep (se 3 (by rfl) ⟨493151, by rfl⟩ : syracuseStep 2630141 = 986303) B986303
theorem B3318569 : Blo 459783 3318569 := bstep (se 2 (by rfl) ⟨1244463, by rfl⟩ : syracuseStep 3318569 = 2488927) B2488927
theorem B1484939 : Blo 459783 1484939 := bstep (se 1 (by rfl) ⟨1113704, by rfl⟩ : syracuseStep 1484939 = 2227409) B2227409
theorem B1747565 : Blo 459783 1747565 := bstep (se 3 (by rfl) ⟨327668, by rfl⟩ : syracuseStep 1747565 = 655337) B655337
theorem B2370541 : Blo 459783 2370541 := bstep (se 3 (by rfl) ⟨444476, by rfl⟩ : syracuseStep 2370541 = 888953) B888953
theorem B2337983 : Blo 459783 2337983 := bstep (se 1 (by rfl) ⟨1753487, by rfl⟩ : syracuseStep 2337983 = 3506975) B3506975
theorem B2960833 : Blo 459783 2960833 := bstep (se 2 (by rfl) ⟨1110312, by rfl⟩ : syracuseStep 2960833 = 2220625) B2220625
theorem B1748735 : Blo 459783 1748735 := bstep (se 1 (by rfl) ⟨1311551, by rfl⟩ : syracuseStep 1748735 = 2623103) B2623103
theorem B2699227 : Blo 459783 2699227 := bstep (se 1 (by rfl) ⟨2024420, by rfl⟩ : syracuseStep 2699227 = 4048841) B4048841
theorem B1749235 : Blo 459783 1749235 := bstep (se 1 (by rfl) ⟨1311926, by rfl⟩ : syracuseStep 1749235 = 2623853) B2623853
theorem B5353769 : Blo 459783 5353769 := bstep (se 2 (by rfl) ⟨2007663, by rfl⟩ : syracuseStep 5353769 = 4015327) B4015327
theorem B2634767 : Blo 459783 2634767 := bstep (se 1 (by rfl) ⟨1976075, by rfl⟩ : syracuseStep 2634767 = 3952151) B3952151
theorem B8893799 : Blo 459783 8893799 := bstep (se 1 (by rfl) ⟨6670349, by rfl⟩ : syracuseStep 8893799 = 13340699) B13340699
theorem B1553903 : Blo 459783 1553903 := bstep (se 1 (by rfl) ⟨1165427, by rfl⟩ : syracuseStep 1553903 = 2330855) B2330855
theorem B703259 : Blo 459783 703259 := bstep (se 1 (by rfl) ⟨527444, by rfl⟩ : syracuseStep 703259 = 1054889) B1054889
theorem B1752137 : Blo 459783 1752137 := bstep (se 2 (by rfl) ⟨657051, by rfl⟩ : syracuseStep 1752137 = 1314103) B1314103
theorem B8437925 : Blo 459783 8437925 := bstep (se 4 (by rfl) ⟨791055, by rfl⟩ : syracuseStep 8437925 = 1582111) B1582111
theorem B1164071 : Blo 459783 1164071 := bstep (se 1 (by rfl) ⟨873053, by rfl⟩ : syracuseStep 1164071 = 1746107) B1746107
theorem B1754095 : Blo 459783 1754095 := bstep (se 1 (by rfl) ⟨1315571, by rfl⟩ : syracuseStep 1754095 = 2631143) B2631143
theorem B50742773 : Blo 459783 50742773 := bstep (se 5 (by rfl) ⟨2378567, by rfl⟩ : syracuseStep 50742773 = 4757135) B4757135
theorem B19286423 : Blo 459783 19286423 := bstep (se 1 (by rfl) ⟨14464817, by rfl⟩ : syracuseStep 19286423 = 28929635) B28929635
theorem B3328427 : Blo 459783 3328427 := bstep (se 1 (by rfl) ⟨2496320, by rfl⟩ : syracuseStep 3328427 = 4992641) B4992641
theorem B2345597 : Blo 459783 2345597 := bstep (se 3 (by rfl) ⟨439799, by rfl⟩ : syracuseStep 2345597 = 879599) B879599
theorem B1035431 : Blo 459783 1035431 := bstep (se 1 (by rfl) ⟨776573, by rfl⟩ : syracuseStep 1035431 = 1553147) B1553147
theorem B3493367 : Blo 459783 3493367 := bstep (se 1 (by rfl) ⟨2620025, by rfl⟩ : syracuseStep 3493367 = 5240051) B5240051
theorem B1757497 : Blo 459783 1757497 := bstep (se 2 (by rfl) ⟨659061, by rfl⟩ : syracuseStep 1757497 = 1318123) B1318123
theorem B1036799 : Blo 459783 1036799 := bstep (se 1 (by rfl) ⟨777599, by rfl⟩ : syracuseStep 1036799 = 1555199) B1555199
theorem B16798211 : Blo 459783 16798211 := bstep (se 1 (by rfl) ⟨12598658, by rfl⟩ : syracuseStep 16798211 = 25197317) B25197317
theorem B1561193 : Blo 459783 1561193 := bstep (se 2 (by rfl) ⟨585447, by rfl⟩ : syracuseStep 1561193 = 1170895) B1170895
theorem B742265 : Blo 459783 742265 := bstep (se 2 (by rfl) ⟨278349, by rfl⟩ : syracuseStep 742265 = 556699) B556699
theorem B1037339 : Blo 459783 1037339 := bstep (se 1 (by rfl) ⟨778004, by rfl⟩ : syracuseStep 1037339 = 1556009) B1556009
theorem B1562111 : Blo 459783 1562111 := bstep (se 1 (by rfl) ⟨1171583, by rfl⟩ : syracuseStep 1562111 = 2343167) B2343167
theorem B1037915 : Blo 459783 1037915 := bstep (se 1 (by rfl) ⟨778436, by rfl⟩ : syracuseStep 1037915 = 1556873) B1556873
theorem B5592979 : Blo 459783 5592979 := bstep (se 1 (by rfl) ⟨4194734, by rfl⟩ : syracuseStep 5592979 = 8389469) B8389469
theorem B1038671 : Blo 459783 1038671 := bstep (se 1 (by rfl) ⟨779003, by rfl⟩ : syracuseStep 1038671 = 1558007) B1558007
theorem B875711 : Blo 459783 875711 := bstep (se 1 (by rfl) ⟨656783, by rfl⟩ : syracuseStep 875711 = 1313567) B1313567
theorem B7495841 : Blo 459783 7495841 := bstep (se 2 (by rfl) ⟨2810940, by rfl⟩ : syracuseStep 7495841 = 5621881) B5621881
theorem B779503 : Blo 459783 779503 := bstep (se 1 (by rfl) ⟨584627, by rfl⟩ : syracuseStep 779503 = 1169255) B1169255
theorem B1041659 : Blo 459783 1041659 := bstep (se 1 (by rfl) ⟨781244, by rfl⟩ : syracuseStep 1041659 = 1562489) B1562489
theorem B582967 : Blo 459783 582967 := bstep (se 1 (by rfl) ⟨437225, by rfl⟩ : syracuseStep 582967 = 874451) B874451
theorem B1041785 : Blo 459783 1041785 := bstep (se 2 (by rfl) ⟨390669, by rfl⟩ : syracuseStep 1041785 = 781339) B781339
theorem B3335579 : Blo 459783 3335579 := bstep (se 1 (by rfl) ⟨2501684, by rfl⟩ : syracuseStep 3335579 = 5003369) B5003369
theorem B1041983 : Blo 459783 1041983 := bstep (se 1 (by rfl) ⟨781487, by rfl⟩ : syracuseStep 1041983 = 1562975) B1562975
theorem B1042145 : Blo 459783 1042145 := bstep (se 2 (by rfl) ⟨390804, by rfl⟩ : syracuseStep 1042145 = 781609) B781609
theorem B517999 : Blo 459783 517999 := bstep (se 1 (by rfl) ⟨388499, by rfl⟩ : syracuseStep 517999 = 776999) B776999
theorem B1042523 : Blo 459783 1042523 := bstep (se 1 (by rfl) ⟨781892, by rfl⟩ : syracuseStep 1042523 = 1563785) B1563785
theorem B1042559 : Blo 459783 1042559 := bstep (se 1 (by rfl) ⟨781919, by rfl⟩ : syracuseStep 1042559 = 1563839) B1563839
theorem B28340063 : Blo 459783 28340063 := bstep (se 1 (by rfl) ⟨21255047, by rfl⟩ : syracuseStep 28340063 = 42510095) B42510095
theorem B5009687 : Blo 459783 5009687 := bstep (se 1 (by rfl) ⟨3757265, by rfl⟩ : syracuseStep 5009687 = 7514531) B7514531
theorem B1831567 : Blo 459783 1831567 := bstep (se 1 (by rfl) ⟨1373675, by rfl⟩ : syracuseStep 1831567 = 2747351) B2747351
theorem B4421567 : Blo 459783 4421567 := bstep (se 1 (by rfl) ⟨3316175, by rfl⟩ : syracuseStep 4421567 = 6632351) B6632351
theorem B1670441 : Blo 459783 1670441 := bstep (se 2 (by rfl) ⟨626415, by rfl⟩ : syracuseStep 1670441 = 1252831) B1252831
theorem B2490439 : Blo 459783 2490439 := bstep (se 1 (by rfl) ⟨1867829, by rfl⟩ : syracuseStep 2490439 = 3735659) B3735659
theorem B1967003 : Blo 459783 1967003 := bstep (se 1 (by rfl) ⟨1475252, by rfl⟩ : syracuseStep 1967003 = 2950505) B2950505
theorem B460015 : Blo 459783 460015 := bstep (se 1 (by rfl) ⟨345011, by rfl⟩ : syracuseStep 460015 = 690023) B690023
theorem B2491631 : Blo 459783 2491631 := bstep (se 1 (by rfl) ⟨1868723, by rfl⟩ : syracuseStep 2491631 = 3737447) B3737447
theorem B2623535 : Blo 459783 2623535 := bstep (se 1 (by rfl) ⟨1967651, by rfl⟩ : syracuseStep 2623535 = 3935303) B3935303
theorem B690287 : Blo 459783 690287 := bstep (se 1 (by rfl) ⟨517715, by rfl⟩ : syracuseStep 690287 = 1035431) B1035431
theorem B2328911 : Blo 459783 2328911 := bstep (se 1 (by rfl) ⟨1746683, by rfl⟩ : syracuseStep 2328911 = 3493367) B3493367
theorem B690665 : Blo 459783 690665 := bstep (se 2 (by rfl) ⟨258999, by rfl⟩ : syracuseStep 690665 = 517999) B517999
theorem B461311 : Blo 459783 461311 := bstep (se 1 (by rfl) ⟨345983, by rfl⟩ : syracuseStep 461311 = 691967) B691967
theorem B691199 : Blo 459783 691199 := bstep (se 1 (by rfl) ⟨518399, by rfl⟩ : syracuseStep 691199 = 1036799) B1036799
theorem B461935 : Blo 459783 461935 := bstep (se 1 (by rfl) ⟨346451, by rfl⟩ : syracuseStep 461935 = 692903) B692903
theorem B462063 : Blo 459783 462063 := bstep (se 1 (by rfl) ⟨346547, by rfl⟩ : syracuseStep 462063 = 693095) B693095
theorem B494843 : Blo 459783 494843 := bstep (se 1 (by rfl) ⟨371132, by rfl⟩ : syracuseStep 494843 = 742265) B742265
theorem B462143 : Blo 459783 462143 := bstep (se 1 (by rfl) ⟨346607, by rfl⟩ : syracuseStep 462143 = 693215) B693215
theorem B691559 : Blo 459783 691559 := bstep (se 1 (by rfl) ⟨518669, by rfl⟩ : syracuseStep 691559 = 1037339) B1037339
theorem B2035199 : Blo 459783 2035199 := bstep (se 1 (by rfl) ⟨1526399, by rfl⟩ : syracuseStep 2035199 = 3052799) B3052799
theorem B691943 : Blo 459783 691943 := bstep (se 1 (by rfl) ⟨518957, by rfl⟩ : syracuseStep 691943 = 1037915) B1037915
theorem B462875 : Blo 459783 462875 := bstep (se 1 (by rfl) ⟨347156, by rfl⟩ : syracuseStep 462875 = 694313) B694313
theorem B462895 : Blo 459783 462895 := bstep (se 1 (by rfl) ⟨347171, by rfl⟩ : syracuseStep 462895 = 694343) B694343
theorem B692447 : Blo 459783 692447 := bstep (se 1 (by rfl) ⟨519335, by rfl⟩ : syracuseStep 692447 = 1038671) B1038671
theorem B1578491 : Blo 459783 1578491 := bstep (se 1 (by rfl) ⟨1183868, by rfl⟩ : syracuseStep 1578491 = 2367737) B2367737
theorem B2332313 : Blo 459783 2332313 := bstep (se 2 (by rfl) ⟨874617, by rfl⟩ : syracuseStep 2332313 = 1749235) B1749235
theorem B694439 : Blo 459783 694439 := bstep (se 1 (by rfl) ⟨520829, by rfl⟩ : syracuseStep 694439 = 1041659) B1041659
theorem B1317053 : Blo 459783 1317053 := bstep (se 3 (by rfl) ⟨246947, by rfl⟩ : syracuseStep 1317053 = 493895) B493895
theorem B694523 : Blo 459783 694523 := bstep (se 1 (by rfl) ⟨520892, by rfl⟩ : syracuseStep 694523 = 1041785) B1041785
theorem B694655 : Blo 459783 694655 := bstep (se 1 (by rfl) ⟨520991, by rfl⟩ : syracuseStep 694655 = 1041983) B1041983
theorem B694763 : Blo 459783 694763 := bstep (se 1 (by rfl) ⟨521072, by rfl⟩ : syracuseStep 694763 = 1042145) B1042145
theorem B695015 : Blo 459783 695015 := bstep (se 1 (by rfl) ⟨521261, by rfl⟩ : syracuseStep 695015 = 1042523) B1042523
theorem B695039 : Blo 459783 695039 := bstep (se 1 (by rfl) ⟨521279, by rfl⟩ : syracuseStep 695039 = 1042559) B1042559
theorem B2335229 : Blo 459783 2335229 := bstep (se 3 (by rfl) ⟨437855, by rfl⟩ : syracuseStep 2335229 = 875711) B875711
theorem B41527133 : Blo 459783 41527133 := bstep (se 3 (by rfl) ⟨7786337, by rfl⟩ : syracuseStep 41527133 = 15572675) B15572675
theorem B468839 : Blo 459783 468839 := bstep (se 1 (by rfl) ⟨351629, by rfl⟩ : syracuseStep 468839 = 703259) B703259
theorem B14395877 : Blo 459783 14395877 := bstep (se 4 (by rfl) ⟨1349613, by rfl⟩ : syracuseStep 14395877 = 2699227) B2699227
theorem B33828515 : Blo 459783 33828515 := bstep (se 1 (by rfl) ⟨25371386, by rfl⟩ : syracuseStep 33828515 = 50742773) B50742773
theorem B2338793 : Blo 459783 2338793 := bstep (se 2 (by rfl) ⟨877047, by rfl⟩ : syracuseStep 2338793 = 1754095) B1754095
theorem B12857615 : Blo 459783 12857615 := bstep (se 1 (by rfl) ⟨9643211, by rfl⟩ : syracuseStep 12857615 = 19286423) B19286423
theorem B3160721 : Blo 459783 3160721 := bstep (se 2 (by rfl) ⟨1185270, by rfl⟩ : syracuseStep 3160721 = 2370541) B2370541
theorem B1555631 : Blo 459783 1555631 := bstep (se 1 (by rfl) ⟨1166723, by rfl⟩ : syracuseStep 1555631 = 2333447) B2333447
theorem B3947777 : Blo 459783 3947777 := bstep (se 2 (by rfl) ⟨1480416, by rfl⟩ : syracuseStep 3947777 = 2960833) B2960833
theorem B2211263 : Blo 459783 2211263 := bstep (se 1 (by rfl) ⟨1658447, by rfl⟩ : syracuseStep 2211263 = 3316895) B3316895
theorem B4997227 : Blo 459783 4997227 := bstep (se 1 (by rfl) ⟨3747920, by rfl⟩ : syracuseStep 4997227 = 7495841) B7495841
theorem B1753427 : Blo 459783 1753427 := bstep (se 1 (by rfl) ⟨1315070, by rfl⟩ : syracuseStep 1753427 = 2630141) B2630141
theorem B2343329 : Blo 459783 2343329 := bstep (se 2 (by rfl) ⟨878748, by rfl⟩ : syracuseStep 2343329 = 1757497) B1757497
theorem B2212379 : Blo 459783 2212379 := bstep (se 1 (by rfl) ⟨1659284, by rfl⟩ : syracuseStep 2212379 = 3318569) B3318569
theorem B2442089 : Blo 459783 2442089 := bstep (se 2 (by rfl) ⟨915783, by rfl⟩ : syracuseStep 2442089 = 1831567) B1831567
theorem B1165043 : Blo 459783 1165043 := bstep (se 1 (by rfl) ⟨873782, by rfl⟩ : syracuseStep 1165043 = 1747565) B1747565
theorem B1558655 : Blo 459783 1558655 := bstep (se 1 (by rfl) ⟨1168991, by rfl⟩ : syracuseStep 1558655 = 2337983) B2337983
theorem B1165823 : Blo 459783 1165823 := bstep (se 1 (by rfl) ⟨874367, by rfl⟩ : syracuseStep 1165823 = 1748735) B1748735
theorem B7457305 : Blo 459783 7457305 := bstep (se 2 (by rfl) ⟨2796489, by rfl⟩ : syracuseStep 7457305 = 5592979) B5592979
theorem B18893375 : Blo 459783 18893375 := bstep (se 1 (by rfl) ⟨14170031, by rfl⟩ : syracuseStep 18893375 = 28340063) B28340063
theorem B13290641 : Blo 459783 13290641 := bstep (se 2 (by rfl) ⟨4983990, by rfl⟩ : syracuseStep 13290641 = 9967981) B9967981
theorem B1756511 : Blo 459783 1756511 := bstep (se 1 (by rfl) ⟨1317383, by rfl⟩ : syracuseStep 1756511 = 2634767) B2634767
theorem B1035935 : Blo 459783 1035935 := bstep (se 1 (by rfl) ⟨776951, by rfl⟩ : syracuseStep 1035935 = 1553903) B1553903
theorem B1168091 : Blo 459783 1168091 := bstep (se 1 (by rfl) ⟨876068, by rfl⟩ : syracuseStep 1168091 = 1752137) B1752137
theorem B5625283 : Blo 459783 5625283 := bstep (se 1 (by rfl) ⟨4218962, by rfl⟩ : syracuseStep 5625283 = 8437925) B8437925
theorem B776047 : Blo 459783 776047 := bstep (se 1 (by rfl) ⟨582035, by rfl⟩ : syracuseStep 776047 = 1164071) B1164071
theorem B3955463 : Blo 459783 3955463 := bstep (se 1 (by rfl) ⟨2966597, by rfl⟩ : syracuseStep 3955463 = 5933195) B5933195
theorem B2218951 : Blo 459783 2218951 := bstep (se 1 (by rfl) ⟨1664213, by rfl⟩ : syracuseStep 2218951 = 3328427) B3328427
theorem B1039337 : Blo 459783 1039337 := bstep (se 2 (by rfl) ⟨389751, by rfl⟩ : syracuseStep 1039337 = 779503) B779503
theorem B777289 : Blo 459783 777289 := bstep (se 2 (by rfl) ⟨291483, by rfl⟩ : syracuseStep 777289 = 582967) B582967
theorem B1563731 : Blo 459783 1563731 := bstep (se 1 (by rfl) ⟨1172798, by rfl⟩ : syracuseStep 1563731 = 2345597) B2345597
theorem B11198807 : Blo 459783 11198807 := bstep (se 1 (by rfl) ⟨8399105, by rfl⟩ : syracuseStep 11198807 = 16798211) B16798211
theorem B1040795 : Blo 459783 1040795 := bstep (se 1 (by rfl) ⟨780596, by rfl⟩ : syracuseStep 1040795 = 1561193) B1561193
theorem B36004823 : Blo 459783 36004823 := bstep (se 1 (by rfl) ⟨27003617, by rfl⟩ : syracuseStep 36004823 = 54007235) B54007235
theorem B1041407 : Blo 459783 1041407 := bstep (se 1 (by rfl) ⟨781055, by rfl⟩ : syracuseStep 1041407 = 1562111) B1562111
theorem B5269211 : Blo 459783 5269211 := bstep (se 1 (by rfl) ⟨3951908, by rfl⟩ : syracuseStep 5269211 = 7903817) B7903817
theorem B1141499 : Blo 459783 1141499 := bstep (se 1 (by rfl) ⟨856124, by rfl⟩ : syracuseStep 1141499 = 1712249) B1712249
theorem B3959837 : Blo 459783 3959837 := bstep (se 3 (by rfl) ⟨742469, by rfl⟩ : syracuseStep 3959837 = 1484939) B1484939
theorem B2223719 : Blo 459783 2223719 := bstep (se 1 (by rfl) ⟨1667789, by rfl⟩ : syracuseStep 2223719 = 3335579) B3335579
theorem B3339791 : Blo 459783 3339791 := bstep (se 1 (by rfl) ⟨2504843, by rfl⟩ : syracuseStep 3339791 = 5009687) B5009687
theorem B3569179 : Blo 459783 3569179 := bstep (se 1 (by rfl) ⟨2676884, by rfl⟩ : syracuseStep 3569179 = 5353769) B5353769
theorem B4454509 : Blo 459783 4454509 := bstep (se 3 (by rfl) ⟨835220, by rfl⟩ : syracuseStep 4454509 = 1670441) B1670441
theorem B5929199 : Blo 459783 5929199 := bstep (se 1 (by rfl) ⟨4446899, by rfl⟩ : syracuseStep 5929199 = 8893799) B8893799
theorem B2947711 : Blo 459783 2947711 := bstep (se 1 (by rfl) ⟨2210783, by rfl⟩ : syracuseStep 2947711 = 4421567) B4421567
theorem B1474919 : Blo 459783 1474919 := bstep (se 1 (by rfl) ⟨1106189, by rfl⟩ : syracuseStep 1474919 = 2212379) B2212379
theorem B1311335 : Blo 459783 1311335 := bstep (se 1 (by rfl) ⟨983501, by rfl⟩ : syracuseStep 1311335 = 1967003) B1967003
theorem B460191 : Blo 459783 460191 := bstep (se 1 (by rfl) ⟨345143, by rfl⟩ : syracuseStep 460191 = 690287) B690287
theorem B460443 : Blo 459783 460443 := bstep (se 1 (by rfl) ⟨345332, by rfl⟩ : syracuseStep 460443 = 690665) B690665
theorem B460799 : Blo 459783 460799 := bstep (se 1 (by rfl) ⟨345599, by rfl⟩ : syracuseStep 460799 = 691199) B691199
theorem B461039 : Blo 459783 461039 := bstep (se 1 (by rfl) ⟨345779, by rfl⟩ : syracuseStep 461039 = 691559) B691559
theorem B690623 : Blo 459783 690623 := bstep (se 1 (by rfl) ⟨517967, by rfl⟩ : syracuseStep 690623 = 1035935) B1035935
theorem B461295 : Blo 459783 461295 := bstep (se 1 (by rfl) ⟨345971, by rfl⟩ : syracuseStep 461295 = 691943) B691943
theorem B461631 : Blo 459783 461631 := bstep (se 1 (by rfl) ⟨346223, by rfl⟩ : syracuseStep 461631 = 692447) B692447
theorem B1052327 : Blo 459783 1052327 := bstep (se 1 (by rfl) ⟨789245, by rfl⟩ : syracuseStep 1052327 = 1578491) B1578491
theorem B462959 : Blo 459783 462959 := bstep (se 1 (by rfl) ⟨347219, by rfl⟩ : syracuseStep 462959 = 694439) B694439
theorem B463015 : Blo 459783 463015 := bstep (se 1 (by rfl) ⟨347261, by rfl⟩ : syracuseStep 463015 = 694523) B694523
theorem B463103 : Blo 459783 463103 := bstep (se 1 (by rfl) ⟨347327, by rfl⟩ : syracuseStep 463103 = 694655) B694655
theorem B463175 : Blo 459783 463175 := bstep (se 1 (by rfl) ⟨347381, by rfl⟩ : syracuseStep 463175 = 694763) B694763
theorem B463343 : Blo 459783 463343 := bstep (se 1 (by rfl) ⟨347507, by rfl⟩ : syracuseStep 463343 = 695015) B695015
theorem B463359 : Blo 459783 463359 := bstep (se 1 (by rfl) ⟨347519, by rfl⟩ : syracuseStep 463359 = 695039) B695039
theorem B692891 : Blo 459783 692891 := bstep (se 1 (by rfl) ⟨519668, by rfl⟩ : syracuseStep 692891 = 1039337) B1039337
theorem B1250237 : Blo 459783 1250237 := bstep (se 3 (by rfl) ⟨234419, by rfl⟩ : syracuseStep 1250237 = 468839) B468839
theorem B693863 : Blo 459783 693863 := bstep (se 1 (by rfl) ⟨520397, by rfl⟩ : syracuseStep 693863 = 1040795) B1040795
theorem B694271 : Blo 459783 694271 := bstep (se 1 (by rfl) ⟨520703, by rfl⟩ : syracuseStep 694271 = 1041407) B1041407
theorem B3512807 : Blo 459783 3512807 := bstep (se 1 (by rfl) ⟨2634605, by rfl⟩ : syracuseStep 3512807 = 5269211) B5269211
theorem B4758905 : Blo 459783 4758905 := bstep (se 2 (by rfl) ⟨1784589, by rfl⟩ : syracuseStep 4758905 = 3569179) B3569179
theorem B1482479 : Blo 459783 1482479 := bstep (se 1 (by rfl) ⟨1111859, by rfl⟩ : syracuseStep 1482479 = 2223719) B2223719
theorem B22552343 : Blo 459783 22552343 := bstep (se 1 (by rfl) ⟨16914257, by rfl⟩ : syracuseStep 22552343 = 33828515) B33828515
theorem B5939345 : Blo 459783 5939345 := bstep (se 2 (by rfl) ⟨2227254, by rfl⟩ : syracuseStep 5939345 = 4454509) B4454509
theorem B1319581 : Blo 459783 1319581 := bstep (se 3 (by rfl) ⟨247421, by rfl⟩ : syracuseStep 1319581 = 494843) B494843
theorem B2958601 : Blo 459783 2958601 := bstep (se 2 (by rfl) ⟨1109475, by rfl⟩ : syracuseStep 2958601 = 2218951) B2218951
theorem B2107147 : Blo 459783 2107147 := bstep (se 1 (by rfl) ⟨1580360, by rfl⟩ : syracuseStep 2107147 = 3160721) B3160721
theorem B2631851 : Blo 459783 2631851 := bstep (se 1 (by rfl) ⟨1973888, by rfl⟩ : syracuseStep 2631851 = 3947777) B3947777
theorem B3320585 : Blo 459783 3320585 := bstep (se 2 (by rfl) ⟨1245219, by rfl⟩ : syracuseStep 3320585 = 2490439) B2490439
theorem B6662969 : Blo 459783 6662969 := bstep (se 2 (by rfl) ⟨2498613, by rfl⟩ : syracuseStep 6662969 = 4997227) B4997227
theorem B1749023 : Blo 459783 1749023 := bstep (se 1 (by rfl) ⟨1311767, by rfl⟩ : syracuseStep 1749023 = 2623535) B2623535
theorem B1552607 : Blo 459783 1552607 := bstep (se 1 (by rfl) ⟨1164455, by rfl⟩ : syracuseStep 1552607 = 2328911) B2328911
theorem B12595583 : Blo 459783 12595583 := bstep (se 1 (by rfl) ⟨9446687, by rfl⟩ : syracuseStep 12595583 = 18893375) B18893375
theorem B8860427 : Blo 459783 8860427 := bstep (se 1 (by rfl) ⟨6645320, by rfl⟩ : syracuseStep 8860427 = 13290641) B13290641
theorem B1356799 : Blo 459783 1356799 := bstep (se 1 (by rfl) ⟨1017599, by rfl⟩ : syracuseStep 1356799 = 2035199) B2035199
theorem B9943073 : Blo 459783 9943073 := bstep (se 2 (by rfl) ⟨3728652, by rfl⟩ : syracuseStep 9943073 = 7457305) B7457305
theorem B1554875 : Blo 459783 1554875 := bstep (se 1 (by rfl) ⟨1166156, by rfl⟩ : syracuseStep 1554875 = 2332313) B2332313
theorem B2636975 : Blo 459783 2636975 := bstep (se 1 (by rfl) ⟨1977731, by rfl⟩ : syracuseStep 2636975 = 3955463) B3955463
theorem B1556819 : Blo 459783 1556819 := bstep (se 1 (by rfl) ⟨1167614, by rfl⟩ : syracuseStep 1556819 = 2335229) B2335229
theorem B24003215 : Blo 459783 24003215 := bstep (se 1 (by rfl) ⟨18002411, by rfl⟩ : syracuseStep 24003215 = 36004823) B36004823
theorem B2639891 : Blo 459783 2639891 := bstep (se 1 (by rfl) ⟨1979918, by rfl⟩ : syracuseStep 2639891 = 3959837) B3959837
theorem B1034729 : Blo 459783 1034729 := bstep (se 2 (by rfl) ⟨388023, by rfl⟩ : syracuseStep 1034729 = 776047) B776047
theorem B1559195 : Blo 459783 1559195 := bstep (se 1 (by rfl) ⟨1169396, by rfl⟩ : syracuseStep 1559195 = 2338793) B2338793
theorem B8571743 : Blo 459783 8571743 := bstep (se 1 (by rfl) ⟨6428807, by rfl⟩ : syracuseStep 8571743 = 12857615) B12857615
theorem B1036385 : Blo 459783 1036385 := bstep (se 2 (by rfl) ⟨388644, by rfl⟩ : syracuseStep 1036385 = 777289) B777289
theorem B3952799 : Blo 459783 3952799 := bstep (se 1 (by rfl) ⟨2964599, by rfl⟩ : syracuseStep 3952799 = 5929199) B5929199
theorem B1037087 : Blo 459783 1037087 := bstep (se 1 (by rfl) ⟨777815, by rfl⟩ : syracuseStep 1037087 = 1555631) B1555631
theorem B1168951 : Blo 459783 1168951 := bstep (se 1 (by rfl) ⟨876713, by rfl⟩ : syracuseStep 1168951 = 1753427) B1753427
theorem B1562219 : Blo 459783 1562219 := bstep (se 1 (by rfl) ⟨1171664, by rfl⟩ : syracuseStep 1562219 = 2343329) B2343329
theorem B1628059 : Blo 459783 1628059 := bstep (se 1 (by rfl) ⟨1221044, by rfl⟩ : syracuseStep 1628059 = 2442089) B2442089
theorem B1661087 : Blo 459783 1661087 := bstep (se 1 (by rfl) ⟨1245815, by rfl⟩ : syracuseStep 1661087 = 2491631) B2491631
theorem B776695 : Blo 459783 776695 := bstep (se 1 (by rfl) ⟨582521, by rfl⟩ : syracuseStep 776695 = 1165043) B1165043
theorem B1039103 : Blo 459783 1039103 := bstep (se 1 (by rfl) ⟨779327, by rfl⟩ : syracuseStep 1039103 = 1558655) B1558655
theorem B777215 : Blo 459783 777215 := bstep (se 1 (by rfl) ⟨582911, by rfl⟩ : syracuseStep 777215 = 1165823) B1165823
theorem B1171007 : Blo 459783 1171007 := bstep (se 1 (by rfl) ⟨878255, by rfl⟩ : syracuseStep 1171007 = 1756511) B1756511
theorem B778727 : Blo 459783 778727 := bstep (se 1 (by rfl) ⟨584045, by rfl⟩ : syracuseStep 778727 = 1168091) B1168091
theorem B878035 : Blo 459783 878035 := bstep (se 1 (by rfl) ⟨658526, by rfl⟩ : syracuseStep 878035 = 1317053) B1317053
theorem B1042487 : Blo 459783 1042487 := bstep (se 1 (by rfl) ⟨781865, by rfl⟩ : syracuseStep 1042487 = 1563731) B1563731
theorem B7465871 : Blo 459783 7465871 := bstep (se 1 (by rfl) ⟨5599403, by rfl⟩ : syracuseStep 7465871 = 11198807) B11198807
theorem B27684755 : Blo 459783 27684755 := bstep (se 1 (by rfl) ⟨20763566, by rfl⟩ : syracuseStep 27684755 = 41527133) B41527133
theorem B9597251 : Blo 459783 9597251 := bstep (se 1 (by rfl) ⟨7197938, by rfl⟩ : syracuseStep 9597251 = 14395877) B14395877
theorem B7500377 : Blo 459783 7500377 := bstep (se 2 (by rfl) ⟨2812641, by rfl⟩ : syracuseStep 7500377 = 5625283) B5625283
theorem B3043997 : Blo 459783 3043997 := bstep (se 3 (by rfl) ⟨570749, by rfl⟩ : syracuseStep 3043997 = 1141499) B1141499
theorem B3930281 : Blo 459783 3930281 := bstep (se 2 (by rfl) ⟨1473855, by rfl⟩ : syracuseStep 3930281 = 2947711) B2947711
theorem B2226527 : Blo 459783 2226527 := bstep (se 1 (by rfl) ⟨1669895, by rfl⟩ : syracuseStep 2226527 = 3339791) B3339791
theorem B1474175 : Blo 459783 1474175 := bstep (se 1 (by rfl) ⟨1105631, by rfl⟩ : syracuseStep 1474175 = 2211263) B2211263
theorem B983279 : Blo 459783 983279 := bstep (se 1 (by rfl) ⟨737459, by rfl⟩ : syracuseStep 983279 = 1474919) B1474919
theorem B25592669 : Blo 459783 25592669 := bstep (se 3 (by rfl) ⟨4798625, by rfl⟩ : syracuseStep 25592669 = 9597251) B9597251
theorem B460415 : Blo 459783 460415 := bstep (se 1 (by rfl) ⟨345311, by rfl⟩ : syracuseStep 460415 = 690623) B690623
theorem B689819 : Blo 459783 689819 := bstep (se 1 (by rfl) ⟨517364, by rfl⟩ : syracuseStep 689819 = 1034729) B1034729
theorem B690923 : Blo 459783 690923 := bstep (se 1 (by rfl) ⟨518192, by rfl⟩ : syracuseStep 690923 = 1036385) B1036385
theorem B461927 : Blo 459783 461927 := bstep (se 1 (by rfl) ⟨346445, by rfl⟩ : syracuseStep 461927 = 692891) B692891
theorem B691391 : Blo 459783 691391 := bstep (se 1 (by rfl) ⟨518543, by rfl⟩ : syracuseStep 691391 = 1037087) B1037087
theorem B462575 : Blo 459783 462575 := bstep (se 1 (by rfl) ⟨346931, by rfl⟩ : syracuseStep 462575 = 693863) B693863
theorem B462847 : Blo 459783 462847 := bstep (se 1 (by rfl) ⟨347135, by rfl⟩ : syracuseStep 462847 = 694271) B694271
theorem B692735 : Blo 459783 692735 := bstep (se 1 (by rfl) ⟨519551, by rfl⟩ : syracuseStep 692735 = 1039103) B1039103
theorem B988319 : Blo 459783 988319 := bstep (se 1 (by rfl) ⟨741239, by rfl⟩ : syracuseStep 988319 = 1482479) B1482479
theorem B4429565 : Blo 459783 4429565 := bstep (se 3 (by rfl) ⟨830543, by rfl⟩ : syracuseStep 4429565 = 1661087) B1661087
theorem B1809065 : Blo 459783 1809065 := bstep (se 2 (by rfl) ⟨678399, by rfl⟩ : syracuseStep 1809065 = 1356799) B1356799
theorem B694991 : Blo 459783 694991 := bstep (se 1 (by rfl) ⟨521243, by rfl⟩ : syracuseStep 694991 = 1042487) B1042487
theorem B2170745 : Blo 459783 2170745 := bstep (se 2 (by rfl) ⟨814029, by rfl⟩ : syracuseStep 2170745 = 1628059) B1628059
theorem B18456503 : Blo 459783 18456503 := bstep (se 1 (by rfl) ⟨13842377, by rfl⟩ : syracuseStep 18456503 = 27684755) B27684755
theorem B8397055 : Blo 459783 8397055 := bstep (se 1 (by rfl) ⟨6297791, by rfl⟩ : syracuseStep 8397055 = 12595583) B12595583
theorem B5906951 : Blo 459783 5906951 := bstep (se 1 (by rfl) ⟨4430213, by rfl⟩ : syracuseStep 5906951 = 8860427) B8860427
theorem B6628715 : Blo 459783 6628715 := bstep (se 1 (by rfl) ⟨4971536, by rfl⟩ : syracuseStep 6628715 = 9943073) B9943073
theorem B1484351 : Blo 459783 1484351 := bstep (se 1 (by rfl) ⟨1113263, by rfl⟩ : syracuseStep 1484351 = 2226527) B2226527
theorem B16002143 : Blo 459783 16002143 := bstep (se 1 (by rfl) ⟨12001607, by rfl⟩ : syracuseStep 16002143 = 24003215) B24003215
theorem B20001005 : Blo 459783 20001005 := bstep (se 3 (by rfl) ⟨3750188, by rfl⟩ : syracuseStep 20001005 = 7500377) B7500377
theorem B3944801 : Blo 459783 3944801 := bstep (se 2 (by rfl) ⟨1479300, by rfl⟩ : syracuseStep 3944801 = 2958601) B2958601
theorem B5714495 : Blo 459783 5714495 := bstep (se 1 (by rfl) ⟨4285871, by rfl⟩ : syracuseStep 5714495 = 8571743) B8571743
theorem B701551 : Blo 459783 701551 := bstep (se 1 (by rfl) ⟨526163, by rfl⟩ : syracuseStep 701551 = 1052327) B1052327
theorem B2635199 : Blo 459783 2635199 := bstep (se 1 (by rfl) ⟨1976399, by rfl⟩ : syracuseStep 2635199 = 3952799) B3952799
theorem B833491 : Blo 459783 833491 := bstep (se 1 (by rfl) ⟨625118, by rfl⟩ : syracuseStep 833491 = 1250237) B1250237
theorem B2341871 : Blo 459783 2341871 := bstep (se 1 (by rfl) ⟨1756403, by rfl⟩ : syracuseStep 2341871 = 3512807) B3512807
theorem B1754567 : Blo 459783 1754567 := bstep (se 1 (by rfl) ⟨1315925, by rfl⟩ : syracuseStep 1754567 = 2631851) B2631851
theorem B2213723 : Blo 459783 2213723 := bstep (se 1 (by rfl) ⟨1660292, by rfl⟩ : syracuseStep 2213723 = 3320585) B3320585
theorem B4441979 : Blo 459783 4441979 := bstep (se 1 (by rfl) ⟨3331484, by rfl⟩ : syracuseStep 4441979 = 6662969) B6662969
theorem B1558601 : Blo 459783 1558601 := bstep (se 2 (by rfl) ⟨584475, by rfl⟩ : syracuseStep 1558601 = 1168951) B1168951
theorem B1166015 : Blo 459783 1166015 := bstep (se 1 (by rfl) ⟨874511, by rfl⟩ : syracuseStep 1166015 = 1749023) B1749023
theorem B1035071 : Blo 459783 1035071 := bstep (se 1 (by rfl) ⟨776303, by rfl⟩ : syracuseStep 1035071 = 1552607) B1552607
theorem B1035593 : Blo 459783 1035593 := bstep (se 2 (by rfl) ⟨388347, by rfl⟩ : syracuseStep 1035593 = 776695) B776695
theorem B1036583 : Blo 459783 1036583 := bstep (se 1 (by rfl) ⟨777437, by rfl⟩ : syracuseStep 1036583 = 1554875) B1554875
theorem B1757983 : Blo 459783 1757983 := bstep (se 1 (by rfl) ⟨1318487, by rfl⟩ : syracuseStep 1757983 = 2636975) B2636975
theorem B1037879 : Blo 459783 1037879 := bstep (se 1 (by rfl) ⟨778409, by rfl⟩ : syracuseStep 1037879 = 1556819) B1556819
theorem B874223 : Blo 459783 874223 := bstep (se 1 (by rfl) ⟨655667, by rfl⟩ : syracuseStep 874223 = 1311335) B1311335
theorem B1759441 : Blo 459783 1759441 := bstep (se 2 (by rfl) ⟨659790, by rfl⟩ : syracuseStep 1759441 = 1319581) B1319581
theorem B1759927 : Blo 459783 1759927 := bstep (se 1 (by rfl) ⟨1319945, by rfl⟩ : syracuseStep 1759927 = 2639891) B2639891
theorem B1039463 : Blo 459783 1039463 := bstep (se 1 (by rfl) ⟨779597, by rfl⟩ : syracuseStep 1039463 = 1559195) B1559195
theorem B1170713 : Blo 459783 1170713 := bstep (se 2 (by rfl) ⟨439017, by rfl⟩ : syracuseStep 1170713 = 878035) B878035
theorem B2809529 : Blo 459783 2809529 := bstep (se 2 (by rfl) ⟨1053573, by rfl⟩ : syracuseStep 2809529 = 2107147) B2107147
theorem B1041479 : Blo 459783 1041479 := bstep (se 1 (by rfl) ⟨781109, by rfl⟩ : syracuseStep 1041479 = 1562219) B1562219
theorem B518143 : Blo 459783 518143 := bstep (se 1 (by rfl) ⟨388607, by rfl⟩ : syracuseStep 518143 = 777215) B777215
theorem B3172603 : Blo 459783 3172603 := bstep (se 1 (by rfl) ⟨2379452, by rfl⟩ : syracuseStep 3172603 = 4758905) B4758905
theorem B780671 : Blo 459783 780671 := bstep (se 1 (by rfl) ⟨585503, by rfl⟩ : syracuseStep 780671 = 1171007) B1171007
theorem B15034895 : Blo 459783 15034895 := bstep (se 1 (by rfl) ⟨11276171, by rfl⟩ : syracuseStep 15034895 = 22552343) B22552343
theorem B3959563 : Blo 459783 3959563 := bstep (se 1 (by rfl) ⟨2969672, by rfl⟩ : syracuseStep 3959563 = 5939345) B5939345
theorem B519151 : Blo 459783 519151 := bstep (se 1 (by rfl) ⟨389363, by rfl⟩ : syracuseStep 519151 = 778727) B778727
theorem B4977247 : Blo 459783 4977247 := bstep (se 1 (by rfl) ⟨3732935, by rfl⟩ : syracuseStep 4977247 = 7465871) B7465871
theorem B2029331 : Blo 459783 2029331 := bstep (se 1 (by rfl) ⟨1521998, by rfl⟩ : syracuseStep 2029331 = 3043997) B3043997
theorem B2620187 : Blo 459783 2620187 := bstep (se 1 (by rfl) ⟨1965140, by rfl⟩ : syracuseStep 2620187 = 3930281) B3930281
theorem B982783 : Blo 459783 982783 := bstep (se 1 (by rfl) ⟨737087, by rfl⟩ : syracuseStep 982783 = 1474175) B1474175
theorem B2622077 : Blo 459783 2622077 := bstep (se 3 (by rfl) ⟨491639, by rfl⟩ : syracuseStep 2622077 = 983279) B983279
theorem B459879 : Blo 459783 459879 := bstep (se 1 (by rfl) ⟨344909, by rfl⟩ : syracuseStep 459879 = 689819) B689819
theorem B1475815 : Blo 459783 1475815 := bstep (se 1 (by rfl) ⟨1106861, by rfl⟩ : syracuseStep 1475815 = 2213723) B2213723
theorem B460615 : Blo 459783 460615 := bstep (se 1 (by rfl) ⟨345461, by rfl⟩ : syracuseStep 460615 = 690923) B690923
theorem B690047 : Blo 459783 690047 := bstep (se 1 (by rfl) ⟨517535, by rfl⟩ : syracuseStep 690047 = 1035071) B1035071
theorem B460927 : Blo 459783 460927 := bstep (se 1 (by rfl) ⟨345695, by rfl⟩ : syracuseStep 460927 = 691391) B691391
theorem B690395 : Blo 459783 690395 := bstep (se 1 (by rfl) ⟨517796, by rfl⟩ : syracuseStep 690395 = 1035593) B1035593
theorem B690857 : Blo 459783 690857 := bstep (se 2 (by rfl) ⟨259071, by rfl⟩ : syracuseStep 690857 = 518143) B518143
theorem B691055 : Blo 459783 691055 := bstep (se 1 (by rfl) ⟨518291, by rfl⟩ : syracuseStep 691055 = 1036583) B1036583
theorem B4230137 : Blo 459783 4230137 := bstep (se 2 (by rfl) ⟨1586301, by rfl⟩ : syracuseStep 4230137 = 3172603) B3172603
theorem B461823 : Blo 459783 461823 := bstep (se 1 (by rfl) ⟨346367, by rfl⟩ : syracuseStep 461823 = 692735) B692735
theorem B5279417 : Blo 459783 5279417 := bstep (se 2 (by rfl) ⟨1979781, by rfl⟩ : syracuseStep 5279417 = 3959563) B3959563
theorem B691919 : Blo 459783 691919 := bstep (se 1 (by rfl) ⟨518939, by rfl⟩ : syracuseStep 691919 = 1037879) B1037879
theorem B2953043 : Blo 459783 2953043 := bstep (se 1 (by rfl) ⟨2214782, by rfl⟩ : syracuseStep 2953043 = 4429565) B4429565
theorem B692201 : Blo 459783 692201 := bstep (se 2 (by rfl) ⟨259575, by rfl⟩ : syracuseStep 692201 = 519151) B519151
theorem B463327 : Blo 459783 463327 := bstep (se 1 (by rfl) ⟨347495, by rfl⟩ : syracuseStep 463327 = 694991) B694991
theorem B5411549 : Blo 459783 5411549 := bstep (se 3 (by rfl) ⟨1014665, by rfl⟩ : syracuseStep 5411549 = 2029331) B2029331
theorem B692975 : Blo 459783 692975 := bstep (se 1 (by rfl) ⟨519731, by rfl⟩ : syracuseStep 692975 = 1039463) B1039463
theorem B1873019 : Blo 459783 1873019 := bstep (se 1 (by rfl) ⟨1404764, by rfl⟩ : syracuseStep 1873019 = 2809529) B2809529
theorem B1447163 : Blo 459783 1447163 := bstep (se 1 (by rfl) ⟨1085372, by rfl⟩ : syracuseStep 1447163 = 2170745) B2170745
theorem B3937967 : Blo 459783 3937967 := bstep (se 1 (by rfl) ⟨2953475, by rfl⟩ : syracuseStep 3937967 = 5906951) B5906951
theorem B694319 : Blo 459783 694319 := bstep (se 1 (by rfl) ⟨520739, by rfl⟩ : syracuseStep 694319 = 1041479) B1041479
theorem B989567 : Blo 459783 989567 := bstep (se 1 (by rfl) ⟨742175, by rfl⟩ : syracuseStep 989567 = 1484351) B1484351
theorem B4824173 : Blo 459783 4824173 := bstep (se 3 (by rfl) ⟨904532, by rfl⟩ : syracuseStep 4824173 = 1809065) B1809065
theorem B2629867 : Blo 459783 2629867 := bstep (se 1 (by rfl) ⟨1972400, by rfl⟩ : syracuseStep 2629867 = 3944801) B3944801
theorem B3809663 : Blo 459783 3809663 := bstep (se 1 (by rfl) ⟨2857247, by rfl⟩ : syracuseStep 3809663 = 5714495) B5714495
theorem B1746791 : Blo 459783 1746791 := bstep (se 1 (by rfl) ⟨1310093, by rfl⟩ : syracuseStep 1746791 = 2620187) B2620187
theorem B2961319 : Blo 459783 2961319 := bstep (se 1 (by rfl) ⟨2220989, by rfl⟩ : syracuseStep 2961319 = 4441979) B4441979
theorem B2635517 : Blo 459783 2635517 := bstep (se 3 (by rfl) ⟨494159, by rfl⟩ : syracuseStep 2635517 = 988319) B988319
theorem B6636329 : Blo 459783 6636329 := bstep (se 2 (by rfl) ⟨2488623, by rfl⟩ : syracuseStep 6636329 = 4977247) B4977247
theorem B2343977 : Blo 459783 2343977 := bstep (se 2 (by rfl) ⟨878991, by rfl⟩ : syracuseStep 2343977 = 1757983) B1757983
theorem B935401 : Blo 459783 935401 := bstep (se 2 (by rfl) ⟨350775, by rfl⟩ : syracuseStep 935401 = 701551) B701551
theorem B10668095 : Blo 459783 10668095 := bstep (se 1 (by rfl) ⟨8001071, by rfl⟩ : syracuseStep 10668095 = 16002143) B16002143
theorem B2345921 : Blo 459783 2345921 := bstep (se 2 (by rfl) ⟨879720, by rfl⟩ : syracuseStep 2345921 = 1759441) B1759441
theorem B2346569 : Blo 459783 2346569 := bstep (se 2 (by rfl) ⟨879963, by rfl⟩ : syracuseStep 2346569 = 1759927) B1759927
theorem B1756799 : Blo 459783 1756799 := bstep (se 1 (by rfl) ⟨1317599, by rfl⟩ : syracuseStep 1756799 = 2635199) B2635199
theorem B1561247 : Blo 459783 1561247 := bstep (se 1 (by rfl) ⟨1170935, by rfl⟩ : syracuseStep 1561247 = 2341871) B2341871
theorem B11196073 : Blo 459783 11196073 := bstep (se 2 (by rfl) ⟨4198527, by rfl⟩ : syracuseStep 11196073 = 8397055) B8397055
theorem B17061779 : Blo 459783 17061779 := bstep (se 1 (by rfl) ⟨12796334, by rfl⟩ : syracuseStep 17061779 = 25592669) B25592669
theorem B1169711 : Blo 459783 1169711 := bstep (se 1 (by rfl) ⟨877283, by rfl⟩ : syracuseStep 1169711 = 1754567) B1754567
theorem B1039067 : Blo 459783 1039067 := bstep (se 1 (by rfl) ⟨779300, by rfl⟩ : syracuseStep 1039067 = 1558601) B1558601
theorem B777343 : Blo 459783 777343 := bstep (se 1 (by rfl) ⟨583007, by rfl⟩ : syracuseStep 777343 = 1166015) B1166015
theorem B582815 : Blo 459783 582815 := bstep (se 1 (by rfl) ⟨437111, by rfl⟩ : syracuseStep 582815 = 874223) B874223
theorem B780475 : Blo 459783 780475 := bstep (se 1 (by rfl) ⟨585356, by rfl⟩ : syracuseStep 780475 = 1170713) B1170713
theorem B4419143 : Blo 459783 4419143 := bstep (se 1 (by rfl) ⟨3314357, by rfl⟩ : syracuseStep 4419143 = 6628715) B6628715
theorem B520447 : Blo 459783 520447 := bstep (se 1 (by rfl) ⟨390335, by rfl⟩ : syracuseStep 520447 = 780671) B780671
theorem B10023263 : Blo 459783 10023263 := bstep (se 1 (by rfl) ⟨7517447, by rfl⟩ : syracuseStep 10023263 = 15034895) B15034895
theorem B1111321 : Blo 459783 1111321 := bstep (se 2 (by rfl) ⟨416745, by rfl⟩ : syracuseStep 1111321 = 833491) B833491
theorem B13334003 : Blo 459783 13334003 := bstep (se 1 (by rfl) ⟨10000502, by rfl⟩ : syracuseStep 13334003 = 20001005) B20001005
theorem B5241509 : Blo 459783 5241509 := bstep (se 4 (by rfl) ⟨491391, by rfl⟩ : syracuseStep 5241509 = 982783) B982783
theorem B49217341 : Blo 459783 49217341 := bstep (se 3 (by rfl) ⟨9228251, by rfl⟩ : syracuseStep 49217341 = 18456503) B18456503
theorem B3506489 : Blo 459783 3506489 := bstep (se 2 (by rfl) ⟨1314933, by rfl⟩ : syracuseStep 3506489 = 2629867) B2629867
theorem B4424219 : Blo 459783 4424219 := bstep (se 1 (by rfl) ⟨3318164, by rfl⟩ : syracuseStep 4424219 = 6636329) B6636329
theorem B460031 : Blo 459783 460031 := bstep (se 1 (by rfl) ⟨345023, by rfl⟩ : syracuseStep 460031 = 690047) B690047
theorem B7112063 : Blo 459783 7112063 := bstep (se 1 (by rfl) ⟨5334047, by rfl⟩ : syracuseStep 7112063 = 10668095) B10668095
theorem B460263 : Blo 459783 460263 := bstep (se 1 (by rfl) ⟨345197, by rfl⟩ : syracuseStep 460263 = 690395) B690395
theorem B1967753 : Blo 459783 1967753 := bstep (se 2 (by rfl) ⟨737907, by rfl⟩ : syracuseStep 1967753 = 1475815) B1475815
theorem B460571 : Blo 459783 460571 := bstep (se 1 (by rfl) ⟨345428, by rfl⟩ : syracuseStep 460571 = 690857) B690857
theorem B460703 : Blo 459783 460703 := bstep (se 1 (by rfl) ⟨345527, by rfl⟩ : syracuseStep 460703 = 691055) B691055
theorem B1247201 : Blo 459783 1247201 := bstep (se 2 (by rfl) ⟨467700, by rfl⟩ : syracuseStep 1247201 = 935401) B935401
theorem B2820091 : Blo 459783 2820091 := bstep (se 1 (by rfl) ⟨2115068, by rfl⟩ : syracuseStep 2820091 = 4230137) B4230137
theorem B461279 : Blo 459783 461279 := bstep (se 1 (by rfl) ⟨345959, by rfl⟩ : syracuseStep 461279 = 691919) B691919
theorem B1968695 : Blo 459783 1968695 := bstep (se 1 (by rfl) ⟨1476521, by rfl⟩ : syracuseStep 1968695 = 2953043) B2953043
theorem B461467 : Blo 459783 461467 := bstep (se 1 (by rfl) ⟨346100, by rfl⟩ : syracuseStep 461467 = 692201) B692201
theorem B461983 : Blo 459783 461983 := bstep (se 1 (by rfl) ⟨346487, by rfl⟩ : syracuseStep 461983 = 692975) B692975
theorem B1248679 : Blo 459783 1248679 := bstep (se 1 (by rfl) ⟨936509, by rfl⟩ : syracuseStep 1248679 = 1873019) B1873019
theorem B2625311 : Blo 459783 2625311 := bstep (se 1 (by rfl) ⟨1968983, by rfl⟩ : syracuseStep 2625311 = 3937967) B3937967
theorem B11374519 : Blo 459783 11374519 := bstep (se 1 (by rfl) ⟨8530889, by rfl⟩ : syracuseStep 11374519 = 17061779) B17061779
theorem B462879 : Blo 459783 462879 := bstep (se 1 (by rfl) ⟨347159, by rfl⟩ : syracuseStep 462879 = 694319) B694319
theorem B659711 : Blo 459783 659711 := bstep (se 1 (by rfl) ⟨494783, by rfl⟩ : syracuseStep 659711 = 989567) B989567
theorem B692711 : Blo 459783 692711 := bstep (se 1 (by rfl) ⟨519533, by rfl⟩ : syracuseStep 692711 = 1039067) B1039067
theorem B3216115 : Blo 459783 3216115 := bstep (se 1 (by rfl) ⟨2412086, by rfl⟩ : syracuseStep 3216115 = 4824173) B4824173
theorem B693929 : Blo 459783 693929 := bstep (se 2 (by rfl) ⟨260223, by rfl⟩ : syracuseStep 693929 = 520447) B520447
theorem B1481761 : Blo 459783 1481761 := bstep (se 2 (by rfl) ⟨555660, by rfl⟩ : syracuseStep 1481761 = 1111321) B1111321
theorem B8889335 : Blo 459783 8889335 := bstep (se 1 (by rfl) ⟨6667001, by rfl⟩ : syracuseStep 8889335 = 13334003) B13334003
theorem B1748051 : Blo 459783 1748051 := bstep (se 1 (by rfl) ⟨1311038, by rfl⟩ : syracuseStep 1748051 = 2622077) B2622077
theorem B14430797 : Blo 459783 14430797 := bstep (se 3 (by rfl) ⟨2705774, by rfl⟩ : syracuseStep 14430797 = 5411549) B5411549
theorem B3519611 : Blo 459783 3519611 := bstep (se 1 (by rfl) ⟨2639708, by rfl⟩ : syracuseStep 3519611 = 5279417) B5279417
theorem B1554173 : Blo 459783 1554173 := bstep (se 3 (by rfl) ⟨291407, by rfl⟩ : syracuseStep 1554173 = 582815) B582815
theorem B964775 : Blo 459783 964775 := bstep (se 1 (by rfl) ⟨723581, by rfl⟩ : syracuseStep 964775 = 1447163) B1447163
theorem B3948425 : Blo 459783 3948425 := bstep (se 2 (by rfl) ⟨1480659, by rfl⟩ : syracuseStep 3948425 = 2961319) B2961319
theorem B2539775 : Blo 459783 2539775 := bstep (se 1 (by rfl) ⟨1904831, by rfl⟩ : syracuseStep 2539775 = 3809663) B3809663
theorem B1164527 : Blo 459783 1164527 := bstep (se 1 (by rfl) ⟨873395, by rfl⟩ : syracuseStep 1164527 = 1746791) B1746791
theorem B14928097 : Blo 459783 14928097 := bstep (se 2 (by rfl) ⟨5598036, by rfl⟩ : syracuseStep 14928097 = 11196073) B11196073
theorem B1757011 : Blo 459783 1757011 := bstep (se 1 (by rfl) ⟨1317758, by rfl⟩ : syracuseStep 1757011 = 2635517) B2635517
theorem B1036457 : Blo 459783 1036457 := bstep (se 2 (by rfl) ⟨388671, by rfl⟩ : syracuseStep 1036457 = 777343) B777343
theorem B3494339 : Blo 459783 3494339 := bstep (se 1 (by rfl) ⟨2620754, by rfl⟩ : syracuseStep 3494339 = 5241509) B5241509
theorem B65623121 : Blo 459783 65623121 := bstep (se 2 (by rfl) ⟨24608670, by rfl⟩ : syracuseStep 65623121 = 49217341) B49217341
theorem B1562651 : Blo 459783 1562651 := bstep (se 1 (by rfl) ⟨1171988, by rfl⟩ : syracuseStep 1562651 = 2343977) B2343977
theorem B1563947 : Blo 459783 1563947 := bstep (se 1 (by rfl) ⟨1172960, by rfl⟩ : syracuseStep 1563947 = 2345921) B2345921
theorem B1564379 : Blo 459783 1564379 := bstep (se 1 (by rfl) ⟨1173284, by rfl⟩ : syracuseStep 1564379 = 2346569) B2346569
theorem B1171199 : Blo 459783 1171199 := bstep (se 1 (by rfl) ⟨878399, by rfl⟩ : syracuseStep 1171199 = 1756799) B1756799
theorem B1040633 : Blo 459783 1040633 := bstep (se 2 (by rfl) ⟨390237, by rfl⟩ : syracuseStep 1040633 = 780475) B780475
theorem B1040831 : Blo 459783 1040831 := bstep (se 1 (by rfl) ⟨780623, by rfl⟩ : syracuseStep 1040831 = 1561247) B1561247
theorem B779807 : Blo 459783 779807 := bstep (se 1 (by rfl) ⟨584855, by rfl⟩ : syracuseStep 779807 = 1169711) B1169711
theorem B2946095 : Blo 459783 2946095 := bstep (se 1 (by rfl) ⟨2209571, by rfl⟩ : syracuseStep 2946095 = 4419143) B4419143
theorem B6682175 : Blo 459783 6682175 := bstep (se 1 (by rfl) ⟨5011631, by rfl⟩ : syracuseStep 6682175 = 10023263) B10023263
theorem B2949479 : Blo 459783 2949479 := bstep (se 1 (by rfl) ⟨2212109, by rfl⟩ : syracuseStep 2949479 = 4424219) B4424219
theorem B1312463 : Blo 459783 1312463 := bstep (se 1 (by rfl) ⟨984347, by rfl⟩ : syracuseStep 1312463 = 1968695) B1968695
theorem B690971 : Blo 459783 690971 := bstep (se 1 (by rfl) ⟨518228, by rfl⟩ : syracuseStep 690971 = 1036457) B1036457
theorem B2329559 : Blo 459783 2329559 := bstep (se 1 (by rfl) ⟨1747169, by rfl⟩ : syracuseStep 2329559 = 3494339) B3494339
theorem B461807 : Blo 459783 461807 := bstep (se 1 (by rfl) ⟨346355, by rfl⟩ : syracuseStep 461807 = 692711) B692711
theorem B43748747 : Blo 459783 43748747 := bstep (se 1 (by rfl) ⟨32811560, by rfl⟩ : syracuseStep 43748747 = 65623121) B65623121
theorem B462619 : Blo 459783 462619 := bstep (se 1 (by rfl) ⟨346964, by rfl⟩ : syracuseStep 462619 = 693929) B693929
theorem B5247341 : Blo 459783 5247341 := bstep (se 3 (by rfl) ⟨983876, by rfl⟩ : syracuseStep 5247341 = 1967753) B1967753
theorem B693755 : Blo 459783 693755 := bstep (se 1 (by rfl) ⟨520316, by rfl⟩ : syracuseStep 693755 = 1040633) B1040633
theorem B693887 : Blo 459783 693887 := bstep (se 1 (by rfl) ⟨520415, by rfl⟩ : syracuseStep 693887 = 1040831) B1040831
theorem B6659621 : Blo 459783 6659621 := bstep (se 4 (by rfl) ⟨624339, by rfl⟩ : syracuseStep 6659621 = 1248679) B1248679
theorem B1975681 : Blo 459783 1975681 := bstep (se 2 (by rfl) ⟨740880, by rfl⟩ : syracuseStep 1975681 = 1481761) B1481761
theorem B2632283 : Blo 459783 2632283 := bstep (se 1 (by rfl) ⟨1974212, by rfl⟩ : syracuseStep 2632283 = 3948425) B3948425
theorem B2337659 : Blo 459783 2337659 := bstep (se 1 (by rfl) ⟨1753244, by rfl⟩ : syracuseStep 2337659 = 3506489) B3506489
theorem B831467 : Blo 459783 831467 := bstep (se 1 (by rfl) ⟨623600, by rfl⟩ : syracuseStep 831467 = 1247201) B1247201
theorem B1750207 : Blo 459783 1750207 := bstep (se 1 (by rfl) ⟨1312655, by rfl⟩ : syracuseStep 1750207 = 2625311) B2625311
theorem B19904129 : Blo 459783 19904129 := bstep (se 2 (by rfl) ⟨7464048, by rfl⟩ : syracuseStep 19904129 = 14928097) B14928097
theorem B2342681 : Blo 459783 2342681 := bstep (se 2 (by rfl) ⟨878505, by rfl⟩ : syracuseStep 2342681 = 1757011) B1757011
theorem B1165367 : Blo 459783 1165367 := bstep (se 1 (by rfl) ⟨874025, by rfl⟩ : syracuseStep 1165367 = 1748051) B1748051
theorem B9620531 : Blo 459783 9620531 := bstep (se 1 (by rfl) ⟨7215398, by rfl⟩ : syracuseStep 9620531 = 14430797) B14430797
theorem B2346407 : Blo 459783 2346407 := bstep (se 1 (by rfl) ⟨1759805, by rfl⟩ : syracuseStep 2346407 = 3519611) B3519611
theorem B1036115 : Blo 459783 1036115 := bstep (se 1 (by rfl) ⟨777086, by rfl⟩ : syracuseStep 1036115 = 1554173) B1554173
theorem B643183 : Blo 459783 643183 := bstep (se 1 (by rfl) ⟨482387, by rfl⟩ : syracuseStep 643183 = 964775) B964775
theorem B1693183 : Blo 459783 1693183 := bstep (se 1 (by rfl) ⟨1269887, by rfl⟩ : syracuseStep 1693183 = 2539775) B2539775
theorem B1759229 : Blo 459783 1759229 := bstep (se 3 (by rfl) ⟨329855, by rfl⟩ : syracuseStep 1759229 = 659711) B659711
theorem B776351 : Blo 459783 776351 := bstep (se 1 (by rfl) ⟨582263, by rfl⟩ : syracuseStep 776351 = 1164527) B1164527
theorem B4741375 : Blo 459783 4741375 := bstep (se 1 (by rfl) ⟨3556031, by rfl⟩ : syracuseStep 4741375 = 7112063) B7112063
theorem B3760121 : Blo 459783 3760121 := bstep (se 2 (by rfl) ⟨1410045, by rfl⟩ : syracuseStep 3760121 = 2820091) B2820091
theorem B1041767 : Blo 459783 1041767 := bstep (se 1 (by rfl) ⟨781325, by rfl⟩ : syracuseStep 1041767 = 1562651) B1562651
theorem B1042631 : Blo 459783 1042631 := bstep (se 1 (by rfl) ⟨781973, by rfl⟩ : syracuseStep 1042631 = 1563947) B1563947
theorem B1042919 : Blo 459783 1042919 := bstep (se 1 (by rfl) ⟨782189, by rfl⟩ : syracuseStep 1042919 = 1564379) B1564379
theorem B780799 : Blo 459783 780799 := bstep (se 1 (by rfl) ⟨585599, by rfl⟩ : syracuseStep 780799 = 1171199) B1171199
theorem B15166025 : Blo 459783 15166025 := bstep (se 2 (by rfl) ⟨5687259, by rfl⟩ : syracuseStep 15166025 = 11374519) B11374519
theorem B5926223 : Blo 459783 5926223 := bstep (se 1 (by rfl) ⟨4444667, by rfl⟩ : syracuseStep 5926223 = 8889335) B8889335
theorem B4288153 : Blo 459783 4288153 := bstep (se 2 (by rfl) ⟨1608057, by rfl⟩ : syracuseStep 4288153 = 3216115) B3216115
theorem B519871 : Blo 459783 519871 := bstep (se 1 (by rfl) ⟨389903, by rfl⟩ : syracuseStep 519871 = 779807) B779807
theorem B1964063 : Blo 459783 1964063 := bstep (se 1 (by rfl) ⟨1473047, by rfl⟩ : syracuseStep 1964063 = 2946095) B2946095
theorem B4454783 : Blo 459783 4454783 := bstep (se 1 (by rfl) ⟨3341087, by rfl⟩ : syracuseStep 4454783 = 6682175) B6682175
theorem B1966319 : Blo 459783 1966319 := bstep (se 1 (by rfl) ⟨1474739, by rfl⟩ : syracuseStep 1966319 = 2949479) B2949479
theorem B460647 : Blo 459783 460647 := bstep (se 1 (by rfl) ⟨345485, by rfl⟩ : syracuseStep 460647 = 690971) B690971
theorem B29165831 : Blo 459783 29165831 := bstep (se 1 (by rfl) ⟨21874373, by rfl⟩ : syracuseStep 29165831 = 43748747) B43748747
theorem B690743 : Blo 459783 690743 := bstep (se 1 (by rfl) ⟨518057, by rfl⟩ : syracuseStep 690743 = 1036115) B1036115
theorem B462503 : Blo 459783 462503 := bstep (se 1 (by rfl) ⟨346877, by rfl⟩ : syracuseStep 462503 = 693755) B693755
theorem B462591 : Blo 459783 462591 := bstep (se 1 (by rfl) ⟨346943, by rfl⟩ : syracuseStep 462591 = 693887) B693887
theorem B693161 : Blo 459783 693161 := bstep (se 2 (by rfl) ⟨259935, by rfl⟩ : syracuseStep 693161 = 519871) B519871
theorem B694511 : Blo 459783 694511 := bstep (se 1 (by rfl) ⟨520883, by rfl⟩ : syracuseStep 694511 = 1041767) B1041767
theorem B695087 : Blo 459783 695087 := bstep (se 1 (by rfl) ⟨521315, by rfl⟩ : syracuseStep 695087 = 1042631) B1042631
theorem B2333609 : Blo 459783 2333609 := bstep (se 2 (by rfl) ⟨875103, by rfl⟩ : syracuseStep 2333609 = 1750207) B1750207
theorem B695279 : Blo 459783 695279 := bstep (se 1 (by rfl) ⟨521459, by rfl⟩ : syracuseStep 695279 = 1042919) B1042919
theorem B2634241 : Blo 459783 2634241 := bstep (se 2 (by rfl) ⟨987840, by rfl⟩ : syracuseStep 2634241 = 1975681) B1975681
theorem B1553039 : Blo 459783 1553039 := bstep (se 1 (by rfl) ⟨1164779, by rfl⟩ : syracuseStep 1553039 = 2329559) B2329559
theorem B5717537 : Blo 459783 5717537 := bstep (se 2 (by rfl) ⟨2144076, by rfl⟩ : syracuseStep 5717537 = 4288153) B4288153
theorem B4439747 : Blo 459783 4439747 := bstep (se 1 (by rfl) ⟨3329810, by rfl⟩ : syracuseStep 4439747 = 6659621) B6659621
theorem B2506747 : Blo 459783 2506747 := bstep (se 1 (by rfl) ⟨1880060, by rfl⟩ : syracuseStep 2506747 = 3760121) B3760121
theorem B10110683 : Blo 459783 10110683 := bstep (se 1 (by rfl) ⟨7583012, by rfl⟩ : syracuseStep 10110683 = 15166025) B15166025
theorem B1754855 : Blo 459783 1754855 := bstep (se 1 (by rfl) ⟨1316141, by rfl⟩ : syracuseStep 1754855 = 2632283) B2632283
theorem B1558439 : Blo 459783 1558439 := bstep (se 1 (by rfl) ⟨1168829, by rfl⟩ : syracuseStep 1558439 = 2337659) B2337659
theorem B3950815 : Blo 459783 3950815 := bstep (se 1 (by rfl) ⟨2963111, by rfl⟩ : syracuseStep 3950815 = 5926223) B5926223
theorem B2969855 : Blo 459783 2969855 := bstep (se 1 (by rfl) ⟨2227391, by rfl⟩ : syracuseStep 2969855 = 4454783) B4454783
theorem B1561787 : Blo 459783 1561787 := bstep (se 1 (by rfl) ⟨1171340, by rfl⟩ : syracuseStep 1561787 = 2342681) B2342681
theorem B874975 : Blo 459783 874975 := bstep (se 1 (by rfl) ⟨656231, by rfl⟩ : syracuseStep 874975 = 1312463) B1312463
theorem B776911 : Blo 459783 776911 := bstep (se 1 (by rfl) ⟨582683, by rfl⟩ : syracuseStep 776911 = 1165367) B1165367
theorem B6413687 : Blo 459783 6413687 := bstep (se 1 (by rfl) ⟨4810265, by rfl⟩ : syracuseStep 6413687 = 9620531) B9620531
theorem B1564271 : Blo 459783 1564271 := bstep (se 1 (by rfl) ⟨1173203, by rfl⟩ : syracuseStep 1564271 = 2346407) B2346407
theorem B13721237 : Blo 459783 13721237 := bstep (se 6 (by rfl) ⟨321591, by rfl⟩ : syracuseStep 13721237 = 643183) B643183
theorem B3498227 : Blo 459783 3498227 := bstep (se 1 (by rfl) ⟨2623670, by rfl⟩ : syracuseStep 3498227 = 5247341) B5247341
theorem B1041065 : Blo 459783 1041065 := bstep (se 2 (by rfl) ⟨390399, by rfl⟩ : syracuseStep 1041065 = 780799) B780799
theorem B1172819 : Blo 459783 1172819 := bstep (se 1 (by rfl) ⟨879614, by rfl⟩ : syracuseStep 1172819 = 1759229) B1759229
theorem B517567 : Blo 459783 517567 := bstep (se 1 (by rfl) ⟨388175, by rfl⟩ : syracuseStep 517567 = 776351) B776351
theorem B2257577 : Blo 459783 2257577 := bstep (se 2 (by rfl) ⟨846591, by rfl⟩ : syracuseStep 2257577 = 1693183) B1693183
theorem B554311 : Blo 459783 554311 := bstep (se 1 (by rfl) ⟨415733, by rfl⟩ : syracuseStep 554311 = 831467) B831467
theorem B6321833 : Blo 459783 6321833 := bstep (se 2 (by rfl) ⟨2370687, by rfl⟩ : syracuseStep 6321833 = 4741375) B4741375
theorem B13269419 : Blo 459783 13269419 := bstep (se 1 (by rfl) ⟨9952064, by rfl⟩ : syracuseStep 13269419 = 19904129) B19904129
theorem B1309375 : Blo 459783 1309375 := bstep (se 1 (by rfl) ⟨982031, by rfl⟩ : syracuseStep 1309375 = 1964063) B1964063
theorem B1310879 : Blo 459783 1310879 := bstep (se 1 (by rfl) ⟨983159, by rfl⟩ : syracuseStep 1310879 = 1966319) B1966319
theorem B460495 : Blo 459783 460495 := bstep (se 1 (by rfl) ⟨345371, by rfl⟩ : syracuseStep 460495 = 690743) B690743
theorem B690089 : Blo 459783 690089 := bstep (se 2 (by rfl) ⟨258783, by rfl⟩ : syracuseStep 690089 = 517567) B517567
theorem B462107 : Blo 459783 462107 := bstep (se 1 (by rfl) ⟨346580, by rfl⟩ : syracuseStep 462107 = 693161) B693161
theorem B463007 : Blo 459783 463007 := bstep (se 1 (by rfl) ⟨347255, by rfl⟩ : syracuseStep 463007 = 694511) B694511
theorem B463391 : Blo 459783 463391 := bstep (se 1 (by rfl) ⟨347543, by rfl⟩ : syracuseStep 463391 = 695087) B695087
theorem B463519 : Blo 459783 463519 := bstep (se 1 (by rfl) ⟨347639, by rfl⟩ : syracuseStep 463519 = 695279) B695279
theorem B9147491 : Blo 459783 9147491 := bstep (se 1 (by rfl) ⟨6860618, by rfl⟩ : syracuseStep 9147491 = 13721237) B13721237
theorem B2332151 : Blo 459783 2332151 := bstep (se 1 (by rfl) ⟨1749113, by rfl⟩ : syracuseStep 2332151 = 3498227) B3498227
theorem B694043 : Blo 459783 694043 := bstep (se 1 (by rfl) ⟨520532, by rfl⟩ : syracuseStep 694043 = 1041065) B1041065
theorem B3512321 : Blo 459783 3512321 := bstep (se 2 (by rfl) ⟨1317120, by rfl⟩ : syracuseStep 3512321 = 2634241) B2634241
theorem B1745833 : Blo 459783 1745833 := bstep (se 2 (by rfl) ⟨654687, by rfl⟩ : syracuseStep 1745833 = 1309375) B1309375
theorem B3811691 : Blo 459783 3811691 := bstep (se 1 (by rfl) ⟨2858768, by rfl⟩ : syracuseStep 3811691 = 5717537) B5717537
theorem B2959831 : Blo 459783 2959831 := bstep (se 1 (by rfl) ⟨2219873, by rfl⟩ : syracuseStep 2959831 = 4439747) B4439747
theorem B19443887 : Blo 459783 19443887 := bstep (se 1 (by rfl) ⟨14582915, by rfl⟩ : syracuseStep 19443887 = 29165831) B29165831
theorem B1979903 : Blo 459783 1979903 := bstep (se 1 (by rfl) ⟨1484927, by rfl⟩ : syracuseStep 1979903 = 2969855) B2969855
theorem B1555739 : Blo 459783 1555739 := bstep (se 1 (by rfl) ⟨1166804, by rfl⟩ : syracuseStep 1555739 = 2333609) B2333609
theorem B4275791 : Blo 459783 4275791 := bstep (se 1 (by rfl) ⟨3206843, by rfl⟩ : syracuseStep 4275791 = 6413687) B6413687
theorem B739081 : Blo 459783 739081 := bstep (se 2 (by rfl) ⟨277155, by rfl⟩ : syracuseStep 739081 = 554311) B554311
theorem B1035359 : Blo 459783 1035359 := bstep (se 1 (by rfl) ⟨776519, by rfl⟩ : syracuseStep 1035359 = 1553039) B1553039
theorem B1166633 : Blo 459783 1166633 := bstep (se 2 (by rfl) ⟨437487, by rfl⟩ : syracuseStep 1166633 = 874975) B874975
theorem B1035881 : Blo 459783 1035881 := bstep (se 2 (by rfl) ⟨388455, by rfl⟩ : syracuseStep 1035881 = 776911) B776911
theorem B4214555 : Blo 459783 4214555 := bstep (se 1 (by rfl) ⟨3160916, by rfl⟩ : syracuseStep 4214555 = 6321833) B6321833
theorem B6740455 : Blo 459783 6740455 := bstep (se 1 (by rfl) ⟨5055341, by rfl⟩ : syracuseStep 6740455 = 10110683) B10110683
theorem B1169903 : Blo 459783 1169903 := bstep (se 1 (by rfl) ⟨877427, by rfl⟩ : syracuseStep 1169903 = 1754855) B1754855
theorem B1038959 : Blo 459783 1038959 := bstep (se 1 (by rfl) ⟨779219, by rfl⟩ : syracuseStep 1038959 = 1558439) B1558439
theorem B5267753 : Blo 459783 5267753 := bstep (se 2 (by rfl) ⟨1975407, by rfl⟩ : syracuseStep 5267753 = 3950815) B3950815
theorem B1041191 : Blo 459783 1041191 := bstep (se 1 (by rfl) ⟨780893, by rfl⟩ : syracuseStep 1041191 = 1561787) B1561787
theorem B1042847 : Blo 459783 1042847 := bstep (se 1 (by rfl) ⟨782135, by rfl⟩ : syracuseStep 1042847 = 1564271) B1564271
theorem B781879 : Blo 459783 781879 := bstep (se 1 (by rfl) ⟨586409, by rfl⟩ : syracuseStep 781879 = 1172819) B1172819
theorem B1505051 : Blo 459783 1505051 := bstep (se 1 (by rfl) ⟨1128788, by rfl⟩ : syracuseStep 1505051 = 2257577) B2257577
theorem B8846279 : Blo 459783 8846279 := bstep (se 1 (by rfl) ⟨6634709, by rfl⟩ : syracuseStep 8846279 = 13269419) B13269419
theorem B3342329 : Blo 459783 3342329 := bstep (se 2 (by rfl) ⟨1253373, by rfl⟩ : syracuseStep 3342329 = 2506747) B2506747
theorem B2327777 : Blo 459783 2327777 := bstep (se 2 (by rfl) ⟨872916, by rfl⟩ : syracuseStep 2327777 = 1745833) B1745833
theorem B460059 : Blo 459783 460059 := bstep (se 1 (by rfl) ⟨345044, by rfl⟩ : syracuseStep 460059 = 690089) B690089
theorem B690239 : Blo 459783 690239 := bstep (se 1 (by rfl) ⟨517679, by rfl⟩ : syracuseStep 690239 = 1035359) B1035359
theorem B985441 : Blo 459783 985441 := bstep (se 2 (by rfl) ⟨369540, by rfl⟩ : syracuseStep 985441 = 739081) B739081
theorem B690587 : Blo 459783 690587 := bstep (se 1 (by rfl) ⟨517940, by rfl⟩ : syracuseStep 690587 = 1035881) B1035881
theorem B6098327 : Blo 459783 6098327 := bstep (se 1 (by rfl) ⟨4573745, by rfl⟩ : syracuseStep 6098327 = 9147491) B9147491
theorem B462695 : Blo 459783 462695 := bstep (se 1 (by rfl) ⟨347021, by rfl⟩ : syracuseStep 462695 = 694043) B694043
theorem B692639 : Blo 459783 692639 := bstep (se 1 (by rfl) ⟨519479, by rfl⟩ : syracuseStep 692639 = 1038959) B1038959
theorem B3511835 : Blo 459783 3511835 := bstep (se 1 (by rfl) ⟨2633876, by rfl⟩ : syracuseStep 3511835 = 5267753) B5267753
theorem B694127 : Blo 459783 694127 := bstep (se 1 (by rfl) ⟨520595, by rfl⟩ : syracuseStep 694127 = 1041191) B1041191
theorem B695231 : Blo 459783 695231 := bstep (se 1 (by rfl) ⟨521423, by rfl⟩ : syracuseStep 695231 = 1042847) B1042847
theorem B8987273 : Blo 459783 8987273 := bstep (se 2 (by rfl) ⟨3370227, by rfl⟩ : syracuseStep 8987273 = 6740455) B6740455
theorem B1319935 : Blo 459783 1319935 := bstep (se 1 (by rfl) ⟨989951, by rfl⟩ : syracuseStep 1319935 = 1979903) B1979903
theorem B3946441 : Blo 459783 3946441 := bstep (se 2 (by rfl) ⟨1479915, by rfl⟩ : syracuseStep 3946441 = 2959831) B2959831
theorem B1554767 : Blo 459783 1554767 := bstep (se 1 (by rfl) ⟨1166075, by rfl⟩ : syracuseStep 1554767 = 2332151) B2332151
theorem B2341547 : Blo 459783 2341547 := bstep (se 1 (by rfl) ⟨1756160, by rfl⟩ : syracuseStep 2341547 = 3512321) B3512321
theorem B2541127 : Blo 459783 2541127 := bstep (se 1 (by rfl) ⟨1905845, by rfl⟩ : syracuseStep 2541127 = 3811691) B3811691
theorem B12962591 : Blo 459783 12962591 := bstep (se 1 (by rfl) ⟨9721943, by rfl⟩ : syracuseStep 12962591 = 19443887) B19443887
theorem B1003367 : Blo 459783 1003367 := bstep (se 1 (by rfl) ⟨752525, by rfl⟩ : syracuseStep 1003367 = 1505051) B1505051
theorem B1037159 : Blo 459783 1037159 := bstep (se 1 (by rfl) ⟨777869, by rfl⟩ : syracuseStep 1037159 = 1555739) B1555739
theorem B873919 : Blo 459783 873919 := bstep (se 1 (by rfl) ⟨655439, by rfl⟩ : syracuseStep 873919 = 1310879) B1310879
theorem B777755 : Blo 459783 777755 := bstep (se 1 (by rfl) ⟨583316, by rfl⟩ : syracuseStep 777755 = 1166633) B1166633
theorem B2809703 : Blo 459783 2809703 := bstep (se 1 (by rfl) ⟨2107277, by rfl⟩ : syracuseStep 2809703 = 4214555) B4214555
theorem B779935 : Blo 459783 779935 := bstep (se 1 (by rfl) ⟨584951, by rfl⟩ : syracuseStep 779935 = 1169903) B1169903
theorem B1042505 : Blo 459783 1042505 := bstep (se 2 (by rfl) ⟨390939, by rfl⟩ : syracuseStep 1042505 = 781879) B781879
theorem B5897519 : Blo 459783 5897519 := bstep (se 1 (by rfl) ⟨4423139, by rfl⟩ : syracuseStep 5897519 = 8846279) B8846279
theorem B2850527 : Blo 459783 2850527 := bstep (se 1 (by rfl) ⟨2137895, by rfl⟩ : syracuseStep 2850527 = 4275791) B4275791
theorem B2228219 : Blo 459783 2228219 := bstep (se 1 (by rfl) ⟨1671164, by rfl⟩ : syracuseStep 2228219 = 3342329) B3342329
theorem B460159 : Blo 459783 460159 := bstep (se 1 (by rfl) ⟨345119, by rfl⟩ : syracuseStep 460159 = 690239) B690239
theorem B460391 : Blo 459783 460391 := bstep (se 1 (by rfl) ⟨345293, by rfl⟩ : syracuseStep 460391 = 690587) B690587
theorem B4065551 : Blo 459783 4065551 := bstep (se 1 (by rfl) ⟨3049163, by rfl⟩ : syracuseStep 4065551 = 6098327) B6098327
theorem B461759 : Blo 459783 461759 := bstep (se 1 (by rfl) ⟨346319, by rfl⟩ : syracuseStep 461759 = 692639) B692639
theorem B1313921 : Blo 459783 1313921 := bstep (se 2 (by rfl) ⟨492720, by rfl⟩ : syracuseStep 1313921 = 985441) B985441
theorem B691439 : Blo 459783 691439 := bstep (se 1 (by rfl) ⟨518579, by rfl⟩ : syracuseStep 691439 = 1037159) B1037159
theorem B462751 : Blo 459783 462751 := bstep (se 1 (by rfl) ⟨347063, by rfl⟩ : syracuseStep 462751 = 694127) B694127
theorem B463487 : Blo 459783 463487 := bstep (se 1 (by rfl) ⟨347615, by rfl⟩ : syracuseStep 463487 = 695231) B695231
theorem B1873135 : Blo 459783 1873135 := bstep (se 1 (by rfl) ⟨1404851, by rfl⟩ : syracuseStep 1873135 = 2809703) B2809703
theorem B695003 : Blo 459783 695003 := bstep (se 1 (by rfl) ⟨521252, by rfl⟩ : syracuseStep 695003 = 1042505) B1042505
theorem B1485479 : Blo 459783 1485479 := bstep (se 1 (by rfl) ⟨1114109, by rfl⟩ : syracuseStep 1485479 = 2228219) B2228219
theorem B1551851 : Blo 459783 1551851 := bstep (se 1 (by rfl) ⟨1163888, by rfl⟩ : syracuseStep 1551851 = 2327777) B2327777
theorem B3388169 : Blo 459783 3388169 := bstep (se 2 (by rfl) ⟨1270563, by rfl⟩ : syracuseStep 3388169 = 2541127) B2541127
theorem B668911 : Blo 459783 668911 := bstep (se 1 (by rfl) ⟨501683, by rfl⟩ : syracuseStep 668911 = 1003367) B1003367
theorem B2341223 : Blo 459783 2341223 := bstep (se 1 (by rfl) ⟨1755917, by rfl⟩ : syracuseStep 2341223 = 3511835) B3511835
theorem B1165225 : Blo 459783 1165225 := bstep (se 2 (by rfl) ⟨436959, by rfl⟩ : syracuseStep 1165225 = 873919) B873919
theorem B5261921 : Blo 459783 5261921 := bstep (se 2 (by rfl) ⟨1973220, by rfl⟩ : syracuseStep 5261921 = 3946441) B3946441
theorem B1036511 : Blo 459783 1036511 := bstep (se 1 (by rfl) ⟨777383, by rfl⟩ : syracuseStep 1036511 = 1554767) B1554767
theorem B1561031 : Blo 459783 1561031 := bstep (se 1 (by rfl) ⟨1170773, by rfl⟩ : syracuseStep 1561031 = 2341547) B2341547
theorem B1759913 : Blo 459783 1759913 := bstep (se 2 (by rfl) ⟨659967, by rfl⟩ : syracuseStep 1759913 = 1319935) B1319935
theorem B8641727 : Blo 459783 8641727 := bstep (se 1 (by rfl) ⟨6481295, by rfl⟩ : syracuseStep 8641727 = 12962591) B12962591
theorem B1039913 : Blo 459783 1039913 := bstep (se 2 (by rfl) ⟨389967, by rfl⟩ : syracuseStep 1039913 = 779935) B779935
theorem B518503 : Blo 459783 518503 := bstep (se 1 (by rfl) ⟨388877, by rfl⟩ : syracuseStep 518503 = 777755) B777755
theorem B5991515 : Blo 459783 5991515 := bstep (se 1 (by rfl) ⟨4493636, by rfl⟩ : syracuseStep 5991515 = 8987273) B8987273
theorem B3931679 : Blo 459783 3931679 := bstep (se 1 (by rfl) ⟨2948759, by rfl⟩ : syracuseStep 3931679 = 5897519) B5897519
theorem B1900351 : Blo 459783 1900351 := bstep (se 1 (by rfl) ⟨1425263, by rfl⟩ : syracuseStep 1900351 = 2850527) B2850527
theorem B3507947 : Blo 459783 3507947 := bstep (se 1 (by rfl) ⟨2630960, by rfl⟩ : syracuseStep 3507947 = 5261921) B5261921
theorem B460959 : Blo 459783 460959 := bstep (se 1 (by rfl) ⟨345719, by rfl⟩ : syracuseStep 460959 = 691439) B691439
theorem B691007 : Blo 459783 691007 := bstep (se 1 (by rfl) ⟨518255, by rfl⟩ : syracuseStep 691007 = 1036511) B1036511
theorem B691337 : Blo 459783 691337 := bstep (se 2 (by rfl) ⟨259251, by rfl⟩ : syracuseStep 691337 = 518503) B518503
theorem B463335 : Blo 459783 463335 := bstep (se 1 (by rfl) ⟨347501, by rfl⟩ : syracuseStep 463335 = 695003) B695003
theorem B693275 : Blo 459783 693275 := bstep (se 1 (by rfl) ⟨519956, by rfl⟩ : syracuseStep 693275 = 1039913) B1039913
theorem B2497513 : Blo 459783 2497513 := bstep (se 2 (by rfl) ⟨936567, by rfl⟩ : syracuseStep 2497513 = 1873135) B1873135
theorem B891881 : Blo 459783 891881 := bstep (se 2 (by rfl) ⟨334455, by rfl⟩ : syracuseStep 891881 = 668911) B668911
theorem B990319 : Blo 459783 990319 := bstep (se 1 (by rfl) ⟨742739, by rfl⟩ : syracuseStep 990319 = 1485479) B1485479
theorem B10135205 : Blo 459783 10135205 := bstep (se 4 (by rfl) ⟨950175, by rfl⟩ : syracuseStep 10135205 = 1900351) B1900351
theorem B1553633 : Blo 459783 1553633 := bstep (se 2 (by rfl) ⟨582612, by rfl⟩ : syracuseStep 1553633 = 1165225) B1165225
theorem B1034567 : Blo 459783 1034567 := bstep (se 1 (by rfl) ⟨775925, by rfl⟩ : syracuseStep 1034567 = 1551851) B1551851
theorem B1560815 : Blo 459783 1560815 := bstep (se 1 (by rfl) ⟨1170611, by rfl⟩ : syracuseStep 1560815 = 2341223) B2341223
theorem B2710367 : Blo 459783 2710367 := bstep (se 1 (by rfl) ⟨2032775, by rfl⟩ : syracuseStep 2710367 = 4065551) B4065551
theorem B875947 : Blo 459783 875947 := bstep (se 1 (by rfl) ⟨656960, by rfl⟩ : syracuseStep 875947 = 1313921) B1313921
theorem B1040687 : Blo 459783 1040687 := bstep (se 1 (by rfl) ⟨780515, by rfl⟩ : syracuseStep 1040687 = 1561031) B1561031
theorem B1173275 : Blo 459783 1173275 := bstep (se 1 (by rfl) ⟨879956, by rfl⟩ : syracuseStep 1173275 = 1759913) B1759913
theorem B5761151 : Blo 459783 5761151 := bstep (se 1 (by rfl) ⟨4320863, by rfl⟩ : syracuseStep 5761151 = 8641727) B8641727
theorem B3994343 : Blo 459783 3994343 := bstep (se 1 (by rfl) ⟨2995757, by rfl⟩ : syracuseStep 3994343 = 5991515) B5991515
theorem B2258779 : Blo 459783 2258779 := bstep (se 1 (by rfl) ⟨1694084, by rfl⟩ : syracuseStep 2258779 = 3388169) B3388169
theorem B2621119 : Blo 459783 2621119 := bstep (se 1 (by rfl) ⟨1965839, by rfl⟩ : syracuseStep 2621119 = 3931679) B3931679
theorem B689711 : Blo 459783 689711 := bstep (se 1 (by rfl) ⟨517283, by rfl⟩ : syracuseStep 689711 = 1034567) B1034567
theorem B460671 : Blo 459783 460671 := bstep (se 1 (by rfl) ⟨345503, by rfl⟩ : syracuseStep 460671 = 691007) B691007
theorem B460891 : Blo 459783 460891 := bstep (se 1 (by rfl) ⟨345668, by rfl⟩ : syracuseStep 460891 = 691337) B691337
theorem B462183 : Blo 459783 462183 := bstep (se 1 (by rfl) ⟨346637, by rfl⟩ : syracuseStep 462183 = 693275) B693275
theorem B1806911 : Blo 459783 1806911 := bstep (se 1 (by rfl) ⟨1355183, by rfl⟩ : syracuseStep 1806911 = 2710367) B2710367
theorem B594587 : Blo 459783 594587 := bstep (se 1 (by rfl) ⟨445940, by rfl⟩ : syracuseStep 594587 = 891881) B891881
theorem B693791 : Blo 459783 693791 := bstep (se 1 (by rfl) ⟨520343, by rfl⟩ : syracuseStep 693791 = 1040687) B1040687
theorem B6756803 : Blo 459783 6756803 := bstep (se 1 (by rfl) ⟨5067602, by rfl⟩ : syracuseStep 6756803 = 10135205) B10135205
theorem B3840767 : Blo 459783 3840767 := bstep (se 1 (by rfl) ⟨2880575, by rfl⟩ : syracuseStep 3840767 = 5761151) B5761151
theorem B2662895 : Blo 459783 2662895 := bstep (se 1 (by rfl) ⟨1997171, by rfl⟩ : syracuseStep 2662895 = 3994343) B3994343
theorem B1320425 : Blo 459783 1320425 := bstep (se 2 (by rfl) ⟨495159, by rfl⟩ : syracuseStep 1320425 = 990319) B990319
theorem B2338631 : Blo 459783 2338631 := bstep (se 1 (by rfl) ⟨1753973, by rfl⟩ : syracuseStep 2338631 = 3507947) B3507947
theorem B1035755 : Blo 459783 1035755 := bstep (se 1 (by rfl) ⟨776816, by rfl⟩ : syracuseStep 1035755 = 1553633) B1553633
theorem B3330017 : Blo 459783 3330017 := bstep (se 2 (by rfl) ⟨1248756, by rfl⟩ : syracuseStep 3330017 = 2497513) B2497513
theorem B1167929 : Blo 459783 1167929 := bstep (se 2 (by rfl) ⟨437973, by rfl⟩ : syracuseStep 1167929 = 875947) B875947
theorem B3494825 : Blo 459783 3494825 := bstep (se 2 (by rfl) ⟨1310559, by rfl⟩ : syracuseStep 3494825 = 2621119) B2621119
theorem B1040543 : Blo 459783 1040543 := bstep (se 1 (by rfl) ⟨780407, by rfl⟩ : syracuseStep 1040543 = 1560815) B1560815
theorem B782183 : Blo 459783 782183 := bstep (se 1 (by rfl) ⟨586637, by rfl⟩ : syracuseStep 782183 = 1173275) B1173275
theorem B3011705 : Blo 459783 3011705 := bstep (se 2 (by rfl) ⟨1129389, by rfl⟩ : syracuseStep 3011705 = 2258779) B2258779
theorem B459807 : Blo 459783 459807 := bstep (se 1 (by rfl) ⟨344855, by rfl⟩ : syracuseStep 459807 = 689711) B689711
theorem B690503 : Blo 459783 690503 := bstep (se 1 (by rfl) ⟨517877, by rfl⟩ : syracuseStep 690503 = 1035755) B1035755
theorem B2329883 : Blo 459783 2329883 := bstep (se 1 (by rfl) ⟨1747412, by rfl⟩ : syracuseStep 2329883 = 3494825) B3494825
theorem B462527 : Blo 459783 462527 := bstep (se 1 (by rfl) ⟨346895, by rfl⟩ : syracuseStep 462527 = 693791) B693791
theorem B2560511 : Blo 459783 2560511 := bstep (se 1 (by rfl) ⟨1920383, by rfl⟩ : syracuseStep 2560511 = 3840767) B3840767
theorem B693695 : Blo 459783 693695 := bstep (se 1 (by rfl) ⟨520271, by rfl⟩ : syracuseStep 693695 = 1040543) B1040543
theorem B2007803 : Blo 459783 2007803 := bstep (se 1 (by rfl) ⟨1505852, by rfl⟩ : syracuseStep 2007803 = 3011705) B3011705
theorem B1585565 : Blo 459783 1585565 := bstep (se 3 (by rfl) ⟨297293, by rfl⟩ : syracuseStep 1585565 = 594587) B594587
theorem B4504535 : Blo 459783 4504535 := bstep (se 1 (by rfl) ⟨3378401, by rfl⟩ : syracuseStep 4504535 = 6756803) B6756803
theorem B1559087 : Blo 459783 1559087 := bstep (se 1 (by rfl) ⟨1169315, by rfl⟩ : syracuseStep 1559087 = 2338631) B2338631
theorem B7101053 : Blo 459783 7101053 := bstep (se 3 (by rfl) ⟨1331447, by rfl⟩ : syracuseStep 7101053 = 2662895) B2662895
theorem B2220011 : Blo 459783 2220011 := bstep (se 1 (by rfl) ⟨1665008, by rfl⟩ : syracuseStep 2220011 = 3330017) B3330017
theorem B778619 : Blo 459783 778619 := bstep (se 1 (by rfl) ⟨583964, by rfl⟩ : syracuseStep 778619 = 1167929) B1167929
theorem B1204607 : Blo 459783 1204607 := bstep (se 1 (by rfl) ⟨903455, by rfl⟩ : syracuseStep 1204607 = 1806911) B1806911
theorem B880283 : Blo 459783 880283 := bstep (se 1 (by rfl) ⟨660212, by rfl⟩ : syracuseStep 880283 = 1320425) B1320425
theorem B521455 : Blo 459783 521455 := bstep (se 1 (by rfl) ⟨391091, by rfl⟩ : syracuseStep 521455 = 782183) B782183
theorem B460335 : Blo 459783 460335 := bstep (se 1 (by rfl) ⟨345251, by rfl⟩ : syracuseStep 460335 = 690503) B690503
theorem B1707007 : Blo 459783 1707007 := bstep (se 1 (by rfl) ⟨1280255, by rfl⟩ : syracuseStep 1707007 = 2560511) B2560511
theorem B462463 : Blo 459783 462463 := bstep (se 1 (by rfl) ⟨346847, by rfl⟩ : syracuseStep 462463 = 693695) B693695
theorem B1480007 : Blo 459783 1480007 := bstep (se 1 (by rfl) ⟨1110005, by rfl⟩ : syracuseStep 1480007 = 2220011) B2220011
theorem B695273 : Blo 459783 695273 := bstep (se 2 (by rfl) ⟨260727, by rfl⟩ : syracuseStep 695273 = 521455) B521455
theorem B1057043 : Blo 459783 1057043 := bstep (se 1 (by rfl) ⟨792782, by rfl⟩ : syracuseStep 1057043 = 1585565) B1585565
theorem B1553255 : Blo 459783 1553255 := bstep (se 1 (by rfl) ⟨1164941, by rfl⟩ : syracuseStep 1553255 = 2329883) B2329883
theorem B4734035 : Blo 459783 4734035 := bstep (se 1 (by rfl) ⟨3550526, by rfl⟩ : syracuseStep 4734035 = 7101053) B7101053
theorem B803071 : Blo 459783 803071 := bstep (se 1 (by rfl) ⟨602303, by rfl⟩ : syracuseStep 803071 = 1204607) B1204607
theorem B3003023 : Blo 459783 3003023 := bstep (se 1 (by rfl) ⟨2252267, by rfl⟩ : syracuseStep 3003023 = 4504535) B4504535
theorem B1039391 : Blo 459783 1039391 := bstep (se 1 (by rfl) ⟨779543, by rfl⟩ : syracuseStep 1039391 = 1559087) B1559087
theorem B519079 : Blo 459783 519079 := bstep (se 1 (by rfl) ⟨389309, by rfl⟩ : syracuseStep 519079 = 778619) B778619
theorem B1338535 : Blo 459783 1338535 := bstep (se 1 (by rfl) ⟨1003901, by rfl⟩ : syracuseStep 1338535 = 2007803) B2007803
theorem B586855 : Blo 459783 586855 := bstep (se 1 (by rfl) ⟨440141, by rfl⟩ : syracuseStep 586855 = 880283) B880283
theorem B2002015 : Blo 459783 2002015 := bstep (se 1 (by rfl) ⟨1501511, by rfl⟩ : syracuseStep 2002015 = 3003023) B3003023
theorem B986671 : Blo 459783 986671 := bstep (se 1 (by rfl) ⟨740003, by rfl⟩ : syracuseStep 986671 = 1480007) B1480007
theorem B692105 : Blo 459783 692105 := bstep (se 2 (by rfl) ⟨259539, by rfl⟩ : syracuseStep 692105 = 519079) B519079
theorem B463515 : Blo 459783 463515 := bstep (se 1 (by rfl) ⟨347636, by rfl⟩ : syracuseStep 463515 = 695273) B695273
theorem B692927 : Blo 459783 692927 := bstep (se 1 (by rfl) ⟨519695, by rfl⟩ : syracuseStep 692927 = 1039391) B1039391
theorem B3156023 : Blo 459783 3156023 := bstep (se 1 (by rfl) ⟨2367017, by rfl⟩ : syracuseStep 3156023 = 4734035) B4734035
theorem B2276009 : Blo 459783 2276009 := bstep (se 2 (by rfl) ⟨853503, by rfl⟩ : syracuseStep 2276009 = 1707007) B1707007
theorem B1784713 : Blo 459783 1784713 := bstep (se 2 (by rfl) ⟨669267, by rfl⟩ : syracuseStep 1784713 = 1338535) B1338535
theorem B704695 : Blo 459783 704695 := bstep (se 1 (by rfl) ⟨528521, by rfl⟩ : syracuseStep 704695 = 1057043) B1057043
theorem B1035503 : Blo 459783 1035503 := bstep (se 1 (by rfl) ⟨776627, by rfl⟩ : syracuseStep 1035503 = 1553255) B1553255
theorem B1070761 : Blo 459783 1070761 := bstep (se 2 (by rfl) ⟨401535, by rfl⟩ : syracuseStep 1070761 = 803071) B803071
theorem B782473 : Blo 459783 782473 := bstep (se 2 (by rfl) ⟨293427, by rfl⟩ : syracuseStep 782473 = 586855) B586855
theorem B690335 : Blo 459783 690335 := bstep (se 1 (by rfl) ⟨517751, by rfl⟩ : syracuseStep 690335 = 1035503) B1035503
theorem B461403 : Blo 459783 461403 := bstep (se 1 (by rfl) ⟨346052, by rfl⟩ : syracuseStep 461403 = 692105) B692105
theorem B461951 : Blo 459783 461951 := bstep (se 1 (by rfl) ⟨346463, by rfl⟩ : syracuseStep 461951 = 692927) B692927
theorem B1315561 : Blo 459783 1315561 := bstep (se 2 (by rfl) ⟨493335, by rfl⟩ : syracuseStep 1315561 = 986671) B986671
theorem B2104015 : Blo 459783 2104015 := bstep (se 1 (by rfl) ⟨1578011, by rfl⟩ : syracuseStep 2104015 = 3156023) B3156023
theorem B1517339 : Blo 459783 1517339 := bstep (se 1 (by rfl) ⟨1138004, by rfl⟩ : syracuseStep 1517339 = 2276009) B2276009
theorem B1427681 : Blo 459783 1427681 := bstep (se 2 (by rfl) ⟨535380, by rfl⟩ : syracuseStep 1427681 = 1070761) B1070761
theorem B2379617 : Blo 459783 2379617 := bstep (se 2 (by rfl) ⟨892356, by rfl⟩ : syracuseStep 2379617 = 1784713) B1784713
theorem B939593 : Blo 459783 939593 := bstep (se 2 (by rfl) ⟨352347, by rfl⟩ : syracuseStep 939593 = 704695) B704695
theorem B1043297 : Blo 459783 1043297 := bstep (se 2 (by rfl) ⟨391236, by rfl⟩ : syracuseStep 1043297 = 782473) B782473
theorem B10677413 : Blo 459783 10677413 := bstep (se 4 (by rfl) ⟨1001007, by rfl⟩ : syracuseStep 10677413 = 2002015) B2002015
theorem B460223 : Blo 459783 460223 := bstep (se 1 (by rfl) ⟨345167, by rfl⟩ : syracuseStep 460223 = 690335) B690335
theorem B951787 : Blo 459783 951787 := bstep (se 1 (by rfl) ⟨713840, by rfl⟩ : syracuseStep 951787 = 1427681) B1427681
theorem B626395 : Blo 459783 626395 := bstep (se 1 (by rfl) ⟨469796, by rfl⟩ : syracuseStep 626395 = 939593) B939593
theorem B695531 : Blo 459783 695531 := bstep (se 1 (by rfl) ⟨521648, by rfl⟩ : syracuseStep 695531 = 1043297) B1043297
theorem B7118275 : Blo 459783 7118275 := bstep (se 1 (by rfl) ⟨5338706, by rfl⟩ : syracuseStep 7118275 = 10677413) B10677413
theorem B1586411 : Blo 459783 1586411 := bstep (se 1 (by rfl) ⟨1189808, by rfl⟩ : syracuseStep 1586411 = 2379617) B2379617
theorem B1754081 : Blo 459783 1754081 := bstep (se 2 (by rfl) ⟨657780, by rfl⟩ : syracuseStep 1754081 = 1315561) B1315561
theorem B2805353 : Blo 459783 2805353 := bstep (se 2 (by rfl) ⟨1052007, by rfl⟩ : syracuseStep 2805353 = 2104015) B2104015
theorem B1011559 : Blo 459783 1011559 := bstep (se 1 (by rfl) ⟨758669, by rfl⟩ : syracuseStep 1011559 = 1517339) B1517339
theorem B1870235 : Blo 459783 1870235 := bstep (se 1 (by rfl) ⟨1402676, by rfl⟩ : syracuseStep 1870235 = 2805353) B2805353
theorem B463687 : Blo 459783 463687 := bstep (se 1 (by rfl) ⟨347765, by rfl⟩ : syracuseStep 463687 = 695531) B695531
theorem B1348745 : Blo 459783 1348745 := bstep (se 2 (by rfl) ⟨505779, by rfl⟩ : syracuseStep 1348745 = 1011559) B1011559
theorem B1057607 : Blo 459783 1057607 := bstep (se 1 (by rfl) ⟨793205, by rfl⟩ : syracuseStep 1057607 = 1586411) B1586411
theorem B835193 : Blo 459783 835193 := bstep (se 2 (by rfl) ⟨313197, by rfl⟩ : syracuseStep 835193 = 626395) B626395
theorem B9491033 : Blo 459783 9491033 := bstep (se 2 (by rfl) ⟨3559137, by rfl⟩ : syracuseStep 9491033 = 7118275) B7118275
theorem B1169387 : Blo 459783 1169387 := bstep (se 1 (by rfl) ⟨877040, by rfl⟩ : syracuseStep 1169387 = 1754081) B1754081
theorem B1269049 : Blo 459783 1269049 := bstep (se 2 (by rfl) ⟨475893, by rfl⟩ : syracuseStep 1269049 = 951787) B951787
theorem B1246823 : Blo 459783 1246823 := bstep (se 1 (by rfl) ⟨935117, by rfl⟩ : syracuseStep 1246823 = 1870235) B1870235
theorem B25309421 : Blo 459783 25309421 := bstep (se 3 (by rfl) ⟨4745516, by rfl⟩ : syracuseStep 25309421 = 9491033) B9491033
theorem B705071 : Blo 459783 705071 := bstep (se 1 (by rfl) ⟨528803, by rfl⟩ : syracuseStep 705071 = 1057607) B1057607
theorem B1692065 : Blo 459783 1692065 := bstep (se 2 (by rfl) ⟨634524, by rfl⟩ : syracuseStep 1692065 = 1269049) B1269049
theorem B3596653 : Blo 459783 3596653 := bstep (se 3 (by rfl) ⟨674372, by rfl⟩ : syracuseStep 3596653 = 1348745) B1348745
theorem B779591 : Blo 459783 779591 := bstep (se 1 (by rfl) ⟨584693, by rfl⟩ : syracuseStep 779591 = 1169387) B1169387
theorem B556795 : Blo 459783 556795 := bstep (se 1 (by rfl) ⟨417596, by rfl⟩ : syracuseStep 556795 = 835193) B835193
theorem B4795537 : Blo 459783 4795537 := bstep (se 2 (by rfl) ⟨1798326, by rfl⟩ : syracuseStep 4795537 = 3596653) B3596653
theorem B831215 : Blo 459783 831215 := bstep (se 1 (by rfl) ⟨623411, by rfl⟩ : syracuseStep 831215 = 1246823) B1246823
theorem B1880189 : Blo 459783 1880189 := bstep (se 3 (by rfl) ⟨352535, by rfl⟩ : syracuseStep 1880189 = 705071) B705071
theorem B1128043 : Blo 459783 1128043 := bstep (se 1 (by rfl) ⟨846032, by rfl⟩ : syracuseStep 1128043 = 1692065) B1692065
theorem B742393 : Blo 459783 742393 := bstep (se 2 (by rfl) ⟨278397, by rfl⟩ : syracuseStep 742393 = 556795) B556795
theorem B519727 : Blo 459783 519727 := bstep (se 1 (by rfl) ⟨389795, by rfl⟩ : syracuseStep 519727 = 779591) B779591
theorem B16872947 : Blo 459783 16872947 := bstep (se 1 (by rfl) ⟨12654710, by rfl⟩ : syracuseStep 16872947 = 25309421) B25309421
theorem B6394049 : Blo 459783 6394049 := bstep (se 2 (by rfl) ⟨2397768, by rfl⟩ : syracuseStep 6394049 = 4795537) B4795537
theorem B692969 : Blo 459783 692969 := bstep (se 2 (by rfl) ⟨259863, by rfl⟩ : syracuseStep 692969 = 519727) B519727
theorem B989857 : Blo 459783 989857 := bstep (se 2 (by rfl) ⟨371196, by rfl⟩ : syracuseStep 989857 = 742393) B742393
theorem B1253459 : Blo 459783 1253459 := bstep (se 1 (by rfl) ⟨940094, by rfl⟩ : syracuseStep 1253459 = 1880189) B1880189
theorem B11248631 : Blo 459783 11248631 := bstep (se 1 (by rfl) ⟨8436473, by rfl⟩ : syracuseStep 11248631 = 16872947) B16872947
theorem B1504057 : Blo 459783 1504057 := bstep (se 2 (by rfl) ⟨564021, by rfl⟩ : syracuseStep 1504057 = 1128043) B1128043
theorem B554143 : Blo 459783 554143 := bstep (se 1 (by rfl) ⟨415607, by rfl⟩ : syracuseStep 554143 = 831215) B831215
theorem B4262699 : Blo 459783 4262699 := bstep (se 1 (by rfl) ⟨3197024, by rfl⟩ : syracuseStep 4262699 = 6394049) B6394049
theorem B461979 : Blo 459783 461979 := bstep (se 1 (by rfl) ⟨346484, by rfl⟩ : syracuseStep 461979 = 692969) B692969
theorem B2005409 : Blo 459783 2005409 := bstep (se 2 (by rfl) ⟨752028, by rfl⟩ : syracuseStep 2005409 = 1504057) B1504057
theorem B1319809 : Blo 459783 1319809 := bstep (se 2 (by rfl) ⟨494928, by rfl⟩ : syracuseStep 1319809 = 989857) B989857
theorem B835639 : Blo 459783 835639 := bstep (se 1 (by rfl) ⟨626729, by rfl⟩ : syracuseStep 835639 = 1253459) B1253459
theorem B738857 : Blo 459783 738857 := bstep (se 2 (by rfl) ⟨277071, by rfl⟩ : syracuseStep 738857 = 554143) B554143
theorem B7499087 : Blo 459783 7499087 := bstep (se 1 (by rfl) ⟨5624315, by rfl⟩ : syracuseStep 7499087 = 11248631) B11248631
theorem B4456741 : Blo 459783 4456741 := bstep (se 4 (by rfl) ⟨417819, by rfl⟩ : syracuseStep 4456741 = 835639) B835639
theorem B492571 : Blo 459783 492571 := bstep (se 1 (by rfl) ⟨369428, by rfl⟩ : syracuseStep 492571 = 738857) B738857
theorem B5347757 : Blo 459783 5347757 := bstep (se 3 (by rfl) ⟨1002704, by rfl⟩ : syracuseStep 5347757 = 2005409) B2005409
theorem B4999391 : Blo 459783 4999391 := bstep (se 1 (by rfl) ⟨3749543, by rfl⟩ : syracuseStep 4999391 = 7499087) B7499087
theorem B1759745 : Blo 459783 1759745 := bstep (se 2 (by rfl) ⟨659904, by rfl⟩ : syracuseStep 1759745 = 1319809) B1319809
theorem B2841799 : Blo 459783 2841799 := bstep (se 1 (by rfl) ⟨2131349, by rfl⟩ : syracuseStep 2841799 = 4262699) B4262699
theorem B656761 : Blo 459783 656761 := bstep (se 2 (by rfl) ⟨246285, by rfl⟩ : syracuseStep 656761 = 492571) B492571
theorem B5942321 : Blo 459783 5942321 := bstep (se 2 (by rfl) ⟨2228370, by rfl⟩ : syracuseStep 5942321 = 4456741) B4456741
theorem B3789065 : Blo 459783 3789065 := bstep (se 2 (by rfl) ⟨1420899, by rfl⟩ : syracuseStep 3789065 = 2841799) B2841799
theorem B3332927 : Blo 459783 3332927 := bstep (se 1 (by rfl) ⟨2499695, by rfl⟩ : syracuseStep 3332927 = 4999391) B4999391
theorem B3565171 : Blo 459783 3565171 := bstep (se 1 (by rfl) ⟨2673878, by rfl⟩ : syracuseStep 3565171 = 5347757) B5347757
theorem B1173163 : Blo 459783 1173163 := bstep (se 1 (by rfl) ⟨879872, by rfl⟩ : syracuseStep 1173163 = 1759745) B1759745
theorem B4753561 : Blo 459783 4753561 := bstep (se 2 (by rfl) ⟨1782585, by rfl⟩ : syracuseStep 4753561 = 3565171) B3565171
theorem B10104173 : Blo 459783 10104173 := bstep (se 3 (by rfl) ⟨1894532, by rfl⟩ : syracuseStep 10104173 = 3789065) B3789065
theorem B875681 : Blo 459783 875681 := bstep (se 2 (by rfl) ⟨328380, by rfl⟩ : syracuseStep 875681 = 656761) B656761
theorem B1564217 : Blo 459783 1564217 := bstep (se 2 (by rfl) ⟨586581, by rfl⟩ : syracuseStep 1564217 = 1173163) B1173163
theorem B2221951 : Blo 459783 2221951 := bstep (se 1 (by rfl) ⟨1666463, by rfl⟩ : syracuseStep 2221951 = 3332927) B3332927
theorem B3961547 : Blo 459783 3961547 := bstep (se 1 (by rfl) ⟨2971160, by rfl⟩ : syracuseStep 3961547 = 5942321) B5942321
theorem B2962601 : Blo 459783 2962601 := bstep (se 2 (by rfl) ⟨1110975, by rfl⟩ : syracuseStep 2962601 = 2221951) B2221951
theorem B6338081 : Blo 459783 6338081 := bstep (se 2 (by rfl) ⟨2376780, by rfl⟩ : syracuseStep 6338081 = 4753561) B4753561
theorem B6736115 : Blo 459783 6736115 := bstep (se 1 (by rfl) ⟨5052086, by rfl⟩ : syracuseStep 6736115 = 10104173) B10104173
theorem B2641031 : Blo 459783 2641031 := bstep (se 1 (by rfl) ⟨1980773, by rfl⟩ : syracuseStep 2641031 = 3961547) B3961547
theorem B583787 : Blo 459783 583787 := bstep (se 1 (by rfl) ⟨437840, by rfl⟩ : syracuseStep 583787 = 875681) B875681
theorem B1042811 : Blo 459783 1042811 := bstep (se 1 (by rfl) ⟨782108, by rfl⟩ : syracuseStep 1042811 = 1564217) B1564217
theorem B4490743 : Blo 459783 4490743 := bstep (se 1 (by rfl) ⟨3368057, by rfl⟩ : syracuseStep 4490743 = 6736115) B6736115
theorem B695207 : Blo 459783 695207 := bstep (se 1 (by rfl) ⟨521405, by rfl⟩ : syracuseStep 695207 = 1042811) B1042811
theorem B1975067 : Blo 459783 1975067 := bstep (se 1 (by rfl) ⟨1481300, by rfl⟩ : syracuseStep 1975067 = 2962601) B2962601
theorem B1556765 : Blo 459783 1556765 := bstep (se 3 (by rfl) ⟨291893, by rfl⟩ : syracuseStep 1556765 = 583787) B583787
theorem B1760687 : Blo 459783 1760687 := bstep (se 1 (by rfl) ⟨1320515, by rfl⟩ : syracuseStep 1760687 = 2641031) B2641031
theorem B4225387 : Blo 459783 4225387 := bstep (se 1 (by rfl) ⟨3169040, by rfl⟩ : syracuseStep 4225387 = 6338081) B6338081
theorem B463471 : Blo 459783 463471 := bstep (se 1 (by rfl) ⟨347603, by rfl⟩ : syracuseStep 463471 = 695207) B695207
theorem B1316711 : Blo 459783 1316711 := bstep (se 1 (by rfl) ⟨987533, by rfl⟩ : syracuseStep 1316711 = 1975067) B1975067
theorem B1037843 : Blo 459783 1037843 := bstep (se 1 (by rfl) ⟨778382, by rfl⟩ : syracuseStep 1037843 = 1556765) B1556765
theorem B5987657 : Blo 459783 5987657 := bstep (se 2 (by rfl) ⟨2245371, by rfl⟩ : syracuseStep 5987657 = 4490743) B4490743
theorem B1173791 : Blo 459783 1173791 := bstep (se 1 (by rfl) ⟨880343, by rfl⟩ : syracuseStep 1173791 = 1760687) B1760687
theorem B5633849 : Blo 459783 5633849 := bstep (se 2 (by rfl) ⟨2112693, by rfl⟩ : syracuseStep 5633849 = 4225387) B4225387
theorem B691895 : Blo 459783 691895 := bstep (se 1 (by rfl) ⟨518921, by rfl⟩ : syracuseStep 691895 = 1037843) B1037843
theorem B3755899 : Blo 459783 3755899 := bstep (se 1 (by rfl) ⟨2816924, by rfl⟩ : syracuseStep 3755899 = 5633849) B5633849
theorem B877807 : Blo 459783 877807 := bstep (se 1 (by rfl) ⟨658355, by rfl⟩ : syracuseStep 877807 = 1316711) B1316711
theorem B3991771 : Blo 459783 3991771 := bstep (se 1 (by rfl) ⟨2993828, by rfl⟩ : syracuseStep 3991771 = 5987657) B5987657
theorem B782527 : Blo 459783 782527 := bstep (se 1 (by rfl) ⟨586895, by rfl⟩ : syracuseStep 782527 = 1173791) B1173791
theorem B461263 : Blo 459783 461263 := bstep (se 1 (by rfl) ⟨345947, by rfl⟩ : syracuseStep 461263 = 691895) B691895
theorem B5322361 : Blo 459783 5322361 := bstep (se 2 (by rfl) ⟨1995885, by rfl⟩ : syracuseStep 5322361 = 3991771) B3991771
theorem B1170409 : Blo 459783 1170409 := bstep (se 2 (by rfl) ⟨438903, by rfl⟩ : syracuseStep 1170409 = 877807) B877807
theorem B5007865 : Blo 459783 5007865 := bstep (se 2 (by rfl) ⟨1877949, by rfl⟩ : syracuseStep 5007865 = 3755899) B3755899
theorem B1043369 : Blo 459783 1043369 := bstep (se 2 (by rfl) ⟨391263, by rfl⟩ : syracuseStep 1043369 = 782527) B782527
theorem B695579 : Blo 459783 695579 := bstep (se 1 (by rfl) ⟨521684, by rfl⟩ : syracuseStep 695579 = 1043369) B1043369
theorem B7096481 : Blo 459783 7096481 := bstep (se 2 (by rfl) ⟨2661180, by rfl⟩ : syracuseStep 7096481 = 5322361) B5322361
theorem B1560545 : Blo 459783 1560545 := bstep (se 2 (by rfl) ⟨585204, by rfl⟩ : syracuseStep 1560545 = 1170409) B1170409
theorem B6677153 : Blo 459783 6677153 := bstep (se 2 (by rfl) ⟨2503932, by rfl⟩ : syracuseStep 6677153 = 5007865) B5007865
theorem B463719 : Blo 459783 463719 := bstep (se 1 (by rfl) ⟨347789, by rfl⟩ : syracuseStep 463719 = 695579) B695579
theorem B4730987 : Blo 459783 4730987 := bstep (se 1 (by rfl) ⟨3548240, by rfl⟩ : syracuseStep 4730987 = 7096481) B7096481
theorem B1040363 : Blo 459783 1040363 := bstep (se 1 (by rfl) ⟨780272, by rfl⟩ : syracuseStep 1040363 = 1560545) B1560545
theorem B4451435 : Blo 459783 4451435 := bstep (se 1 (by rfl) ⟨3338576, by rfl⟩ : syracuseStep 4451435 = 6677153) B6677153
theorem B693575 : Blo 459783 693575 := bstep (se 1 (by rfl) ⟨520181, by rfl⟩ : syracuseStep 693575 = 1040363) B1040363
theorem B3153991 : Blo 459783 3153991 := bstep (se 1 (by rfl) ⟨2365493, by rfl⟩ : syracuseStep 3153991 = 4730987) B4730987
theorem B2967623 : Blo 459783 2967623 := bstep (se 1 (by rfl) ⟨2225717, by rfl⟩ : syracuseStep 2967623 = 4451435) B4451435
theorem B462383 : Blo 459783 462383 := bstep (se 1 (by rfl) ⟨346787, by rfl⟩ : syracuseStep 462383 = 693575) B693575
theorem B4205321 : Blo 459783 4205321 := bstep (se 2 (by rfl) ⟨1576995, by rfl⟩ : syracuseStep 4205321 = 3153991) B3153991
theorem B1978415 : Blo 459783 1978415 := bstep (se 1 (by rfl) ⟨1483811, by rfl⟩ : syracuseStep 1978415 = 2967623) B2967623
theorem B1318943 : Blo 459783 1318943 := bstep (se 1 (by rfl) ⟨989207, by rfl⟩ : syracuseStep 1318943 = 1978415) B1978415
theorem B2803547 : Blo 459783 2803547 := bstep (se 1 (by rfl) ⟨2102660, by rfl⟩ : syracuseStep 2803547 = 4205321) B4205321
theorem B1869031 : Blo 459783 1869031 := bstep (se 1 (by rfl) ⟨1401773, by rfl⟩ : syracuseStep 1869031 = 2803547) B2803547
theorem B3517181 : Blo 459783 3517181 := bstep (se 3 (by rfl) ⟨659471, by rfl⟩ : syracuseStep 3517181 = 1318943) B1318943
theorem B2492041 : Blo 459783 2492041 := bstep (se 2 (by rfl) ⟨934515, by rfl⟩ : syracuseStep 2492041 = 1869031) B1869031
theorem B2344787 : Blo 459783 2344787 := bstep (se 1 (by rfl) ⟨1758590, by rfl⟩ : syracuseStep 2344787 = 3517181) B3517181
theorem B3322721 : Blo 459783 3322721 := bstep (se 2 (by rfl) ⟨1246020, by rfl⟩ : syracuseStep 3322721 = 2492041) B2492041
theorem B1563191 : Blo 459783 1563191 := bstep (se 1 (by rfl) ⟨1172393, by rfl⟩ : syracuseStep 1563191 = 2344787) B2344787
theorem B2215147 : Blo 459783 2215147 := bstep (se 1 (by rfl) ⟨1661360, by rfl⟩ : syracuseStep 2215147 = 3322721) B3322721
theorem B1042127 : Blo 459783 1042127 := bstep (se 1 (by rfl) ⟨781595, by rfl⟩ : syracuseStep 1042127 = 1563191) B1563191
theorem B2953529 : Blo 459783 2953529 := bstep (se 2 (by rfl) ⟨1107573, by rfl⟩ : syracuseStep 2953529 = 2215147) B2215147
theorem B694751 : Blo 459783 694751 := bstep (se 1 (by rfl) ⟨521063, by rfl⟩ : syracuseStep 694751 = 1042127) B1042127
theorem B1969019 : Blo 459783 1969019 := bstep (se 1 (by rfl) ⟨1476764, by rfl⟩ : syracuseStep 1969019 = 2953529) B2953529
theorem B463167 : Blo 459783 463167 := bstep (se 1 (by rfl) ⟨347375, by rfl⟩ : syracuseStep 463167 = 694751) B694751
theorem B1312679 : Blo 459783 1312679 := bstep (se 1 (by rfl) ⟨984509, by rfl⟩ : syracuseStep 1312679 = 1969019) B1969019
theorem B875119 : Blo 459783 875119 := bstep (se 1 (by rfl) ⟨656339, by rfl⟩ : syracuseStep 875119 = 1312679) B1312679
theorem B1166825 : Blo 459783 1166825 := bstep (se 2 (by rfl) ⟨437559, by rfl⟩ : syracuseStep 1166825 = 875119) B875119
theorem B777883 : Blo 459783 777883 := bstep (se 1 (by rfl) ⟨583412, by rfl⟩ : syracuseStep 777883 = 1166825) B1166825
theorem B1037177 : Blo 459783 1037177 := bstep (se 2 (by rfl) ⟨388941, by rfl⟩ : syracuseStep 1037177 = 777883) B777883
theorem B691451 : Blo 459783 691451 := bstep (se 1 (by rfl) ⟨518588, by rfl⟩ : syracuseStep 691451 = 1037177) B1037177
theorem B460967 : Blo 459783 460967 := bstep (se 1 (by rfl) ⟨345725, by rfl⟩ : syracuseStep 460967 = 691451) B691451

theorem C0 (j : ℕ) (h1 : 114945 ≤ j) (h2 : j ≤ 115644) : Blo 459783 (4 * j + 3) := by
  interval_cases j
  · exact B459783
  · exact B459787
  · exact B459791
  · exact B459795
  · exact B459799
  · exact B459803
  · exact B459807
  · exact B459811
  · exact B459815
  · exact B459819
  · exact B459823
  · exact B459827
  · exact B459831
  · exact B459835
  · exact B459839
  · exact B459843
  · exact B459847
  · exact B459851
  · exact B459855
  · exact B459859
  · exact B459863
  · exact B459867
  · exact B459871
  · exact B459875
  · exact B459879
  · exact B459883
  · exact B459887
  · exact B459891
  · exact B459895
  · exact B459899
  · exact B459903
  · exact B459907
  · exact B459911
  · exact B459915
  · exact B459919
  · exact B459923
  · exact B459927
  · exact B459931
  · exact B459935
  · exact B459939
  · exact B459943
  · exact B459947
  · exact B459951
  · exact B459955
  · exact B459959
  · exact B459963
  · exact B459967
  · exact B459971
  · exact B459975
  · exact B459979
  · exact B459983
  · exact B459987
  · exact B459991
  · exact B459995
  · exact B459999
  · exact B460003
  · exact B460007
  · exact B460011
  · exact B460015
  · exact B460019
  · exact B460023
  · exact B460027
  · exact B460031
  · exact B460035
  · exact B460039
  · exact B460043
  · exact B460047
  · exact B460051
  · exact B460055
  · exact B460059
  · exact B460063
  · exact B460067
  · exact B460071
  · exact B460075
  · exact B460079
  · exact B460083
  · exact B460087
  · exact B460091
  · exact B460095
  · exact B460099
  · exact B460103
  · exact B460107
  · exact B460111
  · exact B460115
  · exact B460119
  · exact B460123
  · exact B460127
  · exact B460131
  · exact B460135
  · exact B460139
  · exact B460143
  · exact B460147
  · exact B460151
  · exact B460155
  · exact B460159
  · exact B460163
  · exact B460167
  · exact B460171
  · exact B460175
  · exact B460179
  · exact B460183
  · exact B460187
  · exact B460191
  · exact B460195
  · exact B460199
  · exact B460203
  · exact B460207
  · exact B460211
  · exact B460215
  · exact B460219
  · exact B460223
  · exact B460227
  · exact B460231
  · exact B460235
  · exact B460239
  · exact B460243
  · exact B460247
  · exact B460251
  · exact B460255
  · exact B460259
  · exact B460263
  · exact B460267
  · exact B460271
  · exact B460275
  · exact B460279
  · exact B460283
  · exact B460287
  · exact B460291
  · exact B460295
  · exact B460299
  · exact B460303
  · exact B460307
  · exact B460311
  · exact B460315
  · exact B460319
  · exact B460323
  · exact B460327
  · exact B460331
  · exact B460335
  · exact B460339
  · exact B460343
  · exact B460347
  · exact B460351
  · exact B460355
  · exact B460359
  · exact B460363
  · exact B460367
  · exact B460371
  · exact B460375
  · exact B460379
  · exact B460383
  · exact B460387
  · exact B460391
  · exact B460395
  · exact B460399
  · exact B460403
  · exact B460407
  · exact B460411
  · exact B460415
  · exact B460419
  · exact B460423
  · exact B460427
  · exact B460431
  · exact B460435
  · exact B460439
  · exact B460443
  · exact B460447
  · exact B460451
  · exact B460455
  · exact B460459
  · exact B460463
  · exact B460467
  · exact B460471
  · exact B460475
  · exact B460479
  · exact B460483
  · exact B460487
  · exact B460491
  · exact B460495
  · exact B460499
  · exact B460503
  · exact B460507
  · exact B460511
  · exact B460515
  · exact B460519
  · exact B460523
  · exact B460527
  · exact B460531
  · exact B460535
  · exact B460539
  · exact B460543
  · exact B460547
  · exact B460551
  · exact B460555
  · exact B460559
  · exact B460563
  · exact B460567
  · exact B460571
  · exact B460575
  · exact B460579
  · exact B460583
  · exact B460587
  · exact B460591
  · exact B460595
  · exact B460599
  · exact B460603
  · exact B460607
  · exact B460611
  · exact B460615
  · exact B460619
  · exact B460623
  · exact B460627
  · exact B460631
  · exact B460635
  · exact B460639
  · exact B460643
  · exact B460647
  · exact B460651
  · exact B460655
  · exact B460659
  · exact B460663
  · exact B460667
  · exact B460671
  · exact B460675
  · exact B460679
  · exact B460683
  · exact B460687
  · exact B460691
  · exact B460695
  · exact B460699
  · exact B460703
  · exact B460707
  · exact B460711
  · exact B460715
  · exact B460719
  · exact B460723
  · exact B460727
  · exact B460731
  · exact B460735
  · exact B460739
  · exact B460743
  · exact B460747
  · exact B460751
  · exact B460755
  · exact B460759
  · exact B460763
  · exact B460767
  · exact B460771
  · exact B460775
  · exact B460779
  · exact B460783
  · exact B460787
  · exact B460791
  · exact B460795
  · exact B460799
  · exact B460803
  · exact B460807
  · exact B460811
  · exact B460815
  · exact B460819
  · exact B460823
  · exact B460827
  · exact B460831
  · exact B460835
  · exact B460839
  · exact B460843
  · exact B460847
  · exact B460851
  · exact B460855
  · exact B460859
  · exact B460863
  · exact B460867
  · exact B460871
  · exact B460875
  · exact B460879
  · exact B460883
  · exact B460887
  · exact B460891
  · exact B460895
  · exact B460899
  · exact B460903
  · exact B460907
  · exact B460911
  · exact B460915
  · exact B460919
  · exact B460923
  · exact B460927
  · exact B460931
  · exact B460935
  · exact B460939
  · exact B460943
  · exact B460947
  · exact B460951
  · exact B460955
  · exact B460959
  · exact B460963
  · exact B460967
  · exact B460971
  · exact B460975
  · exact B460979
  · exact B460983
  · exact B460987
  · exact B460991
  · exact B460995
  · exact B460999
  · exact B461003
  · exact B461007
  · exact B461011
  · exact B461015
  · exact B461019
  · exact B461023
  · exact B461027
  · exact B461031
  · exact B461035
  · exact B461039
  · exact B461043
  · exact B461047
  · exact B461051
  · exact B461055
  · exact B461059
  · exact B461063
  · exact B461067
  · exact B461071
  · exact B461075
  · exact B461079
  · exact B461083
  · exact B461087
  · exact B461091
  · exact B461095
  · exact B461099
  · exact B461103
  · exact B461107
  · exact B461111
  · exact B461115
  · exact B461119
  · exact B461123
  · exact B461127
  · exact B461131
  · exact B461135
  · exact B461139
  · exact B461143
  · exact B461147
  · exact B461151
  · exact B461155
  · exact B461159
  · exact B461163
  · exact B461167
  · exact B461171
  · exact B461175
  · exact B461179
  · exact B461183
  · exact B461187
  · exact B461191
  · exact B461195
  · exact B461199
  · exact B461203
  · exact B461207
  · exact B461211
  · exact B461215
  · exact B461219
  · exact B461223
  · exact B461227
  · exact B461231
  · exact B461235
  · exact B461239
  · exact B461243
  · exact B461247
  · exact B461251
  · exact B461255
  · exact B461259
  · exact B461263
  · exact B461267
  · exact B461271
  · exact B461275
  · exact B461279
  · exact B461283
  · exact B461287
  · exact B461291
  · exact B461295
  · exact B461299
  · exact B461303
  · exact B461307
  · exact B461311
  · exact B461315
  · exact B461319
  · exact B461323
  · exact B461327
  · exact B461331
  · exact B461335
  · exact B461339
  · exact B461343
  · exact B461347
  · exact B461351
  · exact B461355
  · exact B461359
  · exact B461363
  · exact B461367
  · exact B461371
  · exact B461375
  · exact B461379
  · exact B461383
  · exact B461387
  · exact B461391
  · exact B461395
  · exact B461399
  · exact B461403
  · exact B461407
  · exact B461411
  · exact B461415
  · exact B461419
  · exact B461423
  · exact B461427
  · exact B461431
  · exact B461435
  · exact B461439
  · exact B461443
  · exact B461447
  · exact B461451
  · exact B461455
  · exact B461459
  · exact B461463
  · exact B461467
  · exact B461471
  · exact B461475
  · exact B461479
  · exact B461483
  · exact B461487
  · exact B461491
  · exact B461495
  · exact B461499
  · exact B461503
  · exact B461507
  · exact B461511
  · exact B461515
  · exact B461519
  · exact B461523
  · exact B461527
  · exact B461531
  · exact B461535
  · exact B461539
  · exact B461543
  · exact B461547
  · exact B461551
  · exact B461555
  · exact B461559
  · exact B461563
  · exact B461567
  · exact B461571
  · exact B461575
  · exact B461579
  · exact B461583
  · exact B461587
  · exact B461591
  · exact B461595
  · exact B461599
  · exact B461603
  · exact B461607
  · exact B461611
  · exact B461615
  · exact B461619
  · exact B461623
  · exact B461627
  · exact B461631
  · exact B461635
  · exact B461639
  · exact B461643
  · exact B461647
  · exact B461651
  · exact B461655
  · exact B461659
  · exact B461663
  · exact B461667
  · exact B461671
  · exact B461675
  · exact B461679
  · exact B461683
  · exact B461687
  · exact B461691
  · exact B461695
  · exact B461699
  · exact B461703
  · exact B461707
  · exact B461711
  · exact B461715
  · exact B461719
  · exact B461723
  · exact B461727
  · exact B461731
  · exact B461735
  · exact B461739
  · exact B461743
  · exact B461747
  · exact B461751
  · exact B461755
  · exact B461759
  · exact B461763
  · exact B461767
  · exact B461771
  · exact B461775
  · exact B461779
  · exact B461783
  · exact B461787
  · exact B461791
  · exact B461795
  · exact B461799
  · exact B461803
  · exact B461807
  · exact B461811
  · exact B461815
  · exact B461819
  · exact B461823
  · exact B461827
  · exact B461831
  · exact B461835
  · exact B461839
  · exact B461843
  · exact B461847
  · exact B461851
  · exact B461855
  · exact B461859
  · exact B461863
  · exact B461867
  · exact B461871
  · exact B461875
  · exact B461879
  · exact B461883
  · exact B461887
  · exact B461891
  · exact B461895
  · exact B461899
  · exact B461903
  · exact B461907
  · exact B461911
  · exact B461915
  · exact B461919
  · exact B461923
  · exact B461927
  · exact B461931
  · exact B461935
  · exact B461939
  · exact B461943
  · exact B461947
  · exact B461951
  · exact B461955
  · exact B461959
  · exact B461963
  · exact B461967
  · exact B461971
  · exact B461975
  · exact B461979
  · exact B461983
  · exact B461987
  · exact B461991
  · exact B461995
  · exact B461999
  · exact B462003
  · exact B462007
  · exact B462011
  · exact B462015
  · exact B462019
  · exact B462023
  · exact B462027
  · exact B462031
  · exact B462035
  · exact B462039
  · exact B462043
  · exact B462047
  · exact B462051
  · exact B462055
  · exact B462059
  · exact B462063
  · exact B462067
  · exact B462071
  · exact B462075
  · exact B462079
  · exact B462083
  · exact B462087
  · exact B462091
  · exact B462095
  · exact B462099
  · exact B462103
  · exact B462107
  · exact B462111
  · exact B462115
  · exact B462119
  · exact B462123
  · exact B462127
  · exact B462131
  · exact B462135
  · exact B462139
  · exact B462143
  · exact B462147
  · exact B462151
  · exact B462155
  · exact B462159
  · exact B462163
  · exact B462167
  · exact B462171
  · exact B462175
  · exact B462179
  · exact B462183
  · exact B462187
  · exact B462191
  · exact B462195
  · exact B462199
  · exact B462203
  · exact B462207
  · exact B462211
  · exact B462215
  · exact B462219
  · exact B462223
  · exact B462227
  · exact B462231
  · exact B462235
  · exact B462239
  · exact B462243
  · exact B462247
  · exact B462251
  · exact B462255
  · exact B462259
  · exact B462263
  · exact B462267
  · exact B462271
  · exact B462275
  · exact B462279
  · exact B462283
  · exact B462287
  · exact B462291
  · exact B462295
  · exact B462299
  · exact B462303
  · exact B462307
  · exact B462311
  · exact B462315
  · exact B462319
  · exact B462323
  · exact B462327
  · exact B462331
  · exact B462335
  · exact B462339
  · exact B462343
  · exact B462347
  · exact B462351
  · exact B462355
  · exact B462359
  · exact B462363
  · exact B462367
  · exact B462371
  · exact B462375
  · exact B462379
  · exact B462383
  · exact B462387
  · exact B462391
  · exact B462395
  · exact B462399
  · exact B462403
  · exact B462407
  · exact B462411
  · exact B462415
  · exact B462419
  · exact B462423
  · exact B462427
  · exact B462431
  · exact B462435
  · exact B462439
  · exact B462443
  · exact B462447
  · exact B462451
  · exact B462455
  · exact B462459
  · exact B462463
  · exact B462467
  · exact B462471
  · exact B462475
  · exact B462479
  · exact B462483
  · exact B462487
  · exact B462491
  · exact B462495
  · exact B462499
  · exact B462503
  · exact B462507
  · exact B462511
  · exact B462515
  · exact B462519
  · exact B462523
  · exact B462527
  · exact B462531
  · exact B462535
  · exact B462539
  · exact B462543
  · exact B462547
  · exact B462551
  · exact B462555
  · exact B462559
  · exact B462563
  · exact B462567
  · exact B462571
  · exact B462575
  · exact B462579

theorem C1 (j : ℕ) (h1 : 115645 ≤ j) (h2 : j ≤ 115945) : Blo 459783 (4 * j + 3) := by
  interval_cases j
  · exact B462583
  · exact B462587
  · exact B462591
  · exact B462595
  · exact B462599
  · exact B462603
  · exact B462607
  · exact B462611
  · exact B462615
  · exact B462619
  · exact B462623
  · exact B462627
  · exact B462631
  · exact B462635
  · exact B462639
  · exact B462643
  · exact B462647
  · exact B462651
  · exact B462655
  · exact B462659
  · exact B462663
  · exact B462667
  · exact B462671
  · exact B462675
  · exact B462679
  · exact B462683
  · exact B462687
  · exact B462691
  · exact B462695
  · exact B462699
  · exact B462703
  · exact B462707
  · exact B462711
  · exact B462715
  · exact B462719
  · exact B462723
  · exact B462727
  · exact B462731
  · exact B462735
  · exact B462739
  · exact B462743
  · exact B462747
  · exact B462751
  · exact B462755
  · exact B462759
  · exact B462763
  · exact B462767
  · exact B462771
  · exact B462775
  · exact B462779
  · exact B462783
  · exact B462787
  · exact B462791
  · exact B462795
  · exact B462799
  · exact B462803
  · exact B462807
  · exact B462811
  · exact B462815
  · exact B462819
  · exact B462823
  · exact B462827
  · exact B462831
  · exact B462835
  · exact B462839
  · exact B462843
  · exact B462847
  · exact B462851
  · exact B462855
  · exact B462859
  · exact B462863
  · exact B462867
  · exact B462871
  · exact B462875
  · exact B462879
  · exact B462883
  · exact B462887
  · exact B462891
  · exact B462895
  · exact B462899
  · exact B462903
  · exact B462907
  · exact B462911
  · exact B462915
  · exact B462919
  · exact B462923
  · exact B462927
  · exact B462931
  · exact B462935
  · exact B462939
  · exact B462943
  · exact B462947
  · exact B462951
  · exact B462955
  · exact B462959
  · exact B462963
  · exact B462967
  · exact B462971
  · exact B462975
  · exact B462979
  · exact B462983
  · exact B462987
  · exact B462991
  · exact B462995
  · exact B462999
  · exact B463003
  · exact B463007
  · exact B463011
  · exact B463015
  · exact B463019
  · exact B463023
  · exact B463027
  · exact B463031
  · exact B463035
  · exact B463039
  · exact B463043
  · exact B463047
  · exact B463051
  · exact B463055
  · exact B463059
  · exact B463063
  · exact B463067
  · exact B463071
  · exact B463075
  · exact B463079
  · exact B463083
  · exact B463087
  · exact B463091
  · exact B463095
  · exact B463099
  · exact B463103
  · exact B463107
  · exact B463111
  · exact B463115
  · exact B463119
  · exact B463123
  · exact B463127
  · exact B463131
  · exact B463135
  · exact B463139
  · exact B463143
  · exact B463147
  · exact B463151
  · exact B463155
  · exact B463159
  · exact B463163
  · exact B463167
  · exact B463171
  · exact B463175
  · exact B463179
  · exact B463183
  · exact B463187
  · exact B463191
  · exact B463195
  · exact B463199
  · exact B463203
  · exact B463207
  · exact B463211
  · exact B463215
  · exact B463219
  · exact B463223
  · exact B463227
  · exact B463231
  · exact B463235
  · exact B463239
  · exact B463243
  · exact B463247
  · exact B463251
  · exact B463255
  · exact B463259
  · exact B463263
  · exact B463267
  · exact B463271
  · exact B463275
  · exact B463279
  · exact B463283
  · exact B463287
  · exact B463291
  · exact B463295
  · exact B463299
  · exact B463303
  · exact B463307
  · exact B463311
  · exact B463315
  · exact B463319
  · exact B463323
  · exact B463327
  · exact B463331
  · exact B463335
  · exact B463339
  · exact B463343
  · exact B463347
  · exact B463351
  · exact B463355
  · exact B463359
  · exact B463363
  · exact B463367
  · exact B463371
  · exact B463375
  · exact B463379
  · exact B463383
  · exact B463387
  · exact B463391
  · exact B463395
  · exact B463399
  · exact B463403
  · exact B463407
  · exact B463411
  · exact B463415
  · exact B463419
  · exact B463423
  · exact B463427
  · exact B463431
  · exact B463435
  · exact B463439
  · exact B463443
  · exact B463447
  · exact B463451
  · exact B463455
  · exact B463459
  · exact B463463
  · exact B463467
  · exact B463471
  · exact B463475
  · exact B463479
  · exact B463483
  · exact B463487
  · exact B463491
  · exact B463495
  · exact B463499
  · exact B463503
  · exact B463507
  · exact B463511
  · exact B463515
  · exact B463519
  · exact B463523
  · exact B463527
  · exact B463531
  · exact B463535
  · exact B463539
  · exact B463543
  · exact B463547
  · exact B463551
  · exact B463555
  · exact B463559
  · exact B463563
  · exact B463567
  · exact B463571
  · exact B463575
  · exact B463579
  · exact B463583
  · exact B463587
  · exact B463591
  · exact B463595
  · exact B463599
  · exact B463603
  · exact B463607
  · exact B463611
  · exact B463615
  · exact B463619
  · exact B463623
  · exact B463627
  · exact B463631
  · exact B463635
  · exact B463639
  · exact B463643
  · exact B463647
  · exact B463651
  · exact B463655
  · exact B463659
  · exact B463663
  · exact B463667
  · exact B463671
  · exact B463675
  · exact B463679
  · exact B463683
  · exact B463687
  · exact B463691
  · exact B463695
  · exact B463699
  · exact B463703
  · exact B463707
  · exact B463711
  · exact B463715
  · exact B463719
  · exact B463723
  · exact B463727
  · exact B463731
  · exact B463735
  · exact B463739
  · exact B463743
  · exact B463747
  · exact B463751
  · exact B463755
  · exact B463759
  · exact B463763
  · exact B463767
  · exact B463771
  · exact B463775
  · exact B463779
  · exact B463783

theorem solution (m : ℕ) (hlo : 459783 ≤ m) (hhi : m ≤ 463783) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 114945 ≤ j := by omega
    have hj2 : j ≤ 115945 := by omega
    have hb : Blo 459783 (4 * j + 3) := by
      rcases Nat.lt_or_ge j 115645 with hc0 | hc0
      · exact C0 j (by omega) (by omega)
      exact C1 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
