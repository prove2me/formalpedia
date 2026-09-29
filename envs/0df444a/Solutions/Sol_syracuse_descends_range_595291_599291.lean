-- Prove2me | solution 1 for syracuse_descends_range_595291_599291
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-09T19:04:27.595833+00:00
-- url     : https://prove2.me/submissions/34cd2636-8006-4ab9-b263-0a6b11c99e7a

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


theorem B1343501 : Blo 595291 1343501 := bbase (se 3 (by rfl) ⟨251906, by rfl⟩ : syracuseStep 1343501 = 503813) (by norm_num)
theorem B1507349 : Blo 595291 1507349 := bbase (se 6 (by rfl) ⟨35328, by rfl⟩ : syracuseStep 1507349 = 70657) (by norm_num)
theorem B1146901 : Blo 595291 1146901 := bbase (se 6 (by rfl) ⟨26880, by rfl⟩ : syracuseStep 1146901 = 53761) (by norm_num)
theorem B753725 : Blo 595291 753725 := bbase (se 3 (by rfl) ⟨141323, by rfl⟩ : syracuseStep 753725 = 282647) (by norm_num)
theorem B1343573 : Blo 595291 1343573 := bbase (se 8 (by rfl) ⟨7872, by rfl⟩ : syracuseStep 1343573 = 15745) (by norm_num)
theorem B753781 : Blo 595291 753781 := bbase (se 5 (by rfl) ⟨35333, by rfl⟩ : syracuseStep 753781 = 70667) (by norm_num)
theorem B1343645 : Blo 595291 1343645 := bbase (se 3 (by rfl) ⟨251933, by rfl⟩ : syracuseStep 1343645 = 503867) (by norm_num)
theorem B852133 : Blo 595291 852133 := bbase (se 4 (by rfl) ⟨79887, by rfl⟩ : syracuseStep 852133 = 159775) (by norm_num)
theorem B753877 : Blo 595291 753877 := bbase (se 7 (by rfl) ⟨8834, by rfl⟩ : syracuseStep 753877 = 17669) (by norm_num)
theorem B1343717 : Blo 595291 1343717 := bbase (se 4 (by rfl) ⟨125973, by rfl⟩ : syracuseStep 1343717 = 251947) (by norm_num)
theorem B1310957 : Blo 595291 1310957 := bbase (se 3 (by rfl) ⟨245804, by rfl⟩ : syracuseStep 1310957 = 491609) (by norm_num)
theorem B4522229 : Blo 595291 4522229 := bbase (se 5 (by rfl) ⟨211979, by rfl⟩ : syracuseStep 4522229 = 423959) (by norm_num)
theorem B1343789 : Blo 595291 1343789 := bbase (se 3 (by rfl) ⟨251960, by rfl⟩ : syracuseStep 1343789 = 503921) (by norm_num)
theorem B3014981 : Blo 595291 3014981 := bbase (se 4 (by rfl) ⟨282654, by rfl⟩ : syracuseStep 3014981 = 565309) (by norm_num)
theorem B1507693 : Blo 595291 1507693 := bbase (se 3 (by rfl) ⟨282692, by rfl⟩ : syracuseStep 1507693 = 565385) (by norm_num)
theorem B1343861 : Blo 595291 1343861 := bbase (se 5 (by rfl) ⟨62993, by rfl⟩ : syracuseStep 1343861 = 125987) (by norm_num)
theorem B754049 : Blo 595291 754049 := bbase (se 2 (by rfl) ⟨282768, by rfl⟩ : syracuseStep 754049 = 565537) (by norm_num)
theorem B6816149 : Blo 595291 6816149 := bbase (se 6 (by rfl) ⟨159753, by rfl⟩ : syracuseStep 6816149 = 319507) (by norm_num)
theorem B754105 : Blo 595291 754105 := bbase (se 2 (by rfl) ⟨282789, by rfl⟩ : syracuseStep 754105 = 565579) (by norm_num)
theorem B1343933 : Blo 595291 1343933 := bbase (se 3 (by rfl) ⟨251987, by rfl⟩ : syracuseStep 1343933 = 503975) (by norm_num)
theorem B1507805 : Blo 595291 1507805 := bbase (se 3 (by rfl) ⟨282713, by rfl⟩ : syracuseStep 1507805 = 565427) (by norm_num)
theorem B1344005 : Blo 595291 1344005 := bbase (se 4 (by rfl) ⟨126000, by rfl⟩ : syracuseStep 1344005 = 252001) (by norm_num)
theorem B2425349 : Blo 595291 2425349 := bbase (se 4 (by rfl) ⟨227376, by rfl⟩ : syracuseStep 2425349 = 454753) (by norm_num)
theorem B754201 : Blo 595291 754201 := bbase (se 2 (by rfl) ⟨282825, by rfl⟩ : syracuseStep 754201 = 565651) (by norm_num)
theorem B1344077 : Blo 595291 1344077 := bbase (se 3 (by rfl) ⟨252014, by rfl⟩ : syracuseStep 1344077 = 504029) (by norm_num)
theorem B1278541 : Blo 595291 1278541 := bbase (se 3 (by rfl) ⟨239726, by rfl⟩ : syracuseStep 1278541 = 479453) (by norm_num)
theorem B1147477 : Blo 595291 1147477 := bbase (se 8 (by rfl) ⟨6723, by rfl⟩ : syracuseStep 1147477 = 13447) (by norm_num)
theorem B1344149 : Blo 595291 1344149 := bbase (se 6 (by rfl) ⟨31503, by rfl⟩ : syracuseStep 1344149 = 63007) (by norm_num)
theorem B1507997 : Blo 595291 1507997 := bbase (se 3 (by rfl) ⟨282749, by rfl⟩ : syracuseStep 1507997 = 565499) (by norm_num)
theorem B754373 : Blo 595291 754373 := bbase (se 4 (by rfl) ⟨70722, by rfl⟩ : syracuseStep 754373 = 141445) (by norm_num)
theorem B1278661 : Blo 595291 1278661 := bbase (se 4 (by rfl) ⟨119874, by rfl⟩ : syracuseStep 1278661 = 239749) (by norm_num)
theorem B1344221 : Blo 595291 1344221 := bbase (se 3 (by rfl) ⟨252041, by rfl⟩ : syracuseStep 1344221 = 504083) (by norm_num)
theorem B852725 : Blo 595291 852725 := bbase (se 5 (by rfl) ⟨39971, by rfl⟩ : syracuseStep 852725 = 79943) (by norm_num)
theorem B754429 : Blo 595291 754429 := bbase (se 3 (by rfl) ⟨141455, by rfl⟩ : syracuseStep 754429 = 282911) (by norm_num)
theorem B1344293 : Blo 595291 1344293 := bbase (se 4 (by rfl) ⟨126027, by rfl⟩ : syracuseStep 1344293 = 252055) (by norm_num)
theorem B852805 : Blo 595291 852805 := bbase (se 4 (by rfl) ⟨79950, by rfl⟩ : syracuseStep 852805 = 159901) (by norm_num)
theorem B754525 : Blo 595291 754525 := bbase (se 3 (by rfl) ⟨141473, by rfl⟩ : syracuseStep 754525 = 282947) (by norm_num)
theorem B1344365 : Blo 595291 1344365 := bbase (se 3 (by rfl) ⟨252068, by rfl⟩ : syracuseStep 1344365 = 504137) (by norm_num)
theorem B1344437 : Blo 595291 1344437 := bbase (se 5 (by rfl) ⟨63020, by rfl⟩ : syracuseStep 1344437 = 126041) (by norm_num)
theorem B852925 : Blo 595291 852925 := bbase (se 3 (by rfl) ⟨159923, by rfl⟩ : syracuseStep 852925 = 319847) (by norm_num)
theorem B1278917 : Blo 595291 1278917 := bbase (se 4 (by rfl) ⟨119898, by rfl⟩ : syracuseStep 1278917 = 239797) (by norm_num)
theorem B1508341 : Blo 595291 1508341 := bbase (se 5 (by rfl) ⟨70703, by rfl⟩ : syracuseStep 1508341 = 141407) (by norm_num)
theorem B1344509 : Blo 595291 1344509 := bbase (se 3 (by rfl) ⟨252095, by rfl⟩ : syracuseStep 1344509 = 504191) (by norm_num)
theorem B754697 : Blo 595291 754697 := bbase (se 2 (by rfl) ⟨283011, by rfl⟩ : syracuseStep 754697 = 566023) (by norm_num)
theorem B853021 : Blo 595291 853021 := bbase (se 3 (by rfl) ⟨159941, by rfl⟩ : syracuseStep 853021 = 319883) (by norm_num)
theorem B754753 : Blo 595291 754753 := bbase (se 2 (by rfl) ⟨283032, by rfl⟩ : syracuseStep 754753 = 566065) (by norm_num)
theorem B1344581 : Blo 595291 1344581 := bbase (se 4 (by rfl) ⟨126054, by rfl⟩ : syracuseStep 1344581 = 252109) (by norm_num)
theorem B1508453 : Blo 595291 1508453 := bbase (se 4 (by rfl) ⟨141417, by rfl⟩ : syracuseStep 1508453 = 282835) (by norm_num)
theorem B1344653 : Blo 595291 1344653 := bbase (se 3 (by rfl) ⟨252122, by rfl⟩ : syracuseStep 1344653 = 504245) (by norm_num)
theorem B754849 : Blo 595291 754849 := bbase (se 2 (by rfl) ⟨283068, by rfl⟩ : syracuseStep 754849 = 566137) (by norm_num)
theorem B1344725 : Blo 595291 1344725 := bbase (se 7 (by rfl) ⟨15758, by rfl⟩ : syracuseStep 1344725 = 31517) (by norm_num)
theorem B1344797 : Blo 595291 1344797 := bbase (se 3 (by rfl) ⟨252149, by rfl⟩ : syracuseStep 1344797 = 504299) (by norm_num)
theorem B1508645 : Blo 595291 1508645 := bbase (se 4 (by rfl) ⟨141435, by rfl⟩ : syracuseStep 1508645 = 282871) (by norm_num)
theorem B755021 : Blo 595291 755021 := bbase (se 3 (by rfl) ⟨141566, by rfl⟩ : syracuseStep 755021 = 283133) (by norm_num)
theorem B1344869 : Blo 595291 1344869 := bbase (se 4 (by rfl) ⟨126081, by rfl⟩ : syracuseStep 1344869 = 252163) (by norm_num)
theorem B755077 : Blo 595291 755077 := bbase (se 4 (by rfl) ⟨70788, by rfl⟩ : syracuseStep 755077 = 141577) (by norm_num)
theorem B2262437 : Blo 595291 2262437 := bbase (se 4 (by rfl) ⟨212103, by rfl⟩ : syracuseStep 2262437 = 424207) (by norm_num)
theorem B1344941 : Blo 595291 1344941 := bbase (se 3 (by rfl) ⟨252176, by rfl⟩ : syracuseStep 1344941 = 504353) (by norm_num)
theorem B755173 : Blo 595291 755173 := bbase (se 4 (by rfl) ⟨70797, by rfl⟩ : syracuseStep 755173 = 141595) (by norm_num)
theorem B1934837 : Blo 595291 1934837 := bbase (se 5 (by rfl) ⟨90695, by rfl⟩ : syracuseStep 1934837 = 181391) (by norm_num)
theorem B1345013 : Blo 595291 1345013 := bbase (se 5 (by rfl) ⟨63047, by rfl⟩ : syracuseStep 1345013 = 126095) (by norm_num)
theorem B3409397 : Blo 595291 3409397 := bbase (se 5 (by rfl) ⟨159815, by rfl⟩ : syracuseStep 3409397 = 319631) (by norm_num)
theorem B2557493 : Blo 595291 2557493 := bbase (se 5 (by rfl) ⟨119882, by rfl⟩ : syracuseStep 2557493 = 239765) (by norm_num)
theorem B1345085 : Blo 595291 1345085 := bbase (se 3 (by rfl) ⟨252203, by rfl⟩ : syracuseStep 1345085 = 504407) (by norm_num)
theorem B3016277 : Blo 595291 3016277 := bbase (se 8 (by rfl) ⟨17673, by rfl⟩ : syracuseStep 3016277 = 35347) (by norm_num)
theorem B1508989 : Blo 595291 1508989 := bbase (se 3 (by rfl) ⟨282935, by rfl⟩ : syracuseStep 1508989 = 565871) (by norm_num)
theorem B1345157 : Blo 595291 1345157 := bbase (se 4 (by rfl) ⟨126108, by rfl⟩ : syracuseStep 1345157 = 252217) (by norm_num)
theorem B755345 : Blo 595291 755345 := bbase (se 2 (by rfl) ⟨283254, by rfl⟩ : syracuseStep 755345 = 566509) (by norm_num)
theorem B1312405 : Blo 595291 1312405 := bbase (se 6 (by rfl) ⟨30759, by rfl⟩ : syracuseStep 1312405 = 61519) (by norm_num)
theorem B2262725 : Blo 595291 2262725 := bbase (se 4 (by rfl) ⟨212130, by rfl⟩ : syracuseStep 2262725 = 424261) (by norm_num)
theorem B755401 : Blo 595291 755401 := bbase (se 2 (by rfl) ⟨283275, by rfl⟩ : syracuseStep 755401 = 566551) (by norm_num)
theorem B1345229 : Blo 595291 1345229 := bbase (se 3 (by rfl) ⟨252230, by rfl⟩ : syracuseStep 1345229 = 504461) (by norm_num)
theorem B1509101 : Blo 595291 1509101 := bbase (se 3 (by rfl) ⟨282956, by rfl⟩ : syracuseStep 1509101 = 565913) (by norm_num)
theorem B1345301 : Blo 595291 1345301 := bbase (se 6 (by rfl) ⟨31530, by rfl⟩ : syracuseStep 1345301 = 63061) (by norm_num)
theorem B755497 : Blo 595291 755497 := bbase (se 2 (by rfl) ⟨283311, by rfl⟩ : syracuseStep 755497 = 566623) (by norm_num)
theorem B1279805 : Blo 595291 1279805 := bbase (se 3 (by rfl) ⟨239963, by rfl⟩ : syracuseStep 1279805 = 479927) (by norm_num)
theorem B1345373 : Blo 595291 1345373 := bbase (se 3 (by rfl) ⟨252257, by rfl⟩ : syracuseStep 1345373 = 504515) (by norm_num)
theorem B1345445 : Blo 595291 1345445 := bbase (se 4 (by rfl) ⟨126135, by rfl⟩ : syracuseStep 1345445 = 252271) (by norm_num)
theorem B1509293 : Blo 595291 1509293 := bbase (se 3 (by rfl) ⟨282992, by rfl⟩ : syracuseStep 1509293 = 565985) (by norm_num)
theorem B2754485 : Blo 595291 2754485 := bbase (se 5 (by rfl) ⟨129116, by rfl⟩ : syracuseStep 2754485 = 258233) (by norm_num)
theorem B755669 : Blo 595291 755669 := bbase (se 7 (by rfl) ⟨8855, by rfl⟩ : syracuseStep 755669 = 17711) (by norm_num)
theorem B1345517 : Blo 595291 1345517 := bbase (se 3 (by rfl) ⟨252284, by rfl⟩ : syracuseStep 1345517 = 504569) (by norm_num)
theorem B755725 : Blo 595291 755725 := bbase (se 3 (by rfl) ⟨141698, by rfl⟩ : syracuseStep 755725 = 283397) (by norm_num)
theorem B1345589 : Blo 595291 1345589 := bbase (se 5 (by rfl) ⟨63074, by rfl⟩ : syracuseStep 1345589 = 126149) (by norm_num)
theorem B1935461 : Blo 595291 1935461 := bbase (se 4 (by rfl) ⟨181449, by rfl⟩ : syracuseStep 1935461 = 362899) (by norm_num)
theorem B755821 : Blo 595291 755821 := bbase (se 3 (by rfl) ⟨141716, by rfl⟩ : syracuseStep 755821 = 283433) (by norm_num)
theorem B1345661 : Blo 595291 1345661 := bbase (se 3 (by rfl) ⟨252311, by rfl⟩ : syracuseStep 1345661 = 504623) (by norm_num)
theorem B1345733 : Blo 595291 1345733 := bbase (se 4 (by rfl) ⟨126162, by rfl⟩ : syracuseStep 1345733 = 252325) (by norm_num)
theorem B1509637 : Blo 595291 1509637 := bbase (se 4 (by rfl) ⟨141528, by rfl⟩ : syracuseStep 1509637 = 283057) (by norm_num)
theorem B1345805 : Blo 595291 1345805 := bbase (se 3 (by rfl) ⟨252338, by rfl⟩ : syracuseStep 1345805 = 504677) (by norm_num)
theorem B755993 : Blo 595291 755993 := bbase (se 2 (by rfl) ⟨283497, by rfl⟩ : syracuseStep 755993 = 566995) (by norm_num)
theorem B756049 : Blo 595291 756049 := bbase (se 2 (by rfl) ⟨283518, by rfl⟩ : syracuseStep 756049 = 567037) (by norm_num)
theorem B1345877 : Blo 595291 1345877 := bbase (se 10 (by rfl) ⟨1971, by rfl⟩ : syracuseStep 1345877 = 3943) (by norm_num)
theorem B1509749 : Blo 595291 1509749 := bbase (se 5 (by rfl) ⟨70769, by rfl⟩ : syracuseStep 1509749 = 141539) (by norm_num)
theorem B1345949 : Blo 595291 1345949 := bbase (se 3 (by rfl) ⟨252365, by rfl⟩ : syracuseStep 1345949 = 504731) (by norm_num)
theorem B756145 : Blo 595291 756145 := bbase (se 2 (by rfl) ⟨283554, by rfl⟩ : syracuseStep 756145 = 567109) (by norm_num)
theorem B1018325 : Blo 595291 1018325 := bbase (se 7 (by rfl) ⟨11933, by rfl⟩ : syracuseStep 1018325 = 23867) (by norm_num)
theorem B1706453 : Blo 595291 1706453 := bbase (se 7 (by rfl) ⟨19997, by rfl⟩ : syracuseStep 1706453 = 39995) (by norm_num)
theorem B1346021 : Blo 595291 1346021 := bbase (se 4 (by rfl) ⟨126189, by rfl⟩ : syracuseStep 1346021 = 252379) (by norm_num)
theorem B1346093 : Blo 595291 1346093 := bbase (se 3 (by rfl) ⟨252392, by rfl⟩ : syracuseStep 1346093 = 504785) (by norm_num)
theorem B1509941 : Blo 595291 1509941 := bbase (se 5 (by rfl) ⟨70778, by rfl⟩ : syracuseStep 1509941 = 141557) (by norm_num)
theorem B1149509 : Blo 595291 1149509 := bbase (se 4 (by rfl) ⟨107766, by rfl⟩ : syracuseStep 1149509 = 215533) (by norm_num)
theorem B756317 : Blo 595291 756317 := bbase (se 3 (by rfl) ⟨141809, by rfl⟩ : syracuseStep 756317 = 283619) (by norm_num)
theorem B1346165 : Blo 595291 1346165 := bbase (se 5 (by rfl) ⟨63101, by rfl⟩ : syracuseStep 1346165 = 126203) (by norm_num)
theorem B789113 : Blo 595291 789113 := bbase (se 2 (by rfl) ⟨295917, by rfl⟩ : syracuseStep 789113 = 591835) (by norm_num)
theorem B756373 : Blo 595291 756373 := bbase (se 6 (by rfl) ⟨17727, by rfl⟩ : syracuseStep 756373 = 35455) (by norm_num)
theorem B1346237 : Blo 595291 1346237 := bbase (se 3 (by rfl) ⟨252419, by rfl⟩ : syracuseStep 1346237 = 504839) (by norm_num)
theorem B756469 : Blo 595291 756469 := bbase (se 5 (by rfl) ⟨35459, by rfl⟩ : syracuseStep 756469 = 70919) (by norm_num)
theorem B1346309 : Blo 595291 1346309 := bbase (se 4 (by rfl) ⟨126216, by rfl⟩ : syracuseStep 1346309 = 252433) (by norm_num)
theorem B1346381 : Blo 595291 1346381 := bbase (se 3 (by rfl) ⟨252446, by rfl⟩ : syracuseStep 1346381 = 504893) (by norm_num)
theorem B3017573 : Blo 595291 3017573 := bbase (se 4 (by rfl) ⟨282897, by rfl⟩ : syracuseStep 3017573 = 565795) (by norm_num)
theorem B2263909 : Blo 595291 2263909 := bbase (se 4 (by rfl) ⟨212241, by rfl⟩ : syracuseStep 2263909 = 424483) (by norm_num)
theorem B1510285 : Blo 595291 1510285 := bbase (se 3 (by rfl) ⟨283178, by rfl⟩ : syracuseStep 1510285 = 566357) (by norm_num)
theorem B1346453 : Blo 595291 1346453 := bbase (se 6 (by rfl) ⟨31557, by rfl⟩ : syracuseStep 1346453 = 63115) (by norm_num)
theorem B756641 : Blo 595291 756641 := bbase (se 2 (by rfl) ⟨283740, by rfl⟩ : syracuseStep 756641 = 567481) (by norm_num)
theorem B756697 : Blo 595291 756697 := bbase (se 2 (by rfl) ⟨283761, by rfl⟩ : syracuseStep 756697 = 567523) (by norm_num)
theorem B1346525 : Blo 595291 1346525 := bbase (se 3 (by rfl) ⟨252473, by rfl⟩ : syracuseStep 1346525 = 504947) (by norm_num)
theorem B1510397 : Blo 595291 1510397 := bbase (se 3 (by rfl) ⟨283199, by rfl⟩ : syracuseStep 1510397 = 566399) (by norm_num)
theorem B1346597 : Blo 595291 1346597 := bbase (se 4 (by rfl) ⟨126243, by rfl⟩ : syracuseStep 1346597 = 252487) (by norm_num)
theorem B756793 : Blo 595291 756793 := bbase (se 2 (by rfl) ⟨283797, by rfl⟩ : syracuseStep 756793 = 567595) (by norm_num)
theorem B1346669 : Blo 595291 1346669 := bbase (se 3 (by rfl) ⟨252500, by rfl⟩ : syracuseStep 1346669 = 505001) (by norm_num)
theorem B2264213 : Blo 595291 2264213 := bbase (se 6 (by rfl) ⟨53067, by rfl⟩ : syracuseStep 2264213 = 106135) (by norm_num)
theorem B1346741 : Blo 595291 1346741 := bbase (se 5 (by rfl) ⟨63128, by rfl⟩ : syracuseStep 1346741 = 126257) (by norm_num)
theorem B1510589 : Blo 595291 1510589 := bbase (se 3 (by rfl) ⟨283235, by rfl⟩ : syracuseStep 1510589 = 566471) (by norm_num)
theorem B756965 : Blo 595291 756965 := bbase (se 4 (by rfl) ⟨70965, by rfl⟩ : syracuseStep 756965 = 141931) (by norm_num)
theorem B1346813 : Blo 595291 1346813 := bbase (se 3 (by rfl) ⟨252527, by rfl⟩ : syracuseStep 1346813 = 505055) (by norm_num)
theorem B757021 : Blo 595291 757021 := bbase (se 3 (by rfl) ⟨141941, by rfl⟩ : syracuseStep 757021 = 283883) (by norm_num)
theorem B2559269 : Blo 595291 2559269 := bbase (se 4 (by rfl) ⟨239931, by rfl⟩ : syracuseStep 2559269 = 479863) (by norm_num)
theorem B1346885 : Blo 595291 1346885 := bbase (se 4 (by rfl) ⟨126270, by rfl⟩ : syracuseStep 1346885 = 252541) (by norm_num)
theorem B757117 : Blo 595291 757117 := bbase (se 3 (by rfl) ⟨141959, by rfl⟩ : syracuseStep 757117 = 283919) (by norm_num)
theorem B1346957 : Blo 595291 1346957 := bbase (se 3 (by rfl) ⟨252554, by rfl⟩ : syracuseStep 1346957 = 505109) (by norm_num)
theorem B1019309 : Blo 595291 1019309 := bbase (se 3 (by rfl) ⟨191120, by rfl⟩ : syracuseStep 1019309 = 382241) (by norm_num)
theorem B3837365 : Blo 595291 3837365 := bbase (se 5 (by rfl) ⟨179876, by rfl⟩ : syracuseStep 3837365 = 359753) (by norm_num)
theorem B1347029 : Blo 595291 1347029 := bbase (se 7 (by rfl) ⟨15785, by rfl⟩ : syracuseStep 1347029 = 31571) (by norm_num)
theorem B1019413 : Blo 595291 1019413 := bbase (se 6 (by rfl) ⟨23892, by rfl⟩ : syracuseStep 1019413 = 47785) (by norm_num)
theorem B1510933 : Blo 595291 1510933 := bbase (se 6 (by rfl) ⟨35412, by rfl⟩ : syracuseStep 1510933 = 70825) (by norm_num)
theorem B2559509 : Blo 595291 2559509 := bbase (se 6 (by rfl) ⟨59988, by rfl⟩ : syracuseStep 2559509 = 119977) (by norm_num)
theorem B1347101 : Blo 595291 1347101 := bbase (se 3 (by rfl) ⟨252581, by rfl⟩ : syracuseStep 1347101 = 505163) (by norm_num)
theorem B757289 : Blo 595291 757289 := bbase (se 2 (by rfl) ⟨283983, by rfl⟩ : syracuseStep 757289 = 567967) (by norm_num)
theorem B757345 : Blo 595291 757345 := bbase (se 2 (by rfl) ⟨284004, by rfl⟩ : syracuseStep 757345 = 568009) (by norm_num)
theorem B1347173 : Blo 595291 1347173 := bbase (se 4 (by rfl) ⟨126297, by rfl⟩ : syracuseStep 1347173 = 252595) (by norm_num)
theorem B1511045 : Blo 595291 1511045 := bbase (se 4 (by rfl) ⟨141660, by rfl⟩ : syracuseStep 1511045 = 283321) (by norm_num)
theorem B1347245 : Blo 595291 1347245 := bbase (se 3 (by rfl) ⟨252608, by rfl⟩ : syracuseStep 1347245 = 505217) (by norm_num)
theorem B757441 : Blo 595291 757441 := bbase (se 2 (by rfl) ⟨284040, by rfl⟩ : syracuseStep 757441 = 568081) (by norm_num)
theorem B1347317 : Blo 595291 1347317 := bbase (se 5 (by rfl) ⟨63155, by rfl⟩ : syracuseStep 1347317 = 126311) (by norm_num)
theorem B1347389 : Blo 595291 1347389 := bbase (se 3 (by rfl) ⟨252635, by rfl⟩ : syracuseStep 1347389 = 505271) (by norm_num)
theorem B1511237 : Blo 595291 1511237 := bbase (se 4 (by rfl) ⟨141678, by rfl⟩ : syracuseStep 1511237 = 283357) (by norm_num)
theorem B757613 : Blo 595291 757613 := bbase (se 3 (by rfl) ⟨142052, by rfl⟩ : syracuseStep 757613 = 284105) (by norm_num)
theorem B2723701 : Blo 595291 2723701 := bbase (se 5 (by rfl) ⟨127673, by rfl⟩ : syracuseStep 2723701 = 255347) (by norm_num)
theorem B1347461 : Blo 595291 1347461 := bbase (se 4 (by rfl) ⟨126324, by rfl⟩ : syracuseStep 1347461 = 252649) (by norm_num)
theorem B757669 : Blo 595291 757669 := bbase (se 4 (by rfl) ⟨71031, by rfl⟩ : syracuseStep 757669 = 142063) (by norm_num)
theorem B692173 : Blo 595291 692173 := bbase (se 3 (by rfl) ⟨129782, by rfl⟩ : syracuseStep 692173 = 259565) (by norm_num)
theorem B1347533 : Blo 595291 1347533 := bbase (se 3 (by rfl) ⟨252662, by rfl⟩ : syracuseStep 1347533 = 505325) (by norm_num)
theorem B11636693 : Blo 595291 11636693 := bbase (se 7 (by rfl) ⟨136367, by rfl⟩ : syracuseStep 11636693 = 272735) (by norm_num)
theorem B757765 : Blo 595291 757765 := bbase (se 4 (by rfl) ⟨71040, by rfl⟩ : syracuseStep 757765 = 142081) (by norm_num)
theorem B1347605 : Blo 595291 1347605 := bbase (se 6 (by rfl) ⟨31584, by rfl⟩ : syracuseStep 1347605 = 63169) (by norm_num)
theorem B1347677 : Blo 595291 1347677 := bbase (se 3 (by rfl) ⟨252689, by rfl⟩ : syracuseStep 1347677 = 505379) (by norm_num)
theorem B3018869 : Blo 595291 3018869 := bbase (se 5 (by rfl) ⟨141509, by rfl⟩ : syracuseStep 3018869 = 283019) (by norm_num)
theorem B1511581 : Blo 595291 1511581 := bbase (se 3 (by rfl) ⟨283421, by rfl⟩ : syracuseStep 1511581 = 566843) (by norm_num)
theorem B1347749 : Blo 595291 1347749 := bbase (se 4 (by rfl) ⟨126351, by rfl⟩ : syracuseStep 1347749 = 252703) (by norm_num)
theorem B757937 : Blo 595291 757937 := bbase (se 2 (by rfl) ⟨284226, by rfl⟩ : syracuseStep 757937 = 568453) (by norm_num)
theorem B757993 : Blo 595291 757993 := bbase (se 2 (by rfl) ⟨284247, by rfl⟩ : syracuseStep 757993 = 568495) (by norm_num)
theorem B1347821 : Blo 595291 1347821 := bbase (se 3 (by rfl) ⟨252716, by rfl⟩ : syracuseStep 1347821 = 505433) (by norm_num)
theorem B1511693 : Blo 595291 1511693 := bbase (se 3 (by rfl) ⟨283442, by rfl⟩ : syracuseStep 1511693 = 566885) (by norm_num)
theorem B954677 : Blo 595291 954677 := bbase (se 5 (by rfl) ⟨44750, by rfl⟩ : syracuseStep 954677 = 89501) (by norm_num)
theorem B1347893 : Blo 595291 1347893 := bbase (se 5 (by rfl) ⟨63182, by rfl⟩ : syracuseStep 1347893 = 126365) (by norm_num)
theorem B758089 : Blo 595291 758089 := bbase (se 2 (by rfl) ⟨284283, by rfl⟩ : syracuseStep 758089 = 568567) (by norm_num)
theorem B1347965 : Blo 595291 1347965 := bbase (se 3 (by rfl) ⟨252743, by rfl⟩ : syracuseStep 1347965 = 505487) (by norm_num)
theorem B1348037 : Blo 595291 1348037 := bbase (se 4 (by rfl) ⟨126378, by rfl⟩ : syracuseStep 1348037 = 252757) (by norm_num)
theorem B1511885 : Blo 595291 1511885 := bbase (se 3 (by rfl) ⟨283478, by rfl⟩ : syracuseStep 1511885 = 566957) (by norm_num)
theorem B758261 : Blo 595291 758261 := bbase (se 5 (by rfl) ⟨35543, by rfl⟩ : syracuseStep 758261 = 71087) (by norm_num)
theorem B1348109 : Blo 595291 1348109 := bbase (se 3 (by rfl) ⟨252770, by rfl⟩ : syracuseStep 1348109 = 505541) (by norm_num)
theorem B758317 : Blo 595291 758317 := bbase (se 3 (by rfl) ⟨142184, by rfl⟩ : syracuseStep 758317 = 284369) (by norm_num)
theorem B1348181 : Blo 595291 1348181 := bbase (se 8 (by rfl) ⟨7899, by rfl⟩ : syracuseStep 1348181 = 15799) (by norm_num)
theorem B1151581 : Blo 595291 1151581 := bbase (se 3 (by rfl) ⟨215921, by rfl⟩ : syracuseStep 1151581 = 431843) (by norm_num)
theorem B758413 : Blo 595291 758413 := bbase (se 3 (by rfl) ⟨142202, by rfl⟩ : syracuseStep 758413 = 284405) (by norm_num)
theorem B1348253 : Blo 595291 1348253 := bbase (se 3 (by rfl) ⟨252797, by rfl⟩ : syracuseStep 1348253 = 505595) (by norm_num)
theorem B725701 : Blo 595291 725701 := bbase (se 4 (by rfl) ⟨68034, by rfl⟩ : syracuseStep 725701 = 136069) (by norm_num)
theorem B1348325 : Blo 595291 1348325 := bbase (se 4 (by rfl) ⟨126405, by rfl⟩ : syracuseStep 1348325 = 252811) (by norm_num)
theorem B1512229 : Blo 595291 1512229 := bbase (se 4 (by rfl) ⟨141771, by rfl⟩ : syracuseStep 1512229 = 283543) (by norm_num)
theorem B1348397 : Blo 595291 1348397 := bbase (se 3 (by rfl) ⟨252824, by rfl⟩ : syracuseStep 1348397 = 505649) (by norm_num)
theorem B1512341 : Blo 595291 1512341 := bbase (se 6 (by rfl) ⟨35445, by rfl⟩ : syracuseStep 1512341 = 70891) (by norm_num)
theorem B2331605 : Blo 595291 2331605 := bbase (se 7 (by rfl) ⟨27323, by rfl⟩ : syracuseStep 2331605 = 54647) (by norm_num)
theorem B726013 : Blo 595291 726013 := bbase (se 3 (by rfl) ⟨136127, by rfl⟩ : syracuseStep 726013 = 272255) (by norm_num)
theorem B1512533 : Blo 595291 1512533 := bbase (se 8 (by rfl) ⟨8862, by rfl⟩ : syracuseStep 1512533 = 17725) (by norm_num)
theorem B2266325 : Blo 595291 2266325 := bbase (se 7 (by rfl) ⟨26558, by rfl⟩ : syracuseStep 2266325 = 53117) (by norm_num)
theorem B2495701 : Blo 595291 2495701 := bbase (se 7 (by rfl) ⟨29246, by rfl⟩ : syracuseStep 2495701 = 58493) (by norm_num)
theorem B955613 : Blo 595291 955613 := bbase (se 3 (by rfl) ⟨179177, by rfl⟩ : syracuseStep 955613 = 358355) (by norm_num)
theorem B3020165 : Blo 595291 3020165 := bbase (se 4 (by rfl) ⟨283140, by rfl⟩ : syracuseStep 3020165 = 566281) (by norm_num)
theorem B1021349 : Blo 595291 1021349 := bbase (se 4 (by rfl) ⟨95751, by rfl⟩ : syracuseStep 1021349 = 191503) (by norm_num)
theorem B1512877 : Blo 595291 1512877 := bbase (se 3 (by rfl) ⟨283664, by rfl⟩ : syracuseStep 1512877 = 567329) (by norm_num)
theorem B2594261 : Blo 595291 2594261 := bbase (se 7 (by rfl) ⟨30401, by rfl⟩ : syracuseStep 2594261 = 60803) (by norm_num)
theorem B2266613 : Blo 595291 2266613 := bbase (se 5 (by rfl) ⟨106247, by rfl⟩ : syracuseStep 2266613 = 212495) (by norm_num)
theorem B1512989 : Blo 595291 1512989 := bbase (se 3 (by rfl) ⟨283685, by rfl⟩ : syracuseStep 1512989 = 567371) (by norm_num)
theorem B1513181 : Blo 595291 1513181 := bbase (se 3 (by rfl) ⟨283721, by rfl⟩ : syracuseStep 1513181 = 567443) (by norm_num)
theorem B956261 : Blo 595291 956261 := bbase (se 4 (by rfl) ⟨89649, by rfl⟩ : syracuseStep 956261 = 179299) (by norm_num)
theorem B1611701 : Blo 595291 1611701 := bbase (se 5 (by rfl) ⟨75548, by rfl⟩ : syracuseStep 1611701 = 151097) (by norm_num)
theorem B1513525 : Blo 595291 1513525 := bbase (se 5 (by rfl) ⟨70946, by rfl⟩ : syracuseStep 1513525 = 141893) (by norm_num)
theorem B1513637 : Blo 595291 1513637 := bbase (se 4 (by rfl) ⟨141903, by rfl⟩ : syracuseStep 1513637 = 283807) (by norm_num)
theorem B9214165 : Blo 595291 9214165 := bbase (se 7 (by rfl) ⟨107978, by rfl⟩ : syracuseStep 9214165 = 215957) (by norm_num)
theorem B727277 : Blo 595291 727277 := bbase (se 3 (by rfl) ⟨136364, by rfl⟩ : syracuseStep 727277 = 272729) (by norm_num)
theorem B4921685 : Blo 595291 4921685 := bbase (se 10 (by rfl) ⟨7209, by rfl⟩ : syracuseStep 4921685 = 14419) (by norm_num)
theorem B1513829 : Blo 595291 1513829 := bbase (se 4 (by rfl) ⟨141921, by rfl⟩ : syracuseStep 1513829 = 283843) (by norm_num)
theorem B1612229 : Blo 595291 1612229 := bbase (se 4 (by rfl) ⟨151146, by rfl⟩ : syracuseStep 1612229 = 302293) (by norm_num)
theorem B3021461 : Blo 595291 3021461 := bbase (se 6 (by rfl) ⟨70815, by rfl⟩ : syracuseStep 3021461 = 141631) (by norm_num)
theorem B2267797 : Blo 595291 2267797 := bbase (se 6 (by rfl) ⟨53151, by rfl⟩ : syracuseStep 2267797 = 106303) (by norm_num)
theorem B1514173 : Blo 595291 1514173 := bbase (se 3 (by rfl) ⟨283907, by rfl⟩ : syracuseStep 1514173 = 567815) (by norm_num)
theorem B1514285 : Blo 595291 1514285 := bbase (se 3 (by rfl) ⟨283928, by rfl⟩ : syracuseStep 1514285 = 567857) (by norm_num)
theorem B1907509 : Blo 595291 1907509 := bbase (se 5 (by rfl) ⟨89414, by rfl⟩ : syracuseStep 1907509 = 178829) (by norm_num)
theorem B957253 : Blo 595291 957253 := bbase (se 4 (by rfl) ⟨89742, by rfl⟩ : syracuseStep 957253 = 179485) (by norm_num)
theorem B2268101 : Blo 595291 2268101 := bbase (se 4 (by rfl) ⟨212634, by rfl⟩ : syracuseStep 2268101 = 425269) (by norm_num)
theorem B1514477 : Blo 595291 1514477 := bbase (se 3 (by rfl) ⟨283964, by rfl⟩ : syracuseStep 1514477 = 567929) (by norm_num)
theorem B1023101 : Blo 595291 1023101 := bbase (se 3 (by rfl) ⟨191831, by rfl⟩ : syracuseStep 1023101 = 383663) (by norm_num)
theorem B957701 : Blo 595291 957701 := bbase (se 4 (by rfl) ⟨89784, by rfl⟩ : syracuseStep 957701 = 179569) (by norm_num)
theorem B1514821 : Blo 595291 1514821 := bbase (se 4 (by rfl) ⟨142014, by rfl⟩ : syracuseStep 1514821 = 284029) (by norm_num)
theorem B1514933 : Blo 595291 1514933 := bbase (se 5 (by rfl) ⟨71012, by rfl⟩ : syracuseStep 1514933 = 142025) (by norm_num)
theorem B957901 : Blo 595291 957901 := bbase (se 3 (by rfl) ⟨179606, by rfl⟩ : syracuseStep 957901 = 359213) (by norm_num)
theorem B1515125 : Blo 595291 1515125 := bbase (se 5 (by rfl) ⟨71021, by rfl⟩ : syracuseStep 1515125 = 142043) (by norm_num)
theorem B958157 : Blo 595291 958157 := bbase (se 3 (by rfl) ⟨179654, by rfl⟩ : syracuseStep 958157 = 359309) (by norm_num)
theorem B4530005 : Blo 595291 4530005 := bbase (se 9 (by rfl) ⟨13271, by rfl⟩ : syracuseStep 4530005 = 26543) (by norm_num)
theorem B2039701 : Blo 595291 2039701 := bbase (se 6 (by rfl) ⟨47805, by rfl⟩ : syracuseStep 2039701 = 95611) (by norm_num)
theorem B3022757 : Blo 595291 3022757 := bbase (se 4 (by rfl) ⟨283383, by rfl⟩ : syracuseStep 3022757 = 566767) (by norm_num)
theorem B1515469 : Blo 595291 1515469 := bbase (se 3 (by rfl) ⟨284150, by rfl⟩ : syracuseStep 1515469 = 568301) (by norm_num)
theorem B892949 : Blo 595291 892949 := bbase (se 6 (by rfl) ⟨20928, by rfl⟩ : syracuseStep 892949 = 41857) (by norm_num)
theorem B892973 : Blo 595291 892973 := bbase (se 3 (by rfl) ⟨167432, by rfl⟩ : syracuseStep 892973 = 334865) (by norm_num)
theorem B1515581 : Blo 595291 1515581 := bbase (se 3 (by rfl) ⟨284171, by rfl⟩ : syracuseStep 1515581 = 568343) (by norm_num)
theorem B892997 : Blo 595291 892997 := bbase (se 4 (by rfl) ⟨83718, by rfl⟩ : syracuseStep 892997 = 167437) (by norm_num)
theorem B893021 : Blo 595291 893021 := bbase (se 3 (by rfl) ⟨167441, by rfl⟩ : syracuseStep 893021 = 334883) (by norm_num)
theorem B893045 : Blo 595291 893045 := bbase (se 5 (by rfl) ⟨41861, by rfl⟩ : syracuseStep 893045 = 83723) (by norm_num)
theorem B893069 : Blo 595291 893069 := bbase (se 3 (by rfl) ⟨167450, by rfl⟩ : syracuseStep 893069 = 334901) (by norm_num)
theorem B893093 : Blo 595291 893093 := bbase (se 4 (by rfl) ⟨83727, by rfl⟩ : syracuseStep 893093 = 167455) (by norm_num)
theorem B893117 : Blo 595291 893117 := bbase (se 3 (by rfl) ⟨167459, by rfl⟩ : syracuseStep 893117 = 334919) (by norm_num)
theorem B893141 : Blo 595291 893141 := bbase (se 7 (by rfl) ⟨10466, by rfl⟩ : syracuseStep 893141 = 20933) (by norm_num)
theorem B893165 : Blo 595291 893165 := bbase (se 3 (by rfl) ⟨167468, by rfl⟩ : syracuseStep 893165 = 334937) (by norm_num)
theorem B1515773 : Blo 595291 1515773 := bbase (se 3 (by rfl) ⟨284207, by rfl⟩ : syracuseStep 1515773 = 568415) (by norm_num)
theorem B893189 : Blo 595291 893189 := bbase (se 4 (by rfl) ⟨83736, by rfl⟩ : syracuseStep 893189 = 167473) (by norm_num)
theorem B893213 : Blo 595291 893213 := bbase (se 3 (by rfl) ⟨167477, by rfl⟩ : syracuseStep 893213 = 334955) (by norm_num)
theorem B893237 : Blo 595291 893237 := bbase (se 5 (by rfl) ⟨41870, by rfl⟩ : syracuseStep 893237 = 83741) (by norm_num)
theorem B893261 : Blo 595291 893261 := bbase (se 3 (by rfl) ⟨167486, by rfl⟩ : syracuseStep 893261 = 334973) (by norm_num)
theorem B893285 : Blo 595291 893285 := bbase (se 4 (by rfl) ⟨83745, by rfl⟩ : syracuseStep 893285 = 167491) (by norm_num)
theorem B893309 : Blo 595291 893309 := bbase (se 3 (by rfl) ⟨167495, by rfl⟩ : syracuseStep 893309 = 334991) (by norm_num)
theorem B893333 : Blo 595291 893333 := bbase (se 6 (by rfl) ⟨20937, by rfl⟩ : syracuseStep 893333 = 41875) (by norm_num)
theorem B893357 : Blo 595291 893357 := bbase (se 3 (by rfl) ⟨167504, by rfl⟩ : syracuseStep 893357 = 335009) (by norm_num)
theorem B4301237 : Blo 595291 4301237 := bbase (se 5 (by rfl) ⟨201620, by rfl⟩ : syracuseStep 4301237 = 403241) (by norm_num)
theorem B893381 : Blo 595291 893381 := bbase (se 4 (by rfl) ⟨83754, by rfl⟩ : syracuseStep 893381 = 167509) (by norm_num)
theorem B893405 : Blo 595291 893405 := bbase (se 3 (by rfl) ⟨167513, by rfl⟩ : syracuseStep 893405 = 335027) (by norm_num)
theorem B893429 : Blo 595291 893429 := bbase (se 5 (by rfl) ⟨41879, by rfl⟩ : syracuseStep 893429 = 83759) (by norm_num)
theorem B893453 : Blo 595291 893453 := bbase (se 3 (by rfl) ⟨167522, by rfl⟩ : syracuseStep 893453 = 335045) (by norm_num)
theorem B1090061 : Blo 595291 1090061 := bbase (se 3 (by rfl) ⟨204386, by rfl⟩ : syracuseStep 1090061 = 408773) (by norm_num)
theorem B893477 : Blo 595291 893477 := bbase (se 4 (by rfl) ⟨83763, by rfl⟩ : syracuseStep 893477 = 167527) (by norm_num)
theorem B893501 : Blo 595291 893501 := bbase (se 3 (by rfl) ⟨167531, by rfl⟩ : syracuseStep 893501 = 335063) (by norm_num)
theorem B893525 : Blo 595291 893525 := bbase (se 8 (by rfl) ⟨5235, by rfl⟩ : syracuseStep 893525 = 10471) (by norm_num)
theorem B1516117 : Blo 595291 1516117 := bbase (se 8 (by rfl) ⟨8883, by rfl⟩ : syracuseStep 1516117 = 17767) (by norm_num)
theorem B893549 : Blo 595291 893549 := bbase (se 3 (by rfl) ⟨167540, by rfl⟩ : syracuseStep 893549 = 335081) (by norm_num)
theorem B893573 : Blo 595291 893573 := bbase (se 4 (by rfl) ⟨83772, by rfl⟩ : syracuseStep 893573 = 167545) (by norm_num)
theorem B893597 : Blo 595291 893597 := bbase (se 3 (by rfl) ⟨167549, by rfl⟩ : syracuseStep 893597 = 335099) (by norm_num)
theorem B893621 : Blo 595291 893621 := bbase (se 5 (by rfl) ⟨41888, by rfl⟩ : syracuseStep 893621 = 83777) (by norm_num)
theorem B1516229 : Blo 595291 1516229 := bbase (se 4 (by rfl) ⟨142146, by rfl⟩ : syracuseStep 1516229 = 284293) (by norm_num)
theorem B893645 : Blo 595291 893645 := bbase (se 3 (by rfl) ⟨167558, by rfl⟩ : syracuseStep 893645 = 335117) (by norm_num)
theorem B893669 : Blo 595291 893669 := bbase (se 4 (by rfl) ⟨83781, by rfl⟩ : syracuseStep 893669 = 167563) (by norm_num)
theorem B893693 : Blo 595291 893693 := bbase (se 3 (by rfl) ⟨167567, by rfl⟩ : syracuseStep 893693 = 335135) (by norm_num)
theorem B893717 : Blo 595291 893717 := bbase (se 6 (by rfl) ⟨20946, by rfl⟩ : syracuseStep 893717 = 41893) (by norm_num)
theorem B893741 : Blo 595291 893741 := bbase (se 3 (by rfl) ⟨167576, by rfl⟩ : syracuseStep 893741 = 335153) (by norm_num)
theorem B959285 : Blo 595291 959285 := bbase (se 5 (by rfl) ⟨44966, by rfl⟩ : syracuseStep 959285 = 89933) (by norm_num)
theorem B893765 : Blo 595291 893765 := bbase (se 4 (by rfl) ⟨83790, by rfl⟩ : syracuseStep 893765 = 167581) (by norm_num)
theorem B893789 : Blo 595291 893789 := bbase (se 3 (by rfl) ⟨167585, by rfl⟩ : syracuseStep 893789 = 335171) (by norm_num)
theorem B1450853 : Blo 595291 1450853 := bbase (se 4 (by rfl) ⟨136017, by rfl⟩ : syracuseStep 1450853 = 272035) (by norm_num)
theorem B893813 : Blo 595291 893813 := bbase (se 5 (by rfl) ⟨41897, by rfl⟩ : syracuseStep 893813 = 83795) (by norm_num)
theorem B1516421 : Blo 595291 1516421 := bbase (se 4 (by rfl) ⟨142164, by rfl⟩ : syracuseStep 1516421 = 284329) (by norm_num)
theorem B893837 : Blo 595291 893837 := bbase (se 3 (by rfl) ⟨167594, by rfl⟩ : syracuseStep 893837 = 335189) (by norm_num)
theorem B893861 : Blo 595291 893861 := bbase (se 4 (by rfl) ⟨83799, by rfl⟩ : syracuseStep 893861 = 167599) (by norm_num)
theorem B893885 : Blo 595291 893885 := bbase (se 3 (by rfl) ⟨167603, by rfl⟩ : syracuseStep 893885 = 335207) (by norm_num)
theorem B893909 : Blo 595291 893909 := bbase (se 7 (by rfl) ⟨10475, by rfl⟩ : syracuseStep 893909 = 20951) (by norm_num)
theorem B893933 : Blo 595291 893933 := bbase (se 3 (by rfl) ⟨167612, by rfl⟩ : syracuseStep 893933 = 335225) (by norm_num)
theorem B893957 : Blo 595291 893957 := bbase (se 4 (by rfl) ⟨83808, by rfl⟩ : syracuseStep 893957 = 167617) (by norm_num)
theorem B2270213 : Blo 595291 2270213 := bbase (se 4 (by rfl) ⟨212832, by rfl⟩ : syracuseStep 2270213 = 425665) (by norm_num)
theorem B893981 : Blo 595291 893981 := bbase (se 3 (by rfl) ⟨167621, by rfl⟩ : syracuseStep 893981 = 335243) (by norm_num)
theorem B894005 : Blo 595291 894005 := bbase (se 5 (by rfl) ⟨41906, by rfl⟩ : syracuseStep 894005 = 83813) (by norm_num)
theorem B894029 : Blo 595291 894029 := bbase (se 3 (by rfl) ⟨167630, by rfl⟩ : syracuseStep 894029 = 335261) (by norm_num)
theorem B894053 : Blo 595291 894053 := bbase (se 4 (by rfl) ⟨83817, by rfl⟩ : syracuseStep 894053 = 167635) (by norm_num)
theorem B894077 : Blo 595291 894077 := bbase (se 3 (by rfl) ⟨167639, by rfl⟩ : syracuseStep 894077 = 335279) (by norm_num)
theorem B894101 : Blo 595291 894101 := bbase (se 6 (by rfl) ⟨20955, by rfl⟩ : syracuseStep 894101 = 41911) (by norm_num)
theorem B894125 : Blo 595291 894125 := bbase (se 3 (by rfl) ⟨167648, by rfl⟩ : syracuseStep 894125 = 335297) (by norm_num)
theorem B3024053 : Blo 595291 3024053 := bbase (se 5 (by rfl) ⟨141752, by rfl⟩ : syracuseStep 3024053 = 283505) (by norm_num)
theorem B894149 : Blo 595291 894149 := bbase (se 4 (by rfl) ⟨83826, by rfl⟩ : syracuseStep 894149 = 167653) (by norm_num)
theorem B894173 : Blo 595291 894173 := bbase (se 3 (by rfl) ⟨167657, by rfl⟩ : syracuseStep 894173 = 335315) (by norm_num)
theorem B1516765 : Blo 595291 1516765 := bbase (se 3 (by rfl) ⟨284393, by rfl⟩ : syracuseStep 1516765 = 568787) (by norm_num)
theorem B894197 : Blo 595291 894197 := bbase (se 5 (by rfl) ⟨41915, by rfl⟩ : syracuseStep 894197 = 83831) (by norm_num)
theorem B894221 : Blo 595291 894221 := bbase (se 3 (by rfl) ⟨167666, by rfl⟩ : syracuseStep 894221 = 335333) (by norm_num)
theorem B894245 : Blo 595291 894245 := bbase (se 4 (by rfl) ⟨83835, by rfl⟩ : syracuseStep 894245 = 167671) (by norm_num)
theorem B2270501 : Blo 595291 2270501 := bbase (se 4 (by rfl) ⟨212859, by rfl⟩ : syracuseStep 2270501 = 425719) (by norm_num)
theorem B959797 : Blo 595291 959797 := bbase (se 5 (by rfl) ⟨44990, by rfl⟩ : syracuseStep 959797 = 89981) (by norm_num)
theorem B894269 : Blo 595291 894269 := bbase (se 3 (by rfl) ⟨167675, by rfl⟩ : syracuseStep 894269 = 335351) (by norm_num)
theorem B1516877 : Blo 595291 1516877 := bbase (se 3 (by rfl) ⟨284414, by rfl⟩ : syracuseStep 1516877 = 568829) (by norm_num)
theorem B894293 : Blo 595291 894293 := bbase (se 12 (by rfl) ⟨327, by rfl⟩ : syracuseStep 894293 = 655) (by norm_num)
theorem B894317 : Blo 595291 894317 := bbase (se 3 (by rfl) ⟨167684, by rfl⟩ : syracuseStep 894317 = 335369) (by norm_num)
theorem B894341 : Blo 595291 894341 := bbase (se 4 (by rfl) ⟨83844, by rfl⟩ : syracuseStep 894341 = 167689) (by norm_num)
theorem B894365 : Blo 595291 894365 := bbase (se 3 (by rfl) ⟨167693, by rfl⟩ : syracuseStep 894365 = 335387) (by norm_num)
theorem B894389 : Blo 595291 894389 := bbase (se 5 (by rfl) ⟨41924, by rfl⟩ : syracuseStep 894389 = 83849) (by norm_num)
theorem B1811909 : Blo 595291 1811909 := bbase (se 4 (by rfl) ⟨169866, by rfl⟩ : syracuseStep 1811909 = 339733) (by norm_num)
theorem B894413 : Blo 595291 894413 := bbase (se 3 (by rfl) ⟨167702, by rfl⟩ : syracuseStep 894413 = 335405) (by norm_num)
theorem B2041301 : Blo 595291 2041301 := bbase (se 7 (by rfl) ⟨23921, by rfl⟩ : syracuseStep 2041301 = 47843) (by norm_num)
theorem B894437 : Blo 595291 894437 := bbase (se 4 (by rfl) ⟨83853, by rfl⟩ : syracuseStep 894437 = 167707) (by norm_num)
theorem B894461 : Blo 595291 894461 := bbase (se 3 (by rfl) ⟨167711, by rfl⟩ : syracuseStep 894461 = 335423) (by norm_num)
theorem B894485 : Blo 595291 894485 := bbase (se 6 (by rfl) ⟨20964, by rfl⟩ : syracuseStep 894485 = 41929) (by norm_num)
theorem B2041381 : Blo 595291 2041381 := bbase (se 4 (by rfl) ⟨191379, by rfl⟩ : syracuseStep 2041381 = 382759) (by norm_num)
theorem B894509 : Blo 595291 894509 := bbase (se 3 (by rfl) ⟨167720, by rfl⟩ : syracuseStep 894509 = 335441) (by norm_num)
theorem B894533 : Blo 595291 894533 := bbase (se 4 (by rfl) ⟨83862, by rfl⟩ : syracuseStep 894533 = 167725) (by norm_num)
theorem B894557 : Blo 595291 894557 := bbase (se 3 (by rfl) ⟨167729, by rfl⟩ : syracuseStep 894557 = 335459) (by norm_num)
theorem B894581 : Blo 595291 894581 := bbase (se 5 (by rfl) ⟨41933, by rfl⟩ : syracuseStep 894581 = 83867) (by norm_num)
theorem B1910405 : Blo 595291 1910405 := bbase (se 4 (by rfl) ⟨179100, by rfl⟩ : syracuseStep 1910405 = 358201) (by norm_num)
theorem B894605 : Blo 595291 894605 := bbase (se 3 (by rfl) ⟨167738, by rfl⟩ : syracuseStep 894605 = 335477) (by norm_num)
theorem B894629 : Blo 595291 894629 := bbase (se 4 (by rfl) ⟨83871, by rfl⟩ : syracuseStep 894629 = 167743) (by norm_num)
theorem B894653 : Blo 595291 894653 := bbase (se 3 (by rfl) ⟨167747, by rfl⟩ : syracuseStep 894653 = 335495) (by norm_num)
theorem B894677 : Blo 595291 894677 := bbase (se 7 (by rfl) ⟨10484, by rfl⟩ : syracuseStep 894677 = 20969) (by norm_num)
theorem B894701 : Blo 595291 894701 := bbase (se 3 (by rfl) ⟨167756, by rfl⟩ : syracuseStep 894701 = 335513) (by norm_num)
theorem B5089013 : Blo 595291 5089013 := bbase (se 5 (by rfl) ⟨238547, by rfl⟩ : syracuseStep 5089013 = 477095) (by norm_num)
theorem B894725 : Blo 595291 894725 := bbase (se 4 (by rfl) ⟨83880, by rfl⟩ : syracuseStep 894725 = 167761) (by norm_num)
theorem B894749 : Blo 595291 894749 := bbase (se 3 (by rfl) ⟨167765, by rfl⟩ : syracuseStep 894749 = 335531) (by norm_num)
theorem B894773 : Blo 595291 894773 := bbase (se 5 (by rfl) ⟨41942, by rfl⟩ : syracuseStep 894773 = 83885) (by norm_num)
theorem B894797 : Blo 595291 894797 := bbase (se 3 (by rfl) ⟨167774, by rfl⟩ : syracuseStep 894797 = 335549) (by norm_num)
theorem B894821 : Blo 595291 894821 := bbase (se 4 (by rfl) ⟨83889, by rfl⟩ : syracuseStep 894821 = 167779) (by norm_num)
theorem B1615733 : Blo 595291 1615733 := bbase (se 5 (by rfl) ⟨75737, by rfl⟩ : syracuseStep 1615733 = 151475) (by norm_num)
theorem B894845 : Blo 595291 894845 := bbase (se 3 (by rfl) ⟨167783, by rfl⟩ : syracuseStep 894845 = 335567) (by norm_num)
theorem B894869 : Blo 595291 894869 := bbase (se 6 (by rfl) ⟨20973, by rfl⟩ : syracuseStep 894869 = 41947) (by norm_num)
theorem B894893 : Blo 595291 894893 := bbase (se 3 (by rfl) ⟨167792, by rfl⟩ : syracuseStep 894893 = 335585) (by norm_num)
theorem B894917 : Blo 595291 894917 := bbase (se 4 (by rfl) ⟨83898, by rfl⟩ : syracuseStep 894917 = 167797) (by norm_num)
theorem B894941 : Blo 595291 894941 := bbase (se 3 (by rfl) ⟨167801, by rfl⟩ : syracuseStep 894941 = 335603) (by norm_num)
theorem B894965 : Blo 595291 894965 := bbase (se 5 (by rfl) ⟨41951, by rfl⟩ : syracuseStep 894965 = 83903) (by norm_num)
theorem B894989 : Blo 595291 894989 := bbase (se 3 (by rfl) ⟨167810, by rfl⟩ : syracuseStep 894989 = 335621) (by norm_num)
theorem B7645205 : Blo 595291 7645205 := bbase (se 6 (by rfl) ⟨179184, by rfl⟩ : syracuseStep 7645205 = 358369) (by norm_num)
theorem B9218069 : Blo 595291 9218069 := bbase (se 6 (by rfl) ⟨216048, by rfl⟩ : syracuseStep 9218069 = 432097) (by norm_num)
theorem B895013 : Blo 595291 895013 := bbase (se 4 (by rfl) ⟨83907, by rfl⟩ : syracuseStep 895013 = 167815) (by norm_num)
theorem B895037 : Blo 595291 895037 := bbase (se 3 (by rfl) ⟨167819, by rfl⟩ : syracuseStep 895037 = 335639) (by norm_num)
theorem B895061 : Blo 595291 895061 := bbase (se 8 (by rfl) ⟨5244, by rfl⟩ : syracuseStep 895061 = 10489) (by norm_num)
theorem B895085 : Blo 595291 895085 := bbase (se 3 (by rfl) ⟨167828, by rfl⟩ : syracuseStep 895085 = 335657) (by norm_num)
theorem B2861189 : Blo 595291 2861189 := bbase (se 4 (by rfl) ⟨268236, by rfl⟩ : syracuseStep 2861189 = 536473) (by norm_num)
theorem B895109 : Blo 595291 895109 := bbase (se 4 (by rfl) ⟨83916, by rfl⟩ : syracuseStep 895109 = 167833) (by norm_num)
theorem B764041 : Blo 595291 764041 := bbase (se 2 (by rfl) ⟨286515, by rfl⟩ : syracuseStep 764041 = 573031) (by norm_num)
theorem B895133 : Blo 595291 895133 := bbase (se 3 (by rfl) ⟨167837, by rfl⟩ : syracuseStep 895133 = 335675) (by norm_num)
theorem B895157 : Blo 595291 895157 := bbase (se 5 (by rfl) ⟨41960, by rfl⟩ : syracuseStep 895157 = 83921) (by norm_num)
theorem B2009285 : Blo 595291 2009285 := bbase (se 4 (by rfl) ⟨188370, by rfl⟩ : syracuseStep 2009285 = 376741) (by norm_num)
theorem B895181 : Blo 595291 895181 := bbase (se 3 (by rfl) ⟨167846, by rfl⟩ : syracuseStep 895181 = 335693) (by norm_num)
theorem B895205 : Blo 595291 895205 := bbase (se 4 (by rfl) ⟨83925, by rfl⟩ : syracuseStep 895205 = 167851) (by norm_num)
theorem B895229 : Blo 595291 895229 := bbase (se 3 (by rfl) ⟨167855, by rfl⟩ : syracuseStep 895229 = 335711) (by norm_num)
theorem B895253 : Blo 595291 895253 := bbase (se 6 (by rfl) ⟨20982, by rfl⟩ : syracuseStep 895253 = 41965) (by norm_num)
theorem B895277 : Blo 595291 895277 := bbase (se 3 (by rfl) ⟨167864, by rfl⟩ : syracuseStep 895277 = 335729) (by norm_num)
theorem B895301 : Blo 595291 895301 := bbase (se 4 (by rfl) ⟨83934, by rfl⟩ : syracuseStep 895301 = 167869) (by norm_num)
theorem B895325 : Blo 595291 895325 := bbase (se 3 (by rfl) ⟨167873, by rfl⟩ : syracuseStep 895325 = 335747) (by norm_num)
theorem B895349 : Blo 595291 895349 := bbase (se 5 (by rfl) ⟨41969, by rfl⟩ : syracuseStep 895349 = 83939) (by norm_num)
theorem B3451253 : Blo 595291 3451253 := bbase (se 5 (by rfl) ⟨161777, by rfl⟩ : syracuseStep 3451253 = 323555) (by norm_num)
theorem B895373 : Blo 595291 895373 := bbase (se 3 (by rfl) ⟨167882, by rfl⟩ : syracuseStep 895373 = 335765) (by norm_num)
theorem B895397 : Blo 595291 895397 := bbase (se 4 (by rfl) ⟨83943, by rfl⟩ : syracuseStep 895397 = 167887) (by norm_num)
theorem B895421 : Blo 595291 895421 := bbase (se 3 (by rfl) ⟨167891, by rfl⟩ : syracuseStep 895421 = 335783) (by norm_num)
theorem B3025349 : Blo 595291 3025349 := bbase (se 4 (by rfl) ⟨283626, by rfl⟩ : syracuseStep 3025349 = 567253) (by norm_num)
theorem B2271685 : Blo 595291 2271685 := bbase (se 4 (by rfl) ⟨212970, by rfl⟩ : syracuseStep 2271685 = 425941) (by norm_num)
theorem B895445 : Blo 595291 895445 := bbase (se 7 (by rfl) ⟨10493, by rfl⟩ : syracuseStep 895445 = 20987) (by norm_num)
theorem B7678421 : Blo 595291 7678421 := bbase (se 7 (by rfl) ⟨89981, by rfl⟩ : syracuseStep 7678421 = 179963) (by norm_num)
theorem B895469 : Blo 595291 895469 := bbase (se 3 (by rfl) ⟨167900, by rfl⟩ : syracuseStep 895469 = 335801) (by norm_num)
theorem B895493 : Blo 595291 895493 := bbase (se 4 (by rfl) ⟨83952, by rfl⟩ : syracuseStep 895493 = 167905) (by norm_num)
theorem B895517 : Blo 595291 895517 := bbase (se 3 (by rfl) ⟨167909, by rfl⟩ : syracuseStep 895517 = 335819) (by norm_num)
theorem B895541 : Blo 595291 895541 := bbase (se 5 (by rfl) ⟨41978, by rfl⟩ : syracuseStep 895541 = 83957) (by norm_num)
theorem B895565 : Blo 595291 895565 := bbase (se 3 (by rfl) ⟨167918, by rfl⟩ : syracuseStep 895565 = 335837) (by norm_num)
theorem B895589 : Blo 595291 895589 := bbase (se 4 (by rfl) ⟨83961, by rfl⟩ : syracuseStep 895589 = 167923) (by norm_num)
theorem B2009717 : Blo 595291 2009717 := bbase (se 5 (by rfl) ⟨94205, by rfl⟩ : syracuseStep 2009717 = 188411) (by norm_num)
theorem B895613 : Blo 595291 895613 := bbase (se 3 (by rfl) ⟨167927, by rfl⟩ : syracuseStep 895613 = 335855) (by norm_num)
theorem B895637 : Blo 595291 895637 := bbase (se 6 (by rfl) ⟨20991, by rfl⟩ : syracuseStep 895637 = 41983) (by norm_num)
theorem B895661 : Blo 595291 895661 := bbase (se 3 (by rfl) ⟨167936, by rfl⟩ : syracuseStep 895661 = 335873) (by norm_num)
theorem B830125 : Blo 595291 830125 := bbase (se 3 (by rfl) ⟨155648, by rfl⟩ : syracuseStep 830125 = 311297) (by norm_num)
theorem B1288885 : Blo 595291 1288885 := bbase (se 5 (by rfl) ⟨60416, by rfl⟩ : syracuseStep 1288885 = 120833) (by norm_num)
theorem B895685 : Blo 595291 895685 := bbase (se 4 (by rfl) ⟨83970, by rfl⟩ : syracuseStep 895685 = 167941) (by norm_num)
theorem B895709 : Blo 595291 895709 := bbase (se 3 (by rfl) ⟨167945, by rfl⟩ : syracuseStep 895709 = 335891) (by norm_num)
theorem B895733 : Blo 595291 895733 := bbase (se 5 (by rfl) ⟨41987, by rfl⟩ : syracuseStep 895733 = 83975) (by norm_num)
theorem B2271989 : Blo 595291 2271989 := bbase (se 5 (by rfl) ⟨106499, by rfl⟩ : syracuseStep 2271989 = 212999) (by norm_num)
theorem B895757 : Blo 595291 895757 := bbase (se 3 (by rfl) ⟨167954, by rfl⟩ : syracuseStep 895757 = 335909) (by norm_num)
theorem B895781 : Blo 595291 895781 := bbase (se 4 (by rfl) ⟨83979, by rfl⟩ : syracuseStep 895781 = 167959) (by norm_num)
theorem B895805 : Blo 595291 895805 := bbase (se 3 (by rfl) ⟨167963, by rfl⟩ : syracuseStep 895805 = 335927) (by norm_num)
theorem B895829 : Blo 595291 895829 := bbase (se 9 (by rfl) ⟨2624, by rfl⟩ : syracuseStep 895829 = 5249) (by norm_num)
theorem B895853 : Blo 595291 895853 := bbase (se 3 (by rfl) ⟨167972, by rfl⟩ : syracuseStep 895853 = 335945) (by norm_num)
theorem B895877 : Blo 595291 895877 := bbase (se 4 (by rfl) ⟨83988, by rfl⟩ : syracuseStep 895877 = 167977) (by norm_num)
theorem B1911701 : Blo 595291 1911701 := bbase (se 6 (by rfl) ⟨44805, by rfl⟩ : syracuseStep 1911701 = 89611) (by norm_num)
theorem B895901 : Blo 595291 895901 := bbase (se 3 (by rfl) ⟨167981, by rfl⟩ : syracuseStep 895901 = 335963) (by norm_num)
theorem B895925 : Blo 595291 895925 := bbase (se 5 (by rfl) ⟨41996, by rfl⟩ : syracuseStep 895925 = 83993) (by norm_num)
theorem B895949 : Blo 595291 895949 := bbase (se 3 (by rfl) ⟨167990, by rfl⟩ : syracuseStep 895949 = 335981) (by norm_num)
theorem B895973 : Blo 595291 895973 := bbase (se 4 (by rfl) ⟨83997, by rfl⟩ : syracuseStep 895973 = 167995) (by norm_num)
theorem B1289197 : Blo 595291 1289197 := bbase (se 3 (by rfl) ⟨241724, by rfl⟩ : syracuseStep 1289197 = 483449) (by norm_num)
theorem B895997 : Blo 595291 895997 := bbase (se 3 (by rfl) ⟨167999, by rfl⟩ : syracuseStep 895997 = 335999) (by norm_num)
theorem B896021 : Blo 595291 896021 := bbase (se 6 (by rfl) ⟨21000, by rfl⟩ : syracuseStep 896021 = 42001) (by norm_num)
theorem B2010149 : Blo 595291 2010149 := bbase (se 4 (by rfl) ⟨188451, by rfl⟩ : syracuseStep 2010149 = 376903) (by norm_num)
theorem B896045 : Blo 595291 896045 := bbase (se 3 (by rfl) ⟨168008, by rfl⟩ : syracuseStep 896045 = 336017) (by norm_num)
theorem B896069 : Blo 595291 896069 := bbase (se 4 (by rfl) ⟨84006, by rfl⟩ : syracuseStep 896069 = 168013) (by norm_num)
theorem B896093 : Blo 595291 896093 := bbase (se 3 (by rfl) ⟨168017, by rfl⟩ : syracuseStep 896093 = 336035) (by norm_num)
theorem B896117 : Blo 595291 896117 := bbase (se 5 (by rfl) ⟨42005, by rfl⟩ : syracuseStep 896117 = 84011) (by norm_num)
theorem B896141 : Blo 595291 896141 := bbase (se 3 (by rfl) ⟨168026, by rfl⟩ : syracuseStep 896141 = 336053) (by norm_num)
theorem B896165 : Blo 595291 896165 := bbase (se 4 (by rfl) ⟨84015, by rfl⟩ : syracuseStep 896165 = 168031) (by norm_num)
theorem B896189 : Blo 595291 896189 := bbase (se 3 (by rfl) ⟨168035, by rfl⟩ : syracuseStep 896189 = 336071) (by norm_num)
theorem B896213 : Blo 595291 896213 := bbase (se 7 (by rfl) ⟨10502, by rfl⟩ : syracuseStep 896213 = 21005) (by norm_num)
theorem B896237 : Blo 595291 896237 := bbase (se 3 (by rfl) ⟨168044, by rfl⟩ : syracuseStep 896237 = 336089) (by norm_num)
theorem B3222773 : Blo 595291 3222773 := bbase (se 5 (by rfl) ⟨151067, by rfl⟩ : syracuseStep 3222773 = 302135) (by norm_num)
theorem B896261 : Blo 595291 896261 := bbase (se 4 (by rfl) ⟨84024, by rfl⟩ : syracuseStep 896261 = 168049) (by norm_num)
theorem B896285 : Blo 595291 896285 := bbase (se 3 (by rfl) ⟨168053, by rfl⟩ : syracuseStep 896285 = 336107) (by norm_num)
theorem B896309 : Blo 595291 896309 := bbase (se 5 (by rfl) ⟨42014, by rfl⟩ : syracuseStep 896309 = 84029) (by norm_num)
theorem B896333 : Blo 595291 896333 := bbase (se 3 (by rfl) ⟨168062, by rfl⟩ : syracuseStep 896333 = 336125) (by norm_num)
theorem B896357 : Blo 595291 896357 := bbase (se 4 (by rfl) ⟨84033, by rfl⟩ : syracuseStep 896357 = 168067) (by norm_num)
theorem B896381 : Blo 595291 896381 := bbase (se 3 (by rfl) ⟨168071, by rfl⟩ : syracuseStep 896381 = 336143) (by norm_num)
theorem B896405 : Blo 595291 896405 := bbase (se 6 (by rfl) ⟨21009, by rfl⟩ : syracuseStep 896405 = 42019) (by norm_num)
theorem B896429 : Blo 595291 896429 := bbase (se 3 (by rfl) ⟨168080, by rfl⟩ : syracuseStep 896429 = 336161) (by norm_num)
theorem B2862533 : Blo 595291 2862533 := bbase (se 4 (by rfl) ⟨268362, by rfl⟩ : syracuseStep 2862533 = 536725) (by norm_num)
theorem B896453 : Blo 595291 896453 := bbase (se 4 (by rfl) ⟨84042, by rfl⟩ : syracuseStep 896453 = 168085) (by norm_num)
theorem B2010581 : Blo 595291 2010581 := bbase (se 7 (by rfl) ⟨23561, by rfl⟩ : syracuseStep 2010581 = 47123) (by norm_num)
theorem B896477 : Blo 595291 896477 := bbase (se 3 (by rfl) ⟨168089, by rfl⟩ : syracuseStep 896477 = 336179) (by norm_num)
theorem B896501 : Blo 595291 896501 := bbase (se 5 (by rfl) ⟨42023, by rfl⟩ : syracuseStep 896501 = 84047) (by norm_num)
theorem B896525 : Blo 595291 896525 := bbase (se 3 (by rfl) ⟨168098, by rfl⟩ : syracuseStep 896525 = 336197) (by norm_num)
theorem B896549 : Blo 595291 896549 := bbase (se 4 (by rfl) ⟨84051, by rfl⟩ : syracuseStep 896549 = 168103) (by norm_num)
theorem B896573 : Blo 595291 896573 := bbase (se 3 (by rfl) ⟨168107, by rfl⟩ : syracuseStep 896573 = 336215) (by norm_num)
theorem B896597 : Blo 595291 896597 := bbase (se 8 (by rfl) ⟨5253, by rfl⟩ : syracuseStep 896597 = 10507) (by norm_num)
theorem B831061 : Blo 595291 831061 := bbase (se 8 (by rfl) ⟨4869, by rfl⟩ : syracuseStep 831061 = 9739) (by norm_num)
theorem B896621 : Blo 595291 896621 := bbase (se 3 (by rfl) ⟨168116, by rfl⟩ : syracuseStep 896621 = 336233) (by norm_num)
theorem B896645 : Blo 595291 896645 := bbase (se 4 (by rfl) ⟨84060, by rfl⟩ : syracuseStep 896645 = 168121) (by norm_num)
theorem B896669 : Blo 595291 896669 := bbase (se 3 (by rfl) ⟨168125, by rfl⟩ : syracuseStep 896669 = 336251) (by norm_num)
theorem B1814197 : Blo 595291 1814197 := bbase (se 5 (by rfl) ⟨85040, by rfl⟩ : syracuseStep 1814197 = 170081) (by norm_num)
theorem B896693 : Blo 595291 896693 := bbase (se 5 (by rfl) ⟨42032, by rfl⟩ : syracuseStep 896693 = 84065) (by norm_num)
theorem B896717 : Blo 595291 896717 := bbase (se 3 (by rfl) ⟨168134, by rfl⟩ : syracuseStep 896717 = 336269) (by norm_num)
theorem B3026645 : Blo 595291 3026645 := bbase (se 7 (by rfl) ⟨35468, by rfl⟩ : syracuseStep 3026645 = 70937) (by norm_num)
theorem B896741 : Blo 595291 896741 := bbase (se 4 (by rfl) ⟨84069, by rfl⟩ : syracuseStep 896741 = 168139) (by norm_num)
theorem B896765 : Blo 595291 896765 := bbase (se 3 (by rfl) ⟨168143, by rfl⟩ : syracuseStep 896765 = 336287) (by norm_num)
theorem B896789 : Blo 595291 896789 := bbase (se 6 (by rfl) ⟨21018, by rfl⟩ : syracuseStep 896789 = 42037) (by norm_num)
theorem B896813 : Blo 595291 896813 := bbase (se 3 (by rfl) ⟨168152, by rfl⟩ : syracuseStep 896813 = 336305) (by norm_num)
theorem B896837 : Blo 595291 896837 := bbase (se 4 (by rfl) ⟨84078, by rfl⟩ : syracuseStep 896837 = 168157) (by norm_num)
theorem B896861 : Blo 595291 896861 := bbase (se 3 (by rfl) ⟨168161, by rfl⟩ : syracuseStep 896861 = 336323) (by norm_num)
theorem B896885 : Blo 595291 896885 := bbase (se 5 (by rfl) ⟨42041, by rfl⟩ : syracuseStep 896885 = 84083) (by norm_num)
theorem B2011013 : Blo 595291 2011013 := bbase (se 4 (by rfl) ⟨188532, by rfl⟩ : syracuseStep 2011013 = 377065) (by norm_num)
theorem B896909 : Blo 595291 896909 := bbase (se 3 (by rfl) ⟨168170, by rfl⟩ : syracuseStep 896909 = 336341) (by norm_num)
theorem B896933 : Blo 595291 896933 := bbase (se 4 (by rfl) ⟨84087, by rfl⟩ : syracuseStep 896933 = 168175) (by norm_num)
theorem B896957 : Blo 595291 896957 := bbase (se 3 (by rfl) ⟨168179, by rfl⟩ : syracuseStep 896957 = 336359) (by norm_num)
theorem B896981 : Blo 595291 896981 := bbase (se 7 (by rfl) ⟨10511, by rfl⟩ : syracuseStep 896981 = 21023) (by norm_num)
theorem B897005 : Blo 595291 897005 := bbase (se 3 (by rfl) ⟨168188, by rfl⟩ : syracuseStep 897005 = 336377) (by norm_num)
theorem B897029 : Blo 595291 897029 := bbase (se 4 (by rfl) ⟨84096, by rfl⟩ : syracuseStep 897029 = 168193) (by norm_num)
theorem B897053 : Blo 595291 897053 := bbase (se 3 (by rfl) ⟨168197, by rfl⟩ : syracuseStep 897053 = 336395) (by norm_num)
theorem B897077 : Blo 595291 897077 := bbase (se 5 (by rfl) ⟨42050, by rfl⟩ : syracuseStep 897077 = 84101) (by norm_num)
theorem B897101 : Blo 595291 897101 := bbase (se 3 (by rfl) ⟨168206, by rfl⟩ : syracuseStep 897101 = 336413) (by norm_num)
theorem B897125 : Blo 595291 897125 := bbase (se 4 (by rfl) ⟨84105, by rfl⟩ : syracuseStep 897125 = 168211) (by norm_num)
theorem B897149 : Blo 595291 897149 := bbase (se 3 (by rfl) ⟨168215, by rfl⟩ : syracuseStep 897149 = 336431) (by norm_num)
theorem B2044037 : Blo 595291 2044037 := bbase (se 4 (by rfl) ⟨191628, by rfl⟩ : syracuseStep 2044037 = 383257) (by norm_num)
theorem B897173 : Blo 595291 897173 := bbase (se 6 (by rfl) ⟨21027, by rfl⟩ : syracuseStep 897173 = 42055) (by norm_num)
theorem B897197 : Blo 595291 897197 := bbase (se 3 (by rfl) ⟨168224, by rfl⟩ : syracuseStep 897197 = 336449) (by norm_num)
theorem B897221 : Blo 595291 897221 := bbase (se 4 (by rfl) ⟨84114, by rfl⟩ : syracuseStep 897221 = 168229) (by norm_num)
theorem B6140117 : Blo 595291 6140117 := bbase (se 7 (by rfl) ⟨71954, by rfl⟩ : syracuseStep 6140117 = 143909) (by norm_num)
theorem B897245 : Blo 595291 897245 := bbase (se 3 (by rfl) ⟨168233, by rfl⟩ : syracuseStep 897245 = 336467) (by norm_num)
theorem B897269 : Blo 595291 897269 := bbase (se 5 (by rfl) ⟨42059, by rfl⟩ : syracuseStep 897269 = 84119) (by norm_num)
theorem B897293 : Blo 595291 897293 := bbase (se 3 (by rfl) ⟨168242, by rfl⟩ : syracuseStep 897293 = 336485) (by norm_num)
theorem B897317 : Blo 595291 897317 := bbase (se 4 (by rfl) ⟨84123, by rfl⟩ : syracuseStep 897317 = 168247) (by norm_num)
theorem B2011445 : Blo 595291 2011445 := bbase (se 5 (by rfl) ⟨94286, by rfl⟩ : syracuseStep 2011445 = 188573) (by norm_num)
theorem B897341 : Blo 595291 897341 := bbase (se 3 (by rfl) ⟨168251, by rfl⟩ : syracuseStep 897341 = 336503) (by norm_num)
theorem B897365 : Blo 595291 897365 := bbase (se 10 (by rfl) ⟨1314, by rfl⟩ : syracuseStep 897365 = 2629) (by norm_num)
theorem B897389 : Blo 595291 897389 := bbase (se 3 (by rfl) ⟨168260, by rfl⟩ : syracuseStep 897389 = 336521) (by norm_num)
theorem B897413 : Blo 595291 897413 := bbase (se 4 (by rfl) ⟨84132, by rfl⟩ : syracuseStep 897413 = 168265) (by norm_num)
theorem B897437 : Blo 595291 897437 := bbase (se 3 (by rfl) ⟨168269, by rfl⟩ : syracuseStep 897437 = 336539) (by norm_num)
theorem B897461 : Blo 595291 897461 := bbase (se 5 (by rfl) ⟨42068, by rfl⟩ : syracuseStep 897461 = 84137) (by norm_num)
theorem B897485 : Blo 595291 897485 := bbase (se 3 (by rfl) ⟨168278, by rfl⟩ : syracuseStep 897485 = 336557) (by norm_num)
theorem B897509 : Blo 595291 897509 := bbase (se 4 (by rfl) ⟨84141, by rfl⟩ : syracuseStep 897509 = 168283) (by norm_num)
theorem B897533 : Blo 595291 897533 := bbase (se 3 (by rfl) ⟨168287, by rfl⟩ : syracuseStep 897533 = 336575) (by norm_num)
theorem B897557 : Blo 595291 897557 := bbase (se 6 (by rfl) ⟨21036, by rfl⟩ : syracuseStep 897557 = 42073) (by norm_num)
theorem B897581 : Blo 595291 897581 := bbase (se 3 (by rfl) ⟨168296, by rfl⟩ : syracuseStep 897581 = 336593) (by norm_num)
theorem B897605 : Blo 595291 897605 := bbase (se 4 (by rfl) ⟨84150, by rfl⟩ : syracuseStep 897605 = 168301) (by norm_num)
theorem B897629 : Blo 595291 897629 := bbase (se 3 (by rfl) ⟨168305, by rfl⟩ : syracuseStep 897629 = 336611) (by norm_num)
theorem B897653 : Blo 595291 897653 := bbase (se 5 (by rfl) ⟨42077, by rfl⟩ : syracuseStep 897653 = 84155) (by norm_num)
theorem B766597 : Blo 595291 766597 := bbase (se 4 (by rfl) ⟨71868, by rfl⟩ : syracuseStep 766597 = 143737) (by norm_num)
theorem B897677 : Blo 595291 897677 := bbase (se 3 (by rfl) ⟨168314, by rfl⟩ : syracuseStep 897677 = 336629) (by norm_num)
theorem B897701 : Blo 595291 897701 := bbase (se 4 (by rfl) ⟨84159, by rfl⟩ : syracuseStep 897701 = 168319) (by norm_num)
theorem B897725 : Blo 595291 897725 := bbase (se 3 (by rfl) ⟨168323, by rfl⟩ : syracuseStep 897725 = 336647) (by norm_num)
theorem B1913557 : Blo 595291 1913557 := bbase (se 7 (by rfl) ⟨22424, by rfl⟩ : syracuseStep 1913557 = 44849) (by norm_num)
theorem B897749 : Blo 595291 897749 := bbase (se 7 (by rfl) ⟨10520, by rfl⟩ : syracuseStep 897749 = 21041) (by norm_num)
theorem B2011877 : Blo 595291 2011877 := bbase (se 4 (by rfl) ⟨188613, by rfl⟩ : syracuseStep 2011877 = 377227) (by norm_num)
theorem B897773 : Blo 595291 897773 := bbase (se 3 (by rfl) ⟨168332, by rfl⟩ : syracuseStep 897773 = 336665) (by norm_num)
theorem B897797 : Blo 595291 897797 := bbase (se 4 (by rfl) ⟨84168, by rfl⟩ : syracuseStep 897797 = 168337) (by norm_num)
theorem B1815317 : Blo 595291 1815317 := bbase (se 6 (by rfl) ⟨42546, by rfl⟩ : syracuseStep 1815317 = 85093) (by norm_num)
theorem B897821 : Blo 595291 897821 := bbase (se 3 (by rfl) ⟨168341, by rfl⟩ : syracuseStep 897821 = 336683) (by norm_num)
theorem B897845 : Blo 595291 897845 := bbase (se 5 (by rfl) ⟨42086, by rfl⟩ : syracuseStep 897845 = 84173) (by norm_num)
theorem B2274101 : Blo 595291 2274101 := bbase (se 5 (by rfl) ⟨106598, by rfl⟩ : syracuseStep 2274101 = 213197) (by norm_num)
theorem B1815365 : Blo 595291 1815365 := bbase (se 4 (by rfl) ⟨170190, by rfl⟩ : syracuseStep 1815365 = 340381) (by norm_num)
theorem B897869 : Blo 595291 897869 := bbase (se 3 (by rfl) ⟨168350, by rfl⟩ : syracuseStep 897869 = 336701) (by norm_num)
theorem B2732885 : Blo 595291 2732885 := bbase (se 9 (by rfl) ⟨8006, by rfl⟩ : syracuseStep 2732885 = 16013) (by norm_num)
theorem B897893 : Blo 595291 897893 := bbase (se 4 (by rfl) ⟨84177, by rfl⟩ : syracuseStep 897893 = 168355) (by norm_num)
theorem B897917 : Blo 595291 897917 := bbase (se 3 (by rfl) ⟨168359, by rfl⟩ : syracuseStep 897917 = 336719) (by norm_num)
theorem B897941 : Blo 595291 897941 := bbase (se 6 (by rfl) ⟨21045, by rfl⟩ : syracuseStep 897941 = 42091) (by norm_num)
theorem B897965 : Blo 595291 897965 := bbase (se 3 (by rfl) ⟨168368, by rfl⟩ : syracuseStep 897965 = 336737) (by norm_num)
theorem B635845 : Blo 595291 635845 := bbase (se 4 (by rfl) ⟨59610, by rfl⟩ : syracuseStep 635845 = 119221) (by norm_num)
theorem B897989 : Blo 595291 897989 := bbase (se 4 (by rfl) ⟨84186, by rfl⟩ : syracuseStep 897989 = 168373) (by norm_num)
theorem B898013 : Blo 595291 898013 := bbase (se 3 (by rfl) ⟨168377, by rfl⟩ : syracuseStep 898013 = 336755) (by norm_num)
theorem B3027941 : Blo 595291 3027941 := bbase (se 4 (by rfl) ⟨283869, by rfl⟩ : syracuseStep 3027941 = 567739) (by norm_num)
theorem B898037 : Blo 595291 898037 := bbase (se 5 (by rfl) ⟨42095, by rfl⟩ : syracuseStep 898037 = 84191) (by norm_num)
theorem B898061 : Blo 595291 898061 := bbase (se 3 (by rfl) ⟨168386, by rfl⟩ : syracuseStep 898061 = 336773) (by norm_num)
theorem B898085 : Blo 595291 898085 := bbase (se 4 (by rfl) ⟨84195, by rfl⟩ : syracuseStep 898085 = 168391) (by norm_num)
theorem B3224629 : Blo 595291 3224629 := bbase (se 5 (by rfl) ⟨151154, by rfl⟩ : syracuseStep 3224629 = 302309) (by norm_num)
theorem B898109 : Blo 595291 898109 := bbase (se 3 (by rfl) ⟨168395, by rfl⟩ : syracuseStep 898109 = 336791) (by norm_num)
theorem B635969 : Blo 595291 635969 := bbase (se 2 (by rfl) ⟨238488, by rfl⟩ : syracuseStep 635969 = 476977) (by norm_num)
theorem B898133 : Blo 595291 898133 := bbase (se 8 (by rfl) ⟨5262, by rfl⟩ : syracuseStep 898133 = 10525) (by norm_num)
theorem B2274389 : Blo 595291 2274389 := bbase (se 8 (by rfl) ⟨13326, by rfl⟩ : syracuseStep 2274389 = 26653) (by norm_num)
theorem B898157 : Blo 595291 898157 := bbase (se 3 (by rfl) ⟨168404, by rfl⟩ : syracuseStep 898157 = 336809) (by norm_num)
theorem B898181 : Blo 595291 898181 := bbase (se 4 (by rfl) ⟨84204, by rfl⟩ : syracuseStep 898181 = 168409) (by norm_num)
theorem B2012309 : Blo 595291 2012309 := bbase (se 6 (by rfl) ⟨47163, by rfl⟩ : syracuseStep 2012309 = 94327) (by norm_num)
theorem B1422485 : Blo 595291 1422485 := bbase (se 6 (by rfl) ⟨33339, by rfl⟩ : syracuseStep 1422485 = 66679) (by norm_num)
theorem B898205 : Blo 595291 898205 := bbase (se 3 (by rfl) ⟨168413, by rfl⟩ : syracuseStep 898205 = 336827) (by norm_num)
theorem B898229 : Blo 595291 898229 := bbase (se 5 (by rfl) ⟨42104, by rfl⟩ : syracuseStep 898229 = 84209) (by norm_num)
theorem B898253 : Blo 595291 898253 := bbase (se 3 (by rfl) ⟨168422, by rfl⟩ : syracuseStep 898253 = 336845) (by norm_num)
theorem B898277 : Blo 595291 898277 := bbase (se 4 (by rfl) ⟨84213, by rfl⟩ : syracuseStep 898277 = 168427) (by norm_num)
theorem B898301 : Blo 595291 898301 := bbase (se 3 (by rfl) ⟨168431, by rfl⟩ : syracuseStep 898301 = 336863) (by norm_num)
theorem B898325 : Blo 595291 898325 := bbase (se 6 (by rfl) ⟨21054, by rfl⟩ : syracuseStep 898325 = 42109) (by norm_num)
theorem B898349 : Blo 595291 898349 := bbase (se 3 (by rfl) ⟨168440, by rfl⟩ : syracuseStep 898349 = 336881) (by norm_num)
theorem B636221 : Blo 595291 636221 := bbase (se 3 (by rfl) ⟨119291, by rfl⟩ : syracuseStep 636221 = 238583) (by norm_num)
theorem B898373 : Blo 595291 898373 := bbase (se 4 (by rfl) ⟨84222, by rfl⟩ : syracuseStep 898373 = 168445) (by norm_num)
theorem B898397 : Blo 595291 898397 := bbase (se 3 (by rfl) ⟨168449, by rfl⟩ : syracuseStep 898397 = 336899) (by norm_num)
theorem B898421 : Blo 595291 898421 := bbase (se 5 (by rfl) ⟨42113, by rfl⟩ : syracuseStep 898421 = 84227) (by norm_num)
theorem B898445 : Blo 595291 898445 := bbase (se 3 (by rfl) ⟨168458, by rfl⟩ : syracuseStep 898445 = 336917) (by norm_num)
theorem B898469 : Blo 595291 898469 := bbase (se 4 (by rfl) ⟨84231, by rfl⟩ : syracuseStep 898469 = 168463) (by norm_num)
theorem B898493 : Blo 595291 898493 := bbase (se 3 (by rfl) ⟨168467, by rfl⟩ : syracuseStep 898493 = 336935) (by norm_num)
theorem B898517 : Blo 595291 898517 := bbase (se 7 (by rfl) ⟨10529, by rfl⟩ : syracuseStep 898517 = 21059) (by norm_num)
theorem B898541 : Blo 595291 898541 := bbase (se 3 (by rfl) ⟨168476, by rfl⟩ : syracuseStep 898541 = 336953) (by norm_num)
theorem B898565 : Blo 595291 898565 := bbase (se 4 (by rfl) ⟨84240, by rfl⟩ : syracuseStep 898565 = 168481) (by norm_num)
theorem B898589 : Blo 595291 898589 := bbase (se 3 (by rfl) ⟨168485, by rfl⟩ : syracuseStep 898589 = 336971) (by norm_num)
theorem B898613 : Blo 595291 898613 := bbase (se 5 (by rfl) ⟨42122, by rfl⟩ : syracuseStep 898613 = 84245) (by norm_num)
theorem B2012741 : Blo 595291 2012741 := bbase (se 4 (by rfl) ⟨188694, by rfl⟩ : syracuseStep 2012741 = 377389) (by norm_num)
theorem B898637 : Blo 595291 898637 := bbase (se 3 (by rfl) ⟨168494, by rfl⟩ : syracuseStep 898637 = 336989) (by norm_num)
theorem B898661 : Blo 595291 898661 := bbase (se 4 (by rfl) ⟨84249, by rfl⟩ : syracuseStep 898661 = 168499) (by norm_num)
theorem B898685 : Blo 595291 898685 := bbase (se 3 (by rfl) ⟨168503, by rfl⟩ : syracuseStep 898685 = 337007) (by norm_num)
theorem B898709 : Blo 595291 898709 := bbase (se 6 (by rfl) ⟨21063, by rfl⟩ : syracuseStep 898709 = 42127) (by norm_num)
theorem B898733 : Blo 595291 898733 := bbase (se 3 (by rfl) ⟨168512, by rfl⟩ : syracuseStep 898733 = 337025) (by norm_num)
theorem B898757 : Blo 595291 898757 := bbase (se 4 (by rfl) ⟨84258, by rfl⟩ : syracuseStep 898757 = 168517) (by norm_num)
theorem B898781 : Blo 595291 898781 := bbase (se 3 (by rfl) ⟨168521, by rfl⟩ : syracuseStep 898781 = 337043) (by norm_num)
theorem B898805 : Blo 595291 898805 := bbase (se 5 (by rfl) ⟨42131, by rfl⟩ : syracuseStep 898805 = 84263) (by norm_num)
theorem B636665 : Blo 595291 636665 := bbase (se 2 (by rfl) ⟨238749, by rfl⟩ : syracuseStep 636665 = 477499) (by norm_num)
theorem B898829 : Blo 595291 898829 := bbase (se 3 (by rfl) ⟨168530, by rfl⟩ : syracuseStep 898829 = 337061) (by norm_num)
theorem B898853 : Blo 595291 898853 := bbase (se 4 (by rfl) ⟨84267, by rfl⟩ : syracuseStep 898853 = 168535) (by norm_num)
theorem B898877 : Blo 595291 898877 := bbase (se 3 (by rfl) ⟨168539, by rfl⟩ : syracuseStep 898877 = 337079) (by norm_num)
theorem B898901 : Blo 595291 898901 := bbase (se 9 (by rfl) ⟨2633, by rfl⟩ : syracuseStep 898901 = 5267) (by norm_num)
theorem B898925 : Blo 595291 898925 := bbase (se 3 (by rfl) ⟨168548, by rfl⟩ : syracuseStep 898925 = 337097) (by norm_num)
theorem B636913 : Blo 595291 636913 := bbase (se 2 (by rfl) ⟨238842, by rfl⟩ : syracuseStep 636913 = 477685) (by norm_num)
theorem B2013173 : Blo 595291 2013173 := bbase (se 5 (by rfl) ⟨94367, by rfl⟩ : syracuseStep 2013173 = 188735) (by norm_num)
theorem B669721 : Blo 595291 669721 := bbase (se 2 (by rfl) ⟨251145, by rfl⟩ : syracuseStep 669721 = 502291) (by norm_num)
theorem B604193 : Blo 595291 604193 := bbase (se 2 (by rfl) ⟨226572, by rfl⟩ : syracuseStep 604193 = 453145) (by norm_num)
theorem B669757 : Blo 595291 669757 := bbase (se 3 (by rfl) ⟨125579, by rfl⟩ : syracuseStep 669757 = 251159) (by norm_num)
theorem B669793 : Blo 595291 669793 := bbase (se 2 (by rfl) ⟨251172, by rfl⟩ : syracuseStep 669793 = 502345) (by norm_num)
theorem B669829 : Blo 595291 669829 := bbase (se 4 (by rfl) ⟨62796, by rfl⟩ : syracuseStep 669829 = 125593) (by norm_num)
theorem B4307093 : Blo 595291 4307093 := bbase (se 6 (by rfl) ⟨100947, by rfl⟩ : syracuseStep 4307093 = 201895) (by norm_num)
theorem B669865 : Blo 595291 669865 := bbase (se 2 (by rfl) ⟨251199, by rfl⟩ : syracuseStep 669865 = 502399) (by norm_num)
theorem B669901 : Blo 595291 669901 := bbase (se 3 (by rfl) ⟨125606, by rfl⟩ : syracuseStep 669901 = 251213) (by norm_num)
theorem B669937 : Blo 595291 669937 := bbase (se 2 (by rfl) ⟨251226, by rfl⟩ : syracuseStep 669937 = 502453) (by norm_num)
theorem B3029237 : Blo 595291 3029237 := bbase (se 5 (by rfl) ⟨141995, by rfl⟩ : syracuseStep 3029237 = 283991) (by norm_num)
theorem B669973 : Blo 595291 669973 := bbase (se 6 (by rfl) ⟨15702, by rfl⟩ : syracuseStep 669973 = 31405) (by norm_num)
theorem B670009 : Blo 595291 670009 := bbase (se 2 (by rfl) ⟨251253, by rfl⟩ : syracuseStep 670009 = 502507) (by norm_num)
theorem B670045 : Blo 595291 670045 := bbase (se 3 (by rfl) ⟨125633, by rfl⟩ : syracuseStep 670045 = 251267) (by norm_num)
theorem B670081 : Blo 595291 670081 := bbase (se 2 (by rfl) ⟨251280, by rfl⟩ : syracuseStep 670081 = 502561) (by norm_num)
theorem B670117 : Blo 595291 670117 := bbase (se 4 (by rfl) ⟨62823, by rfl⟩ : syracuseStep 670117 = 125647) (by norm_num)
theorem B2013605 : Blo 595291 2013605 := bbase (se 4 (by rfl) ⟨188775, by rfl⟩ : syracuseStep 2013605 = 377551) (by norm_num)
theorem B637357 : Blo 595291 637357 := bbase (se 3 (by rfl) ⟨119504, by rfl⟩ : syracuseStep 637357 = 239009) (by norm_num)
theorem B670153 : Blo 595291 670153 := bbase (se 2 (by rfl) ⟨251307, by rfl⟩ : syracuseStep 670153 = 502615) (by norm_num)
theorem B637417 : Blo 595291 637417 := bbase (se 2 (by rfl) ⟨239031, by rfl⟩ : syracuseStep 637417 = 478063) (by norm_num)
theorem B670189 : Blo 595291 670189 := bbase (se 3 (by rfl) ⟨125660, by rfl⟩ : syracuseStep 670189 = 251321) (by norm_num)
theorem B670225 : Blo 595291 670225 := bbase (se 2 (by rfl) ⟨251334, by rfl⟩ : syracuseStep 670225 = 502669) (by norm_num)
theorem B670261 : Blo 595291 670261 := bbase (se 5 (by rfl) ⟨31418, by rfl⟩ : syracuseStep 670261 = 62837) (by norm_num)
theorem B670297 : Blo 595291 670297 := bbase (se 2 (by rfl) ⟨251361, by rfl⟩ : syracuseStep 670297 = 502723) (by norm_num)
theorem B604777 : Blo 595291 604777 := bbase (se 2 (by rfl) ⟨226791, by rfl⟩ : syracuseStep 604777 = 453583) (by norm_num)
theorem B604789 : Blo 595291 604789 := bbase (se 5 (by rfl) ⟨28349, by rfl⟩ : syracuseStep 604789 = 56699) (by norm_num)
theorem B670333 : Blo 595291 670333 := bbase (se 3 (by rfl) ⟨125687, by rfl⟩ : syracuseStep 670333 = 251375) (by norm_num)
theorem B670369 : Blo 595291 670369 := bbase (se 2 (by rfl) ⟨251388, by rfl⟩ : syracuseStep 670369 = 502777) (by norm_num)
theorem B670405 : Blo 595291 670405 := bbase (se 4 (by rfl) ⟨62850, by rfl⟩ : syracuseStep 670405 = 125701) (by norm_num)
theorem B670441 : Blo 595291 670441 := bbase (se 2 (by rfl) ⟨251415, by rfl⟩ : syracuseStep 670441 = 502831) (by norm_num)
theorem B670477 : Blo 595291 670477 := bbase (se 3 (by rfl) ⟨125714, by rfl⟩ : syracuseStep 670477 = 251429) (by norm_num)
theorem B637733 : Blo 595291 637733 := bbase (se 4 (by rfl) ⟨59787, by rfl⟩ : syracuseStep 637733 = 119575) (by norm_num)
theorem B670513 : Blo 595291 670513 := bbase (se 2 (by rfl) ⟨251442, by rfl⟩ : syracuseStep 670513 = 502885) (by norm_num)
theorem B670549 : Blo 595291 670549 := bbase (se 9 (by rfl) ⟨1964, by rfl⟩ : syracuseStep 670549 = 3929) (by norm_num)
theorem B2014037 : Blo 595291 2014037 := bbase (se 9 (by rfl) ⟨5900, by rfl⟩ : syracuseStep 2014037 = 11801) (by norm_num)
theorem B670585 : Blo 595291 670585 := bbase (se 2 (by rfl) ⟨251469, by rfl⟩ : syracuseStep 670585 = 502939) (by norm_num)
theorem B670621 : Blo 595291 670621 := bbase (se 3 (by rfl) ⟨125741, by rfl⟩ : syracuseStep 670621 = 251483) (by norm_num)
theorem B670657 : Blo 595291 670657 := bbase (se 2 (by rfl) ⟨251496, by rfl⟩ : syracuseStep 670657 = 502993) (by norm_num)
theorem B670693 : Blo 595291 670693 := bbase (se 4 (by rfl) ⟨62877, by rfl⟩ : syracuseStep 670693 = 125755) (by norm_num)
theorem B670729 : Blo 595291 670729 := bbase (se 2 (by rfl) ⟨251523, by rfl⟩ : syracuseStep 670729 = 503047) (by norm_num)
theorem B670765 : Blo 595291 670765 := bbase (se 3 (by rfl) ⟨125768, by rfl⟩ : syracuseStep 670765 = 251537) (by norm_num)
theorem B670801 : Blo 595291 670801 := bbase (se 2 (by rfl) ⟨251550, by rfl⟩ : syracuseStep 670801 = 503101) (by norm_num)
theorem B1162325 : Blo 595291 1162325 := bbase (se 8 (by rfl) ⟨6810, by rfl⟩ : syracuseStep 1162325 = 13621) (by norm_num)
theorem B2866261 : Blo 595291 2866261 := bbase (se 8 (by rfl) ⟨16794, by rfl⟩ : syracuseStep 2866261 = 33589) (by norm_num)
theorem B670837 : Blo 595291 670837 := bbase (se 5 (by rfl) ⟨31445, by rfl⟩ : syracuseStep 670837 = 62891) (by norm_num)
theorem B670873 : Blo 595291 670873 := bbase (se 2 (by rfl) ⟨251577, by rfl⟩ : syracuseStep 670873 = 503155) (by norm_num)
theorem B670909 : Blo 595291 670909 := bbase (se 3 (by rfl) ⟨125795, by rfl⟩ : syracuseStep 670909 = 251591) (by norm_num)
theorem B670945 : Blo 595291 670945 := bbase (se 2 (by rfl) ⟨251604, by rfl⟩ : syracuseStep 670945 = 503209) (by norm_num)
theorem B638177 : Blo 595291 638177 := bbase (se 2 (by rfl) ⟨239316, by rfl⟩ : syracuseStep 638177 = 478633) (by norm_num)
theorem B670981 : Blo 595291 670981 := bbase (se 4 (by rfl) ⟨62904, by rfl⟩ : syracuseStep 670981 = 125809) (by norm_num)
theorem B2014469 : Blo 595291 2014469 := bbase (se 4 (by rfl) ⟨188856, by rfl⟩ : syracuseStep 2014469 = 377713) (by norm_num)
theorem B638237 : Blo 595291 638237 := bbase (se 3 (by rfl) ⟨119669, by rfl⟩ : syracuseStep 638237 = 239339) (by norm_num)
theorem B671017 : Blo 595291 671017 := bbase (se 2 (by rfl) ⟨251631, by rfl⟩ : syracuseStep 671017 = 503263) (by norm_num)
theorem B671053 : Blo 595291 671053 := bbase (se 3 (by rfl) ⟨125822, by rfl⟩ : syracuseStep 671053 = 251645) (by norm_num)
theorem B671089 : Blo 595291 671089 := bbase (se 2 (by rfl) ⟨251658, by rfl⟩ : syracuseStep 671089 = 503317) (by norm_num)
theorem B671125 : Blo 595291 671125 := bbase (se 6 (by rfl) ⟨15729, by rfl⟩ : syracuseStep 671125 = 31459) (by norm_num)
theorem B638365 : Blo 595291 638365 := bbase (se 3 (by rfl) ⟨119693, by rfl⟩ : syracuseStep 638365 = 239387) (by norm_num)
theorem B4537781 : Blo 595291 4537781 := bbase (se 5 (by rfl) ⟨212708, by rfl⟩ : syracuseStep 4537781 = 425417) (by norm_num)
theorem B671161 : Blo 595291 671161 := bbase (se 2 (by rfl) ⟨251685, by rfl⟩ : syracuseStep 671161 = 503371) (by norm_num)
theorem B671197 : Blo 595291 671197 := bbase (se 3 (by rfl) ⟨125849, by rfl⟩ : syracuseStep 671197 = 251699) (by norm_num)
theorem B671233 : Blo 595291 671233 := bbase (se 2 (by rfl) ⟨251712, by rfl⟩ : syracuseStep 671233 = 503425) (by norm_num)
theorem B3030533 : Blo 595291 3030533 := bbase (se 4 (by rfl) ⟨284112, by rfl⟩ : syracuseStep 3030533 = 568225) (by norm_num)
theorem B671269 : Blo 595291 671269 := bbase (se 4 (by rfl) ⟨62931, by rfl⟩ : syracuseStep 671269 = 125863) (by norm_num)
theorem B671305 : Blo 595291 671305 := bbase (se 2 (by rfl) ⟨251739, by rfl⟩ : syracuseStep 671305 = 503479) (by norm_num)
theorem B671341 : Blo 595291 671341 := bbase (se 3 (by rfl) ⟨125876, by rfl⟩ : syracuseStep 671341 = 251753) (by norm_num)
theorem B1130125 : Blo 595291 1130125 := bbase (se 3 (by rfl) ⟨211898, by rfl⟩ : syracuseStep 1130125 = 423797) (by norm_num)
theorem B671377 : Blo 595291 671377 := bbase (se 2 (by rfl) ⟨251766, by rfl⟩ : syracuseStep 671377 = 503533) (by norm_num)
theorem B1359517 : Blo 595291 1359517 := bbase (se 3 (by rfl) ⟨254909, by rfl⟩ : syracuseStep 1359517 = 509819) (by norm_num)
theorem B671413 : Blo 595291 671413 := bbase (se 5 (by rfl) ⟨31472, by rfl⟩ : syracuseStep 671413 = 62945) (by norm_num)
theorem B2014901 : Blo 595291 2014901 := bbase (se 5 (by rfl) ⟨94448, by rfl⟩ : syracuseStep 2014901 = 188897) (by norm_num)
theorem B671449 : Blo 595291 671449 := bbase (se 2 (by rfl) ⟨251793, by rfl⟩ : syracuseStep 671449 = 503587) (by norm_num)
theorem B671485 : Blo 595291 671485 := bbase (se 3 (by rfl) ⟨125903, by rfl⟩ : syracuseStep 671485 = 251807) (by norm_num)
theorem B1130269 : Blo 595291 1130269 := bbase (se 3 (by rfl) ⟨211925, by rfl⟩ : syracuseStep 1130269 = 423851) (by norm_num)
theorem B671521 : Blo 595291 671521 := bbase (se 2 (by rfl) ⟨251820, by rfl⟩ : syracuseStep 671521 = 503641) (by norm_num)
theorem B671557 : Blo 595291 671557 := bbase (se 4 (by rfl) ⟨62958, by rfl⟩ : syracuseStep 671557 = 125917) (by norm_num)
theorem B638809 : Blo 595291 638809 := bbase (se 2 (by rfl) ⟨239553, by rfl⟩ : syracuseStep 638809 = 479107) (by norm_num)
theorem B671593 : Blo 595291 671593 := bbase (se 2 (by rfl) ⟨251847, by rfl⟩ : syracuseStep 671593 = 503695) (by norm_num)
theorem B671629 : Blo 595291 671629 := bbase (se 3 (by rfl) ⟨125930, by rfl⟩ : syracuseStep 671629 = 251861) (by norm_num)
theorem B671665 : Blo 595291 671665 := bbase (se 2 (by rfl) ⟨251874, by rfl⟩ : syracuseStep 671665 = 503749) (by norm_num)
theorem B1130429 : Blo 595291 1130429 := bbase (se 3 (by rfl) ⟨211955, by rfl⟩ : syracuseStep 1130429 = 423911) (by norm_num)
theorem B638929 : Blo 595291 638929 := bbase (se 2 (by rfl) ⟨239598, by rfl⟩ : syracuseStep 638929 = 479197) (by norm_num)
theorem B671701 : Blo 595291 671701 := bbase (se 7 (by rfl) ⟨7871, by rfl⟩ : syracuseStep 671701 = 15743) (by norm_num)
theorem B671737 : Blo 595291 671737 := bbase (se 2 (by rfl) ⟨251901, by rfl⟩ : syracuseStep 671737 = 503803) (by norm_num)
theorem B671773 : Blo 595291 671773 := bbase (se 3 (by rfl) ⟨125957, by rfl⟩ : syracuseStep 671773 = 251915) (by norm_num)
theorem B606241 : Blo 595291 606241 := bbase (se 2 (by rfl) ⟨227340, by rfl⟩ : syracuseStep 606241 = 454681) (by norm_num)
theorem B606269 : Blo 595291 606269 := bbase (se 3 (by rfl) ⟨113675, by rfl⟩ : syracuseStep 606269 = 227351) (by norm_num)
theorem B671809 : Blo 595291 671809 := bbase (se 2 (by rfl) ⟨251928, by rfl⟩ : syracuseStep 671809 = 503857) (by norm_num)
theorem B1130573 : Blo 595291 1130573 := bbase (se 3 (by rfl) ⟨211982, by rfl⟩ : syracuseStep 1130573 = 423965) (by norm_num)
theorem B606289 : Blo 595291 606289 := bbase (se 2 (by rfl) ⟨227358, by rfl⟩ : syracuseStep 606289 = 454717) (by norm_num)
theorem B2015333 : Blo 595291 2015333 := bbase (se 4 (by rfl) ⟨188937, by rfl⟩ : syracuseStep 2015333 = 377875) (by norm_num)
theorem B671845 : Blo 595291 671845 := bbase (se 4 (by rfl) ⟨62985, by rfl⟩ : syracuseStep 671845 = 125971) (by norm_num)
theorem B671881 : Blo 595291 671881 := bbase (se 2 (by rfl) ⟨251955, by rfl⟩ : syracuseStep 671881 = 503911) (by norm_num)
theorem B671917 : Blo 595291 671917 := bbase (se 3 (by rfl) ⟨125984, by rfl⟩ : syracuseStep 671917 = 251969) (by norm_num)
theorem B639181 : Blo 595291 639181 := bbase (se 3 (by rfl) ⟨119846, by rfl⟩ : syracuseStep 639181 = 239693) (by norm_num)
theorem B671953 : Blo 595291 671953 := bbase (se 2 (by rfl) ⟨251982, by rfl⟩ : syracuseStep 671953 = 503965) (by norm_num)
theorem B639185 : Blo 595291 639185 := bbase (se 2 (by rfl) ⟨239694, by rfl⟩ : syracuseStep 639185 = 479389) (by norm_num)
theorem B4079861 : Blo 595291 4079861 := bbase (se 5 (by rfl) ⟨191243, by rfl⟩ : syracuseStep 4079861 = 382487) (by norm_num)
theorem B671989 : Blo 595291 671989 := bbase (se 5 (by rfl) ⟨31499, by rfl⟩ : syracuseStep 671989 = 62999) (by norm_num)
theorem B672025 : Blo 595291 672025 := bbase (se 2 (by rfl) ⟨252009, by rfl⟩ : syracuseStep 672025 = 504019) (by norm_num)
theorem B672061 : Blo 595291 672061 := bbase (se 3 (by rfl) ⟨126011, by rfl⟩ : syracuseStep 672061 = 252023) (by norm_num)
theorem B672097 : Blo 595291 672097 := bbase (se 2 (by rfl) ⟨252036, by rfl⟩ : syracuseStep 672097 = 504073) (by norm_num)
theorem B1130861 : Blo 595291 1130861 := bbase (se 3 (by rfl) ⟨212036, by rfl⟩ : syracuseStep 1130861 = 424073) (by norm_num)
theorem B672133 : Blo 595291 672133 := bbase (se 4 (by rfl) ⟨63012, by rfl⟩ : syracuseStep 672133 = 126025) (by norm_num)
theorem B1458589 : Blo 595291 1458589 := bbase (se 3 (by rfl) ⟨273485, by rfl⟩ : syracuseStep 1458589 = 546971) (by norm_num)
theorem B672169 : Blo 595291 672169 := bbase (se 2 (by rfl) ⟨252063, by rfl⟩ : syracuseStep 672169 = 504127) (by norm_num)
theorem B672205 : Blo 595291 672205 := bbase (se 3 (by rfl) ⟨126038, by rfl⟩ : syracuseStep 672205 = 252077) (by norm_num)
theorem B672241 : Blo 595291 672241 := bbase (se 2 (by rfl) ⟨252090, by rfl⟩ : syracuseStep 672241 = 504181) (by norm_num)
theorem B1131013 : Blo 595291 1131013 := bbase (se 4 (by rfl) ⟨106032, by rfl⟩ : syracuseStep 1131013 = 212065) (by norm_num)
theorem B2015765 : Blo 595291 2015765 := bbase (se 6 (by rfl) ⟨47244, by rfl⟩ : syracuseStep 2015765 = 94489) (by norm_num)
theorem B672277 : Blo 595291 672277 := bbase (se 6 (by rfl) ⟨15756, by rfl⟩ : syracuseStep 672277 = 31513) (by norm_num)
theorem B672313 : Blo 595291 672313 := bbase (se 2 (by rfl) ⟨252117, by rfl⟩ : syracuseStep 672313 = 504235) (by norm_num)
theorem B3228245 : Blo 595291 3228245 := bbase (se 8 (by rfl) ⟨18915, by rfl⟩ : syracuseStep 3228245 = 37831) (by norm_num)
theorem B672349 : Blo 595291 672349 := bbase (se 3 (by rfl) ⟨126065, by rfl⟩ : syracuseStep 672349 = 252131) (by norm_num)
theorem B672385 : Blo 595291 672385 := bbase (se 2 (by rfl) ⟨252144, by rfl⟩ : syracuseStep 672385 = 504289) (by norm_num)
theorem B606853 : Blo 595291 606853 := bbase (se 4 (by rfl) ⟨56892, by rfl⟩ : syracuseStep 606853 = 113785) (by norm_num)
theorem B672421 : Blo 595291 672421 := bbase (se 4 (by rfl) ⟨63039, by rfl⟩ : syracuseStep 672421 = 126079) (by norm_num)
theorem B672457 : Blo 595291 672457 := bbase (se 2 (by rfl) ⟨252171, by rfl⟩ : syracuseStep 672457 = 504343) (by norm_num)
theorem B672493 : Blo 595291 672493 := bbase (se 3 (by rfl) ⟨126092, by rfl⟩ : syracuseStep 672493 = 252185) (by norm_num)
theorem B639749 : Blo 595291 639749 := bbase (se 4 (by rfl) ⟨59976, by rfl⟩ : syracuseStep 639749 = 119953) (by norm_num)
theorem B672529 : Blo 595291 672529 := bbase (se 2 (by rfl) ⟨252198, by rfl⟩ : syracuseStep 672529 = 504397) (by norm_num)
theorem B3228437 : Blo 595291 3228437 := bbase (se 6 (by rfl) ⟨75666, by rfl⟩ : syracuseStep 3228437 = 151333) (by norm_num)
theorem B3031829 : Blo 595291 3031829 := bbase (se 6 (by rfl) ⟨71058, by rfl⟩ : syracuseStep 3031829 = 142117) (by norm_num)
theorem B1131317 : Blo 595291 1131317 := bbase (se 5 (by rfl) ⟨53030, by rfl⟩ : syracuseStep 1131317 = 106061) (by norm_num)
theorem B672565 : Blo 595291 672565 := bbase (se 5 (by rfl) ⟨31526, by rfl⟩ : syracuseStep 672565 = 63053) (by norm_num)
theorem B1917749 : Blo 595291 1917749 := bbase (se 5 (by rfl) ⟨89894, by rfl⟩ : syracuseStep 1917749 = 179789) (by norm_num)
theorem B672601 : Blo 595291 672601 := bbase (se 2 (by rfl) ⟨252225, by rfl⟩ : syracuseStep 672601 = 504451) (by norm_num)
theorem B1459037 : Blo 595291 1459037 := bbase (se 3 (by rfl) ⟨273569, by rfl⟩ : syracuseStep 1459037 = 547139) (by norm_num)
theorem B672637 : Blo 595291 672637 := bbase (se 3 (by rfl) ⟨126119, by rfl⟩ : syracuseStep 672637 = 252239) (by norm_num)
theorem B1819525 : Blo 595291 1819525 := bbase (se 4 (by rfl) ⟨170580, by rfl⟩ : syracuseStep 1819525 = 341161) (by norm_num)
theorem B672673 : Blo 595291 672673 := bbase (se 2 (by rfl) ⟨252252, by rfl⟩ : syracuseStep 672673 = 504505) (by norm_num)
theorem B639937 : Blo 595291 639937 := bbase (se 2 (by rfl) ⟨239976, by rfl⟩ : syracuseStep 639937 = 479953) (by norm_num)
theorem B2016197 : Blo 595291 2016197 := bbase (se 4 (by rfl) ⟨189018, by rfl⟩ : syracuseStep 2016197 = 378037) (by norm_num)
theorem B672709 : Blo 595291 672709 := bbase (se 4 (by rfl) ⟨63066, by rfl⟩ : syracuseStep 672709 = 126133) (by norm_num)
theorem B607181 : Blo 595291 607181 := bbase (se 3 (by rfl) ⟨113846, by rfl⟩ : syracuseStep 607181 = 227693) (by norm_num)
theorem B672745 : Blo 595291 672745 := bbase (se 2 (by rfl) ⟨252279, by rfl⟩ : syracuseStep 672745 = 504559) (by norm_num)
theorem B607213 : Blo 595291 607213 := bbase (se 3 (by rfl) ⟨113852, by rfl⟩ : syracuseStep 607213 = 227705) (by norm_num)
theorem B672781 : Blo 595291 672781 := bbase (se 3 (by rfl) ⟨126146, by rfl⟩ : syracuseStep 672781 = 252293) (by norm_num)
theorem B672817 : Blo 595291 672817 := bbase (se 2 (by rfl) ⟨252306, by rfl⟩ : syracuseStep 672817 = 504613) (by norm_num)
theorem B672853 : Blo 595291 672853 := bbase (se 8 (by rfl) ⟨3942, by rfl⟩ : syracuseStep 672853 = 7885) (by norm_num)
theorem B672889 : Blo 595291 672889 := bbase (se 2 (by rfl) ⟨252333, by rfl⟩ : syracuseStep 672889 = 504667) (by norm_num)
theorem B672925 : Blo 595291 672925 := bbase (se 3 (by rfl) ⟨126173, by rfl⟩ : syracuseStep 672925 = 252347) (by norm_num)
theorem B2802869 : Blo 595291 2802869 := bbase (se 5 (by rfl) ⟨131384, by rfl⟩ : syracuseStep 2802869 = 262769) (by norm_num)
theorem B672961 : Blo 595291 672961 := bbase (se 2 (by rfl) ⟨252360, by rfl⟩ : syracuseStep 672961 = 504721) (by norm_num)
theorem B672997 : Blo 595291 672997 := bbase (se 4 (by rfl) ⟨63093, by rfl⟩ : syracuseStep 672997 = 126187) (by norm_num)
theorem B673033 : Blo 595291 673033 := bbase (se 2 (by rfl) ⟨252387, by rfl⟩ : syracuseStep 673033 = 504775) (by norm_num)
theorem B673069 : Blo 595291 673069 := bbase (se 3 (by rfl) ⟨126200, by rfl⟩ : syracuseStep 673069 = 252401) (by norm_num)
theorem B673105 : Blo 595291 673105 := bbase (se 2 (by rfl) ⟨252414, by rfl⟩ : syracuseStep 673105 = 504829) (by norm_num)
theorem B2016629 : Blo 595291 2016629 := bbase (se 5 (by rfl) ⟨94529, by rfl⟩ : syracuseStep 2016629 = 189059) (by norm_num)
theorem B673141 : Blo 595291 673141 := bbase (se 5 (by rfl) ⟨31553, by rfl⟩ : syracuseStep 673141 = 63107) (by norm_num)
theorem B673177 : Blo 595291 673177 := bbase (se 2 (by rfl) ⟨252441, by rfl⟩ : syracuseStep 673177 = 504883) (by norm_num)
theorem B673213 : Blo 595291 673213 := bbase (se 3 (by rfl) ⟨126227, by rfl⟩ : syracuseStep 673213 = 252455) (by norm_num)
theorem B673249 : Blo 595291 673249 := bbase (se 2 (by rfl) ⟨252468, by rfl⟩ : syracuseStep 673249 = 504937) (by norm_num)
theorem B673285 : Blo 595291 673285 := bbase (se 4 (by rfl) ⟨63120, by rfl⟩ : syracuseStep 673285 = 126241) (by norm_num)
theorem B1132069 : Blo 595291 1132069 := bbase (se 4 (by rfl) ⟨106131, by rfl⟩ : syracuseStep 1132069 = 212263) (by norm_num)
theorem B673321 : Blo 595291 673321 := bbase (se 2 (by rfl) ⟨252495, by rfl⟩ : syracuseStep 673321 = 504991) (by norm_num)
theorem B673357 : Blo 595291 673357 := bbase (se 3 (by rfl) ⟨126254, by rfl⟩ : syracuseStep 673357 = 252509) (by norm_num)
theorem B673393 : Blo 595291 673393 := bbase (se 2 (by rfl) ⟨252522, by rfl⟩ : syracuseStep 673393 = 505045) (by norm_num)
theorem B5097077 : Blo 595291 5097077 := bbase (se 5 (by rfl) ⟨238925, by rfl⟩ : syracuseStep 5097077 = 477851) (by norm_num)
theorem B673429 : Blo 595291 673429 := bbase (se 6 (by rfl) ⟨15783, by rfl⟩ : syracuseStep 673429 = 31567) (by norm_num)
theorem B1132213 : Blo 595291 1132213 := bbase (se 5 (by rfl) ⟨53072, by rfl⟩ : syracuseStep 1132213 = 106145) (by norm_num)
theorem B673465 : Blo 595291 673465 := bbase (se 2 (by rfl) ⟨252549, by rfl⟩ : syracuseStep 673465 = 505099) (by norm_num)
theorem B3819221 : Blo 595291 3819221 := bbase (se 7 (by rfl) ⟨44756, by rfl⟩ : syracuseStep 3819221 = 89513) (by norm_num)
theorem B673501 : Blo 595291 673501 := bbase (se 3 (by rfl) ⟨126281, by rfl⟩ : syracuseStep 673501 = 252563) (by norm_num)
theorem B673537 : Blo 595291 673537 := bbase (se 2 (by rfl) ⟨252576, by rfl⟩ : syracuseStep 673537 = 505153) (by norm_num)
theorem B2017061 : Blo 595291 2017061 := bbase (se 4 (by rfl) ⟨189099, by rfl⟩ : syracuseStep 2017061 = 378199) (by norm_num)
theorem B673573 : Blo 595291 673573 := bbase (se 4 (by rfl) ⟨63147, by rfl⟩ : syracuseStep 673573 = 126295) (by norm_num)
theorem B673609 : Blo 595291 673609 := bbase (se 2 (by rfl) ⟨252603, by rfl⟩ : syracuseStep 673609 = 505207) (by norm_num)
theorem B1132373 : Blo 595291 1132373 := bbase (se 9 (by rfl) ⟨3317, by rfl⟩ : syracuseStep 1132373 = 6635) (by norm_num)
theorem B673645 : Blo 595291 673645 := bbase (se 3 (by rfl) ⟨126308, by rfl⟩ : syracuseStep 673645 = 252617) (by norm_num)
theorem B673681 : Blo 595291 673681 := bbase (se 2 (by rfl) ⟨252630, by rfl⟩ : syracuseStep 673681 = 505261) (by norm_num)
theorem B673717 : Blo 595291 673717 := bbase (se 5 (by rfl) ⟨31580, by rfl⟩ : syracuseStep 673717 = 63161) (by norm_num)
theorem B673753 : Blo 595291 673753 := bbase (se 2 (by rfl) ⟨252657, by rfl⟩ : syracuseStep 673753 = 505315) (by norm_num)
theorem B1132517 : Blo 595291 1132517 := bbase (se 4 (by rfl) ⟨106173, by rfl⟩ : syracuseStep 1132517 = 212347) (by norm_num)
theorem B673789 : Blo 595291 673789 := bbase (se 3 (by rfl) ⟨126335, by rfl⟩ : syracuseStep 673789 = 252671) (by norm_num)
theorem B673825 : Blo 595291 673825 := bbase (se 2 (by rfl) ⟨252684, by rfl⟩ : syracuseStep 673825 = 505369) (by norm_num)
theorem B3033125 : Blo 595291 3033125 := bbase (se 4 (by rfl) ⟨284355, by rfl⟩ : syracuseStep 3033125 = 568711) (by norm_num)
theorem B673861 : Blo 595291 673861 := bbase (se 4 (by rfl) ⟨63174, by rfl⟩ : syracuseStep 673861 = 126349) (by norm_num)
theorem B673897 : Blo 595291 673897 := bbase (se 2 (by rfl) ⟨252711, by rfl⟩ : syracuseStep 673897 = 505423) (by norm_num)
theorem B1722485 : Blo 595291 1722485 := bbase (se 5 (by rfl) ⟨80741, by rfl⟩ : syracuseStep 1722485 = 161483) (by norm_num)
theorem B673933 : Blo 595291 673933 := bbase (se 3 (by rfl) ⟨126362, by rfl⟩ : syracuseStep 673933 = 252725) (by norm_num)
theorem B673969 : Blo 595291 673969 := bbase (se 2 (by rfl) ⟨252738, by rfl⟩ : syracuseStep 673969 = 505477) (by norm_num)
theorem B2017493 : Blo 595291 2017493 := bbase (se 7 (by rfl) ⟨23642, by rfl⟩ : syracuseStep 2017493 = 47285) (by norm_num)
theorem B674005 : Blo 595291 674005 := bbase (se 7 (by rfl) ⟨7898, by rfl⟩ : syracuseStep 674005 = 15797) (by norm_num)
theorem B674041 : Blo 595291 674041 := bbase (se 2 (by rfl) ⟨252765, by rfl⟩ : syracuseStep 674041 = 505531) (by norm_num)
theorem B1132805 : Blo 595291 1132805 := bbase (se 4 (by rfl) ⟨106200, by rfl⟩ : syracuseStep 1132805 = 212401) (by norm_num)
theorem B674077 : Blo 595291 674077 := bbase (se 3 (by rfl) ⟨126389, by rfl⟩ : syracuseStep 674077 = 252779) (by norm_num)
theorem B674113 : Blo 595291 674113 := bbase (se 2 (by rfl) ⟨252792, by rfl⟩ : syracuseStep 674113 = 505585) (by norm_num)
theorem B674149 : Blo 595291 674149 := bbase (se 4 (by rfl) ⟨63201, by rfl⟩ : syracuseStep 674149 = 126403) (by norm_num)
theorem B674185 : Blo 595291 674185 := bbase (se 2 (by rfl) ⟨252819, by rfl⟩ : syracuseStep 674185 = 505639) (by norm_num)
theorem B1132957 : Blo 595291 1132957 := bbase (se 3 (by rfl) ⟨212429, by rfl⟩ : syracuseStep 1132957 = 424859) (by norm_num)
theorem B2148773 : Blo 595291 2148773 := bbase (se 4 (by rfl) ⟨201447, by rfl⟩ : syracuseStep 2148773 = 402895) (by norm_num)
theorem B3230165 : Blo 595291 3230165 := bbase (se 7 (by rfl) ⟨37853, by rfl⟩ : syracuseStep 3230165 = 75707) (by norm_num)
theorem B3394133 : Blo 595291 3394133 := bbase (se 8 (by rfl) ⟨19887, by rfl⟩ : syracuseStep 3394133 = 39775) (by norm_num)
theorem B2017925 : Blo 595291 2017925 := bbase (se 4 (by rfl) ⟨189180, by rfl⟩ : syracuseStep 2017925 = 378361) (by norm_num)
theorem B1133261 : Blo 595291 1133261 := bbase (se 3 (by rfl) ⟨212486, by rfl⟩ : syracuseStep 1133261 = 424973) (by norm_num)
theorem B5327669 : Blo 595291 5327669 := bbase (se 5 (by rfl) ⟨249734, by rfl⟩ : syracuseStep 5327669 = 499469) (by norm_num)
theorem B1035101 : Blo 595291 1035101 := bbase (se 3 (by rfl) ⟨194081, by rfl⟩ : syracuseStep 1035101 = 388163) (by norm_num)
theorem B2870261 : Blo 595291 2870261 := bbase (se 5 (by rfl) ⟨134543, by rfl⟩ : syracuseStep 2870261 = 269087) (by norm_num)
theorem B2018357 : Blo 595291 2018357 := bbase (se 5 (by rfl) ⟨94610, by rfl⟩ : syracuseStep 2018357 = 189221) (by norm_num)
theorem B1723685 : Blo 595291 1723685 := bbase (se 4 (by rfl) ⟨161595, by rfl⟩ : syracuseStep 1723685 = 323191) (by norm_num)
theorem B1134013 : Blo 595291 1134013 := bbase (se 3 (by rfl) ⟨212627, by rfl⟩ : syracuseStep 1134013 = 425255) (by norm_num)
theorem B2018789 : Blo 595291 2018789 := bbase (se 4 (by rfl) ⟨189261, by rfl⟩ : syracuseStep 2018789 = 378523) (by norm_num)
theorem B1134157 : Blo 595291 1134157 := bbase (se 3 (by rfl) ⟨212654, by rfl⟩ : syracuseStep 1134157 = 425309) (by norm_num)
theorem B1134317 : Blo 595291 1134317 := bbase (se 3 (by rfl) ⟨212684, by rfl⟩ : syracuseStep 1134317 = 425369) (by norm_num)
theorem B3395317 : Blo 595291 3395317 := bbase (se 5 (by rfl) ⟨159155, by rfl⟩ : syracuseStep 3395317 = 318311) (by norm_num)
theorem B2543413 : Blo 595291 2543413 := bbase (se 5 (by rfl) ⟨119222, by rfl⟩ : syracuseStep 2543413 = 238445) (by norm_num)
theorem B872245 : Blo 595291 872245 := bbase (se 5 (by rfl) ⟨40886, by rfl⟩ : syracuseStep 872245 = 81773) (by norm_num)
theorem B4312885 : Blo 595291 4312885 := bbase (se 5 (by rfl) ⟨202166, by rfl⟩ : syracuseStep 4312885 = 404333) (by norm_num)
theorem B5820245 : Blo 595291 5820245 := bbase (se 9 (by rfl) ⟨17051, by rfl⟩ : syracuseStep 5820245 = 34103) (by norm_num)
theorem B1134461 : Blo 595291 1134461 := bbase (se 3 (by rfl) ⟨212711, by rfl⟩ : syracuseStep 1134461 = 425423) (by norm_num)
theorem B2019221 : Blo 595291 2019221 := bbase (se 6 (by rfl) ⟨47325, by rfl⟩ : syracuseStep 2019221 = 94651) (by norm_num)
theorem B2871413 : Blo 595291 2871413 := bbase (se 5 (by rfl) ⟨134597, by rfl⟩ : syracuseStep 2871413 = 269195) (by norm_num)
theorem B1134749 : Blo 595291 1134749 := bbase (se 3 (by rfl) ⟨212765, by rfl⟩ : syracuseStep 1134749 = 425531) (by norm_num)
theorem B1134901 : Blo 595291 1134901 := bbase (se 5 (by rfl) ⟨53198, by rfl⟩ : syracuseStep 1134901 = 106397) (by norm_num)
theorem B2019653 : Blo 595291 2019653 := bbase (se 4 (by rfl) ⟨189342, by rfl⟩ : syracuseStep 2019653 = 378685) (by norm_num)
theorem B1528141 : Blo 595291 1528141 := bbase (se 3 (by rfl) ⟨286526, by rfl⟩ : syracuseStep 1528141 = 573053) (by norm_num)
theorem B2544149 : Blo 595291 2544149 := bbase (se 6 (by rfl) ⟨59628, by rfl⟩ : syracuseStep 2544149 = 119257) (by norm_num)
theorem B3494453 : Blo 595291 3494453 := bbase (se 5 (by rfl) ⟨163802, by rfl⟩ : syracuseStep 3494453 = 327605) (by norm_num)
theorem B1135205 : Blo 595291 1135205 := bbase (se 4 (by rfl) ⟨106425, by rfl⟩ : syracuseStep 1135205 = 212851) (by norm_num)
theorem B873181 : Blo 595291 873181 := bbase (se 3 (by rfl) ⟨163721, by rfl⟩ : syracuseStep 873181 = 327443) (by norm_num)
theorem B2020085 : Blo 595291 2020085 := bbase (se 5 (by rfl) ⟨94691, by rfl⟩ : syracuseStep 2020085 = 189383) (by norm_num)
theorem B2872181 : Blo 595291 2872181 := bbase (se 5 (by rfl) ⟨134633, by rfl⟩ : syracuseStep 2872181 = 269267) (by norm_num)
theorem B906149 : Blo 595291 906149 := bbase (se 4 (by rfl) ⟨84951, by rfl⟩ : syracuseStep 906149 = 169903) (by norm_num)
theorem B808013 : Blo 595291 808013 := bbase (se 3 (by rfl) ⟨151502, by rfl⟩ : syracuseStep 808013 = 303005) (by norm_num)
theorem B1004629 : Blo 595291 1004629 := bbase (se 8 (by rfl) ⟨5886, by rfl⟩ : syracuseStep 1004629 = 11773) (by norm_num)
theorem B2020517 : Blo 595291 2020517 := bbase (se 4 (by rfl) ⟨189423, by rfl⟩ : syracuseStep 2020517 = 378847) (by norm_num)
theorem B1004717 : Blo 595291 1004717 := bbase (se 3 (by rfl) ⟨188384, by rfl⟩ : syracuseStep 1004717 = 376769) (by norm_num)
theorem B2151701 : Blo 595291 2151701 := bbase (se 6 (by rfl) ⟨50430, by rfl⟩ : syracuseStep 2151701 = 100861) (by norm_num)
theorem B808213 : Blo 595291 808213 := bbase (se 6 (by rfl) ⟨18942, by rfl⟩ : syracuseStep 808213 = 37885) (by norm_num)
theorem B1004845 : Blo 595291 1004845 := bbase (se 3 (by rfl) ⟨188408, by rfl⟩ : syracuseStep 1004845 = 376817) (by norm_num)
theorem B808277 : Blo 595291 808277 := bbase (se 16 (by rfl) ⟨18, by rfl⟩ : syracuseStep 808277 = 37) (by norm_num)
theorem B1135957 : Blo 595291 1135957 := bbase (se 18 (by rfl) ⟨6, by rfl⟩ : syracuseStep 1135957 = 13) (by norm_num)
theorem B1004933 : Blo 595291 1004933 := bbase (se 4 (by rfl) ⟨94212, by rfl⟩ : syracuseStep 1004933 = 188425) (by norm_num)
theorem B1136101 : Blo 595291 1136101 := bbase (se 4 (by rfl) ⟨106509, by rfl⟩ : syracuseStep 1136101 = 213019) (by norm_num)
theorem B1005061 : Blo 595291 1005061 := bbase (se 4 (by rfl) ⟨94224, by rfl⟩ : syracuseStep 1005061 = 188449) (by norm_num)
theorem B2020949 : Blo 595291 2020949 := bbase (se 8 (by rfl) ⟨11841, by rfl⟩ : syracuseStep 2020949 = 23683) (by norm_num)
theorem B1005149 : Blo 595291 1005149 := bbase (se 3 (by rfl) ⟨188465, by rfl⟩ : syracuseStep 1005149 = 376931) (by norm_num)
theorem B1136261 : Blo 595291 1136261 := bbase (se 4 (by rfl) ⟨106524, by rfl⟩ : syracuseStep 1136261 = 213049) (by norm_num)
theorem B3397301 : Blo 595291 3397301 := bbase (se 5 (by rfl) ⟨159248, by rfl⟩ : syracuseStep 3397301 = 318497) (by norm_num)
theorem B1005277 : Blo 595291 1005277 := bbase (se 3 (by rfl) ⟨188489, by rfl⟩ : syracuseStep 1005277 = 376979) (by norm_num)
theorem B1136405 : Blo 595291 1136405 := bbase (se 6 (by rfl) ⟨26634, by rfl⟩ : syracuseStep 1136405 = 53269) (by norm_num)
theorem B1005365 : Blo 595291 1005365 := bbase (se 5 (by rfl) ⟨47126, by rfl⟩ : syracuseStep 1005365 = 94253) (by norm_num)
theorem B1005493 : Blo 595291 1005493 := bbase (se 5 (by rfl) ⟨47132, by rfl⟩ : syracuseStep 1005493 = 94265) (by norm_num)
theorem B2021381 : Blo 595291 2021381 := bbase (se 4 (by rfl) ⟨189504, by rfl⟩ : syracuseStep 2021381 = 379009) (by norm_num)
theorem B1005581 : Blo 595291 1005581 := bbase (se 3 (by rfl) ⟨188546, by rfl⟩ : syracuseStep 1005581 = 377093) (by norm_num)
theorem B1136693 : Blo 595291 1136693 := bbase (se 5 (by rfl) ⟨53282, by rfl⟩ : syracuseStep 1136693 = 106565) (by norm_num)
theorem B1005709 : Blo 595291 1005709 := bbase (se 3 (by rfl) ⟨188570, by rfl⟩ : syracuseStep 1005709 = 377141) (by norm_num)
theorem B1136845 : Blo 595291 1136845 := bbase (se 3 (by rfl) ⟨213158, by rfl⟩ : syracuseStep 1136845 = 426317) (by norm_num)
theorem B1005797 : Blo 595291 1005797 := bbase (se 4 (by rfl) ⟨94293, by rfl⟩ : syracuseStep 1005797 = 188587) (by norm_num)
theorem B1136941 : Blo 595291 1136941 := bbase (se 3 (by rfl) ⟨213176, by rfl⟩ : syracuseStep 1136941 = 426353) (by norm_num)
theorem B18340181 : Blo 595291 18340181 := bbase (se 10 (by rfl) ⟨26865, by rfl⟩ : syracuseStep 18340181 = 53731) (by norm_num)
theorem B1005925 : Blo 595291 1005925 := bbase (se 4 (by rfl) ⟨94305, by rfl⟩ : syracuseStep 1005925 = 188611) (by norm_num)
theorem B1366397 : Blo 595291 1366397 := bbase (se 3 (by rfl) ⟨256199, by rfl⟩ : syracuseStep 1366397 = 512399) (by norm_num)
theorem B2021813 : Blo 595291 2021813 := bbase (se 5 (by rfl) ⟨94772, by rfl⟩ : syracuseStep 2021813 = 189545) (by norm_num)
theorem B1006013 : Blo 595291 1006013 := bbase (se 3 (by rfl) ⟨188627, by rfl⟩ : syracuseStep 1006013 = 377255) (by norm_num)
theorem B1137149 : Blo 595291 1137149 := bbase (se 3 (by rfl) ⟨213215, by rfl⟩ : syracuseStep 1137149 = 426431) (by norm_num)
theorem B1432093 : Blo 595291 1432093 := bbase (se 3 (by rfl) ⟨268517, by rfl⟩ : syracuseStep 1432093 = 537035) (by norm_num)
theorem B1006141 : Blo 595291 1006141 := bbase (se 3 (by rfl) ⟨188651, by rfl⟩ : syracuseStep 1006141 = 377303) (by norm_num)
theorem B907877 : Blo 595291 907877 := bbase (se 4 (by rfl) ⟨85113, by rfl⟩ : syracuseStep 907877 = 170227) (by norm_num)
theorem B1432189 : Blo 595291 1432189 := bbase (se 3 (by rfl) ⟨268535, by rfl⟩ : syracuseStep 1432189 = 537071) (by norm_num)
theorem B1006229 : Blo 595291 1006229 := bbase (se 6 (by rfl) ⟨23583, by rfl⟩ : syracuseStep 1006229 = 47167) (by norm_num)
theorem B1006357 : Blo 595291 1006357 := bbase (se 6 (by rfl) ⟨23586, by rfl⟩ : syracuseStep 1006357 = 47173) (by norm_num)
theorem B2022245 : Blo 595291 2022245 := bbase (se 4 (by rfl) ⟨189585, by rfl⟩ : syracuseStep 2022245 = 379171) (by norm_num)
theorem B1006445 : Blo 595291 1006445 := bbase (se 3 (by rfl) ⟨188708, by rfl⟩ : syracuseStep 1006445 = 377417) (by norm_num)
theorem B1006573 : Blo 595291 1006573 := bbase (se 3 (by rfl) ⟨188732, by rfl⟩ : syracuseStep 1006573 = 377465) (by norm_num)
theorem B4545557 : Blo 595291 4545557 := bbase (se 6 (by rfl) ⟨106536, by rfl⟩ : syracuseStep 4545557 = 213073) (by norm_num)
theorem B1006661 : Blo 595291 1006661 := bbase (se 4 (by rfl) ⟨94374, by rfl⟩ : syracuseStep 1006661 = 188749) (by norm_num)
theorem B777325 : Blo 595291 777325 := bbase (se 3 (by rfl) ⟨145748, by rfl⟩ : syracuseStep 777325 = 291497) (by norm_num)
theorem B679061 : Blo 595291 679061 := bbase (se 6 (by rfl) ⟨15915, by rfl⟩ : syracuseStep 679061 = 31831) (by norm_num)
theorem B908437 : Blo 595291 908437 := bbase (se 6 (by rfl) ⟨21291, by rfl⟩ : syracuseStep 908437 = 42583) (by norm_num)
theorem B2415781 : Blo 595291 2415781 := bbase (se 4 (by rfl) ⟨226479, by rfl⟩ : syracuseStep 2415781 = 452959) (by norm_num)
theorem B1006789 : Blo 595291 1006789 := bbase (se 4 (by rfl) ⟨94386, by rfl⟩ : syracuseStep 1006789 = 188773) (by norm_num)
theorem B15260885 : Blo 595291 15260885 := bbase (se 7 (by rfl) ⟨178838, by rfl⟩ : syracuseStep 15260885 = 357677) (by norm_num)
theorem B1006877 : Blo 595291 1006877 := bbase (se 3 (by rfl) ⟨188789, by rfl⟩ : syracuseStep 1006877 = 377579) (by norm_num)
theorem B1727797 : Blo 595291 1727797 := bbase (se 5 (by rfl) ⟨80990, by rfl⟩ : syracuseStep 1727797 = 161981) (by norm_num)
theorem B1007005 : Blo 595291 1007005 := bbase (se 3 (by rfl) ⟨188813, by rfl⟩ : syracuseStep 1007005 = 377627) (by norm_num)
theorem B1007093 : Blo 595291 1007093 := bbase (se 5 (by rfl) ⟨47207, by rfl⟩ : syracuseStep 1007093 = 94415) (by norm_num)
theorem B1007221 : Blo 595291 1007221 := bbase (se 5 (by rfl) ⟨47213, by rfl⟩ : syracuseStep 1007221 = 94427) (by norm_num)
theorem B3825269 : Blo 595291 3825269 := bbase (se 5 (by rfl) ⟨179309, by rfl⟩ : syracuseStep 3825269 = 358619) (by norm_num)
theorem B1433285 : Blo 595291 1433285 := bbase (se 4 (by rfl) ⟨134370, by rfl⟩ : syracuseStep 1433285 = 268741) (by norm_num)
theorem B1007309 : Blo 595291 1007309 := bbase (se 3 (by rfl) ⟨188870, by rfl⟩ : syracuseStep 1007309 = 377741) (by norm_num)
theorem B2547445 : Blo 595291 2547445 := bbase (se 5 (by rfl) ⟨119411, by rfl⟩ : syracuseStep 2547445 = 238823) (by norm_num)
theorem B1007437 : Blo 595291 1007437 := bbase (se 3 (by rfl) ⟨188894, by rfl⟩ : syracuseStep 1007437 = 377789) (by norm_num)
theorem B3399509 : Blo 595291 3399509 := bbase (se 9 (by rfl) ⟨9959, by rfl⟩ : syracuseStep 3399509 = 19919) (by norm_num)
theorem B1007525 : Blo 595291 1007525 := bbase (se 4 (by rfl) ⟨94455, by rfl⟩ : syracuseStep 1007525 = 188911) (by norm_num)
theorem B2187269 : Blo 595291 2187269 := bbase (se 4 (by rfl) ⟨205056, by rfl⟩ : syracuseStep 2187269 = 410113) (by norm_num)
theorem B1007653 : Blo 595291 1007653 := bbase (se 4 (by rfl) ⟨94467, by rfl⟩ : syracuseStep 1007653 = 188935) (by norm_num)
theorem B1007741 : Blo 595291 1007741 := bbase (se 3 (by rfl) ⟨188951, by rfl⟩ : syracuseStep 1007741 = 377903) (by norm_num)
theorem B647317 : Blo 595291 647317 := bbase (se 6 (by rfl) ⟨15171, by rfl⟩ : syracuseStep 647317 = 30343) (by norm_num)
theorem B1401013 : Blo 595291 1401013 := bbase (se 5 (by rfl) ⟨65672, by rfl⟩ : syracuseStep 1401013 = 131345) (by norm_num)
theorem B2187445 : Blo 595291 2187445 := bbase (se 5 (by rfl) ⟨102536, by rfl⟩ : syracuseStep 2187445 = 205073) (by norm_num)
theorem B1695973 : Blo 595291 1695973 := bbase (se 4 (by rfl) ⟨158997, by rfl⟩ : syracuseStep 1695973 = 317995) (by norm_num)
theorem B1007869 : Blo 595291 1007869 := bbase (se 3 (by rfl) ⟨188975, by rfl⟩ : syracuseStep 1007869 = 377951) (by norm_num)
theorem B909605 : Blo 595291 909605 := bbase (se 4 (by rfl) ⟨85275, by rfl⟩ : syracuseStep 909605 = 170551) (by norm_num)
theorem B5431637 : Blo 595291 5431637 := bbase (se 10 (by rfl) ⟨7956, by rfl⟩ : syracuseStep 5431637 = 15913) (by norm_num)
theorem B1007957 : Blo 595291 1007957 := bbase (se 10 (by rfl) ⟨1476, by rfl⟩ : syracuseStep 1007957 = 2953) (by norm_num)
theorem B6906197 : Blo 595291 6906197 := bbase (se 10 (by rfl) ⟨10116, by rfl⟩ : syracuseStep 6906197 = 20233) (by norm_num)
theorem B1696133 : Blo 595291 1696133 := bbase (se 4 (by rfl) ⟨159012, by rfl⟩ : syracuseStep 1696133 = 318025) (by norm_num)
theorem B2417045 : Blo 595291 2417045 := bbase (se 6 (by rfl) ⟨56649, by rfl⟩ : syracuseStep 2417045 = 113299) (by norm_num)
theorem B1008085 : Blo 595291 1008085 := bbase (se 7 (by rfl) ⟨11813, by rfl⟩ : syracuseStep 1008085 = 23627) (by norm_num)
theorem B1008173 : Blo 595291 1008173 := bbase (se 3 (by rfl) ⟨189032, by rfl⟩ : syracuseStep 1008173 = 378065) (by norm_num)
theorem B1696373 : Blo 595291 1696373 := bbase (se 5 (by rfl) ⟨79517, by rfl⟩ : syracuseStep 1696373 = 159035) (by norm_num)
theorem B1434245 : Blo 595291 1434245 := bbase (se 4 (by rfl) ⟨134460, by rfl⟩ : syracuseStep 1434245 = 268921) (by norm_num)
theorem B1008301 : Blo 595291 1008301 := bbase (se 3 (by rfl) ⟨189056, by rfl⟩ : syracuseStep 1008301 = 378113) (by norm_num)
theorem B746237 : Blo 595291 746237 := bbase (se 3 (by rfl) ⟨139919, by rfl⟩ : syracuseStep 746237 = 279839) (by norm_num)
theorem B1008389 : Blo 595291 1008389 := bbase (se 4 (by rfl) ⟨94536, by rfl⟩ : syracuseStep 1008389 = 189073) (by norm_num)
theorem B1696565 : Blo 595291 1696565 := bbase (se 5 (by rfl) ⟨79526, by rfl⟩ : syracuseStep 1696565 = 159053) (by norm_num)
theorem B1008517 : Blo 595291 1008517 := bbase (se 4 (by rfl) ⟨94548, by rfl⟩ : syracuseStep 1008517 = 189097) (by norm_num)
theorem B1008605 : Blo 595291 1008605 := bbase (se 3 (by rfl) ⟨189113, by rfl⟩ : syracuseStep 1008605 = 378227) (by norm_num)
theorem B2909189 : Blo 595291 2909189 := bbase (se 4 (by rfl) ⟨272736, by rfl⟩ : syracuseStep 2909189 = 545473) (by norm_num)
theorem B615433 : Blo 595291 615433 := bbase (se 2 (by rfl) ⟨230787, by rfl⟩ : syracuseStep 615433 = 461575) (by norm_num)
theorem B1008733 : Blo 595291 1008733 := bbase (se 3 (by rfl) ⟨189137, by rfl⟩ : syracuseStep 1008733 = 378275) (by norm_num)
theorem B1008821 : Blo 595291 1008821 := bbase (se 5 (by rfl) ⟨47288, by rfl⟩ : syracuseStep 1008821 = 94577) (by norm_num)
theorem B2417957 : Blo 595291 2417957 := bbase (se 4 (by rfl) ⟨226683, by rfl⟩ : syracuseStep 2417957 = 453367) (by norm_num)
theorem B1729829 : Blo 595291 1729829 := bbase (se 4 (by rfl) ⟨162171, by rfl⟩ : syracuseStep 1729829 = 324343) (by norm_num)
theorem B1008949 : Blo 595291 1008949 := bbase (se 5 (by rfl) ⟨47294, by rfl⟩ : syracuseStep 1008949 = 94589) (by norm_num)
theorem B1009037 : Blo 595291 1009037 := bbase (se 3 (by rfl) ⟨189194, by rfl⟩ : syracuseStep 1009037 = 378389) (by norm_num)
theorem B1009165 : Blo 595291 1009165 := bbase (se 3 (by rfl) ⟨189218, by rfl⟩ : syracuseStep 1009165 = 378437) (by norm_num)
theorem B1009253 : Blo 595291 1009253 := bbase (se 4 (by rfl) ⟨94617, by rfl⟩ : syracuseStep 1009253 = 189235) (by norm_num)
theorem B681601 : Blo 595291 681601 := bbase (se 2 (by rfl) ⟨255600, by rfl⟩ : syracuseStep 681601 = 511201) (by norm_num)
theorem B1009381 : Blo 595291 1009381 := bbase (se 4 (by rfl) ⟨94629, by rfl⟩ : syracuseStep 1009381 = 189259) (by norm_num)
theorem B1697557 : Blo 595291 1697557 := bbase (se 6 (by rfl) ⟨39786, by rfl⟩ : syracuseStep 1697557 = 79573) (by norm_num)
theorem B1009469 : Blo 595291 1009469 := bbase (se 3 (by rfl) ⟨189275, by rfl⟩ : syracuseStep 1009469 = 378551) (by norm_num)
theorem B1009597 : Blo 595291 1009597 := bbase (se 3 (by rfl) ⟨189299, by rfl⟩ : syracuseStep 1009597 = 378599) (by norm_num)
theorem B1009685 : Blo 595291 1009685 := bbase (se 6 (by rfl) ⟨23664, by rfl⟩ : syracuseStep 1009685 = 47329) (by norm_num)
theorem B1009813 : Blo 595291 1009813 := bbase (se 6 (by rfl) ⟨23667, by rfl⟩ : syracuseStep 1009813 = 47335) (by norm_num)
theorem B1009901 : Blo 595291 1009901 := bbase (se 3 (by rfl) ⟨189356, by rfl⟩ : syracuseStep 1009901 = 378713) (by norm_num)
theorem B2156789 : Blo 595291 2156789 := bbase (se 5 (by rfl) ⟨101099, by rfl⟩ : syracuseStep 2156789 = 202199) (by norm_num)
theorem B1436005 : Blo 595291 1436005 := bbase (se 4 (by rfl) ⟨134625, by rfl⟩ : syracuseStep 1436005 = 269251) (by norm_num)
theorem B1010029 : Blo 595291 1010029 := bbase (se 3 (by rfl) ⟨189380, by rfl⟩ : syracuseStep 1010029 = 378761) (by norm_num)
theorem B1010117 : Blo 595291 1010117 := bbase (se 4 (by rfl) ⟨94698, by rfl⟩ : syracuseStep 1010117 = 189397) (by norm_num)
theorem B2157077 : Blo 595291 2157077 := bbase (se 6 (by rfl) ⟨50556, by rfl⟩ : syracuseStep 2157077 = 101113) (by norm_num)
theorem B2419253 : Blo 595291 2419253 := bbase (se 5 (by rfl) ⟨113402, by rfl⟩ : syracuseStep 2419253 = 226805) (by norm_num)
theorem B1010245 : Blo 595291 1010245 := bbase (se 4 (by rfl) ⟨94710, by rfl⟩ : syracuseStep 1010245 = 189421) (by norm_num)
theorem B1436237 : Blo 595291 1436237 := bbase (se 3 (by rfl) ⟨269294, by rfl⟩ : syracuseStep 1436237 = 538589) (by norm_num)
theorem B715393 : Blo 595291 715393 := bbase (se 2 (by rfl) ⟨268272, by rfl⟩ : syracuseStep 715393 = 536545) (by norm_num)
theorem B1010333 : Blo 595291 1010333 := bbase (se 3 (by rfl) ⟨189437, by rfl⟩ : syracuseStep 1010333 = 378875) (by norm_num)
theorem B1272485 : Blo 595291 1272485 := bbase (se 4 (by rfl) ⟨119295, by rfl⟩ : syracuseStep 1272485 = 238591) (by norm_num)
theorem B2550437 : Blo 595291 2550437 := bbase (se 4 (by rfl) ⟨239103, by rfl⟩ : syracuseStep 2550437 = 478207) (by norm_num)
theorem B1010461 : Blo 595291 1010461 := bbase (se 3 (by rfl) ⟨189461, by rfl⟩ : syracuseStep 1010461 = 378923) (by norm_num)
theorem B1272629 : Blo 595291 1272629 := bbase (se 5 (by rfl) ⟨59654, by rfl⟩ : syracuseStep 1272629 = 119309) (by norm_num)
theorem B715585 : Blo 595291 715585 := bbase (se 2 (by rfl) ⟨268344, by rfl⟩ : syracuseStep 715585 = 536689) (by norm_num)
theorem B1698661 : Blo 595291 1698661 := bbase (se 4 (by rfl) ⟨159249, by rfl⟩ : syracuseStep 1698661 = 318499) (by norm_num)
theorem B1010549 : Blo 595291 1010549 := bbase (se 5 (by rfl) ⟨47369, by rfl⟩ : syracuseStep 1010549 = 94739) (by norm_num)
theorem B682897 : Blo 595291 682897 := bbase (se 2 (by rfl) ⟨256086, by rfl⟩ : syracuseStep 682897 = 512173) (by norm_num)
theorem B1436629 : Blo 595291 1436629 := bbase (se 7 (by rfl) ⟨16835, by rfl⟩ : syracuseStep 1436629 = 33671) (by norm_num)
theorem B1010677 : Blo 595291 1010677 := bbase (se 5 (by rfl) ⟨47375, by rfl⟩ : syracuseStep 1010677 = 94751) (by norm_num)
theorem B1010765 : Blo 595291 1010765 := bbase (se 3 (by rfl) ⟨189518, by rfl⟩ : syracuseStep 1010765 = 379037) (by norm_num)
theorem B1272989 : Blo 595291 1272989 := bbase (se 3 (by rfl) ⟨238685, by rfl⟩ : syracuseStep 1272989 = 477371) (by norm_num)
theorem B1010893 : Blo 595291 1010893 := bbase (se 3 (by rfl) ⟨189542, by rfl⟩ : syracuseStep 1010893 = 379085) (by norm_num)
theorem B3075317 : Blo 595291 3075317 := bbase (se 5 (by rfl) ⟨144155, by rfl⟩ : syracuseStep 3075317 = 288311) (by norm_num)
theorem B1010981 : Blo 595291 1010981 := bbase (se 4 (by rfl) ⟨94779, by rfl⟩ : syracuseStep 1010981 = 189559) (by norm_num)
theorem B1076549 : Blo 595291 1076549 := bbase (se 4 (by rfl) ⟨100926, by rfl⟩ : syracuseStep 1076549 = 201853) (by norm_num)
theorem B1011109 : Blo 595291 1011109 := bbase (se 4 (by rfl) ⟨94791, by rfl⟩ : syracuseStep 1011109 = 189583) (by norm_num)
theorem B1011197 : Blo 595291 1011197 := bbase (se 3 (by rfl) ⟨189599, by rfl⟩ : syracuseStep 1011197 = 379199) (by norm_num)
theorem B2551445 : Blo 595291 2551445 := bbase (se 6 (by rfl) ⟨59799, by rfl⟩ : syracuseStep 2551445 = 119599) (by norm_num)
theorem B716465 : Blo 595291 716465 := bbase (se 2 (by rfl) ⟨268674, by rfl⟩ : syracuseStep 716465 = 537349) (by norm_num)
theorem B847685 : Blo 595291 847685 := bbase (se 4 (by rfl) ⟨79470, by rfl⟩ : syracuseStep 847685 = 158941) (by norm_num)
theorem B1273877 : Blo 595291 1273877 := bbase (se 6 (by rfl) ⟨29856, by rfl⟩ : syracuseStep 1273877 = 59713) (by norm_num)
theorem B1437725 : Blo 595291 1437725 := bbase (se 3 (by rfl) ⟨269573, by rfl⟩ : syracuseStep 1437725 = 539147) (by norm_num)
theorem B1339469 : Blo 595291 1339469 := bbase (se 3 (by rfl) ⟨251150, by rfl⟩ : syracuseStep 1339469 = 502301) (by norm_num)
theorem B2355317 : Blo 595291 2355317 := bbase (se 5 (by rfl) ⟨110405, by rfl⟩ : syracuseStep 2355317 = 220811) (by norm_num)
theorem B1339541 : Blo 595291 1339541 := bbase (se 6 (by rfl) ⟨31395, by rfl⟩ : syracuseStep 1339541 = 62791) (by norm_num)
theorem B716969 : Blo 595291 716969 := bbase (se 2 (by rfl) ⟨268863, by rfl⟩ : syracuseStep 716969 = 537727) (by norm_num)
theorem B717017 : Blo 595291 717017 := bbase (se 2 (by rfl) ⟨268881, by rfl⟩ : syracuseStep 717017 = 537763) (by norm_num)
theorem B1339613 : Blo 595291 1339613 := bbase (se 3 (by rfl) ⟨251177, by rfl⟩ : syracuseStep 1339613 = 502355) (by norm_num)
theorem B1274125 : Blo 595291 1274125 := bbase (se 3 (by rfl) ⟨238898, by rfl⟩ : syracuseStep 1274125 = 477797) (by norm_num)
theorem B1339685 : Blo 595291 1339685 := bbase (se 4 (by rfl) ⟨125595, by rfl⟩ : syracuseStep 1339685 = 251191) (by norm_num)
theorem B1438013 : Blo 595291 1438013 := bbase (se 3 (by rfl) ⟨269627, by rfl⟩ : syracuseStep 1438013 = 539255) (by norm_num)
theorem B1700165 : Blo 595291 1700165 := bbase (se 4 (by rfl) ⟨159390, by rfl⟩ : syracuseStep 1700165 = 318781) (by norm_num)
theorem B1339757 : Blo 595291 1339757 := bbase (se 3 (by rfl) ⟨251204, by rfl⟩ : syracuseStep 1339757 = 502409) (by norm_num)
theorem B848237 : Blo 595291 848237 := bbase (se 3 (by rfl) ⟨159044, by rfl⟩ : syracuseStep 848237 = 318089) (by norm_num)
theorem B1339829 : Blo 595291 1339829 := bbase (se 5 (by rfl) ⟨62804, by rfl⟩ : syracuseStep 1339829 = 125609) (by norm_num)
theorem B717277 : Blo 595291 717277 := bbase (se 3 (by rfl) ⟨134489, by rfl⟩ : syracuseStep 717277 = 268979) (by norm_num)
theorem B1339901 : Blo 595291 1339901 := bbase (se 3 (by rfl) ⟨251231, by rfl⟩ : syracuseStep 1339901 = 502463) (by norm_num)
theorem B1339973 : Blo 595291 1339973 := bbase (se 4 (by rfl) ⟨125622, by rfl⟩ : syracuseStep 1339973 = 251245) (by norm_num)
theorem B1340045 : Blo 595291 1340045 := bbase (se 3 (by rfl) ⟨251258, by rfl⟩ : syracuseStep 1340045 = 502517) (by norm_num)
theorem B1340117 : Blo 595291 1340117 := bbase (se 7 (by rfl) ⟨15704, by rfl⟩ : syracuseStep 1340117 = 31409) (by norm_num)
theorem B717541 : Blo 595291 717541 := bbase (se 4 (by rfl) ⟨67269, by rfl⟩ : syracuseStep 717541 = 134539) (by norm_num)
theorem B1274629 : Blo 595291 1274629 := bbase (se 4 (by rfl) ⟨119496, by rfl⟩ : syracuseStep 1274629 = 238993) (by norm_num)
theorem B1340189 : Blo 595291 1340189 := bbase (se 3 (by rfl) ⟨251285, by rfl⟩ : syracuseStep 1340189 = 502571) (by norm_num)
theorem B717661 : Blo 595291 717661 := bbase (se 3 (by rfl) ⟨134561, by rfl⟩ : syracuseStep 717661 = 269123) (by norm_num)
theorem B1340261 : Blo 595291 1340261 := bbase (se 4 (by rfl) ⟨125649, by rfl⟩ : syracuseStep 1340261 = 251299) (by norm_num)
theorem B1078157 : Blo 595291 1078157 := bbase (se 3 (by rfl) ⟨202154, by rfl⟩ : syracuseStep 1078157 = 404309) (by norm_num)
theorem B1340333 : Blo 595291 1340333 := bbase (se 3 (by rfl) ⟨251312, by rfl⟩ : syracuseStep 1340333 = 502625) (by norm_num)
theorem B24474581 : Blo 595291 24474581 := bbase (se 7 (by rfl) ⟨286811, by rfl⟩ : syracuseStep 24474581 = 573623) (by norm_num)
theorem B1340405 : Blo 595291 1340405 := bbase (se 5 (by rfl) ⟨62831, by rfl⟩ : syracuseStep 1340405 = 125663) (by norm_num)
theorem B1340477 : Blo 595291 1340477 := bbase (se 3 (by rfl) ⟨251339, by rfl⟩ : syracuseStep 1340477 = 502679) (by norm_num)
theorem B848989 : Blo 595291 848989 := bbase (se 3 (by rfl) ⟨159185, by rfl⟩ : syracuseStep 848989 = 318371) (by norm_num)
theorem B1340549 : Blo 595291 1340549 := bbase (se 4 (by rfl) ⟨125676, by rfl⟩ : syracuseStep 1340549 = 251353) (by norm_num)
theorem B1340621 : Blo 595291 1340621 := bbase (se 3 (by rfl) ⟨251366, by rfl⟩ : syracuseStep 1340621 = 502733) (by norm_num)
theorem B1078525 : Blo 595291 1078525 := bbase (se 3 (by rfl) ⟨202223, by rfl⟩ : syracuseStep 1078525 = 404447) (by norm_num)
theorem B1340693 : Blo 595291 1340693 := bbase (se 6 (by rfl) ⟨31422, by rfl⟩ : syracuseStep 1340693 = 62845) (by norm_num)
theorem B1340765 : Blo 595291 1340765 := bbase (se 3 (by rfl) ⟨251393, by rfl⟩ : syracuseStep 1340765 = 502787) (by norm_num)
theorem B2553221 : Blo 595291 2553221 := bbase (se 4 (by rfl) ⟨239364, by rfl⟩ : syracuseStep 2553221 = 478729) (by norm_num)
theorem B1340837 : Blo 595291 1340837 := bbase (se 4 (by rfl) ⟨125703, by rfl⟩ : syracuseStep 1340837 = 251407) (by norm_num)
theorem B1209821 : Blo 595291 1209821 := bbase (se 3 (by rfl) ⟨226841, by rfl⟩ : syracuseStep 1209821 = 453683) (by norm_num)
theorem B1340909 : Blo 595291 1340909 := bbase (se 3 (by rfl) ⟨251420, by rfl⟩ : syracuseStep 1340909 = 502841) (by norm_num)
theorem B1340981 : Blo 595291 1340981 := bbase (se 5 (by rfl) ⟨62858, by rfl⟩ : syracuseStep 1340981 = 125717) (by norm_num)
theorem B1341053 : Blo 595291 1341053 := bbase (se 3 (by rfl) ⟨251447, by rfl⟩ : syracuseStep 1341053 = 502895) (by norm_num)
theorem B1275517 : Blo 595291 1275517 := bbase (se 3 (by rfl) ⟨239159, by rfl⟩ : syracuseStep 1275517 = 478319) (by norm_num)
theorem B718517 : Blo 595291 718517 := bbase (se 5 (by rfl) ⟨33680, by rfl⟩ : syracuseStep 718517 = 67361) (by norm_num)
theorem B1341125 : Blo 595291 1341125 := bbase (se 4 (by rfl) ⟨125730, by rfl⟩ : syracuseStep 1341125 = 251461) (by norm_num)
theorem B1341197 : Blo 595291 1341197 := bbase (se 3 (by rfl) ⟨251474, by rfl⟩ : syracuseStep 1341197 = 502949) (by norm_num)
theorem B1341269 : Blo 595291 1341269 := bbase (se 9 (by rfl) ⟨3929, by rfl⟩ : syracuseStep 1341269 = 7859) (by norm_num)
theorem B849781 : Blo 595291 849781 := bbase (se 5 (by rfl) ⟨39833, by rfl⟩ : syracuseStep 849781 = 79667) (by norm_num)
theorem B1701749 : Blo 595291 1701749 := bbase (se 5 (by rfl) ⟨79769, by rfl⟩ : syracuseStep 1701749 = 159539) (by norm_num)
theorem B1341341 : Blo 595291 1341341 := bbase (se 3 (by rfl) ⟨251501, by rfl⟩ : syracuseStep 1341341 = 503003) (by norm_num)
theorem B1341413 : Blo 595291 1341413 := bbase (se 4 (by rfl) ⟨125757, by rfl⟩ : syracuseStep 1341413 = 251515) (by norm_num)
theorem B1341485 : Blo 595291 1341485 := bbase (se 3 (by rfl) ⟨251528, by rfl⟩ : syracuseStep 1341485 = 503057) (by norm_num)
theorem B1276013 : Blo 595291 1276013 := bbase (se 3 (by rfl) ⟨239252, by rfl⟩ : syracuseStep 1276013 = 478505) (by norm_num)
theorem B1341557 : Blo 595291 1341557 := bbase (se 5 (by rfl) ⟨62885, by rfl⟩ : syracuseStep 1341557 = 125771) (by norm_num)
theorem B1341629 : Blo 595291 1341629 := bbase (se 3 (by rfl) ⟨251555, by rfl⟩ : syracuseStep 1341629 = 503111) (by norm_num)
theorem B850117 : Blo 595291 850117 := bbase (se 4 (by rfl) ⟨79698, by rfl⟩ : syracuseStep 850117 = 159397) (by norm_num)
theorem B1341701 : Blo 595291 1341701 := bbase (se 4 (by rfl) ⟨125784, by rfl⟩ : syracuseStep 1341701 = 251569) (by norm_num)
theorem B1341773 : Blo 595291 1341773 := bbase (se 3 (by rfl) ⟨251582, by rfl⟩ : syracuseStep 1341773 = 503165) (by norm_num)
theorem B719237 : Blo 595291 719237 := bbase (se 4 (by rfl) ⟨67428, by rfl⟩ : syracuseStep 719237 = 134857) (by norm_num)
theorem B1341845 : Blo 595291 1341845 := bbase (se 6 (by rfl) ⟨31449, by rfl⟩ : syracuseStep 1341845 = 62899) (by norm_num)
theorem B850333 : Blo 595291 850333 := bbase (se 3 (by rfl) ⟨159437, by rfl⟩ : syracuseStep 850333 = 318875) (by norm_num)
theorem B10222037 : Blo 595291 10222037 := bbase (se 7 (by rfl) ⟨119789, by rfl⟩ : syracuseStep 10222037 = 239579) (by norm_num)
theorem B1341917 : Blo 595291 1341917 := bbase (se 3 (by rfl) ⟨251609, by rfl⟩ : syracuseStep 1341917 = 503219) (by norm_num)
theorem B1702421 : Blo 595291 1702421 := bbase (se 6 (by rfl) ⟨39900, by rfl⟩ : syracuseStep 1702421 = 79801) (by norm_num)
theorem B1341989 : Blo 595291 1341989 := bbase (se 4 (by rfl) ⟨125811, by rfl⟩ : syracuseStep 1341989 = 251623) (by norm_num)
theorem B3111509 : Blo 595291 3111509 := bbase (se 8 (by rfl) ⟨18231, by rfl⟩ : syracuseStep 3111509 = 36463) (by norm_num)
theorem B1079909 : Blo 595291 1079909 := bbase (se 4 (by rfl) ⟨101241, by rfl⟩ : syracuseStep 1079909 = 202483) (by norm_num)
theorem B1342061 : Blo 595291 1342061 := bbase (se 3 (by rfl) ⟨251636, by rfl⟩ : syracuseStep 1342061 = 503273) (by norm_num)
theorem B7666325 : Blo 595291 7666325 := bbase (se 6 (by rfl) ⟨179679, by rfl⟩ : syracuseStep 7666325 = 359359) (by norm_num)
theorem B1342133 : Blo 595291 1342133 := bbase (se 5 (by rfl) ⟨62912, by rfl⟩ : syracuseStep 1342133 = 125825) (by norm_num)
theorem B719545 : Blo 595291 719545 := bbase (se 2 (by rfl) ⟨269829, by rfl⟩ : syracuseStep 719545 = 539659) (by norm_num)
theorem B1342205 : Blo 595291 1342205 := bbase (se 3 (by rfl) ⟨251663, by rfl⟩ : syracuseStep 1342205 = 503327) (by norm_num)
theorem B850709 : Blo 595291 850709 := bbase (se 6 (by rfl) ⟨19938, by rfl⟩ : syracuseStep 850709 = 39877) (by norm_num)
theorem B719641 : Blo 595291 719641 := bbase (se 2 (by rfl) ⟨269865, by rfl⟩ : syracuseStep 719641 = 539731) (by norm_num)
theorem B1342277 : Blo 595291 1342277 := bbase (se 4 (by rfl) ⟨125838, by rfl⟩ : syracuseStep 1342277 = 251677) (by norm_num)
theorem B74316629 : Blo 595291 74316629 := bbase (se 9 (by rfl) ⟨217724, by rfl⟩ : syracuseStep 74316629 = 435449) (by norm_num)
theorem B1342349 : Blo 595291 1342349 := bbase (se 3 (by rfl) ⟨251690, by rfl⟩ : syracuseStep 1342349 = 503381) (by norm_num)
theorem B719785 : Blo 595291 719785 := bbase (se 2 (by rfl) ⟨269919, by rfl⟩ : syracuseStep 719785 = 539839) (by norm_num)
theorem B1702853 : Blo 595291 1702853 := bbase (se 4 (by rfl) ⟨159642, by rfl⟩ : syracuseStep 1702853 = 319285) (by norm_num)
theorem B1342421 : Blo 595291 1342421 := bbase (se 7 (by rfl) ⟨15731, by rfl⟩ : syracuseStep 1342421 = 31463) (by norm_num)
theorem B1276901 : Blo 595291 1276901 := bbase (se 4 (by rfl) ⟨119709, by rfl⟩ : syracuseStep 1276901 = 239419) (by norm_num)
theorem B1342493 : Blo 595291 1342493 := bbase (se 3 (by rfl) ⟨251717, by rfl⟩ : syracuseStep 1342493 = 503435) (by norm_num)
theorem B3013685 : Blo 595291 3013685 := bbase (se 5 (by rfl) ⟨141266, by rfl⟩ : syracuseStep 3013685 = 282533) (by norm_num)
theorem B1277021 : Blo 595291 1277021 := bbase (se 3 (by rfl) ⟨239441, by rfl⟩ : syracuseStep 1277021 = 478883) (by norm_num)
theorem B1342565 : Blo 595291 1342565 := bbase (se 4 (by rfl) ⟨125865, by rfl⟩ : syracuseStep 1342565 = 251731) (by norm_num)
theorem B1342637 : Blo 595291 1342637 := bbase (se 3 (by rfl) ⟨251744, by rfl⟩ : syracuseStep 1342637 = 503489) (by norm_num)
theorem B1342709 : Blo 595291 1342709 := bbase (se 5 (by rfl) ⟨62939, by rfl⟩ : syracuseStep 1342709 = 125879) (by norm_num)
theorem B1342781 : Blo 595291 1342781 := bbase (se 3 (by rfl) ⟨251771, by rfl⟩ : syracuseStep 1342781 = 503543) (by norm_num)
theorem B2260325 : Blo 595291 2260325 := bbase (se 4 (by rfl) ⟨211905, by rfl⟩ : syracuseStep 2260325 = 423811) (by norm_num)
theorem B1342853 : Blo 595291 1342853 := bbase (se 4 (by rfl) ⟨125892, by rfl⟩ : syracuseStep 1342853 = 251785) (by norm_num)
theorem B1342925 : Blo 595291 1342925 := bbase (se 3 (by rfl) ⟨251798, by rfl⟩ : syracuseStep 1342925 = 503597) (by norm_num)
theorem B1342997 : Blo 595291 1342997 := bbase (se 6 (by rfl) ⟨31476, by rfl⟩ : syracuseStep 1342997 = 62953) (by norm_num)
theorem B1343069 : Blo 595291 1343069 := bbase (se 3 (by rfl) ⟨251825, by rfl⟩ : syracuseStep 1343069 = 503651) (by norm_num)
theorem B1343141 : Blo 595291 1343141 := bbase (se 4 (by rfl) ⟨125919, by rfl⟩ : syracuseStep 1343141 = 251839) (by norm_num)
theorem B1703605 : Blo 595291 1703605 := bbase (se 5 (by rfl) ⟨79856, by rfl⟩ : syracuseStep 1703605 = 159713) (by norm_num)
theorem B1277653 : Blo 595291 1277653 := bbase (se 7 (by rfl) ⟨14972, by rfl⟩ : syracuseStep 1277653 = 29945) (by norm_num)
theorem B1507045 : Blo 595291 1507045 := bbase (se 4 (by rfl) ⟨141285, by rfl⟩ : syracuseStep 1507045 = 282571) (by norm_num)
theorem B1343213 : Blo 595291 1343213 := bbase (se 3 (by rfl) ⟨251852, by rfl⟩ : syracuseStep 1343213 = 503705) (by norm_num)
theorem B753457 : Blo 595291 753457 := bbase (se 2 (by rfl) ⟨282546, by rfl⟩ : syracuseStep 753457 = 565093) (by norm_num)
theorem B1343285 : Blo 595291 1343285 := bbase (se 5 (by rfl) ⟨62966, by rfl⟩ : syracuseStep 1343285 = 125933) (by norm_num)
theorem B1212221 : Blo 595291 1212221 := bbase (se 3 (by rfl) ⟨227291, by rfl⟩ : syracuseStep 1212221 = 454583) (by norm_num)
theorem B1507157 : Blo 595291 1507157 := bbase (se 9 (by rfl) ⟨4415, by rfl⟩ : syracuseStep 1507157 = 8831) (by norm_num)
theorem B1343357 : Blo 595291 1343357 := bbase (se 3 (by rfl) ⟨251879, by rfl⟩ : syracuseStep 1343357 = 503759) (by norm_num)
theorem B753553 : Blo 595291 753553 := bbase (se 2 (by rfl) ⟨282582, by rfl⟩ : syracuseStep 753553 = 565165) (by norm_num)
theorem B1343429 : Blo 595291 1343429 := bbase (se 4 (by rfl) ⟨125946, by rfl⟩ : syracuseStep 1343429 = 251893) (by norm_num)
theorem B1343537 : Blo 595291 1343537 := bstep (se 2 (by rfl) ⟨503826, by rfl⟩ : syracuseStep 1343537 = 1007653) B1007653
theorem B753715 : Blo 595291 753715 := bstep (se 1 (by rfl) ⟨565286, by rfl⟩ : syracuseStep 753715 = 1130573) B1130573
theorem B1343555 : Blo 595291 1343555 := bstep (se 1 (by rfl) ⟨1007666, by rfl⟩ : syracuseStep 1343555 = 2015333) B2015333
theorem B3014819 : Blo 595291 3014819 := bstep (se 1 (by rfl) ⟨2261114, by rfl⟩ : syracuseStep 3014819 = 4522229) B4522229
theorem B2719907 : Blo 595291 2719907 := bstep (se 1 (by rfl) ⟨2039930, by rfl⟩ : syracuseStep 2719907 = 4079861) B4079861
theorem B1868017 : Blo 595291 1868017 := bstep (se 2 (by rfl) ⟨700506, by rfl⟩ : syracuseStep 1868017 = 1401013) B1401013
theorem B2916593 : Blo 595291 2916593 := bstep (se 2 (by rfl) ⟨1093722, by rfl⟩ : syracuseStep 2916593 = 2187445) B2187445
theorem B2261297 : Blo 595291 2261297 := bstep (se 2 (by rfl) ⟨847986, by rfl⟩ : syracuseStep 2261297 = 1695973) B1695973
theorem B1343825 : Blo 595291 1343825 := bstep (se 2 (by rfl) ⟨503934, by rfl⟩ : syracuseStep 1343825 = 1007869) B1007869
theorem B1343843 : Blo 595291 1343843 := bstep (se 1 (by rfl) ⟨1007882, by rfl⟩ : syracuseStep 1343843 = 2015765) B2015765
theorem B754211 : Blo 595291 754211 := bstep (se 1 (by rfl) ⟨565658, by rfl⟩ : syracuseStep 754211 = 1131317) B1131317
theorem B1278499 : Blo 595291 1278499 := bstep (se 1 (by rfl) ⟨958874, by rfl⟩ : syracuseStep 1278499 = 1917749) B1917749
theorem B1704493 : Blo 595291 1704493 := bstep (se 3 (by rfl) ⟨319592, by rfl⟩ : syracuseStep 1704493 = 639185) B639185
theorem B1344113 : Blo 595291 1344113 := bstep (se 2 (by rfl) ⟨504042, by rfl⟩ : syracuseStep 1344113 = 1008085) B1008085
theorem B1344131 : Blo 595291 1344131 := bstep (se 1 (by rfl) ⟨1008098, by rfl⟩ : syracuseStep 1344131 = 2016197) B2016197
theorem B852611 : Blo 595291 852611 := bstep (se 1 (by rfl) ⟨639458, by rfl⟩ : syracuseStep 852611 = 1278917) B1278917
theorem B1508017 : Blo 595291 1508017 := bstep (se 2 (by rfl) ⟨565506, by rfl⟩ : syracuseStep 1508017 = 1131013) B1131013
theorem B1704721 : Blo 595291 1704721 := bstep (se 2 (by rfl) ⟨639270, by rfl⟩ : syracuseStep 1704721 = 1278541) B1278541
theorem B1868579 : Blo 595291 1868579 := bstep (se 1 (by rfl) ⟨1401434, by rfl⟩ : syracuseStep 1868579 = 2802869) B2802869
theorem B3834701 : Blo 595291 3834701 := bstep (se 3 (by rfl) ⟨719006, by rfl⟩ : syracuseStep 3834701 = 1438013) B1438013
theorem B14484365 : Blo 595291 14484365 := bstep (se 3 (by rfl) ⟨2715818, by rfl⟩ : syracuseStep 14484365 = 5431637) B5431637
theorem B1344401 : Blo 595291 1344401 := bstep (se 2 (by rfl) ⟨504150, by rfl⟩ : syracuseStep 1344401 = 1008301) B1008301
theorem B1344419 : Blo 595291 1344419 := bstep (se 1 (by rfl) ⟨1008314, by rfl⟩ : syracuseStep 1344419 = 2016629) B2016629
theorem B1704881 : Blo 595291 1704881 := bstep (se 2 (by rfl) ⟨639330, by rfl⟩ : syracuseStep 1704881 = 1278661) B1278661
theorem B1508291 : Blo 595291 1508291 := bstep (se 1 (by rfl) ⟨1131218, by rfl⟩ : syracuseStep 1508291 = 2262437) B2262437
theorem B3015629 : Blo 595291 3015629 := bstep (se 3 (by rfl) ⟨565430, by rfl⟩ : syracuseStep 3015629 = 1130861) B1130861
theorem B2261965 : Blo 595291 2261965 := bstep (se 3 (by rfl) ⟨424118, by rfl⟩ : syracuseStep 2261965 = 848237) B848237
theorem B1704995 : Blo 595291 1704995 := bstep (se 1 (by rfl) ⟨1278746, by rfl⟩ : syracuseStep 1704995 = 2557493) B2557493
theorem B3408965 : Blo 595291 3408965 := bstep (se 4 (by rfl) ⟨319590, by rfl⟩ : syracuseStep 3408965 = 639181) B639181
theorem B1508483 : Blo 595291 1508483 := bstep (se 1 (by rfl) ⟨1131362, by rfl⟩ : syracuseStep 1508483 = 2262725) B2262725
theorem B1344689 : Blo 595291 1344689 := bstep (se 2 (by rfl) ⟨504258, by rfl⟩ : syracuseStep 1344689 = 1008517) B1008517
theorem B2426033 : Blo 595291 2426033 := bstep (se 2 (by rfl) ⟨909762, by rfl⟩ : syracuseStep 2426033 = 1819525) B1819525
theorem B1344707 : Blo 595291 1344707 := bstep (se 1 (by rfl) ⟨1008530, by rfl⟩ : syracuseStep 1344707 = 2017061) B2017061
theorem B754915 : Blo 595291 754915 := bstep (se 1 (by rfl) ⟨566186, by rfl⟩ : syracuseStep 754915 = 1132373) B1132373
theorem B853249 : Blo 595291 853249 := bstep (se 2 (by rfl) ⟨319968, by rfl⟩ : syracuseStep 853249 = 639937) B639937
theorem B1836323 : Blo 595291 1836323 := bstep (se 1 (by rfl) ⟨1377242, by rfl⟩ : syracuseStep 1836323 = 2754485) B2754485
theorem B755011 : Blo 595291 755011 := bstep (se 1 (by rfl) ⟨566258, by rfl⟩ : syracuseStep 755011 = 1132517) B1132517
theorem B820577 : Blo 595291 820577 := bstep (se 2 (by rfl) ⟨307716, by rfl⟩ : syracuseStep 820577 = 615433) B615433
theorem B1148323 : Blo 595291 1148323 := bstep (se 1 (by rfl) ⟨861242, by rfl⟩ : syracuseStep 1148323 = 1722485) B1722485
theorem B1344977 : Blo 595291 1344977 := bstep (se 2 (by rfl) ⟨504366, by rfl⟩ : syracuseStep 1344977 = 1008733) B1008733
theorem B1344995 : Blo 595291 1344995 := bstep (se 1 (by rfl) ⟨1008746, by rfl⟩ : syracuseStep 1344995 = 2017493) B2017493
theorem B2262755 : Blo 595291 2262755 := bstep (se 1 (by rfl) ⟨1697066, by rfl⟩ : syracuseStep 2262755 = 3394133) B3394133
theorem B1345265 : Blo 595291 1345265 := bstep (se 2 (by rfl) ⟨504474, by rfl⟩ : syracuseStep 1345265 = 1008949) B1008949
theorem B1279729 : Blo 595291 1279729 := bstep (se 2 (by rfl) ⟨479898, by rfl⟩ : syracuseStep 1279729 = 959797) B959797
theorem B1345283 : Blo 595291 1345283 := bstep (se 1 (by rfl) ⟨1008962, by rfl⟩ : syracuseStep 1345283 = 2017925) B2017925
theorem B755507 : Blo 595291 755507 := bstep (se 1 (by rfl) ⟨566630, by rfl⟩ : syracuseStep 755507 = 1133261) B1133261
theorem B1705997 : Blo 595291 1705997 := bstep (se 3 (by rfl) ⟨319874, by rfl⟩ : syracuseStep 1705997 = 639749) B639749
theorem B1345553 : Blo 595291 1345553 := bstep (se 2 (by rfl) ⟨504582, by rfl⟩ : syracuseStep 1345553 = 1009165) B1009165
theorem B1345571 : Blo 595291 1345571 := bstep (se 1 (by rfl) ⟨1009178, by rfl⟩ : syracuseStep 1345571 = 2018357) B2018357
theorem B1509425 : Blo 595291 1509425 := bstep (se 2 (by rfl) ⟨566034, by rfl⟩ : syracuseStep 1509425 = 1132069) B1132069
theorem B1509475 : Blo 595291 1509475 := bstep (se 1 (by rfl) ⟨1132106, by rfl⟩ : syracuseStep 1509475 = 2264213) B2264213
theorem B4524173 : Blo 595291 4524173 := bstep (se 3 (by rfl) ⟨848282, by rfl⟩ : syracuseStep 4524173 = 1696565) B1696565
theorem B1706179 : Blo 595291 1706179 := bstep (se 1 (by rfl) ⟨1279634, by rfl⟩ : syracuseStep 1706179 = 2559269) B2559269
theorem B1509617 : Blo 595291 1509617 := bstep (se 2 (by rfl) ⟨566106, by rfl⟩ : syracuseStep 1509617 = 1132213) B1132213
theorem B2558243 : Blo 595291 2558243 := bstep (se 1 (by rfl) ⟨1918682, by rfl⟩ : syracuseStep 2558243 = 3837365) B3837365
theorem B1345841 : Blo 595291 1345841 := bstep (se 2 (by rfl) ⟨504690, by rfl⟩ : syracuseStep 1345841 = 1009381) B1009381
theorem B1345859 : Blo 595291 1345859 := bstep (se 1 (by rfl) ⟨1009394, by rfl⟩ : syracuseStep 1345859 = 2018789) B2018789
theorem B1706339 : Blo 595291 1706339 := bstep (se 1 (by rfl) ⟨1279754, by rfl⟩ : syracuseStep 1706339 = 2559509) B2559509
theorem B2263409 : Blo 595291 2263409 := bstep (se 2 (by rfl) ⟨848778, by rfl⟩ : syracuseStep 2263409 = 1697557) B1697557
theorem B756211 : Blo 595291 756211 := bstep (se 1 (by rfl) ⟨567158, by rfl⟩ : syracuseStep 756211 = 1134317) B1134317
theorem B1346129 : Blo 595291 1346129 := bstep (se 2 (by rfl) ⟨504798, by rfl⟩ : syracuseStep 1346129 = 1009597) B1009597
theorem B756307 : Blo 595291 756307 := bstep (se 1 (by rfl) ⟨567230, by rfl⟩ : syracuseStep 756307 = 1134461) B1134461
theorem B1346147 : Blo 595291 1346147 := bstep (se 1 (by rfl) ⟨1009610, by rfl⟩ : syracuseStep 1346147 = 2019221) B2019221
theorem B1018721 : Blo 595291 1018721 := bstep (se 2 (by rfl) ⟨382020, by rfl⟩ : syracuseStep 1018721 = 764041) B764041
theorem B1346417 : Blo 595291 1346417 := bstep (se 2 (by rfl) ⟨504906, by rfl⟩ : syracuseStep 1346417 = 1009813) B1009813
theorem B1346435 : Blo 595291 1346435 := bstep (se 1 (by rfl) ⟨1009826, by rfl⟩ : syracuseStep 1346435 = 2019653) B2019653
theorem B18385973 : Blo 595291 18385973 := bstep (se 5 (by rfl) ⟨861842, by rfl⟩ : syracuseStep 18385973 = 1723685) B1723685
theorem B756803 : Blo 595291 756803 := bstep (se 1 (by rfl) ⟨567602, by rfl⟩ : syracuseStep 756803 = 1135205) B1135205
theorem B1346705 : Blo 595291 1346705 := bstep (se 2 (by rfl) ⟨505014, by rfl⟩ : syracuseStep 1346705 = 1010029) B1010029
theorem B1346723 : Blo 595291 1346723 := bstep (se 1 (by rfl) ⟨1010042, by rfl⟩ : syracuseStep 1346723 = 2020085) B2020085
theorem B1510609 : Blo 595291 1510609 := bstep (se 2 (by rfl) ⟨566478, by rfl⟩ : syracuseStep 1510609 = 1132957) B1132957
theorem B1346993 : Blo 595291 1346993 := bstep (se 2 (by rfl) ⟨505122, by rfl⟩ : syracuseStep 1346993 = 1010245) B1010245
theorem B1347011 : Blo 595291 1347011 := bstep (se 1 (by rfl) ⟨1010258, by rfl⟩ : syracuseStep 1347011 = 2020517) B2020517
theorem B1510883 : Blo 595291 1510883 := bstep (se 1 (by rfl) ⟨1133162, by rfl⟩ : syracuseStep 1510883 = 2266325) B2266325
theorem B953857 : Blo 595291 953857 := bstep (se 2 (by rfl) ⟨357696, by rfl⟩ : syracuseStep 953857 = 715393) B715393
theorem B1511075 : Blo 595291 1511075 := bstep (se 1 (by rfl) ⟨1133306, by rfl⟩ : syracuseStep 1511075 = 2266613) B2266613
theorem B1347281 : Blo 595291 1347281 := bstep (se 2 (by rfl) ⟨505230, by rfl⟩ : syracuseStep 1347281 = 1010461) B1010461
theorem B1347299 : Blo 595291 1347299 := bstep (se 1 (by rfl) ⟨1010474, by rfl⟩ : syracuseStep 1347299 = 2020949) B2020949
theorem B954113 : Blo 595291 954113 := bstep (se 2 (by rfl) ⟨357792, by rfl⟩ : syracuseStep 954113 = 715585) B715585
theorem B757507 : Blo 595291 757507 := bstep (se 1 (by rfl) ⟨568130, by rfl⟩ : syracuseStep 757507 = 1136261) B1136261
theorem B2264867 : Blo 595291 2264867 := bstep (se 1 (by rfl) ⟨1698650, by rfl⟩ : syracuseStep 2264867 = 3397301) B3397301
theorem B3018545 : Blo 595291 3018545 := bstep (se 2 (by rfl) ⟨1131954, by rfl⟩ : syracuseStep 3018545 = 2263909) B2263909
theorem B2264881 : Blo 595291 2264881 := bstep (se 2 (by rfl) ⟨849330, by rfl⟩ : syracuseStep 2264881 = 1698661) B1698661
theorem B757603 : Blo 595291 757603 := bstep (se 1 (by rfl) ⟨568202, by rfl⟩ : syracuseStep 757603 = 1136405) B1136405
theorem B1347569 : Blo 595291 1347569 := bstep (se 2 (by rfl) ⟨505338, by rfl⟩ : syracuseStep 1347569 = 1010677) B1010677
theorem B1347587 : Blo 595291 1347587 := bstep (se 1 (by rfl) ⟨1010690, by rfl⟩ : syracuseStep 1347587 = 2021381) B2021381
theorem B12226787 : Blo 595291 12226787 := bstep (se 1 (by rfl) ⟨9170090, by rfl⟩ : syracuseStep 12226787 = 18340181) B18340181
theorem B3281123 : Blo 595291 3281123 := bstep (se 1 (by rfl) ⟨2460842, by rfl⟩ : syracuseStep 3281123 = 4921685) B4921685
theorem B1347857 : Blo 595291 1347857 := bstep (se 2 (by rfl) ⟨505446, by rfl⟩ : syracuseStep 1347857 = 1010893) B1010893
theorem B1347875 : Blo 595291 1347875 := bstep (se 1 (by rfl) ⟨1010906, by rfl⟩ : syracuseStep 1347875 = 2021813) B2021813
theorem B758099 : Blo 595291 758099 := bstep (se 1 (by rfl) ⟨568574, by rfl⟩ : syracuseStep 758099 = 1137149) B1137149
theorem B1348145 : Blo 595291 1348145 := bstep (se 2 (by rfl) ⟨505554, by rfl⟩ : syracuseStep 1348145 = 1011109) B1011109
theorem B1348163 : Blo 595291 1348163 := bstep (se 1 (by rfl) ⟨1011122, by rfl⟩ : syracuseStep 1348163 = 2022245) B2022245
theorem B1512017 : Blo 595291 1512017 := bstep (se 2 (by rfl) ⟨567006, by rfl⟩ : syracuseStep 1512017 = 1134013) B1134013
theorem B1512067 : Blo 595291 1512067 := bstep (se 1 (by rfl) ⟨1134050, by rfl⟩ : syracuseStep 1512067 = 2268101) B2268101
theorem B1512209 : Blo 595291 1512209 := bstep (se 2 (by rfl) ⟨567078, by rfl⟩ : syracuseStep 1512209 = 1134157) B1134157
theorem B3412813 : Blo 595291 3412813 := bstep (se 3 (by rfl) ⟨639902, by rfl⟩ : syracuseStep 3412813 = 1279805) B1279805
theorem B3838853 : Blo 595291 3838853 := bstep (se 4 (by rfl) ⟨359892, by rfl⟩ : syracuseStep 3838853 = 719785) B719785
theorem B4527089 : Blo 595291 4527089 := bstep (se 2 (by rfl) ⟨1697658, by rfl⟩ : syracuseStep 4527089 = 3395317) B3395317
theorem B955523 : Blo 595291 955523 := bstep (se 1 (by rfl) ⟨716642, by rfl⟩ : syracuseStep 955523 = 1433285) B1433285
theorem B3020003 : Blo 595291 3020003 := bstep (se 1 (by rfl) ⟨2265002, by rfl⟩ : syracuseStep 3020003 = 4530005) B4530005
theorem B2266339 : Blo 595291 2266339 := bstep (se 1 (by rfl) ⟨1699754, by rfl⟩ : syracuseStep 2266339 = 3399509) B3399509
theorem B922897 : Blo 595291 922897 := bstep (se 2 (by rfl) ⟨346086, by rfl⟩ : syracuseStep 922897 = 692173) B692173
theorem B3872069 : Blo 595291 3872069 := bstep (se 4 (by rfl) ⟨363006, by rfl⟩ : syracuseStep 3872069 = 726013) B726013
theorem B595299 : Blo 595291 595299 := bstep (se 1 (by rfl) ⟨446474, by rfl⟩ : syracuseStep 595299 = 892949) B892949
theorem B595315 : Blo 595291 595315 := bstep (se 1 (by rfl) ⟨446486, by rfl⟩ : syracuseStep 595315 = 892973) B892973
theorem B595331 : Blo 595291 595331 := bstep (se 1 (by rfl) ⟨446498, by rfl⟩ : syracuseStep 595331 = 892997) B892997
theorem B595347 : Blo 595291 595347 := bstep (se 1 (by rfl) ⟨446510, by rfl⟩ : syracuseStep 595347 = 893021) B893021
theorem B595363 : Blo 595291 595363 := bstep (se 1 (by rfl) ⟨446522, by rfl⟩ : syracuseStep 595363 = 893045) B893045
theorem B1611181 : Blo 595291 1611181 := bstep (se 3 (by rfl) ⟨302096, by rfl⟩ : syracuseStep 1611181 = 604193) B604193
theorem B595379 : Blo 595291 595379 := bstep (se 1 (by rfl) ⟨446534, by rfl⟩ : syracuseStep 595379 = 893069) B893069
theorem B595395 : Blo 595291 595395 := bstep (se 1 (by rfl) ⟨446546, by rfl⟩ : syracuseStep 595395 = 893093) B893093
theorem B595411 : Blo 595291 595411 := bstep (se 1 (by rfl) ⟨446558, by rfl⟩ : syracuseStep 595411 = 893117) B893117
theorem B595427 : Blo 595291 595427 := bstep (se 1 (by rfl) ⟨446570, by rfl⟩ : syracuseStep 595427 = 893141) B893141
theorem B595443 : Blo 595291 595443 := bstep (se 1 (by rfl) ⟨446582, by rfl⟩ : syracuseStep 595443 = 893165) B893165
theorem B595459 : Blo 595291 595459 := bstep (se 1 (by rfl) ⟨446594, by rfl⟩ : syracuseStep 595459 = 893189) B893189
theorem B595475 : Blo 595291 595475 := bstep (se 1 (by rfl) ⟨446606, by rfl⟩ : syracuseStep 595475 = 893213) B893213
theorem B595491 : Blo 595291 595491 := bstep (se 1 (by rfl) ⟨446618, by rfl⟩ : syracuseStep 595491 = 893237) B893237
theorem B595507 : Blo 595291 595507 := bstep (se 1 (by rfl) ⟨446630, by rfl⟩ : syracuseStep 595507 = 893261) B893261
theorem B595523 : Blo 595291 595523 := bstep (se 1 (by rfl) ⟨446642, by rfl⟩ : syracuseStep 595523 = 893285) B893285
theorem B595539 : Blo 595291 595539 := bstep (se 1 (by rfl) ⟨446654, by rfl⟩ : syracuseStep 595539 = 893309) B893309
theorem B595555 : Blo 595291 595555 := bstep (se 1 (by rfl) ⟨446666, by rfl⟩ : syracuseStep 595555 = 893333) B893333
theorem B595571 : Blo 595291 595571 := bstep (se 1 (by rfl) ⟨446678, by rfl⟩ : syracuseStep 595571 = 893357) B893357
theorem B595587 : Blo 595291 595587 := bstep (se 1 (by rfl) ⟨446690, by rfl⟩ : syracuseStep 595587 = 893381) B893381
theorem B595603 : Blo 595291 595603 := bstep (se 1 (by rfl) ⟨446702, by rfl⟩ : syracuseStep 595603 = 893405) B893405
theorem B595619 : Blo 595291 595619 := bstep (se 1 (by rfl) ⟨446714, by rfl⟩ : syracuseStep 595619 = 893429) B893429
theorem B595635 : Blo 595291 595635 := bstep (se 1 (by rfl) ⟨446726, by rfl⟩ : syracuseStep 595635 = 893453) B893453
theorem B595651 : Blo 595291 595651 := bstep (se 1 (by rfl) ⟨446738, by rfl⟩ : syracuseStep 595651 = 893477) B893477
theorem B595667 : Blo 595291 595667 := bstep (se 1 (by rfl) ⟨446750, by rfl⟩ : syracuseStep 595667 = 893501) B893501
theorem B595683 : Blo 595291 595683 := bstep (se 1 (by rfl) ⟨446762, by rfl⟩ : syracuseStep 595683 = 893525) B893525
theorem B1513201 : Blo 595291 1513201 := bstep (se 2 (by rfl) ⟨567450, by rfl⟩ : syracuseStep 1513201 = 1134901) B1134901
theorem B595699 : Blo 595291 595699 := bstep (se 1 (by rfl) ⟨446774, by rfl⟩ : syracuseStep 595699 = 893549) B893549
theorem B595715 : Blo 595291 595715 := bstep (se 1 (by rfl) ⟨446786, by rfl⟩ : syracuseStep 595715 = 893573) B893573
theorem B2037521 : Blo 595291 2037521 := bstep (se 2 (by rfl) ⟨764070, by rfl⟩ : syracuseStep 2037521 = 1528141) B1528141
theorem B595731 : Blo 595291 595731 := bstep (se 1 (by rfl) ⟨446798, by rfl⟩ : syracuseStep 595731 = 893597) B893597
theorem B595747 : Blo 595291 595747 := bstep (se 1 (by rfl) ⟨446810, by rfl⟩ : syracuseStep 595747 = 893621) B893621
theorem B595763 : Blo 595291 595763 := bstep (se 1 (by rfl) ⟨446822, by rfl⟩ : syracuseStep 595763 = 893645) B893645
theorem B595779 : Blo 595291 595779 := bstep (se 1 (by rfl) ⟨446834, by rfl⟩ : syracuseStep 595779 = 893669) B893669
theorem B595795 : Blo 595291 595795 := bstep (se 1 (by rfl) ⟨446846, by rfl⟩ : syracuseStep 595795 = 893693) B893693
theorem B595811 : Blo 595291 595811 := bstep (se 1 (by rfl) ⟨446858, by rfl⟩ : syracuseStep 595811 = 893717) B893717
theorem B595827 : Blo 595291 595827 := bstep (se 1 (by rfl) ⟨446870, by rfl⟩ : syracuseStep 595827 = 893741) B893741
theorem B595843 : Blo 595291 595843 := bstep (se 1 (by rfl) ⟨446882, by rfl⟩ : syracuseStep 595843 = 893765) B893765
theorem B595859 : Blo 595291 595859 := bstep (se 1 (by rfl) ⟨446894, by rfl⟩ : syracuseStep 595859 = 893789) B893789
theorem B595875 : Blo 595291 595875 := bstep (se 1 (by rfl) ⟨446906, by rfl⟩ : syracuseStep 595875 = 893813) B893813
theorem B595891 : Blo 595291 595891 := bstep (se 1 (by rfl) ⟨446918, by rfl⟩ : syracuseStep 595891 = 893837) B893837
theorem B595907 : Blo 595291 595907 := bstep (se 1 (by rfl) ⟨446930, by rfl⟩ : syracuseStep 595907 = 893861) B893861
theorem B956369 : Blo 595291 956369 := bstep (se 2 (by rfl) ⟨358638, by rfl⟩ : syracuseStep 956369 = 717277) B717277
theorem B595923 : Blo 595291 595923 := bstep (se 1 (by rfl) ⟨446942, by rfl⟩ : syracuseStep 595923 = 893885) B893885
theorem B595939 : Blo 595291 595939 := bstep (se 1 (by rfl) ⟨446954, by rfl⟩ : syracuseStep 595939 = 893909) B893909
theorem B595955 : Blo 595291 595955 := bstep (se 1 (by rfl) ⟨446966, by rfl⟩ : syracuseStep 595955 = 893933) B893933
theorem B1513475 : Blo 595291 1513475 := bstep (se 1 (by rfl) ⟨1135106, by rfl⟩ : syracuseStep 1513475 = 2270213) B2270213
theorem B595971 : Blo 595291 595971 := bstep (se 1 (by rfl) ⟨446978, by rfl⟩ : syracuseStep 595971 = 893957) B893957
theorem B1939459 : Blo 595291 1939459 := bstep (se 1 (by rfl) ⟨1454594, by rfl⟩ : syracuseStep 1939459 = 2909189) B2909189
theorem B3020813 : Blo 595291 3020813 := bstep (se 3 (by rfl) ⟨566402, by rfl⟩ : syracuseStep 3020813 = 1132805) B1132805
theorem B595987 : Blo 595291 595987 := bstep (se 1 (by rfl) ⟨446990, by rfl⟩ : syracuseStep 595987 = 893981) B893981
theorem B596003 : Blo 595291 596003 := bstep (se 1 (by rfl) ⟨447002, by rfl⟩ : syracuseStep 596003 = 894005) B894005
theorem B596019 : Blo 595291 596019 := bstep (se 1 (by rfl) ⟨447014, by rfl⟩ : syracuseStep 596019 = 894029) B894029
theorem B596035 : Blo 595291 596035 := bstep (se 1 (by rfl) ⟨447026, by rfl⟩ : syracuseStep 596035 = 894053) B894053
theorem B596051 : Blo 595291 596051 := bstep (se 1 (by rfl) ⟨447038, by rfl⟩ : syracuseStep 596051 = 894077) B894077
theorem B596067 : Blo 595291 596067 := bstep (se 1 (by rfl) ⟨447050, by rfl⟩ : syracuseStep 596067 = 894101) B894101
theorem B596083 : Blo 595291 596083 := bstep (se 1 (by rfl) ⟨447062, by rfl⟩ : syracuseStep 596083 = 894125) B894125
theorem B596099 : Blo 595291 596099 := bstep (se 1 (by rfl) ⟨447074, by rfl⟩ : syracuseStep 596099 = 894149) B894149
theorem B596115 : Blo 595291 596115 := bstep (se 1 (by rfl) ⟨447086, by rfl⟩ : syracuseStep 596115 = 894173) B894173
theorem B596131 : Blo 595291 596131 := bstep (se 1 (by rfl) ⟨447098, by rfl⟩ : syracuseStep 596131 = 894197) B894197
theorem B1022129 : Blo 595291 1022129 := bstep (se 2 (by rfl) ⟨383298, by rfl⟩ : syracuseStep 1022129 = 766597) B766597
theorem B596147 : Blo 595291 596147 := bstep (se 1 (by rfl) ⟨447110, by rfl⟩ : syracuseStep 596147 = 894221) B894221
theorem B596163 : Blo 595291 596163 := bstep (se 1 (by rfl) ⟨447122, by rfl⟩ : syracuseStep 596163 = 894245) B894245
theorem B1611971 : Blo 595291 1611971 := bstep (se 1 (by rfl) ⟨1208978, by rfl⟩ : syracuseStep 1611971 = 2417957) B2417957
theorem B1513667 : Blo 595291 1513667 := bstep (se 1 (by rfl) ⟨1135250, by rfl⟩ : syracuseStep 1513667 = 2270501) B2270501
theorem B1153219 : Blo 595291 1153219 := bstep (se 1 (by rfl) ⟨864914, by rfl⟩ : syracuseStep 1153219 = 1729829) B1729829
theorem B596179 : Blo 595291 596179 := bstep (se 1 (by rfl) ⟨447134, by rfl⟩ : syracuseStep 596179 = 894269) B894269
theorem B596195 : Blo 595291 596195 := bstep (se 1 (by rfl) ⟨447146, by rfl⟩ : syracuseStep 596195 = 894293) B894293
theorem B596211 : Blo 595291 596211 := bstep (se 1 (by rfl) ⟨447158, by rfl⟩ : syracuseStep 596211 = 894317) B894317
theorem B596227 : Blo 595291 596227 := bstep (se 1 (by rfl) ⟨447170, by rfl⟩ : syracuseStep 596227 = 894341) B894341
theorem B596243 : Blo 595291 596243 := bstep (se 1 (by rfl) ⟨447182, by rfl⟩ : syracuseStep 596243 = 894365) B894365
theorem B24254741 : Blo 595291 24254741 := bstep (se 6 (by rfl) ⟨568470, by rfl⟩ : syracuseStep 24254741 = 1136941) B1136941
theorem B596259 : Blo 595291 596259 := bstep (se 1 (by rfl) ⟨447194, by rfl⟩ : syracuseStep 596259 = 894389) B894389
theorem B596275 : Blo 595291 596275 := bstep (se 1 (by rfl) ⟨447206, by rfl⟩ : syracuseStep 596275 = 894413) B894413
theorem B596291 : Blo 595291 596291 := bstep (se 1 (by rfl) ⟨447218, by rfl⟩ : syracuseStep 596291 = 894437) B894437
theorem B596307 : Blo 595291 596307 := bstep (se 1 (by rfl) ⟨447230, by rfl⟩ : syracuseStep 596307 = 894461) B894461
theorem B596323 : Blo 595291 596323 := bstep (se 1 (by rfl) ⟨447242, by rfl⟩ : syracuseStep 596323 = 894485) B894485
theorem B596339 : Blo 595291 596339 := bstep (se 1 (by rfl) ⟨447254, by rfl⟩ : syracuseStep 596339 = 894509) B894509
theorem B596355 : Blo 595291 596355 := bstep (se 1 (by rfl) ⟨447266, by rfl⟩ : syracuseStep 596355 = 894533) B894533
theorem B596371 : Blo 595291 596371 := bstep (se 1 (by rfl) ⟨447278, by rfl⟩ : syracuseStep 596371 = 894557) B894557
theorem B596387 : Blo 595291 596387 := bstep (se 1 (by rfl) ⟨447290, by rfl⟩ : syracuseStep 596387 = 894581) B894581
theorem B596403 : Blo 595291 596403 := bstep (se 1 (by rfl) ⟨447302, by rfl⟩ : syracuseStep 596403 = 894605) B894605
theorem B596419 : Blo 595291 596419 := bstep (se 1 (by rfl) ⟨447314, by rfl⟩ : syracuseStep 596419 = 894629) B894629
theorem B956881 : Blo 595291 956881 := bstep (se 2 (by rfl) ⟨358830, by rfl⟩ : syracuseStep 956881 = 717661) B717661
theorem B596435 : Blo 595291 596435 := bstep (se 1 (by rfl) ⟨447326, by rfl⟩ : syracuseStep 596435 = 894653) B894653
theorem B596451 : Blo 595291 596451 := bstep (se 1 (by rfl) ⟨447338, by rfl⟩ : syracuseStep 596451 = 894677) B894677
theorem B596467 : Blo 595291 596467 := bstep (se 1 (by rfl) ⟨447350, by rfl⟩ : syracuseStep 596467 = 894701) B894701
theorem B596483 : Blo 595291 596483 := bstep (se 1 (by rfl) ⟨447362, by rfl⟩ : syracuseStep 596483 = 894725) B894725
theorem B4299277 : Blo 595291 4299277 := bstep (se 3 (by rfl) ⟨806114, by rfl⟩ : syracuseStep 4299277 = 1612229) B1612229
theorem B596499 : Blo 595291 596499 := bstep (se 1 (by rfl) ⟨447374, by rfl⟩ : syracuseStep 596499 = 894749) B894749
theorem B596515 : Blo 595291 596515 := bstep (se 1 (by rfl) ⟨447386, by rfl⟩ : syracuseStep 596515 = 894773) B894773
theorem B596531 : Blo 595291 596531 := bstep (se 1 (by rfl) ⟨447398, by rfl⟩ : syracuseStep 596531 = 894797) B894797
theorem B596547 : Blo 595291 596547 := bstep (se 1 (by rfl) ⟨447410, by rfl⟩ : syracuseStep 596547 = 894821) B894821
theorem B596563 : Blo 595291 596563 := bstep (se 1 (by rfl) ⟨447422, by rfl⟩ : syracuseStep 596563 = 894845) B894845
theorem B596579 : Blo 595291 596579 := bstep (se 1 (by rfl) ⟨447434, by rfl⟩ : syracuseStep 596579 = 894869) B894869
theorem B596595 : Blo 595291 596595 := bstep (se 1 (by rfl) ⟨447446, by rfl⟩ : syracuseStep 596595 = 894893) B894893
theorem B596611 : Blo 595291 596611 := bstep (se 1 (by rfl) ⟨447458, by rfl⟩ : syracuseStep 596611 = 894917) B894917
theorem B596627 : Blo 595291 596627 := bstep (se 1 (by rfl) ⟨447470, by rfl⟩ : syracuseStep 596627 = 894941) B894941
theorem B596643 : Blo 595291 596643 := bstep (se 1 (by rfl) ⟨447482, by rfl⟩ : syracuseStep 596643 = 894965) B894965
theorem B596659 : Blo 595291 596659 := bstep (se 1 (by rfl) ⟨447494, by rfl⟩ : syracuseStep 596659 = 894989) B894989
theorem B596675 : Blo 595291 596675 := bstep (se 1 (by rfl) ⟨447506, by rfl⟩ : syracuseStep 596675 = 895013) B895013
theorem B596691 : Blo 595291 596691 := bstep (se 1 (by rfl) ⟨447518, by rfl⟩ : syracuseStep 596691 = 895037) B895037
theorem B596707 : Blo 595291 596707 := bstep (se 1 (by rfl) ⟨447530, by rfl⟩ : syracuseStep 596707 = 895061) B895061
theorem B596723 : Blo 595291 596723 := bstep (se 1 (by rfl) ⟨447542, by rfl⟩ : syracuseStep 596723 = 895085) B895085
theorem B1907459 : Blo 595291 1907459 := bstep (se 1 (by rfl) ⟨1430594, by rfl⟩ : syracuseStep 1907459 = 2861189) B2861189
theorem B596739 : Blo 595291 596739 := bstep (se 1 (by rfl) ⟨447554, by rfl⟩ : syracuseStep 596739 = 895109) B895109
theorem B596755 : Blo 595291 596755 := bstep (se 1 (by rfl) ⟨447566, by rfl⟩ : syracuseStep 596755 = 895133) B895133
theorem B596771 : Blo 595291 596771 := bstep (se 1 (by rfl) ⟨447578, by rfl⟩ : syracuseStep 596771 = 895157) B895157
theorem B596787 : Blo 595291 596787 := bstep (se 1 (by rfl) ⟨447590, by rfl⟩ : syracuseStep 596787 = 895181) B895181
theorem B596803 : Blo 595291 596803 := bstep (se 1 (by rfl) ⟨447602, by rfl⟩ : syracuseStep 596803 = 895205) B895205
theorem B596819 : Blo 595291 596819 := bstep (se 1 (by rfl) ⟨447614, by rfl⟩ : syracuseStep 596819 = 895229) B895229
theorem B596835 : Blo 595291 596835 := bstep (se 1 (by rfl) ⟨447626, by rfl⟩ : syracuseStep 596835 = 895253) B895253
theorem B596851 : Blo 595291 596851 := bstep (se 1 (by rfl) ⟨447638, by rfl⟩ : syracuseStep 596851 = 895277) B895277
theorem B596867 : Blo 595291 596867 := bstep (se 1 (by rfl) ⟨447650, by rfl⟩ : syracuseStep 596867 = 895301) B895301
theorem B596883 : Blo 595291 596883 := bstep (se 1 (by rfl) ⟨447662, by rfl⟩ : syracuseStep 596883 = 895325) B895325
theorem B596899 : Blo 595291 596899 := bstep (se 1 (by rfl) ⟨447674, by rfl⟩ : syracuseStep 596899 = 895349) B895349
theorem B596915 : Blo 595291 596915 := bstep (se 1 (by rfl) ⟨447686, by rfl⟩ : syracuseStep 596915 = 895373) B895373
theorem B596931 : Blo 595291 596931 := bstep (se 1 (by rfl) ⟨447698, by rfl⟩ : syracuseStep 596931 = 895397) B895397
theorem B596947 : Blo 595291 596947 := bstep (se 1 (by rfl) ⟨447710, by rfl⟩ : syracuseStep 596947 = 895421) B895421
theorem B596963 : Blo 595291 596963 := bstep (se 1 (by rfl) ⟨447722, by rfl⟩ : syracuseStep 596963 = 895445) B895445
theorem B5118947 : Blo 595291 5118947 := bstep (se 1 (by rfl) ⟨3839210, by rfl⟩ : syracuseStep 5118947 = 7678421) B7678421
theorem B2104301 : Blo 595291 2104301 := bstep (se 3 (by rfl) ⟨394556, by rfl⟩ : syracuseStep 2104301 = 789113) B789113
theorem B596979 : Blo 595291 596979 := bstep (se 1 (by rfl) ⟨447734, by rfl⟩ : syracuseStep 596979 = 895469) B895469
theorem B596995 : Blo 595291 596995 := bstep (se 1 (by rfl) ⟨447746, by rfl⟩ : syracuseStep 596995 = 895493) B895493
theorem B597011 : Blo 595291 597011 := bstep (se 1 (by rfl) ⟨447758, by rfl⟩ : syracuseStep 597011 = 895517) B895517
theorem B1612835 : Blo 595291 1612835 := bstep (se 1 (by rfl) ⟨1209626, by rfl⟩ : syracuseStep 1612835 = 2419253) B2419253
theorem B597027 : Blo 595291 597027 := bstep (se 1 (by rfl) ⟨447770, by rfl⟩ : syracuseStep 597027 = 895541) B895541
theorem B597043 : Blo 595291 597043 := bstep (se 1 (by rfl) ⟨447782, by rfl⟩ : syracuseStep 597043 = 895565) B895565
theorem B957491 : Blo 595291 957491 := bstep (se 1 (by rfl) ⟨718118, by rfl⟩ : syracuseStep 957491 = 1436237) B1436237
theorem B597059 : Blo 595291 597059 := bstep (se 1 (by rfl) ⟨447794, by rfl⟩ : syracuseStep 597059 = 895589) B895589
theorem B597075 : Blo 595291 597075 := bstep (se 1 (by rfl) ⟨447806, by rfl⟩ : syracuseStep 597075 = 895613) B895613
theorem B597091 : Blo 595291 597091 := bstep (se 1 (by rfl) ⟨447818, by rfl⟩ : syracuseStep 597091 = 895637) B895637
theorem B1514609 : Blo 595291 1514609 := bstep (se 2 (by rfl) ⟨567978, by rfl⟩ : syracuseStep 1514609 = 1135957) B1135957
theorem B597107 : Blo 595291 597107 := bstep (se 1 (by rfl) ⟨447830, by rfl⟩ : syracuseStep 597107 = 895661) B895661
theorem B597123 : Blo 595291 597123 := bstep (se 1 (by rfl) ⟨447842, by rfl⟩ : syracuseStep 597123 = 895685) B895685
theorem B597139 : Blo 595291 597139 := bstep (se 1 (by rfl) ⟨447854, by rfl⟩ : syracuseStep 597139 = 895709) B895709
theorem B597155 : Blo 595291 597155 := bstep (se 1 (by rfl) ⟨447866, by rfl⟩ : syracuseStep 597155 = 895733) B895733
theorem B1514659 : Blo 595291 1514659 := bstep (se 1 (by rfl) ⟨1135994, by rfl⟩ : syracuseStep 1514659 = 2271989) B2271989
theorem B597171 : Blo 595291 597171 := bstep (se 1 (by rfl) ⟨447878, by rfl⟩ : syracuseStep 597171 = 895757) B895757
theorem B597187 : Blo 595291 597187 := bstep (se 1 (by rfl) ⟨447890, by rfl⟩ : syracuseStep 597187 = 895781) B895781
theorem B597203 : Blo 595291 597203 := bstep (se 1 (by rfl) ⟨447902, by rfl⟩ : syracuseStep 597203 = 895805) B895805
theorem B597219 : Blo 595291 597219 := bstep (se 1 (by rfl) ⟨447914, by rfl⟩ : syracuseStep 597219 = 895829) B895829
theorem B597235 : Blo 595291 597235 := bstep (se 1 (by rfl) ⟨447926, by rfl⟩ : syracuseStep 597235 = 895853) B895853
theorem B597251 : Blo 595291 597251 := bstep (se 1 (by rfl) ⟨447938, by rfl⟩ : syracuseStep 597251 = 895877) B895877
theorem B597267 : Blo 595291 597267 := bstep (se 1 (by rfl) ⟨447950, by rfl⟩ : syracuseStep 597267 = 895901) B895901
theorem B597283 : Blo 595291 597283 := bstep (se 1 (by rfl) ⟨447962, by rfl⟩ : syracuseStep 597283 = 895925) B895925
theorem B1514801 : Blo 595291 1514801 := bstep (se 2 (by rfl) ⟨568050, by rfl⟩ : syracuseStep 1514801 = 1136101) B1136101
theorem B597299 : Blo 595291 597299 := bstep (se 1 (by rfl) ⟨447974, by rfl⟩ : syracuseStep 597299 = 895949) B895949
theorem B597315 : Blo 595291 597315 := bstep (se 1 (by rfl) ⟨447986, by rfl⟩ : syracuseStep 597315 = 895973) B895973
theorem B597331 : Blo 595291 597331 := bstep (se 1 (by rfl) ⟨447998, by rfl⟩ : syracuseStep 597331 = 895997) B895997
theorem B597347 : Blo 595291 597347 := bstep (se 1 (by rfl) ⟨448010, by rfl⟩ : syracuseStep 597347 = 896021) B896021
theorem B597363 : Blo 595291 597363 := bstep (se 1 (by rfl) ⟨448022, by rfl⟩ : syracuseStep 597363 = 896045) B896045
theorem B597379 : Blo 595291 597379 := bstep (se 1 (by rfl) ⟨448034, by rfl⟩ : syracuseStep 597379 = 896069) B896069
theorem B2268557 : Blo 595291 2268557 := bstep (se 3 (by rfl) ⟨425354, by rfl⟩ : syracuseStep 2268557 = 850709) B850709
theorem B597395 : Blo 595291 597395 := bstep (se 1 (by rfl) ⟨448046, by rfl⟩ : syracuseStep 597395 = 896093) B896093
theorem B597411 : Blo 595291 597411 := bstep (se 1 (by rfl) ⟨448058, by rfl⟩ : syracuseStep 597411 = 896117) B896117
theorem B597427 : Blo 595291 597427 := bstep (se 1 (by rfl) ⟨448070, by rfl⟩ : syracuseStep 597427 = 896141) B896141
theorem B597443 : Blo 595291 597443 := bstep (se 1 (by rfl) ⟨448082, by rfl⟩ : syracuseStep 597443 = 896165) B896165
theorem B597459 : Blo 595291 597459 := bstep (se 1 (by rfl) ⟨448094, by rfl⟩ : syracuseStep 597459 = 896189) B896189
theorem B597475 : Blo 595291 597475 := bstep (se 1 (by rfl) ⟨448106, by rfl⟩ : syracuseStep 597475 = 896213) B896213
theorem B597491 : Blo 595291 597491 := bstep (se 1 (by rfl) ⟨448118, by rfl⟩ : syracuseStep 597491 = 896237) B896237
theorem B597507 : Blo 595291 597507 := bstep (se 1 (by rfl) ⟨448130, by rfl⟩ : syracuseStep 597507 = 896261) B896261
theorem B597523 : Blo 595291 597523 := bstep (se 1 (by rfl) ⟨448142, by rfl⟩ : syracuseStep 597523 = 896285) B896285
theorem B597539 : Blo 595291 597539 := bstep (se 1 (by rfl) ⟨448154, by rfl⟩ : syracuseStep 597539 = 896309) B896309
theorem B597555 : Blo 595291 597555 := bstep (se 1 (by rfl) ⟨448166, by rfl⟩ : syracuseStep 597555 = 896333) B896333
theorem B597571 : Blo 595291 597571 := bstep (se 1 (by rfl) ⟨448178, by rfl⟩ : syracuseStep 597571 = 896357) B896357
theorem B2760269 : Blo 595291 2760269 := bstep (se 3 (by rfl) ⟨517550, by rfl⟩ : syracuseStep 2760269 = 1035101) B1035101
theorem B597587 : Blo 595291 597587 := bstep (se 1 (by rfl) ⟨448190, by rfl⟩ : syracuseStep 597587 = 896381) B896381
theorem B597603 : Blo 595291 597603 := bstep (se 1 (by rfl) ⟨448202, by rfl⟩ : syracuseStep 597603 = 896405) B896405
theorem B597619 : Blo 595291 597619 := bstep (se 1 (by rfl) ⟨448214, by rfl⟩ : syracuseStep 597619 = 896429) B896429
theorem B1908355 : Blo 595291 1908355 := bstep (se 1 (by rfl) ⟨1431266, by rfl⟩ : syracuseStep 1908355 = 2862533) B2862533
theorem B597635 : Blo 595291 597635 := bstep (se 1 (by rfl) ⟨448226, by rfl⟩ : syracuseStep 597635 = 896453) B896453
theorem B597651 : Blo 595291 597651 := bstep (se 1 (by rfl) ⟨448238, by rfl⟩ : syracuseStep 597651 = 896477) B896477
theorem B597667 : Blo 595291 597667 := bstep (se 1 (by rfl) ⟨448250, by rfl⟩ : syracuseStep 597667 = 896501) B896501
theorem B597683 : Blo 595291 597683 := bstep (se 1 (by rfl) ⟨448262, by rfl⟩ : syracuseStep 597683 = 896525) B896525
theorem B597699 : Blo 595291 597699 := bstep (se 1 (by rfl) ⟨448274, by rfl⟩ : syracuseStep 597699 = 896549) B896549
theorem B597715 : Blo 595291 597715 := bstep (se 1 (by rfl) ⟨448286, by rfl⟩ : syracuseStep 597715 = 896573) B896573
theorem B597731 : Blo 595291 597731 := bstep (se 1 (by rfl) ⟨448298, by rfl⟩ : syracuseStep 597731 = 896597) B896597
theorem B597747 : Blo 595291 597747 := bstep (se 1 (by rfl) ⟨448310, by rfl⟩ : syracuseStep 597747 = 896621) B896621
theorem B597763 : Blo 595291 597763 := bstep (se 1 (by rfl) ⟨448322, by rfl⟩ : syracuseStep 597763 = 896645) B896645
theorem B597779 : Blo 595291 597779 := bstep (se 1 (by rfl) ⟨448334, by rfl⟩ : syracuseStep 597779 = 896669) B896669
theorem B597795 : Blo 595291 597795 := bstep (se 1 (by rfl) ⟨448346, by rfl⟩ : syracuseStep 597795 = 896693) B896693
theorem B597811 : Blo 595291 597811 := bstep (se 1 (by rfl) ⟨448358, by rfl⟩ : syracuseStep 597811 = 896717) B896717
theorem B597827 : Blo 595291 597827 := bstep (se 1 (by rfl) ⟨448370, by rfl⟩ : syracuseStep 597827 = 896741) B896741
theorem B597843 : Blo 595291 597843 := bstep (se 1 (by rfl) ⟨448382, by rfl⟩ : syracuseStep 597843 = 896765) B896765
theorem B597859 : Blo 595291 597859 := bstep (se 1 (by rfl) ⟨448394, by rfl⟩ : syracuseStep 597859 = 896789) B896789
theorem B597875 : Blo 595291 597875 := bstep (se 1 (by rfl) ⟨448406, by rfl⟩ : syracuseStep 597875 = 896813) B896813
theorem B597891 : Blo 595291 597891 := bstep (se 1 (by rfl) ⟨448418, by rfl⟩ : syracuseStep 597891 = 896837) B896837
theorem B597907 : Blo 595291 597907 := bstep (se 1 (by rfl) ⟨448430, by rfl⟩ : syracuseStep 597907 = 896861) B896861
theorem B597923 : Blo 595291 597923 := bstep (se 1 (by rfl) ⟨448442, by rfl⟩ : syracuseStep 597923 = 896885) B896885
theorem B597939 : Blo 595291 597939 := bstep (se 1 (by rfl) ⟨448454, by rfl⟩ : syracuseStep 597939 = 896909) B896909
theorem B597955 : Blo 595291 597955 := bstep (se 1 (by rfl) ⟨448466, by rfl⟩ : syracuseStep 597955 = 896933) B896933
theorem B597971 : Blo 595291 597971 := bstep (se 1 (by rfl) ⟨448478, by rfl⟩ : syracuseStep 597971 = 896957) B896957
theorem B597987 : Blo 595291 597987 := bstep (se 1 (by rfl) ⟨448490, by rfl⟩ : syracuseStep 597987 = 896981) B896981
theorem B598003 : Blo 595291 598003 := bstep (se 1 (by rfl) ⟨448502, by rfl⟩ : syracuseStep 598003 = 897005) B897005
theorem B598019 : Blo 595291 598019 := bstep (se 1 (by rfl) ⟨448514, by rfl⟩ : syracuseStep 598019 = 897029) B897029
theorem B598035 : Blo 595291 598035 := bstep (se 1 (by rfl) ⟨448526, by rfl⟩ : syracuseStep 598035 = 897053) B897053
theorem B958483 : Blo 595291 958483 := bstep (se 1 (by rfl) ⟨718862, by rfl⟩ : syracuseStep 958483 = 1437725) B1437725
theorem B892961 : Blo 595291 892961 := bstep (se 2 (by rfl) ⟨334860, by rfl⟩ : syracuseStep 892961 = 669721) B669721
theorem B598051 : Blo 595291 598051 := bstep (se 1 (by rfl) ⟨448538, by rfl⟩ : syracuseStep 598051 = 897077) B897077
theorem B892979 : Blo 595291 892979 := bstep (se 1 (by rfl) ⟨669734, by rfl⟩ : syracuseStep 892979 = 1339469) B1339469
theorem B598067 : Blo 595291 598067 := bstep (se 1 (by rfl) ⟨448550, by rfl⟩ : syracuseStep 598067 = 897101) B897101
theorem B598083 : Blo 595291 598083 := bstep (se 1 (by rfl) ⟨448562, by rfl⟩ : syracuseStep 598083 = 897125) B897125
theorem B893009 : Blo 595291 893009 := bstep (se 2 (by rfl) ⟨334878, by rfl⟩ : syracuseStep 893009 = 669757) B669757
theorem B598099 : Blo 595291 598099 := bstep (se 1 (by rfl) ⟨448574, by rfl⟩ : syracuseStep 598099 = 897149) B897149
theorem B893027 : Blo 595291 893027 := bstep (se 1 (by rfl) ⟨669770, by rfl⟩ : syracuseStep 893027 = 1339541) B1339541
theorem B598115 : Blo 595291 598115 := bstep (se 1 (by rfl) ⟨448586, by rfl⟩ : syracuseStep 598115 = 897173) B897173
theorem B598131 : Blo 595291 598131 := bstep (se 1 (by rfl) ⟨448598, by rfl⟩ : syracuseStep 598131 = 897197) B897197
theorem B893057 : Blo 595291 893057 := bstep (se 2 (by rfl) ⟨334896, by rfl⟩ : syracuseStep 893057 = 669793) B669793
theorem B598147 : Blo 595291 598147 := bstep (se 1 (by rfl) ⟨448610, by rfl⟩ : syracuseStep 598147 = 897221) B897221
theorem B893075 : Blo 595291 893075 := bstep (se 1 (by rfl) ⟨669806, by rfl⟩ : syracuseStep 893075 = 1339613) B1339613
theorem B598163 : Blo 595291 598163 := bstep (se 1 (by rfl) ⟨448622, by rfl⟩ : syracuseStep 598163 = 897245) B897245
theorem B598179 : Blo 595291 598179 := bstep (se 1 (by rfl) ⟨448634, by rfl⟩ : syracuseStep 598179 = 897269) B897269
theorem B893105 : Blo 595291 893105 := bstep (se 2 (by rfl) ⟨334914, by rfl⟩ : syracuseStep 893105 = 669829) B669829
theorem B598195 : Blo 595291 598195 := bstep (se 1 (by rfl) ⟨448646, by rfl⟩ : syracuseStep 598195 = 897293) B897293
theorem B893123 : Blo 595291 893123 := bstep (se 1 (by rfl) ⟨669842, by rfl⟩ : syracuseStep 893123 = 1339685) B1339685
theorem B10887365 : Blo 595291 10887365 := bstep (se 4 (by rfl) ⟨1020690, by rfl⟩ : syracuseStep 10887365 = 2041381) B2041381
theorem B598211 : Blo 595291 598211 := bstep (se 1 (by rfl) ⟨448658, by rfl⟩ : syracuseStep 598211 = 897317) B897317
theorem B598227 : Blo 595291 598227 := bstep (se 1 (by rfl) ⟨448670, by rfl⟩ : syracuseStep 598227 = 897341) B897341
theorem B893153 : Blo 595291 893153 := bstep (se 2 (by rfl) ⟨334932, by rfl⟩ : syracuseStep 893153 = 669865) B669865
theorem B598243 : Blo 595291 598243 := bstep (se 1 (by rfl) ⟨448682, by rfl⟩ : syracuseStep 598243 = 897365) B897365
theorem B893171 : Blo 595291 893171 := bstep (se 1 (by rfl) ⟨669878, by rfl⟩ : syracuseStep 893171 = 1339757) B1339757
theorem B598259 : Blo 595291 598259 := bstep (se 1 (by rfl) ⟨448694, by rfl⟩ : syracuseStep 598259 = 897389) B897389
theorem B598275 : Blo 595291 598275 := bstep (se 1 (by rfl) ⟨448706, by rfl⟩ : syracuseStep 598275 = 897413) B897413
theorem B893201 : Blo 595291 893201 := bstep (se 2 (by rfl) ⟨334950, by rfl⟩ : syracuseStep 893201 = 669901) B669901
theorem B1515793 : Blo 595291 1515793 := bstep (se 2 (by rfl) ⟨568422, by rfl⟩ : syracuseStep 1515793 = 1136845) B1136845
theorem B598291 : Blo 595291 598291 := bstep (se 1 (by rfl) ⟨448718, by rfl⟩ : syracuseStep 598291 = 897437) B897437
theorem B893219 : Blo 595291 893219 := bstep (se 1 (by rfl) ⟨669914, by rfl⟩ : syracuseStep 893219 = 1339829) B1339829
theorem B598307 : Blo 595291 598307 := bstep (se 1 (by rfl) ⟨448730, by rfl⟩ : syracuseStep 598307 = 897461) B897461
theorem B598323 : Blo 595291 598323 := bstep (se 1 (by rfl) ⟨448742, by rfl⟩ : syracuseStep 598323 = 897485) B897485
theorem B893249 : Blo 595291 893249 := bstep (se 2 (by rfl) ⟨334968, by rfl⟩ : syracuseStep 893249 = 669937) B669937
theorem B598339 : Blo 595291 598339 := bstep (se 1 (by rfl) ⟨448754, by rfl⟩ : syracuseStep 598339 = 897509) B897509
theorem B893267 : Blo 595291 893267 := bstep (se 1 (by rfl) ⟨669950, by rfl⟩ : syracuseStep 893267 = 1339901) B1339901
theorem B598355 : Blo 595291 598355 := bstep (se 1 (by rfl) ⟨448766, by rfl⟩ : syracuseStep 598355 = 897533) B897533
theorem B598371 : Blo 595291 598371 := bstep (se 1 (by rfl) ⟨448778, by rfl⟩ : syracuseStep 598371 = 897557) B897557
theorem B893297 : Blo 595291 893297 := bstep (se 2 (by rfl) ⟨334986, by rfl⟩ : syracuseStep 893297 = 669973) B669973
theorem B598387 : Blo 595291 598387 := bstep (se 1 (by rfl) ⟨448790, by rfl⟩ : syracuseStep 598387 = 897581) B897581
theorem B893315 : Blo 595291 893315 := bstep (se 1 (by rfl) ⟨669986, by rfl⟩ : syracuseStep 893315 = 1339973) B1339973
theorem B598403 : Blo 595291 598403 := bstep (se 1 (by rfl) ⟨448802, by rfl⟩ : syracuseStep 598403 = 897605) B897605
theorem B1810829 : Blo 595291 1810829 := bstep (se 3 (by rfl) ⟨339530, by rfl⟩ : syracuseStep 1810829 = 679061) B679061
theorem B598419 : Blo 595291 598419 := bstep (se 1 (by rfl) ⟨448814, by rfl⟩ : syracuseStep 598419 = 897629) B897629
theorem B893345 : Blo 595291 893345 := bstep (se 2 (by rfl) ⟨335004, by rfl⟩ : syracuseStep 893345 = 670009) B670009
theorem B598435 : Blo 595291 598435 := bstep (se 1 (by rfl) ⟨448826, by rfl⟩ : syracuseStep 598435 = 897653) B897653
theorem B893363 : Blo 595291 893363 := bstep (se 1 (by rfl) ⟨670022, by rfl⟩ : syracuseStep 893363 = 1340045) B1340045
theorem B598451 : Blo 595291 598451 := bstep (se 1 (by rfl) ⟨448838, by rfl⟩ : syracuseStep 598451 = 897677) B897677
theorem B598467 : Blo 595291 598467 := bstep (se 1 (by rfl) ⟨448850, by rfl⟩ : syracuseStep 598467 = 897701) B897701
theorem B893393 : Blo 595291 893393 := bstep (se 2 (by rfl) ⟨335022, by rfl⟩ : syracuseStep 893393 = 670045) B670045
theorem B598483 : Blo 595291 598483 := bstep (se 1 (by rfl) ⟨448862, by rfl⟩ : syracuseStep 598483 = 897725) B897725
theorem B893411 : Blo 595291 893411 := bstep (se 1 (by rfl) ⟨670058, by rfl⟩ : syracuseStep 893411 = 1340117) B1340117
theorem B598499 : Blo 595291 598499 := bstep (se 1 (by rfl) ⟨448874, by rfl⟩ : syracuseStep 598499 = 897749) B897749
theorem B598515 : Blo 595291 598515 := bstep (se 1 (by rfl) ⟨448886, by rfl⟩ : syracuseStep 598515 = 897773) B897773
theorem B893441 : Blo 595291 893441 := bstep (se 2 (by rfl) ⟨335040, by rfl⟩ : syracuseStep 893441 = 670081) B670081
theorem B598531 : Blo 595291 598531 := bstep (se 1 (by rfl) ⟨448898, by rfl⟩ : syracuseStep 598531 = 897797) B897797
theorem B893459 : Blo 595291 893459 := bstep (se 1 (by rfl) ⟨670094, by rfl⟩ : syracuseStep 893459 = 1340189) B1340189
theorem B598547 : Blo 595291 598547 := bstep (se 1 (by rfl) ⟨448910, by rfl⟩ : syracuseStep 598547 = 897821) B897821
theorem B598563 : Blo 595291 598563 := bstep (se 1 (by rfl) ⟨448922, by rfl⟩ : syracuseStep 598563 = 897845) B897845
theorem B1516067 : Blo 595291 1516067 := bstep (se 1 (by rfl) ⟨1137050, by rfl⟩ : syracuseStep 1516067 = 2274101) B2274101
theorem B893489 : Blo 595291 893489 := bstep (se 2 (by rfl) ⟨335058, by rfl⟩ : syracuseStep 893489 = 670117) B670117
theorem B598579 : Blo 595291 598579 := bstep (se 1 (by rfl) ⟨448934, by rfl⟩ : syracuseStep 598579 = 897869) B897869
theorem B893507 : Blo 595291 893507 := bstep (se 1 (by rfl) ⟨670130, by rfl⟩ : syracuseStep 893507 = 1340261) B1340261
theorem B598595 : Blo 595291 598595 := bstep (se 1 (by rfl) ⟨448946, by rfl⟩ : syracuseStep 598595 = 897893) B897893
theorem B598611 : Blo 595291 598611 := bstep (se 1 (by rfl) ⟨448958, by rfl⟩ : syracuseStep 598611 = 897917) B897917
theorem B893537 : Blo 595291 893537 := bstep (se 2 (by rfl) ⟨335076, by rfl⟩ : syracuseStep 893537 = 670153) B670153
theorem B598627 : Blo 595291 598627 := bstep (se 1 (by rfl) ⟨448970, by rfl⟩ : syracuseStep 598627 = 897941) B897941
theorem B893555 : Blo 595291 893555 := bstep (se 1 (by rfl) ⟨670166, by rfl⟩ : syracuseStep 893555 = 1340333) B1340333
theorem B598643 : Blo 595291 598643 := bstep (se 1 (by rfl) ⟨448982, by rfl⟩ : syracuseStep 598643 = 897965) B897965
theorem B598659 : Blo 595291 598659 := bstep (se 1 (by rfl) ⟨448994, by rfl⟩ : syracuseStep 598659 = 897989) B897989
theorem B893585 : Blo 595291 893585 := bstep (se 2 (by rfl) ⟨335094, by rfl⟩ : syracuseStep 893585 = 670189) B670189
theorem B598675 : Blo 595291 598675 := bstep (se 1 (by rfl) ⟨449006, by rfl⟩ : syracuseStep 598675 = 898013) B898013
theorem B893603 : Blo 595291 893603 := bstep (se 1 (by rfl) ⟨670202, by rfl⟩ : syracuseStep 893603 = 1340405) B1340405
theorem B598691 : Blo 595291 598691 := bstep (se 1 (by rfl) ⟨449018, by rfl⟩ : syracuseStep 598691 = 898037) B898037
theorem B598707 : Blo 595291 598707 := bstep (se 1 (by rfl) ⟨449030, by rfl⟩ : syracuseStep 598707 = 898061) B898061
theorem B893633 : Blo 595291 893633 := bstep (se 2 (by rfl) ⟨335112, by rfl⟩ : syracuseStep 893633 = 670225) B670225
theorem B598723 : Blo 595291 598723 := bstep (se 1 (by rfl) ⟨449042, by rfl⟩ : syracuseStep 598723 = 898085) B898085
theorem B1909457 : Blo 595291 1909457 := bstep (se 2 (by rfl) ⟨716046, by rfl⟩ : syracuseStep 1909457 = 1432093) B1432093
theorem B893651 : Blo 595291 893651 := bstep (se 1 (by rfl) ⟨670238, by rfl⟩ : syracuseStep 893651 = 1340477) B1340477
theorem B598739 : Blo 595291 598739 := bstep (se 1 (by rfl) ⟨449054, by rfl⟩ : syracuseStep 598739 = 898109) B898109
theorem B598755 : Blo 595291 598755 := bstep (se 1 (by rfl) ⟨449066, by rfl⟩ : syracuseStep 598755 = 898133) B898133
theorem B1516259 : Blo 595291 1516259 := bstep (se 1 (by rfl) ⟨1137194, by rfl⟩ : syracuseStep 1516259 = 2274389) B2274389
theorem B893681 : Blo 595291 893681 := bstep (se 2 (by rfl) ⟨335130, by rfl⟩ : syracuseStep 893681 = 670261) B670261
theorem B598771 : Blo 595291 598771 := bstep (se 1 (by rfl) ⟨449078, by rfl⟩ : syracuseStep 598771 = 898157) B898157
theorem B893699 : Blo 595291 893699 := bstep (se 1 (by rfl) ⟨670274, by rfl⟩ : syracuseStep 893699 = 1340549) B1340549
theorem B598787 : Blo 595291 598787 := bstep (se 1 (by rfl) ⟨449090, by rfl⟩ : syracuseStep 598787 = 898181) B898181
theorem B598803 : Blo 595291 598803 := bstep (se 1 (by rfl) ⟨449102, by rfl⟩ : syracuseStep 598803 = 898205) B898205
theorem B893729 : Blo 595291 893729 := bstep (se 2 (by rfl) ⟨335148, by rfl⟩ : syracuseStep 893729 = 670297) B670297
theorem B598819 : Blo 595291 598819 := bstep (se 1 (by rfl) ⟨449114, by rfl⟩ : syracuseStep 598819 = 898229) B898229
theorem B893747 : Blo 595291 893747 := bstep (se 1 (by rfl) ⟨670310, by rfl⟩ : syracuseStep 893747 = 1340621) B1340621
theorem B598835 : Blo 595291 598835 := bstep (se 1 (by rfl) ⟨449126, by rfl⟩ : syracuseStep 598835 = 898253) B898253
theorem B598851 : Blo 595291 598851 := bstep (se 1 (by rfl) ⟨449138, by rfl⟩ : syracuseStep 598851 = 898277) B898277
theorem B893777 : Blo 595291 893777 := bstep (se 2 (by rfl) ⟨335166, by rfl⟩ : syracuseStep 893777 = 670333) B670333
theorem B1909585 : Blo 595291 1909585 := bstep (se 2 (by rfl) ⟨716094, by rfl⟩ : syracuseStep 1909585 = 1432189) B1432189
theorem B598867 : Blo 595291 598867 := bstep (se 1 (by rfl) ⟨449150, by rfl⟩ : syracuseStep 598867 = 898301) B898301
theorem B893795 : Blo 595291 893795 := bstep (se 1 (by rfl) ⟨670346, by rfl⟩ : syracuseStep 893795 = 1340693) B1340693
theorem B598883 : Blo 595291 598883 := bstep (se 1 (by rfl) ⟨449162, by rfl⟩ : syracuseStep 598883 = 898325) B898325
theorem B3023729 : Blo 595291 3023729 := bstep (se 2 (by rfl) ⟨1133898, by rfl⟩ : syracuseStep 3023729 = 2267797) B2267797
theorem B598899 : Blo 595291 598899 := bstep (se 1 (by rfl) ⟨449174, by rfl⟩ : syracuseStep 598899 = 898349) B898349
theorem B893825 : Blo 595291 893825 := bstep (se 2 (by rfl) ⟨335184, by rfl⟩ : syracuseStep 893825 = 670369) B670369
theorem B598915 : Blo 595291 598915 := bstep (se 1 (by rfl) ⟨449186, by rfl⟩ : syracuseStep 598915 = 898373) B898373
theorem B893843 : Blo 595291 893843 := bstep (se 1 (by rfl) ⟨670382, by rfl⟩ : syracuseStep 893843 = 1340765) B1340765
theorem B598931 : Blo 595291 598931 := bstep (se 1 (by rfl) ⟨449198, by rfl⟩ : syracuseStep 598931 = 898397) B898397
theorem B959393 : Blo 595291 959393 := bstep (se 2 (by rfl) ⟨359772, by rfl⟩ : syracuseStep 959393 = 719545) B719545
theorem B598947 : Blo 595291 598947 := bstep (se 1 (by rfl) ⟨449210, by rfl⟩ : syracuseStep 598947 = 898421) B898421
theorem B893873 : Blo 595291 893873 := bstep (se 2 (by rfl) ⟨335202, by rfl⟩ : syracuseStep 893873 = 670405) B670405
theorem B598963 : Blo 595291 598963 := bstep (se 1 (by rfl) ⟨449222, by rfl⟩ : syracuseStep 598963 = 898445) B898445
theorem B893891 : Blo 595291 893891 := bstep (se 1 (by rfl) ⟨670418, by rfl⟩ : syracuseStep 893891 = 1340837) B1340837
theorem B598979 : Blo 595291 598979 := bstep (se 1 (by rfl) ⟨449234, by rfl⟩ : syracuseStep 598979 = 898469) B898469
theorem B598995 : Blo 595291 598995 := bstep (se 1 (by rfl) ⟨449246, by rfl⟩ : syracuseStep 598995 = 898493) B898493
theorem B893921 : Blo 595291 893921 := bstep (se 2 (by rfl) ⟨335220, by rfl⟩ : syracuseStep 893921 = 670441) B670441
theorem B599011 : Blo 595291 599011 := bstep (se 1 (by rfl) ⟨449258, by rfl⟩ : syracuseStep 599011 = 898517) B898517
theorem B893939 : Blo 595291 893939 := bstep (se 1 (by rfl) ⟨670454, by rfl⟩ : syracuseStep 893939 = 1340909) B1340909
theorem B599027 : Blo 595291 599027 := bstep (se 1 (by rfl) ⟨449270, by rfl⟩ : syracuseStep 599027 = 898541) B898541
theorem B599043 : Blo 595291 599043 := bstep (se 1 (by rfl) ⟨449282, by rfl⟩ : syracuseStep 599043 = 898565) B898565
theorem B893969 : Blo 595291 893969 := bstep (se 2 (by rfl) ⟨335238, by rfl⟩ : syracuseStep 893969 = 670477) B670477
theorem B599059 : Blo 595291 599059 := bstep (se 1 (by rfl) ⟨449294, by rfl⟩ : syracuseStep 599059 = 898589) B898589
theorem B959521 : Blo 595291 959521 := bstep (se 2 (by rfl) ⟨359820, by rfl⟩ : syracuseStep 959521 = 719641) B719641
theorem B893987 : Blo 595291 893987 := bstep (se 1 (by rfl) ⟨670490, by rfl⟩ : syracuseStep 893987 = 1340981) B1340981
theorem B599075 : Blo 595291 599075 := bstep (se 1 (by rfl) ⟨449306, by rfl⟩ : syracuseStep 599075 = 898613) B898613
theorem B599091 : Blo 595291 599091 := bstep (se 1 (by rfl) ⟨449318, by rfl⟩ : syracuseStep 599091 = 898637) B898637
theorem B894017 : Blo 595291 894017 := bstep (se 2 (by rfl) ⟨335256, by rfl⟩ : syracuseStep 894017 = 670513) B670513
theorem B599107 : Blo 595291 599107 := bstep (se 1 (by rfl) ⟨449330, by rfl⟩ : syracuseStep 599107 = 898661) B898661
theorem B894035 : Blo 595291 894035 := bstep (se 1 (by rfl) ⟨670526, by rfl⟩ : syracuseStep 894035 = 1341053) B1341053
theorem B599123 : Blo 595291 599123 := bstep (se 1 (by rfl) ⟨449342, by rfl⟩ : syracuseStep 599123 = 898685) B898685
theorem B599139 : Blo 595291 599139 := bstep (se 1 (by rfl) ⟨449354, by rfl⟩ : syracuseStep 599139 = 898709) B898709
theorem B894065 : Blo 595291 894065 := bstep (se 2 (by rfl) ⟨335274, by rfl⟩ : syracuseStep 894065 = 670549) B670549
theorem B599155 : Blo 595291 599155 := bstep (se 1 (by rfl) ⟨449366, by rfl⟩ : syracuseStep 599155 = 898733) B898733
theorem B894083 : Blo 595291 894083 := bstep (se 1 (by rfl) ⟨670562, by rfl⟩ : syracuseStep 894083 = 1341125) B1341125
theorem B599171 : Blo 595291 599171 := bstep (se 1 (by rfl) ⟨449378, by rfl⟩ : syracuseStep 599171 = 898757) B898757
theorem B599187 : Blo 595291 599187 := bstep (se 1 (by rfl) ⟨449390, by rfl⟩ : syracuseStep 599187 = 898781) B898781
theorem B894113 : Blo 595291 894113 := bstep (se 2 (by rfl) ⟨335292, by rfl⟩ : syracuseStep 894113 = 670585) B670585
theorem B599203 : Blo 595291 599203 := bstep (se 1 (by rfl) ⟨449402, by rfl⟩ : syracuseStep 599203 = 898805) B898805
theorem B894131 : Blo 595291 894131 := bstep (se 1 (by rfl) ⟨670598, by rfl⟩ : syracuseStep 894131 = 1341197) B1341197
theorem B599219 : Blo 595291 599219 := bstep (se 1 (by rfl) ⟨449414, by rfl⟩ : syracuseStep 599219 = 898829) B898829
theorem B599235 : Blo 595291 599235 := bstep (se 1 (by rfl) ⟨449426, by rfl⟩ : syracuseStep 599235 = 898853) B898853
theorem B894161 : Blo 595291 894161 := bstep (se 2 (by rfl) ⟨335310, by rfl⟩ : syracuseStep 894161 = 670621) B670621
theorem B599251 : Blo 595291 599251 := bstep (se 1 (by rfl) ⟨449438, by rfl⟩ : syracuseStep 599251 = 898877) B898877
theorem B894179 : Blo 595291 894179 := bstep (se 1 (by rfl) ⟨670634, by rfl⟩ : syracuseStep 894179 = 1341269) B1341269
theorem B599267 : Blo 595291 599267 := bstep (se 1 (by rfl) ⟨449450, by rfl⟩ : syracuseStep 599267 = 898901) B898901
theorem B599283 : Blo 595291 599283 := bstep (se 1 (by rfl) ⟨449462, by rfl⟩ : syracuseStep 599283 = 898925) B898925
theorem B894209 : Blo 595291 894209 := bstep (se 2 (by rfl) ⟨335328, by rfl⟩ : syracuseStep 894209 = 670657) B670657
theorem B894227 : Blo 595291 894227 := bstep (se 1 (by rfl) ⟨670670, by rfl⟩ : syracuseStep 894227 = 1341341) B1341341
theorem B894257 : Blo 595291 894257 := bstep (se 2 (by rfl) ⟨335346, by rfl⟩ : syracuseStep 894257 = 670693) B670693
theorem B894275 : Blo 595291 894275 := bstep (se 1 (by rfl) ⟨670706, by rfl⟩ : syracuseStep 894275 = 1341413) B1341413
theorem B894305 : Blo 595291 894305 := bstep (se 2 (by rfl) ⟨335364, by rfl⟩ : syracuseStep 894305 = 670729) B670729
theorem B894323 : Blo 595291 894323 := bstep (se 1 (by rfl) ⟨670742, by rfl⟩ : syracuseStep 894323 = 1341485) B1341485
theorem B894353 : Blo 595291 894353 := bstep (se 2 (by rfl) ⟨335382, by rfl⟩ : syracuseStep 894353 = 670765) B670765
theorem B894371 : Blo 595291 894371 := bstep (se 1 (by rfl) ⟨670778, by rfl⟩ : syracuseStep 894371 = 1341557) B1341557
theorem B894401 : Blo 595291 894401 := bstep (se 2 (by rfl) ⟨335400, by rfl⟩ : syracuseStep 894401 = 670801) B670801
theorem B894419 : Blo 595291 894419 := bstep (se 1 (by rfl) ⟨670814, by rfl⟩ : syracuseStep 894419 = 1341629) B1341629
theorem B894449 : Blo 595291 894449 := bstep (se 2 (by rfl) ⟨335418, by rfl⟩ : syracuseStep 894449 = 670837) B670837
theorem B894467 : Blo 595291 894467 := bstep (se 1 (by rfl) ⟨670850, by rfl⟩ : syracuseStep 894467 = 1341701) B1341701
theorem B894497 : Blo 595291 894497 := bstep (se 2 (by rfl) ⟨335436, by rfl⟩ : syracuseStep 894497 = 670873) B670873
theorem B3221041 : Blo 595291 3221041 := bstep (se 2 (by rfl) ⟨1207890, by rfl⟩ : syracuseStep 3221041 = 2415781) B2415781
theorem B894515 : Blo 595291 894515 := bstep (se 1 (by rfl) ⟨670886, by rfl⟩ : syracuseStep 894515 = 1341773) B1341773
theorem B894545 : Blo 595291 894545 := bstep (se 2 (by rfl) ⟨335454, by rfl⟩ : syracuseStep 894545 = 670909) B670909
theorem B894563 : Blo 595291 894563 := bstep (se 1 (by rfl) ⟨670922, by rfl⟩ : syracuseStep 894563 = 1341845) B1341845
theorem B894593 : Blo 595291 894593 := bstep (se 2 (by rfl) ⟨335472, by rfl⟩ : syracuseStep 894593 = 670945) B670945
theorem B894611 : Blo 595291 894611 := bstep (se 1 (by rfl) ⟨670958, by rfl⟩ : syracuseStep 894611 = 1341917) B1341917
theorem B894641 : Blo 595291 894641 := bstep (se 2 (by rfl) ⟨335490, by rfl⟩ : syracuseStep 894641 = 670981) B670981
theorem B894659 : Blo 595291 894659 := bstep (se 1 (by rfl) ⟨670994, by rfl⟩ : syracuseStep 894659 = 1341989) B1341989
theorem B894689 : Blo 595291 894689 := bstep (se 2 (by rfl) ⟨335508, by rfl⟩ : syracuseStep 894689 = 671017) B671017
theorem B2074339 : Blo 595291 2074339 := bstep (se 1 (by rfl) ⟨1555754, by rfl⟩ : syracuseStep 2074339 = 3111509) B3111509
theorem B2303729 : Blo 595291 2303729 := bstep (se 2 (by rfl) ⟨863898, by rfl⟩ : syracuseStep 2303729 = 1727797) B1727797
theorem B894707 : Blo 595291 894707 := bstep (se 1 (by rfl) ⟨671030, by rfl⟩ : syracuseStep 894707 = 1342061) B1342061
theorem B894737 : Blo 595291 894737 := bstep (se 2 (by rfl) ⟨335526, by rfl⟩ : syracuseStep 894737 = 671053) B671053
theorem B894755 : Blo 595291 894755 := bstep (se 1 (by rfl) ⟨671066, by rfl⟩ : syracuseStep 894755 = 1342133) B1342133
theorem B1910573 : Blo 595291 1910573 := bstep (se 3 (by rfl) ⟨358232, by rfl⟩ : syracuseStep 1910573 = 716465) B716465
theorem B894785 : Blo 595291 894785 := bstep (se 2 (by rfl) ⟨335544, by rfl⟩ : syracuseStep 894785 = 671089) B671089
theorem B894803 : Blo 595291 894803 := bstep (se 1 (by rfl) ⟨671102, by rfl⟩ : syracuseStep 894803 = 1342205) B1342205
theorem B894833 : Blo 595291 894833 := bstep (se 2 (by rfl) ⟨335562, by rfl⟩ : syracuseStep 894833 = 671125) B671125
theorem B894851 : Blo 595291 894851 := bstep (se 1 (by rfl) ⟨671138, by rfl⟩ : syracuseStep 894851 = 1342277) B1342277
theorem B894881 : Blo 595291 894881 := bstep (se 2 (by rfl) ⟨335580, by rfl⟩ : syracuseStep 894881 = 671161) B671161
theorem B894899 : Blo 595291 894899 := bstep (se 1 (by rfl) ⟨671174, by rfl⟩ : syracuseStep 894899 = 1342349) B1342349
theorem B894929 : Blo 595291 894929 := bstep (se 2 (by rfl) ⟨335598, by rfl⟩ : syracuseStep 894929 = 671197) B671197
theorem B894947 : Blo 595291 894947 := bstep (se 1 (by rfl) ⟨671210, by rfl⟩ : syracuseStep 894947 = 1342421) B1342421
theorem B894977 : Blo 595291 894977 := bstep (se 2 (by rfl) ⟨335616, by rfl⟩ : syracuseStep 894977 = 671233) B671233
theorem B894995 : Blo 595291 894995 := bstep (se 1 (by rfl) ⟨671246, by rfl⟩ : syracuseStep 894995 = 1342493) B1342493
theorem B2009123 : Blo 595291 2009123 := bstep (se 1 (by rfl) ⟨1506842, by rfl⟩ : syracuseStep 2009123 = 3013685) B3013685
theorem B895025 : Blo 595291 895025 := bstep (se 2 (by rfl) ⟨335634, by rfl⟩ : syracuseStep 895025 = 671269) B671269
theorem B895043 : Blo 595291 895043 := bstep (se 1 (by rfl) ⟨671282, by rfl⟩ : syracuseStep 895043 = 1342565) B1342565
theorem B895073 : Blo 595291 895073 := bstep (se 2 (by rfl) ⟨335652, by rfl⟩ : syracuseStep 895073 = 671305) B671305
theorem B895091 : Blo 595291 895091 := bstep (se 1 (by rfl) ⟨671318, by rfl⟩ : syracuseStep 895091 = 1342637) B1342637
theorem B895121 : Blo 595291 895121 := bstep (se 2 (by rfl) ⟨335670, by rfl⟩ : syracuseStep 895121 = 671341) B671341
theorem B895139 : Blo 595291 895139 := bstep (se 1 (by rfl) ⟨671354, by rfl⟩ : syracuseStep 895139 = 1342709) B1342709
theorem B895169 : Blo 595291 895169 := bstep (se 2 (by rfl) ⟨335688, by rfl⟩ : syracuseStep 895169 = 671377) B671377
theorem B1812689 : Blo 595291 1812689 := bstep (se 2 (by rfl) ⟨679758, by rfl⟩ : syracuseStep 1812689 = 1359517) B1359517
theorem B895187 : Blo 595291 895187 := bstep (se 1 (by rfl) ⟨671390, by rfl⟩ : syracuseStep 895187 = 1342781) B1342781
theorem B895217 : Blo 595291 895217 := bstep (se 2 (by rfl) ⟨335706, by rfl⟩ : syracuseStep 895217 = 671413) B671413
theorem B2271473 : Blo 595291 2271473 := bstep (se 2 (by rfl) ⟨851802, by rfl⟩ : syracuseStep 2271473 = 1703605) B1703605
theorem B895235 : Blo 595291 895235 := bstep (se 1 (by rfl) ⟨671426, by rfl⟩ : syracuseStep 895235 = 1342853) B1342853
theorem B895265 : Blo 595291 895265 := bstep (se 2 (by rfl) ⟨335724, by rfl⟩ : syracuseStep 895265 = 671449) B671449
theorem B3025187 : Blo 595291 3025187 := bstep (se 1 (by rfl) ⟨2268890, by rfl⟩ : syracuseStep 3025187 = 4537781) B4537781
theorem B2009393 : Blo 595291 2009393 := bstep (se 2 (by rfl) ⟨753522, by rfl⟩ : syracuseStep 2009393 = 1507045) B1507045
theorem B895283 : Blo 595291 895283 := bstep (se 1 (by rfl) ⟨671462, by rfl⟩ : syracuseStep 895283 = 1342925) B1342925
theorem B895313 : Blo 595291 895313 := bstep (se 2 (by rfl) ⟨335742, by rfl⟩ : syracuseStep 895313 = 671485) B671485
theorem B895331 : Blo 595291 895331 := bstep (se 1 (by rfl) ⟨671498, by rfl⟩ : syracuseStep 895331 = 1342997) B1342997
theorem B895361 : Blo 595291 895361 := bstep (se 2 (by rfl) ⟨335760, by rfl⟩ : syracuseStep 895361 = 671521) B671521
theorem B895379 : Blo 595291 895379 := bstep (se 1 (by rfl) ⟨671534, by rfl⟩ : syracuseStep 895379 = 1343069) B1343069
theorem B895409 : Blo 595291 895409 := bstep (se 2 (by rfl) ⟨335778, by rfl⟩ : syracuseStep 895409 = 671557) B671557
theorem B895427 : Blo 595291 895427 := bstep (se 1 (by rfl) ⟨671570, by rfl⟩ : syracuseStep 895427 = 1343141) B1343141
theorem B895457 : Blo 595291 895457 := bstep (se 2 (by rfl) ⟨335796, by rfl⟩ : syracuseStep 895457 = 671593) B671593
theorem B895475 : Blo 595291 895475 := bstep (se 1 (by rfl) ⟨671606, by rfl⟩ : syracuseStep 895475 = 1343213) B1343213
theorem B895505 : Blo 595291 895505 := bstep (se 2 (by rfl) ⟨335814, by rfl⟩ : syracuseStep 895505 = 671629) B671629
theorem B895523 : Blo 595291 895523 := bstep (se 1 (by rfl) ⟨671642, by rfl⟩ : syracuseStep 895523 = 1343285) B1343285
theorem B895553 : Blo 595291 895553 := bstep (se 2 (by rfl) ⟨335832, by rfl⟩ : syracuseStep 895553 = 671665) B671665
theorem B895571 : Blo 595291 895571 := bstep (se 1 (by rfl) ⟨671678, by rfl⟩ : syracuseStep 895571 = 1343357) B1343357
theorem B895601 : Blo 595291 895601 := bstep (se 2 (by rfl) ⟨335850, by rfl⟩ : syracuseStep 895601 = 671701) B671701
theorem B895619 : Blo 595291 895619 := bstep (se 1 (by rfl) ⟨671714, by rfl⟩ : syracuseStep 895619 = 1343429) B1343429
theorem B895649 : Blo 595291 895649 := bstep (se 2 (by rfl) ⟨335868, by rfl⟩ : syracuseStep 895649 = 671737) B671737
theorem B895667 : Blo 595291 895667 := bstep (se 1 (by rfl) ⟨671750, by rfl⟩ : syracuseStep 895667 = 1343501) B1343501
theorem B895697 : Blo 595291 895697 := bstep (se 2 (by rfl) ⟨335886, by rfl⟩ : syracuseStep 895697 = 671773) B671773
theorem B895715 : Blo 595291 895715 := bstep (se 1 (by rfl) ⟨671786, by rfl⟩ : syracuseStep 895715 = 1343573) B1343573
theorem B895745 : Blo 595291 895745 := bstep (se 2 (by rfl) ⟨335904, by rfl⟩ : syracuseStep 895745 = 671809) B671809
theorem B895763 : Blo 595291 895763 := bstep (se 1 (by rfl) ⟨671822, by rfl⟩ : syracuseStep 895763 = 1343645) B1343645
theorem B895793 : Blo 595291 895793 := bstep (se 2 (by rfl) ⟨335922, by rfl⟩ : syracuseStep 895793 = 671845) B671845
theorem B895811 : Blo 595291 895811 := bstep (se 1 (by rfl) ⟨671858, by rfl⟩ : syracuseStep 895811 = 1343717) B1343717
theorem B2009933 : Blo 595291 2009933 := bstep (se 3 (by rfl) ⟨376862, by rfl⟩ : syracuseStep 2009933 = 753725) B753725
theorem B1616717 : Blo 595291 1616717 := bstep (se 3 (by rfl) ⟨303134, by rfl⟩ : syracuseStep 1616717 = 606269) B606269
theorem B895841 : Blo 595291 895841 := bstep (se 2 (by rfl) ⟨335940, by rfl⟩ : syracuseStep 895841 = 671881) B671881
theorem B895859 : Blo 595291 895859 := bstep (se 1 (by rfl) ⟨671894, by rfl⟩ : syracuseStep 895859 = 1343789) B1343789
theorem B2009987 : Blo 595291 2009987 := bstep (se 1 (by rfl) ⟨1507490, by rfl⟩ : syracuseStep 2009987 = 3014981) B3014981
theorem B895889 : Blo 595291 895889 := bstep (se 2 (by rfl) ⟨335958, by rfl⟩ : syracuseStep 895889 = 671917) B671917
theorem B895907 : Blo 595291 895907 := bstep (se 1 (by rfl) ⟨671930, by rfl⟩ : syracuseStep 895907 = 1343861) B1343861
theorem B895937 : Blo 595291 895937 := bstep (se 2 (by rfl) ⟨335976, by rfl⟩ : syracuseStep 895937 = 671953) B671953
theorem B895955 : Blo 595291 895955 := bstep (se 1 (by rfl) ⟨671966, by rfl⟩ : syracuseStep 895955 = 1343933) B1343933
theorem B895985 : Blo 595291 895985 := bstep (se 2 (by rfl) ⟨335994, by rfl⟩ : syracuseStep 895985 = 671989) B671989
theorem B896003 : Blo 595291 896003 := bstep (se 1 (by rfl) ⟨672002, by rfl⟩ : syracuseStep 896003 = 1344005) B1344005
theorem B896033 : Blo 595291 896033 := bstep (se 2 (by rfl) ⟨336012, by rfl⟩ : syracuseStep 896033 = 672025) B672025
theorem B896051 : Blo 595291 896051 := bstep (se 1 (by rfl) ⟨672038, by rfl⟩ : syracuseStep 896051 = 1344077) B1344077
theorem B3025997 : Blo 595291 3025997 := bstep (se 3 (by rfl) ⟨567374, by rfl⟩ : syracuseStep 3025997 = 1134749) B1134749
theorem B896081 : Blo 595291 896081 := bstep (se 2 (by rfl) ⟨336030, by rfl⟩ : syracuseStep 896081 = 672061) B672061
theorem B896099 : Blo 595291 896099 := bstep (se 1 (by rfl) ⟨672074, by rfl⟩ : syracuseStep 896099 = 1344149) B1344149
theorem B1911917 : Blo 595291 1911917 := bstep (se 3 (by rfl) ⟨358484, by rfl⟩ : syracuseStep 1911917 = 716969) B716969
theorem B896129 : Blo 595291 896129 := bstep (se 2 (by rfl) ⟨336048, by rfl⟩ : syracuseStep 896129 = 672097) B672097
theorem B2010257 : Blo 595291 2010257 := bstep (se 2 (by rfl) ⟨753846, by rfl⟩ : syracuseStep 2010257 = 1507693) B1507693
theorem B896147 : Blo 595291 896147 := bstep (se 1 (by rfl) ⟨672110, by rfl⟩ : syracuseStep 896147 = 1344221) B1344221
theorem B896177 : Blo 595291 896177 := bstep (se 2 (by rfl) ⟨336066, by rfl⟩ : syracuseStep 896177 = 672133) B672133
theorem B896195 : Blo 595291 896195 := bstep (se 1 (by rfl) ⟨672146, by rfl⟩ : syracuseStep 896195 = 1344293) B1344293
theorem B1944785 : Blo 595291 1944785 := bstep (se 2 (by rfl) ⟨729294, by rfl⟩ : syracuseStep 1944785 = 1458589) B1458589
theorem B896225 : Blo 595291 896225 := bstep (se 2 (by rfl) ⟨336084, by rfl⟩ : syracuseStep 896225 = 672169) B672169
theorem B896243 : Blo 595291 896243 := bstep (se 1 (by rfl) ⟨672182, by rfl⟩ : syracuseStep 896243 = 1344365) B1344365
theorem B896273 : Blo 595291 896273 := bstep (se 2 (by rfl) ⟨336102, by rfl⟩ : syracuseStep 896273 = 672205) B672205
theorem B896291 : Blo 595291 896291 := bstep (se 1 (by rfl) ⟨672218, by rfl⟩ : syracuseStep 896291 = 1344437) B1344437
theorem B896321 : Blo 595291 896321 := bstep (se 2 (by rfl) ⟨336120, by rfl⟩ : syracuseStep 896321 = 672241) B672241
theorem B896339 : Blo 595291 896339 := bstep (se 1 (by rfl) ⟨672254, by rfl⟩ : syracuseStep 896339 = 1344509) B1344509
theorem B896369 : Blo 595291 896369 := bstep (se 2 (by rfl) ⟨336138, by rfl⟩ : syracuseStep 896369 = 672277) B672277
theorem B896387 : Blo 595291 896387 := bstep (se 1 (by rfl) ⟨672290, by rfl⟩ : syracuseStep 896387 = 1344581) B1344581
theorem B896417 : Blo 595291 896417 := bstep (se 2 (by rfl) ⟨336156, by rfl⟩ : syracuseStep 896417 = 672313) B672313
theorem B896435 : Blo 595291 896435 := bstep (se 1 (by rfl) ⟨672326, by rfl⟩ : syracuseStep 896435 = 1344653) B1344653
theorem B3452357 : Blo 595291 3452357 := bstep (se 4 (by rfl) ⟨323658, by rfl⟩ : syracuseStep 3452357 = 647317) B647317
theorem B896465 : Blo 595291 896465 := bstep (se 2 (by rfl) ⟨336174, by rfl⟩ : syracuseStep 896465 = 672349) B672349
theorem B896483 : Blo 595291 896483 := bstep (se 1 (by rfl) ⟨672362, by rfl⟩ : syracuseStep 896483 = 1344725) B1344725
theorem B896513 : Blo 595291 896513 := bstep (se 2 (by rfl) ⟨336192, by rfl⟩ : syracuseStep 896513 = 672385) B672385
theorem B896531 : Blo 595291 896531 := bstep (se 1 (by rfl) ⟨672398, by rfl⟩ : syracuseStep 896531 = 1344797) B1344797
theorem B896561 : Blo 595291 896561 := bstep (se 2 (by rfl) ⟨336210, by rfl⟩ : syracuseStep 896561 = 672421) B672421
theorem B896579 : Blo 595291 896579 := bstep (se 1 (by rfl) ⟨672434, by rfl⟩ : syracuseStep 896579 = 1344869) B1344869
theorem B896609 : Blo 595291 896609 := bstep (se 2 (by rfl) ⟨336228, by rfl⟩ : syracuseStep 896609 = 672457) B672457
theorem B896627 : Blo 595291 896627 := bstep (se 1 (by rfl) ⟨672470, by rfl⟩ : syracuseStep 896627 = 1344941) B1344941
theorem B896657 : Blo 595291 896657 := bstep (se 2 (by rfl) ⟨336246, by rfl⟩ : syracuseStep 896657 = 672493) B672493
theorem B1289891 : Blo 595291 1289891 := bstep (se 1 (by rfl) ⟨967418, by rfl⟩ : syracuseStep 1289891 = 1934837) B1934837
theorem B896675 : Blo 595291 896675 := bstep (se 1 (by rfl) ⟨672506, by rfl⟩ : syracuseStep 896675 = 1345013) B1345013
theorem B2272931 : Blo 595291 2272931 := bstep (se 1 (by rfl) ⟨1704698, by rfl⟩ : syracuseStep 2272931 = 3409397) B3409397
theorem B2010797 : Blo 595291 2010797 := bstep (se 3 (by rfl) ⟨377024, by rfl⟩ : syracuseStep 2010797 = 754049) B754049
theorem B896705 : Blo 595291 896705 := bstep (se 2 (by rfl) ⟨336264, by rfl⟩ : syracuseStep 896705 = 672529) B672529
theorem B896723 : Blo 595291 896723 := bstep (se 1 (by rfl) ⟨672542, by rfl⟩ : syracuseStep 896723 = 1345085) B1345085
theorem B2010851 : Blo 595291 2010851 := bstep (se 1 (by rfl) ⟨1508138, by rfl⟩ : syracuseStep 2010851 = 3016277) B3016277
theorem B896753 : Blo 595291 896753 := bstep (se 2 (by rfl) ⟨336282, by rfl⟩ : syracuseStep 896753 = 672565) B672565
theorem B896771 : Blo 595291 896771 := bstep (se 1 (by rfl) ⟨672578, by rfl⟩ : syracuseStep 896771 = 1345157) B1345157
theorem B896801 : Blo 595291 896801 := bstep (se 2 (by rfl) ⟨336300, by rfl⟩ : syracuseStep 896801 = 672601) B672601
theorem B896819 : Blo 595291 896819 := bstep (se 1 (by rfl) ⟨672614, by rfl⟩ : syracuseStep 896819 = 1345229) B1345229
theorem B896849 : Blo 595291 896849 := bstep (se 2 (by rfl) ⟨336318, by rfl⟩ : syracuseStep 896849 = 672637) B672637
theorem B896867 : Blo 595291 896867 := bstep (se 1 (by rfl) ⟨672650, by rfl⟩ : syracuseStep 896867 = 1345301) B1345301
theorem B896897 : Blo 595291 896897 := bstep (se 2 (by rfl) ⟨336336, by rfl⟩ : syracuseStep 896897 = 672673) B672673
theorem B896915 : Blo 595291 896915 := bstep (se 1 (by rfl) ⟨672686, by rfl⟩ : syracuseStep 896915 = 1345373) B1345373
theorem B896945 : Blo 595291 896945 := bstep (se 2 (by rfl) ⟨336354, by rfl⟩ : syracuseStep 896945 = 672709) B672709
theorem B896963 : Blo 595291 896963 := bstep (se 1 (by rfl) ⟨672722, by rfl⟩ : syracuseStep 896963 = 1345445) B1345445
theorem B896993 : Blo 595291 896993 := bstep (se 2 (by rfl) ⟨336372, by rfl⟩ : syracuseStep 896993 = 672745) B672745
theorem B2011121 : Blo 595291 2011121 := bstep (se 2 (by rfl) ⟨754170, by rfl⟩ : syracuseStep 2011121 = 1508341) B1508341
theorem B897011 : Blo 595291 897011 := bstep (se 1 (by rfl) ⟨672758, by rfl⟩ : syracuseStep 897011 = 1345517) B1345517
theorem B6467597 : Blo 595291 6467597 := bstep (se 3 (by rfl) ⟨1212674, by rfl⟩ : syracuseStep 6467597 = 2425349) B2425349
theorem B897041 : Blo 595291 897041 := bstep (se 2 (by rfl) ⟨336390, by rfl⟩ : syracuseStep 897041 = 672781) B672781
theorem B897059 : Blo 595291 897059 := bstep (se 1 (by rfl) ⟨672794, by rfl⟩ : syracuseStep 897059 = 1345589) B1345589
theorem B897089 : Blo 595291 897089 := bstep (se 2 (by rfl) ⟨336408, by rfl⟩ : syracuseStep 897089 = 672817) B672817
theorem B897107 : Blo 595291 897107 := bstep (se 1 (by rfl) ⟨672830, by rfl⟩ : syracuseStep 897107 = 1345661) B1345661
theorem B897137 : Blo 595291 897137 := bstep (se 2 (by rfl) ⟨336426, by rfl⟩ : syracuseStep 897137 = 672853) B672853
theorem B897155 : Blo 595291 897155 := bstep (se 1 (by rfl) ⟨672866, by rfl⟩ : syracuseStep 897155 = 1345733) B1345733
theorem B897185 : Blo 595291 897185 := bstep (se 2 (by rfl) ⟨336444, by rfl⟩ : syracuseStep 897185 = 672889) B672889
theorem B897203 : Blo 595291 897203 := bstep (se 1 (by rfl) ⟨672902, by rfl⟩ : syracuseStep 897203 = 1345805) B1345805
theorem B897233 : Blo 595291 897233 := bstep (se 2 (by rfl) ⟨336462, by rfl⟩ : syracuseStep 897233 = 672925) B672925
theorem B897251 : Blo 595291 897251 := bstep (se 1 (by rfl) ⟨672938, by rfl⟩ : syracuseStep 897251 = 1345877) B1345877
theorem B897281 : Blo 595291 897281 := bstep (se 2 (by rfl) ⟨336480, by rfl⟩ : syracuseStep 897281 = 672961) B672961
theorem B897299 : Blo 595291 897299 := bstep (se 1 (by rfl) ⟨672974, by rfl⟩ : syracuseStep 897299 = 1345949) B1345949
theorem B897329 : Blo 595291 897329 := bstep (se 2 (by rfl) ⟨336498, by rfl⟩ : syracuseStep 897329 = 672997) B672997
theorem B897347 : Blo 595291 897347 := bstep (se 1 (by rfl) ⟨673010, by rfl⟩ : syracuseStep 897347 = 1346021) B1346021
theorem B897377 : Blo 595291 897377 := bstep (se 2 (by rfl) ⟨336516, by rfl⟩ : syracuseStep 897377 = 673033) B673033
theorem B897395 : Blo 595291 897395 := bstep (se 1 (by rfl) ⟨673046, by rfl⟩ : syracuseStep 897395 = 1346093) B1346093
theorem B897425 : Blo 595291 897425 := bstep (se 2 (by rfl) ⟨336534, by rfl⟩ : syracuseStep 897425 = 673069) B673069
theorem B897443 : Blo 595291 897443 := bstep (se 1 (by rfl) ⟨673082, by rfl⟩ : syracuseStep 897443 = 1346165) B1346165
theorem B897473 : Blo 595291 897473 := bstep (se 2 (by rfl) ⟨336552, by rfl⟩ : syracuseStep 897473 = 673105) B673105
theorem B897491 : Blo 595291 897491 := bstep (se 1 (by rfl) ⟨673118, by rfl⟩ : syracuseStep 897491 = 1346237) B1346237
theorem B897521 : Blo 595291 897521 := bstep (se 2 (by rfl) ⟨336570, by rfl⟩ : syracuseStep 897521 = 673141) B673141
theorem B897539 : Blo 595291 897539 := bstep (se 1 (by rfl) ⟨673154, by rfl⟩ : syracuseStep 897539 = 1346309) B1346309
theorem B2011661 : Blo 595291 2011661 := bstep (se 3 (by rfl) ⟨377186, by rfl⟩ : syracuseStep 2011661 = 754373) B754373
theorem B897569 : Blo 595291 897569 := bstep (se 2 (by rfl) ⟨336588, by rfl⟩ : syracuseStep 897569 = 673177) B673177
theorem B3551779 : Blo 595291 3551779 := bstep (se 1 (by rfl) ⟨2663834, by rfl⟩ : syracuseStep 3551779 = 5327669) B5327669
theorem B897587 : Blo 595291 897587 := bstep (se 1 (by rfl) ⟨673190, by rfl⟩ : syracuseStep 897587 = 1346381) B1346381
theorem B2011715 : Blo 595291 2011715 := bstep (se 1 (by rfl) ⟨1508786, by rfl⟩ : syracuseStep 2011715 = 3017573) B3017573
theorem B897617 : Blo 595291 897617 := bstep (se 2 (by rfl) ⟨336606, by rfl⟩ : syracuseStep 897617 = 673213) B673213
theorem B897635 : Blo 595291 897635 := bstep (se 1 (by rfl) ⟨673226, by rfl⟩ : syracuseStep 897635 = 1346453) B1346453
theorem B897665 : Blo 595291 897665 := bstep (se 2 (by rfl) ⟨336624, by rfl⟩ : syracuseStep 897665 = 673249) B673249
theorem B2273933 : Blo 595291 2273933 := bstep (se 3 (by rfl) ⟨426362, by rfl⟩ : syracuseStep 2273933 = 852725) B852725
theorem B897683 : Blo 595291 897683 := bstep (se 1 (by rfl) ⟨673262, by rfl⟩ : syracuseStep 897683 = 1346525) B1346525
theorem B1913507 : Blo 595291 1913507 := bstep (se 1 (by rfl) ⟨1435130, by rfl⟩ : syracuseStep 1913507 = 2870261) B2870261
theorem B897713 : Blo 595291 897713 := bstep (se 2 (by rfl) ⟨336642, by rfl⟩ : syracuseStep 897713 = 673285) B673285
theorem B897731 : Blo 595291 897731 := bstep (se 1 (by rfl) ⟨673298, by rfl⟩ : syracuseStep 897731 = 1346597) B1346597
theorem B897761 : Blo 595291 897761 := bstep (se 2 (by rfl) ⟨336660, by rfl⟩ : syracuseStep 897761 = 673321) B673321
theorem B897779 : Blo 595291 897779 := bstep (se 1 (by rfl) ⟨673334, by rfl⟩ : syracuseStep 897779 = 1346669) B1346669
theorem B897809 : Blo 595291 897809 := bstep (se 2 (by rfl) ⟨336678, by rfl⟩ : syracuseStep 897809 = 673357) B673357
theorem B897827 : Blo 595291 897827 := bstep (se 1 (by rfl) ⟨673370, by rfl⟩ : syracuseStep 897827 = 1346741) B1346741
theorem B897857 : Blo 595291 897857 := bstep (se 2 (by rfl) ⟨336696, by rfl⟩ : syracuseStep 897857 = 673393) B673393
theorem B2011985 : Blo 595291 2011985 := bstep (se 2 (by rfl) ⟨754494, by rfl⟩ : syracuseStep 2011985 = 1508989) B1508989
theorem B897875 : Blo 595291 897875 := bstep (se 1 (by rfl) ⟨673406, by rfl⟩ : syracuseStep 897875 = 1346813) B1346813
theorem B897905 : Blo 595291 897905 := bstep (se 2 (by rfl) ⟨336714, by rfl⟩ : syracuseStep 897905 = 673429) B673429
theorem B897923 : Blo 595291 897923 := bstep (se 1 (by rfl) ⟨673442, by rfl⟩ : syracuseStep 897923 = 1346885) B1346885
theorem B897953 : Blo 595291 897953 := bstep (se 2 (by rfl) ⟨336732, by rfl⟩ : syracuseStep 897953 = 673465) B673465
theorem B897971 : Blo 595291 897971 := bstep (se 1 (by rfl) ⟨673478, by rfl⟩ : syracuseStep 897971 = 1346957) B1346957
theorem B7648181 : Blo 595291 7648181 := bstep (se 5 (by rfl) ⟨358508, by rfl⟩ : syracuseStep 7648181 = 717017) B717017
theorem B898001 : Blo 595291 898001 := bstep (se 2 (by rfl) ⟨336750, by rfl⟩ : syracuseStep 898001 = 673501) B673501
theorem B898019 : Blo 595291 898019 := bstep (se 1 (by rfl) ⟨673514, by rfl⟩ : syracuseStep 898019 = 1347029) B1347029
theorem B898049 : Blo 595291 898049 := bstep (se 2 (by rfl) ⟨336768, by rfl⟩ : syracuseStep 898049 = 673537) B673537
theorem B898067 : Blo 595291 898067 := bstep (se 1 (by rfl) ⟨673550, by rfl⟩ : syracuseStep 898067 = 1347101) B1347101
theorem B898097 : Blo 595291 898097 := bstep (se 2 (by rfl) ⟨336786, by rfl⟩ : syracuseStep 898097 = 673573) B673573
theorem B898115 : Blo 595291 898115 := bstep (se 1 (by rfl) ⟨673586, by rfl⟩ : syracuseStep 898115 = 1347173) B1347173
theorem B898145 : Blo 595291 898145 := bstep (se 2 (by rfl) ⟨336804, by rfl⟩ : syracuseStep 898145 = 673609) B673609
theorem B898163 : Blo 595291 898163 := bstep (se 1 (by rfl) ⟨673622, by rfl⟩ : syracuseStep 898163 = 1347245) B1347245
theorem B898193 : Blo 595291 898193 := bstep (se 2 (by rfl) ⟨336822, by rfl⟩ : syracuseStep 898193 = 673645) B673645
theorem B898211 : Blo 595291 898211 := bstep (se 1 (by rfl) ⟨673658, by rfl⟩ : syracuseStep 898211 = 1347317) B1347317
theorem B898241 : Blo 595291 898241 := bstep (se 2 (by rfl) ⟨336840, by rfl⟩ : syracuseStep 898241 = 673681) B673681
theorem B898259 : Blo 595291 898259 := bstep (se 1 (by rfl) ⟨673694, by rfl⟩ : syracuseStep 898259 = 1347389) B1347389
theorem B3880163 : Blo 595291 3880163 := bstep (se 1 (by rfl) ⟨2910122, by rfl⟩ : syracuseStep 3880163 = 5820245) B5820245
theorem B898289 : Blo 595291 898289 := bstep (se 2 (by rfl) ⟨336858, by rfl⟩ : syracuseStep 898289 = 673717) B673717
theorem B898307 : Blo 595291 898307 := bstep (se 1 (by rfl) ⟨673730, by rfl⟩ : syracuseStep 898307 = 1347461) B1347461
theorem B898337 : Blo 595291 898337 := bstep (se 2 (by rfl) ⟨336876, by rfl⟩ : syracuseStep 898337 = 673753) B673753
theorem B898355 : Blo 595291 898355 := bstep (se 1 (by rfl) ⟨673766, by rfl⟩ : syracuseStep 898355 = 1347533) B1347533
theorem B898385 : Blo 595291 898385 := bstep (se 2 (by rfl) ⟨336894, by rfl⟩ : syracuseStep 898385 = 673789) B673789
theorem B898403 : Blo 595291 898403 := bstep (se 1 (by rfl) ⟨673802, by rfl⟩ : syracuseStep 898403 = 1347605) B1347605
theorem B2012525 : Blo 595291 2012525 := bstep (se 3 (by rfl) ⟨377348, by rfl⟩ : syracuseStep 2012525 = 754697) B754697
theorem B898433 : Blo 595291 898433 := bstep (se 2 (by rfl) ⟨336912, by rfl⟩ : syracuseStep 898433 = 673825) B673825
theorem B898451 : Blo 595291 898451 := bstep (se 1 (by rfl) ⟨673838, by rfl⟩ : syracuseStep 898451 = 1347677) B1347677
theorem B2012579 : Blo 595291 2012579 := bstep (se 1 (by rfl) ⟨1509434, by rfl⟩ : syracuseStep 2012579 = 3018869) B3018869
theorem B1914275 : Blo 595291 1914275 := bstep (se 1 (by rfl) ⟨1435706, by rfl⟩ : syracuseStep 1914275 = 2871413) B2871413
theorem B898481 : Blo 595291 898481 := bstep (se 2 (by rfl) ⟨336930, by rfl⟩ : syracuseStep 898481 = 673861) B673861
theorem B898499 : Blo 595291 898499 := bstep (se 1 (by rfl) ⟨673874, by rfl⟩ : syracuseStep 898499 = 1347749) B1347749
theorem B898529 : Blo 595291 898529 := bstep (se 2 (by rfl) ⟨336948, by rfl⟩ : syracuseStep 898529 = 673897) B673897
theorem B898547 : Blo 595291 898547 := bstep (se 1 (by rfl) ⟨673910, by rfl⟩ : syracuseStep 898547 = 1347821) B1347821
theorem B898577 : Blo 595291 898577 := bstep (se 2 (by rfl) ⟨336966, by rfl⟩ : syracuseStep 898577 = 673933) B673933
theorem B898595 : Blo 595291 898595 := bstep (se 1 (by rfl) ⟨673946, by rfl⟩ : syracuseStep 898595 = 1347893) B1347893
theorem B898625 : Blo 595291 898625 := bstep (se 2 (by rfl) ⟨336984, by rfl⟩ : syracuseStep 898625 = 673969) B673969
theorem B898643 : Blo 595291 898643 := bstep (se 1 (by rfl) ⟨673982, by rfl⟩ : syracuseStep 898643 = 1347965) B1347965
theorem B898673 : Blo 595291 898673 := bstep (se 2 (by rfl) ⟨337002, by rfl⟩ : syracuseStep 898673 = 674005) B674005
theorem B898691 : Blo 595291 898691 := bstep (se 1 (by rfl) ⟨674018, by rfl⟩ : syracuseStep 898691 = 1348037) B1348037
theorem B898721 : Blo 595291 898721 := bstep (se 2 (by rfl) ⟨337020, by rfl⟩ : syracuseStep 898721 = 674041) B674041
theorem B2012849 : Blo 595291 2012849 := bstep (se 2 (by rfl) ⟨754818, by rfl⟩ : syracuseStep 2012849 = 1509637) B1509637
theorem B898739 : Blo 595291 898739 := bstep (se 1 (by rfl) ⟨674054, by rfl⟩ : syracuseStep 898739 = 1348109) B1348109
theorem B898769 : Blo 595291 898769 := bstep (se 2 (by rfl) ⟨337038, by rfl⟩ : syracuseStep 898769 = 674077) B674077
theorem B898787 : Blo 595291 898787 := bstep (se 1 (by rfl) ⟨674090, by rfl⟩ : syracuseStep 898787 = 1348181) B1348181
theorem B898817 : Blo 595291 898817 := bstep (se 2 (by rfl) ⟨337056, by rfl⟩ : syracuseStep 898817 = 674113) B674113
theorem B898835 : Blo 595291 898835 := bstep (se 1 (by rfl) ⟨674126, by rfl⟩ : syracuseStep 898835 = 1348253) B1348253
theorem B27997973 : Blo 595291 27997973 := bstep (se 6 (by rfl) ⟨656202, by rfl⟩ : syracuseStep 27997973 = 1312405) B1312405
theorem B1914673 : Blo 595291 1914673 := bstep (se 2 (by rfl) ⟨718002, by rfl⟩ : syracuseStep 1914673 = 1436005) B1436005
theorem B898865 : Blo 595291 898865 := bstep (se 2 (by rfl) ⟨337074, by rfl⟩ : syracuseStep 898865 = 674149) B674149
theorem B898883 : Blo 595291 898883 := bstep (se 1 (by rfl) ⟨674162, by rfl⟩ : syracuseStep 898883 = 1348325) B1348325
theorem B898913 : Blo 595291 898913 := bstep (se 2 (by rfl) ⟨337092, by rfl⟩ : syracuseStep 898913 = 674185) B674185
theorem B898931 : Blo 595291 898931 := bstep (se 1 (by rfl) ⟨674198, by rfl⟩ : syracuseStep 898931 = 1348397) B1348397
theorem B1914787 : Blo 595291 1914787 := bstep (se 1 (by rfl) ⟨1436090, by rfl⟩ : syracuseStep 1914787 = 2872181) B2872181
theorem B3028913 : Blo 595291 3028913 := bstep (se 2 (by rfl) ⟨1135842, by rfl⟩ : syracuseStep 3028913 = 2271685) B2271685
theorem B604099 : Blo 595291 604099 := bstep (se 1 (by rfl) ⟨453074, by rfl⟩ : syracuseStep 604099 = 906149) B906149
theorem B3225541 : Blo 595291 3225541 := bstep (se 4 (by rfl) ⟨302394, by rfl⟩ : syracuseStep 3225541 = 604789) B604789
theorem B1554403 : Blo 595291 1554403 := bstep (se 1 (by rfl) ⟨1165802, by rfl⟩ : syracuseStep 1554403 = 2331605) B2331605
theorem B669811 : Blo 595291 669811 := bstep (se 1 (by rfl) ⟨502358, by rfl⟩ : syracuseStep 669811 = 1004717) B1004717
theorem B637075 : Blo 595291 637075 := bstep (se 1 (by rfl) ⟨477806, by rfl⟩ : syracuseStep 637075 = 955613) B955613
theorem B2013389 : Blo 595291 2013389 := bstep (se 3 (by rfl) ⟨377510, by rfl⟩ : syracuseStep 2013389 = 755021) B755021
theorem B1718513 : Blo 595291 1718513 := bstep (se 2 (by rfl) ⟨644442, by rfl⟩ : syracuseStep 1718513 = 1288885) B1288885
theorem B669955 : Blo 595291 669955 := bstep (se 1 (by rfl) ⟨502466, by rfl⟩ : syracuseStep 669955 = 1004933) B1004933
theorem B2013443 : Blo 595291 2013443 := bstep (se 1 (by rfl) ⟨1510082, by rfl⟩ : syracuseStep 2013443 = 3020165) B3020165
theorem B670099 : Blo 595291 670099 := bstep (se 1 (by rfl) ⟨502574, by rfl⟩ : syracuseStep 670099 = 1005149) B1005149
theorem B4831757 : Blo 595291 4831757 := bstep (se 3 (by rfl) ⟨905954, by rfl⟩ : syracuseStep 4831757 = 1811909) B1811909
theorem B2013713 : Blo 595291 2013713 := bstep (se 2 (by rfl) ⟨755142, by rfl⟩ : syracuseStep 2013713 = 1510285) B1510285
theorem B670243 : Blo 595291 670243 := bstep (se 1 (by rfl) ⟨502682, by rfl⟩ : syracuseStep 670243 = 1005365) B1005365
theorem B637507 : Blo 595291 637507 := bstep (se 1 (by rfl) ⟨478130, by rfl⟩ : syracuseStep 637507 = 956261) B956261
theorem B3226189 : Blo 595291 3226189 := bstep (se 3 (by rfl) ⟨604910, by rfl⟩ : syracuseStep 3226189 = 1209821) B1209821
theorem B1915505 : Blo 595291 1915505 := bstep (se 2 (by rfl) ⟨718314, by rfl⟩ : syracuseStep 1915505 = 1436629) B1436629
theorem B1718929 : Blo 595291 1718929 := bstep (se 2 (by rfl) ⟨644598, by rfl⟩ : syracuseStep 1718929 = 1289197) B1289197
theorem B670387 : Blo 595291 670387 := bstep (se 1 (by rfl) ⟨502790, by rfl⟩ : syracuseStep 670387 = 1005581) B1005581
theorem B670531 : Blo 595291 670531 := bstep (se 1 (by rfl) ⟨502898, by rfl⟩ : syracuseStep 670531 = 1005797) B1005797
theorem B670675 : Blo 595291 670675 := bstep (se 1 (by rfl) ⟨503006, by rfl⟩ : syracuseStep 670675 = 1006013) B1006013
theorem B5094413 : Blo 595291 5094413 := bstep (se 3 (by rfl) ⟨955202, by rfl⟩ : syracuseStep 5094413 = 1910405) B1910405
theorem B2014253 : Blo 595291 2014253 := bstep (se 3 (by rfl) ⟨377672, by rfl⟩ : syracuseStep 2014253 = 755345) B755345
theorem B605251 : Blo 595291 605251 := bstep (se 1 (by rfl) ⟨453938, by rfl⟩ : syracuseStep 605251 = 907877) B907877
theorem B670819 : Blo 595291 670819 := bstep (se 1 (by rfl) ⟨503114, by rfl⟩ : syracuseStep 670819 = 1006229) B1006229
theorem B2014307 : Blo 595291 2014307 := bstep (se 1 (by rfl) ⟨1510730, by rfl⟩ : syracuseStep 2014307 = 3021461) B3021461
theorem B1916045 : Blo 595291 1916045 := bstep (se 3 (by rfl) ⟨359258, by rfl⟩ : syracuseStep 1916045 = 718517) B718517
theorem B670963 : Blo 595291 670963 := bstep (se 1 (by rfl) ⟨503222, by rfl⟩ : syracuseStep 670963 = 1006445) B1006445
theorem B3030371 : Blo 595291 3030371 := bstep (se 1 (by rfl) ⟨2272778, by rfl⟩ : syracuseStep 3030371 = 4545557) B4545557
theorem B1359217 : Blo 595291 1359217 := bstep (se 2 (by rfl) ⟨509706, by rfl⟩ : syracuseStep 1359217 = 1019413) B1019413
theorem B2014577 : Blo 595291 2014577 := bstep (se 2 (by rfl) ⟨755466, by rfl⟩ : syracuseStep 2014577 = 1510933) B1510933
theorem B671107 : Blo 595291 671107 := bstep (se 1 (by rfl) ⟨503330, by rfl⟩ : syracuseStep 671107 = 1006661) B1006661
theorem B10173923 : Blo 595291 10173923 := bstep (se 1 (by rfl) ⟨7630442, by rfl⟩ : syracuseStep 10173923 = 15260885) B15260885
theorem B671251 : Blo 595291 671251 := bstep (se 1 (by rfl) ⟨503438, by rfl⟩ : syracuseStep 671251 = 1006877) B1006877
theorem B671395 : Blo 595291 671395 := bstep (se 1 (by rfl) ⟨503546, by rfl⟩ : syracuseStep 671395 = 1007093) B1007093
theorem B3391217 : Blo 595291 3391217 := bstep (se 2 (by rfl) ⟨1271706, by rfl⟩ : syracuseStep 3391217 = 2543413) B2543413
theorem B1162993 : Blo 595291 1162993 := bstep (se 2 (by rfl) ⟨436122, by rfl⟩ : syracuseStep 1162993 = 872245) B872245
theorem B5750513 : Blo 595291 5750513 := bstep (se 2 (by rfl) ⟨2156442, by rfl⟩ : syracuseStep 5750513 = 4312885) B4312885
theorem B671539 : Blo 595291 671539 := bstep (se 1 (by rfl) ⟨503654, by rfl⟩ : syracuseStep 671539 = 1007309) B1007309
theorem B638771 : Blo 595291 638771 := bstep (se 1 (by rfl) ⟨479078, by rfl⟩ : syracuseStep 638771 = 958157) B958157
theorem B2015117 : Blo 595291 2015117 := bstep (se 3 (by rfl) ⟨377834, by rfl⟩ : syracuseStep 2015117 = 755669) B755669
theorem B671683 : Blo 595291 671683 := bstep (se 1 (by rfl) ⟨503762, by rfl⟩ : syracuseStep 671683 = 1007525) B1007525
theorem B2015171 : Blo 595291 2015171 := bstep (se 1 (by rfl) ⟨1511378, by rfl⟩ : syracuseStep 2015171 = 3022757) B3022757
theorem B1458179 : Blo 595291 1458179 := bstep (se 1 (by rfl) ⟨1093634, by rfl⟩ : syracuseStep 1458179 = 2187269) B2187269
theorem B671827 : Blo 595291 671827 := bstep (se 1 (by rfl) ⟨503870, by rfl⟩ : syracuseStep 671827 = 1007741) B1007741
theorem B3031181 : Blo 595291 3031181 := bstep (se 3 (by rfl) ⟨568346, by rfl⟩ : syracuseStep 3031181 = 1136693) B1136693
theorem B606403 : Blo 595291 606403 := bstep (se 1 (by rfl) ⟨454802, by rfl⟩ : syracuseStep 606403 = 909605) B909605
theorem B2015441 : Blo 595291 2015441 := bstep (se 2 (by rfl) ⟨755790, by rfl⟩ : syracuseStep 2015441 = 1511581) B1511581
theorem B671971 : Blo 595291 671971 := bstep (se 1 (by rfl) ⟨503978, by rfl⟩ : syracuseStep 671971 = 1007957) B1007957
theorem B4604131 : Blo 595291 4604131 := bstep (se 1 (by rfl) ⟨3453098, by rfl⟩ : syracuseStep 4604131 = 6906197) B6906197
theorem B1130755 : Blo 595291 1130755 := bstep (se 1 (by rfl) ⟨848066, by rfl⟩ : syracuseStep 1130755 = 1696133) B1696133
theorem B5161229 : Blo 595291 5161229 := bstep (se 3 (by rfl) ⟨967730, by rfl⟩ : syracuseStep 5161229 = 1935461) B1935461
theorem B2867491 : Blo 595291 2867491 := bstep (se 1 (by rfl) ⟨2150618, by rfl⟩ : syracuseStep 2867491 = 4301237) B4301237
theorem B672115 : Blo 595291 672115 := bstep (se 1 (by rfl) ⟨504086, by rfl⟩ : syracuseStep 672115 = 1008173) B1008173
theorem B1130915 : Blo 595291 1130915 := bstep (se 1 (by rfl) ⟨848186, by rfl⟩ : syracuseStep 1130915 = 1696373) B1696373
theorem B672259 : Blo 595291 672259 := bstep (se 1 (by rfl) ⟨504194, by rfl⟩ : syracuseStep 672259 = 1008389) B1008389
theorem B639523 : Blo 595291 639523 := bstep (se 1 (by rfl) ⟨479642, by rfl⟩ : syracuseStep 639523 = 959285) B959285
theorem B37274165 : Blo 595291 37274165 := bstep (se 5 (by rfl) ⟨1747226, by rfl⟩ : syracuseStep 37274165 = 3494453) B3494453
theorem B967235 : Blo 595291 967235 := bstep (se 1 (by rfl) ⟨725426, by rfl⟩ : syracuseStep 967235 = 1450853) B1450853
theorem B672403 : Blo 595291 672403 := bstep (se 1 (by rfl) ⟨504302, by rfl⟩ : syracuseStep 672403 = 1008605) B1008605
theorem B2015981 : Blo 595291 2015981 := bstep (se 3 (by rfl) ⟨377996, by rfl⟩ : syracuseStep 2015981 = 755993) B755993
theorem B2016035 : Blo 595291 2016035 := bstep (se 1 (by rfl) ⟨1512026, by rfl⟩ : syracuseStep 2016035 = 3024053) B3024053
theorem B672547 : Blo 595291 672547 := bstep (se 1 (by rfl) ⟨504410, by rfl⟩ : syracuseStep 672547 = 1008821) B1008821
theorem B967601 : Blo 595291 967601 := bstep (se 2 (by rfl) ⟨362850, by rfl⟩ : syracuseStep 967601 = 725701) B725701
theorem B672691 : Blo 595291 672691 := bstep (se 1 (by rfl) ⟨504518, by rfl⟩ : syracuseStep 672691 = 1009037) B1009037
theorem B1164241 : Blo 595291 1164241 := bstep (se 2 (by rfl) ⟨436590, by rfl⟩ : syracuseStep 1164241 = 873181) B873181
theorem B1360867 : Blo 595291 1360867 := bstep (se 1 (by rfl) ⟨1020650, by rfl⟩ : syracuseStep 1360867 = 2041301) B2041301
theorem B1917965 : Blo 595291 1917965 := bstep (se 3 (by rfl) ⟨359618, by rfl⟩ : syracuseStep 1917965 = 719237) B719237
theorem B2016305 : Blo 595291 2016305 := bstep (se 2 (by rfl) ⟨756114, by rfl⟩ : syracuseStep 2016305 = 1512229) B1512229
theorem B672835 : Blo 595291 672835 := bstep (se 1 (by rfl) ⟨504626, by rfl⟩ : syracuseStep 672835 = 1009253) B1009253
theorem B3392675 : Blo 595291 3392675 := bstep (se 1 (by rfl) ⟨2544506, by rfl⟩ : syracuseStep 3392675 = 5089013) B5089013
theorem B672979 : Blo 595291 672979 := bstep (se 1 (by rfl) ⟨504734, by rfl⟩ : syracuseStep 672979 = 1009469) B1009469
theorem B5096803 : Blo 595291 5096803 := bstep (se 1 (by rfl) ⟨3822602, by rfl⟩ : syracuseStep 5096803 = 7645205) B7645205
theorem B673123 : Blo 595291 673123 := bstep (se 1 (by rfl) ⟨504842, by rfl⟩ : syracuseStep 673123 = 1009685) B1009685
theorem B6145379 : Blo 595291 6145379 := bstep (se 1 (by rfl) ⟨4609034, by rfl⟩ : syracuseStep 6145379 = 9218069) B9218069
theorem B5752205 : Blo 595291 5752205 := bstep (se 3 (by rfl) ⟨1078538, by rfl⟩ : syracuseStep 5752205 = 2157077) B2157077
theorem B1131985 : Blo 595291 1131985 := bstep (se 2 (by rfl) ⟨424494, by rfl⟩ : syracuseStep 1131985 = 848989) B848989
theorem B673267 : Blo 595291 673267 := bstep (se 1 (by rfl) ⟨504950, by rfl⟩ : syracuseStep 673267 = 1009901) B1009901
theorem B3065357 : Blo 595291 3065357 := bstep (se 3 (by rfl) ⟨574754, by rfl⟩ : syracuseStep 3065357 = 1149509) B1149509
theorem B2016845 : Blo 595291 2016845 := bstep (se 3 (by rfl) ⟨378158, by rfl⟩ : syracuseStep 2016845 = 756317) B756317
theorem B3327601 : Blo 595291 3327601 := bstep (se 2 (by rfl) ⟨1247850, by rfl⟩ : syracuseStep 3327601 = 2495701) B2495701
theorem B2016899 : Blo 595291 2016899 := bstep (se 1 (by rfl) ⟨1512674, by rfl⟩ : syracuseStep 2016899 = 3025349) B3025349
theorem B673411 : Blo 595291 673411 := bstep (se 1 (by rfl) ⟨505058, by rfl⟩ : syracuseStep 673411 = 1010117) B1010117
theorem B673555 : Blo 595291 673555 := bstep (se 1 (by rfl) ⟨505166, by rfl⟩ : syracuseStep 673555 = 1010333) B1010333
theorem B2017169 : Blo 595291 2017169 := bstep (se 2 (by rfl) ⟨756438, by rfl⟩ : syracuseStep 2017169 = 1512877) B1512877
theorem B673699 : Blo 595291 673699 := bstep (se 1 (by rfl) ⟨505274, by rfl⟩ : syracuseStep 673699 = 1010549) B1010549
theorem B673843 : Blo 595291 673843 := bstep (se 1 (by rfl) ⟨505382, by rfl⟩ : syracuseStep 673843 = 1010765) B1010765
theorem B3393677 : Blo 595291 3393677 := bstep (se 3 (by rfl) ⟨636314, by rfl⟩ : syracuseStep 3393677 = 1272629) B1272629
theorem B2148515 : Blo 595291 2148515 := bstep (se 1 (by rfl) ⟨1611386, by rfl⟩ : syracuseStep 2148515 = 3222773) B3222773
theorem B2050211 : Blo 595291 2050211 := bstep (se 1 (by rfl) ⟨1537658, by rfl⟩ : syracuseStep 2050211 = 3075317) B3075317
theorem B673987 : Blo 595291 673987 := bstep (se 1 (by rfl) ⟨505490, by rfl⟩ : syracuseStep 673987 = 1010981) B1010981
theorem B674131 : Blo 595291 674131 := bstep (se 1 (by rfl) ⟨505598, by rfl⟩ : syracuseStep 674131 = 1011197) B1011197
theorem B2017709 : Blo 595291 2017709 := bstep (se 3 (by rfl) ⟨378320, by rfl⟩ : syracuseStep 2017709 = 756641) B756641
theorem B2017763 : Blo 595291 2017763 := bstep (se 1 (by rfl) ⟨1513322, by rfl⟩ : syracuseStep 2017763 = 3026645) B3026645
theorem B1133041 : Blo 595291 1133041 := bstep (se 2 (by rfl) ⟨424890, by rfl⟩ : syracuseStep 1133041 = 849781) B849781
theorem B2018033 : Blo 595291 2018033 := bstep (se 2 (by rfl) ⟨756762, by rfl⟩ : syracuseStep 2018033 = 1513525) B1513525
theorem B1362691 : Blo 595291 1362691 := bstep (se 1 (by rfl) ⟨1022018, by rfl⟩ : syracuseStep 1362691 = 2044037) B2044037
theorem B1133443 : Blo 595291 1133443 := bstep (se 1 (by rfl) ⟨850082, by rfl⟩ : syracuseStep 1133443 = 1700165) B1700165
theorem B1133489 : Blo 595291 1133489 := bstep (se 2 (by rfl) ⟨425058, by rfl⟩ : syracuseStep 1133489 = 850117) B850117
theorem B1133777 : Blo 595291 1133777 := bstep (se 2 (by rfl) ⟨425166, by rfl⟩ : syracuseStep 1133777 = 850333) B850333
theorem B1821923 : Blo 595291 1821923 := bstep (se 1 (by rfl) ⟨1366442, by rfl⟩ : syracuseStep 1821923 = 2732885) B2732885
theorem B2018573 : Blo 595291 2018573 := bstep (se 3 (by rfl) ⟨378482, by rfl⟩ : syracuseStep 2018573 = 756965) B756965
theorem B2018627 : Blo 595291 2018627 := bstep (se 1 (by rfl) ⟨1513970, by rfl⟩ : syracuseStep 2018627 = 3027941) B3027941
theorem B806369 : Blo 595291 806369 := bstep (se 2 (by rfl) ⟨302388, by rfl⟩ : syracuseStep 806369 = 604777) B604777
theorem B2870797 : Blo 595291 2870797 := bstep (se 3 (by rfl) ⟨538274, by rfl⟩ : syracuseStep 2870797 = 1076549) B1076549
theorem B2018897 : Blo 595291 2018897 := bstep (se 2 (by rfl) ⟨757086, by rfl⟩ : syracuseStep 2018897 = 1514173) B1514173
theorem B2543345 : Blo 595291 2543345 := bstep (se 2 (by rfl) ⟨953754, by rfl⟩ : syracuseStep 2543345 = 1907509) B1907509
theorem B1134499 : Blo 595291 1134499 := bstep (se 1 (by rfl) ⟨850874, by rfl⟩ : syracuseStep 1134499 = 1701749) B1701749
theorem B2871395 : Blo 595291 2871395 := bstep (se 1 (by rfl) ⟨2153546, by rfl⟩ : syracuseStep 2871395 = 4307093) B4307093
theorem B2019437 : Blo 595291 2019437 := bstep (se 3 (by rfl) ⟨378644, by rfl⟩ : syracuseStep 2019437 = 757289) B757289
theorem B3821681 : Blo 595291 3821681 := bstep (se 2 (by rfl) ⟨1433130, by rfl⟩ : syracuseStep 3821681 = 2866261) B2866261
theorem B1036433 : Blo 595291 1036433 := bstep (se 2 (by rfl) ⟨388662, by rfl⟩ : syracuseStep 1036433 = 777325) B777325
theorem B2019491 : Blo 595291 2019491 := bstep (se 1 (by rfl) ⟨1514618, by rfl⟩ : syracuseStep 2019491 = 3029237) B3029237
theorem B1134947 : Blo 595291 1134947 := bstep (se 1 (by rfl) ⟨851210, by rfl⟩ : syracuseStep 1134947 = 1702421) B1702421
theorem B2019761 : Blo 595291 2019761 := bstep (se 2 (by rfl) ⟨757410, by rfl⟩ : syracuseStep 2019761 = 1514821) B1514821
theorem B1135235 : Blo 595291 1135235 := bstep (se 1 (by rfl) ⟨851426, by rfl⟩ : syracuseStep 1135235 = 1702853) B1702853
theorem B774883 : Blo 595291 774883 := bstep (se 1 (by rfl) ⟨581162, by rfl⟩ : syracuseStep 774883 = 1162325) B1162325
theorem B6476597 : Blo 595291 6476597 := bstep (se 5 (by rfl) ⟨303590, by rfl⟩ : syracuseStep 6476597 = 607181) B607181
theorem B2020301 : Blo 595291 2020301 := bstep (se 3 (by rfl) ⟨378806, by rfl⟩ : syracuseStep 2020301 = 757613) B757613
theorem B3396593 : Blo 595291 3396593 := bstep (se 2 (by rfl) ⟨1273722, by rfl⟩ : syracuseStep 3396593 = 2547445) B2547445
theorem B2020355 : Blo 595291 2020355 := bstep (se 1 (by rfl) ⟨1515266, by rfl⟩ : syracuseStep 2020355 = 3030533) B3030533
theorem B1004609 : Blo 595291 1004609 := bstep (se 2 (by rfl) ⟨376728, by rfl⟩ : syracuseStep 1004609 = 753457) B753457
theorem B1004737 : Blo 595291 1004737 := bstep (se 2 (by rfl) ⟨376776, by rfl⟩ : syracuseStep 1004737 = 753553) B753553
theorem B808147 : Blo 595291 808147 := bstep (se 1 (by rfl) ⟨606110, by rfl⟩ : syracuseStep 808147 = 1212221) B1212221
theorem B1004771 : Blo 595291 1004771 := bstep (se 1 (by rfl) ⟨753578, by rfl⟩ : syracuseStep 1004771 = 1507157) B1507157
theorem B2020625 : Blo 595291 2020625 := bstep (se 2 (by rfl) ⟨757734, by rfl⟩ : syracuseStep 2020625 = 1515469) B1515469
theorem B1004899 : Blo 595291 1004899 := bstep (se 1 (by rfl) ⟨753674, by rfl⟩ : syracuseStep 1004899 = 1507349) B1507349
theorem B1529201 : Blo 595291 1529201 := bstep (se 2 (by rfl) ⟨573450, by rfl⟩ : syracuseStep 1529201 = 1146901) B1146901
theorem B808321 : Blo 595291 808321 := bstep (se 2 (by rfl) ⟨303120, by rfl⟩ : syracuseStep 808321 = 606241) B606241
theorem B808385 : Blo 595291 808385 := bstep (se 2 (by rfl) ⟨303144, by rfl⟩ : syracuseStep 808385 = 606289) B606289
theorem B1005041 : Blo 595291 1005041 := bstep (se 2 (by rfl) ⟨376890, by rfl⟩ : syracuseStep 1005041 = 753781) B753781
theorem B1136177 : Blo 595291 1136177 := bstep (se 2 (by rfl) ⟨426066, by rfl⟩ : syracuseStep 1136177 = 852133) B852133
theorem B4544099 : Blo 595291 4544099 := bstep (se 1 (by rfl) ⟨3408074, by rfl⟩ : syracuseStep 4544099 = 6816149) B6816149
theorem B1005169 : Blo 595291 1005169 := bstep (se 2 (by rfl) ⟨376938, by rfl⟩ : syracuseStep 1005169 = 753877) B753877
theorem B1005203 : Blo 595291 1005203 := bstep (se 1 (by rfl) ⟨753902, by rfl⟩ : syracuseStep 1005203 = 1507805) B1507805
theorem B2152163 : Blo 595291 2152163 := bstep (se 1 (by rfl) ⟨1614122, by rfl⟩ : syracuseStep 2152163 = 3228245) B3228245
theorem B1005331 : Blo 595291 1005331 := bstep (se 1 (by rfl) ⟨753998, by rfl⟩ : syracuseStep 1005331 = 1507997) B1507997
theorem B2021165 : Blo 595291 2021165 := bstep (se 3 (by rfl) ⟨378968, by rfl⟩ : syracuseStep 2021165 = 757937) B757937
theorem B2152291 : Blo 595291 2152291 := bstep (se 1 (by rfl) ⟨1614218, by rfl⟩ : syracuseStep 2152291 = 3228437) B3228437
theorem B2021219 : Blo 595291 2021219 := bstep (se 1 (by rfl) ⟨1515914, by rfl⟩ : syracuseStep 2021219 = 3031829) B3031829
theorem B972691 : Blo 595291 972691 := bstep (se 1 (by rfl) ⟨729518, by rfl⟩ : syracuseStep 972691 = 1459037) B1459037
theorem B1005473 : Blo 595291 1005473 := bstep (se 2 (by rfl) ⟨377052, by rfl⟩ : syracuseStep 1005473 = 754105) B754105
theorem B1005601 : Blo 595291 1005601 := bstep (se 2 (by rfl) ⟨377100, by rfl⟩ : syracuseStep 1005601 = 754201) B754201
theorem B1005635 : Blo 595291 1005635 := bstep (se 1 (by rfl) ⟨754226, by rfl⟩ : syracuseStep 1005635 = 1508453) B1508453
theorem B1529969 : Blo 595291 1529969 := bstep (se 2 (by rfl) ⟨573738, by rfl⟩ : syracuseStep 1529969 = 1147477) B1147477
theorem B2021489 : Blo 595291 2021489 := bstep (se 2 (by rfl) ⟨758058, by rfl⟩ : syracuseStep 2021489 = 1516117) B1516117
theorem B2545805 : Blo 595291 2545805 := bstep (se 3 (by rfl) ⟨477338, by rfl⟩ : syracuseStep 2545805 = 954677) B954677
theorem B809137 : Blo 595291 809137 := bstep (se 2 (by rfl) ⟨303426, by rfl⟩ : syracuseStep 809137 = 606853) B606853
theorem B1005763 : Blo 595291 1005763 := bstep (se 1 (by rfl) ⟨754322, by rfl⟩ : syracuseStep 1005763 = 1508645) B1508645
theorem B1005905 : Blo 595291 1005905 := bstep (se 2 (by rfl) ⟨377214, by rfl⟩ : syracuseStep 1005905 = 754429) B754429
theorem B3398051 : Blo 595291 3398051 := bstep (se 1 (by rfl) ⟨2548538, by rfl⟩ : syracuseStep 3398051 = 5097077) B5097077
theorem B1137073 : Blo 595291 1137073 := bstep (se 2 (by rfl) ⟨426402, by rfl⟩ : syracuseStep 1137073 = 852805) B852805
theorem B1006033 : Blo 595291 1006033 := bstep (se 2 (by rfl) ⟨377262, by rfl⟩ : syracuseStep 1006033 = 754525) B754525
theorem B2546147 : Blo 595291 2546147 := bstep (se 1 (by rfl) ⟨1909610, by rfl⟩ : syracuseStep 2546147 = 3819221) B3819221
theorem B1006067 : Blo 595291 1006067 := bstep (se 1 (by rfl) ⟨754550, by rfl⟩ : syracuseStep 1006067 = 1509101) B1509101
theorem B1137233 : Blo 595291 1137233 := bstep (se 2 (by rfl) ⟨426462, by rfl⟩ : syracuseStep 1137233 = 852925) B852925
theorem B1006195 : Blo 595291 1006195 := bstep (se 1 (by rfl) ⟨754646, by rfl⟩ : syracuseStep 1006195 = 1509293) B1509293
theorem B2022029 : Blo 595291 2022029 := bstep (se 3 (by rfl) ⟨379130, by rfl⟩ : syracuseStep 2022029 = 758261) B758261
theorem B2022083 : Blo 595291 2022083 := bstep (se 1 (by rfl) ⟨1516562, by rfl⟩ : syracuseStep 2022083 = 3033125) B3033125
theorem B1006337 : Blo 595291 1006337 := bstep (se 2 (by rfl) ⟨377376, by rfl⟩ : syracuseStep 1006337 = 754753) B754753
theorem B1006465 : Blo 595291 1006465 := bstep (se 2 (by rfl) ⟨377424, by rfl⟩ : syracuseStep 1006465 = 754849) B754849
theorem B1006499 : Blo 595291 1006499 := bstep (se 1 (by rfl) ⟨754874, by rfl⟩ : syracuseStep 1006499 = 1509749) B1509749
theorem B2022353 : Blo 595291 2022353 := bstep (se 2 (by rfl) ⟨758382, by rfl⟩ : syracuseStep 2022353 = 1516765) B1516765
theorem B678883 : Blo 595291 678883 := bstep (se 1 (by rfl) ⟨509162, by rfl⟩ : syracuseStep 678883 = 1018325) B1018325
theorem B1137635 : Blo 595291 1137635 := bstep (se 1 (by rfl) ⟨853226, by rfl⟩ : syracuseStep 1137635 = 1706453) B1706453
theorem B3824653 : Blo 595291 3824653 := bstep (se 3 (by rfl) ⟨717122, by rfl⟩ : syracuseStep 3824653 = 1434245) B1434245
theorem B1006627 : Blo 595291 1006627 := bstep (se 1 (by rfl) ⟨754970, by rfl⟩ : syracuseStep 1006627 = 1509941) B1509941
theorem B1006769 : Blo 595291 1006769 := bstep (se 2 (by rfl) ⟨377538, by rfl⟩ : syracuseStep 1006769 = 755077) B755077
theorem B1006897 : Blo 595291 1006897 := bstep (se 2 (by rfl) ⟨377586, by rfl⟩ : syracuseStep 1006897 = 755173) B755173
theorem B1989965 : Blo 595291 1989965 := bstep (se 3 (by rfl) ⟨373118, by rfl⟩ : syracuseStep 1989965 = 746237) B746237
theorem B1006931 : Blo 595291 1006931 := bstep (se 1 (by rfl) ⟨755198, by rfl⟩ : syracuseStep 1006931 = 1510397) B1510397
theorem B1007059 : Blo 595291 1007059 := bstep (se 1 (by rfl) ⟨755294, by rfl⟩ : syracuseStep 1007059 = 1510589) B1510589
theorem B908801 : Blo 595291 908801 := bstep (se 2 (by rfl) ⟨340800, by rfl⟩ : syracuseStep 908801 = 681601) B681601
theorem B1007201 : Blo 595291 1007201 := bstep (se 2 (by rfl) ⟨377700, by rfl⟩ : syracuseStep 1007201 = 755401) B755401
theorem B2875085 : Blo 595291 2875085 := bstep (se 3 (by rfl) ⟨539078, by rfl⟩ : syracuseStep 2875085 = 1078157) B1078157
theorem B1007329 : Blo 595291 1007329 := bstep (se 2 (by rfl) ⟨377748, by rfl⟩ : syracuseStep 1007329 = 755497) B755497
theorem B1007363 : Blo 595291 1007363 := bstep (se 1 (by rfl) ⟨755522, by rfl⟩ : syracuseStep 1007363 = 1511045) B1511045
theorem B7757621 : Blo 595291 7757621 := bstep (se 5 (by rfl) ⟨363638, by rfl⟩ : syracuseStep 7757621 = 727277) B727277
theorem B1007491 : Blo 595291 1007491 := bstep (se 1 (by rfl) ⟨755618, by rfl⟩ : syracuseStep 1007491 = 1511237) B1511237
theorem B7757795 : Blo 595291 7757795 := bstep (se 1 (by rfl) ⟨5818346, by rfl⟩ : syracuseStep 7757795 = 11636693) B11636693
theorem B1007633 : Blo 595291 1007633 := bstep (se 2 (by rfl) ⟨377862, by rfl⟩ : syracuseStep 1007633 = 755725) B755725
theorem B1007761 : Blo 595291 1007761 := bstep (se 2 (by rfl) ⟨377910, by rfl⟩ : syracuseStep 1007761 = 755821) B755821
theorem B1695917 : Blo 595291 1695917 := bstep (se 3 (by rfl) ⟨317984, by rfl⟩ : syracuseStep 1695917 = 635969) B635969
theorem B1007795 : Blo 595291 1007795 := bstep (se 1 (by rfl) ⟨755846, by rfl⟩ : syracuseStep 1007795 = 1511693) B1511693
theorem B2154701 : Blo 595291 2154701 := bstep (se 3 (by rfl) ⟨404006, by rfl⟩ : syracuseStep 2154701 = 808013) B808013
theorem B1007923 : Blo 595291 1007923 := bstep (se 1 (by rfl) ⟨755942, by rfl⟩ : syracuseStep 1007923 = 1511885) B1511885
theorem B1696099 : Blo 595291 1696099 := bstep (se 1 (by rfl) ⟨1272074, by rfl⟩ : syracuseStep 1696099 = 2544149) B2544149
theorem B1008065 : Blo 595291 1008065 := bstep (se 2 (by rfl) ⟨378024, by rfl⟩ : syracuseStep 1008065 = 756049) B756049
theorem B1008193 : Blo 595291 1008193 := bstep (se 2 (by rfl) ⟨378072, by rfl⟩ : syracuseStep 1008193 = 756145) B756145
theorem B1008227 : Blo 595291 1008227 := bstep (se 1 (by rfl) ⟨756170, by rfl⟩ : syracuseStep 1008227 = 1512341) B1512341
theorem B1008355 : Blo 595291 1008355 := bstep (se 1 (by rfl) ⟨756266, by rfl⟩ : syracuseStep 1008355 = 1512533) B1512533
theorem B1696589 : Blo 595291 1696589 := bstep (se 3 (by rfl) ⟨318110, by rfl⟩ : syracuseStep 1696589 = 636221) B636221
theorem B1434467 : Blo 595291 1434467 := bstep (se 1 (by rfl) ⟨1075850, by rfl⟩ : syracuseStep 1434467 = 2151701) B2151701
theorem B1008497 : Blo 595291 1008497 := bstep (se 2 (by rfl) ⟨378186, by rfl⟩ : syracuseStep 1008497 = 756373) B756373
theorem B2155405 : Blo 595291 2155405 := bstep (se 3 (by rfl) ⟨404138, by rfl⟩ : syracuseStep 2155405 = 808277) B808277
theorem B1106833 : Blo 595291 1106833 := bstep (se 2 (by rfl) ⟨415062, by rfl⟩ : syracuseStep 1106833 = 830125) B830125
theorem B680899 : Blo 595291 680899 := bstep (se 1 (by rfl) ⟨510674, by rfl⟩ : syracuseStep 680899 = 1021349) B1021349
theorem B1729507 : Blo 595291 1729507 := bstep (se 1 (by rfl) ⟨1297130, by rfl⟩ : syracuseStep 1729507 = 2594261) B2594261
theorem B1008625 : Blo 595291 1008625 := bstep (se 2 (by rfl) ⟨378234, by rfl⟩ : syracuseStep 1008625 = 756469) B756469
theorem B1008659 : Blo 595291 1008659 := bstep (se 1 (by rfl) ⟨756494, by rfl⟩ : syracuseStep 1008659 = 1512989) B1512989
theorem B1008787 : Blo 595291 1008787 := bstep (se 1 (by rfl) ⟨756590, by rfl⟩ : syracuseStep 1008787 = 1513181) B1513181
theorem B910529 : Blo 595291 910529 := bstep (se 2 (by rfl) ⟨341448, by rfl⟩ : syracuseStep 910529 = 682897) B682897
theorem B3826885 : Blo 595291 3826885 := bstep (se 4 (by rfl) ⟨358770, by rfl⟩ : syracuseStep 3826885 = 717541) B717541
theorem B1008929 : Blo 595291 1008929 := bstep (se 2 (by rfl) ⟨378348, by rfl⟩ : syracuseStep 1008929 = 756697) B756697
theorem B1074467 : Blo 595291 1074467 := bstep (se 1 (by rfl) ⟨805850, by rfl⟩ : syracuseStep 1074467 = 1611701) B1611701
theorem B1009057 : Blo 595291 1009057 := bstep (se 2 (by rfl) ⟨378396, by rfl⟩ : syracuseStep 1009057 = 756793) B756793
theorem B1009091 : Blo 595291 1009091 := bstep (se 1 (by rfl) ⟨756818, by rfl⟩ : syracuseStep 1009091 = 1513637) B1513637
theorem B25781813 : Blo 595291 25781813 := bstep (se 5 (by rfl) ⟨1208522, by rfl⟩ : syracuseStep 25781813 = 2417045) B2417045
theorem B1009219 : Blo 595291 1009219 := bstep (se 1 (by rfl) ⟨756914, by rfl⟩ : syracuseStep 1009219 = 1513829) B1513829
theorem B910931 : Blo 595291 910931 := bstep (se 1 (by rfl) ⟨683198, by rfl⟩ : syracuseStep 910931 = 1366397) B1366397
theorem B1009361 : Blo 595291 1009361 := bstep (se 2 (by rfl) ⟨378510, by rfl⟩ : syracuseStep 1009361 = 757021) B757021
theorem B1009489 : Blo 595291 1009489 := bstep (se 2 (by rfl) ⟨378558, by rfl⟩ : syracuseStep 1009489 = 757117) B757117
theorem B1009523 : Blo 595291 1009523 := bstep (se 1 (by rfl) ⟨757142, by rfl⟩ : syracuseStep 1009523 = 1514285) B1514285
theorem B1697773 : Blo 595291 1697773 := bstep (se 3 (by rfl) ⟨318332, by rfl⟩ : syracuseStep 1697773 = 636665) B636665
theorem B1009651 : Blo 595291 1009651 := bstep (se 1 (by rfl) ⟨757238, by rfl⟩ : syracuseStep 1009651 = 1514477) B1514477
theorem B682067 : Blo 595291 682067 := bstep (se 1 (by rfl) ⟨511550, by rfl⟩ : syracuseStep 682067 = 1023101) B1023101
theorem B1108081 : Blo 595291 1108081 := bstep (se 2 (by rfl) ⟨415530, by rfl⟩ : syracuseStep 1108081 = 831061) B831061
theorem B1009793 : Blo 595291 1009793 := bstep (se 2 (by rfl) ⟨378672, by rfl⟩ : syracuseStep 1009793 = 757345) B757345
theorem B2418929 : Blo 595291 2418929 := bstep (se 2 (by rfl) ⟨907098, by rfl⟩ : syracuseStep 2418929 = 1814197) B1814197
theorem B1009921 : Blo 595291 1009921 := bstep (se 2 (by rfl) ⟨378720, by rfl⟩ : syracuseStep 1009921 = 757441) B757441
theorem B1009955 : Blo 595291 1009955 := bstep (se 1 (by rfl) ⟨757466, by rfl⟩ : syracuseStep 1009955 = 1514933) B1514933
theorem B2550179 : Blo 595291 2550179 := bstep (se 1 (by rfl) ⟨1912634, by rfl⟩ : syracuseStep 2550179 = 3825269) B3825269
theorem B1010083 : Blo 595291 1010083 := bstep (se 1 (by rfl) ⟨757562, by rfl⟩ : syracuseStep 1010083 = 1515125) B1515125
theorem B3631601 : Blo 595291 3631601 := bstep (se 2 (by rfl) ⟨1361850, by rfl⟩ : syracuseStep 3631601 = 2723701) B2723701
theorem B1010225 : Blo 595291 1010225 := bstep (se 2 (by rfl) ⟨378834, by rfl⟩ : syracuseStep 1010225 = 757669) B757669
theorem B3238469 : Blo 595291 3238469 := bstep (se 4 (by rfl) ⟨303606, by rfl⟩ : syracuseStep 3238469 = 607213) B607213
theorem B1010353 : Blo 595291 1010353 := bstep (se 2 (by rfl) ⟨378882, by rfl⟩ : syracuseStep 1010353 = 757765) B757765
theorem B1010387 : Blo 595291 1010387 := bstep (se 1 (by rfl) ⟨757790, by rfl⟩ : syracuseStep 1010387 = 1515581) B1515581
theorem B11627317 : Blo 595291 11627317 := bstep (se 5 (by rfl) ⟨545030, by rfl⟩ : syracuseStep 11627317 = 1090061) B1090061
theorem B4549445 : Blo 595291 4549445 := bstep (se 4 (by rfl) ⟨426510, by rfl⟩ : syracuseStep 4549445 = 853021) B853021
theorem B1010515 : Blo 595291 1010515 := bstep (se 1 (by rfl) ⟨757886, by rfl⟩ : syracuseStep 1010515 = 1515773) B1515773
theorem B17198021 : Blo 595291 17198021 := bstep (se 4 (by rfl) ⟨1612314, by rfl⟩ : syracuseStep 17198021 = 3224629) B3224629
theorem B1010657 : Blo 595291 1010657 := bstep (se 2 (by rfl) ⟨378996, by rfl⟩ : syracuseStep 1010657 = 757993) B757993
theorem B1698833 : Blo 595291 1698833 := bstep (se 2 (by rfl) ⟨637062, by rfl⟩ : syracuseStep 1698833 = 1274125) B1274125
theorem B1010785 : Blo 595291 1010785 := bstep (se 2 (by rfl) ⟨379044, by rfl⟩ : syracuseStep 1010785 = 758089) B758089
theorem B1010819 : Blo 595291 1010819 := bstep (se 1 (by rfl) ⟨758114, by rfl⟩ : syracuseStep 1010819 = 1516229) B1516229
theorem B1010947 : Blo 595291 1010947 := bstep (se 1 (by rfl) ⟨758210, by rfl⟩ : syracuseStep 1010947 = 1516421) B1516421
theorem B1011089 : Blo 595291 1011089 := bstep (se 2 (by rfl) ⟨379158, by rfl⟩ : syracuseStep 1011089 = 758317) B758317
theorem B1535441 : Blo 595291 1535441 := bstep (se 2 (by rfl) ⟨575790, by rfl⟩ : syracuseStep 1535441 = 1151581) B1151581
theorem B1011217 : Blo 595291 1011217 := bstep (se 2 (by rfl) ⟨379206, by rfl⟩ : syracuseStep 1011217 = 758413) B758413
theorem B1011251 : Blo 595291 1011251 := bstep (se 1 (by rfl) ⟨758438, by rfl⟩ : syracuseStep 1011251 = 1516877) B1516877
theorem B2551409 : Blo 595291 2551409 := bstep (se 2 (by rfl) ⟨956778, by rfl⟩ : syracuseStep 2551409 = 1913557) B1913557
theorem B9203341 : Blo 595291 9203341 := bstep (se 3 (by rfl) ⟨1725626, by rfl⟩ : syracuseStep 9203341 = 3451253) B3451253
theorem B1699505 : Blo 595291 1699505 := bstep (se 2 (by rfl) ⟨637314, by rfl⟩ : syracuseStep 1699505 = 1274629) B1274629
theorem B5730061 : Blo 595291 5730061 := bstep (se 3 (by rfl) ⟨1074386, by rfl⟩ : syracuseStep 5730061 = 2148773) B2148773
theorem B8613773 : Blo 595291 8613773 := bstep (se 3 (by rfl) ⟨1615082, by rfl⟩ : syracuseStep 8613773 = 3230165) B3230165
theorem B1077155 : Blo 595291 1077155 := bstep (se 1 (by rfl) ⟨807866, by rfl⟩ : syracuseStep 1077155 = 1615733) B1615733
theorem B847793 : Blo 595291 847793 := bstep (se 2 (by rfl) ⟨317922, by rfl⟩ : syracuseStep 847793 = 635845) B635845
theorem B1339505 : Blo 595291 1339505 := bstep (se 2 (by rfl) ⟨502314, by rfl⟩ : syracuseStep 1339505 = 1004629) B1004629
theorem B1339523 : Blo 595291 1339523 := bstep (se 1 (by rfl) ⟨1004642, by rfl⟩ : syracuseStep 1339523 = 2009285) B2009285
theorem B1437859 : Blo 595291 1437859 := bstep (se 1 (by rfl) ⟨1078394, by rfl⟩ : syracuseStep 1437859 = 2156789) B2156789
theorem B1438033 : Blo 595291 1438033 := bstep (se 2 (by rfl) ⟨539262, by rfl⟩ : syracuseStep 1438033 = 1078525) B1078525
theorem B1077617 : Blo 595291 1077617 := bstep (se 2 (by rfl) ⟨404106, by rfl⟩ : syracuseStep 1077617 = 808213) B808213
theorem B1339793 : Blo 595291 1339793 := bstep (se 2 (by rfl) ⟨502422, by rfl⟩ : syracuseStep 1339793 = 1004845) B1004845
theorem B1339811 : Blo 595291 1339811 := bstep (se 1 (by rfl) ⟨1004858, by rfl⟩ : syracuseStep 1339811 = 2009717) B2009717
theorem B848323 : Blo 595291 848323 := bstep (se 1 (by rfl) ⟨636242, by rfl⟩ : syracuseStep 848323 = 1272485) B1272485
theorem B1700291 : Blo 595291 1700291 := bstep (se 1 (by rfl) ⟨1275218, by rfl⟩ : syracuseStep 1700291 = 2550437) B2550437
theorem B1274467 : Blo 595291 1274467 := bstep (se 1 (by rfl) ⟨955850, by rfl⟩ : syracuseStep 1274467 = 1911701) B1911701
theorem B1340081 : Blo 595291 1340081 := bstep (se 2 (by rfl) ⟨502530, by rfl⟩ : syracuseStep 1340081 = 1005061) B1005061
theorem B1340099 : Blo 595291 1340099 := bstep (se 1 (by rfl) ⟨1005074, by rfl⟩ : syracuseStep 1340099 = 2010149) B2010149
theorem B1700621 : Blo 595291 1700621 := bstep (se 3 (by rfl) ⟨318866, by rfl⟩ : syracuseStep 1700621 = 637733) B637733
theorem B848659 : Blo 595291 848659 := bstep (se 1 (by rfl) ⟨636494, by rfl⟩ : syracuseStep 848659 = 1272989) B1272989
theorem B1700689 : Blo 595291 1700689 := bstep (se 2 (by rfl) ⟨637758, by rfl⟩ : syracuseStep 1700689 = 1275517) B1275517
theorem B1340369 : Blo 595291 1340369 := bstep (se 2 (by rfl) ⟨502638, by rfl⟩ : syracuseStep 1340369 = 1005277) B1005277
theorem B1340387 : Blo 595291 1340387 := bstep (se 1 (by rfl) ⟨1005290, by rfl⟩ : syracuseStep 1340387 = 2010581) B2010581
theorem B1700963 : Blo 595291 1700963 := bstep (se 1 (by rfl) ⟨1275722, by rfl⟩ : syracuseStep 1700963 = 2551445) B2551445
theorem B1340657 : Blo 595291 1340657 := bstep (se 2 (by rfl) ⟨502746, by rfl⟩ : syracuseStep 1340657 = 1005493) B1005493
theorem B1340675 : Blo 595291 1340675 := bstep (se 1 (by rfl) ⟨1005506, by rfl⟩ : syracuseStep 1340675 = 2011013) B2011013
theorem B849217 : Blo 595291 849217 := bstep (se 2 (by rfl) ⟨318456, by rfl⟩ : syracuseStep 849217 = 636913) B636913
theorem B849251 : Blo 595291 849251 := bstep (se 1 (by rfl) ⟨636938, by rfl⟩ : syracuseStep 849251 = 1273877) B1273877
theorem B1570211 : Blo 595291 1570211 := bstep (se 1 (by rfl) ⟨1177658, by rfl⟩ : syracuseStep 1570211 = 2355317) B2355317
theorem B4093411 : Blo 595291 4093411 := bstep (se 1 (by rfl) ⟨3070058, by rfl⟩ : syracuseStep 4093411 = 6140117) B6140117
theorem B1340945 : Blo 595291 1340945 := bstep (se 2 (by rfl) ⟨502854, by rfl⟩ : syracuseStep 1340945 = 1005709) B1005709
theorem B1340963 : Blo 595291 1340963 := bstep (se 1 (by rfl) ⟨1005722, by rfl⟩ : syracuseStep 1340963 = 2011445) B2011445
theorem B12285553 : Blo 595291 12285553 := bstep (se 2 (by rfl) ⟨4607082, by rfl⟩ : syracuseStep 12285553 = 9214165) B9214165
theorem B1341233 : Blo 595291 1341233 := bstep (se 2 (by rfl) ⟨502962, by rfl⟩ : syracuseStep 1341233 = 1005925) B1005925
theorem B1341251 : Blo 595291 1341251 := bstep (se 1 (by rfl) ⟨1005938, by rfl⟩ : syracuseStep 1341251 = 2011877) B2011877
theorem B1210211 : Blo 595291 1210211 := bstep (se 1 (by rfl) ⟨907658, by rfl⟩ : syracuseStep 1210211 = 1815317) B1815317
theorem B1210243 : Blo 595291 1210243 := bstep (se 1 (by rfl) ⟨907682, by rfl⟩ : syracuseStep 1210243 = 1815365) B1815365
theorem B849809 : Blo 595291 849809 := bstep (se 2 (by rfl) ⟨318678, by rfl⟩ : syracuseStep 849809 = 637357) B637357
theorem B1701805 : Blo 595291 1701805 := bstep (se 3 (by rfl) ⟨319088, by rfl⟩ : syracuseStep 1701805 = 638177) B638177
theorem B849889 : Blo 595291 849889 := bstep (se 2 (by rfl) ⟨318708, by rfl⟩ : syracuseStep 849889 = 637417) B637417
theorem B16316387 : Blo 595291 16316387 := bstep (se 1 (by rfl) ⟨12237290, by rfl⟩ : syracuseStep 16316387 = 24474581) B24474581
theorem B2553869 : Blo 595291 2553869 := bstep (se 3 (by rfl) ⟨478850, by rfl⟩ : syracuseStep 2553869 = 957701) B957701
theorem B1701965 : Blo 595291 1701965 := bstep (se 3 (by rfl) ⟨319118, by rfl⟩ : syracuseStep 1701965 = 638237) B638237
theorem B1341521 : Blo 595291 1341521 := bstep (se 2 (by rfl) ⟨503070, by rfl⟩ : syracuseStep 1341521 = 1006141) B1006141
theorem B1341539 : Blo 595291 1341539 := bstep (se 1 (by rfl) ⟨1006154, by rfl⟩ : syracuseStep 1341539 = 2012309) B2012309
theorem B948323 : Blo 595291 948323 := bstep (se 1 (by rfl) ⟨711242, by rfl⟩ : syracuseStep 948323 = 1422485) B1422485
theorem B1702147 : Blo 595291 1702147 := bstep (se 1 (by rfl) ⟨1276610, by rfl⟩ : syracuseStep 1702147 = 2553221) B2553221
theorem B1341809 : Blo 595291 1341809 := bstep (se 2 (by rfl) ⟨503178, by rfl⟩ : syracuseStep 1341809 = 1006357) B1006357
theorem B1341827 : Blo 595291 1341827 := bstep (se 1 (by rfl) ⟨1006370, by rfl⟩ : syracuseStep 1341827 = 2012741) B2012741
theorem B1276337 : Blo 595291 1276337 := bstep (se 2 (by rfl) ⟨478626, by rfl⟩ : syracuseStep 1276337 = 957253) B957253
theorem B2718157 : Blo 595291 2718157 := bstep (se 3 (by rfl) ⟨509654, by rfl⟩ : syracuseStep 2718157 = 1019309) B1019309
theorem B1342097 : Blo 595291 1342097 := bstep (se 2 (by rfl) ⟨503286, by rfl⟩ : syracuseStep 1342097 = 1006573) B1006573
theorem B1342115 : Blo 595291 1342115 := bstep (se 1 (by rfl) ⟨1006586, by rfl⟩ : syracuseStep 1342115 = 2013173) B2013173
theorem B850675 : Blo 595291 850675 := bstep (se 1 (by rfl) ⟨638006, by rfl⟩ : syracuseStep 850675 = 1276013) B1276013
theorem B1211249 : Blo 595291 1211249 := bstep (se 2 (by rfl) ⟨454218, by rfl⟩ : syracuseStep 1211249 = 908437) B908437
theorem B1342385 : Blo 595291 1342385 := bstep (se 2 (by rfl) ⟨503394, by rfl⟩ : syracuseStep 1342385 = 1006789) B1006789
theorem B1342403 : Blo 595291 1342403 := bstep (se 1 (by rfl) ⟨1006802, by rfl⟩ : syracuseStep 1342403 = 2013605) B2013605
theorem B6814691 : Blo 595291 6814691 := bstep (se 1 (by rfl) ⟨5111018, by rfl⟩ : syracuseStep 6814691 = 10222037) B10222037
theorem B719939 : Blo 595291 719939 := bstep (se 1 (by rfl) ⟨539954, by rfl⟩ : syracuseStep 719939 = 1079909) B1079909
theorem B5110883 : Blo 595291 5110883 := bstep (se 1 (by rfl) ⟨3833162, by rfl⟩ : syracuseStep 5110883 = 7666325) B7666325
theorem B3406981 : Blo 595291 3406981 := bstep (se 4 (by rfl) ⟨319404, by rfl⟩ : syracuseStep 3406981 = 638809) B638809
theorem B1342673 : Blo 595291 1342673 := bstep (se 2 (by rfl) ⟨503502, by rfl⟩ : syracuseStep 1342673 = 1007005) B1007005
theorem B851153 : Blo 595291 851153 := bstep (se 2 (by rfl) ⟨319182, by rfl⟩ : syracuseStep 851153 = 638365) B638365
theorem B55934165 : Blo 595291 55934165 := bstep (se 7 (by rfl) ⟨655478, by rfl⟩ : syracuseStep 55934165 = 1310957) B1310957
theorem B49544419 : Blo 595291 49544419 := bstep (se 1 (by rfl) ⟨37158314, by rfl⟩ : syracuseStep 49544419 = 74316629) B74316629
theorem B1342691 : Blo 595291 1342691 := bstep (se 1 (by rfl) ⟨1007018, by rfl⟩ : syracuseStep 1342691 = 2014037) B2014037
theorem B1277201 : Blo 595291 1277201 := bstep (se 2 (by rfl) ⟨478950, by rfl⟩ : syracuseStep 1277201 = 957901) B957901
theorem B851267 : Blo 595291 851267 := bstep (se 1 (by rfl) ⟨638450, by rfl⟩ : syracuseStep 851267 = 1276901) B1276901
theorem B851347 : Blo 595291 851347 := bstep (se 1 (by rfl) ⟨638510, by rfl⟩ : syracuseStep 851347 = 1277021) B1277021
theorem B1342961 : Blo 595291 1342961 := bstep (se 2 (by rfl) ⟨503610, by rfl⟩ : syracuseStep 1342961 = 1007221) B1007221
theorem B1342979 : Blo 595291 1342979 := bstep (se 1 (by rfl) ⟨1007234, by rfl⟩ : syracuseStep 1342979 = 2014469) B2014469
theorem B2260493 : Blo 595291 2260493 := bstep (se 3 (by rfl) ⟨423842, by rfl⟩ : syracuseStep 2260493 = 847685) B847685
theorem B1506833 : Blo 595291 1506833 := bstep (se 2 (by rfl) ⟨565062, by rfl⟩ : syracuseStep 1506833 = 1130125) B1130125
theorem B1506883 : Blo 595291 1506883 := bstep (se 1 (by rfl) ⟨1130162, by rfl⟩ : syracuseStep 1506883 = 2260325) B2260325
theorem B1703537 : Blo 595291 1703537 := bstep (se 2 (by rfl) ⟨638826, by rfl⟩ : syracuseStep 1703537 = 1277653) B1277653
theorem B1507025 : Blo 595291 1507025 := bstep (se 2 (by rfl) ⟨565134, by rfl⟩ : syracuseStep 1507025 = 1130269) B1130269
theorem B1343249 : Blo 595291 1343249 := bstep (se 2 (by rfl) ⟨503718, by rfl⟩ : syracuseStep 1343249 = 1007437) B1007437
theorem B1343267 : Blo 595291 1343267 := bstep (se 1 (by rfl) ⟨1007450, by rfl⟩ : syracuseStep 1343267 = 2014901) B2014901
theorem B2719601 : Blo 595291 2719601 := bstep (se 2 (by rfl) ⟨1019850, by rfl⟩ : syracuseStep 2719601 = 2039701) B2039701
theorem B851905 : Blo 595291 851905 := bstep (se 2 (by rfl) ⟨319464, by rfl⟩ : syracuseStep 851905 = 638929) B638929
theorem B753619 : Blo 595291 753619 := bstep (se 1 (by rfl) ⟨565214, by rfl⟩ : syracuseStep 753619 = 1130429) B1130429
theorem B5111909 : Blo 595291 5111909 := bstep (se 4 (by rfl) ⟨479241, by rfl⟩ : syracuseStep 5111909 = 958483) B958483
theorem B1343627 : Blo 595291 1343627 := bstep (se 1 (by rfl) ⟨1007720, by rfl⟩ : syracuseStep 1343627 = 2015441) B2015441
theorem B3440819 : Blo 595291 3440819 := bstep (se 1 (by rfl) ⟨2580614, by rfl⟩ : syracuseStep 3440819 = 5161229) B5161229
theorem B1343681 : Blo 595291 1343681 := bstep (se 2 (by rfl) ⟨503880, by rfl⟩ : syracuseStep 1343681 = 1007761) B1007761
theorem B1507531 : Blo 595291 1507531 := bstep (se 1 (by rfl) ⟨1130648, by rfl⟩ : syracuseStep 1507531 = 2261297) B2261297
theorem B753943 : Blo 595291 753943 := bstep (se 1 (by rfl) ⟨565457, by rfl⟩ : syracuseStep 753943 = 1130915) B1130915
theorem B2490689 : Blo 595291 2490689 := bstep (se 2 (by rfl) ⟨934008, by rfl⟩ : syracuseStep 2490689 = 1868017) B1868017
theorem B1507673 : Blo 595291 1507673 := bstep (se 2 (by rfl) ⟨565377, by rfl⟩ : syracuseStep 1507673 = 1130755) B1130755
theorem B1343897 : Blo 595291 1343897 := bstep (se 2 (by rfl) ⟨503961, by rfl⟩ : syracuseStep 1343897 = 1007923) B1007923
theorem B2261465 : Blo 595291 2261465 := bstep (se 2 (by rfl) ⟨848049, by rfl⟩ : syracuseStep 2261465 = 1696099) B1696099
theorem B1343987 : Blo 595291 1343987 := bstep (se 1 (by rfl) ⟨1007990, by rfl⟩ : syracuseStep 1343987 = 2015981) B2015981
theorem B1344023 : Blo 595291 1344023 := bstep (se 1 (by rfl) ⟨1008017, by rfl⟩ : syracuseStep 1344023 = 2016035) B2016035
theorem B1245719 : Blo 595291 1245719 := bstep (se 1 (by rfl) ⟨934289, by rfl⟩ : syracuseStep 1245719 = 1868579) B1868579
theorem B2556467 : Blo 595291 2556467 := bstep (se 1 (by rfl) ⟨1917350, by rfl⟩ : syracuseStep 2556467 = 3834701) B3834701
theorem B1344203 : Blo 595291 1344203 := bstep (se 1 (by rfl) ⟨1008152, by rfl⟩ : syracuseStep 1344203 = 2016305) B2016305
theorem B1704665 : Blo 595291 1704665 := bstep (se 2 (by rfl) ⟨639249, by rfl⟩ : syracuseStep 1704665 = 1278499) B1278499
theorem B852697 : Blo 595291 852697 := bstep (se 2 (by rfl) ⟨319761, by rfl⟩ : syracuseStep 852697 = 639523) B639523
theorem B1344257 : Blo 595291 1344257 := bstep (se 2 (by rfl) ⟨504096, by rfl⟩ : syracuseStep 1344257 = 1008193) B1008193
theorem B2261783 : Blo 595291 2261783 := bstep (se 1 (by rfl) ⟨1696337, by rfl⟩ : syracuseStep 2261783 = 3392675) B3392675
theorem B4096919 : Blo 595291 4096919 := bstep (se 1 (by rfl) ⟨3072689, by rfl⟩ : syracuseStep 4096919 = 6145379) B6145379
theorem B3834803 : Blo 595291 3834803 := bstep (se 1 (by rfl) ⟨2876102, by rfl⟩ : syracuseStep 3834803 = 5752205) B5752205
theorem B1344473 : Blo 595291 1344473 := bstep (se 2 (by rfl) ⟨504177, by rfl⟩ : syracuseStep 1344473 = 1008355) B1008355
theorem B1344563 : Blo 595291 1344563 := bstep (se 1 (by rfl) ⟨1008422, by rfl⟩ : syracuseStep 1344563 = 2016845) B2016845
theorem B1344599 : Blo 595291 1344599 := bstep (se 1 (by rfl) ⟨1008449, by rfl⟩ : syracuseStep 1344599 = 2016899) B2016899
theorem B1508503 : Blo 595291 1508503 := bstep (se 1 (by rfl) ⟨1131377, by rfl⟩ : syracuseStep 1508503 = 2262755) B2262755
theorem B1475777 : Blo 595291 1475777 := bstep (se 2 (by rfl) ⟨553416, by rfl⟩ : syracuseStep 1475777 = 1106833) B1106833
theorem B1344779 : Blo 595291 1344779 := bstep (se 1 (by rfl) ⟨1008584, by rfl⟩ : syracuseStep 1344779 = 2017169) B2017169
theorem B3015953 : Blo 595291 3015953 := bstep (se 2 (by rfl) ⟨1130982, by rfl⟩ : syracuseStep 3015953 = 2261965) B2261965
theorem B1344833 : Blo 595291 1344833 := bstep (se 2 (by rfl) ⟨504312, by rfl⟩ : syracuseStep 1344833 = 1008625) B1008625
theorem B1279361 : Blo 595291 1279361 := bstep (se 2 (by rfl) ⟨479760, by rfl⟩ : syracuseStep 1279361 = 959521) B959521
theorem B3016115 : Blo 595291 3016115 := bstep (se 1 (by rfl) ⟨2262086, by rfl⟩ : syracuseStep 3016115 = 4524173) B4524173
theorem B2262451 : Blo 595291 2262451 := bstep (se 1 (by rfl) ⟨1696838, by rfl⟩ : syracuseStep 2262451 = 3393677) B3393677
theorem B1345049 : Blo 595291 1345049 := bstep (se 2 (by rfl) ⟨504393, by rfl⟩ : syracuseStep 1345049 = 1008787) B1008787
theorem B1508939 : Blo 595291 1508939 := bstep (se 1 (by rfl) ⟨1131704, by rfl⟩ : syracuseStep 1508939 = 2263409) B2263409
theorem B1345139 : Blo 595291 1345139 := bstep (se 1 (by rfl) ⟨1008854, by rfl⟩ : syracuseStep 1345139 = 2017709) B2017709
theorem B1345175 : Blo 595291 1345175 := bstep (se 1 (by rfl) ⟨1008881, by rfl⟩ : syracuseStep 1345175 = 2017763) B2017763
theorem B1345355 : Blo 595291 1345355 := bstep (se 1 (by rfl) ⟨1009016, by rfl⟩ : syracuseStep 1345355 = 2018033) B2018033
theorem B1345409 : Blo 595291 1345409 := bstep (se 2 (by rfl) ⟨504528, by rfl⟩ : syracuseStep 1345409 = 1009057) B1009057
theorem B1509313 : Blo 595291 1509313 := bstep (se 2 (by rfl) ⟨565992, by rfl⟩ : syracuseStep 1509313 = 1131985) B1131985
theorem B755659 : Blo 595291 755659 := bstep (se 1 (by rfl) ⟨566744, by rfl⟩ : syracuseStep 755659 = 1133489) B1133489
theorem B12257315 : Blo 595291 12257315 := bstep (se 1 (by rfl) ⟨9192986, by rfl⟩ : syracuseStep 12257315 = 18385973) B18385973
theorem B4294721 : Blo 595291 4294721 := bstep (se 2 (by rfl) ⟨1610520, by rfl⟩ : syracuseStep 4294721 = 3221041) B3221041
theorem B1345625 : Blo 595291 1345625 := bstep (se 2 (by rfl) ⟨504609, by rfl⟩ : syracuseStep 1345625 = 1009219) B1009219
theorem B1214615 : Blo 595291 1214615 := bstep (se 1 (by rfl) ⟨910961, by rfl⟩ : syracuseStep 1214615 = 1821923) B1821923
theorem B1345715 : Blo 595291 1345715 := bstep (se 1 (by rfl) ⟨1009286, by rfl⟩ : syracuseStep 1345715 = 2018573) B2018573
theorem B1345751 : Blo 595291 1345751 := bstep (se 1 (by rfl) ⟨1009313, by rfl⟩ : syracuseStep 1345751 = 2018627) B2018627
theorem B1706305 : Blo 595291 1706305 := bstep (se 2 (by rfl) ⟨639864, by rfl⟩ : syracuseStep 1706305 = 1279729) B1279729
theorem B1345931 : Blo 595291 1345931 := bstep (se 1 (by rfl) ⟨1009448, by rfl⟩ : syracuseStep 1345931 = 2018897) B2018897
theorem B1345985 : Blo 595291 1345985 := bstep (se 2 (by rfl) ⟨504744, by rfl⟩ : syracuseStep 1345985 = 1009489) B1009489
theorem B1509911 : Blo 595291 1509911 := bstep (se 1 (by rfl) ⟨1132433, by rfl⟩ : syracuseStep 1509911 = 2264867) B2264867
theorem B2263697 : Blo 595291 2263697 := bstep (se 2 (by rfl) ⟨848886, by rfl⟩ : syracuseStep 2263697 = 1697773) B1697773
theorem B1346201 : Blo 595291 1346201 := bstep (se 2 (by rfl) ⟨504825, by rfl⟩ : syracuseStep 1346201 = 1009651) B1009651
theorem B5114573 : Blo 595291 5114573 := bstep (se 3 (by rfl) ⟨958982, by rfl⟩ : syracuseStep 5114573 = 1917965) B1917965
theorem B1346291 : Blo 595291 1346291 := bstep (se 1 (by rfl) ⟨1009718, by rfl⟩ : syracuseStep 1346291 = 2019437) B2019437
theorem B690955 : Blo 595291 690955 := bstep (se 1 (by rfl) ⟨518216, by rfl⟩ : syracuseStep 690955 = 1036433) B1036433
theorem B1346327 : Blo 595291 1346327 := bstep (se 1 (by rfl) ⟨1009745, by rfl⟩ : syracuseStep 1346327 = 2019491) B2019491
theorem B1477441 : Blo 595291 1477441 := bstep (se 2 (by rfl) ⟨554040, by rfl⟩ : syracuseStep 1477441 = 1108081) B1108081
theorem B756631 : Blo 595291 756631 := bstep (se 1 (by rfl) ⟨567473, by rfl⟩ : syracuseStep 756631 = 1134947) B1134947
theorem B1346507 : Blo 595291 1346507 := bstep (se 1 (by rfl) ⟨1009880, by rfl⟩ : syracuseStep 1346507 = 2019761) B2019761
theorem B1346561 : Blo 595291 1346561 := bstep (se 2 (by rfl) ⟨504960, by rfl⟩ : syracuseStep 1346561 = 1009921) B1009921
theorem B1346777 : Blo 595291 1346777 := bstep (se 2 (by rfl) ⟨505041, by rfl⟩ : syracuseStep 1346777 = 1010083) B1010083
theorem B2559235 : Blo 595291 2559235 := bstep (se 1 (by rfl) ⟨1919426, by rfl⟩ : syracuseStep 2559235 = 3838853) B3838853
theorem B1346867 : Blo 595291 1346867 := bstep (se 1 (by rfl) ⟨1010150, by rfl⟩ : syracuseStep 1346867 = 2020301) B2020301
theorem B1510721 : Blo 595291 1510721 := bstep (se 2 (by rfl) ⟨566520, by rfl⟩ : syracuseStep 1510721 = 1133041) B1133041
theorem B3018059 : Blo 595291 3018059 := bstep (se 1 (by rfl) ⟨2263544, by rfl⟩ : syracuseStep 3018059 = 4527089) B4527089
theorem B2264395 : Blo 595291 2264395 := bstep (se 1 (by rfl) ⟨1698296, by rfl⟩ : syracuseStep 2264395 = 3396593) B3396593
theorem B1346903 : Blo 595291 1346903 := bstep (se 1 (by rfl) ⟨1010177, by rfl⟩ : syracuseStep 1346903 = 2020355) B2020355
theorem B1347083 : Blo 595291 1347083 := bstep (se 1 (by rfl) ⟨1010312, by rfl⟩ : syracuseStep 1347083 = 2020625) B2020625
theorem B1347137 : Blo 595291 1347137 := bstep (se 2 (by rfl) ⟨505176, by rfl⟩ : syracuseStep 1347137 = 1010353) B1010353
theorem B1019467 : Blo 595291 1019467 := bstep (se 1 (by rfl) ⟨764600, by rfl⟩ : syracuseStep 1019467 = 1529201) B1529201
theorem B2264669 : Blo 595291 2264669 := bstep (se 3 (by rfl) ⟨424625, by rfl⟩ : syracuseStep 2264669 = 849251) B849251
theorem B757451 : Blo 595291 757451 := bstep (se 1 (by rfl) ⟨568088, by rfl⟩ : syracuseStep 757451 = 1136177) B1136177
theorem B15503089 : Blo 595291 15503089 := bstep (se 2 (by rfl) ⟨5813658, by rfl⟩ : syracuseStep 15503089 = 11627317) B11627317
theorem B1347353 : Blo 595291 1347353 := bstep (se 2 (by rfl) ⟨505257, by rfl⟩ : syracuseStep 1347353 = 1010515) B1010515
theorem B1511257 : Blo 595291 1511257 := bstep (se 2 (by rfl) ⟨566721, by rfl⟩ : syracuseStep 1511257 = 1133443) B1133443
theorem B1347443 : Blo 595291 1347443 := bstep (se 1 (by rfl) ⟨1010582, by rfl⟩ : syracuseStep 1347443 = 2021165) B2021165
theorem B1347479 : Blo 595291 1347479 := bstep (se 1 (by rfl) ⟨1010609, by rfl⟩ : syracuseStep 1347479 = 2021219) B2021219
theorem B1347659 : Blo 595291 1347659 := bstep (se 1 (by rfl) ⟨1010744, by rfl⟩ : syracuseStep 1347659 = 2021489) B2021489
theorem B1347713 : Blo 595291 1347713 := bstep (se 2 (by rfl) ⟨505392, by rfl⟩ : syracuseStep 1347713 = 1010785) B1010785
theorem B2429149 : Blo 595291 2429149 := bstep (se 3 (by rfl) ⟨455465, by rfl⟩ : syracuseStep 2429149 = 910931) B910931
theorem B2265367 : Blo 595291 2265367 := bstep (se 1 (by rfl) ⟨1699025, by rfl⟩ : syracuseStep 2265367 = 3398051) B3398051
theorem B1347929 : Blo 595291 1347929 := bstep (se 2 (by rfl) ⟨505473, by rfl⟩ : syracuseStep 1347929 = 1010947) B1010947
theorem B758155 : Blo 595291 758155 := bstep (se 1 (by rfl) ⟨568616, by rfl⟩ : syracuseStep 758155 = 1137233) B1137233
theorem B1348019 : Blo 595291 1348019 := bstep (se 1 (by rfl) ⟨1011014, by rfl⟩ : syracuseStep 1348019 = 2022029) B2022029
theorem B1348055 : Blo 595291 1348055 := bstep (se 1 (by rfl) ⟨1011041, by rfl⟩ : syracuseStep 1348055 = 2022083) B2022083
theorem B1348235 : Blo 595291 1348235 := bstep (se 1 (by rfl) ⟨1011176, by rfl⟩ : syracuseStep 1348235 = 2022353) B2022353
theorem B3412631 : Blo 595291 3412631 := bstep (se 1 (by rfl) ⟨2559473, by rfl⟩ : syracuseStep 3412631 = 5118947) B5118947
theorem B758423 : Blo 595291 758423 := bstep (se 1 (by rfl) ⟨568817, by rfl⟩ : syracuseStep 758423 = 1137635) B1137635
theorem B8622773 : Blo 595291 8622773 := bstep (se 5 (by rfl) ⟨404192, by rfl⟩ : syracuseStep 8622773 = 808385) B808385
theorem B1348289 : Blo 595291 1348289 := bstep (se 2 (by rfl) ⟨505608, by rfl⟩ : syracuseStep 1348289 = 1011217) B1011217
theorem B1512371 : Blo 595291 1512371 := bstep (se 1 (by rfl) ⟨1134278, by rfl⟩ : syracuseStep 1512371 = 2268557) B2268557
theorem B7640081 : Blo 595291 7640081 := bstep (se 2 (by rfl) ⟨2865030, by rfl⟩ : syracuseStep 7640081 = 5730061) B5730061
theorem B2266157 : Blo 595291 2266157 := bstep (se 3 (by rfl) ⟨424904, by rfl⟩ : syracuseStep 2266157 = 849809) B849809
theorem B3019841 : Blo 595291 3019841 := bstep (se 2 (by rfl) ⟨1132440, by rfl⟩ : syracuseStep 3019841 = 2264881) B2264881
theorem B1512665 : Blo 595291 1512665 := bstep (se 2 (by rfl) ⟨567249, by rfl⟩ : syracuseStep 1512665 = 1134499) B1134499
theorem B595307 : Blo 595291 595307 := bstep (se 1 (by rfl) ⟨446480, by rfl⟩ : syracuseStep 595307 = 892961) B892961
theorem B595319 : Blo 595291 595319 := bstep (se 1 (by rfl) ⟨446489, by rfl⟩ : syracuseStep 595319 = 892979) B892979
theorem B595339 : Blo 595291 595339 := bstep (se 1 (by rfl) ⟨446504, by rfl⟩ : syracuseStep 595339 = 893009) B893009
theorem B595351 : Blo 595291 595351 := bstep (se 1 (by rfl) ⟨446513, by rfl⟩ : syracuseStep 595351 = 893027) B893027
theorem B595371 : Blo 595291 595371 := bstep (se 1 (by rfl) ⟨446528, by rfl⟩ : syracuseStep 595371 = 893057) B893057
theorem B595383 : Blo 595291 595383 := bstep (se 1 (by rfl) ⟨446537, by rfl⟩ : syracuseStep 595383 = 893075) B893075
theorem B595403 : Blo 595291 595403 := bstep (se 1 (by rfl) ⟨446552, by rfl⟩ : syracuseStep 595403 = 893105) B893105
theorem B595415 : Blo 595291 595415 := bstep (se 1 (by rfl) ⟨446561, by rfl⟩ : syracuseStep 595415 = 893123) B893123
theorem B595435 : Blo 595291 595435 := bstep (se 1 (by rfl) ⟨446576, by rfl⟩ : syracuseStep 595435 = 893153) B893153
theorem B595447 : Blo 595291 595447 := bstep (se 1 (by rfl) ⟨446585, by rfl⟩ : syracuseStep 595447 = 893171) B893171
theorem B595467 : Blo 595291 595467 := bstep (se 1 (by rfl) ⟨446600, by rfl⟩ : syracuseStep 595467 = 893201) B893201
theorem B595479 : Blo 595291 595479 := bstep (se 1 (by rfl) ⟨446609, by rfl⟩ : syracuseStep 595479 = 893219) B893219
theorem B595499 : Blo 595291 595499 := bstep (se 1 (by rfl) ⟨446624, by rfl⟩ : syracuseStep 595499 = 893249) B893249
theorem B595511 : Blo 595291 595511 := bstep (se 1 (by rfl) ⟨446633, by rfl⟩ : syracuseStep 595511 = 893267) B893267
theorem B595531 : Blo 595291 595531 := bstep (se 1 (by rfl) ⟨446648, by rfl⟩ : syracuseStep 595531 = 893297) B893297
theorem B595543 : Blo 595291 595543 := bstep (se 1 (by rfl) ⟨446657, by rfl⟩ : syracuseStep 595543 = 893315) B893315
theorem B595563 : Blo 595291 595563 := bstep (se 1 (by rfl) ⟨446672, by rfl⟩ : syracuseStep 595563 = 893345) B893345
theorem B595575 : Blo 595291 595575 := bstep (se 1 (by rfl) ⟨446681, by rfl⟩ : syracuseStep 595575 = 893363) B893363
theorem B595595 : Blo 595291 595595 := bstep (se 1 (by rfl) ⟨446696, by rfl⟩ : syracuseStep 595595 = 893393) B893393
theorem B595607 : Blo 595291 595607 := bstep (se 1 (by rfl) ⟨446705, by rfl⟩ : syracuseStep 595607 = 893411) B893411
theorem B595627 : Blo 595291 595627 := bstep (se 1 (by rfl) ⟨446720, by rfl⟩ : syracuseStep 595627 = 893441) B893441
theorem B595639 : Blo 595291 595639 := bstep (se 1 (by rfl) ⟨446729, by rfl⟩ : syracuseStep 595639 = 893459) B893459
theorem B595659 : Blo 595291 595659 := bstep (se 1 (by rfl) ⟨446744, by rfl⟩ : syracuseStep 595659 = 893489) B893489
theorem B595671 : Blo 595291 595671 := bstep (se 1 (by rfl) ⟨446753, by rfl⟩ : syracuseStep 595671 = 893507) B893507
theorem B595691 : Blo 595291 595691 := bstep (se 1 (by rfl) ⟨446768, by rfl⟩ : syracuseStep 595691 = 893537) B893537
theorem B595703 : Blo 595291 595703 := bstep (se 1 (by rfl) ⟨446777, by rfl⟩ : syracuseStep 595703 = 893555) B893555
theorem B595723 : Blo 595291 595723 := bstep (se 1 (by rfl) ⟨446792, by rfl⟩ : syracuseStep 595723 = 893585) B893585
theorem B595735 : Blo 595291 595735 := bstep (se 1 (by rfl) ⟨446801, by rfl⟩ : syracuseStep 595735 = 893603) B893603
theorem B595755 : Blo 595291 595755 := bstep (se 1 (by rfl) ⟨446816, by rfl⟩ : syracuseStep 595755 = 893633) B893633
theorem B595767 : Blo 595291 595767 := bstep (se 1 (by rfl) ⟨446825, by rfl⟩ : syracuseStep 595767 = 893651) B893651
theorem B595787 : Blo 595291 595787 := bstep (se 1 (by rfl) ⟨446840, by rfl⟩ : syracuseStep 595787 = 893681) B893681
theorem B595799 : Blo 595291 595799 := bstep (se 1 (by rfl) ⟨446849, by rfl⟩ : syracuseStep 595799 = 893699) B893699
theorem B595819 : Blo 595291 595819 := bstep (se 1 (by rfl) ⟨446864, by rfl⟩ : syracuseStep 595819 = 893729) B893729
theorem B595831 : Blo 595291 595831 := bstep (se 1 (by rfl) ⟨446873, by rfl⟩ : syracuseStep 595831 = 893747) B893747
theorem B595851 : Blo 595291 595851 := bstep (se 1 (by rfl) ⟨446888, by rfl⟩ : syracuseStep 595851 = 893777) B893777
theorem B595863 : Blo 595291 595863 := bstep (se 1 (by rfl) ⟨446897, by rfl⟩ : syracuseStep 595863 = 893795) B893795
theorem B595883 : Blo 595291 595883 := bstep (se 1 (by rfl) ⟨446912, by rfl⟩ : syracuseStep 595883 = 893825) B893825
theorem B595895 : Blo 595291 595895 := bstep (se 1 (by rfl) ⟨446921, by rfl⟩ : syracuseStep 595895 = 893843) B893843
theorem B595915 : Blo 595291 595915 := bstep (se 1 (by rfl) ⟨446936, by rfl⟩ : syracuseStep 595915 = 893873) B893873
theorem B595927 : Blo 595291 595927 := bstep (se 1 (by rfl) ⟨446945, by rfl⟩ : syracuseStep 595927 = 893891) B893891
theorem B595947 : Blo 595291 595947 := bstep (se 1 (by rfl) ⟨446960, by rfl⟩ : syracuseStep 595947 = 893921) B893921
theorem B595959 : Blo 595291 595959 := bstep (se 1 (by rfl) ⟨446969, by rfl⟩ : syracuseStep 595959 = 893939) B893939
theorem B595979 : Blo 595291 595979 := bstep (se 1 (by rfl) ⟨446984, by rfl⟩ : syracuseStep 595979 = 893969) B893969
theorem B595991 : Blo 595291 595991 := bstep (se 1 (by rfl) ⟨446993, by rfl⟩ : syracuseStep 595991 = 893987) B893987
theorem B596011 : Blo 595291 596011 := bstep (se 1 (by rfl) ⟨447008, by rfl⟩ : syracuseStep 596011 = 894017) B894017
theorem B596023 : Blo 595291 596023 := bstep (se 1 (by rfl) ⟨447017, by rfl⟩ : syracuseStep 596023 = 894035) B894035
theorem B596043 : Blo 595291 596043 := bstep (se 1 (by rfl) ⟨447032, by rfl⟩ : syracuseStep 596043 = 894065) B894065
theorem B596055 : Blo 595291 596055 := bstep (se 1 (by rfl) ⟨447041, by rfl⟩ : syracuseStep 596055 = 894083) B894083
theorem B6821981 : Blo 595291 6821981 := bstep (se 3 (by rfl) ⟨1279121, by rfl⟩ : syracuseStep 6821981 = 2558243) B2558243
theorem B596075 : Blo 595291 596075 := bstep (se 1 (by rfl) ⟨447056, by rfl⟩ : syracuseStep 596075 = 894113) B894113
theorem B596087 : Blo 595291 596087 := bstep (se 1 (by rfl) ⟨447065, by rfl⟩ : syracuseStep 596087 = 894131) B894131
theorem B596107 : Blo 595291 596107 := bstep (se 1 (by rfl) ⟨447080, by rfl⟩ : syracuseStep 596107 = 894161) B894161
theorem B596119 : Blo 595291 596119 := bstep (se 1 (by rfl) ⟨447089, by rfl⟩ : syracuseStep 596119 = 894179) B894179
theorem B596139 : Blo 595291 596139 := bstep (se 1 (by rfl) ⟨447104, by rfl⟩ : syracuseStep 596139 = 894209) B894209
theorem B596151 : Blo 595291 596151 := bstep (se 1 (by rfl) ⟨447113, by rfl⟩ : syracuseStep 596151 = 894227) B894227
theorem B596171 : Blo 595291 596171 := bstep (se 1 (by rfl) ⟨447128, by rfl⟩ : syracuseStep 596171 = 894257) B894257
theorem B596183 : Blo 595291 596183 := bstep (se 1 (by rfl) ⟨447137, by rfl⟩ : syracuseStep 596183 = 894275) B894275
theorem B596203 : Blo 595291 596203 := bstep (se 1 (by rfl) ⟨447152, by rfl⟩ : syracuseStep 596203 = 894305) B894305
theorem B596215 : Blo 595291 596215 := bstep (se 1 (by rfl) ⟨447161, by rfl⟩ : syracuseStep 596215 = 894323) B894323
theorem B596235 : Blo 595291 596235 := bstep (se 1 (by rfl) ⟨447176, by rfl⟩ : syracuseStep 596235 = 894353) B894353
theorem B596247 : Blo 595291 596247 := bstep (se 1 (by rfl) ⟨447185, by rfl⟩ : syracuseStep 596247 = 894371) B894371
theorem B596267 : Blo 595291 596267 := bstep (se 1 (by rfl) ⟨447200, by rfl⟩ : syracuseStep 596267 = 894401) B894401
theorem B596279 : Blo 595291 596279 := bstep (se 1 (by rfl) ⟨447209, by rfl⟩ : syracuseStep 596279 = 894419) B894419
theorem B596299 : Blo 595291 596299 := bstep (se 1 (by rfl) ⟨447224, by rfl⟩ : syracuseStep 596299 = 894449) B894449
theorem B596311 : Blo 595291 596311 := bstep (se 1 (by rfl) ⟨447233, by rfl⟩ : syracuseStep 596311 = 894467) B894467
theorem B596331 : Blo 595291 596331 := bstep (se 1 (by rfl) ⟨447248, by rfl⟩ : syracuseStep 596331 = 894497) B894497
theorem B596343 : Blo 595291 596343 := bstep (se 1 (by rfl) ⟨447257, by rfl⟩ : syracuseStep 596343 = 894515) B894515
theorem B596363 : Blo 595291 596363 := bstep (se 1 (by rfl) ⟨447272, by rfl⟩ : syracuseStep 596363 = 894545) B894545
theorem B596375 : Blo 595291 596375 := bstep (se 1 (by rfl) ⟨447281, by rfl⟩ : syracuseStep 596375 = 894563) B894563
theorem B596395 : Blo 595291 596395 := bstep (se 1 (by rfl) ⟨447296, by rfl⟩ : syracuseStep 596395 = 894593) B894593
theorem B596407 : Blo 595291 596407 := bstep (se 1 (by rfl) ⟨447305, by rfl⟩ : syracuseStep 596407 = 894611) B894611
theorem B2267585 : Blo 595291 2267585 := bstep (se 2 (by rfl) ⟨850344, by rfl⟩ : syracuseStep 2267585 = 1700689) B1700689
theorem B596427 : Blo 595291 596427 := bstep (se 1 (by rfl) ⟨447320, by rfl⟩ : syracuseStep 596427 = 894641) B894641
theorem B596439 : Blo 595291 596439 := bstep (se 1 (by rfl) ⟨447329, by rfl⟩ : syracuseStep 596439 = 894659) B894659
theorem B596459 : Blo 595291 596459 := bstep (se 1 (by rfl) ⟨447344, by rfl⟩ : syracuseStep 596459 = 894689) B894689
theorem B596471 : Blo 595291 596471 := bstep (se 1 (by rfl) ⟨447353, by rfl⟩ : syracuseStep 596471 = 894707) B894707
theorem B596491 : Blo 595291 596491 := bstep (se 1 (by rfl) ⟨447368, by rfl⟩ : syracuseStep 596491 = 894737) B894737
theorem B596503 : Blo 595291 596503 := bstep (se 1 (by rfl) ⟨447377, by rfl⟩ : syracuseStep 596503 = 894755) B894755
theorem B596523 : Blo 595291 596523 := bstep (se 1 (by rfl) ⟨447392, by rfl⟩ : syracuseStep 596523 = 894785) B894785
theorem B596535 : Blo 595291 596535 := bstep (se 1 (by rfl) ⟨447401, by rfl⟩ : syracuseStep 596535 = 894803) B894803
theorem B596555 : Blo 595291 596555 := bstep (se 1 (by rfl) ⟨447416, by rfl⟩ : syracuseStep 596555 = 894833) B894833
theorem B596567 : Blo 595291 596567 := bstep (se 1 (by rfl) ⟨447425, by rfl⟩ : syracuseStep 596567 = 894851) B894851
theorem B596587 : Blo 595291 596587 := bstep (se 1 (by rfl) ⟨447440, by rfl⟩ : syracuseStep 596587 = 894881) B894881
theorem B596599 : Blo 595291 596599 := bstep (se 1 (by rfl) ⟨447449, by rfl⟩ : syracuseStep 596599 = 894899) B894899
theorem B596619 : Blo 595291 596619 := bstep (se 1 (by rfl) ⟨447464, by rfl⟩ : syracuseStep 596619 = 894929) B894929
theorem B596631 : Blo 595291 596631 := bstep (se 1 (by rfl) ⟨447473, by rfl⟩ : syracuseStep 596631 = 894947) B894947
theorem B596651 : Blo 595291 596651 := bstep (se 1 (by rfl) ⟨447488, by rfl⟩ : syracuseStep 596651 = 894977) B894977
theorem B596663 : Blo 595291 596663 := bstep (se 1 (by rfl) ⟨447497, by rfl⟩ : syracuseStep 596663 = 894995) B894995
theorem B596683 : Blo 595291 596683 := bstep (se 1 (by rfl) ⟨447512, by rfl⟩ : syracuseStep 596683 = 895025) B895025
theorem B596695 : Blo 595291 596695 := bstep (se 1 (by rfl) ⟨447521, by rfl⟩ : syracuseStep 596695 = 895043) B895043
theorem B596715 : Blo 595291 596715 := bstep (se 1 (by rfl) ⟨447536, by rfl⟩ : syracuseStep 596715 = 895073) B895073
theorem B596727 : Blo 595291 596727 := bstep (se 1 (by rfl) ⟨447545, by rfl⟩ : syracuseStep 596727 = 895091) B895091
theorem B4922117 : Blo 595291 4922117 := bstep (se 4 (by rfl) ⟨461448, by rfl⟩ : syracuseStep 4922117 = 922897) B922897
theorem B596747 : Blo 595291 596747 := bstep (se 1 (by rfl) ⟨447560, by rfl⟩ : syracuseStep 596747 = 895121) B895121
theorem B596759 : Blo 595291 596759 := bstep (se 1 (by rfl) ⟨447569, by rfl⟩ : syracuseStep 596759 = 895139) B895139
theorem B596779 : Blo 595291 596779 := bstep (se 1 (by rfl) ⟨447584, by rfl⟩ : syracuseStep 596779 = 895169) B895169
theorem B596791 : Blo 595291 596791 := bstep (se 1 (by rfl) ⟨447593, by rfl⟩ : syracuseStep 596791 = 895187) B895187
theorem B1612619 : Blo 595291 1612619 := bstep (se 1 (by rfl) ⟨1209464, by rfl⟩ : syracuseStep 1612619 = 2418929) B2418929
theorem B596811 : Blo 595291 596811 := bstep (se 1 (by rfl) ⟨447608, by rfl⟩ : syracuseStep 596811 = 895217) B895217
theorem B1514315 : Blo 595291 1514315 := bstep (se 1 (by rfl) ⟨1135736, by rfl⟩ : syracuseStep 1514315 = 2271473) B2271473
theorem B596823 : Blo 595291 596823 := bstep (se 1 (by rfl) ⟨447617, by rfl⟩ : syracuseStep 596823 = 895235) B895235
theorem B596843 : Blo 595291 596843 := bstep (se 1 (by rfl) ⟨447632, by rfl⟩ : syracuseStep 596843 = 895265) B895265
theorem B596855 : Blo 595291 596855 := bstep (se 1 (by rfl) ⟨447641, by rfl⟩ : syracuseStep 596855 = 895283) B895283
theorem B596875 : Blo 595291 596875 := bstep (se 1 (by rfl) ⟨447656, by rfl⟩ : syracuseStep 596875 = 895313) B895313
theorem B596887 : Blo 595291 596887 := bstep (se 1 (by rfl) ⟨447665, by rfl⟩ : syracuseStep 596887 = 895331) B895331
theorem B596907 : Blo 595291 596907 := bstep (se 1 (by rfl) ⟨447680, by rfl⟩ : syracuseStep 596907 = 895361) B895361
theorem B596919 : Blo 595291 596919 := bstep (se 1 (by rfl) ⟨447689, by rfl⟩ : syracuseStep 596919 = 895379) B895379
theorem B596939 : Blo 595291 596939 := bstep (se 1 (by rfl) ⟨447704, by rfl⟩ : syracuseStep 596939 = 895409) B895409
theorem B596951 : Blo 595291 596951 := bstep (se 1 (by rfl) ⟨447713, by rfl⟩ : syracuseStep 596951 = 895427) B895427
theorem B3021785 : Blo 595291 3021785 := bstep (se 2 (by rfl) ⟨1133169, by rfl⟩ : syracuseStep 3021785 = 2266339) B2266339
theorem B596971 : Blo 595291 596971 := bstep (se 1 (by rfl) ⟨447728, by rfl⟩ : syracuseStep 596971 = 895457) B895457
theorem B596983 : Blo 595291 596983 := bstep (se 1 (by rfl) ⟨447737, by rfl⟩ : syracuseStep 596983 = 895475) B895475
theorem B597003 : Blo 595291 597003 := bstep (se 1 (by rfl) ⟨447752, by rfl⟩ : syracuseStep 597003 = 895505) B895505
theorem B597015 : Blo 595291 597015 := bstep (se 1 (by rfl) ⟨447761, by rfl⟩ : syracuseStep 597015 = 895523) B895523
theorem B597035 : Blo 595291 597035 := bstep (se 1 (by rfl) ⟨447776, by rfl⟩ : syracuseStep 597035 = 895553) B895553
theorem B597047 : Blo 595291 597047 := bstep (se 1 (by rfl) ⟨447785, by rfl⟩ : syracuseStep 597047 = 895571) B895571
theorem B597067 : Blo 595291 597067 := bstep (se 1 (by rfl) ⟨447800, by rfl⟩ : syracuseStep 597067 = 895601) B895601
theorem B597079 : Blo 595291 597079 := bstep (se 1 (by rfl) ⟨447809, by rfl⟩ : syracuseStep 597079 = 895619) B895619
theorem B597099 : Blo 595291 597099 := bstep (se 1 (by rfl) ⟨447824, by rfl⟩ : syracuseStep 597099 = 895649) B895649
theorem B597111 : Blo 595291 597111 := bstep (se 1 (by rfl) ⟨447833, by rfl⟩ : syracuseStep 597111 = 895667) B895667
theorem B597131 : Blo 595291 597131 := bstep (se 1 (by rfl) ⟨447848, by rfl⟩ : syracuseStep 597131 = 895697) B895697
theorem B597143 : Blo 595291 597143 := bstep (se 1 (by rfl) ⟨447857, by rfl⟩ : syracuseStep 597143 = 895715) B895715
theorem B597163 : Blo 595291 597163 := bstep (se 1 (by rfl) ⟨447872, by rfl⟩ : syracuseStep 597163 = 895745) B895745
theorem B597175 : Blo 595291 597175 := bstep (se 1 (by rfl) ⟨447881, by rfl⟩ : syracuseStep 597175 = 895763) B895763
theorem B597195 : Blo 595291 597195 := bstep (se 1 (by rfl) ⟨447896, by rfl⟩ : syracuseStep 597195 = 895793) B895793
theorem B597207 : Blo 595291 597207 := bstep (se 1 (by rfl) ⟨447905, by rfl⟩ : syracuseStep 597207 = 895811) B895811
theorem B597227 : Blo 595291 597227 := bstep (se 1 (by rfl) ⟨447920, by rfl⟩ : syracuseStep 597227 = 895841) B895841
theorem B597239 : Blo 595291 597239 := bstep (se 1 (by rfl) ⟨447929, by rfl⟩ : syracuseStep 597239 = 895859) B895859
theorem B597259 : Blo 595291 597259 := bstep (se 1 (by rfl) ⟨447944, by rfl⟩ : syracuseStep 597259 = 895889) B895889
theorem B597271 : Blo 595291 597271 := bstep (se 1 (by rfl) ⟨447953, by rfl⟩ : syracuseStep 597271 = 895907) B895907
theorem B597291 : Blo 595291 597291 := bstep (se 1 (by rfl) ⟨447968, by rfl⟩ : syracuseStep 597291 = 895937) B895937
theorem B597303 : Blo 595291 597303 := bstep (se 1 (by rfl) ⟨447977, by rfl⟩ : syracuseStep 597303 = 895955) B895955
theorem B597323 : Blo 595291 597323 := bstep (se 1 (by rfl) ⟨447992, by rfl⟩ : syracuseStep 597323 = 895985) B895985
theorem B597335 : Blo 595291 597335 := bstep (se 1 (by rfl) ⟨448001, by rfl⟩ : syracuseStep 597335 = 896003) B896003
theorem B597355 : Blo 595291 597355 := bstep (se 1 (by rfl) ⟨448016, by rfl⟩ : syracuseStep 597355 = 896033) B896033
theorem B597367 : Blo 595291 597367 := bstep (se 1 (by rfl) ⟨448025, by rfl⟩ : syracuseStep 597367 = 896051) B896051
theorem B597387 : Blo 595291 597387 := bstep (se 1 (by rfl) ⟨448040, by rfl⟩ : syracuseStep 597387 = 896081) B896081
theorem B597399 : Blo 595291 597399 := bstep (se 1 (by rfl) ⟨448049, by rfl⟩ : syracuseStep 597399 = 896099) B896099
theorem B597419 : Blo 595291 597419 := bstep (se 1 (by rfl) ⟨448064, by rfl⟩ : syracuseStep 597419 = 896129) B896129
theorem B597431 : Blo 595291 597431 := bstep (se 1 (by rfl) ⟨448073, by rfl⟩ : syracuseStep 597431 = 896147) B896147
theorem B597451 : Blo 595291 597451 := bstep (se 1 (by rfl) ⟨448088, by rfl⟩ : syracuseStep 597451 = 896177) B896177
theorem B597463 : Blo 595291 597463 := bstep (se 1 (by rfl) ⟨448097, by rfl⟩ : syracuseStep 597463 = 896195) B896195
theorem B597483 : Blo 595291 597483 := bstep (se 1 (by rfl) ⟨448112, by rfl⟩ : syracuseStep 597483 = 896225) B896225
theorem B597495 : Blo 595291 597495 := bstep (se 1 (by rfl) ⟨448121, by rfl⟩ : syracuseStep 597495 = 896243) B896243
theorem B597515 : Blo 595291 597515 := bstep (se 1 (by rfl) ⟨448136, by rfl⟩ : syracuseStep 597515 = 896273) B896273
theorem B597527 : Blo 595291 597527 := bstep (se 1 (by rfl) ⟨448145, by rfl⟩ : syracuseStep 597527 = 896291) B896291
theorem B597547 : Blo 595291 597547 := bstep (se 1 (by rfl) ⟨448160, by rfl⟩ : syracuseStep 597547 = 896321) B896321
theorem B597559 : Blo 595291 597559 := bstep (se 1 (by rfl) ⟨448169, by rfl⟩ : syracuseStep 597559 = 896339) B896339
theorem B8592965 : Blo 595291 8592965 := bstep (se 4 (by rfl) ⟨805590, by rfl⟩ : syracuseStep 8592965 = 1611181) B1611181
theorem B597579 : Blo 595291 597579 := bstep (se 1 (by rfl) ⟨448184, by rfl⟩ : syracuseStep 597579 = 896369) B896369
theorem B597591 : Blo 595291 597591 := bstep (se 1 (by rfl) ⟨448193, by rfl⟩ : syracuseStep 597591 = 896387) B896387
theorem B597611 : Blo 595291 597611 := bstep (se 1 (by rfl) ⟨448208, by rfl⟩ : syracuseStep 597611 = 896417) B896417
theorem B597623 : Blo 595291 597623 := bstep (se 1 (by rfl) ⟨448217, by rfl⟩ : syracuseStep 597623 = 896435) B896435
theorem B2301571 : Blo 595291 2301571 := bstep (se 1 (by rfl) ⟨1726178, by rfl⟩ : syracuseStep 2301571 = 3452357) B3452357
theorem B597643 : Blo 595291 597643 := bstep (se 1 (by rfl) ⟨448232, by rfl⟩ : syracuseStep 597643 = 896465) B896465
theorem B597655 : Blo 595291 597655 := bstep (se 1 (by rfl) ⟨448241, by rfl⟩ : syracuseStep 597655 = 896483) B896483
theorem B597675 : Blo 595291 597675 := bstep (se 1 (by rfl) ⟨448256, by rfl⟩ : syracuseStep 597675 = 896513) B896513
theorem B597687 : Blo 595291 597687 := bstep (se 1 (by rfl) ⟨448265, by rfl⟩ : syracuseStep 597687 = 896531) B896531
theorem B597707 : Blo 595291 597707 := bstep (se 1 (by rfl) ⟨448280, by rfl⟩ : syracuseStep 597707 = 896561) B896561
theorem B597719 : Blo 595291 597719 := bstep (se 1 (by rfl) ⟨448289, by rfl⟩ : syracuseStep 597719 = 896579) B896579
theorem B597739 : Blo 595291 597739 := bstep (se 1 (by rfl) ⟨448304, by rfl⟩ : syracuseStep 597739 = 896609) B896609
theorem B597751 : Blo 595291 597751 := bstep (se 1 (by rfl) ⟨448313, by rfl⟩ : syracuseStep 597751 = 896627) B896627
theorem B597771 : Blo 595291 597771 := bstep (se 1 (by rfl) ⟨448328, by rfl⟩ : syracuseStep 597771 = 896657) B896657
theorem B859927 : Blo 595291 859927 := bstep (se 1 (by rfl) ⟨644945, by rfl⟩ : syracuseStep 859927 = 1289891) B1289891
theorem B597783 : Blo 595291 597783 := bstep (se 1 (by rfl) ⟨448337, by rfl⟩ : syracuseStep 597783 = 896675) B896675
theorem B1515287 : Blo 595291 1515287 := bstep (se 1 (by rfl) ⟨1136465, by rfl⟩ : syracuseStep 1515287 = 2272931) B2272931
theorem B597803 : Blo 595291 597803 := bstep (se 1 (by rfl) ⟨448352, by rfl⟩ : syracuseStep 597803 = 896705) B896705
theorem B597815 : Blo 595291 597815 := bstep (se 1 (by rfl) ⟨448361, by rfl⟩ : syracuseStep 597815 = 896723) B896723
theorem B597835 : Blo 595291 597835 := bstep (se 1 (by rfl) ⟨448376, by rfl⟩ : syracuseStep 597835 = 896753) B896753
theorem B597847 : Blo 595291 597847 := bstep (se 1 (by rfl) ⟨448385, by rfl⟩ : syracuseStep 597847 = 896771) B896771
theorem B1613657 : Blo 595291 1613657 := bstep (se 2 (by rfl) ⟨605121, by rfl⟩ : syracuseStep 1613657 = 1210243) B1210243
theorem B597867 : Blo 595291 597867 := bstep (se 1 (by rfl) ⟨448400, by rfl⟩ : syracuseStep 597867 = 896801) B896801
theorem B597879 : Blo 595291 597879 := bstep (se 1 (by rfl) ⟨448409, by rfl⟩ : syracuseStep 597879 = 896819) B896819
theorem B597899 : Blo 595291 597899 := bstep (se 1 (by rfl) ⟨448424, by rfl⟩ : syracuseStep 597899 = 896849) B896849
theorem B2269073 : Blo 595291 2269073 := bstep (se 2 (by rfl) ⟨850902, by rfl⟩ : syracuseStep 2269073 = 1701805) B1701805
theorem B597911 : Blo 595291 597911 := bstep (se 1 (by rfl) ⟨448433, by rfl⟩ : syracuseStep 597911 = 896867) B896867
theorem B597931 : Blo 595291 597931 := bstep (se 1 (by rfl) ⟨448448, by rfl⟩ : syracuseStep 597931 = 896897) B896897
theorem B4300721 : Blo 595291 4300721 := bstep (se 2 (by rfl) ⟨1612770, by rfl⟩ : syracuseStep 4300721 = 3225541) B3225541
theorem B5742515 : Blo 595291 5742515 := bstep (se 1 (by rfl) ⟨4306886, by rfl⟩ : syracuseStep 5742515 = 8613773) B8613773
theorem B597943 : Blo 595291 597943 := bstep (se 1 (by rfl) ⟨448457, by rfl⟩ : syracuseStep 597943 = 896915) B896915
theorem B597963 : Blo 595291 597963 := bstep (se 1 (by rfl) ⟨448472, by rfl⟩ : syracuseStep 597963 = 896945) B896945
theorem B597975 : Blo 595291 597975 := bstep (se 1 (by rfl) ⟨448481, by rfl⟩ : syracuseStep 597975 = 896963) B896963
theorem B2072537 : Blo 595291 2072537 := bstep (se 2 (by rfl) ⟨777201, by rfl⟩ : syracuseStep 2072537 = 1554403) B1554403
theorem B597995 : Blo 595291 597995 := bstep (se 1 (by rfl) ⟨448496, by rfl⟩ : syracuseStep 597995 = 896993) B896993
theorem B598007 : Blo 595291 598007 := bstep (se 1 (by rfl) ⟨448505, by rfl⟩ : syracuseStep 598007 = 897011) B897011
theorem B598027 : Blo 595291 598027 := bstep (se 1 (by rfl) ⟨448520, by rfl⟩ : syracuseStep 598027 = 897041) B897041
theorem B598039 : Blo 595291 598039 := bstep (se 1 (by rfl) ⟨448529, by rfl⟩ : syracuseStep 598039 = 897059) B897059
theorem B598059 : Blo 595291 598059 := bstep (se 1 (by rfl) ⟨448544, by rfl⟩ : syracuseStep 598059 = 897089) B897089
theorem B598071 : Blo 595291 598071 := bstep (se 1 (by rfl) ⟨448553, by rfl⟩ : syracuseStep 598071 = 897107) B897107
theorem B893003 : Blo 595291 893003 := bstep (se 1 (by rfl) ⟨669752, by rfl⟩ : syracuseStep 893003 = 1339505) B1339505
theorem B598091 : Blo 595291 598091 := bstep (se 1 (by rfl) ⟨448568, by rfl⟩ : syracuseStep 598091 = 897137) B897137
theorem B893015 : Blo 595291 893015 := bstep (se 1 (by rfl) ⟨669761, by rfl⟩ : syracuseStep 893015 = 1339523) B1339523
theorem B598103 : Blo 595291 598103 := bstep (se 1 (by rfl) ⟨448577, by rfl⟩ : syracuseStep 598103 = 897155) B897155
theorem B598123 : Blo 595291 598123 := bstep (se 1 (by rfl) ⟨448592, by rfl⟩ : syracuseStep 598123 = 897185) B897185
theorem B598135 : Blo 595291 598135 := bstep (se 1 (by rfl) ⟨448601, by rfl⟩ : syracuseStep 598135 = 897203) B897203
theorem B598155 : Blo 595291 598155 := bstep (se 1 (by rfl) ⟨448616, by rfl⟩ : syracuseStep 598155 = 897233) B897233
theorem B598167 : Blo 595291 598167 := bstep (se 1 (by rfl) ⟨448625, by rfl⟩ : syracuseStep 598167 = 897251) B897251
theorem B893081 : Blo 595291 893081 := bstep (se 2 (by rfl) ⟨334905, by rfl⟩ : syracuseStep 893081 = 669811) B669811
theorem B598187 : Blo 595291 598187 := bstep (se 1 (by rfl) ⟨448640, by rfl⟩ : syracuseStep 598187 = 897281) B897281
theorem B598199 : Blo 595291 598199 := bstep (se 1 (by rfl) ⟨448649, by rfl⟩ : syracuseStep 598199 = 897299) B897299
theorem B598219 : Blo 595291 598219 := bstep (se 1 (by rfl) ⟨448664, by rfl⟩ : syracuseStep 598219 = 897329) B897329
theorem B598231 : Blo 595291 598231 := bstep (se 1 (by rfl) ⟨448673, by rfl⟩ : syracuseStep 598231 = 897347) B897347
theorem B598251 : Blo 595291 598251 := bstep (se 1 (by rfl) ⟨448688, by rfl⟩ : syracuseStep 598251 = 897377) B897377
theorem B598263 : Blo 595291 598263 := bstep (se 1 (by rfl) ⟨448697, by rfl⟩ : syracuseStep 598263 = 897395) B897395
theorem B893195 : Blo 595291 893195 := bstep (se 1 (by rfl) ⟨669896, by rfl⟩ : syracuseStep 893195 = 1339793) B1339793
theorem B598283 : Blo 595291 598283 := bstep (se 1 (by rfl) ⟨448712, by rfl⟩ : syracuseStep 598283 = 897425) B897425
theorem B893207 : Blo 595291 893207 := bstep (se 1 (by rfl) ⟨669905, by rfl⟩ : syracuseStep 893207 = 1339811) B1339811
theorem B598295 : Blo 595291 598295 := bstep (se 1 (by rfl) ⟨448721, by rfl⟩ : syracuseStep 598295 = 897443) B897443
theorem B598315 : Blo 595291 598315 := bstep (se 1 (by rfl) ⟨448736, by rfl⟩ : syracuseStep 598315 = 897473) B897473
theorem B598327 : Blo 595291 598327 := bstep (se 1 (by rfl) ⟨448745, by rfl⟩ : syracuseStep 598327 = 897491) B897491
theorem B598347 : Blo 595291 598347 := bstep (se 1 (by rfl) ⟨448760, by rfl⟩ : syracuseStep 598347 = 897521) B897521
theorem B598359 : Blo 595291 598359 := bstep (se 1 (by rfl) ⟨448769, by rfl⟩ : syracuseStep 598359 = 897539) B897539
theorem B893273 : Blo 595291 893273 := bstep (se 2 (by rfl) ⟨334977, by rfl⟩ : syracuseStep 893273 = 669955) B669955
theorem B2269529 : Blo 595291 2269529 := bstep (se 2 (by rfl) ⟨851073, by rfl⟩ : syracuseStep 2269529 = 1702147) B1702147
theorem B598379 : Blo 595291 598379 := bstep (se 1 (by rfl) ⟨448784, by rfl⟩ : syracuseStep 598379 = 897569) B897569
theorem B598391 : Blo 595291 598391 := bstep (se 1 (by rfl) ⟨448793, by rfl⟩ : syracuseStep 598391 = 897587) B897587
theorem B598411 : Blo 595291 598411 := bstep (se 1 (by rfl) ⟨448808, by rfl⟩ : syracuseStep 598411 = 897617) B897617
theorem B598423 : Blo 595291 598423 := bstep (se 1 (by rfl) ⟨448817, by rfl⟩ : syracuseStep 598423 = 897635) B897635
theorem B598443 : Blo 595291 598443 := bstep (se 1 (by rfl) ⟨448832, by rfl⟩ : syracuseStep 598443 = 897665) B897665
theorem B598455 : Blo 595291 598455 := bstep (se 1 (by rfl) ⟨448841, by rfl⟩ : syracuseStep 598455 = 897683) B897683
theorem B1515955 : Blo 595291 1515955 := bstep (se 1 (by rfl) ⟨1136966, by rfl⟩ : syracuseStep 1515955 = 2273933) B2273933
theorem B893387 : Blo 595291 893387 := bstep (se 1 (by rfl) ⟨670040, by rfl⟩ : syracuseStep 893387 = 1340081) B1340081
theorem B598475 : Blo 595291 598475 := bstep (se 1 (by rfl) ⟨448856, by rfl⟩ : syracuseStep 598475 = 897713) B897713
theorem B893399 : Blo 595291 893399 := bstep (se 1 (by rfl) ⟨670049, by rfl⟩ : syracuseStep 893399 = 1340099) B1340099
theorem B598487 : Blo 595291 598487 := bstep (se 1 (by rfl) ⟨448865, by rfl⟩ : syracuseStep 598487 = 897731) B897731
theorem B598507 : Blo 595291 598507 := bstep (se 1 (by rfl) ⟨448880, by rfl⟩ : syracuseStep 598507 = 897761) B897761
theorem B598519 : Blo 595291 598519 := bstep (se 1 (by rfl) ⟨448889, by rfl⟩ : syracuseStep 598519 = 897779) B897779
theorem B598539 : Blo 595291 598539 := bstep (se 1 (by rfl) ⟨448904, by rfl⟩ : syracuseStep 598539 = 897809) B897809
theorem B598551 : Blo 595291 598551 := bstep (se 1 (by rfl) ⟨448913, by rfl⟩ : syracuseStep 598551 = 897827) B897827
theorem B893465 : Blo 595291 893465 := bstep (se 2 (by rfl) ⟨335049, by rfl⟩ : syracuseStep 893465 = 670099) B670099
theorem B3023405 : Blo 595291 3023405 := bstep (se 3 (by rfl) ⟨566888, by rfl⟩ : syracuseStep 3023405 = 1133777) B1133777
theorem B2269741 : Blo 595291 2269741 := bstep (se 3 (by rfl) ⟨425576, by rfl⟩ : syracuseStep 2269741 = 851153) B851153
theorem B598571 : Blo 595291 598571 := bstep (se 1 (by rfl) ⟨448928, by rfl⟩ : syracuseStep 598571 = 897857) B897857
theorem B598583 : Blo 595291 598583 := bstep (se 1 (by rfl) ⟨448937, by rfl⟩ : syracuseStep 598583 = 897875) B897875
theorem B1516097 : Blo 595291 1516097 := bstep (se 2 (by rfl) ⟨568536, by rfl⟩ : syracuseStep 1516097 = 1137073) B1137073
theorem B598603 : Blo 595291 598603 := bstep (se 1 (by rfl) ⟨448952, by rfl⟩ : syracuseStep 598603 = 897905) B897905
theorem B598615 : Blo 595291 598615 := bstep (se 1 (by rfl) ⟨448961, by rfl⟩ : syracuseStep 598615 = 897923) B897923
theorem B598635 : Blo 595291 598635 := bstep (se 1 (by rfl) ⟨448976, by rfl⟩ : syracuseStep 598635 = 897953) B897953
theorem B598647 : Blo 595291 598647 := bstep (se 1 (by rfl) ⟨448985, by rfl⟩ : syracuseStep 598647 = 897971) B897971
theorem B893579 : Blo 595291 893579 := bstep (se 1 (by rfl) ⟨670184, by rfl⟩ : syracuseStep 893579 = 1340369) B1340369
theorem B598667 : Blo 595291 598667 := bstep (se 1 (by rfl) ⟨449000, by rfl⟩ : syracuseStep 598667 = 898001) B898001
theorem B893591 : Blo 595291 893591 := bstep (se 1 (by rfl) ⟨670193, by rfl⟩ : syracuseStep 893591 = 1340387) B1340387
theorem B598679 : Blo 595291 598679 := bstep (se 1 (by rfl) ⟨449009, by rfl⟩ : syracuseStep 598679 = 898019) B898019
theorem B598699 : Blo 595291 598699 := bstep (se 1 (by rfl) ⟨449024, by rfl⟩ : syracuseStep 598699 = 898049) B898049
theorem B598711 : Blo 595291 598711 := bstep (se 1 (by rfl) ⟨449033, by rfl⟩ : syracuseStep 598711 = 898067) B898067
theorem B598731 : Blo 595291 598731 := bstep (se 1 (by rfl) ⟨449048, by rfl⟩ : syracuseStep 598731 = 898097) B898097
theorem B598743 : Blo 595291 598743 := bstep (se 1 (by rfl) ⟨449057, by rfl⟩ : syracuseStep 598743 = 898115) B898115
theorem B893657 : Blo 595291 893657 := bstep (se 2 (by rfl) ⟨335121, by rfl⟩ : syracuseStep 893657 = 670243) B670243
theorem B598763 : Blo 595291 598763 := bstep (se 1 (by rfl) ⟨449072, by rfl⟩ : syracuseStep 598763 = 898145) B898145
theorem B598775 : Blo 595291 598775 := bstep (se 1 (by rfl) ⟨449081, by rfl⟩ : syracuseStep 598775 = 898163) B898163
theorem B598795 : Blo 595291 598795 := bstep (se 1 (by rfl) ⟨449096, by rfl⟩ : syracuseStep 598795 = 898193) B898193
theorem B4301585 : Blo 595291 4301585 := bstep (se 2 (by rfl) ⟨1613094, by rfl⟩ : syracuseStep 4301585 = 3226189) B3226189
theorem B598807 : Blo 595291 598807 := bstep (se 1 (by rfl) ⟨449105, by rfl⟩ : syracuseStep 598807 = 898211) B898211
theorem B598827 : Blo 595291 598827 := bstep (se 1 (by rfl) ⟨449120, by rfl⟩ : syracuseStep 598827 = 898241) B898241
theorem B598839 : Blo 595291 598839 := bstep (se 1 (by rfl) ⟨449129, by rfl⟩ : syracuseStep 598839 = 898259) B898259
theorem B893771 : Blo 595291 893771 := bstep (se 1 (by rfl) ⟨670328, by rfl⟩ : syracuseStep 893771 = 1340657) B1340657
theorem B598859 : Blo 595291 598859 := bstep (se 1 (by rfl) ⟨449144, by rfl⟩ : syracuseStep 598859 = 898289) B898289
theorem B893783 : Blo 595291 893783 := bstep (se 1 (by rfl) ⟨670337, by rfl⟩ : syracuseStep 893783 = 1340675) B1340675
theorem B598871 : Blo 595291 598871 := bstep (se 1 (by rfl) ⟨449153, by rfl⟩ : syracuseStep 598871 = 898307) B898307
theorem B2270045 : Blo 595291 2270045 := bstep (se 3 (by rfl) ⟨425633, by rfl⟩ : syracuseStep 2270045 = 851267) B851267
theorem B598891 : Blo 595291 598891 := bstep (se 1 (by rfl) ⟨449168, by rfl⟩ : syracuseStep 598891 = 898337) B898337
theorem B598903 : Blo 595291 598903 := bstep (se 1 (by rfl) ⟨449177, by rfl⟩ : syracuseStep 598903 = 898355) B898355
theorem B598923 : Blo 595291 598923 := bstep (se 1 (by rfl) ⟨449192, by rfl⟩ : syracuseStep 598923 = 898385) B898385
theorem B598935 : Blo 595291 598935 := bstep (se 1 (by rfl) ⟨449201, by rfl⟩ : syracuseStep 598935 = 898403) B898403
theorem B893849 : Blo 595291 893849 := bstep (se 2 (by rfl) ⟨335193, by rfl⟩ : syracuseStep 893849 = 670387) B670387
theorem B598955 : Blo 595291 598955 := bstep (se 1 (by rfl) ⟨449216, by rfl⟩ : syracuseStep 598955 = 898433) B898433
theorem B598967 : Blo 595291 598967 := bstep (se 1 (by rfl) ⟨449225, by rfl⟩ : syracuseStep 598967 = 898451) B898451
theorem B598987 : Blo 595291 598987 := bstep (se 1 (by rfl) ⟨449240, by rfl⟩ : syracuseStep 598987 = 898481) B898481
theorem B598999 : Blo 595291 598999 := bstep (se 1 (by rfl) ⟨449249, by rfl⟩ : syracuseStep 598999 = 898499) B898499
theorem B599019 : Blo 595291 599019 := bstep (se 1 (by rfl) ⟨449264, by rfl⟩ : syracuseStep 599019 = 898529) B898529
theorem B599031 : Blo 595291 599031 := bstep (se 1 (by rfl) ⟨449273, by rfl⟩ : syracuseStep 599031 = 898547) B898547
theorem B893963 : Blo 595291 893963 := bstep (se 1 (by rfl) ⟨670472, by rfl⟩ : syracuseStep 893963 = 1340945) B1340945
theorem B599051 : Blo 595291 599051 := bstep (se 1 (by rfl) ⟨449288, by rfl⟩ : syracuseStep 599051 = 898577) B898577
theorem B893975 : Blo 595291 893975 := bstep (se 1 (by rfl) ⟨670481, by rfl⟩ : syracuseStep 893975 = 1340963) B1340963
theorem B599063 : Blo 595291 599063 := bstep (se 1 (by rfl) ⟨449297, by rfl⟩ : syracuseStep 599063 = 898595) B898595
theorem B599083 : Blo 595291 599083 := bstep (se 1 (by rfl) ⟨449312, by rfl⟩ : syracuseStep 599083 = 898625) B898625
theorem B599095 : Blo 595291 599095 := bstep (se 1 (by rfl) ⟨449321, by rfl⟩ : syracuseStep 599095 = 898643) B898643
theorem B599115 : Blo 595291 599115 := bstep (se 1 (by rfl) ⟨449336, by rfl⟩ : syracuseStep 599115 = 898673) B898673
theorem B599127 : Blo 595291 599127 := bstep (se 1 (by rfl) ⟨449345, by rfl⟩ : syracuseStep 599127 = 898691) B898691
theorem B894041 : Blo 595291 894041 := bstep (se 2 (by rfl) ⟨335265, by rfl⟩ : syracuseStep 894041 = 670531) B670531
theorem B599147 : Blo 595291 599147 := bstep (se 1 (by rfl) ⟨449360, by rfl⟩ : syracuseStep 599147 = 898721) B898721
theorem B599159 : Blo 595291 599159 := bstep (se 1 (by rfl) ⟨449369, by rfl⟩ : syracuseStep 599159 = 898739) B898739
theorem B599179 : Blo 595291 599179 := bstep (se 1 (by rfl) ⟨449384, by rfl⟩ : syracuseStep 599179 = 898769) B898769
theorem B599191 : Blo 595291 599191 := bstep (se 1 (by rfl) ⟨449393, by rfl⟩ : syracuseStep 599191 = 898787) B898787
theorem B599211 : Blo 595291 599211 := bstep (se 1 (by rfl) ⟨449408, by rfl⟩ : syracuseStep 599211 = 898817) B898817
theorem B599223 : Blo 595291 599223 := bstep (se 1 (by rfl) ⟨449417, by rfl⟩ : syracuseStep 599223 = 898835) B898835
theorem B894155 : Blo 595291 894155 := bstep (se 1 (by rfl) ⟨670616, by rfl⟩ : syracuseStep 894155 = 1341233) B1341233
theorem B599243 : Blo 595291 599243 := bstep (se 1 (by rfl) ⟨449432, by rfl⟩ : syracuseStep 599243 = 898865) B898865
theorem B894167 : Blo 595291 894167 := bstep (se 1 (by rfl) ⟨670625, by rfl⟩ : syracuseStep 894167 = 1341251) B1341251
theorem B599255 : Blo 595291 599255 := bstep (se 1 (by rfl) ⟨449441, by rfl⟩ : syracuseStep 599255 = 898883) B898883
theorem B599275 : Blo 595291 599275 := bstep (se 1 (by rfl) ⟨449456, by rfl⟩ : syracuseStep 599275 = 898913) B898913
theorem B599287 : Blo 595291 599287 := bstep (se 1 (by rfl) ⟨449465, by rfl⟩ : syracuseStep 599287 = 898931) B898931
theorem B894233 : Blo 595291 894233 := bstep (se 2 (by rfl) ⟨335337, by rfl⟩ : syracuseStep 894233 = 670675) B670675
theorem B894347 : Blo 595291 894347 := bstep (se 1 (by rfl) ⟨670760, by rfl⟩ : syracuseStep 894347 = 1341521) B1341521
theorem B894359 : Blo 595291 894359 := bstep (se 1 (by rfl) ⟨670769, by rfl⟩ : syracuseStep 894359 = 1341539) B1341539
theorem B632215 : Blo 595291 632215 := bstep (se 1 (by rfl) ⟨474161, by rfl⟩ : syracuseStep 632215 = 948323) B948323
theorem B894425 : Blo 595291 894425 := bstep (se 2 (by rfl) ⟨335409, by rfl⟩ : syracuseStep 894425 = 670819) B670819
theorem B894539 : Blo 595291 894539 := bstep (se 1 (by rfl) ⟨670904, by rfl⟩ : syracuseStep 894539 = 1341809) B1341809
theorem B894551 : Blo 595291 894551 := bstep (se 1 (by rfl) ⟨670913, by rfl⟩ : syracuseStep 894551 = 1341827) B1341827
theorem B894617 : Blo 595291 894617 := bstep (se 2 (by rfl) ⟨335481, by rfl⟩ : syracuseStep 894617 = 670963) B670963
theorem B3221171 : Blo 595291 3221171 := bstep (se 1 (by rfl) ⟨2415878, by rfl⟩ : syracuseStep 3221171 = 4831757) B4831757
theorem B894731 : Blo 595291 894731 := bstep (se 1 (by rfl) ⟨671048, by rfl⟩ : syracuseStep 894731 = 1342097) B1342097
theorem B894743 : Blo 595291 894743 := bstep (se 1 (by rfl) ⟨671057, by rfl⟩ : syracuseStep 894743 = 1342115) B1342115
theorem B1812289 : Blo 595291 1812289 := bstep (se 2 (by rfl) ⟨679608, by rfl⟩ : syracuseStep 1812289 = 1359217) B1359217
theorem B894809 : Blo 595291 894809 := bstep (se 2 (by rfl) ⟨335553, by rfl⟩ : syracuseStep 894809 = 671107) B671107
theorem B894923 : Blo 595291 894923 := bstep (se 1 (by rfl) ⟨671192, by rfl⟩ : syracuseStep 894923 = 1342385) B1342385
theorem B894935 : Blo 595291 894935 := bstep (se 1 (by rfl) ⟨671201, by rfl⟩ : syracuseStep 894935 = 1342403) B1342403
theorem B895001 : Blo 595291 895001 := bstep (se 2 (by rfl) ⟨335625, by rfl⟩ : syracuseStep 895001 = 671251) B671251
theorem B2009177 : Blo 595291 2009177 := bstep (se 2 (by rfl) ⟨753441, by rfl⟩ : syracuseStep 2009177 = 1506883) B1506883
theorem B5187685 : Blo 595291 5187685 := bstep (se 4 (by rfl) ⟨486345, by rfl⟩ : syracuseStep 5187685 = 972691) B972691
theorem B895115 : Blo 595291 895115 := bstep (se 1 (by rfl) ⟨671336, by rfl⟩ : syracuseStep 895115 = 1342673) B1342673
theorem B895127 : Blo 595291 895127 := bstep (se 1 (by rfl) ⟨671345, by rfl⟩ : syracuseStep 895127 = 1342691) B1342691
theorem B895193 : Blo 595291 895193 := bstep (se 2 (by rfl) ⟨335697, by rfl⟩ : syracuseStep 895193 = 671395) B671395
theorem B1550657 : Blo 595291 1550657 := bstep (se 2 (by rfl) ⟨581496, by rfl⟩ : syracuseStep 1550657 = 1162993) B1162993
theorem B895307 : Blo 595291 895307 := bstep (se 1 (by rfl) ⟨671480, by rfl⟩ : syracuseStep 895307 = 1342961) B1342961
theorem B895319 : Blo 595291 895319 := bstep (se 1 (by rfl) ⟨671489, by rfl⟩ : syracuseStep 895319 = 1342979) B1342979
theorem B3221861 : Blo 595291 3221861 := bstep (se 4 (by rfl) ⟨302049, by rfl⟩ : syracuseStep 3221861 = 604099) B604099
theorem B895385 : Blo 595291 895385 := bstep (se 2 (by rfl) ⟨335769, by rfl⟩ : syracuseStep 895385 = 671539) B671539
theorem B895499 : Blo 595291 895499 := bstep (se 1 (by rfl) ⟨671624, by rfl⟩ : syracuseStep 895499 = 1343249) B1343249
theorem B895511 : Blo 595291 895511 := bstep (se 1 (by rfl) ⟨671633, by rfl⟩ : syracuseStep 895511 = 1343267) B1343267
theorem B1813067 : Blo 595291 1813067 := bstep (se 1 (by rfl) ⟨1359800, by rfl⟩ : syracuseStep 1813067 = 2719601) B2719601
theorem B895577 : Blo 595291 895577 := bstep (se 2 (by rfl) ⟨335841, by rfl⟩ : syracuseStep 895577 = 671683) B671683
theorem B895691 : Blo 595291 895691 := bstep (se 1 (by rfl) ⟨671768, by rfl⟩ : syracuseStep 895691 = 1343537) B1343537
theorem B895703 : Blo 595291 895703 := bstep (se 1 (by rfl) ⟨671777, by rfl⟩ : syracuseStep 895703 = 1343555) B1343555
theorem B2009879 : Blo 595291 2009879 := bstep (se 1 (by rfl) ⟨1507409, by rfl⟩ : syracuseStep 2009879 = 3014819) B3014819
theorem B1813271 : Blo 595291 1813271 := bstep (se 1 (by rfl) ⟨1359953, by rfl⟩ : syracuseStep 1813271 = 2719907) B2719907
theorem B895769 : Blo 595291 895769 := bstep (se 2 (by rfl) ⟨335913, by rfl⟩ : syracuseStep 895769 = 671827) B671827
theorem B1944395 : Blo 595291 1944395 := bstep (se 1 (by rfl) ⟨1458296, by rfl⟩ : syracuseStep 1944395 = 2916593) B2916593
theorem B895883 : Blo 595291 895883 := bstep (se 1 (by rfl) ⟨671912, by rfl⟩ : syracuseStep 895883 = 1343825) B1343825
theorem B895895 : Blo 595291 895895 := bstep (se 1 (by rfl) ⟨671921, by rfl⟩ : syracuseStep 895895 = 1343843) B1343843
theorem B895961 : Blo 595291 895961 := bstep (se 2 (by rfl) ⟨335985, by rfl⟩ : syracuseStep 895961 = 671971) B671971
theorem B6138841 : Blo 595291 6138841 := bstep (se 2 (by rfl) ⟨2302065, by rfl⟩ : syracuseStep 6138841 = 4604131) B4604131
theorem B24849443 : Blo 595291 24849443 := bstep (se 1 (by rfl) ⟨18637082, by rfl⟩ : syracuseStep 24849443 = 37274165) B37274165
theorem B896075 : Blo 595291 896075 := bstep (se 1 (by rfl) ⟨672056, by rfl⟩ : syracuseStep 896075 = 1344113) B1344113
theorem B896087 : Blo 595291 896087 := bstep (se 1 (by rfl) ⟨672065, by rfl⟩ : syracuseStep 896087 = 1344131) B1344131
theorem B896153 : Blo 595291 896153 := bstep (se 2 (by rfl) ⟨336057, by rfl⟩ : syracuseStep 896153 = 672115) B672115
theorem B896267 : Blo 595291 896267 := bstep (se 1 (by rfl) ⟨672200, by rfl⟩ : syracuseStep 896267 = 1344401) B1344401
theorem B896279 : Blo 595291 896279 := bstep (se 1 (by rfl) ⟨672209, by rfl⟩ : syracuseStep 896279 = 1344419) B1344419
theorem B2010419 : Blo 595291 2010419 := bstep (se 1 (by rfl) ⟨1507814, by rfl⟩ : syracuseStep 2010419 = 3015629) B3015629
theorem B896345 : Blo 595291 896345 := bstep (se 2 (by rfl) ⟨336129, by rfl⟩ : syracuseStep 896345 = 672259) B672259
theorem B2272643 : Blo 595291 2272643 := bstep (se 1 (by rfl) ⟨1704482, by rfl⟩ : syracuseStep 2272643 = 3408965) B3408965
theorem B2272657 : Blo 595291 2272657 := bstep (se 2 (by rfl) ⟨852246, by rfl⟩ : syracuseStep 2272657 = 1704493) B1704493
theorem B896459 : Blo 595291 896459 := bstep (se 1 (by rfl) ⟨672344, by rfl⟩ : syracuseStep 896459 = 1344689) B1344689
theorem B1617355 : Blo 595291 1617355 := bstep (se 1 (by rfl) ⟨1213016, by rfl⟩ : syracuseStep 1617355 = 2426033) B2426033
theorem B896471 : Blo 595291 896471 := bstep (se 1 (by rfl) ⟨672353, by rfl⟩ : syracuseStep 896471 = 1344707) B1344707
theorem B1224215 : Blo 595291 1224215 := bstep (se 1 (by rfl) ⟨918161, by rfl⟩ : syracuseStep 1224215 = 1836323) B1836323
theorem B896537 : Blo 595291 896537 := bstep (se 2 (by rfl) ⟨336201, by rfl⟩ : syracuseStep 896537 = 672403) B672403
theorem B2010689 : Blo 595291 2010689 := bstep (se 2 (by rfl) ⟨754008, by rfl⟩ : syracuseStep 2010689 = 1508017) B1508017
theorem B896651 : Blo 595291 896651 := bstep (se 1 (by rfl) ⟨672488, by rfl⟩ : syracuseStep 896651 = 1344977) B1344977
theorem B896663 : Blo 595291 896663 := bstep (se 1 (by rfl) ⟨672497, by rfl⟩ : syracuseStep 896663 = 1344995) B1344995
theorem B2043571 : Blo 595291 2043571 := bstep (se 1 (by rfl) ⟨1532678, by rfl⟩ : syracuseStep 2043571 = 3065357) B3065357
theorem B2272961 : Blo 595291 2272961 := bstep (se 2 (by rfl) ⟨852360, by rfl⟩ : syracuseStep 2272961 = 1704721) B1704721
theorem B896729 : Blo 595291 896729 := bstep (se 2 (by rfl) ⟨336273, by rfl⟩ : syracuseStep 896729 = 672547) B672547
theorem B896843 : Blo 595291 896843 := bstep (se 1 (by rfl) ⟨672632, by rfl⟩ : syracuseStep 896843 = 1345265) B1345265
theorem B896855 : Blo 595291 896855 := bstep (se 1 (by rfl) ⟨672641, by rfl⟩ : syracuseStep 896855 = 1345283) B1345283
theorem B896921 : Blo 595291 896921 := bstep (se 2 (by rfl) ⟨336345, by rfl⟩ : syracuseStep 896921 = 672691) B672691
theorem B1552321 : Blo 595291 1552321 := bstep (se 2 (by rfl) ⟨582120, by rfl⟩ : syracuseStep 1552321 = 1164241) B1164241
theorem B1814489 : Blo 595291 1814489 := bstep (se 2 (by rfl) ⟨680433, by rfl⟩ : syracuseStep 1814489 = 1360867) B1360867
theorem B2306009 : Blo 595291 2306009 := bstep (se 2 (by rfl) ⟨864753, by rfl⟩ : syracuseStep 2306009 = 1729507) B1729507
theorem B897035 : Blo 595291 897035 := bstep (se 1 (by rfl) ⟨672776, by rfl⟩ : syracuseStep 897035 = 1345553) B1345553
theorem B897047 : Blo 595291 897047 := bstep (se 1 (by rfl) ⟨672785, by rfl⟩ : syracuseStep 897047 = 1345571) B1345571
theorem B897113 : Blo 595291 897113 := bstep (se 2 (by rfl) ⟨336417, by rfl⟩ : syracuseStep 897113 = 672835) B672835
theorem B2011229 : Blo 595291 2011229 := bstep (se 3 (by rfl) ⟨377105, by rfl⟩ : syracuseStep 2011229 = 754211) B754211
theorem B897227 : Blo 595291 897227 := bstep (se 1 (by rfl) ⟨672920, by rfl⟩ : syracuseStep 897227 = 1345841) B1345841
theorem B897239 : Blo 595291 897239 := bstep (se 1 (by rfl) ⟨672929, by rfl⟩ : syracuseStep 897239 = 1345859) B1345859
theorem B897305 : Blo 595291 897305 := bstep (se 2 (by rfl) ⟨336489, by rfl⟩ : syracuseStep 897305 = 672979) B672979
theorem B3027293 : Blo 595291 3027293 := bstep (se 3 (by rfl) ⟨567617, by rfl⟩ : syracuseStep 3027293 = 1135235) B1135235
theorem B2273629 : Blo 595291 2273629 := bstep (se 3 (by rfl) ⟨426305, by rfl⟩ : syracuseStep 2273629 = 852611) B852611
theorem B897419 : Blo 595291 897419 := bstep (se 1 (by rfl) ⟨673064, by rfl⟩ : syracuseStep 897419 = 1346129) B1346129
theorem B897431 : Blo 595291 897431 := bstep (se 1 (by rfl) ⟨673073, by rfl⟩ : syracuseStep 897431 = 1346147) B1346147
theorem B6795737 : Blo 595291 6795737 := bstep (se 2 (by rfl) ⟨2548401, by rfl⟩ : syracuseStep 6795737 = 5096803) B5096803
theorem B897497 : Blo 595291 897497 := bstep (se 2 (by rfl) ⟨336561, by rfl⟩ : syracuseStep 897497 = 673123) B673123
theorem B897611 : Blo 595291 897611 := bstep (se 1 (by rfl) ⟨673208, by rfl⟩ : syracuseStep 897611 = 1346417) B1346417
theorem B897623 : Blo 595291 897623 := bstep (se 1 (by rfl) ⟨673217, by rfl⟩ : syracuseStep 897623 = 1346435) B1346435
theorem B897689 : Blo 595291 897689 := bstep (se 2 (by rfl) ⟨336633, by rfl⟩ : syracuseStep 897689 = 673267) B673267
theorem B897803 : Blo 595291 897803 := bstep (se 1 (by rfl) ⟨673352, by rfl⟩ : syracuseStep 897803 = 1346705) B1346705
theorem B897815 : Blo 595291 897815 := bstep (se 1 (by rfl) ⟨673361, by rfl⟩ : syracuseStep 897815 = 1346723) B1346723
theorem B4436801 : Blo 595291 4436801 := bstep (se 2 (by rfl) ⟨1663800, by rfl⟩ : syracuseStep 4436801 = 3327601) B3327601
theorem B897881 : Blo 595291 897881 := bstep (se 2 (by rfl) ⟨336705, by rfl⟩ : syracuseStep 897881 = 673411) B673411
theorem B897995 : Blo 595291 897995 := bstep (se 1 (by rfl) ⟨673496, by rfl⟩ : syracuseStep 897995 = 1346993) B1346993
theorem B898007 : Blo 595291 898007 := bstep (se 1 (by rfl) ⟨673505, by rfl⟩ : syracuseStep 898007 = 1347011) B1347011
theorem B2765785 : Blo 595291 2765785 := bstep (se 2 (by rfl) ⟨1037169, by rfl⟩ : syracuseStep 2765785 = 2074339) B2074339
theorem B898073 : Blo 595291 898073 := bstep (se 2 (by rfl) ⟨336777, by rfl⟩ : syracuseStep 898073 = 673555) B673555
theorem B898187 : Blo 595291 898187 := bstep (se 1 (by rfl) ⟨673640, by rfl⟩ : syracuseStep 898187 = 1347281) B1347281
theorem B898199 : Blo 595291 898199 := bstep (se 1 (by rfl) ⟨673649, by rfl⟩ : syracuseStep 898199 = 1347299) B1347299
theorem B2012363 : Blo 595291 2012363 := bstep (se 1 (by rfl) ⟨1509272, by rfl⟩ : syracuseStep 2012363 = 3018545) B3018545
theorem B898265 : Blo 595291 898265 := bstep (se 2 (by rfl) ⟨336849, by rfl⟩ : syracuseStep 898265 = 673699) B673699
theorem B898379 : Blo 595291 898379 := bstep (se 1 (by rfl) ⟨673784, by rfl⟩ : syracuseStep 898379 = 1347569) B1347569
theorem B898391 : Blo 595291 898391 := bstep (se 1 (by rfl) ⟨673793, by rfl⟩ : syracuseStep 898391 = 1347587) B1347587
theorem B1914263 : Blo 595291 1914263 := bstep (se 1 (by rfl) ⟨1435697, by rfl⟩ : syracuseStep 1914263 = 2871395) B2871395
theorem B898457 : Blo 595291 898457 := bstep (se 2 (by rfl) ⟨336921, by rfl⟩ : syracuseStep 898457 = 673843) B673843
theorem B2012633 : Blo 595291 2012633 := bstep (se 2 (by rfl) ⟨754737, by rfl⟩ : syracuseStep 2012633 = 1509475) B1509475
theorem B898571 : Blo 595291 898571 := bstep (se 1 (by rfl) ⟨673928, by rfl⟩ : syracuseStep 898571 = 1347857) B1347857
theorem B898583 : Blo 595291 898583 := bstep (se 1 (by rfl) ⟨673937, by rfl⟩ : syracuseStep 898583 = 1347875) B1347875
theorem B898649 : Blo 595291 898649 := bstep (se 2 (by rfl) ⟨336993, by rfl⟩ : syracuseStep 898649 = 673987) B673987
theorem B2274905 : Blo 595291 2274905 := bstep (se 2 (by rfl) ⟨853089, by rfl⟩ : syracuseStep 2274905 = 1706179) B1706179
theorem B898763 : Blo 595291 898763 := bstep (se 1 (by rfl) ⟨674072, by rfl⟩ : syracuseStep 898763 = 1348145) B1348145
theorem B898775 : Blo 595291 898775 := bstep (se 1 (by rfl) ⟨674081, by rfl⟩ : syracuseStep 898775 = 1348163) B1348163
theorem B898841 : Blo 595291 898841 := bstep (se 2 (by rfl) ⟨337065, by rfl⟩ : syracuseStep 898841 = 674131) B674131
theorem B669739 : Blo 595291 669739 := bstep (se 1 (by rfl) ⟨502304, by rfl⟩ : syracuseStep 669739 = 1004609) B1004609
theorem B669847 : Blo 595291 669847 := bstep (se 1 (by rfl) ⟨502385, by rfl⟩ : syracuseStep 669847 = 1004771) B1004771
theorem B2013335 : Blo 595291 2013335 := bstep (se 1 (by rfl) ⟨1510001, by rfl⟩ : syracuseStep 2013335 = 3020003) B3020003
theorem B670027 : Blo 595291 670027 := bstep (se 1 (by rfl) ⟨502520, by rfl⟩ : syracuseStep 670027 = 1005041) B1005041
theorem B1816921 : Blo 595291 1816921 := bstep (se 2 (by rfl) ⟨681345, by rfl⟩ : syracuseStep 1816921 = 1362691) B1362691
theorem B3029399 : Blo 595291 3029399 := bstep (se 1 (by rfl) ⟨2272049, by rfl⟩ : syracuseStep 3029399 = 4544099) B4544099
theorem B670135 : Blo 595291 670135 := bstep (se 1 (by rfl) ⟨502601, by rfl⟩ : syracuseStep 670135 = 1005203) B1005203
theorem B670315 : Blo 595291 670315 := bstep (se 1 (by rfl) ⟨502736, by rfl⟩ : syracuseStep 670315 = 1005473) B1005473
theorem B637579 : Blo 595291 637579 := bstep (se 1 (by rfl) ⟨478184, by rfl⟩ : syracuseStep 637579 = 956369) B956369
theorem B2013875 : Blo 595291 2013875 := bstep (se 1 (by rfl) ⟨1510406, by rfl⟩ : syracuseStep 2013875 = 3020813) B3020813
theorem B670423 : Blo 595291 670423 := bstep (se 1 (by rfl) ⟨502817, by rfl⟩ : syracuseStep 670423 = 1005635) B1005635
theorem B16169827 : Blo 595291 16169827 := bstep (se 1 (by rfl) ⟨12127370, by rfl⟩ : syracuseStep 16169827 = 24254741) B24254741
theorem B670603 : Blo 595291 670603 := bstep (se 1 (by rfl) ⟨502952, by rfl⟩ : syracuseStep 670603 = 1005905) B1005905
theorem B2014145 : Blo 595291 2014145 := bstep (se 2 (by rfl) ⟨755304, by rfl⟩ : syracuseStep 2014145 = 1510609) B1510609
theorem B670711 : Blo 595291 670711 := bstep (se 1 (by rfl) ⟨503033, by rfl⟩ : syracuseStep 670711 = 1006067) B1006067
theorem B670891 : Blo 595291 670891 := bstep (se 1 (by rfl) ⟨503168, by rfl⟩ : syracuseStep 670891 = 1006337) B1006337
theorem B670999 : Blo 595291 670999 := bstep (se 1 (by rfl) ⟨503249, by rfl⟩ : syracuseStep 670999 = 1006499) B1006499
theorem B638327 : Blo 595291 638327 := bstep (se 1 (by rfl) ⟨478745, by rfl⟩ : syracuseStep 638327 = 957491) B957491
theorem B671179 : Blo 595291 671179 := bstep (se 1 (by rfl) ⟨503384, by rfl⟩ : syracuseStep 671179 = 1006769) B1006769
theorem B2014685 : Blo 595291 2014685 := bstep (se 3 (by rfl) ⟨377753, by rfl⟩ : syracuseStep 2014685 = 755507) B755507
theorem B12271121 : Blo 595291 12271121 := bstep (se 2 (by rfl) ⟨4601670, by rfl⟩ : syracuseStep 12271121 = 9203341) B9203341
theorem B671287 : Blo 595291 671287 := bstep (se 1 (by rfl) ⟨503465, by rfl⟩ : syracuseStep 671287 = 1006931) B1006931
theorem B671467 : Blo 595291 671467 := bstep (se 1 (by rfl) ⟨503600, by rfl⟩ : syracuseStep 671467 = 1007201) B1007201
theorem B1916723 : Blo 595291 1916723 := bstep (se 1 (by rfl) ⟨1437542, by rfl⟩ : syracuseStep 1916723 = 2875085) B2875085
theorem B671575 : Blo 595291 671575 := bstep (se 1 (by rfl) ⟨503681, by rfl⟩ : syracuseStep 671575 = 1007363) B1007363
theorem B671755 : Blo 595291 671755 := bstep (se 1 (by rfl) ⟨503816, by rfl⟩ : syracuseStep 671755 = 1007633) B1007633
theorem B1130611 : Blo 595291 1130611 := bstep (se 1 (by rfl) ⟨847958, by rfl⟩ : syracuseStep 1130611 = 1695917) B1695917
theorem B671863 : Blo 595291 671863 := bstep (se 1 (by rfl) ⟨503897, by rfl⟩ : syracuseStep 671863 = 1007795) B1007795
theorem B7258243 : Blo 595291 7258243 := bstep (se 1 (by rfl) ⟨5443682, by rfl⟩ : syracuseStep 7258243 = 10887365) B10887365
theorem B1917145 : Blo 595291 1917145 := bstep (se 2 (by rfl) ⟨718929, by rfl⟩ : syracuseStep 1917145 = 1437859) B1437859
theorem B1818845 : Blo 595291 1818845 := bstep (se 3 (by rfl) ⟨341033, by rfl⟩ : syracuseStep 1818845 = 682067) B682067
theorem B672043 : Blo 595291 672043 := bstep (se 1 (by rfl) ⟨504032, by rfl⟩ : syracuseStep 672043 = 1008065) B1008065
theorem B4079917 : Blo 595291 4079917 := bstep (se 3 (by rfl) ⟨764984, by rfl⟩ : syracuseStep 4079917 = 1529969) B1529969
theorem B3228005 : Blo 595291 3228005 := bstep (se 4 (by rfl) ⟨302625, by rfl⟩ : syracuseStep 3228005 = 605251) B605251
theorem B672151 : Blo 595291 672151 := bstep (se 1 (by rfl) ⟨504113, by rfl⟩ : syracuseStep 672151 = 1008227) B1008227
theorem B1917377 : Blo 595291 1917377 := bstep (se 2 (by rfl) ⟨719016, by rfl⟩ : syracuseStep 1917377 = 1438033) B1438033
theorem B1131059 : Blo 595291 1131059 := bstep (se 1 (by rfl) ⟨848294, by rfl⟩ : syracuseStep 1131059 = 1696589) B1696589
theorem B2015819 : Blo 595291 2015819 := bstep (se 1 (by rfl) ⟨1511864, by rfl⟩ : syracuseStep 2015819 = 3023729) B3023729
theorem B672331 : Blo 595291 672331 := bstep (se 1 (by rfl) ⟨504248, by rfl⟩ : syracuseStep 672331 = 1008497) B1008497
theorem B1131097 : Blo 595291 1131097 := bstep (se 2 (by rfl) ⟨424161, by rfl⟩ : syracuseStep 1131097 = 848323) B848323
theorem B639595 : Blo 595291 639595 := bstep (se 1 (by rfl) ⟨479696, by rfl⟩ : syracuseStep 639595 = 959393) B959393
theorem B672439 : Blo 595291 672439 := bstep (se 1 (by rfl) ⟨504329, by rfl⟩ : syracuseStep 672439 = 1008659) B1008659
theorem B4735705 : Blo 595291 4735705 := bstep (se 2 (by rfl) ⟨1775889, by rfl⟩ : syracuseStep 4735705 = 3551779) B3551779
theorem B607019 : Blo 595291 607019 := bstep (se 1 (by rfl) ⟨455264, by rfl⟩ : syracuseStep 607019 = 910529) B910529
theorem B2016089 : Blo 595291 2016089 := bstep (se 2 (by rfl) ⟨756033, by rfl⟩ : syracuseStep 2016089 = 1512067) B1512067
theorem B672619 : Blo 595291 672619 := bstep (se 1 (by rfl) ⟨504464, by rfl⟩ : syracuseStep 672619 = 1008929) B1008929
theorem B672727 : Blo 595291 672727 := bstep (se 1 (by rfl) ⟨504545, by rfl⟩ : syracuseStep 672727 = 1009091) B1009091
theorem B1033177 : Blo 595291 1033177 := bstep (se 2 (by rfl) ⟨387441, by rfl⟩ : syracuseStep 1033177 = 774883) B774883
theorem B1131545 : Blo 595291 1131545 := bstep (se 2 (by rfl) ⟨424329, by rfl⟩ : syracuseStep 1131545 = 848659) B848659
theorem B17187875 : Blo 595291 17187875 := bstep (se 1 (by rfl) ⟨12890906, by rfl⟩ : syracuseStep 17187875 = 25781813) B25781813
theorem B4310117 : Blo 595291 4310117 := bstep (se 4 (by rfl) ⟨404073, by rfl⟩ : syracuseStep 4310117 = 808147) B808147
theorem B672907 : Blo 595291 672907 := bstep (se 1 (by rfl) ⟨504680, by rfl⟩ : syracuseStep 672907 = 1009361) B1009361
theorem B673015 : Blo 595291 673015 := bstep (se 1 (by rfl) ⟨504761, by rfl⟩ : syracuseStep 673015 = 1009523) B1009523
theorem B9684269 : Blo 595291 9684269 := bstep (se 3 (by rfl) ⟨1815800, by rfl⟩ : syracuseStep 9684269 = 3631601) B3631601
theorem B673195 : Blo 595291 673195 := bstep (se 1 (by rfl) ⟨504896, by rfl⟩ : syracuseStep 673195 = 1009793) B1009793
theorem B2016791 : Blo 595291 2016791 := bstep (se 1 (by rfl) ⟨1512593, by rfl⟩ : syracuseStep 2016791 = 3025187) B3025187
theorem B673303 : Blo 595291 673303 := bstep (se 1 (by rfl) ⟨504977, by rfl⟩ : syracuseStep 673303 = 1009955) B1009955
theorem B673483 : Blo 595291 673483 := bstep (se 1 (by rfl) ⟨505112, by rfl⟩ : syracuseStep 673483 = 1010225) B1010225
theorem B1132289 : Blo 595291 1132289 := bstep (se 2 (by rfl) ⟨424608, by rfl⟩ : syracuseStep 1132289 = 849217) B849217
theorem B673591 : Blo 595291 673591 := bstep (se 1 (by rfl) ⟨505193, by rfl⟩ : syracuseStep 673591 = 1010387) B1010387
theorem B3032963 : Blo 595291 3032963 := bstep (se 1 (by rfl) ⟨2274722, by rfl⟩ : syracuseStep 3032963 = 4549445) B4549445
theorem B5457881 : Blo 595291 5457881 := bstep (se 2 (by rfl) ⟨2046705, by rfl⟩ : syracuseStep 5457881 = 4093411) B4093411
theorem B673771 : Blo 595291 673771 := bstep (se 1 (by rfl) ⟨505328, by rfl⟩ : syracuseStep 673771 = 1010657) B1010657
theorem B1132555 : Blo 595291 1132555 := bstep (se 1 (by rfl) ⟨849416, by rfl⟩ : syracuseStep 1132555 = 1698833) B1698833
theorem B2017331 : Blo 595291 2017331 := bstep (se 1 (by rfl) ⟨1512998, by rfl⟩ : syracuseStep 2017331 = 3025997) B3025997
theorem B673879 : Blo 595291 673879 := bstep (se 1 (by rfl) ⟨505409, by rfl⟩ : syracuseStep 673879 = 1010819) B1010819
theorem B1296523 : Blo 595291 1296523 := bstep (se 1 (by rfl) ⟨972392, by rfl⟩ : syracuseStep 1296523 = 1944785) B1944785
theorem B4311245 : Blo 595291 4311245 := bstep (se 3 (by rfl) ⟨808358, by rfl⟩ : syracuseStep 4311245 = 1616717) B1616717
theorem B674059 : Blo 595291 674059 := bstep (se 1 (by rfl) ⟨505544, by rfl⟩ : syracuseStep 674059 = 1011089) B1011089
theorem B2017601 : Blo 595291 2017601 := bstep (se 2 (by rfl) ⟨756600, by rfl⟩ : syracuseStep 2017601 = 1513201) B1513201
theorem B674167 : Blo 595291 674167 := bstep (se 1 (by rfl) ⟨505625, by rfl⟩ : syracuseStep 674167 = 1011251) B1011251
theorem B1133003 : Blo 595291 1133003 := bstep (se 1 (by rfl) ⟨849752, by rfl⟩ : syracuseStep 1133003 = 1699505) B1699505
theorem B2869721 : Blo 595291 2869721 := bstep (se 2 (by rfl) ⟨1076145, by rfl⟩ : syracuseStep 2869721 = 2152291) B2152291
theorem B1133185 : Blo 595291 1133185 := bstep (se 2 (by rfl) ⟨424944, by rfl⟩ : syracuseStep 1133185 = 849889) B849889
theorem B4311731 : Blo 595291 4311731 := bstep (se 1 (by rfl) ⟨3233798, by rfl⟩ : syracuseStep 4311731 = 6467597) B6467597
theorem B2018141 : Blo 595291 2018141 := bstep (se 3 (by rfl) ⟨378401, by rfl⟩ : syracuseStep 2018141 = 756803) B756803
theorem B1919837 : Blo 595291 1919837 := bstep (se 3 (by rfl) ⟨359969, by rfl⟩ : syracuseStep 1919837 = 719939) B719939
theorem B1133527 : Blo 595291 1133527 := bstep (se 1 (by rfl) ⟨850145, by rfl⟩ : syracuseStep 1133527 = 1700291) B1700291
theorem B1133747 : Blo 595291 1133747 := bstep (se 1 (by rfl) ⟨850310, by rfl⟩ : syracuseStep 1133747 = 1700621) B1700621
theorem B3624209 : Blo 595291 3624209 := bstep (se 2 (by rfl) ⟨1359078, by rfl⟩ : syracuseStep 3624209 = 2718157) B2718157
theorem B5098787 : Blo 595291 5098787 := bstep (se 1 (by rfl) ⟨3824090, by rfl⟩ : syracuseStep 5098787 = 7648181) B7648181
theorem B1133975 : Blo 595291 1133975 := bstep (se 1 (by rfl) ⟨850481, by rfl⟩ : syracuseStep 1133975 = 1700963) B1700963
theorem B1134233 : Blo 595291 1134233 := bstep (se 2 (by rfl) ⟨425337, by rfl⟩ : syracuseStep 1134233 = 850675) B850675
theorem B18665315 : Blo 595291 18665315 := bstep (se 1 (by rfl) ⟨13998986, by rfl⟩ : syracuseStep 18665315 = 27997973) B27997973
theorem B806807 : Blo 595291 806807 := bstep (se 1 (by rfl) ⟨605105, by rfl⟩ : syracuseStep 806807 = 1210211) B1210211
theorem B2150317 : Blo 595291 2150317 := bstep (se 3 (by rfl) ⟨403184, by rfl⟩ : syracuseStep 2150317 = 806369) B806369
theorem B2019275 : Blo 595291 2019275 := bstep (se 1 (by rfl) ⟨1514456, by rfl⟩ : syracuseStep 2019275 = 3028913) B3028913
theorem B905177 : Blo 595291 905177 := bstep (se 2 (by rfl) ⟨339441, by rfl⟩ : syracuseStep 905177 = 678883) B678883
theorem B5099537 : Blo 595291 5099537 := bstep (se 2 (by rfl) ⟨1912326, by rfl⟩ : syracuseStep 5099537 = 3824653) B3824653
theorem B1134643 : Blo 595291 1134643 := bstep (se 1 (by rfl) ⟨850982, by rfl⟩ : syracuseStep 1134643 = 1701965) B1701965
theorem B4542641 : Blo 595291 4542641 := bstep (se 2 (by rfl) ⟨1703490, by rfl⟩ : syracuseStep 4542641 = 3406981) B3406981
theorem B7360717 : Blo 595291 7360717 := bstep (se 3 (by rfl) ⟨1380134, by rfl⟩ : syracuseStep 7360717 = 2760269) B2760269
theorem B2019545 : Blo 595291 2019545 := bstep (se 2 (by rfl) ⟨757329, by rfl⟩ : syracuseStep 2019545 = 1514659) B1514659
theorem B1135129 : Blo 595291 1135129 := bstep (se 2 (by rfl) ⟨425673, by rfl⟩ : syracuseStep 1135129 = 851347) B851347
theorem B807499 : Blo 595291 807499 := bstep (se 1 (by rfl) ⟨605624, by rfl⟩ : syracuseStep 807499 = 1211249) B1211249
theorem B4543127 : Blo 595291 4543127 := bstep (se 1 (by rfl) ⟨3407345, by rfl⟩ : syracuseStep 4543127 = 6814691) B6814691
theorem B2544301 : Blo 595291 2544301 := bstep (se 3 (by rfl) ⟨477056, by rfl⟩ : syracuseStep 2544301 = 954113) B954113
theorem B3396275 : Blo 595291 3396275 := bstep (se 1 (by rfl) ⟨2547206, by rfl⟩ : syracuseStep 3396275 = 5094413) B5094413
theorem B2544473 : Blo 595291 2544473 := bstep (se 2 (by rfl) ⟨954177, by rfl⟩ : syracuseStep 2544473 = 1908355) B1908355
theorem B2020247 : Blo 595291 2020247 := bstep (se 1 (by rfl) ⟨1515185, by rfl⟩ : syracuseStep 2020247 = 3030371) B3030371
theorem B1004555 : Blo 595291 1004555 := bstep (se 1 (by rfl) ⟨753416, by rfl⟩ : syracuseStep 1004555 = 1506833) B1506833
theorem B1135691 : Blo 595291 1135691 := bstep (se 1 (by rfl) ⟨851768, by rfl⟩ : syracuseStep 1135691 = 1703537) B1703537
theorem B1004683 : Blo 595291 1004683 := bstep (se 1 (by rfl) ⟨753512, by rfl⟩ : syracuseStep 1004683 = 1507025) B1507025
theorem B1135873 : Blo 595291 1135873 := bstep (se 2 (by rfl) ⟨425952, by rfl⟩ : syracuseStep 1135873 = 851905) B851905
theorem B1004825 : Blo 595291 1004825 := bstep (se 2 (by rfl) ⟨376809, by rfl⟩ : syracuseStep 1004825 = 753619) B753619
theorem B972119 : Blo 595291 972119 := bstep (se 1 (by rfl) ⟨729089, by rfl⟩ : syracuseStep 972119 = 1458179) B1458179
theorem B1004953 : Blo 595291 1004953 := bstep (se 2 (by rfl) ⟨376857, by rfl⟩ : syracuseStep 1004953 = 753715) B753715
theorem B2020787 : Blo 595291 2020787 := bstep (se 1 (by rfl) ⟨1515590, by rfl⟩ : syracuseStep 2020787 = 3031181) B3031181
theorem B808537 : Blo 595291 808537 := bstep (se 2 (by rfl) ⟨303201, by rfl⟩ : syracuseStep 808537 = 606403) B606403
theorem B2021057 : Blo 595291 2021057 := bstep (se 2 (by rfl) ⟨757896, by rfl⟩ : syracuseStep 2021057 = 1515793) B1515793
theorem B3823321 : Blo 595291 3823321 := bstep (se 2 (by rfl) ⟨1433745, by rfl⟩ : syracuseStep 3823321 = 2867491) B2867491
theorem B9656243 : Blo 595291 9656243 := bstep (se 1 (by rfl) ⟨7242182, by rfl⟩ : syracuseStep 9656243 = 14484365) B14484365
theorem B645067 : Blo 595291 645067 := bstep (se 1 (by rfl) ⟨483800, by rfl⟩ : syracuseStep 645067 = 967601) B967601
theorem B1136587 : Blo 595291 1136587 := bstep (se 1 (by rfl) ⟨852440, by rfl⟩ : syracuseStep 1136587 = 1704881) B1704881
theorem B1005527 : Blo 595291 1005527 := bstep (se 1 (by rfl) ⟨754145, by rfl⟩ : syracuseStep 1005527 = 1508291) B1508291
theorem B1136663 : Blo 595291 1136663 := bstep (se 1 (by rfl) ⟨852497, by rfl⟩ : syracuseStep 1136663 = 1704995) B1704995
theorem B1005655 : Blo 595291 1005655 := bstep (se 1 (by rfl) ⟨754241, by rfl⟩ : syracuseStep 1005655 = 1508483) B1508483
theorem B3397733 : Blo 595291 3397733 := bstep (se 4 (by rfl) ⟨318537, by rfl⟩ : syracuseStep 3397733 = 637075) B637075
theorem B2021597 : Blo 595291 2021597 := bstep (se 3 (by rfl) ⟨379049, by rfl⟩ : syracuseStep 2021597 = 758099) B758099
theorem B2546113 : Blo 595291 2546113 := bstep (se 2 (by rfl) ⟨954792, by rfl⟩ : syracuseStep 2546113 = 1909585) B1909585
theorem B2873873 : Blo 595291 2873873 := bstep (se 2 (by rfl) ⟨1077702, by rfl⟩ : syracuseStep 2873873 = 2155405) B2155405
theorem B907865 : Blo 595291 907865 := bstep (se 2 (by rfl) ⟨340449, by rfl⟩ : syracuseStep 907865 = 680899) B680899
theorem B1137331 : Blo 595291 1137331 := bstep (se 1 (by rfl) ⟨852998, by rfl⟩ : syracuseStep 1137331 = 1705997) B1705997
theorem B1006283 : Blo 595291 1006283 := bstep (se 1 (by rfl) ⟨754712, by rfl⟩ : syracuseStep 1006283 = 1509425) B1509425
theorem B1432343 : Blo 595291 1432343 := bstep (se 1 (by rfl) ⟨1074257, by rfl⟩ : syracuseStep 1432343 = 2148515) B2148515
theorem B1366807 : Blo 595291 1366807 := bstep (se 1 (by rfl) ⟨1025105, by rfl⟩ : syracuseStep 1366807 = 2050211) B2050211
theorem B1006411 : Blo 595291 1006411 := bstep (se 1 (by rfl) ⟨754808, by rfl⟩ : syracuseStep 1006411 = 1509617) B1509617
theorem B2579293 : Blo 595291 2579293 := bstep (se 3 (by rfl) ⟨483617, by rfl⟩ : syracuseStep 2579293 = 967235) B967235
theorem B1137559 : Blo 595291 1137559 := bstep (se 1 (by rfl) ⟨853169, by rfl⟩ : syracuseStep 1137559 = 1706339) B1706339
theorem B5102513 : Blo 595291 5102513 := bstep (se 2 (by rfl) ⟨1913442, by rfl⟩ : syracuseStep 5102513 = 3826885) B3826885
theorem B1006553 : Blo 595291 1006553 := bstep (se 2 (by rfl) ⟨377457, by rfl⟩ : syracuseStep 1006553 = 754915) B754915
theorem B1137665 : Blo 595291 1137665 := bstep (se 2 (by rfl) ⟨426624, by rfl⟩ : syracuseStep 1137665 = 853249) B853249
theorem B1006681 : Blo 595291 1006681 := bstep (se 2 (by rfl) ⟨377505, by rfl⟩ : syracuseStep 1006681 = 755011) B755011
theorem B1531097 : Blo 595291 1531097 := bstep (se 2 (by rfl) ⟨574161, by rfl⟩ : syracuseStep 1531097 = 1148323) B1148323
theorem B679147 : Blo 595291 679147 := bstep (se 1 (by rfl) ⟨509360, by rfl⟩ : syracuseStep 679147 = 1018721) B1018721
theorem B3825245 : Blo 595291 3825245 := bstep (se 3 (by rfl) ⟨717233, by rfl⟩ : syracuseStep 3825245 = 1434467) B1434467
theorem B1007255 : Blo 595291 1007255 := bstep (se 1 (by rfl) ⟨755441, by rfl⟩ : syracuseStep 1007255 = 1510883) B1510883
theorem B1007383 : Blo 595291 1007383 := bstep (se 1 (by rfl) ⟨755537, by rfl⟩ : syracuseStep 1007383 = 1511075) B1511075
theorem B1695563 : Blo 595291 1695563 := bstep (se 1 (by rfl) ⟨1271672, by rfl⟩ : syracuseStep 1695563 = 2543345) B2543345
theorem B2547787 : Blo 595291 2547787 := bstep (se 1 (by rfl) ⟨1910840, by rfl⟩ : syracuseStep 2547787 = 3821681) B3821681
theorem B8151191 : Blo 595291 8151191 := bstep (se 1 (by rfl) ⟨6113393, by rfl⟩ : syracuseStep 8151191 = 12226787) B12226787
theorem B2187415 : Blo 595291 2187415 := bstep (se 1 (by rfl) ⟨1640561, by rfl⟩ : syracuseStep 2187415 = 3281123) B3281123
theorem B2548061 : Blo 595291 2548061 := bstep (se 3 (by rfl) ⟨477761, by rfl⟩ : syracuseStep 2548061 = 955523) B955523
theorem B1008011 : Blo 595291 1008011 := bstep (se 1 (by rfl) ⟨756008, by rfl⟩ : syracuseStep 1008011 = 1512017) B1512017
theorem B1008139 : Blo 595291 1008139 := bstep (se 1 (by rfl) ⟨756104, by rfl⟩ : syracuseStep 1008139 = 1512209) B1512209
theorem B4317731 : Blo 595291 4317731 := bstep (se 1 (by rfl) ⟨3238298, by rfl⟩ : syracuseStep 4317731 = 6476597) B6476597
theorem B1008281 : Blo 595291 1008281 := bstep (se 2 (by rfl) ⟨378105, by rfl⟩ : syracuseStep 1008281 = 756211) B756211
theorem B1008409 : Blo 595291 1008409 := bstep (se 2 (by rfl) ⟨378153, by rfl⟩ : syracuseStep 1008409 = 756307) B756307
theorem B2581379 : Blo 595291 2581379 := bstep (se 1 (by rfl) ⟨1936034, by rfl⟩ : syracuseStep 2581379 = 3872069) B3872069
theorem B2188205 : Blo 595291 2188205 := bstep (se 3 (by rfl) ⟨410288, by rfl⟩ : syracuseStep 2188205 = 820577) B820577
theorem B1434775 : Blo 595291 1434775 := bstep (se 1 (by rfl) ⟨1076081, by rfl⟩ : syracuseStep 1434775 = 2152163) B2152163
theorem B1008983 : Blo 595291 1008983 := bstep (se 1 (by rfl) ⟨756737, by rfl⟩ : syracuseStep 1008983 = 1513475) B1513475
theorem B1697203 : Blo 595291 1697203 := bstep (se 1 (by rfl) ⟨1272902, by rfl⟩ : syracuseStep 1697203 = 2545805) B2545805
theorem B681419 : Blo 595291 681419 := bstep (se 1 (by rfl) ⟨511064, by rfl⟩ : syracuseStep 681419 = 1022129) B1022129
theorem B1074647 : Blo 595291 1074647 := bstep (se 1 (by rfl) ⟨805985, by rfl⟩ : syracuseStep 1074647 = 1611971) B1611971
theorem B1009111 : Blo 595291 1009111 := bstep (se 1 (by rfl) ⟨756833, by rfl⟩ : syracuseStep 1009111 = 1513667) B1513667
theorem B1697431 : Blo 595291 1697431 := bstep (se 1 (by rfl) ⟨1273073, by rfl⟩ : syracuseStep 1697431 = 2546147) B2546147
theorem B1271639 : Blo 595291 1271639 := bstep (se 1 (by rfl) ⟨953729, by rfl⟩ : syracuseStep 1271639 = 1907459) B1907459
theorem B1402867 : Blo 595291 1402867 := bstep (se 1 (by rfl) ⟨1052150, by rfl⟩ : syracuseStep 1402867 = 2104301) B2104301
theorem B1271809 : Blo 595291 1271809 := bstep (se 2 (by rfl) ⟨476928, by rfl⟩ : syracuseStep 1271809 = 953857) B953857
theorem B3827729 : Blo 595291 3827729 := bstep (se 2 (by rfl) ⟨1435398, by rfl⟩ : syracuseStep 3827729 = 2870797) B2870797
theorem B1075223 : Blo 595291 1075223 := bstep (se 1 (by rfl) ⟨806417, by rfl⟩ : syracuseStep 1075223 = 1612835) B1612835
theorem B5433389 : Blo 595291 5433389 := bstep (se 3 (by rfl) ⟨1018760, by rfl⟩ : syracuseStep 5433389 = 2037521) B2037521
theorem B1009739 : Blo 595291 1009739 := bstep (se 1 (by rfl) ⟨757304, by rfl⟩ : syracuseStep 1009739 = 1514609) B1514609
theorem B1009867 : Blo 595291 1009867 := bstep (se 1 (by rfl) ⟨757400, by rfl⟩ : syracuseStep 1009867 = 1514801) B1514801
theorem B1010009 : Blo 595291 1010009 := bstep (se 2 (by rfl) ⟨378753, by rfl⟩ : syracuseStep 1010009 = 757507) B757507
theorem B1010137 : Blo 595291 1010137 := bstep (se 2 (by rfl) ⟨378801, by rfl⟩ : syracuseStep 1010137 = 757603) B757603
theorem B5171747 : Blo 595291 5171747 := bstep (se 1 (by rfl) ⟨3878810, by rfl⟩ : syracuseStep 5171747 = 7757621) B7757621
theorem B5171863 : Blo 595291 5171863 := bstep (se 1 (by rfl) ⟨3878897, by rfl⟩ : syracuseStep 5171863 = 7757795) B7757795
theorem B9693877 : Blo 595291 9693877 := bstep (se 5 (by rfl) ⟨454400, by rfl⟩ : syracuseStep 9693877 = 908801) B908801
theorem B6810317 : Blo 595291 6810317 := bstep (se 3 (by rfl) ⟨1276934, by rfl⟩ : syracuseStep 6810317 = 2553869) B2553869
theorem B1436467 : Blo 595291 1436467 := bstep (se 1 (by rfl) ⟨1077350, by rfl⟩ : syracuseStep 1436467 = 2154701) B2154701
theorem B1207219 : Blo 595291 1207219 := bstep (se 1 (by rfl) ⟨905414, by rfl⟩ : syracuseStep 1207219 = 1810829) B1810829
theorem B1010711 : Blo 595291 1010711 := bstep (se 1 (by rfl) ⟨758033, by rfl⟩ : syracuseStep 1010711 = 1516067) B1516067
theorem B1272971 : Blo 595291 1272971 := bstep (se 1 (by rfl) ⟨954728, by rfl⟩ : syracuseStep 1272971 = 1909457) B1909457
theorem B1010839 : Blo 595291 1010839 := bstep (se 1 (by rfl) ⟨758129, by rfl⟩ : syracuseStep 1010839 = 1516259) B1516259
theorem B1699289 : Blo 595291 1699289 := bstep (se 2 (by rfl) ⟨637233, by rfl⟩ : syracuseStep 1699289 = 1274467) B1274467
theorem B716311 : Blo 595291 716311 := bstep (se 1 (by rfl) ⟨537233, by rfl⟩ : syracuseStep 716311 = 1074467) B1074467
theorem B4550417 : Blo 595291 4550417 := bstep (se 2 (by rfl) ⟨1706406, by rfl⟩ : syracuseStep 4550417 = 3412813) B3412813
theorem B3403565 : Blo 595291 3403565 := bstep (se 3 (by rfl) ⟨638168, by rfl⟩ : syracuseStep 3403565 = 1276337) B1276337
theorem B1535819 : Blo 595291 1535819 := bstep (se 1 (by rfl) ⟨1151864, by rfl⟩ : syracuseStep 1535819 = 2303729) B2303729
theorem B1273715 : Blo 595291 1273715 := bstep (se 1 (by rfl) ⟨955286, by rfl⟩ : syracuseStep 1273715 = 1910573) B1910573
theorem B1339415 : Blo 595291 1339415 := bstep (se 1 (by rfl) ⟨1004561, by rfl⟩ : syracuseStep 1339415 = 2009123) B2009123
theorem B1208459 : Blo 595291 1208459 := bstep (se 1 (by rfl) ⟨906344, by rfl⟩ : syracuseStep 1208459 = 1812689) B1812689
theorem B1339595 : Blo 595291 1339595 := bstep (se 1 (by rfl) ⟨1004696, by rfl⟩ : syracuseStep 1339595 = 2009393) B2009393
theorem B1339649 : Blo 595291 1339649 := bstep (se 2 (by rfl) ⟨502368, by rfl⟩ : syracuseStep 1339649 = 1004737) B1004737
theorem B1700119 : Blo 595291 1700119 := bstep (se 1 (by rfl) ⟨1275089, by rfl⟩ : syracuseStep 1700119 = 2550179) B2550179
theorem B2158979 : Blo 595291 2158979 := bstep (se 1 (by rfl) ⟨1619234, by rfl⟩ : syracuseStep 2158979 = 3238469) B3238469
theorem B1339865 : Blo 595291 1339865 := bstep (se 2 (by rfl) ⟨502449, by rfl⟩ : syracuseStep 1339865 = 1004899) B1004899
theorem B1077761 : Blo 595291 1077761 := bstep (se 2 (by rfl) ⟨404160, by rfl⟩ : syracuseStep 1077761 = 808321) B808321
theorem B1339955 : Blo 595291 1339955 := bstep (se 1 (by rfl) ⟨1004966, by rfl⟩ : syracuseStep 1339955 = 2009933) B2009933
theorem B1339991 : Blo 595291 1339991 := bstep (se 1 (by rfl) ⟨1004993, by rfl⟩ : syracuseStep 1339991 = 2009987) B2009987
theorem B11465347 : Blo 595291 11465347 := bstep (se 1 (by rfl) ⟨8599010, by rfl⟩ : syracuseStep 11465347 = 17198021) B17198021
theorem B1274611 : Blo 595291 1274611 := bstep (se 1 (by rfl) ⟨955958, by rfl⟩ : syracuseStep 1274611 = 1911917) B1911917
theorem B1340171 : Blo 595291 1340171 := bstep (se 1 (by rfl) ⟨1005128, by rfl⟩ : syracuseStep 1340171 = 2010257) B2010257
theorem B1340225 : Blo 595291 1340225 := bstep (se 2 (by rfl) ⟨502584, by rfl⟩ : syracuseStep 1340225 = 1005169) B1005169
theorem B16380737 : Blo 595291 16380737 := bstep (se 2 (by rfl) ⟨6142776, by rfl⟩ : syracuseStep 16380737 = 12285553) B12285553
theorem B1340441 : Blo 595291 1340441 := bstep (se 2 (by rfl) ⟨502665, by rfl⟩ : syracuseStep 1340441 = 1005331) B1005331
theorem B2552897 : Blo 595291 2552897 := bstep (se 2 (by rfl) ⟨957336, by rfl⟩ : syracuseStep 2552897 = 1914673) B1914673
theorem B1700939 : Blo 595291 1700939 := bstep (se 1 (by rfl) ⟨1275704, by rfl⟩ : syracuseStep 1700939 = 2551409) B2551409
theorem B1340531 : Blo 595291 1340531 := bstep (se 1 (by rfl) ⟨1005398, by rfl⟩ : syracuseStep 1340531 = 2010797) B2010797
theorem B1340567 : Blo 595291 1340567 := bstep (se 1 (by rfl) ⟨1005425, by rfl⟩ : syracuseStep 1340567 = 2010851) B2010851
theorem B2553049 : Blo 595291 2553049 := bstep (se 2 (by rfl) ⟨957393, by rfl⟩ : syracuseStep 2553049 = 1914787) B1914787
theorem B718103 : Blo 595291 718103 := bstep (se 1 (by rfl) ⟨538577, by rfl⟩ : syracuseStep 718103 = 1077155) B1077155
theorem B1340747 : Blo 595291 1340747 := bstep (se 1 (by rfl) ⟨1005560, by rfl⟩ : syracuseStep 1340747 = 2011121) B2011121
theorem B2585945 : Blo 595291 2585945 := bstep (se 2 (by rfl) ⟨969729, by rfl⟩ : syracuseStep 2585945 = 1939459) B1939459
theorem B1340801 : Blo 595291 1340801 := bstep (se 2 (by rfl) ⟨502800, by rfl⟩ : syracuseStep 1340801 = 1005601) B1005601
theorem B1078849 : Blo 595291 1078849 := bstep (se 2 (by rfl) ⟨404568, by rfl⟩ : syracuseStep 1078849 = 809137) B809137
theorem B718411 : Blo 595291 718411 := bstep (se 1 (by rfl) ⟨538808, by rfl⟩ : syracuseStep 718411 = 1077617) B1077617
theorem B1341017 : Blo 595291 1341017 := bstep (se 2 (by rfl) ⟨502881, by rfl⟩ : syracuseStep 1341017 = 1005763) B1005763
theorem B1537625 : Blo 595291 1537625 := bstep (se 2 (by rfl) ⟨576609, by rfl⟩ : syracuseStep 1537625 = 1153219) B1153219
theorem B1341107 : Blo 595291 1341107 := bstep (se 1 (by rfl) ⟨1005830, by rfl⟩ : syracuseStep 1341107 = 2011661) B2011661
theorem B1341143 : Blo 595291 1341143 := bstep (se 1 (by rfl) ⟨1005857, by rfl⟩ : syracuseStep 1341143 = 2011715) B2011715
theorem B1275671 : Blo 595291 1275671 := bstep (se 1 (by rfl) ⟨956753, by rfl⟩ : syracuseStep 1275671 = 1913507) B1913507
theorem B1341323 : Blo 595291 1341323 := bstep (se 1 (by rfl) ⟨1005992, by rfl⟩ : syracuseStep 1341323 = 2011985) B2011985
theorem B149157773 : Blo 595291 149157773 := bstep (se 3 (by rfl) ⟨27967082, by rfl⟩ : syracuseStep 149157773 = 55934165) B55934165
theorem B1341377 : Blo 595291 1341377 := bstep (se 2 (by rfl) ⟨503016, by rfl⟩ : syracuseStep 1341377 = 1006033) B1006033
theorem B1275841 : Blo 595291 1275841 := bstep (se 2 (by rfl) ⟨478440, by rfl⟩ : syracuseStep 1275841 = 956881) B956881
theorem B5732369 : Blo 595291 5732369 := bstep (se 2 (by rfl) ⟨2149638, by rfl⟩ : syracuseStep 5732369 = 4299277) B4299277
theorem B850009 : Blo 595291 850009 := bstep (se 2 (by rfl) ⟨318753, by rfl⟩ : syracuseStep 850009 = 637507) B637507
theorem B2586775 : Blo 595291 2586775 := bstep (se 1 (by rfl) ⟨1940081, by rfl⟩ : syracuseStep 2586775 = 3880163) B3880163
theorem B1341593 : Blo 595291 1341593 := bstep (se 2 (by rfl) ⟨503097, by rfl⟩ : syracuseStep 1341593 = 1006195) B1006195
theorem B2291905 : Blo 595291 2291905 := bstep (se 2 (by rfl) ⟨859464, by rfl⟩ : syracuseStep 2291905 = 1718929) B1718929
theorem B5306573 : Blo 595291 5306573 := bstep (se 3 (by rfl) ⟨994982, by rfl⟩ : syracuseStep 5306573 = 1989965) B1989965
theorem B1341683 : Blo 595291 1341683 := bstep (se 1 (by rfl) ⟨1006262, by rfl⟩ : syracuseStep 1341683 = 2012525) B2012525
theorem B1046807 : Blo 595291 1046807 := bstep (se 1 (by rfl) ⟨785105, by rfl⟩ : syracuseStep 1046807 = 1570211) B1570211
theorem B1341719 : Blo 595291 1341719 := bstep (se 1 (by rfl) ⟨1006289, by rfl⟩ : syracuseStep 1341719 = 2012579) B2012579
theorem B1276183 : Blo 595291 1276183 := bstep (se 1 (by rfl) ⟨957137, by rfl⟩ : syracuseStep 1276183 = 1914275) B1914275
theorem B1341899 : Blo 595291 1341899 := bstep (se 1 (by rfl) ⟨1006424, by rfl⟩ : syracuseStep 1341899 = 2012849) B2012849
theorem B1341953 : Blo 595291 1341953 := bstep (se 2 (by rfl) ⟨503232, by rfl⟩ : syracuseStep 1341953 = 1006465) B1006465
theorem B4094509 : Blo 595291 4094509 := bstep (se 3 (by rfl) ⟨767720, by rfl⟩ : syracuseStep 4094509 = 1535441) B1535441
theorem B10877591 : Blo 595291 10877591 := bstep (se 1 (by rfl) ⟨8158193, by rfl⟩ : syracuseStep 10877591 = 16316387) B16316387
theorem B1342169 : Blo 595291 1342169 := bstep (se 2 (by rfl) ⟨503313, by rfl⟩ : syracuseStep 1342169 = 1006627) B1006627
theorem B1342259 : Blo 595291 1342259 := bstep (se 1 (by rfl) ⟨1006694, by rfl⟩ : syracuseStep 1342259 = 2013389) B2013389
theorem B1145675 : Blo 595291 1145675 := bstep (se 1 (by rfl) ⟨859256, by rfl⟩ : syracuseStep 1145675 = 1718513) B1718513
theorem B1342295 : Blo 595291 1342295 := bstep (se 1 (by rfl) ⟨1006721, by rfl⟩ : syracuseStep 1342295 = 2013443) B2013443
theorem B66059225 : Blo 595291 66059225 := bstep (se 2 (by rfl) ⟨24772209, by rfl⟩ : syracuseStep 66059225 = 49544419) B49544419
theorem B1342475 : Blo 595291 1342475 := bstep (se 1 (by rfl) ⟨1006856, by rfl⟩ : syracuseStep 1342475 = 2013713) B2013713
theorem B1342529 : Blo 595291 1342529 := bstep (se 2 (by rfl) ⟨503448, by rfl⟩ : syracuseStep 1342529 = 1006897) B1006897
theorem B1277003 : Blo 595291 1277003 := bstep (se 1 (by rfl) ⟨957752, by rfl⟩ : syracuseStep 1277003 = 1915505) B1915505
theorem B1342745 : Blo 595291 1342745 := bstep (se 2 (by rfl) ⟨503529, by rfl⟩ : syracuseStep 1342745 = 1007059) B1007059
theorem B1342835 : Blo 595291 1342835 := bstep (se 1 (by rfl) ⟨1007126, by rfl⟩ : syracuseStep 1342835 = 2014253) B2014253
theorem B1342871 : Blo 595291 1342871 := bstep (se 1 (by rfl) ⟨1007153, by rfl⟩ : syracuseStep 1342871 = 2014307) B2014307
theorem B3407255 : Blo 595291 3407255 := bstep (se 1 (by rfl) ⟨2555441, by rfl⟩ : syracuseStep 3407255 = 5110883) B5110883
theorem B1277363 : Blo 595291 1277363 := bstep (se 1 (by rfl) ⟨958022, by rfl⟩ : syracuseStep 1277363 = 1916045) B1916045
theorem B1703389 : Blo 595291 1703389 := bstep (se 3 (by rfl) ⟨319385, by rfl⟩ : syracuseStep 1703389 = 638771) B638771
theorem B851467 : Blo 595291 851467 := bstep (se 1 (by rfl) ⟨638600, by rfl⟩ : syracuseStep 851467 = 1277201) B1277201
theorem B1343051 : Blo 595291 1343051 := bstep (se 1 (by rfl) ⟨1007288, by rfl⟩ : syracuseStep 1343051 = 2014577) B2014577
theorem B1343105 : Blo 595291 1343105 := bstep (se 2 (by rfl) ⟨503664, by rfl⟩ : syracuseStep 1343105 = 1007329) B1007329
theorem B6782615 : Blo 595291 6782615 := bstep (se 1 (by rfl) ⟨5086961, by rfl⟩ : syracuseStep 6782615 = 10173923) B10173923
theorem B1506995 : Blo 595291 1506995 := bstep (se 1 (by rfl) ⟨1130246, by rfl⟩ : syracuseStep 1506995 = 2260493) B2260493
theorem B2260781 : Blo 595291 2260781 := bstep (se 3 (by rfl) ⟨423896, by rfl⟩ : syracuseStep 2260781 = 847793) B847793
theorem B2260811 : Blo 595291 2260811 := bstep (se 1 (by rfl) ⟨1695608, by rfl⟩ : syracuseStep 2260811 = 3391217) B3391217
theorem B3833675 : Blo 595291 3833675 := bstep (se 1 (by rfl) ⟨2875256, by rfl⟩ : syracuseStep 3833675 = 5750513) B5750513
theorem B1343321 : Blo 595291 1343321 := bstep (se 2 (by rfl) ⟨503745, by rfl⟩ : syracuseStep 1343321 = 1007491) B1007491
theorem B1343411 : Blo 595291 1343411 := bstep (se 1 (by rfl) ⟨1007558, by rfl⟩ : syracuseStep 1343411 = 2015117) B2015117
theorem B1343447 : Blo 595291 1343447 := bstep (se 1 (by rfl) ⟨1007585, by rfl⟩ : syracuseStep 1343447 = 2015171) B2015171
theorem B3407939 : Blo 595291 3407939 := bstep (se 1 (by rfl) ⟨2555954, by rfl⟩ : syracuseStep 3407939 = 5111909) B5111909
theorem B2293879 : Blo 595291 2293879 := bstep (se 1 (by rfl) ⟨1720409, by rfl⟩ : syracuseStep 2293879 = 3440819) B3440819
theorem B1212563 : Blo 595291 1212563 := bstep (se 1 (by rfl) ⟨909422, by rfl⟩ : syracuseStep 1212563 = 1818845) B1818845
theorem B1507481 : Blo 595291 1507481 := bstep (se 2 (by rfl) ⟨565305, by rfl⟩ : syracuseStep 1507481 = 1130611) B1130611
theorem B2916553 : Blo 595291 2916553 := bstep (se 2 (by rfl) ⟨1093707, by rfl⟩ : syracuseStep 2916553 = 2187415) B2187415
theorem B2556193 : Blo 595291 2556193 := bstep (se 2 (by rfl) ⟨958572, by rfl⟩ : syracuseStep 2556193 = 1917145) B1917145
theorem B1278251 : Blo 595291 1278251 := bstep (se 1 (by rfl) ⟨958688, by rfl⟩ : syracuseStep 1278251 = 1917377) B1917377
theorem B1507643 : Blo 595291 1507643 := bstep (se 1 (by rfl) ⟨1130732, by rfl⟩ : syracuseStep 1507643 = 2261465) B2261465
theorem B754039 : Blo 595291 754039 := bstep (se 1 (by rfl) ⟨565529, by rfl⟩ : syracuseStep 754039 = 1131059) B1131059
theorem B1704311 : Blo 595291 1704311 := bstep (se 1 (by rfl) ⟨1278233, by rfl⟩ : syracuseStep 1704311 = 2556467) B2556467
theorem B1343879 : Blo 595291 1343879 := bstep (se 1 (by rfl) ⟨1007909, by rfl⟩ : syracuseStep 1343879 = 2015819) B2015819
theorem B5439889 : Blo 595291 5439889 := bstep (se 2 (by rfl) ⟨2039958, by rfl⟩ : syracuseStep 5439889 = 4079917) B4079917
theorem B1507855 : Blo 595291 1507855 := bstep (se 1 (by rfl) ⟨1130891, by rfl⟩ : syracuseStep 1507855 = 2261783) B2261783
theorem B1344059 : Blo 595291 1344059 := bstep (se 1 (by rfl) ⟨1008044, by rfl⟩ : syracuseStep 1344059 = 2016089) B2016089
theorem B2556535 : Blo 595291 2556535 := bstep (se 1 (by rfl) ⟨1917401, by rfl⟩ : syracuseStep 2556535 = 3834803) B3834803
theorem B1344185 : Blo 595291 1344185 := bstep (se 2 (by rfl) ⟨504069, by rfl⟩ : syracuseStep 1344185 = 1008139) B1008139
theorem B754363 : Blo 595291 754363 := bstep (se 1 (by rfl) ⟨565772, by rfl⟩ : syracuseStep 754363 = 1131545) B1131545
theorem B1508129 : Blo 595291 1508129 := bstep (se 2 (by rfl) ⟨565548, by rfl⟩ : syracuseStep 1508129 = 1131097) B1131097
theorem B6456179 : Blo 595291 6456179 := bstep (se 1 (by rfl) ⟨4842134, by rfl⟩ : syracuseStep 6456179 = 9684269) B9684269
theorem B12223493 : Blo 595291 12223493 := bstep (se 4 (by rfl) ⟨1145952, by rfl⟩ : syracuseStep 12223493 = 2291905) B2291905
theorem B1344527 : Blo 595291 1344527 := bstep (se 1 (by rfl) ⟨1008395, by rfl⟩ : syracuseStep 1344527 = 2016791) B2016791
theorem B1344545 : Blo 595291 1344545 := bstep (se 2 (by rfl) ⟨504204, by rfl⟩ : syracuseStep 1344545 = 1008409) B1008409
theorem B754859 : Blo 595291 754859 := bstep (se 1 (by rfl) ⟨566144, by rfl⟩ : syracuseStep 754859 = 1132289) B1132289
theorem B1377569 : Blo 595291 1377569 := bstep (se 2 (by rfl) ⟨516588, by rfl⟩ : syracuseStep 1377569 = 1033177) B1033177
theorem B1344887 : Blo 595291 1344887 := bstep (se 1 (by rfl) ⟨1008665, by rfl⟩ : syracuseStep 1344887 = 2017331) B2017331
theorem B1345067 : Blo 595291 1345067 := bstep (se 1 (by rfl) ⟨1008800, by rfl⟩ : syracuseStep 1345067 = 2017601) B2017601
theorem B755335 : Blo 595291 755335 := bstep (se 1 (by rfl) ⟨566501, by rfl⟩ : syracuseStep 755335 = 1133003) B1133003
theorem B1509131 : Blo 595291 1509131 := bstep (se 1 (by rfl) ⟨1131848, by rfl⟩ : syracuseStep 1509131 = 2263697) B2263697
theorem B3409715 : Blo 595291 3409715 := bstep (se 1 (by rfl) ⟨2557286, by rfl⟩ : syracuseStep 3409715 = 5114573) B5114573
theorem B1345427 : Blo 595291 1345427 := bstep (se 1 (by rfl) ⟨1009070, by rfl⟩ : syracuseStep 1345427 = 2018141) B2018141
theorem B1279891 : Blo 595291 1279891 := bstep (se 1 (by rfl) ⟨959918, by rfl⟩ : syracuseStep 1279891 = 1919837) B1919837
theorem B3016601 : Blo 595291 3016601 := bstep (se 2 (by rfl) ⟨1131225, by rfl⟩ : syracuseStep 3016601 = 2262451) B2262451
theorem B2262937 : Blo 595291 2262937 := bstep (se 2 (by rfl) ⟨848601, by rfl⟩ : syracuseStep 2262937 = 1697203) B1697203
theorem B1345481 : Blo 595291 1345481 := bstep (se 2 (by rfl) ⟨504555, by rfl⟩ : syracuseStep 1345481 = 1009111) B1009111
theorem B755831 : Blo 595291 755831 := bstep (se 1 (by rfl) ⟨566873, by rfl⟩ : syracuseStep 755831 = 1133747) B1133747
theorem B2263241 : Blo 595291 2263241 := bstep (se 2 (by rfl) ⟨848715, by rfl⟩ : syracuseStep 2263241 = 1697431) B1697431
theorem B755983 : Blo 595291 755983 := bstep (se 1 (by rfl) ⟨566987, by rfl⟩ : syracuseStep 755983 = 1133975) B1133975
theorem B1509779 : Blo 595291 1509779 := bstep (se 1 (by rfl) ⟨1132334, by rfl⟩ : syracuseStep 1509779 = 2264669) B2264669
theorem B756155 : Blo 595291 756155 := bstep (se 1 (by rfl) ⟨567116, by rfl⟩ : syracuseStep 756155 = 1134233) B1134233
theorem B1346183 : Blo 595291 1346183 := bstep (se 1 (by rfl) ⟨1009637, by rfl⟩ : syracuseStep 1346183 = 2019275) B2019275
theorem B1870489 : Blo 595291 1870489 := bstep (se 2 (by rfl) ⟨701433, by rfl⟩ : syracuseStep 1870489 = 1402867) B1402867
theorem B1510073 : Blo 595291 1510073 := bstep (se 2 (by rfl) ⟨566277, by rfl⟩ : syracuseStep 1510073 = 1132555) B1132555
theorem B6916913 : Blo 595291 6916913 := bstep (se 2 (by rfl) ⟨2593842, by rfl⟩ : syracuseStep 6916913 = 5187685) B5187685
theorem B1346363 : Blo 595291 1346363 := bstep (se 1 (by rfl) ⟨1009772, by rfl⟩ : syracuseStep 1346363 = 2019545) B2019545
theorem B1346489 : Blo 595291 1346489 := bstep (se 2 (by rfl) ⟨504933, by rfl⟩ : syracuseStep 1346489 = 1009867) B1009867
theorem B2264183 : Blo 595291 2264183 := bstep (se 1 (by rfl) ⟨1698137, by rfl⟩ : syracuseStep 2264183 = 3396275) B3396275
theorem B3935405 : Blo 595291 3935405 := bstep (se 3 (by rfl) ⟨737888, by rfl⟩ : syracuseStep 3935405 = 1475777) B1475777
theorem B3411173 : Blo 595291 3411173 := bstep (se 4 (by rfl) ⟨319797, by rfl⟩ : syracuseStep 3411173 = 639595) B639595
theorem B1346831 : Blo 595291 1346831 := bstep (se 1 (by rfl) ⟨1010123, by rfl⟩ : syracuseStep 1346831 = 2020247) B2020247
theorem B1346849 : Blo 595291 1346849 := bstep (se 2 (by rfl) ⟨505068, by rfl⟩ : syracuseStep 1346849 = 1010137) B1010137
theorem B1510771 : Blo 595291 1510771 := bstep (se 1 (by rfl) ⟨1133078, by rfl⟩ : syracuseStep 1510771 = 2266157) B2266157
theorem B757127 : Blo 595291 757127 := bstep (se 1 (by rfl) ⟨567845, by rfl⟩ : syracuseStep 757127 = 1135691) B1135691
theorem B1510913 : Blo 595291 1510913 := bstep (se 2 (by rfl) ⟨566592, by rfl⟩ : syracuseStep 1510913 = 1133185) B1133185
theorem B2592317 : Blo 595291 2592317 := bstep (se 3 (by rfl) ⟨486059, by rfl⟩ : syracuseStep 2592317 = 972119) B972119
theorem B1347191 : Blo 595291 1347191 := bstep (se 1 (by rfl) ⟨1010393, by rfl⟩ : syracuseStep 1347191 = 2020787) B2020787
theorem B3411629 : Blo 595291 3411629 := bstep (se 3 (by rfl) ⟨639680, by rfl⟩ : syracuseStep 3411629 = 1279361) B1279361
theorem B1969921 : Blo 595291 1969921 := bstep (se 2 (by rfl) ⟨738720, by rfl⟩ : syracuseStep 1969921 = 1477441) B1477441
theorem B1347371 : Blo 595291 1347371 := bstep (se 1 (by rfl) ⟨1010528, by rfl⟩ : syracuseStep 1347371 = 2021057) B2021057
theorem B1609625 : Blo 595291 1609625 := bstep (se 2 (by rfl) ⟨603609, by rfl⟩ : syracuseStep 1609625 = 1207219) B1207219
theorem B1511369 : Blo 595291 1511369 := bstep (se 2 (by rfl) ⟨566763, by rfl⟩ : syracuseStep 1511369 = 1133527) B1133527
theorem B757775 : Blo 595291 757775 := bstep (se 1 (by rfl) ⟨568331, by rfl⟩ : syracuseStep 757775 = 1136663) B1136663
theorem B2265155 : Blo 595291 2265155 := bstep (se 1 (by rfl) ⟨1698866, by rfl⟩ : syracuseStep 2265155 = 3397733) B3397733
theorem B1347731 : Blo 595291 1347731 := bstep (se 1 (by rfl) ⟨1010798, by rfl⟩ : syracuseStep 1347731 = 2021597) B2021597
theorem B1347785 : Blo 595291 1347785 := bstep (se 2 (by rfl) ⟨505419, by rfl⟩ : syracuseStep 1347785 = 1010839) B1010839
theorem B1511723 : Blo 595291 1511723 := bstep (se 1 (by rfl) ⟨1133792, by rfl⟩ : syracuseStep 1511723 = 2267585) B2267585
theorem B3412313 : Blo 595291 3412313 := bstep (se 2 (by rfl) ⟨1279617, by rfl⟩ : syracuseStep 3412313 = 2559235) B2559235
theorem B3019193 : Blo 595291 3019193 := bstep (se 2 (by rfl) ⟨1132197, by rfl⟩ : syracuseStep 3019193 = 2264395) B2264395
theorem B3281411 : Blo 595291 3281411 := bstep (se 1 (by rfl) ⟨2461058, by rfl⟩ : syracuseStep 3281411 = 4922117) B4922117
theorem B955081 : Blo 595291 955081 := bstep (se 2 (by rfl) ⟨358155, by rfl⟩ : syracuseStep 955081 = 716311) B716311
theorem B1020731 : Blo 595291 1020731 := bstep (se 1 (by rfl) ⟨765548, by rfl⟩ : syracuseStep 1020731 = 1531097) B1531097
theorem B2724761 : Blo 595291 2724761 := bstep (se 2 (by rfl) ⟨1021785, by rfl⟩ : syracuseStep 2724761 = 2043571) B2043571
theorem B14554349 : Blo 595291 14554349 := bstep (se 3 (by rfl) ⟨2728940, by rfl⟩ : syracuseStep 14554349 = 5457881) B5457881
theorem B2069761 : Blo 595291 2069761 := bstep (se 2 (by rfl) ⟨776160, by rfl⟩ : syracuseStep 2069761 = 1552321) B1552321
theorem B1512715 : Blo 595291 1512715 := bstep (se 1 (by rfl) ⟨1134536, by rfl⟩ : syracuseStep 1512715 = 2269073) B2269073
theorem B1381691 : Blo 595291 1381691 := bstep (se 1 (by rfl) ⟨1036268, by rfl⟩ : syracuseStep 1381691 = 2072537) B2072537
theorem B595335 : Blo 595291 595335 := bstep (se 1 (by rfl) ⟨446501, by rfl⟩ : syracuseStep 595335 = 893003) B893003
theorem B595343 : Blo 595291 595343 := bstep (se 1 (by rfl) ⟨446507, by rfl⟩ : syracuseStep 595343 = 893015) B893015
theorem B1512857 : Blo 595291 1512857 := bstep (se 2 (by rfl) ⟨567321, by rfl⟩ : syracuseStep 1512857 = 1134643) B1134643
theorem B595387 : Blo 595291 595387 := bstep (se 1 (by rfl) ⟨446540, by rfl⟩ : syracuseStep 595387 = 893081) B893081
theorem B595463 : Blo 595291 595463 := bstep (se 1 (by rfl) ⟨446597, by rfl⟩ : syracuseStep 595463 = 893195) B893195
theorem B595471 : Blo 595291 595471 := bstep (se 1 (by rfl) ⟨446603, by rfl⟩ : syracuseStep 595471 = 893207) B893207
theorem B595515 : Blo 595291 595515 := bstep (se 1 (by rfl) ⟨446636, by rfl⟩ : syracuseStep 595515 = 893273) B893273
theorem B1513019 : Blo 595291 1513019 := bstep (se 1 (by rfl) ⟨1134764, by rfl⟩ : syracuseStep 1513019 = 2269529) B2269529
theorem B595591 : Blo 595291 595591 := bstep (se 1 (by rfl) ⟨446693, by rfl⟩ : syracuseStep 595591 = 893387) B893387
theorem B595599 : Blo 595291 595599 := bstep (se 1 (by rfl) ⟨446699, by rfl⟩ : syracuseStep 595599 = 893399) B893399
theorem B595643 : Blo 595291 595643 := bstep (se 1 (by rfl) ⟨446732, by rfl⟩ : syracuseStep 595643 = 893465) B893465
theorem B3020489 : Blo 595291 3020489 := bstep (se 2 (by rfl) ⟨1132683, by rfl⟩ : syracuseStep 3020489 = 2265367) B2265367
theorem B2266825 : Blo 595291 2266825 := bstep (se 2 (by rfl) ⟨850059, by rfl⟩ : syracuseStep 2266825 = 1700119) B1700119
theorem B595719 : Blo 595291 595719 := bstep (se 1 (by rfl) ⟨446789, by rfl⟩ : syracuseStep 595719 = 893579) B893579
theorem B595727 : Blo 595291 595727 := bstep (se 1 (by rfl) ⟨446795, by rfl⟩ : syracuseStep 595727 = 893591) B893591
theorem B595771 : Blo 595291 595771 := bstep (se 1 (by rfl) ⟨446828, by rfl⟩ : syracuseStep 595771 = 893657) B893657
theorem B595847 : Blo 595291 595847 := bstep (se 1 (by rfl) ⟨446885, by rfl⟩ : syracuseStep 595847 = 893771) B893771
theorem B595855 : Blo 595291 595855 := bstep (se 1 (by rfl) ⟨446891, by rfl⟩ : syracuseStep 595855 = 893783) B893783
theorem B1513363 : Blo 595291 1513363 := bstep (se 1 (by rfl) ⟨1135022, by rfl⟩ : syracuseStep 1513363 = 2270045) B2270045
theorem B595899 : Blo 595291 595899 := bstep (se 1 (by rfl) ⟨446924, by rfl⟩ : syracuseStep 595899 = 893849) B893849
theorem B595975 : Blo 595291 595975 := bstep (se 1 (by rfl) ⟨446981, by rfl⟩ : syracuseStep 595975 = 893963) B893963
theorem B595983 : Blo 595291 595983 := bstep (se 1 (by rfl) ⟨446987, by rfl⟩ : syracuseStep 595983 = 893975) B893975
theorem B1513505 : Blo 595291 1513505 := bstep (se 2 (by rfl) ⟨567564, by rfl⟩ : syracuseStep 1513505 = 1135129) B1135129
theorem B596027 : Blo 595291 596027 := bstep (se 1 (by rfl) ⟨447020, by rfl⟩ : syracuseStep 596027 = 894041) B894041
theorem B596103 : Blo 595291 596103 := bstep (se 1 (by rfl) ⟨447077, by rfl⟩ : syracuseStep 596103 = 894155) B894155
theorem B596111 : Blo 595291 596111 := bstep (se 1 (by rfl) ⟨447083, by rfl⟩ : syracuseStep 596111 = 894167) B894167
theorem B596155 : Blo 595291 596155 := bstep (se 1 (by rfl) ⟨447116, by rfl⟩ : syracuseStep 596155 = 894233) B894233
theorem B596231 : Blo 595291 596231 := bstep (se 1 (by rfl) ⟨447173, by rfl⟩ : syracuseStep 596231 = 894347) B894347
theorem B596239 : Blo 595291 596239 := bstep (se 1 (by rfl) ⟨447179, by rfl⟩ : syracuseStep 596239 = 894359) B894359
theorem B596283 : Blo 595291 596283 := bstep (se 1 (by rfl) ⟨447212, by rfl⟩ : syracuseStep 596283 = 894425) B894425
theorem B596359 : Blo 595291 596359 := bstep (se 1 (by rfl) ⟨447269, by rfl⟩ : syracuseStep 596359 = 894539) B894539
theorem B596367 : Blo 595291 596367 := bstep (se 1 (by rfl) ⟨447275, by rfl⟩ : syracuseStep 596367 = 894551) B894551
theorem B596411 : Blo 595291 596411 := bstep (se 1 (by rfl) ⟨447308, by rfl⟩ : syracuseStep 596411 = 894617) B894617
theorem B596487 : Blo 595291 596487 := bstep (se 1 (by rfl) ⟨447365, by rfl⟩ : syracuseStep 596487 = 894731) B894731
theorem B596495 : Blo 595291 596495 := bstep (se 1 (by rfl) ⟨447371, by rfl⟩ : syracuseStep 596495 = 894743) B894743
theorem B596539 : Blo 595291 596539 := bstep (se 1 (by rfl) ⟨447404, by rfl⟩ : syracuseStep 596539 = 894809) B894809
theorem B596615 : Blo 595291 596615 := bstep (se 1 (by rfl) ⟨447461, by rfl⟩ : syracuseStep 596615 = 894923) B894923
theorem B596623 : Blo 595291 596623 := bstep (se 1 (by rfl) ⟨447467, by rfl⟩ : syracuseStep 596623 = 894935) B894935
theorem B596667 : Blo 595291 596667 := bstep (se 1 (by rfl) ⟨447500, by rfl⟩ : syracuseStep 596667 = 895001) B895001
theorem B596743 : Blo 595291 596743 := bstep (se 1 (by rfl) ⟨447557, by rfl⟩ : syracuseStep 596743 = 895115) B895115
theorem B596751 : Blo 595291 596751 := bstep (se 1 (by rfl) ⟨447563, by rfl⟩ : syracuseStep 596751 = 895127) B895127
theorem B596795 : Blo 595291 596795 := bstep (se 1 (by rfl) ⟨447596, by rfl⟩ : syracuseStep 596795 = 895193) B895193
theorem B596871 : Blo 595291 596871 := bstep (se 1 (by rfl) ⟨447653, by rfl⟩ : syracuseStep 596871 = 895307) B895307
theorem B596879 : Blo 595291 596879 := bstep (se 1 (by rfl) ⟨447659, by rfl⟩ : syracuseStep 596879 = 895319) B895319
theorem B596923 : Blo 595291 596923 := bstep (se 1 (by rfl) ⟨447692, by rfl⟩ : syracuseStep 596923 = 895385) B895385
theorem B1514497 : Blo 595291 1514497 := bstep (se 2 (by rfl) ⟨567936, by rfl⟩ : syracuseStep 1514497 = 1135873) B1135873
theorem B596999 : Blo 595291 596999 := bstep (se 1 (by rfl) ⟨447749, by rfl⟩ : syracuseStep 596999 = 895499) B895499
theorem B597007 : Blo 595291 597007 := bstep (se 1 (by rfl) ⟨447755, by rfl⟩ : syracuseStep 597007 = 895511) B895511
theorem B597051 : Blo 595291 597051 := bstep (se 1 (by rfl) ⟨447788, by rfl⟩ : syracuseStep 597051 = 895577) B895577
theorem B597127 : Blo 595291 597127 := bstep (se 1 (by rfl) ⟨447845, by rfl⟩ : syracuseStep 597127 = 895691) B895691
theorem B597135 : Blo 595291 597135 := bstep (se 1 (by rfl) ⟨447851, by rfl⟩ : syracuseStep 597135 = 895703) B895703
theorem B597179 : Blo 595291 597179 := bstep (se 1 (by rfl) ⟨447884, by rfl⟩ : syracuseStep 597179 = 895769) B895769
theorem B597255 : Blo 595291 597255 := bstep (se 1 (by rfl) ⟨447941, by rfl⟩ : syracuseStep 597255 = 895883) B895883
theorem B597263 : Blo 595291 597263 := bstep (se 1 (by rfl) ⟨447947, by rfl⟩ : syracuseStep 597263 = 895895) B895895
theorem B597307 : Blo 595291 597307 := bstep (se 1 (by rfl) ⟨447980, by rfl⟩ : syracuseStep 597307 = 895961) B895961
theorem B597383 : Blo 595291 597383 := bstep (se 1 (by rfl) ⟨448037, by rfl⟩ : syracuseStep 597383 = 896075) B896075
theorem B597391 : Blo 595291 597391 := bstep (se 1 (by rfl) ⟨448043, by rfl⟩ : syracuseStep 597391 = 896087) B896087
theorem B957881 : Blo 595291 957881 := bstep (se 2 (by rfl) ⟨359205, by rfl⟩ : syracuseStep 957881 = 718411) B718411
theorem B597435 : Blo 595291 597435 := bstep (se 1 (by rfl) ⟨448076, by rfl⟩ : syracuseStep 597435 = 896153) B896153
theorem B597511 : Blo 595291 597511 := bstep (se 1 (by rfl) ⟨448133, by rfl⟩ : syracuseStep 597511 = 896267) B896267
theorem B597519 : Blo 595291 597519 := bstep (se 1 (by rfl) ⟨448139, by rfl⟩ : syracuseStep 597519 = 896279) B896279
theorem B3055133 : Blo 595291 3055133 := bstep (se 3 (by rfl) ⟨572837, by rfl⟩ : syracuseStep 3055133 = 1145675) B1145675
theorem B597563 : Blo 595291 597563 := bstep (se 1 (by rfl) ⟨448172, by rfl⟩ : syracuseStep 597563 = 896345) B896345
theorem B1515095 : Blo 595291 1515095 := bstep (se 1 (by rfl) ⟨1136321, by rfl⟩ : syracuseStep 1515095 = 2272643) B2272643
theorem B597639 : Blo 595291 597639 := bstep (se 1 (by rfl) ⟨448229, by rfl⟩ : syracuseStep 597639 = 896459) B896459
theorem B597647 : Blo 595291 597647 := bstep (se 1 (by rfl) ⟨448235, by rfl⟩ : syracuseStep 597647 = 896471) B896471
theorem B597691 : Blo 595291 597691 := bstep (se 1 (by rfl) ⟨448268, by rfl⟩ : syracuseStep 597691 = 896537) B896537
theorem B597767 : Blo 595291 597767 := bstep (se 1 (by rfl) ⟨448325, by rfl⟩ : syracuseStep 597767 = 896651) B896651
theorem B597775 : Blo 595291 597775 := bstep (se 1 (by rfl) ⟨448331, by rfl⟩ : syracuseStep 597775 = 896663) B896663
theorem B1515307 : Blo 595291 1515307 := bstep (se 1 (by rfl) ⟨1136480, by rfl⟩ : syracuseStep 1515307 = 2272961) B2272961
theorem B597819 : Blo 595291 597819 := bstep (se 1 (by rfl) ⟨448364, by rfl⟩ : syracuseStep 597819 = 896729) B896729
theorem B2269043 : Blo 595291 2269043 := bstep (se 1 (by rfl) ⟨1701782, by rfl⟩ : syracuseStep 2269043 = 3403565) B3403565
theorem B597895 : Blo 595291 597895 := bstep (se 1 (by rfl) ⟨448421, by rfl⟩ : syracuseStep 597895 = 896843) B896843
theorem B597903 : Blo 595291 597903 := bstep (se 1 (by rfl) ⟨448427, by rfl⟩ : syracuseStep 597903 = 896855) B896855
theorem B1515449 : Blo 595291 1515449 := bstep (se 2 (by rfl) ⟨568293, by rfl⟩ : syracuseStep 1515449 = 1136587) B1136587
theorem B597947 : Blo 595291 597947 := bstep (se 1 (by rfl) ⟨448460, by rfl⟩ : syracuseStep 597947 = 896921) B896921
theorem B598023 : Blo 595291 598023 := bstep (se 1 (by rfl) ⟨448517, by rfl⟩ : syracuseStep 598023 = 897035) B897035
theorem B892943 : Blo 595291 892943 := bstep (se 1 (by rfl) ⟨669707, by rfl⟩ : syracuseStep 892943 = 1339415) B1339415
theorem B598031 : Blo 595291 598031 := bstep (se 1 (by rfl) ⟨448523, by rfl⟩ : syracuseStep 598031 = 897047) B897047
theorem B892985 : Blo 595291 892985 := bstep (se 2 (by rfl) ⟨334869, by rfl⟩ : syracuseStep 892985 = 669739) B669739
theorem B598075 : Blo 595291 598075 := bstep (se 1 (by rfl) ⟨448556, by rfl⟩ : syracuseStep 598075 = 897113) B897113
theorem B893063 : Blo 595291 893063 := bstep (se 1 (by rfl) ⟨669797, by rfl⟩ : syracuseStep 893063 = 1339595) B1339595
theorem B598151 : Blo 595291 598151 := bstep (se 1 (by rfl) ⟨448613, by rfl⟩ : syracuseStep 598151 = 897227) B897227
theorem B598159 : Blo 595291 598159 := bstep (se 1 (by rfl) ⟨448619, by rfl⟩ : syracuseStep 598159 = 897239) B897239
theorem B893099 : Blo 595291 893099 := bstep (se 1 (by rfl) ⟨669824, by rfl⟩ : syracuseStep 893099 = 1339649) B1339649
theorem B598203 : Blo 595291 598203 := bstep (se 1 (by rfl) ⟨448652, by rfl⟩ : syracuseStep 598203 = 897305) B897305
theorem B893129 : Blo 595291 893129 := bstep (se 2 (by rfl) ⟨334923, by rfl⟩ : syracuseStep 893129 = 669847) B669847
theorem B3449033 : Blo 595291 3449033 := bstep (se 2 (by rfl) ⟨1293387, by rfl⟩ : syracuseStep 3449033 = 2586775) B2586775
theorem B598279 : Blo 595291 598279 := bstep (se 1 (by rfl) ⟨448709, by rfl⟩ : syracuseStep 598279 = 897419) B897419
theorem B598287 : Blo 595291 598287 := bstep (se 1 (by rfl) ⟨448715, by rfl⟩ : syracuseStep 598287 = 897431) B897431
theorem B893243 : Blo 595291 893243 := bstep (se 1 (by rfl) ⟨669932, by rfl⟩ : syracuseStep 893243 = 1339865) B1339865
theorem B4530491 : Blo 595291 4530491 := bstep (se 1 (by rfl) ⟨3397868, by rfl⟩ : syracuseStep 4530491 = 6795737) B6795737
theorem B598331 : Blo 595291 598331 := bstep (se 1 (by rfl) ⟨448748, by rfl⟩ : syracuseStep 598331 = 897497) B897497
theorem B893303 : Blo 595291 893303 := bstep (se 1 (by rfl) ⟨669977, by rfl⟩ : syracuseStep 893303 = 1339955) B1339955
theorem B598407 : Blo 595291 598407 := bstep (se 1 (by rfl) ⟨448805, by rfl⟩ : syracuseStep 598407 = 897611) B897611
theorem B893327 : Blo 595291 893327 := bstep (se 1 (by rfl) ⟨669995, by rfl⟩ : syracuseStep 893327 = 1339991) B1339991
theorem B598415 : Blo 595291 598415 := bstep (se 1 (by rfl) ⟨448811, by rfl⟩ : syracuseStep 598415 = 897623) B897623
theorem B893369 : Blo 595291 893369 := bstep (se 2 (by rfl) ⟨335013, by rfl⟩ : syracuseStep 893369 = 670027) B670027
theorem B598459 : Blo 595291 598459 := bstep (se 1 (by rfl) ⟨448844, by rfl⟩ : syracuseStep 598459 = 897689) B897689
theorem B893447 : Blo 595291 893447 := bstep (se 1 (by rfl) ⟨670085, by rfl⟩ : syracuseStep 893447 = 1340171) B1340171
theorem B598535 : Blo 595291 598535 := bstep (se 1 (by rfl) ⟨448901, by rfl⟩ : syracuseStep 598535 = 897803) B897803
theorem B598543 : Blo 595291 598543 := bstep (se 1 (by rfl) ⟨448907, by rfl⟩ : syracuseStep 598543 = 897815) B897815
theorem B893483 : Blo 595291 893483 := bstep (se 1 (by rfl) ⟨670112, by rfl⟩ : syracuseStep 893483 = 1340225) B1340225
theorem B10920491 : Blo 595291 10920491 := bstep (se 1 (by rfl) ⟨8190368, by rfl⟩ : syracuseStep 10920491 = 16380737) B16380737
theorem B2957867 : Blo 595291 2957867 := bstep (se 1 (by rfl) ⟨2218400, by rfl⟩ : syracuseStep 2957867 = 4436801) B4436801
theorem B598587 : Blo 595291 598587 := bstep (se 1 (by rfl) ⟨448940, by rfl⟩ : syracuseStep 598587 = 897881) B897881
theorem B893513 : Blo 595291 893513 := bstep (se 2 (by rfl) ⟨335067, by rfl⟩ : syracuseStep 893513 = 670135) B670135
theorem B598663 : Blo 595291 598663 := bstep (se 1 (by rfl) ⟨448997, by rfl⟩ : syracuseStep 598663 = 897995) B897995
theorem B598671 : Blo 595291 598671 := bstep (se 1 (by rfl) ⟨449003, by rfl⟩ : syracuseStep 598671 = 898007) B898007
theorem B893627 : Blo 595291 893627 := bstep (se 1 (by rfl) ⟨670220, by rfl⟩ : syracuseStep 893627 = 1340441) B1340441
theorem B598715 : Blo 595291 598715 := bstep (se 1 (by rfl) ⟨449036, by rfl⟩ : syracuseStep 598715 = 898073) B898073
theorem B893687 : Blo 595291 893687 := bstep (se 1 (by rfl) ⟨670265, by rfl⟩ : syracuseStep 893687 = 1340531) B1340531
theorem B598791 : Blo 595291 598791 := bstep (se 1 (by rfl) ⟨449093, by rfl⟩ : syracuseStep 598791 = 898187) B898187
theorem B893711 : Blo 595291 893711 := bstep (se 1 (by rfl) ⟨670283, by rfl⟩ : syracuseStep 893711 = 1340567) B1340567
theorem B598799 : Blo 595291 598799 := bstep (se 1 (by rfl) ⟨449099, by rfl⟩ : syracuseStep 598799 = 898199) B898199
theorem B893753 : Blo 595291 893753 := bstep (se 2 (by rfl) ⟨335157, by rfl⟩ : syracuseStep 893753 = 670315) B670315
theorem B598843 : Blo 595291 598843 := bstep (se 1 (by rfl) ⟨449132, by rfl⟩ : syracuseStep 598843 = 898265) B898265
theorem B893831 : Blo 595291 893831 := bstep (se 1 (by rfl) ⟨670373, by rfl⟩ : syracuseStep 893831 = 1340747) B1340747
theorem B598919 : Blo 595291 598919 := bstep (se 1 (by rfl) ⟨449189, by rfl⟩ : syracuseStep 598919 = 898379) B898379
theorem B598927 : Blo 595291 598927 := bstep (se 1 (by rfl) ⟨449195, by rfl⟩ : syracuseStep 598927 = 898391) B898391
theorem B1516441 : Blo 595291 1516441 := bstep (se 2 (by rfl) ⟨568665, by rfl⟩ : syracuseStep 1516441 = 1137331) B1137331
theorem B893867 : Blo 595291 893867 := bstep (se 1 (by rfl) ⟨670400, by rfl⟩ : syracuseStep 893867 = 1340801) B1340801
theorem B598971 : Blo 595291 598971 := bstep (se 1 (by rfl) ⟨449228, by rfl⟩ : syracuseStep 598971 = 898457) B898457
theorem B893897 : Blo 595291 893897 := bstep (se 2 (by rfl) ⟨335211, by rfl⟩ : syracuseStep 893897 = 670423) B670423
theorem B599047 : Blo 595291 599047 := bstep (se 1 (by rfl) ⟨449285, by rfl⟩ : syracuseStep 599047 = 898571) B898571
theorem B599055 : Blo 595291 599055 := bstep (se 1 (by rfl) ⟨449291, by rfl⟩ : syracuseStep 599055 = 898583) B898583
theorem B894011 : Blo 595291 894011 := bstep (se 1 (by rfl) ⟨670508, by rfl⟩ : syracuseStep 894011 = 1341017) B1341017
theorem B599099 : Blo 595291 599099 := bstep (se 1 (by rfl) ⟨449324, by rfl⟩ : syracuseStep 599099 = 898649) B898649
theorem B1516603 : Blo 595291 1516603 := bstep (se 1 (by rfl) ⟨1137452, by rfl⟩ : syracuseStep 1516603 = 2274905) B2274905
theorem B1025083 : Blo 595291 1025083 := bstep (se 1 (by rfl) ⟨768812, by rfl⟩ : syracuseStep 1025083 = 1537625) B1537625
theorem B894071 : Blo 595291 894071 := bstep (se 1 (by rfl) ⟨670553, by rfl⟩ : syracuseStep 894071 = 1341107) B1341107
theorem B599175 : Blo 595291 599175 := bstep (se 1 (by rfl) ⟨449381, by rfl⟩ : syracuseStep 599175 = 898763) B898763
theorem B894095 : Blo 595291 894095 := bstep (se 1 (by rfl) ⟨670571, by rfl⟩ : syracuseStep 894095 = 1341143) B1341143
theorem B599183 : Blo 595291 599183 := bstep (se 1 (by rfl) ⟨449387, by rfl⟩ : syracuseStep 599183 = 898775) B898775
theorem B894137 : Blo 595291 894137 := bstep (se 2 (by rfl) ⟨335301, by rfl⟩ : syracuseStep 894137 = 670603) B670603
theorem B599227 : Blo 595291 599227 := bstep (se 1 (by rfl) ⟨449420, by rfl⟩ : syracuseStep 599227 = 898841) B898841
theorem B1516745 : Blo 595291 1516745 := bstep (se 2 (by rfl) ⟨568779, by rfl⟩ : syracuseStep 1516745 = 1137559) B1137559
theorem B894215 : Blo 595291 894215 := bstep (se 1 (by rfl) ⟨670661, by rfl⟩ : syracuseStep 894215 = 1341323) B1341323
theorem B894251 : Blo 595291 894251 := bstep (se 1 (by rfl) ⟨670688, by rfl⟩ : syracuseStep 894251 = 1341377) B1341377
theorem B894281 : Blo 595291 894281 := bstep (se 2 (by rfl) ⟨335355, by rfl⟩ : syracuseStep 894281 = 670711) B670711
theorem B894395 : Blo 595291 894395 := bstep (se 1 (by rfl) ⟨670796, by rfl⟩ : syracuseStep 894395 = 1341593) B1341593
theorem B894455 : Blo 595291 894455 := bstep (se 1 (by rfl) ⟨670841, by rfl⟩ : syracuseStep 894455 = 1341683) B1341683
theorem B697871 : Blo 595291 697871 := bstep (se 1 (by rfl) ⟨523403, by rfl⟩ : syracuseStep 697871 = 1046807) B1046807
theorem B894479 : Blo 595291 894479 := bstep (se 1 (by rfl) ⟨670859, by rfl⟩ : syracuseStep 894479 = 1341719) B1341719
theorem B894521 : Blo 595291 894521 := bstep (se 2 (by rfl) ⟨335445, by rfl⟩ : syracuseStep 894521 = 670891) B670891
theorem B894599 : Blo 595291 894599 := bstep (se 1 (by rfl) ⟨670949, by rfl⟩ : syracuseStep 894599 = 1341899) B1341899
theorem B894635 : Blo 595291 894635 := bstep (se 1 (by rfl) ⟨670976, by rfl⟩ : syracuseStep 894635 = 1341953) B1341953
theorem B894665 : Blo 595291 894665 := bstep (se 2 (by rfl) ⟨335499, by rfl⟩ : syracuseStep 894665 = 670999) B670999
theorem B7251727 : Blo 595291 7251727 := bstep (se 1 (by rfl) ⟨5438795, by rfl⟩ : syracuseStep 7251727 = 10877591) B10877591
theorem B894779 : Blo 595291 894779 := bstep (se 1 (by rfl) ⟨671084, by rfl⟩ : syracuseStep 894779 = 1342169) B1342169
theorem B894839 : Blo 595291 894839 := bstep (se 1 (by rfl) ⟨671129, by rfl⟩ : syracuseStep 894839 = 1342259) B1342259
theorem B894863 : Blo 595291 894863 := bstep (se 1 (by rfl) ⟨671147, by rfl⟩ : syracuseStep 894863 = 1342295) B1342295
theorem B894905 : Blo 595291 894905 := bstep (se 2 (by rfl) ⟨335589, by rfl⟩ : syracuseStep 894905 = 671179) B671179
theorem B2271185 : Blo 595291 2271185 := bstep (se 2 (by rfl) ⟨851694, by rfl⟩ : syracuseStep 2271185 = 1703389) B1703389
theorem B894983 : Blo 595291 894983 := bstep (se 1 (by rfl) ⟨671237, by rfl⟩ : syracuseStep 894983 = 1342475) B1342475
theorem B895019 : Blo 595291 895019 := bstep (se 1 (by rfl) ⟨671264, by rfl⟩ : syracuseStep 895019 = 1342529) B1342529
theorem B895049 : Blo 595291 895049 := bstep (se 2 (by rfl) ⟨335643, by rfl⟩ : syracuseStep 895049 = 671287) B671287
theorem B895163 : Blo 595291 895163 := bstep (se 1 (by rfl) ⟨671372, by rfl⟩ : syracuseStep 895163 = 1342745) B1342745
theorem B895223 : Blo 595291 895223 := bstep (se 1 (by rfl) ⟨671417, by rfl⟩ : syracuseStep 895223 = 1342835) B1342835
theorem B895247 : Blo 595291 895247 := bstep (se 1 (by rfl) ⟨671435, by rfl⟩ : syracuseStep 895247 = 1342871) B1342871
theorem B2271503 : Blo 595291 2271503 := bstep (se 1 (by rfl) ⟨1703627, by rfl⟩ : syracuseStep 2271503 = 3407255) B3407255
theorem B895289 : Blo 595291 895289 := bstep (se 2 (by rfl) ⟨335733, by rfl⟩ : syracuseStep 895289 = 671467) B671467
theorem B895367 : Blo 595291 895367 := bstep (se 1 (by rfl) ⟨671525, by rfl⟩ : syracuseStep 895367 = 1343051) B1343051
theorem B895403 : Blo 595291 895403 := bstep (se 1 (by rfl) ⟨671552, by rfl⟩ : syracuseStep 895403 = 1343105) B1343105
theorem B895433 : Blo 595291 895433 := bstep (se 2 (by rfl) ⟨335787, by rfl⟩ : syracuseStep 895433 = 671575) B671575
theorem B15313373 : Blo 595291 15313373 := bstep (se 3 (by rfl) ⟨2871257, by rfl⟩ : syracuseStep 15313373 = 5742515) B5742515
theorem B895547 : Blo 595291 895547 := bstep (se 1 (by rfl) ⟨671660, by rfl⟩ : syracuseStep 895547 = 1343321) B1343321
theorem B895607 : Blo 595291 895607 := bstep (se 1 (by rfl) ⟨671705, by rfl⟩ : syracuseStep 895607 = 1343411) B1343411
theorem B895631 : Blo 595291 895631 := bstep (se 1 (by rfl) ⟨671723, by rfl⟩ : syracuseStep 895631 = 1343447) B1343447
theorem B895673 : Blo 595291 895673 := bstep (se 2 (by rfl) ⟨335877, by rfl⟩ : syracuseStep 895673 = 671755) B671755
theorem B895751 : Blo 595291 895751 := bstep (se 1 (by rfl) ⟨671813, by rfl⟩ : syracuseStep 895751 = 1343627) B1343627
theorem B895787 : Blo 595291 895787 := bstep (se 1 (by rfl) ⟨671840, by rfl⟩ : syracuseStep 895787 = 1343681) B1343681
theorem B895817 : Blo 595291 895817 := bstep (se 2 (by rfl) ⟨335931, by rfl⟩ : syracuseStep 895817 = 671863) B671863
theorem B9677657 : Blo 595291 9677657 := bstep (se 2 (by rfl) ⟨3629121, by rfl⟩ : syracuseStep 9677657 = 7258243) B7258243
theorem B2010041 : Blo 595291 2010041 := bstep (se 2 (by rfl) ⟨753765, by rfl⟩ : syracuseStep 2010041 = 1507531) B1507531
theorem B895931 : Blo 595291 895931 := bstep (se 1 (by rfl) ⟨671948, by rfl⟩ : syracuseStep 895931 = 1343897) B1343897
theorem B895991 : Blo 595291 895991 := bstep (se 1 (by rfl) ⟨671993, by rfl⟩ : syracuseStep 895991 = 1343987) B1343987
theorem B896015 : Blo 595291 896015 := bstep (se 1 (by rfl) ⟨672011, by rfl⟩ : syracuseStep 896015 = 1344023) B1344023
theorem B896057 : Blo 595291 896057 := bstep (se 2 (by rfl) ⟨336021, by rfl⟩ : syracuseStep 896057 = 672043) B672043
theorem B896135 : Blo 595291 896135 := bstep (se 1 (by rfl) ⟨672101, by rfl⟩ : syracuseStep 896135 = 1344203) B1344203
theorem B896171 : Blo 595291 896171 := bstep (se 1 (by rfl) ⟨672128, by rfl⟩ : syracuseStep 896171 = 1344257) B1344257
theorem B896201 : Blo 595291 896201 := bstep (se 2 (by rfl) ⟨336075, by rfl⟩ : syracuseStep 896201 = 672151) B672151
theorem B2731279 : Blo 595291 2731279 := bstep (se 1 (by rfl) ⟨2048459, by rfl⟩ : syracuseStep 2731279 = 4096919) B4096919
theorem B896315 : Blo 595291 896315 := bstep (se 1 (by rfl) ⟨672236, by rfl⟩ : syracuseStep 896315 = 1344473) B1344473
theorem B896375 : Blo 595291 896375 := bstep (se 1 (by rfl) ⟨672281, by rfl⟩ : syracuseStep 896375 = 1344563) B1344563
theorem B896399 : Blo 595291 896399 := bstep (se 1 (by rfl) ⟨672299, by rfl⟩ : syracuseStep 896399 = 1344599) B1344599
theorem B3026321 : Blo 595291 3026321 := bstep (se 2 (by rfl) ⟨1134870, by rfl⟩ : syracuseStep 3026321 = 2269741) B2269741
theorem B896441 : Blo 595291 896441 := bstep (se 2 (by rfl) ⟨336165, by rfl⟩ : syracuseStep 896441 = 672331) B672331
theorem B896519 : Blo 595291 896519 := bstep (se 1 (by rfl) ⟨672389, by rfl⟩ : syracuseStep 896519 = 1344779) B1344779
theorem B2010635 : Blo 595291 2010635 := bstep (se 1 (by rfl) ⟨1507976, by rfl⟩ : syracuseStep 2010635 = 3015953) B3015953
theorem B896555 : Blo 595291 896555 := bstep (se 1 (by rfl) ⟨672416, by rfl⟩ : syracuseStep 896555 = 1344833) B1344833
theorem B896585 : Blo 595291 896585 := bstep (se 2 (by rfl) ⟨336219, by rfl⟩ : syracuseStep 896585 = 672439) B672439
theorem B2010743 : Blo 595291 2010743 := bstep (se 1 (by rfl) ⟨1508057, by rfl⟩ : syracuseStep 2010743 = 3016115) B3016115
theorem B896699 : Blo 595291 896699 := bstep (se 1 (by rfl) ⟨672524, by rfl⟩ : syracuseStep 896699 = 1345049) B1345049
theorem B896759 : Blo 595291 896759 := bstep (se 1 (by rfl) ⟨672569, by rfl⟩ : syracuseStep 896759 = 1345139) B1345139
theorem B896783 : Blo 595291 896783 := bstep (se 1 (by rfl) ⟨672587, by rfl⟩ : syracuseStep 896783 = 1345175) B1345175
theorem B896825 : Blo 595291 896825 := bstep (se 2 (by rfl) ⟨336309, by rfl⟩ : syracuseStep 896825 = 672619) B672619
theorem B896903 : Blo 595291 896903 := bstep (se 1 (by rfl) ⟨672677, by rfl⟩ : syracuseStep 896903 = 1345355) B1345355
theorem B896939 : Blo 595291 896939 := bstep (se 1 (by rfl) ⟨672704, by rfl⟩ : syracuseStep 896939 = 1345409) B1345409
theorem B896969 : Blo 595291 896969 := bstep (se 2 (by rfl) ⟨336363, by rfl⟩ : syracuseStep 896969 = 672727) B672727
theorem B8171543 : Blo 595291 8171543 := bstep (se 1 (by rfl) ⟨6128657, by rfl⟩ : syracuseStep 8171543 = 12257315) B12257315
theorem B897083 : Blo 595291 897083 := bstep (se 1 (by rfl) ⟨672812, by rfl⟩ : syracuseStep 897083 = 1345625) B1345625
theorem B3321917 : Blo 595291 3321917 := bstep (se 3 (by rfl) ⟨622859, by rfl⟩ : syracuseStep 3321917 = 1245719) B1245719
theorem B897143 : Blo 595291 897143 := bstep (se 1 (by rfl) ⟨672857, by rfl⟩ : syracuseStep 897143 = 1345715) B1345715
theorem B897167 : Blo 595291 897167 := bstep (se 1 (by rfl) ⟨672875, by rfl⟩ : syracuseStep 897167 = 1345751) B1345751
theorem B897209 : Blo 595291 897209 := bstep (se 2 (by rfl) ⟨336453, by rfl⟩ : syracuseStep 897209 = 672907) B672907
theorem B2011337 : Blo 595291 2011337 := bstep (se 2 (by rfl) ⟨754251, by rfl⟩ : syracuseStep 2011337 = 1508503) B1508503
theorem B1913033 : Blo 595291 1913033 := bstep (se 2 (by rfl) ⟨717387, by rfl⟩ : syracuseStep 1913033 = 1434775) B1434775
theorem B897287 : Blo 595291 897287 := bstep (se 1 (by rfl) ⟨672965, by rfl⟩ : syracuseStep 897287 = 1345931) B1345931
theorem B897323 : Blo 595291 897323 := bstep (se 1 (by rfl) ⟨672992, by rfl⟩ : syracuseStep 897323 = 1345985) B1345985
theorem B1913147 : Blo 595291 1913147 := bstep (se 1 (by rfl) ⟨1434860, by rfl⟩ : syracuseStep 1913147 = 2869721) B2869721
theorem B897353 : Blo 595291 897353 := bstep (se 2 (by rfl) ⟨336507, by rfl⟩ : syracuseStep 897353 = 673015) B673015
theorem B897467 : Blo 595291 897467 := bstep (se 1 (by rfl) ⟨673100, by rfl⟩ : syracuseStep 897467 = 1346201) B1346201
theorem B897527 : Blo 595291 897527 := bstep (se 1 (by rfl) ⟨673145, by rfl⟩ : syracuseStep 897527 = 1346291) B1346291
theorem B897551 : Blo 595291 897551 := bstep (se 1 (by rfl) ⟨673163, by rfl⟩ : syracuseStep 897551 = 1346327) B1346327
theorem B897593 : Blo 595291 897593 := bstep (se 2 (by rfl) ⟨336597, by rfl⟩ : syracuseStep 897593 = 673195) B673195
theorem B897671 : Blo 595291 897671 := bstep (se 1 (by rfl) ⟨673253, by rfl⟩ : syracuseStep 897671 = 1346507) B1346507
theorem B897707 : Blo 595291 897707 := bstep (se 1 (by rfl) ⟨673280, by rfl⟩ : syracuseStep 897707 = 1346561) B1346561
theorem B897737 : Blo 595291 897737 := bstep (se 2 (by rfl) ⟨336651, by rfl⟩ : syracuseStep 897737 = 673303) B673303
theorem B1618717 : Blo 595291 1618717 := bstep (se 3 (by rfl) ⟨303509, by rfl⟩ : syracuseStep 1618717 = 607019) B607019
theorem B897851 : Blo 595291 897851 := bstep (se 1 (by rfl) ⟨673388, by rfl⟩ : syracuseStep 897851 = 1346777) B1346777
theorem B897911 : Blo 595291 897911 := bstep (se 1 (by rfl) ⟨673433, by rfl⟩ : syracuseStep 897911 = 1346867) B1346867
theorem B2012039 : Blo 595291 2012039 := bstep (se 1 (by rfl) ⟨1509029, by rfl⟩ : syracuseStep 2012039 = 3018059) B3018059
theorem B897935 : Blo 595291 897935 := bstep (se 1 (by rfl) ⟨673451, by rfl⟩ : syracuseStep 897935 = 1346903) B1346903
theorem B897977 : Blo 595291 897977 := bstep (se 2 (by rfl) ⟨336741, by rfl⟩ : syracuseStep 897977 = 673483) B673483
theorem B898055 : Blo 595291 898055 := bstep (se 1 (by rfl) ⟨673541, by rfl⟩ : syracuseStep 898055 = 1347083) B1347083
theorem B898091 : Blo 595291 898091 := bstep (se 1 (by rfl) ⟨673568, by rfl⟩ : syracuseStep 898091 = 1347137) B1347137
theorem B898121 : Blo 595291 898121 := bstep (se 2 (by rfl) ⟨336795, by rfl⟩ : syracuseStep 898121 = 673591) B673591
theorem B898235 : Blo 595291 898235 := bstep (se 1 (by rfl) ⟨673676, by rfl⟩ : syracuseStep 898235 = 1347353) B1347353
theorem B898295 : Blo 595291 898295 := bstep (se 1 (by rfl) ⟨673721, by rfl⟩ : syracuseStep 898295 = 1347443) B1347443
theorem B2012417 : Blo 595291 2012417 := bstep (se 2 (by rfl) ⟨754656, by rfl⟩ : syracuseStep 2012417 = 1509313) B1509313
theorem B898319 : Blo 595291 898319 := bstep (se 1 (by rfl) ⟨673739, by rfl⟩ : syracuseStep 898319 = 1347479) B1347479
theorem B898361 : Blo 595291 898361 := bstep (se 2 (by rfl) ⟨336885, by rfl⟩ : syracuseStep 898361 = 673771) B673771
theorem B603451 : Blo 595291 603451 := bstep (se 1 (by rfl) ⟨452588, by rfl⟩ : syracuseStep 603451 = 905177) B905177
theorem B898439 : Blo 595291 898439 := bstep (se 1 (by rfl) ⟨673829, by rfl⟩ : syracuseStep 898439 = 1347659) B1347659
theorem B898475 : Blo 595291 898475 := bstep (se 1 (by rfl) ⟨673856, by rfl⟩ : syracuseStep 898475 = 1347713) B1347713
theorem B898505 : Blo 595291 898505 := bstep (se 2 (by rfl) ⟨336939, by rfl⟩ : syracuseStep 898505 = 673879) B673879
theorem B3028427 : Blo 595291 3028427 := bstep (se 1 (by rfl) ⟨2271320, by rfl⟩ : syracuseStep 3028427 = 4542641) B4542641
theorem B4535837 : Blo 595291 4535837 := bstep (se 3 (by rfl) ⟨850469, by rfl⟩ : syracuseStep 4535837 = 1700939) B1700939
theorem B898619 : Blo 595291 898619 := bstep (se 1 (by rfl) ⟨673964, by rfl⟩ : syracuseStep 898619 = 1347929) B1347929
theorem B898679 : Blo 595291 898679 := bstep (se 1 (by rfl) ⟨674009, by rfl⟩ : syracuseStep 898679 = 1348019) B1348019
theorem B898703 : Blo 595291 898703 := bstep (se 1 (by rfl) ⟨674027, by rfl⟩ : syracuseStep 898703 = 1348055) B1348055
theorem B898745 : Blo 595291 898745 := bstep (se 2 (by rfl) ⟨337029, by rfl⟩ : syracuseStep 898745 = 674059) B674059
theorem B2275073 : Blo 595291 2275073 := bstep (se 2 (by rfl) ⟨853152, by rfl⟩ : syracuseStep 2275073 = 1706305) B1706305
theorem B898823 : Blo 595291 898823 := bstep (se 1 (by rfl) ⟨674117, by rfl⟩ : syracuseStep 898823 = 1348235) B1348235
theorem B3028751 : Blo 595291 3028751 := bstep (se 1 (by rfl) ⟨2271563, by rfl⟩ : syracuseStep 3028751 = 4543127) B4543127
theorem B2275087 : Blo 595291 2275087 := bstep (se 1 (by rfl) ⟨1706315, by rfl⟩ : syracuseStep 2275087 = 3412631) B3412631
theorem B5748515 : Blo 595291 5748515 := bstep (se 1 (by rfl) ⟨4311386, by rfl⟩ : syracuseStep 5748515 = 8622773) B8622773
theorem B898859 : Blo 595291 898859 := bstep (se 1 (by rfl) ⟨674144, by rfl⟩ : syracuseStep 898859 = 1348289) B1348289
theorem B898889 : Blo 595291 898889 := bstep (se 2 (by rfl) ⟨337083, by rfl⟩ : syracuseStep 898889 = 674167) B674167
theorem B669703 : Blo 595291 669703 := bstep (se 1 (by rfl) ⟨502277, by rfl⟩ : syracuseStep 669703 = 1004555) B1004555
theorem B5093387 : Blo 595291 5093387 := bstep (se 1 (by rfl) ⟨3820040, by rfl⟩ : syracuseStep 5093387 = 7640081) B7640081
theorem B2013227 : Blo 595291 2013227 := bstep (se 1 (by rfl) ⟨1509920, by rfl⟩ : syracuseStep 2013227 = 3019841) B3019841
theorem B1914941 : Blo 595291 1914941 := bstep (se 3 (by rfl) ⟨359051, by rfl⟩ : syracuseStep 1914941 = 718103) B718103
theorem B669883 : Blo 595291 669883 := bstep (se 1 (by rfl) ⟨502412, by rfl⟩ : syracuseStep 669883 = 1004825) B1004825
theorem B6895817 : Blo 595291 6895817 := bstep (se 2 (by rfl) ⟨2585931, by rfl⟩ : syracuseStep 6895817 = 5171863) B5171863
theorem B6895853 : Blo 595291 6895853 := bstep (se 3 (by rfl) ⟨1292972, by rfl⟩ : syracuseStep 6895853 = 2585945) B2585945
theorem B12925169 : Blo 595291 12925169 := bstep (se 2 (by rfl) ⟨4846938, by rfl⟩ : syracuseStep 12925169 = 9693877) B9693877
theorem B1915289 : Blo 595291 1915289 := bstep (se 2 (by rfl) ⟨718233, by rfl⟩ : syracuseStep 1915289 = 1436467) B1436467
theorem B1817117 : Blo 595291 1817117 := bstep (se 3 (by rfl) ⟨340709, by rfl⟩ : syracuseStep 1817117 = 681419) B681419
theorem B6437495 : Blo 595291 6437495 := bstep (se 1 (by rfl) ⟨4828121, by rfl⟩ : syracuseStep 6437495 = 9656243) B9656243
theorem B670351 : Blo 595291 670351 := bstep (se 1 (by rfl) ⟨502763, by rfl⟩ : syracuseStep 670351 = 1005527) B1005527
theorem B1915915 : Blo 595291 1915915 := bstep (se 1 (by rfl) ⟨1436936, by rfl⟩ : syracuseStep 1915915 = 2873873) B2873873
theorem B605243 : Blo 595291 605243 := bstep (se 1 (by rfl) ⟨453932, by rfl⟩ : syracuseStep 605243 = 907865) B907865
theorem B670855 : Blo 595291 670855 := bstep (se 1 (by rfl) ⟨503141, by rfl⟩ : syracuseStep 670855 = 1006283) B1006283
theorem B3030209 : Blo 595291 3030209 := bstep (se 2 (by rfl) ⟨1136328, by rfl⟩ : syracuseStep 3030209 = 2272657) B2272657
theorem B671035 : Blo 595291 671035 := bstep (se 1 (by rfl) ⟨503276, by rfl⟩ : syracuseStep 671035 = 1006553) B1006553
theorem B2014523 : Blo 595291 2014523 := bstep (se 1 (by rfl) ⟨1510892, by rfl⟩ : syracuseStep 2014523 = 3021785) B3021785
theorem B1359289 : Blo 595291 1359289 := bstep (se 2 (by rfl) ⟨509733, by rfl⟩ : syracuseStep 1359289 = 1019467) B1019467
theorem B671503 : Blo 595291 671503 := bstep (se 1 (by rfl) ⟨503627, by rfl⟩ : syracuseStep 671503 = 1007255) B1007255
theorem B2015009 : Blo 595291 2015009 := bstep (se 2 (by rfl) ⟨755628, by rfl⟩ : syracuseStep 2015009 = 1511257) B1511257
theorem B1130375 : Blo 595291 1130375 := bstep (se 1 (by rfl) ⟨847781, by rfl⟩ : syracuseStep 1130375 = 1695563) B1695563
theorem B2867089 : Blo 595291 2867089 := bstep (se 2 (by rfl) ⟨1075158, by rfl⟩ : syracuseStep 2867089 = 2150317) B2150317
theorem B2867147 : Blo 595291 2867147 := bstep (se 1 (by rfl) ⟨2150360, by rfl⟩ : syracuseStep 2867147 = 4300721) B4300721
theorem B11452589 : Blo 595291 11452589 := bstep (se 3 (by rfl) ⟨2147360, by rfl⟩ : syracuseStep 11452589 = 4294721) B4294721
theorem B672007 : Blo 595291 672007 := bstep (se 1 (by rfl) ⟨504005, by rfl⟩ : syracuseStep 672007 = 1008011) B1008011
theorem B9814289 : Blo 595291 9814289 := bstep (se 2 (by rfl) ⟨3680358, by rfl⟩ : syracuseStep 9814289 = 7360717) B7360717
theorem B2015603 : Blo 595291 2015603 := bstep (se 1 (by rfl) ⟨1511702, by rfl⟩ : syracuseStep 2015603 = 3023405) B3023405
theorem B672187 : Blo 595291 672187 := bstep (se 1 (by rfl) ⟨504140, by rfl⟩ : syracuseStep 672187 = 1008281) B1008281
theorem B3031505 : Blo 595291 3031505 := bstep (se 2 (by rfl) ⟨1136814, by rfl⟩ : syracuseStep 3031505 = 2273629) B2273629
theorem B2867723 : Blo 595291 2867723 := bstep (se 1 (by rfl) ⟨2150792, by rfl⟩ : syracuseStep 2867723 = 4301585) B4301585
theorem B1720919 : Blo 595291 1720919 := bstep (se 1 (by rfl) ⟨1290689, by rfl⟩ : syracuseStep 1720919 = 2581379) B2581379
theorem B1458803 : Blo 595291 1458803 := bstep (se 1 (by rfl) ⟨1094102, by rfl⟩ : syracuseStep 1458803 = 2188205) B2188205
theorem B15287129 : Blo 595291 15287129 := bstep (se 2 (by rfl) ⟨5732673, by rfl⟩ : syracuseStep 15287129 = 11465347) B11465347
theorem B3392401 : Blo 595291 3392401 := bstep (se 2 (by rfl) ⟨1272150, by rfl⟩ : syracuseStep 3392401 = 2544301) B2544301
theorem B672655 : Blo 595291 672655 := bstep (se 1 (by rfl) ⟨504491, by rfl⟩ : syracuseStep 672655 = 1008983) B1008983
theorem B2147447 : Blo 595291 2147447 := bstep (se 1 (by rfl) ⟨1610585, by rfl⟩ : syracuseStep 2147447 = 3221171) B3221171
theorem B3622117 : Blo 595291 3622117 := bstep (se 4 (by rfl) ⟨339573, by rfl⟩ : syracuseStep 3622117 = 679147) B679147
theorem B3687713 : Blo 595291 3687713 := bstep (se 2 (by rfl) ⟨1382892, by rfl⟩ : syracuseStep 3687713 = 2765785) B2765785
theorem B3622259 : Blo 595291 3622259 := bstep (se 1 (by rfl) ⟨2716694, by rfl⟩ : syracuseStep 3622259 = 5433389) B5433389
theorem B673159 : Blo 595291 673159 := bstep (se 1 (by rfl) ⟨504869, by rfl⟩ : syracuseStep 673159 = 1009739) B1009739
theorem B1033771 : Blo 595291 1033771 := bstep (se 1 (by rfl) ⟨775328, by rfl⟩ : syracuseStep 1033771 = 1550657) B1550657
theorem B673339 : Blo 595291 673339 := bstep (se 1 (by rfl) ⟨505004, by rfl⟩ : syracuseStep 673339 = 1010009) B1010009
theorem B4540211 : Blo 595291 4540211 := bstep (se 1 (by rfl) ⟨3405158, by rfl⟩ : syracuseStep 4540211 = 6810317) B6810317
theorem B1296263 : Blo 595291 1296263 := bstep (se 1 (by rfl) ⟨972197, by rfl⟩ : syracuseStep 1296263 = 1944395) B1944395
theorem B673807 : Blo 595291 673807 := bstep (se 1 (by rfl) ⟨505355, by rfl⟩ : syracuseStep 673807 = 1010711) B1010711
theorem B16566295 : Blo 595291 16566295 := bstep (se 1 (by rfl) ⟨12424721, by rfl⟩ : syracuseStep 16566295 = 24849443) B24849443
theorem B3819581 : Blo 595291 3819581 := bstep (se 3 (by rfl) ⟨716171, by rfl⟩ : syracuseStep 3819581 = 1432343) B1432343
theorem B4835389 : Blo 595291 4835389 := bstep (se 3 (by rfl) ⟨906635, by rfl⟩ : syracuseStep 4835389 = 1813271) B1813271
theorem B5097761 : Blo 595291 5097761 := bstep (se 2 (by rfl) ⟨1911660, by rfl⟩ : syracuseStep 5097761 = 3823321) B3823321
theorem B1132859 : Blo 595291 1132859 := bstep (se 1 (by rfl) ⟨849644, by rfl⟩ : syracuseStep 1132859 = 1699289) B1699289
theorem B3033611 : Blo 595291 3033611 := bstep (se 1 (by rfl) ⟨2275208, by rfl⟩ : syracuseStep 3033611 = 4550417) B4550417
theorem B3033773 : Blo 595291 3033773 := bstep (se 3 (by rfl) ⟨568832, by rfl⟩ : syracuseStep 3033773 = 1137665) B1137665
theorem B805639 : Blo 595291 805639 := bstep (se 1 (by rfl) ⟨604229, by rfl⟩ : syracuseStep 805639 = 1208459) B1208459
theorem B1133345 : Blo 595291 1133345 := bstep (se 2 (by rfl) ⟨425004, by rfl⟩ : syracuseStep 1133345 = 850009) B850009
theorem B2018195 : Blo 595291 2018195 := bstep (se 1 (by rfl) ⟨1513646, by rfl⟩ : syracuseStep 2018195 = 3027293) B3027293
theorem B5753861 : Blo 595291 5753861 := bstep (se 4 (by rfl) ⟨539424, by rfl⟩ : syracuseStep 5753861 = 1078849) B1078849
theorem B3394817 : Blo 595291 3394817 := bstep (se 2 (by rfl) ⟨1273056, by rfl⟩ : syracuseStep 3394817 = 2546113) B2546113
theorem B5459345 : Blo 595291 5459345 := bstep (se 2 (by rfl) ⟨2047254, by rfl⟩ : syracuseStep 5459345 = 4094509) B4094509
theorem B1822409 : Blo 595291 1822409 := bstep (se 2 (by rfl) ⟨683403, by rfl⟩ : syracuseStep 1822409 = 1366807) B1366807
theorem B99438515 : Blo 595291 99438515 := bstep (se 1 (by rfl) ⟨74578886, by rfl⟩ : syracuseStep 99438515 = 149157773) B149157773
theorem B3821579 : Blo 595291 3821579 := bstep (se 1 (by rfl) ⟨2866184, by rfl⟩ : syracuseStep 3821579 = 5732369) B5732369
theorem B2019599 : Blo 595291 2019599 := bstep (se 1 (by rfl) ⟨1514699, by rfl⟩ : syracuseStep 2019599 = 3029399) B3029399
theorem B2019869 : Blo 595291 2019869 := bstep (se 3 (by rfl) ⟨378725, by rfl⟩ : syracuseStep 2019869 = 757451) B757451
theorem B1135289 : Blo 595291 1135289 := bstep (se 2 (by rfl) ⟨425733, by rfl⟩ : syracuseStep 1135289 = 851467) B851467
theorem B3068761 : Blo 595291 3068761 := bstep (se 2 (by rfl) ⟨1150785, by rfl⟩ : syracuseStep 3068761 = 2301571) B2301571
theorem B6804485 : Blo 595291 6804485 := bstep (se 4 (by rfl) ⟨637920, by rfl⟩ : syracuseStep 6804485 = 1275841) B1275841
theorem B8180747 : Blo 595291 8180747 := bstep (se 1 (by rfl) ⟨6135560, by rfl⟩ : syracuseStep 8180747 = 12271121) B12271121
theorem B2151485 : Blo 595291 2151485 := bstep (se 3 (by rfl) ⟨403403, by rfl⟩ : syracuseStep 2151485 = 806807) B806807
theorem B1004663 : Blo 595291 1004663 := bstep (se 1 (by rfl) ⟨753497, by rfl⟩ : syracuseStep 1004663 = 1506995) B1506995
theorem B3397049 : Blo 595291 3397049 := bstep (se 2 (by rfl) ⟨1273893, by rfl⟩ : syracuseStep 3397049 = 2547787) B2547787
theorem B1005115 : Blo 595291 1005115 := bstep (se 1 (by rfl) ⟨753836, by rfl⟩ : syracuseStep 1005115 = 1507673) B1507673
theorem B2152003 : Blo 595291 2152003 := bstep (se 1 (by rfl) ⟨1614002, by rfl⟩ : syracuseStep 2152003 = 3228005) B3228005
theorem B1005257 : Blo 595291 1005257 := bstep (se 2 (by rfl) ⟨376971, by rfl⟩ : syracuseStep 1005257 = 753943) B753943
theorem B1136443 : Blo 595291 1136443 := bstep (se 1 (by rfl) ⟨852332, by rfl⟩ : syracuseStep 1136443 = 1704665) B1704665
theorem B2021273 : Blo 595291 2021273 := bstep (se 2 (by rfl) ⟨757977, by rfl⟩ : syracuseStep 2021273 = 1515955) B1515955
theorem B11458583 : Blo 595291 11458583 := bstep (se 1 (by rfl) ⟨8593937, by rfl⟩ : syracuseStep 11458583 = 17187875) B17187875
theorem B2873411 : Blo 595291 2873411 := bstep (se 1 (by rfl) ⟨2155058, by rfl⟩ : syracuseStep 2873411 = 4310117) B4310117
theorem B6641837 : Blo 595291 6641837 := bstep (se 3 (by rfl) ⟨1245344, by rfl⟩ : syracuseStep 6641837 = 2490689) B2490689
theorem B6314273 : Blo 595291 6314273 := bstep (se 2 (by rfl) ⟨2367852, by rfl⟩ : syracuseStep 6314273 = 4735705) B4735705
theorem B1136929 : Blo 595291 1136929 := bstep (se 2 (by rfl) ⟨426348, by rfl⟩ : syracuseStep 1136929 = 852697) B852697
theorem B1005959 : Blo 595291 1005959 := bstep (se 1 (by rfl) ⟨754469, by rfl⟩ : syracuseStep 1005959 = 1508939) B1508939
theorem B2021975 : Blo 595291 2021975 := bstep (se 1 (by rfl) ⟨1516481, by rfl⟩ : syracuseStep 2021975 = 3032963) B3032963
theorem B809743 : Blo 595291 809743 := bstep (se 1 (by rfl) ⟨607307, by rfl⟩ : syracuseStep 809743 = 1214615) B1214615
theorem B2874163 : Blo 595291 2874163 := bstep (se 1 (by rfl) ⟨2155622, by rfl⟩ : syracuseStep 2874163 = 4311245) B4311245
theorem B1006607 : Blo 595291 1006607 := bstep (se 1 (by rfl) ⟨754955, by rfl⟩ : syracuseStep 1006607 = 1509911) B1509911
theorem B2022461 : Blo 595291 2022461 := bstep (se 3 (by rfl) ⟨379211, by rfl⟩ : syracuseStep 2022461 = 758423) B758423
theorem B2416139 : Blo 595291 2416139 := bstep (se 1 (by rfl) ⟨1812104, by rfl⟩ : syracuseStep 2416139 = 3624209) B3624209
theorem B3399191 : Blo 595291 3399191 := bstep (se 1 (by rfl) ⟨2549393, by rfl⟩ : syracuseStep 3399191 = 5098787) B5098787
theorem B1007147 : Blo 595291 1007147 := bstep (se 1 (by rfl) ⟨755360, by rfl⟩ : syracuseStep 1007147 = 1510721) B1510721
theorem B2416385 : Blo 595291 2416385 := bstep (se 2 (by rfl) ⟨906144, by rfl⟩ : syracuseStep 2416385 = 1812289) B1812289
theorem B12443543 : Blo 595291 12443543 := bstep (se 1 (by rfl) ⟨9332657, by rfl⟩ : syracuseStep 12443543 = 18665315) B18665315
theorem B1007545 : Blo 595291 1007545 := bstep (se 2 (by rfl) ⟨377829, by rfl⟩ : syracuseStep 1007545 = 755659) B755659
theorem B1695745 : Blo 595291 1695745 := bstep (se 2 (by rfl) ⟨635904, by rfl⟩ : syracuseStep 1695745 = 1271809) B1271809
theorem B3399691 : Blo 595291 3399691 := bstep (se 1 (by rfl) ⟨2549768, by rfl⟩ : syracuseStep 3399691 = 5099537) B5099537
theorem B1728697 : Blo 595291 1728697 := bstep (se 2 (by rfl) ⟨648261, by rfl⟩ : syracuseStep 1728697 = 1296523) B1296523
theorem B1696315 : Blo 595291 1696315 := bstep (se 1 (by rfl) ⟨1272236, by rfl⟩ : syracuseStep 1696315 = 2544473) B2544473
theorem B1008247 : Blo 595291 1008247 := bstep (se 1 (by rfl) ⟨756185, by rfl⟩ : syracuseStep 1008247 = 1512371) B1512371
theorem B1008443 : Blo 595291 1008443 := bstep (se 1 (by rfl) ⟨756332, by rfl⟩ : syracuseStep 1008443 = 1512665) B1512665
theorem B34366517 : Blo 595291 34366517 := bstep (se 5 (by rfl) ⟨1610930, by rfl⟩ : syracuseStep 34366517 = 3221861) B3221861
theorem B1008841 : Blo 595291 1008841 := bstep (se 2 (by rfl) ⟨378315, by rfl⟩ : syracuseStep 1008841 = 756631) B756631
theorem B8185121 : Blo 595291 8185121 := bstep (se 2 (by rfl) ⟨3069420, by rfl⟩ : syracuseStep 8185121 = 6138841) B6138841
theorem B23029109 : Blo 595291 23029109 := bstep (se 5 (by rfl) ⟨1079489, by rfl⟩ : syracuseStep 23029109 = 2158979) B2158979
theorem B4547987 : Blo 595291 4547987 := bstep (se 1 (by rfl) ⟨3410990, by rfl⟩ : syracuseStep 4547987 = 6821981) B6821981
theorem B13756229 : Blo 595291 13756229 := bstep (se 4 (by rfl) ⟨1289646, by rfl⟩ : syracuseStep 13756229 = 2579293) B2579293
theorem B1075079 : Blo 595291 1075079 := bstep (se 1 (by rfl) ⟨806309, by rfl⟩ : syracuseStep 1075079 = 1612619) B1612619
theorem B1009543 : Blo 595291 1009543 := bstep (se 1 (by rfl) ⟨757157, by rfl⟩ : syracuseStep 1009543 = 1514315) B1514315
theorem B2156473 : Blo 595291 2156473 := bstep (se 2 (by rfl) ⟨808677, by rfl⟩ : syracuseStep 2156473 = 1617355) B1617355
theorem B3401675 : Blo 595291 3401675 := bstep (se 1 (by rfl) ⟨2551256, by rfl⟩ : syracuseStep 3401675 = 5102513) B5102513
theorem B20670785 : Blo 595291 20670785 := bstep (se 2 (by rfl) ⟨7751544, by rfl⟩ : syracuseStep 20670785 = 15503089) B15503089
theorem B5728643 : Blo 595291 5728643 := bstep (se 1 (by rfl) ⟨4296482, by rfl⟩ : syracuseStep 5728643 = 8592965) B8592965
theorem B2550163 : Blo 595291 2550163 := bstep (se 1 (by rfl) ⟨1912622, by rfl⟩ : syracuseStep 2550163 = 3825245) B3825245
theorem B1010191 : Blo 595291 1010191 := bstep (se 1 (by rfl) ⟨757643, by rfl⟩ : syracuseStep 1010191 = 1515287) B1515287
theorem B1075771 : Blo 595291 1075771 := bstep (se 1 (by rfl) ⟨806828, by rfl⟩ : syracuseStep 1075771 = 1613657) B1613657
theorem B5434127 : Blo 595291 5434127 := bstep (se 1 (by rfl) ⟨4075595, by rfl⟩ : syracuseStep 5434127 = 8151191) B8151191
theorem B1698707 : Blo 595291 1698707 := bstep (se 1 (by rfl) ⟨1274030, by rfl⟩ : syracuseStep 1698707 = 2548061) B2548061
theorem B14740373 : Blo 595291 14740373 := bstep (se 6 (by rfl) ⟨345477, by rfl⟩ : syracuseStep 14740373 = 690955) B690955
theorem B3238865 : Blo 595291 3238865 := bstep (se 2 (by rfl) ⟨1214574, by rfl⟩ : syracuseStep 3238865 = 2429149) B2429149
theorem B2878487 : Blo 595291 2878487 := bstep (se 1 (by rfl) ⟨2158865, by rfl⟩ : syracuseStep 2878487 = 4317731) B4317731
theorem B1010731 : Blo 595291 1010731 := bstep (se 1 (by rfl) ⟨758048, by rfl⟩ : syracuseStep 1010731 = 1516097) B1516097
theorem B1010873 : Blo 595291 1010873 := bstep (se 2 (by rfl) ⟨379077, by rfl⟩ : syracuseStep 1010873 = 758155) B758155
theorem B14150861 : Blo 595291 14150861 := bstep (se 3 (by rfl) ⟨2653286, by rfl⟩ : syracuseStep 14150861 = 5306573) B5306573
theorem B1076665 : Blo 595291 1076665 := bstep (se 2 (by rfl) ⟨403749, by rfl⟩ : syracuseStep 1076665 = 807499) B807499
theorem B716431 : Blo 595291 716431 := bstep (se 1 (by rfl) ⟨537323, by rfl⟩ : syracuseStep 716431 = 1074647) B1074647
theorem B1699481 : Blo 595291 1699481 := bstep (se 2 (by rfl) ⟨637305, by rfl⟩ : syracuseStep 1699481 = 1274611) B1274611
theorem B847759 : Blo 595291 847759 := bstep (se 1 (by rfl) ⟨635819, by rfl⟩ : syracuseStep 847759 = 1271639) B1271639
theorem B2551819 : Blo 595291 2551819 := bstep (se 1 (by rfl) ⟨1913864, by rfl⟩ : syracuseStep 2551819 = 3827729) B3827729
theorem B716815 : Blo 595291 716815 := bstep (se 1 (by rfl) ⟨537611, by rfl⟩ : syracuseStep 716815 = 1075223) B1075223
theorem B1339451 : Blo 595291 1339451 := bstep (se 1 (by rfl) ⟨1004588, by rfl⟩ : syracuseStep 1339451 = 2009177) B2009177
theorem B13791325 : Blo 595291 13791325 := bstep (se 3 (by rfl) ⟨2585873, by rfl⟩ : syracuseStep 13791325 = 5171747) B5171747
theorem B1339577 : Blo 595291 1339577 := bstep (se 2 (by rfl) ⟨502341, by rfl⟩ : syracuseStep 1339577 = 1004683) B1004683
theorem B3404065 : Blo 595291 3404065 := bstep (se 2 (by rfl) ⟨1276524, by rfl⟩ : syracuseStep 3404065 = 2553049) B2553049
theorem B1208711 : Blo 595291 1208711 := bstep (se 1 (by rfl) ⟨906533, by rfl⟩ : syracuseStep 1208711 = 1813067) B1813067
theorem B11497949 : Blo 595291 11497949 := bstep (se 3 (by rfl) ⟨2155865, by rfl⟩ : syracuseStep 11497949 = 4311731) B4311731
theorem B1339919 : Blo 595291 1339919 := bstep (se 1 (by rfl) ⟨1004939, by rfl⟩ : syracuseStep 1339919 = 2009879) B2009879
theorem B1339937 : Blo 595291 1339937 := bstep (se 2 (by rfl) ⟨502476, by rfl⟩ : syracuseStep 1339937 = 1004953) B1004953
theorem B848647 : Blo 595291 848647 := bstep (se 1 (by rfl) ⟨636485, by rfl⟩ : syracuseStep 848647 = 1272971) B1272971
theorem B1078049 : Blo 595291 1078049 := bstep (se 2 (by rfl) ⟨404268, by rfl⟩ : syracuseStep 1078049 = 808537) B808537
theorem B3371813 : Blo 595291 3371813 := bstep (se 4 (by rfl) ⟨316107, by rfl⟩ : syracuseStep 3371813 = 632215) B632215
theorem B1340279 : Blo 595291 1340279 := bstep (se 1 (by rfl) ⟨1005209, by rfl⟩ : syracuseStep 1340279 = 2010419) B2010419
theorem B816143 : Blo 595291 816143 := bstep (se 1 (by rfl) ⟨612107, by rfl⟩ : syracuseStep 816143 = 1224215) B1224215
theorem B1340459 : Blo 595291 1340459 := bstep (se 1 (by rfl) ⟨1005344, by rfl⟩ : syracuseStep 1340459 = 2010689) B2010689
theorem B849143 : Blo 595291 849143 := bstep (se 1 (by rfl) ⟨636857, by rfl⟩ : syracuseStep 849143 = 1273715) B1273715
theorem B1209659 : Blo 595291 1209659 := bstep (se 1 (by rfl) ⟨907244, by rfl⟩ : syracuseStep 1209659 = 1814489) B1814489
theorem B1537339 : Blo 595291 1537339 := bstep (se 1 (by rfl) ⟨1153004, by rfl⟩ : syracuseStep 1537339 = 2306009) B2306009
theorem B1340819 : Blo 595291 1340819 := bstep (se 1 (by rfl) ⟨1005614, by rfl⟩ : syracuseStep 1340819 = 2011229) B2011229
theorem B1340873 : Blo 595291 1340873 := bstep (se 2 (by rfl) ⟨502827, by rfl⟩ : syracuseStep 1340873 = 1005655) B1005655
theorem B3405341 : Blo 595291 3405341 := bstep (se 3 (by rfl) ⟨638501, by rfl⟩ : syracuseStep 3405341 = 1277003) B1277003
theorem B718507 : Blo 595291 718507 := bstep (se 1 (by rfl) ⟨538880, by rfl⟩ : syracuseStep 718507 = 1077761) B1077761
theorem B1701577 : Blo 595291 1701577 := bstep (se 2 (by rfl) ⟨638091, by rfl⟩ : syracuseStep 1701577 = 1276183) B1276183
theorem B2422561 : Blo 595291 2422561 := bstep (se 2 (by rfl) ⟨908460, by rfl⟩ : syracuseStep 2422561 = 1816921) B1816921
theorem B1701931 : Blo 595291 1701931 := bstep (se 1 (by rfl) ⟨1276448, by rfl⟩ : syracuseStep 1701931 = 2552897) B2552897
theorem B1341575 : Blo 595291 1341575 := bstep (se 1 (by rfl) ⟨1006181, by rfl⟩ : syracuseStep 1341575 = 2012363) B2012363
theorem B850105 : Blo 595291 850105 := bstep (se 2 (by rfl) ⟨318789, by rfl⟩ : syracuseStep 850105 = 637579) B637579
theorem B1276175 : Blo 595291 1276175 := bstep (se 1 (by rfl) ⟨957131, by rfl⟩ : syracuseStep 1276175 = 1914263) B1914263
theorem B1341755 : Blo 595291 1341755 := bstep (se 1 (by rfl) ⟨1006316, by rfl⟩ : syracuseStep 1341755 = 2012633) B2012633
theorem B1702205 : Blo 595291 1702205 := bstep (se 3 (by rfl) ⟨319163, by rfl⟩ : syracuseStep 1702205 = 638327) B638327
theorem B1341881 : Blo 595291 1341881 := bstep (se 2 (by rfl) ⟨503205, by rfl⟩ : syracuseStep 1341881 = 1006411) B1006411
theorem B21559769 : Blo 595291 21559769 := bstep (se 2 (by rfl) ⟨8084913, by rfl⟩ : syracuseStep 21559769 = 16169827) B16169827
theorem B850447 : Blo 595291 850447 := bstep (se 1 (by rfl) ⟨637835, by rfl⟩ : syracuseStep 850447 = 1275671) B1275671
theorem B1342223 : Blo 595291 1342223 := bstep (se 1 (by rfl) ⟨1006667, by rfl⟩ : syracuseStep 1342223 = 2013335) B2013335
theorem B1342241 : Blo 595291 1342241 := bstep (se 2 (by rfl) ⟨503340, by rfl⟩ : syracuseStep 1342241 = 1006681) B1006681
theorem B1342583 : Blo 595291 1342583 := bstep (se 1 (by rfl) ⟨1006937, by rfl⟩ : syracuseStep 1342583 = 2013875) B2013875
theorem B1342763 : Blo 595291 1342763 := bstep (se 1 (by rfl) ⟨1007072, by rfl⟩ : syracuseStep 1342763 = 2014145) B2014145
theorem B44039483 : Blo 595291 44039483 := bstep (se 1 (by rfl) ⟨33029612, by rfl⟩ : syracuseStep 44039483 = 66059225) B66059225
theorem B5111261 : Blo 595291 5111261 := bstep (se 3 (by rfl) ⟨958361, by rfl⟩ : syracuseStep 5111261 = 1916723) B1916723
theorem B4095517 : Blo 595291 4095517 := bstep (se 3 (by rfl) ⟨767909, by rfl⟩ : syracuseStep 4095517 = 1535819) B1535819
theorem B851575 : Blo 595291 851575 := bstep (se 1 (by rfl) ⟨638681, by rfl⟩ : syracuseStep 851575 = 1277363) B1277363
theorem B1343123 : Blo 595291 1343123 := bstep (se 1 (by rfl) ⟨1007342, by rfl⟩ : syracuseStep 1343123 = 2014685) B2014685
theorem B1146569 : Blo 595291 1146569 := bstep (se 2 (by rfl) ⟨429963, by rfl⟩ : syracuseStep 1146569 = 859927) B859927
theorem B1343177 : Blo 595291 1343177 := bstep (se 2 (by rfl) ⟨503691, by rfl⟩ : syracuseStep 1343177 = 1007383) B1007383
theorem B3440357 : Blo 595291 3440357 := bstep (se 4 (by rfl) ⟨322533, by rfl⟩ : syracuseStep 3440357 = 645067) B645067
theorem B4521743 : Blo 595291 4521743 := bstep (se 1 (by rfl) ⟨3391307, by rfl⟩ : syracuseStep 4521743 = 6782615) B6782615
theorem B1507187 : Blo 595291 1507187 := bstep (se 1 (by rfl) ⟨1130390, by rfl⟩ : syracuseStep 1507187 = 2260781) B2260781
theorem B1507207 : Blo 595291 1507207 := bstep (se 1 (by rfl) ⟨1130405, by rfl⟩ : syracuseStep 1507207 = 2260811) B2260811
theorem B2555783 : Blo 595291 2555783 := bstep (se 1 (by rfl) ⟨1916837, by rfl⟩ : syracuseStep 2555783 = 3833675) B3833675
theorem B2260993 : Blo 595291 2260993 := bstep (se 2 (by rfl) ⟨847872, by rfl⟩ : syracuseStep 2260993 = 1695745) B1695745
theorem B7635059 : Blo 595291 7635059 := bstep (se 1 (by rfl) ⟨5726294, by rfl⟩ : syracuseStep 7635059 = 11452589) B11452589
theorem B852167 : Blo 595291 852167 := bstep (se 1 (by rfl) ⟨639125, by rfl⟩ : syracuseStep 852167 = 1278251) B1278251
theorem B1343735 : Blo 595291 1343735 := bstep (se 1 (by rfl) ⟨1007801, by rfl⟩ : syracuseStep 1343735 = 2015603) B2015603
theorem B3408257 : Blo 595291 3408257 := bstep (se 2 (by rfl) ⟨1278096, by rfl⟩ : syracuseStep 3408257 = 2556193) B2556193
theorem B1147279 : Blo 595291 1147279 := bstep (se 1 (by rfl) ⟨860459, by rfl⟩ : syracuseStep 1147279 = 1720919) B1720919
theorem B10191419 : Blo 595291 10191419 := bstep (se 1 (by rfl) ⟨7643564, by rfl⟩ : syracuseStep 10191419 = 15287129) B15287129
theorem B2261753 : Blo 595291 2261753 := bstep (se 2 (by rfl) ⟨848157, by rfl⟩ : syracuseStep 2261753 = 1696315) B1696315
theorem B1344329 : Blo 595291 1344329 := bstep (se 2 (by rfl) ⟨504123, by rfl⟩ : syracuseStep 1344329 = 1008247) B1008247
theorem B3408713 : Blo 595291 3408713 := bstep (se 2 (by rfl) ⟨1278267, by rfl⟩ : syracuseStep 3408713 = 2556535) B2556535
theorem B918379 : Blo 595291 918379 := bstep (se 1 (by rfl) ⟨688784, by rfl⟩ : syracuseStep 918379 = 1377569) B1377569
theorem B2458475 : Blo 595291 2458475 := bstep (se 1 (by rfl) ⟨1843856, by rfl⟩ : syracuseStep 2458475 = 3687713) B3687713
theorem B4523201 : Blo 595291 4523201 := bstep (se 2 (by rfl) ⟨1696200, by rfl⟩ : syracuseStep 4523201 = 3392401) B3392401
theorem B8750429 : Blo 595291 8750429 := bstep (se 3 (by rfl) ⟨1640705, by rfl⟩ : syracuseStep 8750429 = 3281411) B3281411
theorem B1508827 : Blo 595291 1508827 := bstep (se 1 (by rfl) ⟨1131620, by rfl⟩ : syracuseStep 1508827 = 2263241) B2263241
theorem B755239 : Blo 595291 755239 := bstep (se 1 (by rfl) ⟨566429, by rfl⟩ : syracuseStep 755239 = 1132859) B1132859
theorem B1345121 : Blo 595291 1345121 := bstep (se 2 (by rfl) ⟨504420, by rfl⟩ : syracuseStep 1345121 = 1008841) B1008841
theorem B755563 : Blo 595291 755563 := bstep (se 1 (by rfl) ⟨566672, by rfl⟩ : syracuseStep 755563 = 1133345) B1133345
theorem B1345463 : Blo 595291 1345463 := bstep (se 1 (by rfl) ⟨1009097, by rfl⟩ : syracuseStep 1345463 = 2018195) B2018195
theorem B3835907 : Blo 595291 3835907 := bstep (se 1 (by rfl) ⟨2876930, by rfl⟩ : syracuseStep 3835907 = 5753861) B5753861
theorem B1378361 : Blo 595291 1378361 := bstep (se 2 (by rfl) ⟨516885, by rfl⟩ : syracuseStep 1378361 = 1033771) B1033771
theorem B1509455 : Blo 595291 1509455 := bstep (se 1 (by rfl) ⟨1132091, by rfl⟩ : syracuseStep 1509455 = 2264183) B2264183
theorem B2623603 : Blo 595291 2623603 := bstep (se 1 (by rfl) ⟨1967702, by rfl⟩ : syracuseStep 2623603 = 3935405) B3935405
theorem B2263211 : Blo 595291 2263211 := bstep (se 1 (by rfl) ⟨1697408, by rfl⟩ : syracuseStep 2263211 = 3394817) B3394817
theorem B3639563 : Blo 595291 3639563 := bstep (se 1 (by rfl) ⟨2729672, by rfl⟩ : syracuseStep 3639563 = 5459345) B5459345
theorem B9668969 : Blo 595291 9668969 := bstep (se 2 (by rfl) ⟨3625863, by rfl⟩ : syracuseStep 9668969 = 7251727) B7251727
theorem B1214939 : Blo 595291 1214939 := bstep (se 1 (by rfl) ⟨911204, by rfl⟩ : syracuseStep 1214939 = 1822409) B1822409
theorem B1346057 : Blo 595291 1346057 := bstep (se 2 (by rfl) ⟨504771, by rfl⟩ : syracuseStep 1346057 = 1009543) B1009543
theorem B1706521 : Blo 595291 1706521 := bstep (se 2 (by rfl) ⟨639945, by rfl⟩ : syracuseStep 1706521 = 1279891) B1279891
theorem B3017249 : Blo 595291 3017249 := bstep (se 2 (by rfl) ⟨1131468, by rfl⟩ : syracuseStep 3017249 = 2262937) B2262937
theorem B66292343 : Blo 595291 66292343 := bstep (se 1 (by rfl) ⟨49719257, by rfl⟩ : syracuseStep 66292343 = 99438515) B99438515
theorem B22088393 : Blo 595291 22088393 := bstep (se 2 (by rfl) ⟨8283147, by rfl⟩ : syracuseStep 22088393 = 16566295) B16566295
theorem B1510103 : Blo 595291 1510103 := bstep (se 1 (by rfl) ⟨1132577, by rfl⟩ : syracuseStep 1510103 = 2265155) B2265155
theorem B1346399 : Blo 595291 1346399 := bstep (se 1 (by rfl) ⟨1009799, by rfl⟩ : syracuseStep 1346399 = 2019599) B2019599
theorem B1346579 : Blo 595291 1346579 := bstep (se 1 (by rfl) ⟨1009934, by rfl⟩ : syracuseStep 1346579 = 2019869) B2019869
theorem B756859 : Blo 595291 756859 := bstep (se 1 (by rfl) ⟨567644, by rfl⟩ : syracuseStep 756859 = 1135289) B1135289
theorem B2264381 : Blo 595291 2264381 := bstep (se 3 (by rfl) ⟨424571, by rfl⟩ : syracuseStep 2264381 = 849143) B849143
theorem B1346921 : Blo 595291 1346921 := bstep (se 2 (by rfl) ⟨505095, by rfl⟩ : syracuseStep 1346921 = 1010191) B1010191
theorem B9702899 : Blo 595291 9702899 := bstep (se 1 (by rfl) ⟨7277174, by rfl⟩ : syracuseStep 9702899 = 14554349) B14554349
theorem B2493985 : Blo 595291 2493985 := bstep (se 2 (by rfl) ⟨935244, by rfl⟩ : syracuseStep 2493985 = 1870489) B1870489
theorem B921127 : Blo 595291 921127 := bstep (se 1 (by rfl) ⟨690845, by rfl⟩ : syracuseStep 921127 = 1381691) B1381691
theorem B2264699 : Blo 595291 2264699 := bstep (se 1 (by rfl) ⟨1698524, by rfl⟩ : syracuseStep 2264699 = 3397049) B3397049
theorem B1347515 : Blo 595291 1347515 := bstep (se 1 (by rfl) ⟨1010636, by rfl⟩ : syracuseStep 1347515 = 2021273) B2021273
theorem B7639055 : Blo 595291 7639055 := bstep (se 1 (by rfl) ⟨5729291, by rfl⟩ : syracuseStep 7639055 = 11458583) B11458583
theorem B4526117 : Blo 595291 4526117 := bstep (se 4 (by rfl) ⟨424323, by rfl⟩ : syracuseStep 4526117 = 848647) B848647
theorem B1347641 : Blo 595291 1347641 := bstep (se 2 (by rfl) ⟨505365, by rfl⟩ : syracuseStep 1347641 = 1010731) B1010731
theorem B4427891 : Blo 595291 4427891 := bstep (se 1 (by rfl) ⟨3320918, by rfl⟩ : syracuseStep 4427891 = 6641837) B6641837
theorem B3641705 : Blo 595291 3641705 := bstep (se 2 (by rfl) ⟨1365639, by rfl⟩ : syracuseStep 3641705 = 2731279) B2731279
theorem B1347983 : Blo 595291 1347983 := bstep (se 1 (by rfl) ⟨1010987, by rfl⟩ : syracuseStep 1347983 = 2021975) B2021975
theorem B1348307 : Blo 595291 1348307 := bstep (se 1 (by rfl) ⟨1011230, by rfl⟩ : syracuseStep 1348307 = 2022461) B2022461
theorem B955241 : Blo 595291 955241 := bstep (se 2 (by rfl) ⟨358215, by rfl⟩ : syracuseStep 955241 = 716431) B716431
theorem B2626561 : Blo 595291 2626561 := bstep (se 2 (by rfl) ⟨984960, by rfl⟩ : syracuseStep 2626561 = 1969921) B1969921
theorem B1610759 : Blo 595291 1610759 := bstep (se 1 (by rfl) ⟨1208069, by rfl⟩ : syracuseStep 1610759 = 2416139) B2416139
theorem B2266127 : Blo 595291 2266127 := bstep (se 1 (by rfl) ⟨1699595, by rfl⟩ : syracuseStep 2266127 = 3399191) B3399191
theorem B2036755 : Blo 595291 2036755 := bstep (se 1 (by rfl) ⟨1527566, by rfl⟩ : syracuseStep 2036755 = 3055133) B3055133
theorem B1610923 : Blo 595291 1610923 := bstep (se 1 (by rfl) ⟨1208192, by rfl⟩ : syracuseStep 1610923 = 2416385) B2416385
theorem B1512695 : Blo 595291 1512695 := bstep (se 1 (by rfl) ⟨1134521, by rfl⟩ : syracuseStep 1512695 = 2269043) B2269043
theorem B8295695 : Blo 595291 8295695 := bstep (se 1 (by rfl) ⟨6221771, by rfl⟩ : syracuseStep 8295695 = 12443543) B12443543
theorem B595295 : Blo 595291 595295 := bstep (se 1 (by rfl) ⟨446471, by rfl⟩ : syracuseStep 595295 = 892943) B892943
theorem B595323 : Blo 595291 595323 := bstep (se 1 (by rfl) ⟨446492, by rfl⟩ : syracuseStep 595323 = 892985) B892985
theorem B595375 : Blo 595291 595375 := bstep (se 1 (by rfl) ⟨446531, by rfl⟩ : syracuseStep 595375 = 893063) B893063
theorem B595399 : Blo 595291 595399 := bstep (se 1 (by rfl) ⟨446549, by rfl⟩ : syracuseStep 595399 = 893099) B893099
theorem B18388433 : Blo 595291 18388433 := bstep (se 2 (by rfl) ⟨6895662, by rfl⟩ : syracuseStep 18388433 = 13791325) B13791325
theorem B595419 : Blo 595291 595419 := bstep (se 1 (by rfl) ⟨446564, by rfl⟩ : syracuseStep 595419 = 893129) B893129
theorem B2299355 : Blo 595291 2299355 := bstep (se 1 (by rfl) ⟨1724516, by rfl⟩ : syracuseStep 2299355 = 3449033) B3449033
theorem B595495 : Blo 595291 595495 := bstep (se 1 (by rfl) ⟨446621, by rfl⟩ : syracuseStep 595495 = 893243) B893243
theorem B3020327 : Blo 595291 3020327 := bstep (se 1 (by rfl) ⟨2265245, by rfl⟩ : syracuseStep 3020327 = 4530491) B4530491
theorem B595535 : Blo 595291 595535 := bstep (se 1 (by rfl) ⟨446651, by rfl⟩ : syracuseStep 595535 = 893303) B893303
theorem B595551 : Blo 595291 595551 := bstep (se 1 (by rfl) ⟨446663, by rfl⟩ : syracuseStep 595551 = 893327) B893327
theorem B595579 : Blo 595291 595579 := bstep (se 1 (by rfl) ⟨446684, by rfl⟩ : syracuseStep 595579 = 893369) B893369
theorem B595631 : Blo 595291 595631 := bstep (se 1 (by rfl) ⟨446723, by rfl⟩ : syracuseStep 595631 = 893447) B893447
theorem B595655 : Blo 595291 595655 := bstep (se 1 (by rfl) ⟨446741, by rfl⟩ : syracuseStep 595655 = 893483) B893483
theorem B7280327 : Blo 595291 7280327 := bstep (se 1 (by rfl) ⟨5460245, by rfl⟩ : syracuseStep 7280327 = 10920491) B10920491
theorem B1971911 : Blo 595291 1971911 := bstep (se 1 (by rfl) ⟨1478933, by rfl⟩ : syracuseStep 1971911 = 2957867) B2957867
theorem B595675 : Blo 595291 595675 := bstep (se 1 (by rfl) ⟨446756, by rfl⟩ : syracuseStep 595675 = 893513) B893513
theorem B595751 : Blo 595291 595751 := bstep (se 1 (by rfl) ⟨446813, by rfl⟩ : syracuseStep 595751 = 893627) B893627
theorem B595791 : Blo 595291 595791 := bstep (se 1 (by rfl) ⟨446843, by rfl⟩ : syracuseStep 595791 = 893687) B893687
theorem B595807 : Blo 595291 595807 := bstep (se 1 (by rfl) ⟨446855, by rfl⟩ : syracuseStep 595807 = 893711) B893711
theorem B595835 : Blo 595291 595835 := bstep (se 1 (by rfl) ⟨446876, by rfl⟩ : syracuseStep 595835 = 893753) B893753
theorem B595887 : Blo 595291 595887 := bstep (se 1 (by rfl) ⟨446915, by rfl⟩ : syracuseStep 595887 = 893831) B893831
theorem B595911 : Blo 595291 595911 := bstep (se 1 (by rfl) ⟨446933, by rfl⟩ : syracuseStep 595911 = 893867) B893867
theorem B595931 : Blo 595291 595931 := bstep (se 1 (by rfl) ⟨446948, by rfl⟩ : syracuseStep 595931 = 893897) B893897
theorem B22911011 : Blo 595291 22911011 := bstep (se 1 (by rfl) ⟨17183258, by rfl⟩ : syracuseStep 22911011 = 34366517) B34366517
theorem B596007 : Blo 595291 596007 := bstep (se 1 (by rfl) ⟨447005, by rfl⟩ : syracuseStep 596007 = 894011) B894011
theorem B596047 : Blo 595291 596047 := bstep (se 1 (by rfl) ⟨447035, by rfl⟩ : syracuseStep 596047 = 894071) B894071
theorem B596063 : Blo 595291 596063 := bstep (se 1 (by rfl) ⟨447047, by rfl⟩ : syracuseStep 596063 = 894095) B894095
theorem B596091 : Blo 595291 596091 := bstep (se 1 (by rfl) ⟨447068, by rfl⟩ : syracuseStep 596091 = 894137) B894137
theorem B596143 : Blo 595291 596143 := bstep (se 1 (by rfl) ⟨447107, by rfl⟩ : syracuseStep 596143 = 894215) B894215
theorem B596167 : Blo 595291 596167 := bstep (se 1 (by rfl) ⟨447125, by rfl⟩ : syracuseStep 596167 = 894251) B894251
theorem B596187 : Blo 595291 596187 := bstep (se 1 (by rfl) ⟨447140, by rfl⟩ : syracuseStep 596187 = 894281) B894281
theorem B596263 : Blo 595291 596263 := bstep (se 1 (by rfl) ⟨447197, by rfl⟩ : syracuseStep 596263 = 894395) B894395
theorem B596303 : Blo 595291 596303 := bstep (se 1 (by rfl) ⟨447227, by rfl⟩ : syracuseStep 596303 = 894455) B894455
theorem B596319 : Blo 595291 596319 := bstep (se 1 (by rfl) ⟨447239, by rfl⟩ : syracuseStep 596319 = 894479) B894479
theorem B596347 : Blo 595291 596347 := bstep (se 1 (by rfl) ⟨447260, by rfl⟩ : syracuseStep 596347 = 894521) B894521
theorem B596399 : Blo 595291 596399 := bstep (se 1 (by rfl) ⟨447299, by rfl⟩ : syracuseStep 596399 = 894599) B894599
theorem B596423 : Blo 595291 596423 := bstep (se 1 (by rfl) ⟨447317, by rfl⟩ : syracuseStep 596423 = 894635) B894635
theorem B596443 : Blo 595291 596443 := bstep (se 1 (by rfl) ⟨447332, by rfl⟩ : syracuseStep 596443 = 894665) B894665
theorem B596519 : Blo 595291 596519 := bstep (se 1 (by rfl) ⟨447389, by rfl⟩ : syracuseStep 596519 = 894779) B894779
theorem B596559 : Blo 595291 596559 := bstep (se 1 (by rfl) ⟨447419, by rfl⟩ : syracuseStep 596559 = 894839) B894839
theorem B596575 : Blo 595291 596575 := bstep (se 1 (by rfl) ⟨447431, by rfl⟩ : syracuseStep 596575 = 894863) B894863
theorem B596603 : Blo 595291 596603 := bstep (se 1 (by rfl) ⟨447452, by rfl⟩ : syracuseStep 596603 = 894905) B894905
theorem B2267783 : Blo 595291 2267783 := bstep (se 1 (by rfl) ⟨1700837, by rfl⟩ : syracuseStep 2267783 = 3401675) B3401675
theorem B1514123 : Blo 595291 1514123 := bstep (se 1 (by rfl) ⟨1135592, by rfl⟩ : syracuseStep 1514123 = 2271185) B2271185
theorem B596655 : Blo 595291 596655 := bstep (se 1 (by rfl) ⟨447491, by rfl⟩ : syracuseStep 596655 = 894983) B894983
theorem B596679 : Blo 595291 596679 := bstep (se 1 (by rfl) ⟨447509, by rfl⟩ : syracuseStep 596679 = 895019) B895019
theorem B596699 : Blo 595291 596699 := bstep (se 1 (by rfl) ⟨447524, by rfl⟩ : syracuseStep 596699 = 895049) B895049
theorem B596775 : Blo 595291 596775 := bstep (se 1 (by rfl) ⟨447581, by rfl⟩ : syracuseStep 596775 = 895163) B895163
theorem B596815 : Blo 595291 596815 := bstep (se 1 (by rfl) ⟨447611, by rfl⟩ : syracuseStep 596815 = 895223) B895223
theorem B596831 : Blo 595291 596831 := bstep (se 1 (by rfl) ⟨447623, by rfl⟩ : syracuseStep 596831 = 895247) B895247
theorem B1514335 : Blo 595291 1514335 := bstep (se 1 (by rfl) ⟨1135751, by rfl⟩ : syracuseStep 1514335 = 2271503) B2271503
theorem B596859 : Blo 595291 596859 := bstep (se 1 (by rfl) ⟨447644, by rfl⟩ : syracuseStep 596859 = 895289) B895289
theorem B596911 : Blo 595291 596911 := bstep (se 1 (by rfl) ⟨447683, by rfl⟩ : syracuseStep 596911 = 895367) B895367
theorem B596935 : Blo 595291 596935 := bstep (se 1 (by rfl) ⟨447701, by rfl⟩ : syracuseStep 596935 = 895403) B895403
theorem B596955 : Blo 595291 596955 := bstep (se 1 (by rfl) ⟨447716, by rfl⟩ : syracuseStep 596955 = 895433) B895433
theorem B2759681 : Blo 595291 2759681 := bstep (se 2 (by rfl) ⟨1034880, by rfl⟩ : syracuseStep 2759681 = 2069761) B2069761
theorem B597031 : Blo 595291 597031 := bstep (se 1 (by rfl) ⟨447773, by rfl⟩ : syracuseStep 597031 = 895547) B895547
theorem B597071 : Blo 595291 597071 := bstep (se 1 (by rfl) ⟨447803, by rfl⟩ : syracuseStep 597071 = 895607) B895607
theorem B597087 : Blo 595291 597087 := bstep (se 1 (by rfl) ⟨447815, by rfl⟩ : syracuseStep 597087 = 895631) B895631
theorem B597115 : Blo 595291 597115 := bstep (se 1 (by rfl) ⟨447836, by rfl⟩ : syracuseStep 597115 = 895673) B895673
theorem B597167 : Blo 595291 597167 := bstep (se 1 (by rfl) ⟨447875, by rfl⟩ : syracuseStep 597167 = 895751) B895751
theorem B597191 : Blo 595291 597191 := bstep (se 1 (by rfl) ⟨447893, by rfl⟩ : syracuseStep 597191 = 895787) B895787
theorem B597211 : Blo 595291 597211 := bstep (se 1 (by rfl) ⟨447908, by rfl⟩ : syracuseStep 597211 = 895817) B895817
theorem B597287 : Blo 595291 597287 := bstep (se 1 (by rfl) ⟨447965, by rfl⟩ : syracuseStep 597287 = 895931) B895931
theorem B597327 : Blo 595291 597327 := bstep (se 1 (by rfl) ⟨447995, by rfl⟩ : syracuseStep 597327 = 895991) B895991
theorem B597343 : Blo 595291 597343 := bstep (se 1 (by rfl) ⟨448007, by rfl⟩ : syracuseStep 597343 = 896015) B896015
theorem B597371 : Blo 595291 597371 := bstep (se 1 (by rfl) ⟨448028, by rfl⟩ : syracuseStep 597371 = 896057) B896057
theorem B597423 : Blo 595291 597423 := bstep (se 1 (by rfl) ⟨448067, by rfl⟩ : syracuseStep 597423 = 896135) B896135
theorem B597447 : Blo 595291 597447 := bstep (se 1 (by rfl) ⟨448085, by rfl⟩ : syracuseStep 597447 = 896171) B896171
theorem B597467 : Blo 595291 597467 := bstep (se 1 (by rfl) ⟨448100, by rfl⟩ : syracuseStep 597467 = 896201) B896201
theorem B597543 : Blo 595291 597543 := bstep (se 1 (by rfl) ⟨448157, by rfl⟩ : syracuseStep 597543 = 896315) B896315
theorem B958009 : Blo 595291 958009 := bstep (se 2 (by rfl) ⟨359253, by rfl⟩ : syracuseStep 958009 = 718507) B718507
theorem B597583 : Blo 595291 597583 := bstep (se 1 (by rfl) ⟨448187, by rfl⟩ : syracuseStep 597583 = 896375) B896375
theorem B597599 : Blo 595291 597599 := bstep (se 1 (by rfl) ⟨448199, by rfl⟩ : syracuseStep 597599 = 896399) B896399
theorem B3022433 : Blo 595291 3022433 := bstep (se 2 (by rfl) ⟨1133412, by rfl⟩ : syracuseStep 3022433 = 2266825) B2266825
theorem B2268769 : Blo 595291 2268769 := bstep (se 2 (by rfl) ⟨850788, by rfl⟩ : syracuseStep 2268769 = 1701577) B1701577
theorem B597627 : Blo 595291 597627 := bstep (se 1 (by rfl) ⟨448220, by rfl⟩ : syracuseStep 597627 = 896441) B896441
theorem B597679 : Blo 595291 597679 := bstep (se 1 (by rfl) ⟨448259, by rfl⟩ : syracuseStep 597679 = 896519) B896519
theorem B597703 : Blo 595291 597703 := bstep (se 1 (by rfl) ⟨448277, by rfl⟩ : syracuseStep 597703 = 896555) B896555
theorem B597723 : Blo 595291 597723 := bstep (se 1 (by rfl) ⟨448292, by rfl⟩ : syracuseStep 597723 = 896585) B896585
theorem B1515257 : Blo 595291 1515257 := bstep (se 2 (by rfl) ⟨568221, by rfl⟩ : syracuseStep 1515257 = 1136443) B1136443
theorem B597799 : Blo 595291 597799 := bstep (se 1 (by rfl) ⟨448349, by rfl⟩ : syracuseStep 597799 = 896699) B896699
theorem B597839 : Blo 595291 597839 := bstep (se 1 (by rfl) ⟨448379, by rfl⟩ : syracuseStep 597839 = 896759) B896759
theorem B597855 : Blo 595291 597855 := bstep (se 1 (by rfl) ⟨448391, by rfl⟩ : syracuseStep 597855 = 896783) B896783
theorem B597883 : Blo 595291 597883 := bstep (se 1 (by rfl) ⟨448412, by rfl⟩ : syracuseStep 597883 = 896825) B896825
theorem B597935 : Blo 595291 597935 := bstep (se 1 (by rfl) ⟨448451, by rfl⟩ : syracuseStep 597935 = 896903) B896903
theorem B597959 : Blo 595291 597959 := bstep (se 1 (by rfl) ⟨448469, by rfl⟩ : syracuseStep 597959 = 896939) B896939
theorem B597979 : Blo 595291 597979 := bstep (se 1 (by rfl) ⟨448484, by rfl⟩ : syracuseStep 597979 = 896969) B896969
theorem B892937 : Blo 595291 892937 := bstep (se 2 (by rfl) ⟨334851, by rfl⟩ : syracuseStep 892937 = 669703) B669703
theorem B5447695 : Blo 595291 5447695 := bstep (se 1 (by rfl) ⟨4085771, by rfl⟩ : syracuseStep 5447695 = 8171543) B8171543
theorem B892967 : Blo 595291 892967 := bstep (se 1 (by rfl) ⟨669725, by rfl⟩ : syracuseStep 892967 = 1339451) B1339451
theorem B598055 : Blo 595291 598055 := bstep (se 1 (by rfl) ⟨448541, by rfl⟩ : syracuseStep 598055 = 897083) B897083
theorem B2269241 : Blo 595291 2269241 := bstep (se 2 (by rfl) ⟨850965, by rfl⟩ : syracuseStep 2269241 = 1701931) B1701931
theorem B598095 : Blo 595291 598095 := bstep (se 1 (by rfl) ⟨448571, by rfl⟩ : syracuseStep 598095 = 897143) B897143
theorem B598111 : Blo 595291 598111 := bstep (se 1 (by rfl) ⟨448583, by rfl⟩ : syracuseStep 598111 = 897167) B897167
theorem B893051 : Blo 595291 893051 := bstep (se 1 (by rfl) ⟨669788, by rfl⟩ : syracuseStep 893051 = 1339577) B1339577
theorem B598139 : Blo 595291 598139 := bstep (se 1 (by rfl) ⟨448604, by rfl⟩ : syracuseStep 598139 = 897209) B897209
theorem B1613981 : Blo 595291 1613981 := bstep (se 3 (by rfl) ⟨302621, by rfl⟩ : syracuseStep 1613981 = 605243) B605243
theorem B598191 : Blo 595291 598191 := bstep (se 1 (by rfl) ⟨448643, by rfl⟩ : syracuseStep 598191 = 897287) B897287
theorem B598215 : Blo 595291 598215 := bstep (se 1 (by rfl) ⟨448661, by rfl⟩ : syracuseStep 598215 = 897323) B897323
theorem B598235 : Blo 595291 598235 := bstep (se 1 (by rfl) ⟨448676, by rfl⟩ : syracuseStep 598235 = 897353) B897353
theorem B893177 : Blo 595291 893177 := bstep (se 2 (by rfl) ⟨334941, by rfl⟩ : syracuseStep 893177 = 669883) B669883
theorem B598311 : Blo 595291 598311 := bstep (se 1 (by rfl) ⟨448733, by rfl⟩ : syracuseStep 598311 = 897467) B897467
theorem B598351 : Blo 595291 598351 := bstep (se 1 (by rfl) ⟨448763, by rfl⟩ : syracuseStep 598351 = 897527) B897527
theorem B893279 : Blo 595291 893279 := bstep (se 1 (by rfl) ⟨669959, by rfl⟩ : syracuseStep 893279 = 1339919) B1339919
theorem B598367 : Blo 595291 598367 := bstep (se 1 (by rfl) ⟨448775, by rfl⟩ : syracuseStep 598367 = 897551) B897551
theorem B893291 : Blo 595291 893291 := bstep (se 1 (by rfl) ⟨669968, by rfl⟩ : syracuseStep 893291 = 1339937) B1339937
theorem B598395 : Blo 595291 598395 := bstep (se 1 (by rfl) ⟨448796, by rfl⟩ : syracuseStep 598395 = 897593) B897593
theorem B1515905 : Blo 595291 1515905 := bstep (se 2 (by rfl) ⟨568464, by rfl⟩ : syracuseStep 1515905 = 1136929) B1136929
theorem B598447 : Blo 595291 598447 := bstep (se 1 (by rfl) ⟨448835, by rfl⟩ : syracuseStep 598447 = 897671) B897671
theorem B598471 : Blo 595291 598471 := bstep (se 1 (by rfl) ⟨448853, by rfl⟩ : syracuseStep 598471 = 897707) B897707
theorem B598491 : Blo 595291 598491 := bstep (se 1 (by rfl) ⟨448868, by rfl⟩ : syracuseStep 598491 = 897737) B897737
theorem B598567 : Blo 595291 598567 := bstep (se 1 (by rfl) ⟨448925, by rfl⟩ : syracuseStep 598567 = 897851) B897851
theorem B893519 : Blo 595291 893519 := bstep (se 1 (by rfl) ⟨670139, by rfl⟩ : syracuseStep 893519 = 1340279) B1340279
theorem B598607 : Blo 595291 598607 := bstep (se 1 (by rfl) ⟨448955, by rfl⟩ : syracuseStep 598607 = 897911) B897911
theorem B598623 : Blo 595291 598623 := bstep (se 1 (by rfl) ⟨448967, by rfl⟩ : syracuseStep 598623 = 897935) B897935
theorem B10887797 : Blo 595291 10887797 := bstep (se 5 (by rfl) ⟨510365, by rfl⟩ : syracuseStep 10887797 = 1020731) B1020731
theorem B598651 : Blo 595291 598651 := bstep (se 1 (by rfl) ⟨448988, by rfl⟩ : syracuseStep 598651 = 897977) B897977
theorem B598703 : Blo 595291 598703 := bstep (se 1 (by rfl) ⟨449027, by rfl⟩ : syracuseStep 598703 = 898055) B898055
theorem B893639 : Blo 595291 893639 := bstep (se 1 (by rfl) ⟨670229, by rfl⟩ : syracuseStep 893639 = 1340459) B1340459
theorem B598727 : Blo 595291 598727 := bstep (se 1 (by rfl) ⟨449045, by rfl⟩ : syracuseStep 598727 = 898091) B898091
theorem B598747 : Blo 595291 598747 := bstep (se 1 (by rfl) ⟨449060, by rfl⟩ : syracuseStep 598747 = 898121) B898121
theorem B598823 : Blo 595291 598823 := bstep (se 1 (by rfl) ⟨449117, by rfl⟩ : syracuseStep 598823 = 898235) B898235
theorem B598863 : Blo 595291 598863 := bstep (se 1 (by rfl) ⟨449147, by rfl⟩ : syracuseStep 598863 = 898295) B898295
theorem B598879 : Blo 595291 598879 := bstep (se 1 (by rfl) ⟨449159, by rfl⟩ : syracuseStep 598879 = 898319) B898319
theorem B893801 : Blo 595291 893801 := bstep (se 2 (by rfl) ⟨335175, by rfl⟩ : syracuseStep 893801 = 670351) B670351
theorem B598907 : Blo 595291 598907 := bstep (se 1 (by rfl) ⟨449180, by rfl⟩ : syracuseStep 598907 = 898361) B898361
theorem B598959 : Blo 595291 598959 := bstep (se 1 (by rfl) ⟨449219, by rfl⟩ : syracuseStep 598959 = 898439) B898439
theorem B893879 : Blo 595291 893879 := bstep (se 1 (by rfl) ⟨670409, by rfl⟩ : syracuseStep 893879 = 1340819) B1340819
theorem B598983 : Blo 595291 598983 := bstep (se 1 (by rfl) ⟨449237, by rfl⟩ : syracuseStep 598983 = 898475) B898475
theorem B893915 : Blo 595291 893915 := bstep (se 1 (by rfl) ⟨670436, by rfl⟩ : syracuseStep 893915 = 1340873) B1340873
theorem B599003 : Blo 595291 599003 := bstep (se 1 (by rfl) ⟨449252, by rfl⟩ : syracuseStep 599003 = 898505) B898505
theorem B3023891 : Blo 595291 3023891 := bstep (se 1 (by rfl) ⟨2267918, by rfl⟩ : syracuseStep 3023891 = 4535837) B4535837
theorem B2270227 : Blo 595291 2270227 := bstep (se 1 (by rfl) ⟨1702670, by rfl⟩ : syracuseStep 2270227 = 3405341) B3405341
theorem B599079 : Blo 595291 599079 := bstep (se 1 (by rfl) ⟨449309, by rfl⟩ : syracuseStep 599079 = 898619) B898619
theorem B599119 : Blo 595291 599119 := bstep (se 1 (by rfl) ⟨449339, by rfl⟩ : syracuseStep 599119 = 898679) B898679
theorem B599135 : Blo 595291 599135 := bstep (se 1 (by rfl) ⟨449351, by rfl⟩ : syracuseStep 599135 = 898703) B898703
theorem B599163 : Blo 595291 599163 := bstep (se 1 (by rfl) ⟨449372, by rfl⟩ : syracuseStep 599163 = 898745) B898745
theorem B1516715 : Blo 595291 1516715 := bstep (se 1 (by rfl) ⟨1137536, by rfl⟩ : syracuseStep 1516715 = 2275073) B2275073
theorem B599215 : Blo 595291 599215 := bstep (se 1 (by rfl) ⟨449411, by rfl⟩ : syracuseStep 599215 = 898823) B898823
theorem B599239 : Blo 595291 599239 := bstep (se 1 (by rfl) ⟨449429, by rfl⟩ : syracuseStep 599239 = 898859) B898859
theorem B599259 : Blo 595291 599259 := bstep (se 1 (by rfl) ⟨449444, by rfl⟩ : syracuseStep 599259 = 898889) B898889
theorem B894383 : Blo 595291 894383 := bstep (se 1 (by rfl) ⟨670787, by rfl⟩ : syracuseStep 894383 = 1341575) B1341575
theorem B4597211 : Blo 595291 4597211 := bstep (se 1 (by rfl) ⟨3447908, by rfl⟩ : syracuseStep 4597211 = 6895817) B6895817
theorem B4597235 : Blo 595291 4597235 := bstep (se 1 (by rfl) ⟨3447926, by rfl⟩ : syracuseStep 4597235 = 6895853) B6895853
theorem B894473 : Blo 595291 894473 := bstep (se 2 (by rfl) ⟨335427, by rfl⟩ : syracuseStep 894473 = 670855) B670855
theorem B894503 : Blo 595291 894503 := bstep (se 1 (by rfl) ⟨670877, by rfl⟩ : syracuseStep 894503 = 1341755) B1341755
theorem B894587 : Blo 595291 894587 := bstep (se 1 (by rfl) ⟨670940, by rfl⟩ : syracuseStep 894587 = 1341881) B1341881
theorem B4531949 : Blo 595291 4531949 := bstep (se 3 (by rfl) ⟨849740, by rfl⟩ : syracuseStep 4531949 = 1699481) B1699481
theorem B894713 : Blo 595291 894713 := bstep (se 2 (by rfl) ⟨335517, by rfl⟩ : syracuseStep 894713 = 671035) B671035
theorem B894815 : Blo 595291 894815 := bstep (se 1 (by rfl) ⟨671111, by rfl⟩ : syracuseStep 894815 = 1342223) B1342223
theorem B894827 : Blo 595291 894827 := bstep (se 1 (by rfl) ⟨671120, by rfl⟩ : syracuseStep 894827 = 1342241) B1342241
theorem B3057517 : Blo 595291 3057517 := bstep (se 3 (by rfl) ⟨573284, by rfl⟩ : syracuseStep 3057517 = 1146569) B1146569
theorem B1812385 : Blo 595291 1812385 := bstep (se 2 (by rfl) ⟨679644, by rfl⟩ : syracuseStep 1812385 = 1359289) B1359289
theorem B895055 : Blo 595291 895055 := bstep (se 1 (by rfl) ⟨671291, by rfl⟩ : syracuseStep 895055 = 1342583) B1342583
theorem B895175 : Blo 595291 895175 := bstep (se 1 (by rfl) ⟨671381, by rfl⟩ : syracuseStep 895175 = 1342763) B1342763
theorem B895337 : Blo 595291 895337 := bstep (se 2 (by rfl) ⟨335751, by rfl⟩ : syracuseStep 895337 = 671503) B671503
theorem B895415 : Blo 595291 895415 := bstep (se 1 (by rfl) ⟨671561, by rfl⟩ : syracuseStep 895415 = 1343123) B1343123
theorem B895451 : Blo 595291 895451 := bstep (se 1 (by rfl) ⟨671588, by rfl⟩ : syracuseStep 895451 = 1343177) B1343177
theorem B2009609 : Blo 595291 2009609 := bstep (se 2 (by rfl) ⟨753603, by rfl⟩ : syracuseStep 2009609 = 1507207) B1507207
theorem B1911431 : Blo 595291 1911431 := bstep (se 1 (by rfl) ⟨1433573, by rfl⟩ : syracuseStep 1911431 = 2867147) B2867147
theorem B4532921 : Blo 595291 4532921 := bstep (se 2 (by rfl) ⟨1699845, by rfl⟩ : syracuseStep 4532921 = 3399691) B3399691
theorem B2271959 : Blo 595291 2271959 := bstep (se 1 (by rfl) ⟨1703969, by rfl⟩ : syracuseStep 2271959 = 3407939) B3407939
theorem B3058505 : Blo 595291 3058505 := bstep (se 2 (by rfl) ⟨1146939, by rfl⟩ : syracuseStep 3058505 = 2293879) B2293879
theorem B2304929 : Blo 595291 2304929 := bstep (se 2 (by rfl) ⟨864348, by rfl⟩ : syracuseStep 2304929 = 1728697) B1728697
theorem B895919 : Blo 595291 895919 := bstep (se 1 (by rfl) ⟨671939, by rfl⟩ : syracuseStep 895919 = 1343879) B1343879
theorem B1911815 : Blo 595291 1911815 := bstep (se 1 (by rfl) ⟨1433861, by rfl⟩ : syracuseStep 1911815 = 2867723) B2867723
theorem B896009 : Blo 595291 896009 := bstep (se 2 (by rfl) ⟨336003, by rfl⟩ : syracuseStep 896009 = 672007) B672007
theorem B896039 : Blo 595291 896039 := bstep (se 1 (by rfl) ⟨672029, by rfl⟩ : syracuseStep 896039 = 1344059) B1344059
theorem B896123 : Blo 595291 896123 := bstep (se 1 (by rfl) ⟨672092, by rfl⟩ : syracuseStep 896123 = 1344185) B1344185
theorem B4304119 : Blo 595291 4304119 := bstep (se 1 (by rfl) ⟨3228089, by rfl⟩ : syracuseStep 4304119 = 6456179) B6456179
theorem B896249 : Blo 595291 896249 := bstep (se 2 (by rfl) ⟨336093, by rfl⟩ : syracuseStep 896249 = 672187) B672187
theorem B896351 : Blo 595291 896351 := bstep (se 1 (by rfl) ⟨672263, by rfl⟩ : syracuseStep 896351 = 1344527) B1344527
theorem B2010473 : Blo 595291 2010473 := bstep (se 2 (by rfl) ⟨753927, by rfl⟩ : syracuseStep 2010473 = 1507855) B1507855
theorem B896363 : Blo 595291 896363 := bstep (se 1 (by rfl) ⟨672272, by rfl⟩ : syracuseStep 896363 = 1344545) B1344545
theorem B896591 : Blo 595291 896591 := bstep (se 1 (by rfl) ⟨672443, by rfl⟩ : syracuseStep 896591 = 1344887) B1344887
theorem B4533893 : Blo 595291 4533893 := bstep (se 4 (by rfl) ⟨425052, by rfl⟩ : syracuseStep 4533893 = 850105) B850105
theorem B896711 : Blo 595291 896711 := bstep (se 1 (by rfl) ⟨672533, by rfl⟩ : syracuseStep 896711 = 1345067) B1345067
theorem B896873 : Blo 595291 896873 := bstep (se 2 (by rfl) ⟨336327, by rfl⟩ : syracuseStep 896873 = 672655) B672655
theorem B3026807 : Blo 595291 3026807 := bstep (se 1 (by rfl) ⟨2270105, by rfl⟩ : syracuseStep 3026807 = 4540211) B4540211
theorem B2273143 : Blo 595291 2273143 := bstep (se 1 (by rfl) ⟨1704857, by rfl⟩ : syracuseStep 2273143 = 3409715) B3409715
theorem B896951 : Blo 595291 896951 := bstep (se 1 (by rfl) ⟨672713, by rfl⟩ : syracuseStep 896951 = 1345427) B1345427
theorem B2011067 : Blo 595291 2011067 := bstep (se 1 (by rfl) ⟨1508300, by rfl⟩ : syracuseStep 2011067 = 3016601) B3016601
theorem B896987 : Blo 595291 896987 := bstep (se 1 (by rfl) ⟨672740, by rfl⟩ : syracuseStep 896987 = 1345481) B1345481
theorem B4829489 : Blo 595291 4829489 := bstep (se 2 (by rfl) ⟨1811058, by rfl⟩ : syracuseStep 4829489 = 3622117) B3622117
theorem B897455 : Blo 595291 897455 := bstep (se 1 (by rfl) ⟨673091, by rfl⟩ : syracuseStep 897455 = 1346183) B1346183
theorem B897545 : Blo 595291 897545 := bstep (se 2 (by rfl) ⟨336579, by rfl⟩ : syracuseStep 897545 = 673159) B673159
theorem B897575 : Blo 595291 897575 := bstep (se 1 (by rfl) ⟨673181, by rfl⟩ : syracuseStep 897575 = 1346363) B1346363
theorem B897659 : Blo 595291 897659 := bstep (se 1 (by rfl) ⟨673244, by rfl⟩ : syracuseStep 897659 = 1346489) B1346489
theorem B897785 : Blo 595291 897785 := bstep (se 2 (by rfl) ⟨336669, by rfl⟩ : syracuseStep 897785 = 673339) B673339
theorem B29012741 : Blo 595291 29012741 := bstep (se 4 (by rfl) ⟨2719944, by rfl⟩ : syracuseStep 29012741 = 5439889) B5439889
theorem B2274115 : Blo 595291 2274115 := bstep (se 1 (by rfl) ⟨1705586, by rfl⟩ : syracuseStep 2274115 = 3411173) B3411173
theorem B897887 : Blo 595291 897887 := bstep (se 1 (by rfl) ⟨673415, by rfl⟩ : syracuseStep 897887 = 1346831) B1346831
theorem B897899 : Blo 595291 897899 := bstep (se 1 (by rfl) ⟨673424, by rfl⟩ : syracuseStep 897899 = 1346849) B1346849
theorem B898127 : Blo 595291 898127 := bstep (se 1 (by rfl) ⟨673595, by rfl⟩ : syracuseStep 898127 = 1347191) B1347191
theorem B2274419 : Blo 595291 2274419 := bstep (se 1 (by rfl) ⟨1705814, by rfl⟩ : syracuseStep 2274419 = 3411629) B3411629
theorem B898247 : Blo 595291 898247 := bstep (se 1 (by rfl) ⟨673685, by rfl⟩ : syracuseStep 898247 = 1347371) B1347371
theorem B898409 : Blo 595291 898409 := bstep (se 2 (by rfl) ⟨336903, by rfl⟩ : syracuseStep 898409 = 673807) B673807
theorem B2176381 : Blo 595291 2176381 := bstep (se 3 (by rfl) ⟨408071, by rfl⟩ : syracuseStep 2176381 = 816143) B816143
theorem B898487 : Blo 595291 898487 := bstep (se 1 (by rfl) ⟨673865, by rfl⟩ : syracuseStep 898487 = 1347731) B1347731
theorem B898523 : Blo 595291 898523 := bstep (se 1 (by rfl) ⟨673892, by rfl⟩ : syracuseStep 898523 = 1347785) B1347785
theorem B2274875 : Blo 595291 2274875 := bstep (se 1 (by rfl) ⟨1706156, by rfl⟩ : syracuseStep 2274875 = 3412313) B3412313
theorem B2012795 : Blo 595291 2012795 := bstep (se 1 (by rfl) ⟨1509596, by rfl⟩ : syracuseStep 2012795 = 3019193) B3019193
theorem B2012957 : Blo 595291 2012957 := bstep (se 3 (by rfl) ⟨377429, by rfl⟩ : syracuseStep 2012957 = 754859) B754859
theorem B1816507 : Blo 595291 1816507 := bstep (se 1 (by rfl) ⟨1362380, by rfl⟩ : syracuseStep 1816507 = 2724761) B2724761
theorem B4536323 : Blo 595291 4536323 := bstep (se 1 (by rfl) ⟨3402242, by rfl⟩ : syracuseStep 4536323 = 6804485) B6804485
theorem B5453831 : Blo 595291 5453831 := bstep (se 1 (by rfl) ⟨4090373, by rfl⟩ : syracuseStep 5453831 = 8180747) B8180747
theorem B669775 : Blo 595291 669775 := bstep (se 1 (by rfl) ⟨502331, by rfl⟩ : syracuseStep 669775 = 1004663) B1004663
theorem B3225757 : Blo 595291 3225757 := bstep (se 3 (by rfl) ⟨604829, by rfl⟩ : syracuseStep 3225757 = 1209659) B1209659
theorem B5093765 : Blo 595291 5093765 := bstep (se 4 (by rfl) ⟨477540, by rfl⟩ : syracuseStep 5093765 = 955081) B955081
theorem B670171 : Blo 595291 670171 := bstep (se 1 (by rfl) ⟨502628, by rfl⟩ : syracuseStep 670171 = 1005257) B1005257
theorem B2013659 : Blo 595291 2013659 := bstep (se 1 (by rfl) ⟨1510244, by rfl⟩ : syracuseStep 2013659 = 3020489) B3020489
theorem B1915607 : Blo 595291 1915607 := bstep (se 1 (by rfl) ⟨1436705, by rfl⟩ : syracuseStep 1915607 = 2873411) B2873411
theorem B4209515 : Blo 595291 4209515 := bstep (se 1 (by rfl) ⟨3157136, by rfl⟩ : syracuseStep 4209515 = 6314273) B6314273
theorem B670639 : Blo 595291 670639 := bstep (se 1 (by rfl) ⟨502979, by rfl⟩ : syracuseStep 670639 = 1005959) B1005959
theorem B2014361 : Blo 595291 2014361 := bstep (se 2 (by rfl) ⟨755385, by rfl⟩ : syracuseStep 2014361 = 1510771) B1510771
theorem B671071 : Blo 595291 671071 := bstep (se 1 (by rfl) ⟨503303, by rfl⟩ : syracuseStep 671071 = 1006607) B1006607
theorem B638587 : Blo 595291 638587 := bstep (se 1 (by rfl) ⟨478940, by rfl⟩ : syracuseStep 638587 = 957881) B957881
theorem B2866877 : Blo 595291 2866877 := bstep (se 3 (by rfl) ⟨537539, by rfl⟩ : syracuseStep 2866877 = 1075079) B1075079
theorem B3456701 : Blo 595291 3456701 := bstep (se 3 (by rfl) ⟨648131, by rfl⟩ : syracuseStep 3456701 = 1296263) B1296263
theorem B671431 : Blo 595291 671431 := bstep (se 1 (by rfl) ⟨503573, by rfl⟩ : syracuseStep 671431 = 1007147) B1007147
theorem B1130345 : Blo 595291 1130345 := bstep (se 2 (by rfl) ⟨423879, by rfl⟩ : syracuseStep 1130345 = 847759) B847759
theorem B2015549 : Blo 595291 2015549 := bstep (se 3 (by rfl) ⟨377915, by rfl⟩ : syracuseStep 2015549 = 755831) B755831
theorem B4538753 : Blo 595291 4538753 := bstep (se 2 (by rfl) ⟨1702032, by rfl⟩ : syracuseStep 4538753 = 3404065) B3404065
theorem B672295 : Blo 595291 672295 := bstep (se 1 (by rfl) ⟨504221, by rfl⟩ : syracuseStep 672295 = 1008443) B1008443
theorem B5456747 : Blo 595291 5456747 := bstep (se 1 (by rfl) ⟨4092560, by rfl⟩ : syracuseStep 5456747 = 8185121) B8185121
theorem B15352739 : Blo 595291 15352739 := bstep (se 1 (by rfl) ⟨11514554, by rfl⟩ : syracuseStep 15352739 = 23029109) B23029109
theorem B3031991 : Blo 595291 3031991 := bstep (se 1 (by rfl) ⟨2273993, by rfl⟩ : syracuseStep 3031991 = 4547987) B4547987
theorem B2016413 : Blo 595291 2016413 := bstep (se 3 (by rfl) ⟨378077, by rfl⟩ : syracuseStep 2016413 = 756155) B756155
theorem B13780523 : Blo 595291 13780523 := bstep (se 1 (by rfl) ⟨10335392, by rfl⟩ : syracuseStep 13780523 = 20670785) B20670785
theorem B3819095 : Blo 595291 3819095 := bstep (se 1 (by rfl) ⟨2864321, by rfl⟩ : syracuseStep 3819095 = 5728643) B5728643
theorem B10208915 : Blo 595291 10208915 := bstep (se 1 (by rfl) ⟨7656686, by rfl⟩ : syracuseStep 10208915 = 15313373) B15313373
theorem B2016953 : Blo 595291 2016953 := bstep (se 2 (by rfl) ⟨756357, by rfl⟩ : syracuseStep 2016953 = 1512715) B1512715
theorem B804601 : Blo 595291 804601 := bstep (se 2 (by rfl) ⟨301725, by rfl⟩ : syracuseStep 804601 = 603451) B603451
theorem B2049785 : Blo 595291 2049785 := bstep (se 2 (by rfl) ⟨768669, by rfl⟩ : syracuseStep 2049785 = 1537339) B1537339
theorem B3622751 : Blo 595291 3622751 := bstep (se 1 (by rfl) ⟨2717063, by rfl⟩ : syracuseStep 3622751 = 5434127) B5434127
theorem B1132471 : Blo 595291 1132471 := bstep (se 1 (by rfl) ⟨849353, by rfl⟩ : syracuseStep 1132471 = 1698707) B1698707
theorem B1918991 : Blo 595291 1918991 := bstep (se 1 (by rfl) ⟨1439243, by rfl⟩ : syracuseStep 1918991 = 2878487) B2878487
theorem B2869337 : Blo 595291 2869337 := bstep (se 2 (by rfl) ⟨1076001, by rfl⟩ : syracuseStep 2869337 = 2152003) B2152003
theorem B673915 : Blo 595291 673915 := bstep (se 1 (by rfl) ⟨505436, by rfl⟩ : syracuseStep 673915 = 1010873) B1010873
theorem B2017547 : Blo 595291 2017547 := bstep (se 1 (by rfl) ⟨1513160, by rfl⟩ : syracuseStep 2017547 = 3026321) B3026321
theorem B3033449 : Blo 595291 3033449 := bstep (se 2 (by rfl) ⟨1137543, by rfl⟩ : syracuseStep 3033449 = 2275087) B2275087
theorem B3230081 : Blo 595291 3230081 := bstep (se 2 (by rfl) ⟨1211280, by rfl⟩ : syracuseStep 3230081 = 2422561) B2422561
theorem B2017817 : Blo 595291 2017817 := bstep (se 2 (by rfl) ⟨756681, by rfl⟩ : syracuseStep 2017817 = 1513363) B1513363
theorem B2214611 : Blo 595291 2214611 := bstep (se 1 (by rfl) ⟨1660958, by rfl⟩ : syracuseStep 2214611 = 3321917) B3321917
theorem B805807 : Blo 595291 805807 := bstep (se 1 (by rfl) ⟨604355, by rfl⟩ : syracuseStep 805807 = 1208711) B1208711
theorem B2247875 : Blo 595291 2247875 := bstep (se 1 (by rfl) ⟨1685906, by rfl⟩ : syracuseStep 2247875 = 3371813) B3371813
theorem B1133929 : Blo 595291 1133929 := bstep (se 2 (by rfl) ⟨425223, by rfl⟩ : syracuseStep 1133929 = 850447) B850447
theorem B2018951 : Blo 595291 2018951 := bstep (se 1 (by rfl) ⟨1514213, by rfl⟩ : syracuseStep 2018951 = 3028427) B3028427
theorem B2019005 : Blo 595291 2019005 := bstep (se 3 (by rfl) ⟨378563, by rfl⟩ : syracuseStep 2019005 = 757127) B757127
theorem B2019167 : Blo 595291 2019167 := bstep (se 1 (by rfl) ⟨1514375, by rfl⟩ : syracuseStep 2019167 = 3028751) B3028751
theorem B2019329 : Blo 595291 2019329 := bstep (se 2 (by rfl) ⟨757248, by rfl⟩ : syracuseStep 2019329 = 1514497) B1514497
theorem B3395591 : Blo 595291 3395591 := bstep (se 1 (by rfl) ⟨2546693, by rfl⟩ : syracuseStep 3395591 = 5093387) B5093387
theorem B1134803 : Blo 595291 1134803 := bstep (se 1 (by rfl) ⟨851102, by rfl⟩ : syracuseStep 1134803 = 1702205) B1702205
theorem B14373179 : Blo 595291 14373179 := bstep (se 1 (by rfl) ⟨10779884, by rfl⟩ : syracuseStep 14373179 = 21559769) B21559769
theorem B5460689 : Blo 595291 5460689 := bstep (se 2 (by rfl) ⟨2047758, by rfl⟩ : syracuseStep 5460689 = 4095517) B4095517
theorem B2020139 : Blo 595291 2020139 := bstep (se 1 (by rfl) ⟨1515104, by rfl⟩ : syracuseStep 2020139 = 3030209) B3030209
theorem B1135433 : Blo 595291 1135433 := bstep (se 2 (by rfl) ⟨425787, by rfl⟩ : syracuseStep 1135433 = 851575) B851575
theorem B2020409 : Blo 595291 2020409 := bstep (se 2 (by rfl) ⟨757653, by rfl⟩ : syracuseStep 2020409 = 1515307) B1515307
theorem B3822785 : Blo 595291 3822785 := bstep (se 2 (by rfl) ⟨1433544, by rfl⟩ : syracuseStep 3822785 = 2867089) B2867089
theorem B1004791 : Blo 595291 1004791 := bstep (se 1 (by rfl) ⟨753593, by rfl⟩ : syracuseStep 1004791 = 1507187) B1507187
theorem B2020733 : Blo 595291 2020733 := bstep (se 3 (by rfl) ⟨378887, by rfl⟩ : syracuseStep 2020733 = 757775) B757775
theorem B3823013 : Blo 595291 3823013 := bstep (se 4 (by rfl) ⟨358407, by rfl⟩ : syracuseStep 3823013 = 716815) B716815
theorem B808375 : Blo 595291 808375 := bstep (se 1 (by rfl) ⟨606281, by rfl⟩ : syracuseStep 808375 = 1212563) B1212563
theorem B1004987 : Blo 595291 1004987 := bstep (se 1 (by rfl) ⟨753740, by rfl⟩ : syracuseStep 1004987 = 1507481) B1507481
theorem B1005095 : Blo 595291 1005095 := bstep (se 1 (by rfl) ⟨753821, by rfl⟩ : syracuseStep 1005095 = 1507643) B1507643
theorem B1136207 : Blo 595291 1136207 := bstep (se 1 (by rfl) ⟨852155, by rfl⟩ : syracuseStep 1136207 = 1704311) B1704311
theorem B3888737 : Blo 595291 3888737 := bstep (se 2 (by rfl) ⟨1458276, by rfl⟩ : syracuseStep 3888737 = 2916553) B2916553
theorem B2021003 : Blo 595291 2021003 := bstep (se 1 (by rfl) ⟨1515752, by rfl⟩ : syracuseStep 2021003 = 3031505) B3031505
theorem B972535 : Blo 595291 972535 := bstep (se 1 (by rfl) ⟨729401, by rfl⟩ : syracuseStep 972535 = 1458803) B1458803
theorem B1005385 : Blo 595291 1005385 := bstep (se 2 (by rfl) ⟨377019, by rfl⟩ : syracuseStep 1005385 = 754039) B754039
theorem B1005419 : Blo 595291 1005419 := bstep (se 1 (by rfl) ⟨754064, by rfl⟩ : syracuseStep 1005419 = 1508129) B1508129
theorem B8148995 : Blo 595291 8148995 := bstep (se 1 (by rfl) ⟨6111746, by rfl⟩ : syracuseStep 8148995 = 12223493) B12223493
theorem B26171437 : Blo 595291 26171437 := bstep (se 3 (by rfl) ⟨4907144, by rfl⟩ : syracuseStep 26171437 = 9814289) B9814289
theorem B1431631 : Blo 595291 1431631 := bstep (se 1 (by rfl) ⟨1073723, by rfl⟩ : syracuseStep 1431631 = 2147447) B2147447
theorem B1005817 : Blo 595291 1005817 := bstep (se 2 (by rfl) ⟨377181, by rfl⟩ : syracuseStep 1005817 = 754363) B754363
theorem B1006087 : Blo 595291 1006087 := bstep (se 1 (by rfl) ⟨754565, by rfl⟩ : syracuseStep 1006087 = 1509131) B1509131
theorem B2021921 : Blo 595291 2021921 := bstep (se 2 (by rfl) ⟨758220, by rfl⟩ : syracuseStep 2021921 = 1516441) B1516441
theorem B2546387 : Blo 595291 2546387 := bstep (se 1 (by rfl) ⟨1909790, by rfl⟩ : syracuseStep 2546387 = 3819581) B3819581
theorem B2022137 : Blo 595291 2022137 := bstep (se 2 (by rfl) ⟨758301, by rfl⟩ : syracuseStep 2022137 = 1516603) B1516603
theorem B1366777 : Blo 595291 1366777 := bstep (se 2 (by rfl) ⟨512541, by rfl⟩ : syracuseStep 1366777 = 1025083) B1025083
theorem B3398507 : Blo 595291 3398507 := bstep (se 1 (by rfl) ⟨2548880, by rfl⟩ : syracuseStep 3398507 = 5097761) B5097761
theorem B1006519 : Blo 595291 1006519 := bstep (se 1 (by rfl) ⟨754889, by rfl⟩ : syracuseStep 1006519 = 1509779) B1509779
theorem B2022407 : Blo 595291 2022407 := bstep (se 1 (by rfl) ⟨1516805, by rfl⟩ : syracuseStep 2022407 = 3033611) B3033611
theorem B2022515 : Blo 595291 2022515 := bstep (se 1 (by rfl) ⟨1516886, by rfl⟩ : syracuseStep 2022515 = 3033773) B3033773
theorem B1006715 : Blo 595291 1006715 := bstep (se 1 (by rfl) ⟨755036, by rfl⟩ : syracuseStep 1006715 = 1510073) B1510073
theorem B4611275 : Blo 595291 4611275 := bstep (se 1 (by rfl) ⟨3458456, by rfl⟩ : syracuseStep 4611275 = 6916913) B6916913
theorem B2874797 : Blo 595291 2874797 := bstep (se 3 (by rfl) ⟨539024, by rfl⟩ : syracuseStep 2874797 = 1078049) B1078049
theorem B1007113 : Blo 595291 1007113 := bstep (se 2 (by rfl) ⟨377667, by rfl⟩ : syracuseStep 1007113 = 755335) B755335
theorem B1007275 : Blo 595291 1007275 := bstep (se 1 (by rfl) ⟨755456, by rfl⟩ : syracuseStep 1007275 = 1510913) B1510913
theorem B1728211 : Blo 595291 1728211 := bstep (se 1 (by rfl) ⟨1296158, by rfl⟩ : syracuseStep 1728211 = 2592317) B2592317
theorem B2875297 : Blo 595291 2875297 := bstep (se 2 (by rfl) ⟨1078236, by rfl⟩ : syracuseStep 2875297 = 2156473) B2156473
theorem B1073083 : Blo 595291 1073083 := bstep (se 1 (by rfl) ⟨804812, by rfl⟩ : syracuseStep 1073083 = 1609625) B1609625
theorem B1007579 : Blo 595291 1007579 := bstep (se 1 (by rfl) ⟨755684, by rfl⟩ : syracuseStep 1007579 = 1511369) B1511369
theorem B2547719 : Blo 595291 2547719 := bstep (se 1 (by rfl) ⟨1910789, by rfl⟩ : syracuseStep 2547719 = 3821579) B3821579
theorem B6447185 : Blo 595291 6447185 := bstep (se 2 (by rfl) ⟨2417694, by rfl⟩ : syracuseStep 6447185 = 4835389) B4835389
theorem B1007815 : Blo 595291 1007815 := bstep (se 1 (by rfl) ⟨755861, by rfl⟩ : syracuseStep 1007815 = 1511723) B1511723
theorem B1007977 : Blo 595291 1007977 := bstep (se 2 (by rfl) ⟨377991, by rfl⟩ : syracuseStep 1007977 = 755983) B755983
theorem B3400217 : Blo 595291 3400217 := bstep (se 2 (by rfl) ⟨1275081, by rfl⟩ : syracuseStep 3400217 = 2550163) B2550163
theorem B1434323 : Blo 595291 1434323 := bstep (se 1 (by rfl) ⟨1075742, by rfl⟩ : syracuseStep 1434323 = 2151485) B2151485
theorem B1434361 : Blo 595291 1434361 := bstep (se 2 (by rfl) ⟨537885, by rfl⟩ : syracuseStep 1434361 = 1075771) B1075771
theorem B1008571 : Blo 595291 1008571 := bstep (se 1 (by rfl) ⟨756428, by rfl⟩ : syracuseStep 1008571 = 1512857) B1512857
theorem B9659357 : Blo 595291 9659357 := bstep (se 3 (by rfl) ⟨1811129, by rfl⟩ : syracuseStep 9659357 = 3622259) B3622259
theorem B1074185 : Blo 595291 1074185 := bstep (se 2 (by rfl) ⟨402819, by rfl⟩ : syracuseStep 1074185 = 805639) B805639
theorem B1008679 : Blo 595291 1008679 := bstep (se 1 (by rfl) ⟨756509, by rfl⟩ : syracuseStep 1008679 = 1513019) B1513019
theorem B1009003 : Blo 595291 1009003 := bstep (se 1 (by rfl) ⟨756752, by rfl⟩ : syracuseStep 1009003 = 1513505) B1513505
theorem B1860989 : Blo 595291 1860989 := bstep (se 3 (by rfl) ⟨348935, by rfl⟩ : syracuseStep 1860989 = 697871) B697871
theorem B1435553 : Blo 595291 1435553 := bstep (se 2 (by rfl) ⟨538332, by rfl⟩ : syracuseStep 1435553 = 1076665) B1076665
theorem B1010063 : Blo 595291 1010063 := bstep (se 1 (by rfl) ⟨757547, by rfl⟩ : syracuseStep 1010063 = 1515095) B1515095
theorem B1010299 : Blo 595291 1010299 := bstep (se 1 (by rfl) ⟨757724, by rfl⟩ : syracuseStep 1010299 = 1515449) B1515449
theorem B3402425 : Blo 595291 3402425 := bstep (se 2 (by rfl) ⟨1275909, by rfl⟩ : syracuseStep 3402425 = 2551819) B2551819
theorem B5106509 : Blo 595291 5106509 := bstep (se 3 (by rfl) ⟨957470, by rfl⟩ : syracuseStep 5106509 = 1914941) B1914941
theorem B3403133 : Blo 595291 3403133 := bstep (se 3 (by rfl) ⟨638087, by rfl⟩ : syracuseStep 3403133 = 1276175) B1276175
theorem B1011163 : Blo 595291 1011163 := bstep (se 1 (by rfl) ⟨758372, by rfl⟩ : syracuseStep 1011163 = 1516745) B1516745
theorem B2158289 : Blo 595291 2158289 := bstep (se 2 (by rfl) ⟨809358, by rfl⟩ : syracuseStep 2158289 = 1618717) B1618717
theorem B4091681 : Blo 595291 4091681 := bstep (se 2 (by rfl) ⟨1534380, by rfl⟩ : syracuseStep 4091681 = 3068761) B3068761
theorem B9170819 : Blo 595291 9170819 := bstep (se 1 (by rfl) ⟨6878114, by rfl⟩ : syracuseStep 9170819 = 13756229) B13756229
theorem B17166653 : Blo 595291 17166653 := bstep (se 3 (by rfl) ⟨3218747, by rfl⟩ : syracuseStep 17166653 = 6437495) B6437495
theorem B6451771 : Blo 595291 6451771 := bstep (se 1 (by rfl) ⟨4838828, by rfl⟩ : syracuseStep 6451771 = 9677657) B9677657
theorem B9826915 : Blo 595291 9826915 := bstep (se 1 (by rfl) ⟨7370186, by rfl⟩ : syracuseStep 9826915 = 14740373) B14740373
theorem B1340027 : Blo 595291 1340027 := bstep (se 1 (by rfl) ⟨1005020, by rfl⟩ : syracuseStep 1340027 = 2010041) B2010041
theorem B2159243 : Blo 595291 2159243 := bstep (se 1 (by rfl) ⟨1619432, by rfl⟩ : syracuseStep 2159243 = 3238865) B3238865
theorem B1340153 : Blo 595291 1340153 := bstep (se 2 (by rfl) ⟨502557, by rfl⟩ : syracuseStep 1340153 = 1005115) B1005115
theorem B9433907 : Blo 595291 9433907 := bstep (se 1 (by rfl) ⟨7075430, by rfl⟩ : syracuseStep 9433907 = 14150861) B14150861
theorem B1340423 : Blo 595291 1340423 := bstep (se 1 (by rfl) ⟨1005317, by rfl⟩ : syracuseStep 1340423 = 2010635) B2010635
theorem B1340495 : Blo 595291 1340495 := bstep (se 1 (by rfl) ⟨1005371, by rfl⟩ : syracuseStep 1340495 = 2010743) B2010743
theorem B1340891 : Blo 595291 1340891 := bstep (se 1 (by rfl) ⟨1005668, by rfl⟩ : syracuseStep 1340891 = 2011337) B2011337
theorem B1275355 : Blo 595291 1275355 := bstep (se 1 (by rfl) ⟨956516, by rfl⟩ : syracuseStep 1275355 = 1913033) B1913033
theorem B1275431 : Blo 595291 1275431 := bstep (se 1 (by rfl) ⟨956573, by rfl⟩ : syracuseStep 1275431 = 1913147) B1913147
theorem B7665299 : Blo 595291 7665299 := bstep (se 1 (by rfl) ⟨5748974, by rfl⟩ : syracuseStep 7665299 = 11497949) B11497949
theorem B1341359 : Blo 595291 1341359 := bstep (se 1 (by rfl) ⟨1006019, by rfl⟩ : syracuseStep 1341359 = 2012039) B2012039
theorem B1341611 : Blo 595291 1341611 := bstep (se 1 (by rfl) ⟨1006208, by rfl⟩ : syracuseStep 1341611 = 2012417) B2012417
theorem B1079657 : Blo 595291 1079657 := bstep (se 2 (by rfl) ⟨404871, by rfl⟩ : syracuseStep 1079657 = 809743) B809743
theorem B3832217 : Blo 595291 3832217 := bstep (se 2 (by rfl) ⟨1437081, by rfl⟩ : syracuseStep 3832217 = 2874163) B2874163
theorem B3832343 : Blo 595291 3832343 := bstep (se 1 (by rfl) ⟨2874257, by rfl⟩ : syracuseStep 3832343 = 5748515) B5748515
theorem B2554553 : Blo 595291 2554553 := bstep (se 2 (by rfl) ⟨957957, by rfl⟩ : syracuseStep 2554553 = 1915915) B1915915
theorem B1342151 : Blo 595291 1342151 := bstep (se 1 (by rfl) ⟨1006613, by rfl⟩ : syracuseStep 1342151 = 2013227) B2013227
theorem B8616779 : Blo 595291 8616779 := bstep (se 1 (by rfl) ⟨6462584, by rfl⟩ : syracuseStep 8616779 = 12925169) B12925169
theorem B1276859 : Blo 595291 1276859 := bstep (se 1 (by rfl) ⟨957644, by rfl⟩ : syracuseStep 1276859 = 1915289) B1915289
theorem B1211411 : Blo 595291 1211411 := bstep (se 1 (by rfl) ⟨908558, by rfl⟩ : syracuseStep 1211411 = 1817117) B1817117
theorem B29359655 : Blo 595291 29359655 := bstep (se 1 (by rfl) ⟨22019741, by rfl⟩ : syracuseStep 29359655 = 44039483) B44039483
theorem B1343015 : Blo 595291 1343015 := bstep (se 1 (by rfl) ⟨1007261, by rfl⟩ : syracuseStep 1343015 = 2014523) B2014523
theorem B3407507 : Blo 595291 3407507 := bstep (se 1 (by rfl) ⟨2555630, by rfl⟩ : syracuseStep 3407507 = 5111261) B5111261
theorem B3014333 : Blo 595291 3014333 := bstep (se 3 (by rfl) ⟨565187, by rfl⟩ : syracuseStep 3014333 = 1130375) B1130375
theorem B2293571 : Blo 595291 2293571 := bstep (se 1 (by rfl) ⟨1720178, by rfl⟩ : syracuseStep 2293571 = 3440357) B3440357
theorem B3014495 : Blo 595291 3014495 := bstep (se 1 (by rfl) ⟨2260871, by rfl⟩ : syracuseStep 3014495 = 4521743) B4521743
theorem B1343339 : Blo 595291 1343339 := bstep (se 1 (by rfl) ⟨1007504, by rfl⟩ : syracuseStep 1343339 = 2015009) B2015009
theorem B1343393 : Blo 595291 1343393 := bstep (se 2 (by rfl) ⟨503772, by rfl⟩ : syracuseStep 1343393 = 1007545) B1007545
theorem B1703855 : Blo 595291 1703855 := bstep (se 1 (by rfl) ⟨1277891, by rfl⟩ : syracuseStep 1703855 = 2555783) B2555783
theorem B3014657 : Blo 595291 3014657 := bstep (se 2 (by rfl) ⟨1130496, by rfl⟩ : syracuseStep 3014657 = 2260993) B2260993
theorem B1343699 : Blo 595291 1343699 := bstep (se 1 (by rfl) ⟨1007774, by rfl⟩ : syracuseStep 1343699 = 2015549) B2015549
theorem B1343753 : Blo 595291 1343753 := bstep (se 2 (by rfl) ⟨503907, by rfl⟩ : syracuseStep 1343753 = 1007815) B1007815
theorem B1343969 : Blo 595291 1343969 := bstep (se 2 (by rfl) ⟨503988, by rfl⟩ : syracuseStep 1343969 = 1007977) B1007977
theorem B1507835 : Blo 595291 1507835 := bstep (se 1 (by rfl) ⟨1130876, by rfl⟩ : syracuseStep 1507835 = 2261753) B2261753
theorem B3637831 : Blo 595291 3637831 := bstep (se 1 (by rfl) ⟨2728373, by rfl⟩ : syracuseStep 3637831 = 5456747) B5456747
theorem B1638983 : Blo 595291 1638983 := bstep (se 1 (by rfl) ⟨1229237, by rfl⟩ : syracuseStep 1638983 = 2458475) B2458475
theorem B1344275 : Blo 595291 1344275 := bstep (se 1 (by rfl) ⟨1008206, by rfl⟩ : syracuseStep 1344275 = 2016413) B2016413
theorem B3015467 : Blo 595291 3015467 := bstep (se 1 (by rfl) ⟨2261600, by rfl⟩ : syracuseStep 3015467 = 4523201) B4523201
theorem B5833619 : Blo 595291 5833619 := bstep (se 1 (by rfl) ⟨4375214, by rfl⟩ : syracuseStep 5833619 = 8750429) B8750429
theorem B1344635 : Blo 595291 1344635 := bstep (se 1 (by rfl) ⟨1008476, by rfl⟩ : syracuseStep 1344635 = 2016953) B2016953
theorem B1344761 : Blo 595291 1344761 := bstep (se 2 (by rfl) ⟨504285, by rfl⟩ : syracuseStep 1344761 = 1008571) B1008571
theorem B2557271 : Blo 595291 2557271 := bstep (se 1 (by rfl) ⟨1917953, by rfl⟩ : syracuseStep 2557271 = 3835907) B3835907
theorem B1279327 : Blo 595291 1279327 := bstep (se 1 (by rfl) ⟨959495, by rfl⟩ : syracuseStep 1279327 = 1918991) B1918991
theorem B918907 : Blo 595291 918907 := bstep (se 1 (by rfl) ⟨689180, by rfl⟩ : syracuseStep 918907 = 1378361) B1378361
theorem B1344905 : Blo 595291 1344905 := bstep (se 2 (by rfl) ⟨504339, by rfl⟩ : syracuseStep 1344905 = 1008679) B1008679
theorem B1508807 : Blo 595291 1508807 := bstep (se 1 (by rfl) ⟨1131605, by rfl⟩ : syracuseStep 1508807 = 2263211) B2263211
theorem B1345031 : Blo 595291 1345031 := bstep (se 1 (by rfl) ⟨1008773, by rfl⟩ : syracuseStep 1345031 = 2017547) B2017547
theorem B2426375 : Blo 595291 2426375 := bstep (se 1 (by rfl) ⟨1819781, by rfl⟩ : syracuseStep 2426375 = 3639563) B3639563
theorem B1345211 : Blo 595291 1345211 := bstep (se 1 (by rfl) ⟨1008908, by rfl⟩ : syracuseStep 1345211 = 2017817) B2017817
theorem B1476407 : Blo 595291 1476407 := bstep (se 1 (by rfl) ⟨1107305, by rfl⟩ : syracuseStep 1476407 = 2214611) B2214611
theorem B1345337 : Blo 595291 1345337 := bstep (se 2 (by rfl) ⟨504501, by rfl⟩ : syracuseStep 1345337 = 1009003) B1009003
theorem B1509587 : Blo 595291 1509587 := bstep (se 1 (by rfl) ⟨1132190, by rfl⟩ : syracuseStep 1509587 = 2264381) B2264381
theorem B1509799 : Blo 595291 1509799 := bstep (se 1 (by rfl) ⟨1132349, by rfl⟩ : syracuseStep 1509799 = 2264699) B2264699
theorem B1345967 : Blo 595291 1345967 := bstep (se 1 (by rfl) ⟨1009475, by rfl⟩ : syracuseStep 1345967 = 2018951) B2018951
theorem B1346003 : Blo 595291 1346003 := bstep (se 1 (by rfl) ⟨1009502, by rfl⟩ : syracuseStep 1346003 = 2019005) B2019005
theorem B1346111 : Blo 595291 1346111 := bstep (se 1 (by rfl) ⟨1009583, by rfl⟩ : syracuseStep 1346111 = 2019167) B2019167
theorem B1509961 : Blo 595291 1509961 := bstep (se 2 (by rfl) ⟨566235, by rfl⟩ : syracuseStep 1509961 = 1132471) B1132471
theorem B1346219 : Blo 595291 1346219 := bstep (se 1 (by rfl) ⟨1009664, by rfl⟩ : syracuseStep 1346219 = 2019329) B2019329
theorem B2263727 : Blo 595291 2263727 := bstep (se 1 (by rfl) ⟨1697795, by rfl⟩ : syracuseStep 2263727 = 3395591) B3395591
theorem B3017411 : Blo 595291 3017411 := bstep (se 1 (by rfl) ⟨2263058, by rfl⟩ : syracuseStep 3017411 = 4526117) B4526117
theorem B2951927 : Blo 595291 2951927 := bstep (se 1 (by rfl) ⟨2213945, by rfl⟩ : syracuseStep 2951927 = 4427891) B4427891
theorem B756535 : Blo 595291 756535 := bstep (se 1 (by rfl) ⟨567401, by rfl⟩ : syracuseStep 756535 = 1134803) B1134803
theorem B2427803 : Blo 595291 2427803 := bstep (se 1 (by rfl) ⟨1820852, by rfl⟩ : syracuseStep 2427803 = 3641705) B3641705
theorem B3640459 : Blo 595291 3640459 := bstep (se 1 (by rfl) ⟨2730344, by rfl⟩ : syracuseStep 3640459 = 5460689) B5460689
theorem B1346759 : Blo 595291 1346759 := bstep (se 1 (by rfl) ⟨1010069, by rfl⟩ : syracuseStep 1346759 = 2020139) B2020139
theorem B756955 : Blo 595291 756955 := bstep (se 1 (by rfl) ⟨567716, by rfl⟩ : syracuseStep 756955 = 1135433) B1135433
theorem B1510751 : Blo 595291 1510751 := bstep (se 1 (by rfl) ⟨1133063, by rfl⟩ : syracuseStep 1510751 = 2266127) B2266127
theorem B1346939 : Blo 595291 1346939 := bstep (se 1 (by rfl) ⟨1010204, by rfl⟩ : syracuseStep 1346939 = 2020409) B2020409
theorem B1347065 : Blo 595291 1347065 := bstep (se 2 (by rfl) ⟨505149, by rfl⟩ : syracuseStep 1347065 = 1010299) B1010299
theorem B1347155 : Blo 595291 1347155 := bstep (se 1 (by rfl) ⟨1010366, by rfl⟩ : syracuseStep 1347155 = 2020733) B2020733
theorem B12258955 : Blo 595291 12258955 := bstep (se 1 (by rfl) ⟨9194216, by rfl⟩ : syracuseStep 12258955 = 18388433) B18388433
theorem B2592491 : Blo 595291 2592491 := bstep (se 1 (by rfl) ⟨1944368, by rfl⟩ : syracuseStep 2592491 = 3888737) B3888737
theorem B1347335 : Blo 595291 1347335 := bstep (se 1 (by rfl) ⟨1010501, by rfl⟩ : syracuseStep 1347335 = 2021003) B2021003
theorem B15274007 : Blo 595291 15274007 := bstep (se 1 (by rfl) ⟨11455505, by rfl⟩ : syracuseStep 15274007 = 22911011) B22911011
theorem B5738825 : Blo 595291 5738825 := bstep (se 2 (by rfl) ⟨2152059, by rfl⟩ : syracuseStep 5738825 = 4304119) B4304119
theorem B1347947 : Blo 595291 1347947 := bstep (se 1 (by rfl) ⟨1010960, by rfl⟩ : syracuseStep 1347947 = 2021921) B2021921
theorem B1511855 : Blo 595291 1511855 := bstep (se 1 (by rfl) ⟨1133891, by rfl⟩ : syracuseStep 1511855 = 2267783) B2267783
theorem B1511905 : Blo 595291 1511905 := bstep (se 2 (by rfl) ⟨566964, by rfl⟩ : syracuseStep 1511905 = 1133929) B1133929
theorem B1348091 : Blo 595291 1348091 := bstep (se 1 (by rfl) ⟨1011068, by rfl⟩ : syracuseStep 1348091 = 2022137) B2022137
theorem B2265671 : Blo 595291 2265671 := bstep (se 1 (by rfl) ⟨1699253, by rfl⟩ : syracuseStep 2265671 = 3398507) B3398507
theorem B1348217 : Blo 595291 1348217 := bstep (se 2 (by rfl) ⟨505581, by rfl⟩ : syracuseStep 1348217 = 1011163) B1011163
theorem B1348271 : Blo 595291 1348271 := bstep (se 1 (by rfl) ⟨1011203, by rfl⟩ : syracuseStep 1348271 = 2022407) B2022407
theorem B1348343 : Blo 595291 1348343 := bstep (se 1 (by rfl) ⟨1011257, by rfl⟩ : syracuseStep 1348343 = 2022515) B2022515
theorem B4297637 : Blo 595291 4297637 := bstep (se 4 (by rfl) ⟨402903, by rfl⟩ : syracuseStep 4297637 = 805807) B805807
theorem B595291 : Blo 595291 595291 := bstep (se 1 (by rfl) ⟨446468, by rfl⟩ : syracuseStep 595291 = 892937) B892937
theorem B595311 : Blo 595291 595311 := bstep (se 1 (by rfl) ⟨446483, by rfl⟩ : syracuseStep 595311 = 892967) B892967
theorem B1512827 : Blo 595291 1512827 := bstep (se 1 (by rfl) ⟨1134620, by rfl⟩ : syracuseStep 1512827 = 2269241) B2269241
theorem B4298123 : Blo 595291 4298123 := bstep (se 1 (by rfl) ⟨3223592, by rfl⟩ : syracuseStep 4298123 = 6447185) B6447185
theorem B595367 : Blo 595291 595367 := bstep (se 1 (by rfl) ⟨446525, by rfl⟩ : syracuseStep 595367 = 893051) B893051
theorem B595451 : Blo 595291 595451 := bstep (se 1 (by rfl) ⟨446588, by rfl⟩ : syracuseStep 595451 = 893177) B893177
theorem B595519 : Blo 595291 595519 := bstep (se 1 (by rfl) ⟨446639, by rfl⟩ : syracuseStep 595519 = 893279) B893279
theorem B595527 : Blo 595291 595527 := bstep (se 1 (by rfl) ⟨446645, by rfl⟩ : syracuseStep 595527 = 893291) B893291
theorem B2266811 : Blo 595291 2266811 := bstep (se 1 (by rfl) ⟨1700108, by rfl⟩ : syracuseStep 2266811 = 3400217) B3400217
theorem B595679 : Blo 595291 595679 := bstep (se 1 (by rfl) ⟨446759, by rfl⟩ : syracuseStep 595679 = 893519) B893519
theorem B595759 : Blo 595291 595759 := bstep (se 1 (by rfl) ⟨446819, by rfl⟩ : syracuseStep 595759 = 893639) B893639
theorem B956215 : Blo 595291 956215 := bstep (se 1 (by rfl) ⟨717161, by rfl⟩ : syracuseStep 956215 = 1434323) B1434323
theorem B595867 : Blo 595291 595867 := bstep (se 1 (by rfl) ⟨446900, by rfl⟩ : syracuseStep 595867 = 893801) B893801
theorem B595919 : Blo 595291 595919 := bstep (se 1 (by rfl) ⟨446939, by rfl⟩ : syracuseStep 595919 = 893879) B893879
theorem B595943 : Blo 595291 595943 := bstep (se 1 (by rfl) ⟨446957, by rfl⟩ : syracuseStep 595943 = 893915) B893915
theorem B596255 : Blo 595291 596255 := bstep (se 1 (by rfl) ⟨447191, by rfl⟩ : syracuseStep 596255 = 894383) B894383
theorem B596315 : Blo 595291 596315 := bstep (se 1 (by rfl) ⟨447236, by rfl⟩ : syracuseStep 596315 = 894473) B894473
theorem B596335 : Blo 595291 596335 := bstep (se 1 (by rfl) ⟨447251, by rfl⟩ : syracuseStep 596335 = 894503) B894503
theorem B596391 : Blo 595291 596391 := bstep (se 1 (by rfl) ⟨447293, by rfl⟩ : syracuseStep 596391 = 894587) B894587
theorem B3021299 : Blo 595291 3021299 := bstep (se 1 (by rfl) ⟨2265974, by rfl⟩ : syracuseStep 3021299 = 4531949) B4531949
theorem B596475 : Blo 595291 596475 := bstep (se 1 (by rfl) ⟨447356, by rfl⟩ : syracuseStep 596475 = 894713) B894713
theorem B596543 : Blo 595291 596543 := bstep (se 1 (by rfl) ⟨447407, by rfl⟩ : syracuseStep 596543 = 894815) B894815
theorem B596551 : Blo 595291 596551 := bstep (se 1 (by rfl) ⟨447413, by rfl⟩ : syracuseStep 596551 = 894827) B894827
theorem B957035 : Blo 595291 957035 := bstep (se 1 (by rfl) ⟨717776, by rfl⟩ : syracuseStep 957035 = 1435553) B1435553
theorem B596703 : Blo 595291 596703 := bstep (se 1 (by rfl) ⟨447527, by rfl⟩ : syracuseStep 596703 = 895055) B895055
theorem B596783 : Blo 595291 596783 := bstep (se 1 (by rfl) ⟨447587, by rfl⟩ : syracuseStep 596783 = 895175) B895175
theorem B596891 : Blo 595291 596891 := bstep (se 1 (by rfl) ⟨447668, by rfl⟩ : syracuseStep 596891 = 895337) B895337
theorem B596943 : Blo 595291 596943 := bstep (se 1 (by rfl) ⟨447707, by rfl⟩ : syracuseStep 596943 = 895415) B895415
theorem B596967 : Blo 595291 596967 := bstep (se 1 (by rfl) ⟨447725, by rfl⟩ : syracuseStep 596967 = 895451) B895451
theorem B3021947 : Blo 595291 3021947 := bstep (se 1 (by rfl) ⟨2266460, by rfl⟩ : syracuseStep 3021947 = 4532921) B4532921
theorem B2268283 : Blo 595291 2268283 := bstep (se 1 (by rfl) ⟨1701212, by rfl⟩ : syracuseStep 2268283 = 3402425) B3402425
theorem B1514639 : Blo 595291 1514639 := bstep (se 1 (by rfl) ⟨1135979, by rfl⟩ : syracuseStep 1514639 = 2271959) B2271959
theorem B2039003 : Blo 595291 2039003 := bstep (se 1 (by rfl) ⟨1529252, by rfl⟩ : syracuseStep 2039003 = 3058505) B3058505
theorem B597279 : Blo 595291 597279 := bstep (se 1 (by rfl) ⟨447959, by rfl⟩ : syracuseStep 597279 = 895919) B895919
theorem B597339 : Blo 595291 597339 := bstep (se 1 (by rfl) ⟨448004, by rfl⟩ : syracuseStep 597339 = 896009) B896009
theorem B597359 : Blo 595291 597359 := bstep (se 1 (by rfl) ⟨448019, by rfl⟩ : syracuseStep 597359 = 896039) B896039
theorem B597415 : Blo 595291 597415 := bstep (se 1 (by rfl) ⟨448061, by rfl⟩ : syracuseStep 597415 = 896123) B896123
theorem B597499 : Blo 595291 597499 := bstep (se 1 (by rfl) ⟨448124, by rfl⟩ : syracuseStep 597499 = 896249) B896249
theorem B597567 : Blo 595291 597567 := bstep (se 1 (by rfl) ⟨448175, by rfl⟩ : syracuseStep 597567 = 896351) B896351
theorem B597575 : Blo 595291 597575 := bstep (se 1 (by rfl) ⟨448181, by rfl⟩ : syracuseStep 597575 = 896363) B896363
theorem B2268755 : Blo 595291 2268755 := bstep (se 1 (by rfl) ⟨1701566, by rfl⟩ : syracuseStep 2268755 = 3403133) B3403133
theorem B597727 : Blo 595291 597727 := bstep (se 1 (by rfl) ⟨448295, by rfl⟩ : syracuseStep 597727 = 896591) B896591
theorem B3022595 : Blo 595291 3022595 := bstep (se 1 (by rfl) ⟨2266946, by rfl⟩ : syracuseStep 3022595 = 4533893) B4533893
theorem B597807 : Blo 595291 597807 := bstep (se 1 (by rfl) ⟨448355, by rfl⟩ : syracuseStep 597807 = 896711) B896711
theorem B2727787 : Blo 595291 2727787 := bstep (se 1 (by rfl) ⟨2045840, by rfl⟩ : syracuseStep 2727787 = 4091681) B4091681
theorem B597915 : Blo 595291 597915 := bstep (se 1 (by rfl) ⟨448436, by rfl⟩ : syracuseStep 597915 = 896873) B896873
theorem B597967 : Blo 595291 597967 := bstep (se 1 (by rfl) ⟨448475, by rfl⟩ : syracuseStep 597967 = 896951) B896951
theorem B597991 : Blo 595291 597991 := bstep (se 1 (by rfl) ⟨448493, by rfl⟩ : syracuseStep 597991 = 896987) B896987
theorem B893033 : Blo 595291 893033 := bstep (se 2 (by rfl) ⟨334887, by rfl⟩ : syracuseStep 893033 = 669775) B669775
theorem B1908841 : Blo 595291 1908841 := bstep (se 2 (by rfl) ⟨715815, by rfl⟩ : syracuseStep 1908841 = 1431631) B1431631
theorem B3219659 : Blo 595291 3219659 := bstep (se 1 (by rfl) ⟨2414744, by rfl⟩ : syracuseStep 3219659 = 4829489) B4829489
theorem B4301009 : Blo 595291 4301009 := bstep (se 2 (by rfl) ⟨1612878, by rfl⟩ : syracuseStep 4301009 = 3225757) B3225757
theorem B11444435 : Blo 595291 11444435 := bstep (se 1 (by rfl) ⟨8583326, by rfl⟩ : syracuseStep 11444435 = 17166653) B17166653
theorem B598303 : Blo 595291 598303 := bstep (se 1 (by rfl) ⟨448727, by rfl⟩ : syracuseStep 598303 = 897455) B897455
theorem B598363 : Blo 595291 598363 := bstep (se 1 (by rfl) ⟨448772, by rfl⟩ : syracuseStep 598363 = 897545) B897545
theorem B598383 : Blo 595291 598383 := bstep (se 1 (by rfl) ⟨448787, by rfl⟩ : syracuseStep 598383 = 897575) B897575
theorem B893351 : Blo 595291 893351 := bstep (se 1 (by rfl) ⟨670013, by rfl⟩ : syracuseStep 893351 = 1340027) B1340027
theorem B598439 : Blo 595291 598439 := bstep (se 1 (by rfl) ⟨448829, by rfl⟩ : syracuseStep 598439 = 897659) B897659
theorem B893435 : Blo 595291 893435 := bstep (se 1 (by rfl) ⟨670076, by rfl⟩ : syracuseStep 893435 = 1340153) B1340153
theorem B598523 : Blo 595291 598523 := bstep (se 1 (by rfl) ⟨448892, by rfl⟩ : syracuseStep 598523 = 897785) B897785
theorem B19341827 : Blo 595291 19341827 := bstep (se 1 (by rfl) ⟨14506370, by rfl⟩ : syracuseStep 19341827 = 29012741) B29012741
theorem B598591 : Blo 595291 598591 := bstep (se 1 (by rfl) ⟨448943, by rfl⟩ : syracuseStep 598591 = 897887) B897887
theorem B598599 : Blo 595291 598599 := bstep (se 1 (by rfl) ⟨448949, by rfl⟩ : syracuseStep 598599 = 897899) B897899
theorem B893561 : Blo 595291 893561 := bstep (se 2 (by rfl) ⟨335085, by rfl⟩ : syracuseStep 893561 = 670171) B670171
theorem B893615 : Blo 595291 893615 := bstep (se 1 (by rfl) ⟨670211, by rfl⟩ : syracuseStep 893615 = 1340423) B1340423
theorem B893663 : Blo 595291 893663 := bstep (se 1 (by rfl) ⟨670247, by rfl⟩ : syracuseStep 893663 = 1340495) B1340495
theorem B598751 : Blo 595291 598751 := bstep (se 1 (by rfl) ⟨449063, by rfl⟩ : syracuseStep 598751 = 898127) B898127
theorem B1516279 : Blo 595291 1516279 := bstep (se 1 (by rfl) ⟨1137209, by rfl⟩ : syracuseStep 1516279 = 2274419) B2274419
theorem B598831 : Blo 595291 598831 := bstep (se 1 (by rfl) ⟨449123, by rfl⟩ : syracuseStep 598831 = 898247) B898247
theorem B598939 : Blo 595291 598939 := bstep (se 1 (by rfl) ⟨449204, by rfl⟩ : syracuseStep 598939 = 898409) B898409
theorem B598991 : Blo 595291 598991 := bstep (se 1 (by rfl) ⟨449243, by rfl⟩ : syracuseStep 598991 = 898487) B898487
theorem B893927 : Blo 595291 893927 := bstep (se 1 (by rfl) ⟨670445, by rfl⟩ : syracuseStep 893927 = 1340891) B1340891
theorem B599015 : Blo 595291 599015 := bstep (se 1 (by rfl) ⟨449261, by rfl⟩ : syracuseStep 599015 = 898523) B898523
theorem B1516583 : Blo 595291 1516583 := bstep (se 1 (by rfl) ⟨1137437, by rfl⟩ : syracuseStep 1516583 = 2274875) B2274875
theorem B894185 : Blo 595291 894185 := bstep (se 2 (by rfl) ⟨335319, by rfl⟩ : syracuseStep 894185 = 670639) B670639
theorem B894239 : Blo 595291 894239 := bstep (se 1 (by rfl) ⟨670679, by rfl⟩ : syracuseStep 894239 = 1341359) B1341359
theorem B3024215 : Blo 595291 3024215 := bstep (se 1 (by rfl) ⟨2268161, by rfl⟩ : syracuseStep 3024215 = 4536323) B4536323
theorem B894407 : Blo 595291 894407 := bstep (se 1 (by rfl) ⟨670805, by rfl⟩ : syracuseStep 894407 = 1341611) B1341611
theorem B894761 : Blo 595291 894761 := bstep (se 2 (by rfl) ⟨335535, by rfl⟩ : syracuseStep 894761 = 671071) B671071
theorem B894767 : Blo 595291 894767 := bstep (se 1 (by rfl) ⟨671075, by rfl⟩ : syracuseStep 894767 = 1342151) B1342151
theorem B5744519 : Blo 595291 5744519 := bstep (se 1 (by rfl) ⟨4308389, by rfl⟩ : syracuseStep 5744519 = 8616779) B8616779
theorem B3025025 : Blo 595291 3025025 := bstep (se 2 (by rfl) ⟨1134384, by rfl⟩ : syracuseStep 3025025 = 2268769) B2268769
theorem B895241 : Blo 595291 895241 := bstep (se 2 (by rfl) ⟨335715, by rfl⟩ : syracuseStep 895241 = 671431) B671431
theorem B2304281 : Blo 595291 2304281 := bstep (se 2 (by rfl) ⟨864105, by rfl⟩ : syracuseStep 2304281 = 1728211) B1728211
theorem B19573103 : Blo 595291 19573103 := bstep (se 1 (by rfl) ⟨14679827, by rfl⟩ : syracuseStep 19573103 = 29359655) B29359655
theorem B895343 : Blo 595291 895343 := bstep (se 1 (by rfl) ⟨671507, by rfl⟩ : syracuseStep 895343 = 1343015) B1343015
theorem B2271671 : Blo 595291 2271671 := bstep (se 1 (by rfl) ⟨1703753, by rfl⟩ : syracuseStep 2271671 = 3407507) B3407507
theorem B2009555 : Blo 595291 2009555 := bstep (se 1 (by rfl) ⟨1507166, by rfl⟩ : syracuseStep 2009555 = 3014333) B3014333
theorem B1911251 : Blo 595291 1911251 := bstep (se 1 (by rfl) ⟨1433438, by rfl⟩ : syracuseStep 1911251 = 2866877) B2866877
theorem B2304467 : Blo 595291 2304467 := bstep (se 1 (by rfl) ⟨1728350, by rfl⟩ : syracuseStep 2304467 = 3456701) B3456701
theorem B2009663 : Blo 595291 2009663 := bstep (se 1 (by rfl) ⟨1507247, by rfl⟩ : syracuseStep 2009663 = 3014495) B3014495
theorem B895559 : Blo 595291 895559 := bstep (se 1 (by rfl) ⟨671669, by rfl⟩ : syracuseStep 895559 = 1343339) B1343339
theorem B895595 : Blo 595291 895595 := bstep (se 1 (by rfl) ⟨671696, by rfl⟩ : syracuseStep 895595 = 1343393) B1343393
theorem B5090039 : Blo 595291 5090039 := bstep (se 1 (by rfl) ⟨3817529, by rfl⟩ : syracuseStep 5090039 = 7635059) B7635059
theorem B895823 : Blo 595291 895823 := bstep (se 1 (by rfl) ⟨671867, by rfl⟩ : syracuseStep 895823 = 1343735) B1343735
theorem B3025835 : Blo 595291 3025835 := bstep (se 1 (by rfl) ⟨2269376, by rfl⟩ : syracuseStep 3025835 = 4538753) B4538753
theorem B2272171 : Blo 595291 2272171 := bstep (se 1 (by rfl) ⟨1704128, by rfl⟩ : syracuseStep 2272171 = 3408257) B3408257
theorem B6794279 : Blo 595291 6794279 := bstep (se 1 (by rfl) ⟨5095709, by rfl⟩ : syracuseStep 6794279 = 10191419) B10191419
theorem B2272445 : Blo 595291 2272445 := bstep (se 3 (by rfl) ⟨426083, by rfl⟩ : syracuseStep 2272445 = 852167) B852167
theorem B896219 : Blo 595291 896219 := bstep (se 1 (by rfl) ⟨672164, by rfl⟩ : syracuseStep 896219 = 1344329) B1344329
theorem B2272475 : Blo 595291 2272475 := bstep (se 1 (by rfl) ⟨1704356, by rfl⟩ : syracuseStep 2272475 = 3408713) B3408713
theorem B10235159 : Blo 595291 10235159 := bstep (se 1 (by rfl) ⟨7676369, by rfl⟩ : syracuseStep 10235159 = 15352739) B15352739
theorem B896393 : Blo 595291 896393 := bstep (se 2 (by rfl) ⟨336147, by rfl⟩ : syracuseStep 896393 = 672295) B672295
theorem B1912481 : Blo 595291 1912481 := bstep (se 2 (by rfl) ⟨717180, by rfl⟩ : syracuseStep 1912481 = 1434361) B1434361
theorem B9187015 : Blo 595291 9187015 := bstep (se 1 (by rfl) ⟨6890261, by rfl⟩ : syracuseStep 9187015 = 13780523) B13780523
theorem B896747 : Blo 595291 896747 := bstep (se 1 (by rfl) ⟨672560, by rfl⟩ : syracuseStep 896747 = 1345121) B1345121
theorem B1224505 : Blo 595291 1224505 := bstep (se 2 (by rfl) ⟨459189, by rfl⟩ : syracuseStep 1224505 = 918379) B918379
theorem B896975 : Blo 595291 896975 := bstep (se 1 (by rfl) ⟨672731, by rfl⟩ : syracuseStep 896975 = 1345463) B1345463
theorem B3026969 : Blo 595291 3026969 := bstep (se 2 (by rfl) ⟨1135113, by rfl⟩ : syracuseStep 3026969 = 2270227) B2270227
theorem B1912891 : Blo 595291 1912891 := bstep (se 1 (by rfl) ⟨1434668, by rfl⟩ : syracuseStep 1912891 = 2869337) B2869337
theorem B897371 : Blo 595291 897371 := bstep (se 1 (by rfl) ⟨673028, by rfl⟩ : syracuseStep 897371 = 1346057) B1346057
theorem B2011499 : Blo 595291 2011499 := bstep (se 1 (by rfl) ⟨1508624, by rfl⟩ : syracuseStep 2011499 = 3017249) B3017249
theorem B14725595 : Blo 595291 14725595 := bstep (se 1 (by rfl) ⟨11044196, by rfl⟩ : syracuseStep 14725595 = 22088393) B22088393
theorem B897599 : Blo 595291 897599 := bstep (se 1 (by rfl) ⟨673199, by rfl⟩ : syracuseStep 897599 = 1346399) B1346399
theorem B2011769 : Blo 595291 2011769 := bstep (se 2 (by rfl) ⟨754413, by rfl⟩ : syracuseStep 2011769 = 1508827) B1508827
theorem B897719 : Blo 595291 897719 := bstep (se 1 (by rfl) ⟨673289, by rfl⟩ : syracuseStep 897719 = 1346579) B1346579
theorem B897947 : Blo 595291 897947 := bstep (se 1 (by rfl) ⟨673460, by rfl⟩ : syracuseStep 897947 = 1346921) B1346921
theorem B6468599 : Blo 595291 6468599 := bstep (se 1 (by rfl) ⟨4851449, by rfl⟩ : syracuseStep 6468599 = 9702899) B9702899
theorem B4076689 : Blo 595291 4076689 := bstep (se 2 (by rfl) ⟨1528758, by rfl⟩ : syracuseStep 4076689 = 3057517) B3057517
theorem B898343 : Blo 595291 898343 := bstep (se 1 (by rfl) ⟨673757, by rfl⟩ : syracuseStep 898343 = 1347515) B1347515
theorem B5092703 : Blo 595291 5092703 := bstep (se 1 (by rfl) ⟨3819527, by rfl⟩ : syracuseStep 5092703 = 7639055) B7639055
theorem B898427 : Blo 595291 898427 := bstep (se 1 (by rfl) ⟨673820, by rfl⟩ : syracuseStep 898427 = 1347641) B1347641
theorem B898553 : Blo 595291 898553 := bstep (se 2 (by rfl) ⟨336957, by rfl⟩ : syracuseStep 898553 = 673915) B673915
theorem B9582119 : Blo 595291 9582119 := bstep (se 1 (by rfl) ⟨7186589, by rfl⟩ : syracuseStep 9582119 = 14373179) B14373179
theorem B898655 : Blo 595291 898655 := bstep (se 1 (by rfl) ⟨673991, by rfl⟩ : syracuseStep 898655 = 1347983) B1347983
theorem B898871 : Blo 595291 898871 := bstep (se 1 (by rfl) ⟨674153, by rfl⟩ : syracuseStep 898871 = 1348307) B1348307
theorem B636827 : Blo 595291 636827 := bstep (se 1 (by rfl) ⟨477620, by rfl⟩ : syracuseStep 636827 = 955241) B955241
theorem B2275361 : Blo 595291 2275361 := bstep (se 2 (by rfl) ⟨853260, by rfl⟩ : syracuseStep 2275361 = 1706521) B1706521
theorem B669991 : Blo 595291 669991 := bstep (se 1 (by rfl) ⟨502493, by rfl⟩ : syracuseStep 669991 = 1004987) B1004987
theorem B4962637 : Blo 595291 4962637 := bstep (se 3 (by rfl) ⟨930494, by rfl⟩ : syracuseStep 4962637 = 1860989) B1860989
theorem B670063 : Blo 595291 670063 := bstep (se 1 (by rfl) ⟨502547, by rfl⟩ : syracuseStep 670063 = 1005095) B1005095
theorem B2013551 : Blo 595291 2013551 := bstep (se 1 (by rfl) ⟨1510163, by rfl⟩ : syracuseStep 2013551 = 3020327) B3020327
theorem B670279 : Blo 595291 670279 := bstep (se 1 (by rfl) ⟨502709, by rfl⟩ : syracuseStep 670279 = 1005419) B1005419
theorem B7289477 : Blo 595291 7289477 := bstep (se 4 (by rfl) ⟨683388, by rfl⟩ : syracuseStep 7289477 = 1366777) B1366777
theorem B3029885 : Blo 595291 3029885 := bstep (se 3 (by rfl) ⟨568103, by rfl⟩ : syracuseStep 3029885 = 1136207) B1136207
theorem B19414205 : Blo 595291 19414205 := bstep (se 3 (by rfl) ⟨3640163, by rfl⟩ : syracuseStep 19414205 = 7280327) B7280327
theorem B5258429 : Blo 595291 5258429 := bstep (se 3 (by rfl) ⟨985955, by rfl⟩ : syracuseStep 5258429 = 1971911) B1971911
theorem B3325313 : Blo 595291 3325313 := bstep (se 2 (by rfl) ⟨1246992, by rfl⟩ : syracuseStep 3325313 = 2493985) B2493985
theorem B1228169 : Blo 595291 1228169 := bstep (se 2 (by rfl) ⟨460563, by rfl⟩ : syracuseStep 1228169 = 921127) B921127
theorem B671143 : Blo 595291 671143 := bstep (se 1 (by rfl) ⟨503357, by rfl⟩ : syracuseStep 671143 = 1006715) B1006715
theorem B1916531 : Blo 595291 1916531 := bstep (se 1 (by rfl) ⟨1437398, by rfl⟩ : syracuseStep 1916531 = 2874797) B2874797
theorem B2014955 : Blo 595291 2014955 := bstep (se 1 (by rfl) ⟨1511216, by rfl⟩ : syracuseStep 2014955 = 3022433) B3022433
theorem B3030857 : Blo 595291 3030857 := bstep (se 2 (by rfl) ⟨1136571, by rfl⟩ : syracuseStep 3030857 = 2273143) B2273143
theorem B671719 : Blo 595291 671719 := bstep (se 1 (by rfl) ⟨503789, by rfl⟩ : syracuseStep 671719 = 1007579) B1007579
theorem B10862693 : Blo 595291 10862693 := bstep (se 4 (by rfl) ⟨1018377, by rfl⟩ : syracuseStep 10862693 = 2036755) B2036755
theorem B7258531 : Blo 595291 7258531 := bstep (se 1 (by rfl) ⟨5443898, by rfl⟩ : syracuseStep 7258531 = 10887797) B10887797
theorem B6439571 : Blo 595291 6439571 := bstep (se 1 (by rfl) ⟨4829678, by rfl⟩ : syracuseStep 6439571 = 9659357) B9659357
theorem B2015927 : Blo 595291 2015927 := bstep (se 1 (by rfl) ⟨1511945, by rfl⟩ : syracuseStep 2015927 = 3023891) B3023891
theorem B8602361 : Blo 595291 8602361 := bstep (se 2 (by rfl) ⟨3225885, by rfl⟩ : syracuseStep 8602361 = 6451771) B6451771
theorem B3064807 : Blo 595291 3064807 := bstep (se 1 (by rfl) ⟨2298605, by rfl⟩ : syracuseStep 3064807 = 4597211) B4597211
theorem B3064823 : Blo 595291 3064823 := bstep (se 1 (by rfl) ⟨2298617, by rfl⟩ : syracuseStep 3064823 = 4597235) B4597235
theorem B3032153 : Blo 595291 3032153 := bstep (se 2 (by rfl) ⟨1137057, by rfl⟩ : syracuseStep 3032153 = 2274115) B2274115
theorem B2147897 : Blo 595291 2147897 := bstep (se 2 (by rfl) ⟨805461, by rfl⟩ : syracuseStep 2147897 = 1610923) B1610923
theorem B673375 : Blo 595291 673375 := bstep (se 1 (by rfl) ⟨505031, by rfl⟩ : syracuseStep 673375 = 1010063) B1010063
theorem B2901841 : Blo 595291 2901841 := bstep (se 2 (by rfl) ⟨1088190, by rfl⟩ : syracuseStep 2901841 = 2176381) B2176381
theorem B1296713 : Blo 595291 1296713 := bstep (se 2 (by rfl) ⟨486267, by rfl⟩ : syracuseStep 1296713 = 972535) B972535
theorem B2017871 : Blo 595291 2017871 := bstep (se 1 (by rfl) ⟨1513403, by rfl⟩ : syracuseStep 2017871 = 3026807) B3026807
theorem B6113879 : Blo 595291 6113879 := bstep (se 1 (by rfl) ⟨4585409, by rfl⟩ : syracuseStep 6113879 = 9170819) B9170819
theorem B7359149 : Blo 595291 7359149 := bstep (se 3 (by rfl) ⟨1379840, by rfl⟩ : syracuseStep 7359149 = 2759681) B2759681
theorem B2019113 : Blo 595291 2019113 := bstep (se 2 (by rfl) ⟨757167, by rfl⟩ : syracuseStep 2019113 = 1514335) B1514335
theorem B3395843 : Blo 595291 3395843 := bstep (se 1 (by rfl) ⟨2546882, by rfl⟩ : syracuseStep 3395843 = 5093765) B5093765
theorem B2806343 : Blo 595291 2806343 := bstep (se 1 (by rfl) ⟨2104757, by rfl⟩ : syracuseStep 2806343 = 4209515) B4209515
theorem B807607 : Blo 595291 807607 := bstep (se 1 (by rfl) ⟨605705, by rfl⟩ : syracuseStep 807607 = 1211411) B1211411
theorem B4543613 : Blo 595291 4543613 := bstep (se 3 (by rfl) ⟨851927, by rfl⟩ : syracuseStep 4543613 = 1703855) B1703855
theorem B1529047 : Blo 595291 1529047 := bstep (se 1 (by rfl) ⟨1146785, by rfl⟩ : syracuseStep 1529047 = 2293571) B2293571
theorem B1430777 : Blo 595291 1430777 := bstep (se 2 (by rfl) ⟨536541, by rfl⟩ : syracuseStep 1430777 = 1073083) B1073083
theorem B7263593 : Blo 595291 7263593 := bstep (se 2 (by rfl) ⟨2723847, by rfl⟩ : syracuseStep 7263593 = 5447695) B5447695
theorem B1529705 : Blo 595291 1529705 := bstep (se 2 (by rfl) ⟨573639, by rfl⟩ : syracuseStep 1529705 = 1147279) B1147279
theorem B2021327 : Blo 595291 2021327 := bstep (se 1 (by rfl) ⟨1515995, by rfl⟩ : syracuseStep 2021327 = 3031991) B3031991
theorem B2546063 : Blo 595291 2546063 := bstep (se 1 (by rfl) ⟨1909547, by rfl⟩ : syracuseStep 2546063 = 3819095) B3819095
theorem B6805943 : Blo 595291 6805943 := bstep (se 1 (by rfl) ⟨5104457, by rfl⟩ : syracuseStep 6805943 = 10208915) B10208915
theorem B1366523 : Blo 595291 1366523 := bstep (se 1 (by rfl) ⟨1024892, by rfl⟩ : syracuseStep 1366523 = 2049785) B2049785
theorem B2415167 : Blo 595291 2415167 := bstep (se 1 (by rfl) ⟨1811375, by rfl⟩ : syracuseStep 2415167 = 3622751) B3622751
theorem B1006303 : Blo 595291 1006303 := bstep (se 1 (by rfl) ⟨754727, by rfl⟩ : syracuseStep 1006303 = 1509455) B1509455
theorem B6445979 : Blo 595291 6445979 := bstep (se 1 (by rfl) ⟨4834484, by rfl⟩ : syracuseStep 6445979 = 9668969) B9668969
theorem B2022299 : Blo 595291 2022299 := bstep (se 1 (by rfl) ⟨1516724, by rfl⟩ : syracuseStep 2022299 = 3033449) B3033449
theorem B2153387 : Blo 595291 2153387 := bstep (se 1 (by rfl) ⟨1615040, by rfl⟩ : syracuseStep 2153387 = 3230081) B3230081
theorem B44194895 : Blo 595291 44194895 := bstep (se 1 (by rfl) ⟨33146171, by rfl⟩ : syracuseStep 44194895 = 66292343) B66292343
theorem B1006735 : Blo 595291 1006735 := bstep (se 1 (by rfl) ⟨755051, by rfl⟩ : syracuseStep 1006735 = 1510103) B1510103
theorem B1006985 : Blo 595291 1006985 := bstep (se 2 (by rfl) ⟨377619, by rfl⟩ : syracuseStep 1006985 = 755239) B755239
theorem B1498583 : Blo 595291 1498583 := bstep (se 1 (by rfl) ⟨1123937, by rfl⟩ : syracuseStep 1498583 = 2247875) B2247875
theorem B1072801 : Blo 595291 1072801 := bstep (se 2 (by rfl) ⟨402300, by rfl⟩ : syracuseStep 1072801 = 804601) B804601
theorem B1007417 : Blo 595291 1007417 := bstep (se 2 (by rfl) ⟨377781, by rfl⟩ : syracuseStep 1007417 = 755563) B755563
theorem B2416513 : Blo 595291 2416513 := bstep (se 2 (by rfl) ⟨906192, by rfl⟩ : syracuseStep 2416513 = 1812385) B1812385
theorem B3498137 : Blo 595291 3498137 := bstep (se 2 (by rfl) ⟨1311801, by rfl⟩ : syracuseStep 3498137 = 2623603) B2623603
theorem B1073839 : Blo 595291 1073839 := bstep (se 1 (by rfl) ⟨805379, by rfl⟩ : syracuseStep 1073839 = 1610759) B1610759
theorem B2548523 : Blo 595291 2548523 := bstep (se 1 (by rfl) ⟨1911392, by rfl⟩ : syracuseStep 2548523 = 3822785) B3822785
theorem B1008463 : Blo 595291 1008463 := bstep (se 1 (by rfl) ⟨756347, by rfl⟩ : syracuseStep 1008463 = 1512695) B1512695
theorem B5530463 : Blo 595291 5530463 := bstep (se 1 (by rfl) ⟨4147847, by rfl⟩ : syracuseStep 5530463 = 8295695) B8295695
theorem B2548675 : Blo 595291 2548675 := bstep (se 1 (by rfl) ⟨1911506, by rfl⟩ : syracuseStep 2548675 = 3823013) B3823013
theorem B1532903 : Blo 595291 1532903 := bstep (se 1 (by rfl) ⟨1149677, by rfl⟩ : syracuseStep 1532903 = 2299355) B2299355
theorem B5432663 : Blo 595291 5432663 := bstep (se 1 (by rfl) ⟨4074497, by rfl⟩ : syracuseStep 5432663 = 8148995) B8148995
theorem B3401149 : Blo 595291 3401149 := bstep (se 3 (by rfl) ⟨637715, by rfl⟩ : syracuseStep 3401149 = 1275431) B1275431
theorem B1009145 : Blo 595291 1009145 := bstep (se 2 (by rfl) ⟨378429, by rfl⟩ : syracuseStep 1009145 = 756859) B756859
theorem B1009415 : Blo 595291 1009415 := bstep (se 1 (by rfl) ⟨757061, by rfl⟩ : syracuseStep 1009415 = 1514123) B1514123
theorem B1697591 : Blo 595291 1697591 := bstep (se 1 (by rfl) ⟨1273193, by rfl⟩ : syracuseStep 1697591 = 2546387) B2546387
theorem B3074183 : Blo 595291 3074183 := bstep (se 1 (by rfl) ⟨2305637, by rfl⟩ : syracuseStep 3074183 = 4611275) B4611275
theorem B1010171 : Blo 595291 1010171 := bstep (se 1 (by rfl) ⟨757628, by rfl⟩ : syracuseStep 1010171 = 1515257) B1515257
theorem B1698479 : Blo 595291 1698479 := bstep (se 1 (by rfl) ⟨1273859, by rfl⟩ : syracuseStep 1698479 = 2547719) B2547719
theorem B1075987 : Blo 595291 1075987 := bstep (se 1 (by rfl) ⟨806990, by rfl⟩ : syracuseStep 1075987 = 1613981) B1613981
theorem B1010603 : Blo 595291 1010603 := bstep (se 1 (by rfl) ⟨757952, by rfl⟩ : syracuseStep 1010603 = 1515905) B1515905
theorem B716123 : Blo 595291 716123 := bstep (se 1 (by rfl) ⟨537092, by rfl⟩ : syracuseStep 716123 = 1074185) B1074185
theorem B1011143 : Blo 595291 1011143 := bstep (se 1 (by rfl) ⟨758357, by rfl⟩ : syracuseStep 1011143 = 1516715) B1516715
theorem B13102553 : Blo 595291 13102553 := bstep (se 2 (by rfl) ⟨4913457, by rfl⟩ : syracuseStep 13102553 = 9826915) B9826915
theorem B3239837 : Blo 595291 3239837 := bstep (se 3 (by rfl) ⟨607469, by rfl⟩ : syracuseStep 3239837 = 1214939) B1214939
theorem B3502081 : Blo 595291 3502081 := bstep (se 2 (by rfl) ⟨1313280, by rfl⟩ : syracuseStep 3502081 = 2626561) B2626561
theorem B1339721 : Blo 595291 1339721 := bstep (se 2 (by rfl) ⟨502395, by rfl⟩ : syracuseStep 1339721 = 1004791) B1004791
theorem B1339739 : Blo 595291 1339739 := bstep (se 1 (by rfl) ⟨1004804, by rfl⟩ : syracuseStep 1339739 = 2009609) B2009609
theorem B1274287 : Blo 595291 1274287 := bstep (se 1 (by rfl) ⟨955715, by rfl⟩ : syracuseStep 1274287 = 1911431) B1911431
theorem B3404339 : Blo 595291 3404339 := bstep (se 1 (by rfl) ⟨2553254, by rfl⟩ : syracuseStep 3404339 = 5106509) B5106509
theorem B5108285 : Blo 595291 5108285 := bstep (se 3 (by rfl) ⟨957803, by rfl⟩ : syracuseStep 5108285 = 1915607) B1915607
theorem B1077833 : Blo 595291 1077833 := bstep (se 2 (by rfl) ⟨404187, by rfl⟩ : syracuseStep 1077833 = 808375) B808375
theorem B1536619 : Blo 595291 1536619 := bstep (se 1 (by rfl) ⟨1152464, by rfl⟩ : syracuseStep 1536619 = 2304929) B2304929
theorem B1700473 : Blo 595291 1700473 := bstep (se 2 (by rfl) ⟨637677, by rfl⟩ : syracuseStep 1700473 = 1275355) B1275355
theorem B1274543 : Blo 595291 1274543 := bstep (se 1 (by rfl) ⟨955907, by rfl⟩ : syracuseStep 1274543 = 1911815) B1911815
theorem B1340315 : Blo 595291 1340315 := bstep (se 1 (by rfl) ⟨1005236, by rfl⟩ : syracuseStep 1340315 = 2010473) B2010473
theorem B1340513 : Blo 595291 1340513 := bstep (se 2 (by rfl) ⟨502692, by rfl⟩ : syracuseStep 1340513 = 1005385) B1005385
theorem B1438859 : Blo 595291 1438859 := bstep (se 1 (by rfl) ⟨1079144, by rfl⟩ : syracuseStep 1438859 = 2158289) B2158289
theorem B2422009 : Blo 595291 2422009 := bstep (se 2 (by rfl) ⟨908253, by rfl⟩ : syracuseStep 2422009 = 1816507) B1816507
theorem B1340711 : Blo 595291 1340711 := bstep (se 1 (by rfl) ⟨1005533, by rfl⟩ : syracuseStep 1340711 = 2011067) B2011067
theorem B34895249 : Blo 595291 34895249 := bstep (se 2 (by rfl) ⟨13085718, by rfl⟩ : syracuseStep 34895249 = 26171437) B26171437
theorem B1341089 : Blo 595291 1341089 := bstep (se 2 (by rfl) ⟨502908, by rfl⟩ : syracuseStep 1341089 = 1005817) B1005817
theorem B1439495 : Blo 595291 1439495 := bstep (se 1 (by rfl) ⟨1079621, by rfl⟩ : syracuseStep 1439495 = 2159243) B2159243
theorem B6289271 : Blo 595291 6289271 := bstep (se 1 (by rfl) ⟨4716953, by rfl⟩ : syracuseStep 6289271 = 9433907) B9433907
theorem B3405797 : Blo 595291 3405797 := bstep (se 4 (by rfl) ⟨319293, by rfl⟩ : syracuseStep 3405797 = 638587) B638587
theorem B1341449 : Blo 595291 1341449 := bstep (se 2 (by rfl) ⟨503043, by rfl⟩ : syracuseStep 1341449 = 1006087) B1006087
theorem B1341863 : Blo 595291 1341863 := bstep (se 1 (by rfl) ⟨1006397, by rfl⟩ : syracuseStep 1341863 = 2012795) B2012795
theorem B5110199 : Blo 595291 5110199 := bstep (se 1 (by rfl) ⟨3832649, by rfl⟩ : syracuseStep 5110199 = 7665299) B7665299
theorem B1341971 : Blo 595291 1341971 := bstep (se 1 (by rfl) ⟨1006478, by rfl⟩ : syracuseStep 1341971 = 2012957) B2012957
theorem B1342025 : Blo 595291 1342025 := bstep (se 2 (by rfl) ⟨503259, by rfl⟩ : syracuseStep 1342025 = 1006519) B1006519
theorem B3635887 : Blo 595291 3635887 := bstep (se 1 (by rfl) ⟨2726915, by rfl⟩ : syracuseStep 3635887 = 5453831) B5453831
theorem B719771 : Blo 595291 719771 := bstep (se 1 (by rfl) ⟨539828, by rfl⟩ : syracuseStep 719771 = 1079657) B1079657
theorem B2554811 : Blo 595291 2554811 := bstep (se 1 (by rfl) ⟨1916108, by rfl⟩ : syracuseStep 2554811 = 3832217) B3832217
theorem B1342439 : Blo 595291 1342439 := bstep (se 1 (by rfl) ⟨1006829, by rfl⟩ : syracuseStep 1342439 = 2013659) B2013659
theorem B2554895 : Blo 595291 2554895 := bstep (se 1 (by rfl) ⟨1916171, by rfl⟩ : syracuseStep 2554895 = 3832343) B3832343
theorem B1703035 : Blo 595291 1703035 := bstep (se 1 (by rfl) ⟨1277276, by rfl⟩ : syracuseStep 1703035 = 2554553) B2554553
theorem B851239 : Blo 595291 851239 := bstep (se 1 (by rfl) ⟨638429, by rfl⟩ : syracuseStep 851239 = 1276859) B1276859
theorem B1342817 : Blo 595291 1342817 := bstep (se 2 (by rfl) ⟨503556, by rfl⟩ : syracuseStep 1342817 = 1007113) B1007113
theorem B1277345 : Blo 595291 1277345 := bstep (se 2 (by rfl) ⟨479004, by rfl⟩ : syracuseStep 1277345 = 958009) B958009
theorem B1342907 : Blo 595291 1342907 := bstep (se 1 (by rfl) ⟨1007180, by rfl⟩ : syracuseStep 1342907 = 2014361) B2014361
theorem B1343033 : Blo 595291 1343033 := bstep (se 2 (by rfl) ⟨503637, by rfl⟩ : syracuseStep 1343033 = 1007275) B1007275
theorem B3833729 : Blo 595291 3833729 := bstep (se 2 (by rfl) ⟨1437648, by rfl⟩ : syracuseStep 3833729 = 2875297) B2875297
theorem B753563 : Blo 595291 753563 := bstep (se 1 (by rfl) ⟨565172, by rfl⟩ : syracuseStep 753563 = 1130345) B1130345
theorem B18677765 : Blo 595291 18677765 := bstep (se 4 (by rfl) ⟨1751040, by rfl⟩ : syracuseStep 18677765 = 3502081) B3502081
theorem B7241795 : Blo 595291 7241795 := bstep (se 1 (by rfl) ⟨5431346, by rfl⟩ : syracuseStep 7241795 = 10862693) B10862693
theorem B4293047 : Blo 595291 4293047 := bstep (se 1 (by rfl) ⟨3219785, by rfl⟩ : syracuseStep 4293047 = 6439571) B6439571
theorem B1343951 : Blo 595291 1343951 := bstep (se 1 (by rfl) ⟨1007963, by rfl⟩ : syracuseStep 1343951 = 2015927) B2015927
theorem B5734907 : Blo 595291 5734907 := bstep (se 1 (by rfl) ⟨4301180, by rfl⟩ : syracuseStep 5734907 = 8602361) B8602361
theorem B4850441 : Blo 595291 4850441 := bstep (se 2 (by rfl) ⟨1818915, by rfl⟩ : syracuseStep 4850441 = 3637831) B3637831
theorem B1704847 : Blo 595291 1704847 := bstep (se 1 (by rfl) ⟨1278635, by rfl⟩ : syracuseStep 1704847 = 2557271) B2557271
theorem B1344617 : Blo 595291 1344617 := bstep (se 2 (by rfl) ⟨504231, by rfl⟩ : syracuseStep 1344617 = 1008463) B1008463
theorem B1345247 : Blo 595291 1345247 := bstep (se 1 (by rfl) ⟨1008935, by rfl⟩ : syracuseStep 1345247 = 2017871) B2017871
theorem B1509151 : Blo 595291 1509151 := bstep (se 1 (by rfl) ⟨1131863, by rfl⟩ : syracuseStep 1509151 = 2263727) B2263727
theorem B1705769 : Blo 595291 1705769 := bstep (se 2 (by rfl) ⟨639663, by rfl⟩ : syracuseStep 1705769 = 1279327) B1279327
theorem B1967951 : Blo 595291 1967951 := bstep (se 1 (by rfl) ⟨1475963, by rfl⟩ : syracuseStep 1967951 = 2951927) B2951927
theorem B1346075 : Blo 595291 1346075 := bstep (se 1 (by rfl) ⟨1009556, by rfl⟩ : syracuseStep 1346075 = 2019113) B2019113
theorem B2263895 : Blo 595291 2263895 := bstep (se 1 (by rfl) ⟨1697921, by rfl⟩ : syracuseStep 2263895 = 3395843) B3395843
theorem B1510447 : Blo 595291 1510447 := bstep (se 1 (by rfl) ⟨1132835, by rfl⟩ : syracuseStep 1510447 = 2265671) B2265671
theorem B1870895 : Blo 595291 1870895 := bstep (se 1 (by rfl) ⟨1403171, by rfl⟩ : syracuseStep 1870895 = 2806343) B2806343
theorem B953851 : Blo 595291 953851 := bstep (se 1 (by rfl) ⟨715388, by rfl⟩ : syracuseStep 953851 = 1430777) B1430777
theorem B1511207 : Blo 595291 1511207 := bstep (se 1 (by rfl) ⟨1133405, by rfl⟩ : syracuseStep 1511207 = 2266811) B2266811
theorem B1019803 : Blo 595291 1019803 := bstep (se 1 (by rfl) ⟨764852, by rfl⟩ : syracuseStep 1019803 = 1529705) B1529705
theorem B1347551 : Blo 595291 1347551 := bstep (se 1 (by rfl) ⟨1010663, by rfl⟩ : syracuseStep 1347551 = 2021327) B2021327
theorem B5738597 : Blo 595291 5738597 := bstep (se 4 (by rfl) ⟨537993, by rfl⟩ : syracuseStep 5738597 = 1075987) B1075987
theorem B4853945 : Blo 595291 4853945 := bstep (se 2 (by rfl) ⟨1820229, by rfl⟩ : syracuseStep 4853945 = 3640459) B3640459
theorem B1610111 : Blo 595291 1610111 := bstep (se 1 (by rfl) ⟨1207583, by rfl⟩ : syracuseStep 1610111 = 2415167) B2415167
theorem B4297319 : Blo 595291 4297319 := bstep (se 1 (by rfl) ⟨3222989, by rfl⟩ : syracuseStep 4297319 = 6445979) B6445979
theorem B1348199 : Blo 595291 1348199 := bstep (se 1 (by rfl) ⟨1011149, by rfl⟩ : syracuseStep 1348199 = 2022299) B2022299
theorem B29463263 : Blo 595291 29463263 := bstep (se 1 (by rfl) ⟨22097447, by rfl⟩ : syracuseStep 29463263 = 44194895) B44194895
theorem B3937085 : Blo 595291 3937085 := bstep (se 3 (by rfl) ⟨738203, by rfl⟩ : syracuseStep 3937085 = 1476407) B1476407
theorem B1512503 : Blo 595291 1512503 := bstep (se 1 (by rfl) ⟨1134377, by rfl⟩ : syracuseStep 1512503 = 2268755) B2268755
theorem B595355 : Blo 595291 595355 := bstep (se 1 (by rfl) ⟨446516, by rfl⟩ : syracuseStep 595355 = 893033) B893033
theorem B2332091 : Blo 595291 2332091 := bstep (se 1 (by rfl) ⟨1749068, by rfl⟩ : syracuseStep 2332091 = 3498137) B3498137
theorem B595567 : Blo 595291 595567 := bstep (se 1 (by rfl) ⟨446675, by rfl⟩ : syracuseStep 595567 = 893351) B893351
theorem B595623 : Blo 595291 595623 := bstep (se 1 (by rfl) ⟨446717, by rfl⟩ : syracuseStep 595623 = 893435) B893435
theorem B595707 : Blo 595291 595707 := bstep (se 1 (by rfl) ⟨446780, by rfl⟩ : syracuseStep 595707 = 893561) B893561
theorem B595743 : Blo 595291 595743 := bstep (se 1 (by rfl) ⟨446807, by rfl⟩ : syracuseStep 595743 = 893615) B893615
theorem B595775 : Blo 595291 595775 := bstep (se 1 (by rfl) ⟨446831, by rfl⟩ : syracuseStep 595775 = 893663) B893663
theorem B595951 : Blo 595291 595951 := bstep (se 1 (by rfl) ⟨446963, by rfl⟩ : syracuseStep 595951 = 893927) B893927
theorem B596123 : Blo 595291 596123 := bstep (se 1 (by rfl) ⟨447092, by rfl⟩ : syracuseStep 596123 = 894185) B894185
theorem B2267297 : Blo 595291 2267297 := bstep (se 2 (by rfl) ⟨850236, by rfl⟩ : syracuseStep 2267297 = 1700473) B1700473
theorem B596159 : Blo 595291 596159 := bstep (se 1 (by rfl) ⟨447119, by rfl⟩ : syracuseStep 596159 = 894239) B894239
theorem B596271 : Blo 595291 596271 := bstep (se 1 (by rfl) ⟨447203, by rfl⟩ : syracuseStep 596271 = 894407) B894407
theorem B596507 : Blo 595291 596507 := bstep (se 1 (by rfl) ⟨447380, by rfl⟩ : syracuseStep 596507 = 894761) B894761
theorem B596511 : Blo 595291 596511 := bstep (se 1 (by rfl) ⟨447383, by rfl⟩ : syracuseStep 596511 = 894767) B894767
theorem B596827 : Blo 595291 596827 := bstep (se 1 (by rfl) ⟨447620, by rfl⟩ : syracuseStep 596827 = 895241) B895241
theorem B596895 : Blo 595291 596895 := bstep (se 1 (by rfl) ⟨447671, by rfl⟩ : syracuseStep 596895 = 895343) B895343
theorem B2038729 : Blo 595291 2038729 := bstep (se 2 (by rfl) ⟨764523, by rfl⟩ : syracuseStep 2038729 = 1529047) B1529047
theorem B1514447 : Blo 595291 1514447 := bstep (se 1 (by rfl) ⟨1135835, by rfl⟩ : syracuseStep 1514447 = 2271671) B2271671
theorem B61905941 : Blo 595291 61905941 := bstep (se 6 (by rfl) ⟨1450920, by rfl⟩ : syracuseStep 61905941 = 2901841) B2901841
theorem B597039 : Blo 595291 597039 := bstep (se 1 (by rfl) ⟨447779, by rfl⟩ : syracuseStep 597039 = 895559) B895559
theorem B597063 : Blo 595291 597063 := bstep (se 1 (by rfl) ⟨447797, by rfl⟩ : syracuseStep 597063 = 895595) B895595
theorem B597215 : Blo 595291 597215 := bstep (se 1 (by rfl) ⟨447911, by rfl⟩ : syracuseStep 597215 = 895823) B895823
theorem B4529519 : Blo 595291 4529519 := bstep (se 1 (by rfl) ⟨3397139, by rfl⟩ : syracuseStep 4529519 = 6794279) B6794279
theorem B1514963 : Blo 595291 1514963 := bstep (se 1 (by rfl) ⟨1136222, by rfl⟩ : syracuseStep 1514963 = 2272445) B2272445
theorem B597479 : Blo 595291 597479 := bstep (se 1 (by rfl) ⟨448109, by rfl⟩ : syracuseStep 597479 = 896219) B896219
theorem B1514983 : Blo 595291 1514983 := bstep (se 1 (by rfl) ⟨1136237, by rfl⟩ : syracuseStep 1514983 = 2272475) B2272475
theorem B6823439 : Blo 595291 6823439 := bstep (se 1 (by rfl) ⟨5117579, by rfl⟩ : syracuseStep 6823439 = 10235159) B10235159
theorem B597595 : Blo 595291 597595 := bstep (se 1 (by rfl) ⟨448196, by rfl⟩ : syracuseStep 597595 = 896393) B896393
theorem B597831 : Blo 595291 597831 := bstep (se 1 (by rfl) ⟨448373, by rfl⟩ : syracuseStep 597831 = 896747) B896747
theorem B597983 : Blo 595291 597983 := bstep (se 1 (by rfl) ⟨448487, by rfl⟩ : syracuseStep 597983 = 896975) B896975
theorem B893147 : Blo 595291 893147 := bstep (se 1 (by rfl) ⟨669860, by rfl⟩ : syracuseStep 893147 = 1339721) B1339721
theorem B893159 : Blo 595291 893159 := bstep (se 1 (by rfl) ⟨669869, by rfl⟩ : syracuseStep 893159 = 1339739) B1339739
theorem B598247 : Blo 595291 598247 := bstep (se 1 (by rfl) ⟨448685, by rfl⟩ : syracuseStep 598247 = 897371) B897371
theorem B2269559 : Blo 595291 2269559 := bstep (se 1 (by rfl) ⟨1702169, by rfl⟩ : syracuseStep 2269559 = 3404339) B3404339
theorem B598399 : Blo 595291 598399 := bstep (se 1 (by rfl) ⟨448799, by rfl⟩ : syracuseStep 598399 = 897599) B897599
theorem B893321 : Blo 595291 893321 := bstep (se 2 (by rfl) ⟨334995, by rfl⟩ : syracuseStep 893321 = 669991) B669991
theorem B598479 : Blo 595291 598479 := bstep (se 1 (by rfl) ⟨448859, by rfl⟩ : syracuseStep 598479 = 897719) B897719
theorem B893417 : Blo 595291 893417 := bstep (se 2 (by rfl) ⟨335031, by rfl⟩ : syracuseStep 893417 = 670063) B670063
theorem B893543 : Blo 595291 893543 := bstep (se 1 (by rfl) ⟨670157, by rfl⟩ : syracuseStep 893543 = 1340315) B1340315
theorem B598631 : Blo 595291 598631 := bstep (se 1 (by rfl) ⟨448973, by rfl⟩ : syracuseStep 598631 = 897947) B897947
theorem B893675 : Blo 595291 893675 := bstep (se 1 (by rfl) ⟨670256, by rfl⟩ : syracuseStep 893675 = 1340513) B1340513
theorem B959239 : Blo 595291 959239 := bstep (se 1 (by rfl) ⟨719429, by rfl⟩ : syracuseStep 959239 = 1438859) B1438859
theorem B893705 : Blo 595291 893705 := bstep (se 2 (by rfl) ⟨335139, by rfl⟩ : syracuseStep 893705 = 670279) B670279
theorem B893807 : Blo 595291 893807 := bstep (se 1 (by rfl) ⟨670355, by rfl⟩ : syracuseStep 893807 = 1340711) B1340711
theorem B598895 : Blo 595291 598895 := bstep (se 1 (by rfl) ⟨449171, by rfl⟩ : syracuseStep 598895 = 898343) B898343
theorem B1909661 : Blo 595291 1909661 := bstep (se 3 (by rfl) ⟨358061, by rfl⟩ : syracuseStep 1909661 = 716123) B716123
theorem B598951 : Blo 595291 598951 := bstep (se 1 (by rfl) ⟨449213, by rfl⟩ : syracuseStep 598951 = 898427) B898427
theorem B599035 : Blo 595291 599035 := bstep (se 1 (by rfl) ⟨449276, by rfl⟩ : syracuseStep 599035 = 898553) B898553
theorem B599103 : Blo 595291 599103 := bstep (se 1 (by rfl) ⟨449327, by rfl⟩ : syracuseStep 599103 = 898655) B898655
theorem B894059 : Blo 595291 894059 := bstep (se 1 (by rfl) ⟨670544, by rfl⟩ : syracuseStep 894059 = 1341089) B1341089
theorem B959663 : Blo 595291 959663 := bstep (se 1 (by rfl) ⟨719747, by rfl⟩ : syracuseStep 959663 = 1439495) B1439495
theorem B599247 : Blo 595291 599247 := bstep (se 1 (by rfl) ⟨449435, by rfl⟩ : syracuseStep 599247 = 898871) B898871
theorem B2270531 : Blo 595291 2270531 := bstep (se 1 (by rfl) ⟨1702898, by rfl⟩ : syracuseStep 2270531 = 3405797) B3405797
theorem B894299 : Blo 595291 894299 := bstep (se 1 (by rfl) ⟨670724, by rfl⟩ : syracuseStep 894299 = 1341449) B1341449
theorem B1516907 : Blo 595291 1516907 := bstep (se 1 (by rfl) ⟨1137680, by rfl⟩ : syracuseStep 1516907 = 2275361) B2275361
theorem B3024377 : Blo 595291 3024377 := bstep (se 2 (by rfl) ⟨1134141, by rfl⟩ : syracuseStep 3024377 = 2268283) B2268283
theorem B2270713 : Blo 595291 2270713 := bstep (se 2 (by rfl) ⟨851517, by rfl⟩ : syracuseStep 2270713 = 1703035) B1703035
theorem B894575 : Blo 595291 894575 := bstep (se 1 (by rfl) ⟨670931, by rfl⟩ : syracuseStep 894575 = 1341863) B1341863
theorem B6792821 : Blo 595291 6792821 := bstep (se 5 (by rfl) ⟨318413, by rfl⟩ : syracuseStep 6792821 = 636827) B636827
theorem B894647 : Blo 595291 894647 := bstep (se 1 (by rfl) ⟨670985, by rfl⟩ : syracuseStep 894647 = 1341971) B1341971
theorem B894683 : Blo 595291 894683 := bstep (se 1 (by rfl) ⟨671012, by rfl⟩ : syracuseStep 894683 = 1342025) B1342025
theorem B4859651 : Blo 595291 4859651 := bstep (se 1 (by rfl) ⟨3644738, by rfl⟩ : syracuseStep 4859651 = 7289477) B7289477
theorem B894857 : Blo 595291 894857 := bstep (se 2 (by rfl) ⟨335571, by rfl⟩ : syracuseStep 894857 = 671143) B671143
theorem B894959 : Blo 595291 894959 := bstep (se 1 (by rfl) ⟨671219, by rfl⟩ : syracuseStep 894959 = 1342439) B1342439
theorem B895211 : Blo 595291 895211 := bstep (se 1 (by rfl) ⟨671408, by rfl⟩ : syracuseStep 895211 = 1342817) B1342817
theorem B895271 : Blo 595291 895271 := bstep (se 1 (by rfl) ⟨671453, by rfl⟩ : syracuseStep 895271 = 1342907) B1342907
theorem B895355 : Blo 595291 895355 := bstep (se 1 (by rfl) ⟨671516, by rfl⟩ : syracuseStep 895355 = 1343033) B1343033
theorem B2009501 : Blo 595291 2009501 := bstep (se 3 (by rfl) ⟨376781, by rfl⟩ : syracuseStep 2009501 = 753563) B753563
theorem B3222017 : Blo 595291 3222017 := bstep (se 2 (by rfl) ⟨1208256, by rfl⟩ : syracuseStep 3222017 = 2416513) B2416513
theorem B895625 : Blo 595291 895625 := bstep (se 2 (by rfl) ⟨335859, by rfl⟩ : syracuseStep 895625 = 671719) B671719
theorem B2009771 : Blo 595291 2009771 := bstep (se 1 (by rfl) ⟨1507328, by rfl⟩ : syracuseStep 2009771 = 3014657) B3014657
theorem B895799 : Blo 595291 895799 := bstep (se 1 (by rfl) ⟨671849, by rfl⟩ : syracuseStep 895799 = 1343699) B1343699
theorem B895835 : Blo 595291 895835 := bstep (se 1 (by rfl) ⟨671876, by rfl⟩ : syracuseStep 895835 = 1343753) B1343753
theorem B895979 : Blo 595291 895979 := bstep (se 1 (by rfl) ⟨671984, by rfl⟩ : syracuseStep 895979 = 1343969) B1343969
theorem B1092655 : Blo 595291 1092655 := bstep (se 1 (by rfl) ⟨819491, by rfl⟩ : syracuseStep 1092655 = 1638983) B1638983
theorem B896183 : Blo 595291 896183 := bstep (se 1 (by rfl) ⟨672137, by rfl⟩ : syracuseStep 896183 = 1344275) B1344275
theorem B2010311 : Blo 595291 2010311 := bstep (se 1 (by rfl) ⟨1507733, by rfl⟩ : syracuseStep 2010311 = 3015467) B3015467
theorem B9678041 : Blo 595291 9678041 := bstep (se 2 (by rfl) ⟨3629265, by rfl⟩ : syracuseStep 9678041 = 7258531) B7258531
theorem B2043215 : Blo 595291 2043215 := bstep (se 1 (by rfl) ⟨1532411, by rfl⟩ : syracuseStep 2043215 = 3064823) B3064823
theorem B896423 : Blo 595291 896423 := bstep (se 1 (by rfl) ⟨672317, by rfl⟩ : syracuseStep 896423 = 1344635) B1344635
theorem B896507 : Blo 595291 896507 := bstep (se 1 (by rfl) ⟨672380, by rfl⟩ : syracuseStep 896507 = 1344761) B1344761
theorem B896603 : Blo 595291 896603 := bstep (se 1 (by rfl) ⟨672452, by rfl⟩ : syracuseStep 896603 = 1344905) B1344905
theorem B896687 : Blo 595291 896687 := bstep (se 1 (by rfl) ⟨672515, by rfl⟩ : syracuseStep 896687 = 1345031) B1345031
theorem B1617583 : Blo 595291 1617583 := bstep (se 1 (by rfl) ⟨1213187, by rfl⟩ : syracuseStep 1617583 = 2426375) B2426375
theorem B896807 : Blo 595291 896807 := bstep (se 1 (by rfl) ⟨672605, by rfl⟩ : syracuseStep 896807 = 1345211) B1345211
theorem B896891 : Blo 595291 896891 := bstep (se 1 (by rfl) ⟨672668, by rfl⟩ : syracuseStep 896891 = 1345337) B1345337
theorem B39268253 : Blo 595291 39268253 := bstep (se 3 (by rfl) ⟨7362797, by rfl⟩ : syracuseStep 39268253 = 14725595) B14725595
theorem B864475 : Blo 595291 864475 := bstep (se 1 (by rfl) ⟨648356, by rfl⟩ : syracuseStep 864475 = 1296713) B1296713
theorem B897311 : Blo 595291 897311 := bstep (se 1 (by rfl) ⟨672983, by rfl⟩ : syracuseStep 897311 = 1345967) B1345967
theorem B897335 : Blo 595291 897335 := bstep (se 1 (by rfl) ⟨673001, by rfl⟩ : syracuseStep 897335 = 1346003) B1346003
theorem B897407 : Blo 595291 897407 := bstep (se 1 (by rfl) ⟨673055, by rfl⟩ : syracuseStep 897407 = 1346111) B1346111
theorem B4075919 : Blo 595291 4075919 := bstep (se 1 (by rfl) ⟨3056939, by rfl⟩ : syracuseStep 4075919 = 6113879) B6113879
theorem B897479 : Blo 595291 897479 := bstep (se 1 (by rfl) ⟨673109, by rfl⟩ : syracuseStep 897479 = 1346219) B1346219
theorem B2011607 : Blo 595291 2011607 := bstep (se 1 (by rfl) ⟨1508705, by rfl⟩ : syracuseStep 2011607 = 3017411) B3017411
theorem B4534865 : Blo 595291 4534865 := bstep (se 2 (by rfl) ⟨1700574, by rfl⟩ : syracuseStep 4534865 = 3401149) B3401149
theorem B1618535 : Blo 595291 1618535 := bstep (se 1 (by rfl) ⟨1213901, by rfl⟩ : syracuseStep 1618535 = 2427803) B2427803
theorem B897833 : Blo 595291 897833 := bstep (se 2 (by rfl) ⟨336687, by rfl⟩ : syracuseStep 897833 = 673375) B673375
theorem B897839 : Blo 595291 897839 := bstep (se 1 (by rfl) ⟨673379, by rfl⟩ : syracuseStep 897839 = 1346759) B1346759
theorem B897959 : Blo 595291 897959 := bstep (se 1 (by rfl) ⟨673469, by rfl⟩ : syracuseStep 897959 = 1346939) B1346939
theorem B898043 : Blo 595291 898043 := bstep (se 1 (by rfl) ⟨673532, by rfl⟩ : syracuseStep 898043 = 1347065) B1347065
theorem B898103 : Blo 595291 898103 := bstep (se 1 (by rfl) ⟨673577, by rfl⟩ : syracuseStep 898103 = 1347155) B1347155
theorem B898223 : Blo 595291 898223 := bstep (se 1 (by rfl) ⟨673667, by rfl⟩ : syracuseStep 898223 = 1347335) B1347335
theorem B898631 : Blo 595291 898631 := bstep (se 1 (by rfl) ⟨673973, by rfl⟩ : syracuseStep 898631 = 1347947) B1347947
theorem B898727 : Blo 595291 898727 := bstep (se 1 (by rfl) ⟨674045, by rfl⟩ : syracuseStep 898727 = 1348091) B1348091
theorem B898811 : Blo 595291 898811 := bstep (se 1 (by rfl) ⟨674108, by rfl⟩ : syracuseStep 898811 = 1348217) B1348217
theorem B898847 : Blo 595291 898847 := bstep (se 1 (by rfl) ⟨674135, by rfl⟩ : syracuseStep 898847 = 1348271) B1348271
theorem B898895 : Blo 595291 898895 := bstep (se 1 (by rfl) ⟨674171, by rfl⟩ : syracuseStep 898895 = 1348343) B1348343
theorem B2013065 : Blo 595291 2013065 := bstep (se 2 (by rfl) ⟨754899, by rfl⟩ : syracuseStep 2013065 = 1509799) B1509799
theorem B2865091 : Blo 595291 2865091 := bstep (se 1 (by rfl) ⟨2148818, by rfl⟩ : syracuseStep 2865091 = 4297637) B4297637
theorem B3029075 : Blo 595291 3029075 := bstep (se 1 (by rfl) ⟨2271806, by rfl⟩ : syracuseStep 3029075 = 4543613) B4543613
theorem B2013281 : Blo 595291 2013281 := bstep (se 2 (by rfl) ⟨754980, by rfl⟩ : syracuseStep 2013281 = 1509961) B1509961
theorem B2865415 : Blo 595291 2865415 := bstep (se 1 (by rfl) ⟨2149061, by rfl⟩ : syracuseStep 2865415 = 4298123) B4298123
theorem B3029561 : Blo 595291 3029561 := bstep (se 2 (by rfl) ⟨1136085, by rfl⟩ : syracuseStep 3029561 = 2272171) B2272171
theorem B4537295 : Blo 595291 4537295 := bstep (se 1 (by rfl) ⟨3402971, by rfl⟩ : syracuseStep 4537295 = 6805943) B6805943
theorem B2014199 : Blo 595291 2014199 := bstep (se 1 (by rfl) ⟨1510649, by rfl⟩ : syracuseStep 2014199 = 3021299) B3021299
theorem B2014631 : Blo 595291 2014631 := bstep (se 1 (by rfl) ⟨1510973, by rfl⟩ : syracuseStep 2014631 = 3021947) B3021947
theorem B1359335 : Blo 595291 1359335 := bstep (se 1 (by rfl) ⟨1019501, by rfl⟩ : syracuseStep 1359335 = 2039003) B2039003
theorem B671323 : Blo 595291 671323 := bstep (se 1 (by rfl) ⟨503492, by rfl⟩ : syracuseStep 671323 = 1006985) B1006985
theorem B999055 : Blo 595291 999055 := bstep (se 1 (by rfl) ⟨749291, by rfl⟩ : syracuseStep 999055 = 1498583) B1498583
theorem B2015063 : Blo 595291 2015063 := bstep (se 1 (by rfl) ⟨1511297, by rfl⟩ : syracuseStep 2015063 = 3022595) B3022595
theorem B671611 : Blo 595291 671611 := bstep (se 1 (by rfl) ⟨503708, by rfl⟩ : syracuseStep 671611 = 1007417) B1007417
theorem B2146439 : Blo 595291 2146439 := bstep (se 1 (by rfl) ⟨1609829, by rfl⟩ : syracuseStep 2146439 = 3219659) B3219659
theorem B2867339 : Blo 595291 2867339 := bstep (se 1 (by rfl) ⟨2150504, by rfl⟩ : syracuseStep 2867339 = 4301009) B4301009
theorem B12894551 : Blo 595291 12894551 := bstep (se 1 (by rfl) ⟨9670913, by rfl⟩ : syracuseStep 12894551 = 19341827) B19341827
theorem B3686975 : Blo 595291 3686975 := bstep (se 1 (by rfl) ⟨2765231, by rfl⟩ : syracuseStep 3686975 = 5530463) B5530463
theorem B2015873 : Blo 595291 2015873 := bstep (se 2 (by rfl) ⟨755952, by rfl⟩ : syracuseStep 2015873 = 1511905) B1511905
theorem B6144749 : Blo 595291 6144749 := bstep (se 3 (by rfl) ⟨1152140, by rfl⟩ : syracuseStep 6144749 = 2304281) B2304281
theorem B2048825 : Blo 595291 2048825 := bstep (se 2 (by rfl) ⟨768309, by rfl⟩ : syracuseStep 2048825 = 1536619) B1536619
theorem B3621775 : Blo 595291 3621775 := bstep (se 1 (by rfl) ⟨2716331, by rfl⟩ : syracuseStep 3621775 = 5432663) B5432663
theorem B2016143 : Blo 595291 2016143 := bstep (se 1 (by rfl) ⟨1512107, by rfl⟩ : syracuseStep 2016143 = 3024215) B3024215
theorem B672763 : Blo 595291 672763 := bstep (se 1 (by rfl) ⟨504572, by rfl⟩ : syracuseStep 672763 = 1009145) B1009145
theorem B672943 : Blo 595291 672943 := bstep (se 1 (by rfl) ⟨504707, by rfl⟩ : syracuseStep 672943 = 1009415) B1009415
theorem B1131727 : Blo 595291 1131727 := bstep (se 1 (by rfl) ⟨848795, by rfl⟩ : syracuseStep 1131727 = 1697591) B1697591
theorem B2016683 : Blo 595291 2016683 := bstep (se 1 (by rfl) ⟨1512512, by rfl⟩ : syracuseStep 2016683 = 3025025) B3025025
theorem B2049455 : Blo 595291 2049455 := bstep (se 1 (by rfl) ⟨1537091, by rfl⟩ : syracuseStep 2049455 = 3074183) B3074183
theorem B3229345 : Blo 595291 3229345 := bstep (se 2 (by rfl) ⟨1211004, by rfl⟩ : syracuseStep 3229345 = 2422009) B2422009
theorem B673447 : Blo 595291 673447 := bstep (se 1 (by rfl) ⟨505085, by rfl⟩ : syracuseStep 673447 = 1010171) B1010171
theorem B1132319 : Blo 595291 1132319 := bstep (se 1 (by rfl) ⟨849239, by rfl⟩ : syracuseStep 1132319 = 1698479) B1698479
theorem B3393359 : Blo 595291 3393359 := bstep (se 1 (by rfl) ⟨2545019, by rfl⟩ : syracuseStep 3393359 = 5090039) B5090039
theorem B2017223 : Blo 595291 2017223 := bstep (se 1 (by rfl) ⟨1512917, by rfl⟩ : syracuseStep 2017223 = 3025835) B3025835
theorem B673735 : Blo 595291 673735 := bstep (se 1 (by rfl) ⟨505301, by rfl⟩ : syracuseStep 673735 = 1010603) B1010603
theorem B4900837 : Blo 595291 4900837 := bstep (se 4 (by rfl) ⟨459453, by rfl⟩ : syracuseStep 4900837 = 918907) B918907
theorem B674095 : Blo 595291 674095 := bstep (se 1 (by rfl) ⟨505571, by rfl⟩ : syracuseStep 674095 = 1011143) B1011143
theorem B8735035 : Blo 595291 8735035 := bstep (se 1 (by rfl) ⟨6551276, by rfl⟩ : syracuseStep 8735035 = 13102553) B13102553
theorem B1919389 : Blo 595291 1919389 := bstep (se 3 (by rfl) ⟨359885, by rfl⟩ : syracuseStep 1919389 = 719771) B719771
theorem B2017979 : Blo 595291 2017979 := bstep (se 1 (by rfl) ⟨1513484, by rfl⟩ : syracuseStep 2017979 = 3026969) B3026969
theorem B4312399 : Blo 595291 4312399 := bstep (se 1 (by rfl) ⟨3234299, by rfl⟩ : syracuseStep 4312399 = 6468599) B6468599
theorem B3395135 : Blo 595291 3395135 := bstep (se 1 (by rfl) ⟨2546351, by rfl⟩ : syracuseStep 3395135 = 5092703) B5092703
theorem B8867501 : Blo 595291 8867501 := bstep (se 3 (by rfl) ⟨1662656, by rfl⟩ : syracuseStep 8867501 = 3325313) B3325313
theorem B1134985 : Blo 595291 1134985 := bstep (se 2 (by rfl) ⟨425619, by rfl⟩ : syracuseStep 1134985 = 851239) B851239
theorem B2019923 : Blo 595291 2019923 := bstep (se 1 (by rfl) ⟨1514942, by rfl⟩ : syracuseStep 2019923 = 3029885) B3029885
theorem B1430401 : Blo 595291 1430401 := bstep (se 2 (by rfl) ⟨536400, by rfl⟩ : syracuseStep 1430401 = 1072801) B1072801
theorem B2020571 : Blo 595291 2020571 := bstep (se 1 (by rfl) ⟨1515428, by rfl⟩ : syracuseStep 2020571 = 3030857) B3030857
theorem B2545121 : Blo 595291 2545121 := bstep (se 2 (by rfl) ⟨954420, by rfl⟩ : syracuseStep 2545121 = 1908841) B1908841
theorem B1005223 : Blo 595291 1005223 := bstep (se 1 (by rfl) ⟨753917, by rfl⟩ : syracuseStep 1005223 = 1507835) B1507835
theorem B3889079 : Blo 595291 3889079 := bstep (se 1 (by rfl) ⟨2916809, by rfl⟩ : syracuseStep 3889079 = 5833619) B5833619
theorem B2021435 : Blo 595291 2021435 := bstep (se 1 (by rfl) ⟨1516076, by rfl⟩ : syracuseStep 2021435 = 3032153) B3032153
theorem B1431785 : Blo 595291 1431785 := bstep (se 2 (by rfl) ⟨536919, by rfl⟩ : syracuseStep 1431785 = 1073839) B1073839
theorem B1005871 : Blo 595291 1005871 := bstep (se 1 (by rfl) ⟨754403, by rfl⟩ : syracuseStep 1005871 = 1508807) B1508807
theorem B2021705 : Blo 595291 2021705 := bstep (se 2 (by rfl) ⟨758139, by rfl⟩ : syracuseStep 2021705 = 1516279) B1516279
theorem B1431931 : Blo 595291 1431931 := bstep (se 1 (by rfl) ⟨1073948, by rfl⟩ : syracuseStep 1431931 = 2147897) B2147897
theorem B3398233 : Blo 595291 3398233 := bstep (se 2 (by rfl) ⟨1274337, by rfl⟩ : syracuseStep 3398233 = 2548675) B2548675
theorem B4086409 : Blo 595291 4086409 := bstep (se 2 (by rfl) ⟨1532403, by rfl⟩ : syracuseStep 4086409 = 3064807) B3064807
theorem B1006391 : Blo 595291 1006391 := bstep (se 1 (by rfl) ⟨754793, by rfl⟩ : syracuseStep 1006391 = 1509587) B1509587
theorem B4906099 : Blo 595291 4906099 := bstep (se 1 (by rfl) ⟨3679574, by rfl⟩ : syracuseStep 4906099 = 7359149) B7359149
theorem B1007167 : Blo 595291 1007167 := bstep (se 1 (by rfl) ⟨755375, by rfl⟩ : syracuseStep 1007167 = 1510751) B1510751
theorem B4087741 : Blo 595291 4087741 := bstep (se 3 (by rfl) ⟨766451, by rfl⟩ : syracuseStep 4087741 = 1532903) B1532903
theorem B10182671 : Blo 595291 10182671 := bstep (se 1 (by rfl) ⟨7637003, by rfl⟩ : syracuseStep 10182671 = 15274007) B15274007
theorem B3825883 : Blo 595291 3825883 := bstep (se 1 (by rfl) ⟨2869412, by rfl⟩ : syracuseStep 3825883 = 5738825) B5738825
theorem B1007903 : Blo 595291 1007903 := bstep (se 1 (by rfl) ⟨755927, by rfl⟩ : syracuseStep 1007903 = 1511855) B1511855
theorem B4842395 : Blo 595291 4842395 := bstep (se 1 (by rfl) ⟨3631796, by rfl⟩ : syracuseStep 4842395 = 7263593) B7263593
theorem B1008551 : Blo 595291 1008551 := bstep (se 1 (by rfl) ⟨756413, by rfl⟩ : syracuseStep 1008551 = 1512827) B1512827
theorem B1008713 : Blo 595291 1008713 := bstep (se 2 (by rfl) ⟨378267, by rfl⟩ : syracuseStep 1008713 = 756535) B756535
theorem B1697375 : Blo 595291 1697375 := bstep (se 1 (by rfl) ⟨1273031, by rfl⟩ : syracuseStep 1697375 = 2546063) B2546063
theorem B1009273 : Blo 595291 1009273 := bstep (se 2 (by rfl) ⟨378477, by rfl⟩ : syracuseStep 1009273 = 756955) B756955
theorem B911015 : Blo 595291 911015 := bstep (se 1 (by rfl) ⟨683261, by rfl⟩ : syracuseStep 911015 = 1366523) B1366523
theorem B1435591 : Blo 595291 1435591 := bstep (se 1 (by rfl) ⟨1076693, by rfl⟩ : syracuseStep 1435591 = 2153387) B2153387
theorem B1009759 : Blo 595291 1009759 := bstep (se 1 (by rfl) ⟨757319, by rfl⟩ : syracuseStep 1009759 = 1514639) B1514639
theorem B16345273 : Blo 595291 16345273 := bstep (se 2 (by rfl) ⟨6129477, by rfl⟩ : syracuseStep 16345273 = 12258955) B12258955
theorem B12249353 : Blo 595291 12249353 := bstep (se 2 (by rfl) ⟨4593507, by rfl⟩ : syracuseStep 12249353 = 9187015) B9187015
theorem B1632673 : Blo 595291 1632673 := bstep (se 2 (by rfl) ⟨612252, by rfl⟩ : syracuseStep 1632673 = 1224505) B1224505
theorem B2550521 : Blo 595291 2550521 := bstep (se 2 (by rfl) ⟨956445, by rfl⟩ : syracuseStep 2550521 = 1912891) B1912891
theorem B7629623 : Blo 595291 7629623 := bstep (se 1 (by rfl) ⟨5722217, by rfl⟩ : syracuseStep 7629623 = 11444435) B11444435
theorem B1699015 : Blo 595291 1699015 := bstep (se 1 (by rfl) ⟨1274261, by rfl⟩ : syracuseStep 1699015 = 2548523) B2548523
theorem B1699049 : Blo 595291 1699049 := bstep (se 2 (by rfl) ⟨637143, by rfl⟩ : syracuseStep 1699049 = 1274287) B1274287
theorem B1011055 : Blo 595291 1011055 := bstep (se 1 (by rfl) ⟨758291, by rfl⟩ : syracuseStep 1011055 = 1516583) B1516583
theorem B1076809 : Blo 595291 1076809 := bstep (se 2 (by rfl) ⟨403803, by rfl⟩ : syracuseStep 1076809 = 807607) B807607
theorem B52194941 : Blo 595291 52194941 := bstep (se 3 (by rfl) ⟨9786551, by rfl⟩ : syracuseStep 52194941 = 19573103) B19573103
theorem B3829679 : Blo 595291 3829679 := bstep (se 1 (by rfl) ⟨2872259, by rfl⟩ : syracuseStep 3829679 = 5744519) B5744519
theorem B5435585 : Blo 595291 5435585 := bstep (se 2 (by rfl) ⟨2038344, by rfl⟩ : syracuseStep 5435585 = 4076689) B4076689
theorem B2552093 : Blo 595291 2552093 := bstep (se 3 (by rfl) ⟨478517, by rfl⟩ : syracuseStep 2552093 = 957035) B957035
theorem B1339703 : Blo 595291 1339703 := bstep (se 1 (by rfl) ⟨1004777, by rfl⟩ : syracuseStep 1339703 = 2009555) B2009555
theorem B1274167 : Blo 595291 1274167 := bstep (se 1 (by rfl) ⟨955625, by rfl⟩ : syracuseStep 1274167 = 1911251) B1911251
theorem B1536311 : Blo 595291 1536311 := bstep (se 1 (by rfl) ⟨1152233, by rfl⟩ : syracuseStep 1536311 = 2304467) B2304467
theorem B1339775 : Blo 595291 1339775 := bstep (se 1 (by rfl) ⟨1004831, by rfl⟩ : syracuseStep 1339775 = 2009663) B2009663
theorem B58192789 : Blo 595291 58192789 := bstep (se 6 (by rfl) ⟨1363893, by rfl⟩ : syracuseStep 58192789 = 2727787) B2727787
theorem B1274953 : Blo 595291 1274953 := bstep (se 2 (by rfl) ⟨478107, by rfl⟩ : syracuseStep 1274953 = 956215) B956215
theorem B1274987 : Blo 595291 1274987 := bstep (se 1 (by rfl) ⟨956240, by rfl⟩ : syracuseStep 1274987 = 1912481) B1912481
theorem B2159891 : Blo 595291 2159891 := bstep (se 1 (by rfl) ⟨1619918, by rfl⟩ : syracuseStep 2159891 = 3239837) B3239837
theorem B1340999 : Blo 595291 1340999 := bstep (se 1 (by rfl) ⟨1005749, by rfl⟩ : syracuseStep 1340999 = 2011499) B2011499
theorem B3405523 : Blo 595291 3405523 := bstep (se 1 (by rfl) ⟨2554142, by rfl⟩ : syracuseStep 3405523 = 5108285) B5108285
theorem B718555 : Blo 595291 718555 := bstep (se 1 (by rfl) ⟨538916, by rfl⟩ : syracuseStep 718555 = 1077833) B1077833
theorem B1341179 : Blo 595291 1341179 := bstep (se 1 (by rfl) ⟨1005884, by rfl⟩ : syracuseStep 1341179 = 2011769) B2011769
theorem B6616849 : Blo 595291 6616849 := bstep (se 2 (by rfl) ⟨2481318, by rfl⟩ : syracuseStep 6616849 = 4962637) B4962637
theorem B849695 : Blo 595291 849695 := bstep (se 1 (by rfl) ⟨637271, by rfl⟩ : syracuseStep 849695 = 1274543) B1274543
theorem B4847849 : Blo 595291 4847849 := bstep (se 2 (by rfl) ⟨1817943, by rfl⟩ : syracuseStep 4847849 = 3635887) B3635887
theorem B23263499 : Blo 595291 23263499 := bstep (se 1 (by rfl) ⟨17447624, by rfl⟩ : syracuseStep 23263499 = 34895249) B34895249
theorem B1341737 : Blo 595291 1341737 := bstep (se 2 (by rfl) ⟨503151, by rfl⟩ : syracuseStep 1341737 = 1006303) B1006303
theorem B3275117 : Blo 595291 3275117 := bstep (se 3 (by rfl) ⟨614084, by rfl⟩ : syracuseStep 3275117 = 1228169) B1228169
theorem B6388079 : Blo 595291 6388079 := bstep (se 1 (by rfl) ⟨4791059, by rfl⟩ : syracuseStep 6388079 = 9582119) B9582119
theorem B4192847 : Blo 595291 4192847 := bstep (se 1 (by rfl) ⟨3144635, by rfl⟩ : syracuseStep 4192847 = 6289271) B6289271
theorem B1342313 : Blo 595291 1342313 := bstep (se 2 (by rfl) ⟨503367, by rfl⟩ : syracuseStep 1342313 = 1006735) B1006735
theorem B1342367 : Blo 595291 1342367 := bstep (se 1 (by rfl) ⟨1006775, by rfl⟩ : syracuseStep 1342367 = 2013551) B2013551
theorem B3406799 : Blo 595291 3406799 := bstep (se 1 (by rfl) ⟨2555099, by rfl⟩ : syracuseStep 3406799 = 5110199) B5110199
theorem B6913309 : Blo 595291 6913309 := bstep (se 3 (by rfl) ⟨1296245, by rfl⟩ : syracuseStep 6913309 = 2592491) B2592491
theorem B1703207 : Blo 595291 1703207 := bstep (se 1 (by rfl) ⟨1277405, by rfl⟩ : syracuseStep 1703207 = 2554811) B2554811
theorem B1703263 : Blo 595291 1703263 := bstep (se 1 (by rfl) ⟨1277447, by rfl⟩ : syracuseStep 1703263 = 2554895) B2554895
theorem B12942803 : Blo 595291 12942803 := bstep (se 1 (by rfl) ⟨9707102, by rfl⟩ : syracuseStep 12942803 = 19414205) B19414205
theorem B3505619 : Blo 595291 3505619 := bstep (se 1 (by rfl) ⟨2629214, by rfl⟩ : syracuseStep 3505619 = 5258429) B5258429
theorem B851563 : Blo 595291 851563 := bstep (se 1 (by rfl) ⟨638672, by rfl⟩ : syracuseStep 851563 = 1277345) B1277345
theorem B1277687 : Blo 595291 1277687 := bstep (se 1 (by rfl) ⟨958265, by rfl⟩ : syracuseStep 1277687 = 1916531) B1916531
theorem B1343303 : Blo 595291 1343303 := bstep (se 1 (by rfl) ⟨1007477, by rfl⟩ : syracuseStep 1343303 = 2014955) B2014955
theorem B2555819 : Blo 595291 2555819 := bstep (se 1 (by rfl) ⟨1916864, by rfl⟩ : syracuseStep 2555819 = 3833729) B3833729
theorem B12451843 : Blo 595291 12451843 := bstep (se 1 (by rfl) ⟨9338882, by rfl⟩ : syracuseStep 12451843 = 18677765) B18677765
theorem B2457983 : Blo 595291 2457983 := bstep (se 1 (by rfl) ⟨1843487, by rfl⟩ : syracuseStep 2457983 = 3686975) B3686975
theorem B1343915 : Blo 595291 1343915 := bstep (se 1 (by rfl) ⟨1007936, by rfl⟩ : syracuseStep 1343915 = 2015873) B2015873
theorem B4096499 : Blo 595291 4096499 := bstep (se 1 (by rfl) ⟨3072374, by rfl⟩ : syracuseStep 4096499 = 6144749) B6144749
theorem B1344095 : Blo 595291 1344095 := bstep (se 1 (by rfl) ⟨1008071, by rfl⟩ : syracuseStep 1344095 = 2016143) B2016143
theorem B1344455 : Blo 595291 1344455 := bstep (se 1 (by rfl) ⟨1008341, by rfl⟩ : syracuseStep 1344455 = 2016683) B2016683
theorem B1278985 : Blo 595291 1278985 := bstep (se 2 (by rfl) ⟨479619, by rfl⟩ : syracuseStep 1278985 = 959239) B959239
theorem B2262239 : Blo 595291 2262239 := bstep (se 1 (by rfl) ⟨1696679, by rfl⟩ : syracuseStep 2262239 = 3393359) B3393359
theorem B1311967 : Blo 595291 1311967 := bstep (se 1 (by rfl) ⟨983975, by rfl⟩ : syracuseStep 1311967 = 1967951) B1967951
theorem B1344815 : Blo 595291 1344815 := bstep (se 1 (by rfl) ⟨1008611, by rfl⟩ : syracuseStep 1344815 = 2017223) B2017223
theorem B1508969 : Blo 595291 1508969 := bstep (se 2 (by rfl) ⟨565863, by rfl⟩ : syracuseStep 1508969 = 1131727) B1131727
theorem B1345319 : Blo 595291 1345319 := bstep (se 1 (by rfl) ⟨1008989, by rfl⟩ : syracuseStep 1345319 = 2017979) B2017979
theorem B1509263 : Blo 595291 1509263 := bstep (se 1 (by rfl) ⟨1131947, by rfl⟩ : syracuseStep 1509263 = 2263895) B2263895
theorem B1345697 : Blo 595291 1345697 := bstep (se 2 (by rfl) ⟨504636, by rfl⟩ : syracuseStep 1345697 = 1009273) B1009273
theorem B2263423 : Blo 595291 2263423 := bstep (se 1 (by rfl) ⟨1697567, by rfl⟩ : syracuseStep 2263423 = 3395135) B3395135
theorem B1346345 : Blo 595291 1346345 := bstep (se 2 (by rfl) ⟨504879, by rfl⟩ : syracuseStep 1346345 = 1009759) B1009759
theorem B21793697 : Blo 595291 21793697 := bstep (se 2 (by rfl) ⟨8172636, by rfl⟩ : syracuseStep 21793697 = 16345273) B16345273
theorem B1346615 : Blo 595291 1346615 := bstep (se 1 (by rfl) ⟨1009961, by rfl⟩ : syracuseStep 1346615 = 2019923) B2019923
theorem B2559185 : Blo 595291 2559185 := bstep (se 2 (by rfl) ⟨959694, by rfl⟩ : syracuseStep 2559185 = 1919389) B1919389
theorem B2624723 : Blo 595291 2624723 := bstep (se 1 (by rfl) ⟨1968542, by rfl⟩ : syracuseStep 2624723 = 3937085) B3937085
theorem B1347047 : Blo 595291 1347047 := bstep (se 1 (by rfl) ⟨1010285, by rfl⟩ : syracuseStep 1347047 = 2020571) B2020571
theorem B6786989 : Blo 595291 6786989 := bstep (se 3 (by rfl) ⟨1272560, by rfl⟩ : syracuseStep 6786989 = 2545121) B2545121
theorem B2592719 : Blo 595291 2592719 := bstep (se 1 (by rfl) ⟨1944539, by rfl⟩ : syracuseStep 2592719 = 3889079) B3889079
theorem B1347623 : Blo 595291 1347623 := bstep (se 1 (by rfl) ⟨1010717, by rfl⟩ : syracuseStep 1347623 = 2021435) B2021435
theorem B1511531 : Blo 595291 1511531 := bstep (se 1 (by rfl) ⟨1133648, by rfl⟩ : syracuseStep 1511531 = 2267297) B2267297
theorem B954523 : Blo 595291 954523 := bstep (se 1 (by rfl) ⟨715892, by rfl⟩ : syracuseStep 954523 = 1431785) B1431785
theorem B1347803 : Blo 595291 1347803 := bstep (se 1 (by rfl) ⟨1010852, by rfl⟩ : syracuseStep 1347803 = 2021705) B2021705
theorem B2265353 : Blo 595291 2265353 := bstep (se 2 (by rfl) ⟨849507, by rfl⟩ : syracuseStep 2265353 = 1699015) B1699015
theorem B1348073 : Blo 595291 1348073 := bstep (se 2 (by rfl) ⟨505527, by rfl⟩ : syracuseStep 1348073 = 1011055) B1011055
theorem B3019517 : Blo 595291 3019517 := bstep (se 3 (by rfl) ⟨566159, by rfl⟩ : syracuseStep 3019517 = 1132319) B1132319
theorem B2265853 : Blo 595291 2265853 := bstep (se 3 (by rfl) ⟨424847, by rfl⟩ : syracuseStep 2265853 = 849695) B849695
theorem B3019679 : Blo 595291 3019679 := bstep (se 1 (by rfl) ⟨2264759, by rfl⟩ : syracuseStep 3019679 = 4529519) B4529519
theorem B6788447 : Blo 595291 6788447 := bstep (se 1 (by rfl) ⟨5091335, by rfl⟩ : syracuseStep 6788447 = 10182671) B10182671
theorem B595431 : Blo 595291 595431 := bstep (se 1 (by rfl) ⟨446573, by rfl⟩ : syracuseStep 595431 = 893147) B893147
theorem B595439 : Blo 595291 595439 := bstep (se 1 (by rfl) ⟨446579, by rfl⟩ : syracuseStep 595439 = 893159) B893159
theorem B1513039 : Blo 595291 1513039 := bstep (se 1 (by rfl) ⟨1134779, by rfl⟩ : syracuseStep 1513039 = 2269559) B2269559
theorem B595547 : Blo 595291 595547 := bstep (se 1 (by rfl) ⟨446660, by rfl⟩ : syracuseStep 595547 = 893321) B893321
theorem B595611 : Blo 595291 595611 := bstep (se 1 (by rfl) ⟨446708, by rfl⟩ : syracuseStep 595611 = 893417) B893417
theorem B595695 : Blo 595291 595695 := bstep (se 1 (by rfl) ⟨446771, by rfl⟩ : syracuseStep 595695 = 893543) B893543
theorem B595783 : Blo 595291 595783 := bstep (se 1 (by rfl) ⟨446837, by rfl⟩ : syracuseStep 595783 = 893675) B893675
theorem B595803 : Blo 595291 595803 := bstep (se 1 (by rfl) ⟨446852, by rfl⟩ : syracuseStep 595803 = 893705) B893705
theorem B1513313 : Blo 595291 1513313 := bstep (se 2 (by rfl) ⟨567492, by rfl⟩ : syracuseStep 1513313 = 1134985) B1134985
theorem B595871 : Blo 595291 595871 := bstep (se 1 (by rfl) ⟨446903, by rfl⟩ : syracuseStep 595871 = 893807) B893807
theorem B596039 : Blo 595291 596039 := bstep (se 1 (by rfl) ⟨447029, by rfl⟩ : syracuseStep 596039 = 894059) B894059
theorem B1513687 : Blo 595291 1513687 := bstep (se 1 (by rfl) ⟨1135265, by rfl⟩ : syracuseStep 1513687 = 2270531) B2270531
theorem B596199 : Blo 595291 596199 := bstep (se 1 (by rfl) ⟨447149, by rfl⟩ : syracuseStep 596199 = 894299) B894299
theorem B596383 : Blo 595291 596383 := bstep (se 1 (by rfl) ⟨447287, by rfl⟩ : syracuseStep 596383 = 894575) B894575
theorem B4528547 : Blo 595291 4528547 := bstep (se 1 (by rfl) ⟨3396410, by rfl⟩ : syracuseStep 4528547 = 6792821) B6792821
theorem B596431 : Blo 595291 596431 := bstep (se 1 (by rfl) ⟨447323, by rfl⟩ : syracuseStep 596431 = 894647) B894647
theorem B596455 : Blo 595291 596455 := bstep (se 1 (by rfl) ⟨447341, by rfl⟩ : syracuseStep 596455 = 894683) B894683
theorem B1907201 : Blo 595291 1907201 := bstep (se 2 (by rfl) ⟨715200, by rfl⟩ : syracuseStep 1907201 = 1430401) B1430401
theorem B596571 : Blo 595291 596571 := bstep (se 1 (by rfl) ⟨447428, by rfl⟩ : syracuseStep 596571 = 894857) B894857
theorem B596639 : Blo 595291 596639 := bstep (se 1 (by rfl) ⟨447479, by rfl⟩ : syracuseStep 596639 = 894959) B894959
theorem B596807 : Blo 595291 596807 := bstep (se 1 (by rfl) ⟨447605, by rfl⟩ : syracuseStep 596807 = 895211) B895211
theorem B596847 : Blo 595291 596847 := bstep (se 1 (by rfl) ⟨447635, by rfl⟩ : syracuseStep 596847 = 895271) B895271
theorem B596903 : Blo 595291 596903 := bstep (se 1 (by rfl) ⟨447677, by rfl⟩ : syracuseStep 596903 = 895355) B895355
theorem B597083 : Blo 595291 597083 := bstep (se 1 (by rfl) ⟨447812, by rfl⟩ : syracuseStep 597083 = 895625) B895625
theorem B5086415 : Blo 595291 5086415 := bstep (se 1 (by rfl) ⟨3814811, by rfl⟩ : syracuseStep 5086415 = 7629623) B7629623
theorem B597199 : Blo 595291 597199 := bstep (se 1 (by rfl) ⟨447899, by rfl⟩ : syracuseStep 597199 = 895799) B895799
theorem B597223 : Blo 595291 597223 := bstep (se 1 (by rfl) ⟨447917, by rfl⟩ : syracuseStep 597223 = 895835) B895835
theorem B597319 : Blo 595291 597319 := bstep (se 1 (by rfl) ⟨447989, by rfl⟩ : syracuseStep 597319 = 895979) B895979
theorem B597455 : Blo 595291 597455 := bstep (se 1 (by rfl) ⟨448091, by rfl⟩ : syracuseStep 597455 = 896183) B896183
theorem B597615 : Blo 595291 597615 := bstep (se 1 (by rfl) ⟨448211, by rfl⟩ : syracuseStep 597615 = 896423) B896423
theorem B958073 : Blo 595291 958073 := bstep (se 2 (by rfl) ⟨359277, by rfl⟩ : syracuseStep 958073 = 718555) B718555
theorem B597671 : Blo 595291 597671 := bstep (se 1 (by rfl) ⟨448253, by rfl⟩ : syracuseStep 597671 = 896507) B896507
theorem B8822465 : Blo 595291 8822465 := bstep (se 2 (by rfl) ⟨3308424, by rfl⟩ : syracuseStep 8822465 = 6616849) B6616849
theorem B597735 : Blo 595291 597735 := bstep (se 1 (by rfl) ⟨448301, by rfl⟩ : syracuseStep 597735 = 896603) B896603
theorem B597791 : Blo 595291 597791 := bstep (se 1 (by rfl) ⟨448343, by rfl⟩ : syracuseStep 597791 = 896687) B896687
theorem B597871 : Blo 595291 597871 := bstep (se 1 (by rfl) ⟨448403, by rfl⟩ : syracuseStep 597871 = 896807) B896807
theorem B597927 : Blo 595291 597927 := bstep (se 1 (by rfl) ⟨448445, by rfl⟩ : syracuseStep 597927 = 896891) B896891
theorem B4989053 : Blo 595291 4989053 := bstep (se 3 (by rfl) ⟨935447, by rfl⟩ : syracuseStep 4989053 = 1870895) B1870895
theorem B598207 : Blo 595291 598207 := bstep (se 1 (by rfl) ⟨448655, by rfl⟩ : syracuseStep 598207 = 897311) B897311
theorem B893135 : Blo 595291 893135 := bstep (se 1 (by rfl) ⟨669851, by rfl⟩ : syracuseStep 893135 = 1339703) B1339703
theorem B598223 : Blo 595291 598223 := bstep (se 1 (by rfl) ⟨448667, by rfl⟩ : syracuseStep 598223 = 897335) B897335
theorem B1024207 : Blo 595291 1024207 := bstep (se 1 (by rfl) ⟨768155, by rfl⟩ : syracuseStep 1024207 = 1536311) B1536311
theorem B893183 : Blo 595291 893183 := bstep (se 1 (by rfl) ⟨669887, by rfl⟩ : syracuseStep 893183 = 1339775) B1339775
theorem B598271 : Blo 595291 598271 := bstep (se 1 (by rfl) ⟨448703, by rfl⟩ : syracuseStep 598271 = 897407) B897407
theorem B598319 : Blo 595291 598319 := bstep (se 1 (by rfl) ⟨448739, by rfl⟩ : syracuseStep 598319 = 897479) B897479
theorem B3023243 : Blo 595291 3023243 := bstep (se 1 (by rfl) ⟨2267432, by rfl⟩ : syracuseStep 3023243 = 4534865) B4534865
theorem B1909241 : Blo 595291 1909241 := bstep (se 2 (by rfl) ⟨715965, by rfl⟩ : syracuseStep 1909241 = 1431931) B1431931
theorem B598555 : Blo 595291 598555 := bstep (se 1 (by rfl) ⟨448916, by rfl⟩ : syracuseStep 598555 = 897833) B897833
theorem B598559 : Blo 595291 598559 := bstep (se 1 (by rfl) ⟨448919, by rfl⟩ : syracuseStep 598559 = 897839) B897839
theorem B598639 : Blo 595291 598639 := bstep (se 1 (by rfl) ⟨448979, by rfl⟩ : syracuseStep 598639 = 897959) B897959
theorem B598695 : Blo 595291 598695 := bstep (se 1 (by rfl) ⟨449021, by rfl⟩ : syracuseStep 598695 = 898043) B898043
theorem B598735 : Blo 595291 598735 := bstep (se 1 (by rfl) ⟨449051, by rfl⟩ : syracuseStep 598735 = 898103) B898103
theorem B598815 : Blo 595291 598815 := bstep (se 1 (by rfl) ⟨449111, by rfl⟩ : syracuseStep 598815 = 898223) B898223
theorem B4530977 : Blo 595291 4530977 := bstep (se 2 (by rfl) ⟨1699116, by rfl⟩ : syracuseStep 4530977 = 3398233) B3398233
theorem B5448545 : Blo 595291 5448545 := bstep (se 2 (by rfl) ⟨2043204, by rfl⟩ : syracuseStep 5448545 = 4086409) B4086409
theorem B893999 : Blo 595291 893999 := bstep (se 1 (by rfl) ⟨670499, by rfl⟩ : syracuseStep 893999 = 1340999) B1340999
theorem B599087 : Blo 595291 599087 := bstep (se 1 (by rfl) ⟨449315, by rfl⟩ : syracuseStep 599087 = 898631) B898631
theorem B599151 : Blo 595291 599151 := bstep (se 1 (by rfl) ⟨449363, by rfl⟩ : syracuseStep 599151 = 898727) B898727
theorem B894119 : Blo 595291 894119 := bstep (se 1 (by rfl) ⟨670589, by rfl⟩ : syracuseStep 894119 = 1341179) B1341179
theorem B599207 : Blo 595291 599207 := bstep (se 1 (by rfl) ⟨449405, by rfl⟩ : syracuseStep 599207 = 898811) B898811
theorem B599231 : Blo 595291 599231 := bstep (se 1 (by rfl) ⟨449423, by rfl⟩ : syracuseStep 599231 = 898847) B898847
theorem B9348317 : Blo 595291 9348317 := bstep (se 3 (by rfl) ⟨1752809, by rfl⟩ : syracuseStep 9348317 = 3505619) B3505619
theorem B599263 : Blo 595291 599263 := bstep (se 1 (by rfl) ⟨449447, by rfl⟩ : syracuseStep 599263 = 898895) B898895
theorem B15508999 : Blo 595291 15508999 := bstep (se 1 (by rfl) ⟨11631749, by rfl⟩ : syracuseStep 15508999 = 23263499) B23263499
theorem B894491 : Blo 595291 894491 := bstep (se 1 (by rfl) ⟨670868, by rfl⟩ : syracuseStep 894491 = 1341737) B1341737
theorem B9217745 : Blo 595291 9217745 := bstep (se 2 (by rfl) ⟨3456654, by rfl⟩ : syracuseStep 9217745 = 6913309) B6913309
theorem B2795231 : Blo 595291 2795231 := bstep (se 1 (by rfl) ⟨2096423, by rfl⟩ : syracuseStep 2795231 = 4192847) B4192847
theorem B2271017 : Blo 595291 2271017 := bstep (se 2 (by rfl) ⟨851631, by rfl⟩ : syracuseStep 2271017 = 1703263) B1703263
theorem B894875 : Blo 595291 894875 := bstep (se 1 (by rfl) ⟨671156, by rfl⟩ : syracuseStep 894875 = 1342313) B1342313
theorem B894911 : Blo 595291 894911 := bstep (se 1 (by rfl) ⟨671183, by rfl⟩ : syracuseStep 894911 = 1342367) B1342367
theorem B3024863 : Blo 595291 3024863 := bstep (se 1 (by rfl) ⟨2268647, by rfl⟩ : syracuseStep 3024863 = 4537295) B4537295
theorem B2271199 : Blo 595291 2271199 := bstep (se 1 (by rfl) ⟨1703399, by rfl⟩ : syracuseStep 2271199 = 3406799) B3406799
theorem B895097 : Blo 595291 895097 := bstep (se 2 (by rfl) ⟨335661, by rfl⟩ : syracuseStep 895097 = 671323) B671323
theorem B8628535 : Blo 595291 8628535 := bstep (se 1 (by rfl) ⟨6471401, by rfl⟩ : syracuseStep 8628535 = 12942803) B12942803
theorem B895481 : Blo 595291 895481 := bstep (se 2 (by rfl) ⟨335805, by rfl⟩ : syracuseStep 895481 = 671611) B671611
theorem B895535 : Blo 595291 895535 := bstep (se 1 (by rfl) ⟨671651, by rfl⟩ : syracuseStep 895535 = 1343303) B1343303
theorem B5450321 : Blo 595291 5450321 := bstep (se 2 (by rfl) ⟨2043870, by rfl⟩ : syracuseStep 5450321 = 4087741) B4087741
theorem B4827863 : Blo 595291 4827863 := bstep (se 1 (by rfl) ⟨3620897, by rfl⟩ : syracuseStep 4827863 = 7241795) B7241795
theorem B1911559 : Blo 595291 1911559 := bstep (se 1 (by rfl) ⟨1433669, by rfl⟩ : syracuseStep 1911559 = 2867339) B2867339
theorem B8596367 : Blo 595291 8596367 := bstep (se 1 (by rfl) ⟨6447275, by rfl⟩ : syracuseStep 8596367 = 12894551) B12894551
theorem B895967 : Blo 595291 895967 := bstep (se 1 (by rfl) ⟨671975, by rfl⟩ : syracuseStep 895967 = 1343951) B1343951
theorem B896411 : Blo 595291 896411 := bstep (se 1 (by rfl) ⟨672308, by rfl⟩ : syracuseStep 896411 = 1344617) B1344617
theorem B11448125 : Blo 595291 11448125 := bstep (se 3 (by rfl) ⟨2146523, by rfl⟩ : syracuseStep 11448125 = 4293047) B4293047
theorem B896831 : Blo 595291 896831 := bstep (se 1 (by rfl) ⟨672623, by rfl⟩ : syracuseStep 896831 = 1345247) B1345247
theorem B4829033 : Blo 595291 4829033 := bstep (se 2 (by rfl) ⟨1810887, by rfl⟩ : syracuseStep 4829033 = 3621775) B3621775
theorem B2273129 : Blo 595291 2273129 := bstep (se 2 (by rfl) ⟨852423, by rfl⟩ : syracuseStep 2273129 = 1704847) B1704847
theorem B897017 : Blo 595291 897017 := bstep (se 2 (by rfl) ⟨336381, by rfl⟩ : syracuseStep 897017 = 672763) B672763
theorem B897257 : Blo 595291 897257 := bstep (se 2 (by rfl) ⟨336471, by rfl⟩ : syracuseStep 897257 = 672943) B672943
theorem B897383 : Blo 595291 897383 := bstep (se 1 (by rfl) ⟨673037, by rfl⟩ : syracuseStep 897383 = 1346075) B1346075
theorem B3027617 : Blo 595291 3027617 := bstep (se 2 (by rfl) ⟨1135356, by rfl⟩ : syracuseStep 3027617 = 2270713) B2270713
theorem B4305793 : Blo 595291 4305793 := bstep (se 2 (by rfl) ⟨1614672, by rfl⟩ : syracuseStep 4305793 = 3229345) B3229345
theorem B897929 : Blo 595291 897929 := bstep (se 2 (by rfl) ⟨336723, by rfl⟩ : syracuseStep 897929 = 673447) B673447
theorem B2012201 : Blo 595291 2012201 := bstep (se 2 (by rfl) ⟨754575, by rfl⟩ : syracuseStep 2012201 = 1509151) B1509151
theorem B5092429 : Blo 595291 5092429 := bstep (se 3 (by rfl) ⟨954830, by rfl⟩ : syracuseStep 5092429 = 1909661) B1909661
theorem B5911667 : Blo 595291 5911667 := bstep (se 1 (by rfl) ⟨4433750, by rfl⟩ : syracuseStep 5911667 = 8867501) B8867501
theorem B1914121 : Blo 595291 1914121 := bstep (se 2 (by rfl) ⟨717795, by rfl⟩ : syracuseStep 1914121 = 1435591) B1435591
theorem B898313 : Blo 595291 898313 := bstep (se 2 (by rfl) ⟨336867, by rfl⟩ : syracuseStep 898313 = 673735) B673735
theorem B6534449 : Blo 595291 6534449 := bstep (se 2 (by rfl) ⟨2450418, by rfl⟩ : syracuseStep 6534449 = 4900837) B4900837
theorem B898367 : Blo 595291 898367 := bstep (se 1 (by rfl) ⟨673775, by rfl⟩ : syracuseStep 898367 = 1347551) B1347551
theorem B898793 : Blo 595291 898793 := bstep (se 2 (by rfl) ⟨337047, by rfl⟩ : syracuseStep 898793 = 674095) B674095
theorem B2864879 : Blo 595291 2864879 := bstep (se 1 (by rfl) ⟨2148659, by rfl⟩ : syracuseStep 2864879 = 4297319) B4297319
theorem B898799 : Blo 595291 898799 := bstep (se 1 (by rfl) ⟨674099, by rfl⟩ : syracuseStep 898799 = 1348199) B1348199
theorem B11646713 : Blo 595291 11646713 := bstep (se 2 (by rfl) ⟨4367517, by rfl⟩ : syracuseStep 11646713 = 8735035) B8735035
theorem B19642175 : Blo 595291 19642175 := bstep (se 1 (by rfl) ⟨14731631, by rfl⟩ : syracuseStep 19642175 = 29463263) B29463263
theorem B2176897 : Blo 595291 2176897 := bstep (se 2 (by rfl) ⟨816336, by rfl⟩ : syracuseStep 2176897 = 1632673) B1632673
theorem B1554727 : Blo 595291 1554727 := bstep (se 1 (by rfl) ⟨1166045, by rfl⟩ : syracuseStep 1554727 = 2332091) B2332091
theorem B2013929 : Blo 595291 2013929 := bstep (se 2 (by rfl) ⟨755223, by rfl⟩ : syracuseStep 2013929 = 1510447) B1510447
theorem B5749865 : Blo 595291 5749865 := bstep (se 2 (by rfl) ⟨2156199, by rfl⟩ : syracuseStep 5749865 = 4312399) B4312399
theorem B670927 : Blo 595291 670927 := bstep (se 1 (by rfl) ⟨503195, by rfl⟩ : syracuseStep 670927 = 1006391) B1006391
theorem B41270627 : Blo 595291 41270627 := bstep (se 1 (by rfl) ⟨30952970, by rfl⟩ : syracuseStep 41270627 = 61905941) B61905941
theorem B1359737 : Blo 595291 1359737 := bstep (se 2 (by rfl) ⟨509901, by rfl⟩ : syracuseStep 1359737 = 1019803) B1019803
theorem B671935 : Blo 595291 671935 := bstep (se 1 (by rfl) ⟨503951, by rfl⟩ : syracuseStep 671935 = 1007903) B1007903
theorem B26165861 : Blo 595291 26165861 := bstep (se 4 (by rfl) ⟨2453049, by rfl⟩ : syracuseStep 26165861 = 4906099) B4906099
theorem B3228263 : Blo 595291 3228263 := bstep (se 1 (by rfl) ⟨2421197, by rfl⟩ : syracuseStep 3228263 = 4842395) B4842395
theorem B672367 : Blo 595291 672367 := bstep (se 1 (by rfl) ⟨504275, by rfl⟩ : syracuseStep 672367 = 1008551) B1008551
theorem B672475 : Blo 595291 672475 := bstep (se 1 (by rfl) ⟨504356, by rfl⟩ : syracuseStep 672475 = 1008713) B1008713
theorem B639775 : Blo 595291 639775 := bstep (se 1 (by rfl) ⟨479831, by rfl⟩ : syracuseStep 639775 = 959663) B959663
theorem B2016251 : Blo 595291 2016251 := bstep (se 1 (by rfl) ⟨1512188, by rfl⟩ : syracuseStep 2016251 = 3024377) B3024377
theorem B1131583 : Blo 595291 1131583 := bstep (se 1 (by rfl) ⟨848687, by rfl⟩ : syracuseStep 1131583 = 1697375) B1697375
theorem B607343 : Blo 595291 607343 := bstep (se 1 (by rfl) ⟨455507, by rfl⟩ : syracuseStep 607343 = 911015) B911015
theorem B2148011 : Blo 595291 2148011 := bstep (se 1 (by rfl) ⟨1611008, by rfl⟩ : syracuseStep 2148011 = 3222017) B3222017
theorem B1132699 : Blo 595291 1132699 := bstep (se 1 (by rfl) ⟨849524, by rfl⟩ : syracuseStep 1132699 = 1699049) B1699049
theorem B1362143 : Blo 595291 1362143 := bstep (se 1 (by rfl) ⟨1021607, by rfl⟩ : syracuseStep 1362143 = 2043215) B2043215
theorem B4540697 : Blo 595291 4540697 := bstep (se 2 (by rfl) ⟨1702761, by rfl⟩ : syracuseStep 4540697 = 3405523) B3405523
theorem B3820121 : Blo 595291 3820121 := bstep (se 2 (by rfl) ⟨1432545, by rfl⟩ : syracuseStep 3820121 = 2865091) B2865091
theorem B3623723 : Blo 595291 3623723 := bstep (se 1 (by rfl) ⟨2717792, by rfl⟩ : syracuseStep 3623723 = 5435585) B5435585
theorem B3820553 : Blo 595291 3820553 := bstep (se 2 (by rfl) ⟨1432707, by rfl⟩ : syracuseStep 3820553 = 2865415) B2865415
theorem B4541669 : Blo 595291 4541669 := bstep (se 4 (by rfl) ⟨425781, by rfl⟩ : syracuseStep 4541669 = 851563) B851563
theorem B5328293 : Blo 595291 5328293 := bstep (se 4 (by rfl) ⟨499527, by rfl⟩ : syracuseStep 5328293 = 999055) B999055
theorem B2019383 : Blo 595291 2019383 := bstep (se 1 (by rfl) ⟨1514537, by rfl⟩ : syracuseStep 2019383 = 3029075) B3029075
theorem B3231899 : Blo 595291 3231899 := bstep (se 1 (by rfl) ⟨2423924, by rfl⟩ : syracuseStep 3231899 = 4847849) B4847849
theorem B2183411 : Blo 595291 2183411 := bstep (se 1 (by rfl) ⟨1637558, by rfl⟩ : syracuseStep 2183411 = 3275117) B3275117
theorem B2019707 : Blo 595291 2019707 := bstep (se 1 (by rfl) ⟨1514780, by rfl⟩ : syracuseStep 2019707 = 3029561) B3029561
theorem B2019977 : Blo 595291 2019977 := bstep (se 2 (by rfl) ⟨757491, by rfl⟩ : syracuseStep 2019977 = 1514983) B1514983
theorem B1135471 : Blo 595291 1135471 := bstep (se 1 (by rfl) ⟨851603, by rfl⟩ : syracuseStep 1135471 = 1703207) B1703207
theorem B906223 : Blo 595291 906223 := bstep (se 1 (by rfl) ⟨679667, by rfl⟩ : syracuseStep 906223 = 1359335) B1359335
theorem B1430959 : Blo 595291 1430959 := bstep (se 1 (by rfl) ⟨1073219, by rfl⟩ : syracuseStep 1430959 = 2146439) B2146439
theorem B5101177 : Blo 595291 5101177 := bstep (se 2 (by rfl) ⟨1912941, by rfl⟩ : syracuseStep 5101177 = 3825883) B3825883
theorem B3823271 : Blo 595291 3823271 := bstep (se 1 (by rfl) ⟨2867453, by rfl⟩ : syracuseStep 3823271 = 5734907) B5734907
theorem B3233627 : Blo 595291 3233627 := bstep (se 1 (by rfl) ⟨2425220, by rfl⟩ : syracuseStep 3233627 = 4850441) B4850441
theorem B1366303 : Blo 595291 1366303 := bstep (se 1 (by rfl) ⟨1024727, by rfl⟩ : syracuseStep 1366303 = 2049455) B2049455
theorem B4610533 : Blo 595291 4610533 := bstep (se 4 (by rfl) ⟨432237, by rfl⟩ : syracuseStep 4610533 = 864475) B864475
theorem B1137179 : Blo 595291 1137179 := bstep (se 1 (by rfl) ⟨852884, by rfl⟩ : syracuseStep 1137179 = 1705769) B1705769
theorem B5463533 : Blo 595291 5463533 := bstep (se 3 (by rfl) ⟨1024412, by rfl⟩ : syracuseStep 5463533 = 2048825) B2048825
theorem B1007471 : Blo 595291 1007471 := bstep (se 1 (by rfl) ⟨755603, by rfl⟩ : syracuseStep 1007471 = 1511207) B1511207
theorem B3825731 : Blo 595291 3825731 := bstep (se 1 (by rfl) ⟨2869298, by rfl⟩ : syracuseStep 3825731 = 5738597) B5738597
theorem B3235963 : Blo 595291 3235963 := bstep (se 1 (by rfl) ⟨2426972, by rfl⟩ : syracuseStep 3235963 = 4853945) B4853945
theorem B1073407 : Blo 595291 1073407 := bstep (se 1 (by rfl) ⟨805055, by rfl⟩ : syracuseStep 1073407 = 1610111) B1610111
theorem B3399965 : Blo 595291 3399965 := bstep (se 3 (by rfl) ⟨637493, by rfl⟩ : syracuseStep 3399965 = 1274987) B1274987
theorem B1008335 : Blo 595291 1008335 := bstep (se 1 (by rfl) ⟨756251, by rfl⟩ : syracuseStep 1008335 = 1512503) B1512503
theorem B1009631 : Blo 595291 1009631 := bstep (se 1 (by rfl) ⟨757223, by rfl⟩ : syracuseStep 1009631 = 1514447) B1514447
theorem B1271801 : Blo 595291 1271801 := bstep (se 2 (by rfl) ⟨476925, by rfl⟩ : syracuseStep 1271801 = 953851) B953851
theorem B1435745 : Blo 595291 1435745 := bstep (se 2 (by rfl) ⟨538404, by rfl⟩ : syracuseStep 1435745 = 1076809) B1076809
theorem B2156777 : Blo 595291 2156777 := bstep (se 2 (by rfl) ⟨808791, by rfl⟩ : syracuseStep 2156777 = 1617583) B1617583
theorem B1009975 : Blo 595291 1009975 := bstep (se 1 (by rfl) ⟨757481, by rfl⟩ : syracuseStep 1009975 = 1514963) B1514963
theorem B4548959 : Blo 595291 4548959 := bstep (se 1 (by rfl) ⟨3411719, by rfl⟩ : syracuseStep 4548959 = 6823439) B6823439
theorem B5827493 : Blo 595291 5827493 := bstep (se 4 (by rfl) ⟨546327, by rfl⟩ : syracuseStep 5827493 = 1092655) B1092655
theorem B1698889 : Blo 595291 1698889 := bstep (se 2 (by rfl) ⟨637083, by rfl⟩ : syracuseStep 1698889 = 1274167) B1274167
theorem B32664941 : Blo 595291 32664941 := bstep (se 3 (by rfl) ⟨6124676, by rfl⟩ : syracuseStep 32664941 = 12249353) B12249353
theorem B1011271 : Blo 595291 1011271 := bstep (se 1 (by rfl) ⟨758453, by rfl⟩ : syracuseStep 1011271 = 1516907) B1516907
theorem B17034877 : Blo 595291 17034877 := bstep (se 3 (by rfl) ⟨3194039, by rfl⟩ : syracuseStep 17034877 = 6388079) B6388079
theorem B3239767 : Blo 595291 3239767 := bstep (se 1 (by rfl) ⟨2429825, by rfl⟩ : syracuseStep 3239767 = 4859651) B4859651
theorem B77590385 : Blo 595291 77590385 := bstep (se 2 (by rfl) ⟨29096394, by rfl⟩ : syracuseStep 77590385 = 58192789) B58192789
theorem B1699937 : Blo 595291 1699937 := bstep (se 2 (by rfl) ⟨637476, by rfl⟩ : syracuseStep 1699937 = 1274953) B1274953
theorem B1339667 : Blo 595291 1339667 := bstep (se 1 (by rfl) ⟨1004750, by rfl⟩ : syracuseStep 1339667 = 2009501) B2009501
theorem B1339847 : Blo 595291 1339847 := bstep (se 1 (by rfl) ⟨1004885, by rfl⟩ : syracuseStep 1339847 = 2009771) B2009771
theorem B1700347 : Blo 595291 1700347 := bstep (se 1 (by rfl) ⟨1275260, by rfl⟩ : syracuseStep 1700347 = 2550521) B2550521
theorem B1340207 : Blo 595291 1340207 := bstep (se 1 (by rfl) ⟨1005155, by rfl⟩ : syracuseStep 1340207 = 2010311) B2010311
theorem B6452027 : Blo 595291 6452027 := bstep (se 1 (by rfl) ⟨4839020, by rfl⟩ : syracuseStep 6452027 = 9678041) B9678041
theorem B1340297 : Blo 595291 1340297 := bstep (se 2 (by rfl) ⟨502611, by rfl⟩ : syracuseStep 1340297 = 1005223) B1005223
theorem B34796627 : Blo 595291 34796627 := bstep (se 1 (by rfl) ⟨26097470, by rfl⟩ : syracuseStep 34796627 = 52194941) B52194941
theorem B26178835 : Blo 595291 26178835 := bstep (se 1 (by rfl) ⟨19634126, by rfl⟩ : syracuseStep 26178835 = 39268253) B39268253
theorem B2553119 : Blo 595291 2553119 := bstep (se 1 (by rfl) ⟨1914839, by rfl⟩ : syracuseStep 2553119 = 3829679) B3829679
theorem B1701395 : Blo 595291 1701395 := bstep (se 1 (by rfl) ⟨1276046, by rfl⟩ : syracuseStep 1701395 = 2552093) B2552093
theorem B2717279 : Blo 595291 2717279 := bstep (se 1 (by rfl) ⟨2037959, by rfl⟩ : syracuseStep 2717279 = 4075919) B4075919
theorem B1341071 : Blo 595291 1341071 := bstep (se 1 (by rfl) ⟨1005803, by rfl⟩ : syracuseStep 1341071 = 2011607) B2011607
theorem B1341161 : Blo 595291 1341161 := bstep (se 2 (by rfl) ⟨502935, by rfl⟩ : syracuseStep 1341161 = 1005871) B1005871
theorem B1079023 : Blo 595291 1079023 := bstep (se 1 (by rfl) ⟨809267, by rfl⟩ : syracuseStep 1079023 = 1618535) B1618535
theorem B1439927 : Blo 595291 1439927 := bstep (se 1 (by rfl) ⟨1079945, by rfl⟩ : syracuseStep 1439927 = 2159891) B2159891
theorem B1342043 : Blo 595291 1342043 := bstep (se 1 (by rfl) ⟨1006532, by rfl⟩ : syracuseStep 1342043 = 2013065) B2013065
theorem B2718305 : Blo 595291 2718305 := bstep (se 2 (by rfl) ⟨1019364, by rfl⟩ : syracuseStep 2718305 = 2038729) B2038729
theorem B1342187 : Blo 595291 1342187 := bstep (se 1 (by rfl) ⟨1006640, by rfl⟩ : syracuseStep 1342187 = 2013281) B2013281
theorem B1342799 : Blo 595291 1342799 := bstep (se 1 (by rfl) ⟨1007099, by rfl⟩ : syracuseStep 1342799 = 2014199) B2014199
theorem B1342889 : Blo 595291 1342889 := bstep (se 2 (by rfl) ⟨503583, by rfl⟩ : syracuseStep 1342889 = 1007167) B1007167
theorem B1343087 : Blo 595291 1343087 := bstep (se 1 (by rfl) ⟨1007315, by rfl⟩ : syracuseStep 1343087 = 2014631) B2014631
theorem B851791 : Blo 595291 851791 := bstep (se 1 (by rfl) ⟨638843, by rfl⟩ : syracuseStep 851791 = 1277687) B1277687
theorem B1343375 : Blo 595291 1343375 := bstep (se 1 (by rfl) ⟨1007531, by rfl⟩ : syracuseStep 1343375 = 2015063) B2015063
theorem B1703879 : Blo 595291 1703879 := bstep (se 1 (by rfl) ⟨1277909, by rfl⟩ : syracuseStep 1703879 = 2555819) B2555819
theorem B1344167 : Blo 595291 1344167 := bstep (se 1 (by rfl) ⟨1008125, by rfl⟩ : syracuseStep 1344167 = 2016251) B2016251
theorem B1508159 : Blo 595291 1508159 := bstep (se 1 (by rfl) ⟨1131119, by rfl⟩ : syracuseStep 1508159 = 2262239) B2262239
theorem B6554621 : Blo 595291 6554621 := bstep (se 3 (by rfl) ⟨1228991, by rfl⟩ : syracuseStep 6554621 = 2457983) B2457983
theorem B853033 : Blo 595291 853033 := bstep (se 2 (by rfl) ⟨319887, by rfl⟩ : syracuseStep 853033 = 639775) B639775
theorem B1705313 : Blo 595291 1705313 := bstep (se 2 (by rfl) ⟨639492, by rfl⟩ : syracuseStep 1705313 = 1278985) B1278985
theorem B1508777 : Blo 595291 1508777 := bstep (se 2 (by rfl) ⟨565791, by rfl⟩ : syracuseStep 1508777 = 1131583) B1131583
theorem B20678665 : Blo 595291 20678665 := bstep (se 2 (by rfl) ⟨7754499, by rfl⟩ : syracuseStep 20678665 = 15508999) B15508999
theorem B1706123 : Blo 595291 1706123 := bstep (se 1 (by rfl) ⟨1279592, by rfl⟩ : syracuseStep 1706123 = 2559185) B2559185
theorem B4524659 : Blo 595291 4524659 := bstep (se 1 (by rfl) ⟨3393494, by rfl⟩ : syracuseStep 4524659 = 6786989) B6786989
theorem B1346255 : Blo 595291 1346255 := bstep (se 1 (by rfl) ⟨1009691, by rfl⟩ : syracuseStep 1346255 = 2019383) B2019383
theorem B1510235 : Blo 595291 1510235 := bstep (se 1 (by rfl) ⟨1132676, by rfl⟩ : syracuseStep 1510235 = 2265353) B2265353
theorem B1510265 : Blo 595291 1510265 := bstep (se 2 (by rfl) ⟨566349, by rfl⟩ : syracuseStep 1510265 = 1132699) B1132699
theorem B1346471 : Blo 595291 1346471 := bstep (se 1 (by rfl) ⟨1009853, by rfl⟩ : syracuseStep 1346471 = 2019707) B2019707
theorem B1346633 : Blo 595291 1346633 := bstep (se 2 (by rfl) ⟨504987, by rfl⟩ : syracuseStep 1346633 = 1009975) B1009975
theorem B11504713 : Blo 595291 11504713 := bstep (se 2 (by rfl) ⟨4314267, by rfl⟩ : syracuseStep 11504713 = 8628535) B8628535
theorem B1346651 : Blo 595291 1346651 := bstep (se 1 (by rfl) ⟨1009988, by rfl⟩ : syracuseStep 1346651 = 2019977) B2019977
theorem B3017897 : Blo 595291 3017897 := bstep (se 2 (by rfl) ⟨1131711, by rfl⟩ : syracuseStep 3017897 = 2263423) B2263423
theorem B4525631 : Blo 595291 4525631 := bstep (se 1 (by rfl) ⟨3394223, by rfl⟩ : syracuseStep 4525631 = 6788447) B6788447
theorem B2265185 : Blo 595291 2265185 := bstep (se 2 (by rfl) ⟨849444, by rfl⟩ : syracuseStep 2265185 = 1698889) B1698889
theorem B3019031 : Blo 595291 3019031 := bstep (se 1 (by rfl) ⟨2264273, by rfl⟩ : syracuseStep 3019031 = 4528547) B4528547
theorem B1348361 : Blo 595291 1348361 := bstep (se 2 (by rfl) ⟨505635, by rfl⟩ : syracuseStep 1348361 = 1011271) B1011271
theorem B22713169 : Blo 595291 22713169 := bstep (se 2 (by rfl) ⟨8517438, by rfl⟩ : syracuseStep 22713169 = 17034877) B17034877
theorem B3642355 : Blo 595291 3642355 := bstep (se 1 (by rfl) ⟨2731766, by rfl⟩ : syracuseStep 3642355 = 5463533) B5463533
theorem B595423 : Blo 595291 595423 := bstep (se 1 (by rfl) ⟨446567, by rfl⟩ : syracuseStep 595423 = 893135) B893135
theorem B595455 : Blo 595291 595455 := bstep (se 1 (by rfl) ⟨446591, by rfl⟩ : syracuseStep 595455 = 893183) B893183
theorem B2266643 : Blo 595291 2266643 := bstep (se 1 (by rfl) ⟨1699982, by rfl⟩ : syracuseStep 2266643 = 3399965) B3399965
theorem B3020651 : Blo 595291 3020651 := bstep (se 1 (by rfl) ⟨2265488, by rfl⟩ : syracuseStep 3020651 = 4530977) B4530977
theorem B2267129 : Blo 595291 2267129 := bstep (se 2 (by rfl) ⟨850173, by rfl⟩ : syracuseStep 2267129 = 1700347) B1700347
theorem B595999 : Blo 595291 595999 := bstep (se 1 (by rfl) ⟨446999, by rfl⟩ : syracuseStep 595999 = 893999) B893999
theorem B596079 : Blo 595291 596079 := bstep (se 1 (by rfl) ⟨447059, by rfl⟩ : syracuseStep 596079 = 894119) B894119
theorem B6232211 : Blo 595291 6232211 := bstep (se 1 (by rfl) ⟨4674158, by rfl⟩ : syracuseStep 6232211 = 9348317) B9348317
theorem B3021137 : Blo 595291 3021137 := bstep (se 2 (by rfl) ⟨1132926, by rfl⟩ : syracuseStep 3021137 = 2265853) B2265853
theorem B596327 : Blo 595291 596327 := bstep (se 1 (by rfl) ⟨447245, by rfl⟩ : syracuseStep 596327 = 894491) B894491
theorem B1513961 : Blo 595291 1513961 := bstep (se 2 (by rfl) ⟨567735, by rfl⟩ : syracuseStep 1513961 = 1135471) B1135471
theorem B5741057 : Blo 595291 5741057 := bstep (se 2 (by rfl) ⟨2152896, by rfl⟩ : syracuseStep 5741057 = 4305793) B4305793
theorem B1514011 : Blo 595291 1514011 := bstep (se 1 (by rfl) ⟨1135508, by rfl⟩ : syracuseStep 1514011 = 2271017) B2271017
theorem B596583 : Blo 595291 596583 := bstep (se 1 (by rfl) ⟨447437, by rfl⟩ : syracuseStep 596583 = 894875) B894875
theorem B596607 : Blo 595291 596607 := bstep (se 1 (by rfl) ⟨447455, by rfl⟩ : syracuseStep 596607 = 894911) B894911
theorem B596731 : Blo 595291 596731 := bstep (se 1 (by rfl) ⟨447548, by rfl⟩ : syracuseStep 596731 = 895097) B895097
theorem B6789905 : Blo 595291 6789905 := bstep (se 2 (by rfl) ⟨2546214, by rfl⟩ : syracuseStep 6789905 = 5092429) B5092429
theorem B596987 : Blo 595291 596987 := bstep (se 1 (by rfl) ⟨447740, by rfl⟩ : syracuseStep 596987 = 895481) B895481
theorem B34905113 : Blo 595291 34905113 := bstep (se 2 (by rfl) ⟨13089417, by rfl⟩ : syracuseStep 34905113 = 26178835) B26178835
theorem B597023 : Blo 595291 597023 := bstep (se 1 (by rfl) ⟨447767, by rfl⟩ : syracuseStep 597023 = 895535) B895535
theorem B1907945 : Blo 595291 1907945 := bstep (se 2 (by rfl) ⟨715479, by rfl⟩ : syracuseStep 1907945 = 1430959) B1430959
theorem B597311 : Blo 595291 597311 := bstep (se 1 (by rfl) ⟨447983, by rfl⟩ : syracuseStep 597311 = 895967) B895967
theorem B597607 : Blo 595291 597607 := bstep (se 1 (by rfl) ⟨448205, by rfl⟩ : syracuseStep 597607 = 896411) B896411
theorem B597887 : Blo 595291 597887 := bstep (se 1 (by rfl) ⟨448415, by rfl⟩ : syracuseStep 597887 = 896831) B896831
theorem B3219355 : Blo 595291 3219355 := bstep (se 1 (by rfl) ⟨2414516, by rfl⟩ : syracuseStep 3219355 = 4829033) B4829033
theorem B1515419 : Blo 595291 1515419 := bstep (se 1 (by rfl) ⟨1136564, by rfl⟩ : syracuseStep 1515419 = 2273129) B2273129
theorem B598011 : Blo 595291 598011 := bstep (se 1 (by rfl) ⟨448508, by rfl⟩ : syracuseStep 598011 = 897017) B897017
theorem B598171 : Blo 595291 598171 := bstep (se 1 (by rfl) ⟨448628, by rfl⟩ : syracuseStep 598171 = 897257) B897257
theorem B893111 : Blo 595291 893111 := bstep (se 1 (by rfl) ⟨669833, by rfl⟩ : syracuseStep 893111 = 1339667) B1339667
theorem B598255 : Blo 595291 598255 := bstep (se 1 (by rfl) ⟨448691, by rfl⟩ : syracuseStep 598255 = 897383) B897383
theorem B893231 : Blo 595291 893231 := bstep (se 1 (by rfl) ⟨669923, by rfl⟩ : syracuseStep 893231 = 1339847) B1339847
theorem B2072969 : Blo 595291 2072969 := bstep (se 2 (by rfl) ⟨777363, by rfl⟩ : syracuseStep 2072969 = 1554727) B1554727
theorem B893471 : Blo 595291 893471 := bstep (se 1 (by rfl) ⟨670103, by rfl⟩ : syracuseStep 893471 = 1340207) B1340207
theorem B4301351 : Blo 595291 4301351 := bstep (se 1 (by rfl) ⟨3226013, by rfl⟩ : syracuseStep 4301351 = 6452027) B6452027
theorem B893531 : Blo 595291 893531 := bstep (se 1 (by rfl) ⟨670148, by rfl⟩ : syracuseStep 893531 = 1340297) B1340297
theorem B598619 : Blo 595291 598619 := bstep (se 1 (by rfl) ⟨448964, by rfl⟩ : syracuseStep 598619 = 897929) B897929
theorem B3941111 : Blo 595291 3941111 := bstep (se 1 (by rfl) ⟨2955833, by rfl⟩ : syracuseStep 3941111 = 5911667) B5911667
theorem B598875 : Blo 595291 598875 := bstep (se 1 (by rfl) ⟨449156, by rfl⟩ : syracuseStep 598875 = 898313) B898313
theorem B598911 : Blo 595291 598911 := bstep (se 1 (by rfl) ⟨449183, by rfl⟩ : syracuseStep 598911 = 898367) B898367
theorem B1811519 : Blo 595291 1811519 := bstep (se 1 (by rfl) ⟨1358639, by rfl⟩ : syracuseStep 1811519 = 2717279) B2717279
theorem B894047 : Blo 595291 894047 := bstep (se 1 (by rfl) ⟨670535, by rfl⟩ : syracuseStep 894047 = 1341071) B1341071
theorem B894107 : Blo 595291 894107 := bstep (se 1 (by rfl) ⟨670580, by rfl⟩ : syracuseStep 894107 = 1341161) B1341161
theorem B599195 : Blo 595291 599195 := bstep (se 1 (by rfl) ⟨449396, by rfl⟩ : syracuseStep 599195 = 898793) B898793
theorem B1909919 : Blo 595291 1909919 := bstep (se 1 (by rfl) ⟨1432439, by rfl⟩ : syracuseStep 1909919 = 2864879) B2864879
theorem B599199 : Blo 595291 599199 := bstep (se 1 (by rfl) ⟨449399, by rfl⟩ : syracuseStep 599199 = 898799) B898799
theorem B959951 : Blo 595291 959951 := bstep (se 1 (by rfl) ⟨719963, by rfl⟩ : syracuseStep 959951 = 1439927) B1439927
theorem B894569 : Blo 595291 894569 := bstep (se 2 (by rfl) ⟨335463, by rfl⟩ : syracuseStep 894569 = 670927) B670927
theorem B894695 : Blo 595291 894695 := bstep (se 1 (by rfl) ⟨671021, by rfl⟩ : syracuseStep 894695 = 1342043) B1342043
theorem B1812203 : Blo 595291 1812203 := bstep (se 1 (by rfl) ⟨1359152, by rfl⟩ : syracuseStep 1812203 = 2718305) B2718305
theorem B17278757 : Blo 595291 17278757 := bstep (se 4 (by rfl) ⟨1619883, by rfl⟩ : syracuseStep 17278757 = 3239767) B3239767
theorem B894791 : Blo 595291 894791 := bstep (se 1 (by rfl) ⟨671093, by rfl⟩ : syracuseStep 894791 = 1342187) B1342187
theorem B895199 : Blo 595291 895199 := bstep (se 1 (by rfl) ⟨671399, by rfl⟩ : syracuseStep 895199 = 1342799) B1342799
theorem B895259 : Blo 595291 895259 := bstep (se 1 (by rfl) ⟨671444, by rfl⟩ : syracuseStep 895259 = 1342889) B1342889
theorem B895391 : Blo 595291 895391 := bstep (se 1 (by rfl) ⟨671543, by rfl⟩ : syracuseStep 895391 = 1343087) B1343087
theorem B895583 : Blo 595291 895583 := bstep (se 1 (by rfl) ⟨671687, by rfl⟩ : syracuseStep 895583 = 1343375) B1343375
theorem B895913 : Blo 595291 895913 := bstep (se 2 (by rfl) ⟨335967, by rfl⟩ : syracuseStep 895913 = 671935) B671935
theorem B895943 : Blo 595291 895943 := bstep (se 1 (by rfl) ⟨671957, by rfl⟩ : syracuseStep 895943 = 1343915) B1343915
theorem B896063 : Blo 595291 896063 := bstep (se 1 (by rfl) ⟨672047, by rfl⟩ : syracuseStep 896063 = 1344095) B1344095
theorem B17443907 : Blo 595291 17443907 := bstep (se 1 (by rfl) ⟨13082930, by rfl⟩ : syracuseStep 17443907 = 26165861) B26165861
theorem B896303 : Blo 595291 896303 := bstep (se 1 (by rfl) ⟨672227, by rfl⟩ : syracuseStep 896303 = 1344455) B1344455
theorem B5090789 : Blo 595291 5090789 := bstep (se 4 (by rfl) ⟨477261, by rfl⟩ : syracuseStep 5090789 = 954523) B954523
theorem B896489 : Blo 595291 896489 := bstep (se 2 (by rfl) ⟨336183, by rfl⟩ : syracuseStep 896489 = 672367) B672367
theorem B896543 : Blo 595291 896543 := bstep (se 1 (by rfl) ⟨672407, by rfl⟩ : syracuseStep 896543 = 1344815) B1344815
theorem B896633 : Blo 595291 896633 := bstep (se 2 (by rfl) ⟨336237, by rfl⟩ : syracuseStep 896633 = 672475) B672475
theorem B896879 : Blo 595291 896879 := bstep (se 1 (by rfl) ⟨672659, by rfl⟩ : syracuseStep 896879 = 1345319) B1345319
theorem B10923997 : Blo 595291 10923997 := bstep (se 3 (by rfl) ⟨2048249, by rfl⟩ : syracuseStep 10923997 = 4096499) B4096499
theorem B897131 : Blo 595291 897131 := bstep (se 1 (by rfl) ⟨672848, by rfl⟩ : syracuseStep 897131 = 1345697) B1345697
theorem B3027131 : Blo 595291 3027131 := bstep (se 1 (by rfl) ⟨2270348, by rfl⟩ : syracuseStep 3027131 = 4540697) B4540697
theorem B1749289 : Blo 595291 1749289 := bstep (se 2 (by rfl) ⟨655983, by rfl⟩ : syracuseStep 1749289 = 1311967) B1311967
theorem B897563 : Blo 595291 897563 := bstep (se 1 (by rfl) ⟨673172, by rfl⟩ : syracuseStep 897563 = 1346345) B1346345
theorem B14529131 : Blo 595291 14529131 := bstep (se 1 (by rfl) ⟨10896848, by rfl⟩ : syracuseStep 14529131 = 21793697) B21793697
theorem B897743 : Blo 595291 897743 := bstep (se 1 (by rfl) ⟨673307, by rfl⟩ : syracuseStep 897743 = 1346615) B1346615
theorem B1749815 : Blo 595291 1749815 := bstep (se 1 (by rfl) ⟨1312361, by rfl⟩ : syracuseStep 1749815 = 2624723) B2624723
theorem B3027779 : Blo 595291 3027779 := bstep (se 1 (by rfl) ⟨2270834, by rfl⟩ : syracuseStep 3027779 = 4541669) B4541669
theorem B898031 : Blo 595291 898031 := bstep (se 1 (by rfl) ⟨673523, by rfl⟩ : syracuseStep 898031 = 1347047) B1347047
theorem B3028265 : Blo 595291 3028265 := bstep (se 2 (by rfl) ⟨1135599, by rfl⟩ : syracuseStep 3028265 = 2271199) B2271199
theorem B898415 : Blo 595291 898415 := bstep (se 1 (by rfl) ⟨673811, by rfl⟩ : syracuseStep 898415 = 1347623) B1347623
theorem B898535 : Blo 595291 898535 := bstep (se 1 (by rfl) ⟨673901, by rfl⟩ : syracuseStep 898535 = 1347803) B1347803
theorem B1455607 : Blo 595291 1455607 := bstep (se 1 (by rfl) ⟨1091705, by rfl⟩ : syracuseStep 1455607 = 2183411) B2183411
theorem B1619581 : Blo 595291 1619581 := bstep (se 3 (by rfl) ⟨303671, by rfl⟩ : syracuseStep 1619581 = 607343) B607343
theorem B898715 : Blo 595291 898715 := bstep (se 1 (by rfl) ⟨674036, by rfl⟩ : syracuseStep 898715 = 1348073) B1348073
theorem B2013011 : Blo 595291 2013011 := bstep (se 1 (by rfl) ⟨1509758, by rfl⟩ : syracuseStep 2013011 = 3019517) B3019517
theorem B2013119 : Blo 595291 2013119 := bstep (se 1 (by rfl) ⟨1509839, by rfl⟩ : syracuseStep 2013119 = 3019679) B3019679
theorem B56835125 : Blo 595291 56835125 := bstep (se 5 (by rfl) ⟨2664146, by rfl⟩ : syracuseStep 56835125 = 5328293) B5328293
theorem B7453949 : Blo 595291 7453949 := bstep (se 3 (by rfl) ⟨1397615, by rfl⟩ : syracuseStep 7453949 = 2795231) B2795231
theorem B3390943 : Blo 595291 3390943 := bstep (se 1 (by rfl) ⟨2543207, by rfl⟩ : syracuseStep 3390943 = 5086415) B5086415
theorem B5881643 : Blo 595291 5881643 := bstep (se 1 (by rfl) ⟨4411232, by rfl⟩ : syracuseStep 5881643 = 8822465) B8822465
theorem B671647 : Blo 595291 671647 := bstep (se 1 (by rfl) ⟨503735, by rfl⟩ : syracuseStep 671647 = 1007471) B1007471
theorem B3391469 : Blo 595291 3391469 := bstep (se 3 (by rfl) ⟨635900, by rfl⟩ : syracuseStep 3391469 = 1271801) B1271801
theorem B3326035 : Blo 595291 3326035 := bstep (se 1 (by rfl) ⟨2494526, by rfl⟩ : syracuseStep 3326035 = 4989053) B4989053
theorem B2015495 : Blo 595291 2015495 := bstep (se 1 (by rfl) ⟨1511621, by rfl⟩ : syracuseStep 2015495 = 3023243) B3023243
theorem B672223 : Blo 595291 672223 := bstep (se 1 (by rfl) ⟨504167, by rfl⟩ : syracuseStep 672223 = 1008335) B1008335
theorem B6145163 : Blo 595291 6145163 := bstep (se 1 (by rfl) ⟨4608872, by rfl⟩ : syracuseStep 6145163 = 9217745) B9217745
theorem B2016575 : Blo 595291 2016575 := bstep (se 1 (by rfl) ⟨1512431, by rfl⟩ : syracuseStep 2016575 = 3024863) B3024863
theorem B673087 : Blo 595291 673087 := bstep (se 1 (by rfl) ⟨504815, by rfl⟩ : syracuseStep 673087 = 1009631) B1009631
theorem B3032477 : Blo 595291 3032477 := bstep (se 3 (by rfl) ⟨568589, by rfl⟩ : syracuseStep 3032477 = 1137179) B1137179
theorem B3032639 : Blo 595291 3032639 := bstep (se 1 (by rfl) ⟨2274479, by rfl⟩ : syracuseStep 3032639 = 4548959) B4548959
theorem B3884995 : Blo 595291 3884995 := bstep (se 1 (by rfl) ⟨2913746, by rfl⟩ : syracuseStep 3884995 = 5827493) B5827493
theorem B2017385 : Blo 595291 2017385 := bstep (se 2 (by rfl) ⟨756519, by rfl⟩ : syracuseStep 2017385 = 1513039) B1513039
theorem B6801569 : Blo 595291 6801569 := bstep (se 2 (by rfl) ⟨2550588, by rfl⟩ : syracuseStep 6801569 = 5101177) B5101177
theorem B21776627 : Blo 595291 21776627 := bstep (se 1 (by rfl) ⟨16332470, by rfl⟩ : syracuseStep 21776627 = 32664941) B32664941
theorem B2902529 : Blo 595291 2902529 := bstep (se 2 (by rfl) ⟨1088448, by rfl⟩ : syracuseStep 2902529 = 2176897) B2176897
theorem B51726923 : Blo 595291 51726923 := bstep (se 1 (by rfl) ⟨38795192, by rfl⟩ : syracuseStep 51726923 = 77590385) B77590385
theorem B1133291 : Blo 595291 1133291 := bstep (se 1 (by rfl) ⟨849968, by rfl⟩ : syracuseStep 1133291 = 1699937) B1699937
theorem B2018249 : Blo 595291 2018249 := bstep (se 2 (by rfl) ⟨756843, by rfl⟩ : syracuseStep 2018249 = 1513687) B1513687
theorem B1821737 : Blo 595291 1821737 := bstep (se 2 (by rfl) ⟨683151, by rfl⟩ : syracuseStep 1821737 = 1366303) B1366303
theorem B2018411 : Blo 595291 2018411 := bstep (se 1 (by rfl) ⟨1513808, by rfl⟩ : syracuseStep 2018411 = 3027617) B3027617
theorem B6147377 : Blo 595291 6147377 := bstep (se 2 (by rfl) ⟨2305266, by rfl⟩ : syracuseStep 6147377 = 4610533) B4610533
theorem B1134263 : Blo 595291 1134263 := bstep (se 1 (by rfl) ⟨850697, by rfl⟩ : syracuseStep 1134263 = 1701395) B1701395
theorem B13094783 : Blo 595291 13094783 := bstep (se 1 (by rfl) ⟨9821087, by rfl⟩ : syracuseStep 13094783 = 19642175) B19642175
theorem B27513751 : Blo 595291 27513751 := bstep (se 1 (by rfl) ⟨20635313, by rfl⟩ : syracuseStep 27513751 = 41270627) B41270627
theorem B1135721 : Blo 595291 1135721 := bstep (se 2 (by rfl) ⟨425895, by rfl⟩ : syracuseStep 1135721 = 851791) B851791
theorem B906491 : Blo 595291 906491 := bstep (se 1 (by rfl) ⟨679868, by rfl⟩ : syracuseStep 906491 = 1359737) B1359737
theorem B1135919 : Blo 595291 1135919 := bstep (se 1 (by rfl) ⟨851939, by rfl⟩ : syracuseStep 1135919 = 1703879) B1703879
theorem B16602457 : Blo 595291 16602457 := bstep (se 2 (by rfl) ⟨6225921, by rfl⟩ : syracuseStep 16602457 = 12451843) B12451843
theorem B4314617 : Blo 595291 4314617 := bstep (se 2 (by rfl) ⟨1617981, by rfl⟩ : syracuseStep 4314617 = 3235963) B3235963
theorem B1431209 : Blo 595291 1431209 := bstep (se 2 (by rfl) ⟨536703, by rfl⟩ : syracuseStep 1431209 = 1073407) B1073407
theorem B2152175 : Blo 595291 2152175 := bstep (se 1 (by rfl) ⟨1614131, by rfl⟩ : syracuseStep 2152175 = 3228263) B3228263
theorem B1005979 : Blo 595291 1005979 := bstep (se 1 (by rfl) ⟨754484, by rfl⟩ : syracuseStep 1005979 = 1508969) B1508969
theorem B1432007 : Blo 595291 1432007 := bstep (se 1 (by rfl) ⟨1074005, by rfl⟩ : syracuseStep 1432007 = 2148011) B2148011
theorem B1006175 : Blo 595291 1006175 := bstep (se 1 (by rfl) ⟨754631, by rfl⟩ : syracuseStep 1006175 = 1509263) B1509263
theorem B908095 : Blo 595291 908095 := bstep (se 1 (by rfl) ⟨681071, by rfl⟩ : syracuseStep 908095 = 1362143) B1362143
theorem B2546747 : Blo 595291 2546747 := bstep (se 1 (by rfl) ⟨1910060, by rfl⟩ : syracuseStep 2546747 = 3820121) B3820121
theorem B2415815 : Blo 595291 2415815 := bstep (se 1 (by rfl) ⟨1811861, by rfl⟩ : syracuseStep 2415815 = 3623723) B3623723
theorem B2547035 : Blo 595291 2547035 := bstep (se 1 (by rfl) ⟨1910276, by rfl⟩ : syracuseStep 2547035 = 3820553) B3820553
theorem B1728479 : Blo 595291 1728479 := bstep (se 1 (by rfl) ⟨1296359, by rfl⟩ : syracuseStep 1728479 = 2592719) B2592719
theorem B1007687 : Blo 595291 1007687 := bstep (se 1 (by rfl) ⟨755765, by rfl⟩ : syracuseStep 1007687 = 1511531) B1511531
theorem B2154599 : Blo 595291 2154599 := bstep (se 1 (by rfl) ⟨1615949, by rfl⟩ : syracuseStep 2154599 = 3231899) B3231899
theorem B2548745 : Blo 595291 2548745 := bstep (se 2 (by rfl) ⟨955779, by rfl⟩ : syracuseStep 2548745 = 1911559) B1911559
theorem B2548847 : Blo 595291 2548847 := bstep (se 1 (by rfl) ⟨1911635, by rfl⟩ : syracuseStep 2548847 = 3823271) B3823271
theorem B2155751 : Blo 595291 2155751 := bstep (se 1 (by rfl) ⟨1616813, by rfl⟩ : syracuseStep 2155751 = 3233627) B3233627
theorem B1008875 : Blo 595291 1008875 := bstep (se 1 (by rfl) ⟨756656, by rfl⟩ : syracuseStep 1008875 = 1513313) B1513313
theorem B21849749 : Blo 595291 21849749 := bstep (se 6 (by rfl) ⟨512103, by rfl⟩ : syracuseStep 21849749 = 1024207) B1024207
theorem B1271467 : Blo 595291 1271467 := bstep (se 1 (by rfl) ⟨953600, by rfl⟩ : syracuseStep 1271467 = 1907201) B1907201
theorem B31057901 : Blo 595291 31057901 := bstep (se 3 (by rfl) ⟨5823356, by rfl⟩ : syracuseStep 31057901 = 11646713) B11646713
theorem B2550487 : Blo 595291 2550487 := bstep (se 1 (by rfl) ⟨1912865, by rfl⟩ : syracuseStep 2550487 = 3825731) B3825731
theorem B3828653 : Blo 595291 3828653 := bstep (se 3 (by rfl) ⟨717872, by rfl⟩ : syracuseStep 3828653 = 1435745) B1435745
theorem B1272827 : Blo 595291 1272827 := bstep (se 1 (by rfl) ⟨954620, by rfl⟩ : syracuseStep 1272827 = 1909241) B1909241
theorem B3632363 : Blo 595291 3632363 := bstep (se 1 (by rfl) ⟨2724272, by rfl⟩ : syracuseStep 3632363 = 5448545) B5448545
theorem B1208297 : Blo 595291 1208297 := bstep (se 2 (by rfl) ⟨453111, by rfl⟩ : syracuseStep 1208297 = 906223) B906223
theorem B1437851 : Blo 595291 1437851 := bstep (se 1 (by rfl) ⟨1078388, by rfl⟩ : syracuseStep 1437851 = 2156777) B2156777
theorem B2552161 : Blo 595291 2552161 := bstep (se 2 (by rfl) ⟨957060, by rfl⟩ : syracuseStep 2552161 = 1914121) B1914121
theorem B3633547 : Blo 595291 3633547 := bstep (se 1 (by rfl) ⟨2725160, by rfl⟩ : syracuseStep 3633547 = 5450321) B5450321
theorem B12874301 : Blo 595291 12874301 := bstep (se 3 (by rfl) ⟨2413931, by rfl⟩ : syracuseStep 12874301 = 4827863) B4827863
theorem B5730911 : Blo 595291 5730911 := bstep (se 1 (by rfl) ⟨4298183, by rfl⟩ : syracuseStep 5730911 = 8596367) B8596367
theorem B1438697 : Blo 595291 1438697 := bstep (se 2 (by rfl) ⟨539511, by rfl⟩ : syracuseStep 1438697 = 1079023) B1079023
theorem B7632083 : Blo 595291 7632083 := bstep (se 1 (by rfl) ⟨5724062, by rfl⟩ : syracuseStep 7632083 = 11448125) B11448125
theorem B1341467 : Blo 595291 1341467 := bstep (se 1 (by rfl) ⟨1006100, by rfl⟩ : syracuseStep 1341467 = 2012201) B2012201
theorem B23197751 : Blo 595291 23197751 := bstep (se 1 (by rfl) ⟨17398313, by rfl⟩ : syracuseStep 23197751 = 34796627) B34796627
theorem B1702079 : Blo 595291 1702079 := bstep (se 1 (by rfl) ⟨1276559, by rfl⟩ : syracuseStep 1702079 = 2553119) B2553119
theorem B4356299 : Blo 595291 4356299 := bstep (se 1 (by rfl) ⟨3267224, by rfl⟩ : syracuseStep 4356299 = 6534449) B6534449
theorem B2554861 : Blo 595291 2554861 := bstep (se 3 (by rfl) ⟨479036, by rfl⟩ : syracuseStep 2554861 = 958073) B958073
theorem B1342619 : Blo 595291 1342619 := bstep (se 1 (by rfl) ⟨1006964, by rfl⟩ : syracuseStep 1342619 = 2013929) B2013929
theorem B3833243 : Blo 595291 3833243 := bstep (se 1 (by rfl) ⟨2874932, by rfl⟩ : syracuseStep 3833243 = 5749865) B5749865
theorem B1343663 : Blo 595291 1343663 := bstep (se 1 (by rfl) ⟨1007747, by rfl⟩ : syracuseStep 1343663 = 2015495) B2015495
theorem B4096775 : Blo 595291 4096775 := bstep (se 1 (by rfl) ⟨3072581, by rfl⟩ : syracuseStep 4096775 = 6145163) B6145163
theorem B1344383 : Blo 595291 1344383 := bstep (se 1 (by rfl) ⟨1008287, by rfl⟩ : syracuseStep 1344383 = 2016575) B2016575
theorem B1344923 : Blo 595291 1344923 := bstep (se 1 (by rfl) ⟨1008692, by rfl⟩ : syracuseStep 1344923 = 2017385) B2017385
theorem B14517751 : Blo 595291 14517751 := bstep (se 1 (by rfl) ⟨10888313, by rfl⟩ : syracuseStep 14517751 = 21776627) B21776627
theorem B1935019 : Blo 595291 1935019 := bstep (se 1 (by rfl) ⟨1451264, by rfl⟩ : syracuseStep 1935019 = 2902529) B2902529
theorem B3016439 : Blo 595291 3016439 := bstep (se 1 (by rfl) ⟨2262329, by rfl⟩ : syracuseStep 3016439 = 4524659) B4524659
theorem B1345499 : Blo 595291 1345499 := bstep (se 1 (by rfl) ⟨1009124, by rfl⟩ : syracuseStep 1345499 = 2018249) B2018249
theorem B1345607 : Blo 595291 1345607 := bstep (se 1 (by rfl) ⟨1009205, by rfl⟩ : syracuseStep 1345607 = 2018411) B2018411
theorem B4098251 : Blo 595291 4098251 := bstep (se 1 (by rfl) ⟨3073688, by rfl⟩ : syracuseStep 4098251 = 6147377) B6147377
theorem B3017087 : Blo 595291 3017087 := bstep (se 1 (by rfl) ⟨2262815, by rfl⟩ : syracuseStep 3017087 = 4525631) B4525631
theorem B5179993 : Blo 595291 5179993 := bstep (se 2 (by rfl) ⟨1942497, by rfl⟩ : syracuseStep 5179993 = 3884995) B3884995
theorem B1510123 : Blo 595291 1510123 := bstep (se 1 (by rfl) ⟨1132592, by rfl⟩ : syracuseStep 1510123 = 2265185) B2265185
theorem B757279 : Blo 595291 757279 := bstep (se 1 (by rfl) ⟨567959, by rfl⟩ : syracuseStep 757279 = 1135919) B1135919
theorem B1511095 : Blo 595291 1511095 := bstep (se 1 (by rfl) ⟨1133321, by rfl⟩ : syracuseStep 1511095 = 2266643) B2266643
theorem B2559869 : Blo 595291 2559869 := bstep (se 3 (by rfl) ⟨479975, by rfl⟩ : syracuseStep 2559869 = 959951) B959951
theorem B1511419 : Blo 595291 1511419 := bstep (se 1 (by rfl) ⟨1133564, by rfl⟩ : syracuseStep 1511419 = 2267129) B2267129
theorem B15339617 : Blo 595291 15339617 := bstep (se 2 (by rfl) ⟨5752356, by rfl⟩ : syracuseStep 15339617 = 11504713) B11504713
theorem B954671 : Blo 595291 954671 := bstep (se 1 (by rfl) ⟨716003, by rfl⟩ : syracuseStep 954671 = 1432007) B1432007
theorem B4526603 : Blo 595291 4526603 := bstep (se 1 (by rfl) ⟨3394952, by rfl⟩ : syracuseStep 4526603 = 6789905) B6789905
theorem B5739133 : Blo 595291 5739133 := bstep (se 3 (by rfl) ⟨1076087, by rfl⟩ : syracuseStep 5739133 = 2152175) B2152175
theorem B23270075 : Blo 595291 23270075 := bstep (se 1 (by rfl) ⟨17452556, by rfl⟩ : syracuseStep 23270075 = 34905113) B34905113
theorem B1610543 : Blo 595291 1610543 := bstep (se 1 (by rfl) ⟨1207907, by rfl⟩ : syracuseStep 1610543 = 2415815) B2415815
theorem B1152319 : Blo 595291 1152319 := bstep (se 1 (by rfl) ⟨864239, by rfl⟩ : syracuseStep 1152319 = 1728479) B1728479
theorem B595407 : Blo 595291 595407 := bstep (se 1 (by rfl) ⟨446555, by rfl⟩ : syracuseStep 595407 = 893111) B893111
theorem B595487 : Blo 595291 595487 := bstep (se 1 (by rfl) ⟨446615, by rfl⟩ : syracuseStep 595487 = 893231) B893231
theorem B1381979 : Blo 595291 1381979 := bstep (se 1 (by rfl) ⟨1036484, by rfl⟩ : syracuseStep 1381979 = 2072969) B2072969
theorem B595647 : Blo 595291 595647 := bstep (se 1 (by rfl) ⟨446735, by rfl⟩ : syracuseStep 595647 = 893471) B893471
theorem B2332385 : Blo 595291 2332385 := bstep (se 2 (by rfl) ⟨874644, by rfl⟩ : syracuseStep 2332385 = 1749289) B1749289
theorem B595687 : Blo 595291 595687 := bstep (se 1 (by rfl) ⟨446765, by rfl⟩ : syracuseStep 595687 = 893531) B893531
theorem B2627407 : Blo 595291 2627407 := bstep (se 1 (by rfl) ⟨1970555, by rfl⟩ : syracuseStep 2627407 = 3941111) B3941111
theorem B596031 : Blo 595291 596031 := bstep (se 1 (by rfl) ⟨447023, by rfl⟩ : syracuseStep 596031 = 894047) B894047
theorem B596071 : Blo 595291 596071 := bstep (se 1 (by rfl) ⟨447053, by rfl⟩ : syracuseStep 596071 = 894107) B894107
theorem B596379 : Blo 595291 596379 := bstep (se 1 (by rfl) ⟨447284, by rfl⟩ : syracuseStep 596379 = 894569) B894569
theorem B30284225 : Blo 595291 30284225 := bstep (se 2 (by rfl) ⟨11356584, by rfl⟩ : syracuseStep 30284225 = 22713169) B22713169
theorem B596463 : Blo 595291 596463 := bstep (se 1 (by rfl) ⟨447347, by rfl⟩ : syracuseStep 596463 = 894695) B894695
theorem B596527 : Blo 595291 596527 := bstep (se 1 (by rfl) ⟨447395, by rfl⟩ : syracuseStep 596527 = 894791) B894791
theorem B4856473 : Blo 595291 4856473 := bstep (se 2 (by rfl) ⟨1821177, by rfl⟩ : syracuseStep 4856473 = 3642355) B3642355
theorem B596799 : Blo 595291 596799 := bstep (se 1 (by rfl) ⟨447599, by rfl⟩ : syracuseStep 596799 = 895199) B895199
theorem B596839 : Blo 595291 596839 := bstep (se 1 (by rfl) ⟨447629, by rfl⟩ : syracuseStep 596839 = 895259) B895259
theorem B596927 : Blo 595291 596927 := bstep (se 1 (by rfl) ⟨447695, by rfl⟩ : syracuseStep 596927 = 895391) B895391
theorem B597055 : Blo 595291 597055 := bstep (se 1 (by rfl) ⟨447791, by rfl⟩ : syracuseStep 597055 = 895583) B895583
theorem B597275 : Blo 595291 597275 := bstep (se 1 (by rfl) ⟨447956, by rfl⟩ : syracuseStep 597275 = 895913) B895913
theorem B3022109 : Blo 595291 3022109 := bstep (se 3 (by rfl) ⟨566645, by rfl⟩ : syracuseStep 3022109 = 1133291) B1133291
theorem B597295 : Blo 595291 597295 := bstep (se 1 (by rfl) ⟨447971, by rfl⟩ : syracuseStep 597295 = 895943) B895943
theorem B1940809 : Blo 595291 1940809 := bstep (se 2 (by rfl) ⟨727803, by rfl⟩ : syracuseStep 1940809 = 1455607) B1455607
theorem B597375 : Blo 595291 597375 := bstep (se 1 (by rfl) ⟨448031, by rfl⟩ : syracuseStep 597375 = 896063) B896063
theorem B597535 : Blo 595291 597535 := bstep (se 1 (by rfl) ⟨448151, by rfl⟩ : syracuseStep 597535 = 896303) B896303
theorem B597659 : Blo 595291 597659 := bstep (se 1 (by rfl) ⟨448244, by rfl⟩ : syracuseStep 597659 = 896489) B896489
theorem B597695 : Blo 595291 597695 := bstep (se 1 (by rfl) ⟨448271, by rfl⟩ : syracuseStep 597695 = 896543) B896543
theorem B597755 : Blo 595291 597755 := bstep (se 1 (by rfl) ⟨448316, by rfl⟩ : syracuseStep 597755 = 896633) B896633
theorem B597919 : Blo 595291 597919 := bstep (se 1 (by rfl) ⟨448439, by rfl⟩ : syracuseStep 597919 = 896879) B896879
theorem B598087 : Blo 595291 598087 := bstep (se 1 (by rfl) ⟨448565, by rfl⟩ : syracuseStep 598087 = 897131) B897131
theorem B958567 : Blo 595291 958567 := bstep (se 1 (by rfl) ⟨718925, by rfl⟩ : syracuseStep 958567 = 1437851) B1437851
theorem B4857965 : Blo 595291 4857965 := bstep (se 3 (by rfl) ⟨910868, by rfl⟩ : syracuseStep 4857965 = 1821737) B1821737
theorem B598375 : Blo 595291 598375 := bstep (se 1 (by rfl) ⟨448781, by rfl⟩ : syracuseStep 598375 = 897563) B897563
theorem B598495 : Blo 595291 598495 := bstep (se 1 (by rfl) ⟨448871, by rfl⟩ : syracuseStep 598495 = 897743) B897743
theorem B959131 : Blo 595291 959131 := bstep (se 1 (by rfl) ⟨719348, by rfl⟩ : syracuseStep 959131 = 1438697) B1438697
theorem B598687 : Blo 595291 598687 := bstep (se 1 (by rfl) ⟨449015, by rfl⟩ : syracuseStep 598687 = 898031) B898031
theorem B5088055 : Blo 595291 5088055 := bstep (se 1 (by rfl) ⟨3816041, by rfl⟩ : syracuseStep 5088055 = 7632083) B7632083
theorem B598943 : Blo 595291 598943 := bstep (se 1 (by rfl) ⟨449207, by rfl⟩ : syracuseStep 598943 = 898415) B898415
theorem B599023 : Blo 595291 599023 := bstep (se 1 (by rfl) ⟨449267, by rfl⟩ : syracuseStep 599023 = 898535) B898535
theorem B599143 : Blo 595291 599143 := bstep (se 1 (by rfl) ⟨449357, by rfl⟩ : syracuseStep 599143 = 898715) B898715
theorem B894311 : Blo 595291 894311 := bstep (se 1 (by rfl) ⟨670733, by rfl⟩ : syracuseStep 894311 = 1341467) B1341467
theorem B3024701 : Blo 595291 3024701 := bstep (se 3 (by rfl) ⟨567131, by rfl⟩ : syracuseStep 3024701 = 1134263) B1134263
theorem B37890083 : Blo 595291 37890083 := bstep (se 1 (by rfl) ⟨28417562, by rfl⟩ : syracuseStep 37890083 = 56835125) B56835125
theorem B895079 : Blo 595291 895079 := bstep (se 1 (by rfl) ⟨671309, by rfl⟩ : syracuseStep 895079 = 1342619) B1342619
theorem B895529 : Blo 595291 895529 := bstep (se 2 (by rfl) ⟨335823, by rfl⟩ : syracuseStep 895529 = 671647) B671647
theorem B3222125 : Blo 595291 3222125 := bstep (se 3 (by rfl) ⟨604148, by rfl⟩ : syracuseStep 3222125 = 1208297) B1208297
theorem B4434713 : Blo 595291 4434713 := bstep (se 2 (by rfl) ⟨1663017, by rfl⟩ : syracuseStep 4434713 = 3326035) B3326035
theorem B896111 : Blo 595291 896111 := bstep (se 1 (by rfl) ⟨672083, by rfl⟩ : syracuseStep 896111 = 1344167) B1344167
theorem B896297 : Blo 595291 896297 := bstep (se 2 (by rfl) ⟨336111, by rfl⟩ : syracuseStep 896297 = 672223) B672223
theorem B4369747 : Blo 595291 4369747 := bstep (se 1 (by rfl) ⟨3277310, by rfl⟩ : syracuseStep 4369747 = 6554621) B6554621
theorem B4534379 : Blo 595291 4534379 := bstep (se 1 (by rfl) ⟨3400784, by rfl⟩ : syracuseStep 4534379 = 6801569) B6801569
theorem B34484615 : Blo 595291 34484615 := bstep (se 1 (by rfl) ⟨25863461, by rfl⟩ : syracuseStep 34484615 = 51726923) B51726923
theorem B897449 : Blo 595291 897449 := bstep (se 2 (by rfl) ⟨336543, by rfl⟩ : syracuseStep 897449 = 673087) B673087
theorem B897503 : Blo 595291 897503 := bstep (se 1 (by rfl) ⟨673127, by rfl⟩ : syracuseStep 897503 = 1346255) B1346255
theorem B897647 : Blo 595291 897647 := bstep (se 1 (by rfl) ⟨673235, by rfl⟩ : syracuseStep 897647 = 1346471) B1346471
theorem B897755 : Blo 595291 897755 := bstep (se 1 (by rfl) ⟨673316, by rfl⟩ : syracuseStep 897755 = 1346633) B1346633
theorem B897767 : Blo 595291 897767 := bstep (se 1 (by rfl) ⟨673325, by rfl⟩ : syracuseStep 897767 = 1346651) B1346651
theorem B2011931 : Blo 595291 2011931 := bstep (se 1 (by rfl) ⟨1508948, by rfl⟩ : syracuseStep 2011931 = 3017897) B3017897
theorem B8729855 : Blo 595291 8729855 := bstep (se 1 (by rfl) ⟨6547391, by rfl⟩ : syracuseStep 8729855 = 13094783) B13094783
theorem B79508789 : Blo 595291 79508789 := bstep (se 5 (by rfl) ⟨3726974, by rfl⟩ : syracuseStep 79508789 = 7453949) B7453949
theorem B27571553 : Blo 595291 27571553 := bstep (se 2 (by rfl) ⟨10339332, by rfl⟩ : syracuseStep 27571553 = 20678665) B20678665
theorem B2012687 : Blo 595291 2012687 := bstep (se 1 (by rfl) ⟨1509515, by rfl⟩ : syracuseStep 2012687 = 3019031) B3019031
theorem B3028589 : Blo 595291 3028589 := bstep (se 3 (by rfl) ⟨567860, by rfl⟩ : syracuseStep 3028589 = 1135721) B1135721
theorem B898907 : Blo 595291 898907 := bstep (se 1 (by rfl) ⟨674180, by rfl⟩ : syracuseStep 898907 = 1348361) B1348361
theorem B2013767 : Blo 595291 2013767 := bstep (se 1 (by rfl) ⟨1510325, by rfl⟩ : syracuseStep 2013767 = 3020651) B3020651
theorem B2014091 : Blo 595291 2014091 := bstep (se 1 (by rfl) ⟨1510568, by rfl⟩ : syracuseStep 2014091 = 3021137) B3021137
theorem B670783 : Blo 595291 670783 := bstep (se 1 (by rfl) ⟨503087, by rfl⟩ : syracuseStep 670783 = 1006175) B1006175
theorem B3816557 : Blo 595291 3816557 := bstep (se 3 (by rfl) ⟨715604, by rfl⟩ : syracuseStep 3816557 = 1431209) B1431209
theorem B14565329 : Blo 595291 14565329 := bstep (se 2 (by rfl) ⟨5461998, by rfl⟩ : syracuseStep 14565329 = 10923997) B10923997
theorem B671791 : Blo 595291 671791 := bstep (se 1 (by rfl) ⟨503843, by rfl⟩ : syracuseStep 671791 = 1007687) B1007687
theorem B2867567 : Blo 595291 2867567 := bstep (se 1 (by rfl) ⟨2150675, by rfl⟩ : syracuseStep 2867567 = 4301351) B4301351
theorem B11616797 : Blo 595291 11616797 := bstep (se 3 (by rfl) ⟨2178149, by rfl⟩ : syracuseStep 11616797 = 4356299) B4356299
theorem B672583 : Blo 595291 672583 := bstep (se 1 (by rfl) ⟨504437, by rfl⟩ : syracuseStep 672583 = 1008875) B1008875
theorem B14566499 : Blo 595291 14566499 := bstep (se 1 (by rfl) ⟨10924874, by rfl⟩ : syracuseStep 14566499 = 21849749) B21849749
theorem B11519171 : Blo 595291 11519171 := bstep (se 1 (by rfl) ⟨8639378, by rfl⟩ : syracuseStep 11519171 = 17278757) B17278757
theorem B36685001 : Blo 595291 36685001 := bstep (se 2 (by rfl) ⟨13756875, by rfl⟩ : syracuseStep 36685001 = 27513751) B27513751
theorem B22136609 : Blo 595291 22136609 := bstep (se 2 (by rfl) ⟨8301228, by rfl⟩ : syracuseStep 22136609 = 16602457) B16602457
theorem B3393859 : Blo 595291 3393859 := bstep (se 1 (by rfl) ⟨2545394, by rfl⟩ : syracuseStep 3393859 = 5090789) B5090789
theorem B2018087 : Blo 595291 2018087 := bstep (se 1 (by rfl) ⟨1513565, by rfl⟩ : syracuseStep 2018087 = 3027131) B3027131
theorem B3820607 : Blo 595291 3820607 := bstep (se 1 (by rfl) ⟨2865455, by rfl⟩ : syracuseStep 3820607 = 5730911) B5730911
theorem B9686087 : Blo 595291 9686087 := bstep (se 1 (by rfl) ⟨7264565, by rfl⟩ : syracuseStep 9686087 = 14529131) B14529131
theorem B1166543 : Blo 595291 1166543 := bstep (se 1 (by rfl) ⟨874907, by rfl⟩ : syracuseStep 1166543 = 1749815) B1749815
theorem B2018519 : Blo 595291 2018519 := bstep (se 1 (by rfl) ⟨1513889, by rfl⟩ : syracuseStep 2018519 = 3027779) B3027779
theorem B2018681 : Blo 595291 2018681 := bstep (se 2 (by rfl) ⟨757005, by rfl⟩ : syracuseStep 2018681 = 1514011) B1514011
theorem B2018843 : Blo 595291 2018843 := bstep (se 1 (by rfl) ⟨1514132, by rfl⟩ : syracuseStep 2018843 = 3028265) B3028265
theorem B1134719 : Blo 595291 1134719 := bstep (se 1 (by rfl) ⟨851039, by rfl⟩ : syracuseStep 1134719 = 1702079) B1702079
theorem B3921095 : Blo 595291 3921095 := bstep (se 1 (by rfl) ⟨2940821, by rfl⟩ : syracuseStep 3921095 = 5881643) B5881643
theorem B1005439 : Blo 595291 1005439 := bstep (se 1 (by rfl) ⟨754079, by rfl⟩ : syracuseStep 1005439 = 1508159) B1508159
theorem B2021651 : Blo 595291 2021651 := bstep (se 1 (by rfl) ⟨1516238, by rfl⟩ : syracuseStep 2021651 = 3032477) B3032477
theorem B1005851 : Blo 595291 1005851 := bstep (se 1 (by rfl) ⟨754388, by rfl⟩ : syracuseStep 1005851 = 1508777) B1508777
theorem B2021759 : Blo 595291 2021759 := bstep (se 1 (by rfl) ⟨1516319, by rfl⟩ : syracuseStep 2021759 = 3032639) B3032639
theorem B1137377 : Blo 595291 1137377 := bstep (se 2 (by rfl) ⟨426516, by rfl⟩ : syracuseStep 1137377 = 853033) B853033
theorem B1137415 : Blo 595291 1137415 := bstep (se 1 (by rfl) ⟨853061, by rfl⟩ : syracuseStep 1137415 = 1706123) B1706123
theorem B1006823 : Blo 595291 1006823 := bstep (se 1 (by rfl) ⟨755117, by rfl⟩ : syracuseStep 1006823 = 1510235) B1510235
theorem B1006843 : Blo 595291 1006843 := bstep (se 1 (by rfl) ⟨755132, by rfl⟩ : syracuseStep 1006843 = 1510265) B1510265
theorem B2417309 : Blo 595291 2417309 := bstep (se 3 (by rfl) ⟨453245, by rfl⟩ : syracuseStep 2417309 = 906491) B906491
theorem B4547501 : Blo 595291 4547501 := bstep (se 3 (by rfl) ⟨852656, by rfl⟩ : syracuseStep 4547501 = 1705313) B1705313
theorem B3400649 : Blo 595291 3400649 := bstep (se 2 (by rfl) ⟨1275243, by rfl⟩ : syracuseStep 3400649 = 2550487) B2550487
theorem B2876411 : Blo 595291 2876411 := bstep (se 1 (by rfl) ⟨2157308, by rfl⟩ : syracuseStep 2876411 = 4314617) B4314617
theorem B4154807 : Blo 595291 4154807 := bstep (se 1 (by rfl) ⟨3116105, by rfl⟩ : syracuseStep 4154807 = 6232211) B6232211
theorem B1009307 : Blo 595291 1009307 := bstep (se 1 (by rfl) ⟨756980, by rfl⟩ : syracuseStep 1009307 = 1513961) B1513961
theorem B3827371 : Blo 595291 3827371 := bstep (se 1 (by rfl) ⟨2870528, by rfl⟩ : syracuseStep 3827371 = 5741057) B5741057
theorem B1697831 : Blo 595291 1697831 := bstep (se 1 (by rfl) ⟨1273373, by rfl⟩ : syracuseStep 1697831 = 2546747) B2546747
theorem B1271963 : Blo 595291 1271963 := bstep (se 1 (by rfl) ⟨953972, by rfl⟩ : syracuseStep 1271963 = 1907945) B1907945
theorem B1698023 : Blo 595291 1698023 := bstep (se 1 (by rfl) ⟨1273517, by rfl⟩ : syracuseStep 1698023 = 2547035) B2547035
theorem B1010279 : Blo 595291 1010279 := bstep (se 1 (by rfl) ⟨757709, by rfl⟩ : syracuseStep 1010279 = 1515419) B1515419
theorem B1436399 : Blo 595291 1436399 := bstep (se 1 (by rfl) ⟨1077299, by rfl⟩ : syracuseStep 1436399 = 2154599) B2154599
theorem B3402881 : Blo 595291 3402881 := bstep (se 2 (by rfl) ⟨1276080, by rfl⟩ : syracuseStep 3402881 = 2552161) B2552161
theorem B4844729 : Blo 595291 4844729 := bstep (se 2 (by rfl) ⟨1816773, by rfl⟩ : syracuseStep 4844729 = 3633547) B3633547
theorem B1699163 : Blo 595291 1699163 := bstep (se 1 (by rfl) ⟨1274372, by rfl⟩ : syracuseStep 1699163 = 2548745) B2548745
theorem B1207679 : Blo 595291 1207679 := bstep (se 1 (by rfl) ⟨905759, by rfl⟩ : syracuseStep 1207679 = 1811519) B1811519
theorem B1699231 : Blo 595291 1699231 := bstep (se 1 (by rfl) ⟨1274423, by rfl⟩ : syracuseStep 1699231 = 2548847) B2548847
theorem B1273279 : Blo 595291 1273279 := bstep (se 1 (by rfl) ⟨954959, by rfl⟩ : syracuseStep 1273279 = 1909919) B1909919
theorem B1437167 : Blo 595291 1437167 := bstep (se 1 (by rfl) ⟨1077875, by rfl⟩ : syracuseStep 1437167 = 2155751) B2155751
theorem B1208135 : Blo 595291 1208135 := bstep (se 1 (by rfl) ⟨906101, by rfl⟩ : syracuseStep 1208135 = 1812203) B1812203
theorem B20705267 : Blo 595291 20705267 := bstep (se 1 (by rfl) ⟨15528950, by rfl⟩ : syracuseStep 20705267 = 31057901) B31057901
theorem B2552435 : Blo 595291 2552435 := bstep (se 1 (by rfl) ⟨1914326, by rfl⟩ : syracuseStep 2552435 = 3828653) B3828653
theorem B848551 : Blo 595291 848551 := bstep (se 1 (by rfl) ⟨636413, by rfl⟩ : syracuseStep 848551 = 1272827) B1272827
theorem B11629271 : Blo 595291 11629271 := bstep (se 1 (by rfl) ⟨8721953, by rfl⟩ : syracuseStep 11629271 = 17443907) B17443907
theorem B2421575 : Blo 595291 2421575 := bstep (se 1 (by rfl) ⟨1816181, by rfl⟩ : syracuseStep 2421575 = 3632363) B3632363
theorem B2159441 : Blo 595291 2159441 := bstep (se 2 (by rfl) ⟨809790, by rfl⟩ : syracuseStep 2159441 = 1619581) B1619581
theorem B8582867 : Blo 595291 8582867 := bstep (se 1 (by rfl) ⟨6437150, by rfl⟩ : syracuseStep 8582867 = 12874301) B12874301
theorem B1341305 : Blo 595291 1341305 := bstep (se 2 (by rfl) ⟨502989, by rfl⟩ : syracuseStep 1341305 = 1005979) B1005979
theorem B6781157 : Blo 595291 6781157 := bstep (se 4 (by rfl) ⟨635733, by rfl⟩ : syracuseStep 6781157 = 1271467) B1271467
theorem B1210793 : Blo 595291 1210793 := bstep (se 2 (by rfl) ⟨454047, by rfl⟩ : syracuseStep 1210793 = 908095) B908095
theorem B1342007 : Blo 595291 1342007 := bstep (se 1 (by rfl) ⟨1006505, by rfl⟩ : syracuseStep 1342007 = 2013011) B2013011
theorem B1342079 : Blo 595291 1342079 := bstep (se 1 (by rfl) ⟨1006559, by rfl⟩ : syracuseStep 1342079 = 2013119) B2013119
theorem B3406481 : Blo 595291 3406481 := bstep (se 2 (by rfl) ⟨1277430, by rfl⟩ : syracuseStep 3406481 = 2554861) B2554861
theorem B15465167 : Blo 595291 15465167 := bstep (se 1 (by rfl) ⟨11598875, by rfl⟩ : syracuseStep 15465167 = 23197751) B23197751
theorem B4521257 : Blo 595291 4521257 := bstep (se 2 (by rfl) ⟨1695471, by rfl⟩ : syracuseStep 4521257 = 3390943) B3390943
theorem B2555495 : Blo 595291 2555495 := bstep (se 1 (by rfl) ⟨1916621, by rfl⟩ : syracuseStep 2555495 = 3833243) B3833243
theorem B4292473 : Blo 595291 4292473 := bstep (se 2 (by rfl) ⟨1609677, by rfl⟩ : syracuseStep 4292473 = 3219355) B3219355
theorem B2260979 : Blo 595291 2260979 := bstep (se 1 (by rfl) ⟨1695734, by rfl⟩ : syracuseStep 2260979 = 3391469) B3391469
theorem B1278089 : Blo 595291 1278089 := bstep (se 2 (by rfl) ⟨479283, by rfl⟩ : syracuseStep 1278089 = 958567) B958567
theorem B1278841 : Blo 595291 1278841 := bstep (se 2 (by rfl) ⟨479565, by rfl⟩ : syracuseStep 1278841 = 959131) B959131
theorem B6784073 : Blo 595291 6784073 := bstep (se 2 (by rfl) ⟨2544027, by rfl⟩ : syracuseStep 6784073 = 5088055) B5088055
theorem B1345391 : Blo 595291 1345391 := bstep (se 1 (by rfl) ⟨1009043, by rfl⟩ : syracuseStep 1345391 = 2018087) B2018087
theorem B6457391 : Blo 595291 6457391 := bstep (se 1 (by rfl) ⟨4843043, by rfl⟩ : syracuseStep 6457391 = 9686087) B9686087
theorem B4294781 : Blo 595291 4294781 := bstep (se 3 (by rfl) ⟨805271, by rfl⟩ : syracuseStep 4294781 = 1610543) B1610543
theorem B1345679 : Blo 595291 1345679 := bstep (se 1 (by rfl) ⟨1009259, by rfl⟩ : syracuseStep 1345679 = 2018519) B2018519
theorem B1345787 : Blo 595291 1345787 := bstep (se 1 (by rfl) ⟨1009340, by rfl⟩ : syracuseStep 1345787 = 2018681) B2018681
theorem B1345895 : Blo 595291 1345895 := bstep (se 1 (by rfl) ⟨1009421, by rfl⟩ : syracuseStep 1345895 = 2018843) B2018843
theorem B1706579 : Blo 595291 1706579 := bstep (se 1 (by rfl) ⟨1279934, by rfl⟩ : syracuseStep 1706579 = 2559869) B2559869
theorem B10226411 : Blo 595291 10226411 := bstep (se 1 (by rfl) ⟨7669808, by rfl⟩ : syracuseStep 10226411 = 15339617) B15339617
theorem B756479 : Blo 595291 756479 := bstep (se 1 (by rfl) ⟨567359, by rfl⟩ : syracuseStep 756479 = 1134719) B1134719
theorem B3017735 : Blo 595291 3017735 := bstep (se 1 (by rfl) ⟨2263301, by rfl⟩ : syracuseStep 3017735 = 4526603) B4526603
theorem B4525145 : Blo 595291 4525145 := bstep (se 2 (by rfl) ⟨1696929, by rfl⟩ : syracuseStep 4525145 = 3393859) B3393859
theorem B27626629 : Blo 595291 27626629 := bstep (se 4 (by rfl) ⟨2589996, by rfl⟩ : syracuseStep 27626629 = 5179993) B5179993
theorem B10456253 : Blo 595291 10456253 := bstep (se 3 (by rfl) ⟨1960547, by rfl⟩ : syracuseStep 10456253 = 3921095) B3921095
theorem B12881909 : Blo 595291 12881909 := bstep (se 5 (by rfl) ⟨603839, by rfl⟩ : syracuseStep 12881909 = 1207679) B1207679
theorem B1347767 : Blo 595291 1347767 := bstep (se 1 (by rfl) ⟨1010825, by rfl⟩ : syracuseStep 1347767 = 2021651) B2021651
theorem B1347839 : Blo 595291 1347839 := bstep (se 1 (by rfl) ⟨1010879, by rfl⟩ : syracuseStep 1347839 = 2021759) B2021759
theorem B20189483 : Blo 595291 20189483 := bstep (se 1 (by rfl) ⟨15142112, by rfl⟩ : syracuseStep 20189483 = 30284225) B30284225
theorem B12915125 : Blo 595291 12915125 := bstep (se 5 (by rfl) ⟨605396, by rfl⟩ : syracuseStep 12915125 = 1210793) B1210793
theorem B758251 : Blo 595291 758251 := bstep (se 1 (by rfl) ⟨568688, by rfl⟩ : syracuseStep 758251 = 1137377) B1137377
theorem B2265641 : Blo 595291 2265641 := bstep (se 2 (by rfl) ⟨849615, by rfl⟩ : syracuseStep 2265641 = 1699231) B1699231
theorem B1611539 : Blo 595291 1611539 := bstep (se 1 (by rfl) ⟨1208654, by rfl⟩ : syracuseStep 1611539 = 2417309) B2417309
theorem B4528061 : Blo 595291 4528061 := bstep (se 3 (by rfl) ⟨849011, by rfl⟩ : syracuseStep 4528061 = 1698023) B1698023
theorem B2267099 : Blo 595291 2267099 := bstep (se 1 (by rfl) ⟨1700324, by rfl⟩ : syracuseStep 2267099 = 3400649) B3400649
theorem B596207 : Blo 595291 596207 := bstep (se 1 (by rfl) ⟨447155, by rfl⟩ : syracuseStep 596207 = 894311) B894311
theorem B596719 : Blo 595291 596719 := bstep (se 1 (by rfl) ⟨447539, by rfl⟩ : syracuseStep 596719 = 895079) B895079
theorem B597019 : Blo 595291 597019 := bstep (se 1 (by rfl) ⟨447764, by rfl⟩ : syracuseStep 597019 = 895529) B895529
theorem B957599 : Blo 595291 957599 := bstep (se 1 (by rfl) ⟨718199, by rfl⟩ : syracuseStep 957599 = 1436399) B1436399
theorem B2956475 : Blo 595291 2956475 := bstep (se 1 (by rfl) ⟨2217356, by rfl⟩ : syracuseStep 2956475 = 4434713) B4434713
theorem B597407 : Blo 595291 597407 := bstep (se 1 (by rfl) ⟨448055, by rfl⟩ : syracuseStep 597407 = 896111) B896111
theorem B2268587 : Blo 595291 2268587 := bstep (se 1 (by rfl) ⟨1701440, by rfl⟩ : syracuseStep 2268587 = 3402881) B3402881
theorem B597531 : Blo 595291 597531 := bstep (se 1 (by rfl) ⟨448148, by rfl⟩ : syracuseStep 597531 = 896297) B896297
theorem B958111 : Blo 595291 958111 := bstep (se 1 (by rfl) ⟨718583, by rfl⟩ : syracuseStep 958111 = 1437167) B1437167
theorem B3022919 : Blo 595291 3022919 := bstep (se 1 (by rfl) ⟨2267189, by rfl⟩ : syracuseStep 3022919 = 4534379) B4534379
theorem B598299 : Blo 595291 598299 := bstep (se 1 (by rfl) ⟨448724, by rfl⟩ : syracuseStep 598299 = 897449) B897449
theorem B598335 : Blo 595291 598335 := bstep (se 1 (by rfl) ⟨448751, by rfl⟩ : syracuseStep 598335 = 897503) B897503
theorem B598431 : Blo 595291 598431 := bstep (se 1 (by rfl) ⟨448823, by rfl⟩ : syracuseStep 598431 = 897647) B897647
theorem B598503 : Blo 595291 598503 := bstep (se 1 (by rfl) ⟨448877, by rfl⟩ : syracuseStep 598503 = 897755) B897755
theorem B12919277 : Blo 595291 12919277 := bstep (se 3 (by rfl) ⟨2422364, by rfl⟩ : syracuseStep 12919277 = 4844729) B4844729
theorem B598511 : Blo 595291 598511 := bstep (se 1 (by rfl) ⟨448883, by rfl⟩ : syracuseStep 598511 = 897767) B897767
theorem B1614383 : Blo 595291 1614383 := bstep (se 1 (by rfl) ⟨1210787, by rfl⟩ : syracuseStep 1614383 = 2421575) B2421575
theorem B1516553 : Blo 595291 1516553 := bstep (se 2 (by rfl) ⟨568707, by rfl⟩ : syracuseStep 1516553 = 1137415) B1137415
theorem B599271 : Blo 595291 599271 := bstep (se 1 (by rfl) ⟨449453, by rfl⟩ : syracuseStep 599271 = 898907) B898907
theorem B894203 : Blo 595291 894203 := bstep (se 1 (by rfl) ⟨670652, by rfl⟩ : syracuseStep 894203 = 1341305) B1341305
theorem B894377 : Blo 595291 894377 := bstep (se 2 (by rfl) ⟨335391, by rfl⟩ : syracuseStep 894377 = 670783) B670783
theorem B894671 : Blo 595291 894671 := bstep (se 1 (by rfl) ⟨671003, by rfl⟩ : syracuseStep 894671 = 1342007) B1342007
theorem B894719 : Blo 595291 894719 := bstep (se 1 (by rfl) ⟨671039, by rfl⟩ : syracuseStep 894719 = 1342079) B1342079
theorem B2270987 : Blo 595291 2270987 := bstep (se 1 (by rfl) ⟨1703240, by rfl⟩ : syracuseStep 2270987 = 3406481) B3406481
theorem B3221693 : Blo 595291 3221693 := bstep (se 3 (by rfl) ⟨604067, by rfl⟩ : syracuseStep 3221693 = 1208135) B1208135
theorem B9710219 : Blo 595291 9710219 := bstep (se 1 (by rfl) ⟨7282664, by rfl⟩ : syracuseStep 9710219 = 14565329) B14565329
theorem B895721 : Blo 595291 895721 := bstep (se 2 (by rfl) ⟨335895, by rfl⟩ : syracuseStep 895721 = 671791) B671791
theorem B895775 : Blo 595291 895775 := bstep (se 1 (by rfl) ⟨671831, by rfl⟩ : syracuseStep 895775 = 1343663) B1343663
theorem B896255 : Blo 595291 896255 := bstep (se 1 (by rfl) ⟨672191, by rfl⟩ : syracuseStep 896255 = 1344383) B1344383
theorem B9710999 : Blo 595291 9710999 := bstep (se 1 (by rfl) ⟨7283249, by rfl⟩ : syracuseStep 9710999 = 14566499) B14566499
theorem B7679447 : Blo 595291 7679447 := bstep (se 1 (by rfl) ⟨5759585, by rfl⟩ : syracuseStep 7679447 = 11519171) B11519171
theorem B24456667 : Blo 595291 24456667 := bstep (se 1 (by rfl) ⟨18342500, by rfl⟩ : syracuseStep 24456667 = 36685001) B36685001
theorem B896615 : Blo 595291 896615 := bstep (se 1 (by rfl) ⟨672461, by rfl⟩ : syracuseStep 896615 = 1344923) B1344923
theorem B7646845 : Blo 595291 7646845 := bstep (se 3 (by rfl) ⟨1433783, by rfl⟩ : syracuseStep 7646845 = 2867567) B2867567
theorem B896777 : Blo 595291 896777 := bstep (se 2 (by rfl) ⟨336291, by rfl⟩ : syracuseStep 896777 = 672583) B672583
theorem B2010959 : Blo 595291 2010959 := bstep (se 1 (by rfl) ⟨1508219, by rfl⟩ : syracuseStep 2010959 = 3016439) B3016439
theorem B896999 : Blo 595291 896999 := bstep (se 1 (by rfl) ⟨672749, by rfl⟩ : syracuseStep 896999 = 1345499) B1345499
theorem B897071 : Blo 595291 897071 := bstep (se 1 (by rfl) ⟨672803, by rfl⟩ : syracuseStep 897071 = 1345607) B1345607
theorem B30978125 : Blo 595291 30978125 := bstep (se 3 (by rfl) ⟨5808398, by rfl⟩ : syracuseStep 30978125 = 11616797) B11616797
theorem B2732167 : Blo 595291 2732167 := bstep (se 1 (by rfl) ⟨2049125, by rfl⟩ : syracuseStep 2732167 = 4098251) B4098251
theorem B2011391 : Blo 595291 2011391 := bstep (se 1 (by rfl) ⟨1508543, by rfl⟩ : syracuseStep 2011391 = 3017087) B3017087
theorem B10924733 : Blo 595291 10924733 := bstep (se 3 (by rfl) ⟨2048387, by rfl⟩ : syracuseStep 10924733 = 4096775) B4096775
theorem B15513383 : Blo 595291 15513383 := bstep (se 1 (by rfl) ⟨11635037, by rfl⟩ : syracuseStep 15513383 = 23270075) B23270075
theorem B2013497 : Blo 595291 2013497 := bstep (se 2 (by rfl) ⟨755061, by rfl⟩ : syracuseStep 2013497 = 1510123) B1510123
theorem B1554923 : Blo 595291 1554923 := bstep (se 1 (by rfl) ⟨1166192, by rfl⟩ : syracuseStep 1554923 = 2332385) B2332385
theorem B670567 : Blo 595291 670567 := bstep (se 1 (by rfl) ⟨502925, by rfl⟩ : syracuseStep 670567 = 1005851) B1005851
theorem B3685277 : Blo 595291 3685277 := bstep (se 3 (by rfl) ⟨690989, by rfl⟩ : syracuseStep 3685277 = 1381979) B1381979
theorem B59030957 : Blo 595291 59030957 := bstep (se 3 (by rfl) ⟨11068304, by rfl⟩ : syracuseStep 59030957 = 22136609) B22136609
theorem B671215 : Blo 595291 671215 := bstep (se 1 (by rfl) ⟨503411, by rfl⟩ : syracuseStep 671215 = 1006823) B1006823
theorem B2014739 : Blo 595291 2014739 := bstep (se 1 (by rfl) ⟨1511054, by rfl⟩ : syracuseStep 2014739 = 3022109) B3022109
theorem B2014793 : Blo 595291 2014793 := bstep (se 2 (by rfl) ⟨755547, by rfl⟩ : syracuseStep 2014793 = 1511095) B1511095
theorem B2015225 : Blo 595291 2015225 := bstep (se 2 (by rfl) ⟨755709, by rfl⟩ : syracuseStep 2015225 = 1511419) B1511419
theorem B3391901 : Blo 595291 3391901 := bstep (se 3 (by rfl) ⟨635981, by rfl⟩ : syracuseStep 3391901 = 1271963) B1271963
theorem B3031667 : Blo 595291 3031667 := bstep (se 1 (by rfl) ⟨2273750, by rfl⟩ : syracuseStep 3031667 = 4547501) B4547501
theorem B1917607 : Blo 595291 1917607 := bstep (se 1 (by rfl) ⟨1438205, by rfl⟩ : syracuseStep 1917607 = 2876411) B2876411
theorem B7652177 : Blo 595291 7652177 := bstep (se 2 (by rfl) ⟨2869566, by rfl⟩ : syracuseStep 7652177 = 5739133) B5739133
theorem B1131401 : Blo 595291 1131401 := bstep (se 2 (by rfl) ⟨424275, by rfl⟩ : syracuseStep 1131401 = 848551) B848551
theorem B2769871 : Blo 595291 2769871 := bstep (se 1 (by rfl) ⟨2077403, by rfl⟩ : syracuseStep 2769871 = 4154807) B4154807
theorem B672871 : Blo 595291 672871 := bstep (se 1 (by rfl) ⟨504653, by rfl⟩ : syracuseStep 672871 = 1009307) B1009307
theorem B2016467 : Blo 595291 2016467 := bstep (se 1 (by rfl) ⟨1512350, by rfl⟩ : syracuseStep 2016467 = 3024701) B3024701
theorem B1131887 : Blo 595291 1131887 := bstep (se 1 (by rfl) ⟨848915, by rfl⟩ : syracuseStep 1131887 = 1697831) B1697831
theorem B673519 : Blo 595291 673519 := bstep (se 1 (by rfl) ⟨505139, by rfl⟩ : syracuseStep 673519 = 1010279) B1010279
theorem B2148083 : Blo 595291 2148083 := bstep (se 1 (by rfl) ⟨1611062, by rfl⟩ : syracuseStep 2148083 = 3222125) B3222125
theorem B1132775 : Blo 595291 1132775 := bstep (se 1 (by rfl) ⟨849581, by rfl⟩ : syracuseStep 1132775 = 1699163) B1699163
theorem B22989743 : Blo 595291 22989743 := bstep (se 1 (by rfl) ⟨17242307, by rfl⟩ : syracuseStep 22989743 = 34484615) B34484615
theorem B7752847 : Blo 595291 7752847 := bstep (se 1 (by rfl) ⟨5814635, by rfl⟩ : syracuseStep 7752847 = 11629271) B11629271
theorem B5819903 : Blo 595291 5819903 := bstep (se 1 (by rfl) ⟨4364927, by rfl⟩ : syracuseStep 5819903 = 8729855) B8729855
theorem B6475297 : Blo 595291 6475297 := bstep (se 2 (by rfl) ⟨2428236, by rfl⟩ : syracuseStep 6475297 = 4856473) B4856473
theorem B53005859 : Blo 595291 53005859 := bstep (se 1 (by rfl) ⟨39754394, by rfl⟩ : syracuseStep 53005859 = 79508789) B79508789
theorem B2019059 : Blo 595291 2019059 := bstep (se 1 (by rfl) ⟨1514294, by rfl⟩ : syracuseStep 2019059 = 3028589) B3028589
theorem B5721911 : Blo 595291 5721911 := bstep (se 1 (by rfl) ⟨4291433, by rfl⟩ : syracuseStep 5721911 = 8582867) B8582867
theorem B10310111 : Blo 595291 10310111 := bstep (se 1 (by rfl) ⟨7732583, by rfl⟩ : syracuseStep 10310111 = 15465167) B15465167
theorem B2544371 : Blo 595291 2544371 := bstep (se 1 (by rfl) ⟨1908278, by rfl⟩ : syracuseStep 2544371 = 3816557) B3816557
theorem B5723297 : Blo 595291 5723297 := bstep (se 2 (by rfl) ⟨2146236, by rfl⟩ : syracuseStep 5723297 = 4292473) B4292473
theorem B2545789 : Blo 595291 2545789 := bstep (se 3 (by rfl) ⟨477335, by rfl⟩ : syracuseStep 2545789 = 954671) B954671
theorem B19357001 : Blo 595291 19357001 := bstep (se 2 (by rfl) ⟨7258875, by rfl⟩ : syracuseStep 19357001 = 14517751) B14517751
theorem B2547071 : Blo 595291 2547071 := bstep (se 1 (by rfl) ⟨1910303, by rfl⟩ : syracuseStep 2547071 = 3820607) B3820607
theorem B777695 : Blo 595291 777695 := bstep (se 1 (by rfl) ⟨583271, by rfl⟩ : syracuseStep 777695 = 1166543) B1166543
theorem B2580025 : Blo 595291 2580025 := bstep (se 2 (by rfl) ⟨967509, by rfl⟩ : syracuseStep 2580025 = 1935019) B1935019
theorem B5103161 : Blo 595291 5103161 := bstep (se 2 (by rfl) ⟨1913685, by rfl⟩ : syracuseStep 5103161 = 3827371) B3827371
theorem B5826329 : Blo 595291 5826329 := bstep (se 2 (by rfl) ⟨2184873, by rfl⟩ : syracuseStep 5826329 = 4369747) B4369747
theorem B1697705 : Blo 595291 1697705 := bstep (se 2 (by rfl) ⟨636639, by rfl⟩ : syracuseStep 1697705 = 1273279) B1273279
theorem B1009705 : Blo 595291 1009705 := bstep (se 2 (by rfl) ⟨378639, by rfl⟩ : syracuseStep 1009705 = 757279) B757279
theorem B3238643 : Blo 595291 3238643 := bstep (se 1 (by rfl) ⟨2428982, by rfl⟩ : syracuseStep 3238643 = 4857965) B4857965
theorem B25260055 : Blo 595291 25260055 := bstep (se 1 (by rfl) ⟨18945041, by rfl⟩ : syracuseStep 25260055 = 37890083) B37890083
theorem B1536425 : Blo 595291 1536425 := bstep (se 2 (by rfl) ⟨576159, by rfl⟩ : syracuseStep 1536425 = 1152319) B1152319
theorem B3503209 : Blo 595291 3503209 := bstep (se 2 (by rfl) ⟨1313703, by rfl⟩ : syracuseStep 3503209 = 2627407) B2627407
theorem B1340585 : Blo 595291 1340585 := bstep (se 2 (by rfl) ⟨502719, by rfl⟩ : syracuseStep 1340585 = 1005439) B1005439
theorem B1701623 : Blo 595291 1701623 := bstep (se 1 (by rfl) ⟨1276217, by rfl⟩ : syracuseStep 1701623 = 2552435) B2552435
theorem B1341287 : Blo 595291 1341287 := bstep (se 1 (by rfl) ⟨1005965, by rfl⟩ : syracuseStep 1341287 = 2011931) B2011931
theorem B1439627 : Blo 595291 1439627 := bstep (se 1 (by rfl) ⟨1079720, by rfl⟩ : syracuseStep 1439627 = 2159441) B2159441
theorem B18381035 : Blo 595291 18381035 := bstep (se 1 (by rfl) ⟨13785776, by rfl⟩ : syracuseStep 18381035 = 27571553) B27571553
theorem B1341791 : Blo 595291 1341791 := bstep (se 1 (by rfl) ⟨1006343, by rfl⟩ : syracuseStep 1341791 = 2012687) B2012687
theorem B4520771 : Blo 595291 4520771 := bstep (se 1 (by rfl) ⟨3390578, by rfl⟩ : syracuseStep 4520771 = 6781157) B6781157
theorem B1342457 : Blo 595291 1342457 := bstep (se 2 (by rfl) ⟨503421, by rfl⟩ : syracuseStep 1342457 = 1006843) B1006843
theorem B1342511 : Blo 595291 1342511 := bstep (se 1 (by rfl) ⟨1006883, by rfl⟩ : syracuseStep 1342511 = 2013767) B2013767
theorem B2587745 : Blo 595291 2587745 := bstep (se 2 (by rfl) ⟨970404, by rfl⟩ : syracuseStep 2587745 = 1940809) B1940809
theorem B1342727 : Blo 595291 1342727 := bstep (se 1 (by rfl) ⟨1007045, by rfl⟩ : syracuseStep 1342727 = 2014091) B2014091
theorem B3014171 : Blo 595291 3014171 := bstep (se 1 (by rfl) ⟨2260628, by rfl⟩ : syracuseStep 3014171 = 4521257) B4521257
theorem B1703663 : Blo 595291 1703663 := bstep (se 1 (by rfl) ⟨1277747, by rfl⟩ : syracuseStep 1703663 = 2555495) B2555495
theorem B55214045 : Blo 595291 55214045 := bstep (se 3 (by rfl) ⟨10352633, by rfl⟩ : syracuseStep 55214045 = 20705267) B20705267
theorem B1507319 : Blo 595291 1507319 := bstep (se 1 (by rfl) ⟨1130489, by rfl⟩ : syracuseStep 1507319 = 2260979) B2260979
theorem B852059 : Blo 595291 852059 := bstep (se 1 (by rfl) ⟨639044, by rfl⟩ : syracuseStep 852059 = 1278089) B1278089
theorem B2261267 : Blo 595291 2261267 := bstep (se 1 (by rfl) ⟨1695950, by rfl⟩ : syracuseStep 2261267 = 3391901) B3391901
theorem B754267 : Blo 595291 754267 := bstep (se 1 (by rfl) ⟨565700, by rfl⟩ : syracuseStep 754267 = 1131401) B1131401
theorem B4522715 : Blo 595291 4522715 := bstep (se 1 (by rfl) ⟨3392036, by rfl⟩ : syracuseStep 4522715 = 6784073) B6784073
theorem B1344311 : Blo 595291 1344311 := bstep (se 1 (by rfl) ⟨1008233, by rfl⟩ : syracuseStep 1344311 = 2016467) B2016467
theorem B2556809 : Blo 595291 2556809 := bstep (se 2 (by rfl) ⟨958803, by rfl⟩ : syracuseStep 2556809 = 1917607) B1917607
theorem B754591 : Blo 595291 754591 := bstep (se 1 (by rfl) ⟨565943, by rfl⟩ : syracuseStep 754591 = 1131887) B1131887
theorem B1705121 : Blo 595291 1705121 := bstep (se 2 (by rfl) ⟨639420, by rfl⟩ : syracuseStep 1705121 = 1278841) B1278841
theorem B755183 : Blo 595291 755183 := bstep (se 1 (by rfl) ⟨566387, by rfl⟩ : syracuseStep 755183 = 1132775) B1132775
theorem B6817607 : Blo 595291 6817607 := bstep (se 1 (by rfl) ⟨5113205, by rfl⟩ : syracuseStep 6817607 = 10226411) B10226411
theorem B3016763 : Blo 595291 3016763 := bstep (se 1 (by rfl) ⟨2262572, by rfl⟩ : syracuseStep 3016763 = 4525145) B4525145
theorem B1346039 : Blo 595291 1346039 := bstep (se 1 (by rfl) ⟨1009529, by rfl⟩ : syracuseStep 1346039 = 2019059) B2019059
theorem B8587939 : Blo 595291 8587939 := bstep (se 1 (by rfl) ⟨6440954, by rfl⟩ : syracuseStep 8587939 = 12881909) B12881909
theorem B1346273 : Blo 595291 1346273 := bstep (se 2 (by rfl) ⟨504852, by rfl⟩ : syracuseStep 1346273 = 1009705) B1009705
theorem B1510427 : Blo 595291 1510427 := bstep (se 1 (by rfl) ⟨1132820, by rfl⟩ : syracuseStep 1510427 = 2265641) B2265641
theorem B3018707 : Blo 595291 3018707 := bstep (se 1 (by rfl) ⟨2264030, by rfl⟩ : syracuseStep 3018707 = 4528061) B4528061
theorem B1511399 : Blo 595291 1511399 := bstep (se 1 (by rfl) ⟨1133549, by rfl⟩ : syracuseStep 1511399 = 2267099) B2267099
theorem B36835505 : Blo 595291 36835505 := bstep (se 2 (by rfl) ⟨13813314, by rfl⟩ : syracuseStep 36835505 = 27626629) B27626629
theorem B32608889 : Blo 595291 32608889 := bstep (se 2 (by rfl) ⟨12228333, by rfl⟩ : syracuseStep 32608889 = 24456667) B24456667
theorem B1970983 : Blo 595291 1970983 := bstep (se 1 (by rfl) ⟨1478237, by rfl⟩ : syracuseStep 1970983 = 2956475) B2956475
theorem B10195793 : Blo 595291 10195793 := bstep (se 2 (by rfl) ⟨3823422, by rfl⟩ : syracuseStep 10195793 = 7646845) B7646845
theorem B1512391 : Blo 595291 1512391 := bstep (se 1 (by rfl) ⟨1134293, by rfl⟩ : syracuseStep 1512391 = 2268587) B2268587
theorem B3839005 : Blo 595291 3839005 := bstep (se 3 (by rfl) ⟨719813, by rfl⟩ : syracuseStep 3839005 = 1439627) B1439627
theorem B3642889 : Blo 595291 3642889 := bstep (se 2 (by rfl) ⟨1366083, by rfl⟩ : syracuseStep 3642889 = 2732167) B2732167
theorem B596135 : Blo 595291 596135 := bstep (se 1 (by rfl) ⟨447101, by rfl⟩ : syracuseStep 596135 = 894203) B894203
theorem B596251 : Blo 595291 596251 := bstep (se 1 (by rfl) ⟨447188, by rfl⟩ : syracuseStep 596251 = 894377) B894377
theorem B596447 : Blo 595291 596447 := bstep (se 1 (by rfl) ⟨447335, by rfl⟩ : syracuseStep 596447 = 894671) B894671
theorem B596479 : Blo 595291 596479 := bstep (se 1 (by rfl) ⟨447359, by rfl⟩ : syracuseStep 596479 = 894719) B894719
theorem B1513991 : Blo 595291 1513991 := bstep (se 1 (by rfl) ⟨1135493, by rfl⟩ : syracuseStep 1513991 = 2270987) B2270987
theorem B597147 : Blo 595291 597147 := bstep (se 1 (by rfl) ⟨447860, by rfl⟩ : syracuseStep 597147 = 895721) B895721
theorem B597183 : Blo 595291 597183 := bstep (se 1 (by rfl) ⟨447887, by rfl⟩ : syracuseStep 597183 = 895775) B895775
theorem B597503 : Blo 595291 597503 := bstep (se 1 (by rfl) ⟨448127, by rfl⟩ : syracuseStep 597503 = 896255) B896255
theorem B5119631 : Blo 595291 5119631 := bstep (se 1 (by rfl) ⟨3839723, by rfl⟩ : syracuseStep 5119631 = 7679447) B7679447
theorem B597743 : Blo 595291 597743 := bstep (se 1 (by rfl) ⟨448307, by rfl⟩ : syracuseStep 597743 = 896615) B896615
theorem B597851 : Blo 595291 597851 := bstep (se 1 (by rfl) ⟨448388, by rfl⟩ : syracuseStep 597851 = 896777) B896777
theorem B597999 : Blo 595291 597999 := bstep (se 1 (by rfl) ⟨448499, by rfl⟩ : syracuseStep 597999 = 896999) B896999
theorem B598047 : Blo 595291 598047 := bstep (se 1 (by rfl) ⟨448535, by rfl⟩ : syracuseStep 598047 = 897071) B897071
theorem B20652083 : Blo 595291 20652083 := bstep (se 1 (by rfl) ⟨15489062, by rfl⟩ : syracuseStep 20652083 = 30978125) B30978125
theorem B1024283 : Blo 595291 1024283 := bstep (se 1 (by rfl) ⟨768212, by rfl⟩ : syracuseStep 1024283 = 1536425) B1536425
theorem B7283155 : Blo 595291 7283155 := bstep (se 1 (by rfl) ⟨5462366, by rfl⟩ : syracuseStep 7283155 = 10924733) B10924733
theorem B893723 : Blo 595291 893723 := bstep (se 1 (by rfl) ⟨670292, by rfl⟩ : syracuseStep 893723 = 1340585) B1340585
theorem B894089 : Blo 595291 894089 := bstep (se 2 (by rfl) ⟨335283, by rfl⟩ : syracuseStep 894089 = 670567) B670567
theorem B894191 : Blo 595291 894191 := bstep (se 1 (by rfl) ⟨670643, by rfl⟩ : syracuseStep 894191 = 1341287) B1341287
theorem B2073853 : Blo 595291 2073853 := bstep (se 3 (by rfl) ⟨388847, by rfl⟩ : syracuseStep 2073853 = 777695) B777695
theorem B894527 : Blo 595291 894527 := bstep (se 1 (by rfl) ⟨670895, by rfl⟩ : syracuseStep 894527 = 1341791) B1341791
theorem B894953 : Blo 595291 894953 := bstep (se 2 (by rfl) ⟨335607, by rfl⟩ : syracuseStep 894953 = 671215) B671215
theorem B894971 : Blo 595291 894971 := bstep (se 1 (by rfl) ⟨671228, by rfl⟩ : syracuseStep 894971 = 1342457) B1342457
theorem B895007 : Blo 595291 895007 := bstep (se 1 (by rfl) ⟨671255, by rfl⟩ : syracuseStep 895007 = 1342511) B1342511
theorem B895151 : Blo 595291 895151 := bstep (se 1 (by rfl) ⟨671363, by rfl⟩ : syracuseStep 895151 = 1342727) B1342727
theorem B2009447 : Blo 595291 2009447 := bstep (se 1 (by rfl) ⟨1507085, by rfl⟩ : syracuseStep 2009447 = 3014171) B3014171
theorem B36809363 : Blo 595291 36809363 := bstep (se 1 (by rfl) ⟨27607022, by rfl⟩ : syracuseStep 36809363 = 55214045) B55214045
theorem B134720293 : Blo 595291 134720293 := bstep (se 4 (by rfl) ⟨12630027, by rfl⟩ : syracuseStep 134720293 = 25260055) B25260055
theorem B896927 : Blo 595291 896927 := bstep (se 1 (by rfl) ⟨672695, by rfl⟩ : syracuseStep 896927 = 1345391) B1345391
theorem B4304927 : Blo 595291 4304927 := bstep (se 1 (by rfl) ⟨3228695, by rfl⟩ : syracuseStep 4304927 = 6457391) B6457391
theorem B2863187 : Blo 595291 2863187 := bstep (se 1 (by rfl) ⟨2147390, by rfl⟩ : syracuseStep 2863187 = 4294781) B4294781
theorem B897119 : Blo 595291 897119 := bstep (se 1 (by rfl) ⟨672839, by rfl⟩ : syracuseStep 897119 = 1345679) B1345679
theorem B897161 : Blo 595291 897161 := bstep (se 2 (by rfl) ⟨336435, by rfl⟩ : syracuseStep 897161 = 672871) B672871
theorem B897191 : Blo 595291 897191 := bstep (se 1 (by rfl) ⟨672893, by rfl⟩ : syracuseStep 897191 = 1345787) B1345787
theorem B897263 : Blo 595291 897263 := bstep (se 1 (by rfl) ⟨672947, by rfl⟩ : syracuseStep 897263 = 1345895) B1345895
theorem B2011823 : Blo 595291 2011823 := bstep (se 1 (by rfl) ⟨1508867, by rfl⟩ : syracuseStep 2011823 = 3017735) B3017735
theorem B898025 : Blo 595291 898025 := bstep (se 2 (by rfl) ⟨336759, by rfl⟩ : syracuseStep 898025 = 673519) B673519
theorem B3879935 : Blo 595291 3879935 := bstep (se 1 (by rfl) ⟨2909951, by rfl⟩ : syracuseStep 3879935 = 5819903) B5819903
theorem B35337239 : Blo 595291 35337239 := bstep (se 1 (by rfl) ⟨26502929, by rfl⟩ : syracuseStep 35337239 = 53005859) B53005859
theorem B3814607 : Blo 595291 3814607 := bstep (se 1 (by rfl) ⟨2860955, by rfl⟩ : syracuseStep 3814607 = 5721911) B5721911
theorem B898511 : Blo 595291 898511 := bstep (se 1 (by rfl) ⟨673883, by rfl⟩ : syracuseStep 898511 = 1347767) B1347767
theorem B898559 : Blo 595291 898559 := bstep (se 1 (by rfl) ⟨673919, by rfl⟩ : syracuseStep 898559 = 1347839) B1347839
theorem B3815531 : Blo 595291 3815531 := bstep (se 1 (by rfl) ⟨2861648, by rfl⟩ : syracuseStep 3815531 = 5723297) B5723297
theorem B10337129 : Blo 595291 10337129 := bstep (se 2 (by rfl) ⟨3876423, by rfl⟩ : syracuseStep 10337129 = 7752847) B7752847
theorem B8633729 : Blo 595291 8633729 := bstep (se 2 (by rfl) ⟨3237648, by rfl⟩ : syracuseStep 8633729 = 6475297) B6475297
theorem B638399 : Blo 595291 638399 := bstep (se 1 (by rfl) ⟨478799, by rfl⟩ : syracuseStep 638399 = 957599) B957599
theorem B2015279 : Blo 595291 2015279 := bstep (se 1 (by rfl) ⟨1511459, by rfl⟩ : syracuseStep 2015279 = 3022919) B3022919
theorem B3884219 : Blo 595291 3884219 := bstep (se 1 (by rfl) ⟨2913164, by rfl⟩ : syracuseStep 3884219 = 5826329) B5826329
theorem B1131803 : Blo 595291 1131803 := bstep (se 1 (by rfl) ⟨848852, by rfl⟩ : syracuseStep 1131803 = 1697705) B1697705
theorem B4146461 : Blo 595291 4146461 := bstep (se 3 (by rfl) ⟨777461, by rfl⟩ : syracuseStep 4146461 = 1554923) B1554923
theorem B2147795 : Blo 595291 2147795 := bstep (se 1 (by rfl) ⟨1610846, by rfl⟩ : syracuseStep 2147795 = 3221693) B3221693
theorem B4670945 : Blo 595291 4670945 := bstep (se 2 (by rfl) ⟨1751604, by rfl⟩ : syracuseStep 4670945 = 3503209) B3503209
theorem B6473479 : Blo 595291 6473479 := bstep (se 1 (by rfl) ⟨4855109, by rfl⟩ : syracuseStep 6473479 = 9710219) B9710219
theorem B8636381 : Blo 595291 8636381 := bstep (se 3 (by rfl) ⟨1619321, by rfl⟩ : syracuseStep 8636381 = 3238643) B3238643
theorem B2017277 : Blo 595291 2017277 := bstep (se 3 (by rfl) ⟨378239, by rfl⟩ : syracuseStep 2017277 = 756479) B756479
theorem B6473999 : Blo 595291 6473999 := bstep (se 1 (by rfl) ⟨4855499, by rfl⟩ : syracuseStep 6473999 = 9710999) B9710999
theorem B3394385 : Blo 595291 3394385 := bstep (se 2 (by rfl) ⟨1272894, by rfl⟩ : syracuseStep 3394385 = 2545789) B2545789
theorem B6900653 : Blo 595291 6900653 := bstep (se 3 (by rfl) ⟨1293872, by rfl⟩ : syracuseStep 6900653 = 2587745) B2587745
theorem B1134415 : Blo 595291 1134415 := bstep (se 1 (by rfl) ⟨850811, by rfl⟩ : syracuseStep 1134415 = 1701623) B1701623
theorem B10342255 : Blo 595291 10342255 := bstep (se 1 (by rfl) ⟨7756691, by rfl⟩ : syracuseStep 10342255 = 15513383) B15513383
theorem B1135775 : Blo 595291 1135775 := bstep (se 1 (by rfl) ⟨851831, by rfl⟩ : syracuseStep 1135775 = 1703663) B1703663
theorem B1004879 : Blo 595291 1004879 := bstep (se 1 (by rfl) ⟨753659, by rfl⟩ : syracuseStep 1004879 = 1507319) B1507319
theorem B2021111 : Blo 595291 2021111 := bstep (se 1 (by rfl) ⟨1515833, by rfl⟩ : syracuseStep 2021111 = 3031667) B3031667
theorem B5101451 : Blo 595291 5101451 := bstep (se 1 (by rfl) ⟨3826088, by rfl⟩ : syracuseStep 5101451 = 7652177) B7652177
theorem B1432055 : Blo 595291 1432055 := bstep (se 1 (by rfl) ⟨1074041, by rfl⟩ : syracuseStep 1432055 = 2148083) B2148083
theorem B3693161 : Blo 595291 3693161 := bstep (se 2 (by rfl) ⟨1384935, by rfl⟩ : syracuseStep 3693161 = 2769871) B2769871
theorem B1137719 : Blo 595291 1137719 := bstep (se 1 (by rfl) ⟨853289, by rfl⟩ : syracuseStep 1137719 = 1706579) B1706579
theorem B15326495 : Blo 595291 15326495 := bstep (se 1 (by rfl) ⟨11494871, by rfl⟩ : syracuseStep 15326495 = 22989743) B22989743
theorem B6970835 : Blo 595291 6970835 := bstep (se 1 (by rfl) ⟨5228126, by rfl⟩ : syracuseStep 6970835 = 10456253) B10456253
theorem B13459655 : Blo 595291 13459655 := bstep (se 1 (by rfl) ⟨10094741, by rfl⟩ : syracuseStep 13459655 = 20189483) B20189483
theorem B8610083 : Blo 595291 8610083 := bstep (se 1 (by rfl) ⟨6457562, by rfl⟩ : syracuseStep 8610083 = 12915125) B12915125
theorem B6873407 : Blo 595291 6873407 := bstep (se 1 (by rfl) ⟨5155055, by rfl⟩ : syracuseStep 6873407 = 10310111) B10310111
theorem B1696247 : Blo 595291 1696247 := bstep (se 1 (by rfl) ⟨1272185, by rfl⟩ : syracuseStep 1696247 = 2544371) B2544371
theorem B1074359 : Blo 595291 1074359 := bstep (se 1 (by rfl) ⟨805769, by rfl⟩ : syracuseStep 1074359 = 1611539) B1611539
theorem B12904667 : Blo 595291 12904667 := bstep (se 1 (by rfl) ⟨9678500, by rfl⟩ : syracuseStep 12904667 = 19357001) B19357001
theorem B1698047 : Blo 595291 1698047 := bstep (se 1 (by rfl) ⟨1273535, by rfl⟩ : syracuseStep 1698047 = 2547071) B2547071
theorem B3402107 : Blo 595291 3402107 := bstep (se 1 (by rfl) ⟨2551580, by rfl⟩ : syracuseStep 3402107 = 5103161) B5103161
theorem B8612851 : Blo 595291 8612851 := bstep (se 1 (by rfl) ⟨6459638, by rfl⟩ : syracuseStep 8612851 = 12919277) B12919277
theorem B1076255 : Blo 595291 1076255 := bstep (se 1 (by rfl) ⟨807191, by rfl⟩ : syracuseStep 1076255 = 1614383) B1614383
theorem B1011001 : Blo 595291 1011001 := bstep (se 2 (by rfl) ⟨379125, by rfl⟩ : syracuseStep 1011001 = 758251) B758251
theorem B1011035 : Blo 595291 1011035 := bstep (se 1 (by rfl) ⟨758276, by rfl⟩ : syracuseStep 1011035 = 1516553) B1516553
theorem B1340639 : Blo 595291 1340639 := bstep (se 1 (by rfl) ⟨1005479, by rfl⟩ : syracuseStep 1340639 = 2010959) B2010959
theorem B1340927 : Blo 595291 1340927 := bstep (se 1 (by rfl) ⟨1005695, by rfl⟩ : syracuseStep 1340927 = 2011391) B2011391
theorem B5109925 : Blo 595291 5109925 := bstep (se 4 (by rfl) ⟨479055, by rfl⟩ : syracuseStep 5109925 = 958111) B958111
theorem B12254023 : Blo 595291 12254023 := bstep (se 1 (by rfl) ⟨9190517, by rfl⟩ : syracuseStep 12254023 = 18381035) B18381035
theorem B1342331 : Blo 595291 1342331 := bstep (se 1 (by rfl) ⟨1006748, by rfl⟩ : syracuseStep 1342331 = 2013497) B2013497
theorem B3013847 : Blo 595291 3013847 := bstep (se 1 (by rfl) ⟨2260385, by rfl⟩ : syracuseStep 3013847 = 4520771) B4520771
theorem B2456851 : Blo 595291 2456851 := bstep (se 1 (by rfl) ⟨1842638, by rfl⟩ : syracuseStep 2456851 = 3685277) B3685277
theorem B3440033 : Blo 595291 3440033 := bstep (se 2 (by rfl) ⟨1290012, by rfl⟩ : syracuseStep 3440033 = 2580025) B2580025
theorem B39353971 : Blo 595291 39353971 := bstep (se 1 (by rfl) ⟨29515478, by rfl⟩ : syracuseStep 39353971 = 59030957) B59030957
theorem B1343159 : Blo 595291 1343159 := bstep (se 1 (by rfl) ⟨1007369, by rfl⟩ : syracuseStep 1343159 = 2014739) B2014739
theorem B1343195 : Blo 595291 1343195 := bstep (se 1 (by rfl) ⟨1007396, by rfl⟩ : syracuseStep 1343195 = 2014793) B2014793
theorem B1343483 : Blo 595291 1343483 := bstep (se 1 (by rfl) ⟨1007612, by rfl⟩ : syracuseStep 1343483 = 2015225) B2015225
theorem B1343519 : Blo 595291 1343519 := bstep (se 1 (by rfl) ⟨1007639, by rfl⟩ : syracuseStep 1343519 = 2015279) B2015279
theorem B1507511 : Blo 595291 1507511 := bstep (se 1 (by rfl) ⟨1130633, by rfl⟩ : syracuseStep 1507511 = 2261267) B2261267
theorem B3015143 : Blo 595291 3015143 := bstep (se 1 (by rfl) ⟨2261357, by rfl⟩ : syracuseStep 3015143 = 4522715) B4522715
theorem B1704539 : Blo 595291 1704539 := bstep (se 1 (by rfl) ⟨1278404, by rfl⟩ : syracuseStep 1704539 = 2556809) B2556809
theorem B2589479 : Blo 595291 2589479 := bstep (se 1 (by rfl) ⟨1942109, by rfl⟩ : syracuseStep 2589479 = 3884219) B3884219
theorem B754535 : Blo 595291 754535 := bstep (se 1 (by rfl) ⟨565901, by rfl⟩ : syracuseStep 754535 = 1131803) B1131803
theorem B3113963 : Blo 595291 3113963 := bstep (se 1 (by rfl) ⟨2335472, by rfl⟩ : syracuseStep 3113963 = 4670945) B4670945
theorem B1344851 : Blo 595291 1344851 := bstep (se 1 (by rfl) ⟨1008638, by rfl⟩ : syracuseStep 1344851 = 2017277) B2017277
theorem B2262923 : Blo 595291 2262923 := bstep (se 1 (by rfl) ⟨1697192, by rfl⟩ : syracuseStep 2262923 = 3394385) B3394385
theorem B757183 : Blo 595291 757183 := bstep (se 1 (by rfl) ⟨567887, by rfl⟩ : syracuseStep 757183 = 1135775) B1135775
theorem B1347407 : Blo 595291 1347407 := bstep (se 1 (by rfl) ⟨1010555, by rfl⟩ : syracuseStep 1347407 = 2021111) B2021111
theorem B954703 : Blo 595291 954703 := bstep (se 1 (by rfl) ⟨716027, by rfl⟩ : syracuseStep 954703 = 1432055) B1432055
theorem B2462107 : Blo 595291 2462107 := bstep (se 1 (by rfl) ⟨1846580, by rfl⟩ : syracuseStep 2462107 = 3693161) B3693161
theorem B1348001 : Blo 595291 1348001 := bstep (se 2 (by rfl) ⟨505500, by rfl⟩ : syracuseStep 1348001 = 1011001) B1011001
theorem B758479 : Blo 595291 758479 := bstep (se 1 (by rfl) ⟨568859, by rfl⟩ : syracuseStep 758479 = 1137719) B1137719
theorem B3413087 : Blo 595291 3413087 := bstep (se 1 (by rfl) ⟨2559815, by rfl⟩ : syracuseStep 3413087 = 5119631) B5119631
theorem B1512553 : Blo 595291 1512553 := bstep (se 2 (by rfl) ⟨567207, by rfl⟩ : syracuseStep 1512553 = 1134415) B1134415
theorem B13768055 : Blo 595291 13768055 := bstep (se 1 (by rfl) ⟨10326041, by rfl⟩ : syracuseStep 13768055 = 20652083) B20652083
theorem B5740055 : Blo 595291 5740055 := bstep (se 1 (by rfl) ⟨4305041, by rfl⟩ : syracuseStep 5740055 = 8610083) B8610083
theorem B595815 : Blo 595291 595815 := bstep (se 1 (by rfl) ⟨446861, by rfl⟩ : syracuseStep 595815 = 893723) B893723
theorem B596059 : Blo 595291 596059 := bstep (se 1 (by rfl) ⟨447044, by rfl⟩ : syracuseStep 596059 = 894089) B894089
theorem B596127 : Blo 595291 596127 := bstep (se 1 (by rfl) ⟨447095, by rfl⟩ : syracuseStep 596127 = 894191) B894191
theorem B596351 : Blo 595291 596351 := bstep (se 1 (by rfl) ⟨447263, by rfl⟩ : syracuseStep 596351 = 894527) B894527
theorem B2627977 : Blo 595291 2627977 := bstep (se 2 (by rfl) ⟨985491, by rfl⟩ : syracuseStep 2627977 = 1970983) B1970983
theorem B596635 : Blo 595291 596635 := bstep (se 1 (by rfl) ⟨447476, by rfl⟩ : syracuseStep 596635 = 894953) B894953
theorem B596647 : Blo 595291 596647 := bstep (se 1 (by rfl) ⟨447485, by rfl⟩ : syracuseStep 596647 = 894971) B894971
theorem B596671 : Blo 595291 596671 := bstep (se 1 (by rfl) ⟨447503, by rfl⟩ : syracuseStep 596671 = 895007) B895007
theorem B5118673 : Blo 595291 5118673 := bstep (se 2 (by rfl) ⟨1919502, by rfl⟩ : syracuseStep 5118673 = 3839005) B3839005
theorem B596767 : Blo 595291 596767 := bstep (se 1 (by rfl) ⟨447575, by rfl⟩ : syracuseStep 596767 = 895151) B895151
theorem B2268071 : Blo 595291 2268071 := bstep (se 1 (by rfl) ⟨1701053, by rfl⟩ : syracuseStep 2268071 = 3402107) B3402107
theorem B4857185 : Blo 595291 4857185 := bstep (se 2 (by rfl) ⟨1821444, by rfl⟩ : syracuseStep 4857185 = 3642889) B3642889
theorem B597951 : Blo 595291 597951 := bstep (se 1 (by rfl) ⟨448463, by rfl⟩ : syracuseStep 597951 = 896927) B896927
theorem B1908791 : Blo 595291 1908791 := bstep (se 1 (by rfl) ⟨1431593, by rfl⟩ : syracuseStep 1908791 = 2863187) B2863187
theorem B598079 : Blo 595291 598079 := bstep (se 1 (by rfl) ⟨448559, by rfl⟩ : syracuseStep 598079 = 897119) B897119
theorem B598107 : Blo 595291 598107 := bstep (se 1 (by rfl) ⟨448580, by rfl⟩ : syracuseStep 598107 = 897161) B897161
theorem B598127 : Blo 595291 598127 := bstep (se 1 (by rfl) ⟨448595, by rfl⟩ : syracuseStep 598127 = 897191) B897191
theorem B598175 : Blo 595291 598175 := bstep (se 1 (by rfl) ⟨448631, by rfl⟩ : syracuseStep 598175 = 897263) B897263
theorem B598683 : Blo 595291 598683 := bstep (se 1 (by rfl) ⟨449012, by rfl⟩ : syracuseStep 598683 = 898025) B898025
theorem B893759 : Blo 595291 893759 := bstep (se 1 (by rfl) ⟨670319, by rfl⟩ : syracuseStep 893759 = 1340639) B1340639
theorem B599007 : Blo 595291 599007 := bstep (se 1 (by rfl) ⟨449255, by rfl⟩ : syracuseStep 599007 = 898511) B898511
theorem B893951 : Blo 595291 893951 := bstep (se 1 (by rfl) ⟨670463, by rfl⟩ : syracuseStep 893951 = 1340927) B1340927
theorem B599039 : Blo 595291 599039 := bstep (se 1 (by rfl) ⟨449279, by rfl⟩ : syracuseStep 599039 = 898559) B898559
theorem B6891419 : Blo 595291 6891419 := bstep (se 1 (by rfl) ⟨5168564, by rfl⟩ : syracuseStep 6891419 = 10337129) B10337129
theorem B894887 : Blo 595291 894887 := bstep (se 1 (by rfl) ⟨671165, by rfl⟩ : syracuseStep 894887 = 1342331) B1342331
theorem B2009231 : Blo 595291 2009231 := bstep (se 1 (by rfl) ⟨1506923, by rfl⟩ : syracuseStep 2009231 = 3013847) B3013847
theorem B52471961 : Blo 595291 52471961 := bstep (se 2 (by rfl) ⟨19676985, by rfl⟩ : syracuseStep 52471961 = 39353971) B39353971
theorem B895439 : Blo 595291 895439 := bstep (se 1 (by rfl) ⟨671579, by rfl⟩ : syracuseStep 895439 = 1343159) B1343159
theorem B895463 : Blo 595291 895463 := bstep (se 1 (by rfl) ⟨671597, by rfl⟩ : syracuseStep 895463 = 1343195) B1343195
theorem B895655 : Blo 595291 895655 := bstep (se 1 (by rfl) ⟨671741, by rfl⟩ : syracuseStep 895655 = 1343483) B1343483
theorem B11479805 : Blo 595291 11479805 := bstep (se 3 (by rfl) ⟨2152463, by rfl⟩ : syracuseStep 11479805 = 4304927) B4304927
theorem B2272157 : Blo 595291 2272157 := bstep (se 3 (by rfl) ⟨426029, by rfl⟩ : syracuseStep 2272157 = 852059) B852059
theorem B35892413 : Blo 595291 35892413 := bstep (se 3 (by rfl) ⟨6729827, by rfl⟩ : syracuseStep 35892413 = 13459655) B13459655
theorem B896207 : Blo 595291 896207 := bstep (se 1 (by rfl) ⟨672155, by rfl⟩ : syracuseStep 896207 = 1344311) B1344311
theorem B9710873 : Blo 595291 9710873 := bstep (se 2 (by rfl) ⟨3641577, by rfl⟩ : syracuseStep 9710873 = 7283155) B7283155
theorem B2731421 : Blo 595291 2731421 := bstep (se 3 (by rfl) ⟨512141, by rfl⟩ : syracuseStep 2731421 = 1024283) B1024283
theorem B2764307 : Blo 595291 2764307 := bstep (se 1 (by rfl) ⟨2073230, by rfl⟩ : syracuseStep 2764307 = 4146461) B4146461
theorem B2011175 : Blo 595291 2011175 := bstep (se 1 (by rfl) ⟨1508381, by rfl⟩ : syracuseStep 2011175 = 3016763) B3016763
theorem B897359 : Blo 595291 897359 := bstep (se 1 (by rfl) ⟨673019, by rfl⟩ : syracuseStep 897359 = 1346039) B1346039
theorem B2765137 : Blo 595291 2765137 := bstep (se 2 (by rfl) ⟨1036926, by rfl⟩ : syracuseStep 2765137 = 2073853) B2073853
theorem B897515 : Blo 595291 897515 := bstep (se 1 (by rfl) ⟨673136, by rfl⟩ : syracuseStep 897515 = 1346273) B1346273
theorem B4600435 : Blo 595291 4600435 := bstep (se 1 (by rfl) ⟨3450326, by rfl⟩ : syracuseStep 4600435 = 6900653) B6900653
theorem B8631305 : Blo 595291 8631305 := bstep (se 2 (by rfl) ⟨3236739, by rfl⟩ : syracuseStep 8631305 = 6473479) B6473479
theorem B2012471 : Blo 595291 2012471 := bstep (se 1 (by rfl) ⟨1509353, by rfl⟩ : syracuseStep 2012471 = 3018707) B3018707
theorem B24557003 : Blo 595291 24557003 := bstep (se 1 (by rfl) ⟨18417752, by rfl⟩ : syracuseStep 24557003 = 36835505) B36835505
theorem B21739259 : Blo 595291 21739259 := bstep (se 1 (by rfl) ⟨16304444, by rfl⟩ : syracuseStep 21739259 = 32608889) B32608889
theorem B6797195 : Blo 595291 6797195 := bstep (se 1 (by rfl) ⟨5097896, by rfl⟩ : syracuseStep 6797195 = 10195793) B10195793
theorem B11450585 : Blo 595291 11450585 := bstep (se 2 (by rfl) ⟨4293969, by rfl⟩ : syracuseStep 11450585 = 8587939) B8587939
theorem B669919 : Blo 595291 669919 := bstep (se 1 (by rfl) ⟨502439, by rfl⟩ : syracuseStep 669919 = 1004879) B1004879
theorem B2013821 : Blo 595291 2013821 := bstep (se 3 (by rfl) ⟨377591, by rfl⟩ : syracuseStep 2013821 = 755183) B755183
theorem B11483801 : Blo 595291 11483801 := bstep (se 2 (by rfl) ⟨4306425, by rfl⟩ : syracuseStep 11483801 = 8612851) B8612851
theorem B65354789 : Blo 595291 65354789 := bstep (se 4 (by rfl) ⟨6127011, by rfl⟩ : syracuseStep 65354789 = 12254023) B12254023
theorem B1130831 : Blo 595291 1130831 := bstep (se 1 (by rfl) ⟨848123, by rfl⟩ : syracuseStep 1130831 = 1696247) B1696247
theorem B2016521 : Blo 595291 2016521 := bstep (se 2 (by rfl) ⟨756195, by rfl⟩ : syracuseStep 2016521 = 1512391) B1512391
theorem B8603111 : Blo 595291 8603111 := bstep (se 1 (by rfl) ⟨6452333, by rfl⟩ : syracuseStep 8603111 = 12904667) B12904667
theorem B1132031 : Blo 595291 1132031 := bstep (se 1 (by rfl) ⟨849023, by rfl⟩ : syracuseStep 1132031 = 1698047) B1698047
theorem B98158301 : Blo 595291 98158301 := bstep (se 3 (by rfl) ⟨18404681, by rfl⟩ : syracuseStep 98158301 = 36809363) B36809363
theorem B674023 : Blo 595291 674023 := bstep (se 1 (by rfl) ⟨505517, by rfl⟩ : syracuseStep 674023 = 1011035) B1011035
theorem B2543071 : Blo 595291 2543071 := bstep (se 1 (by rfl) ⟨1907303, by rfl⟩ : syracuseStep 2543071 = 3814607) B3814607
theorem B2543687 : Blo 595291 2543687 := bstep (se 1 (by rfl) ⟨1907765, by rfl⟩ : syracuseStep 2543687 = 3815531) B3815531
theorem B5755819 : Blo 595291 5755819 := bstep (se 1 (by rfl) ⟨4316864, by rfl⟩ : syracuseStep 5755819 = 8633729) B8633729
theorem B1136747 : Blo 595291 1136747 := bstep (se 1 (by rfl) ⟨852560, by rfl⟩ : syracuseStep 1136747 = 1705121) B1705121
theorem B1005689 : Blo 595291 1005689 := bstep (se 2 (by rfl) ⟨377133, by rfl⟩ : syracuseStep 1005689 = 754267) B754267
theorem B1431863 : Blo 595291 1431863 := bstep (se 1 (by rfl) ⟨1073897, by rfl⟩ : syracuseStep 1431863 = 2147795) B2147795
theorem B1006121 : Blo 595291 1006121 := bstep (se 2 (by rfl) ⟨377295, by rfl⟩ : syracuseStep 1006121 = 754591) B754591
theorem B4545071 : Blo 595291 4545071 := bstep (se 1 (by rfl) ⟨3408803, by rfl⟩ : syracuseStep 4545071 = 6817607) B6817607
theorem B5757587 : Blo 595291 5757587 := bstep (se 1 (by rfl) ⟨4318190, by rfl⟩ : syracuseStep 5757587 = 8636381) B8636381
theorem B4315999 : Blo 595291 4315999 := bstep (se 1 (by rfl) ⟨3236999, by rfl⟩ : syracuseStep 4315999 = 6473999) B6473999
theorem B1006951 : Blo 595291 1006951 := bstep (se 1 (by rfl) ⟨755213, by rfl⟩ : syracuseStep 1006951 = 1510427) B1510427
theorem B1007599 : Blo 595291 1007599 := bstep (se 1 (by rfl) ⟨755699, by rfl⟩ : syracuseStep 1007599 = 1511399) B1511399
theorem B179627057 : Blo 595291 179627057 := bstep (se 2 (by rfl) ⟨67360146, by rfl⟩ : syracuseStep 179627057 = 134720293) B134720293
theorem B3400967 : Blo 595291 3400967 := bstep (se 1 (by rfl) ⟨2550725, by rfl⟩ : syracuseStep 3400967 = 5101451) B5101451
theorem B1009327 : Blo 595291 1009327 := bstep (se 1 (by rfl) ⟨756995, by rfl⟩ : syracuseStep 1009327 = 1513991) B1513991
theorem B10217663 : Blo 595291 10217663 := bstep (se 1 (by rfl) ⟨7663247, by rfl⟩ : syracuseStep 10217663 = 15326495) B15326495
theorem B4647223 : Blo 595291 4647223 := bstep (se 1 (by rfl) ⟨3485417, by rfl⟩ : syracuseStep 4647223 = 6970835) B6970835
theorem B13789673 : Blo 595291 13789673 := bstep (se 2 (by rfl) ⟨5171127, by rfl⟩ : syracuseStep 13789673 = 10342255) B10342255
theorem B4582271 : Blo 595291 4582271 := bstep (se 1 (by rfl) ⟨3436703, by rfl⟩ : syracuseStep 4582271 = 6873407) B6873407
theorem B716239 : Blo 595291 716239 := bstep (se 1 (by rfl) ⟨537179, by rfl⟩ : syracuseStep 716239 = 1074359) B1074359
theorem B1339631 : Blo 595291 1339631 := bstep (se 1 (by rfl) ⟨1004723, by rfl⟩ : syracuseStep 1339631 = 2009447) B2009447
theorem B717503 : Blo 595291 717503 := bstep (se 1 (by rfl) ⟨538127, by rfl⟩ : syracuseStep 717503 = 1076255) B1076255
theorem B6813233 : Blo 595291 6813233 := bstep (se 2 (by rfl) ⟨2554962, by rfl⟩ : syracuseStep 6813233 = 5109925) B5109925
theorem B1341215 : Blo 595291 1341215 := bstep (se 1 (by rfl) ⟨1005911, by rfl⟩ : syracuseStep 1341215 = 2011823) B2011823
theorem B2586623 : Blo 595291 2586623 := bstep (se 1 (by rfl) ⟨1939967, by rfl⟩ : syracuseStep 2586623 = 3879935) B3879935
theorem B23558159 : Blo 595291 23558159 := bstep (se 1 (by rfl) ⟨17668619, by rfl⟩ : syracuseStep 23558159 = 35337239) B35337239
theorem B1702397 : Blo 595291 1702397 := bstep (se 3 (by rfl) ⟨319199, by rfl⟩ : syracuseStep 1702397 = 638399) B638399
theorem B3275801 : Blo 595291 3275801 := bstep (se 2 (by rfl) ⟨1228425, by rfl⟩ : syracuseStep 3275801 = 2456851) B2456851
theorem B2293355 : Blo 595291 2293355 := bstep (se 1 (by rfl) ⟨1720016, by rfl⟩ : syracuseStep 2293355 = 3440033) B3440033
theorem B753887 : Blo 595291 753887 := bstep (se 1 (by rfl) ⟨565415, by rfl⟩ : syracuseStep 753887 = 1130831) B1130831
theorem B1344347 : Blo 595291 1344347 := bstep (se 1 (by rfl) ⟨1008260, by rfl⟩ : syracuseStep 1344347 = 2016521) B2016521
theorem B5735407 : Blo 595291 5735407 := bstep (se 1 (by rfl) ⟨4301555, by rfl⟩ : syracuseStep 5735407 = 8603111) B8603111
theorem B754687 : Blo 595291 754687 := bstep (se 1 (by rfl) ⟨566015, by rfl⟩ : syracuseStep 754687 = 1132031) B1132031
theorem B65438867 : Blo 595291 65438867 := bstep (se 1 (by rfl) ⟨49079150, by rfl⟩ : syracuseStep 65438867 = 98158301) B98158301
theorem B1508615 : Blo 595291 1508615 := bstep (se 1 (by rfl) ⟨1131461, by rfl⟩ : syracuseStep 1508615 = 2262923) B2262923
theorem B1345769 : Blo 595291 1345769 := bstep (se 2 (by rfl) ⟨504663, by rfl⟩ : syracuseStep 1345769 = 1009327) B1009327
theorem B9178703 : Blo 595291 9178703 := bstep (se 1 (by rfl) ⟨6884027, by rfl⟩ : syracuseStep 9178703 = 13768055) B13768055
theorem B757831 : Blo 595291 757831 := bstep (se 1 (by rfl) ⟨568373, by rfl⟩ : syracuseStep 757831 = 1136747) B1136747
theorem B954575 : Blo 595291 954575 := bstep (se 1 (by rfl) ⟨715931, by rfl⟩ : syracuseStep 954575 = 1431863) B1431863
theorem B3838391 : Blo 595291 3838391 := bstep (se 1 (by rfl) ⟨2878793, by rfl⟩ : syracuseStep 3838391 = 5757587) B5757587
theorem B954985 : Blo 595291 954985 := bstep (se 2 (by rfl) ⟨358119, by rfl⟩ : syracuseStep 954985 = 716239) B716239
theorem B1512047 : Blo 595291 1512047 := bstep (se 1 (by rfl) ⟨1134035, by rfl⟩ : syracuseStep 1512047 = 2268071) B2268071
theorem B62821757 : Blo 595291 62821757 := bstep (se 3 (by rfl) ⟨11779079, by rfl⟩ : syracuseStep 62821757 = 23558159) B23558159
theorem B3282809 : Blo 595291 3282809 := bstep (se 2 (by rfl) ⟨1231053, by rfl⟩ : syracuseStep 3282809 = 2462107) B2462107
theorem B595839 : Blo 595291 595839 := bstep (se 1 (by rfl) ⟨446879, by rfl⟩ : syracuseStep 595839 = 893759) B893759
theorem B595967 : Blo 595291 595967 := bstep (se 1 (by rfl) ⟨446975, by rfl⟩ : syracuseStep 595967 = 893951) B893951
theorem B6133913 : Blo 595291 6133913 := bstep (se 2 (by rfl) ⟨2300217, by rfl⟩ : syracuseStep 6133913 = 4600435) B4600435
theorem B2267311 : Blo 595291 2267311 := bstep (se 1 (by rfl) ⟨1700483, by rfl⟩ : syracuseStep 2267311 = 3400967) B3400967
theorem B7674425 : Blo 595291 7674425 := bstep (se 2 (by rfl) ⟨2877909, by rfl⟩ : syracuseStep 7674425 = 5755819) B5755819
theorem B4594279 : Blo 595291 4594279 := bstep (se 1 (by rfl) ⟨3445709, by rfl⟩ : syracuseStep 4594279 = 6891419) B6891419
theorem B596591 : Blo 595291 596591 := bstep (se 1 (by rfl) ⟨447443, by rfl⟩ : syracuseStep 596591 = 894887) B894887
theorem B596959 : Blo 595291 596959 := bstep (se 1 (by rfl) ⟨447719, by rfl⟩ : syracuseStep 596959 = 895439) B895439
theorem B596975 : Blo 595291 596975 := bstep (se 1 (by rfl) ⟨447731, by rfl⟩ : syracuseStep 596975 = 895463) B895463
theorem B597103 : Blo 595291 597103 := bstep (se 1 (by rfl) ⟨447827, by rfl⟩ : syracuseStep 597103 = 895655) B895655
theorem B3054847 : Blo 595291 3054847 := bstep (se 1 (by rfl) ⟨2291135, by rfl⟩ : syracuseStep 3054847 = 4582271) B4582271
theorem B1514771 : Blo 595291 1514771 := bstep (se 1 (by rfl) ⟨1136078, by rfl⟩ : syracuseStep 1514771 = 2272157) B2272157
theorem B23928275 : Blo 595291 23928275 := bstep (se 1 (by rfl) ⟨17946206, by rfl⟩ : syracuseStep 23928275 = 35892413) B35892413
theorem B597471 : Blo 595291 597471 := bstep (se 1 (by rfl) ⟨448103, by rfl⟩ : syracuseStep 597471 = 896207) B896207
theorem B1842871 : Blo 595291 1842871 := bstep (se 1 (by rfl) ⟨1382153, by rfl⟩ : syracuseStep 1842871 = 2764307) B2764307
theorem B893087 : Blo 595291 893087 := bstep (se 1 (by rfl) ⟨669815, by rfl⟩ : syracuseStep 893087 = 1339631) B1339631
theorem B598239 : Blo 595291 598239 := bstep (se 1 (by rfl) ⟨448679, by rfl⟩ : syracuseStep 598239 = 897359) B897359
theorem B893225 : Blo 595291 893225 := bstep (se 2 (by rfl) ⟨334959, by rfl⟩ : syracuseStep 893225 = 669919) B669919
theorem B598343 : Blo 595291 598343 := bstep (se 1 (by rfl) ⟨448757, by rfl⟩ : syracuseStep 598343 = 897515) B897515
theorem B12952493 : Blo 595291 12952493 := bstep (se 3 (by rfl) ⟨2428592, by rfl⟩ : syracuseStep 12952493 = 4857185) B4857185
theorem B6824897 : Blo 595291 6824897 := bstep (se 2 (by rfl) ⟨2559336, by rfl⟩ : syracuseStep 6824897 = 5118673) B5118673
theorem B7283789 : Blo 595291 7283789 := bstep (se 3 (by rfl) ⟨1365710, by rfl⟩ : syracuseStep 7283789 = 2731421) B2731421
theorem B14492839 : Blo 595291 14492839 := bstep (se 1 (by rfl) ⟨10869629, by rfl⟩ : syracuseStep 14492839 = 21739259) B21739259
theorem B894143 : Blo 595291 894143 := bstep (se 1 (by rfl) ⟨670607, by rfl⟩ : syracuseStep 894143 = 1341215) B1341215
theorem B4531463 : Blo 595291 4531463 := bstep (se 1 (by rfl) ⟨3398597, by rfl⟩ : syracuseStep 4531463 = 6797195) B6797195
theorem B895679 : Blo 595291 895679 := bstep (se 1 (by rfl) ⟨671759, by rfl⟩ : syracuseStep 895679 = 1343519) B1343519
theorem B2010095 : Blo 595291 2010095 := bstep (se 1 (by rfl) ⟨1507571, by rfl⟩ : syracuseStep 2010095 = 3015143) B3015143
theorem B2075975 : Blo 595291 2075975 := bstep (se 1 (by rfl) ⟨1556981, by rfl⟩ : syracuseStep 2075975 = 3113963) B3113963
theorem B896567 : Blo 595291 896567 := bstep (se 1 (by rfl) ⟨672425, by rfl⟩ : syracuseStep 896567 = 1344851) B1344851
theorem B24785189 : Blo 595291 24785189 := bstep (se 4 (by rfl) ⟨2323611, by rfl⟩ : syracuseStep 24785189 = 4647223) B4647223
theorem B1913341 : Blo 595291 1913341 := bstep (se 3 (by rfl) ⟨358751, by rfl⟩ : syracuseStep 1913341 = 717503) B717503
theorem B2012093 : Blo 595291 2012093 := bstep (se 3 (by rfl) ⟨377267, by rfl⟩ : syracuseStep 2012093 = 754535) B754535
theorem B898271 : Blo 595291 898271 := bstep (se 1 (by rfl) ⟨673703, by rfl⟩ : syracuseStep 898271 = 1347407) B1347407
theorem B898667 : Blo 595291 898667 := bstep (se 1 (by rfl) ⟨674000, by rfl⟩ : syracuseStep 898667 = 1348001) B1348001
theorem B898697 : Blo 595291 898697 := bstep (se 2 (by rfl) ⟨337011, by rfl⟩ : syracuseStep 898697 = 674023) B674023
theorem B2275391 : Blo 595291 2275391 := bstep (se 1 (by rfl) ⟨1706543, by rfl⟩ : syracuseStep 2275391 = 3413087) B3413087
theorem B670459 : Blo 595291 670459 := bstep (se 1 (by rfl) ⟨502844, by rfl⟩ : syracuseStep 670459 = 1005689) B1005689
theorem B670747 : Blo 595291 670747 := bstep (se 1 (by rfl) ⟨503060, by rfl⟩ : syracuseStep 670747 = 1006121) B1006121
theorem B3030047 : Blo 595291 3030047 := bstep (se 1 (by rfl) ⟨2272535, by rfl⟩ : syracuseStep 3030047 = 4545071) B4545071
theorem B3390761 : Blo 595291 3390761 := bstep (se 2 (by rfl) ⟨1271535, by rfl⟩ : syracuseStep 3390761 = 2543071) B2543071
theorem B3686849 : Blo 595291 3686849 := bstep (se 2 (by rfl) ⟨1382568, by rfl⟩ : syracuseStep 3686849 = 2765137) B2765137
theorem B119751371 : Blo 595291 119751371 := bstep (se 1 (by rfl) ⟨89813528, by rfl⟩ : syracuseStep 119751371 = 179627057) B179627057
theorem B4539725 : Blo 595291 4539725 := bstep (se 3 (by rfl) ⟨851198, by rfl⟩ : syracuseStep 4539725 = 1702397) B1702397
theorem B34981307 : Blo 595291 34981307 := bstep (se 1 (by rfl) ⟨26235980, by rfl⟩ : syracuseStep 34981307 = 52471961) B52471961
theorem B2016737 : Blo 595291 2016737 := bstep (se 2 (by rfl) ⟨756276, by rfl⟩ : syracuseStep 2016737 = 1512553) B1512553
theorem B9193115 : Blo 595291 9193115 := bstep (se 1 (by rfl) ⟨6894836, by rfl⟩ : syracuseStep 9193115 = 13789673) B13789673
theorem B7653203 : Blo 595291 7653203 := bstep (se 1 (by rfl) ⟨5739902, by rfl⟩ : syracuseStep 7653203 = 11479805) B11479805
theorem B6473915 : Blo 595291 6473915 := bstep (se 1 (by rfl) ⟨4855436, by rfl⟩ : syracuseStep 6473915 = 9710873) B9710873
theorem B5754203 : Blo 595291 5754203 := bstep (se 1 (by rfl) ⟨4315652, by rfl⟩ : syracuseStep 5754203 = 8631305) B8631305
theorem B16371335 : Blo 595291 16371335 := bstep (se 1 (by rfl) ⟨12278501, by rfl⟩ : syracuseStep 16371335 = 24557003) B24557003
theorem B4542155 : Blo 595291 4542155 := bstep (se 1 (by rfl) ⟨3406616, by rfl⟩ : syracuseStep 4542155 = 6813233) B6813233
theorem B5754665 : Blo 595291 5754665 := bstep (se 2 (by rfl) ⟨2157999, by rfl⟩ : syracuseStep 5754665 = 4315999) B4315999
theorem B7655867 : Blo 595291 7655867 := bstep (se 1 (by rfl) ⟨5741900, by rfl⟩ : syracuseStep 7655867 = 11483801) B11483801
theorem B2183867 : Blo 595291 2183867 := bstep (se 1 (by rfl) ⟨1637900, by rfl⟩ : syracuseStep 2183867 = 3275801) B3275801
theorem B43569859 : Blo 595291 43569859 := bstep (se 1 (by rfl) ⟨32677394, by rfl⟩ : syracuseStep 43569859 = 65354789) B65354789
theorem B1528903 : Blo 595291 1528903 := bstep (se 1 (by rfl) ⟨1146677, by rfl⟩ : syracuseStep 1528903 = 2293355) B2293355
theorem B1005007 : Blo 595291 1005007 := bstep (se 1 (by rfl) ⟨753755, by rfl⟩ : syracuseStep 1005007 = 1507511) B1507511
theorem B1136359 : Blo 595291 1136359 := bstep (se 1 (by rfl) ⟨852269, by rfl⟩ : syracuseStep 1136359 = 1704539) B1704539
theorem B1726319 : Blo 595291 1726319 := bstep (se 1 (by rfl) ⟨1294739, by rfl⟩ : syracuseStep 1726319 = 2589479) B2589479
theorem B1695791 : Blo 595291 1695791 := bstep (se 1 (by rfl) ⟨1271843, by rfl⟩ : syracuseStep 1695791 = 2543687) B2543687
theorem B3826703 : Blo 595291 3826703 := bstep (se 1 (by rfl) ⟨2870027, by rfl⟩ : syracuseStep 3826703 = 5740055) B5740055
theorem B1009577 : Blo 595291 1009577 := bstep (se 2 (by rfl) ⟨378591, by rfl⟩ : syracuseStep 1009577 = 757183) B757183
theorem B1272527 : Blo 595291 1272527 := bstep (se 1 (by rfl) ⟨954395, by rfl⟩ : syracuseStep 1272527 = 1908791) B1908791
theorem B1272937 : Blo 595291 1272937 := bstep (se 2 (by rfl) ⟨477351, by rfl⟩ : syracuseStep 1272937 = 954703) B954703
theorem B1011305 : Blo 595291 1011305 := bstep (se 2 (by rfl) ⟨379239, by rfl⟩ : syracuseStep 1011305 = 758479) B758479
theorem B1339487 : Blo 595291 1339487 := bstep (se 1 (by rfl) ⟨1004615, by rfl⟩ : syracuseStep 1339487 = 2009231) B2009231
theorem B6811775 : Blo 595291 6811775 := bstep (se 1 (by rfl) ⟨5108831, by rfl⟩ : syracuseStep 6811775 = 10217663) B10217663
theorem B1340783 : Blo 595291 1340783 := bstep (se 1 (by rfl) ⟨1005587, by rfl⟩ : syracuseStep 1340783 = 2011175) B2011175
theorem B3503969 : Blo 595291 3503969 := bstep (se 2 (by rfl) ⟨1313988, by rfl⟩ : syracuseStep 3503969 = 2627977) B2627977
theorem B1341647 : Blo 595291 1341647 := bstep (se 1 (by rfl) ⟨1006235, by rfl⟩ : syracuseStep 1341647 = 2012471) B2012471
theorem B7633723 : Blo 595291 7633723 := bstep (se 1 (by rfl) ⟨5725292, by rfl⟩ : syracuseStep 7633723 = 11450585) B11450585
theorem B1342547 : Blo 595291 1342547 := bstep (se 1 (by rfl) ⟨1006910, by rfl⟩ : syracuseStep 1342547 = 2013821) B2013821
theorem B1342601 : Blo 595291 1342601 := bstep (se 2 (by rfl) ⟨503475, by rfl⟩ : syracuseStep 1342601 = 1006951) B1006951
theorem B1343465 : Blo 595291 1343465 := bstep (se 2 (by rfl) ⟨503799, by rfl⟩ : syracuseStep 1343465 = 1007599) B1007599
theorem B27590645 : Blo 595291 27590645 := bstep (se 5 (by rfl) ⟨1293311, by rfl⟩ : syracuseStep 27590645 = 2586623) B2586623
theorem B2457899 : Blo 595291 2457899 := bstep (se 1 (by rfl) ⟨1843424, by rfl⟩ : syracuseStep 2457899 = 3686849) B3686849
theorem B1344491 : Blo 595291 1344491 := bstep (se 1 (by rfl) ⟨1008368, by rfl⟩ : syracuseStep 1344491 = 2016737) B2016737
theorem B3836135 : Blo 595291 3836135 := bstep (se 1 (by rfl) ⟨2877101, by rfl⟩ : syracuseStep 3836135 = 5754203) B5754203
theorem B3836443 : Blo 595291 3836443 := bstep (se 1 (by rfl) ⟨2877332, by rfl⟩ : syracuseStep 3836443 = 5754665) B5754665
theorem B2558927 : Blo 595291 2558927 := bstep (se 1 (by rfl) ⟨1919195, by rfl⟩ : syracuseStep 2558927 = 3838391) B3838391
theorem B41881171 : Blo 595291 41881171 := bstep (se 1 (by rfl) ⟨31410878, by rfl⟩ : syracuseStep 41881171 = 62821757) B62821757
theorem B5116283 : Blo 595291 5116283 := bstep (se 1 (by rfl) ⟨3837212, by rfl⟩ : syracuseStep 5116283 = 7674425) B7674425
theorem B24514973 : Blo 595291 24514973 := bstep (se 3 (by rfl) ⟨4596557, by rfl⟩ : syracuseStep 24514973 = 9193115) B9193115
theorem B8754157 : Blo 595291 8754157 := bstep (se 3 (by rfl) ⟨1641404, by rfl⟩ : syracuseStep 8754157 = 3282809) B3282809
theorem B595391 : Blo 595291 595391 := bstep (se 1 (by rfl) ⟨446543, by rfl⟩ : syracuseStep 595391 = 893087) B893087
theorem B595483 : Blo 595291 595483 := bstep (se 1 (by rfl) ⟨446612, by rfl⟩ : syracuseStep 595483 = 893225) B893225
theorem B4855859 : Blo 595291 4855859 := bstep (se 1 (by rfl) ⟨3641894, by rfl⟩ : syracuseStep 4855859 = 7283789) B7283789
theorem B596095 : Blo 595291 596095 := bstep (se 1 (by rfl) ⟨447071, by rfl⟩ : syracuseStep 596095 = 894143) B894143
theorem B3020975 : Blo 595291 3020975 := bstep (se 1 (by rfl) ⟨2265731, by rfl⟩ : syracuseStep 3020975 = 4531463) B4531463
theorem B2038537 : Blo 595291 2038537 := bstep (se 2 (by rfl) ⟨764451, by rfl⟩ : syracuseStep 2038537 = 1528903) B1528903
theorem B597119 : Blo 595291 597119 := bstep (se 1 (by rfl) ⟨447839, by rfl⟩ : syracuseStep 597119 = 895679) B895679
theorem B1383983 : Blo 595291 1383983 := bstep (se 1 (by rfl) ⟨1037987, by rfl⟩ : syracuseStep 1383983 = 2075975) B2075975
theorem B1515145 : Blo 595291 1515145 := bstep (se 2 (by rfl) ⟨568179, by rfl⟩ : syracuseStep 1515145 = 1136359) B1136359
theorem B597711 : Blo 595291 597711 := bstep (se 1 (by rfl) ⟨448283, by rfl⟩ : syracuseStep 597711 = 896567) B896567
theorem B892991 : Blo 595291 892991 := bstep (se 1 (by rfl) ⟨669743, by rfl⟩ : syracuseStep 892991 = 1339487) B1339487
theorem B16523459 : Blo 595291 16523459 := bstep (se 1 (by rfl) ⟨12392594, by rfl⟩ : syracuseStep 16523459 = 24785189) B24785189
theorem B3023081 : Blo 595291 3023081 := bstep (se 2 (by rfl) ⟨1133655, by rfl⟩ : syracuseStep 3023081 = 2267311) B2267311
theorem B598847 : Blo 595291 598847 := bstep (se 1 (by rfl) ⟨449135, by rfl⟩ : syracuseStep 598847 = 898271) B898271
theorem B893855 : Blo 595291 893855 := bstep (se 1 (by rfl) ⟨670391, by rfl⟩ : syracuseStep 893855 = 1340783) B1340783
theorem B893945 : Blo 595291 893945 := bstep (se 2 (by rfl) ⟨335229, by rfl⟩ : syracuseStep 893945 = 670459) B670459
theorem B599111 : Blo 595291 599111 := bstep (se 1 (by rfl) ⟨449333, by rfl⟩ : syracuseStep 599111 = 898667) B898667
theorem B599131 : Blo 595291 599131 := bstep (se 1 (by rfl) ⟨449348, by rfl⟩ : syracuseStep 599131 = 898697) B898697
theorem B2335979 : Blo 595291 2335979 := bstep (se 1 (by rfl) ⟨1751984, by rfl⟩ : syracuseStep 2335979 = 3503969) B3503969
theorem B894329 : Blo 595291 894329 := bstep (se 2 (by rfl) ⟨335373, by rfl⟩ : syracuseStep 894329 = 670747) B670747
theorem B1516927 : Blo 595291 1516927 := bstep (se 1 (by rfl) ⟨1137695, by rfl⟩ : syracuseStep 1516927 = 2275391) B2275391
theorem B894431 : Blo 595291 894431 := bstep (se 1 (by rfl) ⟨670823, by rfl⟩ : syracuseStep 894431 = 1341647) B1341647
theorem B4073129 : Blo 595291 4073129 := bstep (se 2 (by rfl) ⟨1527423, by rfl⟩ : syracuseStep 4073129 = 3054847) B3054847
theorem B43656893 : Blo 595291 43656893 := bstep (se 3 (by rfl) ⟨8185667, by rfl⟩ : syracuseStep 43656893 = 16371335) B16371335
theorem B895031 : Blo 595291 895031 := bstep (se 1 (by rfl) ⟨671273, by rfl⟩ : syracuseStep 895031 = 1342547) B1342547
theorem B895067 : Blo 595291 895067 := bstep (se 1 (by rfl) ⟨671300, by rfl⟩ : syracuseStep 895067 = 1342601) B1342601
theorem B895643 : Blo 595291 895643 := bstep (se 1 (by rfl) ⟨671732, by rfl⟩ : syracuseStep 895643 = 1343465) B1343465
theorem B18393763 : Blo 595291 18393763 := bstep (se 1 (by rfl) ⟨13795322, by rfl⟩ : syracuseStep 18393763 = 27590645) B27590645
theorem B79834247 : Blo 595291 79834247 := bstep (se 1 (by rfl) ⟨59875685, by rfl⟩ : syracuseStep 79834247 = 119751371) B119751371
theorem B896231 : Blo 595291 896231 := bstep (se 1 (by rfl) ⟨672173, by rfl⟩ : syracuseStep 896231 = 1344347) B1344347
theorem B2010365 : Blo 595291 2010365 := bstep (se 3 (by rfl) ⟨376943, by rfl⟩ : syracuseStep 2010365 = 753887) B753887
theorem B43625911 : Blo 595291 43625911 := bstep (se 1 (by rfl) ⟨32719433, by rfl⟩ : syracuseStep 43625911 = 65438867) B65438867
theorem B3026483 : Blo 595291 3026483 := bstep (se 1 (by rfl) ⟨2269862, by rfl⟩ : syracuseStep 3026483 = 4539725) B4539725
theorem B7647209 : Blo 595291 7647209 := bstep (se 2 (by rfl) ⟨2867703, by rfl⟩ : syracuseStep 7647209 = 5735407) B5735407
theorem B897179 : Blo 595291 897179 := bstep (se 1 (by rfl) ⟨672884, by rfl⟩ : syracuseStep 897179 = 1345769) B1345769
theorem B3028103 : Blo 595291 3028103 := bstep (se 1 (by rfl) ⟨2271077, by rfl⟩ : syracuseStep 3028103 = 4542155) B4542155
theorem B10204541 : Blo 595291 10204541 := bstep (se 3 (by rfl) ⟨1913351, by rfl⟩ : syracuseStep 10204541 = 3826703) B3826703
theorem B636383 : Blo 595291 636383 := bstep (se 1 (by rfl) ⟨477287, by rfl⟩ : syracuseStep 636383 = 954575) B954575
theorem B1455911 : Blo 595291 1455911 := bstep (se 1 (by rfl) ⟨1091933, by rfl⟩ : syracuseStep 1455911 = 2183867) B2183867
theorem B4603517 : Blo 595291 4603517 := bstep (se 3 (by rfl) ⟨863159, by rfl⟩ : syracuseStep 4603517 = 1726319) B1726319
theorem B1130527 : Blo 595291 1130527 := bstep (se 1 (by rfl) ⟨847895, by rfl⟩ : syracuseStep 1130527 = 1695791) B1695791
theorem B8634995 : Blo 595291 8634995 := bstep (se 1 (by rfl) ⟨6476246, by rfl⟩ : syracuseStep 8634995 = 12952493) B12952493
theorem B673051 : Blo 595291 673051 := bstep (se 1 (by rfl) ⟨504788, by rfl⟩ : syracuseStep 673051 = 1009577) B1009577
theorem B674203 : Blo 595291 674203 := bstep (se 1 (by rfl) ⟨505652, by rfl⟩ : syracuseStep 674203 = 1011305) B1011305
theorem B4541183 : Blo 595291 4541183 := bstep (se 1 (by rfl) ⟨3405887, by rfl⟩ : syracuseStep 4541183 = 6811775) B6811775
theorem B10178297 : Blo 595291 10178297 := bstep (se 2 (by rfl) ⟨3816861, by rfl⟩ : syracuseStep 10178297 = 7633723) B7633723
theorem B2020031 : Blo 595291 2020031 := bstep (se 1 (by rfl) ⟨1515023, by rfl⟩ : syracuseStep 2020031 = 3030047) B3030047
theorem B1005743 : Blo 595291 1005743 := bstep (se 1 (by rfl) ⟨754307, by rfl⟩ : syracuseStep 1005743 = 1508615) B1508615
theorem B23320871 : Blo 595291 23320871 := bstep (se 1 (by rfl) ⟨17490653, by rfl⟩ : syracuseStep 23320871 = 34981307) B34981307
theorem B5102135 : Blo 595291 5102135 := bstep (se 1 (by rfl) ⟨3826601, by rfl⟩ : syracuseStep 5102135 = 7653203) B7653203
theorem B1006249 : Blo 595291 1006249 := bstep (se 2 (by rfl) ⟨377343, by rfl⟩ : syracuseStep 1006249 = 754687) B754687
theorem B4315943 : Blo 595291 4315943 := bstep (se 1 (by rfl) ⟨3236957, by rfl⟩ : syracuseStep 4315943 = 6473915) B6473915
theorem B19323785 : Blo 595291 19323785 := bstep (se 2 (by rfl) ⟨7246419, by rfl⟩ : syracuseStep 19323785 = 14492839) B14492839
theorem B6119135 : Blo 595291 6119135 := bstep (se 1 (by rfl) ⟨4589351, by rfl⟩ : syracuseStep 6119135 = 9178703) B9178703
theorem B5103911 : Blo 595291 5103911 := bstep (se 1 (by rfl) ⟨3827933, by rfl⟩ : syracuseStep 5103911 = 7655867) B7655867
theorem B1008031 : Blo 595291 1008031 := bstep (se 1 (by rfl) ⟨756023, by rfl⟩ : syracuseStep 1008031 = 1512047) B1512047
theorem B4089275 : Blo 595291 4089275 := bstep (se 1 (by rfl) ⟨3066956, by rfl⟩ : syracuseStep 4089275 = 6133913) B6133913
theorem B1697249 : Blo 595291 1697249 := bstep (se 2 (by rfl) ⟨636468, by rfl⟩ : syracuseStep 1697249 = 1272937) B1272937
theorem B1009847 : Blo 595291 1009847 := bstep (se 1 (by rfl) ⟨757385, by rfl⟩ : syracuseStep 1009847 = 1514771) B1514771
theorem B15952183 : Blo 595291 15952183 := bstep (se 1 (by rfl) ⟨11964137, by rfl⟩ : syracuseStep 15952183 = 23928275) B23928275
theorem B1010441 : Blo 595291 1010441 := bstep (se 2 (by rfl) ⟨378915, by rfl⟩ : syracuseStep 1010441 = 757831) B757831
theorem B4549931 : Blo 595291 4549931 := bstep (se 1 (by rfl) ⟨3412448, by rfl⟩ : syracuseStep 4549931 = 6824897) B6824897
theorem B2551121 : Blo 595291 2551121 := bstep (se 2 (by rfl) ⟨956670, by rfl⟩ : syracuseStep 2551121 = 1913341) B1913341
theorem B1273313 : Blo 595291 1273313 := bstep (se 2 (by rfl) ⟨477492, by rfl⟩ : syracuseStep 1273313 = 954985) B954985
theorem B58093145 : Blo 595291 58093145 := bstep (se 2 (by rfl) ⟨21784929, by rfl⟩ : syracuseStep 58093145 = 43569859) B43569859
theorem B848351 : Blo 595291 848351 := bstep (se 1 (by rfl) ⟨636263, by rfl⟩ : syracuseStep 848351 = 1272527) B1272527
theorem B1340009 : Blo 595291 1340009 := bstep (se 2 (by rfl) ⟨502503, by rfl⟩ : syracuseStep 1340009 = 1005007) B1005007
theorem B1340063 : Blo 595291 1340063 := bstep (se 1 (by rfl) ⟨1005047, by rfl⟩ : syracuseStep 1340063 = 2010095) B2010095
theorem B1341395 : Blo 595291 1341395 := bstep (se 1 (by rfl) ⟨1006046, by rfl⟩ : syracuseStep 1341395 = 2012093) B2012093
theorem B6125705 : Blo 595291 6125705 := bstep (se 2 (by rfl) ⟨2297139, by rfl⟩ : syracuseStep 6125705 = 4594279) B4594279
theorem B2260507 : Blo 595291 2260507 := bstep (se 1 (by rfl) ⟨1695380, by rfl⟩ : syracuseStep 2260507 = 3390761) B3390761
theorem B2457161 : Blo 595291 2457161 := bstep (se 2 (by rfl) ⟨921435, by rfl⟩ : syracuseStep 2457161 = 1842871) B1842871
theorem B1507369 : Blo 595291 1507369 := bstep (se 2 (by rfl) ⟨565263, by rfl⟩ : syracuseStep 1507369 = 1130527) B1130527
theorem B1638599 : Blo 595291 1638599 := bstep (se 1 (by rfl) ⟨1228949, by rfl⟩ : syracuseStep 1638599 = 2457899) B2457899
theorem B1344041 : Blo 595291 1344041 := bstep (se 2 (by rfl) ⟨504015, by rfl⟩ : syracuseStep 1344041 = 1008031) B1008031
theorem B2262269 : Blo 595291 2262269 := bstep (se 3 (by rfl) ⟨424175, by rfl⟩ : syracuseStep 2262269 = 848351) B848351
theorem B2557423 : Blo 595291 2557423 := bstep (se 1 (by rfl) ⟨1918067, by rfl⟩ : syracuseStep 2557423 = 3836135) B3836135
theorem B1705951 : Blo 595291 1705951 := bstep (se 1 (by rfl) ⟨1279463, by rfl⟩ : syracuseStep 1705951 = 2558927) B2558927
theorem B6785531 : Blo 595291 6785531 := bstep (se 1 (by rfl) ⟨5089148, by rfl⟩ : syracuseStep 6785531 = 10178297) B10178297
theorem B3410855 : Blo 595291 3410855 := bstep (se 1 (by rfl) ⟨2558141, by rfl⟩ : syracuseStep 3410855 = 5116283) B5116283
theorem B1346687 : Blo 595291 1346687 := bstep (se 1 (by rfl) ⟨1010015, by rfl⟩ : syracuseStep 1346687 = 2020031) B2020031
theorem B5115257 : Blo 595291 5115257 := bstep (se 2 (by rfl) ⟨1918221, by rfl⟩ : syracuseStep 5115257 = 3836443) B3836443
theorem B58167881 : Blo 595291 58167881 := bstep (se 2 (by rfl) ⟨21812955, by rfl⟩ : syracuseStep 58167881 = 43625911) B43625911
theorem B12882523 : Blo 595291 12882523 := bstep (se 1 (by rfl) ⟨9661892, by rfl⟩ : syracuseStep 12882523 = 19323785) B19323785
theorem B55841561 : Blo 595291 55841561 := bstep (se 2 (by rfl) ⟨20940585, by rfl⟩ : syracuseStep 55841561 = 41881171) B41881171
theorem B922655 : Blo 595291 922655 := bstep (se 1 (by rfl) ⟨691991, by rfl⟩ : syracuseStep 922655 = 1383983) B1383983
theorem B595327 : Blo 595291 595327 := bstep (se 1 (by rfl) ⟨446495, by rfl⟩ : syracuseStep 595327 = 892991) B892991
theorem B11015639 : Blo 595291 11015639 := bstep (se 1 (by rfl) ⟨8261729, by rfl⟩ : syracuseStep 11015639 = 16523459) B16523459
theorem B595903 : Blo 595291 595903 := bstep (se 1 (by rfl) ⟨446927, by rfl⟩ : syracuseStep 595903 = 893855) B893855
theorem B595963 : Blo 595291 595963 := bstep (se 1 (by rfl) ⟨446972, by rfl⟩ : syracuseStep 595963 = 893945) B893945
theorem B596219 : Blo 595291 596219 := bstep (se 1 (by rfl) ⟨447164, by rfl⟩ : syracuseStep 596219 = 894329) B894329
theorem B2726183 : Blo 595291 2726183 := bstep (se 1 (by rfl) ⟨2044637, by rfl⟩ : syracuseStep 2726183 = 4089275) B4089275
theorem B596287 : Blo 595291 596287 := bstep (se 1 (by rfl) ⟨447215, by rfl⟩ : syracuseStep 596287 = 894431) B894431
theorem B29104595 : Blo 595291 29104595 := bstep (se 1 (by rfl) ⟨21828446, by rfl⟩ : syracuseStep 29104595 = 43656893) B43656893
theorem B11672209 : Blo 595291 11672209 := bstep (se 2 (by rfl) ⟨4377078, by rfl⟩ : syracuseStep 11672209 = 8754157) B8754157
theorem B596687 : Blo 595291 596687 := bstep (se 1 (by rfl) ⟨447515, by rfl⟩ : syracuseStep 596687 = 895031) B895031
theorem B596711 : Blo 595291 596711 := bstep (se 1 (by rfl) ⟨447533, by rfl⟩ : syracuseStep 596711 = 895067) B895067
theorem B597095 : Blo 595291 597095 := bstep (se 1 (by rfl) ⟨447821, by rfl⟩ : syracuseStep 597095 = 895643) B895643
theorem B53222831 : Blo 595291 53222831 := bstep (se 1 (by rfl) ⟨39917123, by rfl⟩ : syracuseStep 53222831 = 79834247) B79834247
theorem B597487 : Blo 595291 597487 := bstep (se 1 (by rfl) ⟨448115, by rfl⟩ : syracuseStep 597487 = 896231) B896231
theorem B598119 : Blo 595291 598119 := bstep (se 1 (by rfl) ⟨448589, by rfl⟩ : syracuseStep 598119 = 897179) B897179
theorem B893339 : Blo 595291 893339 := bstep (se 1 (by rfl) ⟨670004, by rfl⟩ : syracuseStep 893339 = 1340009) B1340009
theorem B893375 : Blo 595291 893375 := bstep (se 1 (by rfl) ⟨670031, by rfl⟩ : syracuseStep 893375 = 1340063) B1340063
theorem B894263 : Blo 595291 894263 := bstep (se 1 (by rfl) ⟨670697, by rfl⟩ : syracuseStep 894263 = 1341395) B1341395
theorem B896327 : Blo 595291 896327 := bstep (se 1 (by rfl) ⟨672245, by rfl⟩ : syracuseStep 896327 = 1344491) B1344491
theorem B85078309 : Blo 595291 85078309 := bstep (se 4 (by rfl) ⟨7976091, by rfl⟩ : syracuseStep 85078309 = 15952183) B15952183
theorem B897401 : Blo 595291 897401 := bstep (se 2 (by rfl) ⟨336525, by rfl⟩ : syracuseStep 897401 = 673051) B673051
theorem B3027455 : Blo 595291 3027455 := bstep (se 1 (by rfl) ⟨2270591, by rfl⟩ : syracuseStep 3027455 = 4541183) B4541183
theorem B898937 : Blo 595291 898937 := bstep (se 2 (by rfl) ⟨337101, by rfl⟩ : syracuseStep 898937 = 674203) B674203
theorem B24525017 : Blo 595291 24525017 := bstep (se 2 (by rfl) ⟨9196881, by rfl⟩ : syracuseStep 24525017 = 18393763) B18393763
theorem B670495 : Blo 595291 670495 := bstep (se 1 (by rfl) ⟨502871, by rfl⟩ : syracuseStep 670495 = 1005743) B1005743
theorem B2013983 : Blo 595291 2013983 := bstep (se 1 (by rfl) ⟨1510487, by rfl⟩ : syracuseStep 2013983 = 3020975) B3020975
theorem B15547247 : Blo 595291 15547247 := bstep (se 1 (by rfl) ⟨11660435, by rfl⟩ : syracuseStep 15547247 = 23320871) B23320871
theorem B4079423 : Blo 595291 4079423 := bstep (se 1 (by rfl) ⟨3059567, by rfl⟩ : syracuseStep 4079423 = 6119135) B6119135
theorem B2015387 : Blo 595291 2015387 := bstep (se 1 (by rfl) ⟨1511540, by rfl⟩ : syracuseStep 2015387 = 3023081) B3023081
theorem B1557319 : Blo 595291 1557319 := bstep (se 1 (by rfl) ⟨1167989, by rfl⟩ : syracuseStep 1557319 = 2335979) B2335979
theorem B1131499 : Blo 595291 1131499 := bstep (se 1 (by rfl) ⟨848624, by rfl⟩ : syracuseStep 1131499 = 1697249) B1697249
theorem B673231 : Blo 595291 673231 := bstep (se 1 (by rfl) ⟨504923, by rfl⟩ : syracuseStep 673231 = 1009847) B1009847
theorem B673627 : Blo 595291 673627 := bstep (se 1 (by rfl) ⟨505220, by rfl⟩ : syracuseStep 673627 = 1010441) B1010441
theorem B3033287 : Blo 595291 3033287 := bstep (se 1 (by rfl) ⟨2274965, by rfl⟩ : syracuseStep 3033287 = 4549931) B4549931
theorem B2017655 : Blo 595291 2017655 := bstep (se 1 (by rfl) ⟨1513241, by rfl⟩ : syracuseStep 2017655 = 3026483) B3026483
theorem B5098139 : Blo 595291 5098139 := bstep (se 1 (by rfl) ⟨3823604, by rfl⟩ : syracuseStep 5098139 = 7647209) B7647209
theorem B2018735 : Blo 595291 2018735 := bstep (se 1 (by rfl) ⟨1514051, by rfl⟩ : syracuseStep 2018735 = 3028103) B3028103
theorem B6803027 : Blo 595291 6803027 := bstep (se 1 (by rfl) ⟨5102270, by rfl⟩ : syracuseStep 6803027 = 10204541) B10204541
theorem B970607 : Blo 595291 970607 := bstep (se 1 (by rfl) ⟨727955, by rfl⟩ : syracuseStep 970607 = 1455911) B1455911
theorem B4083803 : Blo 595291 4083803 := bstep (se 1 (by rfl) ⟨3062852, by rfl⟩ : syracuseStep 4083803 = 6125705) B6125705
theorem B2020193 : Blo 595291 2020193 := bstep (se 2 (by rfl) ⟨757572, by rfl⟩ : syracuseStep 2020193 = 1515145) B1515145
theorem B3069011 : Blo 595291 3069011 := bstep (se 1 (by rfl) ⟨2301758, by rfl⟩ : syracuseStep 3069011 = 4603517) B4603517
theorem B5756663 : Blo 595291 5756663 := bstep (se 1 (by rfl) ⟨4317497, by rfl⟩ : syracuseStep 5756663 = 8634995) B8634995
theorem B2022569 : Blo 595291 2022569 := bstep (se 2 (by rfl) ⟨758463, by rfl⟩ : syracuseStep 2022569 = 1516927) B1516927
theorem B16343315 : Blo 595291 16343315 := bstep (se 1 (by rfl) ⟨12257486, by rfl⟩ : syracuseStep 16343315 = 24514973) B24514973
theorem B1697021 : Blo 595291 1697021 := bstep (se 3 (by rfl) ⟨318191, by rfl⟩ : syracuseStep 1697021 = 636383) B636383
theorem B3237239 : Blo 595291 3237239 := bstep (se 1 (by rfl) ⟨2427929, by rfl⟩ : syracuseStep 3237239 = 4855859) B4855859
theorem B3401423 : Blo 595291 3401423 := bstep (se 1 (by rfl) ⟨2551067, by rfl⟩ : syracuseStep 3401423 = 5102135) B5102135
theorem B2877295 : Blo 595291 2877295 := bstep (se 1 (by rfl) ⟨2157971, by rfl⟩ : syracuseStep 2877295 = 4315943) B4315943
theorem B3402607 : Blo 595291 3402607 := bstep (se 1 (by rfl) ⟨2551955, by rfl⟩ : syracuseStep 3402607 = 5103911) B5103911
theorem B2715419 : Blo 595291 2715419 := bstep (se 1 (by rfl) ⟨2036564, by rfl⟩ : syracuseStep 2715419 = 4073129) B4073129
theorem B1340243 : Blo 595291 1340243 := bstep (se 1 (by rfl) ⟨1005182, by rfl⟩ : syracuseStep 1340243 = 2010365) B2010365
theorem B1700747 : Blo 595291 1700747 := bstep (se 1 (by rfl) ⟨1275560, by rfl⟩ : syracuseStep 1700747 = 2551121) B2551121
theorem B848875 : Blo 595291 848875 := bstep (se 1 (by rfl) ⟨636656, by rfl⟩ : syracuseStep 848875 = 1273313) B1273313
theorem B38728763 : Blo 595291 38728763 := bstep (se 1 (by rfl) ⟨29046572, by rfl⟩ : syracuseStep 38728763 = 58093145) B58093145
theorem B1341665 : Blo 595291 1341665 := bstep (se 2 (by rfl) ⟨503124, by rfl⟩ : syracuseStep 1341665 = 1006249) B1006249
theorem B2718049 : Blo 595291 2718049 := bstep (se 2 (by rfl) ⟨1019268, by rfl⟩ : syracuseStep 2718049 = 2038537) B2038537
theorem B3014009 : Blo 595291 3014009 := bstep (se 2 (by rfl) ⟨1130253, by rfl⟩ : syracuseStep 3014009 = 2260507) B2260507
theorem B1638107 : Blo 595291 1638107 := bstep (se 1 (by rfl) ⟨1228580, by rfl⟩ : syracuseStep 1638107 = 2457161) B2457161
theorem B1343591 : Blo 595291 1343591 := bstep (se 1 (by rfl) ⟨1007693, by rfl⟩ : syracuseStep 1343591 = 2015387) B2015387
theorem B1508179 : Blo 595291 1508179 := bstep (se 1 (by rfl) ⟨1131134, by rfl⟩ : syracuseStep 1508179 = 2262269) B2262269
theorem B1508665 : Blo 595291 1508665 := bstep (se 2 (by rfl) ⟨565749, by rfl⟩ : syracuseStep 1508665 = 1131499) B1131499
theorem B1345103 : Blo 595291 1345103 := bstep (se 1 (by rfl) ⟨1008827, by rfl⟩ : syracuseStep 1345103 = 2017655) B2017655
theorem B4523687 : Blo 595291 4523687 := bstep (se 1 (by rfl) ⟨3392765, by rfl⟩ : syracuseStep 4523687 = 6785531) B6785531
theorem B3409897 : Blo 595291 3409897 := bstep (se 2 (by rfl) ⟨1278711, by rfl⟩ : syracuseStep 3409897 = 2557423) B2557423
theorem B3410171 : Blo 595291 3410171 := bstep (se 1 (by rfl) ⟨2557628, by rfl⟩ : syracuseStep 3410171 = 5115257) B5115257
theorem B1345823 : Blo 595291 1345823 := bstep (se 1 (by rfl) ⟨1009367, by rfl⟩ : syracuseStep 1345823 = 2018735) B2018735
theorem B3836393 : Blo 595291 3836393 := bstep (se 2 (by rfl) ⟨1438647, by rfl⟩ : syracuseStep 3836393 = 2877295) B2877295
theorem B2722535 : Blo 595291 2722535 := bstep (se 1 (by rfl) ⟨2041901, by rfl⟩ : syracuseStep 2722535 = 4083803) B4083803
theorem B2460413 : Blo 595291 2460413 := bstep (se 3 (by rfl) ⟨461327, by rfl⟩ : syracuseStep 2460413 = 922655) B922655
theorem B37227707 : Blo 595291 37227707 := bstep (se 1 (by rfl) ⟨27920780, by rfl⟩ : syracuseStep 37227707 = 55841561) B55841561
theorem B1346795 : Blo 595291 1346795 := bstep (se 1 (by rfl) ⟨1010096, by rfl⟩ : syracuseStep 1346795 = 2020193) B2020193
theorem B7343759 : Blo 595291 7343759 := bstep (se 1 (by rfl) ⟨5507819, by rfl⟩ : syracuseStep 7343759 = 11015639) B11015639
theorem B3837775 : Blo 595291 3837775 := bstep (se 1 (by rfl) ⟨2878331, by rfl⟩ : syracuseStep 3837775 = 5756663) B5756663
theorem B19403063 : Blo 595291 19403063 := bstep (se 1 (by rfl) ⟨14552297, by rfl⟩ : syracuseStep 19403063 = 29104595) B29104595
theorem B1348379 : Blo 595291 1348379 := bstep (se 1 (by rfl) ⟨1011284, by rfl⟩ : syracuseStep 1348379 = 2022569) B2022569
theorem B595559 : Blo 595291 595559 := bstep (se 1 (by rfl) ⟨446669, by rfl⟩ : syracuseStep 595559 = 893339) B893339
theorem B595583 : Blo 595291 595583 := bstep (se 1 (by rfl) ⟨446687, by rfl⟩ : syracuseStep 595583 = 893375) B893375
theorem B17176697 : Blo 595291 17176697 := bstep (se 2 (by rfl) ⟨6441261, by rfl⟩ : syracuseStep 17176697 = 12882523) B12882523
theorem B596175 : Blo 595291 596175 := bstep (se 1 (by rfl) ⟨447131, by rfl⟩ : syracuseStep 596175 = 894263) B894263
theorem B2267615 : Blo 595291 2267615 := bstep (se 1 (by rfl) ⟨1700711, by rfl⟩ : syracuseStep 2267615 = 3401423) B3401423
theorem B597551 : Blo 595291 597551 := bstep (se 1 (by rfl) ⟨448163, by rfl⟩ : syracuseStep 597551 = 896327) B896327
theorem B1810279 : Blo 595291 1810279 := bstep (se 1 (by rfl) ⟨1357709, by rfl⟩ : syracuseStep 1810279 = 2715419) B2715419
theorem B598267 : Blo 595291 598267 := bstep (se 1 (by rfl) ⟨448700, by rfl⟩ : syracuseStep 598267 = 897401) B897401
theorem B893495 : Blo 595291 893495 := bstep (se 1 (by rfl) ⟨670121, by rfl⟩ : syracuseStep 893495 = 1340243) B1340243
theorem B893993 : Blo 595291 893993 := bstep (se 2 (by rfl) ⟨335247, by rfl⟩ : syracuseStep 893993 = 670495) B670495
theorem B599291 : Blo 595291 599291 := bstep (se 1 (by rfl) ⟨449468, by rfl⟩ : syracuseStep 599291 = 898937) B898937
theorem B894443 : Blo 595291 894443 := bstep (se 1 (by rfl) ⟨670832, by rfl⟩ : syracuseStep 894443 = 1341665) B1341665
theorem B10364831 : Blo 595291 10364831 := bstep (se 1 (by rfl) ⟨7773623, by rfl⟩ : syracuseStep 10364831 = 15547247) B15547247
theorem B2009339 : Blo 595291 2009339 := bstep (se 1 (by rfl) ⟨1507004, by rfl⟩ : syracuseStep 2009339 = 3014009) B3014009
theorem B1092071 : Blo 595291 1092071 := bstep (se 1 (by rfl) ⟨819053, by rfl⟩ : syracuseStep 1092071 = 1638107) B1638107
theorem B2009825 : Blo 595291 2009825 := bstep (se 2 (by rfl) ⟨753684, by rfl⟩ : syracuseStep 2009825 = 1507369) B1507369
theorem B896027 : Blo 595291 896027 := bstep (se 1 (by rfl) ⟨672020, by rfl⟩ : syracuseStep 896027 = 1344041) B1344041
theorem B2076425 : Blo 595291 2076425 := bstep (se 2 (by rfl) ⟨778659, by rfl⟩ : syracuseStep 2076425 = 1557319) B1557319
theorem B897641 : Blo 595291 897641 := bstep (se 2 (by rfl) ⟨336615, by rfl⟩ : syracuseStep 897641 = 673231) B673231
theorem B2273903 : Blo 595291 2273903 := bstep (se 1 (by rfl) ⟨1705427, by rfl⟩ : syracuseStep 2273903 = 3410855) B3410855
theorem B17478389 : Blo 595291 17478389 := bstep (se 5 (by rfl) ⟨819299, by rfl⟩ : syracuseStep 17478389 = 1638599) B1638599
theorem B897791 : Blo 595291 897791 := bstep (se 1 (by rfl) ⟨673343, by rfl⟩ : syracuseStep 897791 = 1346687) B1346687
theorem B4535351 : Blo 595291 4535351 := bstep (se 1 (by rfl) ⟨3401513, by rfl⟩ : syracuseStep 4535351 = 6803027) B6803027
theorem B898169 : Blo 595291 898169 := bstep (se 2 (by rfl) ⟨336813, by rfl⟩ : syracuseStep 898169 = 673627) B673627
theorem B2274601 : Blo 595291 2274601 := bstep (se 2 (by rfl) ⟨852975, by rfl⟩ : syracuseStep 2274601 = 1705951) B1705951
theorem B38778587 : Blo 595291 38778587 := bstep (se 1 (by rfl) ⟨29083940, by rfl⟩ : syracuseStep 38778587 = 58167881) B58167881
theorem B2046007 : Blo 595291 2046007 := bstep (se 1 (by rfl) ⟨1534505, by rfl⟩ : syracuseStep 2046007 = 3069011) B3069011
theorem B4536809 : Blo 595291 4536809 := bstep (se 2 (by rfl) ⟨1701303, by rfl⟩ : syracuseStep 4536809 = 3402607) B3402607
theorem B10895543 : Blo 595291 10895543 := bstep (se 1 (by rfl) ⟨8171657, by rfl⟩ : syracuseStep 10895543 = 16343315) B16343315
theorem B1131347 : Blo 595291 1131347 := bstep (se 1 (by rfl) ⟨848510, by rfl⟩ : syracuseStep 1131347 = 1697021) B1697021
theorem B1131833 : Blo 595291 1131833 := bstep (se 2 (by rfl) ⟨424437, by rfl⟩ : syracuseStep 1131833 = 848875) B848875
theorem B2018303 : Blo 595291 2018303 := bstep (se 1 (by rfl) ⟨1513727, by rfl⟩ : syracuseStep 2018303 = 3027455) B3027455
theorem B3624065 : Blo 595291 3624065 := bstep (se 2 (by rfl) ⟨1359024, by rfl⟩ : syracuseStep 3624065 = 2718049) B2718049
theorem B1133831 : Blo 595291 1133831 := bstep (se 1 (by rfl) ⟨850373, by rfl⟩ : syracuseStep 1133831 = 1700747) B1700747
theorem B2022191 : Blo 595291 2022191 := bstep (se 1 (by rfl) ⟨1516643, by rfl⟩ : syracuseStep 2022191 = 3033287) B3033287
theorem B3398759 : Blo 595291 3398759 := bstep (se 1 (by rfl) ⟨2549069, by rfl⟩ : syracuseStep 3398759 = 5098139) B5098139
theorem B647071 : Blo 595291 647071 := bstep (se 1 (by rfl) ⟨485303, by rfl⟩ : syracuseStep 647071 = 970607) B970607
theorem B35481887 : Blo 595291 35481887 := bstep (se 1 (by rfl) ⟨26611415, by rfl⟩ : syracuseStep 35481887 = 53222831) B53222831
theorem B113437745 : Blo 595291 113437745 := bstep (se 2 (by rfl) ⟨42539154, by rfl⟩ : syracuseStep 113437745 = 85078309) B85078309
theorem B7269821 : Blo 595291 7269821 := bstep (se 3 (by rfl) ⟨1363091, by rfl⟩ : syracuseStep 7269821 = 2726183) B2726183
theorem B2158159 : Blo 595291 2158159 := bstep (se 1 (by rfl) ⟨1618619, by rfl⟩ : syracuseStep 2158159 = 3237239) B3237239
theorem B25819175 : Blo 595291 25819175 := bstep (se 1 (by rfl) ⟨19364381, by rfl⟩ : syracuseStep 25819175 = 38728763) B38728763
theorem B15562945 : Blo 595291 15562945 := bstep (se 2 (by rfl) ⟨5836104, by rfl⟩ : syracuseStep 15562945 = 11672209) B11672209
theorem B16350011 : Blo 595291 16350011 := bstep (se 1 (by rfl) ⟨12262508, by rfl⟩ : syracuseStep 16350011 = 24525017) B24525017
theorem B1342655 : Blo 595291 1342655 := bstep (se 1 (by rfl) ⟨1006991, by rfl⟩ : syracuseStep 1342655 = 2013983) B2013983
theorem B2719615 : Blo 595291 2719615 := bstep (se 1 (by rfl) ⟨2039711, by rfl⟩ : syracuseStep 2719615 = 4079423) B4079423
theorem B3015791 : Blo 595291 3015791 := bstep (se 1 (by rfl) ⟨2261843, by rfl⟩ : syracuseStep 3015791 = 4523687) B4523687
theorem B2557595 : Blo 595291 2557595 := bstep (se 1 (by rfl) ⟨1918196, by rfl⟩ : syracuseStep 2557595 = 3836393) B3836393
theorem B1345535 : Blo 595291 1345535 := bstep (se 1 (by rfl) ⟨1009151, by rfl⟩ : syracuseStep 1345535 = 2018303) B2018303
theorem B755887 : Blo 595291 755887 := bstep (se 1 (by rfl) ⟨566915, by rfl⟩ : syracuseStep 755887 = 1133831) B1133831
theorem B3016925 : Blo 595291 3016925 := bstep (se 3 (by rfl) ⟨565673, by rfl⟩ : syracuseStep 3016925 = 1131347) B1131347
theorem B3018221 : Blo 595291 3018221 := bstep (se 3 (by rfl) ⟨565916, by rfl⟩ : syracuseStep 3018221 = 1131833) B1131833
theorem B1511743 : Blo 595291 1511743 := bstep (se 1 (by rfl) ⟨1133807, by rfl⟩ : syracuseStep 1511743 = 2267615) B2267615
theorem B1348127 : Blo 595291 1348127 := bstep (se 1 (by rfl) ⟨1011095, by rfl⟩ : syracuseStep 1348127 = 2022191) B2022191
theorem B2265839 : Blo 595291 2265839 := bstep (se 1 (by rfl) ⟨1699379, by rfl⟩ : syracuseStep 2265839 = 3398759) B3398759
theorem B5117033 : Blo 595291 5117033 := bstep (se 2 (by rfl) ⟨1918887, by rfl⟩ : syracuseStep 5117033 = 3837775) B3837775
theorem B595663 : Blo 595291 595663 := bstep (se 1 (by rfl) ⟨446747, by rfl⟩ : syracuseStep 595663 = 893495) B893495
theorem B595995 : Blo 595291 595995 := bstep (se 1 (by rfl) ⟨446996, by rfl⟩ : syracuseStep 595995 = 893993) B893993
theorem B596295 : Blo 595291 596295 := bstep (se 1 (by rfl) ⟨447221, by rfl⟩ : syracuseStep 596295 = 894443) B894443
theorem B728047 : Blo 595291 728047 := bstep (se 1 (by rfl) ⟨546035, by rfl⟩ : syracuseStep 728047 = 1092071) B1092071
theorem B6561101 : Blo 595291 6561101 := bstep (se 3 (by rfl) ⟨1230206, by rfl⟩ : syracuseStep 6561101 = 2460413) B2460413
theorem B597351 : Blo 595291 597351 := bstep (se 1 (by rfl) ⟨448013, by rfl⟩ : syracuseStep 597351 = 896027) B896027
theorem B1384283 : Blo 595291 1384283 := bstep (se 1 (by rfl) ⟨1038212, by rfl⟩ : syracuseStep 1384283 = 2076425) B2076425
theorem B2728009 : Blo 595291 2728009 := bstep (se 2 (by rfl) ⟨1023003, by rfl⟩ : syracuseStep 2728009 = 2046007) B2046007
theorem B20750593 : Blo 595291 20750593 := bstep (se 2 (by rfl) ⟨7781472, by rfl⟩ : syracuseStep 20750593 = 15562945) B15562945
theorem B598427 : Blo 595291 598427 := bstep (se 1 (by rfl) ⟨448820, by rfl⟩ : syracuseStep 598427 = 897641) B897641
theorem B1515935 : Blo 595291 1515935 := bstep (se 1 (by rfl) ⟨1136951, by rfl⟩ : syracuseStep 1515935 = 2273903) B2273903
theorem B598527 : Blo 595291 598527 := bstep (se 1 (by rfl) ⟨448895, by rfl⟩ : syracuseStep 598527 = 897791) B897791
theorem B3023567 : Blo 595291 3023567 := bstep (se 1 (by rfl) ⟨2267675, by rfl⟩ : syracuseStep 3023567 = 4535351) B4535351
theorem B598779 : Blo 595291 598779 := bstep (se 1 (by rfl) ⟨449084, by rfl⟩ : syracuseStep 598779 = 898169) B898169
theorem B17212783 : Blo 595291 17212783 := bstep (se 1 (by rfl) ⟨12909587, by rfl⟩ : syracuseStep 17212783 = 25819175) B25819175
theorem B3024539 : Blo 595291 3024539 := bstep (se 1 (by rfl) ⟨2268404, by rfl⟩ : syracuseStep 3024539 = 4536809) B4536809
theorem B895103 : Blo 595291 895103 := bstep (se 1 (by rfl) ⟨671327, by rfl⟩ : syracuseStep 895103 = 1342655) B1342655
theorem B3451045 : Blo 595291 3451045 := bstep (se 4 (by rfl) ⟨323535, by rfl⟩ : syracuseStep 3451045 = 647071) B647071
theorem B895727 : Blo 595291 895727 := bstep (se 1 (by rfl) ⟨671795, by rfl⟩ : syracuseStep 895727 = 1343591) B1343591
theorem B896735 : Blo 595291 896735 := bstep (se 1 (by rfl) ⟨672551, by rfl⟩ : syracuseStep 896735 = 1345103) B1345103
theorem B2010905 : Blo 595291 2010905 := bstep (se 2 (by rfl) ⟨754089, by rfl⟩ : syracuseStep 2010905 = 1508179) B1508179
theorem B2273447 : Blo 595291 2273447 := bstep (se 1 (by rfl) ⟨1705085, by rfl⟩ : syracuseStep 2273447 = 3410171) B3410171
theorem B897215 : Blo 595291 897215 := bstep (se 1 (by rfl) ⟨672911, by rfl⟩ : syracuseStep 897215 = 1345823) B1345823
theorem B2011553 : Blo 595291 2011553 := bstep (se 2 (by rfl) ⟨754332, by rfl⟩ : syracuseStep 2011553 = 1508665) B1508665
theorem B1815023 : Blo 595291 1815023 := bstep (se 1 (by rfl) ⟨1361267, by rfl⟩ : syracuseStep 1815023 = 2722535) B2722535
theorem B46609037 : Blo 595291 46609037 := bstep (se 3 (by rfl) ⟨8739194, by rfl⟩ : syracuseStep 46609037 = 17478389) B17478389
theorem B24818471 : Blo 595291 24818471 := bstep (se 1 (by rfl) ⟨18613853, by rfl⟩ : syracuseStep 24818471 = 37227707) B37227707
theorem B897863 : Blo 595291 897863 := bstep (se 1 (by rfl) ⟨673397, by rfl⟩ : syracuseStep 897863 = 1346795) B1346795
theorem B4895839 : Blo 595291 4895839 := bstep (se 1 (by rfl) ⟨3671879, by rfl⟩ : syracuseStep 4895839 = 7343759) B7343759
theorem B898919 : Blo 595291 898919 := bstep (se 1 (by rfl) ⟨674189, by rfl⟩ : syracuseStep 898919 = 1348379) B1348379
theorem B11451131 : Blo 595291 11451131 := bstep (se 1 (by rfl) ⟨8588348, by rfl⟩ : syracuseStep 11451131 = 17176697) B17176697
theorem B3032801 : Blo 595291 3032801 := bstep (se 2 (by rfl) ⟨1137300, by rfl⟩ : syracuseStep 3032801 = 2274601) B2274601
theorem B9654821 : Blo 595291 9654821 := bstep (se 4 (by rfl) ⟨905139, by rfl⟩ : syracuseStep 9654821 = 1810279) B1810279
theorem B10900007 : Blo 595291 10900007 := bstep (se 1 (by rfl) ⟨8175005, by rfl⟩ : syracuseStep 10900007 = 16350011) B16350011
theorem B3626153 : Blo 595291 3626153 := bstep (se 2 (by rfl) ⟨1359807, by rfl⟩ : syracuseStep 3626153 = 2719615) B2719615
theorem B7263695 : Blo 595291 7263695 := bstep (se 1 (by rfl) ⟨5447771, by rfl⟩ : syracuseStep 7263695 = 10895543) B10895543
theorem B2416043 : Blo 595291 2416043 := bstep (se 1 (by rfl) ⟨1812032, by rfl⟩ : syracuseStep 2416043 = 3624065) B3624065
theorem B4546529 : Blo 595291 4546529 := bstep (se 2 (by rfl) ⟨1704948, by rfl⟩ : syracuseStep 4546529 = 3409897) B3409897
theorem B12935375 : Blo 595291 12935375 := bstep (se 1 (by rfl) ⟨9701531, by rfl⟩ : syracuseStep 12935375 = 19403063) B19403063
theorem B2877545 : Blo 595291 2877545 := bstep (se 2 (by rfl) ⟨1079079, by rfl⟩ : syracuseStep 2877545 = 2158159) B2158159
theorem B6909887 : Blo 595291 6909887 := bstep (se 1 (by rfl) ⟨5182415, by rfl⟩ : syracuseStep 6909887 = 10364831) B10364831
theorem B1339559 : Blo 595291 1339559 := bstep (se 1 (by rfl) ⟨1004669, by rfl⟩ : syracuseStep 1339559 = 2009339) B2009339
theorem B23654591 : Blo 595291 23654591 := bstep (se 1 (by rfl) ⟨17740943, by rfl⟩ : syracuseStep 23654591 = 35481887) B35481887
theorem B1339883 : Blo 595291 1339883 := bstep (se 1 (by rfl) ⟨1004912, by rfl⟩ : syracuseStep 1339883 = 2009825) B2009825
theorem B75625163 : Blo 595291 75625163 := bstep (se 1 (by rfl) ⟨56718872, by rfl⟩ : syracuseStep 75625163 = 113437745) B113437745
theorem B4846547 : Blo 595291 4846547 := bstep (se 1 (by rfl) ⟨3634910, by rfl⟩ : syracuseStep 4846547 = 7269821) B7269821
theorem B25852391 : Blo 595291 25852391 := bstep (se 1 (by rfl) ⟨19389293, by rfl⟩ : syracuseStep 25852391 = 38778587) B38778587
theorem B14549381 : Blo 595291 14549381 := bstep (se 4 (by rfl) ⟨1364004, by rfl⟩ : syracuseStep 14549381 = 2728009) B2728009
theorem B1705063 : Blo 595291 1705063 := bstep (se 1 (by rfl) ⟨1278797, by rfl⟩ : syracuseStep 1705063 = 2557595) B2557595
theorem B1510559 : Blo 595291 1510559 := bstep (se 1 (by rfl) ⟨1132919, by rfl⟩ : syracuseStep 1510559 = 2265839) B2265839
theorem B3411355 : Blo 595291 3411355 := bstep (se 1 (by rfl) ⟨2558516, by rfl⟩ : syracuseStep 3411355 = 5117033) B5117033
theorem B1610695 : Blo 595291 1610695 := bstep (se 1 (by rfl) ⟨1208021, by rfl⟩ : syracuseStep 1610695 = 2416043) B2416043
theorem B922855 : Blo 595291 922855 := bstep (se 1 (by rfl) ⟨692141, by rfl⟩ : syracuseStep 922855 = 1384283) B1384283
theorem B8623583 : Blo 595291 8623583 := bstep (se 1 (by rfl) ⟨6467687, by rfl⟩ : syracuseStep 8623583 = 12935375) B12935375
theorem B7673453 : Blo 595291 7673453 := bstep (se 3 (by rfl) ⟨1438772, by rfl⟩ : syracuseStep 7673453 = 2877545) B2877545
theorem B596735 : Blo 595291 596735 := bstep (se 1 (by rfl) ⟨447551, by rfl⟩ : syracuseStep 596735 = 895103) B895103
theorem B6527785 : Blo 595291 6527785 := bstep (se 2 (by rfl) ⟨2447919, by rfl⟩ : syracuseStep 6527785 = 4895839) B4895839
theorem B597151 : Blo 595291 597151 := bstep (se 1 (by rfl) ⟨447863, by rfl⟩ : syracuseStep 597151 = 895727) B895727
theorem B597823 : Blo 595291 597823 := bstep (se 1 (by rfl) ⟨448367, by rfl⟩ : syracuseStep 597823 = 896735) B896735
theorem B893039 : Blo 595291 893039 := bstep (se 1 (by rfl) ⟨669779, by rfl⟩ : syracuseStep 893039 = 1339559) B1339559
theorem B1515631 : Blo 595291 1515631 := bstep (se 1 (by rfl) ⟨1136723, by rfl⟩ : syracuseStep 1515631 = 2273447) B2273447
theorem B598143 : Blo 595291 598143 := bstep (se 1 (by rfl) ⟨448607, by rfl⟩ : syracuseStep 598143 = 897215) B897215
theorem B15769727 : Blo 595291 15769727 := bstep (se 1 (by rfl) ⟨11827295, by rfl⟩ : syracuseStep 15769727 = 23654591) B23654591
theorem B893255 : Blo 595291 893255 := bstep (se 1 (by rfl) ⟨669941, by rfl⟩ : syracuseStep 893255 = 1339883) B1339883
theorem B31072691 : Blo 595291 31072691 := bstep (se 1 (by rfl) ⟨23304518, by rfl⟩ : syracuseStep 31072691 = 46609037) B46609037
theorem B598575 : Blo 595291 598575 := bstep (se 1 (by rfl) ⟨448931, by rfl⟩ : syracuseStep 598575 = 897863) B897863
theorem B599279 : Blo 595291 599279 := bstep (se 1 (by rfl) ⟨449459, by rfl⟩ : syracuseStep 599279 = 898919) B898919
theorem B18426365 : Blo 595291 18426365 := bstep (se 3 (by rfl) ⟨3454943, by rfl⟩ : syracuseStep 18426365 = 6909887) B6909887
theorem B27667457 : Blo 595291 27667457 := bstep (se 2 (by rfl) ⟨10375296, by rfl⟩ : syracuseStep 27667457 = 20750593) B20750593
theorem B2010527 : Blo 595291 2010527 := bstep (se 1 (by rfl) ⟨1507895, by rfl⟩ : syracuseStep 2010527 = 3015791) B3015791
theorem B897023 : Blo 595291 897023 := bstep (se 1 (by rfl) ⟨672767, by rfl⟩ : syracuseStep 897023 = 1345535) B1345535
theorem B2011283 : Blo 595291 2011283 := bstep (se 1 (by rfl) ⟨1508462, by rfl⟩ : syracuseStep 2011283 = 3016925) B3016925
theorem B22950377 : Blo 595291 22950377 := bstep (se 2 (by rfl) ⟨8606391, by rfl⟩ : syracuseStep 22950377 = 17212783) B17212783
theorem B2012147 : Blo 595291 2012147 := bstep (se 1 (by rfl) ⟨1509110, by rfl⟩ : syracuseStep 2012147 = 3018221) B3018221
theorem B4601393 : Blo 595291 4601393 := bstep (se 2 (by rfl) ⟨1725522, by rfl⟩ : syracuseStep 4601393 = 3451045) B3451045
theorem B898751 : Blo 595291 898751 := bstep (se 1 (by rfl) ⟨674063, by rfl⟩ : syracuseStep 898751 = 1348127) B1348127
theorem B6436547 : Blo 595291 6436547 := bstep (se 1 (by rfl) ⟨4827410, by rfl⟩ : syracuseStep 6436547 = 9654821) B9654821
theorem B4374067 : Blo 595291 4374067 := bstep (se 1 (by rfl) ⟨3280550, by rfl⟩ : syracuseStep 4374067 = 6561101) B6561101
theorem B3031019 : Blo 595291 3031019 := bstep (se 1 (by rfl) ⟨2273264, by rfl⟩ : syracuseStep 3031019 = 4546529) B4546529
theorem B2015657 : Blo 595291 2015657 := bstep (se 2 (by rfl) ⟨755871, by rfl⟩ : syracuseStep 2015657 = 1511743) B1511743
theorem B2015711 : Blo 595291 2015711 := bstep (se 1 (by rfl) ⟨1511783, by rfl⟩ : syracuseStep 2015711 = 3023567) B3023567
theorem B2016359 : Blo 595291 2016359 := bstep (se 1 (by rfl) ⟨1512269, by rfl⟩ : syracuseStep 2016359 = 3024539) B3024539
theorem B50416775 : Blo 595291 50416775 := bstep (se 1 (by rfl) ⟨37812581, by rfl⟩ : syracuseStep 50416775 = 75625163) B75625163
theorem B3231031 : Blo 595291 3231031 := bstep (se 1 (by rfl) ⟨2423273, by rfl⟩ : syracuseStep 3231031 = 4846547) B4846547
theorem B970729 : Blo 595291 970729 := bstep (se 2 (by rfl) ⟨364023, by rfl⟩ : syracuseStep 970729 = 728047) B728047
theorem B2021867 : Blo 595291 2021867 := bstep (se 1 (by rfl) ⟨1516400, by rfl⟩ : syracuseStep 2021867 = 3032801) B3032801
theorem B1007849 : Blo 595291 1007849 := bstep (se 2 (by rfl) ⟨377943, by rfl⟩ : syracuseStep 1007849 = 755887) B755887
theorem B7266671 : Blo 595291 7266671 := bstep (se 1 (by rfl) ⟨5450003, by rfl⟩ : syracuseStep 7266671 = 10900007) B10900007
theorem B2417435 : Blo 595291 2417435 := bstep (se 1 (by rfl) ⟨1813076, by rfl⟩ : syracuseStep 2417435 = 3626153) B3626153
theorem B4842463 : Blo 595291 4842463 := bstep (se 1 (by rfl) ⟨3631847, by rfl⟩ : syracuseStep 4842463 = 7263695) B7263695
theorem B1010623 : Blo 595291 1010623 := bstep (se 1 (by rfl) ⟨757967, by rfl⟩ : syracuseStep 1010623 = 1515935) B1515935
theorem B1340603 : Blo 595291 1340603 := bstep (se 1 (by rfl) ⟨1005452, by rfl⟩ : syracuseStep 1340603 = 2010905) B2010905
theorem B1341035 : Blo 595291 1341035 := bstep (se 1 (by rfl) ⟨1005776, by rfl⟩ : syracuseStep 1341035 = 2011553) B2011553
theorem B1210015 : Blo 595291 1210015 := bstep (se 1 (by rfl) ⟨907511, by rfl⟩ : syracuseStep 1210015 = 1815023) B1815023
theorem B16545647 : Blo 595291 16545647 := bstep (se 1 (by rfl) ⟨12409235, by rfl⟩ : syracuseStep 16545647 = 24818471) B24818471
theorem B17234927 : Blo 595291 17234927 := bstep (se 1 (by rfl) ⟨12926195, by rfl⟩ : syracuseStep 17234927 = 25852391) B25852391
theorem B7634087 : Blo 595291 7634087 := bstep (se 1 (by rfl) ⟨5725565, by rfl⟩ : syracuseStep 7634087 = 11451131) B11451131
theorem B9699587 : Blo 595291 9699587 := bstep (se 1 (by rfl) ⟨7274690, by rfl⟩ : syracuseStep 9699587 = 14549381) B14549381
theorem B1343771 : Blo 595291 1343771 := bstep (se 1 (by rfl) ⟨1007828, by rfl⟩ : syracuseStep 1343771 = 2015657) B2015657
theorem B1343807 : Blo 595291 1343807 := bstep (se 1 (by rfl) ⟨1007855, by rfl⟩ : syracuseStep 1343807 = 2015711) B2015711
theorem B1344239 : Blo 595291 1344239 := bstep (se 1 (by rfl) ⟨1008179, by rfl⟩ : syracuseStep 1344239 = 2016359) B2016359
theorem B6456617 : Blo 595291 6456617 := bstep (se 2 (by rfl) ⟨2421231, by rfl⟩ : syracuseStep 6456617 = 4842463) B4842463
theorem B5115635 : Blo 595291 5115635 := bstep (se 1 (by rfl) ⟨3836726, by rfl⟩ : syracuseStep 5115635 = 7673453) B7673453
theorem B1347497 : Blo 595291 1347497 := bstep (se 2 (by rfl) ⟨505311, by rfl⟩ : syracuseStep 1347497 = 1010623) B1010623
theorem B1347911 : Blo 595291 1347911 := bstep (se 1 (by rfl) ⟨1010933, by rfl⟩ : syracuseStep 1347911 = 2021867) B2021867
theorem B595359 : Blo 595291 595359 := bstep (se 1 (by rfl) ⟨446519, by rfl⟩ : syracuseStep 595359 = 893039) B893039
theorem B595503 : Blo 595291 595503 := bstep (se 1 (by rfl) ⟨446627, by rfl⟩ : syracuseStep 595503 = 893255) B893255
theorem B1611623 : Blo 595291 1611623 := bstep (se 1 (by rfl) ⟨1208717, by rfl⟩ : syracuseStep 1611623 = 2417435) B2417435
theorem B1613353 : Blo 595291 1613353 := bstep (se 2 (by rfl) ⟨605007, by rfl⟩ : syracuseStep 1613353 = 1210015) B1210015
theorem B598015 : Blo 595291 598015 := bstep (se 1 (by rfl) ⟨448511, by rfl⟩ : syracuseStep 598015 = 897023) B897023
theorem B893735 : Blo 595291 893735 := bstep (se 1 (by rfl) ⟨670301, by rfl⟩ : syracuseStep 893735 = 1340603) B1340603
theorem B894023 : Blo 595291 894023 := bstep (se 1 (by rfl) ⟨670517, by rfl⟩ : syracuseStep 894023 = 1341035) B1341035
theorem B599167 : Blo 595291 599167 := bstep (se 1 (by rfl) ⟨449375, by rfl⟩ : syracuseStep 599167 = 898751) B898751
theorem B5089391 : Blo 595291 5089391 := bstep (se 1 (by rfl) ⟨3817043, by rfl⟩ : syracuseStep 5089391 = 7634087) B7634087
theorem B2273417 : Blo 595291 2273417 := bstep (se 2 (by rfl) ⟨852531, by rfl⟩ : syracuseStep 2273417 = 1705063) B1705063
theorem B5749055 : Blo 595291 5749055 := bstep (se 1 (by rfl) ⟨4311791, by rfl⟩ : syracuseStep 5749055 = 8623583) B8623583
theorem B4308041 : Blo 595291 4308041 := bstep (se 2 (by rfl) ⟨1615515, by rfl⟩ : syracuseStep 4308041 = 3231031) B3231031
theorem B671899 : Blo 595291 671899 := bstep (se 1 (by rfl) ⟨503924, by rfl⟩ : syracuseStep 671899 = 1007849) B1007849
theorem B2147593 : Blo 595291 2147593 := bstep (se 2 (by rfl) ⟨805347, by rfl⟩ : syracuseStep 2147593 = 1610695) B1610695
theorem B1230473 : Blo 595291 1230473 := bstep (se 2 (by rfl) ⟨461427, by rfl⟩ : syracuseStep 1230473 = 922855) B922855
theorem B3067595 : Blo 595291 3067595 := bstep (se 1 (by rfl) ⟨2300696, by rfl⟩ : syracuseStep 3067595 = 4601393) B4601393
theorem B8703713 : Blo 595291 8703713 := bstep (se 2 (by rfl) ⟨3263892, by rfl⟩ : syracuseStep 8703713 = 6527785) B6527785
theorem B11030431 : Blo 595291 11030431 := bstep (se 1 (by rfl) ⟨8272823, by rfl⟩ : syracuseStep 11030431 = 16545647) B16545647
theorem B11489951 : Blo 595291 11489951 := bstep (se 1 (by rfl) ⟨8617463, by rfl⟩ : syracuseStep 11489951 = 17234927) B17234927
theorem B2020679 : Blo 595291 2020679 := bstep (se 1 (by rfl) ⟨1515509, by rfl⟩ : syracuseStep 2020679 = 3031019) B3031019
theorem B2020841 : Blo 595291 2020841 := bstep (se 2 (by rfl) ⟨757815, by rfl⟩ : syracuseStep 2020841 = 1515631) B1515631
theorem B82860509 : Blo 595291 82860509 := bstep (se 3 (by rfl) ⟨15536345, by rfl⟩ : syracuseStep 82860509 = 31072691) B31072691
theorem B33611183 : Blo 595291 33611183 := bstep (se 1 (by rfl) ⟨25208387, by rfl⟩ : syracuseStep 33611183 = 50416775) B50416775
theorem B1007039 : Blo 595291 1007039 := bstep (se 1 (by rfl) ⟨755279, by rfl⟩ : syracuseStep 1007039 = 1510559) B1510559
theorem B4548473 : Blo 595291 4548473 := bstep (se 2 (by rfl) ⟨1705677, by rfl⟩ : syracuseStep 4548473 = 3411355) B3411355
theorem B10513151 : Blo 595291 10513151 := bstep (se 1 (by rfl) ⟨7884863, by rfl⟩ : syracuseStep 10513151 = 15769727) B15769727
theorem B4844447 : Blo 595291 4844447 := bstep (se 1 (by rfl) ⟨3633335, by rfl⟩ : syracuseStep 4844447 = 7266671) B7266671
theorem B12284243 : Blo 595291 12284243 := bstep (se 1 (by rfl) ⟨9213182, by rfl⟩ : syracuseStep 12284243 = 18426365) B18426365
theorem B18444971 : Blo 595291 18444971 := bstep (se 1 (by rfl) ⟨13833728, by rfl⟩ : syracuseStep 18444971 = 27667457) B27667457
theorem B1340351 : Blo 595291 1340351 := bstep (se 1 (by rfl) ⟨1005263, by rfl⟩ : syracuseStep 1340351 = 2010527) B2010527
theorem B1340855 : Blo 595291 1340855 := bstep (se 1 (by rfl) ⟨1005641, by rfl⟩ : syracuseStep 1340855 = 2011283) B2011283
theorem B15300251 : Blo 595291 15300251 := bstep (se 1 (by rfl) ⟨11475188, by rfl⟩ : syracuseStep 15300251 = 22950377) B22950377
theorem B1341431 : Blo 595291 1341431 := bstep (se 1 (by rfl) ⟨1006073, by rfl⟩ : syracuseStep 1341431 = 2012147) B2012147
theorem B4291031 : Blo 595291 4291031 := bstep (se 1 (by rfl) ⟨3218273, by rfl⟩ : syracuseStep 4291031 = 6436547) B6436547
theorem B5832089 : Blo 595291 5832089 := bstep (se 2 (by rfl) ⟨2187033, by rfl⟩ : syracuseStep 5832089 = 4374067) B4374067
theorem B20708885 : Blo 595291 20708885 := bstep (se 6 (by rfl) ⟨485364, by rfl⟩ : syracuseStep 20708885 = 970729) B970729
theorem B820315 : Blo 595291 820315 := bstep (se 1 (by rfl) ⟨615236, by rfl⟩ : syracuseStep 820315 = 1230473) B1230473
theorem B3410423 : Blo 595291 3410423 := bstep (se 1 (by rfl) ⟨2557817, by rfl⟩ : syracuseStep 3410423 = 5115635) B5115635
theorem B1347119 : Blo 595291 1347119 := bstep (se 1 (by rfl) ⟨1010339, by rfl⟩ : syracuseStep 1347119 = 2020679) B2020679
theorem B1347227 : Blo 595291 1347227 := bstep (se 1 (by rfl) ⟨1010420, by rfl⟩ : syracuseStep 1347227 = 2020841) B2020841
theorem B4297661 : Blo 595291 4297661 := bstep (se 3 (by rfl) ⟨805811, by rfl⟩ : syracuseStep 4297661 = 1611623) B1611623
theorem B595823 : Blo 595291 595823 := bstep (se 1 (by rfl) ⟨446867, by rfl⟩ : syracuseStep 595823 = 893735) B893735
theorem B596015 : Blo 595291 596015 := bstep (se 1 (by rfl) ⟨447011, by rfl⟩ : syracuseStep 596015 = 894023) B894023
theorem B1515611 : Blo 595291 1515611 := bstep (se 1 (by rfl) ⟨1136708, by rfl⟩ : syracuseStep 1515611 = 2273417) B2273417
theorem B12296647 : Blo 595291 12296647 := bstep (se 1 (by rfl) ⟨9222485, by rfl⟩ : syracuseStep 12296647 = 18444971) B18444971
theorem B893567 : Blo 595291 893567 := bstep (se 1 (by rfl) ⟨670175, by rfl⟩ : syracuseStep 893567 = 1340351) B1340351
theorem B893903 : Blo 595291 893903 := bstep (se 1 (by rfl) ⟨670427, by rfl⟩ : syracuseStep 893903 = 1340855) B1340855
theorem B10200167 : Blo 595291 10200167 := bstep (se 1 (by rfl) ⟨7650125, by rfl⟩ : syracuseStep 10200167 = 15300251) B15300251
theorem B894287 : Blo 595291 894287 := bstep (se 1 (by rfl) ⟨670715, by rfl⟩ : syracuseStep 894287 = 1341431) B1341431
theorem B2860687 : Blo 595291 2860687 := bstep (se 1 (by rfl) ⟨2145515, by rfl⟩ : syracuseStep 2860687 = 4291031) B4291031
theorem B23209901 : Blo 595291 23209901 := bstep (se 3 (by rfl) ⟨4351856, by rfl⟩ : syracuseStep 23209901 = 8703713) B8703713
theorem B13805923 : Blo 595291 13805923 := bstep (se 1 (by rfl) ⟨10354442, by rfl⟩ : syracuseStep 13805923 = 20708885) B20708885
theorem B6466391 : Blo 595291 6466391 := bstep (se 1 (by rfl) ⟨4849793, by rfl⟩ : syracuseStep 6466391 = 9699587) B9699587
theorem B895847 : Blo 595291 895847 := bstep (se 1 (by rfl) ⟨671885, by rfl⟩ : syracuseStep 895847 = 1343771) B1343771
theorem B895865 : Blo 595291 895865 := bstep (se 2 (by rfl) ⟨335949, by rfl⟩ : syracuseStep 895865 = 671899) B671899
theorem B895871 : Blo 595291 895871 := bstep (se 1 (by rfl) ⟨671903, by rfl⟩ : syracuseStep 895871 = 1343807) B1343807
theorem B896159 : Blo 595291 896159 := bstep (se 1 (by rfl) ⟨672119, by rfl⟩ : syracuseStep 896159 = 1344239) B1344239
theorem B4304411 : Blo 595291 4304411 := bstep (se 1 (by rfl) ⟨3228308, by rfl⟩ : syracuseStep 4304411 = 6456617) B6456617
theorem B2863457 : Blo 595291 2863457 := bstep (se 2 (by rfl) ⟨1073796, by rfl⟩ : syracuseStep 2863457 = 2147593) B2147593
theorem B2045063 : Blo 595291 2045063 := bstep (se 1 (by rfl) ⟨1533797, by rfl⟩ : syracuseStep 2045063 = 3067595) B3067595
theorem B898331 : Blo 595291 898331 := bstep (se 1 (by rfl) ⟨673748, by rfl⟩ : syracuseStep 898331 = 1347497) B1347497
theorem B898607 : Blo 595291 898607 := bstep (se 1 (by rfl) ⟨673955, by rfl⟩ : syracuseStep 898607 = 1347911) B1347911
theorem B671359 : Blo 595291 671359 := bstep (se 1 (by rfl) ⟨503519, by rfl⟩ : syracuseStep 671359 = 1007039) B1007039
theorem B3032315 : Blo 595291 3032315 := bstep (se 1 (by rfl) ⟨2274236, by rfl⟩ : syracuseStep 3032315 = 4548473) B4548473
theorem B3392927 : Blo 595291 3392927 := bstep (se 1 (by rfl) ⟨2544695, by rfl⟩ : syracuseStep 3392927 = 5089391) B5089391
theorem B3229631 : Blo 595291 3229631 := bstep (se 1 (by rfl) ⟨2422223, by rfl⟩ : syracuseStep 3229631 = 4844447) B4844447
theorem B2872027 : Blo 595291 2872027 := bstep (se 1 (by rfl) ⟨2154020, by rfl⟩ : syracuseStep 2872027 = 4308041) B4308041
theorem B2151137 : Blo 595291 2151137 := bstep (se 2 (by rfl) ⟨806676, by rfl⟩ : syracuseStep 2151137 = 1613353) B1613353
theorem B3888059 : Blo 595291 3888059 := bstep (se 1 (by rfl) ⟨2916044, by rfl⟩ : syracuseStep 3888059 = 5832089) B5832089
theorem B7659967 : Blo 595291 7659967 := bstep (se 1 (by rfl) ⟨5744975, by rfl⟩ : syracuseStep 7659967 = 11489951) B11489951
theorem B55240339 : Blo 595291 55240339 := bstep (se 1 (by rfl) ⟨41430254, by rfl⟩ : syracuseStep 55240339 = 82860509) B82860509
theorem B22407455 : Blo 595291 22407455 := bstep (se 1 (by rfl) ⟨16805591, by rfl⟩ : syracuseStep 22407455 = 33611183) B33611183
theorem B14707241 : Blo 595291 14707241 := bstep (se 2 (by rfl) ⟨5515215, by rfl⟩ : syracuseStep 14707241 = 11030431) B11030431
theorem B7008767 : Blo 595291 7008767 := bstep (se 1 (by rfl) ⟨5256575, by rfl⟩ : syracuseStep 7008767 = 10513151) B10513151
theorem B8189495 : Blo 595291 8189495 := bstep (se 1 (by rfl) ⟨6142121, by rfl⟩ : syracuseStep 8189495 = 12284243) B12284243
theorem B3832703 : Blo 595291 3832703 := bstep (se 1 (by rfl) ⟨2874527, by rfl⟩ : syracuseStep 3832703 = 5749055) B5749055
theorem B2261951 : Blo 595291 2261951 := bstep (se 1 (by rfl) ⟨1696463, by rfl⟩ : syracuseStep 2261951 = 3392927) B3392927
theorem B5736365 : Blo 595291 5736365 := bstep (se 3 (by rfl) ⟨1075568, by rfl⟩ : syracuseStep 5736365 = 2151137) B2151137
theorem B595711 : Blo 595291 595711 := bstep (se 1 (by rfl) ⟨446783, by rfl⟩ : syracuseStep 595711 = 893567) B893567
theorem B595935 : Blo 595291 595935 := bstep (se 1 (by rfl) ⟨446951, by rfl⟩ : syracuseStep 595935 = 893903) B893903
theorem B596191 : Blo 595291 596191 := bstep (se 1 (by rfl) ⟨447143, by rfl⟩ : syracuseStep 596191 = 894287) B894287
theorem B15473267 : Blo 595291 15473267 := bstep (se 1 (by rfl) ⟨11604950, by rfl⟩ : syracuseStep 15473267 = 23209901) B23209901
theorem B9804827 : Blo 595291 9804827 := bstep (se 1 (by rfl) ⟨7353620, by rfl⟩ : syracuseStep 9804827 = 14707241) B14707241
theorem B597231 : Blo 595291 597231 := bstep (se 1 (by rfl) ⟨447923, by rfl⟩ : syracuseStep 597231 = 895847) B895847
theorem B597243 : Blo 595291 597243 := bstep (se 1 (by rfl) ⟨447932, by rfl⟩ : syracuseStep 597243 = 895865) B895865
theorem B597247 : Blo 595291 597247 := bstep (se 1 (by rfl) ⟨447935, by rfl⟩ : syracuseStep 597247 = 895871) B895871
theorem B597439 : Blo 595291 597439 := bstep (se 1 (by rfl) ⟨448079, by rfl⟩ : syracuseStep 597439 = 896159) B896159
theorem B1908971 : Blo 595291 1908971 := bstep (se 1 (by rfl) ⟨1431728, by rfl⟩ : syracuseStep 1908971 = 2863457) B2863457
theorem B598887 : Blo 595291 598887 := bstep (se 1 (by rfl) ⟨449165, by rfl⟩ : syracuseStep 598887 = 898331) B898331
theorem B599071 : Blo 595291 599071 := bstep (se 1 (by rfl) ⟨449303, by rfl⟩ : syracuseStep 599071 = 898607) B898607
theorem B895145 : Blo 595291 895145 := bstep (se 2 (by rfl) ⟨335679, by rfl⟩ : syracuseStep 895145 = 671359) B671359
theorem B16395529 : Blo 595291 16395529 := bstep (se 2 (by rfl) ⟨6148323, by rfl⟩ : syracuseStep 16395529 = 12296647) B12296647
theorem B1093753 : Blo 595291 1093753 := bstep (se 2 (by rfl) ⟨410157, by rfl⟩ : syracuseStep 1093753 = 820315) B820315
theorem B2273615 : Blo 595291 2273615 := bstep (se 1 (by rfl) ⟨1705211, by rfl⟩ : syracuseStep 2273615 = 3410423) B3410423
theorem B3814249 : Blo 595291 3814249 := bstep (se 2 (by rfl) ⟨1430343, by rfl⟩ : syracuseStep 3814249 = 2860687) B2860687
theorem B898079 : Blo 595291 898079 := bstep (se 1 (by rfl) ⟨673559, by rfl⟩ : syracuseStep 898079 = 1347119) B1347119
theorem B898151 : Blo 595291 898151 := bstep (se 1 (by rfl) ⟨673613, by rfl⟩ : syracuseStep 898151 = 1347227) B1347227
theorem B10368157 : Blo 595291 10368157 := bstep (se 3 (by rfl) ⟨1944029, by rfl⟩ : syracuseStep 10368157 = 3888059) B3888059
theorem B2865107 : Blo 595291 2865107 := bstep (se 1 (by rfl) ⟨2148830, by rfl⟩ : syracuseStep 2865107 = 4297661) B4297661
theorem B6800111 : Blo 595291 6800111 := bstep (se 1 (by rfl) ⟨5100083, by rfl⟩ : syracuseStep 6800111 = 10200167) B10200167
theorem B59753213 : Blo 595291 59753213 := bstep (se 3 (by rfl) ⟨11203727, by rfl⟩ : syracuseStep 59753213 = 22407455) B22407455
theorem B4310927 : Blo 595291 4310927 := bstep (se 1 (by rfl) ⟨3233195, by rfl⟩ : syracuseStep 4310927 = 6466391) B6466391
theorem B2869607 : Blo 595291 2869607 := bstep (se 1 (by rfl) ⟨2152205, by rfl⟩ : syracuseStep 2869607 = 4304411) B4304411
theorem B4672511 : Blo 595291 4672511 := bstep (se 1 (by rfl) ⟨3504383, by rfl⟩ : syracuseStep 4672511 = 7008767) B7008767
theorem B1363375 : Blo 595291 1363375 := bstep (se 1 (by rfl) ⟨1022531, by rfl⟩ : syracuseStep 1363375 = 2045063) B2045063
theorem B5459663 : Blo 595291 5459663 := bstep (se 1 (by rfl) ⟨4094747, by rfl⟩ : syracuseStep 5459663 = 8189495) B8189495
theorem B10213289 : Blo 595291 10213289 := bstep (se 2 (by rfl) ⟨3829983, by rfl⟩ : syracuseStep 10213289 = 7659967) B7659967
theorem B2021543 : Blo 595291 2021543 := bstep (se 1 (by rfl) ⟨1516157, by rfl⟩ : syracuseStep 2021543 = 3032315) B3032315
theorem B2153087 : Blo 595291 2153087 := bstep (se 1 (by rfl) ⟨1614815, by rfl⟩ : syracuseStep 2153087 = 3229631) B3229631
theorem B73653785 : Blo 595291 73653785 := bstep (se 2 (by rfl) ⟨27620169, by rfl⟩ : syracuseStep 73653785 = 55240339) B55240339
theorem B18407897 : Blo 595291 18407897 := bstep (se 2 (by rfl) ⟨6902961, by rfl⟩ : syracuseStep 18407897 = 13805923) B13805923
theorem B1010407 : Blo 595291 1010407 := bstep (se 1 (by rfl) ⟨757805, by rfl⟩ : syracuseStep 1010407 = 1515611) B1515611
theorem B3829369 : Blo 595291 3829369 := bstep (se 2 (by rfl) ⟨1436013, by rfl⟩ : syracuseStep 3829369 = 2872027) B2872027
theorem B2555135 : Blo 595291 2555135 := bstep (se 1 (by rfl) ⟨1916351, by rfl⟩ : syracuseStep 2555135 = 3832703) B3832703
theorem B1507967 : Blo 595291 1507967 := bstep (se 1 (by rfl) ⟨1130975, by rfl⟩ : syracuseStep 1507967 = 2261951) B2261951
theorem B3115007 : Blo 595291 3115007 := bstep (se 1 (by rfl) ⟨2336255, by rfl⟩ : syracuseStep 3115007 = 4672511) B4672511
theorem B1347209 : Blo 595291 1347209 := bstep (se 2 (by rfl) ⟨505203, by rfl⟩ : syracuseStep 1347209 = 1010407) B1010407
theorem B1347695 : Blo 595291 1347695 := bstep (se 1 (by rfl) ⟨1010771, by rfl⟩ : syracuseStep 1347695 = 2021543) B2021543
theorem B21860705 : Blo 595291 21860705 := bstep (se 2 (by rfl) ⟨8197764, by rfl⟩ : syracuseStep 21860705 = 16395529) B16395529
theorem B5085665 : Blo 595291 5085665 := bstep (se 2 (by rfl) ⟨1907124, by rfl⟩ : syracuseStep 5085665 = 3814249) B3814249
theorem B596763 : Blo 595291 596763 := bstep (se 1 (by rfl) ⟨447572, by rfl⟩ : syracuseStep 596763 = 895145) B895145
theorem B1515743 : Blo 595291 1515743 := bstep (se 1 (by rfl) ⟨1136807, by rfl⟩ : syracuseStep 1515743 = 2273615) B2273615
theorem B598719 : Blo 595291 598719 := bstep (se 1 (by rfl) ⟨449039, by rfl⟩ : syracuseStep 598719 = 898079) B898079
theorem B598767 : Blo 595291 598767 := bstep (se 1 (by rfl) ⟨449075, by rfl⟩ : syracuseStep 598767 = 898151) B898151
theorem B1910071 : Blo 595291 1910071 := bstep (se 1 (by rfl) ⟨1432553, by rfl⟩ : syracuseStep 1910071 = 2865107) B2865107
theorem B14559101 : Blo 595291 14559101 := bstep (se 3 (by rfl) ⟨2729831, by rfl⟩ : syracuseStep 14559101 = 5459663) B5459663
theorem B4533407 : Blo 595291 4533407 := bstep (se 1 (by rfl) ⟨3400055, by rfl⟩ : syracuseStep 4533407 = 6800111) B6800111
theorem B1913071 : Blo 595291 1913071 := bstep (se 1 (by rfl) ⟨1434803, by rfl⟩ : syracuseStep 1913071 = 2869607) B2869607
theorem B1817833 : Blo 595291 1817833 := bstep (se 2 (by rfl) ⟨681687, by rfl⟩ : syracuseStep 1817833 = 1363375) B1363375
theorem B6536551 : Blo 595291 6536551 := bstep (se 1 (by rfl) ⟨4902413, by rfl⟩ : syracuseStep 6536551 = 9804827) B9804827
theorem B49102523 : Blo 595291 49102523 := bstep (se 1 (by rfl) ⟨36826892, by rfl⟩ : syracuseStep 49102523 = 73653785) B73653785
theorem B1458337 : Blo 595291 1458337 := bstep (se 2 (by rfl) ⟨546876, by rfl⟩ : syracuseStep 1458337 = 1093753) B1093753
theorem B12271931 : Blo 595291 12271931 := bstep (se 1 (by rfl) ⟨9203948, by rfl⟩ : syracuseStep 12271931 = 18407897) B18407897
theorem B39835475 : Blo 595291 39835475 := bstep (se 1 (by rfl) ⟨29876606, by rfl⟩ : syracuseStep 39835475 = 59753213) B59753213
theorem B2873951 : Blo 595291 2873951 := bstep (se 1 (by rfl) ⟨2155463, by rfl⟩ : syracuseStep 2873951 = 4310927) B4310927
theorem B3824243 : Blo 595291 3824243 := bstep (se 1 (by rfl) ⟨2868182, by rfl⟩ : syracuseStep 3824243 = 5736365) B5736365
theorem B6808859 : Blo 595291 6808859 := bstep (se 1 (by rfl) ⟨5106644, by rfl⟩ : syracuseStep 6808859 = 10213289) B10213289
theorem B10315511 : Blo 595291 10315511 := bstep (se 1 (by rfl) ⟨7736633, by rfl⟩ : syracuseStep 10315511 = 15473267) B15473267
theorem B1435391 : Blo 595291 1435391 := bstep (se 1 (by rfl) ⟨1076543, by rfl⟩ : syracuseStep 1435391 = 2153087) B2153087
theorem B5105825 : Blo 595291 5105825 := bstep (se 2 (by rfl) ⟨1914684, by rfl⟩ : syracuseStep 5105825 = 3829369) B3829369
theorem B1272647 : Blo 595291 1272647 := bstep (se 1 (by rfl) ⟨954485, by rfl⟩ : syracuseStep 1272647 = 1908971) B1908971
theorem B13824209 : Blo 595291 13824209 := bstep (se 2 (by rfl) ⟨5184078, by rfl⟩ : syracuseStep 13824209 = 10368157) B10368157
theorem B1703423 : Blo 595291 1703423 := bstep (se 1 (by rfl) ⟨1277567, by rfl⟩ : syracuseStep 1703423 = 2555135) B2555135
theorem B956927 : Blo 595291 956927 := bstep (se 1 (by rfl) ⟨717695, by rfl⟩ : syracuseStep 956927 = 1435391) B1435391
theorem B9706067 : Blo 595291 9706067 := bstep (se 1 (by rfl) ⟨7279550, by rfl⟩ : syracuseStep 9706067 = 14559101) B14559101
theorem B3022271 : Blo 595291 3022271 := bstep (se 1 (by rfl) ⟨2266703, by rfl⟩ : syracuseStep 3022271 = 4533407) B4533407
theorem B9216139 : Blo 595291 9216139 := bstep (se 1 (by rfl) ⟨6912104, by rfl⟩ : syracuseStep 9216139 = 13824209) B13824209
theorem B1944449 : Blo 595291 1944449 := bstep (se 2 (by rfl) ⟨729168, by rfl⟩ : syracuseStep 1944449 = 1458337) B1458337
theorem B2076671 : Blo 595291 2076671 := bstep (se 1 (by rfl) ⟨1557503, by rfl⟩ : syracuseStep 2076671 = 3115007) B3115007
theorem B898139 : Blo 595291 898139 := bstep (se 1 (by rfl) ⟨673604, by rfl⟩ : syracuseStep 898139 = 1347209) B1347209
theorem B898463 : Blo 595291 898463 := bstep (se 1 (by rfl) ⟨673847, by rfl⟩ : syracuseStep 898463 = 1347695) B1347695
theorem B26556983 : Blo 595291 26556983 := bstep (se 1 (by rfl) ⟨19917737, by rfl⟩ : syracuseStep 26556983 = 39835475) B39835475
theorem B3390443 : Blo 595291 3390443 := bstep (se 1 (by rfl) ⟨2542832, by rfl⟩ : syracuseStep 3390443 = 5085665) B5085665
theorem B1915967 : Blo 595291 1915967 := bstep (se 1 (by rfl) ⟨1436975, by rfl⟩ : syracuseStep 1915967 = 2873951) B2873951
theorem B4539239 : Blo 595291 4539239 := bstep (se 1 (by rfl) ⟨3404429, by rfl⟩ : syracuseStep 4539239 = 6808859) B6808859
theorem B1135615 : Blo 595291 1135615 := bstep (se 1 (by rfl) ⟨851711, by rfl⟩ : syracuseStep 1135615 = 1703423) B1703423
theorem B8181287 : Blo 595291 8181287 := bstep (se 1 (by rfl) ⟨6135965, by rfl⟩ : syracuseStep 8181287 = 12271931) B12271931
theorem B1005311 : Blo 595291 1005311 := bstep (se 1 (by rfl) ⟨753983, by rfl⟩ : syracuseStep 1005311 = 1507967) B1507967
theorem B14573803 : Blo 595291 14573803 := bstep (se 1 (by rfl) ⟨10930352, by rfl⟩ : syracuseStep 14573803 = 21860705) B21860705
theorem B2549495 : Blo 595291 2549495 := bstep (se 1 (by rfl) ⟨1912121, by rfl⟩ : syracuseStep 2549495 = 3824243) B3824243
theorem B1010495 : Blo 595291 1010495 := bstep (se 1 (by rfl) ⟨757871, by rfl⟩ : syracuseStep 1010495 = 1515743) B1515743
theorem B2550761 : Blo 595291 2550761 := bstep (se 2 (by rfl) ⟨956535, by rfl⟩ : syracuseStep 2550761 = 1913071) B1913071
theorem B6877007 : Blo 595291 6877007 := bstep (se 1 (by rfl) ⟨5157755, by rfl⟩ : syracuseStep 6877007 = 10315511) B10315511
theorem B3403883 : Blo 595291 3403883 := bstep (se 1 (by rfl) ⟨2552912, by rfl⟩ : syracuseStep 3403883 = 5105825) B5105825
theorem B10187045 : Blo 595291 10187045 := bstep (se 4 (by rfl) ⟨955035, by rfl⟩ : syracuseStep 10187045 = 1910071) B1910071
theorem B848431 : Blo 595291 848431 := bstep (se 1 (by rfl) ⟨636323, by rfl⟩ : syracuseStep 848431 = 1272647) B1272647
theorem B2423777 : Blo 595291 2423777 := bstep (se 2 (by rfl) ⟨908916, by rfl⟩ : syracuseStep 2423777 = 1817833) B1817833
theorem B8715401 : Blo 595291 8715401 := bstep (se 2 (by rfl) ⟨3268275, by rfl⟩ : syracuseStep 8715401 = 6536551) B6536551
theorem B32735015 : Blo 595291 32735015 := bstep (se 1 (by rfl) ⟨24551261, by rfl⟩ : syracuseStep 32735015 = 49102523) B49102523
theorem B12288185 : Blo 595291 12288185 := bstep (se 2 (by rfl) ⟨4608069, by rfl⟩ : syracuseStep 12288185 = 9216139) B9216139
theorem B19431737 : Blo 595291 19431737 := bstep (se 2 (by rfl) ⟨7286901, by rfl⟩ : syracuseStep 19431737 = 14573803) B14573803
theorem B1514153 : Blo 595291 1514153 := bstep (se 2 (by rfl) ⟨567807, by rfl⟩ : syracuseStep 1514153 = 1135615) B1135615
theorem B6463405 : Blo 595291 6463405 := bstep (se 3 (by rfl) ⟨1211888, by rfl⟩ : syracuseStep 6463405 = 2423777) B2423777
theorem B1384447 : Blo 595291 1384447 := bstep (se 1 (by rfl) ⟨1038335, by rfl⟩ : syracuseStep 1384447 = 2076671) B2076671
theorem B2269255 : Blo 595291 2269255 := bstep (se 1 (by rfl) ⟨1701941, by rfl⟩ : syracuseStep 2269255 = 3403883) B3403883
theorem B6791363 : Blo 595291 6791363 := bstep (se 1 (by rfl) ⟨5093522, by rfl⟩ : syracuseStep 6791363 = 10187045) B10187045
theorem B598759 : Blo 595291 598759 := bstep (se 1 (by rfl) ⟨449069, by rfl⟩ : syracuseStep 598759 = 898139) B898139
theorem B598975 : Blo 595291 598975 := bstep (se 1 (by rfl) ⟨449231, by rfl⟩ : syracuseStep 598975 = 898463) B898463
theorem B17704655 : Blo 595291 17704655 := bstep (se 1 (by rfl) ⟨13278491, by rfl⟩ : syracuseStep 17704655 = 26556983) B26556983
theorem B5810267 : Blo 595291 5810267 := bstep (se 1 (by rfl) ⟨4357700, by rfl⟩ : syracuseStep 5810267 = 8715401) B8715401
theorem B3026159 : Blo 595291 3026159 := bstep (se 1 (by rfl) ⟨2269619, by rfl⟩ : syracuseStep 3026159 = 4539239) B4539239
theorem B5454191 : Blo 595291 5454191 := bstep (se 1 (by rfl) ⟨4090643, by rfl⟩ : syracuseStep 5454191 = 8181287) B8181287
theorem B670207 : Blo 595291 670207 := bstep (se 1 (by rfl) ⟨502655, by rfl⟩ : syracuseStep 670207 = 1005311) B1005311
theorem B637951 : Blo 595291 637951 := bstep (se 1 (by rfl) ⟨478463, by rfl⟩ : syracuseStep 637951 = 956927) B956927
theorem B6470711 : Blo 595291 6470711 := bstep (se 1 (by rfl) ⟨4853033, by rfl⟩ : syracuseStep 6470711 = 9706067) B9706067
theorem B6798653 : Blo 595291 6798653 := bstep (se 3 (by rfl) ⟨1274747, by rfl⟩ : syracuseStep 6798653 = 2549495) B2549495
theorem B2014847 : Blo 595291 2014847 := bstep (se 1 (by rfl) ⟨1511135, by rfl⟩ : syracuseStep 2014847 = 3022271) B3022271
theorem B1131241 : Blo 595291 1131241 := bstep (se 2 (by rfl) ⟨424215, by rfl⟩ : syracuseStep 1131241 = 848431) B848431
theorem B673663 : Blo 595291 673663 := bstep (se 1 (by rfl) ⟨505247, by rfl⟩ : syracuseStep 673663 = 1010495) B1010495
theorem B1296299 : Blo 595291 1296299 := bstep (se 1 (by rfl) ⟨972224, by rfl⟩ : syracuseStep 1296299 = 1944449) B1944449
theorem B1700507 : Blo 595291 1700507 := bstep (se 1 (by rfl) ⟨1275380, by rfl⟩ : syracuseStep 1700507 = 2550761) B2550761
theorem B4584671 : Blo 595291 4584671 := bstep (se 1 (by rfl) ⟨3438503, by rfl⟩ : syracuseStep 4584671 = 6877007) B6877007
theorem B2260295 : Blo 595291 2260295 := bstep (se 1 (by rfl) ⟨1695221, by rfl⟩ : syracuseStep 2260295 = 3390443) B3390443
theorem B1277311 : Blo 595291 1277311 := bstep (se 1 (by rfl) ⟨957983, by rfl⟩ : syracuseStep 1277311 = 1915967) B1915967
theorem B21823343 : Blo 595291 21823343 := bstep (se 1 (by rfl) ⟨16367507, by rfl⟩ : syracuseStep 21823343 = 32735015) B32735015
theorem B8192123 : Blo 595291 8192123 := bstep (se 1 (by rfl) ⟨6144092, by rfl⟩ : syracuseStep 8192123 = 12288185) B12288185
theorem B1508321 : Blo 595291 1508321 := bstep (se 2 (by rfl) ⟨565620, by rfl⟩ : syracuseStep 1508321 = 1131241) B1131241
theorem B4527575 : Blo 595291 4527575 := bstep (se 1 (by rfl) ⟨3395681, by rfl⟩ : syracuseStep 4527575 = 6791363) B6791363
theorem B11803103 : Blo 595291 11803103 := bstep (se 1 (by rfl) ⟨8852327, by rfl⟩ : syracuseStep 11803103 = 17704655) B17704655
theorem B3873511 : Blo 595291 3873511 := bstep (se 1 (by rfl) ⟨2905133, by rfl⟩ : syracuseStep 3873511 = 5810267) B5810267
theorem B893609 : Blo 595291 893609 := bstep (se 2 (by rfl) ⟨335103, by rfl⟩ : syracuseStep 893609 = 670207) B670207
theorem B3056447 : Blo 595291 3056447 := bstep (se 1 (by rfl) ⟨2292335, by rfl⟩ : syracuseStep 3056447 = 4584671) B4584671
theorem B4532435 : Blo 595291 4532435 := bstep (se 1 (by rfl) ⟨3399326, by rfl⟩ : syracuseStep 4532435 = 6798653) B6798653
theorem B1845929 : Blo 595291 1845929 := bstep (se 2 (by rfl) ⟨692223, by rfl⟩ : syracuseStep 1845929 = 1384447) B1384447
theorem B3025673 : Blo 595291 3025673 := bstep (se 2 (by rfl) ⟨1134627, by rfl⟩ : syracuseStep 3025673 = 2269255) B2269255
theorem B12954491 : Blo 595291 12954491 := bstep (se 1 (by rfl) ⟨9715868, by rfl⟩ : syracuseStep 12954491 = 19431737) B19431737
theorem B864199 : Blo 595291 864199 := bstep (se 1 (by rfl) ⟨648149, by rfl⟩ : syracuseStep 864199 = 1296299) B1296299
theorem B898217 : Blo 595291 898217 := bstep (se 2 (by rfl) ⟨336831, by rfl⟩ : syracuseStep 898217 = 673663) B673663
theorem B2017439 : Blo 595291 2017439 := bstep (se 1 (by rfl) ⟨1513079, by rfl⟩ : syracuseStep 2017439 = 3026159) B3026159
theorem B1133671 : Blo 595291 1133671 := bstep (se 1 (by rfl) ⟨850253, by rfl⟩ : syracuseStep 1133671 = 1700507) B1700507
theorem B4313807 : Blo 595291 4313807 := bstep (se 1 (by rfl) ⟨3235355, by rfl⟩ : syracuseStep 4313807 = 6470711) B6470711
theorem B1009435 : Blo 595291 1009435 := bstep (se 1 (by rfl) ⟨757076, by rfl⟩ : syracuseStep 1009435 = 1514153) B1514153
theorem B850601 : Blo 595291 850601 := bstep (se 2 (by rfl) ⟨318975, by rfl⟩ : syracuseStep 850601 = 637951) B637951
theorem B3636127 : Blo 595291 3636127 := bstep (se 1 (by rfl) ⟨2727095, by rfl⟩ : syracuseStep 3636127 = 5454191) B5454191
theorem B1703081 : Blo 595291 1703081 := bstep (se 2 (by rfl) ⟨638655, by rfl⟩ : syracuseStep 1703081 = 1277311) B1277311
theorem B1506863 : Blo 595291 1506863 := bstep (se 1 (by rfl) ⟨1130147, by rfl⟩ : syracuseStep 1506863 = 2260295) B2260295
theorem B1343231 : Blo 595291 1343231 := bstep (se 1 (by rfl) ⟨1007423, by rfl⟩ : syracuseStep 1343231 = 2014847) B2014847
theorem B8617873 : Blo 595291 8617873 := bstep (se 2 (by rfl) ⟨3231702, by rfl⟩ : syracuseStep 8617873 = 6463405) B6463405
theorem B14548895 : Blo 595291 14548895 := bstep (se 1 (by rfl) ⟨10911671, by rfl⟩ : syracuseStep 14548895 = 21823343) B21823343
theorem B1344959 : Blo 595291 1344959 := bstep (se 1 (by rfl) ⟨1008719, by rfl⟩ : syracuseStep 1344959 = 2017439) B2017439
theorem B1345913 : Blo 595291 1345913 := bstep (se 2 (by rfl) ⟨504717, by rfl⟩ : syracuseStep 1345913 = 1009435) B1009435
theorem B3018383 : Blo 595291 3018383 := bstep (se 1 (by rfl) ⟨2263787, by rfl⟩ : syracuseStep 3018383 = 4527575) B4527575
theorem B1511561 : Blo 595291 1511561 := bstep (se 2 (by rfl) ⟨566835, by rfl⟩ : syracuseStep 1511561 = 1133671) B1133671
theorem B7868735 : Blo 595291 7868735 := bstep (se 1 (by rfl) ⟨5901551, by rfl⟩ : syracuseStep 7868735 = 11803103) B11803103
theorem B1152265 : Blo 595291 1152265 := bstep (se 2 (by rfl) ⟨432099, by rfl⟩ : syracuseStep 1152265 = 864199) B864199
theorem B595739 : Blo 595291 595739 := bstep (se 1 (by rfl) ⟨446804, by rfl⟩ : syracuseStep 595739 = 893609) B893609
theorem B2037631 : Blo 595291 2037631 := bstep (se 1 (by rfl) ⟨1528223, by rfl⟩ : syracuseStep 2037631 = 3056447) B3056447
theorem B3021623 : Blo 595291 3021623 := bstep (se 1 (by rfl) ⟨2266217, by rfl⟩ : syracuseStep 3021623 = 4532435) B4532435
theorem B2268269 : Blo 595291 2268269 := bstep (se 3 (by rfl) ⟨425300, by rfl⟩ : syracuseStep 2268269 = 850601) B850601
theorem B4922477 : Blo 595291 4922477 := bstep (se 3 (by rfl) ⟨922964, by rfl⟩ : syracuseStep 4922477 = 1845929) B1845929
theorem B598811 : Blo 595291 598811 := bstep (se 1 (by rfl) ⟨449108, by rfl⟩ : syracuseStep 598811 = 898217) B898217
theorem B895487 : Blo 595291 895487 := bstep (se 1 (by rfl) ⟨671615, by rfl⟩ : syracuseStep 895487 = 1343231) B1343231
theorem B2017115 : Blo 595291 2017115 := bstep (se 1 (by rfl) ⟨1512836, by rfl⟩ : syracuseStep 2017115 = 3025673) B3025673
theorem B8636327 : Blo 595291 8636327 := bstep (se 1 (by rfl) ⟨6477245, by rfl⟩ : syracuseStep 8636327 = 12954491) B12954491
theorem B5164681 : Blo 595291 5164681 := bstep (se 2 (by rfl) ⟨1936755, by rfl⟩ : syracuseStep 5164681 = 3873511) B3873511
theorem B1135387 : Blo 595291 1135387 := bstep (se 1 (by rfl) ⟨851540, by rfl⟩ : syracuseStep 1135387 = 1703081) B1703081
theorem B1004575 : Blo 595291 1004575 := bstep (se 1 (by rfl) ⟨753431, by rfl⟩ : syracuseStep 1004575 = 1506863) B1506863
theorem B11490497 : Blo 595291 11490497 := bstep (se 2 (by rfl) ⟨4308936, by rfl⟩ : syracuseStep 11490497 = 8617873) B8617873
theorem B5461415 : Blo 595291 5461415 := bstep (se 1 (by rfl) ⟨4096061, by rfl⟩ : syracuseStep 5461415 = 8192123) B8192123
theorem B1005547 : Blo 595291 1005547 := bstep (se 1 (by rfl) ⟨754160, by rfl⟩ : syracuseStep 1005547 = 1508321) B1508321
theorem B2875871 : Blo 595291 2875871 := bstep (se 1 (by rfl) ⟨2156903, by rfl⟩ : syracuseStep 2875871 = 4313807) B4313807
theorem B4848169 : Blo 595291 4848169 := bstep (se 2 (by rfl) ⟨1818063, by rfl⟩ : syracuseStep 4848169 = 3636127) B3636127
theorem B9699263 : Blo 595291 9699263 := bstep (se 1 (by rfl) ⟨7274447, by rfl⟩ : syracuseStep 9699263 = 14548895) B14548895
theorem B1344743 : Blo 595291 1344743 := bstep (se 1 (by rfl) ⟨1008557, by rfl⟩ : syracuseStep 1344743 = 2017115) B2017115
theorem B7668989 : Blo 595291 7668989 := bstep (se 3 (by rfl) ⟨1437935, by rfl⟩ : syracuseStep 7668989 = 2875871) B2875871
theorem B5245823 : Blo 595291 5245823 := bstep (se 1 (by rfl) ⟨3934367, by rfl⟩ : syracuseStep 5245823 = 7868735) B7868735
theorem B3640943 : Blo 595291 3640943 := bstep (se 1 (by rfl) ⟨2730707, by rfl⟩ : syracuseStep 3640943 = 5461415) B5461415
theorem B1512179 : Blo 595291 1512179 := bstep (se 1 (by rfl) ⟨1134134, by rfl⟩ : syracuseStep 1512179 = 2268269) B2268269
theorem B3281651 : Blo 595291 3281651 := bstep (se 1 (by rfl) ⟨2461238, by rfl⟩ : syracuseStep 3281651 = 4922477) B4922477
theorem B6886241 : Blo 595291 6886241 := bstep (se 2 (by rfl) ⟨2582340, by rfl⟩ : syracuseStep 6886241 = 5164681) B5164681
theorem B1513849 : Blo 595291 1513849 := bstep (se 2 (by rfl) ⟨567693, by rfl⟩ : syracuseStep 1513849 = 1135387) B1135387
theorem B596991 : Blo 595291 596991 := bstep (se 1 (by rfl) ⟨447743, by rfl⟩ : syracuseStep 596991 = 895487) B895487
theorem B6464225 : Blo 595291 6464225 := bstep (se 2 (by rfl) ⟨2424084, by rfl⟩ : syracuseStep 6464225 = 4848169) B4848169
theorem B6466175 : Blo 595291 6466175 := bstep (se 1 (by rfl) ⟨4849631, by rfl⟩ : syracuseStep 6466175 = 9699263) B9699263
theorem B896639 : Blo 595291 896639 := bstep (se 1 (by rfl) ⟨672479, by rfl⟩ : syracuseStep 896639 = 1344959) B1344959
theorem B897275 : Blo 595291 897275 := bstep (se 1 (by rfl) ⟨672956, by rfl⟩ : syracuseStep 897275 = 1345913) B1345913
theorem B2012255 : Blo 595291 2012255 := bstep (se 1 (by rfl) ⟨1509191, by rfl⟩ : syracuseStep 2012255 = 3018383) B3018383
theorem B2014415 : Blo 595291 2014415 := bstep (se 1 (by rfl) ⟨1510811, by rfl⟩ : syracuseStep 2014415 = 3021623) B3021623
theorem B5757551 : Blo 595291 5757551 := bstep (se 1 (by rfl) ⟨4318163, by rfl⟩ : syracuseStep 5757551 = 8636327) B8636327
theorem B1007707 : Blo 595291 1007707 := bstep (se 1 (by rfl) ⟨755780, by rfl⟩ : syracuseStep 1007707 = 1511561) B1511561
theorem B7660331 : Blo 595291 7660331 := bstep (se 1 (by rfl) ⟨5745248, by rfl⟩ : syracuseStep 7660331 = 11490497) B11490497
theorem B1339433 : Blo 595291 1339433 := bstep (se 2 (by rfl) ⟨502287, by rfl⟩ : syracuseStep 1339433 = 1004575) B1004575
theorem B1536353 : Blo 595291 1536353 := bstep (se 2 (by rfl) ⟨576132, by rfl⟩ : syracuseStep 1536353 = 1152265) B1152265
theorem B2716841 : Blo 595291 2716841 := bstep (se 2 (by rfl) ⟨1018815, by rfl⟩ : syracuseStep 2716841 = 2037631) B2037631
theorem B1340729 : Blo 595291 1340729 := bstep (se 2 (by rfl) ⟨502773, by rfl⟩ : syracuseStep 1340729 = 1005547) B1005547
theorem B1343609 : Blo 595291 1343609 := bstep (se 2 (by rfl) ⟨503853, by rfl⟩ : syracuseStep 1343609 = 1007707) B1007707
theorem B5112659 : Blo 595291 5112659 := bstep (se 1 (by rfl) ⟨3834494, by rfl⟩ : syracuseStep 5112659 = 7668989) B7668989
theorem B17237933 : Blo 595291 17237933 := bstep (se 3 (by rfl) ⟨3232112, by rfl⟩ : syracuseStep 17237933 = 6464225) B6464225
theorem B2427295 : Blo 595291 2427295 := bstep (se 1 (by rfl) ⟨1820471, by rfl⟩ : syracuseStep 2427295 = 3640943) B3640943
theorem B7244909 : Blo 595291 7244909 := bstep (se 3 (by rfl) ⟨1358420, by rfl⟩ : syracuseStep 7244909 = 2716841) B2716841
theorem B4590827 : Blo 595291 4590827 := bstep (se 1 (by rfl) ⟨3443120, by rfl⟩ : syracuseStep 4590827 = 6886241) B6886241
theorem B3838367 : Blo 595291 3838367 := bstep (se 1 (by rfl) ⟨2878775, by rfl⟩ : syracuseStep 3838367 = 5757551) B5757551
theorem B597759 : Blo 595291 597759 := bstep (se 1 (by rfl) ⟨448319, by rfl⟩ : syracuseStep 597759 = 896639) B896639
theorem B892955 : Blo 595291 892955 := bstep (se 1 (by rfl) ⟨669716, by rfl⟩ : syracuseStep 892955 = 1339433) B1339433
theorem B598183 : Blo 595291 598183 := bstep (se 1 (by rfl) ⟨448637, by rfl⟩ : syracuseStep 598183 = 897275) B897275
theorem B1024235 : Blo 595291 1024235 := bstep (se 1 (by rfl) ⟨768176, by rfl⟩ : syracuseStep 1024235 = 1536353) B1536353
theorem B893819 : Blo 595291 893819 := bstep (se 1 (by rfl) ⟨670364, by rfl⟩ : syracuseStep 893819 = 1340729) B1340729
theorem B896495 : Blo 595291 896495 := bstep (se 1 (by rfl) ⟨672371, by rfl⟩ : syracuseStep 896495 = 1344743) B1344743
theorem B4310783 : Blo 595291 4310783 := bstep (se 1 (by rfl) ⟨3233087, by rfl⟩ : syracuseStep 4310783 = 6466175) B6466175
theorem B2018465 : Blo 595291 2018465 := bstep (se 2 (by rfl) ⟨756924, by rfl⟩ : syracuseStep 2018465 = 1513849) B1513849
theorem B3497215 : Blo 595291 3497215 := bstep (se 1 (by rfl) ⟨2622911, by rfl⟩ : syracuseStep 3497215 = 5245823) B5245823
theorem B1008119 : Blo 595291 1008119 := bstep (se 1 (by rfl) ⟨756089, by rfl⟩ : syracuseStep 1008119 = 1512179) B1512179
theorem B2187767 : Blo 595291 2187767 := bstep (se 1 (by rfl) ⟨1640825, by rfl⟩ : syracuseStep 2187767 = 3281651) B3281651
theorem B5106887 : Blo 595291 5106887 := bstep (se 1 (by rfl) ⟨3830165, by rfl⟩ : syracuseStep 5106887 = 7660331) B7660331
theorem B1341503 : Blo 595291 1341503 := bstep (se 1 (by rfl) ⟨1006127, by rfl⟩ : syracuseStep 1341503 = 2012255) B2012255
theorem B1342943 : Blo 595291 1342943 := bstep (se 1 (by rfl) ⟨1007207, by rfl⟩ : syracuseStep 1342943 = 2014415) B2014415
theorem B3408439 : Blo 595291 3408439 := bstep (se 1 (by rfl) ⟨2556329, by rfl⟩ : syracuseStep 3408439 = 5112659) B5112659
theorem B5834045 : Blo 595291 5834045 := bstep (se 3 (by rfl) ⟨1093883, by rfl⟩ : syracuseStep 5834045 = 2187767) B2187767
theorem B1345643 : Blo 595291 1345643 := bstep (se 1 (by rfl) ⟨1009232, by rfl⟩ : syracuseStep 1345643 = 2018465) B2018465
theorem B2558911 : Blo 595291 2558911 := bstep (se 1 (by rfl) ⟨1919183, by rfl⟩ : syracuseStep 2558911 = 3838367) B3838367
theorem B595303 : Blo 595291 595303 := bstep (se 1 (by rfl) ⟨446477, by rfl⟩ : syracuseStep 595303 = 892955) B892955
theorem B595879 : Blo 595291 595879 := bstep (se 1 (by rfl) ⟨446909, by rfl⟩ : syracuseStep 595879 = 893819) B893819
theorem B597663 : Blo 595291 597663 := bstep (se 1 (by rfl) ⟨448247, by rfl⟩ : syracuseStep 597663 = 896495) B896495
theorem B894335 : Blo 595291 894335 := bstep (se 1 (by rfl) ⟨670751, by rfl⟩ : syracuseStep 894335 = 1341503) B1341503
theorem B4662953 : Blo 595291 4662953 := bstep (se 2 (by rfl) ⟨1748607, by rfl⟩ : syracuseStep 4662953 = 3497215) B3497215
theorem B895295 : Blo 595291 895295 := bstep (se 1 (by rfl) ⟨671471, by rfl⟩ : syracuseStep 895295 = 1342943) B1342943
theorem B895739 : Blo 595291 895739 := bstep (se 1 (by rfl) ⟨671804, by rfl⟩ : syracuseStep 895739 = 1343609) B1343609
theorem B4829939 : Blo 595291 4829939 := bstep (se 1 (by rfl) ⟨3622454, by rfl⟩ : syracuseStep 4829939 = 7244909) B7244909
theorem B3060551 : Blo 595291 3060551 := bstep (se 1 (by rfl) ⟨2295413, by rfl⟩ : syracuseStep 3060551 = 4590827) B4590827
theorem B672079 : Blo 595291 672079 := bstep (se 1 (by rfl) ⟨504059, by rfl⟩ : syracuseStep 672079 = 1008119) B1008119
theorem B2873855 : Blo 595291 2873855 := bstep (se 1 (by rfl) ⟨2155391, by rfl⟩ : syracuseStep 2873855 = 4310783) B4310783
theorem B11491955 : Blo 595291 11491955 := bstep (se 1 (by rfl) ⟨8618966, by rfl⟩ : syracuseStep 11491955 = 17237933) B17237933
theorem B3236393 : Blo 595291 3236393 := bstep (se 2 (by rfl) ⟨1213647, by rfl⟩ : syracuseStep 3236393 = 2427295) B2427295
theorem B682823 : Blo 595291 682823 := bstep (se 1 (by rfl) ⟨512117, by rfl⟩ : syracuseStep 682823 = 1024235) B1024235
theorem B3404591 : Blo 595291 3404591 := bstep (se 1 (by rfl) ⟨2553443, by rfl⟩ : syracuseStep 3404591 = 5106887) B5106887
theorem B8161469 : Blo 595291 8161469 := bstep (se 3 (by rfl) ⟨1530275, by rfl⟩ : syracuseStep 8161469 = 3060551) B3060551
theorem B3411881 : Blo 595291 3411881 := bstep (se 2 (by rfl) ⟨1279455, by rfl⟩ : syracuseStep 3411881 = 2558911) B2558911
theorem B596223 : Blo 595291 596223 := bstep (se 1 (by rfl) ⟨447167, by rfl⟩ : syracuseStep 596223 = 894335) B894335
theorem B596863 : Blo 595291 596863 := bstep (se 1 (by rfl) ⟨447647, by rfl⟩ : syracuseStep 596863 = 895295) B895295
theorem B597159 : Blo 595291 597159 := bstep (se 1 (by rfl) ⟨447869, by rfl⟩ : syracuseStep 597159 = 895739) B895739
theorem B3219959 : Blo 595291 3219959 := bstep (se 1 (by rfl) ⟨2414969, by rfl⟩ : syracuseStep 3219959 = 4829939) B4829939
theorem B2269727 : Blo 595291 2269727 := bstep (se 1 (by rfl) ⟨1702295, by rfl⟩ : syracuseStep 2269727 = 3404591) B3404591
theorem B896105 : Blo 595291 896105 := bstep (se 2 (by rfl) ⟨336039, by rfl⟩ : syracuseStep 896105 = 672079) B672079
theorem B897095 : Blo 595291 897095 := bstep (se 1 (by rfl) ⟨672821, by rfl⟩ : syracuseStep 897095 = 1345643) B1345643
theorem B8630381 : Blo 595291 8630381 := bstep (se 3 (by rfl) ⟨1618196, by rfl⟩ : syracuseStep 8630381 = 3236393) B3236393
theorem B1915903 : Blo 595291 1915903 := bstep (se 1 (by rfl) ⟨1436927, by rfl⟩ : syracuseStep 1915903 = 2873855) B2873855
theorem B1820861 : Blo 595291 1820861 := bstep (se 3 (by rfl) ⟨341411, by rfl⟩ : syracuseStep 1820861 = 682823) B682823
theorem B4544585 : Blo 595291 4544585 := bstep (se 2 (by rfl) ⟨1704219, by rfl⟩ : syracuseStep 4544585 = 3408439) B3408439
theorem B15557453 : Blo 595291 15557453 := bstep (se 3 (by rfl) ⟨2917022, by rfl⟩ : syracuseStep 15557453 = 5834045) B5834045
theorem B7661303 : Blo 595291 7661303 := bstep (se 1 (by rfl) ⟨5745977, by rfl⟩ : syracuseStep 7661303 = 11491955) B11491955
theorem B3108635 : Blo 595291 3108635 := bstep (se 1 (by rfl) ⟨2331476, by rfl⟩ : syracuseStep 3108635 = 4662953) B4662953
theorem B8586557 : Blo 595291 8586557 := bstep (se 3 (by rfl) ⟨1609979, by rfl⟩ : syracuseStep 8586557 = 3219959) B3219959
theorem B5440979 : Blo 595291 5440979 := bstep (se 1 (by rfl) ⟨4080734, by rfl⟩ : syracuseStep 5440979 = 8161469) B8161469
theorem B1213907 : Blo 595291 1213907 := bstep (se 1 (by rfl) ⟨910430, by rfl⟩ : syracuseStep 1213907 = 1820861) B1820861
theorem B1513151 : Blo 595291 1513151 := bstep (se 1 (by rfl) ⟨1134863, by rfl⟩ : syracuseStep 1513151 = 2269727) B2269727
theorem B597403 : Blo 595291 597403 := bstep (se 1 (by rfl) ⟨448052, by rfl⟩ : syracuseStep 597403 = 896105) B896105
theorem B2072423 : Blo 595291 2072423 := bstep (se 1 (by rfl) ⟨1554317, by rfl⟩ : syracuseStep 2072423 = 3108635) B3108635
theorem B598063 : Blo 595291 598063 := bstep (se 1 (by rfl) ⟨448547, by rfl⟩ : syracuseStep 598063 = 897095) B897095
theorem B2274587 : Blo 595291 2274587 := bstep (se 1 (by rfl) ⟨1705940, by rfl⟩ : syracuseStep 2274587 = 3411881) B3411881
theorem B3029723 : Blo 595291 3029723 := bstep (se 1 (by rfl) ⟨2272292, by rfl⟩ : syracuseStep 3029723 = 4544585) B4544585
theorem B10371635 : Blo 595291 10371635 := bstep (se 1 (by rfl) ⟨7778726, by rfl⟩ : syracuseStep 10371635 = 15557453) B15557453
theorem B5753587 : Blo 595291 5753587 := bstep (se 1 (by rfl) ⟨4315190, by rfl⟩ : syracuseStep 5753587 = 8630381) B8630381
theorem B5107535 : Blo 595291 5107535 := bstep (se 1 (by rfl) ⟨3830651, by rfl⟩ : syracuseStep 5107535 = 7661303) B7661303
theorem B2554537 : Blo 595291 2554537 := bstep (se 2 (by rfl) ⟨957951, by rfl⟩ : syracuseStep 2554537 = 1915903) B1915903
theorem B6914423 : Blo 595291 6914423 := bstep (se 1 (by rfl) ⟨5185817, by rfl⟩ : syracuseStep 6914423 = 10371635) B10371635
theorem B7671449 : Blo 595291 7671449 := bstep (se 2 (by rfl) ⟨2876793, by rfl⟩ : syracuseStep 7671449 = 5753587) B5753587
theorem B1516391 : Blo 595291 1516391 := bstep (se 1 (by rfl) ⟨1137293, by rfl⟩ : syracuseStep 1516391 = 2274587) B2274587
theorem B2019815 : Blo 595291 2019815 := bstep (se 1 (by rfl) ⟨1514861, by rfl⟩ : syracuseStep 2019815 = 3029723) B3029723
theorem B5526461 : Blo 595291 5526461 := bstep (se 3 (by rfl) ⟨1036211, by rfl⟩ : syracuseStep 5526461 = 2072423) B2072423
theorem B5724371 : Blo 595291 5724371 := bstep (se 1 (by rfl) ⟨4293278, by rfl⟩ : syracuseStep 5724371 = 8586557) B8586557
theorem B1008767 : Blo 595291 1008767 := bstep (se 1 (by rfl) ⟨756575, by rfl⟩ : syracuseStep 1008767 = 1513151) B1513151
theorem B14509277 : Blo 595291 14509277 := bstep (se 3 (by rfl) ⟨2720489, by rfl⟩ : syracuseStep 14509277 = 5440979) B5440979
theorem B3237085 : Blo 595291 3237085 := bstep (se 3 (by rfl) ⟨606953, by rfl⟩ : syracuseStep 3237085 = 1213907) B1213907
theorem B3405023 : Blo 595291 3405023 := bstep (se 1 (by rfl) ⟨2553767, by rfl⟩ : syracuseStep 3405023 = 5107535) B5107535
theorem B3406049 : Blo 595291 3406049 := bstep (se 2 (by rfl) ⟨1277268, by rfl⟩ : syracuseStep 3406049 = 2554537) B2554537
theorem B5114299 : Blo 595291 5114299 := bstep (se 1 (by rfl) ⟨3835724, by rfl⟩ : syracuseStep 5114299 = 7671449) B7671449
theorem B1346543 : Blo 595291 1346543 := bstep (se 1 (by rfl) ⟨1009907, by rfl⟩ : syracuseStep 1346543 = 2019815) B2019815
theorem B9672851 : Blo 595291 9672851 := bstep (se 1 (by rfl) ⟨7254638, by rfl⟩ : syracuseStep 9672851 = 14509277) B14509277
theorem B2270015 : Blo 595291 2270015 := bstep (se 1 (by rfl) ⟨1702511, by rfl⟩ : syracuseStep 2270015 = 3405023) B3405023
theorem B2270699 : Blo 595291 2270699 := bstep (se 1 (by rfl) ⟨1703024, by rfl⟩ : syracuseStep 2270699 = 3406049) B3406049
theorem B3684307 : Blo 595291 3684307 := bstep (se 1 (by rfl) ⟨2763230, by rfl⟩ : syracuseStep 3684307 = 5526461) B5526461
theorem B3816247 : Blo 595291 3816247 := bstep (se 1 (by rfl) ⟨2862185, by rfl⟩ : syracuseStep 3816247 = 5724371) B5724371
theorem B672511 : Blo 595291 672511 := bstep (se 1 (by rfl) ⟨504383, by rfl⟩ : syracuseStep 672511 = 1008767) B1008767
theorem B18438461 : Blo 595291 18438461 := bstep (se 3 (by rfl) ⟨3457211, by rfl⟩ : syracuseStep 18438461 = 6914423) B6914423
theorem B4316113 : Blo 595291 4316113 := bstep (se 2 (by rfl) ⟨1618542, by rfl⟩ : syracuseStep 4316113 = 3237085) B3237085
theorem B1010927 : Blo 595291 1010927 := bstep (se 1 (by rfl) ⟨758195, by rfl⟩ : syracuseStep 1010927 = 1516391) B1516391
theorem B6819065 : Blo 595291 6819065 := bstep (se 2 (by rfl) ⟨2557149, by rfl⟩ : syracuseStep 6819065 = 5114299) B5114299
theorem B12292307 : Blo 595291 12292307 := bstep (se 1 (by rfl) ⟨9219230, by rfl⟩ : syracuseStep 12292307 = 18438461) B18438461
theorem B1513343 : Blo 595291 1513343 := bstep (se 1 (by rfl) ⟨1135007, by rfl⟩ : syracuseStep 1513343 = 2270015) B2270015
theorem B1513799 : Blo 595291 1513799 := bstep (se 1 (by rfl) ⟨1135349, by rfl⟩ : syracuseStep 1513799 = 2270699) B2270699
theorem B5088329 : Blo 595291 5088329 := bstep (se 2 (by rfl) ⟨1908123, by rfl⟩ : syracuseStep 5088329 = 3816247) B3816247
theorem B896681 : Blo 595291 896681 := bstep (se 2 (by rfl) ⟨336255, by rfl⟩ : syracuseStep 896681 = 672511) B672511
theorem B897695 : Blo 595291 897695 := bstep (se 1 (by rfl) ⟨673271, by rfl⟩ : syracuseStep 897695 = 1346543) B1346543
theorem B673951 : Blo 595291 673951 := bstep (se 1 (by rfl) ⟨505463, by rfl⟩ : syracuseStep 673951 = 1010927) B1010927
theorem B5754817 : Blo 595291 5754817 := bstep (se 2 (by rfl) ⟨2158056, by rfl⟩ : syracuseStep 5754817 = 4316113) B4316113
theorem B6448567 : Blo 595291 6448567 := bstep (se 1 (by rfl) ⟨4836425, by rfl⟩ : syracuseStep 6448567 = 9672851) B9672851
theorem B4912409 : Blo 595291 4912409 := bstep (se 2 (by rfl) ⟨1842153, by rfl⟩ : syracuseStep 4912409 = 3684307) B3684307
theorem B8194871 : Blo 595291 8194871 := bstep (se 1 (by rfl) ⟨6146153, by rfl⟩ : syracuseStep 8194871 = 12292307) B12292307
theorem B7673089 : Blo 595291 7673089 := bstep (se 2 (by rfl) ⟨2877408, by rfl⟩ : syracuseStep 7673089 = 5754817) B5754817
theorem B597787 : Blo 595291 597787 := bstep (se 1 (by rfl) ⟨448340, by rfl⟩ : syracuseStep 597787 = 896681) B896681
theorem B598463 : Blo 595291 598463 := bstep (se 1 (by rfl) ⟨448847, by rfl⟩ : syracuseStep 598463 = 897695) B897695
theorem B8598089 : Blo 595291 8598089 := bstep (se 2 (by rfl) ⟨3224283, by rfl⟩ : syracuseStep 8598089 = 6448567) B6448567
theorem B898601 : Blo 595291 898601 := bstep (se 2 (by rfl) ⟨336975, by rfl⟩ : syracuseStep 898601 = 673951) B673951
theorem B3392219 : Blo 595291 3392219 := bstep (se 1 (by rfl) ⟨2544164, by rfl⟩ : syracuseStep 3392219 = 5088329) B5088329
theorem B4546043 : Blo 595291 4546043 := bstep (se 1 (by rfl) ⟨3409532, by rfl⟩ : syracuseStep 4546043 = 6819065) B6819065
theorem B1008895 : Blo 595291 1008895 := bstep (se 1 (by rfl) ⟨756671, by rfl⟩ : syracuseStep 1008895 = 1513343) B1513343
theorem B1009199 : Blo 595291 1009199 := bstep (se 1 (by rfl) ⟨756899, by rfl⟩ : syracuseStep 1009199 = 1513799) B1513799
theorem B3274939 : Blo 595291 3274939 := bstep (se 1 (by rfl) ⟨2456204, by rfl⟩ : syracuseStep 3274939 = 4912409) B4912409
theorem B2261479 : Blo 595291 2261479 := bstep (se 1 (by rfl) ⟨1696109, by rfl⟩ : syracuseStep 2261479 = 3392219) B3392219
theorem B1345193 : Blo 595291 1345193 := bstep (se 2 (by rfl) ⟨504447, by rfl⟩ : syracuseStep 1345193 = 1008895) B1008895
theorem B10230785 : Blo 595291 10230785 := bstep (se 2 (by rfl) ⟨3836544, by rfl⟩ : syracuseStep 10230785 = 7673089) B7673089
theorem B4366585 : Blo 595291 4366585 := bstep (se 2 (by rfl) ⟨1637469, by rfl⟩ : syracuseStep 4366585 = 3274939) B3274939
theorem B599067 : Blo 595291 599067 := bstep (se 1 (by rfl) ⟨449300, by rfl⟩ : syracuseStep 599067 = 898601) B898601
theorem B3030695 : Blo 595291 3030695 := bstep (se 1 (by rfl) ⟨2273021, by rfl⟩ : syracuseStep 3030695 = 4546043) B4546043
theorem B672799 : Blo 595291 672799 := bstep (se 1 (by rfl) ⟨504599, by rfl⟩ : syracuseStep 672799 = 1009199) B1009199
theorem B5463247 : Blo 595291 5463247 := bstep (se 1 (by rfl) ⟨4097435, by rfl⟩ : syracuseStep 5463247 = 8194871) B8194871
theorem B5732059 : Blo 595291 5732059 := bstep (se 1 (by rfl) ⟨4299044, by rfl⟩ : syracuseStep 5732059 = 8598089) B8598089
theorem B3015305 : Blo 595291 3015305 := bstep (se 2 (by rfl) ⟨1130739, by rfl⟩ : syracuseStep 3015305 = 2261479) B2261479
theorem B6820523 : Blo 595291 6820523 := bstep (se 1 (by rfl) ⟨5115392, by rfl⟩ : syracuseStep 6820523 = 10230785) B10230785
theorem B7642745 : Blo 595291 7642745 := bstep (se 2 (by rfl) ⟨2866029, by rfl⟩ : syracuseStep 7642745 = 5732059) B5732059
theorem B7284329 : Blo 595291 7284329 := bstep (se 2 (by rfl) ⟨2731623, by rfl⟩ : syracuseStep 7284329 = 5463247) B5463247
theorem B896795 : Blo 595291 896795 := bstep (se 1 (by rfl) ⟨672596, by rfl⟩ : syracuseStep 896795 = 1345193) B1345193
theorem B897065 : Blo 595291 897065 := bstep (se 2 (by rfl) ⟨336399, by rfl⟩ : syracuseStep 897065 = 672799) B672799
theorem B2020463 : Blo 595291 2020463 := bstep (se 1 (by rfl) ⟨1515347, by rfl⟩ : syracuseStep 2020463 = 3030695) B3030695
theorem B5822113 : Blo 595291 5822113 := bstep (se 2 (by rfl) ⟨2183292, by rfl⟩ : syracuseStep 5822113 = 4366585) B4366585
theorem B1346975 : Blo 595291 1346975 := bstep (se 1 (by rfl) ⟨1010231, by rfl⟩ : syracuseStep 1346975 = 2020463) B2020463
theorem B4856219 : Blo 595291 4856219 := bstep (se 1 (by rfl) ⟨3642164, by rfl⟩ : syracuseStep 4856219 = 7284329) B7284329
theorem B597863 : Blo 595291 597863 := bstep (se 1 (by rfl) ⟨448397, by rfl⟩ : syracuseStep 597863 = 896795) B896795
theorem B598043 : Blo 595291 598043 := bstep (se 1 (by rfl) ⟨448532, by rfl⟩ : syracuseStep 598043 = 897065) B897065
theorem B2010203 : Blo 595291 2010203 := bstep (se 1 (by rfl) ⟨1507652, by rfl⟩ : syracuseStep 2010203 = 3015305) B3015305
theorem B5095163 : Blo 595291 5095163 := bstep (se 1 (by rfl) ⟨3821372, by rfl⟩ : syracuseStep 5095163 = 7642745) B7642745
theorem B4547015 : Blo 595291 4547015 := bstep (se 1 (by rfl) ⟨3410261, by rfl⟩ : syracuseStep 4547015 = 6820523) B6820523
theorem B7762817 : Blo 595291 7762817 := bstep (se 2 (by rfl) ⟨2911056, by rfl⟩ : syracuseStep 7762817 = 5822113) B5822113
theorem B897983 : Blo 595291 897983 := bstep (se 1 (by rfl) ⟨673487, by rfl⟩ : syracuseStep 897983 = 1346975) B1346975
theorem B3031343 : Blo 595291 3031343 := bstep (se 1 (by rfl) ⟨2273507, by rfl⟩ : syracuseStep 3031343 = 4547015) B4547015
theorem B3396775 : Blo 595291 3396775 := bstep (se 1 (by rfl) ⟨2547581, by rfl⟩ : syracuseStep 3396775 = 5095163) B5095163
theorem B20700845 : Blo 595291 20700845 := bstep (se 3 (by rfl) ⟨3881408, by rfl⟩ : syracuseStep 20700845 = 7762817) B7762817
theorem B3237479 : Blo 595291 3237479 := bstep (se 1 (by rfl) ⟨2428109, by rfl⟩ : syracuseStep 3237479 = 4856219) B4856219
theorem B1340135 : Blo 595291 1340135 := bstep (se 1 (by rfl) ⟨1005101, by rfl⟩ : syracuseStep 1340135 = 2010203) B2010203
theorem B13800563 : Blo 595291 13800563 := bstep (se 1 (by rfl) ⟨10350422, by rfl⟩ : syracuseStep 13800563 = 20700845) B20700845
theorem B4529033 : Blo 595291 4529033 := bstep (se 2 (by rfl) ⟨1698387, by rfl⟩ : syracuseStep 4529033 = 3396775) B3396775
theorem B893423 : Blo 595291 893423 := bstep (se 1 (by rfl) ⟨670067, by rfl⟩ : syracuseStep 893423 = 1340135) B1340135
theorem B598655 : Blo 595291 598655 := bstep (se 1 (by rfl) ⟨448991, by rfl⟩ : syracuseStep 598655 = 897983) B897983
theorem B2020895 : Blo 595291 2020895 := bstep (se 1 (by rfl) ⟨1515671, by rfl⟩ : syracuseStep 2020895 = 3031343) B3031343
theorem B2158319 : Blo 595291 2158319 := bstep (se 1 (by rfl) ⟨1618739, by rfl⟩ : syracuseStep 2158319 = 3237479) B3237479
theorem B1347263 : Blo 595291 1347263 := bstep (se 1 (by rfl) ⟨1010447, by rfl⟩ : syracuseStep 1347263 = 2020895) B2020895
theorem B3019355 : Blo 595291 3019355 := bstep (se 1 (by rfl) ⟨2264516, by rfl⟩ : syracuseStep 3019355 = 4529033) B4529033
theorem B595615 : Blo 595291 595615 := bstep (se 1 (by rfl) ⟨446711, by rfl⟩ : syracuseStep 595615 = 893423) B893423
theorem B9200375 : Blo 595291 9200375 := bstep (se 1 (by rfl) ⟨6900281, by rfl⟩ : syracuseStep 9200375 = 13800563) B13800563
theorem B1438879 : Blo 595291 1438879 := bstep (se 1 (by rfl) ⟨1079159, by rfl⟩ : syracuseStep 1438879 = 2158319) B2158319
theorem B6133583 : Blo 595291 6133583 := bstep (se 1 (by rfl) ⟨4600187, by rfl⟩ : syracuseStep 6133583 = 9200375) B9200375
theorem B898175 : Blo 595291 898175 := bstep (se 1 (by rfl) ⟨673631, by rfl⟩ : syracuseStep 898175 = 1347263) B1347263
theorem B2012903 : Blo 595291 2012903 := bstep (se 1 (by rfl) ⟨1509677, by rfl⟩ : syracuseStep 2012903 = 3019355) B3019355
theorem B1918505 : Blo 595291 1918505 := bstep (se 2 (by rfl) ⟨719439, by rfl⟩ : syracuseStep 1918505 = 1438879) B1438879
theorem B1279003 : Blo 595291 1279003 := bstep (se 1 (by rfl) ⟨959252, by rfl⟩ : syracuseStep 1279003 = 1918505) B1918505
theorem B598783 : Blo 595291 598783 := bstep (se 1 (by rfl) ⟨449087, by rfl⟩ : syracuseStep 598783 = 898175) B898175
theorem B4089055 : Blo 595291 4089055 := bstep (se 1 (by rfl) ⟨3066791, by rfl⟩ : syracuseStep 4089055 = 6133583) B6133583
theorem B1341935 : Blo 595291 1341935 := bstep (se 1 (by rfl) ⟨1006451, by rfl⟩ : syracuseStep 1341935 = 2012903) B2012903
theorem B1705337 : Blo 595291 1705337 := bstep (se 2 (by rfl) ⟨639501, by rfl⟩ : syracuseStep 1705337 = 1279003) B1279003
theorem B894623 : Blo 595291 894623 := bstep (se 1 (by rfl) ⟨670967, by rfl⟩ : syracuseStep 894623 = 1341935) B1341935
theorem B5452073 : Blo 595291 5452073 := bstep (se 2 (by rfl) ⟨2044527, by rfl⟩ : syracuseStep 5452073 = 4089055) B4089055
theorem B596415 : Blo 595291 596415 := bstep (se 1 (by rfl) ⟨447311, by rfl⟩ : syracuseStep 596415 = 894623) B894623
theorem B1136891 : Blo 595291 1136891 := bstep (se 1 (by rfl) ⟨852668, by rfl⟩ : syracuseStep 1136891 = 1705337) B1705337
theorem B3634715 : Blo 595291 3634715 := bstep (se 1 (by rfl) ⟨2726036, by rfl⟩ : syracuseStep 3634715 = 5452073) B5452073
theorem B757927 : Blo 595291 757927 := bstep (se 1 (by rfl) ⟨568445, by rfl⟩ : syracuseStep 757927 = 1136891) B1136891
theorem B2423143 : Blo 595291 2423143 := bstep (se 1 (by rfl) ⟨1817357, by rfl⟩ : syracuseStep 2423143 = 3634715) B3634715
theorem B3230857 : Blo 595291 3230857 := bstep (se 2 (by rfl) ⟨1211571, by rfl⟩ : syracuseStep 3230857 = 2423143) B2423143
theorem B1010569 : Blo 595291 1010569 := bstep (se 2 (by rfl) ⟨378963, by rfl⟩ : syracuseStep 1010569 = 757927) B757927
theorem B1347425 : Blo 595291 1347425 := bstep (se 2 (by rfl) ⟨505284, by rfl⟩ : syracuseStep 1347425 = 1010569) B1010569
theorem B17231237 : Blo 595291 17231237 := bstep (se 4 (by rfl) ⟨1615428, by rfl⟩ : syracuseStep 17231237 = 3230857) B3230857
theorem B898283 : Blo 595291 898283 := bstep (se 1 (by rfl) ⟨673712, by rfl⟩ : syracuseStep 898283 = 1347425) B1347425
theorem B11487491 : Blo 595291 11487491 := bstep (se 1 (by rfl) ⟨8615618, by rfl⟩ : syracuseStep 11487491 = 17231237) B17231237
theorem B598855 : Blo 595291 598855 := bstep (se 1 (by rfl) ⟨449141, by rfl⟩ : syracuseStep 598855 = 898283) B898283
theorem B7658327 : Blo 595291 7658327 := bstep (se 1 (by rfl) ⟨5743745, by rfl⟩ : syracuseStep 7658327 = 11487491) B11487491
theorem B5105551 : Blo 595291 5105551 := bstep (se 1 (by rfl) ⟨3829163, by rfl⟩ : syracuseStep 5105551 = 7658327) B7658327
theorem B6807401 : Blo 595291 6807401 := bstep (se 2 (by rfl) ⟨2552775, by rfl⟩ : syracuseStep 6807401 = 5105551) B5105551
theorem B4538267 : Blo 595291 4538267 := bstep (se 1 (by rfl) ⟨3403700, by rfl⟩ : syracuseStep 4538267 = 6807401) B6807401
theorem B3025511 : Blo 595291 3025511 := bstep (se 1 (by rfl) ⟨2269133, by rfl⟩ : syracuseStep 3025511 = 4538267) B4538267
theorem B2017007 : Blo 595291 2017007 := bstep (se 1 (by rfl) ⟨1512755, by rfl⟩ : syracuseStep 2017007 = 3025511) B3025511
theorem B1344671 : Blo 595291 1344671 := bstep (se 1 (by rfl) ⟨1008503, by rfl⟩ : syracuseStep 1344671 = 2017007) B2017007
theorem B896447 : Blo 595291 896447 := bstep (se 1 (by rfl) ⟨672335, by rfl⟩ : syracuseStep 896447 = 1344671) B1344671
theorem B597631 : Blo 595291 597631 := bstep (se 1 (by rfl) ⟨448223, by rfl⟩ : syracuseStep 597631 = 896447) B896447

theorem C0 (j : ℕ) (h1 : 148822 ≤ j) (h2 : j ≤ 149521) : Blo 595291 (4 * j + 3) := by
  interval_cases j
  · exact B595291
  · exact B595295
  · exact B595299
  · exact B595303
  · exact B595307
  · exact B595311
  · exact B595315
  · exact B595319
  · exact B595323
  · exact B595327
  · exact B595331
  · exact B595335
  · exact B595339
  · exact B595343
  · exact B595347
  · exact B595351
  · exact B595355
  · exact B595359
  · exact B595363
  · exact B595367
  · exact B595371
  · exact B595375
  · exact B595379
  · exact B595383
  · exact B595387
  · exact B595391
  · exact B595395
  · exact B595399
  · exact B595403
  · exact B595407
  · exact B595411
  · exact B595415
  · exact B595419
  · exact B595423
  · exact B595427
  · exact B595431
  · exact B595435
  · exact B595439
  · exact B595443
  · exact B595447
  · exact B595451
  · exact B595455
  · exact B595459
  · exact B595463
  · exact B595467
  · exact B595471
  · exact B595475
  · exact B595479
  · exact B595483
  · exact B595487
  · exact B595491
  · exact B595495
  · exact B595499
  · exact B595503
  · exact B595507
  · exact B595511
  · exact B595515
  · exact B595519
  · exact B595523
  · exact B595527
  · exact B595531
  · exact B595535
  · exact B595539
  · exact B595543
  · exact B595547
  · exact B595551
  · exact B595555
  · exact B595559
  · exact B595563
  · exact B595567
  · exact B595571
  · exact B595575
  · exact B595579
  · exact B595583
  · exact B595587
  · exact B595591
  · exact B595595
  · exact B595599
  · exact B595603
  · exact B595607
  · exact B595611
  · exact B595615
  · exact B595619
  · exact B595623
  · exact B595627
  · exact B595631
  · exact B595635
  · exact B595639
  · exact B595643
  · exact B595647
  · exact B595651
  · exact B595655
  · exact B595659
  · exact B595663
  · exact B595667
  · exact B595671
  · exact B595675
  · exact B595679
  · exact B595683
  · exact B595687
  · exact B595691
  · exact B595695
  · exact B595699
  · exact B595703
  · exact B595707
  · exact B595711
  · exact B595715
  · exact B595719
  · exact B595723
  · exact B595727
  · exact B595731
  · exact B595735
  · exact B595739
  · exact B595743
  · exact B595747
  · exact B595751
  · exact B595755
  · exact B595759
  · exact B595763
  · exact B595767
  · exact B595771
  · exact B595775
  · exact B595779
  · exact B595783
  · exact B595787
  · exact B595791
  · exact B595795
  · exact B595799
  · exact B595803
  · exact B595807
  · exact B595811
  · exact B595815
  · exact B595819
  · exact B595823
  · exact B595827
  · exact B595831
  · exact B595835
  · exact B595839
  · exact B595843
  · exact B595847
  · exact B595851
  · exact B595855
  · exact B595859
  · exact B595863
  · exact B595867
  · exact B595871
  · exact B595875
  · exact B595879
  · exact B595883
  · exact B595887
  · exact B595891
  · exact B595895
  · exact B595899
  · exact B595903
  · exact B595907
  · exact B595911
  · exact B595915
  · exact B595919
  · exact B595923
  · exact B595927
  · exact B595931
  · exact B595935
  · exact B595939
  · exact B595943
  · exact B595947
  · exact B595951
  · exact B595955
  · exact B595959
  · exact B595963
  · exact B595967
  · exact B595971
  · exact B595975
  · exact B595979
  · exact B595983
  · exact B595987
  · exact B595991
  · exact B595995
  · exact B595999
  · exact B596003
  · exact B596007
  · exact B596011
  · exact B596015
  · exact B596019
  · exact B596023
  · exact B596027
  · exact B596031
  · exact B596035
  · exact B596039
  · exact B596043
  · exact B596047
  · exact B596051
  · exact B596055
  · exact B596059
  · exact B596063
  · exact B596067
  · exact B596071
  · exact B596075
  · exact B596079
  · exact B596083
  · exact B596087
  · exact B596091
  · exact B596095
  · exact B596099
  · exact B596103
  · exact B596107
  · exact B596111
  · exact B596115
  · exact B596119
  · exact B596123
  · exact B596127
  · exact B596131
  · exact B596135
  · exact B596139
  · exact B596143
  · exact B596147
  · exact B596151
  · exact B596155
  · exact B596159
  · exact B596163
  · exact B596167
  · exact B596171
  · exact B596175
  · exact B596179
  · exact B596183
  · exact B596187
  · exact B596191
  · exact B596195
  · exact B596199
  · exact B596203
  · exact B596207
  · exact B596211
  · exact B596215
  · exact B596219
  · exact B596223
  · exact B596227
  · exact B596231
  · exact B596235
  · exact B596239
  · exact B596243
  · exact B596247
  · exact B596251
  · exact B596255
  · exact B596259
  · exact B596263
  · exact B596267
  · exact B596271
  · exact B596275
  · exact B596279
  · exact B596283
  · exact B596287
  · exact B596291
  · exact B596295
  · exact B596299
  · exact B596303
  · exact B596307
  · exact B596311
  · exact B596315
  · exact B596319
  · exact B596323
  · exact B596327
  · exact B596331
  · exact B596335
  · exact B596339
  · exact B596343
  · exact B596347
  · exact B596351
  · exact B596355
  · exact B596359
  · exact B596363
  · exact B596367
  · exact B596371
  · exact B596375
  · exact B596379
  · exact B596383
  · exact B596387
  · exact B596391
  · exact B596395
  · exact B596399
  · exact B596403
  · exact B596407
  · exact B596411
  · exact B596415
  · exact B596419
  · exact B596423
  · exact B596427
  · exact B596431
  · exact B596435
  · exact B596439
  · exact B596443
  · exact B596447
  · exact B596451
  · exact B596455
  · exact B596459
  · exact B596463
  · exact B596467
  · exact B596471
  · exact B596475
  · exact B596479
  · exact B596483
  · exact B596487
  · exact B596491
  · exact B596495
  · exact B596499
  · exact B596503
  · exact B596507
  · exact B596511
  · exact B596515
  · exact B596519
  · exact B596523
  · exact B596527
  · exact B596531
  · exact B596535
  · exact B596539
  · exact B596543
  · exact B596547
  · exact B596551
  · exact B596555
  · exact B596559
  · exact B596563
  · exact B596567
  · exact B596571
  · exact B596575
  · exact B596579
  · exact B596583
  · exact B596587
  · exact B596591
  · exact B596595
  · exact B596599
  · exact B596603
  · exact B596607
  · exact B596611
  · exact B596615
  · exact B596619
  · exact B596623
  · exact B596627
  · exact B596631
  · exact B596635
  · exact B596639
  · exact B596643
  · exact B596647
  · exact B596651
  · exact B596655
  · exact B596659
  · exact B596663
  · exact B596667
  · exact B596671
  · exact B596675
  · exact B596679
  · exact B596683
  · exact B596687
  · exact B596691
  · exact B596695
  · exact B596699
  · exact B596703
  · exact B596707
  · exact B596711
  · exact B596715
  · exact B596719
  · exact B596723
  · exact B596727
  · exact B596731
  · exact B596735
  · exact B596739
  · exact B596743
  · exact B596747
  · exact B596751
  · exact B596755
  · exact B596759
  · exact B596763
  · exact B596767
  · exact B596771
  · exact B596775
  · exact B596779
  · exact B596783
  · exact B596787
  · exact B596791
  · exact B596795
  · exact B596799
  · exact B596803
  · exact B596807
  · exact B596811
  · exact B596815
  · exact B596819
  · exact B596823
  · exact B596827
  · exact B596831
  · exact B596835
  · exact B596839
  · exact B596843
  · exact B596847
  · exact B596851
  · exact B596855
  · exact B596859
  · exact B596863
  · exact B596867
  · exact B596871
  · exact B596875
  · exact B596879
  · exact B596883
  · exact B596887
  · exact B596891
  · exact B596895
  · exact B596899
  · exact B596903
  · exact B596907
  · exact B596911
  · exact B596915
  · exact B596919
  · exact B596923
  · exact B596927
  · exact B596931
  · exact B596935
  · exact B596939
  · exact B596943
  · exact B596947
  · exact B596951
  · exact B596955
  · exact B596959
  · exact B596963
  · exact B596967
  · exact B596971
  · exact B596975
  · exact B596979
  · exact B596983
  · exact B596987
  · exact B596991
  · exact B596995
  · exact B596999
  · exact B597003
  · exact B597007
  · exact B597011
  · exact B597015
  · exact B597019
  · exact B597023
  · exact B597027
  · exact B597031
  · exact B597035
  · exact B597039
  · exact B597043
  · exact B597047
  · exact B597051
  · exact B597055
  · exact B597059
  · exact B597063
  · exact B597067
  · exact B597071
  · exact B597075
  · exact B597079
  · exact B597083
  · exact B597087
  · exact B597091
  · exact B597095
  · exact B597099
  · exact B597103
  · exact B597107
  · exact B597111
  · exact B597115
  · exact B597119
  · exact B597123
  · exact B597127
  · exact B597131
  · exact B597135
  · exact B597139
  · exact B597143
  · exact B597147
  · exact B597151
  · exact B597155
  · exact B597159
  · exact B597163
  · exact B597167
  · exact B597171
  · exact B597175
  · exact B597179
  · exact B597183
  · exact B597187
  · exact B597191
  · exact B597195
  · exact B597199
  · exact B597203
  · exact B597207
  · exact B597211
  · exact B597215
  · exact B597219
  · exact B597223
  · exact B597227
  · exact B597231
  · exact B597235
  · exact B597239
  · exact B597243
  · exact B597247
  · exact B597251
  · exact B597255
  · exact B597259
  · exact B597263
  · exact B597267
  · exact B597271
  · exact B597275
  · exact B597279
  · exact B597283
  · exact B597287
  · exact B597291
  · exact B597295
  · exact B597299
  · exact B597303
  · exact B597307
  · exact B597311
  · exact B597315
  · exact B597319
  · exact B597323
  · exact B597327
  · exact B597331
  · exact B597335
  · exact B597339
  · exact B597343
  · exact B597347
  · exact B597351
  · exact B597355
  · exact B597359
  · exact B597363
  · exact B597367
  · exact B597371
  · exact B597375
  · exact B597379
  · exact B597383
  · exact B597387
  · exact B597391
  · exact B597395
  · exact B597399
  · exact B597403
  · exact B597407
  · exact B597411
  · exact B597415
  · exact B597419
  · exact B597423
  · exact B597427
  · exact B597431
  · exact B597435
  · exact B597439
  · exact B597443
  · exact B597447
  · exact B597451
  · exact B597455
  · exact B597459
  · exact B597463
  · exact B597467
  · exact B597471
  · exact B597475
  · exact B597479
  · exact B597483
  · exact B597487
  · exact B597491
  · exact B597495
  · exact B597499
  · exact B597503
  · exact B597507
  · exact B597511
  · exact B597515
  · exact B597519
  · exact B597523
  · exact B597527
  · exact B597531
  · exact B597535
  · exact B597539
  · exact B597543
  · exact B597547
  · exact B597551
  · exact B597555
  · exact B597559
  · exact B597563
  · exact B597567
  · exact B597571
  · exact B597575
  · exact B597579
  · exact B597583
  · exact B597587
  · exact B597591
  · exact B597595
  · exact B597599
  · exact B597603
  · exact B597607
  · exact B597611
  · exact B597615
  · exact B597619
  · exact B597623
  · exact B597627
  · exact B597631
  · exact B597635
  · exact B597639
  · exact B597643
  · exact B597647
  · exact B597651
  · exact B597655
  · exact B597659
  · exact B597663
  · exact B597667
  · exact B597671
  · exact B597675
  · exact B597679
  · exact B597683
  · exact B597687
  · exact B597691
  · exact B597695
  · exact B597699
  · exact B597703
  · exact B597707
  · exact B597711
  · exact B597715
  · exact B597719
  · exact B597723
  · exact B597727
  · exact B597731
  · exact B597735
  · exact B597739
  · exact B597743
  · exact B597747
  · exact B597751
  · exact B597755
  · exact B597759
  · exact B597763
  · exact B597767
  · exact B597771
  · exact B597775
  · exact B597779
  · exact B597783
  · exact B597787
  · exact B597791
  · exact B597795
  · exact B597799
  · exact B597803
  · exact B597807
  · exact B597811
  · exact B597815
  · exact B597819
  · exact B597823
  · exact B597827
  · exact B597831
  · exact B597835
  · exact B597839
  · exact B597843
  · exact B597847
  · exact B597851
  · exact B597855
  · exact B597859
  · exact B597863
  · exact B597867
  · exact B597871
  · exact B597875
  · exact B597879
  · exact B597883
  · exact B597887
  · exact B597891
  · exact B597895
  · exact B597899
  · exact B597903
  · exact B597907
  · exact B597911
  · exact B597915
  · exact B597919
  · exact B597923
  · exact B597927
  · exact B597931
  · exact B597935
  · exact B597939
  · exact B597943
  · exact B597947
  · exact B597951
  · exact B597955
  · exact B597959
  · exact B597963
  · exact B597967
  · exact B597971
  · exact B597975
  · exact B597979
  · exact B597983
  · exact B597987
  · exact B597991
  · exact B597995
  · exact B597999
  · exact B598003
  · exact B598007
  · exact B598011
  · exact B598015
  · exact B598019
  · exact B598023
  · exact B598027
  · exact B598031
  · exact B598035
  · exact B598039
  · exact B598043
  · exact B598047
  · exact B598051
  · exact B598055
  · exact B598059
  · exact B598063
  · exact B598067
  · exact B598071
  · exact B598075
  · exact B598079
  · exact B598083
  · exact B598087

theorem C1 (j : ℕ) (h1 : 149522 ≤ j) (h2 : j ≤ 149822) : Blo 595291 (4 * j + 3) := by
  interval_cases j
  · exact B598091
  · exact B598095
  · exact B598099
  · exact B598103
  · exact B598107
  · exact B598111
  · exact B598115
  · exact B598119
  · exact B598123
  · exact B598127
  · exact B598131
  · exact B598135
  · exact B598139
  · exact B598143
  · exact B598147
  · exact B598151
  · exact B598155
  · exact B598159
  · exact B598163
  · exact B598167
  · exact B598171
  · exact B598175
  · exact B598179
  · exact B598183
  · exact B598187
  · exact B598191
  · exact B598195
  · exact B598199
  · exact B598203
  · exact B598207
  · exact B598211
  · exact B598215
  · exact B598219
  · exact B598223
  · exact B598227
  · exact B598231
  · exact B598235
  · exact B598239
  · exact B598243
  · exact B598247
  · exact B598251
  · exact B598255
  · exact B598259
  · exact B598263
  · exact B598267
  · exact B598271
  · exact B598275
  · exact B598279
  · exact B598283
  · exact B598287
  · exact B598291
  · exact B598295
  · exact B598299
  · exact B598303
  · exact B598307
  · exact B598311
  · exact B598315
  · exact B598319
  · exact B598323
  · exact B598327
  · exact B598331
  · exact B598335
  · exact B598339
  · exact B598343
  · exact B598347
  · exact B598351
  · exact B598355
  · exact B598359
  · exact B598363
  · exact B598367
  · exact B598371
  · exact B598375
  · exact B598379
  · exact B598383
  · exact B598387
  · exact B598391
  · exact B598395
  · exact B598399
  · exact B598403
  · exact B598407
  · exact B598411
  · exact B598415
  · exact B598419
  · exact B598423
  · exact B598427
  · exact B598431
  · exact B598435
  · exact B598439
  · exact B598443
  · exact B598447
  · exact B598451
  · exact B598455
  · exact B598459
  · exact B598463
  · exact B598467
  · exact B598471
  · exact B598475
  · exact B598479
  · exact B598483
  · exact B598487
  · exact B598491
  · exact B598495
  · exact B598499
  · exact B598503
  · exact B598507
  · exact B598511
  · exact B598515
  · exact B598519
  · exact B598523
  · exact B598527
  · exact B598531
  · exact B598535
  · exact B598539
  · exact B598543
  · exact B598547
  · exact B598551
  · exact B598555
  · exact B598559
  · exact B598563
  · exact B598567
  · exact B598571
  · exact B598575
  · exact B598579
  · exact B598583
  · exact B598587
  · exact B598591
  · exact B598595
  · exact B598599
  · exact B598603
  · exact B598607
  · exact B598611
  · exact B598615
  · exact B598619
  · exact B598623
  · exact B598627
  · exact B598631
  · exact B598635
  · exact B598639
  · exact B598643
  · exact B598647
  · exact B598651
  · exact B598655
  · exact B598659
  · exact B598663
  · exact B598667
  · exact B598671
  · exact B598675
  · exact B598679
  · exact B598683
  · exact B598687
  · exact B598691
  · exact B598695
  · exact B598699
  · exact B598703
  · exact B598707
  · exact B598711
  · exact B598715
  · exact B598719
  · exact B598723
  · exact B598727
  · exact B598731
  · exact B598735
  · exact B598739
  · exact B598743
  · exact B598747
  · exact B598751
  · exact B598755
  · exact B598759
  · exact B598763
  · exact B598767
  · exact B598771
  · exact B598775
  · exact B598779
  · exact B598783
  · exact B598787
  · exact B598791
  · exact B598795
  · exact B598799
  · exact B598803
  · exact B598807
  · exact B598811
  · exact B598815
  · exact B598819
  · exact B598823
  · exact B598827
  · exact B598831
  · exact B598835
  · exact B598839
  · exact B598843
  · exact B598847
  · exact B598851
  · exact B598855
  · exact B598859
  · exact B598863
  · exact B598867
  · exact B598871
  · exact B598875
  · exact B598879
  · exact B598883
  · exact B598887
  · exact B598891
  · exact B598895
  · exact B598899
  · exact B598903
  · exact B598907
  · exact B598911
  · exact B598915
  · exact B598919
  · exact B598923
  · exact B598927
  · exact B598931
  · exact B598935
  · exact B598939
  · exact B598943
  · exact B598947
  · exact B598951
  · exact B598955
  · exact B598959
  · exact B598963
  · exact B598967
  · exact B598971
  · exact B598975
  · exact B598979
  · exact B598983
  · exact B598987
  · exact B598991
  · exact B598995
  · exact B598999
  · exact B599003
  · exact B599007
  · exact B599011
  · exact B599015
  · exact B599019
  · exact B599023
  · exact B599027
  · exact B599031
  · exact B599035
  · exact B599039
  · exact B599043
  · exact B599047
  · exact B599051
  · exact B599055
  · exact B599059
  · exact B599063
  · exact B599067
  · exact B599071
  · exact B599075
  · exact B599079
  · exact B599083
  · exact B599087
  · exact B599091
  · exact B599095
  · exact B599099
  · exact B599103
  · exact B599107
  · exact B599111
  · exact B599115
  · exact B599119
  · exact B599123
  · exact B599127
  · exact B599131
  · exact B599135
  · exact B599139
  · exact B599143
  · exact B599147
  · exact B599151
  · exact B599155
  · exact B599159
  · exact B599163
  · exact B599167
  · exact B599171
  · exact B599175
  · exact B599179
  · exact B599183
  · exact B599187
  · exact B599191
  · exact B599195
  · exact B599199
  · exact B599203
  · exact B599207
  · exact B599211
  · exact B599215
  · exact B599219
  · exact B599223
  · exact B599227
  · exact B599231
  · exact B599235
  · exact B599239
  · exact B599243
  · exact B599247
  · exact B599251
  · exact B599255
  · exact B599259
  · exact B599263
  · exact B599267
  · exact B599271
  · exact B599275
  · exact B599279
  · exact B599283
  · exact B599287
  · exact B599291

theorem solution (m : ℕ) (hlo : 595291 ≤ m) (hhi : m ≤ 599291) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 148822 ≤ j := by omega
    have hj2 : j ≤ 149822 := by omega
    have hb : Blo 595291 (4 * j + 3) := by
      rcases Nat.lt_or_ge j 149522 with hc0 | hc0
      · exact C0 j (by omega) (by omega)
      exact C1 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
