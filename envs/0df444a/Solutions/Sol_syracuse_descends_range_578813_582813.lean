-- Prove2me | solution 1 for syracuse_descends_range_578813_582813
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-09T17:48:40.99173+00:00
-- url     : https://prove2.me/submissions/950a3bc2-3419-4c4f-889c-ff68a2d87ff4

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


theorem B1966085 : Blo 578813 1966085 := bbase (se 4 (by rfl) ⟨184320, by rfl⟩ : syracuseStep 1966085 = 368641) (by norm_num)
theorem B1310741 : Blo 578813 1310741 := bbase (se 6 (by rfl) ⟨30720, by rfl⟩ : syracuseStep 1310741 = 61441) (by norm_num)
theorem B655393 : Blo 578813 655393 := bbase (se 2 (by rfl) ⟨245772, by rfl⟩ : syracuseStep 655393 = 491545) (by norm_num)
theorem B655429 : Blo 578813 655429 := bbase (se 4 (by rfl) ⟨61446, by rfl⟩ : syracuseStep 655429 = 122893) (by norm_num)
theorem B983117 : Blo 578813 983117 := bbase (se 3 (by rfl) ⟨184334, by rfl⟩ : syracuseStep 983117 = 368669) (by norm_num)
theorem B1572949 : Blo 578813 1572949 := bbase (se 8 (by rfl) ⟨9216, by rfl⟩ : syracuseStep 1572949 = 18433) (by norm_num)
theorem B1474645 : Blo 578813 1474645 := bbase (se 8 (by rfl) ⟨8640, by rfl⟩ : syracuseStep 1474645 = 17281) (by norm_num)
theorem B1310813 : Blo 578813 1310813 := bbase (se 3 (by rfl) ⟨245777, by rfl⟩ : syracuseStep 1310813 = 491555) (by norm_num)
theorem B655465 : Blo 578813 655465 := bbase (se 2 (by rfl) ⟨245799, by rfl⟩ : syracuseStep 655465 = 491599) (by norm_num)
theorem B589933 : Blo 578813 589933 := bbase (se 3 (by rfl) ⟨110612, by rfl⟩ : syracuseStep 589933 = 221225) (by norm_num)
theorem B655501 : Blo 578813 655501 := bbase (se 3 (by rfl) ⟨122906, by rfl⟩ : syracuseStep 655501 = 245813) (by norm_num)
theorem B1310885 : Blo 578813 1310885 := bbase (se 4 (by rfl) ⟨122895, by rfl⟩ : syracuseStep 1310885 = 245791) (by norm_num)
theorem B655537 : Blo 578813 655537 := bbase (se 2 (by rfl) ⟨245826, by rfl⟩ : syracuseStep 655537 = 491653) (by norm_num)
theorem B1474757 : Blo 578813 1474757 := bbase (se 4 (by rfl) ⟨138258, by rfl⟩ : syracuseStep 1474757 = 276517) (by norm_num)
theorem B983245 : Blo 578813 983245 := bbase (se 3 (by rfl) ⟨184358, by rfl⟩ : syracuseStep 983245 = 368717) (by norm_num)
theorem B655573 : Blo 578813 655573 := bbase (se 7 (by rfl) ⟨7682, by rfl⟩ : syracuseStep 655573 = 15365) (by norm_num)
theorem B1310957 : Blo 578813 1310957 := bbase (se 3 (by rfl) ⟨245804, by rfl⟩ : syracuseStep 1310957 = 491609) (by norm_num)
theorem B655609 : Blo 578813 655609 := bbase (se 2 (by rfl) ⟨245853, by rfl⟩ : syracuseStep 655609 = 491707) (by norm_num)
theorem B655645 : Blo 578813 655645 := bbase (se 3 (by rfl) ⟨122933, by rfl⟩ : syracuseStep 655645 = 245867) (by norm_num)
theorem B1507621 : Blo 578813 1507621 := bbase (se 4 (by rfl) ⟨141339, by rfl⟩ : syracuseStep 1507621 = 282679) (by norm_num)
theorem B983333 : Blo 578813 983333 := bbase (se 4 (by rfl) ⟨92187, by rfl⟩ : syracuseStep 983333 = 184375) (by norm_num)
theorem B1311029 : Blo 578813 1311029 := bbase (se 5 (by rfl) ⟨61454, by rfl⟩ : syracuseStep 1311029 = 122909) (by norm_num)
theorem B1311101 : Blo 578813 1311101 := bbase (se 3 (by rfl) ⟨245831, by rfl⟩ : syracuseStep 1311101 = 491663) (by norm_num)
theorem B1474949 : Blo 578813 1474949 := bbase (se 4 (by rfl) ⟨138276, by rfl⟩ : syracuseStep 1474949 = 276553) (by norm_num)
theorem B983461 : Blo 578813 983461 := bbase (se 4 (by rfl) ⟨92199, by rfl⟩ : syracuseStep 983461 = 184399) (by norm_num)
theorem B1966517 : Blo 578813 1966517 := bbase (se 5 (by rfl) ⟨92180, by rfl⟩ : syracuseStep 1966517 = 184361) (by norm_num)
theorem B1311173 : Blo 578813 1311173 := bbase (se 4 (by rfl) ⟨122922, by rfl⟩ : syracuseStep 1311173 = 245845) (by norm_num)
theorem B1180109 : Blo 578813 1180109 := bbase (se 3 (by rfl) ⟨221270, by rfl⟩ : syracuseStep 1180109 = 442541) (by norm_num)
theorem B1671637 : Blo 578813 1671637 := bbase (se 7 (by rfl) ⟨19589, by rfl⟩ : syracuseStep 1671637 = 39179) (by norm_num)
theorem B1311245 : Blo 578813 1311245 := bbase (se 3 (by rfl) ⟨245858, by rfl⟩ : syracuseStep 1311245 = 491717) (by norm_num)
theorem B1311317 : Blo 578813 1311317 := bbase (se 8 (by rfl) ⟨7683, by rfl⟩ : syracuseStep 1311317 = 15367) (by norm_num)
theorem B6292181 : Blo 578813 6292181 := bbase (se 7 (by rfl) ⟨73736, by rfl⟩ : syracuseStep 6292181 = 147473) (by norm_num)
theorem B7144213 : Blo 578813 7144213 := bbase (se 6 (by rfl) ⟨167442, by rfl⟩ : syracuseStep 7144213 = 334885) (by norm_num)
theorem B1966949 : Blo 578813 1966949 := bbase (se 4 (by rfl) ⟨184401, by rfl⟩ : syracuseStep 1966949 = 368803) (by norm_num)
theorem B14320597 : Blo 578813 14320597 := bbase (se 7 (by rfl) ⟨167819, by rfl⟩ : syracuseStep 14320597 = 335639) (by norm_num)
theorem B2950181 : Blo 578813 2950181 := bbase (se 4 (by rfl) ⟨276579, by rfl⟩ : syracuseStep 2950181 = 553159) (by norm_num)
theorem B4949045 : Blo 578813 4949045 := bbase (se 5 (by rfl) ⟨231986, by rfl⟩ : syracuseStep 4949045 = 463973) (by norm_num)
theorem B787573 : Blo 578813 787573 := bbase (se 5 (by rfl) ⟨36917, by rfl⟩ : syracuseStep 787573 = 73835) (by norm_num)
theorem B1574213 : Blo 578813 1574213 := bbase (se 4 (by rfl) ⟨147582, by rfl⟩ : syracuseStep 1574213 = 295165) (by norm_num)
theorem B1049965 : Blo 578813 1049965 := bbase (se 3 (by rfl) ⟨196868, by rfl⟩ : syracuseStep 1049965 = 393737) (by norm_num)
theorem B1574453 : Blo 578813 1574453 := bbase (se 5 (by rfl) ⟨73802, by rfl⟩ : syracuseStep 1574453 = 147605) (by norm_num)
theorem B2360981 : Blo 578813 2360981 := bbase (se 6 (by rfl) ⟨55335, by rfl⟩ : syracuseStep 2360981 = 110671) (by norm_num)
theorem B755353 : Blo 578813 755353 := bbase (se 2 (by rfl) ⟨283257, by rfl⟩ : syracuseStep 755353 = 566515) (by norm_num)
theorem B2655973 : Blo 578813 2655973 := bbase (se 4 (by rfl) ⟨248997, by rfl⟩ : syracuseStep 2655973 = 497995) (by norm_num)
theorem B5310197 : Blo 578813 5310197 := bbase (se 5 (by rfl) ⟨248915, by rfl⟩ : syracuseStep 5310197 = 497831) (by norm_num)
theorem B2361125 : Blo 578813 2361125 := bbase (se 4 (by rfl) ⟨221355, by rfl⟩ : syracuseStep 2361125 = 442711) (by norm_num)
theorem B2098997 : Blo 578813 2098997 := bbase (se 5 (by rfl) ⟨98390, by rfl⟩ : syracuseStep 2098997 = 196781) (by norm_num)
theorem B1771429 : Blo 578813 1771429 := bbase (se 4 (by rfl) ⟨166071, by rfl⟩ : syracuseStep 1771429 = 332143) (by norm_num)
theorem B5572597 : Blo 578813 5572597 := bbase (se 5 (by rfl) ⟨261215, by rfl⟩ : syracuseStep 5572597 = 522431) (by norm_num)
theorem B2197813 : Blo 578813 2197813 := bbase (se 5 (by rfl) ⟨103022, by rfl⟩ : syracuseStep 2197813 = 206045) (by norm_num)
theorem B2198117 : Blo 578813 2198117 := bbase (se 4 (by rfl) ⟨206073, by rfl⟩ : syracuseStep 2198117 = 412147) (by norm_num)
theorem B2788357 : Blo 578813 2788357 := bbase (se 4 (by rfl) ⟨261408, by rfl⟩ : syracuseStep 2788357 = 522817) (by norm_num)
theorem B757081 : Blo 578813 757081 := bbase (se 2 (by rfl) ⟨283905, by rfl⟩ : syracuseStep 757081 = 567811) (by norm_num)
theorem B4197845 : Blo 578813 4197845 := bbase (se 7 (by rfl) ⟨49193, by rfl⟩ : syracuseStep 4197845 = 98387) (by norm_num)
theorem B2723701 : Blo 578813 2723701 := bbase (se 5 (by rfl) ⟨127673, by rfl⟩ : syracuseStep 2723701 = 255347) (by norm_num)
theorem B11932181 : Blo 578813 11932181 := bbase (se 6 (by rfl) ⟨279660, by rfl⟩ : syracuseStep 11932181 = 559321) (by norm_num)
theorem B2200229 : Blo 578813 2200229 := bbase (se 4 (by rfl) ⟨206271, by rfl⟩ : syracuseStep 2200229 = 412543) (by norm_num)
theorem B5083829 : Blo 578813 5083829 := bbase (se 5 (by rfl) ⟨238304, by rfl⟩ : syracuseStep 5083829 = 476609) (by norm_num)
theorem B2200517 : Blo 578813 2200517 := bbase (se 4 (by rfl) ⟨206298, by rfl⟩ : syracuseStep 2200517 = 412597) (by norm_num)
theorem B627721 : Blo 578813 627721 := bbase (se 2 (by rfl) ⟨235395, by rfl⟩ : syracuseStep 627721 = 470791) (by norm_num)
theorem B824357 : Blo 578813 824357 := bbase (se 4 (by rfl) ⟨77283, by rfl⟩ : syracuseStep 824357 = 154567) (by norm_num)
theorem B824909 : Blo 578813 824909 := bbase (se 3 (by rfl) ⟨154670, by rfl⟩ : syracuseStep 824909 = 309341) (by norm_num)
theorem B1677125 : Blo 578813 1677125 := bbase (se 4 (by rfl) ⟨157230, by rfl⟩ : syracuseStep 1677125 = 314461) (by norm_num)
theorem B1513333 : Blo 578813 1513333 := bbase (se 5 (by rfl) ⟨70937, by rfl⟩ : syracuseStep 1513333 = 141875) (by norm_num)
theorem B3774485 : Blo 578813 3774485 := bbase (se 6 (by rfl) ⟨88464, by rfl⟩ : syracuseStep 3774485 = 176929) (by norm_num)
theorem B596033 : Blo 578813 596033 := bbase (se 2 (by rfl) ⟨223512, by rfl⟩ : syracuseStep 596033 = 447025) (by norm_num)
theorem B2201701 : Blo 578813 2201701 := bbase (se 4 (by rfl) ⟨206409, by rfl⟩ : syracuseStep 2201701 = 412819) (by norm_num)
theorem B628925 : Blo 578813 628925 := bbase (se 3 (by rfl) ⟨117923, by rfl⟩ : syracuseStep 628925 = 235847) (by norm_num)
theorem B825661 : Blo 578813 825661 := bbase (se 3 (by rfl) ⟨154811, by rfl⟩ : syracuseStep 825661 = 309623) (by norm_num)
theorem B3316085 : Blo 578813 3316085 := bbase (se 5 (by rfl) ⟨155441, by rfl⟩ : syracuseStep 3316085 = 310883) (by norm_num)
theorem B2202005 : Blo 578813 2202005 := bbase (se 6 (by rfl) ⟨51609, by rfl⟩ : syracuseStep 2202005 = 103219) (by norm_num)
theorem B629305 : Blo 578813 629305 := bbase (se 2 (by rfl) ⟨235989, by rfl⟩ : syracuseStep 629305 = 471979) (by norm_num)
theorem B4397813 : Blo 578813 4397813 := bbase (se 5 (by rfl) ⟨206147, by rfl⟩ : syracuseStep 4397813 = 412295) (by norm_num)
theorem B20126677 : Blo 578813 20126677 := bbase (se 7 (by rfl) ⟨235859, by rfl⟩ : syracuseStep 20126677 = 471719) (by norm_num)
theorem B826453 : Blo 578813 826453 := bbase (se 8 (by rfl) ⟨4842, by rfl⟩ : syracuseStep 826453 = 9685) (by norm_num)
theorem B695633 : Blo 578813 695633 := bbase (se 2 (by rfl) ⟨260862, by rfl⟩ : syracuseStep 695633 = 521725) (by norm_num)
theorem B630137 : Blo 578813 630137 := bbase (se 2 (by rfl) ⟨236301, by rfl⟩ : syracuseStep 630137 = 472603) (by norm_num)
theorem B826789 : Blo 578813 826789 := bbase (se 4 (by rfl) ⟨77511, by rfl⟩ : syracuseStep 826789 = 155023) (by norm_num)
theorem B827005 : Blo 578813 827005 := bbase (se 3 (by rfl) ⟨155063, by rfl⟩ : syracuseStep 827005 = 310127) (by norm_num)
theorem B2989781 : Blo 578813 2989781 := bbase (se 7 (by rfl) ⟨35036, by rfl⟩ : syracuseStep 2989781 = 70073) (by norm_num)
theorem B597785 : Blo 578813 597785 := bbase (se 2 (by rfl) ⟨224169, by rfl⟩ : syracuseStep 597785 = 448339) (by norm_num)
theorem B827381 : Blo 578813 827381 := bbase (se 5 (by rfl) ⟨38783, by rfl⟩ : syracuseStep 827381 = 77567) (by norm_num)
theorem B696325 : Blo 578813 696325 := bbase (se 4 (by rfl) ⟨65280, by rfl⟩ : syracuseStep 696325 = 130561) (by norm_num)
theorem B1450037 : Blo 578813 1450037 := bbase (se 5 (by rfl) ⟨67970, by rfl⟩ : syracuseStep 1450037 = 135941) (by norm_num)
theorem B696421 : Blo 578813 696421 := bbase (se 4 (by rfl) ⟨65289, by rfl⟩ : syracuseStep 696421 = 130579) (by norm_num)
theorem B5578901 : Blo 578813 5578901 := bbase (se 6 (by rfl) ⟨130755, by rfl⟩ : syracuseStep 5578901 = 261511) (by norm_num)
theorem B2204117 : Blo 578813 2204117 := bbase (se 7 (by rfl) ⟨25829, by rfl⟩ : syracuseStep 2204117 = 51659) (by norm_num)
theorem B2204405 : Blo 578813 2204405 := bbase (se 5 (by rfl) ⟨103331, by rfl⟩ : syracuseStep 2204405 = 206663) (by norm_num)
theorem B697205 : Blo 578813 697205 := bbase (se 5 (by rfl) ⟨32681, by rfl⟩ : syracuseStep 697205 = 65363) (by norm_num)
theorem B4957109 : Blo 578813 4957109 := bbase (se 5 (by rfl) ⟨232364, by rfl⟩ : syracuseStep 4957109 = 464729) (by norm_num)
theorem B5022805 : Blo 578813 5022805 := bbase (se 8 (by rfl) ⟨29430, by rfl⟩ : syracuseStep 5022805 = 58861) (by norm_num)
theorem B697513 : Blo 578813 697513 := bbase (se 2 (by rfl) ⟨261567, by rfl⟩ : syracuseStep 697513 = 523135) (by norm_num)
theorem B828805 : Blo 578813 828805 := bbase (se 4 (by rfl) ⟨77700, by rfl⟩ : syracuseStep 828805 = 155401) (by norm_num)
theorem B927229 : Blo 578813 927229 := bbase (se 3 (by rfl) ⟨173855, by rfl⟩ : syracuseStep 927229 = 347711) (by norm_num)
theorem B697901 : Blo 578813 697901 := bbase (se 3 (by rfl) ⟨130856, by rfl⟩ : syracuseStep 697901 = 261713) (by norm_num)
theorem B1320581 : Blo 578813 1320581 := bbase (se 4 (by rfl) ⟨123804, by rfl⟩ : syracuseStep 1320581 = 247609) (by norm_num)
theorem B2795141 : Blo 578813 2795141 := bbase (se 4 (by rfl) ⟨262044, by rfl⟩ : syracuseStep 2795141 = 524089) (by norm_num)
theorem B927613 : Blo 578813 927613 := bbase (se 3 (by rfl) ⟨173927, by rfl⟩ : syracuseStep 927613 = 347855) (by norm_num)
theorem B698257 : Blo 578813 698257 := bbase (se 2 (by rfl) ⟨261846, by rfl⟩ : syracuseStep 698257 = 523693) (by norm_num)
theorem B2205589 : Blo 578813 2205589 := bbase (se 6 (by rfl) ⟨51693, by rfl⟩ : syracuseStep 2205589 = 103387) (by norm_num)
theorem B829397 : Blo 578813 829397 := bbase (se 7 (by rfl) ⟨9719, by rfl⟩ : syracuseStep 829397 = 19439) (by norm_num)
theorem B829477 : Blo 578813 829477 := bbase (se 4 (by rfl) ⟨77763, by rfl⟩ : syracuseStep 829477 = 155527) (by norm_num)
theorem B8366165 : Blo 578813 8366165 := bbase (se 8 (by rfl) ⟨49020, by rfl⟩ : syracuseStep 8366165 = 98041) (by norm_num)
theorem B927869 : Blo 578813 927869 := bbase (se 3 (by rfl) ⟨173975, by rfl⟩ : syracuseStep 927869 = 347951) (by norm_num)
theorem B6629525 : Blo 578813 6629525 := bbase (se 6 (by rfl) ⟨155379, by rfl⟩ : syracuseStep 6629525 = 310759) (by norm_num)
theorem B829597 : Blo 578813 829597 := bbase (se 3 (by rfl) ⟨155549, by rfl⟩ : syracuseStep 829597 = 311099) (by norm_num)
theorem B2205893 : Blo 578813 2205893 := bbase (se 4 (by rfl) ⟨206802, by rfl⟩ : syracuseStep 2205893 = 413605) (by norm_num)
theorem B698593 : Blo 578813 698593 := bbase (se 2 (by rfl) ⟨261972, by rfl⟩ : syracuseStep 698593 = 523945) (by norm_num)
theorem B829693 : Blo 578813 829693 := bbase (se 3 (by rfl) ⟨155567, by rfl⟩ : syracuseStep 829693 = 311135) (by norm_num)
theorem B1059149 : Blo 578813 1059149 := bbase (se 3 (by rfl) ⟨198590, by rfl⟩ : syracuseStep 1059149 = 397181) (by norm_num)
theorem B1649317 : Blo 578813 1649317 := bbase (se 4 (by rfl) ⟨154623, by rfl⟩ : syracuseStep 1649317 = 309247) (by norm_num)
theorem B994069 : Blo 578813 994069 := bbase (se 6 (by rfl) ⟨23298, by rfl⟩ : syracuseStep 994069 = 46597) (by norm_num)
theorem B1649477 : Blo 578813 1649477 := bbase (se 4 (by rfl) ⟨154638, by rfl⟩ : syracuseStep 1649477 = 309277) (by norm_num)
theorem B928741 : Blo 578813 928741 := bbase (se 4 (by rfl) ⟨87069, by rfl⟩ : syracuseStep 928741 = 174139) (by norm_num)
theorem B2796565 : Blo 578813 2796565 := bbase (se 6 (by rfl) ⟨65544, by rfl⟩ : syracuseStep 2796565 = 131089) (by norm_num)
theorem B1649717 : Blo 578813 1649717 := bbase (se 5 (by rfl) ⟨77330, by rfl⟩ : syracuseStep 1649717 = 154661) (by norm_num)
theorem B928837 : Blo 578813 928837 := bbase (se 4 (by rfl) ⟨87078, by rfl⟩ : syracuseStep 928837 = 174157) (by norm_num)
theorem B699473 : Blo 578813 699473 := bbase (se 2 (by rfl) ⟨262302, by rfl⟩ : syracuseStep 699473 = 524605) (by norm_num)
theorem B928997 : Blo 578813 928997 := bbase (se 4 (by rfl) ⟨87093, by rfl⟩ : syracuseStep 928997 = 174187) (by norm_num)
theorem B1649909 : Blo 578813 1649909 := bbase (se 5 (by rfl) ⟨77339, by rfl⟩ : syracuseStep 1649909 = 154679) (by norm_num)
theorem B699781 : Blo 578813 699781 := bbase (se 4 (by rfl) ⟨65604, by rfl⟩ : syracuseStep 699781 = 131209) (by norm_num)
theorem B732665 : Blo 578813 732665 := bbase (se 2 (by rfl) ⟨274749, by rfl⟩ : syracuseStep 732665 = 549499) (by norm_num)
theorem B732721 : Blo 578813 732721 := bbase (se 2 (by rfl) ⟨274770, by rfl⟩ : syracuseStep 732721 = 549541) (by norm_num)
theorem B732817 : Blo 578813 732817 := bbase (se 2 (by rfl) ⟨274806, by rfl⟩ : syracuseStep 732817 = 549613) (by norm_num)
theorem B700165 : Blo 578813 700165 := bbase (se 4 (by rfl) ⟨65640, by rfl⟩ : syracuseStep 700165 = 131281) (by norm_num)
theorem B732989 : Blo 578813 732989 := bbase (se 3 (by rfl) ⟨137435, by rfl⟩ : syracuseStep 732989 = 274871) (by norm_num)
theorem B2862917 : Blo 578813 2862917 := bbase (se 4 (by rfl) ⟨268398, by rfl⟩ : syracuseStep 2862917 = 536797) (by norm_num)
theorem B733045 : Blo 578813 733045 := bbase (se 5 (by rfl) ⟨34361, by rfl⟩ : syracuseStep 733045 = 68723) (by norm_num)
theorem B733141 : Blo 578813 733141 := bbase (se 7 (by rfl) ⟨8591, by rfl⟩ : syracuseStep 733141 = 17183) (by norm_num)
theorem B733313 : Blo 578813 733313 := bbase (se 2 (by rfl) ⟨274992, by rfl⟩ : syracuseStep 733313 = 549985) (by norm_num)
theorem B897173 : Blo 578813 897173 := bbase (se 6 (by rfl) ⟨21027, by rfl⟩ : syracuseStep 897173 = 42055) (by norm_num)
theorem B733369 : Blo 578813 733369 := bbase (se 2 (by rfl) ⟨275013, by rfl⟩ : syracuseStep 733369 = 550027) (by norm_num)
theorem B1650901 : Blo 578813 1650901 := bbase (se 7 (by rfl) ⟨19346, by rfl⟩ : syracuseStep 1650901 = 38693) (by norm_num)
theorem B2208005 : Blo 578813 2208005 := bbase (se 4 (by rfl) ⟨207000, by rfl⟩ : syracuseStep 2208005 = 414001) (by norm_num)
theorem B733465 : Blo 578813 733465 := bbase (se 2 (by rfl) ⟨275049, by rfl⟩ : syracuseStep 733465 = 550099) (by norm_num)
theorem B1323317 : Blo 578813 1323317 := bbase (se 5 (by rfl) ⟨62030, by rfl⟩ : syracuseStep 1323317 = 124061) (by norm_num)
theorem B930125 : Blo 578813 930125 := bbase (se 3 (by rfl) ⟨174398, by rfl⟩ : syracuseStep 930125 = 348797) (by norm_num)
theorem B733637 : Blo 578813 733637 := bbase (se 4 (by rfl) ⟨68778, by rfl⟩ : syracuseStep 733637 = 137557) (by norm_num)
theorem B733693 : Blo 578813 733693 := bbase (se 3 (by rfl) ⟨137567, by rfl⟩ : syracuseStep 733693 = 275135) (by norm_num)
theorem B2208293 : Blo 578813 2208293 := bbase (se 4 (by rfl) ⟨207027, by rfl⟩ : syracuseStep 2208293 = 414055) (by norm_num)
theorem B733789 : Blo 578813 733789 := bbase (se 3 (by rfl) ⟨137585, by rfl⟩ : syracuseStep 733789 = 275171) (by norm_num)
theorem B733961 : Blo 578813 733961 := bbase (se 2 (by rfl) ⟨275235, by rfl⟩ : syracuseStep 733961 = 550471) (by norm_num)
theorem B734017 : Blo 578813 734017 := bbase (se 2 (by rfl) ⟨275256, by rfl⟩ : syracuseStep 734017 = 550513) (by norm_num)
theorem B930637 : Blo 578813 930637 := bbase (se 3 (by rfl) ⟨174494, by rfl⟩ : syracuseStep 930637 = 348989) (by norm_num)
theorem B734113 : Blo 578813 734113 := bbase (se 2 (by rfl) ⟨275292, by rfl⟩ : syracuseStep 734113 = 550585) (by norm_num)
theorem B1586117 : Blo 578813 1586117 := bbase (se 4 (by rfl) ⟨148698, by rfl⟩ : syracuseStep 1586117 = 297397) (by norm_num)
theorem B734285 : Blo 578813 734285 := bbase (se 3 (by rfl) ⟨137678, by rfl⟩ : syracuseStep 734285 = 275357) (by norm_num)
theorem B9942101 : Blo 578813 9942101 := bbase (se 8 (by rfl) ⟨58254, by rfl⟩ : syracuseStep 9942101 = 116509) (by norm_num)
theorem B734341 : Blo 578813 734341 := bbase (se 4 (by rfl) ⟨68844, by rfl⟩ : syracuseStep 734341 = 137689) (by norm_num)
theorem B4240565 : Blo 578813 4240565 := bbase (se 5 (by rfl) ⟨198776, by rfl⟩ : syracuseStep 4240565 = 397553) (by norm_num)
theorem B734437 : Blo 578813 734437 := bbase (se 4 (by rfl) ⟨68853, by rfl⟩ : syracuseStep 734437 = 137707) (by norm_num)
theorem B1652005 : Blo 578813 1652005 := bbase (se 4 (by rfl) ⟨154875, by rfl⟩ : syracuseStep 1652005 = 309751) (by norm_num)
theorem B734609 : Blo 578813 734609 := bbase (se 2 (by rfl) ⟨275478, by rfl⟩ : syracuseStep 734609 = 550957) (by norm_num)
theorem B734665 : Blo 578813 734665 := bbase (se 2 (by rfl) ⟨275499, by rfl⟩ : syracuseStep 734665 = 550999) (by norm_num)
theorem B734761 : Blo 578813 734761 := bbase (se 2 (by rfl) ⟨275535, by rfl⟩ : syracuseStep 734761 = 551071) (by norm_num)
theorem B2209477 : Blo 578813 2209477 := bbase (se 4 (by rfl) ⟨207138, by rfl⟩ : syracuseStep 2209477 = 414277) (by norm_num)
theorem B734933 : Blo 578813 734933 := bbase (se 7 (by rfl) ⟨8612, by rfl⟩ : syracuseStep 734933 = 17225) (by norm_num)
theorem B2897669 : Blo 578813 2897669 := bbase (se 4 (by rfl) ⟨271656, by rfl⟩ : syracuseStep 2897669 = 543313) (by norm_num)
theorem B1357573 : Blo 578813 1357573 := bbase (se 4 (by rfl) ⟨127272, by rfl⟩ : syracuseStep 1357573 = 254545) (by norm_num)
theorem B734989 : Blo 578813 734989 := bbase (se 3 (by rfl) ⟨137810, by rfl⟩ : syracuseStep 734989 = 275621) (by norm_num)
theorem B931637 : Blo 578813 931637 := bbase (se 5 (by rfl) ⟨43670, by rfl⟩ : syracuseStep 931637 = 87341) (by norm_num)
theorem B735085 : Blo 578813 735085 := bbase (se 3 (by rfl) ⟨137828, by rfl⟩ : syracuseStep 735085 = 275657) (by norm_num)
theorem B931765 : Blo 578813 931765 := bbase (se 5 (by rfl) ⟨43676, by rfl⟩ : syracuseStep 931765 = 87353) (by norm_num)
theorem B931829 : Blo 578813 931829 := bbase (se 5 (by rfl) ⟨43679, by rfl⟩ : syracuseStep 931829 = 87359) (by norm_num)
theorem B2209781 : Blo 578813 2209781 := bbase (se 5 (by rfl) ⟨103583, by rfl⟩ : syracuseStep 2209781 = 207167) (by norm_num)
theorem B735257 : Blo 578813 735257 := bbase (se 2 (by rfl) ⟨275721, by rfl⟩ : syracuseStep 735257 = 551443) (by norm_num)
theorem B2930741 : Blo 578813 2930741 := bbase (se 5 (by rfl) ⟨137378, by rfl⟩ : syracuseStep 2930741 = 274757) (by norm_num)
theorem B735313 : Blo 578813 735313 := bbase (se 2 (by rfl) ⟨275742, by rfl⟩ : syracuseStep 735313 = 551485) (by norm_num)
theorem B7944277 : Blo 578813 7944277 := bbase (se 8 (by rfl) ⟨46548, by rfl⟩ : syracuseStep 7944277 = 93097) (by norm_num)
theorem B735409 : Blo 578813 735409 := bbase (se 2 (by rfl) ⟨275778, by rfl⟩ : syracuseStep 735409 = 551557) (by norm_num)
theorem B4405589 : Blo 578813 4405589 := bbase (se 10 (by rfl) ⟨6453, by rfl⟩ : syracuseStep 4405589 = 12907) (by norm_num)
theorem B188627285 : Blo 578813 188627285 := bbase (se 10 (by rfl) ⟨276309, by rfl⟩ : syracuseStep 188627285 = 552619) (by norm_num)
theorem B735581 : Blo 578813 735581 := bbase (se 3 (by rfl) ⟨137921, by rfl⟩ : syracuseStep 735581 = 275843) (by norm_num)
theorem B735637 : Blo 578813 735637 := bbase (se 6 (by rfl) ⟨17241, by rfl⟩ : syracuseStep 735637 = 34483) (by norm_num)
theorem B735733 : Blo 578813 735733 := bbase (se 5 (by rfl) ⟨34487, by rfl⟩ : syracuseStep 735733 = 68975) (by norm_num)
theorem B735905 : Blo 578813 735905 := bbase (se 2 (by rfl) ⟨275964, by rfl⟩ : syracuseStep 735905 = 551929) (by norm_num)
theorem B735961 : Blo 578813 735961 := bbase (se 2 (by rfl) ⟨275985, by rfl⟩ : syracuseStep 735961 = 551971) (by norm_num)
theorem B2472677 : Blo 578813 2472677 := bbase (se 4 (by rfl) ⟨231813, by rfl⟩ : syracuseStep 2472677 = 463627) (by norm_num)
theorem B1653509 : Blo 578813 1653509 := bbase (se 4 (by rfl) ⟨155016, by rfl⟩ : syracuseStep 1653509 = 310033) (by norm_num)
theorem B736057 : Blo 578813 736057 := bbase (se 2 (by rfl) ⟨276021, by rfl⟩ : syracuseStep 736057 = 552043) (by norm_num)
theorem B3718037 : Blo 578813 3718037 := bbase (se 6 (by rfl) ⟨87141, by rfl⟩ : syracuseStep 3718037 = 174283) (by norm_num)
theorem B736229 : Blo 578813 736229 := bbase (se 4 (by rfl) ⟨69021, by rfl⟩ : syracuseStep 736229 = 138043) (by norm_num)
theorem B736285 : Blo 578813 736285 := bbase (se 3 (by rfl) ⟨138053, by rfl⟩ : syracuseStep 736285 = 276107) (by norm_num)
theorem B1326181 : Blo 578813 1326181 := bbase (se 4 (by rfl) ⟨124329, by rfl⟩ : syracuseStep 1326181 = 248659) (by norm_num)
theorem B736381 : Blo 578813 736381 := bbase (se 3 (by rfl) ⟨138071, by rfl⟩ : syracuseStep 736381 = 276143) (by norm_num)
theorem B933125 : Blo 578813 933125 := bbase (se 4 (by rfl) ⟨87480, by rfl⟩ : syracuseStep 933125 = 174961) (by norm_num)
theorem B933149 : Blo 578813 933149 := bbase (se 3 (by rfl) ⟨174965, by rfl⟩ : syracuseStep 933149 = 349931) (by norm_num)
theorem B736553 : Blo 578813 736553 := bbase (se 2 (by rfl) ⟨276207, by rfl⟩ : syracuseStep 736553 = 552415) (by norm_num)
theorem B2932037 : Blo 578813 2932037 := bbase (se 4 (by rfl) ⟨274878, by rfl⟩ : syracuseStep 2932037 = 549757) (by norm_num)
theorem B736609 : Blo 578813 736609 := bbase (se 2 (by rfl) ⟨276228, by rfl⟩ : syracuseStep 736609 = 552457) (by norm_num)
theorem B1981829 : Blo 578813 1981829 := bbase (se 4 (by rfl) ⟨185796, by rfl⟩ : syracuseStep 1981829 = 371593) (by norm_num)
theorem B933277 : Blo 578813 933277 := bbase (se 3 (by rfl) ⟨174989, by rfl⟩ : syracuseStep 933277 = 349979) (by norm_num)
theorem B736705 : Blo 578813 736705 := bbase (se 2 (by rfl) ⟨276264, by rfl⟩ : syracuseStep 736705 = 552529) (by norm_num)
theorem B2473429 : Blo 578813 2473429 := bbase (se 7 (by rfl) ⟨28985, by rfl⟩ : syracuseStep 2473429 = 57971) (by norm_num)
theorem B736877 : Blo 578813 736877 := bbase (se 3 (by rfl) ⟨138164, by rfl⟩ : syracuseStep 736877 = 276329) (by norm_num)
theorem B6274709 : Blo 578813 6274709 := bbase (se 6 (by rfl) ⟨147063, by rfl⟩ : syracuseStep 6274709 = 294127) (by norm_num)
theorem B736933 : Blo 578813 736933 := bbase (se 4 (by rfl) ⟨69087, by rfl⟩ : syracuseStep 736933 = 138175) (by norm_num)
theorem B737029 : Blo 578813 737029 := bbase (se 4 (by rfl) ⟨69096, by rfl⟩ : syracuseStep 737029 = 138193) (by norm_num)
theorem B3030901 : Blo 578813 3030901 := bbase (se 5 (by rfl) ⟨142073, by rfl⟩ : syracuseStep 3030901 = 284147) (by norm_num)
theorem B868229 : Blo 578813 868229 := bbase (se 4 (by rfl) ⟨81396, by rfl⟩ : syracuseStep 868229 = 162793) (by norm_num)
theorem B868253 : Blo 578813 868253 := bbase (se 3 (by rfl) ⟨162797, by rfl⟩ : syracuseStep 868253 = 325595) (by norm_num)
theorem B737201 : Blo 578813 737201 := bbase (se 2 (by rfl) ⟨276450, by rfl⟩ : syracuseStep 737201 = 552901) (by norm_num)
theorem B868277 : Blo 578813 868277 := bbase (se 5 (by rfl) ⟨40700, by rfl⟩ : syracuseStep 868277 = 81401) (by norm_num)
theorem B1392565 : Blo 578813 1392565 := bbase (se 5 (by rfl) ⟨65276, by rfl⟩ : syracuseStep 1392565 = 130553) (by norm_num)
theorem B868301 : Blo 578813 868301 := bbase (se 3 (by rfl) ⟨162806, by rfl⟩ : syracuseStep 868301 = 325613) (by norm_num)
theorem B868325 : Blo 578813 868325 := bbase (se 4 (by rfl) ⟨81405, by rfl⟩ : syracuseStep 868325 = 162811) (by norm_num)
theorem B737257 : Blo 578813 737257 := bbase (se 2 (by rfl) ⟨276471, by rfl⟩ : syracuseStep 737257 = 552943) (by norm_num)
theorem B868349 : Blo 578813 868349 := bbase (se 3 (by rfl) ⟨162815, by rfl⟩ : syracuseStep 868349 = 325631) (by norm_num)
theorem B868373 : Blo 578813 868373 := bbase (se 6 (by rfl) ⟨20352, by rfl⟩ : syracuseStep 868373 = 40705) (by norm_num)
theorem B868397 : Blo 578813 868397 := bbase (se 3 (by rfl) ⟨162824, by rfl⟩ : syracuseStep 868397 = 325649) (by norm_num)
theorem B2211893 : Blo 578813 2211893 := bbase (se 5 (by rfl) ⟨103682, by rfl⟩ : syracuseStep 2211893 = 207365) (by norm_num)
theorem B868421 : Blo 578813 868421 := bbase (se 4 (by rfl) ⟨81414, by rfl⟩ : syracuseStep 868421 = 162829) (by norm_num)
theorem B737353 : Blo 578813 737353 := bbase (se 2 (by rfl) ⟨276507, by rfl⟩ : syracuseStep 737353 = 553015) (by norm_num)
theorem B1491029 : Blo 578813 1491029 := bbase (se 8 (by rfl) ⟨8736, by rfl⟩ : syracuseStep 1491029 = 17473) (by norm_num)
theorem B868445 : Blo 578813 868445 := bbase (se 3 (by rfl) ⟨162833, by rfl⟩ : syracuseStep 868445 = 325667) (by norm_num)
theorem B868469 : Blo 578813 868469 := bbase (se 5 (by rfl) ⟨40709, by rfl⟩ : syracuseStep 868469 = 81419) (by norm_num)
theorem B868493 : Blo 578813 868493 := bbase (se 3 (by rfl) ⟨162842, by rfl⟩ : syracuseStep 868493 = 325685) (by norm_num)
theorem B868517 : Blo 578813 868517 := bbase (se 4 (by rfl) ⟨81423, by rfl⟩ : syracuseStep 868517 = 162847) (by norm_num)
theorem B2474165 : Blo 578813 2474165 := bbase (se 5 (by rfl) ⟨115976, by rfl⟩ : syracuseStep 2474165 = 231953) (by norm_num)
theorem B868541 : Blo 578813 868541 := bbase (se 3 (by rfl) ⟨162851, by rfl⟩ : syracuseStep 868541 = 325703) (by norm_num)
theorem B868565 : Blo 578813 868565 := bbase (se 7 (by rfl) ⟨10178, by rfl⟩ : syracuseStep 868565 = 20357) (by norm_num)
theorem B868589 : Blo 578813 868589 := bbase (se 3 (by rfl) ⟨162860, by rfl⟩ : syracuseStep 868589 = 325721) (by norm_num)
theorem B737525 : Blo 578813 737525 := bbase (se 5 (by rfl) ⟨34571, by rfl⟩ : syracuseStep 737525 = 69143) (by norm_num)
theorem B868613 : Blo 578813 868613 := bbase (se 4 (by rfl) ⟨81432, by rfl⟩ : syracuseStep 868613 = 162865) (by norm_num)
theorem B868637 : Blo 578813 868637 := bbase (se 3 (by rfl) ⟨162869, by rfl⟩ : syracuseStep 868637 = 325739) (by norm_num)
theorem B737581 : Blo 578813 737581 := bbase (se 3 (by rfl) ⟨138296, by rfl⟩ : syracuseStep 737581 = 276593) (by norm_num)
theorem B868661 : Blo 578813 868661 := bbase (se 5 (by rfl) ⟨40718, by rfl⟩ : syracuseStep 868661 = 81437) (by norm_num)
theorem B1655093 : Blo 578813 1655093 := bbase (se 5 (by rfl) ⟨77582, by rfl⟩ : syracuseStep 1655093 = 155165) (by norm_num)
theorem B868685 : Blo 578813 868685 := bbase (se 3 (by rfl) ⟨162878, by rfl⟩ : syracuseStep 868685 = 325757) (by norm_num)
theorem B2212181 : Blo 578813 2212181 := bbase (se 10 (by rfl) ⟨3240, by rfl⟩ : syracuseStep 2212181 = 6481) (by norm_num)
theorem B868709 : Blo 578813 868709 := bbase (se 4 (by rfl) ⟨81441, by rfl⟩ : syracuseStep 868709 = 162883) (by norm_num)
theorem B606565 : Blo 578813 606565 := bbase (se 4 (by rfl) ⟨56865, by rfl⟩ : syracuseStep 606565 = 113731) (by norm_num)
theorem B868733 : Blo 578813 868733 := bbase (se 3 (by rfl) ⟨162887, by rfl⟩ : syracuseStep 868733 = 325775) (by norm_num)
theorem B868757 : Blo 578813 868757 := bbase (se 6 (by rfl) ⟨20361, by rfl⟩ : syracuseStep 868757 = 40723) (by norm_num)
theorem B868781 : Blo 578813 868781 := bbase (se 3 (by rfl) ⟨162896, by rfl⟩ : syracuseStep 868781 = 325793) (by norm_num)
theorem B868805 : Blo 578813 868805 := bbase (se 4 (by rfl) ⟨81450, by rfl⟩ : syracuseStep 868805 = 162901) (by norm_num)
theorem B868829 : Blo 578813 868829 := bbase (se 3 (by rfl) ⟨162905, by rfl⟩ : syracuseStep 868829 = 325811) (by norm_num)
theorem B868853 : Blo 578813 868853 := bbase (se 5 (by rfl) ⟨40727, by rfl⟩ : syracuseStep 868853 = 81455) (by norm_num)
theorem B868877 : Blo 578813 868877 := bbase (se 3 (by rfl) ⟨162914, by rfl⟩ : syracuseStep 868877 = 325829) (by norm_num)
theorem B868901 : Blo 578813 868901 := bbase (se 4 (by rfl) ⟨81459, by rfl⟩ : syracuseStep 868901 = 162919) (by norm_num)
theorem B705085 : Blo 578813 705085 := bbase (se 3 (by rfl) ⟨132203, by rfl⟩ : syracuseStep 705085 = 264407) (by norm_num)
theorem B868925 : Blo 578813 868925 := bbase (se 3 (by rfl) ⟨162923, by rfl⟩ : syracuseStep 868925 = 325847) (by norm_num)
theorem B868949 : Blo 578813 868949 := bbase (se 8 (by rfl) ⟨5091, by rfl⟩ : syracuseStep 868949 = 10183) (by norm_num)
theorem B2933333 : Blo 578813 2933333 := bbase (se 8 (by rfl) ⟨17187, by rfl⟩ : syracuseStep 2933333 = 34375) (by norm_num)
theorem B868973 : Blo 578813 868973 := bbase (se 3 (by rfl) ⟨162932, by rfl⟩ : syracuseStep 868973 = 325865) (by norm_num)
theorem B868997 : Blo 578813 868997 := bbase (se 4 (by rfl) ⟨81468, by rfl⟩ : syracuseStep 868997 = 162937) (by norm_num)
theorem B869021 : Blo 578813 869021 := bbase (se 3 (by rfl) ⟨162941, by rfl⟩ : syracuseStep 869021 = 325883) (by norm_num)
theorem B869045 : Blo 578813 869045 := bbase (se 5 (by rfl) ⟨40736, by rfl⟩ : syracuseStep 869045 = 81473) (by norm_num)
theorem B869069 : Blo 578813 869069 := bbase (se 3 (by rfl) ⟨162950, by rfl⟩ : syracuseStep 869069 = 325901) (by norm_num)
theorem B869093 : Blo 578813 869093 := bbase (se 4 (by rfl) ⟨81477, by rfl⟩ : syracuseStep 869093 = 162955) (by norm_num)
theorem B869117 : Blo 578813 869117 := bbase (se 3 (by rfl) ⟨162959, by rfl⟩ : syracuseStep 869117 = 325919) (by norm_num)
theorem B869141 : Blo 578813 869141 := bbase (se 6 (by rfl) ⟨20370, by rfl⟩ : syracuseStep 869141 = 40741) (by norm_num)
theorem B869165 : Blo 578813 869165 := bbase (se 3 (by rfl) ⟨162968, by rfl⟩ : syracuseStep 869165 = 325937) (by norm_num)
theorem B869189 : Blo 578813 869189 := bbase (se 4 (by rfl) ⟨81486, by rfl⟩ : syracuseStep 869189 = 162973) (by norm_num)
theorem B869213 : Blo 578813 869213 := bbase (se 3 (by rfl) ⟨162977, by rfl⟩ : syracuseStep 869213 = 325955) (by norm_num)
theorem B869237 : Blo 578813 869237 := bbase (se 5 (by rfl) ⟨40745, by rfl⟩ : syracuseStep 869237 = 81491) (by norm_num)
theorem B869261 : Blo 578813 869261 := bbase (se 3 (by rfl) ⟨162986, by rfl⟩ : syracuseStep 869261 = 325973) (by norm_num)
theorem B1491853 : Blo 578813 1491853 := bbase (se 3 (by rfl) ⟨279722, by rfl⟩ : syracuseStep 1491853 = 559445) (by norm_num)
theorem B869285 : Blo 578813 869285 := bbase (se 4 (by rfl) ⟨81495, by rfl⟩ : syracuseStep 869285 = 162991) (by norm_num)
theorem B869309 : Blo 578813 869309 := bbase (se 3 (by rfl) ⟨162995, by rfl⟩ : syracuseStep 869309 = 325991) (by norm_num)
theorem B869333 : Blo 578813 869333 := bbase (se 7 (by rfl) ⟨10187, by rfl⟩ : syracuseStep 869333 = 20375) (by norm_num)
theorem B1655765 : Blo 578813 1655765 := bbase (se 7 (by rfl) ⟨19403, by rfl⟩ : syracuseStep 1655765 = 38807) (by norm_num)
theorem B869357 : Blo 578813 869357 := bbase (se 3 (by rfl) ⟨163004, by rfl⟩ : syracuseStep 869357 = 326009) (by norm_num)
theorem B869381 : Blo 578813 869381 := bbase (se 4 (by rfl) ⟨81504, by rfl⟩ : syracuseStep 869381 = 163009) (by norm_num)
theorem B869405 : Blo 578813 869405 := bbase (se 3 (by rfl) ⟨163013, by rfl⟩ : syracuseStep 869405 = 326027) (by norm_num)
theorem B869429 : Blo 578813 869429 := bbase (se 5 (by rfl) ⟨40754, by rfl⟩ : syracuseStep 869429 = 81509) (by norm_num)
theorem B705613 : Blo 578813 705613 := bbase (se 3 (by rfl) ⟨132302, by rfl⟩ : syracuseStep 705613 = 264605) (by norm_num)
theorem B869453 : Blo 578813 869453 := bbase (se 3 (by rfl) ⟨163022, by rfl⟩ : syracuseStep 869453 = 326045) (by norm_num)
theorem B869477 : Blo 578813 869477 := bbase (se 4 (by rfl) ⟨81513, by rfl⟩ : syracuseStep 869477 = 163027) (by norm_num)
theorem B869501 : Blo 578813 869501 := bbase (se 3 (by rfl) ⟨163031, by rfl⟩ : syracuseStep 869501 = 326063) (by norm_num)
theorem B869525 : Blo 578813 869525 := bbase (se 6 (by rfl) ⟨20379, by rfl⟩ : syracuseStep 869525 = 40759) (by norm_num)
theorem B869549 : Blo 578813 869549 := bbase (se 3 (by rfl) ⟨163040, by rfl⟩ : syracuseStep 869549 = 326081) (by norm_num)
theorem B869573 : Blo 578813 869573 := bbase (se 4 (by rfl) ⟨81522, by rfl⟩ : syracuseStep 869573 = 163045) (by norm_num)
theorem B869597 : Blo 578813 869597 := bbase (se 3 (by rfl) ⟨163049, by rfl⟩ : syracuseStep 869597 = 326099) (by norm_num)
theorem B869621 : Blo 578813 869621 := bbase (se 5 (by rfl) ⟨40763, by rfl⟩ : syracuseStep 869621 = 81527) (by norm_num)
theorem B1099021 : Blo 578813 1099021 := bbase (se 3 (by rfl) ⟨206066, by rfl⟩ : syracuseStep 1099021 = 412133) (by norm_num)
theorem B869645 : Blo 578813 869645 := bbase (se 3 (by rfl) ⟨163058, by rfl⟩ : syracuseStep 869645 = 326117) (by norm_num)
theorem B4179221 : Blo 578813 4179221 := bbase (se 6 (by rfl) ⟨97950, by rfl⟩ : syracuseStep 4179221 = 195901) (by norm_num)
theorem B869669 : Blo 578813 869669 := bbase (se 4 (by rfl) ⟨81531, by rfl⟩ : syracuseStep 869669 = 163063) (by norm_num)
theorem B869693 : Blo 578813 869693 := bbase (se 3 (by rfl) ⟨163067, by rfl⟩ : syracuseStep 869693 = 326135) (by norm_num)
theorem B869717 : Blo 578813 869717 := bbase (se 12 (by rfl) ⟨318, by rfl⟩ : syracuseStep 869717 = 637) (by norm_num)
theorem B869741 : Blo 578813 869741 := bbase (se 3 (by rfl) ⟨163076, by rfl⟩ : syracuseStep 869741 = 326153) (by norm_num)
theorem B869765 : Blo 578813 869765 := bbase (se 4 (by rfl) ⟨81540, by rfl⟩ : syracuseStep 869765 = 163081) (by norm_num)
theorem B1656197 : Blo 578813 1656197 := bbase (se 4 (by rfl) ⟨155268, by rfl⟩ : syracuseStep 1656197 = 310537) (by norm_num)
theorem B1099165 : Blo 578813 1099165 := bbase (se 3 (by rfl) ⟨206093, by rfl⟩ : syracuseStep 1099165 = 412187) (by norm_num)
theorem B869789 : Blo 578813 869789 := bbase (se 3 (by rfl) ⟨163085, by rfl⟩ : syracuseStep 869789 = 326171) (by norm_num)
theorem B869813 : Blo 578813 869813 := bbase (se 5 (by rfl) ⟨40772, by rfl⟩ : syracuseStep 869813 = 81545) (by norm_num)
theorem B869837 : Blo 578813 869837 := bbase (se 3 (by rfl) ⟨163094, by rfl⟩ : syracuseStep 869837 = 326189) (by norm_num)
theorem B869861 : Blo 578813 869861 := bbase (se 4 (by rfl) ⟨81549, by rfl⟩ : syracuseStep 869861 = 163099) (by norm_num)
theorem B1492469 : Blo 578813 1492469 := bbase (se 5 (by rfl) ⟨69959, by rfl⟩ : syracuseStep 1492469 = 139919) (by norm_num)
theorem B869885 : Blo 578813 869885 := bbase (se 3 (by rfl) ⟨163103, by rfl⟩ : syracuseStep 869885 = 326207) (by norm_num)
theorem B869909 : Blo 578813 869909 := bbase (se 6 (by rfl) ⟨20388, by rfl⟩ : syracuseStep 869909 = 40777) (by norm_num)
theorem B869933 : Blo 578813 869933 := bbase (se 3 (by rfl) ⟨163112, by rfl⟩ : syracuseStep 869933 = 326225) (by norm_num)
theorem B1099325 : Blo 578813 1099325 := bbase (se 3 (by rfl) ⟨206123, by rfl⟩ : syracuseStep 1099325 = 412247) (by norm_num)
theorem B869957 : Blo 578813 869957 := bbase (se 4 (by rfl) ⟨81558, by rfl⟩ : syracuseStep 869957 = 163117) (by norm_num)
theorem B869981 : Blo 578813 869981 := bbase (se 3 (by rfl) ⟨163121, by rfl⟩ : syracuseStep 869981 = 326243) (by norm_num)
theorem B870005 : Blo 578813 870005 := bbase (se 5 (by rfl) ⟨40781, by rfl⟩ : syracuseStep 870005 = 81563) (by norm_num)
theorem B870029 : Blo 578813 870029 := bbase (se 3 (by rfl) ⟨163130, by rfl⟩ : syracuseStep 870029 = 326261) (by norm_num)
theorem B870053 : Blo 578813 870053 := bbase (se 4 (by rfl) ⟨81567, by rfl⟩ : syracuseStep 870053 = 163135) (by norm_num)
theorem B870077 : Blo 578813 870077 := bbase (se 3 (by rfl) ⟨163139, by rfl⟩ : syracuseStep 870077 = 326279) (by norm_num)
theorem B1099469 : Blo 578813 1099469 := bbase (se 3 (by rfl) ⟨206150, by rfl⟩ : syracuseStep 1099469 = 412301) (by norm_num)
theorem B870101 : Blo 578813 870101 := bbase (se 7 (by rfl) ⟨10196, by rfl⟩ : syracuseStep 870101 = 20393) (by norm_num)
theorem B4703957 : Blo 578813 4703957 := bbase (se 7 (by rfl) ⟨55124, by rfl⟩ : syracuseStep 4703957 = 110249) (by norm_num)
theorem B870125 : Blo 578813 870125 := bbase (se 3 (by rfl) ⟨163148, by rfl⟩ : syracuseStep 870125 = 326297) (by norm_num)
theorem B870149 : Blo 578813 870149 := bbase (se 4 (by rfl) ⟨81576, by rfl⟩ : syracuseStep 870149 = 163153) (by norm_num)
theorem B870173 : Blo 578813 870173 := bbase (se 3 (by rfl) ⟨163157, by rfl⟩ : syracuseStep 870173 = 326315) (by norm_num)
theorem B870197 : Blo 578813 870197 := bbase (se 5 (by rfl) ⟨40790, by rfl⟩ : syracuseStep 870197 = 81581) (by norm_num)
theorem B870221 : Blo 578813 870221 := bbase (se 3 (by rfl) ⟨163166, by rfl⟩ : syracuseStep 870221 = 326333) (by norm_num)
theorem B2934629 : Blo 578813 2934629 := bbase (se 4 (by rfl) ⟨275121, by rfl⟩ : syracuseStep 2934629 = 550243) (by norm_num)
theorem B870245 : Blo 578813 870245 := bbase (se 4 (by rfl) ⟨81585, by rfl⟩ : syracuseStep 870245 = 163171) (by norm_num)
theorem B870269 : Blo 578813 870269 := bbase (se 3 (by rfl) ⟨163175, by rfl⟩ : syracuseStep 870269 = 326351) (by norm_num)
theorem B870293 : Blo 578813 870293 := bbase (se 6 (by rfl) ⟨20397, by rfl⟩ : syracuseStep 870293 = 40795) (by norm_num)
theorem B706469 : Blo 578813 706469 := bbase (se 4 (by rfl) ⟨66231, by rfl⟩ : syracuseStep 706469 = 132463) (by norm_num)
theorem B870317 : Blo 578813 870317 := bbase (se 3 (by rfl) ⟨163184, by rfl⟩ : syracuseStep 870317 = 326369) (by norm_num)
theorem B870341 : Blo 578813 870341 := bbase (se 4 (by rfl) ⟨81594, by rfl⟩ : syracuseStep 870341 = 163189) (by norm_num)
theorem B870365 : Blo 578813 870365 := bbase (se 3 (by rfl) ⟨163193, by rfl⟩ : syracuseStep 870365 = 326387) (by norm_num)
theorem B1099757 : Blo 578813 1099757 := bbase (se 3 (by rfl) ⟨206204, by rfl⟩ : syracuseStep 1099757 = 412409) (by norm_num)
theorem B870389 : Blo 578813 870389 := bbase (se 5 (by rfl) ⟨40799, by rfl⟩ : syracuseStep 870389 = 81599) (by norm_num)
theorem B870413 : Blo 578813 870413 := bbase (se 3 (by rfl) ⟨163202, by rfl⟩ : syracuseStep 870413 = 326405) (by norm_num)
theorem B870437 : Blo 578813 870437 := bbase (se 4 (by rfl) ⟨81603, by rfl⟩ : syracuseStep 870437 = 163207) (by norm_num)
theorem B870461 : Blo 578813 870461 := bbase (se 3 (by rfl) ⟨163211, by rfl⟩ : syracuseStep 870461 = 326423) (by norm_num)
theorem B870485 : Blo 578813 870485 := bbase (se 8 (by rfl) ⟨5100, by rfl⟩ : syracuseStep 870485 = 10201) (by norm_num)
theorem B870509 : Blo 578813 870509 := bbase (se 3 (by rfl) ⟨163220, by rfl⟩ : syracuseStep 870509 = 326441) (by norm_num)
theorem B1656949 : Blo 578813 1656949 := bbase (se 5 (by rfl) ⟨77669, by rfl⟩ : syracuseStep 1656949 = 155339) (by norm_num)
theorem B1099909 : Blo 578813 1099909 := bbase (se 4 (by rfl) ⟨103116, by rfl⟩ : syracuseStep 1099909 = 206233) (by norm_num)
theorem B870533 : Blo 578813 870533 := bbase (se 4 (by rfl) ⟨81612, by rfl⟩ : syracuseStep 870533 = 163225) (by norm_num)
theorem B870557 : Blo 578813 870557 := bbase (se 3 (by rfl) ⟨163229, by rfl⟩ : syracuseStep 870557 = 326459) (by norm_num)
theorem B870581 : Blo 578813 870581 := bbase (se 5 (by rfl) ⟨40808, by rfl⟩ : syracuseStep 870581 = 81617) (by norm_num)
theorem B870605 : Blo 578813 870605 := bbase (se 3 (by rfl) ⟨163238, by rfl⟩ : syracuseStep 870605 = 326477) (by norm_num)
theorem B870629 : Blo 578813 870629 := bbase (se 4 (by rfl) ⟨81621, by rfl⟩ : syracuseStep 870629 = 163243) (by norm_num)
theorem B870653 : Blo 578813 870653 := bbase (se 3 (by rfl) ⟨163247, by rfl⟩ : syracuseStep 870653 = 326495) (by norm_num)
theorem B1394957 : Blo 578813 1394957 := bbase (se 3 (by rfl) ⟨261554, by rfl⟩ : syracuseStep 1394957 = 523109) (by norm_num)
theorem B870677 : Blo 578813 870677 := bbase (se 6 (by rfl) ⟨20406, by rfl⟩ : syracuseStep 870677 = 40813) (by norm_num)
theorem B870701 : Blo 578813 870701 := bbase (se 3 (by rfl) ⟨163256, by rfl⟩ : syracuseStep 870701 = 326513) (by norm_num)
theorem B870725 : Blo 578813 870725 := bbase (se 4 (by rfl) ⟨81630, by rfl⟩ : syracuseStep 870725 = 163261) (by norm_num)
theorem B870749 : Blo 578813 870749 := bbase (se 3 (by rfl) ⟨163265, by rfl⟩ : syracuseStep 870749 = 326531) (by norm_num)
theorem B870773 : Blo 578813 870773 := bbase (se 5 (by rfl) ⟨40817, by rfl⟩ : syracuseStep 870773 = 81635) (by norm_num)
theorem B870797 : Blo 578813 870797 := bbase (se 3 (by rfl) ⟨163274, by rfl⟩ : syracuseStep 870797 = 326549) (by norm_num)
theorem B1395101 : Blo 578813 1395101 := bbase (se 3 (by rfl) ⟨261581, by rfl⟩ : syracuseStep 1395101 = 523163) (by norm_num)
theorem B870821 : Blo 578813 870821 := bbase (se 4 (by rfl) ⟨81639, by rfl⟩ : syracuseStep 870821 = 163279) (by norm_num)
theorem B1100213 : Blo 578813 1100213 := bbase (se 5 (by rfl) ⟨51572, by rfl⟩ : syracuseStep 1100213 = 103145) (by norm_num)
theorem B870845 : Blo 578813 870845 := bbase (se 3 (by rfl) ⟨163283, by rfl⟩ : syracuseStep 870845 = 326567) (by norm_num)
theorem B870869 : Blo 578813 870869 := bbase (se 7 (by rfl) ⟨10205, by rfl⟩ : syracuseStep 870869 = 20411) (by norm_num)
theorem B707033 : Blo 578813 707033 := bbase (se 2 (by rfl) ⟨265137, by rfl⟩ : syracuseStep 707033 = 530275) (by norm_num)
theorem B838117 : Blo 578813 838117 := bbase (se 4 (by rfl) ⟨78573, by rfl⟩ : syracuseStep 838117 = 157147) (by norm_num)
theorem B870893 : Blo 578813 870893 := bbase (se 3 (by rfl) ⟨163292, by rfl⟩ : syracuseStep 870893 = 326585) (by norm_num)
theorem B870917 : Blo 578813 870917 := bbase (se 4 (by rfl) ⟨81648, by rfl⟩ : syracuseStep 870917 = 163297) (by norm_num)
theorem B870941 : Blo 578813 870941 := bbase (se 3 (by rfl) ⟨163301, by rfl⟩ : syracuseStep 870941 = 326603) (by norm_num)
theorem B870965 : Blo 578813 870965 := bbase (se 5 (by rfl) ⟨40826, by rfl⟩ : syracuseStep 870965 = 81653) (by norm_num)
theorem B870989 : Blo 578813 870989 := bbase (se 3 (by rfl) ⟨163310, by rfl⟩ : syracuseStep 870989 = 326621) (by norm_num)
theorem B871013 : Blo 578813 871013 := bbase (se 4 (by rfl) ⟨81657, by rfl⟩ : syracuseStep 871013 = 163315) (by norm_num)
theorem B871037 : Blo 578813 871037 := bbase (se 3 (by rfl) ⟨163319, by rfl⟩ : syracuseStep 871037 = 326639) (by norm_num)
theorem B871061 : Blo 578813 871061 := bbase (se 6 (by rfl) ⟨20415, by rfl⟩ : syracuseStep 871061 = 40831) (by norm_num)
theorem B871085 : Blo 578813 871085 := bbase (se 3 (by rfl) ⟨163328, by rfl⟩ : syracuseStep 871085 = 326657) (by norm_num)
theorem B3721909 : Blo 578813 3721909 := bbase (se 5 (by rfl) ⟨174464, by rfl⟩ : syracuseStep 3721909 = 348929) (by norm_num)
theorem B871109 : Blo 578813 871109 := bbase (se 4 (by rfl) ⟨81666, by rfl⟩ : syracuseStep 871109 = 163333) (by norm_num)
theorem B871133 : Blo 578813 871133 := bbase (se 3 (by rfl) ⟨163337, by rfl⟩ : syracuseStep 871133 = 326675) (by norm_num)
theorem B871157 : Blo 578813 871157 := bbase (se 5 (by rfl) ⟨40835, by rfl⟩ : syracuseStep 871157 = 81671) (by norm_num)
theorem B871181 : Blo 578813 871181 := bbase (se 3 (by rfl) ⟨163346, by rfl⟩ : syracuseStep 871181 = 326693) (by norm_num)
theorem B871205 : Blo 578813 871205 := bbase (se 4 (by rfl) ⟨81675, by rfl⟩ : syracuseStep 871205 = 163351) (by norm_num)
theorem B871229 : Blo 578813 871229 := bbase (se 3 (by rfl) ⟨163355, by rfl⟩ : syracuseStep 871229 = 326711) (by norm_num)
theorem B7064405 : Blo 578813 7064405 := bbase (se 9 (by rfl) ⟨20696, by rfl⟩ : syracuseStep 7064405 = 41393) (by norm_num)
theorem B871253 : Blo 578813 871253 := bbase (se 9 (by rfl) ⟨2552, by rfl⟩ : syracuseStep 871253 = 5105) (by norm_num)
theorem B871277 : Blo 578813 871277 := bbase (se 3 (by rfl) ⟨163364, by rfl⟩ : syracuseStep 871277 = 326729) (by norm_num)
theorem B871301 : Blo 578813 871301 := bbase (se 4 (by rfl) ⟨81684, by rfl⟩ : syracuseStep 871301 = 163369) (by norm_num)
theorem B871325 : Blo 578813 871325 := bbase (se 3 (by rfl) ⟨163373, by rfl⟩ : syracuseStep 871325 = 326747) (by norm_num)
theorem B871349 : Blo 578813 871349 := bbase (se 5 (by rfl) ⟨40844, by rfl⟩ : syracuseStep 871349 = 81689) (by norm_num)
theorem B871373 : Blo 578813 871373 := bbase (se 3 (by rfl) ⟨163382, by rfl⟩ : syracuseStep 871373 = 326765) (by norm_num)
theorem B1985509 : Blo 578813 1985509 := bbase (se 4 (by rfl) ⟨186141, by rfl⟩ : syracuseStep 1985509 = 372283) (by norm_num)
theorem B871397 : Blo 578813 871397 := bbase (se 4 (by rfl) ⟨81693, by rfl⟩ : syracuseStep 871397 = 163387) (by norm_num)
theorem B871421 : Blo 578813 871421 := bbase (se 3 (by rfl) ⟨163391, by rfl⟩ : syracuseStep 871421 = 326783) (by norm_num)
theorem B871445 : Blo 578813 871445 := bbase (se 6 (by rfl) ⟨20424, by rfl⟩ : syracuseStep 871445 = 40849) (by norm_num)
theorem B871469 : Blo 578813 871469 := bbase (se 3 (by rfl) ⟨163400, by rfl⟩ : syracuseStep 871469 = 326801) (by norm_num)
theorem B871493 : Blo 578813 871493 := bbase (se 4 (by rfl) ⟨81702, by rfl⟩ : syracuseStep 871493 = 163405) (by norm_num)
theorem B871517 : Blo 578813 871517 := bbase (se 3 (by rfl) ⟨163409, by rfl⟩ : syracuseStep 871517 = 326819) (by norm_num)
theorem B2935925 : Blo 578813 2935925 := bbase (se 5 (by rfl) ⟨137621, by rfl⟩ : syracuseStep 2935925 = 275243) (by norm_num)
theorem B871541 : Blo 578813 871541 := bbase (se 5 (by rfl) ⟨40853, by rfl⟩ : syracuseStep 871541 = 81707) (by norm_num)
theorem B871565 : Blo 578813 871565 := bbase (se 3 (by rfl) ⟨163418, by rfl⟩ : syracuseStep 871565 = 326837) (by norm_num)
theorem B1100965 : Blo 578813 1100965 := bbase (se 4 (by rfl) ⟨103215, by rfl⟩ : syracuseStep 1100965 = 206431) (by norm_num)
theorem B871589 : Blo 578813 871589 := bbase (se 4 (by rfl) ⟨81711, by rfl⟩ : syracuseStep 871589 = 163423) (by norm_num)
theorem B871613 : Blo 578813 871613 := bbase (se 3 (by rfl) ⟨163427, by rfl⟩ : syracuseStep 871613 = 326855) (by norm_num)
theorem B871637 : Blo 578813 871637 := bbase (se 7 (by rfl) ⟨10214, by rfl⟩ : syracuseStep 871637 = 20429) (by norm_num)
theorem B871661 : Blo 578813 871661 := bbase (se 3 (by rfl) ⟨163436, by rfl⟩ : syracuseStep 871661 = 326873) (by norm_num)
theorem B871685 : Blo 578813 871685 := bbase (se 4 (by rfl) ⟨81720, by rfl⟩ : syracuseStep 871685 = 163441) (by norm_num)
theorem B1592581 : Blo 578813 1592581 := bbase (se 4 (by rfl) ⟨149304, by rfl⟩ : syracuseStep 1592581 = 298609) (by norm_num)
theorem B871709 : Blo 578813 871709 := bbase (se 3 (by rfl) ⟨163445, by rfl⟩ : syracuseStep 871709 = 326891) (by norm_num)
theorem B1101109 : Blo 578813 1101109 := bbase (se 5 (by rfl) ⟨51614, by rfl⟩ : syracuseStep 1101109 = 103229) (by norm_num)
theorem B871733 : Blo 578813 871733 := bbase (se 5 (by rfl) ⟨40862, by rfl⟩ : syracuseStep 871733 = 81725) (by norm_num)
theorem B871757 : Blo 578813 871757 := bbase (se 3 (by rfl) ⟨163454, by rfl⟩ : syracuseStep 871757 = 326909) (by norm_num)
theorem B871781 : Blo 578813 871781 := bbase (se 4 (by rfl) ⟨81729, by rfl⟩ : syracuseStep 871781 = 163459) (by norm_num)
theorem B1494389 : Blo 578813 1494389 := bbase (se 5 (by rfl) ⟨70049, by rfl⟩ : syracuseStep 1494389 = 140099) (by norm_num)
theorem B871805 : Blo 578813 871805 := bbase (se 3 (by rfl) ⟨163463, by rfl⟩ : syracuseStep 871805 = 326927) (by norm_num)
theorem B2477461 : Blo 578813 2477461 := bbase (se 6 (by rfl) ⟨58065, by rfl⟩ : syracuseStep 2477461 = 116131) (by norm_num)
theorem B871829 : Blo 578813 871829 := bbase (se 6 (by rfl) ⟨20433, by rfl⟩ : syracuseStep 871829 = 40867) (by norm_num)
theorem B871853 : Blo 578813 871853 := bbase (se 3 (by rfl) ⟨163472, by rfl⟩ : syracuseStep 871853 = 326945) (by norm_num)
theorem B871877 : Blo 578813 871877 := bbase (se 4 (by rfl) ⟨81738, by rfl⟩ : syracuseStep 871877 = 163477) (by norm_num)
theorem B1101269 : Blo 578813 1101269 := bbase (se 7 (by rfl) ⟨12905, by rfl⟩ : syracuseStep 1101269 = 25811) (by norm_num)
theorem B871901 : Blo 578813 871901 := bbase (se 3 (by rfl) ⟨163481, by rfl⟩ : syracuseStep 871901 = 326963) (by norm_num)
theorem B871925 : Blo 578813 871925 := bbase (se 5 (by rfl) ⟨40871, by rfl⟩ : syracuseStep 871925 = 81743) (by norm_num)
theorem B871949 : Blo 578813 871949 := bbase (se 3 (by rfl) ⟨163490, by rfl⟩ : syracuseStep 871949 = 326981) (by norm_num)
theorem B871973 : Blo 578813 871973 := bbase (se 4 (by rfl) ⟨81747, by rfl⟩ : syracuseStep 871973 = 163495) (by norm_num)
theorem B871997 : Blo 578813 871997 := bbase (se 3 (by rfl) ⟨163499, by rfl⟩ : syracuseStep 871997 = 326999) (by norm_num)
theorem B872021 : Blo 578813 872021 := bbase (se 8 (by rfl) ⟨5109, by rfl⟩ : syracuseStep 872021 = 10219) (by norm_num)
theorem B1101413 : Blo 578813 1101413 := bbase (se 4 (by rfl) ⟨103257, by rfl⟩ : syracuseStep 1101413 = 206515) (by norm_num)
theorem B872045 : Blo 578813 872045 := bbase (se 3 (by rfl) ⟨163508, by rfl⟩ : syracuseStep 872045 = 327017) (by norm_num)
theorem B872069 : Blo 578813 872069 := bbase (se 4 (by rfl) ⟨81756, by rfl⟩ : syracuseStep 872069 = 163513) (by norm_num)
theorem B872093 : Blo 578813 872093 := bbase (se 3 (by rfl) ⟨163517, by rfl⟩ : syracuseStep 872093 = 327035) (by norm_num)
theorem B872117 : Blo 578813 872117 := bbase (se 5 (by rfl) ⟨40880, by rfl⟩ : syracuseStep 872117 = 81761) (by norm_num)
theorem B872141 : Blo 578813 872141 := bbase (se 3 (by rfl) ⟨163526, by rfl⟩ : syracuseStep 872141 = 327053) (by norm_num)
theorem B872165 : Blo 578813 872165 := bbase (se 4 (by rfl) ⟨81765, by rfl⟩ : syracuseStep 872165 = 163531) (by norm_num)
theorem B872189 : Blo 578813 872189 := bbase (se 3 (by rfl) ⟨163535, by rfl⟩ : syracuseStep 872189 = 327071) (by norm_num)
theorem B1953557 : Blo 578813 1953557 := bbase (se 6 (by rfl) ⟨45786, by rfl⟩ : syracuseStep 1953557 = 91573) (by norm_num)
theorem B872213 : Blo 578813 872213 := bbase (se 6 (by rfl) ⟨20442, by rfl⟩ : syracuseStep 872213 = 40885) (by norm_num)
theorem B872237 : Blo 578813 872237 := bbase (se 3 (by rfl) ⟨163544, by rfl⟩ : syracuseStep 872237 = 327089) (by norm_num)
theorem B872261 : Blo 578813 872261 := bbase (se 4 (by rfl) ⟨81774, by rfl⟩ : syracuseStep 872261 = 163549) (by norm_num)
theorem B872285 : Blo 578813 872285 := bbase (se 3 (by rfl) ⟨163553, by rfl⟩ : syracuseStep 872285 = 327107) (by norm_num)
theorem B2346853 : Blo 578813 2346853 := bbase (se 4 (by rfl) ⟨220017, by rfl⟩ : syracuseStep 2346853 = 440035) (by norm_num)
theorem B872309 : Blo 578813 872309 := bbase (se 5 (by rfl) ⟨40889, by rfl⟩ : syracuseStep 872309 = 81779) (by norm_num)
theorem B708473 : Blo 578813 708473 := bbase (se 2 (by rfl) ⟨265677, by rfl⟩ : syracuseStep 708473 = 531355) (by norm_num)
theorem B1101701 : Blo 578813 1101701 := bbase (se 4 (by rfl) ⟨103284, by rfl⟩ : syracuseStep 1101701 = 206569) (by norm_num)
theorem B872333 : Blo 578813 872333 := bbase (se 3 (by rfl) ⟨163562, by rfl⟩ : syracuseStep 872333 = 327125) (by norm_num)
theorem B872357 : Blo 578813 872357 := bbase (se 4 (by rfl) ⟨81783, by rfl⟩ : syracuseStep 872357 = 163567) (by norm_num)
theorem B872381 : Blo 578813 872381 := bbase (se 3 (by rfl) ⟨163571, by rfl⟩ : syracuseStep 872381 = 327143) (by norm_num)
theorem B839629 : Blo 578813 839629 := bbase (se 3 (by rfl) ⟨157430, by rfl⟩ : syracuseStep 839629 = 314861) (by norm_num)
theorem B872405 : Blo 578813 872405 := bbase (se 7 (by rfl) ⟨10223, by rfl⟩ : syracuseStep 872405 = 20447) (by norm_num)
theorem B872429 : Blo 578813 872429 := bbase (se 3 (by rfl) ⟨163580, by rfl⟩ : syracuseStep 872429 = 327161) (by norm_num)
theorem B655357 : Blo 578813 655357 := bbase (se 3 (by rfl) ⟨122879, by rfl⟩ : syracuseStep 655357 = 245759) (by norm_num)
theorem B970741 : Blo 578813 970741 := bbase (se 5 (by rfl) ⟨45503, by rfl⟩ : syracuseStep 970741 = 91007) (by norm_num)
theorem B872453 : Blo 578813 872453 := bbase (se 4 (by rfl) ⟨81792, by rfl⟩ : syracuseStep 872453 = 163585) (by norm_num)
theorem B1101853 : Blo 578813 1101853 := bbase (se 3 (by rfl) ⟨206597, by rfl⟩ : syracuseStep 1101853 = 413195) (by norm_num)
theorem B872477 : Blo 578813 872477 := bbase (se 3 (by rfl) ⟨163589, by rfl⟩ : syracuseStep 872477 = 327179) (by norm_num)
theorem B872501 : Blo 578813 872501 := bbase (se 5 (by rfl) ⟨40898, by rfl⟩ : syracuseStep 872501 = 81797) (by norm_num)
theorem B872525 : Blo 578813 872525 := bbase (se 3 (by rfl) ⟨163598, by rfl⟩ : syracuseStep 872525 = 327197) (by norm_num)
theorem B872549 : Blo 578813 872549 := bbase (se 4 (by rfl) ⟨81801, by rfl⟩ : syracuseStep 872549 = 163603) (by norm_num)
theorem B872573 : Blo 578813 872573 := bbase (se 3 (by rfl) ⟨163607, by rfl⟩ : syracuseStep 872573 = 327215) (by norm_num)
theorem B872597 : Blo 578813 872597 := bbase (se 6 (by rfl) ⟨20451, by rfl⟩ : syracuseStep 872597 = 40903) (by norm_num)
theorem B872621 : Blo 578813 872621 := bbase (se 3 (by rfl) ⟨163616, by rfl⟩ : syracuseStep 872621 = 327233) (by norm_num)
theorem B1953989 : Blo 578813 1953989 := bbase (se 4 (by rfl) ⟨183186, by rfl⟩ : syracuseStep 1953989 = 366373) (by norm_num)
theorem B872645 : Blo 578813 872645 := bbase (se 4 (by rfl) ⟨81810, by rfl⟩ : syracuseStep 872645 = 163621) (by norm_num)
theorem B872669 : Blo 578813 872669 := bbase (se 3 (by rfl) ⟨163625, by rfl⟩ : syracuseStep 872669 = 327251) (by norm_num)
theorem B872693 : Blo 578813 872693 := bbase (se 5 (by rfl) ⟨40907, by rfl⟩ : syracuseStep 872693 = 81815) (by norm_num)
theorem B872717 : Blo 578813 872717 := bbase (se 3 (by rfl) ⟨163634, by rfl⟩ : syracuseStep 872717 = 327269) (by norm_num)
theorem B872741 : Blo 578813 872741 := bbase (se 4 (by rfl) ⟨81819, by rfl⟩ : syracuseStep 872741 = 163639) (by norm_num)
theorem B872765 : Blo 578813 872765 := bbase (se 3 (by rfl) ⟨163643, by rfl⟩ : syracuseStep 872765 = 327287) (by norm_num)
theorem B1102157 : Blo 578813 1102157 := bbase (se 3 (by rfl) ⟨206654, by rfl⟩ : syracuseStep 1102157 = 413309) (by norm_num)
theorem B872789 : Blo 578813 872789 := bbase (se 10 (by rfl) ⟨1278, by rfl⟩ : syracuseStep 872789 = 2557) (by norm_num)
theorem B1397101 : Blo 578813 1397101 := bbase (se 3 (by rfl) ⟨261956, by rfl⟩ : syracuseStep 1397101 = 523913) (by norm_num)
theorem B872813 : Blo 578813 872813 := bbase (se 3 (by rfl) ⟨163652, by rfl⟩ : syracuseStep 872813 = 327305) (by norm_num)
theorem B2937221 : Blo 578813 2937221 := bbase (se 4 (by rfl) ⟨275364, by rfl⟩ : syracuseStep 2937221 = 550729) (by norm_num)
theorem B872837 : Blo 578813 872837 := bbase (se 4 (by rfl) ⟨81828, by rfl⟩ : syracuseStep 872837 = 163657) (by norm_num)
theorem B872861 : Blo 578813 872861 := bbase (se 3 (by rfl) ⟨163661, by rfl⟩ : syracuseStep 872861 = 327323) (by norm_num)
theorem B872885 : Blo 578813 872885 := bbase (se 5 (by rfl) ⟨40916, by rfl⟩ : syracuseStep 872885 = 81833) (by norm_num)
theorem B872909 : Blo 578813 872909 := bbase (se 3 (by rfl) ⟨163670, by rfl⟩ : syracuseStep 872909 = 327341) (by norm_num)
theorem B872933 : Blo 578813 872933 := bbase (se 4 (by rfl) ⟨81837, by rfl⟩ : syracuseStep 872933 = 163675) (by norm_num)
theorem B872957 : Blo 578813 872957 := bbase (se 3 (by rfl) ⟨163679, by rfl⟩ : syracuseStep 872957 = 327359) (by norm_num)
theorem B872981 : Blo 578813 872981 := bbase (se 6 (by rfl) ⟨20460, by rfl⟩ : syracuseStep 872981 = 40921) (by norm_num)
theorem B873005 : Blo 578813 873005 := bbase (se 3 (by rfl) ⟨163688, by rfl⟩ : syracuseStep 873005 = 327377) (by norm_num)
theorem B873029 : Blo 578813 873029 := bbase (se 4 (by rfl) ⟨81846, by rfl⟩ : syracuseStep 873029 = 163693) (by norm_num)
theorem B873053 : Blo 578813 873053 := bbase (se 3 (by rfl) ⟨163697, by rfl⟩ : syracuseStep 873053 = 327395) (by norm_num)
theorem B1954421 : Blo 578813 1954421 := bbase (se 5 (by rfl) ⟨91613, by rfl⟩ : syracuseStep 1954421 = 183227) (by norm_num)
theorem B873077 : Blo 578813 873077 := bbase (se 5 (by rfl) ⟨40925, by rfl⟩ : syracuseStep 873077 = 81851) (by norm_num)
theorem B873101 : Blo 578813 873101 := bbase (se 3 (by rfl) ⟨163706, by rfl⟩ : syracuseStep 873101 = 327413) (by norm_num)
theorem B873125 : Blo 578813 873125 := bbase (se 4 (by rfl) ⟨81855, by rfl⟩ : syracuseStep 873125 = 163711) (by norm_num)
theorem B873149 : Blo 578813 873149 := bbase (se 3 (by rfl) ⟨163715, by rfl⟩ : syracuseStep 873149 = 327431) (by norm_num)
theorem B873173 : Blo 578813 873173 := bbase (se 7 (by rfl) ⟨10232, by rfl⟩ : syracuseStep 873173 = 20465) (by norm_num)
theorem B873197 : Blo 578813 873197 := bbase (se 3 (by rfl) ⟨163724, by rfl⟩ : syracuseStep 873197 = 327449) (by norm_num)
theorem B873221 : Blo 578813 873221 := bbase (se 4 (by rfl) ⟨81864, by rfl⟩ : syracuseStep 873221 = 163729) (by norm_num)
theorem B873245 : Blo 578813 873245 := bbase (se 3 (by rfl) ⟨163733, by rfl⟩ : syracuseStep 873245 = 327467) (by norm_num)
theorem B873269 : Blo 578813 873269 := bbase (se 5 (by rfl) ⟨40934, by rfl⟩ : syracuseStep 873269 = 81869) (by norm_num)
theorem B873293 : Blo 578813 873293 := bbase (se 3 (by rfl) ⟨163742, by rfl⟩ : syracuseStep 873293 = 327485) (by norm_num)
theorem B873317 : Blo 578813 873317 := bbase (se 4 (by rfl) ⟨81873, by rfl⟩ : syracuseStep 873317 = 163747) (by norm_num)
theorem B873341 : Blo 578813 873341 := bbase (se 3 (by rfl) ⟨163751, by rfl⟩ : syracuseStep 873341 = 327503) (by norm_num)
theorem B873365 : Blo 578813 873365 := bbase (se 6 (by rfl) ⟨20469, by rfl⟩ : syracuseStep 873365 = 40939) (by norm_num)
theorem B873389 : Blo 578813 873389 := bbase (se 3 (by rfl) ⟨163760, by rfl⟩ : syracuseStep 873389 = 327521) (by norm_num)
theorem B873413 : Blo 578813 873413 := bbase (se 4 (by rfl) ⟨81882, by rfl⟩ : syracuseStep 873413 = 163765) (by norm_num)
theorem B873437 : Blo 578813 873437 := bbase (se 3 (by rfl) ⟨163769, by rfl⟩ : syracuseStep 873437 = 327539) (by norm_num)
theorem B1004525 : Blo 578813 1004525 := bbase (se 3 (by rfl) ⟨188348, by rfl⟩ : syracuseStep 1004525 = 376697) (by norm_num)
theorem B873461 : Blo 578813 873461 := bbase (se 5 (by rfl) ⟨40943, by rfl⟩ : syracuseStep 873461 = 81887) (by norm_num)
theorem B873485 : Blo 578813 873485 := bbase (se 3 (by rfl) ⟨163778, by rfl⟩ : syracuseStep 873485 = 327557) (by norm_num)
theorem B1954853 : Blo 578813 1954853 := bbase (se 4 (by rfl) ⟨183267, by rfl⟩ : syracuseStep 1954853 = 366535) (by norm_num)
theorem B873509 : Blo 578813 873509 := bbase (se 4 (by rfl) ⟨81891, by rfl⟩ : syracuseStep 873509 = 163783) (by norm_num)
theorem B1102909 : Blo 578813 1102909 := bbase (se 3 (by rfl) ⟨206795, by rfl⟩ : syracuseStep 1102909 = 413591) (by norm_num)
theorem B873533 : Blo 578813 873533 := bbase (se 3 (by rfl) ⟨163787, by rfl⟩ : syracuseStep 873533 = 327575) (by norm_num)
theorem B873557 : Blo 578813 873557 := bbase (se 8 (by rfl) ⟨5118, by rfl⟩ : syracuseStep 873557 = 10237) (by norm_num)
theorem B873581 : Blo 578813 873581 := bbase (se 3 (by rfl) ⟨163796, by rfl⟩ : syracuseStep 873581 = 327593) (by norm_num)
theorem B840829 : Blo 578813 840829 := bbase (se 3 (by rfl) ⟨157655, by rfl⟩ : syracuseStep 840829 = 315311) (by norm_num)
theorem B873605 : Blo 578813 873605 := bbase (se 4 (by rfl) ⟨81900, by rfl⟩ : syracuseStep 873605 = 163801) (by norm_num)
theorem B873629 : Blo 578813 873629 := bbase (se 3 (by rfl) ⟨163805, by rfl⟩ : syracuseStep 873629 = 327611) (by norm_num)
theorem B873653 : Blo 578813 873653 := bbase (se 5 (by rfl) ⟨40952, by rfl⟩ : syracuseStep 873653 = 81905) (by norm_num)
theorem B1103053 : Blo 578813 1103053 := bbase (se 3 (by rfl) ⟨206822, by rfl⟩ : syracuseStep 1103053 = 413645) (by norm_num)
theorem B873677 : Blo 578813 873677 := bbase (se 3 (by rfl) ⟨163814, by rfl⟩ : syracuseStep 873677 = 327629) (by norm_num)
theorem B4183253 : Blo 578813 4183253 := bbase (se 7 (by rfl) ⟨49022, by rfl⟩ : syracuseStep 4183253 = 98045) (by norm_num)
theorem B873701 : Blo 578813 873701 := bbase (se 4 (by rfl) ⟨81909, by rfl⟩ : syracuseStep 873701 = 163819) (by norm_num)
theorem B873725 : Blo 578813 873725 := bbase (se 3 (by rfl) ⟨163823, by rfl⟩ : syracuseStep 873725 = 327647) (by norm_num)
theorem B873749 : Blo 578813 873749 := bbase (se 6 (by rfl) ⟨20478, by rfl⟩ : syracuseStep 873749 = 40957) (by norm_num)
theorem B873773 : Blo 578813 873773 := bbase (se 3 (by rfl) ⟨163832, by rfl⟩ : syracuseStep 873773 = 327665) (by norm_num)
theorem B3626293 : Blo 578813 3626293 := bbase (se 5 (by rfl) ⟨169982, by rfl⟩ : syracuseStep 3626293 = 339965) (by norm_num)
theorem B873797 : Blo 578813 873797 := bbase (se 4 (by rfl) ⟨81918, by rfl⟩ : syracuseStep 873797 = 163837) (by norm_num)
theorem B873821 : Blo 578813 873821 := bbase (se 3 (by rfl) ⟨163841, by rfl⟩ : syracuseStep 873821 = 327683) (by norm_num)
theorem B1103213 : Blo 578813 1103213 := bbase (se 3 (by rfl) ⟨206852, by rfl⟩ : syracuseStep 1103213 = 413705) (by norm_num)
theorem B873845 : Blo 578813 873845 := bbase (se 5 (by rfl) ⟨40961, by rfl⟩ : syracuseStep 873845 = 81923) (by norm_num)
theorem B873869 : Blo 578813 873869 := bbase (se 3 (by rfl) ⟨163850, by rfl⟩ : syracuseStep 873869 = 327701) (by norm_num)
theorem B873893 : Blo 578813 873893 := bbase (se 4 (by rfl) ⟨81927, by rfl⟩ : syracuseStep 873893 = 163855) (by norm_num)
theorem B873917 : Blo 578813 873917 := bbase (se 3 (by rfl) ⟨163859, by rfl⟩ : syracuseStep 873917 = 327719) (by norm_num)
theorem B1955285 : Blo 578813 1955285 := bbase (se 7 (by rfl) ⟨22913, by rfl⟩ : syracuseStep 1955285 = 45827) (by norm_num)
theorem B873941 : Blo 578813 873941 := bbase (se 7 (by rfl) ⟨10241, by rfl⟩ : syracuseStep 873941 = 20483) (by norm_num)
theorem B873965 : Blo 578813 873965 := bbase (se 3 (by rfl) ⟨163868, by rfl⟩ : syracuseStep 873965 = 327737) (by norm_num)
theorem B1103357 : Blo 578813 1103357 := bbase (se 3 (by rfl) ⟨206879, by rfl⟩ : syracuseStep 1103357 = 413759) (by norm_num)
theorem B873989 : Blo 578813 873989 := bbase (se 4 (by rfl) ⟨81936, by rfl⟩ : syracuseStep 873989 = 163873) (by norm_num)
theorem B874013 : Blo 578813 874013 := bbase (se 3 (by rfl) ⟨163877, by rfl⟩ : syracuseStep 874013 = 327755) (by norm_num)
theorem B874037 : Blo 578813 874037 := bbase (se 5 (by rfl) ⟨40970, by rfl⟩ : syracuseStep 874037 = 81941) (by norm_num)
theorem B874061 : Blo 578813 874061 := bbase (se 3 (by rfl) ⟨163886, by rfl⟩ : syracuseStep 874061 = 327773) (by norm_num)
theorem B874085 : Blo 578813 874085 := bbase (se 4 (by rfl) ⟨81945, by rfl⟩ : syracuseStep 874085 = 163891) (by norm_num)
theorem B874109 : Blo 578813 874109 := bbase (se 3 (by rfl) ⟨163895, by rfl⟩ : syracuseStep 874109 = 327791) (by norm_num)
theorem B1857173 : Blo 578813 1857173 := bbase (se 6 (by rfl) ⟨43527, by rfl⟩ : syracuseStep 1857173 = 87055) (by norm_num)
theorem B2938517 : Blo 578813 2938517 := bbase (se 6 (by rfl) ⟨68871, by rfl⟩ : syracuseStep 2938517 = 137743) (by norm_num)
theorem B874133 : Blo 578813 874133 := bbase (se 6 (by rfl) ⟨20487, by rfl⟩ : syracuseStep 874133 = 40975) (by norm_num)
theorem B874157 : Blo 578813 874157 := bbase (se 3 (by rfl) ⟨163904, by rfl⟩ : syracuseStep 874157 = 327809) (by norm_num)
theorem B874181 : Blo 578813 874181 := bbase (se 4 (by rfl) ⟨81954, by rfl⟩ : syracuseStep 874181 = 163909) (by norm_num)
theorem B1398485 : Blo 578813 1398485 := bbase (se 7 (by rfl) ⟨16388, by rfl⟩ : syracuseStep 1398485 = 32777) (by norm_num)
theorem B1398493 : Blo 578813 1398493 := bbase (se 3 (by rfl) ⟨262217, by rfl⟩ : syracuseStep 1398493 = 524435) (by norm_num)
theorem B874205 : Blo 578813 874205 := bbase (se 3 (by rfl) ⟨163913, by rfl⟩ : syracuseStep 874205 = 327827) (by norm_num)
theorem B1103645 : Blo 578813 1103645 := bbase (se 3 (by rfl) ⟨206933, by rfl⟩ : syracuseStep 1103645 = 413867) (by norm_num)
theorem B1955717 : Blo 578813 1955717 := bbase (se 4 (by rfl) ⟨183348, by rfl⟩ : syracuseStep 1955717 = 366697) (by norm_num)
theorem B4413365 : Blo 578813 4413365 := bbase (se 5 (by rfl) ⟨206876, by rfl⟩ : syracuseStep 4413365 = 413753) (by norm_num)
theorem B1103797 : Blo 578813 1103797 := bbase (se 5 (by rfl) ⟨51740, by rfl⟩ : syracuseStep 1103797 = 103481) (by norm_num)
theorem B2578405 : Blo 578813 2578405 := bbase (se 4 (by rfl) ⟨241725, by rfl⟩ : syracuseStep 2578405 = 483451) (by norm_num)
theorem B1104101 : Blo 578813 1104101 := bbase (se 4 (by rfl) ⟨103509, by rfl⟩ : syracuseStep 1104101 = 207019) (by norm_num)
theorem B1956149 : Blo 578813 1956149 := bbase (se 5 (by rfl) ⟨91694, by rfl⟩ : syracuseStep 1956149 = 183389) (by norm_num)
theorem B2480453 : Blo 578813 2480453 := bbase (se 4 (by rfl) ⟨232542, by rfl⟩ : syracuseStep 2480453 = 465085) (by norm_num)
theorem B1858085 : Blo 578813 1858085 := bbase (se 4 (by rfl) ⟨174195, by rfl⟩ : syracuseStep 1858085 = 348391) (by norm_num)
theorem B1399493 : Blo 578813 1399493 := bbase (se 4 (by rfl) ⟨131202, by rfl⟩ : syracuseStep 1399493 = 262405) (by norm_num)
theorem B1956581 : Blo 578813 1956581 := bbase (se 4 (by rfl) ⟨183429, by rfl⟩ : syracuseStep 1956581 = 366859) (by norm_num)
theorem B908101 : Blo 578813 908101 := bbase (se 4 (by rfl) ⟨85134, by rfl⟩ : syracuseStep 908101 = 170269) (by norm_num)
theorem B2087765 : Blo 578813 2087765 := bbase (se 9 (by rfl) ⟨6116, by rfl⟩ : syracuseStep 2087765 = 12233) (by norm_num)
theorem B1465229 : Blo 578813 1465229 := bbase (se 3 (by rfl) ⟨274730, by rfl⟩ : syracuseStep 1465229 = 549461) (by norm_num)
theorem B2939813 : Blo 578813 2939813 := bbase (se 4 (by rfl) ⟨275607, by rfl⟩ : syracuseStep 2939813 = 551215) (by norm_num)
theorem B1104853 : Blo 578813 1104853 := bbase (se 7 (by rfl) ⟨12947, by rfl⟩ : syracuseStep 1104853 = 25895) (by norm_num)
theorem B1104997 : Blo 578813 1104997 := bbase (se 4 (by rfl) ⟨103593, by rfl⟩ : syracuseStep 1104997 = 207187) (by norm_num)
theorem B1957013 : Blo 578813 1957013 := bbase (se 6 (by rfl) ⟨45867, by rfl⟩ : syracuseStep 1957013 = 91735) (by norm_num)
theorem B2645173 : Blo 578813 2645173 := bbase (se 5 (by rfl) ⟨123992, by rfl⟩ : syracuseStep 2645173 = 247985) (by norm_num)
theorem B1465573 : Blo 578813 1465573 := bbase (se 4 (by rfl) ⟨137397, by rfl⟩ : syracuseStep 1465573 = 274795) (by norm_num)
theorem B1105157 : Blo 578813 1105157 := bbase (se 4 (by rfl) ⟨103608, by rfl⟩ : syracuseStep 1105157 = 207217) (by norm_num)
theorem B2481461 : Blo 578813 2481461 := bbase (se 5 (by rfl) ⟨116318, by rfl⟩ : syracuseStep 2481461 = 232637) (by norm_num)
theorem B1465685 : Blo 578813 1465685 := bbase (se 11 (by rfl) ⟨1073, by rfl⟩ : syracuseStep 1465685 = 2147) (by norm_num)
theorem B5037461 : Blo 578813 5037461 := bbase (se 6 (by rfl) ⟨118065, by rfl⟩ : syracuseStep 5037461 = 236131) (by norm_num)
theorem B1105301 : Blo 578813 1105301 := bbase (se 6 (by rfl) ⟨25905, by rfl⟩ : syracuseStep 1105301 = 51811) (by norm_num)
theorem B1400261 : Blo 578813 1400261 := bbase (se 4 (by rfl) ⟨131274, by rfl⟩ : syracuseStep 1400261 = 262549) (by norm_num)
theorem B3300821 : Blo 578813 3300821 := bbase (se 7 (by rfl) ⟨38681, by rfl⟩ : syracuseStep 3300821 = 77363) (by norm_num)
theorem B1465877 : Blo 578813 1465877 := bbase (se 6 (by rfl) ⟨34356, by rfl⟩ : syracuseStep 1465877 = 68713) (by norm_num)
theorem B1957445 : Blo 578813 1957445 := bbase (se 4 (by rfl) ⟨183510, by rfl⟩ : syracuseStep 1957445 = 367021) (by norm_num)
theorem B5594741 : Blo 578813 5594741 := bbase (se 5 (by rfl) ⟨262253, by rfl⟩ : syracuseStep 5594741 = 524507) (by norm_num)
theorem B2088629 : Blo 578813 2088629 := bbase (se 5 (by rfl) ⟨97904, by rfl⟩ : syracuseStep 2088629 = 195809) (by norm_num)
theorem B1105589 : Blo 578813 1105589 := bbase (se 5 (by rfl) ⟨51824, by rfl⟩ : syracuseStep 1105589 = 103649) (by norm_num)
theorem B745249 : Blo 578813 745249 := bbase (se 2 (by rfl) ⟨279468, by rfl⟩ : syracuseStep 745249 = 558937) (by norm_num)
theorem B1892165 : Blo 578813 1892165 := bbase (se 4 (by rfl) ⟨177390, by rfl⟩ : syracuseStep 1892165 = 354781) (by norm_num)
theorem B1105741 : Blo 578813 1105741 := bbase (se 3 (by rfl) ⟨207326, by rfl⟩ : syracuseStep 1105741 = 414653) (by norm_num)
theorem B1859429 : Blo 578813 1859429 := bbase (se 4 (by rfl) ⟨174321, by rfl⟩ : syracuseStep 1859429 = 348643) (by norm_num)
theorem B1466221 : Blo 578813 1466221 := bbase (se 3 (by rfl) ⟨274916, by rfl⟩ : syracuseStep 1466221 = 549833) (by norm_num)
theorem B1302389 : Blo 578813 1302389 := bbase (se 5 (by rfl) ⟨61049, by rfl⟩ : syracuseStep 1302389 = 122099) (by norm_num)
theorem B1302461 : Blo 578813 1302461 := bbase (se 3 (by rfl) ⟨244211, by rfl⟩ : syracuseStep 1302461 = 488423) (by norm_num)
theorem B1466333 : Blo 578813 1466333 := bbase (se 3 (by rfl) ⟨274937, by rfl⟩ : syracuseStep 1466333 = 549875) (by norm_num)
theorem B1564645 : Blo 578813 1564645 := bbase (se 4 (by rfl) ⟨146685, by rfl⟩ : syracuseStep 1564645 = 293371) (by norm_num)
theorem B1957877 : Blo 578813 1957877 := bbase (se 5 (by rfl) ⟨91775, by rfl⟩ : syracuseStep 1957877 = 183551) (by norm_num)
theorem B1302533 : Blo 578813 1302533 := bbase (se 4 (by rfl) ⟨122112, by rfl⟩ : syracuseStep 1302533 = 244225) (by norm_num)
theorem B1302605 : Blo 578813 1302605 := bbase (se 3 (by rfl) ⟨244238, by rfl⟩ : syracuseStep 1302605 = 488477) (by norm_num)
theorem B1106045 : Blo 578813 1106045 := bbase (se 3 (by rfl) ⟨207383, by rfl⟩ : syracuseStep 1106045 = 414767) (by norm_num)
theorem B2384005 : Blo 578813 2384005 := bbase (se 4 (by rfl) ⟨223500, by rfl⟩ : syracuseStep 2384005 = 447001) (by norm_num)
theorem B1302677 : Blo 578813 1302677 := bbase (se 6 (by rfl) ⟨30531, by rfl⟩ : syracuseStep 1302677 = 61063) (by norm_num)
theorem B1466525 : Blo 578813 1466525 := bbase (se 3 (by rfl) ⟨274973, by rfl⟩ : syracuseStep 1466525 = 549947) (by norm_num)
theorem B2941109 : Blo 578813 2941109 := bbase (se 5 (by rfl) ⟨137864, by rfl⟩ : syracuseStep 2941109 = 275729) (by norm_num)
theorem B1302749 : Blo 578813 1302749 := bbase (se 3 (by rfl) ⟨244265, by rfl⟩ : syracuseStep 1302749 = 488531) (by norm_num)
theorem B1302821 : Blo 578813 1302821 := bbase (se 4 (by rfl) ⟨122139, by rfl⟩ : syracuseStep 1302821 = 244279) (by norm_num)
theorem B2351429 : Blo 578813 2351429 := bbase (se 4 (by rfl) ⟨220446, by rfl⟩ : syracuseStep 2351429 = 440893) (by norm_num)
theorem B1302893 : Blo 578813 1302893 := bbase (se 3 (by rfl) ⟨244292, by rfl⟩ : syracuseStep 1302893 = 488585) (by norm_num)
theorem B1958309 : Blo 578813 1958309 := bbase (se 4 (by rfl) ⟨183591, by rfl⟩ : syracuseStep 1958309 = 367183) (by norm_num)
theorem B1302965 : Blo 578813 1302965 := bbase (se 5 (by rfl) ⟨61076, by rfl⟩ : syracuseStep 1302965 = 122153) (by norm_num)
theorem B1237493 : Blo 578813 1237493 := bbase (se 5 (by rfl) ⟨58007, by rfl⟩ : syracuseStep 1237493 = 116015) (by norm_num)
theorem B1466869 : Blo 578813 1466869 := bbase (se 5 (by rfl) ⟨68759, by rfl⟩ : syracuseStep 1466869 = 137519) (by norm_num)
theorem B1303037 : Blo 578813 1303037 := bbase (se 3 (by rfl) ⟨244319, by rfl⟩ : syracuseStep 1303037 = 488639) (by norm_num)
theorem B1303109 : Blo 578813 1303109 := bbase (se 4 (by rfl) ⟨122166, by rfl⟩ : syracuseStep 1303109 = 244333) (by norm_num)
theorem B1466981 : Blo 578813 1466981 := bbase (se 4 (by rfl) ⟨137529, by rfl⟩ : syracuseStep 1466981 = 275059) (by norm_num)
theorem B3302005 : Blo 578813 3302005 := bbase (se 5 (by rfl) ⟨154781, by rfl⟩ : syracuseStep 3302005 = 309563) (by norm_num)
theorem B1237637 : Blo 578813 1237637 := bbase (se 4 (by rfl) ⟨116028, by rfl⟩ : syracuseStep 1237637 = 232057) (by norm_num)
theorem B1303181 : Blo 578813 1303181 := bbase (se 3 (by rfl) ⟨244346, by rfl⟩ : syracuseStep 1303181 = 488693) (by norm_num)
theorem B1303253 : Blo 578813 1303253 := bbase (se 7 (by rfl) ⟨15272, by rfl⟩ : syracuseStep 1303253 = 30545) (by norm_num)
theorem B746209 : Blo 578813 746209 := bbase (se 2 (by rfl) ⟨279828, by rfl⟩ : syracuseStep 746209 = 559657) (by norm_num)
theorem B1303325 : Blo 578813 1303325 := bbase (se 3 (by rfl) ⟨244373, by rfl⟩ : syracuseStep 1303325 = 488747) (by norm_num)
theorem B1467173 : Blo 578813 1467173 := bbase (se 4 (by rfl) ⟨137547, by rfl⟩ : syracuseStep 1467173 = 275095) (by norm_num)
theorem B1958741 : Blo 578813 1958741 := bbase (se 9 (by rfl) ⟨5738, by rfl⟩ : syracuseStep 1958741 = 11477) (by norm_num)
theorem B1303397 : Blo 578813 1303397 := bbase (se 4 (by rfl) ⟨122193, by rfl⟩ : syracuseStep 1303397 = 244387) (by norm_num)
theorem B746377 : Blo 578813 746377 := bbase (se 2 (by rfl) ⟨279891, by rfl⟩ : syracuseStep 746377 = 559783) (by norm_num)
theorem B1303469 : Blo 578813 1303469 := bbase (se 3 (by rfl) ⟨244400, by rfl⟩ : syracuseStep 1303469 = 488801) (by norm_num)
theorem B1237997 : Blo 578813 1237997 := bbase (se 3 (by rfl) ⟨232124, by rfl⟩ : syracuseStep 1237997 = 464249) (by norm_num)
theorem B1303541 : Blo 578813 1303541 := bbase (se 5 (by rfl) ⟨61103, by rfl⟩ : syracuseStep 1303541 = 122207) (by norm_num)
theorem B2483237 : Blo 578813 2483237 := bbase (se 4 (by rfl) ⟨232803, by rfl⟩ : syracuseStep 2483237 = 465607) (by norm_num)
theorem B1303613 : Blo 578813 1303613 := bbase (se 3 (by rfl) ⟨244427, by rfl⟩ : syracuseStep 1303613 = 488855) (by norm_num)
theorem B1467517 : Blo 578813 1467517 := bbase (se 3 (by rfl) ⟨275159, by rfl⟩ : syracuseStep 1467517 = 550319) (by norm_num)
theorem B1303685 : Blo 578813 1303685 := bbase (se 4 (by rfl) ⟨122220, by rfl⟩ : syracuseStep 1303685 = 244441) (by norm_num)
theorem B1303757 : Blo 578813 1303757 := bbase (se 3 (by rfl) ⟨244454, by rfl⟩ : syracuseStep 1303757 = 488909) (by norm_num)
theorem B1467629 : Blo 578813 1467629 := bbase (se 3 (by rfl) ⟨275180, by rfl⟩ : syracuseStep 1467629 = 550361) (by norm_num)
theorem B1860853 : Blo 578813 1860853 := bbase (se 5 (by rfl) ⟨87227, by rfl⟩ : syracuseStep 1860853 = 174455) (by norm_num)
theorem B1959173 : Blo 578813 1959173 := bbase (se 4 (by rfl) ⟨183672, by rfl⟩ : syracuseStep 1959173 = 367345) (by norm_num)
theorem B1303829 : Blo 578813 1303829 := bbase (se 6 (by rfl) ⟨30558, by rfl⟩ : syracuseStep 1303829 = 61117) (by norm_num)
theorem B1303901 : Blo 578813 1303901 := bbase (se 3 (by rfl) ⟨244481, by rfl⟩ : syracuseStep 1303901 = 488963) (by norm_num)
theorem B1303973 : Blo 578813 1303973 := bbase (se 4 (by rfl) ⟨122247, by rfl⟩ : syracuseStep 1303973 = 244495) (by norm_num)
theorem B1467821 : Blo 578813 1467821 := bbase (se 3 (by rfl) ⟨275216, by rfl⟩ : syracuseStep 1467821 = 550433) (by norm_num)
theorem B2942405 : Blo 578813 2942405 := bbase (se 4 (by rfl) ⟨275850, by rfl⟩ : syracuseStep 2942405 = 551701) (by norm_num)
theorem B1304045 : Blo 578813 1304045 := bbase (se 3 (by rfl) ⟨244508, by rfl⟩ : syracuseStep 1304045 = 489017) (by norm_num)
theorem B681485 : Blo 578813 681485 := bbase (se 3 (by rfl) ⟨127778, by rfl⟩ : syracuseStep 681485 = 255557) (by norm_num)
theorem B1304117 : Blo 578813 1304117 := bbase (se 5 (by rfl) ⟨61130, by rfl⟩ : syracuseStep 1304117 = 122261) (by norm_num)
theorem B1304189 : Blo 578813 1304189 := bbase (se 3 (by rfl) ⟨244535, by rfl⟩ : syracuseStep 1304189 = 489071) (by norm_num)
theorem B1959605 : Blo 578813 1959605 := bbase (se 5 (by rfl) ⟨91856, by rfl⟩ : syracuseStep 1959605 = 183713) (by norm_num)
theorem B1304261 : Blo 578813 1304261 := bbase (se 4 (by rfl) ⟨122274, by rfl⟩ : syracuseStep 1304261 = 244549) (by norm_num)
theorem B3761909 : Blo 578813 3761909 := bbase (se 5 (by rfl) ⟨176339, by rfl⟩ : syracuseStep 3761909 = 352679) (by norm_num)
theorem B1468165 : Blo 578813 1468165 := bbase (se 4 (by rfl) ⟨137640, by rfl⟩ : syracuseStep 1468165 = 275281) (by norm_num)
theorem B1304333 : Blo 578813 1304333 := bbase (se 3 (by rfl) ⟨244562, by rfl⟩ : syracuseStep 1304333 = 489125) (by norm_num)
theorem B1304405 : Blo 578813 1304405 := bbase (se 9 (by rfl) ⟨3821, by rfl⟩ : syracuseStep 1304405 = 7643) (by norm_num)
theorem B1238885 : Blo 578813 1238885 := bbase (se 4 (by rfl) ⟨116145, by rfl⟩ : syracuseStep 1238885 = 232291) (by norm_num)
theorem B1468277 : Blo 578813 1468277 := bbase (se 5 (by rfl) ⟨68825, by rfl⟩ : syracuseStep 1468277 = 137651) (by norm_num)
theorem B976765 : Blo 578813 976765 := bbase (se 3 (by rfl) ⟨183143, by rfl⟩ : syracuseStep 976765 = 366287) (by norm_num)
theorem B714629 : Blo 578813 714629 := bbase (se 4 (by rfl) ⟨66996, by rfl⟩ : syracuseStep 714629 = 133993) (by norm_num)
theorem B1304477 : Blo 578813 1304477 := bbase (se 3 (by rfl) ⟨244589, by rfl⟩ : syracuseStep 1304477 = 489179) (by norm_num)
theorem B976853 : Blo 578813 976853 := bbase (se 7 (by rfl) ⟨11447, by rfl⟩ : syracuseStep 976853 = 22895) (by norm_num)
theorem B1304549 : Blo 578813 1304549 := bbase (se 4 (by rfl) ⟨122301, by rfl⟩ : syracuseStep 1304549 = 244603) (by norm_num)
theorem B4777973 : Blo 578813 4777973 := bbase (se 5 (by rfl) ⟨223967, by rfl⟩ : syracuseStep 4777973 = 447935) (by norm_num)
theorem B1304621 : Blo 578813 1304621 := bbase (se 3 (by rfl) ⟨244616, by rfl⟩ : syracuseStep 1304621 = 489233) (by norm_num)
theorem B1468469 : Blo 578813 1468469 := bbase (se 5 (by rfl) ⟨68834, by rfl⟩ : syracuseStep 1468469 = 137669) (by norm_num)
theorem B976981 : Blo 578813 976981 := bbase (se 8 (by rfl) ⟨5724, by rfl⟩ : syracuseStep 976981 = 11449) (by norm_num)
theorem B1239133 : Blo 578813 1239133 := bbase (se 3 (by rfl) ⟨232337, by rfl⟩ : syracuseStep 1239133 = 464675) (by norm_num)
theorem B2091109 : Blo 578813 2091109 := bbase (se 4 (by rfl) ⟨196041, by rfl⟩ : syracuseStep 2091109 = 392083) (by norm_num)
theorem B1960037 : Blo 578813 1960037 := bbase (se 4 (by rfl) ⟨183753, by rfl⟩ : syracuseStep 1960037 = 367507) (by norm_num)
theorem B1304693 : Blo 578813 1304693 := bbase (se 5 (by rfl) ⟨61157, by rfl⟩ : syracuseStep 1304693 = 122315) (by norm_num)
theorem B977069 : Blo 578813 977069 := bbase (se 3 (by rfl) ⟨183200, by rfl⟩ : syracuseStep 977069 = 366401) (by norm_num)
theorem B1304765 : Blo 578813 1304765 := bbase (se 3 (by rfl) ⟨244643, by rfl⟩ : syracuseStep 1304765 = 489287) (by norm_num)
theorem B1304837 : Blo 578813 1304837 := bbase (se 4 (by rfl) ⟨122328, by rfl⟩ : syracuseStep 1304837 = 244657) (by norm_num)
theorem B977197 : Blo 578813 977197 := bbase (se 3 (by rfl) ⟨183224, by rfl⟩ : syracuseStep 977197 = 366449) (by norm_num)
theorem B1304909 : Blo 578813 1304909 := bbase (se 3 (by rfl) ⟨244670, by rfl⟩ : syracuseStep 1304909 = 489341) (by norm_num)
theorem B977285 : Blo 578813 977285 := bbase (se 4 (by rfl) ⟨91620, by rfl⟩ : syracuseStep 977285 = 183241) (by norm_num)
theorem B1468813 : Blo 578813 1468813 := bbase (se 3 (by rfl) ⟨275402, by rfl⟩ : syracuseStep 1468813 = 550805) (by norm_num)
theorem B1304981 : Blo 578813 1304981 := bbase (se 6 (by rfl) ⟨30585, by rfl⟩ : syracuseStep 1304981 = 61171) (by norm_num)
theorem B1305053 : Blo 578813 1305053 := bbase (se 3 (by rfl) ⟨244697, by rfl⟩ : syracuseStep 1305053 = 489395) (by norm_num)
theorem B1468925 : Blo 578813 1468925 := bbase (se 3 (by rfl) ⟨275423, by rfl⟩ : syracuseStep 1468925 = 550847) (by norm_num)
theorem B977413 : Blo 578813 977413 := bbase (se 4 (by rfl) ⟨91632, by rfl⟩ : syracuseStep 977413 = 183265) (by norm_num)
theorem B1960469 : Blo 578813 1960469 := bbase (se 6 (by rfl) ⟨45948, by rfl⟩ : syracuseStep 1960469 = 91897) (by norm_num)
theorem B1305125 : Blo 578813 1305125 := bbase (se 4 (by rfl) ⟨122355, by rfl⟩ : syracuseStep 1305125 = 244711) (by norm_num)
theorem B3303989 : Blo 578813 3303989 := bbase (se 5 (by rfl) ⟨154874, by rfl⟩ : syracuseStep 3303989 = 309749) (by norm_num)
theorem B1239637 : Blo 578813 1239637 := bbase (se 8 (by rfl) ⟨7263, by rfl⟩ : syracuseStep 1239637 = 14527) (by norm_num)
theorem B977501 : Blo 578813 977501 := bbase (se 3 (by rfl) ⟨183281, by rfl⟩ : syracuseStep 977501 = 366563) (by norm_num)
theorem B1305197 : Blo 578813 1305197 := bbase (se 3 (by rfl) ⟨244724, by rfl⟩ : syracuseStep 1305197 = 489449) (by norm_num)
theorem B1305269 : Blo 578813 1305269 := bbase (se 5 (by rfl) ⟨61184, by rfl⟩ : syracuseStep 1305269 = 122369) (by norm_num)
theorem B1174205 : Blo 578813 1174205 := bbase (se 3 (by rfl) ⟨220163, by rfl⟩ : syracuseStep 1174205 = 440327) (by norm_num)
theorem B1469117 : Blo 578813 1469117 := bbase (se 3 (by rfl) ⟨275459, by rfl⟩ : syracuseStep 1469117 = 550919) (by norm_num)
theorem B2943701 : Blo 578813 2943701 := bbase (se 7 (by rfl) ⟨34496, by rfl⟩ : syracuseStep 2943701 = 68993) (by norm_num)
theorem B977629 : Blo 578813 977629 := bbase (se 3 (by rfl) ⟨183305, by rfl⟩ : syracuseStep 977629 = 366611) (by norm_num)
theorem B1305341 : Blo 578813 1305341 := bbase (se 3 (by rfl) ⟨244751, by rfl⟩ : syracuseStep 1305341 = 489503) (by norm_num)
theorem B977717 : Blo 578813 977717 := bbase (se 5 (by rfl) ⟨45830, by rfl⟩ : syracuseStep 977717 = 91661) (by norm_num)
theorem B1862453 : Blo 578813 1862453 := bbase (se 5 (by rfl) ⟨87302, by rfl⟩ : syracuseStep 1862453 = 174605) (by norm_num)
theorem B1305413 : Blo 578813 1305413 := bbase (se 4 (by rfl) ⟨122382, by rfl⟩ : syracuseStep 1305413 = 244765) (by norm_num)
theorem B1305485 : Blo 578813 1305485 := bbase (se 3 (by rfl) ⟨244778, by rfl⟩ : syracuseStep 1305485 = 489557) (by norm_num)
theorem B977845 : Blo 578813 977845 := bbase (se 5 (by rfl) ⟨45836, by rfl⟩ : syracuseStep 977845 = 91673) (by norm_num)
theorem B1960901 : Blo 578813 1960901 := bbase (se 4 (by rfl) ⟨183834, by rfl⟩ : syracuseStep 1960901 = 367669) (by norm_num)
theorem B1305557 : Blo 578813 1305557 := bbase (se 7 (by rfl) ⟨15299, by rfl⟩ : syracuseStep 1305557 = 30599) (by norm_num)
theorem B977933 : Blo 578813 977933 := bbase (se 3 (by rfl) ⟨183362, by rfl⟩ : syracuseStep 977933 = 366725) (by norm_num)
theorem B1469461 : Blo 578813 1469461 := bbase (se 6 (by rfl) ⟨34440, by rfl⟩ : syracuseStep 1469461 = 68881) (by norm_num)
theorem B1305629 : Blo 578813 1305629 := bbase (se 3 (by rfl) ⟨244805, by rfl⟩ : syracuseStep 1305629 = 489611) (by norm_num)
theorem B1305701 : Blo 578813 1305701 := bbase (se 4 (by rfl) ⟨122409, by rfl⟩ : syracuseStep 1305701 = 244819) (by norm_num)
theorem B1469573 : Blo 578813 1469573 := bbase (se 4 (by rfl) ⟨137772, by rfl⟩ : syracuseStep 1469573 = 275545) (by norm_num)
theorem B978061 : Blo 578813 978061 := bbase (se 3 (by rfl) ⟨183386, by rfl⟩ : syracuseStep 978061 = 366773) (by norm_num)
theorem B1305773 : Blo 578813 1305773 := bbase (se 3 (by rfl) ⟨244832, by rfl⟩ : syracuseStep 1305773 = 489665) (by norm_num)
theorem B978149 : Blo 578813 978149 := bbase (se 4 (by rfl) ⟨91701, by rfl⟩ : syracuseStep 978149 = 183403) (by norm_num)
theorem B1305845 : Blo 578813 1305845 := bbase (se 5 (by rfl) ⟨61211, by rfl⟩ : syracuseStep 1305845 = 122423) (by norm_num)
theorem B3534101 : Blo 578813 3534101 := bbase (se 6 (by rfl) ⟨82830, by rfl⟩ : syracuseStep 3534101 = 165661) (by norm_num)
theorem B1305917 : Blo 578813 1305917 := bbase (se 3 (by rfl) ⟨244859, by rfl⟩ : syracuseStep 1305917 = 489719) (by norm_num)
theorem B1469765 : Blo 578813 1469765 := bbase (se 4 (by rfl) ⟨137790, by rfl⟩ : syracuseStep 1469765 = 275581) (by norm_num)
theorem B978277 : Blo 578813 978277 := bbase (se 4 (by rfl) ⟨91713, by rfl⟩ : syracuseStep 978277 = 183427) (by norm_num)
theorem B1961333 : Blo 578813 1961333 := bbase (se 5 (by rfl) ⟨91937, by rfl⟩ : syracuseStep 1961333 = 183875) (by norm_num)
theorem B1305989 : Blo 578813 1305989 := bbase (se 4 (by rfl) ⟨122436, by rfl⟩ : syracuseStep 1305989 = 244873) (by norm_num)
theorem B978365 : Blo 578813 978365 := bbase (se 3 (by rfl) ⟨183443, by rfl⟩ : syracuseStep 978365 = 366887) (by norm_num)
theorem B1306061 : Blo 578813 1306061 := bbase (se 3 (by rfl) ⟨244886, by rfl⟩ : syracuseStep 1306061 = 489773) (by norm_num)
theorem B1240525 : Blo 578813 1240525 := bbase (se 3 (by rfl) ⟨232598, by rfl⟩ : syracuseStep 1240525 = 465197) (by norm_num)
theorem B1306133 : Blo 578813 1306133 := bbase (se 6 (by rfl) ⟨30612, by rfl⟩ : syracuseStep 1306133 = 61225) (by norm_num)
theorem B978493 : Blo 578813 978493 := bbase (se 3 (by rfl) ⟨183467, by rfl⟩ : syracuseStep 978493 = 366935) (by norm_num)
theorem B1306205 : Blo 578813 1306205 := bbase (se 3 (by rfl) ⟨244913, by rfl⟩ : syracuseStep 1306205 = 489827) (by norm_num)
theorem B880229 : Blo 578813 880229 := bbase (se 4 (by rfl) ⟨82521, by rfl⟩ : syracuseStep 880229 = 165043) (by norm_num)
theorem B978581 : Blo 578813 978581 := bbase (se 6 (by rfl) ⟨22935, by rfl⟩ : syracuseStep 978581 = 45871) (by norm_num)
theorem B1470109 : Blo 578813 1470109 := bbase (se 3 (by rfl) ⟨275645, by rfl⟩ : syracuseStep 1470109 = 551291) (by norm_num)
theorem B1535645 : Blo 578813 1535645 := bbase (se 3 (by rfl) ⟨287933, by rfl⟩ : syracuseStep 1535645 = 575867) (by norm_num)
theorem B1306277 : Blo 578813 1306277 := bbase (se 4 (by rfl) ⟨122463, by rfl⟩ : syracuseStep 1306277 = 244927) (by norm_num)
theorem B1306349 : Blo 578813 1306349 := bbase (se 3 (by rfl) ⟨244940, by rfl⟩ : syracuseStep 1306349 = 489881) (by norm_num)
theorem B1470221 : Blo 578813 1470221 := bbase (se 3 (by rfl) ⟨275666, by rfl⟩ : syracuseStep 1470221 = 551333) (by norm_num)
theorem B978709 : Blo 578813 978709 := bbase (se 6 (by rfl) ⟨22938, by rfl⟩ : syracuseStep 978709 = 45877) (by norm_num)
theorem B1961765 : Blo 578813 1961765 := bbase (se 4 (by rfl) ⟨183915, by rfl⟩ : syracuseStep 1961765 = 367831) (by norm_num)
theorem B1306421 : Blo 578813 1306421 := bbase (se 5 (by rfl) ⟨61238, by rfl⟩ : syracuseStep 1306421 = 122477) (by norm_num)
theorem B618349 : Blo 578813 618349 := bbase (se 3 (by rfl) ⟨115940, by rfl⟩ : syracuseStep 618349 = 231881) (by norm_num)
theorem B978797 : Blo 578813 978797 := bbase (se 3 (by rfl) ⟨183524, by rfl⟩ : syracuseStep 978797 = 367049) (by norm_num)
theorem B1306493 : Blo 578813 1306493 := bbase (se 3 (by rfl) ⟨244967, by rfl⟩ : syracuseStep 1306493 = 489935) (by norm_num)
theorem B2977669 : Blo 578813 2977669 := bbase (se 4 (by rfl) ⟨279156, by rfl⟩ : syracuseStep 2977669 = 558313) (by norm_num)
theorem B1863557 : Blo 578813 1863557 := bbase (se 4 (by rfl) ⟨174708, by rfl⟩ : syracuseStep 1863557 = 349417) (by norm_num)
theorem B1044373 : Blo 578813 1044373 := bbase (se 6 (by rfl) ⟨24477, by rfl⟩ : syracuseStep 1044373 = 48955) (by norm_num)
theorem B651181 : Blo 578813 651181 := bbase (se 3 (by rfl) ⟨122096, by rfl⟩ : syracuseStep 651181 = 244193) (by norm_num)
theorem B1241021 : Blo 578813 1241021 := bbase (se 3 (by rfl) ⟨232691, by rfl⟩ : syracuseStep 1241021 = 465383) (by norm_num)
theorem B1306565 : Blo 578813 1306565 := bbase (se 4 (by rfl) ⟨122490, by rfl⟩ : syracuseStep 1306565 = 244981) (by norm_num)
theorem B1470413 : Blo 578813 1470413 := bbase (se 3 (by rfl) ⟨275702, by rfl⟩ : syracuseStep 1470413 = 551405) (by norm_num)
theorem B651217 : Blo 578813 651217 := bbase (se 2 (by rfl) ⟨244206, by rfl⟩ : syracuseStep 651217 = 488413) (by norm_num)
theorem B2944997 : Blo 578813 2944997 := bbase (se 4 (by rfl) ⟨276093, by rfl⟩ : syracuseStep 2944997 = 552187) (by norm_num)
theorem B618473 : Blo 578813 618473 := bbase (se 2 (by rfl) ⟨231927, by rfl⟩ : syracuseStep 618473 = 463855) (by norm_num)
theorem B978925 : Blo 578813 978925 := bbase (se 3 (by rfl) ⟨183548, by rfl⟩ : syracuseStep 978925 = 367097) (by norm_num)
theorem B651253 : Blo 578813 651253 := bbase (se 5 (by rfl) ⟨30527, by rfl⟩ : syracuseStep 651253 = 61055) (by norm_num)
theorem B1306637 : Blo 578813 1306637 := bbase (se 3 (by rfl) ⟨244994, by rfl⟩ : syracuseStep 1306637 = 489989) (by norm_num)
theorem B651289 : Blo 578813 651289 := bbase (se 2 (by rfl) ⟨244233, by rfl⟩ : syracuseStep 651289 = 488467) (by norm_num)
theorem B1044517 : Blo 578813 1044517 := bbase (se 4 (by rfl) ⟨97923, by rfl⟩ : syracuseStep 1044517 = 195847) (by norm_num)
theorem B651325 : Blo 578813 651325 := bbase (se 3 (by rfl) ⟨122123, by rfl⟩ : syracuseStep 651325 = 244247) (by norm_num)
theorem B979013 : Blo 578813 979013 := bbase (se 4 (by rfl) ⟨91782, by rfl⟩ : syracuseStep 979013 = 183565) (by norm_num)
theorem B1306709 : Blo 578813 1306709 := bbase (se 8 (by rfl) ⟨7656, by rfl⟩ : syracuseStep 1306709 = 15313) (by norm_num)
theorem B651361 : Blo 578813 651361 := bbase (se 2 (by rfl) ⟨244260, by rfl⟩ : syracuseStep 651361 = 488521) (by norm_num)
theorem B2355317 : Blo 578813 2355317 := bbase (se 5 (by rfl) ⟨110405, by rfl⟩ : syracuseStep 2355317 = 220811) (by norm_num)
theorem B651397 : Blo 578813 651397 := bbase (se 4 (by rfl) ⟨61068, by rfl⟩ : syracuseStep 651397 = 122137) (by norm_num)
theorem B1306781 : Blo 578813 1306781 := bbase (se 3 (by rfl) ⟨245021, by rfl⟩ : syracuseStep 1306781 = 490043) (by norm_num)
theorem B651433 : Blo 578813 651433 := bbase (se 2 (by rfl) ⟨244287, by rfl⟩ : syracuseStep 651433 = 488575) (by norm_num)
theorem B979141 : Blo 578813 979141 := bbase (se 4 (by rfl) ⟨91794, by rfl⟩ : syracuseStep 979141 = 183589) (by norm_num)
theorem B651469 : Blo 578813 651469 := bbase (se 3 (by rfl) ⟨122150, by rfl⟩ : syracuseStep 651469 = 244301) (by norm_num)
theorem B1962197 : Blo 578813 1962197 := bbase (se 7 (by rfl) ⟨22994, by rfl⟩ : syracuseStep 1962197 = 45989) (by norm_num)
theorem B618725 : Blo 578813 618725 := bbase (se 4 (by rfl) ⟨58005, by rfl⟩ : syracuseStep 618725 = 116011) (by norm_num)
theorem B1306853 : Blo 578813 1306853 := bbase (se 4 (by rfl) ⟨122517, by rfl⟩ : syracuseStep 1306853 = 245035) (by norm_num)
theorem B651505 : Blo 578813 651505 := bbase (se 2 (by rfl) ⟨244314, by rfl⟩ : syracuseStep 651505 = 488629) (by norm_num)
theorem B1044733 : Blo 578813 1044733 := bbase (se 3 (by rfl) ⟨195887, by rfl⟩ : syracuseStep 1044733 = 391775) (by norm_num)
theorem B651541 : Blo 578813 651541 := bbase (se 6 (by rfl) ⟨15270, by rfl⟩ : syracuseStep 651541 = 30541) (by norm_num)
theorem B979229 : Blo 578813 979229 := bbase (se 3 (by rfl) ⟨183605, by rfl⟩ : syracuseStep 979229 = 367211) (by norm_num)
theorem B1470757 : Blo 578813 1470757 := bbase (se 4 (by rfl) ⟨137883, by rfl⟩ : syracuseStep 1470757 = 275767) (by norm_num)
theorem B1306925 : Blo 578813 1306925 := bbase (se 3 (by rfl) ⟨245048, by rfl⟩ : syracuseStep 1306925 = 490097) (by norm_num)
theorem B651577 : Blo 578813 651577 := bbase (se 2 (by rfl) ⟨244341, by rfl⟩ : syracuseStep 651577 = 488683) (by norm_num)
theorem B782669 : Blo 578813 782669 := bbase (se 3 (by rfl) ⟨146750, by rfl⟩ : syracuseStep 782669 = 293501) (by norm_num)
theorem B651613 : Blo 578813 651613 := bbase (se 3 (by rfl) ⟨122177, by rfl⟩ : syracuseStep 651613 = 244355) (by norm_num)
theorem B1306997 : Blo 578813 1306997 := bbase (se 5 (by rfl) ⟨61265, by rfl⟩ : syracuseStep 1306997 = 122531) (by norm_num)
theorem B651649 : Blo 578813 651649 := bbase (se 2 (by rfl) ⟨244368, by rfl⟩ : syracuseStep 651649 = 488737) (by norm_num)
theorem B1470869 : Blo 578813 1470869 := bbase (se 6 (by rfl) ⟨34473, by rfl⟩ : syracuseStep 1470869 = 68947) (by norm_num)
theorem B979357 : Blo 578813 979357 := bbase (se 3 (by rfl) ⟨183629, by rfl⟩ : syracuseStep 979357 = 367259) (by norm_num)
theorem B651685 : Blo 578813 651685 := bbase (se 4 (by rfl) ⟨61095, by rfl⟩ : syracuseStep 651685 = 122191) (by norm_num)
theorem B1307069 : Blo 578813 1307069 := bbase (se 3 (by rfl) ⟨245075, by rfl⟩ : syracuseStep 1307069 = 490151) (by norm_num)
theorem B651721 : Blo 578813 651721 := bbase (se 2 (by rfl) ⟨244395, by rfl⟩ : syracuseStep 651721 = 488791) (by norm_num)
theorem B651757 : Blo 578813 651757 := bbase (se 3 (by rfl) ⟨122204, by rfl⟩ : syracuseStep 651757 = 244409) (by norm_num)
theorem B979445 : Blo 578813 979445 := bbase (se 5 (by rfl) ⟨45911, by rfl⟩ : syracuseStep 979445 = 91823) (by norm_num)
theorem B1307141 : Blo 578813 1307141 := bbase (se 4 (by rfl) ⟨122544, by rfl⟩ : syracuseStep 1307141 = 245089) (by norm_num)
theorem B651793 : Blo 578813 651793 := bbase (se 2 (by rfl) ⟨244422, by rfl⟩ : syracuseStep 651793 = 488845) (by norm_num)
theorem B651829 : Blo 578813 651829 := bbase (se 5 (by rfl) ⟨30554, by rfl⟩ : syracuseStep 651829 = 61109) (by norm_num)
theorem B1307213 : Blo 578813 1307213 := bbase (se 3 (by rfl) ⟨245102, by rfl⟩ : syracuseStep 1307213 = 490205) (by norm_num)
theorem B1471061 : Blo 578813 1471061 := bbase (se 8 (by rfl) ⟨8619, by rfl⟩ : syracuseStep 1471061 = 17239) (by norm_num)
theorem B651865 : Blo 578813 651865 := bbase (se 2 (by rfl) ⟨244449, by rfl⟩ : syracuseStep 651865 = 488899) (by norm_num)
theorem B979573 : Blo 578813 979573 := bbase (se 5 (by rfl) ⟨45917, by rfl⟩ : syracuseStep 979573 = 91835) (by norm_num)
theorem B651901 : Blo 578813 651901 := bbase (se 3 (by rfl) ⟨122231, by rfl⟩ : syracuseStep 651901 = 244463) (by norm_num)
theorem B1962629 : Blo 578813 1962629 := bbase (se 4 (by rfl) ⟨183996, by rfl⟩ : syracuseStep 1962629 = 367993) (by norm_num)
theorem B1307285 : Blo 578813 1307285 := bbase (se 6 (by rfl) ⟨30639, by rfl⟩ : syracuseStep 1307285 = 61279) (by norm_num)
theorem B651937 : Blo 578813 651937 := bbase (se 2 (by rfl) ⟨244476, by rfl⟩ : syracuseStep 651937 = 488953) (by norm_num)
theorem B619169 : Blo 578813 619169 := bbase (se 2 (by rfl) ⟨232188, by rfl⟩ : syracuseStep 619169 = 464377) (by norm_num)
theorem B651973 : Blo 578813 651973 := bbase (se 4 (by rfl) ⟨61122, by rfl⟩ : syracuseStep 651973 = 122245) (by norm_num)
theorem B979661 : Blo 578813 979661 := bbase (se 3 (by rfl) ⟨183686, by rfl⟩ : syracuseStep 979661 = 367373) (by norm_num)
theorem B3306197 : Blo 578813 3306197 := bbase (se 7 (by rfl) ⟨38744, by rfl⟩ : syracuseStep 3306197 = 77489) (by norm_num)
theorem B1307357 : Blo 578813 1307357 := bbase (se 3 (by rfl) ⟨245129, by rfl⟩ : syracuseStep 1307357 = 490259) (by norm_num)
theorem B652009 : Blo 578813 652009 := bbase (se 2 (by rfl) ⟨244503, by rfl⟩ : syracuseStep 652009 = 489007) (by norm_num)
theorem B652045 : Blo 578813 652045 := bbase (se 3 (by rfl) ⟨122258, by rfl⟩ : syracuseStep 652045 = 244517) (by norm_num)
theorem B1307429 : Blo 578813 1307429 := bbase (se 4 (by rfl) ⟨122571, by rfl⟩ : syracuseStep 1307429 = 245143) (by norm_num)
theorem B652081 : Blo 578813 652081 := bbase (se 2 (by rfl) ⟨244530, by rfl⟩ : syracuseStep 652081 = 489061) (by norm_num)
theorem B1241909 : Blo 578813 1241909 := bbase (se 5 (by rfl) ⟨58214, by rfl⟩ : syracuseStep 1241909 = 116429) (by norm_num)
theorem B979789 : Blo 578813 979789 := bbase (se 3 (by rfl) ⟨183710, by rfl⟩ : syracuseStep 979789 = 367421) (by norm_num)
theorem B652117 : Blo 578813 652117 := bbase (se 9 (by rfl) ⟨1910, by rfl⟩ : syracuseStep 652117 = 3821) (by norm_num)
theorem B5665621 : Blo 578813 5665621 := bbase (se 9 (by rfl) ⟨16598, by rfl⟩ : syracuseStep 5665621 = 33197) (by norm_num)
theorem B1307501 : Blo 578813 1307501 := bbase (se 3 (by rfl) ⟨245156, by rfl⟩ : syracuseStep 1307501 = 490313) (by norm_num)
theorem B652153 : Blo 578813 652153 := bbase (se 2 (by rfl) ⟨244557, by rfl⟩ : syracuseStep 652153 = 489115) (by norm_num)
theorem B619417 : Blo 578813 619417 := bbase (se 2 (by rfl) ⟨232281, by rfl⟩ : syracuseStep 619417 = 464563) (by norm_num)
theorem B652189 : Blo 578813 652189 := bbase (se 3 (by rfl) ⟨122285, by rfl⟩ : syracuseStep 652189 = 244571) (by norm_num)
theorem B979877 : Blo 578813 979877 := bbase (se 4 (by rfl) ⟨91863, by rfl⟩ : syracuseStep 979877 = 183727) (by norm_num)
theorem B1471405 : Blo 578813 1471405 := bbase (se 3 (by rfl) ⟨275888, by rfl⟩ : syracuseStep 1471405 = 551777) (by norm_num)
theorem B1242029 : Blo 578813 1242029 := bbase (se 3 (by rfl) ⟨232880, by rfl⟩ : syracuseStep 1242029 = 465761) (by norm_num)
theorem B1307573 : Blo 578813 1307573 := bbase (se 5 (by rfl) ⟨61292, by rfl⟩ : syracuseStep 1307573 = 122585) (by norm_num)
theorem B652225 : Blo 578813 652225 := bbase (se 2 (by rfl) ⟨244584, by rfl⟩ : syracuseStep 652225 = 489169) (by norm_num)
theorem B652261 : Blo 578813 652261 := bbase (se 4 (by rfl) ⟨61149, by rfl⟩ : syracuseStep 652261 = 122299) (by norm_num)
theorem B1307645 : Blo 578813 1307645 := bbase (se 3 (by rfl) ⟨245183, by rfl⟩ : syracuseStep 1307645 = 490367) (by norm_num)
theorem B652297 : Blo 578813 652297 := bbase (se 2 (by rfl) ⟨244611, by rfl⟩ : syracuseStep 652297 = 489223) (by norm_num)
theorem B1471517 : Blo 578813 1471517 := bbase (se 3 (by rfl) ⟨275909, by rfl⟩ : syracuseStep 1471517 = 551819) (by norm_num)
theorem B1045541 : Blo 578813 1045541 := bbase (se 4 (by rfl) ⟨98019, by rfl⟩ : syracuseStep 1045541 = 196039) (by norm_num)
theorem B980005 : Blo 578813 980005 := bbase (se 4 (by rfl) ⟨91875, by rfl⟩ : syracuseStep 980005 = 183751) (by norm_num)
theorem B652333 : Blo 578813 652333 := bbase (se 3 (by rfl) ⟨122312, by rfl⟩ : syracuseStep 652333 = 244625) (by norm_num)
theorem B1569845 : Blo 578813 1569845 := bbase (se 5 (by rfl) ⟨73586, by rfl⟩ : syracuseStep 1569845 = 147173) (by norm_num)
theorem B1963061 : Blo 578813 1963061 := bbase (se 5 (by rfl) ⟨92018, by rfl⟩ : syracuseStep 1963061 = 184037) (by norm_num)
theorem B1307717 : Blo 578813 1307717 := bbase (se 4 (by rfl) ⟨122598, by rfl⟩ : syracuseStep 1307717 = 245197) (by norm_num)
theorem B652369 : Blo 578813 652369 := bbase (se 2 (by rfl) ⟨244638, by rfl⟩ : syracuseStep 652369 = 489277) (by norm_num)
theorem B652405 : Blo 578813 652405 := bbase (se 5 (by rfl) ⟨30581, by rfl⟩ : syracuseStep 652405 = 61163) (by norm_num)
theorem B980093 : Blo 578813 980093 := bbase (se 3 (by rfl) ⟨183767, by rfl⟩ : syracuseStep 980093 = 367535) (by norm_num)
theorem B1307789 : Blo 578813 1307789 := bbase (se 3 (by rfl) ⟨245210, by rfl⟩ : syracuseStep 1307789 = 490421) (by norm_num)
theorem B3536021 : Blo 578813 3536021 := bbase (se 6 (by rfl) ⟨82875, by rfl⟩ : syracuseStep 3536021 = 165751) (by norm_num)
theorem B652441 : Blo 578813 652441 := bbase (se 2 (by rfl) ⟨244665, by rfl⟩ : syracuseStep 652441 = 489331) (by norm_num)
theorem B652477 : Blo 578813 652477 := bbase (se 3 (by rfl) ⟨122339, by rfl⟩ : syracuseStep 652477 = 244679) (by norm_num)
theorem B1307861 : Blo 578813 1307861 := bbase (se 7 (by rfl) ⟨15326, by rfl⟩ : syracuseStep 1307861 = 30653) (by norm_num)
theorem B2487509 : Blo 578813 2487509 := bbase (se 7 (by rfl) ⟨29150, by rfl⟩ : syracuseStep 2487509 = 58301) (by norm_num)
theorem B586973 : Blo 578813 586973 := bbase (se 3 (by rfl) ⟨110057, by rfl⟩ : syracuseStep 586973 = 220115) (by norm_num)
theorem B1471709 : Blo 578813 1471709 := bbase (se 3 (by rfl) ⟨275945, by rfl⟩ : syracuseStep 1471709 = 551891) (by norm_num)
theorem B652513 : Blo 578813 652513 := bbase (se 2 (by rfl) ⟨244692, by rfl⟩ : syracuseStep 652513 = 489385) (by norm_num)
theorem B4715765 : Blo 578813 4715765 := bbase (se 5 (by rfl) ⟨221051, by rfl⟩ : syracuseStep 4715765 = 442103) (by norm_num)
theorem B2946293 : Blo 578813 2946293 := bbase (se 5 (by rfl) ⟨138107, by rfl⟩ : syracuseStep 2946293 = 276215) (by norm_num)
theorem B980221 : Blo 578813 980221 := bbase (se 3 (by rfl) ⟨183791, by rfl⟩ : syracuseStep 980221 = 367583) (by norm_num)
theorem B652549 : Blo 578813 652549 := bbase (se 4 (by rfl) ⟨61176, by rfl⟩ : syracuseStep 652549 = 122353) (by norm_num)
theorem B1307933 : Blo 578813 1307933 := bbase (se 3 (by rfl) ⟨245237, by rfl⟩ : syracuseStep 1307933 = 490475) (by norm_num)
theorem B652585 : Blo 578813 652585 := bbase (se 2 (by rfl) ⟨244719, by rfl⟩ : syracuseStep 652585 = 489439) (by norm_num)
theorem B652621 : Blo 578813 652621 := bbase (se 3 (by rfl) ⟨122366, by rfl⟩ : syracuseStep 652621 = 244733) (by norm_num)
theorem B619861 : Blo 578813 619861 := bbase (se 13 (by rfl) ⟨113, by rfl⟩ : syracuseStep 619861 = 227) (by norm_num)
theorem B980309 : Blo 578813 980309 := bbase (se 13 (by rfl) ⟨179, by rfl⟩ : syracuseStep 980309 = 359) (by norm_num)
theorem B1308005 : Blo 578813 1308005 := bbase (se 4 (by rfl) ⟨122625, by rfl⟩ : syracuseStep 1308005 = 245251) (by norm_num)
theorem B652657 : Blo 578813 652657 := bbase (se 2 (by rfl) ⟨244746, by rfl⟩ : syracuseStep 652657 = 489493) (by norm_num)
theorem B619921 : Blo 578813 619921 := bbase (se 2 (by rfl) ⟨232470, by rfl⟩ : syracuseStep 619921 = 464941) (by norm_num)
theorem B652693 : Blo 578813 652693 := bbase (se 6 (by rfl) ⟨15297, by rfl⟩ : syracuseStep 652693 = 30595) (by norm_num)
theorem B2717093 : Blo 578813 2717093 := bbase (se 4 (by rfl) ⟨254727, by rfl⟩ : syracuseStep 2717093 = 509455) (by norm_num)
theorem B1308077 : Blo 578813 1308077 := bbase (se 3 (by rfl) ⟨245264, by rfl⟩ : syracuseStep 1308077 = 490529) (by norm_num)
theorem B652729 : Blo 578813 652729 := bbase (se 2 (by rfl) ⟨244773, by rfl⟩ : syracuseStep 652729 = 489547) (by norm_num)
theorem B980437 : Blo 578813 980437 := bbase (se 7 (by rfl) ⟨11489, by rfl⟩ : syracuseStep 980437 = 22979) (by norm_num)
theorem B652765 : Blo 578813 652765 := bbase (se 3 (by rfl) ⟨122393, by rfl⟩ : syracuseStep 652765 = 244787) (by norm_num)
theorem B1963493 : Blo 578813 1963493 := bbase (se 4 (by rfl) ⟨184077, by rfl⟩ : syracuseStep 1963493 = 368155) (by norm_num)
theorem B1308149 : Blo 578813 1308149 := bbase (se 5 (by rfl) ⟨61319, by rfl⟩ : syracuseStep 1308149 = 122639) (by norm_num)
theorem B652801 : Blo 578813 652801 := bbase (se 2 (by rfl) ⟨244800, by rfl⟩ : syracuseStep 652801 = 489601) (by norm_num)
theorem B4421141 : Blo 578813 4421141 := bbase (se 6 (by rfl) ⟨103620, by rfl⟩ : syracuseStep 4421141 = 207241) (by norm_num)
theorem B652837 : Blo 578813 652837 := bbase (se 4 (by rfl) ⟨61203, by rfl⟩ : syracuseStep 652837 = 122407) (by norm_num)
theorem B1242661 : Blo 578813 1242661 := bbase (se 4 (by rfl) ⟨116499, by rfl⟩ : syracuseStep 1242661 = 232999) (by norm_num)
theorem B980525 : Blo 578813 980525 := bbase (se 3 (by rfl) ⟨183848, by rfl⟩ : syracuseStep 980525 = 367697) (by norm_num)
theorem B1472053 : Blo 578813 1472053 := bbase (se 5 (by rfl) ⟨69002, by rfl⟩ : syracuseStep 1472053 = 138005) (by norm_num)
theorem B1308221 : Blo 578813 1308221 := bbase (se 3 (by rfl) ⟨245291, by rfl⟩ : syracuseStep 1308221 = 490583) (by norm_num)
theorem B652873 : Blo 578813 652873 := bbase (se 2 (by rfl) ⟨244827, by rfl⟩ : syracuseStep 652873 = 489655) (by norm_num)
theorem B652909 : Blo 578813 652909 := bbase (se 3 (by rfl) ⟨122420, by rfl⟩ : syracuseStep 652909 = 244841) (by norm_num)
theorem B1308293 : Blo 578813 1308293 := bbase (se 4 (by rfl) ⟨122652, by rfl⟩ : syracuseStep 1308293 = 245305) (by norm_num)
theorem B652945 : Blo 578813 652945 := bbase (se 2 (by rfl) ⟨244854, by rfl⟩ : syracuseStep 652945 = 489709) (by norm_num)
theorem B1472165 : Blo 578813 1472165 := bbase (se 4 (by rfl) ⟨138015, by rfl⟩ : syracuseStep 1472165 = 276031) (by norm_num)
theorem B980653 : Blo 578813 980653 := bbase (se 3 (by rfl) ⟨183872, by rfl⟩ : syracuseStep 980653 = 367745) (by norm_num)
theorem B652981 : Blo 578813 652981 := bbase (se 5 (by rfl) ⟨30608, by rfl⟩ : syracuseStep 652981 = 61217) (by norm_num)
theorem B620237 : Blo 578813 620237 := bbase (se 3 (by rfl) ⟨116294, by rfl⟩ : syracuseStep 620237 = 232589) (by norm_num)
theorem B1308365 : Blo 578813 1308365 := bbase (se 3 (by rfl) ⟨245318, by rfl⟩ : syracuseStep 1308365 = 490637) (by norm_num)
theorem B653017 : Blo 578813 653017 := bbase (se 2 (by rfl) ⟨244881, by rfl⟩ : syracuseStep 653017 = 489763) (by norm_num)
theorem B653053 : Blo 578813 653053 := bbase (se 3 (by rfl) ⟨122447, by rfl⟩ : syracuseStep 653053 = 244895) (by norm_num)
theorem B587521 : Blo 578813 587521 := bbase (se 2 (by rfl) ⟨220320, by rfl⟩ : syracuseStep 587521 = 440641) (by norm_num)
theorem B980741 : Blo 578813 980741 := bbase (se 4 (by rfl) ⟨91944, by rfl⟩ : syracuseStep 980741 = 183889) (by norm_num)
theorem B1865477 : Blo 578813 1865477 := bbase (se 4 (by rfl) ⟨174888, by rfl⟩ : syracuseStep 1865477 = 349777) (by norm_num)
theorem B1308437 : Blo 578813 1308437 := bbase (se 6 (by rfl) ⟨30666, by rfl⟩ : syracuseStep 1308437 = 61333) (by norm_num)
theorem B653089 : Blo 578813 653089 := bbase (se 2 (by rfl) ⟨244908, by rfl⟩ : syracuseStep 653089 = 489817) (by norm_num)
theorem B587557 : Blo 578813 587557 := bbase (se 4 (by rfl) ⟨55083, by rfl⟩ : syracuseStep 587557 = 110167) (by norm_num)
theorem B1046333 : Blo 578813 1046333 := bbase (se 3 (by rfl) ⟨196187, by rfl⟩ : syracuseStep 1046333 = 392375) (by norm_num)
theorem B653125 : Blo 578813 653125 := bbase (se 4 (by rfl) ⟨61230, by rfl⟩ : syracuseStep 653125 = 122461) (by norm_num)
theorem B1308509 : Blo 578813 1308509 := bbase (se 3 (by rfl) ⟨245345, by rfl⟩ : syracuseStep 1308509 = 490691) (by norm_num)
theorem B1472357 : Blo 578813 1472357 := bbase (se 4 (by rfl) ⟨138033, by rfl⟩ : syracuseStep 1472357 = 276067) (by norm_num)
theorem B653161 : Blo 578813 653161 := bbase (se 2 (by rfl) ⟨244935, by rfl⟩ : syracuseStep 653161 = 489871) (by norm_num)
theorem B980869 : Blo 578813 980869 := bbase (se 4 (by rfl) ⟨91956, by rfl⟩ : syracuseStep 980869 = 183913) (by norm_num)
theorem B653197 : Blo 578813 653197 := bbase (se 3 (by rfl) ⟨122474, by rfl⟩ : syracuseStep 653197 = 244949) (by norm_num)
theorem B1963925 : Blo 578813 1963925 := bbase (se 6 (by rfl) ⟨46029, by rfl⟩ : syracuseStep 1963925 = 92059) (by norm_num)
theorem B1308581 : Blo 578813 1308581 := bbase (se 4 (by rfl) ⟨122679, by rfl⟩ : syracuseStep 1308581 = 245359) (by norm_num)
theorem B653233 : Blo 578813 653233 := bbase (se 2 (by rfl) ⟨244962, by rfl⟩ : syracuseStep 653233 = 489925) (by norm_num)
theorem B1046477 : Blo 578813 1046477 := bbase (se 3 (by rfl) ⟨196214, by rfl⟩ : syracuseStep 1046477 = 392429) (by norm_num)
theorem B653269 : Blo 578813 653269 := bbase (se 7 (by rfl) ⟨7655, by rfl⟩ : syracuseStep 653269 = 15311) (by norm_num)
theorem B980957 : Blo 578813 980957 := bbase (se 3 (by rfl) ⟨183929, by rfl⟩ : syracuseStep 980957 = 367859) (by norm_num)
theorem B2357221 : Blo 578813 2357221 := bbase (se 4 (by rfl) ⟨220989, by rfl⟩ : syracuseStep 2357221 = 441979) (by norm_num)
theorem B1308653 : Blo 578813 1308653 := bbase (se 3 (by rfl) ⟨245372, by rfl⟩ : syracuseStep 1308653 = 490745) (by norm_num)
theorem B653305 : Blo 578813 653305 := bbase (se 2 (by rfl) ⟨244989, by rfl⟩ : syracuseStep 653305 = 489979) (by norm_num)
theorem B653341 : Blo 578813 653341 := bbase (se 3 (by rfl) ⟨122501, by rfl⟩ : syracuseStep 653341 = 245003) (by norm_num)
theorem B1046557 : Blo 578813 1046557 := bbase (se 3 (by rfl) ⟨196229, by rfl⟩ : syracuseStep 1046557 = 392459) (by norm_num)
theorem B1308725 : Blo 578813 1308725 := bbase (se 5 (by rfl) ⟨61346, by rfl⟩ : syracuseStep 1308725 = 122693) (by norm_num)
theorem B653377 : Blo 578813 653377 := bbase (se 2 (by rfl) ⟨245016, by rfl⟩ : syracuseStep 653377 = 490033) (by norm_num)
theorem B1046621 : Blo 578813 1046621 := bbase (se 3 (by rfl) ⟨196241, by rfl⟩ : syracuseStep 1046621 = 392483) (by norm_num)
theorem B981085 : Blo 578813 981085 := bbase (se 3 (by rfl) ⟨183953, by rfl⟩ : syracuseStep 981085 = 367907) (by norm_num)
theorem B653413 : Blo 578813 653413 := bbase (se 4 (by rfl) ⟨61257, by rfl⟩ : syracuseStep 653413 = 122515) (by norm_num)
theorem B1308797 : Blo 578813 1308797 := bbase (se 3 (by rfl) ⟨245399, by rfl⟩ : syracuseStep 1308797 = 490799) (by norm_num)
theorem B653449 : Blo 578813 653449 := bbase (se 2 (by rfl) ⟨245043, by rfl⟩ : syracuseStep 653449 = 490087) (by norm_num)
theorem B620681 : Blo 578813 620681 := bbase (se 2 (by rfl) ⟨232755, by rfl⟩ : syracuseStep 620681 = 465511) (by norm_num)
theorem B653485 : Blo 578813 653485 := bbase (se 3 (by rfl) ⟨122528, by rfl⟩ : syracuseStep 653485 = 245057) (by norm_num)
theorem B981173 : Blo 578813 981173 := bbase (se 5 (by rfl) ⟨45992, by rfl⟩ : syracuseStep 981173 = 91985) (by norm_num)
theorem B1472701 : Blo 578813 1472701 := bbase (se 3 (by rfl) ⟨276131, by rfl⟩ : syracuseStep 1472701 = 552263) (by norm_num)
theorem B620741 : Blo 578813 620741 := bbase (se 4 (by rfl) ⟨58194, by rfl⟩ : syracuseStep 620741 = 116389) (by norm_num)
theorem B1308869 : Blo 578813 1308869 := bbase (se 4 (by rfl) ⟨122706, by rfl⟩ : syracuseStep 1308869 = 245413) (by norm_num)
theorem B653521 : Blo 578813 653521 := bbase (se 2 (by rfl) ⟨245070, by rfl⟩ : syracuseStep 653521 = 490141) (by norm_num)
theorem B653557 : Blo 578813 653557 := bbase (se 5 (by rfl) ⟨30635, by rfl⟩ : syracuseStep 653557 = 61271) (by norm_num)
theorem B1308941 : Blo 578813 1308941 := bbase (se 3 (by rfl) ⟨245426, by rfl⟩ : syracuseStep 1308941 = 490853) (by norm_num)
theorem B653593 : Blo 578813 653593 := bbase (se 2 (by rfl) ⟨245097, by rfl⟩ : syracuseStep 653593 = 490195) (by norm_num)
theorem B784685 : Blo 578813 784685 := bbase (se 3 (by rfl) ⟨147128, by rfl⟩ : syracuseStep 784685 = 294257) (by norm_num)
theorem B1472813 : Blo 578813 1472813 := bbase (se 3 (by rfl) ⟨276152, by rfl⟩ : syracuseStep 1472813 = 552305) (by norm_num)
theorem B981301 : Blo 578813 981301 := bbase (se 5 (by rfl) ⟨45998, by rfl⟩ : syracuseStep 981301 = 91997) (by norm_num)
theorem B653629 : Blo 578813 653629 := bbase (se 3 (by rfl) ⟨122555, by rfl⟩ : syracuseStep 653629 = 245111) (by norm_num)
theorem B620869 : Blo 578813 620869 := bbase (se 4 (by rfl) ⟨58206, by rfl⟩ : syracuseStep 620869 = 116413) (by norm_num)
theorem B1964357 : Blo 578813 1964357 := bbase (se 4 (by rfl) ⟨184158, by rfl⟩ : syracuseStep 1964357 = 368317) (by norm_num)
theorem B1309013 : Blo 578813 1309013 := bbase (se 10 (by rfl) ⟨1917, by rfl⟩ : syracuseStep 1309013 = 3835) (by norm_num)
theorem B653665 : Blo 578813 653665 := bbase (se 2 (by rfl) ⟨245124, by rfl⟩ : syracuseStep 653665 = 490249) (by norm_num)
theorem B3733877 : Blo 578813 3733877 := bbase (se 5 (by rfl) ⟨175025, by rfl⟩ : syracuseStep 3733877 = 350051) (by norm_num)
theorem B653701 : Blo 578813 653701 := bbase (se 4 (by rfl) ⟨61284, by rfl⟩ : syracuseStep 653701 = 122569) (by norm_num)
theorem B981389 : Blo 578813 981389 := bbase (se 3 (by rfl) ⟨184010, by rfl⟩ : syracuseStep 981389 = 368021) (by norm_num)
theorem B1309085 : Blo 578813 1309085 := bbase (se 3 (by rfl) ⟨245453, by rfl⟩ : syracuseStep 1309085 = 490907) (by norm_num)
theorem B1243549 : Blo 578813 1243549 := bbase (se 3 (by rfl) ⟨233165, by rfl⟩ : syracuseStep 1243549 = 466331) (by norm_num)
theorem B653737 : Blo 578813 653737 := bbase (se 2 (by rfl) ⟨245151, by rfl⟩ : syracuseStep 653737 = 490303) (by norm_num)
theorem B653773 : Blo 578813 653773 := bbase (se 3 (by rfl) ⟨122582, by rfl⟩ : syracuseStep 653773 = 245165) (by norm_num)
theorem B1309157 : Blo 578813 1309157 := bbase (se 4 (by rfl) ⟨122733, by rfl⟩ : syracuseStep 1309157 = 245467) (by norm_num)
theorem B1473005 : Blo 578813 1473005 := bbase (se 3 (by rfl) ⟨276188, by rfl⟩ : syracuseStep 1473005 = 552377) (by norm_num)
theorem B653809 : Blo 578813 653809 := bbase (se 2 (by rfl) ⟨245178, by rfl⟩ : syracuseStep 653809 = 490357) (by norm_num)
theorem B2947589 : Blo 578813 2947589 := bbase (se 4 (by rfl) ⟨276336, by rfl⟩ : syracuseStep 2947589 = 552673) (by norm_num)
theorem B981517 : Blo 578813 981517 := bbase (se 3 (by rfl) ⟨184034, by rfl⟩ : syracuseStep 981517 = 368069) (by norm_num)
theorem B653845 : Blo 578813 653845 := bbase (se 6 (by rfl) ⟨15324, by rfl⟩ : syracuseStep 653845 = 30649) (by norm_num)
theorem B1243669 : Blo 578813 1243669 := bbase (se 6 (by rfl) ⟨29148, by rfl⟩ : syracuseStep 1243669 = 58297) (by norm_num)
theorem B1309229 : Blo 578813 1309229 := bbase (se 3 (by rfl) ⟨245480, by rfl⟩ : syracuseStep 1309229 = 490961) (by norm_num)
theorem B653881 : Blo 578813 653881 := bbase (se 2 (by rfl) ⟨245205, by rfl⟩ : syracuseStep 653881 = 490411) (by norm_num)
theorem B653917 : Blo 578813 653917 := bbase (se 3 (by rfl) ⟨122609, by rfl⟩ : syracuseStep 653917 = 245219) (by norm_num)
theorem B981605 : Blo 578813 981605 := bbase (se 4 (by rfl) ⟨92025, by rfl⟩ : syracuseStep 981605 = 184051) (by norm_num)
theorem B1309301 : Blo 578813 1309301 := bbase (se 5 (by rfl) ⟨61373, by rfl⟩ : syracuseStep 1309301 = 122747) (by norm_num)
theorem B653953 : Blo 578813 653953 := bbase (se 2 (by rfl) ⟨245232, by rfl⟩ : syracuseStep 653953 = 490465) (by norm_num)
theorem B653989 : Blo 578813 653989 := bbase (se 4 (by rfl) ⟨61311, by rfl⟩ : syracuseStep 653989 = 122623) (by norm_num)
theorem B1309373 : Blo 578813 1309373 := bbase (se 3 (by rfl) ⟨245507, by rfl⟩ : syracuseStep 1309373 = 491015) (by norm_num)
theorem B654025 : Blo 578813 654025 := bbase (se 2 (by rfl) ⟨245259, by rfl⟩ : syracuseStep 654025 = 490519) (by norm_num)
theorem B981733 : Blo 578813 981733 := bbase (se 4 (by rfl) ⟨92037, by rfl⟩ : syracuseStep 981733 = 184075) (by norm_num)
theorem B654061 : Blo 578813 654061 := bbase (se 3 (by rfl) ⟨122636, by rfl⟩ : syracuseStep 654061 = 245273) (by norm_num)
theorem B1964789 : Blo 578813 1964789 := bbase (se 5 (by rfl) ⟨92099, by rfl⟩ : syracuseStep 1964789 = 184199) (by norm_num)
theorem B621313 : Blo 578813 621313 := bbase (se 2 (by rfl) ⟨232992, by rfl⟩ : syracuseStep 621313 = 465985) (by norm_num)
theorem B1309445 : Blo 578813 1309445 := bbase (se 4 (by rfl) ⟨122760, by rfl⟩ : syracuseStep 1309445 = 245521) (by norm_num)
theorem B654097 : Blo 578813 654097 := bbase (se 2 (by rfl) ⟨245286, by rfl⟩ : syracuseStep 654097 = 490573) (by norm_num)
theorem B1243925 : Blo 578813 1243925 := bbase (se 6 (by rfl) ⟨29154, by rfl⟩ : syracuseStep 1243925 = 58309) (by norm_num)
theorem B654133 : Blo 578813 654133 := bbase (se 5 (by rfl) ⟨30662, by rfl⟩ : syracuseStep 654133 = 61325) (by norm_num)
theorem B981821 : Blo 578813 981821 := bbase (se 3 (by rfl) ⟨184091, by rfl⟩ : syracuseStep 981821 = 368183) (by norm_num)
theorem B1473349 : Blo 578813 1473349 := bbase (se 4 (by rfl) ⟨138126, by rfl⟩ : syracuseStep 1473349 = 276253) (by norm_num)
theorem B1309517 : Blo 578813 1309517 := bbase (se 3 (by rfl) ⟨245534, by rfl⟩ : syracuseStep 1309517 = 491069) (by norm_num)
theorem B654169 : Blo 578813 654169 := bbase (se 2 (by rfl) ⟨245313, by rfl⟩ : syracuseStep 654169 = 490627) (by norm_num)
theorem B621433 : Blo 578813 621433 := bbase (se 2 (by rfl) ⟨233037, by rfl⟩ : syracuseStep 621433 = 466075) (by norm_num)
theorem B654205 : Blo 578813 654205 := bbase (se 3 (by rfl) ⟨122663, by rfl⟩ : syracuseStep 654205 = 245327) (by norm_num)
theorem B1309589 : Blo 578813 1309589 := bbase (se 6 (by rfl) ⟨30693, by rfl⟩ : syracuseStep 1309589 = 61387) (by norm_num)
theorem B654241 : Blo 578813 654241 := bbase (se 2 (by rfl) ⟨245340, by rfl⟩ : syracuseStep 654241 = 490681) (by norm_num)
theorem B1473461 : Blo 578813 1473461 := bbase (se 5 (by rfl) ⟨69068, by rfl⟩ : syracuseStep 1473461 = 138137) (by norm_num)
theorem B981949 : Blo 578813 981949 := bbase (se 3 (by rfl) ⟨184115, by rfl⟩ : syracuseStep 981949 = 368231) (by norm_num)
theorem B654277 : Blo 578813 654277 := bbase (se 4 (by rfl) ⟨61338, by rfl⟩ : syracuseStep 654277 = 122677) (by norm_num)
theorem B2489285 : Blo 578813 2489285 := bbase (se 4 (by rfl) ⟨233370, by rfl⟩ : syracuseStep 2489285 = 466741) (by norm_num)
theorem B1309661 : Blo 578813 1309661 := bbase (se 3 (by rfl) ⟨245561, by rfl⟩ : syracuseStep 1309661 = 491123) (by norm_num)
theorem B588773 : Blo 578813 588773 := bbase (se 4 (by rfl) ⟨55197, by rfl⟩ : syracuseStep 588773 = 110395) (by norm_num)
theorem B654313 : Blo 578813 654313 := bbase (se 2 (by rfl) ⟨245367, by rfl⟩ : syracuseStep 654313 = 490735) (by norm_num)
theorem B654349 : Blo 578813 654349 := bbase (se 3 (by rfl) ⟨122690, by rfl⟩ : syracuseStep 654349 = 245381) (by norm_num)
theorem B982037 : Blo 578813 982037 := bbase (se 6 (by rfl) ⟨23016, by rfl⟩ : syracuseStep 982037 = 46033) (by norm_num)
theorem B1309733 : Blo 578813 1309733 := bbase (se 4 (by rfl) ⟨122787, by rfl⟩ : syracuseStep 1309733 = 245575) (by norm_num)
theorem B654385 : Blo 578813 654385 := bbase (se 2 (by rfl) ⟨245394, by rfl⟩ : syracuseStep 654385 = 490789) (by norm_num)
theorem B654421 : Blo 578813 654421 := bbase (se 8 (by rfl) ⟨3834, by rfl⟩ : syracuseStep 654421 = 7669) (by norm_num)
theorem B1309805 : Blo 578813 1309805 := bbase (se 3 (by rfl) ⟨245588, by rfl⟩ : syracuseStep 1309805 = 491177) (by norm_num)
theorem B621685 : Blo 578813 621685 := bbase (se 5 (by rfl) ⟨29141, by rfl⟩ : syracuseStep 621685 = 58283) (by norm_num)
theorem B1473653 : Blo 578813 1473653 := bbase (se 5 (by rfl) ⟨69077, by rfl⟩ : syracuseStep 1473653 = 138155) (by norm_num)
theorem B654457 : Blo 578813 654457 := bbase (se 2 (by rfl) ⟨245421, by rfl⟩ : syracuseStep 654457 = 490843) (by norm_num)
theorem B621689 : Blo 578813 621689 := bbase (se 2 (by rfl) ⟨233133, by rfl⟩ : syracuseStep 621689 = 466267) (by norm_num)
theorem B982165 : Blo 578813 982165 := bbase (se 6 (by rfl) ⟨23019, by rfl⟩ : syracuseStep 982165 = 46039) (by norm_num)
theorem B1866901 : Blo 578813 1866901 := bbase (se 6 (by rfl) ⟨43755, by rfl⟩ : syracuseStep 1866901 = 87511) (by norm_num)
theorem B654493 : Blo 578813 654493 := bbase (se 3 (by rfl) ⟨122717, by rfl⟩ : syracuseStep 654493 = 245435) (by norm_num)
theorem B1965221 : Blo 578813 1965221 := bbase (se 4 (by rfl) ⟨184239, by rfl⟩ : syracuseStep 1965221 = 368479) (by norm_num)
theorem B1309877 : Blo 578813 1309877 := bbase (se 5 (by rfl) ⟨61400, by rfl⟩ : syracuseStep 1309877 = 122801) (by norm_num)
theorem B654529 : Blo 578813 654529 := bbase (se 2 (by rfl) ⟨245448, by rfl⟩ : syracuseStep 654529 = 490897) (by norm_num)
theorem B654565 : Blo 578813 654565 := bbase (se 4 (by rfl) ⟨61365, by rfl⟩ : syracuseStep 654565 = 122731) (by norm_num)
theorem B589033 : Blo 578813 589033 := bbase (se 2 (by rfl) ⟨220887, by rfl⟩ : syracuseStep 589033 = 441775) (by norm_num)
theorem B982253 : Blo 578813 982253 := bbase (se 3 (by rfl) ⟨184172, by rfl⟩ : syracuseStep 982253 = 368345) (by norm_num)
theorem B1309949 : Blo 578813 1309949 := bbase (se 3 (by rfl) ⟨245615, by rfl⟩ : syracuseStep 1309949 = 491231) (by norm_num)
theorem B654601 : Blo 578813 654601 := bbase (se 2 (by rfl) ⟨245475, by rfl⟩ : syracuseStep 654601 = 490951) (by norm_num)
theorem B654637 : Blo 578813 654637 := bbase (se 3 (by rfl) ⟨122744, by rfl⟩ : syracuseStep 654637 = 245489) (by norm_num)
theorem B1310021 : Blo 578813 1310021 := bbase (se 4 (by rfl) ⟨122814, by rfl⟩ : syracuseStep 1310021 = 245629) (by norm_num)
theorem B654673 : Blo 578813 654673 := bbase (se 2 (by rfl) ⟨245502, by rfl⟩ : syracuseStep 654673 = 491005) (by norm_num)
theorem B982381 : Blo 578813 982381 := bbase (se 3 (by rfl) ⟨184196, by rfl⟩ : syracuseStep 982381 = 368393) (by norm_num)
theorem B654709 : Blo 578813 654709 := bbase (se 5 (by rfl) ⟨30689, by rfl⟩ : syracuseStep 654709 = 61379) (by norm_num)
theorem B1310093 : Blo 578813 1310093 := bbase (se 3 (by rfl) ⟨245642, by rfl⟩ : syracuseStep 1310093 = 491285) (by norm_num)
theorem B654745 : Blo 578813 654745 := bbase (se 2 (by rfl) ⟨245529, by rfl⟩ : syracuseStep 654745 = 491059) (by norm_num)
theorem B654781 : Blo 578813 654781 := bbase (se 3 (by rfl) ⟨122771, by rfl⟩ : syracuseStep 654781 = 245543) (by norm_num)
theorem B2358725 : Blo 578813 2358725 := bbase (se 4 (by rfl) ⟨221130, by rfl⟩ : syracuseStep 2358725 = 442261) (by norm_num)
theorem B982469 : Blo 578813 982469 := bbase (se 4 (by rfl) ⟨92106, by rfl⟩ : syracuseStep 982469 = 184213) (by norm_num)
theorem B1473997 : Blo 578813 1473997 := bbase (se 3 (by rfl) ⟨276374, by rfl⟩ : syracuseStep 1473997 = 552749) (by norm_num)
theorem B2784725 : Blo 578813 2784725 := bbase (se 7 (by rfl) ⟨32633, by rfl⟩ : syracuseStep 2784725 = 65267) (by norm_num)
theorem B1310165 : Blo 578813 1310165 := bbase (se 7 (by rfl) ⟨15353, by rfl⟩ : syracuseStep 1310165 = 30707) (by norm_num)
theorem B654817 : Blo 578813 654817 := bbase (se 2 (by rfl) ⟨245556, by rfl⟩ : syracuseStep 654817 = 491113) (by norm_num)
theorem B654853 : Blo 578813 654853 := bbase (se 4 (by rfl) ⟨61392, by rfl⟩ : syracuseStep 654853 = 122785) (by norm_num)
theorem B1310237 : Blo 578813 1310237 := bbase (se 3 (by rfl) ⟨245669, by rfl⟩ : syracuseStep 1310237 = 491339) (by norm_num)
theorem B654889 : Blo 578813 654889 := bbase (se 2 (by rfl) ⟨245583, by rfl⟩ : syracuseStep 654889 = 491167) (by norm_num)
theorem B1474109 : Blo 578813 1474109 := bbase (se 3 (by rfl) ⟨276395, by rfl⟩ : syracuseStep 1474109 = 552791) (by norm_num)
theorem B982597 : Blo 578813 982597 := bbase (se 4 (by rfl) ⟨92118, by rfl⟩ : syracuseStep 982597 = 184237) (by norm_num)
theorem B654925 : Blo 578813 654925 := bbase (se 3 (by rfl) ⟨122798, by rfl⟩ : syracuseStep 654925 = 245597) (by norm_num)
theorem B1965653 : Blo 578813 1965653 := bbase (se 8 (by rfl) ⟨11517, by rfl⟩ : syracuseStep 1965653 = 23035) (by norm_num)
theorem B1310309 : Blo 578813 1310309 := bbase (se 4 (by rfl) ⟨122841, by rfl⟩ : syracuseStep 1310309 = 245683) (by norm_num)
theorem B654961 : Blo 578813 654961 := bbase (se 2 (by rfl) ⟨245610, by rfl⟩ : syracuseStep 654961 = 491221) (by norm_num)
theorem B654997 : Blo 578813 654997 := bbase (se 6 (by rfl) ⟨15351, by rfl⟩ : syracuseStep 654997 = 30703) (by norm_num)
theorem B982685 : Blo 578813 982685 := bbase (se 3 (by rfl) ⟨184253, by rfl⟩ : syracuseStep 982685 = 368507) (by norm_num)
theorem B1310381 : Blo 578813 1310381 := bbase (se 3 (by rfl) ⟨245696, by rfl⟩ : syracuseStep 1310381 = 491393) (by norm_num)
theorem B622253 : Blo 578813 622253 := bbase (se 3 (by rfl) ⟨116672, by rfl⟩ : syracuseStep 622253 = 233345) (by norm_num)
theorem B655033 : Blo 578813 655033 := bbase (se 2 (by rfl) ⟨245637, by rfl⟩ : syracuseStep 655033 = 491275) (by norm_num)
theorem B655069 : Blo 578813 655069 := bbase (se 3 (by rfl) ⟨122825, by rfl⟩ : syracuseStep 655069 = 245651) (by norm_num)
theorem B1310453 : Blo 578813 1310453 := bbase (se 5 (by rfl) ⟨61427, by rfl⟩ : syracuseStep 1310453 = 122855) (by norm_num)
theorem B589565 : Blo 578813 589565 := bbase (se 3 (by rfl) ⟨110543, by rfl⟩ : syracuseStep 589565 = 221087) (by norm_num)
theorem B1474301 : Blo 578813 1474301 := bbase (se 3 (by rfl) ⟨276431, by rfl⟩ : syracuseStep 1474301 = 552863) (by norm_num)
theorem B655105 : Blo 578813 655105 := bbase (se 2 (by rfl) ⟨245664, by rfl⟩ : syracuseStep 655105 = 491329) (by norm_num)
theorem B2948885 : Blo 578813 2948885 := bbase (se 6 (by rfl) ⟨69114, by rfl⟩ : syracuseStep 2948885 = 138229) (by norm_num)
theorem B982813 : Blo 578813 982813 := bbase (se 3 (by rfl) ⟨184277, by rfl⟩ : syracuseStep 982813 = 368555) (by norm_num)
theorem B655141 : Blo 578813 655141 := bbase (se 4 (by rfl) ⟨61419, by rfl⟩ : syracuseStep 655141 = 122839) (by norm_num)
theorem B1310525 : Blo 578813 1310525 := bbase (se 3 (by rfl) ⟨245723, by rfl⟩ : syracuseStep 1310525 = 491447) (by norm_num)
theorem B655177 : Blo 578813 655177 := bbase (se 2 (by rfl) ⟨245691, by rfl⟩ : syracuseStep 655177 = 491383) (by norm_num)
theorem B655213 : Blo 578813 655213 := bbase (se 3 (by rfl) ⟨122852, by rfl⟩ : syracuseStep 655213 = 245705) (by norm_num)
theorem B982901 : Blo 578813 982901 := bbase (se 5 (by rfl) ⟨46073, by rfl⟩ : syracuseStep 982901 = 92147) (by norm_num)
theorem B1310597 : Blo 578813 1310597 := bbase (se 4 (by rfl) ⟨122868, by rfl⟩ : syracuseStep 1310597 = 245737) (by norm_num)
theorem B655249 : Blo 578813 655249 := bbase (se 2 (by rfl) ⟨245718, by rfl⟩ : syracuseStep 655249 = 491437) (by norm_num)
theorem B7438229 : Blo 578813 7438229 := bbase (se 6 (by rfl) ⟨174333, by rfl⟩ : syracuseStep 7438229 = 348667) (by norm_num)
theorem B655285 : Blo 578813 655285 := bbase (se 5 (by rfl) ⟨30716, by rfl⟩ : syracuseStep 655285 = 61433) (by norm_num)
theorem B1310669 : Blo 578813 1310669 := bbase (se 3 (by rfl) ⟨245750, by rfl⟩ : syracuseStep 1310669 = 491501) (by norm_num)
theorem B884693 : Blo 578813 884693 := bbase (se 7 (by rfl) ⟨10367, by rfl⟩ : syracuseStep 884693 = 20735) (by norm_num)
theorem B655321 : Blo 578813 655321 := bbase (se 2 (by rfl) ⟨245745, by rfl⟩ : syracuseStep 655321 = 491491) (by norm_num)
theorem B983029 : Blo 578813 983029 := bbase (se 5 (by rfl) ⟨46079, by rfl⟩ : syracuseStep 983029 = 92159) (by norm_num)
theorem B1310723 : Blo 578813 1310723 := bstep (se 1 (by rfl) ⟨983042, by rfl⟩ : syracuseStep 1310723 = 1966085) B1966085
theorem B1474595 : Blo 578813 1474595 := bstep (se 1 (by rfl) ⟨1105946, by rfl⟩ : syracuseStep 1474595 = 2211893) B2211893
theorem B655411 : Blo 578813 655411 := bstep (se 1 (by rfl) ⟨491558, by rfl⟩ : syracuseStep 655411 = 983117) B983117
theorem B983137 : Blo 578813 983137 := bstep (se 2 (by rfl) ⟨368676, by rfl⟩ : syracuseStep 983137 = 737353) B737353
theorem B2097265 : Blo 578813 2097265 := bstep (se 2 (by rfl) ⟨786474, by rfl⟩ : syracuseStep 2097265 = 1572949) B1572949
theorem B1966193 : Blo 578813 1966193 := bstep (se 2 (by rfl) ⟨737322, by rfl⟩ : syracuseStep 1966193 = 1474645) B1474645
theorem B983171 : Blo 578813 983171 := bstep (se 1 (by rfl) ⟨737378, by rfl⟩ : syracuseStep 983171 = 1474757) B1474757
theorem B3178673 : Blo 578813 3178673 := bstep (se 2 (by rfl) ⟨1192002, by rfl⟩ : syracuseStep 3178673 = 2384005) B2384005
theorem B655555 : Blo 578813 655555 := bstep (se 1 (by rfl) ⟨491666, by rfl⟩ : syracuseStep 655555 = 983333) B983333
theorem B1474787 : Blo 578813 1474787 := bstep (se 1 (by rfl) ⟨1106090, by rfl⟩ : syracuseStep 1474787 = 2212181) B2212181
theorem B983299 : Blo 578813 983299 := bstep (se 1 (by rfl) ⟨737474, by rfl⟩ : syracuseStep 983299 = 1474949) B1474949
theorem B1310993 : Blo 578813 1310993 := bstep (se 2 (by rfl) ⟨491622, by rfl⟩ : syracuseStep 1310993 = 983245) B983245
theorem B1311011 : Blo 578813 1311011 := bstep (se 1 (by rfl) ⟨983258, by rfl⟩ : syracuseStep 1311011 = 1966517) B1966517
theorem B983441 : Blo 578813 983441 := bstep (se 2 (by rfl) ⟨368790, by rfl⟩ : syracuseStep 983441 = 737581) B737581
theorem B4194787 : Blo 578813 4194787 := bstep (se 1 (by rfl) ⟨3146090, by rfl⟩ : syracuseStep 4194787 = 6292181) B6292181
theorem B1311281 : Blo 578813 1311281 := bstep (se 2 (by rfl) ⟨491730, by rfl⟩ : syracuseStep 1311281 = 983461) B983461
theorem B1311299 : Blo 578813 1311299 := bstep (se 1 (by rfl) ⟨983474, by rfl⟩ : syracuseStep 1311299 = 1966949) B1966949
theorem B3146309 : Blo 578813 3146309 := bstep (se 4 (by rfl) ⟨294966, by rfl⟩ : syracuseStep 3146309 = 589933) B589933
theorem B2228849 : Blo 578813 2228849 := bstep (se 2 (by rfl) ⟨835818, by rfl⟩ : syracuseStep 2228849 = 1671637) B1671637
theorem B1966733 : Blo 578813 1966733 := bstep (se 3 (by rfl) ⟨368762, by rfl⟩ : syracuseStep 1966733 = 737525) B737525
theorem B6357685 : Blo 578813 6357685 := bstep (se 5 (by rfl) ⟨298016, by rfl⟩ : syracuseStep 6357685 = 596033) B596033
theorem B1966787 : Blo 578813 1966787 := bstep (se 1 (by rfl) ⟨1475090, by rfl⟩ : syracuseStep 1966787 = 2950181) B2950181
theorem B2786147 : Blo 578813 2786147 := bstep (se 1 (by rfl) ⟨2089610, by rfl⟩ : syracuseStep 2786147 = 4179221) B4179221
theorem B1049635 : Blo 578813 1049635 := bstep (se 1 (by rfl) ⟨787226, by rfl⟩ : syracuseStep 1049635 = 1574453) B1574453
theorem B1573987 : Blo 578813 1573987 := bstep (se 1 (by rfl) ⟨1180490, by rfl⟩ : syracuseStep 1573987 = 2360981) B2360981
theorem B3540131 : Blo 578813 3540131 := bstep (se 1 (by rfl) ⟨2655098, by rfl⟩ : syracuseStep 3540131 = 5310197) B5310197
theorem B1574083 : Blo 578813 1574083 := bstep (se 1 (by rfl) ⟨1180562, by rfl⟩ : syracuseStep 1574083 = 2361125) B2361125
theorem B3146957 : Blo 578813 3146957 := bstep (se 3 (by rfl) ⟨590054, by rfl⟩ : syracuseStep 3146957 = 1180109) B1180109
theorem B4425029 : Blo 578813 4425029 := bstep (se 4 (by rfl) ⟨414846, by rfl⟩ : syracuseStep 4425029 = 829693) B829693
theorem B1050097 : Blo 578813 1050097 := bstep (se 2 (by rfl) ⟨393786, by rfl⟩ : syracuseStep 1050097 = 787573) B787573
theorem B2361905 : Blo 578813 2361905 := bstep (se 2 (by rfl) ⟨885714, by rfl⟩ : syracuseStep 2361905 = 1771429) B1771429
theorem B2198285 : Blo 578813 2198285 := bstep (se 3 (by rfl) ⟨412178, by rfl⟩ : syracuseStep 2198285 = 824357) B824357
theorem B2788145 : Blo 578813 2788145 := bstep (se 2 (by rfl) ⟨1045554, by rfl⟩ : syracuseStep 2788145 = 2091109) B2091109
theorem B1117489 : Blo 578813 1117489 := bstep (se 2 (by rfl) ⟨419058, by rfl⟩ : syracuseStep 1117489 = 838117) B838117
theorem B2788835 : Blo 578813 2788835 := bstep (se 1 (by rfl) ⟨2091626, by rfl⟩ : syracuseStep 2788835 = 4183253) B4183253
theorem B4197901 : Blo 578813 4197901 := bstep (se 3 (by rfl) ⟨787106, by rfl⟩ : syracuseStep 4197901 = 1574213) B1574213
theorem B2199089 : Blo 578813 2199089 := bstep (se 2 (by rfl) ⟨824658, by rfl⟩ : syracuseStep 2199089 = 1649317) B1649317
theorem B3313669 : Blo 578813 3313669 := bstep (se 4 (by rfl) ⟨310656, by rfl⟩ : syracuseStep 3313669 = 621313) B621313
theorem B2199757 : Blo 578813 2199757 := bstep (se 3 (by rfl) ⟨412454, by rfl⟩ : syracuseStep 2199757 = 824909) B824909
theorem B4952461 : Blo 578813 4952461 := bstep (se 3 (by rfl) ⟨928586, by rfl⟩ : syracuseStep 4952461 = 1857173) B1857173
theorem B2200547 : Blo 578813 2200547 := bstep (se 1 (by rfl) ⟨1650410, by rfl⟩ : syracuseStep 2200547 = 3300821) B3300821
theorem B1905677 : Blo 578813 1905677 := bstep (se 3 (by rfl) ⟨357314, by rfl⟩ : syracuseStep 1905677 = 714629) B714629
theorem B824465 : Blo 578813 824465 := bstep (se 2 (by rfl) ⟨309174, by rfl⟩ : syracuseStep 824465 = 618349) B618349
theorem B3970225 : Blo 578813 3970225 := bstep (se 2 (by rfl) ⟨1488834, by rfl⟩ : syracuseStep 3970225 = 2977669) B2977669
theorem B2790605 : Blo 578813 2790605 := bstep (se 3 (by rfl) ⟨523238, by rfl⟩ : syracuseStep 2790605 = 1046477) B1046477
theorem B1119505 : Blo 578813 1119505 := bstep (se 2 (by rfl) ⟨419814, by rfl⟩ : syracuseStep 1119505 = 839629) B839629
theorem B10065293 : Blo 578813 10065293 := bstep (se 3 (by rfl) ⟨1887242, by rfl⟩ : syracuseStep 10065293 = 3774485) B3774485
theorem B2790989 : Blo 578813 2790989 := bstep (se 3 (by rfl) ⟨523310, by rfl⟩ : syracuseStep 2790989 = 1046621) B1046621
theorem B2201201 : Blo 578813 2201201 := bstep (se 2 (by rfl) ⟨825450, by rfl⟩ : syracuseStep 2201201 = 1650901) B1650901
theorem B824995 : Blo 578813 824995 := bstep (se 1 (by rfl) ⟨618746, by rfl⟩ : syracuseStep 824995 = 1237493) B1237493
theorem B4953797 : Blo 578813 4953797 := bstep (se 4 (by rfl) ⟨464418, by rfl⟩ : syracuseStep 4953797 = 928837) B928837
theorem B1677133 : Blo 578813 1677133 := bstep (se 3 (by rfl) ⟨314462, by rfl⟩ : syracuseStep 1677133 = 628925) B628925
theorem B3315653 : Blo 578813 3315653 := bstep (se 4 (by rfl) ⟨310842, by rfl⟩ : syracuseStep 3315653 = 621685) B621685
theorem B825331 : Blo 578813 825331 := bstep (se 1 (by rfl) ⟨618998, by rfl⟩ : syracuseStep 825331 = 1237997) B1237997
theorem B825889 : Blo 578813 825889 := bstep (se 2 (by rfl) ⟨309708, by rfl⟩ : syracuseStep 825889 = 619417) B619417
theorem B825923 : Blo 578813 825923 := bstep (se 1 (by rfl) ⟨619442, by rfl⟩ : syracuseStep 825923 = 1238885) B1238885
theorem B3185315 : Blo 578813 3185315 := bstep (se 1 (by rfl) ⟨2388986, by rfl⟩ : syracuseStep 3185315 = 4777973) B4777973
theorem B5577443 : Blo 578813 5577443 := bstep (se 1 (by rfl) ⟨4183082, by rfl⟩ : syracuseStep 5577443 = 8366165) B8366165
theorem B1121105 : Blo 578813 1121105 := bstep (se 2 (by rfl) ⟨420414, by rfl⟩ : syracuseStep 1121105 = 840829) B840829
theorem B2202659 : Blo 578813 2202659 := bstep (se 1 (by rfl) ⟨1651994, by rfl⟩ : syracuseStep 2202659 = 3303989) B3303989
theorem B2202673 : Blo 578813 2202673 := bstep (se 2 (by rfl) ⟨826002, by rfl⟩ : syracuseStep 2202673 = 1652005) B1652005
theorem B826481 : Blo 578813 826481 := bstep (se 2 (by rfl) ⟨309930, by rfl⟩ : syracuseStep 826481 = 619861) B619861
theorem B826561 : Blo 578813 826561 := bstep (se 2 (by rfl) ⟨309960, by rfl⟩ : syracuseStep 826561 = 619921) B619921
theorem B1810097 : Blo 578813 1810097 := bstep (se 2 (by rfl) ⟨678786, by rfl⟩ : syracuseStep 1810097 = 1357573) B1357573
theorem B1023763 : Blo 578813 1023763 := bstep (se 1 (by rfl) ⟨767822, by rfl⟩ : syracuseStep 1023763 = 1535645) B1535645
theorem B64659221 : Blo 578813 64659221 := bstep (se 6 (by rfl) ⟨1515450, by rfl⟩ : syracuseStep 64659221 = 3030901) B3030901
theorem B1908611 : Blo 578813 1908611 := bstep (se 1 (by rfl) ⟨1431458, by rfl⟩ : syracuseStep 1908611 = 2862917) B2862917
theorem B827347 : Blo 578813 827347 := bstep (se 1 (by rfl) ⟨620510, by rfl⟩ : syracuseStep 827347 = 1241021) B1241021
theorem B598115 : Blo 578813 598115 := bstep (se 1 (by rfl) ⟨448586, by rfl⟩ : syracuseStep 598115 = 897173) B897173
theorem B10592369 : Blo 578813 10592369 := bstep (se 2 (by rfl) ⟨3972138, by rfl⟩ : syracuseStep 10592369 = 7944277) B7944277
theorem B827825 : Blo 578813 827825 := bstep (se 2 (by rfl) ⟨310434, by rfl⟩ : syracuseStep 827825 = 620869) B620869
theorem B2204131 : Blo 578813 2204131 := bstep (se 1 (by rfl) ⟨1653098, by rfl⟩ : syracuseStep 2204131 = 3306197) B3306197
theorem B827939 : Blo 578813 827939 := bstep (se 1 (by rfl) ⟨620954, by rfl⟩ : syracuseStep 827939 = 1241909) B1241909
theorem B828019 : Blo 578813 828019 := bstep (se 1 (by rfl) ⟨621014, by rfl⟩ : syracuseStep 828019 = 1242029) B1242029
theorem B1057411 : Blo 578813 1057411 := bstep (se 1 (by rfl) ⟨793058, by rfl⟩ : syracuseStep 1057411 = 1586117) B1586117
theorem B4399757 : Blo 578813 4399757 := bstep (se 3 (by rfl) ⟨824954, by rfl⟩ : syracuseStep 4399757 = 1649909) B1649909
theorem B697027 : Blo 578813 697027 := bstep (se 1 (by rfl) ⟨522770, by rfl⟩ : syracuseStep 697027 = 1045541) B1045541
theorem B6628067 : Blo 578813 6628067 := bstep (se 1 (by rfl) ⟨4971050, by rfl⟩ : syracuseStep 6628067 = 9942101) B9942101
theorem B2827043 : Blo 578813 2827043 := bstep (se 1 (by rfl) ⟨2120282, by rfl⟩ : syracuseStep 2827043 = 4240565) B4240565
theorem B1811395 : Blo 578813 1811395 := bstep (se 1 (by rfl) ⟨1358546, by rfl⟩ : syracuseStep 1811395 = 2717093) B2717093
theorem B1680365 : Blo 578813 1680365 := bstep (se 3 (by rfl) ⟨315068, by rfl⟩ : syracuseStep 1680365 = 630137) B630137
theorem B828577 : Blo 578813 828577 := bstep (se 2 (by rfl) ⟨310716, by rfl⟩ : syracuseStep 828577 = 621433) B621433
theorem B14165189 : Blo 578813 14165189 := bstep (se 4 (by rfl) ⟨1327986, by rfl⟩ : syracuseStep 14165189 = 2655973) B2655973
theorem B697555 : Blo 578813 697555 := bstep (se 1 (by rfl) ⟨523166, by rfl⟩ : syracuseStep 697555 = 1046333) B1046333
theorem B1648451 : Blo 578813 1648451 := bstep (se 1 (by rfl) ⟨1236338, by rfl⟩ : syracuseStep 1648451 = 2472677) B2472677
theorem B829283 : Blo 578813 829283 := bstep (se 1 (by rfl) ⟨621962, by rfl⟩ : syracuseStep 829283 = 1243925) B1243925
theorem B8071109 : Blo 578813 8071109 := bstep (se 4 (by rfl) ⟨756666, by rfl⟩ : syracuseStep 8071109 = 1513333) B1513333
theorem B1321219 : Blo 578813 1321219 := bstep (se 1 (by rfl) ⟨990914, by rfl⟩ : syracuseStep 1321219 = 1981829) B1981829
theorem B993665 : Blo 578813 993665 := bstep (se 2 (by rfl) ⟨372624, by rfl⟩ : syracuseStep 993665 = 745249) B745249
theorem B4958819 : Blo 578813 4958819 := bstep (se 1 (by rfl) ⟨3719114, by rfl⟩ : syracuseStep 4958819 = 7438229) B7438229
theorem B1649261 : Blo 578813 1649261 := bstep (se 3 (by rfl) ⟨309236, by rfl⟩ : syracuseStep 1649261 = 618473) B618473
theorem B2206349 : Blo 578813 2206349 := bstep (se 3 (by rfl) ⟨413690, by rfl⟩ : syracuseStep 2206349 = 827381) B827381
theorem B928433 : Blo 578813 928433 := bstep (se 2 (by rfl) ⟨348162, by rfl⟩ : syracuseStep 928433 = 696325) B696325
theorem B1649443 : Blo 578813 1649443 := bstep (se 1 (by rfl) ⟨1237082, by rfl⟩ : syracuseStep 1649443 = 2474165) B2474165
theorem B2010161 : Blo 578813 2010161 := bstep (se 2 (by rfl) ⟨753810, by rfl⟩ : syracuseStep 2010161 = 1507621) B1507621
theorem B3714245 : Blo 578813 3714245 := bstep (se 4 (by rfl) ⟨348210, by rfl⟩ : syracuseStep 3714245 = 696421) B696421
theorem B1649933 : Blo 578813 1649933 := bstep (se 3 (by rfl) ⟨309362, by rfl⟩ : syracuseStep 1649933 = 618725) B618725
theorem B4402673 : Blo 578813 4402673 := bstep (se 2 (by rfl) ⟨1651002, by rfl⟩ : syracuseStep 4402673 = 3302005) B3302005
theorem B15904309 : Blo 578813 15904309 := bstep (se 5 (by rfl) ⟨745514, by rfl⟩ : syracuseStep 15904309 = 1491029) B1491029
theorem B994945 : Blo 578813 994945 := bstep (se 2 (by rfl) ⟨373104, by rfl⟩ : syracuseStep 994945 = 746209) B746209
theorem B994979 : Blo 578813 994979 := bstep (se 1 (by rfl) ⟨746234, by rfl⟩ : syracuseStep 994979 = 1492469) B1492469
theorem B732883 : Blo 578813 732883 := bstep (se 1 (by rfl) ⟨549662, by rfl⟩ : syracuseStep 732883 = 1099325) B1099325
theorem B732979 : Blo 578813 732979 := bstep (se 1 (by rfl) ⟨549734, by rfl⟩ : syracuseStep 732979 = 1099469) B1099469
theorem B6697073 : Blo 578813 6697073 := bstep (se 2 (by rfl) ⟨2511402, by rfl⟩ : syracuseStep 6697073 = 5022805) B5022805
theorem B929971 : Blo 578813 929971 := bstep (se 1 (by rfl) ⟨697478, by rfl⟩ : syracuseStep 929971 = 1394957) B1394957
theorem B930017 : Blo 578813 930017 := bstep (se 2 (by rfl) ⟨348756, by rfl⟩ : syracuseStep 930017 = 697513) B697513
theorem B733475 : Blo 578813 733475 := bstep (se 1 (by rfl) ⟨550106, by rfl⟩ : syracuseStep 733475 = 1100213) B1100213
theorem B1651117 : Blo 578813 1651117 := bstep (se 3 (by rfl) ⟨309584, by rfl⟩ : syracuseStep 1651117 = 619169) B619169
theorem B996259 : Blo 578813 996259 := bstep (se 1 (by rfl) ⟨747194, by rfl⟩ : syracuseStep 996259 = 1494389) B1494389
theorem B734179 : Blo 578813 734179 := bstep (se 1 (by rfl) ⟨550634, by rfl⟩ : syracuseStep 734179 = 1101269) B1101269
theorem B2798563 : Blo 578813 2798563 := bstep (se 1 (by rfl) ⟨2098922, by rfl⟩ : syracuseStep 2798563 = 4197845) B4197845
theorem B734275 : Blo 578813 734275 := bstep (se 1 (by rfl) ⟨550706, by rfl⟩ : syracuseStep 734275 = 1101413) B1101413
theorem B931009 : Blo 578813 931009 := bstep (se 2 (by rfl) ⟨349128, by rfl⟩ : syracuseStep 931009 = 698257) B698257
theorem B1652177 : Blo 578813 1652177 := bstep (se 2 (by rfl) ⟨619566, by rfl⟩ : syracuseStep 1652177 = 1239133) B1239133
theorem B2209265 : Blo 578813 2209265 := bstep (se 2 (by rfl) ⟨828474, by rfl⟩ : syracuseStep 2209265 = 1656949) B1656949
theorem B734771 : Blo 578813 734771 := bstep (se 1 (by rfl) ⟨551078, by rfl⟩ : syracuseStep 734771 = 1102157) B1102157
theorem B931457 : Blo 578813 931457 := bstep (se 2 (by rfl) ⟨349296, by rfl⟩ : syracuseStep 931457 = 698593) B698593
theorem B3356293 : Blo 578813 3356293 := bstep (se 4 (by rfl) ⟨314652, by rfl⟩ : syracuseStep 3356293 = 629305) B629305
theorem B2930417 : Blo 578813 2930417 := bstep (se 2 (by rfl) ⟨1098906, by rfl⟩ : syracuseStep 2930417 = 2197813) B2197813
theorem B3389219 : Blo 578813 3389219 := bstep (se 1 (by rfl) ⟨2541914, by rfl⟩ : syracuseStep 3389219 = 5083829) B5083829
theorem B1652849 : Blo 578813 1652849 := bstep (se 2 (by rfl) ⟨619818, by rfl⟩ : syracuseStep 1652849 = 1239637) B1239637
theorem B4962545 : Blo 578813 4962545 := bstep (se 2 (by rfl) ⟨1860954, by rfl⟩ : syracuseStep 4962545 = 3721909) B3721909
theorem B735475 : Blo 578813 735475 := bstep (se 1 (by rfl) ⟨551606, by rfl⟩ : syracuseStep 735475 = 1103213) B1103213
theorem B735571 : Blo 578813 735571 := bstep (se 1 (by rfl) ⟨551678, by rfl⟩ : syracuseStep 735571 = 1103357) B1103357
theorem B1325425 : Blo 578813 1325425 := bstep (se 2 (by rfl) ⟨497034, by rfl⟩ : syracuseStep 1325425 = 994069) B994069
theorem B932323 : Blo 578813 932323 := bstep (se 1 (by rfl) ⟨699242, by rfl⟩ : syracuseStep 932323 = 1398485) B1398485
theorem B3717809 : Blo 578813 3717809 := bstep (se 2 (by rfl) ⟨1394178, by rfl⟩ : syracuseStep 3717809 = 2788357) B2788357
theorem B736067 : Blo 578813 736067 := bstep (se 1 (by rfl) ⟨552050, by rfl⟩ : syracuseStep 736067 = 1104101) B1104101
theorem B1653635 : Blo 578813 1653635 := bstep (se 1 (by rfl) ⟨1240226, by rfl⟩ : syracuseStep 1653635 = 2480453) B2480453
theorem B2210723 : Blo 578813 2210723 := bstep (se 1 (by rfl) ⟨1658042, by rfl⟩ : syracuseStep 2210723 = 3316085) B3316085
theorem B3521549 : Blo 578813 3521549 := bstep (se 3 (by rfl) ⟨660290, by rfl⟩ : syracuseStep 3521549 = 1320581) B1320581
theorem B932995 : Blo 578813 932995 := bstep (se 1 (by rfl) ⟨699746, by rfl⟩ : syracuseStep 932995 = 1399493) B1399493
theorem B2931875 : Blo 578813 2931875 := bstep (se 1 (by rfl) ⟨2198906, by rfl⟩ : syracuseStep 2931875 = 4397813) B4397813
theorem B933041 : Blo 578813 933041 := bstep (se 2 (by rfl) ⟨349890, by rfl⟩ : syracuseStep 933041 = 699781) B699781
theorem B1653965 : Blo 578813 1653965 := bstep (se 3 (by rfl) ⟨310118, by rfl⟩ : syracuseStep 1653965 = 620237) B620237
theorem B1391843 : Blo 578813 1391843 := bstep (se 1 (by rfl) ⟨1043882, by rfl⟩ : syracuseStep 1391843 = 2087765) B2087765
theorem B1654033 : Blo 578813 1654033 := bstep (se 2 (by rfl) ⟨620262, by rfl⟩ : syracuseStep 1654033 = 1240525) B1240525
theorem B3980677 : Blo 578813 3980677 := bstep (se 4 (by rfl) ⟨373188, by rfl⟩ : syracuseStep 3980677 = 746377) B746377
theorem B736771 : Blo 578813 736771 := bstep (se 1 (by rfl) ⟨552578, by rfl⟩ : syracuseStep 736771 = 1105157) B1105157
theorem B4472333 : Blo 578813 4472333 := bstep (se 3 (by rfl) ⟨838562, by rfl⟩ : syracuseStep 4472333 = 1677125) B1677125
theorem B1654307 : Blo 578813 1654307 := bstep (se 1 (by rfl) ⟨1240730, by rfl⟩ : syracuseStep 1654307 = 2481461) B2481461
theorem B3358307 : Blo 578813 3358307 := bstep (se 1 (by rfl) ⟨2518730, by rfl⟩ : syracuseStep 3358307 = 5037461) B5037461
theorem B736867 : Blo 578813 736867 := bstep (se 1 (by rfl) ⟨552650, by rfl⟩ : syracuseStep 736867 = 1105301) B1105301
theorem B933553 : Blo 578813 933553 := bstep (se 2 (by rfl) ⟨350082, by rfl⟩ : syracuseStep 933553 = 700165) B700165
theorem B1883917 : Blo 578813 1883917 := bstep (se 3 (by rfl) ⟨353234, by rfl⟩ : syracuseStep 1883917 = 706469) B706469
theorem B1392419 : Blo 578813 1392419 := bstep (se 1 (by rfl) ⟨1044314, by rfl⟩ : syracuseStep 1392419 = 2088629) B2088629
theorem B3129137 : Blo 578813 3129137 := bstep (se 2 (by rfl) ⟨1173426, by rfl⟩ : syracuseStep 3129137 = 2346853) B2346853
theorem B1392497 : Blo 578813 1392497 := bstep (se 2 (by rfl) ⟨522186, by rfl⟩ : syracuseStep 1392497 = 1044373) B1044373
theorem B2211725 : Blo 578813 2211725 := bstep (se 3 (by rfl) ⟨414698, by rfl⟩ : syracuseStep 2211725 = 829397) B829397
theorem B868241 : Blo 578813 868241 := bstep (se 2 (by rfl) ⟨325590, by rfl⟩ : syracuseStep 868241 = 651181) B651181
theorem B868259 : Blo 578813 868259 := bstep (se 1 (by rfl) ⟨651194, by rfl⟩ : syracuseStep 868259 = 1302389) B1302389
theorem B868289 : Blo 578813 868289 := bstep (se 2 (by rfl) ⟨325608, by rfl⟩ : syracuseStep 868289 = 651217) B651217
theorem B2932685 : Blo 578813 2932685 := bstep (se 3 (by rfl) ⟨549878, by rfl⟩ : syracuseStep 2932685 = 1099757) B1099757
theorem B868307 : Blo 578813 868307 := bstep (se 1 (by rfl) ⟨651230, by rfl⟩ : syracuseStep 868307 = 1302461) B1302461
theorem B1294321 : Blo 578813 1294321 := bstep (se 2 (by rfl) ⟨485370, by rfl⟩ : syracuseStep 1294321 = 970741) B970741
theorem B868337 : Blo 578813 868337 := bstep (se 2 (by rfl) ⟨325626, by rfl⟩ : syracuseStep 868337 = 651253) B651253
theorem B868355 : Blo 578813 868355 := bstep (se 1 (by rfl) ⟨651266, by rfl⟩ : syracuseStep 868355 = 1302533) B1302533
theorem B868385 : Blo 578813 868385 := bstep (se 2 (by rfl) ⟨325644, by rfl⟩ : syracuseStep 868385 = 651289) B651289
theorem B966691 : Blo 578813 966691 := bstep (se 1 (by rfl) ⟨725018, by rfl⟩ : syracuseStep 966691 = 1450037) B1450037
theorem B1392689 : Blo 578813 1392689 := bstep (se 2 (by rfl) ⟨522258, by rfl⟩ : syracuseStep 1392689 = 1044517) B1044517
theorem B868403 : Blo 578813 868403 := bstep (se 1 (by rfl) ⟨651302, by rfl⟩ : syracuseStep 868403 = 1302605) B1302605
theorem B868433 : Blo 578813 868433 := bstep (se 2 (by rfl) ⟨325662, by rfl⟩ : syracuseStep 868433 = 651325) B651325
theorem B737363 : Blo 578813 737363 := bstep (se 1 (by rfl) ⟨553022, by rfl⟩ : syracuseStep 737363 = 1106045) B1106045
theorem B868451 : Blo 578813 868451 := bstep (se 1 (by rfl) ⟨651338, by rfl⟩ : syracuseStep 868451 = 1302677) B1302677
theorem B3719267 : Blo 578813 3719267 := bstep (se 1 (by rfl) ⟨2789450, by rfl⟩ : syracuseStep 3719267 = 5578901) B5578901
theorem B868481 : Blo 578813 868481 := bstep (se 2 (by rfl) ⟨325680, by rfl⟩ : syracuseStep 868481 = 651361) B651361
theorem B868499 : Blo 578813 868499 := bstep (se 1 (by rfl) ⟨651374, by rfl⟩ : syracuseStep 868499 = 1302749) B1302749
theorem B868529 : Blo 578813 868529 := bstep (se 2 (by rfl) ⟨325698, by rfl⟩ : syracuseStep 868529 = 651397) B651397
theorem B868547 : Blo 578813 868547 := bstep (se 1 (by rfl) ⟨651410, by rfl⟩ : syracuseStep 868547 = 1302821) B1302821
theorem B868577 : Blo 578813 868577 := bstep (se 2 (by rfl) ⟨325716, by rfl⟩ : syracuseStep 868577 = 651433) B651433
theorem B868595 : Blo 578813 868595 := bstep (se 1 (by rfl) ⟨651446, by rfl⟩ : syracuseStep 868595 = 1302893) B1302893
theorem B868625 : Blo 578813 868625 := bstep (se 2 (by rfl) ⟨325734, by rfl⟩ : syracuseStep 868625 = 651469) B651469
theorem B868643 : Blo 578813 868643 := bstep (se 1 (by rfl) ⟨651482, by rfl⟩ : syracuseStep 868643 = 1302965) B1302965
theorem B868673 : Blo 578813 868673 := bstep (se 2 (by rfl) ⟨325752, by rfl⟩ : syracuseStep 868673 = 651505) B651505
theorem B2474317 : Blo 578813 2474317 := bstep (se 3 (by rfl) ⟨463934, by rfl⟩ : syracuseStep 2474317 = 927869) B927869
theorem B1392977 : Blo 578813 1392977 := bstep (se 2 (by rfl) ⟨522366, by rfl⟩ : syracuseStep 1392977 = 1044733) B1044733
theorem B868691 : Blo 578813 868691 := bstep (se 1 (by rfl) ⟨651518, by rfl⟩ : syracuseStep 868691 = 1303037) B1303037
theorem B1655149 : Blo 578813 1655149 := bstep (se 3 (by rfl) ⟨310340, by rfl⟩ : syracuseStep 1655149 = 620681) B620681
theorem B868721 : Blo 578813 868721 := bstep (se 2 (by rfl) ⟨325770, by rfl⟩ : syracuseStep 868721 = 651541) B651541
theorem B868739 : Blo 578813 868739 := bstep (se 1 (by rfl) ⟨651554, by rfl⟩ : syracuseStep 868739 = 1303109) B1303109
theorem B868769 : Blo 578813 868769 := bstep (se 2 (by rfl) ⟨325788, by rfl⟩ : syracuseStep 868769 = 651577) B651577
theorem B868787 : Blo 578813 868787 := bstep (se 1 (by rfl) ⟨651590, by rfl⟩ : syracuseStep 868787 = 1303181) B1303181
theorem B868817 : Blo 578813 868817 := bstep (se 2 (by rfl) ⟨325806, by rfl⟩ : syracuseStep 868817 = 651613) B651613
theorem B868835 : Blo 578813 868835 := bstep (se 1 (by rfl) ⟨651626, by rfl⟩ : syracuseStep 868835 = 1303253) B1303253
theorem B868865 : Blo 578813 868865 := bstep (se 2 (by rfl) ⟨325824, by rfl⟩ : syracuseStep 868865 = 651649) B651649
theorem B1655309 : Blo 578813 1655309 := bstep (se 3 (by rfl) ⟨310370, by rfl⟩ : syracuseStep 1655309 = 620741) B620741
theorem B868883 : Blo 578813 868883 := bstep (se 1 (by rfl) ⟨651662, by rfl⟩ : syracuseStep 868883 = 1303325) B1303325
theorem B868913 : Blo 578813 868913 := bstep (se 2 (by rfl) ⟨325842, by rfl⟩ : syracuseStep 868913 = 651685) B651685
theorem B868931 : Blo 578813 868931 := bstep (se 1 (by rfl) ⟨651698, by rfl⟩ : syracuseStep 868931 = 1303397) B1303397
theorem B868961 : Blo 578813 868961 := bstep (se 2 (by rfl) ⟨325860, by rfl⟩ : syracuseStep 868961 = 651721) B651721
theorem B868979 : Blo 578813 868979 := bstep (se 1 (by rfl) ⟨651734, by rfl⟩ : syracuseStep 868979 = 1303469) B1303469
theorem B869009 : Blo 578813 869009 := bstep (se 2 (by rfl) ⟨325878, by rfl⟩ : syracuseStep 869009 = 651757) B651757
theorem B869027 : Blo 578813 869027 := bstep (se 1 (by rfl) ⟨651770, by rfl⟩ : syracuseStep 869027 = 1303541) B1303541
theorem B869057 : Blo 578813 869057 := bstep (se 2 (by rfl) ⟨325896, by rfl⟩ : syracuseStep 869057 = 651793) B651793
theorem B1655491 : Blo 578813 1655491 := bstep (se 1 (by rfl) ⟨1241618, by rfl⟩ : syracuseStep 1655491 = 2483237) B2483237
theorem B869075 : Blo 578813 869075 := bstep (se 1 (by rfl) ⟨651806, by rfl⟩ : syracuseStep 869075 = 1303613) B1303613
theorem B869105 : Blo 578813 869105 := bstep (se 2 (by rfl) ⟨325914, by rfl⟩ : syracuseStep 869105 = 651829) B651829
theorem B869123 : Blo 578813 869123 := bstep (se 1 (by rfl) ⟨651842, by rfl⟩ : syracuseStep 869123 = 1303685) B1303685
theorem B869153 : Blo 578813 869153 := bstep (se 2 (by rfl) ⟨325932, by rfl⟩ : syracuseStep 869153 = 651865) B651865
theorem B869171 : Blo 578813 869171 := bstep (se 1 (by rfl) ⟨651878, by rfl⟩ : syracuseStep 869171 = 1303757) B1303757
theorem B869201 : Blo 578813 869201 := bstep (se 2 (by rfl) ⟨325950, by rfl⟩ : syracuseStep 869201 = 651901) B651901
theorem B869219 : Blo 578813 869219 := bstep (se 1 (by rfl) ⟨651914, by rfl⟩ : syracuseStep 869219 = 1303829) B1303829
theorem B869249 : Blo 578813 869249 := bstep (se 2 (by rfl) ⟨325968, by rfl⟩ : syracuseStep 869249 = 651937) B651937
theorem B869267 : Blo 578813 869267 := bstep (se 1 (by rfl) ⟨651950, by rfl⟩ : syracuseStep 869267 = 1303901) B1303901
theorem B869297 : Blo 578813 869297 := bstep (se 2 (by rfl) ⟨325986, by rfl⟩ : syracuseStep 869297 = 651973) B651973
theorem B869315 : Blo 578813 869315 := bstep (se 1 (by rfl) ⟨651986, by rfl⟩ : syracuseStep 869315 = 1303973) B1303973
theorem B869345 : Blo 578813 869345 := bstep (se 2 (by rfl) ⟨326004, by rfl⟩ : syracuseStep 869345 = 652009) B652009
theorem B869363 : Blo 578813 869363 := bstep (se 1 (by rfl) ⟨652022, by rfl⟩ : syracuseStep 869363 = 1304045) B1304045
theorem B869393 : Blo 578813 869393 := bstep (se 2 (by rfl) ⟨326022, by rfl⟩ : syracuseStep 869393 = 652045) B652045
theorem B869411 : Blo 578813 869411 := bstep (se 1 (by rfl) ⟨652058, by rfl⟩ : syracuseStep 869411 = 1304117) B1304117
theorem B869441 : Blo 578813 869441 := bstep (se 2 (by rfl) ⟨326040, by rfl⟩ : syracuseStep 869441 = 652081) B652081
theorem B3720269 : Blo 578813 3720269 := bstep (se 3 (by rfl) ⟨697550, by rfl⟩ : syracuseStep 3720269 = 1395101) B1395101
theorem B869459 : Blo 578813 869459 := bstep (se 1 (by rfl) ⟨652094, by rfl⟩ : syracuseStep 869459 = 1304189) B1304189
theorem B869489 : Blo 578813 869489 := bstep (se 2 (by rfl) ⟨326058, by rfl⟩ : syracuseStep 869489 = 652117) B652117
theorem B7554161 : Blo 578813 7554161 := bstep (se 2 (by rfl) ⟨2832810, by rfl⟩ : syracuseStep 7554161 = 5665621) B5665621
theorem B869507 : Blo 578813 869507 := bstep (se 1 (by rfl) ⟨652130, by rfl⟩ : syracuseStep 869507 = 1304261) B1304261
theorem B869537 : Blo 578813 869537 := bstep (se 2 (by rfl) ⟨326076, by rfl⟩ : syracuseStep 869537 = 652153) B652153
theorem B2507939 : Blo 578813 2507939 := bstep (se 1 (by rfl) ⟨1880954, by rfl⟩ : syracuseStep 2507939 = 3761909) B3761909
theorem B869555 : Blo 578813 869555 := bstep (se 1 (by rfl) ⟨652166, by rfl⟩ : syracuseStep 869555 = 1304333) B1304333
theorem B869585 : Blo 578813 869585 := bstep (se 2 (by rfl) ⟨326094, by rfl⟩ : syracuseStep 869585 = 652189) B652189
theorem B869603 : Blo 578813 869603 := bstep (se 1 (by rfl) ⟨652202, by rfl⟩ : syracuseStep 869603 = 1304405) B1304405
theorem B1885421 : Blo 578813 1885421 := bstep (se 3 (by rfl) ⟨353516, by rfl⟩ : syracuseStep 1885421 = 707033) B707033
theorem B869633 : Blo 578813 869633 := bstep (se 2 (by rfl) ⟨326112, by rfl⟩ : syracuseStep 869633 = 652225) B652225
theorem B869651 : Blo 578813 869651 := bstep (se 1 (by rfl) ⟨652238, by rfl⟩ : syracuseStep 869651 = 1304477) B1304477
theorem B869681 : Blo 578813 869681 := bstep (se 2 (by rfl) ⟨326130, by rfl⟩ : syracuseStep 869681 = 652261) B652261
theorem B869699 : Blo 578813 869699 := bstep (se 1 (by rfl) ⟨652274, by rfl⟩ : syracuseStep 869699 = 1304549) B1304549
theorem B869729 : Blo 578813 869729 := bstep (se 2 (by rfl) ⟨326148, by rfl⟩ : syracuseStep 869729 = 652297) B652297
theorem B869747 : Blo 578813 869747 := bstep (se 1 (by rfl) ⟨652310, by rfl⟩ : syracuseStep 869747 = 1304621) B1304621
theorem B869777 : Blo 578813 869777 := bstep (se 2 (by rfl) ⟨326166, by rfl⟩ : syracuseStep 869777 = 652333) B652333
theorem B869795 : Blo 578813 869795 := bstep (se 1 (by rfl) ⟨652346, by rfl⟩ : syracuseStep 869795 = 1304693) B1304693
theorem B869825 : Blo 578813 869825 := bstep (se 2 (by rfl) ⟨326184, by rfl⟩ : syracuseStep 869825 = 652369) B652369
theorem B869843 : Blo 578813 869843 := bstep (se 1 (by rfl) ⟨652382, by rfl⟩ : syracuseStep 869843 = 1304765) B1304765
theorem B869873 : Blo 578813 869873 := bstep (se 2 (by rfl) ⟨326202, by rfl⟩ : syracuseStep 869873 = 652405) B652405
theorem B869891 : Blo 578813 869891 := bstep (se 1 (by rfl) ⟨652418, by rfl⟩ : syracuseStep 869891 = 1304837) B1304837
theorem B869921 : Blo 578813 869921 := bstep (se 2 (by rfl) ⟨326220, by rfl⟩ : syracuseStep 869921 = 652441) B652441
theorem B706099 : Blo 578813 706099 := bstep (se 1 (by rfl) ⟨529574, by rfl⟩ : syracuseStep 706099 = 1059149) B1059149
theorem B869939 : Blo 578813 869939 := bstep (se 1 (by rfl) ⟨652454, by rfl⟩ : syracuseStep 869939 = 1304909) B1304909
theorem B869969 : Blo 578813 869969 := bstep (se 2 (by rfl) ⟨326238, by rfl⟩ : syracuseStep 869969 = 652477) B652477
theorem B869987 : Blo 578813 869987 := bstep (se 1 (by rfl) ⟨652490, by rfl⟩ : syracuseStep 869987 = 1304981) B1304981
theorem B870017 : Blo 578813 870017 := bstep (se 2 (by rfl) ⟨326256, by rfl⟩ : syracuseStep 870017 = 652513) B652513
theorem B870035 : Blo 578813 870035 := bstep (se 1 (by rfl) ⟨652526, by rfl⟩ : syracuseStep 870035 = 1305053) B1305053
theorem B870065 : Blo 578813 870065 := bstep (se 2 (by rfl) ⟨326274, by rfl⟩ : syracuseStep 870065 = 652549) B652549
theorem B870083 : Blo 578813 870083 := bstep (se 1 (by rfl) ⟨652562, by rfl⟩ : syracuseStep 870083 = 1305125) B1305125
theorem B870113 : Blo 578813 870113 := bstep (se 2 (by rfl) ⟨326292, by rfl⟩ : syracuseStep 870113 = 652585) B652585
theorem B4835057 : Blo 578813 4835057 := bstep (se 2 (by rfl) ⟨1813146, by rfl⟩ : syracuseStep 4835057 = 3626293) B3626293
theorem B870131 : Blo 578813 870131 := bstep (se 1 (by rfl) ⟨652598, by rfl⟩ : syracuseStep 870131 = 1305197) B1305197
theorem B870161 : Blo 578813 870161 := bstep (se 2 (by rfl) ⟨326310, by rfl⟩ : syracuseStep 870161 = 652621) B652621
theorem B870179 : Blo 578813 870179 := bstep (se 1 (by rfl) ⟨652634, by rfl⟩ : syracuseStep 870179 = 1305269) B1305269
theorem B870209 : Blo 578813 870209 := bstep (se 2 (by rfl) ⟨326328, by rfl⟩ : syracuseStep 870209 = 652657) B652657
theorem B870227 : Blo 578813 870227 := bstep (se 1 (by rfl) ⟨652670, by rfl⟩ : syracuseStep 870227 = 1305341) B1305341
theorem B870257 : Blo 578813 870257 := bstep (se 2 (by rfl) ⟨326346, by rfl⟩ : syracuseStep 870257 = 652693) B652693
theorem B1099651 : Blo 578813 1099651 := bstep (se 1 (by rfl) ⟨824738, by rfl⟩ : syracuseStep 1099651 = 1649477) B1649477
theorem B870275 : Blo 578813 870275 := bstep (se 1 (by rfl) ⟨652706, by rfl⟩ : syracuseStep 870275 = 1305413) B1305413
theorem B870305 : Blo 578813 870305 := bstep (se 2 (by rfl) ⟨326364, by rfl⟩ : syracuseStep 870305 = 652729) B652729
theorem B870323 : Blo 578813 870323 := bstep (se 1 (by rfl) ⟨652742, by rfl⟩ : syracuseStep 870323 = 1305485) B1305485
theorem B870353 : Blo 578813 870353 := bstep (se 2 (by rfl) ⟨326382, by rfl⟩ : syracuseStep 870353 = 652765) B652765
theorem B870371 : Blo 578813 870371 := bstep (se 1 (by rfl) ⟨652778, by rfl⟩ : syracuseStep 870371 = 1305557) B1305557
theorem B870401 : Blo 578813 870401 := bstep (se 2 (by rfl) ⟨326400, by rfl⟩ : syracuseStep 870401 = 652801) B652801
theorem B870419 : Blo 578813 870419 := bstep (se 1 (by rfl) ⟨652814, by rfl⟩ : syracuseStep 870419 = 1305629) B1305629
theorem B1099811 : Blo 578813 1099811 := bstep (se 1 (by rfl) ⟨824858, by rfl⟩ : syracuseStep 1099811 = 1649717) B1649717
theorem B870449 : Blo 578813 870449 := bstep (se 2 (by rfl) ⟨326418, by rfl⟩ : syracuseStep 870449 = 652837) B652837
theorem B1656881 : Blo 578813 1656881 := bstep (se 2 (by rfl) ⟨621330, by rfl⟩ : syracuseStep 1656881 = 1242661) B1242661
theorem B870467 : Blo 578813 870467 := bstep (se 1 (by rfl) ⟨652850, by rfl⟩ : syracuseStep 870467 = 1305701) B1305701
theorem B870497 : Blo 578813 870497 := bstep (se 2 (by rfl) ⟨326436, by rfl⟩ : syracuseStep 870497 = 652873) B652873
theorem B870515 : Blo 578813 870515 := bstep (se 1 (by rfl) ⟨652886, by rfl⟩ : syracuseStep 870515 = 1305773) B1305773
theorem B4966541 : Blo 578813 4966541 := bstep (se 3 (by rfl) ⟨931226, by rfl⟩ : syracuseStep 4966541 = 1862453) B1862453
theorem B870545 : Blo 578813 870545 := bstep (se 2 (by rfl) ⟨326454, by rfl⟩ : syracuseStep 870545 = 652909) B652909
theorem B870563 : Blo 578813 870563 := bstep (se 1 (by rfl) ⟨652922, by rfl⟩ : syracuseStep 870563 = 1305845) B1305845
theorem B870593 : Blo 578813 870593 := bstep (se 2 (by rfl) ⟨326472, by rfl⟩ : syracuseStep 870593 = 652945) B652945
theorem B870611 : Blo 578813 870611 := bstep (se 1 (by rfl) ⟨652958, by rfl⟩ : syracuseStep 870611 = 1305917) B1305917
theorem B870641 : Blo 578813 870641 := bstep (se 2 (by rfl) ⟨326490, by rfl⟩ : syracuseStep 870641 = 652981) B652981
theorem B870659 : Blo 578813 870659 := bstep (se 1 (by rfl) ⟨652994, by rfl⟩ : syracuseStep 870659 = 1305989) B1305989
theorem B22399253 : Blo 578813 22399253 := bstep (se 6 (by rfl) ⟨524982, by rfl⟩ : syracuseStep 22399253 = 1049965) B1049965
theorem B870689 : Blo 578813 870689 := bstep (se 2 (by rfl) ⟨326508, by rfl⟩ : syracuseStep 870689 = 653017) B653017
theorem B870707 : Blo 578813 870707 := bstep (se 1 (by rfl) ⟨653030, by rfl⟩ : syracuseStep 870707 = 1306061) B1306061
theorem B870737 : Blo 578813 870737 := bstep (se 2 (by rfl) ⟨326526, by rfl⟩ : syracuseStep 870737 = 653053) B653053
theorem B870755 : Blo 578813 870755 := bstep (se 1 (by rfl) ⟨653066, by rfl⟩ : syracuseStep 870755 = 1306133) B1306133
theorem B870785 : Blo 578813 870785 := bstep (se 2 (by rfl) ⟨326544, by rfl⟩ : syracuseStep 870785 = 653089) B653089
theorem B870803 : Blo 578813 870803 := bstep (se 1 (by rfl) ⟨653102, by rfl⟩ : syracuseStep 870803 = 1306205) B1306205
theorem B870833 : Blo 578813 870833 := bstep (se 2 (by rfl) ⟨326562, by rfl⟩ : syracuseStep 870833 = 653125) B653125
theorem B870851 : Blo 578813 870851 := bstep (se 1 (by rfl) ⟨653138, by rfl⟩ : syracuseStep 870851 = 1306277) B1306277
theorem B870881 : Blo 578813 870881 := bstep (se 2 (by rfl) ⟨326580, by rfl⟩ : syracuseStep 870881 = 653161) B653161
theorem B870899 : Blo 578813 870899 := bstep (se 1 (by rfl) ⟨653174, by rfl⟩ : syracuseStep 870899 = 1306349) B1306349
theorem B870929 : Blo 578813 870929 := bstep (se 2 (by rfl) ⟨326598, by rfl⟩ : syracuseStep 870929 = 653197) B653197
theorem B870947 : Blo 578813 870947 := bstep (se 1 (by rfl) ⟨653210, by rfl⟩ : syracuseStep 870947 = 1306421) B1306421
theorem B870977 : Blo 578813 870977 := bstep (se 2 (by rfl) ⟨326616, by rfl⟩ : syracuseStep 870977 = 653233) B653233
theorem B870995 : Blo 578813 870995 := bstep (se 1 (by rfl) ⟨653246, by rfl⟩ : syracuseStep 870995 = 1306493) B1306493
theorem B871025 : Blo 578813 871025 := bstep (se 2 (by rfl) ⟨326634, by rfl⟩ : syracuseStep 871025 = 653269) B653269
theorem B871043 : Blo 578813 871043 := bstep (se 1 (by rfl) ⟨653282, by rfl⟩ : syracuseStep 871043 = 1306565) B1306565
theorem B871073 : Blo 578813 871073 := bstep (se 2 (by rfl) ⟨326652, by rfl⟩ : syracuseStep 871073 = 653305) B653305
theorem B871091 : Blo 578813 871091 := bstep (se 1 (by rfl) ⟨653318, by rfl⟩ : syracuseStep 871091 = 1306637) B1306637
theorem B871121 : Blo 578813 871121 := bstep (se 2 (by rfl) ⟨326670, by rfl⟩ : syracuseStep 871121 = 653341) B653341
theorem B1395409 : Blo 578813 1395409 := bstep (se 2 (by rfl) ⟨523278, by rfl⟩ : syracuseStep 1395409 = 1046557) B1046557
theorem B871139 : Blo 578813 871139 := bstep (se 1 (by rfl) ⟨653354, by rfl⟩ : syracuseStep 871139 = 1306709) B1306709
theorem B871169 : Blo 578813 871169 := bstep (se 2 (by rfl) ⟨326688, by rfl⟩ : syracuseStep 871169 = 653377) B653377
theorem B871187 : Blo 578813 871187 := bstep (se 1 (by rfl) ⟨653390, by rfl⟩ : syracuseStep 871187 = 1306781) B1306781
theorem B2935601 : Blo 578813 2935601 := bstep (se 2 (by rfl) ⟨1100850, by rfl⟩ : syracuseStep 2935601 = 2201701) B2201701
theorem B871217 : Blo 578813 871217 := bstep (se 2 (by rfl) ⟨326706, by rfl⟩ : syracuseStep 871217 = 653413) B653413
theorem B871235 : Blo 578813 871235 := bstep (se 1 (by rfl) ⟨653426, by rfl⟩ : syracuseStep 871235 = 1306853) B1306853
theorem B871265 : Blo 578813 871265 := bstep (se 2 (by rfl) ⟨326724, by rfl⟩ : syracuseStep 871265 = 653449) B653449
theorem B871283 : Blo 578813 871283 := bstep (se 1 (by rfl) ⟨653462, by rfl⟩ : syracuseStep 871283 = 1306925) B1306925
theorem B871313 : Blo 578813 871313 := bstep (se 2 (by rfl) ⟨326742, by rfl⟩ : syracuseStep 871313 = 653485) B653485
theorem B871331 : Blo 578813 871331 := bstep (se 1 (by rfl) ⟨653498, by rfl⟩ : syracuseStep 871331 = 1306997) B1306997
theorem B871361 : Blo 578813 871361 := bstep (se 2 (by rfl) ⟨326760, by rfl⟩ : syracuseStep 871361 = 653521) B653521
theorem B871379 : Blo 578813 871379 := bstep (se 1 (by rfl) ⟨653534, by rfl⟩ : syracuseStep 871379 = 1307069) B1307069
theorem B1657837 : Blo 578813 1657837 := bstep (se 3 (by rfl) ⟨310844, by rfl⟩ : syracuseStep 1657837 = 621689) B621689
theorem B871409 : Blo 578813 871409 := bstep (se 2 (by rfl) ⟨326778, by rfl⟩ : syracuseStep 871409 = 653557) B653557
theorem B871427 : Blo 578813 871427 := bstep (se 1 (by rfl) ⟨653570, by rfl⟩ : syracuseStep 871427 = 1307141) B1307141
theorem B871457 : Blo 578813 871457 := bstep (se 2 (by rfl) ⟨326796, by rfl⟩ : syracuseStep 871457 = 653593) B653593
theorem B871475 : Blo 578813 871475 := bstep (se 1 (by rfl) ⟨653606, by rfl⟩ : syracuseStep 871475 = 1307213) B1307213
theorem B1100881 : Blo 578813 1100881 := bstep (se 2 (by rfl) ⟨412830, by rfl⟩ : syracuseStep 1100881 = 825661) B825661
theorem B871505 : Blo 578813 871505 := bstep (se 2 (by rfl) ⟨326814, by rfl⟩ : syracuseStep 871505 = 653629) B653629
theorem B871523 : Blo 578813 871523 := bstep (se 1 (by rfl) ⟨653642, by rfl⟩ : syracuseStep 871523 = 1307285) B1307285
theorem B871553 : Blo 578813 871553 := bstep (se 2 (by rfl) ⟨326832, by rfl⟩ : syracuseStep 871553 = 653665) B653665
theorem B871571 : Blo 578813 871571 := bstep (se 1 (by rfl) ⟨653678, by rfl⟩ : syracuseStep 871571 = 1307357) B1307357
theorem B871601 : Blo 578813 871601 := bstep (se 2 (by rfl) ⟨326850, by rfl⟩ : syracuseStep 871601 = 653701) B653701
theorem B871619 : Blo 578813 871619 := bstep (se 1 (by rfl) ⟨653714, by rfl⟩ : syracuseStep 871619 = 1307429) B1307429
theorem B1658065 : Blo 578813 1658065 := bstep (se 2 (by rfl) ⟨621774, by rfl⟩ : syracuseStep 1658065 = 1243549) B1243549
theorem B871649 : Blo 578813 871649 := bstep (se 2 (by rfl) ⟨326868, by rfl⟩ : syracuseStep 871649 = 653737) B653737
theorem B871667 : Blo 578813 871667 := bstep (se 1 (by rfl) ⟨653750, by rfl⟩ : syracuseStep 871667 = 1307501) B1307501
theorem B871697 : Blo 578813 871697 := bstep (se 2 (by rfl) ⟨326886, by rfl⟩ : syracuseStep 871697 = 653773) B653773
theorem B871715 : Blo 578813 871715 := bstep (se 1 (by rfl) ⟨653786, by rfl⟩ : syracuseStep 871715 = 1307573) B1307573
theorem B871745 : Blo 578813 871745 := bstep (se 2 (by rfl) ⟨326904, by rfl⟩ : syracuseStep 871745 = 653809) B653809
theorem B871763 : Blo 578813 871763 := bstep (se 1 (by rfl) ⟨653822, by rfl⟩ : syracuseStep 871763 = 1307645) B1307645
theorem B871793 : Blo 578813 871793 := bstep (se 2 (by rfl) ⟨326922, by rfl⟩ : syracuseStep 871793 = 653845) B653845
theorem B1658225 : Blo 578813 1658225 := bstep (se 2 (by rfl) ⟨621834, by rfl⟩ : syracuseStep 1658225 = 1243669) B1243669
theorem B871811 : Blo 578813 871811 := bstep (se 1 (by rfl) ⟨653858, by rfl⟩ : syracuseStep 871811 = 1307717) B1307717
theorem B871841 : Blo 578813 871841 := bstep (se 2 (by rfl) ⟨326940, by rfl⟩ : syracuseStep 871841 = 653881) B653881
theorem B871859 : Blo 578813 871859 := bstep (se 1 (by rfl) ⟨653894, by rfl⟩ : syracuseStep 871859 = 1307789) B1307789
theorem B871889 : Blo 578813 871889 := bstep (se 2 (by rfl) ⟨326958, by rfl⟩ : syracuseStep 871889 = 653917) B653917
theorem B871907 : Blo 578813 871907 := bstep (se 1 (by rfl) ⟨653930, by rfl⟩ : syracuseStep 871907 = 1307861) B1307861
theorem B1658339 : Blo 578813 1658339 := bstep (se 1 (by rfl) ⟨1243754, by rfl⟩ : syracuseStep 1658339 = 2487509) B2487509
theorem B871937 : Blo 578813 871937 := bstep (se 2 (by rfl) ⟨326976, by rfl⟩ : syracuseStep 871937 = 653953) B653953
theorem B871955 : Blo 578813 871955 := bstep (se 1 (by rfl) ⟨653966, by rfl⟩ : syracuseStep 871955 = 1307933) B1307933
theorem B1855021 : Blo 578813 1855021 := bstep (se 3 (by rfl) ⟨347816, by rfl⟩ : syracuseStep 1855021 = 695633) B695633
theorem B871985 : Blo 578813 871985 := bstep (se 2 (by rfl) ⟨326994, by rfl⟩ : syracuseStep 871985 = 653989) B653989
theorem B872003 : Blo 578813 872003 := bstep (se 1 (by rfl) ⟨654002, by rfl⟩ : syracuseStep 872003 = 1308005) B1308005
theorem B872033 : Blo 578813 872033 := bstep (se 2 (by rfl) ⟨327012, by rfl⟩ : syracuseStep 872033 = 654025) B654025
theorem B872051 : Blo 578813 872051 := bstep (se 1 (by rfl) ⟨654038, by rfl⟩ : syracuseStep 872051 = 1308077) B1308077
theorem B872081 : Blo 578813 872081 := bstep (se 2 (by rfl) ⟨327030, by rfl⟩ : syracuseStep 872081 = 654061) B654061
theorem B872099 : Blo 578813 872099 := bstep (se 1 (by rfl) ⟨654074, by rfl⟩ : syracuseStep 872099 = 1308149) B1308149
theorem B872129 : Blo 578813 872129 := bstep (se 2 (by rfl) ⟨327048, by rfl⟩ : syracuseStep 872129 = 654097) B654097
theorem B872147 : Blo 578813 872147 := bstep (se 1 (by rfl) ⟨654110, by rfl⟩ : syracuseStep 872147 = 1308221) B1308221
theorem B872177 : Blo 578813 872177 := bstep (se 2 (by rfl) ⟨327066, by rfl⟩ : syracuseStep 872177 = 654133) B654133
theorem B872195 : Blo 578813 872195 := bstep (se 1 (by rfl) ⟨654146, by rfl⟩ : syracuseStep 872195 = 1308293) B1308293
theorem B872225 : Blo 578813 872225 := bstep (se 2 (by rfl) ⟨327084, by rfl⟩ : syracuseStep 872225 = 654169) B654169
theorem B872243 : Blo 578813 872243 := bstep (se 1 (by rfl) ⟨654182, by rfl⟩ : syracuseStep 872243 = 1308365) B1308365
theorem B872273 : Blo 578813 872273 := bstep (se 2 (by rfl) ⟨327102, by rfl⟩ : syracuseStep 872273 = 654205) B654205
theorem B872291 : Blo 578813 872291 := bstep (se 1 (by rfl) ⟨654218, by rfl⟩ : syracuseStep 872291 = 1308437) B1308437
theorem B872321 : Blo 578813 872321 := bstep (se 2 (by rfl) ⟨327120, by rfl⟩ : syracuseStep 872321 = 654241) B654241
theorem B872339 : Blo 578813 872339 := bstep (se 1 (by rfl) ⟨654254, by rfl⟩ : syracuseStep 872339 = 1308509) B1308509
theorem B872369 : Blo 578813 872369 := bstep (se 2 (by rfl) ⟨327138, by rfl⟩ : syracuseStep 872369 = 654277) B654277
theorem B872387 : Blo 578813 872387 := bstep (se 1 (by rfl) ⟨654290, by rfl⟩ : syracuseStep 872387 = 1308581) B1308581
theorem B872417 : Blo 578813 872417 := bstep (se 2 (by rfl) ⟨327156, by rfl⟩ : syracuseStep 872417 = 654313) B654313
theorem B1953773 : Blo 578813 1953773 := bstep (se 3 (by rfl) ⟨366332, by rfl⟩ : syracuseStep 1953773 = 732665) B732665
theorem B872435 : Blo 578813 872435 := bstep (se 1 (by rfl) ⟨654326, by rfl⟩ : syracuseStep 872435 = 1308653) B1308653
theorem B872465 : Blo 578813 872465 := bstep (se 2 (by rfl) ⟨327174, by rfl⟩ : syracuseStep 872465 = 654349) B654349
theorem B1953827 : Blo 578813 1953827 := bstep (se 1 (by rfl) ⟨1465370, by rfl⟩ : syracuseStep 1953827 = 2930741) B2930741
theorem B872483 : Blo 578813 872483 := bstep (se 1 (by rfl) ⟨654362, by rfl⟩ : syracuseStep 872483 = 1308725) B1308725
theorem B872513 : Blo 578813 872513 := bstep (se 2 (by rfl) ⟨327192, by rfl⟩ : syracuseStep 872513 = 654385) B654385
theorem B872531 : Blo 578813 872531 := bstep (se 1 (by rfl) ⟨654398, by rfl⟩ : syracuseStep 872531 = 1308797) B1308797
theorem B1101937 : Blo 578813 1101937 := bstep (se 2 (by rfl) ⟨413226, by rfl⟩ : syracuseStep 1101937 = 826453) B826453
theorem B872561 : Blo 578813 872561 := bstep (se 2 (by rfl) ⟨327210, by rfl⟩ : syracuseStep 872561 = 654421) B654421
theorem B872579 : Blo 578813 872579 := bstep (se 1 (by rfl) ⟨654434, by rfl⟩ : syracuseStep 872579 = 1308869) B1308869
theorem B872609 : Blo 578813 872609 := bstep (se 2 (by rfl) ⟨327228, by rfl⟩ : syracuseStep 872609 = 654457) B654457
theorem B872627 : Blo 578813 872627 := bstep (se 1 (by rfl) ⟨654470, by rfl⟩ : syracuseStep 872627 = 1308941) B1308941
theorem B3133637 : Blo 578813 3133637 := bstep (se 4 (by rfl) ⟨293778, by rfl⟩ : syracuseStep 3133637 = 587557) B587557
theorem B872657 : Blo 578813 872657 := bstep (se 2 (by rfl) ⟨327246, by rfl⟩ : syracuseStep 872657 = 654493) B654493
theorem B2937059 : Blo 578813 2937059 := bstep (se 1 (by rfl) ⟨2202794, by rfl⟩ : syracuseStep 2937059 = 4405589) B4405589
theorem B125751523 : Blo 578813 125751523 := bstep (se 1 (by rfl) ⟨94313642, by rfl⟩ : syracuseStep 125751523 = 188627285) B188627285
theorem B872675 : Blo 578813 872675 := bstep (se 1 (by rfl) ⟨654506, by rfl⟩ : syracuseStep 872675 = 1309013) B1309013
theorem B3526897 : Blo 578813 3526897 := bstep (se 2 (by rfl) ⟨1322586, by rfl⟩ : syracuseStep 3526897 = 2645173) B2645173
theorem B872705 : Blo 578813 872705 := bstep (se 2 (by rfl) ⟨327264, by rfl⟩ : syracuseStep 872705 = 654529) B654529
theorem B872723 : Blo 578813 872723 := bstep (se 1 (by rfl) ⟨654542, by rfl⟩ : syracuseStep 872723 = 1309085) B1309085
theorem B1954097 : Blo 578813 1954097 := bstep (se 2 (by rfl) ⟨732786, by rfl⟩ : syracuseStep 1954097 = 1465573) B1465573
theorem B872753 : Blo 578813 872753 := bstep (se 2 (by rfl) ⟨327282, by rfl⟩ : syracuseStep 872753 = 654565) B654565
theorem B872771 : Blo 578813 872771 := bstep (se 1 (by rfl) ⟨654578, by rfl⟩ : syracuseStep 872771 = 1309157) B1309157
theorem B872801 : Blo 578813 872801 := bstep (se 2 (by rfl) ⟨327300, by rfl⟩ : syracuseStep 872801 = 654601) B654601
theorem B872819 : Blo 578813 872819 := bstep (se 1 (by rfl) ⟨654614, by rfl⟩ : syracuseStep 872819 = 1309229) B1309229
theorem B872849 : Blo 578813 872849 := bstep (se 2 (by rfl) ⟨327318, by rfl⟩ : syracuseStep 872849 = 654637) B654637
theorem B872867 : Blo 578813 872867 := bstep (se 1 (by rfl) ⟨654650, by rfl⟩ : syracuseStep 872867 = 1309301) B1309301
theorem B872897 : Blo 578813 872897 := bstep (se 2 (by rfl) ⟨327336, by rfl⟩ : syracuseStep 872897 = 654673) B654673
theorem B1659341 : Blo 578813 1659341 := bstep (se 3 (by rfl) ⟨311126, by rfl⟩ : syracuseStep 1659341 = 622253) B622253
theorem B872915 : Blo 578813 872915 := bstep (se 1 (by rfl) ⟨654686, by rfl⟩ : syracuseStep 872915 = 1309373) B1309373
theorem B872945 : Blo 578813 872945 := bstep (se 2 (by rfl) ⟨327354, by rfl⟩ : syracuseStep 872945 = 654709) B654709
theorem B1102339 : Blo 578813 1102339 := bstep (se 1 (by rfl) ⟨826754, by rfl⟩ : syracuseStep 1102339 = 1653509) B1653509
theorem B872963 : Blo 578813 872963 := bstep (se 1 (by rfl) ⟨654722, by rfl⟩ : syracuseStep 872963 = 1309445) B1309445
theorem B872993 : Blo 578813 872993 := bstep (se 2 (by rfl) ⟨327372, by rfl⟩ : syracuseStep 872993 = 654745) B654745
theorem B1102385 : Blo 578813 1102385 := bstep (se 2 (by rfl) ⟨413394, by rfl⟩ : syracuseStep 1102385 = 826789) B826789
theorem B873011 : Blo 578813 873011 := bstep (se 1 (by rfl) ⟨654758, by rfl⟩ : syracuseStep 873011 = 1309517) B1309517
theorem B873041 : Blo 578813 873041 := bstep (se 2 (by rfl) ⟨327390, by rfl⟩ : syracuseStep 873041 = 654781) B654781
theorem B2478691 : Blo 578813 2478691 := bstep (se 1 (by rfl) ⟨1859018, by rfl⟩ : syracuseStep 2478691 = 3718037) B3718037
theorem B873059 : Blo 578813 873059 := bstep (se 1 (by rfl) ⟨654794, by rfl⟩ : syracuseStep 873059 = 1309589) B1309589
theorem B3297905 : Blo 578813 3297905 := bstep (se 2 (by rfl) ⟨1236714, by rfl⟩ : syracuseStep 3297905 = 2473429) B2473429
theorem B873089 : Blo 578813 873089 := bstep (se 2 (by rfl) ⟨327408, by rfl⟩ : syracuseStep 873089 = 654817) B654817
theorem B1659523 : Blo 578813 1659523 := bstep (se 1 (by rfl) ⟨1244642, by rfl⟩ : syracuseStep 1659523 = 2489285) B2489285
theorem B873107 : Blo 578813 873107 := bstep (se 1 (by rfl) ⟨654830, by rfl⟩ : syracuseStep 873107 = 1309661) B1309661
theorem B873137 : Blo 578813 873137 := bstep (se 2 (by rfl) ⟨327426, by rfl⟩ : syracuseStep 873137 = 654853) B654853
theorem B873155 : Blo 578813 873155 := bstep (se 1 (by rfl) ⟨654866, by rfl⟩ : syracuseStep 873155 = 1309733) B1309733
theorem B873185 : Blo 578813 873185 := bstep (se 2 (by rfl) ⟨327444, by rfl⟩ : syracuseStep 873185 = 654889) B654889
theorem B1594093 : Blo 578813 1594093 := bstep (se 3 (by rfl) ⟨298892, by rfl⟩ : syracuseStep 1594093 = 597785) B597785
theorem B873203 : Blo 578813 873203 := bstep (se 1 (by rfl) ⟨654902, by rfl⟩ : syracuseStep 873203 = 1309805) B1309805
theorem B873233 : Blo 578813 873233 := bstep (se 2 (by rfl) ⟨327462, by rfl⟩ : syracuseStep 873233 = 654925) B654925
theorem B873251 : Blo 578813 873251 := bstep (se 1 (by rfl) ⟨654938, by rfl⟩ : syracuseStep 873251 = 1309877) B1309877
theorem B873281 : Blo 578813 873281 := bstep (se 2 (by rfl) ⟨327480, by rfl⟩ : syracuseStep 873281 = 654961) B654961
theorem B1954637 : Blo 578813 1954637 := bstep (se 3 (by rfl) ⟨366494, by rfl⟩ : syracuseStep 1954637 = 732989) B732989
theorem B1102673 : Blo 578813 1102673 := bstep (se 2 (by rfl) ⟨413502, by rfl⟩ : syracuseStep 1102673 = 827005) B827005
theorem B873299 : Blo 578813 873299 := bstep (se 1 (by rfl) ⟨654974, by rfl⟩ : syracuseStep 873299 = 1309949) B1309949
theorem B873329 : Blo 578813 873329 := bstep (se 2 (by rfl) ⟨327498, by rfl⟩ : syracuseStep 873329 = 654997) B654997
theorem B1954691 : Blo 578813 1954691 := bstep (se 1 (by rfl) ⟨1466018, by rfl⟩ : syracuseStep 1954691 = 2932037) B2932037
theorem B873347 : Blo 578813 873347 := bstep (se 1 (by rfl) ⟨655010, by rfl⟩ : syracuseStep 873347 = 1310021) B1310021
theorem B873377 : Blo 578813 873377 := bstep (se 2 (by rfl) ⟨327516, by rfl⟩ : syracuseStep 873377 = 655033) B655033
theorem B873395 : Blo 578813 873395 := bstep (se 1 (by rfl) ⟨655046, by rfl⟩ : syracuseStep 873395 = 1310093) B1310093
theorem B873425 : Blo 578813 873425 := bstep (se 2 (by rfl) ⟨327534, by rfl⟩ : syracuseStep 873425 = 655069) B655069
theorem B1856483 : Blo 578813 1856483 := bstep (se 1 (by rfl) ⟨1392362, by rfl⟩ : syracuseStep 1856483 = 2784725) B2784725
theorem B873443 : Blo 578813 873443 := bstep (se 1 (by rfl) ⟨655082, by rfl⟩ : syracuseStep 873443 = 1310165) B1310165
theorem B1889261 : Blo 578813 1889261 := bstep (se 3 (by rfl) ⟨354236, by rfl⟩ : syracuseStep 1889261 = 708473) B708473
theorem B873473 : Blo 578813 873473 := bstep (se 2 (by rfl) ⟨327552, by rfl⟩ : syracuseStep 873473 = 655105) B655105
theorem B2937869 : Blo 578813 2937869 := bstep (se 3 (by rfl) ⟨550850, by rfl⟩ : syracuseStep 2937869 = 1101701) B1101701
theorem B873491 : Blo 578813 873491 := bstep (se 1 (by rfl) ⟨655118, by rfl⟩ : syracuseStep 873491 = 1310237) B1310237
theorem B873521 : Blo 578813 873521 := bstep (se 2 (by rfl) ⟨327570, by rfl⟩ : syracuseStep 873521 = 655141) B655141
theorem B873539 : Blo 578813 873539 := bstep (se 1 (by rfl) ⟨655154, by rfl⟩ : syracuseStep 873539 = 1310309) B1310309
theorem B873569 : Blo 578813 873569 := bstep (se 2 (by rfl) ⟨327588, by rfl⟩ : syracuseStep 873569 = 655177) B655177
theorem B4183139 : Blo 578813 4183139 := bstep (se 1 (by rfl) ⟨3137354, by rfl⟩ : syracuseStep 4183139 = 6274709) B6274709
theorem B873587 : Blo 578813 873587 := bstep (se 1 (by rfl) ⟨655190, by rfl⟩ : syracuseStep 873587 = 1310381) B1310381
theorem B1954961 : Blo 578813 1954961 := bstep (se 2 (by rfl) ⟨733110, by rfl⟩ : syracuseStep 1954961 = 1466221) B1466221
theorem B873617 : Blo 578813 873617 := bstep (se 2 (by rfl) ⟨327606, by rfl⟩ : syracuseStep 873617 = 655213) B655213
theorem B873635 : Blo 578813 873635 := bstep (se 1 (by rfl) ⟨655226, by rfl⟩ : syracuseStep 873635 = 1310453) B1310453
theorem B873665 : Blo 578813 873665 := bstep (se 2 (by rfl) ⟨327624, by rfl⟩ : syracuseStep 873665 = 655249) B655249
theorem B873683 : Blo 578813 873683 := bstep (se 1 (by rfl) ⟨655262, by rfl⟩ : syracuseStep 873683 = 1310525) B1310525
theorem B1856753 : Blo 578813 1856753 := bstep (se 2 (by rfl) ⟨696282, by rfl⟩ : syracuseStep 1856753 = 1392565) B1392565
theorem B873713 : Blo 578813 873713 := bstep (se 2 (by rfl) ⟨327642, by rfl⟩ : syracuseStep 873713 = 655285) B655285
theorem B578819 : Blo 578813 578819 := bstep (se 1 (by rfl) ⟨434114, by rfl⟩ : syracuseStep 578819 = 868229) B868229
theorem B873731 : Blo 578813 873731 := bstep (se 1 (by rfl) ⟨655298, by rfl⟩ : syracuseStep 873731 = 1310597) B1310597
theorem B578835 : Blo 578813 578835 := bstep (se 1 (by rfl) ⟨434126, by rfl⟩ : syracuseStep 578835 = 868253) B868253
theorem B873761 : Blo 578813 873761 := bstep (se 2 (by rfl) ⟨327660, by rfl⟩ : syracuseStep 873761 = 655321) B655321
theorem B578851 : Blo 578813 578851 := bstep (se 1 (by rfl) ⟨434138, by rfl⟩ : syracuseStep 578851 = 868277) B868277
theorem B2086193 : Blo 578813 2086193 := bstep (se 2 (by rfl) ⟨782322, by rfl⟩ : syracuseStep 2086193 = 1564645) B1564645
theorem B578867 : Blo 578813 578867 := bstep (se 1 (by rfl) ⟨434150, by rfl⟩ : syracuseStep 578867 = 868301) B868301
theorem B873779 : Blo 578813 873779 := bstep (se 1 (by rfl) ⟨655334, by rfl⟩ : syracuseStep 873779 = 1310669) B1310669
theorem B578883 : Blo 578813 578883 := bstep (se 1 (by rfl) ⟨434162, by rfl⟩ : syracuseStep 578883 = 868325) B868325
theorem B578899 : Blo 578813 578899 := bstep (se 1 (by rfl) ⟨434174, by rfl⟩ : syracuseStep 578899 = 868349) B868349
theorem B873809 : Blo 578813 873809 := bstep (se 2 (by rfl) ⟨327678, by rfl⟩ : syracuseStep 873809 = 655357) B655357
theorem B578915 : Blo 578813 578915 := bstep (se 1 (by rfl) ⟨434186, by rfl⟩ : syracuseStep 578915 = 868373) B868373
theorem B873827 : Blo 578813 873827 := bstep (se 1 (by rfl) ⟨655370, by rfl⟩ : syracuseStep 873827 = 1310741) B1310741
theorem B578931 : Blo 578813 578931 := bstep (se 1 (by rfl) ⟨434198, by rfl⟩ : syracuseStep 578931 = 868397) B868397
theorem B578947 : Blo 578813 578947 := bstep (se 1 (by rfl) ⟨434210, by rfl⟩ : syracuseStep 578947 = 868421) B868421
theorem B873857 : Blo 578813 873857 := bstep (se 2 (by rfl) ⟨327696, by rfl⟩ : syracuseStep 873857 = 655393) B655393
theorem B578963 : Blo 578813 578963 := bstep (se 1 (by rfl) ⟨434222, by rfl⟩ : syracuseStep 578963 = 868445) B868445
theorem B873875 : Blo 578813 873875 := bstep (se 1 (by rfl) ⟨655406, by rfl⟩ : syracuseStep 873875 = 1310813) B1310813
theorem B578979 : Blo 578813 578979 := bstep (se 1 (by rfl) ⟨434234, by rfl⟩ : syracuseStep 578979 = 868469) B868469
theorem B873905 : Blo 578813 873905 := bstep (se 2 (by rfl) ⟨327714, by rfl⟩ : syracuseStep 873905 = 655429) B655429
theorem B578995 : Blo 578813 578995 := bstep (se 1 (by rfl) ⟨434246, by rfl⟩ : syracuseStep 578995 = 868493) B868493
theorem B579011 : Blo 578813 579011 := bstep (se 1 (by rfl) ⟨434258, by rfl⟩ : syracuseStep 579011 = 868517) B868517
theorem B873923 : Blo 578813 873923 := bstep (se 1 (by rfl) ⟨655442, by rfl⟩ : syracuseStep 873923 = 1310885) B1310885
theorem B579027 : Blo 578813 579027 := bstep (se 1 (by rfl) ⟨434270, by rfl⟩ : syracuseStep 579027 = 868541) B868541
theorem B873953 : Blo 578813 873953 := bstep (se 2 (by rfl) ⟨327732, by rfl⟩ : syracuseStep 873953 = 655465) B655465
theorem B579043 : Blo 578813 579043 := bstep (se 1 (by rfl) ⟨434282, by rfl⟩ : syracuseStep 579043 = 868565) B868565
theorem B579059 : Blo 578813 579059 := bstep (se 1 (by rfl) ⟨434294, by rfl⟩ : syracuseStep 579059 = 868589) B868589
theorem B873971 : Blo 578813 873971 := bstep (se 1 (by rfl) ⟨655478, by rfl⟩ : syracuseStep 873971 = 1310957) B1310957
theorem B579075 : Blo 578813 579075 := bstep (se 1 (by rfl) ⟨434306, by rfl⟩ : syracuseStep 579075 = 868613) B868613
theorem B874001 : Blo 578813 874001 := bstep (se 2 (by rfl) ⟨327750, by rfl⟩ : syracuseStep 874001 = 655501) B655501
theorem B579091 : Blo 578813 579091 := bstep (se 1 (by rfl) ⟨434318, by rfl⟩ : syracuseStep 579091 = 868637) B868637
theorem B13391381 : Blo 578813 13391381 := bstep (se 6 (by rfl) ⟨313860, by rfl⟩ : syracuseStep 13391381 = 627721) B627721
theorem B579107 : Blo 578813 579107 := bstep (se 1 (by rfl) ⟨434330, by rfl⟩ : syracuseStep 579107 = 868661) B868661
theorem B1103395 : Blo 578813 1103395 := bstep (se 1 (by rfl) ⟨827546, by rfl⟩ : syracuseStep 1103395 = 1655093) B1655093
theorem B874019 : Blo 578813 874019 := bstep (se 1 (by rfl) ⟨655514, by rfl⟩ : syracuseStep 874019 = 1311029) B1311029
theorem B579123 : Blo 578813 579123 := bstep (se 1 (by rfl) ⟨434342, by rfl⟩ : syracuseStep 579123 = 868685) B868685
theorem B874049 : Blo 578813 874049 := bstep (se 2 (by rfl) ⟨327768, by rfl⟩ : syracuseStep 874049 = 655537) B655537
theorem B579139 : Blo 578813 579139 := bstep (se 1 (by rfl) ⟨434354, by rfl⟩ : syracuseStep 579139 = 868709) B868709
theorem B579155 : Blo 578813 579155 := bstep (se 1 (by rfl) ⟨434366, by rfl⟩ : syracuseStep 579155 = 868733) B868733
theorem B874067 : Blo 578813 874067 := bstep (se 1 (by rfl) ⟨655550, by rfl⟩ : syracuseStep 874067 = 1311101) B1311101
theorem B579171 : Blo 578813 579171 := bstep (se 1 (by rfl) ⟨434378, by rfl⟩ : syracuseStep 579171 = 868757) B868757
theorem B874097 : Blo 578813 874097 := bstep (se 2 (by rfl) ⟨327786, by rfl⟩ : syracuseStep 874097 = 655573) B655573
theorem B579187 : Blo 578813 579187 := bstep (se 1 (by rfl) ⟨434390, by rfl⟩ : syracuseStep 579187 = 868781) B868781
theorem B579203 : Blo 578813 579203 := bstep (se 1 (by rfl) ⟨434402, by rfl⟩ : syracuseStep 579203 = 868805) B868805
theorem B874115 : Blo 578813 874115 := bstep (se 1 (by rfl) ⟨655586, by rfl⟩ : syracuseStep 874115 = 1311173) B1311173
theorem B579219 : Blo 578813 579219 := bstep (se 1 (by rfl) ⟨434414, by rfl⟩ : syracuseStep 579219 = 868829) B868829
theorem B874145 : Blo 578813 874145 := bstep (se 2 (by rfl) ⟨327804, by rfl⟩ : syracuseStep 874145 = 655609) B655609
theorem B579235 : Blo 578813 579235 := bstep (se 1 (by rfl) ⟨434426, by rfl⟩ : syracuseStep 579235 = 868853) B868853
theorem B1955501 : Blo 578813 1955501 := bstep (se 3 (by rfl) ⟨366656, by rfl⟩ : syracuseStep 1955501 = 733313) B733313
theorem B579251 : Blo 578813 579251 := bstep (se 1 (by rfl) ⟨434438, by rfl⟩ : syracuseStep 579251 = 868877) B868877
theorem B874163 : Blo 578813 874163 := bstep (se 1 (by rfl) ⟨655622, by rfl⟩ : syracuseStep 874163 = 1311245) B1311245
theorem B579267 : Blo 578813 579267 := bstep (se 1 (by rfl) ⟨434450, by rfl⟩ : syracuseStep 579267 = 868901) B868901
theorem B874193 : Blo 578813 874193 := bstep (se 2 (by rfl) ⟨327822, by rfl⟩ : syracuseStep 874193 = 655645) B655645
theorem B579283 : Blo 578813 579283 := bstep (se 1 (by rfl) ⟨434462, by rfl⟩ : syracuseStep 579283 = 868925) B868925
theorem B579299 : Blo 578813 579299 := bstep (se 1 (by rfl) ⟨434474, by rfl⟩ : syracuseStep 579299 = 868949) B868949
theorem B1955555 : Blo 578813 1955555 := bstep (se 1 (by rfl) ⟨1466666, by rfl⟩ : syracuseStep 1955555 = 2933333) B2933333
theorem B874211 : Blo 578813 874211 := bstep (se 1 (by rfl) ⟨655658, by rfl⟩ : syracuseStep 874211 = 1311317) B1311317
theorem B579315 : Blo 578813 579315 := bstep (se 1 (by rfl) ⟨434486, by rfl⟩ : syracuseStep 579315 = 868973) B868973
theorem B579331 : Blo 578813 579331 := bstep (se 1 (by rfl) ⟨434498, by rfl⟩ : syracuseStep 579331 = 868997) B868997
theorem B579347 : Blo 578813 579347 := bstep (se 1 (by rfl) ⟨434510, by rfl⟩ : syracuseStep 579347 = 869021) B869021
theorem B579363 : Blo 578813 579363 := bstep (se 1 (by rfl) ⟨434522, by rfl⟩ : syracuseStep 579363 = 869045) B869045
theorem B808753 : Blo 578813 808753 := bstep (se 2 (by rfl) ⟨303282, by rfl⟩ : syracuseStep 808753 = 606565) B606565
theorem B579379 : Blo 578813 579379 := bstep (se 1 (by rfl) ⟨434534, by rfl⟩ : syracuseStep 579379 = 869069) B869069
theorem B579395 : Blo 578813 579395 := bstep (se 1 (by rfl) ⟨434546, by rfl⟩ : syracuseStep 579395 = 869093) B869093
theorem B579411 : Blo 578813 579411 := bstep (se 1 (by rfl) ⟨434558, by rfl⟩ : syracuseStep 579411 = 869117) B869117
theorem B579427 : Blo 578813 579427 := bstep (se 1 (by rfl) ⟨434570, by rfl⟩ : syracuseStep 579427 = 869141) B869141
theorem B579443 : Blo 578813 579443 := bstep (se 1 (by rfl) ⟨434582, by rfl⟩ : syracuseStep 579443 = 869165) B869165
theorem B579459 : Blo 578813 579459 := bstep (se 1 (by rfl) ⟨434594, by rfl⟩ : syracuseStep 579459 = 869189) B869189
theorem B579475 : Blo 578813 579475 := bstep (se 1 (by rfl) ⟨434606, by rfl⟩ : syracuseStep 579475 = 869213) B869213
theorem B579491 : Blo 578813 579491 := bstep (se 1 (by rfl) ⟨434618, by rfl⟩ : syracuseStep 579491 = 869237) B869237
theorem B579507 : Blo 578813 579507 := bstep (se 1 (by rfl) ⟨434630, by rfl⟩ : syracuseStep 579507 = 869261) B869261
theorem B579523 : Blo 578813 579523 := bstep (se 1 (by rfl) ⟨434642, by rfl⟩ : syracuseStep 579523 = 869285) B869285
theorem B579539 : Blo 578813 579539 := bstep (se 1 (by rfl) ⟨434654, by rfl⟩ : syracuseStep 579539 = 869309) B869309
theorem B579555 : Blo 578813 579555 := bstep (se 1 (by rfl) ⟨434666, by rfl⟩ : syracuseStep 579555 = 869333) B869333
theorem B1103843 : Blo 578813 1103843 := bstep (se 1 (by rfl) ⟨827882, by rfl⟩ : syracuseStep 1103843 = 1655765) B1655765
theorem B1955825 : Blo 578813 1955825 := bstep (se 2 (by rfl) ⟨733434, by rfl⟩ : syracuseStep 1955825 = 1466869) B1466869
theorem B579571 : Blo 578813 579571 := bstep (se 1 (by rfl) ⟨434678, by rfl⟩ : syracuseStep 579571 = 869357) B869357
theorem B579587 : Blo 578813 579587 := bstep (se 1 (by rfl) ⟨434690, by rfl⟩ : syracuseStep 579587 = 869381) B869381
theorem B579603 : Blo 578813 579603 := bstep (se 1 (by rfl) ⟨434702, by rfl⟩ : syracuseStep 579603 = 869405) B869405
theorem B3299363 : Blo 578813 3299363 := bstep (se 1 (by rfl) ⟨2474522, by rfl⟩ : syracuseStep 3299363 = 4949045) B4949045
theorem B579619 : Blo 578813 579619 := bstep (se 1 (by rfl) ⟨434714, by rfl⟩ : syracuseStep 579619 = 869429) B869429
theorem B579635 : Blo 578813 579635 := bstep (se 1 (by rfl) ⟨434726, by rfl⟩ : syracuseStep 579635 = 869453) B869453
theorem B579651 : Blo 578813 579651 := bstep (se 1 (by rfl) ⟨434738, by rfl⟩ : syracuseStep 579651 = 869477) B869477
theorem B579667 : Blo 578813 579667 := bstep (se 1 (by rfl) ⟨434750, by rfl⟩ : syracuseStep 579667 = 869501) B869501
theorem B579683 : Blo 578813 579683 := bstep (se 1 (by rfl) ⟨434762, by rfl⟩ : syracuseStep 579683 = 869525) B869525
theorem B579699 : Blo 578813 579699 := bstep (se 1 (by rfl) ⟨434774, by rfl⟩ : syracuseStep 579699 = 869549) B869549
theorem B579715 : Blo 578813 579715 := bstep (se 1 (by rfl) ⟨434786, by rfl⟩ : syracuseStep 579715 = 869573) B869573
theorem B3528845 : Blo 578813 3528845 := bstep (se 3 (by rfl) ⟨661658, by rfl⟩ : syracuseStep 3528845 = 1323317) B1323317
theorem B579731 : Blo 578813 579731 := bstep (se 1 (by rfl) ⟨434798, by rfl⟩ : syracuseStep 579731 = 869597) B869597
theorem B579747 : Blo 578813 579747 := bstep (se 1 (by rfl) ⟨434810, by rfl⟩ : syracuseStep 579747 = 869621) B869621
theorem B579763 : Blo 578813 579763 := bstep (se 1 (by rfl) ⟨434822, by rfl⟩ : syracuseStep 579763 = 869645) B869645
theorem B579779 : Blo 578813 579779 := bstep (se 1 (by rfl) ⟨434834, by rfl⟩ : syracuseStep 579779 = 869669) B869669
theorem B2087117 : Blo 578813 2087117 := bstep (se 3 (by rfl) ⟨391334, by rfl⟩ : syracuseStep 2087117 = 782669) B782669
theorem B579795 : Blo 578813 579795 := bstep (se 1 (by rfl) ⟨434846, by rfl⟩ : syracuseStep 579795 = 869693) B869693
theorem B579811 : Blo 578813 579811 := bstep (se 1 (by rfl) ⟨434858, by rfl⟩ : syracuseStep 579811 = 869717) B869717
theorem B579827 : Blo 578813 579827 := bstep (se 1 (by rfl) ⟨434870, by rfl⟩ : syracuseStep 579827 = 869741) B869741
theorem B579843 : Blo 578813 579843 := bstep (se 1 (by rfl) ⟨434882, by rfl⟩ : syracuseStep 579843 = 869765) B869765
theorem B1104131 : Blo 578813 1104131 := bstep (se 1 (by rfl) ⟨828098, by rfl⟩ : syracuseStep 1104131 = 1656197) B1656197
theorem B579859 : Blo 578813 579859 := bstep (se 1 (by rfl) ⟨434894, by rfl⟩ : syracuseStep 579859 = 869789) B869789
theorem B579875 : Blo 578813 579875 := bstep (se 1 (by rfl) ⟨434906, by rfl⟩ : syracuseStep 579875 = 869813) B869813
theorem B579891 : Blo 578813 579891 := bstep (se 1 (by rfl) ⟨434918, by rfl⟩ : syracuseStep 579891 = 869837) B869837
theorem B579907 : Blo 578813 579907 := bstep (se 1 (by rfl) ⟨434930, by rfl⟩ : syracuseStep 579907 = 869861) B869861
theorem B579923 : Blo 578813 579923 := bstep (se 1 (by rfl) ⟨434942, by rfl⟩ : syracuseStep 579923 = 869885) B869885
theorem B579939 : Blo 578813 579939 := bstep (se 1 (by rfl) ⟨434954, by rfl⟩ : syracuseStep 579939 = 869909) B869909
theorem B9525617 : Blo 578813 9525617 := bstep (se 2 (by rfl) ⟨3572106, by rfl⟩ : syracuseStep 9525617 = 7144213) B7144213
theorem B579955 : Blo 578813 579955 := bstep (se 1 (by rfl) ⟨434966, by rfl⟩ : syracuseStep 579955 = 869933) B869933
theorem B579971 : Blo 578813 579971 := bstep (se 1 (by rfl) ⟨434978, by rfl⟩ : syracuseStep 579971 = 869957) B869957
theorem B579987 : Blo 578813 579987 := bstep (se 1 (by rfl) ⟨434990, by rfl⟩ : syracuseStep 579987 = 869981) B869981
theorem B580003 : Blo 578813 580003 := bstep (se 1 (by rfl) ⟨435002, by rfl⟩ : syracuseStep 580003 = 870005) B870005
theorem B580019 : Blo 578813 580019 := bstep (se 1 (by rfl) ⟨435014, by rfl⟩ : syracuseStep 580019 = 870029) B870029
theorem B580035 : Blo 578813 580035 := bstep (se 1 (by rfl) ⟨435026, by rfl⟩ : syracuseStep 580035 = 870053) B870053
theorem B580051 : Blo 578813 580051 := bstep (se 1 (by rfl) ⟨435038, by rfl⟩ : syracuseStep 580051 = 870077) B870077
theorem B580067 : Blo 578813 580067 := bstep (se 1 (by rfl) ⟨435050, by rfl⟩ : syracuseStep 580067 = 870101) B870101
theorem B3135971 : Blo 578813 3135971 := bstep (se 1 (by rfl) ⟨2351978, by rfl⟩ : syracuseStep 3135971 = 4703957) B4703957
theorem B580083 : Blo 578813 580083 := bstep (se 1 (by rfl) ⟨435062, by rfl⟩ : syracuseStep 580083 = 870125) B870125
theorem B580099 : Blo 578813 580099 := bstep (se 1 (by rfl) ⟨435074, by rfl⟩ : syracuseStep 580099 = 870149) B870149
theorem B1956365 : Blo 578813 1956365 := bstep (se 3 (by rfl) ⟨366818, by rfl⟩ : syracuseStep 1956365 = 733637) B733637
theorem B1989137 : Blo 578813 1989137 := bstep (se 2 (by rfl) ⟨745926, by rfl⟩ : syracuseStep 1989137 = 1491853) B1491853
theorem B580115 : Blo 578813 580115 := bstep (se 1 (by rfl) ⟨435086, by rfl⟩ : syracuseStep 580115 = 870173) B870173
theorem B580131 : Blo 578813 580131 := bstep (se 1 (by rfl) ⟨435098, by rfl⟩ : syracuseStep 580131 = 870197) B870197
theorem B1399331 : Blo 578813 1399331 := bstep (se 1 (by rfl) ⟨1049498, by rfl⟩ : syracuseStep 1399331 = 2098997) B2098997
theorem B580147 : Blo 578813 580147 := bstep (se 1 (by rfl) ⟨435110, by rfl⟩ : syracuseStep 580147 = 870221) B870221
theorem B1956419 : Blo 578813 1956419 := bstep (se 1 (by rfl) ⟨1467314, by rfl⟩ : syracuseStep 1956419 = 2934629) B2934629
theorem B580163 : Blo 578813 580163 := bstep (se 1 (by rfl) ⟨435122, by rfl⟩ : syracuseStep 580163 = 870245) B870245
theorem B580179 : Blo 578813 580179 := bstep (se 1 (by rfl) ⟨435134, by rfl⟩ : syracuseStep 580179 = 870269) B870269
theorem B580195 : Blo 578813 580195 := bstep (se 1 (by rfl) ⟨435146, by rfl⟩ : syracuseStep 580195 = 870293) B870293
theorem B19094129 : Blo 578813 19094129 := bstep (se 2 (by rfl) ⟨7160298, by rfl⟩ : syracuseStep 19094129 = 14320597) B14320597
theorem B580211 : Blo 578813 580211 := bstep (se 1 (by rfl) ⟨435158, by rfl⟩ : syracuseStep 580211 = 870317) B870317
theorem B580227 : Blo 578813 580227 := bstep (se 1 (by rfl) ⟨435170, by rfl⟩ : syracuseStep 580227 = 870341) B870341
theorem B580243 : Blo 578813 580243 := bstep (se 1 (by rfl) ⟨435182, by rfl⟩ : syracuseStep 580243 = 870365) B870365
theorem B580259 : Blo 578813 580259 := bstep (se 1 (by rfl) ⟨435194, by rfl⟩ : syracuseStep 580259 = 870389) B870389
theorem B580275 : Blo 578813 580275 := bstep (se 1 (by rfl) ⟨435206, by rfl⟩ : syracuseStep 580275 = 870413) B870413
theorem B580291 : Blo 578813 580291 := bstep (se 1 (by rfl) ⟨435218, by rfl⟩ : syracuseStep 580291 = 870437) B870437
theorem B580307 : Blo 578813 580307 := bstep (se 1 (by rfl) ⟨435230, by rfl⟩ : syracuseStep 580307 = 870461) B870461
theorem B580323 : Blo 578813 580323 := bstep (se 1 (by rfl) ⟨435242, by rfl⟩ : syracuseStep 580323 = 870485) B870485
theorem B580339 : Blo 578813 580339 := bstep (se 1 (by rfl) ⟨435254, by rfl⟩ : syracuseStep 580339 = 870509) B870509
theorem B580355 : Blo 578813 580355 := bstep (se 1 (by rfl) ⟨435266, by rfl⟩ : syracuseStep 580355 = 870533) B870533
theorem B940817 : Blo 578813 940817 := bstep (se 2 (by rfl) ⟨352806, by rfl⟩ : syracuseStep 940817 = 705613) B705613
theorem B580371 : Blo 578813 580371 := bstep (se 1 (by rfl) ⟨435278, by rfl⟩ : syracuseStep 580371 = 870557) B870557
theorem B580387 : Blo 578813 580387 := bstep (se 1 (by rfl) ⟨435290, by rfl⟩ : syracuseStep 580387 = 870581) B870581
theorem B580403 : Blo 578813 580403 := bstep (se 1 (by rfl) ⟨435302, by rfl⟩ : syracuseStep 580403 = 870605) B870605
theorem B580419 : Blo 578813 580419 := bstep (se 1 (by rfl) ⟨435314, by rfl⟩ : syracuseStep 580419 = 870629) B870629
theorem B1956689 : Blo 578813 1956689 := bstep (se 2 (by rfl) ⟨733758, by rfl⟩ : syracuseStep 1956689 = 1467517) B1467517
theorem B580435 : Blo 578813 580435 := bstep (se 1 (by rfl) ⟨435326, by rfl⟩ : syracuseStep 580435 = 870653) B870653
theorem B580451 : Blo 578813 580451 := bstep (se 1 (by rfl) ⟨435338, by rfl⟩ : syracuseStep 580451 = 870677) B870677
theorem B580467 : Blo 578813 580467 := bstep (se 1 (by rfl) ⟨435350, by rfl⟩ : syracuseStep 580467 = 870701) B870701
theorem B580483 : Blo 578813 580483 := bstep (se 1 (by rfl) ⟨435362, by rfl⟩ : syracuseStep 580483 = 870725) B870725
theorem B580499 : Blo 578813 580499 := bstep (se 1 (by rfl) ⟨435374, by rfl⟩ : syracuseStep 580499 = 870749) B870749
theorem B580515 : Blo 578813 580515 := bstep (se 1 (by rfl) ⟨435386, by rfl⟩ : syracuseStep 580515 = 870773) B870773
theorem B580531 : Blo 578813 580531 := bstep (se 1 (by rfl) ⟨435398, by rfl⟩ : syracuseStep 580531 = 870797) B870797
theorem B580547 : Blo 578813 580547 := bstep (se 1 (by rfl) ⟨435410, by rfl⟩ : syracuseStep 580547 = 870821) B870821
theorem B580563 : Blo 578813 580563 := bstep (se 1 (by rfl) ⟨435422, by rfl⟩ : syracuseStep 580563 = 870845) B870845
theorem B580579 : Blo 578813 580579 := bstep (se 1 (by rfl) ⟨435434, by rfl⟩ : syracuseStep 580579 = 870869) B870869
theorem B2481137 : Blo 578813 2481137 := bstep (se 2 (by rfl) ⟨930426, by rfl⟩ : syracuseStep 2481137 = 1860853) B1860853
theorem B580595 : Blo 578813 580595 := bstep (se 1 (by rfl) ⟨435446, by rfl⟩ : syracuseStep 580595 = 870893) B870893
theorem B580611 : Blo 578813 580611 := bstep (se 1 (by rfl) ⟨435458, by rfl⟩ : syracuseStep 580611 = 870917) B870917
theorem B3300365 : Blo 578813 3300365 := bstep (se 3 (by rfl) ⟨618818, by rfl⟩ : syracuseStep 3300365 = 1237637) B1237637
theorem B1465361 : Blo 578813 1465361 := bstep (se 2 (by rfl) ⟨549510, by rfl⟩ : syracuseStep 1465361 = 1099021) B1099021
theorem B580627 : Blo 578813 580627 := bstep (se 1 (by rfl) ⟨435470, by rfl⟩ : syracuseStep 580627 = 870941) B870941
theorem B580643 : Blo 578813 580643 := bstep (se 1 (by rfl) ⟨435482, by rfl⟩ : syracuseStep 580643 = 870965) B870965
theorem B580659 : Blo 578813 580659 := bstep (se 1 (by rfl) ⟨435494, by rfl⟩ : syracuseStep 580659 = 870989) B870989
theorem B1465411 : Blo 578813 1465411 := bstep (se 1 (by rfl) ⟨1099058, by rfl⟩ : syracuseStep 1465411 = 2198117) B2198117
theorem B580675 : Blo 578813 580675 := bstep (se 1 (by rfl) ⟨435506, by rfl⟩ : syracuseStep 580675 = 871013) B871013
theorem B580691 : Blo 578813 580691 := bstep (se 1 (by rfl) ⟨435518, by rfl⟩ : syracuseStep 580691 = 871037) B871037
theorem B580707 : Blo 578813 580707 := bstep (se 1 (by rfl) ⟨435530, by rfl⟩ : syracuseStep 580707 = 871061) B871061
theorem B580723 : Blo 578813 580723 := bstep (se 1 (by rfl) ⟨435542, by rfl⟩ : syracuseStep 580723 = 871085) B871085
theorem B580739 : Blo 578813 580739 := bstep (se 1 (by rfl) ⟨435554, by rfl⟩ : syracuseStep 580739 = 871109) B871109
theorem B580755 : Blo 578813 580755 := bstep (se 1 (by rfl) ⟨435566, by rfl⟩ : syracuseStep 580755 = 871133) B871133
theorem B580771 : Blo 578813 580771 := bstep (se 1 (by rfl) ⟨435578, by rfl⟩ : syracuseStep 580771 = 871157) B871157
theorem B1105073 : Blo 578813 1105073 := bstep (se 2 (by rfl) ⟨414402, by rfl⟩ : syracuseStep 1105073 = 828805) B828805
theorem B580787 : Blo 578813 580787 := bstep (se 1 (by rfl) ⟨435590, by rfl⟩ : syracuseStep 580787 = 871181) B871181
theorem B580803 : Blo 578813 580803 := bstep (se 1 (by rfl) ⟨435602, by rfl⟩ : syracuseStep 580803 = 871205) B871205
theorem B1465553 : Blo 578813 1465553 := bstep (se 2 (by rfl) ⟨549582, by rfl⟩ : syracuseStep 1465553 = 1099165) B1099165
theorem B580819 : Blo 578813 580819 := bstep (se 1 (by rfl) ⟨435614, by rfl⟩ : syracuseStep 580819 = 871229) B871229
theorem B4709603 : Blo 578813 4709603 := bstep (se 1 (by rfl) ⟨3532202, by rfl⟩ : syracuseStep 4709603 = 7064405) B7064405
theorem B580835 : Blo 578813 580835 := bstep (se 1 (by rfl) ⟨435626, by rfl⟩ : syracuseStep 580835 = 871253) B871253
theorem B580851 : Blo 578813 580851 := bstep (se 1 (by rfl) ⟨435638, by rfl⟩ : syracuseStep 580851 = 871277) B871277
theorem B580867 : Blo 578813 580867 := bstep (se 1 (by rfl) ⟨435650, by rfl⟩ : syracuseStep 580867 = 871301) B871301
theorem B580883 : Blo 578813 580883 := bstep (se 1 (by rfl) ⟨435662, by rfl⟩ : syracuseStep 580883 = 871325) B871325
theorem B580899 : Blo 578813 580899 := bstep (se 1 (by rfl) ⟨435674, by rfl⟩ : syracuseStep 580899 = 871349) B871349
theorem B580915 : Blo 578813 580915 := bstep (se 1 (by rfl) ⟨435686, by rfl⟩ : syracuseStep 580915 = 871373) B871373
theorem B580931 : Blo 578813 580931 := bstep (se 1 (by rfl) ⟨435698, by rfl⟩ : syracuseStep 580931 = 871397) B871397
theorem B1236305 : Blo 578813 1236305 := bstep (se 2 (by rfl) ⟨463614, by rfl⟩ : syracuseStep 1236305 = 927229) B927229
theorem B580947 : Blo 578813 580947 := bstep (se 1 (by rfl) ⟨435710, by rfl⟩ : syracuseStep 580947 = 871421) B871421
theorem B580963 : Blo 578813 580963 := bstep (se 1 (by rfl) ⟨435722, by rfl⟩ : syracuseStep 580963 = 871445) B871445
theorem B1957229 : Blo 578813 1957229 := bstep (se 3 (by rfl) ⟨366980, by rfl⟩ : syracuseStep 1957229 = 733961) B733961
theorem B580979 : Blo 578813 580979 := bstep (se 1 (by rfl) ⟨435734, by rfl⟩ : syracuseStep 580979 = 871469) B871469
theorem B580995 : Blo 578813 580995 := bstep (se 1 (by rfl) ⟨435746, by rfl⟩ : syracuseStep 580995 = 871493) B871493
theorem B581011 : Blo 578813 581011 := bstep (se 1 (by rfl) ⟨435758, by rfl⟩ : syracuseStep 581011 = 871517) B871517
theorem B1957283 : Blo 578813 1957283 := bstep (se 1 (by rfl) ⟨1467962, by rfl⟩ : syracuseStep 1957283 = 2935925) B2935925
theorem B581027 : Blo 578813 581027 := bstep (se 1 (by rfl) ⟨435770, by rfl⟩ : syracuseStep 581027 = 871541) B871541
theorem B581043 : Blo 578813 581043 := bstep (se 1 (by rfl) ⟨435782, by rfl⟩ : syracuseStep 581043 = 871565) B871565
theorem B581059 : Blo 578813 581059 := bstep (se 1 (by rfl) ⟨435794, by rfl⟩ : syracuseStep 581059 = 871589) B871589
theorem B581075 : Blo 578813 581075 := bstep (se 1 (by rfl) ⟨435806, by rfl⟩ : syracuseStep 581075 = 871613) B871613
theorem B581091 : Blo 578813 581091 := bstep (se 1 (by rfl) ⟨435818, by rfl⟩ : syracuseStep 581091 = 871637) B871637
theorem B581107 : Blo 578813 581107 := bstep (se 1 (by rfl) ⟨435830, by rfl⟩ : syracuseStep 581107 = 871661) B871661
theorem B581123 : Blo 578813 581123 := bstep (se 1 (by rfl) ⟨435842, by rfl⟩ : syracuseStep 581123 = 871685) B871685
theorem B581139 : Blo 578813 581139 := bstep (se 1 (by rfl) ⟨435854, by rfl⟩ : syracuseStep 581139 = 871709) B871709
theorem B581155 : Blo 578813 581155 := bstep (se 1 (by rfl) ⟨435866, by rfl⟩ : syracuseStep 581155 = 871733) B871733
theorem B581171 : Blo 578813 581171 := bstep (se 1 (by rfl) ⟨435878, by rfl⟩ : syracuseStep 581171 = 871757) B871757
theorem B581187 : Blo 578813 581187 := bstep (se 1 (by rfl) ⟨435890, by rfl⟩ : syracuseStep 581187 = 871781) B871781
theorem B581203 : Blo 578813 581203 := bstep (se 1 (by rfl) ⟨435902, by rfl⟩ : syracuseStep 581203 = 871805) B871805
theorem B581219 : Blo 578813 581219 := bstep (se 1 (by rfl) ⟨435914, by rfl⟩ : syracuseStep 581219 = 871829) B871829
theorem B581235 : Blo 578813 581235 := bstep (se 1 (by rfl) ⟨435926, by rfl⟩ : syracuseStep 581235 = 871853) B871853
theorem B581251 : Blo 578813 581251 := bstep (se 1 (by rfl) ⟨435938, by rfl⟩ : syracuseStep 581251 = 871877) B871877
theorem B1859213 : Blo 578813 1859213 := bstep (se 3 (by rfl) ⟨348602, by rfl⟩ : syracuseStep 1859213 = 697205) B697205
theorem B581267 : Blo 578813 581267 := bstep (se 1 (by rfl) ⟨435950, by rfl⟩ : syracuseStep 581267 = 871901) B871901
theorem B581283 : Blo 578813 581283 := bstep (se 1 (by rfl) ⟨435962, by rfl⟩ : syracuseStep 581283 = 871925) B871925
theorem B1957553 : Blo 578813 1957553 := bstep (se 2 (by rfl) ⟨734082, by rfl⟩ : syracuseStep 1957553 = 1468165) B1468165
theorem B581299 : Blo 578813 581299 := bstep (se 1 (by rfl) ⟨435974, by rfl⟩ : syracuseStep 581299 = 871949) B871949
theorem B581315 : Blo 578813 581315 := bstep (se 1 (by rfl) ⟨435986, by rfl⟩ : syracuseStep 581315 = 871973) B871973
theorem B581331 : Blo 578813 581331 := bstep (se 1 (by rfl) ⟨435998, by rfl⟩ : syracuseStep 581331 = 871997) B871997
theorem B581347 : Blo 578813 581347 := bstep (se 1 (by rfl) ⟨436010, by rfl⟩ : syracuseStep 581347 = 872021) B872021
theorem B581363 : Blo 578813 581363 := bstep (se 1 (by rfl) ⟨436022, by rfl⟩ : syracuseStep 581363 = 872045) B872045
theorem B581379 : Blo 578813 581379 := bstep (se 1 (by rfl) ⟨436034, by rfl⟩ : syracuseStep 581379 = 872069) B872069
theorem B581395 : Blo 578813 581395 := bstep (se 1 (by rfl) ⟨436046, by rfl⟩ : syracuseStep 581395 = 872093) B872093
theorem B581411 : Blo 578813 581411 := bstep (se 1 (by rfl) ⟨436058, by rfl⟩ : syracuseStep 581411 = 872117) B872117
theorem B581427 : Blo 578813 581427 := bstep (se 1 (by rfl) ⟨436070, by rfl⟩ : syracuseStep 581427 = 872141) B872141
theorem B581443 : Blo 578813 581443 := bstep (se 1 (by rfl) ⟨436082, by rfl⟩ : syracuseStep 581443 = 872165) B872165
theorem B1302353 : Blo 578813 1302353 := bstep (se 2 (by rfl) ⟨488382, by rfl⟩ : syracuseStep 1302353 = 976765) B976765
theorem B1236817 : Blo 578813 1236817 := bstep (se 2 (by rfl) ⟨463806, by rfl⟩ : syracuseStep 1236817 = 927613) B927613
theorem B581459 : Blo 578813 581459 := bstep (se 1 (by rfl) ⟨436094, by rfl⟩ : syracuseStep 581459 = 872189) B872189
theorem B1302371 : Blo 578813 1302371 := bstep (se 1 (by rfl) ⟨976778, by rfl⟩ : syracuseStep 1302371 = 1953557) B1953557
theorem B581475 : Blo 578813 581475 := bstep (se 1 (by rfl) ⟨436106, by rfl⟩ : syracuseStep 581475 = 872213) B872213
theorem B2940785 : Blo 578813 2940785 := bstep (se 2 (by rfl) ⟨1102794, by rfl⟩ : syracuseStep 2940785 = 2205589) B2205589
theorem B581491 : Blo 578813 581491 := bstep (se 1 (by rfl) ⟨436118, by rfl⟩ : syracuseStep 581491 = 872237) B872237
theorem B581507 : Blo 578813 581507 := bstep (se 1 (by rfl) ⟨436130, by rfl⟩ : syracuseStep 581507 = 872261) B872261
theorem B581523 : Blo 578813 581523 := bstep (se 1 (by rfl) ⟨436142, by rfl⟩ : syracuseStep 581523 = 872285) B872285
theorem B581539 : Blo 578813 581539 := bstep (se 1 (by rfl) ⟨436154, by rfl⟩ : syracuseStep 581539 = 872309) B872309
theorem B581555 : Blo 578813 581555 := bstep (se 1 (by rfl) ⟨436166, by rfl⟩ : syracuseStep 581555 = 872333) B872333
theorem B581571 : Blo 578813 581571 := bstep (se 1 (by rfl) ⟨436178, by rfl⟩ : syracuseStep 581571 = 872357) B872357
theorem B581587 : Blo 578813 581587 := bstep (se 1 (by rfl) ⟨436190, by rfl⟩ : syracuseStep 581587 = 872381) B872381
theorem B581603 : Blo 578813 581603 := bstep (se 1 (by rfl) ⟨436202, by rfl⟩ : syracuseStep 581603 = 872405) B872405
theorem B7430129 : Blo 578813 7430129 := bstep (se 2 (by rfl) ⟨2786298, by rfl⟩ : syracuseStep 7430129 = 5572597) B5572597
theorem B581619 : Blo 578813 581619 := bstep (se 1 (by rfl) ⟨436214, by rfl⟩ : syracuseStep 581619 = 872429) B872429
theorem B581635 : Blo 578813 581635 := bstep (se 1 (by rfl) ⟨436226, by rfl⟩ : syracuseStep 581635 = 872453) B872453
theorem B581651 : Blo 578813 581651 := bstep (se 1 (by rfl) ⟨436238, by rfl⟩ : syracuseStep 581651 = 872477) B872477
theorem B581667 : Blo 578813 581667 := bstep (se 1 (by rfl) ⟨436250, by rfl⟩ : syracuseStep 581667 = 872501) B872501
theorem B1105969 : Blo 578813 1105969 := bstep (se 2 (by rfl) ⟨414738, by rfl⟩ : syracuseStep 1105969 = 829477) B829477
theorem B581683 : Blo 578813 581683 := bstep (se 1 (by rfl) ⟨436262, by rfl⟩ : syracuseStep 581683 = 872525) B872525
theorem B581699 : Blo 578813 581699 := bstep (se 1 (by rfl) ⟨436274, by rfl⟩ : syracuseStep 581699 = 872549) B872549
theorem B581715 : Blo 578813 581715 := bstep (se 1 (by rfl) ⟨436286, by rfl⟩ : syracuseStep 581715 = 872573) B872573
theorem B581731 : Blo 578813 581731 := bstep (se 1 (by rfl) ⟨436298, by rfl⟩ : syracuseStep 581731 = 872597) B872597
theorem B1302641 : Blo 578813 1302641 := bstep (se 2 (by rfl) ⟨488490, by rfl⟩ : syracuseStep 1302641 = 976981) B976981
theorem B581747 : Blo 578813 581747 := bstep (se 1 (by rfl) ⟨436310, by rfl⟩ : syracuseStep 581747 = 872621) B872621
theorem B1302659 : Blo 578813 1302659 := bstep (se 1 (by rfl) ⟨976994, by rfl⟩ : syracuseStep 1302659 = 1953989) B1953989
theorem B581763 : Blo 578813 581763 := bstep (se 1 (by rfl) ⟨436322, by rfl⟩ : syracuseStep 581763 = 872645) B872645
theorem B581779 : Blo 578813 581779 := bstep (se 1 (by rfl) ⟨436334, by rfl⟩ : syracuseStep 581779 = 872669) B872669
theorem B581795 : Blo 578813 581795 := bstep (se 1 (by rfl) ⟨436346, by rfl⟩ : syracuseStep 581795 = 872693) B872693
theorem B1466545 : Blo 578813 1466545 := bstep (se 2 (by rfl) ⟨549954, by rfl⟩ : syracuseStep 1466545 = 1099909) B1099909
theorem B581811 : Blo 578813 581811 := bstep (se 1 (by rfl) ⟨436358, by rfl⟩ : syracuseStep 581811 = 872717) B872717
theorem B581827 : Blo 578813 581827 := bstep (se 1 (by rfl) ⟨436370, by rfl⟩ : syracuseStep 581827 = 872741) B872741
theorem B1958093 : Blo 578813 1958093 := bstep (se 3 (by rfl) ⟨367142, by rfl⟩ : syracuseStep 1958093 = 734285) B734285
theorem B1106129 : Blo 578813 1106129 := bstep (se 2 (by rfl) ⟨414798, by rfl⟩ : syracuseStep 1106129 = 829597) B829597
theorem B581843 : Blo 578813 581843 := bstep (se 1 (by rfl) ⟨436382, by rfl⟩ : syracuseStep 581843 = 872765) B872765
theorem B581859 : Blo 578813 581859 := bstep (se 1 (by rfl) ⟨436394, by rfl⟩ : syracuseStep 581859 = 872789) B872789
theorem B581875 : Blo 578813 581875 := bstep (se 1 (by rfl) ⟨436406, by rfl⟩ : syracuseStep 581875 = 872813) B872813
theorem B1958147 : Blo 578813 1958147 := bstep (se 1 (by rfl) ⟨1468610, by rfl⟩ : syracuseStep 1958147 = 2937221) B2937221
theorem B581891 : Blo 578813 581891 := bstep (se 1 (by rfl) ⟨436418, by rfl⟩ : syracuseStep 581891 = 872837) B872837
theorem B581907 : Blo 578813 581907 := bstep (se 1 (by rfl) ⟨436430, by rfl⟩ : syracuseStep 581907 = 872861) B872861
theorem B581923 : Blo 578813 581923 := bstep (se 1 (by rfl) ⟨436442, by rfl⟩ : syracuseStep 581923 = 872885) B872885
theorem B581939 : Blo 578813 581939 := bstep (se 1 (by rfl) ⟨436454, by rfl⟩ : syracuseStep 581939 = 872909) B872909
theorem B581955 : Blo 578813 581955 := bstep (se 1 (by rfl) ⟨436466, by rfl⟩ : syracuseStep 581955 = 872933) B872933
theorem B3760453 : Blo 578813 3760453 := bstep (se 4 (by rfl) ⟨352542, by rfl⟩ : syracuseStep 3760453 = 705085) B705085
theorem B581971 : Blo 578813 581971 := bstep (se 1 (by rfl) ⟨436478, by rfl⟩ : syracuseStep 581971 = 872957) B872957
theorem B7954787 : Blo 578813 7954787 := bstep (se 1 (by rfl) ⟨5966090, by rfl⟩ : syracuseStep 7954787 = 11932181) B11932181
theorem B581987 : Blo 578813 581987 := bstep (se 1 (by rfl) ⟨436490, by rfl⟩ : syracuseStep 581987 = 872981) B872981
theorem B582003 : Blo 578813 582003 := bstep (se 1 (by rfl) ⟨436502, by rfl⟩ : syracuseStep 582003 = 873005) B873005
theorem B582019 : Blo 578813 582019 := bstep (se 1 (by rfl) ⟨436514, by rfl⟩ : syracuseStep 582019 = 873029) B873029
theorem B1302929 : Blo 578813 1302929 := bstep (se 2 (by rfl) ⟨488598, by rfl⟩ : syracuseStep 1302929 = 977197) B977197
theorem B582035 : Blo 578813 582035 := bstep (se 1 (by rfl) ⟨436526, by rfl⟩ : syracuseStep 582035 = 873053) B873053
theorem B1302947 : Blo 578813 1302947 := bstep (se 1 (by rfl) ⟨977210, by rfl⟩ : syracuseStep 1302947 = 1954421) B1954421
theorem B582051 : Blo 578813 582051 := bstep (se 1 (by rfl) ⟨436538, by rfl⟩ : syracuseStep 582051 = 873077) B873077
theorem B582067 : Blo 578813 582067 := bstep (se 1 (by rfl) ⟨436550, by rfl⟩ : syracuseStep 582067 = 873101) B873101
theorem B1466819 : Blo 578813 1466819 := bstep (se 1 (by rfl) ⟨1100114, by rfl⟩ : syracuseStep 1466819 = 2200229) B2200229
theorem B582083 : Blo 578813 582083 := bstep (se 1 (by rfl) ⟨436562, by rfl⟩ : syracuseStep 582083 = 873125) B873125
theorem B582099 : Blo 578813 582099 := bstep (se 1 (by rfl) ⟨436574, by rfl⟩ : syracuseStep 582099 = 873149) B873149
theorem B582115 : Blo 578813 582115 := bstep (se 1 (by rfl) ⟨436586, by rfl⟩ : syracuseStep 582115 = 873173) B873173
theorem B582131 : Blo 578813 582131 := bstep (se 1 (by rfl) ⟨436598, by rfl⟩ : syracuseStep 582131 = 873197) B873197
theorem B582147 : Blo 578813 582147 := bstep (se 1 (by rfl) ⟨436610, by rfl⟩ : syracuseStep 582147 = 873221) B873221
theorem B1958417 : Blo 578813 1958417 := bstep (se 2 (by rfl) ⟨734406, by rfl⟩ : syracuseStep 1958417 = 1468813) B1468813
theorem B582163 : Blo 578813 582163 := bstep (se 1 (by rfl) ⟨436622, by rfl⟩ : syracuseStep 582163 = 873245) B873245
theorem B582179 : Blo 578813 582179 := bstep (se 1 (by rfl) ⟨436634, by rfl⟩ : syracuseStep 582179 = 873269) B873269
theorem B582195 : Blo 578813 582195 := bstep (se 1 (by rfl) ⟨436646, by rfl⟩ : syracuseStep 582195 = 873293) B873293
theorem B582211 : Blo 578813 582211 := bstep (se 1 (by rfl) ⟨436658, by rfl⟩ : syracuseStep 582211 = 873317) B873317
theorem B1565261 : Blo 578813 1565261 := bstep (se 3 (by rfl) ⟨293486, by rfl⟩ : syracuseStep 1565261 = 586973) B586973
theorem B582227 : Blo 578813 582227 := bstep (se 1 (by rfl) ⟨436670, by rfl⟩ : syracuseStep 582227 = 873341) B873341
theorem B582243 : Blo 578813 582243 := bstep (se 1 (by rfl) ⟨436682, by rfl⟩ : syracuseStep 582243 = 873365) B873365
theorem B582259 : Blo 578813 582259 := bstep (se 1 (by rfl) ⟨436694, by rfl⟩ : syracuseStep 582259 = 873389) B873389
theorem B1467011 : Blo 578813 1467011 := bstep (se 1 (by rfl) ⟨1100258, by rfl⟩ : syracuseStep 1467011 = 2200517) B2200517
theorem B582275 : Blo 578813 582275 := bstep (se 1 (by rfl) ⟨436706, by rfl⟩ : syracuseStep 582275 = 873413) B873413
theorem B582291 : Blo 578813 582291 := bstep (se 1 (by rfl) ⟨436718, by rfl⟩ : syracuseStep 582291 = 873437) B873437
theorem B582307 : Blo 578813 582307 := bstep (se 1 (by rfl) ⟨436730, by rfl⟩ : syracuseStep 582307 = 873461) B873461
theorem B1303217 : Blo 578813 1303217 := bstep (se 2 (by rfl) ⟨488706, by rfl⟩ : syracuseStep 1303217 = 977413) B977413
theorem B582323 : Blo 578813 582323 := bstep (se 1 (by rfl) ⟨436742, by rfl⟩ : syracuseStep 582323 = 873485) B873485
theorem B1303235 : Blo 578813 1303235 := bstep (se 1 (by rfl) ⟨977426, by rfl⟩ : syracuseStep 1303235 = 1954853) B1954853
theorem B582339 : Blo 578813 582339 := bstep (se 1 (by rfl) ⟨436754, by rfl⟩ : syracuseStep 582339 = 873509) B873509
theorem B582355 : Blo 578813 582355 := bstep (se 1 (by rfl) ⟨436766, by rfl⟩ : syracuseStep 582355 = 873533) B873533
theorem B582371 : Blo 578813 582371 := bstep (se 1 (by rfl) ⟨436778, by rfl⟩ : syracuseStep 582371 = 873557) B873557
theorem B582387 : Blo 578813 582387 := bstep (se 1 (by rfl) ⟨436790, by rfl⟩ : syracuseStep 582387 = 873581) B873581
theorem B582403 : Blo 578813 582403 := bstep (se 1 (by rfl) ⟨436802, by rfl⟩ : syracuseStep 582403 = 873605) B873605
theorem B582419 : Blo 578813 582419 := bstep (se 1 (by rfl) ⟨436814, by rfl⟩ : syracuseStep 582419 = 873629) B873629
theorem B582435 : Blo 578813 582435 := bstep (se 1 (by rfl) ⟨436826, by rfl⟩ : syracuseStep 582435 = 873653) B873653
theorem B582451 : Blo 578813 582451 := bstep (se 1 (by rfl) ⟨436838, by rfl⟩ : syracuseStep 582451 = 873677) B873677
theorem B582467 : Blo 578813 582467 := bstep (se 1 (by rfl) ⟨436850, by rfl⟩ : syracuseStep 582467 = 873701) B873701
theorem B582483 : Blo 578813 582483 := bstep (se 1 (by rfl) ⟨436862, by rfl⟩ : syracuseStep 582483 = 873725) B873725
theorem B582499 : Blo 578813 582499 := bstep (se 1 (by rfl) ⟨436874, by rfl⟩ : syracuseStep 582499 = 873749) B873749
theorem B582515 : Blo 578813 582515 := bstep (se 1 (by rfl) ⟨436886, by rfl⟩ : syracuseStep 582515 = 873773) B873773
theorem B582531 : Blo 578813 582531 := bstep (se 1 (by rfl) ⟨436898, by rfl⟩ : syracuseStep 582531 = 873797) B873797
theorem B582547 : Blo 578813 582547 := bstep (se 1 (by rfl) ⟨436910, by rfl⟩ : syracuseStep 582547 = 873821) B873821
theorem B582563 : Blo 578813 582563 := bstep (se 1 (by rfl) ⟨436922, by rfl⟩ : syracuseStep 582563 = 873845) B873845
theorem B582579 : Blo 578813 582579 := bstep (se 1 (by rfl) ⟨436934, by rfl⟩ : syracuseStep 582579 = 873869) B873869
theorem B582595 : Blo 578813 582595 := bstep (se 1 (by rfl) ⟨436946, by rfl⟩ : syracuseStep 582595 = 873893) B873893
theorem B1303505 : Blo 578813 1303505 := bstep (se 2 (by rfl) ⟨488814, by rfl⟩ : syracuseStep 1303505 = 977629) B977629
theorem B582611 : Blo 578813 582611 := bstep (se 1 (by rfl) ⟨436958, by rfl⟩ : syracuseStep 582611 = 873917) B873917
theorem B1303523 : Blo 578813 1303523 := bstep (se 1 (by rfl) ⟨977642, by rfl⟩ : syracuseStep 1303523 = 1955285) B1955285
theorem B582627 : Blo 578813 582627 := bstep (se 1 (by rfl) ⟨436970, by rfl⟩ : syracuseStep 582627 = 873941) B873941
theorem B582643 : Blo 578813 582643 := bstep (se 1 (by rfl) ⟨436982, by rfl⟩ : syracuseStep 582643 = 873965) B873965
theorem B582659 : Blo 578813 582659 := bstep (se 1 (by rfl) ⟨436994, by rfl⟩ : syracuseStep 582659 = 873989) B873989
theorem B582675 : Blo 578813 582675 := bstep (se 1 (by rfl) ⟨437006, by rfl⟩ : syracuseStep 582675 = 874013) B874013
theorem B582691 : Blo 578813 582691 := bstep (se 1 (by rfl) ⟨437018, by rfl⟩ : syracuseStep 582691 = 874037) B874037
theorem B1958957 : Blo 578813 1958957 := bstep (se 3 (by rfl) ⟨367304, by rfl⟩ : syracuseStep 1958957 = 734609) B734609
theorem B582707 : Blo 578813 582707 := bstep (se 1 (by rfl) ⟨437030, by rfl⟩ : syracuseStep 582707 = 874061) B874061
theorem B582723 : Blo 578813 582723 := bstep (se 1 (by rfl) ⟨437042, by rfl⟩ : syracuseStep 582723 = 874085) B874085
theorem B582739 : Blo 578813 582739 := bstep (se 1 (by rfl) ⟨437054, by rfl⟩ : syracuseStep 582739 = 874109) B874109
theorem B1959011 : Blo 578813 1959011 := bstep (se 1 (by rfl) ⟨1469258, by rfl⟩ : syracuseStep 1959011 = 2938517) B2938517
theorem B582755 : Blo 578813 582755 := bstep (se 1 (by rfl) ⟨437066, by rfl⟩ : syracuseStep 582755 = 874133) B874133
theorem B582771 : Blo 578813 582771 := bstep (se 1 (by rfl) ⟨437078, by rfl⟩ : syracuseStep 582771 = 874157) B874157
theorem B582787 : Blo 578813 582787 := bstep (se 1 (by rfl) ⟨437090, by rfl⟩ : syracuseStep 582787 = 874181) B874181
theorem B582803 : Blo 578813 582803 := bstep (se 1 (by rfl) ⟨437102, by rfl⟩ : syracuseStep 582803 = 874205) B874205
theorem B1303793 : Blo 578813 1303793 := bstep (se 2 (by rfl) ⟨488922, by rfl⟩ : syracuseStep 1303793 = 977845) B977845
theorem B1303811 : Blo 578813 1303811 := bstep (se 1 (by rfl) ⟨977858, by rfl⟩ : syracuseStep 1303811 = 1955717) B1955717
theorem B2942243 : Blo 578813 2942243 := bstep (se 1 (by rfl) ⟨2206682, by rfl⟩ : syracuseStep 2942243 = 4413365) B4413365
theorem B1238321 : Blo 578813 1238321 := bstep (se 2 (by rfl) ⟨464370, by rfl⟩ : syracuseStep 1238321 = 928741) B928741
theorem B2647345 : Blo 578813 2647345 := bstep (se 2 (by rfl) ⟨992754, by rfl⟩ : syracuseStep 2647345 = 1985509) B1985509
theorem B1959281 : Blo 578813 1959281 := bstep (se 2 (by rfl) ⟨734730, by rfl⟩ : syracuseStep 1959281 = 1469461) B1469461
theorem B3728753 : Blo 578813 3728753 := bstep (se 2 (by rfl) ⟨1398282, by rfl⟩ : syracuseStep 3728753 = 2796565) B2796565
theorem B1861069 : Blo 578813 1861069 := bstep (se 3 (by rfl) ⟨348950, by rfl⟩ : syracuseStep 1861069 = 697901) B697901
theorem B1304081 : Blo 578813 1304081 := bstep (se 2 (by rfl) ⟨489030, by rfl⟩ : syracuseStep 1304081 = 978061) B978061
theorem B1304099 : Blo 578813 1304099 := bstep (se 1 (by rfl) ⟨978074, by rfl⟩ : syracuseStep 1304099 = 1956149) B1956149
theorem B1467953 : Blo 578813 1467953 := bstep (se 2 (by rfl) ⟨550482, by rfl⟩ : syracuseStep 1467953 = 1100965) B1100965
theorem B1468003 : Blo 578813 1468003 := bstep (se 1 (by rfl) ⟨1101002, by rfl⟩ : syracuseStep 1468003 = 2202005) B2202005
theorem B2123441 : Blo 578813 2123441 := bstep (se 2 (by rfl) ⟨796290, by rfl⟩ : syracuseStep 2123441 = 1592581) B1592581
theorem B1238723 : Blo 578813 1238723 := bstep (se 1 (by rfl) ⟨929042, by rfl⟩ : syracuseStep 1238723 = 1858085) B1858085
theorem B1468145 : Blo 578813 1468145 := bstep (se 2 (by rfl) ⟨550554, by rfl⟩ : syracuseStep 1468145 = 1101109) B1101109
theorem B1009441 : Blo 578813 1009441 := bstep (se 2 (by rfl) ⟨378540, by rfl⟩ : syracuseStep 1009441 = 757081) B757081
theorem B1304369 : Blo 578813 1304369 := bstep (se 2 (by rfl) ⟨489138, by rfl⟩ : syracuseStep 1304369 = 978277) B978277
theorem B1304387 : Blo 578813 1304387 := bstep (se 1 (by rfl) ⟨978290, by rfl⟩ : syracuseStep 1304387 = 1956581) B1956581
theorem B3303281 : Blo 578813 3303281 := bstep (se 2 (by rfl) ⟨1238730, by rfl⟩ : syracuseStep 3303281 = 2477461) B2477461
theorem B1959821 : Blo 578813 1959821 := bstep (se 3 (by rfl) ⟨367466, by rfl⟩ : syracuseStep 1959821 = 734933) B734933
theorem B976819 : Blo 578813 976819 := bstep (se 1 (by rfl) ⟨732614, by rfl⟩ : syracuseStep 976819 = 1465229) B1465229
theorem B1959875 : Blo 578813 1959875 := bstep (se 1 (by rfl) ⟨1469906, by rfl⟩ : syracuseStep 1959875 = 2939813) B2939813
theorem B4974605 : Blo 578813 4974605 := bstep (se 3 (by rfl) ⟨932738, by rfl⟩ : syracuseStep 4974605 = 1865477) B1865477
theorem B976961 : Blo 578813 976961 := bstep (se 2 (by rfl) ⟨366360, by rfl⟩ : syracuseStep 976961 = 732721) B732721
theorem B2943053 : Blo 578813 2943053 := bstep (se 3 (by rfl) ⟨551822, by rfl⟩ : syracuseStep 2943053 = 1103645) B1103645
theorem B1304657 : Blo 578813 1304657 := bstep (se 2 (by rfl) ⟨489246, by rfl⟩ : syracuseStep 1304657 = 978493) B978493
theorem B1304675 : Blo 578813 1304675 := bstep (se 1 (by rfl) ⟨978506, by rfl⟩ : syracuseStep 1304675 = 1957013) B1957013
theorem B977089 : Blo 578813 977089 := bstep (se 2 (by rfl) ⟨366408, by rfl⟩ : syracuseStep 977089 = 732817) B732817
theorem B1960145 : Blo 578813 1960145 := bstep (se 2 (by rfl) ⟨735054, by rfl⟩ : syracuseStep 1960145 = 1470109) B1470109
theorem B977123 : Blo 578813 977123 := bstep (se 1 (by rfl) ⟨732842, by rfl⟩ : syracuseStep 977123 = 1465685) B1465685
theorem B977251 : Blo 578813 977251 := bstep (se 1 (by rfl) ⟨732938, by rfl⟩ : syracuseStep 977251 = 1465877) B1465877
theorem B1304945 : Blo 578813 1304945 := bstep (se 2 (by rfl) ⟨489354, by rfl⟩ : syracuseStep 1304945 = 978709) B978709
theorem B1304963 : Blo 578813 1304963 := bstep (se 1 (by rfl) ⟨978722, by rfl⟩ : syracuseStep 1304963 = 1957445) B1957445
theorem B3729827 : Blo 578813 3729827 := bstep (se 1 (by rfl) ⟨2797370, by rfl⟩ : syracuseStep 3729827 = 5594741) B5594741
theorem B1993187 : Blo 578813 1993187 := bstep (se 1 (by rfl) ⟨1494890, by rfl⟩ : syracuseStep 1993187 = 2989781) B2989781
theorem B977393 : Blo 578813 977393 := bstep (se 2 (by rfl) ⟨366522, by rfl⟩ : syracuseStep 977393 = 733045) B733045
theorem B3631601 : Blo 578813 3631601 := bstep (se 2 (by rfl) ⟨1361850, by rfl⟩ : syracuseStep 3631601 = 2723701) B2723701
theorem B1239619 : Blo 578813 1239619 := bstep (se 1 (by rfl) ⟨929714, by rfl⟩ : syracuseStep 1239619 = 1859429) B1859429
theorem B977521 : Blo 578813 977521 := bstep (se 2 (by rfl) ⟨366570, by rfl⟩ : syracuseStep 977521 = 733141) B733141
theorem B2484877 : Blo 578813 2484877 := bstep (se 3 (by rfl) ⟨465914, by rfl⟩ : syracuseStep 2484877 = 931829) B931829
theorem B1305233 : Blo 578813 1305233 := bstep (se 2 (by rfl) ⟨489462, by rfl⟩ : syracuseStep 1305233 = 978925) B978925
theorem B977555 : Blo 578813 977555 := bstep (se 1 (by rfl) ⟨733166, by rfl⟩ : syracuseStep 977555 = 1466333) B1466333
theorem B1305251 : Blo 578813 1305251 := bstep (se 1 (by rfl) ⟨978938, by rfl⟩ : syracuseStep 1305251 = 1957877) B1957877
theorem B1469137 : Blo 578813 1469137 := bstep (se 2 (by rfl) ⟨550926, by rfl⟩ : syracuseStep 1469137 = 1101853) B1101853
theorem B1960685 : Blo 578813 1960685 := bstep (se 3 (by rfl) ⟨367628, by rfl⟩ : syracuseStep 1960685 = 735257) B735257
theorem B977683 : Blo 578813 977683 := bstep (se 1 (by rfl) ⟨733262, by rfl⟩ : syracuseStep 977683 = 1466525) B1466525
theorem B1960739 : Blo 578813 1960739 := bstep (se 1 (by rfl) ⟨1470554, by rfl⟩ : syracuseStep 1960739 = 2941109) B2941109
theorem B7269173 : Blo 578813 7269173 := bstep (se 5 (by rfl) ⟨340742, by rfl⟩ : syracuseStep 7269173 = 681485) B681485
theorem B1567619 : Blo 578813 1567619 := bstep (se 1 (by rfl) ⟨1175714, by rfl⟩ : syracuseStep 1567619 = 2351429) B2351429
theorem B977825 : Blo 578813 977825 := bstep (se 2 (by rfl) ⟨366684, by rfl⟩ : syracuseStep 977825 = 733369) B733369
theorem B1305521 : Blo 578813 1305521 := bstep (se 2 (by rfl) ⟨489570, by rfl⟩ : syracuseStep 1305521 = 979141) B979141
theorem B1305539 : Blo 578813 1305539 := bstep (se 1 (by rfl) ⟨979154, by rfl⟩ : syracuseStep 1305539 = 1958309) B1958309
theorem B1469411 : Blo 578813 1469411 := bstep (se 1 (by rfl) ⟨1102058, by rfl⟩ : syracuseStep 1469411 = 2204117) B2204117
theorem B977953 : Blo 578813 977953 := bstep (se 2 (by rfl) ⟨366732, by rfl⟩ : syracuseStep 977953 = 733465) B733465
theorem B1961009 : Blo 578813 1961009 := bstep (se 2 (by rfl) ⟨735378, by rfl⟩ : syracuseStep 1961009 = 1470757) B1470757
theorem B977987 : Blo 578813 977987 := bstep (se 1 (by rfl) ⟨733490, by rfl⟩ : syracuseStep 977987 = 1466981) B1466981
theorem B1862801 : Blo 578813 1862801 := bstep (se 2 (by rfl) ⟨698550, by rfl⟩ : syracuseStep 1862801 = 1397101) B1397101
theorem B1469603 : Blo 578813 1469603 := bstep (se 1 (by rfl) ⟨1102202, by rfl⟩ : syracuseStep 1469603 = 2204405) B2204405
theorem B978115 : Blo 578813 978115 := bstep (se 1 (by rfl) ⟨733586, by rfl⟩ : syracuseStep 978115 = 1467173) B1467173
theorem B1305809 : Blo 578813 1305809 := bstep (se 2 (by rfl) ⟨489678, by rfl⟩ : syracuseStep 1305809 = 979357) B979357
theorem B1305827 : Blo 578813 1305827 := bstep (se 1 (by rfl) ⟨979370, by rfl⟩ : syracuseStep 1305827 = 1958741) B1958741
theorem B3304739 : Blo 578813 3304739 := bstep (se 1 (by rfl) ⟨2478554, by rfl⟩ : syracuseStep 3304739 = 4957109) B4957109
theorem B978257 : Blo 578813 978257 := bstep (se 2 (by rfl) ⟨366846, by rfl⟩ : syracuseStep 978257 = 733693) B733693
theorem B2092493 : Blo 578813 2092493 := bstep (se 3 (by rfl) ⟨392342, by rfl⟩ : syracuseStep 2092493 = 784685) B784685
theorem B978385 : Blo 578813 978385 := bstep (se 2 (by rfl) ⟨366894, by rfl⟩ : syracuseStep 978385 = 733789) B733789
theorem B1306097 : Blo 578813 1306097 := bstep (se 2 (by rfl) ⟨489786, by rfl⟩ : syracuseStep 1306097 = 979573) B979573
theorem B978419 : Blo 578813 978419 := bstep (se 1 (by rfl) ⟨733814, by rfl⟩ : syracuseStep 978419 = 1467629) B1467629
theorem B1306115 : Blo 578813 1306115 := bstep (se 1 (by rfl) ⟨979586, by rfl⟩ : syracuseStep 1306115 = 1959173) B1959173
theorem B1961549 : Blo 578813 1961549 := bstep (se 3 (by rfl) ⟨367790, by rfl⟩ : syracuseStep 1961549 = 735581) B735581
theorem B978547 : Blo 578813 978547 := bstep (se 1 (by rfl) ⟨733910, by rfl⟩ : syracuseStep 978547 = 1467821) B1467821
theorem B1961603 : Blo 578813 1961603 := bstep (se 1 (by rfl) ⟨1471202, by rfl⟩ : syracuseStep 1961603 = 2942405) B2942405
theorem B978689 : Blo 578813 978689 := bstep (se 2 (by rfl) ⟨367008, by rfl⟩ : syracuseStep 978689 = 734017) B734017
theorem B1863427 : Blo 578813 1863427 := bstep (se 1 (by rfl) ⟨1397570, by rfl⟩ : syracuseStep 1863427 = 2795141) B2795141
theorem B1306385 : Blo 578813 1306385 := bstep (se 2 (by rfl) ⟨489894, by rfl⟩ : syracuseStep 1306385 = 979789) B979789
theorem B1240849 : Blo 578813 1240849 := bstep (se 2 (by rfl) ⟨465318, by rfl⟩ : syracuseStep 1240849 = 930637) B930637
theorem B1306403 : Blo 578813 1306403 := bstep (se 1 (by rfl) ⟨979802, by rfl⟩ : syracuseStep 1306403 = 1959605) B1959605
theorem B978817 : Blo 578813 978817 := bstep (se 2 (by rfl) ⟨367056, by rfl⟩ : syracuseStep 978817 = 734113) B734113
theorem B1961873 : Blo 578813 1961873 := bstep (se 2 (by rfl) ⟨735702, by rfl⟩ : syracuseStep 1961873 = 1471405) B1471405
theorem B978851 : Blo 578813 978851 := bstep (se 1 (by rfl) ⟨734138, by rfl⟩ : syracuseStep 978851 = 1468277) B1468277
theorem B651235 : Blo 578813 651235 := bstep (se 1 (by rfl) ⟨488426, by rfl⟩ : syracuseStep 651235 = 976853) B976853
theorem B978979 : Blo 578813 978979 := bstep (se 1 (by rfl) ⟨734234, by rfl⟩ : syracuseStep 978979 = 1468469) B1468469
theorem B1306673 : Blo 578813 1306673 := bstep (se 2 (by rfl) ⟨490002, by rfl⟩ : syracuseStep 1306673 = 980005) B980005
theorem B1306691 : Blo 578813 1306691 := bstep (se 1 (by rfl) ⟨980018, by rfl⟩ : syracuseStep 1306691 = 1960037) B1960037
theorem B1470545 : Blo 578813 1470545 := bstep (se 2 (by rfl) ⟨551454, by rfl⟩ : syracuseStep 1470545 = 1102909) B1102909
theorem B4419683 : Blo 578813 4419683 := bstep (se 1 (by rfl) ⟨3314762, by rfl⟩ : syracuseStep 4419683 = 6629525) B6629525
theorem B651379 : Blo 578813 651379 := bstep (se 1 (by rfl) ⟨488534, by rfl⟩ : syracuseStep 651379 = 977069) B977069
theorem B1470595 : Blo 578813 1470595 := bstep (se 1 (by rfl) ⟨1102946, by rfl⟩ : syracuseStep 1470595 = 2205893) B2205893
theorem B979121 : Blo 578813 979121 := bstep (se 2 (by rfl) ⟨367170, by rfl⟩ : syracuseStep 979121 = 734341) B734341
theorem B651523 : Blo 578813 651523 := bstep (se 1 (by rfl) ⟨488642, by rfl⟩ : syracuseStep 651523 = 977285) B977285
theorem B1470737 : Blo 578813 1470737 := bstep (se 2 (by rfl) ⟨551526, by rfl⟩ : syracuseStep 1470737 = 1103053) B1103053
theorem B979249 : Blo 578813 979249 := bstep (se 2 (by rfl) ⟨367218, by rfl⟩ : syracuseStep 979249 = 734437) B734437
theorem B1306961 : Blo 578813 1306961 := bstep (se 2 (by rfl) ⟨490110, by rfl⟩ : syracuseStep 1306961 = 980221) B980221
theorem B979283 : Blo 578813 979283 := bstep (se 1 (by rfl) ⟨734462, by rfl⟩ : syracuseStep 979283 = 1468925) B1468925
theorem B1306979 : Blo 578813 1306979 := bstep (se 1 (by rfl) ⟨980234, by rfl⟩ : syracuseStep 1306979 = 1960469) B1960469
theorem B651667 : Blo 578813 651667 := bstep (se 1 (by rfl) ⟨488750, by rfl⟩ : syracuseStep 651667 = 977501) B977501
theorem B1962413 : Blo 578813 1962413 := bstep (se 3 (by rfl) ⟨367952, by rfl⟩ : syracuseStep 1962413 = 735905) B735905
theorem B782803 : Blo 578813 782803 := bstep (se 1 (by rfl) ⟨587102, by rfl⟩ : syracuseStep 782803 = 1174205) B1174205
theorem B979411 : Blo 578813 979411 := bstep (se 1 (by rfl) ⟨734558, by rfl⟩ : syracuseStep 979411 = 1469117) B1469117
theorem B1962467 : Blo 578813 1962467 := bstep (se 1 (by rfl) ⟨1471850, by rfl⟩ : syracuseStep 1962467 = 2943701) B2943701
theorem B651811 : Blo 578813 651811 := bstep (se 1 (by rfl) ⟨488858, by rfl⟩ : syracuseStep 651811 = 977717) B977717
theorem B979553 : Blo 578813 979553 := bstep (se 2 (by rfl) ⟨367332, by rfl⟩ : syracuseStep 979553 = 734665) B734665
theorem B1307249 : Blo 578813 1307249 := bstep (se 2 (by rfl) ⟨490218, by rfl⟩ : syracuseStep 1307249 = 980437) B980437
theorem B1307267 : Blo 578813 1307267 := bstep (se 1 (by rfl) ⟨980450, by rfl⟩ : syracuseStep 1307267 = 1960901) B1960901
theorem B651955 : Blo 578813 651955 := bstep (se 1 (by rfl) ⟨488966, by rfl⟩ : syracuseStep 651955 = 977933) B977933
theorem B979681 : Blo 578813 979681 := bstep (se 2 (by rfl) ⟨367380, by rfl⟩ : syracuseStep 979681 = 734761) B734761
theorem B1962737 : Blo 578813 1962737 := bstep (se 2 (by rfl) ⟨736026, by rfl⟩ : syracuseStep 1962737 = 1472053) B1472053
theorem B979715 : Blo 578813 979715 := bstep (se 1 (by rfl) ⟨734786, by rfl⟩ : syracuseStep 979715 = 1469573) B1469573
theorem B652099 : Blo 578813 652099 := bstep (se 1 (by rfl) ⟨489074, by rfl⟩ : syracuseStep 652099 = 978149) B978149
theorem B619331 : Blo 578813 619331 := bstep (se 1 (by rfl) ⟨464498, by rfl⟩ : syracuseStep 619331 = 928997) B928997
theorem B2356067 : Blo 578813 2356067 := bstep (se 1 (by rfl) ⟨1767050, by rfl⟩ : syracuseStep 2356067 = 3534101) B3534101
theorem B979843 : Blo 578813 979843 := bstep (se 1 (by rfl) ⟨734882, by rfl⟩ : syracuseStep 979843 = 1469765) B1469765
theorem B1307537 : Blo 578813 1307537 := bstep (se 2 (by rfl) ⟨490326, by rfl⟩ : syracuseStep 1307537 = 980653) B980653
theorem B1307555 : Blo 578813 1307555 := bstep (se 1 (by rfl) ⟨980666, by rfl⟩ : syracuseStep 1307555 = 1961333) B1961333
theorem B2945969 : Blo 578813 2945969 := bstep (se 2 (by rfl) ⟨1104738, by rfl⟩ : syracuseStep 2945969 = 2209477) B2209477
theorem B1864657 : Blo 578813 1864657 := bstep (se 2 (by rfl) ⟨699246, by rfl⟩ : syracuseStep 1864657 = 1398493) B1398493
theorem B652243 : Blo 578813 652243 := bstep (se 1 (by rfl) ⟨489182, by rfl⟩ : syracuseStep 652243 = 978365) B978365
theorem B783361 : Blo 578813 783361 := bstep (se 2 (by rfl) ⟨293760, by rfl⟩ : syracuseStep 783361 = 587521) B587521
theorem B979985 : Blo 578813 979985 := bstep (se 2 (by rfl) ⟨367494, by rfl⟩ : syracuseStep 979985 = 734989) B734989
theorem B586819 : Blo 578813 586819 := bstep (se 1 (by rfl) ⟨440114, by rfl⟩ : syracuseStep 586819 = 880229) B880229
theorem B652387 : Blo 578813 652387 := bstep (se 1 (by rfl) ⟨489290, by rfl⟩ : syracuseStep 652387 = 978581) B978581
theorem B980113 : Blo 578813 980113 := bstep (se 2 (by rfl) ⟨367542, by rfl⟩ : syracuseStep 980113 = 735085) B735085
theorem B1307825 : Blo 578813 1307825 := bstep (se 2 (by rfl) ⟨490434, by rfl⟩ : syracuseStep 1307825 = 980869) B980869
theorem B980147 : Blo 578813 980147 := bstep (se 1 (by rfl) ⟨735110, by rfl⟩ : syracuseStep 980147 = 1470221) B1470221
theorem B1307843 : Blo 578813 1307843 := bstep (se 1 (by rfl) ⟨980882, by rfl⟩ : syracuseStep 1307843 = 1961765) B1961765
theorem B1471729 : Blo 578813 1471729 := bstep (se 2 (by rfl) ⟨551898, by rfl⟩ : syracuseStep 1471729 = 1103797) B1103797
theorem B1242353 : Blo 578813 1242353 := bstep (se 2 (by rfl) ⟨465882, by rfl⟩ : syracuseStep 1242353 = 931765) B931765
theorem B652531 : Blo 578813 652531 := bstep (se 1 (by rfl) ⟨489398, by rfl⟩ : syracuseStep 652531 = 978797) B978797
theorem B1242371 : Blo 578813 1242371 := bstep (se 1 (by rfl) ⟨931778, by rfl⟩ : syracuseStep 1242371 = 1863557) B1863557
theorem B1570061 : Blo 578813 1570061 := bstep (se 3 (by rfl) ⟨294386, by rfl⟩ : syracuseStep 1570061 = 588773) B588773
theorem B1963277 : Blo 578813 1963277 := bstep (se 3 (by rfl) ⟨368114, by rfl⟩ : syracuseStep 1963277 = 736229) B736229
theorem B3437873 : Blo 578813 3437873 := bstep (se 2 (by rfl) ⟨1289202, by rfl⟩ : syracuseStep 3437873 = 2578405) B2578405
theorem B3142961 : Blo 578813 3142961 := bstep (se 2 (by rfl) ⟨1178610, by rfl⟩ : syracuseStep 3142961 = 2357221) B2357221
theorem B980275 : Blo 578813 980275 := bstep (se 1 (by rfl) ⟨735206, by rfl⟩ : syracuseStep 980275 = 1470413) B1470413
theorem B1963331 : Blo 578813 1963331 := bstep (se 1 (by rfl) ⟨1472498, by rfl⟩ : syracuseStep 1963331 = 2944997) B2944997
theorem B652675 : Blo 578813 652675 := bstep (se 1 (by rfl) ⟨489506, by rfl⟩ : syracuseStep 652675 = 979013) B979013
theorem B1570211 : Blo 578813 1570211 := bstep (se 1 (by rfl) ⟨1177658, by rfl⟩ : syracuseStep 1570211 = 2355317) B2355317
theorem B980417 : Blo 578813 980417 := bstep (se 2 (by rfl) ⟨367656, by rfl⟩ : syracuseStep 980417 = 735313) B735313
theorem B1308113 : Blo 578813 1308113 := bstep (se 2 (by rfl) ⟨490542, by rfl⟩ : syracuseStep 1308113 = 981085) B981085
theorem B1308131 : Blo 578813 1308131 := bstep (se 1 (by rfl) ⟨981098, by rfl⟩ : syracuseStep 1308131 = 1962197) B1962197
theorem B1472003 : Blo 578813 1472003 := bstep (se 1 (by rfl) ⟨1104002, by rfl⟩ : syracuseStep 1472003 = 2208005) B2208005
theorem B652819 : Blo 578813 652819 := bstep (se 1 (by rfl) ⟨489614, by rfl⟩ : syracuseStep 652819 = 979229) B979229
theorem B1865261 : Blo 578813 1865261 := bstep (se 3 (by rfl) ⟨349736, by rfl⟩ : syracuseStep 1865261 = 699473) B699473
theorem B620083 : Blo 578813 620083 := bstep (se 1 (by rfl) ⟨465062, by rfl⟩ : syracuseStep 620083 = 930125) B930125
theorem B980545 : Blo 578813 980545 := bstep (se 2 (by rfl) ⟨367704, by rfl⟩ : syracuseStep 980545 = 735409) B735409
theorem B1963601 : Blo 578813 1963601 := bstep (se 2 (by rfl) ⟨736350, by rfl⟩ : syracuseStep 1963601 = 1472701) B1472701
theorem B980579 : Blo 578813 980579 := bstep (se 1 (by rfl) ⟨735434, by rfl⟩ : syracuseStep 980579 = 1470869) B1470869
theorem B652963 : Blo 578813 652963 := bstep (se 1 (by rfl) ⟨489722, by rfl⟩ : syracuseStep 652963 = 979445) B979445
theorem B1472195 : Blo 578813 1472195 := bstep (se 1 (by rfl) ⟨1104146, by rfl⟩ : syracuseStep 1472195 = 2208293) B2208293
theorem B980707 : Blo 578813 980707 := bstep (se 1 (by rfl) ⟨735530, by rfl⟩ : syracuseStep 980707 = 1471061) B1471061
theorem B1308401 : Blo 578813 1308401 := bstep (se 2 (by rfl) ⟨490650, by rfl⟩ : syracuseStep 1308401 = 981301) B981301
theorem B1308419 : Blo 578813 1308419 := bstep (se 1 (by rfl) ⟨981314, by rfl⟩ : syracuseStep 1308419 = 1962629) B1962629
theorem B653107 : Blo 578813 653107 := bstep (se 1 (by rfl) ⟨489830, by rfl⟩ : syracuseStep 653107 = 979661) B979661
theorem B980849 : Blo 578813 980849 := bstep (se 2 (by rfl) ⟨367818, by rfl⟩ : syracuseStep 980849 = 735637) B735637
theorem B653251 : Blo 578813 653251 := bstep (se 1 (by rfl) ⟨489938, by rfl⟩ : syracuseStep 653251 = 979877) B979877
theorem B980977 : Blo 578813 980977 := bstep (se 2 (by rfl) ⟨367866, by rfl⟩ : syracuseStep 980977 = 735733) B735733
theorem B2488333 : Blo 578813 2488333 := bstep (se 3 (by rfl) ⟨466562, by rfl⟩ : syracuseStep 2488333 = 933125) B933125
theorem B1308689 : Blo 578813 1308689 := bstep (se 2 (by rfl) ⟨490758, by rfl⟩ : syracuseStep 1308689 = 981517) B981517
theorem B981011 : Blo 578813 981011 := bstep (se 1 (by rfl) ⟨735758, by rfl⟩ : syracuseStep 981011 = 1471517) B1471517
theorem B1046563 : Blo 578813 1046563 := bstep (se 1 (by rfl) ⟨784922, by rfl⟩ : syracuseStep 1046563 = 1569845) B1569845
theorem B1308707 : Blo 578813 1308707 := bstep (se 1 (by rfl) ⟨981530, by rfl⟩ : syracuseStep 1308707 = 1963061) B1963061
theorem B20183093 : Blo 578813 20183093 := bstep (se 5 (by rfl) ⟨946082, by rfl⟩ : syracuseStep 20183093 = 1892165) B1892165
theorem B653395 : Blo 578813 653395 := bstep (se 1 (by rfl) ⟨490046, by rfl⟩ : syracuseStep 653395 = 980093) B980093
theorem B2357347 : Blo 578813 2357347 := bstep (se 1 (by rfl) ⟨1768010, by rfl⟩ : syracuseStep 2357347 = 3536021) B3536021
theorem B1964141 : Blo 578813 1964141 := bstep (se 3 (by rfl) ⟨368276, by rfl⟩ : syracuseStep 1964141 = 736553) B736553
theorem B4028549 : Blo 578813 4028549 := bstep (se 4 (by rfl) ⟨377676, by rfl⟩ : syracuseStep 4028549 = 755353) B755353
theorem B981139 : Blo 578813 981139 := bstep (se 1 (by rfl) ⟨735854, by rfl⟩ : syracuseStep 981139 = 1471709) B1471709
theorem B3143843 : Blo 578813 3143843 := bstep (se 1 (by rfl) ⟨2357882, by rfl⟩ : syracuseStep 3143843 = 4715765) B4715765
theorem B1964195 : Blo 578813 1964195 := bstep (se 1 (by rfl) ⟨1473146, by rfl⟩ : syracuseStep 1964195 = 2946293) B2946293
theorem B653539 : Blo 578813 653539 := bstep (se 1 (by rfl) ⟨490154, by rfl⟩ : syracuseStep 653539 = 980309) B980309
theorem B981281 : Blo 578813 981281 := bstep (se 2 (by rfl) ⟨367980, by rfl⟩ : syracuseStep 981281 = 735961) B735961
theorem B1308977 : Blo 578813 1308977 := bstep (se 2 (by rfl) ⟨490866, by rfl⟩ : syracuseStep 1308977 = 981733) B981733
theorem B1308995 : Blo 578813 1308995 := bstep (se 1 (by rfl) ⟨981746, by rfl⟩ : syracuseStep 1308995 = 1963493) B1963493
theorem B2947427 : Blo 578813 2947427 := bstep (se 1 (by rfl) ⟨2210570, by rfl⟩ : syracuseStep 2947427 = 4421141) B4421141
theorem B653683 : Blo 578813 653683 := bstep (se 1 (by rfl) ⟨490262, by rfl⟩ : syracuseStep 653683 = 980525) B980525
theorem B981409 : Blo 578813 981409 := bstep (se 2 (by rfl) ⟨368028, by rfl⟩ : syracuseStep 981409 = 736057) B736057
theorem B1210801 : Blo 578813 1210801 := bstep (se 2 (by rfl) ⟨454050, by rfl⟩ : syracuseStep 1210801 = 908101) B908101
theorem B1964465 : Blo 578813 1964465 := bstep (se 2 (by rfl) ⟨736674, by rfl⟩ : syracuseStep 1964465 = 1473349) B1473349
theorem B981443 : Blo 578813 981443 := bstep (se 1 (by rfl) ⟨736082, by rfl⟩ : syracuseStep 981443 = 1472165) B1472165
theorem B1931779 : Blo 578813 1931779 := bstep (se 1 (by rfl) ⟨1448834, by rfl⟩ : syracuseStep 1931779 = 2897669) B2897669
theorem B653827 : Blo 578813 653827 := bstep (se 1 (by rfl) ⟨490370, by rfl⟩ : syracuseStep 653827 = 980741) B980741
theorem B6289933 : Blo 578813 6289933 := bstep (se 3 (by rfl) ⟨1179362, by rfl⟩ : syracuseStep 6289933 = 2358725) B2358725
theorem B3734029 : Blo 578813 3734029 := bstep (se 3 (by rfl) ⟨700130, by rfl⟩ : syracuseStep 3734029 = 1400261) B1400261
theorem B621091 : Blo 578813 621091 := bstep (se 1 (by rfl) ⟨465818, by rfl⟩ : syracuseStep 621091 = 931637) B931637
theorem B981571 : Blo 578813 981571 := bstep (se 1 (by rfl) ⟨736178, by rfl⟩ : syracuseStep 981571 = 1472357) B1472357
theorem B1309265 : Blo 578813 1309265 := bstep (se 2 (by rfl) ⟨490974, by rfl⟩ : syracuseStep 1309265 = 981949) B981949
theorem B1309283 : Blo 578813 1309283 := bstep (se 1 (by rfl) ⟨981962, by rfl⟩ : syracuseStep 1309283 = 1963925) B1963925
theorem B26835569 : Blo 578813 26835569 := bstep (se 2 (by rfl) ⟨10063338, by rfl⟩ : syracuseStep 26835569 = 20126677) B20126677
theorem B1473137 : Blo 578813 1473137 := bstep (se 2 (by rfl) ⟨552426, by rfl⟩ : syracuseStep 1473137 = 1104853) B1104853
theorem B653971 : Blo 578813 653971 := bstep (se 1 (by rfl) ⟨490478, by rfl⟩ : syracuseStep 653971 = 980957) B980957
theorem B1473187 : Blo 578813 1473187 := bstep (se 1 (by rfl) ⟨1104890, by rfl⟩ : syracuseStep 1473187 = 2209781) B2209781
theorem B981713 : Blo 578813 981713 := bstep (se 2 (by rfl) ⟨368142, by rfl⟩ : syracuseStep 981713 = 736285) B736285
theorem B654115 : Blo 578813 654115 := bstep (se 1 (by rfl) ⟨490586, by rfl⟩ : syracuseStep 654115 = 981173) B981173
theorem B1768241 : Blo 578813 1768241 := bstep (se 2 (by rfl) ⟨663090, by rfl⟩ : syracuseStep 1768241 = 1326181) B1326181
theorem B1473329 : Blo 578813 1473329 := bstep (se 2 (by rfl) ⟨552498, by rfl⟩ : syracuseStep 1473329 = 1104997) B1104997
theorem B981841 : Blo 578813 981841 := bstep (se 2 (by rfl) ⟨368190, by rfl⟩ : syracuseStep 981841 = 736381) B736381
theorem B1309553 : Blo 578813 1309553 := bstep (se 2 (by rfl) ⟨491082, by rfl⟩ : syracuseStep 1309553 = 982165) B982165
theorem B2489201 : Blo 578813 2489201 := bstep (se 2 (by rfl) ⟨933450, by rfl⟩ : syracuseStep 2489201 = 1866901) B1866901
theorem B981875 : Blo 578813 981875 := bstep (se 1 (by rfl) ⟨736406, by rfl⟩ : syracuseStep 981875 = 1472813) B1472813
theorem B1309571 : Blo 578813 1309571 := bstep (se 1 (by rfl) ⟨982178, by rfl⟩ : syracuseStep 1309571 = 1964357) B1964357
theorem B2489251 : Blo 578813 2489251 := bstep (se 1 (by rfl) ⟨1866938, by rfl⟩ : syracuseStep 2489251 = 3733877) B3733877
theorem B654259 : Blo 578813 654259 := bstep (se 1 (by rfl) ⟨490694, by rfl⟩ : syracuseStep 654259 = 981389) B981389
theorem B1965005 : Blo 578813 1965005 := bstep (se 3 (by rfl) ⟨368438, by rfl⟩ : syracuseStep 1965005 = 736877) B736877
theorem B785377 : Blo 578813 785377 := bstep (se 2 (by rfl) ⟨294516, by rfl⟩ : syracuseStep 785377 = 589033) B589033
theorem B982003 : Blo 578813 982003 := bstep (se 1 (by rfl) ⟨736502, by rfl⟩ : syracuseStep 982003 = 1473005) B1473005
theorem B1965059 : Blo 578813 1965059 := bstep (se 1 (by rfl) ⟨1473794, by rfl⟩ : syracuseStep 1965059 = 2947589) B2947589
theorem B654403 : Blo 578813 654403 := bstep (se 1 (by rfl) ⟨490802, by rfl⟩ : syracuseStep 654403 = 981605) B981605
theorem B982145 : Blo 578813 982145 := bstep (se 2 (by rfl) ⟨368304, by rfl⟩ : syracuseStep 982145 = 736609) B736609
theorem B2948237 : Blo 578813 2948237 := bstep (se 3 (by rfl) ⟨552794, by rfl⟩ : syracuseStep 2948237 = 1105589) B1105589
theorem B1309841 : Blo 578813 1309841 := bstep (se 2 (by rfl) ⟨491190, by rfl⟩ : syracuseStep 1309841 = 982381) B982381
theorem B1309859 : Blo 578813 1309859 := bstep (se 1 (by rfl) ⟨982394, by rfl⟩ : syracuseStep 1309859 = 1964789) B1964789
theorem B1244369 : Blo 578813 1244369 := bstep (se 2 (by rfl) ⟨466638, by rfl⟩ : syracuseStep 1244369 = 933277) B933277
theorem B654547 : Blo 578813 654547 := bstep (se 1 (by rfl) ⟨490910, by rfl⟩ : syracuseStep 654547 = 981821) B981821
theorem B982273 : Blo 578813 982273 := bstep (se 2 (by rfl) ⟨368352, by rfl⟩ : syracuseStep 982273 = 736705) B736705
theorem B1965329 : Blo 578813 1965329 := bstep (se 2 (by rfl) ⟨736998, by rfl⟩ : syracuseStep 1965329 = 1473997) B1473997
theorem B982307 : Blo 578813 982307 := bstep (se 1 (by rfl) ⟨736730, by rfl⟩ : syracuseStep 982307 = 1473461) B1473461
theorem B1572173 : Blo 578813 1572173 := bstep (se 3 (by rfl) ⟨294782, by rfl⟩ : syracuseStep 1572173 = 589565) B589565
theorem B654691 : Blo 578813 654691 := bstep (se 1 (by rfl) ⟨491018, by rfl⟩ : syracuseStep 654691 = 982037) B982037
theorem B982435 : Blo 578813 982435 := bstep (se 1 (by rfl) ⟨736826, by rfl⟩ : syracuseStep 982435 = 1473653) B1473653
theorem B1310129 : Blo 578813 1310129 := bstep (se 2 (by rfl) ⟨491298, by rfl⟩ : syracuseStep 1310129 = 982597) B982597
theorem B1310147 : Blo 578813 1310147 := bstep (se 1 (by rfl) ⟨982610, by rfl⟩ : syracuseStep 1310147 = 1965221) B1965221
theorem B654835 : Blo 578813 654835 := bstep (se 1 (by rfl) ⟨491126, by rfl⟩ : syracuseStep 654835 = 982253) B982253
theorem B622099 : Blo 578813 622099 := bstep (se 1 (by rfl) ⟨466574, by rfl⟩ : syracuseStep 622099 = 933149) B933149
theorem B982577 : Blo 578813 982577 := bstep (se 2 (by rfl) ⟨368466, by rfl⟩ : syracuseStep 982577 = 736933) B736933
theorem B654979 : Blo 578813 654979 := bstep (se 1 (by rfl) ⟨491234, by rfl⟩ : syracuseStep 654979 = 982469) B982469
theorem B982705 : Blo 578813 982705 := bstep (se 2 (by rfl) ⟨368514, by rfl⟩ : syracuseStep 982705 = 737029) B737029
theorem B1310417 : Blo 578813 1310417 := bstep (se 2 (by rfl) ⟨491406, by rfl⟩ : syracuseStep 1310417 = 982813) B982813
theorem B982739 : Blo 578813 982739 := bstep (se 1 (by rfl) ⟨737054, by rfl⟩ : syracuseStep 982739 = 1474109) B1474109
theorem B1310435 : Blo 578813 1310435 := bstep (se 1 (by rfl) ⟨982826, by rfl⟩ : syracuseStep 1310435 = 1965653) B1965653
theorem B1474321 : Blo 578813 1474321 := bstep (se 2 (by rfl) ⟨552870, by rfl⟩ : syracuseStep 1474321 = 1105741) B1105741
theorem B655123 : Blo 578813 655123 := bstep (se 1 (by rfl) ⟨491342, by rfl⟩ : syracuseStep 655123 = 982685) B982685
theorem B1965869 : Blo 578813 1965869 := bstep (se 3 (by rfl) ⟨368600, by rfl⟩ : syracuseStep 1965869 = 737201) B737201
theorem B10714933 : Blo 578813 10714933 := bstep (se 5 (by rfl) ⟨502262, by rfl⟩ : syracuseStep 10714933 = 1004525) B1004525
theorem B982867 : Blo 578813 982867 := bstep (se 1 (by rfl) ⟨737150, by rfl⟩ : syracuseStep 982867 = 1474301) B1474301
theorem B1965923 : Blo 578813 1965923 := bstep (se 1 (by rfl) ⟨1474442, by rfl⟩ : syracuseStep 1965923 = 2948885) B2948885
theorem B2359181 : Blo 578813 2359181 := bstep (se 3 (by rfl) ⟨442346, by rfl⟩ : syracuseStep 2359181 = 884693) B884693
theorem B655267 : Blo 578813 655267 := bstep (se 1 (by rfl) ⟨491450, by rfl⟩ : syracuseStep 655267 = 982901) B982901
theorem B983009 : Blo 578813 983009 := bstep (se 2 (by rfl) ⟨368628, by rfl⟩ : syracuseStep 983009 = 737257) B737257
theorem B1310705 : Blo 578813 1310705 := bstep (se 2 (by rfl) ⟨491514, by rfl⟩ : syracuseStep 1310705 = 983029) B983029
theorem B983063 : Blo 578813 983063 := bstep (se 1 (by rfl) ⟨737297, by rfl⟩ : syracuseStep 983063 = 1474595) B1474595
theorem B1474625 : Blo 578813 1474625 := bstep (se 2 (by rfl) ⟨552984, by rfl⟩ : syracuseStep 1474625 = 1105969) B1105969
theorem B1310795 : Blo 578813 1310795 := bstep (se 1 (by rfl) ⟨983096, by rfl⟩ : syracuseStep 1310795 = 1966193) B1966193
theorem B655447 : Blo 578813 655447 := bstep (se 1 (by rfl) ⟨491585, by rfl⟩ : syracuseStep 655447 = 983171) B983171
theorem B1310849 : Blo 578813 1310849 := bstep (se 2 (by rfl) ⟨491568, by rfl⟩ : syracuseStep 1310849 = 983137) B983137
theorem B983191 : Blo 578813 983191 := bstep (se 1 (by rfl) ⟨737393, by rfl⟩ : syracuseStep 983191 = 1474787) B1474787
theorem B1966301 : Blo 578813 1966301 := bstep (se 3 (by rfl) ⟨368681, by rfl⟩ : syracuseStep 1966301 = 737363) B737363
theorem B655627 : Blo 578813 655627 := bstep (se 1 (by rfl) ⟨491720, by rfl⟩ : syracuseStep 655627 = 983441) B983441
theorem B1311065 : Blo 578813 1311065 := bstep (se 2 (by rfl) ⟨491649, by rfl⟩ : syracuseStep 1311065 = 983299) B983299
theorem B2097539 : Blo 578813 2097539 := bstep (se 1 (by rfl) ⟨1573154, by rfl⟩ : syracuseStep 2097539 = 3146309) B3146309
theorem B5013937 : Blo 578813 5013937 := bstep (se 2 (by rfl) ⟨1880226, by rfl⟩ : syracuseStep 5013937 = 3760453) B3760453
theorem B1311155 : Blo 578813 1311155 := bstep (se 1 (by rfl) ⟨983366, by rfl⟩ : syracuseStep 1311155 = 1966733) B1966733
theorem B1311191 : Blo 578813 1311191 := bstep (se 1 (by rfl) ⟨983393, by rfl⟩ : syracuseStep 1311191 = 1966787) B1966787
theorem B1671959 : Blo 578813 1671959 := bstep (se 1 (by rfl) ⟨1253969, by rfl⟩ : syracuseStep 1671959 = 2507939) B2507939
theorem B2360087 : Blo 578813 2360087 := bstep (se 1 (by rfl) ⟨1770065, by rfl⟩ : syracuseStep 2360087 = 3540131) B3540131
theorem B2097971 : Blo 578813 2097971 := bstep (se 1 (by rfl) ⟨1573478, by rfl⟩ : syracuseStep 2097971 = 3146957) B3146957
theorem B1409881 : Blo 578813 1409881 := bstep (se 2 (by rfl) ⟨528705, by rfl⟩ : syracuseStep 1409881 = 1057411) B1057411
theorem B2950019 : Blo 578813 2950019 := bstep (se 1 (by rfl) ⟨2212514, by rfl⟩ : syracuseStep 2950019 = 4425029) B4425029
theorem B3311027 : Blo 578813 3311027 := bstep (se 1 (by rfl) ⟨2483270, by rfl⟩ : syracuseStep 3311027 = 4966541) B4966541
theorem B120620501 : Blo 578813 120620501 := bstep (se 7 (by rfl) ⟨1413521, by rfl⟩ : syracuseStep 120620501 = 2827043) B2827043
theorem B2098649 : Blo 578813 2098649 := bstep (se 2 (by rfl) ⟨786993, by rfl⟩ : syracuseStep 2098649 = 1573987) B1573987
theorem B1574603 : Blo 578813 1574603 := bstep (se 1 (by rfl) ⟨1180952, by rfl⟩ : syracuseStep 1574603 = 2361905) B2361905
theorem B1345921 : Blo 578813 1345921 := bstep (se 2 (by rfl) ⟨504720, by rfl⟩ : syracuseStep 1345921 = 1009441) B1009441
theorem B3312485 : Blo 578813 3312485 := bstep (se 4 (by rfl) ⟨310545, by rfl⟩ : syracuseStep 3312485 = 621091) B621091
theorem B2198573 : Blo 578813 2198573 := bstep (se 3 (by rfl) ⟨412232, by rfl⟩ : syracuseStep 2198573 = 824465) B824465
theorem B2198603 : Blo 578813 2198603 := bstep (se 1 (by rfl) ⟨1648952, by rfl⟩ : syracuseStep 2198603 = 3297905) B3297905
theorem B2788759 : Blo 578813 2788759 := bstep (se 1 (by rfl) ⟨2091569, by rfl⟩ : syracuseStep 2788759 = 4183139) B4183139
theorem B3313169 : Blo 578813 3313169 := bstep (se 2 (by rfl) ⟨1242438, by rfl⟩ : syracuseStep 3313169 = 2484877) B2484877
theorem B2199257 : Blo 578813 2199257 := bstep (se 2 (by rfl) ⟨824721, by rfl⟩ : syracuseStep 2199257 = 1649443) B1649443
theorem B2199575 : Blo 578813 2199575 := bstep (se 1 (by rfl) ⟨1649681, by rfl⟩ : syracuseStep 2199575 = 3299363) B3299363
theorem B627211 : Blo 578813 627211 := bstep (se 1 (by rfl) ⟨470408, by rfl⟩ : syracuseStep 627211 = 940817) B940817
theorem B2200243 : Blo 578813 2200243 := bstep (se 1 (by rfl) ⟨1650182, by rfl⟩ : syracuseStep 2200243 = 3300365) B3300365
theorem B21205745 : Blo 578813 21205745 := bstep (se 2 (by rfl) ⟨7952154, by rfl⟩ : syracuseStep 21205745 = 15904309) B15904309
theorem B4395869 : Blo 578813 4395869 := bstep (se 3 (by rfl) ⟨824225, by rfl⟩ : syracuseStep 4395869 = 1648451) B1648451
theorem B824203 : Blo 578813 824203 := bstep (se 1 (by rfl) ⟨618152, by rfl⟩ : syracuseStep 824203 = 1236305) B1236305
theorem B4953419 : Blo 578813 4953419 := bstep (se 1 (by rfl) ⟨3715064, by rfl⟩ : syracuseStep 4953419 = 7430129) B7430129
theorem B2201489 : Blo 578813 2201489 := bstep (se 2 (by rfl) ⟨825558, by rfl⟩ : syracuseStep 2201489 = 1651117) B1651117
theorem B1120243 : Blo 578813 1120243 := bstep (se 1 (by rfl) ⟨840182, by rfl⟩ : syracuseStep 1120243 = 1680365) B1680365
theorem B9443459 : Blo 578813 9443459 := bstep (se 1 (by rfl) ⟨7082594, by rfl⟩ : syracuseStep 9443459 = 14165189) B14165189
theorem B825547 : Blo 578813 825547 := bstep (se 1 (by rfl) ⟨619160, by rfl⟩ : syracuseStep 825547 = 1238321) B1238321
theorem B21174533 : Blo 578813 21174533 := bstep (se 4 (by rfl) ⟨1985112, by rfl⟩ : syracuseStep 21174533 = 3970225) B3970225
theorem B8395109 : Blo 578813 8395109 := bstep (se 4 (by rfl) ⟨787041, by rfl⟩ : syracuseStep 8395109 = 1574083) B1574083
theorem B1415627 : Blo 578813 1415627 := bstep (se 1 (by rfl) ⟨1061720, by rfl⟩ : syracuseStep 1415627 = 2123441) B2123441
theorem B825815 : Blo 578813 825815 := bstep (se 1 (by rfl) ⟨619361, by rfl⟩ : syracuseStep 825815 = 1238723) B1238723
theorem B2202187 : Blo 578813 2202187 := bstep (se 1 (by rfl) ⟨1651640, by rfl⟩ : syracuseStep 2202187 = 3303281) B3303281
theorem B5380739 : Blo 578813 5380739 := bstep (se 1 (by rfl) ⟨4035554, by rfl⟩ : syracuseStep 5380739 = 8071109) B8071109
theorem B3316403 : Blo 578813 3316403 := bstep (se 1 (by rfl) ⟨2487302, by rfl⟩ : syracuseStep 3316403 = 4974605) B4974605
theorem B2202461 : Blo 578813 2202461 := bstep (se 3 (by rfl) ⟨412961, by rfl⟩ : syracuseStep 2202461 = 825923) B825923
theorem B826777 : Blo 578813 826777 := bstep (se 2 (by rfl) ⟨310041, by rfl⟩ : syracuseStep 826777 = 620083) B620083
theorem B2203159 : Blo 578813 2203159 := bstep (se 1 (by rfl) ⟨1652369, by rfl⟩ : syracuseStep 2203159 = 3304739) B3304739
theorem B2236177 : Blo 578813 2236177 := bstep (se 2 (by rfl) ⟨838566, by rfl⟩ : syracuseStep 2236177 = 1677133) B1677133
theorem B663319 : Blo 578813 663319 := bstep (se 1 (by rfl) ⟨497489, by rfl⟩ : syracuseStep 663319 = 994979) B994979
theorem B3317777 : Blo 578813 3317777 := bstep (se 2 (by rfl) ⟨1244166, by rfl⟩ : syracuseStep 3317777 = 2488333) B2488333
theorem B4464715 : Blo 578813 4464715 := bstep (se 1 (by rfl) ⟨3348536, by rfl⟩ : syracuseStep 4464715 = 6697073) B6697073
theorem B3317861 : Blo 578813 3317861 := bstep (se 4 (by rfl) ⟨311049, by rfl⟩ : syracuseStep 3317861 = 622099) B622099
theorem B2203949 : Blo 578813 2203949 := bstep (se 3 (by rfl) ⟨413240, by rfl⟩ : syracuseStep 2203949 = 826481) B826481
theorem B3318317 : Blo 578813 3318317 := bstep (se 3 (by rfl) ⟨622184, by rfl⟩ : syracuseStep 3318317 = 1244369) B1244369
theorem B77537845 : Blo 578813 77537845 := bstep (se 5 (by rfl) ⟨3634586, by rfl⟩ : syracuseStep 77537845 = 7269173) B7269173
theorem B1614401 : Blo 578813 1614401 := bstep (se 2 (by rfl) ⟨605400, by rfl⟩ : syracuseStep 1614401 = 1210801) B1210801
theorem B3711581 : Blo 578813 3711581 := bstep (se 3 (by rfl) ⟨695921, by rfl⟩ : syracuseStep 3711581 = 1391843) B1391843
theorem B828235 : Blo 578813 828235 := bstep (se 1 (by rfl) ⟨621176, by rfl⟩ : syracuseStep 828235 = 1242353) B1242353
theorem B828247 : Blo 578813 828247 := bstep (se 1 (by rfl) ⟨621185, by rfl⟩ : syracuseStep 828247 = 1242371) B1242371
theorem B3319001 : Blo 578813 3319001 := bstep (se 2 (by rfl) ⟨1244625, by rfl⟩ : syracuseStep 3319001 = 2489251) B2489251
theorem B8955485 : Blo 578813 8955485 := bstep (se 3 (by rfl) ⟨1679153, by rfl⟩ : syracuseStep 8955485 = 3358307) B3358307
theorem B2205377 : Blo 578813 2205377 := bstep (se 2 (by rfl) ⟨827016, by rfl⟩ : syracuseStep 2205377 = 1654033) B1654033
theorem B1649089 : Blo 578813 1649089 := bstep (se 2 (by rfl) ⟨618408, by rfl⟩ : syracuseStep 1649089 = 1236817) B1236817
theorem B928279 : Blo 578813 928279 := bstep (se 1 (by rfl) ⟨696209, by rfl⟩ : syracuseStep 928279 = 1392419) B1392419
theorem B928331 : Blo 578813 928331 := bstep (se 1 (by rfl) ⟨696248, by rfl⟩ : syracuseStep 928331 = 1392497) B1392497
theorem B928459 : Blo 578813 928459 := bstep (se 1 (by rfl) ⟨696344, by rfl⟩ : syracuseStep 928459 = 1392689) B1392689
theorem B1288921 : Blo 578813 1288921 := bstep (se 2 (by rfl) ⟨483345, by rfl⟩ : syracuseStep 1288921 = 966691) B966691
theorem B2796353 : Blo 578813 2796353 := bstep (se 2 (by rfl) ⟨1048632, by rfl⟩ : syracuseStep 2796353 = 2097265) B2097265
theorem B5581669 : Blo 578813 5581669 := bstep (se 4 (by rfl) ⟨523281, by rfl⟩ : syracuseStep 5581669 = 1046563) B1046563
theorem B1485899 : Blo 578813 1485899 := bstep (se 1 (by rfl) ⟨1114424, by rfl⟩ : syracuseStep 1485899 = 2228849) B2228849
theorem B2206865 : Blo 578813 2206865 := bstep (se 2 (by rfl) ⟨827574, by rfl⟩ : syracuseStep 2206865 = 1655149) B1655149
theorem B3714605 : Blo 578813 3714605 := bstep (se 3 (by rfl) ⟨696488, by rfl⟩ : syracuseStep 3714605 = 1392977) B1392977
theorem B929369 : Blo 578813 929369 := bstep (se 2 (by rfl) ⟨348513, by rfl⟩ : syracuseStep 929369 = 697027) B697027
theorem B2207321 : Blo 578813 2207321 := bstep (se 2 (by rfl) ⟨827745, by rfl⟩ : syracuseStep 2207321 = 1655491) B1655491
theorem B2207533 : Blo 578813 2207533 := bstep (se 3 (by rfl) ⟨413912, by rfl⟩ : syracuseStep 2207533 = 827825) B827825
theorem B733207 : Blo 578813 733207 := bstep (se 1 (by rfl) ⟨549905, by rfl⟩ : syracuseStep 733207 = 1099811) B1099811
theorem B2207837 : Blo 578813 2207837 := bstep (se 3 (by rfl) ⟨413969, by rfl⟩ : syracuseStep 2207837 = 827939) B827939
theorem B4174949 : Blo 578813 4174949 := bstep (se 4 (by rfl) ⟨391401, by rfl⟩ : syracuseStep 4174949 = 782803) B782803
theorem B10302821 : Blo 578813 10302821 := bstep (se 4 (by rfl) ⟨965889, by rfl⟩ : syracuseStep 10302821 = 1931779) B1931779
theorem B734923 : Blo 578813 734923 := bstep (se 1 (by rfl) ⟨551192, by rfl⟩ : syracuseStep 734923 = 1102385) B1102385
theorem B5027789 : Blo 578813 5027789 := bstep (se 3 (by rfl) ⟨942710, by rfl⟩ : syracuseStep 5027789 = 1885421) B1885421
theorem B1259507 : Blo 578813 1259507 := bstep (se 1 (by rfl) ⟨944630, by rfl⟩ : syracuseStep 1259507 = 1889261) B1889261
theorem B1652825 : Blo 578813 1652825 := bstep (se 2 (by rfl) ⟨619809, by rfl⟩ : syracuseStep 1652825 = 1239619) B1239619
theorem B8927587 : Blo 578813 8927587 := bstep (se 1 (by rfl) ⟨6695690, by rfl⟩ : syracuseStep 8927587 = 13391381) B13391381
theorem B2210435 : Blo 578813 2210435 := bstep (se 1 (by rfl) ⟨1657826, by rfl⟩ : syracuseStep 2210435 = 3315653) B3315653
theorem B2210449 : Blo 578813 2210449 := bstep (se 2 (by rfl) ⟨828918, by rfl⟩ : syracuseStep 2210449 = 1657837) B1657837
theorem B735895 : Blo 578813 735895 := bstep (se 1 (by rfl) ⟨551921, by rfl⟩ : syracuseStep 735895 = 1103843) B1103843
theorem B1391411 : Blo 578813 1391411 := bstep (se 1 (by rfl) ⟨1043558, by rfl⟩ : syracuseStep 1391411 = 2087117) B2087117
theorem B2210753 : Blo 578813 2210753 := bstep (se 2 (by rfl) ⟨829032, by rfl⟩ : syracuseStep 2210753 = 1658065) B1658065
theorem B932887 : Blo 578813 932887 := bstep (se 1 (by rfl) ⟨699665, by rfl⟩ : syracuseStep 932887 = 1399331) B1399331
theorem B1489985 : Blo 578813 1489985 := bstep (se 2 (by rfl) ⟨558744, by rfl⟩ : syracuseStep 1489985 = 1117489) B1117489
theorem B12729419 : Blo 578813 12729419 := bstep (se 1 (by rfl) ⟨9547064, by rfl⟩ : syracuseStep 12729419 = 19094129) B19094129
theorem B3718295 : Blo 578813 3718295 := bstep (se 1 (by rfl) ⟨2788721, by rfl⟩ : syracuseStep 3718295 = 5577443) B5577443
theorem B1654091 : Blo 578813 1654091 := bstep (se 1 (by rfl) ⟨1240568, by rfl⟩ : syracuseStep 1654091 = 2481137) B2481137
theorem B2473361 : Blo 578813 2473361 := bstep (se 2 (by rfl) ⟨927510, by rfl⟩ : syracuseStep 2473361 = 1855021) B1855021
theorem B736715 : Blo 578813 736715 := bstep (se 1 (by rfl) ⟨552536, by rfl⟩ : syracuseStep 736715 = 1105073) B1105073
theorem B1326593 : Blo 578813 1326593 := bstep (se 2 (by rfl) ⟨497472, by rfl⟩ : syracuseStep 1326593 = 994945) B994945
theorem B2211421 : Blo 578813 2211421 := bstep (se 3 (by rfl) ⟨414641, by rfl⟩ : syracuseStep 2211421 = 829283) B829283
theorem B43106147 : Blo 578813 43106147 := bstep (se 1 (by rfl) ⟨32329610, by rfl⟩ : syracuseStep 43106147 = 64659221) B64659221
theorem B868235 : Blo 578813 868235 := bstep (se 1 (by rfl) ⟨651176, by rfl⟩ : syracuseStep 868235 = 1302353) B1302353
theorem B868247 : Blo 578813 868247 := bstep (se 1 (by rfl) ⟨651185, by rfl⟩ : syracuseStep 868247 = 1302371) B1302371
theorem B868313 : Blo 578813 868313 := bstep (se 2 (by rfl) ⟨325617, by rfl⟩ : syracuseStep 868313 = 651235) B651235
theorem B868427 : Blo 578813 868427 := bstep (se 1 (by rfl) ⟨651320, by rfl⟩ : syracuseStep 868427 = 1302641) B1302641
theorem B7061579 : Blo 578813 7061579 := bstep (se 1 (by rfl) ⟨5296184, by rfl⟩ : syracuseStep 7061579 = 10592369) B10592369
theorem B868439 : Blo 578813 868439 := bstep (se 1 (by rfl) ⟨651329, by rfl⟩ : syracuseStep 868439 = 1302659) B1302659
theorem B737419 : Blo 578813 737419 := bstep (se 1 (by rfl) ⟨553064, by rfl⟩ : syracuseStep 737419 = 1106129) B1106129
theorem B868505 : Blo 578813 868505 := bstep (se 2 (by rfl) ⟨325689, by rfl⟩ : syracuseStep 868505 = 651379) B651379
theorem B868619 : Blo 578813 868619 := bstep (se 1 (by rfl) ⟨651464, by rfl⟩ : syracuseStep 868619 = 1302929) B1302929
theorem B2933009 : Blo 578813 2933009 := bstep (se 2 (by rfl) ⟨1099878, by rfl⟩ : syracuseStep 2933009 = 2199757) B2199757
theorem B868631 : Blo 578813 868631 := bstep (se 1 (by rfl) ⟨651473, by rfl⟩ : syracuseStep 868631 = 1302947) B1302947
theorem B4702529 : Blo 578813 4702529 := bstep (se 2 (by rfl) ⟨1763448, by rfl⟩ : syracuseStep 4702529 = 3526897) B3526897
theorem B868697 : Blo 578813 868697 := bstep (se 2 (by rfl) ⟨325761, by rfl⟩ : syracuseStep 868697 = 651523) B651523
theorem B2933171 : Blo 578813 2933171 := bstep (se 1 (by rfl) ⟨2199878, by rfl⟩ : syracuseStep 2933171 = 4399757) B4399757
theorem B868811 : Blo 578813 868811 := bstep (se 1 (by rfl) ⟨651608, by rfl⟩ : syracuseStep 868811 = 1303217) B1303217
theorem B868823 : Blo 578813 868823 := bstep (se 1 (by rfl) ⟨651617, by rfl⟩ : syracuseStep 868823 = 1303235) B1303235
theorem B6603281 : Blo 578813 6603281 := bstep (se 2 (by rfl) ⟨2476230, by rfl⟩ : syracuseStep 6603281 = 4952461) B4952461
theorem B868889 : Blo 578813 868889 := bstep (se 2 (by rfl) ⟨325833, by rfl⟩ : syracuseStep 868889 = 651667) B651667
theorem B869003 : Blo 578813 869003 := bstep (se 1 (by rfl) ⟨651752, by rfl⟩ : syracuseStep 869003 = 1303505) B1303505
theorem B869015 : Blo 578813 869015 := bstep (se 1 (by rfl) ⟨651761, by rfl⟩ : syracuseStep 869015 = 1303523) B1303523
theorem B869081 : Blo 578813 869081 := bstep (se 2 (by rfl) ⟨325905, by rfl⟩ : syracuseStep 869081 = 651811) B651811
theorem B869195 : Blo 578813 869195 := bstep (se 1 (by rfl) ⟨651896, by rfl⟩ : syracuseStep 869195 = 1303793) B1303793
theorem B869207 : Blo 578813 869207 := bstep (se 1 (by rfl) ⟨651905, by rfl⟩ : syracuseStep 869207 = 1303811) B1303811
theorem B2212697 : Blo 578813 2212697 := bstep (se 2 (by rfl) ⟨829761, by rfl⟩ : syracuseStep 2212697 = 1659523) B1659523
theorem B869273 : Blo 578813 869273 := bstep (se 2 (by rfl) ⟨325977, by rfl⟩ : syracuseStep 869273 = 651955) B651955
theorem B869387 : Blo 578813 869387 := bstep (se 1 (by rfl) ⟨652040, by rfl⟩ : syracuseStep 869387 = 1304081) B1304081
theorem B869399 : Blo 578813 869399 := bstep (se 1 (by rfl) ⟨652049, by rfl⟩ : syracuseStep 869399 = 1304099) B1304099
theorem B869465 : Blo 578813 869465 := bstep (se 2 (by rfl) ⟨326049, by rfl⟩ : syracuseStep 869465 = 652099) B652099
theorem B3720293 : Blo 578813 3720293 := bstep (se 4 (by rfl) ⟨348777, by rfl⟩ : syracuseStep 3720293 = 697555) B697555
theorem B869579 : Blo 578813 869579 := bstep (se 1 (by rfl) ⟨652184, by rfl⟩ : syracuseStep 869579 = 1304369) B1304369
theorem B869591 : Blo 578813 869591 := bstep (se 1 (by rfl) ⟨652193, by rfl⟩ : syracuseStep 869591 = 1304387) B1304387
theorem B1328345 : Blo 578813 1328345 := bstep (se 2 (by rfl) ⟨498129, by rfl⟩ : syracuseStep 1328345 = 996259) B996259
theorem B869657 : Blo 578813 869657 := bstep (se 2 (by rfl) ⟨326121, by rfl⟩ : syracuseStep 869657 = 652243) B652243
theorem B9684269 : Blo 578813 9684269 := bstep (se 3 (by rfl) ⟨1815800, by rfl⟩ : syracuseStep 9684269 = 3631601) B3631601
theorem B869771 : Blo 578813 869771 := bstep (se 1 (by rfl) ⟨652328, by rfl⟩ : syracuseStep 869771 = 1304657) B1304657
theorem B869783 : Blo 578813 869783 := bstep (se 1 (by rfl) ⟨652337, by rfl⟩ : syracuseStep 869783 = 1304675) B1304675
theorem B869849 : Blo 578813 869849 := bstep (se 2 (by rfl) ⟨326193, by rfl⟩ : syracuseStep 869849 = 652387) B652387
theorem B869963 : Blo 578813 869963 := bstep (se 1 (by rfl) ⟨652472, by rfl⟩ : syracuseStep 869963 = 1304945) B1304945
theorem B869975 : Blo 578813 869975 := bstep (se 1 (by rfl) ⟨652481, by rfl⟩ : syracuseStep 869975 = 1304963) B1304963
theorem B1328791 : Blo 578813 1328791 := bstep (se 1 (by rfl) ⟨996593, by rfl⟩ : syracuseStep 1328791 = 1993187) B1993187
theorem B870041 : Blo 578813 870041 := bstep (se 2 (by rfl) ⟨326265, by rfl⟩ : syracuseStep 870041 = 652531) B652531
theorem B1492673 : Blo 578813 1492673 := bstep (se 2 (by rfl) ⟨559752, by rfl⟩ : syracuseStep 1492673 = 1119505) B1119505
theorem B1099507 : Blo 578813 1099507 := bstep (se 1 (by rfl) ⟨824630, by rfl⟩ : syracuseStep 1099507 = 1649261) B1649261
theorem B870155 : Blo 578813 870155 := bstep (se 1 (by rfl) ⟨652616, by rfl⟩ : syracuseStep 870155 = 1305233) B1305233
theorem B870167 : Blo 578813 870167 := bstep (se 1 (by rfl) ⟨652625, by rfl⟩ : syracuseStep 870167 = 1305251) B1305251
theorem B2475821 : Blo 578813 2475821 := bstep (se 3 (by rfl) ⟨464216, by rfl⟩ : syracuseStep 2475821 = 928433) B928433
theorem B870233 : Blo 578813 870233 := bstep (se 2 (by rfl) ⟨326337, by rfl⟩ : syracuseStep 870233 = 652675) B652675
theorem B870347 : Blo 578813 870347 := bstep (se 1 (by rfl) ⟨652760, by rfl⟩ : syracuseStep 870347 = 1305521) B1305521
theorem B870359 : Blo 578813 870359 := bstep (se 1 (by rfl) ⟨652769, by rfl⟩ : syracuseStep 870359 = 1305539) B1305539
theorem B870425 : Blo 578813 870425 := bstep (se 2 (by rfl) ⟨326409, by rfl⟩ : syracuseStep 870425 = 652819) B652819
theorem B2476163 : Blo 578813 2476163 := bstep (se 1 (by rfl) ⟨1857122, by rfl⟩ : syracuseStep 2476163 = 3714245) B3714245
theorem B870539 : Blo 578813 870539 := bstep (se 1 (by rfl) ⟨652904, by rfl⟩ : syracuseStep 870539 = 1305809) B1305809
theorem B870551 : Blo 578813 870551 := bstep (se 1 (by rfl) ⟨652913, by rfl⟩ : syracuseStep 870551 = 1305827) B1305827
theorem B4475057 : Blo 578813 4475057 := bstep (se 2 (by rfl) ⟨1678146, by rfl⟩ : syracuseStep 4475057 = 3356293) B3356293
theorem B1099955 : Blo 578813 1099955 := bstep (se 1 (by rfl) ⟨824966, by rfl⟩ : syracuseStep 1099955 = 1649933) B1649933
theorem B1099993 : Blo 578813 1099993 := bstep (se 2 (by rfl) ⟨412497, by rfl⟩ : syracuseStep 1099993 = 824995) B824995
theorem B870617 : Blo 578813 870617 := bstep (se 2 (by rfl) ⟨326481, by rfl⟩ : syracuseStep 870617 = 652963) B652963
theorem B1394995 : Blo 578813 1394995 := bstep (se 1 (by rfl) ⟨1046246, by rfl⟩ : syracuseStep 1394995 = 2092493) B2092493
theorem B2935115 : Blo 578813 2935115 := bstep (se 1 (by rfl) ⟨2201336, by rfl⟩ : syracuseStep 2935115 = 4402673) B4402673
theorem B870731 : Blo 578813 870731 := bstep (se 1 (by rfl) ⟨653048, by rfl⟩ : syracuseStep 870731 = 1306097) B1306097
theorem B870743 : Blo 578813 870743 := bstep (se 1 (by rfl) ⟨653057, by rfl⟩ : syracuseStep 870743 = 1306115) B1306115
theorem B870809 : Blo 578813 870809 := bstep (se 2 (by rfl) ⟨326553, by rfl⟩ : syracuseStep 870809 = 653107) B653107
theorem B870923 : Blo 578813 870923 := bstep (se 1 (by rfl) ⟨653192, by rfl⟩ : syracuseStep 870923 = 1306385) B1306385
theorem B870935 : Blo 578813 870935 := bstep (se 1 (by rfl) ⟨653201, by rfl⟩ : syracuseStep 870935 = 1306403) B1306403
theorem B871001 : Blo 578813 871001 := bstep (se 2 (by rfl) ⟨326625, by rfl⟩ : syracuseStep 871001 = 653251) B653251
theorem B1100441 : Blo 578813 1100441 := bstep (se 2 (by rfl) ⟨412665, by rfl⟩ : syracuseStep 1100441 = 825331) B825331
theorem B871115 : Blo 578813 871115 := bstep (se 1 (by rfl) ⟨653336, by rfl⟩ : syracuseStep 871115 = 1306673) B1306673
theorem B871127 : Blo 578813 871127 := bstep (se 1 (by rfl) ⟨653345, by rfl⟩ : syracuseStep 871127 = 1306691) B1306691
theorem B871193 : Blo 578813 871193 := bstep (se 2 (by rfl) ⟨326697, by rfl⟩ : syracuseStep 871193 = 653395) B653395
theorem B871307 : Blo 578813 871307 := bstep (se 1 (by rfl) ⟨653480, by rfl⟩ : syracuseStep 871307 = 1306961) B1306961
theorem B871319 : Blo 578813 871319 := bstep (se 1 (by rfl) ⟨653489, by rfl⟩ : syracuseStep 871319 = 1306979) B1306979
theorem B871385 : Blo 578813 871385 := bstep (se 2 (by rfl) ⟨326769, by rfl⟩ : syracuseStep 871385 = 653539) B653539
theorem B871499 : Blo 578813 871499 := bstep (se 1 (by rfl) ⟨653624, by rfl⟩ : syracuseStep 871499 = 1307249) B1307249
theorem B871511 : Blo 578813 871511 := bstep (se 1 (by rfl) ⟨653633, by rfl⟩ : syracuseStep 871511 = 1307267) B1307267
theorem B871577 : Blo 578813 871577 := bstep (se 2 (by rfl) ⟨326841, by rfl⟩ : syracuseStep 871577 = 653683) B653683
theorem B871691 : Blo 578813 871691 := bstep (se 1 (by rfl) ⟨653768, by rfl⟩ : syracuseStep 871691 = 1307537) B1307537
theorem B871703 : Blo 578813 871703 := bstep (se 1 (by rfl) ⟨653777, by rfl⟩ : syracuseStep 871703 = 1307555) B1307555
theorem B871769 : Blo 578813 871769 := bstep (se 2 (by rfl) ⟨326913, by rfl⟩ : syracuseStep 871769 = 653827) B653827
theorem B6606197 : Blo 578813 6606197 := bstep (se 5 (by rfl) ⟨309665, by rfl⟩ : syracuseStep 6606197 = 619331) B619331
theorem B1101185 : Blo 578813 1101185 := bstep (se 2 (by rfl) ⟨412944, by rfl⟩ : syracuseStep 1101185 = 825889) B825889
theorem B871883 : Blo 578813 871883 := bstep (se 1 (by rfl) ⟨653912, by rfl⟩ : syracuseStep 871883 = 1307825) B1307825
theorem B871895 : Blo 578813 871895 := bstep (se 1 (by rfl) ⟨653921, by rfl⟩ : syracuseStep 871895 = 1307843) B1307843
theorem B871961 : Blo 578813 871961 := bstep (se 2 (by rfl) ⟨326985, by rfl⟩ : syracuseStep 871961 = 653971) B653971
theorem B1101451 : Blo 578813 1101451 := bstep (se 1 (by rfl) ⟨826088, by rfl⟩ : syracuseStep 1101451 = 1652177) B1652177
theorem B872075 : Blo 578813 872075 := bstep (se 1 (by rfl) ⟨654056, by rfl⟩ : syracuseStep 872075 = 1308113) B1308113
theorem B872087 : Blo 578813 872087 := bstep (se 1 (by rfl) ⟨654065, by rfl⟩ : syracuseStep 872087 = 1308131) B1308131
theorem B872153 : Blo 578813 872153 := bstep (se 2 (by rfl) ⟨327057, by rfl⟩ : syracuseStep 872153 = 654115) B654115
theorem B1953611 : Blo 578813 1953611 := bstep (se 1 (by rfl) ⟨1465208, by rfl⟩ : syracuseStep 1953611 = 2930417) B2930417
theorem B872267 : Blo 578813 872267 := bstep (se 1 (by rfl) ⟨654200, by rfl⟩ : syracuseStep 872267 = 1308401) B1308401
theorem B872279 : Blo 578813 872279 := bstep (se 1 (by rfl) ⟨654209, by rfl⟩ : syracuseStep 872279 = 1308419) B1308419
theorem B872345 : Blo 578813 872345 := bstep (se 2 (by rfl) ⟨327129, by rfl⟩ : syracuseStep 872345 = 654259) B654259
theorem B872459 : Blo 578813 872459 := bstep (se 1 (by rfl) ⟨654344, by rfl⟩ : syracuseStep 872459 = 1308689) B1308689
theorem B872471 : Blo 578813 872471 := bstep (se 1 (by rfl) ⟨654353, by rfl⟩ : syracuseStep 872471 = 1308707) B1308707
theorem B13455395 : Blo 578813 13455395 := bstep (se 1 (by rfl) ⟨10091546, by rfl⟩ : syracuseStep 13455395 = 20183093) B20183093
theorem B2936897 : Blo 578813 2936897 := bstep (se 2 (by rfl) ⟨1101336, by rfl⟩ : syracuseStep 2936897 = 2202673) B2202673
theorem B10047557 : Blo 578813 10047557 := bstep (se 4 (by rfl) ⟨941958, by rfl⟩ : syracuseStep 10047557 = 1883917) B1883917
theorem B1101899 : Blo 578813 1101899 := bstep (se 1 (by rfl) ⟨826424, by rfl⟩ : syracuseStep 1101899 = 1652849) B1652849
theorem B1953881 : Blo 578813 1953881 := bstep (se 2 (by rfl) ⟨732705, by rfl⟩ : syracuseStep 1953881 = 1465411) B1465411
theorem B872537 : Blo 578813 872537 := bstep (se 2 (by rfl) ⟨327201, by rfl⟩ : syracuseStep 872537 = 654403) B654403
theorem B872651 : Blo 578813 872651 := bstep (se 1 (by rfl) ⟨654488, by rfl⟩ : syracuseStep 872651 = 1308977) B1308977
theorem B872663 : Blo 578813 872663 := bstep (se 1 (by rfl) ⟨654497, by rfl⟩ : syracuseStep 872663 = 1308995) B1308995
theorem B1102081 : Blo 578813 1102081 := bstep (se 2 (by rfl) ⟨413280, by rfl⟩ : syracuseStep 1102081 = 826561) B826561
theorem B872729 : Blo 578813 872729 := bstep (se 2 (by rfl) ⟨327273, by rfl⟩ : syracuseStep 872729 = 654547) B654547
theorem B872843 : Blo 578813 872843 := bstep (se 1 (by rfl) ⟨654632, by rfl⟩ : syracuseStep 872843 = 1309265) B1309265
theorem B872855 : Blo 578813 872855 := bstep (se 1 (by rfl) ⟨654641, by rfl⟩ : syracuseStep 872855 = 1309283) B1309283
theorem B2478539 : Blo 578813 2478539 := bstep (se 1 (by rfl) ⟨1858904, by rfl⟩ : syracuseStep 2478539 = 3717809) B3717809
theorem B872921 : Blo 578813 872921 := bstep (se 2 (by rfl) ⟨327345, by rfl⟩ : syracuseStep 872921 = 654691) B654691
theorem B873035 : Blo 578813 873035 := bstep (se 1 (by rfl) ⟨654776, by rfl⟩ : syracuseStep 873035 = 1309553) B1309553
theorem B1659467 : Blo 578813 1659467 := bstep (se 1 (by rfl) ⟨1244600, by rfl⟩ : syracuseStep 1659467 = 2489201) B2489201
theorem B1102423 : Blo 578813 1102423 := bstep (se 1 (by rfl) ⟨826817, by rfl⟩ : syracuseStep 1102423 = 1653635) B1653635
theorem B873047 : Blo 578813 873047 := bstep (se 1 (by rfl) ⟨654785, by rfl⟩ : syracuseStep 873047 = 1309571) B1309571
theorem B873113 : Blo 578813 873113 := bstep (se 2 (by rfl) ⟨327417, by rfl⟩ : syracuseStep 873113 = 654835) B654835
theorem B2347699 : Blo 578813 2347699 := bstep (se 1 (by rfl) ⟨1760774, by rfl⟩ : syracuseStep 2347699 = 3521549) B3521549
theorem B873227 : Blo 578813 873227 := bstep (se 1 (by rfl) ⟨654920, by rfl⟩ : syracuseStep 873227 = 1309841) B1309841
theorem B1954583 : Blo 578813 1954583 := bstep (se 1 (by rfl) ⟨1465937, by rfl⟩ : syracuseStep 1954583 = 2931875) B2931875
theorem B873239 : Blo 578813 873239 := bstep (se 1 (by rfl) ⟨654929, by rfl⟩ : syracuseStep 873239 = 1309859) B1309859
theorem B1102643 : Blo 578813 1102643 := bstep (se 1 (by rfl) ⟨826982, by rfl⟩ : syracuseStep 1102643 = 1653965) B1653965
theorem B873305 : Blo 578813 873305 := bstep (se 2 (by rfl) ⟨327489, by rfl⟩ : syracuseStep 873305 = 654979) B654979
theorem B873419 : Blo 578813 873419 := bstep (se 1 (by rfl) ⟨655064, by rfl⟩ : syracuseStep 873419 = 1310129) B1310129
theorem B873431 : Blo 578813 873431 := bstep (se 1 (by rfl) ⟨655073, by rfl⟩ : syracuseStep 873431 = 1310147) B1310147
theorem B1102871 : Blo 578813 1102871 := bstep (se 1 (by rfl) ⟨827153, by rfl⟩ : syracuseStep 1102871 = 1654307) B1654307
theorem B873497 : Blo 578813 873497 := bstep (se 2 (by rfl) ⟨327561, by rfl⟩ : syracuseStep 873497 = 655123) B655123
theorem B1365017 : Blo 578813 1365017 := bstep (se 2 (by rfl) ⟨511881, by rfl⟩ : syracuseStep 1365017 = 1023763) B1023763
theorem B873611 : Blo 578813 873611 := bstep (se 1 (by rfl) ⟨655208, by rfl⟩ : syracuseStep 873611 = 1310417) B1310417
theorem B873623 : Blo 578813 873623 := bstep (se 1 (by rfl) ⟨655217, by rfl⟩ : syracuseStep 873623 = 1310435) B1310435
theorem B2086091 : Blo 578813 2086091 := bstep (se 1 (by rfl) ⟨1564568, by rfl⟩ : syracuseStep 2086091 = 3129137) B3129137
theorem B873689 : Blo 578813 873689 := bstep (se 2 (by rfl) ⟨327633, by rfl⟩ : syracuseStep 873689 = 655267) B655267
theorem B578827 : Blo 578813 578827 := bstep (se 1 (by rfl) ⟨434120, by rfl⟩ : syracuseStep 578827 = 868241) B868241
theorem B578839 : Blo 578813 578839 := bstep (se 1 (by rfl) ⟨434129, by rfl⟩ : syracuseStep 578839 = 868259) B868259
theorem B1103129 : Blo 578813 1103129 := bstep (se 2 (by rfl) ⟨413673, by rfl⟩ : syracuseStep 1103129 = 827347) B827347
theorem B578859 : Blo 578813 578859 := bstep (se 1 (by rfl) ⟨434144, by rfl⟩ : syracuseStep 578859 = 868289) B868289
theorem B1955123 : Blo 578813 1955123 := bstep (se 1 (by rfl) ⟨1466342, by rfl⟩ : syracuseStep 1955123 = 2932685) B2932685
theorem B578871 : Blo 578813 578871 := bstep (se 1 (by rfl) ⟨434153, by rfl⟩ : syracuseStep 578871 = 868307) B868307
theorem B1725761 : Blo 578813 1725761 := bstep (se 2 (by rfl) ⟨647160, by rfl⟩ : syracuseStep 1725761 = 1294321) B1294321
theorem B578891 : Blo 578813 578891 := bstep (se 1 (by rfl) ⟨434168, by rfl⟩ : syracuseStep 578891 = 868337) B868337
theorem B873803 : Blo 578813 873803 := bstep (se 1 (by rfl) ⟨655352, by rfl⟩ : syracuseStep 873803 = 1310705) B1310705
theorem B578903 : Blo 578813 578903 := bstep (se 1 (by rfl) ⟨434177, by rfl⟩ : syracuseStep 578903 = 868355) B868355
theorem B873815 : Blo 578813 873815 := bstep (se 1 (by rfl) ⟨655361, by rfl⟩ : syracuseStep 873815 = 1310723) B1310723
theorem B578923 : Blo 578813 578923 := bstep (se 1 (by rfl) ⟨434192, by rfl⟩ : syracuseStep 578923 = 868385) B868385
theorem B578935 : Blo 578813 578935 := bstep (se 1 (by rfl) ⟨434201, by rfl⟩ : syracuseStep 578935 = 868403) B868403
theorem B578955 : Blo 578813 578955 := bstep (se 1 (by rfl) ⟨434216, by rfl⟩ : syracuseStep 578955 = 868433) B868433
theorem B578967 : Blo 578813 578967 := bstep (se 1 (by rfl) ⟨434225, by rfl⟩ : syracuseStep 578967 = 868451) B868451
theorem B2479511 : Blo 578813 2479511 := bstep (se 1 (by rfl) ⟨1859633, by rfl⟩ : syracuseStep 2479511 = 3719267) B3719267
theorem B873881 : Blo 578813 873881 := bstep (se 2 (by rfl) ⟨327705, by rfl⟩ : syracuseStep 873881 = 655411) B655411
theorem B578987 : Blo 578813 578987 := bstep (se 1 (by rfl) ⟨434240, by rfl⟩ : syracuseStep 578987 = 868481) B868481
theorem B578999 : Blo 578813 578999 := bstep (se 1 (by rfl) ⟨434249, by rfl⟩ : syracuseStep 578999 = 868499) B868499
theorem B579019 : Blo 578813 579019 := bstep (se 1 (by rfl) ⟨434264, by rfl⟩ : syracuseStep 579019 = 868529) B868529
theorem B2119115 : Blo 578813 2119115 := bstep (se 1 (by rfl) ⟨1589336, by rfl⟩ : syracuseStep 2119115 = 3178673) B3178673
theorem B579031 : Blo 578813 579031 := bstep (se 1 (by rfl) ⟨434273, by rfl⟩ : syracuseStep 579031 = 868547) B868547
theorem B579051 : Blo 578813 579051 := bstep (se 1 (by rfl) ⟨434288, by rfl⟩ : syracuseStep 579051 = 868577) B868577
theorem B579063 : Blo 578813 579063 := bstep (se 1 (by rfl) ⟨434297, by rfl⟩ : syracuseStep 579063 = 868595) B868595
theorem B579083 : Blo 578813 579083 := bstep (se 1 (by rfl) ⟨434312, by rfl⟩ : syracuseStep 579083 = 868625) B868625
theorem B873995 : Blo 578813 873995 := bstep (se 1 (by rfl) ⟨655496, by rfl⟩ : syracuseStep 873995 = 1310993) B1310993
theorem B579095 : Blo 578813 579095 := bstep (se 1 (by rfl) ⟨434321, by rfl⟩ : syracuseStep 579095 = 868643) B868643
theorem B874007 : Blo 578813 874007 := bstep (se 1 (by rfl) ⟨655505, by rfl⟩ : syracuseStep 874007 = 1311011) B1311011
theorem B579115 : Blo 578813 579115 := bstep (se 1 (by rfl) ⟨434336, by rfl⟩ : syracuseStep 579115 = 868673) B868673
theorem B579127 : Blo 578813 579127 := bstep (se 1 (by rfl) ⟨434345, by rfl⟩ : syracuseStep 579127 = 868691) B868691
theorem B1955393 : Blo 578813 1955393 := bstep (se 2 (by rfl) ⟨733272, by rfl⟩ : syracuseStep 1955393 = 1466545) B1466545
theorem B579147 : Blo 578813 579147 := bstep (se 1 (by rfl) ⟨434360, by rfl⟩ : syracuseStep 579147 = 868721) B868721
theorem B579159 : Blo 578813 579159 := bstep (se 1 (by rfl) ⟨434369, by rfl⟩ : syracuseStep 579159 = 868739) B868739
theorem B874073 : Blo 578813 874073 := bstep (se 2 (by rfl) ⟨327777, by rfl⟩ : syracuseStep 874073 = 655555) B655555
theorem B1594973 : Blo 578813 1594973 := bstep (se 3 (by rfl) ⟨299057, by rfl⟩ : syracuseStep 1594973 = 598115) B598115
theorem B579179 : Blo 578813 579179 := bstep (se 1 (by rfl) ⟨434384, by rfl⟩ : syracuseStep 579179 = 868769) B868769
theorem B579191 : Blo 578813 579191 := bstep (se 1 (by rfl) ⟨434393, by rfl⟩ : syracuseStep 579191 = 868787) B868787
theorem B579211 : Blo 578813 579211 := bstep (se 1 (by rfl) ⟨434408, by rfl⟩ : syracuseStep 579211 = 868817) B868817
theorem B579223 : Blo 578813 579223 := bstep (se 1 (by rfl) ⟨434417, by rfl⟩ : syracuseStep 579223 = 868835) B868835
theorem B579243 : Blo 578813 579243 := bstep (se 1 (by rfl) ⟨434432, by rfl⟩ : syracuseStep 579243 = 868865) B868865
theorem B1103539 : Blo 578813 1103539 := bstep (se 1 (by rfl) ⟨827654, by rfl⟩ : syracuseStep 1103539 = 1655309) B1655309
theorem B579255 : Blo 578813 579255 := bstep (se 1 (by rfl) ⟨434441, by rfl⟩ : syracuseStep 579255 = 868883) B868883
theorem B579275 : Blo 578813 579275 := bstep (se 1 (by rfl) ⟨434456, by rfl⟩ : syracuseStep 579275 = 868913) B868913
theorem B874187 : Blo 578813 874187 := bstep (se 1 (by rfl) ⟨655640, by rfl⟩ : syracuseStep 874187 = 1311281) B1311281
theorem B579287 : Blo 578813 579287 := bstep (se 1 (by rfl) ⟨434465, by rfl⟩ : syracuseStep 579287 = 868931) B868931
theorem B874199 : Blo 578813 874199 := bstep (se 1 (by rfl) ⟨655649, by rfl⟩ : syracuseStep 874199 = 1311299) B1311299
theorem B579307 : Blo 578813 579307 := bstep (se 1 (by rfl) ⟨434480, by rfl⟩ : syracuseStep 579307 = 868961) B868961
theorem B579319 : Blo 578813 579319 := bstep (se 1 (by rfl) ⟨434489, by rfl⟩ : syracuseStep 579319 = 868979) B868979
theorem B579339 : Blo 578813 579339 := bstep (se 1 (by rfl) ⟨434504, by rfl⟩ : syracuseStep 579339 = 869009) B869009
theorem B3299089 : Blo 578813 3299089 := bstep (se 2 (by rfl) ⟨1237158, by rfl⟩ : syracuseStep 3299089 = 2474317) B2474317
theorem B579351 : Blo 578813 579351 := bstep (se 1 (by rfl) ⟨434513, by rfl⟩ : syracuseStep 579351 = 869027) B869027
theorem B579371 : Blo 578813 579371 := bstep (se 1 (by rfl) ⟨434528, by rfl⟩ : syracuseStep 579371 = 869057) B869057
theorem B579383 : Blo 578813 579383 := bstep (se 1 (by rfl) ⟨434537, by rfl⟩ : syracuseStep 579383 = 869075) B869075
theorem B579403 : Blo 578813 579403 := bstep (se 1 (by rfl) ⟨434552, by rfl⟩ : syracuseStep 579403 = 869105) B869105
theorem B579415 : Blo 578813 579415 := bstep (se 1 (by rfl) ⟨434561, by rfl⟩ : syracuseStep 579415 = 869123) B869123
theorem B579435 : Blo 578813 579435 := bstep (se 1 (by rfl) ⟨434576, by rfl⟩ : syracuseStep 579435 = 869153) B869153
theorem B579447 : Blo 578813 579447 := bstep (se 1 (by rfl) ⟨434585, by rfl⟩ : syracuseStep 579447 = 869171) B869171
theorem B579467 : Blo 578813 579467 := bstep (se 1 (by rfl) ⟨434600, by rfl⟩ : syracuseStep 579467 = 869201) B869201
theorem B579479 : Blo 578813 579479 := bstep (se 1 (by rfl) ⟨434609, by rfl⟩ : syracuseStep 579479 = 869219) B869219
theorem B1857431 : Blo 578813 1857431 := bstep (se 1 (by rfl) ⟨1393073, by rfl⟩ : syracuseStep 1857431 = 2786147) B2786147
theorem B579499 : Blo 578813 579499 := bstep (se 1 (by rfl) ⟨434624, by rfl⟩ : syracuseStep 579499 = 869249) B869249
theorem B579511 : Blo 578813 579511 := bstep (se 1 (by rfl) ⟨434633, by rfl⟩ : syracuseStep 579511 = 869267) B869267
theorem B579531 : Blo 578813 579531 := bstep (se 1 (by rfl) ⟨434648, by rfl⟩ : syracuseStep 579531 = 869297) B869297
theorem B579543 : Blo 578813 579543 := bstep (se 1 (by rfl) ⟨434657, by rfl⟩ : syracuseStep 579543 = 869315) B869315
theorem B2938841 : Blo 578813 2938841 := bstep (se 2 (by rfl) ⟨1102065, by rfl⟩ : syracuseStep 2938841 = 2204131) B2204131
theorem B5593049 : Blo 578813 5593049 := bstep (se 2 (by rfl) ⟨2097393, by rfl⟩ : syracuseStep 5593049 = 4194787) B4194787
theorem B579563 : Blo 578813 579563 := bstep (se 1 (by rfl) ⟨434672, by rfl⟩ : syracuseStep 579563 = 869345) B869345
theorem B579575 : Blo 578813 579575 := bstep (se 1 (by rfl) ⟨434681, by rfl⟩ : syracuseStep 579575 = 869363) B869363
theorem B579595 : Blo 578813 579595 := bstep (se 1 (by rfl) ⟨434696, by rfl⟩ : syracuseStep 579595 = 869393) B869393
theorem B579607 : Blo 578813 579607 := bstep (se 1 (by rfl) ⟨434705, by rfl⟩ : syracuseStep 579607 = 869411) B869411
theorem B579627 : Blo 578813 579627 := bstep (se 1 (by rfl) ⟨434720, by rfl⟩ : syracuseStep 579627 = 869441) B869441
theorem B2480179 : Blo 578813 2480179 := bstep (se 1 (by rfl) ⟨1860134, by rfl⟩ : syracuseStep 2480179 = 3720269) B3720269
theorem B579639 : Blo 578813 579639 := bstep (se 1 (by rfl) ⟨434729, by rfl⟩ : syracuseStep 579639 = 869459) B869459
theorem B579659 : Blo 578813 579659 := bstep (se 1 (by rfl) ⟨434744, by rfl⟩ : syracuseStep 579659 = 869489) B869489
theorem B5036107 : Blo 578813 5036107 := bstep (se 1 (by rfl) ⟨3777080, by rfl⟩ : syracuseStep 5036107 = 7554161) B7554161
theorem B579671 : Blo 578813 579671 := bstep (se 1 (by rfl) ⟨434753, by rfl⟩ : syracuseStep 579671 = 869507) B869507
theorem B1955933 : Blo 578813 1955933 := bstep (se 3 (by rfl) ⟨366737, by rfl⟩ : syracuseStep 1955933 = 733475) B733475
theorem B579691 : Blo 578813 579691 := bstep (se 1 (by rfl) ⟨434768, by rfl⟩ : syracuseStep 579691 = 869537) B869537
theorem B579703 : Blo 578813 579703 := bstep (se 1 (by rfl) ⟨434777, by rfl⟩ : syracuseStep 579703 = 869555) B869555
theorem B579723 : Blo 578813 579723 := bstep (se 1 (by rfl) ⟨434792, by rfl⟩ : syracuseStep 579723 = 869585) B869585
theorem B579735 : Blo 578813 579735 := bstep (se 1 (by rfl) ⟨434801, by rfl⟩ : syracuseStep 579735 = 869603) B869603
theorem B1104025 : Blo 578813 1104025 := bstep (se 2 (by rfl) ⟨414009, by rfl⟩ : syracuseStep 1104025 = 828019) B828019
theorem B579755 : Blo 578813 579755 := bstep (se 1 (by rfl) ⟨434816, by rfl⟩ : syracuseStep 579755 = 869633) B869633
theorem B579767 : Blo 578813 579767 := bstep (se 1 (by rfl) ⟨434825, by rfl⟩ : syracuseStep 579767 = 869651) B869651
theorem B579787 : Blo 578813 579787 := bstep (se 1 (by rfl) ⟨434840, by rfl⟩ : syracuseStep 579787 = 869681) B869681
theorem B579799 : Blo 578813 579799 := bstep (se 1 (by rfl) ⟨434849, by rfl⟩ : syracuseStep 579799 = 869699) B869699
theorem B579819 : Blo 578813 579819 := bstep (se 1 (by rfl) ⟨434864, by rfl⟩ : syracuseStep 579819 = 869729) B869729
theorem B8476913 : Blo 578813 8476913 := bstep (se 2 (by rfl) ⟨3178842, by rfl⟩ : syracuseStep 8476913 = 6357685) B6357685
theorem B579831 : Blo 578813 579831 := bstep (se 1 (by rfl) ⟨434873, by rfl⟩ : syracuseStep 579831 = 869747) B869747
theorem B579851 : Blo 578813 579851 := bstep (se 1 (by rfl) ⟨434888, by rfl⟩ : syracuseStep 579851 = 869777) B869777
theorem B579863 : Blo 578813 579863 := bstep (se 1 (by rfl) ⟨434897, by rfl⟩ : syracuseStep 579863 = 869795) B869795
theorem B579883 : Blo 578813 579883 := bstep (se 1 (by rfl) ⟨434912, by rfl⟩ : syracuseStep 579883 = 869825) B869825
theorem B579895 : Blo 578813 579895 := bstep (se 1 (by rfl) ⟨434921, by rfl⟩ : syracuseStep 579895 = 869843) B869843
theorem B579915 : Blo 578813 579915 := bstep (se 1 (by rfl) ⟨434936, by rfl⟩ : syracuseStep 579915 = 869873) B869873
theorem B579927 : Blo 578813 579927 := bstep (se 1 (by rfl) ⟨434945, by rfl⟩ : syracuseStep 579927 = 869891) B869891
theorem B579947 : Blo 578813 579947 := bstep (se 1 (by rfl) ⟨434960, by rfl⟩ : syracuseStep 579947 = 869921) B869921
theorem B579959 : Blo 578813 579959 := bstep (se 1 (by rfl) ⟨434969, by rfl⟩ : syracuseStep 579959 = 869939) B869939
theorem B579979 : Blo 578813 579979 := bstep (se 1 (by rfl) ⟨434984, by rfl⟩ : syracuseStep 579979 = 869969) B869969
theorem B579991 : Blo 578813 579991 := bstep (se 1 (by rfl) ⟨434993, by rfl⟩ : syracuseStep 579991 = 869987) B869987
theorem B580011 : Blo 578813 580011 := bstep (se 1 (by rfl) ⟨435008, by rfl⟩ : syracuseStep 580011 = 870017) B870017
theorem B580023 : Blo 578813 580023 := bstep (se 1 (by rfl) ⟨435017, by rfl⟩ : syracuseStep 580023 = 870035) B870035
theorem B580043 : Blo 578813 580043 := bstep (se 1 (by rfl) ⟨435032, by rfl⟩ : syracuseStep 580043 = 870065) B870065
theorem B580055 : Blo 578813 580055 := bstep (se 1 (by rfl) ⟨435041, by rfl⟩ : syracuseStep 580055 = 870083) B870083
theorem B580075 : Blo 578813 580075 := bstep (se 1 (by rfl) ⟨435056, by rfl⟩ : syracuseStep 580075 = 870113) B870113
theorem B580087 : Blo 578813 580087 := bstep (se 1 (by rfl) ⟨435065, by rfl⟩ : syracuseStep 580087 = 870131) B870131
theorem B580107 : Blo 578813 580107 := bstep (se 1 (by rfl) ⟨435080, by rfl⟩ : syracuseStep 580107 = 870161) B870161
theorem B580119 : Blo 578813 580119 := bstep (se 1 (by rfl) ⟨435089, by rfl⟩ : syracuseStep 580119 = 870179) B870179
theorem B580139 : Blo 578813 580139 := bstep (se 1 (by rfl) ⟨435104, by rfl⟩ : syracuseStep 580139 = 870209) B870209
theorem B580151 : Blo 578813 580151 := bstep (se 1 (by rfl) ⟨435113, by rfl⟩ : syracuseStep 580151 = 870227) B870227
theorem B580171 : Blo 578813 580171 := bstep (se 1 (by rfl) ⟨435128, by rfl⟩ : syracuseStep 580171 = 870257) B870257
theorem B580183 : Blo 578813 580183 := bstep (se 1 (by rfl) ⟨435137, by rfl⟩ : syracuseStep 580183 = 870275) B870275
theorem B2415193 : Blo 578813 2415193 := bstep (se 2 (by rfl) ⟨905697, by rfl⟩ : syracuseStep 2415193 = 1811395) B1811395
theorem B580203 : Blo 578813 580203 := bstep (se 1 (by rfl) ⟨435152, by rfl⟩ : syracuseStep 580203 = 870305) B870305
theorem B580215 : Blo 578813 580215 := bstep (se 1 (by rfl) ⟨435161, by rfl⟩ : syracuseStep 580215 = 870323) B870323
theorem B580235 : Blo 578813 580235 := bstep (se 1 (by rfl) ⟨435176, by rfl⟩ : syracuseStep 580235 = 870353) B870353
theorem B580247 : Blo 578813 580247 := bstep (se 1 (by rfl) ⟨435185, by rfl⟩ : syracuseStep 580247 = 870371) B870371
theorem B580267 : Blo 578813 580267 := bstep (se 1 (by rfl) ⟨435200, by rfl⟩ : syracuseStep 580267 = 870401) B870401
theorem B580279 : Blo 578813 580279 := bstep (se 1 (by rfl) ⟨435209, by rfl⟩ : syracuseStep 580279 = 870419) B870419
theorem B580299 : Blo 578813 580299 := bstep (se 1 (by rfl) ⟨435224, by rfl⟩ : syracuseStep 580299 = 870449) B870449
theorem B1104587 : Blo 578813 1104587 := bstep (se 1 (by rfl) ⟨828440, by rfl⟩ : syracuseStep 1104587 = 1656881) B1656881
theorem B580311 : Blo 578813 580311 := bstep (se 1 (by rfl) ⟨435233, by rfl⟩ : syracuseStep 580311 = 870467) B870467
theorem B1399513 : Blo 578813 1399513 := bstep (se 2 (by rfl) ⟨524817, by rfl⟩ : syracuseStep 1399513 = 1049635) B1049635
theorem B580331 : Blo 578813 580331 := bstep (se 1 (by rfl) ⟨435248, by rfl⟩ : syracuseStep 580331 = 870497) B870497
theorem B580343 : Blo 578813 580343 := bstep (se 1 (by rfl) ⟨435257, by rfl⟩ : syracuseStep 580343 = 870515) B870515
theorem B580363 : Blo 578813 580363 := bstep (se 1 (by rfl) ⟨435272, by rfl⟩ : syracuseStep 580363 = 870545) B870545
theorem B580375 : Blo 578813 580375 := bstep (se 1 (by rfl) ⟨435281, by rfl⟩ : syracuseStep 580375 = 870563) B870563
theorem B580395 : Blo 578813 580395 := bstep (se 1 (by rfl) ⟨435296, by rfl⟩ : syracuseStep 580395 = 870593) B870593
theorem B580407 : Blo 578813 580407 := bstep (se 1 (by rfl) ⟨435305, by rfl⟩ : syracuseStep 580407 = 870611) B870611
theorem B580427 : Blo 578813 580427 := bstep (se 1 (by rfl) ⟨435320, by rfl⟩ : syracuseStep 580427 = 870641) B870641
theorem B580439 : Blo 578813 580439 := bstep (se 1 (by rfl) ⟨435329, by rfl⟩ : syracuseStep 580439 = 870659) B870659
theorem B14932835 : Blo 578813 14932835 := bstep (se 1 (by rfl) ⟨11199626, by rfl⟩ : syracuseStep 14932835 = 22399253) B22399253
theorem B580459 : Blo 578813 580459 := bstep (se 1 (by rfl) ⟨435344, by rfl⟩ : syracuseStep 580459 = 870689) B870689
theorem B580471 : Blo 578813 580471 := bstep (se 1 (by rfl) ⟨435353, by rfl⟩ : syracuseStep 580471 = 870707) B870707
theorem B1104769 : Blo 578813 1104769 := bstep (se 2 (by rfl) ⟨414288, by rfl⟩ : syracuseStep 1104769 = 828577) B828577
theorem B580491 : Blo 578813 580491 := bstep (se 1 (by rfl) ⟨435368, by rfl⟩ : syracuseStep 580491 = 870737) B870737
theorem B580503 : Blo 578813 580503 := bstep (se 1 (by rfl) ⟨435377, by rfl⟩ : syracuseStep 580503 = 870755) B870755
theorem B580523 : Blo 578813 580523 := bstep (se 1 (by rfl) ⟨435392, by rfl⟩ : syracuseStep 580523 = 870785) B870785
theorem B580535 : Blo 578813 580535 := bstep (se 1 (by rfl) ⟨435401, by rfl⟩ : syracuseStep 580535 = 870803) B870803
theorem B580555 : Blo 578813 580555 := bstep (se 1 (by rfl) ⟨435416, by rfl⟩ : syracuseStep 580555 = 870833) B870833
theorem B580567 : Blo 578813 580567 := bstep (se 1 (by rfl) ⟨435425, by rfl⟩ : syracuseStep 580567 = 870851) B870851
theorem B580587 : Blo 578813 580587 := bstep (se 1 (by rfl) ⟨435440, by rfl⟩ : syracuseStep 580587 = 870881) B870881
theorem B580599 : Blo 578813 580599 := bstep (se 1 (by rfl) ⟨435449, by rfl⟩ : syracuseStep 580599 = 870899) B870899
theorem B580619 : Blo 578813 580619 := bstep (se 1 (by rfl) ⟨435464, by rfl⟩ : syracuseStep 580619 = 870929) B870929
theorem B580631 : Blo 578813 580631 := bstep (se 1 (by rfl) ⟨435473, by rfl⟩ : syracuseStep 580631 = 870947) B870947
theorem B580651 : Blo 578813 580651 := bstep (se 1 (by rfl) ⟨435488, by rfl⟩ : syracuseStep 580651 = 870977) B870977
theorem B580663 : Blo 578813 580663 := bstep (se 1 (by rfl) ⟨435497, by rfl⟩ : syracuseStep 580663 = 870995) B870995
theorem B3529793 : Blo 578813 3529793 := bstep (se 2 (by rfl) ⟨1323672, by rfl⟩ : syracuseStep 3529793 = 2647345) B2647345
theorem B580683 : Blo 578813 580683 := bstep (se 1 (by rfl) ⟨435512, by rfl⟩ : syracuseStep 580683 = 871025) B871025
theorem B580695 : Blo 578813 580695 := bstep (se 1 (by rfl) ⟨435521, by rfl⟩ : syracuseStep 580695 = 871043) B871043
theorem B580715 : Blo 578813 580715 := bstep (se 1 (by rfl) ⟨435536, by rfl⟩ : syracuseStep 580715 = 871073) B871073
theorem B580727 : Blo 578813 580727 := bstep (se 1 (by rfl) ⟨435545, by rfl⟩ : syracuseStep 580727 = 871091) B871091
theorem B580747 : Blo 578813 580747 := bstep (se 1 (by rfl) ⟨435560, by rfl⟩ : syracuseStep 580747 = 871121) B871121
theorem B580759 : Blo 578813 580759 := bstep (se 1 (by rfl) ⟨435569, by rfl⟩ : syracuseStep 580759 = 871139) B871139
theorem B580779 : Blo 578813 580779 := bstep (se 1 (by rfl) ⟨435584, by rfl⟩ : syracuseStep 580779 = 871169) B871169
theorem B1465523 : Blo 578813 1465523 := bstep (se 1 (by rfl) ⟨1099142, by rfl⟩ : syracuseStep 1465523 = 2198285) B2198285
theorem B580791 : Blo 578813 580791 := bstep (se 1 (by rfl) ⟨435593, by rfl⟩ : syracuseStep 580791 = 871187) B871187
theorem B1957067 : Blo 578813 1957067 := bstep (se 1 (by rfl) ⟨1467800, by rfl⟩ : syracuseStep 1957067 = 2935601) B2935601
theorem B1858763 : Blo 578813 1858763 := bstep (se 1 (by rfl) ⟨1394072, by rfl⟩ : syracuseStep 1858763 = 2788145) B2788145
theorem B580811 : Blo 578813 580811 := bstep (se 1 (by rfl) ⟨435608, by rfl⟩ : syracuseStep 580811 = 871217) B871217
theorem B580823 : Blo 578813 580823 := bstep (se 1 (by rfl) ⟨435617, by rfl⟩ : syracuseStep 580823 = 871235) B871235
theorem B580843 : Blo 578813 580843 := bstep (se 1 (by rfl) ⟨435632, by rfl⟩ : syracuseStep 580843 = 871265) B871265
theorem B580855 : Blo 578813 580855 := bstep (se 1 (by rfl) ⟨435641, by rfl⟩ : syracuseStep 580855 = 871283) B871283
theorem B580875 : Blo 578813 580875 := bstep (se 1 (by rfl) ⟨435656, by rfl⟩ : syracuseStep 580875 = 871313) B871313
theorem B2481425 : Blo 578813 2481425 := bstep (se 2 (by rfl) ⟨930534, by rfl⟩ : syracuseStep 2481425 = 1861069) B1861069
theorem B580887 : Blo 578813 580887 := bstep (se 1 (by rfl) ⟨435665, by rfl⟩ : syracuseStep 580887 = 871331) B871331
theorem B580907 : Blo 578813 580907 := bstep (se 1 (by rfl) ⟨435680, by rfl⟩ : syracuseStep 580907 = 871361) B871361
theorem B580919 : Blo 578813 580919 := bstep (se 1 (by rfl) ⟨435689, by rfl⟩ : syracuseStep 580919 = 871379) B871379
theorem B1400129 : Blo 578813 1400129 := bstep (se 2 (by rfl) ⟨525048, by rfl⟩ : syracuseStep 1400129 = 1050097) B1050097
theorem B580939 : Blo 578813 580939 := bstep (se 1 (by rfl) ⟨435704, by rfl⟩ : syracuseStep 580939 = 871409) B871409
theorem B580951 : Blo 578813 580951 := bstep (se 1 (by rfl) ⟨435713, by rfl⟩ : syracuseStep 580951 = 871427) B871427
theorem B580971 : Blo 578813 580971 := bstep (se 1 (by rfl) ⟨435728, by rfl⟩ : syracuseStep 580971 = 871457) B871457
theorem B580983 : Blo 578813 580983 := bstep (se 1 (by rfl) ⟨435737, by rfl⟩ : syracuseStep 580983 = 871475) B871475
theorem B581003 : Blo 578813 581003 := bstep (se 1 (by rfl) ⟨435752, by rfl⟩ : syracuseStep 581003 = 871505) B871505
theorem B581015 : Blo 578813 581015 := bstep (se 1 (by rfl) ⟨435761, by rfl⟩ : syracuseStep 581015 = 871523) B871523
theorem B941465 : Blo 578813 941465 := bstep (se 2 (by rfl) ⟨353049, by rfl⟩ : syracuseStep 941465 = 706099) B706099
theorem B581035 : Blo 578813 581035 := bstep (se 1 (by rfl) ⟨435776, by rfl⟩ : syracuseStep 581035 = 871553) B871553
theorem B581047 : Blo 578813 581047 := bstep (se 1 (by rfl) ⟨435785, by rfl⟩ : syracuseStep 581047 = 871571) B871571
theorem B581067 : Blo 578813 581067 := bstep (se 1 (by rfl) ⟨435800, by rfl⟩ : syracuseStep 581067 = 871601) B871601
theorem B581079 : Blo 578813 581079 := bstep (se 1 (by rfl) ⟨435809, by rfl⟩ : syracuseStep 581079 = 871619) B871619
theorem B1957337 : Blo 578813 1957337 := bstep (se 2 (by rfl) ⟨734001, by rfl⟩ : syracuseStep 1957337 = 1468003) B1468003
theorem B581099 : Blo 578813 581099 := bstep (se 1 (by rfl) ⟨435824, by rfl⟩ : syracuseStep 581099 = 871649) B871649
theorem B581111 : Blo 578813 581111 := bstep (se 1 (by rfl) ⟨435833, by rfl⟩ : syracuseStep 581111 = 871667) B871667
theorem B581131 : Blo 578813 581131 := bstep (se 1 (by rfl) ⟨435848, by rfl⟩ : syracuseStep 581131 = 871697) B871697
theorem B581143 : Blo 578813 581143 := bstep (se 1 (by rfl) ⟨435857, by rfl⟩ : syracuseStep 581143 = 871715) B871715
theorem B581163 : Blo 578813 581163 := bstep (se 1 (by rfl) ⟨435872, by rfl⟩ : syracuseStep 581163 = 871745) B871745
theorem B2940461 : Blo 578813 2940461 := bstep (se 3 (by rfl) ⟨551336, by rfl⟩ : syracuseStep 2940461 = 1102673) B1102673
theorem B581175 : Blo 578813 581175 := bstep (se 1 (by rfl) ⟨435881, by rfl⟩ : syracuseStep 581175 = 871763) B871763
theorem B581195 : Blo 578813 581195 := bstep (se 1 (by rfl) ⟨435896, by rfl⟩ : syracuseStep 581195 = 871793) B871793
theorem B1105483 : Blo 578813 1105483 := bstep (se 1 (by rfl) ⟨829112, by rfl⟩ : syracuseStep 1105483 = 1658225) B1658225
theorem B581207 : Blo 578813 581207 := bstep (se 1 (by rfl) ⟨435905, by rfl⟩ : syracuseStep 581207 = 871811) B871811
theorem B581227 : Blo 578813 581227 := bstep (se 1 (by rfl) ⟨435920, by rfl⟩ : syracuseStep 581227 = 871841) B871841
theorem B581239 : Blo 578813 581239 := bstep (se 1 (by rfl) ⟨435929, by rfl⟩ : syracuseStep 581239 = 871859) B871859
theorem B581259 : Blo 578813 581259 := bstep (se 1 (by rfl) ⟨435944, by rfl⟩ : syracuseStep 581259 = 871889) B871889
theorem B581271 : Blo 578813 581271 := bstep (se 1 (by rfl) ⟨435953, by rfl⟩ : syracuseStep 581271 = 871907) B871907
theorem B1105559 : Blo 578813 1105559 := bstep (se 1 (by rfl) ⟨829169, by rfl⟩ : syracuseStep 1105559 = 1658339) B1658339
theorem B581291 : Blo 578813 581291 := bstep (se 1 (by rfl) ⟨435968, by rfl⟩ : syracuseStep 581291 = 871937) B871937
theorem B581303 : Blo 578813 581303 := bstep (se 1 (by rfl) ⟨435977, by rfl⟩ : syracuseStep 581303 = 871955) B871955
theorem B1466059 : Blo 578813 1466059 := bstep (se 1 (by rfl) ⟨1099544, by rfl⟩ : syracuseStep 1466059 = 2199089) B2199089
theorem B581323 : Blo 578813 581323 := bstep (se 1 (by rfl) ⟨435992, by rfl⟩ : syracuseStep 581323 = 871985) B871985
theorem B581335 : Blo 578813 581335 := bstep (se 1 (by rfl) ⟨436001, by rfl⟩ : syracuseStep 581335 = 872003) B872003
theorem B581355 : Blo 578813 581355 := bstep (se 1 (by rfl) ⟨436016, by rfl⟩ : syracuseStep 581355 = 872033) B872033
theorem B581367 : Blo 578813 581367 := bstep (se 1 (by rfl) ⟨436025, by rfl⟩ : syracuseStep 581367 = 872051) B872051
theorem B581387 : Blo 578813 581387 := bstep (se 1 (by rfl) ⟨436040, by rfl⟩ : syracuseStep 581387 = 872081) B872081
theorem B581399 : Blo 578813 581399 := bstep (se 1 (by rfl) ⟨436049, by rfl⟩ : syracuseStep 581399 = 872099) B872099
theorem B581419 : Blo 578813 581419 := bstep (se 1 (by rfl) ⟨436064, by rfl⟩ : syracuseStep 581419 = 872129) B872129
theorem B581431 : Blo 578813 581431 := bstep (se 1 (by rfl) ⟨436073, by rfl⟩ : syracuseStep 581431 = 872147) B872147
theorem B581451 : Blo 578813 581451 := bstep (se 1 (by rfl) ⟨436088, by rfl⟩ : syracuseStep 581451 = 872177) B872177
theorem B581463 : Blo 578813 581463 := bstep (se 1 (by rfl) ⟨436097, by rfl⟩ : syracuseStep 581463 = 872195) B872195
theorem B1466201 : Blo 578813 1466201 := bstep (se 2 (by rfl) ⟨549825, by rfl⟩ : syracuseStep 1466201 = 1099651) B1099651
theorem B581483 : Blo 578813 581483 := bstep (se 1 (by rfl) ⟨436112, by rfl⟩ : syracuseStep 581483 = 872225) B872225
theorem B581495 : Blo 578813 581495 := bstep (se 1 (by rfl) ⟨436121, by rfl⟩ : syracuseStep 581495 = 872243) B872243
theorem B581515 : Blo 578813 581515 := bstep (se 1 (by rfl) ⟨436136, by rfl⟩ : syracuseStep 581515 = 872273) B872273
theorem B581527 : Blo 578813 581527 := bstep (se 1 (by rfl) ⟨436145, by rfl⟩ : syracuseStep 581527 = 872291) B872291
theorem B1302425 : Blo 578813 1302425 := bstep (se 2 (by rfl) ⟨488409, by rfl⟩ : syracuseStep 1302425 = 976819) B976819
theorem B581547 : Blo 578813 581547 := bstep (se 1 (by rfl) ⟨436160, by rfl⟩ : syracuseStep 581547 = 872321) B872321
theorem B581559 : Blo 578813 581559 := bstep (se 1 (by rfl) ⟨436169, by rfl⟩ : syracuseStep 581559 = 872339) B872339
theorem B581579 : Blo 578813 581579 := bstep (se 1 (by rfl) ⟨436184, by rfl⟩ : syracuseStep 581579 = 872369) B872369
theorem B581591 : Blo 578813 581591 := bstep (se 1 (by rfl) ⟨436193, by rfl⟩ : syracuseStep 581591 = 872387) B872387
theorem B581611 : Blo 578813 581611 := bstep (se 1 (by rfl) ⟨436208, by rfl⟩ : syracuseStep 581611 = 872417) B872417
theorem B1302515 : Blo 578813 1302515 := bstep (se 1 (by rfl) ⟨976886, by rfl⟩ : syracuseStep 1302515 = 1953773) B1953773
theorem B581623 : Blo 578813 581623 := bstep (se 1 (by rfl) ⟨436217, by rfl⟩ : syracuseStep 581623 = 872435) B872435
theorem B581643 : Blo 578813 581643 := bstep (se 1 (by rfl) ⟨436232, by rfl⟩ : syracuseStep 581643 = 872465) B872465
theorem B1302551 : Blo 578813 1302551 := bstep (se 1 (by rfl) ⟨976913, by rfl⟩ : syracuseStep 1302551 = 1953827) B1953827
theorem B581655 : Blo 578813 581655 := bstep (se 1 (by rfl) ⟨436241, by rfl⟩ : syracuseStep 581655 = 872483) B872483
theorem B581675 : Blo 578813 581675 := bstep (se 1 (by rfl) ⟨436256, by rfl⟩ : syracuseStep 581675 = 872513) B872513
theorem B581687 : Blo 578813 581687 := bstep (se 1 (by rfl) ⟨436265, by rfl⟩ : syracuseStep 581687 = 872531) B872531
theorem B581707 : Blo 578813 581707 := bstep (se 1 (by rfl) ⟨436280, by rfl⟩ : syracuseStep 581707 = 872561) B872561
theorem B581719 : Blo 578813 581719 := bstep (se 1 (by rfl) ⟨436289, by rfl⟩ : syracuseStep 581719 = 872579) B872579
theorem B581739 : Blo 578813 581739 := bstep (se 1 (by rfl) ⟨436304, by rfl⟩ : syracuseStep 581739 = 872609) B872609
theorem B581751 : Blo 578813 581751 := bstep (se 1 (by rfl) ⟨436313, by rfl⟩ : syracuseStep 581751 = 872627) B872627
theorem B2089091 : Blo 578813 2089091 := bstep (se 1 (by rfl) ⟨1566818, by rfl⟩ : syracuseStep 2089091 = 3133637) B3133637
theorem B581771 : Blo 578813 581771 := bstep (se 1 (by rfl) ⟨436328, by rfl⟩ : syracuseStep 581771 = 872657) B872657
theorem B1958039 : Blo 578813 1958039 := bstep (se 1 (by rfl) ⟨1468529, by rfl⟩ : syracuseStep 1958039 = 2937059) B2937059
theorem B581783 : Blo 578813 581783 := bstep (se 1 (by rfl) ⟨436337, by rfl⟩ : syracuseStep 581783 = 872675) B872675
theorem B581803 : Blo 578813 581803 := bstep (se 1 (by rfl) ⟨436352, by rfl⟩ : syracuseStep 581803 = 872705) B872705
theorem B581815 : Blo 578813 581815 := bstep (se 1 (by rfl) ⟨436361, by rfl⟩ : syracuseStep 581815 = 872723) B872723
theorem B1302731 : Blo 578813 1302731 := bstep (se 1 (by rfl) ⟨977048, by rfl⟩ : syracuseStep 1302731 = 1954097) B1954097
theorem B581835 : Blo 578813 581835 := bstep (se 1 (by rfl) ⟨436376, by rfl⟩ : syracuseStep 581835 = 872753) B872753
theorem B581847 : Blo 578813 581847 := bstep (se 1 (by rfl) ⟨436385, by rfl⟩ : syracuseStep 581847 = 872771) B872771
theorem B581867 : Blo 578813 581867 := bstep (se 1 (by rfl) ⟨436400, by rfl⟩ : syracuseStep 581867 = 872801) B872801
theorem B581879 : Blo 578813 581879 := bstep (se 1 (by rfl) ⟨436409, by rfl⟩ : syracuseStep 581879 = 872819) B872819
theorem B1302785 : Blo 578813 1302785 := bstep (se 2 (by rfl) ⟨488544, by rfl⟩ : syracuseStep 1302785 = 977089) B977089
theorem B581899 : Blo 578813 581899 := bstep (se 1 (by rfl) ⟨436424, by rfl⟩ : syracuseStep 581899 = 872849) B872849
theorem B581911 : Blo 578813 581911 := bstep (se 1 (by rfl) ⟨436433, by rfl⟩ : syracuseStep 581911 = 872867) B872867
theorem B581931 : Blo 578813 581931 := bstep (se 1 (by rfl) ⟨436448, by rfl⟩ : syracuseStep 581931 = 872897) B872897
theorem B1106227 : Blo 578813 1106227 := bstep (se 1 (by rfl) ⟨829670, by rfl⟩ : syracuseStep 1106227 = 1659341) B1659341
theorem B581943 : Blo 578813 581943 := bstep (se 1 (by rfl) ⟨436457, by rfl⟩ : syracuseStep 581943 = 872915) B872915
theorem B581963 : Blo 578813 581963 := bstep (se 1 (by rfl) ⟨436472, by rfl⟩ : syracuseStep 581963 = 872945) B872945
theorem B581975 : Blo 578813 581975 := bstep (se 1 (by rfl) ⟨436481, by rfl⟩ : syracuseStep 581975 = 872963) B872963
theorem B1761625 : Blo 578813 1761625 := bstep (se 2 (by rfl) ⟨660609, by rfl⟩ : syracuseStep 1761625 = 1321219) B1321219
theorem B581995 : Blo 578813 581995 := bstep (se 1 (by rfl) ⟨436496, by rfl⟩ : syracuseStep 581995 = 872993) B872993
theorem B582007 : Blo 578813 582007 := bstep (se 1 (by rfl) ⟨436505, by rfl⟩ : syracuseStep 582007 = 873011) B873011
theorem B582027 : Blo 578813 582027 := bstep (se 1 (by rfl) ⟨436520, by rfl⟩ : syracuseStep 582027 = 873041) B873041
theorem B582039 : Blo 578813 582039 := bstep (se 1 (by rfl) ⟨436529, by rfl⟩ : syracuseStep 582039 = 873059) B873059
theorem B582059 : Blo 578813 582059 := bstep (se 1 (by rfl) ⟨436544, by rfl⟩ : syracuseStep 582059 = 873089) B873089
theorem B582071 : Blo 578813 582071 := bstep (se 1 (by rfl) ⟨436553, by rfl⟩ : syracuseStep 582071 = 873107) B873107
theorem B582091 : Blo 578813 582091 := bstep (se 1 (by rfl) ⟨436568, by rfl⟩ : syracuseStep 582091 = 873137) B873137
theorem B582103 : Blo 578813 582103 := bstep (se 1 (by rfl) ⟨436577, by rfl⟩ : syracuseStep 582103 = 873155) B873155
theorem B1303001 : Blo 578813 1303001 := bstep (se 2 (by rfl) ⟨488625, by rfl⟩ : syracuseStep 1303001 = 977251) B977251
theorem B582123 : Blo 578813 582123 := bstep (se 1 (by rfl) ⟨436592, by rfl⟩ : syracuseStep 582123 = 873185) B873185
theorem B582135 : Blo 578813 582135 := bstep (se 1 (by rfl) ⟨436601, by rfl⟩ : syracuseStep 582135 = 873203) B873203
theorem B582155 : Blo 578813 582155 := bstep (se 1 (by rfl) ⟨436616, by rfl⟩ : syracuseStep 582155 = 873233) B873233
theorem B582167 : Blo 578813 582167 := bstep (se 1 (by rfl) ⟨436625, by rfl⟩ : syracuseStep 582167 = 873251) B873251
theorem B582187 : Blo 578813 582187 := bstep (se 1 (by rfl) ⟨436640, by rfl⟩ : syracuseStep 582187 = 873281) B873281
theorem B1303091 : Blo 578813 1303091 := bstep (se 1 (by rfl) ⟨977318, by rfl⟩ : syracuseStep 1303091 = 1954637) B1954637
theorem B582199 : Blo 578813 582199 := bstep (se 1 (by rfl) ⟨436649, by rfl⟩ : syracuseStep 582199 = 873299) B873299
theorem B582219 : Blo 578813 582219 := bstep (se 1 (by rfl) ⟨436664, by rfl⟩ : syracuseStep 582219 = 873329) B873329
theorem B1303127 : Blo 578813 1303127 := bstep (se 1 (by rfl) ⟨977345, by rfl⟩ : syracuseStep 1303127 = 1954691) B1954691
theorem B582231 : Blo 578813 582231 := bstep (se 1 (by rfl) ⟨436673, by rfl⟩ : syracuseStep 582231 = 873347) B873347
theorem B582251 : Blo 578813 582251 := bstep (se 1 (by rfl) ⟨436688, by rfl⟩ : syracuseStep 582251 = 873377) B873377
theorem B582263 : Blo 578813 582263 := bstep (se 1 (by rfl) ⟨436697, by rfl⟩ : syracuseStep 582263 = 873395) B873395
theorem B582283 : Blo 578813 582283 := bstep (se 1 (by rfl) ⟨436712, by rfl⟩ : syracuseStep 582283 = 873425) B873425
theorem B1237655 : Blo 578813 1237655 := bstep (se 1 (by rfl) ⟨928241, by rfl⟩ : syracuseStep 1237655 = 1856483) B1856483
theorem B1467031 : Blo 578813 1467031 := bstep (se 1 (by rfl) ⟨1100273, by rfl⟩ : syracuseStep 1467031 = 2200547) B2200547
theorem B582295 : Blo 578813 582295 := bstep (se 1 (by rfl) ⟨436721, by rfl⟩ : syracuseStep 582295 = 873443) B873443
theorem B582315 : Blo 578813 582315 := bstep (se 1 (by rfl) ⟨436736, by rfl⟩ : syracuseStep 582315 = 873473) B873473
theorem B1270451 : Blo 578813 1270451 := bstep (se 1 (by rfl) ⟨952838, by rfl⟩ : syracuseStep 1270451 = 1905677) B1905677
theorem B1958579 : Blo 578813 1958579 := bstep (se 1 (by rfl) ⟨1468934, by rfl⟩ : syracuseStep 1958579 = 2937869) B2937869
theorem B582327 : Blo 578813 582327 := bstep (se 1 (by rfl) ⟨436745, by rfl⟩ : syracuseStep 582327 = 873491) B873491
theorem B582347 : Blo 578813 582347 := bstep (se 1 (by rfl) ⟨436760, by rfl⟩ : syracuseStep 582347 = 873521) B873521
theorem B4186829 : Blo 578813 4186829 := bstep (se 3 (by rfl) ⟨785030, by rfl⟩ : syracuseStep 4186829 = 1570061) B1570061
theorem B582359 : Blo 578813 582359 := bstep (se 1 (by rfl) ⟨436769, by rfl⟩ : syracuseStep 582359 = 873539) B873539
theorem B582379 : Blo 578813 582379 := bstep (se 1 (by rfl) ⟨436784, by rfl⟩ : syracuseStep 582379 = 873569) B873569
theorem B582391 : Blo 578813 582391 := bstep (se 1 (by rfl) ⟨436793, by rfl⟩ : syracuseStep 582391 = 873587) B873587
theorem B1303307 : Blo 578813 1303307 := bstep (se 1 (by rfl) ⟨977480, by rfl⟩ : syracuseStep 1303307 = 1954961) B1954961
theorem B582411 : Blo 578813 582411 := bstep (se 1 (by rfl) ⟨436808, by rfl⟩ : syracuseStep 582411 = 873617) B873617
theorem B582423 : Blo 578813 582423 := bstep (se 1 (by rfl) ⟨436817, by rfl⟩ : syracuseStep 582423 = 873635) B873635
theorem B582443 : Blo 578813 582443 := bstep (se 1 (by rfl) ⟨436832, by rfl⟩ : syracuseStep 582443 = 873665) B873665
theorem B5563181 : Blo 578813 5563181 := bstep (se 3 (by rfl) ⟨1043096, by rfl⟩ : syracuseStep 5563181 = 2086193) B2086193
theorem B1860403 : Blo 578813 1860403 := bstep (se 1 (by rfl) ⟨1395302, by rfl⟩ : syracuseStep 1860403 = 2790605) B2790605
theorem B582455 : Blo 578813 582455 := bstep (se 1 (by rfl) ⟨436841, by rfl⟩ : syracuseStep 582455 = 873683) B873683
theorem B1303361 : Blo 578813 1303361 := bstep (se 2 (by rfl) ⟨488760, by rfl⟩ : syracuseStep 1303361 = 977521) B977521
theorem B1237835 : Blo 578813 1237835 := bstep (se 1 (by rfl) ⟨928376, by rfl⟩ : syracuseStep 1237835 = 1856753) B1856753
theorem B582475 : Blo 578813 582475 := bstep (se 1 (by rfl) ⟨436856, by rfl⟩ : syracuseStep 582475 = 873713) B873713
theorem B582487 : Blo 578813 582487 := bstep (se 1 (by rfl) ⟨436865, by rfl⟩ : syracuseStep 582487 = 873731) B873731
theorem B582507 : Blo 578813 582507 := bstep (se 1 (by rfl) ⟨436880, by rfl⟩ : syracuseStep 582507 = 873761) B873761
theorem B582519 : Blo 578813 582519 := bstep (se 1 (by rfl) ⟨436889, by rfl⟩ : syracuseStep 582519 = 873779) B873779
theorem B582539 : Blo 578813 582539 := bstep (se 1 (by rfl) ⟨436904, by rfl⟩ : syracuseStep 582539 = 873809) B873809
theorem B582551 : Blo 578813 582551 := bstep (se 1 (by rfl) ⟨436913, by rfl⟩ : syracuseStep 582551 = 873827) B873827
theorem B582571 : Blo 578813 582571 := bstep (se 1 (by rfl) ⟨436928, by rfl⟩ : syracuseStep 582571 = 873857) B873857
theorem B6710195 : Blo 578813 6710195 := bstep (se 1 (by rfl) ⟨5032646, by rfl⟩ : syracuseStep 6710195 = 10065293) B10065293
theorem B582583 : Blo 578813 582583 := bstep (se 1 (by rfl) ⟨436937, by rfl⟩ : syracuseStep 582583 = 873875) B873875
theorem B1958849 : Blo 578813 1958849 := bstep (se 2 (by rfl) ⟨734568, by rfl⟩ : syracuseStep 1958849 = 1469137) B1469137
theorem B1860545 : Blo 578813 1860545 := bstep (se 2 (by rfl) ⟨697704, by rfl⟩ : syracuseStep 1860545 = 1395409) B1395409
theorem B582603 : Blo 578813 582603 := bstep (se 1 (by rfl) ⟨436952, by rfl⟩ : syracuseStep 582603 = 873905) B873905
theorem B582615 : Blo 578813 582615 := bstep (se 1 (by rfl) ⟨436961, by rfl⟩ : syracuseStep 582615 = 873923) B873923
theorem B582635 : Blo 578813 582635 := bstep (se 1 (by rfl) ⟨436976, by rfl⟩ : syracuseStep 582635 = 873953) B873953
theorem B582647 : Blo 578813 582647 := bstep (se 1 (by rfl) ⟨436985, by rfl⟩ : syracuseStep 582647 = 873971) B873971
theorem B582667 : Blo 578813 582667 := bstep (se 1 (by rfl) ⟨437000, by rfl⟩ : syracuseStep 582667 = 874001) B874001
theorem B582679 : Blo 578813 582679 := bstep (se 1 (by rfl) ⟨437009, by rfl⟩ : syracuseStep 582679 = 874019) B874019
theorem B1303577 : Blo 578813 1303577 := bstep (se 2 (by rfl) ⟨488841, by rfl⟩ : syracuseStep 1303577 = 977683) B977683
theorem B582699 : Blo 578813 582699 := bstep (se 1 (by rfl) ⟨437024, by rfl⟩ : syracuseStep 582699 = 874049) B874049
theorem B1860659 : Blo 578813 1860659 := bstep (se 1 (by rfl) ⟨1395494, by rfl⟩ : syracuseStep 1860659 = 2790989) B2790989
theorem B582711 : Blo 578813 582711 := bstep (se 1 (by rfl) ⟨437033, by rfl⟩ : syracuseStep 582711 = 874067) B874067
theorem B1467467 : Blo 578813 1467467 := bstep (se 1 (by rfl) ⟨1100600, by rfl⟩ : syracuseStep 1467467 = 2201201) B2201201
theorem B582731 : Blo 578813 582731 := bstep (se 1 (by rfl) ⟨437048, by rfl⟩ : syracuseStep 582731 = 874097) B874097
theorem B582743 : Blo 578813 582743 := bstep (se 1 (by rfl) ⟨437057, by rfl⟩ : syracuseStep 582743 = 874115) B874115
theorem B582763 : Blo 578813 582763 := bstep (se 1 (by rfl) ⟨437072, by rfl⟩ : syracuseStep 582763 = 874145) B874145
theorem B1303667 : Blo 578813 1303667 := bstep (se 1 (by rfl) ⟨977750, by rfl⟩ : syracuseStep 1303667 = 1955501) B1955501
theorem B582775 : Blo 578813 582775 := bstep (se 1 (by rfl) ⟨437081, by rfl⟩ : syracuseStep 582775 = 874163) B874163
theorem B3302531 : Blo 578813 3302531 := bstep (se 1 (by rfl) ⟨2476898, by rfl⟩ : syracuseStep 3302531 = 4953797) B4953797
theorem B582795 : Blo 578813 582795 := bstep (se 1 (by rfl) ⟨437096, by rfl⟩ : syracuseStep 582795 = 874193) B874193
theorem B1303703 : Blo 578813 1303703 := bstep (se 1 (by rfl) ⟨977777, by rfl⟩ : syracuseStep 1303703 = 1955555) B1955555
theorem B582807 : Blo 578813 582807 := bstep (se 1 (by rfl) ⟨437105, by rfl⟩ : syracuseStep 582807 = 874211) B874211
theorem B1303883 : Blo 578813 1303883 := bstep (se 1 (by rfl) ⟨977912, by rfl⟩ : syracuseStep 1303883 = 1955825) B1955825
theorem B1303937 : Blo 578813 1303937 := bstep (se 2 (by rfl) ⟨488976, by rfl⟩ : syracuseStep 1303937 = 977953) B977953
theorem B2352563 : Blo 578813 2352563 := bstep (se 1 (by rfl) ⟨1764422, by rfl⟩ : syracuseStep 2352563 = 3528845) B3528845
theorem B1467841 : Blo 578813 1467841 := bstep (se 2 (by rfl) ⟨550440, by rfl⟩ : syracuseStep 1467841 = 1100881) B1100881
theorem B1959389 : Blo 578813 1959389 := bstep (se 3 (by rfl) ⟨367385, by rfl⟩ : syracuseStep 1959389 = 734771) B734771
theorem B6350411 : Blo 578813 6350411 := bstep (se 1 (by rfl) ⟨4762808, by rfl⟩ : syracuseStep 6350411 = 9525617) B9525617
theorem B1304153 : Blo 578813 1304153 := bstep (se 2 (by rfl) ⟨489057, by rfl⟩ : syracuseStep 1304153 = 978115) B978115
theorem B2090647 : Blo 578813 2090647 := bstep (se 1 (by rfl) ⟨1567985, by rfl⟩ : syracuseStep 2090647 = 3135971) B3135971
theorem B2483885 : Blo 578813 2483885 := bstep (se 3 (by rfl) ⟨465728, by rfl⟩ : syracuseStep 2483885 = 931457) B931457
theorem B1304243 : Blo 578813 1304243 := bstep (se 1 (by rfl) ⟨978182, by rfl⟩ : syracuseStep 1304243 = 1956365) B1956365
theorem B1304279 : Blo 578813 1304279 := bstep (se 1 (by rfl) ⟨978209, by rfl⟩ : syracuseStep 1304279 = 1956419) B1956419
theorem B2123543 : Blo 578813 2123543 := bstep (se 1 (by rfl) ⟨1592657, by rfl⟩ : syracuseStep 2123543 = 3185315) B3185315
theorem B1304459 : Blo 578813 1304459 := bstep (se 1 (by rfl) ⟨978344, by rfl⟩ : syracuseStep 1304459 = 1956689) B1956689
theorem B747403 : Blo 578813 747403 := bstep (se 1 (by rfl) ⟨560552, by rfl⟩ : syracuseStep 747403 = 1121105) B1121105
theorem B1304513 : Blo 578813 1304513 := bstep (se 2 (by rfl) ⟨489192, by rfl⟩ : syracuseStep 1304513 = 978385) B978385
theorem B976907 : Blo 578813 976907 := bstep (se 1 (by rfl) ⟨732680, by rfl⟩ : syracuseStep 976907 = 1465361) B1465361
theorem B5597201 : Blo 578813 5597201 := bstep (se 2 (by rfl) ⟨2098950, by rfl⟩ : syracuseStep 5597201 = 4197901) B4197901
theorem B1468439 : Blo 578813 1468439 := bstep (se 1 (by rfl) ⟨1101329, by rfl⟩ : syracuseStep 1468439 = 2202659) B2202659
theorem B977035 : Blo 578813 977035 := bstep (se 1 (by rfl) ⟨732776, by rfl⟩ : syracuseStep 977035 = 1465553) B1465553
theorem B3139735 : Blo 578813 3139735 := bstep (se 1 (by rfl) ⟨2354801, by rfl⟩ : syracuseStep 3139735 = 4709603) B4709603
theorem B1304729 : Blo 578813 1304729 := bstep (se 2 (by rfl) ⟨489273, by rfl⟩ : syracuseStep 1304729 = 978547) B978547
theorem B1304819 : Blo 578813 1304819 := bstep (se 1 (by rfl) ⟨978614, by rfl⟩ : syracuseStep 1304819 = 1957229) B1957229
theorem B1304855 : Blo 578813 1304855 := bstep (se 1 (by rfl) ⟨978641, by rfl⟩ : syracuseStep 1304855 = 1957283) B1957283
theorem B977177 : Blo 578813 977177 := bstep (se 2 (by rfl) ⟨366441, by rfl⟩ : syracuseStep 977177 = 732883) B732883
theorem B2484569 : Blo 578813 2484569 := bstep (se 2 (by rfl) ⟨931713, by rfl⟩ : syracuseStep 2484569 = 1863427) B1863427
theorem B977305 : Blo 578813 977305 := bstep (se 2 (by rfl) ⟨366489, by rfl⟩ : syracuseStep 977305 = 732979) B732979
theorem B1239475 : Blo 578813 1239475 := bstep (se 1 (by rfl) ⟨929606, by rfl⟩ : syracuseStep 1239475 = 1859213) B1859213
theorem B1206731 : Blo 578813 1206731 := bstep (se 1 (by rfl) ⟨905048, by rfl⟩ : syracuseStep 1206731 = 1810097) B1810097
theorem B1305035 : Blo 578813 1305035 := bstep (se 1 (by rfl) ⟨978776, by rfl⟩ : syracuseStep 1305035 = 1957553) B1957553
theorem B1305089 : Blo 578813 1305089 := bstep (se 2 (by rfl) ⟨489408, by rfl⟩ : syracuseStep 1305089 = 978817) B978817
theorem B1960523 : Blo 578813 1960523 := bstep (se 1 (by rfl) ⟨1470392, by rfl⟩ : syracuseStep 1960523 = 2940785) B2940785
theorem B1272407 : Blo 578813 1272407 := bstep (se 1 (by rfl) ⟨954305, by rfl⟩ : syracuseStep 1272407 = 1908611) B1908611
theorem B4418225 : Blo 578813 4418225 := bstep (se 2 (by rfl) ⟨1656834, by rfl⟩ : syracuseStep 4418225 = 3313669) B3313669
theorem B1305305 : Blo 578813 1305305 := bstep (se 2 (by rfl) ⟨489489, by rfl⟩ : syracuseStep 1305305 = 978979) B978979
theorem B1305395 : Blo 578813 1305395 := bstep (se 1 (by rfl) ⟨979046, by rfl⟩ : syracuseStep 1305395 = 1958093) B1958093
theorem B1469249 : Blo 578813 1469249 := bstep (se 2 (by rfl) ⟨550968, by rfl⟩ : syracuseStep 1469249 = 1101937) B1101937
theorem B1305431 : Blo 578813 1305431 := bstep (se 1 (by rfl) ⟨979073, by rfl⟩ : syracuseStep 1305431 = 1958147) B1958147
theorem B1960793 : Blo 578813 1960793 := bstep (se 2 (by rfl) ⟨735297, by rfl⟩ : syracuseStep 1960793 = 1470595) B1470595
theorem B5303191 : Blo 578813 5303191 := bstep (se 1 (by rfl) ⟨3977393, by rfl⟩ : syracuseStep 5303191 = 7954787) B7954787
theorem B1239961 : Blo 578813 1239961 := bstep (se 2 (by rfl) ⟨464985, by rfl⟩ : syracuseStep 1239961 = 929971) B929971
theorem B977879 : Blo 578813 977879 := bstep (se 1 (by rfl) ⟨733409, by rfl⟩ : syracuseStep 977879 = 1466819) B1466819
theorem B167668697 : Blo 578813 167668697 := bstep (se 2 (by rfl) ⟨62875761, by rfl⟩ : syracuseStep 167668697 = 125751523) B125751523
theorem B1305611 : Blo 578813 1305611 := bstep (se 1 (by rfl) ⟨979208, by rfl⟩ : syracuseStep 1305611 = 1958417) B1958417
theorem B10742797 : Blo 578813 10742797 := bstep (se 3 (by rfl) ⟨2014274, by rfl⟩ : syracuseStep 10742797 = 4028549) B4028549
theorem B1043507 : Blo 578813 1043507 := bstep (se 1 (by rfl) ⟨782630, by rfl⟩ : syracuseStep 1043507 = 1565261) B1565261
theorem B1305665 : Blo 578813 1305665 := bstep (se 2 (by rfl) ⟨489624, by rfl⟩ : syracuseStep 1305665 = 979249) B979249
theorem B978007 : Blo 578813 978007 := bstep (se 1 (by rfl) ⟨733505, by rfl⟩ : syracuseStep 978007 = 1467011) B1467011
theorem B4418711 : Blo 578813 4418711 := bstep (se 1 (by rfl) ⟨3314033, by rfl⟩ : syracuseStep 4418711 = 6628067) B6628067
theorem B1305881 : Blo 578813 1305881 := bstep (se 2 (by rfl) ⟨489705, by rfl⟩ : syracuseStep 1305881 = 979411) B979411
theorem B1469785 : Blo 578813 1469785 := bstep (se 2 (by rfl) ⟨551169, by rfl⟩ : syracuseStep 1469785 = 1102339) B1102339
theorem B2944349 : Blo 578813 2944349 := bstep (se 3 (by rfl) ⟨552065, by rfl⟩ : syracuseStep 2944349 = 1104131) B1104131
theorem B1305971 : Blo 578813 1305971 := bstep (se 1 (by rfl) ⟨979478, by rfl⟩ : syracuseStep 1305971 = 1958957) B1958957
theorem B1306007 : Blo 578813 1306007 := bstep (se 1 (by rfl) ⟨979505, by rfl⟩ : syracuseStep 1306007 = 1959011) B1959011
theorem B3304921 : Blo 578813 3304921 := bstep (se 2 (by rfl) ⟨1239345, by rfl⟩ : syracuseStep 3304921 = 2478691) B2478691
theorem B1961495 : Blo 578813 1961495 := bstep (se 1 (by rfl) ⟨1471121, by rfl⟩ : syracuseStep 1961495 = 2942243) B2942243
theorem B1306187 : Blo 578813 1306187 := bstep (se 1 (by rfl) ⟨979640, by rfl⟩ : syracuseStep 1306187 = 1959281) B1959281
theorem B2485835 : Blo 578813 2485835 := bstep (se 1 (by rfl) ⟨1864376, by rfl⟩ : syracuseStep 2485835 = 3728753) B3728753
theorem B1306241 : Blo 578813 1306241 := bstep (se 2 (by rfl) ⟨489840, by rfl⟩ : syracuseStep 1306241 = 979681) B979681
theorem B2125457 : Blo 578813 2125457 := bstep (se 2 (by rfl) ⟨797046, by rfl⟩ : syracuseStep 2125457 = 1594093) B1594093
theorem B2649773 : Blo 578813 2649773 := bstep (se 3 (by rfl) ⟨496832, by rfl⟩ : syracuseStep 2649773 = 993665) B993665
theorem B978635 : Blo 578813 978635 := bstep (se 1 (by rfl) ⟨733976, by rfl⟩ : syracuseStep 978635 = 1467953) B1467953
theorem B978763 : Blo 578813 978763 := bstep (se 1 (by rfl) ⟨734072, by rfl⟩ : syracuseStep 978763 = 1468145) B1468145
theorem B1306457 : Blo 578813 1306457 := bstep (se 2 (by rfl) ⟨489921, by rfl⟩ : syracuseStep 1306457 = 979843) B979843
theorem B1306547 : Blo 578813 1306547 := bstep (se 1 (by rfl) ⟨979910, by rfl⟩ : syracuseStep 1306547 = 1959821) B1959821
theorem B2486209 : Blo 578813 2486209 := bstep (se 2 (by rfl) ⟨932328, by rfl⟩ : syracuseStep 2486209 = 1864657) B1864657
theorem B1306583 : Blo 578813 1306583 := bstep (se 1 (by rfl) ⟨979937, by rfl⟩ : syracuseStep 1306583 = 1959875) B1959875
theorem B978905 : Blo 578813 978905 := bstep (se 2 (by rfl) ⟨367089, by rfl⟩ : syracuseStep 978905 = 734179) B734179
theorem B3731417 : Blo 578813 3731417 := bstep (se 2 (by rfl) ⟨1399281, by rfl⟩ : syracuseStep 3731417 = 2798563) B2798563
theorem B1044481 : Blo 578813 1044481 := bstep (se 2 (by rfl) ⟨391680, by rfl⟩ : syracuseStep 1044481 = 783361) B783361
theorem B651307 : Blo 578813 651307 := bstep (se 1 (by rfl) ⟨488480, by rfl⟩ : syracuseStep 651307 = 976961) B976961
theorem B5304365 : Blo 578813 5304365 := bstep (se 3 (by rfl) ⟨994568, by rfl⟩ : syracuseStep 5304365 = 1989137) B1989137
theorem B1962035 : Blo 578813 1962035 := bstep (se 1 (by rfl) ⟨1471526, by rfl⟩ : syracuseStep 1962035 = 2943053) B2943053
theorem B782425 : Blo 578813 782425 := bstep (se 2 (by rfl) ⟨293409, by rfl⟩ : syracuseStep 782425 = 586819) B586819
theorem B979033 : Blo 578813 979033 := bstep (se 2 (by rfl) ⟨367137, by rfl⟩ : syracuseStep 979033 = 734275) B734275
theorem B1306763 : Blo 578813 1306763 := bstep (se 1 (by rfl) ⟨980072, by rfl⟩ : syracuseStep 1306763 = 1960145) B1960145
theorem B651415 : Blo 578813 651415 := bstep (se 1 (by rfl) ⟨488561, by rfl⟩ : syracuseStep 651415 = 977123) B977123
theorem B1306817 : Blo 578813 1306817 := bstep (se 2 (by rfl) ⟨490056, by rfl⟩ : syracuseStep 1306817 = 980113) B980113
theorem B1241345 : Blo 578813 1241345 := bstep (se 2 (by rfl) ⟨465504, by rfl⟩ : syracuseStep 1241345 = 931009) B931009
theorem B2486551 : Blo 578813 2486551 := bstep (se 1 (by rfl) ⟨1864913, by rfl⟩ : syracuseStep 2486551 = 3729827) B3729827
theorem B1962305 : Blo 578813 1962305 := bstep (se 2 (by rfl) ⟨735864, by rfl⟩ : syracuseStep 1962305 = 1471729) B1471729
theorem B651595 : Blo 578813 651595 := bstep (se 1 (by rfl) ⟨488696, by rfl⟩ : syracuseStep 651595 = 977393) B977393
theorem B3305879 : Blo 578813 3305879 := bstep (se 1 (by rfl) ⟨2479409, by rfl⟩ : syracuseStep 3305879 = 4958819) B4958819
theorem B1307033 : Blo 578813 1307033 := bstep (se 2 (by rfl) ⟨490137, by rfl⟩ : syracuseStep 1307033 = 980275) B980275
theorem B1470899 : Blo 578813 1470899 := bstep (se 1 (by rfl) ⟨1103174, by rfl⟩ : syracuseStep 1470899 = 2206349) B2206349
theorem B651703 : Blo 578813 651703 := bstep (se 1 (by rfl) ⟨488777, by rfl⟩ : syracuseStep 651703 = 977555) B977555
theorem B1307123 : Blo 578813 1307123 := bstep (se 1 (by rfl) ⟨980342, by rfl⟩ : syracuseStep 1307123 = 1960685) B1960685
theorem B1307159 : Blo 578813 1307159 := bstep (se 1 (by rfl) ⟨980369, by rfl⟩ : syracuseStep 1307159 = 1960739) B1960739
theorem B1045079 : Blo 578813 1045079 := bstep (se 1 (by rfl) ⟨783809, by rfl⟩ : syracuseStep 1045079 = 1567619) B1567619
theorem B651883 : Blo 578813 651883 := bstep (se 1 (by rfl) ⟨488912, by rfl⟩ : syracuseStep 651883 = 977825) B977825
theorem B979607 : Blo 578813 979607 := bstep (se 1 (by rfl) ⟨734705, by rfl⟩ : syracuseStep 979607 = 1469411) B1469411
theorem B1340107 : Blo 578813 1340107 := bstep (se 1 (by rfl) ⟨1005080, by rfl⟩ : syracuseStep 1340107 = 2010161) B2010161
theorem B1307339 : Blo 578813 1307339 := bstep (se 1 (by rfl) ⟨980504, by rfl⟩ : syracuseStep 1307339 = 1961009) B1961009
theorem B651991 : Blo 578813 651991 := bstep (se 1 (by rfl) ⟨488993, by rfl⟩ : syracuseStep 651991 = 977987) B977987
theorem B1471193 : Blo 578813 1471193 := bstep (se 2 (by rfl) ⟨551697, by rfl⟩ : syracuseStep 1471193 = 1103395) B1103395
theorem B1307393 : Blo 578813 1307393 := bstep (se 2 (by rfl) ⟨490272, by rfl⟩ : syracuseStep 1307393 = 980545) B980545
theorem B1241867 : Blo 578813 1241867 := bstep (se 1 (by rfl) ⟨931400, by rfl⟩ : syracuseStep 1241867 = 1862801) B1862801
theorem B979735 : Blo 578813 979735 := bstep (se 1 (by rfl) ⟨734801, by rfl⟩ : syracuseStep 979735 = 1469603) B1469603
theorem B4715309 : Blo 578813 4715309 := bstep (se 3 (by rfl) ⟨884120, by rfl⟩ : syracuseStep 4715309 = 1768241) B1768241
theorem B1962845 : Blo 578813 1962845 := bstep (se 3 (by rfl) ⟨368033, by rfl⟩ : syracuseStep 1962845 = 736067) B736067
theorem B652171 : Blo 578813 652171 := bstep (se 1 (by rfl) ⟨489128, by rfl⟩ : syracuseStep 652171 = 978257) B978257
theorem B1307609 : Blo 578813 1307609 := bstep (se 2 (by rfl) ⟨490353, by rfl⟩ : syracuseStep 1307609 = 980707) B980707
theorem B652279 : Blo 578813 652279 := bstep (se 1 (by rfl) ⟨489209, by rfl⟩ : syracuseStep 652279 = 978419) B978419
theorem B1307699 : Blo 578813 1307699 := bstep (se 1 (by rfl) ⟨980774, by rfl⟩ : syracuseStep 1307699 = 1961549) B1961549
theorem B1078337 : Blo 578813 1078337 := bstep (se 2 (by rfl) ⟨404376, by rfl⟩ : syracuseStep 1078337 = 808753) B808753
theorem B1307735 : Blo 578813 1307735 := bstep (se 1 (by rfl) ⟨980801, by rfl⟩ : syracuseStep 1307735 = 1961603) B1961603
theorem B652459 : Blo 578813 652459 := bstep (se 1 (by rfl) ⟨489344, by rfl⟩ : syracuseStep 652459 = 978689) B978689
theorem B51573941 : Blo 578813 51573941 := bstep (se 5 (by rfl) ⟨2417528, by rfl⟩ : syracuseStep 51573941 = 4835057) B4835057
theorem B1307915 : Blo 578813 1307915 := bstep (se 1 (by rfl) ⟨980936, by rfl⟩ : syracuseStep 1307915 = 1961873) B1961873
theorem B652567 : Blo 578813 652567 := bstep (se 1 (by rfl) ⟨489425, by rfl⟩ : syracuseStep 652567 = 978851) B978851
theorem B1307969 : Blo 578813 1307969 := bstep (se 2 (by rfl) ⟨490488, by rfl⟩ : syracuseStep 1307969 = 980977) B980977
theorem B980363 : Blo 578813 980363 := bstep (se 1 (by rfl) ⟨735272, by rfl⟩ : syracuseStep 980363 = 1470545) B1470545
theorem B2946455 : Blo 578813 2946455 := bstep (se 1 (by rfl) ⟨2209841, by rfl⟩ : syracuseStep 2946455 = 4419683) B4419683
theorem B652747 : Blo 578813 652747 := bstep (se 1 (by rfl) ⟨489560, by rfl⟩ : syracuseStep 652747 = 979121) B979121
theorem B3143129 : Blo 578813 3143129 := bstep (se 2 (by rfl) ⟨1178673, by rfl⟩ : syracuseStep 3143129 = 2357347) B2357347
theorem B620011 : Blo 578813 620011 := bstep (se 1 (by rfl) ⟨465008, by rfl⟩ : syracuseStep 620011 = 930017) B930017
theorem B980491 : Blo 578813 980491 := bstep (se 1 (by rfl) ⟨735368, by rfl⟩ : syracuseStep 980491 = 1470737) B1470737
theorem B1308185 : Blo 578813 1308185 := bstep (se 2 (by rfl) ⟨490569, by rfl⟩ : syracuseStep 1308185 = 981139) B981139
theorem B652855 : Blo 578813 652855 := bstep (se 1 (by rfl) ⟨489641, by rfl⟩ : syracuseStep 652855 = 979283) B979283
theorem B1308275 : Blo 578813 1308275 := bstep (se 1 (by rfl) ⟨981206, by rfl⟩ : syracuseStep 1308275 = 1962413) B1962413
theorem B1308311 : Blo 578813 1308311 := bstep (se 1 (by rfl) ⟨981233, by rfl⟩ : syracuseStep 1308311 = 1962467) B1962467
theorem B980633 : Blo 578813 980633 := bstep (se 2 (by rfl) ⟨367737, by rfl⟩ : syracuseStep 980633 = 735475) B735475
theorem B653035 : Blo 578813 653035 := bstep (se 1 (by rfl) ⟨489776, by rfl⟩ : syracuseStep 653035 = 979553) B979553
theorem B980761 : Blo 578813 980761 := bstep (se 2 (by rfl) ⟨367785, by rfl⟩ : syracuseStep 980761 = 735571) B735571
theorem B1767233 : Blo 578813 1767233 := bstep (se 2 (by rfl) ⟨662712, by rfl⟩ : syracuseStep 1767233 = 1325425) B1325425
theorem B1308491 : Blo 578813 1308491 := bstep (se 1 (by rfl) ⟨981368, by rfl⟩ : syracuseStep 1308491 = 1962737) B1962737
theorem B653143 : Blo 578813 653143 := bstep (se 1 (by rfl) ⟨489857, by rfl⟩ : syracuseStep 653143 = 979715) B979715
theorem B1308545 : Blo 578813 1308545 := bstep (se 2 (by rfl) ⟨490704, by rfl⟩ : syracuseStep 1308545 = 981409) B981409
theorem B1570711 : Blo 578813 1570711 := bstep (se 1 (by rfl) ⟨1178033, by rfl⟩ : syracuseStep 1570711 = 2356067) B2356067
theorem B1963979 : Blo 578813 1963979 := bstep (se 1 (by rfl) ⟨1472984, by rfl⟩ : syracuseStep 1963979 = 2945969) B2945969
theorem B1243097 : Blo 578813 1243097 := bstep (se 2 (by rfl) ⟨466161, by rfl⟩ : syracuseStep 1243097 = 932323) B932323
theorem B653323 : Blo 578813 653323 := bstep (se 1 (by rfl) ⟨489992, by rfl⟩ : syracuseStep 653323 = 979985) B979985
theorem B8386577 : Blo 578813 8386577 := bstep (se 2 (by rfl) ⟨3144966, by rfl⟩ : syracuseStep 8386577 = 6289933) B6289933
theorem B4978705 : Blo 578813 4978705 := bstep (se 2 (by rfl) ⟨1867014, by rfl⟩ : syracuseStep 4978705 = 3734029) B3734029
theorem B1308761 : Blo 578813 1308761 := bstep (se 2 (by rfl) ⟨490785, by rfl⟩ : syracuseStep 1308761 = 981571) B981571
theorem B653431 : Blo 578813 653431 := bstep (se 1 (by rfl) ⟨490073, by rfl⟩ : syracuseStep 653431 = 980147) B980147
theorem B1308851 : Blo 578813 1308851 := bstep (se 1 (by rfl) ⟨981638, by rfl⟩ : syracuseStep 1308851 = 1963277) B1963277
theorem B2291915 : Blo 578813 2291915 := bstep (se 1 (by rfl) ⟨1718936, by rfl⟩ : syracuseStep 2291915 = 3437873) B3437873
theorem B2095307 : Blo 578813 2095307 := bstep (se 1 (by rfl) ⟨1571480, by rfl⟩ : syracuseStep 2095307 = 3142961) B3142961
theorem B1308887 : Blo 578813 1308887 := bstep (se 1 (by rfl) ⟨981665, by rfl⟩ : syracuseStep 1308887 = 1963331) B1963331
theorem B1964249 : Blo 578813 1964249 := bstep (se 2 (by rfl) ⟨736593, by rfl⟩ : syracuseStep 1964249 = 1473187) B1473187
theorem B1046807 : Blo 578813 1046807 := bstep (se 1 (by rfl) ⟨785105, by rfl⟩ : syracuseStep 1046807 = 1570211) B1570211
theorem B653611 : Blo 578813 653611 := bstep (se 1 (by rfl) ⟨490208, by rfl⟩ : syracuseStep 653611 = 980417) B980417
theorem B1472843 : Blo 578813 1472843 := bstep (se 1 (by rfl) ⟨1104632, by rfl⟩ : syracuseStep 1472843 = 2209265) B2209265
theorem B981335 : Blo 578813 981335 := bstep (se 1 (by rfl) ⟨736001, by rfl⟩ : syracuseStep 981335 = 1472003) B1472003
theorem B1243507 : Blo 578813 1243507 := bstep (se 1 (by rfl) ⟨932630, by rfl⟩ : syracuseStep 1243507 = 1865261) B1865261
theorem B1309067 : Blo 578813 1309067 := bstep (se 1 (by rfl) ⟨981800, by rfl⟩ : syracuseStep 1309067 = 1963601) B1963601
theorem B653719 : Blo 578813 653719 := bstep (se 1 (by rfl) ⟨490289, by rfl⟩ : syracuseStep 653719 = 980579) B980579
theorem B1309121 : Blo 578813 1309121 := bstep (se 2 (by rfl) ⟨490920, by rfl⟩ : syracuseStep 1309121 = 981841) B981841
theorem B981463 : Blo 578813 981463 := bstep (se 1 (by rfl) ⟨736097, by rfl⟩ : syracuseStep 981463 = 1472195) B1472195
theorem B2259479 : Blo 578813 2259479 := bstep (se 1 (by rfl) ⟨1694609, by rfl⟩ : syracuseStep 2259479 = 3389219) B3389219
theorem B653899 : Blo 578813 653899 := bstep (se 1 (by rfl) ⟨490424, by rfl⟩ : syracuseStep 653899 = 980849) B980849
theorem B7436893 : Blo 578813 7436893 := bstep (se 3 (by rfl) ⟨1394417, by rfl⟩ : syracuseStep 7436893 = 2788835) B2788835
theorem B1047169 : Blo 578813 1047169 := bstep (se 2 (by rfl) ⟨392688, by rfl⟩ : syracuseStep 1047169 = 785377) B785377
theorem B1309337 : Blo 578813 1309337 := bstep (se 2 (by rfl) ⟨491001, by rfl⟩ : syracuseStep 1309337 = 982003) B982003
theorem B654007 : Blo 578813 654007 := bstep (se 1 (by rfl) ⟨490505, by rfl⟩ : syracuseStep 654007 = 981011) B981011
theorem B1309427 : Blo 578813 1309427 := bstep (se 1 (by rfl) ⟨982070, by rfl⟩ : syracuseStep 1309427 = 1964141) B1964141
theorem B6617861 : Blo 578813 6617861 := bstep (se 4 (by rfl) ⟨620424, by rfl⟩ : syracuseStep 6617861 = 1240849) B1240849
theorem B2095895 : Blo 578813 2095895 := bstep (se 1 (by rfl) ⟨1571921, by rfl⟩ : syracuseStep 2095895 = 3143843) B3143843
theorem B1309463 : Blo 578813 1309463 := bstep (se 1 (by rfl) ⟨982097, by rfl⟩ : syracuseStep 1309463 = 1964195) B1964195
theorem B3308363 : Blo 578813 3308363 := bstep (se 1 (by rfl) ⟨2481272, by rfl⟩ : syracuseStep 3308363 = 4962545) B4962545
theorem B1243993 : Blo 578813 1243993 := bstep (se 2 (by rfl) ⟨466497, by rfl⟩ : syracuseStep 1243993 = 932995) B932995
theorem B654187 : Blo 578813 654187 := bstep (se 1 (by rfl) ⟨490640, by rfl⟩ : syracuseStep 654187 = 981281) B981281
theorem B1964951 : Blo 578813 1964951 := bstep (se 1 (by rfl) ⟨1473713, by rfl⟩ : syracuseStep 1964951 = 2947427) B2947427
theorem B1309643 : Blo 578813 1309643 := bstep (se 1 (by rfl) ⟨982232, by rfl⟩ : syracuseStep 1309643 = 1964465) B1964465
theorem B654295 : Blo 578813 654295 := bstep (se 1 (by rfl) ⟨490721, by rfl⟩ : syracuseStep 654295 = 981443) B981443
theorem B1309697 : Blo 578813 1309697 := bstep (se 2 (by rfl) ⟨491136, by rfl⟩ : syracuseStep 1309697 = 982273) B982273
theorem B17890379 : Blo 578813 17890379 := bstep (se 1 (by rfl) ⟨13417784, by rfl⟩ : syracuseStep 17890379 = 26835569) B26835569
theorem B982091 : Blo 578813 982091 := bstep (se 1 (by rfl) ⟨736568, by rfl⟩ : syracuseStep 982091 = 1473137) B1473137
theorem B654475 : Blo 578813 654475 := bstep (se 1 (by rfl) ⟨490856, by rfl⟩ : syracuseStep 654475 = 981713) B981713
theorem B5307569 : Blo 578813 5307569 := bstep (se 2 (by rfl) ⟨1990338, by rfl⟩ : syracuseStep 5307569 = 3980677) B3980677
theorem B982219 : Blo 578813 982219 := bstep (se 1 (by rfl) ⟨736664, by rfl⟩ : syracuseStep 982219 = 1473329) B1473329
theorem B1309913 : Blo 578813 1309913 := bstep (se 2 (by rfl) ⟨491217, by rfl⟩ : syracuseStep 1309913 = 982435) B982435
theorem B654583 : Blo 578813 654583 := bstep (se 1 (by rfl) ⟨490937, by rfl⟩ : syracuseStep 654583 = 981875) B981875
theorem B1473815 : Blo 578813 1473815 := bstep (se 1 (by rfl) ⟨1105361, by rfl⟩ : syracuseStep 1473815 = 2210723) B2210723
theorem B1310003 : Blo 578813 1310003 := bstep (se 1 (by rfl) ⟨982502, by rfl⟩ : syracuseStep 1310003 = 1965005) B1965005
theorem B1310039 : Blo 578813 1310039 := bstep (se 1 (by rfl) ⟨982529, by rfl⟩ : syracuseStep 1310039 = 1965059) B1965059
theorem B982361 : Blo 578813 982361 := bstep (se 2 (by rfl) ⟨368385, by rfl⟩ : syracuseStep 982361 = 736771) B736771
theorem B654763 : Blo 578813 654763 := bstep (se 1 (by rfl) ⟨491072, by rfl⟩ : syracuseStep 654763 = 982145) B982145
theorem B1965491 : Blo 578813 1965491 := bstep (se 1 (by rfl) ⟨1474118, by rfl⟩ : syracuseStep 1965491 = 2948237) B2948237
theorem B622027 : Blo 578813 622027 := bstep (se 1 (by rfl) ⟨466520, by rfl⟩ : syracuseStep 622027 = 933041) B933041
theorem B982489 : Blo 578813 982489 := bstep (se 2 (by rfl) ⟨368433, by rfl⟩ : syracuseStep 982489 = 736867) B736867
theorem B1310219 : Blo 578813 1310219 := bstep (se 1 (by rfl) ⟨982664, by rfl⟩ : syracuseStep 1310219 = 1965329) B1965329
theorem B654871 : Blo 578813 654871 := bstep (se 1 (by rfl) ⟨491153, by rfl⟩ : syracuseStep 654871 = 982307) B982307
theorem B1048115 : Blo 578813 1048115 := bstep (se 1 (by rfl) ⟨786086, by rfl⟩ : syracuseStep 1048115 = 1572173) B1572173
theorem B1310273 : Blo 578813 1310273 := bstep (se 2 (by rfl) ⟨491352, by rfl⟩ : syracuseStep 1310273 = 982705) B982705
theorem B1244737 : Blo 578813 1244737 := bstep (se 2 (by rfl) ⟨466776, by rfl⟩ : syracuseStep 1244737 = 933553) B933553
theorem B2981555 : Blo 578813 2981555 := bstep (se 1 (by rfl) ⟨2236166, by rfl⟩ : syracuseStep 2981555 = 4472333) B4472333
theorem B1965761 : Blo 578813 1965761 := bstep (se 2 (by rfl) ⟨737160, by rfl⟩ : syracuseStep 1965761 = 1474321) B1474321
theorem B655051 : Blo 578813 655051 := bstep (se 1 (by rfl) ⟨491288, by rfl⟩ : syracuseStep 655051 = 982577) B982577
theorem B14286577 : Blo 578813 14286577 := bstep (se 2 (by rfl) ⟨5357466, by rfl⟩ : syracuseStep 14286577 = 10714933) B10714933
theorem B1310489 : Blo 578813 1310489 := bstep (se 2 (by rfl) ⟨491433, by rfl⟩ : syracuseStep 1310489 = 982867) B982867
theorem B655159 : Blo 578813 655159 := bstep (se 1 (by rfl) ⟨491369, by rfl⟩ : syracuseStep 655159 = 982739) B982739
theorem B1310579 : Blo 578813 1310579 := bstep (se 1 (by rfl) ⟨982934, by rfl⟩ : syracuseStep 1310579 = 1965869) B1965869
theorem B1310615 : Blo 578813 1310615 := bstep (se 1 (by rfl) ⟨982961, by rfl⟩ : syracuseStep 1310615 = 1965923) B1965923
theorem B1572787 : Blo 578813 1572787 := bstep (se 1 (by rfl) ⟨1179590, by rfl⟩ : syracuseStep 1572787 = 2359181) B2359181
theorem B1474483 : Blo 578813 1474483 := bstep (se 1 (by rfl) ⟨1105862, by rfl⟩ : syracuseStep 1474483 = 2211725) B2211725
theorem B655339 : Blo 578813 655339 := bstep (se 1 (by rfl) ⟨491504, by rfl⟩ : syracuseStep 655339 = 983009) B983009
theorem B655375 : Blo 578813 655375 := bstep (se 1 (by rfl) ⟨491531, by rfl⟩ : syracuseStep 655375 = 983063) B983063
theorem B983083 : Blo 578813 983083 := bstep (se 1 (by rfl) ⟨737312, by rfl⟩ : syracuseStep 983083 = 1474625) B1474625
theorem B1310867 : Blo 578813 1310867 := bstep (se 1 (by rfl) ⟨983150, by rfl⟩ : syracuseStep 1310867 = 1966301) B1966301
theorem B983225 : Blo 578813 983225 := bstep (se 2 (by rfl) ⟨368709, by rfl⟩ : syracuseStep 983225 = 737419) B737419
theorem B1310921 : Blo 578813 1310921 := bstep (se 2 (by rfl) ⟨491595, by rfl⟩ : syracuseStep 1310921 = 983191) B983191
theorem B1474969 : Blo 578813 1474969 := bstep (se 2 (by rfl) ⟨553113, by rfl⟩ : syracuseStep 1474969 = 1106227) B1106227
theorem B1573391 : Blo 578813 1573391 := bstep (se 1 (by rfl) ⟨1180043, by rfl⟩ : syracuseStep 1573391 = 2360087) B2360087
theorem B1475131 : Blo 578813 1475131 := bstep (se 1 (by rfl) ⟨1106348, by rfl⟩ : syracuseStep 1475131 = 2212697) B2212697
theorem B6685249 : Blo 578813 6685249 := bstep (se 2 (by rfl) ⟨2506968, by rfl⟩ : syracuseStep 6685249 = 5013937) B5013937
theorem B1966679 : Blo 578813 1966679 := bstep (se 1 (by rfl) ⟨1475009, by rfl⟩ : syracuseStep 1966679 = 2950019) B2950019
theorem B3310253 : Blo 578813 3310253 := bstep (se 3 (by rfl) ⟨620672, by rfl⟩ : syracuseStep 3310253 = 1241345) B1241345
theorem B103383793 : Blo 578813 103383793 := bstep (se 2 (by rfl) ⟨38768922, by rfl⟩ : syracuseStep 103383793 = 77537845) B77537845
theorem B885563 : Blo 578813 885563 := bstep (se 1 (by rfl) ⟨664172, by rfl⟩ : syracuseStep 885563 = 1328345) B1328345
theorem B6456179 : Blo 578813 6456179 := bstep (se 1 (by rfl) ⟨4842134, by rfl⟩ : syracuseStep 6456179 = 9684269) B9684269
theorem B80413667 : Blo 578813 80413667 := bstep (se 1 (by rfl) ⟨60310250, by rfl⟩ : syracuseStep 80413667 = 120620501) B120620501
theorem B1049735 : Blo 578813 1049735 := bstep (se 1 (by rfl) ⟨787301, by rfl⟩ : syracuseStep 1049735 = 1574603) B1574603
theorem B4458557 : Blo 578813 4458557 := bstep (se 3 (by rfl) ⟨835979, by rfl⟩ : syracuseStep 4458557 = 1671959) B1671959
theorem B2787529 : Blo 578813 2787529 := bstep (se 2 (by rfl) ⟨1045323, by rfl⟩ : syracuseStep 2787529 = 2090647) B2090647
theorem B1771721 : Blo 578813 1771721 := bstep (se 2 (by rfl) ⟨664395, by rfl⟩ : syracuseStep 1771721 = 1328791) B1328791
theorem B4950821 : Blo 578813 4950821 := bstep (se 4 (by rfl) ⟨464139, by rfl⟩ : syracuseStep 4950821 = 928279) B928279
theorem B12881029 : Blo 578813 12881029 := bstep (se 4 (by rfl) ⟨1207596, by rfl⟩ : syracuseStep 12881029 = 2415193) B2415193
theorem B2198785 : Blo 578813 2198785 := bstep (se 2 (by rfl) ⟨824544, by rfl⟩ : syracuseStep 2198785 = 1649089) B1649089
theorem B1150507 : Blo 578813 1150507 := bstep (se 1 (by rfl) ⟨862880, by rfl⟩ : syracuseStep 1150507 = 1725761) B1725761
theorem B1412743 : Blo 578813 1412743 := bstep (se 1 (by rfl) ⟨1059557, by rfl⟩ : syracuseStep 1412743 = 2119115) B2119115
theorem B7147237 : Blo 578813 7147237 := bstep (se 4 (by rfl) ⟨670053, by rfl⟩ : syracuseStep 7147237 = 1340107) B1340107
theorem B7442225 : Blo 578813 7442225 := bstep (se 2 (by rfl) ⟨2790834, by rfl⟩ : syracuseStep 7442225 = 5581669) B5581669
theorem B14323729 : Blo 578813 14323729 := bstep (se 2 (by rfl) ⟨5371398, by rfl⟩ : syracuseStep 14323729 = 10742797) B10742797
theorem B6295639 : Blo 578813 6295639 := bstep (se 1 (by rfl) ⟨4721729, by rfl⟩ : syracuseStep 6295639 = 9443459) B9443459
theorem B6623693 : Blo 578813 6623693 := bstep (se 3 (by rfl) ⟨1241942, by rfl⟩ : syracuseStep 6623693 = 2483885) B2483885
theorem B627643 : Blo 578813 627643 := bstep (se 1 (by rfl) ⟨470732, by rfl⟩ : syracuseStep 627643 = 941465) B941465
theorem B13407437 : Blo 578813 13407437 := bstep (se 3 (by rfl) ⟨2513894, by rfl⟩ : syracuseStep 13407437 = 5027789) B5027789
theorem B3314945 : Blo 578813 3314945 := bstep (se 2 (by rfl) ⟨1243104, by rfl⟩ : syracuseStep 3314945 = 2486209) B2486209
theorem B3315401 : Blo 578813 3315401 := bstep (se 2 (by rfl) ⟨1243275, by rfl⟩ : syracuseStep 3315401 = 2486551) B2486551
theorem B825103 : Blo 578813 825103 := bstep (se 1 (by rfl) ⟨618827, by rfl⟩ : syracuseStep 825103 = 1237655) B1237655
theorem B3708787 : Blo 578813 3708787 := bstep (se 1 (by rfl) ⟨2781590, by rfl⟩ : syracuseStep 3708787 = 5563181) B5563181
theorem B825223 : Blo 578813 825223 := bstep (se 1 (by rfl) ⟨618917, by rfl⟩ : syracuseStep 825223 = 1237835) B1237835
theorem B2201687 : Blo 578813 2201687 := bstep (se 1 (by rfl) ⟨1651265, by rfl⟩ : syracuseStep 2201687 = 3302531) B3302531
theorem B5970323 : Blo 578813 5970323 := bstep (se 1 (by rfl) ⟨4477742, by rfl⟩ : syracuseStep 5970323 = 8955485) B8955485
theorem B2202173 : Blo 578813 2202173 := bstep (se 3 (by rfl) ⟨412907, by rfl⟩ : syracuseStep 2202173 = 825815) B825815
theorem B826681 : Blo 578813 826681 := bstep (se 2 (by rfl) ⟨310005, by rfl⟩ : syracuseStep 826681 = 620011) B620011
theorem B111779131 : Blo 578813 111779131 := bstep (se 1 (by rfl) ⟨83834348, by rfl⟩ : syracuseStep 111779131 = 167668697) B167668697
theorem B695671 : Blo 578813 695671 := bstep (se 1 (by rfl) ⟨521753, by rfl⟩ : syracuseStep 695671 = 1043507) B1043507
theorem B990599 : Blo 578813 990599 := bstep (se 1 (by rfl) ⟨742949, by rfl⟩ : syracuseStep 990599 = 1485899) B1485899
theorem B4398785 : Blo 578813 4398785 := bstep (se 2 (by rfl) ⟨1649544, by rfl⟩ : syracuseStep 4398785 = 3299089) B3299089
theorem B1416971 : Blo 578813 1416971 := bstep (se 1 (by rfl) ⟨1062728, by rfl⟩ : syracuseStep 1416971 = 2125457) B2125457
theorem B28712981 : Blo 578813 28712981 := bstep (se 6 (by rfl) ⟨672960, by rfl⟩ : syracuseStep 28712981 = 1345921) B1345921
theorem B2203919 : Blo 578813 2203919 := bstep (se 1 (by rfl) ⟨1652939, by rfl⟩ : syracuseStep 2203919 = 3305879) B3305879
theorem B696719 : Blo 578813 696719 := bstep (se 1 (by rfl) ⟨522539, by rfl⟩ : syracuseStep 696719 = 1045079) B1045079
theorem B11903449 : Blo 578813 11903449 := bstep (se 2 (by rfl) ⟨4463793, by rfl⟩ : syracuseStep 11903449 = 8927587) B8927587
theorem B827911 : Blo 578813 827911 := bstep (se 1 (by rfl) ⟨620933, by rfl⟩ : syracuseStep 827911 = 1241867) B1241867
theorem B34382627 : Blo 578813 34382627 := bstep (se 1 (by rfl) ⟨25786970, by rfl⟩ : syracuseStep 34382627 = 51573941) B51573941
theorem B828731 : Blo 578813 828731 := bstep (se 1 (by rfl) ⟨621548, by rfl⟩ : syracuseStep 828731 = 1243097) B1243097
theorem B697871 : Blo 578813 697871 := bstep (se 1 (by rfl) ⟨523403, by rfl⟩ : syracuseStep 697871 = 1046807) B1046807
theorem B927607 : Blo 578813 927607 := bstep (se 1 (by rfl) ⟨695705, by rfl⟩ : syracuseStep 927607 = 1391411) B1391411
theorem B2205575 : Blo 578813 2205575 := bstep (se 1 (by rfl) ⟨1654181, by rfl⟩ : syracuseStep 2205575 = 3308363) B3308363
theorem B829369 : Blo 578813 829369 := bstep (se 2 (by rfl) ⟨311013, by rfl⟩ : syracuseStep 829369 = 622027) B622027
theorem B993323 : Blo 578813 993323 := bstep (se 1 (by rfl) ⟨744992, by rfl⟩ : syracuseStep 993323 = 1489985) B1489985
theorem B1648907 : Blo 578813 1648907 := bstep (se 1 (by rfl) ⟨1236680, by rfl⟩ : syracuseStep 1648907 = 2473361) B2473361
theorem B19048769 : Blo 578813 19048769 := bstep (se 2 (by rfl) ⟨7143288, by rfl⟩ : syracuseStep 19048769 = 14286577) B14286577
theorem B698743 : Blo 578813 698743 := bstep (se 1 (by rfl) ⟨524057, by rfl⟩ : syracuseStep 698743 = 1048115) B1048115
theorem B14560181 : Blo 578813 14560181 := bstep (se 5 (by rfl) ⟨682508, by rfl⟩ : syracuseStep 14560181 = 1365017) B1365017
theorem B4402187 : Blo 578813 4402187 := bstep (se 1 (by rfl) ⟨3301640, by rfl⟩ : syracuseStep 4402187 = 6603281) B6603281
theorem B4172933 : Blo 578813 4172933 := bstep (se 4 (by rfl) ⟨391212, by rfl⟩ : syracuseStep 4172933 = 782425) B782425
theorem B2207351 : Blo 578813 2207351 := bstep (se 1 (by rfl) ⟨1655513, by rfl⟩ : syracuseStep 2207351 = 3311027) B3311027
theorem B1879841 : Blo 578813 1879841 := bstep (se 2 (by rfl) ⟨704940, by rfl⟩ : syracuseStep 1879841 = 1409881) B1409881
theorem B1650547 : Blo 578813 1650547 := bstep (se 1 (by rfl) ⟨1237910, by rfl⟩ : syracuseStep 1650547 = 2475821) B2475821
theorem B1650775 : Blo 578813 1650775 := bstep (se 1 (by rfl) ⟨1238081, by rfl⟩ : syracuseStep 1650775 = 2476163) B2476163
theorem B733303 : Blo 578813 733303 := bstep (se 1 (by rfl) ⟨549977, by rfl⟩ : syracuseStep 733303 = 1099955) B1099955
theorem B733627 : Blo 578813 733627 := bstep (se 1 (by rfl) ⟨550220, by rfl⟩ : syracuseStep 733627 = 1100441) B1100441
theorem B3387869 : Blo 578813 3387869 := bstep (se 3 (by rfl) ⟨635225, by rfl⟩ : syracuseStep 3387869 = 1270451) B1270451
theorem B2208323 : Blo 578813 2208323 := bstep (se 1 (by rfl) ⟨1656242, by rfl⟩ : syracuseStep 2208323 = 3312485) B3312485
theorem B4404131 : Blo 578813 4404131 := bstep (se 1 (by rfl) ⟨3303098, by rfl⟩ : syracuseStep 4404131 = 6606197) B6606197
theorem B734123 : Blo 578813 734123 := bstep (se 1 (by rfl) ⟨550592, by rfl⟩ : syracuseStep 734123 = 1101185) B1101185
theorem B2208779 : Blo 578813 2208779 := bstep (se 1 (by rfl) ⟨1656584, by rfl⟩ : syracuseStep 2208779 = 3313169) B3313169
theorem B6698371 : Blo 578813 6698371 := bstep (se 1 (by rfl) ⟨5023778, by rfl⟩ : syracuseStep 6698371 = 10047557) B10047557
theorem B734599 : Blo 578813 734599 := bstep (se 1 (by rfl) ⟨550949, by rfl⟩ : syracuseStep 734599 = 1101899) B1101899
theorem B1652359 : Blo 578813 1652359 := bstep (se 1 (by rfl) ⟨1239269, by rfl⟩ : syracuseStep 1652359 = 2478539) B2478539
theorem B14137163 : Blo 578813 14137163 := bstep (se 1 (by rfl) ⟨10602872, by rfl⟩ : syracuseStep 14137163 = 21205745) B21205745
theorem B735095 : Blo 578813 735095 := bstep (se 1 (by rfl) ⟨551321, by rfl⟩ : syracuseStep 735095 = 1102643) B1102643
theorem B2930579 : Blo 578813 2930579 := bstep (se 1 (by rfl) ⟨2197934, by rfl⟩ : syracuseStep 2930579 = 4395869) B4395869
theorem B1652633 : Blo 578813 1652633 := bstep (se 2 (by rfl) ⟨619737, by rfl⟩ : syracuseStep 1652633 = 1239475) B1239475
theorem B735247 : Blo 578813 735247 := bstep (se 1 (by rfl) ⟨551435, by rfl⟩ : syracuseStep 735247 = 1102871) B1102871
theorem B1390727 : Blo 578813 1390727 := bstep (se 1 (by rfl) ⟨1043045, by rfl⟩ : syracuseStep 1390727 = 2086091) B2086091
theorem B735419 : Blo 578813 735419 := bstep (se 1 (by rfl) ⟨551564, by rfl⟩ : syracuseStep 735419 = 1103129) B1103129
theorem B1718561 : Blo 578813 1718561 := bstep (se 2 (by rfl) ⟨644460, by rfl⟩ : syracuseStep 1718561 = 1288921) B1288921
theorem B1063315 : Blo 578813 1063315 := bstep (se 1 (by rfl) ⟨797486, by rfl⟩ : syracuseStep 1063315 = 1594973) B1594973
theorem B1653281 : Blo 578813 1653281 := bstep (se 2 (by rfl) ⟨619980, by rfl⟩ : syracuseStep 1653281 = 1239961) B1239961
theorem B3587159 : Blo 578813 3587159 := bstep (se 1 (by rfl) ⟨2690369, by rfl⟩ : syracuseStep 3587159 = 5380739) B5380739
theorem B2210935 : Blo 578813 2210935 := bstep (se 1 (by rfl) ⟨1658201, by rfl⟩ : syracuseStep 2210935 = 3316403) B3316403
theorem B736391 : Blo 578813 736391 := bstep (se 1 (by rfl) ⟨552293, by rfl⟩ : syracuseStep 736391 = 1104587) B1104587
theorem B3980461 : Blo 578813 3980461 := bstep (se 3 (by rfl) ⟨746336, by rfl⟩ : syracuseStep 3980461 = 1492673) B1492673
theorem B3718345 : Blo 578813 3718345 := bstep (se 2 (by rfl) ⟨1394379, by rfl⟩ : syracuseStep 3718345 = 2788759) B2788759
theorem B4406561 : Blo 578813 4406561 := bstep (se 2 (by rfl) ⟨1652460, by rfl⟩ : syracuseStep 4406561 = 3304921) B3304921
theorem B1654283 : Blo 578813 1654283 := bstep (se 1 (by rfl) ⟨1240712, by rfl⟩ : syracuseStep 1654283 = 2481425) B2481425
theorem B933419 : Blo 578813 933419 := bstep (se 1 (by rfl) ⟨700064, by rfl⟩ : syracuseStep 933419 = 1400129) B1400129
theorem B737039 : Blo 578813 737039 := bstep (se 1 (by rfl) ⟨552779, by rfl⟩ : syracuseStep 737039 = 1105559) B1105559
theorem B868283 : Blo 578813 868283 := bstep (se 1 (by rfl) ⟨651212, by rfl⟩ : syracuseStep 868283 = 1302425) B1302425
theorem B3358685 : Blo 578813 3358685 := bstep (se 3 (by rfl) ⟨629753, by rfl⟩ : syracuseStep 3358685 = 1259507) B1259507
theorem B868343 : Blo 578813 868343 := bstep (se 1 (by rfl) ⟨651257, by rfl⟩ : syracuseStep 868343 = 1302515) B1302515
theorem B1392641 : Blo 578813 1392641 := bstep (se 2 (by rfl) ⟨522240, by rfl⟩ : syracuseStep 1392641 = 1044481) B1044481
theorem B2211851 : Blo 578813 2211851 := bstep (se 1 (by rfl) ⟨1658888, by rfl⟩ : syracuseStep 2211851 = 3317777) B3317777
theorem B868367 : Blo 578813 868367 := bstep (se 1 (by rfl) ⟨651275, by rfl⟩ : syracuseStep 868367 = 1302551) B1302551
theorem B868409 : Blo 578813 868409 := bstep (se 2 (by rfl) ⟨325653, by rfl⟩ : syracuseStep 868409 = 651307) B651307
theorem B2211907 : Blo 578813 2211907 := bstep (se 1 (by rfl) ⟨1658930, by rfl⟩ : syracuseStep 2211907 = 3317861) B3317861
theorem B1392727 : Blo 578813 1392727 := bstep (se 1 (by rfl) ⟨1044545, by rfl⟩ : syracuseStep 1392727 = 2089091) B2089091
theorem B868487 : Blo 578813 868487 := bstep (se 1 (by rfl) ⟨651365, by rfl⟩ : syracuseStep 868487 = 1302731) B1302731
theorem B868523 : Blo 578813 868523 := bstep (se 1 (by rfl) ⟨651392, by rfl⟩ : syracuseStep 868523 = 1302785) B1302785
theorem B868553 : Blo 578813 868553 := bstep (se 2 (by rfl) ⟨325707, by rfl⟩ : syracuseStep 868553 = 651415) B651415
theorem B4407533 : Blo 578813 4407533 := bstep (se 3 (by rfl) ⟨826412, by rfl⟩ : syracuseStep 4407533 = 1652825) B1652825
theorem B868667 : Blo 578813 868667 := bstep (se 1 (by rfl) ⟨651500, by rfl⟩ : syracuseStep 868667 = 1303001) B1303001
theorem B2212211 : Blo 578813 2212211 := bstep (se 1 (by rfl) ⟨1659158, by rfl⟩ : syracuseStep 2212211 = 3318317) B3318317
theorem B868727 : Blo 578813 868727 := bstep (se 1 (by rfl) ⟨651545, by rfl⟩ : syracuseStep 868727 = 1303091) B1303091
theorem B868751 : Blo 578813 868751 := bstep (se 1 (by rfl) ⟨651563, by rfl⟩ : syracuseStep 868751 = 1303127) B1303127
theorem B2474387 : Blo 578813 2474387 := bstep (se 1 (by rfl) ⟨1855790, by rfl⟩ : syracuseStep 2474387 = 3711581) B3711581
theorem B868793 : Blo 578813 868793 := bstep (se 2 (by rfl) ⟨325797, by rfl⟩ : syracuseStep 868793 = 651595) B651595
theorem B868871 : Blo 578813 868871 := bstep (se 1 (by rfl) ⟨651653, by rfl⟩ : syracuseStep 868871 = 1303307) B1303307
theorem B6111773 : Blo 578813 6111773 := bstep (se 3 (by rfl) ⟨1145957, by rfl⟩ : syracuseStep 6111773 = 2291915) B2291915
theorem B868907 : Blo 578813 868907 := bstep (se 1 (by rfl) ⟨651680, by rfl⟩ : syracuseStep 868907 = 1303361) B1303361
theorem B868937 : Blo 578813 868937 := bstep (se 2 (by rfl) ⟨325851, by rfl⟩ : syracuseStep 868937 = 651703) B651703
theorem B4473463 : Blo 578813 4473463 := bstep (se 1 (by rfl) ⟨3355097, by rfl⟩ : syracuseStep 4473463 = 6710195) B6710195
theorem B836281 : Blo 578813 836281 := bstep (se 2 (by rfl) ⟨313605, by rfl⟩ : syracuseStep 836281 = 627211) B627211
theorem B869051 : Blo 578813 869051 := bstep (se 1 (by rfl) ⟨651788, by rfl⟩ : syracuseStep 869051 = 1303577) B1303577
theorem B869111 : Blo 578813 869111 := bstep (se 1 (by rfl) ⟨651833, by rfl⟩ : syracuseStep 869111 = 1303667) B1303667
theorem B869135 : Blo 578813 869135 := bstep (se 1 (by rfl) ⟨651851, by rfl⟩ : syracuseStep 869135 = 1303703) B1303703
theorem B869177 : Blo 578813 869177 := bstep (se 2 (by rfl) ⟨325941, by rfl⟩ : syracuseStep 869177 = 651883) B651883
theorem B2212667 : Blo 578813 2212667 := bstep (se 1 (by rfl) ⟨1659500, by rfl⟩ : syracuseStep 2212667 = 3319001) B3319001
theorem B869255 : Blo 578813 869255 := bstep (se 1 (by rfl) ⟨651941, by rfl⟩ : syracuseStep 869255 = 1303883) B1303883
theorem B3130265 : Blo 578813 3130265 := bstep (se 2 (by rfl) ⟨1173849, by rfl⟩ : syracuseStep 3130265 = 2347699) B2347699
theorem B2933657 : Blo 578813 2933657 := bstep (se 2 (by rfl) ⟨1100121, by rfl⟩ : syracuseStep 2933657 = 2200243) B2200243
theorem B869291 : Blo 578813 869291 := bstep (se 1 (by rfl) ⟨651968, by rfl⟩ : syracuseStep 869291 = 1303937) B1303937
theorem B869321 : Blo 578813 869321 := bstep (se 2 (by rfl) ⟨325995, by rfl⟩ : syracuseStep 869321 = 651991) B651991
theorem B869435 : Blo 578813 869435 := bstep (se 1 (by rfl) ⟨652076, by rfl⟩ : syracuseStep 869435 = 1304153) B1304153
theorem B869495 : Blo 578813 869495 := bstep (se 1 (by rfl) ⟨652121, by rfl⟩ : syracuseStep 869495 = 1304243) B1304243
theorem B869519 : Blo 578813 869519 := bstep (se 1 (by rfl) ⟨652139, by rfl⟩ : syracuseStep 869519 = 1304279) B1304279
theorem B1098937 : Blo 578813 1098937 := bstep (se 2 (by rfl) ⟨412101, by rfl⟩ : syracuseStep 1098937 = 824203) B824203
theorem B869561 : Blo 578813 869561 := bstep (se 2 (by rfl) ⟨326085, by rfl⟩ : syracuseStep 869561 = 652171) B652171
theorem B869639 : Blo 578813 869639 := bstep (se 1 (by rfl) ⟨652229, by rfl⟩ : syracuseStep 869639 = 1304459) B1304459
theorem B869675 : Blo 578813 869675 := bstep (se 1 (by rfl) ⟨652256, by rfl⟩ : syracuseStep 869675 = 1304513) B1304513
theorem B869705 : Blo 578813 869705 := bstep (se 2 (by rfl) ⟨326139, by rfl⟩ : syracuseStep 869705 = 652279) B652279
theorem B869819 : Blo 578813 869819 := bstep (se 1 (by rfl) ⟨652364, by rfl⟩ : syracuseStep 869819 = 1304729) B1304729
theorem B869879 : Blo 578813 869879 := bstep (se 1 (by rfl) ⟨652409, by rfl⟩ : syracuseStep 869879 = 1304819) B1304819
theorem B869903 : Blo 578813 869903 := bstep (se 1 (by rfl) ⟨652427, by rfl⟩ : syracuseStep 869903 = 1304855) B1304855
theorem B869945 : Blo 578813 869945 := bstep (se 2 (by rfl) ⟨326229, by rfl⟩ : syracuseStep 869945 = 652459) B652459
theorem B1656379 : Blo 578813 1656379 := bstep (se 1 (by rfl) ⟨1242284, by rfl⟩ : syracuseStep 1656379 = 2484569) B2484569
theorem B3393085 : Blo 578813 3393085 := bstep (se 3 (by rfl) ⟨636203, by rfl⟩ : syracuseStep 3393085 = 1272407) B1272407
theorem B804487 : Blo 578813 804487 := bstep (se 1 (by rfl) ⟨603365, by rfl⟩ : syracuseStep 804487 = 1206731) B1206731
theorem B870023 : Blo 578813 870023 := bstep (se 1 (by rfl) ⟨652517, by rfl⟩ : syracuseStep 870023 = 1305035) B1305035
theorem B870059 : Blo 578813 870059 := bstep (se 1 (by rfl) ⟨652544, by rfl⟩ : syracuseStep 870059 = 1305089) B1305089
theorem B870089 : Blo 578813 870089 := bstep (se 2 (by rfl) ⟨326283, by rfl⟩ : syracuseStep 870089 = 652567) B652567
theorem B870203 : Blo 578813 870203 := bstep (se 1 (by rfl) ⟨652652, by rfl⟩ : syracuseStep 870203 = 1305305) B1305305
theorem B870263 : Blo 578813 870263 := bstep (se 1 (by rfl) ⟨652697, by rfl⟩ : syracuseStep 870263 = 1305395) B1305395
theorem B870287 : Blo 578813 870287 := bstep (se 1 (by rfl) ⟨652715, by rfl⟩ : syracuseStep 870287 = 1305431) B1305431
theorem B870329 : Blo 578813 870329 := bstep (se 2 (by rfl) ⟨326373, by rfl⟩ : syracuseStep 870329 = 652747) B652747
theorem B870407 : Blo 578813 870407 := bstep (se 1 (by rfl) ⟨652805, by rfl⟩ : syracuseStep 870407 = 1305611) B1305611
theorem B870443 : Blo 578813 870443 := bstep (se 1 (by rfl) ⟨652832, by rfl⟩ : syracuseStep 870443 = 1305665) B1305665
theorem B870473 : Blo 578813 870473 := bstep (se 2 (by rfl) ⟨326427, by rfl⟩ : syracuseStep 870473 = 652855) B652855
theorem B4409477 : Blo 578813 4409477 := bstep (se 4 (by rfl) ⟨413388, by rfl⟩ : syracuseStep 4409477 = 826777) B826777
theorem B870587 : Blo 578813 870587 := bstep (se 1 (by rfl) ⟨652940, by rfl⟩ : syracuseStep 870587 = 1305881) B1305881
theorem B870647 : Blo 578813 870647 := bstep (se 1 (by rfl) ⟨652985, by rfl⟩ : syracuseStep 870647 = 1305971) B1305971
theorem B870671 : Blo 578813 870671 := bstep (se 1 (by rfl) ⟨653003, by rfl⟩ : syracuseStep 870671 = 1306007) B1306007
theorem B870713 : Blo 578813 870713 := bstep (se 2 (by rfl) ⟨326517, by rfl⟩ : syracuseStep 870713 = 653035) B653035
theorem B2476403 : Blo 578813 2476403 := bstep (se 1 (by rfl) ⟨1857302, by rfl⟩ : syracuseStep 2476403 = 3714605) B3714605
theorem B870791 : Blo 578813 870791 := bstep (se 1 (by rfl) ⟨653093, by rfl⟩ : syracuseStep 870791 = 1306187) B1306187
theorem B1657223 : Blo 578813 1657223 := bstep (se 1 (by rfl) ⟨1242917, by rfl⟩ : syracuseStep 1657223 = 2485835) B2485835
theorem B870827 : Blo 578813 870827 := bstep (se 1 (by rfl) ⟨653120, by rfl⟩ : syracuseStep 870827 = 1306241) B1306241
theorem B870857 : Blo 578813 870857 := bstep (se 2 (by rfl) ⟨326571, by rfl⟩ : syracuseStep 870857 = 653143) B653143
theorem B870971 : Blo 578813 870971 := bstep (se 1 (by rfl) ⟨653228, by rfl⟩ : syracuseStep 870971 = 1306457) B1306457
theorem B871031 : Blo 578813 871031 := bstep (se 1 (by rfl) ⟨653273, by rfl⟩ : syracuseStep 871031 = 1306547) B1306547
theorem B871055 : Blo 578813 871055 := bstep (se 1 (by rfl) ⟨653291, by rfl⟩ : syracuseStep 871055 = 1306583) B1306583
theorem B1493657 : Blo 578813 1493657 := bstep (se 2 (by rfl) ⟨560121, by rfl⟩ : syracuseStep 1493657 = 1120243) B1120243
theorem B871097 : Blo 578813 871097 := bstep (se 2 (by rfl) ⟨326661, by rfl⟩ : syracuseStep 871097 = 653323) B653323
theorem B6638273 : Blo 578813 6638273 := bstep (se 2 (by rfl) ⟨2489352, by rfl⟩ : syracuseStep 6638273 = 4978705) B4978705
theorem B871175 : Blo 578813 871175 := bstep (se 1 (by rfl) ⟨653381, by rfl⟩ : syracuseStep 871175 = 1306763) B1306763
theorem B871211 : Blo 578813 871211 := bstep (se 1 (by rfl) ⟨653408, by rfl⟩ : syracuseStep 871211 = 1306817) B1306817
theorem B871241 : Blo 578813 871241 := bstep (se 2 (by rfl) ⟨326715, by rfl⟩ : syracuseStep 871241 = 653431) B653431
theorem B15944597 : Blo 578813 15944597 := bstep (se 6 (by rfl) ⟨373701, by rfl⟩ : syracuseStep 15944597 = 747403) B747403
theorem B1100729 : Blo 578813 1100729 := bstep (se 2 (by rfl) ⟨412773, by rfl⟩ : syracuseStep 1100729 = 825547) B825547
theorem B871355 : Blo 578813 871355 := bstep (se 1 (by rfl) ⟨653516, by rfl⟩ : syracuseStep 871355 = 1307033) B1307033
theorem B871415 : Blo 578813 871415 := bstep (se 1 (by rfl) ⟨653561, by rfl⟩ : syracuseStep 871415 = 1307123) B1307123
theorem B871439 : Blo 578813 871439 := bstep (se 1 (by rfl) ⟨653579, by rfl⟩ : syracuseStep 871439 = 1307159) B1307159
theorem B871481 : Blo 578813 871481 := bstep (se 2 (by rfl) ⟨326805, by rfl⟩ : syracuseStep 871481 = 653611) B653611
theorem B871559 : Blo 578813 871559 := bstep (se 1 (by rfl) ⟨653669, by rfl⟩ : syracuseStep 871559 = 1307339) B1307339
theorem B1658009 : Blo 578813 1658009 := bstep (se 2 (by rfl) ⟨621753, by rfl⟩ : syracuseStep 1658009 = 1243507) B1243507
theorem B871595 : Blo 578813 871595 := bstep (se 1 (by rfl) ⟨653696, by rfl⟩ : syracuseStep 871595 = 1307393) B1307393
theorem B871625 : Blo 578813 871625 := bstep (se 2 (by rfl) ⟨326859, by rfl⟩ : syracuseStep 871625 = 653719) B653719
theorem B871739 : Blo 578813 871739 := bstep (se 1 (by rfl) ⟨653804, by rfl⟩ : syracuseStep 871739 = 1307609) B1307609
theorem B871799 : Blo 578813 871799 := bstep (se 1 (by rfl) ⟨653849, by rfl⟩ : syracuseStep 871799 = 1307699) B1307699
theorem B871823 : Blo 578813 871823 := bstep (se 1 (by rfl) ⟨653867, by rfl⟩ : syracuseStep 871823 = 1307735) B1307735
theorem B2936249 : Blo 578813 2936249 := bstep (se 2 (by rfl) ⟨1101093, by rfl⟩ : syracuseStep 2936249 = 2202187) B2202187
theorem B871865 : Blo 578813 871865 := bstep (se 2 (by rfl) ⟨326949, by rfl⟩ : syracuseStep 871865 = 653899) B653899
theorem B9915857 : Blo 578813 9915857 := bstep (se 2 (by rfl) ⟨3718446, by rfl⟩ : syracuseStep 9915857 = 7436893) B7436893
theorem B1396225 : Blo 578813 1396225 := bstep (se 2 (by rfl) ⟨523584, by rfl⟩ : syracuseStep 1396225 = 1047169) B1047169
theorem B871943 : Blo 578813 871943 := bstep (se 1 (by rfl) ⟨653957, by rfl⟩ : syracuseStep 871943 = 1307915) B1307915
theorem B871979 : Blo 578813 871979 := bstep (se 1 (by rfl) ⟨653984, by rfl⟩ : syracuseStep 871979 = 1307969) B1307969
theorem B6868547 : Blo 578813 6868547 := bstep (se 1 (by rfl) ⟨5151410, by rfl⟩ : syracuseStep 6868547 = 10302821) B10302821
theorem B872009 : Blo 578813 872009 := bstep (se 2 (by rfl) ⟨327003, by rfl⟩ : syracuseStep 872009 = 654007) B654007
theorem B872123 : Blo 578813 872123 := bstep (se 1 (by rfl) ⟨654092, by rfl⟩ : syracuseStep 872123 = 1308185) B1308185
theorem B872183 : Blo 578813 872183 := bstep (se 1 (by rfl) ⟨654137, by rfl⟩ : syracuseStep 872183 = 1308275) B1308275
theorem B872207 : Blo 578813 872207 := bstep (se 1 (by rfl) ⟨654155, by rfl⟩ : syracuseStep 872207 = 1308311) B1308311
theorem B1658657 : Blo 578813 1658657 := bstep (se 2 (by rfl) ⟨621996, by rfl⟩ : syracuseStep 1658657 = 1243993) B1243993
theorem B872249 : Blo 578813 872249 := bstep (se 2 (by rfl) ⟨327093, by rfl⟩ : syracuseStep 872249 = 654187) B654187
theorem B872327 : Blo 578813 872327 := bstep (se 1 (by rfl) ⟨654245, by rfl⟩ : syracuseStep 872327 = 1308491) B1308491
theorem B872363 : Blo 578813 872363 := bstep (se 1 (by rfl) ⟨654272, by rfl⟩ : syracuseStep 872363 = 1308545) B1308545
theorem B872393 : Blo 578813 872393 := bstep (se 2 (by rfl) ⟨327147, by rfl⟩ : syracuseStep 872393 = 654295) B654295
theorem B5591051 : Blo 578813 5591051 := bstep (se 1 (by rfl) ⟨4193288, by rfl⟩ : syracuseStep 5591051 = 8386577) B8386577
theorem B872507 : Blo 578813 872507 := bstep (se 1 (by rfl) ⟨654380, by rfl⟩ : syracuseStep 872507 = 1308761) B1308761
theorem B872567 : Blo 578813 872567 := bstep (se 1 (by rfl) ⟨654425, by rfl⟩ : syracuseStep 872567 = 1308851) B1308851
theorem B1396871 : Blo 578813 1396871 := bstep (se 1 (by rfl) ⟨1047653, by rfl⟩ : syracuseStep 1396871 = 2095307) B2095307
theorem B872591 : Blo 578813 872591 := bstep (se 1 (by rfl) ⟨654443, by rfl⟩ : syracuseStep 872591 = 1308887) B1308887
theorem B872633 : Blo 578813 872633 := bstep (se 2 (by rfl) ⟨327237, by rfl⟩ : syracuseStep 872633 = 654475) B654475
theorem B872711 : Blo 578813 872711 := bstep (se 1 (by rfl) ⟨654533, by rfl⟩ : syracuseStep 872711 = 1309067) B1309067
theorem B872747 : Blo 578813 872747 := bstep (se 1 (by rfl) ⟨654560, by rfl⟩ : syracuseStep 872747 = 1309121) B1309121
theorem B872777 : Blo 578813 872777 := bstep (se 2 (by rfl) ⟨327291, by rfl⟩ : syracuseStep 872777 = 654583) B654583
theorem B872891 : Blo 578813 872891 := bstep (se 1 (by rfl) ⟨654668, by rfl⟩ : syracuseStep 872891 = 1309337) B1309337
theorem B7066061 : Blo 578813 7066061 := bstep (se 3 (by rfl) ⟨1324886, by rfl⟩ : syracuseStep 7066061 = 2649773) B2649773
theorem B872951 : Blo 578813 872951 := bstep (se 1 (by rfl) ⟨654713, by rfl⟩ : syracuseStep 872951 = 1309427) B1309427
theorem B4411907 : Blo 578813 4411907 := bstep (se 1 (by rfl) ⟨3308930, by rfl⟩ : syracuseStep 4411907 = 6617861) B6617861
theorem B1397263 : Blo 578813 1397263 := bstep (se 1 (by rfl) ⟨1047947, by rfl⟩ : syracuseStep 1397263 = 2095895) B2095895
theorem B872975 : Blo 578813 872975 := bstep (se 1 (by rfl) ⟨654731, by rfl⟩ : syracuseStep 872975 = 1309463) B1309463
theorem B873017 : Blo 578813 873017 := bstep (se 2 (by rfl) ⟨327381, by rfl⟩ : syracuseStep 873017 = 654763) B654763
theorem B873095 : Blo 578813 873095 := bstep (se 1 (by rfl) ⟨654821, by rfl⟩ : syracuseStep 873095 = 1309643) B1309643
theorem B873131 : Blo 578813 873131 := bstep (se 1 (by rfl) ⟨654848, by rfl⟩ : syracuseStep 873131 = 1309697) B1309697
theorem B2937545 : Blo 578813 2937545 := bstep (se 2 (by rfl) ⟨1101579, by rfl⟩ : syracuseStep 2937545 = 2203159) B2203159
theorem B873161 : Blo 578813 873161 := bstep (se 2 (by rfl) ⟨327435, by rfl⟩ : syracuseStep 873161 = 654871) B654871
theorem B1659649 : Blo 578813 1659649 := bstep (se 2 (by rfl) ⟨622368, by rfl⟩ : syracuseStep 1659649 = 1244737) B1244737
theorem B2478863 : Blo 578813 2478863 := bstep (se 1 (by rfl) ⟨1859147, by rfl⟩ : syracuseStep 2478863 = 3718295) B3718295
theorem B873275 : Blo 578813 873275 := bstep (se 1 (by rfl) ⟨654956, by rfl⟩ : syracuseStep 873275 = 1309913) B1309913
theorem B873335 : Blo 578813 873335 := bstep (se 1 (by rfl) ⟨655001, by rfl⟩ : syracuseStep 873335 = 1310003) B1310003
theorem B1102727 : Blo 578813 1102727 := bstep (se 1 (by rfl) ⟨827045, by rfl⟩ : syracuseStep 1102727 = 1654091) B1654091
theorem B873359 : Blo 578813 873359 := bstep (se 1 (by rfl) ⟨655019, by rfl⟩ : syracuseStep 873359 = 1310039) B1310039
theorem B1954745 : Blo 578813 1954745 := bstep (se 2 (by rfl) ⟨733029, by rfl⟩ : syracuseStep 1954745 = 1466059) B1466059
theorem B873401 : Blo 578813 873401 := bstep (se 2 (by rfl) ⟨327525, by rfl⟩ : syracuseStep 873401 = 655051) B655051
theorem B873479 : Blo 578813 873479 := bstep (se 1 (by rfl) ⟨655109, by rfl⟩ : syracuseStep 873479 = 1310219) B1310219
theorem B873515 : Blo 578813 873515 := bstep (se 1 (by rfl) ⟨655136, by rfl⟩ : syracuseStep 873515 = 1310273) B1310273
theorem B873545 : Blo 578813 873545 := bstep (se 2 (by rfl) ⟨327579, by rfl⟩ : syracuseStep 873545 = 655159) B655159
theorem B1987703 : Blo 578813 1987703 := bstep (se 1 (by rfl) ⟨1490777, by rfl⟩ : syracuseStep 1987703 = 2981555) B2981555
theorem B873659 : Blo 578813 873659 := bstep (se 1 (by rfl) ⟨655244, by rfl⟩ : syracuseStep 873659 = 1310489) B1310489
theorem B873719 : Blo 578813 873719 := bstep (se 1 (by rfl) ⟨655289, by rfl⟩ : syracuseStep 873719 = 1310579) B1310579
theorem B578823 : Blo 578813 578823 := bstep (se 1 (by rfl) ⟨434117, by rfl⟩ : syracuseStep 578823 = 868235) B868235
theorem B578831 : Blo 578813 578831 := bstep (se 1 (by rfl) ⟨434123, by rfl⟩ : syracuseStep 578831 = 868247) B868247
theorem B873743 : Blo 578813 873743 := bstep (se 1 (by rfl) ⟨655307, by rfl⟩ : syracuseStep 873743 = 1310615) B1310615
theorem B873785 : Blo 578813 873785 := bstep (se 2 (by rfl) ⟨327669, by rfl⟩ : syracuseStep 873785 = 655339) B655339
theorem B578875 : Blo 578813 578875 := bstep (se 1 (by rfl) ⟨434156, by rfl⟩ : syracuseStep 578875 = 868313) B868313
theorem B578951 : Blo 578813 578951 := bstep (se 1 (by rfl) ⟨434213, by rfl⟩ : syracuseStep 578951 = 868427) B868427
theorem B4707719 : Blo 578813 4707719 := bstep (se 1 (by rfl) ⟨3530789, by rfl⟩ : syracuseStep 4707719 = 7061579) B7061579
theorem B873863 : Blo 578813 873863 := bstep (se 1 (by rfl) ⟨655397, by rfl⟩ : syracuseStep 873863 = 1310795) B1310795
theorem B578959 : Blo 578813 578959 := bstep (se 1 (by rfl) ⟨434219, by rfl⟩ : syracuseStep 578959 = 868439) B868439
theorem B873899 : Blo 578813 873899 := bstep (se 1 (by rfl) ⟨655424, by rfl⟩ : syracuseStep 873899 = 1310849) B1310849
theorem B5952953 : Blo 578813 5952953 := bstep (se 2 (by rfl) ⟨2232357, by rfl⟩ : syracuseStep 5952953 = 4464715) B4464715
theorem B579003 : Blo 578813 579003 := bstep (se 1 (by rfl) ⟨434252, by rfl⟩ : syracuseStep 579003 = 868505) B868505
theorem B873929 : Blo 578813 873929 := bstep (se 2 (by rfl) ⟨327723, by rfl⟩ : syracuseStep 873929 = 655447) B655447
theorem B579079 : Blo 578813 579079 := bstep (se 1 (by rfl) ⟨434309, by rfl⟩ : syracuseStep 579079 = 868619) B868619
theorem B1955339 : Blo 578813 1955339 := bstep (se 1 (by rfl) ⟨1466504, by rfl⟩ : syracuseStep 1955339 = 2933009) B2933009
theorem B579087 : Blo 578813 579087 := bstep (se 1 (by rfl) ⟨434315, by rfl⟩ : syracuseStep 579087 = 868631) B868631
theorem B3135019 : Blo 578813 3135019 := bstep (se 1 (by rfl) ⟨2351264, by rfl⟩ : syracuseStep 3135019 = 4702529) B4702529
theorem B579131 : Blo 578813 579131 := bstep (se 1 (by rfl) ⟨434348, by rfl⟩ : syracuseStep 579131 = 868697) B868697
theorem B874043 : Blo 578813 874043 := bstep (se 1 (by rfl) ⟨655532, by rfl⟩ : syracuseStep 874043 = 1311065) B1311065
theorem B1398359 : Blo 578813 1398359 := bstep (se 1 (by rfl) ⟨1048769, by rfl⟩ : syracuseStep 1398359 = 2097539) B2097539
theorem B1955447 : Blo 578813 1955447 := bstep (se 1 (by rfl) ⟨1466585, by rfl⟩ : syracuseStep 1955447 = 2933171) B2933171
theorem B874103 : Blo 578813 874103 := bstep (se 1 (by rfl) ⟨655577, by rfl⟩ : syracuseStep 874103 = 1311155) B1311155
theorem B579207 : Blo 578813 579207 := bstep (se 1 (by rfl) ⟨434405, by rfl⟩ : syracuseStep 579207 = 868811) B868811
theorem B579215 : Blo 578813 579215 := bstep (se 1 (by rfl) ⟨434411, by rfl⟩ : syracuseStep 579215 = 868823) B868823
theorem B874127 : Blo 578813 874127 := bstep (se 1 (by rfl) ⟨655595, by rfl⟩ : syracuseStep 874127 = 1311191) B1311191
theorem B874169 : Blo 578813 874169 := bstep (se 2 (by rfl) ⟨327813, by rfl⟩ : syracuseStep 874169 = 655627) B655627
theorem B579259 : Blo 578813 579259 := bstep (se 1 (by rfl) ⟨434444, by rfl⟩ : syracuseStep 579259 = 868889) B868889
theorem B579335 : Blo 578813 579335 := bstep (se 1 (by rfl) ⟨434501, by rfl⟩ : syracuseStep 579335 = 869003) B869003
theorem B579343 : Blo 578813 579343 := bstep (se 1 (by rfl) ⟨434507, by rfl⟩ : syracuseStep 579343 = 869015) B869015
theorem B2348833 : Blo 578813 2348833 := bstep (se 2 (by rfl) ⟨880812, by rfl⟩ : syracuseStep 2348833 = 1761625) B1761625
theorem B579387 : Blo 578813 579387 := bstep (se 1 (by rfl) ⟨434540, by rfl⟩ : syracuseStep 579387 = 869081) B869081
theorem B1398647 : Blo 578813 1398647 := bstep (se 1 (by rfl) ⟨1048985, by rfl⟩ : syracuseStep 1398647 = 2097971) B2097971
theorem B579463 : Blo 578813 579463 := bstep (se 1 (by rfl) ⟨434597, by rfl⟩ : syracuseStep 579463 = 869195) B869195
theorem B579471 : Blo 578813 579471 := bstep (se 1 (by rfl) ⟨434603, by rfl⟩ : syracuseStep 579471 = 869207) B869207
theorem B579515 : Blo 578813 579515 := bstep (se 1 (by rfl) ⟨434636, by rfl⟩ : syracuseStep 579515 = 869273) B869273
theorem B579591 : Blo 578813 579591 := bstep (se 1 (by rfl) ⟨434693, by rfl⟩ : syracuseStep 579591 = 869387) B869387
theorem B579599 : Blo 578813 579599 := bstep (se 1 (by rfl) ⟨434699, by rfl⟩ : syracuseStep 579599 = 869399) B869399
theorem B579643 : Blo 578813 579643 := bstep (se 1 (by rfl) ⟨434732, by rfl⟩ : syracuseStep 579643 = 869465) B869465
theorem B2480195 : Blo 578813 2480195 := bstep (se 1 (by rfl) ⟨1860146, by rfl⟩ : syracuseStep 2480195 = 3720293) B3720293
theorem B579719 : Blo 578813 579719 := bstep (se 1 (by rfl) ⟨434789, by rfl⟩ : syracuseStep 579719 = 869579) B869579
theorem B579727 : Blo 578813 579727 := bstep (se 1 (by rfl) ⟨434795, by rfl⟩ : syracuseStep 579727 = 869591) B869591
theorem B579771 : Blo 578813 579771 := bstep (se 1 (by rfl) ⟨434828, by rfl⟩ : syracuseStep 579771 = 869657) B869657
theorem B1956041 : Blo 578813 1956041 := bstep (se 2 (by rfl) ⟨733515, by rfl⟩ : syracuseStep 1956041 = 1467031) B1467031
theorem B579847 : Blo 578813 579847 := bstep (se 1 (by rfl) ⟨434885, by rfl⟩ : syracuseStep 579847 = 869771) B869771
theorem B579855 : Blo 578813 579855 := bstep (se 1 (by rfl) ⟨434891, by rfl⟩ : syracuseStep 579855 = 869783) B869783
theorem B579899 : Blo 578813 579899 := bstep (se 1 (by rfl) ⟨434924, by rfl⟩ : syracuseStep 579899 = 869849) B869849
theorem B579975 : Blo 578813 579975 := bstep (se 1 (by rfl) ⟨434981, by rfl⟩ : syracuseStep 579975 = 869963) B869963
theorem B579983 : Blo 578813 579983 := bstep (se 1 (by rfl) ⟨434987, by rfl⟩ : syracuseStep 579983 = 869975) B869975
theorem B2480537 : Blo 578813 2480537 := bstep (se 2 (by rfl) ⟨930201, by rfl⟩ : syracuseStep 2480537 = 1860403) B1860403
theorem B580027 : Blo 578813 580027 := bstep (se 1 (by rfl) ⟨435020, by rfl⟩ : syracuseStep 580027 = 870041) B870041
theorem B1104329 : Blo 578813 1104329 := bstep (se 2 (by rfl) ⟨414123, by rfl⟩ : syracuseStep 1104329 = 828247) B828247
theorem B580103 : Blo 578813 580103 := bstep (se 1 (by rfl) ⟨435077, by rfl⟩ : syracuseStep 580103 = 870155) B870155
theorem B580111 : Blo 578813 580111 := bstep (se 1 (by rfl) ⟨435083, by rfl⟩ : syracuseStep 580111 = 870167) B870167
theorem B580155 : Blo 578813 580155 := bstep (se 1 (by rfl) ⟨435116, by rfl⟩ : syracuseStep 580155 = 870233) B870233
theorem B580231 : Blo 578813 580231 := bstep (se 1 (by rfl) ⟨435173, by rfl⟩ : syracuseStep 580231 = 870347) B870347
theorem B580239 : Blo 578813 580239 := bstep (se 1 (by rfl) ⟨435179, by rfl⟩ : syracuseStep 580239 = 870359) B870359
theorem B580283 : Blo 578813 580283 := bstep (se 1 (by rfl) ⟨435212, by rfl⟩ : syracuseStep 580283 = 870425) B870425
theorem B580359 : Blo 578813 580359 := bstep (se 1 (by rfl) ⟨435269, by rfl⟩ : syracuseStep 580359 = 870539) B870539
theorem B580367 : Blo 578813 580367 := bstep (se 1 (by rfl) ⟨435275, by rfl⟩ : syracuseStep 580367 = 870551) B870551
theorem B580411 : Blo 578813 580411 := bstep (se 1 (by rfl) ⟨435308, by rfl⟩ : syracuseStep 580411 = 870617) B870617
theorem B1956743 : Blo 578813 1956743 := bstep (se 1 (by rfl) ⟨1467557, by rfl⟩ : syracuseStep 1956743 = 2935115) B2935115
theorem B580487 : Blo 578813 580487 := bstep (se 1 (by rfl) ⟨435365, by rfl⟩ : syracuseStep 580487 = 870731) B870731
theorem B580495 : Blo 578813 580495 := bstep (se 1 (by rfl) ⟨435371, by rfl⟩ : syracuseStep 580495 = 870743) B870743
theorem B580539 : Blo 578813 580539 := bstep (se 1 (by rfl) ⟨435404, by rfl⟩ : syracuseStep 580539 = 870809) B870809
theorem B580615 : Blo 578813 580615 := bstep (se 1 (by rfl) ⟨435461, by rfl⟩ : syracuseStep 580615 = 870923) B870923
theorem B580623 : Blo 578813 580623 := bstep (se 1 (by rfl) ⟨435467, by rfl⟩ : syracuseStep 580623 = 870935) B870935
theorem B580667 : Blo 578813 580667 := bstep (se 1 (by rfl) ⟨435500, by rfl⟩ : syracuseStep 580667 = 871001) B871001
theorem B580743 : Blo 578813 580743 := bstep (se 1 (by rfl) ⟨435557, by rfl⟩ : syracuseStep 580743 = 871115) B871115
theorem B580751 : Blo 578813 580751 := bstep (se 1 (by rfl) ⟨435563, by rfl⟩ : syracuseStep 580751 = 871127) B871127
theorem B47733941 : Blo 578813 47733941 := bstep (se 5 (by rfl) ⟨2237528, by rfl⟩ : syracuseStep 47733941 = 4475057) B4475057
theorem B580795 : Blo 578813 580795 := bstep (se 1 (by rfl) ⟨435596, by rfl⟩ : syracuseStep 580795 = 871193) B871193
theorem B11164877 : Blo 578813 11164877 := bstep (se 3 (by rfl) ⟨2093414, by rfl⟩ : syracuseStep 11164877 = 4186829) B4186829
theorem B1957121 : Blo 578813 1957121 := bstep (se 2 (by rfl) ⟨733920, by rfl⟩ : syracuseStep 1957121 = 1467841) B1467841
theorem B580871 : Blo 578813 580871 := bstep (se 1 (by rfl) ⟨435653, by rfl⟩ : syracuseStep 580871 = 871307) B871307
theorem B580879 : Blo 578813 580879 := bstep (se 1 (by rfl) ⟨435659, by rfl⟩ : syracuseStep 580879 = 871319) B871319
theorem B580923 : Blo 578813 580923 := bstep (se 1 (by rfl) ⟨435692, by rfl⟩ : syracuseStep 580923 = 871385) B871385
theorem B1465715 : Blo 578813 1465715 := bstep (se 1 (by rfl) ⟨1099286, by rfl⟩ : syracuseStep 1465715 = 2198573) B2198573
theorem B1465735 : Blo 578813 1465735 := bstep (se 1 (by rfl) ⟨1099301, by rfl⟩ : syracuseStep 1465735 = 2198603) B2198603
theorem B580999 : Blo 578813 580999 := bstep (se 1 (by rfl) ⟨435749, by rfl⟩ : syracuseStep 580999 = 871499) B871499
theorem B581007 : Blo 578813 581007 := bstep (se 1 (by rfl) ⟨435755, by rfl⟩ : syracuseStep 581007 = 871511) B871511
theorem B581051 : Blo 578813 581051 := bstep (se 1 (by rfl) ⟨435788, by rfl⟩ : syracuseStep 581051 = 871577) B871577
theorem B581127 : Blo 578813 581127 := bstep (se 1 (by rfl) ⟨435845, by rfl⟩ : syracuseStep 581127 = 871691) B871691
theorem B581135 : Blo 578813 581135 := bstep (se 1 (by rfl) ⟨435851, by rfl⟩ : syracuseStep 581135 = 871703) B871703
theorem B581179 : Blo 578813 581179 := bstep (se 1 (by rfl) ⟨435884, by rfl⟩ : syracuseStep 581179 = 871769) B871769
theorem B581255 : Blo 578813 581255 := bstep (se 1 (by rfl) ⟨435941, by rfl⟩ : syracuseStep 581255 = 871883) B871883
theorem B581263 : Blo 578813 581263 := bstep (se 1 (by rfl) ⟨435947, by rfl⟩ : syracuseStep 581263 = 871895) B871895
theorem B1466009 : Blo 578813 1466009 := bstep (se 2 (by rfl) ⟨549753, by rfl⟩ : syracuseStep 1466009 = 1099507) B1099507
theorem B581307 : Blo 578813 581307 := bstep (se 1 (by rfl) ⟨435980, by rfl⟩ : syracuseStep 581307 = 871961) B871961
theorem B581383 : Blo 578813 581383 := bstep (se 1 (by rfl) ⟨436037, by rfl⟩ : syracuseStep 581383 = 872075) B872075
theorem B581391 : Blo 578813 581391 := bstep (se 1 (by rfl) ⟨436043, by rfl⟩ : syracuseStep 581391 = 872087) B872087
theorem B1466171 : Blo 578813 1466171 := bstep (se 1 (by rfl) ⟨1099628, by rfl⟩ : syracuseStep 1466171 = 2199257) B2199257
theorem B581435 : Blo 578813 581435 := bstep (se 1 (by rfl) ⟨436076, by rfl⟩ : syracuseStep 581435 = 872153) B872153
theorem B1302407 : Blo 578813 1302407 := bstep (se 1 (by rfl) ⟨976805, by rfl⟩ : syracuseStep 1302407 = 1953611) B1953611
theorem B581511 : Blo 578813 581511 := bstep (se 1 (by rfl) ⟨436133, by rfl⟩ : syracuseStep 581511 = 872267) B872267
theorem B581519 : Blo 578813 581519 := bstep (se 1 (by rfl) ⟨436139, by rfl⟩ : syracuseStep 581519 = 872279) B872279
theorem B581563 : Blo 578813 581563 := bstep (se 1 (by rfl) ⟨436172, by rfl⟩ : syracuseStep 581563 = 872345) B872345
theorem B581639 : Blo 578813 581639 := bstep (se 1 (by rfl) ⟨436229, by rfl⟩ : syracuseStep 581639 = 872459) B872459
theorem B1466383 : Blo 578813 1466383 := bstep (se 1 (by rfl) ⟨1099787, by rfl⟩ : syracuseStep 1466383 = 2199575) B2199575
theorem B581647 : Blo 578813 581647 := bstep (se 1 (by rfl) ⟨436235, by rfl⟩ : syracuseStep 581647 = 872471) B872471
theorem B8970263 : Blo 578813 8970263 := bstep (se 1 (by rfl) ⟨6727697, by rfl⟩ : syracuseStep 8970263 = 13455395) B13455395
theorem B1957931 : Blo 578813 1957931 := bstep (se 1 (by rfl) ⟨1468448, by rfl⟩ : syracuseStep 1957931 = 2936897) B2936897
theorem B1302587 : Blo 578813 1302587 := bstep (se 1 (by rfl) ⟨976940, by rfl⟩ : syracuseStep 1302587 = 1953881) B1953881
theorem B581691 : Blo 578813 581691 := bstep (se 1 (by rfl) ⟨436268, by rfl⟩ : syracuseStep 581691 = 872537) B872537
theorem B581767 : Blo 578813 581767 := bstep (se 1 (by rfl) ⟨436325, by rfl⟩ : syracuseStep 581767 = 872651) B872651
theorem B581775 : Blo 578813 581775 := bstep (se 1 (by rfl) ⟨436331, by rfl⟩ : syracuseStep 581775 = 872663) B872663
theorem B2875565 : Blo 578813 2875565 := bstep (se 3 (by rfl) ⟨539168, by rfl⟩ : syracuseStep 2875565 = 1078337) B1078337
theorem B1302713 : Blo 578813 1302713 := bstep (se 2 (by rfl) ⟨488517, by rfl⟩ : syracuseStep 1302713 = 977035) B977035
theorem B581819 : Blo 578813 581819 := bstep (se 1 (by rfl) ⟨436364, by rfl⟩ : syracuseStep 581819 = 872729) B872729
theorem B4186313 : Blo 578813 4186313 := bstep (se 2 (by rfl) ⟨1569867, by rfl⟩ : syracuseStep 4186313 = 3139735) B3139735
theorem B581895 : Blo 578813 581895 := bstep (se 1 (by rfl) ⟨436421, by rfl⟩ : syracuseStep 581895 = 872843) B872843
theorem B11133197 : Blo 578813 11133197 := bstep (se 3 (by rfl) ⟨2087474, by rfl⟩ : syracuseStep 11133197 = 4174949) B4174949
theorem B581903 : Blo 578813 581903 := bstep (se 1 (by rfl) ⟨436427, by rfl⟩ : syracuseStep 581903 = 872855) B872855
theorem B1466657 : Blo 578813 1466657 := bstep (se 2 (by rfl) ⟨549996, by rfl⟩ : syracuseStep 1466657 = 1099993) B1099993
theorem B581947 : Blo 578813 581947 := bstep (se 1 (by rfl) ⟨436460, by rfl⟩ : syracuseStep 581947 = 872921) B872921
theorem B582023 : Blo 578813 582023 := bstep (se 1 (by rfl) ⟨436517, by rfl⟩ : syracuseStep 582023 = 873035) B873035
theorem B1106311 : Blo 578813 1106311 := bstep (se 1 (by rfl) ⟨829733, by rfl⟩ : syracuseStep 1106311 = 1659467) B1659467
theorem B582031 : Blo 578813 582031 := bstep (se 1 (by rfl) ⟨436523, by rfl⟩ : syracuseStep 582031 = 873047) B873047
theorem B1859993 : Blo 578813 1859993 := bstep (se 2 (by rfl) ⟨697497, by rfl⟩ : syracuseStep 1859993 = 1394995) B1394995
theorem B582075 : Blo 578813 582075 := bstep (se 1 (by rfl) ⟨436556, by rfl⟩ : syracuseStep 582075 = 873113) B873113
theorem B582151 : Blo 578813 582151 := bstep (se 1 (by rfl) ⟨436613, by rfl⟩ : syracuseStep 582151 = 873227) B873227
theorem B1303055 : Blo 578813 1303055 := bstep (se 1 (by rfl) ⟨977291, by rfl⟩ : syracuseStep 1303055 = 1954583) B1954583
theorem B582159 : Blo 578813 582159 := bstep (se 1 (by rfl) ⟨436619, by rfl⟩ : syracuseStep 582159 = 873239) B873239
theorem B1303073 : Blo 578813 1303073 := bstep (se 2 (by rfl) ⟨488652, by rfl⟩ : syracuseStep 1303073 = 977305) B977305
theorem B582203 : Blo 578813 582203 := bstep (se 1 (by rfl) ⟨436652, by rfl⟩ : syracuseStep 582203 = 873305) B873305
theorem B582279 : Blo 578813 582279 := bstep (se 1 (by rfl) ⟨436709, by rfl⟩ : syracuseStep 582279 = 873419) B873419
theorem B582287 : Blo 578813 582287 := bstep (se 1 (by rfl) ⟨436715, by rfl⟩ : syracuseStep 582287 = 873431) B873431
theorem B582331 : Blo 578813 582331 := bstep (se 1 (by rfl) ⟨436748, by rfl⟩ : syracuseStep 582331 = 873497) B873497
theorem B582407 : Blo 578813 582407 := bstep (se 1 (by rfl) ⟨436805, by rfl⟩ : syracuseStep 582407 = 873611) B873611
theorem B582415 : Blo 578813 582415 := bstep (se 1 (by rfl) ⟨436811, by rfl⟩ : syracuseStep 582415 = 873623) B873623
theorem B582459 : Blo 578813 582459 := bstep (se 1 (by rfl) ⟨436844, by rfl⟩ : syracuseStep 582459 = 873689) B873689
theorem B1303415 : Blo 578813 1303415 := bstep (se 1 (by rfl) ⟨977561, by rfl⟩ : syracuseStep 1303415 = 1955123) B1955123
theorem B3302279 : Blo 578813 3302279 := bstep (se 1 (by rfl) ⟨2476709, by rfl⟩ : syracuseStep 3302279 = 4953419) B4953419
theorem B582535 : Blo 578813 582535 := bstep (se 1 (by rfl) ⟨436901, by rfl⟩ : syracuseStep 582535 = 873803) B873803
theorem B582543 : Blo 578813 582543 := bstep (se 1 (by rfl) ⟨436907, by rfl⟩ : syracuseStep 582543 = 873815) B873815
theorem B1237945 : Blo 578813 1237945 := bstep (se 2 (by rfl) ⟨464229, by rfl⟩ : syracuseStep 1237945 = 928459) B928459
theorem B582587 : Blo 578813 582587 := bstep (se 1 (by rfl) ⟨436940, by rfl⟩ : syracuseStep 582587 = 873881) B873881
theorem B582663 : Blo 578813 582663 := bstep (se 1 (by rfl) ⟨436997, by rfl⟩ : syracuseStep 582663 = 873995) B873995
theorem B582671 : Blo 578813 582671 := bstep (se 1 (by rfl) ⟨437003, by rfl⟩ : syracuseStep 582671 = 874007) B874007
theorem B1303595 : Blo 578813 1303595 := bstep (se 1 (by rfl) ⟨977696, by rfl⟩ : syracuseStep 1303595 = 1955393) B1955393
theorem B582715 : Blo 578813 582715 := bstep (se 1 (by rfl) ⟨437036, by rfl⟩ : syracuseStep 582715 = 874073) B874073
theorem B6612029 : Blo 578813 6612029 := bstep (se 3 (by rfl) ⟨1239755, by rfl⟩ : syracuseStep 6612029 = 2479511) B2479511
theorem B582791 : Blo 578813 582791 := bstep (se 1 (by rfl) ⟨437093, by rfl⟩ : syracuseStep 582791 = 874187) B874187
theorem B582799 : Blo 578813 582799 := bstep (se 1 (by rfl) ⟨437099, by rfl⟩ : syracuseStep 582799 = 874199) B874199
theorem B7070921 : Blo 578813 7070921 := bstep (se 2 (by rfl) ⟨2651595, by rfl⟩ : syracuseStep 7070921 = 5303191) B5303191
theorem B8381677 : Blo 578813 8381677 := bstep (se 3 (by rfl) ⟨1571564, by rfl⟩ : syracuseStep 8381677 = 3143129) B3143129
theorem B5596397 : Blo 578813 5596397 := bstep (se 3 (by rfl) ⟨1049324, by rfl⟩ : syracuseStep 5596397 = 2098649) B2098649
theorem B1467659 : Blo 578813 1467659 := bstep (se 1 (by rfl) ⟨1100744, by rfl⟩ : syracuseStep 1467659 = 2201489) B2201489
theorem B1238287 : Blo 578813 1238287 := bstep (se 1 (by rfl) ⟨928715, by rfl⟩ : syracuseStep 1238287 = 1857431) B1857431
theorem B1959227 : Blo 578813 1959227 := bstep (se 1 (by rfl) ⟨1469420, by rfl⟩ : syracuseStep 1959227 = 2938841) B2938841
theorem B3728699 : Blo 578813 3728699 := bstep (se 1 (by rfl) ⟨2796524, by rfl⟩ : syracuseStep 3728699 = 5593049) B5593049
theorem B1303955 : Blo 578813 1303955 := bstep (se 1 (by rfl) ⟨977966, by rfl⟩ : syracuseStep 1303955 = 1955933) B1955933
theorem B1304009 : Blo 578813 1304009 := bstep (se 2 (by rfl) ⟨489003, by rfl⟩ : syracuseStep 1304009 = 978007) B978007
theorem B14116355 : Blo 578813 14116355 := bstep (se 1 (by rfl) ⟨10587266, by rfl⟩ : syracuseStep 14116355 = 21174533) B21174533
theorem B16934429 : Blo 578813 16934429 := bstep (se 3 (by rfl) ⟨3175205, by rfl⟩ : syracuseStep 16934429 = 6350411) B6350411
theorem B5596739 : Blo 578813 5596739 := bstep (se 1 (by rfl) ⟨4197554, by rfl⟩ : syracuseStep 5596739 = 8395109) B8395109
theorem B943751 : Blo 578813 943751 := bstep (se 1 (by rfl) ⟨707813, by rfl⟩ : syracuseStep 943751 = 1415627) B1415627
theorem B4417253 : Blo 578813 4417253 := bstep (se 4 (by rfl) ⟨414117, by rfl⟩ : syracuseStep 4417253 = 828235) B828235
theorem B1959713 : Blo 578813 1959713 := bstep (se 2 (by rfl) ⟨734892, by rfl⟩ : syracuseStep 1959713 = 1469785) B1469785
theorem B1468307 : Blo 578813 1468307 := bstep (se 1 (by rfl) ⟨1101230, by rfl⟩ : syracuseStep 1468307 = 2202461) B2202461
theorem B9955223 : Blo 578813 9955223 := bstep (se 1 (by rfl) ⟨7466417, by rfl⟩ : syracuseStep 9955223 = 14932835) B14932835
theorem B2353195 : Blo 578813 2353195 := bstep (se 1 (by rfl) ⟨1764896, by rfl⟩ : syracuseStep 2353195 = 3529793) B3529793
theorem B5662781 : Blo 578813 5662781 := bstep (se 3 (by rfl) ⟨1061771, by rfl⟩ : syracuseStep 5662781 = 2123543) B2123543
theorem B977015 : Blo 578813 977015 := bstep (se 1 (by rfl) ⟨732761, by rfl⟩ : syracuseStep 977015 = 1465523) B1465523
theorem B1304711 : Blo 578813 1304711 := bstep (se 1 (by rfl) ⟨978533, by rfl⟩ : syracuseStep 1304711 = 1957067) B1957067
theorem B1239175 : Blo 578813 1239175 := bstep (se 1 (by rfl) ⟨929381, by rfl⟩ : syracuseStep 1239175 = 1858763) B1858763
theorem B1468601 : Blo 578813 1468601 := bstep (se 2 (by rfl) ⟨550725, by rfl⟩ : syracuseStep 1468601 = 1101451) B1101451
theorem B1304891 : Blo 578813 1304891 := bstep (se 1 (by rfl) ⟨978668, by rfl⟩ : syracuseStep 1304891 = 1957337) B1957337
theorem B1960307 : Blo 578813 1960307 := bstep (se 1 (by rfl) ⟨1470230, by rfl⟩ : syracuseStep 1960307 = 2940461) B2940461
theorem B2943377 : Blo 578813 2943377 := bstep (se 2 (by rfl) ⟨1103766, by rfl⟩ : syracuseStep 2943377 = 2207533) B2207533
theorem B1305017 : Blo 578813 1305017 := bstep (se 2 (by rfl) ⟨489381, by rfl⟩ : syracuseStep 1305017 = 978763) B978763
theorem B977467 : Blo 578813 977467 := bstep (se 1 (by rfl) ⟨733100, by rfl⟩ : syracuseStep 977467 = 1466201) B1466201
theorem B977609 : Blo 578813 977609 := bstep (se 2 (by rfl) ⟨366603, by rfl⟩ : syracuseStep 977609 = 733207) B733207
theorem B1305359 : Blo 578813 1305359 := bstep (se 1 (by rfl) ⟨979019, by rfl⟩ : syracuseStep 1305359 = 1958039) B1958039
theorem B1305377 : Blo 578813 1305377 := bstep (se 2 (by rfl) ⟨489516, by rfl⟩ : syracuseStep 1305377 = 979033) B979033
theorem B1469299 : Blo 578813 1469299 := bstep (se 1 (by rfl) ⟨1101974, by rfl⟩ : syracuseStep 1469299 = 2203949) B2203949
theorem B1469441 : Blo 578813 1469441 := bstep (se 2 (by rfl) ⟨551040, by rfl⟩ : syracuseStep 1469441 = 1102081) B1102081
theorem B1076267 : Blo 578813 1076267 := bstep (se 1 (by rfl) ⟨807200, by rfl⟩ : syracuseStep 1076267 = 1614401) B1614401
theorem B1305719 : Blo 578813 1305719 := bstep (se 1 (by rfl) ⟨979289, by rfl⟩ : syracuseStep 1305719 = 1958579) B1958579
theorem B1305899 : Blo 578813 1305899 := bstep (se 1 (by rfl) ⟨979424, by rfl⟩ : syracuseStep 1305899 = 1958849) B1958849
theorem B1240363 : Blo 578813 1240363 := bstep (se 1 (by rfl) ⟨930272, by rfl⟩ : syracuseStep 1240363 = 1860545) B1860545
theorem B22605101 : Blo 578813 22605101 := bstep (se 3 (by rfl) ⟨4238456, by rfl⟩ : syracuseStep 22605101 = 8476913) B8476913
theorem B1240439 : Blo 578813 1240439 := bstep (se 1 (by rfl) ⟨930329, by rfl⟩ : syracuseStep 1240439 = 1860659) B1860659
theorem B978311 : Blo 578813 978311 := bstep (se 1 (by rfl) ⟨733733, by rfl⟩ : syracuseStep 978311 = 1467467) B1467467
theorem B1469897 : Blo 578813 1469897 := bstep (se 2 (by rfl) ⟨551211, by rfl⟩ : syracuseStep 1469897 = 1102423) B1102423
theorem B1568375 : Blo 578813 1568375 := bstep (se 1 (by rfl) ⟨1176281, by rfl⟩ : syracuseStep 1568375 = 2352563) B2352563
theorem B1306259 : Blo 578813 1306259 := bstep (se 1 (by rfl) ⟨979694, by rfl⟩ : syracuseStep 1306259 = 1959389) B1959389
theorem B1306313 : Blo 578813 1306313 := bstep (se 2 (by rfl) ⟨489867, by rfl⟩ : syracuseStep 1306313 = 979735) B979735
theorem B1470251 : Blo 578813 1470251 := bstep (se 1 (by rfl) ⟨1102688, by rfl⟩ : syracuseStep 1470251 = 2205377) B2205377
theorem B651271 : Blo 578813 651271 := bstep (se 1 (by rfl) ⟨488453, by rfl⟩ : syracuseStep 651271 = 976907) B976907
theorem B3731467 : Blo 578813 3731467 := bstep (se 1 (by rfl) ⟨2798600, by rfl⟩ : syracuseStep 3731467 = 5597201) B5597201
theorem B978959 : Blo 578813 978959 := bstep (se 1 (by rfl) ⟨734219, by rfl⟩ : syracuseStep 978959 = 1468439) B1468439
theorem B651451 : Blo 578813 651451 := bstep (se 1 (by rfl) ⟨488588, by rfl⟩ : syracuseStep 651451 = 977177) B977177
theorem B618887 : Blo 578813 618887 := bstep (se 1 (by rfl) ⟨464165, by rfl⟩ : syracuseStep 618887 = 928331) B928331
theorem B1307015 : Blo 578813 1307015 := bstep (se 1 (by rfl) ⟨980261, by rfl⟩ : syracuseStep 1307015 = 1960523) B1960523
theorem B2945483 : Blo 578813 2945483 := bstep (se 1 (by rfl) ⟨2209112, by rfl⟩ : syracuseStep 2945483 = 4418225) B4418225
theorem B979499 : Blo 578813 979499 := bstep (se 1 (by rfl) ⟨734624, by rfl⟩ : syracuseStep 979499 = 1469249) B1469249
theorem B1864235 : Blo 578813 1864235 := bstep (se 1 (by rfl) ⟨1398176, by rfl⟩ : syracuseStep 1864235 = 2796353) B2796353
theorem B1307195 : Blo 578813 1307195 := bstep (se 1 (by rfl) ⟨980396, by rfl⟩ : syracuseStep 1307195 = 1960793) B1960793
theorem B651919 : Blo 578813 651919 := bstep (se 1 (by rfl) ⟨488939, by rfl⟩ : syracuseStep 651919 = 977879) B977879
theorem B1307321 : Blo 578813 1307321 := bstep (se 2 (by rfl) ⟨490245, by rfl⟩ : syracuseStep 1307321 = 980491) B980491
theorem B1471243 : Blo 578813 1471243 := bstep (se 1 (by rfl) ⟨1103432, by rfl⟩ : syracuseStep 1471243 = 2206865) B2206865
theorem B2945807 : Blo 578813 2945807 := bstep (se 1 (by rfl) ⟨2209355, by rfl⟩ : syracuseStep 2945807 = 4418711) B4418711
theorem B1962899 : Blo 578813 1962899 := bstep (se 1 (by rfl) ⟨1472174, by rfl⟩ : syracuseStep 1962899 = 2944349) B2944349
theorem B1471385 : Blo 578813 1471385 := bstep (se 2 (by rfl) ⟨551769, by rfl⟩ : syracuseStep 1471385 = 1103539) B1103539
theorem B979897 : Blo 578813 979897 := bstep (se 2 (by rfl) ⟨367461, by rfl⟩ : syracuseStep 979897 = 734923) B734923
theorem B1307663 : Blo 578813 1307663 := bstep (se 1 (by rfl) ⟨980747, by rfl⟩ : syracuseStep 1307663 = 1961495) B1961495
theorem B1307681 : Blo 578813 1307681 := bstep (se 2 (by rfl) ⟨490380, by rfl⟩ : syracuseStep 1307681 = 980761) B980761
theorem B619579 : Blo 578813 619579 := bstep (se 1 (by rfl) ⟨464684, by rfl⟩ : syracuseStep 619579 = 929369) B929369
theorem B1471547 : Blo 578813 1471547 := bstep (se 1 (by rfl) ⟨1103660, by rfl⟩ : syracuseStep 1471547 = 2207321) B2207321
theorem B652423 : Blo 578813 652423 := bstep (se 1 (by rfl) ⟨489317, by rfl⟩ : syracuseStep 652423 = 978635) B978635
theorem B2094281 : Blo 578813 2094281 := bstep (se 2 (by rfl) ⟨785355, by rfl⟩ : syracuseStep 2094281 = 1570711) B1570711
theorem B652603 : Blo 578813 652603 := bstep (se 1 (by rfl) ⟨489452, by rfl⟩ : syracuseStep 652603 = 978905) B978905
theorem B2487611 : Blo 578813 2487611 := bstep (se 1 (by rfl) ⟨1865708, by rfl⟩ : syracuseStep 2487611 = 3731417) B3731417
theorem B3536243 : Blo 578813 3536243 := bstep (se 1 (by rfl) ⟨2652182, by rfl⟩ : syracuseStep 3536243 = 5304365) B5304365
theorem B1308023 : Blo 578813 1308023 := bstep (se 1 (by rfl) ⟨981017, by rfl⟩ : syracuseStep 1308023 = 1962035) B1962035
theorem B1471891 : Blo 578813 1471891 := bstep (se 1 (by rfl) ⟨1103918, by rfl⟩ : syracuseStep 1471891 = 2207837) B2207837
theorem B3306905 : Blo 578813 3306905 := bstep (se 2 (by rfl) ⟨1240089, by rfl⟩ : syracuseStep 3306905 = 2480179) B2480179
theorem B6714809 : Blo 578813 6714809 := bstep (se 2 (by rfl) ⟨2518053, by rfl⟩ : syracuseStep 6714809 = 5036107) B5036107
theorem B1472033 : Blo 578813 1472033 := bstep (se 2 (by rfl) ⟨552012, by rfl⟩ : syracuseStep 1472033 = 1104025) B1104025
theorem B1308203 : Blo 578813 1308203 := bstep (se 1 (by rfl) ⟨981152, by rfl⟩ : syracuseStep 1308203 = 1962305) B1962305
theorem B980599 : Blo 578813 980599 := bstep (se 1 (by rfl) ⟨735449, by rfl⟩ : syracuseStep 980599 = 1470899) B1470899
theorem B653071 : Blo 578813 653071 := bstep (se 1 (by rfl) ⟨489803, by rfl⟩ : syracuseStep 653071 = 979607) B979607
theorem B980795 : Blo 578813 980795 := bstep (se 1 (by rfl) ⟨735596, by rfl⟩ : syracuseStep 980795 = 1471193) B1471193
theorem B3143539 : Blo 578813 3143539 := bstep (se 1 (by rfl) ⟨2357654, by rfl⟩ : syracuseStep 3143539 = 4715309) B4715309
theorem B1308563 : Blo 578813 1308563 := bstep (se 1 (by rfl) ⟨981422, by rfl⟩ : syracuseStep 1308563 = 1962845) B1962845
theorem B1308617 : Blo 578813 1308617 := bstep (se 2 (by rfl) ⟨490731, by rfl⟩ : syracuseStep 1308617 = 981463) B981463
theorem B2947265 : Blo 578813 2947265 := bstep (se 2 (by rfl) ⟨1105224, by rfl⟩ : syracuseStep 2947265 = 2210449) B2210449
theorem B981193 : Blo 578813 981193 := bstep (se 2 (by rfl) ⟨367947, by rfl⟩ : syracuseStep 981193 = 735895) B735895
theorem B653575 : Blo 578813 653575 := bstep (se 1 (by rfl) ⟨490181, by rfl⟩ : syracuseStep 653575 = 980363) B980363
theorem B1964303 : Blo 578813 1964303 := bstep (se 1 (by rfl) ⟨1473227, by rfl⟩ : syracuseStep 1964303 = 2946455) B2946455
theorem B1866017 : Blo 578813 1866017 := bstep (se 2 (by rfl) ⟨699756, by rfl⟩ : syracuseStep 1866017 = 1399513) B1399513
theorem B653755 : Blo 578813 653755 := bstep (se 1 (by rfl) ⟨490316, by rfl⟩ : syracuseStep 653755 = 980633) B980633
theorem B1473025 : Blo 578813 1473025 := bstep (se 2 (by rfl) ⟨552384, by rfl⟩ : syracuseStep 1473025 = 1104769) B1104769
theorem B1964573 : Blo 578813 1964573 := bstep (se 3 (by rfl) ⟨368357, by rfl⟩ : syracuseStep 1964573 = 736715) B736715
theorem B1178155 : Blo 578813 1178155 := bstep (se 1 (by rfl) ⟨883616, by rfl⟩ : syracuseStep 1178155 = 1767233) B1767233
theorem B1309319 : Blo 578813 1309319 := bstep (se 1 (by rfl) ⟨981989, by rfl⟩ : syracuseStep 1309319 = 1963979) B1963979
theorem B1243849 : Blo 578813 1243849 := bstep (se 2 (by rfl) ⟨466443, by rfl⟩ : syracuseStep 1243849 = 932887) B932887
theorem B3537701 : Blo 578813 3537701 := bstep (se 4 (by rfl) ⟨331659, by rfl⟩ : syracuseStep 3537701 = 663319) B663319
theorem B1309499 : Blo 578813 1309499 := bstep (se 1 (by rfl) ⟨982124, by rfl⟩ : syracuseStep 1309499 = 1964249) B1964249
theorem B981895 : Blo 578813 981895 := bstep (se 1 (by rfl) ⟨736421, by rfl⟩ : syracuseStep 981895 = 1472843) B1472843
theorem B654223 : Blo 578813 654223 := bstep (se 1 (by rfl) ⟨490667, by rfl⟩ : syracuseStep 654223 = 981335) B981335
theorem B1309625 : Blo 578813 1309625 := bstep (se 2 (by rfl) ⟨491109, by rfl⟩ : syracuseStep 1309625 = 982219) B982219
theorem B1506319 : Blo 578813 1506319 := bstep (se 1 (by rfl) ⟨1129739, by rfl⟩ : syracuseStep 1506319 = 2259479) B2259479
theorem B1473623 : Blo 578813 1473623 := bstep (se 1 (by rfl) ⟨1105217, by rfl⟩ : syracuseStep 1473623 = 2210435) B2210435
theorem B1309967 : Blo 578813 1309967 := bstep (se 1 (by rfl) ⟨982475, by rfl⟩ : syracuseStep 1309967 = 1964951) B1964951
theorem B1309985 : Blo 578813 1309985 := bstep (se 2 (by rfl) ⟨491244, by rfl⟩ : syracuseStep 1309985 = 982489) B982489
theorem B1473835 : Blo 578813 1473835 := bstep (se 1 (by rfl) ⟨1105376, by rfl⟩ : syracuseStep 1473835 = 2210753) B2210753
theorem B8486279 : Blo 578813 8486279 := bstep (se 1 (by rfl) ⟨6364709, by rfl⟩ : syracuseStep 8486279 = 12729419) B12729419
theorem B11926919 : Blo 578813 11926919 := bstep (se 1 (by rfl) ⟨8945189, by rfl⟩ : syracuseStep 11926919 = 17890379) B17890379
theorem B654727 : Blo 578813 654727 := bstep (se 1 (by rfl) ⟨491045, by rfl⟩ : syracuseStep 654727 = 982091) B982091
theorem B1473977 : Blo 578813 1473977 := bstep (se 2 (by rfl) ⟨552741, by rfl⟩ : syracuseStep 1473977 = 1105483) B1105483
theorem B3538379 : Blo 578813 3538379 := bstep (se 1 (by rfl) ⟨2653784, by rfl⟩ : syracuseStep 3538379 = 5307569) B5307569
theorem B2948561 : Blo 578813 2948561 := bstep (se 2 (by rfl) ⟨1105710, by rfl⟩ : syracuseStep 2948561 = 2211421) B2211421
theorem B982543 : Blo 578813 982543 := bstep (se 1 (by rfl) ⟨736907, by rfl⟩ : syracuseStep 982543 = 1473815) B1473815
theorem B654907 : Blo 578813 654907 := bstep (se 1 (by rfl) ⟨491180, by rfl⟩ : syracuseStep 654907 = 982361) B982361
theorem B1310327 : Blo 578813 1310327 := bstep (se 1 (by rfl) ⟨982745, by rfl⟩ : syracuseStep 1310327 = 1965491) B1965491
theorem B884395 : Blo 578813 884395 := bstep (se 1 (by rfl) ⟨663296, by rfl⟩ : syracuseStep 884395 = 1326593) B1326593
theorem B2981569 : Blo 578813 2981569 := bstep (se 2 (by rfl) ⟨1118088, by rfl⟩ : syracuseStep 2981569 = 2236177) B2236177
theorem B1310507 : Blo 578813 1310507 := bstep (se 1 (by rfl) ⟨982880, by rfl⟩ : syracuseStep 1310507 = 1965761) B1965761
theorem B28737431 : Blo 578813 28737431 := bstep (se 1 (by rfl) ⟨21553073, by rfl⟩ : syracuseStep 28737431 = 43106147) B43106147
theorem B2097049 : Blo 578813 2097049 := bstep (se 2 (by rfl) ⟨786393, by rfl⟩ : syracuseStep 2097049 = 1572787) B1572787
theorem B1965977 : Blo 578813 1965977 := bstep (se 2 (by rfl) ⟨737241, by rfl⟩ : syracuseStep 1965977 = 1474483) B1474483
theorem B5898269 : Blo 578813 5898269 := bstep (se 3 (by rfl) ⟨1105925, by rfl⟩ : syracuseStep 5898269 = 2211851) B2211851
theorem B1310777 : Blo 578813 1310777 := bstep (se 2 (by rfl) ⟨491541, by rfl⟩ : syracuseStep 1310777 = 983083) B983083
theorem B2949209 : Blo 578813 2949209 := bstep (se 2 (by rfl) ⟨1105953, by rfl⟩ : syracuseStep 2949209 = 2211907) B2211907
theorem B655483 : Blo 578813 655483 := bstep (se 1 (by rfl) ⟨491612, by rfl⟩ : syracuseStep 655483 = 983225) B983225
theorem B12550373 : Blo 578813 12550373 := bstep (se 4 (by rfl) ⟨1176597, by rfl⟩ : syracuseStep 12550373 = 2353195) B2353195
theorem B1474807 : Blo 578813 1474807 := bstep (se 1 (by rfl) ⟨1106105, by rfl⟩ : syracuseStep 1474807 = 2212211) B2212211
theorem B1311119 : Blo 578813 1311119 := bstep (se 1 (by rfl) ⟨983339, by rfl⟩ : syracuseStep 1311119 = 1966679) B1966679
theorem B7668173 : Blo 578813 7668173 := bstep (se 3 (by rfl) ⟨1437782, by rfl⟩ : syracuseStep 7668173 = 2875565) B2875565
theorem B1475081 : Blo 578813 1475081 := bstep (se 2 (by rfl) ⟨553155, by rfl⟩ : syracuseStep 1475081 = 1106311) B1106311
theorem B1966625 : Blo 578813 1966625 := bstep (se 2 (by rfl) ⟨737484, by rfl⟩ : syracuseStep 1966625 = 1474969) B1474969
theorem B590375 : Blo 578813 590375 := bstep (se 1 (by rfl) ⟨442781, by rfl⟩ : syracuseStep 590375 = 885563) B885563
theorem B1475111 : Blo 578813 1475111 := bstep (se 1 (by rfl) ⟨1106333, by rfl⟩ : syracuseStep 1475111 = 2212667) B2212667
theorem B53609111 : Blo 578813 53609111 := bstep (se 1 (by rfl) ⟨40206833, by rfl⟩ : syracuseStep 53609111 = 80413667) B80413667
theorem B1966841 : Blo 578813 1966841 := bstep (se 2 (by rfl) ⟨737565, by rfl⟩ : syracuseStep 1966841 = 1475131) B1475131
theorem B8913665 : Blo 578813 8913665 := bstep (se 2 (by rfl) ⟨3342624, by rfl⟩ : syracuseStep 8913665 = 6685249) B6685249
theorem B5964617 : Blo 578813 5964617 := bstep (se 2 (by rfl) ⟨2236731, by rfl⟩ : syracuseStep 5964617 = 4473463) B4473463
theorem B1115041 : Blo 578813 1115041 := bstep (se 2 (by rfl) ⟨418140, by rfl⟩ : syracuseStep 1115041 = 836281) B836281
theorem B4195709 : Blo 578813 4195709 := bstep (se 3 (by rfl) ⟨786695, by rfl⟩ : syracuseStep 4195709 = 1573391) B1573391
theorem B1181147 : Blo 578813 1181147 := bstep (se 1 (by rfl) ⟨885860, by rfl⟩ : syracuseStep 1181147 = 1771721) B1771721
theorem B11175569 : Blo 578813 11175569 := bstep (se 2 (by rfl) ⟨4190838, by rfl⟩ : syracuseStep 11175569 = 8381677) B8381677
theorem B4425515 : Blo 578813 4425515 := bstep (se 1 (by rfl) ⟨3319136, by rfl⟩ : syracuseStep 4425515 = 6638273) B6638273
theorem B4524113 : Blo 578813 4524113 := bstep (se 2 (by rfl) ⟨1696542, by rfl⟩ : syracuseStep 4524113 = 3393085) B3393085
theorem B3968635 : Blo 578813 3968635 := bstep (se 1 (by rfl) ⟨2976476, by rfl⟩ : syracuseStep 3968635 = 5952953) B5952953
theorem B17174705 : Blo 578813 17174705 := bstep (se 2 (by rfl) ⟨6440514, by rfl⟩ : syracuseStep 17174705 = 12881029) B12881029
theorem B31822627 : Blo 578813 31822627 := bstep (se 1 (by rfl) ⟨23866970, by rfl⟩ : syracuseStep 31822627 = 47733941) B47733941
theorem B7443251 : Blo 578813 7443251 := bstep (se 1 (by rfl) ⟨5582438, by rfl⟩ : syracuseStep 7443251 = 11164877) B11164877
theorem B2200729 : Blo 578813 2200729 := bstep (se 2 (by rfl) ⟨825273, by rfl⟩ : syracuseStep 2200729 = 1650547) B1650547
theorem B8033701 : Blo 578813 8033701 := bstep (se 4 (by rfl) ⟨753159, by rfl⟩ : syracuseStep 8033701 = 1506319) B1506319
theorem B2201033 : Blo 578813 2201033 := bstep (se 2 (by rfl) ⟨825387, by rfl⟩ : syracuseStep 2201033 = 1650775) B1650775
theorem B8394185 : Blo 578813 8394185 := bstep (se 2 (by rfl) ⟨3147819, by rfl⟩ : syracuseStep 8394185 = 6295639) B6295639
theorem B2790875 : Blo 578813 2790875 := bstep (se 1 (by rfl) ⟨2093156, by rfl⟩ : syracuseStep 2790875 = 4186313) B4186313
theorem B3708605 : Blo 578813 3708605 := bstep (se 3 (by rfl) ⟨695363, by rfl⟩ : syracuseStep 3708605 = 1390727) B1390727
theorem B2201519 : Blo 578813 2201519 := bstep (se 1 (by rfl) ⟨1651139, by rfl⟩ : syracuseStep 2201519 = 3302279) B3302279
theorem B9410903 : Blo 578813 9410903 := bstep (se 1 (by rfl) ⟨7058177, by rfl⟩ : syracuseStep 9410903 = 14116355) B14116355
theorem B3775187 : Blo 578813 3775187 := bstep (se 1 (by rfl) ⟨2831390, by rfl⟩ : syracuseStep 3775187 = 5662781) B5662781
theorem B9706787 : Blo 578813 9706787 := bstep (se 1 (by rfl) ⟨7280090, by rfl⟩ : syracuseStep 9706787 = 14560181) B14560181
theorem B2203145 : Blo 578813 2203145 := bstep (se 2 (by rfl) ⟨826179, by rfl⟩ : syracuseStep 2203145 = 1652359) B1652359
theorem B1253227 : Blo 578813 1253227 := bstep (se 1 (by rfl) ⟨939920, by rfl⟩ : syracuseStep 1253227 = 1879841) B1879841
theorem B1417753 : Blo 578813 1417753 := bstep (se 2 (by rfl) ⟨531657, by rfl⟩ : syracuseStep 1417753 = 1063315) B1063315
theorem B2204603 : Blo 578813 2204603 := bstep (se 1 (by rfl) ⟨1653452, by rfl⟩ : syracuseStep 2204603 = 3306905) B3306905
theorem B4957793 : Blo 578813 4957793 := bstep (se 2 (by rfl) ⟨1859172, by rfl⟩ : syracuseStep 4957793 = 3718345) B3718345
theorem B149038841 : Blo 578813 149038841 := bstep (se 2 (by rfl) ⟨55889565, by rfl⟩ : syracuseStep 149038841 = 111779131) B111779131
theorem B3778589 : Blo 578813 3778589 := bstep (se 3 (by rfl) ⟨708485, by rfl⟩ : syracuseStep 3778589 = 1416971) B1416971
theorem B3975425 : Blo 578813 3975425 := bstep (se 2 (by rfl) ⟨1490784, by rfl⟩ : syracuseStep 3975425 = 2981569) B2981569
theorem B2796065 : Blo 578813 2796065 := bstep (se 2 (by rfl) ⟨1048524, by rfl⟩ : syracuseStep 2796065 = 2097049) B2097049
theorem B2239123 : Blo 578813 2239123 := bstep (se 1 (by rfl) ⟨1679342, by rfl⟩ : syracuseStep 2239123 = 3358685) B3358685
theorem B928427 : Blo 578813 928427 := bstep (se 1 (by rfl) ⟨696320, by rfl⟩ : syracuseStep 928427 = 1392641) B1392641
theorem B1649591 : Blo 578813 1649591 := bstep (se 1 (by rfl) ⟨1237193, by rfl⟩ : syracuseStep 1649591 = 2474387) B2474387
theorem B4074515 : Blo 578813 4074515 := bstep (se 1 (by rfl) ⟨3055886, by rfl⟩ : syracuseStep 4074515 = 6111773) B6111773
theorem B2206835 : Blo 578813 2206835 := bstep (se 1 (by rfl) ⟨1655126, by rfl⟩ : syracuseStep 2206835 = 3310253) B3310253
theorem B4304119 : Blo 578813 4304119 := bstep (se 1 (by rfl) ⟨3228089, by rfl⟩ : syracuseStep 4304119 = 6456179) B6456179
theorem B15871265 : Blo 578813 15871265 := bstep (se 2 (by rfl) ⟨5951724, by rfl⟩ : syracuseStep 15871265 = 11903449) B11903449
theorem B699823 : Blo 578813 699823 := bstep (se 1 (by rfl) ⟨524867, by rfl⟩ : syracuseStep 699823 = 1049735) B1049735
theorem B1650365 : Blo 578813 1650365 := bstep (se 3 (by rfl) ⟨309443, by rfl⟩ : syracuseStep 1650365 = 618887) B618887
theorem B1650593 : Blo 578813 1650593 := bstep (se 2 (by rfl) ⟨618972, by rfl⟩ : syracuseStep 1650593 = 1237945) B1237945
theorem B1650935 : Blo 578813 1650935 := bstep (se 1 (by rfl) ⟨1238201, by rfl⟩ : syracuseStep 1650935 = 2476403) B2476403
theorem B1651049 : Blo 578813 1651049 := bstep (se 2 (by rfl) ⟨619143, by rfl⟩ : syracuseStep 1651049 = 1238287) B1238287
theorem B995771 : Blo 578813 995771 := bstep (se 1 (by rfl) ⟨746828, by rfl⟩ : syracuseStep 995771 = 1493657) B1493657
theorem B10629731 : Blo 578813 10629731 := bstep (se 1 (by rfl) ⟨7972298, by rfl⟩ : syracuseStep 10629731 = 15944597) B15944597
theorem B2208505 : Blo 578813 2208505 := bstep (se 2 (by rfl) ⟨828189, by rfl⟩ : syracuseStep 2208505 = 1656379) B1656379
theorem B4961483 : Blo 578813 4961483 := bstep (se 1 (by rfl) ⟨3721112, by rfl⟩ : syracuseStep 4961483 = 7442225) B7442225
theorem B931247 : Blo 578813 931247 := bstep (se 1 (by rfl) ⟨698435, by rfl⟩ : syracuseStep 931247 = 1396871) B1396871
theorem B1652233 : Blo 578813 1652233 := bstep (se 2 (by rfl) ⟨619587, by rfl⟩ : syracuseStep 1652233 = 1239175) B1239175
theorem B3716705 : Blo 578813 3716705 := bstep (se 2 (by rfl) ⟨1393764, by rfl⟩ : syracuseStep 3716705 = 2787529) B2787529
theorem B931657 : Blo 578813 931657 := bstep (se 2 (by rfl) ⟨349371, by rfl⟩ : syracuseStep 931657 = 698743) B698743
theorem B1652575 : Blo 578813 1652575 := bstep (se 1 (by rfl) ⟨1239431, by rfl⟩ : syracuseStep 1652575 = 2478863) B2478863
theorem B735151 : Blo 578813 735151 := bstep (se 1 (by rfl) ⟨551363, by rfl⟩ : syracuseStep 735151 = 1102727) B1102727
theorem B1325135 : Blo 578813 1325135 := bstep (se 1 (by rfl) ⟨993851, by rfl⟩ : syracuseStep 1325135 = 1987703) B1987703
theorem B2209949 : Blo 578813 2209949 := bstep (se 3 (by rfl) ⟨414365, by rfl⟩ : syracuseStep 2209949 = 828731) B828731
theorem B2209963 : Blo 578813 2209963 := bstep (se 1 (by rfl) ⟨1657472, by rfl⟩ : syracuseStep 2209963 = 3314945) B3314945
theorem B932239 : Blo 578813 932239 := bstep (se 1 (by rfl) ⟨699179, by rfl⟩ : syracuseStep 932239 = 1398359) B1398359
theorem B2210267 : Blo 578813 2210267 := bstep (se 1 (by rfl) ⟨1657700, by rfl⟩ : syracuseStep 2210267 = 3315401) B3315401
theorem B1653463 : Blo 578813 1653463 := bstep (se 1 (by rfl) ⟨1240097, by rfl⟩ : syracuseStep 1653463 = 2480195) B2480195
theorem B10566389 : Blo 578813 10566389 := bstep (se 5 (by rfl) ⟨495299, by rfl⟩ : syracuseStep 10566389 = 990599) B990599
theorem B3980215 : Blo 578813 3980215 := bstep (se 1 (by rfl) ⟨2985161, by rfl⟩ : syracuseStep 3980215 = 5970323) B5970323
theorem B1653691 : Blo 578813 1653691 := bstep (se 1 (by rfl) ⟨1240268, by rfl⟩ : syracuseStep 1653691 = 2480537) B2480537
theorem B736219 : Blo 578813 736219 := bstep (se 1 (by rfl) ⟨552164, by rfl⟩ : syracuseStep 736219 = 1104329) B1104329
theorem B2931713 : Blo 578813 2931713 := bstep (se 2 (by rfl) ⟨1099392, by rfl⟩ : syracuseStep 2931713 = 2198785) B2198785
theorem B1653817 : Blo 578813 1653817 := bstep (se 2 (by rfl) ⟨620181, by rfl⟩ : syracuseStep 1653817 = 1240363) B1240363
theorem B1883657 : Blo 578813 1883657 := bstep (se 2 (by rfl) ⟨706371, by rfl⟩ : syracuseStep 1883657 = 1412743) B1412743
theorem B2932523 : Blo 578813 2932523 := bstep (se 1 (by rfl) ⟨2199392, by rfl⟩ : syracuseStep 2932523 = 4398785) B4398785
theorem B868271 : Blo 578813 868271 := bstep (se 1 (by rfl) ⟨651203, by rfl⟩ : syracuseStep 868271 = 1302407) B1302407
theorem B868361 : Blo 578813 868361 := bstep (se 2 (by rfl) ⟨325635, by rfl⟩ : syracuseStep 868361 = 651271) B651271
theorem B5980175 : Blo 578813 5980175 := bstep (se 1 (by rfl) ⟨4485131, by rfl⟩ : syracuseStep 5980175 = 8970263) B8970263
theorem B868391 : Blo 578813 868391 := bstep (se 1 (by rfl) ⟨651293, by rfl⟩ : syracuseStep 868391 = 1302587) B1302587
theorem B868475 : Blo 578813 868475 := bstep (se 1 (by rfl) ⟨651356, by rfl⟩ : syracuseStep 868475 = 1302713) B1302713
theorem B7422131 : Blo 578813 7422131 := bstep (se 1 (by rfl) ⟨5566598, by rfl⟩ : syracuseStep 7422131 = 11133197) B11133197
theorem B868601 : Blo 578813 868601 := bstep (se 2 (by rfl) ⟨325725, by rfl⟩ : syracuseStep 868601 = 651451) B651451
theorem B868703 : Blo 578813 868703 := bstep (se 1 (by rfl) ⟨651527, by rfl⟩ : syracuseStep 868703 = 1303055) B1303055
theorem B868715 : Blo 578813 868715 := bstep (se 1 (by rfl) ⟨651536, by rfl⟩ : syracuseStep 868715 = 1303073) B1303073
theorem B22921751 : Blo 578813 22921751 := bstep (se 1 (by rfl) ⟨17191313, by rfl⟩ : syracuseStep 22921751 = 34382627) B34382627
theorem B868943 : Blo 578813 868943 := bstep (se 1 (by rfl) ⟨651707, by rfl⟩ : syracuseStep 868943 = 1303415) B1303415
theorem B869063 : Blo 578813 869063 := bstep (se 1 (by rfl) ⟨651797, by rfl⟩ : syracuseStep 869063 = 1303595) B1303595
theorem B4408019 : Blo 578813 4408019 := bstep (se 1 (by rfl) ⟨3306014, by rfl⟩ : syracuseStep 4408019 = 6612029) B6612029
theorem B869225 : Blo 578813 869225 := bstep (se 2 (by rfl) ⟨325959, by rfl⟩ : syracuseStep 869225 = 651919) B651919
theorem B869303 : Blo 578813 869303 := bstep (se 1 (by rfl) ⟨651977, by rfl⟩ : syracuseStep 869303 = 1303955) B1303955
theorem B869339 : Blo 578813 869339 := bstep (se 1 (by rfl) ⟨652004, by rfl⟩ : syracuseStep 869339 = 1304009) B1304009
theorem B2212865 : Blo 578813 2212865 := bstep (se 2 (by rfl) ⟨829824, by rfl⟩ : syracuseStep 2212865 = 1659649) B1659649
theorem B11289619 : Blo 578813 11289619 := bstep (se 1 (by rfl) ⟨8467214, by rfl⟩ : syracuseStep 11289619 = 16934429) B16934429
theorem B836857 : Blo 578813 836857 := bstep (se 2 (by rfl) ⟨313821, by rfl⟩ : syracuseStep 836857 = 627643) B627643
theorem B6636815 : Blo 578813 6636815 := bstep (se 1 (by rfl) ⟨4977611, by rfl⟩ : syracuseStep 6636815 = 9955223) B9955223
theorem B869807 : Blo 578813 869807 := bstep (se 1 (by rfl) ⟨652355, by rfl⟩ : syracuseStep 869807 = 1304711) B1304711
theorem B1099271 : Blo 578813 1099271 := bstep (se 1 (by rfl) ⟨824453, by rfl⟩ : syracuseStep 1099271 = 1648907) B1648907
theorem B869897 : Blo 578813 869897 := bstep (se 2 (by rfl) ⟨326211, by rfl⟩ : syracuseStep 869897 = 652423) B652423
theorem B869927 : Blo 578813 869927 := bstep (se 1 (by rfl) ⟨652445, by rfl⟩ : syracuseStep 869927 = 1304891) B1304891
theorem B12699179 : Blo 578813 12699179 := bstep (se 1 (by rfl) ⟨9524384, by rfl⟩ : syracuseStep 12699179 = 19048769) B19048769
theorem B870011 : Blo 578813 870011 := bstep (se 1 (by rfl) ⟨652508, by rfl⟩ : syracuseStep 870011 = 1305017) B1305017
theorem B870137 : Blo 578813 870137 := bstep (se 2 (by rfl) ⟨326301, by rfl⟩ : syracuseStep 870137 = 652603) B652603
theorem B8931161 : Blo 578813 8931161 := bstep (se 2 (by rfl) ⟨3349185, by rfl⟩ : syracuseStep 8931161 = 6698371) B6698371
theorem B870239 : Blo 578813 870239 := bstep (se 1 (by rfl) ⟨652679, by rfl⟩ : syracuseStep 870239 = 1305359) B1305359
theorem B870251 : Blo 578813 870251 := bstep (se 1 (by rfl) ⟨652688, by rfl⟩ : syracuseStep 870251 = 1305377) B1305377
theorem B2934791 : Blo 578813 2934791 := bstep (se 1 (by rfl) ⟨2201093, by rfl⟩ : syracuseStep 2934791 = 4402187) B4402187
theorem B4180025 : Blo 578813 4180025 := bstep (se 2 (by rfl) ⟨1567509, by rfl⟩ : syracuseStep 4180025 = 3135019) B3135019
theorem B870479 : Blo 578813 870479 := bstep (se 1 (by rfl) ⟨652859, by rfl⟩ : syracuseStep 870479 = 1305719) B1305719
theorem B870599 : Blo 578813 870599 := bstep (se 1 (by rfl) ⟨652949, by rfl⟩ : syracuseStep 870599 = 1305899) B1305899
theorem B1100137 : Blo 578813 1100137 := bstep (se 2 (by rfl) ⟨412551, by rfl⟩ : syracuseStep 1100137 = 825103) B825103
theorem B870761 : Blo 578813 870761 := bstep (se 2 (by rfl) ⟨326535, by rfl⟩ : syracuseStep 870761 = 653071) B653071
theorem B3131777 : Blo 578813 3131777 := bstep (se 2 (by rfl) ⟨1174416, by rfl⟩ : syracuseStep 3131777 = 2348833) B2348833
theorem B870839 : Blo 578813 870839 := bstep (se 1 (by rfl) ⟨653129, by rfl⟩ : syracuseStep 870839 = 1306259) B1306259
theorem B870875 : Blo 578813 870875 := bstep (se 1 (by rfl) ⟨653156, by rfl⟩ : syracuseStep 870875 = 1306313) B1306313
theorem B2935277 : Blo 578813 2935277 := bstep (se 3 (by rfl) ⟨550364, by rfl⟩ : syracuseStep 2935277 = 1100729) B1100729
theorem B1100297 : Blo 578813 1100297 := bstep (se 2 (by rfl) ⟨412611, by rfl⟩ : syracuseStep 1100297 = 825223) B825223
theorem B871343 : Blo 578813 871343 := bstep (se 1 (by rfl) ⟨653507, by rfl⟩ : syracuseStep 871343 = 1307015) B1307015
theorem B871433 : Blo 578813 871433 := bstep (se 2 (by rfl) ⟨326787, by rfl⟩ : syracuseStep 871433 = 653575) B653575
theorem B871463 : Blo 578813 871463 := bstep (se 1 (by rfl) ⟨653597, by rfl⟩ : syracuseStep 871463 = 1307195) B1307195
theorem B871547 : Blo 578813 871547 := bstep (se 1 (by rfl) ⟨653660, by rfl⟩ : syracuseStep 871547 = 1307321) B1307321
theorem B871673 : Blo 578813 871673 := bstep (se 2 (by rfl) ⟨326877, by rfl⟩ : syracuseStep 871673 = 653755) B653755
theorem B2936087 : Blo 578813 2936087 := bstep (se 1 (by rfl) ⟨2202065, by rfl⟩ : syracuseStep 2936087 = 4404131) B4404131
theorem B871775 : Blo 578813 871775 := bstep (se 1 (by rfl) ⟨653831, by rfl⟩ : syracuseStep 871775 = 1307663) B1307663
theorem B871787 : Blo 578813 871787 := bstep (se 1 (by rfl) ⟨653840, by rfl⟩ : syracuseStep 871787 = 1307681) B1307681
theorem B1396187 : Blo 578813 1396187 := bstep (se 1 (by rfl) ⟨1047140, by rfl⟩ : syracuseStep 1396187 = 2094281) B2094281
theorem B1658407 : Blo 578813 1658407 := bstep (se 1 (by rfl) ⟨1243805, by rfl⟩ : syracuseStep 1658407 = 2487611) B2487611
theorem B872015 : Blo 578813 872015 := bstep (se 1 (by rfl) ⟨654011, by rfl⟩ : syracuseStep 872015 = 1308023) B1308023
theorem B1658465 : Blo 578813 1658465 := bstep (se 2 (by rfl) ⟨621924, by rfl⟩ : syracuseStep 1658465 = 1243849) B1243849
theorem B4476539 : Blo 578813 4476539 := bstep (se 1 (by rfl) ⟨3357404, by rfl⟩ : syracuseStep 4476539 = 6714809) B6714809
theorem B872135 : Blo 578813 872135 := bstep (se 1 (by rfl) ⟨654101, by rfl⟩ : syracuseStep 872135 = 1308203) B1308203
theorem B872297 : Blo 578813 872297 := bstep (se 2 (by rfl) ⟨327111, by rfl⟩ : syracuseStep 872297 = 654223) B654223
theorem B9424775 : Blo 578813 9424775 := bstep (se 1 (by rfl) ⟨7068581, by rfl⟩ : syracuseStep 9424775 = 14137163) B14137163
theorem B1953719 : Blo 578813 1953719 := bstep (se 1 (by rfl) ⟨1465289, by rfl⟩ : syracuseStep 1953719 = 2930579) B2930579
theorem B872375 : Blo 578813 872375 := bstep (se 1 (by rfl) ⟨654281, by rfl⟩ : syracuseStep 872375 = 1308563) B1308563
theorem B1101755 : Blo 578813 1101755 := bstep (se 1 (by rfl) ⟨826316, by rfl⟩ : syracuseStep 1101755 = 1652633) B1652633
theorem B872411 : Blo 578813 872411 := bstep (se 1 (by rfl) ⟨654308, by rfl⟩ : syracuseStep 872411 = 1308617) B1308617
theorem B4411421 : Blo 578813 4411421 := bstep (se 3 (by rfl) ⟨827141, by rfl⟩ : syracuseStep 4411421 = 1654283) B1654283
theorem B1102187 : Blo 578813 1102187 := bstep (se 1 (by rfl) ⟨826640, by rfl⟩ : syracuseStep 1102187 = 1653281) B1653281
theorem B1102241 : Blo 578813 1102241 := bstep (se 2 (by rfl) ⟨413340, by rfl⟩ : syracuseStep 1102241 = 826681) B826681
theorem B872879 : Blo 578813 872879 := bstep (se 1 (by rfl) ⟨654659, by rfl⟩ : syracuseStep 872879 = 1309319) B1309319
theorem B1954313 : Blo 578813 1954313 := bstep (se 2 (by rfl) ⟨732867, by rfl⟩ : syracuseStep 1954313 = 1465735) B1465735
theorem B872969 : Blo 578813 872969 := bstep (se 2 (by rfl) ⟨327363, by rfl⟩ : syracuseStep 872969 = 654727) B654727
theorem B872999 : Blo 578813 872999 := bstep (se 1 (by rfl) ⟨654749, by rfl⟩ : syracuseStep 872999 = 1309499) B1309499
theorem B16765541 : Blo 578813 16765541 := bstep (se 4 (by rfl) ⟨1571769, by rfl⟩ : syracuseStep 16765541 = 3143539) B3143539
theorem B873083 : Blo 578813 873083 := bstep (se 1 (by rfl) ⟨654812, by rfl⟩ : syracuseStep 873083 = 1309625) B1309625
theorem B873209 : Blo 578813 873209 := bstep (se 2 (by rfl) ⟨327453, by rfl⟩ : syracuseStep 873209 = 654907) B654907
theorem B873311 : Blo 578813 873311 := bstep (se 1 (by rfl) ⟨654983, by rfl⟩ : syracuseStep 873311 = 1309967) B1309967
theorem B2937707 : Blo 578813 2937707 := bstep (se 1 (by rfl) ⟨2203280, by rfl⟩ : syracuseStep 2937707 = 4406561) B4406561
theorem B873323 : Blo 578813 873323 := bstep (se 1 (by rfl) ⟨654992, by rfl⟩ : syracuseStep 873323 = 1309985) B1309985
theorem B5657519 : Blo 578813 5657519 := bstep (se 1 (by rfl) ⟨4243139, by rfl⟩ : syracuseStep 5657519 = 8486279) B8486279
theorem B7951279 : Blo 578813 7951279 := bstep (se 1 (by rfl) ⟨5963459, by rfl⟩ : syracuseStep 7951279 = 11926919) B11926919
theorem B873551 : Blo 578813 873551 := bstep (se 1 (by rfl) ⟨655163, by rfl⟩ : syracuseStep 873551 = 1310327) B1310327
theorem B873671 : Blo 578813 873671 := bstep (se 1 (by rfl) ⟨655253, by rfl⟩ : syracuseStep 873671 = 1310507) B1310507
theorem B19158287 : Blo 578813 19158287 := bstep (se 1 (by rfl) ⟨14368715, by rfl⟩ : syracuseStep 19158287 = 28737431) B28737431
theorem B578855 : Blo 578813 578855 := bstep (se 1 (by rfl) ⟨434141, by rfl⟩ : syracuseStep 578855 = 868283) B868283
theorem B578895 : Blo 578813 578895 := bstep (se 1 (by rfl) ⟨434171, by rfl⟩ : syracuseStep 578895 = 868343) B868343
theorem B578911 : Blo 578813 578911 := bstep (se 1 (by rfl) ⟨434183, by rfl⟩ : syracuseStep 578911 = 868367) B868367
theorem B1955177 : Blo 578813 1955177 := bstep (se 2 (by rfl) ⟨733191, by rfl⟩ : syracuseStep 1955177 = 1466383) B1466383
theorem B873833 : Blo 578813 873833 := bstep (se 2 (by rfl) ⟨327687, by rfl⟩ : syracuseStep 873833 = 655375) B655375
theorem B578939 : Blo 578813 578939 := bstep (se 1 (by rfl) ⟨434204, by rfl⟩ : syracuseStep 578939 = 868409) B868409
theorem B76567949 : Blo 578813 76567949 := bstep (se 3 (by rfl) ⟨14356490, by rfl⟩ : syracuseStep 76567949 = 28712981) B28712981
theorem B578991 : Blo 578813 578991 := bstep (se 1 (by rfl) ⟨434243, by rfl⟩ : syracuseStep 578991 = 868487) B868487
theorem B873911 : Blo 578813 873911 := bstep (se 1 (by rfl) ⟨655433, by rfl⟩ : syracuseStep 873911 = 1310867) B1310867
theorem B579015 : Blo 578813 579015 := bstep (se 1 (by rfl) ⟨434261, by rfl⟩ : syracuseStep 579015 = 868523) B868523
theorem B1856969 : Blo 578813 1856969 := bstep (se 2 (by rfl) ⟨696363, by rfl⟩ : syracuseStep 1856969 = 1392727) B1392727
theorem B579035 : Blo 578813 579035 := bstep (se 1 (by rfl) ⟨434276, by rfl⟩ : syracuseStep 579035 = 868553) B868553
theorem B873947 : Blo 578813 873947 := bstep (se 1 (by rfl) ⟨655460, by rfl⟩ : syracuseStep 873947 = 1310921) B1310921
theorem B2938355 : Blo 578813 2938355 := bstep (se 1 (by rfl) ⟨2203766, by rfl⟩ : syracuseStep 2938355 = 4407533) B4407533
theorem B579111 : Blo 578813 579111 := bstep (se 1 (by rfl) ⟨434333, by rfl⟩ : syracuseStep 579111 = 868667) B868667
theorem B579151 : Blo 578813 579151 := bstep (se 1 (by rfl) ⟨434363, by rfl⟩ : syracuseStep 579151 = 868727) B868727
theorem B579167 : Blo 578813 579167 := bstep (se 1 (by rfl) ⟨434375, by rfl⟩ : syracuseStep 579167 = 868751) B868751
theorem B579195 : Blo 578813 579195 := bstep (se 1 (by rfl) ⟨434396, by rfl⟩ : syracuseStep 579195 = 868793) B868793
theorem B579247 : Blo 578813 579247 := bstep (se 1 (by rfl) ⟨434435, by rfl⟩ : syracuseStep 579247 = 868871) B868871
theorem B579271 : Blo 578813 579271 := bstep (se 1 (by rfl) ⟨434453, by rfl⟩ : syracuseStep 579271 = 868907) B868907
theorem B579291 : Blo 578813 579291 := bstep (se 1 (by rfl) ⟨434468, by rfl⟩ : syracuseStep 579291 = 868937) B868937
theorem B579367 : Blo 578813 579367 := bstep (se 1 (by rfl) ⟨434525, by rfl⟩ : syracuseStep 579367 = 869051) B869051
theorem B579407 : Blo 578813 579407 := bstep (se 1 (by rfl) ⟨434555, by rfl⟩ : syracuseStep 579407 = 869111) B869111
theorem B579423 : Blo 578813 579423 := bstep (se 1 (by rfl) ⟨434567, by rfl⟩ : syracuseStep 579423 = 869135) B869135
theorem B579451 : Blo 578813 579451 := bstep (se 1 (by rfl) ⟨434588, by rfl⟩ : syracuseStep 579451 = 869177) B869177
theorem B579503 : Blo 578813 579503 := bstep (se 1 (by rfl) ⟨434627, by rfl⟩ : syracuseStep 579503 = 869255) B869255
theorem B2086843 : Blo 578813 2086843 := bstep (se 1 (by rfl) ⟨1565132, by rfl⟩ : syracuseStep 2086843 = 3130265) B3130265
theorem B1955771 : Blo 578813 1955771 := bstep (se 1 (by rfl) ⟨1466828, by rfl⟩ : syracuseStep 1955771 = 2933657) B2933657
theorem B579527 : Blo 578813 579527 := bstep (se 1 (by rfl) ⟨434645, by rfl⟩ : syracuseStep 579527 = 869291) B869291
theorem B579547 : Blo 578813 579547 := bstep (se 1 (by rfl) ⟨434660, by rfl⟩ : syracuseStep 579547 = 869321) B869321
theorem B1103881 : Blo 578813 1103881 := bstep (se 2 (by rfl) ⟨413955, by rfl⟩ : syracuseStep 1103881 = 827911) B827911
theorem B579623 : Blo 578813 579623 := bstep (se 1 (by rfl) ⟨434717, by rfl⟩ : syracuseStep 579623 = 869435) B869435
theorem B579663 : Blo 578813 579663 := bstep (se 1 (by rfl) ⟨434747, by rfl⟩ : syracuseStep 579663 = 869495) B869495
theorem B579679 : Blo 578813 579679 := bstep (se 1 (by rfl) ⟨434759, by rfl⟩ : syracuseStep 579679 = 869519) B869519
theorem B579707 : Blo 578813 579707 := bstep (se 1 (by rfl) ⟨434780, by rfl⟩ : syracuseStep 579707 = 869561) B869561
theorem B579759 : Blo 578813 579759 := bstep (se 1 (by rfl) ⟨434819, by rfl⟩ : syracuseStep 579759 = 869639) B869639
theorem B579783 : Blo 578813 579783 := bstep (se 1 (by rfl) ⟨434837, by rfl⟩ : syracuseStep 579783 = 869675) B869675
theorem B579803 : Blo 578813 579803 := bstep (se 1 (by rfl) ⟨434852, by rfl⟩ : syracuseStep 579803 = 869705) B869705
theorem B579879 : Blo 578813 579879 := bstep (se 1 (by rfl) ⟨434909, by rfl⟩ : syracuseStep 579879 = 869819) B869819
theorem B579919 : Blo 578813 579919 := bstep (se 1 (by rfl) ⟨434939, by rfl⟩ : syracuseStep 579919 = 869879) B869879
theorem B579935 : Blo 578813 579935 := bstep (se 1 (by rfl) ⟨434951, by rfl⟩ : syracuseStep 579935 = 869903) B869903
theorem B579963 : Blo 578813 579963 := bstep (se 1 (by rfl) ⟨434972, by rfl⟩ : syracuseStep 579963 = 869945) B869945
theorem B1857917 : Blo 578813 1857917 := bstep (se 3 (by rfl) ⟨348359, by rfl⟩ : syracuseStep 1857917 = 696719) B696719
theorem B580015 : Blo 578813 580015 := bstep (se 1 (by rfl) ⟨435011, by rfl⟩ : syracuseStep 580015 = 870023) B870023
theorem B580039 : Blo 578813 580039 := bstep (se 1 (by rfl) ⟨435029, by rfl⟩ : syracuseStep 580039 = 870059) B870059
theorem B580059 : Blo 578813 580059 := bstep (se 1 (by rfl) ⟨435044, by rfl⟩ : syracuseStep 580059 = 870089) B870089
theorem B580135 : Blo 578813 580135 := bstep (se 1 (by rfl) ⟨435101, by rfl⟩ : syracuseStep 580135 = 870203) B870203
theorem B580175 : Blo 578813 580175 := bstep (se 1 (by rfl) ⟨435131, by rfl⟩ : syracuseStep 580175 = 870263) B870263
theorem B580191 : Blo 578813 580191 := bstep (se 1 (by rfl) ⟨435143, by rfl⟩ : syracuseStep 580191 = 870287) B870287
theorem B580219 : Blo 578813 580219 := bstep (se 1 (by rfl) ⟨435164, by rfl⟩ : syracuseStep 580219 = 870329) B870329
theorem B580271 : Blo 578813 580271 := bstep (se 1 (by rfl) ⟨435203, by rfl⟩ : syracuseStep 580271 = 870407) B870407
theorem B580295 : Blo 578813 580295 := bstep (se 1 (by rfl) ⟨435221, by rfl⟩ : syracuseStep 580295 = 870443) B870443
theorem B2972371 : Blo 578813 2972371 := bstep (se 1 (by rfl) ⟨2229278, by rfl⟩ : syracuseStep 2972371 = 4458557) B4458557
theorem B580315 : Blo 578813 580315 := bstep (se 1 (by rfl) ⟨435236, by rfl⟩ : syracuseStep 580315 = 870473) B870473
theorem B2939651 : Blo 578813 2939651 := bstep (se 1 (by rfl) ⟨2204738, by rfl⟩ : syracuseStep 2939651 = 4409477) B4409477
theorem B4971293 : Blo 578813 4971293 := bstep (se 3 (by rfl) ⟨932117, by rfl⟩ : syracuseStep 4971293 = 1864235) B1864235
theorem B580391 : Blo 578813 580391 := bstep (se 1 (by rfl) ⟨435293, by rfl⟩ : syracuseStep 580391 = 870587) B870587
theorem B580431 : Blo 578813 580431 := bstep (se 1 (by rfl) ⟨435323, by rfl⟩ : syracuseStep 580431 = 870647) B870647
theorem B580447 : Blo 578813 580447 := bstep (se 1 (by rfl) ⟨435335, by rfl⟩ : syracuseStep 580447 = 870671) B870671
theorem B580475 : Blo 578813 580475 := bstep (se 1 (by rfl) ⟨435356, by rfl⟩ : syracuseStep 580475 = 870713) B870713
theorem B1465249 : Blo 578813 1465249 := bstep (se 2 (by rfl) ⟨549468, by rfl⟩ : syracuseStep 1465249 = 1098937) B1098937
theorem B580527 : Blo 578813 580527 := bstep (se 1 (by rfl) ⟨435395, by rfl⟩ : syracuseStep 580527 = 870791) B870791
theorem B1104815 : Blo 578813 1104815 := bstep (se 1 (by rfl) ⟨828611, by rfl⟩ : syracuseStep 1104815 = 1657223) B1657223
theorem B580551 : Blo 578813 580551 := bstep (se 1 (by rfl) ⟨435413, by rfl⟩ : syracuseStep 580551 = 870827) B870827
theorem B580571 : Blo 578813 580571 := bstep (se 1 (by rfl) ⟨435428, by rfl⟩ : syracuseStep 580571 = 870857) B870857
theorem B580647 : Blo 578813 580647 := bstep (se 1 (by rfl) ⟨435485, by rfl⟩ : syracuseStep 580647 = 870971) B870971
theorem B580687 : Blo 578813 580687 := bstep (se 1 (by rfl) ⟨435515, by rfl⟩ : syracuseStep 580687 = 871031) B871031
theorem B580703 : Blo 578813 580703 := bstep (se 1 (by rfl) ⟨435527, by rfl⟩ : syracuseStep 580703 = 871055) B871055
theorem B580731 : Blo 578813 580731 := bstep (se 1 (by rfl) ⟨435548, by rfl⟩ : syracuseStep 580731 = 871097) B871097
theorem B580783 : Blo 578813 580783 := bstep (se 1 (by rfl) ⟨435587, by rfl⟩ : syracuseStep 580783 = 871175) B871175
theorem B3300547 : Blo 578813 3300547 := bstep (se 1 (by rfl) ⟨2475410, by rfl⟩ : syracuseStep 3300547 = 4950821) B4950821
theorem B580807 : Blo 578813 580807 := bstep (se 1 (by rfl) ⟨435605, by rfl⟩ : syracuseStep 580807 = 871211) B871211
theorem B580827 : Blo 578813 580827 := bstep (se 1 (by rfl) ⟨435620, by rfl⟩ : syracuseStep 580827 = 871241) B871241
theorem B580903 : Blo 578813 580903 := bstep (se 1 (by rfl) ⟨435677, by rfl⟩ : syracuseStep 580903 = 871355) B871355
theorem B580943 : Blo 578813 580943 := bstep (se 1 (by rfl) ⟨435707, by rfl⟩ : syracuseStep 580943 = 871415) B871415
theorem B580959 : Blo 578813 580959 := bstep (se 1 (by rfl) ⟨435719, by rfl⟩ : syracuseStep 580959 = 871439) B871439
theorem B580987 : Blo 578813 580987 := bstep (se 1 (by rfl) ⟨435740, by rfl⟩ : syracuseStep 580987 = 871481) B871481
theorem B581039 : Blo 578813 581039 := bstep (se 1 (by rfl) ⟨435779, by rfl⟩ : syracuseStep 581039 = 871559) B871559
theorem B1105339 : Blo 578813 1105339 := bstep (se 1 (by rfl) ⟨829004, by rfl⟩ : syracuseStep 1105339 = 1658009) B1658009
theorem B581063 : Blo 578813 581063 := bstep (se 1 (by rfl) ⟨435797, by rfl⟩ : syracuseStep 581063 = 871595) B871595
theorem B581083 : Blo 578813 581083 := bstep (se 1 (by rfl) ⟨435812, by rfl⟩ : syracuseStep 581083 = 871625) B871625
theorem B1072649 : Blo 578813 1072649 := bstep (se 2 (by rfl) ⟨402243, by rfl⟩ : syracuseStep 1072649 = 804487) B804487
theorem B581159 : Blo 578813 581159 := bstep (se 1 (by rfl) ⟨435869, by rfl⟩ : syracuseStep 581159 = 871739) B871739
theorem B581199 : Blo 578813 581199 := bstep (se 1 (by rfl) ⟨435899, by rfl⟩ : syracuseStep 581199 = 871799) B871799
theorem B581215 : Blo 578813 581215 := bstep (se 1 (by rfl) ⟨435911, by rfl⟩ : syracuseStep 581215 = 871823) B871823
theorem B1957499 : Blo 578813 1957499 := bstep (se 1 (by rfl) ⟨1468124, by rfl⟩ : syracuseStep 1957499 = 2936249) B2936249
theorem B581243 : Blo 578813 581243 := bstep (se 1 (by rfl) ⟨435932, by rfl⟩ : syracuseStep 581243 = 871865) B871865
theorem B6610571 : Blo 578813 6610571 := bstep (se 1 (by rfl) ⟨4957928, by rfl⟩ : syracuseStep 6610571 = 9915857) B9915857
theorem B581295 : Blo 578813 581295 := bstep (se 1 (by rfl) ⟨435971, by rfl⟩ : syracuseStep 581295 = 871943) B871943
theorem B581319 : Blo 578813 581319 := bstep (se 1 (by rfl) ⟨435989, by rfl⟩ : syracuseStep 581319 = 871979) B871979
theorem B4579031 : Blo 578813 4579031 := bstep (se 1 (by rfl) ⟨3434273, by rfl⟩ : syracuseStep 4579031 = 6868547) B6868547
theorem B581339 : Blo 578813 581339 := bstep (se 1 (by rfl) ⟨436004, by rfl⟩ : syracuseStep 581339 = 872009) B872009
theorem B1957661 : Blo 578813 1957661 := bstep (se 3 (by rfl) ⟨367061, by rfl⟩ : syracuseStep 1957661 = 734123) B734123
theorem B581415 : Blo 578813 581415 := bstep (se 1 (by rfl) ⟨436061, by rfl⟩ : syracuseStep 581415 = 872123) B872123
theorem B1236809 : Blo 578813 1236809 := bstep (se 2 (by rfl) ⟨463803, by rfl⟩ : syracuseStep 1236809 = 927607) B927607
theorem B581455 : Blo 578813 581455 := bstep (se 1 (by rfl) ⟨436091, by rfl⟩ : syracuseStep 581455 = 872183) B872183
theorem B581471 : Blo 578813 581471 := bstep (se 1 (by rfl) ⟨436103, by rfl⟩ : syracuseStep 581471 = 872207) B872207
theorem B581499 : Blo 578813 581499 := bstep (se 1 (by rfl) ⟨436124, by rfl⟩ : syracuseStep 581499 = 872249) B872249
theorem B1105825 : Blo 578813 1105825 := bstep (se 2 (by rfl) ⟨414684, by rfl⟩ : syracuseStep 1105825 = 829369) B829369
theorem B581551 : Blo 578813 581551 := bstep (se 1 (by rfl) ⟨436163, by rfl⟩ : syracuseStep 581551 = 872327) B872327
theorem B581575 : Blo 578813 581575 := bstep (se 1 (by rfl) ⟨436181, by rfl⟩ : syracuseStep 581575 = 872363) B872363
theorem B581595 : Blo 578813 581595 := bstep (se 1 (by rfl) ⟨436196, by rfl⟩ : syracuseStep 581595 = 872393) B872393
theorem B3727367 : Blo 578813 3727367 := bstep (se 1 (by rfl) ⟨2795525, by rfl⟩ : syracuseStep 3727367 = 5591051) B5591051
theorem B581671 : Blo 578813 581671 := bstep (se 1 (by rfl) ⟨436253, by rfl⟩ : syracuseStep 581671 = 872507) B872507
theorem B581711 : Blo 578813 581711 := bstep (se 1 (by rfl) ⟨436283, by rfl⟩ : syracuseStep 581711 = 872567) B872567
theorem B581727 : Blo 578813 581727 := bstep (se 1 (by rfl) ⟨436295, by rfl⟩ : syracuseStep 581727 = 872591) B872591
theorem B581755 : Blo 578813 581755 := bstep (se 1 (by rfl) ⟨436316, by rfl⟩ : syracuseStep 581755 = 872633) B872633
theorem B581807 : Blo 578813 581807 := bstep (se 1 (by rfl) ⟨436355, by rfl⟩ : syracuseStep 581807 = 872711) B872711
theorem B581831 : Blo 578813 581831 := bstep (se 1 (by rfl) ⟨436373, by rfl⟩ : syracuseStep 581831 = 872747) B872747
theorem B581851 : Blo 578813 581851 := bstep (se 1 (by rfl) ⟨436388, by rfl⟩ : syracuseStep 581851 = 872777) B872777
theorem B6283493 : Blo 578813 6283493 := bstep (se 4 (by rfl) ⟨589077, by rfl⟩ : syracuseStep 6283493 = 1178155) B1178155
theorem B581927 : Blo 578813 581927 := bstep (se 1 (by rfl) ⟨436445, by rfl⟩ : syracuseStep 581927 = 872891) B872891
theorem B4710707 : Blo 578813 4710707 := bstep (se 1 (by rfl) ⟨3533030, by rfl⟩ : syracuseStep 4710707 = 7066061) B7066061
theorem B4415795 : Blo 578813 4415795 := bstep (se 1 (by rfl) ⟨3311846, by rfl⟩ : syracuseStep 4415795 = 6623693) B6623693
theorem B581967 : Blo 578813 581967 := bstep (se 1 (by rfl) ⟨436475, by rfl⟩ : syracuseStep 581967 = 872951) B872951
theorem B2941271 : Blo 578813 2941271 := bstep (se 1 (by rfl) ⟨2205953, by rfl⟩ : syracuseStep 2941271 = 4411907) B4411907
theorem B581983 : Blo 578813 581983 := bstep (se 1 (by rfl) ⟨436487, by rfl⟩ : syracuseStep 581983 = 872975) B872975
theorem B582011 : Blo 578813 582011 := bstep (se 1 (by rfl) ⟨436508, by rfl⟩ : syracuseStep 582011 = 873017) B873017
theorem B582063 : Blo 578813 582063 := bstep (se 1 (by rfl) ⟨436547, by rfl⟩ : syracuseStep 582063 = 873095) B873095
theorem B582087 : Blo 578813 582087 := bstep (se 1 (by rfl) ⟨436565, by rfl⟩ : syracuseStep 582087 = 873131) B873131
theorem B1958363 : Blo 578813 1958363 := bstep (se 1 (by rfl) ⟨1468772, by rfl⟩ : syracuseStep 1958363 = 2937545) B2937545
theorem B582107 : Blo 578813 582107 := bstep (se 1 (by rfl) ⟨436580, by rfl⟩ : syracuseStep 582107 = 873161) B873161
theorem B582183 : Blo 578813 582183 := bstep (se 1 (by rfl) ⟨436637, by rfl⟩ : syracuseStep 582183 = 873275) B873275
theorem B582223 : Blo 578813 582223 := bstep (se 1 (by rfl) ⟨436667, by rfl⟩ : syracuseStep 582223 = 873335) B873335
theorem B582239 : Blo 578813 582239 := bstep (se 1 (by rfl) ⟨436679, by rfl⟩ : syracuseStep 582239 = 873359) B873359
theorem B1303163 : Blo 578813 1303163 := bstep (se 1 (by rfl) ⟨977372, by rfl⟩ : syracuseStep 1303163 = 1954745) B1954745
theorem B582267 : Blo 578813 582267 := bstep (se 1 (by rfl) ⟨436700, by rfl⟩ : syracuseStep 582267 = 873401) B873401
theorem B582319 : Blo 578813 582319 := bstep (se 1 (by rfl) ⟨436739, by rfl⟩ : syracuseStep 582319 = 873479) B873479
theorem B582343 : Blo 578813 582343 := bstep (se 1 (by rfl) ⟨436757, by rfl⟩ : syracuseStep 582343 = 873515) B873515
theorem B582363 : Blo 578813 582363 := bstep (se 1 (by rfl) ⟨436772, by rfl⟩ : syracuseStep 582363 = 873545) B873545
theorem B1303289 : Blo 578813 1303289 := bstep (se 2 (by rfl) ⟨488733, by rfl⟩ : syracuseStep 1303289 = 977467) B977467
theorem B582439 : Blo 578813 582439 := bstep (se 1 (by rfl) ⟨436829, by rfl⟩ : syracuseStep 582439 = 873659) B873659
theorem B8938291 : Blo 578813 8938291 := bstep (se 1 (by rfl) ⟨6703718, by rfl⟩ : syracuseStep 8938291 = 13407437) B13407437
theorem B582479 : Blo 578813 582479 := bstep (se 1 (by rfl) ⟨436859, by rfl⟩ : syracuseStep 582479 = 873719) B873719
theorem B582495 : Blo 578813 582495 := bstep (se 1 (by rfl) ⟨436871, by rfl⟩ : syracuseStep 582495 = 873743) B873743
theorem B582523 : Blo 578813 582523 := bstep (se 1 (by rfl) ⟨436892, by rfl⟩ : syracuseStep 582523 = 873785) B873785
theorem B3138479 : Blo 578813 3138479 := bstep (se 1 (by rfl) ⟨2353859, by rfl⟩ : syracuseStep 3138479 = 4707719) B4707719
theorem B582575 : Blo 578813 582575 := bstep (se 1 (by rfl) ⟨436931, by rfl⟩ : syracuseStep 582575 = 873863) B873863
theorem B582599 : Blo 578813 582599 := bstep (se 1 (by rfl) ⟨436949, by rfl⟩ : syracuseStep 582599 = 873899) B873899
theorem B582619 : Blo 578813 582619 := bstep (se 1 (by rfl) ⟨436964, by rfl⟩ : syracuseStep 582619 = 873929) B873929
theorem B1303559 : Blo 578813 1303559 := bstep (se 1 (by rfl) ⟨977669, by rfl⟩ : syracuseStep 1303559 = 1955339) B1955339
theorem B582695 : Blo 578813 582695 := bstep (se 1 (by rfl) ⟨437021, by rfl⟩ : syracuseStep 582695 = 874043) B874043
theorem B1303631 : Blo 578813 1303631 := bstep (se 1 (by rfl) ⟨977723, by rfl⟩ : syracuseStep 1303631 = 1955447) B1955447
theorem B582735 : Blo 578813 582735 := bstep (se 1 (by rfl) ⟨437051, by rfl⟩ : syracuseStep 582735 = 874103) B874103
theorem B582751 : Blo 578813 582751 := bstep (se 1 (by rfl) ⟨437063, by rfl⟩ : syracuseStep 582751 = 874127) B874127
theorem B582779 : Blo 578813 582779 := bstep (se 1 (by rfl) ⟨437084, by rfl⟩ : syracuseStep 582779 = 874169) B874169
theorem B1959065 : Blo 578813 1959065 := bstep (se 2 (by rfl) ⟨734649, by rfl⟩ : syracuseStep 1959065 = 1469299) B1469299
theorem B551380229 : Blo 578813 551380229 := bstep (se 4 (by rfl) ⟨51691896, by rfl⟩ : syracuseStep 551380229 = 103383793) B103383793
theorem B1860989 : Blo 578813 1860989 := bstep (se 3 (by rfl) ⟨348935, by rfl⟩ : syracuseStep 1860989 = 697871) B697871
theorem B1467791 : Blo 578813 1467791 := bstep (se 1 (by rfl) ⟨1100843, by rfl⟩ : syracuseStep 1467791 = 2201687) B2201687
theorem B1304027 : Blo 578813 1304027 := bstep (se 1 (by rfl) ⟨978020, by rfl⟩ : syracuseStep 1304027 = 1956041) B1956041
theorem B2516669 : Blo 578813 2516669 := bstep (se 3 (by rfl) ⟨471875, by rfl⟩ : syracuseStep 2516669 = 943751) B943751
theorem B1468115 : Blo 578813 1468115 := bstep (se 1 (by rfl) ⟨1101086, by rfl⟩ : syracuseStep 1468115 = 2202173) B2202173
theorem B1304495 : Blo 578813 1304495 := bstep (se 1 (by rfl) ⟨978371, by rfl⟩ : syracuseStep 1304495 = 1956743) B1956743
theorem B1861633 : Blo 578813 1861633 := bstep (se 2 (by rfl) ⟨698112, by rfl⟩ : syracuseStep 1861633 = 1396225) B1396225
theorem B1534009 : Blo 578813 1534009 := bstep (se 2 (by rfl) ⟨575253, by rfl⟩ : syracuseStep 1534009 = 1150507) B1150507
theorem B1304747 : Blo 578813 1304747 := bstep (se 1 (by rfl) ⟨978560, by rfl⟩ : syracuseStep 1304747 = 1957121) B1957121
theorem B977143 : Blo 578813 977143 := bstep (se 1 (by rfl) ⟨732857, by rfl⟩ : syracuseStep 977143 = 1465715) B1465715
theorem B9529649 : Blo 578813 9529649 := bstep (se 2 (by rfl) ⟨3573618, by rfl⟩ : syracuseStep 9529649 = 7147237) B7147237
theorem B1960253 : Blo 578813 1960253 := bstep (se 3 (by rfl) ⟨367547, by rfl⟩ : syracuseStep 1960253 = 735095) B735095
theorem B3729725 : Blo 578813 3729725 := bstep (se 3 (by rfl) ⟨699323, by rfl⟩ : syracuseStep 3729725 = 1398647) B1398647
theorem B977339 : Blo 578813 977339 := bstep (se 1 (by rfl) ⟨733004, by rfl⟩ : syracuseStep 977339 = 1466009) B1466009
theorem B977447 : Blo 578813 977447 := bstep (se 1 (by rfl) ⟨733085, by rfl⟩ : syracuseStep 977447 = 1466171) B1466171
theorem B4975289 : Blo 578813 4975289 := bstep (se 2 (by rfl) ⟨1865733, by rfl⟩ : syracuseStep 4975289 = 3731467) B3731467
theorem B19098305 : Blo 578813 19098305 := bstep (se 2 (by rfl) ⟨7161864, by rfl⟩ : syracuseStep 19098305 = 14323729) B14323729
theorem B1305287 : Blo 578813 1305287 := bstep (se 1 (by rfl) ⟨978965, by rfl⟩ : syracuseStep 1305287 = 1957931) B1957931
theorem B2648861 : Blo 578813 2648861 := bstep (se 3 (by rfl) ⟨496661, by rfl⟩ : syracuseStep 2648861 = 993323) B993323
theorem B977737 : Blo 578813 977737 := bstep (se 2 (by rfl) ⟨366651, by rfl⟩ : syracuseStep 977737 = 733303) B733303
theorem B1469279 : Blo 578813 1469279 := bstep (se 1 (by rfl) ⟨1101959, by rfl⟩ : syracuseStep 1469279 = 2203919) B2203919
theorem B977771 : Blo 578813 977771 := bstep (se 1 (by rfl) ⟨733328, by rfl⟩ : syracuseStep 977771 = 1466657) B1466657
theorem B1239995 : Blo 578813 1239995 := bstep (se 1 (by rfl) ⟨929996, by rfl⟩ : syracuseStep 1239995 = 1859993) B1859993
theorem B3304421 : Blo 578813 3304421 := bstep (se 4 (by rfl) ⟨309789, by rfl⟩ : syracuseStep 3304421 = 619579) B619579
theorem B1961117 : Blo 578813 1961117 := bstep (se 3 (by rfl) ⟨367709, by rfl⟩ : syracuseStep 1961117 = 735419) B735419
theorem B978169 : Blo 578813 978169 := bstep (se 2 (by rfl) ⟨366813, by rfl⟩ : syracuseStep 978169 = 733627) B733627
theorem B1863017 : Blo 578813 1863017 := bstep (se 2 (by rfl) ⟨698631, by rfl⟩ : syracuseStep 1863017 = 1397263) B1397263
theorem B4713947 : Blo 578813 4713947 := bstep (se 1 (by rfl) ⟨3535460, by rfl⟩ : syracuseStep 4713947 = 7070921) B7070921
theorem B3730931 : Blo 578813 3730931 := bstep (se 1 (by rfl) ⟨2798198, by rfl⟩ : syracuseStep 3730931 = 5596397) B5596397
theorem B978439 : Blo 578813 978439 := bstep (se 1 (by rfl) ⟨733829, by rfl⟩ : syracuseStep 978439 = 1467659) B1467659
theorem B1306151 : Blo 578813 1306151 := bstep (se 1 (by rfl) ⟨979613, by rfl⟩ : syracuseStep 1306151 = 1959227) B1959227
theorem B2485799 : Blo 578813 2485799 := bstep (se 1 (by rfl) ⟨1864349, by rfl⟩ : syracuseStep 2485799 = 3728699) B3728699
theorem B1961657 : Blo 578813 1961657 := bstep (se 2 (by rfl) ⟨735621, by rfl⟩ : syracuseStep 1961657 = 1471243) B1471243
theorem B3731159 : Blo 578813 3731159 := bstep (se 1 (by rfl) ⟨2798369, by rfl⟩ : syracuseStep 3731159 = 5596739) B5596739
theorem B2944835 : Blo 578813 2944835 := bstep (se 1 (by rfl) ⟨2208626, by rfl⟩ : syracuseStep 2944835 = 4417253) B4417253
theorem B1306475 : Blo 578813 1306475 := bstep (se 1 (by rfl) ⟨979856, by rfl⟩ : syracuseStep 1306475 = 1959713) B1959713
theorem B1306529 : Blo 578813 1306529 := bstep (se 2 (by rfl) ⟨489948, by rfl⟩ : syracuseStep 1306529 = 979897) B979897
theorem B1470383 : Blo 578813 1470383 := bstep (se 1 (by rfl) ⟨1102787, by rfl⟩ : syracuseStep 1470383 = 2205575) B2205575
theorem B978871 : Blo 578813 978871 := bstep (se 1 (by rfl) ⟨734153, by rfl⟩ : syracuseStep 978871 = 1468307) B1468307
theorem B651343 : Blo 578813 651343 := bstep (se 1 (by rfl) ⟨488507, by rfl⟩ : syracuseStep 651343 = 977015) B977015
theorem B979067 : Blo 578813 979067 := bstep (se 1 (by rfl) ⟨734300, by rfl⟩ : syracuseStep 979067 = 1468601) B1468601
theorem B1306871 : Blo 578813 1306871 := bstep (se 1 (by rfl) ⟨980153, by rfl⟩ : syracuseStep 1306871 = 1960307) B1960307
theorem B1962251 : Blo 578813 1962251 := bstep (se 1 (by rfl) ⟨1471688, by rfl⟩ : syracuseStep 1962251 = 2943377) B2943377
theorem B651739 : Blo 578813 651739 := bstep (se 1 (by rfl) ⟨488804, by rfl⟩ : syracuseStep 651739 = 977609) B977609
theorem B979465 : Blo 578813 979465 := bstep (se 2 (by rfl) ⟨367299, by rfl⟩ : syracuseStep 979465 = 734599) B734599
theorem B1962521 : Blo 578813 1962521 := bstep (se 2 (by rfl) ⟨735945, by rfl⟩ : syracuseStep 1962521 = 1471891) B1471891
theorem B979627 : Blo 578813 979627 := bstep (se 1 (by rfl) ⟨734720, by rfl⟩ : syracuseStep 979627 = 1469441) B1469441
theorem B717511 : Blo 578813 717511 := bstep (se 1 (by rfl) ⟨538133, by rfl⟩ : syracuseStep 717511 = 1076267) B1076267
theorem B2781955 : Blo 578813 2781955 := bstep (se 1 (by rfl) ⟨2086466, by rfl⟩ : syracuseStep 2781955 = 4172933) B4172933
theorem B1307465 : Blo 578813 1307465 := bstep (se 2 (by rfl) ⟨490299, by rfl⟩ : syracuseStep 1307465 = 980599) B980599
theorem B15070067 : Blo 578813 15070067 := bstep (se 1 (by rfl) ⟨11302550, by rfl⟩ : syracuseStep 15070067 = 22605101) B22605101
theorem B652207 : Blo 578813 652207 := bstep (se 1 (by rfl) ⟨489155, by rfl⟩ : syracuseStep 652207 = 978311) B978311
theorem B979931 : Blo 578813 979931 := bstep (se 1 (by rfl) ⟨734948, by rfl⟩ : syracuseStep 979931 = 1469897) B1469897
theorem B1045583 : Blo 578813 1045583 := bstep (se 1 (by rfl) ⟨784187, by rfl⟩ : syracuseStep 1045583 = 1568375) B1568375
theorem B1471567 : Blo 578813 1471567 := bstep (se 1 (by rfl) ⟨1103675, by rfl⟩ : syracuseStep 1471567 = 2207351) B2207351
theorem B14840981 : Blo 578813 14840981 := bstep (se 6 (by rfl) ⟨347835, by rfl⟩ : syracuseStep 14840981 = 695671) B695671
theorem B4945049 : Blo 578813 4945049 := bstep (se 2 (by rfl) ⟨1854393, by rfl⟩ : syracuseStep 4945049 = 3708787) B3708787
theorem B980167 : Blo 578813 980167 := bstep (se 1 (by rfl) ⟨735125, by rfl⟩ : syracuseStep 980167 = 1470251) B1470251
theorem B652639 : Blo 578813 652639 := bstep (se 1 (by rfl) ⟨489479, by rfl⟩ : syracuseStep 652639 = 978959) B978959
theorem B980329 : Blo 578813 980329 := bstep (se 2 (by rfl) ⟨367623, by rfl⟩ : syracuseStep 980329 = 735247) B735247
theorem B1308257 : Blo 578813 1308257 := bstep (se 2 (by rfl) ⟨490596, by rfl⟩ : syracuseStep 1308257 = 981193) B981193
theorem B1963655 : Blo 578813 1963655 := bstep (se 1 (by rfl) ⟨1472741, by rfl⟩ : syracuseStep 1963655 = 2945483) B2945483
theorem B2258579 : Blo 578813 2258579 := bstep (se 1 (by rfl) ⟨1693934, by rfl⟩ : syracuseStep 2258579 = 3387869) B3387869
theorem B1963709 : Blo 578813 1963709 := bstep (se 3 (by rfl) ⟨368195, by rfl⟩ : syracuseStep 1963709 = 736391) B736391
theorem B652999 : Blo 578813 652999 := bstep (se 1 (by rfl) ⟨489749, by rfl⟩ : syracuseStep 652999 = 979499) B979499
theorem B1472215 : Blo 578813 1472215 := bstep (se 1 (by rfl) ⟨1104161, by rfl⟩ : syracuseStep 1472215 = 2208323) B2208323
theorem B1963871 : Blo 578813 1963871 := bstep (se 1 (by rfl) ⟨1472903, by rfl⟩ : syracuseStep 1963871 = 2945807) B2945807
theorem B1308599 : Blo 578813 1308599 := bstep (se 1 (by rfl) ⟨981449, by rfl⟩ : syracuseStep 1308599 = 1962899) B1962899
theorem B980923 : Blo 578813 980923 := bstep (se 1 (by rfl) ⟨735692, by rfl⟩ : syracuseStep 980923 = 1471385) B1471385
theorem B1964033 : Blo 578813 1964033 := bstep (se 2 (by rfl) ⟨736512, by rfl⟩ : syracuseStep 1964033 = 1473025) B1473025
theorem B1472519 : Blo 578813 1472519 := bstep (se 1 (by rfl) ⟨1104389, by rfl⟩ : syracuseStep 1472519 = 2208779) B2208779
theorem B981031 : Blo 578813 981031 := bstep (se 1 (by rfl) ⟨735773, by rfl⟩ : syracuseStep 981031 = 1471547) B1471547
theorem B2357495 : Blo 578813 2357495 := bstep (se 1 (by rfl) ⟨1768121, by rfl⟩ : syracuseStep 2357495 = 3536243) B3536243
theorem B3307837 : Blo 578813 3307837 := bstep (se 3 (by rfl) ⟨620219, by rfl⟩ : syracuseStep 3307837 = 1240439) B1240439
theorem B981355 : Blo 578813 981355 := bstep (se 1 (by rfl) ⟨736016, by rfl⟩ : syracuseStep 981355 = 1472033) B1472033
theorem B1309193 : Blo 578813 1309193 := bstep (se 2 (by rfl) ⟨490947, by rfl⟩ : syracuseStep 1309193 = 981895) B981895
theorem B653863 : Blo 578813 653863 := bstep (se 1 (by rfl) ⟨490397, by rfl⟩ : syracuseStep 653863 = 980795) B980795
theorem B1964843 : Blo 578813 1964843 := bstep (se 1 (by rfl) ⟨1473632, by rfl⟩ : syracuseStep 1964843 = 2947265) B2947265
theorem B2947913 : Blo 578813 2947913 := bstep (se 2 (by rfl) ⟨1105467, by rfl⟩ : syracuseStep 2947913 = 2210935) B2210935
theorem B1309535 : Blo 578813 1309535 := bstep (se 1 (by rfl) ⟨982151, by rfl⟩ : syracuseStep 1309535 = 1964303) B1964303
theorem B1145707 : Blo 578813 1145707 := bstep (se 1 (by rfl) ⟨859280, by rfl⟩ : syracuseStep 1145707 = 1718561) B1718561
theorem B1244011 : Blo 578813 1244011 := bstep (se 1 (by rfl) ⟨933008, by rfl⟩ : syracuseStep 1244011 = 1866017) B1866017
theorem B5307281 : Blo 578813 5307281 := bstep (se 2 (by rfl) ⟨1990230, by rfl⟩ : syracuseStep 5307281 = 3980461) B3980461
theorem B1309715 : Blo 578813 1309715 := bstep (se 1 (by rfl) ⟨982286, by rfl⟩ : syracuseStep 1309715 = 1964573) B1964573
theorem B1965113 : Blo 578813 1965113 := bstep (se 2 (by rfl) ⟨736917, by rfl⟩ : syracuseStep 1965113 = 1473835) B1473835
theorem B2358467 : Blo 578813 2358467 := bstep (se 1 (by rfl) ⟨1768850, by rfl⟩ : syracuseStep 2358467 = 3537701) B3537701
theorem B1310057 : Blo 578813 1310057 := bstep (se 2 (by rfl) ⟨491271, by rfl⟩ : syracuseStep 1310057 = 982543) B982543
theorem B1965437 : Blo 578813 1965437 := bstep (se 3 (by rfl) ⟨368519, by rfl⟩ : syracuseStep 1965437 = 737039) B737039
theorem B2391439 : Blo 578813 2391439 := bstep (se 1 (by rfl) ⟨1793579, by rfl⟩ : syracuseStep 2391439 = 3587159) B3587159
theorem B982415 : Blo 578813 982415 := bstep (se 1 (by rfl) ⟨736811, by rfl⟩ : syracuseStep 982415 = 1473623) B1473623
theorem B4423085 : Blo 578813 4423085 := bstep (se 3 (by rfl) ⟨829328, by rfl⟩ : syracuseStep 4423085 = 1658657) B1658657
theorem B1179193 : Blo 578813 1179193 := bstep (se 2 (by rfl) ⟨442197, by rfl⟩ : syracuseStep 1179193 = 884395) B884395
theorem B982651 : Blo 578813 982651 := bstep (se 1 (by rfl) ⟨736988, by rfl⟩ : syracuseStep 982651 = 1473977) B1473977
theorem B2358919 : Blo 578813 2358919 := bstep (se 1 (by rfl) ⟨1769189, by rfl⟩ : syracuseStep 2358919 = 3538379) B3538379
theorem B1965707 : Blo 578813 1965707 := bstep (se 1 (by rfl) ⟨1474280, by rfl⟩ : syracuseStep 1965707 = 2948561) B2948561
theorem B622279 : Blo 578813 622279 := bstep (se 1 (by rfl) ⟨466709, by rfl⟩ : syracuseStep 622279 = 933419) B933419
theorem B1310651 : Blo 578813 1310651 := bstep (se 1 (by rfl) ⟨982988, by rfl⟩ : syracuseStep 1310651 = 1965977) B1965977
theorem B1966139 : Blo 578813 1966139 := bstep (se 1 (by rfl) ⟨1474604, by rfl⟩ : syracuseStep 1966139 = 2949209) B2949209
theorem B15728717 : Blo 578813 15728717 := bstep (se 3 (by rfl) ⟨2949134, by rfl⟩ : syracuseStep 15728717 = 5898269) B5898269
theorem B4948087 : Blo 578813 4948087 := bstep (se 1 (by rfl) ⟨3711065, by rfl⟩ : syracuseStep 4948087 = 7422131) B7422131
theorem B5112115 : Blo 578813 5112115 := bstep (se 1 (by rfl) ⟨3834086, by rfl⟩ : syracuseStep 5112115 = 7668173) B7668173
theorem B1966409 : Blo 578813 1966409 := bstep (se 2 (by rfl) ⟨737403, by rfl⟩ : syracuseStep 1966409 = 1474807) B1474807
theorem B983387 : Blo 578813 983387 := bstep (se 1 (by rfl) ⟨737540, by rfl⟩ : syracuseStep 983387 = 1475081) B1475081
theorem B1311083 : Blo 578813 1311083 := bstep (se 1 (by rfl) ⟨983312, by rfl⟩ : syracuseStep 1311083 = 1966625) B1966625
theorem B983407 : Blo 578813 983407 := bstep (se 1 (by rfl) ⟨737555, by rfl⟩ : syracuseStep 983407 = 1475111) B1475111
theorem B1311227 : Blo 578813 1311227 := bstep (se 1 (by rfl) ⟨983420, by rfl⟩ : syracuseStep 1311227 = 1966841) B1966841
theorem B1475243 : Blo 578813 1475243 := bstep (se 1 (by rfl) ⟨1106432, by rfl⟩ : syracuseStep 1475243 = 2212865) B2212865
theorem B4424543 : Blo 578813 4424543 := bstep (se 1 (by rfl) ⟨3318407, by rfl⟩ : syracuseStep 4424543 = 6636815) B6636815
theorem B2655389 : Blo 578813 2655389 := bstep (se 3 (by rfl) ⟨497885, by rfl⟩ : syracuseStep 2655389 = 995771) B995771
theorem B2950343 : Blo 578813 2950343 := bstep (se 1 (by rfl) ⟨2212757, by rfl⟩ : syracuseStep 2950343 = 4425515) B4425515
theorem B2786683 : Blo 578813 2786683 := bstep (se 1 (by rfl) ⟨2090012, by rfl⟩ : syracuseStep 2786683 = 4180025) B4180025
theorem B3016075 : Blo 578813 3016075 := bstep (se 1 (by rfl) ⟨2262056, by rfl⟩ : syracuseStep 3016075 = 4524113) B4524113
theorem B1574333 : Blo 578813 1574333 := bstep (se 3 (by rfl) ⟨295187, by rfl⟩ : syracuseStep 1574333 = 590375) B590375
theorem B28345949 : Blo 578813 28345949 := bstep (se 3 (by rfl) ⟨5314865, by rfl⟩ : syracuseStep 28345949 = 10629731) B10629731
theorem B2984359 : Blo 578813 2984359 := bstep (se 1 (by rfl) ⟨2238269, by rfl⟩ : syracuseStep 2984359 = 4476539) B4476539
theorem B11177027 : Blo 578813 11177027 := bstep (se 1 (by rfl) ⟨8382770, by rfl⟩ : syracuseStep 11177027 = 16765541) B16765541
theorem B3771679 : Blo 578813 3771679 := bstep (se 1 (by rfl) ⟨2828759, by rfl⟩ : syracuseStep 3771679 = 5657519) B5657519
theorem B51088765 : Blo 578813 51088765 := bstep (se 3 (by rfl) ⟨9579143, by rfl⟩ : syracuseStep 51088765 = 19158287) B19158287
theorem B2985497 : Blo 578813 2985497 := bstep (se 2 (by rfl) ⟨1119561, by rfl⟩ : syracuseStep 2985497 = 2239123) B2239123
theorem B3149725 : Blo 578813 3149725 := bstep (se 3 (by rfl) ⟨590573, by rfl⟩ : syracuseStep 3149725 = 1181147) B1181147
theorem B5738825 : Blo 578813 5738825 := bstep (se 2 (by rfl) ⟨2152059, by rfl⟩ : syracuseStep 5738825 = 4304119) B4304119
theorem B3314195 : Blo 578813 3314195 := bstep (se 1 (by rfl) ⟨2485646, by rfl⟩ : syracuseStep 3314195 = 4971293) B4971293
theorem B3052687 : Blo 578813 3052687 := bstep (se 1 (by rfl) ⟨2289515, by rfl⟩ : syracuseStep 3052687 = 4579031) B4579031
theorem B956681 : Blo 578813 956681 := bstep (se 2 (by rfl) ⟨358755, by rfl⟩ : syracuseStep 956681 = 717511) B717511
theorem B4954445 : Blo 578813 4954445 := bstep (se 3 (by rfl) ⟨928958, by rfl⟩ : syracuseStep 4954445 = 1857917) B1857917
theorem B3709273 : Blo 578813 3709273 := bstep (se 2 (by rfl) ⟨1390977, by rfl⟩ : syracuseStep 3709273 = 2781955) B2781955
theorem B1677779 : Blo 578813 1677779 := bstep (se 1 (by rfl) ⟨1258334, by rfl⟩ : syracuseStep 1677779 = 2516669) B2516669
theorem B99359227 : Blo 578813 99359227 := bstep (se 1 (by rfl) ⟨74519420, by rfl⟩ : syracuseStep 99359227 = 149038841) B149038841
theorem B4463237 : Blo 578813 4463237 := bstep (se 4 (by rfl) ⟨418428, by rfl⟩ : syracuseStep 4463237 = 836857) B836857
theorem B3316859 : Blo 578813 3316859 := bstep (se 1 (by rfl) ⟨2487644, by rfl⟩ : syracuseStep 3316859 = 4975289) B4975289
theorem B10067165 : Blo 578813 10067165 := bstep (se 3 (by rfl) ⟨1887593, by rfl⟩ : syracuseStep 10067165 = 3775187) B3775187
theorem B2202947 : Blo 578813 2202947 := bstep (se 1 (by rfl) ⟨1652210, by rfl⟩ : syracuseStep 2202947 = 3304421) B3304421
theorem B2202977 : Blo 578813 2202977 := bstep (se 2 (by rfl) ⟨826116, by rfl⟩ : syracuseStep 2202977 = 1652233) B1652233
theorem B2203433 : Blo 578813 2203433 := bstep (se 2 (by rfl) ⟨826287, by rfl⟩ : syracuseStep 2203433 = 1652575) B1652575
theorem B697055 : Blo 578813 697055 := bstep (se 1 (by rfl) ⟨522791, by rfl⟩ : syracuseStep 697055 = 1045583) B1045583
theorem B2204617 : Blo 578813 2204617 := bstep (se 2 (by rfl) ⟨826731, by rfl⟩ : syracuseStep 2204617 = 1653463) B1653463
theorem B2204921 : Blo 578813 2204921 := bstep (se 2 (by rfl) ⟨826845, by rfl⟩ : syracuseStep 2204921 = 1653691) B1653691
theorem B2860397 : Blo 578813 2860397 := bstep (se 3 (by rfl) ⟨536324, by rfl⟩ : syracuseStep 2860397 = 1072649) B1072649
theorem B2205089 : Blo 578813 2205089 := bstep (se 2 (by rfl) ⟨826908, by rfl⟩ : syracuseStep 2205089 = 1653817) B1653817
theorem B4400729 : Blo 578813 4400729 := bstep (se 2 (by rfl) ⟨1650273, by rfl⟩ : syracuseStep 4400729 = 3300547) B3300547
theorem B3188585 : Blo 578813 3188585 := bstep (se 2 (by rfl) ⟨1195719, by rfl⟩ : syracuseStep 3188585 = 2391439) B2391439
theorem B829705 : Blo 578813 829705 := bstep (se 2 (by rfl) ⟨311139, by rfl⟩ : syracuseStep 829705 = 622279) B622279
theorem B1255771 : Blo 578813 1255771 := bstep (se 1 (by rfl) ⟨941828, by rfl⟩ : syracuseStep 1255771 = 1883657) B1883657
theorem B8366915 : Blo 578813 8366915 := bstep (se 1 (by rfl) ⟨6275186, by rfl⟩ : syracuseStep 8366915 = 12550373) B12550373
theorem B15281167 : Blo 578813 15281167 := bstep (se 1 (by rfl) ⟨11460875, by rfl⟩ : syracuseStep 15281167 = 22921751) B22921751
theorem B5942443 : Blo 578813 5942443 := bstep (se 1 (by rfl) ⟨4456832, by rfl⟩ : syracuseStep 5942443 = 8913665) B8913665
theorem B3976411 : Blo 578813 3976411 := bstep (se 1 (by rfl) ⟨2982308, by rfl⟩ : syracuseStep 3976411 = 5964617) B5964617
theorem B2797139 : Blo 578813 2797139 := bstep (se 1 (by rfl) ⟨2097854, by rfl⟩ : syracuseStep 2797139 = 4195709) B4195709
theorem B8466119 : Blo 578813 8466119 := bstep (se 1 (by rfl) ⟨6349589, by rfl⟩ : syracuseStep 8466119 = 12699179) B12699179
theorem B7450379 : Blo 578813 7450379 := bstep (se 1 (by rfl) ⟨5587784, by rfl⟩ : syracuseStep 7450379 = 11175569) B11175569
theorem B1486721 : Blo 578813 1486721 := bstep (se 2 (by rfl) ⟨557520, by rfl⟩ : syracuseStep 1486721 = 1115041) B1115041
theorem B15052825 : Blo 578813 15052825 := bstep (se 2 (by rfl) ⟨5644809, by rfl⟩ : syracuseStep 15052825 = 11289619) B11289619
theorem B733531 : Blo 578813 733531 := bstep (se 1 (by rfl) ⟨550148, by rfl⟩ : syracuseStep 733531 = 1100297) B1100297
theorem B930791 : Blo 578813 930791 := bstep (se 1 (by rfl) ⟨698093, by rfl⟩ : syracuseStep 930791 = 1396187) B1396187
theorem B734503 : Blo 578813 734503 := bstep (se 1 (by rfl) ⟨550877, by rfl⟩ : syracuseStep 734503 = 1101755) B1101755
theorem B2045345 : Blo 578813 2045345 := bstep (se 2 (by rfl) ⟨767004, by rfl⟩ : syracuseStep 2045345 = 1534009) B1534009
theorem B734827 : Blo 578813 734827 := bstep (se 1 (by rfl) ⟨551120, by rfl⟩ : syracuseStep 734827 = 1102241) B1102241
theorem B4962167 : Blo 578813 4962167 := bstep (se 1 (by rfl) ⟨3721625, by rfl⟩ : syracuseStep 4962167 = 7443251) B7443251
theorem B4962637 : Blo 578813 4962637 := bstep (se 3 (by rfl) ⟨930494, by rfl⟩ : syracuseStep 4962637 = 1860989) B1860989
theorem B2931389 : Blo 578813 2931389 := bstep (se 3 (by rfl) ⟨549635, by rfl⟩ : syracuseStep 2931389 = 1099271) B1099271
theorem B6273935 : Blo 578813 6273935 := bstep (se 1 (by rfl) ⟨4705451, by rfl⟩ : syracuseStep 6273935 = 9410903) B9410903
theorem B6110437 : Blo 578813 6110437 := bstep (se 4 (by rfl) ⟨572853, by rfl⟩ : syracuseStep 6110437 = 1145707) B1145707
theorem B736543 : Blo 578813 736543 := bstep (se 1 (by rfl) ⟨552407, by rfl⟩ : syracuseStep 736543 = 1104815) B1104815
theorem B2211209 : Blo 578813 2211209 := bstep (se 2 (by rfl) ⟨829203, by rfl⟩ : syracuseStep 2211209 = 1658407) B1658407
theorem B5291513 : Blo 578813 5291513 := bstep (se 2 (by rfl) ⟨1984317, by rfl⟩ : syracuseStep 5291513 = 3968635) B3968635
theorem B6471191 : Blo 578813 6471191 := bstep (se 1 (by rfl) ⟨4853393, by rfl⟩ : syracuseStep 6471191 = 9706787) B9706787
theorem B4407047 : Blo 578813 4407047 := bstep (se 1 (by rfl) ⟨3305285, by rfl⟩ : syracuseStep 4407047 = 6610571) B6610571
theorem B10076237 : Blo 578813 10076237 := bstep (se 3 (by rfl) ⟨1889294, by rfl⟩ : syracuseStep 10076237 = 3778589) B3778589
theorem B868457 : Blo 578813 868457 := bstep (se 2 (by rfl) ⟨325671, by rfl⟩ : syracuseStep 868457 = 651343) B651343
theorem B868775 : Blo 578813 868775 := bstep (se 1 (by rfl) ⟨651581, by rfl⟩ : syracuseStep 868775 = 1303163) B1303163
theorem B868859 : Blo 578813 868859 := bstep (se 1 (by rfl) ⟨651644, by rfl⟩ : syracuseStep 868859 = 1303289) B1303289
theorem B868985 : Blo 578813 868985 := bstep (se 2 (by rfl) ⟨325869, by rfl⟩ : syracuseStep 868985 = 651739) B651739
theorem B869039 : Blo 578813 869039 := bstep (se 1 (by rfl) ⟨651779, by rfl⟩ : syracuseStep 869039 = 1303559) B1303559
theorem B869087 : Blo 578813 869087 := bstep (se 1 (by rfl) ⟨651815, by rfl⟩ : syracuseStep 869087 = 1303631) B1303631
theorem B869351 : Blo 578813 869351 := bstep (se 1 (by rfl) ⟨652013, by rfl⟩ : syracuseStep 869351 = 1304027) B1304027
theorem B869609 : Blo 578813 869609 := bstep (se 2 (by rfl) ⟨326103, by rfl⟩ : syracuseStep 869609 = 652207) B652207
theorem B10601705 : Blo 578813 10601705 := bstep (se 2 (by rfl) ⟨3975639, by rfl⟩ : syracuseStep 10601705 = 7951279) B7951279
theorem B869663 : Blo 578813 869663 := bstep (se 1 (by rfl) ⟨652247, by rfl⟩ : syracuseStep 869663 = 1304495) B1304495
theorem B869831 : Blo 578813 869831 := bstep (se 1 (by rfl) ⟨652373, by rfl⟩ : syracuseStep 869831 = 1304747) B1304747
theorem B2934305 : Blo 578813 2934305 := bstep (se 2 (by rfl) ⟨1100364, by rfl⟩ : syracuseStep 2934305 = 2200729) B2200729
theorem B2475805 : Blo 578813 2475805 := bstep (se 3 (by rfl) ⟨464213, by rfl⟩ : syracuseStep 2475805 = 928427) B928427
theorem B870185 : Blo 578813 870185 := bstep (se 2 (by rfl) ⟨326319, by rfl⟩ : syracuseStep 870185 = 652639) B652639
theorem B12732203 : Blo 578813 12732203 := bstep (se 1 (by rfl) ⟨9549152, by rfl⟩ : syracuseStep 12732203 = 19098305) B19098305
theorem B870191 : Blo 578813 870191 := bstep (se 1 (by rfl) ⟨652643, by rfl⟩ : syracuseStep 870191 = 1305287) B1305287
theorem B1099727 : Blo 578813 1099727 := bstep (se 1 (by rfl) ⟨824795, by rfl⟩ : syracuseStep 1099727 = 1649591) B1649591
theorem B870665 : Blo 578813 870665 := bstep (se 2 (by rfl) ⟨326499, by rfl⟩ : syracuseStep 870665 = 652999) B652999
theorem B870767 : Blo 578813 870767 := bstep (se 1 (by rfl) ⟨653075, by rfl⟩ : syracuseStep 870767 = 1306151) B1306151
theorem B1657199 : Blo 578813 1657199 := bstep (se 1 (by rfl) ⟨1242899, by rfl⟩ : syracuseStep 1657199 = 2485799) B2485799
theorem B1100243 : Blo 578813 1100243 := bstep (se 1 (by rfl) ⟨825182, by rfl⟩ : syracuseStep 1100243 = 1650365) B1650365
theorem B870983 : Blo 578813 870983 := bstep (se 1 (by rfl) ⟨653237, by rfl⟩ : syracuseStep 870983 = 1306475) B1306475
theorem B1100395 : Blo 578813 1100395 := bstep (se 1 (by rfl) ⟨825296, by rfl⟩ : syracuseStep 1100395 = 1650593) B1650593
theorem B871019 : Blo 578813 871019 := bstep (se 1 (by rfl) ⟨653264, by rfl⟩ : syracuseStep 871019 = 1306529) B1306529
theorem B1100623 : Blo 578813 1100623 := bstep (se 1 (by rfl) ⟨825467, by rfl⟩ : syracuseStep 1100623 = 1650935) B1650935
theorem B871247 : Blo 578813 871247 := bstep (se 1 (by rfl) ⟨653435, by rfl⟩ : syracuseStep 871247 = 1306871) B1306871
theorem B1100699 : Blo 578813 1100699 := bstep (se 1 (by rfl) ⟨825524, by rfl⟩ : syracuseStep 1100699 = 1651049) B1651049
theorem B4410449 : Blo 578813 4410449 := bstep (se 2 (by rfl) ⟨1653918, by rfl⟩ : syracuseStep 4410449 = 3307837) B3307837
theorem B871643 : Blo 578813 871643 := bstep (se 1 (by rfl) ⟨653732, by rfl⟩ : syracuseStep 871643 = 1307465) B1307465
theorem B10046711 : Blo 578813 10046711 := bstep (se 1 (by rfl) ⟨7535033, by rfl⟩ : syracuseStep 10046711 = 15070067) B15070067
theorem B871817 : Blo 578813 871817 := bstep (se 2 (by rfl) ⟨326931, by rfl⟩ : syracuseStep 871817 = 653863) B653863
theorem B3296699 : Blo 578813 3296699 := bstep (se 1 (by rfl) ⟨2472524, by rfl⟩ : syracuseStep 3296699 = 4945049) B4945049
theorem B2477803 : Blo 578813 2477803 := bstep (se 1 (by rfl) ⟨1858352, by rfl⟩ : syracuseStep 2477803 = 3716705) B3716705
theorem B872171 : Blo 578813 872171 := bstep (se 1 (by rfl) ⟨654128, by rfl⟩ : syracuseStep 872171 = 1308257) B1308257
theorem B1658681 : Blo 578813 1658681 := bstep (se 2 (by rfl) ⟨622005, by rfl⟩ : syracuseStep 1658681 = 1244011) B1244011
theorem B1953665 : Blo 578813 1953665 := bstep (se 2 (by rfl) ⟨732624, by rfl⟩ : syracuseStep 1953665 = 1465249) B1465249
theorem B872399 : Blo 578813 872399 := bstep (se 1 (by rfl) ⟨654299, by rfl⟩ : syracuseStep 872399 = 1308599) B1308599
theorem B872795 : Blo 578813 872795 := bstep (se 1 (by rfl) ⟨654596, by rfl⟩ : syracuseStep 872795 = 1309193) B1309193
theorem B873023 : Blo 578813 873023 := bstep (se 1 (by rfl) ⟨654767, by rfl⟩ : syracuseStep 873023 = 1309535) B1309535
theorem B1954475 : Blo 578813 1954475 := bstep (se 1 (by rfl) ⟨1465856, by rfl⟩ : syracuseStep 1954475 = 2931713) B2931713
theorem B873143 : Blo 578813 873143 := bstep (se 1 (by rfl) ⟨654857, by rfl⟩ : syracuseStep 873143 = 1309715) B1309715
theorem B3298157 : Blo 578813 3298157 := bstep (se 3 (by rfl) ⟨618404, by rfl⟩ : syracuseStep 3298157 = 1236809) B1236809
theorem B873371 : Blo 578813 873371 := bstep (se 1 (by rfl) ⟨655028, by rfl⟩ : syracuseStep 873371 = 1310057) B1310057
theorem B1955015 : Blo 578813 1955015 := bstep (se 1 (by rfl) ⟨1466261, by rfl⟩ : syracuseStep 1955015 = 2932523) B2932523
theorem B578847 : Blo 578813 578847 := bstep (se 1 (by rfl) ⟨434135, by rfl⟩ : syracuseStep 578847 = 868271) B868271
theorem B873767 : Blo 578813 873767 := bstep (se 1 (by rfl) ⟨655325, by rfl⟩ : syracuseStep 873767 = 1310651) B1310651
theorem B578907 : Blo 578813 578907 := bstep (se 1 (by rfl) ⟨434180, by rfl⟩ : syracuseStep 578907 = 868361) B868361
theorem B3986783 : Blo 578813 3986783 := bstep (se 1 (by rfl) ⟨2990087, by rfl⟩ : syracuseStep 3986783 = 5980175) B5980175
theorem B578927 : Blo 578813 578927 := bstep (se 1 (by rfl) ⟨434195, by rfl⟩ : syracuseStep 578927 = 868391) B868391
theorem B873851 : Blo 578813 873851 := bstep (se 1 (by rfl) ⟨655388, by rfl⟩ : syracuseStep 873851 = 1310777) B1310777
theorem B578983 : Blo 578813 578983 := bstep (se 1 (by rfl) ⟨434237, by rfl⟩ : syracuseStep 578983 = 868475) B868475
theorem B873977 : Blo 578813 873977 := bstep (se 2 (by rfl) ⟨327741, by rfl⟩ : syracuseStep 873977 = 655483) B655483
theorem B579067 : Blo 578813 579067 := bstep (se 1 (by rfl) ⟨434300, by rfl⟩ : syracuseStep 579067 = 868601) B868601
theorem B579135 : Blo 578813 579135 := bstep (se 1 (by rfl) ⟨434351, by rfl⟩ : syracuseStep 579135 = 868703) B868703
theorem B579143 : Blo 578813 579143 := bstep (se 1 (by rfl) ⟨434357, by rfl⟩ : syracuseStep 579143 = 868715) B868715
theorem B874079 : Blo 578813 874079 := bstep (se 1 (by rfl) ⟨655559, by rfl⟩ : syracuseStep 874079 = 1311119) B1311119
theorem B579295 : Blo 578813 579295 := bstep (se 1 (by rfl) ⟨434471, by rfl⟩ : syracuseStep 579295 = 868943) B868943
theorem B35739407 : Blo 578813 35739407 := bstep (se 1 (by rfl) ⟨26804555, by rfl⟩ : syracuseStep 35739407 = 53609111) B53609111
theorem B579375 : Blo 578813 579375 := bstep (se 1 (by rfl) ⟨434531, by rfl⟩ : syracuseStep 579375 = 869063) B869063
theorem B2938679 : Blo 578813 2938679 := bstep (se 1 (by rfl) ⟨2204009, by rfl⟩ : syracuseStep 2938679 = 4408019) B4408019
theorem B579483 : Blo 578813 579483 := bstep (se 1 (by rfl) ⟨434612, by rfl⟩ : syracuseStep 579483 = 869225) B869225
theorem B579535 : Blo 578813 579535 := bstep (se 1 (by rfl) ⟨434651, by rfl⟩ : syracuseStep 579535 = 869303) B869303
theorem B579559 : Blo 578813 579559 := bstep (se 1 (by rfl) ⟨434669, by rfl⟩ : syracuseStep 579559 = 869339) B869339
theorem B2939165 : Blo 578813 2939165 := bstep (se 3 (by rfl) ⟨551093, by rfl⟩ : syracuseStep 2939165 = 1102187) B1102187
theorem B579871 : Blo 578813 579871 := bstep (se 1 (by rfl) ⟨434903, by rfl⟩ : syracuseStep 579871 = 869807) B869807
theorem B579931 : Blo 578813 579931 := bstep (se 1 (by rfl) ⟨434948, by rfl⟩ : syracuseStep 579931 = 869897) B869897
theorem B579951 : Blo 578813 579951 := bstep (se 1 (by rfl) ⟨434963, by rfl⟩ : syracuseStep 579951 = 869927) B869927
theorem B11917721 : Blo 578813 11917721 := bstep (se 2 (by rfl) ⟨4469145, by rfl⟩ : syracuseStep 11917721 = 8938291) B8938291
theorem B580007 : Blo 578813 580007 := bstep (se 1 (by rfl) ⟨435005, by rfl⟩ : syracuseStep 580007 = 870011) B870011
theorem B580091 : Blo 578813 580091 := bstep (se 1 (by rfl) ⟨435068, by rfl⟩ : syracuseStep 580091 = 870137) B870137
theorem B580159 : Blo 578813 580159 := bstep (se 1 (by rfl) ⟨435119, by rfl⟩ : syracuseStep 580159 = 870239) B870239
theorem B580167 : Blo 578813 580167 := bstep (se 1 (by rfl) ⟨435125, by rfl⟩ : syracuseStep 580167 = 870251) B870251
theorem B1956527 : Blo 578813 1956527 := bstep (se 1 (by rfl) ⟨1467395, by rfl⟩ : syracuseStep 1956527 = 2934791) B2934791
theorem B580319 : Blo 578813 580319 := bstep (se 1 (by rfl) ⟨435239, by rfl⟩ : syracuseStep 580319 = 870479) B870479
theorem B580399 : Blo 578813 580399 := bstep (se 1 (by rfl) ⟨435299, by rfl⟩ : syracuseStep 580399 = 870599) B870599
theorem B580507 : Blo 578813 580507 := bstep (se 1 (by rfl) ⟨435380, by rfl⟩ : syracuseStep 580507 = 870761) B870761
theorem B2087851 : Blo 578813 2087851 := bstep (se 1 (by rfl) ⟨1565888, by rfl⟩ : syracuseStep 2087851 = 3131777) B3131777
theorem B580559 : Blo 578813 580559 := bstep (se 1 (by rfl) ⟨435419, by rfl⟩ : syracuseStep 580559 = 870839) B870839
theorem B580583 : Blo 578813 580583 := bstep (se 1 (by rfl) ⟨435437, by rfl⟩ : syracuseStep 580583 = 870875) B870875
theorem B1956851 : Blo 578813 1956851 := bstep (se 1 (by rfl) ⟨1467638, by rfl⟩ : syracuseStep 1956851 = 2935277) B2935277
theorem B183196853 : Blo 578813 183196853 := bstep (se 5 (by rfl) ⟨8587352, by rfl⟩ : syracuseStep 183196853 = 17174705) B17174705
theorem B580895 : Blo 578813 580895 := bstep (se 1 (by rfl) ⟨435671, by rfl⟩ : syracuseStep 580895 = 871343) B871343
theorem B580955 : Blo 578813 580955 := bstep (se 1 (by rfl) ⟨435716, by rfl⟩ : syracuseStep 580955 = 871433) B871433
theorem B580975 : Blo 578813 580975 := bstep (se 1 (by rfl) ⟨435731, by rfl⟩ : syracuseStep 580975 = 871463) B871463
theorem B4971941 : Blo 578813 4971941 := bstep (se 4 (by rfl) ⟨466119, by rfl⟩ : syracuseStep 4971941 = 932239) B932239
theorem B581031 : Blo 578813 581031 := bstep (se 1 (by rfl) ⟨435773, by rfl⟩ : syracuseStep 581031 = 871547) B871547
theorem B581115 : Blo 578813 581115 := bstep (se 1 (by rfl) ⟨435836, by rfl⟩ : syracuseStep 581115 = 871673) B871673
theorem B1957391 : Blo 578813 1957391 := bstep (se 1 (by rfl) ⟨1468043, by rfl⟩ : syracuseStep 1957391 = 2936087) B2936087
theorem B581183 : Blo 578813 581183 := bstep (se 1 (by rfl) ⟨435887, by rfl⟩ : syracuseStep 581183 = 871775) B871775
theorem B581191 : Blo 578813 581191 := bstep (se 1 (by rfl) ⟨435893, by rfl⟩ : syracuseStep 581191 = 871787) B871787
theorem B581343 : Blo 578813 581343 := bstep (se 1 (by rfl) ⟨436007, by rfl⟩ : syracuseStep 581343 = 872015) B872015
theorem B1105643 : Blo 578813 1105643 := bstep (se 1 (by rfl) ⟨829232, by rfl⟩ : syracuseStep 1105643 = 1658465) B1658465
theorem B581423 : Blo 578813 581423 := bstep (se 1 (by rfl) ⟨436067, by rfl⟩ : syracuseStep 581423 = 872135) B872135
theorem B581531 : Blo 578813 581531 := bstep (se 1 (by rfl) ⟨436148, by rfl⟩ : syracuseStep 581531 = 872297) B872297
theorem B6283183 : Blo 578813 6283183 := bstep (se 1 (by rfl) ⟨4712387, by rfl⟩ : syracuseStep 6283183 = 9424775) B9424775
theorem B1302479 : Blo 578813 1302479 := bstep (se 1 (by rfl) ⟨976859, by rfl⟩ : syracuseStep 1302479 = 1953719) B1953719
theorem B581583 : Blo 578813 581583 := bstep (se 1 (by rfl) ⟨436187, by rfl⟩ : syracuseStep 581583 = 872375) B872375
theorem B581607 : Blo 578813 581607 := bstep (se 1 (by rfl) ⟨436205, by rfl⟩ : syracuseStep 581607 = 872411) B872411
theorem B2482177 : Blo 578813 2482177 := bstep (se 2 (by rfl) ⟨930816, by rfl⟩ : syracuseStep 2482177 = 1861633) B1861633
theorem B2940947 : Blo 578813 2940947 := bstep (se 1 (by rfl) ⟨2205710, by rfl⟩ : syracuseStep 2940947 = 4411421) B4411421
theorem B7561349 : Blo 578813 7561349 := bstep (se 4 (by rfl) ⟨708876, by rfl⟩ : syracuseStep 7561349 = 1417753) B1417753
theorem B581919 : Blo 578813 581919 := bstep (se 1 (by rfl) ⟨436439, by rfl⟩ : syracuseStep 581919 = 872879) B872879
theorem B1302857 : Blo 578813 1302857 := bstep (se 2 (by rfl) ⟨488571, by rfl⟩ : syracuseStep 1302857 = 977143) B977143
theorem B1302875 : Blo 578813 1302875 := bstep (se 1 (by rfl) ⟨977156, by rfl⟩ : syracuseStep 1302875 = 1954313) B1954313
theorem B581979 : Blo 578813 581979 := bstep (se 1 (by rfl) ⟨436484, by rfl⟩ : syracuseStep 581979 = 872969) B872969
theorem B581999 : Blo 578813 581999 := bstep (se 1 (by rfl) ⟨436499, by rfl⟩ : syracuseStep 581999 = 872999) B872999
theorem B582055 : Blo 578813 582055 := bstep (se 1 (by rfl) ⟨436541, by rfl⟩ : syracuseStep 582055 = 873083) B873083
theorem B1466849 : Blo 578813 1466849 := bstep (se 2 (by rfl) ⟨550068, by rfl⟩ : syracuseStep 1466849 = 1100137) B1100137
theorem B582139 : Blo 578813 582139 := bstep (se 1 (by rfl) ⟨436604, by rfl⟩ : syracuseStep 582139 = 873209) B873209
theorem B582207 : Blo 578813 582207 := bstep (se 1 (by rfl) ⟨436655, by rfl⟩ : syracuseStep 582207 = 873311) B873311
theorem B1958471 : Blo 578813 1958471 := bstep (se 1 (by rfl) ⟨1468853, by rfl⟩ : syracuseStep 1958471 = 2937707) B2937707
theorem B582215 : Blo 578813 582215 := bstep (se 1 (by rfl) ⟨436661, by rfl⟩ : syracuseStep 582215 = 873323) B873323
theorem B582367 : Blo 578813 582367 := bstep (se 1 (by rfl) ⟨436775, by rfl⟩ : syracuseStep 582367 = 873551) B873551
theorem B582447 : Blo 578813 582447 := bstep (se 1 (by rfl) ⟨436835, by rfl⟩ : syracuseStep 582447 = 873671) B873671
theorem B1303451 : Blo 578813 1303451 := bstep (se 1 (by rfl) ⟨977588, by rfl⟩ : syracuseStep 1303451 = 1955177) B1955177
theorem B582555 : Blo 578813 582555 := bstep (se 1 (by rfl) ⟨436916, by rfl⟩ : syracuseStep 582555 = 873833) B873833
theorem B51045299 : Blo 578813 51045299 := bstep (se 1 (by rfl) ⟨38283974, by rfl⟩ : syracuseStep 51045299 = 76567949) B76567949
theorem B582607 : Blo 578813 582607 := bstep (se 1 (by rfl) ⟨436955, by rfl⟩ : syracuseStep 582607 = 873911) B873911
theorem B1237979 : Blo 578813 1237979 := bstep (se 1 (by rfl) ⟨928484, by rfl⟩ : syracuseStep 1237979 = 1856969) B1856969
theorem B1467355 : Blo 578813 1467355 := bstep (se 1 (by rfl) ⟨1100516, by rfl⟩ : syracuseStep 1467355 = 2201033) B2201033
theorem B5596123 : Blo 578813 5596123 := bstep (se 1 (by rfl) ⟨4197092, by rfl⟩ : syracuseStep 5596123 = 8394185) B8394185
theorem B1860583 : Blo 578813 1860583 := bstep (se 1 (by rfl) ⟨1395437, by rfl⟩ : syracuseStep 1860583 = 2790875) B2790875
theorem B582631 : Blo 578813 582631 := bstep (se 1 (by rfl) ⟨436973, by rfl⟩ : syracuseStep 582631 = 873947) B873947
theorem B1958903 : Blo 578813 1958903 := bstep (se 1 (by rfl) ⟨1469177, by rfl⟩ : syracuseStep 1958903 = 2938355) B2938355
theorem B1303649 : Blo 578813 1303649 := bstep (se 2 (by rfl) ⟨488868, by rfl⟩ : syracuseStep 1303649 = 977737) B977737
theorem B1467679 : Blo 578813 1467679 := bstep (se 1 (by rfl) ⟨1100759, by rfl⟩ : syracuseStep 1467679 = 2201519) B2201519
theorem B1303847 : Blo 578813 1303847 := bstep (se 1 (by rfl) ⟨977885, by rfl⟩ : syracuseStep 1303847 = 1955771) B1955771
theorem B1304225 : Blo 578813 1304225 := bstep (se 2 (by rfl) ⟨489084, by rfl⟩ : syracuseStep 1304225 = 978169) B978169
theorem B9889613 : Blo 578813 9889613 := bstep (se 3 (by rfl) ⟨1854302, by rfl⟩ : syracuseStep 9889613 = 3708605) B3708605
theorem B1959767 : Blo 578813 1959767 := bstep (se 1 (by rfl) ⟨1469825, by rfl⟩ : syracuseStep 1959767 = 2939651) B2939651
theorem B1304585 : Blo 578813 1304585 := bstep (se 2 (by rfl) ⟨489219, by rfl⟩ : syracuseStep 1304585 = 978439) B978439
theorem B23816429 : Blo 578813 23816429 := bstep (se 3 (by rfl) ⟨4465580, by rfl⟩ : syracuseStep 23816429 = 8931161) B8931161
theorem B1468763 : Blo 578813 1468763 := bstep (se 1 (by rfl) ⟨1101572, by rfl⟩ : syracuseStep 1468763 = 2203145) B2203145
theorem B1304999 : Blo 578813 1304999 := bstep (se 1 (by rfl) ⟨978749, by rfl⟩ : syracuseStep 1304999 = 1957499) B1957499
theorem B1305107 : Blo 578813 1305107 := bstep (se 1 (by rfl) ⟨978830, by rfl⟩ : syracuseStep 1305107 = 1957661) B1957661
theorem B1305161 : Blo 578813 1305161 := bstep (se 2 (by rfl) ⟨489435, by rfl⟩ : syracuseStep 1305161 = 978871) B978871
theorem B2484911 : Blo 578813 2484911 := bstep (se 1 (by rfl) ⟨1863683, by rfl⟩ : syracuseStep 2484911 = 3727367) B3727367
theorem B4188995 : Blo 578813 4188995 := bstep (se 1 (by rfl) ⟨3141746, by rfl⟩ : syracuseStep 4188995 = 6283493) B6283493
theorem B3140471 : Blo 578813 3140471 := bstep (se 1 (by rfl) ⟨2355353, by rfl⟩ : syracuseStep 3140471 = 4710707) B4710707
theorem B2943863 : Blo 578813 2943863 := bstep (se 1 (by rfl) ⟨2207897, by rfl⟩ : syracuseStep 2943863 = 4415795) B4415795
theorem B1960847 : Blo 578813 1960847 := bstep (se 1 (by rfl) ⟨1470635, by rfl⟩ : syracuseStep 1960847 = 2941271) B2941271
theorem B1305575 : Blo 578813 1305575 := bstep (se 1 (by rfl) ⟨979181, by rfl⟩ : syracuseStep 1305575 = 1958363) B1958363
theorem B2092319 : Blo 578813 2092319 := bstep (se 1 (by rfl) ⟨1569239, by rfl⟩ : syracuseStep 2092319 = 3138479) B3138479
theorem B1469735 : Blo 578813 1469735 := bstep (se 1 (by rfl) ⟨1102301, by rfl⟩ : syracuseStep 1469735 = 2204603) B2204603
theorem B1305953 : Blo 578813 1305953 := bstep (se 2 (by rfl) ⟨489732, by rfl⟩ : syracuseStep 1305953 = 979465) B979465
theorem B1306043 : Blo 578813 1306043 := bstep (se 1 (by rfl) ⟨979532, by rfl⟩ : syracuseStep 1306043 = 1959065) B1959065
theorem B367586819 : Blo 578813 367586819 := bstep (se 1 (by rfl) ⟨275690114, by rfl⟩ : syracuseStep 367586819 = 551380229) B551380229
theorem B1306169 : Blo 578813 1306169 := bstep (se 2 (by rfl) ⟨489813, by rfl⟩ : syracuseStep 1306169 = 979627) B979627
theorem B978527 : Blo 578813 978527 := bstep (se 1 (by rfl) ⟨733895, by rfl⟩ : syracuseStep 978527 = 1467791) B1467791
theorem B2944673 : Blo 578813 2944673 := bstep (se 2 (by rfl) ⟨1104252, by rfl⟩ : syracuseStep 2944673 = 2208505) B2208505
theorem B42430169 : Blo 578813 42430169 := bstep (se 2 (by rfl) ⟨15911313, by rfl⟩ : syracuseStep 42430169 = 31822627) B31822627
theorem B3305195 : Blo 578813 3305195 := bstep (se 1 (by rfl) ⟨2478896, by rfl⟩ : syracuseStep 3305195 = 4957793) B4957793
theorem B978743 : Blo 578813 978743 := bstep (se 1 (by rfl) ⟨734057, by rfl⟩ : syracuseStep 978743 = 1468115) B1468115
theorem B1962089 : Blo 578813 1962089 := bstep (se 2 (by rfl) ⟨735783, by rfl⟩ : syracuseStep 1962089 = 1471567) B1471567
theorem B2650283 : Blo 578813 2650283 := bstep (se 1 (by rfl) ⟨1987712, by rfl⟩ : syracuseStep 2650283 = 3975425) B3975425
theorem B6353099 : Blo 578813 6353099 := bstep (se 1 (by rfl) ⟨4764824, by rfl⟩ : syracuseStep 6353099 = 9529649) B9529649
theorem B1306835 : Blo 578813 1306835 := bstep (se 1 (by rfl) ⟨980126, by rfl⟩ : syracuseStep 1306835 = 1960253) B1960253
theorem B2486483 : Blo 578813 2486483 := bstep (se 1 (by rfl) ⟨1864862, by rfl⟩ : syracuseStep 2486483 = 3729725) B3729725
theorem B1306889 : Blo 578813 1306889 := bstep (se 2 (by rfl) ⟨490083, by rfl⟩ : syracuseStep 1306889 = 980167) B980167
theorem B651559 : Blo 578813 651559 := bstep (se 1 (by rfl) ⟨488669, by rfl⟩ : syracuseStep 651559 = 977339) B977339
theorem B1864043 : Blo 578813 1864043 := bstep (se 1 (by rfl) ⟨1398032, by rfl⟩ : syracuseStep 1864043 = 2796065) B2796065
theorem B651631 : Blo 578813 651631 := bstep (se 1 (by rfl) ⟨488723, by rfl⟩ : syracuseStep 651631 = 977447) B977447
theorem B1307105 : Blo 578813 1307105 := bstep (se 2 (by rfl) ⟨490164, by rfl⟩ : syracuseStep 1307105 = 980329) B980329
theorem B1765907 : Blo 578813 1765907 := bstep (se 1 (by rfl) ⟨1324430, by rfl⟩ : syracuseStep 1765907 = 2648861) B2648861
theorem B10711601 : Blo 578813 10711601 := bstep (se 2 (by rfl) ⟨4016850, by rfl⟩ : syracuseStep 10711601 = 8033701) B8033701
theorem B979519 : Blo 578813 979519 := bstep (se 1 (by rfl) ⟨734639, by rfl⟩ : syracuseStep 979519 = 1469279) B1469279
theorem B651847 : Blo 578813 651847 := bstep (se 1 (by rfl) ⟨488885, by rfl⟩ : syracuseStep 651847 = 977771) B977771
theorem B2716343 : Blo 578813 2716343 := bstep (se 1 (by rfl) ⟨2037257, by rfl⟩ : syracuseStep 2716343 = 4074515) B4074515
theorem B1471223 : Blo 578813 1471223 := bstep (se 1 (by rfl) ⟨1103417, by rfl⟩ : syracuseStep 1471223 = 2206835) B2206835
theorem B1307411 : Blo 578813 1307411 := bstep (se 1 (by rfl) ⟨980558, by rfl⟩ : syracuseStep 1307411 = 1961117) B1961117
theorem B10580843 : Blo 578813 10580843 := bstep (se 1 (by rfl) ⟨7935632, by rfl⟩ : syracuseStep 10580843 = 15871265) B15871265
theorem B1242011 : Blo 578813 1242011 := bstep (se 1 (by rfl) ⟨931508, by rfl⟩ : syracuseStep 1242011 = 1863017) B1863017
theorem B3732389 : Blo 578813 3732389 := bstep (se 4 (by rfl) ⟨349911, by rfl⟩ : syracuseStep 3732389 = 699823) B699823
theorem B1962953 : Blo 578813 1962953 := bstep (se 2 (by rfl) ⟨736107, by rfl⟩ : syracuseStep 1962953 = 1472215) B1472215
theorem B3142631 : Blo 578813 3142631 := bstep (se 1 (by rfl) ⟨2356973, by rfl⟩ : syracuseStep 3142631 = 4713947) B4713947
theorem B2487287 : Blo 578813 2487287 := bstep (se 1 (by rfl) ⟨1865465, by rfl⟩ : syracuseStep 2487287 = 3730931) B3730931
theorem B1242209 : Blo 578813 1242209 := bstep (se 2 (by rfl) ⟨465828, by rfl⟩ : syracuseStep 1242209 = 931657) B931657
theorem B1307771 : Blo 578813 1307771 := bstep (se 1 (by rfl) ⟨980828, by rfl⟩ : syracuseStep 1307771 = 1961657) B1961657
theorem B2487439 : Blo 578813 2487439 := bstep (se 1 (by rfl) ⟨1865579, by rfl⟩ : syracuseStep 2487439 = 3731159) B3731159
theorem B3306653 : Blo 578813 3306653 := bstep (se 3 (by rfl) ⟨619997, by rfl⟩ : syracuseStep 3306653 = 1239995) B1239995
theorem B1963223 : Blo 578813 1963223 := bstep (se 1 (by rfl) ⟨1472417, by rfl⟩ : syracuseStep 1963223 = 2944835) B2944835
theorem B980201 : Blo 578813 980201 := bstep (se 2 (by rfl) ⟨367575, by rfl⟩ : syracuseStep 980201 = 735151) B735151
theorem B2782457 : Blo 578813 2782457 := bstep (se 2 (by rfl) ⟨1043421, by rfl⟩ : syracuseStep 2782457 = 2086843) B2086843
theorem B1307897 : Blo 578813 1307897 := bstep (se 2 (by rfl) ⟨490461, by rfl⟩ : syracuseStep 1307897 = 980923) B980923
theorem B980255 : Blo 578813 980255 := bstep (se 1 (by rfl) ⟨735191, by rfl⟩ : syracuseStep 980255 = 1470383) B1470383
theorem B1471841 : Blo 578813 1471841 := bstep (se 2 (by rfl) ⟨551940, by rfl⟩ : syracuseStep 1471841 = 1103881) B1103881
theorem B1308041 : Blo 578813 1308041 := bstep (se 2 (by rfl) ⟨490515, by rfl⟩ : syracuseStep 1308041 = 981031) B981031
theorem B652711 : Blo 578813 652711 := bstep (se 1 (by rfl) ⟨489533, by rfl⟩ : syracuseStep 652711 = 979067) B979067
theorem B1308167 : Blo 578813 1308167 := bstep (se 1 (by rfl) ⟨981125, by rfl⟩ : syracuseStep 1308167 = 1962251) B1962251
theorem B2946617 : Blo 578813 2946617 := bstep (se 2 (by rfl) ⟨1104981, by rfl⟩ : syracuseStep 2946617 = 2209963) B2209963
theorem B1308347 : Blo 578813 1308347 := bstep (se 1 (by rfl) ⟨981260, by rfl⟩ : syracuseStep 1308347 = 1962521) B1962521
theorem B1308473 : Blo 578813 1308473 := bstep (se 2 (by rfl) ⟨490677, by rfl⟩ : syracuseStep 1308473 = 981355) B981355
theorem B653287 : Blo 578813 653287 := bstep (se 1 (by rfl) ⟨489965, by rfl⟩ : syracuseStep 653287 = 979931) B979931
theorem B9893987 : Blo 578813 9893987 := bstep (se 1 (by rfl) ⟨7420490, by rfl⟩ : syracuseStep 9893987 = 14840981) B14840981
theorem B3307655 : Blo 578813 3307655 := bstep (se 1 (by rfl) ⟨2480741, by rfl⟩ : syracuseStep 3307655 = 4961483) B4961483
theorem B3963161 : Blo 578813 3963161 := bstep (se 2 (by rfl) ⟨1486185, by rfl⟩ : syracuseStep 3963161 = 2972371) B2972371
theorem B620831 : Blo 578813 620831 := bstep (se 1 (by rfl) ⟨465623, by rfl⟩ : syracuseStep 620831 = 931247) B931247
theorem B1309103 : Blo 578813 1309103 := bstep (se 1 (by rfl) ⟨981827, by rfl⟩ : syracuseStep 1309103 = 1963655) B1963655
theorem B1505719 : Blo 578813 1505719 := bstep (se 1 (by rfl) ⟨1129289, by rfl⟩ : syracuseStep 1505719 = 2258579) B2258579
theorem B1309139 : Blo 578813 1309139 := bstep (se 1 (by rfl) ⟨981854, by rfl⟩ : syracuseStep 1309139 = 1963709) B1963709
theorem B1309247 : Blo 578813 1309247 := bstep (se 1 (by rfl) ⟨981935, by rfl⟩ : syracuseStep 1309247 = 1963871) B1963871
theorem B5306953 : Blo 578813 5306953 := bstep (se 2 (by rfl) ⟨1990107, by rfl⟩ : syracuseStep 5306953 = 3980215) B3980215
theorem B981625 : Blo 578813 981625 := bstep (se 2 (by rfl) ⟨368109, by rfl⟩ : syracuseStep 981625 = 736219) B736219
theorem B1309355 : Blo 578813 1309355 := bstep (se 1 (by rfl) ⟨982016, by rfl⟩ : syracuseStep 1309355 = 1964033) B1964033
theorem B981679 : Blo 578813 981679 := bstep (se 1 (by rfl) ⟨736259, by rfl⟩ : syracuseStep 981679 = 1472519) B1472519
theorem B883423 : Blo 578813 883423 := bstep (se 1 (by rfl) ⟨662567, by rfl⟩ : syracuseStep 883423 = 1325135) B1325135
theorem B1473299 : Blo 578813 1473299 := bstep (se 1 (by rfl) ⟨1104974, by rfl⟩ : syracuseStep 1473299 = 2209949) B2209949
theorem B1571663 : Blo 578813 1571663 := bstep (se 1 (by rfl) ⟨1178747, by rfl⟩ : syracuseStep 1571663 = 2357495) B2357495
theorem B1473511 : Blo 578813 1473511 := bstep (se 1 (by rfl) ⟨1105133, by rfl⟩ : syracuseStep 1473511 = 2210267) B2210267
theorem B7044259 : Blo 578813 7044259 := bstep (se 1 (by rfl) ⟨5283194, by rfl⟩ : syracuseStep 7044259 = 10566389) B10566389
theorem B1309895 : Blo 578813 1309895 := bstep (se 1 (by rfl) ⟨982421, by rfl⟩ : syracuseStep 1309895 = 1964843) B1964843
theorem B1965275 : Blo 578813 1965275 := bstep (se 1 (by rfl) ⟨1473956, by rfl⟩ : syracuseStep 1965275 = 2947913) B2947913
theorem B1473785 : Blo 578813 1473785 := bstep (se 2 (by rfl) ⟨552669, by rfl⟩ : syracuseStep 1473785 = 1105339) B1105339
theorem B3538187 : Blo 578813 3538187 := bstep (se 1 (by rfl) ⟨2653640, by rfl⟩ : syracuseStep 3538187 = 5307281) B5307281
theorem B1310075 : Blo 578813 1310075 := bstep (se 1 (by rfl) ⟨982556, by rfl⟩ : syracuseStep 1310075 = 1965113) B1965113
theorem B1572257 : Blo 578813 1572257 := bstep (se 2 (by rfl) ⟨589596, by rfl⟩ : syracuseStep 1572257 = 1179193) B1179193
theorem B1572311 : Blo 578813 1572311 := bstep (se 1 (by rfl) ⟨1179233, by rfl⟩ : syracuseStep 1572311 = 2358467) B2358467
theorem B1310201 : Blo 578813 1310201 := bstep (se 2 (by rfl) ⟨491325, by rfl⟩ : syracuseStep 1310201 = 982651) B982651
theorem B3145225 : Blo 578813 3145225 := bstep (se 2 (by rfl) ⟨1179459, by rfl⟩ : syracuseStep 3145225 = 2358919) B2358919
theorem B1310291 : Blo 578813 1310291 := bstep (se 1 (by rfl) ⟨982718, by rfl⟩ : syracuseStep 1310291 = 1965437) B1965437
theorem B654943 : Blo 578813 654943 := bstep (se 1 (by rfl) ⟨491207, by rfl⟩ : syracuseStep 654943 = 982415) B982415
theorem B2948723 : Blo 578813 2948723 := bstep (se 1 (by rfl) ⟨2211542, by rfl⟩ : syracuseStep 2948723 = 4423085) B4423085
theorem B1310471 : Blo 578813 1310471 := bstep (se 1 (by rfl) ⟨982853, by rfl⟩ : syracuseStep 1310471 = 1965707) B1965707
theorem B1670969 : Blo 578813 1670969 := bstep (se 2 (by rfl) ⟨626613, by rfl⟩ : syracuseStep 1670969 = 1253227) B1253227
theorem B1474433 : Blo 578813 1474433 := bstep (se 2 (by rfl) ⟨552912, by rfl⟩ : syracuseStep 1474433 = 1105825) B1105825
theorem B3309569 : Blo 578813 3309569 := bstep (se 2 (by rfl) ⟨1241088, by rfl⟩ : syracuseStep 3309569 = 2482177) B2482177
theorem B1310759 : Blo 578813 1310759 := bstep (se 1 (by rfl) ⟨983069, by rfl⟩ : syracuseStep 1310759 = 1966139) B1966139
theorem B10485811 : Blo 578813 10485811 := bstep (se 1 (by rfl) ⟨7864358, by rfl⟩ : syracuseStep 10485811 = 15728717) B15728717
theorem B6717491 : Blo 578813 6717491 := bstep (se 1 (by rfl) ⟨5038118, by rfl⟩ : syracuseStep 6717491 = 10076237) B10076237
theorem B1310939 : Blo 578813 1310939 := bstep (se 1 (by rfl) ⟨983204, by rfl⟩ : syracuseStep 1310939 = 1966409) B1966409
theorem B655591 : Blo 578813 655591 := bstep (se 1 (by rfl) ⟨491693, by rfl⟩ : syracuseStep 655591 = 983387) B983387
theorem B983495 : Blo 578813 983495 := bstep (se 1 (by rfl) ⟨737621, by rfl⟩ : syracuseStep 983495 = 1475243) B1475243
theorem B1311209 : Blo 578813 1311209 := bstep (se 2 (by rfl) ⟨491703, by rfl⟩ : syracuseStep 1311209 = 983407) B983407
theorem B2949695 : Blo 578813 2949695 := bstep (se 1 (by rfl) ⟨2212271, by rfl⟩ : syracuseStep 2949695 = 4424543) B4424543
theorem B1966895 : Blo 578813 1966895 := bstep (se 1 (by rfl) ⟨1475171, by rfl⟩ : syracuseStep 1966895 = 2950343) B2950343
theorem B1049555 : Blo 578813 1049555 := bstep (se 1 (by rfl) ⟨787166, by rfl⟩ : syracuseStep 1049555 = 1574333) B1574333
theorem B27264613 : Blo 578813 27264613 := bstep (se 4 (by rfl) ⟨2556057, by rfl⟩ : syracuseStep 27264613 = 5112115) B5112115
theorem B2197799 : Blo 578813 2197799 := bstep (se 1 (by rfl) ⟨1648349, by rfl⟩ : syracuseStep 2197799 = 3296699) B3296699
theorem B3312029 : Blo 578813 3312029 := bstep (se 3 (by rfl) ⟨621005, by rfl⟩ : syracuseStep 3312029 = 1242011) B1242011
theorem B7081037 : Blo 578813 7081037 := bstep (se 3 (by rfl) ⟨1327694, by rfl⟩ : syracuseStep 7081037 = 2655389) B2655389
theorem B1674361 : Blo 578813 1674361 := bstep (se 2 (by rfl) ⟨627885, by rfl⟩ : syracuseStep 1674361 = 1255771) B1255771
theorem B2198771 : Blo 578813 2198771 := bstep (se 1 (by rfl) ⟨1649078, by rfl⟩ : syracuseStep 2198771 = 3298157) B3298157
theorem B2657855 : Blo 578813 2657855 := bstep (se 1 (by rfl) ⟨1993391, by rfl⟩ : syracuseStep 2657855 = 3986783) B3986783
theorem B23826271 : Blo 578813 23826271 := bstep (se 1 (by rfl) ⟨17869703, by rfl⟩ : syracuseStep 23826271 = 35739407) B35739407
theorem B1118519 : Blo 578813 1118519 := bstep (se 1 (by rfl) ⟨838889, by rfl⟩ : syracuseStep 1118519 = 1677779) B1677779
theorem B33952541 : Blo 578813 33952541 := bstep (se 3 (by rfl) ⟨6366101, by rfl⟩ : syracuseStep 33952541 = 12732203) B12732203
theorem B122131235 : Blo 578813 122131235 := bstep (se 1 (by rfl) ⟨91598426, by rfl⟩ : syracuseStep 122131235 = 183196853) B183196853
theorem B3314627 : Blo 578813 3314627 := bstep (se 1 (by rfl) ⟨2485970, by rfl⟩ : syracuseStep 3314627 = 4971941) B4971941
theorem B4199633 : Blo 578813 4199633 := bstep (se 2 (by rfl) ⟨1574862, by rfl⟩ : syracuseStep 4199633 = 3149725) B3149725
theorem B825319 : Blo 578813 825319 := bstep (se 1 (by rfl) ⟨618989, by rfl⟩ : syracuseStep 825319 = 1237979) B1237979
theorem B1906931 : Blo 578813 1906931 := bstep (se 1 (by rfl) ⟨1430198, by rfl⟩ : syracuseStep 1906931 = 2860397) B2860397
theorem B6593075 : Blo 578813 6593075 := bstep (se 1 (by rfl) ⟨4944806, by rfl⟩ : syracuseStep 6593075 = 9889613) B9889613
theorem B4070249 : Blo 578813 4070249 := bstep (se 2 (by rfl) ⟨1526343, by rfl⟩ : syracuseStep 4070249 = 3052687) B3052687
theorem B3316585 : Blo 578813 3316585 := bstep (se 2 (by rfl) ⟨1243719, by rfl⟩ : syracuseStep 3316585 = 2487439) B2487439
theorem B5577943 : Blo 578813 5577943 := bstep (se 1 (by rfl) ⟨4183457, by rfl⟩ : syracuseStep 5577943 = 8366915) B8366915
theorem B2792663 : Blo 578813 2792663 := bstep (se 1 (by rfl) ⟨2094497, by rfl⟩ : syracuseStep 2792663 = 4188995) B4188995
theorem B5644079 : Blo 578813 5644079 := bstep (se 1 (by rfl) ⟨4233059, by rfl⟩ : syracuseStep 5644079 = 8466119) B8466119
theorem B28286779 : Blo 578813 28286779 := bstep (se 1 (by rfl) ⟨21215084, by rfl⟩ : syracuseStep 28286779 = 42430169) B42430169
theorem B2203463 : Blo 578813 2203463 := bstep (se 1 (by rfl) ⟨1652597, by rfl⟩ : syracuseStep 2203463 = 3305195) B3305195
theorem B991147 : Blo 578813 991147 := bstep (se 1 (by rfl) ⟨743360, by rfl⟩ : syracuseStep 991147 = 1486721) B1486721
theorem B4235399 : Blo 578813 4235399 := bstep (se 1 (by rfl) ⟨3176549, by rfl⟩ : syracuseStep 4235399 = 6353099) B6353099
theorem B1810895 : Blo 578813 1810895 := bstep (se 1 (by rfl) ⟨1358171, by rfl⟩ : syracuseStep 1810895 = 2716343) B2716343
theorem B7053895 : Blo 578813 7053895 := bstep (se 1 (by rfl) ⟨5290421, by rfl⟩ : syracuseStep 7053895 = 10580843) B10580843
theorem B2007625 : Blo 578813 2007625 := bstep (se 2 (by rfl) ⟨752859, by rfl⟩ : syracuseStep 2007625 = 1505719) B1505719
theorem B828139 : Blo 578813 828139 := bstep (se 1 (by rfl) ⟨621104, by rfl⟩ : syracuseStep 828139 = 1242209) B1242209
theorem B2204435 : Blo 578813 2204435 := bstep (se 1 (by rfl) ⟨1653326, by rfl⟩ : syracuseStep 2204435 = 3306653) B3306653
theorem B6595991 : Blo 578813 6595991 := bstep (se 1 (by rfl) ⟨4946993, by rfl⟩ : syracuseStep 6595991 = 9893987) B9893987
theorem B2205103 : Blo 578813 2205103 := bstep (se 1 (by rfl) ⟨1653827, by rfl⟩ : syracuseStep 2205103 = 3307655) B3307655
theorem B6597449 : Blo 578813 6597449 := bstep (se 2 (by rfl) ⟨2474043, by rfl⟩ : syracuseStep 6597449 = 4948087) B4948087
theorem B733151 : Blo 578813 733151 := bstep (se 1 (by rfl) ⟨549863, by rfl⟩ : syracuseStep 733151 = 1099727) B1099727
theorem B3715577 : Blo 578813 3715577 := bstep (se 2 (by rfl) ⟨1393341, by rfl⟩ : syracuseStep 3715577 = 2786683) B2786683
theorem B733799 : Blo 578813 733799 := bstep (se 1 (by rfl) ⟨550349, by rfl⟩ : syracuseStep 733799 = 1100699) B1100699
theorem B7451351 : Blo 578813 7451351 := bstep (se 1 (by rfl) ⟨5588513, by rfl⟩ : syracuseStep 7451351 = 11177027) B11177027
theorem B2209463 : Blo 578813 2209463 := bstep (se 1 (by rfl) ⟨1657097, by rfl⟩ : syracuseStep 2209463 = 3314195) B3314195
theorem B3979145 : Blo 578813 3979145 := bstep (se 2 (by rfl) ⟨1492179, by rfl⟩ : syracuseStep 3979145 = 2984359) B2984359
theorem B5454253 : Blo 578813 5454253 := bstep (se 3 (by rfl) ⟨1022672, by rfl⟩ : syracuseStep 5454253 = 2045345) B2045345
theorem B637787 : Blo 578813 637787 := bstep (se 1 (by rfl) ⟨478340, by rfl⟩ : syracuseStep 637787 = 956681) B956681
theorem B7945147 : Blo 578813 7945147 := bstep (se 1 (by rfl) ⟨5958860, by rfl⟩ : syracuseStep 7945147 = 11917721) B11917721
theorem B5028905 : Blo 578813 5028905 := bstep (se 2 (by rfl) ⟨1885839, by rfl⟩ : syracuseStep 5028905 = 3771679) B3771679
theorem B2211239 : Blo 578813 2211239 := bstep (se 1 (by rfl) ⟨1658429, by rfl⟩ : syracuseStep 2211239 = 3316859) B3316859
theorem B737095 : Blo 578813 737095 := bstep (se 1 (by rfl) ⟨552821, by rfl⟩ : syracuseStep 737095 = 1105643) B1105643
theorem B868319 : Blo 578813 868319 := bstep (se 1 (by rfl) ⟨651239, by rfl⟩ : syracuseStep 868319 = 1302479) B1302479
theorem B20070433 : Blo 578813 20070433 := bstep (se 2 (by rfl) ⟨7526412, by rfl⟩ : syracuseStep 20070433 = 15052825) B15052825
theorem B868571 : Blo 578813 868571 := bstep (se 1 (by rfl) ⟨651428, by rfl⟩ : syracuseStep 868571 = 1302857) B1302857
theorem B868583 : Blo 578813 868583 := bstep (se 1 (by rfl) ⟨651437, by rfl⟩ : syracuseStep 868583 = 1302875) B1302875
theorem B868745 : Blo 578813 868745 := bstep (se 2 (by rfl) ⟨325779, by rfl⟩ : syracuseStep 868745 = 651559) B651559
theorem B868841 : Blo 578813 868841 := bstep (se 2 (by rfl) ⟨325815, by rfl⟩ : syracuseStep 868841 = 651631) B651631
theorem B868967 : Blo 578813 868967 := bstep (se 1 (by rfl) ⟨651725, by rfl⟩ : syracuseStep 868967 = 1303451) B1303451
theorem B34030199 : Blo 578813 34030199 := bstep (se 1 (by rfl) ⟨25522649, by rfl⟩ : syracuseStep 34030199 = 51045299) B51045299
theorem B869099 : Blo 578813 869099 := bstep (se 1 (by rfl) ⟨651824, by rfl⟩ : syracuseStep 869099 = 1303649) B1303649
theorem B1655549 : Blo 578813 1655549 := bstep (se 3 (by rfl) ⟨310415, by rfl⟩ : syracuseStep 1655549 = 620831) B620831
theorem B869129 : Blo 578813 869129 := bstep (se 2 (by rfl) ⟨325923, by rfl⟩ : syracuseStep 869129 = 651847) B651847
theorem B869231 : Blo 578813 869231 := bstep (se 1 (by rfl) ⟨651923, by rfl⟩ : syracuseStep 869231 = 1303847) B1303847
theorem B2933819 : Blo 578813 2933819 := bstep (se 1 (by rfl) ⟨2200364, by rfl⟩ : syracuseStep 2933819 = 4400729) B4400729
theorem B869483 : Blo 578813 869483 := bstep (se 1 (by rfl) ⟨652112, by rfl⟩ : syracuseStep 869483 = 1304225) B1304225
theorem B2933981 : Blo 578813 2933981 := bstep (se 3 (by rfl) ⟨550121, by rfl⟩ : syracuseStep 2933981 = 1100243) B1100243
theorem B869723 : Blo 578813 869723 := bstep (se 1 (by rfl) ⟨652292, by rfl⟩ : syracuseStep 869723 = 1304585) B1304585
theorem B15877619 : Blo 578813 15877619 := bstep (se 1 (by rfl) ⟨11908214, by rfl⟩ : syracuseStep 15877619 = 23816429) B23816429
theorem B869999 : Blo 578813 869999 := bstep (se 1 (by rfl) ⟨652499, by rfl⟩ : syracuseStep 869999 = 1304999) B1304999
theorem B870071 : Blo 578813 870071 := bstep (se 1 (by rfl) ⟨652553, by rfl⟩ : syracuseStep 870071 = 1305107) B1305107
theorem B870107 : Blo 578813 870107 := bstep (se 1 (by rfl) ⟨652580, by rfl⟩ : syracuseStep 870107 = 1305161) B1305161
theorem B1656607 : Blo 578813 1656607 := bstep (se 1 (by rfl) ⟨1242455, by rfl⟩ : syracuseStep 1656607 = 2484911) B2484911
theorem B870281 : Blo 578813 870281 := bstep (se 2 (by rfl) ⟨326355, by rfl⟩ : syracuseStep 870281 = 652711) B652711
theorem B870383 : Blo 578813 870383 := bstep (se 1 (by rfl) ⟨652787, by rfl⟩ : syracuseStep 870383 = 1305575) B1305575
theorem B1394879 : Blo 578813 1394879 := bstep (se 1 (by rfl) ⟨1046159, by rfl⟩ : syracuseStep 1394879 = 2092319) B2092319
theorem B870635 : Blo 578813 870635 := bstep (se 1 (by rfl) ⟨652976, by rfl⟩ : syracuseStep 870635 = 1305953) B1305953
theorem B870695 : Blo 578813 870695 := bstep (se 1 (by rfl) ⟨653021, by rfl⟩ : syracuseStep 870695 = 1306043) B1306043
theorem B245057879 : Blo 578813 245057879 := bstep (se 1 (by rfl) ⟨183793409, by rfl⟩ : syracuseStep 245057879 = 367586819) B367586819
theorem B870779 : Blo 578813 870779 := bstep (se 1 (by rfl) ⟨653084, by rfl⟩ : syracuseStep 870779 = 1306169) B1306169
theorem B4966919 : Blo 578813 4966919 := bstep (se 1 (by rfl) ⟨3725189, by rfl⟩ : syracuseStep 4966919 = 7450379) B7450379
theorem B871049 : Blo 578813 871049 := bstep (se 2 (by rfl) ⟨326643, by rfl⟩ : syracuseStep 871049 = 653287) B653287
theorem B871223 : Blo 578813 871223 := bstep (se 1 (by rfl) ⟨653417, by rfl⟩ : syracuseStep 871223 = 1306835) B1306835
theorem B1657655 : Blo 578813 1657655 := bstep (se 1 (by rfl) ⟨1243241, by rfl⟩ : syracuseStep 1657655 = 2486483) B2486483
theorem B871259 : Blo 578813 871259 := bstep (se 1 (by rfl) ⟨653444, by rfl⟩ : syracuseStep 871259 = 1306889) B1306889
theorem B871403 : Blo 578813 871403 := bstep (se 1 (by rfl) ⟨653552, by rfl⟩ : syracuseStep 871403 = 1307105) B1307105
theorem B871607 : Blo 578813 871607 := bstep (se 1 (by rfl) ⟨653705, by rfl⟩ : syracuseStep 871607 = 1307411) B1307411
theorem B26791229 : Blo 578813 26791229 := bstep (se 3 (by rfl) ⟨5023355, by rfl⟩ : syracuseStep 26791229 = 10046711) B10046711
theorem B1658191 : Blo 578813 1658191 := bstep (se 1 (by rfl) ⟨1243643, by rfl⟩ : syracuseStep 1658191 = 2487287) B2487287
theorem B871847 : Blo 578813 871847 := bstep (se 1 (by rfl) ⟨653885, by rfl⟩ : syracuseStep 871847 = 1307771) B1307771
theorem B1854971 : Blo 578813 1854971 := bstep (se 1 (by rfl) ⟨1391228, by rfl⟩ : syracuseStep 1854971 = 2782457) B2782457
theorem B871931 : Blo 578813 871931 := bstep (se 1 (by rfl) ⟨653948, by rfl⟩ : syracuseStep 871931 = 1307897) B1307897
theorem B872027 : Blo 578813 872027 := bstep (se 1 (by rfl) ⟨654020, by rfl⟩ : syracuseStep 872027 = 1308041) B1308041
theorem B872111 : Blo 578813 872111 := bstep (se 1 (by rfl) ⟨654083, by rfl⟩ : syracuseStep 872111 = 1308167) B1308167
theorem B872231 : Blo 578813 872231 := bstep (se 1 (by rfl) ⟨654173, by rfl⟩ : syracuseStep 872231 = 1308347) B1308347
theorem B872315 : Blo 578813 872315 := bstep (se 1 (by rfl) ⟨654236, by rfl⟩ : syracuseStep 872315 = 1308473) B1308473
theorem B17256509 : Blo 578813 17256509 := bstep (se 3 (by rfl) ⟨3235595, by rfl⟩ : syracuseStep 17256509 = 6471191) B6471191
theorem B2642107 : Blo 578813 2642107 := bstep (se 1 (by rfl) ⟨1981580, by rfl⟩ : syracuseStep 2642107 = 3963161) B3963161
theorem B9392345 : Blo 578813 9392345 := bstep (se 2 (by rfl) ⟨3522129, by rfl⟩ : syracuseStep 9392345 = 7044259) B7044259
theorem B7459037 : Blo 578813 7459037 := bstep (se 3 (by rfl) ⟨1398569, by rfl⟩ : syracuseStep 7459037 = 2797139) B2797139
theorem B872735 : Blo 578813 872735 := bstep (se 1 (by rfl) ⟨654551, by rfl⟩ : syracuseStep 872735 = 1309103) B1309103
theorem B8147249 : Blo 578813 8147249 := bstep (se 2 (by rfl) ⟨3055218, by rfl⟩ : syracuseStep 8147249 = 6110437) B6110437
theorem B872759 : Blo 578813 872759 := bstep (se 1 (by rfl) ⟨654569, by rfl⟩ : syracuseStep 872759 = 1309139) B1309139
theorem B872831 : Blo 578813 872831 := bstep (se 1 (by rfl) ⟨654623, by rfl⟩ : syracuseStep 872831 = 1309247) B1309247
theorem B872903 : Blo 578813 872903 := bstep (se 1 (by rfl) ⟨654677, by rfl⟩ : syracuseStep 872903 = 1309355) B1309355
theorem B1954259 : Blo 578813 1954259 := bstep (se 1 (by rfl) ⟨1465694, by rfl⟩ : syracuseStep 1954259 = 2931389) B2931389
theorem B4182623 : Blo 578813 4182623 := bstep (se 1 (by rfl) ⟨3136967, by rfl⟩ : syracuseStep 4182623 = 6273935) B6273935
theorem B873257 : Blo 578813 873257 := bstep (se 2 (by rfl) ⟨327471, by rfl⟩ : syracuseStep 873257 = 654943) B654943
theorem B873263 : Blo 578813 873263 := bstep (se 1 (by rfl) ⟨654947, by rfl⟩ : syracuseStep 873263 = 1309895) B1309895
theorem B873383 : Blo 578813 873383 := bstep (se 1 (by rfl) ⟨655037, by rfl⟩ : syracuseStep 873383 = 1310075) B1310075
theorem B3527675 : Blo 578813 3527675 := bstep (se 1 (by rfl) ⟨2645756, by rfl⟩ : syracuseStep 3527675 = 5291513) B5291513
theorem B873467 : Blo 578813 873467 := bstep (se 1 (by rfl) ⟨655100, by rfl⟩ : syracuseStep 873467 = 1310201) B1310201
theorem B873527 : Blo 578813 873527 := bstep (se 1 (by rfl) ⟨655145, by rfl⟩ : syracuseStep 873527 = 1310291) B1310291
theorem B2938031 : Blo 578813 2938031 := bstep (se 1 (by rfl) ⟨2203523, by rfl⟩ : syracuseStep 2938031 = 4407047) B4407047
theorem B873647 : Blo 578813 873647 := bstep (se 1 (by rfl) ⟨655235, by rfl⟩ : syracuseStep 873647 = 1310471) B1310471
theorem B8377577 : Blo 578813 8377577 := bstep (se 2 (by rfl) ⟨3141591, by rfl⟩ : syracuseStep 8377577 = 6283183) B6283183
theorem B578971 : Blo 578813 578971 := bstep (se 1 (by rfl) ⟨434228, by rfl⟩ : syracuseStep 578971 = 868457) B868457
theorem B874055 : Blo 578813 874055 := bstep (se 1 (by rfl) ⟨655541, by rfl⟩ : syracuseStep 874055 = 1311083) B1311083
theorem B579183 : Blo 578813 579183 := bstep (se 1 (by rfl) ⟨434387, by rfl⟩ : syracuseStep 579183 = 868775) B868775
theorem B325998229 : Blo 578813 325998229 := bstep (se 6 (by rfl) ⟨7640583, by rfl⟩ : syracuseStep 325998229 = 15281167) B15281167
theorem B579239 : Blo 578813 579239 := bstep (se 1 (by rfl) ⟨434429, by rfl⟩ : syracuseStep 579239 = 868859) B868859
theorem B874151 : Blo 578813 874151 := bstep (se 1 (by rfl) ⟨655613, by rfl⟩ : syracuseStep 874151 = 1311227) B1311227
theorem B579323 : Blo 578813 579323 := bstep (se 1 (by rfl) ⟨434492, by rfl⟩ : syracuseStep 579323 = 868985) B868985
theorem B579359 : Blo 578813 579359 := bstep (se 1 (by rfl) ⟨434519, by rfl⟩ : syracuseStep 579359 = 869039) B869039
theorem B579391 : Blo 578813 579391 := bstep (se 1 (by rfl) ⟨434543, by rfl⟩ : syracuseStep 579391 = 869087) B869087
theorem B579567 : Blo 578813 579567 := bstep (se 1 (by rfl) ⟨434675, by rfl⟩ : syracuseStep 579567 = 869351) B869351
theorem B579739 : Blo 578813 579739 := bstep (se 1 (by rfl) ⟨434804, by rfl⟩ : syracuseStep 579739 = 869609) B869609
theorem B579775 : Blo 578813 579775 := bstep (se 1 (by rfl) ⟨434831, by rfl⟩ : syracuseStep 579775 = 869663) B869663
theorem B579887 : Blo 578813 579887 := bstep (se 1 (by rfl) ⟨434915, by rfl⟩ : syracuseStep 579887 = 869831) B869831
theorem B1956203 : Blo 578813 1956203 := bstep (se 1 (by rfl) ⟨1467152, by rfl⟩ : syracuseStep 1956203 = 2934305) B2934305
theorem B18897299 : Blo 578813 18897299 := bstep (se 1 (by rfl) ⟨14172974, by rfl⟩ : syracuseStep 18897299 = 28345949) B28345949
theorem B580123 : Blo 578813 580123 := bstep (se 1 (by rfl) ⟨435092, by rfl⟩ : syracuseStep 580123 = 870185) B870185
theorem B580127 : Blo 578813 580127 := bstep (se 1 (by rfl) ⟨435095, by rfl⟩ : syracuseStep 580127 = 870191) B870191
theorem B2939489 : Blo 578813 2939489 := bstep (se 2 (by rfl) ⟨1102308, by rfl⟩ : syracuseStep 2939489 = 2204617) B2204617
theorem B1956473 : Blo 578813 1956473 := bstep (se 2 (by rfl) ⟨733677, by rfl⟩ : syracuseStep 1956473 = 1467355) B1467355
theorem B7461497 : Blo 578813 7461497 := bstep (se 2 (by rfl) ⟨2798061, by rfl⟩ : syracuseStep 7461497 = 5596123) B5596123
theorem B2480777 : Blo 578813 2480777 := bstep (se 2 (by rfl) ⟨930291, by rfl⟩ : syracuseStep 2480777 = 1860583) B1860583
theorem B580443 : Blo 578813 580443 := bstep (se 1 (by rfl) ⟨435332, by rfl⟩ : syracuseStep 580443 = 870665) B870665
theorem B580511 : Blo 578813 580511 := bstep (se 1 (by rfl) ⟨435383, by rfl⟩ : syracuseStep 580511 = 870767) B870767
theorem B1956905 : Blo 578813 1956905 := bstep (se 2 (by rfl) ⟨733839, by rfl⟩ : syracuseStep 1956905 = 1467679) B1467679
theorem B580655 : Blo 578813 580655 := bstep (se 1 (by rfl) ⟨435491, by rfl⟩ : syracuseStep 580655 = 870983) B870983
theorem B580679 : Blo 578813 580679 := bstep (se 1 (by rfl) ⟨435509, by rfl⟩ : syracuseStep 580679 = 871019) B871019
theorem B4021433 : Blo 578813 4021433 := bstep (se 2 (by rfl) ⟨1508037, by rfl⟩ : syracuseStep 4021433 = 3016075) B3016075
theorem B580831 : Blo 578813 580831 := bstep (se 1 (by rfl) ⟨435623, by rfl⟩ : syracuseStep 580831 = 871247) B871247
theorem B2940299 : Blo 578813 2940299 := bstep (se 1 (by rfl) ⟨2205224, by rfl⟩ : syracuseStep 2940299 = 4410449) B4410449
theorem B581095 : Blo 578813 581095 := bstep (se 1 (by rfl) ⟨435821, by rfl⟩ : syracuseStep 581095 = 871643) B871643
theorem B581211 : Blo 578813 581211 := bstep (se 1 (by rfl) ⟨435908, by rfl⟩ : syracuseStep 581211 = 871817) B871817
theorem B1990331 : Blo 578813 1990331 := bstep (se 1 (by rfl) ⟨1492748, by rfl⟩ : syracuseStep 1990331 = 2985497) B2985497
theorem B3301073 : Blo 578813 3301073 := bstep (se 2 (by rfl) ⟨1237902, by rfl⟩ : syracuseStep 3301073 = 2475805) B2475805
theorem B581447 : Blo 578813 581447 := bstep (se 1 (by rfl) ⟨436085, by rfl⟩ : syracuseStep 581447 = 872171) B872171
theorem B1105787 : Blo 578813 1105787 := bstep (se 1 (by rfl) ⟨829340, by rfl⟩ : syracuseStep 1105787 = 1658681) B1658681
theorem B1302443 : Blo 578813 1302443 := bstep (se 1 (by rfl) ⟨976832, by rfl⟩ : syracuseStep 1302443 = 1953665) B1953665
theorem B2482109 : Blo 578813 2482109 := bstep (se 3 (by rfl) ⟨465395, by rfl⟩ : syracuseStep 2482109 = 930791) B930791
theorem B581599 : Blo 578813 581599 := bstep (se 1 (by rfl) ⟨436199, by rfl⟩ : syracuseStep 581599 = 872399) B872399
theorem B529915877 : Blo 578813 529915877 := bstep (se 4 (by rfl) ⟨49679613, by rfl⟩ : syracuseStep 529915877 = 99359227) B99359227
theorem B3825883 : Blo 578813 3825883 := bstep (se 1 (by rfl) ⟨2869412, by rfl⟩ : syracuseStep 3825883 = 5738825) B5738825
theorem B581863 : Blo 578813 581863 := bstep (se 1 (by rfl) ⟨436397, by rfl⟩ : syracuseStep 581863 = 872795) B872795
theorem B1106273 : Blo 578813 1106273 := bstep (se 2 (by rfl) ⟨414852, by rfl⟩ : syracuseStep 1106273 = 829705) B829705
theorem B582015 : Blo 578813 582015 := bstep (se 1 (by rfl) ⟨436511, by rfl⟩ : syracuseStep 582015 = 873023) B873023
theorem B1302983 : Blo 578813 1302983 := bstep (se 1 (by rfl) ⟨977237, by rfl⟩ : syracuseStep 1302983 = 1954475) B1954475
theorem B582095 : Blo 578813 582095 := bstep (se 1 (by rfl) ⟨436571, by rfl⟩ : syracuseStep 582095 = 873143) B873143
theorem B582247 : Blo 578813 582247 := bstep (se 1 (by rfl) ⟨436685, by rfl⟩ : syracuseStep 582247 = 873371) B873371
theorem B28271213 : Blo 578813 28271213 := bstep (se 3 (by rfl) ⟨5300852, by rfl⟩ : syracuseStep 28271213 = 10601705) B10601705
theorem B1303343 : Blo 578813 1303343 := bstep (se 1 (by rfl) ⟨977507, by rfl⟩ : syracuseStep 1303343 = 1955015) B1955015
theorem B1467193 : Blo 578813 1467193 := bstep (se 2 (by rfl) ⟨550197, by rfl⟩ : syracuseStep 1467193 = 1100395) B1100395
theorem B582511 : Blo 578813 582511 := bstep (se 1 (by rfl) ⟨436883, by rfl⟩ : syracuseStep 582511 = 873767) B873767
theorem B582567 : Blo 578813 582567 := bstep (se 1 (by rfl) ⟨436925, by rfl⟩ : syracuseStep 582567 = 873851) B873851
theorem B582651 : Blo 578813 582651 := bstep (se 1 (by rfl) ⟨436988, by rfl⟩ : syracuseStep 582651 = 873977) B873977
theorem B582719 : Blo 578813 582719 := bstep (se 1 (by rfl) ⟨437039, by rfl⟩ : syracuseStep 582719 = 874079) B874079
theorem B1467497 : Blo 578813 1467497 := bstep (se 2 (by rfl) ⟨550311, by rfl⟩ : syracuseStep 1467497 = 1100623) B1100623
theorem B1959119 : Blo 578813 1959119 := bstep (se 1 (by rfl) ⟨1469339, by rfl⟩ : syracuseStep 1959119 = 2938679) B2938679
theorem B1959443 : Blo 578813 1959443 := bstep (se 1 (by rfl) ⟨1469582, by rfl⟩ : syracuseStep 1959443 = 2939165) B2939165
theorem B3302963 : Blo 578813 3302963 := bstep (se 1 (by rfl) ⟨2477222, by rfl⟩ : syracuseStep 3302963 = 4954445) B4954445
theorem B7923257 : Blo 578813 7923257 := bstep (se 2 (by rfl) ⟨2971221, by rfl⟩ : syracuseStep 7923257 = 5942443) B5942443
theorem B5301881 : Blo 578813 5301881 := bstep (se 2 (by rfl) ⟨1988205, by rfl⟩ : syracuseStep 5301881 = 3976411) B3976411
theorem B2975491 : Blo 578813 2975491 := bstep (se 1 (by rfl) ⟨2231618, by rfl⟩ : syracuseStep 2975491 = 4463237) B4463237
theorem B1304351 : Blo 578813 1304351 := bstep (se 1 (by rfl) ⟨978263, by rfl⟩ : syracuseStep 1304351 = 1956527) B1956527
theorem B68118353 : Blo 578813 68118353 := bstep (se 2 (by rfl) ⟨25544382, by rfl⟩ : syracuseStep 68118353 = 51088765) B51088765
theorem B1304567 : Blo 578813 1304567 := bstep (se 1 (by rfl) ⟨978425, by rfl⟩ : syracuseStep 1304567 = 1956851) B1956851
theorem B6711443 : Blo 578813 6711443 := bstep (se 1 (by rfl) ⟨5033582, by rfl⟩ : syracuseStep 6711443 = 10067165) B10067165
theorem B1468631 : Blo 578813 1468631 := bstep (se 1 (by rfl) ⟨1101473, by rfl⟩ : syracuseStep 1468631 = 2202947) B2202947
theorem B1468651 : Blo 578813 1468651 := bstep (se 1 (by rfl) ⟨1101488, by rfl⟩ : syracuseStep 1468651 = 2202977) B2202977
theorem B3303737 : Blo 578813 3303737 := bstep (se 2 (by rfl) ⟨1238901, by rfl⟩ : syracuseStep 3303737 = 2477803) B2477803
theorem B1304927 : Blo 578813 1304927 := bstep (se 1 (by rfl) ⟨978695, by rfl⟩ : syracuseStep 1304927 = 1957391) B1957391
theorem B1468955 : Blo 578813 1468955 := bstep (se 1 (by rfl) ⟨1101716, by rfl⟩ : syracuseStep 1468955 = 2203433) B2203433
theorem B1960631 : Blo 578813 1960631 := bstep (se 1 (by rfl) ⟨1470473, by rfl⟩ : syracuseStep 1960631 = 2940947) B2940947
theorem B5040899 : Blo 578813 5040899 := bstep (se 1 (by rfl) ⟨3780674, by rfl⟩ : syracuseStep 5040899 = 7561349) B7561349
theorem B977899 : Blo 578813 977899 := bstep (se 1 (by rfl) ⟨733424, by rfl⟩ : syracuseStep 977899 = 1466849) B1466849
theorem B1305647 : Blo 578813 1305647 := bstep (se 1 (by rfl) ⟨979235, by rfl⟩ : syracuseStep 1305647 = 1958471) B1958471
theorem B978041 : Blo 578813 978041 := bstep (se 2 (by rfl) ⟨366765, by rfl⟩ : syracuseStep 978041 = 733531) B733531
theorem B1305935 : Blo 578813 1305935 := bstep (se 1 (by rfl) ⟨979451, by rfl⟩ : syracuseStep 1305935 = 1958903) B1958903
theorem B1306025 : Blo 578813 1306025 := bstep (se 2 (by rfl) ⟨489759, by rfl⟩ : syracuseStep 1306025 = 979519) B979519
theorem B1469947 : Blo 578813 1469947 := bstep (se 1 (by rfl) ⟨1102460, by rfl⟩ : syracuseStep 1469947 = 2204921) B2204921
theorem B1470059 : Blo 578813 1470059 := bstep (se 1 (by rfl) ⟨1102544, by rfl⟩ : syracuseStep 1470059 = 2205089) B2205089
theorem B4419197 : Blo 578813 4419197 := bstep (se 3 (by rfl) ⟨828599, by rfl⟩ : syracuseStep 4419197 = 1657199) B1657199
theorem B1306511 : Blo 578813 1306511 := bstep (se 1 (by rfl) ⟨979883, by rfl⟩ : syracuseStep 1306511 = 1959767) B1959767
theorem B2125723 : Blo 578813 2125723 := bstep (se 1 (by rfl) ⟨1594292, by rfl⟩ : syracuseStep 2125723 = 3188585) B3188585
theorem B979175 : Blo 578813 979175 := bstep (se 1 (by rfl) ⟨734381, by rfl⟩ : syracuseStep 979175 = 1468763) B1468763
theorem B979337 : Blo 578813 979337 := bstep (se 2 (by rfl) ⟨367251, by rfl⟩ : syracuseStep 979337 = 734503) B734503
theorem B2093647 : Blo 578813 2093647 := bstep (se 1 (by rfl) ⟨1570235, by rfl⟩ : syracuseStep 2093647 = 3140471) B3140471
theorem B1962575 : Blo 578813 1962575 := bstep (se 1 (by rfl) ⟨1471931, by rfl⟩ : syracuseStep 1962575 = 2943863) B2943863
theorem B1307231 : Blo 578813 1307231 := bstep (se 1 (by rfl) ⟨980423, by rfl⟩ : syracuseStep 1307231 = 1960847) B1960847
theorem B979769 : Blo 578813 979769 := bstep (se 2 (by rfl) ⟨367413, by rfl⟩ : syracuseStep 979769 = 734827) B734827
theorem B979823 : Blo 578813 979823 := bstep (se 1 (by rfl) ⟨734867, by rfl⟩ : syracuseStep 979823 = 1469735) B1469735
theorem B7435253 : Blo 578813 7435253 := bstep (se 5 (by rfl) ⟨348527, by rfl⟩ : syracuseStep 7435253 = 697055) B697055
theorem B652351 : Blo 578813 652351 := bstep (se 1 (by rfl) ⟨489263, by rfl⟩ : syracuseStep 652351 = 978527) B978527
theorem B1963115 : Blo 578813 1963115 := bstep (se 1 (by rfl) ⟨1472336, by rfl⟩ : syracuseStep 1963115 = 2944673) B2944673
theorem B652495 : Blo 578813 652495 := bstep (se 1 (by rfl) ⟨489371, by rfl⟩ : syracuseStep 652495 = 978743) B978743
theorem B1308059 : Blo 578813 1308059 := bstep (se 1 (by rfl) ⟨981044, by rfl⟩ : syracuseStep 1308059 = 1962089) B1962089
theorem B1766855 : Blo 578813 1766855 := bstep (se 1 (by rfl) ⟨1325141, by rfl⟩ : syracuseStep 1766855 = 2650283) B2650283
theorem B1242695 : Blo 578813 1242695 := bstep (se 1 (by rfl) ⟨932021, by rfl⟩ : syracuseStep 1242695 = 1864043) B1864043
theorem B1177271 : Blo 578813 1177271 := bstep (se 1 (by rfl) ⟨882953, by rfl⟩ : syracuseStep 1177271 = 1765907) B1765907
theorem B7141067 : Blo 578813 7141067 := bstep (se 1 (by rfl) ⟨5355800, by rfl⟩ : syracuseStep 7141067 = 10711601) B10711601
theorem B6616849 : Blo 578813 6616849 := bstep (se 2 (by rfl) ⟨2481318, by rfl⟩ : syracuseStep 6616849 = 4962637) B4962637
theorem B4945697 : Blo 578813 4945697 := bstep (se 2 (by rfl) ⟨1854636, by rfl⟩ : syracuseStep 4945697 = 3709273) B3709273
theorem B980815 : Blo 578813 980815 := bstep (se 1 (by rfl) ⟨735611, by rfl⟩ : syracuseStep 980815 = 1471223) B1471223
theorem B2488259 : Blo 578813 2488259 := bstep (se 1 (by rfl) ⟨1866194, by rfl⟩ : syracuseStep 2488259 = 3732389) B3732389
theorem B1308635 : Blo 578813 1308635 := bstep (se 1 (by rfl) ⟨981476, by rfl⟩ : syracuseStep 1308635 = 1962953) B1962953
theorem B2095087 : Blo 578813 2095087 := bstep (se 1 (by rfl) ⟨1571315, by rfl⟩ : syracuseStep 2095087 = 3142631) B3142631
theorem B7075937 : Blo 578813 7075937 := bstep (se 2 (by rfl) ⟨2653476, by rfl⟩ : syracuseStep 7075937 = 5306953) B5306953
theorem B1308815 : Blo 578813 1308815 := bstep (se 1 (by rfl) ⟨981611, by rfl⟩ : syracuseStep 1308815 = 1963223) B1963223
theorem B653467 : Blo 578813 653467 := bstep (se 1 (by rfl) ⟨490100, by rfl⟩ : syracuseStep 653467 = 980201) B980201
theorem B1308833 : Blo 578813 1308833 := bstep (se 2 (by rfl) ⟨490812, by rfl⟩ : syracuseStep 1308833 = 981625) B981625
theorem B653503 : Blo 578813 653503 := bstep (se 1 (by rfl) ⟨490127, by rfl⟩ : syracuseStep 653503 = 980255) B980255
theorem B1308905 : Blo 578813 1308905 := bstep (se 2 (by rfl) ⟨490839, by rfl⟩ : syracuseStep 1308905 = 981679) B981679
theorem B981227 : Blo 578813 981227 := bstep (se 1 (by rfl) ⟨735920, by rfl⟩ : syracuseStep 981227 = 1471841) B1471841
theorem B1177897 : Blo 578813 1177897 := bstep (se 2 (by rfl) ⟨441711, by rfl⟩ : syracuseStep 1177897 = 883423) B883423
theorem B1964411 : Blo 578813 1964411 := bstep (se 1 (by rfl) ⟨1473308, by rfl⟩ : syracuseStep 1964411 = 2946617) B2946617
theorem B4192685 : Blo 578813 4192685 := bstep (se 3 (by rfl) ⟨786128, by rfl⟩ : syracuseStep 4192685 = 1572257) B1572257
theorem B2783801 : Blo 578813 2783801 := bstep (se 2 (by rfl) ⟨1043925, by rfl⟩ : syracuseStep 2783801 = 2087851) B2087851
theorem B4192829 : Blo 578813 4192829 := bstep (se 3 (by rfl) ⟨786155, by rfl⟩ : syracuseStep 4192829 = 1572311) B1572311
theorem B3308111 : Blo 578813 3308111 := bstep (se 1 (by rfl) ⟨2481083, by rfl⟩ : syracuseStep 3308111 = 4962167) B4962167
theorem B1964681 : Blo 578813 1964681 := bstep (se 2 (by rfl) ⟨736755, by rfl⟩ : syracuseStep 1964681 = 1473511) B1473511
theorem B982057 : Blo 578813 982057 := bstep (se 2 (by rfl) ⟨368271, by rfl⟩ : syracuseStep 982057 = 736543) B736543
theorem B982199 : Blo 578813 982199 := bstep (se 1 (by rfl) ⟨736649, by rfl⟩ : syracuseStep 982199 = 1473299) B1473299
theorem B1047775 : Blo 578813 1047775 := bstep (se 1 (by rfl) ⟨785831, by rfl⟩ : syracuseStep 1047775 = 1571663) B1571663
theorem B4193633 : Blo 578813 4193633 := bstep (se 2 (by rfl) ⟨1572612, by rfl⟩ : syracuseStep 4193633 = 3145225) B3145225
theorem B1310183 : Blo 578813 1310183 := bstep (se 1 (by rfl) ⟨982637, by rfl⟩ : syracuseStep 1310183 = 1965275) B1965275
theorem B982523 : Blo 578813 982523 := bstep (se 1 (by rfl) ⟨736892, by rfl⟩ : syracuseStep 982523 = 1473785) B1473785
theorem B2358791 : Blo 578813 2358791 := bstep (se 1 (by rfl) ⟨1769093, by rfl⟩ : syracuseStep 2358791 = 3538187) B3538187
theorem B1474139 : Blo 578813 1474139 := bstep (se 1 (by rfl) ⟨1105604, by rfl⟩ : syracuseStep 1474139 = 2211209) B2211209
theorem B1965815 : Blo 578813 1965815 := bstep (se 1 (by rfl) ⟨1474361, by rfl⟩ : syracuseStep 1965815 = 2948723) B2948723
theorem B1113979 : Blo 578813 1113979 := bstep (se 1 (by rfl) ⟨835484, by rfl⟩ : syracuseStep 1113979 = 1670969) B1670969
theorem B982955 : Blo 578813 982955 := bstep (se 1 (by rfl) ⟨737216, by rfl⟩ : syracuseStep 982955 = 1474433) B1474433
theorem B655663 : Blo 578813 655663 := bstep (se 1 (by rfl) ⟨491747, by rfl⟩ : syracuseStep 655663 = 983495) B983495
theorem B1966463 : Blo 578813 1966463 := bstep (se 1 (by rfl) ⟨1474847, by rfl⟩ : syracuseStep 1966463 = 2949695) B2949695
theorem B1311263 : Blo 578813 1311263 := bstep (se 1 (by rfl) ⟨983447, by rfl⟩ : syracuseStep 1311263 = 1966895) B1966895
theorem B9405193 : Blo 578813 9405193 := bstep (se 2 (by rfl) ⟨3526947, by rfl⟩ : syracuseStep 9405193 = 7053895) B7053895
theorem B10585079 : Blo 578813 10585079 := bstep (se 1 (by rfl) ⟨7938809, by rfl⟩ : syracuseStep 10585079 = 15877619) B15877619
theorem B3311279 : Blo 578813 3311279 := bstep (se 1 (by rfl) ⟨2483459, by rfl⟩ : syracuseStep 3311279 = 4966919) B4966919
theorem B4720691 : Blo 578813 4720691 := bstep (se 1 (by rfl) ⟨3540518, by rfl⟩ : syracuseStep 4720691 = 7081037) B7081037
theorem B90540109 : Blo 578813 90540109 := bstep (se 3 (by rfl) ⟨16976270, by rfl⟩ : syracuseStep 90540109 = 33952541) B33952541
theorem B17860819 : Blo 578813 17860819 := bstep (se 1 (by rfl) ⟨13395614, by rfl⟩ : syracuseStep 17860819 = 26791229) B26791229
theorem B3967321 : Blo 578813 3967321 := bstep (se 2 (by rfl) ⟨1487745, by rfl⟩ : syracuseStep 3967321 = 2975491) B2975491
theorem B1771903 : Blo 578813 1771903 := bstep (se 1 (by rfl) ⟨1328927, by rfl⟩ : syracuseStep 1771903 = 2657855) B2657855
theorem B11504339 : Blo 578813 11504339 := bstep (se 1 (by rfl) ⟨8628254, by rfl⟩ : syracuseStep 11504339 = 17256509) B17256509
theorem B6261563 : Blo 578813 6261563 := bstep (se 1 (by rfl) ⟨4696172, by rfl⟩ : syracuseStep 6261563 = 9392345) B9392345
theorem B2788415 : Blo 578813 2788415 := bstep (se 1 (by rfl) ⟨2091311, by rfl⟩ : syracuseStep 2788415 = 4182623) B4182623
theorem B4395383 : Blo 578813 4395383 := bstep (se 1 (by rfl) ⟨3296537, by rfl⟩ : syracuseStep 4395383 = 6593075) B6593075
theorem B42374117 : Blo 578813 42374117 := bstep (se 4 (by rfl) ⟨3972573, by rfl⟩ : syracuseStep 42374117 = 7945147) B7945147
theorem B2200715 : Blo 578813 2200715 := bstep (se 1 (by rfl) ⟨1650536, by rfl⟩ : syracuseStep 2200715 = 3301073) B3301073
theorem B353277251 : Blo 578813 353277251 := bstep (se 1 (by rfl) ⟨264957938, by rfl⟩ : syracuseStep 353277251 = 529915877) B529915877
theorem B2823599 : Blo 578813 2823599 := bstep (se 1 (by rfl) ⟨2117699, by rfl⟩ : syracuseStep 2823599 = 4235399) B4235399
theorem B18847475 : Blo 578813 18847475 := bstep (se 1 (by rfl) ⟨14135606, by rfl⟩ : syracuseStep 18847475 = 28271213) B28271213
theorem B5085149 : Blo 578813 5085149 := bstep (se 3 (by rfl) ⟨953465, by rfl⟩ : syracuseStep 5085149 = 1906931) B1906931
theorem B2791529 : Blo 578813 2791529 := bstep (se 2 (by rfl) ⟨1046823, by rfl⟩ : syracuseStep 2791529 = 2093647) B2093647
theorem B4397327 : Blo 578813 4397327 := bstep (se 1 (by rfl) ⟨3297995, by rfl⟩ : syracuseStep 4397327 = 6595991) B6595991
theorem B2201975 : Blo 578813 2201975 := bstep (se 1 (by rfl) ⟨1651481, by rfl⟩ : syracuseStep 2201975 = 3302963) B3302963
theorem B5282171 : Blo 578813 5282171 := bstep (se 1 (by rfl) ⟨3961628, by rfl⟩ : syracuseStep 5282171 = 7923257) B7923257
theorem B2202491 : Blo 578813 2202491 := bstep (se 1 (by rfl) ⟨1651868, by rfl⟩ : syracuseStep 2202491 = 3303737) B3303737
theorem B4398299 : Blo 578813 4398299 := bstep (se 1 (by rfl) ⟨3298724, by rfl⟩ : syracuseStep 4398299 = 6597449) B6597449
theorem B8822465 : Blo 578813 8822465 := bstep (se 2 (by rfl) ⟨3308424, by rfl⟩ : syracuseStep 8822465 = 6616849) B6616849
theorem B2793449 : Blo 578813 2793449 := bstep (se 2 (by rfl) ⟨1047543, by rfl⟩ : syracuseStep 2793449 = 2095087) B2095087
theorem B4956835 : Blo 578813 4956835 := bstep (se 1 (by rfl) ⟨3717626, by rfl⟩ : syracuseStep 4956835 = 7435253) B7435253
theorem B11183021 : Blo 578813 11183021 := bstep (se 3 (by rfl) ⟨2096816, by rfl⟩ : syracuseStep 11183021 = 4193633) B4193633
theorem B828463 : Blo 578813 828463 := bstep (se 1 (by rfl) ⟨621347, by rfl⟩ : syracuseStep 828463 = 1242695) B1242695
theorem B4760711 : Blo 578813 4760711 := bstep (se 1 (by rfl) ⟨3570533, by rfl⟩ : syracuseStep 4760711 = 7141067) B7141067
theorem B2795123 : Blo 578813 2795123 := bstep (se 1 (by rfl) ⟨2096342, by rfl⟩ : syracuseStep 2795123 = 4192685) B4192685
theorem B2795219 : Blo 578813 2795219 := bstep (se 1 (by rfl) ⟨2096414, by rfl⟩ : syracuseStep 2795219 = 4192829) B4192829
theorem B2205407 : Blo 578813 2205407 := bstep (se 1 (by rfl) ⟨1654055, by rfl⟩ : syracuseStep 2205407 = 3308111) B3308111
theorem B3352603 : Blo 578813 3352603 := bstep (se 1 (by rfl) ⟨2514452, by rfl⟩ : syracuseStep 3352603 = 5028905) B5028905
theorem B1485305 : Blo 578813 1485305 := bstep (se 2 (by rfl) ⟨556989, by rfl⟩ : syracuseStep 1485305 = 1113979) B1113979
theorem B4401701 : Blo 578813 4401701 := bstep (se 4 (by rfl) ⟨412659, by rfl⟩ : syracuseStep 4401701 = 825319) B825319
theorem B1321529 : Blo 578813 1321529 := bstep (se 2 (by rfl) ⟨495573, by rfl⟩ : syracuseStep 1321529 = 991147) B991147
theorem B2206379 : Blo 578813 2206379 := bstep (se 1 (by rfl) ⟨1654784, by rfl⟩ : syracuseStep 2206379 = 3309569) B3309569
theorem B22686799 : Blo 578813 22686799 := bstep (se 1 (by rfl) ⟨17015099, by rfl⟩ : syracuseStep 22686799 = 34030199) B34030199
theorem B4829053 : Blo 578813 4829053 := bstep (se 3 (by rfl) ⟨905447, by rfl⟩ : syracuseStep 4829053 = 1810895) B1810895
theorem B2208019 : Blo 578813 2208019 := bstep (se 1 (by rfl) ⟨1656014, by rfl⟩ : syracuseStep 2208019 = 3312029) B3312029
theorem B36352817 : Blo 578813 36352817 := bstep (se 2 (by rfl) ⟨13632306, by rfl⟩ : syracuseStep 36352817 = 27264613) B27264613
theorem B2208809 : Blo 578813 2208809 := bstep (se 2 (by rfl) ⟨828303, by rfl⟩ : syracuseStep 2208809 = 1656607) B1656607
theorem B2798813 : Blo 578813 2798813 := bstep (se 3 (by rfl) ⟨524777, by rfl⟩ : syracuseStep 2798813 = 1049555) B1049555
theorem B2209751 : Blo 578813 2209751 := bstep (se 1 (by rfl) ⟨1657313, by rfl⟩ : syracuseStep 2209751 = 3314627) B3314627
theorem B2799755 : Blo 578813 2799755 := bstep (se 1 (by rfl) ⟨2099816, by rfl⟩ : syracuseStep 2799755 = 4199633) B4199633
theorem B5585051 : Blo 578813 5585051 := bstep (se 1 (by rfl) ⟨4188788, by rfl⟩ : syracuseStep 5585051 = 8377577) B8377577
theorem B12598199 : Blo 578813 12598199 := bstep (se 1 (by rfl) ⟨9448649, by rfl⟩ : syracuseStep 12598199 = 18897299) B18897299
theorem B1653851 : Blo 578813 1653851 := bstep (se 1 (by rfl) ⟨1240388, by rfl⟩ : syracuseStep 1653851 = 2480777) B2480777
theorem B2210921 : Blo 578813 2210921 := bstep (se 2 (by rfl) ⟨829095, by rfl⟩ : syracuseStep 2210921 = 1658191) B1658191
theorem B1326887 : Blo 578813 1326887 := bstep (se 1 (by rfl) ⟨995165, by rfl⟩ : syracuseStep 1326887 = 1990331) B1990331
theorem B31768361 : Blo 578813 31768361 := bstep (se 2 (by rfl) ⟨11913135, by rfl⟩ : syracuseStep 31768361 = 23826271) B23826271
theorem B6635357 : Blo 578813 6635357 := bstep (se 3 (by rfl) ⟨1244129, by rfl⟩ : syracuseStep 6635357 = 2488259) B2488259
theorem B2834297 : Blo 578813 2834297 := bstep (se 2 (by rfl) ⟨1062861, by rfl⟩ : syracuseStep 2834297 = 2125723) B2125723
theorem B737191 : Blo 578813 737191 := bstep (se 1 (by rfl) ⟨552893, by rfl⟩ : syracuseStep 737191 = 1105787) B1105787
theorem B868295 : Blo 578813 868295 := bstep (se 1 (by rfl) ⟨651221, by rfl⟩ : syracuseStep 868295 = 1302443) B1302443
theorem B1654739 : Blo 578813 1654739 := bstep (se 1 (by rfl) ⟨1241054, by rfl⟩ : syracuseStep 1654739 = 2482109) B2482109
theorem B737515 : Blo 578813 737515 := bstep (se 1 (by rfl) ⟨553136, by rfl⟩ : syracuseStep 737515 = 1106273) B1106273
theorem B3522809 : Blo 578813 3522809 := bstep (se 2 (by rfl) ⟨1321053, by rfl⟩ : syracuseStep 3522809 = 2642107) B2642107
theorem B868655 : Blo 578813 868655 := bstep (se 1 (by rfl) ⟨651491, by rfl⟩ : syracuseStep 868655 = 1302983) B1302983
theorem B3719677 : Blo 578813 3719677 := bstep (se 3 (by rfl) ⟨697439, by rfl⟩ : syracuseStep 3719677 = 1394879) B1394879
theorem B868895 : Blo 578813 868895 := bstep (se 1 (by rfl) ⟨651671, by rfl⟩ : syracuseStep 868895 = 1303343) B1303343
theorem B8929925 : Blo 578813 8929925 := bstep (se 4 (by rfl) ⟨837180, by rfl⟩ : syracuseStep 8929925 = 1674361) B1674361
theorem B869567 : Blo 578813 869567 := bstep (se 1 (by rfl) ⟨652175, by rfl⟩ : syracuseStep 869567 = 1304351) B1304351
theorem B869711 : Blo 578813 869711 := bstep (se 1 (by rfl) ⟨652283, by rfl⟩ : syracuseStep 869711 = 1304567) B1304567
theorem B869801 : Blo 578813 869801 := bstep (se 2 (by rfl) ⟨326175, by rfl⟩ : syracuseStep 869801 = 652351) B652351
theorem B4474295 : Blo 578813 4474295 := bstep (se 1 (by rfl) ⟨3355721, by rfl⟩ : syracuseStep 4474295 = 6711443) B6711443
theorem B869951 : Blo 578813 869951 := bstep (se 1 (by rfl) ⟨652463, by rfl⟩ : syracuseStep 869951 = 1304927) B1304927
theorem B869993 : Blo 578813 869993 := bstep (se 2 (by rfl) ⟨326247, by rfl⟩ : syracuseStep 869993 = 652495) B652495
theorem B3360599 : Blo 578813 3360599 := bstep (se 1 (by rfl) ⟨2520449, by rfl⟩ : syracuseStep 3360599 = 5040899) B5040899
theorem B870431 : Blo 578813 870431 := bstep (se 1 (by rfl) ⟨652823, by rfl⟩ : syracuseStep 870431 = 1305647) B1305647
theorem B870623 : Blo 578813 870623 := bstep (se 1 (by rfl) ⟨652967, by rfl⟩ : syracuseStep 870623 = 1305935) B1305935
theorem B870683 : Blo 578813 870683 := bstep (se 1 (by rfl) ⟨653012, by rfl⟩ : syracuseStep 870683 = 1306025) B1306025
theorem B871007 : Blo 578813 871007 := bstep (se 1 (by rfl) ⟨653255, by rfl⟩ : syracuseStep 871007 = 1306511) B1306511
theorem B871289 : Blo 578813 871289 := bstep (se 2 (by rfl) ⟨326733, by rfl⟩ : syracuseStep 871289 = 653467) B653467
theorem B871337 : Blo 578813 871337 := bstep (se 2 (by rfl) ⟨326751, by rfl⟩ : syracuseStep 871337 = 653503) B653503
theorem B2477051 : Blo 578813 2477051 := bstep (se 1 (by rfl) ⟨1857788, by rfl⟩ : syracuseStep 2477051 = 3715577) B3715577
theorem B871487 : Blo 578813 871487 := bstep (se 1 (by rfl) ⟨653615, by rfl⟩ : syracuseStep 871487 = 1307231) B1307231
theorem B4967567 : Blo 578813 4967567 := bstep (se 1 (by rfl) ⟨3725675, by rfl⟩ : syracuseStep 4967567 = 7451351) B7451351
theorem B872039 : Blo 578813 872039 := bstep (se 1 (by rfl) ⟨654029, by rfl⟩ : syracuseStep 872039 = 1308059) B1308059
theorem B3297131 : Blo 578813 3297131 := bstep (se 1 (by rfl) ⟨2472848, by rfl⟩ : syracuseStep 3297131 = 4945697) B4945697
theorem B872423 : Blo 578813 872423 := bstep (se 1 (by rfl) ⟨654317, by rfl⟩ : syracuseStep 872423 = 1308635) B1308635
theorem B872543 : Blo 578813 872543 := bstep (se 1 (by rfl) ⟨654407, by rfl⟩ : syracuseStep 872543 = 1308815) B1308815
theorem B872555 : Blo 578813 872555 := bstep (se 1 (by rfl) ⟨654416, by rfl⟩ : syracuseStep 872555 = 1308833) B1308833
theorem B872603 : Blo 578813 872603 := bstep (se 1 (by rfl) ⟨654452, by rfl⟩ : syracuseStep 872603 = 1308905) B1308905
theorem B1397033 : Blo 578813 1397033 := bstep (se 2 (by rfl) ⟨523887, by rfl⟩ : syracuseStep 1397033 = 1047775) B1047775
theorem B1855867 : Blo 578813 1855867 := bstep (se 1 (by rfl) ⟨1391900, by rfl⟩ : syracuseStep 1855867 = 2783801) B2783801
theorem B873455 : Blo 578813 873455 := bstep (se 1 (by rfl) ⟨655091, by rfl⟩ : syracuseStep 873455 = 1310183) B1310183
theorem B1955069 : Blo 578813 1955069 := bstep (se 3 (by rfl) ⟨366575, by rfl⟩ : syracuseStep 1955069 = 733151) B733151
theorem B578879 : Blo 578813 578879 := bstep (se 1 (by rfl) ⟨434159, by rfl⟩ : syracuseStep 578879 = 868319) B868319
theorem B873839 : Blo 578813 873839 := bstep (se 1 (by rfl) ⟨655379, by rfl⟩ : syracuseStep 873839 = 1310759) B1310759
theorem B4478327 : Blo 578813 4478327 := bstep (se 1 (by rfl) ⟨3358745, by rfl⟩ : syracuseStep 4478327 = 6717491) B6717491
theorem B26760577 : Blo 578813 26760577 := bstep (se 2 (by rfl) ⟨10035216, by rfl⟩ : syracuseStep 26760577 = 20070433) B20070433
theorem B13981081 : Blo 578813 13981081 := bstep (se 2 (by rfl) ⟨5242905, by rfl⟩ : syracuseStep 13981081 = 10485811) B10485811
theorem B579047 : Blo 578813 579047 := bstep (se 1 (by rfl) ⟨434285, by rfl⟩ : syracuseStep 579047 = 868571) B868571
theorem B873959 : Blo 578813 873959 := bstep (se 1 (by rfl) ⟨655469, by rfl⟩ : syracuseStep 873959 = 1310939) B1310939
theorem B579055 : Blo 578813 579055 := bstep (se 1 (by rfl) ⟨434291, by rfl⟩ : syracuseStep 579055 = 868583) B868583
theorem B579163 : Blo 578813 579163 := bstep (se 1 (by rfl) ⟨434372, by rfl⟩ : syracuseStep 579163 = 868745) B868745
theorem B5101177 : Blo 578813 5101177 := bstep (se 2 (by rfl) ⟨1912941, by rfl⟩ : syracuseStep 5101177 = 3825883) B3825883
theorem B874121 : Blo 578813 874121 := bstep (se 2 (by rfl) ⟨327795, by rfl⟩ : syracuseStep 874121 = 655591) B655591
theorem B579227 : Blo 578813 579227 := bstep (se 1 (by rfl) ⟨434420, by rfl⟩ : syracuseStep 579227 = 868841) B868841
theorem B874139 : Blo 578813 874139 := bstep (se 1 (by rfl) ⟨655604, by rfl⟩ : syracuseStep 874139 = 1311209) B1311209
theorem B579311 : Blo 578813 579311 := bstep (se 1 (by rfl) ⟨434483, by rfl⟩ : syracuseStep 579311 = 868967) B868967
theorem B579399 : Blo 578813 579399 := bstep (se 1 (by rfl) ⟨434549, by rfl⟩ : syracuseStep 579399 = 869099) B869099
theorem B1103699 : Blo 578813 1103699 := bstep (se 1 (by rfl) ⟨827774, by rfl⟩ : syracuseStep 1103699 = 1655549) B1655549
theorem B579419 : Blo 578813 579419 := bstep (se 1 (by rfl) ⟨434564, by rfl⟩ : syracuseStep 579419 = 869129) B869129
theorem B579487 : Blo 578813 579487 := bstep (se 1 (by rfl) ⟨434615, by rfl⟩ : syracuseStep 579487 = 869231) B869231
theorem B1955879 : Blo 578813 1955879 := bstep (se 1 (by rfl) ⟨1466909, by rfl⟩ : syracuseStep 1955879 = 2933819) B2933819
theorem B579655 : Blo 578813 579655 := bstep (se 1 (by rfl) ⟨434741, by rfl⟩ : syracuseStep 579655 = 869483) B869483
theorem B2676833 : Blo 578813 2676833 := bstep (se 2 (by rfl) ⟨1003812, by rfl⟩ : syracuseStep 2676833 = 2007625) B2007625
theorem B1955987 : Blo 578813 1955987 := bstep (se 1 (by rfl) ⟨1466990, by rfl⟩ : syracuseStep 1955987 = 2933981) B2933981
theorem B579815 : Blo 578813 579815 := bstep (se 1 (by rfl) ⟨434861, by rfl⟩ : syracuseStep 579815 = 869723) B869723
theorem B1104185 : Blo 578813 1104185 := bstep (se 2 (by rfl) ⟨414069, by rfl⟩ : syracuseStep 1104185 = 828139) B828139
theorem B579999 : Blo 578813 579999 := bstep (se 1 (by rfl) ⟨434999, by rfl⟩ : syracuseStep 579999 = 869999) B869999
theorem B1956257 : Blo 578813 1956257 := bstep (se 2 (by rfl) ⟨733596, by rfl⟩ : syracuseStep 1956257 = 1467193) B1467193
theorem B580047 : Blo 578813 580047 := bstep (se 1 (by rfl) ⟨435035, by rfl⟩ : syracuseStep 580047 = 870071) B870071
theorem B580071 : Blo 578813 580071 := bstep (se 1 (by rfl) ⟨435053, by rfl⟩ : syracuseStep 580071 = 870107) B870107
theorem B580187 : Blo 578813 580187 := bstep (se 1 (by rfl) ⟨435140, by rfl⟩ : syracuseStep 580187 = 870281) B870281
theorem B580255 : Blo 578813 580255 := bstep (se 1 (by rfl) ⟨435191, by rfl⟩ : syracuseStep 580255 = 870383) B870383
theorem B580423 : Blo 578813 580423 := bstep (se 1 (by rfl) ⟨435317, by rfl⟩ : syracuseStep 580423 = 870635) B870635
theorem B1465199 : Blo 578813 1465199 := bstep (se 1 (by rfl) ⟨1098899, by rfl⟩ : syracuseStep 1465199 = 2197799) B2197799
theorem B580463 : Blo 578813 580463 := bstep (se 1 (by rfl) ⟨435347, by rfl⟩ : syracuseStep 580463 = 870695) B870695
theorem B163371919 : Blo 578813 163371919 := bstep (se 1 (by rfl) ⟨122528939, by rfl⟩ : syracuseStep 163371919 = 245057879) B245057879
theorem B580519 : Blo 578813 580519 := bstep (se 1 (by rfl) ⟨435389, by rfl⟩ : syracuseStep 580519 = 870779) B870779
theorem B1956797 : Blo 578813 1956797 := bstep (se 3 (by rfl) ⟨366899, by rfl⟩ : syracuseStep 1956797 = 733799) B733799
theorem B580699 : Blo 578813 580699 := bstep (se 1 (by rfl) ⟨435524, by rfl⟩ : syracuseStep 580699 = 871049) B871049
theorem B580815 : Blo 578813 580815 := bstep (se 1 (by rfl) ⟨435611, by rfl⟩ : syracuseStep 580815 = 871223) B871223
theorem B1105103 : Blo 578813 1105103 := bstep (se 1 (by rfl) ⟨828827, by rfl⟩ : syracuseStep 1105103 = 1657655) B1657655
theorem B580839 : Blo 578813 580839 := bstep (se 1 (by rfl) ⟨435629, by rfl⟩ : syracuseStep 580839 = 871259) B871259
theorem B2940137 : Blo 578813 2940137 := bstep (se 2 (by rfl) ⟨1102551, by rfl⟩ : syracuseStep 2940137 = 2205103) B2205103
theorem B580935 : Blo 578813 580935 := bstep (se 1 (by rfl) ⟨435701, by rfl⟩ : syracuseStep 580935 = 871403) B871403
theorem B581071 : Blo 578813 581071 := bstep (se 1 (by rfl) ⟨435803, by rfl⟩ : syracuseStep 581071 = 871607) B871607
theorem B1465847 : Blo 578813 1465847 := bstep (se 1 (by rfl) ⟨1099385, by rfl⟩ : syracuseStep 1465847 = 2198771) B2198771
theorem B581231 : Blo 578813 581231 := bstep (se 1 (by rfl) ⟨435923, by rfl⟩ : syracuseStep 581231 = 871847) B871847
theorem B1236647 : Blo 578813 1236647 := bstep (se 1 (by rfl) ⟨927485, by rfl⟩ : syracuseStep 1236647 = 1854971) B1854971
theorem B581287 : Blo 578813 581287 := bstep (se 1 (by rfl) ⟨435965, by rfl⟩ : syracuseStep 581287 = 871931) B871931
theorem B581351 : Blo 578813 581351 := bstep (se 1 (by rfl) ⟨436013, by rfl⟩ : syracuseStep 581351 = 872027) B872027
theorem B581407 : Blo 578813 581407 := bstep (se 1 (by rfl) ⟨436055, by rfl⟩ : syracuseStep 581407 = 872111) B872111
theorem B581487 : Blo 578813 581487 := bstep (se 1 (by rfl) ⟨436115, by rfl⟩ : syracuseStep 581487 = 872231) B872231
theorem B581543 : Blo 578813 581543 := bstep (se 1 (by rfl) ⟨436157, by rfl⟩ : syracuseStep 581543 = 872315) B872315
theorem B4972691 : Blo 578813 4972691 := bstep (se 1 (by rfl) ⟨3729518, by rfl⟩ : syracuseStep 4972691 = 7459037) B7459037
theorem B581823 : Blo 578813 581823 := bstep (se 1 (by rfl) ⟨436367, by rfl⟩ : syracuseStep 581823 = 872735) B872735
theorem B5431499 : Blo 578813 5431499 := bstep (se 1 (by rfl) ⟨4073624, by rfl⟩ : syracuseStep 5431499 = 8147249) B8147249
theorem B745679 : Blo 578813 745679 := bstep (se 1 (by rfl) ⟨559259, by rfl⟩ : syracuseStep 745679 = 1118519) B1118519
theorem B581839 : Blo 578813 581839 := bstep (se 1 (by rfl) ⟨436379, by rfl⟩ : syracuseStep 581839 = 872759) B872759
theorem B581887 : Blo 578813 581887 := bstep (se 1 (by rfl) ⟨436415, by rfl⟩ : syracuseStep 581887 = 872831) B872831
theorem B581935 : Blo 578813 581935 := bstep (se 1 (by rfl) ⟨436451, by rfl⟩ : syracuseStep 581935 = 872903) B872903
theorem B1302839 : Blo 578813 1302839 := bstep (se 1 (by rfl) ⟨977129, by rfl⟩ : syracuseStep 1302839 = 1954259) B1954259
theorem B1958201 : Blo 578813 1958201 := bstep (se 2 (by rfl) ⟨734325, by rfl⟩ : syracuseStep 1958201 = 1468651) B1468651
theorem B81420823 : Blo 578813 81420823 := bstep (se 1 (by rfl) ⟨61065617, by rfl⟩ : syracuseStep 81420823 = 122131235) B122131235
theorem B582171 : Blo 578813 582171 := bstep (se 1 (by rfl) ⟨436628, by rfl⟩ : syracuseStep 582171 = 873257) B873257
theorem B582175 : Blo 578813 582175 := bstep (se 1 (by rfl) ⟨436631, by rfl⟩ : syracuseStep 582175 = 873263) B873263
theorem B582255 : Blo 578813 582255 := bstep (se 1 (by rfl) ⟨436691, by rfl⟩ : syracuseStep 582255 = 873383) B873383
theorem B2351783 : Blo 578813 2351783 := bstep (se 1 (by rfl) ⟨1763837, by rfl⟩ : syracuseStep 2351783 = 3527675) B3527675
theorem B582311 : Blo 578813 582311 := bstep (se 1 (by rfl) ⟨436733, by rfl⟩ : syracuseStep 582311 = 873467) B873467
theorem B582351 : Blo 578813 582351 := bstep (se 1 (by rfl) ⟨436763, by rfl⟩ : syracuseStep 582351 = 873527) B873527
theorem B1958687 : Blo 578813 1958687 := bstep (se 1 (by rfl) ⟨1469015, by rfl⟩ : syracuseStep 1958687 = 2938031) B2938031
theorem B582431 : Blo 578813 582431 := bstep (se 1 (by rfl) ⟨436823, by rfl⟩ : syracuseStep 582431 = 873647) B873647
theorem B582703 : Blo 578813 582703 := bstep (se 1 (by rfl) ⟨437027, by rfl⟩ : syracuseStep 582703 = 874055) B874055
theorem B582767 : Blo 578813 582767 := bstep (se 1 (by rfl) ⟨437075, by rfl⟩ : syracuseStep 582767 = 874151) B874151
theorem B1303865 : Blo 578813 1303865 := bstep (se 2 (by rfl) ⟨488949, by rfl⟩ : syracuseStep 1303865 = 977899) B977899
theorem B1304135 : Blo 578813 1304135 := bstep (se 1 (by rfl) ⟨978101, by rfl⟩ : syracuseStep 1304135 = 1956203) B1956203
theorem B1959659 : Blo 578813 1959659 := bstep (se 1 (by rfl) ⟨1469744, by rfl⟩ : syracuseStep 1959659 = 2939489) B2939489
theorem B1304315 : Blo 578813 1304315 := bstep (se 1 (by rfl) ⟨978236, by rfl⟩ : syracuseStep 1304315 = 1956473) B1956473
theorem B4974331 : Blo 578813 4974331 := bstep (se 1 (by rfl) ⟨3730748, by rfl⟩ : syracuseStep 4974331 = 7461497) B7461497
theorem B2713499 : Blo 578813 2713499 := bstep (se 1 (by rfl) ⟨2035124, by rfl⟩ : syracuseStep 2713499 = 4070249) B4070249
theorem B1959929 : Blo 578813 1959929 := bstep (se 2 (by rfl) ⟨734973, by rfl⟩ : syracuseStep 1959929 = 1469947) B1469947
theorem B1304603 : Blo 578813 1304603 := bstep (se 1 (by rfl) ⟨978452, by rfl⟩ : syracuseStep 1304603 = 1956905) B1956905
theorem B2680955 : Blo 578813 2680955 := bstep (se 1 (by rfl) ⟨2010716, by rfl⟩ : syracuseStep 2680955 = 4021433) B4021433
theorem B1861775 : Blo 578813 1861775 := bstep (se 1 (by rfl) ⟨1396331, by rfl⟩ : syracuseStep 1861775 = 2792663) B2792663
theorem B1960199 : Blo 578813 1960199 := bstep (se 1 (by rfl) ⟨1470149, by rfl⟩ : syracuseStep 1960199 = 2940299) B2940299
theorem B3762719 : Blo 578813 3762719 := bstep (se 1 (by rfl) ⟨2822039, by rfl⟩ : syracuseStep 3762719 = 5644079) B5644079
theorem B1468975 : Blo 578813 1468975 := bstep (se 1 (by rfl) ⟨1101731, by rfl⟩ : syracuseStep 1468975 = 2203463) B2203463
theorem B1469623 : Blo 578813 1469623 := bstep (se 1 (by rfl) ⟨1102217, by rfl⟩ : syracuseStep 1469623 = 2204435) B2204435
theorem B978331 : Blo 578813 978331 := bstep (se 1 (by rfl) ⟨733748, by rfl⟩ : syracuseStep 978331 = 1467497) B1467497
theorem B1306079 : Blo 578813 1306079 := bstep (se 1 (by rfl) ⟨979559, by rfl⟩ : syracuseStep 1306079 = 1959119) B1959119
theorem B1306295 : Blo 578813 1306295 := bstep (se 1 (by rfl) ⟨979721, by rfl⟩ : syracuseStep 1306295 = 1959443) B1959443
theorem B3534587 : Blo 578813 3534587 := bstep (se 1 (by rfl) ⟨2650940, by rfl⟩ : syracuseStep 3534587 = 5301881) B5301881
theorem B45412235 : Blo 578813 45412235 := bstep (se 1 (by rfl) ⟨34059176, by rfl⟩ : syracuseStep 45412235 = 68118353) B68118353
theorem B979087 : Blo 578813 979087 := bstep (se 1 (by rfl) ⟨734315, by rfl⟩ : syracuseStep 979087 = 1468631) B1468631
theorem B979303 : Blo 578813 979303 := bstep (se 1 (by rfl) ⟨734477, by rfl⟩ : syracuseStep 979303 = 1468955) B1468955
theorem B1307087 : Blo 578813 1307087 := bstep (se 1 (by rfl) ⟨980315, by rfl⟩ : syracuseStep 1307087 = 1960631) B1960631
theorem B652027 : Blo 578813 652027 := bstep (se 1 (by rfl) ⟨489020, by rfl⟩ : syracuseStep 652027 = 978041) B978041
theorem B434664305 : Blo 578813 434664305 := bstep (se 2 (by rfl) ⟨162999114, by rfl⟩ : syracuseStep 434664305 = 325998229) B325998229
theorem B1700765 : Blo 578813 1700765 := bstep (se 3 (by rfl) ⟨318893, by rfl⟩ : syracuseStep 1700765 = 637787) B637787
theorem B980039 : Blo 578813 980039 := bstep (se 1 (by rfl) ⟨735029, by rfl⟩ : syracuseStep 980039 = 1470059) B1470059
theorem B2946131 : Blo 578813 2946131 := bstep (se 1 (by rfl) ⟨2209598, by rfl⟩ : syracuseStep 2946131 = 4419197) B4419197
theorem B1307753 : Blo 578813 1307753 := bstep (se 2 (by rfl) ⟨490407, by rfl⟩ : syracuseStep 1307753 = 980815) B980815
theorem B652783 : Blo 578813 652783 := bstep (se 1 (by rfl) ⟨489587, by rfl⟩ : syracuseStep 652783 = 979175) B979175
theorem B652891 : Blo 578813 652891 := bstep (se 1 (by rfl) ⟨489668, by rfl⟩ : syracuseStep 652891 = 979337) B979337
theorem B1308383 : Blo 578813 1308383 := bstep (se 1 (by rfl) ⟨981287, by rfl⟩ : syracuseStep 1308383 = 1962575) B1962575
theorem B1570529 : Blo 578813 1570529 := bstep (se 2 (by rfl) ⟨588948, by rfl⟩ : syracuseStep 1570529 = 1177897) B1177897
theorem B653179 : Blo 578813 653179 := bstep (se 1 (by rfl) ⟨489884, by rfl⟩ : syracuseStep 653179 = 979769) B979769
theorem B7272337 : Blo 578813 7272337 := bstep (se 2 (by rfl) ⟨2727126, by rfl⟩ : syracuseStep 7272337 = 5454253) B5454253
theorem B653215 : Blo 578813 653215 := bstep (se 1 (by rfl) ⟨489911, by rfl⟩ : syracuseStep 653215 = 979823) B979823
theorem B1308743 : Blo 578813 1308743 := bstep (se 1 (by rfl) ⟨981557, by rfl⟩ : syracuseStep 1308743 = 1963115) B1963115
theorem B1177903 : Blo 578813 1177903 := bstep (se 1 (by rfl) ⟨883427, by rfl⟩ : syracuseStep 1177903 = 1766855) B1766855
theorem B784847 : Blo 578813 784847 := bstep (se 1 (by rfl) ⟨588635, by rfl⟩ : syracuseStep 784847 = 1177271) B1177271
theorem B1472975 : Blo 578813 1472975 := bstep (se 1 (by rfl) ⟨1104731, by rfl⟩ : syracuseStep 1472975 = 2209463) B2209463
theorem B4422113 : Blo 578813 4422113 := bstep (se 2 (by rfl) ⟨1658292, by rfl⟩ : syracuseStep 4422113 = 3316585) B3316585
theorem B2652763 : Blo 578813 2652763 := bstep (se 1 (by rfl) ⟨1989572, by rfl⟩ : syracuseStep 2652763 = 3979145) B3979145
theorem B1309409 : Blo 578813 1309409 := bstep (se 2 (by rfl) ⟨491028, by rfl⟩ : syracuseStep 1309409 = 982057) B982057
theorem B4717291 : Blo 578813 4717291 := bstep (se 1 (by rfl) ⟨3537968, by rfl⟩ : syracuseStep 4717291 = 7075937) B7075937
theorem B654151 : Blo 578813 654151 := bstep (se 1 (by rfl) ⟨490613, by rfl⟩ : syracuseStep 654151 = 981227) B981227
theorem B1309607 : Blo 578813 1309607 := bstep (se 1 (by rfl) ⟨982205, by rfl⟩ : syracuseStep 1309607 = 1964411) B1964411
theorem B7437257 : Blo 578813 7437257 := bstep (se 2 (by rfl) ⟨2788971, by rfl⟩ : syracuseStep 7437257 = 5577943) B5577943
theorem B1309787 : Blo 578813 1309787 := bstep (se 1 (by rfl) ⟨982340, by rfl⟩ : syracuseStep 1309787 = 1964681) B1964681
theorem B654799 : Blo 578813 654799 := bstep (se 1 (by rfl) ⟨491099, by rfl⟩ : syracuseStep 654799 = 982199) B982199
theorem B1474159 : Blo 578813 1474159 := bstep (se 1 (by rfl) ⟨1105619, by rfl⟩ : syracuseStep 1474159 = 2211239) B2211239
theorem B655015 : Blo 578813 655015 := bstep (se 1 (by rfl) ⟨491261, by rfl⟩ : syracuseStep 655015 = 982523) B982523
theorem B1572527 : Blo 578813 1572527 := bstep (se 1 (by rfl) ⟨1179395, by rfl⟩ : syracuseStep 1572527 = 2358791) B2358791
theorem B982759 : Blo 578813 982759 := bstep (se 1 (by rfl) ⟨737069, by rfl⟩ : syracuseStep 982759 = 1474139) B1474139
theorem B37715705 : Blo 578813 37715705 := bstep (se 2 (by rfl) ⟨14143389, by rfl⟩ : syracuseStep 37715705 = 28286779) B28286779
theorem B982793 : Blo 578813 982793 := bstep (se 2 (by rfl) ⟨368547, by rfl⟩ : syracuseStep 982793 = 737095) B737095
theorem B1310543 : Blo 578813 1310543 := bstep (se 1 (by rfl) ⟨982907, by rfl⟩ : syracuseStep 1310543 = 1965815) B1965815
theorem B655303 : Blo 578813 655303 := bstep (se 1 (by rfl) ⟨491477, by rfl⟩ : syracuseStep 655303 = 982955) B982955
theorem B1310975 : Blo 578813 1310975 := bstep (se 1 (by rfl) ⟨983231, by rfl⟩ : syracuseStep 1310975 = 1966463) B1966463
theorem B983353 : Blo 578813 983353 := bstep (se 2 (by rfl) ⟨368757, by rfl⟩ : syracuseStep 983353 = 737515) B737515
theorem B108561097 : Blo 578813 108561097 := bstep (se 2 (by rfl) ⟨40710411, by rfl⟩ : syracuseStep 108561097 = 81420823) B81420823
theorem B2982863 : Blo 578813 2982863 := bstep (se 1 (by rfl) ⟨2237147, by rfl⟩ : syracuseStep 2982863 = 4474295) B4474295
theorem B7669559 : Blo 578813 7669559 := bstep (se 1 (by rfl) ⟨5752169, by rfl⟩ : syracuseStep 7669559 = 11504339) B11504339
theorem B3311711 : Blo 578813 3311711 := bstep (se 1 (by rfl) ⟨2483783, by rfl⟩ : syracuseStep 3311711 = 4967567) B4967567
theorem B2198087 : Blo 578813 2198087 := bstep (se 1 (by rfl) ⟨1648565, by rfl⟩ : syracuseStep 2198087 = 3297131) B3297131
theorem B120720145 : Blo 578813 120720145 := bstep (se 2 (by rfl) ⟨45270054, by rfl⟩ : syracuseStep 120720145 = 90540109) B90540109
theorem B2362537 : Blo 578813 2362537 := bstep (se 2 (by rfl) ⟨885951, by rfl⟩ : syracuseStep 2362537 = 1771903) B1771903
theorem B28249411 : Blo 578813 28249411 := bstep (se 1 (by rfl) ⟨21187058, by rfl⟩ : syracuseStep 28249411 = 42374117) B42374117
theorem B2985551 : Blo 578813 2985551 := bstep (se 1 (by rfl) ⟨2239163, by rfl⟩ : syracuseStep 2985551 = 4478327) B4478327
theorem B30249065 : Blo 578813 30249065 := bstep (se 2 (by rfl) ⟨11343399, by rfl⟩ : syracuseStep 30249065 = 22686799) B22686799
theorem B824431 : Blo 578813 824431 := bstep (se 1 (by rfl) ⟨618323, by rfl⟩ : syracuseStep 824431 = 1236647) B1236647
theorem B3315127 : Blo 578813 3315127 := bstep (se 1 (by rfl) ⟨2486345, by rfl⟩ : syracuseStep 3315127 = 4972691) B4972691
theorem B12588509 : Blo 578813 12588509 := bstep (se 3 (by rfl) ⟨2360345, by rfl⟩ : syracuseStep 12588509 = 4720691) B4720691
theorem B1808999 : Blo 578813 1808999 := bstep (se 1 (by rfl) ⟨1356749, by rfl⟩ : syracuseStep 1808999 = 2713499) B2713499
theorem B990203 : Blo 578813 990203 := bstep (se 1 (by rfl) ⟨742652, by rfl⟩ : syracuseStep 990203 = 1485305) B1485305
theorem B289776203 : Blo 578813 289776203 := bstep (se 1 (by rfl) ⟨217332152, by rfl⟩ : syracuseStep 289776203 = 434664305) B434664305
theorem B8398799 : Blo 578813 8398799 := bstep (se 1 (by rfl) ⟨6299099, by rfl⟩ : syracuseStep 8398799 = 12598199) B12598199
theorem B4958171 : Blo 578813 4958171 := bstep (se 1 (by rfl) ⟨3718628, by rfl⟩ : syracuseStep 4958171 = 7437257) B7437257
theorem B54241589 : Blo 578813 54241589 := bstep (se 5 (by rfl) ⟨2542574, by rfl⟩ : syracuseStep 54241589 = 5085149) B5085149
theorem B25143803 : Blo 578813 25143803 := bstep (se 1 (by rfl) ⟨18857852, by rfl⟩ : syracuseStep 25143803 = 37715705) B37715705
theorem B21178907 : Blo 578813 21178907 := bstep (se 1 (by rfl) ⟨15884180, by rfl⟩ : syracuseStep 21178907 = 31768361) B31768361
theorem B7056719 : Blo 578813 7056719 := bstep (se 1 (by rfl) ⟨5292539, by rfl⟩ : syracuseStep 7056719 = 10585079) B10585079
theorem B4959569 : Blo 578813 4959569 := bstep (se 2 (by rfl) ⟨1859838, by rfl⟩ : syracuseStep 4959569 = 3719677) B3719677
theorem B2207519 : Blo 578813 2207519 := bstep (se 1 (by rfl) ⟨1655639, by rfl⟩ : syracuseStep 2207519 = 3311279) B3311279
theorem B2240399 : Blo 578813 2240399 := bstep (se 1 (by rfl) ⟨1680299, by rfl⟩ : syracuseStep 2240399 = 3360599) B3360599
theorem B4174375 : Blo 578813 4174375 := bstep (se 1 (by rfl) ⟨3130781, by rfl⟩ : syracuseStep 4174375 = 6261563) B6261563
theorem B1651367 : Blo 578813 1651367 := bstep (se 1 (by rfl) ⟨1238525, by rfl⟩ : syracuseStep 1651367 = 2477051) B2477051
theorem B6632441 : Blo 578813 6632441 := bstep (se 2 (by rfl) ⟨2487165, by rfl⟩ : syracuseStep 6632441 = 4974331) B4974331
theorem B4470137 : Blo 578813 4470137 := bstep (se 2 (by rfl) ⟨1676301, by rfl⟩ : syracuseStep 4470137 = 3352603) B3352603
theorem B931355 : Blo 578813 931355 := bstep (se 1 (by rfl) ⟨698516, by rfl⟩ : syracuseStep 931355 = 1397033) B1397033
theorem B2930255 : Blo 578813 2930255 := bstep (se 1 (by rfl) ⟨2197691, by rfl⟩ : syracuseStep 2930255 = 4395383) B4395383
theorem B5289761 : Blo 578813 5289761 := bstep (se 2 (by rfl) ⟨1983660, by rfl⟩ : syracuseStep 5289761 = 3967321) B3967321
theorem B235518167 : Blo 578813 235518167 := bstep (se 1 (by rfl) ⟨176638625, by rfl⟩ : syracuseStep 235518167 = 353277251) B353277251
theorem B1882399 : Blo 578813 1882399 := bstep (se 1 (by rfl) ⟨1411799, by rfl⟩ : syracuseStep 1882399 = 2823599) B2823599
theorem B12564983 : Blo 578813 12564983 := bstep (se 1 (by rfl) ⟨9423737, by rfl⟩ : syracuseStep 12564983 = 18847475) B18847475
theorem B735799 : Blo 578813 735799 := bstep (se 1 (by rfl) ⟨551849, by rfl⟩ : syracuseStep 735799 = 1103699) B1103699
theorem B1784555 : Blo 578813 1784555 := bstep (se 1 (by rfl) ⟨1338416, by rfl⟩ : syracuseStep 1784555 = 2676833) B2676833
theorem B2931551 : Blo 578813 2931551 := bstep (se 1 (by rfl) ⟨2198663, by rfl⟩ : syracuseStep 2931551 = 4397327) B4397327
theorem B736123 : Blo 578813 736123 := bstep (se 1 (by rfl) ⟨552092, by rfl⟩ : syracuseStep 736123 = 1104185) B1104185
theorem B3521447 : Blo 578813 3521447 := bstep (se 1 (by rfl) ⟨2641085, by rfl⟩ : syracuseStep 3521447 = 5282171) B5282171
theorem B2932199 : Blo 578813 2932199 := bstep (se 1 (by rfl) ⟨2199149, by rfl⟩ : syracuseStep 2932199 = 4398299) B4398299
theorem B5881643 : Blo 578813 5881643 := bstep (se 1 (by rfl) ⟨4411232, by rfl⟩ : syracuseStep 5881643 = 8822465) B8822465
theorem B6438737 : Blo 578813 6438737 := bstep (se 2 (by rfl) ⟨2414526, by rfl⟩ : syracuseStep 6438737 = 4829053) B4829053
theorem B3620999 : Blo 578813 3620999 := bstep (se 1 (by rfl) ⟨2715749, by rfl⟩ : syracuseStep 3620999 = 5431499) B5431499
theorem B868559 : Blo 578813 868559 := bstep (se 1 (by rfl) ⟨651419, by rfl⟩ : syracuseStep 868559 = 1302839) B1302839
theorem B14893469 : Blo 578813 14893469 := bstep (se 3 (by rfl) ⟨2792525, by rfl⟩ : syracuseStep 14893469 = 5585051) B5585051
theorem B2474489 : Blo 578813 2474489 := bstep (se 2 (by rfl) ⟨927933, by rfl⟩ : syracuseStep 2474489 = 1855867) B1855867
theorem B7455347 : Blo 578813 7455347 := bstep (se 1 (by rfl) ⟨5591510, by rfl⟩ : syracuseStep 7455347 = 11183021) B11183021
theorem B869243 : Blo 578813 869243 := bstep (se 1 (by rfl) ⟨651932, by rfl⟩ : syracuseStep 869243 = 1303865) B1303865
theorem B869369 : Blo 578813 869369 := bstep (se 2 (by rfl) ⟨326013, by rfl⟩ : syracuseStep 869369 = 652027) B652027
theorem B869423 : Blo 578813 869423 := bstep (se 1 (by rfl) ⟨652067, by rfl⟩ : syracuseStep 869423 = 1304135) B1304135
theorem B869543 : Blo 578813 869543 := bstep (se 1 (by rfl) ⟨652157, by rfl⟩ : syracuseStep 869543 = 1304315) B1304315
theorem B869735 : Blo 578813 869735 := bstep (se 1 (by rfl) ⟨652301, by rfl⟩ : syracuseStep 869735 = 1304603) B1304603
theorem B1787303 : Blo 578813 1787303 := bstep (se 1 (by rfl) ⟨1340477, by rfl⟩ : syracuseStep 1787303 = 2680955) B2680955
theorem B3524077 : Blo 578813 3524077 := bstep (se 3 (by rfl) ⟨660764, by rfl⟩ : syracuseStep 3524077 = 1321529) B1321529
theorem B2508479 : Blo 578813 2508479 := bstep (se 1 (by rfl) ⟨1881359, by rfl⟩ : syracuseStep 2508479 = 3762719) B3762719
theorem B2934467 : Blo 578813 2934467 := bstep (se 1 (by rfl) ⟨2200850, by rfl⟩ : syracuseStep 2934467 = 4401701) B4401701
theorem B870377 : Blo 578813 870377 := bstep (se 2 (by rfl) ⟨326391, by rfl⟩ : syracuseStep 870377 = 652783) B652783
theorem B870521 : Blo 578813 870521 := bstep (se 2 (by rfl) ⟨326445, by rfl⟩ : syracuseStep 870521 = 652891) B652891
theorem B6801569 : Blo 578813 6801569 := bstep (se 2 (by rfl) ⟨2550588, by rfl⟩ : syracuseStep 6801569 = 5101177) B5101177
theorem B870719 : Blo 578813 870719 := bstep (se 1 (by rfl) ⟨653039, by rfl⟩ : syracuseStep 870719 = 1306079) B1306079
theorem B870863 : Blo 578813 870863 := bstep (se 1 (by rfl) ⟨653147, by rfl⟩ : syracuseStep 870863 = 1306295) B1306295
theorem B870905 : Blo 578813 870905 := bstep (se 2 (by rfl) ⟨326589, by rfl⟩ : syracuseStep 870905 = 653179) B653179
theorem B870953 : Blo 578813 870953 := bstep (se 2 (by rfl) ⟨326607, by rfl⟩ : syracuseStep 870953 = 653215) B653215
theorem B871391 : Blo 578813 871391 := bstep (se 1 (by rfl) ⟨653543, by rfl⟩ : syracuseStep 871391 = 1307087) B1307087
theorem B24235211 : Blo 578813 24235211 := bstep (se 1 (by rfl) ⟨18176408, by rfl⟩ : syracuseStep 24235211 = 36352817) B36352817
theorem B1133843 : Blo 578813 1133843 := bstep (se 1 (by rfl) ⟨850382, by rfl⟩ : syracuseStep 1133843 = 1700765) B1700765
theorem B871835 : Blo 578813 871835 := bstep (se 1 (by rfl) ⟨653876, by rfl⟩ : syracuseStep 871835 = 1307753) B1307753
theorem B872201 : Blo 578813 872201 := bstep (se 2 (by rfl) ⟨327075, by rfl⟩ : syracuseStep 872201 = 654151) B654151
theorem B872255 : Blo 578813 872255 := bstep (se 1 (by rfl) ⟨654191, by rfl⟩ : syracuseStep 872255 = 1308383) B1308383
theorem B217829225 : Blo 578813 217829225 := bstep (se 2 (by rfl) ⟨81685959, by rfl⟩ : syracuseStep 217829225 = 163371919) B163371919
theorem B872495 : Blo 578813 872495 := bstep (se 1 (by rfl) ⟨654371, by rfl⟩ : syracuseStep 872495 = 1308743) B1308743
theorem B872939 : Blo 578813 872939 := bstep (se 1 (by rfl) ⟨654704, by rfl⟩ : syracuseStep 872939 = 1309409) B1309409
theorem B873065 : Blo 578813 873065 := bstep (se 2 (by rfl) ⟨327399, by rfl⟩ : syracuseStep 873065 = 654799) B654799
theorem B873071 : Blo 578813 873071 := bstep (se 1 (by rfl) ⟨654803, by rfl⟩ : syracuseStep 873071 = 1309607) B1309607
theorem B1102567 : Blo 578813 1102567 := bstep (se 1 (by rfl) ⟨826925, by rfl⟩ : syracuseStep 1102567 = 1653851) B1653851
theorem B873191 : Blo 578813 873191 := bstep (se 1 (by rfl) ⟨654893, by rfl⟩ : syracuseStep 873191 = 1309787) B1309787
theorem B873353 : Blo 578813 873353 := bstep (se 2 (by rfl) ⟨327507, by rfl⟩ : syracuseStep 873353 = 655015) B655015
theorem B873695 : Blo 578813 873695 := bstep (se 1 (by rfl) ⟨655271, by rfl⟩ : syracuseStep 873695 = 1310543) B1310543
theorem B1889531 : Blo 578813 1889531 := bstep (se 1 (by rfl) ⟨1417148, by rfl⟩ : syracuseStep 1889531 = 2834297) B2834297
theorem B873737 : Blo 578813 873737 := bstep (se 2 (by rfl) ⟨327651, by rfl⟩ : syracuseStep 873737 = 655303) B655303
theorem B578863 : Blo 578813 578863 := bstep (se 1 (by rfl) ⟨434147, by rfl⟩ : syracuseStep 578863 = 868295) B868295
theorem B1103159 : Blo 578813 1103159 := bstep (se 1 (by rfl) ⟨827369, by rfl⟩ : syracuseStep 1103159 = 1654739) B1654739
theorem B579103 : Blo 578813 579103 := bstep (se 1 (by rfl) ⟨434327, by rfl⟩ : syracuseStep 579103 = 868655) B868655
theorem B579263 : Blo 578813 579263 := bstep (se 1 (by rfl) ⟨434447, by rfl⟩ : syracuseStep 579263 = 868895) B868895
theorem B874175 : Blo 578813 874175 := bstep (se 1 (by rfl) ⟨655631, by rfl⟩ : syracuseStep 874175 = 1311263) B1311263
theorem B874217 : Blo 578813 874217 := bstep (se 2 (by rfl) ⟨327831, by rfl⟩ : syracuseStep 874217 = 655663) B655663
theorem B5953283 : Blo 578813 5953283 := bstep (se 1 (by rfl) ⟨4464962, by rfl⟩ : syracuseStep 5953283 = 8929925) B8929925
theorem B1988477 : Blo 578813 1988477 := bstep (se 3 (by rfl) ⟨372839, by rfl⟩ : syracuseStep 1988477 = 745679) B745679
theorem B9394157 : Blo 578813 9394157 := bstep (se 3 (by rfl) ⟨1761404, by rfl⟩ : syracuseStep 9394157 = 3522809) B3522809
theorem B579711 : Blo 578813 579711 := bstep (se 1 (by rfl) ⟨434783, by rfl⟩ : syracuseStep 579711 = 869567) B869567
theorem B6609113 : Blo 578813 6609113 := bstep (se 2 (by rfl) ⟨2478417, by rfl⟩ : syracuseStep 6609113 = 4956835) B4956835
theorem B579807 : Blo 578813 579807 := bstep (se 1 (by rfl) ⟨434855, by rfl⟩ : syracuseStep 579807 = 869711) B869711
theorem B579867 : Blo 578813 579867 := bstep (se 1 (by rfl) ⟨434900, by rfl⟩ : syracuseStep 579867 = 869801) B869801
theorem B12540257 : Blo 578813 12540257 := bstep (se 2 (by rfl) ⟨4702596, by rfl⟩ : syracuseStep 12540257 = 9405193) B9405193
theorem B579967 : Blo 578813 579967 := bstep (se 1 (by rfl) ⟨434975, by rfl⟩ : syracuseStep 579967 = 869951) B869951
theorem B579995 : Blo 578813 579995 := bstep (se 1 (by rfl) ⟨434996, by rfl⟩ : syracuseStep 579995 = 869993) B869993
theorem B580287 : Blo 578813 580287 := bstep (se 1 (by rfl) ⟨435215, by rfl⟩ : syracuseStep 580287 = 870431) B870431
theorem B1104617 : Blo 578813 1104617 := bstep (se 2 (by rfl) ⟨414231, by rfl⟩ : syracuseStep 1104617 = 828463) B828463
theorem B580415 : Blo 578813 580415 := bstep (se 1 (by rfl) ⟨435311, by rfl⟩ : syracuseStep 580415 = 870623) B870623
theorem B580455 : Blo 578813 580455 := bstep (se 1 (by rfl) ⟨435341, by rfl⟩ : syracuseStep 580455 = 870683) B870683
theorem B580671 : Blo 578813 580671 := bstep (se 1 (by rfl) ⟨435503, by rfl⟩ : syracuseStep 580671 = 871007) B871007
theorem B580859 : Blo 578813 580859 := bstep (se 1 (by rfl) ⟨435644, by rfl⟩ : syracuseStep 580859 = 871289) B871289
theorem B580891 : Blo 578813 580891 := bstep (se 1 (by rfl) ⟨435668, by rfl⟩ : syracuseStep 580891 = 871337) B871337
theorem B1858943 : Blo 578813 1858943 := bstep (se 1 (by rfl) ⟨1394207, by rfl⟩ : syracuseStep 1858943 = 2788415) B2788415
theorem B580991 : Blo 578813 580991 := bstep (se 1 (by rfl) ⟨435743, by rfl⟩ : syracuseStep 580991 = 871487) B871487
theorem B581359 : Blo 578813 581359 := bstep (se 1 (by rfl) ⟨436019, by rfl⟩ : syracuseStep 581359 = 872039) B872039
theorem B581615 : Blo 578813 581615 := bstep (se 1 (by rfl) ⟨436211, by rfl⟩ : syracuseStep 581615 = 872423) B872423
theorem B581695 : Blo 578813 581695 := bstep (se 1 (by rfl) ⟨436271, by rfl⟩ : syracuseStep 581695 = 872543) B872543
theorem B581703 : Blo 578813 581703 := bstep (se 1 (by rfl) ⟨436277, by rfl⟩ : syracuseStep 581703 = 872555) B872555
theorem B581735 : Blo 578813 581735 := bstep (se 1 (by rfl) ⟨436301, by rfl⟩ : syracuseStep 581735 = 872603) B872603
theorem B23814425 : Blo 578813 23814425 := bstep (se 2 (by rfl) ⟨8930409, by rfl⟩ : syracuseStep 23814425 = 17860819) B17860819
theorem B7463501 : Blo 578813 7463501 := bstep (se 3 (by rfl) ⟨1399406, by rfl⟩ : syracuseStep 7463501 = 2798813) B2798813
theorem B582303 : Blo 578813 582303 := bstep (se 1 (by rfl) ⟨436727, by rfl⟩ : syracuseStep 582303 = 873455) B873455
theorem B1958633 : Blo 578813 1958633 := bstep (se 2 (by rfl) ⟨734487, by rfl⟩ : syracuseStep 1958633 = 1468975) B1468975
theorem B1467143 : Blo 578813 1467143 := bstep (se 1 (by rfl) ⟨1100357, by rfl⟩ : syracuseStep 1467143 = 2200715) B2200715
theorem B1303379 : Blo 578813 1303379 := bstep (se 1 (by rfl) ⟨977534, by rfl⟩ : syracuseStep 1303379 = 1955069) B1955069
theorem B582559 : Blo 578813 582559 := bstep (se 1 (by rfl) ⟨436919, by rfl⟩ : syracuseStep 582559 = 873839) B873839
theorem B582639 : Blo 578813 582639 := bstep (se 1 (by rfl) ⟨436979, by rfl⟩ : syracuseStep 582639 = 873959) B873959
theorem B582747 : Blo 578813 582747 := bstep (se 1 (by rfl) ⟨437060, by rfl⟩ : syracuseStep 582747 = 874121) B874121
theorem B582759 : Blo 578813 582759 := bstep (se 1 (by rfl) ⟨437069, by rfl⟩ : syracuseStep 582759 = 874139) B874139
theorem B1303919 : Blo 578813 1303919 := bstep (se 1 (by rfl) ⟨977939, by rfl⟩ : syracuseStep 1303919 = 1955879) B1955879
theorem B1861019 : Blo 578813 1861019 := bstep (se 1 (by rfl) ⟨1395764, by rfl⟩ : syracuseStep 1861019 = 2791529) B2791529
theorem B1303991 : Blo 578813 1303991 := bstep (se 1 (by rfl) ⟨977993, by rfl⟩ : syracuseStep 1303991 = 1955987) B1955987
theorem B1959497 : Blo 578813 1959497 := bstep (se 2 (by rfl) ⟨734811, by rfl⟩ : syracuseStep 1959497 = 1469623) B1469623
theorem B1467983 : Blo 578813 1467983 := bstep (se 1 (by rfl) ⟨1100987, by rfl⟩ : syracuseStep 1467983 = 2201975) B2201975
theorem B1304171 : Blo 578813 1304171 := bstep (se 1 (by rfl) ⟨978128, by rfl⟩ : syracuseStep 1304171 = 1956257) B1956257
theorem B1304441 : Blo 578813 1304441 := bstep (se 2 (by rfl) ⟨489165, by rfl⟩ : syracuseStep 1304441 = 978331) B978331
theorem B976799 : Blo 578813 976799 := bstep (se 1 (by rfl) ⟨732599, by rfl⟩ : syracuseStep 976799 = 1465199) B1465199
theorem B1468327 : Blo 578813 1468327 := bstep (se 1 (by rfl) ⟨1101245, by rfl⟩ : syracuseStep 1468327 = 2202491) B2202491
theorem B1304531 : Blo 578813 1304531 := bstep (se 1 (by rfl) ⟨978398, by rfl⟩ : syracuseStep 1304531 = 1956797) B1956797
theorem B1960091 : Blo 578813 1960091 := bstep (se 1 (by rfl) ⟨1470068, by rfl⟩ : syracuseStep 1960091 = 2940137) B2940137
theorem B977231 : Blo 578813 977231 := bstep (se 1 (by rfl) ⟨732923, by rfl⟩ : syracuseStep 977231 = 1465847) B1465847
theorem B1862299 : Blo 578813 1862299 := bstep (se 1 (by rfl) ⟨1396724, by rfl⟩ : syracuseStep 1862299 = 2793449) B2793449
theorem B1305449 : Blo 578813 1305449 := bstep (se 2 (by rfl) ⟨489543, by rfl⟩ : syracuseStep 1305449 = 979087) B979087
theorem B1305467 : Blo 578813 1305467 := bstep (se 1 (by rfl) ⟨979100, by rfl⟩ : syracuseStep 1305467 = 1958201) B1958201
theorem B2944025 : Blo 578813 2944025 := bstep (se 2 (by rfl) ⟨1104009, by rfl⟩ : syracuseStep 2944025 = 2208019) B2208019
theorem B1567855 : Blo 578813 1567855 := bstep (se 1 (by rfl) ⟨1175891, by rfl⟩ : syracuseStep 1567855 = 2351783) B2351783
theorem B1305737 : Blo 578813 1305737 := bstep (se 2 (by rfl) ⟨489651, by rfl⟩ : syracuseStep 1305737 = 979303) B979303
theorem B1305791 : Blo 578813 1305791 := bstep (se 1 (by rfl) ⟨979343, by rfl⟩ : syracuseStep 1305791 = 1958687) B1958687
theorem B3173807 : Blo 578813 3173807 := bstep (se 1 (by rfl) ⟨2380355, by rfl⟩ : syracuseStep 3173807 = 4760711) B4760711
theorem B1863415 : Blo 578813 1863415 := bstep (se 1 (by rfl) ⟨1397561, by rfl⟩ : syracuseStep 1863415 = 2795123) B2795123
theorem B1863479 : Blo 578813 1863479 := bstep (se 1 (by rfl) ⟨1397609, by rfl⟩ : syracuseStep 1863479 = 2795219) B2795219
theorem B1470271 : Blo 578813 1470271 := bstep (se 1 (by rfl) ⟨1102703, by rfl⟩ : syracuseStep 1470271 = 2205407) B2205407
theorem B1306439 : Blo 578813 1306439 := bstep (se 1 (by rfl) ⟨979829, by rfl⟩ : syracuseStep 1306439 = 1959659) B1959659
theorem B2092925 : Blo 578813 2092925 := bstep (se 3 (by rfl) ⟨392423, by rfl⟩ : syracuseStep 2092925 = 784847) B784847
theorem B1306619 : Blo 578813 1306619 := bstep (se 1 (by rfl) ⟨979964, by rfl⟩ : syracuseStep 1306619 = 1959929) B1959929
theorem B1241183 : Blo 578813 1241183 := bstep (se 1 (by rfl) ⟨930887, by rfl⟩ : syracuseStep 1241183 = 1861775) B1861775
theorem B1306799 : Blo 578813 1306799 := bstep (se 1 (by rfl) ⟨980099, by rfl⟩ : syracuseStep 1306799 = 1960199) B1960199
theorem B1470919 : Blo 578813 1470919 := bstep (se 1 (by rfl) ⟨1103189, by rfl⟩ : syracuseStep 1470919 = 2206379) B2206379
theorem B35680769 : Blo 578813 35680769 := bstep (se 2 (by rfl) ⟨13380288, by rfl⟩ : syracuseStep 35680769 = 26760577) B26760577
theorem B18641441 : Blo 578813 18641441 := bstep (se 2 (by rfl) ⟨6990540, by rfl⟩ : syracuseStep 18641441 = 13981081) B13981081
theorem B2356391 : Blo 578813 2356391 := bstep (se 1 (by rfl) ⟨1767293, by rfl⟩ : syracuseStep 2356391 = 3534587) B3534587
theorem B9696449 : Blo 578813 9696449 := bstep (se 2 (by rfl) ⟨3636168, by rfl⟩ : syracuseStep 9696449 = 7272337) B7272337
theorem B30274823 : Blo 578813 30274823 := bstep (se 1 (by rfl) ⟨22706117, by rfl⟩ : syracuseStep 30274823 = 45412235) B45412235
theorem B1570537 : Blo 578813 1570537 := bstep (se 2 (by rfl) ⟨588951, by rfl⟩ : syracuseStep 1570537 = 1177903) B1177903
theorem B2946941 : Blo 578813 2946941 := bstep (se 3 (by rfl) ⟨552551, by rfl⟩ : syracuseStep 2946941 = 1105103) B1105103
theorem B1472539 : Blo 578813 1472539 := bstep (se 1 (by rfl) ⟨1104404, by rfl⟩ : syracuseStep 1472539 = 2208809) B2208809
theorem B653359 : Blo 578813 653359 := bstep (se 1 (by rfl) ⟨490019, by rfl⟩ : syracuseStep 653359 = 980039) B980039
theorem B1964087 : Blo 578813 1964087 := bstep (se 1 (by rfl) ⟨1473065, by rfl⟩ : syracuseStep 1964087 = 2946131) B2946131
theorem B3537017 : Blo 578813 3537017 := bstep (se 2 (by rfl) ⟨1326381, by rfl⟩ : syracuseStep 3537017 = 2652763) B2652763
theorem B6289721 : Blo 578813 6289721 := bstep (se 2 (by rfl) ⟨2358645, by rfl⟩ : syracuseStep 6289721 = 4717291) B4717291
theorem B1047019 : Blo 578813 1047019 := bstep (se 1 (by rfl) ⟨785264, by rfl⟩ : syracuseStep 1047019 = 1570529) B1570529
theorem B1473167 : Blo 578813 1473167 := bstep (se 1 (by rfl) ⟨1104875, by rfl⟩ : syracuseStep 1473167 = 2209751) B2209751
theorem B1866503 : Blo 578813 1866503 := bstep (se 1 (by rfl) ⟨1399877, by rfl⟩ : syracuseStep 1866503 = 2799755) B2799755
theorem B981983 : Blo 578813 981983 := bstep (se 1 (by rfl) ⟨736487, by rfl⟩ : syracuseStep 981983 = 1472975) B1472975
theorem B2948075 : Blo 578813 2948075 := bstep (se 1 (by rfl) ⟨2211056, by rfl⟩ : syracuseStep 2948075 = 4422113) B4422113
theorem B1473947 : Blo 578813 1473947 := bstep (se 1 (by rfl) ⟨1105460, by rfl⟩ : syracuseStep 1473947 = 2210921) B2210921
theorem B1965545 : Blo 578813 1965545 := bstep (se 2 (by rfl) ⟨737079, by rfl⟩ : syracuseStep 1965545 = 1474159) B1474159
theorem B1310345 : Blo 578813 1310345 := bstep (se 2 (by rfl) ⟨491379, by rfl⟩ : syracuseStep 1310345 = 982759) B982759
theorem B1048351 : Blo 578813 1048351 := bstep (se 1 (by rfl) ⟨786263, by rfl⟩ : syracuseStep 1048351 = 1572527) B1572527
theorem B655195 : Blo 578813 655195 := bstep (se 1 (by rfl) ⟨491396, by rfl⟩ : syracuseStep 655195 = 982793) B982793
theorem B884591 : Blo 578813 884591 := bstep (se 1 (by rfl) ⟨663443, by rfl⟩ : syracuseStep 884591 = 1326887) B1326887
theorem B982921 : Blo 578813 982921 := bstep (se 2 (by rfl) ⟨368595, by rfl⟩ : syracuseStep 982921 = 737191) B737191
theorem B4423571 : Blo 578813 4423571 := bstep (se 1 (by rfl) ⟨3317678, by rfl⟩ : syracuseStep 4423571 = 6635357) B6635357
theorem B3309821 : Blo 578813 3309821 := bstep (se 3 (by rfl) ⟨620591, by rfl⟩ : syracuseStep 3309821 = 1241183) B1241183
theorem B9928979 : Blo 578813 9928979 := bstep (se 1 (by rfl) ⟨7446734, by rfl⟩ : syracuseStep 9928979 = 14893469) B14893469
theorem B1311137 : Blo 578813 1311137 := bstep (se 2 (by rfl) ⟨491676, by rfl⟩ : syracuseStep 1311137 = 983353) B983353
theorem B1672319 : Blo 578813 1672319 := bstep (se 1 (by rfl) ⟨1254239, by rfl⟩ : syracuseStep 1672319 = 2508479) B2508479
theorem B5113039 : Blo 578813 5113039 := bstep (se 1 (by rfl) ⟨3834779, by rfl⟩ : syracuseStep 5113039 = 7669559) B7669559
theorem B25857197 : Blo 578813 25857197 := bstep (se 3 (by rfl) ⟨4848224, by rfl⟩ : syracuseStep 25857197 = 9696449) B9696449
theorem B8392339 : Blo 578813 8392339 := bstep (se 1 (by rfl) ⟨6294254, by rfl⟩ : syracuseStep 8392339 = 12588509) B12588509
theorem B160960193 : Blo 578813 160960193 := bstep (se 2 (by rfl) ⟨60360072, by rfl⟩ : syracuseStep 160960193 = 120720145) B120720145
theorem B3968855 : Blo 578813 3968855 := bstep (se 1 (by rfl) ⟨2976641, by rfl⟩ : syracuseStep 3968855 = 5953283) B5953283
theorem B6262771 : Blo 578813 6262771 := bstep (se 1 (by rfl) ⟨4697078, by rfl⟩ : syracuseStep 6262771 = 9394157) B9394157
theorem B8360171 : Blo 578813 8360171 := bstep (se 1 (by rfl) ⟨6270128, by rfl⟩ : syracuseStep 8360171 = 12540257) B12540257
theorem B8361893 : Blo 578813 8361893 := bstep (se 4 (by rfl) ⟨783927, by rfl⟩ : syracuseStep 8361893 = 1567855) B1567855
theorem B144644237 : Blo 578813 144644237 := bstep (se 3 (by rfl) ⟨27120794, by rfl⟩ : syracuseStep 144644237 = 54241589) B54241589
theorem B12427627 : Blo 578813 12427627 := bstep (se 1 (by rfl) ⟨9320720, by rfl⟩ : syracuseStep 12427627 = 18641441) B18641441
theorem B64627229 : Blo 578813 64627229 := bstep (se 3 (by rfl) ⟨12117605, by rfl⟩ : syracuseStep 64627229 = 24235211) B24235211
theorem B3023581 : Blo 578813 3023581 := bstep (se 3 (by rfl) ⟨566921, by rfl⟩ : syracuseStep 3023581 = 1133843) B1133843
theorem B8463485 : Blo 578813 8463485 := bstep (se 3 (by rfl) ⟨1586903, by rfl⟩ : syracuseStep 8463485 = 3173807) B3173807
theorem B1189703 : Blo 578813 1189703 := bstep (se 1 (by rfl) ⟨892277, by rfl⟩ : syracuseStep 1189703 = 1784555) B1784555
theorem B5581133 : Blo 578813 5581133 := bstep (se 3 (by rfl) ⟨1046462, by rfl⟩ : syracuseStep 5581133 = 2092925) B2092925
theorem B1649659 : Blo 578813 1649659 := bstep (se 1 (by rfl) ⟨1237244, by rfl⟩ : syracuseStep 1649659 = 2474489) B2474489
theorem B144748129 : Blo 578813 144748129 := bstep (se 2 (by rfl) ⟨54280548, by rfl⟩ : syracuseStep 144748129 = 108561097) B108561097
theorem B2207807 : Blo 578813 2207807 := bstep (se 1 (by rfl) ⟨1655855, by rfl⟩ : syracuseStep 2207807 = 3311711) B3311711
theorem B4534379 : Blo 578813 4534379 := bstep (se 1 (by rfl) ⟨3400784, by rfl⟩ : syracuseStep 4534379 = 6801569) B6801569
theorem B4403645 : Blo 578813 4403645 := bstep (se 3 (by rfl) ⟨825683, by rfl⟩ : syracuseStep 4403645 = 1651367) B1651367
theorem B4698769 : Blo 578813 4698769 := bstep (se 2 (by rfl) ⟨1762038, by rfl⟩ : syracuseStep 4698769 = 3524077) B3524077
theorem B20166043 : Blo 578813 20166043 := bstep (se 1 (by rfl) ⟨15124532, by rfl⟩ : syracuseStep 20166043 = 30249065) B30249065
theorem B1259687 : Blo 578813 1259687 := bstep (se 1 (by rfl) ⟨944765, by rfl⟩ : syracuseStep 1259687 = 1889531) B1889531
theorem B4766141 : Blo 578813 4766141 := bstep (se 3 (by rfl) ⟨893651, by rfl⟩ : syracuseStep 4766141 = 1787303) B1787303
theorem B1325651 : Blo 578813 1325651 := bstep (se 1 (by rfl) ⟨994238, by rfl⟩ : syracuseStep 1325651 = 1988477) B1988477
theorem B4406075 : Blo 578813 4406075 := bstep (se 1 (by rfl) ⟨3304556, by rfl⟩ : syracuseStep 4406075 = 6609113) B6609113
theorem B37665881 : Blo 578813 37665881 := bstep (se 2 (by rfl) ⟨14124705, by rfl⟩ : syracuseStep 37665881 = 28249411) B28249411
theorem B15876283 : Blo 578813 15876283 := bstep (se 1 (by rfl) ⟨11907212, by rfl⟩ : syracuseStep 15876283 = 23814425) B23814425
theorem B193184135 : Blo 578813 193184135 := bstep (se 1 (by rfl) ⟨144888101, by rfl⟩ : syracuseStep 193184135 = 289776203) B289776203
theorem B868919 : Blo 578813 868919 := bstep (se 1 (by rfl) ⟨651689, by rfl⟩ : syracuseStep 868919 = 1303379) B1303379
theorem B12600197 : Blo 578813 12600197 := bstep (se 4 (by rfl) ⟨1181268, by rfl⟩ : syracuseStep 12600197 = 2362537) B2362537
theorem B869279 : Blo 578813 869279 := bstep (se 1 (by rfl) ⟨651959, by rfl⟩ : syracuseStep 869279 = 1303919) B1303919
theorem B869327 : Blo 578813 869327 := bstep (se 1 (by rfl) ⟨651995, by rfl⟩ : syracuseStep 869327 = 1303991) B1303991
theorem B869447 : Blo 578813 869447 := bstep (se 1 (by rfl) ⟨652085, by rfl⟩ : syracuseStep 869447 = 1304171) B1304171
theorem B869627 : Blo 578813 869627 := bstep (se 1 (by rfl) ⟨652220, by rfl⟩ : syracuseStep 869627 = 1304441) B1304441
theorem B869687 : Blo 578813 869687 := bstep (se 1 (by rfl) ⟨652265, by rfl⟩ : syracuseStep 869687 = 1304531) B1304531
theorem B1099241 : Blo 578813 1099241 := bstep (se 2 (by rfl) ⟨412215, by rfl⟩ : syracuseStep 1099241 = 824431) B824431
theorem B16762535 : Blo 578813 16762535 := bstep (se 1 (by rfl) ⟨12571901, by rfl⟩ : syracuseStep 16762535 = 25143803) B25143803
theorem B870299 : Blo 578813 870299 := bstep (se 1 (by rfl) ⟨652724, by rfl⟩ : syracuseStep 870299 = 1305449) B1305449
theorem B870311 : Blo 578813 870311 := bstep (se 1 (by rfl) ⟨652733, by rfl⟩ : syracuseStep 870311 = 1305467) B1305467
theorem B870491 : Blo 578813 870491 := bstep (se 1 (by rfl) ⟨652868, by rfl⟩ : syracuseStep 870491 = 1305737) B1305737
theorem B870527 : Blo 578813 870527 := bstep (se 1 (by rfl) ⟨652895, by rfl⟩ : syracuseStep 870527 = 1305791) B1305791
theorem B4704479 : Blo 578813 4704479 := bstep (se 1 (by rfl) ⟨3528359, by rfl⟩ : syracuseStep 4704479 = 7056719) B7056719
theorem B870959 : Blo 578813 870959 := bstep (se 1 (by rfl) ⟨653219, by rfl⟩ : syracuseStep 870959 = 1306439) B1306439
theorem B1493599 : Blo 578813 1493599 := bstep (se 1 (by rfl) ⟨1120199, by rfl⟩ : syracuseStep 1493599 = 2240399) B2240399
theorem B2640541 : Blo 578813 2640541 := bstep (se 3 (by rfl) ⟨495101, by rfl⟩ : syracuseStep 2640541 = 990203) B990203
theorem B871079 : Blo 578813 871079 := bstep (se 1 (by rfl) ⟨653309, by rfl⟩ : syracuseStep 871079 = 1306619) B1306619
theorem B871145 : Blo 578813 871145 := bstep (se 2 (by rfl) ⟨326679, by rfl⟩ : syracuseStep 871145 = 653359) B653359
theorem B871199 : Blo 578813 871199 := bstep (se 1 (by rfl) ⟨653399, by rfl⟩ : syracuseStep 871199 = 1306799) B1306799
theorem B2509865 : Blo 578813 2509865 := bstep (se 2 (by rfl) ⟨941199, by rfl⟩ : syracuseStep 2509865 = 1882399) B1882399
theorem B1396025 : Blo 578813 1396025 := bstep (se 2 (by rfl) ⟨523509, by rfl⟩ : syracuseStep 1396025 = 1047019) B1047019
theorem B1953503 : Blo 578813 1953503 := bstep (se 1 (by rfl) ⟨1465127, by rfl⟩ : syracuseStep 1953503 = 2930255) B2930255
theorem B3526507 : Blo 578813 3526507 := bstep (se 1 (by rfl) ⟨2644880, by rfl⟩ : syracuseStep 3526507 = 5289761) B5289761
theorem B157012111 : Blo 578813 157012111 := bstep (se 1 (by rfl) ⟨117759083, by rfl⟩ : syracuseStep 157012111 = 235518167) B235518167
theorem B8376655 : Blo 578813 8376655 := bstep (se 1 (by rfl) ⟨6282491, by rfl⟩ : syracuseStep 8376655 = 12564983) B12564983
theorem B1954367 : Blo 578813 1954367 := bstep (se 1 (by rfl) ⟨1465775, by rfl⟩ : syracuseStep 1954367 = 2931551) B2931551
theorem B2347631 : Blo 578813 2347631 := bstep (se 1 (by rfl) ⟨1760723, by rfl⟩ : syracuseStep 2347631 = 3521447) B3521447
theorem B1954799 : Blo 578813 1954799 := bstep (se 1 (by rfl) ⟨1466099, by rfl⟩ : syracuseStep 1954799 = 2932199) B2932199
theorem B1397801 : Blo 578813 1397801 := bstep (se 2 (by rfl) ⟨524175, by rfl⟩ : syracuseStep 1397801 = 1048351) B1048351
theorem B873563 : Blo 578813 873563 := bstep (se 1 (by rfl) ⟨655172, by rfl⟩ : syracuseStep 873563 = 1310345) B1310345
theorem B873593 : Blo 578813 873593 := bstep (se 2 (by rfl) ⟨327597, by rfl⟩ : syracuseStep 873593 = 655195) B655195
theorem B3921095 : Blo 578813 3921095 := bstep (se 1 (by rfl) ⟨2940821, by rfl⟩ : syracuseStep 3921095 = 5881643) B5881643
theorem B2413999 : Blo 578813 2413999 := bstep (se 1 (by rfl) ⟨1810499, by rfl⟩ : syracuseStep 2413999 = 3620999) B3620999
theorem B579039 : Blo 578813 579039 := bstep (se 1 (by rfl) ⟨434279, by rfl⟩ : syracuseStep 579039 = 868559) B868559
theorem B873983 : Blo 578813 873983 := bstep (se 1 (by rfl) ⟨655487, by rfl⟩ : syracuseStep 873983 = 1310975) B1310975
theorem B4970231 : Blo 578813 4970231 := bstep (se 1 (by rfl) ⟨3727673, by rfl⟩ : syracuseStep 4970231 = 7455347) B7455347
theorem B579495 : Blo 578813 579495 := bstep (se 1 (by rfl) ⟨434621, by rfl⟩ : syracuseStep 579495 = 869243) B869243
theorem B579579 : Blo 578813 579579 := bstep (se 1 (by rfl) ⟨434684, by rfl⟩ : syracuseStep 579579 = 869369) B869369
theorem B579615 : Blo 578813 579615 := bstep (se 1 (by rfl) ⟨434711, by rfl⟩ : syracuseStep 579615 = 869423) B869423
theorem B579695 : Blo 578813 579695 := bstep (se 1 (by rfl) ⟨434771, by rfl⟩ : syracuseStep 579695 = 869543) B869543
theorem B579823 : Blo 578813 579823 := bstep (se 1 (by rfl) ⟨434867, by rfl⟩ : syracuseStep 579823 = 869735) B869735
theorem B1956311 : Blo 578813 1956311 := bstep (se 1 (by rfl) ⟨1467233, by rfl⟩ : syracuseStep 1956311 = 2934467) B2934467
theorem B580251 : Blo 578813 580251 := bstep (se 1 (by rfl) ⟨435188, by rfl⟩ : syracuseStep 580251 = 870377) B870377
theorem B580347 : Blo 578813 580347 := bstep (se 1 (by rfl) ⟨435260, by rfl⟩ : syracuseStep 580347 = 870521) B870521
theorem B580479 : Blo 578813 580479 := bstep (se 1 (by rfl) ⟨435359, by rfl⟩ : syracuseStep 580479 = 870719) B870719
theorem B580575 : Blo 578813 580575 := bstep (se 1 (by rfl) ⟨435431, by rfl⟩ : syracuseStep 580575 = 870863) B870863
theorem B580603 : Blo 578813 580603 := bstep (se 1 (by rfl) ⟨435452, by rfl⟩ : syracuseStep 580603 = 870905) B870905
theorem B580635 : Blo 578813 580635 := bstep (se 1 (by rfl) ⟨435476, by rfl⟩ : syracuseStep 580635 = 870953) B870953
theorem B1465391 : Blo 578813 1465391 := bstep (se 1 (by rfl) ⟨1099043, by rfl⟩ : syracuseStep 1465391 = 2198087) B2198087
theorem B580927 : Blo 578813 580927 := bstep (se 1 (by rfl) ⟨435695, by rfl⟩ : syracuseStep 580927 = 871391) B871391
theorem B581223 : Blo 578813 581223 := bstep (se 1 (by rfl) ⟨435917, by rfl⟩ : syracuseStep 581223 = 871835) B871835
theorem B1990367 : Blo 578813 1990367 := bstep (se 1 (by rfl) ⟨1492775, by rfl⟩ : syracuseStep 1990367 = 2985551) B2985551
theorem B581467 : Blo 578813 581467 := bstep (se 1 (by rfl) ⟨436100, by rfl⟩ : syracuseStep 581467 = 872201) B872201
theorem B7954301 : Blo 578813 7954301 := bstep (se 3 (by rfl) ⟨1491431, by rfl⟩ : syracuseStep 7954301 = 2982863) B2982863
theorem B581503 : Blo 578813 581503 := bstep (se 1 (by rfl) ⟨436127, by rfl⟩ : syracuseStep 581503 = 872255) B872255
theorem B1957769 : Blo 578813 1957769 := bstep (se 2 (by rfl) ⟨734163, by rfl⟩ : syracuseStep 1957769 = 1468327) B1468327
theorem B145219483 : Blo 578813 145219483 := bstep (se 1 (by rfl) ⟨108914612, by rfl⟩ : syracuseStep 145219483 = 217829225) B217829225
theorem B581663 : Blo 578813 581663 := bstep (se 1 (by rfl) ⟨436247, by rfl⟩ : syracuseStep 581663 = 872495) B872495
theorem B581959 : Blo 578813 581959 := bstep (se 1 (by rfl) ⟨436469, by rfl⟩ : syracuseStep 581959 = 872939) B872939
theorem B582043 : Blo 578813 582043 := bstep (se 1 (by rfl) ⟨436532, by rfl⟩ : syracuseStep 582043 = 873065) B873065
theorem B582047 : Blo 578813 582047 := bstep (se 1 (by rfl) ⟨436535, by rfl⟩ : syracuseStep 582047 = 873071) B873071
theorem B582127 : Blo 578813 582127 := bstep (se 1 (by rfl) ⟨436595, by rfl⟩ : syracuseStep 582127 = 873191) B873191
theorem B582235 : Blo 578813 582235 := bstep (se 1 (by rfl) ⟨436676, by rfl⟩ : syracuseStep 582235 = 873353) B873353
theorem B2941757 : Blo 578813 2941757 := bstep (se 3 (by rfl) ⟨551579, by rfl⟩ : syracuseStep 2941757 = 1103159) B1103159
theorem B582463 : Blo 578813 582463 := bstep (se 1 (by rfl) ⟨436847, by rfl⟩ : syracuseStep 582463 = 873695) B873695
theorem B582491 : Blo 578813 582491 := bstep (se 1 (by rfl) ⟨436868, by rfl⟩ : syracuseStep 582491 = 873737) B873737
theorem B2483065 : Blo 578813 2483065 := bstep (se 2 (by rfl) ⟨931149, by rfl⟩ : syracuseStep 2483065 = 1862299) B1862299
theorem B582783 : Blo 578813 582783 := bstep (se 1 (by rfl) ⟨437087, by rfl⟩ : syracuseStep 582783 = 874175) B874175
theorem B582811 : Blo 578813 582811 := bstep (se 1 (by rfl) ⟨437108, by rfl⟩ : syracuseStep 582811 = 874217) B874217
theorem B1205999 : Blo 578813 1205999 := bstep (se 1 (by rfl) ⟨904499, by rfl⟩ : syracuseStep 1205999 = 1808999) B1808999
theorem B1239295 : Blo 578813 1239295 := bstep (se 1 (by rfl) ⟨929471, by rfl⟩ : syracuseStep 1239295 = 1858943) B1858943
theorem B2484553 : Blo 578813 2484553 := bstep (se 2 (by rfl) ⟨931707, by rfl⟩ : syracuseStep 2484553 = 1863415) B1863415
theorem B1960361 : Blo 578813 1960361 := bstep (se 2 (by rfl) ⟨735135, by rfl⟩ : syracuseStep 1960361 = 1470271) B1470271
theorem B4975667 : Blo 578813 4975667 := bstep (se 1 (by rfl) ⟨3731750, by rfl⟩ : syracuseStep 4975667 = 7463501) B7463501
theorem B1305755 : Blo 578813 1305755 := bstep (se 1 (by rfl) ⟨979316, by rfl⟩ : syracuseStep 1305755 = 1958633) B1958633
theorem B978095 : Blo 578813 978095 := bstep (se 1 (by rfl) ⟨733571, by rfl⟩ : syracuseStep 978095 = 1467143) B1467143
theorem B1961225 : Blo 578813 1961225 := bstep (se 2 (by rfl) ⟨735459, by rfl⟩ : syracuseStep 1961225 = 1470919) B1470919
theorem B5565833 : Blo 578813 5565833 := bstep (se 2 (by rfl) ⟨2087187, by rfl⟩ : syracuseStep 5565833 = 4174375) B4174375
theorem B1240679 : Blo 578813 1240679 := bstep (se 1 (by rfl) ⟨930509, by rfl⟩ : syracuseStep 1240679 = 1861019) B1861019
theorem B1470089 : Blo 578813 1470089 := bstep (se 2 (by rfl) ⟨551283, by rfl⟩ : syracuseStep 1470089 = 1102567) B1102567
theorem B1306331 : Blo 578813 1306331 := bstep (se 1 (by rfl) ⟨979748, by rfl⟩ : syracuseStep 1306331 = 1959497) B1959497
theorem B978655 : Blo 578813 978655 := bstep (se 1 (by rfl) ⟨733991, by rfl⟩ : syracuseStep 978655 = 1467983) B1467983
theorem B651199 : Blo 578813 651199 := bstep (se 1 (by rfl) ⟨488399, by rfl⟩ : syracuseStep 651199 = 976799) B976799
theorem B5599199 : Blo 578813 5599199 := bstep (se 1 (by rfl) ⟨4199399, by rfl⟩ : syracuseStep 5599199 = 8398799) B8398799
theorem B3305447 : Blo 578813 3305447 := bstep (se 1 (by rfl) ⟨2479085, by rfl⟩ : syracuseStep 3305447 = 4958171) B4958171
theorem B1306727 : Blo 578813 1306727 := bstep (se 1 (by rfl) ⟨980045, by rfl⟩ : syracuseStep 1306727 = 1960091) B1960091
theorem B651487 : Blo 578813 651487 := bstep (se 1 (by rfl) ⟨488615, by rfl⟩ : syracuseStep 651487 = 977231) B977231
theorem B14119271 : Blo 578813 14119271 := bstep (se 1 (by rfl) ⟨10589453, by rfl⟩ : syracuseStep 14119271 = 21178907) B21178907
theorem B4420169 : Blo 578813 4420169 := bstep (se 2 (by rfl) ⟨1657563, by rfl⟩ : syracuseStep 4420169 = 3315127) B3315127
theorem B2945645 : Blo 578813 2945645 := bstep (se 3 (by rfl) ⟨552308, by rfl⟩ : syracuseStep 2945645 = 1104617) B1104617
theorem B1962683 : Blo 578813 1962683 := bstep (se 1 (by rfl) ⟨1472012, by rfl⟩ : syracuseStep 1962683 = 2944025) B2944025
theorem B3306379 : Blo 578813 3306379 := bstep (se 1 (by rfl) ⟨2479784, by rfl⟩ : syracuseStep 3306379 = 4959569) B4959569
theorem B2094049 : Blo 578813 2094049 := bstep (se 2 (by rfl) ⟨785268, by rfl⟩ : syracuseStep 2094049 = 1570537) B1570537
theorem B1471679 : Blo 578813 1471679 := bstep (se 1 (by rfl) ⟨1103759, by rfl⟩ : syracuseStep 1471679 = 2207519) B2207519
theorem B1242319 : Blo 578813 1242319 := bstep (se 1 (by rfl) ⟨931739, by rfl⟩ : syracuseStep 1242319 = 1863479) B1863479
theorem B1963385 : Blo 578813 1963385 := bstep (se 2 (by rfl) ⟨736269, by rfl⟩ : syracuseStep 1963385 = 1472539) B1472539
theorem B23787179 : Blo 578813 23787179 := bstep (se 1 (by rfl) ⟨17840384, by rfl⟩ : syracuseStep 23787179 = 35680769) B35680769
theorem B4421627 : Blo 578813 4421627 := bstep (se 1 (by rfl) ⟨3316220, by rfl⟩ : syracuseStep 4421627 = 6632441) B6632441
theorem B981065 : Blo 578813 981065 := bstep (se 2 (by rfl) ⟨367899, by rfl⟩ : syracuseStep 981065 = 735799) B735799
theorem B1570927 : Blo 578813 1570927 := bstep (se 1 (by rfl) ⟨1178195, by rfl⟩ : syracuseStep 1570927 = 2356391) B2356391
theorem B20183215 : Blo 578813 20183215 := bstep (se 1 (by rfl) ⟨15137411, by rfl⟩ : syracuseStep 20183215 = 30274823) B30274823
theorem B2980091 : Blo 578813 2980091 := bstep (se 1 (by rfl) ⟨2235068, by rfl⟩ : syracuseStep 2980091 = 4470137) B4470137
theorem B620903 : Blo 578813 620903 := bstep (se 1 (by rfl) ⟨465677, by rfl⟩ : syracuseStep 620903 = 931355) B931355
theorem B981497 : Blo 578813 981497 := bstep (se 2 (by rfl) ⟨368061, by rfl⟩ : syracuseStep 981497 = 736123) B736123
theorem B1964627 : Blo 578813 1964627 := bstep (se 1 (by rfl) ⟨1473470, by rfl⟩ : syracuseStep 1964627 = 2946941) B2946941
theorem B1309391 : Blo 578813 1309391 := bstep (se 1 (by rfl) ⟨982043, by rfl⟩ : syracuseStep 1309391 = 1964087) B1964087
theorem B2358011 : Blo 578813 2358011 := bstep (se 1 (by rfl) ⟨1768508, by rfl⟩ : syracuseStep 2358011 = 3537017) B3537017
theorem B4193147 : Blo 578813 4193147 := bstep (se 1 (by rfl) ⟨3144860, by rfl⟩ : syracuseStep 4193147 = 6289721) B6289721
theorem B982111 : Blo 578813 982111 := bstep (se 1 (by rfl) ⟨736583, by rfl⟩ : syracuseStep 982111 = 1473167) B1473167
theorem B1244335 : Blo 578813 1244335 := bstep (se 1 (by rfl) ⟨933251, by rfl⟩ : syracuseStep 1244335 = 1866503) B1866503
theorem B654655 : Blo 578813 654655 := bstep (se 1 (by rfl) ⟨490991, by rfl⟩ : syracuseStep 654655 = 981983) B981983
theorem B1965383 : Blo 578813 1965383 := bstep (se 1 (by rfl) ⟨1474037, by rfl⟩ : syracuseStep 1965383 = 2948075) B2948075
theorem B17169965 : Blo 578813 17169965 := bstep (se 3 (by rfl) ⟨3219368, by rfl⟩ : syracuseStep 17169965 = 6438737) B6438737
theorem B982631 : Blo 578813 982631 := bstep (se 1 (by rfl) ⟨736973, by rfl⟩ : syracuseStep 982631 = 1473947) B1473947
theorem B1310363 : Blo 578813 1310363 := bstep (se 1 (by rfl) ⟨982772, by rfl⟩ : syracuseStep 1310363 = 1965545) B1965545
theorem B1310561 : Blo 578813 1310561 := bstep (se 2 (by rfl) ⟨491460, by rfl⟩ : syracuseStep 1310561 = 982921) B982921
theorem B589727 : Blo 578813 589727 := bstep (se 1 (by rfl) ⟨442295, by rfl⟩ : syracuseStep 589727 = 884591) B884591
theorem B2949047 : Blo 578813 2949047 := bstep (se 1 (by rfl) ⟨2211785, by rfl⟩ : syracuseStep 2949047 = 4423571) B4423571
theorem B6619319 : Blo 578813 6619319 := bstep (se 1 (by rfl) ⟨4964489, by rfl⟩ : syracuseStep 6619319 = 9928979) B9928979
theorem B21168377 : Blo 578813 21168377 := bstep (se 2 (by rfl) ⟨7938141, by rfl⟩ : syracuseStep 21168377 = 15876283) B15876283
theorem B1114879 : Blo 578813 1114879 := bstep (se 1 (by rfl) ⟨836159, by rfl⟩ : syracuseStep 1114879 = 1672319) B1672319
theorem B4031441 : Blo 578813 4031441 := bstep (se 2 (by rfl) ⟨1511790, by rfl⟩ : syracuseStep 4031441 = 3023581) B3023581
theorem B11175023 : Blo 578813 11175023 := bstep (se 1 (by rfl) ⟨8381267, by rfl⟩ : syracuseStep 11175023 = 16762535) B16762535
theorem B3310753 : Blo 578813 3310753 := bstep (se 2 (by rfl) ⟨1241532, by rfl⟩ : syracuseStep 3310753 = 2483065) B2483065
theorem B6817385 : Blo 578813 6817385 := bstep (se 2 (by rfl) ⟨2556519, by rfl⟩ : syracuseStep 6817385 = 5113039) B5113039
theorem B1673243 : Blo 578813 1673243 := bstep (se 1 (by rfl) ⟨1254932, by rfl⟩ : syracuseStep 1673243 = 2509865) B2509865
theorem B17238131 : Blo 578813 17238131 := bstep (se 1 (by rfl) ⟨12928598, by rfl⟩ : syracuseStep 17238131 = 25857197) B25857197
theorem B5573447 : Blo 578813 5573447 := bstep (se 1 (by rfl) ⟨4180085, by rfl⟩ : syracuseStep 5573447 = 8360171) B8360171
theorem B3312737 : Blo 578813 3312737 := bstep (se 2 (by rfl) ⟨1242276, by rfl⟩ : syracuseStep 3312737 = 2484553) B2484553
theorem B10456253 : Blo 578813 10456253 := bstep (se 3 (by rfl) ⟨1960547, by rfl⟩ : syracuseStep 10456253 = 3921095) B3921095
theorem B3313487 : Blo 578813 3313487 := bstep (se 1 (by rfl) ⟨2485115, by rfl⟩ : syracuseStep 3313487 = 4970231) B4970231
theorem B5574595 : Blo 578813 5574595 := bstep (se 1 (by rfl) ⟨4180946, by rfl⟩ : syracuseStep 5574595 = 8361893) B8361893
theorem B2199545 : Blo 578813 2199545 := bstep (se 2 (by rfl) ⟨824829, by rfl⟩ : syracuseStep 2199545 = 1649659) B1649659
theorem B6265025 : Blo 578813 6265025 := bstep (se 2 (by rfl) ⟨2349384, by rfl⟩ : syracuseStep 6265025 = 4698769) B4698769
theorem B793135 : Blo 578813 793135 := bstep (se 1 (by rfl) ⟨594851, by rfl⟩ : syracuseStep 793135 = 1189703) B1189703
theorem B2792065 : Blo 578813 2792065 := bstep (se 2 (by rfl) ⟨1047024, by rfl⟩ : syracuseStep 2792065 = 2094049) B2094049
theorem B3218665 : Blo 578813 3218665 := bstep (se 2 (by rfl) ⟨1206999, by rfl⟩ : syracuseStep 3218665 = 2413999) B2413999
theorem B3317111 : Blo 578813 3317111 := bstep (se 1 (by rfl) ⟨2487833, by rfl⟩ : syracuseStep 3317111 = 4975667) B4975667
theorem B3710555 : Blo 578813 3710555 := bstep (se 1 (by rfl) ⟨2782916, by rfl⟩ : syracuseStep 3710555 = 5565833) B5565833
theorem B827119 : Blo 578813 827119 := bstep (se 1 (by rfl) ⟨620339, by rfl⟩ : syracuseStep 827119 = 1240679) B1240679
theorem B2203631 : Blo 578813 2203631 := bstep (se 1 (by rfl) ⟨1652723, by rfl⟩ : syracuseStep 2203631 = 3305447) B3305447
theorem B3022919 : Blo 578813 3022919 := bstep (se 1 (by rfl) ⟨2267189, by rfl⟩ : syracuseStep 3022919 = 4534379) B4534379
theorem B26910953 : Blo 578813 26910953 := bstep (se 2 (by rfl) ⟨10091607, by rfl⟩ : syracuseStep 26910953 = 20183215) B20183215
theorem B9412847 : Blo 578813 9412847 := bstep (se 1 (by rfl) ⟨7059635, by rfl⟩ : syracuseStep 9412847 = 14119271) B14119271
theorem B2795431 : Blo 578813 2795431 := bstep (se 1 (by rfl) ⟨2096573, by rfl⟩ : syracuseStep 2795431 = 4193147) B4193147
theorem B25110587 : Blo 578813 25110587 := bstep (se 1 (by rfl) ⟨18832940, by rfl⟩ : syracuseStep 25110587 = 37665881) B37665881
theorem B11446643 : Blo 578813 11446643 := bstep (se 1 (by rfl) ⟨8584982, by rfl⟩ : syracuseStep 11446643 = 17169965) B17169965
theorem B2206547 : Blo 578813 2206547 := bstep (se 1 (by rfl) ⟨1654910, by rfl⟩ : syracuseStep 2206547 = 3309821) B3309821
theorem B128789423 : Blo 578813 128789423 := bstep (se 1 (by rfl) ⟨96592067, by rfl⟩ : syracuseStep 128789423 = 193184135) B193184135
theorem B8400131 : Blo 578813 8400131 := bstep (se 1 (by rfl) ⟨6300098, by rfl⟩ : syracuseStep 8400131 = 12600197) B12600197
theorem B837397925 : Blo 578813 837397925 := bstep (se 4 (by rfl) ⟨78506055, by rfl⟩ : syracuseStep 837397925 = 157012111) B157012111
theorem B732827 : Blo 578813 732827 := bstep (se 1 (by rfl) ⟨549620, by rfl⟩ : syracuseStep 732827 = 1099241) B1099241
theorem B930683 : Blo 578813 930683 := bstep (se 1 (by rfl) ⟨698012, by rfl⟩ : syracuseStep 930683 = 1396025) B1396025
theorem B1652393 : Blo 578813 1652393 := bstep (se 2 (by rfl) ⟨619647, by rfl⟩ : syracuseStep 1652393 = 1239295) B1239295
theorem B931867 : Blo 578813 931867 := bstep (se 1 (by rfl) ⟨698900, by rfl⟩ : syracuseStep 931867 = 1397801) B1397801
theorem B3520721 : Blo 578813 3520721 := bstep (se 2 (by rfl) ⟨1320270, by rfl⟩ : syracuseStep 3520721 = 2640541) B2640541
theorem B11189785 : Blo 578813 11189785 := bstep (se 2 (by rfl) ⟨4196169, by rfl⟩ : syracuseStep 11189785 = 8392339) B8392339
theorem B4702009 : Blo 578813 4702009 := bstep (se 2 (by rfl) ⟨1763253, by rfl⟩ : syracuseStep 4702009 = 3526507) B3526507
theorem B1326911 : Blo 578813 1326911 := bstep (se 1 (by rfl) ⟨995183, by rfl⟩ : syracuseStep 1326911 = 1990367) B1990367
theorem B868265 : Blo 578813 868265 := bstep (se 2 (by rfl) ⟨325599, by rfl⟩ : syracuseStep 868265 = 651199) B651199
theorem B868649 : Blo 578813 868649 := bstep (se 2 (by rfl) ⟨325743, by rfl⟩ : syracuseStep 868649 = 651487) B651487
theorem B14140277 : Blo 578813 14140277 := bstep (se 5 (by rfl) ⟨662825, by rfl⟩ : syracuseStep 14140277 = 1325651) B1325651
theorem B1655741 : Blo 578813 1655741 := bstep (se 3 (by rfl) ⟨310451, by rfl⟩ : syracuseStep 1655741 = 620903) B620903
theorem B803999 : Blo 578813 803999 := bstep (se 1 (by rfl) ⟨602999, by rfl⟩ : syracuseStep 803999 = 1205999) B1205999
theorem B4408505 : Blo 578813 4408505 := bstep (se 2 (by rfl) ⟨1653189, by rfl⟩ : syracuseStep 4408505 = 3306379) B3306379
theorem B3720755 : Blo 578813 3720755 := bstep (se 1 (by rfl) ⟨2790566, by rfl⟩ : syracuseStep 3720755 = 5581133) B5581133
theorem B1656425 : Blo 578813 1656425 := bstep (se 2 (by rfl) ⟨621159, by rfl⟩ : syracuseStep 1656425 = 1242319) B1242319
theorem B26888057 : Blo 578813 26888057 := bstep (se 2 (by rfl) ⟨10083021, by rfl⟩ : syracuseStep 26888057 = 20166043) B20166043
theorem B870503 : Blo 578813 870503 := bstep (se 1 (by rfl) ⟨652877, by rfl⟩ : syracuseStep 870503 = 1305755) B1305755
theorem B870887 : Blo 578813 870887 := bstep (se 1 (by rfl) ⟨653165, by rfl⟩ : syracuseStep 870887 = 1306331) B1306331
theorem B871151 : Blo 578813 871151 := bstep (se 1 (by rfl) ⟨653363, by rfl⟩ : syracuseStep 871151 = 1306727) B1306727
theorem B2935763 : Blo 578813 2935763 := bstep (se 1 (by rfl) ⟨2201822, by rfl⟩ : syracuseStep 2935763 = 4403645) B4403645
theorem B839791 : Blo 578813 839791 := bstep (se 1 (by rfl) ⟨629843, by rfl⟩ : syracuseStep 839791 = 1259687) B1259687
theorem B1986727 : Blo 578813 1986727 := bstep (se 1 (by rfl) ⟨1490045, by rfl⟩ : syracuseStep 1986727 = 2980091) B2980091
theorem B1659113 : Blo 578813 1659113 := bstep (se 2 (by rfl) ⟨622167, by rfl⟩ : syracuseStep 1659113 = 1244335) B1244335
theorem B872873 : Blo 578813 872873 := bstep (se 2 (by rfl) ⟨327327, by rfl⟩ : syracuseStep 872873 = 654655) B654655
theorem B872927 : Blo 578813 872927 := bstep (se 1 (by rfl) ⟨654695, by rfl⟩ : syracuseStep 872927 = 1309391) B1309391
theorem B2937383 : Blo 578813 2937383 := bstep (se 1 (by rfl) ⟨2203037, by rfl⟩ : syracuseStep 2937383 = 4406075) B4406075
theorem B873575 : Blo 578813 873575 := bstep (se 1 (by rfl) ⟨655181, by rfl⟩ : syracuseStep 873575 = 1310363) B1310363
theorem B873707 : Blo 578813 873707 := bstep (se 1 (by rfl) ⟨655280, by rfl⟩ : syracuseStep 873707 = 1310561) B1310561
theorem B874091 : Blo 578813 874091 := bstep (se 1 (by rfl) ⟨655568, by rfl⟩ : syracuseStep 874091 = 1311137) B1311137
theorem B579279 : Blo 578813 579279 := bstep (se 1 (by rfl) ⟨434459, by rfl⟩ : syracuseStep 579279 = 868919) B868919
theorem B16570169 : Blo 578813 16570169 := bstep (se 2 (by rfl) ⟨6213813, by rfl⟩ : syracuseStep 16570169 = 12427627) B12427627
theorem B579519 : Blo 578813 579519 := bstep (se 1 (by rfl) ⟨434639, by rfl⟩ : syracuseStep 579519 = 869279) B869279
theorem B579551 : Blo 578813 579551 := bstep (se 1 (by rfl) ⟨434663, by rfl⟩ : syracuseStep 579551 = 869327) B869327
theorem B579631 : Blo 578813 579631 := bstep (se 1 (by rfl) ⟨434723, by rfl⟩ : syracuseStep 579631 = 869447) B869447
theorem B579751 : Blo 578813 579751 := bstep (se 1 (by rfl) ⟨434813, by rfl⟩ : syracuseStep 579751 = 869627) B869627
theorem B579791 : Blo 578813 579791 := bstep (se 1 (by rfl) ⟨434843, by rfl⟩ : syracuseStep 579791 = 869687) B869687
theorem B580199 : Blo 578813 580199 := bstep (se 1 (by rfl) ⟨435149, by rfl⟩ : syracuseStep 580199 = 870299) B870299
theorem B580207 : Blo 578813 580207 := bstep (se 1 (by rfl) ⟨435155, by rfl⟩ : syracuseStep 580207 = 870311) B870311
theorem B580327 : Blo 578813 580327 := bstep (se 1 (by rfl) ⟨435245, by rfl⟩ : syracuseStep 580327 = 870491) B870491
theorem B580351 : Blo 578813 580351 := bstep (se 1 (by rfl) ⟨435263, by rfl⟩ : syracuseStep 580351 = 870527) B870527
theorem B3136319 : Blo 578813 3136319 := bstep (se 1 (by rfl) ⟨2352239, by rfl⟩ : syracuseStep 3136319 = 4704479) B4704479
theorem B580639 : Blo 578813 580639 := bstep (se 1 (by rfl) ⟨435479, by rfl⟩ : syracuseStep 580639 = 870959) B870959
theorem B580719 : Blo 578813 580719 := bstep (se 1 (by rfl) ⟨435539, by rfl⟩ : syracuseStep 580719 = 871079) B871079
theorem B580763 : Blo 578813 580763 := bstep (se 1 (by rfl) ⟨435572, by rfl⟩ : syracuseStep 580763 = 871145) B871145
theorem B580799 : Blo 578813 580799 := bstep (se 1 (by rfl) ⟨435599, by rfl⟩ : syracuseStep 580799 = 871199) B871199
theorem B107306795 : Blo 578813 107306795 := bstep (se 1 (by rfl) ⟨80480096, by rfl⟩ : syracuseStep 107306795 = 160960193) B160960193
theorem B1302335 : Blo 578813 1302335 := bstep (se 1 (by rfl) ⟨976751, by rfl⟩ : syracuseStep 1302335 = 1953503) B1953503
theorem B2645903 : Blo 578813 2645903 := bstep (se 1 (by rfl) ⟨1984427, by rfl⟩ : syracuseStep 2645903 = 3968855) B3968855
theorem B22569293 : Blo 578813 22569293 := bstep (se 3 (by rfl) ⟨4231742, by rfl⟩ : syracuseStep 22569293 = 8463485) B8463485
theorem B1302911 : Blo 578813 1302911 := bstep (se 1 (by rfl) ⟨977183, by rfl⟩ : syracuseStep 1302911 = 1954367) B1954367
theorem B1565087 : Blo 578813 1565087 := bstep (se 1 (by rfl) ⟨1173815, by rfl⟩ : syracuseStep 1565087 = 2347631) B2347631
theorem B1303199 : Blo 578813 1303199 := bstep (se 1 (by rfl) ⟨977399, by rfl⟩ : syracuseStep 1303199 = 1954799) B1954799
theorem B582375 : Blo 578813 582375 := bstep (se 1 (by rfl) ⟨436781, by rfl⟩ : syracuseStep 582375 = 873563) B873563
theorem B582395 : Blo 578813 582395 := bstep (se 1 (by rfl) ⟨436796, by rfl⟩ : syracuseStep 582395 = 873593) B873593
theorem B1991465 : Blo 578813 1991465 := bstep (se 2 (by rfl) ⟨746799, by rfl⟩ : syracuseStep 1991465 = 1493599) B1493599
theorem B582655 : Blo 578813 582655 := bstep (se 1 (by rfl) ⟨436991, by rfl⟩ : syracuseStep 582655 = 873983) B873983
theorem B96429491 : Blo 578813 96429491 := bstep (se 1 (by rfl) ⟨72322118, by rfl⟩ : syracuseStep 96429491 = 144644237) B144644237
theorem B1304207 : Blo 578813 1304207 := bstep (se 1 (by rfl) ⟨978155, by rfl⟩ : syracuseStep 1304207 = 1956311) B1956311
theorem B976927 : Blo 578813 976927 := bstep (se 1 (by rfl) ⟨732695, by rfl⟩ : syracuseStep 976927 = 1465391) B1465391
theorem B192997505 : Blo 578813 192997505 := bstep (se 2 (by rfl) ⟨72374064, by rfl⟩ : syracuseStep 192997505 = 144748129) B144748129
theorem B1304873 : Blo 578813 1304873 := bstep (se 2 (by rfl) ⟨489327, by rfl⟩ : syracuseStep 1304873 = 978655) B978655
theorem B5302867 : Blo 578813 5302867 := bstep (se 1 (by rfl) ⟨3977150, by rfl⟩ : syracuseStep 5302867 = 7954301) B7954301
theorem B1305179 : Blo 578813 1305179 := bstep (se 1 (by rfl) ⟨978884, by rfl⟩ : syracuseStep 1305179 = 1957769) B1957769
theorem B8350361 : Blo 578813 8350361 := bstep (se 2 (by rfl) ⟨3131385, by rfl⟩ : syracuseStep 8350361 = 6262771) B6262771
theorem B43084819 : Blo 578813 43084819 := bstep (se 1 (by rfl) ⟨32313614, by rfl⟩ : syracuseStep 43084819 = 64627229) B64627229
theorem B11168873 : Blo 578813 11168873 := bstep (se 2 (by rfl) ⟨4188327, by rfl⟩ : syracuseStep 11168873 = 8376655) B8376655
theorem B1961171 : Blo 578813 1961171 := bstep (se 1 (by rfl) ⟨1470878, by rfl⟩ : syracuseStep 1961171 = 2941757) B2941757
theorem B1306907 : Blo 578813 1306907 := bstep (se 1 (by rfl) ⟨980180, by rfl⟩ : syracuseStep 1306907 = 1960361) B1960361
theorem B6288029 : Blo 578813 6288029 := bstep (se 3 (by rfl) ⟨1179005, by rfl⟩ : syracuseStep 6288029 = 2358011) B2358011
theorem B652063 : Blo 578813 652063 := bstep (se 1 (by rfl) ⟨489047, by rfl⟩ : syracuseStep 652063 = 978095) B978095
theorem B1307483 : Blo 578813 1307483 := bstep (se 1 (by rfl) ⟨980612, by rfl⟩ : syracuseStep 1307483 = 1961225) B1961225
theorem B980059 : Blo 578813 980059 := bstep (se 1 (by rfl) ⟨735044, by rfl⟩ : syracuseStep 980059 = 1470089) B1470089
theorem B3732799 : Blo 578813 3732799 := bstep (se 1 (by rfl) ⟨2799599, by rfl⟩ : syracuseStep 3732799 = 5599199) B5599199
theorem B1471871 : Blo 578813 1471871 := bstep (se 1 (by rfl) ⟨1103903, by rfl⟩ : syracuseStep 1471871 = 2207807) B2207807
theorem B2094569 : Blo 578813 2094569 := bstep (se 2 (by rfl) ⟨785463, by rfl⟩ : syracuseStep 2094569 = 1570927) B1570927
theorem B2946779 : Blo 578813 2946779 := bstep (se 1 (by rfl) ⟨2210084, by rfl⟩ : syracuseStep 2946779 = 4420169) B4420169
theorem B1963763 : Blo 578813 1963763 := bstep (se 1 (by rfl) ⟨1472822, by rfl⟩ : syracuseStep 1963763 = 2945645) B2945645
theorem B1308455 : Blo 578813 1308455 := bstep (se 1 (by rfl) ⟨981341, by rfl⟩ : syracuseStep 1308455 = 1962683) B1962683
theorem B981119 : Blo 578813 981119 := bstep (se 1 (by rfl) ⟨735839, by rfl⟩ : syracuseStep 981119 = 1471679) B1471679
theorem B1308923 : Blo 578813 1308923 := bstep (se 1 (by rfl) ⟨981692, by rfl⟩ : syracuseStep 1308923 = 1963385) B1963385
theorem B15858119 : Blo 578813 15858119 := bstep (se 1 (by rfl) ⟨11893589, by rfl⟩ : syracuseStep 15858119 = 23787179) B23787179
theorem B2947751 : Blo 578813 2947751 := bstep (se 1 (by rfl) ⟨2210813, by rfl⟩ : syracuseStep 2947751 = 4421627) B4421627
theorem B654043 : Blo 578813 654043 := bstep (se 1 (by rfl) ⟨490532, by rfl⟩ : syracuseStep 654043 = 981065) B981065
theorem B1309481 : Blo 578813 1309481 := bstep (se 2 (by rfl) ⟨491055, by rfl⟩ : syracuseStep 1309481 = 982111) B982111
theorem B3177427 : Blo 578813 3177427 := bstep (se 1 (by rfl) ⟨2383070, by rfl⟩ : syracuseStep 3177427 = 4766141) B4766141
theorem B654331 : Blo 578813 654331 := bstep (se 1 (by rfl) ⟨490748, by rfl⟩ : syracuseStep 654331 = 981497) B981497
theorem B1309751 : Blo 578813 1309751 := bstep (se 1 (by rfl) ⟨982313, by rfl⟩ : syracuseStep 1309751 = 1964627) B1964627
theorem B1310255 : Blo 578813 1310255 := bstep (se 1 (by rfl) ⟨982691, by rfl⟩ : syracuseStep 1310255 = 1965383) B1965383
theorem B655087 : Blo 578813 655087 := bstep (se 1 (by rfl) ⟨491315, by rfl⟩ : syracuseStep 655087 = 982631) B982631
theorem B1572605 : Blo 578813 1572605 := bstep (se 3 (by rfl) ⟨294863, by rfl⟩ : syracuseStep 1572605 = 589727) B589727
theorem B193625977 : Blo 578813 193625977 := bstep (se 2 (by rfl) ⟨72609741, by rfl⟩ : syracuseStep 193625977 = 145219483) B145219483
theorem B1966031 : Blo 578813 1966031 := bstep (se 1 (by rfl) ⟨1474523, by rfl⟩ : syracuseStep 1966031 = 2949047) B2949047
theorem B2687627 : Blo 578813 2687627 := bstep (se 1 (by rfl) ⟨2015720, by rfl⟩ : syracuseStep 2687627 = 4031441) B4031441
theorem B17925371 : Blo 578813 17925371 := bstep (se 1 (by rfl) ⟨13444028, by rfl⟩ : syracuseStep 17925371 = 26888057) B26888057
theorem B1115495 : Blo 578813 1115495 := bstep (se 1 (by rfl) ⟨836621, by rfl⟩ : syracuseStep 1115495 = 1673243) B1673243
theorem B4230053 : Blo 578813 4230053 := bstep (se 4 (by rfl) ⟨396567, by rfl⟩ : syracuseStep 4230053 = 793135) B793135
theorem B11046779 : Blo 578813 11046779 := bstep (se 1 (by rfl) ⟨8285084, by rfl⟩ : syracuseStep 11046779 = 16570169) B16570169
theorem B57446425 : Blo 578813 57446425 := bstep (se 2 (by rfl) ⟨21542409, by rfl⟩ : syracuseStep 57446425 = 43084819) B43084819
theorem B71537863 : Blo 578813 71537863 := bstep (se 1 (by rfl) ⟨53653397, by rfl⟩ : syracuseStep 71537863 = 107306795) B107306795
theorem B15046195 : Blo 578813 15046195 := bstep (se 1 (by rfl) ⟨11284646, by rfl⟩ : syracuseStep 15046195 = 22569293) B22569293
theorem B514660013 : Blo 578813 514660013 := bstep (se 3 (by rfl) ⟨96498752, by rfl⟩ : syracuseStep 514660013 = 192997505) B192997505
theorem B85859615 : Blo 578813 85859615 := bstep (se 1 (by rfl) ⟨64394711, by rfl⟩ : syracuseStep 85859615 = 128789423) B128789423
theorem B7445915 : Blo 578813 7445915 := bstep (se 1 (by rfl) ⟨5584436, by rfl⟩ : syracuseStep 7445915 = 11168873) B11168873
theorem B4236569 : Blo 578813 4236569 := bstep (se 2 (by rfl) ⟨1588713, by rfl⟩ : syracuseStep 4236569 = 3177427) B3177427
theorem B14919713 : Blo 578813 14919713 := bstep (se 2 (by rfl) ⟨5594892, by rfl⟩ : syracuseStep 14919713 = 11189785) B11189785
theorem B7055741 : Blo 578813 7055741 := bstep (se 3 (by rfl) ⟨1322951, by rfl⟩ : syracuseStep 7055741 = 2645903) B2645903
theorem B6269345 : Blo 578813 6269345 := bstep (se 2 (by rfl) ⟨2351004, by rfl⟩ : syracuseStep 6269345 = 4702009) B4702009
theorem B7450015 : Blo 578813 7450015 := bstep (se 1 (by rfl) ⟨5587511, by rfl⟩ : syracuseStep 7450015 = 11175023) B11175023
theorem B1486505 : Blo 578813 1486505 := bstep (se 2 (by rfl) ⟨557439, by rfl⟩ : syracuseStep 1486505 = 1114879) B1114879
theorem B183873397 : Blo 578813 183873397 := bstep (se 5 (by rfl) ⟨8619065, by rfl⟩ : syracuseStep 183873397 = 17238131) B17238131
theorem B3715631 : Blo 578813 3715631 := bstep (se 1 (by rfl) ⟨2786723, by rfl⟩ : syracuseStep 3715631 = 5573447) B5573447
theorem B2208491 : Blo 578813 2208491 := bstep (se 1 (by rfl) ⟨1656368, by rfl⟩ : syracuseStep 2208491 = 3312737) B3312737
theorem B2208991 : Blo 578813 2208991 := bstep (se 1 (by rfl) ⟨1656743, by rfl⟩ : syracuseStep 2208991 = 3313487) B3313487
theorem B2143997 : Blo 578813 2143997 := bstep (se 3 (by rfl) ⟨401999, by rfl⟩ : syracuseStep 2143997 = 803999) B803999
theorem B4176683 : Blo 578813 4176683 := bstep (se 1 (by rfl) ⟨3132512, by rfl⟩ : syracuseStep 4176683 = 6265025) B6265025
theorem B16694261 : Blo 578813 16694261 := bstep (se 5 (by rfl) ⟨782543, by rfl⟩ : syracuseStep 16694261 = 1565087) B1565087
theorem B2211407 : Blo 578813 2211407 := bstep (se 1 (by rfl) ⟨1658555, by rfl⟩ : syracuseStep 2211407 = 3317111) B3317111
theorem B2473703 : Blo 578813 2473703 := bstep (se 1 (by rfl) ⟨1855277, by rfl⟩ : syracuseStep 2473703 = 3710555) B3710555
theorem B868223 : Blo 578813 868223 := bstep (se 1 (by rfl) ⟨651167, by rfl⟩ : syracuseStep 868223 = 1302335) B1302335
theorem B2015279 : Blo 578813 2015279 := bstep (se 1 (by rfl) ⟨1511459, by rfl⟩ : syracuseStep 2015279 = 3022919) B3022919
theorem B17940635 : Blo 578813 17940635 := bstep (se 1 (by rfl) ⟨13455476, by rfl⟩ : syracuseStep 17940635 = 26910953) B26910953
theorem B6275231 : Blo 578813 6275231 := bstep (se 1 (by rfl) ⟨4706423, by rfl⟩ : syracuseStep 6275231 = 9412847) B9412847
theorem B868607 : Blo 578813 868607 := bstep (se 1 (by rfl) ⟨651455, by rfl⟩ : syracuseStep 868607 = 1302911) B1302911
theorem B868799 : Blo 578813 868799 := bstep (se 1 (by rfl) ⟨651599, by rfl⟩ : syracuseStep 868799 = 1303199) B1303199
theorem B1327643 : Blo 578813 1327643 := bstep (se 1 (by rfl) ⟨995732, by rfl⟩ : syracuseStep 1327643 = 1991465) B1991465
theorem B30524381 : Blo 578813 30524381 := bstep (se 3 (by rfl) ⟨5723321, by rfl⟩ : syracuseStep 30524381 = 11446643) B11446643
theorem B869417 : Blo 578813 869417 := bstep (se 2 (by rfl) ⟨326031, by rfl⟩ : syracuseStep 869417 = 652063) B652063
theorem B869471 : Blo 578813 869471 := bstep (se 1 (by rfl) ⟨652103, by rfl⟩ : syracuseStep 869471 = 1304207) B1304207
theorem B869915 : Blo 578813 869915 := bstep (se 1 (by rfl) ⟨652436, by rfl⟩ : syracuseStep 869915 = 1304873) B1304873
theorem B870119 : Blo 578813 870119 := bstep (se 1 (by rfl) ⟨652589, by rfl⟩ : syracuseStep 870119 = 1305179) B1305179
theorem B871271 : Blo 578813 871271 := bstep (se 1 (by rfl) ⟨653453, by rfl⟩ : syracuseStep 871271 = 1306907) B1306907
theorem B871655 : Blo 578813 871655 := bstep (se 1 (by rfl) ⟨653741, by rfl⟩ : syracuseStep 871655 = 1307483) B1307483
theorem B3722753 : Blo 578813 3722753 := bstep (se 2 (by rfl) ⟨1396032, by rfl⟩ : syracuseStep 3722753 = 2792065) B2792065
theorem B872057 : Blo 578813 872057 := bstep (se 2 (by rfl) ⟨327021, by rfl⟩ : syracuseStep 872057 = 654043) B654043
theorem B1396379 : Blo 578813 1396379 := bstep (se 1 (by rfl) ⟨1047284, by rfl⟩ : syracuseStep 1396379 = 2094569) B2094569
theorem B1101595 : Blo 578813 1101595 := bstep (se 1 (by rfl) ⟨826196, by rfl⟩ : syracuseStep 1101595 = 1652393) B1652393
theorem B872303 : Blo 578813 872303 := bstep (se 1 (by rfl) ⟨654227, by rfl⟩ : syracuseStep 872303 = 1308455) B1308455
theorem B872441 : Blo 578813 872441 := bstep (se 2 (by rfl) ⟨327165, by rfl⟩ : syracuseStep 872441 = 654331) B654331
theorem B2347147 : Blo 578813 2347147 := bstep (se 1 (by rfl) ⟨1760360, by rfl⟩ : syracuseStep 2347147 = 3520721) B3520721
theorem B872615 : Blo 578813 872615 := bstep (se 1 (by rfl) ⟨654461, by rfl⟩ : syracuseStep 872615 = 1308923) B1308923
theorem B10572079 : Blo 578813 10572079 := bstep (se 1 (by rfl) ⟨7929059, by rfl⟩ : syracuseStep 10572079 = 15858119) B15858119
theorem B1954205 : Blo 578813 1954205 := bstep (se 3 (by rfl) ⟨366413, by rfl⟩ : syracuseStep 1954205 = 732827) B732827
theorem B872987 : Blo 578813 872987 := bstep (se 1 (by rfl) ⟨654740, by rfl⟩ : syracuseStep 872987 = 1309481) B1309481
theorem B873167 : Blo 578813 873167 := bstep (se 1 (by rfl) ⟨654875, by rfl⟩ : syracuseStep 873167 = 1309751) B1309751
theorem B1102825 : Blo 578813 1102825 := bstep (se 2 (by rfl) ⟨413559, by rfl⟩ : syracuseStep 1102825 = 827119) B827119
theorem B873449 : Blo 578813 873449 := bstep (se 2 (by rfl) ⟨327543, by rfl⟩ : syracuseStep 873449 = 655087) B655087
theorem B873503 : Blo 578813 873503 := bstep (se 1 (by rfl) ⟨655127, by rfl⟩ : syracuseStep 873503 = 1310255) B1310255
theorem B258167969 : Blo 578813 258167969 := bstep (se 2 (by rfl) ⟨96812988, by rfl⟩ : syracuseStep 258167969 = 193625977) B193625977
theorem B578843 : Blo 578813 578843 := bstep (se 1 (by rfl) ⟨434132, by rfl⟩ : syracuseStep 578843 = 868265) B868265
theorem B4412879 : Blo 578813 4412879 := bstep (se 1 (by rfl) ⟨3309659, by rfl⟩ : syracuseStep 4412879 = 6619319) B6619319
theorem B4969957 : Blo 578813 4969957 := bstep (se 4 (by rfl) ⟨465933, by rfl⟩ : syracuseStep 4969957 = 931867) B931867
theorem B14112251 : Blo 578813 14112251 := bstep (se 1 (by rfl) ⟨10584188, by rfl⟩ : syracuseStep 14112251 = 21168377) B21168377
theorem B579099 : Blo 578813 579099 := bstep (se 1 (by rfl) ⟨434324, by rfl⟩ : syracuseStep 579099 = 868649) B868649
theorem B9426851 : Blo 578813 9426851 := bstep (se 1 (by rfl) ⟨7070138, by rfl⟩ : syracuseStep 9426851 = 14140277) B14140277
theorem B4478885 : Blo 578813 4478885 := bstep (se 4 (by rfl) ⟨419895, by rfl⟩ : syracuseStep 4478885 = 839791) B839791
theorem B2939003 : Blo 578813 2939003 := bstep (se 1 (by rfl) ⟨2204252, by rfl⟩ : syracuseStep 2939003 = 4408505) B4408505
theorem B2480503 : Blo 578813 2480503 := bstep (se 1 (by rfl) ⟨1860377, by rfl⟩ : syracuseStep 2480503 = 3720755) B3720755
theorem B1104283 : Blo 578813 1104283 := bstep (se 1 (by rfl) ⟨828212, by rfl⟩ : syracuseStep 1104283 = 1656425) B1656425
theorem B4544923 : Blo 578813 4544923 := bstep (se 1 (by rfl) ⟨3408692, by rfl⟩ : syracuseStep 4544923 = 6817385) B6817385
theorem B580335 : Blo 578813 580335 := bstep (se 1 (by rfl) ⟨435251, by rfl⟩ : syracuseStep 580335 = 870503) B870503
theorem B4414337 : Blo 578813 4414337 := bstep (se 2 (by rfl) ⟨1655376, by rfl⟩ : syracuseStep 4414337 = 3310753) B3310753
theorem B580591 : Blo 578813 580591 := bstep (se 1 (by rfl) ⟨435443, by rfl⟩ : syracuseStep 580591 = 870887) B870887
theorem B580767 : Blo 578813 580767 := bstep (se 1 (by rfl) ⟨435575, by rfl⟩ : syracuseStep 580767 = 871151) B871151
theorem B1957175 : Blo 578813 1957175 := bstep (se 1 (by rfl) ⟨1467881, by rfl⟩ : syracuseStep 1957175 = 2935763) B2935763
theorem B6970835 : Blo 578813 6970835 := bstep (se 1 (by rfl) ⟨5228126, by rfl⟩ : syracuseStep 6970835 = 10456253) B10456253
theorem B4415309 : Blo 578813 4415309 := bstep (se 3 (by rfl) ⟨827870, by rfl⟩ : syracuseStep 4415309 = 1655741) B1655741
theorem B3727241 : Blo 578813 3727241 := bstep (se 2 (by rfl) ⟨1397715, by rfl⟩ : syracuseStep 3727241 = 2795431) B2795431
theorem B1466363 : Blo 578813 1466363 := bstep (se 1 (by rfl) ⟨1099772, by rfl⟩ : syracuseStep 1466363 = 2199545) B2199545
theorem B1302569 : Blo 578813 1302569 := bstep (se 2 (by rfl) ⟨488463, by rfl⟩ : syracuseStep 1302569 = 976927) B976927
theorem B1106075 : Blo 578813 1106075 := bstep (se 1 (by rfl) ⟨829556, by rfl⟩ : syracuseStep 1106075 = 1659113) B1659113
theorem B581915 : Blo 578813 581915 := bstep (se 1 (by rfl) ⟨436436, by rfl⟩ : syracuseStep 581915 = 872873) B872873
theorem B581951 : Blo 578813 581951 := bstep (se 1 (by rfl) ⟨436463, by rfl⟩ : syracuseStep 581951 = 872927) B872927
theorem B1958255 : Blo 578813 1958255 := bstep (se 1 (by rfl) ⟨1468691, by rfl⟩ : syracuseStep 1958255 = 2937383) B2937383
theorem B582383 : Blo 578813 582383 := bstep (se 1 (by rfl) ⟨436787, by rfl⟩ : syracuseStep 582383 = 873575) B873575
theorem B7070489 : Blo 578813 7070489 := bstep (se 2 (by rfl) ⟨2651433, by rfl⟩ : syracuseStep 7070489 = 5302867) B5302867
theorem B582471 : Blo 578813 582471 := bstep (se 1 (by rfl) ⟨436853, by rfl⟩ : syracuseStep 582471 = 873707) B873707
theorem B582727 : Blo 578813 582727 := bstep (se 1 (by rfl) ⟨437045, by rfl⟩ : syracuseStep 582727 = 874091) B874091
theorem B2090879 : Blo 578813 2090879 := bstep (se 1 (by rfl) ⟨1568159, by rfl⟩ : syracuseStep 2090879 = 3136319) B3136319
theorem B7432793 : Blo 578813 7432793 := bstep (se 2 (by rfl) ⟨2787297, by rfl⟩ : syracuseStep 7432793 = 5574595) B5574595
theorem B1469087 : Blo 578813 1469087 := bstep (se 1 (by rfl) ⟨1101815, by rfl⟩ : syracuseStep 1469087 = 2203631) B2203631
theorem B2648969 : Blo 578813 2648969 := bstep (se 2 (by rfl) ⟨993363, by rfl⟩ : syracuseStep 2648969 = 1986727) B1986727
theorem B64286327 : Blo 578813 64286327 := bstep (se 1 (by rfl) ⟨48214745, by rfl⟩ : syracuseStep 64286327 = 96429491) B96429491
theorem B16740391 : Blo 578813 16740391 := bstep (se 1 (by rfl) ⟨12555293, by rfl⟩ : syracuseStep 16740391 = 25110587) B25110587
theorem B1306745 : Blo 578813 1306745 := bstep (se 2 (by rfl) ⟨490029, by rfl⟩ : syracuseStep 1306745 = 980059) B980059
theorem B4977065 : Blo 578813 4977065 := bstep (se 2 (by rfl) ⟨1866399, by rfl⟩ : syracuseStep 4977065 = 3732799) B3732799
theorem B5566907 : Blo 578813 5566907 := bstep (se 1 (by rfl) ⟨4175180, by rfl⟩ : syracuseStep 5566907 = 8350361) B8350361
theorem B1471031 : Blo 578813 1471031 := bstep (se 1 (by rfl) ⟨1103273, by rfl⟩ : syracuseStep 1471031 = 2206547) B2206547
theorem B1307447 : Blo 578813 1307447 := bstep (se 1 (by rfl) ⟨980585, by rfl⟩ : syracuseStep 1307447 = 1961171) B1961171
theorem B5600087 : Blo 578813 5600087 := bstep (se 1 (by rfl) ⟨4200065, by rfl⟩ : syracuseStep 5600087 = 8400131) B8400131
theorem B558265283 : Blo 578813 558265283 := bstep (se 1 (by rfl) ⟨418698962, by rfl⟩ : syracuseStep 558265283 = 837397925) B837397925
theorem B4192019 : Blo 578813 4192019 := bstep (se 1 (by rfl) ⟨3144014, by rfl⟩ : syracuseStep 4192019 = 6288029) B6288029
theorem B620455 : Blo 578813 620455 := bstep (se 1 (by rfl) ⟨465341, by rfl⟩ : syracuseStep 620455 = 930683) B930683
theorem B14153717 : Blo 578813 14153717 := bstep (se 5 (by rfl) ⟨663455, by rfl⟩ : syracuseStep 14153717 = 1326911) B1326911
theorem B981247 : Blo 578813 981247 := bstep (se 1 (by rfl) ⟨735935, by rfl⟩ : syracuseStep 981247 = 1471871) B1471871
theorem B1964519 : Blo 578813 1964519 := bstep (se 1 (by rfl) ⟨1473389, by rfl⟩ : syracuseStep 1964519 = 2946779) B2946779
theorem B1309175 : Blo 578813 1309175 := bstep (se 1 (by rfl) ⟨981881, by rfl⟩ : syracuseStep 1309175 = 1963763) B1963763
theorem B654079 : Blo 578813 654079 := bstep (se 1 (by rfl) ⟨490559, by rfl⟩ : syracuseStep 654079 = 981119) B981119
theorem B4291553 : Blo 578813 4291553 := bstep (se 2 (by rfl) ⟨1609332, by rfl⟩ : syracuseStep 4291553 = 3218665) B3218665
theorem B1965167 : Blo 578813 1965167 := bstep (se 1 (by rfl) ⟨1473875, by rfl⟩ : syracuseStep 1965167 = 2947751) B2947751
theorem B1048403 : Blo 578813 1048403 := bstep (se 1 (by rfl) ⟨786302, by rfl⟩ : syracuseStep 1048403 = 1572605) B1572605
theorem B1310687 : Blo 578813 1310687 := bstep (se 1 (by rfl) ⟨983015, by rfl⟩ : syracuseStep 1310687 = 1966031) B1966031
theorem B1343519 : Blo 578813 1343519 := bstep (se 1 (by rfl) ⟨1007639, by rfl⟩ : syracuseStep 1343519 = 2015279) B2015279
theorem B11960423 : Blo 578813 11960423 := bstep (se 1 (by rfl) ⟨8970317, by rfl⟩ : syracuseStep 11960423 = 17940635) B17940635
theorem B885095 : Blo 578813 885095 := bstep (se 1 (by rfl) ⟨663821, by rfl⟩ : syracuseStep 885095 = 1327643) B1327643
theorem B2949533 : Blo 578813 2949533 := bstep (se 3 (by rfl) ⟨553037, by rfl⟩ : syracuseStep 2949533 = 1106075) B1106075
theorem B20349587 : Blo 578813 20349587 := bstep (se 1 (by rfl) ⟨15262190, by rfl⟩ : syracuseStep 20349587 = 30524381) B30524381
theorem B2820035 : Blo 578813 2820035 := bstep (se 1 (by rfl) ⟨2115026, by rfl⟩ : syracuseStep 2820035 = 4230053) B4230053
theorem B9408167 : Blo 578813 9408167 := bstep (se 1 (by rfl) ⟨7056125, by rfl⟩ : syracuseStep 9408167 = 14112251) B14112251
theorem B2985923 : Blo 578813 2985923 := bstep (se 1 (by rfl) ⟨2239442, by rfl⟩ : syracuseStep 2985923 = 4478885) B4478885
theorem B9933353 : Blo 578813 9933353 := bstep (se 2 (by rfl) ⟨3725007, by rfl⟩ : syracuseStep 9933353 = 7450015) B7450015
theorem B22320521 : Blo 578813 22320521 := bstep (se 2 (by rfl) ⟨8370195, by rfl⟩ : syracuseStep 22320521 = 16740391) B16740391
theorem B14096105 : Blo 578813 14096105 := bstep (se 2 (by rfl) ⟨5286039, by rfl⟩ : syracuseStep 14096105 = 10572079) B10572079
theorem B2824379 : Blo 578813 2824379 := bstep (se 1 (by rfl) ⟨2118284, by rfl⟩ : syracuseStep 2824379 = 4236569) B4236569
theorem B4955195 : Blo 578813 4955195 := bstep (se 1 (by rfl) ⟨3716396, by rfl⟩ : syracuseStep 4955195 = 7432793) B7432793
theorem B6626609 : Blo 578813 6626609 := bstep (se 2 (by rfl) ⟨2484978, by rfl⟩ : syracuseStep 6626609 = 4969957) B4969957
theorem B20061593 : Blo 578813 20061593 := bstep (se 2 (by rfl) ⟨7523097, by rfl⟩ : syracuseStep 20061593 = 15046195) B15046195
theorem B991003 : Blo 578813 991003 := bstep (se 1 (by rfl) ⟨743252, by rfl⟩ : syracuseStep 991003 = 1486505) B1486505
theorem B827273 : Blo 578813 827273 := bstep (se 2 (by rfl) ⟨310227, by rfl⟩ : syracuseStep 827273 = 620455) B620455
theorem B11444141 : Blo 578813 11444141 := bstep (se 3 (by rfl) ⟨2145776, by rfl⟩ : syracuseStep 11444141 = 4291553) B4291553
theorem B3318043 : Blo 578813 3318043 := bstep (se 1 (by rfl) ⟨2488532, by rfl⟩ : syracuseStep 3318043 = 4977065) B4977065
theorem B3711271 : Blo 578813 3711271 := bstep (se 1 (by rfl) ⟨2783453, by rfl⟩ : syracuseStep 3711271 = 5566907) B5566907
theorem B2794679 : Blo 578813 2794679 := bstep (se 1 (by rfl) ⟨2096009, by rfl⟩ : syracuseStep 2794679 = 4192019) B4192019
theorem B1649135 : Blo 578813 1649135 := bstep (se 1 (by rfl) ⟨1236851, by rfl⟩ : syracuseStep 1649135 = 2473703) B2473703
theorem B698935 : Blo 578813 698935 := bstep (se 1 (by rfl) ⟨524201, by rfl⟩ : syracuseStep 698935 = 1048403) B1048403
theorem B172111979 : Blo 578813 172111979 := bstep (se 1 (by rfl) ⟨129083984, by rfl⟩ : syracuseStep 172111979 = 258167969) B258167969
theorem B4963943 : Blo 578813 4963943 := bstep (se 1 (by rfl) ⟨3722957, by rfl⟩ : syracuseStep 4963943 = 7445915) B7445915
theorem B868379 : Blo 578813 868379 := bstep (se 1 (by rfl) ⟨651284, by rfl⟩ : syracuseStep 868379 = 1302569) B1302569
theorem B76595233 : Blo 578813 76595233 := bstep (se 2 (by rfl) ⟨28723212, by rfl⟩ : syracuseStep 76595233 = 57446425) B57446425
theorem B3129529 : Blo 578813 3129529 := bstep (se 2 (by rfl) ⟨1173573, by rfl⟩ : syracuseStep 3129529 = 2347147) B2347147
theorem B1393919 : Blo 578813 1393919 := bstep (se 1 (by rfl) ⟨1045439, by rfl⟩ : syracuseStep 1393919 = 2090879) B2090879
theorem B9946475 : Blo 578813 9946475 := bstep (se 1 (by rfl) ⟨7459856, by rfl⟩ : syracuseStep 9946475 = 14919713) B14919713
theorem B4703827 : Blo 578813 4703827 := bstep (se 1 (by rfl) ⟨3527870, by rfl⟩ : syracuseStep 4703827 = 7055741) B7055741
theorem B4179563 : Blo 578813 4179563 := bstep (se 1 (by rfl) ⟨3134672, by rfl⟩ : syracuseStep 4179563 = 6269345) B6269345
theorem B871163 : Blo 578813 871163 := bstep (se 1 (by rfl) ⟨653372, by rfl⟩ : syracuseStep 871163 = 1306745) B1306745
theorem B2477087 : Blo 578813 2477087 := bstep (se 1 (by rfl) ⟨1857815, by rfl⟩ : syracuseStep 2477087 = 3715631) B3715631
theorem B871631 : Blo 578813 871631 := bstep (se 1 (by rfl) ⟨653723, by rfl⟩ : syracuseStep 871631 = 1307447) B1307447
theorem B872105 : Blo 578813 872105 := bstep (se 2 (by rfl) ⟨327039, by rfl⟩ : syracuseStep 872105 = 654079) B654079
theorem B1429331 : Blo 578813 1429331 := bstep (se 1 (by rfl) ⟨1071998, by rfl⟩ : syracuseStep 1429331 = 2143997) B2143997
theorem B872783 : Blo 578813 872783 := bstep (se 1 (by rfl) ⟨654587, by rfl⟩ : syracuseStep 872783 = 1309175) B1309175
theorem B3723677 : Blo 578813 3723677 := bstep (se 3 (by rfl) ⟨698189, by rfl⟩ : syracuseStep 3723677 = 1396379) B1396379
theorem B11129507 : Blo 578813 11129507 := bstep (se 1 (by rfl) ⟨8347130, by rfl⟩ : syracuseStep 11129507 = 16694261) B16694261
theorem B578815 : Blo 578813 578815 := bstep (se 1 (by rfl) ⟨434111, by rfl⟩ : syracuseStep 578815 = 868223) B868223
theorem B873791 : Blo 578813 873791 := bstep (se 1 (by rfl) ⟨655343, by rfl⟩ : syracuseStep 873791 = 1310687) B1310687
theorem B4183487 : Blo 578813 4183487 := bstep (se 1 (by rfl) ⟨3137615, by rfl⟩ : syracuseStep 4183487 = 6275231) B6275231
theorem B579071 : Blo 578813 579071 := bstep (se 1 (by rfl) ⟨434303, by rfl⟩ : syracuseStep 579071 = 868607) B868607
theorem B579199 : Blo 578813 579199 := bstep (se 1 (by rfl) ⟨434399, by rfl⟩ : syracuseStep 579199 = 868799) B868799
theorem B579611 : Blo 578813 579611 := bstep (se 1 (by rfl) ⟨434708, by rfl⟩ : syracuseStep 579611 = 869417) B869417
theorem B579647 : Blo 578813 579647 := bstep (se 1 (by rfl) ⟨434735, by rfl⟩ : syracuseStep 579647 = 869471) B869471
theorem B11950247 : Blo 578813 11950247 := bstep (se 1 (by rfl) ⟨8962685, by rfl⟩ : syracuseStep 11950247 = 17925371) B17925371
theorem B743663 : Blo 578813 743663 := bstep (se 1 (by rfl) ⟨557747, by rfl⟩ : syracuseStep 743663 = 1115495) B1115495
theorem B579943 : Blo 578813 579943 := bstep (se 1 (by rfl) ⟨434957, by rfl⟩ : syracuseStep 579943 = 869915) B869915
theorem B580079 : Blo 578813 580079 := bstep (se 1 (by rfl) ⟨435059, by rfl⟩ : syracuseStep 580079 = 870119) B870119
theorem B7167005 : Blo 578813 7167005 := bstep (se 3 (by rfl) ⟨1343813, by rfl⟩ : syracuseStep 7167005 = 2687627) B2687627
theorem B580847 : Blo 578813 580847 := bstep (se 1 (by rfl) ⟨435635, by rfl⟩ : syracuseStep 580847 = 871271) B871271
theorem B581103 : Blo 578813 581103 := bstep (se 1 (by rfl) ⟨435827, by rfl⟩ : syracuseStep 581103 = 871655) B871655
theorem B2481835 : Blo 578813 2481835 := bstep (se 1 (by rfl) ⟨1861376, by rfl⟩ : syracuseStep 2481835 = 3722753) B3722753
theorem B581371 : Blo 578813 581371 := bstep (se 1 (by rfl) ⟨436028, by rfl⟩ : syracuseStep 581371 = 872057) B872057
theorem B581535 : Blo 578813 581535 := bstep (se 1 (by rfl) ⟨436151, by rfl⟩ : syracuseStep 581535 = 872303) B872303
theorem B7364519 : Blo 578813 7364519 := bstep (se 1 (by rfl) ⟨5523389, by rfl⟩ : syracuseStep 7364519 = 11046779) B11046779
theorem B581627 : Blo 578813 581627 := bstep (se 1 (by rfl) ⟨436220, by rfl⟩ : syracuseStep 581627 = 872441) B872441
theorem B581743 : Blo 578813 581743 := bstep (se 1 (by rfl) ⟨436307, by rfl⟩ : syracuseStep 581743 = 872615) B872615
theorem B1302803 : Blo 578813 1302803 := bstep (se 1 (by rfl) ⟨977102, by rfl⟩ : syracuseStep 1302803 = 1954205) B1954205
theorem B581991 : Blo 578813 581991 := bstep (se 1 (by rfl) ⟨436493, by rfl⟩ : syracuseStep 581991 = 872987) B872987
theorem B582111 : Blo 578813 582111 := bstep (se 1 (by rfl) ⟨436583, by rfl⟩ : syracuseStep 582111 = 873167) B873167
theorem B582299 : Blo 578813 582299 := bstep (se 1 (by rfl) ⟨436724, by rfl⟩ : syracuseStep 582299 = 873449) B873449
theorem B582335 : Blo 578813 582335 := bstep (se 1 (by rfl) ⟨436751, by rfl⟩ : syracuseStep 582335 = 873503) B873503
theorem B2941919 : Blo 578813 2941919 := bstep (se 1 (by rfl) ⟨2206439, by rfl⟩ : syracuseStep 2941919 = 4412879) B4412879
theorem B343106675 : Blo 578813 343106675 := bstep (se 1 (by rfl) ⟨257330006, by rfl⟩ : syracuseStep 343106675 = 514660013) B514660013
theorem B6284567 : Blo 578813 6284567 := bstep (se 1 (by rfl) ⟨4713425, by rfl⟩ : syracuseStep 6284567 = 9426851) B9426851
theorem B1959335 : Blo 578813 1959335 := bstep (se 1 (by rfl) ⟨1469501, by rfl⟩ : syracuseStep 1959335 = 2939003) B2939003
theorem B2942891 : Blo 578813 2942891 := bstep (se 1 (by rfl) ⟨2207168, by rfl⟩ : syracuseStep 2942891 = 4414337) B4414337
theorem B57239743 : Blo 578813 57239743 := bstep (se 1 (by rfl) ⟨42929807, by rfl⟩ : syracuseStep 57239743 = 85859615) B85859615
theorem B1304783 : Blo 578813 1304783 := bstep (se 1 (by rfl) ⟨978587, by rfl⟩ : syracuseStep 1304783 = 1957175) B1957175
theorem B4647223 : Blo 578813 4647223 := bstep (se 1 (by rfl) ⟨3485417, by rfl⟩ : syracuseStep 4647223 = 6970835) B6970835
theorem B1468793 : Blo 578813 1468793 := bstep (se 2 (by rfl) ⟨550797, by rfl⟩ : syracuseStep 1468793 = 1101595) B1101595
theorem B245164529 : Blo 578813 245164529 := bstep (se 2 (by rfl) ⟨91936698, by rfl⟩ : syracuseStep 245164529 = 183873397) B183873397
theorem B2943539 : Blo 578813 2943539 := bstep (se 1 (by rfl) ⟨2207654, by rfl⟩ : syracuseStep 2943539 = 4415309) B4415309
theorem B2484827 : Blo 578813 2484827 := bstep (se 1 (by rfl) ⟨1863620, by rfl⟩ : syracuseStep 2484827 = 3727241) B3727241
theorem B977575 : Blo 578813 977575 := bstep (se 1 (by rfl) ⟨733181, by rfl⟩ : syracuseStep 977575 = 1466363) B1466363
theorem B1305503 : Blo 578813 1305503 := bstep (se 1 (by rfl) ⟨979127, by rfl⟩ : syracuseStep 1305503 = 1958255) B1958255
theorem B4713659 : Blo 578813 4713659 := bstep (se 1 (by rfl) ⟨3535244, by rfl⟩ : syracuseStep 4713659 = 7070489) B7070489
theorem B1470433 : Blo 578813 1470433 := bstep (se 2 (by rfl) ⟨551412, by rfl⟩ : syracuseStep 1470433 = 1102825) B1102825
theorem B95383817 : Blo 578813 95383817 := bstep (se 2 (by rfl) ⟨35768931, by rfl⟩ : syracuseStep 95383817 = 71537863) B71537863
theorem B2945321 : Blo 578813 2945321 := bstep (se 2 (by rfl) ⟨1104495, by rfl⟩ : syracuseStep 2945321 = 2208991) B2208991
theorem B979391 : Blo 578813 979391 := bstep (se 1 (by rfl) ⟨734543, by rfl⟩ : syracuseStep 979391 = 1469087) B1469087
theorem B1765979 : Blo 578813 1765979 := bstep (se 1 (by rfl) ⟨1324484, by rfl⟩ : syracuseStep 1765979 = 2648969) B2648969
theorem B42857551 : Blo 578813 42857551 := bstep (se 1 (by rfl) ⟨32143163, by rfl⟩ : syracuseStep 42857551 = 64286327) B64286327
theorem B1308329 : Blo 578813 1308329 := bstep (se 2 (by rfl) ⟨490623, by rfl⟩ : syracuseStep 1308329 = 981247) B981247
theorem B980687 : Blo 578813 980687 := bstep (se 1 (by rfl) ⟨735515, by rfl⟩ : syracuseStep 980687 = 1471031) B1471031
theorem B1472327 : Blo 578813 1472327 := bstep (se 1 (by rfl) ⟨1104245, by rfl⟩ : syracuseStep 1472327 = 2208491) B2208491
theorem B3307337 : Blo 578813 3307337 := bstep (se 2 (by rfl) ⟨1240251, by rfl⟩ : syracuseStep 3307337 = 2480503) B2480503
theorem B1472377 : Blo 578813 1472377 := bstep (se 2 (by rfl) ⟨552141, by rfl⟩ : syracuseStep 1472377 = 1104283) B1104283
theorem B6059897 : Blo 578813 6059897 := bstep (se 2 (by rfl) ⟨2272461, by rfl⟩ : syracuseStep 6059897 = 4544923) B4544923
theorem B3733391 : Blo 578813 3733391 := bstep (se 1 (by rfl) ⟨2800043, by rfl⟩ : syracuseStep 3733391 = 5600087) B5600087
theorem B372176855 : Blo 578813 372176855 := bstep (se 1 (by rfl) ⟨279132641, by rfl⟩ : syracuseStep 372176855 = 558265283) B558265283
theorem B9435811 : Blo 578813 9435811 := bstep (se 1 (by rfl) ⟨7076858, by rfl⟩ : syracuseStep 9435811 = 14153717) B14153717
theorem B1309679 : Blo 578813 1309679 := bstep (se 1 (by rfl) ⟨982259, by rfl⟩ : syracuseStep 1309679 = 1964519) B1964519
theorem B2784455 : Blo 578813 2784455 := bstep (se 1 (by rfl) ⟨2088341, by rfl⟩ : syracuseStep 2784455 = 4176683) B4176683
theorem B1310111 : Blo 578813 1310111 := bstep (se 1 (by rfl) ⟨982583, by rfl⟩ : syracuseStep 1310111 = 1965167) B1965167
theorem B1474271 : Blo 578813 1474271 := bstep (se 1 (by rfl) ⟨1105703, by rfl⟩ : syracuseStep 1474271 = 2211407) B2211407
theorem B590063 : Blo 578813 590063 := bstep (se 1 (by rfl) ⟨442547, by rfl⟩ : syracuseStep 590063 = 885095) B885095
theorem B1966355 : Blo 578813 1966355 := bstep (se 1 (by rfl) ⟨1474766, by rfl⟩ : syracuseStep 1966355 = 2949533) B2949533
theorem B4424057 : Blo 578813 4424057 := bstep (se 2 (by rfl) ⟨1659021, by rfl⟩ : syracuseStep 4424057 = 3318043) B3318043
theorem B4948361 : Blo 578813 4948361 := bstep (se 2 (by rfl) ⟨1855635, by rfl⟩ : syracuseStep 4948361 = 3711271) B3711271
theorem B2786375 : Blo 578813 2786375 := bstep (se 1 (by rfl) ⟨2089781, by rfl⟩ : syracuseStep 2786375 = 4179563) B4179563
theorem B54265565 : Blo 578813 54265565 := bstep (se 3 (by rfl) ⟨10174793, by rfl⟩ : syracuseStep 54265565 = 20349587) B20349587
theorem B76319657 : Blo 578813 76319657 := bstep (se 2 (by rfl) ⟨28619871, by rfl⟩ : syracuseStep 76319657 = 57239743) B57239743
theorem B6622235 : Blo 578813 6622235 := bstep (se 1 (by rfl) ⟨4966676, by rfl⟩ : syracuseStep 6622235 = 9933353) B9933353
theorem B14880347 : Blo 578813 14880347 := bstep (se 1 (by rfl) ⟨11160260, by rfl⟩ : syracuseStep 14880347 = 22320521) B22320521
theorem B2788991 : Blo 578813 2788991 := bstep (se 1 (by rfl) ⟨2091743, by rfl⟩ : syracuseStep 2788991 = 4183487) B4183487
theorem B7966831 : Blo 578813 7966831 := bstep (se 1 (by rfl) ⟨5975123, by rfl⟩ : syracuseStep 7966831 = 11950247) B11950247
theorem B13374395 : Blo 578813 13374395 := bstep (se 1 (by rfl) ⟨10030796, by rfl⟩ : syracuseStep 13374395 = 20061593) B20061593
theorem B2204891 : Blo 578813 2204891 := bstep (se 1 (by rfl) ⟨1653668, by rfl⟩ : syracuseStep 2204891 = 3307337) B3307337
theorem B4039931 : Blo 578813 4039931 := bstep (se 1 (by rfl) ⟨3029948, by rfl⟩ : syracuseStep 4039931 = 6059897) B6059897
theorem B3811549 : Blo 578813 3811549 := bstep (se 3 (by rfl) ⟨714665, by rfl⟩ : syracuseStep 3811549 = 1429331) B1429331
theorem B2206061 : Blo 578813 2206061 := bstep (se 3 (by rfl) ⟨413636, by rfl⟩ : syracuseStep 2206061 = 827273) B827273
theorem B1321337 : Blo 578813 1321337 := bstep (se 2 (by rfl) ⟨495501, by rfl⟩ : syracuseStep 1321337 = 991003) B991003
theorem B895679 : Blo 578813 895679 := bstep (se 1 (by rfl) ⟨671759, by rfl⟩ : syracuseStep 895679 = 1343519) B1343519
theorem B7973615 : Blo 578813 7973615 := bstep (se 1 (by rfl) ⟨5980211, by rfl⟩ : syracuseStep 7973615 = 11960423) B11960423
theorem B4172705 : Blo 578813 4172705 := bstep (se 2 (by rfl) ⟨1564764, by rfl⟩ : syracuseStep 4172705 = 3129529) B3129529
theorem B929279 : Blo 578813 929279 := bstep (se 1 (by rfl) ⟨696959, by rfl⟩ : syracuseStep 929279 = 1393919) B1393919
theorem B6630983 : Blo 578813 6630983 := bstep (se 1 (by rfl) ⟨4973237, by rfl⟩ : syracuseStep 6630983 = 9946475) B9946475
theorem B1880023 : Blo 578813 1880023 := bstep (se 1 (by rfl) ⟨1410017, by rfl⟩ : syracuseStep 1880023 = 2820035) B2820035
theorem B24785189 : Blo 578813 24785189 := bstep (se 4 (by rfl) ⟨2323611, by rfl⟩ : syracuseStep 24785189 = 4647223) B4647223
theorem B1651391 : Blo 578813 1651391 := bstep (se 1 (by rfl) ⟨1238543, by rfl⟩ : syracuseStep 1651391 = 2477087) B2477087
theorem B6271769 : Blo 578813 6271769 := bstep (se 2 (by rfl) ⟨2351913, by rfl⟩ : syracuseStep 6271769 = 4703827) B4703827
theorem B6272111 : Blo 578813 6272111 := bstep (se 1 (by rfl) ⟨4704083, by rfl⟩ : syracuseStep 6272111 = 9408167) B9408167
theorem B7419671 : Blo 578813 7419671 := bstep (se 1 (by rfl) ⟨5564753, by rfl⟩ : syracuseStep 7419671 = 11129507) B11129507
theorem B16758845 : Blo 578813 16758845 := bstep (se 3 (by rfl) ⟨3142283, by rfl⟩ : syracuseStep 16758845 = 6284567) B6284567
theorem B931913 : Blo 578813 931913 := bstep (se 2 (by rfl) ⟨349467, by rfl⟩ : syracuseStep 931913 = 698935) B698935
theorem B1882919 : Blo 578813 1882919 := bstep (se 1 (by rfl) ⟨1412189, by rfl⟩ : syracuseStep 1882919 = 2824379) B2824379
theorem B868535 : Blo 578813 868535 := bstep (se 1 (by rfl) ⟨651401, by rfl⟩ : syracuseStep 868535 = 1302803) B1302803
theorem B458965277 : Blo 578813 458965277 := bstep (se 3 (by rfl) ⟨86055989, by rfl⟩ : syracuseStep 458965277 = 172111979) B172111979
theorem B228573605 : Blo 578813 228573605 := bstep (se 4 (by rfl) ⟨21428775, by rfl⟩ : syracuseStep 228573605 = 42857551) B42857551
theorem B1983101 : Blo 578813 1983101 := bstep (se 3 (by rfl) ⟨371831, by rfl⟩ : syracuseStep 1983101 = 743663) B743663
theorem B228737783 : Blo 578813 228737783 := bstep (se 1 (by rfl) ⟨171553337, by rfl⟩ : syracuseStep 228737783 = 343106675) B343106675
theorem B869855 : Blo 578813 869855 := bstep (se 1 (by rfl) ⟨652391, by rfl⟩ : syracuseStep 869855 = 1304783) B1304783
theorem B1099423 : Blo 578813 1099423 := bstep (se 1 (by rfl) ⟨824567, by rfl⟩ : syracuseStep 1099423 = 1649135) B1649135
theorem B1656551 : Blo 578813 1656551 := bstep (se 1 (by rfl) ⟨1242413, by rfl⟩ : syracuseStep 1656551 = 2484827) B2484827
theorem B870335 : Blo 578813 870335 := bstep (se 1 (by rfl) ⟨652751, by rfl⟩ : syracuseStep 870335 = 1305503) B1305503
theorem B63589211 : Blo 578813 63589211 := bstep (se 1 (by rfl) ⟨47691908, by rfl⟩ : syracuseStep 63589211 = 95383817) B95383817
theorem B872219 : Blo 578813 872219 := bstep (se 1 (by rfl) ⟨654164, by rfl⟩ : syracuseStep 872219 = 1308329) B1308329
theorem B873119 : Blo 578813 873119 := bstep (se 1 (by rfl) ⟨654839, by rfl⟩ : syracuseStep 873119 = 1309679) B1309679
theorem B1856303 : Blo 578813 1856303 := bstep (se 1 (by rfl) ⟨1392227, by rfl⟩ : syracuseStep 1856303 = 2784455) B2784455
theorem B873407 : Blo 578813 873407 := bstep (se 1 (by rfl) ⟨655055, by rfl⟩ : syracuseStep 873407 = 1310111) B1310111
theorem B578919 : Blo 578813 578919 := bstep (se 1 (by rfl) ⟨434189, by rfl⟩ : syracuseStep 578919 = 868379) B868379
theorem B102126977 : Blo 578813 102126977 := bstep (se 2 (by rfl) ⟨38297616, by rfl⟩ : syracuseStep 102126977 = 76595233) B76595233
theorem B580775 : Blo 578813 580775 := bstep (se 1 (by rfl) ⟨435581, by rfl⟩ : syracuseStep 580775 = 871163) B871163
theorem B581087 : Blo 578813 581087 := bstep (se 1 (by rfl) ⟨435815, by rfl⟩ : syracuseStep 581087 = 871631) B871631
theorem B581403 : Blo 578813 581403 := bstep (se 1 (by rfl) ⟨436052, by rfl⟩ : syracuseStep 581403 = 872105) B872105
theorem B1990615 : Blo 578813 1990615 := bstep (se 1 (by rfl) ⟨1492961, by rfl⟩ : syracuseStep 1990615 = 2985923) B2985923
theorem B581855 : Blo 578813 581855 := bstep (se 1 (by rfl) ⟨436391, by rfl⟩ : syracuseStep 581855 = 872783) B872783
theorem B2482451 : Blo 578813 2482451 := bstep (se 1 (by rfl) ⟨1861838, by rfl⟩ : syracuseStep 2482451 = 3723677) B3723677
theorem B582527 : Blo 578813 582527 := bstep (se 1 (by rfl) ⟨436895, by rfl⟩ : syracuseStep 582527 = 873791) B873791
theorem B1303433 : Blo 578813 1303433 := bstep (se 2 (by rfl) ⟨488787, by rfl⟩ : syracuseStep 1303433 = 977575) B977575
theorem B9397403 : Blo 578813 9397403 := bstep (se 1 (by rfl) ⟨7048052, by rfl⟩ : syracuseStep 9397403 = 14096105) B14096105
theorem B4778003 : Blo 578813 4778003 := bstep (se 1 (by rfl) ⟨3583502, by rfl⟩ : syracuseStep 4778003 = 7167005) B7167005
theorem B3303463 : Blo 578813 3303463 := bstep (se 1 (by rfl) ⟨2477597, by rfl⟩ : syracuseStep 3303463 = 4955195) B4955195
theorem B4417739 : Blo 578813 4417739 := bstep (se 1 (by rfl) ⟨3313304, by rfl⟩ : syracuseStep 4417739 = 6626609) B6626609
theorem B4909679 : Blo 578813 4909679 := bstep (se 1 (by rfl) ⟨3682259, by rfl⟩ : syracuseStep 4909679 = 7364519) B7364519
theorem B7629427 : Blo 578813 7629427 := bstep (se 1 (by rfl) ⟨5722070, by rfl⟩ : syracuseStep 7629427 = 11444141) B11444141
theorem B1960577 : Blo 578813 1960577 := bstep (se 2 (by rfl) ⟨735216, by rfl⟩ : syracuseStep 1960577 = 1470433) B1470433
theorem B1961279 : Blo 578813 1961279 := bstep (se 1 (by rfl) ⟨1470959, by rfl⟩ : syracuseStep 1961279 = 2941919) B2941919
theorem B1863119 : Blo 578813 1863119 := bstep (se 1 (by rfl) ⟨1397339, by rfl⟩ : syracuseStep 1863119 = 2794679) B2794679
theorem B1306223 : Blo 578813 1306223 := bstep (se 1 (by rfl) ⟨979667, by rfl⟩ : syracuseStep 1306223 = 1959335) B1959335
theorem B1961927 : Blo 578813 1961927 := bstep (se 1 (by rfl) ⟨1471445, by rfl⟩ : syracuseStep 1961927 = 2942891) B2942891
theorem B979195 : Blo 578813 979195 := bstep (se 1 (by rfl) ⟨734396, by rfl⟩ : syracuseStep 979195 = 1468793) B1468793
theorem B163443019 : Blo 578813 163443019 := bstep (se 1 (by rfl) ⟨122582264, by rfl⟩ : syracuseStep 163443019 = 245164529) B245164529
theorem B1962359 : Blo 578813 1962359 := bstep (se 1 (by rfl) ⟨1471769, by rfl⟩ : syracuseStep 1962359 = 2943539) B2943539
theorem B3142439 : Blo 578813 3142439 := bstep (se 1 (by rfl) ⟨2356829, by rfl⟩ : syracuseStep 3142439 = 4713659) B4713659
theorem B1963169 : Blo 578813 1963169 := bstep (se 2 (by rfl) ⟨736188, by rfl⟩ : syracuseStep 1963169 = 1472377) B1472377
theorem B1963547 : Blo 578813 1963547 := bstep (se 1 (by rfl) ⟨1472660, by rfl⟩ : syracuseStep 1963547 = 2945321) B2945321
theorem B652927 : Blo 578813 652927 := bstep (se 1 (by rfl) ⟨489695, by rfl⟩ : syracuseStep 652927 = 979391) B979391
theorem B1177319 : Blo 578813 1177319 := bstep (se 1 (by rfl) ⟨882989, by rfl⟩ : syracuseStep 1177319 = 1765979) B1765979
theorem B12581081 : Blo 578813 12581081 := bstep (se 2 (by rfl) ⟨4717905, by rfl⟩ : syracuseStep 12581081 = 9435811) B9435811
theorem B653791 : Blo 578813 653791 := bstep (se 1 (by rfl) ⟨490343, by rfl⟩ : syracuseStep 653791 = 980687) B980687
theorem B981551 : Blo 578813 981551 := bstep (se 1 (by rfl) ⟨736163, by rfl⟩ : syracuseStep 981551 = 1472327) B1472327
theorem B2488927 : Blo 578813 2488927 := bstep (se 1 (by rfl) ⟨1866695, by rfl⟩ : syracuseStep 2488927 = 3733391) B3733391
theorem B248117903 : Blo 578813 248117903 := bstep (se 1 (by rfl) ⟨186088427, by rfl⟩ : syracuseStep 248117903 = 372176855) B372176855
theorem B3309113 : Blo 578813 3309113 := bstep (se 2 (by rfl) ⟨1240917, by rfl⟩ : syracuseStep 3309113 = 2481835) B2481835
theorem B3309295 : Blo 578813 3309295 := bstep (se 1 (by rfl) ⟨2481971, by rfl⟩ : syracuseStep 3309295 = 4963943) B4963943
theorem B982847 : Blo 578813 982847 := bstep (se 1 (by rfl) ⟨737135, by rfl⟩ : syracuseStep 982847 = 1474271) B1474271
theorem B1310903 : Blo 578813 1310903 := bstep (se 1 (by rfl) ⟨983177, by rfl⟩ : syracuseStep 1310903 = 1966355) B1966355
theorem B2949371 : Blo 578813 2949371 := bstep (se 1 (by rfl) ⟨2212028, by rfl⟩ : syracuseStep 2949371 = 4424057) B4424057
theorem B1573501 : Blo 578813 1573501 := bstep (se 3 (by rfl) ⟨295031, by rfl⟩ : syracuseStep 1573501 = 590063) B590063
theorem B36177043 : Blo 578813 36177043 := bstep (se 1 (by rfl) ⟨27132782, by rfl⟩ : syracuseStep 36177043 = 54265565) B54265565
theorem B5082065 : Blo 578813 5082065 := bstep (se 2 (by rfl) ⟨1905774, by rfl⟩ : syracuseStep 5082065 = 3811549) B3811549
theorem B8916263 : Blo 578813 8916263 := bstep (se 1 (by rfl) ⟨6687197, by rfl⟩ : syracuseStep 8916263 = 13374395) B13374395
theorem B10622441 : Blo 578813 10622441 := bstep (se 2 (by rfl) ⟨3983415, by rfl⟩ : syracuseStep 10622441 = 7966831) B7966831
theorem B6264935 : Blo 578813 6264935 := bstep (se 1 (by rfl) ⟨4698701, by rfl⟩ : syracuseStep 6264935 = 9397403) B9397403
theorem B2693287 : Blo 578813 2693287 := bstep (se 1 (by rfl) ⟨2019965, by rfl⟩ : syracuseStep 2693287 = 4039931) B4039931
theorem B3185335 : Blo 578813 3185335 := bstep (se 1 (by rfl) ⟨2389001, by rfl⟩ : syracuseStep 3185335 = 4778003) B4778003
theorem B5315743 : Blo 578813 5315743 := bstep (se 1 (by rfl) ⟨3986807, by rfl⟩ : syracuseStep 5315743 = 7973615) B7973615
theorem B16523459 : Blo 578813 16523459 := bstep (se 1 (by rfl) ⟨12392594, by rfl⟩ : syracuseStep 16523459 = 24785189) B24785189
theorem B3318569 : Blo 578813 3318569 := bstep (se 2 (by rfl) ⟨1244463, by rfl⟩ : syracuseStep 3318569 = 2488927) B2488927
theorem B1255279 : Blo 578813 1255279 := bstep (se 1 (by rfl) ⟨941459, by rfl⟩ : syracuseStep 1255279 = 1882919) B1882919
theorem B2206075 : Blo 578813 2206075 := bstep (se 1 (by rfl) ⟨1654556, by rfl⟩ : syracuseStep 2206075 = 3309113) B3309113
theorem B152382403 : Blo 578813 152382403 := bstep (se 1 (by rfl) ⟨114286802, by rfl⟩ : syracuseStep 152382403 = 228573605) B228573605
theorem B5288269 : Blo 578813 5288269 := bstep (se 3 (by rfl) ⟨991550, by rfl⟩ : syracuseStep 5288269 = 1983101) B1983101
theorem B4404617 : Blo 578813 4404617 := bstep (se 2 (by rfl) ⟨1651731, by rfl⟩ : syracuseStep 4404617 = 3303463) B3303463
theorem B16725629 : Blo 578813 16725629 := bstep (se 3 (by rfl) ⟨3136055, by rfl⟩ : syracuseStep 16725629 = 6272111) B6272111
theorem B10172569 : Blo 578813 10172569 := bstep (se 2 (by rfl) ⟨3814713, by rfl⟩ : syracuseStep 10172569 = 7629427) B7629427
theorem B2506697 : Blo 578813 2506697 := bstep (se 2 (by rfl) ⟨940011, by rfl⟩ : syracuseStep 2506697 = 1880023) B1880023
theorem B1654967 : Blo 578813 1654967 := bstep (se 1 (by rfl) ⟨1241225, by rfl⟩ : syracuseStep 1654967 = 2482451) B2482451
theorem B217924025 : Blo 578813 217924025 := bstep (se 2 (by rfl) ⟨81721509, by rfl⟩ : syracuseStep 217924025 = 163443019) B163443019
theorem B868955 : Blo 578813 868955 := bstep (se 1 (by rfl) ⟨651716, by rfl⟩ : syracuseStep 868955 = 1303433) B1303433
theorem B3523565 : Blo 578813 3523565 := bstep (se 3 (by rfl) ⟨660668, by rfl⟩ : syracuseStep 3523565 = 1321337) B1321337
theorem B9553909 : Blo 578813 9553909 := bstep (se 5 (by rfl) ⟨447839, by rfl⟩ : syracuseStep 9553909 = 895679) B895679
theorem B870569 : Blo 578813 870569 := bstep (se 2 (by rfl) ⟨326463, by rfl⟩ : syracuseStep 870569 = 652927) B652927
theorem B870815 : Blo 578813 870815 := bstep (se 1 (by rfl) ⟨653111, by rfl⟩ : syracuseStep 870815 = 1306223) B1306223
theorem B1100927 : Blo 578813 1100927 := bstep (se 1 (by rfl) ⟨825695, by rfl⟩ : syracuseStep 1100927 = 1651391) B1651391
theorem B4181179 : Blo 578813 4181179 := bstep (se 1 (by rfl) ⟨3135884, by rfl⟩ : syracuseStep 4181179 = 6271769) B6271769
theorem B871721 : Blo 578813 871721 := bstep (se 2 (by rfl) ⟨326895, by rfl⟩ : syracuseStep 871721 = 653791) B653791
theorem B4968317 : Blo 578813 4968317 := bstep (se 3 (by rfl) ⟨931559, by rfl⟩ : syracuseStep 4968317 = 1863119) B1863119
theorem B2478077 : Blo 578813 2478077 := bstep (se 3 (by rfl) ⟨464639, by rfl⟩ : syracuseStep 2478077 = 929279) B929279
theorem B4412393 : Blo 578813 4412393 := bstep (se 2 (by rfl) ⟨1654647, by rfl⟩ : syracuseStep 4412393 = 3309295) B3309295
theorem B579023 : Blo 578813 579023 := bstep (se 1 (by rfl) ⟨434267, by rfl⟩ : syracuseStep 579023 = 868535) B868535
theorem B305976851 : Blo 578813 305976851 := bstep (se 1 (by rfl) ⟨229482638, by rfl⟩ : syracuseStep 305976851 = 458965277) B458965277
theorem B3298907 : Blo 578813 3298907 := bstep (se 1 (by rfl) ⟨2474180, by rfl⟩ : syracuseStep 3298907 = 4948361) B4948361
theorem B152491855 : Blo 578813 152491855 := bstep (se 1 (by rfl) ⟨114368891, by rfl⟩ : syracuseStep 152491855 = 228737783) B228737783
theorem B1857583 : Blo 578813 1857583 := bstep (se 1 (by rfl) ⟨1393187, by rfl⟩ : syracuseStep 1857583 = 2786375) B2786375
theorem B579903 : Blo 578813 579903 := bstep (se 1 (by rfl) ⟨434927, by rfl⟩ : syracuseStep 579903 = 869855) B869855
theorem B1104367 : Blo 578813 1104367 := bstep (se 1 (by rfl) ⟨828275, by rfl⟩ : syracuseStep 1104367 = 1656551) B1656551
theorem B580223 : Blo 578813 580223 := bstep (se 1 (by rfl) ⟨435167, by rfl⟩ : syracuseStep 580223 = 870335) B870335
theorem B42392807 : Blo 578813 42392807 := bstep (se 1 (by rfl) ⟨31794605, by rfl⟩ : syracuseStep 42392807 = 63589211) B63589211
theorem B50879771 : Blo 578813 50879771 := bstep (se 1 (by rfl) ⟨38159828, by rfl⟩ : syracuseStep 50879771 = 76319657) B76319657
theorem B4414823 : Blo 578813 4414823 := bstep (se 1 (by rfl) ⟨3311117, by rfl⟩ : syracuseStep 4414823 = 6622235) B6622235
theorem B1465897 : Blo 578813 1465897 := bstep (se 2 (by rfl) ⟨549711, by rfl⟩ : syracuseStep 1465897 = 1099423) B1099423
theorem B9920231 : Blo 578813 9920231 := bstep (se 1 (by rfl) ⟨7440173, by rfl⟩ : syracuseStep 9920231 = 14880347) B14880347
theorem B1859327 : Blo 578813 1859327 := bstep (se 1 (by rfl) ⟨1394495, by rfl⟩ : syracuseStep 1859327 = 2788991) B2788991
theorem B581479 : Blo 578813 581479 := bstep (se 1 (by rfl) ⟨436109, by rfl⟩ : syracuseStep 581479 = 872219) B872219
theorem B582079 : Blo 578813 582079 := bstep (se 1 (by rfl) ⟨436559, by rfl⟩ : syracuseStep 582079 = 873119) B873119
theorem B1237535 : Blo 578813 1237535 := bstep (se 1 (by rfl) ⟨928151, by rfl⟩ : syracuseStep 1237535 = 1856303) B1856303
theorem B582271 : Blo 578813 582271 := bstep (se 1 (by rfl) ⟨436703, by rfl⟩ : syracuseStep 582271 = 873407) B873407
theorem B68084651 : Blo 578813 68084651 := bstep (se 1 (by rfl) ⟨51063488, by rfl⟩ : syracuseStep 68084651 = 102126977) B102126977
theorem B1305593 : Blo 578813 1305593 := bstep (se 2 (by rfl) ⟨489597, by rfl⟩ : syracuseStep 1305593 = 979195) B979195
theorem B1469927 : Blo 578813 1469927 := bstep (se 1 (by rfl) ⟨1102445, by rfl⟩ : syracuseStep 1469927 = 2204891) B2204891
theorem B2945159 : Blo 578813 2945159 := bstep (se 1 (by rfl) ⟨2208869, by rfl⟩ : syracuseStep 2945159 = 4417739) B4417739
theorem B1470707 : Blo 578813 1470707 := bstep (se 1 (by rfl) ⟨1103030, by rfl⟩ : syracuseStep 1470707 = 2206061) B2206061
theorem B3273119 : Blo 578813 3273119 := bstep (se 1 (by rfl) ⟨2454839, by rfl⟩ : syracuseStep 3273119 = 4909679) B4909679
theorem B1307051 : Blo 578813 1307051 := bstep (se 1 (by rfl) ⟨980288, by rfl⟩ : syracuseStep 1307051 = 1960577) B1960577
theorem B2781803 : Blo 578813 2781803 := bstep (se 1 (by rfl) ⟨2086352, by rfl⟩ : syracuseStep 2781803 = 4172705) B4172705
theorem B1307519 : Blo 578813 1307519 := bstep (se 1 (by rfl) ⟨980639, by rfl⟩ : syracuseStep 1307519 = 1961279) B1961279
theorem B4420655 : Blo 578813 4420655 := bstep (se 1 (by rfl) ⟨3315491, by rfl⟩ : syracuseStep 4420655 = 6630983) B6630983
theorem B1307951 : Blo 578813 1307951 := bstep (se 1 (by rfl) ⟨980963, by rfl⟩ : syracuseStep 1307951 = 1961927) B1961927
theorem B1308239 : Blo 578813 1308239 := bstep (se 1 (by rfl) ⟨981179, by rfl⟩ : syracuseStep 1308239 = 1962359) B1962359
theorem B2094959 : Blo 578813 2094959 := bstep (se 1 (by rfl) ⟨1571219, by rfl⟩ : syracuseStep 2094959 = 3142439) B3142439
theorem B1308779 : Blo 578813 1308779 := bstep (se 1 (by rfl) ⟨981584, by rfl⟩ : syracuseStep 1308779 = 1963169) B1963169
theorem B1309031 : Blo 578813 1309031 := bstep (se 1 (by rfl) ⟨981773, by rfl⟩ : syracuseStep 1309031 = 1963547) B1963547
theorem B784879 : Blo 578813 784879 := bstep (se 1 (by rfl) ⟨588659, by rfl⟩ : syracuseStep 784879 = 1177319) B1177319
theorem B4946447 : Blo 578813 4946447 := bstep (se 1 (by rfl) ⟨3709835, by rfl⟩ : syracuseStep 4946447 = 7419671) B7419671
theorem B11172563 : Blo 578813 11172563 := bstep (se 1 (by rfl) ⟨8379422, by rfl⟩ : syracuseStep 11172563 = 16758845) B16758845
theorem B621275 : Blo 578813 621275 := bstep (se 1 (by rfl) ⟨465956, by rfl⟩ : syracuseStep 621275 = 931913) B931913
theorem B8387387 : Blo 578813 8387387 := bstep (se 1 (by rfl) ⟨6290540, by rfl⟩ : syracuseStep 8387387 = 12581081) B12581081
theorem B654367 : Blo 578813 654367 := bstep (se 1 (by rfl) ⟨490775, by rfl⟩ : syracuseStep 654367 = 981551) B981551
theorem B165411935 : Blo 578813 165411935 := bstep (se 1 (by rfl) ⟨124058951, by rfl⟩ : syracuseStep 165411935 = 248117903) B248117903
theorem B655231 : Blo 578813 655231 := bstep (se 1 (by rfl) ⟨491423, by rfl⟩ : syracuseStep 655231 = 982847) B982847
theorem B2654153 : Blo 578813 2654153 := bstep (se 2 (by rfl) ⟨995307, by rfl⟩ : syracuseStep 2654153 = 1990615) B1990615
theorem B1966247 : Blo 578813 1966247 := bstep (se 1 (by rfl) ⟨1474685, by rfl⟩ : syracuseStep 1966247 = 2949371) B2949371
theorem B2098001 : Blo 578813 2098001 := bstep (se 2 (by rfl) ⟨786750, by rfl⟩ : syracuseStep 2098001 = 1573501) B1573501
theorem B48236057 : Blo 578813 48236057 := bstep (se 2 (by rfl) ⟨18088521, by rfl⟩ : syracuseStep 48236057 = 36177043) B36177043
theorem B1673705 : Blo 578813 1673705 := bstep (se 2 (by rfl) ⟨627639, by rfl⟩ : syracuseStep 1673705 = 1255279) B1255279
theorem B3312211 : Blo 578813 3312211 := bstep (se 1 (by rfl) ⟨2484158, by rfl⟩ : syracuseStep 3312211 = 4968317) B4968317
theorem B7081627 : Blo 578813 7081627 := bstep (se 1 (by rfl) ⟨5311220, by rfl⟩ : syracuseStep 7081627 = 10622441) B10622441
theorem B203984567 : Blo 578813 203984567 := bstep (se 1 (by rfl) ⟨152988425, by rfl⟩ : syracuseStep 203984567 = 305976851) B305976851
theorem B2199271 : Blo 578813 2199271 := bstep (se 1 (by rfl) ⟨1649453, by rfl⟩ : syracuseStep 2199271 = 3298907) B3298907
theorem B5574905 : Blo 578813 5574905 := bstep (se 2 (by rfl) ⟨2090589, by rfl⟩ : syracuseStep 5574905 = 4181179) B4181179
theorem B33919847 : Blo 578813 33919847 := bstep (se 1 (by rfl) ⟨25439885, by rfl⟩ : syracuseStep 33919847 = 50879771) B50879771
theorem B11015639 : Blo 578813 11015639 := bstep (se 1 (by rfl) ⟨8261729, by rfl⟩ : syracuseStep 11015639 = 16523459) B16523459
theorem B825023 : Blo 578813 825023 := bstep (se 1 (by rfl) ⟨618767, by rfl⟩ : syracuseStep 825023 = 1237535) B1237535
theorem B7051025 : Blo 578813 7051025 := bstep (se 2 (by rfl) ⟨2644134, by rfl⟩ : syracuseStep 7051025 = 5288269) B5288269
theorem B11150419 : Blo 578813 11150419 := bstep (se 1 (by rfl) ⟨8362814, by rfl⟩ : syracuseStep 11150419 = 16725629) B16725629
theorem B7087657 : Blo 578813 7087657 := bstep (se 2 (by rfl) ⟨2657871, by rfl⟩ : syracuseStep 7087657 = 5315743) B5315743
theorem B7448375 : Blo 578813 7448375 := bstep (se 1 (by rfl) ⟨5586281, by rfl⟩ : syracuseStep 7448375 = 11172563) B11172563
theorem B110274623 : Blo 578813 110274623 := bstep (se 1 (by rfl) ⟨82705967, by rfl⟩ : syracuseStep 110274623 = 165411935) B165411935
theorem B9907109 : Blo 578813 9907109 := bstep (se 4 (by rfl) ⟨928791, by rfl⟩ : syracuseStep 9907109 = 1857583) B1857583
theorem B3388043 : Blo 578813 3388043 := bstep (se 1 (by rfl) ⟨2541032, by rfl⟩ : syracuseStep 3388043 = 5082065) B5082065
theorem B733951 : Blo 578813 733951 := bstep (se 1 (by rfl) ⟨550463, by rfl⟩ : syracuseStep 733951 = 1100927) B1100927
theorem B5944175 : Blo 578813 5944175 := bstep (se 1 (by rfl) ⟨4458131, by rfl⟩ : syracuseStep 5944175 = 8916263) B8916263
theorem B1652051 : Blo 578813 1652051 := bstep (se 1 (by rfl) ⟨1239038, by rfl⟩ : syracuseStep 1652051 = 2478077) B2478077
theorem B4176623 : Blo 578813 4176623 := bstep (se 1 (by rfl) ⟨3132467, by rfl⟩ : syracuseStep 4176623 = 6264935) B6264935
theorem B28261871 : Blo 578813 28261871 := bstep (se 1 (by rfl) ⟨21196403, by rfl⟩ : syracuseStep 28261871 = 42392807) B42392807
theorem B2212379 : Blo 578813 2212379 := bstep (se 1 (by rfl) ⟨1659284, by rfl⟩ : syracuseStep 2212379 = 3318569) B3318569
theorem B1656733 : Blo 578813 1656733 := bstep (se 3 (by rfl) ⟨310637, by rfl⟩ : syracuseStep 1656733 = 621275) B621275
theorem B870395 : Blo 578813 870395 := bstep (se 1 (by rfl) ⟨652796, by rfl⟩ : syracuseStep 870395 = 1305593) B1305593
theorem B3591049 : Blo 578813 3591049 := bstep (se 2 (by rfl) ⟨1346643, by rfl⟩ : syracuseStep 3591049 = 2693287) B2693287
theorem B2182079 : Blo 578813 2182079 := bstep (se 1 (by rfl) ⟨1636559, by rfl⟩ : syracuseStep 2182079 = 3273119) B3273119
theorem B871367 : Blo 578813 871367 := bstep (se 1 (by rfl) ⟨653525, by rfl⟩ : syracuseStep 871367 = 1307051) B1307051
theorem B1854535 : Blo 578813 1854535 := bstep (se 1 (by rfl) ⟨1390901, by rfl⟩ : syracuseStep 1854535 = 2781803) B2781803
theorem B871679 : Blo 578813 871679 := bstep (se 1 (by rfl) ⟨653759, by rfl⟩ : syracuseStep 871679 = 1307519) B1307519
theorem B871967 : Blo 578813 871967 := bstep (se 1 (by rfl) ⟨653975, by rfl⟩ : syracuseStep 871967 = 1307951) B1307951
theorem B4247113 : Blo 578813 4247113 := bstep (se 2 (by rfl) ⟨1592667, by rfl⟩ : syracuseStep 4247113 = 3185335) B3185335
theorem B2936411 : Blo 578813 2936411 := bstep (se 1 (by rfl) ⟨2202308, by rfl⟩ : syracuseStep 2936411 = 4404617) B4404617
theorem B872159 : Blo 578813 872159 := bstep (se 1 (by rfl) ⟨654119, by rfl⟩ : syracuseStep 872159 = 1308239) B1308239
theorem B1396639 : Blo 578813 1396639 := bstep (se 1 (by rfl) ⟨1047479, by rfl⟩ : syracuseStep 1396639 = 2094959) B2094959
theorem B872489 : Blo 578813 872489 := bstep (se 2 (by rfl) ⟨327183, by rfl⟩ : syracuseStep 872489 = 654367) B654367
theorem B872519 : Blo 578813 872519 := bstep (se 1 (by rfl) ⟨654389, by rfl⟩ : syracuseStep 872519 = 1308779) B1308779
theorem B872687 : Blo 578813 872687 := bstep (se 1 (by rfl) ⟨654515, by rfl⟩ : syracuseStep 872687 = 1309031) B1309031
theorem B3297631 : Blo 578813 3297631 := bstep (se 1 (by rfl) ⟨2473223, by rfl⟩ : syracuseStep 3297631 = 4946447) B4946447
theorem B5591591 : Blo 578813 5591591 := bstep (se 1 (by rfl) ⟨4193693, by rfl⟩ : syracuseStep 5591591 = 8387387) B8387387
theorem B1954529 : Blo 578813 1954529 := bstep (se 2 (by rfl) ⟨732948, by rfl⟩ : syracuseStep 1954529 = 1465897) B1465897
theorem B873641 : Blo 578813 873641 := bstep (se 2 (by rfl) ⟨327615, by rfl⟩ : syracuseStep 873641 = 655231) B655231
theorem B1103311 : Blo 578813 1103311 := bstep (se 1 (by rfl) ⟨827483, by rfl⟩ : syracuseStep 1103311 = 1654967) B1654967
theorem B873935 : Blo 578813 873935 := bstep (se 1 (by rfl) ⟨655451, by rfl⟩ : syracuseStep 873935 = 1310903) B1310903
theorem B579303 : Blo 578813 579303 := bstep (se 1 (by rfl) ⟨434477, by rfl⟩ : syracuseStep 579303 = 868955) B868955
theorem B2349043 : Blo 578813 2349043 := bstep (se 1 (by rfl) ⟨1761782, by rfl⟩ : syracuseStep 2349043 = 3523565) B3523565
theorem B580379 : Blo 578813 580379 := bstep (se 1 (by rfl) ⟨435284, by rfl⟩ : syracuseStep 580379 = 870569) B870569
theorem B580543 : Blo 578813 580543 := bstep (se 1 (by rfl) ⟨435407, by rfl⟩ : syracuseStep 580543 = 870815) B870815
theorem B581147 : Blo 578813 581147 := bstep (se 1 (by rfl) ⟨435860, by rfl⟩ : syracuseStep 581147 = 871721) B871721
theorem B181559069 : Blo 578813 181559069 := bstep (se 3 (by rfl) ⟨34042325, by rfl⟩ : syracuseStep 181559069 = 68084651) B68084651
theorem B4186021 : Blo 578813 4186021 := bstep (se 4 (by rfl) ⟨392439, by rfl⟩ : syracuseStep 4186021 = 784879) B784879
theorem B12738545 : Blo 578813 12738545 := bstep (se 2 (by rfl) ⟨4776954, by rfl⟩ : syracuseStep 12738545 = 9553909) B9553909
theorem B2941433 : Blo 578813 2941433 := bstep (se 2 (by rfl) ⟨1103037, by rfl⟩ : syracuseStep 2941433 = 2206075) B2206075
theorem B2941595 : Blo 578813 2941595 := bstep (se 1 (by rfl) ⟨2206196, by rfl⟩ : syracuseStep 2941595 = 4412393) B4412393
theorem B2324522933 : Blo 578813 2324522933 := bstep (se 5 (by rfl) ⟨108962012, by rfl⟩ : syracuseStep 2324522933 = 217924025) B217924025
theorem B2943215 : Blo 578813 2943215 := bstep (se 1 (by rfl) ⟨2207411, by rfl⟩ : syracuseStep 2943215 = 4414823) B4414823
theorem B812706149 : Blo 578813 812706149 := bstep (se 4 (by rfl) ⟨76191201, by rfl⟩ : syracuseStep 812706149 = 152382403) B152382403
theorem B6613487 : Blo 578813 6613487 := bstep (se 1 (by rfl) ⟨4960115, by rfl⟩ : syracuseStep 6613487 = 9920231) B9920231
theorem B1239551 : Blo 578813 1239551 := bstep (se 1 (by rfl) ⟨929663, by rfl⟩ : syracuseStep 1239551 = 1859327) B1859327
theorem B979951 : Blo 578813 979951 := bstep (se 1 (by rfl) ⟨734963, by rfl⟩ : syracuseStep 979951 = 1469927) B1469927
theorem B203322473 : Blo 578813 203322473 := bstep (se 2 (by rfl) ⟨76245927, by rfl⟩ : syracuseStep 203322473 = 152491855) B152491855
theorem B1963439 : Blo 578813 1963439 := bstep (se 1 (by rfl) ⟨1472579, by rfl⟩ : syracuseStep 1963439 = 2945159) B2945159
theorem B980471 : Blo 578813 980471 := bstep (se 1 (by rfl) ⟨735353, by rfl⟩ : syracuseStep 980471 = 1470707) B1470707
theorem B13563425 : Blo 578813 13563425 := bstep (se 2 (by rfl) ⟨5086284, by rfl⟩ : syracuseStep 13563425 = 10172569) B10172569
theorem B1472489 : Blo 578813 1472489 := bstep (se 2 (by rfl) ⟨552183, by rfl⟩ : syracuseStep 1472489 = 1104367) B1104367
theorem B2947103 : Blo 578813 2947103 := bstep (se 1 (by rfl) ⟨2210327, by rfl⟩ : syracuseStep 2947103 = 4420655) B4420655
theorem B1671131 : Blo 578813 1671131 := bstep (se 1 (by rfl) ⟨1253348, by rfl⟩ : syracuseStep 1671131 = 2506697) B2506697
theorem B1769435 : Blo 578813 1769435 := bstep (se 1 (by rfl) ⟨1327076, by rfl⟩ : syracuseStep 1769435 = 2654153) B2654153
theorem B1310831 : Blo 578813 1310831 := bstep (se 1 (by rfl) ⟨983123, by rfl⟩ : syracuseStep 1310831 = 1966247) B1966247
theorem B1474919 : Blo 578813 1474919 := bstep (se 1 (by rfl) ⟨1106189, by rfl⟩ : syracuseStep 1474919 = 2212379) B2212379
theorem B1115803 : Blo 578813 1115803 := bstep (se 1 (by rfl) ⟨836852, by rfl⟩ : syracuseStep 1115803 = 1673705) B1673705
theorem B135989711 : Blo 578813 135989711 := bstep (se 1 (by rfl) ⟨101992283, by rfl⟩ : syracuseStep 135989711 = 203984567) B203984567
theorem B22613231 : Blo 578813 22613231 := bstep (se 1 (by rfl) ⟨16959923, by rfl⟩ : syracuseStep 22613231 = 33919847) B33919847
theorem B7343759 : Blo 578813 7343759 := bstep (se 1 (by rfl) ⟨5507819, by rfl⟩ : syracuseStep 7343759 = 11015639) B11015639
theorem B4788065 : Blo 578813 4788065 := bstep (se 2 (by rfl) ⟨1795524, by rfl⟩ : syracuseStep 4788065 = 3591049) B3591049
theorem B2200061 : Blo 578813 2200061 := bstep (se 3 (by rfl) ⟨412511, by rfl⟩ : syracuseStep 2200061 = 825023) B825023
theorem B9442169 : Blo 578813 9442169 := bstep (se 2 (by rfl) ⟨3540813, by rfl⟩ : syracuseStep 9442169 = 7081627) B7081627
theorem B8492363 : Blo 578813 8492363 := bstep (se 1 (by rfl) ⟨6369272, by rfl⟩ : syracuseStep 8492363 = 12738545) B12738545
theorem B4396841 : Blo 578813 4396841 := bstep (se 2 (by rfl) ⟨1648815, by rfl⟩ : syracuseStep 4396841 = 3297631) B3297631
theorem B826367 : Blo 578813 826367 := bstep (se 1 (by rfl) ⟨619775, by rfl⟩ : syracuseStep 826367 = 1239551) B1239551
theorem B5581361 : Blo 578813 5581361 := bstep (se 2 (by rfl) ⟨2093010, by rfl⟩ : syracuseStep 5581361 = 4186021) B4186021
theorem B12528229 : Blo 578813 12528229 := bstep (se 4 (by rfl) ⟨1174521, by rfl⟩ : syracuseStep 12528229 = 2349043) B2349043
theorem B32157371 : Blo 578813 32157371 := bstep (se 1 (by rfl) ⟨24118028, by rfl⟩ : syracuseStep 32157371 = 48236057) B48236057
theorem B9450209 : Blo 578813 9450209 := bstep (se 2 (by rfl) ⟨3543828, by rfl⟩ : syracuseStep 9450209 = 7087657) B7087657
theorem B2208977 : Blo 578813 2208977 := bstep (se 2 (by rfl) ⟨828366, by rfl⟩ : syracuseStep 2208977 = 1656733) B1656733
theorem B3716603 : Blo 578813 3716603 := bstep (se 1 (by rfl) ⟨2787452, by rfl⟩ : syracuseStep 3716603 = 5574905) B5574905
theorem B4700683 : Blo 578813 4700683 := bstep (se 1 (by rfl) ⟨3525512, by rfl⟩ : syracuseStep 4700683 = 7051025) B7051025
theorem B2472713 : Blo 578813 2472713 := bstep (se 2 (by rfl) ⟨927267, by rfl⟩ : syracuseStep 2472713 = 1854535) B1854535
theorem B2932361 : Blo 578813 2932361 := bstep (se 2 (by rfl) ⟨1099635, by rfl⟩ : syracuseStep 2932361 = 2199271) B2199271
theorem B4965583 : Blo 578813 4965583 := bstep (se 1 (by rfl) ⟨3724187, by rfl⟩ : syracuseStep 4965583 = 7448375) B7448375
theorem B1549681955 : Blo 578813 1549681955 := bstep (se 1 (by rfl) ⟨1162261466, by rfl⟩ : syracuseStep 1549681955 = 2324522933) B2324522933
theorem B73516415 : Blo 578813 73516415 := bstep (se 1 (by rfl) ⟨55137311, by rfl⟩ : syracuseStep 73516415 = 110274623) B110274623
theorem B541804099 : Blo 578813 541804099 := bstep (se 1 (by rfl) ⟨406353074, by rfl⟩ : syracuseStep 541804099 = 812706149) B812706149
theorem B4408991 : Blo 578813 4408991 := bstep (se 1 (by rfl) ⟨3306743, by rfl⟩ : syracuseStep 4408991 = 6613487) B6613487
theorem B6604739 : Blo 578813 6604739 := bstep (se 1 (by rfl) ⟨4953554, by rfl⟩ : syracuseStep 6604739 = 9907109) B9907109
theorem B5818877 : Blo 578813 5818877 := bstep (se 3 (by rfl) ⟨1091039, by rfl⟩ : syracuseStep 5818877 = 2182079) B2182079
theorem B135548315 : Blo 578813 135548315 := bstep (se 1 (by rfl) ⟨101661236, by rfl⟩ : syracuseStep 135548315 = 203322473) B203322473
theorem B1101367 : Blo 578813 1101367 := bstep (se 1 (by rfl) ⟨826025, by rfl⟩ : syracuseStep 1101367 = 1652051) B1652051
theorem B1398667 : Blo 578813 1398667 := bstep (se 1 (by rfl) ⟨1049000, by rfl⟩ : syracuseStep 1398667 = 2098001) B2098001
theorem B580263 : Blo 578813 580263 := bstep (se 1 (by rfl) ⟨435197, by rfl⟩ : syracuseStep 580263 = 870395) B870395
theorem B14867225 : Blo 578813 14867225 := bstep (se 2 (by rfl) ⟨5575209, by rfl⟩ : syracuseStep 14867225 = 11150419) B11150419
theorem B580911 : Blo 578813 580911 := bstep (se 1 (by rfl) ⟨435683, by rfl⟩ : syracuseStep 580911 = 871367) B871367
theorem B581119 : Blo 578813 581119 := bstep (se 1 (by rfl) ⟨435839, by rfl⟩ : syracuseStep 581119 = 871679) B871679
theorem B581311 : Blo 578813 581311 := bstep (se 1 (by rfl) ⟨435983, by rfl⟩ : syracuseStep 581311 = 871967) B871967
theorem B1957607 : Blo 578813 1957607 := bstep (se 1 (by rfl) ⟨1468205, by rfl⟩ : syracuseStep 1957607 = 2936411) B2936411
theorem B581439 : Blo 578813 581439 := bstep (se 1 (by rfl) ⟨436079, by rfl⟩ : syracuseStep 581439 = 872159) B872159
theorem B581659 : Blo 578813 581659 := bstep (se 1 (by rfl) ⟨436244, by rfl⟩ : syracuseStep 581659 = 872489) B872489
theorem B581679 : Blo 578813 581679 := bstep (se 1 (by rfl) ⟨436259, by rfl⟩ : syracuseStep 581679 = 872519) B872519
theorem B581791 : Blo 578813 581791 := bstep (se 1 (by rfl) ⟨436343, by rfl⟩ : syracuseStep 581791 = 872687) B872687
theorem B3727727 : Blo 578813 3727727 := bstep (se 1 (by rfl) ⟨2795795, by rfl⟩ : syracuseStep 3727727 = 5591591) B5591591
theorem B1303019 : Blo 578813 1303019 := bstep (se 1 (by rfl) ⟨977264, by rfl⟩ : syracuseStep 1303019 = 1954529) B1954529
theorem B4416281 : Blo 578813 4416281 := bstep (se 2 (by rfl) ⟨1656105, by rfl⟩ : syracuseStep 4416281 = 3312211) B3312211
theorem B582427 : Blo 578813 582427 := bstep (se 1 (by rfl) ⟨436820, by rfl⟩ : syracuseStep 582427 = 873641) B873641
theorem B582623 : Blo 578813 582623 := bstep (se 1 (by rfl) ⟨436967, by rfl⟩ : syracuseStep 582623 = 873935) B873935
theorem B5662817 : Blo 578813 5662817 := bstep (se 2 (by rfl) ⟨2123556, by rfl⟩ : syracuseStep 5662817 = 4247113) B4247113
theorem B121039379 : Blo 578813 121039379 := bstep (se 1 (by rfl) ⟨90779534, by rfl⟩ : syracuseStep 121039379 = 181559069) B181559069
theorem B1862185 : Blo 578813 1862185 := bstep (se 2 (by rfl) ⟨698319, by rfl⟩ : syracuseStep 1862185 = 1396639) B1396639
theorem B1960955 : Blo 578813 1960955 := bstep (se 1 (by rfl) ⟨1470716, by rfl⟩ : syracuseStep 1960955 = 2941433) B2941433
theorem B1961063 : Blo 578813 1961063 := bstep (se 1 (by rfl) ⟨1470797, by rfl⟩ : syracuseStep 1961063 = 2941595) B2941595
theorem B978601 : Blo 578813 978601 := bstep (se 2 (by rfl) ⟨366975, by rfl⟩ : syracuseStep 978601 = 733951) B733951
theorem B1306601 : Blo 578813 1306601 := bstep (se 2 (by rfl) ⟨489975, by rfl⟩ : syracuseStep 1306601 = 979951) B979951
theorem B1962143 : Blo 578813 1962143 := bstep (se 1 (by rfl) ⟨1471607, by rfl⟩ : syracuseStep 1962143 = 2943215) B2943215
theorem B1471081 : Blo 578813 1471081 := bstep (se 2 (by rfl) ⟨551655, by rfl⟩ : syracuseStep 1471081 = 1103311) B1103311
theorem B11137661 : Blo 578813 11137661 := bstep (se 3 (by rfl) ⟨2088311, by rfl⟩ : syracuseStep 11137661 = 4176623) B4176623
theorem B2258695 : Blo 578813 2258695 := bstep (se 1 (by rfl) ⟨1694021, by rfl⟩ : syracuseStep 2258695 = 3388043) B3388043
theorem B3962783 : Blo 578813 3962783 := bstep (se 1 (by rfl) ⟨2972087, by rfl⟩ : syracuseStep 3962783 = 5944175) B5944175
theorem B1308959 : Blo 578813 1308959 := bstep (se 1 (by rfl) ⟨981719, by rfl⟩ : syracuseStep 1308959 = 1963439) B1963439
theorem B653647 : Blo 578813 653647 := bstep (se 1 (by rfl) ⟨490235, by rfl⟩ : syracuseStep 653647 = 980471) B980471
theorem B9042283 : Blo 578813 9042283 := bstep (se 1 (by rfl) ⟨6781712, by rfl⟩ : syracuseStep 9042283 = 13563425) B13563425
theorem B981659 : Blo 578813 981659 := bstep (se 1 (by rfl) ⟨736244, by rfl⟩ : syracuseStep 981659 = 1472489) B1472489
theorem B1964735 : Blo 578813 1964735 := bstep (se 1 (by rfl) ⟨1473551, by rfl⟩ : syracuseStep 1964735 = 2947103) B2947103
theorem B18841247 : Blo 578813 18841247 := bstep (se 1 (by rfl) ⟨14130935, by rfl⟩ : syracuseStep 18841247 = 28261871) B28261871
theorem B1179623 : Blo 578813 1179623 := bstep (se 1 (by rfl) ⟨884717, by rfl⟩ : syracuseStep 1179623 = 1769435) B1769435
theorem B1114087 : Blo 578813 1114087 := bstep (se 1 (by rfl) ⟨835565, by rfl⟩ : syracuseStep 1114087 = 1671131) B1671131
theorem B983279 : Blo 578813 983279 := bstep (se 1 (by rfl) ⟨737459, by rfl⟩ : syracuseStep 983279 = 1474919) B1474919
theorem B6620777 : Blo 578813 6620777 := bstep (se 2 (by rfl) ⟨2482791, by rfl⟩ : syracuseStep 6620777 = 4965583) B4965583
theorem B722405465 : Blo 578813 722405465 := bstep (se 2 (by rfl) ⟨270902049, by rfl⟩ : syracuseStep 722405465 = 541804099) B541804099
theorem B15075487 : Blo 578813 15075487 := bstep (se 1 (by rfl) ⟨11306615, by rfl⟩ : syracuseStep 15075487 = 22613231) B22613231
theorem B6294779 : Blo 578813 6294779 := bstep (se 1 (by rfl) ⟨4721084, by rfl⟩ : syracuseStep 6294779 = 9442169) B9442169
theorem B3775211 : Blo 578813 3775211 := bstep (se 1 (by rfl) ⟨2831408, by rfl⟩ : syracuseStep 3775211 = 5662817) B5662817
theorem B2203645 : Blo 578813 2203645 := bstep (se 3 (by rfl) ⟨413183, by rfl⟩ : syracuseStep 2203645 = 826367) B826367
theorem B6300139 : Blo 578813 6300139 := bstep (se 1 (by rfl) ⟨4725104, by rfl⟩ : syracuseStep 6300139 = 9450209) B9450209
theorem B6267577 : Blo 578813 6267577 := bstep (se 2 (by rfl) ⟨2350341, by rfl⟩ : syracuseStep 6267577 = 4700683) B4700683
theorem B1648475 : Blo 578813 1648475 := bstep (se 1 (by rfl) ⟨1236356, by rfl⟩ : syracuseStep 1648475 = 2472713) B2472713
theorem B12560831 : Blo 578813 12560831 := bstep (se 1 (by rfl) ⟨9420623, by rfl⟩ : syracuseStep 12560831 = 18841247) B18841247
theorem B1485449 : Blo 578813 1485449 := bstep (se 2 (by rfl) ⟨557043, by rfl⟩ : syracuseStep 1485449 = 1114087) B1114087
theorem B1033121303 : Blo 578813 1033121303 := bstep (se 1 (by rfl) ⟨774840977, by rfl⟩ : syracuseStep 1033121303 = 1549681955) B1549681955
theorem B4403159 : Blo 578813 4403159 := bstep (se 1 (by rfl) ⟨3302369, by rfl⟩ : syracuseStep 4403159 = 6604739) B6604739
theorem B3879251 : Blo 578813 3879251 := bstep (se 1 (by rfl) ⟨2909438, by rfl⟩ : syracuseStep 3879251 = 5818877) B5818877
theorem B1487737 : Blo 578813 1487737 := bstep (se 2 (by rfl) ⟨557901, by rfl⟩ : syracuseStep 1487737 = 1115803) B1115803
theorem B4895839 : Blo 578813 4895839 := bstep (se 1 (by rfl) ⟨3671879, by rfl⟩ : syracuseStep 4895839 = 7343759) B7343759
theorem B3192043 : Blo 578813 3192043 := bstep (se 1 (by rfl) ⟨2394032, by rfl⟩ : syracuseStep 3192043 = 4788065) B4788065
theorem B2931227 : Blo 578813 2931227 := bstep (se 1 (by rfl) ⟨2198420, by rfl⟩ : syracuseStep 2931227 = 4396841) B4396841
theorem B9911483 : Blo 578813 9911483 := bstep (se 1 (by rfl) ⟨7433612, by rfl⟩ : syracuseStep 9911483 = 14867225) B14867225
theorem B868679 : Blo 578813 868679 := bstep (se 1 (by rfl) ⟨651509, by rfl⟩ : syracuseStep 868679 = 1303019) B1303019
theorem B80692919 : Blo 578813 80692919 := bstep (se 1 (by rfl) ⟨60519689, by rfl⟩ : syracuseStep 80692919 = 121039379) B121039379
theorem B3720907 : Blo 578813 3720907 := bstep (se 1 (by rfl) ⟨2790680, by rfl⟩ : syracuseStep 3720907 = 5581361) B5581361
theorem B871067 : Blo 578813 871067 := bstep (se 1 (by rfl) ⟨653300, by rfl⟩ : syracuseStep 871067 = 1306601) B1306601
theorem B7425107 : Blo 578813 7425107 := bstep (se 1 (by rfl) ⟨5568830, by rfl⟩ : syracuseStep 7425107 = 11137661) B11137661
theorem B871529 : Blo 578813 871529 := bstep (se 2 (by rfl) ⟨326823, by rfl⟩ : syracuseStep 871529 = 653647) B653647
theorem B2477735 : Blo 578813 2477735 := bstep (se 1 (by rfl) ⟨1858301, by rfl⟩ : syracuseStep 2477735 = 3716603) B3716603
theorem B2641855 : Blo 578813 2641855 := bstep (se 1 (by rfl) ⟨1981391, by rfl⟩ : syracuseStep 2641855 = 3962783) B3962783
theorem B12046373 : Blo 578813 12046373 := bstep (se 4 (by rfl) ⟨1129347, by rfl⟩ : syracuseStep 12046373 = 2258695) B2258695
theorem B872639 : Blo 578813 872639 := bstep (se 1 (by rfl) ⟨654479, by rfl⟩ : syracuseStep 872639 = 1308959) B1308959
theorem B1954907 : Blo 578813 1954907 := bstep (se 1 (by rfl) ⟨1466180, by rfl⟩ : syracuseStep 1954907 = 2932361) B2932361
theorem B873887 : Blo 578813 873887 := bstep (se 1 (by rfl) ⟨655415, by rfl⟩ : syracuseStep 873887 = 1310831) B1310831
theorem B2939327 : Blo 578813 2939327 := bstep (se 1 (by rfl) ⟨2204495, by rfl⟩ : syracuseStep 2939327 = 4408991) B4408991
theorem B90659807 : Blo 578813 90659807 := bstep (se 1 (by rfl) ⟨67994855, by rfl⟩ : syracuseStep 90659807 = 135989711) B135989711
theorem B90365543 : Blo 578813 90365543 := bstep (se 1 (by rfl) ⟨67774157, by rfl⟩ : syracuseStep 90365543 = 135548315) B135548315
theorem B1466707 : Blo 578813 1466707 := bstep (se 1 (by rfl) ⟨1100030, by rfl⟩ : syracuseStep 1466707 = 2200061) B2200061
theorem B2482913 : Blo 578813 2482913 := bstep (se 2 (by rfl) ⟨931092, by rfl⟩ : syracuseStep 2482913 = 1862185) B1862185
theorem B16704305 : Blo 578813 16704305 := bstep (se 2 (by rfl) ⟨6264114, by rfl⟩ : syracuseStep 16704305 = 12528229) B12528229
theorem B5661575 : Blo 578813 5661575 := bstep (se 1 (by rfl) ⟨4246181, by rfl⟩ : syracuseStep 5661575 = 8492363) B8492363
theorem B196043773 : Blo 578813 196043773 := bstep (se 3 (by rfl) ⟨36758207, by rfl⟩ : syracuseStep 196043773 = 73516415) B73516415
theorem B1468489 : Blo 578813 1468489 := bstep (se 2 (by rfl) ⟨550683, by rfl⟩ : syracuseStep 1468489 = 1101367) B1101367
theorem B1304801 : Blo 578813 1304801 := bstep (se 2 (by rfl) ⟨489300, by rfl⟩ : syracuseStep 1304801 = 978601) B978601
theorem B1305071 : Blo 578813 1305071 := bstep (se 1 (by rfl) ⟨978803, by rfl⟩ : syracuseStep 1305071 = 1957607) B1957607
theorem B2485151 : Blo 578813 2485151 := bstep (se 1 (by rfl) ⟨1863863, by rfl⟩ : syracuseStep 2485151 = 3727727) B3727727
theorem B2944187 : Blo 578813 2944187 := bstep (se 1 (by rfl) ⟨2208140, by rfl⟩ : syracuseStep 2944187 = 4416281) B4416281
theorem B1961441 : Blo 578813 1961441 := bstep (se 2 (by rfl) ⟨735540, by rfl⟩ : syracuseStep 1961441 = 1471081) B1471081
theorem B1307303 : Blo 578813 1307303 := bstep (se 1 (by rfl) ⟨980477, by rfl⟩ : syracuseStep 1307303 = 1960955) B1960955
theorem B1307375 : Blo 578813 1307375 := bstep (se 1 (by rfl) ⟨980531, by rfl⟩ : syracuseStep 1307375 = 1961063) B1961063
theorem B1864889 : Blo 578813 1864889 := bstep (se 2 (by rfl) ⟨699333, by rfl⟩ : syracuseStep 1864889 = 1398667) B1398667
theorem B1308095 : Blo 578813 1308095 := bstep (se 1 (by rfl) ⟨981071, by rfl⟩ : syracuseStep 1308095 = 1962143) B1962143
theorem B12056377 : Blo 578813 12056377 := bstep (se 2 (by rfl) ⟨4521141, by rfl⟩ : syracuseStep 12056377 = 9042283) B9042283
theorem B1472651 : Blo 578813 1472651 := bstep (se 1 (by rfl) ⟨1104488, by rfl⟩ : syracuseStep 1472651 = 2208977) B2208977
theorem B654439 : Blo 578813 654439 := bstep (se 1 (by rfl) ⟨490829, by rfl⟩ : syracuseStep 654439 = 981659) B981659
theorem B1309823 : Blo 578813 1309823 := bstep (se 1 (by rfl) ⟨982367, by rfl⟩ : syracuseStep 1309823 = 1964735) B1964735
theorem B85752989 : Blo 578813 85752989 := bstep (se 3 (by rfl) ⟨16078685, by rfl⟩ : syracuseStep 85752989 = 32157371) B32157371
theorem B786415 : Blo 578813 786415 := bstep (se 1 (by rfl) ⟨589811, by rfl⟩ : syracuseStep 786415 = 1179623) B1179623
theorem B655519 : Blo 578813 655519 := bstep (se 1 (by rfl) ⟨491639, by rfl⟩ : syracuseStep 655519 = 983279) B983279
theorem B8356769 : Blo 578813 8356769 := bstep (se 2 (by rfl) ⟨3133788, by rfl⟩ : syracuseStep 8356769 = 6267577) B6267577
theorem B261391697 : Blo 578813 261391697 := bstep (se 2 (by rfl) ⟨98021886, by rfl⟩ : syracuseStep 261391697 = 196043773) B196043773
theorem B4950071 : Blo 578813 4950071 := bstep (se 1 (by rfl) ⟨3712553, by rfl⟩ : syracuseStep 4950071 = 7425107) B7425107
theorem B4196519 : Blo 578813 4196519 := bstep (se 1 (by rfl) ⟨3147389, by rfl⟩ : syracuseStep 4196519 = 6294779) B6294779
theorem B8030915 : Blo 578813 8030915 := bstep (se 1 (by rfl) ⟨6023186, by rfl⟩ : syracuseStep 8030915 = 12046373) B12046373
theorem B7934597 : Blo 578813 7934597 := bstep (se 4 (by rfl) ⟨743868, by rfl⟩ : syracuseStep 7934597 = 1487737) B1487737
theorem B3774383 : Blo 578813 3774383 := bstep (se 1 (by rfl) ⟨2830787, by rfl⟩ : syracuseStep 3774383 = 5661575) B5661575
theorem B6527785 : Blo 578813 6527785 := bstep (se 2 (by rfl) ⟨2447919, by rfl⟩ : syracuseStep 6527785 = 4895839) B4895839
theorem B990299 : Blo 578813 990299 := bstep (se 1 (by rfl) ⟨742724, by rfl⟩ : syracuseStep 990299 = 1485449) B1485449
theorem B8400185 : Blo 578813 8400185 := bstep (se 2 (by rfl) ⟨3150069, by rfl⟩ : syracuseStep 8400185 = 6300139) B6300139
theorem B481603643 : Blo 578813 481603643 := bstep (se 1 (by rfl) ⟨361202732, by rfl⟩ : syracuseStep 481603643 = 722405465) B722405465
theorem B4961209 : Blo 578813 4961209 := bstep (se 2 (by rfl) ⟨1860453, by rfl⟩ : syracuseStep 4961209 = 3720907) B3720907
theorem B1651823 : Blo 578813 1651823 := bstep (se 1 (by rfl) ⟨1238867, by rfl⟩ : syracuseStep 1651823 = 2477735) B2477735
theorem B20100649 : Blo 578813 20100649 := bstep (se 2 (by rfl) ⟨7537743, by rfl⟩ : syracuseStep 20100649 = 15075487) B15075487
theorem B60439871 : Blo 578813 60439871 := bstep (se 1 (by rfl) ⟨45329903, by rfl⟩ : syracuseStep 60439871 = 90659807) B90659807
theorem B60243695 : Blo 578813 60243695 := bstep (se 1 (by rfl) ⟨45182771, by rfl⟩ : syracuseStep 60243695 = 90365543) B90365543
theorem B3522473 : Blo 578813 3522473 := bstep (se 2 (by rfl) ⟨1320927, by rfl⟩ : syracuseStep 3522473 = 2641855) B2641855
theorem B1655275 : Blo 578813 1655275 := bstep (se 1 (by rfl) ⟨1241456, by rfl⟩ : syracuseStep 1655275 = 2482913) B2482913
theorem B1098983 : Blo 578813 1098983 := bstep (se 1 (by rfl) ⟨824237, by rfl⟩ : syracuseStep 1098983 = 1648475) B1648475
theorem B869867 : Blo 578813 869867 := bstep (se 1 (by rfl) ⟨652400, by rfl⟩ : syracuseStep 869867 = 1304801) B1304801
theorem B8373887 : Blo 578813 8373887 := bstep (se 1 (by rfl) ⟨6280415, by rfl⟩ : syracuseStep 8373887 = 12560831) B12560831
theorem B870047 : Blo 578813 870047 := bstep (se 1 (by rfl) ⟨652535, by rfl⟩ : syracuseStep 870047 = 1305071) B1305071
theorem B1656767 : Blo 578813 1656767 := bstep (se 1 (by rfl) ⟨1242575, by rfl⟩ : syracuseStep 1656767 = 2485151) B2485151
theorem B16075169 : Blo 578813 16075169 := bstep (se 2 (by rfl) ⟨6028188, by rfl⟩ : syracuseStep 16075169 = 12056377) B12056377
theorem B2935439 : Blo 578813 2935439 := bstep (se 1 (by rfl) ⟨2201579, by rfl⟩ : syracuseStep 2935439 = 4403159) B4403159
theorem B871535 : Blo 578813 871535 := bstep (se 1 (by rfl) ⟨653651, by rfl⟩ : syracuseStep 871535 = 1307303) B1307303
theorem B871583 : Blo 578813 871583 := bstep (se 1 (by rfl) ⟨653687, by rfl⟩ : syracuseStep 871583 = 1307375) B1307375
theorem B872063 : Blo 578813 872063 := bstep (se 1 (by rfl) ⟨654047, by rfl⟩ : syracuseStep 872063 = 1308095) B1308095
theorem B872585 : Blo 578813 872585 := bstep (se 2 (by rfl) ⟨327219, by rfl⟩ : syracuseStep 872585 = 654439) B654439
theorem B1954151 : Blo 578813 1954151 := bstep (se 1 (by rfl) ⟨1465613, by rfl⟩ : syracuseStep 1954151 = 2931227) B2931227
theorem B873215 : Blo 578813 873215 := bstep (se 1 (by rfl) ⟨654911, by rfl⟩ : syracuseStep 873215 = 1309823) B1309823
theorem B57168659 : Blo 578813 57168659 := bstep (se 1 (by rfl) ⟨42876494, by rfl⟩ : syracuseStep 57168659 = 85752989) B85752989
theorem B6607655 : Blo 578813 6607655 := bstep (se 1 (by rfl) ⟨4955741, by rfl⟩ : syracuseStep 6607655 = 9911483) B9911483
theorem B2938193 : Blo 578813 2938193 := bstep (se 2 (by rfl) ⟨1101822, by rfl⟩ : syracuseStep 2938193 = 2203645) B2203645
theorem B579119 : Blo 578813 579119 := bstep (se 1 (by rfl) ⟨434339, by rfl⟩ : syracuseStep 579119 = 868679) B868679
theorem B1955609 : Blo 578813 1955609 := bstep (se 2 (by rfl) ⟨733353, by rfl⟩ : syracuseStep 1955609 = 1466707) B1466707
theorem B4413851 : Blo 578813 4413851 := bstep (se 1 (by rfl) ⟨3310388, by rfl⟩ : syracuseStep 4413851 = 6620777) B6620777
theorem B53795279 : Blo 578813 53795279 := bstep (se 1 (by rfl) ⟨40346459, by rfl⟩ : syracuseStep 53795279 = 80692919) B80692919
theorem B580711 : Blo 578813 580711 := bstep (se 1 (by rfl) ⟨435533, by rfl⟩ : syracuseStep 580711 = 871067) B871067
theorem B581019 : Blo 578813 581019 := bstep (se 1 (by rfl) ⟨435764, by rfl⟩ : syracuseStep 581019 = 871529) B871529
theorem B1957985 : Blo 578813 1957985 := bstep (se 2 (by rfl) ⟨734244, by rfl⟩ : syracuseStep 1957985 = 1468489) B1468489
theorem B581759 : Blo 578813 581759 := bstep (se 1 (by rfl) ⟨436319, by rfl⟩ : syracuseStep 581759 = 872639) B872639
theorem B1303271 : Blo 578813 1303271 := bstep (se 1 (by rfl) ⟨977453, by rfl⟩ : syracuseStep 1303271 = 1954907) B1954907
theorem B582591 : Blo 578813 582591 := bstep (se 1 (by rfl) ⟨436943, by rfl⟩ : syracuseStep 582591 = 873887) B873887
theorem B1959551 : Blo 578813 1959551 := bstep (se 1 (by rfl) ⟨1469663, by rfl⟩ : syracuseStep 1959551 = 2939327) B2939327
theorem B2516807 : Blo 578813 2516807 := bstep (se 1 (by rfl) ⟨1887605, by rfl⟩ : syracuseStep 2516807 = 3775211) B3775211
theorem B11136203 : Blo 578813 11136203 := bstep (se 1 (by rfl) ⟨8352152, by rfl⟩ : syracuseStep 11136203 = 16704305) B16704305
theorem B4256057 : Blo 578813 4256057 := bstep (se 2 (by rfl) ⟨1596021, by rfl⟩ : syracuseStep 4256057 = 3192043) B3192043
theorem B1962791 : Blo 578813 1962791 := bstep (se 1 (by rfl) ⟨1472093, by rfl⟩ : syracuseStep 1962791 = 2944187) B2944187
theorem B1307627 : Blo 578813 1307627 := bstep (se 1 (by rfl) ⟨980720, by rfl⟩ : syracuseStep 1307627 = 1961441) B1961441
theorem B688747535 : Blo 578813 688747535 := bstep (se 1 (by rfl) ⟨516560651, by rfl⟩ : syracuseStep 688747535 = 1033121303) B1033121303
theorem B2586167 : Blo 578813 2586167 := bstep (se 1 (by rfl) ⟨1939625, by rfl⟩ : syracuseStep 2586167 = 3879251) B3879251
theorem B1243259 : Blo 578813 1243259 := bstep (se 1 (by rfl) ⟨932444, by rfl⟩ : syracuseStep 1243259 = 1864889) B1864889
theorem B981767 : Blo 578813 981767 := bstep (se 1 (by rfl) ⟨736325, by rfl⟩ : syracuseStep 981767 = 1472651) B1472651
theorem B1048553 : Blo 578813 1048553 := bstep (se 2 (by rfl) ⟨393207, by rfl⟩ : syracuseStep 1048553 = 786415) B786415
theorem B5571179 : Blo 578813 5571179 := bstep (se 1 (by rfl) ⟨4178384, by rfl⟩ : syracuseStep 5571179 = 8356769) B8356769
theorem B174261131 : Blo 578813 174261131 := bstep (se 1 (by rfl) ⟨130695848, by rfl⟩ : syracuseStep 174261131 = 261391697) B261391697
theorem B10716779 : Blo 578813 10716779 := bstep (se 1 (by rfl) ⟨8037584, by rfl⟩ : syracuseStep 10716779 = 16075169) B16075169
theorem B38112439 : Blo 578813 38112439 := bstep (se 1 (by rfl) ⟨28584329, by rfl⟩ : syracuseStep 38112439 = 57168659) B57168659
theorem B660199 : Blo 578813 660199 := bstep (se 1 (by rfl) ⟨495149, by rfl⟩ : syracuseStep 660199 = 990299) B990299
theorem B1677871 : Blo 578813 1677871 := bstep (se 1 (by rfl) ⟨1258403, by rfl⟩ : syracuseStep 1677871 = 2516807) B2516807
theorem B321069095 : Blo 578813 321069095 := bstep (se 1 (by rfl) ⟨240801821, by rfl⟩ : syracuseStep 321069095 = 481603643) B481603643
theorem B828839 : Blo 578813 828839 := bstep (se 1 (by rfl) ⟨621629, by rfl⟩ : syracuseStep 828839 = 1243259) B1243259
theorem B699035 : Blo 578813 699035 := bstep (se 1 (by rfl) ⟨524276, by rfl⟩ : syracuseStep 699035 = 1048553) B1048553
theorem B2207033 : Blo 578813 2207033 := bstep (se 2 (by rfl) ⟨827637, by rfl⟩ : syracuseStep 2207033 = 1655275) B1655275
theorem B732655 : Blo 578813 732655 := bstep (se 1 (by rfl) ⟨549491, by rfl⟩ : syracuseStep 732655 = 1098983) B1098983
theorem B5582591 : Blo 578813 5582591 := bstep (se 1 (by rfl) ⟨4186943, by rfl⟩ : syracuseStep 5582591 = 8373887) B8373887
theorem B2797679 : Blo 578813 2797679 := bstep (se 1 (by rfl) ⟨2098259, by rfl⟩ : syracuseStep 2797679 = 4196519) B4196519
theorem B5353943 : Blo 578813 5353943 := bstep (se 1 (by rfl) ⟨4015457, by rfl⟩ : syracuseStep 5353943 = 8030915) B8030915
theorem B5289731 : Blo 578813 5289731 := bstep (se 1 (by rfl) ⟨3967298, by rfl⟩ : syracuseStep 5289731 = 7934597) B7934597
theorem B4405103 : Blo 578813 4405103 := bstep (se 1 (by rfl) ⟨3303827, by rfl⟩ : syracuseStep 4405103 = 6607655) B6607655
theorem B35863519 : Blo 578813 35863519 := bstep (se 1 (by rfl) ⟨26897639, by rfl⟩ : syracuseStep 35863519 = 53795279) B53795279
theorem B868847 : Blo 578813 868847 := bstep (se 1 (by rfl) ⟨651635, by rfl⟩ : syracuseStep 868847 = 1303271) B1303271
theorem B7424135 : Blo 578813 7424135 := bstep (se 1 (by rfl) ⟨5568101, by rfl⟩ : syracuseStep 7424135 = 11136203) B11136203
theorem B2837371 : Blo 578813 2837371 := bstep (se 1 (by rfl) ⟨2128028, by rfl⟩ : syracuseStep 2837371 = 4256057) B4256057
theorem B871751 : Blo 578813 871751 := bstep (se 1 (by rfl) ⟨653813, by rfl⟩ : syracuseStep 871751 = 1307627) B1307627
theorem B459165023 : Blo 578813 459165023 := bstep (se 1 (by rfl) ⟨344373767, by rfl⟩ : syracuseStep 459165023 = 688747535) B688747535
theorem B1101215 : Blo 578813 1101215 := bstep (se 1 (by rfl) ⟨825911, by rfl⟩ : syracuseStep 1101215 = 1651823) B1651823
theorem B1724111 : Blo 578813 1724111 := bstep (se 1 (by rfl) ⟨1293083, by rfl⟩ : syracuseStep 1724111 = 2586167) B2586167
theorem B8703713 : Blo 578813 8703713 := bstep (se 2 (by rfl) ⟨3263892, by rfl⟩ : syracuseStep 8703713 = 6527785) B6527785
theorem B40293247 : Blo 578813 40293247 := bstep (se 1 (by rfl) ⟨30219935, by rfl⟩ : syracuseStep 40293247 = 60439871) B60439871
theorem B40162463 : Blo 578813 40162463 := bstep (se 1 (by rfl) ⟨30121847, by rfl⟩ : syracuseStep 40162463 = 60243695) B60243695
theorem B2348315 : Blo 578813 2348315 := bstep (se 1 (by rfl) ⟨1761236, by rfl⟩ : syracuseStep 2348315 = 3522473) B3522473
theorem B874025 : Blo 578813 874025 := bstep (se 2 (by rfl) ⟨327759, by rfl⟩ : syracuseStep 874025 = 655519) B655519
theorem B579911 : Blo 578813 579911 := bstep (se 1 (by rfl) ⟨434933, by rfl⟩ : syracuseStep 579911 = 869867) B869867
theorem B580031 : Blo 578813 580031 := bstep (se 1 (by rfl) ⟨435023, by rfl⟩ : syracuseStep 580031 = 870047) B870047
theorem B1104511 : Blo 578813 1104511 := bstep (se 1 (by rfl) ⟨828383, by rfl⟩ : syracuseStep 1104511 = 1656767) B1656767
theorem B3300047 : Blo 578813 3300047 := bstep (se 1 (by rfl) ⟨2475035, by rfl⟩ : syracuseStep 3300047 = 4950071) B4950071
theorem B1956959 : Blo 578813 1956959 := bstep (se 1 (by rfl) ⟨1467719, by rfl⟩ : syracuseStep 1956959 = 2935439) B2935439
theorem B581023 : Blo 578813 581023 := bstep (se 1 (by rfl) ⟨435767, by rfl⟩ : syracuseStep 581023 = 871535) B871535
theorem B581055 : Blo 578813 581055 := bstep (se 1 (by rfl) ⟨435791, by rfl⟩ : syracuseStep 581055 = 871583) B871583
theorem B581375 : Blo 578813 581375 := bstep (se 1 (by rfl) ⟨436031, by rfl⟩ : syracuseStep 581375 = 872063) B872063
theorem B581723 : Blo 578813 581723 := bstep (se 1 (by rfl) ⟨436292, by rfl⟩ : syracuseStep 581723 = 872585) B872585
theorem B1302767 : Blo 578813 1302767 := bstep (se 1 (by rfl) ⟨977075, by rfl⟩ : syracuseStep 1302767 = 1954151) B1954151
theorem B582143 : Blo 578813 582143 := bstep (se 1 (by rfl) ⟨436607, by rfl⟩ : syracuseStep 582143 = 873215) B873215
theorem B1958795 : Blo 578813 1958795 := bstep (se 1 (by rfl) ⟨1469096, by rfl⟩ : syracuseStep 1958795 = 2938193) B2938193
theorem B1303739 : Blo 578813 1303739 := bstep (se 1 (by rfl) ⟨977804, by rfl⟩ : syracuseStep 1303739 = 1955609) B1955609
theorem B2516255 : Blo 578813 2516255 := bstep (se 1 (by rfl) ⟨1887191, by rfl⟩ : syracuseStep 2516255 = 3774383) B3774383
theorem B2942567 : Blo 578813 2942567 := bstep (se 1 (by rfl) ⟨2206925, by rfl⟩ : syracuseStep 2942567 = 4413851) B4413851
theorem B1305323 : Blo 578813 1305323 := bstep (se 1 (by rfl) ⟨978992, by rfl⟩ : syracuseStep 1305323 = 1957985) B1957985
theorem B1306367 : Blo 578813 1306367 := bstep (se 1 (by rfl) ⟨979775, by rfl⟩ : syracuseStep 1306367 = 1959551) B1959551
theorem B6614945 : Blo 578813 6614945 := bstep (se 2 (by rfl) ⟨2480604, by rfl⟩ : syracuseStep 6614945 = 4961209) B4961209
theorem B26800865 : Blo 578813 26800865 := bstep (se 2 (by rfl) ⟨10050324, by rfl⟩ : syracuseStep 26800865 = 20100649) B20100649
theorem B5600123 : Blo 578813 5600123 := bstep (se 1 (by rfl) ⟨4200092, by rfl⟩ : syracuseStep 5600123 = 8400185) B8400185
theorem B1308527 : Blo 578813 1308527 := bstep (se 1 (by rfl) ⟨981395, by rfl⟩ : syracuseStep 1308527 = 1962791) B1962791
theorem B654511 : Blo 578813 654511 := bstep (se 1 (by rfl) ⟨490883, by rfl⟩ : syracuseStep 654511 = 981767) B981767
theorem B7144519 : Blo 578813 7144519 := bstep (se 1 (by rfl) ⟨5358389, by rfl⟩ : syracuseStep 7144519 = 10716779) B10716779
theorem B4949423 : Blo 578813 4949423 := bstep (se 1 (by rfl) ⟨3712067, by rfl⟩ : syracuseStep 4949423 = 7424135) B7424135
theorem B1149407 : Blo 578813 1149407 := bstep (se 1 (by rfl) ⟨862055, by rfl⟩ : syracuseStep 1149407 = 1724111) B1724111
theorem B26774975 : Blo 578813 26774975 := bstep (se 1 (by rfl) ⟨20081231, by rfl⟩ : syracuseStep 26774975 = 40162463) B40162463
theorem B2200031 : Blo 578813 2200031 := bstep (se 1 (by rfl) ⟨1650023, by rfl⟩ : syracuseStep 2200031 = 3300047) B3300047
theorem B214046063 : Blo 578813 214046063 := bstep (se 1 (by rfl) ⟨160534547, by rfl⟩ : syracuseStep 214046063 = 321069095) B321069095
theorem B1677503 : Blo 578813 1677503 := bstep (se 1 (by rfl) ⟨1258127, by rfl⟩ : syracuseStep 1677503 = 2516255) B2516255
theorem B17867243 : Blo 578813 17867243 := bstep (se 1 (by rfl) ⟨13400432, by rfl⟩ : syracuseStep 17867243 = 26800865) B26800865
theorem B2237161 : Blo 578813 2237161 := bstep (se 2 (by rfl) ⟨838935, by rfl⟩ : syracuseStep 2237161 = 1677871) B1677871
theorem B47818025 : Blo 578813 47818025 := bstep (se 2 (by rfl) ⟨17931759, by rfl⟩ : syracuseStep 47818025 = 35863519) B35863519
theorem B23209901 : Blo 578813 23209901 := bstep (se 3 (by rfl) ⟨4351856, by rfl⟩ : syracuseStep 23209901 = 8703713) B8703713
theorem B3714119 : Blo 578813 3714119 := bstep (se 1 (by rfl) ⟨2785589, by rfl⟩ : syracuseStep 3714119 = 5571179) B5571179
theorem B116174087 : Blo 578813 116174087 := bstep (se 1 (by rfl) ⟨87130565, by rfl⟩ : syracuseStep 116174087 = 174261131) B174261131
theorem B2210237 : Blo 578813 2210237 := bstep (se 3 (by rfl) ⟨414419, by rfl⟩ : syracuseStep 2210237 = 828839) B828839
theorem B3783161 : Blo 578813 3783161 := bstep (se 2 (by rfl) ⟨1418685, by rfl⟩ : syracuseStep 3783161 = 2837371) B2837371
theorem B868511 : Blo 578813 868511 := bstep (se 1 (by rfl) ⟨651383, by rfl⟩ : syracuseStep 868511 = 1302767) B1302767
theorem B869159 : Blo 578813 869159 := bstep (se 1 (by rfl) ⟨651869, by rfl⟩ : syracuseStep 869159 = 1303739) B1303739
theorem B53724329 : Blo 578813 53724329 := bstep (se 2 (by rfl) ⟨20146623, by rfl⟩ : syracuseStep 53724329 = 40293247) B40293247
theorem B7456373 : Blo 578813 7456373 := bstep (se 5 (by rfl) ⟨349517, by rfl⟩ : syracuseStep 7456373 = 699035) B699035
theorem B870215 : Blo 578813 870215 := bstep (se 1 (by rfl) ⟨652661, by rfl⟩ : syracuseStep 870215 = 1305323) B1305323
theorem B870911 : Blo 578813 870911 := bstep (se 1 (by rfl) ⟨653183, by rfl⟩ : syracuseStep 870911 = 1306367) B1306367
theorem B3721727 : Blo 578813 3721727 := bstep (se 1 (by rfl) ⟨2791295, by rfl⟩ : syracuseStep 3721727 = 5582591) B5582591
theorem B4409963 : Blo 578813 4409963 := bstep (se 1 (by rfl) ⟨3307472, by rfl⟩ : syracuseStep 4409963 = 6614945) B6614945
theorem B2936573 : Blo 578813 2936573 := bstep (se 3 (by rfl) ⟨550607, by rfl⟩ : syracuseStep 2936573 = 1101215) B1101215
theorem B3526487 : Blo 578813 3526487 := bstep (se 1 (by rfl) ⟨2644865, by rfl⟩ : syracuseStep 3526487 = 5289731) B5289731
theorem B2936735 : Blo 578813 2936735 := bstep (se 1 (by rfl) ⟨2202551, by rfl⟩ : syracuseStep 2936735 = 4405103) B4405103
theorem B872351 : Blo 578813 872351 := bstep (se 1 (by rfl) ⟨654263, by rfl⟩ : syracuseStep 872351 = 1308527) B1308527
theorem B872681 : Blo 578813 872681 := bstep (se 2 (by rfl) ⟨327255, by rfl⟩ : syracuseStep 872681 = 654511) B654511
theorem B579231 : Blo 578813 579231 := bstep (se 1 (by rfl) ⟨434423, by rfl⟩ : syracuseStep 579231 = 868847) B868847
theorem B14277181 : Blo 578813 14277181 := bstep (se 3 (by rfl) ⟨2676971, by rfl⟩ : syracuseStep 14277181 = 5353943) B5353943
theorem B581167 : Blo 578813 581167 := bstep (se 1 (by rfl) ⟨435875, by rfl⟩ : syracuseStep 581167 = 871751) B871751
theorem B306110015 : Blo 578813 306110015 := bstep (se 1 (by rfl) ⟨229582511, by rfl⟩ : syracuseStep 306110015 = 459165023) B459165023
theorem B1565543 : Blo 578813 1565543 := bstep (se 1 (by rfl) ⟨1174157, by rfl⟩ : syracuseStep 1565543 = 2348315) B2348315
theorem B582683 : Blo 578813 582683 := bstep (se 1 (by rfl) ⟨437012, by rfl⟩ : syracuseStep 582683 = 874025) B874025
theorem B50816585 : Blo 578813 50816585 := bstep (se 2 (by rfl) ⟨19056219, by rfl⟩ : syracuseStep 50816585 = 38112439) B38112439
theorem B976873 : Blo 578813 976873 := bstep (se 2 (by rfl) ⟨366327, by rfl⟩ : syracuseStep 976873 = 732655) B732655
theorem B1304639 : Blo 578813 1304639 := bstep (se 1 (by rfl) ⟨978479, by rfl⟩ : syracuseStep 1304639 = 1956959) B1956959
theorem B1305863 : Blo 578813 1305863 := bstep (se 1 (by rfl) ⟨979397, by rfl⟩ : syracuseStep 1305863 = 1958795) B1958795
theorem B880265 : Blo 578813 880265 := bstep (se 2 (by rfl) ⟨330099, by rfl⟩ : syracuseStep 880265 = 660199) B660199
theorem B1961711 : Blo 578813 1961711 := bstep (se 1 (by rfl) ⟨1471283, by rfl⟩ : syracuseStep 1961711 = 2942567) B2942567
theorem B1471355 : Blo 578813 1471355 := bstep (se 1 (by rfl) ⟨1103516, by rfl⟩ : syracuseStep 1471355 = 2207033) B2207033
theorem B1865119 : Blo 578813 1865119 := bstep (se 1 (by rfl) ⟨1398839, by rfl⟩ : syracuseStep 1865119 = 2797679) B2797679
theorem B3733415 : Blo 578813 3733415 := bstep (se 1 (by rfl) ⟨2800061, by rfl⟩ : syracuseStep 3733415 = 5600123) B5600123
theorem B1472681 : Blo 578813 1472681 := bstep (se 2 (by rfl) ⟨552255, by rfl⟩ : syracuseStep 1472681 = 1104511) B1104511
theorem B35816219 : Blo 578813 35816219 := bstep (se 1 (by rfl) ⟨26862164, by rfl⟩ : syracuseStep 35816219 = 53724329) B53724329
theorem B2982881 : Blo 578813 2982881 := bstep (se 2 (by rfl) ⟨1118580, by rfl⟩ : syracuseStep 2982881 = 2237161) B2237161
theorem B47645981 : Blo 578813 47645981 := bstep (se 3 (by rfl) ⟨8933621, by rfl⟩ : syracuseStep 47645981 = 17867243) B17867243
theorem B1118335 : Blo 578813 1118335 := bstep (se 1 (by rfl) ⟨838751, by rfl⟩ : syracuseStep 1118335 = 1677503) B1677503
theorem B15473267 : Blo 578813 15473267 := bstep (se 1 (by rfl) ⟨11604950, by rfl⟩ : syracuseStep 15473267 = 23209901) B23209901
theorem B766271 : Blo 578813 766271 := bstep (se 1 (by rfl) ⟨574703, by rfl⟩ : syracuseStep 766271 = 1149407) B1149407
theorem B135510893 : Blo 578813 135510893 := bstep (se 3 (by rfl) ⟨25408292, by rfl⟩ : syracuseStep 135510893 = 50816585) B50816585
theorem B869759 : Blo 578813 869759 := bstep (se 1 (by rfl) ⟨652319, by rfl⟩ : syracuseStep 869759 = 1304639) B1304639
theorem B2476079 : Blo 578813 2476079 := bstep (se 1 (by rfl) ⟨1857059, by rfl⟩ : syracuseStep 2476079 = 3714119) B3714119
theorem B870575 : Blo 578813 870575 := bstep (se 1 (by rfl) ⟨652931, by rfl⟩ : syracuseStep 870575 = 1305863) B1305863
theorem B77449391 : Blo 578813 77449391 := bstep (se 1 (by rfl) ⟨58087043, by rfl⟩ : syracuseStep 77449391 = 116174087) B116174087
theorem B2347373 : Blo 578813 2347373 := bstep (se 3 (by rfl) ⟨440132, by rfl⟩ : syracuseStep 2347373 = 880265) B880265
theorem B579007 : Blo 578813 579007 := bstep (se 1 (by rfl) ⟨434255, by rfl⟩ : syracuseStep 579007 = 868511) B868511
theorem B579439 : Blo 578813 579439 := bstep (se 1 (by rfl) ⟨434579, by rfl⟩ : syracuseStep 579439 = 869159) B869159
theorem B3299615 : Blo 578813 3299615 := bstep (se 1 (by rfl) ⟨2474711, by rfl⟩ : syracuseStep 3299615 = 4949423) B4949423
theorem B4970915 : Blo 578813 4970915 := bstep (se 1 (by rfl) ⟨3728186, by rfl⟩ : syracuseStep 4970915 = 7456373) B7456373
theorem B580143 : Blo 578813 580143 := bstep (se 1 (by rfl) ⟨435107, by rfl⟩ : syracuseStep 580143 = 870215) B870215
theorem B9526025 : Blo 578813 9526025 := bstep (se 2 (by rfl) ⟨3572259, by rfl⟩ : syracuseStep 9526025 = 7144519) B7144519
theorem B580607 : Blo 578813 580607 := bstep (se 1 (by rfl) ⟨435455, by rfl⟩ : syracuseStep 580607 = 870911) B870911
theorem B2939975 : Blo 578813 2939975 := bstep (se 1 (by rfl) ⟨2204981, by rfl⟩ : syracuseStep 2939975 = 4409963) B4409963
theorem B17849983 : Blo 578813 17849983 := bstep (se 1 (by rfl) ⟨13387487, by rfl⟩ : syracuseStep 17849983 = 26774975) B26774975
theorem B1957715 : Blo 578813 1957715 := bstep (se 1 (by rfl) ⟨1468286, by rfl⟩ : syracuseStep 1957715 = 2936573) B2936573
theorem B2350991 : Blo 578813 2350991 := bstep (se 1 (by rfl) ⟨1763243, by rfl⟩ : syracuseStep 2350991 = 3526487) B3526487
theorem B1957823 : Blo 578813 1957823 := bstep (se 1 (by rfl) ⟨1468367, by rfl⟩ : syracuseStep 1957823 = 2936735) B2936735
theorem B581567 : Blo 578813 581567 := bstep (se 1 (by rfl) ⟨436175, by rfl⟩ : syracuseStep 581567 = 872351) B872351
theorem B1302497 : Blo 578813 1302497 := bstep (se 2 (by rfl) ⟨488436, by rfl⟩ : syracuseStep 1302497 = 976873) B976873
theorem B581787 : Blo 578813 581787 := bstep (se 1 (by rfl) ⟨436340, by rfl⟩ : syracuseStep 581787 = 872681) B872681
theorem B1466687 : Blo 578813 1466687 := bstep (se 1 (by rfl) ⟨1100015, by rfl⟩ : syracuseStep 1466687 = 2200031) B2200031
theorem B142697375 : Blo 578813 142697375 := bstep (se 1 (by rfl) ⟨107023031, by rfl⟩ : syracuseStep 142697375 = 214046063) B214046063
theorem B204073343 : Blo 578813 204073343 := bstep (se 1 (by rfl) ⟨153055007, by rfl⟩ : syracuseStep 204073343 = 306110015) B306110015
theorem B1043695 : Blo 578813 1043695 := bstep (se 1 (by rfl) ⟨782771, by rfl⟩ : syracuseStep 1043695 = 1565543) B1565543
theorem B31878683 : Blo 578813 31878683 := bstep (se 1 (by rfl) ⟨23909012, by rfl⟩ : syracuseStep 31878683 = 47818025) B47818025
theorem B9924605 : Blo 578813 9924605 := bstep (se 3 (by rfl) ⟨1860863, by rfl⟩ : syracuseStep 9924605 = 3721727) B3721727
theorem B2486825 : Blo 578813 2486825 := bstep (se 2 (by rfl) ⟨932559, by rfl⟩ : syracuseStep 2486825 = 1865119) B1865119
theorem B1307807 : Blo 578813 1307807 := bstep (se 1 (by rfl) ⟨980855, by rfl⟩ : syracuseStep 1307807 = 1961711) B1961711
theorem B980903 : Blo 578813 980903 := bstep (se 1 (by rfl) ⟨735677, by rfl⟩ : syracuseStep 980903 = 1471355) B1471355
theorem B19036241 : Blo 578813 19036241 := bstep (se 2 (by rfl) ⟨7138590, by rfl⟩ : syracuseStep 19036241 = 14277181) B14277181
theorem B2488943 : Blo 578813 2488943 := bstep (se 1 (by rfl) ⟨1866707, by rfl⟩ : syracuseStep 2488943 = 3733415) B3733415
theorem B981787 : Blo 578813 981787 := bstep (se 1 (by rfl) ⟨736340, by rfl⟩ : syracuseStep 981787 = 1472681) B1472681
theorem B1473491 : Blo 578813 1473491 := bstep (se 1 (by rfl) ⟨1105118, by rfl⟩ : syracuseStep 1473491 = 2210237) B2210237
theorem B2522107 : Blo 578813 2522107 := bstep (se 1 (by rfl) ⟨1891580, by rfl⟩ : syracuseStep 2522107 = 3783161) B3783161
theorem B2199743 : Blo 578813 2199743 := bstep (se 1 (by rfl) ⟨1649807, by rfl⟩ : syracuseStep 2199743 = 3299615) B3299615
theorem B3313943 : Blo 578813 3313943 := bstep (se 1 (by rfl) ⟨2485457, by rfl⟩ : syracuseStep 3313943 = 4970915) B4970915
theorem B95131583 : Blo 578813 95131583 := bstep (se 1 (by rfl) ⟨71348687, by rfl⟩ : syracuseStep 95131583 = 142697375) B142697375
theorem B12690827 : Blo 578813 12690827 := bstep (se 1 (by rfl) ⟨9518120, by rfl⟩ : syracuseStep 12690827 = 19036241) B19036241
theorem B23799977 : Blo 578813 23799977 := bstep (se 2 (by rfl) ⟨8924991, by rfl⟩ : syracuseStep 23799977 = 17849983) B17849983
theorem B6269309 : Blo 578813 6269309 := bstep (se 3 (by rfl) ⟨1175495, by rfl⟩ : syracuseStep 6269309 = 2350991) B2350991
theorem B2043389 : Blo 578813 2043389 := bstep (se 3 (by rfl) ⟨383135, by rfl⟩ : syracuseStep 2043389 = 766271) B766271
theorem B31763987 : Blo 578813 31763987 := bstep (se 1 (by rfl) ⟨23822990, by rfl⟩ : syracuseStep 31763987 = 47645981) B47645981
theorem B1650719 : Blo 578813 1650719 := bstep (se 1 (by rfl) ⟨1238039, by rfl⟩ : syracuseStep 1650719 = 2476079) B2476079
theorem B1391593 : Blo 578813 1391593 := bstep (se 2 (by rfl) ⟨521847, by rfl⟩ : syracuseStep 1391593 = 1043695) B1043695
theorem B868331 : Blo 578813 868331 := bstep (se 1 (by rfl) ⟨651248, by rfl⟩ : syracuseStep 868331 = 1302497) B1302497
theorem B1491113 : Blo 578813 1491113 := bstep (se 2 (by rfl) ⟨559167, by rfl⟩ : syracuseStep 1491113 = 1118335) B1118335
theorem B21252455 : Blo 578813 21252455 := bstep (se 1 (by rfl) ⟨15939341, by rfl⟩ : syracuseStep 21252455 = 31878683) B31878683
theorem B1657883 : Blo 578813 1657883 := bstep (se 1 (by rfl) ⟨1243412, by rfl⟩ : syracuseStep 1657883 = 2486825) B2486825
theorem B871871 : Blo 578813 871871 := bstep (se 1 (by rfl) ⟨653903, by rfl⟩ : syracuseStep 871871 = 1307807) B1307807
theorem B3362809 : Blo 578813 3362809 := bstep (se 2 (by rfl) ⟨1261053, by rfl⟩ : syracuseStep 3362809 = 2522107) B2522107
theorem B1659295 : Blo 578813 1659295 := bstep (se 1 (by rfl) ⟨1244471, by rfl⟩ : syracuseStep 1659295 = 2488943) B2488943
theorem B23877479 : Blo 578813 23877479 := bstep (se 1 (by rfl) ⟨17908109, by rfl⟩ : syracuseStep 23877479 = 35816219) B35816219
theorem B1988587 : Blo 578813 1988587 := bstep (se 1 (by rfl) ⟨1491440, by rfl⟩ : syracuseStep 1988587 = 2982881) B2982881
theorem B579839 : Blo 578813 579839 := bstep (se 1 (by rfl) ⟨434879, by rfl⟩ : syracuseStep 579839 = 869759) B869759
theorem B580383 : Blo 578813 580383 := bstep (se 1 (by rfl) ⟨435287, by rfl⟩ : syracuseStep 580383 = 870575) B870575
theorem B51632927 : Blo 578813 51632927 := bstep (se 1 (by rfl) ⟨38724695, by rfl⟩ : syracuseStep 51632927 = 77449391) B77449391
theorem B1564915 : Blo 578813 1564915 := bstep (se 1 (by rfl) ⟨1173686, by rfl⟩ : syracuseStep 1564915 = 2347373) B2347373
theorem B10315511 : Blo 578813 10315511 := bstep (se 1 (by rfl) ⟨7736633, by rfl⟩ : syracuseStep 10315511 = 15473267) B15473267
theorem B6350683 : Blo 578813 6350683 := bstep (se 1 (by rfl) ⟨4763012, by rfl⟩ : syracuseStep 6350683 = 9526025) B9526025
theorem B1959983 : Blo 578813 1959983 := bstep (se 1 (by rfl) ⟨1469987, by rfl⟩ : syracuseStep 1959983 = 2939975) B2939975
theorem B1305143 : Blo 578813 1305143 := bstep (se 1 (by rfl) ⟨978857, by rfl⟩ : syracuseStep 1305143 = 1957715) B1957715
theorem B1305215 : Blo 578813 1305215 := bstep (se 1 (by rfl) ⟨978911, by rfl⟩ : syracuseStep 1305215 = 1957823) B1957823
theorem B977791 : Blo 578813 977791 := bstep (se 1 (by rfl) ⟨733343, by rfl⟩ : syracuseStep 977791 = 1466687) B1466687
theorem B136048895 : Blo 578813 136048895 := bstep (se 1 (by rfl) ⟨102036671, by rfl⟩ : syracuseStep 136048895 = 204073343) B204073343
theorem B6616403 : Blo 578813 6616403 := bstep (se 1 (by rfl) ⟨4962302, by rfl⟩ : syracuseStep 6616403 = 9924605) B9924605
theorem B1309049 : Blo 578813 1309049 := bstep (se 2 (by rfl) ⟨490893, by rfl⟩ : syracuseStep 1309049 = 981787) B981787
theorem B653935 : Blo 578813 653935 := bstep (se 1 (by rfl) ⟨490451, by rfl⟩ : syracuseStep 653935 = 980903) B980903
theorem B90340595 : Blo 578813 90340595 := bstep (se 1 (by rfl) ⟨67755446, by rfl⟩ : syracuseStep 90340595 = 135510893) B135510893
theorem B982327 : Blo 578813 982327 := bstep (se 1 (by rfl) ⟨736745, by rfl⟩ : syracuseStep 982327 = 1473491) B1473491
theorem B8460551 : Blo 578813 8460551 := bstep (se 1 (by rfl) ⟨6345413, by rfl⟩ : syracuseStep 8460551 = 12690827) B12690827
theorem B15866651 : Blo 578813 15866651 := bstep (se 1 (by rfl) ⟨11899988, by rfl⟩ : syracuseStep 15866651 = 23799977) B23799977
theorem B21175991 : Blo 578813 21175991 := bstep (se 1 (by rfl) ⟨15881993, by rfl⟩ : syracuseStep 21175991 = 31763987) B31763987
theorem B5449037 : Blo 578813 5449037 := bstep (se 3 (by rfl) ⟨1021694, by rfl⟩ : syracuseStep 5449037 = 2043389) B2043389
theorem B994075 : Blo 578813 994075 := bstep (se 1 (by rfl) ⟨745556, by rfl⟩ : syracuseStep 994075 = 1491113) B1491113
theorem B14168303 : Blo 578813 14168303 := bstep (se 1 (by rfl) ⟨10626227, by rfl⟩ : syracuseStep 14168303 = 21252455) B21252455
theorem B8467577 : Blo 578813 8467577 := bstep (se 2 (by rfl) ⟨3175341, by rfl⟩ : syracuseStep 8467577 = 6350683) B6350683
theorem B2209295 : Blo 578813 2209295 := bstep (se 1 (by rfl) ⟨1656971, by rfl⟩ : syracuseStep 2209295 = 3313943) B3313943
theorem B63421055 : Blo 578813 63421055 := bstep (se 1 (by rfl) ⟨47565791, by rfl⟩ : syracuseStep 63421055 = 95131583) B95131583
theorem B34421951 : Blo 578813 34421951 := bstep (se 1 (by rfl) ⟨25816463, by rfl⟩ : syracuseStep 34421951 = 51632927) B51632927
theorem B2212393 : Blo 578813 2212393 := bstep (se 2 (by rfl) ⟨829647, by rfl⟩ : syracuseStep 2212393 = 1659295) B1659295
theorem B4179539 : Blo 578813 4179539 := bstep (se 1 (by rfl) ⟨3134654, by rfl⟩ : syracuseStep 4179539 = 6269309) B6269309
theorem B870095 : Blo 578813 870095 := bstep (se 1 (by rfl) ⟨652571, by rfl⟩ : syracuseStep 870095 = 1305143) B1305143
theorem B870143 : Blo 578813 870143 := bstep (se 1 (by rfl) ⟨652607, by rfl⟩ : syracuseStep 870143 = 1305215) B1305215
theorem B1100479 : Blo 578813 1100479 := bstep (se 1 (by rfl) ⟨825359, by rfl⟩ : syracuseStep 1100479 = 1650719) B1650719
theorem B871913 : Blo 578813 871913 := bstep (se 2 (by rfl) ⟨326967, by rfl⟩ : syracuseStep 871913 = 653935) B653935
theorem B4410935 : Blo 578813 4410935 := bstep (se 1 (by rfl) ⟨3308201, by rfl⟩ : syracuseStep 4410935 = 6616403) B6616403
theorem B1855457 : Blo 578813 1855457 := bstep (se 2 (by rfl) ⟨695796, by rfl⟩ : syracuseStep 1855457 = 1391593) B1391593
theorem B872699 : Blo 578813 872699 := bstep (se 1 (by rfl) ⟨654524, by rfl⟩ : syracuseStep 872699 = 1309049) B1309049
theorem B578887 : Blo 578813 578887 := bstep (se 1 (by rfl) ⟨434165, by rfl⟩ : syracuseStep 578887 = 868331) B868331
theorem B2086553 : Blo 578813 2086553 := bstep (se 2 (by rfl) ⟨782457, by rfl⟩ : syracuseStep 2086553 = 1564915) B1564915
theorem B1105255 : Blo 578813 1105255 := bstep (se 1 (by rfl) ⟨828941, by rfl⟩ : syracuseStep 1105255 = 1657883) B1657883
theorem B581247 : Blo 578813 581247 := bstep (se 1 (by rfl) ⟨435935, by rfl⟩ : syracuseStep 581247 = 871871) B871871
theorem B1466495 : Blo 578813 1466495 := bstep (se 1 (by rfl) ⟨1099871, by rfl⟩ : syracuseStep 1466495 = 2199743) B2199743
theorem B1303721 : Blo 578813 1303721 := bstep (se 2 (by rfl) ⟨488895, by rfl⟩ : syracuseStep 1303721 = 977791) B977791
theorem B15918319 : Blo 578813 15918319 := bstep (se 1 (by rfl) ⟨11938739, by rfl⟩ : syracuseStep 15918319 = 23877479) B23877479
theorem B4483745 : Blo 578813 4483745 := bstep (se 2 (by rfl) ⟨1681404, by rfl⟩ : syracuseStep 4483745 = 3362809) B3362809
theorem B6877007 : Blo 578813 6877007 := bstep (se 1 (by rfl) ⟨5157755, by rfl⟩ : syracuseStep 6877007 = 10315511) B10315511
theorem B1306655 : Blo 578813 1306655 := bstep (se 1 (by rfl) ⟨979991, by rfl⟩ : syracuseStep 1306655 = 1959983) B1959983
theorem B2651449 : Blo 578813 2651449 := bstep (se 2 (by rfl) ⟨994293, by rfl⟩ : syracuseStep 2651449 = 1988587) B1988587
theorem B90699263 : Blo 578813 90699263 := bstep (se 1 (by rfl) ⟨68024447, by rfl⟩ : syracuseStep 90699263 = 136048895) B136048895
theorem B1309769 : Blo 578813 1309769 := bstep (se 2 (by rfl) ⟨491163, by rfl⟩ : syracuseStep 1309769 = 982327) B982327
theorem B60227063 : Blo 578813 60227063 := bstep (se 1 (by rfl) ⟨45170297, by rfl⟩ : syracuseStep 60227063 = 90340595) B90340595
theorem B2949857 : Blo 578813 2949857 := bstep (se 2 (by rfl) ⟨1106196, by rfl⟩ : syracuseStep 2949857 = 2212393) B2212393
theorem B2786359 : Blo 578813 2786359 := bstep (se 1 (by rfl) ⟨2089769, by rfl⟩ : syracuseStep 2786359 = 4179539) B4179539
theorem B5640367 : Blo 578813 5640367 := bstep (se 1 (by rfl) ⟨4230275, by rfl⟩ : syracuseStep 5640367 = 8460551) B8460551
theorem B2989163 : Blo 578813 2989163 := bstep (se 1 (by rfl) ⟨2241872, by rfl⟩ : syracuseStep 2989163 = 4483745) B4483745
theorem B42311069 : Blo 578813 42311069 := bstep (se 3 (by rfl) ⟨7933325, by rfl⟩ : syracuseStep 42311069 = 15866651) B15866651
theorem B9445535 : Blo 578813 9445535 := bstep (se 1 (by rfl) ⟨7084151, by rfl⟩ : syracuseStep 9445535 = 14168303) B14168303
theorem B5645051 : Blo 578813 5645051 := bstep (se 1 (by rfl) ⟨4233788, by rfl⟩ : syracuseStep 5645051 = 8467577) B8467577
theorem B60466175 : Blo 578813 60466175 := bstep (se 1 (by rfl) ⟨45349631, by rfl⟩ : syracuseStep 60466175 = 90699263) B90699263
theorem B42280703 : Blo 578813 42280703 := bstep (se 1 (by rfl) ⟨31710527, by rfl⟩ : syracuseStep 42280703 = 63421055) B63421055
theorem B22947967 : Blo 578813 22947967 := bstep (se 1 (by rfl) ⟨17210975, by rfl⟩ : syracuseStep 22947967 = 34421951) B34421951
theorem B40151375 : Blo 578813 40151375 := bstep (se 1 (by rfl) ⟨30113531, by rfl⟩ : syracuseStep 40151375 = 60227063) B60227063
theorem B14530765 : Blo 578813 14530765 := bstep (se 3 (by rfl) ⟨2724518, by rfl⟩ : syracuseStep 14530765 = 5449037) B5449037
theorem B1391035 : Blo 578813 1391035 := bstep (se 1 (by rfl) ⟨1043276, by rfl⟩ : syracuseStep 1391035 = 2086553) B2086553
theorem B869147 : Blo 578813 869147 := bstep (se 1 (by rfl) ⟨651860, by rfl⟩ : syracuseStep 869147 = 1303721) B1303721
theorem B871103 : Blo 578813 871103 := bstep (se 1 (by rfl) ⟨653327, by rfl⟩ : syracuseStep 871103 = 1306655) B1306655
theorem B873179 : Blo 578813 873179 := bstep (se 1 (by rfl) ⟨654884, by rfl⟩ : syracuseStep 873179 = 1309769) B1309769
theorem B580063 : Blo 578813 580063 := bstep (se 1 (by rfl) ⟨435047, by rfl⟩ : syracuseStep 580063 = 870095) B870095
theorem B580095 : Blo 578813 580095 := bstep (se 1 (by rfl) ⟨435071, by rfl⟩ : syracuseStep 580095 = 870143) B870143
theorem B21224425 : Blo 578813 21224425 := bstep (se 2 (by rfl) ⟨7959159, by rfl⟩ : syracuseStep 21224425 = 15918319) B15918319
theorem B581275 : Blo 578813 581275 := bstep (se 1 (by rfl) ⟨435956, by rfl⟩ : syracuseStep 581275 = 871913) B871913
theorem B2940623 : Blo 578813 2940623 := bstep (se 1 (by rfl) ⟨2205467, by rfl⟩ : syracuseStep 2940623 = 4410935) B4410935
theorem B1236971 : Blo 578813 1236971 := bstep (se 1 (by rfl) ⟨927728, by rfl⟩ : syracuseStep 1236971 = 1855457) B1855457
theorem B581799 : Blo 578813 581799 := bstep (se 1 (by rfl) ⟨436349, by rfl⟩ : syracuseStep 581799 = 872699) B872699
theorem B1467305 : Blo 578813 1467305 := bstep (se 2 (by rfl) ⟨550239, by rfl⟩ : syracuseStep 1467305 = 1100479) B1100479
theorem B5301733 : Blo 578813 5301733 := bstep (se 4 (by rfl) ⟨497037, by rfl⟩ : syracuseStep 5301733 = 994075) B994075
theorem B14117327 : Blo 578813 14117327 := bstep (se 1 (by rfl) ⟨10587995, by rfl⟩ : syracuseStep 14117327 = 21175991) B21175991
theorem B977663 : Blo 578813 977663 := bstep (se 1 (by rfl) ⟨733247, by rfl⟩ : syracuseStep 977663 = 1466495) B1466495
theorem B3535265 : Blo 578813 3535265 := bstep (se 2 (by rfl) ⟨1325724, by rfl⟩ : syracuseStep 3535265 = 2651449) B2651449
theorem B4584671 : Blo 578813 4584671 := bstep (se 1 (by rfl) ⟨3438503, by rfl⟩ : syracuseStep 4584671 = 6877007) B6877007
theorem B1472863 : Blo 578813 1472863 := bstep (se 1 (by rfl) ⟨1104647, by rfl⟩ : syracuseStep 1472863 = 2209295) B2209295
theorem B1473673 : Blo 578813 1473673 := bstep (se 2 (by rfl) ⟨552627, by rfl⟩ : syracuseStep 1473673 = 1105255) B1105255
theorem B1966571 : Blo 578813 1966571 := bstep (se 1 (by rfl) ⟨1474928, by rfl⟩ : syracuseStep 1966571 = 2949857) B2949857
theorem B122389157 : Blo 578813 122389157 := bstep (se 4 (by rfl) ⟨11473983, by rfl⟩ : syracuseStep 122389157 = 22947967) B22947967
theorem B6297023 : Blo 578813 6297023 := bstep (se 1 (by rfl) ⟨4722767, by rfl⟩ : syracuseStep 6297023 = 9445535) B9445535
theorem B40310783 : Blo 578813 40310783 := bstep (se 1 (by rfl) ⟨30233087, by rfl⟩ : syracuseStep 40310783 = 60466175) B60466175
theorem B28187135 : Blo 578813 28187135 := bstep (se 1 (by rfl) ⟨21140351, by rfl⟩ : syracuseStep 28187135 = 42280703) B42280703
theorem B9411551 : Blo 578813 9411551 := bstep (se 1 (by rfl) ⟨7058663, by rfl⟩ : syracuseStep 9411551 = 14117327) B14117327
theorem B19374353 : Blo 578813 19374353 := bstep (se 2 (by rfl) ⟨7265382, by rfl⟩ : syracuseStep 19374353 = 14530765) B14530765
theorem B3056447 : Blo 578813 3056447 := bstep (se 1 (by rfl) ⟨2292335, by rfl⟩ : syracuseStep 3056447 = 4584671) B4584671
theorem B3715145 : Blo 578813 3715145 := bstep (se 2 (by rfl) ⟨1393179, by rfl⟩ : syracuseStep 3715145 = 2786359) B2786359
theorem B7520489 : Blo 578813 7520489 := bstep (se 2 (by rfl) ⟨2820183, by rfl⟩ : syracuseStep 7520489 = 5640367) B5640367
theorem B1854713 : Blo 578813 1854713 := bstep (se 2 (by rfl) ⟨695517, by rfl⟩ : syracuseStep 1854713 = 1391035) B1391035
theorem B28299233 : Blo 578813 28299233 := bstep (se 2 (by rfl) ⟨10612212, by rfl⟩ : syracuseStep 28299233 = 21224425) B21224425
theorem B3298589 : Blo 578813 3298589 := bstep (se 3 (by rfl) ⟨618485, by rfl⟩ : syracuseStep 3298589 = 1236971) B1236971
theorem B579431 : Blo 578813 579431 := bstep (se 1 (by rfl) ⟨434573, by rfl⟩ : syracuseStep 579431 = 869147) B869147
theorem B9427373 : Blo 578813 9427373 := bstep (se 3 (by rfl) ⟨1767632, by rfl⟩ : syracuseStep 9427373 = 3535265) B3535265
theorem B580735 : Blo 578813 580735 := bstep (se 1 (by rfl) ⟨435551, by rfl⟩ : syracuseStep 580735 = 871103) B871103
theorem B7068977 : Blo 578813 7068977 := bstep (se 2 (by rfl) ⟨2650866, by rfl⟩ : syracuseStep 7068977 = 5301733) B5301733
theorem B582119 : Blo 578813 582119 := bstep (se 1 (by rfl) ⟨436589, by rfl⟩ : syracuseStep 582119 = 873179) B873179
theorem B1992775 : Blo 578813 1992775 := bstep (se 1 (by rfl) ⟨1494581, by rfl⟩ : syracuseStep 1992775 = 2989163) B2989163
theorem B28207379 : Blo 578813 28207379 := bstep (se 1 (by rfl) ⟨21155534, by rfl⟩ : syracuseStep 28207379 = 42311069) B42311069
theorem B1960415 : Blo 578813 1960415 := bstep (se 1 (by rfl) ⟨1470311, by rfl⟩ : syracuseStep 1960415 = 2940623) B2940623
theorem B3763367 : Blo 578813 3763367 := bstep (se 1 (by rfl) ⟨2822525, by rfl⟩ : syracuseStep 3763367 = 5645051) B5645051
theorem B978203 : Blo 578813 978203 := bstep (se 1 (by rfl) ⟨733652, by rfl⟩ : syracuseStep 978203 = 1467305) B1467305
theorem B26767583 : Blo 578813 26767583 := bstep (se 1 (by rfl) ⟨20075687, by rfl⟩ : syracuseStep 26767583 = 40151375) B40151375
theorem B651775 : Blo 578813 651775 := bstep (se 1 (by rfl) ⟨488831, by rfl⟩ : syracuseStep 651775 = 977663) B977663
theorem B1963817 : Blo 578813 1963817 := bstep (se 2 (by rfl) ⟨736431, by rfl⟩ : syracuseStep 1963817 = 1472863) B1472863
theorem B1964897 : Blo 578813 1964897 := bstep (se 2 (by rfl) ⟨736836, by rfl⟩ : syracuseStep 1964897 = 1473673) B1473673
theorem B5013659 : Blo 578813 5013659 := bstep (se 1 (by rfl) ⟨3760244, by rfl⟩ : syracuseStep 5013659 = 7520489) B7520489
theorem B1311047 : Blo 578813 1311047 := bstep (se 1 (by rfl) ⟨983285, by rfl⟩ : syracuseStep 1311047 = 1966571) B1966571
theorem B81592771 : Blo 578813 81592771 := bstep (se 1 (by rfl) ⟨61194578, by rfl⟩ : syracuseStep 81592771 = 122389157) B122389157
theorem B2657033 : Blo 578813 2657033 := bstep (se 2 (by rfl) ⟨996387, by rfl⟩ : syracuseStep 2657033 = 1992775) B1992775
theorem B2199059 : Blo 578813 2199059 := bstep (se 1 (by rfl) ⟨1649294, by rfl⟩ : syracuseStep 2199059 = 3298589) B3298589
theorem B4198015 : Blo 578813 4198015 := bstep (se 1 (by rfl) ⟨3148511, by rfl⟩ : syracuseStep 4198015 = 6297023) B6297023
theorem B26873855 : Blo 578813 26873855 := bstep (se 1 (by rfl) ⟨20155391, by rfl⟩ : syracuseStep 26873855 = 40310783) B40310783
theorem B12916235 : Blo 578813 12916235 := bstep (se 1 (by rfl) ⟨9687176, by rfl⟩ : syracuseStep 12916235 = 19374353) B19374353
theorem B2037631 : Blo 578813 2037631 := bstep (se 1 (by rfl) ⟨1528223, by rfl⟩ : syracuseStep 2037631 = 3056447) B3056447
theorem B18791423 : Blo 578813 18791423 := bstep (se 1 (by rfl) ⟨14093567, by rfl⟩ : syracuseStep 18791423 = 28187135) B28187135
theorem B6274367 : Blo 578813 6274367 := bstep (se 1 (by rfl) ⟨4705775, by rfl⟩ : syracuseStep 6274367 = 9411551) B9411551
theorem B869033 : Blo 578813 869033 := bstep (se 2 (by rfl) ⟨325887, by rfl⟩ : syracuseStep 869033 = 651775) B651775
theorem B2508911 : Blo 578813 2508911 := bstep (se 1 (by rfl) ⟨1881683, by rfl⟩ : syracuseStep 2508911 = 3763367) B3763367
theorem B2476763 : Blo 578813 2476763 := bstep (se 1 (by rfl) ⟨1857572, by rfl⟩ : syracuseStep 2476763 = 3715145) B3715145
theorem B17845055 : Blo 578813 17845055 := bstep (se 1 (by rfl) ⟨13383791, by rfl⟩ : syracuseStep 17845055 = 26767583) B26767583
theorem B1236475 : Blo 578813 1236475 := bstep (se 1 (by rfl) ⟨927356, by rfl⟩ : syracuseStep 1236475 = 1854713) B1854713
theorem B6284915 : Blo 578813 6284915 := bstep (se 1 (by rfl) ⟨4713686, by rfl⟩ : syracuseStep 6284915 = 9427373) B9427373
theorem B4712651 : Blo 578813 4712651 := bstep (se 1 (by rfl) ⟨3534488, by rfl⟩ : syracuseStep 4712651 = 7068977) B7068977
theorem B18804919 : Blo 578813 18804919 := bstep (se 1 (by rfl) ⟨14103689, by rfl⟩ : syracuseStep 18804919 = 28207379) B28207379
theorem B1306943 : Blo 578813 1306943 := bstep (se 1 (by rfl) ⟨980207, by rfl⟩ : syracuseStep 1306943 = 1960415) B1960415
theorem B652135 : Blo 578813 652135 := bstep (se 1 (by rfl) ⟨489101, by rfl⟩ : syracuseStep 652135 = 978203) B978203
theorem B1309211 : Blo 578813 1309211 := bstep (se 1 (by rfl) ⟨981908, by rfl⟩ : syracuseStep 1309211 = 1963817) B1963817
theorem B1309931 : Blo 578813 1309931 := bstep (se 1 (by rfl) ⟨982448, by rfl⟩ : syracuseStep 1309931 = 1964897) B1964897
theorem B75464621 : Blo 578813 75464621 := bstep (se 3 (by rfl) ⟨14149616, by rfl⟩ : syracuseStep 75464621 = 28299233) B28299233
theorem B3342439 : Blo 578813 3342439 := bstep (se 1 (by rfl) ⟨2506829, by rfl⟩ : syracuseStep 3342439 = 5013659) B5013659
theorem B108790361 : Blo 578813 108790361 := bstep (se 2 (by rfl) ⟨40796385, by rfl⟩ : syracuseStep 108790361 = 81592771) B81592771
theorem B1672607 : Blo 578813 1672607 := bstep (se 1 (by rfl) ⟨1254455, by rfl⟩ : syracuseStep 1672607 = 2508911) B2508911
theorem B1771355 : Blo 578813 1771355 := bstep (se 1 (by rfl) ⟨1328516, by rfl⟩ : syracuseStep 1771355 = 2657033) B2657033
theorem B11896703 : Blo 578813 11896703 := bstep (se 1 (by rfl) ⟨8922527, by rfl⟩ : syracuseStep 11896703 = 17845055) B17845055
theorem B25073225 : Blo 578813 25073225 := bstep (se 2 (by rfl) ⟨9402459, by rfl⟩ : syracuseStep 25073225 = 18804919) B18804919
theorem B6594533 : Blo 578813 6594533 := bstep (se 4 (by rfl) ⟨618237, by rfl⟩ : syracuseStep 6594533 = 1236475) B1236475
theorem B12527615 : Blo 578813 12527615 := bstep (se 1 (by rfl) ⟨9395711, by rfl⟩ : syracuseStep 12527615 = 18791423) B18791423
theorem B50309747 : Blo 578813 50309747 := bstep (se 1 (by rfl) ⟨37732310, by rfl⟩ : syracuseStep 50309747 = 75464621) B75464621
theorem B1651175 : Blo 578813 1651175 := bstep (se 1 (by rfl) ⟨1238381, by rfl⟩ : syracuseStep 1651175 = 2476763) B2476763
theorem B869513 : Blo 578813 869513 := bstep (se 2 (by rfl) ⟨326067, by rfl⟩ : syracuseStep 869513 = 652135) B652135
theorem B871295 : Blo 578813 871295 := bstep (se 1 (by rfl) ⟨653471, by rfl⟩ : syracuseStep 871295 = 1306943) B1306943
theorem B872807 : Blo 578813 872807 := bstep (se 1 (by rfl) ⟨654605, by rfl⟩ : syracuseStep 872807 = 1309211) B1309211
theorem B873287 : Blo 578813 873287 := bstep (se 1 (by rfl) ⟨654965, by rfl⟩ : syracuseStep 873287 = 1309931) B1309931
theorem B4182911 : Blo 578813 4182911 := bstep (se 1 (by rfl) ⟨3137183, by rfl⟩ : syracuseStep 4182911 = 6274367) B6274367
theorem B874031 : Blo 578813 874031 := bstep (se 1 (by rfl) ⟨655523, by rfl⟩ : syracuseStep 874031 = 1311047) B1311047
theorem B579355 : Blo 578813 579355 := bstep (se 1 (by rfl) ⟨434516, by rfl⟩ : syracuseStep 579355 = 869033) B869033
theorem B1466039 : Blo 578813 1466039 := bstep (se 1 (by rfl) ⟨1099529, by rfl⟩ : syracuseStep 1466039 = 2199059) B2199059
theorem B17915903 : Blo 578813 17915903 := bstep (se 1 (by rfl) ⟨13436927, by rfl⟩ : syracuseStep 17915903 = 26873855) B26873855
theorem B8610823 : Blo 578813 8610823 := bstep (se 1 (by rfl) ⟨6458117, by rfl⟩ : syracuseStep 8610823 = 12916235) B12916235
theorem B5597353 : Blo 578813 5597353 := bstep (se 2 (by rfl) ⟨2099007, by rfl⟩ : syracuseStep 5597353 = 4198015) B4198015
theorem B4189943 : Blo 578813 4189943 := bstep (se 1 (by rfl) ⟨3142457, by rfl⟩ : syracuseStep 4189943 = 6284915) B6284915
theorem B3141767 : Blo 578813 3141767 := bstep (se 1 (by rfl) ⟨2356325, by rfl⟩ : syracuseStep 3141767 = 4712651) B4712651
theorem B2716841 : Blo 578813 2716841 := bstep (se 2 (by rfl) ⟨1018815, by rfl⟩ : syracuseStep 2716841 = 2037631) B2037631
theorem B4456585 : Blo 578813 4456585 := bstep (se 2 (by rfl) ⟨1671219, by rfl⟩ : syracuseStep 4456585 = 3342439) B3342439
theorem B7931135 : Blo 578813 7931135 := bstep (se 1 (by rfl) ⟨5948351, by rfl⟩ : syracuseStep 7931135 = 11896703) B11896703
theorem B7244909 : Blo 578813 7244909 := bstep (se 3 (by rfl) ⟨1358420, by rfl⟩ : syracuseStep 7244909 = 2716841) B2716841
theorem B2788607 : Blo 578813 2788607 := bstep (se 1 (by rfl) ⟨2091455, by rfl⟩ : syracuseStep 2788607 = 4182911) B4182911
theorem B16715483 : Blo 578813 16715483 := bstep (se 1 (by rfl) ⟨12536612, by rfl⟩ : syracuseStep 16715483 = 25073225) B25073225
theorem B4460285 : Blo 578813 4460285 := bstep (se 3 (by rfl) ⟨836303, by rfl⟩ : syracuseStep 4460285 = 1672607) B1672607
theorem B4723613 : Blo 578813 4723613 := bstep (se 3 (by rfl) ⟨885677, by rfl⟩ : syracuseStep 4723613 = 1771355) B1771355
theorem B4396355 : Blo 578813 4396355 := bstep (se 1 (by rfl) ⟨3297266, by rfl⟩ : syracuseStep 4396355 = 6594533) B6594533
theorem B2793295 : Blo 578813 2793295 := bstep (se 1 (by rfl) ⟨2094971, by rfl⟩ : syracuseStep 2793295 = 4189943) B4189943
theorem B72526907 : Blo 578813 72526907 := bstep (se 1 (by rfl) ⟨54395180, by rfl⟩ : syracuseStep 72526907 = 108790361) B108790361
theorem B11481097 : Blo 578813 11481097 := bstep (se 2 (by rfl) ⟨4305411, by rfl⟩ : syracuseStep 11481097 = 8610823) B8610823
theorem B11943935 : Blo 578813 11943935 := bstep (se 1 (by rfl) ⟨8957951, by rfl⟩ : syracuseStep 11943935 = 17915903) B17915903
theorem B33539831 : Blo 578813 33539831 := bstep (se 1 (by rfl) ⟨25154873, by rfl⟩ : syracuseStep 33539831 = 50309747) B50309747
theorem B1100783 : Blo 578813 1100783 := bstep (se 1 (by rfl) ⟨825587, by rfl⟩ : syracuseStep 1100783 = 1651175) B1651175
theorem B579675 : Blo 578813 579675 := bstep (se 1 (by rfl) ⟨434756, by rfl⟩ : syracuseStep 579675 = 869513) B869513
theorem B580863 : Blo 578813 580863 := bstep (se 1 (by rfl) ⟨435647, by rfl⟩ : syracuseStep 580863 = 871295) B871295
theorem B7463137 : Blo 578813 7463137 := bstep (se 2 (by rfl) ⟨2798676, by rfl⟩ : syracuseStep 7463137 = 5597353) B5597353
theorem B581871 : Blo 578813 581871 := bstep (se 1 (by rfl) ⟨436403, by rfl⟩ : syracuseStep 581871 = 872807) B872807
theorem B582191 : Blo 578813 582191 := bstep (se 1 (by rfl) ⟨436643, by rfl⟩ : syracuseStep 582191 = 873287) B873287
theorem B582687 : Blo 578813 582687 := bstep (se 1 (by rfl) ⟨437015, by rfl⟩ : syracuseStep 582687 = 874031) B874031
theorem B977359 : Blo 578813 977359 := bstep (se 1 (by rfl) ⟨733019, by rfl⟩ : syracuseStep 977359 = 1466039) B1466039
theorem B8351743 : Blo 578813 8351743 := bstep (se 1 (by rfl) ⟨6263807, by rfl⟩ : syracuseStep 8351743 = 12527615) B12527615
theorem B2094511 : Blo 578813 2094511 := bstep (se 1 (by rfl) ⟨1570883, by rfl⟩ : syracuseStep 2094511 = 3141767) B3141767
theorem B11143655 : Blo 578813 11143655 := bstep (se 1 (by rfl) ⟨8357741, by rfl⟩ : syracuseStep 11143655 = 16715483) B16715483
theorem B3149075 : Blo 578813 3149075 := bstep (se 1 (by rfl) ⟨2361806, by rfl⟩ : syracuseStep 3149075 = 4723613) B4723613
theorem B15308129 : Blo 578813 15308129 := bstep (se 2 (by rfl) ⟨5740548, by rfl⟩ : syracuseStep 15308129 = 11481097) B11481097
theorem B2792681 : Blo 578813 2792681 := bstep (se 2 (by rfl) ⟨1047255, by rfl⟩ : syracuseStep 2792681 = 2094511) B2094511
theorem B23768453 : Blo 578813 23768453 := bstep (se 4 (by rfl) ⟨2228292, by rfl⟩ : syracuseStep 23768453 = 4456585) B4456585
theorem B22359887 : Blo 578813 22359887 := bstep (se 1 (by rfl) ⟨16769915, by rfl⟩ : syracuseStep 22359887 = 33539831) B33539831
theorem B733855 : Blo 578813 733855 := bstep (se 1 (by rfl) ⟨550391, by rfl⟩ : syracuseStep 733855 = 1100783) B1100783
theorem B4829939 : Blo 578813 4829939 := bstep (se 1 (by rfl) ⟨3622454, by rfl⟩ : syracuseStep 4829939 = 7244909) B7244909
theorem B21149693 : Blo 578813 21149693 := bstep (se 3 (by rfl) ⟨3965567, by rfl⟩ : syracuseStep 21149693 = 7931135) B7931135
theorem B2930903 : Blo 578813 2930903 := bstep (se 1 (by rfl) ⟨2198177, by rfl⟩ : syracuseStep 2930903 = 4396355) B4396355
theorem B48351271 : Blo 578813 48351271 := bstep (se 1 (by rfl) ⟨36263453, by rfl⟩ : syracuseStep 48351271 = 72526907) B72526907
theorem B7962623 : Blo 578813 7962623 := bstep (se 1 (by rfl) ⟨5971967, by rfl⟩ : syracuseStep 7962623 = 11943935) B11943935
theorem B3724393 : Blo 578813 3724393 := bstep (se 2 (by rfl) ⟨1396647, by rfl⟩ : syracuseStep 3724393 = 2793295) B2793295
theorem B9950849 : Blo 578813 9950849 := bstep (se 2 (by rfl) ⟨3731568, by rfl⟩ : syracuseStep 9950849 = 7463137) B7463137
theorem B1859071 : Blo 578813 1859071 := bstep (se 1 (by rfl) ⟨1394303, by rfl⟩ : syracuseStep 1859071 = 2788607) B2788607
theorem B2973523 : Blo 578813 2973523 := bstep (se 1 (by rfl) ⟨2230142, by rfl⟩ : syracuseStep 2973523 = 4460285) B4460285
theorem B1303145 : Blo 578813 1303145 := bstep (se 2 (by rfl) ⟨488679, by rfl⟩ : syracuseStep 1303145 = 977359) B977359
theorem B11135657 : Blo 578813 11135657 := bstep (se 2 (by rfl) ⟨4175871, by rfl⟩ : syracuseStep 11135657 = 8351743) B8351743
theorem B5308415 : Blo 578813 5308415 := bstep (se 1 (by rfl) ⟨3981311, by rfl⟩ : syracuseStep 5308415 = 7962623) B7962623
theorem B3219959 : Blo 578813 3219959 := bstep (se 1 (by rfl) ⟨2414969, by rfl⟩ : syracuseStep 3219959 = 4829939) B4829939
theorem B8397533 : Blo 578813 8397533 := bstep (se 3 (by rfl) ⟨1574537, by rfl⟩ : syracuseStep 8397533 = 3149075) B3149075
theorem B14099795 : Blo 578813 14099795 := bstep (se 1 (by rfl) ⟨10574846, by rfl⟩ : syracuseStep 14099795 = 21149693) B21149693
theorem B64468361 : Blo 578813 64468361 := bstep (se 2 (by rfl) ⟨24175635, by rfl⟩ : syracuseStep 64468361 = 48351271) B48351271
theorem B6633899 : Blo 578813 6633899 := bstep (se 1 (by rfl) ⟨4975424, by rfl⟩ : syracuseStep 6633899 = 9950849) B9950849
theorem B868763 : Blo 578813 868763 := bstep (se 1 (by rfl) ⟨651572, by rfl⟩ : syracuseStep 868763 = 1303145) B1303145
theorem B4965857 : Blo 578813 4965857 := bstep (se 2 (by rfl) ⟨1862196, by rfl⟩ : syracuseStep 4965857 = 3724393) B3724393
theorem B7423771 : Blo 578813 7423771 := bstep (se 1 (by rfl) ⟨5567828, by rfl⟩ : syracuseStep 7423771 = 11135657) B11135657
theorem B15845635 : Blo 578813 15845635 := bstep (se 1 (by rfl) ⟨11884226, by rfl⟩ : syracuseStep 15845635 = 23768453) B23768453
theorem B1953935 : Blo 578813 1953935 := bstep (se 1 (by rfl) ⟨1465451, by rfl⟩ : syracuseStep 1953935 = 2930903) B2930903
theorem B2478761 : Blo 578813 2478761 := bstep (se 2 (by rfl) ⟨929535, by rfl⟩ : syracuseStep 2478761 = 1859071) B1859071
theorem B7429103 : Blo 578813 7429103 := bstep (se 1 (by rfl) ⟨5571827, by rfl⟩ : syracuseStep 7429103 = 11143655) B11143655
theorem B40821677 : Blo 578813 40821677 := bstep (se 3 (by rfl) ⟨7654064, by rfl⟩ : syracuseStep 40821677 = 15308129) B15308129
theorem B1861787 : Blo 578813 1861787 := bstep (se 1 (by rfl) ⟨1396340, by rfl⟩ : syracuseStep 1861787 = 2792681) B2792681
theorem B978473 : Blo 578813 978473 := bstep (se 2 (by rfl) ⟨366927, by rfl⟩ : syracuseStep 978473 = 733855) B733855
theorem B14906591 : Blo 578813 14906591 := bstep (se 1 (by rfl) ⟨11179943, by rfl⟩ : syracuseStep 14906591 = 22359887) B22359887
theorem B3964697 : Blo 578813 3964697 := bstep (se 2 (by rfl) ⟨1486761, by rfl⟩ : syracuseStep 3964697 = 2973523) B2973523
theorem B3310571 : Blo 578813 3310571 := bstep (se 1 (by rfl) ⟨2482928, by rfl⟩ : syracuseStep 3310571 = 4965857) B4965857
theorem B8586557 : Blo 578813 8586557 := bstep (se 3 (by rfl) ⟨1609979, by rfl⟩ : syracuseStep 8586557 = 3219959) B3219959
theorem B9898361 : Blo 578813 9898361 := bstep (se 2 (by rfl) ⟨3711885, by rfl⟩ : syracuseStep 9898361 = 7423771) B7423771
theorem B4952735 : Blo 578813 4952735 := bstep (se 1 (by rfl) ⟨3714551, by rfl⟩ : syracuseStep 4952735 = 7429103) B7429103
theorem B9937727 : Blo 578813 9937727 := bstep (se 1 (by rfl) ⟨7453295, by rfl⟩ : syracuseStep 9937727 = 14906591) B14906591
theorem B3538943 : Blo 578813 3538943 := bstep (se 1 (by rfl) ⟨2654207, by rfl⟩ : syracuseStep 3538943 = 5308415) B5308415
theorem B1652507 : Blo 578813 1652507 := bstep (se 1 (by rfl) ⟨1239380, by rfl⟩ : syracuseStep 1652507 = 2478761) B2478761
theorem B27214451 : Blo 578813 27214451 := bstep (se 1 (by rfl) ⟨20410838, by rfl⟩ : syracuseStep 27214451 = 40821677) B40821677
theorem B42978907 : Blo 578813 42978907 := bstep (se 1 (by rfl) ⟨32234180, by rfl⟩ : syracuseStep 42978907 = 64468361) B64468361
theorem B2643131 : Blo 578813 2643131 := bstep (se 1 (by rfl) ⟨1982348, by rfl⟩ : syracuseStep 2643131 = 3964697) B3964697
theorem B579175 : Blo 578813 579175 := bstep (se 1 (by rfl) ⟨434381, by rfl⟩ : syracuseStep 579175 = 868763) B868763
theorem B1302623 : Blo 578813 1302623 := bstep (se 1 (by rfl) ⟨976967, by rfl⟩ : syracuseStep 1302623 = 1953935) B1953935
theorem B21127513 : Blo 578813 21127513 := bstep (se 2 (by rfl) ⟨7922817, by rfl⟩ : syracuseStep 21127513 = 15845635) B15845635
theorem B5598355 : Blo 578813 5598355 := bstep (se 1 (by rfl) ⟨4198766, by rfl⟩ : syracuseStep 5598355 = 8397533) B8397533
theorem B9399863 : Blo 578813 9399863 := bstep (se 1 (by rfl) ⟨7049897, by rfl⟩ : syracuseStep 9399863 = 14099795) B14099795
theorem B1241191 : Blo 578813 1241191 := bstep (se 1 (by rfl) ⟨930893, by rfl⟩ : syracuseStep 1241191 = 1861787) B1861787
theorem B652315 : Blo 578813 652315 := bstep (se 1 (by rfl) ⟨489236, by rfl⟩ : syracuseStep 652315 = 978473) B978473
theorem B4422599 : Blo 578813 4422599 := bstep (se 1 (by rfl) ⟨3316949, by rfl⟩ : syracuseStep 4422599 = 6633899) B6633899
theorem B6625151 : Blo 578813 6625151 := bstep (se 1 (by rfl) ⟨4968863, by rfl⟩ : syracuseStep 6625151 = 9937727) B9937727
theorem B6266575 : Blo 578813 6266575 := bstep (se 1 (by rfl) ⟨4699931, by rfl⟩ : syracuseStep 6266575 = 9399863) B9399863
theorem B2359295 : Blo 578813 2359295 := bstep (se 1 (by rfl) ⟨1769471, by rfl⟩ : syracuseStep 2359295 = 3538943) B3538943
theorem B229220837 : Blo 578813 229220837 := bstep (se 4 (by rfl) ⟨21489453, by rfl⟩ : syracuseStep 229220837 = 42978907) B42978907
theorem B2207047 : Blo 578813 2207047 := bstep (se 1 (by rfl) ⟨1655285, by rfl⟩ : syracuseStep 2207047 = 3310571) B3310571
theorem B6598907 : Blo 578813 6598907 := bstep (se 1 (by rfl) ⟨4949180, by rfl⟩ : syracuseStep 6598907 = 9898361) B9898361
theorem B868415 : Blo 578813 868415 := bstep (se 1 (by rfl) ⟨651311, by rfl⟩ : syracuseStep 868415 = 1302623) B1302623
theorem B1654921 : Blo 578813 1654921 := bstep (se 2 (by rfl) ⟨620595, by rfl⟩ : syracuseStep 1654921 = 1241191) B1241191
theorem B869753 : Blo 578813 869753 := bstep (se 2 (by rfl) ⟨326157, by rfl⟩ : syracuseStep 869753 = 652315) B652315
theorem B1101671 : Blo 578813 1101671 := bstep (se 1 (by rfl) ⟨826253, by rfl⟩ : syracuseStep 1101671 = 1652507) B1652507
theorem B18142967 : Blo 578813 18142967 := bstep (se 1 (by rfl) ⟨13607225, by rfl⟩ : syracuseStep 18142967 = 27214451) B27214451
theorem B28170017 : Blo 578813 28170017 := bstep (se 2 (by rfl) ⟨10563756, by rfl⟩ : syracuseStep 28170017 = 21127513) B21127513
theorem B5724371 : Blo 578813 5724371 := bstep (se 1 (by rfl) ⟨4293278, by rfl⟩ : syracuseStep 5724371 = 8586557) B8586557
theorem B3301823 : Blo 578813 3301823 := bstep (se 1 (by rfl) ⟨2476367, by rfl⟩ : syracuseStep 3301823 = 4952735) B4952735
theorem B1762087 : Blo 578813 1762087 := bstep (se 1 (by rfl) ⟨1321565, by rfl⟩ : syracuseStep 1762087 = 2643131) B2643131
theorem B7464473 : Blo 578813 7464473 := bstep (se 2 (by rfl) ⟨2799177, by rfl⟩ : syracuseStep 7464473 = 5598355) B5598355
theorem B2948399 : Blo 578813 2948399 := bstep (se 1 (by rfl) ⟨2211299, by rfl⟩ : syracuseStep 2948399 = 4422599) B4422599
theorem B18780011 : Blo 578813 18780011 := bstep (se 1 (by rfl) ⟨14085008, by rfl⟩ : syracuseStep 18780011 = 28170017) B28170017
theorem B2201215 : Blo 578813 2201215 := bstep (se 1 (by rfl) ⟨1650911, by rfl⟩ : syracuseStep 2201215 = 3301823) B3301823
theorem B4399271 : Blo 578813 4399271 := bstep (se 1 (by rfl) ⟨3299453, by rfl⟩ : syracuseStep 4399271 = 6598907) B6598907
theorem B2206561 : Blo 578813 2206561 := bstep (se 2 (by rfl) ⟨827460, by rfl⟩ : syracuseStep 2206561 = 1654921) B1654921
theorem B734447 : Blo 578813 734447 := bstep (se 1 (by rfl) ⟨550835, by rfl⟩ : syracuseStep 734447 = 1101671) B1101671
theorem B3816247 : Blo 578813 3816247 := bstep (se 1 (by rfl) ⟨2862185, by rfl⟩ : syracuseStep 3816247 = 5724371) B5724371
theorem B48381245 : Blo 578813 48381245 := bstep (se 3 (by rfl) ⟨9071483, by rfl⟩ : syracuseStep 48381245 = 18142967) B18142967
theorem B152813891 : Blo 578813 152813891 := bstep (se 1 (by rfl) ⟨114610418, by rfl⟩ : syracuseStep 152813891 = 229220837) B229220837
theorem B578943 : Blo 578813 578943 := bstep (se 1 (by rfl) ⟨434207, by rfl⟩ : syracuseStep 578943 = 868415) B868415
theorem B579835 : Blo 578813 579835 := bstep (se 1 (by rfl) ⟨434876, by rfl⟩ : syracuseStep 579835 = 869753) B869753
theorem B2349449 : Blo 578813 2349449 := bstep (se 2 (by rfl) ⟨881043, by rfl⟩ : syracuseStep 2349449 = 1762087) B1762087
theorem B4416767 : Blo 578813 4416767 := bstep (se 1 (by rfl) ⟨3312575, by rfl⟩ : syracuseStep 4416767 = 6625151) B6625151
theorem B2942729 : Blo 578813 2942729 := bstep (se 2 (by rfl) ⟨1103523, by rfl⟩ : syracuseStep 2942729 = 2207047) B2207047
theorem B4976315 : Blo 578813 4976315 := bstep (se 1 (by rfl) ⟨3732236, by rfl⟩ : syracuseStep 4976315 = 7464473) B7464473
theorem B33421733 : Blo 578813 33421733 := bstep (se 4 (by rfl) ⟨3133287, by rfl⟩ : syracuseStep 33421733 = 6266575) B6266575
theorem B1965599 : Blo 578813 1965599 := bstep (se 1 (by rfl) ⟨1474199, by rfl⟩ : syracuseStep 1965599 = 2948399) B2948399
theorem B1572863 : Blo 578813 1572863 := bstep (se 1 (by rfl) ⟨1179647, by rfl⟩ : syracuseStep 1572863 = 2359295) B2359295
theorem B101875927 : Blo 578813 101875927 := bstep (se 1 (by rfl) ⟨76406945, by rfl⟩ : syracuseStep 101875927 = 152813891) B152813891
theorem B12520007 : Blo 578813 12520007 := bstep (se 1 (by rfl) ⟨9390005, by rfl⟩ : syracuseStep 12520007 = 18780011) B18780011
theorem B3317543 : Blo 578813 3317543 := bstep (se 1 (by rfl) ⟨2488157, by rfl⟩ : syracuseStep 3317543 = 4976315) B4976315
theorem B5088329 : Blo 578813 5088329 := bstep (se 2 (by rfl) ⟨1908123, by rfl⟩ : syracuseStep 5088329 = 3816247) B3816247
theorem B32254163 : Blo 578813 32254163 := bstep (se 1 (by rfl) ⟨24190622, by rfl⟩ : syracuseStep 32254163 = 48381245) B48381245
theorem B2932847 : Blo 578813 2932847 := bstep (se 1 (by rfl) ⟨2199635, by rfl⟩ : syracuseStep 2932847 = 4399271) B4399271
theorem B2934953 : Blo 578813 2934953 := bstep (se 2 (by rfl) ⟨1100607, by rfl⟩ : syracuseStep 2934953 = 2201215) B2201215
theorem B1958525 : Blo 578813 1958525 := bstep (se 3 (by rfl) ⟨367223, by rfl⟩ : syracuseStep 1958525 = 734447) B734447
theorem B2942081 : Blo 578813 2942081 := bstep (se 2 (by rfl) ⟨1103280, by rfl⟩ : syracuseStep 2942081 = 2206561) B2206561
theorem B1566299 : Blo 578813 1566299 := bstep (se 1 (by rfl) ⟨1174724, by rfl⟩ : syracuseStep 1566299 = 2349449) B2349449
theorem B2944511 : Blo 578813 2944511 := bstep (se 1 (by rfl) ⟨2208383, by rfl⟩ : syracuseStep 2944511 = 4416767) B4416767
theorem B1961819 : Blo 578813 1961819 := bstep (se 1 (by rfl) ⟨1471364, by rfl⟩ : syracuseStep 1961819 = 2942729) B2942729
theorem B22281155 : Blo 578813 22281155 := bstep (se 1 (by rfl) ⟨16710866, by rfl⟩ : syracuseStep 22281155 = 33421733) B33421733
theorem B1310399 : Blo 578813 1310399 := bstep (se 1 (by rfl) ⟨982799, by rfl⟩ : syracuseStep 1310399 = 1965599) B1965599
theorem B4194301 : Blo 578813 4194301 := bstep (se 3 (by rfl) ⟨786431, by rfl⟩ : syracuseStep 4194301 = 1572863) B1572863
theorem B21502775 : Blo 578813 21502775 := bstep (se 1 (by rfl) ⟨16127081, by rfl⟩ : syracuseStep 21502775 = 32254163) B32254163
theorem B14854103 : Blo 578813 14854103 := bstep (se 1 (by rfl) ⟨11140577, by rfl⟩ : syracuseStep 14854103 = 22281155) B22281155
theorem B135834569 : Blo 578813 135834569 := bstep (se 2 (by rfl) ⟨50937963, by rfl⟩ : syracuseStep 135834569 = 101875927) B101875927
theorem B2211695 : Blo 578813 2211695 := bstep (se 1 (by rfl) ⟨1658771, by rfl⟩ : syracuseStep 2211695 = 3317543) B3317543
theorem B3392219 : Blo 578813 3392219 := bstep (se 1 (by rfl) ⟨2544164, by rfl⟩ : syracuseStep 3392219 = 5088329) B5088329
theorem B873599 : Blo 578813 873599 := bstep (se 1 (by rfl) ⟨655199, by rfl⟩ : syracuseStep 873599 = 1310399) B1310399
theorem B5592401 : Blo 578813 5592401 := bstep (se 2 (by rfl) ⟨2097150, by rfl⟩ : syracuseStep 5592401 = 4194301) B4194301
theorem B1955231 : Blo 578813 1955231 := bstep (se 1 (by rfl) ⟨1466423, by rfl⟩ : syracuseStep 1955231 = 2932847) B2932847
theorem B1956635 : Blo 578813 1956635 := bstep (se 1 (by rfl) ⟨1467476, by rfl⟩ : syracuseStep 1956635 = 2934953) B2934953
theorem B8346671 : Blo 578813 8346671 := bstep (se 1 (by rfl) ⟨6260003, by rfl⟩ : syracuseStep 8346671 = 12520007) B12520007
theorem B1305683 : Blo 578813 1305683 := bstep (se 1 (by rfl) ⟨979262, by rfl⟩ : syracuseStep 1305683 = 1958525) B1958525
theorem B1961387 : Blo 578813 1961387 := bstep (se 1 (by rfl) ⟨1471040, by rfl⟩ : syracuseStep 1961387 = 2942081) B2942081
theorem B1044199 : Blo 578813 1044199 := bstep (se 1 (by rfl) ⟨783149, by rfl⟩ : syracuseStep 1044199 = 1566299) B1566299
theorem B1963007 : Blo 578813 1963007 := bstep (se 1 (by rfl) ⟨1472255, by rfl⟩ : syracuseStep 1963007 = 2944511) B2944511
theorem B1307879 : Blo 578813 1307879 := bstep (se 1 (by rfl) ⟨980909, by rfl⟩ : syracuseStep 1307879 = 1961819) B1961819
theorem B2261479 : Blo 578813 2261479 := bstep (se 1 (by rfl) ⟨1696109, by rfl⟩ : syracuseStep 2261479 = 3392219) B3392219
theorem B9902735 : Blo 578813 9902735 := bstep (se 1 (by rfl) ⟨7427051, by rfl⟩ : syracuseStep 9902735 = 14854103) B14854103
theorem B14335183 : Blo 578813 14335183 := bstep (se 1 (by rfl) ⟨10751387, by rfl⟩ : syracuseStep 14335183 = 21502775) B21502775
theorem B1392265 : Blo 578813 1392265 := bstep (se 2 (by rfl) ⟨522099, by rfl⟩ : syracuseStep 1392265 = 1044199) B1044199
theorem B90556379 : Blo 578813 90556379 := bstep (se 1 (by rfl) ⟨67917284, by rfl⟩ : syracuseStep 90556379 = 135834569) B135834569
theorem B870455 : Blo 578813 870455 := bstep (se 1 (by rfl) ⟨652841, by rfl⟩ : syracuseStep 870455 = 1305683) B1305683
theorem B871919 : Blo 578813 871919 := bstep (se 1 (by rfl) ⟨653939, by rfl⟩ : syracuseStep 871919 = 1307879) B1307879
theorem B582399 : Blo 578813 582399 := bstep (se 1 (by rfl) ⟨436799, by rfl⟩ : syracuseStep 582399 = 873599) B873599
theorem B3728267 : Blo 578813 3728267 := bstep (se 1 (by rfl) ⟨2796200, by rfl⟩ : syracuseStep 3728267 = 5592401) B5592401
theorem B1303487 : Blo 578813 1303487 := bstep (se 1 (by rfl) ⟨977615, by rfl⟩ : syracuseStep 1303487 = 1955231) B1955231
theorem B1304423 : Blo 578813 1304423 := bstep (se 1 (by rfl) ⟨978317, by rfl⟩ : syracuseStep 1304423 = 1956635) B1956635
theorem B5564447 : Blo 578813 5564447 := bstep (se 1 (by rfl) ⟨4173335, by rfl⟩ : syracuseStep 5564447 = 8346671) B8346671
theorem B1307591 : Blo 578813 1307591 := bstep (se 1 (by rfl) ⟨980693, by rfl⟩ : syracuseStep 1307591 = 1961387) B1961387
theorem B1308671 : Blo 578813 1308671 := bstep (se 1 (by rfl) ⟨981503, by rfl⟩ : syracuseStep 1308671 = 1963007) B1963007
theorem B1474463 : Blo 578813 1474463 := bstep (se 1 (by rfl) ⟨1105847, by rfl⟩ : syracuseStep 1474463 = 2211695) B2211695
theorem B3015305 : Blo 578813 3015305 := bstep (se 2 (by rfl) ⟨1130739, by rfl⟩ : syracuseStep 3015305 = 2261479) B2261479
theorem B3709631 : Blo 578813 3709631 := bstep (se 1 (by rfl) ⟨2782223, by rfl⟩ : syracuseStep 3709631 = 5564447) B5564447
theorem B19113577 : Blo 578813 19113577 := bstep (se 2 (by rfl) ⟨7167591, by rfl⟩ : syracuseStep 19113577 = 14335183) B14335183
theorem B60370919 : Blo 578813 60370919 := bstep (se 1 (by rfl) ⟨45278189, by rfl⟩ : syracuseStep 60370919 = 90556379) B90556379
theorem B6601823 : Blo 578813 6601823 := bstep (se 1 (by rfl) ⟨4951367, by rfl⟩ : syracuseStep 6601823 = 9902735) B9902735
theorem B868991 : Blo 578813 868991 := bstep (se 1 (by rfl) ⟨651743, by rfl⟩ : syracuseStep 868991 = 1303487) B1303487
theorem B869615 : Blo 578813 869615 := bstep (se 1 (by rfl) ⟨652211, by rfl⟩ : syracuseStep 869615 = 1304423) B1304423
theorem B871727 : Blo 578813 871727 := bstep (se 1 (by rfl) ⟨653795, by rfl⟩ : syracuseStep 871727 = 1307591) B1307591
theorem B872447 : Blo 578813 872447 := bstep (se 1 (by rfl) ⟨654335, by rfl⟩ : syracuseStep 872447 = 1308671) B1308671
theorem B1856353 : Blo 578813 1856353 := bstep (se 2 (by rfl) ⟨696132, by rfl⟩ : syracuseStep 1856353 = 1392265) B1392265
theorem B580303 : Blo 578813 580303 := bstep (se 1 (by rfl) ⟨435227, by rfl⟩ : syracuseStep 580303 = 870455) B870455
theorem B581279 : Blo 578813 581279 := bstep (se 1 (by rfl) ⟨435959, by rfl⟩ : syracuseStep 581279 = 871919) B871919
theorem B2485511 : Blo 578813 2485511 := bstep (se 1 (by rfl) ⟨1864133, by rfl⟩ : syracuseStep 2485511 = 3728267) B3728267
theorem B982975 : Blo 578813 982975 := bstep (se 1 (by rfl) ⟨737231, by rfl⟩ : syracuseStep 982975 = 1474463) B1474463
theorem B40247279 : Blo 578813 40247279 := bstep (se 1 (by rfl) ⟨30185459, by rfl⟩ : syracuseStep 40247279 = 60370919) B60370919
theorem B4401215 : Blo 578813 4401215 := bstep (se 1 (by rfl) ⟨3300911, by rfl⟩ : syracuseStep 4401215 = 6601823) B6601823
theorem B2010203 : Blo 578813 2010203 := bstep (se 1 (by rfl) ⟨1507652, by rfl⟩ : syracuseStep 2010203 = 3015305) B3015305
theorem B2473087 : Blo 578813 2473087 := bstep (se 1 (by rfl) ⟨1854815, by rfl⟩ : syracuseStep 2473087 = 3709631) B3709631
theorem B2475137 : Blo 578813 2475137 := bstep (se 2 (by rfl) ⟨928176, by rfl⟩ : syracuseStep 2475137 = 1856353) B1856353
theorem B1657007 : Blo 578813 1657007 := bstep (se 1 (by rfl) ⟨1242755, by rfl⟩ : syracuseStep 1657007 = 2485511) B2485511
theorem B579327 : Blo 578813 579327 := bstep (se 1 (by rfl) ⟨434495, by rfl⟩ : syracuseStep 579327 = 868991) B868991
theorem B579743 : Blo 578813 579743 := bstep (se 1 (by rfl) ⟨434807, by rfl⟩ : syracuseStep 579743 = 869615) B869615
theorem B581151 : Blo 578813 581151 := bstep (se 1 (by rfl) ⟨435863, by rfl⟩ : syracuseStep 581151 = 871727) B871727
theorem B581631 : Blo 578813 581631 := bstep (se 1 (by rfl) ⟨436223, by rfl⟩ : syracuseStep 581631 = 872447) B872447
theorem B101939077 : Blo 578813 101939077 := bstep (se 4 (by rfl) ⟨9556788, by rfl⟩ : syracuseStep 101939077 = 19113577) B19113577
theorem B1310633 : Blo 578813 1310633 := bstep (se 2 (by rfl) ⟨491487, by rfl⟩ : syracuseStep 1310633 = 982975) B982975
theorem B6600365 : Blo 578813 6600365 := bstep (se 3 (by rfl) ⟨1237568, by rfl⟩ : syracuseStep 6600365 = 2475137) B2475137
theorem B2934143 : Blo 578813 2934143 := bstep (se 1 (by rfl) ⟨2200607, by rfl⟩ : syracuseStep 2934143 = 4401215) B4401215
theorem B3297449 : Blo 578813 3297449 := bstep (se 2 (by rfl) ⟨1236543, by rfl⟩ : syracuseStep 3297449 = 2473087) B2473087
theorem B873755 : Blo 578813 873755 := bstep (se 1 (by rfl) ⟨655316, by rfl⟩ : syracuseStep 873755 = 1310633) B1310633
theorem B1104671 : Blo 578813 1104671 := bstep (se 1 (by rfl) ⟨828503, by rfl⟩ : syracuseStep 1104671 = 1657007) B1657007
theorem B26831519 : Blo 578813 26831519 := bstep (se 1 (by rfl) ⟨20123639, by rfl⟩ : syracuseStep 26831519 = 40247279) B40247279
theorem B1340135 : Blo 578813 1340135 := bstep (se 1 (by rfl) ⟨1005101, by rfl⟩ : syracuseStep 1340135 = 2010203) B2010203
theorem B135918769 : Blo 578813 135918769 := bstep (se 2 (by rfl) ⟨50969538, by rfl⟩ : syracuseStep 135918769 = 101939077) B101939077
theorem B2198299 : Blo 578813 2198299 := bstep (se 1 (by rfl) ⟨1648724, by rfl⟩ : syracuseStep 2198299 = 3297449) B3297449
theorem B893423 : Blo 578813 893423 := bstep (se 1 (by rfl) ⟨670067, by rfl⟩ : syracuseStep 893423 = 1340135) B1340135
theorem B4400243 : Blo 578813 4400243 := bstep (se 1 (by rfl) ⟨3300182, by rfl⟩ : syracuseStep 4400243 = 6600365) B6600365
theorem B736447 : Blo 578813 736447 := bstep (se 1 (by rfl) ⟨552335, by rfl⟩ : syracuseStep 736447 = 1104671) B1104671
theorem B181225025 : Blo 578813 181225025 := bstep (se 2 (by rfl) ⟨67959384, by rfl⟩ : syracuseStep 181225025 = 135918769) B135918769
theorem B1956095 : Blo 578813 1956095 := bstep (se 1 (by rfl) ⟨1467071, by rfl⟩ : syracuseStep 1956095 = 2934143) B2934143
theorem B582503 : Blo 578813 582503 := bstep (se 1 (by rfl) ⟨436877, by rfl⟩ : syracuseStep 582503 = 873755) B873755
theorem B17887679 : Blo 578813 17887679 := bstep (se 1 (by rfl) ⟨13415759, by rfl⟩ : syracuseStep 17887679 = 26831519) B26831519
theorem B120816683 : Blo 578813 120816683 := bstep (se 1 (by rfl) ⟨90612512, by rfl⟩ : syracuseStep 120816683 = 181225025) B181225025
theorem B2931065 : Blo 578813 2931065 := bstep (se 2 (by rfl) ⟨1099149, by rfl⟩ : syracuseStep 2931065 = 2198299) B2198299
theorem B2933495 : Blo 578813 2933495 := bstep (se 1 (by rfl) ⟨2200121, by rfl⟩ : syracuseStep 2933495 = 4400243) B4400243
theorem B2382461 : Blo 578813 2382461 := bstep (se 3 (by rfl) ⟨446711, by rfl⟩ : syracuseStep 2382461 = 893423) B893423
theorem B1304063 : Blo 578813 1304063 := bstep (se 1 (by rfl) ⟨978047, by rfl⟩ : syracuseStep 1304063 = 1956095) B1956095
theorem B11925119 : Blo 578813 11925119 := bstep (se 1 (by rfl) ⟨8943839, by rfl⟩ : syracuseStep 11925119 = 17887679) B17887679
theorem B981929 : Blo 578813 981929 := bstep (se 2 (by rfl) ⟨368223, by rfl⟩ : syracuseStep 981929 = 736447) B736447
theorem B80544455 : Blo 578813 80544455 := bstep (se 1 (by rfl) ⟨60408341, by rfl⟩ : syracuseStep 80544455 = 120816683) B120816683
theorem B1588307 : Blo 578813 1588307 := bstep (se 1 (by rfl) ⟨1191230, by rfl⟩ : syracuseStep 1588307 = 2382461) B2382461
theorem B869375 : Blo 578813 869375 := bstep (se 1 (by rfl) ⟨652031, by rfl⟩ : syracuseStep 869375 = 1304063) B1304063
theorem B7950079 : Blo 578813 7950079 := bstep (se 1 (by rfl) ⟨5962559, by rfl⟩ : syracuseStep 7950079 = 11925119) B11925119
theorem B1954043 : Blo 578813 1954043 := bstep (se 1 (by rfl) ⟨1465532, by rfl⟩ : syracuseStep 1954043 = 2931065) B2931065
theorem B1955663 : Blo 578813 1955663 := bstep (se 1 (by rfl) ⟨1466747, by rfl⟩ : syracuseStep 1955663 = 2933495) B2933495
theorem B654619 : Blo 578813 654619 := bstep (se 1 (by rfl) ⟨490964, by rfl⟩ : syracuseStep 654619 = 981929) B981929
theorem B4235485 : Blo 578813 4235485 := bstep (se 3 (by rfl) ⟨794153, by rfl⟩ : syracuseStep 4235485 = 1588307) B1588307
theorem B10600105 : Blo 578813 10600105 := bstep (se 2 (by rfl) ⟨3975039, by rfl⟩ : syracuseStep 10600105 = 7950079) B7950079
theorem B872825 : Blo 578813 872825 := bstep (se 2 (by rfl) ⟨327309, by rfl⟩ : syracuseStep 872825 = 654619) B654619
theorem B53696303 : Blo 578813 53696303 := bstep (se 1 (by rfl) ⟨40272227, by rfl⟩ : syracuseStep 53696303 = 80544455) B80544455
theorem B579583 : Blo 578813 579583 := bstep (se 1 (by rfl) ⟨434687, by rfl⟩ : syracuseStep 579583 = 869375) B869375
theorem B1302695 : Blo 578813 1302695 := bstep (se 1 (by rfl) ⟨977021, by rfl⟩ : syracuseStep 1302695 = 1954043) B1954043
theorem B1303775 : Blo 578813 1303775 := bstep (se 1 (by rfl) ⟨977831, by rfl⟩ : syracuseStep 1303775 = 1955663) B1955663
theorem B14133473 : Blo 578813 14133473 := bstep (se 2 (by rfl) ⟨5300052, by rfl⟩ : syracuseStep 14133473 = 10600105) B10600105
theorem B5647313 : Blo 578813 5647313 := bstep (se 2 (by rfl) ⟨2117742, by rfl⟩ : syracuseStep 5647313 = 4235485) B4235485
theorem B35797535 : Blo 578813 35797535 := bstep (se 1 (by rfl) ⟨26848151, by rfl⟩ : syracuseStep 35797535 = 53696303) B53696303
theorem B868463 : Blo 578813 868463 := bstep (se 1 (by rfl) ⟨651347, by rfl⟩ : syracuseStep 868463 = 1302695) B1302695
theorem B869183 : Blo 578813 869183 := bstep (se 1 (by rfl) ⟨651887, by rfl⟩ : syracuseStep 869183 = 1303775) B1303775
theorem B581883 : Blo 578813 581883 := bstep (se 1 (by rfl) ⟨436412, by rfl⟩ : syracuseStep 581883 = 872825) B872825
theorem B23865023 : Blo 578813 23865023 := bstep (se 1 (by rfl) ⟨17898767, by rfl⟩ : syracuseStep 23865023 = 35797535) B35797535
theorem B9422315 : Blo 578813 9422315 := bstep (se 1 (by rfl) ⟨7066736, by rfl⟩ : syracuseStep 9422315 = 14133473) B14133473
theorem B578975 : Blo 578813 578975 := bstep (se 1 (by rfl) ⟨434231, by rfl⟩ : syracuseStep 578975 = 868463) B868463
theorem B579455 : Blo 578813 579455 := bstep (se 1 (by rfl) ⟨434591, by rfl⟩ : syracuseStep 579455 = 869183) B869183
theorem B3764875 : Blo 578813 3764875 := bstep (se 1 (by rfl) ⟨2823656, by rfl⟩ : syracuseStep 3764875 = 5647313) B5647313
theorem B5019833 : Blo 578813 5019833 := bstep (se 2 (by rfl) ⟨1882437, by rfl⟩ : syracuseStep 5019833 = 3764875) B3764875
theorem B15910015 : Blo 578813 15910015 := bstep (se 1 (by rfl) ⟨11932511, by rfl⟩ : syracuseStep 15910015 = 23865023) B23865023
theorem B6281543 : Blo 578813 6281543 := bstep (se 1 (by rfl) ⟨4711157, by rfl⟩ : syracuseStep 6281543 = 9422315) B9422315
theorem B3346555 : Blo 578813 3346555 := bstep (se 1 (by rfl) ⟨2509916, by rfl⟩ : syracuseStep 3346555 = 5019833) B5019833
theorem B21213353 : Blo 578813 21213353 := bstep (se 2 (by rfl) ⟨7955007, by rfl⟩ : syracuseStep 21213353 = 15910015) B15910015
theorem B4187695 : Blo 578813 4187695 := bstep (se 1 (by rfl) ⟨3140771, by rfl⟩ : syracuseStep 4187695 = 6281543) B6281543
theorem B4462073 : Blo 578813 4462073 := bstep (se 2 (by rfl) ⟨1673277, by rfl⟩ : syracuseStep 4462073 = 3346555) B3346555
theorem B5583593 : Blo 578813 5583593 := bstep (se 2 (by rfl) ⟨2093847, by rfl⟩ : syracuseStep 5583593 = 4187695) B4187695
theorem B14142235 : Blo 578813 14142235 := bstep (se 1 (by rfl) ⟨10606676, by rfl⟩ : syracuseStep 14142235 = 21213353) B21213353
theorem B18856313 : Blo 578813 18856313 := bstep (se 2 (by rfl) ⟨7071117, by rfl⟩ : syracuseStep 18856313 = 14142235) B14142235
theorem B3722395 : Blo 578813 3722395 := bstep (se 1 (by rfl) ⟨2791796, by rfl⟩ : syracuseStep 3722395 = 5583593) B5583593
theorem B2974715 : Blo 578813 2974715 := bstep (se 1 (by rfl) ⟨2231036, by rfl⟩ : syracuseStep 2974715 = 4462073) B4462073
theorem B4963193 : Blo 578813 4963193 := bstep (se 2 (by rfl) ⟨1861197, by rfl⟩ : syracuseStep 4963193 = 3722395) B3722395
theorem B1983143 : Blo 578813 1983143 := bstep (se 1 (by rfl) ⟨1487357, by rfl⟩ : syracuseStep 1983143 = 2974715) B2974715
theorem B12570875 : Blo 578813 12570875 := bstep (se 1 (by rfl) ⟨9428156, by rfl⟩ : syracuseStep 12570875 = 18856313) B18856313
theorem B1322095 : Blo 578813 1322095 := bstep (se 1 (by rfl) ⟨991571, by rfl⟩ : syracuseStep 1322095 = 1983143) B1983143
theorem B8380583 : Blo 578813 8380583 := bstep (se 1 (by rfl) ⟨6285437, by rfl⟩ : syracuseStep 8380583 = 12570875) B12570875
theorem B3308795 : Blo 578813 3308795 := bstep (se 1 (by rfl) ⟨2481596, by rfl⟩ : syracuseStep 3308795 = 4963193) B4963193
theorem B2205863 : Blo 578813 2205863 := bstep (se 1 (by rfl) ⟨1654397, by rfl⟩ : syracuseStep 2205863 = 3308795) B3308795
theorem B5587055 : Blo 578813 5587055 := bstep (se 1 (by rfl) ⟨4190291, by rfl⟩ : syracuseStep 5587055 = 8380583) B8380583
theorem B1762793 : Blo 578813 1762793 := bstep (se 2 (by rfl) ⟨661047, by rfl⟩ : syracuseStep 1762793 = 1322095) B1322095
theorem B3724703 : Blo 578813 3724703 := bstep (se 1 (by rfl) ⟨2793527, by rfl⟩ : syracuseStep 3724703 = 5587055) B5587055
theorem B1175195 : Blo 578813 1175195 := bstep (se 1 (by rfl) ⟨881396, by rfl⟩ : syracuseStep 1175195 = 1762793) B1762793
theorem B1470575 : Blo 578813 1470575 := bstep (se 1 (by rfl) ⟨1102931, by rfl⟩ : syracuseStep 1470575 = 2205863) B2205863
theorem B3133853 : Blo 578813 3133853 := bstep (se 3 (by rfl) ⟨587597, by rfl⟩ : syracuseStep 3133853 = 1175195) B1175195
theorem B2483135 : Blo 578813 2483135 := bstep (se 1 (by rfl) ⟨1862351, by rfl⟩ : syracuseStep 2483135 = 3724703) B3724703
theorem B980383 : Blo 578813 980383 := bstep (se 1 (by rfl) ⟨735287, by rfl⟩ : syracuseStep 980383 = 1470575) B1470575
theorem B1655423 : Blo 578813 1655423 := bstep (se 1 (by rfl) ⟨1241567, by rfl⟩ : syracuseStep 1655423 = 2483135) B2483135
theorem B2089235 : Blo 578813 2089235 := bstep (se 1 (by rfl) ⟨1566926, by rfl⟩ : syracuseStep 2089235 = 3133853) B3133853
theorem B1307177 : Blo 578813 1307177 := bstep (se 2 (by rfl) ⟨490191, by rfl⟩ : syracuseStep 1307177 = 980383) B980383
theorem B1392823 : Blo 578813 1392823 := bstep (se 1 (by rfl) ⟨1044617, by rfl⟩ : syracuseStep 1392823 = 2089235) B2089235
theorem B871451 : Blo 578813 871451 := bstep (se 1 (by rfl) ⟨653588, by rfl⟩ : syracuseStep 871451 = 1307177) B1307177
theorem B1103615 : Blo 578813 1103615 := bstep (se 1 (by rfl) ⟨827711, by rfl⟩ : syracuseStep 1103615 = 1655423) B1655423
theorem B735743 : Blo 578813 735743 := bstep (se 1 (by rfl) ⟨551807, by rfl⟩ : syracuseStep 735743 = 1103615) B1103615
theorem B1857097 : Blo 578813 1857097 := bstep (se 2 (by rfl) ⟨696411, by rfl⟩ : syracuseStep 1857097 = 1392823) B1392823
theorem B580967 : Blo 578813 580967 := bstep (se 1 (by rfl) ⟨435725, by rfl⟩ : syracuseStep 580967 = 871451) B871451
theorem B2476129 : Blo 578813 2476129 := bstep (se 2 (by rfl) ⟨928548, by rfl⟩ : syracuseStep 2476129 = 1857097) B1857097
theorem B1961981 : Blo 578813 1961981 := bstep (se 3 (by rfl) ⟨367871, by rfl⟩ : syracuseStep 1961981 = 735743) B735743
theorem B3301505 : Blo 578813 3301505 := bstep (se 2 (by rfl) ⟨1238064, by rfl⟩ : syracuseStep 3301505 = 2476129) B2476129
theorem B1307987 : Blo 578813 1307987 := bstep (se 1 (by rfl) ⟨980990, by rfl⟩ : syracuseStep 1307987 = 1961981) B1961981
theorem B2201003 : Blo 578813 2201003 := bstep (se 1 (by rfl) ⟨1650752, by rfl⟩ : syracuseStep 2201003 = 3301505) B3301505
theorem B871991 : Blo 578813 871991 := bstep (se 1 (by rfl) ⟨653993, by rfl⟩ : syracuseStep 871991 = 1307987) B1307987
theorem B581327 : Blo 578813 581327 := bstep (se 1 (by rfl) ⟨435995, by rfl⟩ : syracuseStep 581327 = 871991) B871991
theorem B1467335 : Blo 578813 1467335 := bstep (se 1 (by rfl) ⟨1100501, by rfl⟩ : syracuseStep 1467335 = 2201003) B2201003
theorem B978223 : Blo 578813 978223 := bstep (se 1 (by rfl) ⟨733667, by rfl⟩ : syracuseStep 978223 = 1467335) B1467335
theorem B1304297 : Blo 578813 1304297 := bstep (se 2 (by rfl) ⟨489111, by rfl⟩ : syracuseStep 1304297 = 978223) B978223
theorem B869531 : Blo 578813 869531 := bstep (se 1 (by rfl) ⟨652148, by rfl⟩ : syracuseStep 869531 = 1304297) B1304297
theorem B579687 : Blo 578813 579687 := bstep (se 1 (by rfl) ⟨434765, by rfl⟩ : syracuseStep 579687 = 869531) B869531

theorem C0 (j : ℕ) (h1 : 144703 ≤ j) (h2 : j ≤ 145402) : Blo 578813 (4 * j + 3) := by
  interval_cases j
  · exact B578815
  · exact B578819
  · exact B578823
  · exact B578827
  · exact B578831
  · exact B578835
  · exact B578839
  · exact B578843
  · exact B578847
  · exact B578851
  · exact B578855
  · exact B578859
  · exact B578863
  · exact B578867
  · exact B578871
  · exact B578875
  · exact B578879
  · exact B578883
  · exact B578887
  · exact B578891
  · exact B578895
  · exact B578899
  · exact B578903
  · exact B578907
  · exact B578911
  · exact B578915
  · exact B578919
  · exact B578923
  · exact B578927
  · exact B578931
  · exact B578935
  · exact B578939
  · exact B578943
  · exact B578947
  · exact B578951
  · exact B578955
  · exact B578959
  · exact B578963
  · exact B578967
  · exact B578971
  · exact B578975
  · exact B578979
  · exact B578983
  · exact B578987
  · exact B578991
  · exact B578995
  · exact B578999
  · exact B579003
  · exact B579007
  · exact B579011
  · exact B579015
  · exact B579019
  · exact B579023
  · exact B579027
  · exact B579031
  · exact B579035
  · exact B579039
  · exact B579043
  · exact B579047
  · exact B579051
  · exact B579055
  · exact B579059
  · exact B579063
  · exact B579067
  · exact B579071
  · exact B579075
  · exact B579079
  · exact B579083
  · exact B579087
  · exact B579091
  · exact B579095
  · exact B579099
  · exact B579103
  · exact B579107
  · exact B579111
  · exact B579115
  · exact B579119
  · exact B579123
  · exact B579127
  · exact B579131
  · exact B579135
  · exact B579139
  · exact B579143
  · exact B579147
  · exact B579151
  · exact B579155
  · exact B579159
  · exact B579163
  · exact B579167
  · exact B579171
  · exact B579175
  · exact B579179
  · exact B579183
  · exact B579187
  · exact B579191
  · exact B579195
  · exact B579199
  · exact B579203
  · exact B579207
  · exact B579211
  · exact B579215
  · exact B579219
  · exact B579223
  · exact B579227
  · exact B579231
  · exact B579235
  · exact B579239
  · exact B579243
  · exact B579247
  · exact B579251
  · exact B579255
  · exact B579259
  · exact B579263
  · exact B579267
  · exact B579271
  · exact B579275
  · exact B579279
  · exact B579283
  · exact B579287
  · exact B579291
  · exact B579295
  · exact B579299
  · exact B579303
  · exact B579307
  · exact B579311
  · exact B579315
  · exact B579319
  · exact B579323
  · exact B579327
  · exact B579331
  · exact B579335
  · exact B579339
  · exact B579343
  · exact B579347
  · exact B579351
  · exact B579355
  · exact B579359
  · exact B579363
  · exact B579367
  · exact B579371
  · exact B579375
  · exact B579379
  · exact B579383
  · exact B579387
  · exact B579391
  · exact B579395
  · exact B579399
  · exact B579403
  · exact B579407
  · exact B579411
  · exact B579415
  · exact B579419
  · exact B579423
  · exact B579427
  · exact B579431
  · exact B579435
  · exact B579439
  · exact B579443
  · exact B579447
  · exact B579451
  · exact B579455
  · exact B579459
  · exact B579463
  · exact B579467
  · exact B579471
  · exact B579475
  · exact B579479
  · exact B579483
  · exact B579487
  · exact B579491
  · exact B579495
  · exact B579499
  · exact B579503
  · exact B579507
  · exact B579511
  · exact B579515
  · exact B579519
  · exact B579523
  · exact B579527
  · exact B579531
  · exact B579535
  · exact B579539
  · exact B579543
  · exact B579547
  · exact B579551
  · exact B579555
  · exact B579559
  · exact B579563
  · exact B579567
  · exact B579571
  · exact B579575
  · exact B579579
  · exact B579583
  · exact B579587
  · exact B579591
  · exact B579595
  · exact B579599
  · exact B579603
  · exact B579607
  · exact B579611
  · exact B579615
  · exact B579619
  · exact B579623
  · exact B579627
  · exact B579631
  · exact B579635
  · exact B579639
  · exact B579643
  · exact B579647
  · exact B579651
  · exact B579655
  · exact B579659
  · exact B579663
  · exact B579667
  · exact B579671
  · exact B579675
  · exact B579679
  · exact B579683
  · exact B579687
  · exact B579691
  · exact B579695
  · exact B579699
  · exact B579703
  · exact B579707
  · exact B579711
  · exact B579715
  · exact B579719
  · exact B579723
  · exact B579727
  · exact B579731
  · exact B579735
  · exact B579739
  · exact B579743
  · exact B579747
  · exact B579751
  · exact B579755
  · exact B579759
  · exact B579763
  · exact B579767
  · exact B579771
  · exact B579775
  · exact B579779
  · exact B579783
  · exact B579787
  · exact B579791
  · exact B579795
  · exact B579799
  · exact B579803
  · exact B579807
  · exact B579811
  · exact B579815
  · exact B579819
  · exact B579823
  · exact B579827
  · exact B579831
  · exact B579835
  · exact B579839
  · exact B579843
  · exact B579847
  · exact B579851
  · exact B579855
  · exact B579859
  · exact B579863
  · exact B579867
  · exact B579871
  · exact B579875
  · exact B579879
  · exact B579883
  · exact B579887
  · exact B579891
  · exact B579895
  · exact B579899
  · exact B579903
  · exact B579907
  · exact B579911
  · exact B579915
  · exact B579919
  · exact B579923
  · exact B579927
  · exact B579931
  · exact B579935
  · exact B579939
  · exact B579943
  · exact B579947
  · exact B579951
  · exact B579955
  · exact B579959
  · exact B579963
  · exact B579967
  · exact B579971
  · exact B579975
  · exact B579979
  · exact B579983
  · exact B579987
  · exact B579991
  · exact B579995
  · exact B579999
  · exact B580003
  · exact B580007
  · exact B580011
  · exact B580015
  · exact B580019
  · exact B580023
  · exact B580027
  · exact B580031
  · exact B580035
  · exact B580039
  · exact B580043
  · exact B580047
  · exact B580051
  · exact B580055
  · exact B580059
  · exact B580063
  · exact B580067
  · exact B580071
  · exact B580075
  · exact B580079
  · exact B580083
  · exact B580087
  · exact B580091
  · exact B580095
  · exact B580099
  · exact B580103
  · exact B580107
  · exact B580111
  · exact B580115
  · exact B580119
  · exact B580123
  · exact B580127
  · exact B580131
  · exact B580135
  · exact B580139
  · exact B580143
  · exact B580147
  · exact B580151
  · exact B580155
  · exact B580159
  · exact B580163
  · exact B580167
  · exact B580171
  · exact B580175
  · exact B580179
  · exact B580183
  · exact B580187
  · exact B580191
  · exact B580195
  · exact B580199
  · exact B580203
  · exact B580207
  · exact B580211
  · exact B580215
  · exact B580219
  · exact B580223
  · exact B580227
  · exact B580231
  · exact B580235
  · exact B580239
  · exact B580243
  · exact B580247
  · exact B580251
  · exact B580255
  · exact B580259
  · exact B580263
  · exact B580267
  · exact B580271
  · exact B580275
  · exact B580279
  · exact B580283
  · exact B580287
  · exact B580291
  · exact B580295
  · exact B580299
  · exact B580303
  · exact B580307
  · exact B580311
  · exact B580315
  · exact B580319
  · exact B580323
  · exact B580327
  · exact B580331
  · exact B580335
  · exact B580339
  · exact B580343
  · exact B580347
  · exact B580351
  · exact B580355
  · exact B580359
  · exact B580363
  · exact B580367
  · exact B580371
  · exact B580375
  · exact B580379
  · exact B580383
  · exact B580387
  · exact B580391
  · exact B580395
  · exact B580399
  · exact B580403
  · exact B580407
  · exact B580411
  · exact B580415
  · exact B580419
  · exact B580423
  · exact B580427
  · exact B580431
  · exact B580435
  · exact B580439
  · exact B580443
  · exact B580447
  · exact B580451
  · exact B580455
  · exact B580459
  · exact B580463
  · exact B580467
  · exact B580471
  · exact B580475
  · exact B580479
  · exact B580483
  · exact B580487
  · exact B580491
  · exact B580495
  · exact B580499
  · exact B580503
  · exact B580507
  · exact B580511
  · exact B580515
  · exact B580519
  · exact B580523
  · exact B580527
  · exact B580531
  · exact B580535
  · exact B580539
  · exact B580543
  · exact B580547
  · exact B580551
  · exact B580555
  · exact B580559
  · exact B580563
  · exact B580567
  · exact B580571
  · exact B580575
  · exact B580579
  · exact B580583
  · exact B580587
  · exact B580591
  · exact B580595
  · exact B580599
  · exact B580603
  · exact B580607
  · exact B580611
  · exact B580615
  · exact B580619
  · exact B580623
  · exact B580627
  · exact B580631
  · exact B580635
  · exact B580639
  · exact B580643
  · exact B580647
  · exact B580651
  · exact B580655
  · exact B580659
  · exact B580663
  · exact B580667
  · exact B580671
  · exact B580675
  · exact B580679
  · exact B580683
  · exact B580687
  · exact B580691
  · exact B580695
  · exact B580699
  · exact B580703
  · exact B580707
  · exact B580711
  · exact B580715
  · exact B580719
  · exact B580723
  · exact B580727
  · exact B580731
  · exact B580735
  · exact B580739
  · exact B580743
  · exact B580747
  · exact B580751
  · exact B580755
  · exact B580759
  · exact B580763
  · exact B580767
  · exact B580771
  · exact B580775
  · exact B580779
  · exact B580783
  · exact B580787
  · exact B580791
  · exact B580795
  · exact B580799
  · exact B580803
  · exact B580807
  · exact B580811
  · exact B580815
  · exact B580819
  · exact B580823
  · exact B580827
  · exact B580831
  · exact B580835
  · exact B580839
  · exact B580843
  · exact B580847
  · exact B580851
  · exact B580855
  · exact B580859
  · exact B580863
  · exact B580867
  · exact B580871
  · exact B580875
  · exact B580879
  · exact B580883
  · exact B580887
  · exact B580891
  · exact B580895
  · exact B580899
  · exact B580903
  · exact B580907
  · exact B580911
  · exact B580915
  · exact B580919
  · exact B580923
  · exact B580927
  · exact B580931
  · exact B580935
  · exact B580939
  · exact B580943
  · exact B580947
  · exact B580951
  · exact B580955
  · exact B580959
  · exact B580963
  · exact B580967
  · exact B580971
  · exact B580975
  · exact B580979
  · exact B580983
  · exact B580987
  · exact B580991
  · exact B580995
  · exact B580999
  · exact B581003
  · exact B581007
  · exact B581011
  · exact B581015
  · exact B581019
  · exact B581023
  · exact B581027
  · exact B581031
  · exact B581035
  · exact B581039
  · exact B581043
  · exact B581047
  · exact B581051
  · exact B581055
  · exact B581059
  · exact B581063
  · exact B581067
  · exact B581071
  · exact B581075
  · exact B581079
  · exact B581083
  · exact B581087
  · exact B581091
  · exact B581095
  · exact B581099
  · exact B581103
  · exact B581107
  · exact B581111
  · exact B581115
  · exact B581119
  · exact B581123
  · exact B581127
  · exact B581131
  · exact B581135
  · exact B581139
  · exact B581143
  · exact B581147
  · exact B581151
  · exact B581155
  · exact B581159
  · exact B581163
  · exact B581167
  · exact B581171
  · exact B581175
  · exact B581179
  · exact B581183
  · exact B581187
  · exact B581191
  · exact B581195
  · exact B581199
  · exact B581203
  · exact B581207
  · exact B581211
  · exact B581215
  · exact B581219
  · exact B581223
  · exact B581227
  · exact B581231
  · exact B581235
  · exact B581239
  · exact B581243
  · exact B581247
  · exact B581251
  · exact B581255
  · exact B581259
  · exact B581263
  · exact B581267
  · exact B581271
  · exact B581275
  · exact B581279
  · exact B581283
  · exact B581287
  · exact B581291
  · exact B581295
  · exact B581299
  · exact B581303
  · exact B581307
  · exact B581311
  · exact B581315
  · exact B581319
  · exact B581323
  · exact B581327
  · exact B581331
  · exact B581335
  · exact B581339
  · exact B581343
  · exact B581347
  · exact B581351
  · exact B581355
  · exact B581359
  · exact B581363
  · exact B581367
  · exact B581371
  · exact B581375
  · exact B581379
  · exact B581383
  · exact B581387
  · exact B581391
  · exact B581395
  · exact B581399
  · exact B581403
  · exact B581407
  · exact B581411
  · exact B581415
  · exact B581419
  · exact B581423
  · exact B581427
  · exact B581431
  · exact B581435
  · exact B581439
  · exact B581443
  · exact B581447
  · exact B581451
  · exact B581455
  · exact B581459
  · exact B581463
  · exact B581467
  · exact B581471
  · exact B581475
  · exact B581479
  · exact B581483
  · exact B581487
  · exact B581491
  · exact B581495
  · exact B581499
  · exact B581503
  · exact B581507
  · exact B581511
  · exact B581515
  · exact B581519
  · exact B581523
  · exact B581527
  · exact B581531
  · exact B581535
  · exact B581539
  · exact B581543
  · exact B581547
  · exact B581551
  · exact B581555
  · exact B581559
  · exact B581563
  · exact B581567
  · exact B581571
  · exact B581575
  · exact B581579
  · exact B581583
  · exact B581587
  · exact B581591
  · exact B581595
  · exact B581599
  · exact B581603
  · exact B581607
  · exact B581611

theorem C1 (j : ℕ) (h1 : 145403 ≤ j) (h2 : j ≤ 145702) : Blo 578813 (4 * j + 3) := by
  interval_cases j
  · exact B581615
  · exact B581619
  · exact B581623
  · exact B581627
  · exact B581631
  · exact B581635
  · exact B581639
  · exact B581643
  · exact B581647
  · exact B581651
  · exact B581655
  · exact B581659
  · exact B581663
  · exact B581667
  · exact B581671
  · exact B581675
  · exact B581679
  · exact B581683
  · exact B581687
  · exact B581691
  · exact B581695
  · exact B581699
  · exact B581703
  · exact B581707
  · exact B581711
  · exact B581715
  · exact B581719
  · exact B581723
  · exact B581727
  · exact B581731
  · exact B581735
  · exact B581739
  · exact B581743
  · exact B581747
  · exact B581751
  · exact B581755
  · exact B581759
  · exact B581763
  · exact B581767
  · exact B581771
  · exact B581775
  · exact B581779
  · exact B581783
  · exact B581787
  · exact B581791
  · exact B581795
  · exact B581799
  · exact B581803
  · exact B581807
  · exact B581811
  · exact B581815
  · exact B581819
  · exact B581823
  · exact B581827
  · exact B581831
  · exact B581835
  · exact B581839
  · exact B581843
  · exact B581847
  · exact B581851
  · exact B581855
  · exact B581859
  · exact B581863
  · exact B581867
  · exact B581871
  · exact B581875
  · exact B581879
  · exact B581883
  · exact B581887
  · exact B581891
  · exact B581895
  · exact B581899
  · exact B581903
  · exact B581907
  · exact B581911
  · exact B581915
  · exact B581919
  · exact B581923
  · exact B581927
  · exact B581931
  · exact B581935
  · exact B581939
  · exact B581943
  · exact B581947
  · exact B581951
  · exact B581955
  · exact B581959
  · exact B581963
  · exact B581967
  · exact B581971
  · exact B581975
  · exact B581979
  · exact B581983
  · exact B581987
  · exact B581991
  · exact B581995
  · exact B581999
  · exact B582003
  · exact B582007
  · exact B582011
  · exact B582015
  · exact B582019
  · exact B582023
  · exact B582027
  · exact B582031
  · exact B582035
  · exact B582039
  · exact B582043
  · exact B582047
  · exact B582051
  · exact B582055
  · exact B582059
  · exact B582063
  · exact B582067
  · exact B582071
  · exact B582075
  · exact B582079
  · exact B582083
  · exact B582087
  · exact B582091
  · exact B582095
  · exact B582099
  · exact B582103
  · exact B582107
  · exact B582111
  · exact B582115
  · exact B582119
  · exact B582123
  · exact B582127
  · exact B582131
  · exact B582135
  · exact B582139
  · exact B582143
  · exact B582147
  · exact B582151
  · exact B582155
  · exact B582159
  · exact B582163
  · exact B582167
  · exact B582171
  · exact B582175
  · exact B582179
  · exact B582183
  · exact B582187
  · exact B582191
  · exact B582195
  · exact B582199
  · exact B582203
  · exact B582207
  · exact B582211
  · exact B582215
  · exact B582219
  · exact B582223
  · exact B582227
  · exact B582231
  · exact B582235
  · exact B582239
  · exact B582243
  · exact B582247
  · exact B582251
  · exact B582255
  · exact B582259
  · exact B582263
  · exact B582267
  · exact B582271
  · exact B582275
  · exact B582279
  · exact B582283
  · exact B582287
  · exact B582291
  · exact B582295
  · exact B582299
  · exact B582303
  · exact B582307
  · exact B582311
  · exact B582315
  · exact B582319
  · exact B582323
  · exact B582327
  · exact B582331
  · exact B582335
  · exact B582339
  · exact B582343
  · exact B582347
  · exact B582351
  · exact B582355
  · exact B582359
  · exact B582363
  · exact B582367
  · exact B582371
  · exact B582375
  · exact B582379
  · exact B582383
  · exact B582387
  · exact B582391
  · exact B582395
  · exact B582399
  · exact B582403
  · exact B582407
  · exact B582411
  · exact B582415
  · exact B582419
  · exact B582423
  · exact B582427
  · exact B582431
  · exact B582435
  · exact B582439
  · exact B582443
  · exact B582447
  · exact B582451
  · exact B582455
  · exact B582459
  · exact B582463
  · exact B582467
  · exact B582471
  · exact B582475
  · exact B582479
  · exact B582483
  · exact B582487
  · exact B582491
  · exact B582495
  · exact B582499
  · exact B582503
  · exact B582507
  · exact B582511
  · exact B582515
  · exact B582519
  · exact B582523
  · exact B582527
  · exact B582531
  · exact B582535
  · exact B582539
  · exact B582543
  · exact B582547
  · exact B582551
  · exact B582555
  · exact B582559
  · exact B582563
  · exact B582567
  · exact B582571
  · exact B582575
  · exact B582579
  · exact B582583
  · exact B582587
  · exact B582591
  · exact B582595
  · exact B582599
  · exact B582603
  · exact B582607
  · exact B582611
  · exact B582615
  · exact B582619
  · exact B582623
  · exact B582627
  · exact B582631
  · exact B582635
  · exact B582639
  · exact B582643
  · exact B582647
  · exact B582651
  · exact B582655
  · exact B582659
  · exact B582663
  · exact B582667
  · exact B582671
  · exact B582675
  · exact B582679
  · exact B582683
  · exact B582687
  · exact B582691
  · exact B582695
  · exact B582699
  · exact B582703
  · exact B582707
  · exact B582711
  · exact B582715
  · exact B582719
  · exact B582723
  · exact B582727
  · exact B582731
  · exact B582735
  · exact B582739
  · exact B582743
  · exact B582747
  · exact B582751
  · exact B582755
  · exact B582759
  · exact B582763
  · exact B582767
  · exact B582771
  · exact B582775
  · exact B582779
  · exact B582783
  · exact B582787
  · exact B582791
  · exact B582795
  · exact B582799
  · exact B582803
  · exact B582807
  · exact B582811

theorem solution (m : ℕ) (hlo : 578813 ≤ m) (hhi : m ≤ 582813) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 144703 ≤ j := by omega
    have hj2 : j ≤ 145702 := by omega
    have hb : Blo 578813 (4 * j + 3) := by
      rcases Nat.lt_or_ge j 145403 with hc0 | hc0
      · exact C0 j (by omega) (by omega)
      exact C1 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
