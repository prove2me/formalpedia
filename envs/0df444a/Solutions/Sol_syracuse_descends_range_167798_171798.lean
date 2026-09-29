-- Prove2me | solution 1 for syracuse_descends_range_167798_171798
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-09T16:43:43.552183+00:00
-- url     : https://prove2.me/submissions/80627e72-a484-4390-9cd8-9e602426881b

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


theorem B557237 : Blo 167798 557237 := bbase (se 5 (by rfl) ⟨26120, by rfl⟩ : syracuseStep 557237 = 52241) (by norm_num)
theorem B295093 : Blo 167798 295093 := bbase (se 5 (by rfl) ⟨13832, by rfl⟩ : syracuseStep 295093 = 27665) (by norm_num)
theorem B229565 : Blo 167798 229565 := bbase (se 3 (by rfl) ⟨43043, by rfl⟩ : syracuseStep 229565 = 86087) (by norm_num)
theorem B426181 : Blo 167798 426181 := bbase (se 4 (by rfl) ⟨39954, by rfl⟩ : syracuseStep 426181 = 79909) (by norm_num)
theorem B524485 : Blo 167798 524485 := bbase (se 4 (by rfl) ⟨49170, by rfl⟩ : syracuseStep 524485 = 98341) (by norm_num)
theorem B426293 : Blo 167798 426293 := bbase (se 5 (by rfl) ⟨19982, by rfl⟩ : syracuseStep 426293 = 39965) (by norm_num)
theorem B360821 : Blo 167798 360821 := bbase (se 5 (by rfl) ⟨16913, by rfl⟩ : syracuseStep 360821 = 33827) (by norm_num)
theorem B426485 : Blo 167798 426485 := bbase (se 5 (by rfl) ⟨19991, by rfl⟩ : syracuseStep 426485 = 39983) (by norm_num)
theorem B819845 : Blo 167798 819845 := bbase (se 4 (by rfl) ⟨76860, by rfl⟩ : syracuseStep 819845 = 153721) (by norm_num)
theorem B361189 : Blo 167798 361189 := bbase (se 4 (by rfl) ⟨33861, by rfl⟩ : syracuseStep 361189 = 67723) (by norm_num)
theorem B426829 : Blo 167798 426829 := bbase (se 3 (by rfl) ⟨80030, by rfl⟩ : syracuseStep 426829 = 160061) (by norm_num)
theorem B263093 : Blo 167798 263093 := bbase (se 5 (by rfl) ⟨12332, by rfl⟩ : syracuseStep 263093 = 24665) (by norm_num)
theorem B426941 : Blo 167798 426941 := bbase (se 3 (by rfl) ⟨80051, by rfl⟩ : syracuseStep 426941 = 160103) (by norm_num)
theorem B427133 : Blo 167798 427133 := bbase (se 3 (by rfl) ⟨80087, by rfl⟩ : syracuseStep 427133 = 160175) (by norm_num)
theorem B853253 : Blo 167798 853253 := bbase (se 4 (by rfl) ⟨79992, by rfl⟩ : syracuseStep 853253 = 159985) (by norm_num)
theorem B427477 : Blo 167798 427477 := bbase (se 7 (by rfl) ⟨5009, by rfl⟩ : syracuseStep 427477 = 10019) (by norm_num)
theorem B230917 : Blo 167798 230917 := bbase (se 4 (by rfl) ⟨21648, by rfl⟩ : syracuseStep 230917 = 43297) (by norm_num)
theorem B394813 : Blo 167798 394813 := bbase (se 3 (by rfl) ⟨74027, by rfl⟩ : syracuseStep 394813 = 148055) (by norm_num)
theorem B427589 : Blo 167798 427589 := bbase (se 4 (by rfl) ⟨40086, by rfl⟩ : syracuseStep 427589 = 80173) (by norm_num)
theorem B1279637 : Blo 167798 1279637 := bbase (se 6 (by rfl) ⟨29991, by rfl⟩ : syracuseStep 1279637 = 59983) (by norm_num)
theorem B427781 : Blo 167798 427781 := bbase (se 4 (by rfl) ⟨40104, by rfl⟩ : syracuseStep 427781 = 80209) (by norm_num)
theorem B722789 : Blo 167798 722789 := bbase (se 4 (by rfl) ⟨67761, by rfl⟩ : syracuseStep 722789 = 135523) (by norm_num)
theorem B428125 : Blo 167798 428125 := bbase (se 3 (by rfl) ⟨80273, by rfl⟩ : syracuseStep 428125 = 160547) (by norm_num)
theorem B723077 : Blo 167798 723077 := bbase (se 4 (by rfl) ⟨67788, by rfl⟩ : syracuseStep 723077 = 135577) (by norm_num)
theorem B362693 : Blo 167798 362693 := bbase (se 4 (by rfl) ⟨34002, by rfl⟩ : syracuseStep 362693 = 68005) (by norm_num)
theorem B428237 : Blo 167798 428237 := bbase (se 3 (by rfl) ⟨80294, by rfl⟩ : syracuseStep 428237 = 160589) (by norm_num)
theorem B362837 : Blo 167798 362837 := bbase (se 10 (by rfl) ⟨531, by rfl⟩ : syracuseStep 362837 = 1063) (by norm_num)
theorem B428429 : Blo 167798 428429 := bbase (se 3 (by rfl) ⟨80330, by rfl⟩ : syracuseStep 428429 = 160661) (by norm_num)
theorem B854549 : Blo 167798 854549 := bbase (se 6 (by rfl) ⟨20028, by rfl⟩ : syracuseStep 854549 = 40057) (by norm_num)
theorem B625205 : Blo 167798 625205 := bbase (se 5 (by rfl) ⟨29306, by rfl⟩ : syracuseStep 625205 = 58613) (by norm_num)
theorem B658037 : Blo 167798 658037 := bbase (se 5 (by rfl) ⟨30845, by rfl⟩ : syracuseStep 658037 = 61691) (by norm_num)
theorem B363197 : Blo 167798 363197 := bbase (se 3 (by rfl) ⟨68099, by rfl⟩ : syracuseStep 363197 = 136199) (by norm_num)
theorem B428773 : Blo 167798 428773 := bbase (se 4 (by rfl) ⟨40197, by rfl⟩ : syracuseStep 428773 = 80395) (by norm_num)
theorem B1575733 : Blo 167798 1575733 := bbase (se 5 (by rfl) ⟨73862, by rfl⟩ : syracuseStep 1575733 = 147725) (by norm_num)
theorem B428885 : Blo 167798 428885 := bbase (se 9 (by rfl) ⟨1256, by rfl⟩ : syracuseStep 428885 = 2513) (by norm_num)
theorem B723829 : Blo 167798 723829 := bbase (se 5 (by rfl) ⟨33929, by rfl⟩ : syracuseStep 723829 = 67859) (by norm_num)
theorem B429077 : Blo 167798 429077 := bbase (se 6 (by rfl) ⟨10056, by rfl⟩ : syracuseStep 429077 = 20113) (by norm_num)
theorem B2067605 : Blo 167798 2067605 := bbase (se 6 (by rfl) ⟨48459, by rfl⟩ : syracuseStep 2067605 = 96919) (by norm_num)
theorem B527717 : Blo 167798 527717 := bbase (se 4 (by rfl) ⟨49473, by rfl⟩ : syracuseStep 527717 = 98947) (by norm_num)
theorem B429421 : Blo 167798 429421 := bbase (se 3 (by rfl) ⟨80516, by rfl⟩ : syracuseStep 429421 = 161033) (by norm_num)
theorem B3083669 : Blo 167798 3083669 := bbase (se 6 (by rfl) ⟨72273, by rfl⟩ : syracuseStep 3083669 = 144547) (by norm_num)
theorem B429533 : Blo 167798 429533 := bbase (se 3 (by rfl) ⟨80537, by rfl⟩ : syracuseStep 429533 = 161075) (by norm_num)
theorem B364085 : Blo 167798 364085 := bbase (se 5 (by rfl) ⟨17066, by rfl⟩ : syracuseStep 364085 = 34133) (by norm_num)
theorem B724565 : Blo 167798 724565 := bbase (se 8 (by rfl) ⟨4245, by rfl⟩ : syracuseStep 724565 = 8491) (by norm_num)
theorem B429725 : Blo 167798 429725 := bbase (se 3 (by rfl) ⟨80573, by rfl⟩ : syracuseStep 429725 = 161147) (by norm_num)
theorem B659141 : Blo 167798 659141 := bbase (se 4 (by rfl) ⟨61794, by rfl⟩ : syracuseStep 659141 = 123589) (by norm_num)
theorem B691973 : Blo 167798 691973 := bbase (se 4 (by rfl) ⟨64872, by rfl⟩ : syracuseStep 691973 = 129745) (by norm_num)
theorem B855845 : Blo 167798 855845 := bbase (se 4 (by rfl) ⟨80235, by rfl⟩ : syracuseStep 855845 = 160471) (by norm_num)
theorem B364333 : Blo 167798 364333 := bbase (se 3 (by rfl) ⟨68312, by rfl⟩ : syracuseStep 364333 = 136625) (by norm_num)
theorem B2625493 : Blo 167798 2625493 := bbase (se 7 (by rfl) ⟨30767, by rfl⟩ : syracuseStep 2625493 = 61535) (by norm_num)
theorem B430069 : Blo 167798 430069 := bbase (se 5 (by rfl) ⟨20159, by rfl⟩ : syracuseStep 430069 = 40319) (by norm_num)
theorem B1216565 : Blo 167798 1216565 := bbase (se 5 (by rfl) ⟨57026, by rfl⟩ : syracuseStep 1216565 = 114053) (by norm_num)
theorem B430181 : Blo 167798 430181 := bbase (se 4 (by rfl) ⟨40329, by rfl⟩ : syracuseStep 430181 = 80659) (by norm_num)
theorem B463013 : Blo 167798 463013 := bbase (se 4 (by rfl) ⟨43407, by rfl⟩ : syracuseStep 463013 = 86815) (by norm_num)
theorem B430373 : Blo 167798 430373 := bbase (se 4 (by rfl) ⟨40347, by rfl⟩ : syracuseStep 430373 = 80695) (by norm_num)
theorem B364837 : Blo 167798 364837 := bbase (se 4 (by rfl) ⟨34203, by rfl⟩ : syracuseStep 364837 = 68407) (by norm_num)
theorem B823765 : Blo 167798 823765 := bbase (se 7 (by rfl) ⟨9653, by rfl⟩ : syracuseStep 823765 = 19307) (by norm_num)
theorem B430717 : Blo 167798 430717 := bbase (se 3 (by rfl) ⟨80759, by rfl⟩ : syracuseStep 430717 = 161519) (by norm_num)
theorem B430829 : Blo 167798 430829 := bbase (se 3 (by rfl) ⟨80780, by rfl⟩ : syracuseStep 430829 = 161561) (by norm_num)
theorem B430973 : Blo 167798 430973 := bbase (se 3 (by rfl) ⟨80807, by rfl⟩ : syracuseStep 430973 = 161615) (by norm_num)
theorem B431021 : Blo 167798 431021 := bbase (se 3 (by rfl) ⟨80816, by rfl⟩ : syracuseStep 431021 = 161633) (by norm_num)
theorem B857141 : Blo 167798 857141 := bbase (se 5 (by rfl) ⟨40178, by rfl⟩ : syracuseStep 857141 = 80357) (by norm_num)
theorem B201785 : Blo 167798 201785 := bbase (se 2 (by rfl) ⟨75669, by rfl⟩ : syracuseStep 201785 = 151339) (by norm_num)
theorem B201809 : Blo 167798 201809 := bbase (se 2 (by rfl) ⟨75678, by rfl⟩ : syracuseStep 201809 = 151357) (by norm_num)
theorem B463973 : Blo 167798 463973 := bbase (se 4 (by rfl) ⟨43497, by rfl⟩ : syracuseStep 463973 = 86995) (by norm_num)
theorem B365725 : Blo 167798 365725 := bbase (se 3 (by rfl) ⟨68573, by rfl⟩ : syracuseStep 365725 = 137147) (by norm_num)
theorem B431365 : Blo 167798 431365 := bbase (se 4 (by rfl) ⟨40440, by rfl⟩ : syracuseStep 431365 = 80881) (by norm_num)
theorem B431477 : Blo 167798 431477 := bbase (se 5 (by rfl) ⟨20225, by rfl⟩ : syracuseStep 431477 = 40451) (by norm_num)
theorem B202117 : Blo 167798 202117 := bbase (se 4 (by rfl) ⟨18948, by rfl⟩ : syracuseStep 202117 = 37897) (by norm_num)
theorem B660869 : Blo 167798 660869 := bbase (se 4 (by rfl) ⟨61956, by rfl⟩ : syracuseStep 660869 = 123913) (by norm_num)
theorem B202289 : Blo 167798 202289 := bbase (se 2 (by rfl) ⟨75858, by rfl⟩ : syracuseStep 202289 = 151717) (by norm_num)
theorem B431669 : Blo 167798 431669 := bbase (se 5 (by rfl) ⟨20234, by rfl⟩ : syracuseStep 431669 = 40469) (by norm_num)
theorem B366221 : Blo 167798 366221 := bbase (se 3 (by rfl) ⟨68666, by rfl⟩ : syracuseStep 366221 = 137333) (by norm_num)
theorem B202405 : Blo 167798 202405 := bbase (se 4 (by rfl) ⟨18975, by rfl⟩ : syracuseStep 202405 = 37951) (by norm_num)
theorem B1316533 : Blo 167798 1316533 := bbase (se 5 (by rfl) ⟨61712, by rfl⟩ : syracuseStep 1316533 = 123425) (by norm_num)
theorem B202501 : Blo 167798 202501 := bbase (se 4 (by rfl) ⟨18984, by rfl⟩ : syracuseStep 202501 = 37969) (by norm_num)
theorem B432013 : Blo 167798 432013 := bbase (se 3 (by rfl) ⟨81002, by rfl⟩ : syracuseStep 432013 = 162005) (by norm_num)
theorem B202645 : Blo 167798 202645 := bbase (se 6 (by rfl) ⟨4749, by rfl⟩ : syracuseStep 202645 = 9499) (by norm_num)
theorem B1644533 : Blo 167798 1644533 := bbase (se 5 (by rfl) ⟨77087, by rfl⟩ : syracuseStep 1644533 = 154175) (by norm_num)
theorem B432125 : Blo 167798 432125 := bbase (se 3 (by rfl) ⟨81023, by rfl⟩ : syracuseStep 432125 = 162047) (by norm_num)
theorem B432317 : Blo 167798 432317 := bbase (se 3 (by rfl) ⟨81059, by rfl⟩ : syracuseStep 432317 = 162119) (by norm_num)
theorem B858437 : Blo 167798 858437 := bbase (se 4 (by rfl) ⟨80478, by rfl⟩ : syracuseStep 858437 = 160957) (by norm_num)
theorem B432661 : Blo 167798 432661 := bbase (se 6 (by rfl) ⟨10140, by rfl⟩ : syracuseStep 432661 = 20281) (by norm_num)
theorem B268861 : Blo 167798 268861 := bbase (se 3 (by rfl) ⟨50411, by rfl⟩ : syracuseStep 268861 = 100823) (by norm_num)
theorem B432773 : Blo 167798 432773 := bbase (se 4 (by rfl) ⟨40572, by rfl⟩ : syracuseStep 432773 = 81145) (by norm_num)
theorem B727861 : Blo 167798 727861 := bbase (se 5 (by rfl) ⟨34118, by rfl⟩ : syracuseStep 727861 = 68237) (by norm_num)
theorem B432965 : Blo 167798 432965 := bbase (se 4 (by rfl) ⟨40590, by rfl⟩ : syracuseStep 432965 = 81181) (by norm_num)
theorem B269309 : Blo 167798 269309 := bbase (se 3 (by rfl) ⟨50495, by rfl⟩ : syracuseStep 269309 = 100991) (by norm_num)
theorem B367669 : Blo 167798 367669 := bbase (se 5 (by rfl) ⟨17234, by rfl⟩ : syracuseStep 367669 = 34469) (by norm_num)
theorem B662581 : Blo 167798 662581 := bbase (se 5 (by rfl) ⟨31058, by rfl⟩ : syracuseStep 662581 = 62117) (by norm_num)
theorem B433309 : Blo 167798 433309 := bbase (se 3 (by rfl) ⟨81245, by rfl⟩ : syracuseStep 433309 = 162491) (by norm_num)
theorem B695557 : Blo 167798 695557 := bbase (se 4 (by rfl) ⟨65208, by rfl⟩ : syracuseStep 695557 = 130417) (by norm_num)
theorem B433421 : Blo 167798 433421 := bbase (se 3 (by rfl) ⟨81266, by rfl⟩ : syracuseStep 433421 = 162533) (by norm_num)
theorem B695573 : Blo 167798 695573 := bbase (se 6 (by rfl) ⟨16302, by rfl⟩ : syracuseStep 695573 = 32605) (by norm_num)
theorem B433613 : Blo 167798 433613 := bbase (se 3 (by rfl) ⟨81302, by rfl⟩ : syracuseStep 433613 = 162605) (by norm_num)
theorem B204365 : Blo 167798 204365 := bbase (se 3 (by rfl) ⟨38318, by rfl⟩ : syracuseStep 204365 = 76637) (by norm_num)
theorem B859733 : Blo 167798 859733 := bbase (se 8 (by rfl) ⟨5037, by rfl⟩ : syracuseStep 859733 = 10075) (by norm_num)
theorem B204481 : Blo 167798 204481 := bbase (se 2 (by rfl) ⟨76680, by rfl⟩ : syracuseStep 204481 = 153361) (by norm_num)
theorem B204553 : Blo 167798 204553 := bbase (se 2 (by rfl) ⟨76707, by rfl⟩ : syracuseStep 204553 = 153415) (by norm_num)
theorem B433957 : Blo 167798 433957 := bbase (se 4 (by rfl) ⟨40683, by rfl⟩ : syracuseStep 433957 = 81367) (by norm_num)
theorem B1449845 : Blo 167798 1449845 := bbase (se 5 (by rfl) ⟨67961, by rfl⟩ : syracuseStep 1449845 = 135923) (by norm_num)
theorem B204673 : Blo 167798 204673 := bbase (se 2 (by rfl) ⟨76752, by rfl⟩ : syracuseStep 204673 = 153505) (by norm_num)
theorem B434069 : Blo 167798 434069 := bbase (se 6 (by rfl) ⟨10173, by rfl⟩ : syracuseStep 434069 = 20347) (by norm_num)
theorem B2957269 : Blo 167798 2957269 := bbase (se 7 (by rfl) ⟨34655, by rfl⟩ : syracuseStep 2957269 = 69311) (by norm_num)
theorem B434261 : Blo 167798 434261 := bbase (se 8 (by rfl) ⟨2544, by rfl⟩ : syracuseStep 434261 = 5089) (by norm_num)
theorem B205057 : Blo 167798 205057 := bbase (se 2 (by rfl) ⟨76896, by rfl⟩ : syracuseStep 205057 = 153793) (by norm_num)
theorem B1089845 : Blo 167798 1089845 := bbase (se 5 (by rfl) ⟨51086, by rfl⟩ : syracuseStep 1089845 = 102173) (by norm_num)
theorem B172369 : Blo 167798 172369 := bbase (se 2 (by rfl) ⟨64638, by rfl⟩ : syracuseStep 172369 = 129277) (by norm_num)
theorem B434605 : Blo 167798 434605 := bbase (se 3 (by rfl) ⟨81488, by rfl⟩ : syracuseStep 434605 = 162977) (by norm_num)
theorem B270821 : Blo 167798 270821 := bbase (se 4 (by rfl) ⟨25389, by rfl⟩ : syracuseStep 270821 = 50779) (by norm_num)
theorem B434717 : Blo 167798 434717 := bbase (se 3 (by rfl) ⟨81509, by rfl⟩ : syracuseStep 434717 = 163019) (by norm_num)
theorem B270949 : Blo 167798 270949 := bbase (se 4 (by rfl) ⟨25401, by rfl⟩ : syracuseStep 270949 = 50803) (by norm_num)
theorem B303853 : Blo 167798 303853 := bbase (se 3 (by rfl) ⟨56972, by rfl⟩ : syracuseStep 303853 = 113945) (by norm_num)
theorem B1155829 : Blo 167798 1155829 := bbase (se 5 (by rfl) ⟨54179, by rfl⟩ : syracuseStep 1155829 = 108359) (by norm_num)
theorem B303925 : Blo 167798 303925 := bbase (se 5 (by rfl) ⟨14246, by rfl⟩ : syracuseStep 303925 = 28493) (by norm_num)
theorem B861029 : Blo 167798 861029 := bbase (se 4 (by rfl) ⟨80721, by rfl⟩ : syracuseStep 861029 = 161443) (by norm_num)
theorem B205745 : Blo 167798 205745 := bbase (se 2 (by rfl) ⟨77154, by rfl⟩ : syracuseStep 205745 = 154309) (by norm_num)
theorem B172981 : Blo 167798 172981 := bbase (se 5 (by rfl) ⟨8108, by rfl⟩ : syracuseStep 172981 = 16217) (by norm_num)
theorem B304069 : Blo 167798 304069 := bbase (se 4 (by rfl) ⟨28506, by rfl⟩ : syracuseStep 304069 = 57013) (by norm_num)
theorem B566405 : Blo 167798 566405 := bbase (se 4 (by rfl) ⟨53100, by rfl⟩ : syracuseStep 566405 = 106201) (by norm_num)
theorem B1287413 : Blo 167798 1287413 := bbase (se 5 (by rfl) ⟨60347, by rfl⟩ : syracuseStep 1287413 = 120695) (by norm_num)
theorem B959957 : Blo 167798 959957 := bbase (se 7 (by rfl) ⟨11249, by rfl⟩ : syracuseStep 959957 = 22499) (by norm_num)
theorem B206345 : Blo 167798 206345 := bbase (se 2 (by rfl) ⟨77379, by rfl⟩ : syracuseStep 206345 = 154759) (by norm_num)
theorem B566837 : Blo 167798 566837 := bbase (se 5 (by rfl) ⟨26570, by rfl⟩ : syracuseStep 566837 = 53141) (by norm_num)
theorem B468629 : Blo 167798 468629 := bbase (se 6 (by rfl) ⟨10983, by rfl⟩ : syracuseStep 468629 = 21967) (by norm_num)
theorem B730853 : Blo 167798 730853 := bbase (se 4 (by rfl) ⟨68517, by rfl⟩ : syracuseStep 730853 = 137035) (by norm_num)
theorem B304877 : Blo 167798 304877 := bbase (se 3 (by rfl) ⟨57164, by rfl⟩ : syracuseStep 304877 = 114329) (by norm_num)
theorem B304933 : Blo 167798 304933 := bbase (se 4 (by rfl) ⟨28587, by rfl⟩ : syracuseStep 304933 = 57175) (by norm_num)
theorem B305021 : Blo 167798 305021 := bbase (se 3 (by rfl) ⟨57191, by rfl⟩ : syracuseStep 305021 = 114383) (by norm_num)
theorem B272333 : Blo 167798 272333 := bbase (se 3 (by rfl) ⟨51062, by rfl⟩ : syracuseStep 272333 = 102125) (by norm_num)
theorem B567269 : Blo 167798 567269 := bbase (se 4 (by rfl) ⟨53181, by rfl⟩ : syracuseStep 567269 = 106363) (by norm_num)
theorem B862325 : Blo 167798 862325 := bbase (se 5 (by rfl) ⟨40421, by rfl⟩ : syracuseStep 862325 = 80843) (by norm_num)
theorem B239773 : Blo 167798 239773 := bbase (se 3 (by rfl) ⟨44957, by rfl⟩ : syracuseStep 239773 = 89915) (by norm_num)
theorem B305309 : Blo 167798 305309 := bbase (se 3 (by rfl) ⟨57245, by rfl⟩ : syracuseStep 305309 = 114491) (by norm_num)
theorem B305453 : Blo 167798 305453 := bbase (se 3 (by rfl) ⟨57272, by rfl⟩ : syracuseStep 305453 = 114545) (by norm_num)
theorem B207193 : Blo 167798 207193 := bbase (se 2 (by rfl) ⟨77697, by rfl⟩ : syracuseStep 207193 = 155395) (by norm_num)
theorem B567701 : Blo 167798 567701 := bbase (se 6 (by rfl) ⟨13305, by rfl⟩ : syracuseStep 567701 = 26611) (by norm_num)
theorem B305741 : Blo 167798 305741 := bbase (se 3 (by rfl) ⟨57326, by rfl⟩ : syracuseStep 305741 = 114653) (by norm_num)
theorem B404117 : Blo 167798 404117 := bbase (se 6 (by rfl) ⟨9471, by rfl⟩ : syracuseStep 404117 = 18943) (by norm_num)
theorem B305813 : Blo 167798 305813 := bbase (se 6 (by rfl) ⟨7167, by rfl⟩ : syracuseStep 305813 = 14335) (by norm_num)
theorem B731861 : Blo 167798 731861 := bbase (se 7 (by rfl) ⟨8576, by rfl⟩ : syracuseStep 731861 = 17153) (by norm_num)
theorem B240365 : Blo 167798 240365 := bbase (se 3 (by rfl) ⟨45068, by rfl⟩ : syracuseStep 240365 = 90137) (by norm_num)
theorem B240445 : Blo 167798 240445 := bbase (se 3 (by rfl) ⟨45083, by rfl⟩ : syracuseStep 240445 = 90167) (by norm_num)
theorem B568133 : Blo 167798 568133 := bbase (se 4 (by rfl) ⟨53262, by rfl⟩ : syracuseStep 568133 = 106525) (by norm_num)
theorem B273269 : Blo 167798 273269 := bbase (se 5 (by rfl) ⟨12809, by rfl⟩ : syracuseStep 273269 = 25619) (by norm_num)
theorem B240565 : Blo 167798 240565 := bbase (se 5 (by rfl) ⟨11276, by rfl⟩ : syracuseStep 240565 = 22553) (by norm_num)
theorem B240661 : Blo 167798 240661 := bbase (se 6 (by rfl) ⟨5640, by rfl⟩ : syracuseStep 240661 = 11281) (by norm_num)
theorem B371773 : Blo 167798 371773 := bbase (se 3 (by rfl) ⟨69707, by rfl⟩ : syracuseStep 371773 = 139415) (by norm_num)
theorem B207973 : Blo 167798 207973 := bbase (se 4 (by rfl) ⟨19497, by rfl⟩ : syracuseStep 207973 = 38995) (by norm_num)
theorem B208013 : Blo 167798 208013 := bbase (se 3 (by rfl) ⟨39002, by rfl⟩ : syracuseStep 208013 = 78005) (by norm_num)
theorem B568565 : Blo 167798 568565 := bbase (se 5 (by rfl) ⟨26651, by rfl⟩ : syracuseStep 568565 = 53303) (by norm_num)
theorem B863621 : Blo 167798 863621 := bbase (se 4 (by rfl) ⟨80964, by rfl⟩ : syracuseStep 863621 = 161929) (by norm_num)
theorem B273917 : Blo 167798 273917 := bbase (se 3 (by rfl) ⟨51359, by rfl⟩ : syracuseStep 273917 = 102719) (by norm_num)
theorem B241157 : Blo 167798 241157 := bbase (se 4 (by rfl) ⟨22608, by rfl⟩ : syracuseStep 241157 = 45217) (by norm_num)
theorem B568997 : Blo 167798 568997 := bbase (se 4 (by rfl) ⟨53343, by rfl⟩ : syracuseStep 568997 = 106687) (by norm_num)
theorem B1027765 : Blo 167798 1027765 := bbase (se 5 (by rfl) ⟨48176, by rfl⟩ : syracuseStep 1027765 = 96353) (by norm_num)
theorem B438053 : Blo 167798 438053 := bbase (se 4 (by rfl) ⟨41067, by rfl⟩ : syracuseStep 438053 = 82135) (by norm_num)
theorem B438061 : Blo 167798 438061 := bbase (se 3 (by rfl) ⟨82136, by rfl⟩ : syracuseStep 438061 = 164273) (by norm_num)
theorem B438101 : Blo 167798 438101 := bbase (se 9 (by rfl) ⟨1283, by rfl⟩ : syracuseStep 438101 = 2567) (by norm_num)
theorem B307061 : Blo 167798 307061 := bbase (se 5 (by rfl) ⟨14393, by rfl⟩ : syracuseStep 307061 = 28787) (by norm_num)
theorem B241709 : Blo 167798 241709 := bbase (se 3 (by rfl) ⟨45320, by rfl⟩ : syracuseStep 241709 = 90641) (by norm_num)
theorem B569429 : Blo 167798 569429 := bbase (se 8 (by rfl) ⟨3336, by rfl⟩ : syracuseStep 569429 = 6673) (by norm_num)
theorem B733637 : Blo 167798 733637 := bbase (se 4 (by rfl) ⟨68778, by rfl⟩ : syracuseStep 733637 = 137557) (by norm_num)
theorem B274909 : Blo 167798 274909 := bbase (se 3 (by rfl) ⟨51545, by rfl⟩ : syracuseStep 274909 = 103091) (by norm_num)
theorem B569861 : Blo 167798 569861 := bbase (se 4 (by rfl) ⟨53424, by rfl⟩ : syracuseStep 569861 = 106849) (by norm_num)
theorem B242237 : Blo 167798 242237 := bbase (se 3 (by rfl) ⟨45419, by rfl⟩ : syracuseStep 242237 = 90839) (by norm_num)
theorem B864917 : Blo 167798 864917 := bbase (se 6 (by rfl) ⟨20271, by rfl⟩ : syracuseStep 864917 = 40543) (by norm_num)
theorem B1946389 : Blo 167798 1946389 := bbase (se 6 (by rfl) ⟨45618, by rfl⟩ : syracuseStep 1946389 = 91237) (by norm_num)
theorem B242461 : Blo 167798 242461 := bbase (se 3 (by rfl) ⟨45461, by rfl⟩ : syracuseStep 242461 = 90923) (by norm_num)
theorem B570293 : Blo 167798 570293 := bbase (se 5 (by rfl) ⟨26732, by rfl⟩ : syracuseStep 570293 = 53465) (by norm_num)
theorem B275581 : Blo 167798 275581 := bbase (se 3 (by rfl) ⟨51671, by rfl⟩ : syracuseStep 275581 = 103343) (by norm_num)
theorem B177301 : Blo 167798 177301 := bbase (se 6 (by rfl) ⟨4155, by rfl⟩ : syracuseStep 177301 = 8311) (by norm_num)
theorem B537797 : Blo 167798 537797 := bbase (se 4 (by rfl) ⟨50418, by rfl⟩ : syracuseStep 537797 = 100837) (by norm_num)
theorem B865637 : Blo 167798 865637 := bbase (se 4 (by rfl) ⟨81153, by rfl⟩ : syracuseStep 865637 = 162307) (by norm_num)
theorem B570725 : Blo 167798 570725 := bbase (se 4 (by rfl) ⟨53505, by rfl⟩ : syracuseStep 570725 = 107011) (by norm_num)
theorem B406885 : Blo 167798 406885 := bbase (se 4 (by rfl) ⟨38145, by rfl⟩ : syracuseStep 406885 = 76291) (by norm_num)
theorem B1095029 : Blo 167798 1095029 := bbase (se 5 (by rfl) ⟨51329, by rfl⟩ : syracuseStep 1095029 = 102659) (by norm_num)
theorem B243253 : Blo 167798 243253 := bbase (se 5 (by rfl) ⟨11402, by rfl⟩ : syracuseStep 243253 = 22805) (by norm_num)
theorem B308861 : Blo 167798 308861 := bbase (se 3 (by rfl) ⟨57911, by rfl⟩ : syracuseStep 308861 = 115823) (by norm_num)
theorem B407261 : Blo 167798 407261 := bbase (se 3 (by rfl) ⟨76361, by rfl⟩ : syracuseStep 407261 = 152723) (by norm_num)
theorem B571157 : Blo 167798 571157 := bbase (se 6 (by rfl) ⟨13386, by rfl⟩ : syracuseStep 571157 = 26773) (by norm_num)
theorem B243589 : Blo 167798 243589 := bbase (se 4 (by rfl) ⟨22836, by rfl⟩ : syracuseStep 243589 = 45673) (by norm_num)
theorem B866213 : Blo 167798 866213 := bbase (se 4 (by rfl) ⟨81207, by rfl⟩ : syracuseStep 866213 = 162415) (by norm_num)
theorem B276517 : Blo 167798 276517 := bbase (se 4 (by rfl) ⟨25923, by rfl⟩ : syracuseStep 276517 = 51847) (by norm_num)
theorem B243805 : Blo 167798 243805 := bbase (se 3 (by rfl) ⟨45713, by rfl⟩ : syracuseStep 243805 = 91427) (by norm_num)
theorem B407693 : Blo 167798 407693 := bbase (se 3 (by rfl) ⟨76442, by rfl⟩ : syracuseStep 407693 = 152885) (by norm_num)
theorem B571589 : Blo 167798 571589 := bbase (se 4 (by rfl) ⟨53586, by rfl⟩ : syracuseStep 571589 = 107173) (by norm_num)
theorem B1095893 : Blo 167798 1095893 := bbase (se 7 (by rfl) ⟨12842, by rfl⟩ : syracuseStep 1095893 = 25685) (by norm_num)
theorem B276725 : Blo 167798 276725 := bbase (se 5 (by rfl) ⟨12971, by rfl⟩ : syracuseStep 276725 = 25943) (by norm_num)
theorem B309541 : Blo 167798 309541 := bbase (se 4 (by rfl) ⟨29019, by rfl⟩ : syracuseStep 309541 = 58039) (by norm_num)
theorem B637253 : Blo 167798 637253 := bbase (se 4 (by rfl) ⟨59742, by rfl⟩ : syracuseStep 637253 = 119485) (by norm_num)
theorem B244181 : Blo 167798 244181 := bbase (se 7 (by rfl) ⟨2861, by rfl⟩ : syracuseStep 244181 = 5723) (by norm_num)
theorem B637541 : Blo 167798 637541 := bbase (se 4 (by rfl) ⟨59769, by rfl⟩ : syracuseStep 637541 = 119539) (by norm_num)
theorem B572021 : Blo 167798 572021 := bbase (se 5 (by rfl) ⟨26813, by rfl⟩ : syracuseStep 572021 = 53627) (by norm_num)
theorem B408269 : Blo 167798 408269 := bbase (se 3 (by rfl) ⟨76550, by rfl⟩ : syracuseStep 408269 = 153101) (by norm_num)
theorem B637733 : Blo 167798 637733 := bbase (se 4 (by rfl) ⟨59787, by rfl⟩ : syracuseStep 637733 = 119575) (by norm_num)
theorem B277453 : Blo 167798 277453 := bbase (se 3 (by rfl) ⟨52022, by rfl⟩ : syracuseStep 277453 = 104045) (by norm_num)
theorem B572453 : Blo 167798 572453 := bbase (se 4 (by rfl) ⟨53667, by rfl⟩ : syracuseStep 572453 = 107335) (by norm_num)
theorem B179317 : Blo 167798 179317 := bbase (se 5 (by rfl) ⟨8405, by rfl⟩ : syracuseStep 179317 = 16811) (by norm_num)
theorem B1719413 : Blo 167798 1719413 := bbase (se 5 (by rfl) ⟨80597, by rfl⟩ : syracuseStep 1719413 = 161195) (by norm_num)
theorem B539797 : Blo 167798 539797 := bbase (se 6 (by rfl) ⟨12651, by rfl⟩ : syracuseStep 539797 = 25303) (by norm_num)
theorem B867509 : Blo 167798 867509 := bbase (se 5 (by rfl) ⟨40664, by rfl⟩ : syracuseStep 867509 = 81329) (by norm_num)
theorem B343261 : Blo 167798 343261 := bbase (se 3 (by rfl) ⟨64361, by rfl⟩ : syracuseStep 343261 = 128723) (by norm_num)
theorem B179501 : Blo 167798 179501 := bbase (se 3 (by rfl) ⟨33656, by rfl⟩ : syracuseStep 179501 = 67313) (by norm_num)
theorem B212377 : Blo 167798 212377 := bbase (se 2 (by rfl) ⟨79641, by rfl⟩ : syracuseStep 212377 = 159283) (by norm_num)
theorem B572885 : Blo 167798 572885 := bbase (se 7 (by rfl) ⟨6713, by rfl⟩ : syracuseStep 572885 = 13427) (by norm_num)
theorem B212473 : Blo 167798 212473 := bbase (se 2 (by rfl) ⟨79677, by rfl⟩ : syracuseStep 212473 = 159355) (by norm_num)
theorem B442013 : Blo 167798 442013 := bbase (se 3 (by rfl) ⟨82877, by rfl⟩ : syracuseStep 442013 = 165755) (by norm_num)
theorem B212645 : Blo 167798 212645 := bbase (se 4 (by rfl) ⟨19935, by rfl⟩ : syracuseStep 212645 = 39871) (by norm_num)
theorem B212701 : Blo 167798 212701 := bbase (se 3 (by rfl) ⟨39881, by rfl⟩ : syracuseStep 212701 = 79763) (by norm_num)
theorem B343781 : Blo 167798 343781 := bbase (se 4 (by rfl) ⟨32229, by rfl⟩ : syracuseStep 343781 = 64459) (by norm_num)
theorem B1457909 : Blo 167798 1457909 := bbase (se 5 (by rfl) ⟨68339, by rfl⟩ : syracuseStep 1457909 = 136679) (by norm_num)
theorem B638725 : Blo 167798 638725 := bbase (se 4 (by rfl) ⟨59880, by rfl⟩ : syracuseStep 638725 = 119761) (by norm_num)
theorem B606005 : Blo 167798 606005 := bbase (se 5 (by rfl) ⟨28406, by rfl⟩ : syracuseStep 606005 = 56813) (by norm_num)
theorem B212797 : Blo 167798 212797 := bbase (se 3 (by rfl) ⟨39899, by rfl⟩ : syracuseStep 212797 = 79799) (by norm_num)
theorem B573317 : Blo 167798 573317 := bbase (se 4 (by rfl) ⟨53748, by rfl⟩ : syracuseStep 573317 = 107497) (by norm_num)
theorem B212969 : Blo 167798 212969 := bbase (se 2 (by rfl) ⟨79863, by rfl⟩ : syracuseStep 212969 = 159727) (by norm_num)
theorem B180253 : Blo 167798 180253 := bbase (se 3 (by rfl) ⟨33797, by rfl⟩ : syracuseStep 180253 = 67595) (by norm_num)
theorem B213025 : Blo 167798 213025 := bbase (se 2 (by rfl) ⟨79884, by rfl⟩ : syracuseStep 213025 = 159769) (by norm_num)
theorem B639029 : Blo 167798 639029 := bbase (se 5 (by rfl) ⟨29954, by rfl⟩ : syracuseStep 639029 = 59909) (by norm_num)
theorem B180325 : Blo 167798 180325 := bbase (se 4 (by rfl) ⟨16905, by rfl⟩ : syracuseStep 180325 = 33811) (by norm_num)
theorem B213121 : Blo 167798 213121 := bbase (se 2 (by rfl) ⟨79920, by rfl⟩ : syracuseStep 213121 = 159841) (by norm_num)
theorem B606437 : Blo 167798 606437 := bbase (se 4 (by rfl) ⟨56853, by rfl⟩ : syracuseStep 606437 = 113707) (by norm_num)
theorem B1294613 : Blo 167798 1294613 := bbase (se 6 (by rfl) ⟨30342, by rfl⟩ : syracuseStep 1294613 = 60685) (by norm_num)
theorem B180505 : Blo 167798 180505 := bbase (se 2 (by rfl) ⟨67689, by rfl⟩ : syracuseStep 180505 = 135379) (by norm_num)
theorem B213293 : Blo 167798 213293 := bbase (se 3 (by rfl) ⟨39992, by rfl⟩ : syracuseStep 213293 = 79985) (by norm_num)
theorem B573749 : Blo 167798 573749 := bbase (se 5 (by rfl) ⟨26894, by rfl⟩ : syracuseStep 573749 = 53789) (by norm_num)
theorem B1917269 : Blo 167798 1917269 := bbase (se 10 (by rfl) ⟨2808, by rfl⟩ : syracuseStep 1917269 = 5617) (by norm_num)
theorem B213349 : Blo 167798 213349 := bbase (se 4 (by rfl) ⟨20001, by rfl⟩ : syracuseStep 213349 = 40003) (by norm_num)
theorem B1622389 : Blo 167798 1622389 := bbase (se 5 (by rfl) ⟨76049, by rfl⟩ : syracuseStep 1622389 = 152099) (by norm_num)
theorem B213445 : Blo 167798 213445 := bbase (se 4 (by rfl) ⟨20010, by rfl⟩ : syracuseStep 213445 = 40021) (by norm_num)
theorem B868805 : Blo 167798 868805 := bbase (se 4 (by rfl) ⟨81450, by rfl⟩ : syracuseStep 868805 = 162901) (by norm_num)
theorem B213617 : Blo 167798 213617 := bbase (se 2 (by rfl) ⟨80106, by rfl⟩ : syracuseStep 213617 = 160213) (by norm_num)
theorem B213673 : Blo 167798 213673 := bbase (se 2 (by rfl) ⟨80127, by rfl⟩ : syracuseStep 213673 = 160255) (by norm_num)
theorem B377549 : Blo 167798 377549 := bbase (se 3 (by rfl) ⟨70790, by rfl⟩ : syracuseStep 377549 = 141581) (by norm_num)
theorem B180949 : Blo 167798 180949 := bbase (se 7 (by rfl) ⟨2120, by rfl⟩ : syracuseStep 180949 = 4241) (by norm_num)
theorem B574181 : Blo 167798 574181 := bbase (se 4 (by rfl) ⟨53829, by rfl⟩ : syracuseStep 574181 = 107659) (by norm_num)
theorem B213769 : Blo 167798 213769 := bbase (se 2 (by rfl) ⟨80163, by rfl⟩ : syracuseStep 213769 = 160327) (by norm_num)
theorem B377621 : Blo 167798 377621 := bbase (se 6 (by rfl) ⟨8850, by rfl⟩ : syracuseStep 377621 = 17701) (by norm_num)
theorem B181073 : Blo 167798 181073 := bbase (se 2 (by rfl) ⟨67902, by rfl⟩ : syracuseStep 181073 = 135805) (by norm_num)
theorem B1295189 : Blo 167798 1295189 := bbase (se 9 (by rfl) ⟨3794, by rfl⟩ : syracuseStep 1295189 = 7589) (by norm_num)
theorem B377693 : Blo 167798 377693 := bbase (se 3 (by rfl) ⟨70817, by rfl⟩ : syracuseStep 377693 = 141635) (by norm_num)
theorem B377765 : Blo 167798 377765 := bbase (se 4 (by rfl) ⟨35415, by rfl⟩ : syracuseStep 377765 = 70831) (by norm_num)
theorem B213941 : Blo 167798 213941 := bbase (se 5 (by rfl) ⟨10028, by rfl⟩ : syracuseStep 213941 = 20057) (by norm_num)
theorem B377837 : Blo 167798 377837 := bbase (se 3 (by rfl) ⟨70844, by rfl⟩ : syracuseStep 377837 = 141689) (by norm_num)
theorem B213997 : Blo 167798 213997 := bbase (se 3 (by rfl) ⟨40124, by rfl⟩ : syracuseStep 213997 = 80249) (by norm_num)
theorem B312365 : Blo 167798 312365 := bbase (se 3 (by rfl) ⟨58568, by rfl⟩ : syracuseStep 312365 = 117137) (by norm_num)
theorem B574517 : Blo 167798 574517 := bbase (se 5 (by rfl) ⟨26930, by rfl⟩ : syracuseStep 574517 = 53861) (by norm_num)
theorem B377909 : Blo 167798 377909 := bbase (se 5 (by rfl) ⟨17714, by rfl⟩ : syracuseStep 377909 = 35429) (by norm_num)
theorem B214093 : Blo 167798 214093 := bbase (se 3 (by rfl) ⟨40142, by rfl⟩ : syracuseStep 214093 = 80285) (by norm_num)
theorem B181325 : Blo 167798 181325 := bbase (se 3 (by rfl) ⟨33998, by rfl⟩ : syracuseStep 181325 = 67997) (by norm_num)
theorem B377981 : Blo 167798 377981 := bbase (se 3 (by rfl) ⟨70871, by rfl⟩ : syracuseStep 377981 = 141743) (by norm_num)
theorem B574613 : Blo 167798 574613 := bbase (se 6 (by rfl) ⟨13467, by rfl⟩ : syracuseStep 574613 = 26935) (by norm_num)
theorem B378053 : Blo 167798 378053 := bbase (se 4 (by rfl) ⟨35442, by rfl⟩ : syracuseStep 378053 = 70885) (by norm_num)
theorem B410845 : Blo 167798 410845 := bbase (se 3 (by rfl) ⟨77033, by rfl⟩ : syracuseStep 410845 = 154067) (by norm_num)
theorem B214265 : Blo 167798 214265 := bbase (se 2 (by rfl) ⟨80349, by rfl⟩ : syracuseStep 214265 = 160699) (by norm_num)
theorem B378125 : Blo 167798 378125 := bbase (se 3 (by rfl) ⟨70898, by rfl⟩ : syracuseStep 378125 = 141797) (by norm_num)
theorem B214321 : Blo 167798 214321 := bbase (se 2 (by rfl) ⟨80370, by rfl⟩ : syracuseStep 214321 = 160741) (by norm_num)
theorem B378197 : Blo 167798 378197 := bbase (se 12 (by rfl) ⟨138, by rfl⟩ : syracuseStep 378197 = 277) (by norm_num)
theorem B968021 : Blo 167798 968021 := bbase (se 12 (by rfl) ⟨354, by rfl⟩ : syracuseStep 968021 = 709) (by norm_num)
theorem B214417 : Blo 167798 214417 := bbase (se 2 (by rfl) ⟨80406, by rfl⟩ : syracuseStep 214417 = 160813) (by norm_num)
theorem B378269 : Blo 167798 378269 := bbase (se 3 (by rfl) ⟨70925, by rfl⟩ : syracuseStep 378269 = 141851) (by norm_num)
theorem B378341 : Blo 167798 378341 := bbase (se 4 (by rfl) ⟨35469, by rfl⟩ : syracuseStep 378341 = 70939) (by norm_num)
theorem B181769 : Blo 167798 181769 := bbase (se 2 (by rfl) ⟨68163, by rfl⟩ : syracuseStep 181769 = 136327) (by norm_num)
theorem B345613 : Blo 167798 345613 := bbase (se 3 (by rfl) ⟨64802, by rfl⟩ : syracuseStep 345613 = 129605) (by norm_num)
theorem B378413 : Blo 167798 378413 := bbase (se 3 (by rfl) ⟨70952, by rfl⟩ : syracuseStep 378413 = 141905) (by norm_num)
theorem B214589 : Blo 167798 214589 := bbase (se 3 (by rfl) ⟨40235, by rfl⟩ : syracuseStep 214589 = 80471) (by norm_num)
theorem B575045 : Blo 167798 575045 := bbase (se 4 (by rfl) ⟨53910, by rfl⟩ : syracuseStep 575045 = 107821) (by norm_num)
theorem B4343381 : Blo 167798 4343381 := bbase (se 8 (by rfl) ⟨25449, by rfl⟩ : syracuseStep 4343381 = 50899) (by norm_num)
theorem B378485 : Blo 167798 378485 := bbase (se 5 (by rfl) ⟨17741, by rfl⟩ : syracuseStep 378485 = 35483) (by norm_num)
theorem B214645 : Blo 167798 214645 := bbase (se 5 (by rfl) ⟨10061, by rfl⟩ : syracuseStep 214645 = 20123) (by norm_num)
theorem B378557 : Blo 167798 378557 := bbase (se 3 (by rfl) ⟨70979, by rfl⟩ : syracuseStep 378557 = 141959) (by norm_num)
theorem B214741 : Blo 167798 214741 := bbase (se 7 (by rfl) ⟨2516, by rfl⟩ : syracuseStep 214741 = 5033) (by norm_num)
theorem B182017 : Blo 167798 182017 := bbase (se 2 (by rfl) ⟨68256, by rfl⟩ : syracuseStep 182017 = 136513) (by norm_num)
theorem B378629 : Blo 167798 378629 := bbase (se 4 (by rfl) ⟨35496, by rfl⟩ : syracuseStep 378629 = 70993) (by norm_num)
theorem B378701 : Blo 167798 378701 := bbase (se 3 (by rfl) ⟨71006, by rfl⟩ : syracuseStep 378701 = 142013) (by norm_num)
theorem B214913 : Blo 167798 214913 := bbase (se 2 (by rfl) ⟨80592, by rfl⟩ : syracuseStep 214913 = 161185) (by norm_num)
theorem B378773 : Blo 167798 378773 := bbase (se 6 (by rfl) ⟨8877, by rfl⟩ : syracuseStep 378773 = 17755) (by norm_num)
theorem B214969 : Blo 167798 214969 := bbase (se 2 (by rfl) ⟨80613, by rfl⟩ : syracuseStep 214969 = 161227) (by norm_num)
theorem B378845 : Blo 167798 378845 := bbase (se 3 (by rfl) ⟨71033, by rfl⟩ : syracuseStep 378845 = 142067) (by norm_num)
theorem B575477 : Blo 167798 575477 := bbase (se 5 (by rfl) ⟨26975, by rfl⟩ : syracuseStep 575477 = 53951) (by norm_num)
theorem B215065 : Blo 167798 215065 := bbase (se 2 (by rfl) ⟨80649, by rfl⟩ : syracuseStep 215065 = 161299) (by norm_num)
theorem B378917 : Blo 167798 378917 := bbase (se 4 (by rfl) ⟨35523, by rfl⟩ : syracuseStep 378917 = 71047) (by norm_num)
theorem B542821 : Blo 167798 542821 := bbase (se 4 (by rfl) ⟨50889, by rfl⟩ : syracuseStep 542821 = 101779) (by norm_num)
theorem B378989 : Blo 167798 378989 := bbase (se 3 (by rfl) ⟨71060, by rfl⟩ : syracuseStep 378989 = 142121) (by norm_num)
theorem B641141 : Blo 167798 641141 := bbase (se 5 (by rfl) ⟨30053, by rfl⟩ : syracuseStep 641141 = 60107) (by norm_num)
theorem B379061 : Blo 167798 379061 := bbase (se 5 (by rfl) ⟨17768, by rfl⟩ : syracuseStep 379061 = 35537) (by norm_num)
theorem B182461 : Blo 167798 182461 := bbase (se 3 (by rfl) ⟨34211, by rfl⟩ : syracuseStep 182461 = 68423) (by norm_num)
theorem B215237 : Blo 167798 215237 := bbase (se 4 (by rfl) ⟨20178, by rfl⟩ : syracuseStep 215237 = 40357) (by norm_num)
theorem B182521 : Blo 167798 182521 := bbase (se 2 (by rfl) ⟨68445, by rfl⟩ : syracuseStep 182521 = 136891) (by norm_num)
theorem B379133 : Blo 167798 379133 := bbase (se 3 (by rfl) ⟨71087, by rfl⟩ : syracuseStep 379133 = 142175) (by norm_num)
theorem B215293 : Blo 167798 215293 := bbase (se 3 (by rfl) ⟨40367, by rfl⟩ : syracuseStep 215293 = 80735) (by norm_num)
theorem B379205 : Blo 167798 379205 := bbase (se 4 (by rfl) ⟨35550, by rfl⟩ : syracuseStep 379205 = 71101) (by norm_num)
theorem B215389 : Blo 167798 215389 := bbase (se 3 (by rfl) ⟨40385, by rfl⟩ : syracuseStep 215389 = 80771) (by norm_num)
theorem B412037 : Blo 167798 412037 := bbase (se 4 (by rfl) ⟨38628, by rfl⟩ : syracuseStep 412037 = 77257) (by norm_num)
theorem B379277 : Blo 167798 379277 := bbase (se 3 (by rfl) ⟨71114, by rfl⟩ : syracuseStep 379277 = 142229) (by norm_num)
theorem B641429 : Blo 167798 641429 := bbase (se 6 (by rfl) ⟨15033, by rfl⟩ : syracuseStep 641429 = 30067) (by norm_num)
theorem B575909 : Blo 167798 575909 := bbase (se 4 (by rfl) ⟨53991, by rfl⟩ : syracuseStep 575909 = 107983) (by norm_num)
theorem B379349 : Blo 167798 379349 := bbase (se 7 (by rfl) ⟨4445, by rfl⟩ : syracuseStep 379349 = 8891) (by norm_num)
theorem B969205 : Blo 167798 969205 := bbase (se 5 (by rfl) ⟨45431, by rfl⟩ : syracuseStep 969205 = 90863) (by norm_num)
theorem B215561 : Blo 167798 215561 := bbase (se 2 (by rfl) ⟨80835, by rfl⟩ : syracuseStep 215561 = 161671) (by norm_num)
theorem B379421 : Blo 167798 379421 := bbase (se 3 (by rfl) ⟨71141, by rfl⟩ : syracuseStep 379421 = 142283) (by norm_num)
theorem B182837 : Blo 167798 182837 := bbase (se 5 (by rfl) ⟨8570, by rfl⟩ : syracuseStep 182837 = 17141) (by norm_num)
theorem B215617 : Blo 167798 215617 := bbase (se 2 (by rfl) ⟨80856, by rfl⟩ : syracuseStep 215617 = 161713) (by norm_num)
theorem B412229 : Blo 167798 412229 := bbase (se 4 (by rfl) ⟨38646, by rfl⟩ : syracuseStep 412229 = 77293) (by norm_num)
theorem B379493 : Blo 167798 379493 := bbase (se 4 (by rfl) ⟨35577, by rfl⟩ : syracuseStep 379493 = 71155) (by norm_num)
theorem B215713 : Blo 167798 215713 := bbase (se 2 (by rfl) ⟨80892, by rfl⟩ : syracuseStep 215713 = 161785) (by norm_num)
theorem B379565 : Blo 167798 379565 := bbase (se 3 (by rfl) ⟨71168, by rfl⟩ : syracuseStep 379565 = 142337) (by norm_num)
theorem B379637 : Blo 167798 379637 := bbase (se 5 (by rfl) ⟨17795, by rfl⟩ : syracuseStep 379637 = 35591) (by norm_num)
theorem B379709 : Blo 167798 379709 := bbase (se 3 (by rfl) ⟨71195, by rfl⟩ : syracuseStep 379709 = 142391) (by norm_num)
theorem B215885 : Blo 167798 215885 := bbase (se 3 (by rfl) ⟨40478, by rfl⟩ : syracuseStep 215885 = 80957) (by norm_num)
theorem B576341 : Blo 167798 576341 := bbase (se 9 (by rfl) ⟨1688, by rfl⟩ : syracuseStep 576341 = 3377) (by norm_num)
theorem B379781 : Blo 167798 379781 := bbase (se 4 (by rfl) ⟨35604, by rfl⟩ : syracuseStep 379781 = 71209) (by norm_num)
theorem B215941 : Blo 167798 215941 := bbase (se 4 (by rfl) ⟨20244, by rfl⟩ : syracuseStep 215941 = 40489) (by norm_num)
theorem B478133 : Blo 167798 478133 := bbase (se 5 (by rfl) ⟨22412, by rfl⟩ : syracuseStep 478133 = 44825) (by norm_num)
theorem B379853 : Blo 167798 379853 := bbase (se 3 (by rfl) ⟨71222, by rfl⟩ : syracuseStep 379853 = 142445) (by norm_num)
theorem B216037 : Blo 167798 216037 := bbase (se 4 (by rfl) ⟨20253, by rfl⟩ : syracuseStep 216037 = 40507) (by norm_num)
theorem B183281 : Blo 167798 183281 := bbase (se 2 (by rfl) ⟨68730, by rfl⟩ : syracuseStep 183281 = 137461) (by norm_num)
theorem B379925 : Blo 167798 379925 := bbase (se 6 (by rfl) ⟨8904, by rfl⟩ : syracuseStep 379925 = 17809) (by norm_num)
theorem B183341 : Blo 167798 183341 := bbase (se 3 (by rfl) ⟨34376, by rfl⟩ : syracuseStep 183341 = 68753) (by norm_num)
theorem B379997 : Blo 167798 379997 := bbase (se 3 (by rfl) ⟨71249, by rfl⟩ : syracuseStep 379997 = 142499) (by norm_num)
theorem B216209 : Blo 167798 216209 := bbase (se 2 (by rfl) ⟨81078, by rfl⟩ : syracuseStep 216209 = 162157) (by norm_num)
theorem B380069 : Blo 167798 380069 := bbase (se 4 (by rfl) ⟨35631, by rfl⟩ : syracuseStep 380069 = 71263) (by norm_num)
theorem B216265 : Blo 167798 216265 := bbase (se 2 (by rfl) ⟨81099, by rfl⟩ : syracuseStep 216265 = 162199) (by norm_num)
theorem B380141 : Blo 167798 380141 := bbase (se 3 (by rfl) ⟨71276, by rfl⟩ : syracuseStep 380141 = 142553) (by norm_num)
theorem B576773 : Blo 167798 576773 := bbase (se 4 (by rfl) ⟨54072, by rfl⟩ : syracuseStep 576773 = 108145) (by norm_num)
theorem B347413 : Blo 167798 347413 := bbase (se 6 (by rfl) ⟨8142, by rfl⟩ : syracuseStep 347413 = 16285) (by norm_num)
theorem B216361 : Blo 167798 216361 := bbase (se 2 (by rfl) ⟨81135, by rfl⟩ : syracuseStep 216361 = 162271) (by norm_num)
theorem B380213 : Blo 167798 380213 := bbase (se 5 (by rfl) ⟨17822, by rfl⟩ : syracuseStep 380213 = 35645) (by norm_num)
theorem B380285 : Blo 167798 380285 := bbase (se 3 (by rfl) ⟨71303, by rfl⟩ : syracuseStep 380285 = 142607) (by norm_num)
theorem B380357 : Blo 167798 380357 := bbase (se 4 (by rfl) ⟨35658, by rfl⟩ : syracuseStep 380357 = 71317) (by norm_num)
theorem B216533 : Blo 167798 216533 := bbase (se 7 (by rfl) ⟨2537, by rfl⟩ : syracuseStep 216533 = 5075) (by norm_num)
theorem B609781 : Blo 167798 609781 := bbase (se 5 (by rfl) ⟨28583, by rfl⟩ : syracuseStep 609781 = 57167) (by norm_num)
theorem B380429 : Blo 167798 380429 := bbase (se 3 (by rfl) ⟨71330, by rfl⟩ : syracuseStep 380429 = 142661) (by norm_num)
theorem B216589 : Blo 167798 216589 := bbase (se 3 (by rfl) ⟨40610, by rfl⟩ : syracuseStep 216589 = 81221) (by norm_num)
theorem B642613 : Blo 167798 642613 := bbase (se 5 (by rfl) ⟨30122, by rfl⟩ : syracuseStep 642613 = 60245) (by norm_num)
theorem B380501 : Blo 167798 380501 := bbase (se 8 (by rfl) ⟨2229, by rfl⟩ : syracuseStep 380501 = 4459) (by norm_num)
theorem B216685 : Blo 167798 216685 := bbase (se 3 (by rfl) ⟨40628, by rfl⟩ : syracuseStep 216685 = 81257) (by norm_num)
theorem B380573 : Blo 167798 380573 := bbase (se 3 (by rfl) ⟨71357, by rfl⟩ : syracuseStep 380573 = 142715) (by norm_num)
theorem B478885 : Blo 167798 478885 := bbase (se 4 (by rfl) ⟨44895, by rfl⟩ : syracuseStep 478885 = 89791) (by norm_num)
theorem B577205 : Blo 167798 577205 := bbase (se 5 (by rfl) ⟨27056, by rfl⟩ : syracuseStep 577205 = 54113) (by norm_num)
theorem B380645 : Blo 167798 380645 := bbase (se 4 (by rfl) ⟨35685, by rfl⟩ : syracuseStep 380645 = 71371) (by norm_num)
theorem B216857 : Blo 167798 216857 := bbase (se 2 (by rfl) ⟨81321, by rfl⟩ : syracuseStep 216857 = 162643) (by norm_num)
theorem B380717 : Blo 167798 380717 := bbase (se 3 (by rfl) ⟨71384, by rfl⟩ : syracuseStep 380717 = 142769) (by norm_num)
theorem B216913 : Blo 167798 216913 := bbase (se 2 (by rfl) ⟨81342, by rfl⟩ : syracuseStep 216913 = 162685) (by norm_num)
theorem B642917 : Blo 167798 642917 := bbase (se 4 (by rfl) ⟨60273, by rfl⟩ : syracuseStep 642917 = 120547) (by norm_num)
theorem B380789 : Blo 167798 380789 := bbase (se 5 (by rfl) ⟨17849, by rfl⟩ : syracuseStep 380789 = 35699) (by norm_num)
theorem B217009 : Blo 167798 217009 := bbase (se 2 (by rfl) ⟨81378, by rfl⟩ : syracuseStep 217009 = 162757) (by norm_num)
theorem B380861 : Blo 167798 380861 := bbase (se 3 (by rfl) ⟨71411, by rfl⟩ : syracuseStep 380861 = 142823) (by norm_num)
theorem B380933 : Blo 167798 380933 := bbase (se 4 (by rfl) ⟨35712, by rfl⟩ : syracuseStep 380933 = 71425) (by norm_num)
theorem B381005 : Blo 167798 381005 := bbase (se 3 (by rfl) ⟨71438, by rfl⟩ : syracuseStep 381005 = 142877) (by norm_num)
theorem B217181 : Blo 167798 217181 := bbase (se 3 (by rfl) ⟨40721, by rfl⟩ : syracuseStep 217181 = 81443) (by norm_num)
theorem B577637 : Blo 167798 577637 := bbase (se 4 (by rfl) ⟨54153, by rfl⟩ : syracuseStep 577637 = 108307) (by norm_num)
theorem B381077 : Blo 167798 381077 := bbase (se 6 (by rfl) ⟨8931, by rfl⟩ : syracuseStep 381077 = 17863) (by norm_num)
theorem B2445461 : Blo 167798 2445461 := bbase (se 6 (by rfl) ⟨57315, by rfl⟩ : syracuseStep 2445461 = 114631) (by norm_num)
theorem B217237 : Blo 167798 217237 := bbase (se 6 (by rfl) ⟨5091, by rfl⟩ : syracuseStep 217237 = 10183) (by norm_num)
theorem B381149 : Blo 167798 381149 := bbase (se 3 (by rfl) ⟨71465, by rfl⟩ : syracuseStep 381149 = 142931) (by norm_num)
theorem B217333 : Blo 167798 217333 := bbase (se 5 (by rfl) ⟨10187, by rfl⟩ : syracuseStep 217333 = 20375) (by norm_num)
theorem B381221 : Blo 167798 381221 := bbase (se 4 (by rfl) ⟨35739, by rfl⟩ : syracuseStep 381221 = 71479) (by norm_num)
theorem B381293 : Blo 167798 381293 := bbase (se 3 (by rfl) ⟨71492, by rfl⟩ : syracuseStep 381293 = 142985) (by norm_num)
theorem B381365 : Blo 167798 381365 := bbase (se 5 (by rfl) ⟨17876, by rfl⟩ : syracuseStep 381365 = 35753) (by norm_num)
theorem B971189 : Blo 167798 971189 := bbase (se 5 (by rfl) ⟨45524, by rfl⟩ : syracuseStep 971189 = 91049) (by norm_num)
theorem B1626581 : Blo 167798 1626581 := bbase (se 7 (by rfl) ⟨19061, by rfl⟩ : syracuseStep 1626581 = 38123) (by norm_num)
theorem B381437 : Blo 167798 381437 := bbase (se 3 (by rfl) ⟨71519, by rfl⟩ : syracuseStep 381437 = 143039) (by norm_num)
theorem B578069 : Blo 167798 578069 := bbase (se 6 (by rfl) ⟨13548, by rfl⟩ : syracuseStep 578069 = 27097) (by norm_num)
theorem B283189 : Blo 167798 283189 := bbase (se 5 (by rfl) ⟨13274, by rfl⟩ : syracuseStep 283189 = 26549) (by norm_num)
theorem B381509 : Blo 167798 381509 := bbase (se 4 (by rfl) ⟨35766, by rfl⟩ : syracuseStep 381509 = 71533) (by norm_num)
theorem B283277 : Blo 167798 283277 := bbase (se 3 (by rfl) ⟨53114, by rfl⟩ : syracuseStep 283277 = 106229) (by norm_num)
theorem B381581 : Blo 167798 381581 := bbase (se 3 (by rfl) ⟨71546, by rfl⟩ : syracuseStep 381581 = 143093) (by norm_num)
theorem B381653 : Blo 167798 381653 := bbase (se 7 (by rfl) ⟨4472, by rfl⟩ : syracuseStep 381653 = 8945) (by norm_num)
theorem B283405 : Blo 167798 283405 := bbase (se 3 (by rfl) ⟨53138, by rfl⟩ : syracuseStep 283405 = 106277) (by norm_num)
theorem B381725 : Blo 167798 381725 := bbase (se 3 (by rfl) ⟨71573, by rfl⟩ : syracuseStep 381725 = 143147) (by norm_num)
theorem B283493 : Blo 167798 283493 := bbase (se 4 (by rfl) ⟨26577, by rfl⟩ : syracuseStep 283493 = 53155) (by norm_num)
theorem B381797 : Blo 167798 381797 := bbase (se 4 (by rfl) ⟨35793, by rfl⟩ : syracuseStep 381797 = 71587) (by norm_num)
theorem B381869 : Blo 167798 381869 := bbase (se 3 (by rfl) ⟨71600, by rfl⟩ : syracuseStep 381869 = 143201) (by norm_num)
theorem B545717 : Blo 167798 545717 := bbase (se 5 (by rfl) ⟨25580, by rfl⟩ : syracuseStep 545717 = 51161) (by norm_num)
theorem B578501 : Blo 167798 578501 := bbase (se 4 (by rfl) ⟨54234, by rfl⟩ : syracuseStep 578501 = 108469) (by norm_num)
theorem B283621 : Blo 167798 283621 := bbase (se 4 (by rfl) ⟨26589, by rfl⟩ : syracuseStep 283621 = 53179) (by norm_num)
theorem B381941 : Blo 167798 381941 := bbase (se 5 (by rfl) ⟨17903, by rfl⟩ : syracuseStep 381941 = 35807) (by norm_num)
theorem B283709 : Blo 167798 283709 := bbase (se 3 (by rfl) ⟨53195, by rfl⟩ : syracuseStep 283709 = 106391) (by norm_num)
theorem B382013 : Blo 167798 382013 := bbase (se 3 (by rfl) ⟨71627, by rfl⟩ : syracuseStep 382013 = 143255) (by norm_num)
theorem B185437 : Blo 167798 185437 := bbase (se 3 (by rfl) ⟨34769, by rfl⟩ : syracuseStep 185437 = 69539) (by norm_num)
theorem B382085 : Blo 167798 382085 := bbase (se 4 (by rfl) ⟨35820, by rfl⟩ : syracuseStep 382085 = 71641) (by norm_num)
theorem B283837 : Blo 167798 283837 := bbase (se 3 (by rfl) ⟨53219, by rfl⟩ : syracuseStep 283837 = 106439) (by norm_num)
theorem B382157 : Blo 167798 382157 := bbase (se 3 (by rfl) ⟨71654, by rfl⟩ : syracuseStep 382157 = 143309) (by norm_num)
theorem B283925 : Blo 167798 283925 := bbase (se 6 (by rfl) ⟨6654, by rfl⟩ : syracuseStep 283925 = 13309) (by norm_num)
theorem B382229 : Blo 167798 382229 := bbase (se 6 (by rfl) ⟨8958, by rfl⟩ : syracuseStep 382229 = 17917) (by norm_num)
theorem B382301 : Blo 167798 382301 := bbase (se 3 (by rfl) ⟨71681, by rfl⟩ : syracuseStep 382301 = 143363) (by norm_num)
theorem B578933 : Blo 167798 578933 := bbase (se 5 (by rfl) ⟨27137, by rfl⟩ : syracuseStep 578933 = 54275) (by norm_num)
theorem B284053 : Blo 167798 284053 := bbase (se 6 (by rfl) ⟨6657, by rfl⟩ : syracuseStep 284053 = 13315) (by norm_num)
theorem B382373 : Blo 167798 382373 := bbase (se 4 (by rfl) ⟨35847, by rfl⟩ : syracuseStep 382373 = 71695) (by norm_num)
theorem B284141 : Blo 167798 284141 := bbase (se 3 (by rfl) ⟨53276, by rfl⟩ : syracuseStep 284141 = 106553) (by norm_num)
theorem B382445 : Blo 167798 382445 := bbase (se 3 (by rfl) ⟨71708, by rfl⟩ : syracuseStep 382445 = 143417) (by norm_num)
theorem B382517 : Blo 167798 382517 := bbase (se 5 (by rfl) ⟨17930, by rfl⟩ : syracuseStep 382517 = 35861) (by norm_num)
theorem B284269 : Blo 167798 284269 := bbase (se 3 (by rfl) ⟨53300, by rfl⟩ : syracuseStep 284269 = 106601) (by norm_num)
theorem B382589 : Blo 167798 382589 := bbase (se 3 (by rfl) ⟨71735, by rfl⟩ : syracuseStep 382589 = 143471) (by norm_num)
theorem B218801 : Blo 167798 218801 := bbase (se 2 (by rfl) ⟨82050, by rfl⟩ : syracuseStep 218801 = 164101) (by norm_num)
theorem B284357 : Blo 167798 284357 := bbase (se 4 (by rfl) ⟨26658, by rfl⟩ : syracuseStep 284357 = 53317) (by norm_num)
theorem B382661 : Blo 167798 382661 := bbase (se 4 (by rfl) ⟨35874, by rfl⟩ : syracuseStep 382661 = 71749) (by norm_num)
theorem B382733 : Blo 167798 382733 := bbase (se 3 (by rfl) ⟨71762, by rfl⟩ : syracuseStep 382733 = 143525) (by norm_num)
theorem B1365781 : Blo 167798 1365781 := bbase (se 6 (by rfl) ⟨32010, by rfl⟩ : syracuseStep 1365781 = 64021) (by norm_num)
theorem B579365 : Blo 167798 579365 := bbase (se 4 (by rfl) ⟨54315, by rfl⟩ : syracuseStep 579365 = 108631) (by norm_num)
theorem B251717 : Blo 167798 251717 := bbase (se 4 (by rfl) ⟨23598, by rfl⟩ : syracuseStep 251717 = 47197) (by norm_num)
theorem B284485 : Blo 167798 284485 := bbase (se 4 (by rfl) ⟨26670, by rfl⟩ : syracuseStep 284485 = 53341) (by norm_num)
theorem B382805 : Blo 167798 382805 := bbase (se 9 (by rfl) ⟨1121, by rfl⟩ : syracuseStep 382805 = 2243) (by norm_num)
theorem B251741 : Blo 167798 251741 := bbase (se 3 (by rfl) ⟨47201, by rfl⟩ : syracuseStep 251741 = 94403) (by norm_num)
theorem B251765 : Blo 167798 251765 := bbase (se 5 (by rfl) ⟨11801, by rfl⟩ : syracuseStep 251765 = 23603) (by norm_num)
theorem B251789 : Blo 167798 251789 := bbase (se 3 (by rfl) ⟨47210, by rfl⟩ : syracuseStep 251789 = 94421) (by norm_num)
theorem B284573 : Blo 167798 284573 := bbase (se 3 (by rfl) ⟨53357, by rfl⟩ : syracuseStep 284573 = 106715) (by norm_num)
theorem B382877 : Blo 167798 382877 := bbase (se 3 (by rfl) ⟨71789, by rfl⟩ : syracuseStep 382877 = 143579) (by norm_num)
theorem B251813 : Blo 167798 251813 := bbase (se 4 (by rfl) ⟨23607, by rfl⟩ : syracuseStep 251813 = 47215) (by norm_num)
theorem B645029 : Blo 167798 645029 := bbase (se 4 (by rfl) ⟨60471, by rfl⟩ : syracuseStep 645029 = 120943) (by norm_num)
theorem B251837 : Blo 167798 251837 := bbase (se 3 (by rfl) ⟨47219, by rfl⟩ : syracuseStep 251837 = 94439) (by norm_num)
theorem B251861 : Blo 167798 251861 := bbase (se 7 (by rfl) ⟨2951, by rfl⟩ : syracuseStep 251861 = 5903) (by norm_num)
theorem B382949 : Blo 167798 382949 := bbase (se 4 (by rfl) ⟨35901, by rfl⟩ : syracuseStep 382949 = 71803) (by norm_num)
theorem B251885 : Blo 167798 251885 := bbase (se 3 (by rfl) ⟨47228, by rfl⟩ : syracuseStep 251885 = 94457) (by norm_num)
theorem B251909 : Blo 167798 251909 := bbase (se 4 (by rfl) ⟨23616, by rfl⟩ : syracuseStep 251909 = 47233) (by norm_num)
theorem B251933 : Blo 167798 251933 := bbase (se 3 (by rfl) ⟨47237, by rfl⟩ : syracuseStep 251933 = 94475) (by norm_num)
theorem B284701 : Blo 167798 284701 := bbase (se 3 (by rfl) ⟨53381, by rfl⟩ : syracuseStep 284701 = 106763) (by norm_num)
theorem B383021 : Blo 167798 383021 := bbase (se 3 (by rfl) ⟨71816, by rfl⟩ : syracuseStep 383021 = 143633) (by norm_num)
theorem B251957 : Blo 167798 251957 := bbase (se 5 (by rfl) ⟨11810, by rfl⟩ : syracuseStep 251957 = 23621) (by norm_num)
theorem B251981 : Blo 167798 251981 := bbase (se 3 (by rfl) ⟨47246, by rfl⟩ : syracuseStep 251981 = 94493) (by norm_num)
theorem B415829 : Blo 167798 415829 := bbase (se 8 (by rfl) ⟨2436, by rfl⟩ : syracuseStep 415829 = 4873) (by norm_num)
theorem B252005 : Blo 167798 252005 := bbase (se 4 (by rfl) ⟨23625, by rfl⟩ : syracuseStep 252005 = 47251) (by norm_num)
theorem B284789 : Blo 167798 284789 := bbase (se 5 (by rfl) ⟨13349, by rfl⟩ : syracuseStep 284789 = 26699) (by norm_num)
theorem B383093 : Blo 167798 383093 := bbase (se 5 (by rfl) ⟨17957, by rfl⟩ : syracuseStep 383093 = 35915) (by norm_num)
theorem B252029 : Blo 167798 252029 := bbase (se 3 (by rfl) ⟨47255, by rfl⟩ : syracuseStep 252029 = 94511) (by norm_num)
theorem B252053 : Blo 167798 252053 := bbase (se 6 (by rfl) ⟨5907, by rfl⟩ : syracuseStep 252053 = 11815) (by norm_num)
theorem B252077 : Blo 167798 252077 := bbase (se 3 (by rfl) ⟨47264, by rfl⟩ : syracuseStep 252077 = 94529) (by norm_num)
theorem B383165 : Blo 167798 383165 := bbase (se 3 (by rfl) ⟨71843, by rfl⟩ : syracuseStep 383165 = 143687) (by norm_num)
theorem B252101 : Blo 167798 252101 := bbase (se 4 (by rfl) ⟨23634, by rfl⟩ : syracuseStep 252101 = 47269) (by norm_num)
theorem B645317 : Blo 167798 645317 := bbase (se 4 (by rfl) ⟨60498, by rfl⟩ : syracuseStep 645317 = 120997) (by norm_num)
theorem B547013 : Blo 167798 547013 := bbase (se 4 (by rfl) ⟨51282, by rfl⟩ : syracuseStep 547013 = 102565) (by norm_num)
theorem B579797 : Blo 167798 579797 := bbase (se 7 (by rfl) ⟨6794, by rfl⟩ : syracuseStep 579797 = 13589) (by norm_num)
theorem B252125 : Blo 167798 252125 := bbase (se 3 (by rfl) ⟨47273, by rfl⟩ : syracuseStep 252125 = 94547) (by norm_num)
theorem B252149 : Blo 167798 252149 := bbase (se 5 (by rfl) ⟨11819, by rfl⟩ : syracuseStep 252149 = 23639) (by norm_num)
theorem B284917 : Blo 167798 284917 := bbase (se 5 (by rfl) ⟨13355, by rfl⟩ : syracuseStep 284917 = 26711) (by norm_num)
theorem B383237 : Blo 167798 383237 := bbase (se 4 (by rfl) ⟨35928, by rfl⟩ : syracuseStep 383237 = 71857) (by norm_num)
theorem B252173 : Blo 167798 252173 := bbase (se 3 (by rfl) ⟨47282, by rfl⟩ : syracuseStep 252173 = 94565) (by norm_num)
theorem B252197 : Blo 167798 252197 := bbase (se 4 (by rfl) ⟨23643, by rfl⟩ : syracuseStep 252197 = 47287) (by norm_num)
theorem B252221 : Blo 167798 252221 := bbase (se 3 (by rfl) ⟨47291, by rfl⟩ : syracuseStep 252221 = 94583) (by norm_num)
theorem B285005 : Blo 167798 285005 := bbase (se 3 (by rfl) ⟨53438, by rfl⟩ : syracuseStep 285005 = 106877) (by norm_num)
theorem B383309 : Blo 167798 383309 := bbase (se 3 (by rfl) ⟨71870, by rfl⟩ : syracuseStep 383309 = 143741) (by norm_num)
theorem B252245 : Blo 167798 252245 := bbase (se 10 (by rfl) ⟨369, by rfl⟩ : syracuseStep 252245 = 739) (by norm_num)
theorem B252269 : Blo 167798 252269 := bbase (se 3 (by rfl) ⟨47300, by rfl⟩ : syracuseStep 252269 = 94601) (by norm_num)
theorem B252293 : Blo 167798 252293 := bbase (se 4 (by rfl) ⟨23652, by rfl⟩ : syracuseStep 252293 = 47305) (by norm_num)
theorem B383381 : Blo 167798 383381 := bbase (se 6 (by rfl) ⟨8985, by rfl⟩ : syracuseStep 383381 = 17971) (by norm_num)
theorem B252317 : Blo 167798 252317 := bbase (se 3 (by rfl) ⟨47309, by rfl⟩ : syracuseStep 252317 = 94619) (by norm_num)
theorem B252341 : Blo 167798 252341 := bbase (se 5 (by rfl) ⟨11828, by rfl⟩ : syracuseStep 252341 = 23657) (by norm_num)
theorem B481733 : Blo 167798 481733 := bbase (se 4 (by rfl) ⟨45162, by rfl⟩ : syracuseStep 481733 = 90325) (by norm_num)
theorem B252365 : Blo 167798 252365 := bbase (se 3 (by rfl) ⟨47318, by rfl⟩ : syracuseStep 252365 = 94637) (by norm_num)
theorem B285133 : Blo 167798 285133 := bbase (se 3 (by rfl) ⟨53462, by rfl⟩ : syracuseStep 285133 = 106925) (by norm_num)
theorem B383453 : Blo 167798 383453 := bbase (se 3 (by rfl) ⟨71897, by rfl⟩ : syracuseStep 383453 = 143795) (by norm_num)
theorem B252389 : Blo 167798 252389 := bbase (se 4 (by rfl) ⟨23661, by rfl⟩ : syracuseStep 252389 = 47323) (by norm_num)
theorem B186869 : Blo 167798 186869 := bbase (se 5 (by rfl) ⟨8759, by rfl⟩ : syracuseStep 186869 = 17519) (by norm_num)
theorem B252413 : Blo 167798 252413 := bbase (se 3 (by rfl) ⟨47327, by rfl⟩ : syracuseStep 252413 = 94655) (by norm_num)
theorem B252437 : Blo 167798 252437 := bbase (se 6 (by rfl) ⟨5916, by rfl⟩ : syracuseStep 252437 = 11833) (by norm_num)
theorem B383525 : Blo 167798 383525 := bbase (se 4 (by rfl) ⟨35955, by rfl⟩ : syracuseStep 383525 = 71911) (by norm_num)
theorem B285221 : Blo 167798 285221 := bbase (se 4 (by rfl) ⟨26739, by rfl⟩ : syracuseStep 285221 = 53479) (by norm_num)
theorem B252461 : Blo 167798 252461 := bbase (se 3 (by rfl) ⟨47336, by rfl⟩ : syracuseStep 252461 = 94673) (by norm_num)
theorem B252485 : Blo 167798 252485 := bbase (se 4 (by rfl) ⟨23670, by rfl⟩ : syracuseStep 252485 = 47341) (by norm_num)
theorem B973397 : Blo 167798 973397 := bbase (se 8 (by rfl) ⟨5703, by rfl⟩ : syracuseStep 973397 = 11407) (by norm_num)
theorem B252509 : Blo 167798 252509 := bbase (se 3 (by rfl) ⟨47345, by rfl⟩ : syracuseStep 252509 = 94691) (by norm_num)
theorem B383597 : Blo 167798 383597 := bbase (se 3 (by rfl) ⟨71924, by rfl⟩ : syracuseStep 383597 = 143849) (by norm_num)
theorem B252533 : Blo 167798 252533 := bbase (se 5 (by rfl) ⟨11837, by rfl⟩ : syracuseStep 252533 = 23675) (by norm_num)
theorem B252557 : Blo 167798 252557 := bbase (se 3 (by rfl) ⟨47354, by rfl⟩ : syracuseStep 252557 = 94709) (by norm_num)
theorem B252581 : Blo 167798 252581 := bbase (se 4 (by rfl) ⟨23679, by rfl⟩ : syracuseStep 252581 = 47359) (by norm_num)
theorem B285349 : Blo 167798 285349 := bbase (se 4 (by rfl) ⟨26751, by rfl⟩ : syracuseStep 285349 = 53503) (by norm_num)
theorem B383669 : Blo 167798 383669 := bbase (se 5 (by rfl) ⟨17984, by rfl⟩ : syracuseStep 383669 = 35969) (by norm_num)
theorem B252605 : Blo 167798 252605 := bbase (se 3 (by rfl) ⟨47363, by rfl⟩ : syracuseStep 252605 = 94727) (by norm_num)
theorem B252629 : Blo 167798 252629 := bbase (se 7 (by rfl) ⟨2960, by rfl⟩ : syracuseStep 252629 = 5921) (by norm_num)
theorem B252653 : Blo 167798 252653 := bbase (se 3 (by rfl) ⟨47372, by rfl⟩ : syracuseStep 252653 = 94745) (by norm_num)
theorem B285437 : Blo 167798 285437 := bbase (se 3 (by rfl) ⟨53519, by rfl⟩ : syracuseStep 285437 = 107039) (by norm_num)
theorem B383741 : Blo 167798 383741 := bbase (se 3 (by rfl) ⟨71951, by rfl⟩ : syracuseStep 383741 = 143903) (by norm_num)
theorem B252677 : Blo 167798 252677 := bbase (se 4 (by rfl) ⟨23688, by rfl⟩ : syracuseStep 252677 = 47377) (by norm_num)
theorem B252701 : Blo 167798 252701 := bbase (se 3 (by rfl) ⟨47381, by rfl⟩ : syracuseStep 252701 = 94763) (by norm_num)
theorem B252725 : Blo 167798 252725 := bbase (se 5 (by rfl) ⟨11846, by rfl⟩ : syracuseStep 252725 = 23693) (by norm_num)
theorem B383813 : Blo 167798 383813 := bbase (se 4 (by rfl) ⟨35982, by rfl⟩ : syracuseStep 383813 = 71965) (by norm_num)
theorem B252749 : Blo 167798 252749 := bbase (se 3 (by rfl) ⟨47390, by rfl⟩ : syracuseStep 252749 = 94781) (by norm_num)
theorem B252773 : Blo 167798 252773 := bbase (se 4 (by rfl) ⟨23697, by rfl⟩ : syracuseStep 252773 = 47395) (by norm_num)
theorem B252797 : Blo 167798 252797 := bbase (se 3 (by rfl) ⟨47399, by rfl⟩ : syracuseStep 252797 = 94799) (by norm_num)
theorem B285565 : Blo 167798 285565 := bbase (se 3 (by rfl) ⟨53543, by rfl⟩ : syracuseStep 285565 = 107087) (by norm_num)
theorem B383885 : Blo 167798 383885 := bbase (se 3 (by rfl) ⟨71978, by rfl⟩ : syracuseStep 383885 = 143957) (by norm_num)
theorem B252821 : Blo 167798 252821 := bbase (se 6 (by rfl) ⟨5925, by rfl⟩ : syracuseStep 252821 = 11851) (by norm_num)
theorem B252845 : Blo 167798 252845 := bbase (se 3 (by rfl) ⟨47408, by rfl⟩ : syracuseStep 252845 = 94817) (by norm_num)
theorem B809909 : Blo 167798 809909 := bbase (se 5 (by rfl) ⟨37964, by rfl⟩ : syracuseStep 809909 = 75929) (by norm_num)
theorem B252869 : Blo 167798 252869 := bbase (se 4 (by rfl) ⟨23706, by rfl⟩ : syracuseStep 252869 = 47413) (by norm_num)
theorem B285653 : Blo 167798 285653 := bbase (se 7 (by rfl) ⟨3347, by rfl⟩ : syracuseStep 285653 = 6695) (by norm_num)
theorem B383957 : Blo 167798 383957 := bbase (se 7 (by rfl) ⟨4499, by rfl⟩ : syracuseStep 383957 = 8999) (by norm_num)
theorem B252893 : Blo 167798 252893 := bbase (se 3 (by rfl) ⟨47417, by rfl⟩ : syracuseStep 252893 = 94835) (by norm_num)
theorem B252917 : Blo 167798 252917 := bbase (se 5 (by rfl) ⟨11855, by rfl⟩ : syracuseStep 252917 = 23711) (by norm_num)
theorem B252941 : Blo 167798 252941 := bbase (se 3 (by rfl) ⟨47426, by rfl⟩ : syracuseStep 252941 = 94853) (by norm_num)
theorem B384029 : Blo 167798 384029 := bbase (se 3 (by rfl) ⟨72005, by rfl⟩ : syracuseStep 384029 = 144011) (by norm_num)
theorem B252965 : Blo 167798 252965 := bbase (se 4 (by rfl) ⟨23715, by rfl⟩ : syracuseStep 252965 = 47431) (by norm_num)
theorem B252989 : Blo 167798 252989 := bbase (se 3 (by rfl) ⟨47435, by rfl⟩ : syracuseStep 252989 = 94871) (by norm_num)
theorem B253013 : Blo 167798 253013 := bbase (se 8 (by rfl) ⟨1482, by rfl⟩ : syracuseStep 253013 = 2965) (by norm_num)
theorem B285781 : Blo 167798 285781 := bbase (se 8 (by rfl) ⟨1674, by rfl⟩ : syracuseStep 285781 = 3349) (by norm_num)
theorem B384101 : Blo 167798 384101 := bbase (se 4 (by rfl) ⟨36009, by rfl⟩ : syracuseStep 384101 = 72019) (by norm_num)
theorem B253037 : Blo 167798 253037 := bbase (se 3 (by rfl) ⟨47444, by rfl⟩ : syracuseStep 253037 = 94889) (by norm_num)
theorem B253061 : Blo 167798 253061 := bbase (se 4 (by rfl) ⟨23724, by rfl⟩ : syracuseStep 253061 = 47449) (by norm_num)
theorem B253085 : Blo 167798 253085 := bbase (se 3 (by rfl) ⟨47453, by rfl⟩ : syracuseStep 253085 = 94907) (by norm_num)
theorem B285869 : Blo 167798 285869 := bbase (se 3 (by rfl) ⟨53600, by rfl⟩ : syracuseStep 285869 = 107201) (by norm_num)
theorem B384173 : Blo 167798 384173 := bbase (se 3 (by rfl) ⟨72032, by rfl⟩ : syracuseStep 384173 = 144065) (by norm_num)
theorem B253109 : Blo 167798 253109 := bbase (se 5 (by rfl) ⟨11864, by rfl⟩ : syracuseStep 253109 = 23729) (by norm_num)
theorem B253133 : Blo 167798 253133 := bbase (se 3 (by rfl) ⟨47462, by rfl⟩ : syracuseStep 253133 = 94925) (by norm_num)
theorem B2186453 : Blo 167798 2186453 := bbase (se 7 (by rfl) ⟨25622, by rfl⟩ : syracuseStep 2186453 = 51245) (by norm_num)
theorem B253157 : Blo 167798 253157 := bbase (se 4 (by rfl) ⟨23733, by rfl⟩ : syracuseStep 253157 = 47467) (by norm_num)
theorem B384245 : Blo 167798 384245 := bbase (se 5 (by rfl) ⟨18011, by rfl⟩ : syracuseStep 384245 = 36023) (by norm_num)
theorem B253181 : Blo 167798 253181 := bbase (se 3 (by rfl) ⟨47471, by rfl⟩ : syracuseStep 253181 = 94943) (by norm_num)
theorem B318725 : Blo 167798 318725 := bbase (se 4 (by rfl) ⟨29880, by rfl⟩ : syracuseStep 318725 = 59761) (by norm_num)
theorem B253205 : Blo 167798 253205 := bbase (se 6 (by rfl) ⟨5934, by rfl⟩ : syracuseStep 253205 = 11869) (by norm_num)
theorem B253229 : Blo 167798 253229 := bbase (se 3 (by rfl) ⟨47480, by rfl⟩ : syracuseStep 253229 = 94961) (by norm_num)
theorem B285997 : Blo 167798 285997 := bbase (se 3 (by rfl) ⟨53624, by rfl⟩ : syracuseStep 285997 = 107249) (by norm_num)
theorem B384317 : Blo 167798 384317 := bbase (se 3 (by rfl) ⟨72059, by rfl⟩ : syracuseStep 384317 = 144119) (by norm_num)
theorem B253253 : Blo 167798 253253 := bbase (se 4 (by rfl) ⟨23742, by rfl⟩ : syracuseStep 253253 = 47485) (by norm_num)
theorem B253277 : Blo 167798 253277 := bbase (se 3 (by rfl) ⟨47489, by rfl⟩ : syracuseStep 253277 = 94979) (by norm_num)
theorem B646501 : Blo 167798 646501 := bbase (se 4 (by rfl) ⟨60609, by rfl⟩ : syracuseStep 646501 = 121219) (by norm_num)
theorem B253301 : Blo 167798 253301 := bbase (se 5 (by rfl) ⟨11873, by rfl⟩ : syracuseStep 253301 = 23747) (by norm_num)
theorem B286085 : Blo 167798 286085 := bbase (se 4 (by rfl) ⟨26820, by rfl⟩ : syracuseStep 286085 = 53641) (by norm_num)
theorem B384389 : Blo 167798 384389 := bbase (se 4 (by rfl) ⟨36036, by rfl⟩ : syracuseStep 384389 = 72073) (by norm_num)
theorem B253325 : Blo 167798 253325 := bbase (se 3 (by rfl) ⟨47498, by rfl⟩ : syracuseStep 253325 = 94997) (by norm_num)
theorem B253349 : Blo 167798 253349 := bbase (se 4 (by rfl) ⟨23751, by rfl⟩ : syracuseStep 253349 = 47503) (by norm_num)
theorem B253373 : Blo 167798 253373 := bbase (se 3 (by rfl) ⟨47507, by rfl⟩ : syracuseStep 253373 = 95015) (by norm_num)
theorem B384461 : Blo 167798 384461 := bbase (se 3 (by rfl) ⟨72086, by rfl⟩ : syracuseStep 384461 = 144173) (by norm_num)
theorem B253397 : Blo 167798 253397 := bbase (se 7 (by rfl) ⟨2969, by rfl⟩ : syracuseStep 253397 = 5939) (by norm_num)
theorem B777701 : Blo 167798 777701 := bbase (se 4 (by rfl) ⟨72909, by rfl⟩ : syracuseStep 777701 = 145819) (by norm_num)
theorem B253421 : Blo 167798 253421 := bbase (se 3 (by rfl) ⟨47516, by rfl⟩ : syracuseStep 253421 = 95033) (by norm_num)
theorem B253445 : Blo 167798 253445 := bbase (se 4 (by rfl) ⟨23760, by rfl⟩ : syracuseStep 253445 = 47521) (by norm_num)
theorem B286213 : Blo 167798 286213 := bbase (se 4 (by rfl) ⟨26832, by rfl⟩ : syracuseStep 286213 = 53665) (by norm_num)
theorem B384533 : Blo 167798 384533 := bbase (se 6 (by rfl) ⟨9012, by rfl⟩ : syracuseStep 384533 = 18025) (by norm_num)
theorem B253469 : Blo 167798 253469 := bbase (se 3 (by rfl) ⟨47525, by rfl⟩ : syracuseStep 253469 = 95051) (by norm_num)
theorem B253493 : Blo 167798 253493 := bbase (se 5 (by rfl) ⟨11882, by rfl⟩ : syracuseStep 253493 = 23765) (by norm_num)
theorem B253517 : Blo 167798 253517 := bbase (se 3 (by rfl) ⟨47534, by rfl⟩ : syracuseStep 253517 = 95069) (by norm_num)
theorem B286301 : Blo 167798 286301 := bbase (se 3 (by rfl) ⟨53681, by rfl⟩ : syracuseStep 286301 = 107363) (by norm_num)
theorem B384605 : Blo 167798 384605 := bbase (se 3 (by rfl) ⟨72113, by rfl⟩ : syracuseStep 384605 = 144227) (by norm_num)
theorem B253541 : Blo 167798 253541 := bbase (se 4 (by rfl) ⟨23769, by rfl⟩ : syracuseStep 253541 = 47539) (by norm_num)
theorem B482917 : Blo 167798 482917 := bbase (se 4 (by rfl) ⟨45273, by rfl⟩ : syracuseStep 482917 = 90547) (by norm_num)
theorem B253565 : Blo 167798 253565 := bbase (se 3 (by rfl) ⟨47543, by rfl⟩ : syracuseStep 253565 = 95087) (by norm_num)
theorem B253589 : Blo 167798 253589 := bbase (se 6 (by rfl) ⟨5943, by rfl⟩ : syracuseStep 253589 = 11887) (by norm_num)
theorem B646805 : Blo 167798 646805 := bbase (se 6 (by rfl) ⟨15159, by rfl⟩ : syracuseStep 646805 = 30319) (by norm_num)
theorem B384677 : Blo 167798 384677 := bbase (se 4 (by rfl) ⟨36063, by rfl⟩ : syracuseStep 384677 = 72127) (by norm_num)
theorem B253613 : Blo 167798 253613 := bbase (se 3 (by rfl) ⟨47552, by rfl⟩ : syracuseStep 253613 = 95105) (by norm_num)
theorem B253637 : Blo 167798 253637 := bbase (se 4 (by rfl) ⟨23778, by rfl⟩ : syracuseStep 253637 = 47557) (by norm_num)
theorem B253661 : Blo 167798 253661 := bbase (se 3 (by rfl) ⟨47561, by rfl⟩ : syracuseStep 253661 = 95123) (by norm_num)
theorem B286429 : Blo 167798 286429 := bbase (se 3 (by rfl) ⟨53705, by rfl⟩ : syracuseStep 286429 = 107411) (by norm_num)
theorem B384749 : Blo 167798 384749 := bbase (se 3 (by rfl) ⟨72140, by rfl⟩ : syracuseStep 384749 = 144281) (by norm_num)
theorem B253685 : Blo 167798 253685 := bbase (se 5 (by rfl) ⟨11891, by rfl⟩ : syracuseStep 253685 = 23783) (by norm_num)
theorem B483077 : Blo 167798 483077 := bbase (se 4 (by rfl) ⟨45288, by rfl⟩ : syracuseStep 483077 = 90577) (by norm_num)
theorem B253709 : Blo 167798 253709 := bbase (se 3 (by rfl) ⟨47570, by rfl⟩ : syracuseStep 253709 = 95141) (by norm_num)
theorem B253733 : Blo 167798 253733 := bbase (se 4 (by rfl) ⟨23787, by rfl⟩ : syracuseStep 253733 = 47575) (by norm_num)
theorem B286517 : Blo 167798 286517 := bbase (se 5 (by rfl) ⟨13430, by rfl⟩ : syracuseStep 286517 = 26861) (by norm_num)
theorem B384821 : Blo 167798 384821 := bbase (se 5 (by rfl) ⟨18038, by rfl⟩ : syracuseStep 384821 = 36077) (by norm_num)
theorem B253757 : Blo 167798 253757 := bbase (se 3 (by rfl) ⟨47579, by rfl⟩ : syracuseStep 253757 = 95159) (by norm_num)
theorem B253781 : Blo 167798 253781 := bbase (se 9 (by rfl) ⟨743, by rfl⟩ : syracuseStep 253781 = 1487) (by norm_num)
theorem B253805 : Blo 167798 253805 := bbase (se 3 (by rfl) ⟨47588, by rfl⟩ : syracuseStep 253805 = 95177) (by norm_num)
theorem B384893 : Blo 167798 384893 := bbase (se 3 (by rfl) ⟨72167, by rfl⟩ : syracuseStep 384893 = 144335) (by norm_num)
theorem B253829 : Blo 167798 253829 := bbase (se 4 (by rfl) ⟨23796, by rfl⟩ : syracuseStep 253829 = 47593) (by norm_num)
theorem B581525 : Blo 167798 581525 := bbase (se 6 (by rfl) ⟨13629, by rfl⟩ : syracuseStep 581525 = 27259) (by norm_num)
theorem B253853 : Blo 167798 253853 := bbase (se 3 (by rfl) ⟨47597, by rfl⟩ : syracuseStep 253853 = 95195) (by norm_num)
theorem B253877 : Blo 167798 253877 := bbase (se 5 (by rfl) ⟨11900, by rfl⟩ : syracuseStep 253877 = 23801) (by norm_num)
theorem B286645 : Blo 167798 286645 := bbase (se 5 (by rfl) ⟨13436, by rfl⟩ : syracuseStep 286645 = 26873) (by norm_num)
theorem B384965 : Blo 167798 384965 := bbase (se 4 (by rfl) ⟨36090, by rfl⟩ : syracuseStep 384965 = 72181) (by norm_num)
theorem B253901 : Blo 167798 253901 := bbase (se 3 (by rfl) ⟨47606, by rfl⟩ : syracuseStep 253901 = 95213) (by norm_num)
theorem B253925 : Blo 167798 253925 := bbase (se 4 (by rfl) ⟨23805, by rfl⟩ : syracuseStep 253925 = 47611) (by norm_num)
theorem B319477 : Blo 167798 319477 := bbase (se 5 (by rfl) ⟨14975, by rfl⟩ : syracuseStep 319477 = 29951) (by norm_num)
theorem B483317 : Blo 167798 483317 := bbase (se 5 (by rfl) ⟨22655, by rfl⟩ : syracuseStep 483317 = 45311) (by norm_num)
theorem B253949 : Blo 167798 253949 := bbase (se 3 (by rfl) ⟨47615, by rfl⟩ : syracuseStep 253949 = 95231) (by norm_num)
theorem B548869 : Blo 167798 548869 := bbase (se 4 (by rfl) ⟨51456, by rfl⟩ : syracuseStep 548869 = 102913) (by norm_num)
theorem B286733 : Blo 167798 286733 := bbase (se 3 (by rfl) ⟨53762, by rfl⟩ : syracuseStep 286733 = 107525) (by norm_num)
theorem B385037 : Blo 167798 385037 := bbase (se 3 (by rfl) ⟨72194, by rfl⟩ : syracuseStep 385037 = 144389) (by norm_num)
theorem B253973 : Blo 167798 253973 := bbase (se 6 (by rfl) ⟨5952, by rfl⟩ : syracuseStep 253973 = 11905) (by norm_num)
theorem B253997 : Blo 167798 253997 := bbase (se 3 (by rfl) ⟨47624, by rfl⟩ : syracuseStep 253997 = 95249) (by norm_num)
theorem B254021 : Blo 167798 254021 := bbase (se 4 (by rfl) ⟨23814, by rfl⟩ : syracuseStep 254021 = 47629) (by norm_num)
theorem B385109 : Blo 167798 385109 := bbase (se 8 (by rfl) ⟨2256, by rfl⟩ : syracuseStep 385109 = 4513) (by norm_num)
theorem B254045 : Blo 167798 254045 := bbase (se 3 (by rfl) ⟨47633, by rfl⟩ : syracuseStep 254045 = 95267) (by norm_num)
theorem B254069 : Blo 167798 254069 := bbase (se 5 (by rfl) ⟨11909, by rfl⟩ : syracuseStep 254069 = 23819) (by norm_num)
theorem B319621 : Blo 167798 319621 := bbase (se 4 (by rfl) ⟨29964, by rfl⟩ : syracuseStep 319621 = 59929) (by norm_num)
theorem B254093 : Blo 167798 254093 := bbase (se 3 (by rfl) ⟨47642, by rfl⟩ : syracuseStep 254093 = 95285) (by norm_num)
theorem B286861 : Blo 167798 286861 := bbase (se 3 (by rfl) ⟨53786, by rfl⟩ : syracuseStep 286861 = 107573) (by norm_num)
theorem B385181 : Blo 167798 385181 := bbase (se 3 (by rfl) ⟨72221, by rfl⟩ : syracuseStep 385181 = 144443) (by norm_num)
theorem B254117 : Blo 167798 254117 := bbase (se 4 (by rfl) ⟨23823, by rfl⟩ : syracuseStep 254117 = 47647) (by norm_num)
theorem B483509 : Blo 167798 483509 := bbase (se 5 (by rfl) ⟨22664, by rfl⟩ : syracuseStep 483509 = 45329) (by norm_num)
theorem B254141 : Blo 167798 254141 := bbase (se 3 (by rfl) ⟨47651, by rfl⟩ : syracuseStep 254141 = 95303) (by norm_num)
theorem B254165 : Blo 167798 254165 := bbase (se 7 (by rfl) ⟨2978, by rfl⟩ : syracuseStep 254165 = 5957) (by norm_num)
theorem B286949 : Blo 167798 286949 := bbase (se 4 (by rfl) ⟨26901, by rfl⟩ : syracuseStep 286949 = 53803) (by norm_num)
theorem B385253 : Blo 167798 385253 := bbase (se 4 (by rfl) ⟨36117, by rfl⟩ : syracuseStep 385253 = 72235) (by norm_num)
theorem B254189 : Blo 167798 254189 := bbase (se 3 (by rfl) ⟨47660, by rfl⟩ : syracuseStep 254189 = 95321) (by norm_num)
theorem B254213 : Blo 167798 254213 := bbase (se 4 (by rfl) ⟨23832, by rfl⟩ : syracuseStep 254213 = 47665) (by norm_num)
theorem B254237 : Blo 167798 254237 := bbase (se 3 (by rfl) ⟨47669, by rfl⟩ : syracuseStep 254237 = 95339) (by norm_num)
theorem B319781 : Blo 167798 319781 := bbase (se 4 (by rfl) ⟨29979, by rfl⟩ : syracuseStep 319781 = 59959) (by norm_num)
theorem B385325 : Blo 167798 385325 := bbase (se 3 (by rfl) ⟨72248, by rfl⟩ : syracuseStep 385325 = 144497) (by norm_num)
theorem B254261 : Blo 167798 254261 := bbase (se 5 (by rfl) ⟨11918, by rfl⟩ : syracuseStep 254261 = 23837) (by norm_num)
theorem B254285 : Blo 167798 254285 := bbase (se 3 (by rfl) ⟨47678, by rfl⟩ : syracuseStep 254285 = 95357) (by norm_num)
theorem B254309 : Blo 167798 254309 := bbase (se 4 (by rfl) ⟨23841, by rfl⟩ : syracuseStep 254309 = 47683) (by norm_num)
theorem B287077 : Blo 167798 287077 := bbase (se 4 (by rfl) ⟨26913, by rfl⟩ : syracuseStep 287077 = 53827) (by norm_num)
theorem B385397 : Blo 167798 385397 := bbase (se 5 (by rfl) ⟨18065, by rfl⟩ : syracuseStep 385397 = 36131) (by norm_num)
theorem B188797 : Blo 167798 188797 := bbase (se 3 (by rfl) ⟨35399, by rfl⟩ : syracuseStep 188797 = 70799) (by norm_num)
theorem B254333 : Blo 167798 254333 := bbase (se 3 (by rfl) ⟨47687, by rfl⟩ : syracuseStep 254333 = 95375) (by norm_num)
theorem B254357 : Blo 167798 254357 := bbase (se 6 (by rfl) ⟨5961, by rfl⟩ : syracuseStep 254357 = 11923) (by norm_num)
theorem B188833 : Blo 167798 188833 := bbase (se 2 (by rfl) ⟨70812, by rfl⟩ : syracuseStep 188833 = 141625) (by norm_num)
theorem B254381 : Blo 167798 254381 := bbase (se 3 (by rfl) ⟨47696, by rfl⟩ : syracuseStep 254381 = 95393) (by norm_num)
theorem B319925 : Blo 167798 319925 := bbase (se 5 (by rfl) ⟨14996, by rfl⟩ : syracuseStep 319925 = 29993) (by norm_num)
theorem B1302965 : Blo 167798 1302965 := bbase (se 5 (by rfl) ⟨61076, by rfl⟩ : syracuseStep 1302965 = 122153) (by norm_num)
theorem B287165 : Blo 167798 287165 := bbase (se 3 (by rfl) ⟨53843, by rfl⟩ : syracuseStep 287165 = 107687) (by norm_num)
theorem B385469 : Blo 167798 385469 := bbase (se 3 (by rfl) ⟨72275, by rfl⟩ : syracuseStep 385469 = 144551) (by norm_num)
theorem B188869 : Blo 167798 188869 := bbase (se 4 (by rfl) ⟨17706, by rfl⟩ : syracuseStep 188869 = 35413) (by norm_num)
theorem B254405 : Blo 167798 254405 := bbase (se 4 (by rfl) ⟨23850, by rfl⟩ : syracuseStep 254405 = 47701) (by norm_num)
theorem B254429 : Blo 167798 254429 := bbase (se 3 (by rfl) ⟨47705, by rfl⟩ : syracuseStep 254429 = 95411) (by norm_num)
theorem B188905 : Blo 167798 188905 := bbase (se 2 (by rfl) ⟨70839, by rfl⟩ : syracuseStep 188905 = 141679) (by norm_num)
theorem B254453 : Blo 167798 254453 := bbase (se 5 (by rfl) ⟨11927, by rfl⟩ : syracuseStep 254453 = 23855) (by norm_num)
theorem B1237493 : Blo 167798 1237493 := bbase (se 5 (by rfl) ⟨58007, by rfl⟩ : syracuseStep 1237493 = 116015) (by norm_num)
theorem B385541 : Blo 167798 385541 := bbase (se 4 (by rfl) ⟨36144, by rfl⟩ : syracuseStep 385541 = 72289) (by norm_num)
theorem B188941 : Blo 167798 188941 := bbase (se 3 (by rfl) ⟨35426, by rfl⟩ : syracuseStep 188941 = 70853) (by norm_num)
theorem B254477 : Blo 167798 254477 := bbase (se 3 (by rfl) ⟨47714, by rfl⟩ : syracuseStep 254477 = 95429) (by norm_num)
theorem B254501 : Blo 167798 254501 := bbase (se 4 (by rfl) ⟨23859, by rfl⟩ : syracuseStep 254501 = 47719) (by norm_num)
theorem B188977 : Blo 167798 188977 := bbase (se 2 (by rfl) ⟨70866, by rfl⟩ : syracuseStep 188977 = 141733) (by norm_num)
theorem B254525 : Blo 167798 254525 := bbase (se 3 (by rfl) ⟨47723, by rfl⟩ : syracuseStep 254525 = 95447) (by norm_num)
theorem B287293 : Blo 167798 287293 := bbase (se 3 (by rfl) ⟨53867, by rfl⟩ : syracuseStep 287293 = 107735) (by norm_num)
theorem B385613 : Blo 167798 385613 := bbase (se 3 (by rfl) ⟨72302, by rfl⟩ : syracuseStep 385613 = 144605) (by norm_num)
theorem B189013 : Blo 167798 189013 := bbase (se 8 (by rfl) ⟨1107, by rfl⟩ : syracuseStep 189013 = 2215) (by norm_num)
theorem B254549 : Blo 167798 254549 := bbase (se 8 (by rfl) ⟨1491, by rfl⟩ : syracuseStep 254549 = 2983) (by norm_num)
theorem B254573 : Blo 167798 254573 := bbase (se 3 (by rfl) ⟨47732, by rfl⟩ : syracuseStep 254573 = 95465) (by norm_num)
theorem B189049 : Blo 167798 189049 := bbase (se 2 (by rfl) ⟨70893, by rfl⟩ : syracuseStep 189049 = 141787) (by norm_num)
theorem B254597 : Blo 167798 254597 := bbase (se 4 (by rfl) ⟨23868, by rfl⟩ : syracuseStep 254597 = 47737) (by norm_num)
theorem B287381 : Blo 167798 287381 := bbase (se 6 (by rfl) ⟨6735, by rfl⟩ : syracuseStep 287381 = 13471) (by norm_num)
theorem B385685 : Blo 167798 385685 := bbase (se 6 (by rfl) ⟨9039, by rfl⟩ : syracuseStep 385685 = 18079) (by norm_num)
theorem B189085 : Blo 167798 189085 := bbase (se 3 (by rfl) ⟨35453, by rfl⟩ : syracuseStep 189085 = 70907) (by norm_num)
theorem B254621 : Blo 167798 254621 := bbase (se 3 (by rfl) ⟨47741, by rfl⟩ : syracuseStep 254621 = 95483) (by norm_num)
theorem B254645 : Blo 167798 254645 := bbase (se 5 (by rfl) ⟨11936, by rfl⟩ : syracuseStep 254645 = 23873) (by norm_num)
theorem B189121 : Blo 167798 189121 := bbase (se 2 (by rfl) ⟨70920, by rfl⟩ : syracuseStep 189121 = 141841) (by norm_num)
theorem B254669 : Blo 167798 254669 := bbase (se 3 (by rfl) ⟨47750, by rfl⟩ : syracuseStep 254669 = 95501) (by norm_num)
theorem B320213 : Blo 167798 320213 := bbase (se 7 (by rfl) ⟨3752, by rfl⟩ : syracuseStep 320213 = 7505) (by norm_num)
theorem B385757 : Blo 167798 385757 := bbase (se 3 (by rfl) ⟨72329, by rfl⟩ : syracuseStep 385757 = 144659) (by norm_num)
theorem B189157 : Blo 167798 189157 := bbase (se 4 (by rfl) ⟨17733, by rfl⟩ : syracuseStep 189157 = 35467) (by norm_num)
theorem B254693 : Blo 167798 254693 := bbase (se 4 (by rfl) ⟨23877, by rfl⟩ : syracuseStep 254693 = 47755) (by norm_num)
theorem B254717 : Blo 167798 254717 := bbase (se 3 (by rfl) ⟨47759, by rfl⟩ : syracuseStep 254717 = 95519) (by norm_num)
theorem B189193 : Blo 167798 189193 := bbase (se 2 (by rfl) ⟨70947, by rfl⟩ : syracuseStep 189193 = 141895) (by norm_num)
theorem B1237781 : Blo 167798 1237781 := bbase (se 6 (by rfl) ⟨29010, by rfl⟩ : syracuseStep 1237781 = 58021) (by norm_num)
theorem B254741 : Blo 167798 254741 := bbase (se 6 (by rfl) ⟨5970, by rfl⟩ : syracuseStep 254741 = 11941) (by norm_num)
theorem B287509 : Blo 167798 287509 := bbase (se 6 (by rfl) ⟨6738, by rfl⟩ : syracuseStep 287509 = 13477) (by norm_num)
theorem B385829 : Blo 167798 385829 := bbase (se 4 (by rfl) ⟨36171, by rfl⟩ : syracuseStep 385829 = 72343) (by norm_num)
theorem B189229 : Blo 167798 189229 := bbase (se 3 (by rfl) ⟨35480, by rfl⟩ : syracuseStep 189229 = 70961) (by norm_num)
theorem B254765 : Blo 167798 254765 := bbase (se 3 (by rfl) ⟨47768, by rfl⟩ : syracuseStep 254765 = 95537) (by norm_num)
theorem B254789 : Blo 167798 254789 := bbase (se 4 (by rfl) ⟨23886, by rfl⟩ : syracuseStep 254789 = 47773) (by norm_num)
theorem B189265 : Blo 167798 189265 := bbase (se 2 (by rfl) ⟨70974, by rfl⟩ : syracuseStep 189265 = 141949) (by norm_num)
theorem B254813 : Blo 167798 254813 := bbase (se 3 (by rfl) ⟨47777, by rfl⟩ : syracuseStep 254813 = 95555) (by norm_num)
theorem B615269 : Blo 167798 615269 := bbase (se 4 (by rfl) ⟨57681, by rfl⟩ : syracuseStep 615269 = 115363) (by norm_num)
theorem B320365 : Blo 167798 320365 := bbase (se 3 (by rfl) ⟨60068, by rfl⟩ : syracuseStep 320365 = 120137) (by norm_num)
theorem B287597 : Blo 167798 287597 := bbase (se 3 (by rfl) ⟨53924, by rfl⟩ : syracuseStep 287597 = 107849) (by norm_num)
theorem B385901 : Blo 167798 385901 := bbase (se 3 (by rfl) ⟨72356, by rfl⟩ : syracuseStep 385901 = 144713) (by norm_num)
theorem B189301 : Blo 167798 189301 := bbase (se 5 (by rfl) ⟨8873, by rfl⟩ : syracuseStep 189301 = 17747) (by norm_num)
theorem B254837 : Blo 167798 254837 := bbase (se 5 (by rfl) ⟨11945, by rfl⟩ : syracuseStep 254837 = 23891) (by norm_num)
theorem B254861 : Blo 167798 254861 := bbase (se 3 (by rfl) ⟨47786, by rfl⟩ : syracuseStep 254861 = 95573) (by norm_num)
theorem B189337 : Blo 167798 189337 := bbase (se 2 (by rfl) ⟨71001, by rfl⟩ : syracuseStep 189337 = 142003) (by norm_num)
theorem B254885 : Blo 167798 254885 := bbase (se 4 (by rfl) ⟨23895, by rfl⟩ : syracuseStep 254885 = 47791) (by norm_num)
theorem B385973 : Blo 167798 385973 := bbase (se 5 (by rfl) ⟨18092, by rfl⟩ : syracuseStep 385973 = 36185) (by norm_num)
theorem B189373 : Blo 167798 189373 := bbase (se 3 (by rfl) ⟨35507, by rfl⟩ : syracuseStep 189373 = 71015) (by norm_num)
theorem B254909 : Blo 167798 254909 := bbase (se 3 (by rfl) ⟨47795, by rfl⟩ : syracuseStep 254909 = 95591) (by norm_num)
theorem B254933 : Blo 167798 254933 := bbase (se 7 (by rfl) ⟨2987, by rfl⟩ : syracuseStep 254933 = 5975) (by norm_num)
theorem B189409 : Blo 167798 189409 := bbase (se 2 (by rfl) ⟨71028, by rfl⟩ : syracuseStep 189409 = 142057) (by norm_num)
theorem B254957 : Blo 167798 254957 := bbase (se 3 (by rfl) ⟨47804, by rfl⟩ : syracuseStep 254957 = 95609) (by norm_num)
theorem B287725 : Blo 167798 287725 := bbase (se 3 (by rfl) ⟨53948, by rfl⟩ : syracuseStep 287725 = 107897) (by norm_num)
theorem B386045 : Blo 167798 386045 := bbase (se 3 (by rfl) ⟨72383, by rfl⟩ : syracuseStep 386045 = 144767) (by norm_num)
theorem B189445 : Blo 167798 189445 := bbase (se 4 (by rfl) ⟨17760, by rfl⟩ : syracuseStep 189445 = 35521) (by norm_num)
theorem B254981 : Blo 167798 254981 := bbase (se 4 (by rfl) ⟨23904, by rfl⟩ : syracuseStep 254981 = 47809) (by norm_num)
theorem B2057237 : Blo 167798 2057237 := bbase (se 6 (by rfl) ⟨48216, by rfl⟩ : syracuseStep 2057237 = 96433) (by norm_num)
theorem B255005 : Blo 167798 255005 := bbase (se 3 (by rfl) ⟨47813, by rfl⟩ : syracuseStep 255005 = 95627) (by norm_num)
theorem B189481 : Blo 167798 189481 := bbase (se 2 (by rfl) ⟨71055, by rfl⟩ : syracuseStep 189481 = 142111) (by norm_num)
theorem B255029 : Blo 167798 255029 := bbase (se 5 (by rfl) ⟨11954, by rfl⟩ : syracuseStep 255029 = 23909) (by norm_num)
theorem B287813 : Blo 167798 287813 := bbase (se 4 (by rfl) ⟨26982, by rfl⟩ : syracuseStep 287813 = 53965) (by norm_num)
theorem B386117 : Blo 167798 386117 := bbase (se 4 (by rfl) ⟨36198, by rfl⟩ : syracuseStep 386117 = 72397) (by norm_num)
theorem B189517 : Blo 167798 189517 := bbase (se 3 (by rfl) ⟨35534, by rfl⟩ : syracuseStep 189517 = 71069) (by norm_num)
theorem B255053 : Blo 167798 255053 := bbase (se 3 (by rfl) ⟨47822, by rfl⟩ : syracuseStep 255053 = 95645) (by norm_num)
theorem B255077 : Blo 167798 255077 := bbase (se 4 (by rfl) ⟨23913, by rfl⟩ : syracuseStep 255077 = 47827) (by norm_num)
theorem B189553 : Blo 167798 189553 := bbase (se 2 (by rfl) ⟨71082, by rfl⟩ : syracuseStep 189553 = 142165) (by norm_num)
theorem B255101 : Blo 167798 255101 := bbase (se 3 (by rfl) ⟨47831, by rfl⟩ : syracuseStep 255101 = 95663) (by norm_num)
theorem B386189 : Blo 167798 386189 := bbase (se 3 (by rfl) ⟨72410, by rfl⟩ : syracuseStep 386189 = 144821) (by norm_num)
theorem B189589 : Blo 167798 189589 := bbase (se 6 (by rfl) ⟨4443, by rfl⟩ : syracuseStep 189589 = 8887) (by norm_num)
theorem B255125 : Blo 167798 255125 := bbase (se 6 (by rfl) ⟨5979, by rfl⟩ : syracuseStep 255125 = 11959) (by norm_num)
theorem B484501 : Blo 167798 484501 := bbase (se 6 (by rfl) ⟨11355, by rfl⟩ : syracuseStep 484501 = 22711) (by norm_num)
theorem B320669 : Blo 167798 320669 := bbase (se 3 (by rfl) ⟨60125, by rfl⟩ : syracuseStep 320669 = 120251) (by norm_num)
theorem B255149 : Blo 167798 255149 := bbase (se 3 (by rfl) ⟨47840, by rfl⟩ : syracuseStep 255149 = 95681) (by norm_num)
theorem B189625 : Blo 167798 189625 := bbase (se 2 (by rfl) ⟨71109, by rfl⟩ : syracuseStep 189625 = 142219) (by norm_num)
theorem B255173 : Blo 167798 255173 := bbase (se 4 (by rfl) ⟨23922, by rfl⟩ : syracuseStep 255173 = 47845) (by norm_num)
theorem B287941 : Blo 167798 287941 := bbase (se 4 (by rfl) ⟨26994, by rfl⟩ : syracuseStep 287941 = 53989) (by norm_num)
theorem B386261 : Blo 167798 386261 := bbase (se 7 (by rfl) ⟨4526, by rfl⟩ : syracuseStep 386261 = 9053) (by norm_num)
theorem B189661 : Blo 167798 189661 := bbase (se 3 (by rfl) ⟨35561, by rfl⟩ : syracuseStep 189661 = 71123) (by norm_num)
theorem B255197 : Blo 167798 255197 := bbase (se 3 (by rfl) ⟨47849, by rfl⟩ : syracuseStep 255197 = 95699) (by norm_num)
theorem B681205 : Blo 167798 681205 := bbase (se 5 (by rfl) ⟨31931, by rfl⟩ : syracuseStep 681205 = 63863) (by norm_num)
theorem B255221 : Blo 167798 255221 := bbase (se 5 (by rfl) ⟨11963, by rfl⟩ : syracuseStep 255221 = 23927) (by norm_num)
theorem B189697 : Blo 167798 189697 := bbase (se 2 (by rfl) ⟨71136, by rfl⟩ : syracuseStep 189697 = 142273) (by norm_num)
theorem B255245 : Blo 167798 255245 := bbase (se 3 (by rfl) ⟨47858, by rfl⟩ : syracuseStep 255245 = 95717) (by norm_num)
theorem B288029 : Blo 167798 288029 := bbase (se 3 (by rfl) ⟨54005, by rfl⟩ : syracuseStep 288029 = 108011) (by norm_num)
theorem B386333 : Blo 167798 386333 := bbase (se 3 (by rfl) ⟨72437, by rfl⟩ : syracuseStep 386333 = 144875) (by norm_num)
theorem B189733 : Blo 167798 189733 := bbase (se 4 (by rfl) ⟨17787, by rfl⟩ : syracuseStep 189733 = 35575) (by norm_num)
theorem B255269 : Blo 167798 255269 := bbase (se 4 (by rfl) ⟨23931, by rfl⟩ : syracuseStep 255269 = 47863) (by norm_num)
theorem B877877 : Blo 167798 877877 := bbase (se 5 (by rfl) ⟨41150, by rfl⟩ : syracuseStep 877877 = 82301) (by norm_num)
theorem B255293 : Blo 167798 255293 := bbase (se 3 (by rfl) ⟨47867, by rfl⟩ : syracuseStep 255293 = 95735) (by norm_num)
theorem B189769 : Blo 167798 189769 := bbase (se 2 (by rfl) ⟨71163, by rfl⟩ : syracuseStep 189769 = 142327) (by norm_num)
theorem B255317 : Blo 167798 255317 := bbase (se 12 (by rfl) ⟨93, by rfl⟩ : syracuseStep 255317 = 187) (by norm_num)
theorem B3106133 : Blo 167798 3106133 := bbase (se 12 (by rfl) ⟨1137, by rfl⟩ : syracuseStep 3106133 = 2275) (by norm_num)
theorem B386405 : Blo 167798 386405 := bbase (se 4 (by rfl) ⟨36225, by rfl⟩ : syracuseStep 386405 = 72451) (by norm_num)
theorem B189805 : Blo 167798 189805 := bbase (se 3 (by rfl) ⟨35588, by rfl⟩ : syracuseStep 189805 = 71177) (by norm_num)
theorem B255341 : Blo 167798 255341 := bbase (se 3 (by rfl) ⟨47876, by rfl⟩ : syracuseStep 255341 = 95753) (by norm_num)
theorem B255365 : Blo 167798 255365 := bbase (se 4 (by rfl) ⟨23940, by rfl⟩ : syracuseStep 255365 = 47881) (by norm_num)
theorem B189841 : Blo 167798 189841 := bbase (se 2 (by rfl) ⟨71190, by rfl⟩ : syracuseStep 189841 = 142381) (by norm_num)
theorem B681365 : Blo 167798 681365 := bbase (se 6 (by rfl) ⟨15969, by rfl⟩ : syracuseStep 681365 = 31939) (by norm_num)
theorem B255389 : Blo 167798 255389 := bbase (se 3 (by rfl) ⟨47885, by rfl⟩ : syracuseStep 255389 = 95771) (by norm_num)
theorem B288157 : Blo 167798 288157 := bbase (se 3 (by rfl) ⟨54029, by rfl⟩ : syracuseStep 288157 = 108059) (by norm_num)
theorem B386477 : Blo 167798 386477 := bbase (se 3 (by rfl) ⟨72464, by rfl⟩ : syracuseStep 386477 = 144929) (by norm_num)
theorem B189877 : Blo 167798 189877 := bbase (se 5 (by rfl) ⟨8900, by rfl⟩ : syracuseStep 189877 = 17801) (by norm_num)
theorem B255413 : Blo 167798 255413 := bbase (se 5 (by rfl) ⟨11972, by rfl⟩ : syracuseStep 255413 = 23945) (by norm_num)
theorem B255437 : Blo 167798 255437 := bbase (se 3 (by rfl) ⟨47894, by rfl⟩ : syracuseStep 255437 = 95789) (by norm_num)
theorem B189913 : Blo 167798 189913 := bbase (se 2 (by rfl) ⟨71217, by rfl⟩ : syracuseStep 189913 = 142435) (by norm_num)
theorem B255461 : Blo 167798 255461 := bbase (se 4 (by rfl) ⟨23949, by rfl⟩ : syracuseStep 255461 = 47899) (by norm_num)
theorem B288245 : Blo 167798 288245 := bbase (se 5 (by rfl) ⟨13511, by rfl⟩ : syracuseStep 288245 = 27023) (by norm_num)
theorem B189949 : Blo 167798 189949 := bbase (se 3 (by rfl) ⟨35615, by rfl⟩ : syracuseStep 189949 = 71231) (by norm_num)
theorem B255485 : Blo 167798 255485 := bbase (se 3 (by rfl) ⟨47903, by rfl⟩ : syracuseStep 255485 = 95807) (by norm_num)
theorem B255509 : Blo 167798 255509 := bbase (se 6 (by rfl) ⟨5988, by rfl⟩ : syracuseStep 255509 = 11977) (by norm_num)
theorem B189985 : Blo 167798 189985 := bbase (se 2 (by rfl) ⟨71244, by rfl⟩ : syracuseStep 189985 = 142489) (by norm_num)
theorem B255533 : Blo 167798 255533 := bbase (se 3 (by rfl) ⟨47912, by rfl⟩ : syracuseStep 255533 = 95825) (by norm_num)
theorem B190021 : Blo 167798 190021 := bbase (se 4 (by rfl) ⟨17814, by rfl⟩ : syracuseStep 190021 = 35629) (by norm_num)
theorem B255557 : Blo 167798 255557 := bbase (se 4 (by rfl) ⟨23958, by rfl⟩ : syracuseStep 255557 = 47917) (by norm_num)
theorem B255581 : Blo 167798 255581 := bbase (se 3 (by rfl) ⟨47921, by rfl⟩ : syracuseStep 255581 = 95843) (by norm_num)
theorem B190057 : Blo 167798 190057 := bbase (se 2 (by rfl) ⟨71271, by rfl⟩ : syracuseStep 190057 = 142543) (by norm_num)
theorem B255605 : Blo 167798 255605 := bbase (se 5 (by rfl) ⟨11981, by rfl⟩ : syracuseStep 255605 = 23963) (by norm_num)
theorem B288373 : Blo 167798 288373 := bbase (se 5 (by rfl) ⟨13517, by rfl⟩ : syracuseStep 288373 = 27035) (by norm_num)
theorem B190093 : Blo 167798 190093 := bbase (se 3 (by rfl) ⟨35642, by rfl⟩ : syracuseStep 190093 = 71285) (by norm_num)
theorem B255629 : Blo 167798 255629 := bbase (se 3 (by rfl) ⟨47930, by rfl⟩ : syracuseStep 255629 = 95861) (by norm_num)
theorem B812693 : Blo 167798 812693 := bbase (se 6 (by rfl) ⟨19047, by rfl⟩ : syracuseStep 812693 = 38095) (by norm_num)
theorem B255653 : Blo 167798 255653 := bbase (se 4 (by rfl) ⟨23967, by rfl⟩ : syracuseStep 255653 = 47935) (by norm_num)
theorem B190129 : Blo 167798 190129 := bbase (se 2 (by rfl) ⟨71298, by rfl⟩ : syracuseStep 190129 = 142597) (by norm_num)
theorem B255677 : Blo 167798 255677 := bbase (se 3 (by rfl) ⟨47939, by rfl⟩ : syracuseStep 255677 = 95879) (by norm_num)
theorem B288461 : Blo 167798 288461 := bbase (se 3 (by rfl) ⟨54086, by rfl⟩ : syracuseStep 288461 = 108173) (by norm_num)
theorem B190165 : Blo 167798 190165 := bbase (se 7 (by rfl) ⟨2228, by rfl⟩ : syracuseStep 190165 = 4457) (by norm_num)
theorem B255701 : Blo 167798 255701 := bbase (se 7 (by rfl) ⟨2996, by rfl⟩ : syracuseStep 255701 = 5993) (by norm_num)
theorem B648917 : Blo 167798 648917 := bbase (se 7 (by rfl) ⟨7604, by rfl⟩ : syracuseStep 648917 = 15209) (by norm_num)
theorem B255725 : Blo 167798 255725 := bbase (se 3 (by rfl) ⟨47948, by rfl⟩ : syracuseStep 255725 = 95897) (by norm_num)
theorem B190201 : Blo 167798 190201 := bbase (se 2 (by rfl) ⟨71325, by rfl⟩ : syracuseStep 190201 = 142651) (by norm_num)
theorem B255749 : Blo 167798 255749 := bbase (se 4 (by rfl) ⟨23976, by rfl⟩ : syracuseStep 255749 = 47953) (by norm_num)
theorem B190237 : Blo 167798 190237 := bbase (se 3 (by rfl) ⟨35669, by rfl⟩ : syracuseStep 190237 = 71339) (by norm_num)
theorem B255773 : Blo 167798 255773 := bbase (se 3 (by rfl) ⟨47957, by rfl⟩ : syracuseStep 255773 = 95915) (by norm_num)
theorem B255797 : Blo 167798 255797 := bbase (se 5 (by rfl) ⟨11990, by rfl⟩ : syracuseStep 255797 = 23981) (by norm_num)
theorem B190273 : Blo 167798 190273 := bbase (se 2 (by rfl) ⟨71352, by rfl⟩ : syracuseStep 190273 = 142705) (by norm_num)
theorem B255821 : Blo 167798 255821 := bbase (se 3 (by rfl) ⟨47966, by rfl⟩ : syracuseStep 255821 = 95933) (by norm_num)
theorem B288589 : Blo 167798 288589 := bbase (se 3 (by rfl) ⟨54110, by rfl⟩ : syracuseStep 288589 = 108221) (by norm_num)
theorem B190309 : Blo 167798 190309 := bbase (se 4 (by rfl) ⟨17841, by rfl⟩ : syracuseStep 190309 = 35683) (by norm_num)
theorem B255845 : Blo 167798 255845 := bbase (se 4 (by rfl) ⟨23985, by rfl⟩ : syracuseStep 255845 = 47971) (by norm_num)
theorem B255869 : Blo 167798 255869 := bbase (se 3 (by rfl) ⟨47975, by rfl⟩ : syracuseStep 255869 = 95951) (by norm_num)
theorem B190345 : Blo 167798 190345 := bbase (se 2 (by rfl) ⟨71379, by rfl⟩ : syracuseStep 190345 = 142759) (by norm_num)
theorem B321421 : Blo 167798 321421 := bbase (se 3 (by rfl) ⟨60266, by rfl⟩ : syracuseStep 321421 = 120533) (by norm_num)
theorem B255893 : Blo 167798 255893 := bbase (se 6 (by rfl) ⟨5997, by rfl⟩ : syracuseStep 255893 = 11995) (by norm_num)
theorem B288677 : Blo 167798 288677 := bbase (se 4 (by rfl) ⟨27063, by rfl⟩ : syracuseStep 288677 = 54127) (by norm_num)
theorem B190381 : Blo 167798 190381 := bbase (se 3 (by rfl) ⟨35696, by rfl⟩ : syracuseStep 190381 = 71393) (by norm_num)
theorem B255917 : Blo 167798 255917 := bbase (se 3 (by rfl) ⟨47984, by rfl⟩ : syracuseStep 255917 = 95969) (by norm_num)
theorem B255941 : Blo 167798 255941 := bbase (se 4 (by rfl) ⟨23994, by rfl⟩ : syracuseStep 255941 = 47989) (by norm_num)
theorem B190417 : Blo 167798 190417 := bbase (se 2 (by rfl) ⟨71406, by rfl⟩ : syracuseStep 190417 = 142813) (by norm_num)
theorem B255965 : Blo 167798 255965 := bbase (se 3 (by rfl) ⟨47993, by rfl⟩ : syracuseStep 255965 = 95987) (by norm_num)
theorem B190453 : Blo 167798 190453 := bbase (se 5 (by rfl) ⟨8927, by rfl⟩ : syracuseStep 190453 = 17855) (by norm_num)
theorem B255989 : Blo 167798 255989 := bbase (se 5 (by rfl) ⟨11999, by rfl⟩ : syracuseStep 255989 = 23999) (by norm_num)
theorem B649205 : Blo 167798 649205 := bbase (se 5 (by rfl) ⟨30431, by rfl⟩ : syracuseStep 649205 = 60863) (by norm_num)
theorem B256013 : Blo 167798 256013 := bbase (se 3 (by rfl) ⟨48002, by rfl⟩ : syracuseStep 256013 = 96005) (by norm_num)
theorem B190489 : Blo 167798 190489 := bbase (se 2 (by rfl) ⟨71433, by rfl⟩ : syracuseStep 190489 = 142867) (by norm_num)
theorem B321565 : Blo 167798 321565 := bbase (se 3 (by rfl) ⟨60293, by rfl⟩ : syracuseStep 321565 = 120587) (by norm_num)
theorem B256037 : Blo 167798 256037 := bbase (se 4 (by rfl) ⟨24003, by rfl⟩ : syracuseStep 256037 = 48007) (by norm_num)
theorem B288805 : Blo 167798 288805 := bbase (se 4 (by rfl) ⟨27075, by rfl⟩ : syracuseStep 288805 = 54151) (by norm_num)
theorem B190525 : Blo 167798 190525 := bbase (se 3 (by rfl) ⟨35723, by rfl⟩ : syracuseStep 190525 = 71447) (by norm_num)
theorem B256061 : Blo 167798 256061 := bbase (se 3 (by rfl) ⟨48011, by rfl⟩ : syracuseStep 256061 = 96023) (by norm_num)
theorem B256085 : Blo 167798 256085 := bbase (se 8 (by rfl) ⟨1500, by rfl⟩ : syracuseStep 256085 = 3001) (by norm_num)
theorem B190561 : Blo 167798 190561 := bbase (se 2 (by rfl) ⟨71460, by rfl⟩ : syracuseStep 190561 = 142921) (by norm_num)
theorem B256109 : Blo 167798 256109 := bbase (se 3 (by rfl) ⟨48020, by rfl⟩ : syracuseStep 256109 = 96041) (by norm_num)
theorem B1435765 : Blo 167798 1435765 := bbase (se 5 (by rfl) ⟨67301, by rfl⟩ : syracuseStep 1435765 = 134603) (by norm_num)
theorem B288893 : Blo 167798 288893 := bbase (se 3 (by rfl) ⟨54167, by rfl⟩ : syracuseStep 288893 = 108335) (by norm_num)
theorem B190597 : Blo 167798 190597 := bbase (se 4 (by rfl) ⟨17868, by rfl⟩ : syracuseStep 190597 = 35737) (by norm_num)
theorem B256133 : Blo 167798 256133 := bbase (se 4 (by rfl) ⟨24012, by rfl⟩ : syracuseStep 256133 = 48025) (by norm_num)
theorem B256157 : Blo 167798 256157 := bbase (se 3 (by rfl) ⟨48029, by rfl⟩ : syracuseStep 256157 = 96059) (by norm_num)
theorem B190633 : Blo 167798 190633 := bbase (se 2 (by rfl) ⟨71487, by rfl⟩ : syracuseStep 190633 = 142975) (by norm_num)
theorem B256181 : Blo 167798 256181 := bbase (se 5 (by rfl) ⟨12008, by rfl⟩ : syracuseStep 256181 = 24017) (by norm_num)
theorem B321725 : Blo 167798 321725 := bbase (se 3 (by rfl) ⟨60323, by rfl⟩ : syracuseStep 321725 = 120647) (by norm_num)
theorem B190669 : Blo 167798 190669 := bbase (se 3 (by rfl) ⟨35750, by rfl⟩ : syracuseStep 190669 = 71501) (by norm_num)
theorem B256205 : Blo 167798 256205 := bbase (se 3 (by rfl) ⟨48038, by rfl⟩ : syracuseStep 256205 = 96077) (by norm_num)
theorem B485605 : Blo 167798 485605 := bbase (se 4 (by rfl) ⟨45525, by rfl⟩ : syracuseStep 485605 = 91051) (by norm_num)
theorem B256229 : Blo 167798 256229 := bbase (se 4 (by rfl) ⟨24021, by rfl⟩ : syracuseStep 256229 = 48043) (by norm_num)
theorem B190705 : Blo 167798 190705 := bbase (se 2 (by rfl) ⟨71514, by rfl⟩ : syracuseStep 190705 = 143029) (by norm_num)
theorem B256253 : Blo 167798 256253 := bbase (se 3 (by rfl) ⟨48047, by rfl⟩ : syracuseStep 256253 = 96095) (by norm_num)
theorem B289021 : Blo 167798 289021 := bbase (se 3 (by rfl) ⟨54191, by rfl⟩ : syracuseStep 289021 = 108383) (by norm_num)
theorem B190741 : Blo 167798 190741 := bbase (se 6 (by rfl) ⟨4470, by rfl⟩ : syracuseStep 190741 = 8941) (by norm_num)
theorem B256277 : Blo 167798 256277 := bbase (se 6 (by rfl) ⟨6006, by rfl⟩ : syracuseStep 256277 = 12013) (by norm_num)
theorem B256301 : Blo 167798 256301 := bbase (se 3 (by rfl) ⟨48056, by rfl⟩ : syracuseStep 256301 = 96113) (by norm_num)
theorem B190777 : Blo 167798 190777 := bbase (se 2 (by rfl) ⟨71541, by rfl⟩ : syracuseStep 190777 = 143083) (by norm_num)
theorem B256325 : Blo 167798 256325 := bbase (se 4 (by rfl) ⟨24030, by rfl⟩ : syracuseStep 256325 = 48061) (by norm_num)
theorem B321869 : Blo 167798 321869 := bbase (se 3 (by rfl) ⟨60350, by rfl⟩ : syracuseStep 321869 = 120701) (by norm_num)
theorem B289109 : Blo 167798 289109 := bbase (se 10 (by rfl) ⟨423, by rfl⟩ : syracuseStep 289109 = 847) (by norm_num)
theorem B190813 : Blo 167798 190813 := bbase (se 3 (by rfl) ⟨35777, by rfl⟩ : syracuseStep 190813 = 71555) (by norm_num)
theorem B256349 : Blo 167798 256349 := bbase (se 3 (by rfl) ⟨48065, by rfl⟩ : syracuseStep 256349 = 96131) (by norm_num)
theorem B256373 : Blo 167798 256373 := bbase (se 5 (by rfl) ⟨12017, by rfl⟩ : syracuseStep 256373 = 24035) (by norm_num)
theorem B190849 : Blo 167798 190849 := bbase (se 2 (by rfl) ⟨71568, by rfl⟩ : syracuseStep 190849 = 143137) (by norm_num)
theorem B256397 : Blo 167798 256397 := bbase (se 3 (by rfl) ⟨48074, by rfl⟩ : syracuseStep 256397 = 96149) (by norm_num)
theorem B289189 : Blo 167798 289189 := bbase (se 4 (by rfl) ⟨27111, by rfl⟩ : syracuseStep 289189 = 54223) (by norm_num)
theorem B190885 : Blo 167798 190885 := bbase (se 4 (by rfl) ⟨17895, by rfl⟩ : syracuseStep 190885 = 35791) (by norm_num)
theorem B256421 : Blo 167798 256421 := bbase (se 4 (by rfl) ⟨24039, by rfl⟩ : syracuseStep 256421 = 48079) (by norm_num)
theorem B256445 : Blo 167798 256445 := bbase (se 3 (by rfl) ⟨48083, by rfl⟩ : syracuseStep 256445 = 96167) (by norm_num)
theorem B616901 : Blo 167798 616901 := bbase (se 4 (by rfl) ⟨57834, by rfl⟩ : syracuseStep 616901 = 115669) (by norm_num)
theorem B190921 : Blo 167798 190921 := bbase (se 2 (by rfl) ⟨71595, by rfl⟩ : syracuseStep 190921 = 143191) (by norm_num)
theorem B256469 : Blo 167798 256469 := bbase (se 7 (by rfl) ⟨3005, by rfl⟩ : syracuseStep 256469 = 6011) (by norm_num)
theorem B289237 : Blo 167798 289237 := bbase (se 7 (by rfl) ⟨3389, by rfl⟩ : syracuseStep 289237 = 6779) (by norm_num)
theorem B190957 : Blo 167798 190957 := bbase (se 3 (by rfl) ⟨35804, by rfl⟩ : syracuseStep 190957 = 71609) (by norm_num)
theorem B256493 : Blo 167798 256493 := bbase (se 3 (by rfl) ⟨48092, by rfl⟩ : syracuseStep 256493 = 96185) (by norm_num)
theorem B256517 : Blo 167798 256517 := bbase (se 4 (by rfl) ⟨24048, by rfl⟩ : syracuseStep 256517 = 48097) (by norm_num)
theorem B190993 : Blo 167798 190993 := bbase (se 2 (by rfl) ⟨71622, by rfl⟩ : syracuseStep 190993 = 143245) (by norm_num)
theorem B256541 : Blo 167798 256541 := bbase (se 3 (by rfl) ⟨48101, by rfl⟩ : syracuseStep 256541 = 96203) (by norm_num)
theorem B289325 : Blo 167798 289325 := bbase (se 3 (by rfl) ⟨54248, by rfl⟩ : syracuseStep 289325 = 108497) (by norm_num)
theorem B191029 : Blo 167798 191029 := bbase (se 5 (by rfl) ⟨8954, by rfl⟩ : syracuseStep 191029 = 17909) (by norm_num)
theorem B256565 : Blo 167798 256565 := bbase (se 5 (by rfl) ⟨12026, by rfl⟩ : syracuseStep 256565 = 24053) (by norm_num)
theorem B256589 : Blo 167798 256589 := bbase (se 3 (by rfl) ⟨48110, by rfl⟩ : syracuseStep 256589 = 96221) (by norm_num)
theorem B191065 : Blo 167798 191065 := bbase (se 2 (by rfl) ⟨71649, by rfl⟩ : syracuseStep 191065 = 143299) (by norm_num)
theorem B682597 : Blo 167798 682597 := bbase (se 4 (by rfl) ⟨63993, by rfl⟩ : syracuseStep 682597 = 127987) (by norm_num)
theorem B256613 : Blo 167798 256613 := bbase (se 4 (by rfl) ⟨24057, by rfl⟩ : syracuseStep 256613 = 48115) (by norm_num)
theorem B322157 : Blo 167798 322157 := bbase (se 3 (by rfl) ⟨60404, by rfl⟩ : syracuseStep 322157 = 120809) (by norm_num)
theorem B191101 : Blo 167798 191101 := bbase (se 3 (by rfl) ⟨35831, by rfl⟩ : syracuseStep 191101 = 71663) (by norm_num)
theorem B256637 : Blo 167798 256637 := bbase (se 3 (by rfl) ⟨48119, by rfl⟩ : syracuseStep 256637 = 96239) (by norm_num)
theorem B256661 : Blo 167798 256661 := bbase (se 6 (by rfl) ⟨6015, by rfl⟩ : syracuseStep 256661 = 12031) (by norm_num)
theorem B191137 : Blo 167798 191137 := bbase (se 2 (by rfl) ⟨71676, by rfl⟩ : syracuseStep 191137 = 143353) (by norm_num)
theorem B387749 : Blo 167798 387749 := bbase (se 4 (by rfl) ⟨36351, by rfl⟩ : syracuseStep 387749 = 72703) (by norm_num)
theorem B256685 : Blo 167798 256685 := bbase (se 3 (by rfl) ⟨48128, by rfl⟩ : syracuseStep 256685 = 96257) (by norm_num)
theorem B289453 : Blo 167798 289453 := bbase (se 3 (by rfl) ⟨54272, by rfl⟩ : syracuseStep 289453 = 108545) (by norm_num)
theorem B191173 : Blo 167798 191173 := bbase (se 4 (by rfl) ⟨17922, by rfl⟩ : syracuseStep 191173 = 35845) (by norm_num)
theorem B256709 : Blo 167798 256709 := bbase (se 4 (by rfl) ⟨24066, by rfl⟩ : syracuseStep 256709 = 48133) (by norm_num)
theorem B256733 : Blo 167798 256733 := bbase (se 3 (by rfl) ⟨48137, by rfl⟩ : syracuseStep 256733 = 96275) (by norm_num)
theorem B191209 : Blo 167798 191209 := bbase (se 2 (by rfl) ⟨71703, by rfl⟩ : syracuseStep 191209 = 143407) (by norm_num)
theorem B879349 : Blo 167798 879349 := bbase (se 5 (by rfl) ⟨41219, by rfl⟩ : syracuseStep 879349 = 82439) (by norm_num)
theorem B256757 : Blo 167798 256757 := bbase (se 5 (by rfl) ⟨12035, by rfl⟩ : syracuseStep 256757 = 24071) (by norm_num)
theorem B322309 : Blo 167798 322309 := bbase (se 4 (by rfl) ⟨30216, by rfl⟩ : syracuseStep 322309 = 60433) (by norm_num)
theorem B289541 : Blo 167798 289541 := bbase (se 4 (by rfl) ⟨27144, by rfl⟩ : syracuseStep 289541 = 54289) (by norm_num)
theorem B191245 : Blo 167798 191245 := bbase (se 3 (by rfl) ⟨35858, by rfl⟩ : syracuseStep 191245 = 71717) (by norm_num)
theorem B256781 : Blo 167798 256781 := bbase (se 3 (by rfl) ⟨48146, by rfl⟩ : syracuseStep 256781 = 96293) (by norm_num)
theorem B256805 : Blo 167798 256805 := bbase (se 4 (by rfl) ⟨24075, by rfl⟩ : syracuseStep 256805 = 48151) (by norm_num)
theorem B191281 : Blo 167798 191281 := bbase (se 2 (by rfl) ⟨71730, by rfl⟩ : syracuseStep 191281 = 143461) (by norm_num)
theorem B256829 : Blo 167798 256829 := bbase (se 3 (by rfl) ⟨48155, by rfl⟩ : syracuseStep 256829 = 96311) (by norm_num)
theorem B191317 : Blo 167798 191317 := bbase (se 9 (by rfl) ⟨560, by rfl⟩ : syracuseStep 191317 = 1121) (by norm_num)
theorem B256853 : Blo 167798 256853 := bbase (se 9 (by rfl) ⟨752, by rfl⟩ : syracuseStep 256853 = 1505) (by norm_num)
theorem B256877 : Blo 167798 256877 := bbase (se 3 (by rfl) ⟨48164, by rfl⟩ : syracuseStep 256877 = 96329) (by norm_num)
theorem B191353 : Blo 167798 191353 := bbase (se 2 (by rfl) ⟨71757, by rfl⟩ : syracuseStep 191353 = 143515) (by norm_num)
theorem B256901 : Blo 167798 256901 := bbase (se 4 (by rfl) ⟨24084, by rfl⟩ : syracuseStep 256901 = 48169) (by norm_num)
theorem B289669 : Blo 167798 289669 := bbase (se 4 (by rfl) ⟨27156, by rfl⟩ : syracuseStep 289669 = 54313) (by norm_num)
theorem B191389 : Blo 167798 191389 := bbase (se 3 (by rfl) ⟨35885, by rfl⟩ : syracuseStep 191389 = 71771) (by norm_num)
theorem B256925 : Blo 167798 256925 := bbase (se 3 (by rfl) ⟨48173, by rfl⟩ : syracuseStep 256925 = 96347) (by norm_num)
theorem B256949 : Blo 167798 256949 := bbase (se 5 (by rfl) ⟨12044, by rfl⟩ : syracuseStep 256949 = 24089) (by norm_num)
theorem B191425 : Blo 167798 191425 := bbase (se 2 (by rfl) ⟨71784, by rfl⟩ : syracuseStep 191425 = 143569) (by norm_num)
theorem B256973 : Blo 167798 256973 := bbase (se 3 (by rfl) ⟨48182, by rfl⟩ : syracuseStep 256973 = 96365) (by norm_num)
theorem B289757 : Blo 167798 289757 := bbase (se 3 (by rfl) ⟨54329, by rfl⟩ : syracuseStep 289757 = 108659) (by norm_num)
theorem B191461 : Blo 167798 191461 := bbase (se 4 (by rfl) ⟨17949, by rfl⟩ : syracuseStep 191461 = 35899) (by norm_num)
theorem B256997 : Blo 167798 256997 := bbase (se 4 (by rfl) ⟨24093, by rfl⟩ : syracuseStep 256997 = 48187) (by norm_num)
theorem B257021 : Blo 167798 257021 := bbase (se 3 (by rfl) ⟨48191, by rfl⟩ : syracuseStep 257021 = 96383) (by norm_num)
theorem B191497 : Blo 167798 191497 := bbase (se 2 (by rfl) ⟨71811, by rfl⟩ : syracuseStep 191497 = 143623) (by norm_num)
theorem B257045 : Blo 167798 257045 := bbase (se 6 (by rfl) ⟨6024, by rfl⟩ : syracuseStep 257045 = 12049) (by norm_num)
theorem B191533 : Blo 167798 191533 := bbase (se 3 (by rfl) ⟨35912, by rfl⟩ : syracuseStep 191533 = 71825) (by norm_num)
theorem B257069 : Blo 167798 257069 := bbase (se 3 (by rfl) ⟨48200, by rfl⟩ : syracuseStep 257069 = 96401) (by norm_num)
theorem B322613 : Blo 167798 322613 := bbase (se 5 (by rfl) ⟨15122, by rfl⟩ : syracuseStep 322613 = 30245) (by norm_num)
theorem B257093 : Blo 167798 257093 := bbase (se 4 (by rfl) ⟨24102, by rfl⟩ : syracuseStep 257093 = 48205) (by norm_num)
theorem B191569 : Blo 167798 191569 := bbase (se 2 (by rfl) ⟨71838, by rfl⟩ : syracuseStep 191569 = 143677) (by norm_num)
theorem B257117 : Blo 167798 257117 := bbase (se 3 (by rfl) ⟨48209, by rfl⟩ : syracuseStep 257117 = 96419) (by norm_num)
theorem B289885 : Blo 167798 289885 := bbase (se 3 (by rfl) ⟨54353, by rfl⟩ : syracuseStep 289885 = 108707) (by norm_num)
theorem B191605 : Blo 167798 191605 := bbase (se 5 (by rfl) ⟨8981, by rfl⟩ : syracuseStep 191605 = 17963) (by norm_num)
theorem B257141 : Blo 167798 257141 := bbase (se 5 (by rfl) ⟨12053, by rfl⟩ : syracuseStep 257141 = 24107) (by norm_num)
theorem B257165 : Blo 167798 257165 := bbase (se 3 (by rfl) ⟨48218, by rfl⟩ : syracuseStep 257165 = 96437) (by norm_num)
theorem B650389 : Blo 167798 650389 := bbase (se 6 (by rfl) ⟨15243, by rfl⟩ : syracuseStep 650389 = 30487) (by norm_num)
theorem B191641 : Blo 167798 191641 := bbase (se 2 (by rfl) ⟨71865, by rfl⟩ : syracuseStep 191641 = 143731) (by norm_num)
theorem B257189 : Blo 167798 257189 := bbase (se 4 (by rfl) ⟨24111, by rfl⟩ : syracuseStep 257189 = 48223) (by norm_num)
theorem B191677 : Blo 167798 191677 := bbase (se 3 (by rfl) ⟨35939, by rfl⟩ : syracuseStep 191677 = 71879) (by norm_num)
theorem B257213 : Blo 167798 257213 := bbase (se 3 (by rfl) ⟨48227, by rfl⟩ : syracuseStep 257213 = 96455) (by norm_num)
theorem B257237 : Blo 167798 257237 := bbase (se 7 (by rfl) ⟨3014, by rfl⟩ : syracuseStep 257237 = 6029) (by norm_num)
theorem B191713 : Blo 167798 191713 := bbase (se 2 (by rfl) ⟨71892, by rfl⟩ : syracuseStep 191713 = 143785) (by norm_num)
theorem B257261 : Blo 167798 257261 := bbase (se 3 (by rfl) ⟨48236, by rfl⟩ : syracuseStep 257261 = 96473) (by norm_num)
theorem B191749 : Blo 167798 191749 := bbase (se 4 (by rfl) ⟨17976, by rfl⟩ : syracuseStep 191749 = 35953) (by norm_num)
theorem B257285 : Blo 167798 257285 := bbase (se 4 (by rfl) ⟨24120, by rfl⟩ : syracuseStep 257285 = 48241) (by norm_num)
theorem B257309 : Blo 167798 257309 := bbase (se 3 (by rfl) ⟨48245, by rfl⟩ : syracuseStep 257309 = 96491) (by norm_num)
theorem B191785 : Blo 167798 191785 := bbase (se 2 (by rfl) ⟨71919, by rfl⟩ : syracuseStep 191785 = 143839) (by norm_num)
theorem B257333 : Blo 167798 257333 := bbase (se 5 (by rfl) ⟨12062, by rfl⟩ : syracuseStep 257333 = 24125) (by norm_num)
theorem B191821 : Blo 167798 191821 := bbase (se 3 (by rfl) ⟨35966, by rfl⟩ : syracuseStep 191821 = 71933) (by norm_num)
theorem B257357 : Blo 167798 257357 := bbase (se 3 (by rfl) ⟨48254, by rfl⟩ : syracuseStep 257357 = 96509) (by norm_num)
theorem B617813 : Blo 167798 617813 := bbase (se 11 (by rfl) ⟨452, by rfl⟩ : syracuseStep 617813 = 905) (by norm_num)
theorem B781669 : Blo 167798 781669 := bbase (se 4 (by rfl) ⟨73281, by rfl⟩ : syracuseStep 781669 = 146563) (by norm_num)
theorem B257381 : Blo 167798 257381 := bbase (se 4 (by rfl) ⟨24129, by rfl⟩ : syracuseStep 257381 = 48259) (by norm_num)
theorem B191857 : Blo 167798 191857 := bbase (se 2 (by rfl) ⟨71946, by rfl⟩ : syracuseStep 191857 = 143893) (by norm_num)
theorem B1076597 : Blo 167798 1076597 := bbase (se 5 (by rfl) ⟨50465, by rfl⟩ : syracuseStep 1076597 = 100931) (by norm_num)
theorem B257405 : Blo 167798 257405 := bbase (se 3 (by rfl) ⟨48263, by rfl⟩ : syracuseStep 257405 = 96527) (by norm_num)
theorem B191893 : Blo 167798 191893 := bbase (se 6 (by rfl) ⟨4497, by rfl⟩ : syracuseStep 191893 = 8995) (by norm_num)
theorem B257429 : Blo 167798 257429 := bbase (se 6 (by rfl) ⟨6033, by rfl⟩ : syracuseStep 257429 = 12067) (by norm_num)
theorem B257453 : Blo 167798 257453 := bbase (se 3 (by rfl) ⟨48272, by rfl⟩ : syracuseStep 257453 = 96545) (by norm_num)
theorem B191929 : Blo 167798 191929 := bbase (se 2 (by rfl) ⟨71973, by rfl⟩ : syracuseStep 191929 = 143947) (by norm_num)
theorem B650693 : Blo 167798 650693 := bbase (se 4 (by rfl) ⟨61002, by rfl⟩ : syracuseStep 650693 = 122005) (by norm_num)
theorem B257477 : Blo 167798 257477 := bbase (se 4 (by rfl) ⟨24138, by rfl⟩ : syracuseStep 257477 = 48277) (by norm_num)
theorem B191965 : Blo 167798 191965 := bbase (se 3 (by rfl) ⟨35993, by rfl⟩ : syracuseStep 191965 = 71987) (by norm_num)
theorem B257501 : Blo 167798 257501 := bbase (se 3 (by rfl) ⟨48281, by rfl⟩ : syracuseStep 257501 = 96563) (by norm_num)
theorem B257525 : Blo 167798 257525 := bbase (se 5 (by rfl) ⟨12071, by rfl⟩ : syracuseStep 257525 = 24143) (by norm_num)
theorem B192001 : Blo 167798 192001 := bbase (se 2 (by rfl) ⟨72000, by rfl⟩ : syracuseStep 192001 = 144001) (by norm_num)
theorem B257549 : Blo 167798 257549 := bbase (se 3 (by rfl) ⟨48290, by rfl⟩ : syracuseStep 257549 = 96581) (by norm_num)
theorem B192037 : Blo 167798 192037 := bbase (se 4 (by rfl) ⟨18003, by rfl⟩ : syracuseStep 192037 = 36007) (by norm_num)
theorem B257573 : Blo 167798 257573 := bbase (se 4 (by rfl) ⟨24147, by rfl⟩ : syracuseStep 257573 = 48295) (by norm_num)
theorem B257597 : Blo 167798 257597 := bbase (se 3 (by rfl) ⟨48299, by rfl⟩ : syracuseStep 257597 = 96599) (by norm_num)
theorem B192073 : Blo 167798 192073 := bbase (se 2 (by rfl) ⟨72027, by rfl⟩ : syracuseStep 192073 = 144055) (by norm_num)
theorem B257621 : Blo 167798 257621 := bbase (se 8 (by rfl) ⟨1509, by rfl⟩ : syracuseStep 257621 = 3019) (by norm_num)
theorem B192109 : Blo 167798 192109 := bbase (se 3 (by rfl) ⟨36020, by rfl⟩ : syracuseStep 192109 = 72041) (by norm_num)
theorem B257645 : Blo 167798 257645 := bbase (se 3 (by rfl) ⟨48308, by rfl⟩ : syracuseStep 257645 = 96617) (by norm_num)
theorem B257669 : Blo 167798 257669 := bbase (se 4 (by rfl) ⟨24156, by rfl⟩ : syracuseStep 257669 = 48313) (by norm_num)
theorem B192145 : Blo 167798 192145 := bbase (se 2 (by rfl) ⟨72054, by rfl⟩ : syracuseStep 192145 = 144109) (by norm_num)
theorem B257693 : Blo 167798 257693 := bbase (se 3 (by rfl) ⟨48317, by rfl⟩ : syracuseStep 257693 = 96635) (by norm_num)
theorem B192181 : Blo 167798 192181 := bbase (se 5 (by rfl) ⟨9008, by rfl⟩ : syracuseStep 192181 = 18017) (by norm_num)
theorem B487109 : Blo 167798 487109 := bbase (se 4 (by rfl) ⟨45666, by rfl⟩ : syracuseStep 487109 = 91333) (by norm_num)
theorem B585413 : Blo 167798 585413 := bbase (se 4 (by rfl) ⟨54882, by rfl⟩ : syracuseStep 585413 = 109765) (by norm_num)
theorem B192217 : Blo 167798 192217 := bbase (se 2 (by rfl) ⟨72081, by rfl⟩ : syracuseStep 192217 = 144163) (by norm_num)
theorem B683765 : Blo 167798 683765 := bbase (se 5 (by rfl) ⟨32051, by rfl⟩ : syracuseStep 683765 = 64103) (by norm_num)
theorem B192253 : Blo 167798 192253 := bbase (se 3 (by rfl) ⟨36047, by rfl⟩ : syracuseStep 192253 = 72095) (by norm_num)
theorem B192289 : Blo 167798 192289 := bbase (se 2 (by rfl) ⟨72108, by rfl⟩ : syracuseStep 192289 = 144217) (by norm_num)
theorem B323365 : Blo 167798 323365 := bbase (se 4 (by rfl) ⟨30315, by rfl⟩ : syracuseStep 323365 = 60631) (by norm_num)
theorem B192325 : Blo 167798 192325 := bbase (se 4 (by rfl) ⟨18030, by rfl⟩ : syracuseStep 192325 = 36061) (by norm_num)
theorem B192361 : Blo 167798 192361 := bbase (se 2 (by rfl) ⟨72135, by rfl⟩ : syracuseStep 192361 = 144271) (by norm_num)
theorem B192397 : Blo 167798 192397 := bbase (se 3 (by rfl) ⟨36074, by rfl⟩ : syracuseStep 192397 = 72149) (by norm_num)
theorem B192433 : Blo 167798 192433 := bbase (se 2 (by rfl) ⟨72162, by rfl⟩ : syracuseStep 192433 = 144325) (by norm_num)
theorem B323509 : Blo 167798 323509 := bbase (se 5 (by rfl) ⟨15164, by rfl⟩ : syracuseStep 323509 = 30329) (by norm_num)
theorem B2060245 : Blo 167798 2060245 := bbase (se 7 (by rfl) ⟨24143, by rfl⟩ : syracuseStep 2060245 = 48287) (by norm_num)
theorem B192469 : Blo 167798 192469 := bbase (se 7 (by rfl) ⟨2255, by rfl⟩ : syracuseStep 192469 = 4511) (by norm_num)
theorem B716789 : Blo 167798 716789 := bbase (se 5 (by rfl) ⟨33599, by rfl⟩ : syracuseStep 716789 = 67199) (by norm_num)
theorem B192505 : Blo 167798 192505 := bbase (se 2 (by rfl) ⟨72189, by rfl⟩ : syracuseStep 192505 = 144379) (by norm_num)
theorem B192541 : Blo 167798 192541 := bbase (se 3 (by rfl) ⟨36101, by rfl⟩ : syracuseStep 192541 = 72203) (by norm_num)
theorem B454709 : Blo 167798 454709 := bbase (se 5 (by rfl) ⟨21314, by rfl⟩ : syracuseStep 454709 = 42629) (by norm_num)
theorem B1437749 : Blo 167798 1437749 := bbase (se 5 (by rfl) ⟨67394, by rfl⟩ : syracuseStep 1437749 = 134789) (by norm_num)
theorem B192577 : Blo 167798 192577 := bbase (se 2 (by rfl) ⟨72216, by rfl⟩ : syracuseStep 192577 = 144433) (by norm_num)
theorem B323669 : Blo 167798 323669 := bbase (se 8 (by rfl) ⟨1896, by rfl⟩ : syracuseStep 323669 = 3793) (by norm_num)
theorem B192601 : Blo 167798 192601 := bbase (se 2 (by rfl) ⟨72225, by rfl⟩ : syracuseStep 192601 = 144451) (by norm_num)
theorem B192613 : Blo 167798 192613 := bbase (se 4 (by rfl) ⟨18057, by rfl⟩ : syracuseStep 192613 = 36115) (by norm_num)
theorem B192649 : Blo 167798 192649 := bbase (se 2 (by rfl) ⟨72243, by rfl⟩ : syracuseStep 192649 = 144487) (by norm_num)
theorem B192685 : Blo 167798 192685 := bbase (se 3 (by rfl) ⟨36128, by rfl⟩ : syracuseStep 192685 = 72257) (by norm_num)
theorem B913589 : Blo 167798 913589 := bbase (se 5 (by rfl) ⟨42824, by rfl⟩ : syracuseStep 913589 = 85649) (by norm_num)
theorem B192721 : Blo 167798 192721 := bbase (se 2 (by rfl) ⟨72270, by rfl⟩ : syracuseStep 192721 = 144541) (by norm_num)
theorem B323813 : Blo 167798 323813 := bbase (se 4 (by rfl) ⟨30357, by rfl⟩ : syracuseStep 323813 = 60715) (by norm_num)
theorem B192757 : Blo 167798 192757 := bbase (se 5 (by rfl) ⟨9035, by rfl⟩ : syracuseStep 192757 = 18071) (by norm_num)
theorem B192793 : Blo 167798 192793 := bbase (se 2 (by rfl) ⟨72297, by rfl⟩ : syracuseStep 192793 = 144595) (by norm_num)
theorem B520501 : Blo 167798 520501 := bbase (se 5 (by rfl) ⟨24398, by rfl⟩ : syracuseStep 520501 = 48797) (by norm_num)
theorem B192829 : Blo 167798 192829 := bbase (se 3 (by rfl) ⟨36155, by rfl⟩ : syracuseStep 192829 = 72311) (by norm_num)
theorem B192865 : Blo 167798 192865 := bbase (se 2 (by rfl) ⟨72324, by rfl⟩ : syracuseStep 192865 = 144649) (by norm_num)
theorem B291173 : Blo 167798 291173 := bbase (se 4 (by rfl) ⟨27297, by rfl⟩ : syracuseStep 291173 = 54595) (by norm_num)
theorem B192901 : Blo 167798 192901 := bbase (se 4 (by rfl) ⟨18084, by rfl⟩ : syracuseStep 192901 = 36169) (by norm_num)
theorem B192937 : Blo 167798 192937 := bbase (se 2 (by rfl) ⟨72351, by rfl⟩ : syracuseStep 192937 = 144703) (by norm_num)
theorem B192973 : Blo 167798 192973 := bbase (se 3 (by rfl) ⟨36182, by rfl⟩ : syracuseStep 192973 = 72365) (by norm_num)
theorem B193009 : Blo 167798 193009 := bbase (se 2 (by rfl) ⟨72378, by rfl⟩ : syracuseStep 193009 = 144757) (by norm_num)
theorem B324101 : Blo 167798 324101 := bbase (se 4 (by rfl) ⟨30384, by rfl⟩ : syracuseStep 324101 = 60769) (by norm_num)
theorem B193045 : Blo 167798 193045 := bbase (se 6 (by rfl) ⟨4524, by rfl⟩ : syracuseStep 193045 = 9049) (by norm_num)
theorem B193081 : Blo 167798 193081 := bbase (se 2 (by rfl) ⟨72405, by rfl⟩ : syracuseStep 193081 = 144811) (by norm_num)
theorem B193117 : Blo 167798 193117 := bbase (se 3 (by rfl) ⟨36209, by rfl⟩ : syracuseStep 193117 = 72419) (by norm_num)
theorem B193153 : Blo 167798 193153 := bbase (se 2 (by rfl) ⟨72432, by rfl⟩ : syracuseStep 193153 = 144865) (by norm_num)
theorem B324253 : Blo 167798 324253 := bbase (se 3 (by rfl) ⟨60797, by rfl⟩ : syracuseStep 324253 = 121595) (by norm_num)
theorem B193189 : Blo 167798 193189 := bbase (se 4 (by rfl) ⟨18111, by rfl⟩ : syracuseStep 193189 = 36223) (by norm_num)
theorem B193225 : Blo 167798 193225 := bbase (se 2 (by rfl) ⟨72459, by rfl⟩ : syracuseStep 193225 = 144919) (by norm_num)
theorem B193261 : Blo 167798 193261 := bbase (se 3 (by rfl) ⟨36236, by rfl⟩ : syracuseStep 193261 = 72473) (by norm_num)
theorem B193313 : Blo 167798 193313 := bbase (se 2 (by rfl) ⟨72492, by rfl⟩ : syracuseStep 193313 = 144985) (by norm_num)
theorem B324461 : Blo 167798 324461 := bbase (se 3 (by rfl) ⟨60836, by rfl⟩ : syracuseStep 324461 = 121673) (by norm_num)
theorem B324557 : Blo 167798 324557 := bbase (se 3 (by rfl) ⟨60854, by rfl⟩ : syracuseStep 324557 = 121709) (by norm_num)
theorem B717781 : Blo 167798 717781 := bbase (se 7 (by rfl) ⟨8411, by rfl⟩ : syracuseStep 717781 = 16823) (by norm_num)
theorem B488693 : Blo 167798 488693 := bbase (se 5 (by rfl) ⟨22907, by rfl⟩ : syracuseStep 488693 = 45815) (by norm_num)
theorem B193897 : Blo 167798 193897 := bbase (se 2 (by rfl) ⟨72711, by rfl⟩ : syracuseStep 193897 = 145423) (by norm_num)
theorem B193961 : Blo 167798 193961 := bbase (se 2 (by rfl) ⟨72735, by rfl⟩ : syracuseStep 193961 = 145471) (by norm_num)
theorem B292405 : Blo 167798 292405 := bbase (se 5 (by rfl) ⟨13706, by rfl⟩ : syracuseStep 292405 = 27413) (by norm_num)
theorem B1111733 : Blo 167798 1111733 := bbase (se 5 (by rfl) ⟨52112, by rfl⟩ : syracuseStep 1111733 = 104225) (by norm_num)
theorem B325309 : Blo 167798 325309 := bbase (se 3 (by rfl) ⟨60995, by rfl⟩ : syracuseStep 325309 = 121991) (by norm_num)
theorem B325453 : Blo 167798 325453 := bbase (se 3 (by rfl) ⟨61022, by rfl⟩ : syracuseStep 325453 = 122045) (by norm_num)
theorem B194389 : Blo 167798 194389 := bbase (se 9 (by rfl) ⟨569, by rfl⟩ : syracuseStep 194389 = 1139) (by norm_num)
theorem B325613 : Blo 167798 325613 := bbase (se 3 (by rfl) ⟨61052, by rfl⟩ : syracuseStep 325613 = 122105) (by norm_num)
theorem B292925 : Blo 167798 292925 := bbase (se 3 (by rfl) ⟨54923, by rfl⟩ : syracuseStep 292925 = 109847) (by norm_num)
theorem B325757 : Blo 167798 325757 := bbase (se 3 (by rfl) ⟨61079, by rfl⟩ : syracuseStep 325757 = 122159) (by norm_num)
theorem B358661 : Blo 167798 358661 := bbase (se 4 (by rfl) ⟨33624, by rfl⟩ : syracuseStep 358661 = 67249) (by norm_num)
theorem B260405 : Blo 167798 260405 := bbase (se 5 (by rfl) ⟨12206, by rfl⟩ : syracuseStep 260405 = 24413) (by norm_num)
theorem B227701 : Blo 167798 227701 := bbase (se 5 (by rfl) ⟨10673, by rfl⟩ : syracuseStep 227701 = 21347) (by norm_num)
theorem B358805 : Blo 167798 358805 := bbase (se 6 (by rfl) ⟨8409, by rfl⟩ : syracuseStep 358805 = 16819) (by norm_num)
theorem B326045 : Blo 167798 326045 := bbase (se 3 (by rfl) ⟨61133, by rfl⟩ : syracuseStep 326045 = 122267) (by norm_num)
theorem B260597 : Blo 167798 260597 := bbase (se 5 (by rfl) ⟨12215, by rfl⟩ : syracuseStep 260597 = 24431) (by norm_num)
theorem B2423317 : Blo 167798 2423317 := bbase (se 6 (by rfl) ⟨56796, by rfl⟩ : syracuseStep 2423317 = 113593) (by norm_num)
theorem B260693 : Blo 167798 260693 := bbase (se 8 (by rfl) ⟨1527, by rfl⟩ : syracuseStep 260693 = 3055) (by norm_num)
theorem B850661 : Blo 167798 850661 := bbase (se 4 (by rfl) ⟨79749, by rfl⟩ : syracuseStep 850661 = 159499) (by norm_num)
theorem B1833749 : Blo 167798 1833749 := bbase (se 6 (by rfl) ⟨42978, by rfl⟩ : syracuseStep 1833749 = 85957) (by norm_num)
theorem B228181 : Blo 167798 228181 := bbase (se 9 (by rfl) ⟨668, by rfl⟩ : syracuseStep 228181 = 1337) (by norm_num)
theorem B261029 : Blo 167798 261029 := bbase (se 4 (by rfl) ⟨24471, by rfl⟩ : syracuseStep 261029 = 48943) (by norm_num)
theorem B424885 : Blo 167798 424885 := bbase (se 5 (by rfl) ⟨19916, by rfl⟩ : syracuseStep 424885 = 39833) (by norm_num)
theorem B195593 : Blo 167798 195593 := bbase (se 2 (by rfl) ⟨73347, by rfl⟩ : syracuseStep 195593 = 146695) (by norm_num)
theorem B326669 : Blo 167798 326669 := bbase (se 3 (by rfl) ⟨61250, by rfl⟩ : syracuseStep 326669 = 122501) (by norm_num)
theorem B424997 : Blo 167798 424997 := bbase (se 4 (by rfl) ⟨39843, by rfl⟩ : syracuseStep 424997 = 79687) (by norm_num)
theorem B359549 : Blo 167798 359549 := bbase (se 3 (by rfl) ⟨67415, by rfl⟩ : syracuseStep 359549 = 134831) (by norm_num)
theorem B425189 : Blo 167798 425189 := bbase (se 4 (by rfl) ⟨39861, by rfl⟩ : syracuseStep 425189 = 79723) (by norm_num)
theorem B2227733 : Blo 167798 2227733 := bbase (se 6 (by rfl) ⟨52212, by rfl⟩ : syracuseStep 2227733 = 104425) (by norm_num)
theorem B425533 : Blo 167798 425533 := bbase (se 3 (by rfl) ⟨79787, by rfl⟩ : syracuseStep 425533 = 159575) (by norm_num)
theorem B1638005 : Blo 167798 1638005 := bbase (se 5 (by rfl) ⟨76781, by rfl⟩ : syracuseStep 1638005 = 153563) (by norm_num)
theorem B425645 : Blo 167798 425645 := bbase (se 3 (by rfl) ⟨79808, by rfl⟩ : syracuseStep 425645 = 159617) (by norm_num)
theorem B425837 : Blo 167798 425837 := bbase (se 3 (by rfl) ⟨79844, by rfl⟩ : syracuseStep 425837 = 159689) (by norm_num)
theorem B360301 : Blo 167798 360301 := bbase (se 3 (by rfl) ⟨67556, by rfl⟩ : syracuseStep 360301 = 135113) (by norm_num)
theorem B556949 : Blo 167798 556949 := bbase (se 6 (by rfl) ⟨13053, by rfl⟩ : syracuseStep 556949 = 26107) (by norm_num)
theorem B851957 : Blo 167798 851957 := bbase (se 5 (by rfl) ⟨39935, by rfl⟩ : syracuseStep 851957 = 79871) (by norm_num)
theorem B360445 : Blo 167798 360445 := bbase (se 3 (by rfl) ⟨67583, by rfl⟩ : syracuseStep 360445 = 135167) (by norm_num)
theorem B426019 : Blo 167798 426019 := bstep (se 1 (by rfl) ⟨319514, by rfl⟩ : syracuseStep 426019 = 639029) B639029
theorem B426161 : Blo 167798 426161 := bstep (se 2 (by rfl) ⟨159810, by rfl⟩ : syracuseStep 426161 = 319621) B319621
theorem B1474757 : Blo 167798 1474757 := bstep (se 4 (by rfl) ⟨138258, by rfl⟩ : syracuseStep 1474757 = 276517) B276517
theorem B1278179 : Blo 167798 1278179 := bstep (se 1 (by rfl) ⟨958634, by rfl⟩ : syracuseStep 1278179 = 1917269) B1917269
theorem B229825 : Blo 167798 229825 := bstep (se 2 (by rfl) ⟨86184, by rfl⟩ : syracuseStep 229825 = 172369) B172369
theorem B2163185 : Blo 167798 2163185 := bstep (se 2 (by rfl) ⟨811194, by rfl⟩ : syracuseStep 2163185 = 1622389) B1622389
theorem B361265 : Blo 167798 361265 := bstep (se 2 (by rfl) ⟨135474, by rfl⟩ : syracuseStep 361265 = 270949) B270949
theorem B1573829 : Blo 167798 1573829 := bstep (se 4 (by rfl) ⟨147546, by rfl⟩ : syracuseStep 1573829 = 295093) B295093
theorem B1541105 : Blo 167798 1541105 := bstep (se 2 (by rfl) ⟨577914, by rfl⟩ : syracuseStep 1541105 = 1155829) B1155829
theorem B4949045 : Blo 167798 4949045 := bstep (se 5 (by rfl) ⟨231986, by rfl⟩ : syracuseStep 4949045 = 463973) B463973
theorem B853091 : Blo 167798 853091 := bstep (se 1 (by rfl) ⟨639818, by rfl⟩ : syracuseStep 853091 = 1279637) B1279637
theorem B427153 : Blo 167798 427153 := bstep (se 2 (by rfl) ⟨160182, by rfl⟩ : syracuseStep 427153 = 320365) B320365
theorem B722189 : Blo 167798 722189 := bstep (se 3 (by rfl) ⟨135410, by rfl⟩ : syracuseStep 722189 = 270821) B270821
theorem B427427 : Blo 167798 427427 := bstep (se 1 (by rfl) ⟨320570, by rfl⟩ : syracuseStep 427427 = 641141) B641141
theorem B427619 : Blo 167798 427619 := bstep (se 1 (by rfl) ⟨320714, by rfl⟩ : syracuseStep 427619 = 641429) B641429
theorem B853901 : Blo 167798 853901 := bstep (se 3 (by rfl) ⟨160106, by rfl⟩ : syracuseStep 853901 = 320213) B320213
theorem B460817 : Blo 167798 460817 := bstep (se 2 (by rfl) ⟨172806, by rfl⟩ : syracuseStep 460817 = 345613) B345613
theorem B526417 : Blo 167798 526417 := bstep (se 2 (by rfl) ⟨197406, by rfl⟩ : syracuseStep 526417 = 394813) B394813
theorem B1378403 : Blo 167798 1378403 := bstep (se 1 (by rfl) ⟨1033802, by rfl⟩ : syracuseStep 1378403 = 2067605) B2067605
theorem B1542341 : Blo 167798 1542341 := bstep (se 4 (by rfl) ⟨144594, by rfl⟩ : syracuseStep 1542341 = 289189) B289189
theorem B461315 : Blo 167798 461315 := bstep (se 1 (by rfl) ⟨345986, by rfl⟩ : syracuseStep 461315 = 691973) B691973
theorem B428561 : Blo 167798 428561 := bstep (se 2 (by rfl) ⟨160710, by rfl⟩ : syracuseStep 428561 = 321421) B321421
theorem B428611 : Blo 167798 428611 := bstep (se 1 (by rfl) ⟨321458, by rfl⟩ : syracuseStep 428611 = 642917) B642917
theorem B428753 : Blo 167798 428753 := bstep (se 2 (by rfl) ⟨160782, by rfl⟩ : syracuseStep 428753 = 321565) B321565
theorem B723761 : Blo 167798 723761 := bstep (se 2 (by rfl) ⟨271410, by rfl⟩ : syracuseStep 723761 = 542821) B542821
theorem B1084387 : Blo 167798 1084387 := bstep (se 1 (by rfl) ⟨813290, by rfl⟩ : syracuseStep 1084387 = 1626581) B1626581
theorem B429745 : Blo 167798 429745 := bstep (se 2 (by rfl) ⟨161154, by rfl⟩ : syracuseStep 429745 = 322309) B322309
theorem B2100977 : Blo 167798 2100977 := bstep (se 2 (by rfl) ⟨787866, by rfl⟩ : syracuseStep 2100977 = 1575733) B1575733
theorem B167811 : Blo 167798 167811 := bstep (se 1 (by rfl) ⟨125858, by rfl⟩ : syracuseStep 167811 = 251717) B251717
theorem B167827 : Blo 167798 167827 := bstep (se 1 (by rfl) ⟨125870, by rfl⟩ : syracuseStep 167827 = 251741) B251741
theorem B167843 : Blo 167798 167843 := bstep (se 1 (by rfl) ⟨125882, by rfl⟩ : syracuseStep 167843 = 251765) B251765
theorem B167859 : Blo 167798 167859 := bstep (se 1 (by rfl) ⟨125894, by rfl⟩ : syracuseStep 167859 = 251789) B251789
theorem B167875 : Blo 167798 167875 := bstep (se 1 (by rfl) ⟨125906, by rfl⟩ : syracuseStep 167875 = 251813) B251813
theorem B430019 : Blo 167798 430019 := bstep (se 1 (by rfl) ⟨322514, by rfl⟩ : syracuseStep 430019 = 645029) B645029
theorem B167891 : Blo 167798 167891 := bstep (se 1 (by rfl) ⟨125918, by rfl⟩ : syracuseStep 167891 = 251837) B251837
theorem B167907 : Blo 167798 167907 := bstep (se 1 (by rfl) ⟨125930, by rfl⟩ : syracuseStep 167907 = 251861) B251861
theorem B167923 : Blo 167798 167923 := bstep (se 1 (by rfl) ⟨125942, by rfl⟩ : syracuseStep 167923 = 251885) B251885
theorem B167939 : Blo 167798 167939 := bstep (se 1 (by rfl) ⟨125954, by rfl⟩ : syracuseStep 167939 = 251909) B251909
theorem B167955 : Blo 167798 167955 := bstep (se 1 (by rfl) ⟨125966, by rfl⟩ : syracuseStep 167955 = 251933) B251933
theorem B167971 : Blo 167798 167971 := bstep (se 1 (by rfl) ⟨125978, by rfl⟩ : syracuseStep 167971 = 251957) B251957
theorem B167987 : Blo 167798 167987 := bstep (se 1 (by rfl) ⟨125990, by rfl⟩ : syracuseStep 167987 = 251981) B251981
theorem B168003 : Blo 167798 168003 := bstep (se 1 (by rfl) ⟨126002, by rfl⟩ : syracuseStep 168003 = 252005) B252005
theorem B168019 : Blo 167798 168019 := bstep (se 1 (by rfl) ⟨126014, by rfl⟩ : syracuseStep 168019 = 252029) B252029
theorem B168035 : Blo 167798 168035 := bstep (se 1 (by rfl) ⟨126026, by rfl⟩ : syracuseStep 168035 = 252053) B252053
theorem B168051 : Blo 167798 168051 := bstep (se 1 (by rfl) ⟨126038, by rfl⟩ : syracuseStep 168051 = 252077) B252077
theorem B168067 : Blo 167798 168067 := bstep (se 1 (by rfl) ⟨126050, by rfl⟩ : syracuseStep 168067 = 252101) B252101
theorem B430211 : Blo 167798 430211 := bstep (se 1 (by rfl) ⟨322658, by rfl⟩ : syracuseStep 430211 = 645317) B645317
theorem B364675 : Blo 167798 364675 := bstep (se 1 (by rfl) ⟨273506, by rfl⟩ : syracuseStep 364675 = 547013) B547013
theorem B168083 : Blo 167798 168083 := bstep (se 1 (by rfl) ⟨126062, by rfl⟩ : syracuseStep 168083 = 252125) B252125
theorem B168099 : Blo 167798 168099 := bstep (se 1 (by rfl) ⟨126074, by rfl⟩ : syracuseStep 168099 = 252149) B252149
theorem B168115 : Blo 167798 168115 := bstep (se 1 (by rfl) ⟨126086, by rfl⟩ : syracuseStep 168115 = 252173) B252173
theorem B168131 : Blo 167798 168131 := bstep (se 1 (by rfl) ⟨126098, by rfl⟩ : syracuseStep 168131 = 252197) B252197
theorem B168147 : Blo 167798 168147 := bstep (se 1 (by rfl) ⟨126110, by rfl⟩ : syracuseStep 168147 = 252221) B252221
theorem B168163 : Blo 167798 168163 := bstep (se 1 (by rfl) ⟨126122, by rfl⟩ : syracuseStep 168163 = 252245) B252245
theorem B168179 : Blo 167798 168179 := bstep (se 1 (by rfl) ⟨126134, by rfl⟩ : syracuseStep 168179 = 252269) B252269
theorem B168195 : Blo 167798 168195 := bstep (se 1 (by rfl) ⟨126146, by rfl⟩ : syracuseStep 168195 = 252293) B252293
theorem B168211 : Blo 167798 168211 := bstep (se 1 (by rfl) ⟨126158, by rfl⟩ : syracuseStep 168211 = 252317) B252317
theorem B168227 : Blo 167798 168227 := bstep (se 1 (by rfl) ⟨126170, by rfl⟩ : syracuseStep 168227 = 252341) B252341
theorem B168243 : Blo 167798 168243 := bstep (se 1 (by rfl) ⟨126182, by rfl⟩ : syracuseStep 168243 = 252365) B252365
theorem B168259 : Blo 167798 168259 := bstep (se 1 (by rfl) ⟨126194, by rfl⟩ : syracuseStep 168259 = 252389) B252389
theorem B168275 : Blo 167798 168275 := bstep (se 1 (by rfl) ⟨126206, by rfl⟩ : syracuseStep 168275 = 252413) B252413
theorem B168291 : Blo 167798 168291 := bstep (se 1 (by rfl) ⟨126218, by rfl⟩ : syracuseStep 168291 = 252437) B252437
theorem B463217 : Blo 167798 463217 := bstep (se 2 (by rfl) ⟨173706, by rfl⟩ : syracuseStep 463217 = 347413) B347413
theorem B168307 : Blo 167798 168307 := bstep (se 1 (by rfl) ⟨126230, by rfl⟩ : syracuseStep 168307 = 252461) B252461
theorem B168323 : Blo 167798 168323 := bstep (se 1 (by rfl) ⟨126242, by rfl⟩ : syracuseStep 168323 = 252485) B252485
theorem B2167181 : Blo 167798 2167181 := bstep (se 3 (by rfl) ⟨406346, by rfl⟩ : syracuseStep 2167181 = 812693) B812693
theorem B168339 : Blo 167798 168339 := bstep (se 1 (by rfl) ⟨126254, by rfl⟩ : syracuseStep 168339 = 252509) B252509
theorem B168355 : Blo 167798 168355 := bstep (se 1 (by rfl) ⟨126266, by rfl⟩ : syracuseStep 168355 = 252533) B252533
theorem B168371 : Blo 167798 168371 := bstep (se 1 (by rfl) ⟨126278, by rfl⟩ : syracuseStep 168371 = 252557) B252557
theorem B168387 : Blo 167798 168387 := bstep (se 1 (by rfl) ⟨126290, by rfl⟩ : syracuseStep 168387 = 252581) B252581
theorem B168403 : Blo 167798 168403 := bstep (se 1 (by rfl) ⟨126302, by rfl⟩ : syracuseStep 168403 = 252605) B252605
theorem B168419 : Blo 167798 168419 := bstep (se 1 (by rfl) ⟨126314, by rfl⟩ : syracuseStep 168419 = 252629) B252629
theorem B168435 : Blo 167798 168435 := bstep (se 1 (by rfl) ⟨126326, by rfl⟩ : syracuseStep 168435 = 252653) B252653
theorem B168451 : Blo 167798 168451 := bstep (se 1 (by rfl) ⟨126338, by rfl⟩ : syracuseStep 168451 = 252677) B252677
theorem B168467 : Blo 167798 168467 := bstep (se 1 (by rfl) ⟨126350, by rfl⟩ : syracuseStep 168467 = 252701) B252701
theorem B168483 : Blo 167798 168483 := bstep (se 1 (by rfl) ⟨126362, by rfl⟩ : syracuseStep 168483 = 252725) B252725
theorem B168499 : Blo 167798 168499 := bstep (se 1 (by rfl) ⟨126374, by rfl⟩ : syracuseStep 168499 = 252749) B252749
theorem B168515 : Blo 167798 168515 := bstep (se 1 (by rfl) ⟨126386, by rfl⟩ : syracuseStep 168515 = 252773) B252773
theorem B168531 : Blo 167798 168531 := bstep (se 1 (by rfl) ⟨126398, by rfl⟩ : syracuseStep 168531 = 252797) B252797
theorem B168547 : Blo 167798 168547 := bstep (se 1 (by rfl) ⟨126410, by rfl⟩ : syracuseStep 168547 = 252821) B252821
theorem B168563 : Blo 167798 168563 := bstep (se 1 (by rfl) ⟨126422, by rfl⟩ : syracuseStep 168563 = 252845) B252845
theorem B168579 : Blo 167798 168579 := bstep (se 1 (by rfl) ⟨126434, by rfl⟩ : syracuseStep 168579 = 252869) B252869
theorem B168595 : Blo 167798 168595 := bstep (se 1 (by rfl) ⟨126446, by rfl⟩ : syracuseStep 168595 = 252893) B252893
theorem B168611 : Blo 167798 168611 := bstep (se 1 (by rfl) ⟨126458, by rfl⟩ : syracuseStep 168611 = 252917) B252917
theorem B168627 : Blo 167798 168627 := bstep (se 1 (by rfl) ⟨126470, by rfl⟩ : syracuseStep 168627 = 252941) B252941
theorem B168643 : Blo 167798 168643 := bstep (se 1 (by rfl) ⟨126482, by rfl⟩ : syracuseStep 168643 = 252965) B252965
theorem B168659 : Blo 167798 168659 := bstep (se 1 (by rfl) ⟨126494, by rfl⟩ : syracuseStep 168659 = 252989) B252989
theorem B168675 : Blo 167798 168675 := bstep (se 1 (by rfl) ⟨126506, by rfl⟩ : syracuseStep 168675 = 253013) B253013
theorem B856817 : Blo 167798 856817 := bstep (se 2 (by rfl) ⟨321306, by rfl⟩ : syracuseStep 856817 = 642613) B642613
theorem B168691 : Blo 167798 168691 := bstep (se 1 (by rfl) ⟨126518, by rfl⟩ : syracuseStep 168691 = 253037) B253037
theorem B168707 : Blo 167798 168707 := bstep (se 1 (by rfl) ⟨126530, by rfl⟩ : syracuseStep 168707 = 253061) B253061
theorem B168723 : Blo 167798 168723 := bstep (se 1 (by rfl) ⟨126542, by rfl⟩ : syracuseStep 168723 = 253085) B253085
theorem B168739 : Blo 167798 168739 := bstep (se 1 (by rfl) ⟨126554, by rfl⟩ : syracuseStep 168739 = 253109) B253109
theorem B168755 : Blo 167798 168755 := bstep (se 1 (by rfl) ⟨126566, by rfl⟩ : syracuseStep 168755 = 253133) B253133
theorem B168771 : Blo 167798 168771 := bstep (se 1 (by rfl) ⟨126578, by rfl⟩ : syracuseStep 168771 = 253157) B253157
theorem B168787 : Blo 167798 168787 := bstep (se 1 (by rfl) ⟨126590, by rfl⟩ : syracuseStep 168787 = 253181) B253181
theorem B168803 : Blo 167798 168803 := bstep (se 1 (by rfl) ⟨126602, by rfl⟩ : syracuseStep 168803 = 253205) B253205
theorem B463715 : Blo 167798 463715 := bstep (se 1 (by rfl) ⟨347786, by rfl⟩ : syracuseStep 463715 = 695573) B695573
theorem B168819 : Blo 167798 168819 := bstep (se 1 (by rfl) ⟨126614, by rfl⟩ : syracuseStep 168819 = 253229) B253229
theorem B168835 : Blo 167798 168835 := bstep (se 1 (by rfl) ⟨126626, by rfl⟩ : syracuseStep 168835 = 253253) B253253
theorem B168851 : Blo 167798 168851 := bstep (se 1 (by rfl) ⟨126638, by rfl⟩ : syracuseStep 168851 = 253277) B253277
theorem B168867 : Blo 167798 168867 := bstep (se 1 (by rfl) ⟨126650, by rfl⟩ : syracuseStep 168867 = 253301) B253301
theorem B168883 : Blo 167798 168883 := bstep (se 1 (by rfl) ⟨126662, by rfl⟩ : syracuseStep 168883 = 253325) B253325
theorem B168899 : Blo 167798 168899 := bstep (se 1 (by rfl) ⟨126674, by rfl⟩ : syracuseStep 168899 = 253349) B253349
theorem B922565 : Blo 167798 922565 := bstep (se 4 (by rfl) ⟨86490, by rfl⟩ : syracuseStep 922565 = 172981) B172981
theorem B168915 : Blo 167798 168915 := bstep (se 1 (by rfl) ⟨126686, by rfl⟩ : syracuseStep 168915 = 253373) B253373
theorem B168931 : Blo 167798 168931 := bstep (se 1 (by rfl) ⟨126698, by rfl⟩ : syracuseStep 168931 = 253397) B253397
theorem B168947 : Blo 167798 168947 := bstep (se 1 (by rfl) ⟨126710, by rfl⟩ : syracuseStep 168947 = 253421) B253421
theorem B168963 : Blo 167798 168963 := bstep (se 1 (by rfl) ⟨126722, by rfl⟩ : syracuseStep 168963 = 253445) B253445
theorem B168979 : Blo 167798 168979 := bstep (se 1 (by rfl) ⟨126734, by rfl⟩ : syracuseStep 168979 = 253469) B253469
theorem B168995 : Blo 167798 168995 := bstep (se 1 (by rfl) ⟨126746, by rfl⟩ : syracuseStep 168995 = 253493) B253493
theorem B431153 : Blo 167798 431153 := bstep (se 2 (by rfl) ⟨161682, by rfl⟩ : syracuseStep 431153 = 323365) B323365
theorem B169011 : Blo 167798 169011 := bstep (se 1 (by rfl) ⟨126758, by rfl⟩ : syracuseStep 169011 = 253517) B253517
theorem B169027 : Blo 167798 169027 := bstep (se 1 (by rfl) ⟨126770, by rfl⟩ : syracuseStep 169027 = 253541) B253541
theorem B169043 : Blo 167798 169043 := bstep (se 1 (by rfl) ⟨126782, by rfl⟩ : syracuseStep 169043 = 253565) B253565
theorem B169059 : Blo 167798 169059 := bstep (se 1 (by rfl) ⟨126794, by rfl⟩ : syracuseStep 169059 = 253589) B253589
theorem B431203 : Blo 167798 431203 := bstep (se 1 (by rfl) ⟨323402, by rfl⟩ : syracuseStep 431203 = 646805) B646805
theorem B169075 : Blo 167798 169075 := bstep (se 1 (by rfl) ⟨126806, by rfl⟩ : syracuseStep 169075 = 253613) B253613
theorem B169091 : Blo 167798 169091 := bstep (se 1 (by rfl) ⟨126818, by rfl⟩ : syracuseStep 169091 = 253637) B253637
theorem B169107 : Blo 167798 169107 := bstep (se 1 (by rfl) ⟨126830, by rfl⟩ : syracuseStep 169107 = 253661) B253661
theorem B169123 : Blo 167798 169123 := bstep (se 1 (by rfl) ⟨126842, by rfl⟩ : syracuseStep 169123 = 253685) B253685
theorem B169139 : Blo 167798 169139 := bstep (se 1 (by rfl) ⟨126854, by rfl⟩ : syracuseStep 169139 = 253709) B253709
theorem B169155 : Blo 167798 169155 := bstep (se 1 (by rfl) ⟨126866, by rfl⟩ : syracuseStep 169155 = 253733) B253733
theorem B726221 : Blo 167798 726221 := bstep (se 3 (by rfl) ⟨136166, by rfl⟩ : syracuseStep 726221 = 272333) B272333
theorem B169171 : Blo 167798 169171 := bstep (se 1 (by rfl) ⟨126878, by rfl⟩ : syracuseStep 169171 = 253757) B253757
theorem B169187 : Blo 167798 169187 := bstep (se 1 (by rfl) ⟨126890, by rfl⟩ : syracuseStep 169187 = 253781) B253781
theorem B431345 : Blo 167798 431345 := bstep (se 2 (by rfl) ⟨161754, by rfl⟩ : syracuseStep 431345 = 323509) B323509
theorem B169203 : Blo 167798 169203 := bstep (se 1 (by rfl) ⟨126902, by rfl⟩ : syracuseStep 169203 = 253805) B253805
theorem B169219 : Blo 167798 169219 := bstep (se 1 (by rfl) ⟨126914, by rfl⟩ : syracuseStep 169219 = 253829) B253829
theorem B169235 : Blo 167798 169235 := bstep (se 1 (by rfl) ⟨126926, by rfl⟩ : syracuseStep 169235 = 253853) B253853
theorem B169251 : Blo 167798 169251 := bstep (se 1 (by rfl) ⟨126938, by rfl⟩ : syracuseStep 169251 = 253877) B253877
theorem B169267 : Blo 167798 169267 := bstep (se 1 (by rfl) ⟨126950, by rfl⟩ : syracuseStep 169267 = 253901) B253901
theorem B169283 : Blo 167798 169283 := bstep (se 1 (by rfl) ⟨126962, by rfl⟩ : syracuseStep 169283 = 253925) B253925
theorem B169299 : Blo 167798 169299 := bstep (se 1 (by rfl) ⟨126974, by rfl⟩ : syracuseStep 169299 = 253949) B253949
theorem B169315 : Blo 167798 169315 := bstep (se 1 (by rfl) ⟨126986, by rfl⟩ : syracuseStep 169315 = 253973) B253973
theorem B169331 : Blo 167798 169331 := bstep (se 1 (by rfl) ⟨126998, by rfl⟩ : syracuseStep 169331 = 253997) B253997
theorem B169347 : Blo 167798 169347 := bstep (se 1 (by rfl) ⟨127010, by rfl⟩ : syracuseStep 169347 = 254021) B254021
theorem B169363 : Blo 167798 169363 := bstep (se 1 (by rfl) ⟨127022, by rfl⟩ : syracuseStep 169363 = 254045) B254045
theorem B169379 : Blo 167798 169379 := bstep (se 1 (by rfl) ⟨127034, by rfl⟩ : syracuseStep 169379 = 254069) B254069
theorem B169395 : Blo 167798 169395 := bstep (se 1 (by rfl) ⟨127046, by rfl⟩ : syracuseStep 169395 = 254093) B254093
theorem B169411 : Blo 167798 169411 := bstep (se 1 (by rfl) ⟨127058, by rfl⟩ : syracuseStep 169411 = 254117) B254117
theorem B1283525 : Blo 167798 1283525 := bstep (se 4 (by rfl) ⟨120330, by rfl⟩ : syracuseStep 1283525 = 240661) B240661
theorem B169427 : Blo 167798 169427 := bstep (se 1 (by rfl) ⟨127070, by rfl⟩ : syracuseStep 169427 = 254141) B254141
theorem B169443 : Blo 167798 169443 := bstep (se 1 (by rfl) ⟨127082, by rfl⟩ : syracuseStep 169443 = 254165) B254165
theorem B169459 : Blo 167798 169459 := bstep (se 1 (by rfl) ⟨127094, by rfl⟩ : syracuseStep 169459 = 254189) B254189
theorem B169475 : Blo 167798 169475 := bstep (se 1 (by rfl) ⟨127106, by rfl⟩ : syracuseStep 169475 = 254213) B254213
theorem B169491 : Blo 167798 169491 := bstep (se 1 (by rfl) ⟨127118, by rfl⟩ : syracuseStep 169491 = 254237) B254237
theorem B169507 : Blo 167798 169507 := bstep (se 1 (by rfl) ⟨127130, by rfl⟩ : syracuseStep 169507 = 254261) B254261
theorem B726563 : Blo 167798 726563 := bstep (se 1 (by rfl) ⟨544922, by rfl⟩ : syracuseStep 726563 = 1089845) B1089845
theorem B169523 : Blo 167798 169523 := bstep (se 1 (by rfl) ⟨127142, by rfl⟩ : syracuseStep 169523 = 254285) B254285
theorem B169539 : Blo 167798 169539 := bstep (se 1 (by rfl) ⟨127154, by rfl⟩ : syracuseStep 169539 = 254309) B254309
theorem B169555 : Blo 167798 169555 := bstep (se 1 (by rfl) ⟨127166, by rfl⟩ : syracuseStep 169555 = 254333) B254333
theorem B169571 : Blo 167798 169571 := bstep (se 1 (by rfl) ⟨127178, by rfl⟩ : syracuseStep 169571 = 254357) B254357
theorem B169587 : Blo 167798 169587 := bstep (se 1 (by rfl) ⟨127190, by rfl⟩ : syracuseStep 169587 = 254381) B254381
theorem B169603 : Blo 167798 169603 := bstep (se 1 (by rfl) ⟨127202, by rfl⟩ : syracuseStep 169603 = 254405) B254405
theorem B169619 : Blo 167798 169619 := bstep (se 1 (by rfl) ⟨127214, by rfl⟩ : syracuseStep 169619 = 254429) B254429
theorem B169635 : Blo 167798 169635 := bstep (se 1 (by rfl) ⟨127226, by rfl⟩ : syracuseStep 169635 = 254453) B254453
theorem B824995 : Blo 167798 824995 := bstep (se 1 (by rfl) ⟨618746, by rfl⟩ : syracuseStep 824995 = 1237493) B1237493
theorem B169651 : Blo 167798 169651 := bstep (se 1 (by rfl) ⟨127238, by rfl⟩ : syracuseStep 169651 = 254477) B254477
theorem B169667 : Blo 167798 169667 := bstep (se 1 (by rfl) ⟨127250, by rfl⟩ : syracuseStep 169667 = 254501) B254501
theorem B1087181 : Blo 167798 1087181 := bstep (se 3 (by rfl) ⟨203846, by rfl⟩ : syracuseStep 1087181 = 407693) B407693
theorem B169683 : Blo 167798 169683 := bstep (se 1 (by rfl) ⟨127262, by rfl⟩ : syracuseStep 169683 = 254525) B254525
theorem B169699 : Blo 167798 169699 := bstep (se 1 (by rfl) ⟨127274, by rfl⟩ : syracuseStep 169699 = 254549) B254549
theorem B694001 : Blo 167798 694001 := bstep (se 2 (by rfl) ⟨260250, by rfl⟩ : syracuseStep 694001 = 520501) B520501
theorem B169715 : Blo 167798 169715 := bstep (se 1 (by rfl) ⟨127286, by rfl⟩ : syracuseStep 169715 = 254573) B254573
theorem B169731 : Blo 167798 169731 := bstep (se 1 (by rfl) ⟨127298, by rfl⟩ : syracuseStep 169731 = 254597) B254597
theorem B169747 : Blo 167798 169747 := bstep (se 1 (by rfl) ⟨127310, by rfl⟩ : syracuseStep 169747 = 254621) B254621
theorem B169763 : Blo 167798 169763 := bstep (se 1 (by rfl) ⟨127322, by rfl⟩ : syracuseStep 169763 = 254645) B254645
theorem B169779 : Blo 167798 169779 := bstep (se 1 (by rfl) ⟨127334, by rfl⟩ : syracuseStep 169779 = 254669) B254669
theorem B169795 : Blo 167798 169795 := bstep (se 1 (by rfl) ⟨127346, by rfl⟩ : syracuseStep 169795 = 254693) B254693
theorem B169811 : Blo 167798 169811 := bstep (se 1 (by rfl) ⟨127358, by rfl⟩ : syracuseStep 169811 = 254717) B254717
theorem B825187 : Blo 167798 825187 := bstep (se 1 (by rfl) ⟨618890, by rfl⟩ : syracuseStep 825187 = 1237781) B1237781
theorem B169827 : Blo 167798 169827 := bstep (se 1 (by rfl) ⟨127370, by rfl⟩ : syracuseStep 169827 = 254741) B254741
theorem B169843 : Blo 167798 169843 := bstep (se 1 (by rfl) ⟨127382, by rfl⟩ : syracuseStep 169843 = 254765) B254765
theorem B169859 : Blo 167798 169859 := bstep (se 1 (by rfl) ⟨127394, by rfl⟩ : syracuseStep 169859 = 254789) B254789
theorem B169875 : Blo 167798 169875 := bstep (se 1 (by rfl) ⟨127406, by rfl⟩ : syracuseStep 169875 = 254813) B254813
theorem B169891 : Blo 167798 169891 := bstep (se 1 (by rfl) ⟨127418, by rfl⟩ : syracuseStep 169891 = 254837) B254837
theorem B169907 : Blo 167798 169907 := bstep (se 1 (by rfl) ⟨127430, by rfl⟩ : syracuseStep 169907 = 254861) B254861
theorem B169923 : Blo 167798 169923 := bstep (se 1 (by rfl) ⟨127442, by rfl⟩ : syracuseStep 169923 = 254885) B254885
theorem B956357 : Blo 167798 956357 := bstep (se 4 (by rfl) ⟨89658, by rfl⟩ : syracuseStep 956357 = 179317) B179317
theorem B366545 : Blo 167798 366545 := bstep (se 2 (by rfl) ⟨137454, by rfl⟩ : syracuseStep 366545 = 274909) B274909
theorem B169939 : Blo 167798 169939 := bstep (se 1 (by rfl) ⟨127454, by rfl⟩ : syracuseStep 169939 = 254909) B254909
theorem B169955 : Blo 167798 169955 := bstep (se 1 (by rfl) ⟨127466, by rfl⟩ : syracuseStep 169955 = 254933) B254933
theorem B169971 : Blo 167798 169971 := bstep (se 1 (by rfl) ⟨127478, by rfl⟩ : syracuseStep 169971 = 254957) B254957
theorem B169987 : Blo 167798 169987 := bstep (se 1 (by rfl) ⟨127490, by rfl⟩ : syracuseStep 169987 = 254981) B254981
theorem B170003 : Blo 167798 170003 := bstep (se 1 (by rfl) ⟨127502, by rfl⟩ : syracuseStep 170003 = 255005) B255005
theorem B170019 : Blo 167798 170019 := bstep (se 1 (by rfl) ⟨127514, by rfl⟩ : syracuseStep 170019 = 255029) B255029
theorem B170035 : Blo 167798 170035 := bstep (se 1 (by rfl) ⟨127526, by rfl⟩ : syracuseStep 170035 = 255053) B255053
theorem B170051 : Blo 167798 170051 := bstep (se 1 (by rfl) ⟨127538, by rfl⟩ : syracuseStep 170051 = 255077) B255077
theorem B170067 : Blo 167798 170067 := bstep (se 1 (by rfl) ⟨127550, by rfl⟩ : syracuseStep 170067 = 255101) B255101
theorem B170083 : Blo 167798 170083 := bstep (se 1 (by rfl) ⟨127562, by rfl⟩ : syracuseStep 170083 = 255125) B255125
theorem B170099 : Blo 167798 170099 := bstep (se 1 (by rfl) ⟨127574, by rfl⟩ : syracuseStep 170099 = 255149) B255149
theorem B170115 : Blo 167798 170115 := bstep (se 1 (by rfl) ⟨127586, by rfl⟩ : syracuseStep 170115 = 255173) B255173
theorem B170131 : Blo 167798 170131 := bstep (se 1 (by rfl) ⟨127598, by rfl⟩ : syracuseStep 170131 = 255197) B255197
theorem B858275 : Blo 167798 858275 := bstep (se 1 (by rfl) ⟨643706, by rfl⟩ : syracuseStep 858275 = 1287413) B1287413
theorem B170147 : Blo 167798 170147 := bstep (se 1 (by rfl) ⟨127610, by rfl⟩ : syracuseStep 170147 = 255221) B255221
theorem B170163 : Blo 167798 170163 := bstep (se 1 (by rfl) ⟨127622, by rfl⟩ : syracuseStep 170163 = 255245) B255245
theorem B170179 : Blo 167798 170179 := bstep (se 1 (by rfl) ⟨127634, by rfl⟩ : syracuseStep 170179 = 255269) B255269
theorem B432337 : Blo 167798 432337 := bstep (se 2 (by rfl) ⟨162126, by rfl⟩ : syracuseStep 432337 = 324253) B324253
theorem B170195 : Blo 167798 170195 := bstep (se 1 (by rfl) ⟨127646, by rfl⟩ : syracuseStep 170195 = 255293) B255293
theorem B170211 : Blo 167798 170211 := bstep (se 1 (by rfl) ⟨127658, by rfl⟩ : syracuseStep 170211 = 255317) B255317
theorem B2070755 : Blo 167798 2070755 := bstep (se 1 (by rfl) ⟨1553066, by rfl⟩ : syracuseStep 2070755 = 3106133) B3106133
theorem B170227 : Blo 167798 170227 := bstep (se 1 (by rfl) ⟨127670, by rfl⟩ : syracuseStep 170227 = 255341) B255341
theorem B170243 : Blo 167798 170243 := bstep (se 1 (by rfl) ⟨127682, by rfl⟩ : syracuseStep 170243 = 255365) B255365
theorem B170259 : Blo 167798 170259 := bstep (se 1 (by rfl) ⟨127694, by rfl⟩ : syracuseStep 170259 = 255389) B255389
theorem B170275 : Blo 167798 170275 := bstep (se 1 (by rfl) ⟨127706, by rfl⟩ : syracuseStep 170275 = 255413) B255413
theorem B170291 : Blo 167798 170291 := bstep (se 1 (by rfl) ⟨127718, by rfl⟩ : syracuseStep 170291 = 255437) B255437
theorem B170307 : Blo 167798 170307 := bstep (se 1 (by rfl) ⟨127730, by rfl⟩ : syracuseStep 170307 = 255461) B255461
theorem B170323 : Blo 167798 170323 := bstep (se 1 (by rfl) ⟨127742, by rfl⟩ : syracuseStep 170323 = 255485) B255485
theorem B170339 : Blo 167798 170339 := bstep (se 1 (by rfl) ⟨127754, by rfl⟩ : syracuseStep 170339 = 255509) B255509
theorem B2595185 : Blo 167798 2595185 := bstep (se 2 (by rfl) ⟨973194, by rfl⟩ : syracuseStep 2595185 = 1946389) B1946389
theorem B170355 : Blo 167798 170355 := bstep (se 1 (by rfl) ⟨127766, by rfl⟩ : syracuseStep 170355 = 255533) B255533
theorem B170371 : Blo 167798 170371 := bstep (se 1 (by rfl) ⟨127778, by rfl⟩ : syracuseStep 170371 = 255557) B255557
theorem B170387 : Blo 167798 170387 := bstep (se 1 (by rfl) ⟨127790, by rfl⟩ : syracuseStep 170387 = 255581) B255581
theorem B170403 : Blo 167798 170403 := bstep (se 1 (by rfl) ⟨127802, by rfl⟩ : syracuseStep 170403 = 255605) B255605
theorem B170419 : Blo 167798 170419 := bstep (se 1 (by rfl) ⟨127814, by rfl⟩ : syracuseStep 170419 = 255629) B255629
theorem B170435 : Blo 167798 170435 := bstep (se 1 (by rfl) ⟨127826, by rfl⟩ : syracuseStep 170435 = 255653) B255653
theorem B170451 : Blo 167798 170451 := bstep (se 1 (by rfl) ⟨127838, by rfl⟩ : syracuseStep 170451 = 255677) B255677
theorem B170467 : Blo 167798 170467 := bstep (se 1 (by rfl) ⟨127850, by rfl⟩ : syracuseStep 170467 = 255701) B255701
theorem B432611 : Blo 167798 432611 := bstep (se 1 (by rfl) ⟨324458, by rfl⟩ : syracuseStep 432611 = 648917) B648917
theorem B203251 : Blo 167798 203251 := bstep (se 1 (by rfl) ⟨152438, by rfl⟩ : syracuseStep 203251 = 304877) B304877
theorem B170483 : Blo 167798 170483 := bstep (se 1 (by rfl) ⟨127862, by rfl⟩ : syracuseStep 170483 = 255725) B255725
theorem B170499 : Blo 167798 170499 := bstep (se 1 (by rfl) ⟨127874, by rfl⟩ : syracuseStep 170499 = 255749) B255749
theorem B1645069 : Blo 167798 1645069 := bstep (se 3 (by rfl) ⟨308450, by rfl⟩ : syracuseStep 1645069 = 616901) B616901
theorem B170515 : Blo 167798 170515 := bstep (se 1 (by rfl) ⟨127886, by rfl⟩ : syracuseStep 170515 = 255773) B255773
theorem B170531 : Blo 167798 170531 := bstep (se 1 (by rfl) ⟨127898, by rfl⟩ : syracuseStep 170531 = 255797) B255797
theorem B170547 : Blo 167798 170547 := bstep (se 1 (by rfl) ⟨127910, by rfl⟩ : syracuseStep 170547 = 255821) B255821
theorem B170563 : Blo 167798 170563 := bstep (se 1 (by rfl) ⟨127922, by rfl⟩ : syracuseStep 170563 = 255845) B255845
theorem B203347 : Blo 167798 203347 := bstep (se 1 (by rfl) ⟨152510, by rfl⟩ : syracuseStep 203347 = 305021) B305021
theorem B170579 : Blo 167798 170579 := bstep (se 1 (by rfl) ⟨127934, by rfl⟩ : syracuseStep 170579 = 255869) B255869
theorem B170595 : Blo 167798 170595 := bstep (se 1 (by rfl) ⟨127946, by rfl⟩ : syracuseStep 170595 = 255893) B255893
theorem B957041 : Blo 167798 957041 := bstep (se 2 (by rfl) ⟨358890, by rfl⟩ : syracuseStep 957041 = 717781) B717781
theorem B170611 : Blo 167798 170611 := bstep (se 1 (by rfl) ⟨127958, by rfl⟩ : syracuseStep 170611 = 255917) B255917
theorem B170627 : Blo 167798 170627 := bstep (se 1 (by rfl) ⟨127970, by rfl⟩ : syracuseStep 170627 = 255941) B255941
theorem B498317 : Blo 167798 498317 := bstep (se 3 (by rfl) ⟨93434, by rfl⟩ : syracuseStep 498317 = 186869) B186869
theorem B694925 : Blo 167798 694925 := bstep (se 3 (by rfl) ⟨130298, by rfl⟩ : syracuseStep 694925 = 260597) B260597
theorem B170643 : Blo 167798 170643 := bstep (se 1 (by rfl) ⟨127982, by rfl⟩ : syracuseStep 170643 = 255965) B255965
theorem B170659 : Blo 167798 170659 := bstep (se 1 (by rfl) ⟨127994, by rfl⟩ : syracuseStep 170659 = 255989) B255989
theorem B432803 : Blo 167798 432803 := bstep (se 1 (by rfl) ⟨324602, by rfl⟩ : syracuseStep 432803 = 649205) B649205
theorem B170675 : Blo 167798 170675 := bstep (se 1 (by rfl) ⟨128006, by rfl⟩ : syracuseStep 170675 = 256013) B256013
theorem B170691 : Blo 167798 170691 := bstep (se 1 (by rfl) ⟨128018, by rfl⟩ : syracuseStep 170691 = 256037) B256037
theorem B170707 : Blo 167798 170707 := bstep (se 1 (by rfl) ⟨128030, by rfl⟩ : syracuseStep 170707 = 256061) B256061
theorem B170723 : Blo 167798 170723 := bstep (se 1 (by rfl) ⟨128042, by rfl⟩ : syracuseStep 170723 = 256085) B256085
theorem B170739 : Blo 167798 170739 := bstep (se 1 (by rfl) ⟨128054, by rfl⟩ : syracuseStep 170739 = 256109) B256109
theorem B170755 : Blo 167798 170755 := bstep (se 1 (by rfl) ⟨128066, by rfl⟩ : syracuseStep 170755 = 256133) B256133
theorem B170771 : Blo 167798 170771 := bstep (se 1 (by rfl) ⟨128078, by rfl⟩ : syracuseStep 170771 = 256157) B256157
theorem B170787 : Blo 167798 170787 := bstep (se 1 (by rfl) ⟨128090, by rfl⟩ : syracuseStep 170787 = 256181) B256181
theorem B170803 : Blo 167798 170803 := bstep (se 1 (by rfl) ⟨128102, by rfl⟩ : syracuseStep 170803 = 256205) B256205
theorem B170819 : Blo 167798 170819 := bstep (se 1 (by rfl) ⟨128114, by rfl⟩ : syracuseStep 170819 = 256229) B256229
theorem B170835 : Blo 167798 170835 := bstep (se 1 (by rfl) ⟨128126, by rfl⟩ : syracuseStep 170835 = 256253) B256253
theorem B170851 : Blo 167798 170851 := bstep (se 1 (by rfl) ⟨128138, by rfl⟩ : syracuseStep 170851 = 256277) B256277
theorem B203635 : Blo 167798 203635 := bstep (se 1 (by rfl) ⟨152726, by rfl⟩ : syracuseStep 203635 = 305453) B305453
theorem B170867 : Blo 167798 170867 := bstep (se 1 (by rfl) ⟨128150, by rfl⟩ : syracuseStep 170867 = 256301) B256301
theorem B170883 : Blo 167798 170883 := bstep (se 1 (by rfl) ⟨128162, by rfl⟩ : syracuseStep 170883 = 256325) B256325
theorem B170899 : Blo 167798 170899 := bstep (se 1 (by rfl) ⟨128174, by rfl⟩ : syracuseStep 170899 = 256349) B256349
theorem B170915 : Blo 167798 170915 := bstep (se 1 (by rfl) ⟨128186, by rfl⟩ : syracuseStep 170915 = 256373) B256373
theorem B170931 : Blo 167798 170931 := bstep (se 1 (by rfl) ⟨128198, by rfl⟩ : syracuseStep 170931 = 256397) B256397
theorem B170947 : Blo 167798 170947 := bstep (se 1 (by rfl) ⟨128210, by rfl⟩ : syracuseStep 170947 = 256421) B256421
theorem B859085 : Blo 167798 859085 := bstep (se 3 (by rfl) ⟨161078, by rfl⟩ : syracuseStep 859085 = 322157) B322157
theorem B170963 : Blo 167798 170963 := bstep (se 1 (by rfl) ⟨128222, by rfl⟩ : syracuseStep 170963 = 256445) B256445
theorem B170979 : Blo 167798 170979 := bstep (se 1 (by rfl) ⟨128234, by rfl⟩ : syracuseStep 170979 = 256469) B256469
theorem B170995 : Blo 167798 170995 := bstep (se 1 (by rfl) ⟨128246, by rfl⟩ : syracuseStep 170995 = 256493) B256493
theorem B171011 : Blo 167798 171011 := bstep (se 1 (by rfl) ⟨128258, by rfl⟩ : syracuseStep 171011 = 256517) B256517
theorem B171027 : Blo 167798 171027 := bstep (se 1 (by rfl) ⟨128270, by rfl⟩ : syracuseStep 171027 = 256541) B256541
theorem B171043 : Blo 167798 171043 := bstep (se 1 (by rfl) ⟨128282, by rfl⟩ : syracuseStep 171043 = 256565) B256565
theorem B203827 : Blo 167798 203827 := bstep (se 1 (by rfl) ⟨152870, by rfl⟩ : syracuseStep 203827 = 305741) B305741
theorem B171059 : Blo 167798 171059 := bstep (se 1 (by rfl) ⟨128294, by rfl⟩ : syracuseStep 171059 = 256589) B256589
theorem B171075 : Blo 167798 171075 := bstep (se 1 (by rfl) ⟨128306, by rfl⟩ : syracuseStep 171075 = 256613) B256613
theorem B171091 : Blo 167798 171091 := bstep (se 1 (by rfl) ⟨128318, by rfl⟩ : syracuseStep 171091 = 256637) B256637
theorem B269411 : Blo 167798 269411 := bstep (se 1 (by rfl) ⟨202058, by rfl⟩ : syracuseStep 269411 = 404117) B404117
theorem B171107 : Blo 167798 171107 := bstep (se 1 (by rfl) ⟨128330, by rfl⟩ : syracuseStep 171107 = 256661) B256661
theorem B171123 : Blo 167798 171123 := bstep (se 1 (by rfl) ⟨128342, by rfl⟩ : syracuseStep 171123 = 256685) B256685
theorem B171139 : Blo 167798 171139 := bstep (se 1 (by rfl) ⟨128354, by rfl⟩ : syracuseStep 171139 = 256709) B256709
theorem B171155 : Blo 167798 171155 := bstep (se 1 (by rfl) ⟨128366, by rfl⟩ : syracuseStep 171155 = 256733) B256733
theorem B171171 : Blo 167798 171171 := bstep (se 1 (by rfl) ⟨128378, by rfl⟩ : syracuseStep 171171 = 256757) B256757
theorem B269489 : Blo 167798 269489 := bstep (se 2 (by rfl) ⟨101058, by rfl⟩ : syracuseStep 269489 = 202117) B202117
theorem B171187 : Blo 167798 171187 := bstep (se 1 (by rfl) ⟨128390, by rfl⟩ : syracuseStep 171187 = 256781) B256781
theorem B171203 : Blo 167798 171203 := bstep (se 1 (by rfl) ⟨128402, by rfl⟩ : syracuseStep 171203 = 256805) B256805
theorem B4168901 : Blo 167798 4168901 := bstep (se 4 (by rfl) ⟨390834, by rfl⟩ : syracuseStep 4168901 = 781669) B781669
theorem B171219 : Blo 167798 171219 := bstep (se 1 (by rfl) ⟨128414, by rfl⟩ : syracuseStep 171219 = 256829) B256829
theorem B171235 : Blo 167798 171235 := bstep (se 1 (by rfl) ⟨128426, by rfl⟩ : syracuseStep 171235 = 256853) B256853
theorem B171251 : Blo 167798 171251 := bstep (se 1 (by rfl) ⟨128438, by rfl⟩ : syracuseStep 171251 = 256877) B256877
theorem B171267 : Blo 167798 171267 := bstep (se 1 (by rfl) ⟨128450, by rfl⟩ : syracuseStep 171267 = 256901) B256901
theorem B171283 : Blo 167798 171283 := bstep (se 1 (by rfl) ⟨128462, by rfl⟩ : syracuseStep 171283 = 256925) B256925
theorem B171299 : Blo 167798 171299 := bstep (se 1 (by rfl) ⟨128474, by rfl⟩ : syracuseStep 171299 = 256949) B256949
theorem B171315 : Blo 167798 171315 := bstep (se 1 (by rfl) ⟨128486, by rfl⟩ : syracuseStep 171315 = 256973) B256973
theorem B171331 : Blo 167798 171331 := bstep (se 1 (by rfl) ⟨128498, by rfl⟩ : syracuseStep 171331 = 256997) B256997
theorem B171347 : Blo 167798 171347 := bstep (se 1 (by rfl) ⟨128510, by rfl⟩ : syracuseStep 171347 = 257021) B257021
theorem B171363 : Blo 167798 171363 := bstep (se 1 (by rfl) ⟨128522, by rfl⟩ : syracuseStep 171363 = 257045) B257045
theorem B171379 : Blo 167798 171379 := bstep (se 1 (by rfl) ⟨128534, by rfl⟩ : syracuseStep 171379 = 257069) B257069
theorem B171395 : Blo 167798 171395 := bstep (se 1 (by rfl) ⟨128546, by rfl⟩ : syracuseStep 171395 = 257093) B257093
theorem B171411 : Blo 167798 171411 := bstep (se 1 (by rfl) ⟨128558, by rfl⟩ : syracuseStep 171411 = 257117) B257117
theorem B171427 : Blo 167798 171427 := bstep (se 1 (by rfl) ⟨128570, by rfl⟩ : syracuseStep 171427 = 257141) B257141
theorem B171443 : Blo 167798 171443 := bstep (se 1 (by rfl) ⟨128582, by rfl⟩ : syracuseStep 171443 = 257165) B257165
theorem B171459 : Blo 167798 171459 := bstep (se 1 (by rfl) ⟨128594, by rfl⟩ : syracuseStep 171459 = 257189) B257189
theorem B171475 : Blo 167798 171475 := bstep (se 1 (by rfl) ⟨128606, by rfl⟩ : syracuseStep 171475 = 257213) B257213
theorem B171491 : Blo 167798 171491 := bstep (se 1 (by rfl) ⟨128618, by rfl⟩ : syracuseStep 171491 = 257237) B257237
theorem B171507 : Blo 167798 171507 := bstep (se 1 (by rfl) ⟨128630, by rfl⟩ : syracuseStep 171507 = 257261) B257261
theorem B171523 : Blo 167798 171523 := bstep (se 1 (by rfl) ⟨128642, by rfl⟩ : syracuseStep 171523 = 257285) B257285
theorem B171539 : Blo 167798 171539 := bstep (se 1 (by rfl) ⟨128654, by rfl⟩ : syracuseStep 171539 = 257309) B257309
theorem B171555 : Blo 167798 171555 := bstep (se 1 (by rfl) ⟨128666, by rfl⟩ : syracuseStep 171555 = 257333) B257333
theorem B269873 : Blo 167798 269873 := bstep (se 2 (by rfl) ⟨101202, by rfl⟩ : syracuseStep 269873 = 202405) B202405
theorem B171571 : Blo 167798 171571 := bstep (se 1 (by rfl) ⟨128678, by rfl⟩ : syracuseStep 171571 = 257357) B257357
theorem B171587 : Blo 167798 171587 := bstep (se 1 (by rfl) ⟨128690, by rfl⟩ : syracuseStep 171587 = 257381) B257381
theorem B433745 : Blo 167798 433745 := bstep (se 2 (by rfl) ⟨162654, by rfl⟩ : syracuseStep 433745 = 325309) B325309
theorem B171603 : Blo 167798 171603 := bstep (se 1 (by rfl) ⟨128702, by rfl⟩ : syracuseStep 171603 = 257405) B257405
theorem B171619 : Blo 167798 171619 := bstep (se 1 (by rfl) ⟨128714, by rfl⟩ : syracuseStep 171619 = 257429) B257429
theorem B171635 : Blo 167798 171635 := bstep (se 1 (by rfl) ⟨128726, by rfl⟩ : syracuseStep 171635 = 257453) B257453
theorem B433795 : Blo 167798 433795 := bstep (se 1 (by rfl) ⟨325346, by rfl⟩ : syracuseStep 433795 = 650693) B650693
theorem B171651 : Blo 167798 171651 := bstep (se 1 (by rfl) ⟨128738, by rfl⟩ : syracuseStep 171651 = 257477) B257477
theorem B171667 : Blo 167798 171667 := bstep (se 1 (by rfl) ⟨128750, by rfl⟩ : syracuseStep 171667 = 257501) B257501
theorem B171683 : Blo 167798 171683 := bstep (se 1 (by rfl) ⟨128762, by rfl⟩ : syracuseStep 171683 = 257525) B257525
theorem B270001 : Blo 167798 270001 := bstep (se 2 (by rfl) ⟨101250, by rfl⟩ : syracuseStep 270001 = 202501) B202501
theorem B171699 : Blo 167798 171699 := bstep (se 1 (by rfl) ⟨128774, by rfl⟩ : syracuseStep 171699 = 257549) B257549
theorem B171715 : Blo 167798 171715 := bstep (se 1 (by rfl) ⟨128786, by rfl⟩ : syracuseStep 171715 = 257573) B257573
theorem B171731 : Blo 167798 171731 := bstep (se 1 (by rfl) ⟨128798, by rfl⟩ : syracuseStep 171731 = 257597) B257597
theorem B171747 : Blo 167798 171747 := bstep (se 1 (by rfl) ⟨128810, by rfl⟩ : syracuseStep 171747 = 257621) B257621
theorem B171763 : Blo 167798 171763 := bstep (se 1 (by rfl) ⟨128822, by rfl⟩ : syracuseStep 171763 = 257645) B257645
theorem B171779 : Blo 167798 171779 := bstep (se 1 (by rfl) ⟨128834, by rfl⟩ : syracuseStep 171779 = 257669) B257669
theorem B696077 : Blo 167798 696077 := bstep (se 3 (by rfl) ⟨130514, by rfl⟩ : syracuseStep 696077 = 261029) B261029
theorem B433937 : Blo 167798 433937 := bstep (se 2 (by rfl) ⟨162726, by rfl⟩ : syracuseStep 433937 = 325453) B325453
theorem B171795 : Blo 167798 171795 := bstep (se 1 (by rfl) ⟨128846, by rfl⟩ : syracuseStep 171795 = 257693) B257693
theorem B204707 : Blo 167798 204707 := bstep (se 1 (by rfl) ⟨153530, by rfl⟩ : syracuseStep 204707 = 307061) B307061
theorem B303139 : Blo 167798 303139 := bstep (se 1 (by rfl) ⟨227354, by rfl⟩ : syracuseStep 303139 = 454709) B454709
theorem B958499 : Blo 167798 958499 := bstep (se 1 (by rfl) ⟨718874, by rfl⟩ : syracuseStep 958499 = 1437749) B1437749
theorem B303601 : Blo 167798 303601 := bstep (se 2 (by rfl) ⟨113850, by rfl⟩ : syracuseStep 303601 = 227701) B227701
theorem B730019 : Blo 167798 730019 := bstep (se 1 (by rfl) ⟨547514, by rfl⟩ : syracuseStep 730019 = 1095029) B1095029
theorem B205907 : Blo 167798 205907 := bstep (se 1 (by rfl) ⟨154430, by rfl⟩ : syracuseStep 205907 = 308861) B308861
theorem B304241 : Blo 167798 304241 := bstep (se 2 (by rfl) ⟨114090, by rfl⟩ : syracuseStep 304241 = 228181) B228181
theorem B271507 : Blo 167798 271507 := bstep (se 1 (by rfl) ⟨203630, by rfl⟩ : syracuseStep 271507 = 407261) B407261
theorem B566513 : Blo 167798 566513 := bstep (se 2 (by rfl) ⟨212442, by rfl⟩ : syracuseStep 566513 = 424885) B424885
theorem B369937 : Blo 167798 369937 := bstep (se 2 (by rfl) ⟨138726, by rfl⟩ : syracuseStep 369937 = 277453) B277453
theorem B730595 : Blo 167798 730595 := bstep (se 1 (by rfl) ⟨547946, by rfl⟩ : syracuseStep 730595 = 1095893) B1095893
theorem B239107 : Blo 167798 239107 := bstep (se 1 (by rfl) ⟨179330, by rfl⟩ : syracuseStep 239107 = 358661) B358661
theorem B173603 : Blo 167798 173603 := bstep (se 1 (by rfl) ⟨130202, by rfl⟩ : syracuseStep 173603 = 260405) B260405
theorem B239203 : Blo 167798 239203 := bstep (se 1 (by rfl) ⟨179402, by rfl⟩ : syracuseStep 239203 = 358805) B358805
theorem B4368013 : Blo 167798 4368013 := bstep (se 3 (by rfl) ⟨819002, by rfl⟩ : syracuseStep 4368013 = 1638005) B1638005
theorem B927409 : Blo 167798 927409 := bstep (se 2 (by rfl) ⟨347778, by rfl⟩ : syracuseStep 927409 = 695557) B695557
theorem B567053 : Blo 167798 567053 := bstep (se 3 (by rfl) ⟨106322, by rfl⟩ : syracuseStep 567053 = 212645) B212645
theorem B862001 : Blo 167798 862001 := bstep (se 2 (by rfl) ⟨323250, by rfl⟩ : syracuseStep 862001 = 646501) B646501
theorem B272179 : Blo 167798 272179 := bstep (se 1 (by rfl) ⟨204134, by rfl⟩ : syracuseStep 272179 = 408269) B408269
theorem B567107 : Blo 167798 567107 := bstep (se 1 (by rfl) ⟨425330, by rfl⟩ : syracuseStep 567107 = 850661) B850661
theorem B1222499 : Blo 167798 1222499 := bstep (se 1 (by rfl) ⟨916874, by rfl⟩ : syracuseStep 1222499 = 1833749) B1833749
theorem B567377 : Blo 167798 567377 := bstep (se 2 (by rfl) ⟨212766, by rfl⟩ : syracuseStep 567377 = 425533) B425533
theorem B239699 : Blo 167798 239699 := bstep (se 1 (by rfl) ⟨179774, by rfl⟩ : syracuseStep 239699 = 359549) B359549
theorem B272641 : Blo 167798 272641 := bstep (se 2 (by rfl) ⟨102240, by rfl⟩ : syracuseStep 272641 = 204481) B204481
theorem B272737 : Blo 167798 272737 := bstep (se 2 (by rfl) ⟨102276, by rfl⟩ : syracuseStep 272737 = 204553) B204553
theorem B1485155 : Blo 167798 1485155 := bstep (se 1 (by rfl) ⟨1113866, by rfl⟩ : syracuseStep 1485155 = 2227733) B2227733
theorem B272897 : Blo 167798 272897 := bstep (se 2 (by rfl) ⟨102336, by rfl⟩ : syracuseStep 272897 = 204673) B204673
theorem B404003 : Blo 167798 404003 := bstep (se 1 (by rfl) ⟨303002, by rfl⟩ : syracuseStep 404003 = 606005) B606005
theorem B371299 : Blo 167798 371299 := bstep (se 1 (by rfl) ⟨278474, by rfl⟩ : syracuseStep 371299 = 556949) B556949
theorem B567917 : Blo 167798 567917 := bstep (se 3 (by rfl) ⟨106484, by rfl⟩ : syracuseStep 567917 = 212969) B212969
theorem B3943025 : Blo 167798 3943025 := bstep (se 2 (by rfl) ⟨1478634, by rfl⟩ : syracuseStep 3943025 = 2957269) B2957269
theorem B1911437 : Blo 167798 1911437 := bstep (se 3 (by rfl) ⟨358394, by rfl⟩ : syracuseStep 1911437 = 716789) B716789
theorem B567971 : Blo 167798 567971 := bstep (se 1 (by rfl) ⟨425978, by rfl⟩ : syracuseStep 567971 = 851957) B851957
theorem B731825 : Blo 167798 731825 := bstep (se 2 (by rfl) ⟨274434, by rfl⟩ : syracuseStep 731825 = 548869) B548869
theorem B240337 : Blo 167798 240337 := bstep (se 2 (by rfl) ⟨90126, by rfl⟩ : syracuseStep 240337 = 180253) B180253
theorem B371491 : Blo 167798 371491 := bstep (se 1 (by rfl) ⟨278618, by rfl⟩ : syracuseStep 371491 = 557237) B557237
theorem B404291 : Blo 167798 404291 := bstep (se 1 (by rfl) ⟨303218, by rfl⟩ : syracuseStep 404291 = 606437) B606437
theorem B863075 : Blo 167798 863075 := bstep (se 1 (by rfl) ⟨647306, by rfl⟩ : syracuseStep 863075 = 1294613) B1294613
theorem B568241 : Blo 167798 568241 := bstep (se 2 (by rfl) ⟨213090, by rfl⟩ : syracuseStep 568241 = 426181) B426181
theorem B699313 : Blo 167798 699313 := bstep (se 2 (by rfl) ⟨262242, by rfl⟩ : syracuseStep 699313 = 524485) B524485
theorem B240673 : Blo 167798 240673 := bstep (se 2 (by rfl) ⟨90252, by rfl⟩ : syracuseStep 240673 = 180505) B180505
theorem B1289357 : Blo 167798 1289357 := bstep (se 3 (by rfl) ⟨241754, by rfl⟩ : syracuseStep 1289357 = 483509) B483509
theorem B961733 : Blo 167798 961733 := bstep (se 4 (by rfl) ⟨90162, by rfl⟩ : syracuseStep 961733 = 180325) B180325
theorem B863459 : Blo 167798 863459 := bstep (se 1 (by rfl) ⟨647594, by rfl⟩ : syracuseStep 863459 = 1295189) B1295189
theorem B208243 : Blo 167798 208243 := bstep (se 1 (by rfl) ⟨156182, by rfl⟩ : syracuseStep 208243 = 312365) B312365
theorem B568781 : Blo 167798 568781 := bstep (se 3 (by rfl) ⟨106646, by rfl⟩ : syracuseStep 568781 = 213293) B213293
theorem B568835 : Blo 167798 568835 := bstep (se 1 (by rfl) ⟨426626, by rfl⟩ : syracuseStep 568835 = 853253) B853253
theorem B241265 : Blo 167798 241265 := bstep (se 2 (by rfl) ⟨90474, by rfl⟩ : syracuseStep 241265 = 180949) B180949
theorem B962189 : Blo 167798 962189 := bstep (se 3 (by rfl) ⟨180410, by rfl⟩ : syracuseStep 962189 = 360821) B360821
theorem B405137 : Blo 167798 405137 := bstep (se 2 (by rfl) ⟨151926, by rfl⟩ : syracuseStep 405137 = 303853) B303853
theorem B2895587 : Blo 167798 2895587 := bstep (se 1 (by rfl) ⟨2171690, by rfl⟩ : syracuseStep 2895587 = 4343381) B4343381
theorem B405233 : Blo 167798 405233 := bstep (se 2 (by rfl) ⟨151962, by rfl⟩ : syracuseStep 405233 = 303925) B303925
theorem B569105 : Blo 167798 569105 := bstep (se 2 (by rfl) ⟨213414, by rfl⟩ : syracuseStep 569105 = 426829) B426829
theorem B405425 : Blo 167798 405425 := bstep (se 2 (by rfl) ⟨152034, by rfl⟩ : syracuseStep 405425 = 304069) B304069
theorem B1093637 : Blo 167798 1093637 := bstep (se 4 (by rfl) ⟨102528, by rfl⟩ : syracuseStep 1093637 = 205057) B205057
theorem B864269 : Blo 167798 864269 := bstep (se 3 (by rfl) ⟨162050, by rfl⟩ : syracuseStep 864269 = 324101) B324101
theorem B241795 : Blo 167798 241795 := bstep (se 1 (by rfl) ⟨181346, by rfl⟩ : syracuseStep 241795 = 362693) B362693
theorem B274691 : Blo 167798 274691 := bstep (se 1 (by rfl) ⟨206018, by rfl⟩ : syracuseStep 274691 = 412037) B412037
theorem B569645 : Blo 167798 569645 := bstep (se 3 (by rfl) ⟨106808, by rfl⟩ : syracuseStep 569645 = 213617) B213617
theorem B569699 : Blo 167798 569699 := bstep (se 1 (by rfl) ⟨427274, by rfl⟩ : syracuseStep 569699 = 854549) B854549
theorem B438691 : Blo 167798 438691 := bstep (se 1 (by rfl) ⟨329018, by rfl⟩ : syracuseStep 438691 = 658037) B658037
theorem B242131 : Blo 167798 242131 := bstep (se 1 (by rfl) ⟨181598, by rfl⟩ : syracuseStep 242131 = 363197) B363197
theorem B569969 : Blo 167798 569969 := bstep (se 2 (by rfl) ⟨213738, by rfl⟩ : syracuseStep 569969 = 427477) B427477
theorem B307889 : Blo 167798 307889 := bstep (se 2 (by rfl) ⟨115458, by rfl⟩ : syracuseStep 307889 = 230917) B230917
theorem B242689 : Blo 167798 242689 := bstep (se 2 (by rfl) ⟨91008, by rfl⟩ : syracuseStep 242689 = 182017) B182017
theorem B242723 : Blo 167798 242723 := bstep (se 1 (by rfl) ⟨182042, by rfl⟩ : syracuseStep 242723 = 364085) B364085
theorem B406577 : Blo 167798 406577 := bstep (se 2 (by rfl) ⟨152466, by rfl⟩ : syracuseStep 406577 = 304933) B304933
theorem B439427 : Blo 167798 439427 := bstep (se 1 (by rfl) ⟨329570, by rfl⟩ : syracuseStep 439427 = 659141) B659141
theorem B570509 : Blo 167798 570509 := bstep (se 3 (by rfl) ⟨106970, by rfl⟩ : syracuseStep 570509 = 213941) B213941
theorem B1455245 : Blo 167798 1455245 := bstep (se 3 (by rfl) ⟨272858, by rfl⟩ : syracuseStep 1455245 = 545717) B545717
theorem B701581 : Blo 167798 701581 := bstep (se 3 (by rfl) ⟨131546, by rfl⟩ : syracuseStep 701581 = 263093) B263093
theorem B570563 : Blo 167798 570563 := bstep (se 1 (by rfl) ⟨427922, by rfl⟩ : syracuseStep 570563 = 855845) B855845
theorem B308675 : Blo 167798 308675 := bstep (se 1 (by rfl) ⟨231506, by rfl⟩ : syracuseStep 308675 = 463013) B463013
theorem B570833 : Blo 167798 570833 := bstep (se 2 (by rfl) ⟨214062, by rfl⟩ : syracuseStep 570833 = 428125) B428125
theorem B538093 : Blo 167798 538093 := bstep (se 3 (by rfl) ⟨100892, by rfl⟩ : syracuseStep 538093 = 201785) B201785
theorem B1914353 : Blo 167798 1914353 := bstep (se 2 (by rfl) ⟨717882, by rfl⟩ : syracuseStep 1914353 = 1435765) B1435765
theorem B538157 : Blo 167798 538157 := bstep (se 3 (by rfl) ⟨100904, by rfl⟩ : syracuseStep 538157 = 201809) B201809
theorem B243281 : Blo 167798 243281 := bstep (se 2 (by rfl) ⟨91230, by rfl⟩ : syracuseStep 243281 = 182461) B182461
theorem B243361 : Blo 167798 243361 := bstep (se 2 (by rfl) ⟨91260, by rfl⟩ : syracuseStep 243361 = 182521) B182521
theorem B276257 : Blo 167798 276257 := bstep (se 2 (by rfl) ⟨103596, by rfl⟩ : syracuseStep 276257 = 207193) B207193
theorem B571373 : Blo 167798 571373 := bstep (se 3 (by rfl) ⟨107132, by rfl⟩ : syracuseStep 571373 = 214265) B214265
theorem B1292273 : Blo 167798 1292273 := bstep (se 2 (by rfl) ⟨484602, by rfl⟩ : syracuseStep 1292273 = 969205) B969205
theorem B571427 : Blo 167798 571427 := bstep (se 1 (by rfl) ⟨428570, by rfl⟩ : syracuseStep 571427 = 857141) B857141
theorem B440579 : Blo 167798 440579 := bstep (se 1 (by rfl) ⟨330434, by rfl⟩ : syracuseStep 440579 = 660869) B660869
theorem B571697 : Blo 167798 571697 := bstep (se 2 (by rfl) ⟨214386, by rfl⟩ : syracuseStep 571697 = 428773) B428773
theorem B244147 : Blo 167798 244147 := bstep (se 1 (by rfl) ⟨183110, by rfl⟩ : syracuseStep 244147 = 366221) B366221
theorem B965105 : Blo 167798 965105 := bstep (se 2 (by rfl) ⟨361914, by rfl⟩ : syracuseStep 965105 = 723829) B723829
theorem B1096355 : Blo 167798 1096355 := bstep (se 1 (by rfl) ⟨822266, by rfl⟩ : syracuseStep 1096355 = 1644533) B1644533
theorem B277219 : Blo 167798 277219 := bstep (se 1 (by rfl) ⟨207914, by rfl⟩ : syracuseStep 277219 = 415829) B415829
theorem B572237 : Blo 167798 572237 := bstep (se 3 (by rfl) ⟨107294, by rfl⟩ : syracuseStep 572237 = 214589) B214589
theorem B867185 : Blo 167798 867185 := bstep (se 2 (by rfl) ⟨325194, by rfl⟩ : syracuseStep 867185 = 650389) B650389
theorem B572291 : Blo 167798 572291 := bstep (se 1 (by rfl) ⟨429218, by rfl⟩ : syracuseStep 572291 = 858437) B858437
theorem B572561 : Blo 167798 572561 := bstep (se 2 (by rfl) ⟨214710, by rfl⟩ : syracuseStep 572561 = 429421) B429421
theorem B539939 : Blo 167798 539939 := bstep (se 1 (by rfl) ⟨404954, by rfl⟩ : syracuseStep 539939 = 809909) B809909
theorem B179539 : Blo 167798 179539 := bstep (se 1 (by rfl) ⟨134654, by rfl⟩ : syracuseStep 179539 = 269309) B269309
theorem B1457635 : Blo 167798 1457635 := bstep (se 1 (by rfl) ⟨1093226, by rfl⟩ : syracuseStep 1457635 = 2186453) B2186453
theorem B212483 : Blo 167798 212483 := bstep (se 1 (by rfl) ⟨159362, by rfl⟩ : syracuseStep 212483 = 318725) B318725
theorem B638513 : Blo 167798 638513 := bstep (se 2 (by rfl) ⟨239442, by rfl⟩ : syracuseStep 638513 = 478885) B478885
theorem B573101 : Blo 167798 573101 := bstep (se 3 (by rfl) ⟨107456, by rfl⟩ : syracuseStep 573101 = 214913) B214913
theorem B573155 : Blo 167798 573155 := bstep (se 1 (by rfl) ⟨429866, by rfl⟩ : syracuseStep 573155 = 859733) B859733
theorem B966563 : Blo 167798 966563 := bstep (se 1 (by rfl) ⟨724922, by rfl⟩ : syracuseStep 966563 = 1449845) B1449845
theorem B573425 : Blo 167798 573425 := bstep (se 2 (by rfl) ⟨215034, by rfl⟩ : syracuseStep 573425 = 430069) B430069
theorem B213187 : Blo 167798 213187 := bstep (se 1 (by rfl) ⟨159890, by rfl⟩ : syracuseStep 213187 = 319781) B319781
theorem B213283 : Blo 167798 213283 := bstep (se 1 (by rfl) ⟨159962, by rfl⟩ : syracuseStep 213283 = 319925) B319925
theorem B868643 : Blo 167798 868643 := bstep (se 1 (by rfl) ⟨651482, by rfl⟩ : syracuseStep 868643 = 1302965) B1302965
theorem B1982789 : Blo 167798 1982789 := bstep (se 4 (by rfl) ⟨185886, by rfl⟩ : syracuseStep 1982789 = 371773) B371773
theorem B573965 : Blo 167798 573965 := bstep (se 3 (by rfl) ⟨107618, by rfl⟩ : syracuseStep 573965 = 215237) B215237
theorem B410179 : Blo 167798 410179 := bstep (se 1 (by rfl) ⟨307634, by rfl⟩ : syracuseStep 410179 = 615269) B615269
theorem B574019 : Blo 167798 574019 := bstep (se 1 (by rfl) ⟨430514, by rfl⟩ : syracuseStep 574019 = 861029) B861029
theorem B1098353 : Blo 167798 1098353 := bstep (se 2 (by rfl) ⟨411882, by rfl⟩ : syracuseStep 1098353 = 823765) B823765
theorem B377585 : Blo 167798 377585 := bstep (se 2 (by rfl) ⟨141594, by rfl⟩ : syracuseStep 377585 = 283189) B283189
theorem B377603 : Blo 167798 377603 := bstep (se 1 (by rfl) ⟨283202, by rfl⟩ : syracuseStep 377603 = 566405) B566405
theorem B213779 : Blo 167798 213779 := bstep (se 1 (by rfl) ⟨160334, by rfl⟩ : syracuseStep 213779 = 320669) B320669
theorem B574289 : Blo 167798 574289 := bstep (se 2 (by rfl) ⟨215358, by rfl⟩ : syracuseStep 574289 = 430717) B430717
theorem B967565 : Blo 167798 967565 := bstep (se 3 (by rfl) ⟨181418, by rfl⟩ : syracuseStep 967565 = 362837) B362837
theorem B639971 : Blo 167798 639971 := bstep (se 1 (by rfl) ⟨479978, by rfl⟩ : syracuseStep 639971 = 959957) B959957
theorem B377873 : Blo 167798 377873 := bstep (se 2 (by rfl) ⟨141702, by rfl⟩ : syracuseStep 377873 = 283405) B283405
theorem B377891 : Blo 167798 377891 := bstep (se 1 (by rfl) ⟨283418, by rfl⟩ : syracuseStep 377891 = 566837) B566837
theorem B869453 : Blo 167798 869453 := bstep (se 3 (by rfl) ⟨163022, by rfl⟩ : syracuseStep 869453 = 326045) B326045
theorem B312419 : Blo 167798 312419 := bstep (se 1 (by rfl) ⟨234314, by rfl⟩ : syracuseStep 312419 = 468629) B468629
theorem B378161 : Blo 167798 378161 := bstep (se 2 (by rfl) ⟨141810, by rfl⟩ : syracuseStep 378161 = 283621) B283621
theorem B378179 : Blo 167798 378179 := bstep (se 1 (by rfl) ⟨283634, by rfl⟩ : syracuseStep 378179 = 567269) B567269
theorem B574829 : Blo 167798 574829 := bstep (se 3 (by rfl) ⟨107780, by rfl⟩ : syracuseStep 574829 = 215561) B215561
theorem B574883 : Blo 167798 574883 := bstep (se 1 (by rfl) ⟨431162, by rfl⟩ : syracuseStep 574883 = 862325) B862325
theorem B247249 : Blo 167798 247249 := bstep (se 2 (by rfl) ⟨92718, by rfl⟩ : syracuseStep 247249 = 185437) B185437
theorem B214483 : Blo 167798 214483 := bstep (se 1 (by rfl) ⟨160862, by rfl⟩ : syracuseStep 214483 = 321725) B321725
theorem B1099277 : Blo 167798 1099277 := bstep (se 3 (by rfl) ⟨206114, by rfl⟩ : syracuseStep 1099277 = 412229) B412229
theorem B214579 : Blo 167798 214579 := bstep (se 1 (by rfl) ⟨160934, by rfl⟩ : syracuseStep 214579 = 321869) B321869
theorem B378449 : Blo 167798 378449 := bstep (se 2 (by rfl) ⟨141918, by rfl⟩ : syracuseStep 378449 = 283837) B283837
theorem B378467 : Blo 167798 378467 := bstep (se 1 (by rfl) ⟨283850, by rfl⟩ : syracuseStep 378467 = 567701) B567701
theorem B575153 : Blo 167798 575153 := bstep (se 2 (by rfl) ⟨215682, by rfl⟩ : syracuseStep 575153 = 431365) B431365
theorem B542513 : Blo 167798 542513 := bstep (se 2 (by rfl) ⟨203442, by rfl⟩ : syracuseStep 542513 = 406885) B406885
theorem B378737 : Blo 167798 378737 := bstep (se 2 (by rfl) ⟨142026, by rfl⟩ : syracuseStep 378737 = 284053) B284053
theorem B378755 : Blo 167798 378755 := bstep (se 1 (by rfl) ⟨284066, by rfl⟩ : syracuseStep 378755 = 568133) B568133
theorem B1034117 : Blo 167798 1034117 := bstep (se 4 (by rfl) ⟨96948, by rfl⟩ : syracuseStep 1034117 = 193897) B193897
theorem B182179 : Blo 167798 182179 := bstep (se 1 (by rfl) ⟨136634, by rfl⟩ : syracuseStep 182179 = 273269) B273269
theorem B640973 : Blo 167798 640973 := bstep (se 3 (by rfl) ⟨120182, by rfl⟩ : syracuseStep 640973 = 240365) B240365
theorem B215075 : Blo 167798 215075 := bstep (se 1 (by rfl) ⟨161306, by rfl⟩ : syracuseStep 215075 = 322613) B322613
theorem B379025 : Blo 167798 379025 := bstep (se 2 (by rfl) ⟨142134, by rfl⟩ : syracuseStep 379025 = 284269) B284269
theorem B379043 : Blo 167798 379043 := bstep (se 1 (by rfl) ⟨284282, by rfl⟩ : syracuseStep 379043 = 568565) B568565
theorem B575693 : Blo 167798 575693 := bstep (se 3 (by rfl) ⟨107942, by rfl⟩ : syracuseStep 575693 = 215885) B215885
theorem B411875 : Blo 167798 411875 := bstep (se 1 (by rfl) ⟨308906, by rfl⟩ : syracuseStep 411875 = 617813) B617813
theorem B1755377 : Blo 167798 1755377 := bstep (se 2 (by rfl) ⟨658266, by rfl⟩ : syracuseStep 1755377 = 1316533) B1316533
theorem B575747 : Blo 167798 575747 := bstep (se 1 (by rfl) ⟨431810, by rfl⟩ : syracuseStep 575747 = 863621) B863621
theorem B182611 : Blo 167798 182611 := bstep (se 1 (by rfl) ⟨136958, by rfl⟩ : syracuseStep 182611 = 273917) B273917
theorem B1821041 : Blo 167798 1821041 := bstep (se 2 (by rfl) ⟨682890, by rfl⟩ : syracuseStep 1821041 = 1365781) B1365781
theorem B379313 : Blo 167798 379313 := bstep (se 2 (by rfl) ⟨142242, by rfl⟩ : syracuseStep 379313 = 284485) B284485
theorem B379331 : Blo 167798 379331 := bstep (se 1 (by rfl) ⟨284498, by rfl⟩ : syracuseStep 379331 = 568997) B568997
theorem B576017 : Blo 167798 576017 := bstep (se 2 (by rfl) ⟨216006, by rfl⟩ : syracuseStep 576017 = 432013) B432013
theorem B871117 : Blo 167798 871117 := bstep (se 3 (by rfl) ⟨163334, by rfl⟩ : syracuseStep 871117 = 326669) B326669
theorem B379601 : Blo 167798 379601 := bstep (se 2 (by rfl) ⟨142350, by rfl⟩ : syracuseStep 379601 = 284701) B284701
theorem B379619 : Blo 167798 379619 := bstep (se 1 (by rfl) ⟨284714, by rfl⟩ : syracuseStep 379619 = 569429) B569429
theorem B215779 : Blo 167798 215779 := bstep (se 1 (by rfl) ⟨161834, by rfl⟩ : syracuseStep 215779 = 323669) B323669
theorem B609059 : Blo 167798 609059 := bstep (se 1 (by rfl) ⟨456794, by rfl⟩ : syracuseStep 609059 = 913589) B913589
theorem B215875 : Blo 167798 215875 := bstep (se 1 (by rfl) ⟨161906, by rfl⟩ : syracuseStep 215875 = 323813) B323813
theorem B379889 : Blo 167798 379889 := bstep (se 2 (by rfl) ⟨142458, by rfl⟩ : syracuseStep 379889 = 284917) B284917
theorem B379907 : Blo 167798 379907 := bstep (se 1 (by rfl) ⟨284930, by rfl⟩ : syracuseStep 379907 = 569861) B569861
theorem B576557 : Blo 167798 576557 := bstep (se 3 (by rfl) ⟨108104, by rfl⟩ : syracuseStep 576557 = 216209) B216209
theorem B412721 : Blo 167798 412721 := bstep (se 2 (by rfl) ⟨154770, by rfl⟩ : syracuseStep 412721 = 309541) B309541
theorem B576611 : Blo 167798 576611 := bstep (se 1 (by rfl) ⟨432458, by rfl⟩ : syracuseStep 576611 = 864917) B864917
theorem B216307 : Blo 167798 216307 := bstep (se 1 (by rfl) ⟨162230, by rfl⟩ : syracuseStep 216307 = 324461) B324461
theorem B380177 : Blo 167798 380177 := bstep (se 2 (by rfl) ⟨142566, by rfl⟩ : syracuseStep 380177 = 285133) B285133
theorem B380195 : Blo 167798 380195 := bstep (se 1 (by rfl) ⟨285146, by rfl⟩ : syracuseStep 380195 = 570293) B570293
theorem B216371 : Blo 167798 216371 := bstep (se 1 (by rfl) ⟨162278, by rfl⟩ : syracuseStep 216371 = 324557) B324557
theorem B3231089 : Blo 167798 3231089 := bstep (se 2 (by rfl) ⟨1211658, by rfl⟩ : syracuseStep 3231089 = 2423317) B2423317
theorem B576881 : Blo 167798 576881 := bstep (se 2 (by rfl) ⟨216330, by rfl⟩ : syracuseStep 576881 = 432661) B432661
theorem B478669 : Blo 167798 478669 := bstep (se 3 (by rfl) ⟨89750, by rfl⟩ : syracuseStep 478669 = 179501) B179501
theorem B380465 : Blo 167798 380465 := bstep (se 2 (by rfl) ⟨142674, by rfl⟩ : syracuseStep 380465 = 285349) B285349
theorem B577091 : Blo 167798 577091 := bstep (se 1 (by rfl) ⟨432818, by rfl⟩ : syracuseStep 577091 = 865637) B865637
theorem B380483 : Blo 167798 380483 := bstep (se 1 (by rfl) ⟨285362, by rfl⟩ : syracuseStep 380483 = 570725) B570725
theorem B970481 : Blo 167798 970481 := bstep (se 2 (by rfl) ⟨363930, by rfl⟩ : syracuseStep 970481 = 727861) B727861
theorem B741155 : Blo 167798 741155 := bstep (se 1 (by rfl) ⟨555866, by rfl⟩ : syracuseStep 741155 = 1111733) B1111733
theorem B380753 : Blo 167798 380753 := bstep (se 2 (by rfl) ⟨142782, by rfl⟩ : syracuseStep 380753 = 285565) B285565
theorem B380771 : Blo 167798 380771 := bstep (se 1 (by rfl) ⟨285578, by rfl⟩ : syracuseStep 380771 = 571157) B571157
theorem B577421 : Blo 167798 577421 := bstep (se 3 (by rfl) ⟨108266, by rfl⟩ : syracuseStep 577421 = 216533) B216533
theorem B577475 : Blo 167798 577475 := bstep (se 1 (by rfl) ⟨433106, by rfl⟩ : syracuseStep 577475 = 866213) B866213
theorem B217075 : Blo 167798 217075 := bstep (se 1 (by rfl) ⟨162806, by rfl⟩ : syracuseStep 217075 = 325613) B325613
theorem B643085 : Blo 167798 643085 := bstep (se 3 (by rfl) ⟨120578, by rfl⟩ : syracuseStep 643085 = 241157) B241157
theorem B217171 : Blo 167798 217171 := bstep (se 1 (by rfl) ⟨162878, by rfl⟩ : syracuseStep 217171 = 325757) B325757
theorem B381041 : Blo 167798 381041 := bstep (se 2 (by rfl) ⟨142890, by rfl⟩ : syracuseStep 381041 = 285781) B285781
theorem B381059 : Blo 167798 381059 := bstep (se 1 (by rfl) ⟨285794, by rfl⟩ : syracuseStep 381059 = 571589) B571589
theorem B184483 : Blo 167798 184483 := bstep (se 1 (by rfl) ⟨138362, by rfl⟩ : syracuseStep 184483 = 276725) B276725
theorem B544973 : Blo 167798 544973 := bstep (se 3 (by rfl) ⟨102182, by rfl⟩ : syracuseStep 544973 = 204365) B204365
theorem B577745 : Blo 167798 577745 := bstep (se 2 (by rfl) ⟨216654, by rfl⟩ : syracuseStep 577745 = 433309) B433309
theorem B381329 : Blo 167798 381329 := bstep (se 2 (by rfl) ⟨142998, by rfl⟩ : syracuseStep 381329 = 285997) B285997
theorem B381347 : Blo 167798 381347 := bstep (se 1 (by rfl) ⟨286010, by rfl⟩ : syracuseStep 381347 = 572021) B572021
theorem B1036741 : Blo 167798 1036741 := bstep (se 4 (by rfl) ⟨97194, by rfl⟩ : syracuseStep 1036741 = 194389) B194389
theorem B283169 : Blo 167798 283169 := bstep (se 2 (by rfl) ⟨106188, by rfl⟩ : syracuseStep 283169 = 212377) B212377
theorem B283297 : Blo 167798 283297 := bstep (se 2 (by rfl) ⟨106236, by rfl⟩ : syracuseStep 283297 = 212473) B212473
theorem B381617 : Blo 167798 381617 := bstep (se 2 (by rfl) ⟨143106, by rfl⟩ : syracuseStep 381617 = 286213) B286213
theorem B283331 : Blo 167798 283331 := bstep (se 1 (by rfl) ⟨212498, by rfl⟩ : syracuseStep 283331 = 424997) B424997
theorem B381635 : Blo 167798 381635 := bstep (se 1 (by rfl) ⟨286226, by rfl⟩ : syracuseStep 381635 = 572453) B572453
theorem B578285 : Blo 167798 578285 := bstep (se 3 (by rfl) ⟨108428, by rfl⟩ : syracuseStep 578285 = 216857) B216857
theorem B1168141 : Blo 167798 1168141 := bstep (se 3 (by rfl) ⟨219026, by rfl⟩ : syracuseStep 1168141 = 438053) B438053
theorem B578339 : Blo 167798 578339 := bstep (se 1 (by rfl) ⟨433754, by rfl⟩ : syracuseStep 578339 = 867509) B867509
theorem B643889 : Blo 167798 643889 := bstep (se 2 (by rfl) ⟨241458, by rfl⟩ : syracuseStep 643889 = 482917) B482917
theorem B283459 : Blo 167798 283459 := bstep (se 1 (by rfl) ⟨212594, by rfl⟩ : syracuseStep 283459 = 425189) B425189
theorem B283601 : Blo 167798 283601 := bstep (se 2 (by rfl) ⟨106350, by rfl⟩ : syracuseStep 283601 = 212701) B212701
theorem B381905 : Blo 167798 381905 := bstep (se 2 (by rfl) ⟨143214, by rfl⟩ : syracuseStep 381905 = 286429) B286429
theorem B381923 : Blo 167798 381923 := bstep (se 1 (by rfl) ⟨286442, by rfl⟩ : syracuseStep 381923 = 572885) B572885
theorem B578609 : Blo 167798 578609 := bstep (se 2 (by rfl) ⟨216978, by rfl⟩ : syracuseStep 578609 = 433957) B433957
theorem B283729 : Blo 167798 283729 := bstep (se 2 (by rfl) ⟨106398, by rfl⟩ : syracuseStep 283729 = 212797) B212797
theorem B283763 : Blo 167798 283763 := bstep (se 1 (by rfl) ⟨212822, by rfl⟩ : syracuseStep 283763 = 425645) B425645
theorem B480401 : Blo 167798 480401 := bstep (se 2 (by rfl) ⟨180150, by rfl⟩ : syracuseStep 480401 = 360301) B360301
theorem B971939 : Blo 167798 971939 := bstep (se 1 (by rfl) ⟨728954, by rfl⟩ : syracuseStep 971939 = 1457909) B1457909
theorem B382193 : Blo 167798 382193 := bstep (se 2 (by rfl) ⟨143322, by rfl⟩ : syracuseStep 382193 = 286645) B286645
theorem B283891 : Blo 167798 283891 := bstep (se 1 (by rfl) ⟨212918, by rfl⟩ : syracuseStep 283891 = 425837) B425837
theorem B382211 : Blo 167798 382211 := bstep (se 1 (by rfl) ⟨286658, by rfl⟩ : syracuseStep 382211 = 573317) B573317
theorem B480593 : Blo 167798 480593 := bstep (se 2 (by rfl) ⟨180222, by rfl⟩ : syracuseStep 480593 = 360445) B360445
theorem B284033 : Blo 167798 284033 := bstep (se 2 (by rfl) ⟨106512, by rfl⟩ : syracuseStep 284033 = 213025) B213025
theorem B644557 : Blo 167798 644557 := bstep (se 3 (by rfl) ⟨120854, by rfl⟩ : syracuseStep 644557 = 241709) B241709
theorem B284161 : Blo 167798 284161 := bstep (se 2 (by rfl) ⟨106560, by rfl⟩ : syracuseStep 284161 = 213121) B213121
theorem B382481 : Blo 167798 382481 := bstep (se 2 (by rfl) ⟨143430, by rfl⟩ : syracuseStep 382481 = 286861) B286861
theorem B284195 : Blo 167798 284195 := bstep (se 1 (by rfl) ⟨213146, by rfl⟩ : syracuseStep 284195 = 426293) B426293
theorem B382499 : Blo 167798 382499 := bstep (se 1 (by rfl) ⟨286874, by rfl⟩ : syracuseStep 382499 = 573749) B573749
theorem B579149 : Blo 167798 579149 := bstep (se 3 (by rfl) ⟨108590, by rfl⟩ : syracuseStep 579149 = 217181) B217181
theorem B579203 : Blo 167798 579203 := bstep (se 1 (by rfl) ⟨434402, by rfl⟩ : syracuseStep 579203 = 868805) B868805
theorem B284323 : Blo 167798 284323 := bstep (se 1 (by rfl) ⟨213242, by rfl⟩ : syracuseStep 284323 = 426485) B426485
theorem B546563 : Blo 167798 546563 := bstep (se 1 (by rfl) ⟨409922, by rfl⟩ : syracuseStep 546563 = 819845) B819845
theorem B284465 : Blo 167798 284465 := bstep (se 2 (by rfl) ⟨106674, by rfl⟩ : syracuseStep 284465 = 213349) B213349
theorem B382769 : Blo 167798 382769 := bstep (se 2 (by rfl) ⟨143538, by rfl⟩ : syracuseStep 382769 = 287077) B287077
theorem B251699 : Blo 167798 251699 := bstep (se 1 (by rfl) ⟨188774, by rfl⟩ : syracuseStep 251699 = 377549) B377549
theorem B382787 : Blo 167798 382787 := bstep (se 1 (by rfl) ⟨287090, by rfl⟩ : syracuseStep 382787 = 574181) B574181
theorem B612173 : Blo 167798 612173 := bstep (se 3 (by rfl) ⟨114782, by rfl⟩ : syracuseStep 612173 = 229565) B229565
theorem B251729 : Blo 167798 251729 := bstep (se 2 (by rfl) ⟨94398, by rfl⟩ : syracuseStep 251729 = 188797) B188797
theorem B251747 : Blo 167798 251747 := bstep (se 1 (by rfl) ⟨188810, by rfl⟩ : syracuseStep 251747 = 377621) B377621
theorem B251777 : Blo 167798 251777 := bstep (se 2 (by rfl) ⟨94416, by rfl⟩ : syracuseStep 251777 = 188833) B188833
theorem B579473 : Blo 167798 579473 := bstep (se 2 (by rfl) ⟨217302, by rfl⟩ : syracuseStep 579473 = 434605) B434605
theorem B251795 : Blo 167798 251795 := bstep (se 1 (by rfl) ⟨188846, by rfl⟩ : syracuseStep 251795 = 377693) B377693
theorem B251825 : Blo 167798 251825 := bstep (se 2 (by rfl) ⟨94434, by rfl⟩ : syracuseStep 251825 = 188869) B188869
theorem B284593 : Blo 167798 284593 := bstep (se 2 (by rfl) ⟨106722, by rfl⟩ : syracuseStep 284593 = 213445) B213445
theorem B251843 : Blo 167798 251843 := bstep (se 1 (by rfl) ⟨188882, by rfl⟩ : syracuseStep 251843 = 377765) B377765
theorem B284627 : Blo 167798 284627 := bstep (se 1 (by rfl) ⟨213470, by rfl⟩ : syracuseStep 284627 = 426941) B426941
theorem B251873 : Blo 167798 251873 := bstep (se 2 (by rfl) ⟨94452, by rfl⟩ : syracuseStep 251873 = 188905) B188905
theorem B251891 : Blo 167798 251891 := bstep (se 1 (by rfl) ⟨188918, by rfl⟩ : syracuseStep 251891 = 377837) B377837
theorem B251921 : Blo 167798 251921 := bstep (se 2 (by rfl) ⟨94470, by rfl⟩ : syracuseStep 251921 = 188941) B188941
theorem B251939 : Blo 167798 251939 := bstep (se 1 (by rfl) ⟨188954, by rfl⟩ : syracuseStep 251939 = 377909) B377909
theorem B251969 : Blo 167798 251969 := bstep (se 2 (by rfl) ⟨94488, by rfl⟩ : syracuseStep 251969 = 188977) B188977
theorem B383057 : Blo 167798 383057 := bstep (se 2 (by rfl) ⟨143646, by rfl⟩ : syracuseStep 383057 = 287293) B287293
theorem B251987 : Blo 167798 251987 := bstep (se 1 (by rfl) ⟨188990, by rfl⟩ : syracuseStep 251987 = 377981) B377981
theorem B284755 : Blo 167798 284755 := bstep (se 1 (by rfl) ⟨213566, by rfl⟩ : syracuseStep 284755 = 427133) B427133
theorem B383075 : Blo 167798 383075 := bstep (se 1 (by rfl) ⟨287306, by rfl⟩ : syracuseStep 383075 = 574613) B574613
theorem B252017 : Blo 167798 252017 := bstep (se 2 (by rfl) ⟨94506, by rfl⟩ : syracuseStep 252017 = 189013) B189013
theorem B252035 : Blo 167798 252035 := bstep (se 1 (by rfl) ⟨189026, by rfl⟩ : syracuseStep 252035 = 378053) B378053
theorem B252065 : Blo 167798 252065 := bstep (se 2 (by rfl) ⟨94524, by rfl⟩ : syracuseStep 252065 = 189049) B189049
theorem B252083 : Blo 167798 252083 := bstep (se 1 (by rfl) ⟨189062, by rfl⟩ : syracuseStep 252083 = 378125) B378125
theorem B252113 : Blo 167798 252113 := bstep (se 2 (by rfl) ⟨94542, by rfl⟩ : syracuseStep 252113 = 189085) B189085
theorem B284897 : Blo 167798 284897 := bstep (se 2 (by rfl) ⟨106836, by rfl⟩ : syracuseStep 284897 = 213673) B213673
theorem B252131 : Blo 167798 252131 := bstep (se 1 (by rfl) ⟨189098, by rfl⟩ : syracuseStep 252131 = 378197) B378197
theorem B645347 : Blo 167798 645347 := bstep (se 1 (by rfl) ⟨484010, by rfl⟩ : syracuseStep 645347 = 968021) B968021
theorem B252161 : Blo 167798 252161 := bstep (se 2 (by rfl) ⟨94560, by rfl⟩ : syracuseStep 252161 = 189121) B189121
theorem B776461 : Blo 167798 776461 := bstep (se 3 (by rfl) ⟨145586, by rfl⟩ : syracuseStep 776461 = 291173) B291173
theorem B252179 : Blo 167798 252179 := bstep (se 1 (by rfl) ⟨189134, by rfl⟩ : syracuseStep 252179 = 378269) B378269
theorem B252209 : Blo 167798 252209 := bstep (se 2 (by rfl) ⟨94578, by rfl⟩ : syracuseStep 252209 = 189157) B189157
theorem B481585 : Blo 167798 481585 := bstep (se 2 (by rfl) ⟨180594, by rfl⟩ : syracuseStep 481585 = 361189) B361189
theorem B252227 : Blo 167798 252227 := bstep (se 1 (by rfl) ⟨189170, by rfl⟩ : syracuseStep 252227 = 378341) B378341
theorem B252257 : Blo 167798 252257 := bstep (se 2 (by rfl) ⟨94596, by rfl⟩ : syracuseStep 252257 = 189193) B189193
theorem B285025 : Blo 167798 285025 := bstep (se 2 (by rfl) ⟨106884, by rfl⟩ : syracuseStep 285025 = 213769) B213769
theorem B383345 : Blo 167798 383345 := bstep (se 2 (by rfl) ⟨143754, by rfl⟩ : syracuseStep 383345 = 287509) B287509
theorem B252275 : Blo 167798 252275 := bstep (se 1 (by rfl) ⟨189206, by rfl⟩ : syracuseStep 252275 = 378413) B378413
theorem B285059 : Blo 167798 285059 := bstep (se 1 (by rfl) ⟨213794, by rfl⟩ : syracuseStep 285059 = 427589) B427589
theorem B383363 : Blo 167798 383363 := bstep (se 1 (by rfl) ⟨287522, by rfl⟩ : syracuseStep 383363 = 575045) B575045
theorem B252305 : Blo 167798 252305 := bstep (se 2 (by rfl) ⟨94614, by rfl⟩ : syracuseStep 252305 = 189229) B189229
theorem B252323 : Blo 167798 252323 := bstep (se 1 (by rfl) ⟨189242, by rfl⟩ : syracuseStep 252323 = 378485) B378485
theorem B252353 : Blo 167798 252353 := bstep (se 2 (by rfl) ⟨94632, by rfl⟩ : syracuseStep 252353 = 189265) B189265
theorem B252371 : Blo 167798 252371 := bstep (se 1 (by rfl) ⟨189278, by rfl⟩ : syracuseStep 252371 = 378557) B378557
theorem B252401 : Blo 167798 252401 := bstep (se 2 (by rfl) ⟨94650, by rfl⟩ : syracuseStep 252401 = 189301) B189301
theorem B252419 : Blo 167798 252419 := bstep (se 1 (by rfl) ⟨189314, by rfl⟩ : syracuseStep 252419 = 378629) B378629
theorem B285187 : Blo 167798 285187 := bstep (se 1 (by rfl) ⟨213890, by rfl⟩ : syracuseStep 285187 = 427781) B427781
theorem B252449 : Blo 167798 252449 := bstep (se 2 (by rfl) ⟨94668, by rfl⟩ : syracuseStep 252449 = 189337) B189337
theorem B252467 : Blo 167798 252467 := bstep (se 1 (by rfl) ⟨189350, by rfl⟩ : syracuseStep 252467 = 378701) B378701
theorem B481859 : Blo 167798 481859 := bstep (se 1 (by rfl) ⟨361394, by rfl⟩ : syracuseStep 481859 = 722789) B722789
theorem B252497 : Blo 167798 252497 := bstep (se 2 (by rfl) ⟨94686, by rfl⟩ : syracuseStep 252497 = 189373) B189373
theorem B252515 : Blo 167798 252515 := bstep (se 1 (by rfl) ⟨189386, by rfl⟩ : syracuseStep 252515 = 378773) B378773
theorem B252545 : Blo 167798 252545 := bstep (se 2 (by rfl) ⟨94704, by rfl⟩ : syracuseStep 252545 = 189409) B189409
theorem B285329 : Blo 167798 285329 := bstep (se 2 (by rfl) ⟨106998, by rfl⟩ : syracuseStep 285329 = 213997) B213997
theorem B383633 : Blo 167798 383633 := bstep (se 2 (by rfl) ⟨143862, by rfl⟩ : syracuseStep 383633 = 287725) B287725
theorem B252563 : Blo 167798 252563 := bstep (se 1 (by rfl) ⟨189422, by rfl⟩ : syracuseStep 252563 = 378845) B378845
theorem B383651 : Blo 167798 383651 := bstep (se 1 (by rfl) ⟨287738, by rfl⟩ : syracuseStep 383651 = 575477) B575477
theorem B252593 : Blo 167798 252593 := bstep (se 2 (by rfl) ⟨94722, by rfl⟩ : syracuseStep 252593 = 189445) B189445
theorem B252611 : Blo 167798 252611 := bstep (se 1 (by rfl) ⟨189458, by rfl⟩ : syracuseStep 252611 = 378917) B378917
theorem B252641 : Blo 167798 252641 := bstep (se 2 (by rfl) ⟨94740, by rfl⟩ : syracuseStep 252641 = 189481) B189481
theorem B252659 : Blo 167798 252659 := bstep (se 1 (by rfl) ⟨189494, by rfl⟩ : syracuseStep 252659 = 378989) B378989
theorem B482051 : Blo 167798 482051 := bstep (se 1 (by rfl) ⟨361538, by rfl⟩ : syracuseStep 482051 = 723077) B723077
theorem B252689 : Blo 167798 252689 := bstep (se 2 (by rfl) ⟨94758, by rfl⟩ : syracuseStep 252689 = 189517) B189517
theorem B285457 : Blo 167798 285457 := bstep (se 2 (by rfl) ⟨107046, by rfl⟩ : syracuseStep 285457 = 214093) B214093
theorem B252707 : Blo 167798 252707 := bstep (se 1 (by rfl) ⟨189530, by rfl⟩ : syracuseStep 252707 = 379061) B379061
theorem B285491 : Blo 167798 285491 := bstep (se 1 (by rfl) ⟨214118, by rfl⟩ : syracuseStep 285491 = 428237) B428237
theorem B252737 : Blo 167798 252737 := bstep (se 2 (by rfl) ⟨94776, by rfl⟩ : syracuseStep 252737 = 189553) B189553
theorem B645965 : Blo 167798 645965 := bstep (se 3 (by rfl) ⟨121118, by rfl⟩ : syracuseStep 645965 = 242237) B242237
theorem B252755 : Blo 167798 252755 := bstep (se 1 (by rfl) ⟨189566, by rfl⟩ : syracuseStep 252755 = 379133) B379133
theorem B252785 : Blo 167798 252785 := bstep (se 2 (by rfl) ⟨94794, by rfl⟩ : syracuseStep 252785 = 189589) B189589
theorem B646001 : Blo 167798 646001 := bstep (se 2 (by rfl) ⟨242250, by rfl⟩ : syracuseStep 646001 = 484501) B484501
theorem B252803 : Blo 167798 252803 := bstep (se 1 (by rfl) ⟨189602, by rfl⟩ : syracuseStep 252803 = 379205) B379205
theorem B252833 : Blo 167798 252833 := bstep (se 2 (by rfl) ⟨94812, by rfl⟩ : syracuseStep 252833 = 189625) B189625
theorem B383921 : Blo 167798 383921 := bstep (se 2 (by rfl) ⟨143970, by rfl⟩ : syracuseStep 383921 = 287941) B287941
theorem B252851 : Blo 167798 252851 := bstep (se 1 (by rfl) ⟨189638, by rfl⟩ : syracuseStep 252851 = 379277) B379277
theorem B285619 : Blo 167798 285619 := bstep (se 1 (by rfl) ⟨214214, by rfl⟩ : syracuseStep 285619 = 428429) B428429
theorem B383939 : Blo 167798 383939 := bstep (se 1 (by rfl) ⟨287954, by rfl⟩ : syracuseStep 383939 = 575909) B575909
theorem B252881 : Blo 167798 252881 := bstep (se 2 (by rfl) ⟨94830, by rfl⟩ : syracuseStep 252881 = 189661) B189661
theorem B547793 : Blo 167798 547793 := bstep (se 2 (by rfl) ⟨205422, by rfl⟩ : syracuseStep 547793 = 410845) B410845
theorem B252899 : Blo 167798 252899 := bstep (se 1 (by rfl) ⟨189674, by rfl⟩ : syracuseStep 252899 = 379349) B379349
theorem B908273 : Blo 167798 908273 := bstep (se 2 (by rfl) ⟨340602, by rfl⟩ : syracuseStep 908273 = 681205) B681205
theorem B252929 : Blo 167798 252929 := bstep (se 2 (by rfl) ⟨94848, by rfl⟩ : syracuseStep 252929 = 189697) B189697
theorem B252947 : Blo 167798 252947 := bstep (se 1 (by rfl) ⟨189710, by rfl⟩ : syracuseStep 252947 = 379421) B379421
theorem B252977 : Blo 167798 252977 := bstep (se 2 (by rfl) ⟨94866, by rfl⟩ : syracuseStep 252977 = 189733) B189733
theorem B285761 : Blo 167798 285761 := bstep (se 2 (by rfl) ⟨107160, by rfl⟩ : syracuseStep 285761 = 214321) B214321
theorem B252995 : Blo 167798 252995 := bstep (se 1 (by rfl) ⟨189746, by rfl⟩ : syracuseStep 252995 = 379493) B379493
theorem B253025 : Blo 167798 253025 := bstep (se 2 (by rfl) ⟨94884, by rfl⟩ : syracuseStep 253025 = 189769) B189769
theorem B253043 : Blo 167798 253043 := bstep (se 1 (by rfl) ⟨189782, by rfl⟩ : syracuseStep 253043 = 379565) B379565
theorem B253073 : Blo 167798 253073 := bstep (se 2 (by rfl) ⟨94902, by rfl⟩ : syracuseStep 253073 = 189805) B189805
theorem B253091 : Blo 167798 253091 := bstep (se 1 (by rfl) ⟨189818, by rfl⟩ : syracuseStep 253091 = 379637) B379637
theorem B253121 : Blo 167798 253121 := bstep (se 2 (by rfl) ⟨94920, by rfl⟩ : syracuseStep 253121 = 189841) B189841
theorem B285889 : Blo 167798 285889 := bstep (se 2 (by rfl) ⟨107208, by rfl⟩ : syracuseStep 285889 = 214417) B214417
theorem B384209 : Blo 167798 384209 := bstep (se 2 (by rfl) ⟨144078, by rfl⟩ : syracuseStep 384209 = 288157) B288157
theorem B253139 : Blo 167798 253139 := bstep (se 1 (by rfl) ⟨189854, by rfl⟩ : syracuseStep 253139 = 379709) B379709
theorem B285923 : Blo 167798 285923 := bstep (se 1 (by rfl) ⟨214442, by rfl⟩ : syracuseStep 285923 = 428885) B428885
theorem B384227 : Blo 167798 384227 := bstep (se 1 (by rfl) ⟨288170, by rfl⟩ : syracuseStep 384227 = 576341) B576341
theorem B253169 : Blo 167798 253169 := bstep (se 2 (by rfl) ⟨94938, by rfl⟩ : syracuseStep 253169 = 189877) B189877
theorem B253187 : Blo 167798 253187 := bstep (se 1 (by rfl) ⟨189890, by rfl⟩ : syracuseStep 253187 = 379781) B379781
theorem B253217 : Blo 167798 253217 := bstep (se 2 (by rfl) ⟨94956, by rfl⟩ : syracuseStep 253217 = 189913) B189913
theorem B318755 : Blo 167798 318755 := bstep (se 1 (by rfl) ⟨239066, by rfl⟩ : syracuseStep 318755 = 478133) B478133
theorem B253235 : Blo 167798 253235 := bstep (se 1 (by rfl) ⟨189926, by rfl⟩ : syracuseStep 253235 = 379853) B379853
theorem B253265 : Blo 167798 253265 := bstep (se 2 (by rfl) ⟨94974, by rfl⟩ : syracuseStep 253265 = 189949) B189949
theorem B253283 : Blo 167798 253283 := bstep (se 1 (by rfl) ⟨189962, by rfl⟩ : syracuseStep 253283 = 379925) B379925
theorem B286051 : Blo 167798 286051 := bstep (se 1 (by rfl) ⟨214538, by rfl⟩ : syracuseStep 286051 = 429077) B429077
theorem B253313 : Blo 167798 253313 := bstep (se 2 (by rfl) ⟨94992, by rfl⟩ : syracuseStep 253313 = 189985) B189985
theorem B253331 : Blo 167798 253331 := bstep (se 1 (by rfl) ⟨189998, by rfl⟩ : syracuseStep 253331 = 379997) B379997
theorem B515501 : Blo 167798 515501 := bstep (se 3 (by rfl) ⟨96656, by rfl⟩ : syracuseStep 515501 = 193313) B193313
theorem B253361 : Blo 167798 253361 := bstep (se 2 (by rfl) ⟨95010, by rfl⟩ : syracuseStep 253361 = 190021) B190021
theorem B253379 : Blo 167798 253379 := bstep (se 1 (by rfl) ⟨190034, by rfl⟩ : syracuseStep 253379 = 380069) B380069
theorem B253409 : Blo 167798 253409 := bstep (se 2 (by rfl) ⟨95028, by rfl⟩ : syracuseStep 253409 = 190057) B190057
theorem B286193 : Blo 167798 286193 := bstep (se 2 (by rfl) ⟨107322, by rfl⟩ : syracuseStep 286193 = 214645) B214645
theorem B384497 : Blo 167798 384497 := bstep (se 2 (by rfl) ⟨144186, by rfl⟩ : syracuseStep 384497 = 288373) B288373
theorem B253427 : Blo 167798 253427 := bstep (se 1 (by rfl) ⟨190070, by rfl⟩ : syracuseStep 253427 = 380141) B380141
theorem B384515 : Blo 167798 384515 := bstep (se 1 (by rfl) ⟨288386, by rfl⟩ : syracuseStep 384515 = 576773) B576773
theorem B253457 : Blo 167798 253457 := bstep (se 2 (by rfl) ⟨95046, by rfl⟩ : syracuseStep 253457 = 190093) B190093
theorem B253475 : Blo 167798 253475 := bstep (se 1 (by rfl) ⟨190106, by rfl⟩ : syracuseStep 253475 = 380213) B380213
theorem B482861 : Blo 167798 482861 := bstep (se 3 (by rfl) ⟨90536, by rfl⟩ : syracuseStep 482861 = 181073) B181073
theorem B253505 : Blo 167798 253505 := bstep (se 2 (by rfl) ⟨95064, by rfl⟩ : syracuseStep 253505 = 190129) B190129
theorem B351811 : Blo 167798 351811 := bstep (se 1 (by rfl) ⟨263858, by rfl⟩ : syracuseStep 351811 = 527717) B527717
theorem B253523 : Blo 167798 253523 := bstep (se 1 (by rfl) ⟨190142, by rfl⟩ : syracuseStep 253523 = 380285) B380285
theorem B2055779 : Blo 167798 2055779 := bstep (se 1 (by rfl) ⟨1541834, by rfl⟩ : syracuseStep 2055779 = 3083669) B3083669
theorem B253553 : Blo 167798 253553 := bstep (se 2 (by rfl) ⟨95082, by rfl⟩ : syracuseStep 253553 = 190165) B190165
theorem B286321 : Blo 167798 286321 := bstep (se 2 (by rfl) ⟨107370, by rfl⟩ : syracuseStep 286321 = 214741) B214741
theorem B253571 : Blo 167798 253571 := bstep (se 1 (by rfl) ⟨190178, by rfl⟩ : syracuseStep 253571 = 380357) B380357
theorem B286355 : Blo 167798 286355 := bstep (se 1 (by rfl) ⟨214766, by rfl⟩ : syracuseStep 286355 = 429533) B429533
theorem B253601 : Blo 167798 253601 := bstep (se 2 (by rfl) ⟨95100, by rfl⟩ : syracuseStep 253601 = 190201) B190201
theorem B253619 : Blo 167798 253619 := bstep (se 1 (by rfl) ⟨190214, by rfl⟩ : syracuseStep 253619 = 380429) B380429
theorem B253649 : Blo 167798 253649 := bstep (se 2 (by rfl) ⟨95118, by rfl⟩ : syracuseStep 253649 = 190237) B190237
theorem B253667 : Blo 167798 253667 := bstep (se 1 (by rfl) ⟨190250, by rfl⟩ : syracuseStep 253667 = 380501) B380501
theorem B483043 : Blo 167798 483043 := bstep (se 1 (by rfl) ⟨362282, by rfl⟩ : syracuseStep 483043 = 724565) B724565
theorem B253697 : Blo 167798 253697 := bstep (se 2 (by rfl) ⟨95136, by rfl⟩ : syracuseStep 253697 = 190273) B190273
theorem B384785 : Blo 167798 384785 := bstep (se 2 (by rfl) ⟨144294, by rfl⟩ : syracuseStep 384785 = 288589) B288589
theorem B253715 : Blo 167798 253715 := bstep (se 1 (by rfl) ⟨190286, by rfl⟩ : syracuseStep 253715 = 380573) B380573
theorem B286483 : Blo 167798 286483 := bstep (se 1 (by rfl) ⟨214862, by rfl⟩ : syracuseStep 286483 = 429725) B429725
theorem B384803 : Blo 167798 384803 := bstep (se 1 (by rfl) ⟨288602, by rfl⟩ : syracuseStep 384803 = 577205) B577205
theorem B548653 : Blo 167798 548653 := bstep (se 3 (by rfl) ⟨102872, by rfl⟩ : syracuseStep 548653 = 205745) B205745
theorem B253745 : Blo 167798 253745 := bstep (se 2 (by rfl) ⟨95154, by rfl⟩ : syracuseStep 253745 = 190309) B190309
theorem B253763 : Blo 167798 253763 := bstep (se 1 (by rfl) ⟨190322, by rfl⟩ : syracuseStep 253763 = 380645) B380645
theorem B253793 : Blo 167798 253793 := bstep (se 2 (by rfl) ⟨95172, by rfl⟩ : syracuseStep 253793 = 190345) B190345
theorem B253811 : Blo 167798 253811 := bstep (se 1 (by rfl) ⟨190358, by rfl⟩ : syracuseStep 253811 = 380717) B380717
theorem B253841 : Blo 167798 253841 := bstep (se 2 (by rfl) ⟨95190, by rfl⟩ : syracuseStep 253841 = 190381) B190381
theorem B286625 : Blo 167798 286625 := bstep (se 2 (by rfl) ⟨107484, by rfl⟩ : syracuseStep 286625 = 214969) B214969
theorem B253859 : Blo 167798 253859 := bstep (se 1 (by rfl) ⟨190394, by rfl⟩ : syracuseStep 253859 = 380789) B380789
theorem B253889 : Blo 167798 253889 := bstep (se 2 (by rfl) ⟨95208, by rfl⟩ : syracuseStep 253889 = 190417) B190417
theorem B253907 : Blo 167798 253907 := bstep (se 1 (by rfl) ⟨190430, by rfl⟩ : syracuseStep 253907 = 380861) B380861
theorem B253937 : Blo 167798 253937 := bstep (se 2 (by rfl) ⟨95226, by rfl⟩ : syracuseStep 253937 = 190453) B190453
theorem B253955 : Blo 167798 253955 := bstep (se 1 (by rfl) ⟨190466, by rfl⟩ : syracuseStep 253955 = 380933) B380933
theorem B253985 : Blo 167798 253985 := bstep (se 2 (by rfl) ⟨95244, by rfl⟩ : syracuseStep 253985 = 190489) B190489
theorem B286753 : Blo 167798 286753 := bstep (se 2 (by rfl) ⟨107532, by rfl⟩ : syracuseStep 286753 = 215065) B215065
theorem B811043 : Blo 167798 811043 := bstep (se 1 (by rfl) ⟨608282, by rfl⟩ : syracuseStep 811043 = 1216565) B1216565
theorem B385073 : Blo 167798 385073 := bstep (se 2 (by rfl) ⟨144402, by rfl⟩ : syracuseStep 385073 = 288805) B288805
theorem B254003 : Blo 167798 254003 := bstep (se 1 (by rfl) ⟨190502, by rfl⟩ : syracuseStep 254003 = 381005) B381005
theorem B286787 : Blo 167798 286787 := bstep (se 1 (by rfl) ⟨215090, by rfl⟩ : syracuseStep 286787 = 430181) B430181
theorem B385091 : Blo 167798 385091 := bstep (se 1 (by rfl) ⟨288818, by rfl⟩ : syracuseStep 385091 = 577637) B577637
theorem B254033 : Blo 167798 254033 := bstep (se 2 (by rfl) ⟨95262, by rfl⟩ : syracuseStep 254033 = 190525) B190525
theorem B254051 : Blo 167798 254051 := bstep (se 1 (by rfl) ⟨190538, by rfl⟩ : syracuseStep 254051 = 381077) B381077
theorem B1630307 : Blo 167798 1630307 := bstep (se 1 (by rfl) ⟨1222730, by rfl⟩ : syracuseStep 1630307 = 2445461) B2445461
theorem B254081 : Blo 167798 254081 := bstep (se 2 (by rfl) ⟨95280, by rfl⟩ : syracuseStep 254081 = 190561) B190561
theorem B1532045 : Blo 167798 1532045 := bstep (se 3 (by rfl) ⟨287258, by rfl⟩ : syracuseStep 1532045 = 574517) B574517
theorem B254099 : Blo 167798 254099 := bstep (se 1 (by rfl) ⟨190574, by rfl⟩ : syracuseStep 254099 = 381149) B381149
theorem B254129 : Blo 167798 254129 := bstep (se 2 (by rfl) ⟨95298, by rfl⟩ : syracuseStep 254129 = 190597) B190597
theorem B254147 : Blo 167798 254147 := bstep (se 1 (by rfl) ⟨190610, by rfl⟩ : syracuseStep 254147 = 381221) B381221
theorem B286915 : Blo 167798 286915 := bstep (se 1 (by rfl) ⟨215186, by rfl⟩ : syracuseStep 286915 = 430373) B430373
theorem B483533 : Blo 167798 483533 := bstep (se 3 (by rfl) ⟨90662, by rfl⟩ : syracuseStep 483533 = 181325) B181325
theorem B319697 : Blo 167798 319697 := bstep (se 2 (by rfl) ⟨119886, by rfl⟩ : syracuseStep 319697 = 239773) B239773
theorem B254177 : Blo 167798 254177 := bstep (se 2 (by rfl) ⟨95316, by rfl⟩ : syracuseStep 254177 = 190633) B190633
theorem B254195 : Blo 167798 254195 := bstep (se 1 (by rfl) ⟨190646, by rfl⟩ : syracuseStep 254195 = 381293) B381293
theorem B254225 : Blo 167798 254225 := bstep (se 2 (by rfl) ⟨95334, by rfl⟩ : syracuseStep 254225 = 190669) B190669
theorem B254243 : Blo 167798 254243 := bstep (se 1 (by rfl) ⟨190682, by rfl⟩ : syracuseStep 254243 = 381365) B381365
theorem B647459 : Blo 167798 647459 := bstep (se 1 (by rfl) ⟨485594, by rfl⟩ : syracuseStep 647459 = 971189) B971189
theorem B647473 : Blo 167798 647473 := bstep (se 2 (by rfl) ⟨242802, by rfl⟩ : syracuseStep 647473 = 485605) B485605
theorem B254273 : Blo 167798 254273 := bstep (se 2 (by rfl) ⟨95352, by rfl⟩ : syracuseStep 254273 = 190705) B190705
theorem B287057 : Blo 167798 287057 := bstep (se 2 (by rfl) ⟨107646, by rfl⟩ : syracuseStep 287057 = 215293) B215293
theorem B385361 : Blo 167798 385361 := bstep (se 2 (by rfl) ⟨144510, by rfl⟩ : syracuseStep 385361 = 289021) B289021
theorem B254291 : Blo 167798 254291 := bstep (se 1 (by rfl) ⟨190718, by rfl⟩ : syracuseStep 254291 = 381437) B381437
theorem B385379 : Blo 167798 385379 := bstep (se 1 (by rfl) ⟨289034, by rfl⟩ : syracuseStep 385379 = 578069) B578069
theorem B254321 : Blo 167798 254321 := bstep (se 2 (by rfl) ⟨95370, by rfl⟩ : syracuseStep 254321 = 190741) B190741
theorem B254339 : Blo 167798 254339 := bstep (se 1 (by rfl) ⟨190754, by rfl⟩ : syracuseStep 254339 = 381509) B381509
theorem B254369 : Blo 167798 254369 := bstep (se 2 (by rfl) ⟨95388, by rfl⟩ : syracuseStep 254369 = 190777) B190777
theorem B188851 : Blo 167798 188851 := bstep (se 1 (by rfl) ⟨141638, by rfl⟩ : syracuseStep 188851 = 283277) B283277
theorem B254387 : Blo 167798 254387 := bstep (se 1 (by rfl) ⟨190790, by rfl⟩ : syracuseStep 254387 = 381581) B381581
theorem B254417 : Blo 167798 254417 := bstep (se 2 (by rfl) ⟨95406, by rfl⟩ : syracuseStep 254417 = 190813) B190813
theorem B287185 : Blo 167798 287185 := bstep (se 2 (by rfl) ⟨107694, by rfl⟩ : syracuseStep 287185 = 215389) B215389
theorem B254435 : Blo 167798 254435 := bstep (se 1 (by rfl) ⟨190826, by rfl⟩ : syracuseStep 254435 = 381653) B381653
theorem B287219 : Blo 167798 287219 := bstep (se 1 (by rfl) ⟨215414, by rfl⟩ : syracuseStep 287219 = 430829) B430829
theorem B254465 : Blo 167798 254465 := bstep (se 2 (by rfl) ⟨95424, by rfl⟩ : syracuseStep 254465 = 190849) B190849
theorem B1434125 : Blo 167798 1434125 := bstep (se 3 (by rfl) ⟨268898, by rfl⟩ : syracuseStep 1434125 = 537797) B537797
theorem B254483 : Blo 167798 254483 := bstep (se 1 (by rfl) ⟨190862, by rfl⟩ : syracuseStep 254483 = 381725) B381725
theorem B254513 : Blo 167798 254513 := bstep (se 2 (by rfl) ⟨95442, by rfl⟩ : syracuseStep 254513 = 190885) B190885
theorem B188995 : Blo 167798 188995 := bstep (se 1 (by rfl) ⟨141746, by rfl⟩ : syracuseStep 188995 = 283493) B283493
theorem B254531 : Blo 167798 254531 := bstep (se 1 (by rfl) ⟨190898, by rfl⟩ : syracuseStep 254531 = 381797) B381797
theorem B287315 : Blo 167798 287315 := bstep (se 1 (by rfl) ⟨215486, by rfl⟩ : syracuseStep 287315 = 430973) B430973
theorem B254561 : Blo 167798 254561 := bstep (se 2 (by rfl) ⟨95460, by rfl⟩ : syracuseStep 254561 = 190921) B190921
theorem B385649 : Blo 167798 385649 := bstep (se 2 (by rfl) ⟨144618, by rfl⟩ : syracuseStep 385649 = 289237) B289237
theorem B254579 : Blo 167798 254579 := bstep (se 1 (by rfl) ⟨190934, by rfl⟩ : syracuseStep 254579 = 381869) B381869
theorem B287347 : Blo 167798 287347 := bstep (se 1 (by rfl) ⟨215510, by rfl⟩ : syracuseStep 287347 = 431021) B431021
theorem B385667 : Blo 167798 385667 := bstep (se 1 (by rfl) ⟨289250, by rfl⟩ : syracuseStep 385667 = 578501) B578501
theorem B254609 : Blo 167798 254609 := bstep (se 2 (by rfl) ⟨95478, by rfl⟩ : syracuseStep 254609 = 190957) B190957
theorem B254627 : Blo 167798 254627 := bstep (se 1 (by rfl) ⟨190970, by rfl⟩ : syracuseStep 254627 = 381941) B381941
theorem B254657 : Blo 167798 254657 := bstep (se 2 (by rfl) ⟨95496, by rfl⟩ : syracuseStep 254657 = 190993) B190993
theorem B189139 : Blo 167798 189139 := bstep (se 1 (by rfl) ⟨141854, by rfl⟩ : syracuseStep 189139 = 283709) B283709
theorem B254675 : Blo 167798 254675 := bstep (se 1 (by rfl) ⟨191006, by rfl⟩ : syracuseStep 254675 = 382013) B382013
theorem B254705 : Blo 167798 254705 := bstep (se 2 (by rfl) ⟨95514, by rfl⟩ : syracuseStep 254705 = 191029) B191029
theorem B287489 : Blo 167798 287489 := bstep (se 2 (by rfl) ⟨107808, by rfl⟩ : syracuseStep 287489 = 215617) B215617
theorem B254723 : Blo 167798 254723 := bstep (se 1 (by rfl) ⟨191042, by rfl⟩ : syracuseStep 254723 = 382085) B382085
theorem B254753 : Blo 167798 254753 := bstep (se 2 (by rfl) ⟨95532, by rfl⟩ : syracuseStep 254753 = 191065) B191065
theorem B910129 : Blo 167798 910129 := bstep (se 2 (by rfl) ⟨341298, by rfl⟩ : syracuseStep 910129 = 682597) B682597
theorem B254771 : Blo 167798 254771 := bstep (se 1 (by rfl) ⟨191078, by rfl⟩ : syracuseStep 254771 = 382157) B382157
theorem B254801 : Blo 167798 254801 := bstep (se 2 (by rfl) ⟨95550, by rfl⟩ : syracuseStep 254801 = 191101) B191101
theorem B189283 : Blo 167798 189283 := bstep (se 1 (by rfl) ⟨141962, by rfl⟩ : syracuseStep 189283 = 283925) B283925
theorem B254819 : Blo 167798 254819 := bstep (se 1 (by rfl) ⟨191114, by rfl⟩ : syracuseStep 254819 = 382229) B382229
theorem B254849 : Blo 167798 254849 := bstep (se 2 (by rfl) ⟨95568, by rfl⟩ : syracuseStep 254849 = 191137) B191137
theorem B287617 : Blo 167798 287617 := bstep (se 2 (by rfl) ⟨107856, by rfl⟩ : syracuseStep 287617 = 215713) B215713
theorem B385937 : Blo 167798 385937 := bstep (se 2 (by rfl) ⟨144726, by rfl⟩ : syracuseStep 385937 = 289453) B289453
theorem B254867 : Blo 167798 254867 := bstep (se 1 (by rfl) ⟨191150, by rfl⟩ : syracuseStep 254867 = 382301) B382301
theorem B287651 : Blo 167798 287651 := bstep (se 1 (by rfl) ⟨215738, by rfl⟩ : syracuseStep 287651 = 431477) B431477
theorem B385955 : Blo 167798 385955 := bstep (se 1 (by rfl) ⟨289466, by rfl⟩ : syracuseStep 385955 = 578933) B578933
theorem B254897 : Blo 167798 254897 := bstep (se 2 (by rfl) ⟨95586, by rfl⟩ : syracuseStep 254897 = 191173) B191173
theorem B254915 : Blo 167798 254915 := bstep (se 1 (by rfl) ⟨191186, by rfl⟩ : syracuseStep 254915 = 382373) B382373
theorem B254945 : Blo 167798 254945 := bstep (se 2 (by rfl) ⟨95604, by rfl⟩ : syracuseStep 254945 = 191209) B191209
theorem B1172465 : Blo 167798 1172465 := bstep (se 2 (by rfl) ⟨439674, by rfl⟩ : syracuseStep 1172465 = 879349) B879349
theorem B189427 : Blo 167798 189427 := bstep (se 1 (by rfl) ⟨142070, by rfl⟩ : syracuseStep 189427 = 284141) B284141
theorem B254963 : Blo 167798 254963 := bstep (se 1 (by rfl) ⟨191222, by rfl⟩ : syracuseStep 254963 = 382445) B382445
theorem B254993 : Blo 167798 254993 := bstep (se 2 (by rfl) ⟨95622, by rfl⟩ : syracuseStep 254993 = 191245) B191245
theorem B255011 : Blo 167798 255011 := bstep (se 1 (by rfl) ⟨191258, by rfl⟩ : syracuseStep 255011 = 382517) B382517
theorem B287779 : Blo 167798 287779 := bstep (se 1 (by rfl) ⟨215834, by rfl⟩ : syracuseStep 287779 = 431669) B431669
theorem B255041 : Blo 167798 255041 := bstep (se 2 (by rfl) ⟨95640, by rfl⟩ : syracuseStep 255041 = 191281) B191281
theorem B320593 : Blo 167798 320593 := bstep (se 2 (by rfl) ⟨120222, by rfl⟩ : syracuseStep 320593 = 240445) B240445
theorem B255059 : Blo 167798 255059 := bstep (se 1 (by rfl) ⟨191294, by rfl⟩ : syracuseStep 255059 = 382589) B382589
theorem B517229 : Blo 167798 517229 := bstep (se 3 (by rfl) ⟨96980, by rfl⟩ : syracuseStep 517229 = 193961) B193961
theorem B255089 : Blo 167798 255089 := bstep (se 2 (by rfl) ⟨95658, by rfl⟩ : syracuseStep 255089 = 191317) B191317
theorem B189571 : Blo 167798 189571 := bstep (se 1 (by rfl) ⟨142178, by rfl⟩ : syracuseStep 189571 = 284357) B284357
theorem B255107 : Blo 167798 255107 := bstep (se 1 (by rfl) ⟨191330, by rfl⟩ : syracuseStep 255107 = 382661) B382661
theorem B255137 : Blo 167798 255137 := bstep (se 2 (by rfl) ⟨95676, by rfl⟩ : syracuseStep 255137 = 191353) B191353
theorem B287921 : Blo 167798 287921 := bstep (se 2 (by rfl) ⟨107970, by rfl⟩ : syracuseStep 287921 = 215941) B215941
theorem B386225 : Blo 167798 386225 := bstep (se 2 (by rfl) ⟨144834, by rfl⟩ : syracuseStep 386225 = 289669) B289669
theorem B255155 : Blo 167798 255155 := bstep (se 1 (by rfl) ⟨191366, by rfl⟩ : syracuseStep 255155 = 382733) B382733
theorem B386243 : Blo 167798 386243 := bstep (se 1 (by rfl) ⟨289682, by rfl⟩ : syracuseStep 386243 = 579365) B579365
theorem B255185 : Blo 167798 255185 := bstep (se 2 (by rfl) ⟨95694, by rfl⟩ : syracuseStep 255185 = 191389) B191389
theorem B255203 : Blo 167798 255203 := bstep (se 1 (by rfl) ⟨191402, by rfl⟩ : syracuseStep 255203 = 382805) B382805
theorem B320753 : Blo 167798 320753 := bstep (se 2 (by rfl) ⟨120282, by rfl⟩ : syracuseStep 320753 = 240565) B240565
theorem B255233 : Blo 167798 255233 := bstep (se 2 (by rfl) ⟨95712, by rfl⟩ : syracuseStep 255233 = 191425) B191425
theorem B189715 : Blo 167798 189715 := bstep (se 1 (by rfl) ⟨142286, by rfl⟩ : syracuseStep 189715 = 284573) B284573
theorem B255251 : Blo 167798 255251 := bstep (se 1 (by rfl) ⟨191438, by rfl⟩ : syracuseStep 255251 = 382877) B382877
theorem B255281 : Blo 167798 255281 := bstep (se 2 (by rfl) ⟨95730, by rfl⟩ : syracuseStep 255281 = 191461) B191461
theorem B288049 : Blo 167798 288049 := bstep (se 2 (by rfl) ⟨108018, by rfl⟩ : syracuseStep 288049 = 216037) B216037
theorem B255299 : Blo 167798 255299 := bstep (se 1 (by rfl) ⟨191474, by rfl⟩ : syracuseStep 255299 = 382949) B382949
theorem B288083 : Blo 167798 288083 := bstep (se 1 (by rfl) ⟨216062, by rfl⟩ : syracuseStep 288083 = 432125) B432125
theorem B255329 : Blo 167798 255329 := bstep (se 2 (by rfl) ⟨95748, by rfl⟩ : syracuseStep 255329 = 191497) B191497
theorem B484717 : Blo 167798 484717 := bstep (se 3 (by rfl) ⟨90884, by rfl⟩ : syracuseStep 484717 = 181769) B181769
theorem B550253 : Blo 167798 550253 := bstep (se 3 (by rfl) ⟨103172, by rfl⟩ : syracuseStep 550253 = 206345) B206345
theorem B255347 : Blo 167798 255347 := bstep (se 1 (by rfl) ⟨191510, by rfl⟩ : syracuseStep 255347 = 383021) B383021
theorem B255377 : Blo 167798 255377 := bstep (se 2 (by rfl) ⟨95766, by rfl⟩ : syracuseStep 255377 = 191533) B191533
theorem B189859 : Blo 167798 189859 := bstep (se 1 (by rfl) ⟨142394, by rfl⟩ : syracuseStep 189859 = 284789) B284789
theorem B255395 : Blo 167798 255395 := bstep (se 1 (by rfl) ⟨191546, by rfl⟩ : syracuseStep 255395 = 383093) B383093
theorem B255425 : Blo 167798 255425 := bstep (se 2 (by rfl) ⟨95784, by rfl⟩ : syracuseStep 255425 = 191569) B191569
theorem B386513 : Blo 167798 386513 := bstep (se 2 (by rfl) ⟨144942, by rfl⟩ : syracuseStep 386513 = 289885) B289885
theorem B255443 : Blo 167798 255443 := bstep (se 1 (by rfl) ⟨191582, by rfl⟩ : syracuseStep 255443 = 383165) B383165
theorem B288211 : Blo 167798 288211 := bstep (se 1 (by rfl) ⟨216158, by rfl⟩ : syracuseStep 288211 = 432317) B432317
theorem B386531 : Blo 167798 386531 := bstep (se 1 (by rfl) ⟨289898, by rfl⟩ : syracuseStep 386531 = 579797) B579797
theorem B255473 : Blo 167798 255473 := bstep (se 2 (by rfl) ⟨95802, by rfl⟩ : syracuseStep 255473 = 191605) B191605
theorem B255491 : Blo 167798 255491 := bstep (se 1 (by rfl) ⟨191618, by rfl⟩ : syracuseStep 255491 = 383237) B383237
theorem B255521 : Blo 167798 255521 := bstep (se 2 (by rfl) ⟨95820, by rfl⟩ : syracuseStep 255521 = 191641) B191641
theorem B190003 : Blo 167798 190003 := bstep (se 1 (by rfl) ⟨142502, by rfl⟩ : syracuseStep 190003 = 285005) B285005
theorem B255539 : Blo 167798 255539 := bstep (se 1 (by rfl) ⟨191654, by rfl⟩ : syracuseStep 255539 = 383309) B383309
theorem B255569 : Blo 167798 255569 := bstep (se 2 (by rfl) ⟨95838, by rfl⟩ : syracuseStep 255569 = 191677) B191677
theorem B288353 : Blo 167798 288353 := bstep (se 2 (by rfl) ⟨108132, by rfl⟩ : syracuseStep 288353 = 216265) B216265
theorem B255587 : Blo 167798 255587 := bstep (se 1 (by rfl) ⟨191690, by rfl⟩ : syracuseStep 255587 = 383381) B383381
theorem B255617 : Blo 167798 255617 := bstep (se 2 (by rfl) ⟨95856, by rfl⟩ : syracuseStep 255617 = 191713) B191713
theorem B321155 : Blo 167798 321155 := bstep (se 1 (by rfl) ⟨240866, by rfl⟩ : syracuseStep 321155 = 481733) B481733
theorem B255635 : Blo 167798 255635 := bstep (se 1 (by rfl) ⟨191726, by rfl⟩ : syracuseStep 255635 = 383453) B383453
theorem B255665 : Blo 167798 255665 := bstep (se 2 (by rfl) ⟨95874, by rfl⟩ : syracuseStep 255665 = 191749) B191749
theorem B255683 : Blo 167798 255683 := bstep (se 1 (by rfl) ⟨191762, by rfl⟩ : syracuseStep 255683 = 383525) B383525
theorem B190147 : Blo 167798 190147 := bstep (se 1 (by rfl) ⟨142610, by rfl⟩ : syracuseStep 190147 = 285221) B285221
theorem B255713 : Blo 167798 255713 := bstep (se 2 (by rfl) ⟨95892, by rfl⟩ : syracuseStep 255713 = 191785) B191785
theorem B288481 : Blo 167798 288481 := bstep (se 2 (by rfl) ⟨108180, by rfl⟩ : syracuseStep 288481 = 216361) B216361
theorem B648931 : Blo 167798 648931 := bstep (se 1 (by rfl) ⟨486698, by rfl⟩ : syracuseStep 648931 = 973397) B973397
theorem B255731 : Blo 167798 255731 := bstep (se 1 (by rfl) ⟨191798, by rfl⟩ : syracuseStep 255731 = 383597) B383597
theorem B288515 : Blo 167798 288515 := bstep (se 1 (by rfl) ⟨216386, by rfl⟩ : syracuseStep 288515 = 432773) B432773
theorem B255761 : Blo 167798 255761 := bstep (se 2 (by rfl) ⟨95910, by rfl⟩ : syracuseStep 255761 = 191821) B191821
theorem B255779 : Blo 167798 255779 := bstep (se 1 (by rfl) ⟨191834, by rfl⟩ : syracuseStep 255779 = 383669) B383669
theorem B583469 : Blo 167798 583469 := bstep (se 3 (by rfl) ⟨109400, by rfl⟩ : syracuseStep 583469 = 218801) B218801
theorem B255809 : Blo 167798 255809 := bstep (se 2 (by rfl) ⟨95928, by rfl⟩ : syracuseStep 255809 = 191857) B191857
theorem B190291 : Blo 167798 190291 := bstep (se 1 (by rfl) ⟨142718, by rfl⟩ : syracuseStep 190291 = 285437) B285437
theorem B255827 : Blo 167798 255827 := bstep (se 1 (by rfl) ⟨191870, by rfl⟩ : syracuseStep 255827 = 383741) B383741
theorem B255857 : Blo 167798 255857 := bstep (se 2 (by rfl) ⟨95946, by rfl⟩ : syracuseStep 255857 = 191893) B191893
theorem B255875 : Blo 167798 255875 := bstep (se 1 (by rfl) ⟨191906, by rfl⟩ : syracuseStep 255875 = 383813) B383813
theorem B288643 : Blo 167798 288643 := bstep (se 1 (by rfl) ⟨216482, by rfl⟩ : syracuseStep 288643 = 432965) B432965
theorem B255905 : Blo 167798 255905 := bstep (se 2 (by rfl) ⟨95964, by rfl⟩ : syracuseStep 255905 = 191929) B191929
theorem B255923 : Blo 167798 255923 := bstep (se 1 (by rfl) ⟨191942, by rfl⟩ : syracuseStep 255923 = 383885) B383885
theorem B255953 : Blo 167798 255953 := bstep (se 2 (by rfl) ⟨95982, by rfl⟩ : syracuseStep 255953 = 191965) B191965
theorem B190435 : Blo 167798 190435 := bstep (se 1 (by rfl) ⟨142826, by rfl⟩ : syracuseStep 190435 = 285653) B285653
theorem B255971 : Blo 167798 255971 := bstep (se 1 (by rfl) ⟨191978, by rfl⟩ : syracuseStep 255971 = 383957) B383957
theorem B813041 : Blo 167798 813041 := bstep (se 2 (by rfl) ⟨304890, by rfl⟩ : syracuseStep 813041 = 609781) B609781
theorem B256001 : Blo 167798 256001 := bstep (se 2 (by rfl) ⟨96000, by rfl⟩ : syracuseStep 256001 = 192001) B192001
theorem B288785 : Blo 167798 288785 := bstep (se 2 (by rfl) ⟨108294, by rfl⟩ : syracuseStep 288785 = 216589) B216589
theorem B256019 : Blo 167798 256019 := bstep (se 1 (by rfl) ⟨192014, by rfl⟩ : syracuseStep 256019 = 384029) B384029
theorem B256049 : Blo 167798 256049 := bstep (se 2 (by rfl) ⟨96018, by rfl⟩ : syracuseStep 256049 = 192037) B192037
theorem B256067 : Blo 167798 256067 := bstep (se 1 (by rfl) ⟨192050, by rfl⟩ : syracuseStep 256067 = 384101) B384101
theorem B256097 : Blo 167798 256097 := bstep (se 2 (by rfl) ⟨96036, by rfl⟩ : syracuseStep 256097 = 192073) B192073
theorem B190579 : Blo 167798 190579 := bstep (se 1 (by rfl) ⟨142934, by rfl⟩ : syracuseStep 190579 = 285869) B285869
theorem B256115 : Blo 167798 256115 := bstep (se 1 (by rfl) ⟨192086, by rfl⟩ : syracuseStep 256115 = 384173) B384173
theorem B256145 : Blo 167798 256145 := bstep (se 2 (by rfl) ⟨96054, by rfl⟩ : syracuseStep 256145 = 192109) B192109
theorem B288913 : Blo 167798 288913 := bstep (se 2 (by rfl) ⟨108342, by rfl⟩ : syracuseStep 288913 = 216685) B216685
theorem B256163 : Blo 167798 256163 := bstep (se 1 (by rfl) ⟨192122, by rfl⟩ : syracuseStep 256163 = 384245) B384245
theorem B288947 : Blo 167798 288947 := bstep (se 1 (by rfl) ⟨216710, by rfl⟩ : syracuseStep 288947 = 433421) B433421
theorem B256193 : Blo 167798 256193 := bstep (se 2 (by rfl) ⟨96072, by rfl⟩ : syracuseStep 256193 = 192145) B192145
theorem B256211 : Blo 167798 256211 := bstep (se 1 (by rfl) ⟨192158, by rfl⟩ : syracuseStep 256211 = 384317) B384317
theorem B1370353 : Blo 167798 1370353 := bstep (se 2 (by rfl) ⟨513882, by rfl⟩ : syracuseStep 1370353 = 1027765) B1027765
theorem B256241 : Blo 167798 256241 := bstep (se 2 (by rfl) ⟨96090, by rfl⟩ : syracuseStep 256241 = 192181) B192181
theorem B190723 : Blo 167798 190723 := bstep (se 1 (by rfl) ⟨143042, by rfl⟩ : syracuseStep 190723 = 286085) B286085
theorem B256259 : Blo 167798 256259 := bstep (se 1 (by rfl) ⟨192194, by rfl⟩ : syracuseStep 256259 = 384389) B384389
theorem B256289 : Blo 167798 256289 := bstep (se 2 (by rfl) ⟨96108, by rfl⟩ : syracuseStep 256289 = 192217) B192217
theorem B256307 : Blo 167798 256307 := bstep (se 1 (by rfl) ⟨192230, by rfl⟩ : syracuseStep 256307 = 384461) B384461
theorem B289075 : Blo 167798 289075 := bstep (se 1 (by rfl) ⟨216806, by rfl⟩ : syracuseStep 289075 = 433613) B433613
theorem B518467 : Blo 167798 518467 := bstep (se 1 (by rfl) ⟨388850, by rfl⟩ : syracuseStep 518467 = 777701) B777701
theorem B256337 : Blo 167798 256337 := bstep (se 2 (by rfl) ⟨96126, by rfl⟩ : syracuseStep 256337 = 192253) B192253
theorem B256355 : Blo 167798 256355 := bstep (se 1 (by rfl) ⟨192266, by rfl⟩ : syracuseStep 256355 = 384533) B384533
theorem B256385 : Blo 167798 256385 := bstep (se 2 (by rfl) ⟨96144, by rfl⟩ : syracuseStep 256385 = 192289) B192289
theorem B584081 : Blo 167798 584081 := bstep (se 2 (by rfl) ⟨219030, by rfl⟩ : syracuseStep 584081 = 438061) B438061
theorem B485777 : Blo 167798 485777 := bstep (se 2 (by rfl) ⟨182166, by rfl⟩ : syracuseStep 485777 = 364333) B364333
theorem B190867 : Blo 167798 190867 := bstep (se 1 (by rfl) ⟨143150, by rfl⟩ : syracuseStep 190867 = 286301) B286301
theorem B256403 : Blo 167798 256403 := bstep (se 1 (by rfl) ⟨192302, by rfl⟩ : syracuseStep 256403 = 384605) B384605
theorem B256433 : Blo 167798 256433 := bstep (se 2 (by rfl) ⟨96162, by rfl⟩ : syracuseStep 256433 = 192325) B192325
theorem B289217 : Blo 167798 289217 := bstep (se 2 (by rfl) ⟨108456, by rfl⟩ : syracuseStep 289217 = 216913) B216913
theorem B256451 : Blo 167798 256451 := bstep (se 1 (by rfl) ⟨192338, by rfl⟩ : syracuseStep 256451 = 384677) B384677
theorem B256481 : Blo 167798 256481 := bstep (se 2 (by rfl) ⟨96180, by rfl⟩ : syracuseStep 256481 = 192361) B192361
theorem B256499 : Blo 167798 256499 := bstep (se 1 (by rfl) ⟨192374, by rfl⟩ : syracuseStep 256499 = 384749) B384749
theorem B322051 : Blo 167798 322051 := bstep (se 1 (by rfl) ⟨241538, by rfl⟩ : syracuseStep 322051 = 483077) B483077
theorem B256529 : Blo 167798 256529 := bstep (se 2 (by rfl) ⟨96198, by rfl⟩ : syracuseStep 256529 = 192397) B192397
theorem B191011 : Blo 167798 191011 := bstep (se 1 (by rfl) ⟨143258, by rfl⟩ : syracuseStep 191011 = 286517) B286517
theorem B256547 : Blo 167798 256547 := bstep (se 1 (by rfl) ⟨192410, by rfl⟩ : syracuseStep 256547 = 384821) B384821
theorem B256577 : Blo 167798 256577 := bstep (se 2 (by rfl) ⟨96216, by rfl⟩ : syracuseStep 256577 = 192433) B192433
theorem B289345 : Blo 167798 289345 := bstep (se 2 (by rfl) ⟨108504, by rfl⟩ : syracuseStep 289345 = 217009) B217009
theorem B256595 : Blo 167798 256595 := bstep (se 1 (by rfl) ⟨192446, by rfl⟩ : syracuseStep 256595 = 384893) B384893
theorem B387683 : Blo 167798 387683 := bstep (se 1 (by rfl) ⟨290762, by rfl⟩ : syracuseStep 387683 = 581525) B581525
theorem B289379 : Blo 167798 289379 := bstep (se 1 (by rfl) ⟨217034, by rfl⟩ : syracuseStep 289379 = 434069) B434069
theorem B2746993 : Blo 167798 2746993 := bstep (se 2 (by rfl) ⟨1030122, by rfl⟩ : syracuseStep 2746993 = 2060245) B2060245
theorem B3500657 : Blo 167798 3500657 := bstep (se 2 (by rfl) ⟨1312746, by rfl⟩ : syracuseStep 3500657 = 2625493) B2625493
theorem B256625 : Blo 167798 256625 := bstep (se 2 (by rfl) ⟨96234, by rfl⟩ : syracuseStep 256625 = 192469) B192469
theorem B256643 : Blo 167798 256643 := bstep (se 1 (by rfl) ⟨192482, by rfl⟩ : syracuseStep 256643 = 384965) B384965
theorem B256673 : Blo 167798 256673 := bstep (se 2 (by rfl) ⟨96252, by rfl⟩ : syracuseStep 256673 = 192505) B192505
theorem B322211 : Blo 167798 322211 := bstep (se 1 (by rfl) ⟨241658, by rfl⟩ : syracuseStep 322211 = 483317) B483317
theorem B191155 : Blo 167798 191155 := bstep (se 1 (by rfl) ⟨143366, by rfl⟩ : syracuseStep 191155 = 286733) B286733
theorem B256691 : Blo 167798 256691 := bstep (se 1 (by rfl) ⟨192518, by rfl⟩ : syracuseStep 256691 = 385037) B385037
theorem B256721 : Blo 167798 256721 := bstep (se 2 (by rfl) ⟨96270, by rfl⟩ : syracuseStep 256721 = 192541) B192541
theorem B256739 : Blo 167798 256739 := bstep (se 1 (by rfl) ⟨192554, by rfl⟩ : syracuseStep 256739 = 385109) B385109
theorem B289507 : Blo 167798 289507 := bstep (se 1 (by rfl) ⟨217130, by rfl⟩ : syracuseStep 289507 = 434261) B434261
theorem B256769 : Blo 167798 256769 := bstep (se 2 (by rfl) ⟨96288, by rfl⟩ : syracuseStep 256769 = 192577) B192577
theorem B256787 : Blo 167798 256787 := bstep (se 1 (by rfl) ⟨192590, by rfl⟩ : syracuseStep 256787 = 385181) B385181
theorem B256801 : Blo 167798 256801 := bstep (se 2 (by rfl) ⟨96300, by rfl⟩ : syracuseStep 256801 = 192601) B192601
theorem B256817 : Blo 167798 256817 := bstep (se 2 (by rfl) ⟨96306, by rfl⟩ : syracuseStep 256817 = 192613) B192613
theorem B191299 : Blo 167798 191299 := bstep (se 1 (by rfl) ⟨143474, by rfl⟩ : syracuseStep 191299 = 286949) B286949
theorem B256835 : Blo 167798 256835 := bstep (se 1 (by rfl) ⟨192626, by rfl⟩ : syracuseStep 256835 = 385253) B385253
theorem B256865 : Blo 167798 256865 := bstep (se 2 (by rfl) ⟨96324, by rfl⟩ : syracuseStep 256865 = 192649) B192649
theorem B289649 : Blo 167798 289649 := bstep (se 2 (by rfl) ⟨108618, by rfl⟩ : syracuseStep 289649 = 217237) B217237
theorem B256883 : Blo 167798 256883 := bstep (se 1 (by rfl) ⟨192662, by rfl⟩ : syracuseStep 256883 = 385325) B385325
theorem B256913 : Blo 167798 256913 := bstep (se 2 (by rfl) ⟨96342, by rfl⟩ : syracuseStep 256913 = 192685) B192685
theorem B256931 : Blo 167798 256931 := bstep (se 1 (by rfl) ⟨192698, by rfl⟩ : syracuseStep 256931 = 385397) B385397
theorem B256961 : Blo 167798 256961 := bstep (se 2 (by rfl) ⟨96360, by rfl⟩ : syracuseStep 256961 = 192721) B192721
theorem B3533765 : Blo 167798 3533765 := bstep (se 4 (by rfl) ⟨331290, by rfl⟩ : syracuseStep 3533765 = 662581) B662581
theorem B191443 : Blo 167798 191443 := bstep (se 1 (by rfl) ⟨143582, by rfl⟩ : syracuseStep 191443 = 287165) B287165
theorem B256979 : Blo 167798 256979 := bstep (se 1 (by rfl) ⟨192734, by rfl⟩ : syracuseStep 256979 = 385469) B385469
theorem B257009 : Blo 167798 257009 := bstep (se 2 (by rfl) ⟨96378, by rfl⟩ : syracuseStep 257009 = 192757) B192757
theorem B289777 : Blo 167798 289777 := bstep (se 2 (by rfl) ⟨108666, by rfl⟩ : syracuseStep 289777 = 217333) B217333
theorem B257027 : Blo 167798 257027 := bstep (se 1 (by rfl) ⟨192770, by rfl⟩ : syracuseStep 257027 = 385541) B385541
theorem B289811 : Blo 167798 289811 := bstep (se 1 (by rfl) ⟨217358, by rfl⟩ : syracuseStep 289811 = 434717) B434717
theorem B257057 : Blo 167798 257057 := bstep (se 2 (by rfl) ⟨96396, by rfl⟩ : syracuseStep 257057 = 192793) B192793
theorem B486449 : Blo 167798 486449 := bstep (se 2 (by rfl) ⟨182418, by rfl⟩ : syracuseStep 486449 = 364837) B364837
theorem B257075 : Blo 167798 257075 := bstep (se 1 (by rfl) ⟨192806, by rfl⟩ : syracuseStep 257075 = 385613) B385613
theorem B814157 : Blo 167798 814157 := bstep (se 3 (by rfl) ⟨152654, by rfl⟩ : syracuseStep 814157 = 305309) B305309
theorem B257105 : Blo 167798 257105 := bstep (se 2 (by rfl) ⟨96414, by rfl⟩ : syracuseStep 257105 = 192829) B192829
theorem B191587 : Blo 167798 191587 := bstep (se 1 (by rfl) ⟨143690, by rfl⟩ : syracuseStep 191587 = 287381) B287381
theorem B257123 : Blo 167798 257123 := bstep (se 1 (by rfl) ⟨192842, by rfl⟩ : syracuseStep 257123 = 385685) B385685
theorem B257153 : Blo 167798 257153 := bstep (se 2 (by rfl) ⟨96432, by rfl⟩ : syracuseStep 257153 = 192865) B192865
theorem B257171 : Blo 167798 257171 := bstep (se 1 (by rfl) ⟨192878, by rfl⟩ : syracuseStep 257171 = 385757) B385757
theorem B257201 : Blo 167798 257201 := bstep (se 2 (by rfl) ⟨96450, by rfl⟩ : syracuseStep 257201 = 192901) B192901
theorem B2157749 : Blo 167798 2157749 := bstep (se 5 (by rfl) ⟨101144, by rfl⟩ : syracuseStep 2157749 = 202289) B202289
theorem B257219 : Blo 167798 257219 := bstep (se 1 (by rfl) ⟨192914, by rfl⟩ : syracuseStep 257219 = 385829) B385829
theorem B1109189 : Blo 167798 1109189 := bstep (se 4 (by rfl) ⟨103986, by rfl⟩ : syracuseStep 1109189 = 207973) B207973
theorem B257249 : Blo 167798 257249 := bstep (se 2 (by rfl) ⟨96468, by rfl⟩ : syracuseStep 257249 = 192937) B192937
theorem B191731 : Blo 167798 191731 := bstep (se 1 (by rfl) ⟨143798, by rfl⟩ : syracuseStep 191731 = 287597) B287597
theorem B257267 : Blo 167798 257267 := bstep (se 1 (by rfl) ⟨192950, by rfl⟩ : syracuseStep 257267 = 385901) B385901
theorem B257297 : Blo 167798 257297 := bstep (se 2 (by rfl) ⟨96486, by rfl⟩ : syracuseStep 257297 = 192973) B192973
theorem B257315 : Blo 167798 257315 := bstep (se 1 (by rfl) ⟨192986, by rfl⟩ : syracuseStep 257315 = 385973) B385973
theorem B257345 : Blo 167798 257345 := bstep (se 2 (by rfl) ⟨96504, by rfl⟩ : syracuseStep 257345 = 193009) B193009
theorem B1469765 : Blo 167798 1469765 := bstep (se 4 (by rfl) ⟨137790, by rfl⟩ : syracuseStep 1469765 = 275581) B275581
theorem B257363 : Blo 167798 257363 := bstep (se 1 (by rfl) ⟨193022, by rfl⟩ : syracuseStep 257363 = 386045) B386045
theorem B1371491 : Blo 167798 1371491 := bstep (se 1 (by rfl) ⟨1028618, by rfl⟩ : syracuseStep 1371491 = 2057237) B2057237
theorem B257393 : Blo 167798 257393 := bstep (se 2 (by rfl) ⟨96522, by rfl⟩ : syracuseStep 257393 = 193045) B193045
theorem B191875 : Blo 167798 191875 := bstep (se 1 (by rfl) ⟨143906, by rfl⟩ : syracuseStep 191875 = 287813) B287813
theorem B257411 : Blo 167798 257411 := bstep (se 1 (by rfl) ⟨193058, by rfl⟩ : syracuseStep 257411 = 386117) B386117
theorem B257441 : Blo 167798 257441 := bstep (se 2 (by rfl) ⟨96540, by rfl⟩ : syracuseStep 257441 = 193081) B193081
theorem B257459 : Blo 167798 257459 := bstep (se 1 (by rfl) ⟨193094, by rfl⟩ : syracuseStep 257459 = 386189) B386189
theorem B945605 : Blo 167798 945605 := bstep (se 4 (by rfl) ⟨88650, by rfl⟩ : syracuseStep 945605 = 177301) B177301
theorem B257489 : Blo 167798 257489 := bstep (se 2 (by rfl) ⟨96558, by rfl⟩ : syracuseStep 257489 = 193117) B193117
theorem B257507 : Blo 167798 257507 := bstep (se 1 (by rfl) ⟨193130, by rfl⟩ : syracuseStep 257507 = 386261) B386261
theorem B257537 : Blo 167798 257537 := bstep (se 2 (by rfl) ⟨96576, by rfl⟩ : syracuseStep 257537 = 193153) B193153
theorem B192019 : Blo 167798 192019 := bstep (se 1 (by rfl) ⟨144014, by rfl⟩ : syracuseStep 192019 = 288029) B288029
theorem B257555 : Blo 167798 257555 := bstep (se 1 (by rfl) ⟨193166, by rfl⟩ : syracuseStep 257555 = 386333) B386333
theorem B585251 : Blo 167798 585251 := bstep (se 1 (by rfl) ⟨438938, by rfl⟩ : syracuseStep 585251 = 877877) B877877
theorem B257585 : Blo 167798 257585 := bstep (se 2 (by rfl) ⟨96594, by rfl⟩ : syracuseStep 257585 = 193189) B193189
theorem B2780725 : Blo 167798 2780725 := bstep (se 5 (by rfl) ⟨130346, by rfl⟩ : syracuseStep 2780725 = 260693) B260693
theorem B257603 : Blo 167798 257603 := bstep (se 1 (by rfl) ⟨193202, by rfl⟩ : syracuseStep 257603 = 386405) B386405
theorem B257633 : Blo 167798 257633 := bstep (se 2 (by rfl) ⟨96612, by rfl⟩ : syracuseStep 257633 = 193225) B193225
theorem B454243 : Blo 167798 454243 := bstep (se 1 (by rfl) ⟨340682, by rfl⟩ : syracuseStep 454243 = 681365) B681365
theorem B257651 : Blo 167798 257651 := bstep (se 1 (by rfl) ⟨193238, by rfl⟩ : syracuseStep 257651 = 386477) B386477
theorem B257681 : Blo 167798 257681 := bstep (se 2 (by rfl) ⟨96630, by rfl⟩ : syracuseStep 257681 = 193261) B193261
theorem B192163 : Blo 167798 192163 := bstep (se 1 (by rfl) ⟨144122, by rfl⟩ : syracuseStep 192163 = 288245) B288245
theorem B323281 : Blo 167798 323281 := bstep (se 2 (by rfl) ⟨121230, by rfl⟩ : syracuseStep 323281 = 242461) B242461
theorem B192307 : Blo 167798 192307 := bstep (se 1 (by rfl) ⟨144230, by rfl⟩ : syracuseStep 192307 = 288461) B288461
theorem B487235 : Blo 167798 487235 := bstep (se 1 (by rfl) ⟨365426, by rfl⟩ : syracuseStep 487235 = 730853) B730853
theorem B1830725 : Blo 167798 1830725 := bstep (se 4 (by rfl) ⟨171630, by rfl⟩ : syracuseStep 1830725 = 343261) B343261
theorem B651149 : Blo 167798 651149 := bstep (se 3 (by rfl) ⟨122090, by rfl⟩ : syracuseStep 651149 = 244181) B244181
theorem B192451 : Blo 167798 192451 := bstep (se 1 (by rfl) ⟨144338, by rfl⟩ : syracuseStep 192451 = 288677) B288677
theorem B192595 : Blo 167798 192595 := bstep (se 1 (by rfl) ⟨144446, by rfl⟩ : syracuseStep 192595 = 288893) B288893
theorem B1667213 : Blo 167798 1667213 := bstep (se 3 (by rfl) ⟨312602, by rfl⟩ : syracuseStep 1667213 = 625205) B625205
theorem B487565 : Blo 167798 487565 := bstep (se 3 (by rfl) ⟨91418, by rfl⟩ : syracuseStep 487565 = 182837) B182837
theorem B487633 : Blo 167798 487633 := bstep (se 2 (by rfl) ⟨182862, by rfl⟩ : syracuseStep 487633 = 365725) B365725
theorem B192739 : Blo 167798 192739 := bstep (se 1 (by rfl) ⟨144554, by rfl⟩ : syracuseStep 192739 = 289109) B289109
theorem B4714805 : Blo 167798 4714805 := bstep (se 5 (by rfl) ⟨221006, by rfl⟩ : syracuseStep 4714805 = 442013) B442013
theorem B192883 : Blo 167798 192883 := bstep (se 1 (by rfl) ⟨144662, by rfl⟩ : syracuseStep 192883 = 289325) B289325
theorem B815501 : Blo 167798 815501 := bstep (se 3 (by rfl) ⟨152906, by rfl⟩ : syracuseStep 815501 = 305813) B305813
theorem B258499 : Blo 167798 258499 := bstep (se 1 (by rfl) ⟨193874, by rfl⟩ : syracuseStep 258499 = 387749) B387749
theorem B487907 : Blo 167798 487907 := bstep (se 1 (by rfl) ⟨365930, by rfl⟩ : syracuseStep 487907 = 731861) B731861
theorem B193027 : Blo 167798 193027 := bstep (se 1 (by rfl) ⟨144770, by rfl⟩ : syracuseStep 193027 = 289541) B289541
theorem B193171 : Blo 167798 193171 := bstep (se 1 (by rfl) ⟨144878, by rfl⟩ : syracuseStep 193171 = 289757) B289757
theorem B324337 : Blo 167798 324337 := bstep (se 2 (by rfl) ⟨121626, by rfl⟩ : syracuseStep 324337 = 243253) B243253
theorem B389873 : Blo 167798 389873 := bstep (se 2 (by rfl) ⟨146202, by rfl⟩ : syracuseStep 389873 = 292405) B292405
theorem B1700621 : Blo 167798 1700621 := bstep (se 3 (by rfl) ⟨318866, by rfl⟩ : syracuseStep 1700621 = 637733) B637733
theorem B717731 : Blo 167798 717731 := bstep (se 1 (by rfl) ⟨538298, by rfl⟩ : syracuseStep 717731 = 1076597) B1076597
theorem B324739 : Blo 167798 324739 := bstep (se 1 (by rfl) ⟨243554, by rfl⟩ : syracuseStep 324739 = 487109) B487109
theorem B390275 : Blo 167798 390275 := bstep (se 1 (by rfl) ⟨292706, by rfl⟩ : syracuseStep 390275 = 585413) B585413
theorem B455843 : Blo 167798 455843 := bstep (se 1 (by rfl) ⟨341882, by rfl⟩ : syracuseStep 455843 = 683765) B683765
theorem B324785 : Blo 167798 324785 := bstep (se 2 (by rfl) ⟨121794, by rfl⟩ : syracuseStep 324785 = 243589) B243589
theorem B292067 : Blo 167798 292067 := bstep (se 1 (by rfl) ⟨219050, by rfl⟩ : syracuseStep 292067 = 438101) B438101
theorem B488749 : Blo 167798 488749 := bstep (se 3 (by rfl) ⟨91640, by rfl⟩ : syracuseStep 488749 = 183281) B183281
theorem B521581 : Blo 167798 521581 := bstep (se 3 (by rfl) ⟨97796, by rfl⟩ : syracuseStep 521581 = 195593) B195593
theorem B488909 : Blo 167798 488909 := bstep (se 3 (by rfl) ⟨91670, by rfl⟩ : syracuseStep 488909 = 183341) B183341
theorem B325073 : Blo 167798 325073 := bstep (se 2 (by rfl) ⟨121902, by rfl⟩ : syracuseStep 325073 = 243805) B243805
theorem B489091 : Blo 167798 489091 := bstep (se 1 (by rfl) ⟨366818, by rfl⟩ : syracuseStep 489091 = 733637) B733637
theorem B554701 : Blo 167798 554701 := bstep (se 3 (by rfl) ⟨104006, by rfl⟩ : syracuseStep 554701 = 208013) B208013
theorem B358481 : Blo 167798 358481 := bstep (se 2 (by rfl) ⟨134430, by rfl⟩ : syracuseStep 358481 = 268861) B268861
theorem B325795 : Blo 167798 325795 := bstep (se 1 (by rfl) ⟨244346, by rfl⟩ : syracuseStep 325795 = 488693) B488693
theorem B195283 : Blo 167798 195283 := bstep (se 1 (by rfl) ⟨146462, by rfl⟩ : syracuseStep 195283 = 292925) B292925
theorem B490225 : Blo 167798 490225 := bstep (se 2 (by rfl) ⟨183834, by rfl⟩ : syracuseStep 490225 = 367669) B367669
theorem B719729 : Blo 167798 719729 := bstep (se 2 (by rfl) ⟨269898, by rfl⟩ : syracuseStep 719729 = 539797) B539797
theorem B424835 : Blo 167798 424835 := bstep (se 1 (by rfl) ⟨318626, by rfl⟩ : syracuseStep 424835 = 637253) B637253
theorem B425027 : Blo 167798 425027 := bstep (se 1 (by rfl) ⟨318770, by rfl⟩ : syracuseStep 425027 = 637541) B637541
theorem B1146275 : Blo 167798 1146275 := bstep (se 1 (by rfl) ⟨859706, by rfl⟩ : syracuseStep 1146275 = 1719413) B1719413
theorem B1080773 : Blo 167798 1080773 := bstep (se 4 (by rfl) ⟨101322, by rfl⟩ : syracuseStep 1080773 = 202645) B202645
theorem B851633 : Blo 167798 851633 := bstep (se 2 (by rfl) ⟨319362, by rfl⟩ : syracuseStep 851633 = 638725) B638725
theorem B229187 : Blo 167798 229187 := bstep (se 1 (by rfl) ⟨171890, by rfl⟩ : syracuseStep 229187 = 343781) B343781
theorem B425969 : Blo 167798 425969 := bstep (se 2 (by rfl) ⟨159738, by rfl⟩ : syracuseStep 425969 = 319477) B319477
theorem B983171 : Blo 167798 983171 := bstep (se 1 (by rfl) ⟨737378, by rfl⟩ : syracuseStep 983171 = 1474757) B1474757
theorem B852119 : Blo 167798 852119 := bstep (se 1 (by rfl) ⟨639089, by rfl⟩ : syracuseStep 852119 = 1278179) B1278179
theorem B1442123 : Blo 167798 1442123 := bstep (se 1 (by rfl) ⟨1081592, by rfl⟩ : syracuseStep 1442123 = 2163185) B2163185
theorem B1049219 : Blo 167798 1049219 := bstep (se 1 (by rfl) ⟨786914, by rfl⟩ : syracuseStep 1049219 = 1573829) B1573829
theorem B426647 : Blo 167798 426647 := bstep (se 1 (by rfl) ⟨319985, by rfl⟩ : syracuseStep 426647 = 639971) B639971
theorem B983909 : Blo 167798 983909 := bstep (se 4 (by rfl) ⟨92241, by rfl⟩ : syracuseStep 983909 = 184483) B184483
theorem B2196341 : Blo 167798 2196341 := bstep (se 5 (by rfl) ⟨102953, by rfl⟩ : syracuseStep 2196341 = 205907) B205907
theorem B1213505 : Blo 167798 1213505 := bstep (se 2 (by rfl) ⟨455064, by rfl⟩ : syracuseStep 1213505 = 910129) B910129
theorem B361675 : Blo 167798 361675 := bstep (se 1 (by rfl) ⟨271256, by rfl⟩ : syracuseStep 361675 = 542513) B542513
theorem B689411 : Blo 167798 689411 := bstep (se 1 (by rfl) ⟨517058, by rfl⟩ : syracuseStep 689411 = 1034117) B1034117
theorem B427315 : Blo 167798 427315 := bstep (se 1 (by rfl) ⟨320486, by rfl⟩ : syracuseStep 427315 = 640973) B640973
theorem B918935 : Blo 167798 918935 := bstep (se 1 (by rfl) ⟨689201, by rfl⟩ : syracuseStep 918935 = 1378403) B1378403
theorem B427457 : Blo 167798 427457 := bstep (se 2 (by rfl) ⟨160296, by rfl⟩ : syracuseStep 427457 = 320593) B320593
theorem B362009 : Blo 167798 362009 := bstep (se 2 (by rfl) ⟨135753, by rfl⟩ : syracuseStep 362009 = 271507) B271507
theorem B1214027 : Blo 167798 1214027 := bstep (se 1 (by rfl) ⟨910520, by rfl⟩ : syracuseStep 1214027 = 1821041) B1821041
theorem B493249 : Blo 167798 493249 := bstep (se 2 (by rfl) ⟨184968, by rfl⟩ : syracuseStep 493249 = 369937) B369937
theorem B329665 : Blo 167798 329665 := bstep (se 2 (by rfl) ⟨123624, by rfl⟩ : syracuseStep 329665 = 247249) B247249
theorem B428723 : Blo 167798 428723 := bstep (se 1 (by rfl) ⟨321542, by rfl⟩ : syracuseStep 428723 = 643085) B643085
theorem B1084205 : Blo 167798 1084205 := bstep (se 3 (by rfl) ⟨203288, by rfl⟩ : syracuseStep 1084205 = 406577) B406577
theorem B1444787 : Blo 167798 1444787 := bstep (se 1 (by rfl) ⟨1083590, by rfl⟩ : syracuseStep 1444787 = 2167181) B2167181
theorem B363521 : Blo 167798 363521 := bstep (se 2 (by rfl) ⟨136320, by rfl⟩ : syracuseStep 363521 = 272641) B272641
theorem B691289 : Blo 167798 691289 := bstep (se 2 (by rfl) ⟨259233, by rfl⟩ : syracuseStep 691289 = 518467) B518467
theorem B429259 : Blo 167798 429259 := bstep (se 1 (by rfl) ⟨321944, by rfl⟩ : syracuseStep 429259 = 643889) B643889
theorem B429401 : Blo 167798 429401 := bstep (se 2 (by rfl) ⟨161025, by rfl⟩ : syracuseStep 429401 = 322051) B322051
theorem B495065 : Blo 167798 495065 := bstep (se 2 (by rfl) ⟨185649, by rfl⟩ : syracuseStep 495065 = 371299) B371299
theorem B1281581 : Blo 167798 1281581 := bstep (se 3 (by rfl) ⟨240296, by rfl⟩ : syracuseStep 1281581 = 480593) B480593
theorem B855683 : Blo 167798 855683 := bstep (se 1 (by rfl) ⟨641762, by rfl⟩ : syracuseStep 855683 = 1283525) B1283525
theorem B724787 : Blo 167798 724787 := bstep (se 1 (by rfl) ⟨543590, by rfl⟩ : syracuseStep 724787 = 1087181) B1087181
theorem B462667 : Blo 167798 462667 := bstep (se 1 (by rfl) ⟨347000, by rfl⟩ : syracuseStep 462667 = 694001) B694001
theorem B364375 : Blo 167798 364375 := bstep (se 1 (by rfl) ⟨273281, by rfl⟩ : syracuseStep 364375 = 546563) B546563
theorem B167799 : Blo 167798 167799 := bstep (se 1 (by rfl) ⟨125849, by rfl⟩ : syracuseStep 167799 = 251699) B251699
theorem B167819 : Blo 167798 167819 := bstep (se 1 (by rfl) ⟨125864, by rfl⟩ : syracuseStep 167819 = 251729) B251729
theorem B167831 : Blo 167798 167831 := bstep (se 1 (by rfl) ⟨125873, by rfl⟩ : syracuseStep 167831 = 251747) B251747
theorem B167851 : Blo 167798 167851 := bstep (se 1 (by rfl) ⟨125888, by rfl⟩ : syracuseStep 167851 = 251777) B251777
theorem B167863 : Blo 167798 167863 := bstep (se 1 (by rfl) ⟨125897, by rfl⟩ : syracuseStep 167863 = 251795) B251795
theorem B167883 : Blo 167798 167883 := bstep (se 1 (by rfl) ⟨125912, by rfl⟩ : syracuseStep 167883 = 251825) B251825
theorem B167895 : Blo 167798 167895 := bstep (se 1 (by rfl) ⟨125921, by rfl⟩ : syracuseStep 167895 = 251843) B251843
theorem B1445849 : Blo 167798 1445849 := bstep (se 2 (by rfl) ⟨542193, by rfl⟩ : syracuseStep 1445849 = 1084387) B1084387
theorem B167915 : Blo 167798 167915 := bstep (se 1 (by rfl) ⟨125936, by rfl⟩ : syracuseStep 167915 = 251873) B251873
theorem B167927 : Blo 167798 167927 := bstep (se 1 (by rfl) ⟨125945, by rfl⟩ : syracuseStep 167927 = 251891) B251891
theorem B167947 : Blo 167798 167947 := bstep (se 1 (by rfl) ⟨125960, by rfl⟩ : syracuseStep 167947 = 251921) B251921
theorem B167959 : Blo 167798 167959 := bstep (se 1 (by rfl) ⟨125969, by rfl⟩ : syracuseStep 167959 = 251939) B251939
theorem B167979 : Blo 167798 167979 := bstep (se 1 (by rfl) ⟨125984, by rfl⟩ : syracuseStep 167979 = 251969) B251969
theorem B167991 : Blo 167798 167991 := bstep (se 1 (by rfl) ⟨125993, by rfl⟩ : syracuseStep 167991 = 251987) B251987
theorem B168011 : Blo 167798 168011 := bstep (se 1 (by rfl) ⟨126008, by rfl⟩ : syracuseStep 168011 = 252017) B252017
theorem B168023 : Blo 167798 168023 := bstep (se 1 (by rfl) ⟨126017, by rfl⟩ : syracuseStep 168023 = 252035) B252035
theorem B462941 : Blo 167798 462941 := bstep (se 3 (by rfl) ⟨86801, by rfl⟩ : syracuseStep 462941 = 173603) B173603
theorem B168043 : Blo 167798 168043 := bstep (se 1 (by rfl) ⟨126032, by rfl⟩ : syracuseStep 168043 = 252065) B252065
theorem B168055 : Blo 167798 168055 := bstep (se 1 (by rfl) ⟨126041, by rfl⟩ : syracuseStep 168055 = 252083) B252083
theorem B168075 : Blo 167798 168075 := bstep (se 1 (by rfl) ⟨126056, by rfl⟩ : syracuseStep 168075 = 252113) B252113
theorem B168087 : Blo 167798 168087 := bstep (se 1 (by rfl) ⟨126065, by rfl⟩ : syracuseStep 168087 = 252131) B252131
theorem B430231 : Blo 167798 430231 := bstep (se 1 (by rfl) ⟨322673, by rfl⟩ : syracuseStep 430231 = 645347) B645347
theorem B1380503 : Blo 167798 1380503 := bstep (se 1 (by rfl) ⟨1035377, by rfl⟩ : syracuseStep 1380503 = 2070755) B2070755
theorem B168107 : Blo 167798 168107 := bstep (se 1 (by rfl) ⟨126080, by rfl⟩ : syracuseStep 168107 = 252161) B252161
theorem B168119 : Blo 167798 168119 := bstep (se 1 (by rfl) ⟨126089, by rfl⟩ : syracuseStep 168119 = 252179) B252179
theorem B168139 : Blo 167798 168139 := bstep (se 1 (by rfl) ⟨126104, by rfl⟩ : syracuseStep 168139 = 252209) B252209
theorem B168151 : Blo 167798 168151 := bstep (se 1 (by rfl) ⟨126113, by rfl⟩ : syracuseStep 168151 = 252227) B252227
theorem B168171 : Blo 167798 168171 := bstep (se 1 (by rfl) ⟨126128, by rfl⟩ : syracuseStep 168171 = 252257) B252257
theorem B168183 : Blo 167798 168183 := bstep (se 1 (by rfl) ⟨126137, by rfl⟩ : syracuseStep 168183 = 252275) B252275
theorem B168203 : Blo 167798 168203 := bstep (se 1 (by rfl) ⟨126152, by rfl⟩ : syracuseStep 168203 = 252305) B252305
theorem B18583829 : Blo 167798 18583829 := bstep (se 6 (by rfl) ⟨435558, by rfl⟩ : syracuseStep 18583829 = 871117) B871117
theorem B168215 : Blo 167798 168215 := bstep (se 1 (by rfl) ⟨126161, by rfl⟩ : syracuseStep 168215 = 252323) B252323
theorem B168235 : Blo 167798 168235 := bstep (se 1 (by rfl) ⟨126176, by rfl⟩ : syracuseStep 168235 = 252353) B252353
theorem B168247 : Blo 167798 168247 := bstep (se 1 (by rfl) ⟨126185, by rfl⟩ : syracuseStep 168247 = 252371) B252371
theorem B168267 : Blo 167798 168267 := bstep (se 1 (by rfl) ⟨126200, by rfl⟩ : syracuseStep 168267 = 252401) B252401
theorem B168279 : Blo 167798 168279 := bstep (se 1 (by rfl) ⟨126209, by rfl⟩ : syracuseStep 168279 = 252419) B252419
theorem B168299 : Blo 167798 168299 := bstep (se 1 (by rfl) ⟨126224, by rfl⟩ : syracuseStep 168299 = 252449) B252449
theorem B168311 : Blo 167798 168311 := bstep (se 1 (by rfl) ⟨126233, by rfl⟩ : syracuseStep 168311 = 252467) B252467
theorem B168331 : Blo 167798 168331 := bstep (se 1 (by rfl) ⟨126248, by rfl⟩ : syracuseStep 168331 = 252497) B252497
theorem B168343 : Blo 167798 168343 := bstep (se 1 (by rfl) ⟨126257, by rfl⟩ : syracuseStep 168343 = 252515) B252515
theorem B168363 : Blo 167798 168363 := bstep (se 1 (by rfl) ⟨126272, by rfl⟩ : syracuseStep 168363 = 252545) B252545
theorem B463283 : Blo 167798 463283 := bstep (se 1 (by rfl) ⟨347462, by rfl⟩ : syracuseStep 463283 = 694925) B694925
theorem B168375 : Blo 167798 168375 := bstep (se 1 (by rfl) ⟨126281, by rfl⟩ : syracuseStep 168375 = 252563) B252563
theorem B168395 : Blo 167798 168395 := bstep (se 1 (by rfl) ⟨126296, by rfl⟩ : syracuseStep 168395 = 252593) B252593
theorem B168407 : Blo 167798 168407 := bstep (se 1 (by rfl) ⟨126305, by rfl⟩ : syracuseStep 168407 = 252611) B252611
theorem B168427 : Blo 167798 168427 := bstep (se 1 (by rfl) ⟨126320, by rfl⟩ : syracuseStep 168427 = 252641) B252641
theorem B168439 : Blo 167798 168439 := bstep (se 1 (by rfl) ⟨126329, by rfl⟩ : syracuseStep 168439 = 252659) B252659
theorem B168459 : Blo 167798 168459 := bstep (se 1 (by rfl) ⟨126344, by rfl⟩ : syracuseStep 168459 = 252689) B252689
theorem B168471 : Blo 167798 168471 := bstep (se 1 (by rfl) ⟨126353, by rfl⟩ : syracuseStep 168471 = 252707) B252707
theorem B168491 : Blo 167798 168491 := bstep (se 1 (by rfl) ⟨126368, by rfl⟩ : syracuseStep 168491 = 252737) B252737
theorem B430643 : Blo 167798 430643 := bstep (se 1 (by rfl) ⟨322982, by rfl⟩ : syracuseStep 430643 = 645965) B645965
theorem B168503 : Blo 167798 168503 := bstep (se 1 (by rfl) ⟨126377, by rfl⟩ : syracuseStep 168503 = 252755) B252755
theorem B168523 : Blo 167798 168523 := bstep (se 1 (by rfl) ⟨126392, by rfl⟩ : syracuseStep 168523 = 252785) B252785
theorem B430667 : Blo 167798 430667 := bstep (se 1 (by rfl) ⟨323000, by rfl⟩ : syracuseStep 430667 = 646001) B646001
theorem B168535 : Blo 167798 168535 := bstep (se 1 (by rfl) ⟨126401, by rfl⟩ : syracuseStep 168535 = 252803) B252803
theorem B168555 : Blo 167798 168555 := bstep (se 1 (by rfl) ⟨126416, by rfl⟩ : syracuseStep 168555 = 252833) B252833
theorem B168567 : Blo 167798 168567 := bstep (se 1 (by rfl) ⟨126425, by rfl⟩ : syracuseStep 168567 = 252851) B252851
theorem B168587 : Blo 167798 168587 := bstep (se 1 (by rfl) ⟨126440, by rfl⟩ : syracuseStep 168587 = 252881) B252881
theorem B365195 : Blo 167798 365195 := bstep (se 1 (by rfl) ⟨273896, by rfl⟩ : syracuseStep 365195 = 547793) B547793
theorem B168599 : Blo 167798 168599 := bstep (se 1 (by rfl) ⟨126449, by rfl⟩ : syracuseStep 168599 = 252899) B252899
theorem B168619 : Blo 167798 168619 := bstep (se 1 (by rfl) ⟨126464, by rfl⟩ : syracuseStep 168619 = 252929) B252929
theorem B168631 : Blo 167798 168631 := bstep (se 1 (by rfl) ⟨126473, by rfl⟩ : syracuseStep 168631 = 252947) B252947
theorem B168651 : Blo 167798 168651 := bstep (se 1 (by rfl) ⟨126488, by rfl⟩ : syracuseStep 168651 = 252977) B252977
theorem B168663 : Blo 167798 168663 := bstep (se 1 (by rfl) ⟨126497, by rfl⟩ : syracuseStep 168663 = 252995) B252995
theorem B168683 : Blo 167798 168683 := bstep (se 1 (by rfl) ⟨126512, by rfl⟩ : syracuseStep 168683 = 253025) B253025
theorem B3707633 : Blo 167798 3707633 := bstep (se 2 (by rfl) ⟨1390362, by rfl⟩ : syracuseStep 3707633 = 2780725) B2780725
theorem B168695 : Blo 167798 168695 := bstep (se 1 (by rfl) ⟨126521, by rfl⟩ : syracuseStep 168695 = 253043) B253043
theorem B168715 : Blo 167798 168715 := bstep (se 1 (by rfl) ⟨126536, by rfl⟩ : syracuseStep 168715 = 253073) B253073
theorem B168727 : Blo 167798 168727 := bstep (se 1 (by rfl) ⟨126545, by rfl⟩ : syracuseStep 168727 = 253091) B253091
theorem B168747 : Blo 167798 168747 := bstep (se 1 (by rfl) ⟨126560, by rfl⟩ : syracuseStep 168747 = 253121) B253121
theorem B168759 : Blo 167798 168759 := bstep (se 1 (by rfl) ⟨126569, by rfl⟩ : syracuseStep 168759 = 253139) B253139
theorem B168779 : Blo 167798 168779 := bstep (se 1 (by rfl) ⟨126584, by rfl⟩ : syracuseStep 168779 = 253169) B253169
theorem B168791 : Blo 167798 168791 := bstep (se 1 (by rfl) ⟨126593, by rfl⟩ : syracuseStep 168791 = 253187) B253187
theorem B168811 : Blo 167798 168811 := bstep (se 1 (by rfl) ⟨126608, by rfl⟩ : syracuseStep 168811 = 253217) B253217
theorem B168823 : Blo 167798 168823 := bstep (se 1 (by rfl) ⟨126617, by rfl⟩ : syracuseStep 168823 = 253235) B253235
theorem B168843 : Blo 167798 168843 := bstep (se 1 (by rfl) ⟨126632, by rfl⟩ : syracuseStep 168843 = 253265) B253265
theorem B168855 : Blo 167798 168855 := bstep (se 1 (by rfl) ⟨126641, by rfl⟩ : syracuseStep 168855 = 253283) B253283
theorem B168875 : Blo 167798 168875 := bstep (se 1 (by rfl) ⟨126656, by rfl⟩ : syracuseStep 168875 = 253313) B253313
theorem B168887 : Blo 167798 168887 := bstep (se 1 (by rfl) ⟨126665, by rfl⟩ : syracuseStep 168887 = 253331) B253331
theorem B431041 : Blo 167798 431041 := bstep (se 2 (by rfl) ⟨161640, by rfl⟩ : syracuseStep 431041 = 323281) B323281
theorem B168907 : Blo 167798 168907 := bstep (se 1 (by rfl) ⟨126680, by rfl⟩ : syracuseStep 168907 = 253361) B253361
theorem B168919 : Blo 167798 168919 := bstep (se 1 (by rfl) ⟨126689, by rfl⟩ : syracuseStep 168919 = 253379) B253379
theorem B168939 : Blo 167798 168939 := bstep (se 1 (by rfl) ⟨126704, by rfl⟩ : syracuseStep 168939 = 253409) B253409
theorem B168951 : Blo 167798 168951 := bstep (se 1 (by rfl) ⟨126713, by rfl⟩ : syracuseStep 168951 = 253427) B253427
theorem B168971 : Blo 167798 168971 := bstep (se 1 (by rfl) ⟨126728, by rfl⟩ : syracuseStep 168971 = 253457) B253457
theorem B168983 : Blo 167798 168983 := bstep (se 1 (by rfl) ⟨126737, by rfl⟩ : syracuseStep 168983 = 253475) B253475
theorem B169003 : Blo 167798 169003 := bstep (se 1 (by rfl) ⟨126752, by rfl⟩ : syracuseStep 169003 = 253505) B253505
theorem B169015 : Blo 167798 169015 := bstep (se 1 (by rfl) ⟨126761, by rfl⟩ : syracuseStep 169015 = 253523) B253523
theorem B169035 : Blo 167798 169035 := bstep (se 1 (by rfl) ⟨126776, by rfl⟩ : syracuseStep 169035 = 253553) B253553
theorem B169047 : Blo 167798 169047 := bstep (se 1 (by rfl) ⟨126785, by rfl⟩ : syracuseStep 169047 = 253571) B253571
theorem B169067 : Blo 167798 169067 := bstep (se 1 (by rfl) ⟨126800, by rfl⟩ : syracuseStep 169067 = 253601) B253601
theorem B169079 : Blo 167798 169079 := bstep (se 1 (by rfl) ⟨126809, by rfl⟩ : syracuseStep 169079 = 253619) B253619
theorem B169099 : Blo 167798 169099 := bstep (se 1 (by rfl) ⟨126824, by rfl⟩ : syracuseStep 169099 = 253649) B253649
theorem B169111 : Blo 167798 169111 := bstep (se 1 (by rfl) ⟨126833, by rfl⟩ : syracuseStep 169111 = 253667) B253667
theorem B169131 : Blo 167798 169131 := bstep (se 1 (by rfl) ⟨126848, by rfl⟩ : syracuseStep 169131 = 253697) B253697
theorem B464051 : Blo 167798 464051 := bstep (se 1 (by rfl) ⟨348038, by rfl⟩ : syracuseStep 464051 = 696077) B696077
theorem B169143 : Blo 167798 169143 := bstep (se 1 (by rfl) ⟨126857, by rfl⟩ : syracuseStep 169143 = 253715) B253715
theorem B169163 : Blo 167798 169163 := bstep (se 1 (by rfl) ⟨126872, by rfl⟩ : syracuseStep 169163 = 253745) B253745
theorem B169175 : Blo 167798 169175 := bstep (se 1 (by rfl) ⟨126881, by rfl⟩ : syracuseStep 169175 = 253763) B253763
theorem B169195 : Blo 167798 169195 := bstep (se 1 (by rfl) ⟨126896, by rfl⟩ : syracuseStep 169195 = 253793) B253793
theorem B169207 : Blo 167798 169207 := bstep (se 1 (by rfl) ⟨126905, by rfl⟩ : syracuseStep 169207 = 253811) B253811
theorem B169227 : Blo 167798 169227 := bstep (se 1 (by rfl) ⟨126920, by rfl⟩ : syracuseStep 169227 = 253841) B253841
theorem B169239 : Blo 167798 169239 := bstep (se 1 (by rfl) ⟨126929, by rfl⟩ : syracuseStep 169239 = 253859) B253859
theorem B169259 : Blo 167798 169259 := bstep (se 1 (by rfl) ⟨126944, by rfl⟩ : syracuseStep 169259 = 253889) B253889
theorem B169271 : Blo 167798 169271 := bstep (se 1 (by rfl) ⟨126953, by rfl⟩ : syracuseStep 169271 = 253907) B253907
theorem B169291 : Blo 167798 169291 := bstep (se 1 (by rfl) ⟨126968, by rfl⟩ : syracuseStep 169291 = 253937) B253937
theorem B169303 : Blo 167798 169303 := bstep (se 1 (by rfl) ⟨126977, by rfl⟩ : syracuseStep 169303 = 253955) B253955
theorem B169323 : Blo 167798 169323 := bstep (se 1 (by rfl) ⟨126992, by rfl⟩ : syracuseStep 169323 = 253985) B253985
theorem B169335 : Blo 167798 169335 := bstep (se 1 (by rfl) ⟨127001, by rfl⟩ : syracuseStep 169335 = 254003) B254003
theorem B169355 : Blo 167798 169355 := bstep (se 1 (by rfl) ⟨127016, by rfl⟩ : syracuseStep 169355 = 254033) B254033
theorem B169367 : Blo 167798 169367 := bstep (se 1 (by rfl) ⟨127025, by rfl⟩ : syracuseStep 169367 = 254051) B254051
theorem B1086871 : Blo 167798 1086871 := bstep (se 1 (by rfl) ⟨815153, by rfl⟩ : syracuseStep 1086871 = 1630307) B1630307
theorem B169387 : Blo 167798 169387 := bstep (se 1 (by rfl) ⟨127040, by rfl⟩ : syracuseStep 169387 = 254081) B254081
theorem B169399 : Blo 167798 169399 := bstep (se 1 (by rfl) ⟨127049, by rfl⟩ : syracuseStep 169399 = 254099) B254099
theorem B169419 : Blo 167798 169419 := bstep (se 1 (by rfl) ⟨127064, by rfl⟩ : syracuseStep 169419 = 254129) B254129
theorem B169431 : Blo 167798 169431 := bstep (se 1 (by rfl) ⟨127073, by rfl⟩ : syracuseStep 169431 = 254147) B254147
theorem B169451 : Blo 167798 169451 := bstep (se 1 (by rfl) ⟨127088, by rfl⟩ : syracuseStep 169451 = 254177) B254177
theorem B169463 : Blo 167798 169463 := bstep (se 1 (by rfl) ⟨127097, by rfl⟩ : syracuseStep 169463 = 254195) B254195
theorem B169483 : Blo 167798 169483 := bstep (se 1 (by rfl) ⟨127112, by rfl⟩ : syracuseStep 169483 = 254225) B254225
theorem B169495 : Blo 167798 169495 := bstep (se 1 (by rfl) ⟨127121, by rfl⟩ : syracuseStep 169495 = 254243) B254243
theorem B431639 : Blo 167798 431639 := bstep (se 1 (by rfl) ⟨323729, by rfl⟩ : syracuseStep 431639 = 647459) B647459
theorem B169515 : Blo 167798 169515 := bstep (se 1 (by rfl) ⟨127136, by rfl⟩ : syracuseStep 169515 = 254273) B254273
theorem B169527 : Blo 167798 169527 := bstep (se 1 (by rfl) ⟨127145, by rfl⟩ : syracuseStep 169527 = 254291) B254291
theorem B169547 : Blo 167798 169547 := bstep (se 1 (by rfl) ⟨127160, by rfl⟩ : syracuseStep 169547 = 254321) B254321
theorem B169559 : Blo 167798 169559 := bstep (se 1 (by rfl) ⟨127169, by rfl⟩ : syracuseStep 169559 = 254339) B254339
theorem B169579 : Blo 167798 169579 := bstep (se 1 (by rfl) ⟨127184, by rfl⟩ : syracuseStep 169579 = 254369) B254369
theorem B169591 : Blo 167798 169591 := bstep (se 1 (by rfl) ⟨127193, by rfl⟩ : syracuseStep 169591 = 254387) B254387
theorem B169611 : Blo 167798 169611 := bstep (se 1 (by rfl) ⟨127208, by rfl⟩ : syracuseStep 169611 = 254417) B254417
theorem B169623 : Blo 167798 169623 := bstep (se 1 (by rfl) ⟨127217, by rfl⟩ : syracuseStep 169623 = 254435) B254435
theorem B169643 : Blo 167798 169643 := bstep (se 1 (by rfl) ⟨127232, by rfl⟩ : syracuseStep 169643 = 254465) B254465
theorem B956083 : Blo 167798 956083 := bstep (se 1 (by rfl) ⟨717062, by rfl⟩ : syracuseStep 956083 = 1434125) B1434125
theorem B169655 : Blo 167798 169655 := bstep (se 1 (by rfl) ⟨127241, by rfl⟩ : syracuseStep 169655 = 254483) B254483
theorem B169675 : Blo 167798 169675 := bstep (se 1 (by rfl) ⟨127256, by rfl⟩ : syracuseStep 169675 = 254513) B254513
theorem B169687 : Blo 167798 169687 := bstep (se 1 (by rfl) ⟨127265, by rfl⟩ : syracuseStep 169687 = 254531) B254531
theorem B169707 : Blo 167798 169707 := bstep (se 1 (by rfl) ⟨127280, by rfl⟩ : syracuseStep 169707 = 254561) B254561
theorem B169719 : Blo 167798 169719 := bstep (se 1 (by rfl) ⟨127289, by rfl⟩ : syracuseStep 169719 = 254579) B254579
theorem B169739 : Blo 167798 169739 := bstep (se 1 (by rfl) ⟨127304, by rfl⟩ : syracuseStep 169739 = 254609) B254609
theorem B169751 : Blo 167798 169751 := bstep (se 1 (by rfl) ⟨127313, by rfl⟩ : syracuseStep 169751 = 254627) B254627
theorem B169771 : Blo 167798 169771 := bstep (se 1 (by rfl) ⟨127328, by rfl⟩ : syracuseStep 169771 = 254657) B254657
theorem B169783 : Blo 167798 169783 := bstep (se 1 (by rfl) ⟨127337, by rfl⟩ : syracuseStep 169783 = 254675) B254675
theorem B169803 : Blo 167798 169803 := bstep (se 1 (by rfl) ⟨127352, by rfl⟩ : syracuseStep 169803 = 254705) B254705
theorem B169815 : Blo 167798 169815 := bstep (se 1 (by rfl) ⟨127361, by rfl⟩ : syracuseStep 169815 = 254723) B254723
theorem B169835 : Blo 167798 169835 := bstep (se 1 (by rfl) ⟨127376, by rfl⟩ : syracuseStep 169835 = 254753) B254753
theorem B169847 : Blo 167798 169847 := bstep (se 1 (by rfl) ⟨127385, by rfl⟩ : syracuseStep 169847 = 254771) B254771
theorem B169867 : Blo 167798 169867 := bstep (se 1 (by rfl) ⟨127400, by rfl⟩ : syracuseStep 169867 = 254801) B254801
theorem B169879 : Blo 167798 169879 := bstep (se 1 (by rfl) ⟨127409, by rfl⟩ : syracuseStep 169879 = 254819) B254819
theorem B169899 : Blo 167798 169899 := bstep (se 1 (by rfl) ⟨127424, by rfl⟩ : syracuseStep 169899 = 254849) B254849
theorem B1382321 : Blo 167798 1382321 := bstep (se 2 (by rfl) ⟨518370, by rfl⟩ : syracuseStep 1382321 = 1036741) B1036741
theorem B169911 : Blo 167798 169911 := bstep (se 1 (by rfl) ⟨127433, by rfl⟩ : syracuseStep 169911 = 254867) B254867
theorem B169931 : Blo 167798 169931 := bstep (se 1 (by rfl) ⟨127448, by rfl⟩ : syracuseStep 169931 = 254897) B254897
theorem B169943 : Blo 167798 169943 := bstep (se 1 (by rfl) ⟨127457, by rfl⟩ : syracuseStep 169943 = 254915) B254915
theorem B169963 : Blo 167798 169963 := bstep (se 1 (by rfl) ⟨127472, by rfl⟩ : syracuseStep 169963 = 254945) B254945
theorem B169975 : Blo 167798 169975 := bstep (se 1 (by rfl) ⟨127481, by rfl⟩ : syracuseStep 169975 = 254963) B254963
theorem B169995 : Blo 167798 169995 := bstep (se 1 (by rfl) ⟨127496, by rfl⟩ : syracuseStep 169995 = 254993) B254993
theorem B170007 : Blo 167798 170007 := bstep (se 1 (by rfl) ⟨127505, by rfl⟩ : syracuseStep 170007 = 255011) B255011
theorem B170027 : Blo 167798 170027 := bstep (se 1 (by rfl) ⟨127520, by rfl⟩ : syracuseStep 170027 = 255041) B255041
theorem B170039 : Blo 167798 170039 := bstep (se 1 (by rfl) ⟨127529, by rfl⟩ : syracuseStep 170039 = 255059) B255059
theorem B170059 : Blo 167798 170059 := bstep (se 1 (by rfl) ⟨127544, by rfl⟩ : syracuseStep 170059 = 255089) B255089
theorem B170071 : Blo 167798 170071 := bstep (se 1 (by rfl) ⟨127553, by rfl⟩ : syracuseStep 170071 = 255107) B255107
theorem B170091 : Blo 167798 170091 := bstep (se 1 (by rfl) ⟨127568, by rfl⟩ : syracuseStep 170091 = 255137) B255137
theorem B170103 : Blo 167798 170103 := bstep (se 1 (by rfl) ⟨127577, by rfl⟩ : syracuseStep 170103 = 255155) B255155
theorem B170123 : Blo 167798 170123 := bstep (se 1 (by rfl) ⟨127592, by rfl⟩ : syracuseStep 170123 = 255185) B255185
theorem B170135 : Blo 167798 170135 := bstep (se 1 (by rfl) ⟨127601, by rfl⟩ : syracuseStep 170135 = 255203) B255203
theorem B170155 : Blo 167798 170155 := bstep (se 1 (by rfl) ⟨127616, by rfl⟩ : syracuseStep 170155 = 255233) B255233
theorem B170167 : Blo 167798 170167 := bstep (se 1 (by rfl) ⟨127625, by rfl⟩ : syracuseStep 170167 = 255251) B255251
theorem B170187 : Blo 167798 170187 := bstep (se 1 (by rfl) ⟨127640, by rfl⟩ : syracuseStep 170187 = 255281) B255281
theorem B170199 : Blo 167798 170199 := bstep (se 1 (by rfl) ⟨127649, by rfl⟩ : syracuseStep 170199 = 255299) B255299
theorem B170219 : Blo 167798 170219 := bstep (se 1 (by rfl) ⟨127664, by rfl⟩ : syracuseStep 170219 = 255329) B255329
theorem B170231 : Blo 167798 170231 := bstep (se 1 (by rfl) ⟨127673, by rfl⟩ : syracuseStep 170231 = 255347) B255347
theorem B170251 : Blo 167798 170251 := bstep (se 1 (by rfl) ⟨127688, by rfl⟩ : syracuseStep 170251 = 255377) B255377
theorem B170263 : Blo 167798 170263 := bstep (se 1 (by rfl) ⟨127697, by rfl⟩ : syracuseStep 170263 = 255395) B255395
theorem B170283 : Blo 167798 170283 := bstep (se 1 (by rfl) ⟨127712, by rfl⟩ : syracuseStep 170283 = 255425) B255425
theorem B170295 : Blo 167798 170295 := bstep (se 1 (by rfl) ⟨127721, by rfl⟩ : syracuseStep 170295 = 255443) B255443
theorem B432449 : Blo 167798 432449 := bstep (se 2 (by rfl) ⟨162168, by rfl⟩ : syracuseStep 432449 = 324337) B324337
theorem B170315 : Blo 167798 170315 := bstep (se 1 (by rfl) ⟨127736, by rfl⟩ : syracuseStep 170315 = 255473) B255473
theorem B170327 : Blo 167798 170327 := bstep (se 1 (by rfl) ⟨127745, by rfl⟩ : syracuseStep 170327 = 255491) B255491
theorem B170347 : Blo 167798 170347 := bstep (se 1 (by rfl) ⟨127760, by rfl⟩ : syracuseStep 170347 = 255521) B255521
theorem B170359 : Blo 167798 170359 := bstep (se 1 (by rfl) ⟨127769, by rfl⟩ : syracuseStep 170359 = 255539) B255539
theorem B170379 : Blo 167798 170379 := bstep (se 1 (by rfl) ⟨127784, by rfl⟩ : syracuseStep 170379 = 255569) B255569
theorem B170391 : Blo 167798 170391 := bstep (se 1 (by rfl) ⟨127793, by rfl⟩ : syracuseStep 170391 = 255587) B255587
theorem B170411 : Blo 167798 170411 := bstep (se 1 (by rfl) ⟨127808, by rfl⟩ : syracuseStep 170411 = 255617) B255617
theorem B170423 : Blo 167798 170423 := bstep (se 1 (by rfl) ⟨127817, by rfl⟩ : syracuseStep 170423 = 255635) B255635
theorem B170443 : Blo 167798 170443 := bstep (se 1 (by rfl) ⟨127832, by rfl⟩ : syracuseStep 170443 = 255665) B255665
theorem B170455 : Blo 167798 170455 := bstep (se 1 (by rfl) ⟨127841, by rfl⟩ : syracuseStep 170455 = 255683) B255683
theorem B170475 : Blo 167798 170475 := bstep (se 1 (by rfl) ⟨127856, by rfl⟩ : syracuseStep 170475 = 255713) B255713
theorem B170487 : Blo 167798 170487 := bstep (se 1 (by rfl) ⟨127865, by rfl⟩ : syracuseStep 170487 = 255731) B255731
theorem B170507 : Blo 167798 170507 := bstep (se 1 (by rfl) ⟨127880, by rfl⟩ : syracuseStep 170507 = 255761) B255761
theorem B170519 : Blo 167798 170519 := bstep (se 1 (by rfl) ⟨127889, by rfl⟩ : syracuseStep 170519 = 255779) B255779
theorem B170539 : Blo 167798 170539 := bstep (se 1 (by rfl) ⟨127904, by rfl⟩ : syracuseStep 170539 = 255809) B255809
theorem B170551 : Blo 167798 170551 := bstep (se 1 (by rfl) ⟨127913, by rfl⟩ : syracuseStep 170551 = 255827) B255827
theorem B170571 : Blo 167798 170571 := bstep (se 1 (by rfl) ⟨127928, by rfl⟩ : syracuseStep 170571 = 255857) B255857
theorem B170583 : Blo 167798 170583 := bstep (se 1 (by rfl) ⟨127937, by rfl⟩ : syracuseStep 170583 = 255875) B255875
theorem B170603 : Blo 167798 170603 := bstep (se 1 (by rfl) ⟨127952, by rfl⟩ : syracuseStep 170603 = 255905) B255905
theorem B170615 : Blo 167798 170615 := bstep (se 1 (by rfl) ⟨127961, by rfl⟩ : syracuseStep 170615 = 255923) B255923
theorem B170635 : Blo 167798 170635 := bstep (se 1 (by rfl) ⟨127976, by rfl⟩ : syracuseStep 170635 = 255953) B255953
theorem B170647 : Blo 167798 170647 := bstep (se 1 (by rfl) ⟨127985, by rfl⟩ : syracuseStep 170647 = 255971) B255971
theorem B170667 : Blo 167798 170667 := bstep (se 1 (by rfl) ⟨128000, by rfl⟩ : syracuseStep 170667 = 256001) B256001
theorem B170679 : Blo 167798 170679 := bstep (se 1 (by rfl) ⟨128009, by rfl⟩ : syracuseStep 170679 = 256019) B256019
theorem B170699 : Blo 167798 170699 := bstep (se 1 (by rfl) ⟨128024, by rfl⟩ : syracuseStep 170699 = 256049) B256049
theorem B170711 : Blo 167798 170711 := bstep (se 1 (by rfl) ⟨128033, by rfl⟩ : syracuseStep 170711 = 256067) B256067
theorem B170731 : Blo 167798 170731 := bstep (se 1 (by rfl) ⟨128048, by rfl⟩ : syracuseStep 170731 = 256097) B256097
theorem B170743 : Blo 167798 170743 := bstep (se 1 (by rfl) ⟨128057, by rfl⟩ : syracuseStep 170743 = 256115) B256115
theorem B170763 : Blo 167798 170763 := bstep (se 1 (by rfl) ⟨128072, by rfl⟩ : syracuseStep 170763 = 256145) B256145
theorem B170775 : Blo 167798 170775 := bstep (se 1 (by rfl) ⟨128081, by rfl⟩ : syracuseStep 170775 = 256163) B256163
theorem B170795 : Blo 167798 170795 := bstep (se 1 (by rfl) ⟨128096, by rfl⟩ : syracuseStep 170795 = 256193) B256193
theorem B5315381 : Blo 167798 5315381 := bstep (se 5 (by rfl) ⟨249158, by rfl⟩ : syracuseStep 5315381 = 498317) B498317
theorem B170807 : Blo 167798 170807 := bstep (se 1 (by rfl) ⟨128105, by rfl⟩ : syracuseStep 170807 = 256211) B256211
theorem B170827 : Blo 167798 170827 := bstep (se 1 (by rfl) ⟨128120, by rfl⟩ : syracuseStep 170827 = 256241) B256241
theorem B170839 : Blo 167798 170839 := bstep (se 1 (by rfl) ⟨128129, by rfl⟩ : syracuseStep 170839 = 256259) B256259
theorem B432985 : Blo 167798 432985 := bstep (se 2 (by rfl) ⟨162369, by rfl⟩ : syracuseStep 432985 = 324739) B324739
theorem B170859 : Blo 167798 170859 := bstep (se 1 (by rfl) ⟨128144, by rfl⟩ : syracuseStep 170859 = 256289) B256289
theorem B170871 : Blo 167798 170871 := bstep (se 1 (by rfl) ⟨128153, by rfl⟩ : syracuseStep 170871 = 256307) B256307
theorem B170891 : Blo 167798 170891 := bstep (se 1 (by rfl) ⟨128168, by rfl⟩ : syracuseStep 170891 = 256337) B256337
theorem B170903 : Blo 167798 170903 := bstep (se 1 (by rfl) ⟨128177, by rfl⟩ : syracuseStep 170903 = 256355) B256355
theorem B990103 : Blo 167798 990103 := bstep (se 1 (by rfl) ⟨742577, by rfl⟩ : syracuseStep 990103 = 1485155) B1485155
theorem B170923 : Blo 167798 170923 := bstep (se 1 (by rfl) ⟨128192, by rfl⟩ : syracuseStep 170923 = 256385) B256385
theorem B170935 : Blo 167798 170935 := bstep (se 1 (by rfl) ⟨128201, by rfl⟩ : syracuseStep 170935 = 256403) B256403
theorem B170955 : Blo 167798 170955 := bstep (se 1 (by rfl) ⟨128216, by rfl⟩ : syracuseStep 170955 = 256433) B256433
theorem B170967 : Blo 167798 170967 := bstep (se 1 (by rfl) ⟨128225, by rfl⟩ : syracuseStep 170967 = 256451) B256451
theorem B170987 : Blo 167798 170987 := bstep (se 1 (by rfl) ⟨128240, by rfl⟩ : syracuseStep 170987 = 256481) B256481
theorem B170999 : Blo 167798 170999 := bstep (se 1 (by rfl) ⟨128249, by rfl⟩ : syracuseStep 170999 = 256499) B256499
theorem B171019 : Blo 167798 171019 := bstep (se 1 (by rfl) ⟨128264, by rfl⟩ : syracuseStep 171019 = 256529) B256529
theorem B269335 : Blo 167798 269335 := bstep (se 1 (by rfl) ⟨202001, by rfl⟩ : syracuseStep 269335 = 404003) B404003
theorem B171031 : Blo 167798 171031 := bstep (se 1 (by rfl) ⟨128273, by rfl⟩ : syracuseStep 171031 = 256547) B256547
theorem B171051 : Blo 167798 171051 := bstep (se 1 (by rfl) ⟨128288, by rfl⟩ : syracuseStep 171051 = 256577) B256577
theorem B171063 : Blo 167798 171063 := bstep (se 1 (by rfl) ⟨128297, by rfl⟩ : syracuseStep 171063 = 256595) B256595
theorem B2333771 : Blo 167798 2333771 := bstep (se 1 (by rfl) ⟨1750328, by rfl⟩ : syracuseStep 2333771 = 3500657) B3500657
theorem B2628683 : Blo 167798 2628683 := bstep (se 1 (by rfl) ⟨1971512, by rfl⟩ : syracuseStep 2628683 = 3943025) B3943025
theorem B171083 : Blo 167798 171083 := bstep (se 1 (by rfl) ⟨128312, by rfl⟩ : syracuseStep 171083 = 256625) B256625
theorem B171095 : Blo 167798 171095 := bstep (se 1 (by rfl) ⟨128321, by rfl⟩ : syracuseStep 171095 = 256643) B256643
theorem B957541 : Blo 167798 957541 := bstep (se 4 (by rfl) ⟨89769, by rfl⟩ : syracuseStep 957541 = 179539) B179539
theorem B171115 : Blo 167798 171115 := bstep (se 1 (by rfl) ⟨128336, by rfl⟩ : syracuseStep 171115 = 256673) B256673
theorem B171127 : Blo 167798 171127 := bstep (se 1 (by rfl) ⟨128345, by rfl⟩ : syracuseStep 171127 = 256691) B256691
theorem B171147 : Blo 167798 171147 := bstep (se 1 (by rfl) ⟨128360, by rfl⟩ : syracuseStep 171147 = 256721) B256721
theorem B695441 : Blo 167798 695441 := bstep (se 2 (by rfl) ⟨260790, by rfl⟩ : syracuseStep 695441 = 521581) B521581
theorem B171159 : Blo 167798 171159 := bstep (se 1 (by rfl) ⟨128369, by rfl⟩ : syracuseStep 171159 = 256739) B256739
theorem B171179 : Blo 167798 171179 := bstep (se 1 (by rfl) ⟨128384, by rfl⟩ : syracuseStep 171179 = 256769) B256769
theorem B171191 : Blo 167798 171191 := bstep (se 1 (by rfl) ⟨128393, by rfl⟩ : syracuseStep 171191 = 256787) B256787
theorem B171211 : Blo 167798 171211 := bstep (se 1 (by rfl) ⟨128408, by rfl⟩ : syracuseStep 171211 = 256817) B256817
theorem B171223 : Blo 167798 171223 := bstep (se 1 (by rfl) ⟨128417, by rfl⟩ : syracuseStep 171223 = 256835) B256835
theorem B171243 : Blo 167798 171243 := bstep (se 1 (by rfl) ⟨128432, by rfl⟩ : syracuseStep 171243 = 256865) B256865
theorem B171255 : Blo 167798 171255 := bstep (se 1 (by rfl) ⟨128441, by rfl⟩ : syracuseStep 171255 = 256883) B256883
theorem B171275 : Blo 167798 171275 := bstep (se 1 (by rfl) ⟨128456, by rfl⟩ : syracuseStep 171275 = 256913) B256913
theorem B859409 : Blo 167798 859409 := bstep (se 2 (by rfl) ⟨322278, by rfl⟩ : syracuseStep 859409 = 644557) B644557
theorem B171287 : Blo 167798 171287 := bstep (se 1 (by rfl) ⟨128465, by rfl⟩ : syracuseStep 171287 = 256931) B256931
theorem B171307 : Blo 167798 171307 := bstep (se 1 (by rfl) ⟨128480, by rfl⟩ : syracuseStep 171307 = 256961) B256961
theorem B171319 : Blo 167798 171319 := bstep (se 1 (by rfl) ⟨128489, by rfl⟩ : syracuseStep 171319 = 256979) B256979
theorem B171339 : Blo 167798 171339 := bstep (se 1 (by rfl) ⟨128504, by rfl⟩ : syracuseStep 171339 = 257009) B257009
theorem B171351 : Blo 167798 171351 := bstep (se 1 (by rfl) ⟨128513, by rfl⟩ : syracuseStep 171351 = 257027) B257027
theorem B1285469 : Blo 167798 1285469 := bstep (se 3 (by rfl) ⟨241025, by rfl⟩ : syracuseStep 1285469 = 482051) B482051
theorem B171371 : Blo 167798 171371 := bstep (se 1 (by rfl) ⟨128528, by rfl⟩ : syracuseStep 171371 = 257057) B257057
theorem B171383 : Blo 167798 171383 := bstep (se 1 (by rfl) ⟨128537, by rfl⟩ : syracuseStep 171383 = 257075) B257075
theorem B171403 : Blo 167798 171403 := bstep (se 1 (by rfl) ⟨128552, by rfl⟩ : syracuseStep 171403 = 257105) B257105
theorem B171415 : Blo 167798 171415 := bstep (se 1 (by rfl) ⟨128561, by rfl⟩ : syracuseStep 171415 = 257123) B257123
theorem B171435 : Blo 167798 171435 := bstep (se 1 (by rfl) ⟨128576, by rfl⟩ : syracuseStep 171435 = 257153) B257153
theorem B859571 : Blo 167798 859571 := bstep (se 1 (by rfl) ⟨644678, by rfl⟩ : syracuseStep 859571 = 1289357) B1289357
theorem B171447 : Blo 167798 171447 := bstep (se 1 (by rfl) ⟨128585, by rfl⟩ : syracuseStep 171447 = 257171) B257171
theorem B171467 : Blo 167798 171467 := bstep (se 1 (by rfl) ⟨128600, by rfl⟩ : syracuseStep 171467 = 257201) B257201
theorem B171479 : Blo 167798 171479 := bstep (se 1 (by rfl) ⟨128609, by rfl⟩ : syracuseStep 171479 = 257219) B257219
theorem B171499 : Blo 167798 171499 := bstep (se 1 (by rfl) ⟨128624, by rfl⟩ : syracuseStep 171499 = 257249) B257249
theorem B171511 : Blo 167798 171511 := bstep (se 1 (by rfl) ⟨128633, by rfl⟩ : syracuseStep 171511 = 257267) B257267
theorem B171531 : Blo 167798 171531 := bstep (se 1 (by rfl) ⟨128648, by rfl⟩ : syracuseStep 171531 = 257297) B257297
theorem B171543 : Blo 167798 171543 := bstep (se 1 (by rfl) ⟨128657, by rfl⟩ : syracuseStep 171543 = 257315) B257315
theorem B171563 : Blo 167798 171563 := bstep (se 1 (by rfl) ⟨128672, by rfl⟩ : syracuseStep 171563 = 257345) B257345
theorem B171575 : Blo 167798 171575 := bstep (se 1 (by rfl) ⟨128681, by rfl⟩ : syracuseStep 171575 = 257363) B257363
theorem B171595 : Blo 167798 171595 := bstep (se 1 (by rfl) ⟨128696, by rfl⟩ : syracuseStep 171595 = 257393) B257393
theorem B171607 : Blo 167798 171607 := bstep (se 1 (by rfl) ⟨128705, by rfl⟩ : syracuseStep 171607 = 257411) B257411
theorem B171627 : Blo 167798 171627 := bstep (se 1 (by rfl) ⟨128720, by rfl⟩ : syracuseStep 171627 = 257441) B257441
theorem B171639 : Blo 167798 171639 := bstep (se 1 (by rfl) ⟨128729, by rfl⟩ : syracuseStep 171639 = 257459) B257459
theorem B171659 : Blo 167798 171659 := bstep (se 1 (by rfl) ⟨128744, by rfl⟩ : syracuseStep 171659 = 257489) B257489
theorem B171671 : Blo 167798 171671 := bstep (se 1 (by rfl) ⟨128753, by rfl⟩ : syracuseStep 171671 = 257507) B257507
theorem B171691 : Blo 167798 171691 := bstep (se 1 (by rfl) ⟨128768, by rfl⟩ : syracuseStep 171691 = 257537) B257537
theorem B171703 : Blo 167798 171703 := bstep (se 1 (by rfl) ⟨128777, by rfl⟩ : syracuseStep 171703 = 257555) B257555
theorem B171723 : Blo 167798 171723 := bstep (se 1 (by rfl) ⟨128792, by rfl⟩ : syracuseStep 171723 = 257585) B257585
theorem B171735 : Blo 167798 171735 := bstep (se 1 (by rfl) ⟨128801, by rfl⟩ : syracuseStep 171735 = 257603) B257603
theorem B171755 : Blo 167798 171755 := bstep (se 1 (by rfl) ⟨128816, by rfl⟩ : syracuseStep 171755 = 257633) B257633
theorem B171767 : Blo 167798 171767 := bstep (se 1 (by rfl) ⟨128825, by rfl⟩ : syracuseStep 171767 = 257651) B257651
theorem B270091 : Blo 167798 270091 := bstep (se 1 (by rfl) ⟨202568, by rfl⟩ : syracuseStep 270091 = 405137) B405137
theorem B171787 : Blo 167798 171787 := bstep (se 1 (by rfl) ⟨128840, by rfl⟩ : syracuseStep 171787 = 257681) B257681
theorem B270155 : Blo 167798 270155 := bstep (se 1 (by rfl) ⟨202616, by rfl⟩ : syracuseStep 270155 = 405233) B405233
theorem B1220483 : Blo 167798 1220483 := bstep (se 1 (by rfl) ⟨915362, by rfl⟩ : syracuseStep 1220483 = 1830725) B1830725
theorem B434099 : Blo 167798 434099 := bstep (se 1 (by rfl) ⟨325574, by rfl⟩ : syracuseStep 434099 = 651149) B651149
theorem B270283 : Blo 167798 270283 := bstep (se 1 (by rfl) ⟨202712, by rfl⟩ : syracuseStep 270283 = 405425) B405425
theorem B729091 : Blo 167798 729091 := bstep (se 1 (by rfl) ⟨546818, by rfl⟩ : syracuseStep 729091 = 1093637) B1093637
theorem B434393 : Blo 167798 434393 := bstep (se 2 (by rfl) ⟨162897, by rfl⟩ : syracuseStep 434393 = 325795) B325795
theorem B205259 : Blo 167798 205259 := bstep (se 1 (by rfl) ⟨153944, by rfl⟩ : syracuseStep 205259 = 307889) B307889
theorem B271001 : Blo 167798 271001 := bstep (se 2 (by rfl) ⟨101625, by rfl⟩ : syracuseStep 271001 = 203251) B203251
theorem B303895 : Blo 167798 303895 := bstep (se 1 (by rfl) ⟨227921, by rfl⟩ : syracuseStep 303895 = 455843) B455843
theorem B271129 : Blo 167798 271129 := bstep (se 2 (by rfl) ⟨101673, by rfl⟩ : syracuseStep 271129 = 203347) B203347
theorem B205783 : Blo 167798 205783 := bstep (se 1 (by rfl) ⟨154337, by rfl⟩ : syracuseStep 205783 = 308675) B308675
theorem B369625 : Blo 167798 369625 := bstep (se 2 (by rfl) ⟨138609, by rfl⟩ : syracuseStep 369625 = 277219) B277219
theorem B271513 : Blo 167798 271513 := bstep (se 2 (by rfl) ⟨101817, by rfl⟩ : syracuseStep 271513 = 203635) B203635
theorem B861515 : Blo 167798 861515 := bstep (se 1 (by rfl) ⟨646136, by rfl⟩ : syracuseStep 861515 = 1292273) B1292273
theorem B566621 : Blo 167798 566621 := bstep (se 3 (by rfl) ⟨106241, by rfl⟩ : syracuseStep 566621 = 212483) B212483
theorem B238987 : Blo 167798 238987 := bstep (se 1 (by rfl) ⟨179240, by rfl⟩ : syracuseStep 238987 = 358481) B358481
theorem B271769 : Blo 167798 271769 := bstep (se 2 (by rfl) ⟨101913, by rfl⟩ : syracuseStep 271769 = 203827) B203827
theorem B1451621 : Blo 167798 1451621 := bstep (se 4 (by rfl) ⟨136089, by rfl⟩ : syracuseStep 1451621 = 272179) B272179
theorem B730903 : Blo 167798 730903 := bstep (se 1 (by rfl) ⟨548177, by rfl⟩ : syracuseStep 730903 = 1096355) B1096355
theorem B1943513 : Blo 167798 1943513 := bstep (se 2 (by rfl) ⟨728817, by rfl⟩ : syracuseStep 1943513 = 1457635) B1457635
theorem B469081 : Blo 167798 469081 := bstep (se 2 (by rfl) ⟨175905, by rfl⟩ : syracuseStep 469081 = 351811) B351811
theorem B1976413 : Blo 167798 1976413 := bstep (se 3 (by rfl) ⟨370577, by rfl⟩ : syracuseStep 1976413 = 741155) B741155
theorem B764183 : Blo 167798 764183 := bstep (se 1 (by rfl) ⟨573137, by rfl⟩ : syracuseStep 764183 = 1146275) B1146275
theorem B731537 : Blo 167798 731537 := bstep (se 2 (by rfl) ⟨274326, by rfl⟩ : syracuseStep 731537 = 548653) B548653
theorem B567755 : Blo 167798 567755 := bstep (se 1 (by rfl) ⟨425816, by rfl⟩ : syracuseStep 567755 = 851633) B851633
theorem B404185 : Blo 167798 404185 := bstep (se 2 (by rfl) ⟨151569, by rfl⟩ : syracuseStep 404185 = 303139) B303139
theorem B568025 : Blo 167798 568025 := bstep (se 2 (by rfl) ⟨213009, by rfl⟩ : syracuseStep 568025 = 426019) B426019
theorem B1321859 : Blo 167798 1321859 := bstep (se 1 (by rfl) ⟨991394, by rfl⟩ : syracuseStep 1321859 = 1982789) B1982789
theorem B863297 : Blo 167798 863297 := bstep (se 2 (by rfl) ⟨323736, by rfl⟩ : syracuseStep 863297 = 647473) B647473
theorem B732235 : Blo 167798 732235 := bstep (se 1 (by rfl) ⟨549176, by rfl⟩ : syracuseStep 732235 = 1098353) B1098353
theorem B1453261 : Blo 167798 1453261 := bstep (se 3 (by rfl) ⟨272486, by rfl⟩ : syracuseStep 1453261 = 544973) B544973
theorem B306433 : Blo 167798 306433 := bstep (se 2 (by rfl) ⟨114912, by rfl⟩ : syracuseStep 306433 = 229825) B229825
theorem B404801 : Blo 167798 404801 := bstep (se 2 (by rfl) ⟨151800, by rfl⟩ : syracuseStep 404801 = 303601) B303601
theorem B1027403 : Blo 167798 1027403 := bstep (se 1 (by rfl) ⟨770552, by rfl⟩ : syracuseStep 1027403 = 1541105) B1541105
theorem B732509 : Blo 167798 732509 := bstep (se 3 (by rfl) ⟨137345, by rfl⟩ : syracuseStep 732509 = 274691) B274691
theorem B568727 : Blo 167798 568727 := bstep (se 1 (by rfl) ⟨426545, by rfl⟩ : syracuseStep 568727 = 853091) B853091
theorem B208279 : Blo 167798 208279 := bstep (se 1 (by rfl) ⟨156209, by rfl⟩ : syracuseStep 208279 = 312419) B312419
theorem B732851 : Blo 167798 732851 := bstep (se 1 (by rfl) ⟨549638, by rfl⟩ : syracuseStep 732851 = 1099277) B1099277
theorem B569267 : Blo 167798 569267 := bstep (se 1 (by rfl) ⟨426950, by rfl⟩ : syracuseStep 569267 = 853901) B853901
theorem B307211 : Blo 167798 307211 := bstep (se 1 (by rfl) ⟨230408, by rfl⟩ : syracuseStep 307211 = 460817) B460817
theorem B1028227 : Blo 167798 1028227 := bstep (se 1 (by rfl) ⟨771170, by rfl⟩ : syracuseStep 1028227 = 1542341) B1542341
theorem B274583 : Blo 167798 274583 := bstep (se 1 (by rfl) ⟨205937, by rfl⟩ : syracuseStep 274583 = 411875) B411875
theorem B569537 : Blo 167798 569537 := bstep (se 2 (by rfl) ⟨213576, by rfl⟩ : syracuseStep 569537 = 427153) B427153
theorem B1454597 : Blo 167798 1454597 := bstep (se 4 (by rfl) ⟨136368, by rfl⟩ : syracuseStep 1454597 = 272737) B272737
theorem B275147 : Blo 167798 275147 := bstep (se 1 (by rfl) ⟨206360, by rfl⟩ : syracuseStep 275147 = 412721) B412721
theorem B570077 : Blo 167798 570077 := bstep (se 3 (by rfl) ⟨106889, by rfl⟩ : syracuseStep 570077 = 213779) B213779
theorem B963373 : Blo 167798 963373 := bstep (se 3 (by rfl) ⟨180632, by rfl⟩ : syracuseStep 963373 = 361265) B361265
theorem B865241 : Blo 167798 865241 := bstep (se 2 (by rfl) ⟨324465, by rfl⟩ : syracuseStep 865241 = 648931) B648931
theorem B243481 : Blo 167798 243481 := bstep (se 2 (by rfl) ⟨91305, by rfl⟩ : syracuseStep 243481 = 182611) B182611
theorem B571211 : Blo 167798 571211 := bstep (se 1 (by rfl) ⟨428408, by rfl⟩ : syracuseStep 571211 = 856817) B856817
theorem B309143 : Blo 167798 309143 := bstep (se 1 (by rfl) ⟨231857, by rfl⟩ : syracuseStep 309143 = 463715) B463715
theorem B571481 : Blo 167798 571481 := bstep (se 2 (by rfl) ⟨214305, by rfl⟩ : syracuseStep 571481 = 428611) B428611
theorem B342401 : Blo 167798 342401 := bstep (se 2 (by rfl) ⟨128400, by rfl⟩ : syracuseStep 342401 = 256801) B256801
theorem B866861 : Blo 167798 866861 := bstep (se 3 (by rfl) ⟨162536, by rfl⟩ : syracuseStep 866861 = 325073) B325073
theorem B408115 : Blo 167798 408115 := bstep (se 1 (by rfl) ⟨306086, by rfl⟩ : syracuseStep 408115 = 612173) B612173
theorem B932417 : Blo 167798 932417 := bstep (se 2 (by rfl) ⟨349656, by rfl⟩ : syracuseStep 932417 = 699313) B699313
theorem B637571 : Blo 167798 637571 := bstep (se 1 (by rfl) ⟨478178, by rfl⟩ : syracuseStep 637571 = 956357) B956357
theorem B572183 : Blo 167798 572183 := bstep (se 1 (by rfl) ⟨429137, by rfl⟩ : syracuseStep 572183 = 858275) B858275
theorem B638027 : Blo 167798 638027 := bstep (se 1 (by rfl) ⟨478520, by rfl⟩ : syracuseStep 638027 = 957041) B957041
theorem B638225 : Blo 167798 638225 := bstep (se 2 (by rfl) ⟨239334, by rfl⟩ : syracuseStep 638225 = 478669) B478669
theorem B572723 : Blo 167798 572723 := bstep (se 1 (by rfl) ⟨429542, by rfl⟩ : syracuseStep 572723 = 859085) B859085
theorem B605515 : Blo 167798 605515 := bstep (se 1 (by rfl) ⟨454136, by rfl⟩ : syracuseStep 605515 = 908273) B908273
theorem B736685 : Blo 167798 736685 := bstep (se 3 (by rfl) ⟨138128, by rfl⟩ : syracuseStep 736685 = 276257) B276257
theorem B179659 : Blo 167798 179659 := bstep (se 1 (by rfl) ⟨134744, by rfl⟩ : syracuseStep 179659 = 269489) B269489
theorem B605657 : Blo 167798 605657 := bstep (se 2 (by rfl) ⟨227121, by rfl⟩ : syracuseStep 605657 = 454243) B454243
theorem B572993 : Blo 167798 572993 := bstep (se 2 (by rfl) ⟨214872, by rfl⟩ : syracuseStep 572993 = 429745) B429745
theorem B3259997 : Blo 167798 3259997 := bstep (se 3 (by rfl) ⟨611249, by rfl⟩ : syracuseStep 3259997 = 1222499) B1222499
theorem B343667 : Blo 167798 343667 := bstep (se 1 (by rfl) ⟨257750, by rfl⟩ : syracuseStep 343667 = 515501) B515501
theorem B179915 : Blo 167798 179915 := bstep (se 1 (by rfl) ⟨134936, by rfl⟩ : syracuseStep 179915 = 269873) B269873
theorem B638999 : Blo 167798 638999 := bstep (se 1 (by rfl) ⟨479249, by rfl⟩ : syracuseStep 638999 = 958499) B958499
theorem B540695 : Blo 167798 540695 := bstep (se 1 (by rfl) ⟨405521, by rfl⟩ : syracuseStep 540695 = 811043) B811043
theorem B573533 : Blo 167798 573533 := bstep (se 3 (by rfl) ⟨107537, by rfl⟩ : syracuseStep 573533 = 215075) B215075
theorem B213131 : Blo 167798 213131 := bstep (se 1 (by rfl) ⟨159848, by rfl⟩ : syracuseStep 213131 = 319697) B319697
theorem B639197 : Blo 167798 639197 := bstep (se 3 (by rfl) ⟨119849, by rfl⟩ : syracuseStep 639197 = 239699) B239699
theorem B344665 : Blo 167798 344665 := bstep (se 2 (by rfl) ⟨129249, by rfl⟩ : syracuseStep 344665 = 258499) B258499
theorem B344819 : Blo 167798 344819 := bstep (se 1 (by rfl) ⟨258614, by rfl⟩ : syracuseStep 344819 = 517229) B517229
theorem B377675 : Blo 167798 377675 := bstep (se 1 (by rfl) ⟨283256, by rfl⟩ : syracuseStep 377675 = 566513) B566513
theorem B213835 : Blo 167798 213835 := bstep (se 1 (by rfl) ⟨160376, by rfl⟩ : syracuseStep 213835 = 320753) B320753
theorem B377729 : Blo 167798 377729 := bstep (se 2 (by rfl) ⟨141648, by rfl⟩ : syracuseStep 377729 = 283297) B283297
theorem B1557521 : Blo 167798 1557521 := bstep (se 2 (by rfl) ⟨584070, by rfl⟩ : syracuseStep 1557521 = 1168141) B1168141
theorem B214103 : Blo 167798 214103 := bstep (se 1 (by rfl) ⟨160577, by rfl⟩ : syracuseStep 214103 = 321155) B321155
theorem B377945 : Blo 167798 377945 := bstep (se 2 (by rfl) ⟨141729, by rfl⟩ : syracuseStep 377945 = 283459) B283459
theorem B378035 : Blo 167798 378035 := bstep (se 1 (by rfl) ⟨283526, by rfl⟩ : syracuseStep 378035 = 567053) B567053
theorem B574667 : Blo 167798 574667 := bstep (se 1 (by rfl) ⟨431000, by rfl⟩ : syracuseStep 574667 = 862001) B862001
theorem B378071 : Blo 167798 378071 := bstep (se 1 (by rfl) ⟨283553, by rfl⟩ : syracuseStep 378071 = 567107) B567107
theorem B542027 : Blo 167798 542027 := bstep (se 1 (by rfl) ⟨406520, by rfl⟩ : syracuseStep 542027 = 813041) B813041
theorem B1230173 : Blo 167798 1230173 := bstep (se 3 (by rfl) ⟨230657, by rfl⟩ : syracuseStep 1230173 = 461315) B461315
theorem B378251 : Blo 167798 378251 := bstep (se 1 (by rfl) ⟨283688, by rfl⟩ : syracuseStep 378251 = 567377) B567377
theorem B378305 : Blo 167798 378305 := bstep (se 2 (by rfl) ⟨141864, by rfl⟩ : syracuseStep 378305 = 283729) B283729
theorem B574937 : Blo 167798 574937 := bstep (se 2 (by rfl) ⟨215601, by rfl⟩ : syracuseStep 574937 = 431203) B431203
theorem B935441 : Blo 167798 935441 := bstep (se 2 (by rfl) ⟨350790, by rfl⟩ : syracuseStep 935441 = 701581) B701581
theorem B378521 : Blo 167798 378521 := bstep (se 2 (by rfl) ⟨141945, by rfl⟩ : syracuseStep 378521 = 283891) B283891
theorem B181931 : Blo 167798 181931 := bstep (se 1 (by rfl) ⟨136448, by rfl⟩ : syracuseStep 181931 = 272897) B272897
theorem B378611 : Blo 167798 378611 := bstep (se 1 (by rfl) ⟨283958, by rfl⟩ : syracuseStep 378611 = 567917) B567917
theorem B378647 : Blo 167798 378647 := bstep (se 1 (by rfl) ⟨283985, by rfl⟩ : syracuseStep 378647 = 567971) B567971
theorem B214807 : Blo 167798 214807 := bstep (se 1 (by rfl) ⟨161105, by rfl⟩ : syracuseStep 214807 = 322211) B322211
theorem B575383 : Blo 167798 575383 := bstep (se 1 (by rfl) ⟨431537, by rfl⟩ : syracuseStep 575383 = 863075) B863075
theorem B378827 : Blo 167798 378827 := bstep (se 1 (by rfl) ⟨284120, by rfl⟩ : syracuseStep 378827 = 568241) B568241
theorem B378881 : Blo 167798 378881 := bstep (se 2 (by rfl) ⟨142080, by rfl⟩ : syracuseStep 378881 = 284161) B284161
theorem B542771 : Blo 167798 542771 := bstep (se 1 (by rfl) ⟨407078, by rfl⟩ : syracuseStep 542771 = 814157) B814157
theorem B1624157 : Blo 167798 1624157 := bstep (se 3 (by rfl) ⟨304529, by rfl⟩ : syracuseStep 1624157 = 609059) B609059
theorem B641155 : Blo 167798 641155 := bstep (se 1 (by rfl) ⟨480866, by rfl⟩ : syracuseStep 641155 = 961733) B961733
theorem B739459 : Blo 167798 739459 := bstep (se 1 (by rfl) ⟨554594, by rfl⟩ : syracuseStep 739459 = 1109189) B1109189
theorem B575639 : Blo 167798 575639 := bstep (se 1 (by rfl) ⟨431729, by rfl⟩ : syracuseStep 575639 = 863459) B863459
theorem B379097 : Blo 167798 379097 := bstep (se 2 (by rfl) ⟨142161, by rfl⟩ : syracuseStep 379097 = 284323) B284323
theorem B1099993 : Blo 167798 1099993 := bstep (se 2 (by rfl) ⟨412497, by rfl⟩ : syracuseStep 1099993 = 824995) B824995
theorem B739601 : Blo 167798 739601 := bstep (se 2 (by rfl) ⟨277350, by rfl⟩ : syracuseStep 739601 = 554701) B554701
theorem B379187 : Blo 167798 379187 := bstep (se 1 (by rfl) ⟨284390, by rfl⟩ : syracuseStep 379187 = 568781) B568781
theorem B379223 : Blo 167798 379223 := bstep (se 1 (by rfl) ⟨284417, by rfl⟩ : syracuseStep 379223 = 568835) B568835
theorem B641459 : Blo 167798 641459 := bstep (se 1 (by rfl) ⟨481094, by rfl⟩ : syracuseStep 641459 = 962189) B962189
theorem B1100249 : Blo 167798 1100249 := bstep (se 2 (by rfl) ⟨412593, by rfl⟩ : syracuseStep 1100249 = 825187) B825187
theorem B379403 : Blo 167798 379403 := bstep (se 1 (by rfl) ⟨284552, by rfl⟩ : syracuseStep 379403 = 569105) B569105
theorem B9423373 : Blo 167798 9423373 := bstep (se 3 (by rfl) ⟨1766882, by rfl⟩ : syracuseStep 9423373 = 3533765) B3533765
theorem B379457 : Blo 167798 379457 := bstep (se 2 (by rfl) ⟨142296, by rfl⟩ : syracuseStep 379457 = 284593) B284593
theorem B576179 : Blo 167798 576179 := bstep (se 1 (by rfl) ⟨432134, by rfl⟩ : syracuseStep 576179 = 864269) B864269
theorem B379673 : Blo 167798 379673 := bstep (se 2 (by rfl) ⟨142377, by rfl⟩ : syracuseStep 379673 = 284755) B284755
theorem B379763 : Blo 167798 379763 := bstep (se 1 (by rfl) ⟨284822, by rfl⟩ : syracuseStep 379763 = 569645) B569645
theorem B379799 : Blo 167798 379799 := bstep (se 1 (by rfl) ⟨284849, by rfl⟩ : syracuseStep 379799 = 569699) B569699
theorem B543667 : Blo 167798 543667 := bstep (se 1 (by rfl) ⟨407750, by rfl⟩ : syracuseStep 543667 = 815501) B815501
theorem B576449 : Blo 167798 576449 := bstep (se 2 (by rfl) ⟨216168, by rfl⟩ : syracuseStep 576449 = 432337) B432337
theorem B1035281 : Blo 167798 1035281 := bstep (se 2 (by rfl) ⟨388230, by rfl⟩ : syracuseStep 1035281 = 776461) B776461
theorem B642113 : Blo 167798 642113 := bstep (se 2 (by rfl) ⟨240792, by rfl⟩ : syracuseStep 642113 = 481585) B481585
theorem B379979 : Blo 167798 379979 := bstep (se 1 (by rfl) ⟨284984, by rfl⟩ : syracuseStep 379979 = 569969) B569969
theorem B380033 : Blo 167798 380033 := bstep (se 2 (by rfl) ⟨142512, by rfl⟩ : syracuseStep 380033 = 285025) B285025
theorem B1133747 : Blo 167798 1133747 := bstep (se 1 (by rfl) ⟨850310, by rfl⟩ : syracuseStep 1133747 = 1700621) B1700621
theorem B478487 : Blo 167798 478487 := bstep (se 1 (by rfl) ⟨358865, by rfl⟩ : syracuseStep 478487 = 717731) B717731
theorem B380249 : Blo 167798 380249 := bstep (se 2 (by rfl) ⟨142593, by rfl⟩ : syracuseStep 380249 = 285187) B285187
theorem B380339 : Blo 167798 380339 := bstep (se 1 (by rfl) ⟨285254, by rfl⟩ : syracuseStep 380339 = 570509) B570509
theorem B970163 : Blo 167798 970163 := bstep (se 1 (by rfl) ⟨727622, by rfl⟩ : syracuseStep 970163 = 1455245) B1455245
theorem B216523 : Blo 167798 216523 := bstep (se 1 (by rfl) ⟨162392, by rfl⟩ : syracuseStep 216523 = 324785) B324785
theorem B380375 : Blo 167798 380375 := bstep (se 1 (by rfl) ⟨285281, by rfl⟩ : syracuseStep 380375 = 570563) B570563
theorem B576989 : Blo 167798 576989 := bstep (se 3 (by rfl) ⟨108185, by rfl⟩ : syracuseStep 576989 = 216371) B216371
theorem B3919373 : Blo 167798 3919373 := bstep (se 3 (by rfl) ⟨734882, by rfl⟩ : syracuseStep 3919373 = 1469765) B1469765
theorem B380555 : Blo 167798 380555 := bstep (se 1 (by rfl) ⟨285416, by rfl⟩ : syracuseStep 380555 = 570833) B570833
theorem B380609 : Blo 167798 380609 := bstep (se 2 (by rfl) ⟨142728, by rfl⟩ : syracuseStep 380609 = 285457) B285457
theorem B380825 : Blo 167798 380825 := bstep (se 2 (by rfl) ⟨142809, by rfl⟩ : syracuseStep 380825 = 285619) B285619
theorem B380915 : Blo 167798 380915 := bstep (se 1 (by rfl) ⟨285686, by rfl⟩ : syracuseStep 380915 = 571373) B571373
theorem B380951 : Blo 167798 380951 := bstep (se 1 (by rfl) ⟨285713, by rfl⟩ : syracuseStep 380951 = 571427) B571427
theorem B381131 : Blo 167798 381131 := bstep (se 1 (by rfl) ⟨285848, by rfl⟩ : syracuseStep 381131 = 571697) B571697
theorem B381185 : Blo 167798 381185 := bstep (se 2 (by rfl) ⟨142944, by rfl⟩ : syracuseStep 381185 = 285889) B285889
theorem B643373 : Blo 167798 643373 := bstep (se 3 (by rfl) ⟨120632, by rfl⟩ : syracuseStep 643373 = 241265) B241265
theorem B643403 : Blo 167798 643403 := bstep (se 1 (by rfl) ⟨482552, by rfl⟩ : syracuseStep 643403 = 965105) B965105
theorem B381401 : Blo 167798 381401 := bstep (se 2 (by rfl) ⟨143025, by rfl⟩ : syracuseStep 381401 = 286051) B286051
theorem B381491 : Blo 167798 381491 := bstep (se 1 (by rfl) ⟨286118, by rfl⟩ : syracuseStep 381491 = 572237) B572237
theorem B479819 : Blo 167798 479819 := bstep (se 1 (by rfl) ⟨359864, by rfl⟩ : syracuseStep 479819 = 719729) B719729
theorem B578123 : Blo 167798 578123 := bstep (se 1 (by rfl) ⟨433592, by rfl⟩ : syracuseStep 578123 = 867185) B867185
theorem B283223 : Blo 167798 283223 := bstep (se 1 (by rfl) ⟨212417, by rfl⟩ : syracuseStep 283223 = 424835) B424835
theorem B381527 : Blo 167798 381527 := bstep (se 1 (by rfl) ⟨286145, by rfl⟩ : syracuseStep 381527 = 572291) B572291
theorem B283351 : Blo 167798 283351 := bstep (se 1 (by rfl) ⟨212513, by rfl⟩ : syracuseStep 283351 = 425027) B425027
theorem B381707 : Blo 167798 381707 := bstep (se 1 (by rfl) ⟨286280, by rfl⟩ : syracuseStep 381707 = 572561) B572561
theorem B381761 : Blo 167798 381761 := bstep (se 2 (by rfl) ⟨143160, by rfl⟩ : syracuseStep 381761 = 286321) B286321
theorem B578393 : Blo 167798 578393 := bstep (se 2 (by rfl) ⟨216897, by rfl⟩ : syracuseStep 578393 = 433795) B433795
theorem B611165 : Blo 167798 611165 := bstep (se 3 (by rfl) ⟨114593, by rfl⟩ : syracuseStep 611165 = 229187) B229187
theorem B971621 : Blo 167798 971621 := bstep (se 4 (by rfl) ⟨91089, by rfl⟩ : syracuseStep 971621 = 182179) B182179
theorem B644057 : Blo 167798 644057 := bstep (se 2 (by rfl) ⟨241521, by rfl⟩ : syracuseStep 644057 = 483043) B483043
theorem B381977 : Blo 167798 381977 := bstep (se 2 (by rfl) ⟨143241, by rfl⟩ : syracuseStep 381977 = 286483) B286483
theorem B545885 : Blo 167798 545885 := bstep (se 3 (by rfl) ⟨102353, by rfl⟩ : syracuseStep 545885 = 204707) B204707
theorem B382067 : Blo 167798 382067 := bstep (se 1 (by rfl) ⟨286550, by rfl⟩ : syracuseStep 382067 = 573101) B573101
theorem B382103 : Blo 167798 382103 := bstep (se 1 (by rfl) ⟨286577, by rfl⟩ : syracuseStep 382103 = 573155) B573155
theorem B644375 : Blo 167798 644375 := bstep (se 1 (by rfl) ⟨483281, by rfl⟩ : syracuseStep 644375 = 966563) B966563
theorem B283979 : Blo 167798 283979 := bstep (se 1 (by rfl) ⟨212984, by rfl⟩ : syracuseStep 283979 = 425969) B425969
theorem B382283 : Blo 167798 382283 := bstep (se 1 (by rfl) ⟨286712, by rfl⟩ : syracuseStep 382283 = 573425) B573425
theorem B382337 : Blo 167798 382337 := bstep (se 2 (by rfl) ⟨143376, by rfl⟩ : syracuseStep 382337 = 286753) B286753
theorem B284107 : Blo 167798 284107 := bstep (se 1 (by rfl) ⟨213080, by rfl⟩ : syracuseStep 284107 = 426161) B426161
theorem B579095 : Blo 167798 579095 := bstep (se 1 (by rfl) ⟨434321, by rfl⟩ : syracuseStep 579095 = 868643) B868643
theorem B284249 : Blo 167798 284249 := bstep (se 2 (by rfl) ⟨106593, by rfl⟩ : syracuseStep 284249 = 213187) B213187
theorem B382553 : Blo 167798 382553 := bstep (se 2 (by rfl) ⟨143457, by rfl⟩ : syracuseStep 382553 = 286915) B286915
theorem B382643 : Blo 167798 382643 := bstep (se 1 (by rfl) ⟨286982, by rfl⟩ : syracuseStep 382643 = 573965) B573965
theorem B4085453 : Blo 167798 4085453 := bstep (se 3 (by rfl) ⟨766022, by rfl⟩ : syracuseStep 4085453 = 1532045) B1532045
theorem B382679 : Blo 167798 382679 := bstep (se 1 (by rfl) ⟨287009, by rfl⟩ : syracuseStep 382679 = 574019) B574019
theorem B284377 : Blo 167798 284377 := bstep (se 2 (by rfl) ⟨106641, by rfl⟩ : syracuseStep 284377 = 213283) B213283
theorem B2807557 : Blo 167798 2807557 := bstep (se 4 (by rfl) ⟨263208, by rfl⟩ : syracuseStep 2807557 = 526417) B526417
theorem B251723 : Blo 167798 251723 := bstep (se 1 (by rfl) ⟨188792, by rfl⟩ : syracuseStep 251723 = 377585) B377585
theorem B251735 : Blo 167798 251735 := bstep (se 1 (by rfl) ⟨188801, by rfl⟩ : syracuseStep 251735 = 377603) B377603
theorem B382859 : Blo 167798 382859 := bstep (se 1 (by rfl) ⟨287144, by rfl⟩ : syracuseStep 382859 = 574289) B574289
theorem B251801 : Blo 167798 251801 := bstep (se 2 (by rfl) ⟨94425, by rfl⟩ : syracuseStep 251801 = 188851) B188851
theorem B645043 : Blo 167798 645043 := bstep (se 1 (by rfl) ⟨483782, by rfl⟩ : syracuseStep 645043 = 967565) B967565
theorem B382913 : Blo 167798 382913 := bstep (se 2 (by rfl) ⟨143592, by rfl⟩ : syracuseStep 382913 = 287185) B287185
theorem B251915 : Blo 167798 251915 := bstep (se 1 (by rfl) ⟨188936, by rfl⟩ : syracuseStep 251915 = 377873) B377873
theorem B251927 : Blo 167798 251927 := bstep (se 1 (by rfl) ⟨188945, by rfl⟩ : syracuseStep 251927 = 377891) B377891
theorem B3299363 : Blo 167798 3299363 := bstep (se 1 (by rfl) ⟨2474522, by rfl⟩ : syracuseStep 3299363 = 4949045) B4949045
theorem B579635 : Blo 167798 579635 := bstep (se 1 (by rfl) ⟨434726, by rfl⟩ : syracuseStep 579635 = 869453) B869453
theorem B251993 : Blo 167798 251993 := bstep (se 2 (by rfl) ⟨94497, by rfl⟩ : syracuseStep 251993 = 188995) B188995
theorem B546905 : Blo 167798 546905 := bstep (se 2 (by rfl) ⟨205089, by rfl⟩ : syracuseStep 546905 = 410179) B410179
theorem B12572813 : Blo 167798 12572813 := bstep (se 3 (by rfl) ⟨2357402, by rfl⟩ : syracuseStep 12572813 = 4714805) B4714805
theorem B383129 : Blo 167798 383129 := bstep (se 2 (by rfl) ⟨143673, by rfl⟩ : syracuseStep 383129 = 287347) B287347
theorem B481459 : Blo 167798 481459 := bstep (se 1 (by rfl) ⟨361094, by rfl⟩ : syracuseStep 481459 = 722189) B722189
theorem B252107 : Blo 167798 252107 := bstep (se 1 (by rfl) ⟨189080, by rfl⟩ : syracuseStep 252107 = 378161) B378161
theorem B252119 : Blo 167798 252119 := bstep (se 1 (by rfl) ⟨189089, by rfl⟩ : syracuseStep 252119 = 378179) B378179
theorem B383219 : Blo 167798 383219 := bstep (se 1 (by rfl) ⟨287414, by rfl⟩ : syracuseStep 383219 = 574829) B574829
theorem B284951 : Blo 167798 284951 := bstep (se 1 (by rfl) ⟨213713, by rfl⟩ : syracuseStep 284951 = 427427) B427427
theorem B383255 : Blo 167798 383255 := bstep (se 1 (by rfl) ⟨287441, by rfl⟩ : syracuseStep 383255 = 574883) B574883
theorem B252185 : Blo 167798 252185 := bstep (se 2 (by rfl) ⟨94569, by rfl⟩ : syracuseStep 252185 = 189139) B189139
theorem B1235245 : Blo 167798 1235245 := bstep (se 3 (by rfl) ⟨231608, by rfl⟩ : syracuseStep 1235245 = 463217) B463217
theorem B2873717 : Blo 167798 2873717 := bstep (se 5 (by rfl) ⟨134705, by rfl⟩ : syracuseStep 2873717 = 269411) B269411
theorem B252299 : Blo 167798 252299 := bstep (se 1 (by rfl) ⟨189224, by rfl⟩ : syracuseStep 252299 = 378449) B378449
theorem B252311 : Blo 167798 252311 := bstep (se 1 (by rfl) ⟨189233, by rfl⟩ : syracuseStep 252311 = 378467) B378467
theorem B285079 : Blo 167798 285079 := bstep (se 1 (by rfl) ⟨213809, by rfl⟩ : syracuseStep 285079 = 427619) B427619
theorem B383435 : Blo 167798 383435 := bstep (se 1 (by rfl) ⟨287576, by rfl⟩ : syracuseStep 383435 = 575153) B575153
theorem B252377 : Blo 167798 252377 := bstep (se 2 (by rfl) ⟨94641, by rfl⟩ : syracuseStep 252377 = 189283) B189283
theorem B383489 : Blo 167798 383489 := bstep (se 2 (by rfl) ⟨143808, by rfl⟩ : syracuseStep 383489 = 287617) B287617
theorem B252491 : Blo 167798 252491 := bstep (se 1 (by rfl) ⟨189368, by rfl⟩ : syracuseStep 252491 = 378737) B378737
theorem B252503 : Blo 167798 252503 := bstep (se 1 (by rfl) ⟨189377, by rfl⟩ : syracuseStep 252503 = 378755) B378755
theorem B252569 : Blo 167798 252569 := bstep (se 2 (by rfl) ⟨94713, by rfl⟩ : syracuseStep 252569 = 189427) B189427
theorem B383705 : Blo 167798 383705 := bstep (se 2 (by rfl) ⟨143889, by rfl⟩ : syracuseStep 383705 = 287779) B287779
theorem B252683 : Blo 167798 252683 := bstep (se 1 (by rfl) ⟨189512, by rfl⟩ : syracuseStep 252683 = 379025) B379025
theorem B252695 : Blo 167798 252695 := bstep (se 1 (by rfl) ⟨189521, by rfl⟩ : syracuseStep 252695 = 379043) B379043
theorem B383795 : Blo 167798 383795 := bstep (se 1 (by rfl) ⟨287846, by rfl⟩ : syracuseStep 383795 = 575693) B575693
theorem B1170251 : Blo 167798 1170251 := bstep (se 1 (by rfl) ⟨877688, by rfl⟩ : syracuseStep 1170251 = 1755377) B1755377
theorem B383831 : Blo 167798 383831 := bstep (se 1 (by rfl) ⟨287873, by rfl⟩ : syracuseStep 383831 = 575747) B575747
theorem B252761 : Blo 167798 252761 := bstep (se 2 (by rfl) ⟨94785, by rfl⟩ : syracuseStep 252761 = 189571) B189571
theorem B252875 : Blo 167798 252875 := bstep (se 1 (by rfl) ⟨189656, by rfl⟩ : syracuseStep 252875 = 379313) B379313
theorem B252887 : Blo 167798 252887 := bstep (se 1 (by rfl) ⟨189665, by rfl⟩ : syracuseStep 252887 = 379331) B379331
theorem B285707 : Blo 167798 285707 := bstep (se 1 (by rfl) ⟨214280, by rfl⟩ : syracuseStep 285707 = 428561) B428561
theorem B384011 : Blo 167798 384011 := bstep (se 1 (by rfl) ⟨288008, by rfl⟩ : syracuseStep 384011 = 576017) B576017
theorem B252953 : Blo 167798 252953 := bstep (se 2 (by rfl) ⟨94857, by rfl⟩ : syracuseStep 252953 = 189715) B189715
theorem B384065 : Blo 167798 384065 := bstep (se 2 (by rfl) ⟨144024, by rfl⟩ : syracuseStep 384065 = 288049) B288049
theorem B253067 : Blo 167798 253067 := bstep (se 1 (by rfl) ⟨189800, by rfl⟩ : syracuseStep 253067 = 379601) B379601
theorem B285835 : Blo 167798 285835 := bstep (se 1 (by rfl) ⟨214376, by rfl⟩ : syracuseStep 285835 = 428753) B428753
theorem B646289 : Blo 167798 646289 := bstep (se 2 (by rfl) ⟨242358, by rfl⟩ : syracuseStep 646289 = 484717) B484717
theorem B253079 : Blo 167798 253079 := bstep (se 1 (by rfl) ⟨189809, by rfl⟩ : syracuseStep 253079 = 379619) B379619
theorem B482507 : Blo 167798 482507 := bstep (se 1 (by rfl) ⟨361880, by rfl⟩ : syracuseStep 482507 = 723761) B723761
theorem B253145 : Blo 167798 253145 := bstep (se 2 (by rfl) ⟨94929, by rfl⟩ : syracuseStep 253145 = 189859) B189859
theorem B285977 : Blo 167798 285977 := bstep (se 2 (by rfl) ⟨107241, by rfl⟩ : syracuseStep 285977 = 214483) B214483
theorem B384281 : Blo 167798 384281 := bstep (se 2 (by rfl) ⟨144105, by rfl⟩ : syracuseStep 384281 = 288211) B288211
theorem B1039661 : Blo 167798 1039661 := bstep (se 3 (by rfl) ⟨194936, by rfl⟩ : syracuseStep 1039661 = 389873) B389873
theorem B253259 : Blo 167798 253259 := bstep (se 1 (by rfl) ⟨189944, by rfl⟩ : syracuseStep 253259 = 379889) B379889
theorem B253271 : Blo 167798 253271 := bstep (se 1 (by rfl) ⟨189953, by rfl⟩ : syracuseStep 253271 = 379907) B379907
theorem B318809 : Blo 167798 318809 := bstep (se 2 (by rfl) ⟨119553, by rfl⟩ : syracuseStep 318809 = 239107) B239107
theorem B384371 : Blo 167798 384371 := bstep (se 1 (by rfl) ⟨288278, by rfl⟩ : syracuseStep 384371 = 576557) B576557
theorem B384407 : Blo 167798 384407 := bstep (se 1 (by rfl) ⟨288305, by rfl⟩ : syracuseStep 384407 = 576611) B576611
theorem B253337 : Blo 167798 253337 := bstep (se 2 (by rfl) ⟨95001, by rfl⟩ : syracuseStep 253337 = 190003) B190003
theorem B286105 : Blo 167798 286105 := bstep (se 2 (by rfl) ⟨107289, by rfl⟩ : syracuseStep 286105 = 214579) B214579
theorem B253451 : Blo 167798 253451 := bstep (se 1 (by rfl) ⟨190088, by rfl⟩ : syracuseStep 253451 = 380177) B380177
theorem B253463 : Blo 167798 253463 := bstep (se 1 (by rfl) ⟨190097, by rfl⟩ : syracuseStep 253463 = 380195) B380195
theorem B1236545 : Blo 167798 1236545 := bstep (se 2 (by rfl) ⟨463704, by rfl⟩ : syracuseStep 1236545 = 927409) B927409
theorem B2154059 : Blo 167798 2154059 := bstep (se 1 (by rfl) ⟨1615544, by rfl⟩ : syracuseStep 2154059 = 3231089) B3231089
theorem B384587 : Blo 167798 384587 := bstep (se 1 (by rfl) ⟨288440, by rfl⟩ : syracuseStep 384587 = 576881) B576881
theorem B253529 : Blo 167798 253529 := bstep (se 2 (by rfl) ⟨95073, by rfl⟩ : syracuseStep 253529 = 190147) B190147
theorem B384641 : Blo 167798 384641 := bstep (se 2 (by rfl) ⟨144240, by rfl⟩ : syracuseStep 384641 = 288481) B288481
theorem B253643 : Blo 167798 253643 := bstep (se 1 (by rfl) ⟨190232, by rfl⟩ : syracuseStep 253643 = 380465) B380465
theorem B253655 : Blo 167798 253655 := bstep (se 1 (by rfl) ⟨190241, by rfl⟩ : syracuseStep 253655 = 380483) B380483
theorem B253721 : Blo 167798 253721 := bstep (se 2 (by rfl) ⟨95145, by rfl⟩ : syracuseStep 253721 = 190291) B190291
theorem B1400651 : Blo 167798 1400651 := bstep (se 1 (by rfl) ⟨1050488, by rfl⟩ : syracuseStep 1400651 = 2100977) B2100977
theorem B646987 : Blo 167798 646987 := bstep (se 1 (by rfl) ⟨485240, by rfl⟩ : syracuseStep 646987 = 970481) B970481
theorem B384857 : Blo 167798 384857 := bstep (se 2 (by rfl) ⟨144321, by rfl⟩ : syracuseStep 384857 = 288643) B288643
theorem B253835 : Blo 167798 253835 := bstep (se 1 (by rfl) ⟨190376, by rfl⟩ : syracuseStep 253835 = 380753) B380753
theorem B253847 : Blo 167798 253847 := bstep (se 1 (by rfl) ⟨190385, by rfl⟩ : syracuseStep 253847 = 380771) B380771
theorem B384947 : Blo 167798 384947 := bstep (se 1 (by rfl) ⟨288710, by rfl⟩ : syracuseStep 384947 = 577421) B577421
theorem B286679 : Blo 167798 286679 := bstep (se 1 (by rfl) ⟨215009, by rfl⟩ : syracuseStep 286679 = 430019) B430019
theorem B384983 : Blo 167798 384983 := bstep (se 1 (by rfl) ⟨288737, by rfl⟩ : syracuseStep 384983 = 577475) B577475
theorem B253913 : Blo 167798 253913 := bstep (se 2 (by rfl) ⟨95217, by rfl⟩ : syracuseStep 253913 = 190435) B190435
theorem B254027 : Blo 167798 254027 := bstep (se 1 (by rfl) ⟨190520, by rfl⟩ : syracuseStep 254027 = 381041) B381041
theorem B254039 : Blo 167798 254039 := bstep (se 1 (by rfl) ⟨190529, by rfl⟩ : syracuseStep 254039 = 381059) B381059
theorem B286807 : Blo 167798 286807 := bstep (se 1 (by rfl) ⟨215105, by rfl⟩ : syracuseStep 286807 = 430211) B430211
theorem B647261 : Blo 167798 647261 := bstep (se 3 (by rfl) ⟨121361, by rfl⟩ : syracuseStep 647261 = 242723) B242723
theorem B385163 : Blo 167798 385163 := bstep (se 1 (by rfl) ⟨288872, by rfl⟩ : syracuseStep 385163 = 577745) B577745
theorem B254105 : Blo 167798 254105 := bstep (se 2 (by rfl) ⟨95289, by rfl⟩ : syracuseStep 254105 = 190579) B190579
theorem B385217 : Blo 167798 385217 := bstep (se 2 (by rfl) ⟨144456, by rfl⟩ : syracuseStep 385217 = 288913) B288913
theorem B254219 : Blo 167798 254219 := bstep (se 1 (by rfl) ⟨190664, by rfl⟩ : syracuseStep 254219 = 381329) B381329
theorem B93184277 : Blo 167798 93184277 := bstep (se 6 (by rfl) ⟨2184006, by rfl⟩ : syracuseStep 93184277 = 4368013) B4368013
theorem B254231 : Blo 167798 254231 := bstep (se 1 (by rfl) ⟨190673, by rfl⟩ : syracuseStep 254231 = 381347) B381347
theorem B811309 : Blo 167798 811309 := bstep (se 3 (by rfl) ⟨152120, by rfl⟩ : syracuseStep 811309 = 304241) B304241
theorem B1827137 : Blo 167798 1827137 := bstep (se 2 (by rfl) ⟨685176, by rfl⟩ : syracuseStep 1827137 = 1370353) B1370353
theorem B254297 : Blo 167798 254297 := bstep (se 2 (by rfl) ⟨95361, by rfl⟩ : syracuseStep 254297 = 190723) B190723
theorem B1171805 : Blo 167798 1171805 := bstep (se 3 (by rfl) ⟨219713, by rfl⟩ : syracuseStep 1171805 = 439427) B439427
theorem B188779 : Blo 167798 188779 := bstep (se 1 (by rfl) ⟨141584, by rfl⟩ : syracuseStep 188779 = 283169) B283169
theorem B385433 : Blo 167798 385433 := bstep (se 2 (by rfl) ⟨144537, by rfl⟩ : syracuseStep 385433 = 289075) B289075
theorem B254411 : Blo 167798 254411 := bstep (se 1 (by rfl) ⟨190808, by rfl⟩ : syracuseStep 254411 = 381617) B381617
theorem B188887 : Blo 167798 188887 := bstep (se 1 (by rfl) ⟨141665, by rfl⟩ : syracuseStep 188887 = 283331) B283331
theorem B254423 : Blo 167798 254423 := bstep (se 1 (by rfl) ⟨190817, by rfl⟩ : syracuseStep 254423 = 381635) B381635
theorem B385523 : Blo 167798 385523 := bstep (se 1 (by rfl) ⟨289142, by rfl⟩ : syracuseStep 385523 = 578285) B578285
theorem B385559 : Blo 167798 385559 := bstep (se 1 (by rfl) ⟨289169, by rfl⟩ : syracuseStep 385559 = 578339) B578339
theorem B254489 : Blo 167798 254489 := bstep (se 2 (by rfl) ⟨95433, by rfl⟩ : syracuseStep 254489 = 190867) B190867
theorem B615043 : Blo 167798 615043 := bstep (se 1 (by rfl) ⟨461282, by rfl⟩ : syracuseStep 615043 = 922565) B922565
theorem B189067 : Blo 167798 189067 := bstep (se 1 (by rfl) ⟨141800, by rfl⟩ : syracuseStep 189067 = 283601) B283601
theorem B254603 : Blo 167798 254603 := bstep (se 1 (by rfl) ⟨190952, by rfl⟩ : syracuseStep 254603 = 381905) B381905
theorem B254615 : Blo 167798 254615 := bstep (se 1 (by rfl) ⟨190961, by rfl⟩ : syracuseStep 254615 = 381923) B381923
theorem B287435 : Blo 167798 287435 := bstep (se 1 (by rfl) ⟨215576, by rfl⟩ : syracuseStep 287435 = 431153) B431153
theorem B385739 : Blo 167798 385739 := bstep (se 1 (by rfl) ⟨289304, by rfl⟩ : syracuseStep 385739 = 578609) B578609
theorem B254681 : Blo 167798 254681 := bstep (se 2 (by rfl) ⟨95505, by rfl⟩ : syracuseStep 254681 = 191011) B191011
theorem B189175 : Blo 167798 189175 := bstep (se 1 (by rfl) ⟨141881, by rfl⟩ : syracuseStep 189175 = 283763) B283763
theorem B385793 : Blo 167798 385793 := bstep (se 2 (by rfl) ⟨144672, by rfl⟩ : syracuseStep 385793 = 289345) B289345
theorem B320267 : Blo 167798 320267 := bstep (se 1 (by rfl) ⟨240200, by rfl⟩ : syracuseStep 320267 = 480401) B480401
theorem B647959 : Blo 167798 647959 := bstep (se 1 (by rfl) ⟨485969, by rfl⟩ : syracuseStep 647959 = 971939) B971939
theorem B484147 : Blo 167798 484147 := bstep (se 1 (by rfl) ⟨363110, by rfl⟩ : syracuseStep 484147 = 726221) B726221
theorem B3662657 : Blo 167798 3662657 := bstep (se 2 (by rfl) ⟨1373496, by rfl⟩ : syracuseStep 3662657 = 2746993) B2746993
theorem B254795 : Blo 167798 254795 := bstep (se 1 (by rfl) ⟨191096, by rfl⟩ : syracuseStep 254795 = 382193) B382193
theorem B287563 : Blo 167798 287563 := bstep (se 1 (by rfl) ⟨215672, by rfl⟩ : syracuseStep 287563 = 431345) B431345
theorem B254807 : Blo 167798 254807 := bstep (se 1 (by rfl) ⟨191105, by rfl⟩ : syracuseStep 254807 = 382211) B382211
theorem B254873 : Blo 167798 254873 := bstep (se 2 (by rfl) ⟨95577, by rfl⟩ : syracuseStep 254873 = 191155) B191155
theorem B189355 : Blo 167798 189355 := bstep (se 1 (by rfl) ⟨142016, by rfl⟩ : syracuseStep 189355 = 284033) B284033
theorem B320449 : Blo 167798 320449 := bstep (se 2 (by rfl) ⟨120168, by rfl⟩ : syracuseStep 320449 = 240337) B240337
theorem B1467341 : Blo 167798 1467341 := bstep (se 3 (by rfl) ⟨275126, by rfl⟩ : syracuseStep 1467341 = 550253) B550253
theorem B287705 : Blo 167798 287705 := bstep (se 2 (by rfl) ⟨107889, by rfl⟩ : syracuseStep 287705 = 215779) B215779
theorem B386009 : Blo 167798 386009 := bstep (se 2 (by rfl) ⟨144753, by rfl⟩ : syracuseStep 386009 = 289507) B289507
theorem B254987 : Blo 167798 254987 := bstep (se 1 (by rfl) ⟨191240, by rfl⟩ : syracuseStep 254987 = 382481) B382481
theorem B189463 : Blo 167798 189463 := bstep (se 1 (by rfl) ⟨142097, by rfl⟩ : syracuseStep 189463 = 284195) B284195
theorem B254999 : Blo 167798 254999 := bstep (se 1 (by rfl) ⟨191249, by rfl⟩ : syracuseStep 254999 = 382499) B382499
theorem B484375 : Blo 167798 484375 := bstep (se 1 (by rfl) ⟨363281, by rfl⟩ : syracuseStep 484375 = 726563) B726563
theorem B386099 : Blo 167798 386099 := bstep (se 1 (by rfl) ⟨289574, by rfl⟩ : syracuseStep 386099 = 579149) B579149
theorem B386135 : Blo 167798 386135 := bstep (se 1 (by rfl) ⟨289601, by rfl⟩ : syracuseStep 386135 = 579203) B579203
theorem B255065 : Blo 167798 255065 := bstep (se 2 (by rfl) ⟨95649, by rfl⟩ : syracuseStep 255065 = 191299) B191299
theorem B287833 : Blo 167798 287833 := bstep (se 2 (by rfl) ⟨107937, by rfl⟩ : syracuseStep 287833 = 215875) B215875
theorem B189643 : Blo 167798 189643 := bstep (se 1 (by rfl) ⟨142232, by rfl⟩ : syracuseStep 189643 = 284465) B284465
theorem B255179 : Blo 167798 255179 := bstep (se 1 (by rfl) ⟨191384, by rfl⟩ : syracuseStep 255179 = 382769) B382769
theorem B255191 : Blo 167798 255191 := bstep (se 1 (by rfl) ⟨191393, by rfl⟩ : syracuseStep 255191 = 382787) B382787
theorem B386315 : Blo 167798 386315 := bstep (se 1 (by rfl) ⟨289736, by rfl⟩ : syracuseStep 386315 = 579473) B579473
theorem B255257 : Blo 167798 255257 := bstep (se 2 (by rfl) ⟨95721, by rfl⟩ : syracuseStep 255257 = 191443) B191443
theorem B189751 : Blo 167798 189751 := bstep (se 1 (by rfl) ⟨142313, by rfl⟩ : syracuseStep 189751 = 284627) B284627
theorem B386369 : Blo 167798 386369 := bstep (se 2 (by rfl) ⟨144888, by rfl⟩ : syracuseStep 386369 = 289777) B289777
theorem B320897 : Blo 167798 320897 := bstep (se 2 (by rfl) ⟨120336, by rfl⟩ : syracuseStep 320897 = 240673) B240673
theorem B255371 : Blo 167798 255371 := bstep (se 1 (by rfl) ⟨191528, by rfl⟩ : syracuseStep 255371 = 383057) B383057
theorem B255383 : Blo 167798 255383 := bstep (se 1 (by rfl) ⟨191537, by rfl⟩ : syracuseStep 255383 = 383075) B383075
theorem B255449 : Blo 167798 255449 := bstep (se 2 (by rfl) ⟨95793, by rfl⟩ : syracuseStep 255449 = 191587) B191587
theorem B189931 : Blo 167798 189931 := bstep (se 1 (by rfl) ⟨142448, by rfl⟩ : syracuseStep 189931 = 284897) B284897
theorem B648749 : Blo 167798 648749 := bstep (se 3 (by rfl) ⟨121640, by rfl⟩ : syracuseStep 648749 = 243281) B243281
theorem B1730123 : Blo 167798 1730123 := bstep (se 1 (by rfl) ⟨1297592, by rfl⟩ : syracuseStep 1730123 = 2595185) B2595185
theorem B255563 : Blo 167798 255563 := bstep (se 1 (by rfl) ⟨191672, by rfl⟩ : syracuseStep 255563 = 383345) B383345
theorem B190039 : Blo 167798 190039 := bstep (se 1 (by rfl) ⟨142529, by rfl⟩ : syracuseStep 190039 = 285059) B285059
theorem B255575 : Blo 167798 255575 := bstep (se 1 (by rfl) ⟨191681, by rfl⟩ : syracuseStep 255575 = 383363) B383363
theorem B288407 : Blo 167798 288407 := bstep (se 1 (by rfl) ⟨216305, by rfl⟩ : syracuseStep 288407 = 432611) B432611
theorem B288409 : Blo 167798 288409 := bstep (se 2 (by rfl) ⟨108153, by rfl⟩ : syracuseStep 288409 = 216307) B216307
theorem B255641 : Blo 167798 255641 := bstep (se 2 (by rfl) ⟨95865, by rfl⟩ : syracuseStep 255641 = 191731) B191731
theorem B321239 : Blo 167798 321239 := bstep (se 1 (by rfl) ⟨240929, by rfl⟩ : syracuseStep 321239 = 481859) B481859
theorem B190219 : Blo 167798 190219 := bstep (se 1 (by rfl) ⟨142664, by rfl⟩ : syracuseStep 190219 = 285329) B285329
theorem B255755 : Blo 167798 255755 := bstep (se 1 (by rfl) ⟨191816, by rfl⟩ : syracuseStep 255755 = 383633) B383633
theorem B255767 : Blo 167798 255767 := bstep (se 1 (by rfl) ⟨191825, by rfl⟩ : syracuseStep 255767 = 383651) B383651
theorem B288535 : Blo 167798 288535 := bstep (se 1 (by rfl) ⟨216401, by rfl⟩ : syracuseStep 288535 = 432803) B432803
theorem B255833 : Blo 167798 255833 := bstep (se 2 (by rfl) ⟨95937, by rfl⟩ : syracuseStep 255833 = 191875) B191875
theorem B681821 : Blo 167798 681821 := bstep (se 3 (by rfl) ⟨127841, by rfl⟩ : syracuseStep 681821 = 255683) B255683
theorem B190327 : Blo 167798 190327 := bstep (se 1 (by rfl) ⟨142745, by rfl⟩ : syracuseStep 190327 = 285491) B285491
theorem B255947 : Blo 167798 255947 := bstep (se 1 (by rfl) ⟨191960, by rfl⟩ : syracuseStep 255947 = 383921) B383921
theorem B255959 : Blo 167798 255959 := bstep (se 1 (by rfl) ⟨191969, by rfl⟩ : syracuseStep 255959 = 383939) B383939
theorem B256025 : Blo 167798 256025 := bstep (se 2 (by rfl) ⟨96009, by rfl⟩ : syracuseStep 256025 = 192019) B192019
theorem B190507 : Blo 167798 190507 := bstep (se 1 (by rfl) ⟨142880, by rfl⟩ : syracuseStep 190507 = 285761) B285761
theorem B2779267 : Blo 167798 2779267 := bstep (se 1 (by rfl) ⟨2084450, by rfl⟩ : syracuseStep 2779267 = 4168901) B4168901
theorem B256139 : Blo 167798 256139 := bstep (se 1 (by rfl) ⟨192104, by rfl⟩ : syracuseStep 256139 = 384209) B384209
theorem B190615 : Blo 167798 190615 := bstep (se 1 (by rfl) ⟨142961, by rfl⟩ : syracuseStep 190615 = 285923) B285923
theorem B256151 : Blo 167798 256151 := bstep (se 1 (by rfl) ⟨192113, by rfl⟩ : syracuseStep 256151 = 384227) B384227
theorem B256217 : Blo 167798 256217 := bstep (se 2 (by rfl) ⟨96081, by rfl⟩ : syracuseStep 256217 = 192163) B192163
theorem B190795 : Blo 167798 190795 := bstep (se 1 (by rfl) ⟨143096, by rfl⟩ : syracuseStep 190795 = 286193) B286193
theorem B256331 : Blo 167798 256331 := bstep (se 1 (by rfl) ⟨192248, by rfl⟩ : syracuseStep 256331 = 384497) B384497
theorem B256343 : Blo 167798 256343 := bstep (se 1 (by rfl) ⟨192257, by rfl⟩ : syracuseStep 256343 = 384515) B384515
theorem B321907 : Blo 167798 321907 := bstep (se 1 (by rfl) ⟨241430, by rfl⟩ : syracuseStep 321907 = 482861) B482861
theorem B289163 : Blo 167798 289163 := bstep (se 1 (by rfl) ⟨216872, by rfl⟩ : syracuseStep 289163 = 433745) B433745
theorem B1370519 : Blo 167798 1370519 := bstep (se 1 (by rfl) ⟨1027889, by rfl⟩ : syracuseStep 1370519 = 2055779) B2055779
theorem B256409 : Blo 167798 256409 := bstep (se 2 (by rfl) ⟨96153, by rfl⟩ : syracuseStep 256409 = 192307) B192307
theorem B190903 : Blo 167798 190903 := bstep (se 1 (by rfl) ⟨143177, by rfl⟩ : syracuseStep 190903 = 286355) B286355
theorem B256523 : Blo 167798 256523 := bstep (se 1 (by rfl) ⟨192392, by rfl⟩ : syracuseStep 256523 = 384785) B384785
theorem B289291 : Blo 167798 289291 := bstep (se 1 (by rfl) ⟨216968, by rfl⟩ : syracuseStep 289291 = 433937) B433937
theorem B256535 : Blo 167798 256535 := bstep (se 1 (by rfl) ⟨192401, by rfl⟩ : syracuseStep 256535 = 384803) B384803
theorem B977453 : Blo 167798 977453 := bstep (se 3 (by rfl) ⟨183272, by rfl⟩ : syracuseStep 977453 = 366545) B366545
theorem B256601 : Blo 167798 256601 := bstep (se 2 (by rfl) ⟨96225, by rfl⟩ : syracuseStep 256601 = 192451) B192451
theorem B191083 : Blo 167798 191083 := bstep (se 1 (by rfl) ⟨143312, by rfl⟩ : syracuseStep 191083 = 286625) B286625
theorem B289433 : Blo 167798 289433 := bstep (se 2 (by rfl) ⟨108537, by rfl⟩ : syracuseStep 289433 = 217075) B217075
theorem B256715 : Blo 167798 256715 := bstep (se 1 (by rfl) ⟨192536, by rfl⟩ : syracuseStep 256715 = 385073) B385073
theorem B191191 : Blo 167798 191191 := bstep (se 1 (by rfl) ⟨143393, by rfl⟩ : syracuseStep 191191 = 286787) B286787
theorem B256727 : Blo 167798 256727 := bstep (se 1 (by rfl) ⟨192545, by rfl⟩ : syracuseStep 256727 = 385091) B385091
theorem B256793 : Blo 167798 256793 := bstep (se 2 (by rfl) ⟨96297, by rfl⟩ : syracuseStep 256793 = 192595) B192595
theorem B289561 : Blo 167798 289561 := bstep (se 2 (by rfl) ⟨108585, by rfl⟩ : syracuseStep 289561 = 217171) B217171
theorem B322355 : Blo 167798 322355 := bstep (se 1 (by rfl) ⟨241766, by rfl⟩ : syracuseStep 322355 = 483533) B483533
theorem B322393 : Blo 167798 322393 := bstep (se 2 (by rfl) ⟨120897, by rfl⟩ : syracuseStep 322393 = 241795) B241795
theorem B486233 : Blo 167798 486233 := bstep (se 2 (by rfl) ⟨182337, by rfl⟩ : syracuseStep 486233 = 364675) B364675
theorem B191371 : Blo 167798 191371 := bstep (se 1 (by rfl) ⟨143528, by rfl⟩ : syracuseStep 191371 = 287057) B287057
theorem B256907 : Blo 167798 256907 := bstep (se 1 (by rfl) ⟨192680, by rfl⟩ : syracuseStep 256907 = 385361) B385361
theorem B256919 : Blo 167798 256919 := bstep (se 1 (by rfl) ⟨192689, by rfl⟩ : syracuseStep 256919 = 385379) B385379
theorem B650177 : Blo 167798 650177 := bstep (se 2 (by rfl) ⟨243816, by rfl⟩ : syracuseStep 650177 = 487633) B487633
theorem B256985 : Blo 167798 256985 := bstep (se 2 (by rfl) ⟨96369, by rfl⟩ : syracuseStep 256985 = 192739) B192739
theorem B191479 : Blo 167798 191479 := bstep (se 1 (by rfl) ⟨143609, by rfl⟩ : syracuseStep 191479 = 287219) B287219
theorem B191543 : Blo 167798 191543 := bstep (se 1 (by rfl) ⟨143657, by rfl⟩ : syracuseStep 191543 = 287315) B287315
theorem B257099 : Blo 167798 257099 := bstep (se 1 (by rfl) ⟨192824, by rfl⟩ : syracuseStep 257099 = 385649) B385649
theorem B257111 : Blo 167798 257111 := bstep (se 1 (by rfl) ⟨192833, by rfl⟩ : syracuseStep 257111 = 385667) B385667
theorem B257177 : Blo 167798 257177 := bstep (se 2 (by rfl) ⟨96441, by rfl⟩ : syracuseStep 257177 = 192883) B192883
theorem B191659 : Blo 167798 191659 := bstep (se 1 (by rfl) ⟨143744, by rfl⟩ : syracuseStep 191659 = 287489) B287489
theorem B584921 : Blo 167798 584921 := bstep (se 2 (by rfl) ⟨219345, by rfl⟩ : syracuseStep 584921 = 438691) B438691
theorem B257291 : Blo 167798 257291 := bstep (se 1 (by rfl) ⟨192968, by rfl⟩ : syracuseStep 257291 = 385937) B385937
theorem B486679 : Blo 167798 486679 := bstep (se 1 (by rfl) ⟨365009, by rfl⟩ : syracuseStep 486679 = 730019) B730019
theorem B191767 : Blo 167798 191767 := bstep (se 1 (by rfl) ⟨143825, by rfl⟩ : syracuseStep 191767 = 287651) B287651
theorem B322841 : Blo 167798 322841 := bstep (se 2 (by rfl) ⟨121065, by rfl⟩ : syracuseStep 322841 = 242131) B242131
theorem B257303 : Blo 167798 257303 := bstep (se 1 (by rfl) ⟨192977, by rfl⟩ : syracuseStep 257303 = 385955) B385955
theorem B781643 : Blo 167798 781643 := bstep (se 1 (by rfl) ⟨586232, by rfl⟩ : syracuseStep 781643 = 1172465) B1172465
theorem B257369 : Blo 167798 257369 := bstep (se 2 (by rfl) ⟨96513, by rfl⟩ : syracuseStep 257369 = 193027) B193027
theorem B7925141 : Blo 167798 7925141 := bstep (se 6 (by rfl) ⟨185745, by rfl⟩ : syracuseStep 7925141 = 371491) B371491
theorem B191947 : Blo 167798 191947 := bstep (se 1 (by rfl) ⟨143960, by rfl⟩ : syracuseStep 191947 = 287921) B287921
theorem B257483 : Blo 167798 257483 := bstep (se 1 (by rfl) ⟨193112, by rfl⟩ : syracuseStep 257483 = 386225) B386225
theorem B257495 : Blo 167798 257495 := bstep (se 1 (by rfl) ⟨193121, by rfl⟩ : syracuseStep 257495 = 386243) B386243
theorem B257561 : Blo 167798 257561 := bstep (se 2 (by rfl) ⟨96585, by rfl⟩ : syracuseStep 257561 = 193171) B193171
theorem B192055 : Blo 167798 192055 := bstep (se 1 (by rfl) ⟨144041, by rfl⟩ : syracuseStep 192055 = 288083) B288083
theorem B257675 : Blo 167798 257675 := bstep (se 1 (by rfl) ⟨193256, by rfl⟩ : syracuseStep 257675 = 386513) B386513
theorem B487063 : Blo 167798 487063 := bstep (se 1 (by rfl) ⟨365297, by rfl⟩ : syracuseStep 487063 = 730595) B730595
theorem B257687 : Blo 167798 257687 := bstep (se 1 (by rfl) ⟨193265, by rfl⟩ : syracuseStep 257687 = 386531) B386531
theorem B192235 : Blo 167798 192235 := bstep (se 1 (by rfl) ⟨144176, by rfl⟩ : syracuseStep 192235 = 288353) B288353
theorem B192343 : Blo 167798 192343 := bstep (se 1 (by rfl) ⟨144257, by rfl⟩ : syracuseStep 192343 = 288515) B288515
theorem B388979 : Blo 167798 388979 := bstep (se 1 (by rfl) ⟨291734, by rfl⟩ : syracuseStep 388979 = 583469) B583469
theorem B323585 : Blo 167798 323585 := bstep (se 2 (by rfl) ⟨121344, by rfl⟩ : syracuseStep 323585 = 242689) B242689
theorem B192523 : Blo 167798 192523 := bstep (se 1 (by rfl) ⟨144392, by rfl⟩ : syracuseStep 192523 = 288785) B288785
theorem B192631 : Blo 167798 192631 := bstep (se 1 (by rfl) ⟨144473, by rfl⟩ : syracuseStep 192631 = 288947) B288947
theorem B389387 : Blo 167798 389387 := bstep (se 1 (by rfl) ⟨292040, by rfl⟩ : syracuseStep 389387 = 584081) B584081
theorem B323851 : Blo 167798 323851 := bstep (se 1 (by rfl) ⟨242888, by rfl⟩ : syracuseStep 323851 = 485777) B485777
theorem B192811 : Blo 167798 192811 := bstep (se 1 (by rfl) ⟨144608, by rfl⟩ : syracuseStep 192811 = 289217) B289217
theorem B651665 : Blo 167798 651665 := bstep (se 2 (by rfl) ⟨244374, by rfl⟩ : syracuseStep 651665 = 488749) B488749
theorem B258455 : Blo 167798 258455 := bstep (se 1 (by rfl) ⟨193841, by rfl⟩ : syracuseStep 258455 = 387683) B387683
theorem B192919 : Blo 167798 192919 := bstep (se 1 (by rfl) ⟨144689, by rfl⟩ : syracuseStep 192919 = 289379) B289379
theorem B1274291 : Blo 167798 1274291 := bstep (se 1 (by rfl) ⟨955718, by rfl⟩ : syracuseStep 1274291 = 1911437) B1911437
theorem B487883 : Blo 167798 487883 := bstep (se 1 (by rfl) ⟨365912, by rfl⟩ : syracuseStep 487883 = 731825) B731825
theorem B193099 : Blo 167798 193099 := bstep (se 1 (by rfl) ⟨144824, by rfl⟩ : syracuseStep 193099 = 289649) B289649
theorem B1110629 : Blo 167798 1110629 := bstep (se 4 (by rfl) ⟨104121, by rfl⟩ : syracuseStep 1110629 = 208243) B208243
theorem B717457 : Blo 167798 717457 := bstep (se 2 (by rfl) ⟨269046, by rfl⟩ : syracuseStep 717457 = 538093) B538093
theorem B193207 : Blo 167798 193207 := bstep (se 1 (by rfl) ⟨144905, by rfl⟩ : syracuseStep 193207 = 289811) B289811
theorem B324299 : Blo 167798 324299 := bstep (se 1 (by rfl) ⟨243224, by rfl⟩ : syracuseStep 324299 = 486449) B486449
theorem B1438499 : Blo 167798 1438499 := bstep (se 1 (by rfl) ⟨1078874, by rfl⟩ : syracuseStep 1438499 = 2157749) B2157749
theorem B652121 : Blo 167798 652121 := bstep (se 2 (by rfl) ⟨244545, by rfl⟩ : syracuseStep 652121 = 489091) B489091
theorem B1078109 : Blo 167798 1078109 := bstep (se 3 (by rfl) ⟨202145, by rfl⟩ : syracuseStep 1078109 = 404291) B404291
theorem B324481 : Blo 167798 324481 := bstep (se 2 (by rfl) ⟨121680, by rfl⟩ : syracuseStep 324481 = 243361) B243361
theorem B914327 : Blo 167798 914327 := bstep (se 1 (by rfl) ⟨685745, by rfl⟩ : syracuseStep 914327 = 1371491) B1371491
theorem B390167 : Blo 167798 390167 := bstep (se 1 (by rfl) ⟨292625, by rfl⟩ : syracuseStep 390167 = 585251) B585251
theorem B1930391 : Blo 167798 1930391 := bstep (se 1 (by rfl) ⟨1447793, by rfl⟩ : syracuseStep 1930391 = 2895587) B2895587
theorem B324823 : Blo 167798 324823 := bstep (se 1 (by rfl) ⟨243617, by rfl⟩ : syracuseStep 324823 = 487235) B487235
theorem B1111475 : Blo 167798 1111475 := bstep (se 1 (by rfl) ⟨833606, by rfl⟩ : syracuseStep 1111475 = 1667213) B1667213
theorem B325043 : Blo 167798 325043 := bstep (se 1 (by rfl) ⟨243782, by rfl⟩ : syracuseStep 325043 = 487565) B487565
theorem B325271 : Blo 167798 325271 := bstep (se 1 (by rfl) ⟨243953, by rfl⟩ : syracuseStep 325271 = 487907) B487907
theorem B1275749 : Blo 167798 1275749 := bstep (se 4 (by rfl) ⟨119601, by rfl⟩ : syracuseStep 1275749 = 239203) B239203
theorem B325529 : Blo 167798 325529 := bstep (se 2 (by rfl) ⟨122073, by rfl⟩ : syracuseStep 325529 = 244147) B244147
theorem B2193425 : Blo 167798 2193425 := bstep (se 2 (by rfl) ⟨822534, by rfl⟩ : syracuseStep 2193425 = 1645069) B1645069
theorem B260183 : Blo 167798 260183 := bstep (se 1 (by rfl) ⟨195137, by rfl⟩ : syracuseStep 260183 = 390275) B390275
theorem B850013 : Blo 167798 850013 := bstep (se 3 (by rfl) ⟨159377, by rfl⟩ : syracuseStep 850013 = 318755) B318755
theorem B194711 : Blo 167798 194711 := bstep (se 1 (by rfl) ⟨146033, by rfl⟩ : syracuseStep 194711 = 292067) B292067
theorem B260377 : Blo 167798 260377 := bstep (se 2 (by rfl) ⟨97641, by rfl⟩ : syracuseStep 260377 = 195283) B195283
theorem B325939 : Blo 167798 325939 := bstep (se 1 (by rfl) ⟨244454, by rfl⟩ : syracuseStep 325939 = 488909) B488909
theorem B653633 : Blo 167798 653633 := bstep (se 2 (by rfl) ⟨245112, by rfl⟩ : syracuseStep 653633 = 490225) B490225
theorem B1276235 : Blo 167798 1276235 := bstep (se 1 (by rfl) ⟨957176, by rfl⟩ : syracuseStep 1276235 = 1914353) B1914353
theorem B358771 : Blo 167798 358771 := bstep (se 1 (by rfl) ⟨269078, by rfl⟩ : syracuseStep 358771 = 538157) B538157
theorem B2521613 : Blo 167798 2521613 := bstep (se 3 (by rfl) ⟨472802, by rfl⟩ : syracuseStep 2521613 = 945605) B945605
theorem B293719 : Blo 167798 293719 := bstep (se 1 (by rfl) ⟨220289, by rfl⟩ : syracuseStep 293719 = 440579) B440579
theorem B1538909 : Blo 167798 1538909 := bstep (se 3 (by rfl) ⟨288545, by rfl⟩ : syracuseStep 1538909 = 577091) B577091
theorem B359959 : Blo 167798 359959 := bstep (se 1 (by rfl) ⟨269969, by rfl⟩ : syracuseStep 359959 = 539939) B539939
theorem B360001 : Blo 167798 360001 := bstep (se 2 (by rfl) ⟨135000, by rfl⟩ : syracuseStep 360001 = 270001) B270001
theorem B720515 : Blo 167798 720515 := bstep (se 1 (by rfl) ⟨540386, by rfl⟩ : syracuseStep 720515 = 1080773) B1080773
theorem B425675 : Blo 167798 425675 := bstep (se 1 (by rfl) ⟨319256, by rfl⟩ : syracuseStep 425675 = 638513) B638513
theorem B425999 : Blo 167798 425999 := bstep (se 1 (by rfl) ⟨319499, by rfl⟩ : syracuseStep 425999 = 638999) B638999
theorem B360463 : Blo 167798 360463 := bstep (se 1 (by rfl) ⟨270347, by rfl⟩ : syracuseStep 360463 = 540695) B540695
theorem B819229 : Blo 167798 819229 := bstep (se 3 (by rfl) ⟨153605, by rfl⟩ : syracuseStep 819229 = 307211) B307211
theorem B655447 : Blo 167798 655447 := bstep (se 1 (by rfl) ⟨491585, by rfl⟩ : syracuseStep 655447 = 983171) B983171
theorem B426131 : Blo 167798 426131 := bstep (se 1 (by rfl) ⟨319598, by rfl⟩ : syracuseStep 426131 = 639197) B639197
theorem B1081745 : Blo 167798 1081745 := bstep (se 2 (by rfl) ⟨405654, by rfl⟩ : syracuseStep 1081745 = 811309) B811309
theorem B229879 : Blo 167798 229879 := bstep (se 1 (by rfl) ⟨172409, by rfl⟩ : syracuseStep 229879 = 344819) B344819
theorem B655939 : Blo 167798 655939 := bstep (se 1 (by rfl) ⟨491954, by rfl⟩ : syracuseStep 655939 = 983909) B983909
theorem B459553 : Blo 167798 459553 := bstep (se 2 (by rfl) ⟨172332, by rfl⟩ : syracuseStep 459553 = 344665) B344665
theorem B459607 : Blo 167798 459607 := bstep (se 1 (by rfl) ⟨344705, by rfl⟩ : syracuseStep 459607 = 689411) B689411
theorem B820057 : Blo 167798 820057 := bstep (se 2 (by rfl) ⟨307521, by rfl⟩ : syracuseStep 820057 = 615043) B615043
theorem B361351 : Blo 167798 361351 := bstep (se 1 (by rfl) ⟨271013, by rfl⟩ : syracuseStep 361351 = 542027) B542027
theorem B820115 : Blo 167798 820115 := bstep (se 1 (by rfl) ⟨615086, by rfl⟩ : syracuseStep 820115 = 1230173) B1230173
theorem B623627 : Blo 167798 623627 := bstep (se 1 (by rfl) ⟨467720, by rfl⟩ : syracuseStep 623627 = 935441) B935441
theorem B361505 : Blo 167798 361505 := bstep (se 2 (by rfl) ⟨135564, by rfl⟩ : syracuseStep 361505 = 271129) B271129
theorem B689213 : Blo 167798 689213 := bstep (se 3 (by rfl) ⟨129227, by rfl⟩ : syracuseStep 689213 = 258455) B258455
theorem B427265 : Blo 167798 427265 := bstep (se 2 (by rfl) ⟨160224, by rfl⟩ : syracuseStep 427265 = 320449) B320449
theorem B492833 : Blo 167798 492833 := bstep (se 2 (by rfl) ⟨184812, by rfl⟩ : syracuseStep 492833 = 369625) B369625
theorem B361847 : Blo 167798 361847 := bstep (se 1 (by rfl) ⟨271385, by rfl⟩ : syracuseStep 361847 = 542771) B542771
theorem B1082771 : Blo 167798 1082771 := bstep (se 1 (by rfl) ⟨812078, by rfl⟩ : syracuseStep 1082771 = 1624157) B1624157
theorem B1148381 : Blo 167798 1148381 := bstep (se 3 (by rfl) ⟨215321, by rfl⟩ : syracuseStep 1148381 = 430643) B430643
theorem B493067 : Blo 167798 493067 := bstep (se 1 (by rfl) ⟨369800, by rfl⟩ : syracuseStep 493067 = 739601) B739601
theorem B362017 : Blo 167798 362017 := bstep (se 2 (by rfl) ⟨135756, by rfl⟩ : syracuseStep 362017 = 271513) B271513
theorem B427639 : Blo 167798 427639 := bstep (se 1 (by rfl) ⟨320729, by rfl⟩ : syracuseStep 427639 = 641459) B641459
theorem B690187 : Blo 167798 690187 := bstep (se 1 (by rfl) ⟨517640, by rfl⟩ : syracuseStep 690187 = 1035281) B1035281
theorem B428075 : Blo 167798 428075 := bstep (se 1 (by rfl) ⟨321056, by rfl⟩ : syracuseStep 428075 = 642113) B642113
theorem B460859 : Blo 167798 460859 := bstep (se 1 (by rfl) ⟨345644, by rfl⟩ : syracuseStep 460859 = 691289) B691289
theorem B755831 : Blo 167798 755831 := bstep (se 1 (by rfl) ⟨566873, by rfl⟩ : syracuseStep 755831 = 1133747) B1133747
theorem B657665 : Blo 167798 657665 := bstep (se 2 (by rfl) ⟨246624, by rfl⟩ : syracuseStep 657665 = 493249) B493249
theorem B330043 : Blo 167798 330043 := bstep (se 1 (by rfl) ⟨247532, by rfl⟩ : syracuseStep 330043 = 495065) B495065
theorem B854387 : Blo 167798 854387 := bstep (se 1 (by rfl) ⟨640790, by rfl⟩ : syracuseStep 854387 = 1281581) B1281581
theorem B920335 : Blo 167798 920335 := bstep (se 1 (by rfl) ⟨690251, by rfl⟩ : syracuseStep 920335 = 1380503) B1380503
theorem B625441 : Blo 167798 625441 := bstep (se 2 (by rfl) ⟨234540, by rfl⟩ : syracuseStep 625441 = 469081) B469081
theorem B854873 : Blo 167798 854873 := bstep (se 2 (by rfl) ⟨320577, by rfl⟩ : syracuseStep 854873 = 641155) B641155
theorem B985945 : Blo 167798 985945 := bstep (se 2 (by rfl) ⟨369729, by rfl⟩ : syracuseStep 985945 = 739459) B739459
theorem B3705689 : Blo 167798 3705689 := bstep (se 2 (by rfl) ⟨1389633, by rfl⟩ : syracuseStep 3705689 = 2779267) B2779267
theorem B12389219 : Blo 167798 12389219 := bstep (se 1 (by rfl) ⟨9291914, by rfl⟩ : syracuseStep 12389219 = 18583829) B18583829
theorem B428915 : Blo 167798 428915 := bstep (se 1 (by rfl) ⟨321686, by rfl⟩ : syracuseStep 428915 = 643373) B643373
theorem B428935 : Blo 167798 428935 := bstep (se 1 (by rfl) ⟨321701, by rfl⟩ : syracuseStep 428935 = 643403) B643403
theorem B429209 : Blo 167798 429209 := bstep (se 2 (by rfl) ⟨160953, by rfl⟩ : syracuseStep 429209 = 321907) B321907
theorem B429371 : Blo 167798 429371 := bstep (se 1 (by rfl) ⟨322028, by rfl⟩ : syracuseStep 429371 = 644057) B644057
theorem B363923 : Blo 167798 363923 := bstep (se 1 (by rfl) ⟨272942, by rfl⟩ : syracuseStep 363923 = 545885) B545885
theorem B429583 : Blo 167798 429583 := bstep (se 1 (by rfl) ⟨322187, by rfl⟩ : syracuseStep 429583 = 644375) B644375
theorem B724717 : Blo 167798 724717 := bstep (se 3 (by rfl) ⟨135884, by rfl⟩ : syracuseStep 724717 = 271769) B271769
theorem B429857 : Blo 167798 429857 := bstep (se 2 (by rfl) ⟨161196, by rfl⟩ : syracuseStep 429857 = 322393) B322393
theorem B2723635 : Blo 167798 2723635 := bstep (se 1 (by rfl) ⟨2042726, by rfl⟩ : syracuseStep 2723635 = 4085453) B4085453
theorem B167815 : Blo 167798 167815 := bstep (se 1 (by rfl) ⟨125861, by rfl⟩ : syracuseStep 167815 = 251723) B251723
theorem B167823 : Blo 167798 167823 := bstep (se 1 (by rfl) ⟨125867, by rfl⟩ : syracuseStep 167823 = 251735) B251735
theorem B724889 : Blo 167798 724889 := bstep (se 2 (by rfl) ⟨271833, by rfl⟩ : syracuseStep 724889 = 543667) B543667
theorem B167867 : Blo 167798 167867 := bstep (se 1 (by rfl) ⟨125900, by rfl⟩ : syracuseStep 167867 = 251801) B251801
theorem B921547 : Blo 167798 921547 := bstep (se 1 (by rfl) ⟨691160, by rfl⟩ : syracuseStep 921547 = 1382321) B1382321
theorem B167943 : Blo 167798 167943 := bstep (se 1 (by rfl) ⟨125957, by rfl⟩ : syracuseStep 167943 = 251915) B251915
theorem B167951 : Blo 167798 167951 := bstep (se 1 (by rfl) ⟨125963, by rfl⟩ : syracuseStep 167951 = 251927) B251927
theorem B2199575 : Blo 167798 2199575 := bstep (se 1 (by rfl) ⟨1649681, by rfl⟩ : syracuseStep 2199575 = 3299363) B3299363
theorem B167995 : Blo 167798 167995 := bstep (se 1 (by rfl) ⟨125996, by rfl⟩ : syracuseStep 167995 = 251993) B251993
theorem B364603 : Blo 167798 364603 := bstep (se 1 (by rfl) ⟨273452, by rfl⟩ : syracuseStep 364603 = 546905) B546905
theorem B168071 : Blo 167798 168071 := bstep (se 1 (by rfl) ⟨126053, by rfl⟩ : syracuseStep 168071 = 252107) B252107
theorem B168079 : Blo 167798 168079 := bstep (se 1 (by rfl) ⟨126059, by rfl⟩ : syracuseStep 168079 = 252119) B252119
theorem B168123 : Blo 167798 168123 := bstep (se 1 (by rfl) ⟨126092, by rfl⟩ : syracuseStep 168123 = 252185) B252185
theorem B168199 : Blo 167798 168199 := bstep (se 1 (by rfl) ⟨126149, by rfl⟩ : syracuseStep 168199 = 252299) B252299
theorem B168207 : Blo 167798 168207 := bstep (se 1 (by rfl) ⟨126155, by rfl⟩ : syracuseStep 168207 = 252311) B252311
theorem B1937681 : Blo 167798 1937681 := bstep (se 2 (by rfl) ⟨726630, by rfl⟩ : syracuseStep 1937681 = 1453261) B1453261
theorem B168251 : Blo 167798 168251 := bstep (se 1 (by rfl) ⟨126188, by rfl⟩ : syracuseStep 168251 = 252377) B252377
theorem B168327 : Blo 167798 168327 := bstep (se 1 (by rfl) ⟨126245, by rfl⟩ : syracuseStep 168327 = 252491) B252491
theorem B168335 : Blo 167798 168335 := bstep (se 1 (by rfl) ⟨126251, by rfl⟩ : syracuseStep 168335 = 252503) B252503
theorem B168379 : Blo 167798 168379 := bstep (se 1 (by rfl) ⟨126284, by rfl⟩ : syracuseStep 168379 = 252569) B252569
theorem B168455 : Blo 167798 168455 := bstep (se 1 (by rfl) ⟨126341, by rfl⟩ : syracuseStep 168455 = 252683) B252683
theorem B168463 : Blo 167798 168463 := bstep (se 1 (by rfl) ⟨126347, by rfl⟩ : syracuseStep 168463 = 252695) B252695
theorem B3543587 : Blo 167798 3543587 := bstep (se 1 (by rfl) ⟨2657690, by rfl⟩ : syracuseStep 3543587 = 5315381) B5315381
theorem B168507 : Blo 167798 168507 := bstep (se 1 (by rfl) ⟨126380, by rfl⟩ : syracuseStep 168507 = 252761) B252761
theorem B168583 : Blo 167798 168583 := bstep (se 1 (by rfl) ⟨126437, by rfl⟩ : syracuseStep 168583 = 252875) B252875
theorem B168591 : Blo 167798 168591 := bstep (se 1 (by rfl) ⟨126443, by rfl⟩ : syracuseStep 168591 = 252887) B252887
theorem B168635 : Blo 167798 168635 := bstep (se 1 (by rfl) ⟨126476, by rfl⟩ : syracuseStep 168635 = 252953) B252953
theorem B168711 : Blo 167798 168711 := bstep (se 1 (by rfl) ⟨126533, by rfl⟩ : syracuseStep 168711 = 253067) B253067
theorem B430859 : Blo 167798 430859 := bstep (se 1 (by rfl) ⟨323144, by rfl⟩ : syracuseStep 430859 = 646289) B646289
theorem B463627 : Blo 167798 463627 := bstep (se 1 (by rfl) ⟨347720, by rfl⟩ : syracuseStep 463627 = 695441) B695441
theorem B168719 : Blo 167798 168719 := bstep (se 1 (by rfl) ⟨126539, by rfl⟩ : syracuseStep 168719 = 253079) B253079
theorem B168763 : Blo 167798 168763 := bstep (se 1 (by rfl) ⟨126572, by rfl⟩ : syracuseStep 168763 = 253145) B253145
theorem B693107 : Blo 167798 693107 := bstep (se 1 (by rfl) ⟨519830, by rfl⟩ : syracuseStep 693107 = 1039661) B1039661
theorem B168839 : Blo 167798 168839 := bstep (se 1 (by rfl) ⟨126629, by rfl⟩ : syracuseStep 168839 = 253259) B253259
theorem B168847 : Blo 167798 168847 := bstep (se 1 (by rfl) ⟨126635, by rfl⟩ : syracuseStep 168847 = 253271) B253271
theorem B856979 : Blo 167798 856979 := bstep (se 1 (by rfl) ⟨642734, by rfl⟩ : syracuseStep 856979 = 1285469) B1285469
theorem B168891 : Blo 167798 168891 := bstep (se 1 (by rfl) ⟨126668, by rfl⟩ : syracuseStep 168891 = 253337) B253337
theorem B168967 : Blo 167798 168967 := bstep (se 1 (by rfl) ⟨126725, by rfl⟩ : syracuseStep 168967 = 253451) B253451
theorem B168975 : Blo 167798 168975 := bstep (se 1 (by rfl) ⟨126731, by rfl⟩ : syracuseStep 168975 = 253463) B253463
theorem B824363 : Blo 167798 824363 := bstep (se 1 (by rfl) ⟨618272, by rfl⟩ : syracuseStep 824363 = 1236545) B1236545
theorem B169019 : Blo 167798 169019 := bstep (se 1 (by rfl) ⟨126764, by rfl⟩ : syracuseStep 169019 = 253529) B253529
theorem B824381 : Blo 167798 824381 := bstep (se 3 (by rfl) ⟨154571, by rfl⟩ : syracuseStep 824381 = 309143) B309143
theorem B169095 : Blo 167798 169095 := bstep (se 1 (by rfl) ⟨126821, by rfl⟩ : syracuseStep 169095 = 253643) B253643
theorem B169103 : Blo 167798 169103 := bstep (se 1 (by rfl) ⟨126827, by rfl⟩ : syracuseStep 169103 = 253655) B253655
theorem B169147 : Blo 167798 169147 := bstep (se 1 (by rfl) ⟨126860, by rfl⟩ : syracuseStep 169147 = 253721) B253721
theorem B169223 : Blo 167798 169223 := bstep (se 1 (by rfl) ⟨126917, by rfl⟩ : syracuseStep 169223 = 253835) B253835
theorem B169231 : Blo 167798 169231 := bstep (se 1 (by rfl) ⟨126923, by rfl⟩ : syracuseStep 169231 = 253847) B253847
theorem B169275 : Blo 167798 169275 := bstep (se 1 (by rfl) ⟨126956, by rfl⟩ : syracuseStep 169275 = 253913) B253913
theorem B169351 : Blo 167798 169351 := bstep (se 1 (by rfl) ⟨127013, by rfl⟩ : syracuseStep 169351 = 254027) B254027
theorem B169359 : Blo 167798 169359 := bstep (se 1 (by rfl) ⟨127019, by rfl⟩ : syracuseStep 169359 = 254039) B254039
theorem B431507 : Blo 167798 431507 := bstep (se 1 (by rfl) ⟨323630, by rfl⟩ : syracuseStep 431507 = 647261) B647261
theorem B169403 : Blo 167798 169403 := bstep (se 1 (by rfl) ⟨127052, by rfl⟩ : syracuseStep 169403 = 254105) B254105
theorem B169479 : Blo 167798 169479 := bstep (se 1 (by rfl) ⟨127109, by rfl⟩ : syracuseStep 169479 = 254219) B254219
theorem B169487 : Blo 167798 169487 := bstep (se 1 (by rfl) ⟨127115, by rfl⟩ : syracuseStep 169487 = 254231) B254231
theorem B1218091 : Blo 167798 1218091 := bstep (se 1 (by rfl) ⟨913568, by rfl⟩ : syracuseStep 1218091 = 1827137) B1827137
theorem B169531 : Blo 167798 169531 := bstep (se 1 (by rfl) ⟨127148, by rfl⟩ : syracuseStep 169531 = 254297) B254297
theorem B693821 : Blo 167798 693821 := bstep (se 3 (by rfl) ⟨130091, by rfl⟩ : syracuseStep 693821 = 260183) B260183
theorem B169607 : Blo 167798 169607 := bstep (se 1 (by rfl) ⟨127205, by rfl⟩ : syracuseStep 169607 = 254411) B254411
theorem B169615 : Blo 167798 169615 := bstep (se 1 (by rfl) ⟨127211, by rfl⟩ : syracuseStep 169615 = 254423) B254423
theorem B431801 : Blo 167798 431801 := bstep (se 2 (by rfl) ⟨161925, by rfl⟩ : syracuseStep 431801 = 323851) B323851
theorem B169659 : Blo 167798 169659 := bstep (se 1 (by rfl) ⟨127244, by rfl⟩ : syracuseStep 169659 = 254489) B254489
theorem B169735 : Blo 167798 169735 := bstep (se 1 (by rfl) ⟨127301, by rfl⟩ : syracuseStep 169735 = 254603) B254603
theorem B169743 : Blo 167798 169743 := bstep (se 1 (by rfl) ⟨127307, by rfl⟩ : syracuseStep 169743 = 254615) B254615
theorem B169787 : Blo 167798 169787 := bstep (se 1 (by rfl) ⟨127340, by rfl⟩ : syracuseStep 169787 = 254681) B254681
theorem B169863 : Blo 167798 169863 := bstep (se 1 (by rfl) ⟨127397, by rfl⟩ : syracuseStep 169863 = 254795) B254795
theorem B169871 : Blo 167798 169871 := bstep (se 1 (by rfl) ⟨127403, by rfl⟩ : syracuseStep 169871 = 254807) B254807
theorem B169915 : Blo 167798 169915 := bstep (se 1 (by rfl) ⟨127436, by rfl⟩ : syracuseStep 169915 = 254873) B254873
theorem B169991 : Blo 167798 169991 := bstep (se 1 (by rfl) ⟨127493, by rfl⟩ : syracuseStep 169991 = 254987) B254987
theorem B169999 : Blo 167798 169999 := bstep (se 1 (by rfl) ⟨127499, by rfl⟩ : syracuseStep 169999 = 254999) B254999
theorem B170043 : Blo 167798 170043 := bstep (se 1 (by rfl) ⟨127532, by rfl⟩ : syracuseStep 170043 = 255065) B255065
theorem B170119 : Blo 167798 170119 := bstep (se 1 (by rfl) ⟨127589, by rfl⟩ : syracuseStep 170119 = 255179) B255179
theorem B170127 : Blo 167798 170127 := bstep (se 1 (by rfl) ⟨127595, by rfl⟩ : syracuseStep 170127 = 255191) B255191
theorem B170171 : Blo 167798 170171 := bstep (se 1 (by rfl) ⟨127628, by rfl⟩ : syracuseStep 170171 = 255257) B255257
theorem B956609 : Blo 167798 956609 := bstep (se 2 (by rfl) ⟨358728, by rfl⟩ : syracuseStep 956609 = 717457) B717457
theorem B170247 : Blo 167798 170247 := bstep (se 1 (by rfl) ⟨127685, by rfl⟩ : syracuseStep 170247 = 255371) B255371
theorem B170255 : Blo 167798 170255 := bstep (se 1 (by rfl) ⟨127691, by rfl⟩ : syracuseStep 170255 = 255383) B255383
theorem B170299 : Blo 167798 170299 := bstep (se 1 (by rfl) ⟨127724, by rfl⟩ : syracuseStep 170299 = 255449) B255449
theorem B432499 : Blo 167798 432499 := bstep (se 1 (by rfl) ⟨324374, by rfl⟩ : syracuseStep 432499 = 648749) B648749
theorem B1153415 : Blo 167798 1153415 := bstep (se 1 (by rfl) ⟨865061, by rfl⟩ : syracuseStep 1153415 = 1730123) B1730123
theorem B170375 : Blo 167798 170375 := bstep (se 1 (by rfl) ⟨127781, by rfl⟩ : syracuseStep 170375 = 255563) B255563
theorem B170383 : Blo 167798 170383 := bstep (se 1 (by rfl) ⟨127787, by rfl⟩ : syracuseStep 170383 = 255575) B255575
theorem B1284497 : Blo 167798 1284497 := bstep (se 2 (by rfl) ⟨481686, by rfl⟩ : syracuseStep 1284497 = 963373) B963373
theorem B170427 : Blo 167798 170427 := bstep (se 1 (by rfl) ⟨127820, by rfl⟩ : syracuseStep 170427 = 255641) B255641
theorem B432641 : Blo 167798 432641 := bstep (se 2 (by rfl) ⟨162240, by rfl⟩ : syracuseStep 432641 = 324481) B324481
theorem B170503 : Blo 167798 170503 := bstep (se 1 (by rfl) ⟨127877, by rfl⟩ : syracuseStep 170503 = 255755) B255755
theorem B170511 : Blo 167798 170511 := bstep (se 1 (by rfl) ⟨127883, by rfl⟩ : syracuseStep 170511 = 255767) B255767
theorem B170555 : Blo 167798 170555 := bstep (se 1 (by rfl) ⟨127916, by rfl⟩ : syracuseStep 170555 = 255833) B255833
theorem B170631 : Blo 167798 170631 := bstep (se 1 (by rfl) ⟨127973, by rfl⟩ : syracuseStep 170631 = 255947) B255947
theorem B170639 : Blo 167798 170639 := bstep (se 1 (by rfl) ⟨127979, by rfl⟩ : syracuseStep 170639 = 255959) B255959
theorem B170683 : Blo 167798 170683 := bstep (se 1 (by rfl) ⟨128012, by rfl⟩ : syracuseStep 170683 = 256025) B256025
theorem B170759 : Blo 167798 170759 := bstep (se 1 (by rfl) ⟨128069, by rfl⟩ : syracuseStep 170759 = 256139) B256139
theorem B170767 : Blo 167798 170767 := bstep (se 1 (by rfl) ⟨128075, by rfl⟩ : syracuseStep 170767 = 256151) B256151
theorem B170811 : Blo 167798 170811 := bstep (se 1 (by rfl) ⟨128108, by rfl⟩ : syracuseStep 170811 = 256217) B256217
theorem B170887 : Blo 167798 170887 := bstep (se 1 (by rfl) ⟨128165, by rfl⟩ : syracuseStep 170887 = 256331) B256331
theorem B170895 : Blo 167798 170895 := bstep (se 1 (by rfl) ⟨128171, by rfl⟩ : syracuseStep 170895 = 256343) B256343
theorem B170939 : Blo 167798 170939 := bstep (se 1 (by rfl) ⟨128204, by rfl⟩ : syracuseStep 170939 = 256409) B256409
theorem B433097 : Blo 167798 433097 := bstep (se 2 (by rfl) ⟨162411, by rfl⟩ : syracuseStep 433097 = 324823) B324823
theorem B171015 : Blo 167798 171015 := bstep (se 1 (by rfl) ⟨128261, by rfl⟩ : syracuseStep 171015 = 256523) B256523
theorem B171023 : Blo 167798 171023 := bstep (se 1 (by rfl) ⟨128267, by rfl⟩ : syracuseStep 171023 = 256535) B256535
theorem B171067 : Blo 167798 171067 := bstep (se 1 (by rfl) ⟨128300, by rfl⟩ : syracuseStep 171067 = 256601) B256601
theorem B1940597 : Blo 167798 1940597 := bstep (se 5 (by rfl) ⟨90965, by rfl⟩ : syracuseStep 1940597 = 181931) B181931
theorem B171143 : Blo 167798 171143 := bstep (se 1 (by rfl) ⟨128357, by rfl⟩ : syracuseStep 171143 = 256715) B256715
theorem B171151 : Blo 167798 171151 := bstep (se 1 (by rfl) ⟨128363, by rfl⟩ : syracuseStep 171151 = 256727) B256727
theorem B171195 : Blo 167798 171195 := bstep (se 1 (by rfl) ⟨128396, by rfl⟩ : syracuseStep 171195 = 256793) B256793
theorem B1449161 : Blo 167798 1449161 := bstep (se 2 (by rfl) ⟨543435, by rfl⟩ : syracuseStep 1449161 = 1086871) B1086871
theorem B171271 : Blo 167798 171271 := bstep (se 1 (by rfl) ⟨128453, by rfl⟩ : syracuseStep 171271 = 256907) B256907
theorem B171279 : Blo 167798 171279 := bstep (se 1 (by rfl) ⟨128459, by rfl⟩ : syracuseStep 171279 = 256919) B256919
theorem B433451 : Blo 167798 433451 := bstep (se 1 (by rfl) ⟨325088, by rfl⟩ : syracuseStep 433451 = 650177) B650177
theorem B171323 : Blo 167798 171323 := bstep (se 1 (by rfl) ⟨128492, by rfl⟩ : syracuseStep 171323 = 256985) B256985
theorem B171399 : Blo 167798 171399 := bstep (se 1 (by rfl) ⟨128549, by rfl⟩ : syracuseStep 171399 = 257099) B257099
theorem B171407 : Blo 167798 171407 := bstep (se 1 (by rfl) ⟨128555, by rfl⟩ : syracuseStep 171407 = 257111) B257111
theorem B171451 : Blo 167798 171451 := bstep (se 1 (by rfl) ⟨128588, by rfl⟩ : syracuseStep 171451 = 257177) B257177
theorem B2891213 : Blo 167798 2891213 := bstep (se 3 (by rfl) ⟨542102, by rfl⟩ : syracuseStep 2891213 = 1084205) B1084205
theorem B171527 : Blo 167798 171527 := bstep (se 1 (by rfl) ⟨128645, by rfl⟩ : syracuseStep 171527 = 257291) B257291
theorem B171535 : Blo 167798 171535 := bstep (se 1 (by rfl) ⟨128651, by rfl⟩ : syracuseStep 171535 = 257303) B257303
theorem B269867 : Blo 167798 269867 := bstep (se 1 (by rfl) ⟨202400, by rfl⟩ : syracuseStep 269867 = 404801) B404801
theorem B171579 : Blo 167798 171579 := bstep (se 1 (by rfl) ⟨128684, by rfl⟩ : syracuseStep 171579 = 257369) B257369
theorem B5283427 : Blo 167798 5283427 := bstep (se 1 (by rfl) ⟨3962570, by rfl⟩ : syracuseStep 5283427 = 7925141) B7925141
theorem B171655 : Blo 167798 171655 := bstep (se 1 (by rfl) ⟨128741, by rfl⟩ : syracuseStep 171655 = 257483) B257483
theorem B171663 : Blo 167798 171663 := bstep (se 1 (by rfl) ⟨128747, by rfl⟩ : syracuseStep 171663 = 257495) B257495
theorem B171707 : Blo 167798 171707 := bstep (se 1 (by rfl) ⟨128780, by rfl⟩ : syracuseStep 171707 = 257561) B257561
theorem B171783 : Blo 167798 171783 := bstep (se 1 (by rfl) ⟨128837, by rfl⟩ : syracuseStep 171783 = 257675) B257675
theorem B171791 : Blo 167798 171791 := bstep (se 1 (by rfl) ⟨128843, by rfl⟩ : syracuseStep 171791 = 257687) B257687
theorem B860057 : Blo 167798 860057 := bstep (se 2 (by rfl) ⟨322521, by rfl⟩ : syracuseStep 860057 = 645043) B645043
theorem B434443 : Blo 167798 434443 := bstep (se 1 (by rfl) ⟨325832, by rfl⟩ : syracuseStep 434443 = 651665) B651665
theorem B1646993 : Blo 167798 1646993 := bstep (se 2 (by rfl) ⟨617622, by rfl⟩ : syracuseStep 1646993 = 1235245) B1235245
theorem B434585 : Blo 167798 434585 := bstep (se 2 (by rfl) ⟨162969, by rfl⟩ : syracuseStep 434585 = 325939) B325939
theorem B958999 : Blo 167798 958999 := bstep (se 1 (by rfl) ⟨719249, by rfl⟩ : syracuseStep 958999 = 1438499) B1438499
theorem B434747 : Blo 167798 434747 := bstep (se 1 (by rfl) ⟨326060, by rfl⟩ : syracuseStep 434747 = 652121) B652121
theorem B1286927 : Blo 167798 1286927 := bstep (se 1 (by rfl) ⟨965195, by rfl⟩ : syracuseStep 1286927 = 1930391) B1930391
theorem B1320137 : Blo 167798 1320137 := bstep (se 2 (by rfl) ⟨495051, by rfl⟩ : syracuseStep 1320137 = 990103) B990103
theorem B1615085 : Blo 167798 1615085 := bstep (se 3 (by rfl) ⟨302828, by rfl⟩ : syracuseStep 1615085 = 605657) B605657
theorem B566675 : Blo 167798 566675 := bstep (se 1 (by rfl) ⟨425006, by rfl⟩ : syracuseStep 566675 = 850013) B850013
theorem B435755 : Blo 167798 435755 := bstep (se 1 (by rfl) ⟨326816, by rfl⟩ : syracuseStep 435755 = 653633) B653633
theorem B1681075 : Blo 167798 1681075 := bstep (se 1 (by rfl) ⟨1260806, by rfl⟩ : syracuseStep 1681075 = 2521613) B2521613
theorem B1025939 : Blo 167798 1025939 := bstep (se 1 (by rfl) ⟨769454, by rfl⟩ : syracuseStep 1025939 = 1538909) B1538909
theorem B239545 : Blo 167798 239545 := bstep (se 2 (by rfl) ⟨89829, by rfl⟩ : syracuseStep 239545 = 179659) B179659
theorem B2173331 : Blo 167798 2173331 := bstep (se 1 (by rfl) ⟨1629998, by rfl⟩ : syracuseStep 2173331 = 3259997) B3259997
theorem B862649 : Blo 167798 862649 := bstep (se 2 (by rfl) ⟨323493, by rfl⟩ : syracuseStep 862649 = 646987) B646987
theorem B568079 : Blo 167798 568079 := bstep (se 1 (by rfl) ⟨426059, by rfl⟩ : syracuseStep 568079 = 852119) B852119
theorem B961415 : Blo 167798 961415 := bstep (se 1 (by rfl) ⟨721061, by rfl⟩ : syracuseStep 961415 = 1442123) B1442123
theorem B568349 : Blo 167798 568349 := bstep (se 3 (by rfl) ⟨106565, by rfl⟩ : syracuseStep 568349 = 213131) B213131
theorem B699479 : Blo 167798 699479 := bstep (se 1 (by rfl) ⟨524609, by rfl⟩ : syracuseStep 699479 = 1049219) B1049219
theorem B248491405 : Blo 167798 248491405 := bstep (se 3 (by rfl) ⟨46592138, by rfl⟩ : syracuseStep 248491405 = 93184277) B93184277
theorem B3124813 : Blo 167798 3124813 := bstep (se 3 (by rfl) ⟨585902, by rfl⟩ : syracuseStep 3124813 = 1171805) B1171805
theorem B863945 : Blo 167798 863945 := bstep (se 2 (by rfl) ⟨323979, by rfl⟩ : syracuseStep 863945 = 647959) B647959
theorem B1388677 : Blo 167798 1388677 := bstep (se 4 (by rfl) ⟨130188, by rfl⟩ : syracuseStep 1388677 = 260377) B260377
theorem B2961677 : Blo 167798 2961677 := bstep (se 3 (by rfl) ⟨555314, by rfl⟩ : syracuseStep 2961677 = 1110629) B1110629
theorem B733499 : Blo 167798 733499 := bstep (se 1 (by rfl) ⟨550124, by rfl⟩ : syracuseStep 733499 = 1100249) B1100249
theorem B569753 : Blo 167798 569753 := bstep (se 2 (by rfl) ⟨213657, by rfl⟩ : syracuseStep 569753 = 427315) B427315
theorem B963191 : Blo 167798 963191 := bstep (se 1 (by rfl) ⟨722393, by rfl⟩ : syracuseStep 963191 = 1444787) B1444787
theorem B242347 : Blo 167798 242347 := bstep (se 1 (by rfl) ⟨181760, by rfl⟩ : syracuseStep 242347 = 363521) B363521
theorem B570455 : Blo 167798 570455 := bstep (se 1 (by rfl) ⟨427841, by rfl⟩ : syracuseStep 570455 = 855683) B855683
theorem B767177 : Blo 167798 767177 := bstep (se 2 (by rfl) ⟨287691, by rfl⟩ : syracuseStep 767177 = 575383) B575383
theorem B439553 : Blo 167798 439553 := bstep (se 2 (by rfl) ⟨164832, by rfl⟩ : syracuseStep 439553 = 329665) B329665
theorem B963899 : Blo 167798 963899 := bstep (se 1 (by rfl) ⟨722924, by rfl⟩ : syracuseStep 963899 = 1445849) B1445849
theorem B308627 : Blo 167798 308627 := bstep (se 1 (by rfl) ⟨231470, by rfl⟩ : syracuseStep 308627 = 462941) B462941
theorem B2635217 : Blo 167798 2635217 := bstep (se 2 (by rfl) ⟨988206, by rfl⟩ : syracuseStep 2635217 = 1976413) B1976413
theorem B570941 : Blo 167798 570941 := bstep (se 3 (by rfl) ⟨107051, by rfl⟩ : syracuseStep 570941 = 214103) B214103
theorem B308855 : Blo 167798 308855 := bstep (se 1 (by rfl) ⟨231641, by rfl⟩ : syracuseStep 308855 = 463283) B463283
theorem B2471755 : Blo 167798 2471755 := bstep (se 1 (by rfl) ⟨1853816, by rfl⟩ : syracuseStep 2471755 = 3707633) B3707633
theorem B407443 : Blo 167798 407443 := bstep (se 1 (by rfl) ⟨305582, by rfl⟩ : syracuseStep 407443 = 611165) B611165
theorem B12564497 : Blo 167798 12564497 := bstep (se 2 (by rfl) ⟨4711686, by rfl⟩ : syracuseStep 12564497 = 9423373) B9423373
theorem B309367 : Blo 167798 309367 := bstep (se 1 (by rfl) ⟨232025, by rfl⟩ : syracuseStep 309367 = 464051) B464051
theorem B538913 : Blo 167798 538913 := bstep (se 2 (by rfl) ⟨202092, by rfl⟩ : syracuseStep 538913 = 404185) B404185
theorem B965357 : Blo 167798 965357 := bstep (se 3 (by rfl) ⟨181004, by rfl⟩ : syracuseStep 965357 = 362009) B362009
theorem B1620773 : Blo 167798 1620773 := bstep (se 4 (by rfl) ⟨151947, by rfl⟩ : syracuseStep 1620773 = 303895) B303895
theorem B1915811 : Blo 167798 1915811 := bstep (se 1 (by rfl) ⟨1436858, by rfl⟩ : syracuseStep 1915811 = 2873717) B2873717
theorem B572345 : Blo 167798 572345 := bstep (se 2 (by rfl) ⟨214629, by rfl⟩ : syracuseStep 572345 = 429259) B429259
theorem B408577 : Blo 167798 408577 := bstep (se 2 (by rfl) ⟨153216, by rfl⟩ : syracuseStep 408577 = 306433) B306433
theorem B277705 : Blo 167798 277705 := bstep (se 2 (by rfl) ⟨104139, by rfl⟩ : syracuseStep 277705 = 208279) B208279
theorem B1555847 : Blo 167798 1555847 := bstep (se 1 (by rfl) ⟨1166885, by rfl⟩ : syracuseStep 1555847 = 2333771) B2333771
theorem B1752455 : Blo 167798 1752455 := bstep (se 1 (by rfl) ⟨1314341, by rfl⟩ : syracuseStep 1752455 = 2628683) B2628683
theorem B572939 : Blo 167798 572939 := bstep (se 1 (by rfl) ⟨429704, by rfl⟩ : syracuseStep 572939 = 859409) B859409
theorem B212539 : Blo 167798 212539 := bstep (se 1 (by rfl) ⟨159404, by rfl⟩ : syracuseStep 212539 = 318809) B318809
theorem B573047 : Blo 167798 573047 := bstep (se 1 (by rfl) ⟨429785, by rfl⟩ : syracuseStep 573047 = 859571) B859571
theorem B1097509 : Blo 167798 1097509 := bstep (se 4 (by rfl) ⟨102891, by rfl⟩ : syracuseStep 1097509 = 205783) B205783
theorem B933767 : Blo 167798 933767 := bstep (se 1 (by rfl) ⟨700325, by rfl⟩ : syracuseStep 933767 = 1400651) B1400651
theorem B573641 : Blo 167798 573641 := bstep (se 2 (by rfl) ⟨215115, by rfl⟩ : syracuseStep 573641 = 430231) B430231
theorem B180667 : Blo 167798 180667 := bstep (se 1 (by rfl) ⟨135500, by rfl⟩ : syracuseStep 180667 = 271001) B271001
theorem B213511 : Blo 167798 213511 := bstep (se 1 (by rfl) ⟨160133, by rfl⟩ : syracuseStep 213511 = 320267) B320267
theorem B2441771 : Blo 167798 2441771 := bstep (se 1 (by rfl) ⟨1831328, by rfl⟩ : syracuseStep 2441771 = 3662657) B3662657
theorem B574343 : Blo 167798 574343 := bstep (se 1 (by rfl) ⟨430757, by rfl⟩ : syracuseStep 574343 = 861515) B861515
theorem B377747 : Blo 167798 377747 := bstep (se 1 (by rfl) ⟨283310, by rfl⟩ : syracuseStep 377747 = 566621) B566621
theorem B213931 : Blo 167798 213931 := bstep (se 1 (by rfl) ⟨160448, by rfl⟩ : syracuseStep 213931 = 320897) B320897
theorem B377801 : Blo 167798 377801 := bstep (se 2 (by rfl) ⟨141675, by rfl⟩ : syracuseStep 377801 = 283351) B283351
theorem B967747 : Blo 167798 967747 := bstep (se 1 (by rfl) ⟨725810, by rfl⟩ : syracuseStep 967747 = 1451621) B1451621
theorem B214159 : Blo 167798 214159 := bstep (se 1 (by rfl) ⟨160619, by rfl⟩ : syracuseStep 214159 = 321239) B321239
theorem B574721 : Blo 167798 574721 := bstep (se 2 (by rfl) ⟨215520, by rfl⟩ : syracuseStep 574721 = 431041) B431041
theorem B1295675 : Blo 167798 1295675 := bstep (se 1 (by rfl) ⟨971756, by rfl⟩ : syracuseStep 1295675 = 1943513) B1943513
theorem B509455 : Blo 167798 509455 := bstep (se 1 (by rfl) ⟨382091, by rfl⟩ : syracuseStep 509455 = 764183) B764183
theorem B378503 : Blo 167798 378503 := bstep (se 1 (by rfl) ⟨283877, by rfl⟩ : syracuseStep 378503 = 567755) B567755
theorem B378683 : Blo 167798 378683 := bstep (se 1 (by rfl) ⟨284012, by rfl⟩ : syracuseStep 378683 = 568025) B568025
theorem B214903 : Blo 167798 214903 := bstep (se 1 (by rfl) ⟨161177, by rfl⟩ : syracuseStep 214903 = 322355) B322355
theorem B378809 : Blo 167798 378809 := bstep (se 2 (by rfl) ⟨142053, by rfl⟩ : syracuseStep 378809 = 284107) B284107
theorem B575531 : Blo 167798 575531 := bstep (se 1 (by rfl) ⟨431648, by rfl⟩ : syracuseStep 575531 = 863297) B863297
theorem B215227 : Blo 167798 215227 := bstep (se 1 (by rfl) ⟨161420, by rfl⟩ : syracuseStep 215227 = 322841) B322841
theorem B379151 : Blo 167798 379151 := bstep (se 1 (by rfl) ⟨284363, by rfl⟩ : syracuseStep 379151 = 568727) B568727
theorem B379169 : Blo 167798 379169 := bstep (se 2 (by rfl) ⟨142188, by rfl⟩ : syracuseStep 379169 = 284377) B284377
theorem B379511 : Blo 167798 379511 := bstep (se 1 (by rfl) ⟨284633, by rfl⟩ : syracuseStep 379511 = 569267) B569267
theorem B215723 : Blo 167798 215723 := bstep (se 1 (by rfl) ⟨161792, by rfl⟩ : syracuseStep 215723 = 323585) B323585
theorem B183055 : Blo 167798 183055 := bstep (se 1 (by rfl) ⟨137291, by rfl⟩ : syracuseStep 183055 = 274583) B274583
theorem B379691 : Blo 167798 379691 := bstep (se 1 (by rfl) ⟨284768, by rfl⟩ : syracuseStep 379691 = 569537) B569537
theorem B510781 : Blo 167798 510781 := bstep (se 3 (by rfl) ⟨95771, by rfl⟩ : syracuseStep 510781 = 191543) B191543
theorem B641945 : Blo 167798 641945 := bstep (se 2 (by rfl) ⟨240729, by rfl⟩ : syracuseStep 641945 = 481459) B481459
theorem B969731 : Blo 167798 969731 := bstep (se 1 (by rfl) ⟨727298, by rfl⟩ : syracuseStep 969731 = 1454597) B1454597
theorem B216199 : Blo 167798 216199 := bstep (se 1 (by rfl) ⟨162149, by rfl⟩ : syracuseStep 216199 = 324299) B324299
theorem B183431 : Blo 167798 183431 := bstep (se 1 (by rfl) ⟨137573, by rfl⟩ : syracuseStep 183431 = 275147) B275147
theorem B380051 : Blo 167798 380051 := bstep (se 1 (by rfl) ⟨285038, by rfl⟩ : syracuseStep 380051 = 570077) B570077
theorem B478361 : Blo 167798 478361 := bstep (se 2 (by rfl) ⟨179385, by rfl⟩ : syracuseStep 478361 = 358771) B358771
theorem B380105 : Blo 167798 380105 := bstep (se 2 (by rfl) ⟨142539, by rfl⟩ : syracuseStep 380105 = 285079) B285079
theorem B609551 : Blo 167798 609551 := bstep (se 1 (by rfl) ⟨457163, by rfl⟩ : syracuseStep 609551 = 914327) B914327
theorem B576827 : Blo 167798 576827 := bstep (se 1 (by rfl) ⟨432620, by rfl⟩ : syracuseStep 576827 = 865241) B865241
theorem B544153 : Blo 167798 544153 := bstep (se 2 (by rfl) ⟨204057, by rfl⟩ : syracuseStep 544153 = 408115) B408115
theorem B740983 : Blo 167798 740983 := bstep (se 1 (by rfl) ⟨555737, by rfl⟩ : syracuseStep 740983 = 1111475) B1111475
theorem B216695 : Blo 167798 216695 := bstep (se 1 (by rfl) ⟨162521, by rfl⟩ : syracuseStep 216695 = 325043) B325043
theorem B216847 : Blo 167798 216847 := bstep (se 1 (by rfl) ⟨162635, by rfl⟩ : syracuseStep 216847 = 325271) B325271
theorem B577313 : Blo 167798 577313 := bstep (se 2 (by rfl) ⟨216492, by rfl⟩ : syracuseStep 577313 = 432985) B432985
theorem B380807 : Blo 167798 380807 := bstep (se 1 (by rfl) ⟨285605, by rfl⟩ : syracuseStep 380807 = 571211) B571211
theorem B217019 : Blo 167798 217019 := bstep (se 1 (by rfl) ⟨162764, by rfl⟩ : syracuseStep 217019 = 325529) B325529
theorem B1462283 : Blo 167798 1462283 := bstep (se 1 (by rfl) ⟨1096712, by rfl⟩ : syracuseStep 1462283 = 2193425) B2193425
theorem B380987 : Blo 167798 380987 := bstep (se 1 (by rfl) ⟨285740, by rfl⟩ : syracuseStep 380987 = 571481) B571481
theorem B381113 : Blo 167798 381113 := bstep (se 2 (by rfl) ⟨142917, by rfl⟩ : syracuseStep 381113 = 285835) B285835
theorem B577907 : Blo 167798 577907 := bstep (se 1 (by rfl) ⟨433430, by rfl⟩ : syracuseStep 577907 = 866861) B866861
theorem B807353 : Blo 167798 807353 := bstep (se 2 (by rfl) ⟨302757, by rfl⟩ : syracuseStep 807353 = 605515) B605515
theorem B381455 : Blo 167798 381455 := bstep (se 1 (by rfl) ⟨286091, by rfl⟩ : syracuseStep 381455 = 572183) B572183
theorem B479773 : Blo 167798 479773 := bstep (se 3 (by rfl) ⟨89957, by rfl⟩ : syracuseStep 479773 = 179915) B179915
theorem B381473 : Blo 167798 381473 := bstep (se 2 (by rfl) ⟨143052, by rfl⟩ : syracuseStep 381473 = 286105) B286105
theorem B479945 : Blo 167798 479945 := bstep (se 2 (by rfl) ⟨179979, by rfl⟩ : syracuseStep 479945 = 359959) B359959
theorem B480001 : Blo 167798 480001 := bstep (se 2 (by rfl) ⟨180000, by rfl⟩ : syracuseStep 480001 = 360001) B360001
theorem B381815 : Blo 167798 381815 := bstep (se 1 (by rfl) ⟨286361, by rfl⟩ : syracuseStep 381815 = 572723) B572723
theorem B381995 : Blo 167798 381995 := bstep (se 1 (by rfl) ⟨286496, by rfl⟩ : syracuseStep 381995 = 572993) B572993
theorem B480343 : Blo 167798 480343 := bstep (se 1 (by rfl) ⟨360257, by rfl⟩ : syracuseStep 480343 = 720515) B720515
theorem B283783 : Blo 167798 283783 := bstep (se 1 (by rfl) ⟨212837, by rfl⟩ : syracuseStep 283783 = 425675) B425675
theorem B972121 : Blo 167798 972121 := bstep (se 2 (by rfl) ⟨364545, by rfl⟩ : syracuseStep 972121 = 729091) B729091
theorem B382355 : Blo 167798 382355 := bstep (se 1 (by rfl) ⟨286766, by rfl⟩ : syracuseStep 382355 = 573533) B573533
theorem B382409 : Blo 167798 382409 := bstep (se 2 (by rfl) ⟨143403, by rfl⟩ : syracuseStep 382409 = 286807) B286807
theorem B284431 : Blo 167798 284431 := bstep (se 1 (by rfl) ⟨213323, by rfl⟩ : syracuseStep 284431 = 426647) B426647
theorem B251705 : Blo 167798 251705 := bstep (se 2 (by rfl) ⟨94389, by rfl⟩ : syracuseStep 251705 = 188779) B188779
theorem B251783 : Blo 167798 251783 := bstep (se 1 (by rfl) ⟨188837, by rfl⟩ : syracuseStep 251783 = 377675) B377675
theorem B1464227 : Blo 167798 1464227 := bstep (se 1 (by rfl) ⟨1098170, by rfl⟩ : syracuseStep 1464227 = 2196341) B2196341
theorem B251819 : Blo 167798 251819 := bstep (se 1 (by rfl) ⟨188864, by rfl⟩ : syracuseStep 251819 = 377729) B377729
theorem B251849 : Blo 167798 251849 := bstep (se 2 (by rfl) ⟨94443, by rfl⟩ : syracuseStep 251849 = 188887) B188887
theorem B1038347 : Blo 167798 1038347 := bstep (se 1 (by rfl) ⟨778760, by rfl⟩ : syracuseStep 1038347 = 1557521) B1557521
theorem B809003 : Blo 167798 809003 := bstep (se 1 (by rfl) ⟨606752, by rfl⟩ : syracuseStep 809003 = 1213505) B1213505
theorem B251963 : Blo 167798 251963 := bstep (se 1 (by rfl) ⟨188972, by rfl⟩ : syracuseStep 251963 = 377945) B377945
theorem B252023 : Blo 167798 252023 := bstep (se 1 (by rfl) ⟨189017, by rfl⟩ : syracuseStep 252023 = 378035) B378035
theorem B383111 : Blo 167798 383111 := bstep (se 1 (by rfl) ⟨287333, by rfl⟩ : syracuseStep 383111 = 574667) B574667
theorem B252047 : Blo 167798 252047 := bstep (se 1 (by rfl) ⟨189035, by rfl⟩ : syracuseStep 252047 = 378071) B378071
theorem B252089 : Blo 167798 252089 := bstep (se 2 (by rfl) ⟨94533, by rfl⟩ : syracuseStep 252089 = 189067) B189067
theorem B252167 : Blo 167798 252167 := bstep (se 1 (by rfl) ⟨189125, by rfl⟩ : syracuseStep 252167 = 378251) B378251
theorem B612623 : Blo 167798 612623 := bstep (se 1 (by rfl) ⟨459467, by rfl⟩ : syracuseStep 612623 = 918935) B918935
theorem B252203 : Blo 167798 252203 := bstep (se 1 (by rfl) ⟨189152, by rfl⟩ : syracuseStep 252203 = 378305) B378305
theorem B284971 : Blo 167798 284971 := bstep (se 1 (by rfl) ⟨213728, by rfl⟩ : syracuseStep 284971 = 427457) B427457
theorem B383291 : Blo 167798 383291 := bstep (se 1 (by rfl) ⟨287468, by rfl⟩ : syracuseStep 383291 = 574937) B574937
theorem B252233 : Blo 167798 252233 := bstep (se 2 (by rfl) ⟨94587, by rfl⟩ : syracuseStep 252233 = 189175) B189175
theorem B809351 : Blo 167798 809351 := bstep (se 1 (by rfl) ⟨607013, by rfl⟩ : syracuseStep 809351 = 1214027) B1214027
theorem B645529 : Blo 167798 645529 := bstep (se 2 (by rfl) ⟨242073, by rfl⟩ : syracuseStep 645529 = 484147) B484147
theorem B285113 : Blo 167798 285113 := bstep (se 2 (by rfl) ⟨106917, by rfl⟩ : syracuseStep 285113 = 213835) B213835
theorem B383417 : Blo 167798 383417 := bstep (se 2 (by rfl) ⟨143781, by rfl⟩ : syracuseStep 383417 = 287563) B287563
theorem B252347 : Blo 167798 252347 := bstep (se 1 (by rfl) ⟨189260, by rfl⟩ : syracuseStep 252347 = 378521) B378521
theorem B252407 : Blo 167798 252407 := bstep (se 1 (by rfl) ⟨189305, by rfl⟩ : syracuseStep 252407 = 378611) B378611
theorem B252431 : Blo 167798 252431 := bstep (se 1 (by rfl) ⟨189323, by rfl⟩ : syracuseStep 252431 = 378647) B378647
theorem B1301021 : Blo 167798 1301021 := bstep (se 3 (by rfl) ⟨243941, by rfl⟩ : syracuseStep 1301021 = 487883) B487883
theorem B252473 : Blo 167798 252473 := bstep (se 2 (by rfl) ⟨94677, by rfl⟩ : syracuseStep 252473 = 189355) B189355
theorem B252551 : Blo 167798 252551 := bstep (se 1 (by rfl) ⟨189413, by rfl⟩ : syracuseStep 252551 = 378827) B378827
theorem B252587 : Blo 167798 252587 := bstep (se 1 (by rfl) ⟨189440, by rfl⟩ : syracuseStep 252587 = 378881) B378881
theorem B252617 : Blo 167798 252617 := bstep (se 2 (by rfl) ⟨94731, by rfl⟩ : syracuseStep 252617 = 189463) B189463
theorem B645833 : Blo 167798 645833 := bstep (se 2 (by rfl) ⟨242187, by rfl⟩ : syracuseStep 645833 = 484375) B484375
theorem B383759 : Blo 167798 383759 := bstep (se 1 (by rfl) ⟨287819, by rfl⟩ : syracuseStep 383759 = 575639) B575639
theorem B383777 : Blo 167798 383777 := bstep (se 2 (by rfl) ⟨143916, by rfl⟩ : syracuseStep 383777 = 287833) B287833
theorem B252731 : Blo 167798 252731 := bstep (se 1 (by rfl) ⟨189548, by rfl⟩ : syracuseStep 252731 = 379097) B379097
theorem B252791 : Blo 167798 252791 := bstep (se 1 (by rfl) ⟨189593, by rfl⟩ : syracuseStep 252791 = 379187) B379187
theorem B252815 : Blo 167798 252815 := bstep (se 1 (by rfl) ⟨189611, by rfl⟩ : syracuseStep 252815 = 379223) B379223
theorem B252857 : Blo 167798 252857 := bstep (se 2 (by rfl) ⟨94821, by rfl⟩ : syracuseStep 252857 = 189643) B189643
theorem B252935 : Blo 167798 252935 := bstep (se 1 (by rfl) ⟨189701, by rfl⟩ : syracuseStep 252935 = 379403) B379403
theorem B973853 : Blo 167798 973853 := bstep (se 3 (by rfl) ⟨182597, by rfl⟩ : syracuseStep 973853 = 365195) B365195
theorem B252971 : Blo 167798 252971 := bstep (se 1 (by rfl) ⟨189728, by rfl⟩ : syracuseStep 252971 = 379457) B379457
theorem B253001 : Blo 167798 253001 := bstep (se 2 (by rfl) ⟨94875, by rfl⟩ : syracuseStep 253001 = 189751) B189751
theorem B285815 : Blo 167798 285815 := bstep (se 1 (by rfl) ⟨214361, by rfl⟩ : syracuseStep 285815 = 428723) B428723
theorem B384119 : Blo 167798 384119 := bstep (se 1 (by rfl) ⟨288089, by rfl⟩ : syracuseStep 384119 = 576179) B576179
theorem B318649 : Blo 167798 318649 := bstep (se 2 (by rfl) ⟨119493, by rfl⟩ : syracuseStep 318649 = 238987) B238987
theorem B253115 : Blo 167798 253115 := bstep (se 1 (by rfl) ⟨189836, by rfl⟩ : syracuseStep 253115 = 379673) B379673
theorem B253175 : Blo 167798 253175 := bstep (se 1 (by rfl) ⟨189881, by rfl⟩ : syracuseStep 253175 = 379763) B379763
theorem B253199 : Blo 167798 253199 := bstep (se 1 (by rfl) ⟨189899, by rfl⟩ : syracuseStep 253199 = 379799) B379799
theorem B384299 : Blo 167798 384299 := bstep (se 1 (by rfl) ⟨288224, by rfl⟩ : syracuseStep 384299 = 576449) B576449
theorem B253241 : Blo 167798 253241 := bstep (se 2 (by rfl) ⟨94965, by rfl⟩ : syracuseStep 253241 = 189931) B189931
theorem B253319 : Blo 167798 253319 := bstep (se 1 (by rfl) ⟨189989, by rfl⟩ : syracuseStep 253319 = 379979) B379979
theorem B253355 : Blo 167798 253355 := bstep (se 1 (by rfl) ⟨190016, by rfl⟩ : syracuseStep 253355 = 380033) B380033
theorem B253385 : Blo 167798 253385 := bstep (se 2 (by rfl) ⟨95019, by rfl⟩ : syracuseStep 253385 = 190039) B190039
theorem B318991 : Blo 167798 318991 := bstep (se 1 (by rfl) ⟨239243, by rfl⟩ : syracuseStep 318991 = 478487) B478487
theorem B384545 : Blo 167798 384545 := bstep (se 2 (by rfl) ⟨144204, by rfl⟩ : syracuseStep 384545 = 288409) B288409
theorem B253499 : Blo 167798 253499 := bstep (se 1 (by rfl) ⟨190124, by rfl⟩ : syracuseStep 253499 = 380249) B380249
theorem B286267 : Blo 167798 286267 := bstep (se 1 (by rfl) ⟨214700, by rfl⟩ : syracuseStep 286267 = 429401) B429401
theorem B253559 : Blo 167798 253559 := bstep (se 1 (by rfl) ⟨190169, by rfl⟩ : syracuseStep 253559 = 380339) B380339
theorem B646775 : Blo 167798 646775 := bstep (se 1 (by rfl) ⟨485081, by rfl⟩ : syracuseStep 646775 = 970163) B970163
theorem B253583 : Blo 167798 253583 := bstep (se 1 (by rfl) ⟨190187, by rfl⟩ : syracuseStep 253583 = 380375) B380375
theorem B384659 : Blo 167798 384659 := bstep (se 1 (by rfl) ⟨288494, by rfl⟩ : syracuseStep 384659 = 576989) B576989
theorem B2612915 : Blo 167798 2612915 := bstep (se 1 (by rfl) ⟨1959686, by rfl⟩ : syracuseStep 2612915 = 3919373) B3919373
theorem B253625 : Blo 167798 253625 := bstep (se 2 (by rfl) ⟨95109, by rfl⟩ : syracuseStep 253625 = 190219) B190219
theorem B286409 : Blo 167798 286409 := bstep (se 2 (by rfl) ⟨107403, by rfl⟩ : syracuseStep 286409 = 214807) B214807
theorem B384713 : Blo 167798 384713 := bstep (se 2 (by rfl) ⟨144267, by rfl⟩ : syracuseStep 384713 = 288535) B288535
theorem B974537 : Blo 167798 974537 := bstep (se 2 (by rfl) ⟨365451, by rfl⟩ : syracuseStep 974537 = 730903) B730903
theorem B253703 : Blo 167798 253703 := bstep (se 1 (by rfl) ⟨190277, by rfl⟩ : syracuseStep 253703 = 380555) B380555
theorem B253739 : Blo 167798 253739 := bstep (se 1 (by rfl) ⟨190304, by rfl⟩ : syracuseStep 253739 = 380609) B380609
theorem B253769 : Blo 167798 253769 := bstep (se 2 (by rfl) ⟨95163, by rfl⟩ : syracuseStep 253769 = 190327) B190327
theorem B483191 : Blo 167798 483191 := bstep (se 1 (by rfl) ⟨362393, by rfl⟩ : syracuseStep 483191 = 724787) B724787
theorem B253883 : Blo 167798 253883 := bstep (se 1 (by rfl) ⟨190412, by rfl⟩ : syracuseStep 253883 = 380825) B380825
theorem B253943 : Blo 167798 253943 := bstep (se 1 (by rfl) ⟨190457, by rfl⟩ : syracuseStep 253943 = 380915) B380915
theorem B253967 : Blo 167798 253967 := bstep (se 1 (by rfl) ⟨190475, by rfl⟩ : syracuseStep 253967 = 380951) B380951
theorem B254009 : Blo 167798 254009 := bstep (se 2 (by rfl) ⟨95253, by rfl⟩ : syracuseStep 254009 = 190507) B190507
theorem B254087 : Blo 167798 254087 := bstep (se 1 (by rfl) ⟨190565, by rfl⟩ : syracuseStep 254087 = 381131) B381131
theorem B254123 : Blo 167798 254123 := bstep (se 1 (by rfl) ⟨190592, by rfl⟩ : syracuseStep 254123 = 381185) B381185
theorem B254153 : Blo 167798 254153 := bstep (se 2 (by rfl) ⟨95307, by rfl⟩ : syracuseStep 254153 = 190615) B190615
theorem B1466657 : Blo 167798 1466657 := bstep (se 2 (by rfl) ⟨549996, by rfl⟩ : syracuseStep 1466657 = 1099993) B1099993
theorem B254267 : Blo 167798 254267 := bstep (se 1 (by rfl) ⟨190700, by rfl⟩ : syracuseStep 254267 = 381401) B381401
theorem B254327 : Blo 167798 254327 := bstep (se 1 (by rfl) ⟨190745, by rfl⟩ : syracuseStep 254327 = 381491) B381491
theorem B319879 : Blo 167798 319879 := bstep (se 1 (by rfl) ⟨239909, by rfl⟩ : syracuseStep 319879 = 479819) B479819
theorem B287111 : Blo 167798 287111 := bstep (se 1 (by rfl) ⟨215333, by rfl⟩ : syracuseStep 287111 = 430667) B430667
theorem B385415 : Blo 167798 385415 := bstep (se 1 (by rfl) ⟨289061, by rfl⟩ : syracuseStep 385415 = 578123) B578123
theorem B188815 : Blo 167798 188815 := bstep (se 1 (by rfl) ⟨141611, by rfl⟩ : syracuseStep 188815 = 283223) B283223
theorem B254351 : Blo 167798 254351 := bstep (se 1 (by rfl) ⟨190763, by rfl⟩ : syracuseStep 254351 = 381527) B381527
theorem B254393 : Blo 167798 254393 := bstep (se 2 (by rfl) ⟨95397, by rfl⟩ : syracuseStep 254393 = 190795) B190795
theorem B254471 : Blo 167798 254471 := bstep (se 1 (by rfl) ⟨190853, by rfl⟩ : syracuseStep 254471 = 381707) B381707
theorem B254507 : Blo 167798 254507 := bstep (se 1 (by rfl) ⟨190880, by rfl⟩ : syracuseStep 254507 = 381761) B381761
theorem B385595 : Blo 167798 385595 := bstep (se 1 (by rfl) ⟨289196, by rfl⟩ : syracuseStep 385595 = 578393) B578393
theorem B647747 : Blo 167798 647747 := bstep (se 1 (by rfl) ⟨485810, by rfl⟩ : syracuseStep 647747 = 971621) B971621
theorem B254537 : Blo 167798 254537 := bstep (se 2 (by rfl) ⟨95451, by rfl⟩ : syracuseStep 254537 = 190903) B190903
theorem B385721 : Blo 167798 385721 := bstep (se 2 (by rfl) ⟨144645, by rfl⟩ : syracuseStep 385721 = 289291) B289291
theorem B254651 : Blo 167798 254651 := bstep (se 1 (by rfl) ⟨190988, by rfl⟩ : syracuseStep 254651 = 381977) B381977
theorem B254711 : Blo 167798 254711 := bstep (se 1 (by rfl) ⟨191033, by rfl⟩ : syracuseStep 254711 = 382067) B382067
theorem B254735 : Blo 167798 254735 := bstep (se 1 (by rfl) ⟨191051, by rfl⟩ : syracuseStep 254735 = 382103) B382103
theorem B254777 : Blo 167798 254777 := bstep (se 2 (by rfl) ⟨95541, by rfl⟩ : syracuseStep 254777 = 191083) B191083
theorem B189319 : Blo 167798 189319 := bstep (se 1 (by rfl) ⟨141989, by rfl⟩ : syracuseStep 189319 = 283979) B283979
theorem B254855 : Blo 167798 254855 := bstep (se 1 (by rfl) ⟨191141, by rfl⟩ : syracuseStep 254855 = 382283) B382283
theorem B254891 : Blo 167798 254891 := bstep (se 1 (by rfl) ⟨191168, by rfl⟩ : syracuseStep 254891 = 382337) B382337
theorem B254921 : Blo 167798 254921 := bstep (se 2 (by rfl) ⟨95595, by rfl⟩ : syracuseStep 254921 = 191191) B191191
theorem B287759 : Blo 167798 287759 := bstep (se 1 (by rfl) ⟨215819, by rfl⟩ : syracuseStep 287759 = 431639) B431639
theorem B386063 : Blo 167798 386063 := bstep (se 1 (by rfl) ⟨289547, by rfl⟩ : syracuseStep 386063 = 579095) B579095
theorem B386081 : Blo 167798 386081 := bstep (se 2 (by rfl) ⟨144780, by rfl⟩ : syracuseStep 386081 = 289561) B289561
theorem B189499 : Blo 167798 189499 := bstep (se 1 (by rfl) ⟨142124, by rfl⟩ : syracuseStep 189499 = 284249) B284249
theorem B255035 : Blo 167798 255035 := bstep (se 1 (by rfl) ⟨191276, by rfl⟩ : syracuseStep 255035 = 382553) B382553
theorem B255095 : Blo 167798 255095 := bstep (se 1 (by rfl) ⟨191321, by rfl⟩ : syracuseStep 255095 = 382643) B382643
theorem B255119 : Blo 167798 255119 := bstep (se 1 (by rfl) ⟨191339, by rfl⟩ : syracuseStep 255119 = 382679) B382679
theorem B255161 : Blo 167798 255161 := bstep (se 2 (by rfl) ⟨95685, by rfl⟩ : syracuseStep 255161 = 191371) B191371
theorem B255239 : Blo 167798 255239 := bstep (se 1 (by rfl) ⟨191429, by rfl⟩ : syracuseStep 255239 = 382859) B382859
theorem B255275 : Blo 167798 255275 := bstep (se 1 (by rfl) ⟨191456, by rfl⟩ : syracuseStep 255275 = 382913) B382913
theorem B255305 : Blo 167798 255305 := bstep (se 2 (by rfl) ⟨95739, by rfl⟩ : syracuseStep 255305 = 191479) B191479
theorem B386423 : Blo 167798 386423 := bstep (se 1 (by rfl) ⟨289817, by rfl⟩ : syracuseStep 386423 = 579635) B579635
theorem B8381875 : Blo 167798 8381875 := bstep (se 1 (by rfl) ⟨6286406, by rfl⟩ : syracuseStep 8381875 = 12572813) B12572813
theorem B976313 : Blo 167798 976313 := bstep (se 2 (by rfl) ⟨366117, by rfl⟩ : syracuseStep 976313 = 732235) B732235
theorem B255419 : Blo 167798 255419 := bstep (se 1 (by rfl) ⟨191564, by rfl⟩ : syracuseStep 255419 = 383129) B383129
theorem B255479 : Blo 167798 255479 := bstep (se 1 (by rfl) ⟨191609, by rfl⟩ : syracuseStep 255479 = 383219) B383219
theorem B189967 : Blo 167798 189967 := bstep (se 1 (by rfl) ⟨142475, by rfl⟩ : syracuseStep 189967 = 284951) B284951
theorem B255503 : Blo 167798 255503 := bstep (se 1 (by rfl) ⟨191627, by rfl⟩ : syracuseStep 255503 = 383255) B383255
theorem B288299 : Blo 167798 288299 := bstep (se 1 (by rfl) ⟨216224, by rfl⟩ : syracuseStep 288299 = 432449) B432449
theorem B255545 : Blo 167798 255545 := bstep (se 2 (by rfl) ⟨95829, by rfl⟩ : syracuseStep 255545 = 191659) B191659
theorem B255623 : Blo 167798 255623 := bstep (se 1 (by rfl) ⟨191717, by rfl⟩ : syracuseStep 255623 = 383435) B383435
theorem B255659 : Blo 167798 255659 := bstep (se 1 (by rfl) ⟨191744, by rfl⟩ : syracuseStep 255659 = 383489) B383489
theorem B648905 : Blo 167798 648905 := bstep (se 2 (by rfl) ⟨243339, by rfl⟩ : syracuseStep 648905 = 486679) B486679
theorem B255689 : Blo 167798 255689 := bstep (se 2 (by rfl) ⟨95883, by rfl⟩ : syracuseStep 255689 = 191767) B191767
theorem B255803 : Blo 167798 255803 := bstep (se 1 (by rfl) ⟨191852, by rfl⟩ : syracuseStep 255803 = 383705) B383705
theorem B255863 : Blo 167798 255863 := bstep (se 1 (by rfl) ⟨191897, by rfl⟩ : syracuseStep 255863 = 383795) B383795
theorem B780167 : Blo 167798 780167 := bstep (se 1 (by rfl) ⟨585125, by rfl⟩ : syracuseStep 780167 = 1170251) B1170251
theorem B255887 : Blo 167798 255887 := bstep (se 1 (by rfl) ⟨191915, by rfl⟩ : syracuseStep 255887 = 383831) B383831
theorem B255929 : Blo 167798 255929 := bstep (se 2 (by rfl) ⟨95973, by rfl⟩ : syracuseStep 255929 = 191947) B191947
theorem B288697 : Blo 167798 288697 := bstep (se 2 (by rfl) ⟨108261, by rfl⟩ : syracuseStep 288697 = 216523) B216523
theorem B190471 : Blo 167798 190471 := bstep (se 1 (by rfl) ⟨142853, by rfl⟩ : syracuseStep 190471 = 285707) B285707
theorem B256007 : Blo 167798 256007 := bstep (se 1 (by rfl) ⟨192005, by rfl⟩ : syracuseStep 256007 = 384011) B384011
theorem B256043 : Blo 167798 256043 := bstep (se 1 (by rfl) ⟨192032, by rfl⟩ : syracuseStep 256043 = 384065) B384065
theorem B256073 : Blo 167798 256073 := bstep (se 2 (by rfl) ⟨96027, by rfl⟩ : syracuseStep 256073 = 192055) B192055
theorem B2189429 : Blo 167798 2189429 := bstep (se 5 (by rfl) ⟨102629, by rfl⟩ : syracuseStep 2189429 = 205259) B205259
theorem B321671 : Blo 167798 321671 := bstep (se 1 (by rfl) ⟨241253, by rfl⟩ : syracuseStep 321671 = 482507) B482507
theorem B190651 : Blo 167798 190651 := bstep (se 1 (by rfl) ⟨142988, by rfl⟩ : syracuseStep 190651 = 285977) B285977
theorem B256187 : Blo 167798 256187 := bstep (se 1 (by rfl) ⟨192140, by rfl⟩ : syracuseStep 256187 = 384281) B384281
theorem B649417 : Blo 167798 649417 := bstep (se 2 (by rfl) ⟨243531, by rfl⟩ : syracuseStep 649417 = 487063) B487063
theorem B256247 : Blo 167798 256247 := bstep (se 1 (by rfl) ⟨192185, by rfl⟩ : syracuseStep 256247 = 384371) B384371
theorem B256271 : Blo 167798 256271 := bstep (se 1 (by rfl) ⟨192203, by rfl⟩ : syracuseStep 256271 = 384407) B384407
theorem B256313 : Blo 167798 256313 := bstep (se 2 (by rfl) ⟨96117, by rfl⟩ : syracuseStep 256313 = 192235) B192235
theorem B1436039 : Blo 167798 1436039 := bstep (se 1 (by rfl) ⟨1077029, by rfl⟩ : syracuseStep 1436039 = 2154059) B2154059
theorem B256391 : Blo 167798 256391 := bstep (se 1 (by rfl) ⟨192293, by rfl⟩ : syracuseStep 256391 = 384587) B384587
theorem B256427 : Blo 167798 256427 := bstep (se 1 (by rfl) ⟨192320, by rfl⟩ : syracuseStep 256427 = 384641) B384641
theorem B616889 : Blo 167798 616889 := bstep (se 2 (by rfl) ⟨231333, by rfl⟩ : syracuseStep 616889 = 462667) B462667
theorem B485833 : Blo 167798 485833 := bstep (se 2 (by rfl) ⟨182187, by rfl⟩ : syracuseStep 485833 = 364375) B364375
theorem B256457 : Blo 167798 256457 := bstep (se 2 (by rfl) ⟨96171, by rfl⟩ : syracuseStep 256457 = 192343) B192343
theorem B256571 : Blo 167798 256571 := bstep (se 1 (by rfl) ⟨192428, by rfl⟩ : syracuseStep 256571 = 384857) B384857
theorem B813655 : Blo 167798 813655 := bstep (se 1 (by rfl) ⟨610241, by rfl⟩ : syracuseStep 813655 = 1220483) B1220483
theorem B256631 : Blo 167798 256631 := bstep (se 1 (by rfl) ⟨192473, by rfl⟩ : syracuseStep 256631 = 384947) B384947
theorem B289399 : Blo 167798 289399 := bstep (se 1 (by rfl) ⟨217049, by rfl⟩ : syracuseStep 289399 = 434099) B434099
theorem B191119 : Blo 167798 191119 := bstep (se 1 (by rfl) ⟨143339, by rfl⟩ : syracuseStep 191119 = 286679) B286679
theorem B256655 : Blo 167798 256655 := bstep (se 1 (by rfl) ⟨192491, by rfl⟩ : syracuseStep 256655 = 384983) B384983
theorem B256697 : Blo 167798 256697 := bstep (se 2 (by rfl) ⟨96261, by rfl⟩ : syracuseStep 256697 = 192523) B192523
theorem B256775 : Blo 167798 256775 := bstep (se 1 (by rfl) ⟨192581, by rfl⟩ : syracuseStep 256775 = 385163) B385163
theorem B59894549 : Blo 167798 59894549 := bstep (se 6 (by rfl) ⟨1403778, by rfl⟩ : syracuseStep 59894549 = 2807557) B2807557
theorem B256811 : Blo 167798 256811 := bstep (se 1 (by rfl) ⟨192608, by rfl⟩ : syracuseStep 256811 = 385217) B385217
theorem B289595 : Blo 167798 289595 := bstep (se 1 (by rfl) ⟨217196, by rfl⟩ : syracuseStep 289595 = 434393) B434393
theorem B256841 : Blo 167798 256841 := bstep (se 2 (by rfl) ⟨96315, by rfl⟩ : syracuseStep 256841 = 192631) B192631
theorem B1370969 : Blo 167798 1370969 := bstep (se 2 (by rfl) ⟨514113, by rfl⟩ : syracuseStep 1370969 = 1028227) B1028227
theorem B256955 : Blo 167798 256955 := bstep (se 1 (by rfl) ⟨192716, by rfl⟩ : syracuseStep 256955 = 385433) B385433
theorem B257015 : Blo 167798 257015 := bstep (se 1 (by rfl) ⟨192761, by rfl⟩ : syracuseStep 257015 = 385523) B385523
theorem B257039 : Blo 167798 257039 := bstep (se 1 (by rfl) ⟨192779, by rfl⟩ : syracuseStep 257039 = 385559) B385559
theorem B257081 : Blo 167798 257081 := bstep (se 2 (by rfl) ⟨96405, by rfl⟩ : syracuseStep 257081 = 192811) B192811
theorem B519229 : Blo 167798 519229 := bstep (se 3 (by rfl) ⟨97355, by rfl⟩ : syracuseStep 519229 = 194711) B194711
theorem B191623 : Blo 167798 191623 := bstep (se 1 (by rfl) ⟨143717, by rfl⟩ : syracuseStep 191623 = 287435) B287435
theorem B257159 : Blo 167798 257159 := bstep (se 1 (by rfl) ⟨192869, by rfl⟩ : syracuseStep 257159 = 385739) B385739
theorem B257195 : Blo 167798 257195 := bstep (se 1 (by rfl) ⟨192896, by rfl⟩ : syracuseStep 257195 = 385793) B385793
theorem B257225 : Blo 167798 257225 := bstep (se 2 (by rfl) ⟨96459, by rfl⟩ : syracuseStep 257225 = 192919) B192919
theorem B978227 : Blo 167798 978227 := bstep (se 1 (by rfl) ⟨733670, by rfl⟩ : syracuseStep 978227 = 1467341) B1467341
theorem B191803 : Blo 167798 191803 := bstep (se 1 (by rfl) ⟨143852, by rfl⟩ : syracuseStep 191803 = 287705) B287705
theorem B257339 : Blo 167798 257339 := bstep (se 1 (by rfl) ⟨193004, by rfl⟩ : syracuseStep 257339 = 386009) B386009
theorem B257399 : Blo 167798 257399 := bstep (se 1 (by rfl) ⟨193049, by rfl⟩ : syracuseStep 257399 = 386099) B386099
theorem B257423 : Blo 167798 257423 := bstep (se 1 (by rfl) ⟨193067, by rfl⟩ : syracuseStep 257423 = 386135) B386135
theorem B257465 : Blo 167798 257465 := bstep (se 2 (by rfl) ⟨96549, by rfl⟩ : syracuseStep 257465 = 193099) B193099
theorem B257543 : Blo 167798 257543 := bstep (se 1 (by rfl) ⟨193157, by rfl⟩ : syracuseStep 257543 = 386315) B386315
theorem B257579 : Blo 167798 257579 := bstep (se 1 (by rfl) ⟨193184, by rfl⟩ : syracuseStep 257579 = 386369) B386369
theorem B257609 : Blo 167798 257609 := bstep (se 2 (by rfl) ⟨96603, by rfl⟩ : syracuseStep 257609 = 193207) B193207
theorem B913069 : Blo 167798 913069 := bstep (se 3 (by rfl) ⟨171200, by rfl⟩ : syracuseStep 913069 = 342401) B342401
theorem B1928933 : Blo 167798 1928933 := bstep (se 4 (by rfl) ⟨180837, by rfl⟩ : syracuseStep 1928933 = 361675) B361675
theorem B192271 : Blo 167798 192271 := bstep (se 1 (by rfl) ⟨144203, by rfl⟩ : syracuseStep 192271 = 288407) B288407
theorem B454547 : Blo 167798 454547 := bstep (se 1 (by rfl) ⟨340910, by rfl⟩ : syracuseStep 454547 = 681821) B681821
theorem B192775 : Blo 167798 192775 := bstep (se 1 (by rfl) ⟨144581, by rfl⟩ : syracuseStep 192775 = 289163) B289163
theorem B487691 : Blo 167798 487691 := bstep (se 1 (by rfl) ⟨365768, by rfl⟩ : syracuseStep 487691 = 731537) B731537
theorem B913679 : Blo 167798 913679 := bstep (se 1 (by rfl) ⟨685259, by rfl⟩ : syracuseStep 913679 = 1370519) B1370519
theorem B651635 : Blo 167798 651635 := bstep (se 1 (by rfl) ⟨488726, by rfl⟩ : syracuseStep 651635 = 977453) B977453
theorem B192955 : Blo 167798 192955 := bstep (se 1 (by rfl) ⟨144716, by rfl⟩ : syracuseStep 192955 = 289433) B289433
theorem B324155 : Blo 167798 324155 := bstep (se 1 (by rfl) ⟨243116, by rfl⟩ : syracuseStep 324155 = 486233) B486233
theorem B881239 : Blo 167798 881239 := bstep (se 1 (by rfl) ⟨660929, by rfl⟩ : syracuseStep 881239 = 1321859) B1321859
theorem B389947 : Blo 167798 389947 := bstep (se 1 (by rfl) ⟨292460, by rfl⟩ : syracuseStep 389947 = 584921) B584921
theorem B684935 : Blo 167798 684935 := bstep (se 1 (by rfl) ⟨513701, by rfl⟩ : syracuseStep 684935 = 1027403) B1027403
theorem B521095 : Blo 167798 521095 := bstep (se 1 (by rfl) ⟨390821, by rfl⟩ : syracuseStep 521095 = 781643) B781643
theorem B488339 : Blo 167798 488339 := bstep (se 1 (by rfl) ⟨366254, by rfl⟩ : syracuseStep 488339 = 732509) B732509
theorem B1274777 : Blo 167798 1274777 := bstep (se 2 (by rfl) ⟨478041, by rfl⟩ : syracuseStep 1274777 = 956083) B956083
theorem B324641 : Blo 167798 324641 := bstep (se 2 (by rfl) ⟨121740, by rfl⟩ : syracuseStep 324641 = 243481) B243481
theorem B488567 : Blo 167798 488567 := bstep (se 1 (by rfl) ⟨366425, by rfl⟩ : syracuseStep 488567 = 732851) B732851
theorem B259319 : Blo 167798 259319 := bstep (se 1 (by rfl) ⟨194489, by rfl⟩ : syracuseStep 259319 = 388979) B388979
theorem B259591 : Blo 167798 259591 := bstep (se 1 (by rfl) ⟨194693, by rfl⟩ : syracuseStep 259591 = 389387) B389387
theorem B849527 : Blo 167798 849527 := bstep (se 1 (by rfl) ⟨637145, by rfl⟩ : syracuseStep 849527 = 1274291) B1274291
theorem B718739 : Blo 167798 718739 := bstep (se 1 (by rfl) ⟨539054, by rfl⟩ : syracuseStep 718739 = 1078109) B1078109
theorem B260111 : Blo 167798 260111 := bstep (se 1 (by rfl) ⟨195083, by rfl⟩ : syracuseStep 260111 = 390167) B390167
theorem B391625 : Blo 167798 391625 := bstep (se 2 (by rfl) ⟨146859, by rfl⟩ : syracuseStep 391625 = 293719) B293719
theorem B850499 : Blo 167798 850499 := bstep (se 1 (by rfl) ⟨637874, by rfl⟩ : syracuseStep 850499 = 1275749) B1275749
theorem B359113 : Blo 167798 359113 := bstep (se 2 (by rfl) ⟨134667, by rfl⟩ : syracuseStep 359113 = 269335) B269335
theorem B1276721 : Blo 167798 1276721 := bstep (se 2 (by rfl) ⟨478770, by rfl⟩ : syracuseStep 1276721 = 957541) B957541
theorem B850823 : Blo 167798 850823 := bstep (se 1 (by rfl) ⟨638117, by rfl⟩ : syracuseStep 850823 = 1276235) B1276235
theorem B621611 : Blo 167798 621611 := bstep (se 1 (by rfl) ⟨466208, by rfl⟩ : syracuseStep 621611 = 932417) B932417
theorem B425047 : Blo 167798 425047 := bstep (se 1 (by rfl) ⟨318785, by rfl⟩ : syracuseStep 425047 = 637571) B637571
theorem B425351 : Blo 167798 425351 := bstep (se 1 (by rfl) ⟨319013, by rfl⟩ : syracuseStep 425351 = 638027) B638027
theorem B425483 : Blo 167798 425483 := bstep (se 1 (by rfl) ⟨319112, by rfl⟩ : syracuseStep 425483 = 638225) B638225
theorem B720413 : Blo 167798 720413 := bstep (se 3 (by rfl) ⟨135077, by rfl⟩ : syracuseStep 720413 = 270155) B270155
theorem B491123 : Blo 167798 491123 := bstep (se 1 (by rfl) ⟨368342, by rfl⟩ : syracuseStep 491123 = 736685) B736685
theorem B360121 : Blo 167798 360121 := bstep (se 2 (by rfl) ⟨135045, by rfl⟩ : syracuseStep 360121 = 270091) B270091
theorem B229111 : Blo 167798 229111 := bstep (se 1 (by rfl) ⟨171833, by rfl⟩ : syracuseStep 229111 = 343667) B343667
theorem B360377 : Blo 167798 360377 := bstep (se 2 (by rfl) ⟨135141, by rfl⟩ : syracuseStep 360377 = 270283) B270283
theorem B721163 : Blo 167798 721163 := bstep (se 1 (by rfl) ⟨540872, by rfl⟩ : syracuseStep 721163 = 1081745) B1081745
theorem B426505 : Blo 167798 426505 := bstep (se 2 (by rfl) ⟨159939, by rfl⟩ : syracuseStep 426505 = 319879) B319879
theorem B4915829 : Blo 167798 4915829 := bstep (se 5 (by rfl) ⟨230429, by rfl⟩ : syracuseStep 4915829 = 460859) B460859
theorem B1278665 : Blo 167798 1278665 := bstep (se 2 (by rfl) ⟨479499, by rfl⟩ : syracuseStep 1278665 = 958999) B958999
theorem B459475 : Blo 167798 459475 := bstep (se 1 (by rfl) ⟨344606, by rfl⟩ : syracuseStep 459475 = 689213) B689213
theorem B328555 : Blo 167798 328555 := bstep (se 1 (by rfl) ⟨246416, by rfl⟩ : syracuseStep 328555 = 492833) B492833
theorem B721847 : Blo 167798 721847 := bstep (se 1 (by rfl) ⟨541385, by rfl⟩ : syracuseStep 721847 = 1082771) B1082771
theorem B328711 : Blo 167798 328711 := bstep (se 1 (by rfl) ⟨246533, by rfl⟩ : syracuseStep 328711 = 493067) B493067
theorem B8259479 : Blo 167798 8259479 := bstep (se 1 (by rfl) ⟨6194609, by rfl⟩ : syracuseStep 8259479 = 12389219) B12389219
theorem B11175833 : Blo 167798 11175833 := bstep (se 2 (by rfl) ⟨4190937, by rfl⟩ : syracuseStep 11175833 = 8381875) B8381875
theorem B427963 : Blo 167798 427963 := bstep (se 1 (by rfl) ⟨320972, by rfl⟩ : syracuseStep 427963 = 641945) B641945
theorem B920249 : Blo 167798 920249 := bstep (se 2 (by rfl) ⟨345093, by rfl⟩ : syracuseStep 920249 = 690187) B690187
theorem B2362391 : Blo 167798 2362391 := bstep (se 1 (by rfl) ⟨1771793, by rfl⟩ : syracuseStep 2362391 = 3543587) B3543587
theorem B462071 : Blo 167798 462071 := bstep (se 1 (by rfl) ⟨346553, by rfl⟩ : syracuseStep 462071 = 693107) B693107
theorem B691517 : Blo 167798 691517 := bstep (se 3 (by rfl) ⟨129659, by rfl⟩ : syracuseStep 691517 = 259319) B259319
theorem B1084873 : Blo 167798 1084873 := bstep (se 2 (by rfl) ⟨406827, by rfl⟩ : syracuseStep 1084873 = 813655) B813655
theorem B462547 : Blo 167798 462547 := bstep (se 1 (by rfl) ⟨346910, by rfl⟩ : syracuseStep 462547 = 693821) B693821
theorem B1314593 : Blo 167798 1314593 := bstep (se 2 (by rfl) ⟨492972, by rfl⟩ : syracuseStep 1314593 = 985945) B985945
theorem B167803 : Blo 167798 167803 := bstep (se 1 (by rfl) ⟨125852, by rfl⟩ : syracuseStep 167803 = 251705) B251705
theorem B167855 : Blo 167798 167855 := bstep (se 1 (by rfl) ⟨125891, by rfl⟩ : syracuseStep 167855 = 251783) B251783
theorem B167879 : Blo 167798 167879 := bstep (se 1 (by rfl) ⟨125909, by rfl⟩ : syracuseStep 167879 = 251819) B251819
theorem B167899 : Blo 167798 167899 := bstep (se 1 (by rfl) ⟨125924, by rfl⟩ : syracuseStep 167899 = 251849) B251849
theorem B692231 : Blo 167798 692231 := bstep (se 1 (by rfl) ⟨519173, by rfl⟩ : syracuseStep 692231 = 1038347) B1038347
theorem B167975 : Blo 167798 167975 := bstep (se 1 (by rfl) ⟨125981, by rfl⟩ : syracuseStep 167975 = 251963) B251963
theorem B168015 : Blo 167798 168015 := bstep (se 1 (by rfl) ⟨126011, by rfl⟩ : syracuseStep 168015 = 252023) B252023
theorem B168031 : Blo 167798 168031 := bstep (se 1 (by rfl) ⟨126023, by rfl⟩ : syracuseStep 168031 = 252047) B252047
theorem B168059 : Blo 167798 168059 := bstep (se 1 (by rfl) ⟨126044, by rfl⟩ : syracuseStep 168059 = 252089) B252089
theorem B168111 : Blo 167798 168111 := bstep (se 1 (by rfl) ⟨126083, by rfl⟩ : syracuseStep 168111 = 252167) B252167
theorem B168135 : Blo 167798 168135 := bstep (se 1 (by rfl) ⟨126101, by rfl⟩ : syracuseStep 168135 = 252203) B252203
theorem B168155 : Blo 167798 168155 := bstep (se 1 (by rfl) ⟨126116, by rfl⟩ : syracuseStep 168155 = 252233) B252233
theorem B856331 : Blo 167798 856331 := bstep (se 1 (by rfl) ⟨642248, by rfl⟩ : syracuseStep 856331 = 1284497) B1284497
theorem B168231 : Blo 167798 168231 := bstep (se 1 (by rfl) ⟨126173, by rfl⟩ : syracuseStep 168231 = 252347) B252347
theorem B168271 : Blo 167798 168271 := bstep (se 1 (by rfl) ⟨126203, by rfl⟩ : syracuseStep 168271 = 252407) B252407
theorem B168287 : Blo 167798 168287 := bstep (se 1 (by rfl) ⟨126215, by rfl⟩ : syracuseStep 168287 = 252431) B252431
theorem B168315 : Blo 167798 168315 := bstep (se 1 (by rfl) ⟨126236, by rfl⟩ : syracuseStep 168315 = 252473) B252473
theorem B168367 : Blo 167798 168367 := bstep (se 1 (by rfl) ⟨126275, by rfl⟩ : syracuseStep 168367 = 252551) B252551
theorem B168391 : Blo 167798 168391 := bstep (se 1 (by rfl) ⟨126293, by rfl⟩ : syracuseStep 168391 = 252587) B252587
theorem B168411 : Blo 167798 168411 := bstep (se 1 (by rfl) ⟨126308, by rfl⟩ : syracuseStep 168411 = 252617) B252617
theorem B430555 : Blo 167798 430555 := bstep (se 1 (by rfl) ⟨322916, by rfl⟩ : syracuseStep 430555 = 645833) B645833
theorem B331321873 : Blo 167798 331321873 := bstep (se 2 (by rfl) ⟨124245702, by rfl⟩ : syracuseStep 331321873 = 248491405) B248491405
theorem B725537 : Blo 167798 725537 := bstep (se 2 (by rfl) ⟨272076, by rfl⟩ : syracuseStep 725537 = 544153) B544153
theorem B168487 : Blo 167798 168487 := bstep (se 1 (by rfl) ⟨126365, by rfl⟩ : syracuseStep 168487 = 252731) B252731
theorem B168527 : Blo 167798 168527 := bstep (se 1 (by rfl) ⟨126395, by rfl⟩ : syracuseStep 168527 = 252791) B252791
theorem B168543 : Blo 167798 168543 := bstep (se 1 (by rfl) ⟨126407, by rfl⟩ : syracuseStep 168543 = 252815) B252815
theorem B168571 : Blo 167798 168571 := bstep (se 1 (by rfl) ⟨126428, by rfl⟩ : syracuseStep 168571 = 252857) B252857
theorem B168623 : Blo 167798 168623 := bstep (se 1 (by rfl) ⟨126467, by rfl⟩ : syracuseStep 168623 = 252935) B252935
theorem B168647 : Blo 167798 168647 := bstep (se 1 (by rfl) ⟨126485, by rfl⟩ : syracuseStep 168647 = 252971) B252971
theorem B168667 : Blo 167798 168667 := bstep (se 1 (by rfl) ⟨126500, by rfl⟩ : syracuseStep 168667 = 253001) B253001
theorem B4166417 : Blo 167798 4166417 := bstep (se 2 (by rfl) ⟨1562406, by rfl⟩ : syracuseStep 4166417 = 3124813) B3124813
theorem B168743 : Blo 167798 168743 := bstep (se 1 (by rfl) ⟨126557, by rfl⟩ : syracuseStep 168743 = 253115) B253115
theorem B987977 : Blo 167798 987977 := bstep (se 2 (by rfl) ⟨370491, by rfl⟩ : syracuseStep 987977 = 740983) B740983
theorem B168783 : Blo 167798 168783 := bstep (se 1 (by rfl) ⟨126587, by rfl⟩ : syracuseStep 168783 = 253175) B253175
theorem B168799 : Blo 167798 168799 := bstep (se 1 (by rfl) ⟨126599, by rfl⟩ : syracuseStep 168799 = 253199) B253199
theorem B168827 : Blo 167798 168827 := bstep (se 1 (by rfl) ⟨126620, by rfl⟩ : syracuseStep 168827 = 253241) B253241
theorem B1217425 : Blo 167798 1217425 := bstep (se 2 (by rfl) ⟨456534, by rfl⟩ : syracuseStep 1217425 = 913069) B913069
theorem B168879 : Blo 167798 168879 := bstep (se 1 (by rfl) ⟨126659, by rfl⟩ : syracuseStep 168879 = 253319) B253319
theorem B168903 : Blo 167798 168903 := bstep (se 1 (by rfl) ⟨126677, by rfl⟩ : syracuseStep 168903 = 253355) B253355
theorem B168923 : Blo 167798 168923 := bstep (se 1 (by rfl) ⟨126692, by rfl⟩ : syracuseStep 168923 = 253385) B253385
theorem B168999 : Blo 167798 168999 := bstep (se 1 (by rfl) ⟨126749, by rfl⟩ : syracuseStep 168999 = 253499) B253499
theorem B169039 : Blo 167798 169039 := bstep (se 1 (by rfl) ⟨126779, by rfl⟩ : syracuseStep 169039 = 253559) B253559
theorem B431183 : Blo 167798 431183 := bstep (se 1 (by rfl) ⟨323387, by rfl⟩ : syracuseStep 431183 = 646775) B646775
theorem B169055 : Blo 167798 169055 := bstep (se 1 (by rfl) ⟨126791, by rfl⟩ : syracuseStep 169055 = 253583) B253583
theorem B1741943 : Blo 167798 1741943 := bstep (se 1 (by rfl) ⟨1306457, by rfl⟩ : syracuseStep 1741943 = 2612915) B2612915
theorem B169083 : Blo 167798 169083 := bstep (se 1 (by rfl) ⟨126812, by rfl⟩ : syracuseStep 169083 = 253625) B253625
theorem B169135 : Blo 167798 169135 := bstep (se 1 (by rfl) ⟨126851, by rfl⟩ : syracuseStep 169135 = 253703) B253703
theorem B169159 : Blo 167798 169159 := bstep (se 1 (by rfl) ⟨126869, by rfl⟩ : syracuseStep 169159 = 253739) B253739
theorem B169179 : Blo 167798 169179 := bstep (se 1 (by rfl) ⟨126884, by rfl⟩ : syracuseStep 169179 = 253769) B253769
theorem B169255 : Blo 167798 169255 := bstep (se 1 (by rfl) ⟨126941, by rfl⟩ : syracuseStep 169255 = 253883) B253883
theorem B169295 : Blo 167798 169295 := bstep (se 1 (by rfl) ⟨126971, by rfl⟩ : syracuseStep 169295 = 253943) B253943
theorem B169311 : Blo 167798 169311 := bstep (se 1 (by rfl) ⟨126983, by rfl⟩ : syracuseStep 169311 = 253967) B253967
theorem B169339 : Blo 167798 169339 := bstep (se 1 (by rfl) ⟨127004, by rfl⟩ : syracuseStep 169339 = 254009) B254009
theorem B693629 : Blo 167798 693629 := bstep (se 3 (by rfl) ⟨130055, by rfl⟩ : syracuseStep 693629 = 260111) B260111
theorem B169391 : Blo 167798 169391 := bstep (se 1 (by rfl) ⟨127043, by rfl⟩ : syracuseStep 169391 = 254087) B254087
theorem B169415 : Blo 167798 169415 := bstep (se 1 (by rfl) ⟨127061, by rfl⟩ : syracuseStep 169415 = 254123) B254123
theorem B169435 : Blo 167798 169435 := bstep (se 1 (by rfl) ⟨127076, by rfl⟩ : syracuseStep 169435 = 254153) B254153
theorem B169511 : Blo 167798 169511 := bstep (se 1 (by rfl) ⟨127133, by rfl⟩ : syracuseStep 169511 = 254267) B254267
theorem B169551 : Blo 167798 169551 := bstep (se 1 (by rfl) ⟨127163, by rfl⟩ : syracuseStep 169551 = 254327) B254327
theorem B169567 : Blo 167798 169567 := bstep (se 1 (by rfl) ⟨127175, by rfl⟩ : syracuseStep 169567 = 254351) B254351
theorem B169595 : Blo 167798 169595 := bstep (se 1 (by rfl) ⟨127196, by rfl⟩ : syracuseStep 169595 = 254393) B254393
theorem B169647 : Blo 167798 169647 := bstep (se 1 (by rfl) ⟨127235, by rfl⟩ : syracuseStep 169647 = 254471) B254471
theorem B857789 : Blo 167798 857789 := bstep (se 3 (by rfl) ⟨160835, by rfl⟩ : syracuseStep 857789 = 321671) B321671
theorem B169671 : Blo 167798 169671 := bstep (se 1 (by rfl) ⟨127253, by rfl⟩ : syracuseStep 169671 = 254507) B254507
theorem B431831 : Blo 167798 431831 := bstep (se 1 (by rfl) ⟨323873, by rfl⟩ : syracuseStep 431831 = 647747) B647747
theorem B169691 : Blo 167798 169691 := bstep (se 1 (by rfl) ⟨127268, by rfl⟩ : syracuseStep 169691 = 254537) B254537
theorem B169767 : Blo 167798 169767 := bstep (se 1 (by rfl) ⟨127325, by rfl⟩ : syracuseStep 169767 = 254651) B254651
theorem B169807 : Blo 167798 169807 := bstep (se 1 (by rfl) ⟨127355, by rfl⟩ : syracuseStep 169807 = 254711) B254711
theorem B857951 : Blo 167798 857951 := bstep (se 1 (by rfl) ⟨643463, by rfl⟩ : syracuseStep 857951 = 1286927) B1286927
theorem B169823 : Blo 167798 169823 := bstep (se 1 (by rfl) ⟨127367, by rfl⟩ : syracuseStep 169823 = 254735) B254735
theorem B169851 : Blo 167798 169851 := bstep (se 1 (by rfl) ⟨127388, by rfl⟩ : syracuseStep 169851 = 254777) B254777
theorem B169903 : Blo 167798 169903 := bstep (se 1 (by rfl) ⟨127427, by rfl⟩ : syracuseStep 169903 = 254855) B254855
theorem B169927 : Blo 167798 169927 := bstep (se 1 (by rfl) ⟨127445, by rfl⟩ : syracuseStep 169927 = 254891) B254891
theorem B169947 : Blo 167798 169947 := bstep (se 1 (by rfl) ⟨127460, by rfl⟩ : syracuseStep 169947 = 254921) B254921
theorem B170023 : Blo 167798 170023 := bstep (se 1 (by rfl) ⟨127517, by rfl⟩ : syracuseStep 170023 = 255035) B255035
theorem B170063 : Blo 167798 170063 := bstep (se 1 (by rfl) ⟨127547, by rfl⟩ : syracuseStep 170063 = 255095) B255095
theorem B170079 : Blo 167798 170079 := bstep (se 1 (by rfl) ⟨127559, by rfl⟩ : syracuseStep 170079 = 255119) B255119
theorem B170107 : Blo 167798 170107 := bstep (se 1 (by rfl) ⟨127580, by rfl⟩ : syracuseStep 170107 = 255161) B255161
theorem B170159 : Blo 167798 170159 := bstep (se 1 (by rfl) ⟨127619, by rfl⟩ : syracuseStep 170159 = 255239) B255239
theorem B170183 : Blo 167798 170183 := bstep (se 1 (by rfl) ⟨127637, by rfl⟩ : syracuseStep 170183 = 255275) B255275
theorem B170203 : Blo 167798 170203 := bstep (se 1 (by rfl) ⟨127652, by rfl⟩ : syracuseStep 170203 = 255305) B255305
theorem B170279 : Blo 167798 170279 := bstep (se 1 (by rfl) ⟨127709, by rfl⟩ : syracuseStep 170279 = 255419) B255419
theorem B170319 : Blo 167798 170319 := bstep (se 1 (by rfl) ⟨127739, by rfl⟩ : syracuseStep 170319 = 255479) B255479
theorem B170335 : Blo 167798 170335 := bstep (se 1 (by rfl) ⟨127751, by rfl⟩ : syracuseStep 170335 = 255503) B255503
theorem B170363 : Blo 167798 170363 := bstep (se 1 (by rfl) ⟨127772, by rfl⟩ : syracuseStep 170363 = 255545) B255545
theorem B170415 : Blo 167798 170415 := bstep (se 1 (by rfl) ⟨127811, by rfl⟩ : syracuseStep 170415 = 255623) B255623
theorem B170439 : Blo 167798 170439 := bstep (se 1 (by rfl) ⟨127829, by rfl⟩ : syracuseStep 170439 = 255659) B255659
theorem B170459 : Blo 167798 170459 := bstep (se 1 (by rfl) ⟨127844, by rfl⟩ : syracuseStep 170459 = 255689) B255689
theorem B694793 : Blo 167798 694793 := bstep (se 2 (by rfl) ⟨260547, by rfl⟩ : syracuseStep 694793 = 521095) B521095
theorem B170535 : Blo 167798 170535 := bstep (se 1 (by rfl) ⟨127901, by rfl⟩ : syracuseStep 170535 = 255803) B255803
theorem B170575 : Blo 167798 170575 := bstep (se 1 (by rfl) ⟨127931, by rfl⟩ : syracuseStep 170575 = 255863) B255863
theorem B170591 : Blo 167798 170591 := bstep (se 1 (by rfl) ⟨127943, by rfl⟩ : syracuseStep 170591 = 255887) B255887
theorem B170619 : Blo 167798 170619 := bstep (se 1 (by rfl) ⟨127964, by rfl⟩ : syracuseStep 170619 = 255929) B255929
theorem B170671 : Blo 167798 170671 := bstep (se 1 (by rfl) ⟨128003, by rfl⟩ : syracuseStep 170671 = 256007) B256007
theorem B170695 : Blo 167798 170695 := bstep (se 1 (by rfl) ⟨128021, by rfl⟩ : syracuseStep 170695 = 256043) B256043
theorem B170715 : Blo 167798 170715 := bstep (se 1 (by rfl) ⟨128036, by rfl⟩ : syracuseStep 170715 = 256073) B256073
theorem B170791 : Blo 167798 170791 := bstep (se 1 (by rfl) ⟨128093, by rfl⟩ : syracuseStep 170791 = 256187) B256187
theorem B170831 : Blo 167798 170831 := bstep (se 1 (by rfl) ⟨128123, by rfl⟩ : syracuseStep 170831 = 256247) B256247
theorem B170847 : Blo 167798 170847 := bstep (se 1 (by rfl) ⟨128135, by rfl⟩ : syracuseStep 170847 = 256271) B256271
theorem B170875 : Blo 167798 170875 := bstep (se 1 (by rfl) ⟨128156, by rfl⟩ : syracuseStep 170875 = 256313) B256313
theorem B957359 : Blo 167798 957359 := bstep (se 1 (by rfl) ⟨718019, by rfl⟩ : syracuseStep 957359 = 1436039) B1436039
theorem B170927 : Blo 167798 170927 := bstep (se 1 (by rfl) ⟨128195, by rfl⟩ : syracuseStep 170927 = 256391) B256391
theorem B1448887 : Blo 167798 1448887 := bstep (se 1 (by rfl) ⟨1086665, by rfl⟩ : syracuseStep 1448887 = 2173331) B2173331
theorem B170951 : Blo 167798 170951 := bstep (se 1 (by rfl) ⟨128213, by rfl⟩ : syracuseStep 170951 = 256427) B256427
theorem B170971 : Blo 167798 170971 := bstep (se 1 (by rfl) ⟨128228, by rfl⟩ : syracuseStep 170971 = 256457) B256457
theorem B171047 : Blo 167798 171047 := bstep (se 1 (by rfl) ⟨128285, by rfl⟩ : syracuseStep 171047 = 256571) B256571
theorem B171087 : Blo 167798 171087 := bstep (se 1 (by rfl) ⟨128315, by rfl⟩ : syracuseStep 171087 = 256631) B256631
theorem B171103 : Blo 167798 171103 := bstep (se 1 (by rfl) ⟨128327, by rfl⟩ : syracuseStep 171103 = 256655) B256655
theorem B171131 : Blo 167798 171131 := bstep (se 1 (by rfl) ⟨128348, by rfl⟩ : syracuseStep 171131 = 256697) B256697
theorem B171183 : Blo 167798 171183 := bstep (se 1 (by rfl) ⟨128387, by rfl⟩ : syracuseStep 171183 = 256775) B256775
theorem B171207 : Blo 167798 171207 := bstep (se 1 (by rfl) ⟨128405, by rfl⟩ : syracuseStep 171207 = 256811) B256811
theorem B171227 : Blo 167798 171227 := bstep (se 1 (by rfl) ⟨128420, by rfl⟩ : syracuseStep 171227 = 256841) B256841
theorem B171303 : Blo 167798 171303 := bstep (se 1 (by rfl) ⟨128477, by rfl⟩ : syracuseStep 171303 = 256955) B256955
theorem B171343 : Blo 167798 171343 := bstep (se 1 (by rfl) ⟨128507, by rfl⟩ : syracuseStep 171343 = 257015) B257015
theorem B171359 : Blo 167798 171359 := bstep (se 1 (by rfl) ⟨128519, by rfl⟩ : syracuseStep 171359 = 257039) B257039
theorem B171387 : Blo 167798 171387 := bstep (se 1 (by rfl) ⟨128540, by rfl⟩ : syracuseStep 171387 = 257081) B257081
theorem B466319 : Blo 167798 466319 := bstep (se 1 (by rfl) ⟨349739, by rfl⟩ : syracuseStep 466319 = 699479) B699479
theorem B171439 : Blo 167798 171439 := bstep (se 1 (by rfl) ⟨128579, by rfl⟩ : syracuseStep 171439 = 257159) B257159
theorem B171463 : Blo 167798 171463 := bstep (se 1 (by rfl) ⟨128597, by rfl⟩ : syracuseStep 171463 = 257195) B257195
theorem B171483 : Blo 167798 171483 := bstep (se 1 (by rfl) ⟨128612, by rfl⟩ : syracuseStep 171483 = 257225) B257225
theorem B171559 : Blo 167798 171559 := bstep (se 1 (by rfl) ⟨128669, by rfl⟩ : syracuseStep 171559 = 257339) B257339
theorem B171599 : Blo 167798 171599 := bstep (se 1 (by rfl) ⟨128699, by rfl⟩ : syracuseStep 171599 = 257399) B257399
theorem B171615 : Blo 167798 171615 := bstep (se 1 (by rfl) ⟨128711, by rfl⟩ : syracuseStep 171615 = 257423) B257423
theorem B171643 : Blo 167798 171643 := bstep (se 1 (by rfl) ⟨128732, by rfl⟩ : syracuseStep 171643 = 257465) B257465
theorem B171695 : Blo 167798 171695 := bstep (se 1 (by rfl) ⟨128771, by rfl⟩ : syracuseStep 171695 = 257543) B257543
theorem B171719 : Blo 167798 171719 := bstep (se 1 (by rfl) ⟨128789, by rfl⟩ : syracuseStep 171719 = 257579) B257579
theorem B171739 : Blo 167798 171739 := bstep (se 1 (by rfl) ⟨128804, by rfl⟩ : syracuseStep 171739 = 257609) B257609
theorem B1285955 : Blo 167798 1285955 := bstep (se 1 (by rfl) ⟨964466, by rfl⟩ : syracuseStep 1285955 = 1928933) B1928933
theorem B303031 : Blo 167798 303031 := bstep (se 1 (by rfl) ⟨227273, by rfl⟩ : syracuseStep 303031 = 454547) B454547
theorem B1974451 : Blo 167798 1974451 := bstep (se 1 (by rfl) ⟨1480838, by rfl⟩ : syracuseStep 1974451 = 2961677) B2961677
theorem B434423 : Blo 167798 434423 := bstep (se 1 (by rfl) ⟨325817, by rfl⟩ : syracuseStep 434423 = 651635) B651635
theorem B860705 : Blo 167798 860705 := bstep (se 2 (by rfl) ⟨322764, by rfl⟩ : syracuseStep 860705 = 645529) B645529
theorem B205751 : Blo 167798 205751 := bstep (se 1 (by rfl) ⟨154313, by rfl⟩ : syracuseStep 205751 = 308627) B308627
theorem B566351 : Blo 167798 566351 := bstep (se 1 (by rfl) ⟨424763, by rfl⟩ : syracuseStep 566351 = 849527) B849527
theorem B205903 : Blo 167798 205903 := bstep (se 1 (by rfl) ⟨154427, by rfl⟩ : syracuseStep 205903 = 308855) B308855
theorem B1221925 : Blo 167798 1221925 := bstep (se 4 (by rfl) ⟨114555, by rfl⟩ : syracuseStep 1221925 = 229111) B229111
theorem B1025453 : Blo 167798 1025453 := bstep (se 3 (by rfl) ⟨192272, by rfl⟩ : syracuseStep 1025453 = 384545) B384545
theorem B566729 : Blo 167798 566729 := bstep (se 2 (by rfl) ⟨212523, by rfl⟩ : syracuseStep 566729 = 425047) B425047
theorem B370273 : Blo 167798 370273 := bstep (se 2 (by rfl) ⟨138852, by rfl⟩ : syracuseStep 370273 = 277705) B277705
theorem B14526053 : Blo 167798 14526053 := bstep (se 4 (by rfl) ⟨1361817, by rfl⟩ : syracuseStep 14526053 = 2723635) B2723635
theorem B566999 : Blo 167798 566999 := bstep (se 1 (by rfl) ⟨425249, by rfl⟩ : syracuseStep 566999 = 850499) B850499
theorem B567215 : Blo 167798 567215 := bstep (se 1 (by rfl) ⟨425411, by rfl⟩ : syracuseStep 567215 = 850823) B850823
theorem B240251 : Blo 167798 240251 := bstep (se 1 (by rfl) ⟨180188, by rfl⟩ : syracuseStep 240251 = 360377) B360377
theorem B1092305 : Blo 167798 1092305 := bstep (se 2 (by rfl) ⟨409614, by rfl⟩ : syracuseStep 1092305 = 819229) B819229
theorem B240889 : Blo 167798 240889 := bstep (se 2 (by rfl) ⟨90333, by rfl⟩ : syracuseStep 240889 = 180667) B180667
theorem B306505 : Blo 167798 306505 := bstep (se 2 (by rfl) ⟨114939, by rfl⟩ : syracuseStep 306505 = 229879) B229879
theorem B241003 : Blo 167798 241003 := bstep (se 1 (by rfl) ⟨180752, by rfl⟩ : syracuseStep 241003 = 361505) B361505
theorem B863783 : Blo 167798 863783 := bstep (se 1 (by rfl) ⟨647837, by rfl⟩ : syracuseStep 863783 = 1295675) B1295675
theorem B241231 : Blo 167798 241231 := bstep (se 1 (by rfl) ⟨180923, by rfl⟩ : syracuseStep 241231 = 361847) B361847
theorem B765587 : Blo 167798 765587 := bstep (se 1 (by rfl) ⟨574190, by rfl⟩ : syracuseStep 765587 = 1148381) B1148381
theorem B1093409 : Blo 167798 1093409 := bstep (se 2 (by rfl) ⟨410028, by rfl⟩ : syracuseStep 1093409 = 820057) B820057
theorem B1290329 : Blo 167798 1290329 := bstep (se 2 (by rfl) ⟨483873, by rfl⟩ : syracuseStep 1290329 = 967747) B967747
theorem B438443 : Blo 167798 438443 := bstep (se 1 (by rfl) ⟨328832, by rfl⟩ : syracuseStep 438443 = 657665) B657665
theorem B569591 : Blo 167798 569591 := bstep (se 1 (by rfl) ⟨427193, by rfl⟩ : syracuseStep 569591 = 854387) B854387
theorem B569915 : Blo 167798 569915 := bstep (se 1 (by rfl) ⟨427436, by rfl⟩ : syracuseStep 569915 = 854873) B854873
theorem B2470459 : Blo 167798 2470459 := bstep (se 1 (by rfl) ⟨1852844, by rfl⟩ : syracuseStep 2470459 = 3705689) B3705689
theorem B570185 : Blo 167798 570185 := bstep (se 2 (by rfl) ⟨213819, by rfl⟩ : syracuseStep 570185 = 427639) B427639
theorem B406367 : Blo 167798 406367 := bstep (se 1 (by rfl) ⟨304775, by rfl⟩ : syracuseStep 406367 = 609551) B609551
theorem B2241433 : Blo 167798 2241433 := bstep (se 2 (by rfl) ⟨840537, by rfl⟩ : syracuseStep 2241433 = 1681075) B1681075
theorem B242615 : Blo 167798 242615 := bstep (se 1 (by rfl) ⟨181961, by rfl⟩ : syracuseStep 242615 = 363923) B363923
theorem B1291787 : Blo 167798 1291787 := bstep (se 1 (by rfl) ⟨968840, by rfl⟩ : syracuseStep 1291787 = 1937681) B1937681
theorem B865889 : Blo 167798 865889 := bstep (se 2 (by rfl) ⟨324708, by rfl⟩ : syracuseStep 865889 = 649417) B649417
theorem B538235 : Blo 167798 538235 := bstep (se 1 (by rfl) ⟨403676, by rfl⟩ : syracuseStep 538235 = 807353) B807353
theorem B440057 : Blo 167798 440057 := bstep (se 2 (by rfl) ⟨165021, by rfl⟩ : syracuseStep 440057 = 330043) B330043
theorem B571319 : Blo 167798 571319 := bstep (se 1 (by rfl) ⟨428489, by rfl⟩ : syracuseStep 571319 = 856979) B856979
theorem B1227113 : Blo 167798 1227113 := bstep (se 2 (by rfl) ⟨460167, by rfl⟩ : syracuseStep 1227113 = 920335) B920335
theorem B244073 : Blo 167798 244073 := bstep (se 2 (by rfl) ⟨91527, by rfl⟩ : syracuseStep 244073 = 183055) B183055
theorem B833921 : Blo 167798 833921 := bstep (se 2 (by rfl) ⟨312720, by rfl⟩ : syracuseStep 833921 = 625441) B625441
theorem B571913 : Blo 167798 571913 := bstep (se 2 (by rfl) ⟨214467, by rfl⟩ : syracuseStep 571913 = 428935) B428935
theorem B539335 : Blo 167798 539335 := bstep (se 1 (by rfl) ⟨404501, by rfl⟩ : syracuseStep 539335 = 809003) B809003
theorem B2472677 : Blo 167798 2472677 := bstep (se 4 (by rfl) ⟨231813, by rfl⟩ : syracuseStep 2472677 = 463627) B463627
theorem B637739 : Blo 167798 637739 := bstep (se 1 (by rfl) ⟨478304, by rfl⟩ : syracuseStep 637739 = 956609) B956609
theorem B408415 : Blo 167798 408415 := bstep (se 1 (by rfl) ⟨306311, by rfl⟩ : syracuseStep 408415 = 612623) B612623
theorem B539567 : Blo 167798 539567 := bstep (se 1 (by rfl) ⟨404675, by rfl⟩ : syracuseStep 539567 = 809351) B809351
theorem B768943 : Blo 167798 768943 := bstep (se 1 (by rfl) ⟨576707, by rfl⟩ : syracuseStep 768943 = 1153415) B1153415
theorem B867347 : Blo 167798 867347 := bstep (se 1 (by rfl) ⟨650510, by rfl⟩ : syracuseStep 867347 = 1301021) B1301021
theorem B572777 : Blo 167798 572777 := bstep (se 2 (by rfl) ⟨214791, by rfl⟩ : syracuseStep 572777 = 429583) B429583
theorem B1293731 : Blo 167798 1293731 := bstep (se 1 (by rfl) ⟨970298, by rfl⟩ : syracuseStep 1293731 = 1940597) B1940597
theorem B966107 : Blo 167798 966107 := bstep (se 1 (by rfl) ⟨724580, by rfl⟩ : syracuseStep 966107 = 1449161) B1449161
theorem B966289 : Blo 167798 966289 := bstep (se 2 (by rfl) ⟨362358, by rfl⟩ : syracuseStep 966289 = 724717) B724717
theorem B179911 : Blo 167798 179911 := bstep (se 1 (by rfl) ⟨134933, by rfl⟩ : syracuseStep 179911 = 269867) B269867
theorem B1228729 : Blo 167798 1228729 := bstep (se 2 (by rfl) ⟨460773, by rfl⟩ : syracuseStep 1228729 = 921547) B921547
theorem B573371 : Blo 167798 573371 := bstep (se 1 (by rfl) ⟨430028, by rfl⟩ : syracuseStep 573371 = 860057) B860057
theorem B1851569 : Blo 167798 1851569 := bstep (se 2 (by rfl) ⟨694338, by rfl⟩ : syracuseStep 1851569 = 1388677) B1388677
theorem B1097995 : Blo 167798 1097995 := bstep (se 1 (by rfl) ⟨823496, by rfl⟩ : syracuseStep 1097995 = 1646993) B1646993
theorem B2015549 : Blo 167798 2015549 := bstep (se 3 (by rfl) ⟨377915, by rfl⟩ : syracuseStep 2015549 = 755831) B755831
theorem B2769221 : Blo 167798 2769221 := bstep (se 4 (by rfl) ⟨259614, by rfl⟩ : syracuseStep 2769221 = 519229) B519229
theorem B639697 : Blo 167798 639697 := bstep (se 2 (by rfl) ⟨239886, by rfl⟩ : syracuseStep 639697 = 479773) B479773
theorem B377783 : Blo 167798 377783 := bstep (se 1 (by rfl) ⟨283337, by rfl⟩ : syracuseStep 377783 = 566675) B566675
theorem B640001 : Blo 167798 640001 := bstep (se 2 (by rfl) ⟨240000, by rfl⟩ : syracuseStep 640001 = 480001) B480001
theorem B1459619 : Blo 167798 1459619 := bstep (se 1 (by rfl) ⟨1094714, by rfl⟩ : syracuseStep 1459619 = 2189429) B2189429
theorem B640457 : Blo 167798 640457 := bstep (se 2 (by rfl) ⟨240171, by rfl⟩ : syracuseStep 640457 = 480343) B480343
theorem B378377 : Blo 167798 378377 := bstep (se 2 (by rfl) ⟨141891, by rfl⟩ : syracuseStep 378377 = 283783) B283783
theorem B575099 : Blo 167798 575099 := bstep (se 1 (by rfl) ⟨431324, by rfl⟩ : syracuseStep 575099 = 862649) B862649
theorem B411259 : Blo 167798 411259 := bstep (se 1 (by rfl) ⟨308444, by rfl⟩ : syracuseStep 411259 = 616889) B616889
theorem B575261 : Blo 167798 575261 := bstep (se 3 (by rfl) ⟨107861, by rfl⟩ : syracuseStep 575261 = 215723) B215723
theorem B1296161 : Blo 167798 1296161 := bstep (se 2 (by rfl) ⟨486060, by rfl⟩ : syracuseStep 1296161 = 972121) B972121
theorem B378719 : Blo 167798 378719 := bstep (se 1 (by rfl) ⟨284039, by rfl⟩ : syracuseStep 378719 = 568079) B568079
theorem B39929699 : Blo 167798 39929699 := bstep (se 1 (by rfl) ⟨29947274, by rfl⟩ : syracuseStep 39929699 = 59894549) B59894549
theorem B640943 : Blo 167798 640943 := bstep (se 1 (by rfl) ⟨480707, by rfl⟩ : syracuseStep 640943 = 961415) B961415
theorem B346121 : Blo 167798 346121 := bstep (se 2 (by rfl) ⟨129795, by rfl⟩ : syracuseStep 346121 = 259591) B259591
theorem B378899 : Blo 167798 378899 := bstep (se 1 (by rfl) ⟨284174, by rfl⟩ : syracuseStep 378899 = 568349) B568349
theorem B1624121 : Blo 167798 1624121 := bstep (se 2 (by rfl) ⟨609045, by rfl⟩ : syracuseStep 1624121 = 1218091) B1218091
theorem B379241 : Blo 167798 379241 := bstep (se 2 (by rfl) ⟨142215, by rfl⟩ : syracuseStep 379241 = 284431) B284431
theorem B3295673 : Blo 167798 3295673 := bstep (se 2 (by rfl) ⟨1235877, by rfl⟩ : syracuseStep 3295673 = 2471755) B2471755
theorem B575963 : Blo 167798 575963 := bstep (se 1 (by rfl) ⟨431972, by rfl⟩ : syracuseStep 575963 = 863945) B863945
theorem B543257 : Blo 167798 543257 := bstep (se 2 (by rfl) ⟨203721, by rfl⟩ : syracuseStep 543257 = 407443) B407443
theorem B412489 : Blo 167798 412489 := bstep (se 2 (by rfl) ⟨154683, by rfl⟩ : syracuseStep 412489 = 309367) B309367
theorem B609119 : Blo 167798 609119 := bstep (se 1 (by rfl) ⟨456839, by rfl⟩ : syracuseStep 609119 = 913679) B913679
theorem B379835 : Blo 167798 379835 := bstep (se 1 (by rfl) ⟨284876, by rfl⟩ : syracuseStep 379835 = 569753) B569753
theorem B216103 : Blo 167798 216103 := bstep (se 1 (by rfl) ⟨162077, by rfl⟩ : syracuseStep 216103 = 324155) B324155
theorem B379961 : Blo 167798 379961 := bstep (se 2 (by rfl) ⟨142485, by rfl⟩ : syracuseStep 379961 = 284971) B284971
theorem B642127 : Blo 167798 642127 := bstep (se 1 (by rfl) ⟨481595, by rfl⟩ : syracuseStep 642127 = 963191) B963191
theorem B576665 : Blo 167798 576665 := bstep (se 2 (by rfl) ⟨216249, by rfl⟩ : syracuseStep 576665 = 432499) B432499
theorem B216427 : Blo 167798 216427 := bstep (se 1 (by rfl) ⟨162320, by rfl⟩ : syracuseStep 216427 = 324641) B324641
theorem B380303 : Blo 167798 380303 := bstep (se 1 (by rfl) ⟨285227, by rfl⟩ : syracuseStep 380303 = 570455) B570455
theorem B511451 : Blo 167798 511451 := bstep (se 1 (by rfl) ⟨383588, by rfl⟩ : syracuseStep 511451 = 767177) B767177
theorem B642599 : Blo 167798 642599 := bstep (se 1 (by rfl) ⟨481949, by rfl⟩ : syracuseStep 642599 = 963899) B963899
theorem B478817 : Blo 167798 478817 := bstep (se 2 (by rfl) ⟨179556, by rfl⟩ : syracuseStep 478817 = 359113) B359113
theorem B1756811 : Blo 167798 1756811 := bstep (se 1 (by rfl) ⟨1317608, by rfl⟩ : syracuseStep 1756811 = 2635217) B2635217
theorem B380627 : Blo 167798 380627 := bstep (se 1 (by rfl) ⟨285470, by rfl⟩ : syracuseStep 380627 = 570941) B570941
theorem B479159 : Blo 167798 479159 := bstep (se 1 (by rfl) ⟨359369, by rfl⟩ : syracuseStep 479159 = 718739) B718739
theorem B544769 : Blo 167798 544769 := bstep (se 2 (by rfl) ⟨204288, by rfl⟩ : syracuseStep 544769 = 408577) B408577
theorem B8376331 : Blo 167798 8376331 := bstep (se 1 (by rfl) ⟨6282248, by rfl⟩ : syracuseStep 8376331 = 12564497) B12564497
theorem B577853 : Blo 167798 577853 := bstep (se 3 (by rfl) ⟨108347, by rfl⟩ : syracuseStep 577853 = 216695) B216695
theorem B643571 : Blo 167798 643571 := bstep (se 1 (by rfl) ⟨482678, by rfl⟩ : syracuseStep 643571 = 965357) B965357
theorem B381563 : Blo 167798 381563 := bstep (se 1 (by rfl) ⟨286172, by rfl⟩ : syracuseStep 381563 = 572345) B572345
theorem B414407 : Blo 167798 414407 := bstep (se 1 (by rfl) ⟨310805, by rfl⟩ : syracuseStep 414407 = 621611) B621611
theorem B283385 : Blo 167798 283385 := bstep (se 2 (by rfl) ⟨106269, by rfl⟩ : syracuseStep 283385 = 212539) B212539
theorem B381689 : Blo 167798 381689 := bstep (se 2 (by rfl) ⟨143133, by rfl⟩ : syracuseStep 381689 = 286267) B286267
theorem B480161 : Blo 167798 480161 := bstep (se 2 (by rfl) ⟨180060, by rfl⟩ : syracuseStep 480161 = 360121) B360121
theorem B283567 : Blo 167798 283567 := bstep (se 1 (by rfl) ⟨212675, by rfl⟩ : syracuseStep 283567 = 425351) B425351
theorem B1037231 : Blo 167798 1037231 := bstep (se 1 (by rfl) ⟨777923, by rfl⟩ : syracuseStep 1037231 = 1555847) B1555847
theorem B1168303 : Blo 167798 1168303 := bstep (se 1 (by rfl) ⟨876227, by rfl⟩ : syracuseStep 1168303 = 1752455) B1752455
theorem B283655 : Blo 167798 283655 := bstep (se 1 (by rfl) ⟨212741, by rfl⟩ : syracuseStep 283655 = 425483) B425483
theorem B381959 : Blo 167798 381959 := bstep (se 1 (by rfl) ⟨286469, by rfl⟩ : syracuseStep 381959 = 572939) B572939
theorem B480275 : Blo 167798 480275 := bstep (se 1 (by rfl) ⟨360206, by rfl⟩ : syracuseStep 480275 = 720413) B720413
theorem B1463345 : Blo 167798 1463345 := bstep (se 2 (by rfl) ⟨548754, by rfl⟩ : syracuseStep 1463345 = 1097509) B1097509
theorem B382031 : Blo 167798 382031 := bstep (se 1 (by rfl) ⟨286523, by rfl⟩ : syracuseStep 382031 = 573047) B573047
theorem B578717 : Blo 167798 578717 := bstep (se 3 (by rfl) ⟨108509, by rfl⟩ : syracuseStep 578717 = 217019) B217019
theorem B283999 : Blo 167798 283999 := bstep (se 1 (by rfl) ⟨212999, by rfl⟩ : syracuseStep 283999 = 425999) B425999
theorem B480617 : Blo 167798 480617 := bstep (se 2 (by rfl) ⟨180231, by rfl⟩ : syracuseStep 480617 = 360463) B360463
theorem B284087 : Blo 167798 284087 := bstep (se 1 (by rfl) ⟨213065, by rfl⟩ : syracuseStep 284087 = 426131) B426131
theorem B873929 : Blo 167798 873929 := bstep (se 2 (by rfl) ⟨327723, by rfl⟩ : syracuseStep 873929 = 655447) B655447
theorem B382427 : Blo 167798 382427 := bstep (se 1 (by rfl) ⟨286820, by rfl⟩ : syracuseStep 382427 = 573641) B573641
theorem B579257 : Blo 167798 579257 := bstep (se 2 (by rfl) ⟨217221, by rfl⟩ : syracuseStep 579257 = 434443) B434443
theorem B1627847 : Blo 167798 1627847 := bstep (se 1 (by rfl) ⟨1220885, by rfl⟩ : syracuseStep 1627847 = 2441771) B2441771
theorem B251753 : Blo 167798 251753 := bstep (se 2 (by rfl) ⟨94407, by rfl⟩ : syracuseStep 251753 = 188815) B188815
theorem B382895 : Blo 167798 382895 := bstep (se 1 (by rfl) ⟨287171, by rfl⟩ : syracuseStep 382895 = 574343) B574343
theorem B251831 : Blo 167798 251831 := bstep (se 1 (by rfl) ⟨188873, by rfl⟩ : syracuseStep 251831 = 377747) B377747
theorem B546743 : Blo 167798 546743 := bstep (se 1 (by rfl) ⟨410057, by rfl⟩ : syracuseStep 546743 = 820115) B820115
theorem B251867 : Blo 167798 251867 := bstep (se 1 (by rfl) ⟨188900, by rfl⟩ : syracuseStep 251867 = 377801) B377801
theorem B415751 : Blo 167798 415751 := bstep (se 1 (by rfl) ⟨311813, by rfl⟩ : syracuseStep 415751 = 623627) B623627
theorem B284681 : Blo 167798 284681 := bstep (se 2 (by rfl) ⟨106755, by rfl⟩ : syracuseStep 284681 = 213511) B213511
theorem B874585 : Blo 167798 874585 := bstep (se 2 (by rfl) ⟨327969, by rfl⟩ : syracuseStep 874585 = 655939) B655939
theorem B284843 : Blo 167798 284843 := bstep (se 1 (by rfl) ⟨213632, by rfl⟩ : syracuseStep 284843 = 427265) B427265
theorem B383147 : Blo 167798 383147 := bstep (se 1 (by rfl) ⟨287360, by rfl⟩ : syracuseStep 383147 = 574721) B574721
theorem B612737 : Blo 167798 612737 := bstep (se 2 (by rfl) ⟨229776, by rfl⟩ : syracuseStep 612737 = 459553) B459553
theorem B252335 : Blo 167798 252335 := bstep (se 1 (by rfl) ⟨189251, by rfl⟩ : syracuseStep 252335 = 378503) B378503
theorem B612809 : Blo 167798 612809 := bstep (se 2 (by rfl) ⟨229803, by rfl⟩ : syracuseStep 612809 = 459607) B459607
theorem B252425 : Blo 167798 252425 := bstep (se 2 (by rfl) ⟨94659, by rfl⟩ : syracuseStep 252425 = 189319) B189319
theorem B481801 : Blo 167798 481801 := bstep (se 2 (by rfl) ⟨180675, by rfl⟩ : syracuseStep 481801 = 361351) B361351
theorem B252455 : Blo 167798 252455 := bstep (se 1 (by rfl) ⟨189341, by rfl⟩ : syracuseStep 252455 = 378683) B378683
theorem B285241 : Blo 167798 285241 := bstep (se 2 (by rfl) ⟨106965, by rfl⟩ : syracuseStep 285241 = 213931) B213931
theorem B252539 : Blo 167798 252539 := bstep (se 1 (by rfl) ⟨189404, by rfl⟩ : syracuseStep 252539 = 378809) B378809
theorem B285383 : Blo 167798 285383 := bstep (se 1 (by rfl) ⟨214037, by rfl⟩ : syracuseStep 285383 = 428075) B428075
theorem B383687 : Blo 167798 383687 := bstep (se 1 (by rfl) ⟨287765, by rfl⟩ : syracuseStep 383687 = 575531) B575531
theorem B252665 : Blo 167798 252665 := bstep (se 2 (by rfl) ⟨94749, by rfl⟩ : syracuseStep 252665 = 189499) B189499
theorem B252767 : Blo 167798 252767 := bstep (se 1 (by rfl) ⟨189575, by rfl⟩ : syracuseStep 252767 = 379151) B379151
theorem B285545 : Blo 167798 285545 := bstep (se 2 (by rfl) ⟨107079, by rfl⟩ : syracuseStep 285545 = 214159) B214159
theorem B252779 : Blo 167798 252779 := bstep (se 1 (by rfl) ⟨189584, by rfl⟩ : syracuseStep 252779 = 379169) B379169
theorem B253007 : Blo 167798 253007 := bstep (se 1 (by rfl) ⟨189755, by rfl⟩ : syracuseStep 253007 = 379511) B379511
theorem B253127 : Blo 167798 253127 := bstep (se 1 (by rfl) ⟨189845, by rfl⟩ : syracuseStep 253127 = 379691) B379691
theorem B285943 : Blo 167798 285943 := bstep (se 1 (by rfl) ⟨214457, by rfl⟩ : syracuseStep 285943 = 428915) B428915
theorem B646487 : Blo 167798 646487 := bstep (se 1 (by rfl) ⟨484865, by rfl⟩ : syracuseStep 646487 = 969731) B969731
theorem B253289 : Blo 167798 253289 := bstep (se 2 (by rfl) ⟨94983, by rfl⟩ : syracuseStep 253289 = 189967) B189967
theorem B482689 : Blo 167798 482689 := bstep (se 2 (by rfl) ⟨181008, by rfl⟩ : syracuseStep 482689 = 362017) B362017
theorem B253367 : Blo 167798 253367 := bstep (se 1 (by rfl) ⟨190025, by rfl⟩ : syracuseStep 253367 = 380051) B380051
theorem B318907 : Blo 167798 318907 := bstep (se 1 (by rfl) ⟨239180, by rfl⟩ : syracuseStep 318907 = 478361) B478361
theorem B286139 : Blo 167798 286139 := bstep (se 1 (by rfl) ⟨214604, by rfl⟩ : syracuseStep 286139 = 429209) B429209
theorem B253403 : Blo 167798 253403 := bstep (se 1 (by rfl) ⟨190052, by rfl⟩ : syracuseStep 253403 = 380105) B380105
theorem B286247 : Blo 167798 286247 := bstep (se 1 (by rfl) ⟨214685, by rfl⟩ : syracuseStep 286247 = 429371) B429371
theorem B384551 : Blo 167798 384551 := bstep (se 1 (by rfl) ⟨288413, by rfl⟩ : syracuseStep 384551 = 576827) B576827
theorem B286537 : Blo 167798 286537 := bstep (se 2 (by rfl) ⟨107451, by rfl⟩ : syracuseStep 286537 = 214903) B214903
theorem B286571 : Blo 167798 286571 := bstep (se 1 (by rfl) ⟨214928, by rfl⟩ : syracuseStep 286571 = 429857) B429857
theorem B384875 : Blo 167798 384875 := bstep (se 1 (by rfl) ⟨288656, by rfl⟩ : syracuseStep 384875 = 577313) B577313
theorem B319393 : Blo 167798 319393 := bstep (se 2 (by rfl) ⟨119772, by rfl⟩ : syracuseStep 319393 = 239545) B239545
theorem B384929 : Blo 167798 384929 := bstep (se 2 (by rfl) ⟨144348, by rfl⟩ : syracuseStep 384929 = 288697) B288697
theorem B253871 : Blo 167798 253871 := bstep (se 1 (by rfl) ⟨190403, by rfl⟩ : syracuseStep 253871 = 380807) B380807
theorem B483259 : Blo 167798 483259 := bstep (se 1 (by rfl) ⟨362444, by rfl⟩ : syracuseStep 483259 = 724889) B724889
theorem B974855 : Blo 167798 974855 := bstep (se 1 (by rfl) ⟨731141, by rfl⟩ : syracuseStep 974855 = 1462283) B1462283
theorem B253961 : Blo 167798 253961 := bstep (se 2 (by rfl) ⟨95235, by rfl⟩ : syracuseStep 253961 = 190471) B190471
theorem B1466383 : Blo 167798 1466383 := bstep (se 1 (by rfl) ⟨1099787, by rfl⟩ : syracuseStep 1466383 = 2199575) B2199575
theorem B253991 : Blo 167798 253991 := bstep (se 1 (by rfl) ⟨190493, by rfl⟩ : syracuseStep 253991 = 380987) B380987
theorem B254075 : Blo 167798 254075 := bstep (se 1 (by rfl) ⟨190556, by rfl⟩ : syracuseStep 254075 = 381113) B381113
theorem B385271 : Blo 167798 385271 := bstep (se 1 (by rfl) ⟨288953, by rfl⟩ : syracuseStep 385271 = 577907) B577907
theorem B254201 : Blo 167798 254201 := bstep (se 2 (by rfl) ⟨95325, by rfl⟩ : syracuseStep 254201 = 190651) B190651
theorem B286969 : Blo 167798 286969 := bstep (se 2 (by rfl) ⟨107613, by rfl⟩ : syracuseStep 286969 = 215227) B215227
theorem B254303 : Blo 167798 254303 := bstep (se 1 (by rfl) ⟨190727, by rfl⟩ : syracuseStep 254303 = 381455) B381455
theorem B254315 : Blo 167798 254315 := bstep (se 1 (by rfl) ⟨190736, by rfl⟩ : syracuseStep 254315 = 381473) B381473
theorem B319963 : Blo 167798 319963 := bstep (se 1 (by rfl) ⟨239972, by rfl⟩ : syracuseStep 319963 = 479945) B479945
theorem B287239 : Blo 167798 287239 := bstep (se 1 (by rfl) ⟨215429, by rfl⟩ : syracuseStep 287239 = 430859) B430859
theorem B254543 : Blo 167798 254543 := bstep (se 1 (by rfl) ⟨190907, by rfl⟩ : syracuseStep 254543 = 381815) B381815
theorem B647777 : Blo 167798 647777 := bstep (se 2 (by rfl) ⟨242916, by rfl⟩ : syracuseStep 647777 = 485833) B485833
theorem B1172141 : Blo 167798 1172141 := bstep (se 3 (by rfl) ⟨219776, by rfl⟩ : syracuseStep 1172141 = 439553) B439553
theorem B254663 : Blo 167798 254663 := bstep (se 1 (by rfl) ⟨190997, by rfl⟩ : syracuseStep 254663 = 381995) B381995
theorem B549575 : Blo 167798 549575 := bstep (se 1 (by rfl) ⟨412181, by rfl⟩ : syracuseStep 549575 = 824363) B824363
theorem B549587 : Blo 167798 549587 := bstep (se 1 (by rfl) ⟨412190, by rfl⟩ : syracuseStep 549587 = 824381) B824381
theorem B385865 : Blo 167798 385865 := bstep (se 2 (by rfl) ⟨144699, by rfl⟩ : syracuseStep 385865 = 289399) B289399
theorem B254825 : Blo 167798 254825 := bstep (se 2 (by rfl) ⟨95559, by rfl⟩ : syracuseStep 254825 = 191119) B191119
theorem B287671 : Blo 167798 287671 := bstep (se 1 (by rfl) ⟨215753, by rfl⟩ : syracuseStep 287671 = 431507) B431507
theorem B254903 : Blo 167798 254903 := bstep (se 1 (by rfl) ⟨191177, by rfl⟩ : syracuseStep 254903 = 382355) B382355
theorem B254939 : Blo 167798 254939 := bstep (se 1 (by rfl) ⟨191204, by rfl⟩ : syracuseStep 254939 = 382409) B382409
theorem B681041 : Blo 167798 681041 := bstep (se 2 (by rfl) ⟨255390, by rfl⟩ : syracuseStep 681041 = 510781) B510781
theorem B287867 : Blo 167798 287867 := bstep (se 1 (by rfl) ⟨215900, by rfl⟩ : syracuseStep 287867 = 431801) B431801
theorem B976151 : Blo 167798 976151 := bstep (se 1 (by rfl) ⟨732113, by rfl⟩ : syracuseStep 976151 = 1464227) B1464227
theorem B255407 : Blo 167798 255407 := bstep (se 1 (by rfl) ⟨191555, by rfl⟩ : syracuseStep 255407 = 383111) B383111
theorem B255497 : Blo 167798 255497 := bstep (se 2 (by rfl) ⟨95811, by rfl⟩ : syracuseStep 255497 = 191623) B191623
theorem B288265 : Blo 167798 288265 := bstep (se 2 (by rfl) ⟨108099, by rfl⟩ : syracuseStep 288265 = 216199) B216199
theorem B255527 : Blo 167798 255527 := bstep (se 1 (by rfl) ⟨191645, by rfl⟩ : syracuseStep 255527 = 383291) B383291
theorem B190075 : Blo 167798 190075 := bstep (se 1 (by rfl) ⟨142556, by rfl⟩ : syracuseStep 190075 = 285113) B285113
theorem B255611 : Blo 167798 255611 := bstep (se 1 (by rfl) ⟨191708, by rfl⟩ : syracuseStep 255611 = 383417) B383417
theorem B288427 : Blo 167798 288427 := bstep (se 1 (by rfl) ⟨216320, by rfl⟩ : syracuseStep 288427 = 432641) B432641
theorem B255737 : Blo 167798 255737 := bstep (se 2 (by rfl) ⟨95901, by rfl⟩ : syracuseStep 255737 = 191803) B191803
theorem B255839 : Blo 167798 255839 := bstep (se 1 (by rfl) ⟨191879, by rfl⟩ : syracuseStep 255839 = 383759) B383759
theorem B255851 : Blo 167798 255851 := bstep (se 1 (by rfl) ⟨191888, by rfl⟩ : syracuseStep 255851 = 383777) B383777
theorem B1730413 : Blo 167798 1730413 := bstep (se 3 (by rfl) ⟨324452, by rfl⟩ : syracuseStep 1730413 = 648905) B648905
theorem B288731 : Blo 167798 288731 := bstep (se 1 (by rfl) ⟨216548, by rfl⟩ : syracuseStep 288731 = 433097) B433097
theorem B649235 : Blo 167798 649235 := bstep (se 1 (by rfl) ⟨486926, by rfl⟩ : syracuseStep 649235 = 973853) B973853
theorem B190543 : Blo 167798 190543 := bstep (se 1 (by rfl) ⟨142907, by rfl⟩ : syracuseStep 190543 = 285815) B285815
theorem B256079 : Blo 167798 256079 := bstep (se 1 (by rfl) ⟨192059, by rfl⟩ : syracuseStep 256079 = 384119) B384119
theorem B256199 : Blo 167798 256199 := bstep (se 1 (by rfl) ⟨192149, by rfl⟩ : syracuseStep 256199 = 384299) B384299
theorem B288967 : Blo 167798 288967 := bstep (se 1 (by rfl) ⟨216725, by rfl⟩ : syracuseStep 288967 = 433451) B433451
theorem B1927475 : Blo 167798 1927475 := bstep (se 1 (by rfl) ⟨1445606, by rfl⟩ : syracuseStep 1927475 = 2891213) B2891213
theorem B256361 : Blo 167798 256361 := bstep (se 2 (by rfl) ⟨96135, by rfl⟩ : syracuseStep 256361 = 192271) B192271
theorem B289129 : Blo 167798 289129 := bstep (se 2 (by rfl) ⟨108423, by rfl⟩ : syracuseStep 289129 = 216847) B216847
theorem B256439 : Blo 167798 256439 := bstep (se 1 (by rfl) ⟨192329, by rfl⟩ : syracuseStep 256439 = 384659) B384659
theorem B190939 : Blo 167798 190939 := bstep (se 1 (by rfl) ⟨143204, by rfl⟩ : syracuseStep 190939 = 286409) B286409
theorem B256475 : Blo 167798 256475 := bstep (se 1 (by rfl) ⟨192356, by rfl⟩ : syracuseStep 256475 = 384713) B384713
theorem B649691 : Blo 167798 649691 := bstep (se 1 (by rfl) ⟨487268, by rfl⟩ : syracuseStep 649691 = 974537) B974537
theorem B322127 : Blo 167798 322127 := bstep (se 1 (by rfl) ⟨241595, by rfl⟩ : syracuseStep 322127 = 483191) B483191
theorem B486137 : Blo 167798 486137 := bstep (se 2 (by rfl) ⟨182301, by rfl⟩ : syracuseStep 486137 = 364603) B364603
theorem B977771 : Blo 167798 977771 := bstep (se 1 (by rfl) ⟨733328, by rfl⟩ : syracuseStep 977771 = 1466657) B1466657
theorem B191407 : Blo 167798 191407 := bstep (se 1 (by rfl) ⟨143555, by rfl⟩ : syracuseStep 191407 = 287111) B287111
theorem B256943 : Blo 167798 256943 := bstep (se 1 (by rfl) ⟨192707, by rfl⟩ : syracuseStep 256943 = 385415) B385415
theorem B289723 : Blo 167798 289723 := bstep (se 1 (by rfl) ⟨217292, by rfl⟩ : syracuseStep 289723 = 434585) B434585
theorem B257033 : Blo 167798 257033 := bstep (se 2 (by rfl) ⟨96387, by rfl⟩ : syracuseStep 257033 = 192775) B192775
theorem B257063 : Blo 167798 257063 := bstep (se 1 (by rfl) ⟨192797, by rfl⟩ : syracuseStep 257063 = 385595) B385595
theorem B289831 : Blo 167798 289831 := bstep (se 1 (by rfl) ⟨217373, by rfl⟩ : syracuseStep 289831 = 434747) B434747
theorem B257147 : Blo 167798 257147 := bstep (se 1 (by rfl) ⟨192860, by rfl⟩ : syracuseStep 257147 = 385721) B385721
theorem B257273 : Blo 167798 257273 := bstep (se 2 (by rfl) ⟨96477, by rfl⟩ : syracuseStep 257273 = 192955) B192955
theorem B191839 : Blo 167798 191839 := bstep (se 1 (by rfl) ⟨143879, by rfl⟩ : syracuseStep 191839 = 287759) B287759
theorem B257375 : Blo 167798 257375 := bstep (se 1 (by rfl) ⟨193031, by rfl⟩ : syracuseStep 257375 = 386063) B386063
theorem B257387 : Blo 167798 257387 := bstep (se 1 (by rfl) ⟨193040, by rfl⟩ : syracuseStep 257387 = 386081) B386081
theorem B1437101 : Blo 167798 1437101 := bstep (se 3 (by rfl) ⟨269456, by rfl⟩ : syracuseStep 1437101 = 538913) B538913
theorem B1174985 : Blo 167798 1174985 := bstep (se 2 (by rfl) ⟨440619, by rfl⟩ : syracuseStep 1174985 = 881239) B881239
theorem B880091 : Blo 167798 880091 := bstep (se 1 (by rfl) ⟨660068, by rfl⟩ : syracuseStep 880091 = 1320137) B1320137
theorem B1076723 : Blo 167798 1076723 := bstep (se 1 (by rfl) ⟨807542, by rfl⟩ : syracuseStep 1076723 = 1615085) B1615085
theorem B323129 : Blo 167798 323129 := bstep (se 2 (by rfl) ⟨121173, by rfl⟩ : syracuseStep 323129 = 242347) B242347
theorem B257615 : Blo 167798 257615 := bstep (se 1 (by rfl) ⟨193211, by rfl⟩ : syracuseStep 257615 = 386423) B386423
theorem B650875 : Blo 167798 650875 := bstep (se 1 (by rfl) ⟨488156, by rfl⟩ : syracuseStep 650875 = 976313) B976313
theorem B290503 : Blo 167798 290503 := bstep (se 1 (by rfl) ⟨217877, by rfl⟩ : syracuseStep 290503 = 435755) B435755
theorem B192199 : Blo 167798 192199 := bstep (se 1 (by rfl) ⟨144149, by rfl⟩ : syracuseStep 192199 = 288299) B288299
theorem B519929 : Blo 167798 519929 := bstep (se 2 (by rfl) ⟨194973, by rfl⟩ : syracuseStep 519929 = 389947) B389947
theorem B520111 : Blo 167798 520111 := bstep (se 1 (by rfl) ⟨390083, by rfl⟩ : syracuseStep 520111 = 780167) B780167
theorem B683959 : Blo 167798 683959 := bstep (se 1 (by rfl) ⟨512969, by rfl⟩ : syracuseStep 683959 = 1025939) B1025939
theorem B193063 : Blo 167798 193063 := bstep (se 1 (by rfl) ⟨144797, by rfl⟩ : syracuseStep 193063 = 289595) B289595
theorem B913979 : Blo 167798 913979 := bstep (se 1 (by rfl) ⟨685484, by rfl⟩ : syracuseStep 913979 = 1370969) B1370969
theorem B652151 : Blo 167798 652151 := bstep (se 1 (by rfl) ⟨489113, by rfl⟩ : syracuseStep 652151 = 978227) B978227
theorem B2717093 : Blo 167798 2717093 := bstep (se 4 (by rfl) ⟨254727, by rfl⟩ : syracuseStep 2717093 = 509455) B509455
theorem B325127 : Blo 167798 325127 := bstep (se 1 (by rfl) ⟨243845, by rfl⟩ : syracuseStep 325127 = 487691) B487691
theorem B488999 : Blo 167798 488999 := bstep (se 1 (by rfl) ⟨366749, by rfl⟩ : syracuseStep 488999 = 733499) B733499
theorem B489149 : Blo 167798 489149 := bstep (se 3 (by rfl) ⟨91715, by rfl⟩ : syracuseStep 489149 = 183431) B183431
theorem B456623 : Blo 167798 456623 := bstep (se 1 (by rfl) ⟨342467, by rfl⟩ : syracuseStep 456623 = 684935) B684935
theorem B325559 : Blo 167798 325559 := bstep (se 1 (by rfl) ⟨244169, by rfl⟩ : syracuseStep 325559 = 488339) B488339
theorem B849851 : Blo 167798 849851 := bstep (se 1 (by rfl) ⟨637388, by rfl⟩ : syracuseStep 849851 = 1274777) B1274777
theorem B325711 : Blo 167798 325711 := bstep (se 1 (by rfl) ⟨244283, by rfl⟩ : syracuseStep 325711 = 488567) B488567
theorem B424865 : Blo 167798 424865 := bstep (se 2 (by rfl) ⟨159324, by rfl⟩ : syracuseStep 424865 = 318649) B318649
theorem B261083 : Blo 167798 261083 := bstep (se 1 (by rfl) ⟨195812, by rfl⟩ : syracuseStep 261083 = 391625) B391625
theorem B1309661 : Blo 167798 1309661 := bstep (se 3 (by rfl) ⟨245561, by rfl⟩ : syracuseStep 1309661 = 491123) B491123
theorem B1080515 : Blo 167798 1080515 := bstep (se 1 (by rfl) ⟨810386, by rfl⟩ : syracuseStep 1080515 = 1620773) B1620773
theorem B851147 : Blo 167798 851147 := bstep (se 1 (by rfl) ⟨638360, by rfl⟩ : syracuseStep 851147 = 1276721) B1276721
theorem B1277207 : Blo 167798 1277207 := bstep (se 1 (by rfl) ⟨957905, by rfl⟩ : syracuseStep 1277207 = 1915811) B1915811
theorem B425321 : Blo 167798 425321 := bstep (se 2 (by rfl) ⟨159495, by rfl⟩ : syracuseStep 425321 = 318991) B318991
theorem B7044569 : Blo 167798 7044569 := bstep (se 2 (by rfl) ⟨2641713, by rfl⟩ : syracuseStep 7044569 = 5283427) B5283427
theorem B622511 : Blo 167798 622511 := bstep (se 1 (by rfl) ⟨466883, by rfl⟩ : syracuseStep 622511 = 933767) B933767
theorem B1343699 : Blo 167798 1343699 := bstep (se 1 (by rfl) ⟨1007774, by rfl⟩ : syracuseStep 1343699 = 2015549) B2015549
theorem B3277219 : Blo 167798 3277219 := bstep (se 1 (by rfl) ⟨2457914, by rfl⟩ : syracuseStep 3277219 = 4915829) B4915829
theorem B852443 : Blo 167798 852443 := bstep (se 1 (by rfl) ⟨639332, by rfl⟩ : syracuseStep 852443 = 1278665) B1278665
theorem B426617 : Blo 167798 426617 := bstep (se 2 (by rfl) ⟨159981, by rfl⟩ : syracuseStep 426617 = 319963) B319963
theorem B426667 : Blo 167798 426667 := bstep (se 1 (by rfl) ⟨320000, by rfl⟩ : syracuseStep 426667 = 640001) B640001
theorem B852929 : Blo 167798 852929 := bstep (se 2 (by rfl) ⟨319848, by rfl⟩ : syracuseStep 852929 = 639697) B639697
theorem B426971 : Blo 167798 426971 := bstep (se 1 (by rfl) ⟨320228, by rfl⟩ : syracuseStep 426971 = 640457) B640457
theorem B5506319 : Blo 167798 5506319 := bstep (se 1 (by rfl) ⟨4129739, by rfl⟩ : syracuseStep 5506319 = 8259479) B8259479
theorem B427295 : Blo 167798 427295 := bstep (se 1 (by rfl) ⟨320471, by rfl⟩ : syracuseStep 427295 = 640943) B640943
theorem B230747 : Blo 167798 230747 := bstep (se 1 (by rfl) ⟨173060, by rfl⟩ : syracuseStep 230747 = 346121) B346121
theorem B1082747 : Blo 167798 1082747 := bstep (se 1 (by rfl) ⟨812060, by rfl⟩ : syracuseStep 1082747 = 1624121) B1624121
theorem B1934765 : Blo 167798 1934765 := bstep (se 3 (by rfl) ⟨362768, by rfl⟩ : syracuseStep 1934765 = 725537) B725537
theorem B2197115 : Blo 167798 2197115 := bstep (se 1 (by rfl) ⟨1647836, by rfl⟩ : syracuseStep 2197115 = 3295673) B3295673
theorem B362171 : Blo 167798 362171 := bstep (se 1 (by rfl) ⟨271628, by rfl⟩ : syracuseStep 362171 = 543257) B543257
theorem B1574927 : Blo 167798 1574927 := bstep (se 1 (by rfl) ⟨1181195, by rfl⟩ : syracuseStep 1574927 = 2362391) B2362391
theorem B493697 : Blo 167798 493697 := bstep (se 2 (by rfl) ⟨185136, by rfl⟩ : syracuseStep 493697 = 370273) B370273
theorem B428399 : Blo 167798 428399 := bstep (se 1 (by rfl) ⟨321299, by rfl⟩ : syracuseStep 428399 = 642599) B642599
theorem B363179 : Blo 167798 363179 := bstep (se 1 (by rfl) ⟨272384, by rfl⟩ : syracuseStep 363179 = 544769) B544769
theorem B429047 : Blo 167798 429047 := bstep (se 1 (by rfl) ⟨321785, by rfl⟩ : syracuseStep 429047 = 643571) B643571
theorem B658651 : Blo 167798 658651 := bstep (se 1 (by rfl) ⟨493988, by rfl⟩ : syracuseStep 658651 = 987977) B987977
theorem B691487 : Blo 167798 691487 := bstep (se 1 (by rfl) ⟨518615, by rfl⟩ : syracuseStep 691487 = 1037231) B1037231
theorem B462419 : Blo 167798 462419 := bstep (se 1 (by rfl) ⟨346814, by rfl⟩ : syracuseStep 462419 = 693629) B693629
theorem B1085231 : Blo 167798 1085231 := bstep (se 1 (by rfl) ⟨813923, by rfl⟩ : syracuseStep 1085231 = 1627847) B1627847
theorem B2330477 : Blo 167798 2330477 := bstep (se 3 (by rfl) ⟨436964, by rfl⟩ : syracuseStep 2330477 = 873929) B873929
theorem B167835 : Blo 167798 167835 := bstep (se 1 (by rfl) ⟨125876, by rfl⟩ : syracuseStep 167835 = 251753) B251753
theorem B167887 : Blo 167798 167887 := bstep (se 1 (by rfl) ⟨125915, by rfl⟩ : syracuseStep 167887 = 251831) B251831
theorem B364495 : Blo 167798 364495 := bstep (se 1 (by rfl) ⟨273371, by rfl⟩ : syracuseStep 364495 = 546743) B546743
theorem B167911 : Blo 167798 167911 := bstep (se 1 (by rfl) ⟨125933, by rfl⟩ : syracuseStep 167911 = 251867) B251867
theorem B856169 : Blo 167798 856169 := bstep (se 2 (by rfl) ⟨321063, by rfl⟩ : syracuseStep 856169 = 642127) B642127
theorem B168223 : Blo 167798 168223 := bstep (se 1 (by rfl) ⟨126167, by rfl⟩ : syracuseStep 168223 = 252335) B252335
theorem B168283 : Blo 167798 168283 := bstep (se 1 (by rfl) ⟨126212, by rfl⟩ : syracuseStep 168283 = 252425) B252425
theorem B463195 : Blo 167798 463195 := bstep (se 1 (by rfl) ⟨347396, by rfl⟩ : syracuseStep 463195 = 694793) B694793
theorem B168303 : Blo 167798 168303 := bstep (se 1 (by rfl) ⟨126227, by rfl⟩ : syracuseStep 168303 = 252455) B252455
theorem B9802133 : Blo 167798 9802133 := bstep (se 6 (by rfl) ⟨229737, by rfl⟩ : syracuseStep 9802133 = 459475) B459475
theorem B168359 : Blo 167798 168359 := bstep (se 1 (by rfl) ⟨126269, by rfl⟩ : syracuseStep 168359 = 252539) B252539
theorem B168443 : Blo 167798 168443 := bstep (se 1 (by rfl) ⟨126332, by rfl⟩ : syracuseStep 168443 = 252665) B252665
theorem B168511 : Blo 167798 168511 := bstep (se 1 (by rfl) ⟨126383, by rfl⟩ : syracuseStep 168511 = 252767) B252767
theorem B168519 : Blo 167798 168519 := bstep (se 1 (by rfl) ⟨126389, by rfl⟩ : syracuseStep 168519 = 252779) B252779
theorem B1446497 : Blo 167798 1446497 := bstep (se 2 (by rfl) ⟨542436, by rfl⟩ : syracuseStep 1446497 = 1084873) B1084873
theorem B168671 : Blo 167798 168671 := bstep (se 1 (by rfl) ⟨126503, by rfl⟩ : syracuseStep 168671 = 253007) B253007
theorem B168751 : Blo 167798 168751 := bstep (se 1 (by rfl) ⟨126563, by rfl⟩ : syracuseStep 168751 = 253127) B253127
theorem B430991 : Blo 167798 430991 := bstep (se 1 (by rfl) ⟨323243, by rfl⟩ : syracuseStep 430991 = 646487) B646487
theorem B168859 : Blo 167798 168859 := bstep (se 1 (by rfl) ⟨126644, by rfl⟩ : syracuseStep 168859 = 253289) B253289
theorem B168911 : Blo 167798 168911 := bstep (se 1 (by rfl) ⟨126683, by rfl⟩ : syracuseStep 168911 = 253367) B253367
theorem B168935 : Blo 167798 168935 := bstep (se 1 (by rfl) ⟨126701, by rfl⟩ : syracuseStep 168935 = 253403) B253403
theorem B857303 : Blo 167798 857303 := bstep (se 1 (by rfl) ⟨642977, by rfl⟩ : syracuseStep 857303 = 1285955) B1285955
theorem B693481 : Blo 167798 693481 := bstep (se 2 (by rfl) ⟨260055, by rfl⟩ : syracuseStep 693481 = 520111) B520111
theorem B169247 : Blo 167798 169247 := bstep (se 1 (by rfl) ⟨126935, by rfl⟩ : syracuseStep 169247 = 253871) B253871
theorem B169307 : Blo 167798 169307 := bstep (se 1 (by rfl) ⟨126980, by rfl⟩ : syracuseStep 169307 = 253961) B253961
theorem B169327 : Blo 167798 169327 := bstep (se 1 (by rfl) ⟨126995, by rfl⟩ : syracuseStep 169327 = 253991) B253991
theorem B169383 : Blo 167798 169383 := bstep (se 1 (by rfl) ⟨127037, by rfl⟩ : syracuseStep 169383 = 254075) B254075
theorem B169467 : Blo 167798 169467 := bstep (se 1 (by rfl) ⟨127100, by rfl⟩ : syracuseStep 169467 = 254201) B254201
theorem B169535 : Blo 167798 169535 := bstep (se 1 (by rfl) ⟨127151, by rfl⟩ : syracuseStep 169535 = 254303) B254303
theorem B169543 : Blo 167798 169543 := bstep (se 1 (by rfl) ⟨127157, by rfl⟩ : syracuseStep 169543 = 254315) B254315
theorem B169695 : Blo 167798 169695 := bstep (se 1 (by rfl) ⟨127271, by rfl⟩ : syracuseStep 169695 = 254543) B254543
theorem B431851 : Blo 167798 431851 := bstep (se 1 (by rfl) ⟨323888, by rfl⟩ : syracuseStep 431851 = 647777) B647777
theorem B169775 : Blo 167798 169775 := bstep (se 1 (by rfl) ⟨127331, by rfl⟩ : syracuseStep 169775 = 254663) B254663
theorem B366383 : Blo 167798 366383 := bstep (se 1 (by rfl) ⟨274787, by rfl⟩ : syracuseStep 366383 = 549575) B549575
theorem B366391 : Blo 167798 366391 := bstep (se 1 (by rfl) ⟨274793, by rfl⟩ : syracuseStep 366391 = 549587) B549587
theorem B169883 : Blo 167798 169883 := bstep (se 1 (by rfl) ⟨127412, by rfl⟩ : syracuseStep 169883 = 254825) B254825
theorem B169935 : Blo 167798 169935 := bstep (se 1 (by rfl) ⟨127451, by rfl⟩ : syracuseStep 169935 = 254903) B254903
theorem B169959 : Blo 167798 169959 := bstep (se 1 (by rfl) ⟨127469, by rfl⟩ : syracuseStep 169959 = 254939) B254939
theorem B170271 : Blo 167798 170271 := bstep (se 1 (by rfl) ⟨127703, by rfl⟩ : syracuseStep 170271 = 255407) B255407
theorem B170331 : Blo 167798 170331 := bstep (se 1 (by rfl) ⟨127748, by rfl⟩ : syracuseStep 170331 = 255497) B255497
theorem B170351 : Blo 167798 170351 := bstep (se 1 (by rfl) ⟨127763, by rfl⟩ : syracuseStep 170351 = 255527) B255527
theorem B170407 : Blo 167798 170407 := bstep (se 1 (by rfl) ⟨127805, by rfl⟩ : syracuseStep 170407 = 255611) B255611
theorem B170491 : Blo 167798 170491 := bstep (se 1 (by rfl) ⟨127868, by rfl⟩ : syracuseStep 170491 = 255737) B255737
theorem B170559 : Blo 167798 170559 := bstep (se 1 (by rfl) ⟨127919, by rfl⟩ : syracuseStep 170559 = 255839) B255839
theorem B170567 : Blo 167798 170567 := bstep (se 1 (by rfl) ⟨127925, by rfl⟩ : syracuseStep 170567 = 255851) B255851
theorem B432823 : Blo 167798 432823 := bstep (se 1 (by rfl) ⟨324617, by rfl⟩ : syracuseStep 432823 = 649235) B649235
theorem B170719 : Blo 167798 170719 := bstep (se 1 (by rfl) ⟨128039, by rfl⟩ : syracuseStep 170719 = 256079) B256079
theorem B170799 : Blo 167798 170799 := bstep (se 1 (by rfl) ⟨128099, by rfl⟩ : syracuseStep 170799 = 256199) B256199
theorem B1284983 : Blo 167798 1284983 := bstep (se 1 (by rfl) ⟨963737, by rfl⟩ : syracuseStep 1284983 = 1927475) B1927475
theorem B170907 : Blo 167798 170907 := bstep (se 1 (by rfl) ⟨128180, by rfl⟩ : syracuseStep 170907 = 256361) B256361
theorem B170959 : Blo 167798 170959 := bstep (se 1 (by rfl) ⟨128219, by rfl⟩ : syracuseStep 170959 = 256439) B256439
theorem B170983 : Blo 167798 170983 := bstep (se 1 (by rfl) ⟨128237, by rfl⟩ : syracuseStep 170983 = 256475) B256475
theorem B433127 : Blo 167798 433127 := bstep (se 1 (by rfl) ⟨324845, by rfl⟩ : syracuseStep 433127 = 649691) B649691
theorem B728203 : Blo 167798 728203 := bstep (se 1 (by rfl) ⟨546152, by rfl⟩ : syracuseStep 728203 = 1092305) B1092305
theorem B171295 : Blo 167798 171295 := bstep (se 1 (by rfl) ⟨128471, by rfl⟩ : syracuseStep 171295 = 256943) B256943
theorem B171355 : Blo 167798 171355 := bstep (se 1 (by rfl) ⟨128516, by rfl⟩ : syracuseStep 171355 = 257033) B257033
theorem B171375 : Blo 167798 171375 := bstep (se 1 (by rfl) ⟨128531, by rfl⟩ : syracuseStep 171375 = 257063) B257063
theorem B171431 : Blo 167798 171431 := bstep (se 1 (by rfl) ⟨128573, by rfl⟩ : syracuseStep 171431 = 257147) B257147
theorem B171515 : Blo 167798 171515 := bstep (se 1 (by rfl) ⟨128636, by rfl⟩ : syracuseStep 171515 = 257273) B257273
theorem B171583 : Blo 167798 171583 := bstep (se 1 (by rfl) ⟨128687, by rfl⟩ : syracuseStep 171583 = 257375) B257375
theorem B171591 : Blo 167798 171591 := bstep (se 1 (by rfl) ⟨128693, by rfl⟩ : syracuseStep 171591 = 257387) B257387
theorem B958067 : Blo 167798 958067 := bstep (se 1 (by rfl) ⟨718550, by rfl⟩ : syracuseStep 958067 = 1437101) B1437101
theorem B171743 : Blo 167798 171743 := bstep (se 1 (by rfl) ⟨128807, by rfl⟩ : syracuseStep 171743 = 257615) B257615
theorem B728939 : Blo 167798 728939 := bstep (se 1 (by rfl) ⟨546704, by rfl⟩ : syracuseStep 728939 = 1093409) B1093409
theorem B696221 : Blo 167798 696221 := bstep (se 3 (by rfl) ⟨130541, by rfl⟩ : syracuseStep 696221 = 261083) B261083
theorem B860219 : Blo 167798 860219 := bstep (se 1 (by rfl) ⟨645164, by rfl⟩ : syracuseStep 860219 = 1290329) B1290329
theorem B434281 : Blo 167798 434281 := bstep (se 2 (by rfl) ⟨162855, by rfl⟩ : syracuseStep 434281 = 325711) B325711
theorem B270911 : Blo 167798 270911 := bstep (se 1 (by rfl) ⟨203183, by rfl⟩ : syracuseStep 270911 = 406367) B406367
theorem B434767 : Blo 167798 434767 := bstep (se 1 (by rfl) ⟨326075, by rfl⟩ : syracuseStep 434767 = 652151) B652151
theorem B1844045 : Blo 167798 1844045 := bstep (se 3 (by rfl) ⟨345758, by rfl⟩ : syracuseStep 1844045 = 691517) B691517
theorem B1811395 : Blo 167798 1811395 := bstep (se 1 (by rfl) ⟨1358546, by rfl⟩ : syracuseStep 1811395 = 2717093) B2717093
theorem B861191 : Blo 167798 861191 := bstep (se 1 (by rfl) ⟨645893, by rfl⟩ : syracuseStep 861191 = 1291787) B1291787
theorem B959525 : Blo 167798 959525 := bstep (se 4 (by rfl) ⟨89955, by rfl⟩ : syracuseStep 959525 = 179911) B179911
theorem B1025257 : Blo 167798 1025257 := bstep (se 2 (by rfl) ⟨384471, by rfl⟩ : syracuseStep 1025257 = 768943) B768943
theorem B304415 : Blo 167798 304415 := bstep (se 1 (by rfl) ⟨228311, by rfl⟩ : syracuseStep 304415 = 456623) B456623
theorem B566567 : Blo 167798 566567 := bstep (se 1 (by rfl) ⟨424925, by rfl⟩ : syracuseStep 566567 = 849851) B849851
theorem B861677 : Blo 167798 861677 := bstep (se 3 (by rfl) ⟨161564, by rfl⟩ : syracuseStep 861677 = 323129) B323129
theorem B1648451 : Blo 167798 1648451 := bstep (se 1 (by rfl) ⟨1236338, by rfl⟩ : syracuseStep 1648451 = 2472677) B2472677
theorem B567431 : Blo 167798 567431 := bstep (se 1 (by rfl) ⟨425573, by rfl⟩ : syracuseStep 567431 = 851147) B851147
theorem B1288385 : Blo 167798 1288385 := bstep (se 2 (by rfl) ⟨483144, by rfl⟩ : syracuseStep 1288385 = 966289) B966289
theorem B862487 : Blo 167798 862487 := bstep (se 1 (by rfl) ⟨646865, by rfl⟩ : syracuseStep 862487 = 1293731) B1293731
theorem B4696379 : Blo 167798 4696379 := bstep (se 1 (by rfl) ⟨3522284, by rfl⟩ : syracuseStep 4696379 = 7044569) B7044569
theorem B404041 : Blo 167798 404041 := bstep (se 2 (by rfl) ⟨151515, by rfl⟩ : syracuseStep 404041 = 303031) B303031
theorem B1845949 : Blo 167798 1845949 := bstep (se 3 (by rfl) ⟨346115, by rfl⟩ : syracuseStep 1845949 = 692231) B692231
theorem B1846147 : Blo 167798 1846147 := bstep (se 1 (by rfl) ⟨1384610, by rfl⟩ : syracuseStep 1846147 = 2769221) B2769221
theorem B2632601 : Blo 167798 2632601 := bstep (se 2 (by rfl) ⟨987225, by rfl⟩ : syracuseStep 2632601 = 1974451) B1974451
theorem B568673 : Blo 167798 568673 := bstep (se 2 (by rfl) ⟨213252, by rfl⟩ : syracuseStep 568673 = 426505) B426505
theorem B864107 : Blo 167798 864107 := bstep (se 1 (by rfl) ⟨648080, by rfl⟩ : syracuseStep 864107 = 1296161) B1296161
theorem B26619799 : Blo 167798 26619799 := bstep (se 1 (by rfl) ⟨19964849, by rfl⟩ : syracuseStep 26619799 = 39929699) B39929699
theorem B7450555 : Blo 167798 7450555 := bstep (se 1 (by rfl) ⟨5587916, by rfl⟩ : syracuseStep 7450555 = 11175833) B11175833
theorem B438281 : Blo 167798 438281 := bstep (se 2 (by rfl) ⟨164355, by rfl⟩ : syracuseStep 438281 = 328711) B328711
theorem B274537 : Blo 167798 274537 := bstep (se 2 (by rfl) ⟨102951, by rfl⟩ : syracuseStep 274537 = 205903) B205903
theorem B406079 : Blo 167798 406079 := bstep (se 1 (by rfl) ⟨304559, by rfl⟩ : syracuseStep 406079 = 609119) B609119
theorem B308047 : Blo 167798 308047 := bstep (se 1 (by rfl) ⟨231035, by rfl⟩ : syracuseStep 308047 = 462071) B462071
theorem B340967 : Blo 167798 340967 := bstep (se 1 (by rfl) ⟨255725, by rfl⟩ : syracuseStep 340967 = 511451) B511451
theorem B2307217 : Blo 167798 2307217 := bstep (se 2 (by rfl) ⟨865206, by rfl⟩ : syracuseStep 2307217 = 1730413) B1730413
theorem B570617 : Blo 167798 570617 := bstep (se 2 (by rfl) ⟨213981, by rfl⟩ : syracuseStep 570617 = 427963) B427963
theorem B570887 : Blo 167798 570887 := bstep (se 1 (by rfl) ⟨428165, by rfl⟩ : syracuseStep 570887 = 856331) B856331
theorem B571859 : Blo 167798 571859 := bstep (se 1 (by rfl) ⟨428894, by rfl⟩ : syracuseStep 571859 = 857789) B857789
theorem B571967 : Blo 167798 571967 := bstep (se 1 (by rfl) ⟨428975, by rfl⟩ : syracuseStep 571967 = 857951) B857951
theorem B408491 : Blo 167798 408491 := bstep (se 1 (by rfl) ⟨306368, by rfl⟩ : syracuseStep 408491 = 612737) B612737
theorem B408539 : Blo 167798 408539 := bstep (se 1 (by rfl) ⟨306404, by rfl⟩ : syracuseStep 408539 = 612809) B612809
theorem B408673 : Blo 167798 408673 := bstep (se 2 (by rfl) ⟨153252, by rfl⟩ : syracuseStep 408673 = 306505) B306505
theorem B1752293 : Blo 167798 1752293 := bstep (se 4 (by rfl) ⟨164277, by rfl⟩ : syracuseStep 1752293 = 328555) B328555
theorem B638239 : Blo 167798 638239 := bstep (se 1 (by rfl) ⟨478679, by rfl⟩ : syracuseStep 638239 = 957359) B957359
theorem B867833 : Blo 167798 867833 := bstep (se 2 (by rfl) ⟨325437, by rfl⟩ : syracuseStep 867833 = 650875) B650875
theorem B310879 : Blo 167798 310879 := bstep (se 1 (by rfl) ⟨233159, by rfl⟩ : syracuseStep 310879 = 466319) B466319
theorem B868157 : Blo 167798 868157 := bstep (se 3 (by rfl) ⟨162779, by rfl⟩ : syracuseStep 868157 = 325559) B325559
theorem B573803 : Blo 167798 573803 := bstep (se 1 (by rfl) ⟨430352, by rfl⟩ : syracuseStep 573803 = 860705) B860705
theorem B574073 : Blo 167798 574073 := bstep (se 2 (by rfl) ⟨215277, by rfl⟩ : syracuseStep 574073 = 430555) B430555
theorem B441762497 : Blo 167798 441762497 := bstep (se 2 (by rfl) ⟨165660936, by rfl⟩ : syracuseStep 441762497 = 331321873) B331321873
theorem B377567 : Blo 167798 377567 := bstep (se 1 (by rfl) ⟨283175, by rfl⟩ : syracuseStep 377567 = 566351) B566351
theorem B3293945 : Blo 167798 3293945 := bstep (se 2 (by rfl) ⟨1235229, by rfl⟩ : syracuseStep 3293945 = 2470459) B2470459
theorem B377819 : Blo 167798 377819 := bstep (se 1 (by rfl) ⟨283364, by rfl⟩ : syracuseStep 377819 = 566729) B566729
theorem B9684035 : Blo 167798 9684035 := bstep (se 1 (by rfl) ⟨7263026, by rfl⟩ : syracuseStep 9684035 = 14526053) B14526053
theorem B377999 : Blo 167798 377999 := bstep (se 1 (by rfl) ⟨283499, by rfl⟩ : syracuseStep 377999 = 566999) B566999
theorem B1623233 : Blo 167798 1623233 := bstep (se 2 (by rfl) ⟨608712, by rfl⟩ : syracuseStep 1623233 = 1217425) B1217425
theorem B378089 : Blo 167798 378089 := bstep (se 2 (by rfl) ⟨141783, by rfl⟩ : syracuseStep 378089 = 283567) B283567
theorem B1557737 : Blo 167798 1557737 := bstep (se 2 (by rfl) ⟨584151, by rfl⟩ : syracuseStep 1557737 = 1168303) B1168303
theorem B378143 : Blo 167798 378143 := bstep (se 1 (by rfl) ⟨283607, by rfl⟩ : syracuseStep 378143 = 567215) B567215
theorem B640669 : Blo 167798 640669 := bstep (se 3 (by rfl) ⟨120125, by rfl⟩ : syracuseStep 640669 = 240251) B240251
theorem B214751 : Blo 167798 214751 := bstep (se 1 (by rfl) ⟨161063, by rfl⟩ : syracuseStep 214751 = 322127) B322127
theorem B378665 : Blo 167798 378665 := bstep (se 2 (by rfl) ⟨141999, by rfl⟩ : syracuseStep 378665 = 283999) B283999
theorem B575855 : Blo 167798 575855 := bstep (se 1 (by rfl) ⟨431891, by rfl⟩ : syracuseStep 575855 = 863783) B863783
theorem B510391 : Blo 167798 510391 := bstep (se 1 (by rfl) ⟨382793, by rfl⟩ : syracuseStep 510391 = 765587) B765587
theorem B346619 : Blo 167798 346619 := bstep (se 1 (by rfl) ⟨259964, by rfl⟩ : syracuseStep 346619 = 519929) B519929
theorem B1166113 : Blo 167798 1166113 := bstep (se 2 (by rfl) ⟨437292, by rfl⟩ : syracuseStep 1166113 = 874585) B874585
theorem B379727 : Blo 167798 379727 := bstep (se 1 (by rfl) ⟨284795, by rfl⟩ : syracuseStep 379727 = 569591) B569591
theorem B379943 : Blo 167798 379943 := bstep (se 1 (by rfl) ⟨284957, by rfl⟩ : syracuseStep 379943 = 569915) B569915
theorem B609319 : Blo 167798 609319 := bstep (se 1 (by rfl) ⟨456989, by rfl⟩ : syracuseStep 609319 = 913979) B913979
theorem B380123 : Blo 167798 380123 := bstep (se 1 (by rfl) ⟨285092, by rfl⟩ : syracuseStep 380123 = 570185) B570185
theorem B642401 : Blo 167798 642401 := bstep (se 2 (by rfl) ⟨240900, by rfl⟩ : syracuseStep 642401 = 481801) B481801
theorem B380321 : Blo 167798 380321 := bstep (se 2 (by rfl) ⟨142620, by rfl⟩ : syracuseStep 380321 = 285241) B285241
theorem B216751 : Blo 167798 216751 := bstep (se 1 (by rfl) ⟨162563, by rfl⟩ : syracuseStep 216751 = 325127) B325127
theorem B577259 : Blo 167798 577259 := bstep (se 1 (by rfl) ⟨432944, by rfl⟩ : syracuseStep 577259 = 865889) B865889
theorem B544553 : Blo 167798 544553 := bstep (se 2 (by rfl) ⟨204207, by rfl⟩ : syracuseStep 544553 = 408415) B408415
theorem B380879 : Blo 167798 380879 := bstep (se 1 (by rfl) ⟨285659, by rfl⟩ : syracuseStep 380879 = 571319) B571319
theorem B381257 : Blo 167798 381257 := bstep (se 2 (by rfl) ⟨142971, by rfl⟩ : syracuseStep 381257 = 285943) B285943
theorem B381275 : Blo 167798 381275 := bstep (se 1 (by rfl) ⟨285956, by rfl⟩ : syracuseStep 381275 = 571913) B571913
theorem B643585 : Blo 167798 643585 := bstep (se 2 (by rfl) ⟨241344, by rfl⟩ : syracuseStep 643585 = 482689) B482689
theorem B283243 : Blo 167798 283243 := bstep (se 1 (by rfl) ⟨212432, by rfl⟩ : syracuseStep 283243 = 424865) B424865
theorem B873107 : Blo 167798 873107 := bstep (se 1 (by rfl) ⟨654830, by rfl⟩ : syracuseStep 873107 = 1309661) B1309661
theorem B578231 : Blo 167798 578231 := bstep (se 1 (by rfl) ⟨433673, by rfl⟩ : syracuseStep 578231 = 867347) B867347
theorem B283547 : Blo 167798 283547 := bstep (se 1 (by rfl) ⟨212660, by rfl⟩ : syracuseStep 283547 = 425321) B425321
theorem B381851 : Blo 167798 381851 := bstep (se 1 (by rfl) ⟨286388, by rfl⟩ : syracuseStep 381851 = 572777) B572777
theorem B644071 : Blo 167798 644071 := bstep (se 1 (by rfl) ⟨483053, by rfl⟩ : syracuseStep 644071 = 966107) B966107
theorem B382049 : Blo 167798 382049 := bstep (se 2 (by rfl) ⟨143268, by rfl⟩ : syracuseStep 382049 = 286537) B286537
theorem B644345 : Blo 167798 644345 := bstep (se 2 (by rfl) ⟨241629, by rfl⟩ : syracuseStep 644345 = 483259) B483259
theorem B415007 : Blo 167798 415007 := bstep (se 1 (by rfl) ⟨311255, by rfl⟩ : syracuseStep 415007 = 622511) B622511
theorem B382247 : Blo 167798 382247 := bstep (se 1 (by rfl) ⟨286685, by rfl⟩ : syracuseStep 382247 = 573371) B573371
theorem B1955177 : Blo 167798 1955177 := bstep (se 2 (by rfl) ⟨733191, by rfl⟩ : syracuseStep 1955177 = 1466383) B1466383
theorem B1234379 : Blo 167798 1234379 := bstep (se 1 (by rfl) ⟨925784, by rfl⟩ : syracuseStep 1234379 = 1851569) B1851569
theorem B382625 : Blo 167798 382625 := bstep (se 2 (by rfl) ⟨143484, by rfl⟩ : syracuseStep 382625 = 286969) B286969
theorem B1463993 : Blo 167798 1463993 := bstep (se 2 (by rfl) ⟨548997, by rfl⟩ : syracuseStep 1463993 = 1097995) B1097995
theorem B251855 : Blo 167798 251855 := bstep (se 1 (by rfl) ⟨188891, by rfl⟩ : syracuseStep 251855 = 377783) B377783
theorem B481231 : Blo 167798 481231 := bstep (se 1 (by rfl) ⟨360923, by rfl⟩ : syracuseStep 481231 = 721847) B721847
theorem B382985 : Blo 167798 382985 := bstep (se 2 (by rfl) ⟨143619, by rfl⟩ : syracuseStep 382985 = 287239) B287239
theorem B1923101 : Blo 167798 1923101 := bstep (se 3 (by rfl) ⟨360581, by rfl⟩ : syracuseStep 1923101 = 721163) B721163
theorem B973079 : Blo 167798 973079 := bstep (se 1 (by rfl) ⟨729809, by rfl⟩ : syracuseStep 973079 = 1459619) B1459619
theorem B252251 : Blo 167798 252251 := bstep (se 1 (by rfl) ⟨189188, by rfl⟩ : syracuseStep 252251 = 378377) B378377
theorem B383399 : Blo 167798 383399 := bstep (se 1 (by rfl) ⟨287549, by rfl⟩ : syracuseStep 383399 = 575099) B575099
theorem B383507 : Blo 167798 383507 := bstep (se 1 (by rfl) ⟨287630, by rfl⟩ : syracuseStep 383507 = 575261) B575261
theorem B252479 : Blo 167798 252479 := bstep (se 1 (by rfl) ⟨189359, by rfl⟩ : syracuseStep 252479 = 378719) B378719
theorem B383561 : Blo 167798 383561 := bstep (se 2 (by rfl) ⟨143835, by rfl⟩ : syracuseStep 383561 = 287671) B287671
theorem B252599 : Blo 167798 252599 := bstep (se 1 (by rfl) ⟨189449, by rfl⟩ : syracuseStep 252599 = 378899) B378899
theorem B252827 : Blo 167798 252827 := bstep (se 1 (by rfl) ⟨189620, by rfl⟩ : syracuseStep 252827 = 379241) B379241
theorem B383975 : Blo 167798 383975 := bstep (se 1 (by rfl) ⟨287981, by rfl⟩ : syracuseStep 383975 = 575963) B575963
theorem B1629233 : Blo 167798 1629233 := bstep (se 2 (by rfl) ⟨610962, by rfl⟩ : syracuseStep 1629233 = 1221925) B1221925
theorem B613499 : Blo 167798 613499 := bstep (se 1 (by rfl) ⟨460124, by rfl⟩ : syracuseStep 613499 = 920249) B920249
theorem B1105085 : Blo 167798 1105085 := bstep (se 3 (by rfl) ⟨207203, by rfl⟩ : syracuseStep 1105085 = 414407) B414407
theorem B253223 : Blo 167798 253223 := bstep (se 1 (by rfl) ⟨189917, by rfl⟩ : syracuseStep 253223 = 379835) B379835
theorem B384353 : Blo 167798 384353 := bstep (se 2 (by rfl) ⟨144132, by rfl⟩ : syracuseStep 384353 = 288265) B288265
theorem B253307 : Blo 167798 253307 := bstep (se 1 (by rfl) ⟨189980, by rfl⟩ : syracuseStep 253307 = 379961) B379961
theorem B384443 : Blo 167798 384443 := bstep (se 1 (by rfl) ⟨288332, by rfl⟩ : syracuseStep 384443 = 576665) B576665
theorem B253433 : Blo 167798 253433 := bstep (se 2 (by rfl) ⟨95037, by rfl⟩ : syracuseStep 253433 = 190075) B190075
theorem B548345 : Blo 167798 548345 := bstep (se 2 (by rfl) ⟨205629, by rfl⟩ : syracuseStep 548345 = 411259) B411259
theorem B384569 : Blo 167798 384569 := bstep (se 2 (by rfl) ⟨144213, by rfl⟩ : syracuseStep 384569 = 288427) B288427
theorem B253535 : Blo 167798 253535 := bstep (se 1 (by rfl) ⟨190151, by rfl⟩ : syracuseStep 253535 = 380303) B380303
theorem B319211 : Blo 167798 319211 := bstep (se 1 (by rfl) ⟨239408, by rfl⟩ : syracuseStep 319211 = 478817) B478817
theorem B1171207 : Blo 167798 1171207 := bstep (se 1 (by rfl) ⟨878405, by rfl⟩ : syracuseStep 1171207 = 1756811) B1756811
theorem B253751 : Blo 167798 253751 := bstep (se 1 (by rfl) ⟨190313, by rfl⟩ : syracuseStep 253751 = 380627) B380627
theorem B548669 : Blo 167798 548669 := bstep (se 3 (by rfl) ⟨102875, by rfl⟩ : syracuseStep 548669 = 205751) B205751
theorem B646973 : Blo 167798 646973 := bstep (se 3 (by rfl) ⟨121307, by rfl⟩ : syracuseStep 646973 = 242615) B242615
theorem B876395 : Blo 167798 876395 := bstep (se 1 (by rfl) ⟨657296, by rfl⟩ : syracuseStep 876395 = 1314593) B1314593
theorem B319439 : Blo 167798 319439 := bstep (se 1 (by rfl) ⟨239579, by rfl⟩ : syracuseStep 319439 = 479159) B479159
theorem B254057 : Blo 167798 254057 := bstep (se 2 (by rfl) ⟨95271, by rfl⟩ : syracuseStep 254057 = 190543) B190543
theorem B385235 : Blo 167798 385235 := bstep (se 1 (by rfl) ⟨288926, by rfl⟩ : syracuseStep 385235 = 577853) B577853
theorem B385289 : Blo 167798 385289 := bstep (se 2 (by rfl) ⟨144483, by rfl⟩ : syracuseStep 385289 = 288967) B288967
theorem B4645181 : Blo 167798 4645181 := bstep (se 3 (by rfl) ⟨870971, by rfl⟩ : syracuseStep 4645181 = 1741943) B1741943
theorem B254375 : Blo 167798 254375 := bstep (se 1 (by rfl) ⟨190781, by rfl⟩ : syracuseStep 254375 = 381563) B381563
theorem B385505 : Blo 167798 385505 := bstep (se 2 (by rfl) ⟨144564, by rfl⟩ : syracuseStep 385505 = 289129) B289129
theorem B188923 : Blo 167798 188923 := bstep (se 1 (by rfl) ⟨141692, by rfl⟩ : syracuseStep 188923 = 283385) B283385
theorem B254459 : Blo 167798 254459 := bstep (se 1 (by rfl) ⟨190844, by rfl⟩ : syracuseStep 254459 = 381689) B381689
theorem B2777611 : Blo 167798 2777611 := bstep (se 1 (by rfl) ⟨2083208, by rfl⟩ : syracuseStep 2777611 = 4166417) B4166417
theorem B320107 : Blo 167798 320107 := bstep (se 1 (by rfl) ⟨240080, by rfl⟩ : syracuseStep 320107 = 480161) B480161
theorem B254585 : Blo 167798 254585 := bstep (se 2 (by rfl) ⟨95469, by rfl⟩ : syracuseStep 254585 = 190939) B190939
theorem B189103 : Blo 167798 189103 := bstep (se 1 (by rfl) ⟨141827, by rfl⟩ : syracuseStep 189103 = 283655) B283655
theorem B254639 : Blo 167798 254639 := bstep (se 1 (by rfl) ⟨190979, by rfl⟩ : syracuseStep 254639 = 381959) B381959
theorem B320183 : Blo 167798 320183 := bstep (se 1 (by rfl) ⟨240137, by rfl⟩ : syracuseStep 320183 = 480275) B480275
theorem B975563 : Blo 167798 975563 := bstep (se 1 (by rfl) ⟨731672, by rfl⟩ : syracuseStep 975563 = 1463345) B1463345
theorem B254687 : Blo 167798 254687 := bstep (se 1 (by rfl) ⟨191015, by rfl⟩ : syracuseStep 254687 = 382031) B382031
theorem B287455 : Blo 167798 287455 := bstep (se 1 (by rfl) ⟨215591, by rfl⟩ : syracuseStep 287455 = 431183) B431183
theorem B385811 : Blo 167798 385811 := bstep (se 1 (by rfl) ⟨289358, by rfl⟩ : syracuseStep 385811 = 578717) B578717
theorem B320411 : Blo 167798 320411 := bstep (se 1 (by rfl) ⟨240308, by rfl⟩ : syracuseStep 320411 = 480617) B480617
theorem B189391 : Blo 167798 189391 := bstep (se 1 (by rfl) ⟨142043, by rfl⟩ : syracuseStep 189391 = 284087) B284087
theorem B254951 : Blo 167798 254951 := bstep (se 1 (by rfl) ⟨191213, by rfl⟩ : syracuseStep 254951 = 382427) B382427
theorem B549985 : Blo 167798 549985 := bstep (se 2 (by rfl) ⟨206244, by rfl⟩ : syracuseStep 549985 = 412489) B412489
theorem B386171 : Blo 167798 386171 := bstep (se 1 (by rfl) ⟨289628, by rfl⟩ : syracuseStep 386171 = 579257) B579257
theorem B287887 : Blo 167798 287887 := bstep (se 1 (by rfl) ⟨215915, by rfl⟩ : syracuseStep 287887 = 431831) B431831
theorem B255209 : Blo 167798 255209 := bstep (se 2 (by rfl) ⟨95703, by rfl⟩ : syracuseStep 255209 = 191407) B191407
theorem B386297 : Blo 167798 386297 := bstep (se 2 (by rfl) ⟨144861, by rfl⟩ : syracuseStep 386297 = 289723) B289723
theorem B255263 : Blo 167798 255263 := bstep (se 1 (by rfl) ⟨191447, by rfl⟩ : syracuseStep 255263 = 382895) B382895
theorem B189787 : Blo 167798 189787 := bstep (se 1 (by rfl) ⟨142340, by rfl⟩ : syracuseStep 189787 = 284681) B284681
theorem B288137 : Blo 167798 288137 := bstep (se 2 (by rfl) ⟨108051, by rfl⟩ : syracuseStep 288137 = 216103) B216103
theorem B386441 : Blo 167798 386441 := bstep (se 2 (by rfl) ⟨144915, by rfl⟩ : syracuseStep 386441 = 289831) B289831
theorem B189895 : Blo 167798 189895 := bstep (se 1 (by rfl) ⟨142421, by rfl⟩ : syracuseStep 189895 = 284843) B284843
theorem B255431 : Blo 167798 255431 := bstep (se 1 (by rfl) ⟨191573, by rfl⟩ : syracuseStep 255431 = 383147) B383147
theorem B321185 : Blo 167798 321185 := bstep (se 2 (by rfl) ⟨120444, by rfl⟩ : syracuseStep 321185 = 240889) B240889
theorem B255785 : Blo 167798 255785 := bstep (se 2 (by rfl) ⟨95919, by rfl⟩ : syracuseStep 255785 = 191839) B191839
theorem B190255 : Blo 167798 190255 := bstep (se 1 (by rfl) ⟨142691, by rfl⟩ : syracuseStep 190255 = 285383) B285383
theorem B255791 : Blo 167798 255791 := bstep (se 1 (by rfl) ⟨191843, by rfl⟩ : syracuseStep 255791 = 383687) B383687
theorem B321337 : Blo 167798 321337 := bstep (se 2 (by rfl) ⟨120501, by rfl⟩ : syracuseStep 321337 = 241003) B241003
theorem B288569 : Blo 167798 288569 := bstep (se 2 (by rfl) ⟨108213, by rfl⟩ : syracuseStep 288569 = 216427) B216427
theorem B190363 : Blo 167798 190363 := bstep (se 1 (by rfl) ⟨142772, by rfl⟩ : syracuseStep 190363 = 285545) B285545
theorem B321641 : Blo 167798 321641 := bstep (se 2 (by rfl) ⟨120615, by rfl⟩ : syracuseStep 321641 = 241231) B241231
theorem B11954309 : Blo 167798 11954309 := bstep (se 4 (by rfl) ⟨1120716, by rfl⟩ : syracuseStep 11954309 = 2241433) B2241433
theorem B387337 : Blo 167798 387337 := bstep (se 2 (by rfl) ⟨145251, by rfl⟩ : syracuseStep 387337 = 290503) B290503
theorem B256265 : Blo 167798 256265 := bstep (se 2 (by rfl) ⟨96099, by rfl⟩ : syracuseStep 256265 = 192199) B192199
theorem B616729 : Blo 167798 616729 := bstep (se 2 (by rfl) ⟨231273, by rfl⟩ : syracuseStep 616729 = 462547) B462547
theorem B190759 : Blo 167798 190759 := bstep (se 1 (by rfl) ⟨143069, by rfl⟩ : syracuseStep 190759 = 286139) B286139
theorem B190831 : Blo 167798 190831 := bstep (se 1 (by rfl) ⟨143123, by rfl⟩ : syracuseStep 190831 = 286247) B286247
theorem B256367 : Blo 167798 256367 := bstep (se 1 (by rfl) ⟨192275, by rfl⟩ : syracuseStep 256367 = 384551) B384551
theorem B191047 : Blo 167798 191047 := bstep (se 1 (by rfl) ⟨143285, by rfl⟩ : syracuseStep 191047 = 286571) B286571
theorem B911945 : Blo 167798 911945 := bstep (se 2 (by rfl) ⟨341979, by rfl⟩ : syracuseStep 911945 = 683959) B683959
theorem B256583 : Blo 167798 256583 := bstep (se 1 (by rfl) ⟨192437, by rfl⟩ : syracuseStep 256583 = 384875) B384875
theorem B256619 : Blo 167798 256619 := bstep (se 1 (by rfl) ⟨192464, by rfl⟩ : syracuseStep 256619 = 384929) B384929
theorem B649903 : Blo 167798 649903 := bstep (se 1 (by rfl) ⟨487427, by rfl⟩ : syracuseStep 649903 = 974855) B974855
theorem B11168441 : Blo 167798 11168441 := bstep (se 2 (by rfl) ⟨4188165, by rfl⟩ : syracuseStep 11168441 = 8376331) B8376331
theorem B1108669 : Blo 167798 1108669 := bstep (se 3 (by rfl) ⟨207875, by rfl⟩ : syracuseStep 1108669 = 415751) B415751
theorem B256847 : Blo 167798 256847 := bstep (se 1 (by rfl) ⟨192635, by rfl⟩ : syracuseStep 256847 = 385271) B385271
theorem B289615 : Blo 167798 289615 := bstep (se 1 (by rfl) ⟨217211, by rfl⟩ : syracuseStep 289615 = 434423) B434423
theorem B781427 : Blo 167798 781427 := bstep (se 1 (by rfl) ⟨586070, by rfl⟩ : syracuseStep 781427 = 1172141) B1172141
theorem B257243 : Blo 167798 257243 := bstep (se 1 (by rfl) ⟨192932, by rfl⟩ : syracuseStep 257243 = 385865) B385865
theorem B257417 : Blo 167798 257417 := bstep (se 2 (by rfl) ⟨96531, by rfl⟩ : syracuseStep 257417 = 193063) B193063
theorem B454027 : Blo 167798 454027 := bstep (se 1 (by rfl) ⟨340520, by rfl⟩ : syracuseStep 454027 = 681041) B681041
theorem B191911 : Blo 167798 191911 := bstep (se 1 (by rfl) ⟨143933, by rfl⟩ : syracuseStep 191911 = 287867) B287867
theorem B650767 : Blo 167798 650767 := bstep (se 1 (by rfl) ⟨488075, by rfl⟩ : syracuseStep 650767 = 976151) B976151
theorem B650861 : Blo 167798 650861 := bstep (se 3 (by rfl) ⟨122036, by rfl⟩ : syracuseStep 650861 = 244073) B244073
theorem B683635 : Blo 167798 683635 := bstep (se 1 (by rfl) ⟨512726, by rfl⟩ : syracuseStep 683635 = 1025453) B1025453
theorem B192487 : Blo 167798 192487 := bstep (se 1 (by rfl) ⟨144365, by rfl⟩ : syracuseStep 192487 = 288731) B288731
theorem B324091 : Blo 167798 324091 := bstep (se 1 (by rfl) ⟨243068, by rfl⟩ : syracuseStep 324091 = 486137) B486137
theorem B651847 : Blo 167798 651847 := bstep (se 1 (by rfl) ⟨488885, by rfl⟩ : syracuseStep 651847 = 977771) B977771
theorem B783323 : Blo 167798 783323 := bstep (se 1 (by rfl) ⟨587492, by rfl⟩ : syracuseStep 783323 = 1174985) B1174985
theorem B586727 : Blo 167798 586727 := bstep (se 1 (by rfl) ⟨440045, by rfl⟩ : syracuseStep 586727 = 880091) B880091
theorem B717815 : Blo 167798 717815 := bstep (se 1 (by rfl) ⟨538361, by rfl⟩ : syracuseStep 717815 = 1076723) B1076723
theorem B292295 : Blo 167798 292295 := bstep (se 1 (by rfl) ⟨219221, by rfl⟩ : syracuseStep 292295 = 438443) B438443
theorem B719113 : Blo 167798 719113 := bstep (se 2 (by rfl) ⟨269667, by rfl⟩ : syracuseStep 719113 = 539335) B539335
theorem B325999 : Blo 167798 325999 := bstep (se 1 (by rfl) ⟨244499, by rfl⟩ : syracuseStep 325999 = 488999) B488999
theorem B358823 : Blo 167798 358823 := bstep (se 1 (by rfl) ⟨269117, by rfl⟩ : syracuseStep 358823 = 538235) B538235
theorem B326099 : Blo 167798 326099 := bstep (se 1 (by rfl) ⟨244574, by rfl⟩ : syracuseStep 326099 = 489149) B489149
theorem B293371 : Blo 167798 293371 := bstep (se 1 (by rfl) ⟨220028, by rfl⟩ : syracuseStep 293371 = 440057) B440057
theorem B1931849 : Blo 167798 1931849 := bstep (se 2 (by rfl) ⟨724443, by rfl⟩ : syracuseStep 1931849 = 1448887) B1448887
theorem B818075 : Blo 167798 818075 := bstep (se 1 (by rfl) ⟨613556, by rfl⟩ : syracuseStep 818075 = 1227113) B1227113
theorem B555947 : Blo 167798 555947 := bstep (se 1 (by rfl) ⟨416960, by rfl⟩ : syracuseStep 555947 = 833921) B833921
theorem B425159 : Blo 167798 425159 := bstep (se 1 (by rfl) ⟨318869, by rfl⟩ : syracuseStep 425159 = 637739) B637739
theorem B425209 : Blo 167798 425209 := bstep (se 2 (by rfl) ⟨159453, by rfl⟩ : syracuseStep 425209 = 318907) B318907
theorem B359711 : Blo 167798 359711 := bstep (se 1 (by rfl) ⟨269783, by rfl⟩ : syracuseStep 359711 = 539567) B539567
theorem B720343 : Blo 167798 720343 := bstep (se 1 (by rfl) ⟨540257, by rfl⟩ : syracuseStep 720343 = 1080515) B1080515
theorem B851471 : Blo 167798 851471 := bstep (se 1 (by rfl) ⟨638603, by rfl⟩ : syracuseStep 851471 = 1277207) B1277207
theorem B425857 : Blo 167798 425857 := bstep (se 2 (by rfl) ⟨159696, by rfl⟩ : syracuseStep 425857 = 319393) B319393
theorem B1638305 : Blo 167798 1638305 := bstep (se 2 (by rfl) ⟨614364, by rfl⟩ : syracuseStep 1638305 = 1228729) B1228729
theorem B2195963 : Blo 167798 2195963 := bstep (se 1 (by rfl) ⟨1646972, by rfl⟩ : syracuseStep 2195963 = 3293945) B3293945
theorem B3703481 : Blo 167798 3703481 := bstep (se 2 (by rfl) ⟨1388805, by rfl⟩ : syracuseStep 3703481 = 2777611) B2777611
theorem B6456023 : Blo 167798 6456023 := bstep (se 1 (by rfl) ⟨4842017, by rfl⟩ : syracuseStep 6456023 = 9684035) B9684035
theorem B1082155 : Blo 167798 1082155 := bstep (se 1 (by rfl) ⟨811616, by rfl⟩ : syracuseStep 1082155 = 1623233) B1623233
theorem B426809 : Blo 167798 426809 := bstep (se 2 (by rfl) ⟨160053, by rfl⟩ : syracuseStep 426809 = 320107) B320107
theorem B3670879 : Blo 167798 3670879 := bstep (se 1 (by rfl) ⟨2753159, by rfl⟩ : syracuseStep 3670879 = 5506319) B5506319
theorem B721831 : Blo 167798 721831 := bstep (se 1 (by rfl) ⟨541373, by rfl⟩ : syracuseStep 721831 = 1082747) B1082747
theorem B1049951 : Blo 167798 1049951 := bstep (se 1 (by rfl) ⟨787463, by rfl⟩ : syracuseStep 1049951 = 1574927) B1574927
theorem B329131 : Blo 167798 329131 := bstep (se 1 (by rfl) ⟨246848, by rfl⟩ : syracuseStep 329131 = 493697) B493697
theorem B722429 : Blo 167798 722429 := bstep (se 3 (by rfl) ⟨135455, by rfl⟩ : syracuseStep 722429 = 270911) B270911
theorem B460991 : Blo 167798 460991 := bstep (se 1 (by rfl) ⟨345743, by rfl⟩ : syracuseStep 460991 = 691487) B691487
theorem B854225 : Blo 167798 854225 := bstep (se 2 (by rfl) ⟨320334, by rfl⟩ : syracuseStep 854225 = 640669) B640669
theorem B428267 : Blo 167798 428267 := bstep (se 1 (by rfl) ⟨321200, by rfl⟩ : syracuseStep 428267 = 642401) B642401
theorem B2722085 : Blo 167798 2722085 := bstep (se 4 (by rfl) ⟨255195, by rfl⟩ : syracuseStep 2722085 = 510391) B510391
theorem B428449 : Blo 167798 428449 := bstep (se 2 (by rfl) ⟨160668, by rfl⟩ : syracuseStep 428449 = 321337) B321337
theorem B363035 : Blo 167798 363035 := bstep (se 1 (by rfl) ⟨272276, by rfl⟩ : syracuseStep 363035 = 544553) B544553
theorem B723487 : Blo 167798 723487 := bstep (se 1 (by rfl) ⟨542615, by rfl⟩ : syracuseStep 723487 = 1085231) B1085231
theorem B822305 : Blo 167798 822305 := bstep (se 2 (by rfl) ⟨308364, by rfl⟩ : syracuseStep 822305 = 616729) B616729
theorem B429563 : Blo 167798 429563 := bstep (se 1 (by rfl) ⟨322172, by rfl⟩ : syracuseStep 429563 = 644345) B644345
theorem B1478225 : Blo 167798 1478225 := bstep (se 2 (by rfl) ⟨554334, by rfl⟩ : syracuseStep 1478225 = 1108669) B1108669
theorem B2461265 : Blo 167798 2461265 := bstep (se 2 (by rfl) ⟨922974, by rfl⟩ : syracuseStep 2461265 = 1845949) B1845949
theorem B2461529 : Blo 167798 2461529 := bstep (se 2 (by rfl) ⟨923073, by rfl⟩ : syracuseStep 2461529 = 1846147) B1846147
theorem B167903 : Blo 167798 167903 := bstep (se 1 (by rfl) ⟨125927, by rfl⟩ : syracuseStep 167903 = 251855) B251855
theorem B1282067 : Blo 167798 1282067 := bstep (se 1 (by rfl) ⟨961550, by rfl⟩ : syracuseStep 1282067 = 1923101) B1923101
theorem B168167 : Blo 167798 168167 := bstep (se 1 (by rfl) ⟨126125, by rfl⟩ : syracuseStep 168167 = 252251) B252251
theorem B168319 : Blo 167798 168319 := bstep (se 1 (by rfl) ⟨126239, by rfl⟩ : syracuseStep 168319 = 252479) B252479
theorem B856493 : Blo 167798 856493 := bstep (se 3 (by rfl) ⟨160592, by rfl⟩ : syracuseStep 856493 = 321185) B321185
theorem B168399 : Blo 167798 168399 := bstep (se 1 (by rfl) ⟨126299, by rfl⟩ : syracuseStep 168399 = 252599) B252599
theorem B856655 : Blo 167798 856655 := bstep (se 1 (by rfl) ⟨642491, by rfl⟩ : syracuseStep 856655 = 1284983) B1284983
theorem B168551 : Blo 167798 168551 := bstep (se 1 (by rfl) ⟨126413, by rfl⟩ : syracuseStep 168551 = 252827) B252827
theorem B1086155 : Blo 167798 1086155 := bstep (se 1 (by rfl) ⟨814616, by rfl⟩ : syracuseStep 1086155 = 1629233) B1629233
theorem B4395869 : Blo 167798 4395869 := bstep (se 3 (by rfl) ⟨824225, by rfl⟩ : syracuseStep 4395869 = 1648451) B1648451
theorem B168815 : Blo 167798 168815 := bstep (se 1 (by rfl) ⟨126611, by rfl⟩ : syracuseStep 168815 = 253223) B253223
theorem B168871 : Blo 167798 168871 := bstep (se 1 (by rfl) ⟨126653, by rfl⟩ : syracuseStep 168871 = 253307) B253307
theorem B168955 : Blo 167798 168955 := bstep (se 1 (by rfl) ⟨126716, by rfl⟩ : syracuseStep 168955 = 253433) B253433
theorem B365563 : Blo 167798 365563 := bstep (se 1 (by rfl) ⟨274172, by rfl⟩ : syracuseStep 365563 = 548345) B548345
theorem B169023 : Blo 167798 169023 := bstep (se 1 (by rfl) ⟨126767, by rfl⟩ : syracuseStep 169023 = 253535) B253535
theorem B35493065 : Blo 167798 35493065 := bstep (se 2 (by rfl) ⟨13309899, by rfl⟩ : syracuseStep 35493065 = 26619799) B26619799
theorem B169167 : Blo 167798 169167 := bstep (se 1 (by rfl) ⟨126875, by rfl⟩ : syracuseStep 169167 = 253751) B253751
theorem B365779 : Blo 167798 365779 := bstep (se 1 (by rfl) ⟨274334, by rfl⟩ : syracuseStep 365779 = 548669) B548669
theorem B431315 : Blo 167798 431315 := bstep (se 1 (by rfl) ⟨323486, by rfl⟩ : syracuseStep 431315 = 646973) B646973
theorem B9934073 : Blo 167798 9934073 := bstep (se 2 (by rfl) ⟨3725277, by rfl⟩ : syracuseStep 9934073 = 7450555) B7450555
theorem B464147 : Blo 167798 464147 := bstep (se 1 (by rfl) ⟨348110, by rfl⟩ : syracuseStep 464147 = 696221) B696221
theorem B169371 : Blo 167798 169371 := bstep (se 1 (by rfl) ⟨127028, by rfl⟩ : syracuseStep 169371 = 254057) B254057
theorem B366049 : Blo 167798 366049 := bstep (se 2 (by rfl) ⟨137268, by rfl⟩ : syracuseStep 366049 = 274537) B274537
theorem B169583 : Blo 167798 169583 := bstep (se 1 (by rfl) ⟨127187, by rfl⟩ : syracuseStep 169583 = 254375) B254375
theorem B169639 : Blo 167798 169639 := bstep (se 1 (by rfl) ⟨127229, by rfl⟩ : syracuseStep 169639 = 254459) B254459
theorem B169723 : Blo 167798 169723 := bstep (se 1 (by rfl) ⟨127292, by rfl⟩ : syracuseStep 169723 = 254585) B254585
theorem B169759 : Blo 167798 169759 := bstep (se 1 (by rfl) ⟨127319, by rfl⟩ : syracuseStep 169759 = 254639) B254639
theorem B169791 : Blo 167798 169791 := bstep (se 1 (by rfl) ⟨127343, by rfl⟩ : syracuseStep 169791 = 254687) B254687
theorem B169967 : Blo 167798 169967 := bstep (se 1 (by rfl) ⟨127475, by rfl⟩ : syracuseStep 169967 = 254951) B254951
theorem B432121 : Blo 167798 432121 := bstep (se 2 (by rfl) ⟨162045, by rfl⟩ : syracuseStep 432121 = 324091) B324091
theorem B858113 : Blo 167798 858113 := bstep (se 2 (by rfl) ⟨321792, by rfl⟩ : syracuseStep 858113 = 643585) B643585
theorem B170139 : Blo 167798 170139 := bstep (se 1 (by rfl) ⟨127604, by rfl⟩ : syracuseStep 170139 = 255209) B255209
theorem B202943 : Blo 167798 202943 := bstep (se 1 (by rfl) ⟨152207, by rfl⟩ : syracuseStep 202943 = 304415) B304415
theorem B170175 : Blo 167798 170175 := bstep (se 1 (by rfl) ⟨127631, by rfl⟩ : syracuseStep 170175 = 255263) B255263
theorem B170287 : Blo 167798 170287 := bstep (se 1 (by rfl) ⟨127715, by rfl⟩ : syracuseStep 170287 = 255431) B255431
theorem B170523 : Blo 167798 170523 := bstep (se 1 (by rfl) ⟨127892, by rfl⟩ : syracuseStep 170523 = 255785) B255785
theorem B170527 : Blo 167798 170527 := bstep (se 1 (by rfl) ⟨127895, by rfl⟩ : syracuseStep 170527 = 255791) B255791
theorem B858761 : Blo 167798 858761 := bstep (se 2 (by rfl) ⟨322035, by rfl⟩ : syracuseStep 858761 = 644071) B644071
theorem B924317 : Blo 167798 924317 := bstep (se 3 (by rfl) ⟨173309, by rfl⟩ : syracuseStep 924317 = 346619) B346619
theorem B858923 : Blo 167798 858923 := bstep (se 1 (by rfl) ⟨644192, by rfl⟩ : syracuseStep 858923 = 1288385) B1288385
theorem B170843 : Blo 167798 170843 := bstep (se 1 (by rfl) ⟨128132, by rfl⟩ : syracuseStep 170843 = 256265) B256265
theorem B2431853 : Blo 167798 2431853 := bstep (se 3 (by rfl) ⟨455972, by rfl⟩ : syracuseStep 2431853 = 911945) B911945
theorem B170911 : Blo 167798 170911 := bstep (se 1 (by rfl) ⟨128183, by rfl⟩ : syracuseStep 170911 = 256367) B256367
theorem B924641 : Blo 167798 924641 := bstep (se 2 (by rfl) ⟨346740, by rfl⟩ : syracuseStep 924641 = 693481) B693481
theorem B171055 : Blo 167798 171055 := bstep (se 1 (by rfl) ⟨128291, by rfl⟩ : syracuseStep 171055 = 256583) B256583
theorem B171079 : Blo 167798 171079 := bstep (se 1 (by rfl) ⟨128309, by rfl⟩ : syracuseStep 171079 = 256619) B256619
theorem B7445627 : Blo 167798 7445627 := bstep (se 1 (by rfl) ⟨5584220, by rfl⟩ : syracuseStep 7445627 = 11168441) B11168441
theorem B171231 : Blo 167798 171231 := bstep (se 1 (by rfl) ⟨128423, by rfl⟩ : syracuseStep 171231 = 256847) B256847
theorem B171495 : Blo 167798 171495 := bstep (se 1 (by rfl) ⟨128621, by rfl⟩ : syracuseStep 171495 = 257243) B257243
theorem B171611 : Blo 167798 171611 := bstep (se 1 (by rfl) ⟨128708, by rfl⟩ : syracuseStep 171611 = 257417) B257417
theorem B7020269 : Blo 167798 7020269 := bstep (se 3 (by rfl) ⟨1316300, by rfl⟩ : syracuseStep 7020269 = 2632601) B2632601
theorem B433907 : Blo 167798 433907 := bstep (se 1 (by rfl) ⟨325430, by rfl⟩ : syracuseStep 433907 = 650861) B650861
theorem B958817 : Blo 167798 958817 := bstep (se 2 (by rfl) ⟨359556, by rfl⟩ : syracuseStep 958817 = 719113) B719113
theorem B270719 : Blo 167798 270719 := bstep (se 1 (by rfl) ⟨203039, by rfl⟩ : syracuseStep 270719 = 406079) B406079
theorem B434665 : Blo 167798 434665 := bstep (se 2 (by rfl) ⟨162999, by rfl⟩ : syracuseStep 434665 = 325999) B325999
theorem B239215 : Blo 167798 239215 := bstep (se 1 (by rfl) ⟨179411, by rfl⟩ : syracuseStep 239215 = 358823) B358823
theorem B566945 : Blo 167798 566945 := bstep (se 2 (by rfl) ⟨212604, by rfl⟩ : syracuseStep 566945 = 425209) B425209
theorem B1287899 : Blo 167798 1287899 := bstep (se 1 (by rfl) ⟨965924, by rfl⟩ : syracuseStep 1287899 = 1931849) B1931849
theorem B272327 : Blo 167798 272327 := bstep (se 1 (by rfl) ⟨204245, by rfl⟩ : syracuseStep 272327 = 408491) B408491
theorem B370631 : Blo 167798 370631 := bstep (se 1 (by rfl) ⟨277973, by rfl⟩ : syracuseStep 370631 = 555947) B555947
theorem B960457 : Blo 167798 960457 := bstep (se 2 (by rfl) ⟨360171, by rfl⟩ : syracuseStep 960457 = 720343) B720343
theorem B272359 : Blo 167798 272359 := bstep (se 1 (by rfl) ⟨204269, by rfl⟩ : syracuseStep 272359 = 408539) B408539
theorem B239807 : Blo 167798 239807 := bstep (se 1 (by rfl) ⟨179855, by rfl⟩ : syracuseStep 239807 = 359711) B359711
theorem B567647 : Blo 167798 567647 := bstep (se 1 (by rfl) ⟨425735, by rfl⟩ : syracuseStep 567647 = 851471) B851471
theorem B567809 : Blo 167798 567809 := bstep (se 2 (by rfl) ⟨212928, by rfl⟩ : syracuseStep 567809 = 425857) B425857
theorem B1092203 : Blo 167798 1092203 := bstep (se 1 (by rfl) ⟨819152, by rfl⟩ : syracuseStep 1092203 = 1638305) B1638305
theorem B895799 : Blo 167798 895799 := bstep (se 1 (by rfl) ⟨671849, by rfl⟩ : syracuseStep 895799 = 1343699) B1343699
theorem B568295 : Blo 167798 568295 := bstep (se 1 (by rfl) ⟨426221, by rfl⟩ : syracuseStep 568295 = 852443) B852443
theorem B4369625 : Blo 167798 4369625 := bstep (se 2 (by rfl) ⟨1638609, by rfl⟩ : syracuseStep 4369625 = 3277219) B3277219
theorem B568619 : Blo 167798 568619 := bstep (se 1 (by rfl) ⟨426464, by rfl⟩ : syracuseStep 568619 = 852929) B852929
theorem B568889 : Blo 167798 568889 := bstep (se 2 (by rfl) ⟨213333, by rfl⟩ : syracuseStep 568889 = 426667) B426667
theorem B1289843 : Blo 167798 1289843 := bstep (se 1 (by rfl) ⟨967382, by rfl⟩ : syracuseStep 1289843 = 1934765) B1934765
theorem B733313 : Blo 167798 733313 := bstep (se 2 (by rfl) ⟨274992, by rfl⟩ : syracuseStep 733313 = 549985) B549985
theorem B242119 : Blo 167798 242119 := bstep (se 1 (by rfl) ⟨181589, by rfl⟩ : syracuseStep 242119 = 363179) B363179
theorem B308279 : Blo 167798 308279 := bstep (se 1 (by rfl) ⟨231209, by rfl⟩ : syracuseStep 308279 = 462419) B462419
theorem B1553651 : Blo 167798 1553651 := bstep (se 1 (by rfl) ⟨1165238, by rfl⟩ : syracuseStep 1553651 = 2330477) B2330477
theorem B570779 : Blo 167798 570779 := bstep (se 1 (by rfl) ⟨428084, by rfl⟩ : syracuseStep 570779 = 856169) B856169
theorem B6534755 : Blo 167798 6534755 := bstep (se 1 (by rfl) ⟨4901066, by rfl⟩ : syracuseStep 6534755 = 9802133) B9802133
theorem B964331 : Blo 167798 964331 := bstep (se 1 (by rfl) ⟨723248, by rfl⟩ : syracuseStep 964331 = 1446497) B1446497
theorem B538721 : Blo 167798 538721 := bstep (se 2 (by rfl) ⟨202020, by rfl⟩ : syracuseStep 538721 = 404041) B404041
theorem B571535 : Blo 167798 571535 := bstep (se 1 (by rfl) ⟨428651, by rfl⟩ : syracuseStep 571535 = 857303) B857303
theorem B276671 : Blo 167798 276671 := bstep (se 1 (by rfl) ⟨207503, by rfl⟩ : syracuseStep 276671 = 415007) B415007
theorem B866537 : Blo 167798 866537 := bstep (se 2 (by rfl) ⟨324951, by rfl⟩ : syracuseStep 866537 = 649903) B649903
theorem B1554817 : Blo 167798 1554817 := bstep (se 2 (by rfl) ⟨583056, by rfl⟩ : syracuseStep 1554817 = 1166113) B1166113
theorem B3291677 : Blo 167798 3291677 := bstep (se 3 (by rfl) ⟨617189, by rfl⟩ : syracuseStep 3291677 = 1234379) B1234379
theorem B965789 : Blo 167798 965789 := bstep (se 3 (by rfl) ⟨181085, by rfl⟩ : syracuseStep 965789 = 362171) B362171
theorem B605369 : Blo 167798 605369 := bstep (se 2 (by rfl) ⟨227013, by rfl⟩ : syracuseStep 605369 = 454027) B454027
theorem B572669 : Blo 167798 572669 := bstep (se 3 (by rfl) ⟨107375, by rfl⟩ : syracuseStep 572669 = 214751) B214751
theorem B867689 : Blo 167798 867689 := bstep (se 2 (by rfl) ⟨325383, by rfl⟩ : syracuseStep 867689 = 650767) B650767
theorem B736723 : Blo 167798 736723 := bstep (se 1 (by rfl) ⟨552542, by rfl⟩ : syracuseStep 736723 = 1105085) B1105085
theorem B638711 : Blo 167798 638711 := bstep (se 1 (by rfl) ⟨479033, by rfl⟩ : syracuseStep 638711 = 958067) B958067
theorem B212807 : Blo 167798 212807 := bstep (se 1 (by rfl) ⟨159605, by rfl⟩ : syracuseStep 212807 = 319211) B319211
theorem B212959 : Blo 167798 212959 := bstep (se 1 (by rfl) ⟨159719, by rfl⟩ : syracuseStep 212959 = 319439) B319439
theorem B573479 : Blo 167798 573479 := bstep (se 1 (by rfl) ⟨430109, by rfl⟩ : syracuseStep 573479 = 860219) B860219
theorem B3096787 : Blo 167798 3096787 := bstep (se 1 (by rfl) ⟨2322590, by rfl⟩ : syracuseStep 3096787 = 4645181) B4645181
theorem B213455 : Blo 167798 213455 := bstep (se 1 (by rfl) ⟨160091, by rfl⟩ : syracuseStep 213455 = 320183) B320183
theorem B1229363 : Blo 167798 1229363 := bstep (se 1 (by rfl) ⟨922022, by rfl⟩ : syracuseStep 1229363 = 1844045) B1844045
theorem B213607 : Blo 167798 213607 := bstep (se 1 (by rfl) ⟨160205, by rfl⟩ : syracuseStep 213607 = 320411) B320411
theorem B574127 : Blo 167798 574127 := bstep (se 1 (by rfl) ⟨430595, by rfl⟩ : syracuseStep 574127 = 861191) B861191
theorem B639683 : Blo 167798 639683 := bstep (se 1 (by rfl) ⟨479762, by rfl⟩ : syracuseStep 639683 = 959525) B959525
theorem B869129 : Blo 167798 869129 := bstep (se 2 (by rfl) ⟨325923, by rfl⟩ : syracuseStep 869129 = 651847) B651847
theorem B377657 : Blo 167798 377657 := bstep (se 2 (by rfl) ⟨141621, by rfl⟩ : syracuseStep 377657 = 283243) B283243
theorem B377711 : Blo 167798 377711 := bstep (se 1 (by rfl) ⟨283283, by rfl⟩ : syracuseStep 377711 = 566567) B566567
theorem B574451 : Blo 167798 574451 := bstep (se 1 (by rfl) ⟨430838, by rfl⟩ : syracuseStep 574451 = 861677) B861677
theorem B410729 : Blo 167798 410729 := bstep (se 2 (by rfl) ⟨154023, by rfl⟩ : syracuseStep 410729 = 308047) B308047
theorem B214427 : Blo 167798 214427 := bstep (se 1 (by rfl) ⟨160820, by rfl⟩ : syracuseStep 214427 = 321641) B321641
theorem B378287 : Blo 167798 378287 := bstep (se 1 (by rfl) ⟨283715, by rfl⟩ : syracuseStep 378287 = 567431) B567431
theorem B574991 : Blo 167798 574991 := bstep (se 1 (by rfl) ⟨431243, by rfl⟩ : syracuseStep 574991 = 862487) B862487
theorem B3130919 : Blo 167798 3130919 := bstep (se 1 (by rfl) ⟨2348189, by rfl⟩ : syracuseStep 3130919 = 4696379) B4696379
theorem B379115 : Blo 167798 379115 := bstep (se 1 (by rfl) ⟨284336, by rfl⟩ : syracuseStep 379115 = 568673) B568673
theorem B575801 : Blo 167798 575801 := bstep (se 2 (by rfl) ⟨215925, by rfl⟩ : syracuseStep 575801 = 431851) B431851
theorem B576071 : Blo 167798 576071 := bstep (se 1 (by rfl) ⟨432053, by rfl⟩ : syracuseStep 576071 = 864107) B864107
theorem B641641 : Blo 167798 641641 := bstep (se 2 (by rfl) ⟨240615, by rfl⟩ : syracuseStep 641641 = 481231) B481231
theorem B478543 : Blo 167798 478543 := bstep (se 1 (by rfl) ⟨358907, by rfl⟩ : syracuseStep 478543 = 717815) B717815
theorem B380411 : Blo 167798 380411 := bstep (se 1 (by rfl) ⟨285308, by rfl⟩ : syracuseStep 380411 = 570617) B570617
theorem B577097 : Blo 167798 577097 := bstep (se 2 (by rfl) ⟨216411, by rfl⟩ : syracuseStep 577097 = 432823) B432823
theorem B380591 : Blo 167798 380591 := bstep (se 1 (by rfl) ⟨285443, by rfl⟩ : syracuseStep 380591 = 570887) B570887
theorem B544897 : Blo 167798 544897 := bstep (se 2 (by rfl) ⟨204336, by rfl⟩ : syracuseStep 544897 = 408673) B408673
theorem B970937 : Blo 167798 970937 := bstep (se 2 (by rfl) ⟨364101, by rfl⟩ : syracuseStep 970937 = 728203) B728203
theorem B381239 : Blo 167798 381239 := bstep (se 1 (by rfl) ⟨285929, by rfl⟩ : syracuseStep 381239 = 571859) B571859
theorem B217399 : Blo 167798 217399 := bstep (se 1 (by rfl) ⟨163049, by rfl⟩ : syracuseStep 217399 = 326099) B326099
theorem B381311 : Blo 167798 381311 := bstep (se 1 (by rfl) ⟨285983, by rfl⟩ : syracuseStep 381311 = 571967) B571967
theorem B545383 : Blo 167798 545383 := bstep (se 1 (by rfl) ⟨409037, by rfl⟩ : syracuseStep 545383 = 818075) B818075
theorem B414505 : Blo 167798 414505 := bstep (se 2 (by rfl) ⟨155439, by rfl⟩ : syracuseStep 414505 = 310879) B310879
theorem B283439 : Blo 167798 283439 := bstep (se 1 (by rfl) ⟨212579, by rfl⟩ : syracuseStep 283439 = 425159) B425159
theorem B1168195 : Blo 167798 1168195 := bstep (se 1 (by rfl) ⟨876146, by rfl⟩ : syracuseStep 1168195 = 1752293) B1752293
theorem B578555 : Blo 167798 578555 := bstep (se 1 (by rfl) ⟨433916, by rfl⟩ : syracuseStep 578555 = 867833) B867833
theorem B1561609 : Blo 167798 1561609 := bstep (se 2 (by rfl) ⟨585603, by rfl⟩ : syracuseStep 1561609 = 1171207) B1171207
theorem B578771 : Blo 167798 578771 := bstep (se 1 (by rfl) ⟨434078, by rfl⟩ : syracuseStep 578771 = 868157) B868157
theorem B579041 : Blo 167798 579041 := bstep (se 2 (by rfl) ⟨217140, by rfl⟩ : syracuseStep 579041 = 434281) B434281
theorem B382535 : Blo 167798 382535 := bstep (se 1 (by rfl) ⟨286901, by rfl⟩ : syracuseStep 382535 = 573803) B573803
theorem B284411 : Blo 167798 284411 := bstep (se 1 (by rfl) ⟨213308, by rfl⟩ : syracuseStep 284411 = 426617) B426617
theorem B382715 : Blo 167798 382715 := bstep (se 1 (by rfl) ⟨287036, by rfl⟩ : syracuseStep 382715 = 574073) B574073
theorem B294508331 : Blo 167798 294508331 := bstep (se 1 (by rfl) ⟨220881248, by rfl⟩ : syracuseStep 294508331 = 441762497) B441762497
theorem B251711 : Blo 167798 251711 := bstep (se 1 (by rfl) ⟨188783, by rfl⟩ : syracuseStep 251711 = 377567) B377567
theorem B251879 : Blo 167798 251879 := bstep (se 1 (by rfl) ⟨188909, by rfl⟩ : syracuseStep 251879 = 377819) B377819
theorem B284647 : Blo 167798 284647 := bstep (se 1 (by rfl) ⟨213485, by rfl⟩ : syracuseStep 284647 = 426971) B426971
theorem B251897 : Blo 167798 251897 := bstep (se 2 (by rfl) ⟨94461, by rfl⟩ : syracuseStep 251897 = 188923) B188923
theorem B251999 : Blo 167798 251999 := bstep (se 1 (by rfl) ⟨188999, by rfl⟩ : syracuseStep 251999 = 377999) B377999
theorem B579689 : Blo 167798 579689 := bstep (se 2 (by rfl) ⟨217383, by rfl⟩ : syracuseStep 579689 = 434767) B434767
theorem B252059 : Blo 167798 252059 := bstep (se 1 (by rfl) ⟨189044, by rfl⟩ : syracuseStep 252059 = 378089) B378089
theorem B1038491 : Blo 167798 1038491 := bstep (se 1 (by rfl) ⟨778868, by rfl⟩ : syracuseStep 1038491 = 1557737) B1557737
theorem B252095 : Blo 167798 252095 := bstep (se 1 (by rfl) ⟨189071, by rfl⟩ : syracuseStep 252095 = 378143) B378143
theorem B284863 : Blo 167798 284863 := bstep (se 1 (by rfl) ⟨213647, by rfl⟩ : syracuseStep 284863 = 427295) B427295
theorem B252137 : Blo 167798 252137 := bstep (se 2 (by rfl) ⟨94551, by rfl⟩ : syracuseStep 252137 = 189103) B189103
theorem B383273 : Blo 167798 383273 := bstep (se 2 (by rfl) ⟨143727, by rfl⟩ : syracuseStep 383273 = 287455) B287455
theorem B1464743 : Blo 167798 1464743 := bstep (se 1 (by rfl) ⟨1098557, by rfl⟩ : syracuseStep 1464743 = 2197115) B2197115
theorem B252443 : Blo 167798 252443 := bstep (se 1 (by rfl) ⟨189332, by rfl⟩ : syracuseStep 252443 = 378665) B378665
theorem B2415193 : Blo 167798 2415193 := bstep (se 2 (by rfl) ⟨905697, by rfl⟩ : syracuseStep 2415193 = 1811395) B1811395
theorem B252521 : Blo 167798 252521 := bstep (se 2 (by rfl) ⟨94695, by rfl⟩ : syracuseStep 252521 = 189391) B189391
theorem B383849 : Blo 167798 383849 := bstep (se 2 (by rfl) ⟨143943, by rfl⟩ : syracuseStep 383849 = 287887) B287887
theorem B285599 : Blo 167798 285599 := bstep (se 1 (by rfl) ⟨214199, by rfl⟩ : syracuseStep 285599 = 428399) B428399
theorem B383903 : Blo 167798 383903 := bstep (se 1 (by rfl) ⟨287927, by rfl⟩ : syracuseStep 383903 = 575855) B575855
theorem B1367009 : Blo 167798 1367009 := bstep (se 2 (by rfl) ⟨512628, by rfl⟩ : syracuseStep 1367009 = 1025257) B1025257
theorem B253049 : Blo 167798 253049 := bstep (se 2 (by rfl) ⟨94893, by rfl⟩ : syracuseStep 253049 = 189787) B189787
theorem B253151 : Blo 167798 253151 := bstep (se 1 (by rfl) ⟨189863, by rfl⟩ : syracuseStep 253151 = 379727) B379727
theorem B253193 : Blo 167798 253193 := bstep (se 2 (by rfl) ⟨94947, by rfl⟩ : syracuseStep 253193 = 189895) B189895
theorem B286031 : Blo 167798 286031 := bstep (se 1 (by rfl) ⟨214523, by rfl⟩ : syracuseStep 286031 = 429047) B429047
theorem B253295 : Blo 167798 253295 := bstep (se 1 (by rfl) ⟨189971, by rfl⟩ : syracuseStep 253295 = 379943) B379943
theorem B253415 : Blo 167798 253415 := bstep (se 1 (by rfl) ⟨190061, by rfl⟩ : syracuseStep 253415 = 380123) B380123
theorem B253547 : Blo 167798 253547 := bstep (se 1 (by rfl) ⟨190160, by rfl⟩ : syracuseStep 253547 = 380321) B380321
theorem B253673 : Blo 167798 253673 := bstep (se 2 (by rfl) ⟨95127, by rfl⟩ : syracuseStep 253673 = 190255) B190255
theorem B384839 : Blo 167798 384839 := bstep (se 1 (by rfl) ⟨288629, by rfl⟩ : syracuseStep 384839 = 577259) B577259
theorem B253817 : Blo 167798 253817 := bstep (se 2 (by rfl) ⟨95181, by rfl⟩ : syracuseStep 253817 = 190363) B190363
theorem B909245 : Blo 167798 909245 := bstep (se 3 (by rfl) ⟨170483, by rfl⟩ : syracuseStep 909245 = 340967) B340967
theorem B253919 : Blo 167798 253919 := bstep (se 1 (by rfl) ⟨190439, by rfl⟩ : syracuseStep 253919 = 380879) B380879
theorem B1564645 : Blo 167798 1564645 := bstep (se 4 (by rfl) ⟨146685, by rfl⟩ : syracuseStep 1564645 = 293371) B293371
theorem B254171 : Blo 167798 254171 := bstep (se 1 (by rfl) ⟨190628, by rfl⟩ : syracuseStep 254171 = 381257) B381257
theorem B254183 : Blo 167798 254183 := bstep (se 1 (by rfl) ⟨190637, by rfl⟩ : syracuseStep 254183 = 381275) B381275
theorem B516449 : Blo 167798 516449 := bstep (se 2 (by rfl) ⟨193668, by rfl⟩ : syracuseStep 516449 = 387337) B387337
theorem B254345 : Blo 167798 254345 := bstep (se 2 (by rfl) ⟨95379, by rfl⟩ : syracuseStep 254345 = 190759) B190759
theorem B582071 : Blo 167798 582071 := bstep (se 1 (by rfl) ⟨436553, by rfl⟩ : syracuseStep 582071 = 873107) B873107
theorem B385487 : Blo 167798 385487 := bstep (se 1 (by rfl) ⟨289115, by rfl⟩ : syracuseStep 385487 = 578231) B578231
theorem B254441 : Blo 167798 254441 := bstep (se 2 (by rfl) ⟨95415, by rfl⟩ : syracuseStep 254441 = 190831) B190831
theorem B287327 : Blo 167798 287327 := bstep (se 1 (by rfl) ⟨215495, by rfl⟩ : syracuseStep 287327 = 430991) B430991
theorem B189031 : Blo 167798 189031 := bstep (se 1 (by rfl) ⟨141773, by rfl⟩ : syracuseStep 189031 = 283547) B283547
theorem B254567 : Blo 167798 254567 := bstep (se 1 (by rfl) ⟨190925, by rfl⟩ : syracuseStep 254567 = 381851) B381851
theorem B254699 : Blo 167798 254699 := bstep (se 1 (by rfl) ⟨191024, by rfl⟩ : syracuseStep 254699 = 382049) B382049
theorem B254729 : Blo 167798 254729 := bstep (se 2 (by rfl) ⟨95523, by rfl⟩ : syracuseStep 254729 = 191047) B191047
theorem B254831 : Blo 167798 254831 := bstep (se 1 (by rfl) ⟨191123, by rfl⟩ : syracuseStep 254831 = 382247) B382247
theorem B1303451 : Blo 167798 1303451 := bstep (se 1 (by rfl) ⟨977588, by rfl⟩ : syracuseStep 1303451 = 1955177) B1955177
theorem B615325 : Blo 167798 615325 := bstep (se 3 (by rfl) ⟨115373, by rfl⟩ : syracuseStep 615325 = 230747) B230747
theorem B386153 : Blo 167798 386153 := bstep (se 2 (by rfl) ⟨144807, by rfl⟩ : syracuseStep 386153 = 289615) B289615
theorem B255083 : Blo 167798 255083 := bstep (se 1 (by rfl) ⟨191312, by rfl⟩ : syracuseStep 255083 = 382625) B382625
theorem B975995 : Blo 167798 975995 := bstep (se 1 (by rfl) ⟨731996, by rfl⟩ : syracuseStep 975995 = 1463993) B1463993
theorem B779453 : Blo 167798 779453 := bstep (se 3 (by rfl) ⟨146147, by rfl⟩ : syracuseStep 779453 = 292295) B292295
theorem B255323 : Blo 167798 255323 := bstep (se 1 (by rfl) ⟨191492, by rfl⟩ : syracuseStep 255323 = 382985) B382985
theorem B812425 : Blo 167798 812425 := bstep (se 2 (by rfl) ⟨304659, by rfl⟩ : syracuseStep 812425 = 609319) B609319
theorem B648719 : Blo 167798 648719 := bstep (se 1 (by rfl) ⟨486539, by rfl⟩ : syracuseStep 648719 = 973079) B973079
theorem B255599 : Blo 167798 255599 := bstep (se 1 (by rfl) ⟨191699, by rfl⟩ : syracuseStep 255599 = 383399) B383399
theorem B878201 : Blo 167798 878201 := bstep (se 2 (by rfl) ⟨329325, by rfl⟩ : syracuseStep 878201 = 658651) B658651
theorem B255671 : Blo 167798 255671 := bstep (se 1 (by rfl) ⟨191753, by rfl⟩ : syracuseStep 255671 = 383507) B383507
theorem B255707 : Blo 167798 255707 := bstep (se 1 (by rfl) ⟨191780, by rfl⟩ : syracuseStep 255707 = 383561) B383561
theorem B255881 : Blo 167798 255881 := bstep (se 2 (by rfl) ⟨95955, by rfl⟩ : syracuseStep 255881 = 191911) B191911
theorem B255983 : Blo 167798 255983 := bstep (se 1 (by rfl) ⟨191987, by rfl⟩ : syracuseStep 255983 = 383975) B383975
theorem B288751 : Blo 167798 288751 := bstep (se 1 (by rfl) ⟨216563, by rfl⟩ : syracuseStep 288751 = 433127) B433127
theorem B977021 : Blo 167798 977021 := bstep (se 3 (by rfl) ⟨183191, by rfl⟩ : syracuseStep 977021 = 366383) B366383
theorem B911513 : Blo 167798 911513 := bstep (se 2 (by rfl) ⟨341817, by rfl⟩ : syracuseStep 911513 = 683635) B683635
theorem B289001 : Blo 167798 289001 := bstep (se 2 (by rfl) ⟨108375, by rfl⟩ : syracuseStep 289001 = 216751) B216751
theorem B256235 : Blo 167798 256235 := bstep (se 1 (by rfl) ⟨192176, by rfl⟩ : syracuseStep 256235 = 384353) B384353
theorem B256295 : Blo 167798 256295 := bstep (se 1 (by rfl) ⟨192221, by rfl⟩ : syracuseStep 256295 = 384443) B384443
theorem B256379 : Blo 167798 256379 := bstep (se 1 (by rfl) ⟨192284, by rfl⟩ : syracuseStep 256379 = 384569) B384569
theorem B485959 : Blo 167798 485959 := bstep (se 1 (by rfl) ⟨364469, by rfl⟩ : syracuseStep 485959 = 728939) B728939
theorem B584263 : Blo 167798 584263 := bstep (se 1 (by rfl) ⟨438197, by rfl⟩ : syracuseStep 584263 = 876395) B876395
theorem B485993 : Blo 167798 485993 := bstep (se 2 (by rfl) ⟨182247, by rfl⟩ : syracuseStep 485993 = 364495) B364495
theorem B256649 : Blo 167798 256649 := bstep (se 2 (by rfl) ⟨96243, by rfl⟩ : syracuseStep 256649 = 192487) B192487
theorem B256823 : Blo 167798 256823 := bstep (se 1 (by rfl) ⟨192617, by rfl⟩ : syracuseStep 256823 = 385235) B385235
theorem B256859 : Blo 167798 256859 := bstep (se 1 (by rfl) ⟨192644, by rfl⟩ : syracuseStep 256859 = 385289) B385289
theorem B257003 : Blo 167798 257003 := bstep (se 1 (by rfl) ⟨192752, by rfl⟩ : syracuseStep 257003 = 385505) B385505
theorem B31878157 : Blo 167798 31878157 := bstep (se 3 (by rfl) ⟨5977154, by rfl⟩ : syracuseStep 31878157 = 11954309) B11954309
theorem B617593 : Blo 167798 617593 := bstep (se 2 (by rfl) ⟨231597, by rfl⟩ : syracuseStep 617593 = 463195) B463195
theorem B650375 : Blo 167798 650375 := bstep (se 1 (by rfl) ⟨487781, by rfl⟩ : syracuseStep 650375 = 975563) B975563
theorem B257207 : Blo 167798 257207 := bstep (se 1 (by rfl) ⟨192905, by rfl⟩ : syracuseStep 257207 = 385811) B385811
theorem B257447 : Blo 167798 257447 := bstep (se 1 (by rfl) ⟨193085, by rfl⟩ : syracuseStep 257447 = 386171) B386171
theorem B257531 : Blo 167798 257531 := bstep (se 1 (by rfl) ⟨193148, by rfl⟩ : syracuseStep 257531 = 386297) B386297
theorem B192091 : Blo 167798 192091 := bstep (se 1 (by rfl) ⟨144068, by rfl⟩ : syracuseStep 192091 = 288137) B288137
theorem B257627 : Blo 167798 257627 := bstep (se 1 (by rfl) ⟨193220, by rfl⟩ : syracuseStep 257627 = 386441) B386441
theorem B192379 : Blo 167798 192379 := bstep (se 1 (by rfl) ⟨144284, by rfl⟩ : syracuseStep 192379 = 288569) B288569
theorem B3076289 : Blo 167798 3076289 := bstep (se 2 (by rfl) ⟨1153608, by rfl⟩ : syracuseStep 3076289 = 2307217) B2307217
theorem B520951 : Blo 167798 520951 := bstep (se 1 (by rfl) ⟨390713, by rfl⟩ : syracuseStep 520951 = 781427) B781427
theorem B488521 : Blo 167798 488521 := bstep (se 2 (by rfl) ⟨183195, by rfl⟩ : syracuseStep 488521 = 366391) B366391
theorem B292187 : Blo 167798 292187 := bstep (se 1 (by rfl) ⟨219140, by rfl⟩ : syracuseStep 292187 = 438281) B438281
theorem B1635997 : Blo 167798 1635997 := bstep (se 3 (by rfl) ⟨306749, by rfl⟩ : syracuseStep 1635997 = 613499) B613499
theorem B522215 : Blo 167798 522215 := bstep (se 1 (by rfl) ⟨391661, by rfl⟩ : syracuseStep 522215 = 783323) B783323
theorem B391151 : Blo 167798 391151 := bstep (se 1 (by rfl) ⟨293363, by rfl⟩ : syracuseStep 391151 = 586727) B586727
theorem B850985 : Blo 167798 850985 := bstep (se 2 (by rfl) ⟨319119, by rfl⟩ : syracuseStep 850985 = 638239) B638239
theorem B4129049 : Blo 167798 4129049 := bstep (se 2 (by rfl) ⟨1548393, by rfl⟩ : syracuseStep 4129049 = 3096787) B3096787
theorem B819575 : Blo 167798 819575 := bstep (se 1 (by rfl) ⟨614681, by rfl⟩ : syracuseStep 819575 = 1229363) B1229363
theorem B426455 : Blo 167798 426455 := bstep (se 1 (by rfl) ⟨319841, by rfl⟩ : syracuseStep 426455 = 639683) B639683
theorem B1442873 : Blo 167798 1442873 := bstep (se 2 (by rfl) ⟨541077, by rfl⟩ : syracuseStep 1442873 = 1082155) B1082155
theorem B820433 : Blo 167798 820433 := bstep (se 2 (by rfl) ⟨307662, by rfl⟩ : syracuseStep 820433 = 615325) B615325
theorem B1083233 : Blo 167798 1083233 := bstep (se 2 (by rfl) ⟨406212, by rfl⟩ : syracuseStep 1083233 = 812425) B812425
theorem B985483 : Blo 167798 985483 := bstep (se 1 (by rfl) ⟨739112, by rfl⟩ : syracuseStep 985483 = 1478225) B1478225
theorem B1640843 : Blo 167798 1640843 := bstep (se 1 (by rfl) ⟨1230632, by rfl⟩ : syracuseStep 1640843 = 2461265) B2461265
theorem B1280609 : Blo 167798 1280609 := bstep (se 2 (by rfl) ⟨480228, by rfl⟩ : syracuseStep 1280609 = 960457) B960457
theorem B363145 : Blo 167798 363145 := bstep (se 2 (by rfl) ⟨136179, by rfl⟩ : syracuseStep 363145 = 272359) B272359
theorem B854711 : Blo 167798 854711 := bstep (se 1 (by rfl) ⟨641033, by rfl⟩ : syracuseStep 854711 = 1282067) B1282067
theorem B12881029 : Blo 167798 12881029 := bstep (se 4 (by rfl) ⟨1207596, by rfl⟩ : syracuseStep 12881029 = 2415193) B2415193
theorem B724103 : Blo 167798 724103 := bstep (se 1 (by rfl) ⟨543077, by rfl⟩ : syracuseStep 724103 = 1086155) B1086155
theorem B23662043 : Blo 167798 23662043 := bstep (se 1 (by rfl) ⟨17746532, by rfl⟩ : syracuseStep 23662043 = 35493065) B35493065
theorem B855521 : Blo 167798 855521 := bstep (se 2 (by rfl) ⟨320820, by rfl⟩ : syracuseStep 855521 = 641641) B641641
theorem B6622715 : Blo 167798 6622715 := bstep (se 1 (by rfl) ⟨4967036, by rfl⟩ : syracuseStep 6622715 = 9934073) B9934073
theorem B167807 : Blo 167798 167807 := bstep (se 1 (by rfl) ⟨125855, by rfl⟩ : syracuseStep 167807 = 251711) B251711
theorem B167919 : Blo 167798 167919 := bstep (se 1 (by rfl) ⟨125939, by rfl⟩ : syracuseStep 167919 = 251879) B251879
theorem B167931 : Blo 167798 167931 := bstep (se 1 (by rfl) ⟨125948, by rfl⟩ : syracuseStep 167931 = 251897) B251897
theorem B42504209 : Blo 167798 42504209 := bstep (se 2 (by rfl) ⟨15939078, by rfl⟩ : syracuseStep 42504209 = 31878157) B31878157
theorem B167999 : Blo 167798 167999 := bstep (se 1 (by rfl) ⟨125999, by rfl⟩ : syracuseStep 167999 = 251999) B251999
theorem B168039 : Blo 167798 168039 := bstep (se 1 (by rfl) ⟨126029, by rfl⟩ : syracuseStep 168039 = 252059) B252059
theorem B692327 : Blo 167798 692327 := bstep (se 1 (by rfl) ⟨519245, by rfl⟩ : syracuseStep 692327 = 1038491) B1038491
theorem B168063 : Blo 167798 168063 := bstep (se 1 (by rfl) ⟨126047, by rfl⟩ : syracuseStep 168063 = 252095) B252095
theorem B168091 : Blo 167798 168091 := bstep (se 1 (by rfl) ⟨126068, by rfl⟩ : syracuseStep 168091 = 252137) B252137
theorem B823457 : Blo 167798 823457 := bstep (se 2 (by rfl) ⟨308796, by rfl⟩ : syracuseStep 823457 = 617593) B617593
theorem B168295 : Blo 167798 168295 := bstep (se 1 (by rfl) ⟨126221, by rfl⟩ : syracuseStep 168295 = 252443) B252443
theorem B168347 : Blo 167798 168347 := bstep (se 1 (by rfl) ⟨126260, by rfl⟩ : syracuseStep 168347 = 252521) B252521
theorem B168699 : Blo 167798 168699 := bstep (se 1 (by rfl) ⟨126524, by rfl⟩ : syracuseStep 168699 = 253049) B253049
theorem B168767 : Blo 167798 168767 := bstep (se 1 (by rfl) ⟨126575, by rfl⟩ : syracuseStep 168767 = 253151) B253151
theorem B168795 : Blo 167798 168795 := bstep (se 1 (by rfl) ⟨126596, by rfl⟩ : syracuseStep 168795 = 253193) B253193
theorem B168863 : Blo 167798 168863 := bstep (se 1 (by rfl) ⟨126647, by rfl⟩ : syracuseStep 168863 = 253295) B253295
theorem B168943 : Blo 167798 168943 := bstep (se 1 (by rfl) ⟨126707, by rfl⟩ : syracuseStep 168943 = 253415) B253415
theorem B169031 : Blo 167798 169031 := bstep (se 1 (by rfl) ⟨126773, by rfl⟩ : syracuseStep 169031 = 253547) B253547
theorem B169115 : Blo 167798 169115 := bstep (se 1 (by rfl) ⟨126836, by rfl⟩ : syracuseStep 169115 = 253673) B253673
theorem B726205 : Blo 167798 726205 := bstep (se 3 (by rfl) ⟨136163, by rfl⟩ : syracuseStep 726205 = 272327) B272327
theorem B169211 : Blo 167798 169211 := bstep (se 1 (by rfl) ⟨126908, by rfl⟩ : syracuseStep 169211 = 253817) B253817
theorem B169279 : Blo 167798 169279 := bstep (se 1 (by rfl) ⟨126959, by rfl⟩ : syracuseStep 169279 = 253919) B253919
theorem B169447 : Blo 167798 169447 := bstep (se 1 (by rfl) ⟨127085, by rfl⟩ : syracuseStep 169447 = 254171) B254171
theorem B169455 : Blo 167798 169455 := bstep (se 1 (by rfl) ⟨127091, by rfl⟩ : syracuseStep 169455 = 254183) B254183
theorem B726529 : Blo 167798 726529 := bstep (se 2 (by rfl) ⟨272448, by rfl⟩ : syracuseStep 726529 = 544897) B544897
theorem B169563 : Blo 167798 169563 := bstep (se 1 (by rfl) ⟨127172, by rfl⟩ : syracuseStep 169563 = 254345) B254345
theorem B169627 : Blo 167798 169627 := bstep (se 1 (by rfl) ⟨127220, by rfl⟩ : syracuseStep 169627 = 254441) B254441
theorem B169711 : Blo 167798 169711 := bstep (se 1 (by rfl) ⟨127283, by rfl⟩ : syracuseStep 169711 = 254567) B254567
theorem B169799 : Blo 167798 169799 := bstep (se 1 (by rfl) ⟨127349, by rfl⟩ : syracuseStep 169799 = 254699) B254699
theorem B169819 : Blo 167798 169819 := bstep (se 1 (by rfl) ⟨127364, by rfl⟩ : syracuseStep 169819 = 254729) B254729
theorem B169887 : Blo 167798 169887 := bstep (se 1 (by rfl) ⟨127415, by rfl⟩ : syracuseStep 169887 = 254831) B254831
theorem B170055 : Blo 167798 170055 := bstep (se 1 (by rfl) ⟨127541, by rfl⟩ : syracuseStep 170055 = 255083) B255083
theorem B170215 : Blo 167798 170215 := bstep (se 1 (by rfl) ⟨127661, by rfl⟩ : syracuseStep 170215 = 255323) B255323
theorem B694601 : Blo 167798 694601 := bstep (se 2 (by rfl) ⟨260475, by rfl⟩ : syracuseStep 694601 = 520951) B520951
theorem B432479 : Blo 167798 432479 := bstep (se 1 (by rfl) ⟨324359, by rfl⟩ : syracuseStep 432479 = 648719) B648719
theorem B170399 : Blo 167798 170399 := bstep (se 1 (by rfl) ⟨127799, by rfl⟩ : syracuseStep 170399 = 255599) B255599
theorem B170447 : Blo 167798 170447 := bstep (se 1 (by rfl) ⟨127835, by rfl⟩ : syracuseStep 170447 = 255671) B255671
theorem B170471 : Blo 167798 170471 := bstep (se 1 (by rfl) ⟨127853, by rfl⟩ : syracuseStep 170471 = 255707) B255707
theorem B858599 : Blo 167798 858599 := bstep (se 1 (by rfl) ⟨643949, by rfl⟩ : syracuseStep 858599 = 1287899) B1287899
theorem B170587 : Blo 167798 170587 := bstep (se 1 (by rfl) ⟨127940, by rfl⟩ : syracuseStep 170587 = 255881) B255881
theorem B170655 : Blo 167798 170655 := bstep (se 1 (by rfl) ⟨127991, by rfl⟩ : syracuseStep 170655 = 255983) B255983
theorem B170823 : Blo 167798 170823 := bstep (se 1 (by rfl) ⟨128117, by rfl⟩ : syracuseStep 170823 = 256235) B256235
theorem B170863 : Blo 167798 170863 := bstep (se 1 (by rfl) ⟨128147, by rfl⟩ : syracuseStep 170863 = 256295) B256295
theorem B170919 : Blo 167798 170919 := bstep (se 1 (by rfl) ⟨128189, by rfl⟩ : syracuseStep 170919 = 256379) B256379
theorem B728135 : Blo 167798 728135 := bstep (se 1 (by rfl) ⟨546101, by rfl⟩ : syracuseStep 728135 = 1092203) B1092203
theorem B171099 : Blo 167798 171099 := bstep (se 1 (by rfl) ⟨128324, by rfl⟩ : syracuseStep 171099 = 256649) B256649
theorem B171215 : Blo 167798 171215 := bstep (se 1 (by rfl) ⟨128411, by rfl⟩ : syracuseStep 171215 = 256823) B256823
theorem B171239 : Blo 167798 171239 := bstep (se 1 (by rfl) ⟨128429, by rfl⟩ : syracuseStep 171239 = 256859) B256859
theorem B171335 : Blo 167798 171335 := bstep (se 1 (by rfl) ⟨128501, by rfl⟩ : syracuseStep 171335 = 257003) B257003
theorem B433583 : Blo 167798 433583 := bstep (se 1 (by rfl) ⟨325187, by rfl⟩ : syracuseStep 433583 = 650375) B650375
theorem B171471 : Blo 167798 171471 := bstep (se 1 (by rfl) ⟨128603, by rfl⟩ : syracuseStep 171471 = 257207) B257207
theorem B171631 : Blo 167798 171631 := bstep (se 1 (by rfl) ⟨128723, by rfl⟩ : syracuseStep 171631 = 257447) B257447
theorem B171687 : Blo 167798 171687 := bstep (se 1 (by rfl) ⟨128765, by rfl⟩ : syracuseStep 171687 = 257531) B257531
theorem B171751 : Blo 167798 171751 := bstep (se 1 (by rfl) ⟨128813, by rfl⟩ : syracuseStep 171751 = 257627) B257627
theorem B859895 : Blo 167798 859895 := bstep (se 1 (by rfl) ⟨644921, by rfl⟩ : syracuseStep 859895 = 1289843) B1289843
theorem B2073089 : Blo 167798 2073089 := bstep (se 2 (by rfl) ⟨777408, by rfl⟩ : syracuseStep 2073089 = 1554817) B1554817
theorem B205519 : Blo 167798 205519 := bstep (se 1 (by rfl) ⟨154139, by rfl⟩ : syracuseStep 205519 = 308279) B308279
theorem B567323 : Blo 167798 567323 := bstep (se 1 (by rfl) ⟨425492, by rfl⟩ : syracuseStep 567323 = 850985) B850985
theorem B403579 : Blo 167798 403579 := bstep (se 1 (by rfl) ⟨302684, by rfl⟩ : syracuseStep 403579 = 605369) B605369
theorem B567485 : Blo 167798 567485 := bstep (se 3 (by rfl) ⟨106403, by rfl⟩ : syracuseStep 567485 = 212807) B212807
theorem B6564077 : Blo 167798 6564077 := bstep (se 3 (by rfl) ⟨1230764, by rfl⟩ : syracuseStep 6564077 = 2461529) B2461529
theorem B2468987 : Blo 167798 2468987 := bstep (se 1 (by rfl) ⟨1851740, by rfl⟩ : syracuseStep 2468987 = 3703481) B3703481
theorem B4304015 : Blo 167798 4304015 := bstep (se 1 (by rfl) ⟨3228011, by rfl⟩ : syracuseStep 4304015 = 6456023) B6456023
theorem B699967 : Blo 167798 699967 := bstep (se 1 (by rfl) ⟨524975, by rfl⟩ : syracuseStep 699967 = 1049951) B1049951
theorem B4894505 : Blo 167798 4894505 := bstep (se 2 (by rfl) ⟨1835439, by rfl⟩ : syracuseStep 4894505 = 3670879) B3670879
theorem B569213 : Blo 167798 569213 := bstep (se 3 (by rfl) ⟨106727, by rfl⟩ : syracuseStep 569213 = 213455) B213455
theorem B962441 : Blo 167798 962441 := bstep (se 2 (by rfl) ⟨360915, by rfl⟩ : syracuseStep 962441 = 721831) B721831
theorem B307327 : Blo 167798 307327 := bstep (se 1 (by rfl) ⟨230495, by rfl⟩ : syracuseStep 307327 = 460991) B460991
theorem B569483 : Blo 167798 569483 := bstep (se 1 (by rfl) ⟨427112, by rfl⟩ : syracuseStep 569483 = 854225) B854225
theorem B1814723 : Blo 167798 1814723 := bstep (se 1 (by rfl) ⟨1361042, by rfl⟩ : syracuseStep 1814723 = 2722085) B2722085
theorem B242023 : Blo 167798 242023 := bstep (se 1 (by rfl) ⟨181517, by rfl⟩ : syracuseStep 242023 = 363035) B363035
theorem B438841 : Blo 167798 438841 := bstep (se 2 (by rfl) ⟨164565, by rfl⟩ : syracuseStep 438841 = 329131) B329131
theorem B1291301 : Blo 167798 1291301 := bstep (se 4 (by rfl) ⟨121059, by rfl⟩ : syracuseStep 1291301 = 242119) B242119
theorem B1095277 : Blo 167798 1095277 := bstep (se 3 (by rfl) ⟨205364, by rfl⟩ : syracuseStep 1095277 = 410729) B410729
theorem B570995 : Blo 167798 570995 := bstep (se 1 (by rfl) ⟨428246, by rfl⟩ : syracuseStep 570995 = 856493) B856493
theorem B571103 : Blo 167798 571103 := bstep (se 1 (by rfl) ⟨428327, by rfl⟩ : syracuseStep 571103 = 856655) B856655
theorem B571265 : Blo 167798 571265 := bstep (se 2 (by rfl) ⟨214224, by rfl⟩ : syracuseStep 571265 = 428449) B428449
theorem B2930579 : Blo 167798 2930579 := bstep (se 1 (by rfl) ⟨2197934, by rfl⟩ : syracuseStep 2930579 = 4395869) B4395869
theorem B964649 : Blo 167798 964649 := bstep (se 2 (by rfl) ⟨361743, by rfl⟩ : syracuseStep 964649 = 723487) B723487
theorem B309431 : Blo 167798 309431 := bstep (se 1 (by rfl) ⟨232073, by rfl⟩ : syracuseStep 309431 = 464147) B464147
theorem B571805 : Blo 167798 571805 := bstep (se 3 (by rfl) ⟨107213, by rfl⟩ : syracuseStep 571805 = 214427) B214427
theorem B572075 : Blo 167798 572075 := bstep (se 1 (by rfl) ⟨429056, by rfl⟩ : syracuseStep 572075 = 858113) B858113
theorem B572507 : Blo 167798 572507 := bstep (se 1 (by rfl) ⟨429380, by rfl⟩ : syracuseStep 572507 = 858761) B858761
theorem B638057 : Blo 167798 638057 := bstep (se 2 (by rfl) ⟨239271, by rfl⟩ : syracuseStep 638057 = 478543) B478543
theorem B572615 : Blo 167798 572615 := bstep (se 1 (by rfl) ⟨429461, by rfl⟩ : syracuseStep 572615 = 858923) B858923
theorem B1621235 : Blo 167798 1621235 := bstep (se 1 (by rfl) ⟨1215926, by rfl⟩ : syracuseStep 1621235 = 2431853) B2431853
theorem B6208757 : Blo 167798 6208757 := bstep (se 5 (by rfl) ⟨291035, by rfl⟩ : syracuseStep 6208757 = 582071) B582071
theorem B4963751 : Blo 167798 4963751 := bstep (se 1 (by rfl) ⟨3722813, by rfl⟩ : syracuseStep 4963751 = 7445627) B7445627
theorem B639211 : Blo 167798 639211 := bstep (se 1 (by rfl) ⟨479408, by rfl⟩ : syracuseStep 639211 = 958817) B958817
theorem B344299 : Blo 167798 344299 := bstep (se 1 (by rfl) ⟨258224, by rfl⟩ : syracuseStep 344299 = 516449) B516449
theorem B180479 : Blo 167798 180479 := bstep (se 1 (by rfl) ⟨135359, by rfl⟩ : syracuseStep 180479 = 270719) B270719
theorem B639485 : Blo 167798 639485 := bstep (se 3 (by rfl) ⟨119903, by rfl⟩ : syracuseStep 639485 = 239807) B239807
theorem B541181 : Blo 167798 541181 := bstep (se 3 (by rfl) ⟨101471, by rfl⟩ : syracuseStep 541181 = 202943) B202943
theorem B868967 : Blo 167798 868967 := bstep (se 1 (by rfl) ⟨651725, by rfl⟩ : syracuseStep 868967 = 1303451) B1303451
theorem B1557593 : Blo 167798 1557593 := bstep (se 2 (by rfl) ⟨584097, by rfl⟩ : syracuseStep 1557593 = 1168195) B1168195
theorem B377963 : Blo 167798 377963 := bstep (se 1 (by rfl) ⟨283472, by rfl⟩ : syracuseStep 377963 = 566945) B566945
theorem B247087 : Blo 167798 247087 := bstep (se 1 (by rfl) ⟨185315, by rfl⟩ : syracuseStep 247087 = 370631) B370631
theorem B2082145 : Blo 167798 2082145 := bstep (se 2 (by rfl) ⟨780804, by rfl⟩ : syracuseStep 2082145 = 1561609) B1561609
theorem B607675 : Blo 167798 607675 := bstep (se 1 (by rfl) ⟨455756, by rfl⟩ : syracuseStep 607675 = 911513) B911513
theorem B378431 : Blo 167798 378431 := bstep (se 1 (by rfl) ⟨283823, by rfl⟩ : syracuseStep 378431 = 567647) B567647
theorem B378539 : Blo 167798 378539 := bstep (se 1 (by rfl) ⟨283904, by rfl⟩ : syracuseStep 378539 = 567809) B567809
theorem B378863 : Blo 167798 378863 := bstep (se 1 (by rfl) ⟨284147, by rfl⟩ : syracuseStep 378863 = 568295) B568295
theorem B379079 : Blo 167798 379079 := bstep (se 1 (by rfl) ⟨284309, by rfl⟩ : syracuseStep 379079 = 568619) B568619
theorem B2181329 : Blo 167798 2181329 := bstep (se 2 (by rfl) ⟨817998, by rfl⟩ : syracuseStep 2181329 = 1635997) B1635997
theorem B379259 : Blo 167798 379259 := bstep (se 1 (by rfl) ⟨284444, by rfl⟩ : syracuseStep 379259 = 568889) B568889
theorem B1952261 : Blo 167798 1952261 := bstep (se 4 (by rfl) ⟨183024, by rfl⟩ : syracuseStep 1952261 = 366049) B366049
theorem B379529 : Blo 167798 379529 := bstep (se 2 (by rfl) ⟨142323, by rfl⟩ : syracuseStep 379529 = 284647) B284647
theorem B576161 : Blo 167798 576161 := bstep (se 2 (by rfl) ⟨216060, by rfl⟩ : syracuseStep 576161 = 432121) B432121
theorem B2050859 : Blo 167798 2050859 := bstep (se 1 (by rfl) ⟨1538144, by rfl⟩ : syracuseStep 2050859 = 3076289) B3076289
theorem B379817 : Blo 167798 379817 := bstep (se 2 (by rfl) ⟨142431, by rfl⟩ : syracuseStep 379817 = 284863) B284863
theorem B1035767 : Blo 167798 1035767 := bstep (se 1 (by rfl) ⟨776825, by rfl⟩ : syracuseStep 1035767 = 1553651) B1553651
theorem B380519 : Blo 167798 380519 := bstep (se 1 (by rfl) ⟨285389, by rfl⟩ : syracuseStep 380519 = 570779) B570779
theorem B642887 : Blo 167798 642887 := bstep (se 1 (by rfl) ⟨482165, by rfl⟩ : syracuseStep 642887 = 964331) B964331
theorem B348143 : Blo 167798 348143 := bstep (se 1 (by rfl) ⟨261107, by rfl⟩ : syracuseStep 348143 = 522215) B522215
theorem B381023 : Blo 167798 381023 := bstep (se 1 (by rfl) ⟨285767, by rfl⟩ : syracuseStep 381023 = 571535) B571535
theorem B184447 : Blo 167798 184447 := bstep (se 1 (by rfl) ⟨138335, by rfl⟩ : syracuseStep 184447 = 276671) B276671
theorem B577691 : Blo 167798 577691 := bstep (se 1 (by rfl) ⟨433268, by rfl⟩ : syracuseStep 577691 = 866537) B866537
theorem B643859 : Blo 167798 643859 := bstep (se 1 (by rfl) ⟨482894, by rfl⟩ : syracuseStep 643859 = 965789) B965789
theorem B381779 : Blo 167798 381779 := bstep (se 1 (by rfl) ⟨286334, by rfl⟩ : syracuseStep 381779 = 572669) B572669
theorem B578459 : Blo 167798 578459 := bstep (se 1 (by rfl) ⟨433844, by rfl⟩ : syracuseStep 578459 = 867689) B867689
theorem B283945 : Blo 167798 283945 := bstep (se 2 (by rfl) ⟨106479, by rfl⟩ : syracuseStep 283945 = 212959) B212959
theorem B2086193 : Blo 167798 2086193 := bstep (se 2 (by rfl) ⟨782322, by rfl⟩ : syracuseStep 2086193 = 1564645) B1564645
theorem B382319 : Blo 167798 382319 := bstep (se 1 (by rfl) ⟨286739, by rfl⟩ : syracuseStep 382319 = 573479) B573479
theorem B1463975 : Blo 167798 1463975 := bstep (se 1 (by rfl) ⟨1097981, by rfl⟩ : syracuseStep 1463975 = 2195963) B2195963
theorem B382751 : Blo 167798 382751 := bstep (se 1 (by rfl) ⟨287063, by rfl⟩ : syracuseStep 382751 = 574127) B574127
theorem B579419 : Blo 167798 579419 := bstep (se 1 (by rfl) ⟨434564, by rfl⟩ : syracuseStep 579419 = 869129) B869129
theorem B251771 : Blo 167798 251771 := bstep (se 1 (by rfl) ⟨188828, by rfl⟩ : syracuseStep 251771 = 377657) B377657
theorem B284539 : Blo 167798 284539 := bstep (se 1 (by rfl) ⟨213404, by rfl⟩ : syracuseStep 284539 = 426809) B426809
theorem B251807 : Blo 167798 251807 := bstep (se 1 (by rfl) ⟨188855, by rfl⟩ : syracuseStep 251807 = 377711) B377711
theorem B382967 : Blo 167798 382967 := bstep (se 1 (by rfl) ⟨287225, by rfl⟩ : syracuseStep 382967 = 574451) B574451
theorem B252041 : Blo 167798 252041 := bstep (se 2 (by rfl) ⟨94515, by rfl⟩ : syracuseStep 252041 = 189031) B189031
theorem B284809 : Blo 167798 284809 := bstep (se 2 (by rfl) ⟨106803, by rfl⟩ : syracuseStep 284809 = 213607) B213607
theorem B252191 : Blo 167798 252191 := bstep (se 1 (by rfl) ⟨189143, by rfl⟩ : syracuseStep 252191 = 378287) B378287
theorem B481619 : Blo 167798 481619 := bstep (se 1 (by rfl) ⟨361214, by rfl⟩ : syracuseStep 481619 = 722429) B722429
theorem B383327 : Blo 167798 383327 := bstep (se 1 (by rfl) ⟨287495, by rfl⟩ : syracuseStep 383327 = 574991) B574991
theorem B2087279 : Blo 167798 2087279 := bstep (se 1 (by rfl) ⟨1565459, by rfl⟩ : syracuseStep 2087279 = 3130919) B3130919
theorem B252743 : Blo 167798 252743 := bstep (se 1 (by rfl) ⟨189557, by rfl⟩ : syracuseStep 252743 = 379115) B379115
theorem B285511 : Blo 167798 285511 := bstep (se 1 (by rfl) ⟨214133, by rfl⟩ : syracuseStep 285511 = 428267) B428267
theorem B383867 : Blo 167798 383867 := bstep (se 1 (by rfl) ⟨287900, by rfl⟩ : syracuseStep 383867 = 575801) B575801
theorem B384047 : Blo 167798 384047 := bstep (se 1 (by rfl) ⟨288035, by rfl⟩ : syracuseStep 384047 = 576071) B576071
theorem B548203 : Blo 167798 548203 := bstep (se 1 (by rfl) ⟨411152, by rfl⟩ : syracuseStep 548203 = 822305) B822305
theorem B318953 : Blo 167798 318953 := bstep (se 2 (by rfl) ⟨119607, by rfl⟩ : syracuseStep 318953 = 239215) B239215
theorem B253607 : Blo 167798 253607 := bstep (se 1 (by rfl) ⟨190205, by rfl⟩ : syracuseStep 253607 = 380411) B380411
theorem B286375 : Blo 167798 286375 := bstep (se 1 (by rfl) ⟨214781, by rfl⟩ : syracuseStep 286375 = 429563) B429563
theorem B384731 : Blo 167798 384731 := bstep (se 1 (by rfl) ⟨288548, by rfl⟩ : syracuseStep 384731 = 577097) B577097
theorem B253727 : Blo 167798 253727 := bstep (se 1 (by rfl) ⟨190295, by rfl⟩ : syracuseStep 253727 = 380591) B380591
theorem B2318213 : Blo 167798 2318213 := bstep (se 4 (by rfl) ⟨217332, by rfl⟩ : syracuseStep 2318213 = 434665) B434665
theorem B385001 : Blo 167798 385001 := bstep (se 2 (by rfl) ⟨144375, by rfl⟩ : syracuseStep 385001 = 288751) B288751
theorem B647291 : Blo 167798 647291 := bstep (se 1 (by rfl) ⟨485468, by rfl⟩ : syracuseStep 647291 = 970937) B970937
theorem B254159 : Blo 167798 254159 := bstep (se 1 (by rfl) ⟨190619, by rfl⟩ : syracuseStep 254159 = 381239) B381239
theorem B254207 : Blo 167798 254207 := bstep (se 1 (by rfl) ⟨190655, by rfl⟩ : syracuseStep 254207 = 381311) B381311
theorem B188959 : Blo 167798 188959 := bstep (se 1 (by rfl) ⟨141719, by rfl⟩ : syracuseStep 188959 = 283439) B283439
theorem B2908709 : Blo 167798 2908709 := bstep (se 4 (by rfl) ⟨272691, by rfl⟩ : syracuseStep 2908709 = 545383) B545383
theorem B385703 : Blo 167798 385703 := bstep (se 1 (by rfl) ⟨289277, by rfl⟩ : syracuseStep 385703 = 578555) B578555
theorem B647945 : Blo 167798 647945 := bstep (se 2 (by rfl) ⟨242979, by rfl⟩ : syracuseStep 647945 = 485959) B485959
theorem B779017 : Blo 167798 779017 := bstep (se 2 (by rfl) ⟨292131, by rfl⟩ : syracuseStep 779017 = 584263) B584263
theorem B287543 : Blo 167798 287543 := bstep (se 1 (by rfl) ⟨215657, by rfl⟩ : syracuseStep 287543 = 431315) B431315
theorem B385847 : Blo 167798 385847 := bstep (se 1 (by rfl) ⟨289385, by rfl⟩ : syracuseStep 385847 = 578771) B578771
theorem B779165 : Blo 167798 779165 := bstep (se 3 (by rfl) ⟨146093, by rfl⟩ : syracuseStep 779165 = 292187) B292187
theorem B386027 : Blo 167798 386027 := bstep (se 1 (by rfl) ⟨289520, by rfl⟩ : syracuseStep 386027 = 579041) B579041
theorem B255023 : Blo 167798 255023 := bstep (se 1 (by rfl) ⟨191267, by rfl⟩ : syracuseStep 255023 = 382535) B382535
theorem B189607 : Blo 167798 189607 := bstep (se 1 (by rfl) ⟨142205, by rfl⟩ : syracuseStep 189607 = 284411) B284411
theorem B255143 : Blo 167798 255143 := bstep (se 1 (by rfl) ⟨191357, by rfl⟩ : syracuseStep 255143 = 382715) B382715
theorem B196338887 : Blo 167798 196338887 := bstep (se 1 (by rfl) ⟨147254165, by rfl⟩ : syracuseStep 196338887 = 294508331) B294508331
theorem B386459 : Blo 167798 386459 := bstep (se 1 (by rfl) ⟨289844, by rfl⟩ : syracuseStep 386459 = 579689) B579689
theorem B255515 : Blo 167798 255515 := bstep (se 1 (by rfl) ⟨191636, by rfl⟩ : syracuseStep 255515 = 383273) B383273
theorem B976495 : Blo 167798 976495 := bstep (se 1 (by rfl) ⟨732371, by rfl⟩ : syracuseStep 976495 = 1464743) B1464743
theorem B616211 : Blo 167798 616211 := bstep (se 1 (by rfl) ⟨462158, by rfl⟩ : syracuseStep 616211 = 924317) B924317
theorem B255899 : Blo 167798 255899 := bstep (se 1 (by rfl) ⟨191924, by rfl⟩ : syracuseStep 255899 = 383849) B383849
theorem B190399 : Blo 167798 190399 := bstep (se 1 (by rfl) ⟨142799, by rfl⟩ : syracuseStep 190399 = 285599) B285599
theorem B255935 : Blo 167798 255935 := bstep (se 1 (by rfl) ⟨191951, by rfl⟩ : syracuseStep 255935 = 383903) B383903
theorem B911339 : Blo 167798 911339 := bstep (se 1 (by rfl) ⟨683504, by rfl⟩ : syracuseStep 911339 = 1367009) B1367009
theorem B616427 : Blo 167798 616427 := bstep (se 1 (by rfl) ⟨462320, by rfl⟩ : syracuseStep 616427 = 924641) B924641
theorem B256121 : Blo 167798 256121 := bstep (se 2 (by rfl) ⟨96045, by rfl⟩ : syracuseStep 256121 = 192091) B192091
theorem B190687 : Blo 167798 190687 := bstep (se 1 (by rfl) ⟨143015, by rfl⟩ : syracuseStep 190687 = 286031) B286031
theorem B4680179 : Blo 167798 4680179 := bstep (se 1 (by rfl) ⟨3510134, by rfl⟩ : syracuseStep 4680179 = 7020269) B7020269
theorem B289271 : Blo 167798 289271 := bstep (se 1 (by rfl) ⟨216953, by rfl⟩ : syracuseStep 289271 = 433907) B433907
theorem B256505 : Blo 167798 256505 := bstep (se 2 (by rfl) ⟨96189, by rfl⟩ : syracuseStep 256505 = 192379) B192379
theorem B256559 : Blo 167798 256559 := bstep (se 1 (by rfl) ⟨192419, by rfl⟩ : syracuseStep 256559 = 384839) B384839
theorem B256991 : Blo 167798 256991 := bstep (se 1 (by rfl) ⟨192743, by rfl⟩ : syracuseStep 256991 = 385487) B385487
theorem B191551 : Blo 167798 191551 := bstep (se 1 (by rfl) ⟨143663, by rfl⟩ : syracuseStep 191551 = 287327) B287327
theorem B289865 : Blo 167798 289865 := bstep (se 2 (by rfl) ⟨108699, by rfl⟩ : syracuseStep 289865 = 217399) B217399
theorem B257435 : Blo 167798 257435 := bstep (se 1 (by rfl) ⟨193076, by rfl⟩ : syracuseStep 257435 = 386153) B386153
theorem B650663 : Blo 167798 650663 := bstep (se 1 (by rfl) ⟨487997, by rfl⟩ : syracuseStep 650663 = 975995) B975995
theorem B519635 : Blo 167798 519635 := bstep (se 1 (by rfl) ⟨389726, by rfl⟩ : syracuseStep 519635 = 779453) B779453
theorem B552673 : Blo 167798 552673 := bstep (se 2 (by rfl) ⟨207252, by rfl⟩ : syracuseStep 552673 = 414505) B414505
theorem B585467 : Blo 167798 585467 := bstep (se 1 (by rfl) ⟨439100, by rfl⟩ : syracuseStep 585467 = 878201) B878201
theorem B487417 : Blo 167798 487417 := bstep (se 2 (by rfl) ⟨182781, by rfl⟩ : syracuseStep 487417 = 365563) B365563
theorem B651347 : Blo 167798 651347 := bstep (se 1 (by rfl) ⟨488510, by rfl⟩ : syracuseStep 651347 = 977021) B977021
theorem B651361 : Blo 167798 651361 := bstep (se 2 (by rfl) ⟨244260, by rfl⟩ : syracuseStep 651361 = 488521) B488521
theorem B192667 : Blo 167798 192667 := bstep (se 1 (by rfl) ⟨144500, by rfl⟩ : syracuseStep 192667 = 289001) B289001
theorem B487705 : Blo 167798 487705 := bstep (se 2 (by rfl) ⟨182889, by rfl⟩ : syracuseStep 487705 = 365779) B365779
theorem B323995 : Blo 167798 323995 := bstep (se 1 (by rfl) ⟨242996, by rfl⟩ : syracuseStep 323995 = 485993) B485993
theorem B2913083 : Blo 167798 2913083 := bstep (se 1 (by rfl) ⟨2184812, by rfl⟩ : syracuseStep 2913083 = 4369625) B4369625
theorem B2388797 : Blo 167798 2388797 := bstep (se 3 (by rfl) ⟨447899, by rfl⟩ : syracuseStep 2388797 = 895799) B895799
theorem B488875 : Blo 167798 488875 := bstep (se 1 (by rfl) ⟨366656, by rfl⟩ : syracuseStep 488875 = 733313) B733313
theorem B4356503 : Blo 167798 4356503 := bstep (se 1 (by rfl) ⟨3267377, by rfl⟩ : syracuseStep 4356503 = 6534755) B6534755
theorem B260767 : Blo 167798 260767 := bstep (se 1 (by rfl) ⟨195575, by rfl⟩ : syracuseStep 260767 = 391151) B391151
theorem B359147 : Blo 167798 359147 := bstep (se 1 (by rfl) ⟨269360, by rfl⟩ : syracuseStep 359147 = 538721) B538721
theorem B2194451 : Blo 167798 2194451 := bstep (se 1 (by rfl) ⟨1645838, by rfl⟩ : syracuseStep 2194451 = 3291677) B3291677
theorem B982297 : Blo 167798 982297 := bstep (se 2 (by rfl) ⟨368361, by rfl⟩ : syracuseStep 982297 = 736723) B736723
theorem B2424653 : Blo 167798 2424653 := bstep (se 3 (by rfl) ⟨454622, by rfl⟩ : syracuseStep 2424653 = 909245) B909245
theorem B425807 : Blo 167798 425807 := bstep (se 1 (by rfl) ⟨319355, by rfl⟩ : syracuseStep 425807 = 638711) B638711
theorem B2752699 : Blo 167798 2752699 := bstep (se 1 (by rfl) ⟨2064524, by rfl⟩ : syracuseStep 2752699 = 4129049) B4129049
theorem B852281 : Blo 167798 852281 := bstep (se 2 (by rfl) ⟨319605, by rfl⟩ : syracuseStep 852281 = 639211) B639211
theorem B459065 : Blo 167798 459065 := bstep (se 2 (by rfl) ⟨172149, by rfl⟩ : syracuseStep 459065 = 344299) B344299
theorem B426323 : Blo 167798 426323 := bstep (se 1 (by rfl) ⟨319742, by rfl⟩ : syracuseStep 426323 = 639485) B639485
theorem B360787 : Blo 167798 360787 := bstep (se 1 (by rfl) ⟨270590, by rfl⟩ : syracuseStep 360787 = 541181) B541181
theorem B2195885 : Blo 167798 2195885 := bstep (se 3 (by rfl) ⟨411728, by rfl⟩ : syracuseStep 2195885 = 823457) B823457
theorem B722155 : Blo 167798 722155 := bstep (se 1 (by rfl) ⟨541616, by rfl⟩ : syracuseStep 722155 = 1083233) B1083233
theorem B329449 : Blo 167798 329449 := bstep (se 2 (by rfl) ⟨123543, by rfl⟩ : syracuseStep 329449 = 247087) B247087
theorem B853739 : Blo 167798 853739 := bstep (se 1 (by rfl) ⟨640304, by rfl⟩ : syracuseStep 853739 = 1280609) B1280609
theorem B1542557 : Blo 167798 1542557 := bstep (se 3 (by rfl) ⟨289229, by rfl⟩ : syracuseStep 1542557 = 578459) B578459
theorem B428591 : Blo 167798 428591 := bstep (se 1 (by rfl) ⟨321443, by rfl⟩ : syracuseStep 428591 = 642887) B642887
theorem B429239 : Blo 167798 429239 := bstep (se 1 (by rfl) ⟨321929, by rfl⟩ : syracuseStep 429239 = 643859) B643859
theorem B1313977 : Blo 167798 1313977 := bstep (se 2 (by rfl) ⟨492741, by rfl⟩ : syracuseStep 1313977 = 985483) B985483
theorem B167847 : Blo 167798 167847 := bstep (se 1 (by rfl) ⟨125885, by rfl⟩ : syracuseStep 167847 = 251771) B251771
theorem B167871 : Blo 167798 167871 := bstep (se 1 (by rfl) ⟨125903, by rfl⟩ : syracuseStep 167871 = 251807) B251807
theorem B168027 : Blo 167798 168027 := bstep (se 1 (by rfl) ⟨126020, by rfl⟩ : syracuseStep 168027 = 252041) B252041
theorem B17174705 : Blo 167798 17174705 := bstep (se 2 (by rfl) ⟨6440514, by rfl⟩ : syracuseStep 17174705 = 12881029) B12881029
theorem B168127 : Blo 167798 168127 := bstep (se 1 (by rfl) ⟨126095, by rfl⟩ : syracuseStep 168127 = 252191) B252191
theorem B463067 : Blo 167798 463067 := bstep (se 1 (by rfl) ⟨347300, by rfl⟩ : syracuseStep 463067 = 694601) B694601
theorem B168495 : Blo 167798 168495 := bstep (se 1 (by rfl) ⟨126371, by rfl⟩ : syracuseStep 168495 = 252743) B252743
theorem B169071 : Blo 167798 169071 := bstep (se 1 (by rfl) ⟨126803, by rfl⟩ : syracuseStep 169071 = 253607) B253607
theorem B169151 : Blo 167798 169151 := bstep (se 1 (by rfl) ⟨126863, by rfl⟩ : syracuseStep 169151 = 253727) B253727
theorem B1545475 : Blo 167798 1545475 := bstep (se 1 (by rfl) ⟨1159106, by rfl⟩ : syracuseStep 1545475 = 2318213) B2318213
theorem B431527 : Blo 167798 431527 := bstep (se 1 (by rfl) ⟨323645, by rfl⟩ : syracuseStep 431527 = 647291) B647291
theorem B169439 : Blo 167798 169439 := bstep (se 1 (by rfl) ⟨127079, by rfl⟩ : syracuseStep 169439 = 254159) B254159
theorem B169471 : Blo 167798 169471 := bstep (se 1 (by rfl) ⟨127103, by rfl⟩ : syracuseStep 169471 = 254207) B254207
theorem B1382059 : Blo 167798 1382059 := bstep (se 1 (by rfl) ⟨1036544, by rfl⟩ : syracuseStep 1382059 = 2073089) B2073089
theorem B1939139 : Blo 167798 1939139 := bstep (se 1 (by rfl) ⟨1454354, by rfl⟩ : syracuseStep 1939139 = 2908709) B2908709
theorem B825149 : Blo 167798 825149 := bstep (se 3 (by rfl) ⟨154715, by rfl⟩ : syracuseStep 825149 = 309431) B309431
theorem B431963 : Blo 167798 431963 := bstep (se 1 (by rfl) ⟨323972, by rfl⟩ : syracuseStep 431963 = 647945) B647945
theorem B431993 : Blo 167798 431993 := bstep (se 2 (by rfl) ⟨161997, by rfl⟩ : syracuseStep 431993 = 323995) B323995
theorem B170015 : Blo 167798 170015 := bstep (se 1 (by rfl) ⟨127511, by rfl⟩ : syracuseStep 170015 = 255023) B255023
theorem B170095 : Blo 167798 170095 := bstep (se 1 (by rfl) ⟨127571, by rfl⟩ : syracuseStep 170095 = 255143) B255143
theorem B170343 : Blo 167798 170343 := bstep (se 1 (by rfl) ⟨127757, by rfl⟩ : syracuseStep 170343 = 255515) B255515
theorem B170599 : Blo 167798 170599 := bstep (se 1 (by rfl) ⟨127949, by rfl⟩ : syracuseStep 170599 = 255899) B255899
theorem B170623 : Blo 167798 170623 := bstep (se 1 (by rfl) ⟨127967, by rfl⟩ : syracuseStep 170623 = 255935) B255935
theorem B170747 : Blo 167798 170747 := bstep (se 1 (by rfl) ⟨128060, by rfl⟩ : syracuseStep 170747 = 256121) B256121
theorem B3120119 : Blo 167798 3120119 := bstep (se 1 (by rfl) ⟨2340089, by rfl⟩ : syracuseStep 3120119 = 4680179) B4680179
theorem B171003 : Blo 167798 171003 := bstep (se 1 (by rfl) ⟨128252, by rfl⟩ : syracuseStep 171003 = 256505) B256505
theorem B171039 : Blo 167798 171039 := bstep (se 1 (by rfl) ⟨128279, by rfl⟩ : syracuseStep 171039 = 256559) B256559
theorem B171327 : Blo 167798 171327 := bstep (se 1 (by rfl) ⟨128495, by rfl⟩ : syracuseStep 171327 = 256991) B256991
theorem B1645991 : Blo 167798 1645991 := bstep (se 1 (by rfl) ⟨1234493, by rfl⟩ : syracuseStep 1645991 = 2468987) B2468987
theorem B171623 : Blo 167798 171623 := bstep (se 1 (by rfl) ⟨128717, by rfl⟩ : syracuseStep 171623 = 257435) B257435
theorem B433775 : Blo 167798 433775 := bstep (se 1 (by rfl) ⟨325331, by rfl⟩ : syracuseStep 433775 = 650663) B650663
theorem B434231 : Blo 167798 434231 := bstep (se 1 (by rfl) ⟨325673, by rfl⟩ : syracuseStep 434231 = 651347) B651347
theorem B1942055 : Blo 167798 1942055 := bstep (se 1 (by rfl) ⟨1456541, by rfl⟩ : syracuseStep 1942055 = 2913083) B2913083
theorem B860867 : Blo 167798 860867 := bstep (se 1 (by rfl) ⟨645650, by rfl⟩ : syracuseStep 860867 = 1291301) B1291301
theorem B1385693 : Blo 167798 1385693 := bstep (se 3 (by rfl) ⟨259817, by rfl⟩ : syracuseStep 1385693 = 519635) B519635
theorem B2762045 : Blo 167798 2762045 := bstep (se 3 (by rfl) ⟨517883, by rfl⟩ : syracuseStep 2762045 = 1035767) B1035767
theorem B730937 : Blo 167798 730937 := bstep (se 2 (by rfl) ⟨274101, by rfl⟩ : syracuseStep 730937 = 548203) B548203
theorem B239431 : Blo 167798 239431 := bstep (se 1 (by rfl) ⟨179573, by rfl⟩ : syracuseStep 239431 = 359147) B359147
theorem B4139171 : Blo 167798 4139171 := bstep (se 1 (by rfl) ⟨3104378, by rfl⟩ : syracuseStep 4139171 = 6208757) B6208757
theorem B3713525 : Blo 167798 3713525 := bstep (se 5 (by rfl) ⟨174071, by rfl⟩ : syracuseStep 3713525 = 348143) B348143
theorem B1616435 : Blo 167798 1616435 := bstep (se 1 (by rfl) ⟨1212326, by rfl⟩ : syracuseStep 1616435 = 2424653) B2424653
theorem B1846205 : Blo 167798 1846205 := bstep (se 3 (by rfl) ⟨346163, by rfl⟩ : syracuseStep 1846205 = 692327) B692327
theorem B961915 : Blo 167798 961915 := bstep (se 1 (by rfl) ⟨721436, by rfl⟩ : syracuseStep 961915 = 1442873) B1442873
theorem B274025 : Blo 167798 274025 := bstep (se 2 (by rfl) ⟨102759, by rfl⟩ : syracuseStep 274025 = 205519) B205519
theorem B1454219 : Blo 167798 1454219 := bstep (se 1 (by rfl) ⟨1090664, by rfl⟩ : syracuseStep 1454219 = 2181329) B2181329
theorem B1093895 : Blo 167798 1093895 := bstep (se 1 (by rfl) ⟨820421, by rfl⟩ : syracuseStep 1093895 = 1640843) B1640843
theorem B569807 : Blo 167798 569807 := bstep (se 1 (by rfl) ⟨427355, by rfl⟩ : syracuseStep 569807 = 854711) B854711
theorem B15774695 : Blo 167798 15774695 := bstep (se 1 (by rfl) ⟨11831021, by rfl⟩ : syracuseStep 15774695 = 23662043) B23662043
theorem B570347 : Blo 167798 570347 := bstep (se 1 (by rfl) ⟨427760, by rfl⟩ : syracuseStep 570347 = 855521) B855521
theorem B538105 : Blo 167798 538105 := bstep (se 2 (by rfl) ⟨201789, by rfl⟩ : syracuseStep 538105 = 403579) B403579
theorem B2340485 : Blo 167798 2340485 := bstep (se 4 (by rfl) ⟨219420, by rfl⟩ : syracuseStep 2340485 = 438841) B438841
theorem B1391519 : Blo 167798 1391519 := bstep (se 1 (by rfl) ⟨1043639, by rfl⟩ : syracuseStep 1391519 = 2087279) B2087279
theorem B572399 : Blo 167798 572399 := bstep (se 1 (by rfl) ⟨429299, by rfl⟩ : syracuseStep 572399 = 858599) B858599
theorem B933289 : Blo 167798 933289 := bstep (se 2 (by rfl) ⟨349983, by rfl⟩ : syracuseStep 933289 = 699967) B699967
theorem B736897 : Blo 167798 736897 := bstep (se 2 (by rfl) ⟨276336, by rfl⟩ : syracuseStep 736897 = 552673) B552673
theorem B212635 : Blo 167798 212635 := bstep (se 1 (by rfl) ⟨159476, by rfl⟩ : syracuseStep 212635 = 318953) B318953
theorem B573263 : Blo 167798 573263 := bstep (se 1 (by rfl) ⟨429947, by rfl⟩ : syracuseStep 573263 = 859895) B859895
theorem B868481 : Blo 167798 868481 := bstep (se 2 (by rfl) ⟨325680, by rfl⟩ : syracuseStep 868481 = 651361) B651361
theorem B245929 : Blo 167798 245929 := bstep (se 2 (by rfl) ⟨92223, by rfl⟩ : syracuseStep 245929 = 184447) B184447
theorem B409769 : Blo 167798 409769 := bstep (se 2 (by rfl) ⟨153663, by rfl⟩ : syracuseStep 409769 = 307327) B307327
theorem B130892591 : Blo 167798 130892591 := bstep (se 1 (by rfl) ⟨98169443, by rfl⟩ : syracuseStep 130892591 = 196338887) B196338887
theorem B410807 : Blo 167798 410807 := bstep (se 1 (by rfl) ⟨308105, by rfl⟩ : syracuseStep 410807 = 616211) B616211
theorem B607559 : Blo 167798 607559 := bstep (se 1 (by rfl) ⟨455669, by rfl⟩ : syracuseStep 607559 = 911339) B911339
theorem B410951 : Blo 167798 410951 := bstep (se 1 (by rfl) ⟨308213, by rfl⟩ : syracuseStep 410951 = 616427) B616427
theorem B378215 : Blo 167798 378215 := bstep (se 1 (by rfl) ⟨283661, by rfl⟩ : syracuseStep 378215 = 567323) B567323
theorem B378323 : Blo 167798 378323 := bstep (se 1 (by rfl) ⟨283742, by rfl⟩ : syracuseStep 378323 = 567485) B567485
theorem B4376051 : Blo 167798 4376051 := bstep (se 1 (by rfl) ⟨3282038, by rfl⟩ : syracuseStep 4376051 = 6564077) B6564077
theorem B968273 : Blo 167798 968273 := bstep (se 2 (by rfl) ⟨363102, by rfl⟩ : syracuseStep 968273 = 726205) B726205
theorem B378593 : Blo 167798 378593 := bstep (se 2 (by rfl) ⟨141972, by rfl⟩ : syracuseStep 378593 = 283945) B283945
theorem B968705 : Blo 167798 968705 := bstep (se 2 (by rfl) ⟨363264, by rfl⟩ : syracuseStep 968705 = 726529) B726529
theorem B2869343 : Blo 167798 2869343 := bstep (se 1 (by rfl) ⟨2152007, by rfl⟩ : syracuseStep 2869343 = 4304015) B4304015
theorem B1460369 : Blo 167798 1460369 := bstep (se 2 (by rfl) ⟨547638, by rfl⟩ : syracuseStep 1460369 = 1095277) B1095277
theorem B379385 : Blo 167798 379385 := bstep (se 2 (by rfl) ⟨142269, by rfl⟩ : syracuseStep 379385 = 284539) B284539
theorem B3263003 : Blo 167798 3263003 := bstep (se 1 (by rfl) ⟨2447252, by rfl⟩ : syracuseStep 3263003 = 4894505) B4894505
theorem B379475 : Blo 167798 379475 := bstep (se 1 (by rfl) ⟨284606, by rfl⟩ : syracuseStep 379475 = 569213) B569213
theorem B641627 : Blo 167798 641627 := bstep (se 1 (by rfl) ⟨481220, by rfl⟩ : syracuseStep 641627 = 962441) B962441
theorem B379655 : Blo 167798 379655 := bstep (se 1 (by rfl) ⟨284741, by rfl⟩ : syracuseStep 379655 = 569483) B569483
theorem B379745 : Blo 167798 379745 := bstep (se 2 (by rfl) ⟨142404, by rfl⟩ : syracuseStep 379745 = 284809) B284809
theorem B1592531 : Blo 167798 1592531 := bstep (se 1 (by rfl) ⟨1194398, by rfl⟩ : syracuseStep 1592531 = 2388797) B2388797
theorem B347689 : Blo 167798 347689 := bstep (se 2 (by rfl) ⟨130383, by rfl⟩ : syracuseStep 347689 = 260767) B260767
theorem B380663 : Blo 167798 380663 := bstep (se 1 (by rfl) ⟨285497, by rfl⟩ : syracuseStep 380663 = 570995) B570995
theorem B380681 : Blo 167798 380681 := bstep (se 2 (by rfl) ⟨142755, by rfl⟩ : syracuseStep 380681 = 285511) B285511
theorem B380735 : Blo 167798 380735 := bstep (se 1 (by rfl) ⟨285551, by rfl⟩ : syracuseStep 380735 = 571103) B571103
theorem B380843 : Blo 167798 380843 := bstep (se 1 (by rfl) ⟨285632, by rfl⟩ : syracuseStep 380843 = 571265) B571265
theorem B1953719 : Blo 167798 1953719 := bstep (se 1 (by rfl) ⟨1465289, by rfl⟩ : syracuseStep 1953719 = 2930579) B2930579
theorem B643099 : Blo 167798 643099 := bstep (se 1 (by rfl) ⟨482324, by rfl⟩ : syracuseStep 643099 = 964649) B964649
theorem B2904335 : Blo 167798 2904335 := bstep (se 1 (by rfl) ⟨2178251, by rfl⟩ : syracuseStep 2904335 = 4356503) B4356503
theorem B381203 : Blo 167798 381203 := bstep (se 1 (by rfl) ⟨285902, by rfl⟩ : syracuseStep 381203 = 571805) B571805
theorem B381383 : Blo 167798 381383 := bstep (se 1 (by rfl) ⟨286037, by rfl⟩ : syracuseStep 381383 = 572075) B572075
theorem B1462967 : Blo 167798 1462967 := bstep (se 1 (by rfl) ⟨1097225, by rfl⟩ : syracuseStep 1462967 = 2194451) B2194451
theorem B381671 : Blo 167798 381671 := bstep (se 1 (by rfl) ⟨286253, by rfl⟩ : syracuseStep 381671 = 572507) B572507
theorem B381743 : Blo 167798 381743 := bstep (se 1 (by rfl) ⟨286307, by rfl⟩ : syracuseStep 381743 = 572615) B572615
theorem B381833 : Blo 167798 381833 := bstep (se 2 (by rfl) ⟨143187, by rfl⟩ : syracuseStep 381833 = 286375) B286375
theorem B283871 : Blo 167798 283871 := bstep (se 1 (by rfl) ⟨212903, by rfl⟩ : syracuseStep 283871 = 425807) B425807
theorem B546383 : Blo 167798 546383 := bstep (se 1 (by rfl) ⟨409787, by rfl⟩ : syracuseStep 546383 = 819575) B819575
theorem B284303 : Blo 167798 284303 := bstep (se 1 (by rfl) ⟨213227, by rfl⟩ : syracuseStep 284303 = 426455) B426455
theorem B579311 : Blo 167798 579311 := bstep (se 1 (by rfl) ⟨434483, by rfl⟩ : syracuseStep 579311 = 868967) B868967
theorem B481277 : Blo 167798 481277 := bstep (se 3 (by rfl) ⟨90239, by rfl⟩ : syracuseStep 481277 = 180479) B180479
theorem B251945 : Blo 167798 251945 := bstep (se 2 (by rfl) ⟨94479, by rfl⟩ : syracuseStep 251945 = 188959) B188959
theorem B1038395 : Blo 167798 1038395 := bstep (se 1 (by rfl) ⟨778796, by rfl⟩ : syracuseStep 1038395 = 1557593) B1557593
theorem B251975 : Blo 167798 251975 := bstep (se 1 (by rfl) ⟨188981, by rfl⟩ : syracuseStep 251975 = 377963) B377963
theorem B546955 : Blo 167798 546955 := bstep (se 1 (by rfl) ⟨410216, by rfl⟩ : syracuseStep 546955 = 820433) B820433
theorem B1038689 : Blo 167798 1038689 := bstep (se 2 (by rfl) ⟨389508, by rfl⟩ : syracuseStep 1038689 = 779017) B779017
theorem B252287 : Blo 167798 252287 := bstep (se 1 (by rfl) ⟨189215, by rfl⟩ : syracuseStep 252287 = 378431) B378431
theorem B252359 : Blo 167798 252359 := bstep (se 1 (by rfl) ⟨189269, by rfl⟩ : syracuseStep 252359 = 378539) B378539
theorem B252575 : Blo 167798 252575 := bstep (se 1 (by rfl) ⟨189431, by rfl⟩ : syracuseStep 252575 = 378863) B378863
theorem B252719 : Blo 167798 252719 := bstep (se 1 (by rfl) ⟨189539, by rfl⟩ : syracuseStep 252719 = 379079) B379079
theorem B252809 : Blo 167798 252809 := bstep (se 2 (by rfl) ⟨94803, by rfl⟩ : syracuseStep 252809 = 189607) B189607
theorem B252839 : Blo 167798 252839 := bstep (se 1 (by rfl) ⟨189629, by rfl⟩ : syracuseStep 252839 = 379259) B379259
theorem B1301507 : Blo 167798 1301507 := bstep (se 1 (by rfl) ⟨976130, by rfl⟩ : syracuseStep 1301507 = 1952261) B1952261
theorem B253019 : Blo 167798 253019 := bstep (se 1 (by rfl) ⟨189764, by rfl⟩ : syracuseStep 253019 = 379529) B379529
theorem B384107 : Blo 167798 384107 := bstep (se 1 (by rfl) ⟨288080, by rfl⟩ : syracuseStep 384107 = 576161) B576161
theorem B2776193 : Blo 167798 2776193 := bstep (se 2 (by rfl) ⟨1041072, by rfl⟩ : syracuseStep 2776193 = 2082145) B2082145
theorem B810233 : Blo 167798 810233 := bstep (se 2 (by rfl) ⟨303837, by rfl⟩ : syracuseStep 810233 = 607675) B607675
theorem B253211 : Blo 167798 253211 := bstep (se 1 (by rfl) ⟨189908, by rfl⟩ : syracuseStep 253211 = 379817) B379817
theorem B482735 : Blo 167798 482735 := bstep (se 1 (by rfl) ⟨362051, by rfl⟩ : syracuseStep 482735 = 724103) B724103
theorem B1301993 : Blo 167798 1301993 := bstep (se 2 (by rfl) ⟨488247, by rfl⟩ : syracuseStep 1301993 = 976495) B976495
theorem B4415143 : Blo 167798 4415143 := bstep (se 1 (by rfl) ⟨3311357, by rfl⟩ : syracuseStep 4415143 = 6622715) B6622715
theorem B253679 : Blo 167798 253679 := bstep (se 1 (by rfl) ⟨190259, by rfl⟩ : syracuseStep 253679 = 380519) B380519
theorem B253865 : Blo 167798 253865 := bstep (se 2 (by rfl) ⟨95199, by rfl⟩ : syracuseStep 253865 = 190399) B190399
theorem B28336139 : Blo 167798 28336139 := bstep (se 1 (by rfl) ⟨21252104, by rfl⟩ : syracuseStep 28336139 = 42504209) B42504209
theorem B254015 : Blo 167798 254015 := bstep (se 1 (by rfl) ⟨190511, by rfl⟩ : syracuseStep 254015 = 381023) B381023
theorem B385127 : Blo 167798 385127 := bstep (se 1 (by rfl) ⟨288845, by rfl⟩ : syracuseStep 385127 = 577691) B577691
theorem B254249 : Blo 167798 254249 := bstep (se 2 (by rfl) ⟨95343, by rfl⟩ : syracuseStep 254249 = 190687) B190687
theorem B254519 : Blo 167798 254519 := bstep (se 1 (by rfl) ⟨190889, by rfl⟩ : syracuseStep 254519 = 381779) B381779
theorem B5563181 : Blo 167798 5563181 := bstep (se 3 (by rfl) ⟨1043096, by rfl⟩ : syracuseStep 5563181 = 2086193) B2086193
theorem B484193 : Blo 167798 484193 := bstep (se 2 (by rfl) ⟨181572, by rfl⟩ : syracuseStep 484193 = 363145) B363145
theorem B254879 : Blo 167798 254879 := bstep (se 1 (by rfl) ⟨191159, by rfl⟩ : syracuseStep 254879 = 382319) B382319
theorem B975983 : Blo 167798 975983 := bstep (se 1 (by rfl) ⟨731987, by rfl⟩ : syracuseStep 975983 = 1463975) B1463975
theorem B255167 : Blo 167798 255167 := bstep (se 1 (by rfl) ⟨191375, by rfl⟩ : syracuseStep 255167 = 382751) B382751
theorem B386279 : Blo 167798 386279 := bstep (se 1 (by rfl) ⟨289709, by rfl⟩ : syracuseStep 386279 = 579419) B579419
theorem B255311 : Blo 167798 255311 := bstep (se 1 (by rfl) ⟨191483, by rfl⟩ : syracuseStep 255311 = 382967) B382967
theorem B255401 : Blo 167798 255401 := bstep (se 2 (by rfl) ⟨95775, by rfl⟩ : syracuseStep 255401 = 191551) B191551
theorem B321079 : Blo 167798 321079 := bstep (se 1 (by rfl) ⟨240809, by rfl⟩ : syracuseStep 321079 = 481619) B481619
theorem B255551 : Blo 167798 255551 := bstep (se 1 (by rfl) ⟨191663, by rfl⟩ : syracuseStep 255551 = 383327) B383327
theorem B288319 : Blo 167798 288319 := bstep (se 1 (by rfl) ⟨216239, by rfl⟩ : syracuseStep 288319 = 432479) B432479
theorem B255911 : Blo 167798 255911 := bstep (se 1 (by rfl) ⟨191933, by rfl⟩ : syracuseStep 255911 = 383867) B383867
theorem B256031 : Blo 167798 256031 := bstep (se 1 (by rfl) ⟨192023, by rfl⟩ : syracuseStep 256031 = 384047) B384047
theorem B485423 : Blo 167798 485423 := bstep (se 1 (by rfl) ⟨364067, by rfl⟩ : syracuseStep 485423 = 728135) B728135
theorem B289055 : Blo 167798 289055 := bstep (se 1 (by rfl) ⟨216791, by rfl⟩ : syracuseStep 289055 = 433583) B433583
theorem B256487 : Blo 167798 256487 := bstep (se 1 (by rfl) ⟨192365, by rfl⟩ : syracuseStep 256487 = 384731) B384731
theorem B256667 : Blo 167798 256667 := bstep (se 1 (by rfl) ⟨192500, by rfl⟩ : syracuseStep 256667 = 385001) B385001
theorem B649889 : Blo 167798 649889 := bstep (se 2 (by rfl) ⟨243708, by rfl⟩ : syracuseStep 649889 = 487417) B487417
theorem B256889 : Blo 167798 256889 := bstep (se 2 (by rfl) ⟨96333, by rfl⟩ : syracuseStep 256889 = 192667) B192667
theorem B650273 : Blo 167798 650273 := bstep (se 2 (by rfl) ⟨243852, by rfl⟩ : syracuseStep 650273 = 487705) B487705
theorem B257135 : Blo 167798 257135 := bstep (se 1 (by rfl) ⟨192851, by rfl⟩ : syracuseStep 257135 = 385703) B385703
theorem B322697 : Blo 167798 322697 := bstep (se 2 (by rfl) ⟨121011, by rfl⟩ : syracuseStep 322697 = 242023) B242023
theorem B191695 : Blo 167798 191695 := bstep (se 1 (by rfl) ⟨143771, by rfl⟩ : syracuseStep 191695 = 287543) B287543
theorem B257231 : Blo 167798 257231 := bstep (se 1 (by rfl) ⟨192923, by rfl⟩ : syracuseStep 257231 = 385847) B385847
theorem B519443 : Blo 167798 519443 := bstep (se 1 (by rfl) ⟨389582, by rfl⟩ : syracuseStep 519443 = 779165) B779165
theorem B257351 : Blo 167798 257351 := bstep (se 1 (by rfl) ⟨193013, by rfl⟩ : syracuseStep 257351 = 386027) B386027
theorem B257639 : Blo 167798 257639 := bstep (se 1 (by rfl) ⟨193229, by rfl⟩ : syracuseStep 257639 = 386459) B386459
theorem B454589 : Blo 167798 454589 := bstep (se 3 (by rfl) ⟨85235, by rfl⟩ : syracuseStep 454589 = 170471) B170471
theorem B192847 : Blo 167798 192847 := bstep (se 1 (by rfl) ⟨144635, by rfl⟩ : syracuseStep 192847 = 289271) B289271
theorem B651833 : Blo 167798 651833 := bstep (se 2 (by rfl) ⟨244437, by rfl⟩ : syracuseStep 651833 = 488875) B488875
theorem B193243 : Blo 167798 193243 := bstep (se 1 (by rfl) ⟨144932, by rfl⟩ : syracuseStep 193243 = 289865) B289865
theorem B5468957 : Blo 167798 5468957 := bstep (se 3 (by rfl) ⟨1025429, by rfl⟩ : syracuseStep 5468957 = 2050859) B2050859
theorem B390311 : Blo 167798 390311 := bstep (se 1 (by rfl) ⟨292733, by rfl⟩ : syracuseStep 390311 = 585467) B585467
theorem B1209815 : Blo 167798 1209815 := bstep (se 1 (by rfl) ⟨907361, by rfl⟩ : syracuseStep 1209815 = 1814723) B1814723
theorem B1309729 : Blo 167798 1309729 := bstep (se 2 (by rfl) ⟨491148, by rfl⟩ : syracuseStep 1309729 = 982297) B982297
theorem B425371 : Blo 167798 425371 := bstep (se 1 (by rfl) ⟨319028, by rfl⟩ : syracuseStep 425371 = 638057) B638057
theorem B1080823 : Blo 167798 1080823 := bstep (se 1 (by rfl) ⟨810617, by rfl⟩ : syracuseStep 1080823 = 1621235) B1621235
theorem B3309167 : Blo 167798 3309167 := bstep (se 1 (by rfl) ⟨2481875, by rfl⟩ : syracuseStep 3309167 = 4963751) B4963751
theorem B327905 : Blo 167798 327905 := bstep (se 2 (by rfl) ⟨122964, by rfl⟩ : syracuseStep 327905 = 245929) B245929
theorem B3670265 : Blo 167798 3670265 := bstep (se 2 (by rfl) ⟨1376349, by rfl⟩ : syracuseStep 3670265 = 2752699) B2752699
theorem B2917093 : Blo 167798 2917093 := bstep (se 4 (by rfl) ⟨273477, by rfl⟩ : syracuseStep 2917093 = 546955) B546955
theorem B2917367 : Blo 167798 2917367 := bstep (se 1 (by rfl) ⟨2188025, by rfl⟩ : syracuseStep 2917367 = 4376051) B4376051
theorem B4097141 : Blo 167798 4097141 := bstep (se 5 (by rfl) ⟨192053, by rfl⟩ : syracuseStep 4097141 = 384107) B384107
theorem B427751 : Blo 167798 427751 := bstep (se 1 (by rfl) ⟨320813, by rfl⟩ : syracuseStep 427751 = 641627) B641627
theorem B428105 : Blo 167798 428105 := bstep (se 2 (by rfl) ⟨160539, by rfl⟩ : syracuseStep 428105 = 321079) B321079
theorem B349046909 : Blo 167798 349046909 := bstep (se 3 (by rfl) ⟨65446295, by rfl⟩ : syracuseStep 349046909 = 130892591) B130892591
theorem B1936223 : Blo 167798 1936223 := bstep (se 1 (by rfl) ⟨1452167, by rfl⟩ : syracuseStep 1936223 = 2904335) B2904335
theorem B167963 : Blo 167798 167963 := bstep (se 1 (by rfl) ⟨125972, by rfl⟩ : syracuseStep 167963 = 251945) B251945
theorem B692263 : Blo 167798 692263 := bstep (se 1 (by rfl) ⟨519197, by rfl⟩ : syracuseStep 692263 = 1038395) B1038395
theorem B167983 : Blo 167798 167983 := bstep (se 1 (by rfl) ⟨125987, by rfl⟩ : syracuseStep 167983 = 251975) B251975
theorem B692459 : Blo 167798 692459 := bstep (se 1 (by rfl) ⟨519344, by rfl⟩ : syracuseStep 692459 = 1038689) B1038689
theorem B168191 : Blo 167798 168191 := bstep (se 1 (by rfl) ⟨126143, by rfl⟩ : syracuseStep 168191 = 252287) B252287
theorem B168239 : Blo 167798 168239 := bstep (se 1 (by rfl) ⟨126179, by rfl⟩ : syracuseStep 168239 = 252359) B252359
theorem B168383 : Blo 167798 168383 := bstep (se 1 (by rfl) ⟨126287, by rfl⟩ : syracuseStep 168383 = 252575) B252575
theorem B1282553 : Blo 167798 1282553 := bstep (se 2 (by rfl) ⟨480957, by rfl⟩ : syracuseStep 1282553 = 961915) B961915
theorem B168479 : Blo 167798 168479 := bstep (se 1 (by rfl) ⟨126359, by rfl⟩ : syracuseStep 168479 = 252719) B252719
theorem B168539 : Blo 167798 168539 := bstep (se 1 (by rfl) ⟨126404, by rfl⟩ : syracuseStep 168539 = 252809) B252809
theorem B168559 : Blo 167798 168559 := bstep (se 1 (by rfl) ⟨126419, by rfl⟩ : syracuseStep 168559 = 252839) B252839
theorem B463585 : Blo 167798 463585 := bstep (se 2 (by rfl) ⟨173844, by rfl⟩ : syracuseStep 463585 = 347689) B347689
theorem B168679 : Blo 167798 168679 := bstep (se 1 (by rfl) ⟨126509, by rfl⟩ : syracuseStep 168679 = 253019) B253019
theorem B168807 : Blo 167798 168807 := bstep (se 1 (by rfl) ⟨126605, by rfl⟩ : syracuseStep 168807 = 253211) B253211
theorem B169119 : Blo 167798 169119 := bstep (se 1 (by rfl) ⟨126839, by rfl⟩ : syracuseStep 169119 = 253679) B253679
theorem B169243 : Blo 167798 169243 := bstep (se 1 (by rfl) ⟨126932, by rfl⟩ : syracuseStep 169243 = 253865) B253865
theorem B857465 : Blo 167798 857465 := bstep (se 2 (by rfl) ⟨321549, by rfl⟩ : syracuseStep 857465 = 643099) B643099
theorem B169343 : Blo 167798 169343 := bstep (se 1 (by rfl) ⟨127007, by rfl⟩ : syracuseStep 169343 = 254015) B254015
theorem B169499 : Blo 167798 169499 := bstep (se 1 (by rfl) ⟨127124, by rfl⟩ : syracuseStep 169499 = 254249) B254249
theorem B169679 : Blo 167798 169679 := bstep (se 1 (by rfl) ⟨127259, by rfl⟩ : syracuseStep 169679 = 254519) B254519
theorem B3708787 : Blo 167798 3708787 := bstep (se 1 (by rfl) ⟨2781590, by rfl⟩ : syracuseStep 3708787 = 5563181) B5563181
theorem B169919 : Blo 167798 169919 := bstep (se 1 (by rfl) ⟨127439, by rfl⟩ : syracuseStep 169919 = 254879) B254879
theorem B170111 : Blo 167798 170111 := bstep (se 1 (by rfl) ⟨127583, by rfl⟩ : syracuseStep 170111 = 255167) B255167
theorem B923795 : Blo 167798 923795 := bstep (se 1 (by rfl) ⟨692846, by rfl⟩ : syracuseStep 923795 = 1385693) B1385693
theorem B1841363 : Blo 167798 1841363 := bstep (se 1 (by rfl) ⟨1381022, by rfl⟩ : syracuseStep 1841363 = 2762045) B2762045
theorem B170207 : Blo 167798 170207 := bstep (se 1 (by rfl) ⟨127655, by rfl⟩ : syracuseStep 170207 = 255311) B255311
theorem B170267 : Blo 167798 170267 := bstep (se 1 (by rfl) ⟨127700, by rfl⟩ : syracuseStep 170267 = 255401) B255401
theorem B170367 : Blo 167798 170367 := bstep (se 1 (by rfl) ⟨127775, by rfl⟩ : syracuseStep 170367 = 255551) B255551
theorem B170607 : Blo 167798 170607 := bstep (se 1 (by rfl) ⟨127955, by rfl⟩ : syracuseStep 170607 = 255911) B255911
theorem B170687 : Blo 167798 170687 := bstep (se 1 (by rfl) ⟨128015, by rfl⟩ : syracuseStep 170687 = 256031) B256031
theorem B2759447 : Blo 167798 2759447 := bstep (se 1 (by rfl) ⟨2069585, by rfl⟩ : syracuseStep 2759447 = 4139171) B4139171
theorem B170991 : Blo 167798 170991 := bstep (se 1 (by rfl) ⟨128243, by rfl⟩ : syracuseStep 170991 = 256487) B256487
theorem B171111 : Blo 167798 171111 := bstep (se 1 (by rfl) ⟨128333, by rfl⟩ : syracuseStep 171111 = 256667) B256667
theorem B433259 : Blo 167798 433259 := bstep (se 1 (by rfl) ⟨324944, by rfl⟩ : syracuseStep 433259 = 649889) B649889
theorem B171259 : Blo 167798 171259 := bstep (se 1 (by rfl) ⟨128444, by rfl⟩ : syracuseStep 171259 = 256889) B256889
theorem B171423 : Blo 167798 171423 := bstep (se 1 (by rfl) ⟨128567, by rfl⟩ : syracuseStep 171423 = 257135) B257135
theorem B171487 : Blo 167798 171487 := bstep (se 1 (by rfl) ⟨128615, by rfl⟩ : syracuseStep 171487 = 257231) B257231
theorem B171567 : Blo 167798 171567 := bstep (se 1 (by rfl) ⟨128675, by rfl⟩ : syracuseStep 171567 = 257351) B257351
theorem B1842745 : Blo 167798 1842745 := bstep (se 2 (by rfl) ⟨691029, by rfl⟩ : syracuseStep 1842745 = 1382059) B1382059
theorem B171759 : Blo 167798 171759 := bstep (se 1 (by rfl) ⟨128819, by rfl⟩ : syracuseStep 171759 = 257639) B257639
theorem B303059 : Blo 167798 303059 := bstep (se 1 (by rfl) ⟨227294, by rfl⟩ : syracuseStep 303059 = 454589) B454589
theorem B729263 : Blo 167798 729263 := bstep (se 1 (by rfl) ⟨546947, by rfl⟩ : syracuseStep 729263 = 1093895) B1093895
theorem B434555 : Blo 167798 434555 := bstep (se 1 (by rfl) ⟨325916, by rfl⟩ : syracuseStep 434555 = 651833) B651833
theorem B3645971 : Blo 167798 3645971 := bstep (se 1 (by rfl) ⟨2734478, by rfl⟩ : syracuseStep 3645971 = 5468957) B5468957
theorem B1746305 : Blo 167798 1746305 := bstep (se 2 (by rfl) ⟨654864, by rfl⟩ : syracuseStep 1746305 = 1309729) B1309729
theorem B567161 : Blo 167798 567161 := bstep (se 2 (by rfl) ⟨212685, by rfl⟩ : syracuseStep 567161 = 425371) B425371
theorem B927679 : Blo 167798 927679 := bstep (se 1 (by rfl) ⟨695759, by rfl⟩ : syracuseStep 927679 = 1391519) B1391519
theorem B2206111 : Blo 167798 2206111 := bstep (se 1 (by rfl) ⟨1654583, by rfl⟩ : syracuseStep 2206111 = 3309167) B3309167
theorem B273179 : Blo 167798 273179 := bstep (se 1 (by rfl) ⟨204884, by rfl⟩ : syracuseStep 273179 = 409769) B409769
theorem B568187 : Blo 167798 568187 := bstep (se 1 (by rfl) ⟨426140, by rfl⟩ : syracuseStep 568187 = 852281) B852281
theorem B273871 : Blo 167798 273871 := bstep (se 1 (by rfl) ⟨205403, by rfl⟩ : syracuseStep 273871 = 410807) B410807
theorem B1224173 : Blo 167798 1224173 := bstep (se 3 (by rfl) ⟨229532, by rfl⟩ : syracuseStep 1224173 = 459065) B459065
theorem B569159 : Blo 167798 569159 := bstep (se 1 (by rfl) ⟨426869, by rfl⟩ : syracuseStep 569159 = 853739) B853739
theorem B1912895 : Blo 167798 1912895 := bstep (se 1 (by rfl) ⟨1434671, by rfl⟩ : syracuseStep 1912895 = 2869343) B2869343
theorem B1028371 : Blo 167798 1028371 := bstep (se 1 (by rfl) ⟨771278, by rfl⟩ : syracuseStep 1028371 = 1542557) B1542557
theorem B962873 : Blo 167798 962873 := bstep (se 2 (by rfl) ⟨361077, by rfl⟩ : syracuseStep 962873 = 722155) B722155
theorem B2175335 : Blo 167798 2175335 := bstep (se 1 (by rfl) ⟨1631501, by rfl⟩ : syracuseStep 2175335 = 3263003) B3263003
theorem B1061687 : Blo 167798 1061687 := bstep (se 1 (by rfl) ⟨796265, by rfl⟩ : syracuseStep 1061687 = 1592531) B1592531
theorem B439265 : Blo 167798 439265 := bstep (se 2 (by rfl) ⟨164724, by rfl⟩ : syracuseStep 439265 = 329449) B329449
theorem B308711 : Blo 167798 308711 := bstep (se 1 (by rfl) ⟨231533, by rfl⟩ : syracuseStep 308711 = 463067) B463067
theorem B2602621 : Blo 167798 2602621 := bstep (se 3 (by rfl) ⟨487991, by rfl⟩ : syracuseStep 2602621 = 975983) B975983
theorem B1095869 : Blo 167798 1095869 := bstep (se 3 (by rfl) ⟨205475, by rfl⟩ : syracuseStep 1095869 = 410951) B410951
theorem B1620157 : Blo 167798 1620157 := bstep (se 3 (by rfl) ⟨303779, by rfl⟩ : syracuseStep 1620157 = 607559) B607559
theorem B1292759 : Blo 167798 1292759 := bstep (se 1 (by rfl) ⟨969569, by rfl⟩ : syracuseStep 1292759 = 1939139) B1939139
theorem B1457021 : Blo 167798 1457021 := bstep (se 3 (by rfl) ⟨273191, by rfl⟩ : syracuseStep 1457021 = 546383) B546383
theorem B1751969 : Blo 167798 1751969 := bstep (se 2 (by rfl) ⟨656988, by rfl⟩ : syracuseStep 1751969 = 1313977) B1313977
theorem B2080079 : Blo 167798 2080079 := bstep (se 1 (by rfl) ⟨1560059, by rfl⟩ : syracuseStep 2080079 = 3120119) B3120119
theorem B867671 : Blo 167798 867671 := bstep (se 1 (by rfl) ⟨650753, by rfl⟩ : syracuseStep 867671 = 1301507) B1301507
theorem B1850795 : Blo 167798 1850795 := bstep (se 1 (by rfl) ⟨1388096, by rfl⟩ : syracuseStep 1850795 = 2776193) B2776193
theorem B540155 : Blo 167798 540155 := bstep (se 1 (by rfl) ⟨405116, by rfl⟩ : syracuseStep 540155 = 810233) B810233
theorem B1097327 : Blo 167798 1097327 := bstep (se 1 (by rfl) ⟨822995, by rfl⟩ : syracuseStep 1097327 = 1645991) B1645991
theorem B867995 : Blo 167798 867995 := bstep (se 1 (by rfl) ⟨650996, by rfl⟩ : syracuseStep 867995 = 1301993) B1301993
theorem B18890759 : Blo 167798 18890759 := bstep (se 1 (by rfl) ⟨14168069, by rfl⟩ : syracuseStep 18890759 = 28336139) B28336139
theorem B1294703 : Blo 167798 1294703 := bstep (se 1 (by rfl) ⟨971027, by rfl⟩ : syracuseStep 1294703 = 1942055) B1942055
theorem B573911 : Blo 167798 573911 := bstep (se 1 (by rfl) ⟨430433, by rfl⟩ : syracuseStep 573911 = 860867) B860867
theorem B2475683 : Blo 167798 2475683 := bstep (se 1 (by rfl) ⟨1856762, by rfl⟩ : syracuseStep 2475683 = 3713525) B3713525
theorem B575369 : Blo 167798 575369 := bstep (se 2 (by rfl) ⟨215763, by rfl⟩ : syracuseStep 575369 = 431527) B431527
theorem B1230803 : Blo 167798 1230803 := bstep (se 1 (by rfl) ⟨923102, by rfl⟩ : syracuseStep 1230803 = 1846205) B1846205
theorem B215131 : Blo 167798 215131 := bstep (se 1 (by rfl) ⟨161348, by rfl⟩ : syracuseStep 215131 = 322697) B322697
theorem B346295 : Blo 167798 346295 := bstep (se 1 (by rfl) ⟨259721, by rfl⟩ : syracuseStep 346295 = 519443) B519443
theorem B182683 : Blo 167798 182683 := bstep (se 1 (by rfl) ⟨137012, by rfl⟩ : syracuseStep 182683 = 274025) B274025
theorem B969479 : Blo 167798 969479 := bstep (se 1 (by rfl) ⟨727109, by rfl⟩ : syracuseStep 969479 = 1454219) B1454219
theorem B379871 : Blo 167798 379871 := bstep (se 1 (by rfl) ⟨284903, by rfl⟩ : syracuseStep 379871 = 569807) B569807
theorem B380231 : Blo 167798 380231 := bstep (se 1 (by rfl) ⟨285173, by rfl⟩ : syracuseStep 380231 = 570347) B570347
theorem B806543 : Blo 167798 806543 := bstep (se 1 (by rfl) ⟨604907, by rfl⟩ : syracuseStep 806543 = 1209815) B1209815
theorem B1560323 : Blo 167798 1560323 := bstep (se 1 (by rfl) ⟨1170242, by rfl⟩ : syracuseStep 1560323 = 2340485) B2340485
theorem B381599 : Blo 167798 381599 := bstep (se 1 (by rfl) ⟨286199, by rfl⟩ : syracuseStep 381599 = 572399) B572399
theorem B283513 : Blo 167798 283513 := bstep (se 2 (by rfl) ⟨106317, by rfl⟩ : syracuseStep 283513 = 212635) B212635
theorem B5886857 : Blo 167798 5886857 := bstep (se 2 (by rfl) ⟨2207571, by rfl⟩ : syracuseStep 5886857 = 4415143) B4415143
theorem B382175 : Blo 167798 382175 := bstep (se 1 (by rfl) ⟨286631, by rfl⟩ : syracuseStep 382175 = 573263) B573263
theorem B578987 : Blo 167798 578987 := bstep (se 1 (by rfl) ⟨434240, by rfl⟩ : syracuseStep 578987 = 868481) B868481
theorem B284215 : Blo 167798 284215 := bstep (se 1 (by rfl) ⟨213161, by rfl⟩ : syracuseStep 284215 = 426323) B426323
theorem B1463923 : Blo 167798 1463923 := bstep (se 1 (by rfl) ⟨1097942, by rfl⟩ : syracuseStep 1463923 = 2195885) B2195885
theorem B481049 : Blo 167798 481049 := bstep (se 2 (by rfl) ⟨180393, by rfl⟩ : syracuseStep 481049 = 360787) B360787
theorem B252143 : Blo 167798 252143 := bstep (se 1 (by rfl) ⟨189107, by rfl⟩ : syracuseStep 252143 = 378215) B378215
theorem B252215 : Blo 167798 252215 := bstep (se 1 (by rfl) ⟨189161, by rfl⟩ : syracuseStep 252215 = 378323) B378323
theorem B645515 : Blo 167798 645515 := bstep (se 1 (by rfl) ⟨484136, by rfl⟩ : syracuseStep 645515 = 968273) B968273
theorem B252395 : Blo 167798 252395 := bstep (se 1 (by rfl) ⟨189296, by rfl⟩ : syracuseStep 252395 = 378593) B378593
theorem B645803 : Blo 167798 645803 := bstep (se 1 (by rfl) ⟨484352, by rfl⟩ : syracuseStep 645803 = 968705) B968705
theorem B973579 : Blo 167798 973579 := bstep (se 1 (by rfl) ⟨730184, by rfl⟩ : syracuseStep 973579 = 1460369) B1460369
theorem B252923 : Blo 167798 252923 := bstep (se 1 (by rfl) ⟨189692, by rfl⟩ : syracuseStep 252923 = 379385) B379385
theorem B285727 : Blo 167798 285727 := bstep (se 1 (by rfl) ⟨214295, by rfl⟩ : syracuseStep 285727 = 428591) B428591
theorem B252983 : Blo 167798 252983 := bstep (se 1 (by rfl) ⟨189737, by rfl⟩ : syracuseStep 252983 = 379475) B379475
theorem B253103 : Blo 167798 253103 := bstep (se 1 (by rfl) ⟨189827, by rfl⟩ : syracuseStep 253103 = 379655) B379655
theorem B183196853 : Blo 167798 183196853 := bstep (se 5 (by rfl) ⟨8587352, by rfl⟩ : syracuseStep 183196853 = 17174705) B17174705
theorem B253163 : Blo 167798 253163 := bstep (se 1 (by rfl) ⟨189872, by rfl⟩ : syracuseStep 253163 = 379745) B379745
theorem B384425 : Blo 167798 384425 := bstep (se 2 (by rfl) ⟨144159, by rfl⟩ : syracuseStep 384425 = 288319) B288319
theorem B286159 : Blo 167798 286159 := bstep (se 1 (by rfl) ⟨214619, by rfl⟩ : syracuseStep 286159 = 429239) B429239
theorem B319241 : Blo 167798 319241 := bstep (se 2 (by rfl) ⟨119715, by rfl⟩ : syracuseStep 319241 = 239431) B239431
theorem B253775 : Blo 167798 253775 := bstep (se 1 (by rfl) ⟨190331, by rfl⟩ : syracuseStep 253775 = 380663) B380663
theorem B253787 : Blo 167798 253787 := bstep (se 1 (by rfl) ⟨190340, by rfl⟩ : syracuseStep 253787 = 380681) B380681
theorem B253823 : Blo 167798 253823 := bstep (se 1 (by rfl) ⟨190367, by rfl⟩ : syracuseStep 253823 = 380735) B380735
theorem B253895 : Blo 167798 253895 := bstep (se 1 (by rfl) ⟨190421, by rfl⟩ : syracuseStep 253895 = 380843) B380843
theorem B1302479 : Blo 167798 1302479 := bstep (se 1 (by rfl) ⟨976859, by rfl⟩ : syracuseStep 1302479 = 1953719) B1953719
theorem B254135 : Blo 167798 254135 := bstep (se 1 (by rfl) ⟨190601, by rfl⟩ : syracuseStep 254135 = 381203) B381203
theorem B254255 : Blo 167798 254255 := bstep (se 1 (by rfl) ⟨190691, by rfl⟩ : syracuseStep 254255 = 381383) B381383
theorem B975311 : Blo 167798 975311 := bstep (se 1 (by rfl) ⟨731483, by rfl⟩ : syracuseStep 975311 = 1462967) B1462967
theorem B254447 : Blo 167798 254447 := bstep (se 1 (by rfl) ⟨190835, by rfl⟩ : syracuseStep 254447 = 381671) B381671
theorem B254495 : Blo 167798 254495 := bstep (se 1 (by rfl) ⟨190871, by rfl⟩ : syracuseStep 254495 = 381743) B381743
theorem B254555 : Blo 167798 254555 := bstep (se 1 (by rfl) ⟨190916, by rfl⟩ : syracuseStep 254555 = 381833) B381833
theorem B189247 : Blo 167798 189247 := bstep (se 1 (by rfl) ⟨141935, by rfl⟩ : syracuseStep 189247 = 283871) B283871
theorem B189535 : Blo 167798 189535 := bstep (se 1 (by rfl) ⟨142151, by rfl⟩ : syracuseStep 189535 = 284303) B284303
theorem B386207 : Blo 167798 386207 := bstep (se 1 (by rfl) ⟨289655, by rfl⟩ : syracuseStep 386207 = 579311) B579311
theorem B550099 : Blo 167798 550099 := bstep (se 1 (by rfl) ⟨412574, by rfl⟩ : syracuseStep 550099 = 825149) B825149
theorem B287975 : Blo 167798 287975 := bstep (se 1 (by rfl) ⟨215981, by rfl⟩ : syracuseStep 287975 = 431963) B431963
theorem B287995 : Blo 167798 287995 := bstep (se 1 (by rfl) ⟨215996, by rfl⟩ : syracuseStep 287995 = 431993) B431993
theorem B320851 : Blo 167798 320851 := bstep (se 1 (by rfl) ⟨240638, by rfl⟩ : syracuseStep 320851 = 481277) B481277
theorem B255593 : Blo 167798 255593 := bstep (se 2 (by rfl) ⟨95847, by rfl⟩ : syracuseStep 255593 = 191695) B191695
theorem B321823 : Blo 167798 321823 := bstep (se 1 (by rfl) ⟨241367, by rfl⟩ : syracuseStep 321823 = 482735) B482735
theorem B289183 : Blo 167798 289183 := bstep (se 1 (by rfl) ⟨216887, by rfl⟩ : syracuseStep 289183 = 433775) B433775
theorem B289487 : Blo 167798 289487 := bstep (se 1 (by rfl) ⟨217115, by rfl⟩ : syracuseStep 289487 = 434231) B434231
theorem B256751 : Blo 167798 256751 := bstep (se 1 (by rfl) ⟨192563, by rfl⟩ : syracuseStep 256751 = 385127) B385127
theorem B257129 : Blo 167798 257129 := bstep (se 2 (by rfl) ⟨96423, by rfl⟩ : syracuseStep 257129 = 192847) B192847
theorem B322795 : Blo 167798 322795 := bstep (se 1 (by rfl) ⟨242096, by rfl⟩ : syracuseStep 322795 = 484193) B484193
theorem B257519 : Blo 167798 257519 := bstep (se 1 (by rfl) ⟨193139, by rfl⟩ : syracuseStep 257519 = 386279) B386279
theorem B257657 : Blo 167798 257657 := bstep (se 2 (by rfl) ⟨96621, by rfl⟩ : syracuseStep 257657 = 193243) B193243
theorem B487291 : Blo 167798 487291 := bstep (se 1 (by rfl) ⟨365468, by rfl⟩ : syracuseStep 487291 = 730937) B730937
theorem B323615 : Blo 167798 323615 := bstep (se 1 (by rfl) ⟨242711, by rfl⟩ : syracuseStep 323615 = 485423) B485423
theorem B192703 : Blo 167798 192703 := bstep (se 1 (by rfl) ⟨144527, by rfl⟩ : syracuseStep 192703 = 289055) B289055
theorem B2060633 : Blo 167798 2060633 := bstep (se 2 (by rfl) ⟨772737, by rfl⟩ : syracuseStep 2060633 = 1545475) B1545475
theorem B1077623 : Blo 167798 1077623 := bstep (se 1 (by rfl) ⟨808217, by rfl⟩ : syracuseStep 1077623 = 1616435) B1616435
theorem B717473 : Blo 167798 717473 := bstep (se 2 (by rfl) ⟨269052, by rfl⟩ : syracuseStep 717473 = 538105) B538105
theorem B4977541 : Blo 167798 4977541 := bstep (se 4 (by rfl) ⟨466644, by rfl⟩ : syracuseStep 4977541 = 933289) B933289
theorem B1734061 : Blo 167798 1734061 := bstep (se 3 (by rfl) ⟨325136, by rfl⟩ : syracuseStep 1734061 = 650273) B650273
theorem B10516463 : Blo 167798 10516463 := bstep (se 1 (by rfl) ⟨7887347, by rfl⟩ : syracuseStep 10516463 = 15774695) B15774695
theorem B260207 : Blo 167798 260207 := bstep (se 1 (by rfl) ⟨195155, by rfl⟩ : syracuseStep 260207 = 390311) B390311
theorem B1441097 : Blo 167798 1441097 := bstep (se 2 (by rfl) ⟨540411, by rfl⟩ : syracuseStep 1441097 = 1080823) B1080823
theorem B982529 : Blo 167798 982529 := bstep (se 2 (by rfl) ⟨368448, by rfl⟩ : syracuseStep 982529 = 736897) B736897
theorem B820535 : Blo 167798 820535 := bstep (se 1 (by rfl) ⟨615401, by rfl⟩ : syracuseStep 820535 = 1230803) B1230803
theorem B230863 : Blo 167798 230863 := bstep (se 1 (by rfl) ⟨173147, by rfl⟩ : syracuseStep 230863 = 346295) B346295
theorem B427801 : Blo 167798 427801 := bstep (se 2 (by rfl) ⟨160425, by rfl⟩ : syracuseStep 427801 = 320851) B320851
theorem B461639 : Blo 167798 461639 := bstep (se 1 (by rfl) ⟨346229, by rfl⟩ : syracuseStep 461639 = 692459) B692459
theorem B855035 : Blo 167798 855035 := bstep (se 1 (by rfl) ⟨641276, by rfl⟩ : syracuseStep 855035 = 1282553) B1282553
theorem B429097 : Blo 167798 429097 := bstep (se 2 (by rfl) ⟨160911, by rfl⟩ : syracuseStep 429097 = 321823) B321823
theorem B823229 : Blo 167798 823229 := bstep (se 3 (by rfl) ⟨154355, by rfl⟩ : syracuseStep 823229 = 308711) B308711
theorem B168095 : Blo 167798 168095 := bstep (se 1 (by rfl) ⟨126071, by rfl⟩ : syracuseStep 168095 = 252143) B252143
theorem B168143 : Blo 167798 168143 := bstep (se 1 (by rfl) ⟨126107, by rfl⟩ : syracuseStep 168143 = 252215) B252215
theorem B430343 : Blo 167798 430343 := bstep (se 1 (by rfl) ⟨322757, by rfl⟩ : syracuseStep 430343 = 645515) B645515
theorem B430393 : Blo 167798 430393 := bstep (se 2 (by rfl) ⟨161397, by rfl⟩ : syracuseStep 430393 = 322795) B322795
theorem B168263 : Blo 167798 168263 := bstep (se 1 (by rfl) ⟨126197, by rfl⟩ : syracuseStep 168263 = 252395) B252395
theorem B430535 : Blo 167798 430535 := bstep (se 1 (by rfl) ⟨322901, by rfl⟩ : syracuseStep 430535 = 645803) B645803
theorem B365161 : Blo 167798 365161 := bstep (se 2 (by rfl) ⟨136935, by rfl⟩ : syracuseStep 365161 = 273871) B273871
theorem B168615 : Blo 167798 168615 := bstep (se 1 (by rfl) ⟨126461, by rfl⟩ : syracuseStep 168615 = 252923) B252923
theorem B26546885 : Blo 167798 26546885 := bstep (se 4 (by rfl) ⟨2488770, by rfl⟩ : syracuseStep 26546885 = 4977541) B4977541
theorem B168655 : Blo 167798 168655 := bstep (se 1 (by rfl) ⟨126491, by rfl⟩ : syracuseStep 168655 = 252983) B252983
theorem B168735 : Blo 167798 168735 := bstep (se 1 (by rfl) ⟨126551, by rfl⟩ : syracuseStep 168735 = 253103) B253103
theorem B122131235 : Blo 167798 122131235 := bstep (se 1 (by rfl) ⟨91598426, by rfl⟩ : syracuseStep 122131235 = 183196853) B183196853
theorem B168775 : Blo 167798 168775 := bstep (se 1 (by rfl) ⟨126581, by rfl⟩ : syracuseStep 168775 = 253163) B253163
theorem B169183 : Blo 167798 169183 := bstep (se 1 (by rfl) ⟨126887, by rfl⟩ : syracuseStep 169183 = 253775) B253775
theorem B169191 : Blo 167798 169191 := bstep (se 1 (by rfl) ⟨126893, by rfl⟩ : syracuseStep 169191 = 253787) B253787
theorem B169215 : Blo 167798 169215 := bstep (se 1 (by rfl) ⟨126911, by rfl⟩ : syracuseStep 169215 = 253823) B253823
theorem B169263 : Blo 167798 169263 := bstep (se 1 (by rfl) ⟨126947, by rfl⟩ : syracuseStep 169263 = 253895) B253895
theorem B923017 : Blo 167798 923017 := bstep (se 2 (by rfl) ⟨346131, by rfl⟩ : syracuseStep 923017 = 692263) B692263
theorem B169423 : Blo 167798 169423 := bstep (se 1 (by rfl) ⟨127067, by rfl⟩ : syracuseStep 169423 = 254135) B254135
theorem B169503 : Blo 167798 169503 := bstep (se 1 (by rfl) ⟨127127, by rfl⟩ : syracuseStep 169503 = 254255) B254255
theorem B169631 : Blo 167798 169631 := bstep (se 1 (by rfl) ⟨127223, by rfl⟩ : syracuseStep 169631 = 254447) B254447
theorem B2430647 : Blo 167798 2430647 := bstep (se 1 (by rfl) ⟨1822985, by rfl⟩ : syracuseStep 2430647 = 3645971) B3645971
theorem B169663 : Blo 167798 169663 := bstep (se 1 (by rfl) ⟨127247, by rfl⟩ : syracuseStep 169663 = 254495) B254495
theorem B169703 : Blo 167798 169703 := bstep (se 1 (by rfl) ⟨127277, by rfl⟩ : syracuseStep 169703 = 254555) B254555
theorem B170395 : Blo 167798 170395 := bstep (se 1 (by rfl) ⟨127796, by rfl⟩ : syracuseStep 170395 = 255593) B255593
theorem B171167 : Blo 167798 171167 := bstep (se 1 (by rfl) ⟨128375, by rfl⟩ : syracuseStep 171167 = 256751) B256751
theorem B171419 : Blo 167798 171419 := bstep (se 1 (by rfl) ⟨128564, by rfl⟩ : syracuseStep 171419 = 257129) B257129
theorem B728477 : Blo 167798 728477 := bstep (se 3 (by rfl) ⟨136589, by rfl⟩ : syracuseStep 728477 = 273179) B273179
theorem B171679 : Blo 167798 171679 := bstep (se 1 (by rfl) ⟨128759, by rfl⟩ : syracuseStep 171679 = 257519) B257519
theorem B171771 : Blo 167798 171771 := bstep (se 1 (by rfl) ⟨128828, by rfl⟩ : syracuseStep 171771 = 257657) B257657
theorem B1450223 : Blo 167798 1450223 := bstep (se 1 (by rfl) ⟨1087667, by rfl⟩ : syracuseStep 1450223 = 2175335) B2175335
theorem B173471 : Blo 167798 173471 := bstep (se 1 (by rfl) ⟨130103, by rfl⟩ : syracuseStep 173471 = 260207) B260207
theorem B730579 : Blo 167798 730579 := bstep (se 1 (by rfl) ⟨547934, by rfl⟩ : syracuseStep 730579 = 1095869) B1095869
theorem B2926205 : Blo 167798 2926205 := bstep (se 3 (by rfl) ⟨548663, by rfl⟩ : syracuseStep 2926205 = 1097327) B1097327
theorem B861839 : Blo 167798 861839 := bstep (se 1 (by rfl) ⟨646379, by rfl⟩ : syracuseStep 861839 = 1292759) B1292759
theorem B960731 : Blo 167798 960731 := bstep (se 1 (by rfl) ⟨720548, by rfl⟩ : syracuseStep 960731 = 1441097) B1441097
theorem B1386719 : Blo 167798 1386719 := bstep (se 1 (by rfl) ⟨1040039, by rfl⟩ : syracuseStep 1386719 = 2080079) B2080079
theorem B12593839 : Blo 167798 12593839 := bstep (se 1 (by rfl) ⟨9445379, by rfl⟩ : syracuseStep 12593839 = 18890759) B18890759
theorem B862973 : Blo 167798 862973 := bstep (se 3 (by rfl) ⟨161807, by rfl⟩ : syracuseStep 862973 = 323615) B323615
theorem B863135 : Blo 167798 863135 := bstep (se 1 (by rfl) ⟨647351, by rfl⟩ : syracuseStep 863135 = 1294703) B1294703
theorem B1944911 : Blo 167798 1944911 := bstep (se 1 (by rfl) ⟨1458683, by rfl⟩ : syracuseStep 1944911 = 2917367) B2917367
theorem B2731427 : Blo 167798 2731427 := bstep (se 1 (by rfl) ⟨2048570, by rfl⟩ : syracuseStep 2731427 = 4097141) B4097141
theorem B1650455 : Blo 167798 1650455 := bstep (se 1 (by rfl) ⟨1237841, by rfl⟩ : syracuseStep 1650455 = 2475683) B2475683
theorem B232697939 : Blo 167798 232697939 := bstep (se 1 (by rfl) ⟨174523454, by rfl⟩ : syracuseStep 232697939 = 349046909) B349046909
theorem B733465 : Blo 167798 733465 := bstep (se 2 (by rfl) ⟨275049, by rfl⟩ : syracuseStep 733465 = 550099) B550099
theorem B1290815 : Blo 167798 1290815 := bstep (se 1 (by rfl) ⟨968111, by rfl⟩ : syracuseStep 1290815 = 1936223) B1936223
theorem B537695 : Blo 167798 537695 := bstep (se 1 (by rfl) ⟨403271, by rfl⟩ : syracuseStep 537695 = 806543) B806543
theorem B243577 : Blo 167798 243577 := bstep (se 2 (by rfl) ⟨91341, by rfl⟩ : syracuseStep 243577 = 182683) B182683
theorem B571643 : Blo 167798 571643 := bstep (se 1 (by rfl) ⟨428732, by rfl⟩ : syracuseStep 571643 = 857465) B857465
theorem B1227575 : Blo 167798 1227575 := bstep (se 1 (by rfl) ⟨920681, by rfl⟩ : syracuseStep 1227575 = 1841363) B1841363
theorem B868319 : Blo 167798 868319 := bstep (se 1 (by rfl) ⟨651239, by rfl⟩ : syracuseStep 868319 = 1302479) B1302479
theorem B1164203 : Blo 167798 1164203 := bstep (se 1 (by rfl) ⟨873152, by rfl⟩ : syracuseStep 1164203 = 1746305) B1746305
theorem B378017 : Blo 167798 378017 := bstep (se 2 (by rfl) ⟨141756, by rfl⟩ : syracuseStep 378017 = 283513) B283513
theorem B378107 : Blo 167798 378107 := bstep (se 1 (by rfl) ⟨283580, by rfl⟩ : syracuseStep 378107 = 567161) B567161
theorem B2312081 : Blo 167798 2312081 := bstep (se 2 (by rfl) ⟨867030, by rfl⟩ : syracuseStep 2312081 = 1734061) B1734061
theorem B378791 : Blo 167798 378791 := bstep (se 1 (by rfl) ⟨284093, by rfl⟩ : syracuseStep 378791 = 568187) B568187
theorem B7358525 : Blo 167798 7358525 := bstep (se 3 (by rfl) ⟨1379723, by rfl⟩ : syracuseStep 7358525 = 2759447) B2759447
theorem B378953 : Blo 167798 378953 := bstep (se 2 (by rfl) ⟨142107, by rfl⟩ : syracuseStep 378953 = 284215) B284215
theorem B1951897 : Blo 167798 1951897 := bstep (se 2 (by rfl) ⟨731961, by rfl⟩ : syracuseStep 1951897 = 1463923) B1463923
theorem B379439 : Blo 167798 379439 := bstep (se 1 (by rfl) ⟨284579, by rfl⟩ : syracuseStep 379439 = 569159) B569159
theorem B641915 : Blo 167798 641915 := bstep (se 1 (by rfl) ⟨481436, by rfl⟩ : syracuseStep 641915 = 962873) B962873
theorem B478315 : Blo 167798 478315 := bstep (se 1 (by rfl) ⟨358736, by rfl⟩ : syracuseStep 478315 = 717473) B717473
theorem B707791 : Blo 167798 707791 := bstep (se 1 (by rfl) ⟨530843, by rfl⟩ : syracuseStep 707791 = 1061687) B1061687
theorem B1298105 : Blo 167798 1298105 := bstep (se 2 (by rfl) ⟨486789, by rfl⟩ : syracuseStep 1298105 = 973579) B973579
theorem B3264461 : Blo 167798 3264461 := bstep (se 3 (by rfl) ⟨612086, by rfl⟩ : syracuseStep 3264461 = 1224173) B1224173
theorem B380969 : Blo 167798 380969 := bstep (se 2 (by rfl) ⟨142863, by rfl⟩ : syracuseStep 380969 = 285727) B285727
theorem B971347 : Blo 167798 971347 := bstep (se 1 (by rfl) ⟨728510, by rfl⟩ : syracuseStep 971347 = 1457021) B1457021
theorem B381545 : Blo 167798 381545 := bstep (se 2 (by rfl) ⟨143079, by rfl⟩ : syracuseStep 381545 = 286159) B286159
theorem B1167979 : Blo 167798 1167979 := bstep (se 1 (by rfl) ⟨875984, by rfl⟩ : syracuseStep 1167979 = 1751969) B1751969
theorem B578447 : Blo 167798 578447 := bstep (se 1 (by rfl) ⟨433835, by rfl⟩ : syracuseStep 578447 = 867671) B867671
theorem B1233863 : Blo 167798 1233863 := bstep (se 1 (by rfl) ⟨925397, by rfl⟩ : syracuseStep 1233863 = 1850795) B1850795
theorem B578663 : Blo 167798 578663 := bstep (se 1 (by rfl) ⟨433997, by rfl⟩ : syracuseStep 578663 = 867995) B867995
theorem B808157 : Blo 167798 808157 := bstep (se 3 (by rfl) ⟨151529, by rfl⟩ : syracuseStep 808157 = 303059) B303059
theorem B218603 : Blo 167798 218603 := bstep (se 1 (by rfl) ⟨163952, by rfl⟩ : syracuseStep 218603 = 327905) B327905
theorem B2446843 : Blo 167798 2446843 := bstep (se 1 (by rfl) ⟨1835132, by rfl⟩ : syracuseStep 2446843 = 3670265) B3670265
theorem B382607 : Blo 167798 382607 := bstep (se 1 (by rfl) ⟨286955, by rfl⟩ : syracuseStep 382607 = 573911) B573911
theorem B3889457 : Blo 167798 3889457 := bstep (se 2 (by rfl) ⟨1458546, by rfl⟩ : syracuseStep 3889457 = 2917093) B2917093
theorem B252329 : Blo 167798 252329 := bstep (se 2 (by rfl) ⟨94623, by rfl⟩ : syracuseStep 252329 = 189247) B189247
theorem B285167 : Blo 167798 285167 := bstep (se 1 (by rfl) ⟨213875, by rfl⟩ : syracuseStep 285167 = 427751) B427751
theorem B383579 : Blo 167798 383579 := bstep (se 1 (by rfl) ⟨287684, by rfl⟩ : syracuseStep 383579 = 575369) B575369
theorem B285403 : Blo 167798 285403 := bstep (se 1 (by rfl) ⟨214052, by rfl⟩ : syracuseStep 285403 = 428105) B428105
theorem B252713 : Blo 167798 252713 := bstep (se 2 (by rfl) ⟨94767, by rfl⟩ : syracuseStep 252713 = 189535) B189535
theorem B383993 : Blo 167798 383993 := bstep (se 2 (by rfl) ⟨143997, by rfl⟩ : syracuseStep 383993 = 287995) B287995
theorem B646319 : Blo 167798 646319 := bstep (se 1 (by rfl) ⟨484739, by rfl⟩ : syracuseStep 646319 = 969479) B969479
theorem B253247 : Blo 167798 253247 := bstep (se 1 (by rfl) ⟨189935, by rfl⟩ : syracuseStep 253247 = 379871) B379871
theorem B253487 : Blo 167798 253487 := bstep (se 1 (by rfl) ⟨190115, by rfl⟩ : syracuseStep 253487 = 380231) B380231
theorem B1040215 : Blo 167798 1040215 := bstep (se 1 (by rfl) ⟨780161, by rfl⟩ : syracuseStep 1040215 = 1560323) B1560323
theorem B1236905 : Blo 167798 1236905 := bstep (se 2 (by rfl) ⟨463839, by rfl⟩ : syracuseStep 1236905 = 927679) B927679
theorem B286841 : Blo 167798 286841 := bstep (se 2 (by rfl) ⟨107565, by rfl⟩ : syracuseStep 286841 = 215131) B215131
theorem B254399 : Blo 167798 254399 := bstep (se 1 (by rfl) ⟨190799, by rfl⟩ : syracuseStep 254399 = 381599) B381599
theorem B2941481 : Blo 167798 2941481 := bstep (se 2 (by rfl) ⟨1103055, by rfl⟩ : syracuseStep 2941481 = 2206111) B2206111
theorem B385577 : Blo 167798 385577 := bstep (se 2 (by rfl) ⟨144591, by rfl⟩ : syracuseStep 385577 = 289183) B289183
theorem B3924571 : Blo 167798 3924571 := bstep (se 1 (by rfl) ⟨2943428, by rfl⟩ : syracuseStep 3924571 = 5886857) B5886857
theorem B254783 : Blo 167798 254783 := bstep (se 1 (by rfl) ⟨191087, by rfl⟩ : syracuseStep 254783 = 382175) B382175
theorem B385991 : Blo 167798 385991 := bstep (se 1 (by rfl) ⟨289493, by rfl⟩ : syracuseStep 385991 = 578987) B578987
theorem B320699 : Blo 167798 320699 := bstep (se 1 (by rfl) ⟨240524, by rfl⟩ : syracuseStep 320699 = 481049) B481049
theorem B615863 : Blo 167798 615863 := bstep (se 1 (by rfl) ⟨461897, by rfl⟩ : syracuseStep 615863 = 923795) B923795
theorem B288839 : Blo 167798 288839 := bstep (se 1 (by rfl) ⟨216629, by rfl⟩ : syracuseStep 288839 = 433259) B433259
theorem B256283 : Blo 167798 256283 := bstep (se 1 (by rfl) ⟨192212, by rfl⟩ : syracuseStep 256283 = 384425) B384425
theorem B649721 : Blo 167798 649721 := bstep (se 2 (by rfl) ⟨243645, by rfl⟩ : syracuseStep 649721 = 487291) B487291
theorem B486175 : Blo 167798 486175 := bstep (se 1 (by rfl) ⟨364631, by rfl⟩ : syracuseStep 486175 = 729263) B729263
theorem B289703 : Blo 167798 289703 := bstep (se 1 (by rfl) ⟨217277, by rfl⟩ : syracuseStep 289703 = 434555) B434555
theorem B256937 : Blo 167798 256937 := bstep (se 2 (by rfl) ⟨96351, by rfl⟩ : syracuseStep 256937 = 192703) B192703
theorem B650207 : Blo 167798 650207 := bstep (se 1 (by rfl) ⟨487655, by rfl⟩ : syracuseStep 650207 = 975311) B975311
theorem B1371161 : Blo 167798 1371161 := bstep (se 2 (by rfl) ⟨514185, by rfl⟩ : syracuseStep 1371161 = 1028371) B1028371
theorem B257471 : Blo 167798 257471 := bstep (se 1 (by rfl) ⟨193103, by rfl⟩ : syracuseStep 257471 = 386207) B386207
theorem B191983 : Blo 167798 191983 := bstep (se 1 (by rfl) ⟨143987, by rfl⟩ : syracuseStep 191983 = 287975) B287975
theorem B618113 : Blo 167798 618113 := bstep (se 2 (by rfl) ⟨231792, by rfl⟩ : syracuseStep 618113 = 463585) B463585
theorem B192991 : Blo 167798 192991 := bstep (se 1 (by rfl) ⟨144743, by rfl⟩ : syracuseStep 192991 = 289487) B289487
theorem B3470161 : Blo 167798 3470161 := bstep (se 2 (by rfl) ⟨1301310, by rfl⟩ : syracuseStep 3470161 = 2602621) B2602621
theorem B4945049 : Blo 167798 4945049 := bstep (se 2 (by rfl) ⟨1854393, by rfl⟩ : syracuseStep 4945049 = 3708787) B3708787
theorem B1275263 : Blo 167798 1275263 := bstep (se 1 (by rfl) ⟨956447, by rfl⟩ : syracuseStep 1275263 = 1912895) B1912895
theorem B1373755 : Blo 167798 1373755 := bstep (se 1 (by rfl) ⟨1030316, by rfl⟩ : syracuseStep 1373755 = 2060633) B2060633
theorem B718415 : Blo 167798 718415 := bstep (se 1 (by rfl) ⟨538811, by rfl⟩ : syracuseStep 718415 = 1077623) B1077623
theorem B2160209 : Blo 167798 2160209 := bstep (se 2 (by rfl) ⟨810078, by rfl⟩ : syracuseStep 2160209 = 1620157) B1620157
theorem B292843 : Blo 167798 292843 := bstep (se 1 (by rfl) ⟨219632, by rfl⟩ : syracuseStep 292843 = 439265) B439265
theorem B1440413 : Blo 167798 1440413 := bstep (se 3 (by rfl) ⟨270077, by rfl⟩ : syracuseStep 1440413 = 540155) B540155
theorem B7010975 : Blo 167798 7010975 := bstep (se 1 (by rfl) ⟨5258231, by rfl⟩ : syracuseStep 7010975 = 10516463) B10516463
theorem B851309 : Blo 167798 851309 := bstep (se 3 (by rfl) ⟨159620, by rfl⟩ : syracuseStep 851309 = 319241) B319241
theorem B2456993 : Blo 167798 2456993 := bstep (se 2 (by rfl) ⟨921372, by rfl⟩ : syracuseStep 2456993 = 1842745) B1842745
theorem B655019 : Blo 167798 655019 := bstep (se 1 (by rfl) ⟨491264, by rfl⟩ : syracuseStep 655019 = 982529) B982529
theorem B620527837 : Blo 167798 620527837 := bstep (se 3 (by rfl) ⟨116348969, by rfl⟩ : syracuseStep 620527837 = 232697939) B232697939
theorem B1541387 : Blo 167798 1541387 := bstep (se 1 (by rfl) ⟨1156040, by rfl⟩ : syracuseStep 1541387 = 2312081) B2312081
theorem B427943 : Blo 167798 427943 := bstep (se 1 (by rfl) ⟨320957, by rfl⟩ : syracuseStep 427943 = 641915) B641915
theorem B17697923 : Blo 167798 17697923 := bstep (se 1 (by rfl) ⟨13273442, by rfl⟩ : syracuseStep 17697923 = 26546885) B26546885
theorem B855197 : Blo 167798 855197 := bstep (se 3 (by rfl) ⟨160349, by rfl⟩ : syracuseStep 855197 = 320699) B320699
theorem B822575 : Blo 167798 822575 := bstep (se 1 (by rfl) ⟨616931, by rfl⟩ : syracuseStep 822575 = 1233863) B1233863
theorem B1642301 : Blo 167798 1642301 := bstep (se 3 (by rfl) ⟨307931, by rfl⟩ : syracuseStep 1642301 = 615863) B615863
theorem B2592971 : Blo 167798 2592971 := bstep (se 1 (by rfl) ⟨1944728, by rfl⟩ : syracuseStep 2592971 = 3889457) B3889457
theorem B168219 : Blo 167798 168219 := bstep (se 1 (by rfl) ⟨126164, by rfl⟩ : syracuseStep 168219 = 252329) B252329
theorem B168475 : Blo 167798 168475 := bstep (se 1 (by rfl) ⟨126356, by rfl⟩ : syracuseStep 168475 = 252713) B252713
theorem B430879 : Blo 167798 430879 := bstep (se 1 (by rfl) ⟨323159, by rfl⟩ : syracuseStep 430879 = 646319) B646319
theorem B168831 : Blo 167798 168831 := bstep (se 1 (by rfl) ⟨126623, by rfl⟩ : syracuseStep 168831 = 253247) B253247
theorem B168991 : Blo 167798 168991 := bstep (se 1 (by rfl) ⟨126743, by rfl⟩ : syracuseStep 168991 = 253487) B253487
theorem B824603 : Blo 167798 824603 := bstep (se 1 (by rfl) ⟨618452, by rfl⟩ : syracuseStep 824603 = 1236905) B1236905
theorem B169599 : Blo 167798 169599 := bstep (se 1 (by rfl) ⟨127199, by rfl⟩ : syracuseStep 169599 = 254399) B254399
theorem B169855 : Blo 167798 169855 := bstep (se 1 (by rfl) ⟨127391, by rfl⟩ : syracuseStep 169855 = 254783) B254783
theorem B4626881 : Blo 167798 4626881 := bstep (se 2 (by rfl) ⟨1735080, by rfl⟩ : syracuseStep 4626881 = 3470161) B3470161
theorem B924479 : Blo 167798 924479 := bstep (se 1 (by rfl) ⟨693359, by rfl⟩ : syracuseStep 924479 = 1386719) B1386719
theorem B170855 : Blo 167798 170855 := bstep (se 1 (by rfl) ⟨128141, by rfl⟩ : syracuseStep 170855 = 256283) B256283
theorem B433147 : Blo 167798 433147 := bstep (se 1 (by rfl) ⟨324860, by rfl⟩ : syracuseStep 433147 = 649721) B649721
theorem B171291 : Blo 167798 171291 := bstep (se 1 (by rfl) ⟨128468, by rfl⟩ : syracuseStep 171291 = 256937) B256937
theorem B433471 : Blo 167798 433471 := bstep (se 1 (by rfl) ⟨325103, by rfl⟩ : syracuseStep 433471 = 650207) B650207
theorem B171647 : Blo 167798 171647 := bstep (se 1 (by rfl) ⟨128735, by rfl⟩ : syracuseStep 171647 = 257471) B257471
theorem B860543 : Blo 167798 860543 := bstep (se 1 (by rfl) ⟨645407, by rfl⟩ : syracuseStep 860543 = 1290815) B1290815
theorem B960275 : Blo 167798 960275 := bstep (se 1 (by rfl) ⟨720206, by rfl⟩ : syracuseStep 960275 = 1440413) B1440413
theorem B567539 : Blo 167798 567539 := bstep (se 1 (by rfl) ⟨425654, by rfl⟩ : syracuseStep 567539 = 851309) B851309
theorem B436679 : Blo 167798 436679 := bstep (se 1 (by rfl) ⟨327509, by rfl⟩ : syracuseStep 436679 = 655019) B655019
theorem B1386953 : Blo 167798 1386953 := bstep (se 2 (by rfl) ⟨520107, by rfl⟩ : syracuseStep 1386953 = 1040215) B1040215
theorem B7843949 : Blo 167798 7843949 := bstep (se 3 (by rfl) ⟨1470740, by rfl⟩ : syracuseStep 7843949 = 2941481) B2941481
theorem B307817 : Blo 167798 307817 := bstep (se 2 (by rfl) ⟨115431, by rfl⟩ : syracuseStep 307817 = 230863) B230863
theorem B570023 : Blo 167798 570023 := bstep (se 1 (by rfl) ⟨427517, by rfl⟩ : syracuseStep 570023 = 855035) B855035
theorem B570401 : Blo 167798 570401 := bstep (se 2 (by rfl) ⟨213900, by rfl⟩ : syracuseStep 570401 = 427801) B427801
theorem B865403 : Blo 167798 865403 := bstep (se 1 (by rfl) ⟨649052, by rfl⟩ : syracuseStep 865403 = 1298105) B1298105
theorem B2176307 : Blo 167798 2176307 := bstep (se 1 (by rfl) ⟨1632230, by rfl⟩ : syracuseStep 2176307 = 3264461) B3264461
theorem B2602529 : Blo 167798 2602529 := bstep (se 2 (by rfl) ⟨975948, by rfl⟩ : syracuseStep 2602529 = 1951897) B1951897
theorem B16791785 : Blo 167798 16791785 := bstep (se 2 (by rfl) ⟨6296919, by rfl⟩ : syracuseStep 16791785 = 12593839) B12593839
theorem B1620431 : Blo 167798 1620431 := bstep (se 1 (by rfl) ⟨1215323, by rfl⟩ : syracuseStep 1620431 = 2430647) B2430647
theorem B572129 : Blo 167798 572129 := bstep (se 2 (by rfl) ⟨214548, by rfl⟩ : syracuseStep 572129 = 429097) B429097
theorem B637753 : Blo 167798 637753 := bstep (se 2 (by rfl) ⟨239157, by rfl⟩ : syracuseStep 637753 = 478315) B478315
theorem B1850357 : Blo 167798 1850357 := bstep (se 5 (by rfl) ⟨86735, by rfl⟩ : syracuseStep 1850357 = 173471) B173471
theorem B966815 : Blo 167798 966815 := bstep (se 1 (by rfl) ⟨725111, by rfl⟩ : syracuseStep 966815 = 1450223) B1450223
theorem B573857 : Blo 167798 573857 := bstep (se 2 (by rfl) ⟨215196, by rfl⟩ : syracuseStep 573857 = 430393) B430393
theorem B1295129 : Blo 167798 1295129 := bstep (se 2 (by rfl) ⟨485673, by rfl⟩ : syracuseStep 1295129 = 971347) B971347
theorem B1557305 : Blo 167798 1557305 := bstep (se 2 (by rfl) ⟨583989, by rfl⟩ : syracuseStep 1557305 = 1167979) B1167979
theorem B1950803 : Blo 167798 1950803 := bstep (se 1 (by rfl) ⟨1463102, by rfl⟩ : syracuseStep 1950803 = 2926205) B2926205
theorem B574559 : Blo 167798 574559 := bstep (se 1 (by rfl) ⟨430919, by rfl⟩ : syracuseStep 574559 = 861839) B861839
theorem B640487 : Blo 167798 640487 := bstep (se 1 (by rfl) ⟨480365, by rfl⟩ : syracuseStep 640487 = 960731) B960731
theorem B18695933 : Blo 167798 18695933 := bstep (se 3 (by rfl) ⟨3505487, by rfl⟩ : syracuseStep 18695933 = 7010975) B7010975
theorem B575315 : Blo 167798 575315 := bstep (se 1 (by rfl) ⟨431486, by rfl⟩ : syracuseStep 575315 = 862973) B862973
theorem B1230689 : Blo 167798 1230689 := bstep (se 2 (by rfl) ⟨461508, by rfl⟩ : syracuseStep 1230689 = 923017) B923017
theorem B575423 : Blo 167798 575423 := bstep (se 1 (by rfl) ⟨431567, by rfl⟩ : syracuseStep 575423 = 863135) B863135
theorem B3262457 : Blo 167798 3262457 := bstep (se 2 (by rfl) ⟨1223421, by rfl⟩ : syracuseStep 3262457 = 2446843) B2446843
theorem B1231037 : Blo 167798 1231037 := bstep (se 3 (by rfl) ⟨230819, by rfl⟩ : syracuseStep 1231037 = 461639) B461639
theorem B1296607 : Blo 167798 1296607 := bstep (se 1 (by rfl) ⟨972455, by rfl⟩ : syracuseStep 1296607 = 1944911) B1944911
theorem B1820951 : Blo 167798 1820951 := bstep (se 1 (by rfl) ⟨1365713, by rfl⟩ : syracuseStep 1820951 = 2731427) B2731427
theorem B412075 : Blo 167798 412075 := bstep (se 1 (by rfl) ⟨309056, by rfl⟩ : syracuseStep 412075 = 618113) B618113
theorem B1100303 : Blo 167798 1100303 := bstep (se 1 (by rfl) ⟨825227, by rfl⟩ : syracuseStep 1100303 = 1650455) B1650455
theorem B3296699 : Blo 167798 3296699 := bstep (se 1 (by rfl) ⟨2472524, by rfl⟩ : syracuseStep 3296699 = 4945049) B4945049
theorem B380537 : Blo 167798 380537 := bstep (se 2 (by rfl) ⟨142701, by rfl⟩ : syracuseStep 380537 = 285403) B285403
theorem B478943 : Blo 167798 478943 := bstep (se 1 (by rfl) ⟨359207, by rfl⟩ : syracuseStep 478943 = 718415) B718415
theorem B381095 : Blo 167798 381095 := bstep (se 1 (by rfl) ⟨285821, by rfl⟩ : syracuseStep 381095 = 571643) B571643
theorem B1299077 : Blo 167798 1299077 := bstep (se 4 (by rfl) ⟨121788, by rfl⟩ : syracuseStep 1299077 = 243577) B243577
theorem B578879 : Blo 167798 578879 := bstep (se 1 (by rfl) ⟨434159, by rfl⟩ : syracuseStep 578879 = 868319) B868319
theorem B776135 : Blo 167798 776135 := bstep (se 1 (by rfl) ⟨582101, by rfl⟩ : syracuseStep 776135 = 1164203) B1164203
theorem B252011 : Blo 167798 252011 := bstep (se 1 (by rfl) ⟨189008, by rfl⟩ : syracuseStep 252011 = 378017) B378017
theorem B5232761 : Blo 167798 5232761 := bstep (se 2 (by rfl) ⟨1962285, by rfl⟩ : syracuseStep 5232761 = 3924571) B3924571
theorem B252071 : Blo 167798 252071 := bstep (se 1 (by rfl) ⟨189053, by rfl⟩ : syracuseStep 252071 = 378107) B378107
theorem B252527 : Blo 167798 252527 := bstep (se 1 (by rfl) ⟨189395, by rfl⟩ : syracuseStep 252527 = 378791) B378791
theorem B4905683 : Blo 167798 4905683 := bstep (se 1 (by rfl) ⟨3679262, by rfl⟩ : syracuseStep 4905683 = 7358525) B7358525
theorem B252635 : Blo 167798 252635 := bstep (se 1 (by rfl) ⟨189476, by rfl⟩ : syracuseStep 252635 = 378953) B378953
theorem B252959 : Blo 167798 252959 := bstep (se 1 (by rfl) ⟨189719, by rfl⟩ : syracuseStep 252959 = 379439) B379439
theorem B974105 : Blo 167798 974105 := bstep (se 2 (by rfl) ⟨365289, by rfl⟩ : syracuseStep 974105 = 730579) B730579
theorem B548819 : Blo 167798 548819 := bstep (se 1 (by rfl) ⟨411614, by rfl⟩ : syracuseStep 548819 = 823229) B823229
theorem B253979 : Blo 167798 253979 := bstep (se 1 (by rfl) ⟨190484, by rfl⟩ : syracuseStep 253979 = 380969) B380969
theorem B286895 : Blo 167798 286895 := bstep (se 1 (by rfl) ⟨215171, by rfl⟩ : syracuseStep 286895 = 430343) B430343
theorem B287023 : Blo 167798 287023 := bstep (se 1 (by rfl) ⟨215267, by rfl⟩ : syracuseStep 287023 = 430535) B430535
theorem B254363 : Blo 167798 254363 := bstep (se 1 (by rfl) ⟨190772, by rfl⟩ : syracuseStep 254363 = 381545) B381545
theorem B81420823 : Blo 167798 81420823 := bstep (se 1 (by rfl) ⟨61065617, by rfl⟩ : syracuseStep 81420823 = 122131235) B122131235
theorem B2155085 : Blo 167798 2155085 := bstep (se 3 (by rfl) ⟨404078, by rfl⟩ : syracuseStep 2155085 = 808157) B808157
theorem B385631 : Blo 167798 385631 := bstep (se 1 (by rfl) ⟨289223, by rfl⟩ : syracuseStep 385631 = 578447) B578447
theorem B385775 : Blo 167798 385775 := bstep (se 1 (by rfl) ⟨289331, by rfl⟩ : syracuseStep 385775 = 578663) B578663
theorem B2188093 : Blo 167798 2188093 := bstep (se 3 (by rfl) ⟨410267, by rfl⟩ : syracuseStep 2188093 = 820535) B820535
theorem B648233 : Blo 167798 648233 := bstep (se 2 (by rfl) ⟨243087, by rfl⟩ : syracuseStep 648233 = 486175) B486175
theorem B255071 : Blo 167798 255071 := bstep (se 1 (by rfl) ⟨191303, by rfl⟩ : syracuseStep 255071 = 382607) B382607
theorem B582941 : Blo 167798 582941 := bstep (se 3 (by rfl) ⟨109301, by rfl⟩ : syracuseStep 582941 = 218603) B218603
theorem B943721 : Blo 167798 943721 := bstep (se 2 (by rfl) ⟨353895, by rfl⟩ : syracuseStep 943721 = 707791) B707791
theorem B190111 : Blo 167798 190111 := bstep (se 1 (by rfl) ⟨142583, by rfl⟩ : syracuseStep 190111 = 285167) B285167
theorem B255719 : Blo 167798 255719 := bstep (se 1 (by rfl) ⟨191789, by rfl⟩ : syracuseStep 255719 = 383579) B383579
theorem B255977 : Blo 167798 255977 := bstep (se 2 (by rfl) ⟨95991, by rfl⟩ : syracuseStep 255977 = 191983) B191983
theorem B255995 : Blo 167798 255995 := bstep (se 1 (by rfl) ⟨191996, by rfl⟩ : syracuseStep 255995 = 383993) B383993
theorem B485651 : Blo 167798 485651 := bstep (se 1 (by rfl) ⟨364238, by rfl⟩ : syracuseStep 485651 = 728477) B728477
theorem B191227 : Blo 167798 191227 := bstep (se 1 (by rfl) ⟨143420, by rfl⟩ : syracuseStep 191227 = 286841) B286841
theorem B257051 : Blo 167798 257051 := bstep (se 1 (by rfl) ⟨192788, by rfl⟩ : syracuseStep 257051 = 385577) B385577
theorem B977953 : Blo 167798 977953 := bstep (se 2 (by rfl) ⟨366732, by rfl⟩ : syracuseStep 977953 = 733465) B733465
theorem B257321 : Blo 167798 257321 := bstep (se 2 (by rfl) ⟨96495, by rfl⟩ : syracuseStep 257321 = 192991) B192991
theorem B257327 : Blo 167798 257327 := bstep (se 1 (by rfl) ⟨192995, by rfl⟩ : syracuseStep 257327 = 385991) B385991
theorem B486881 : Blo 167798 486881 := bstep (se 2 (by rfl) ⟨182580, by rfl⟩ : syracuseStep 486881 = 365161) B365161
theorem B192559 : Blo 167798 192559 := bstep (se 1 (by rfl) ⟨144419, by rfl⟩ : syracuseStep 192559 = 288839) B288839
theorem B193135 : Blo 167798 193135 := bstep (se 1 (by rfl) ⟨144851, by rfl⟩ : syracuseStep 193135 = 289703) B289703
theorem B914107 : Blo 167798 914107 := bstep (se 1 (by rfl) ⟨685580, by rfl⟩ : syracuseStep 914107 = 1371161) B1371161
theorem B1831673 : Blo 167798 1831673 := bstep (se 2 (by rfl) ⟨686877, by rfl⟩ : syracuseStep 1831673 = 1373755) B1373755
theorem B390457 : Blo 167798 390457 := bstep (se 2 (by rfl) ⟨146421, by rfl⟩ : syracuseStep 390457 = 292843) B292843
theorem B358463 : Blo 167798 358463 := bstep (se 1 (by rfl) ⟨268847, by rfl⟩ : syracuseStep 358463 = 537695) B537695
theorem B850175 : Blo 167798 850175 := bstep (se 1 (by rfl) ⟨637631, by rfl⟩ : syracuseStep 850175 = 1275263) B1275263
theorem B1440139 : Blo 167798 1440139 := bstep (se 1 (by rfl) ⟨1080104, by rfl⟩ : syracuseStep 1440139 = 2160209) B2160209
theorem B818383 : Blo 167798 818383 := bstep (se 1 (by rfl) ⟨613787, by rfl⟩ : syracuseStep 818383 = 1227575) B1227575
theorem B1637995 : Blo 167798 1637995 := bstep (se 1 (by rfl) ⟨1228496, by rfl⟩ : syracuseStep 1637995 = 2456993) B2456993
theorem B108561097 : Blo 167798 108561097 := bstep (se 2 (by rfl) ⟨40710411, by rfl⟩ : syracuseStep 108561097 = 81420823) B81420823
theorem B426991 : Blo 167798 426991 := bstep (se 1 (by rfl) ⟨320243, by rfl⟩ : syracuseStep 426991 = 640487) B640487
theorem B2917457 : Blo 167798 2917457 := bstep (se 2 (by rfl) ⟨1094046, by rfl⟩ : syracuseStep 2917457 = 2188093) B2188093
theorem B820459 : Blo 167798 820459 := bstep (se 1 (by rfl) ⟨615344, by rfl⟩ : syracuseStep 820459 = 1230689) B1230689
theorem B820691 : Blo 167798 820691 := bstep (se 1 (by rfl) ⟨615518, by rfl⟩ : syracuseStep 820691 = 1231037) B1231037
theorem B1213967 : Blo 167798 1213967 := bstep (se 1 (by rfl) ⟨910475, by rfl⟩ : syracuseStep 1213967 = 1820951) B1820951
theorem B4884461 : Blo 167798 4884461 := bstep (se 3 (by rfl) ⟨915836, by rfl⟩ : syracuseStep 4884461 = 1831673) B1831673
theorem B11798615 : Blo 167798 11798615 := bstep (se 1 (by rfl) ⟨8848961, by rfl⟩ : syracuseStep 11798615 = 17697923) B17697923
theorem B2197799 : Blo 167798 2197799 := bstep (se 1 (by rfl) ⟨1648349, by rfl⟩ : syracuseStep 2197799 = 3296699) B3296699
theorem B168007 : Blo 167798 168007 := bstep (se 1 (by rfl) ⟨126005, by rfl⟩ : syracuseStep 168007 = 252011) B252011
theorem B168047 : Blo 167798 168047 := bstep (se 1 (by rfl) ⟨126035, by rfl⟩ : syracuseStep 168047 = 252071) B252071
theorem B3084587 : Blo 167798 3084587 := bstep (se 1 (by rfl) ⟨2313440, by rfl⟩ : syracuseStep 3084587 = 4626881) B4626881
theorem B168351 : Blo 167798 168351 := bstep (se 1 (by rfl) ⟨126263, by rfl⟩ : syracuseStep 168351 = 252527) B252527
theorem B168423 : Blo 167798 168423 := bstep (se 1 (by rfl) ⟨126317, by rfl⟩ : syracuseStep 168423 = 252635) B252635
theorem B168639 : Blo 167798 168639 := bstep (se 1 (by rfl) ⟨126479, by rfl⟩ : syracuseStep 168639 = 252959) B252959
theorem B365879 : Blo 167798 365879 := bstep (se 1 (by rfl) ⟨274409, by rfl⟩ : syracuseStep 365879 = 548819) B548819
theorem B169319 : Blo 167798 169319 := bstep (se 1 (by rfl) ⟨126989, by rfl⟩ : syracuseStep 169319 = 253979) B253979
theorem B955901 : Blo 167798 955901 := bstep (se 3 (by rfl) ⟨179231, by rfl⟩ : syracuseStep 955901 = 358463) B358463
theorem B169575 : Blo 167798 169575 := bstep (se 1 (by rfl) ⟨127181, by rfl⟩ : syracuseStep 169575 = 254363) B254363
theorem B432155 : Blo 167798 432155 := bstep (se 1 (by rfl) ⟨324116, by rfl⟩ : syracuseStep 432155 = 648233) B648233
theorem B170047 : Blo 167798 170047 := bstep (se 1 (by rfl) ⟨127535, by rfl⟩ : syracuseStep 170047 = 255071) B255071
theorem B1218809 : Blo 167798 1218809 := bstep (se 2 (by rfl) ⟨457053, by rfl⟩ : syracuseStep 1218809 = 914107) B914107
theorem B629147 : Blo 167798 629147 := bstep (se 1 (by rfl) ⟨471860, by rfl⟩ : syracuseStep 629147 = 943721) B943721
theorem B170479 : Blo 167798 170479 := bstep (se 1 (by rfl) ⟨127859, by rfl⟩ : syracuseStep 170479 = 255719) B255719
theorem B170651 : Blo 167798 170651 := bstep (se 1 (by rfl) ⟨127988, by rfl⟩ : syracuseStep 170651 = 255977) B255977
theorem B170663 : Blo 167798 170663 := bstep (se 1 (by rfl) ⟨127997, by rfl⟩ : syracuseStep 170663 = 255995) B255995
theorem B924635 : Blo 167798 924635 := bstep (se 1 (by rfl) ⟨693476, by rfl⟩ : syracuseStep 924635 = 1386953) B1386953
theorem B171367 : Blo 167798 171367 := bstep (se 1 (by rfl) ⟨128525, by rfl⟩ : syracuseStep 171367 = 257051) B257051
theorem B171547 : Blo 167798 171547 := bstep (se 1 (by rfl) ⟨128660, by rfl⟩ : syracuseStep 171547 = 257321) B257321
theorem B171551 : Blo 167798 171551 := bstep (se 1 (by rfl) ⟨128663, by rfl⟩ : syracuseStep 171551 = 257327) B257327
theorem B205211 : Blo 167798 205211 := bstep (se 1 (by rfl) ⟨153908, by rfl⟩ : syracuseStep 205211 = 307817) B307817
theorem B1450871 : Blo 167798 1450871 := bstep (se 1 (by rfl) ⟨1088153, by rfl⟩ : syracuseStep 1450871 = 2176307) B2176307
theorem B566783 : Blo 167798 566783 := bstep (se 1 (by rfl) ⟨425087, by rfl⟩ : syracuseStep 566783 = 850175) B850175
theorem B1091177 : Blo 167798 1091177 := bstep (se 2 (by rfl) ⟨409191, by rfl⟩ : syracuseStep 1091177 = 818383) B818383
theorem B827370449 : Blo 167798 827370449 := bstep (se 2 (by rfl) ⟨310263918, by rfl⟩ : syracuseStep 827370449 = 620527837) B620527837
theorem B12463955 : Blo 167798 12463955 := bstep (se 1 (by rfl) ⟨9347966, by rfl⟩ : syracuseStep 12463955 = 18695933) B18695933
theorem B2174971 : Blo 167798 2174971 := bstep (se 1 (by rfl) ⟨1631228, by rfl⟩ : syracuseStep 2174971 = 3262457) B3262457
theorem B733535 : Blo 167798 733535 := bstep (se 1 (by rfl) ⟨550151, by rfl⟩ : syracuseStep 733535 = 1100303) B1100303
theorem B3453677 : Blo 167798 3453677 := bstep (se 3 (by rfl) ⟨647564, by rfl⟩ : syracuseStep 3453677 = 1295129) B1295129
theorem B570131 : Blo 167798 570131 := bstep (se 1 (by rfl) ⟨427598, by rfl⟩ : syracuseStep 570131 = 855197) B855197
theorem B1094867 : Blo 167798 1094867 := bstep (se 1 (by rfl) ⟨821150, by rfl⟩ : syracuseStep 1094867 = 1642301) B1642301
theorem B8795765 : Blo 167798 8795765 := bstep (se 5 (by rfl) ⟨412301, by rfl⟩ : syracuseStep 8795765 = 824603) B824603
theorem B866051 : Blo 167798 866051 := bstep (se 1 (by rfl) ⟨649538, by rfl⟩ : syracuseStep 866051 = 1299077) B1299077
theorem B4110365 : Blo 167798 4110365 := bstep (se 3 (by rfl) ⟨770693, by rfl⟩ : syracuseStep 4110365 = 1541387) B1541387
theorem B1554509 : Blo 167798 1554509 := bstep (se 3 (by rfl) ⟨291470, by rfl⟩ : syracuseStep 1554509 = 582941) B582941
theorem B3488507 : Blo 167798 3488507 := bstep (se 1 (by rfl) ⟨2616380, by rfl⟩ : syracuseStep 3488507 = 5232761) B5232761
theorem B573695 : Blo 167798 573695 := bstep (se 1 (by rfl) ⟨430271, by rfl⟩ : syracuseStep 573695 = 860543) B860543
theorem B574505 : Blo 167798 574505 := bstep (se 2 (by rfl) ⟨215439, by rfl⟩ : syracuseStep 574505 = 430879) B430879
theorem B640183 : Blo 167798 640183 := bstep (se 1 (by rfl) ⟨480137, by rfl⟩ : syracuseStep 640183 = 960275) B960275
theorem B378359 : Blo 167798 378359 := bstep (se 1 (by rfl) ⟨283769, by rfl⟩ : syracuseStep 378359 = 567539) B567539
theorem B5229299 : Blo 167798 5229299 := bstep (se 1 (by rfl) ⟨3921974, by rfl⟩ : syracuseStep 5229299 = 7843949) B7843949
theorem B380015 : Blo 167798 380015 := bstep (se 1 (by rfl) ⟨285011, by rfl⟩ : syracuseStep 380015 = 570023) B570023
theorem B1920185 : Blo 167798 1920185 := bstep (se 2 (by rfl) ⟨720069, by rfl⟩ : syracuseStep 1920185 = 1440139) B1440139
theorem B380267 : Blo 167798 380267 := bstep (se 1 (by rfl) ⟨285200, by rfl⟩ : syracuseStep 380267 = 570401) B570401
theorem B576935 : Blo 167798 576935 := bstep (se 1 (by rfl) ⟨432701, by rfl⟩ : syracuseStep 576935 = 865403) B865403
theorem B577529 : Blo 167798 577529 := bstep (se 2 (by rfl) ⟨216573, by rfl⟩ : syracuseStep 577529 = 433147) B433147
theorem B11194523 : Blo 167798 11194523 := bstep (se 1 (by rfl) ⟨8395892, by rfl⟩ : syracuseStep 11194523 = 16791785) B16791785
theorem B577961 : Blo 167798 577961 := bstep (se 2 (by rfl) ⟨216735, by rfl⟩ : syracuseStep 577961 = 433471) B433471
theorem B381419 : Blo 167798 381419 := bstep (se 1 (by rfl) ⟨286064, by rfl⟩ : syracuseStep 381419 = 572129) B572129
theorem B1233571 : Blo 167798 1233571 := bstep (se 1 (by rfl) ⟨925178, by rfl⟩ : syracuseStep 1233571 = 1850357) B1850357
theorem B2183993 : Blo 167798 2183993 := bstep (se 2 (by rfl) ⟨818997, by rfl⟩ : syracuseStep 2183993 = 1637995) B1637995
theorem B644543 : Blo 167798 644543 := bstep (se 1 (by rfl) ⟨483407, by rfl⟩ : syracuseStep 644543 = 966815) B966815
theorem B382571 : Blo 167798 382571 := bstep (se 1 (by rfl) ⟨286928, by rfl⟩ : syracuseStep 382571 = 573857) B573857
theorem B382697 : Blo 167798 382697 := bstep (se 2 (by rfl) ⟨143511, by rfl⟩ : syracuseStep 382697 = 287023) B287023
theorem B1038203 : Blo 167798 1038203 := bstep (se 1 (by rfl) ⟨778652, by rfl⟩ : syracuseStep 1038203 = 1557305) B1557305
theorem B1300535 : Blo 167798 1300535 := bstep (se 1 (by rfl) ⟨975401, by rfl⟩ : syracuseStep 1300535 = 1950803) B1950803
theorem B383039 : Blo 167798 383039 := bstep (se 1 (by rfl) ⟨287279, by rfl⟩ : syracuseStep 383039 = 574559) B574559
theorem B383543 : Blo 167798 383543 := bstep (se 1 (by rfl) ⟨287657, by rfl⟩ : syracuseStep 383543 = 575315) B575315
theorem B285295 : Blo 167798 285295 := bstep (se 1 (by rfl) ⟨213971, by rfl⟩ : syracuseStep 285295 = 427943) B427943
theorem B383615 : Blo 167798 383615 := bstep (se 1 (by rfl) ⟨287711, by rfl⟩ : syracuseStep 383615 = 575423) B575423
theorem B548383 : Blo 167798 548383 := bstep (se 1 (by rfl) ⟨411287, by rfl⟩ : syracuseStep 548383 = 822575) B822575
theorem B253481 : Blo 167798 253481 := bstep (se 2 (by rfl) ⟨95055, by rfl⟩ : syracuseStep 253481 = 190111) B190111
theorem B253691 : Blo 167798 253691 := bstep (se 1 (by rfl) ⟨190268, by rfl⟩ : syracuseStep 253691 = 380537) B380537
theorem B319295 : Blo 167798 319295 := bstep (se 1 (by rfl) ⟨239471, by rfl⟩ : syracuseStep 319295 = 478943) B478943
theorem B254063 : Blo 167798 254063 := bstep (se 1 (by rfl) ⟨190547, by rfl⟩ : syracuseStep 254063 = 381095) B381095
theorem B1728647 : Blo 167798 1728647 := bstep (se 1 (by rfl) ⟨1296485, by rfl⟩ : syracuseStep 1728647 = 2592971) B2592971
theorem B1728809 : Blo 167798 1728809 := bstep (se 2 (by rfl) ⟨648303, by rfl⟩ : syracuseStep 1728809 = 1296607) B1296607
theorem B549433 : Blo 167798 549433 := bstep (se 2 (by rfl) ⟨206037, by rfl⟩ : syracuseStep 549433 = 412075) B412075
theorem B385919 : Blo 167798 385919 := bstep (se 1 (by rfl) ⟨289439, by rfl⟩ : syracuseStep 385919 = 578879) B578879
theorem B254969 : Blo 167798 254969 := bstep (se 2 (by rfl) ⟨95613, by rfl⟩ : syracuseStep 254969 = 191227) B191227
theorem B517423 : Blo 167798 517423 := bstep (se 1 (by rfl) ⟨388067, by rfl⟩ : syracuseStep 517423 = 776135) B776135
theorem B1303937 : Blo 167798 1303937 := bstep (se 2 (by rfl) ⟨488976, by rfl⟩ : syracuseStep 1303937 = 977953) B977953
theorem B3270455 : Blo 167798 3270455 := bstep (se 1 (by rfl) ⟨2452841, by rfl⟩ : syracuseStep 3270455 = 4905683) B4905683
theorem B616319 : Blo 167798 616319 := bstep (se 1 (by rfl) ⟨462239, by rfl⟩ : syracuseStep 616319 = 924479) B924479
theorem B649403 : Blo 167798 649403 := bstep (se 1 (by rfl) ⟨487052, by rfl⟩ : syracuseStep 649403 = 974105) B974105
theorem B256745 : Blo 167798 256745 := bstep (se 2 (by rfl) ⟨96279, by rfl⟩ : syracuseStep 256745 = 192559) B192559
theorem B191263 : Blo 167798 191263 := bstep (se 1 (by rfl) ⟨143447, by rfl⟩ : syracuseStep 191263 = 286895) B286895
theorem B1436723 : Blo 167798 1436723 := bstep (se 1 (by rfl) ⟨1077542, by rfl⟩ : syracuseStep 1436723 = 2155085) B2155085
theorem B257087 : Blo 167798 257087 := bstep (se 1 (by rfl) ⟨192815, by rfl⟩ : syracuseStep 257087 = 385631) B385631
theorem B257183 : Blo 167798 257183 := bstep (se 1 (by rfl) ⟨192887, by rfl⟩ : syracuseStep 257183 = 385775) B385775
theorem B257513 : Blo 167798 257513 := bstep (se 2 (by rfl) ⟨96567, by rfl⟩ : syracuseStep 257513 = 193135) B193135
theorem B323767 : Blo 167798 323767 := bstep (se 1 (by rfl) ⟨242825, by rfl⟩ : syracuseStep 323767 = 485651) B485651
theorem B291119 : Blo 167798 291119 := bstep (se 1 (by rfl) ⟨218339, by rfl⟩ : syracuseStep 291119 = 436679) B436679
theorem B520609 : Blo 167798 520609 := bstep (se 2 (by rfl) ⟨195228, by rfl⟩ : syracuseStep 520609 = 390457) B390457
theorem B324587 : Blo 167798 324587 := bstep (se 1 (by rfl) ⟨243440, by rfl⟩ : syracuseStep 324587 = 486881) B486881
theorem B1735019 : Blo 167798 1735019 := bstep (se 1 (by rfl) ⟨1301264, by rfl⟩ : syracuseStep 1735019 = 2602529) B2602529
theorem B850337 : Blo 167798 850337 := bstep (se 2 (by rfl) ⟨318876, by rfl⟩ : syracuseStep 850337 = 637753) B637753
theorem B1080287 : Blo 167798 1080287 := bstep (se 1 (by rfl) ⟨810215, by rfl⟩ : syracuseStep 1080287 = 1620431) B1620431
theorem B7865743 : Blo 167798 7865743 := bstep (se 1 (by rfl) ⟨5899307, by rfl⟩ : syracuseStep 7865743 = 11798615) B11798615
theorem B853577 : Blo 167798 853577 := bstep (se 2 (by rfl) ⟨320091, by rfl⟩ : syracuseStep 853577 = 640183) B640183
theorem B689897 : Blo 167798 689897 := bstep (se 2 (by rfl) ⟨258711, by rfl⟩ : syracuseStep 689897 = 517423) B517423
theorem B1280123 : Blo 167798 1280123 := bstep (se 1 (by rfl) ⟨960092, by rfl⟩ : syracuseStep 1280123 = 1920185) B1920185
theorem B429695 : Blo 167798 429695 := bstep (se 1 (by rfl) ⟨322271, by rfl⟩ : syracuseStep 429695 = 644543) B644543
theorem B692135 : Blo 167798 692135 := bstep (se 1 (by rfl) ⟨519101, by rfl⟩ : syracuseStep 692135 = 1038203) B1038203
theorem B168987 : Blo 167798 168987 := bstep (se 1 (by rfl) ⟨126740, by rfl⟩ : syracuseStep 168987 = 253481) B253481
theorem B169127 : Blo 167798 169127 := bstep (se 1 (by rfl) ⟨126845, by rfl⟩ : syracuseStep 169127 = 253691) B253691
theorem B169375 : Blo 167798 169375 := bstep (se 1 (by rfl) ⟨127031, by rfl⟩ : syracuseStep 169375 = 254063) B254063
theorem B1152431 : Blo 167798 1152431 := bstep (se 1 (by rfl) ⟨864323, by rfl⟩ : syracuseStep 1152431 = 1728647) B1728647
theorem B1152539 : Blo 167798 1152539 := bstep (se 1 (by rfl) ⟨864404, by rfl⟩ : syracuseStep 1152539 = 1728809) B1728809
theorem B431689 : Blo 167798 431689 := bstep (se 2 (by rfl) ⟨161883, by rfl⟩ : syracuseStep 431689 = 323767) B323767
theorem B694145 : Blo 167798 694145 := bstep (se 2 (by rfl) ⟨260304, by rfl⟩ : syracuseStep 694145 = 520609) B520609
theorem B169979 : Blo 167798 169979 := bstep (se 1 (by rfl) ⟨127484, by rfl⟩ : syracuseStep 169979 = 254969) B254969
theorem B1644761 : Blo 167798 1644761 := bstep (se 2 (by rfl) ⟨616785, by rfl⟩ : syracuseStep 1644761 = 1233571) B1233571
theorem B727451 : Blo 167798 727451 := bstep (se 1 (by rfl) ⟨545588, by rfl⟩ : syracuseStep 727451 = 1091177) B1091177
theorem B432935 : Blo 167798 432935 := bstep (se 1 (by rfl) ⟨324701, by rfl⟩ : syracuseStep 432935 = 649403) B649403
theorem B171163 : Blo 167798 171163 := bstep (se 1 (by rfl) ⟨128372, by rfl⟩ : syracuseStep 171163 = 256745) B256745
theorem B957815 : Blo 167798 957815 := bstep (se 1 (by rfl) ⟨718361, by rfl⟩ : syracuseStep 957815 = 1436723) B1436723
theorem B171391 : Blo 167798 171391 := bstep (se 1 (by rfl) ⟨128543, by rfl⟩ : syracuseStep 171391 = 257087) B257087
theorem B171455 : Blo 167798 171455 := bstep (se 1 (by rfl) ⟨128591, by rfl⟩ : syracuseStep 171455 = 257183) B257183
theorem B171675 : Blo 167798 171675 := bstep (se 1 (by rfl) ⟨128756, by rfl⟩ : syracuseStep 171675 = 257513) B257513
theorem B2302451 : Blo 167798 2302451 := bstep (se 1 (by rfl) ⟨1726838, by rfl⟩ : syracuseStep 2302451 = 3453677) B3453677
theorem B729911 : Blo 167798 729911 := bstep (se 1 (by rfl) ⟨547433, by rfl⟩ : syracuseStep 729911 = 1094867) B1094867
theorem B1156679 : Blo 167798 1156679 := bstep (se 1 (by rfl) ⟨867509, by rfl⟩ : syracuseStep 1156679 = 1735019) B1735019
theorem B566891 : Blo 167798 566891 := bstep (se 1 (by rfl) ⟨425168, by rfl⟩ : syracuseStep 566891 = 850337) B850337
theorem B731177 : Blo 167798 731177 := bstep (se 2 (by rfl) ⟨274191, by rfl⟩ : syracuseStep 731177 = 548383) B548383
theorem B1944971 : Blo 167798 1944971 := bstep (se 1 (by rfl) ⟨1458728, by rfl⟩ : syracuseStep 1944971 = 2917457) B2917457
theorem B732577 : Blo 167798 732577 := bstep (se 2 (by rfl) ⟨274716, by rfl⟩ : syracuseStep 732577 = 549433) B549433
theorem B144748129 : Blo 167798 144748129 := bstep (se 2 (by rfl) ⟨54280548, by rfl⟩ : syracuseStep 144748129 = 108561097) B108561097
theorem B569321 : Blo 167798 569321 := bstep (se 2 (by rfl) ⟨213495, by rfl⟩ : syracuseStep 569321 = 426991) B426991
theorem B3256307 : Blo 167798 3256307 := bstep (se 1 (by rfl) ⟨2442230, by rfl⟩ : syracuseStep 3256307 = 4884461) B4884461
theorem B1093945 : Blo 167798 1093945 := bstep (se 2 (by rfl) ⟨410229, by rfl⟩ : syracuseStep 1093945 = 820459) B820459
theorem B3486199 : Blo 167798 3486199 := bstep (se 1 (by rfl) ⟨2614649, by rfl⟩ : syracuseStep 3486199 = 5229299) B5229299
theorem B865565 : Blo 167798 865565 := bstep (se 3 (by rfl) ⟨162293, by rfl⟩ : syracuseStep 865565 = 324587) B324587
theorem B1455995 : Blo 167798 1455995 := bstep (se 1 (by rfl) ⟨1091996, by rfl⟩ : syracuseStep 1455995 = 2183993) B2183993
theorem B243919 : Blo 167798 243919 := bstep (se 1 (by rfl) ⟨182939, by rfl⟩ : syracuseStep 243919 = 365879) B365879
theorem B637267 : Blo 167798 637267 := bstep (se 1 (by rfl) ⟨477950, by rfl⟩ : syracuseStep 637267 = 955901) B955901
theorem B867023 : Blo 167798 867023 := bstep (se 1 (by rfl) ⟨650267, by rfl⟩ : syracuseStep 867023 = 1300535) B1300535
theorem B212863 : Blo 167798 212863 := bstep (se 1 (by rfl) ⟨159647, by rfl⟩ : syracuseStep 212863 = 319295) B319295
theorem B2899961 : Blo 167798 2899961 := bstep (se 2 (by rfl) ⟨1087485, by rfl⟩ : syracuseStep 2899961 = 2174971) B2174971
theorem B4145357 : Blo 167798 4145357 := bstep (se 3 (by rfl) ⟨777254, by rfl⟩ : syracuseStep 4145357 = 1554509) B1554509
theorem B967247 : Blo 167798 967247 := bstep (se 1 (by rfl) ⟨725435, by rfl⟩ : syracuseStep 967247 = 1450871) B1450871
theorem B869291 : Blo 167798 869291 := bstep (se 1 (by rfl) ⟨651968, by rfl⟩ : syracuseStep 869291 = 1303937) B1303937
theorem B377855 : Blo 167798 377855 := bstep (se 1 (by rfl) ⟨283391, by rfl⟩ : syracuseStep 377855 = 566783) B566783
theorem B2180303 : Blo 167798 2180303 := bstep (se 1 (by rfl) ⟨1635227, by rfl⟩ : syracuseStep 2180303 = 3270455) B3270455
theorem B410879 : Blo 167798 410879 := bstep (se 1 (by rfl) ⟨308159, by rfl⟩ : syracuseStep 410879 = 616319) B616319
theorem B8309303 : Blo 167798 8309303 := bstep (se 1 (by rfl) ⟨6231977, by rfl⟩ : syracuseStep 8309303 = 12463955) B12463955
theorem B380087 : Blo 167798 380087 := bstep (se 1 (by rfl) ⟨285065, by rfl⟩ : syracuseStep 380087 = 570131) B570131
theorem B380393 : Blo 167798 380393 := bstep (se 2 (by rfl) ⟨142647, by rfl⟩ : syracuseStep 380393 = 285295) B285295
theorem B577367 : Blo 167798 577367 := bstep (se 1 (by rfl) ⟨433025, by rfl⟩ : syracuseStep 577367 = 866051) B866051
theorem B2740243 : Blo 167798 2740243 := bstep (se 1 (by rfl) ⟨2055182, by rfl⟩ : syracuseStep 2740243 = 4110365) B4110365
theorem B382463 : Blo 167798 382463 := bstep (se 1 (by rfl) ⟨286847, by rfl⟩ : syracuseStep 382463 = 573695) B573695
theorem B383003 : Blo 167798 383003 := bstep (se 1 (by rfl) ⟨287252, by rfl⟩ : syracuseStep 383003 = 574505) B574505
theorem B776317 : Blo 167798 776317 := bstep (se 3 (by rfl) ⟨145559, by rfl⟩ : syracuseStep 776317 = 291119) B291119
theorem B547127 : Blo 167798 547127 := bstep (se 1 (by rfl) ⟨410345, by rfl⟩ : syracuseStep 547127 = 820691) B820691
theorem B252239 : Blo 167798 252239 := bstep (se 1 (by rfl) ⟨189179, by rfl⟩ : syracuseStep 252239 = 378359) B378359
theorem B809311 : Blo 167798 809311 := bstep (se 1 (by rfl) ⟨606983, by rfl⟩ : syracuseStep 809311 = 1213967) B1213967
theorem B547229 : Blo 167798 547229 := bstep (se 3 (by rfl) ⟨102605, by rfl⟩ : syracuseStep 547229 = 205211) B205211
theorem B1465199 : Blo 167798 1465199 := bstep (se 1 (by rfl) ⟨1098899, by rfl⟩ : syracuseStep 1465199 = 2197799) B2197799
theorem B253343 : Blo 167798 253343 := bstep (se 1 (by rfl) ⟨190007, by rfl⟩ : syracuseStep 253343 = 380015) B380015
theorem B253511 : Blo 167798 253511 := bstep (se 1 (by rfl) ⟨190133, by rfl⟩ : syracuseStep 253511 = 380267) B380267
theorem B384623 : Blo 167798 384623 := bstep (se 1 (by rfl) ⟨288467, by rfl⟩ : syracuseStep 384623 = 576935) B576935
theorem B385019 : Blo 167798 385019 := bstep (se 1 (by rfl) ⟨288764, by rfl⟩ : syracuseStep 385019 = 577529) B577529
theorem B7463015 : Blo 167798 7463015 := bstep (se 1 (by rfl) ⟨5597261, by rfl⟩ : syracuseStep 7463015 = 11194523) B11194523
theorem B2056391 : Blo 167798 2056391 := bstep (se 1 (by rfl) ⟨1542293, by rfl⟩ : syracuseStep 2056391 = 3084587) B3084587
theorem B385307 : Blo 167798 385307 := bstep (se 1 (by rfl) ⟨288980, by rfl⟩ : syracuseStep 385307 = 577961) B577961
theorem B254279 : Blo 167798 254279 := bstep (se 1 (by rfl) ⟨190709, by rfl⟩ : syracuseStep 254279 = 381419) B381419
theorem B255017 : Blo 167798 255017 := bstep (se 2 (by rfl) ⟨95631, by rfl⟩ : syracuseStep 255017 = 191263) B191263
theorem B255047 : Blo 167798 255047 := bstep (se 1 (by rfl) ⟨191285, by rfl⟩ : syracuseStep 255047 = 382571) B382571
theorem B255131 : Blo 167798 255131 := bstep (se 1 (by rfl) ⟨191348, by rfl⟩ : syracuseStep 255131 = 382697) B382697
theorem B288103 : Blo 167798 288103 := bstep (se 1 (by rfl) ⟨216077, by rfl⟩ : syracuseStep 288103 = 432155) B432155
theorem B255359 : Blo 167798 255359 := bstep (se 1 (by rfl) ⟨191519, by rfl⟩ : syracuseStep 255359 = 383039) B383039
theorem B812539 : Blo 167798 812539 := bstep (se 1 (by rfl) ⟨609404, by rfl⟩ : syracuseStep 812539 = 1218809) B1218809
theorem B419431 : Blo 167798 419431 := bstep (se 1 (by rfl) ⟨314573, by rfl⟩ : syracuseStep 419431 = 629147) B629147
theorem B255695 : Blo 167798 255695 := bstep (se 1 (by rfl) ⟨191771, by rfl⟩ : syracuseStep 255695 = 383543) B383543
theorem B255743 : Blo 167798 255743 := bstep (se 1 (by rfl) ⟨191807, by rfl⟩ : syracuseStep 255743 = 383615) B383615
theorem B616423 : Blo 167798 616423 := bstep (se 1 (by rfl) ⟨462317, by rfl⟩ : syracuseStep 616423 = 924635) B924635
theorem B257279 : Blo 167798 257279 := bstep (se 1 (by rfl) ⟨192959, by rfl⟩ : syracuseStep 257279 = 385919) B385919
theorem B551580299 : Blo 167798 551580299 := bstep (se 1 (by rfl) ⟨413685224, by rfl⟩ : syracuseStep 551580299 = 827370449) B827370449
theorem B489023 : Blo 167798 489023 := bstep (se 1 (by rfl) ⟨366767, by rfl⟩ : syracuseStep 489023 = 733535) B733535
theorem B5863843 : Blo 167798 5863843 := bstep (se 1 (by rfl) ⟨4397882, by rfl⟩ : syracuseStep 5863843 = 8795765) B8795765
theorem B2325671 : Blo 167798 2325671 := bstep (se 1 (by rfl) ⟨1744253, by rfl⟩ : syracuseStep 2325671 = 3488507) B3488507
theorem B720191 : Blo 167798 720191 := bstep (se 1 (by rfl) ⟨540143, by rfl⟩ : syracuseStep 720191 = 1080287) B1080287
theorem B459931 : Blo 167798 459931 := bstep (se 1 (by rfl) ⟨344948, by rfl⟩ : syracuseStep 459931 = 689897) B689897
theorem B853415 : Blo 167798 853415 := bstep (se 1 (by rfl) ⟨640061, by rfl⟩ : syracuseStep 853415 = 1280123) B1280123
theorem B5539535 : Blo 167798 5539535 := bstep (se 1 (by rfl) ⟨4154651, by rfl⟩ : syracuseStep 5539535 = 8309303) B8309303
theorem B10487657 : Blo 167798 10487657 := bstep (se 2 (by rfl) ⟨3932871, by rfl⟩ : syracuseStep 10487657 = 7865743) B7865743
theorem B1083385 : Blo 167798 1083385 := bstep (se 2 (by rfl) ⟨406269, by rfl⟩ : syracuseStep 1083385 = 812539) B812539
theorem B559241 : Blo 167798 559241 := bstep (se 2 (by rfl) ⟨209715, by rfl⟩ : syracuseStep 559241 = 419431) B419431
theorem B461423 : Blo 167798 461423 := bstep (se 1 (by rfl) ⟨346067, by rfl⟩ : syracuseStep 461423 = 692135) B692135
theorem B821897 : Blo 167798 821897 := bstep (se 2 (by rfl) ⟨308211, by rfl⟩ : syracuseStep 821897 = 616423) B616423
theorem B462763 : Blo 167798 462763 := bstep (se 1 (by rfl) ⟨347072, by rfl⟩ : syracuseStep 462763 = 694145) B694145
theorem B364751 : Blo 167798 364751 := bstep (se 1 (by rfl) ⟨273563, by rfl⟩ : syracuseStep 364751 = 547127) B547127
theorem B168159 : Blo 167798 168159 := bstep (se 1 (by rfl) ⟨126119, by rfl⟩ : syracuseStep 168159 = 252239) B252239
theorem B364819 : Blo 167798 364819 := bstep (se 1 (by rfl) ⟨273614, by rfl⟩ : syracuseStep 364819 = 547229) B547229
theorem B168895 : Blo 167798 168895 := bstep (se 1 (by rfl) ⟨126671, by rfl⟩ : syracuseStep 168895 = 253343) B253343
theorem B169007 : Blo 167798 169007 := bstep (se 1 (by rfl) ⟨126755, by rfl⟩ : syracuseStep 169007 = 253511) B253511
theorem B169519 : Blo 167798 169519 := bstep (se 1 (by rfl) ⟨127139, by rfl⟩ : syracuseStep 169519 = 254279) B254279
theorem B170011 : Blo 167798 170011 := bstep (se 1 (by rfl) ⟨127508, by rfl⟩ : syracuseStep 170011 = 255017) B255017
theorem B170031 : Blo 167798 170031 := bstep (se 1 (by rfl) ⟨127523, by rfl⟩ : syracuseStep 170031 = 255047) B255047
theorem B170087 : Blo 167798 170087 := bstep (se 1 (by rfl) ⟨127565, by rfl⟩ : syracuseStep 170087 = 255131) B255131
theorem B170239 : Blo 167798 170239 := bstep (se 1 (by rfl) ⟨127679, by rfl⟩ : syracuseStep 170239 = 255359) B255359
theorem B170463 : Blo 167798 170463 := bstep (se 1 (by rfl) ⟨127847, by rfl⟩ : syracuseStep 170463 = 255695) B255695
theorem B170495 : Blo 167798 170495 := bstep (se 1 (by rfl) ⟨127871, by rfl⟩ : syracuseStep 170495 = 255743) B255743
theorem B171519 : Blo 167798 171519 := bstep (se 1 (by rfl) ⟨128639, by rfl⟩ : syracuseStep 171519 = 257279) B257279
theorem B2170871 : Blo 167798 2170871 := bstep (se 1 (by rfl) ⟨1628153, by rfl⟩ : syracuseStep 2170871 = 3256307) B3256307
theorem B1550447 : Blo 167798 1550447 := bstep (se 1 (by rfl) ⟨1162835, by rfl⟩ : syracuseStep 1550447 = 2325671) B2325671
theorem B2763571 : Blo 167798 2763571 := bstep (se 1 (by rfl) ⟨2072678, by rfl⟩ : syracuseStep 2763571 = 4145357) B4145357
theorem B1453535 : Blo 167798 1453535 := bstep (se 1 (by rfl) ⟨1090151, by rfl⟩ : syracuseStep 1453535 = 2180303) B2180303
theorem B569051 : Blo 167798 569051 := bstep (se 1 (by rfl) ⟨426788, by rfl⟩ : syracuseStep 569051 = 853577) B853577
theorem B1946429 : Blo 167798 1946429 := bstep (se 3 (by rfl) ⟨364955, by rfl⟩ : syracuseStep 1946429 = 729911) B729911
theorem B1095677 : Blo 167798 1095677 := bstep (se 3 (by rfl) ⟨205439, by rfl⟩ : syracuseStep 1095677 = 410879) B410879
theorem B768287 : Blo 167798 768287 := bstep (se 1 (by rfl) ⟨576215, by rfl⟩ : syracuseStep 768287 = 1152431) B1152431
theorem B768359 : Blo 167798 768359 := bstep (se 1 (by rfl) ⟨576269, by rfl⟩ : syracuseStep 768359 = 1152539) B1152539
theorem B1096507 : Blo 167798 1096507 := bstep (se 1 (by rfl) ⟨822380, by rfl⟩ : syracuseStep 1096507 = 1644761) B1644761
theorem B638543 : Blo 167798 638543 := bstep (se 1 (by rfl) ⟨478907, by rfl⟩ : syracuseStep 638543 = 957815) B957815
theorem B3653657 : Blo 167798 3653657 := bstep (se 2 (by rfl) ⟨1370121, by rfl⟩ : syracuseStep 3653657 = 2740243) B2740243
theorem B1458593 : Blo 167798 1458593 := bstep (se 2 (by rfl) ⟨546972, by rfl⟩ : syracuseStep 1458593 = 1093945) B1093945
theorem B771119 : Blo 167798 771119 := bstep (se 1 (by rfl) ⟨578339, by rfl⟩ : syracuseStep 771119 = 1156679) B1156679
theorem B377927 : Blo 167798 377927 := bstep (se 1 (by rfl) ⟨283445, by rfl⟩ : syracuseStep 377927 = 566891) B566891
theorem B575585 : Blo 167798 575585 := bstep (se 2 (by rfl) ⟨215844, by rfl⟩ : syracuseStep 575585 = 431689) B431689
theorem B1296647 : Blo 167798 1296647 := bstep (se 1 (by rfl) ⟨972485, by rfl⟩ : syracuseStep 1296647 = 1944971) B1944971
theorem B379547 : Blo 167798 379547 := bstep (se 1 (by rfl) ⟨284660, by rfl⟩ : syracuseStep 379547 = 569321) B569321
theorem B1035089 : Blo 167798 1035089 := bstep (se 2 (by rfl) ⟨388158, by rfl⟩ : syracuseStep 1035089 = 776317) B776317
theorem B7818457 : Blo 167798 7818457 := bstep (se 2 (by rfl) ⟨2931921, by rfl⟩ : syracuseStep 7818457 = 5863843) B5863843
theorem B577043 : Blo 167798 577043 := bstep (se 1 (by rfl) ⟨432782, by rfl⟩ : syracuseStep 577043 = 865565) B865565
theorem B970663 : Blo 167798 970663 := bstep (se 1 (by rfl) ⟨727997, by rfl⟩ : syracuseStep 970663 = 1455995) B1455995
theorem B578015 : Blo 167798 578015 := bstep (se 1 (by rfl) ⟨433511, by rfl⟩ : syracuseStep 578015 = 867023) B867023
theorem B480127 : Blo 167798 480127 := bstep (se 1 (by rfl) ⟨360095, by rfl⟩ : syracuseStep 480127 = 720191) B720191
theorem B283817 : Blo 167798 283817 := bstep (se 2 (by rfl) ⟨106431, by rfl⟩ : syracuseStep 283817 = 212863) B212863
theorem B644831 : Blo 167798 644831 := bstep (se 1 (by rfl) ⟨483623, by rfl⟩ : syracuseStep 644831 = 967247) B967247
theorem B579527 : Blo 167798 579527 := bstep (se 1 (by rfl) ⟨434645, by rfl⟩ : syracuseStep 579527 = 869291) B869291
theorem B251903 : Blo 167798 251903 := bstep (se 1 (by rfl) ⟨188927, by rfl⟩ : syracuseStep 251903 = 377855) B377855
theorem B384137 : Blo 167798 384137 := bstep (se 2 (by rfl) ⟨144051, by rfl⟩ : syracuseStep 384137 = 288103) B288103
theorem B253391 : Blo 167798 253391 := bstep (se 1 (by rfl) ⟨190043, by rfl⟩ : syracuseStep 253391 = 380087) B380087
theorem B253595 : Blo 167798 253595 := bstep (se 1 (by rfl) ⟨190196, by rfl⟩ : syracuseStep 253595 = 380393) B380393
theorem B286463 : Blo 167798 286463 := bstep (se 1 (by rfl) ⟨214847, by rfl⟩ : syracuseStep 286463 = 429695) B429695
theorem B384911 : Blo 167798 384911 := bstep (se 1 (by rfl) ⟨288683, by rfl⟩ : syracuseStep 384911 = 577367) B577367
theorem B254975 : Blo 167798 254975 := bstep (se 1 (by rfl) ⟨191231, by rfl⟩ : syracuseStep 254975 = 382463) B382463
theorem B255335 : Blo 167798 255335 := bstep (se 1 (by rfl) ⟨191501, by rfl⟩ : syracuseStep 255335 = 383003) B383003
theorem B484967 : Blo 167798 484967 := bstep (se 1 (by rfl) ⟨363725, by rfl⟩ : syracuseStep 484967 = 727451) B727451
theorem B288623 : Blo 167798 288623 := bstep (se 1 (by rfl) ⟨216467, by rfl⟩ : syracuseStep 288623 = 432935) B432935
theorem B976769 : Blo 167798 976769 := bstep (se 2 (by rfl) ⟨366288, by rfl⟩ : syracuseStep 976769 = 732577) B732577
theorem B976799 : Blo 167798 976799 := bstep (se 1 (by rfl) ⟨732599, by rfl⟩ : syracuseStep 976799 = 1465199) B1465199
theorem B192997505 : Blo 167798 192997505 := bstep (se 2 (by rfl) ⟨72374064, by rfl⟩ : syracuseStep 192997505 = 144748129) B144748129
theorem B256415 : Blo 167798 256415 := bstep (se 1 (by rfl) ⟨192311, by rfl⟩ : syracuseStep 256415 = 384623) B384623
theorem B256679 : Blo 167798 256679 := bstep (se 1 (by rfl) ⟨192509, by rfl⟩ : syracuseStep 256679 = 385019) B385019
theorem B4975343 : Blo 167798 4975343 := bstep (se 1 (by rfl) ⟨3731507, by rfl⟩ : syracuseStep 4975343 = 7463015) B7463015
theorem B1370927 : Blo 167798 1370927 := bstep (se 1 (by rfl) ⟨1028195, by rfl⟩ : syracuseStep 1370927 = 2056391) B2056391
theorem B256871 : Blo 167798 256871 := bstep (se 1 (by rfl) ⟨192653, by rfl⟩ : syracuseStep 256871 = 385307) B385307
theorem B1534967 : Blo 167798 1534967 := bstep (se 1 (by rfl) ⟨1151225, by rfl⟩ : syracuseStep 1534967 = 2302451) B2302451
theorem B4648265 : Blo 167798 4648265 := bstep (se 2 (by rfl) ⟨1743099, by rfl⟩ : syracuseStep 4648265 = 3486199) B3486199
theorem B487451 : Blo 167798 487451 := bstep (se 1 (by rfl) ⟨365588, by rfl⟩ : syracuseStep 487451 = 731177) B731177
theorem B325225 : Blo 167798 325225 := bstep (se 2 (by rfl) ⟨121959, by rfl⟩ : syracuseStep 325225 = 243919) B243919
theorem B367720199 : Blo 167798 367720199 := bstep (se 1 (by rfl) ⟨275790149, by rfl⟩ : syracuseStep 367720199 = 551580299) B551580299
theorem B849689 : Blo 167798 849689 := bstep (se 2 (by rfl) ⟨318633, by rfl⟩ : syracuseStep 849689 = 637267) B637267
theorem B1079081 : Blo 167798 1079081 := bstep (se 2 (by rfl) ⟨404655, by rfl⟩ : syracuseStep 1079081 = 809311) B809311
theorem B326015 : Blo 167798 326015 := bstep (se 1 (by rfl) ⟨244511, by rfl⟩ : syracuseStep 326015 = 489023) B489023
theorem B1933307 : Blo 167798 1933307 := bstep (se 1 (by rfl) ⟨1449980, by rfl⟩ : syracuseStep 1933307 = 2899961) B2899961
theorem B690059 : Blo 167798 690059 := bstep (se 1 (by rfl) ⟨517544, by rfl⟩ : syracuseStep 690059 = 1035089) B1035089
theorem B1444513 : Blo 167798 1444513 := bstep (se 2 (by rfl) ⟨541692, by rfl⟩ : syracuseStep 1444513 = 1083385) B1083385
theorem B429887 : Blo 167798 429887 := bstep (se 1 (by rfl) ⟨322415, by rfl⟩ : syracuseStep 429887 = 644831) B644831
theorem B167935 : Blo 167798 167935 := bstep (se 1 (by rfl) ⟨125951, by rfl⟩ : syracuseStep 167935 = 251903) B251903
theorem B10424609 : Blo 167798 10424609 := bstep (se 2 (by rfl) ⟨3909228, by rfl⟩ : syracuseStep 10424609 = 7818457) B7818457
theorem B168927 : Blo 167798 168927 := bstep (se 1 (by rfl) ⟨126695, by rfl⟩ : syracuseStep 168927 = 253391) B253391
theorem B169063 : Blo 167798 169063 := bstep (se 1 (by rfl) ⟨126797, by rfl⟩ : syracuseStep 169063 = 253595) B253595
theorem B1447247 : Blo 167798 1447247 := bstep (se 1 (by rfl) ⟨1085435, by rfl⟩ : syracuseStep 1447247 = 2170871) B2170871
theorem B514660013 : Blo 167798 514660013 := bstep (se 3 (by rfl) ⟨96498752, by rfl⟩ : syracuseStep 514660013 = 192997505) B192997505
theorem B169983 : Blo 167798 169983 := bstep (se 1 (by rfl) ⟨127487, by rfl⟩ : syracuseStep 169983 = 254975) B254975
theorem B170223 : Blo 167798 170223 := bstep (se 1 (by rfl) ⟨127667, by rfl⟩ : syracuseStep 170223 = 255335) B255335
theorem B170943 : Blo 167798 170943 := bstep (se 1 (by rfl) ⟨128207, by rfl⟩ : syracuseStep 170943 = 256415) B256415
theorem B171119 : Blo 167798 171119 := bstep (se 1 (by rfl) ⟨128339, by rfl⟩ : syracuseStep 171119 = 256679) B256679
theorem B3316895 : Blo 167798 3316895 := bstep (se 1 (by rfl) ⟨2487671, by rfl⟩ : syracuseStep 3316895 = 4975343) B4975343
theorem B171247 : Blo 167798 171247 := bstep (se 1 (by rfl) ⟨128435, by rfl⟩ : syracuseStep 171247 = 256871) B256871
theorem B1023311 : Blo 167798 1023311 := bstep (se 1 (by rfl) ⟨767483, by rfl⟩ : syracuseStep 1023311 = 1534967) B1534967
theorem B433633 : Blo 167798 433633 := bstep (se 2 (by rfl) ⟨162612, by rfl⟩ : syracuseStep 433633 = 325225) B325225
theorem B245146799 : Blo 167798 245146799 := bstep (se 1 (by rfl) ⟨183860099, by rfl⟩ : syracuseStep 245146799 = 367720199) B367720199
theorem B566459 : Blo 167798 566459 := bstep (se 1 (by rfl) ⟨424844, by rfl⟩ : syracuseStep 566459 = 849689) B849689
theorem B730451 : Blo 167798 730451 := bstep (se 1 (by rfl) ⟨547838, by rfl⟩ : syracuseStep 730451 = 1095677) B1095677
theorem B1288871 : Blo 167798 1288871 := bstep (se 1 (by rfl) ⟨966653, by rfl⟩ : syracuseStep 1288871 = 1933307) B1933307
theorem B2435771 : Blo 167798 2435771 := bstep (se 1 (by rfl) ⟨1826828, by rfl⟩ : syracuseStep 2435771 = 3653657) B3653657
theorem B568943 : Blo 167798 568943 := bstep (se 1 (by rfl) ⟨426707, by rfl⟩ : syracuseStep 568943 = 853415) B853415
theorem B6991771 : Blo 167798 6991771 := bstep (se 1 (by rfl) ⟨5243828, by rfl⟩ : syracuseStep 6991771 = 10487657) B10487657
theorem B372827 : Blo 167798 372827 := bstep (se 1 (by rfl) ⟨279620, by rfl⟩ : syracuseStep 372827 = 559241) B559241
theorem B864431 : Blo 167798 864431 := bstep (se 1 (by rfl) ⟨648323, by rfl⟩ : syracuseStep 864431 = 1296647) B1296647
theorem B243167 : Blo 167798 243167 := bstep (se 1 (by rfl) ⟨182375, by rfl⟩ : syracuseStep 243167 = 364751) B364751
theorem B3684761 : Blo 167798 3684761 := bstep (se 2 (by rfl) ⟨1381785, by rfl⟩ : syracuseStep 3684761 = 2763571) B2763571
theorem B1293245 : Blo 167798 1293245 := bstep (se 3 (by rfl) ⟨242483, by rfl⟩ : syracuseStep 1293245 = 484967) B484967
theorem B1294217 : Blo 167798 1294217 := bstep (se 2 (by rfl) ⟨485331, by rfl⟩ : syracuseStep 1294217 = 970663) B970663
theorem B640169 : Blo 167798 640169 := bstep (se 2 (by rfl) ⟨240063, by rfl⟩ : syracuseStep 640169 = 480127) B480127
theorem B1033631 : Blo 167798 1033631 := bstep (se 1 (by rfl) ⟨775223, by rfl⟩ : syracuseStep 1033631 = 1550447) B1550447
theorem B1230461 : Blo 167798 1230461 := bstep (se 3 (by rfl) ⟨230711, by rfl⟩ : syracuseStep 1230461 = 461423) B461423
theorem B3098843 : Blo 167798 3098843 := bstep (se 1 (by rfl) ⟨2324132, by rfl⟩ : syracuseStep 3098843 = 4648265) B4648265
theorem B969023 : Blo 167798 969023 := bstep (se 1 (by rfl) ⟨726767, by rfl⟩ : syracuseStep 969023 = 1453535) B1453535
theorem B379367 : Blo 167798 379367 := bstep (se 1 (by rfl) ⟨284525, by rfl⟩ : syracuseStep 379367 = 569051) B569051
theorem B1297619 : Blo 167798 1297619 := bstep (se 1 (by rfl) ⟨973214, by rfl⟩ : syracuseStep 1297619 = 1946429) B1946429
theorem B1462009 : Blo 167798 1462009 := bstep (se 2 (by rfl) ⟨548253, by rfl⟩ : syracuseStep 1462009 = 1096507) B1096507
theorem B512191 : Blo 167798 512191 := bstep (se 1 (by rfl) ⟨384143, by rfl⟩ : syracuseStep 512191 = 768287) B768287
theorem B512239 : Blo 167798 512239 := bstep (se 1 (by rfl) ⟨384179, by rfl⟩ : syracuseStep 512239 = 768359) B768359
theorem B217343 : Blo 167798 217343 := bstep (se 1 (by rfl) ⟨163007, by rfl⟩ : syracuseStep 217343 = 326015) B326015
theorem B972395 : Blo 167798 972395 := bstep (se 1 (by rfl) ⟨729296, by rfl⟩ : syracuseStep 972395 = 1458593) B1458593
theorem B514079 : Blo 167798 514079 := bstep (se 1 (by rfl) ⟨385559, by rfl⟩ : syracuseStep 514079 = 771119) B771119
theorem B251951 : Blo 167798 251951 := bstep (se 1 (by rfl) ⟨188963, by rfl⟩ : syracuseStep 251951 = 377927) B377927
theorem B3693023 : Blo 167798 3693023 := bstep (se 1 (by rfl) ⟨2769767, by rfl⟩ : syracuseStep 3693023 = 5539535) B5539535
theorem B383723 : Blo 167798 383723 := bstep (se 1 (by rfl) ⟨287792, by rfl⟩ : syracuseStep 383723 = 575585) B575585
theorem B613241 : Blo 167798 613241 := bstep (se 2 (by rfl) ⟨229965, by rfl⟩ : syracuseStep 613241 = 459931) B459931
theorem B547931 : Blo 167798 547931 := bstep (se 1 (by rfl) ⟨410948, by rfl⟩ : syracuseStep 547931 = 821897) B821897
theorem B253031 : Blo 167798 253031 := bstep (se 1 (by rfl) ⟨189773, by rfl⟩ : syracuseStep 253031 = 379547) B379547
theorem B384695 : Blo 167798 384695 := bstep (se 1 (by rfl) ⟨288521, by rfl⟩ : syracuseStep 384695 = 577043) B577043
theorem B385343 : Blo 167798 385343 := bstep (se 1 (by rfl) ⟨289007, by rfl⟩ : syracuseStep 385343 = 578015) B578015
theorem B189211 : Blo 167798 189211 := bstep (se 1 (by rfl) ⟨141908, by rfl⟩ : syracuseStep 189211 = 283817) B283817
theorem B386351 : Blo 167798 386351 := bstep (se 1 (by rfl) ⟨289763, by rfl⟩ : syracuseStep 386351 = 579527) B579527
theorem B256091 : Blo 167798 256091 := bstep (se 1 (by rfl) ⟨192068, by rfl⟩ : syracuseStep 256091 = 384137) B384137
theorem B190975 : Blo 167798 190975 := bstep (se 1 (by rfl) ⟨143231, by rfl⟩ : syracuseStep 190975 = 286463) B286463
theorem B617017 : Blo 167798 617017 := bstep (se 2 (by rfl) ⟨231381, by rfl⟩ : syracuseStep 617017 = 462763) B462763
theorem B256607 : Blo 167798 256607 := bstep (se 1 (by rfl) ⟨192455, by rfl⟩ : syracuseStep 256607 = 384911) B384911
theorem B486425 : Blo 167798 486425 := bstep (se 2 (by rfl) ⟨182409, by rfl⟩ : syracuseStep 486425 = 364819) B364819
theorem B192415 : Blo 167798 192415 := bstep (se 1 (by rfl) ⟨144311, by rfl⟩ : syracuseStep 192415 = 288623) B288623
theorem B651179 : Blo 167798 651179 := bstep (se 1 (by rfl) ⟨488384, by rfl⟩ : syracuseStep 651179 = 976769) B976769
theorem B651199 : Blo 167798 651199 := bstep (se 1 (by rfl) ⟨488399, by rfl⟩ : syracuseStep 651199 = 976799) B976799
theorem B913951 : Blo 167798 913951 := bstep (se 1 (by rfl) ⟨685463, by rfl⟩ : syracuseStep 913951 = 1370927) B1370927
theorem B324967 : Blo 167798 324967 := bstep (se 1 (by rfl) ⟨243725, by rfl⟩ : syracuseStep 324967 = 487451) B487451
theorem B719387 : Blo 167798 719387 := bstep (se 1 (by rfl) ⟨539540, by rfl⟩ : syracuseStep 719387 = 1079081) B1079081
theorem B425695 : Blo 167798 425695 := bstep (se 1 (by rfl) ⟨319271, by rfl⟩ : syracuseStep 425695 = 638543) B638543
theorem B426779 : Blo 167798 426779 := bstep (se 1 (by rfl) ⟨320084, by rfl⟩ : syracuseStep 426779 = 640169) B640169
theorem B689087 : Blo 167798 689087 := bstep (se 1 (by rfl) ⟨516815, by rfl⟩ : syracuseStep 689087 = 1033631) B1033631
theorem B820307 : Blo 167798 820307 := bstep (se 1 (by rfl) ⟨615230, by rfl⟩ : syracuseStep 820307 = 1230461) B1230461
theorem B2065895 : Blo 167798 2065895 := bstep (se 1 (by rfl) ⟨1549421, by rfl⟩ : syracuseStep 2065895 = 3098843) B3098843
theorem B6949739 : Blo 167798 6949739 := bstep (se 1 (by rfl) ⟨5212304, by rfl⟩ : syracuseStep 6949739 = 10424609) B10424609
theorem B822689 : Blo 167798 822689 := bstep (se 2 (by rfl) ⟨308508, by rfl⟩ : syracuseStep 822689 = 617017) B617017
theorem B167967 : Blo 167798 167967 := bstep (se 1 (by rfl) ⟨125975, by rfl⟩ : syracuseStep 167967 = 251951) B251951
theorem B2462015 : Blo 167798 2462015 := bstep (se 1 (by rfl) ⟨1846511, by rfl⟩ : syracuseStep 2462015 = 3693023) B3693023
theorem B168687 : Blo 167798 168687 := bstep (se 1 (by rfl) ⟨126515, by rfl⟩ : syracuseStep 168687 = 253031) B253031
theorem B1840157 : Blo 167798 1840157 := bstep (se 3 (by rfl) ⟨345029, by rfl⟩ : syracuseStep 1840157 = 690059) B690059
theorem B1218601 : Blo 167798 1218601 := bstep (se 2 (by rfl) ⟨456975, by rfl⟩ : syracuseStep 1218601 = 913951) B913951
theorem B170727 : Blo 167798 170727 := bstep (se 1 (by rfl) ⟨128045, by rfl⟩ : syracuseStep 170727 = 256091) B256091
theorem B171071 : Blo 167798 171071 := bstep (se 1 (by rfl) ⟨128303, by rfl⟩ : syracuseStep 171071 = 256607) B256607
theorem B859247 : Blo 167798 859247 := bstep (se 1 (by rfl) ⟨644435, by rfl⟩ : syracuseStep 859247 = 1288871) B1288871
theorem B433289 : Blo 167798 433289 := bstep (se 2 (by rfl) ⟨162483, by rfl⟩ : syracuseStep 433289 = 324967) B324967
theorem B6495389 : Blo 167798 6495389 := bstep (se 3 (by rfl) ⟨1217885, by rfl⟩ : syracuseStep 6495389 = 2435771) B2435771
theorem B434119 : Blo 167798 434119 := bstep (se 1 (by rfl) ⟨325589, by rfl⟩ : syracuseStep 434119 = 651179) B651179
theorem B2728829 : Blo 167798 2728829 := bstep (se 3 (by rfl) ⟨511655, by rfl⟩ : syracuseStep 2728829 = 1023311) B1023311
theorem B862163 : Blo 167798 862163 := bstep (se 1 (by rfl) ⟨646622, by rfl⟩ : syracuseStep 862163 = 1293245) B1293245
theorem B567593 : Blo 167798 567593 := bstep (se 2 (by rfl) ⟨212847, by rfl⟩ : syracuseStep 567593 = 425695) B425695
theorem B862811 : Blo 167798 862811 := bstep (se 1 (by rfl) ⟨647108, by rfl⟩ : syracuseStep 862811 = 1294217) B1294217
theorem B865079 : Blo 167798 865079 := bstep (se 1 (by rfl) ⟨648809, by rfl⟩ : syracuseStep 865079 = 1297619) B1297619
theorem B964831 : Blo 167798 964831 := bstep (se 1 (by rfl) ⟨723623, by rfl⟩ : syracuseStep 964831 = 1447247) B1447247
theorem B342719 : Blo 167798 342719 := bstep (se 1 (by rfl) ⟨257039, by rfl⟩ : syracuseStep 342719 = 514079) B514079
theorem B408827 : Blo 167798 408827 := bstep (se 1 (by rfl) ⟨306620, by rfl⟩ : syracuseStep 408827 = 613241) B613241
theorem B2211263 : Blo 167798 2211263 := bstep (se 1 (by rfl) ⟨1658447, by rfl⟩ : syracuseStep 2211263 = 3316895) B3316895
theorem B1949345 : Blo 167798 1949345 := bstep (se 2 (by rfl) ⟨731004, by rfl⟩ : syracuseStep 1949345 = 1462009) B1462009
theorem B9322361 : Blo 167798 9322361 := bstep (se 2 (by rfl) ⟨3495885, by rfl⟩ : syracuseStep 9322361 = 6991771) B6991771
theorem B868265 : Blo 167798 868265 := bstep (se 2 (by rfl) ⟨325599, by rfl⟩ : syracuseStep 868265 = 651199) B651199
theorem B163431199 : Blo 167798 163431199 := bstep (se 1 (by rfl) ⟨122573399, by rfl⟩ : syracuseStep 163431199 = 245146799) B245146799
theorem B377639 : Blo 167798 377639 := bstep (se 1 (by rfl) ⟨283229, by rfl⟩ : syracuseStep 377639 = 566459) B566459
theorem B379295 : Blo 167798 379295 := bstep (se 1 (by rfl) ⟨284471, by rfl⟩ : syracuseStep 379295 = 568943) B568943
theorem B248551 : Blo 167798 248551 := bstep (se 1 (by rfl) ⟨186413, by rfl⟩ : syracuseStep 248551 = 372827) B372827
theorem B1297133 : Blo 167798 1297133 := bstep (se 3 (by rfl) ⟨243212, by rfl⟩ : syracuseStep 1297133 = 486425) B486425
theorem B576287 : Blo 167798 576287 := bstep (se 1 (by rfl) ⟨432215, by rfl⟩ : syracuseStep 576287 = 864431) B864431
theorem B1461149 : Blo 167798 1461149 := bstep (se 3 (by rfl) ⟨273965, by rfl⟩ : syracuseStep 1461149 = 547931) B547931
theorem B479591 : Blo 167798 479591 := bstep (se 1 (by rfl) ⟨359693, by rfl⟩ : syracuseStep 479591 = 719387) B719387
theorem B578177 : Blo 167798 578177 := bstep (se 2 (by rfl) ⟨216816, by rfl⟩ : syracuseStep 578177 = 433633) B433633
theorem B579581 : Blo 167798 579581 := bstep (se 3 (by rfl) ⟨108671, by rfl⟩ : syracuseStep 579581 = 217343) B217343
theorem B252281 : Blo 167798 252281 := bstep (se 2 (by rfl) ⟨94605, by rfl⟩ : syracuseStep 252281 = 189211) B189211
theorem B646015 : Blo 167798 646015 := bstep (se 1 (by rfl) ⟨484511, by rfl⟩ : syracuseStep 646015 = 969023) B969023
theorem B252911 : Blo 167798 252911 := bstep (se 1 (by rfl) ⟨189683, by rfl⟩ : syracuseStep 252911 = 379367) B379367
theorem B286591 : Blo 167798 286591 := bstep (se 1 (by rfl) ⟨214943, by rfl⟩ : syracuseStep 286591 = 429887) B429887
theorem B254633 : Blo 167798 254633 := bstep (se 2 (by rfl) ⟨95487, by rfl⟩ : syracuseStep 254633 = 190975) B190975
theorem B1926017 : Blo 167798 1926017 := bstep (se 2 (by rfl) ⟨722256, by rfl⟩ : syracuseStep 1926017 = 1444513) B1444513
theorem B648263 : Blo 167798 648263 := bstep (se 1 (by rfl) ⟨486197, by rfl⟩ : syracuseStep 648263 = 972395) B972395
theorem B343106675 : Blo 167798 343106675 := bstep (se 1 (by rfl) ⟨257330006, by rfl⟩ : syracuseStep 343106675 = 514660013) B514660013
theorem B648445 : Blo 167798 648445 := bstep (se 3 (by rfl) ⟨121583, by rfl⟩ : syracuseStep 648445 = 243167) B243167
theorem B255815 : Blo 167798 255815 := bstep (se 1 (by rfl) ⟨191861, by rfl⟩ : syracuseStep 255815 = 383723) B383723
theorem B256463 : Blo 167798 256463 := bstep (se 1 (by rfl) ⟨192347, by rfl⟩ : syracuseStep 256463 = 384695) B384695
theorem B256553 : Blo 167798 256553 := bstep (se 2 (by rfl) ⟨96207, by rfl⟩ : syracuseStep 256553 = 192415) B192415
theorem B256895 : Blo 167798 256895 := bstep (se 1 (by rfl) ⟨192671, by rfl⟩ : syracuseStep 256895 = 385343) B385343
theorem B682921 : Blo 167798 682921 := bstep (se 2 (by rfl) ⟨256095, by rfl⟩ : syracuseStep 682921 = 512191) B512191
theorem B682985 : Blo 167798 682985 := bstep (se 2 (by rfl) ⟨256119, by rfl⟩ : syracuseStep 682985 = 512239) B512239
theorem B257567 : Blo 167798 257567 := bstep (se 1 (by rfl) ⟨193175, by rfl⟩ : syracuseStep 257567 = 386351) B386351
theorem B486967 : Blo 167798 486967 := bstep (se 1 (by rfl) ⟨365225, by rfl⟩ : syracuseStep 486967 = 730451) B730451
theorem B2456507 : Blo 167798 2456507 := bstep (se 1 (by rfl) ⟨1842380, by rfl⟩ : syracuseStep 2456507 = 3684761) B3684761
theorem B459391 : Blo 167798 459391 := bstep (se 1 (by rfl) ⟨344543, by rfl⟩ : syracuseStep 459391 = 689087) B689087
theorem B1377263 : Blo 167798 1377263 := bstep (se 1 (by rfl) ⟨1032947, by rfl⟩ : syracuseStep 1377263 = 2065895) B2065895
theorem B217908265 : Blo 167798 217908265 := bstep (se 2 (by rfl) ⟨81715599, by rfl⟩ : syracuseStep 217908265 = 163431199) B163431199
theorem B1641343 : Blo 167798 1641343 := bstep (se 1 (by rfl) ⟨1231007, by rfl⟩ : syracuseStep 1641343 = 2462015) B2462015
theorem B168187 : Blo 167798 168187 := bstep (se 1 (by rfl) ⟨126140, by rfl⟩ : syracuseStep 168187 = 252281) B252281
theorem B168607 : Blo 167798 168607 := bstep (se 1 (by rfl) ⟨126455, by rfl⟩ : syracuseStep 168607 = 252911) B252911
theorem B4330259 : Blo 167798 4330259 := bstep (se 1 (by rfl) ⟨3247694, by rfl⟩ : syracuseStep 4330259 = 6495389) B6495389
theorem B3642245 : Blo 167798 3642245 := bstep (se 4 (by rfl) ⟨341460, by rfl⟩ : syracuseStep 3642245 = 682921) B682921
theorem B169755 : Blo 167798 169755 := bstep (se 1 (by rfl) ⟨127316, by rfl⟩ : syracuseStep 169755 = 254633) B254633
theorem B1284011 : Blo 167798 1284011 := bstep (se 1 (by rfl) ⟨963008, by rfl⟩ : syracuseStep 1284011 = 1926017) B1926017
theorem B432175 : Blo 167798 432175 := bstep (se 1 (by rfl) ⟨324131, by rfl⟩ : syracuseStep 432175 = 648263) B648263
theorem B170543 : Blo 167798 170543 := bstep (se 1 (by rfl) ⟨127907, by rfl⟩ : syracuseStep 170543 = 255815) B255815
theorem B170975 : Blo 167798 170975 := bstep (se 1 (by rfl) ⟨128231, by rfl⟩ : syracuseStep 170975 = 256463) B256463
theorem B171035 : Blo 167798 171035 := bstep (se 1 (by rfl) ⟨128276, by rfl⟩ : syracuseStep 171035 = 256553) B256553
theorem B171263 : Blo 167798 171263 := bstep (se 1 (by rfl) ⟨128447, by rfl⟩ : syracuseStep 171263 = 256895) B256895
theorem B171711 : Blo 167798 171711 := bstep (se 1 (by rfl) ⟨128783, by rfl⟩ : syracuseStep 171711 = 257567) B257567
theorem B1286441 : Blo 167798 1286441 := bstep (se 2 (by rfl) ⟨482415, by rfl⟩ : syracuseStep 1286441 = 964831) B964831
theorem B1090205 : Blo 167798 1090205 := bstep (se 3 (by rfl) ⟨204413, by rfl⟩ : syracuseStep 1090205 = 408827) B408827
theorem B861353 : Blo 167798 861353 := bstep (se 2 (by rfl) ⟨323007, by rfl⟩ : syracuseStep 861353 = 646015) B646015
theorem B864593 : Blo 167798 864593 := bstep (se 2 (by rfl) ⟨324222, by rfl⟩ : syracuseStep 864593 = 648445) B648445
theorem B864755 : Blo 167798 864755 := bstep (se 1 (by rfl) ⟨648566, by rfl⟩ : syracuseStep 864755 = 1297133) B1297133
theorem B4633159 : Blo 167798 4633159 := bstep (se 1 (by rfl) ⟨3474869, by rfl⟩ : syracuseStep 4633159 = 6949739) B6949739
theorem B1226771 : Blo 167798 1226771 := bstep (se 1 (by rfl) ⟨920078, by rfl⟩ : syracuseStep 1226771 = 1840157) B1840157
theorem B1325605 : Blo 167798 1325605 := bstep (se 4 (by rfl) ⟨124275, by rfl⟩ : syracuseStep 1325605 = 248551) B248551
theorem B572831 : Blo 167798 572831 := bstep (se 1 (by rfl) ⟨429623, by rfl⟩ : syracuseStep 572831 = 859247) B859247
theorem B1819219 : Blo 167798 1819219 := bstep (se 1 (by rfl) ⟨1364414, by rfl⟩ : syracuseStep 1819219 = 2728829) B2728829
theorem B228737783 : Blo 167798 228737783 := bstep (se 1 (by rfl) ⟨171553337, by rfl⟩ : syracuseStep 228737783 = 343106675) B343106675
theorem B574775 : Blo 167798 574775 := bstep (se 1 (by rfl) ⟨431081, by rfl⟩ : syracuseStep 574775 = 862163) B862163
theorem B378395 : Blo 167798 378395 := bstep (se 1 (by rfl) ⟨283796, by rfl⟩ : syracuseStep 378395 = 567593) B567593
theorem B575207 : Blo 167798 575207 := bstep (se 1 (by rfl) ⟨431405, by rfl⟩ : syracuseStep 575207 = 862811) B862811
theorem B1821293 : Blo 167798 1821293 := bstep (se 3 (by rfl) ⟨341492, by rfl⟩ : syracuseStep 1821293 = 682985) B682985
theorem B1624801 : Blo 167798 1624801 := bstep (se 2 (by rfl) ⟨609300, by rfl⟩ : syracuseStep 1624801 = 1218601) B1218601
theorem B576719 : Blo 167798 576719 := bstep (se 1 (by rfl) ⟨432539, by rfl⟩ : syracuseStep 576719 = 865079) B865079
theorem B1299563 : Blo 167798 1299563 := bstep (se 1 (by rfl) ⟨974672, by rfl⟩ : syracuseStep 1299563 = 1949345) B1949345
theorem B382121 : Blo 167798 382121 := bstep (se 2 (by rfl) ⟨143295, by rfl⟩ : syracuseStep 382121 = 286591) B286591
theorem B6214907 : Blo 167798 6214907 := bstep (se 1 (by rfl) ⟨4661180, by rfl⟩ : syracuseStep 6214907 = 9322361) B9322361
theorem B578825 : Blo 167798 578825 := bstep (se 2 (by rfl) ⟨217059, by rfl⟩ : syracuseStep 578825 = 434119) B434119
theorem B578843 : Blo 167798 578843 := bstep (se 1 (by rfl) ⟨434132, by rfl⟩ : syracuseStep 578843 = 868265) B868265
theorem B284519 : Blo 167798 284519 := bstep (se 1 (by rfl) ⟨213389, by rfl⟩ : syracuseStep 284519 = 426779) B426779
theorem B251759 : Blo 167798 251759 := bstep (se 1 (by rfl) ⟨188819, by rfl⟩ : syracuseStep 251759 = 377639) B377639
theorem B546871 : Blo 167798 546871 := bstep (se 1 (by rfl) ⟨410153, by rfl⟩ : syracuseStep 546871 = 820307) B820307
theorem B252863 : Blo 167798 252863 := bstep (se 1 (by rfl) ⟨189647, by rfl⟩ : syracuseStep 252863 = 379295) B379295
theorem B384191 : Blo 167798 384191 := bstep (se 1 (by rfl) ⟨288143, by rfl⟩ : syracuseStep 384191 = 576287) B576287
theorem B974099 : Blo 167798 974099 := bstep (se 1 (by rfl) ⟨730574, by rfl⟩ : syracuseStep 974099 = 1461149) B1461149
theorem B548459 : Blo 167798 548459 := bstep (se 1 (by rfl) ⟨411344, by rfl⟩ : syracuseStep 548459 = 822689) B822689
theorem B319727 : Blo 167798 319727 := bstep (se 1 (by rfl) ⟨239795, by rfl⟩ : syracuseStep 319727 = 479591) B479591
theorem B385451 : Blo 167798 385451 := bstep (se 1 (by rfl) ⟨289088, by rfl⟩ : syracuseStep 385451 = 578177) B578177
theorem B386387 : Blo 167798 386387 := bstep (se 1 (by rfl) ⟨289790, by rfl⟩ : syracuseStep 386387 = 579581) B579581
theorem B649289 : Blo 167798 649289 := bstep (se 2 (by rfl) ⟨243483, by rfl⟩ : syracuseStep 649289 = 486967) B486967
theorem B288859 : Blo 167798 288859 := bstep (se 1 (by rfl) ⟨216644, by rfl⟩ : syracuseStep 288859 = 433289) B433289
theorem B228479 : Blo 167798 228479 := bstep (se 1 (by rfl) ⟨171359, by rfl⟩ : syracuseStep 228479 = 342719) B342719
theorem B1637671 : Blo 167798 1637671 := bstep (se 1 (by rfl) ⟨1228253, by rfl⟩ : syracuseStep 1637671 = 2456507) B2456507
theorem B1474175 : Blo 167798 1474175 := bstep (se 1 (by rfl) ⟨1105631, by rfl⟩ : syracuseStep 1474175 = 2211263) B2211263
theorem B852605 : Blo 167798 852605 := bstep (se 3 (by rfl) ⟨159863, by rfl⟩ : syracuseStep 852605 = 319727) B319727
theorem B918175 : Blo 167798 918175 := bstep (se 1 (by rfl) ⟨688631, by rfl⟩ : syracuseStep 918175 = 1377263) B1377263
theorem B2425625 : Blo 167798 2425625 := bstep (se 2 (by rfl) ⟨909609, by rfl⟩ : syracuseStep 2425625 = 1819219) B1819219
theorem B1214195 : Blo 167798 1214195 := bstep (se 1 (by rfl) ⟨910646, by rfl⟩ : syracuseStep 1214195 = 1821293) B1821293
theorem B2886839 : Blo 167798 2886839 := bstep (se 1 (by rfl) ⟨2165129, by rfl⟩ : syracuseStep 2886839 = 4330259) B4330259
theorem B2428163 : Blo 167798 2428163 := bstep (se 1 (by rfl) ⟨1821122, by rfl⟩ : syracuseStep 2428163 = 3642245) B3642245
theorem B2166401 : Blo 167798 2166401 := bstep (se 2 (by rfl) ⟨812400, by rfl⟩ : syracuseStep 2166401 = 1624801) B1624801
theorem B167839 : Blo 167798 167839 := bstep (se 1 (by rfl) ⟨125879, by rfl⟩ : syracuseStep 167839 = 251759) B251759
theorem B856007 : Blo 167798 856007 := bstep (se 1 (by rfl) ⟨642005, by rfl⟩ : syracuseStep 856007 = 1284011) B1284011
theorem B168575 : Blo 167798 168575 := bstep (se 1 (by rfl) ⟨126431, by rfl⟩ : syracuseStep 168575 = 252863) B252863
theorem B365639 : Blo 167798 365639 := bstep (se 1 (by rfl) ⟨274229, by rfl⟩ : syracuseStep 365639 = 548459) B548459
theorem B857627 : Blo 167798 857627 := bstep (se 1 (by rfl) ⟨643220, by rfl⟩ : syracuseStep 857627 = 1286441) B1286441
theorem B726803 : Blo 167798 726803 := bstep (se 1 (by rfl) ⟨545102, by rfl⟩ : syracuseStep 726803 = 1090205) B1090205
theorem B432859 : Blo 167798 432859 := bstep (se 1 (by rfl) ⟨324644, by rfl⟩ : syracuseStep 432859 = 649289) B649289
theorem B729161 : Blo 167798 729161 := bstep (se 2 (by rfl) ⟨273435, by rfl⟩ : syracuseStep 729161 = 546871) B546871
theorem B866375 : Blo 167798 866375 := bstep (se 1 (by rfl) ⟨649781, by rfl⟩ : syracuseStep 866375 = 1299563) B1299563
theorem B4143271 : Blo 167798 4143271 := bstep (se 1 (by rfl) ⟨3107453, by rfl⟩ : syracuseStep 4143271 = 6214907) B6214907
theorem B6177545 : Blo 167798 6177545 := bstep (se 2 (by rfl) ⟨2316579, by rfl⟩ : syracuseStep 6177545 = 4633159) B4633159
theorem B574235 : Blo 167798 574235 := bstep (se 1 (by rfl) ⟨430676, by rfl⟩ : syracuseStep 574235 = 861353) B861353
theorem B576233 : Blo 167798 576233 := bstep (se 2 (by rfl) ⟨216087, by rfl⟩ : syracuseStep 576233 = 432175) B432175
theorem B576395 : Blo 167798 576395 := bstep (se 1 (by rfl) ⟨432296, by rfl⟩ : syracuseStep 576395 = 864593) B864593
theorem B576503 : Blo 167798 576503 := bstep (se 1 (by rfl) ⟨432377, by rfl⟩ : syracuseStep 576503 = 864755) B864755
theorem B609277 : Blo 167798 609277 := bstep (se 3 (by rfl) ⟨114239, by rfl⟩ : syracuseStep 609277 = 228479) B228479
theorem B2183561 : Blo 167798 2183561 := bstep (se 2 (by rfl) ⟨818835, by rfl⟩ : syracuseStep 2183561 = 1637671) B1637671
theorem B381887 : Blo 167798 381887 := bstep (se 1 (by rfl) ⟨286415, by rfl⟩ : syracuseStep 381887 = 572831) B572831
theorem B152491855 : Blo 167798 152491855 := bstep (se 1 (by rfl) ⟨114368891, by rfl⟩ : syracuseStep 152491855 = 228737783) B228737783
theorem B612521 : Blo 167798 612521 := bstep (se 2 (by rfl) ⟨229695, by rfl⟩ : syracuseStep 612521 = 459391) B459391
theorem B383183 : Blo 167798 383183 := bstep (se 1 (by rfl) ⟨287387, by rfl⟩ : syracuseStep 383183 = 574775) B574775
theorem B252263 : Blo 167798 252263 := bstep (se 1 (by rfl) ⟨189197, by rfl⟩ : syracuseStep 252263 = 378395) B378395
theorem B383471 : Blo 167798 383471 := bstep (se 1 (by rfl) ⟨287603, by rfl⟩ : syracuseStep 383471 = 575207) B575207
theorem B290544353 : Blo 167798 290544353 := bstep (se 2 (by rfl) ⟨108954132, by rfl⟩ : syracuseStep 290544353 = 217908265) B217908265
theorem B384479 : Blo 167798 384479 := bstep (se 1 (by rfl) ⟨288359, by rfl⟩ : syracuseStep 384479 = 576719) B576719
theorem B385145 : Blo 167798 385145 := bstep (se 2 (by rfl) ⟨144429, by rfl⟩ : syracuseStep 385145 = 288859) B288859
theorem B254747 : Blo 167798 254747 := bstep (se 1 (by rfl) ⟨191060, by rfl⟩ : syracuseStep 254747 = 382121) B382121
theorem B385883 : Blo 167798 385883 := bstep (se 1 (by rfl) ⟨289412, by rfl⟩ : syracuseStep 385883 = 578825) B578825
theorem B385895 : Blo 167798 385895 := bstep (se 1 (by rfl) ⟨289421, by rfl⟩ : syracuseStep 385895 = 578843) B578843
theorem B2188457 : Blo 167798 2188457 := bstep (se 2 (by rfl) ⟨820671, by rfl⟩ : syracuseStep 2188457 = 1641343) B1641343
theorem B189679 : Blo 167798 189679 := bstep (se 1 (by rfl) ⟨142259, by rfl⟩ : syracuseStep 189679 = 284519) B284519
theorem B256127 : Blo 167798 256127 := bstep (se 1 (by rfl) ⟨192095, by rfl⟩ : syracuseStep 256127 = 384191) B384191
theorem B649399 : Blo 167798 649399 := bstep (se 1 (by rfl) ⟨487049, by rfl⟩ : syracuseStep 649399 = 974099) B974099
theorem B256967 : Blo 167798 256967 := bstep (se 1 (by rfl) ⟨192725, by rfl⟩ : syracuseStep 256967 = 385451) B385451
theorem B257591 : Blo 167798 257591 := bstep (se 1 (by rfl) ⟨193193, by rfl⟩ : syracuseStep 257591 = 386387) B386387
theorem B1767473 : Blo 167798 1767473 := bstep (se 2 (by rfl) ⟨662802, by rfl⟩ : syracuseStep 1767473 = 1325605) B1325605
theorem B817847 : Blo 167798 817847 := bstep (se 1 (by rfl) ⟨613385, by rfl⟩ : syracuseStep 817847 = 1226771) B1226771
theorem B982783 : Blo 167798 982783 := bstep (se 1 (by rfl) ⟨737087, by rfl⟩ : syracuseStep 982783 = 1474175) B1474175
theorem B1444267 : Blo 167798 1444267 := bstep (se 1 (by rfl) ⟨1083200, by rfl⟩ : syracuseStep 1444267 = 2166401) B2166401
theorem B168175 : Blo 167798 168175 := bstep (se 1 (by rfl) ⟨126131, by rfl⟩ : syracuseStep 168175 = 252263) B252263
theorem B193696235 : Blo 167798 193696235 := bstep (se 1 (by rfl) ⟨145272176, by rfl⟩ : syracuseStep 193696235 = 290544353) B290544353
theorem B169831 : Blo 167798 169831 := bstep (se 1 (by rfl) ⟨127373, by rfl⟩ : syracuseStep 169831 = 254747) B254747
theorem B170751 : Blo 167798 170751 := bstep (se 1 (by rfl) ⟨128063, by rfl⟩ : syracuseStep 170751 = 256127) B256127
theorem B171311 : Blo 167798 171311 := bstep (se 1 (by rfl) ⟨128483, by rfl⟩ : syracuseStep 171311 = 256967) B256967
theorem B171727 : Blo 167798 171727 := bstep (se 1 (by rfl) ⟨128795, by rfl⟩ : syracuseStep 171727 = 257591) B257591
theorem B568403 : Blo 167798 568403 := bstep (se 1 (by rfl) ⟨426302, by rfl⟩ : syracuseStep 568403 = 852605) B852605
theorem B1617083 : Blo 167798 1617083 := bstep (se 1 (by rfl) ⟨1212812, by rfl⟩ : syracuseStep 1617083 = 2425625) B2425625
theorem B1224233 : Blo 167798 1224233 := bstep (se 2 (by rfl) ⟨459087, by rfl⟩ : syracuseStep 1224233 = 918175) B918175
theorem B1618775 : Blo 167798 1618775 := bstep (se 1 (by rfl) ⟨1214081, by rfl⟩ : syracuseStep 1618775 = 2428163) B2428163
theorem B570671 : Blo 167798 570671 := bstep (se 1 (by rfl) ⟨428003, by rfl⟩ : syracuseStep 570671 = 856007) B856007
theorem B865865 : Blo 167798 865865 := bstep (se 2 (by rfl) ⟨324699, by rfl⟩ : syracuseStep 865865 = 649399) B649399
theorem B1455707 : Blo 167798 1455707 := bstep (se 1 (by rfl) ⟨1091780, by rfl⟩ : syracuseStep 1455707 = 2183561) B2183561
theorem B571751 : Blo 167798 571751 := bstep (se 1 (by rfl) ⟨428813, by rfl⟩ : syracuseStep 571751 = 857627) B857627
theorem B408347 : Blo 167798 408347 := bstep (se 1 (by rfl) ⟨306260, by rfl⟩ : syracuseStep 408347 = 612521) B612521
theorem B1458971 : Blo 167798 1458971 := bstep (se 1 (by rfl) ⟨1094228, by rfl⟩ : syracuseStep 1458971 = 2188457) B2188457
theorem B5524361 : Blo 167798 5524361 := bstep (se 2 (by rfl) ⟨2071635, by rfl⟩ : syracuseStep 5524361 = 4143271) B4143271
theorem B577145 : Blo 167798 577145 := bstep (se 2 (by rfl) ⟨216429, by rfl⟩ : syracuseStep 577145 = 432859) B432859
theorem B577583 : Blo 167798 577583 := bstep (se 1 (by rfl) ⟨433187, by rfl⟩ : syracuseStep 577583 = 866375) B866375
theorem B545231 : Blo 167798 545231 := bstep (se 1 (by rfl) ⟨408923, by rfl⟩ : syracuseStep 545231 = 817847) B817847
theorem B4118363 : Blo 167798 4118363 := bstep (se 1 (by rfl) ⟨3088772, by rfl⟩ : syracuseStep 4118363 = 6177545) B6177545
theorem B382823 : Blo 167798 382823 := bstep (se 1 (by rfl) ⟨287117, by rfl⟩ : syracuseStep 382823 = 574235) B574235
theorem B252905 : Blo 167798 252905 := bstep (se 2 (by rfl) ⟨94839, by rfl⟩ : syracuseStep 252905 = 189679) B189679
theorem B384155 : Blo 167798 384155 := bstep (se 1 (by rfl) ⟨288116, by rfl⟩ : syracuseStep 384155 = 576233) B576233
theorem B384263 : Blo 167798 384263 := bstep (se 1 (by rfl) ⟨288197, by rfl⟩ : syracuseStep 384263 = 576395) B576395
theorem B384335 : Blo 167798 384335 := bstep (se 1 (by rfl) ⟨288251, by rfl⟩ : syracuseStep 384335 = 576503) B576503
theorem B1924559 : Blo 167798 1924559 := bstep (se 1 (by rfl) ⟨1443419, by rfl⟩ : syracuseStep 1924559 = 2886839) B2886839
theorem B975037 : Blo 167798 975037 := bstep (se 3 (by rfl) ⟨182819, by rfl⟩ : syracuseStep 975037 = 365639) B365639
theorem B254591 : Blo 167798 254591 := bstep (se 1 (by rfl) ⟨190943, by rfl⟩ : syracuseStep 254591 = 381887) B381887
theorem B484535 : Blo 167798 484535 := bstep (se 1 (by rfl) ⟨363401, by rfl⟩ : syracuseStep 484535 = 726803) B726803
theorem B812369 : Blo 167798 812369 := bstep (se 2 (by rfl) ⟨304638, by rfl⟩ : syracuseStep 812369 = 609277) B609277
theorem B255455 : Blo 167798 255455 := bstep (se 1 (by rfl) ⟨191591, by rfl⟩ : syracuseStep 255455 = 383183) B383183
theorem B255647 : Blo 167798 255647 := bstep (se 1 (by rfl) ⟨191735, by rfl⟩ : syracuseStep 255647 = 383471) B383471
theorem B3237853 : Blo 167798 3237853 := bstep (se 3 (by rfl) ⟨607097, by rfl⟩ : syracuseStep 3237853 = 1214195) B1214195
theorem B256319 : Blo 167798 256319 := bstep (se 1 (by rfl) ⟨192239, by rfl⟩ : syracuseStep 256319 = 384479) B384479
theorem B486107 : Blo 167798 486107 := bstep (se 1 (by rfl) ⟨364580, by rfl⟩ : syracuseStep 486107 = 729161) B729161
theorem B256763 : Blo 167798 256763 := bstep (se 1 (by rfl) ⟨192572, by rfl⟩ : syracuseStep 256763 = 385145) B385145
theorem B257255 : Blo 167798 257255 := bstep (se 1 (by rfl) ⟨192941, by rfl⟩ : syracuseStep 257255 = 385883) B385883
theorem B257263 : Blo 167798 257263 := bstep (se 1 (by rfl) ⟨192947, by rfl⟩ : syracuseStep 257263 = 385895) B385895
theorem B203322473 : Blo 167798 203322473 := bstep (se 2 (by rfl) ⟨76245927, by rfl⟩ : syracuseStep 203322473 = 152491855) B152491855
theorem B1178315 : Blo 167798 1178315 := bstep (se 1 (by rfl) ⟨883736, by rfl⟩ : syracuseStep 1178315 = 1767473) B1767473
theorem B1310377 : Blo 167798 1310377 := bstep (se 2 (by rfl) ⟨491391, by rfl⟩ : syracuseStep 1310377 = 982783) B982783
theorem B363487 : Blo 167798 363487 := bstep (se 1 (by rfl) ⟨272615, by rfl⟩ : syracuseStep 363487 = 545231) B545231
theorem B168603 : Blo 167798 168603 := bstep (se 1 (by rfl) ⟨126452, by rfl⟩ : syracuseStep 168603 = 252905) B252905
theorem B1283039 : Blo 167798 1283039 := bstep (se 1 (by rfl) ⟨962279, by rfl⟩ : syracuseStep 1283039 = 1924559) B1924559
theorem B169727 : Blo 167798 169727 := bstep (se 1 (by rfl) ⟨127295, by rfl⟩ : syracuseStep 169727 = 254591) B254591
theorem B170303 : Blo 167798 170303 := bstep (se 1 (by rfl) ⟨127727, by rfl⟩ : syracuseStep 170303 = 255455) B255455
theorem B170431 : Blo 167798 170431 := bstep (se 1 (by rfl) ⟨127823, by rfl⟩ : syracuseStep 170431 = 255647) B255647
theorem B170879 : Blo 167798 170879 := bstep (se 1 (by rfl) ⟨128159, by rfl⟩ : syracuseStep 170879 = 256319) B256319
theorem B171175 : Blo 167798 171175 := bstep (se 1 (by rfl) ⟨128381, by rfl⟩ : syracuseStep 171175 = 256763) B256763
theorem B171503 : Blo 167798 171503 := bstep (se 1 (by rfl) ⟨128627, by rfl⟩ : syracuseStep 171503 = 257255) B257255
theorem B272231 : Blo 167798 272231 := bstep (se 1 (by rfl) ⟨204173, by rfl⟩ : syracuseStep 272231 = 408347) B408347
theorem B1747169 : Blo 167798 1747169 := bstep (se 2 (by rfl) ⟨655188, by rfl⟩ : syracuseStep 1747169 = 1310377) B1310377
theorem B3682907 : Blo 167798 3682907 := bstep (se 1 (by rfl) ⟨2762180, by rfl⟩ : syracuseStep 3682907 = 5524361) B5524361
theorem B541579 : Blo 167798 541579 := bstep (se 1 (by rfl) ⟨406184, by rfl⟩ : syracuseStep 541579 = 812369) B812369
theorem B378935 : Blo 167798 378935 := bstep (se 1 (by rfl) ⟨284201, by rfl⟩ : syracuseStep 378935 = 568403) B568403
theorem B135548315 : Blo 167798 135548315 := bstep (se 1 (by rfl) ⟨101661236, by rfl⟩ : syracuseStep 135548315 = 203322473) B203322473
theorem B380447 : Blo 167798 380447 := bstep (se 1 (by rfl) ⟨285335, by rfl⟩ : syracuseStep 380447 = 570671) B570671
theorem B577243 : Blo 167798 577243 := bstep (se 1 (by rfl) ⟨432932, by rfl⟩ : syracuseStep 577243 = 865865) B865865
theorem B970471 : Blo 167798 970471 := bstep (se 1 (by rfl) ⟨727853, by rfl⟩ : syracuseStep 970471 = 1455707) B1455707
theorem B381167 : Blo 167798 381167 := bstep (se 1 (by rfl) ⟨285875, by rfl⟩ : syracuseStep 381167 = 571751) B571751
theorem B1300049 : Blo 167798 1300049 := bstep (se 2 (by rfl) ⟨487518, by rfl⟩ : syracuseStep 1300049 = 975037) B975037
theorem B972647 : Blo 167798 972647 := bstep (se 1 (by rfl) ⟨729485, by rfl⟩ : syracuseStep 972647 = 1458971) B1458971
theorem B4317137 : Blo 167798 4317137 := bstep (se 2 (by rfl) ⟨1618926, by rfl⟩ : syracuseStep 4317137 = 3237853) B3237853
theorem B385055 : Blo 167798 385055 := bstep (se 1 (by rfl) ⟨288791, by rfl⟩ : syracuseStep 385055 = 577583) B577583
theorem B129130823 : Blo 167798 129130823 := bstep (se 1 (by rfl) ⟨96848117, by rfl⟩ : syracuseStep 129130823 = 193696235) B193696235
theorem B1925689 : Blo 167798 1925689 := bstep (se 2 (by rfl) ⟨722133, by rfl⟩ : syracuseStep 1925689 = 1444267) B1444267
theorem B2745575 : Blo 167798 2745575 := bstep (se 1 (by rfl) ⟨2059181, by rfl⟩ : syracuseStep 2745575 = 4118363) B4118363
theorem B255215 : Blo 167798 255215 := bstep (se 1 (by rfl) ⟨191411, by rfl⟩ : syracuseStep 255215 = 382823) B382823
theorem B256103 : Blo 167798 256103 := bstep (se 1 (by rfl) ⟨192077, by rfl⟩ : syracuseStep 256103 = 384155) B384155
theorem B256175 : Blo 167798 256175 := bstep (se 1 (by rfl) ⟨192131, by rfl⟩ : syracuseStep 256175 = 384263) B384263
theorem B256223 : Blo 167798 256223 := bstep (se 1 (by rfl) ⟨192167, by rfl⟩ : syracuseStep 256223 = 384335) B384335
theorem B323023 : Blo 167798 323023 := bstep (se 1 (by rfl) ⟨242267, by rfl⟩ : syracuseStep 323023 = 484535) B484535
theorem B1372069 : Blo 167798 1372069 := bstep (se 4 (by rfl) ⟨128631, by rfl⟩ : syracuseStep 1372069 = 257263) B257263
theorem B324071 : Blo 167798 324071 := bstep (se 1 (by rfl) ⟨243053, by rfl⟩ : syracuseStep 324071 = 486107) B486107
theorem B1078055 : Blo 167798 1078055 := bstep (se 1 (by rfl) ⟨808541, by rfl⟩ : syracuseStep 1078055 = 1617083) B1617083
theorem B816155 : Blo 167798 816155 := bstep (se 1 (by rfl) ⟨612116, by rfl⟩ : syracuseStep 816155 = 1224233) B1224233
theorem B1079183 : Blo 167798 1079183 := bstep (se 1 (by rfl) ⟨809387, by rfl⟩ : syracuseStep 1079183 = 1618775) B1618775
theorem B1539053 : Blo 167798 1539053 := bstep (se 3 (by rfl) ⟨288572, by rfl⟩ : syracuseStep 1539053 = 577145) B577145
theorem B785543 : Blo 167798 785543 := bstep (se 1 (by rfl) ⟨589157, by rfl⟩ : syracuseStep 785543 = 1178315) B1178315
theorem B722105 : Blo 167798 722105 := bstep (se 2 (by rfl) ⟨270789, by rfl⟩ : syracuseStep 722105 = 541579) B541579
theorem B855359 : Blo 167798 855359 := bstep (se 1 (by rfl) ⟨641519, by rfl⟩ : syracuseStep 855359 = 1283039) B1283039
theorem B430697 : Blo 167798 430697 := bstep (se 2 (by rfl) ⟨161511, by rfl⟩ : syracuseStep 430697 = 323023) B323023
theorem B86087215 : Blo 167798 86087215 := bstep (se 1 (by rfl) ⟨64565411, by rfl⟩ : syracuseStep 86087215 = 129130823) B129130823
theorem B170143 : Blo 167798 170143 := bstep (se 1 (by rfl) ⟨127607, by rfl⟩ : syracuseStep 170143 = 255215) B255215
theorem B170735 : Blo 167798 170735 := bstep (se 1 (by rfl) ⟨128051, by rfl⟩ : syracuseStep 170735 = 256103) B256103
theorem B170783 : Blo 167798 170783 := bstep (se 1 (by rfl) ⟨128087, by rfl⟩ : syracuseStep 170783 = 256175) B256175
theorem B170815 : Blo 167798 170815 := bstep (se 1 (by rfl) ⟨128111, by rfl⟩ : syracuseStep 170815 = 256223) B256223
theorem B1026035 : Blo 167798 1026035 := bstep (se 1 (by rfl) ⟨769526, by rfl⟩ : syracuseStep 1026035 = 1539053) B1539053
theorem B7317701 : Blo 167798 7317701 := bstep (se 4 (by rfl) ⟨686034, by rfl⟩ : syracuseStep 7317701 = 1372069) B1372069
theorem B2567585 : Blo 167798 2567585 := bstep (se 2 (by rfl) ⟨962844, by rfl⟩ : syracuseStep 2567585 = 1925689) B1925689
theorem B866699 : Blo 167798 866699 := bstep (se 1 (by rfl) ⟨650024, by rfl⟩ : syracuseStep 866699 = 1300049) B1300049
theorem B769657 : Blo 167798 769657 := bstep (se 2 (by rfl) ⟨288621, by rfl⟩ : syracuseStep 769657 = 577243) B577243
theorem B181487 : Blo 167798 181487 := bstep (se 1 (by rfl) ⟨136115, by rfl⟩ : syracuseStep 181487 = 272231) B272231
theorem B1164779 : Blo 167798 1164779 := bstep (se 1 (by rfl) ⟨873584, by rfl⟩ : syracuseStep 1164779 = 1747169) B1747169
theorem B216047 : Blo 167798 216047 := bstep (se 1 (by rfl) ⟨162035, by rfl⟩ : syracuseStep 216047 = 324071) B324071
theorem B544103 : Blo 167798 544103 := bstep (se 1 (by rfl) ⟨408077, by rfl⟩ : syracuseStep 544103 = 816155) B816155
theorem B252623 : Blo 167798 252623 := bstep (se 1 (by rfl) ⟨189467, by rfl⟩ : syracuseStep 252623 = 378935) B378935
theorem B90365543 : Blo 167798 90365543 := bstep (se 1 (by rfl) ⟨67774157, by rfl⟩ : syracuseStep 90365543 = 135548315) B135548315
theorem B253631 : Blo 167798 253631 := bstep (se 1 (by rfl) ⟨190223, by rfl⟩ : syracuseStep 253631 = 380447) B380447
theorem B254111 : Blo 167798 254111 := bstep (se 1 (by rfl) ⟨190583, by rfl⟩ : syracuseStep 254111 = 381167) B381167
theorem B648431 : Blo 167798 648431 := bstep (se 1 (by rfl) ⟨486323, by rfl⟩ : syracuseStep 648431 = 972647) B972647
theorem B484649 : Blo 167798 484649 := bstep (se 2 (by rfl) ⟨181743, by rfl⟩ : syracuseStep 484649 = 363487) B363487
theorem B2878091 : Blo 167798 2878091 := bstep (se 1 (by rfl) ⟨2158568, by rfl⟩ : syracuseStep 2878091 = 4317137) B4317137
theorem B256703 : Blo 167798 256703 := bstep (se 1 (by rfl) ⟨192527, by rfl⟩ : syracuseStep 256703 = 385055) B385055
theorem B1830383 : Blo 167798 1830383 := bstep (se 1 (by rfl) ⟨1372787, by rfl⟩ : syracuseStep 1830383 = 2745575) B2745575
theorem B2094781 : Blo 167798 2094781 := bstep (se 3 (by rfl) ⟨392771, by rfl⟩ : syracuseStep 2094781 = 785543) B785543
theorem B2455271 : Blo 167798 2455271 := bstep (se 1 (by rfl) ⟨1841453, by rfl⟩ : syracuseStep 2455271 = 3682907) B3682907
theorem B718703 : Blo 167798 718703 := bstep (se 1 (by rfl) ⟨539027, by rfl⟩ : syracuseStep 718703 = 1078055) B1078055
theorem B5175845 : Blo 167798 5175845 := bstep (se 4 (by rfl) ⟨485235, by rfl⟩ : syracuseStep 5175845 = 970471) B970471
theorem B719455 : Blo 167798 719455 := bstep (se 1 (by rfl) ⟨539591, by rfl⟩ : syracuseStep 719455 = 1079183) B1079183
theorem B362735 : Blo 167798 362735 := bstep (se 1 (by rfl) ⟨272051, by rfl⟩ : syracuseStep 362735 = 544103) B544103
theorem B168415 : Blo 167798 168415 := bstep (se 1 (by rfl) ⟨126311, by rfl⟩ : syracuseStep 168415 = 252623) B252623
theorem B169087 : Blo 167798 169087 := bstep (se 1 (by rfl) ⟨126815, by rfl⟩ : syracuseStep 169087 = 253631) B253631
theorem B169407 : Blo 167798 169407 := bstep (se 1 (by rfl) ⟨127055, by rfl⟩ : syracuseStep 169407 = 254111) B254111
theorem B432287 : Blo 167798 432287 := bstep (se 1 (by rfl) ⟨324215, by rfl⟩ : syracuseStep 432287 = 648431) B648431
theorem B171135 : Blo 167798 171135 := bstep (se 1 (by rfl) ⟨128351, by rfl⟩ : syracuseStep 171135 = 256703) B256703
theorem B2793041 : Blo 167798 2793041 := bstep (se 2 (by rfl) ⟨1047390, by rfl⟩ : syracuseStep 2793041 = 2094781) B2094781
theorem B1220255 : Blo 167798 1220255 := bstep (se 1 (by rfl) ⟨915191, by rfl⟩ : syracuseStep 1220255 = 1830383) B1830383
theorem B959273 : Blo 167798 959273 := bstep (se 2 (by rfl) ⟨359727, by rfl⟩ : syracuseStep 959273 = 719455) B719455
theorem B3450563 : Blo 167798 3450563 := bstep (se 1 (by rfl) ⟨2587922, by rfl⟩ : syracuseStep 3450563 = 5175845) B5175845
theorem B1026209 : Blo 167798 1026209 := bstep (se 2 (by rfl) ⟨384828, by rfl⟩ : syracuseStep 1026209 = 769657) B769657
theorem B570239 : Blo 167798 570239 := bstep (se 1 (by rfl) ⟨427679, by rfl⟩ : syracuseStep 570239 = 855359) B855359
theorem B60243695 : Blo 167798 60243695 := bstep (se 1 (by rfl) ⟨45182771, by rfl⟩ : syracuseStep 60243695 = 90365543) B90365543
theorem B1918727 : Blo 167798 1918727 := bstep (se 1 (by rfl) ⟨1439045, by rfl⟩ : syracuseStep 1918727 = 2878091) B2878091
theorem B576125 : Blo 167798 576125 := bstep (se 3 (by rfl) ⟨108023, by rfl⟩ : syracuseStep 576125 = 216047) B216047
theorem B479135 : Blo 167798 479135 := bstep (se 1 (by rfl) ⟨359351, by rfl⟩ : syracuseStep 479135 = 718703) B718703
theorem B577799 : Blo 167798 577799 := bstep (se 1 (by rfl) ⟨433349, by rfl⟩ : syracuseStep 577799 = 866699) B866699
theorem B481403 : Blo 167798 481403 := bstep (se 1 (by rfl) ⟨361052, by rfl⟩ : syracuseStep 481403 = 722105) B722105
theorem B776519 : Blo 167798 776519 := bstep (se 1 (by rfl) ⟨582389, by rfl⟩ : syracuseStep 776519 = 1164779) B1164779
theorem B287131 : Blo 167798 287131 := bstep (se 1 (by rfl) ⟨215348, by rfl⟩ : syracuseStep 287131 = 430697) B430697
theorem B483965 : Blo 167798 483965 := bstep (se 3 (by rfl) ⟨90743, by rfl⟩ : syracuseStep 483965 = 181487) B181487
theorem B323099 : Blo 167798 323099 := bstep (se 1 (by rfl) ⟨242324, by rfl⟩ : syracuseStep 323099 = 484649) B484649
theorem B684023 : Blo 167798 684023 := bstep (se 1 (by rfl) ⟨513017, by rfl⟩ : syracuseStep 684023 = 1026035) B1026035
theorem B4878467 : Blo 167798 4878467 := bstep (se 1 (by rfl) ⟨3658850, by rfl⟩ : syracuseStep 4878467 = 7317701) B7317701
theorem B114782953 : Blo 167798 114782953 := bstep (se 2 (by rfl) ⟨43043607, by rfl⟩ : syracuseStep 114782953 = 86087215) B86087215
theorem B6846893 : Blo 167798 6846893 := bstep (se 3 (by rfl) ⟨1283792, by rfl⟩ : syracuseStep 6846893 = 2567585) B2567585
theorem B1636847 : Blo 167798 1636847 := bstep (se 1 (by rfl) ⟨1227635, by rfl⟩ : syracuseStep 1636847 = 2455271) B2455271
theorem B1279151 : Blo 167798 1279151 := bstep (se 1 (by rfl) ⟨959363, by rfl⟩ : syracuseStep 1279151 = 1918727) B1918727
theorem B2300375 : Blo 167798 2300375 := bstep (se 1 (by rfl) ⟨1725281, by rfl⟩ : syracuseStep 2300375 = 3450563) B3450563
theorem B3252311 : Blo 167798 3252311 := bstep (se 1 (by rfl) ⟨2439233, by rfl⟩ : syracuseStep 3252311 = 4878467) B4878467
theorem B4564595 : Blo 167798 4564595 := bstep (se 1 (by rfl) ⟨3423446, by rfl⟩ : syracuseStep 4564595 = 6846893) B6846893
theorem B1091231 : Blo 167798 1091231 := bstep (se 1 (by rfl) ⟨818423, by rfl⟩ : syracuseStep 1091231 = 1636847) B1636847
theorem B241823 : Blo 167798 241823 := bstep (se 1 (by rfl) ⟨181367, by rfl⟩ : syracuseStep 241823 = 362735) B362735
theorem B639515 : Blo 167798 639515 := bstep (se 1 (by rfl) ⟨479636, by rfl⟩ : syracuseStep 639515 = 959273) B959273
theorem B153043937 : Blo 167798 153043937 := bstep (se 2 (by rfl) ⟨57391476, by rfl⟩ : syracuseStep 153043937 = 114782953) B114782953
theorem B215399 : Blo 167798 215399 := bstep (se 1 (by rfl) ⟨161549, by rfl⟩ : syracuseStep 215399 = 323099) B323099
theorem B380159 : Blo 167798 380159 := bstep (se 1 (by rfl) ⟨285119, by rfl⟩ : syracuseStep 380159 = 570239) B570239
theorem B40162463 : Blo 167798 40162463 := bstep (se 1 (by rfl) ⟨30121847, by rfl⟩ : syracuseStep 40162463 = 60243695) B60243695
theorem B1824061 : Blo 167798 1824061 := bstep (se 3 (by rfl) ⟨342011, by rfl⟩ : syracuseStep 1824061 = 684023) B684023
theorem B382841 : Blo 167798 382841 := bstep (se 2 (by rfl) ⟨143565, by rfl⟩ : syracuseStep 382841 = 287131) B287131
theorem B384083 : Blo 167798 384083 := bstep (se 1 (by rfl) ⟨288062, by rfl⟩ : syracuseStep 384083 = 576125) B576125
theorem B385199 : Blo 167798 385199 := bstep (se 1 (by rfl) ⟨288899, by rfl⟩ : syracuseStep 385199 = 577799) B577799
theorem B320935 : Blo 167798 320935 := bstep (se 1 (by rfl) ⟨240701, by rfl⟩ : syracuseStep 320935 = 481403) B481403
theorem B288191 : Blo 167798 288191 := bstep (se 1 (by rfl) ⟨216143, by rfl⟩ : syracuseStep 288191 = 432287) B432287
theorem B517679 : Blo 167798 517679 := bstep (se 1 (by rfl) ⟨388259, by rfl⟩ : syracuseStep 517679 = 776519) B776519
theorem B1862027 : Blo 167798 1862027 := bstep (se 1 (by rfl) ⟨1396520, by rfl⟩ : syracuseStep 1862027 = 2793041) B2793041
theorem B813503 : Blo 167798 813503 := bstep (se 1 (by rfl) ⟨610127, by rfl⟩ : syracuseStep 813503 = 1220255) B1220255
theorem B322643 : Blo 167798 322643 := bstep (se 1 (by rfl) ⟨241982, by rfl⟩ : syracuseStep 322643 = 483965) B483965
theorem B684139 : Blo 167798 684139 := bstep (se 1 (by rfl) ⟨513104, by rfl⟩ : syracuseStep 684139 = 1026209) B1026209
theorem B1277693 : Blo 167798 1277693 := bstep (se 3 (by rfl) ⟨239567, by rfl⟩ : syracuseStep 1277693 = 479135) B479135
theorem B426343 : Blo 167798 426343 := bstep (se 1 (by rfl) ⟨319757, by rfl⟩ : syracuseStep 426343 = 639515) B639515
theorem B852767 : Blo 167798 852767 := bstep (se 1 (by rfl) ⟨639575, by rfl⟩ : syracuseStep 852767 = 1279151) B1279151
theorem B427913 : Blo 167798 427913 := bstep (se 2 (by rfl) ⟨160467, by rfl⟩ : syracuseStep 427913 = 320935) B320935
theorem B26774975 : Blo 167798 26774975 := bstep (se 1 (by rfl) ⟨20081231, by rfl⟩ : syracuseStep 26774975 = 40162463) B40162463
theorem B2168207 : Blo 167798 2168207 := bstep (se 1 (by rfl) ⟨1626155, by rfl⟩ : syracuseStep 2168207 = 3252311) B3252311
theorem B727487 : Blo 167798 727487 := bstep (se 1 (by rfl) ⟨545615, by rfl⟩ : syracuseStep 727487 = 1091231) B1091231
theorem B2432081 : Blo 167798 2432081 := bstep (se 2 (by rfl) ⟨912030, by rfl⟩ : syracuseStep 2432081 = 1824061) B1824061
theorem B860381 : Blo 167798 860381 := bstep (se 3 (by rfl) ⟨161321, by rfl⟩ : syracuseStep 860381 = 322643) B322643
theorem B574397 : Blo 167798 574397 := bstep (se 3 (by rfl) ⟨107699, by rfl⟩ : syracuseStep 574397 = 215399) B215399
theorem B345119 : Blo 167798 345119 := bstep (se 1 (by rfl) ⟨258839, by rfl⟩ : syracuseStep 345119 = 517679) B517679
theorem B542335 : Blo 167798 542335 := bstep (se 1 (by rfl) ⟨406751, by rfl⟩ : syracuseStep 542335 = 813503) B813503
theorem B644861 : Blo 167798 644861 := bstep (se 3 (by rfl) ⟨120911, by rfl⟩ : syracuseStep 644861 = 241823) B241823
theorem B102029291 : Blo 167798 102029291 := bstep (se 1 (by rfl) ⟨76521968, by rfl⟩ : syracuseStep 102029291 = 153043937) B153043937
theorem B253439 : Blo 167798 253439 := bstep (se 1 (by rfl) ⟨190079, by rfl⟩ : syracuseStep 253439 = 380159) B380159
theorem B255227 : Blo 167798 255227 := bstep (se 1 (by rfl) ⟨191420, by rfl⟩ : syracuseStep 255227 = 382841) B382841
theorem B1533583 : Blo 167798 1533583 := bstep (se 1 (by rfl) ⟨1150187, by rfl⟩ : syracuseStep 1533583 = 2300375) B2300375
theorem B256055 : Blo 167798 256055 := bstep (se 1 (by rfl) ⟨192041, by rfl⟩ : syracuseStep 256055 = 384083) B384083
theorem B256799 : Blo 167798 256799 := bstep (se 1 (by rfl) ⟨192599, by rfl⟩ : syracuseStep 256799 = 385199) B385199
theorem B912185 : Blo 167798 912185 := bstep (se 2 (by rfl) ⟨342069, by rfl⟩ : syracuseStep 912185 = 684139) B684139
theorem B192127 : Blo 167798 192127 := bstep (se 1 (by rfl) ⟨144095, by rfl⟩ : syracuseStep 192127 = 288191) B288191
theorem B3043063 : Blo 167798 3043063 := bstep (se 1 (by rfl) ⟨2282297, by rfl⟩ : syracuseStep 3043063 = 4564595) B4564595
theorem B1241351 : Blo 167798 1241351 := bstep (se 1 (by rfl) ⟨931013, by rfl⟩ : syracuseStep 1241351 = 1862027) B1862027
theorem B851795 : Blo 167798 851795 := bstep (se 1 (by rfl) ⟨638846, by rfl⟩ : syracuseStep 851795 = 1277693) B1277693
theorem B723113 : Blo 167798 723113 := bstep (se 2 (by rfl) ⟨271167, by rfl⟩ : syracuseStep 723113 = 542335) B542335
theorem B920317 : Blo 167798 920317 := bstep (se 3 (by rfl) ⟨172559, by rfl⟩ : syracuseStep 920317 = 345119) B345119
theorem B1445471 : Blo 167798 1445471 := bstep (se 1 (by rfl) ⟨1084103, by rfl⟩ : syracuseStep 1445471 = 2168207) B2168207
theorem B429907 : Blo 167798 429907 := bstep (se 1 (by rfl) ⟨322430, by rfl⟩ : syracuseStep 429907 = 644861) B644861
theorem B168959 : Blo 167798 168959 := bstep (se 1 (by rfl) ⟨126719, by rfl⟩ : syracuseStep 168959 = 253439) B253439
theorem B170151 : Blo 167798 170151 := bstep (se 1 (by rfl) ⟨127613, by rfl⟩ : syracuseStep 170151 = 255227) B255227
theorem B170703 : Blo 167798 170703 := bstep (se 1 (by rfl) ⟨128027, by rfl⟩ : syracuseStep 170703 = 256055) B256055
theorem B171199 : Blo 167798 171199 := bstep (se 1 (by rfl) ⟨128399, by rfl⟩ : syracuseStep 171199 = 256799) B256799
theorem B827567 : Blo 167798 827567 := bstep (se 1 (by rfl) ⟨620675, by rfl⟩ : syracuseStep 827567 = 1241351) B1241351
theorem B567863 : Blo 167798 567863 := bstep (se 1 (by rfl) ⟨425897, by rfl⟩ : syracuseStep 567863 = 851795) B851795
theorem B568457 : Blo 167798 568457 := bstep (se 2 (by rfl) ⟨213171, by rfl⟩ : syracuseStep 568457 = 426343) B426343
theorem B568511 : Blo 167798 568511 := bstep (se 1 (by rfl) ⟨426383, by rfl⟩ : syracuseStep 568511 = 852767) B852767
theorem B2044777 : Blo 167798 2044777 := bstep (se 2 (by rfl) ⟨766791, by rfl⟩ : syracuseStep 2044777 = 1533583) B1533583
theorem B1621387 : Blo 167798 1621387 := bstep (se 1 (by rfl) ⟨1216040, by rfl⟩ : syracuseStep 1621387 = 2432081) B2432081
theorem B573587 : Blo 167798 573587 := bstep (se 1 (by rfl) ⟨430190, by rfl⟩ : syracuseStep 573587 = 860381) B860381
theorem B608123 : Blo 167798 608123 := bstep (se 1 (by rfl) ⟨456092, by rfl⟩ : syracuseStep 608123 = 912185) B912185
theorem B382931 : Blo 167798 382931 := bstep (se 1 (by rfl) ⟨287198, by rfl⟩ : syracuseStep 382931 = 574397) B574397
theorem B285275 : Blo 167798 285275 := bstep (se 1 (by rfl) ⟨213956, by rfl⟩ : syracuseStep 285275 = 427913) B427913
theorem B17849983 : Blo 167798 17849983 := bstep (se 1 (by rfl) ⟨13387487, by rfl⟩ : syracuseStep 17849983 = 26774975) B26774975
theorem B68019527 : Blo 167798 68019527 := bstep (se 1 (by rfl) ⟨51014645, by rfl⟩ : syracuseStep 68019527 = 102029291) B102029291
theorem B484991 : Blo 167798 484991 := bstep (se 1 (by rfl) ⟨363743, by rfl⟩ : syracuseStep 484991 = 727487) B727487
theorem B256169 : Blo 167798 256169 := bstep (se 2 (by rfl) ⟨96063, by rfl⟩ : syracuseStep 256169 = 192127) B192127
theorem B4057417 : Blo 167798 4057417 := bstep (se 2 (by rfl) ⟨1521531, by rfl⟩ : syracuseStep 4057417 = 3043063) B3043063
theorem B2726369 : Blo 167798 2726369 := bstep (se 2 (by rfl) ⟨1022388, by rfl⟩ : syracuseStep 2726369 = 2044777) B2044777
theorem B170779 : Blo 167798 170779 := bstep (se 1 (by rfl) ⟨128084, by rfl⟩ : syracuseStep 170779 = 256169) B256169
theorem B23799977 : Blo 167798 23799977 := bstep (se 2 (by rfl) ⟨8924991, by rfl⟩ : syracuseStep 23799977 = 17849983) B17849983
theorem B405415 : Blo 167798 405415 := bstep (se 1 (by rfl) ⟨304061, by rfl⟩ : syracuseStep 405415 = 608123) B608123
theorem B21639557 : Blo 167798 21639557 := bstep (se 4 (by rfl) ⟨2028708, by rfl⟩ : syracuseStep 21639557 = 4057417) B4057417
theorem B963647 : Blo 167798 963647 := bstep (se 1 (by rfl) ⟨722735, by rfl⟩ : syracuseStep 963647 = 1445471) B1445471
theorem B1227089 : Blo 167798 1227089 := bstep (se 2 (by rfl) ⟨460158, by rfl⟩ : syracuseStep 1227089 = 920317) B920317
theorem B573209 : Blo 167798 573209 := bstep (se 2 (by rfl) ⟨214953, by rfl⟩ : syracuseStep 573209 = 429907) B429907
theorem B378575 : Blo 167798 378575 := bstep (se 1 (by rfl) ⟨283931, by rfl⟩ : syracuseStep 378575 = 567863) B567863
theorem B378971 : Blo 167798 378971 := bstep (se 1 (by rfl) ⟨284228, by rfl⟩ : syracuseStep 378971 = 568457) B568457
theorem B379007 : Blo 167798 379007 := bstep (se 1 (by rfl) ⟨284255, by rfl⟩ : syracuseStep 379007 = 568511) B568511
theorem B382391 : Blo 167798 382391 := bstep (se 1 (by rfl) ⟨286793, by rfl⟩ : syracuseStep 382391 = 573587) B573587
theorem B482075 : Blo 167798 482075 := bstep (se 1 (by rfl) ⟨361556, by rfl⟩ : syracuseStep 482075 = 723113) B723113
theorem B255287 : Blo 167798 255287 := bstep (se 1 (by rfl) ⟨191465, by rfl⟩ : syracuseStep 255287 = 382931) B382931
theorem B190183 : Blo 167798 190183 := bstep (se 1 (by rfl) ⟨142637, by rfl⟩ : syracuseStep 190183 = 285275) B285275
theorem B551711 : Blo 167798 551711 := bstep (se 1 (by rfl) ⟨413783, by rfl⟩ : syracuseStep 551711 = 827567) B827567
theorem B45346351 : Blo 167798 45346351 := bstep (se 1 (by rfl) ⟨34009763, by rfl⟩ : syracuseStep 45346351 = 68019527) B68019527
theorem B323327 : Blo 167798 323327 := bstep (se 1 (by rfl) ⟨242495, by rfl⟩ : syracuseStep 323327 = 484991) B484991
theorem B2161849 : Blo 167798 2161849 := bstep (se 2 (by rfl) ⟨810693, by rfl⟩ : syracuseStep 2161849 = 1621387) B1621387
theorem B60461801 : Blo 167798 60461801 := bstep (se 2 (by rfl) ⟨22673175, by rfl⟩ : syracuseStep 60461801 = 45346351) B45346351
theorem B170191 : Blo 167798 170191 := bstep (se 1 (by rfl) ⟨127643, by rfl⟩ : syracuseStep 170191 = 255287) B255287
theorem B15866651 : Blo 167798 15866651 := bstep (se 1 (by rfl) ⟨11899988, by rfl⟩ : syracuseStep 15866651 = 23799977) B23799977
theorem B14426371 : Blo 167798 14426371 := bstep (se 1 (by rfl) ⟨10819778, by rfl⟩ : syracuseStep 14426371 = 21639557) B21639557
theorem B1817579 : Blo 167798 1817579 := bstep (se 1 (by rfl) ⟨1363184, by rfl⟩ : syracuseStep 1817579 = 2726369) B2726369
theorem B215551 : Blo 167798 215551 := bstep (se 1 (by rfl) ⟨161663, by rfl⟩ : syracuseStep 215551 = 323327) B323327
theorem B642431 : Blo 167798 642431 := bstep (se 1 (by rfl) ⟨481823, by rfl⟩ : syracuseStep 642431 = 963647) B963647
theorem B382139 : Blo 167798 382139 := bstep (se 1 (by rfl) ⟨286604, by rfl⟩ : syracuseStep 382139 = 573209) B573209
theorem B252383 : Blo 167798 252383 := bstep (se 1 (by rfl) ⟨189287, by rfl⟩ : syracuseStep 252383 = 378575) B378575
theorem B252647 : Blo 167798 252647 := bstep (se 1 (by rfl) ⟨189485, by rfl⟩ : syracuseStep 252647 = 378971) B378971
theorem B252671 : Blo 167798 252671 := bstep (se 1 (by rfl) ⟨189503, by rfl⟩ : syracuseStep 252671 = 379007) B379007
theorem B253577 : Blo 167798 253577 := bstep (se 2 (by rfl) ⟨95091, by rfl⟩ : syracuseStep 253577 = 190183) B190183
theorem B254927 : Blo 167798 254927 := bstep (se 1 (by rfl) ⟨191195, by rfl⟩ : syracuseStep 254927 = 382391) B382391
theorem B321383 : Blo 167798 321383 := bstep (se 1 (by rfl) ⟨241037, by rfl⟩ : syracuseStep 321383 = 482075) B482075
theorem B1471229 : Blo 167798 1471229 := bstep (se 3 (by rfl) ⟨275855, by rfl⟩ : syracuseStep 1471229 = 551711) B551711
theorem B818059 : Blo 167798 818059 := bstep (se 1 (by rfl) ⟨613544, by rfl⟩ : syracuseStep 818059 = 1227089) B1227089
theorem B2882465 : Blo 167798 2882465 := bstep (se 2 (by rfl) ⟨1080924, by rfl⟩ : syracuseStep 2882465 = 2161849) B2161849
theorem B2162213 : Blo 167798 2162213 := bstep (se 4 (by rfl) ⟨202707, by rfl⟩ : syracuseStep 2162213 = 405415) B405415
theorem B19235161 : Blo 167798 19235161 := bstep (se 2 (by rfl) ⟨7213185, by rfl⟩ : syracuseStep 19235161 = 14426371) B14426371
theorem B428287 : Blo 167798 428287 := bstep (se 1 (by rfl) ⟨321215, by rfl⟩ : syracuseStep 428287 = 642431) B642431
theorem B40307867 : Blo 167798 40307867 := bstep (se 1 (by rfl) ⟨30230900, by rfl⟩ : syracuseStep 40307867 = 60461801) B60461801
theorem B168255 : Blo 167798 168255 := bstep (se 1 (by rfl) ⟨126191, by rfl⟩ : syracuseStep 168255 = 252383) B252383
theorem B168431 : Blo 167798 168431 := bstep (se 1 (by rfl) ⟨126323, by rfl⟩ : syracuseStep 168431 = 252647) B252647
theorem B168447 : Blo 167798 168447 := bstep (se 1 (by rfl) ⟨126335, by rfl⟩ : syracuseStep 168447 = 252671) B252671
theorem B169051 : Blo 167798 169051 := bstep (se 1 (by rfl) ⟨126788, by rfl⟩ : syracuseStep 169051 = 253577) B253577
theorem B169951 : Blo 167798 169951 := bstep (se 1 (by rfl) ⟨127463, by rfl⟩ : syracuseStep 169951 = 254927) B254927
theorem B42311069 : Blo 167798 42311069 := bstep (se 3 (by rfl) ⟨7933325, by rfl⟩ : syracuseStep 42311069 = 15866651) B15866651
theorem B1090745 : Blo 167798 1090745 := bstep (se 2 (by rfl) ⟨409029, by rfl⟩ : syracuseStep 1090745 = 818059) B818059
theorem B214255 : Blo 167798 214255 := bstep (se 1 (by rfl) ⟨160691, by rfl⟩ : syracuseStep 214255 = 321383) B321383
theorem B1921643 : Blo 167798 1921643 := bstep (se 1 (by rfl) ⟨1441232, by rfl⟩ : syracuseStep 1921643 = 2882465) B2882465
theorem B287401 : Blo 167798 287401 := bstep (se 2 (by rfl) ⟨107775, by rfl⟩ : syracuseStep 287401 = 215551) B215551
theorem B254759 : Blo 167798 254759 := bstep (se 1 (by rfl) ⟨191069, by rfl⟩ : syracuseStep 254759 = 382139) B382139
theorem B980819 : Blo 167798 980819 := bstep (se 1 (by rfl) ⟨735614, by rfl⟩ : syracuseStep 980819 = 1471229) B1471229
theorem B1211719 : Blo 167798 1211719 := bstep (se 1 (by rfl) ⟨908789, by rfl⟩ : syracuseStep 1211719 = 1817579) B1817579
theorem B1441475 : Blo 167798 1441475 := bstep (se 1 (by rfl) ⟨1081106, by rfl⟩ : syracuseStep 1441475 = 2162213) B2162213
theorem B26871911 : Blo 167798 26871911 := bstep (se 1 (by rfl) ⟨20153933, by rfl⟩ : syracuseStep 26871911 = 40307867) B40307867
theorem B1281095 : Blo 167798 1281095 := bstep (se 1 (by rfl) ⟨960821, by rfl⟩ : syracuseStep 1281095 = 1921643) B1921643
theorem B169839 : Blo 167798 169839 := bstep (se 1 (by rfl) ⟨127379, by rfl⟩ : syracuseStep 169839 = 254759) B254759
theorem B727163 : Blo 167798 727163 := bstep (se 1 (by rfl) ⟨545372, by rfl⟩ : syracuseStep 727163 = 1090745) B1090745
theorem B1615625 : Blo 167798 1615625 := bstep (se 2 (by rfl) ⟨605859, by rfl⟩ : syracuseStep 1615625 = 1211719) B1211719
theorem B960983 : Blo 167798 960983 := bstep (se 1 (by rfl) ⟨720737, by rfl⟩ : syracuseStep 960983 = 1441475) B1441475
theorem B571049 : Blo 167798 571049 := bstep (se 2 (by rfl) ⟨214143, by rfl⟩ : syracuseStep 571049 = 428287) B428287
theorem B25646881 : Blo 167798 25646881 := bstep (se 2 (by rfl) ⟨9617580, by rfl⟩ : syracuseStep 25646881 = 19235161) B19235161
theorem B383201 : Blo 167798 383201 := bstep (se 2 (by rfl) ⟨143700, by rfl⟩ : syracuseStep 383201 = 287401) B287401
theorem B285673 : Blo 167798 285673 := bstep (se 2 (by rfl) ⟨107127, by rfl⟩ : syracuseStep 285673 = 214255) B214255
theorem B28207379 : Blo 167798 28207379 := bstep (se 1 (by rfl) ⟨21155534, by rfl⟩ : syracuseStep 28207379 = 42311069) B42311069
theorem B653879 : Blo 167798 653879 := bstep (se 1 (by rfl) ⟨490409, by rfl⟩ : syracuseStep 653879 = 980819) B980819
theorem B854063 : Blo 167798 854063 := bstep (se 1 (by rfl) ⟨640547, by rfl⟩ : syracuseStep 854063 = 1281095) B1281095
theorem B1743677 : Blo 167798 1743677 := bstep (se 3 (by rfl) ⟨326939, by rfl⟩ : syracuseStep 1743677 = 653879) B653879
theorem B640655 : Blo 167798 640655 := bstep (se 1 (by rfl) ⟨480491, by rfl⟩ : syracuseStep 640655 = 960983) B960983
theorem B34195841 : Blo 167798 34195841 := bstep (se 2 (by rfl) ⟨12823440, by rfl⟩ : syracuseStep 34195841 = 25646881) B25646881
theorem B380699 : Blo 167798 380699 := bstep (se 1 (by rfl) ⟨285524, by rfl⟩ : syracuseStep 380699 = 571049) B571049
theorem B380897 : Blo 167798 380897 := bstep (se 2 (by rfl) ⟨142836, by rfl⟩ : syracuseStep 380897 = 285673) B285673
theorem B17914607 : Blo 167798 17914607 := bstep (se 1 (by rfl) ⟨13435955, by rfl⟩ : syracuseStep 17914607 = 26871911) B26871911
theorem B484775 : Blo 167798 484775 := bstep (se 1 (by rfl) ⟨363581, by rfl⟩ : syracuseStep 484775 = 727163) B727163
theorem B255467 : Blo 167798 255467 := bstep (se 1 (by rfl) ⟨191600, by rfl⟩ : syracuseStep 255467 = 383201) B383201
theorem B1077083 : Blo 167798 1077083 := bstep (se 1 (by rfl) ⟨807812, by rfl⟩ : syracuseStep 1077083 = 1615625) B1615625
theorem B18804919 : Blo 167798 18804919 := bstep (se 1 (by rfl) ⟨14103689, by rfl⟩ : syracuseStep 18804919 = 28207379) B28207379
theorem B427103 : Blo 167798 427103 := bstep (se 1 (by rfl) ⟨320327, by rfl⟩ : syracuseStep 427103 = 640655) B640655
theorem B25073225 : Blo 167798 25073225 := bstep (se 2 (by rfl) ⟨9402459, by rfl⟩ : syracuseStep 25073225 = 18804919) B18804919
theorem B170311 : Blo 167798 170311 := bstep (se 1 (by rfl) ⟨127733, by rfl⟩ : syracuseStep 170311 = 255467) B255467
theorem B569375 : Blo 167798 569375 := bstep (se 1 (by rfl) ⟨427031, by rfl⟩ : syracuseStep 569375 = 854063) B854063
theorem B11943071 : Blo 167798 11943071 := bstep (se 1 (by rfl) ⟨8957303, by rfl⟩ : syracuseStep 11943071 = 17914607) B17914607
theorem B1162451 : Blo 167798 1162451 := bstep (se 1 (by rfl) ⟨871838, by rfl⟩ : syracuseStep 1162451 = 1743677) B1743677
theorem B22797227 : Blo 167798 22797227 := bstep (se 1 (by rfl) ⟨17097920, by rfl⟩ : syracuseStep 22797227 = 34195841) B34195841
theorem B253799 : Blo 167798 253799 := bstep (se 1 (by rfl) ⟨190349, by rfl⟩ : syracuseStep 253799 = 380699) B380699
theorem B253931 : Blo 167798 253931 := bstep (se 1 (by rfl) ⟨190448, by rfl⟩ : syracuseStep 253931 = 380897) B380897
theorem B323183 : Blo 167798 323183 := bstep (se 1 (by rfl) ⟨242387, by rfl⟩ : syracuseStep 323183 = 484775) B484775
theorem B718055 : Blo 167798 718055 := bstep (se 1 (by rfl) ⟨538541, by rfl⟩ : syracuseStep 718055 = 1077083) B1077083
theorem B16715483 : Blo 167798 16715483 := bstep (se 1 (by rfl) ⟨12536612, by rfl⟩ : syracuseStep 16715483 = 25073225) B25073225
theorem B169199 : Blo 167798 169199 := bstep (se 1 (by rfl) ⟨126899, by rfl⟩ : syracuseStep 169199 = 253799) B253799
theorem B169287 : Blo 167798 169287 := bstep (se 1 (by rfl) ⟨126965, by rfl⟩ : syracuseStep 169287 = 253931) B253931
theorem B215455 : Blo 167798 215455 := bstep (se 1 (by rfl) ⟨161591, by rfl⟩ : syracuseStep 215455 = 323183) B323183
theorem B379583 : Blo 167798 379583 := bstep (se 1 (by rfl) ⟨284687, by rfl⟩ : syracuseStep 379583 = 569375) B569375
theorem B3099869 : Blo 167798 3099869 := bstep (se 3 (by rfl) ⟨581225, by rfl⟩ : syracuseStep 3099869 = 1162451) B1162451
theorem B478703 : Blo 167798 478703 := bstep (se 1 (by rfl) ⟨359027, by rfl⟩ : syracuseStep 478703 = 718055) B718055
theorem B284735 : Blo 167798 284735 := bstep (se 1 (by rfl) ⟨213551, by rfl⟩ : syracuseStep 284735 = 427103) B427103
theorem B15198151 : Blo 167798 15198151 := bstep (se 1 (by rfl) ⟨11398613, by rfl⟩ : syracuseStep 15198151 = 22797227) B22797227
theorem B7962047 : Blo 167798 7962047 := bstep (se 1 (by rfl) ⟨5971535, by rfl⟩ : syracuseStep 7962047 = 11943071) B11943071
theorem B2066579 : Blo 167798 2066579 := bstep (se 1 (by rfl) ⟨1549934, by rfl⟩ : syracuseStep 2066579 = 3099869) B3099869
theorem B11143655 : Blo 167798 11143655 := bstep (se 1 (by rfl) ⟨8357741, by rfl⟩ : syracuseStep 11143655 = 16715483) B16715483
theorem B20264201 : Blo 167798 20264201 := bstep (se 2 (by rfl) ⟨7599075, by rfl⟩ : syracuseStep 20264201 = 15198151) B15198151
theorem B253055 : Blo 167798 253055 := bstep (se 1 (by rfl) ⟨189791, by rfl⟩ : syracuseStep 253055 = 379583) B379583
theorem B319135 : Blo 167798 319135 := bstep (se 1 (by rfl) ⟨239351, by rfl⟩ : syracuseStep 319135 = 478703) B478703
theorem B287273 : Blo 167798 287273 := bstep (se 2 (by rfl) ⟨107727, by rfl⟩ : syracuseStep 287273 = 215455) B215455
theorem B189823 : Blo 167798 189823 := bstep (se 1 (by rfl) ⟨142367, by rfl⟩ : syracuseStep 189823 = 284735) B284735
theorem B5308031 : Blo 167798 5308031 := bstep (se 1 (by rfl) ⟨3981023, by rfl⟩ : syracuseStep 5308031 = 7962047) B7962047
theorem B1377719 : Blo 167798 1377719 := bstep (se 1 (by rfl) ⟨1033289, by rfl⟩ : syracuseStep 1377719 = 2066579) B2066579
theorem B168703 : Blo 167798 168703 := bstep (se 1 (by rfl) ⟨126527, by rfl⟩ : syracuseStep 168703 = 253055) B253055
theorem B13509467 : Blo 167798 13509467 := bstep (se 1 (by rfl) ⟨10132100, by rfl⟩ : syracuseStep 13509467 = 20264201) B20264201
theorem B7429103 : Blo 167798 7429103 := bstep (se 1 (by rfl) ⟨5571827, by rfl⟩ : syracuseStep 7429103 = 11143655) B11143655
theorem B253097 : Blo 167798 253097 := bstep (se 2 (by rfl) ⟨94911, by rfl⟩ : syracuseStep 253097 = 189823) B189823
theorem B191515 : Blo 167798 191515 := bstep (se 1 (by rfl) ⟨143636, by rfl⟩ : syracuseStep 191515 = 287273) B287273
theorem B425513 : Blo 167798 425513 := bstep (se 2 (by rfl) ⟨159567, by rfl⟩ : syracuseStep 425513 = 319135) B319135
theorem B3538687 : Blo 167798 3538687 := bstep (se 1 (by rfl) ⟨2654015, by rfl⟩ : syracuseStep 3538687 = 5308031) B5308031
theorem B918479 : Blo 167798 918479 := bstep (se 1 (by rfl) ⟨688859, by rfl⟩ : syracuseStep 918479 = 1377719) B1377719
theorem B4952735 : Blo 167798 4952735 := bstep (se 1 (by rfl) ⟨3714551, by rfl⟩ : syracuseStep 4952735 = 7429103) B7429103
theorem B168731 : Blo 167798 168731 := bstep (se 1 (by rfl) ⟨126548, by rfl⟩ : syracuseStep 168731 = 253097) B253097
theorem B283675 : Blo 167798 283675 := bstep (se 1 (by rfl) ⟨212756, by rfl⟩ : syracuseStep 283675 = 425513) B425513
theorem B255353 : Blo 167798 255353 := bstep (se 2 (by rfl) ⟨95757, by rfl⟩ : syracuseStep 255353 = 191515) B191515
theorem B9006311 : Blo 167798 9006311 := bstep (se 1 (by rfl) ⟨6754733, by rfl⟩ : syracuseStep 9006311 = 13509467) B13509467
theorem B4718249 : Blo 167798 4718249 := bstep (se 2 (by rfl) ⟨1769343, by rfl⟩ : syracuseStep 4718249 = 3538687) B3538687
theorem B170235 : Blo 167798 170235 := bstep (se 1 (by rfl) ⟨127676, by rfl⟩ : syracuseStep 170235 = 255353) B255353
theorem B6004207 : Blo 167798 6004207 := bstep (se 1 (by rfl) ⟨4503155, by rfl⟩ : syracuseStep 6004207 = 9006311) B9006311
theorem B378233 : Blo 167798 378233 := bstep (se 2 (by rfl) ⟨141837, by rfl⟩ : syracuseStep 378233 = 283675) B283675
theorem B612319 : Blo 167798 612319 := bstep (se 1 (by rfl) ⟨459239, by rfl⟩ : syracuseStep 612319 = 918479) B918479
theorem B3301823 : Blo 167798 3301823 := bstep (se 1 (by rfl) ⟨2476367, by rfl⟩ : syracuseStep 3301823 = 4952735) B4952735
theorem B3145499 : Blo 167798 3145499 := bstep (se 1 (by rfl) ⟨2359124, by rfl⟩ : syracuseStep 3145499 = 4718249) B4718249
theorem B2201215 : Blo 167798 2201215 := bstep (se 1 (by rfl) ⟨1650911, by rfl⟩ : syracuseStep 2201215 = 3301823) B3301823
theorem B8005609 : Blo 167798 8005609 := bstep (se 2 (by rfl) ⟨3002103, by rfl⟩ : syracuseStep 8005609 = 6004207) B6004207
theorem B252155 : Blo 167798 252155 := bstep (se 1 (by rfl) ⟨189116, by rfl⟩ : syracuseStep 252155 = 378233) B378233
theorem B816425 : Blo 167798 816425 := bstep (se 2 (by rfl) ⟨306159, by rfl⟩ : syracuseStep 816425 = 612319) B612319
theorem B2096999 : Blo 167798 2096999 := bstep (se 1 (by rfl) ⟨1572749, by rfl⟩ : syracuseStep 2096999 = 3145499) B3145499
theorem B168103 : Blo 167798 168103 := bstep (se 1 (by rfl) ⟨126077, by rfl⟩ : syracuseStep 168103 = 252155) B252155
theorem B2934953 : Blo 167798 2934953 := bstep (se 2 (by rfl) ⟨1100607, by rfl⟩ : syracuseStep 2934953 = 2201215) B2201215
theorem B544283 : Blo 167798 544283 := bstep (se 1 (by rfl) ⟨408212, by rfl⟩ : syracuseStep 544283 = 816425) B816425
theorem B1397999 : Blo 167798 1397999 := bstep (se 1 (by rfl) ⟨1048499, by rfl⟩ : syracuseStep 1397999 = 2096999) B2096999
theorem B10674145 : Blo 167798 10674145 := bstep (se 2 (by rfl) ⟨4002804, by rfl⟩ : syracuseStep 10674145 = 8005609) B8005609
theorem B362855 : Blo 167798 362855 := bstep (se 1 (by rfl) ⟨272141, by rfl⟩ : syracuseStep 362855 = 544283) B544283
theorem B14232193 : Blo 167798 14232193 := bstep (se 2 (by rfl) ⟨5337072, by rfl⟩ : syracuseStep 14232193 = 10674145) B10674145
theorem B931999 : Blo 167798 931999 := bstep (se 1 (by rfl) ⟨698999, by rfl⟩ : syracuseStep 931999 = 1397999) B1397999
theorem B1956635 : Blo 167798 1956635 := bstep (se 1 (by rfl) ⟨1467476, by rfl⟩ : syracuseStep 1956635 = 2934953) B2934953
theorem B241903 : Blo 167798 241903 := bstep (se 1 (by rfl) ⟨181427, by rfl⟩ : syracuseStep 241903 = 362855) B362855
theorem B75905029 : Blo 167798 75905029 := bstep (se 4 (by rfl) ⟨7116096, by rfl⟩ : syracuseStep 75905029 = 14232193) B14232193
theorem B1304423 : Blo 167798 1304423 := bstep (se 1 (by rfl) ⟨978317, by rfl⟩ : syracuseStep 1304423 = 1956635) B1956635
theorem B1242665 : Blo 167798 1242665 := bstep (se 2 (by rfl) ⟨465999, by rfl⟩ : syracuseStep 1242665 = 931999) B931999
theorem B828443 : Blo 167798 828443 := bstep (se 1 (by rfl) ⟨621332, by rfl⟩ : syracuseStep 828443 = 1242665) B1242665
theorem B869615 : Blo 167798 869615 := bstep (se 1 (by rfl) ⟨652211, by rfl⟩ : syracuseStep 869615 = 1304423) B1304423
theorem B101206705 : Blo 167798 101206705 := bstep (se 2 (by rfl) ⟨37952514, by rfl⟩ : syracuseStep 101206705 = 75905029) B75905029
theorem B322537 : Blo 167798 322537 := bstep (se 2 (by rfl) ⟨120951, by rfl⟩ : syracuseStep 322537 = 241903) B241903
theorem B134942273 : Blo 167798 134942273 := bstep (se 2 (by rfl) ⟨50603352, by rfl⟩ : syracuseStep 134942273 = 101206705) B101206705
theorem B430049 : Blo 167798 430049 := bstep (se 2 (by rfl) ⟨161268, by rfl⟩ : syracuseStep 430049 = 322537) B322537
theorem B579743 : Blo 167798 579743 := bstep (se 1 (by rfl) ⟨434807, by rfl⟩ : syracuseStep 579743 = 869615) B869615
theorem B552295 : Blo 167798 552295 := bstep (se 1 (by rfl) ⟨414221, by rfl⟩ : syracuseStep 552295 = 828443) B828443
theorem B89961515 : Blo 167798 89961515 := bstep (se 1 (by rfl) ⟨67471136, by rfl⟩ : syracuseStep 89961515 = 134942273) B134942273
theorem B736393 : Blo 167798 736393 := bstep (se 2 (by rfl) ⟨276147, by rfl⟩ : syracuseStep 736393 = 552295) B552295
theorem B286699 : Blo 167798 286699 := bstep (se 1 (by rfl) ⟨215024, by rfl⟩ : syracuseStep 286699 = 430049) B430049
theorem B386495 : Blo 167798 386495 := bstep (se 1 (by rfl) ⟨289871, by rfl⟩ : syracuseStep 386495 = 579743) B579743
theorem B59974343 : Blo 167798 59974343 := bstep (se 1 (by rfl) ⟨44980757, by rfl⟩ : syracuseStep 59974343 = 89961515) B89961515
theorem B382265 : Blo 167798 382265 := bstep (se 2 (by rfl) ⟨143349, by rfl⟩ : syracuseStep 382265 = 286699) B286699
theorem B257663 : Blo 167798 257663 := bstep (se 1 (by rfl) ⟨193247, by rfl⟩ : syracuseStep 257663 = 386495) B386495
theorem B981857 : Blo 167798 981857 := bstep (se 2 (by rfl) ⟨368196, by rfl⟩ : syracuseStep 981857 = 736393) B736393
theorem B39982895 : Blo 167798 39982895 := bstep (se 1 (by rfl) ⟨29987171, by rfl⟩ : syracuseStep 39982895 = 59974343) B59974343
theorem B171775 : Blo 167798 171775 := bstep (se 1 (by rfl) ⟨128831, by rfl⟩ : syracuseStep 171775 = 257663) B257663
theorem B254843 : Blo 167798 254843 := bstep (se 1 (by rfl) ⟨191132, by rfl⟩ : syracuseStep 254843 = 382265) B382265
theorem B654571 : Blo 167798 654571 := bstep (se 1 (by rfl) ⟨490928, by rfl⟩ : syracuseStep 654571 = 981857) B981857
theorem B169895 : Blo 167798 169895 := bstep (se 1 (by rfl) ⟨127421, by rfl⟩ : syracuseStep 169895 = 254843) B254843
theorem B26655263 : Blo 167798 26655263 := bstep (se 1 (by rfl) ⟨19991447, by rfl⟩ : syracuseStep 26655263 = 39982895) B39982895
theorem B3491045 : Blo 167798 3491045 := bstep (se 4 (by rfl) ⟨327285, by rfl⟩ : syracuseStep 3491045 = 654571) B654571
theorem B2327363 : Blo 167798 2327363 := bstep (se 1 (by rfl) ⟨1745522, by rfl⟩ : syracuseStep 2327363 = 3491045) B3491045
theorem B17770175 : Blo 167798 17770175 := bstep (se 1 (by rfl) ⟨13327631, by rfl⟩ : syracuseStep 17770175 = 26655263) B26655263
theorem B1551575 : Blo 167798 1551575 := bstep (se 1 (by rfl) ⟨1163681, by rfl⟩ : syracuseStep 1551575 = 2327363) B2327363
theorem B11846783 : Blo 167798 11846783 := bstep (se 1 (by rfl) ⟨8885087, by rfl⟩ : syracuseStep 11846783 = 17770175) B17770175
theorem B31591421 : Blo 167798 31591421 := bstep (se 3 (by rfl) ⟨5923391, by rfl⟩ : syracuseStep 31591421 = 11846783) B11846783
theorem B1034383 : Blo 167798 1034383 := bstep (se 1 (by rfl) ⟨775787, by rfl⟩ : syracuseStep 1034383 = 1551575) B1551575
theorem B1379177 : Blo 167798 1379177 := bstep (se 2 (by rfl) ⟨517191, by rfl⟩ : syracuseStep 1379177 = 1034383) B1034383
theorem B21060947 : Blo 167798 21060947 := bstep (se 1 (by rfl) ⟨15795710, by rfl⟩ : syracuseStep 21060947 = 31591421) B31591421
theorem B919451 : Blo 167798 919451 := bstep (se 1 (by rfl) ⟨689588, by rfl⟩ : syracuseStep 919451 = 1379177) B1379177
theorem B14040631 : Blo 167798 14040631 := bstep (se 1 (by rfl) ⟨10530473, by rfl⟩ : syracuseStep 14040631 = 21060947) B21060947
theorem B18720841 : Blo 167798 18720841 := bstep (se 2 (by rfl) ⟨7020315, by rfl⟩ : syracuseStep 18720841 = 14040631) B14040631
theorem B2451869 : Blo 167798 2451869 := bstep (se 3 (by rfl) ⟨459725, by rfl⟩ : syracuseStep 2451869 = 919451) B919451
theorem B24961121 : Blo 167798 24961121 := bstep (se 2 (by rfl) ⟨9360420, by rfl⟩ : syracuseStep 24961121 = 18720841) B18720841
theorem B1634579 : Blo 167798 1634579 := bstep (se 1 (by rfl) ⟨1225934, by rfl⟩ : syracuseStep 1634579 = 2451869) B2451869
theorem B1089719 : Blo 167798 1089719 := bstep (se 1 (by rfl) ⟨817289, by rfl⟩ : syracuseStep 1089719 = 1634579) B1634579
theorem B16640747 : Blo 167798 16640747 := bstep (se 1 (by rfl) ⟨12480560, by rfl⟩ : syracuseStep 16640747 = 24961121) B24961121
theorem B726479 : Blo 167798 726479 := bstep (se 1 (by rfl) ⟨544859, by rfl⟩ : syracuseStep 726479 = 1089719) B1089719
theorem B11093831 : Blo 167798 11093831 := bstep (se 1 (by rfl) ⟨8320373, by rfl⟩ : syracuseStep 11093831 = 16640747) B16640747
theorem B7395887 : Blo 167798 7395887 := bstep (se 1 (by rfl) ⟨5546915, by rfl⟩ : syracuseStep 7395887 = 11093831) B11093831
theorem B484319 : Blo 167798 484319 := bstep (se 1 (by rfl) ⟨363239, by rfl⟩ : syracuseStep 484319 = 726479) B726479
theorem B4930591 : Blo 167798 4930591 := bstep (se 1 (by rfl) ⟨3697943, by rfl⟩ : syracuseStep 4930591 = 7395887) B7395887
theorem B322879 : Blo 167798 322879 := bstep (se 1 (by rfl) ⟨242159, by rfl⟩ : syracuseStep 322879 = 484319) B484319
theorem B430505 : Blo 167798 430505 := bstep (se 2 (by rfl) ⟨161439, by rfl⟩ : syracuseStep 430505 = 322879) B322879
theorem B6574121 : Blo 167798 6574121 := bstep (se 2 (by rfl) ⟨2465295, by rfl⟩ : syracuseStep 6574121 = 4930591) B4930591
theorem B4382747 : Blo 167798 4382747 := bstep (se 1 (by rfl) ⟨3287060, by rfl⟩ : syracuseStep 4382747 = 6574121) B6574121
theorem B287003 : Blo 167798 287003 := bstep (se 1 (by rfl) ⟨215252, by rfl⟩ : syracuseStep 287003 = 430505) B430505
theorem B2921831 : Blo 167798 2921831 := bstep (se 1 (by rfl) ⟨2191373, by rfl⟩ : syracuseStep 2921831 = 4382747) B4382747
theorem B191335 : Blo 167798 191335 := bstep (se 1 (by rfl) ⟨143501, by rfl⟩ : syracuseStep 191335 = 287003) B287003
theorem B1947887 : Blo 167798 1947887 := bstep (se 1 (by rfl) ⟨1460915, by rfl⟩ : syracuseStep 1947887 = 2921831) B2921831
theorem B255113 : Blo 167798 255113 := bstep (se 2 (by rfl) ⟨95667, by rfl⟩ : syracuseStep 255113 = 191335) B191335
theorem B170075 : Blo 167798 170075 := bstep (se 1 (by rfl) ⟨127556, by rfl⟩ : syracuseStep 170075 = 255113) B255113
theorem B1298591 : Blo 167798 1298591 := bstep (se 1 (by rfl) ⟨973943, by rfl⟩ : syracuseStep 1298591 = 1947887) B1947887
theorem B865727 : Blo 167798 865727 := bstep (se 1 (by rfl) ⟨649295, by rfl⟩ : syracuseStep 865727 = 1298591) B1298591
theorem B577151 : Blo 167798 577151 := bstep (se 1 (by rfl) ⟨432863, by rfl⟩ : syracuseStep 577151 = 865727) B865727
theorem B384767 : Blo 167798 384767 := bstep (se 1 (by rfl) ⟨288575, by rfl⟩ : syracuseStep 384767 = 577151) B577151
theorem B256511 : Blo 167798 256511 := bstep (se 1 (by rfl) ⟨192383, by rfl⟩ : syracuseStep 256511 = 384767) B384767
theorem B171007 : Blo 167798 171007 := bstep (se 1 (by rfl) ⟨128255, by rfl⟩ : syracuseStep 171007 = 256511) B256511

theorem C0 (j : ℕ) (h1 : 41949 ≤ j) (h2 : j ≤ 42648) : Blo 167798 (4 * j + 3) := by
  interval_cases j
  · exact B167799
  · exact B167803
  · exact B167807
  · exact B167811
  · exact B167815
  · exact B167819
  · exact B167823
  · exact B167827
  · exact B167831
  · exact B167835
  · exact B167839
  · exact B167843
  · exact B167847
  · exact B167851
  · exact B167855
  · exact B167859
  · exact B167863
  · exact B167867
  · exact B167871
  · exact B167875
  · exact B167879
  · exact B167883
  · exact B167887
  · exact B167891
  · exact B167895
  · exact B167899
  · exact B167903
  · exact B167907
  · exact B167911
  · exact B167915
  · exact B167919
  · exact B167923
  · exact B167927
  · exact B167931
  · exact B167935
  · exact B167939
  · exact B167943
  · exact B167947
  · exact B167951
  · exact B167955
  · exact B167959
  · exact B167963
  · exact B167967
  · exact B167971
  · exact B167975
  · exact B167979
  · exact B167983
  · exact B167987
  · exact B167991
  · exact B167995
  · exact B167999
  · exact B168003
  · exact B168007
  · exact B168011
  · exact B168015
  · exact B168019
  · exact B168023
  · exact B168027
  · exact B168031
  · exact B168035
  · exact B168039
  · exact B168043
  · exact B168047
  · exact B168051
  · exact B168055
  · exact B168059
  · exact B168063
  · exact B168067
  · exact B168071
  · exact B168075
  · exact B168079
  · exact B168083
  · exact B168087
  · exact B168091
  · exact B168095
  · exact B168099
  · exact B168103
  · exact B168107
  · exact B168111
  · exact B168115
  · exact B168119
  · exact B168123
  · exact B168127
  · exact B168131
  · exact B168135
  · exact B168139
  · exact B168143
  · exact B168147
  · exact B168151
  · exact B168155
  · exact B168159
  · exact B168163
  · exact B168167
  · exact B168171
  · exact B168175
  · exact B168179
  · exact B168183
  · exact B168187
  · exact B168191
  · exact B168195
  · exact B168199
  · exact B168203
  · exact B168207
  · exact B168211
  · exact B168215
  · exact B168219
  · exact B168223
  · exact B168227
  · exact B168231
  · exact B168235
  · exact B168239
  · exact B168243
  · exact B168247
  · exact B168251
  · exact B168255
  · exact B168259
  · exact B168263
  · exact B168267
  · exact B168271
  · exact B168275
  · exact B168279
  · exact B168283
  · exact B168287
  · exact B168291
  · exact B168295
  · exact B168299
  · exact B168303
  · exact B168307
  · exact B168311
  · exact B168315
  · exact B168319
  · exact B168323
  · exact B168327
  · exact B168331
  · exact B168335
  · exact B168339
  · exact B168343
  · exact B168347
  · exact B168351
  · exact B168355
  · exact B168359
  · exact B168363
  · exact B168367
  · exact B168371
  · exact B168375
  · exact B168379
  · exact B168383
  · exact B168387
  · exact B168391
  · exact B168395
  · exact B168399
  · exact B168403
  · exact B168407
  · exact B168411
  · exact B168415
  · exact B168419
  · exact B168423
  · exact B168427
  · exact B168431
  · exact B168435
  · exact B168439
  · exact B168443
  · exact B168447
  · exact B168451
  · exact B168455
  · exact B168459
  · exact B168463
  · exact B168467
  · exact B168471
  · exact B168475
  · exact B168479
  · exact B168483
  · exact B168487
  · exact B168491
  · exact B168495
  · exact B168499
  · exact B168503
  · exact B168507
  · exact B168511
  · exact B168515
  · exact B168519
  · exact B168523
  · exact B168527
  · exact B168531
  · exact B168535
  · exact B168539
  · exact B168543
  · exact B168547
  · exact B168551
  · exact B168555
  · exact B168559
  · exact B168563
  · exact B168567
  · exact B168571
  · exact B168575
  · exact B168579
  · exact B168583
  · exact B168587
  · exact B168591
  · exact B168595
  · exact B168599
  · exact B168603
  · exact B168607
  · exact B168611
  · exact B168615
  · exact B168619
  · exact B168623
  · exact B168627
  · exact B168631
  · exact B168635
  · exact B168639
  · exact B168643
  · exact B168647
  · exact B168651
  · exact B168655
  · exact B168659
  · exact B168663
  · exact B168667
  · exact B168671
  · exact B168675
  · exact B168679
  · exact B168683
  · exact B168687
  · exact B168691
  · exact B168695
  · exact B168699
  · exact B168703
  · exact B168707
  · exact B168711
  · exact B168715
  · exact B168719
  · exact B168723
  · exact B168727
  · exact B168731
  · exact B168735
  · exact B168739
  · exact B168743
  · exact B168747
  · exact B168751
  · exact B168755
  · exact B168759
  · exact B168763
  · exact B168767
  · exact B168771
  · exact B168775
  · exact B168779
  · exact B168783
  · exact B168787
  · exact B168791
  · exact B168795
  · exact B168799
  · exact B168803
  · exact B168807
  · exact B168811
  · exact B168815
  · exact B168819
  · exact B168823
  · exact B168827
  · exact B168831
  · exact B168835
  · exact B168839
  · exact B168843
  · exact B168847
  · exact B168851
  · exact B168855
  · exact B168859
  · exact B168863
  · exact B168867
  · exact B168871
  · exact B168875
  · exact B168879
  · exact B168883
  · exact B168887
  · exact B168891
  · exact B168895
  · exact B168899
  · exact B168903
  · exact B168907
  · exact B168911
  · exact B168915
  · exact B168919
  · exact B168923
  · exact B168927
  · exact B168931
  · exact B168935
  · exact B168939
  · exact B168943
  · exact B168947
  · exact B168951
  · exact B168955
  · exact B168959
  · exact B168963
  · exact B168967
  · exact B168971
  · exact B168975
  · exact B168979
  · exact B168983
  · exact B168987
  · exact B168991
  · exact B168995
  · exact B168999
  · exact B169003
  · exact B169007
  · exact B169011
  · exact B169015
  · exact B169019
  · exact B169023
  · exact B169027
  · exact B169031
  · exact B169035
  · exact B169039
  · exact B169043
  · exact B169047
  · exact B169051
  · exact B169055
  · exact B169059
  · exact B169063
  · exact B169067
  · exact B169071
  · exact B169075
  · exact B169079
  · exact B169083
  · exact B169087
  · exact B169091
  · exact B169095
  · exact B169099
  · exact B169103
  · exact B169107
  · exact B169111
  · exact B169115
  · exact B169119
  · exact B169123
  · exact B169127
  · exact B169131
  · exact B169135
  · exact B169139
  · exact B169143
  · exact B169147
  · exact B169151
  · exact B169155
  · exact B169159
  · exact B169163
  · exact B169167
  · exact B169171
  · exact B169175
  · exact B169179
  · exact B169183
  · exact B169187
  · exact B169191
  · exact B169195
  · exact B169199
  · exact B169203
  · exact B169207
  · exact B169211
  · exact B169215
  · exact B169219
  · exact B169223
  · exact B169227
  · exact B169231
  · exact B169235
  · exact B169239
  · exact B169243
  · exact B169247
  · exact B169251
  · exact B169255
  · exact B169259
  · exact B169263
  · exact B169267
  · exact B169271
  · exact B169275
  · exact B169279
  · exact B169283
  · exact B169287
  · exact B169291
  · exact B169295
  · exact B169299
  · exact B169303
  · exact B169307
  · exact B169311
  · exact B169315
  · exact B169319
  · exact B169323
  · exact B169327
  · exact B169331
  · exact B169335
  · exact B169339
  · exact B169343
  · exact B169347
  · exact B169351
  · exact B169355
  · exact B169359
  · exact B169363
  · exact B169367
  · exact B169371
  · exact B169375
  · exact B169379
  · exact B169383
  · exact B169387
  · exact B169391
  · exact B169395
  · exact B169399
  · exact B169403
  · exact B169407
  · exact B169411
  · exact B169415
  · exact B169419
  · exact B169423
  · exact B169427
  · exact B169431
  · exact B169435
  · exact B169439
  · exact B169443
  · exact B169447
  · exact B169451
  · exact B169455
  · exact B169459
  · exact B169463
  · exact B169467
  · exact B169471
  · exact B169475
  · exact B169479
  · exact B169483
  · exact B169487
  · exact B169491
  · exact B169495
  · exact B169499
  · exact B169503
  · exact B169507
  · exact B169511
  · exact B169515
  · exact B169519
  · exact B169523
  · exact B169527
  · exact B169531
  · exact B169535
  · exact B169539
  · exact B169543
  · exact B169547
  · exact B169551
  · exact B169555
  · exact B169559
  · exact B169563
  · exact B169567
  · exact B169571
  · exact B169575
  · exact B169579
  · exact B169583
  · exact B169587
  · exact B169591
  · exact B169595
  · exact B169599
  · exact B169603
  · exact B169607
  · exact B169611
  · exact B169615
  · exact B169619
  · exact B169623
  · exact B169627
  · exact B169631
  · exact B169635
  · exact B169639
  · exact B169643
  · exact B169647
  · exact B169651
  · exact B169655
  · exact B169659
  · exact B169663
  · exact B169667
  · exact B169671
  · exact B169675
  · exact B169679
  · exact B169683
  · exact B169687
  · exact B169691
  · exact B169695
  · exact B169699
  · exact B169703
  · exact B169707
  · exact B169711
  · exact B169715
  · exact B169719
  · exact B169723
  · exact B169727
  · exact B169731
  · exact B169735
  · exact B169739
  · exact B169743
  · exact B169747
  · exact B169751
  · exact B169755
  · exact B169759
  · exact B169763
  · exact B169767
  · exact B169771
  · exact B169775
  · exact B169779
  · exact B169783
  · exact B169787
  · exact B169791
  · exact B169795
  · exact B169799
  · exact B169803
  · exact B169807
  · exact B169811
  · exact B169815
  · exact B169819
  · exact B169823
  · exact B169827
  · exact B169831
  · exact B169835
  · exact B169839
  · exact B169843
  · exact B169847
  · exact B169851
  · exact B169855
  · exact B169859
  · exact B169863
  · exact B169867
  · exact B169871
  · exact B169875
  · exact B169879
  · exact B169883
  · exact B169887
  · exact B169891
  · exact B169895
  · exact B169899
  · exact B169903
  · exact B169907
  · exact B169911
  · exact B169915
  · exact B169919
  · exact B169923
  · exact B169927
  · exact B169931
  · exact B169935
  · exact B169939
  · exact B169943
  · exact B169947
  · exact B169951
  · exact B169955
  · exact B169959
  · exact B169963
  · exact B169967
  · exact B169971
  · exact B169975
  · exact B169979
  · exact B169983
  · exact B169987
  · exact B169991
  · exact B169995
  · exact B169999
  · exact B170003
  · exact B170007
  · exact B170011
  · exact B170015
  · exact B170019
  · exact B170023
  · exact B170027
  · exact B170031
  · exact B170035
  · exact B170039
  · exact B170043
  · exact B170047
  · exact B170051
  · exact B170055
  · exact B170059
  · exact B170063
  · exact B170067
  · exact B170071
  · exact B170075
  · exact B170079
  · exact B170083
  · exact B170087
  · exact B170091
  · exact B170095
  · exact B170099
  · exact B170103
  · exact B170107
  · exact B170111
  · exact B170115
  · exact B170119
  · exact B170123
  · exact B170127
  · exact B170131
  · exact B170135
  · exact B170139
  · exact B170143
  · exact B170147
  · exact B170151
  · exact B170155
  · exact B170159
  · exact B170163
  · exact B170167
  · exact B170171
  · exact B170175
  · exact B170179
  · exact B170183
  · exact B170187
  · exact B170191
  · exact B170195
  · exact B170199
  · exact B170203
  · exact B170207
  · exact B170211
  · exact B170215
  · exact B170219
  · exact B170223
  · exact B170227
  · exact B170231
  · exact B170235
  · exact B170239
  · exact B170243
  · exact B170247
  · exact B170251
  · exact B170255
  · exact B170259
  · exact B170263
  · exact B170267
  · exact B170271
  · exact B170275
  · exact B170279
  · exact B170283
  · exact B170287
  · exact B170291
  · exact B170295
  · exact B170299
  · exact B170303
  · exact B170307
  · exact B170311
  · exact B170315
  · exact B170319
  · exact B170323
  · exact B170327
  · exact B170331
  · exact B170335
  · exact B170339
  · exact B170343
  · exact B170347
  · exact B170351
  · exact B170355
  · exact B170359
  · exact B170363
  · exact B170367
  · exact B170371
  · exact B170375
  · exact B170379
  · exact B170383
  · exact B170387
  · exact B170391
  · exact B170395
  · exact B170399
  · exact B170403
  · exact B170407
  · exact B170411
  · exact B170415
  · exact B170419
  · exact B170423
  · exact B170427
  · exact B170431
  · exact B170435
  · exact B170439
  · exact B170443
  · exact B170447
  · exact B170451
  · exact B170455
  · exact B170459
  · exact B170463
  · exact B170467
  · exact B170471
  · exact B170475
  · exact B170479
  · exact B170483
  · exact B170487
  · exact B170491
  · exact B170495
  · exact B170499
  · exact B170503
  · exact B170507
  · exact B170511
  · exact B170515
  · exact B170519
  · exact B170523
  · exact B170527
  · exact B170531
  · exact B170535
  · exact B170539
  · exact B170543
  · exact B170547
  · exact B170551
  · exact B170555
  · exact B170559
  · exact B170563
  · exact B170567
  · exact B170571
  · exact B170575
  · exact B170579
  · exact B170583
  · exact B170587
  · exact B170591
  · exact B170595

theorem C1 (j : ℕ) (h1 : 42649 ≤ j) (h2 : j ≤ 42948) : Blo 167798 (4 * j + 3) := by
  interval_cases j
  · exact B170599
  · exact B170603
  · exact B170607
  · exact B170611
  · exact B170615
  · exact B170619
  · exact B170623
  · exact B170627
  · exact B170631
  · exact B170635
  · exact B170639
  · exact B170643
  · exact B170647
  · exact B170651
  · exact B170655
  · exact B170659
  · exact B170663
  · exact B170667
  · exact B170671
  · exact B170675
  · exact B170679
  · exact B170683
  · exact B170687
  · exact B170691
  · exact B170695
  · exact B170699
  · exact B170703
  · exact B170707
  · exact B170711
  · exact B170715
  · exact B170719
  · exact B170723
  · exact B170727
  · exact B170731
  · exact B170735
  · exact B170739
  · exact B170743
  · exact B170747
  · exact B170751
  · exact B170755
  · exact B170759
  · exact B170763
  · exact B170767
  · exact B170771
  · exact B170775
  · exact B170779
  · exact B170783
  · exact B170787
  · exact B170791
  · exact B170795
  · exact B170799
  · exact B170803
  · exact B170807
  · exact B170811
  · exact B170815
  · exact B170819
  · exact B170823
  · exact B170827
  · exact B170831
  · exact B170835
  · exact B170839
  · exact B170843
  · exact B170847
  · exact B170851
  · exact B170855
  · exact B170859
  · exact B170863
  · exact B170867
  · exact B170871
  · exact B170875
  · exact B170879
  · exact B170883
  · exact B170887
  · exact B170891
  · exact B170895
  · exact B170899
  · exact B170903
  · exact B170907
  · exact B170911
  · exact B170915
  · exact B170919
  · exact B170923
  · exact B170927
  · exact B170931
  · exact B170935
  · exact B170939
  · exact B170943
  · exact B170947
  · exact B170951
  · exact B170955
  · exact B170959
  · exact B170963
  · exact B170967
  · exact B170971
  · exact B170975
  · exact B170979
  · exact B170983
  · exact B170987
  · exact B170991
  · exact B170995
  · exact B170999
  · exact B171003
  · exact B171007
  · exact B171011
  · exact B171015
  · exact B171019
  · exact B171023
  · exact B171027
  · exact B171031
  · exact B171035
  · exact B171039
  · exact B171043
  · exact B171047
  · exact B171051
  · exact B171055
  · exact B171059
  · exact B171063
  · exact B171067
  · exact B171071
  · exact B171075
  · exact B171079
  · exact B171083
  · exact B171087
  · exact B171091
  · exact B171095
  · exact B171099
  · exact B171103
  · exact B171107
  · exact B171111
  · exact B171115
  · exact B171119
  · exact B171123
  · exact B171127
  · exact B171131
  · exact B171135
  · exact B171139
  · exact B171143
  · exact B171147
  · exact B171151
  · exact B171155
  · exact B171159
  · exact B171163
  · exact B171167
  · exact B171171
  · exact B171175
  · exact B171179
  · exact B171183
  · exact B171187
  · exact B171191
  · exact B171195
  · exact B171199
  · exact B171203
  · exact B171207
  · exact B171211
  · exact B171215
  · exact B171219
  · exact B171223
  · exact B171227
  · exact B171231
  · exact B171235
  · exact B171239
  · exact B171243
  · exact B171247
  · exact B171251
  · exact B171255
  · exact B171259
  · exact B171263
  · exact B171267
  · exact B171271
  · exact B171275
  · exact B171279
  · exact B171283
  · exact B171287
  · exact B171291
  · exact B171295
  · exact B171299
  · exact B171303
  · exact B171307
  · exact B171311
  · exact B171315
  · exact B171319
  · exact B171323
  · exact B171327
  · exact B171331
  · exact B171335
  · exact B171339
  · exact B171343
  · exact B171347
  · exact B171351
  · exact B171355
  · exact B171359
  · exact B171363
  · exact B171367
  · exact B171371
  · exact B171375
  · exact B171379
  · exact B171383
  · exact B171387
  · exact B171391
  · exact B171395
  · exact B171399
  · exact B171403
  · exact B171407
  · exact B171411
  · exact B171415
  · exact B171419
  · exact B171423
  · exact B171427
  · exact B171431
  · exact B171435
  · exact B171439
  · exact B171443
  · exact B171447
  · exact B171451
  · exact B171455
  · exact B171459
  · exact B171463
  · exact B171467
  · exact B171471
  · exact B171475
  · exact B171479
  · exact B171483
  · exact B171487
  · exact B171491
  · exact B171495
  · exact B171499
  · exact B171503
  · exact B171507
  · exact B171511
  · exact B171515
  · exact B171519
  · exact B171523
  · exact B171527
  · exact B171531
  · exact B171535
  · exact B171539
  · exact B171543
  · exact B171547
  · exact B171551
  · exact B171555
  · exact B171559
  · exact B171563
  · exact B171567
  · exact B171571
  · exact B171575
  · exact B171579
  · exact B171583
  · exact B171587
  · exact B171591
  · exact B171595
  · exact B171599
  · exact B171603
  · exact B171607
  · exact B171611
  · exact B171615
  · exact B171619
  · exact B171623
  · exact B171627
  · exact B171631
  · exact B171635
  · exact B171639
  · exact B171643
  · exact B171647
  · exact B171651
  · exact B171655
  · exact B171659
  · exact B171663
  · exact B171667
  · exact B171671
  · exact B171675
  · exact B171679
  · exact B171683
  · exact B171687
  · exact B171691
  · exact B171695
  · exact B171699
  · exact B171703
  · exact B171707
  · exact B171711
  · exact B171715
  · exact B171719
  · exact B171723
  · exact B171727
  · exact B171731
  · exact B171735
  · exact B171739
  · exact B171743
  · exact B171747
  · exact B171751
  · exact B171755
  · exact B171759
  · exact B171763
  · exact B171767
  · exact B171771
  · exact B171775
  · exact B171779
  · exact B171783
  · exact B171787
  · exact B171791
  · exact B171795

theorem solution (m : ℕ) (hlo : 167798 ≤ m) (hhi : m ≤ 171798) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 41949 ≤ j := by omega
    have hj2 : j ≤ 42948 := by omega
    have hb : Blo 167798 (4 * j + 3) := by
      rcases Nat.lt_or_ge j 42649 with hc0 | hc0
      · exact C0 j (by omega) (by omega)
      exact C1 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
