-- Prove2me | solution 1 for syracuse_descends_range_810345_814345
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-09T19:05:43.035235+00:00
-- url     : https://prove2.me/submissions/31366e1c-d217-462e-aa3b-204ef3f022cd

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


theorem B3080389 : Blo 810345 3080389 := bbase (se 4 (by rfl) ⟨288786, by rfl⟩ : syracuseStep 3080389 = 577573) (by norm_num)
theorem B1540309 : Blo 810345 1540309 := bbase (se 7 (by rfl) ⟨18050, by rfl⟩ : syracuseStep 1540309 = 36101) (by norm_num)
theorem B1736957 : Blo 810345 1736957 := bbase (se 3 (by rfl) ⟨325679, by rfl⟩ : syracuseStep 1736957 = 651359) (by norm_num)
theorem B13861205 : Blo 810345 13861205 := bbase (se 10 (by rfl) ⟨20304, by rfl⟩ : syracuseStep 13861205 = 40609) (by norm_num)
theorem B1540453 : Blo 810345 1540453 := bbase (se 4 (by rfl) ⟨144417, by rfl⟩ : syracuseStep 1540453 = 288835) (by norm_num)
theorem B1671637 : Blo 810345 1671637 := bbase (se 7 (by rfl) ⟨19589, by rfl⟩ : syracuseStep 1671637 = 39179) (by norm_num)
theorem B3080693 : Blo 810345 3080693 := bbase (se 5 (by rfl) ⟨144407, by rfl⟩ : syracuseStep 3080693 = 288815) (by norm_num)
theorem B1540613 : Blo 810345 1540613 := bbase (se 4 (by rfl) ⟨144432, by rfl⟩ : syracuseStep 1540613 = 288865) (by norm_num)
theorem B1540757 : Blo 810345 1540757 := bbase (se 6 (by rfl) ⟨36111, by rfl⟩ : syracuseStep 1540757 = 72223) (by norm_num)
theorem B8356661 : Blo 810345 8356661 := bbase (se 5 (by rfl) ⟨391718, by rfl⟩ : syracuseStep 8356661 = 783437) (by norm_num)
theorem B1541045 : Blo 810345 1541045 := bbase (se 5 (by rfl) ⟨72236, by rfl⟩ : syracuseStep 1541045 = 144473) (by norm_num)
theorem B6783925 : Blo 810345 6783925 := bbase (se 5 (by rfl) ⟨317996, by rfl⟩ : syracuseStep 6783925 = 635993) (by norm_num)
theorem B1541197 : Blo 810345 1541197 := bbase (se 3 (by rfl) ⟨288974, by rfl⟩ : syracuseStep 1541197 = 577949) (by norm_num)
theorem B5866613 : Blo 810345 5866613 := bbase (se 5 (by rfl) ⟨274997, by rfl⟩ : syracuseStep 5866613 = 549995) (by norm_num)
theorem B2196629 : Blo 810345 2196629 := bbase (se 6 (by rfl) ⟨51483, by rfl⟩ : syracuseStep 2196629 = 102967) (by norm_num)
theorem B5276981 : Blo 810345 5276981 := bbase (se 5 (by rfl) ⟨247358, by rfl⟩ : syracuseStep 5276981 = 494717) (by norm_num)
theorem B1541501 : Blo 810345 1541501 := bbase (se 3 (by rfl) ⟨289031, by rfl⟩ : syracuseStep 1541501 = 578063) (by norm_num)
theorem B5866901 : Blo 810345 5866901 := bbase (se 6 (by rfl) ⟨137505, by rfl⟩ : syracuseStep 5866901 = 275011) (by norm_num)
theorem B6948341 : Blo 810345 6948341 := bbase (se 5 (by rfl) ⟨325703, by rfl⟩ : syracuseStep 6948341 = 651407) (by norm_num)
theorem B3901061 : Blo 810345 3901061 := bbase (se 4 (by rfl) ⟨365724, by rfl⟩ : syracuseStep 3901061 = 731449) (by norm_num)
theorem B9242261 : Blo 810345 9242261 := bbase (se 6 (by rfl) ⟨216615, by rfl⟩ : syracuseStep 9242261 = 433231) (by norm_num)
theorem B3606245 : Blo 810345 3606245 := bbase (se 4 (by rfl) ⟨338085, by rfl⟩ : syracuseStep 3606245 = 676171) (by norm_num)
theorem B1738597 : Blo 810345 1738597 := bbase (se 4 (by rfl) ⟨162993, by rfl⟩ : syracuseStep 1738597 = 325987) (by norm_num)
theorem B3475349 : Blo 810345 3475349 := bbase (se 6 (by rfl) ⟨81453, by rfl⟩ : syracuseStep 3475349 = 162907) (by norm_num)
theorem B1017937 : Blo 810345 1017937 := bbase (se 2 (by rfl) ⟨381726, by rfl⟩ : syracuseStep 1017937 = 763453) (by norm_num)
theorem B1542253 : Blo 810345 1542253 := bbase (se 3 (by rfl) ⟨289172, by rfl⟩ : syracuseStep 1542253 = 578345) (by norm_num)
theorem B4622453 : Blo 810345 4622453 := bbase (se 5 (by rfl) ⟨216677, by rfl⟩ : syracuseStep 4622453 = 433355) (by norm_num)
theorem B1542397 : Blo 810345 1542397 := bbase (se 3 (by rfl) ⟨289199, by rfl⟩ : syracuseStep 1542397 = 578399) (by norm_num)
theorem B1542557 : Blo 810345 1542557 := bbase (se 3 (by rfl) ⟨289229, by rfl⟩ : syracuseStep 1542557 = 578459) (by norm_num)
theorem B821713 : Blo 810345 821713 := bbase (se 2 (by rfl) ⟨308142, by rfl⟩ : syracuseStep 821713 = 616285) (by norm_num)
theorem B821749 : Blo 810345 821749 := bbase (se 5 (by rfl) ⟨38519, by rfl⟩ : syracuseStep 821749 = 77039) (by norm_num)
theorem B6162965 : Blo 810345 6162965 := bbase (se 6 (by rfl) ⟨144444, by rfl⟩ : syracuseStep 6162965 = 288889) (by norm_num)
theorem B1542701 : Blo 810345 1542701 := bbase (se 3 (by rfl) ⟨289256, by rfl⟩ : syracuseStep 1542701 = 578513) (by norm_num)
theorem B3082805 : Blo 810345 3082805 := bbase (se 5 (by rfl) ⟨144506, by rfl⟩ : syracuseStep 3082805 = 289013) (by norm_num)
theorem B1542989 : Blo 810345 1542989 := bbase (se 3 (by rfl) ⟨289310, by rfl⟩ : syracuseStep 1542989 = 578621) (by norm_num)
theorem B3083093 : Blo 810345 3083093 := bbase (se 9 (by rfl) ⟨9032, by rfl⟩ : syracuseStep 3083093 = 18065) (by norm_num)
theorem B1543141 : Blo 810345 1543141 := bbase (se 4 (by rfl) ⟨144669, by rfl⟩ : syracuseStep 1543141 = 289339) (by norm_num)
theorem B1215533 : Blo 810345 1215533 := bbase (se 3 (by rfl) ⟨227912, by rfl⟩ : syracuseStep 1215533 = 455825) (by norm_num)
theorem B1215557 : Blo 810345 1215557 := bbase (se 4 (by rfl) ⟨113958, by rfl⟩ : syracuseStep 1215557 = 227917) (by norm_num)
theorem B1215581 : Blo 810345 1215581 := bbase (se 3 (by rfl) ⟨227921, by rfl⟩ : syracuseStep 1215581 = 455843) (by norm_num)
theorem B1215605 : Blo 810345 1215605 := bbase (se 5 (by rfl) ⟨56981, by rfl⟩ : syracuseStep 1215605 = 113963) (by norm_num)
theorem B1215629 : Blo 810345 1215629 := bbase (se 3 (by rfl) ⟨227930, by rfl⟩ : syracuseStep 1215629 = 455861) (by norm_num)
theorem B1215653 : Blo 810345 1215653 := bbase (se 4 (by rfl) ⟨113967, by rfl⟩ : syracuseStep 1215653 = 227935) (by norm_num)
theorem B1215677 : Blo 810345 1215677 := bbase (se 3 (by rfl) ⟨227939, by rfl⟩ : syracuseStep 1215677 = 455879) (by norm_num)
theorem B1215701 : Blo 810345 1215701 := bbase (se 7 (by rfl) ⟨14246, by rfl⟩ : syracuseStep 1215701 = 28493) (by norm_num)
theorem B1215725 : Blo 810345 1215725 := bbase (se 3 (by rfl) ⟨227948, by rfl⟩ : syracuseStep 1215725 = 455897) (by norm_num)
theorem B1215749 : Blo 810345 1215749 := bbase (se 4 (by rfl) ⟨113976, by rfl⟩ : syracuseStep 1215749 = 227953) (by norm_num)
theorem B1543445 : Blo 810345 1543445 := bbase (se 6 (by rfl) ⟨36174, by rfl⟩ : syracuseStep 1543445 = 72349) (by norm_num)
theorem B1215773 : Blo 810345 1215773 := bbase (se 3 (by rfl) ⟨227957, by rfl⟩ : syracuseStep 1215773 = 455915) (by norm_num)
theorem B1215797 : Blo 810345 1215797 := bbase (se 5 (by rfl) ⟨56990, by rfl⟩ : syracuseStep 1215797 = 113981) (by norm_num)
theorem B1215821 : Blo 810345 1215821 := bbase (se 3 (by rfl) ⟨227966, by rfl⟩ : syracuseStep 1215821 = 455933) (by norm_num)
theorem B52596053 : Blo 810345 52596053 := bbase (se 11 (by rfl) ⟨38522, by rfl⟩ : syracuseStep 52596053 = 77045) (by norm_num)
theorem B1215845 : Blo 810345 1215845 := bbase (se 4 (by rfl) ⟨113985, by rfl⟩ : syracuseStep 1215845 = 227971) (by norm_num)
theorem B822641 : Blo 810345 822641 := bbase (se 2 (by rfl) ⟨308490, by rfl⟩ : syracuseStep 822641 = 616981) (by norm_num)
theorem B1215869 : Blo 810345 1215869 := bbase (se 3 (by rfl) ⟨227975, by rfl⟩ : syracuseStep 1215869 = 455951) (by norm_num)
theorem B1215893 : Blo 810345 1215893 := bbase (se 6 (by rfl) ⟨28497, by rfl⟩ : syracuseStep 1215893 = 56995) (by norm_num)
theorem B1215917 : Blo 810345 1215917 := bbase (se 3 (by rfl) ⟨227984, by rfl⟩ : syracuseStep 1215917 = 455969) (by norm_num)
theorem B1215941 : Blo 810345 1215941 := bbase (se 4 (by rfl) ⟨113994, by rfl⟩ : syracuseStep 1215941 = 227989) (by norm_num)
theorem B1215965 : Blo 810345 1215965 := bbase (se 3 (by rfl) ⟨227993, by rfl⟩ : syracuseStep 1215965 = 455987) (by norm_num)
theorem B1215989 : Blo 810345 1215989 := bbase (se 5 (by rfl) ⟨56999, by rfl⟩ : syracuseStep 1215989 = 113999) (by norm_num)
theorem B1216013 : Blo 810345 1216013 := bbase (se 3 (by rfl) ⟨228002, by rfl⟩ : syracuseStep 1216013 = 456005) (by norm_num)
theorem B5213717 : Blo 810345 5213717 := bbase (se 6 (by rfl) ⟨122196, by rfl⟩ : syracuseStep 5213717 = 244393) (by norm_num)
theorem B1216037 : Blo 810345 1216037 := bbase (se 4 (by rfl) ⟨114003, by rfl⟩ : syracuseStep 1216037 = 228007) (by norm_num)
theorem B1216061 : Blo 810345 1216061 := bbase (se 3 (by rfl) ⟨228011, by rfl⟩ : syracuseStep 1216061 = 456023) (by norm_num)
theorem B1216085 : Blo 810345 1216085 := bbase (se 8 (by rfl) ⟨7125, by rfl⟩ : syracuseStep 1216085 = 14251) (by norm_num)
theorem B1216109 : Blo 810345 1216109 := bbase (se 3 (by rfl) ⟨228020, by rfl⟩ : syracuseStep 1216109 = 456041) (by norm_num)
theorem B1216133 : Blo 810345 1216133 := bbase (se 4 (by rfl) ⟨114012, by rfl⟩ : syracuseStep 1216133 = 228025) (by norm_num)
theorem B822917 : Blo 810345 822917 := bbase (se 4 (by rfl) ⟨77148, by rfl⟩ : syracuseStep 822917 = 154297) (by norm_num)
theorem B1216157 : Blo 810345 1216157 := bbase (se 3 (by rfl) ⟨228029, by rfl⟩ : syracuseStep 1216157 = 456059) (by norm_num)
theorem B1216181 : Blo 810345 1216181 := bbase (se 5 (by rfl) ⟨57008, by rfl⟩ : syracuseStep 1216181 = 114017) (by norm_num)
theorem B1216205 : Blo 810345 1216205 := bbase (se 3 (by rfl) ⟨228038, by rfl⟩ : syracuseStep 1216205 = 456077) (by norm_num)
theorem B1216229 : Blo 810345 1216229 := bbase (se 4 (by rfl) ⟨114021, by rfl⟩ : syracuseStep 1216229 = 228043) (by norm_num)
theorem B1216253 : Blo 810345 1216253 := bbase (se 3 (by rfl) ⟨228047, by rfl⟩ : syracuseStep 1216253 = 456095) (by norm_num)
theorem B1216277 : Blo 810345 1216277 := bbase (se 6 (by rfl) ⟨28506, by rfl⟩ : syracuseStep 1216277 = 57013) (by norm_num)
theorem B1216301 : Blo 810345 1216301 := bbase (se 3 (by rfl) ⟨228056, by rfl⟩ : syracuseStep 1216301 = 456113) (by norm_num)
theorem B986941 : Blo 810345 986941 := bbase (se 3 (by rfl) ⟨185051, by rfl⟩ : syracuseStep 986941 = 370103) (by norm_num)
theorem B1216325 : Blo 810345 1216325 := bbase (se 4 (by rfl) ⟨114030, by rfl⟩ : syracuseStep 1216325 = 228061) (by norm_num)
theorem B1216349 : Blo 810345 1216349 := bbase (se 3 (by rfl) ⟨228065, by rfl⟩ : syracuseStep 1216349 = 456131) (by norm_num)
theorem B1216373 : Blo 810345 1216373 := bbase (se 5 (by rfl) ⟨57017, by rfl⟩ : syracuseStep 1216373 = 114035) (by norm_num)
theorem B1216397 : Blo 810345 1216397 := bbase (se 3 (by rfl) ⟨228074, by rfl⟩ : syracuseStep 1216397 = 456149) (by norm_num)
theorem B1216421 : Blo 810345 1216421 := bbase (se 4 (by rfl) ⟨114039, by rfl⟩ : syracuseStep 1216421 = 228079) (by norm_num)
theorem B1216445 : Blo 810345 1216445 := bbase (se 3 (by rfl) ⟨228083, by rfl⟩ : syracuseStep 1216445 = 456167) (by norm_num)
theorem B823241 : Blo 810345 823241 := bbase (se 2 (by rfl) ⟨308715, by rfl⟩ : syracuseStep 823241 = 617431) (by norm_num)
theorem B1216469 : Blo 810345 1216469 := bbase (se 7 (by rfl) ⟨14255, by rfl⟩ : syracuseStep 1216469 = 28511) (by norm_num)
theorem B1216493 : Blo 810345 1216493 := bbase (se 3 (by rfl) ⟨228092, by rfl⟩ : syracuseStep 1216493 = 456185) (by norm_num)
theorem B3084277 : Blo 810345 3084277 := bbase (se 5 (by rfl) ⟨144575, by rfl⟩ : syracuseStep 3084277 = 289151) (by norm_num)
theorem B1216517 : Blo 810345 1216517 := bbase (se 4 (by rfl) ⟨114048, by rfl⟩ : syracuseStep 1216517 = 228097) (by norm_num)
theorem B1544197 : Blo 810345 1544197 := bbase (se 4 (by rfl) ⟨144768, by rfl⟩ : syracuseStep 1544197 = 289537) (by norm_num)
theorem B1216541 : Blo 810345 1216541 := bbase (se 3 (by rfl) ⟨228101, by rfl⟩ : syracuseStep 1216541 = 456203) (by norm_num)
theorem B1216565 : Blo 810345 1216565 := bbase (se 5 (by rfl) ⟨57026, by rfl⟩ : syracuseStep 1216565 = 114053) (by norm_num)
theorem B1216589 : Blo 810345 1216589 := bbase (se 3 (by rfl) ⟨228110, by rfl⟩ : syracuseStep 1216589 = 456221) (by norm_num)
theorem B1216613 : Blo 810345 1216613 := bbase (se 4 (by rfl) ⟨114057, by rfl⟩ : syracuseStep 1216613 = 228115) (by norm_num)
theorem B1216637 : Blo 810345 1216637 := bbase (se 3 (by rfl) ⟨228119, by rfl⟩ : syracuseStep 1216637 = 456239) (by norm_num)
theorem B1216661 : Blo 810345 1216661 := bbase (se 6 (by rfl) ⟨28515, by rfl⟩ : syracuseStep 1216661 = 57031) (by norm_num)
theorem B1544341 : Blo 810345 1544341 := bbase (se 6 (by rfl) ⟨36195, by rfl⟩ : syracuseStep 1544341 = 72391) (by norm_num)
theorem B1216685 : Blo 810345 1216685 := bbase (se 3 (by rfl) ⟨228128, by rfl⟩ : syracuseStep 1216685 = 456257) (by norm_num)
theorem B1216709 : Blo 810345 1216709 := bbase (se 4 (by rfl) ⟨114066, by rfl⟩ : syracuseStep 1216709 = 228133) (by norm_num)
theorem B1216733 : Blo 810345 1216733 := bbase (se 3 (by rfl) ⟨228137, by rfl⟩ : syracuseStep 1216733 = 456275) (by norm_num)
theorem B1216757 : Blo 810345 1216757 := bbase (se 5 (by rfl) ⟨57035, by rfl⟩ : syracuseStep 1216757 = 114071) (by norm_num)
theorem B1216781 : Blo 810345 1216781 := bbase (se 3 (by rfl) ⟨228146, by rfl⟩ : syracuseStep 1216781 = 456293) (by norm_num)
theorem B1216805 : Blo 810345 1216805 := bbase (se 4 (by rfl) ⟨114075, by rfl⟩ : syracuseStep 1216805 = 228151) (by norm_num)
theorem B3084581 : Blo 810345 3084581 := bbase (se 4 (by rfl) ⟨289179, by rfl⟩ : syracuseStep 3084581 = 578359) (by norm_num)
theorem B1544501 : Blo 810345 1544501 := bbase (se 5 (by rfl) ⟨72398, by rfl⟩ : syracuseStep 1544501 = 144797) (by norm_num)
theorem B1216829 : Blo 810345 1216829 := bbase (se 3 (by rfl) ⟨228155, by rfl⟩ : syracuseStep 1216829 = 456311) (by norm_num)
theorem B1216853 : Blo 810345 1216853 := bbase (se 10 (by rfl) ⟨1782, by rfl⟩ : syracuseStep 1216853 = 3565) (by norm_num)
theorem B1216877 : Blo 810345 1216877 := bbase (se 3 (by rfl) ⟨228164, by rfl⟩ : syracuseStep 1216877 = 456329) (by norm_num)
theorem B1216901 : Blo 810345 1216901 := bbase (se 4 (by rfl) ⟨114084, by rfl⟩ : syracuseStep 1216901 = 228169) (by norm_num)
theorem B1216925 : Blo 810345 1216925 := bbase (se 3 (by rfl) ⟨228173, by rfl⟩ : syracuseStep 1216925 = 456347) (by norm_num)
theorem B1216949 : Blo 810345 1216949 := bbase (se 5 (by rfl) ⟨57044, by rfl⟩ : syracuseStep 1216949 = 114089) (by norm_num)
theorem B1544645 : Blo 810345 1544645 := bbase (se 4 (by rfl) ⟨144810, by rfl⟩ : syracuseStep 1544645 = 289621) (by norm_num)
theorem B1216973 : Blo 810345 1216973 := bbase (se 3 (by rfl) ⟨228182, by rfl⟩ : syracuseStep 1216973 = 456365) (by norm_num)
theorem B1216997 : Blo 810345 1216997 := bbase (se 4 (by rfl) ⟨114093, by rfl⟩ : syracuseStep 1216997 = 228187) (by norm_num)
theorem B1217021 : Blo 810345 1217021 := bbase (se 3 (by rfl) ⟨228191, by rfl⟩ : syracuseStep 1217021 = 456383) (by norm_num)
theorem B1217045 : Blo 810345 1217045 := bbase (se 6 (by rfl) ⟨28524, by rfl⟩ : syracuseStep 1217045 = 57049) (by norm_num)
theorem B1217069 : Blo 810345 1217069 := bbase (se 3 (by rfl) ⟨228200, by rfl⟩ : syracuseStep 1217069 = 456401) (by norm_num)
theorem B1217093 : Blo 810345 1217093 := bbase (se 4 (by rfl) ⟨114102, by rfl⟩ : syracuseStep 1217093 = 228205) (by norm_num)
theorem B1217117 : Blo 810345 1217117 := bbase (se 3 (by rfl) ⟨228209, by rfl⟩ : syracuseStep 1217117 = 456419) (by norm_num)
theorem B1217141 : Blo 810345 1217141 := bbase (se 5 (by rfl) ⟨57053, by rfl⟩ : syracuseStep 1217141 = 114107) (by norm_num)
theorem B1249933 : Blo 810345 1249933 := bbase (se 3 (by rfl) ⟨234362, by rfl⟩ : syracuseStep 1249933 = 468725) (by norm_num)
theorem B1217165 : Blo 810345 1217165 := bbase (se 3 (by rfl) ⟨228218, by rfl⟩ : syracuseStep 1217165 = 456437) (by norm_num)
theorem B1217189 : Blo 810345 1217189 := bbase (se 4 (by rfl) ⟨114111, by rfl⟩ : syracuseStep 1217189 = 228223) (by norm_num)
theorem B1217213 : Blo 810345 1217213 := bbase (se 3 (by rfl) ⟨228227, by rfl⟩ : syracuseStep 1217213 = 456455) (by norm_num)
theorem B1217237 : Blo 810345 1217237 := bbase (se 7 (by rfl) ⟨14264, by rfl⟩ : syracuseStep 1217237 = 28529) (by norm_num)
theorem B1544933 : Blo 810345 1544933 := bbase (se 4 (by rfl) ⟨144837, by rfl⟩ : syracuseStep 1544933 = 289675) (by norm_num)
theorem B1217261 : Blo 810345 1217261 := bbase (se 3 (by rfl) ⟨228236, by rfl⟩ : syracuseStep 1217261 = 456473) (by norm_num)
theorem B1217285 : Blo 810345 1217285 := bbase (se 4 (by rfl) ⟨114120, by rfl⟩ : syracuseStep 1217285 = 228241) (by norm_num)
theorem B1217309 : Blo 810345 1217309 := bbase (se 3 (by rfl) ⟨228245, by rfl⟩ : syracuseStep 1217309 = 456491) (by norm_num)
theorem B1217333 : Blo 810345 1217333 := bbase (se 5 (by rfl) ⟨57062, by rfl⟩ : syracuseStep 1217333 = 114125) (by norm_num)
theorem B1217357 : Blo 810345 1217357 := bbase (se 3 (by rfl) ⟨228254, by rfl⟩ : syracuseStep 1217357 = 456509) (by norm_num)
theorem B1217381 : Blo 810345 1217381 := bbase (se 4 (by rfl) ⟨114129, by rfl⟩ : syracuseStep 1217381 = 228259) (by norm_num)
theorem B1217405 : Blo 810345 1217405 := bbase (se 3 (by rfl) ⟨228263, by rfl⟩ : syracuseStep 1217405 = 456527) (by norm_num)
theorem B1545085 : Blo 810345 1545085 := bbase (se 3 (by rfl) ⟨289703, by rfl⟩ : syracuseStep 1545085 = 579407) (by norm_num)
theorem B1217429 : Blo 810345 1217429 := bbase (se 6 (by rfl) ⟨28533, by rfl⟩ : syracuseStep 1217429 = 57067) (by norm_num)
theorem B1217453 : Blo 810345 1217453 := bbase (se 3 (by rfl) ⟨228272, by rfl⟩ : syracuseStep 1217453 = 456545) (by norm_num)
theorem B1217477 : Blo 810345 1217477 := bbase (se 4 (by rfl) ⟨114138, by rfl⟩ : syracuseStep 1217477 = 228277) (by norm_num)
theorem B1217501 : Blo 810345 1217501 := bbase (se 3 (by rfl) ⟨228281, by rfl⟩ : syracuseStep 1217501 = 456563) (by norm_num)
theorem B1217525 : Blo 810345 1217525 := bbase (se 5 (by rfl) ⟨57071, by rfl⟩ : syracuseStep 1217525 = 114143) (by norm_num)
theorem B1217549 : Blo 810345 1217549 := bbase (se 3 (by rfl) ⟨228290, by rfl⟩ : syracuseStep 1217549 = 456581) (by norm_num)
theorem B1217573 : Blo 810345 1217573 := bbase (se 4 (by rfl) ⟨114147, by rfl⟩ : syracuseStep 1217573 = 228295) (by norm_num)
theorem B1217597 : Blo 810345 1217597 := bbase (se 3 (by rfl) ⟨228299, by rfl⟩ : syracuseStep 1217597 = 456599) (by norm_num)
theorem B988225 : Blo 810345 988225 := bbase (se 2 (by rfl) ⟨370584, by rfl⟩ : syracuseStep 988225 = 741169) (by norm_num)
theorem B1217621 : Blo 810345 1217621 := bbase (se 8 (by rfl) ⟨7134, by rfl⟩ : syracuseStep 1217621 = 14269) (by norm_num)
theorem B1217645 : Blo 810345 1217645 := bbase (se 3 (by rfl) ⟨228308, by rfl⟩ : syracuseStep 1217645 = 456617) (by norm_num)
theorem B1217669 : Blo 810345 1217669 := bbase (se 4 (by rfl) ⟨114156, by rfl⟩ : syracuseStep 1217669 = 228313) (by norm_num)
theorem B1217693 : Blo 810345 1217693 := bbase (se 3 (by rfl) ⟨228317, by rfl⟩ : syracuseStep 1217693 = 456635) (by norm_num)
theorem B1545389 : Blo 810345 1545389 := bbase (se 3 (by rfl) ⟨289760, by rfl⟩ : syracuseStep 1545389 = 579521) (by norm_num)
theorem B1217717 : Blo 810345 1217717 := bbase (se 5 (by rfl) ⟨57080, by rfl⟩ : syracuseStep 1217717 = 114161) (by norm_num)
theorem B1217741 : Blo 810345 1217741 := bbase (se 3 (by rfl) ⟨228326, by rfl⟩ : syracuseStep 1217741 = 456653) (by norm_num)
theorem B1742029 : Blo 810345 1742029 := bbase (se 3 (by rfl) ⟨326630, by rfl⟩ : syracuseStep 1742029 = 653261) (by norm_num)
theorem B1217765 : Blo 810345 1217765 := bbase (se 4 (by rfl) ⟨114165, by rfl⟩ : syracuseStep 1217765 = 228331) (by norm_num)
theorem B1217789 : Blo 810345 1217789 := bbase (se 3 (by rfl) ⟨228335, by rfl⟩ : syracuseStep 1217789 = 456671) (by norm_num)
theorem B1217813 : Blo 810345 1217813 := bbase (se 6 (by rfl) ⟨28542, by rfl⟩ : syracuseStep 1217813 = 57085) (by norm_num)
theorem B1217837 : Blo 810345 1217837 := bbase (se 3 (by rfl) ⟨228344, by rfl⟩ : syracuseStep 1217837 = 456689) (by norm_num)
theorem B1217861 : Blo 810345 1217861 := bbase (se 4 (by rfl) ⟨114174, by rfl⟩ : syracuseStep 1217861 = 228349) (by norm_num)
theorem B25335125 : Blo 810345 25335125 := bbase (se 14 (by rfl) ⟨2319, by rfl⟩ : syracuseStep 25335125 = 4639) (by norm_num)
theorem B1217885 : Blo 810345 1217885 := bbase (se 3 (by rfl) ⟨228353, by rfl⟩ : syracuseStep 1217885 = 456707) (by norm_num)
theorem B1217909 : Blo 810345 1217909 := bbase (se 5 (by rfl) ⟨57089, by rfl⟩ : syracuseStep 1217909 = 114179) (by norm_num)
theorem B1217933 : Blo 810345 1217933 := bbase (se 3 (by rfl) ⟨228362, by rfl⟩ : syracuseStep 1217933 = 456725) (by norm_num)
theorem B1217957 : Blo 810345 1217957 := bbase (se 4 (by rfl) ⟨114183, by rfl⟩ : syracuseStep 1217957 = 228367) (by norm_num)
theorem B1217981 : Blo 810345 1217981 := bbase (se 3 (by rfl) ⟨228371, by rfl⟩ : syracuseStep 1217981 = 456743) (by norm_num)
theorem B1218005 : Blo 810345 1218005 := bbase (se 7 (by rfl) ⟨14273, by rfl⟩ : syracuseStep 1218005 = 28547) (by norm_num)
theorem B1218029 : Blo 810345 1218029 := bbase (se 3 (by rfl) ⟨228380, by rfl⟩ : syracuseStep 1218029 = 456761) (by norm_num)
theorem B1218053 : Blo 810345 1218053 := bbase (se 4 (by rfl) ⟨114192, by rfl⟩ : syracuseStep 1218053 = 228385) (by norm_num)
theorem B1054237 : Blo 810345 1054237 := bbase (se 3 (by rfl) ⟨197669, by rfl⟩ : syracuseStep 1054237 = 395339) (by norm_num)
theorem B1218077 : Blo 810345 1218077 := bbase (se 3 (by rfl) ⟨228389, by rfl⟩ : syracuseStep 1218077 = 456779) (by norm_num)
theorem B1218101 : Blo 810345 1218101 := bbase (se 5 (by rfl) ⟨57098, by rfl⟩ : syracuseStep 1218101 = 114197) (by norm_num)
theorem B1218125 : Blo 810345 1218125 := bbase (se 3 (by rfl) ⟨228398, by rfl⟩ : syracuseStep 1218125 = 456797) (by norm_num)
theorem B1218149 : Blo 810345 1218149 := bbase (se 4 (by rfl) ⟨114201, by rfl⟩ : syracuseStep 1218149 = 228403) (by norm_num)
theorem B1218173 : Blo 810345 1218173 := bbase (se 3 (by rfl) ⟨228407, by rfl⟩ : syracuseStep 1218173 = 456815) (by norm_num)
theorem B1218197 : Blo 810345 1218197 := bbase (se 6 (by rfl) ⟨28551, by rfl⟩ : syracuseStep 1218197 = 57103) (by norm_num)
theorem B1218221 : Blo 810345 1218221 := bbase (se 3 (by rfl) ⟨228416, by rfl⟩ : syracuseStep 1218221 = 456833) (by norm_num)
theorem B1218245 : Blo 810345 1218245 := bbase (se 4 (by rfl) ⟨114210, by rfl⟩ : syracuseStep 1218245 = 228421) (by norm_num)
theorem B1218269 : Blo 810345 1218269 := bbase (se 3 (by rfl) ⟨228425, by rfl⟩ : syracuseStep 1218269 = 456851) (by norm_num)
theorem B1218293 : Blo 810345 1218293 := bbase (se 5 (by rfl) ⟨57107, by rfl⟩ : syracuseStep 1218293 = 114215) (by norm_num)
theorem B1218317 : Blo 810345 1218317 := bbase (se 3 (by rfl) ⟨228434, by rfl⟩ : syracuseStep 1218317 = 456869) (by norm_num)
theorem B1218341 : Blo 810345 1218341 := bbase (se 4 (by rfl) ⟨114219, by rfl⟩ : syracuseStep 1218341 = 228439) (by norm_num)
theorem B1218365 : Blo 810345 1218365 := bbase (se 3 (by rfl) ⟨228443, by rfl⟩ : syracuseStep 1218365 = 456887) (by norm_num)
theorem B1218389 : Blo 810345 1218389 := bbase (se 9 (by rfl) ⟨3569, by rfl⟩ : syracuseStep 1218389 = 7139) (by norm_num)
theorem B1218413 : Blo 810345 1218413 := bbase (se 3 (by rfl) ⟨228452, by rfl⟩ : syracuseStep 1218413 = 456905) (by norm_num)
theorem B1218437 : Blo 810345 1218437 := bbase (se 4 (by rfl) ⟨114228, by rfl⟩ : syracuseStep 1218437 = 228457) (by norm_num)
theorem B1218461 : Blo 810345 1218461 := bbase (se 3 (by rfl) ⟨228461, by rfl⟩ : syracuseStep 1218461 = 456923) (by norm_num)
theorem B1218485 : Blo 810345 1218485 := bbase (se 5 (by rfl) ⟨57116, by rfl⟩ : syracuseStep 1218485 = 114233) (by norm_num)
theorem B1218509 : Blo 810345 1218509 := bbase (se 3 (by rfl) ⟨228470, by rfl⟩ : syracuseStep 1218509 = 456941) (by norm_num)
theorem B11704277 : Blo 810345 11704277 := bbase (se 7 (by rfl) ⟨137159, by rfl⟩ : syracuseStep 11704277 = 274319) (by norm_num)
theorem B1218533 : Blo 810345 1218533 := bbase (se 4 (by rfl) ⟨114237, by rfl⟩ : syracuseStep 1218533 = 228475) (by norm_num)
theorem B1218557 : Blo 810345 1218557 := bbase (se 3 (by rfl) ⟨228479, by rfl⟩ : syracuseStep 1218557 = 456959) (by norm_num)
theorem B1218581 : Blo 810345 1218581 := bbase (se 6 (by rfl) ⟨28560, by rfl⟩ : syracuseStep 1218581 = 57121) (by norm_num)
theorem B3708965 : Blo 810345 3708965 := bbase (se 4 (by rfl) ⟨347715, by rfl⟩ : syracuseStep 3708965 = 695431) (by norm_num)
theorem B1218605 : Blo 810345 1218605 := bbase (se 3 (by rfl) ⟨228488, by rfl⟩ : syracuseStep 1218605 = 456977) (by norm_num)
theorem B1218629 : Blo 810345 1218629 := bbase (se 4 (by rfl) ⟨114246, by rfl⟩ : syracuseStep 1218629 = 228493) (by norm_num)
theorem B2922581 : Blo 810345 2922581 := bbase (se 8 (by rfl) ⟨17124, by rfl⟩ : syracuseStep 2922581 = 34249) (by norm_num)
theorem B1218653 : Blo 810345 1218653 := bbase (se 3 (by rfl) ⟨228497, by rfl⟩ : syracuseStep 1218653 = 456995) (by norm_num)
theorem B1218677 : Blo 810345 1218677 := bbase (se 5 (by rfl) ⟨57125, by rfl⟩ : syracuseStep 1218677 = 114251) (by norm_num)
theorem B1218701 : Blo 810345 1218701 := bbase (se 3 (by rfl) ⟨228506, by rfl⟩ : syracuseStep 1218701 = 457013) (by norm_num)
theorem B1218725 : Blo 810345 1218725 := bbase (se 4 (by rfl) ⟨114255, by rfl⟩ : syracuseStep 1218725 = 228511) (by norm_num)
theorem B3709093 : Blo 810345 3709093 := bbase (se 4 (by rfl) ⟨347727, by rfl⟩ : syracuseStep 3709093 = 695455) (by norm_num)
theorem B4397237 : Blo 810345 4397237 := bbase (se 5 (by rfl) ⟨206120, by rfl⟩ : syracuseStep 4397237 = 412241) (by norm_num)
theorem B1218749 : Blo 810345 1218749 := bbase (se 3 (by rfl) ⟨228515, by rfl⟩ : syracuseStep 1218749 = 457031) (by norm_num)
theorem B1317077 : Blo 810345 1317077 := bbase (se 7 (by rfl) ⟨15434, by rfl⟩ : syracuseStep 1317077 = 30869) (by norm_num)
theorem B1218773 : Blo 810345 1218773 := bbase (se 7 (by rfl) ⟨14282, by rfl⟩ : syracuseStep 1218773 = 28565) (by norm_num)
theorem B1218797 : Blo 810345 1218797 := bbase (se 3 (by rfl) ⟨228524, by rfl⟩ : syracuseStep 1218797 = 457049) (by norm_num)
theorem B1218821 : Blo 810345 1218821 := bbase (se 4 (by rfl) ⟨114264, by rfl⟩ : syracuseStep 1218821 = 228529) (by norm_num)
theorem B1218845 : Blo 810345 1218845 := bbase (se 3 (by rfl) ⟨228533, by rfl⟩ : syracuseStep 1218845 = 457067) (by norm_num)
theorem B1218869 : Blo 810345 1218869 := bbase (se 5 (by rfl) ⟨57134, by rfl⟩ : syracuseStep 1218869 = 114269) (by norm_num)
theorem B1644877 : Blo 810345 1644877 := bbase (se 3 (by rfl) ⟨308414, by rfl⟩ : syracuseStep 1644877 = 616829) (by norm_num)
theorem B1218893 : Blo 810345 1218893 := bbase (se 3 (by rfl) ⟨228542, by rfl⟩ : syracuseStep 1218893 = 457085) (by norm_num)
theorem B1218917 : Blo 810345 1218917 := bbase (se 4 (by rfl) ⟨114273, by rfl⟩ : syracuseStep 1218917 = 228547) (by norm_num)
theorem B3086693 : Blo 810345 3086693 := bbase (se 4 (by rfl) ⟨289377, by rfl⟩ : syracuseStep 3086693 = 578755) (by norm_num)
theorem B1218941 : Blo 810345 1218941 := bbase (se 3 (by rfl) ⟨228551, by rfl⟩ : syracuseStep 1218941 = 457103) (by norm_num)
theorem B1218965 : Blo 810345 1218965 := bbase (se 6 (by rfl) ⟨28569, by rfl⟩ : syracuseStep 1218965 = 57139) (by norm_num)
theorem B11737493 : Blo 810345 11737493 := bbase (se 6 (by rfl) ⟨275097, by rfl⟩ : syracuseStep 11737493 = 550195) (by norm_num)
theorem B1218989 : Blo 810345 1218989 := bbase (se 3 (by rfl) ⟨228560, by rfl⟩ : syracuseStep 1218989 = 457121) (by norm_num)
theorem B1808813 : Blo 810345 1808813 := bbase (se 3 (by rfl) ⟨339152, by rfl⟩ : syracuseStep 1808813 = 678305) (by norm_num)
theorem B7018933 : Blo 810345 7018933 := bbase (se 5 (by rfl) ⟨329012, by rfl⟩ : syracuseStep 7018933 = 658025) (by norm_num)
theorem B1219013 : Blo 810345 1219013 := bbase (se 4 (by rfl) ⟨114282, by rfl⟩ : syracuseStep 1219013 = 228565) (by norm_num)
theorem B1219037 : Blo 810345 1219037 := bbase (se 3 (by rfl) ⟨228569, by rfl⟩ : syracuseStep 1219037 = 457139) (by norm_num)
theorem B1219061 : Blo 810345 1219061 := bbase (se 5 (by rfl) ⟨57143, by rfl⟩ : syracuseStep 1219061 = 114287) (by norm_num)
theorem B1219085 : Blo 810345 1219085 := bbase (se 3 (by rfl) ⟨228578, by rfl⟩ : syracuseStep 1219085 = 457157) (by norm_num)
theorem B1219109 : Blo 810345 1219109 := bbase (se 4 (by rfl) ⟨114291, by rfl⟩ : syracuseStep 1219109 = 228583) (by norm_num)
theorem B1219133 : Blo 810345 1219133 := bbase (se 3 (by rfl) ⟨228587, by rfl⟩ : syracuseStep 1219133 = 457175) (by norm_num)
theorem B1219157 : Blo 810345 1219157 := bbase (se 8 (by rfl) ⟨7143, by rfl⟩ : syracuseStep 1219157 = 14287) (by norm_num)
theorem B1219181 : Blo 810345 1219181 := bbase (se 3 (by rfl) ⟨228596, by rfl⟩ : syracuseStep 1219181 = 457193) (by norm_num)
theorem B1219205 : Blo 810345 1219205 := bbase (se 4 (by rfl) ⟨114300, by rfl⟩ : syracuseStep 1219205 = 228601) (by norm_num)
theorem B3086981 : Blo 810345 3086981 := bbase (se 4 (by rfl) ⟨289404, by rfl⟩ : syracuseStep 3086981 = 578809) (by norm_num)
theorem B1219229 : Blo 810345 1219229 := bbase (se 3 (by rfl) ⟨228605, by rfl⟩ : syracuseStep 1219229 = 457211) (by norm_num)
theorem B1219253 : Blo 810345 1219253 := bbase (se 5 (by rfl) ⟨57152, by rfl⟩ : syracuseStep 1219253 = 114305) (by norm_num)
theorem B1219277 : Blo 810345 1219277 := bbase (se 3 (by rfl) ⟨228614, by rfl⟩ : syracuseStep 1219277 = 457229) (by norm_num)
theorem B1219301 : Blo 810345 1219301 := bbase (se 4 (by rfl) ⟨114309, by rfl⟩ : syracuseStep 1219301 = 228619) (by norm_num)
theorem B1219325 : Blo 810345 1219325 := bbase (se 3 (by rfl) ⟨228623, by rfl⟩ : syracuseStep 1219325 = 457247) (by norm_num)
theorem B1219349 : Blo 810345 1219349 := bbase (se 6 (by rfl) ⟨28578, by rfl⟩ : syracuseStep 1219349 = 57157) (by norm_num)
theorem B1219373 : Blo 810345 1219373 := bbase (se 3 (by rfl) ⟨228632, by rfl⟩ : syracuseStep 1219373 = 457265) (by norm_num)
theorem B1645373 : Blo 810345 1645373 := bbase (se 3 (by rfl) ⟨308507, by rfl⟩ : syracuseStep 1645373 = 617015) (by norm_num)
theorem B1219397 : Blo 810345 1219397 := bbase (se 4 (by rfl) ⟨114318, by rfl⟩ : syracuseStep 1219397 = 228637) (by norm_num)
theorem B3119957 : Blo 810345 3119957 := bbase (se 9 (by rfl) ⟨9140, by rfl⟩ : syracuseStep 3119957 = 18281) (by norm_num)
theorem B1219421 : Blo 810345 1219421 := bbase (se 3 (by rfl) ⟨228641, by rfl⟩ : syracuseStep 1219421 = 457283) (by norm_num)
theorem B1481573 : Blo 810345 1481573 := bbase (se 4 (by rfl) ⟨138897, by rfl⟩ : syracuseStep 1481573 = 277795) (by norm_num)
theorem B1219445 : Blo 810345 1219445 := bbase (se 5 (by rfl) ⟨57161, by rfl⟩ : syracuseStep 1219445 = 114323) (by norm_num)
theorem B1219469 : Blo 810345 1219469 := bbase (se 3 (by rfl) ⟨228650, by rfl⟩ : syracuseStep 1219469 = 457301) (by norm_num)
theorem B1219493 : Blo 810345 1219493 := bbase (se 4 (by rfl) ⟨114327, by rfl⟩ : syracuseStep 1219493 = 228655) (by norm_num)
theorem B1153973 : Blo 810345 1153973 := bbase (se 5 (by rfl) ⟨54092, by rfl⟩ : syracuseStep 1153973 = 108185) (by norm_num)
theorem B1219517 : Blo 810345 1219517 := bbase (se 3 (by rfl) ⟨228659, by rfl⟩ : syracuseStep 1219517 = 457319) (by norm_num)
theorem B1219541 : Blo 810345 1219541 := bbase (se 7 (by rfl) ⟨14291, by rfl⟩ : syracuseStep 1219541 = 28583) (by norm_num)
theorem B1219565 : Blo 810345 1219565 := bbase (se 3 (by rfl) ⟨228668, by rfl⟩ : syracuseStep 1219565 = 457337) (by norm_num)
theorem B1219589 : Blo 810345 1219589 := bbase (se 4 (by rfl) ⟨114336, by rfl⟩ : syracuseStep 1219589 = 228673) (by norm_num)
theorem B1219613 : Blo 810345 1219613 := bbase (se 3 (by rfl) ⟨228677, by rfl⟩ : syracuseStep 1219613 = 457355) (by norm_num)
theorem B1219637 : Blo 810345 1219637 := bbase (se 5 (by rfl) ⟨57170, by rfl⟩ : syracuseStep 1219637 = 114341) (by norm_num)
theorem B3513413 : Blo 810345 3513413 := bbase (se 4 (by rfl) ⟨329382, by rfl⟩ : syracuseStep 3513413 = 658765) (by norm_num)
theorem B1219661 : Blo 810345 1219661 := bbase (se 3 (by rfl) ⟨228686, by rfl⟩ : syracuseStep 1219661 = 457373) (by norm_num)
theorem B1219685 : Blo 810345 1219685 := bbase (se 4 (by rfl) ⟨114345, by rfl⟩ : syracuseStep 1219685 = 228691) (by norm_num)
theorem B1219709 : Blo 810345 1219709 := bbase (se 3 (by rfl) ⟨228695, by rfl⟩ : syracuseStep 1219709 = 457391) (by norm_num)
theorem B1219733 : Blo 810345 1219733 := bbase (se 6 (by rfl) ⟨28587, by rfl⟩ : syracuseStep 1219733 = 57175) (by norm_num)
theorem B1219757 : Blo 810345 1219757 := bbase (se 3 (by rfl) ⟨228704, by rfl⟩ : syracuseStep 1219757 = 457409) (by norm_num)
theorem B1219781 : Blo 810345 1219781 := bbase (se 4 (by rfl) ⟨114354, by rfl⟩ : syracuseStep 1219781 = 228709) (by norm_num)
theorem B1219805 : Blo 810345 1219805 := bbase (se 3 (by rfl) ⟨228713, by rfl⟩ : syracuseStep 1219805 = 457427) (by norm_num)
theorem B1219829 : Blo 810345 1219829 := bbase (se 5 (by rfl) ⟨57179, by rfl⟩ : syracuseStep 1219829 = 114359) (by norm_num)
theorem B1219853 : Blo 810345 1219853 := bbase (se 3 (by rfl) ⟨228722, by rfl⟩ : syracuseStep 1219853 = 457445) (by norm_num)
theorem B1219877 : Blo 810345 1219877 := bbase (se 4 (by rfl) ⟨114363, by rfl⟩ : syracuseStep 1219877 = 228727) (by norm_num)
theorem B1219901 : Blo 810345 1219901 := bbase (se 3 (by rfl) ⟨228731, by rfl⟩ : syracuseStep 1219901 = 457463) (by norm_num)
theorem B1219925 : Blo 810345 1219925 := bbase (se 11 (by rfl) ⟨893, by rfl⟩ : syracuseStep 1219925 = 1787) (by norm_num)
theorem B1219949 : Blo 810345 1219949 := bbase (se 3 (by rfl) ⟨228740, by rfl⟩ : syracuseStep 1219949 = 457481) (by norm_num)
theorem B1219973 : Blo 810345 1219973 := bbase (se 4 (by rfl) ⟨114372, by rfl⟩ : syracuseStep 1219973 = 228745) (by norm_num)
theorem B1219997 : Blo 810345 1219997 := bbase (se 3 (by rfl) ⟨228749, by rfl⟩ : syracuseStep 1219997 = 457499) (by norm_num)
theorem B1220021 : Blo 810345 1220021 := bbase (se 5 (by rfl) ⟨57188, by rfl⟩ : syracuseStep 1220021 = 114377) (by norm_num)
theorem B4103621 : Blo 810345 4103621 := bbase (se 4 (by rfl) ⟨384714, by rfl⟩ : syracuseStep 4103621 = 769429) (by norm_num)
theorem B1220045 : Blo 810345 1220045 := bbase (se 3 (by rfl) ⟨228758, by rfl⟩ : syracuseStep 1220045 = 457517) (by norm_num)
theorem B1220069 : Blo 810345 1220069 := bbase (se 4 (by rfl) ⟨114381, by rfl⟩ : syracuseStep 1220069 = 228763) (by norm_num)
theorem B3907061 : Blo 810345 3907061 := bbase (se 5 (by rfl) ⟨183143, by rfl⟩ : syracuseStep 3907061 = 366287) (by norm_num)
theorem B1220093 : Blo 810345 1220093 := bbase (se 3 (by rfl) ⟨228767, by rfl⟩ : syracuseStep 1220093 = 457535) (by norm_num)
theorem B1056277 : Blo 810345 1056277 := bbase (se 6 (by rfl) ⟨24756, by rfl⟩ : syracuseStep 1056277 = 49513) (by norm_num)
theorem B1220117 : Blo 810345 1220117 := bbase (se 6 (by rfl) ⟨28596, by rfl⟩ : syracuseStep 1220117 = 57193) (by norm_num)
theorem B1220141 : Blo 810345 1220141 := bbase (se 3 (by rfl) ⟨228776, by rfl⟩ : syracuseStep 1220141 = 457553) (by norm_num)
theorem B1220165 : Blo 810345 1220165 := bbase (se 4 (by rfl) ⟨114390, by rfl⟩ : syracuseStep 1220165 = 228781) (by norm_num)
theorem B1220189 : Blo 810345 1220189 := bbase (se 3 (by rfl) ⟨228785, by rfl⟩ : syracuseStep 1220189 = 457571) (by norm_num)
theorem B1220213 : Blo 810345 1220213 := bbase (se 5 (by rfl) ⟨57197, by rfl⟩ : syracuseStep 1220213 = 114395) (by norm_num)
theorem B1220237 : Blo 810345 1220237 := bbase (se 3 (by rfl) ⟨228794, by rfl⟩ : syracuseStep 1220237 = 457589) (by norm_num)
theorem B1220261 : Blo 810345 1220261 := bbase (se 4 (by rfl) ⟨114399, by rfl⟩ : syracuseStep 1220261 = 228799) (by norm_num)
theorem B1220285 : Blo 810345 1220285 := bbase (se 3 (by rfl) ⟨228803, by rfl⟩ : syracuseStep 1220285 = 457607) (by norm_num)
theorem B1220309 : Blo 810345 1220309 := bbase (se 7 (by rfl) ⟨14300, by rfl⟩ : syracuseStep 1220309 = 28601) (by norm_num)
theorem B1220333 : Blo 810345 1220333 := bbase (se 3 (by rfl) ⟨228812, by rfl⟩ : syracuseStep 1220333 = 457625) (by norm_num)
theorem B1220357 : Blo 810345 1220357 := bbase (se 4 (by rfl) ⟨114408, by rfl⟩ : syracuseStep 1220357 = 228817) (by norm_num)
theorem B1220381 : Blo 810345 1220381 := bbase (se 3 (by rfl) ⟨228821, by rfl⟩ : syracuseStep 1220381 = 457643) (by norm_num)
theorem B3088165 : Blo 810345 3088165 := bbase (se 4 (by rfl) ⟨289515, by rfl⟩ : syracuseStep 3088165 = 579031) (by norm_num)
theorem B1220405 : Blo 810345 1220405 := bbase (se 5 (by rfl) ⟨57206, by rfl⟩ : syracuseStep 1220405 = 114413) (by norm_num)
theorem B1220429 : Blo 810345 1220429 := bbase (se 3 (by rfl) ⟨228830, by rfl⟩ : syracuseStep 1220429 = 457661) (by norm_num)
theorem B1220453 : Blo 810345 1220453 := bbase (se 4 (by rfl) ⟨114417, by rfl⟩ : syracuseStep 1220453 = 228835) (by norm_num)
theorem B1056629 : Blo 810345 1056629 := bbase (se 5 (by rfl) ⟨49529, by rfl⟩ : syracuseStep 1056629 = 99059) (by norm_num)
theorem B1220477 : Blo 810345 1220477 := bbase (se 3 (by rfl) ⟨228839, by rfl⟩ : syracuseStep 1220477 = 457679) (by norm_num)
theorem B1220501 : Blo 810345 1220501 := bbase (se 6 (by rfl) ⟨28605, by rfl⟩ : syracuseStep 1220501 = 57211) (by norm_num)
theorem B1220525 : Blo 810345 1220525 := bbase (se 3 (by rfl) ⟨228848, by rfl⟩ : syracuseStep 1220525 = 457697) (by norm_num)
theorem B1220549 : Blo 810345 1220549 := bbase (se 4 (by rfl) ⟨114426, by rfl⟩ : syracuseStep 1220549 = 228853) (by norm_num)
theorem B1220573 : Blo 810345 1220573 := bbase (se 3 (by rfl) ⟨228857, by rfl⟩ : syracuseStep 1220573 = 457715) (by norm_num)
theorem B1220597 : Blo 810345 1220597 := bbase (se 5 (by rfl) ⟨57215, by rfl⟩ : syracuseStep 1220597 = 114431) (by norm_num)
theorem B925705 : Blo 810345 925705 := bbase (se 2 (by rfl) ⟨347139, by rfl⟩ : syracuseStep 925705 = 694279) (by norm_num)
theorem B1220621 : Blo 810345 1220621 := bbase (se 3 (by rfl) ⟨228866, by rfl⟩ : syracuseStep 1220621 = 457733) (by norm_num)
theorem B1220645 : Blo 810345 1220645 := bbase (se 4 (by rfl) ⟨114435, by rfl⟩ : syracuseStep 1220645 = 228871) (by norm_num)
theorem B1220669 : Blo 810345 1220669 := bbase (se 3 (by rfl) ⟨228875, by rfl⟩ : syracuseStep 1220669 = 457751) (by norm_num)
theorem B3088469 : Blo 810345 3088469 := bbase (se 8 (by rfl) ⟨18096, by rfl⟩ : syracuseStep 3088469 = 36193) (by norm_num)
theorem B1220693 : Blo 810345 1220693 := bbase (se 8 (by rfl) ⟨7152, by rfl⟩ : syracuseStep 1220693 = 14305) (by norm_num)
theorem B1220717 : Blo 810345 1220717 := bbase (se 3 (by rfl) ⟨228884, by rfl⟩ : syracuseStep 1220717 = 457769) (by norm_num)
theorem B1220741 : Blo 810345 1220741 := bbase (se 4 (by rfl) ⟨114444, by rfl⟩ : syracuseStep 1220741 = 228889) (by norm_num)
theorem B1646741 : Blo 810345 1646741 := bbase (se 6 (by rfl) ⟨38595, by rfl⟩ : syracuseStep 1646741 = 77191) (by norm_num)
theorem B1220765 : Blo 810345 1220765 := bbase (se 3 (by rfl) ⟨228893, by rfl⟩ : syracuseStep 1220765 = 457787) (by norm_num)
theorem B1220789 : Blo 810345 1220789 := bbase (se 5 (by rfl) ⟨57224, by rfl⟩ : syracuseStep 1220789 = 114449) (by norm_num)
theorem B1220813 : Blo 810345 1220813 := bbase (se 3 (by rfl) ⟨228902, by rfl⟩ : syracuseStep 1220813 = 457805) (by norm_num)
theorem B1220837 : Blo 810345 1220837 := bbase (se 4 (by rfl) ⟨114453, by rfl⟩ : syracuseStep 1220837 = 228907) (by norm_num)
theorem B1220861 : Blo 810345 1220861 := bbase (se 3 (by rfl) ⟨228911, by rfl⟩ : syracuseStep 1220861 = 457823) (by norm_num)
theorem B1220885 : Blo 810345 1220885 := bbase (se 6 (by rfl) ⟨28614, by rfl⟩ : syracuseStep 1220885 = 57229) (by norm_num)
theorem B1220909 : Blo 810345 1220909 := bbase (se 3 (by rfl) ⟨228920, by rfl⟩ : syracuseStep 1220909 = 457841) (by norm_num)
theorem B1155397 : Blo 810345 1155397 := bbase (se 4 (by rfl) ⟨108318, by rfl⟩ : syracuseStep 1155397 = 216637) (by norm_num)
theorem B1220933 : Blo 810345 1220933 := bbase (se 4 (by rfl) ⟨114462, by rfl⟩ : syracuseStep 1220933 = 228925) (by norm_num)
theorem B1220957 : Blo 810345 1220957 := bbase (se 3 (by rfl) ⟨228929, by rfl⟩ : syracuseStep 1220957 = 457859) (by norm_num)
theorem B1220981 : Blo 810345 1220981 := bbase (se 5 (by rfl) ⟨57233, by rfl⟩ : syracuseStep 1220981 = 114467) (by norm_num)
theorem B1221005 : Blo 810345 1221005 := bbase (se 3 (by rfl) ⟨228938, by rfl⟩ : syracuseStep 1221005 = 457877) (by norm_num)
theorem B1483157 : Blo 810345 1483157 := bbase (se 6 (by rfl) ⟨34761, by rfl⟩ : syracuseStep 1483157 = 69523) (by norm_num)
theorem B2597285 : Blo 810345 2597285 := bbase (se 4 (by rfl) ⟨243495, by rfl⟩ : syracuseStep 2597285 = 486991) (by norm_num)
theorem B1221029 : Blo 810345 1221029 := bbase (se 4 (by rfl) ⟨114471, by rfl⟩ : syracuseStep 1221029 = 228943) (by norm_num)
theorem B1221053 : Blo 810345 1221053 := bbase (se 3 (by rfl) ⟨228947, by rfl⟩ : syracuseStep 1221053 = 457895) (by norm_num)
theorem B1221077 : Blo 810345 1221077 := bbase (se 7 (by rfl) ⟨14309, by rfl⟩ : syracuseStep 1221077 = 28619) (by norm_num)
theorem B1221101 : Blo 810345 1221101 := bbase (se 3 (by rfl) ⟨228956, by rfl⟩ : syracuseStep 1221101 = 457913) (by norm_num)
theorem B1221125 : Blo 810345 1221125 := bbase (se 4 (by rfl) ⟨114480, by rfl⟩ : syracuseStep 1221125 = 228961) (by norm_num)
theorem B1221149 : Blo 810345 1221149 := bbase (se 3 (by rfl) ⟨228965, by rfl⟩ : syracuseStep 1221149 = 457931) (by norm_num)
theorem B1221173 : Blo 810345 1221173 := bbase (se 5 (by rfl) ⟨57242, by rfl⟩ : syracuseStep 1221173 = 114485) (by norm_num)
theorem B1221197 : Blo 810345 1221197 := bbase (se 3 (by rfl) ⟨228974, by rfl⟩ : syracuseStep 1221197 = 457949) (by norm_num)
theorem B1221221 : Blo 810345 1221221 := bbase (se 4 (by rfl) ⟨114489, by rfl⟩ : syracuseStep 1221221 = 228979) (by norm_num)
theorem B1647229 : Blo 810345 1647229 := bbase (se 3 (by rfl) ⟨308855, by rfl⟩ : syracuseStep 1647229 = 617711) (by norm_num)
theorem B1221245 : Blo 810345 1221245 := bbase (se 3 (by rfl) ⟨228983, by rfl⟩ : syracuseStep 1221245 = 457967) (by norm_num)
theorem B11870869 : Blo 810345 11870869 := bbase (se 6 (by rfl) ⟨278223, by rfl⟩ : syracuseStep 11870869 = 556447) (by norm_num)
theorem B1221269 : Blo 810345 1221269 := bbase (se 6 (by rfl) ⟨28623, by rfl⟩ : syracuseStep 1221269 = 57247) (by norm_num)
theorem B1221293 : Blo 810345 1221293 := bbase (se 3 (by rfl) ⟨228992, by rfl⟩ : syracuseStep 1221293 = 457985) (by norm_num)
theorem B1221317 : Blo 810345 1221317 := bbase (se 4 (by rfl) ⟨114498, by rfl⟩ : syracuseStep 1221317 = 228997) (by norm_num)
theorem B4104917 : Blo 810345 4104917 := bbase (se 7 (by rfl) ⟨48104, by rfl⟩ : syracuseStep 4104917 = 96209) (by norm_num)
theorem B1221341 : Blo 810345 1221341 := bbase (se 3 (by rfl) ⟨229001, by rfl⟩ : syracuseStep 1221341 = 458003) (by norm_num)
theorem B1221365 : Blo 810345 1221365 := bbase (se 5 (by rfl) ⟨57251, by rfl⟩ : syracuseStep 1221365 = 114503) (by norm_num)
theorem B1221389 : Blo 810345 1221389 := bbase (se 3 (by rfl) ⟨229010, by rfl⟩ : syracuseStep 1221389 = 458021) (by norm_num)
theorem B1221413 : Blo 810345 1221413 := bbase (se 4 (by rfl) ⟨114507, by rfl⟩ : syracuseStep 1221413 = 229015) (by norm_num)
theorem B1221437 : Blo 810345 1221437 := bbase (se 3 (by rfl) ⟨229019, by rfl⟩ : syracuseStep 1221437 = 458039) (by norm_num)
theorem B1221461 : Blo 810345 1221461 := bbase (se 9 (by rfl) ⟨3578, by rfl⟩ : syracuseStep 1221461 = 7157) (by norm_num)
theorem B1221485 : Blo 810345 1221485 := bbase (se 3 (by rfl) ⟨229028, by rfl⟩ : syracuseStep 1221485 = 458057) (by norm_num)
theorem B1254269 : Blo 810345 1254269 := bbase (se 3 (by rfl) ⟨235175, by rfl⟩ : syracuseStep 1254269 = 470351) (by norm_num)
theorem B1221509 : Blo 810345 1221509 := bbase (se 4 (by rfl) ⟨114516, by rfl⟩ : syracuseStep 1221509 = 229033) (by norm_num)
theorem B1155989 : Blo 810345 1155989 := bbase (se 6 (by rfl) ⟨27093, by rfl⟩ : syracuseStep 1155989 = 54187) (by norm_num)
theorem B1156069 : Blo 810345 1156069 := bbase (se 4 (by rfl) ⟨108381, by rfl⟩ : syracuseStep 1156069 = 216763) (by norm_num)
theorem B1156189 : Blo 810345 1156189 := bbase (se 3 (by rfl) ⟨216785, by rfl⟩ : syracuseStep 1156189 = 433571) (by norm_num)
theorem B1975477 : Blo 810345 1975477 := bbase (se 5 (by rfl) ⟨92600, by rfl⟩ : syracuseStep 1975477 = 185201) (by norm_num)
theorem B1156285 : Blo 810345 1156285 := bbase (se 3 (by rfl) ⟨216803, by rfl⟩ : syracuseStep 1156285 = 433607) (by norm_num)
theorem B3122405 : Blo 810345 3122405 := bbase (se 4 (by rfl) ⟨292725, by rfl⟩ : syracuseStep 3122405 = 585451) (by norm_num)
theorem B7808309 : Blo 810345 7808309 := bbase (se 5 (by rfl) ⟨366014, by rfl⟩ : syracuseStep 7808309 = 732029) (by norm_num)
theorem B2598389 : Blo 810345 2598389 := bbase (se 5 (by rfl) ⟨121799, by rfl⟩ : syracuseStep 2598389 = 243599) (by norm_num)
theorem B1025617 : Blo 810345 1025617 := bbase (se 2 (by rfl) ⟨384606, by rfl⟩ : syracuseStep 1025617 = 769213) (by norm_num)
theorem B1156781 : Blo 810345 1156781 := bbase (se 3 (by rfl) ⟨216896, by rfl⟩ : syracuseStep 1156781 = 433793) (by norm_num)
theorem B1025713 : Blo 810345 1025713 := bbase (se 2 (by rfl) ⟨384642, by rfl⟩ : syracuseStep 1025713 = 769285) (by norm_num)
theorem B1189621 : Blo 810345 1189621 := bbase (se 5 (by rfl) ⟨55763, by rfl⟩ : syracuseStep 1189621 = 111527) (by norm_num)
theorem B1025885 : Blo 810345 1025885 := bbase (se 3 (by rfl) ⟨192353, by rfl⟩ : syracuseStep 1025885 = 384707) (by norm_num)
theorem B1025941 : Blo 810345 1025941 := bbase (se 6 (by rfl) ⟨24045, by rfl⟩ : syracuseStep 1025941 = 48091) (by norm_num)
theorem B4106213 : Blo 810345 4106213 := bbase (se 4 (by rfl) ⟨384957, by rfl⟩ : syracuseStep 4106213 = 769915) (by norm_num)
theorem B1026037 : Blo 810345 1026037 := bbase (se 5 (by rfl) ⟨48095, by rfl⟩ : syracuseStep 1026037 = 96191) (by norm_num)
theorem B4630517 : Blo 810345 4630517 := bbase (se 5 (by rfl) ⟨217055, by rfl⟩ : syracuseStep 4630517 = 434111) (by norm_num)
theorem B6170741 : Blo 810345 6170741 := bbase (se 5 (by rfl) ⟨289253, by rfl⟩ : syracuseStep 6170741 = 578507) (by norm_num)
theorem B3090581 : Blo 810345 3090581 := bbase (se 6 (by rfl) ⟨72435, by rfl⟩ : syracuseStep 3090581 = 144871) (by norm_num)
theorem B1026209 : Blo 810345 1026209 := bbase (se 2 (by rfl) ⟨384828, by rfl⟩ : syracuseStep 1026209 = 769657) (by norm_num)
theorem B1157333 : Blo 810345 1157333 := bbase (se 7 (by rfl) ⟨13562, by rfl⟩ : syracuseStep 1157333 = 27125) (by norm_num)
theorem B1026265 : Blo 810345 1026265 := bbase (se 2 (by rfl) ⟨384849, by rfl⟩ : syracuseStep 1026265 = 769699) (by norm_num)
theorem B1026361 : Blo 810345 1026361 := bbase (se 2 (by rfl) ⟨384885, by rfl⟩ : syracuseStep 1026361 = 769771) (by norm_num)
theorem B2468165 : Blo 810345 2468165 := bbase (se 4 (by rfl) ⟨231390, by rfl⟩ : syracuseStep 2468165 = 462781) (by norm_num)
theorem B2107765 : Blo 810345 2107765 := bbase (se 5 (by rfl) ⟨98801, by rfl⟩ : syracuseStep 2107765 = 197603) (by norm_num)
theorem B3090869 : Blo 810345 3090869 := bbase (se 5 (by rfl) ⟨144884, by rfl⟩ : syracuseStep 3090869 = 289769) (by norm_num)
theorem B1026533 : Blo 810345 1026533 := bbase (se 4 (by rfl) ⟨96237, by rfl⟩ : syracuseStep 1026533 = 192475) (by norm_num)
theorem B1026589 : Blo 810345 1026589 := bbase (se 3 (by rfl) ⟨192485, by rfl⟩ : syracuseStep 1026589 = 384971) (by norm_num)
theorem B2108005 : Blo 810345 2108005 := bbase (se 4 (by rfl) ⟨197625, by rfl⟩ : syracuseStep 2108005 = 395251) (by norm_num)
theorem B1026685 : Blo 810345 1026685 := bbase (se 3 (by rfl) ⟨192503, by rfl⟩ : syracuseStep 1026685 = 385007) (by norm_num)
theorem B4238021 : Blo 810345 4238021 := bbase (se 4 (by rfl) ⟨397314, by rfl⟩ : syracuseStep 4238021 = 794629) (by norm_num)
theorem B3517141 : Blo 810345 3517141 := bbase (se 7 (by rfl) ⟨41216, by rfl⟩ : syracuseStep 3517141 = 82433) (by norm_num)
theorem B1026857 : Blo 810345 1026857 := bbase (se 2 (by rfl) ⟨385071, by rfl⟩ : syracuseStep 1026857 = 770143) (by norm_num)
theorem B1026913 : Blo 810345 1026913 := bbase (se 2 (by rfl) ⟨385092, by rfl⟩ : syracuseStep 1026913 = 770185) (by norm_num)
theorem B928609 : Blo 810345 928609 := bbase (se 2 (by rfl) ⟨348228, by rfl⟩ : syracuseStep 928609 = 696457) (by norm_num)
theorem B1027009 : Blo 810345 1027009 := bbase (se 2 (by rfl) ⟨385128, by rfl⟩ : syracuseStep 1027009 = 770257) (by norm_num)
theorem B1158085 : Blo 810345 1158085 := bbase (se 4 (by rfl) ⟨108570, by rfl⟩ : syracuseStep 1158085 = 217141) (by norm_num)
theorem B1027181 : Blo 810345 1027181 := bbase (se 3 (by rfl) ⟨192596, by rfl⟩ : syracuseStep 1027181 = 385193) (by norm_num)
theorem B4631701 : Blo 810345 4631701 := bbase (se 6 (by rfl) ⟨108555, by rfl⟩ : syracuseStep 4631701 = 217111) (by norm_num)
theorem B1027237 : Blo 810345 1027237 := bbase (se 4 (by rfl) ⟨96303, by rfl⟩ : syracuseStep 1027237 = 192607) (by norm_num)
theorem B4107509 : Blo 810345 4107509 := bbase (se 5 (by rfl) ⟨192539, by rfl⟩ : syracuseStep 4107509 = 385079) (by norm_num)
theorem B1027333 : Blo 810345 1027333 := bbase (se 4 (by rfl) ⟨96312, by rfl⟩ : syracuseStep 1027333 = 192625) (by norm_num)
theorem B2600309 : Blo 810345 2600309 := bbase (se 5 (by rfl) ⟨121889, by rfl⟩ : syracuseStep 2600309 = 243779) (by norm_num)
theorem B1027505 : Blo 810345 1027505 := bbase (se 2 (by rfl) ⟨385314, by rfl⟩ : syracuseStep 1027505 = 770629) (by norm_num)
theorem B1027561 : Blo 810345 1027561 := bbase (se 2 (by rfl) ⟨385335, by rfl⟩ : syracuseStep 1027561 = 770671) (by norm_num)
theorem B1027657 : Blo 810345 1027657 := bbase (se 2 (by rfl) ⟨385371, by rfl⟩ : syracuseStep 1027657 = 770743) (by norm_num)
theorem B1158877 : Blo 810345 1158877 := bbase (se 3 (by rfl) ⟨217289, by rfl⟩ : syracuseStep 1158877 = 434579) (by norm_num)
theorem B1027829 : Blo 810345 1027829 := bbase (se 5 (by rfl) ⟨48179, by rfl⟩ : syracuseStep 1027829 = 96359) (by norm_num)
theorem B1027885 : Blo 810345 1027885 := bbase (se 3 (by rfl) ⟨192728, by rfl⟩ : syracuseStep 1027885 = 385457) (by norm_num)
theorem B1027981 : Blo 810345 1027981 := bbase (se 3 (by rfl) ⟨192746, by rfl⟩ : syracuseStep 1027981 = 385493) (by norm_num)
theorem B1159213 : Blo 810345 1159213 := bbase (se 3 (by rfl) ⟨217352, by rfl⟩ : syracuseStep 1159213 = 434705) (by norm_num)
theorem B1028153 : Blo 810345 1028153 := bbase (se 2 (by rfl) ⟨385557, by rfl⟩ : syracuseStep 1028153 = 771115) (by norm_num)
theorem B1028209 : Blo 810345 1028209 := bbase (se 2 (by rfl) ⟨385578, by rfl⟩ : syracuseStep 1028209 = 771157) (by norm_num)
theorem B1978501 : Blo 810345 1978501 := bbase (se 4 (by rfl) ⟨185484, by rfl⟩ : syracuseStep 1978501 = 370969) (by norm_num)
theorem B1028305 : Blo 810345 1028305 := bbase (se 2 (by rfl) ⟨385614, by rfl⟩ : syracuseStep 1028305 = 771229) (by norm_num)
theorem B3518677 : Blo 810345 3518677 := bbase (se 7 (by rfl) ⟨41234, by rfl⟩ : syracuseStep 3518677 = 82469) (by norm_num)
theorem B6598901 : Blo 810345 6598901 := bbase (se 5 (by rfl) ⟨309323, by rfl⟩ : syracuseStep 6598901 = 618647) (by norm_num)
theorem B1159429 : Blo 810345 1159429 := bbase (se 4 (by rfl) ⟨108696, by rfl⟩ : syracuseStep 1159429 = 217393) (by norm_num)
theorem B1028477 : Blo 810345 1028477 := bbase (se 3 (by rfl) ⟨192839, by rfl⟩ : syracuseStep 1028477 = 385679) (by norm_num)
theorem B1028533 : Blo 810345 1028533 := bbase (se 5 (by rfl) ⟨48212, by rfl⟩ : syracuseStep 1028533 = 96425) (by norm_num)
theorem B3912133 : Blo 810345 3912133 := bbase (se 4 (by rfl) ⟨366762, by rfl⟩ : syracuseStep 3912133 = 733525) (by norm_num)
theorem B4108805 : Blo 810345 4108805 := bbase (se 4 (by rfl) ⟨385200, by rfl⟩ : syracuseStep 4108805 = 770401) (by norm_num)
theorem B1028629 : Blo 810345 1028629 := bbase (se 6 (by rfl) ⟨24108, by rfl⟩ : syracuseStep 1028629 = 48217) (by norm_num)
theorem B1487477 : Blo 810345 1487477 := bbase (se 5 (by rfl) ⟨69725, by rfl⟩ : syracuseStep 1487477 = 139451) (by norm_num)
theorem B1028801 : Blo 810345 1028801 := bbase (se 2 (by rfl) ⟨385800, by rfl⟩ : syracuseStep 1028801 = 771601) (by norm_num)
theorem B1389269 : Blo 810345 1389269 := bbase (se 7 (by rfl) ⟨16280, by rfl⟩ : syracuseStep 1389269 = 32561) (by norm_num)
theorem B1028857 : Blo 810345 1028857 := bbase (se 2 (by rfl) ⟨385821, by rfl⟩ : syracuseStep 1028857 = 771643) (by norm_num)
theorem B2601733 : Blo 810345 2601733 := bbase (se 4 (by rfl) ⟨243912, by rfl⟩ : syracuseStep 2601733 = 487825) (by norm_num)
theorem B1028953 : Blo 810345 1028953 := bbase (se 2 (by rfl) ⟨385857, by rfl⟩ : syracuseStep 1028953 = 771715) (by norm_num)
theorem B1029125 : Blo 810345 1029125 := bbase (se 4 (by rfl) ⟨96480, by rfl⟩ : syracuseStep 1029125 = 192961) (by norm_num)
theorem B7025717 : Blo 810345 7025717 := bbase (se 5 (by rfl) ⟨329330, by rfl⟩ : syracuseStep 7025717 = 658661) (by norm_num)
theorem B1029181 : Blo 810345 1029181 := bbase (se 3 (by rfl) ⟨192971, by rfl⟩ : syracuseStep 1029181 = 385943) (by norm_num)
theorem B4633685 : Blo 810345 4633685 := bbase (se 8 (by rfl) ⟨27150, by rfl⟩ : syracuseStep 4633685 = 54301) (by norm_num)
theorem B1029277 : Blo 810345 1029277 := bbase (se 3 (by rfl) ⟨192989, by rfl⟩ : syracuseStep 1029277 = 385979) (by norm_num)
theorem B2602181 : Blo 810345 2602181 := bbase (se 4 (by rfl) ⟨243954, by rfl⟩ : syracuseStep 2602181 = 487909) (by norm_num)
theorem B1029449 : Blo 810345 1029449 := bbase (se 2 (by rfl) ⟨386043, by rfl⟩ : syracuseStep 1029449 = 772087) (by norm_num)
theorem B865625 : Blo 810345 865625 := bbase (se 2 (by rfl) ⟨324609, by rfl⟩ : syracuseStep 865625 = 649219) (by norm_num)
theorem B1029505 : Blo 810345 1029505 := bbase (se 2 (by rfl) ⟨386064, by rfl⟩ : syracuseStep 1029505 = 772129) (by norm_num)
theorem B865685 : Blo 810345 865685 := bbase (se 6 (by rfl) ⟨20289, by rfl⟩ : syracuseStep 865685 = 40579) (by norm_num)
theorem B1029601 : Blo 810345 1029601 := bbase (se 2 (by rfl) ⟨386100, by rfl⟩ : syracuseStep 1029601 = 772201) (by norm_num)
theorem B1947149 : Blo 810345 1947149 := bbase (se 3 (by rfl) ⟨365090, by rfl⟩ : syracuseStep 1947149 = 730181) (by norm_num)
theorem B865813 : Blo 810345 865813 := bbase (se 6 (by rfl) ⟨20292, by rfl⟩ : syracuseStep 865813 = 40585) (by norm_num)
theorem B2471525 : Blo 810345 2471525 := bbase (se 4 (by rfl) ⟨231705, by rfl⟩ : syracuseStep 2471525 = 463411) (by norm_num)
theorem B1029773 : Blo 810345 1029773 := bbase (se 3 (by rfl) ⟨193082, by rfl⟩ : syracuseStep 1029773 = 386165) (by norm_num)
theorem B1029829 : Blo 810345 1029829 := bbase (se 4 (by rfl) ⟨96546, by rfl⟩ : syracuseStep 1029829 = 193093) (by norm_num)
theorem B1947349 : Blo 810345 1947349 := bbase (se 7 (by rfl) ⟨22820, by rfl⟩ : syracuseStep 1947349 = 45641) (by norm_num)
theorem B4110101 : Blo 810345 4110101 := bbase (se 6 (by rfl) ⟨96330, by rfl⟩ : syracuseStep 4110101 = 192661) (by norm_num)
theorem B1029925 : Blo 810345 1029925 := bbase (se 4 (by rfl) ⟨96555, by rfl⟩ : syracuseStep 1029925 = 193111) (by norm_num)
theorem B866257 : Blo 810345 866257 := bbase (se 2 (by rfl) ⟨324846, by rfl⟩ : syracuseStep 866257 = 649693) (by norm_num)
theorem B1030097 : Blo 810345 1030097 := bbase (se 2 (by rfl) ⟨386286, by rfl⟩ : syracuseStep 1030097 = 772573) (by norm_num)
theorem B1030153 : Blo 810345 1030153 := bbase (se 2 (by rfl) ⟨386307, by rfl⟩ : syracuseStep 1030153 = 772615) (by norm_num)
theorem B866377 : Blo 810345 866377 := bbase (se 2 (by rfl) ⟨324891, by rfl⟩ : syracuseStep 866377 = 649783) (by norm_num)
theorem B1030249 : Blo 810345 1030249 := bbase (se 2 (by rfl) ⟨386343, by rfl⟩ : syracuseStep 1030249 = 772687) (by norm_num)
theorem B2308277 : Blo 810345 2308277 := bbase (se 5 (by rfl) ⟨108200, by rfl⟩ : syracuseStep 2308277 = 216401) (by norm_num)
theorem B1095877 : Blo 810345 1095877 := bbase (se 4 (by rfl) ⟨102738, by rfl⟩ : syracuseStep 1095877 = 205477) (by norm_num)
theorem B1095925 : Blo 810345 1095925 := bbase (se 5 (by rfl) ⟨51371, by rfl⟩ : syracuseStep 1095925 = 102743) (by norm_num)
theorem B1030421 : Blo 810345 1030421 := bbase (se 6 (by rfl) ⟨24150, by rfl⟩ : syracuseStep 1030421 = 48301) (by norm_num)
theorem B866629 : Blo 810345 866629 := bbase (se 4 (by rfl) ⟨81246, by rfl⟩ : syracuseStep 866629 = 162493) (by norm_num)
theorem B866633 : Blo 810345 866633 := bbase (se 2 (by rfl) ⟨324987, by rfl⟩ : syracuseStep 866633 = 649975) (by norm_num)
theorem B1030477 : Blo 810345 1030477 := bbase (se 3 (by rfl) ⟨193214, by rfl⟩ : syracuseStep 1030477 = 386429) (by norm_num)
theorem B1030573 : Blo 810345 1030573 := bbase (se 3 (by rfl) ⟨193232, by rfl⟩ : syracuseStep 1030573 = 386465) (by norm_num)
theorem B1096141 : Blo 810345 1096141 := bbase (se 3 (by rfl) ⟨205526, by rfl⟩ : syracuseStep 1096141 = 411053) (by norm_num)
theorem B1948157 : Blo 810345 1948157 := bbase (se 3 (by rfl) ⟨365279, by rfl⟩ : syracuseStep 1948157 = 730559) (by norm_num)
theorem B2931461 : Blo 810345 2931461 := bbase (se 4 (by rfl) ⟨274824, by rfl⟩ : syracuseStep 2931461 = 549649) (by norm_num)
theorem B2308949 : Blo 810345 2308949 := bbase (se 9 (by rfl) ⟨6764, by rfl⟩ : syracuseStep 2308949 = 13529) (by norm_num)
theorem B867197 : Blo 810345 867197 := bbase (se 3 (by rfl) ⟨162599, by rfl⟩ : syracuseStep 867197 = 325199) (by norm_num)
theorem B2735045 : Blo 810345 2735045 := bbase (se 4 (by rfl) ⟨256410, by rfl⟩ : syracuseStep 2735045 = 512821) (by norm_num)
theorem B1391573 : Blo 810345 1391573 := bbase (se 7 (by rfl) ⟨16307, by rfl⟩ : syracuseStep 1391573 = 32615) (by norm_num)
theorem B4111397 : Blo 810345 4111397 := bbase (se 4 (by rfl) ⟨385443, by rfl⟩ : syracuseStep 4111397 = 770887) (by norm_num)
theorem B867385 : Blo 810345 867385 := bbase (se 2 (by rfl) ⟨325269, by rfl⟩ : syracuseStep 867385 = 650539) (by norm_num)
theorem B23379029 : Blo 810345 23379029 := bbase (se 8 (by rfl) ⟨136986, by rfl⟩ : syracuseStep 23379029 = 273973) (by norm_num)
theorem B4635893 : Blo 810345 4635893 := bbase (se 5 (by rfl) ⟨217307, by rfl⟩ : syracuseStep 4635893 = 434615) (by norm_num)
theorem B1948925 : Blo 810345 1948925 := bbase (se 3 (by rfl) ⟨365423, by rfl⟩ : syracuseStep 1948925 = 730847) (by norm_num)
theorem B2309381 : Blo 810345 2309381 := bbase (se 4 (by rfl) ⟨216504, by rfl⟩ : syracuseStep 2309381 = 433009) (by norm_num)
theorem B11124053 : Blo 810345 11124053 := bbase (se 11 (by rfl) ⟨8147, by rfl⟩ : syracuseStep 11124053 = 16295) (by norm_num)
theorem B2735477 : Blo 810345 2735477 := bbase (se 5 (by rfl) ⟨128225, by rfl⟩ : syracuseStep 2735477 = 256451) (by norm_num)
theorem B2604437 : Blo 810345 2604437 := bbase (se 6 (by rfl) ⟨61041, by rfl⟩ : syracuseStep 2604437 = 122083) (by norm_num)
theorem B6766037 : Blo 810345 6766037 := bbase (se 7 (by rfl) ⟨79289, by rfl⟩ : syracuseStep 6766037 = 158579) (by norm_num)
theorem B2735909 : Blo 810345 2735909 := bbase (se 4 (by rfl) ⟨256491, by rfl⟩ : syracuseStep 2735909 = 512983) (by norm_num)
theorem B868205 : Blo 810345 868205 := bbase (se 3 (by rfl) ⟨162788, by rfl⟩ : syracuseStep 868205 = 325577) (by norm_num)
theorem B2080709 : Blo 810345 2080709 := bbase (se 4 (by rfl) ⟨195066, by rfl⟩ : syracuseStep 2080709 = 390133) (by norm_num)
theorem B2310133 : Blo 810345 2310133 := bbase (se 5 (by rfl) ⟨108287, by rfl⟩ : syracuseStep 2310133 = 216575) (by norm_num)
theorem B8896661 : Blo 810345 8896661 := bbase (se 6 (by rfl) ⟨208515, by rfl⟩ : syracuseStep 8896661 = 417031) (by norm_num)
theorem B2736341 : Blo 810345 2736341 := bbase (se 7 (by rfl) ⟨32066, by rfl⟩ : syracuseStep 2736341 = 64133) (by norm_num)
theorem B868649 : Blo 810345 868649 := bbase (se 2 (by rfl) ⟨325743, by rfl⟩ : syracuseStep 868649 = 651487) (by norm_num)
theorem B4112693 : Blo 810345 4112693 := bbase (se 5 (by rfl) ⟨192782, by rfl⟩ : syracuseStep 4112693 = 385565) (by norm_num)
theorem B2113997 : Blo 810345 2113997 := bbase (se 3 (by rfl) ⟨396374, by rfl⟩ : syracuseStep 2113997 = 792749) (by norm_num)
theorem B2081285 : Blo 810345 2081285 := bbase (se 4 (by rfl) ⟨195120, by rfl⟩ : syracuseStep 2081285 = 390241) (by norm_num)
theorem B6242837 : Blo 810345 6242837 := bbase (se 6 (by rfl) ⟨146316, by rfl⟩ : syracuseStep 6242837 = 292633) (by norm_num)
theorem B868897 : Blo 810345 868897 := bbase (se 2 (by rfl) ⟨325836, by rfl⟩ : syracuseStep 868897 = 651673) (by norm_num)
theorem B2736773 : Blo 810345 2736773 := bbase (se 4 (by rfl) ⟨256572, by rfl⟩ : syracuseStep 2736773 = 513145) (by norm_num)
theorem B2474869 : Blo 810345 2474869 := bbase (se 5 (by rfl) ⟨116009, by rfl⟩ : syracuseStep 2474869 = 232019) (by norm_num)
theorem B1950637 : Blo 810345 1950637 := bbase (se 3 (by rfl) ⟨365744, by rfl⟩ : syracuseStep 1950637 = 731489) (by norm_num)
theorem B2081717 : Blo 810345 2081717 := bbase (se 5 (by rfl) ⟨97580, by rfl⟩ : syracuseStep 2081717 = 195161) (by norm_num)
theorem B869329 : Blo 810345 869329 := bbase (se 2 (by rfl) ⟨325998, by rfl⟩ : syracuseStep 869329 = 651997) (by norm_num)
theorem B869401 : Blo 810345 869401 := bbase (se 2 (by rfl) ⟨326025, by rfl⟩ : syracuseStep 869401 = 652051) (by norm_num)
theorem B2737205 : Blo 810345 2737205 := bbase (se 5 (by rfl) ⟨128306, by rfl⟩ : syracuseStep 2737205 = 256613) (by norm_num)
theorem B2933941 : Blo 810345 2933941 := bbase (se 5 (by rfl) ⟨137528, by rfl⟩ : syracuseStep 2933941 = 275057) (by norm_num)
theorem B1099093 : Blo 810345 1099093 := bbase (se 12 (by rfl) ⟨402, by rfl⟩ : syracuseStep 1099093 = 805) (by norm_num)
theorem B1852877 : Blo 810345 1852877 := bbase (se 3 (by rfl) ⟨347414, by rfl⟩ : syracuseStep 1852877 = 694829) (by norm_num)
theorem B2737637 : Blo 810345 2737637 := bbase (se 4 (by rfl) ⟨256653, by rfl⟩ : syracuseStep 2737637 = 513307) (by norm_num)
theorem B1951253 : Blo 810345 1951253 := bbase (se 6 (by rfl) ⟨45732, by rfl⟩ : syracuseStep 1951253 = 91465) (by norm_num)
theorem B4113989 : Blo 810345 4113989 := bbase (se 4 (by rfl) ⟨385686, by rfl⟩ : syracuseStep 4113989 = 771373) (by norm_num)
theorem B6178517 : Blo 810345 6178517 := bbase (se 7 (by rfl) ⟨72404, by rfl⟩ : syracuseStep 6178517 = 144809) (by norm_num)
theorem B2738069 : Blo 810345 2738069 := bbase (se 6 (by rfl) ⟨64173, by rfl⟩ : syracuseStep 2738069 = 128347) (by norm_num)
theorem B1951685 : Blo 810345 1951685 := bbase (se 4 (by rfl) ⟨182970, by rfl⟩ : syracuseStep 1951685 = 365941) (by norm_num)
theorem B1853381 : Blo 810345 1853381 := bbase (se 4 (by rfl) ⟨173754, by rfl⟩ : syracuseStep 1853381 = 347509) (by norm_num)
theorem B1853533 : Blo 810345 1853533 := bbase (se 3 (by rfl) ⟨347537, by rfl⟩ : syracuseStep 1853533 = 695075) (by norm_num)
theorem B1755245 : Blo 810345 1755245 := bbase (se 3 (by rfl) ⟨329108, by rfl⟩ : syracuseStep 1755245 = 658217) (by norm_num)
theorem B2738501 : Blo 810345 2738501 := bbase (se 4 (by rfl) ⟨256734, by rfl⟩ : syracuseStep 2738501 = 513469) (by norm_num)
theorem B2083421 : Blo 810345 2083421 := bbase (se 3 (by rfl) ⟨390641, by rfl⟩ : syracuseStep 2083421 = 781283) (by norm_num)
theorem B1100461 : Blo 810345 1100461 := bbase (se 3 (by rfl) ⟨206336, by rfl⟩ : syracuseStep 1100461 = 412673) (by norm_num)
theorem B1100477 : Blo 810345 1100477 := bbase (se 3 (by rfl) ⟨206339, by rfl⟩ : syracuseStep 1100477 = 412679) (by norm_num)
theorem B2738933 : Blo 810345 2738933 := bbase (se 5 (by rfl) ⟨128387, by rfl⟩ : syracuseStep 2738933 = 256775) (by norm_num)
theorem B2312981 : Blo 810345 2312981 := bbase (se 6 (by rfl) ⟨54210, by rfl⟩ : syracuseStep 2312981 = 108421) (by norm_num)
theorem B4115285 : Blo 810345 4115285 := bbase (se 9 (by rfl) ⟨12056, by rfl⟩ : syracuseStep 4115285 = 24113) (by norm_num)
theorem B1559485 : Blo 810345 1559485 := bbase (se 3 (by rfl) ⟨292403, by rfl⟩ : syracuseStep 1559485 = 584807) (by norm_num)
theorem B2116589 : Blo 810345 2116589 := bbase (se 3 (by rfl) ⟨396860, by rfl⟩ : syracuseStep 2116589 = 793721) (by norm_num)
theorem B1559669 : Blo 810345 1559669 := bbase (se 5 (by rfl) ⟨73109, by rfl⟩ : syracuseStep 1559669 = 146219) (by norm_num)
theorem B1952885 : Blo 810345 1952885 := bbase (se 5 (by rfl) ⟨91541, by rfl⟩ : syracuseStep 1952885 = 183083) (by norm_num)
theorem B2739365 : Blo 810345 2739365 := bbase (se 4 (by rfl) ⟨256815, by rfl⟩ : syracuseStep 2739365 = 513631) (by norm_num)
theorem B2608357 : Blo 810345 2608357 := bbase (se 4 (by rfl) ⟨244533, by rfl⟩ : syracuseStep 2608357 = 489067) (by norm_num)
theorem B2051365 : Blo 810345 2051365 := bbase (se 4 (by rfl) ⟨192315, by rfl⟩ : syracuseStep 2051365 = 384631) (by norm_num)
theorem B2051477 : Blo 810345 2051477 := bbase (se 6 (by rfl) ⟨48081, by rfl⟩ : syracuseStep 2051477 = 96163) (by norm_num)
theorem B2608613 : Blo 810345 2608613 := bbase (se 4 (by rfl) ⟨244557, by rfl⟩ : syracuseStep 2608613 = 489115) (by norm_num)
theorem B1232381 : Blo 810345 1232381 := bbase (se 3 (by rfl) ⟨231071, by rfl⟩ : syracuseStep 1232381 = 462143) (by norm_num)
theorem B2051669 : Blo 810345 2051669 := bbase (se 8 (by rfl) ⟨12021, by rfl⟩ : syracuseStep 2051669 = 24043) (by norm_num)
theorem B2739797 : Blo 810345 2739797 := bbase (se 8 (by rfl) ⟨16053, by rfl⟩ : syracuseStep 2739797 = 32107) (by norm_num)
theorem B1298053 : Blo 810345 1298053 := bbase (se 4 (by rfl) ⟨121692, by rfl⟩ : syracuseStep 1298053 = 243385) (by norm_num)
theorem B1855157 : Blo 810345 1855157 := bbase (se 5 (by rfl) ⟨86960, by rfl⟩ : syracuseStep 1855157 = 173921) (by norm_num)
theorem B3952421 : Blo 810345 3952421 := bbase (se 4 (by rfl) ⟨370539, by rfl⟩ : syracuseStep 3952421 = 741079) (by norm_num)
theorem B2052013 : Blo 810345 2052013 := bbase (se 3 (by rfl) ⟨384752, by rfl⟩ : syracuseStep 2052013 = 769505) (by norm_num)
theorem B2314165 : Blo 810345 2314165 := bbase (se 5 (by rfl) ⟨108476, by rfl⟩ : syracuseStep 2314165 = 216953) (by norm_num)
theorem B1462213 : Blo 810345 1462213 := bbase (se 4 (by rfl) ⟨137082, by rfl⟩ : syracuseStep 1462213 = 274165) (by norm_num)
theorem B2740229 : Blo 810345 2740229 := bbase (se 4 (by rfl) ⟨256896, by rfl⟩ : syracuseStep 2740229 = 513793) (by norm_num)
theorem B2052125 : Blo 810345 2052125 := bbase (se 3 (by rfl) ⟨384773, by rfl⟩ : syracuseStep 2052125 = 769547) (by norm_num)
theorem B1462357 : Blo 810345 1462357 := bbase (se 8 (by rfl) ⟨8568, by rfl⟩ : syracuseStep 1462357 = 17137) (by norm_num)
theorem B2314325 : Blo 810345 2314325 := bbase (se 8 (by rfl) ⟨13560, by rfl⟩ : syracuseStep 2314325 = 27121) (by norm_num)
theorem B4116581 : Blo 810345 4116581 := bbase (se 4 (by rfl) ⟨385929, by rfl⟩ : syracuseStep 4116581 = 771859) (by norm_num)
theorem B2052317 : Blo 810345 2052317 := bbase (se 3 (by rfl) ⟨384809, by rfl⟩ : syracuseStep 2052317 = 769619) (by norm_num)
theorem B2314565 : Blo 810345 2314565 := bbase (se 4 (by rfl) ⟨216990, by rfl⟩ : syracuseStep 2314565 = 433981) (by norm_num)
theorem B2740661 : Blo 810345 2740661 := bbase (se 5 (by rfl) ⟨128468, by rfl⟩ : syracuseStep 2740661 = 256937) (by norm_num)
theorem B2314757 : Blo 810345 2314757 := bbase (se 4 (by rfl) ⟨217008, by rfl⟩ : syracuseStep 2314757 = 434017) (by norm_num)
theorem B2052661 : Blo 810345 2052661 := bbase (se 5 (by rfl) ⟨96218, by rfl⟩ : syracuseStep 2052661 = 192437) (by norm_num)
theorem B1561141 : Blo 810345 1561141 := bbase (se 5 (by rfl) ⟨73178, by rfl⟩ : syracuseStep 1561141 = 146357) (by norm_num)
theorem B1823309 : Blo 810345 1823309 := bbase (se 3 (by rfl) ⟨341870, by rfl⟩ : syracuseStep 1823309 = 683741) (by norm_num)
theorem B1299053 : Blo 810345 1299053 := bbase (se 3 (by rfl) ⟨243572, by rfl⟩ : syracuseStep 1299053 = 487145) (by norm_num)
theorem B1823381 : Blo 810345 1823381 := bbase (se 6 (by rfl) ⟨42735, by rfl⟩ : syracuseStep 1823381 = 85471) (by norm_num)
theorem B2052773 : Blo 810345 2052773 := bbase (se 4 (by rfl) ⟨192447, by rfl⟩ : syracuseStep 2052773 = 384895) (by norm_num)
theorem B1823453 : Blo 810345 1823453 := bbase (se 3 (by rfl) ⟨341897, by rfl⟩ : syracuseStep 1823453 = 683795) (by norm_num)
theorem B1299181 : Blo 810345 1299181 := bbase (se 3 (by rfl) ⟨243596, by rfl⟩ : syracuseStep 1299181 = 487193) (by norm_num)
theorem B1823525 : Blo 810345 1823525 := bbase (se 4 (by rfl) ⟨170955, by rfl⟩ : syracuseStep 1823525 = 341911) (by norm_num)
theorem B1299245 : Blo 810345 1299245 := bbase (se 3 (by rfl) ⟨243608, by rfl⟩ : syracuseStep 1299245 = 487217) (by norm_num)
theorem B2052965 : Blo 810345 2052965 := bbase (se 4 (by rfl) ⟨192465, by rfl⟩ : syracuseStep 2052965 = 384931) (by norm_num)
theorem B2741093 : Blo 810345 2741093 := bbase (se 4 (by rfl) ⟨256977, by rfl⟩ : syracuseStep 2741093 = 513955) (by norm_num)
theorem B1823597 : Blo 810345 1823597 := bbase (se 3 (by rfl) ⟨341924, by rfl⟩ : syracuseStep 1823597 = 683849) (by norm_num)
theorem B1823669 : Blo 810345 1823669 := bbase (se 5 (by rfl) ⟨85484, by rfl⟩ : syracuseStep 1823669 = 170969) (by norm_num)
theorem B1823741 : Blo 810345 1823741 := bbase (se 3 (by rfl) ⟨341951, by rfl⟩ : syracuseStep 1823741 = 683903) (by norm_num)
theorem B1856525 : Blo 810345 1856525 := bbase (se 3 (by rfl) ⟨348098, by rfl⟩ : syracuseStep 1856525 = 696197) (by norm_num)
theorem B1823813 : Blo 810345 1823813 := bbase (se 4 (by rfl) ⟨170982, by rfl⟩ : syracuseStep 1823813 = 341965) (by norm_num)
theorem B1823885 : Blo 810345 1823885 := bbase (se 3 (by rfl) ⟨341978, by rfl⟩ : syracuseStep 1823885 = 683957) (by norm_num)
theorem B2053309 : Blo 810345 2053309 := bbase (se 3 (by rfl) ⟨384995, by rfl⟩ : syracuseStep 2053309 = 769991) (by norm_num)
theorem B1823957 : Blo 810345 1823957 := bbase (se 7 (by rfl) ⟨21374, by rfl⟩ : syracuseStep 1823957 = 42749) (by norm_num)
theorem B2741525 : Blo 810345 2741525 := bbase (se 6 (by rfl) ⟨64254, by rfl⟩ : syracuseStep 2741525 = 128509) (by norm_num)
theorem B1824029 : Blo 810345 1824029 := bbase (se 3 (by rfl) ⟨342005, by rfl⟩ : syracuseStep 1824029 = 684011) (by norm_num)
theorem B2053421 : Blo 810345 2053421 := bbase (se 3 (by rfl) ⟨385016, by rfl⟩ : syracuseStep 2053421 = 770033) (by norm_num)
theorem B1463597 : Blo 810345 1463597 := bbase (se 3 (by rfl) ⟨274424, by rfl⟩ : syracuseStep 1463597 = 548849) (by norm_num)
theorem B1824101 : Blo 810345 1824101 := bbase (se 4 (by rfl) ⟨171009, by rfl⟩ : syracuseStep 1824101 = 342019) (by norm_num)
theorem B1955173 : Blo 810345 1955173 := bbase (se 4 (by rfl) ⟨183297, by rfl⟩ : syracuseStep 1955173 = 366595) (by norm_num)
theorem B4117877 : Blo 810345 4117877 := bbase (se 5 (by rfl) ⟨193025, by rfl⟩ : syracuseStep 4117877 = 386051) (by norm_num)
theorem B1824173 : Blo 810345 1824173 := bbase (se 3 (by rfl) ⟨342032, by rfl⟩ : syracuseStep 1824173 = 684065) (by norm_num)
theorem B1955269 : Blo 810345 1955269 := bbase (se 4 (by rfl) ⟨183306, by rfl⟩ : syracuseStep 1955269 = 366613) (by norm_num)
theorem B2315749 : Blo 810345 2315749 := bbase (se 4 (by rfl) ⟨217101, by rfl⟩ : syracuseStep 2315749 = 434203) (by norm_num)
theorem B2053613 : Blo 810345 2053613 := bbase (se 3 (by rfl) ⟨385052, by rfl⟩ : syracuseStep 2053613 = 770105) (by norm_num)
theorem B1824245 : Blo 810345 1824245 := bbase (se 5 (by rfl) ⟨85511, by rfl⟩ : syracuseStep 1824245 = 171023) (by norm_num)
theorem B1824317 : Blo 810345 1824317 := bbase (se 3 (by rfl) ⟨342059, by rfl⟩ : syracuseStep 1824317 = 684119) (by norm_num)
theorem B31217237 : Blo 810345 31217237 := bbase (se 8 (by rfl) ⟨182913, by rfl⟩ : syracuseStep 31217237 = 365827) (by norm_num)
theorem B1824389 : Blo 810345 1824389 := bbase (se 4 (by rfl) ⟨171036, by rfl⟩ : syracuseStep 1824389 = 342073) (by norm_num)
theorem B1955461 : Blo 810345 1955461 := bbase (se 4 (by rfl) ⟨183324, by rfl⟩ : syracuseStep 1955461 = 366649) (by norm_num)
theorem B2741957 : Blo 810345 2741957 := bbase (se 4 (by rfl) ⟨257058, by rfl⟩ : syracuseStep 2741957 = 514117) (by norm_num)
theorem B1824461 : Blo 810345 1824461 := bbase (se 3 (by rfl) ⟨342086, by rfl⟩ : syracuseStep 1824461 = 684173) (by norm_num)
theorem B1824533 : Blo 810345 1824533 := bbase (se 6 (by rfl) ⟨42762, by rfl⟩ : syracuseStep 1824533 = 85525) (by norm_num)
theorem B2053957 : Blo 810345 2053957 := bbase (se 4 (by rfl) ⟨192558, by rfl⟩ : syracuseStep 2053957 = 385117) (by norm_num)
theorem B1824605 : Blo 810345 1824605 := bbase (se 3 (by rfl) ⟨342113, by rfl⟩ : syracuseStep 1824605 = 684227) (by norm_num)
theorem B3463013 : Blo 810345 3463013 := bbase (se 4 (by rfl) ⟨324657, by rfl⟩ : syracuseStep 3463013 = 649315) (by norm_num)
theorem B1824677 : Blo 810345 1824677 := bbase (se 4 (by rfl) ⟨171063, by rfl⟩ : syracuseStep 1824677 = 342127) (by norm_num)
theorem B2054069 : Blo 810345 2054069 := bbase (se 5 (by rfl) ⟨96284, by rfl⟩ : syracuseStep 2054069 = 192569) (by norm_num)
theorem B1955789 : Blo 810345 1955789 := bbase (se 3 (by rfl) ⟨366710, by rfl⟩ : syracuseStep 1955789 = 733421) (by norm_num)
theorem B1824749 : Blo 810345 1824749 := bbase (se 3 (by rfl) ⟨342140, by rfl⟩ : syracuseStep 1824749 = 684281) (by norm_num)
theorem B1824821 : Blo 810345 1824821 := bbase (se 5 (by rfl) ⟨85538, by rfl⟩ : syracuseStep 1824821 = 171077) (by norm_num)
theorem B1300565 : Blo 810345 1300565 := bbase (se 8 (by rfl) ⟨7620, by rfl⟩ : syracuseStep 1300565 = 15241) (by norm_num)
theorem B2054261 : Blo 810345 2054261 := bbase (se 5 (by rfl) ⟨96293, by rfl⟩ : syracuseStep 2054261 = 192587) (by norm_num)
theorem B2742389 : Blo 810345 2742389 := bbase (se 5 (by rfl) ⟨128549, by rfl⟩ : syracuseStep 2742389 = 257099) (by norm_num)
theorem B1824893 : Blo 810345 1824893 := bbase (se 3 (by rfl) ⟨342167, by rfl⟩ : syracuseStep 1824893 = 684335) (by norm_num)
theorem B1824965 : Blo 810345 1824965 := bbase (se 4 (by rfl) ⟨171090, by rfl⟩ : syracuseStep 1824965 = 342181) (by norm_num)
theorem B1300693 : Blo 810345 1300693 := bbase (se 7 (by rfl) ⟨15242, by rfl⟩ : syracuseStep 1300693 = 30485) (by norm_num)
theorem B1825037 : Blo 810345 1825037 := bbase (se 3 (by rfl) ⟨342194, by rfl⟩ : syracuseStep 1825037 = 684389) (by norm_num)
theorem B1825109 : Blo 810345 1825109 := bbase (se 10 (by rfl) ⟨2673, by rfl⟩ : syracuseStep 1825109 = 5347) (by norm_num)
theorem B1956221 : Blo 810345 1956221 := bbase (se 3 (by rfl) ⟨366791, by rfl⟩ : syracuseStep 1956221 = 733583) (by norm_num)
theorem B1825181 : Blo 810345 1825181 := bbase (se 3 (by rfl) ⟨342221, by rfl⟩ : syracuseStep 1825181 = 684443) (by norm_num)
theorem B2054605 : Blo 810345 2054605 := bbase (se 3 (by rfl) ⟨385238, by rfl⟩ : syracuseStep 2054605 = 770477) (by norm_num)
theorem B1825253 : Blo 810345 1825253 := bbase (se 4 (by rfl) ⟨171117, by rfl⟩ : syracuseStep 1825253 = 342235) (by norm_num)
theorem B2742821 : Blo 810345 2742821 := bbase (se 4 (by rfl) ⟨257139, by rfl⟩ : syracuseStep 2742821 = 514279) (by norm_num)
theorem B1825325 : Blo 810345 1825325 := bbase (se 3 (by rfl) ⟨342248, by rfl⟩ : syracuseStep 1825325 = 684497) (by norm_num)
theorem B2316853 : Blo 810345 2316853 := bbase (se 5 (by rfl) ⟨108602, by rfl⟩ : syracuseStep 2316853 = 217205) (by norm_num)
theorem B2054717 : Blo 810345 2054717 := bbase (se 3 (by rfl) ⟨385259, by rfl⟩ : syracuseStep 2054717 = 770519) (by norm_num)
theorem B1825397 : Blo 810345 1825397 := bbase (se 5 (by rfl) ⟨85565, by rfl⟩ : syracuseStep 1825397 = 171131) (by norm_num)
theorem B4119173 : Blo 810345 4119173 := bbase (se 4 (by rfl) ⟨386172, by rfl⟩ : syracuseStep 4119173 = 772345) (by norm_num)
theorem B1825469 : Blo 810345 1825469 := bbase (se 3 (by rfl) ⟨342275, by rfl⟩ : syracuseStep 1825469 = 684551) (by norm_num)
theorem B1956557 : Blo 810345 1956557 := bbase (se 3 (by rfl) ⟨366854, by rfl⟩ : syracuseStep 1956557 = 733709) (by norm_num)
theorem B2054909 : Blo 810345 2054909 := bbase (se 3 (by rfl) ⟨385295, by rfl⟩ : syracuseStep 2054909 = 770591) (by norm_num)
theorem B1825541 : Blo 810345 1825541 := bbase (se 4 (by rfl) ⟨171144, by rfl⟩ : syracuseStep 1825541 = 342289) (by norm_num)
theorem B1825613 : Blo 810345 1825613 := bbase (se 3 (by rfl) ⟨342302, by rfl⟩ : syracuseStep 1825613 = 684605) (by norm_num)
theorem B1825685 : Blo 810345 1825685 := bbase (se 6 (by rfl) ⟨42789, by rfl⟩ : syracuseStep 1825685 = 85579) (by norm_num)
theorem B1465285 : Blo 810345 1465285 := bbase (se 4 (by rfl) ⟨137370, by rfl⟩ : syracuseStep 1465285 = 274741) (by norm_num)
theorem B2743253 : Blo 810345 2743253 := bbase (se 7 (by rfl) ⟨32147, by rfl⟩ : syracuseStep 2743253 = 64295) (by norm_num)
theorem B1825757 : Blo 810345 1825757 := bbase (se 3 (by rfl) ⟨342329, by rfl⟩ : syracuseStep 1825757 = 684659) (by norm_num)
theorem B1301501 : Blo 810345 1301501 := bbase (se 3 (by rfl) ⟨244031, by rfl⟩ : syracuseStep 1301501 = 488063) (by norm_num)
theorem B1825829 : Blo 810345 1825829 := bbase (se 4 (by rfl) ⟨171171, by rfl⟩ : syracuseStep 1825829 = 342343) (by norm_num)
theorem B2055253 : Blo 810345 2055253 := bbase (se 8 (by rfl) ⟨12042, by rfl⟩ : syracuseStep 2055253 = 24085) (by norm_num)
theorem B2088037 : Blo 810345 2088037 := bbase (se 4 (by rfl) ⟨195753, by rfl⟩ : syracuseStep 2088037 = 391507) (by norm_num)
theorem B1825901 : Blo 810345 1825901 := bbase (se 3 (by rfl) ⟨342356, by rfl⟩ : syracuseStep 1825901 = 684713) (by norm_num)
theorem B1825973 : Blo 810345 1825973 := bbase (se 5 (by rfl) ⟨85592, by rfl⟩ : syracuseStep 1825973 = 171185) (by norm_num)
theorem B2055365 : Blo 810345 2055365 := bbase (se 4 (by rfl) ⟨192690, by rfl⟩ : syracuseStep 2055365 = 385381) (by norm_num)
theorem B1465573 : Blo 810345 1465573 := bbase (se 4 (by rfl) ⟨137397, by rfl⟩ : syracuseStep 1465573 = 274795) (by norm_num)
theorem B1826045 : Blo 810345 1826045 := bbase (se 3 (by rfl) ⟨342383, by rfl⟩ : syracuseStep 1826045 = 684767) (by norm_num)
theorem B1301789 : Blo 810345 1301789 := bbase (se 3 (by rfl) ⟨244085, by rfl⟩ : syracuseStep 1301789 = 488171) (by norm_num)
theorem B1826117 : Blo 810345 1826117 := bbase (se 4 (by rfl) ⟨171198, by rfl⟩ : syracuseStep 1826117 = 342397) (by norm_num)
theorem B3169637 : Blo 810345 3169637 := bbase (se 4 (by rfl) ⟨297153, by rfl⟩ : syracuseStep 3169637 = 594307) (by norm_num)
theorem B2055557 : Blo 810345 2055557 := bbase (se 4 (by rfl) ⟨192708, by rfl⟩ : syracuseStep 2055557 = 385417) (by norm_num)
theorem B2743685 : Blo 810345 2743685 := bbase (se 4 (by rfl) ⟨257220, by rfl⟩ : syracuseStep 2743685 = 514441) (by norm_num)
theorem B1826189 : Blo 810345 1826189 := bbase (se 3 (by rfl) ⟨342410, by rfl⟩ : syracuseStep 1826189 = 684821) (by norm_num)
theorem B1367509 : Blo 810345 1367509 := bbase (se 7 (by rfl) ⟨16025, by rfl⟩ : syracuseStep 1367509 = 32051) (by norm_num)
theorem B1826261 : Blo 810345 1826261 := bbase (se 7 (by rfl) ⟨21401, by rfl⟩ : syracuseStep 1826261 = 42803) (by norm_num)
theorem B974305 : Blo 810345 974305 := bbase (se 2 (by rfl) ⟨365364, by rfl⟩ : syracuseStep 974305 = 730729) (by norm_num)
theorem B1826333 : Blo 810345 1826333 := bbase (se 3 (by rfl) ⟨342437, by rfl⟩ : syracuseStep 1826333 = 684875) (by norm_num)
theorem B1367597 : Blo 810345 1367597 := bbase (se 3 (by rfl) ⟨256424, by rfl⟩ : syracuseStep 1367597 = 512849) (by norm_num)
theorem B1236541 : Blo 810345 1236541 := bbase (se 3 (by rfl) ⟨231851, by rfl⟩ : syracuseStep 1236541 = 463703) (by norm_num)
theorem B1826405 : Blo 810345 1826405 := bbase (se 4 (by rfl) ⟨171225, by rfl⟩ : syracuseStep 1826405 = 342451) (by norm_num)
theorem B974497 : Blo 810345 974497 := bbase (se 2 (by rfl) ⟨365436, by rfl⟩ : syracuseStep 974497 = 730873) (by norm_num)
theorem B1367725 : Blo 810345 1367725 := bbase (se 3 (by rfl) ⟨256448, by rfl⟩ : syracuseStep 1367725 = 512897) (by norm_num)
theorem B1826477 : Blo 810345 1826477 := bbase (se 3 (by rfl) ⟨342464, by rfl⟩ : syracuseStep 1826477 = 684929) (by norm_num)
theorem B1302205 : Blo 810345 1302205 := bbase (se 3 (by rfl) ⟨244163, by rfl⟩ : syracuseStep 1302205 = 488327) (by norm_num)
theorem B2055901 : Blo 810345 2055901 := bbase (se 3 (by rfl) ⟨385481, by rfl⟩ : syracuseStep 2055901 = 770963) (by norm_num)
theorem B1826549 : Blo 810345 1826549 := bbase (se 5 (by rfl) ⟨85619, by rfl⟩ : syracuseStep 1826549 = 171239) (by norm_num)
theorem B1367813 : Blo 810345 1367813 := bbase (se 4 (by rfl) ⟨128232, by rfl⟩ : syracuseStep 1367813 = 256465) (by norm_num)
theorem B974597 : Blo 810345 974597 := bbase (se 4 (by rfl) ⟨91368, by rfl⟩ : syracuseStep 974597 = 182737) (by norm_num)
theorem B2744117 : Blo 810345 2744117 := bbase (se 5 (by rfl) ⟨128630, by rfl⟩ : syracuseStep 2744117 = 257261) (by norm_num)
theorem B1826621 : Blo 810345 1826621 := bbase (se 3 (by rfl) ⟨342491, by rfl⟩ : syracuseStep 1826621 = 684983) (by norm_num)
theorem B2056013 : Blo 810345 2056013 := bbase (se 3 (by rfl) ⟨385502, by rfl⟩ : syracuseStep 2056013 = 771005) (by norm_num)
theorem B1367941 : Blo 810345 1367941 := bbase (se 4 (by rfl) ⟨128244, by rfl⟩ : syracuseStep 1367941 = 256489) (by norm_num)
theorem B1826693 : Blo 810345 1826693 := bbase (se 4 (by rfl) ⟨171252, by rfl⟩ : syracuseStep 1826693 = 342505) (by norm_num)
theorem B4120469 : Blo 810345 4120469 := bbase (se 6 (by rfl) ⟨96573, by rfl⟩ : syracuseStep 4120469 = 193147) (by norm_num)
theorem B1826765 : Blo 810345 1826765 := bbase (se 3 (by rfl) ⟨342518, by rfl⟩ : syracuseStep 1826765 = 685037) (by norm_num)
theorem B1368029 : Blo 810345 1368029 := bbase (se 3 (by rfl) ⟨256505, by rfl⟩ : syracuseStep 1368029 = 513011) (by norm_num)
theorem B1466365 : Blo 810345 1466365 := bbase (se 3 (by rfl) ⟨274943, by rfl⟩ : syracuseStep 1466365 = 549887) (by norm_num)
theorem B2056205 : Blo 810345 2056205 := bbase (se 3 (by rfl) ⟨385538, by rfl⟩ : syracuseStep 2056205 = 771077) (by norm_num)
theorem B1826837 : Blo 810345 1826837 := bbase (se 6 (by rfl) ⟨42816, by rfl⟩ : syracuseStep 1826837 = 85633) (by norm_num)
theorem B2318357 : Blo 810345 2318357 := bbase (se 6 (by rfl) ⟨54336, by rfl⟩ : syracuseStep 2318357 = 108673) (by norm_num)
theorem B1368157 : Blo 810345 1368157 := bbase (se 3 (by rfl) ⟨256529, by rfl⟩ : syracuseStep 1368157 = 513059) (by norm_num)
theorem B1826909 : Blo 810345 1826909 := bbase (se 3 (by rfl) ⟨342545, by rfl⟩ : syracuseStep 1826909 = 685091) (by norm_num)
theorem B1466509 : Blo 810345 1466509 := bbase (se 3 (by rfl) ⟨274970, by rfl⟩ : syracuseStep 1466509 = 549941) (by norm_num)
theorem B1826981 : Blo 810345 1826981 := bbase (se 4 (by rfl) ⟨171279, by rfl⟩ : syracuseStep 1826981 = 342559) (by norm_num)
theorem B1368245 : Blo 810345 1368245 := bbase (se 5 (by rfl) ⟨64136, by rfl⟩ : syracuseStep 1368245 = 128273) (by norm_num)
theorem B2744549 : Blo 810345 2744549 := bbase (se 4 (by rfl) ⟨257301, by rfl⟩ : syracuseStep 2744549 = 514603) (by norm_num)
theorem B1827053 : Blo 810345 1827053 := bbase (se 3 (by rfl) ⟨342572, by rfl⟩ : syracuseStep 1827053 = 685145) (by norm_num)
theorem B1466669 : Blo 810345 1466669 := bbase (se 3 (by rfl) ⟨275000, by rfl⟩ : syracuseStep 1466669 = 550001) (by norm_num)
theorem B1368373 : Blo 810345 1368373 := bbase (se 5 (by rfl) ⟨64142, by rfl⟩ : syracuseStep 1368373 = 128285) (by norm_num)
theorem B1827125 : Blo 810345 1827125 := bbase (se 5 (by rfl) ⟨85646, by rfl⟩ : syracuseStep 1827125 = 171293) (by norm_num)
theorem B1040725 : Blo 810345 1040725 := bbase (se 10 (by rfl) ⟨1524, by rfl⟩ : syracuseStep 1040725 = 3049) (by norm_num)
theorem B2056549 : Blo 810345 2056549 := bbase (se 4 (by rfl) ⟨192801, by rfl⟩ : syracuseStep 2056549 = 385603) (by norm_num)
theorem B1466741 : Blo 810345 1466741 := bbase (se 5 (by rfl) ⟨68753, by rfl⟩ : syracuseStep 1466741 = 137507) (by norm_num)
theorem B1827197 : Blo 810345 1827197 := bbase (se 3 (by rfl) ⟨342599, by rfl⟩ : syracuseStep 1827197 = 685199) (by norm_num)
theorem B1368461 : Blo 810345 1368461 := bbase (se 3 (by rfl) ⟨256586, by rfl⟩ : syracuseStep 1368461 = 513173) (by norm_num)
theorem B1827269 : Blo 810345 1827269 := bbase (se 4 (by rfl) ⟨171306, by rfl⟩ : syracuseStep 1827269 = 342613) (by norm_num)
theorem B2056661 : Blo 810345 2056661 := bbase (se 7 (by rfl) ⟨24101, by rfl⟩ : syracuseStep 2056661 = 48203) (by norm_num)
theorem B1368589 : Blo 810345 1368589 := bbase (se 3 (by rfl) ⟨256610, by rfl⟩ : syracuseStep 1368589 = 513221) (by norm_num)
theorem B1827341 : Blo 810345 1827341 := bbase (se 3 (by rfl) ⟨342626, by rfl⟩ : syracuseStep 1827341 = 685253) (by norm_num)
theorem B975385 : Blo 810345 975385 := bbase (se 2 (by rfl) ⟨365769, by rfl⟩ : syracuseStep 975385 = 731539) (by norm_num)
theorem B1827413 : Blo 810345 1827413 := bbase (se 8 (by rfl) ⟨10707, by rfl⟩ : syracuseStep 1827413 = 21415) (by norm_num)
theorem B1368677 : Blo 810345 1368677 := bbase (se 4 (by rfl) ⟨128313, by rfl⟩ : syracuseStep 1368677 = 256627) (by norm_num)
theorem B1303141 : Blo 810345 1303141 := bbase (se 4 (by rfl) ⟨122169, by rfl⟩ : syracuseStep 1303141 = 244339) (by norm_num)
theorem B2056853 : Blo 810345 2056853 := bbase (se 6 (by rfl) ⟨48207, by rfl⟩ : syracuseStep 2056853 = 96415) (by norm_num)
theorem B2744981 : Blo 810345 2744981 := bbase (se 6 (by rfl) ⟨64335, by rfl⟩ : syracuseStep 2744981 = 128671) (by norm_num)
theorem B1827485 : Blo 810345 1827485 := bbase (se 3 (by rfl) ⟨342653, by rfl⟩ : syracuseStep 1827485 = 685307) (by norm_num)
theorem B1368805 : Blo 810345 1368805 := bbase (se 4 (by rfl) ⟨128325, by rfl⟩ : syracuseStep 1368805 = 256651) (by norm_num)
theorem B1827557 : Blo 810345 1827557 := bbase (se 4 (by rfl) ⟨171333, by rfl⟩ : syracuseStep 1827557 = 342667) (by norm_num)
theorem B1827629 : Blo 810345 1827629 := bbase (se 3 (by rfl) ⟨342680, by rfl⟩ : syracuseStep 1827629 = 685361) (by norm_num)
theorem B1368893 : Blo 810345 1368893 := bbase (se 3 (by rfl) ⟨256667, by rfl⟩ : syracuseStep 1368893 = 513335) (by norm_num)
theorem B877429 : Blo 810345 877429 := bbase (se 5 (by rfl) ⟨41129, by rfl⟩ : syracuseStep 877429 = 82259) (by norm_num)
theorem B1827701 : Blo 810345 1827701 := bbase (se 5 (by rfl) ⟨85673, by rfl⟩ : syracuseStep 1827701 = 171347) (by norm_num)
theorem B1369021 : Blo 810345 1369021 := bbase (se 3 (by rfl) ⟨256691, by rfl⟩ : syracuseStep 1369021 = 513383) (by norm_num)
theorem B1827773 : Blo 810345 1827773 := bbase (se 3 (by rfl) ⟨342707, by rfl⟩ : syracuseStep 1827773 = 685415) (by norm_num)
theorem B2057197 : Blo 810345 2057197 := bbase (se 3 (by rfl) ⟨385724, by rfl⟩ : syracuseStep 2057197 = 771449) (by norm_num)
theorem B1827845 : Blo 810345 1827845 := bbase (se 4 (by rfl) ⟨171360, by rfl⟩ : syracuseStep 1827845 = 342721) (by norm_num)
theorem B1369109 : Blo 810345 1369109 := bbase (se 6 (by rfl) ⟨32088, by rfl⟩ : syracuseStep 1369109 = 64177) (by norm_num)
theorem B2745413 : Blo 810345 2745413 := bbase (se 4 (by rfl) ⟨257382, by rfl⟩ : syracuseStep 2745413 = 514765) (by norm_num)
theorem B1827917 : Blo 810345 1827917 := bbase (se 3 (by rfl) ⟨342734, by rfl⟩ : syracuseStep 1827917 = 685469) (by norm_num)
theorem B2057309 : Blo 810345 2057309 := bbase (se 3 (by rfl) ⟨385745, by rfl⟩ : syracuseStep 2057309 = 771491) (by norm_num)
theorem B1369237 : Blo 810345 1369237 := bbase (se 6 (by rfl) ⟨32091, by rfl⟩ : syracuseStep 1369237 = 64183) (by norm_num)
theorem B1827989 : Blo 810345 1827989 := bbase (se 6 (by rfl) ⟨42843, by rfl⟩ : syracuseStep 1827989 = 85687) (by norm_num)
theorem B4121765 : Blo 810345 4121765 := bbase (se 4 (by rfl) ⟨386415, by rfl⟩ : syracuseStep 4121765 = 772831) (by norm_num)
theorem B15623381 : Blo 810345 15623381 := bbase (se 7 (by rfl) ⟨183086, by rfl⟩ : syracuseStep 15623381 = 366173) (by norm_num)
theorem B1828061 : Blo 810345 1828061 := bbase (se 3 (by rfl) ⟨342761, by rfl⟩ : syracuseStep 1828061 = 685523) (by norm_num)
theorem B976097 : Blo 810345 976097 := bbase (se 2 (by rfl) ⟨366036, by rfl⟩ : syracuseStep 976097 = 732073) (by norm_num)
theorem B1369325 : Blo 810345 1369325 := bbase (se 3 (by rfl) ⟨256748, by rfl⟩ : syracuseStep 1369325 = 513497) (by norm_num)
theorem B2057501 : Blo 810345 2057501 := bbase (se 3 (by rfl) ⟨385781, by rfl⟩ : syracuseStep 2057501 = 771563) (by norm_num)
theorem B1828133 : Blo 810345 1828133 := bbase (se 4 (by rfl) ⟨171387, by rfl⟩ : syracuseStep 1828133 = 342775) (by norm_num)
theorem B877921 : Blo 810345 877921 := bbase (se 2 (by rfl) ⟨329220, by rfl⟩ : syracuseStep 877921 = 658441) (by norm_num)
theorem B1369453 : Blo 810345 1369453 := bbase (se 3 (by rfl) ⟨256772, by rfl⟩ : syracuseStep 1369453 = 513545) (by norm_num)
theorem B1828205 : Blo 810345 1828205 := bbase (se 3 (by rfl) ⟨342788, by rfl⟩ : syracuseStep 1828205 = 685577) (by norm_num)
theorem B1828277 : Blo 810345 1828277 := bbase (se 5 (by rfl) ⟨85700, by rfl⟩ : syracuseStep 1828277 = 171401) (by norm_num)
theorem B1369541 : Blo 810345 1369541 := bbase (se 4 (by rfl) ⟨128394, by rfl⟩ : syracuseStep 1369541 = 256789) (by norm_num)
theorem B2745845 : Blo 810345 2745845 := bbase (se 5 (by rfl) ⟨128711, by rfl⟩ : syracuseStep 2745845 = 257423) (by norm_num)
theorem B1828349 : Blo 810345 1828349 := bbase (se 3 (by rfl) ⟨342815, by rfl⟩ : syracuseStep 1828349 = 685631) (by norm_num)
theorem B976433 : Blo 810345 976433 := bbase (se 2 (by rfl) ⟨366162, by rfl⟩ : syracuseStep 976433 = 732325) (by norm_num)
theorem B1369669 : Blo 810345 1369669 := bbase (se 4 (by rfl) ⟨128406, by rfl⟩ : syracuseStep 1369669 = 256813) (by norm_num)
theorem B1828421 : Blo 810345 1828421 := bbase (se 4 (by rfl) ⟨171414, by rfl⟩ : syracuseStep 1828421 = 342829) (by norm_num)
theorem B5203541 : Blo 810345 5203541 := bbase (se 8 (by rfl) ⟨30489, by rfl⟩ : syracuseStep 5203541 = 60979) (by norm_num)
theorem B2057845 : Blo 810345 2057845 := bbase (se 5 (by rfl) ⟨96461, by rfl⟩ : syracuseStep 2057845 = 192923) (by norm_num)
theorem B1828493 : Blo 810345 1828493 := bbase (se 3 (by rfl) ⟨342842, by rfl⟩ : syracuseStep 1828493 = 685685) (by norm_num)
theorem B1369757 : Blo 810345 1369757 := bbase (se 3 (by rfl) ⟨256829, by rfl⟩ : syracuseStep 1369757 = 513659) (by norm_num)
theorem B976549 : Blo 810345 976549 := bbase (se 4 (by rfl) ⟨91551, by rfl⟩ : syracuseStep 976549 = 183103) (by norm_num)
theorem B976573 : Blo 810345 976573 := bbase (se 3 (by rfl) ⟨183107, by rfl⟩ : syracuseStep 976573 = 366215) (by norm_num)
theorem B1828565 : Blo 810345 1828565 := bbase (se 7 (by rfl) ⟨21428, by rfl⟩ : syracuseStep 1828565 = 42857) (by norm_num)
theorem B2057957 : Blo 810345 2057957 := bbase (se 4 (by rfl) ⟨192933, by rfl⟩ : syracuseStep 2057957 = 385867) (by norm_num)
theorem B1304333 : Blo 810345 1304333 := bbase (se 3 (by rfl) ⟨244562, by rfl⟩ : syracuseStep 1304333 = 489125) (by norm_num)
theorem B1369885 : Blo 810345 1369885 := bbase (se 3 (by rfl) ⟨256853, by rfl⟩ : syracuseStep 1369885 = 513707) (by norm_num)
theorem B1828637 : Blo 810345 1828637 := bbase (se 3 (by rfl) ⟨342869, by rfl⟩ : syracuseStep 1828637 = 685739) (by norm_num)
theorem B1042213 : Blo 810345 1042213 := bbase (se 4 (by rfl) ⟨97707, by rfl⟩ : syracuseStep 1042213 = 195415) (by norm_num)
theorem B1828709 : Blo 810345 1828709 := bbase (se 4 (by rfl) ⟨171441, by rfl⟩ : syracuseStep 1828709 = 342883) (by norm_num)
theorem B1369973 : Blo 810345 1369973 := bbase (se 5 (by rfl) ⟨64217, by rfl⟩ : syracuseStep 1369973 = 128435) (by norm_num)
theorem B2058149 : Blo 810345 2058149 := bbase (se 4 (by rfl) ⟨192951, by rfl⟩ : syracuseStep 2058149 = 385903) (by norm_num)
theorem B2746277 : Blo 810345 2746277 := bbase (se 4 (by rfl) ⟨257463, by rfl⟩ : syracuseStep 2746277 = 514927) (by norm_num)
theorem B1566629 : Blo 810345 1566629 := bbase (se 4 (by rfl) ⟨146871, by rfl⟩ : syracuseStep 1566629 = 293743) (by norm_num)
theorem B1828781 : Blo 810345 1828781 := bbase (se 3 (by rfl) ⟨342896, by rfl⟩ : syracuseStep 1828781 = 685793) (by norm_num)
theorem B1370101 : Blo 810345 1370101 := bbase (se 5 (by rfl) ⟨64223, by rfl⟩ : syracuseStep 1370101 = 128447) (by norm_num)
theorem B1828853 : Blo 810345 1828853 := bbase (se 5 (by rfl) ⟨85727, by rfl⟩ : syracuseStep 1828853 = 171455) (by norm_num)
theorem B3467285 : Blo 810345 3467285 := bbase (se 6 (by rfl) ⟨81264, by rfl⟩ : syracuseStep 3467285 = 162529) (by norm_num)
theorem B1828925 : Blo 810345 1828925 := bbase (se 3 (by rfl) ⟨342923, by rfl⟩ : syracuseStep 1828925 = 685847) (by norm_num)
theorem B1370189 : Blo 810345 1370189 := bbase (se 3 (by rfl) ⟨256910, by rfl⟩ : syracuseStep 1370189 = 513821) (by norm_num)
theorem B1828997 : Blo 810345 1828997 := bbase (se 4 (by rfl) ⟨171468, by rfl⟩ : syracuseStep 1828997 = 342937) (by norm_num)
theorem B1370317 : Blo 810345 1370317 := bbase (se 3 (by rfl) ⟨256934, by rfl⟩ : syracuseStep 1370317 = 513869) (by norm_num)
theorem B1829069 : Blo 810345 1829069 := bbase (se 3 (by rfl) ⟨342950, by rfl⟩ : syracuseStep 1829069 = 685901) (by norm_num)
theorem B878801 : Blo 810345 878801 := bbase (se 2 (by rfl) ⟨329550, by rfl⟩ : syracuseStep 878801 = 659101) (by norm_num)
theorem B26699989 : Blo 810345 26699989 := bbase (se 7 (by rfl) ⟨312890, by rfl⟩ : syracuseStep 26699989 = 625781) (by norm_num)
theorem B2058493 : Blo 810345 2058493 := bbase (se 3 (by rfl) ⟨385967, by rfl⟩ : syracuseStep 2058493 = 771935) (by norm_num)
theorem B1829141 : Blo 810345 1829141 := bbase (se 6 (by rfl) ⟨42870, by rfl⟩ : syracuseStep 1829141 = 85741) (by norm_num)
theorem B911641 : Blo 810345 911641 := bbase (se 2 (by rfl) ⟨341865, by rfl⟩ : syracuseStep 911641 = 683731) (by norm_num)
theorem B1370405 : Blo 810345 1370405 := bbase (se 4 (by rfl) ⟨128475, by rfl⟩ : syracuseStep 1370405 = 256951) (by norm_num)
theorem B911677 : Blo 810345 911677 := bbase (se 3 (by rfl) ⟨170939, by rfl⟩ : syracuseStep 911677 = 341879) (by norm_num)
theorem B2746709 : Blo 810345 2746709 := bbase (se 10 (by rfl) ⟨4023, by rfl⟩ : syracuseStep 2746709 = 8047) (by norm_num)
theorem B1730909 : Blo 810345 1730909 := bbase (se 3 (by rfl) ⟨324545, by rfl⟩ : syracuseStep 1730909 = 649091) (by norm_num)
theorem B1829213 : Blo 810345 1829213 := bbase (se 3 (by rfl) ⟨342977, by rfl⟩ : syracuseStep 1829213 = 685955) (by norm_num)
theorem B911713 : Blo 810345 911713 := bbase (se 2 (by rfl) ⟨341892, by rfl⟩ : syracuseStep 911713 = 683785) (by norm_num)
theorem B2058605 : Blo 810345 2058605 := bbase (se 3 (by rfl) ⟨385988, by rfl⟩ : syracuseStep 2058605 = 771977) (by norm_num)
theorem B977269 : Blo 810345 977269 := bbase (se 5 (by rfl) ⟨45809, by rfl⟩ : syracuseStep 977269 = 91619) (by norm_num)
theorem B911749 : Blo 810345 911749 := bbase (se 4 (by rfl) ⟨85476, by rfl⟩ : syracuseStep 911749 = 170953) (by norm_num)
theorem B1370533 : Blo 810345 1370533 := bbase (se 4 (by rfl) ⟨128487, by rfl⟩ : syracuseStep 1370533 = 256975) (by norm_num)
theorem B1829285 : Blo 810345 1829285 := bbase (se 4 (by rfl) ⟨171495, by rfl⟩ : syracuseStep 1829285 = 342991) (by norm_num)
theorem B911785 : Blo 810345 911785 := bbase (se 2 (by rfl) ⟨341919, by rfl⟩ : syracuseStep 911785 = 683839) (by norm_num)
theorem B911821 : Blo 810345 911821 := bbase (se 3 (by rfl) ⟨170966, by rfl⟩ : syracuseStep 911821 = 341933) (by norm_num)
theorem B977365 : Blo 810345 977365 := bbase (se 7 (by rfl) ⟨11453, by rfl⟩ : syracuseStep 977365 = 22907) (by norm_num)
theorem B1829357 : Blo 810345 1829357 := bbase (se 3 (by rfl) ⟨343004, by rfl⟩ : syracuseStep 1829357 = 686009) (by norm_num)
theorem B911857 : Blo 810345 911857 := bbase (se 2 (by rfl) ⟨341946, by rfl⟩ : syracuseStep 911857 = 683893) (by norm_num)
theorem B1370621 : Blo 810345 1370621 := bbase (se 3 (by rfl) ⟨256991, by rfl⟩ : syracuseStep 1370621 = 513983) (by norm_num)
theorem B911893 : Blo 810345 911893 := bbase (se 6 (by rfl) ⟨21372, by rfl⟩ : syracuseStep 911893 = 42745) (by norm_num)
theorem B2058797 : Blo 810345 2058797 := bbase (se 3 (by rfl) ⟨386024, by rfl⟩ : syracuseStep 2058797 = 772049) (by norm_num)
theorem B1829429 : Blo 810345 1829429 := bbase (se 5 (by rfl) ⟨85754, by rfl⟩ : syracuseStep 1829429 = 171509) (by norm_num)
theorem B911929 : Blo 810345 911929 := bbase (se 2 (by rfl) ⟨341973, by rfl⟩ : syracuseStep 911929 = 683947) (by norm_num)
theorem B911965 : Blo 810345 911965 := bbase (se 3 (by rfl) ⟨170993, by rfl⟩ : syracuseStep 911965 = 341987) (by norm_num)
theorem B1370749 : Blo 810345 1370749 := bbase (se 3 (by rfl) ⟨257015, by rfl⟩ : syracuseStep 1370749 = 514031) (by norm_num)
theorem B1829501 : Blo 810345 1829501 := bbase (se 3 (by rfl) ⟨343031, by rfl⟩ : syracuseStep 1829501 = 686063) (by norm_num)
theorem B912001 : Blo 810345 912001 := bbase (se 2 (by rfl) ⟨342000, by rfl⟩ : syracuseStep 912001 = 684001) (by norm_num)
theorem B912037 : Blo 810345 912037 := bbase (se 4 (by rfl) ⟨85503, by rfl⟩ : syracuseStep 912037 = 171007) (by norm_num)
theorem B1829573 : Blo 810345 1829573 := bbase (se 4 (by rfl) ⟨171522, by rfl⟩ : syracuseStep 1829573 = 343045) (by norm_num)
theorem B912073 : Blo 810345 912073 := bbase (se 2 (by rfl) ⟨342027, by rfl⟩ : syracuseStep 912073 = 684055) (by norm_num)
theorem B1370837 : Blo 810345 1370837 := bbase (se 7 (by rfl) ⟨16064, by rfl⟩ : syracuseStep 1370837 = 32129) (by norm_num)
theorem B912109 : Blo 810345 912109 := bbase (se 3 (by rfl) ⟨171020, by rfl⟩ : syracuseStep 912109 = 342041) (by norm_num)
theorem B2747141 : Blo 810345 2747141 := bbase (se 4 (by rfl) ⟨257544, by rfl⟩ : syracuseStep 2747141 = 515089) (by norm_num)
theorem B1829645 : Blo 810345 1829645 := bbase (se 3 (by rfl) ⟨343058, by rfl⟩ : syracuseStep 1829645 = 686117) (by norm_num)
theorem B912145 : Blo 810345 912145 := bbase (se 2 (by rfl) ⟨342054, by rfl⟩ : syracuseStep 912145 = 684109) (by norm_num)
theorem B912181 : Blo 810345 912181 := bbase (se 5 (by rfl) ⟨42758, by rfl⟩ : syracuseStep 912181 = 85517) (by norm_num)
theorem B1174349 : Blo 810345 1174349 := bbase (se 3 (by rfl) ⟨220190, by rfl⟩ : syracuseStep 1174349 = 440381) (by norm_num)
theorem B1370965 : Blo 810345 1370965 := bbase (se 9 (by rfl) ⟨4016, by rfl⟩ : syracuseStep 1370965 = 8033) (by norm_num)
theorem B1829717 : Blo 810345 1829717 := bbase (se 9 (by rfl) ⟨5360, by rfl⟩ : syracuseStep 1829717 = 10721) (by norm_num)
theorem B912217 : Blo 810345 912217 := bbase (se 2 (by rfl) ⟨342081, by rfl⟩ : syracuseStep 912217 = 684163) (by norm_num)
theorem B912253 : Blo 810345 912253 := bbase (se 3 (by rfl) ⟨171047, by rfl⟩ : syracuseStep 912253 = 342095) (by norm_num)
theorem B2059141 : Blo 810345 2059141 := bbase (se 4 (by rfl) ⟨193044, by rfl⟩ : syracuseStep 2059141 = 386089) (by norm_num)
theorem B1829789 : Blo 810345 1829789 := bbase (se 3 (by rfl) ⟨343085, by rfl⟩ : syracuseStep 1829789 = 686171) (by norm_num)
theorem B912289 : Blo 810345 912289 := bbase (se 2 (by rfl) ⟨342108, by rfl⟩ : syracuseStep 912289 = 684217) (by norm_num)
theorem B1371053 : Blo 810345 1371053 := bbase (se 3 (by rfl) ⟨257072, by rfl⟩ : syracuseStep 1371053 = 514145) (by norm_num)
theorem B6155189 : Blo 810345 6155189 := bbase (se 5 (by rfl) ⟨288524, by rfl⟩ : syracuseStep 6155189 = 577049) (by norm_num)
theorem B1043389 : Blo 810345 1043389 := bbase (se 3 (by rfl) ⟨195635, by rfl⟩ : syracuseStep 1043389 = 391271) (by norm_num)
theorem B912325 : Blo 810345 912325 := bbase (se 4 (by rfl) ⟨85530, by rfl⟩ : syracuseStep 912325 = 171061) (by norm_num)
theorem B3959765 : Blo 810345 3959765 := bbase (se 7 (by rfl) ⟨46403, by rfl⟩ : syracuseStep 3959765 = 92807) (by norm_num)
theorem B1829861 : Blo 810345 1829861 := bbase (se 4 (by rfl) ⟨171549, by rfl⟩ : syracuseStep 1829861 = 343099) (by norm_num)
theorem B912361 : Blo 810345 912361 := bbase (se 2 (by rfl) ⟨342135, by rfl⟩ : syracuseStep 912361 = 684271) (by norm_num)
theorem B2059253 : Blo 810345 2059253 := bbase (se 5 (by rfl) ⟨96527, by rfl⟩ : syracuseStep 2059253 = 193055) (by norm_num)
theorem B912397 : Blo 810345 912397 := bbase (se 3 (by rfl) ⟨171074, by rfl⟩ : syracuseStep 912397 = 342149) (by norm_num)
theorem B7826453 : Blo 810345 7826453 := bbase (se 6 (by rfl) ⟨183432, by rfl⟩ : syracuseStep 7826453 = 366865) (by norm_num)
theorem B1371181 : Blo 810345 1371181 := bbase (se 3 (by rfl) ⟨257096, by rfl⟩ : syracuseStep 1371181 = 514193) (by norm_num)
theorem B1829933 : Blo 810345 1829933 := bbase (se 3 (by rfl) ⟨343112, by rfl⟩ : syracuseStep 1829933 = 686225) (by norm_num)
theorem B912433 : Blo 810345 912433 := bbase (se 2 (by rfl) ⟨342162, by rfl⟩ : syracuseStep 912433 = 684325) (by norm_num)
theorem B912469 : Blo 810345 912469 := bbase (se 8 (by rfl) ⟨5346, by rfl⟩ : syracuseStep 912469 = 10693) (by norm_num)
theorem B1830005 : Blo 810345 1830005 := bbase (se 5 (by rfl) ⟨85781, by rfl⟩ : syracuseStep 1830005 = 171563) (by norm_num)
theorem B912505 : Blo 810345 912505 := bbase (se 2 (by rfl) ⟨342189, by rfl⟩ : syracuseStep 912505 = 684379) (by norm_num)
theorem B1371269 : Blo 810345 1371269 := bbase (se 4 (by rfl) ⟨128556, by rfl⟩ : syracuseStep 1371269 = 257113) (by norm_num)
theorem B912541 : Blo 810345 912541 := bbase (se 3 (by rfl) ⟨171101, by rfl⟩ : syracuseStep 912541 = 342203) (by norm_num)
theorem B2059445 : Blo 810345 2059445 := bbase (se 5 (by rfl) ⟨96536, by rfl⟩ : syracuseStep 2059445 = 193073) (by norm_num)
theorem B2747573 : Blo 810345 2747573 := bbase (se 5 (by rfl) ⟨128792, by rfl⟩ : syracuseStep 2747573 = 257585) (by norm_num)
theorem B1830077 : Blo 810345 1830077 := bbase (se 3 (by rfl) ⟨343139, by rfl⟩ : syracuseStep 1830077 = 686279) (by norm_num)
theorem B912577 : Blo 810345 912577 := bbase (se 2 (by rfl) ⟨342216, by rfl⟩ : syracuseStep 912577 = 684433) (by norm_num)
theorem B1731797 : Blo 810345 1731797 := bbase (se 7 (by rfl) ⟨20294, by rfl⟩ : syracuseStep 1731797 = 40589) (by norm_num)
theorem B912613 : Blo 810345 912613 := bbase (se 4 (by rfl) ⟨85557, by rfl⟩ : syracuseStep 912613 = 171115) (by norm_num)
theorem B1371397 : Blo 810345 1371397 := bbase (se 4 (by rfl) ⟨128568, by rfl⟩ : syracuseStep 1371397 = 257137) (by norm_num)
theorem B1830149 : Blo 810345 1830149 := bbase (se 4 (by rfl) ⟨171576, by rfl⟩ : syracuseStep 1830149 = 343153) (by norm_num)
theorem B912649 : Blo 810345 912649 := bbase (se 2 (by rfl) ⟨342243, by rfl⟩ : syracuseStep 912649 = 684487) (by norm_num)
theorem B912685 : Blo 810345 912685 := bbase (se 3 (by rfl) ⟨171128, by rfl⟩ : syracuseStep 912685 = 342257) (by norm_num)
theorem B1731917 : Blo 810345 1731917 := bbase (se 3 (by rfl) ⟨324734, by rfl⟩ : syracuseStep 1731917 = 649469) (by norm_num)
theorem B1830221 : Blo 810345 1830221 := bbase (se 3 (by rfl) ⟨343166, by rfl⟩ : syracuseStep 1830221 = 686333) (by norm_num)
theorem B912721 : Blo 810345 912721 := bbase (se 2 (by rfl) ⟨342270, by rfl⟩ : syracuseStep 912721 = 684541) (by norm_num)
theorem B2223445 : Blo 810345 2223445 := bbase (se 11 (by rfl) ⟨1628, by rfl⟩ : syracuseStep 2223445 = 3257) (by norm_num)
theorem B1371485 : Blo 810345 1371485 := bbase (se 3 (by rfl) ⟨257153, by rfl⟩ : syracuseStep 1371485 = 514307) (by norm_num)
theorem B912757 : Blo 810345 912757 := bbase (se 5 (by rfl) ⟨42785, by rfl⟩ : syracuseStep 912757 = 85571) (by norm_num)
theorem B1830293 : Blo 810345 1830293 := bbase (se 6 (by rfl) ⟨42897, by rfl⟩ : syracuseStep 1830293 = 85795) (by norm_num)
theorem B7925141 : Blo 810345 7925141 := bbase (se 6 (by rfl) ⟨185745, by rfl⟩ : syracuseStep 7925141 = 371491) (by norm_num)
theorem B912793 : Blo 810345 912793 := bbase (se 2 (by rfl) ⟨342297, by rfl⟩ : syracuseStep 912793 = 684595) (by norm_num)
theorem B1043885 : Blo 810345 1043885 := bbase (se 3 (by rfl) ⟨195728, by rfl⟩ : syracuseStep 1043885 = 391457) (by norm_num)
theorem B912829 : Blo 810345 912829 := bbase (se 3 (by rfl) ⟨171155, by rfl⟩ : syracuseStep 912829 = 342311) (by norm_num)
theorem B1371613 : Blo 810345 1371613 := bbase (se 3 (by rfl) ⟨257177, by rfl⟩ : syracuseStep 1371613 = 514355) (by norm_num)
theorem B1830365 : Blo 810345 1830365 := bbase (se 3 (by rfl) ⟨343193, by rfl⟩ : syracuseStep 1830365 = 686387) (by norm_num)
theorem B912865 : Blo 810345 912865 := bbase (se 2 (by rfl) ⟨342324, by rfl⟩ : syracuseStep 912865 = 684649) (by norm_num)
theorem B3698149 : Blo 810345 3698149 := bbase (se 4 (by rfl) ⟨346701, by rfl⟩ : syracuseStep 3698149 = 693403) (by norm_num)
theorem B912901 : Blo 810345 912901 := bbase (se 4 (by rfl) ⟨85584, by rfl⟩ : syracuseStep 912901 = 171169) (by norm_num)
theorem B2059789 : Blo 810345 2059789 := bbase (se 3 (by rfl) ⟨386210, by rfl⟩ : syracuseStep 2059789 = 772421) (by norm_num)
theorem B1830437 : Blo 810345 1830437 := bbase (se 4 (by rfl) ⟨171603, by rfl⟩ : syracuseStep 1830437 = 343207) (by norm_num)
theorem B912937 : Blo 810345 912937 := bbase (se 2 (by rfl) ⟨342351, by rfl⟩ : syracuseStep 912937 = 684703) (by norm_num)
theorem B1371701 : Blo 810345 1371701 := bbase (se 5 (by rfl) ⟨64298, by rfl⟩ : syracuseStep 1371701 = 128597) (by norm_num)
theorem B912973 : Blo 810345 912973 := bbase (se 3 (by rfl) ⟨171182, by rfl⟩ : syracuseStep 912973 = 342365) (by norm_num)
theorem B2748005 : Blo 810345 2748005 := bbase (se 4 (by rfl) ⟨257625, by rfl⟩ : syracuseStep 2748005 = 515251) (by norm_num)
theorem B1830509 : Blo 810345 1830509 := bbase (se 3 (by rfl) ⟨343220, by rfl⟩ : syracuseStep 1830509 = 686441) (by norm_num)
theorem B913009 : Blo 810345 913009 := bbase (se 2 (by rfl) ⟨342378, by rfl⟩ : syracuseStep 913009 = 684757) (by norm_num)
theorem B2059901 : Blo 810345 2059901 := bbase (se 3 (by rfl) ⟨386231, by rfl⟩ : syracuseStep 2059901 = 772463) (by norm_num)
theorem B913045 : Blo 810345 913045 := bbase (se 6 (by rfl) ⟨21399, by rfl⟩ : syracuseStep 913045 = 42799) (by norm_num)
theorem B1371829 : Blo 810345 1371829 := bbase (se 5 (by rfl) ⟨64304, by rfl⟩ : syracuseStep 1371829 = 128609) (by norm_num)
theorem B1830581 : Blo 810345 1830581 := bbase (se 5 (by rfl) ⟨85808, by rfl⟩ : syracuseStep 1830581 = 171617) (by norm_num)
theorem B913081 : Blo 810345 913081 := bbase (se 2 (by rfl) ⟨342405, by rfl⟩ : syracuseStep 913081 = 684811) (by norm_num)
theorem B913117 : Blo 810345 913117 := bbase (se 3 (by rfl) ⟨171209, by rfl⟩ : syracuseStep 913117 = 342419) (by norm_num)
theorem B6582005 : Blo 810345 6582005 := bbase (se 5 (by rfl) ⟨308531, by rfl⟩ : syracuseStep 6582005 = 617063) (by norm_num)
theorem B1830653 : Blo 810345 1830653 := bbase (se 3 (by rfl) ⟨343247, by rfl⟩ : syracuseStep 1830653 = 686495) (by norm_num)
theorem B913153 : Blo 810345 913153 := bbase (se 2 (by rfl) ⟨342432, by rfl⟩ : syracuseStep 913153 = 684865) (by norm_num)
theorem B3469061 : Blo 810345 3469061 := bbase (se 4 (by rfl) ⟨325224, by rfl⟩ : syracuseStep 3469061 = 650449) (by norm_num)
theorem B1371917 : Blo 810345 1371917 := bbase (se 3 (by rfl) ⟨257234, by rfl⟩ : syracuseStep 1371917 = 514469) (by norm_num)
theorem B913189 : Blo 810345 913189 := bbase (se 4 (by rfl) ⟨85611, by rfl⟩ : syracuseStep 913189 = 171223) (by norm_num)
theorem B2060093 : Blo 810345 2060093 := bbase (se 3 (by rfl) ⟨386267, by rfl⟩ : syracuseStep 2060093 = 772535) (by norm_num)
theorem B1830725 : Blo 810345 1830725 := bbase (se 4 (by rfl) ⟨171630, by rfl⟩ : syracuseStep 1830725 = 343261) (by norm_num)
theorem B913225 : Blo 810345 913225 := bbase (se 2 (by rfl) ⟨342459, by rfl⟩ : syracuseStep 913225 = 684919) (by norm_num)
theorem B913261 : Blo 810345 913261 := bbase (se 3 (by rfl) ⟨171236, by rfl⟩ : syracuseStep 913261 = 342473) (by norm_num)
theorem B1372045 : Blo 810345 1372045 := bbase (se 3 (by rfl) ⟨257258, by rfl⟩ : syracuseStep 1372045 = 514517) (by norm_num)
theorem B1830797 : Blo 810345 1830797 := bbase (se 3 (by rfl) ⟨343274, by rfl⟩ : syracuseStep 1830797 = 686549) (by norm_num)
theorem B913297 : Blo 810345 913297 := bbase (se 2 (by rfl) ⟨342486, by rfl⟩ : syracuseStep 913297 = 684973) (by norm_num)
theorem B9891733 : Blo 810345 9891733 := bbase (se 6 (by rfl) ⟨231837, by rfl⟩ : syracuseStep 9891733 = 463675) (by norm_num)
theorem B1044377 : Blo 810345 1044377 := bbase (se 2 (by rfl) ⟨391641, by rfl⟩ : syracuseStep 1044377 = 783283) (by norm_num)
theorem B913333 : Blo 810345 913333 := bbase (se 5 (by rfl) ⟨42812, by rfl⟩ : syracuseStep 913333 = 85625) (by norm_num)
theorem B1732549 : Blo 810345 1732549 := bbase (se 4 (by rfl) ⟨162426, by rfl⟩ : syracuseStep 1732549 = 324853) (by norm_num)
theorem B1830869 : Blo 810345 1830869 := bbase (se 7 (by rfl) ⟨21455, by rfl⟩ : syracuseStep 1830869 = 42911) (by norm_num)
theorem B913369 : Blo 810345 913369 := bbase (se 2 (by rfl) ⟨342513, by rfl⟩ : syracuseStep 913369 = 685027) (by norm_num)
theorem B1372133 : Blo 810345 1372133 := bbase (se 4 (by rfl) ⟨128637, by rfl⟩ : syracuseStep 1372133 = 257275) (by norm_num)
theorem B3469301 : Blo 810345 3469301 := bbase (se 5 (by rfl) ⟨162623, by rfl⟩ : syracuseStep 3469301 = 325247) (by norm_num)
theorem B913405 : Blo 810345 913405 := bbase (se 3 (by rfl) ⟨171263, by rfl⟩ : syracuseStep 913405 = 342527) (by norm_num)
theorem B6582293 : Blo 810345 6582293 := bbase (se 6 (by rfl) ⟨154272, by rfl⟩ : syracuseStep 6582293 = 308545) (by norm_num)
theorem B1830941 : Blo 810345 1830941 := bbase (se 3 (by rfl) ⟨343301, by rfl⟩ : syracuseStep 1830941 = 686603) (by norm_num)
theorem B913441 : Blo 810345 913441 := bbase (se 2 (by rfl) ⟨342540, by rfl⟩ : syracuseStep 913441 = 685081) (by norm_num)
theorem B913477 : Blo 810345 913477 := bbase (se 4 (by rfl) ⟨85638, by rfl⟩ : syracuseStep 913477 = 171277) (by norm_num)
theorem B1372261 : Blo 810345 1372261 := bbase (se 4 (by rfl) ⟨128649, by rfl⟩ : syracuseStep 1372261 = 257299) (by norm_num)
theorem B1831013 : Blo 810345 1831013 := bbase (se 4 (by rfl) ⟨171657, by rfl⟩ : syracuseStep 1831013 = 343315) (by norm_num)
theorem B913513 : Blo 810345 913513 := bbase (se 2 (by rfl) ⟨342567, by rfl⟩ : syracuseStep 913513 = 685135) (by norm_num)
theorem B913549 : Blo 810345 913549 := bbase (se 3 (by rfl) ⟨171290, by rfl⟩ : syracuseStep 913549 = 342581) (by norm_num)
theorem B2060437 : Blo 810345 2060437 := bbase (se 6 (by rfl) ⟨48291, by rfl⟩ : syracuseStep 2060437 = 96583) (by norm_num)
theorem B1831085 : Blo 810345 1831085 := bbase (se 3 (by rfl) ⟨343328, by rfl⟩ : syracuseStep 1831085 = 686657) (by norm_num)
theorem B913585 : Blo 810345 913585 := bbase (se 2 (by rfl) ⟨342594, by rfl⟩ : syracuseStep 913585 = 685189) (by norm_num)
theorem B1372349 : Blo 810345 1372349 := bbase (se 3 (by rfl) ⟨257315, by rfl⟩ : syracuseStep 1372349 = 514631) (by norm_num)
theorem B913621 : Blo 810345 913621 := bbase (se 7 (by rfl) ⟨10706, by rfl⟩ : syracuseStep 913621 = 21413) (by norm_num)
theorem B1831157 : Blo 810345 1831157 := bbase (se 5 (by rfl) ⟨85835, by rfl⟩ : syracuseStep 1831157 = 171671) (by norm_num)
theorem B913657 : Blo 810345 913657 := bbase (se 2 (by rfl) ⟨342621, by rfl⟩ : syracuseStep 913657 = 685243) (by norm_num)
theorem B2060549 : Blo 810345 2060549 := bbase (se 4 (by rfl) ⟨193176, by rfl⟩ : syracuseStep 2060549 = 386353) (by norm_num)
theorem B913693 : Blo 810345 913693 := bbase (se 3 (by rfl) ⟨171317, by rfl⟩ : syracuseStep 913693 = 342635) (by norm_num)
theorem B1372477 : Blo 810345 1372477 := bbase (se 3 (by rfl) ⟨257339, by rfl⟩ : syracuseStep 1372477 = 514679) (by norm_num)
theorem B1831229 : Blo 810345 1831229 := bbase (se 3 (by rfl) ⟨343355, by rfl⟩ : syracuseStep 1831229 = 686711) (by norm_num)
theorem B913729 : Blo 810345 913729 := bbase (se 2 (by rfl) ⟨342648, by rfl⟩ : syracuseStep 913729 = 685297) (by norm_num)
theorem B913765 : Blo 810345 913765 := bbase (se 4 (by rfl) ⟨85665, by rfl⟩ : syracuseStep 913765 = 171331) (by norm_num)
theorem B1831301 : Blo 810345 1831301 := bbase (se 4 (by rfl) ⟨171684, by rfl⟩ : syracuseStep 1831301 = 343369) (by norm_num)
theorem B913801 : Blo 810345 913801 := bbase (se 2 (by rfl) ⟨342675, by rfl⟩ : syracuseStep 913801 = 685351) (by norm_num)
theorem B1372565 : Blo 810345 1372565 := bbase (se 6 (by rfl) ⟨32169, by rfl⟩ : syracuseStep 1372565 = 64339) (by norm_num)
theorem B913837 : Blo 810345 913837 := bbase (se 3 (by rfl) ⟨171344, by rfl⟩ : syracuseStep 913837 = 342689) (by norm_num)
theorem B2060741 : Blo 810345 2060741 := bbase (se 4 (by rfl) ⟨193194, by rfl⟩ : syracuseStep 2060741 = 386389) (by norm_num)
theorem B1831373 : Blo 810345 1831373 := bbase (se 3 (by rfl) ⟨343382, by rfl⟩ : syracuseStep 1831373 = 686765) (by norm_num)
theorem B913873 : Blo 810345 913873 := bbase (se 2 (by rfl) ⟨342702, by rfl⟩ : syracuseStep 913873 = 685405) (by norm_num)
theorem B913909 : Blo 810345 913909 := bbase (se 5 (by rfl) ⟨42839, by rfl⟩ : syracuseStep 913909 = 85679) (by norm_num)
theorem B1372693 : Blo 810345 1372693 := bbase (se 6 (by rfl) ⟨32172, by rfl⟩ : syracuseStep 1372693 = 64345) (by norm_num)
theorem B1831445 : Blo 810345 1831445 := bbase (se 6 (by rfl) ⟨42924, by rfl⟩ : syracuseStep 1831445 = 85849) (by norm_num)
theorem B913945 : Blo 810345 913945 := bbase (se 2 (by rfl) ⟨342729, by rfl⟩ : syracuseStep 913945 = 685459) (by norm_num)
theorem B913981 : Blo 810345 913981 := bbase (se 3 (by rfl) ⟨171371, by rfl⟩ : syracuseStep 913981 = 342743) (by norm_num)
theorem B1831517 : Blo 810345 1831517 := bbase (se 3 (by rfl) ⟨343409, by rfl⟩ : syracuseStep 1831517 = 686819) (by norm_num)
theorem B914017 : Blo 810345 914017 := bbase (se 2 (by rfl) ⟨342756, by rfl⟩ : syracuseStep 914017 = 685513) (by norm_num)
theorem B1372781 : Blo 810345 1372781 := bbase (se 3 (by rfl) ⟨257396, by rfl⟩ : syracuseStep 1372781 = 514793) (by norm_num)
theorem B914053 : Blo 810345 914053 := bbase (se 4 (by rfl) ⟨85692, by rfl⟩ : syracuseStep 914053 = 171385) (by norm_num)
theorem B1831589 : Blo 810345 1831589 := bbase (se 4 (by rfl) ⟨171711, by rfl⟩ : syracuseStep 1831589 = 343423) (by norm_num)
theorem B914089 : Blo 810345 914089 := bbase (se 2 (by rfl) ⟨342783, by rfl⟩ : syracuseStep 914089 = 685567) (by norm_num)
theorem B3076805 : Blo 810345 3076805 := bbase (se 4 (by rfl) ⟨288450, by rfl⟩ : syracuseStep 3076805 = 576901) (by norm_num)
theorem B914125 : Blo 810345 914125 := bbase (se 3 (by rfl) ⟨171398, by rfl⟩ : syracuseStep 914125 = 342797) (by norm_num)
theorem B1372909 : Blo 810345 1372909 := bbase (se 3 (by rfl) ⟨257420, by rfl⟩ : syracuseStep 1372909 = 514841) (by norm_num)
theorem B1831661 : Blo 810345 1831661 := bbase (se 3 (by rfl) ⟨343436, by rfl⟩ : syracuseStep 1831661 = 686873) (by norm_num)
theorem B914161 : Blo 810345 914161 := bbase (se 2 (by rfl) ⟨342810, by rfl⟩ : syracuseStep 914161 = 685621) (by norm_num)
theorem B914197 : Blo 810345 914197 := bbase (se 6 (by rfl) ⟨21426, by rfl⟩ : syracuseStep 914197 = 42853) (by norm_num)
theorem B2061085 : Blo 810345 2061085 := bbase (se 3 (by rfl) ⟨386453, by rfl⟩ : syracuseStep 2061085 = 772907) (by norm_num)
theorem B1831733 : Blo 810345 1831733 := bbase (se 5 (by rfl) ⟨85862, by rfl⟩ : syracuseStep 1831733 = 171725) (by norm_num)
theorem B914233 : Blo 810345 914233 := bbase (se 2 (by rfl) ⟨342837, by rfl⟩ : syracuseStep 914233 = 685675) (by norm_num)
theorem B1733437 : Blo 810345 1733437 := bbase (se 3 (by rfl) ⟨325019, by rfl⟩ : syracuseStep 1733437 = 650039) (by norm_num)
theorem B1372997 : Blo 810345 1372997 := bbase (se 4 (by rfl) ⟨128718, by rfl⟩ : syracuseStep 1372997 = 257437) (by norm_num)
theorem B914269 : Blo 810345 914269 := bbase (se 3 (by rfl) ⟨171425, by rfl⟩ : syracuseStep 914269 = 342851) (by norm_num)
theorem B1831805 : Blo 810345 1831805 := bbase (se 3 (by rfl) ⟨343463, by rfl⟩ : syracuseStep 1831805 = 686927) (by norm_num)
theorem B914305 : Blo 810345 914305 := bbase (se 2 (by rfl) ⟨342864, by rfl⟩ : syracuseStep 914305 = 685729) (by norm_num)
theorem B2061197 : Blo 810345 2061197 := bbase (se 3 (by rfl) ⟨386474, by rfl⟩ : syracuseStep 2061197 = 772949) (by norm_num)
theorem B914341 : Blo 810345 914341 := bbase (se 4 (by rfl) ⟨85719, by rfl⟩ : syracuseStep 914341 = 171439) (by norm_num)
theorem B1733557 : Blo 810345 1733557 := bbase (se 5 (by rfl) ⟨81260, by rfl⟩ : syracuseStep 1733557 = 162521) (by norm_num)
theorem B1373125 : Blo 810345 1373125 := bbase (se 4 (by rfl) ⟨128730, by rfl⟩ : syracuseStep 1373125 = 257461) (by norm_num)
theorem B1831877 : Blo 810345 1831877 := bbase (se 4 (by rfl) ⟨171738, by rfl⟩ : syracuseStep 1831877 = 343477) (by norm_num)
theorem B914377 : Blo 810345 914377 := bbase (se 2 (by rfl) ⟨342891, by rfl⟩ : syracuseStep 914377 = 685783) (by norm_num)
theorem B914413 : Blo 810345 914413 := bbase (se 3 (by rfl) ⟨171452, by rfl⟩ : syracuseStep 914413 = 342905) (by norm_num)
theorem B1831949 : Blo 810345 1831949 := bbase (se 3 (by rfl) ⟨343490, by rfl⟩ : syracuseStep 1831949 = 686981) (by norm_num)
theorem B914449 : Blo 810345 914449 := bbase (se 2 (by rfl) ⟨342918, by rfl⟩ : syracuseStep 914449 = 685837) (by norm_num)
theorem B1373213 : Blo 810345 1373213 := bbase (se 3 (by rfl) ⟨257477, by rfl⟩ : syracuseStep 1373213 = 514955) (by norm_num)
theorem B914485 : Blo 810345 914485 := bbase (se 5 (by rfl) ⟨42866, by rfl⟩ : syracuseStep 914485 = 85733) (by norm_num)
theorem B1832021 : Blo 810345 1832021 := bbase (se 8 (by rfl) ⟨10734, by rfl⟩ : syracuseStep 1832021 = 21469) (by norm_num)
theorem B914521 : Blo 810345 914521 := bbase (se 2 (by rfl) ⟨342945, by rfl⟩ : syracuseStep 914521 = 685891) (by norm_num)
theorem B2782325 : Blo 810345 2782325 := bbase (se 5 (by rfl) ⟨130421, by rfl⟩ : syracuseStep 2782325 = 260843) (by norm_num)
theorem B914557 : Blo 810345 914557 := bbase (se 3 (by rfl) ⟨171479, by rfl⟩ : syracuseStep 914557 = 342959) (by norm_num)
theorem B1373341 : Blo 810345 1373341 := bbase (se 3 (by rfl) ⟨257501, by rfl⟩ : syracuseStep 1373341 = 515003) (by norm_num)
theorem B1832093 : Blo 810345 1832093 := bbase (se 3 (by rfl) ⟨343517, by rfl⟩ : syracuseStep 1832093 = 687035) (by norm_num)
theorem B914593 : Blo 810345 914593 := bbase (se 2 (by rfl) ⟨342972, by rfl⟩ : syracuseStep 914593 = 685945) (by norm_num)
theorem B1733813 : Blo 810345 1733813 := bbase (se 5 (by rfl) ⟨81272, by rfl⟩ : syracuseStep 1733813 = 162545) (by norm_num)
theorem B914629 : Blo 810345 914629 := bbase (se 4 (by rfl) ⟨85746, by rfl⟩ : syracuseStep 914629 = 171493) (by norm_num)
theorem B1832165 : Blo 810345 1832165 := bbase (se 4 (by rfl) ⟨171765, by rfl⟩ : syracuseStep 1832165 = 343531) (by norm_num)
theorem B914665 : Blo 810345 914665 := bbase (se 2 (by rfl) ⟨342999, by rfl⟩ : syracuseStep 914665 = 685999) (by norm_num)
theorem B1373429 : Blo 810345 1373429 := bbase (se 5 (by rfl) ⟨64379, by rfl⟩ : syracuseStep 1373429 = 128759) (by norm_num)
theorem B914701 : Blo 810345 914701 := bbase (se 3 (by rfl) ⟨171506, by rfl⟩ : syracuseStep 914701 = 343013) (by norm_num)
theorem B1832237 : Blo 810345 1832237 := bbase (se 3 (by rfl) ⟨343544, by rfl⟩ : syracuseStep 1832237 = 687089) (by norm_num)
theorem B914737 : Blo 810345 914737 := bbase (se 2 (by rfl) ⟨343026, by rfl⟩ : syracuseStep 914737 = 686053) (by norm_num)
theorem B914773 : Blo 810345 914773 := bbase (se 13 (by rfl) ⟨167, by rfl⟩ : syracuseStep 914773 = 335) (by norm_num)
theorem B1373557 : Blo 810345 1373557 := bbase (se 5 (by rfl) ⟨64385, by rfl⟩ : syracuseStep 1373557 = 128771) (by norm_num)
theorem B914809 : Blo 810345 914809 := bbase (se 2 (by rfl) ⟨343053, by rfl⟩ : syracuseStep 914809 = 686107) (by norm_num)
theorem B914845 : Blo 810345 914845 := bbase (se 3 (by rfl) ⟨171533, by rfl⟩ : syracuseStep 914845 = 343067) (by norm_num)
theorem B914881 : Blo 810345 914881 := bbase (se 2 (by rfl) ⟨343080, by rfl⟩ : syracuseStep 914881 = 686161) (by norm_num)
theorem B1373645 : Blo 810345 1373645 := bbase (se 3 (by rfl) ⟨257558, by rfl⟩ : syracuseStep 1373645 = 515117) (by norm_num)
theorem B914917 : Blo 810345 914917 := bbase (se 4 (by rfl) ⟨85773, by rfl⟩ : syracuseStep 914917 = 171547) (by norm_num)
theorem B914953 : Blo 810345 914953 := bbase (se 2 (by rfl) ⟨343107, by rfl⟩ : syracuseStep 914953 = 686215) (by norm_num)
theorem B914989 : Blo 810345 914989 := bbase (se 3 (by rfl) ⟨171560, by rfl⟩ : syracuseStep 914989 = 343121) (by norm_num)
theorem B1373773 : Blo 810345 1373773 := bbase (se 3 (by rfl) ⟨257582, by rfl⟩ : syracuseStep 1373773 = 515165) (by norm_num)
theorem B915025 : Blo 810345 915025 := bbase (se 2 (by rfl) ⟨343134, by rfl⟩ : syracuseStep 915025 = 686269) (by norm_num)
theorem B915061 : Blo 810345 915061 := bbase (se 5 (by rfl) ⟨42893, by rfl⟩ : syracuseStep 915061 = 85787) (by norm_num)
theorem B915097 : Blo 810345 915097 := bbase (se 2 (by rfl) ⟨343161, by rfl⟩ : syracuseStep 915097 = 686323) (by norm_num)
theorem B1373861 : Blo 810345 1373861 := bbase (se 4 (by rfl) ⟨128799, by rfl⟩ : syracuseStep 1373861 = 257599) (by norm_num)
theorem B915133 : Blo 810345 915133 := bbase (se 3 (by rfl) ⟨171587, by rfl⟩ : syracuseStep 915133 = 343175) (by norm_num)
theorem B915169 : Blo 810345 915169 := bbase (se 2 (by rfl) ⟨343188, by rfl⟩ : syracuseStep 915169 = 686377) (by norm_num)
theorem B915205 : Blo 810345 915205 := bbase (se 4 (by rfl) ⟨85800, by rfl⟩ : syracuseStep 915205 = 171601) (by norm_num)
theorem B1373989 : Blo 810345 1373989 := bbase (se 4 (by rfl) ⟨128811, by rfl⟩ : syracuseStep 1373989 = 257623) (by norm_num)
theorem B915241 : Blo 810345 915241 := bbase (se 2 (by rfl) ⟨343215, by rfl⟩ : syracuseStep 915241 = 686431) (by norm_num)
theorem B915277 : Blo 810345 915277 := bbase (se 3 (by rfl) ⟨171614, by rfl⟩ : syracuseStep 915277 = 343229) (by norm_num)
theorem B915313 : Blo 810345 915313 := bbase (se 2 (by rfl) ⟨343242, by rfl⟩ : syracuseStep 915313 = 686485) (by norm_num)
theorem B1374077 : Blo 810345 1374077 := bbase (se 3 (by rfl) ⟨257639, by rfl⟩ : syracuseStep 1374077 = 515279) (by norm_num)
theorem B915349 : Blo 810345 915349 := bbase (se 6 (by rfl) ⟨21453, by rfl⟩ : syracuseStep 915349 = 42907) (by norm_num)
theorem B915385 : Blo 810345 915385 := bbase (se 2 (by rfl) ⟨343269, by rfl⟩ : syracuseStep 915385 = 686539) (by norm_num)
theorem B915421 : Blo 810345 915421 := bbase (se 3 (by rfl) ⟨171641, by rfl⟩ : syracuseStep 915421 = 343283) (by norm_num)
theorem B1374205 : Blo 810345 1374205 := bbase (se 3 (by rfl) ⟨257663, by rfl⟩ : syracuseStep 1374205 = 515327) (by norm_num)
theorem B915457 : Blo 810345 915457 := bbase (se 2 (by rfl) ⟨343296, by rfl⟩ : syracuseStep 915457 = 686593) (by norm_num)
theorem B915493 : Blo 810345 915493 := bbase (se 4 (by rfl) ⟨85827, by rfl⟩ : syracuseStep 915493 = 171655) (by norm_num)
theorem B1734701 : Blo 810345 1734701 := bbase (se 3 (by rfl) ⟨325256, by rfl⟩ : syracuseStep 1734701 = 650513) (by norm_num)
theorem B915529 : Blo 810345 915529 := bbase (se 2 (by rfl) ⟨343323, by rfl⟩ : syracuseStep 915529 = 686647) (by norm_num)
theorem B2193493 : Blo 810345 2193493 := bbase (se 8 (by rfl) ⟨12852, by rfl⟩ : syracuseStep 2193493 = 25705) (by norm_num)
theorem B915565 : Blo 810345 915565 := bbase (se 3 (by rfl) ⟨171668, by rfl⟩ : syracuseStep 915565 = 343337) (by norm_num)
theorem B915601 : Blo 810345 915601 := bbase (se 2 (by rfl) ⟨343350, by rfl⟩ : syracuseStep 915601 = 686701) (by norm_num)
theorem B915637 : Blo 810345 915637 := bbase (se 5 (by rfl) ⟨42920, by rfl⟩ : syracuseStep 915637 = 85841) (by norm_num)
theorem B915673 : Blo 810345 915673 := bbase (se 2 (by rfl) ⟨343377, by rfl⟩ : syracuseStep 915673 = 686755) (by norm_num)
theorem B3471589 : Blo 810345 3471589 := bbase (se 4 (by rfl) ⟨325461, by rfl⟩ : syracuseStep 3471589 = 650923) (by norm_num)
theorem B915709 : Blo 810345 915709 := bbase (se 3 (by rfl) ⟨171695, by rfl⟩ : syracuseStep 915709 = 343391) (by norm_num)
theorem B1734941 : Blo 810345 1734941 := bbase (se 3 (by rfl) ⟨325301, by rfl⟩ : syracuseStep 1734941 = 650603) (by norm_num)
theorem B915745 : Blo 810345 915745 := bbase (se 2 (by rfl) ⟨343404, by rfl⟩ : syracuseStep 915745 = 686809) (by norm_num)
theorem B915781 : Blo 810345 915781 := bbase (se 4 (by rfl) ⟨85854, by rfl⟩ : syracuseStep 915781 = 171709) (by norm_num)
theorem B2783573 : Blo 810345 2783573 := bbase (se 10 (by rfl) ⟨4077, by rfl⟩ : syracuseStep 2783573 = 8155) (by norm_num)
theorem B915817 : Blo 810345 915817 := bbase (se 2 (by rfl) ⟨343431, by rfl⟩ : syracuseStep 915817 = 686863) (by norm_num)
theorem B915853 : Blo 810345 915853 := bbase (se 3 (by rfl) ⟨171722, by rfl⟩ : syracuseStep 915853 = 343445) (by norm_num)
theorem B915889 : Blo 810345 915889 := bbase (se 2 (by rfl) ⟨343458, by rfl⟩ : syracuseStep 915889 = 686917) (by norm_num)
theorem B1538509 : Blo 810345 1538509 := bbase (se 3 (by rfl) ⟨288470, by rfl⟩ : syracuseStep 1538509 = 576941) (by norm_num)
theorem B915925 : Blo 810345 915925 := bbase (se 7 (by rfl) ⟨10733, by rfl⟩ : syracuseStep 915925 = 21467) (by norm_num)
theorem B915961 : Blo 810345 915961 := bbase (se 2 (by rfl) ⟨343485, by rfl⟩ : syracuseStep 915961 = 686971) (by norm_num)
theorem B4946453 : Blo 810345 4946453 := bbase (se 6 (by rfl) ⟨115932, by rfl⟩ : syracuseStep 4946453 = 231865) (by norm_num)
theorem B915997 : Blo 810345 915997 := bbase (se 3 (by rfl) ⟨171749, by rfl⟩ : syracuseStep 915997 = 343499) (by norm_num)
theorem B916033 : Blo 810345 916033 := bbase (se 2 (by rfl) ⟨343512, by rfl⟩ : syracuseStep 916033 = 687025) (by norm_num)
theorem B6945365 : Blo 810345 6945365 := bbase (se 8 (by rfl) ⟨40695, by rfl⟩ : syracuseStep 6945365 = 81391) (by norm_num)
theorem B916069 : Blo 810345 916069 := bbase (se 4 (by rfl) ⟨85881, by rfl⟩ : syracuseStep 916069 = 171763) (by norm_num)
theorem B1538669 : Blo 810345 1538669 := bbase (se 3 (by rfl) ⟨288500, by rfl⟩ : syracuseStep 1538669 = 577001) (by norm_num)
theorem B916105 : Blo 810345 916105 := bbase (se 2 (by rfl) ⟨343539, by rfl⟩ : syracuseStep 916105 = 687079) (by norm_num)
theorem B1538813 : Blo 810345 1538813 := bbase (se 3 (by rfl) ⟨288527, by rfl⟩ : syracuseStep 1538813 = 577055) (by norm_num)
theorem B3078917 : Blo 810345 3078917 := bbase (se 4 (by rfl) ⟨288648, by rfl⟩ : syracuseStep 3078917 = 577297) (by norm_num)
theorem B1735445 : Blo 810345 1735445 := bbase (se 6 (by rfl) ⟨40674, by rfl⟩ : syracuseStep 1735445 = 81349) (by norm_num)
theorem B1735453 : Blo 810345 1735453 := bbase (se 3 (by rfl) ⟨325397, by rfl⟩ : syracuseStep 1735453 = 650795) (by norm_num)
theorem B1539101 : Blo 810345 1539101 := bbase (se 3 (by rfl) ⟨288581, by rfl⟩ : syracuseStep 1539101 = 577163) (by norm_num)
theorem B3079205 : Blo 810345 3079205 := bbase (se 4 (by rfl) ⟨288675, by rfl⟩ : syracuseStep 3079205 = 577351) (by norm_num)
theorem B2227301 : Blo 810345 2227301 := bbase (se 4 (by rfl) ⟨208809, by rfl⟩ : syracuseStep 2227301 = 417619) (by norm_num)
theorem B1539253 : Blo 810345 1539253 := bbase (se 5 (by rfl) ⟨72152, by rfl⟩ : syracuseStep 1539253 = 144305) (by norm_num)
theorem B1539557 : Blo 810345 1539557 := bbase (se 4 (by rfl) ⟨144333, by rfl⟩ : syracuseStep 1539557 = 288667) (by norm_num)
theorem B9895445 : Blo 810345 9895445 := bbase (se 6 (by rfl) ⟨231924, by rfl⟩ : syracuseStep 9895445 = 463849) (by norm_num)
theorem B3473077 : Blo 810345 3473077 := bbase (se 5 (by rfl) ⟨162800, by rfl⟩ : syracuseStep 3473077 = 325601) (by norm_num)
theorem B3342005 : Blo 810345 3342005 := bbase (se 5 (by rfl) ⟨156656, by rfl⟩ : syracuseStep 3342005 = 313313) (by norm_num)
theorem B3473093 : Blo 810345 3473093 := bbase (se 4 (by rfl) ⟨325602, by rfl⟩ : syracuseStep 3473093 = 651205) (by norm_num)
theorem B2817845 : Blo 810345 2817845 := bbase (se 5 (by rfl) ⟨132086, by rfl⟩ : syracuseStep 2817845 = 264173) (by norm_num)
theorem B1736581 : Blo 810345 1736581 := bbase (se 4 (by rfl) ⟨162804, by rfl⟩ : syracuseStep 1736581 = 325609) (by norm_num)
theorem B3702725 : Blo 810345 3702725 := bbase (se 4 (by rfl) ⟨347130, by rfl⟩ : syracuseStep 3702725 = 694261) (by norm_num)
theorem B5931107 : Blo 810345 5931107 := bstep (se 1 (by rfl) ⟨4448330, by rfl⟩ : syracuseStep 5931107 = 8896661) B8896661
theorem B9240803 : Blo 810345 9240803 := bstep (se 1 (by rfl) ⟨6930602, by rfl⟩ : syracuseStep 9240803 = 13861205) B13861205
theorem B4391309 : Blo 810345 4391309 := bstep (se 3 (by rfl) ⟨823370, by rfl⟩ : syracuseStep 4391309 = 1646741) B1646741
theorem B1540529 : Blo 810345 1540529 := bstep (se 2 (by rfl) ⟨577698, by rfl⟩ : syracuseStep 1540529 = 1155397) B1155397
theorem B7799237 : Blo 810345 7799237 := bstep (se 4 (by rfl) ⟨731178, by rfl⟩ : syracuseStep 7799237 = 1462357) B1462357
theorem B5571107 : Blo 810345 5571107 := bstep (se 1 (by rfl) ⟨4178330, by rfl⟩ : syracuseStep 5571107 = 8356661) B8356661
theorem B2228849 : Blo 810345 2228849 := bstep (se 2 (by rfl) ⟨835818, by rfl⟩ : syracuseStep 2228849 = 1671637) B1671637
theorem B1737521 : Blo 810345 1737521 := bstep (se 2 (by rfl) ⟨651570, by rfl⟩ : syracuseStep 1737521 = 1303141) B1303141
theorem B2196305 : Blo 810345 2196305 := bstep (se 2 (by rfl) ⟨823614, by rfl⟩ : syracuseStep 2196305 = 1647229) B1647229
theorem B15827825 : Blo 810345 15827825 := bstep (se 2 (by rfl) ⟨5935434, by rfl⟩ : syracuseStep 15827825 = 11870869) B11870869
theorem B6161507 : Blo 810345 6161507 := bstep (se 1 (by rfl) ⟨4621130, by rfl⟩ : syracuseStep 6161507 = 9242261) B9242261
theorem B5637325 : Blo 810345 5637325 := bstep (se 3 (by rfl) ⟨1056998, by rfl⟩ : syracuseStep 5637325 = 2113997) B2113997
theorem B9045233 : Blo 810345 9045233 := bstep (se 2 (by rfl) ⟨3391962, by rfl⟩ : syracuseStep 9045233 = 6783925) B6783925
theorem B1541425 : Blo 810345 1541425 := bstep (se 2 (by rfl) ⟨578034, by rfl⟩ : syracuseStep 1541425 = 1156069) B1156069
theorem B16647565 : Blo 810345 16647565 := bstep (se 3 (by rfl) ⟨3121418, by rfl⟩ : syracuseStep 16647565 = 6242837) B6242837
theorem B3081635 : Blo 810345 3081635 := bstep (se 1 (by rfl) ⟨2311226, by rfl⟩ : syracuseStep 3081635 = 4622453) B4622453
theorem B1541585 : Blo 810345 1541585 := bstep (se 2 (by rfl) ⟨578094, by rfl⟩ : syracuseStep 1541585 = 1156189) B1156189
theorem B4622021 : Blo 810345 4622021 := bstep (se 4 (by rfl) ⟨433314, by rfl⟩ : syracuseStep 4622021 = 866629) B866629
theorem B1541987 : Blo 810345 1541987 := bstep (se 1 (by rfl) ⟨1156490, by rfl⟩ : syracuseStep 1541987 = 2312981) B2312981
theorem B3704717 : Blo 810345 3704717 := bstep (se 3 (by rfl) ⟨694634, by rfl⟩ : syracuseStep 3704717 = 1389269) B1389269
theorem B11241413 : Blo 810345 11241413 := bstep (se 4 (by rfl) ⟨1053882, by rfl⟩ : syracuseStep 11241413 = 2107765) B2107765
theorem B9373877 : Blo 810345 9373877 := bstep (se 5 (by rfl) ⟨439400, by rfl⟩ : syracuseStep 9373877 = 878801) B878801
theorem B35064035 : Blo 810345 35064035 := bstep (se 1 (by rfl) ⟨26298026, by rfl⟩ : syracuseStep 35064035 = 52596053) B52596053
theorem B1739075 : Blo 810345 1739075 := bstep (se 1 (by rfl) ⟨1304306, by rfl⟩ : syracuseStep 1739075 = 2608613) B2608613
theorem B3344717 : Blo 810345 3344717 := bstep (se 3 (by rfl) ⟨627134, by rfl⟩ : syracuseStep 3344717 = 1254269) B1254269
theorem B821587 : Blo 810345 821587 := bstep (se 1 (by rfl) ⟨616190, by rfl⟩ : syracuseStep 821587 = 1232381) B1232381
theorem B3475811 : Blo 810345 3475811 := bstep (se 1 (by rfl) ⟨2606858, by rfl⟩ : syracuseStep 3475811 = 5213717) B5213717
theorem B3082637 : Blo 810345 3082637 := bstep (se 3 (by rfl) ⟨577994, by rfl⟩ : syracuseStep 3082637 = 1155989) B1155989
theorem B5212613 : Blo 810345 5212613 := bstep (se 4 (by rfl) ⟨488682, by rfl⟩ : syracuseStep 5212613 = 977365) B977365
theorem B4950733 : Blo 810345 4950733 := bstep (se 3 (by rfl) ⟨928262, by rfl⟩ : syracuseStep 4950733 = 1856525) B1856525
theorem B1542883 : Blo 810345 1542883 := bstep (se 1 (by rfl) ⟨1157162, by rfl⟩ : syracuseStep 1542883 = 2314325) B2314325
theorem B1543043 : Blo 810345 1543043 := bstep (se 1 (by rfl) ⟨1157282, by rfl⟩ : syracuseStep 1543043 = 2314565) B2314565
theorem B1215521 : Blo 810345 1215521 := bstep (se 2 (by rfl) ⟨455820, by rfl⟩ : syracuseStep 1215521 = 911641) B911641
theorem B1215539 : Blo 810345 1215539 := bstep (se 1 (by rfl) ⟨911654, by rfl⟩ : syracuseStep 1215539 = 1823309) B1823309
theorem B1215569 : Blo 810345 1215569 := bstep (se 2 (by rfl) ⟨455838, by rfl⟩ : syracuseStep 1215569 = 911677) B911677
theorem B1215587 : Blo 810345 1215587 := bstep (se 1 (by rfl) ⟨911690, by rfl⟩ : syracuseStep 1215587 = 1823381) B1823381
theorem B1215617 : Blo 810345 1215617 := bstep (se 2 (by rfl) ⟨455856, by rfl⟩ : syracuseStep 1215617 = 911713) B911713
theorem B1215635 : Blo 810345 1215635 := bstep (se 1 (by rfl) ⟨911726, by rfl⟩ : syracuseStep 1215635 = 1823453) B1823453
theorem B1215665 : Blo 810345 1215665 := bstep (se 2 (by rfl) ⟨455874, by rfl⟩ : syracuseStep 1215665 = 911749) B911749
theorem B1215683 : Blo 810345 1215683 := bstep (se 1 (by rfl) ⟨911762, by rfl⟩ : syracuseStep 1215683 = 1823525) B1823525
theorem B1215713 : Blo 810345 1215713 := bstep (se 2 (by rfl) ⟨455892, by rfl⟩ : syracuseStep 1215713 = 911785) B911785
theorem B1215731 : Blo 810345 1215731 := bstep (se 1 (by rfl) ⟨911798, by rfl⟩ : syracuseStep 1215731 = 1823597) B1823597
theorem B1215761 : Blo 810345 1215761 := bstep (se 2 (by rfl) ⟨455910, by rfl⟩ : syracuseStep 1215761 = 911821) B911821
theorem B1215779 : Blo 810345 1215779 := bstep (se 1 (by rfl) ⟨911834, by rfl⟩ : syracuseStep 1215779 = 1823669) B1823669
theorem B1215809 : Blo 810345 1215809 := bstep (se 2 (by rfl) ⟨455928, by rfl⟩ : syracuseStep 1215809 = 911857) B911857
theorem B1215827 : Blo 810345 1215827 := bstep (se 1 (by rfl) ⟨911870, by rfl⟩ : syracuseStep 1215827 = 1823741) B1823741
theorem B1215857 : Blo 810345 1215857 := bstep (se 2 (by rfl) ⟨455946, by rfl⟩ : syracuseStep 1215857 = 911893) B911893
theorem B1215875 : Blo 810345 1215875 := bstep (se 1 (by rfl) ⟨911906, by rfl⟩ : syracuseStep 1215875 = 1823813) B1823813
theorem B1215905 : Blo 810345 1215905 := bstep (se 2 (by rfl) ⟨455964, by rfl⟩ : syracuseStep 1215905 = 911929) B911929
theorem B1215923 : Blo 810345 1215923 := bstep (se 1 (by rfl) ⟨911942, by rfl⟩ : syracuseStep 1215923 = 1823885) B1823885
theorem B1215953 : Blo 810345 1215953 := bstep (se 2 (by rfl) ⟨455982, by rfl⟩ : syracuseStep 1215953 = 911965) B911965
theorem B1215971 : Blo 810345 1215971 := bstep (se 1 (by rfl) ⟨911978, by rfl⟩ : syracuseStep 1215971 = 1823957) B1823957
theorem B1216001 : Blo 810345 1216001 := bstep (se 2 (by rfl) ⟨456000, by rfl⟩ : syracuseStep 1216001 = 912001) B912001
theorem B1216019 : Blo 810345 1216019 := bstep (se 1 (by rfl) ⟨912014, by rfl⟩ : syracuseStep 1216019 = 1824029) B1824029
theorem B1216049 : Blo 810345 1216049 := bstep (se 2 (by rfl) ⟨456018, by rfl⟩ : syracuseStep 1216049 = 912037) B912037
theorem B1216067 : Blo 810345 1216067 := bstep (se 1 (by rfl) ⟨912050, by rfl⟩ : syracuseStep 1216067 = 1824101) B1824101
theorem B1216097 : Blo 810345 1216097 := bstep (se 2 (by rfl) ⟨456036, by rfl⟩ : syracuseStep 1216097 = 912073) B912073
theorem B4689521 : Blo 810345 4689521 := bstep (se 2 (by rfl) ⟨1758570, by rfl⟩ : syracuseStep 4689521 = 3517141) B3517141
theorem B1216115 : Blo 810345 1216115 := bstep (se 1 (by rfl) ⟨912086, by rfl⟩ : syracuseStep 1216115 = 1824173) B1824173
theorem B1216145 : Blo 810345 1216145 := bstep (se 2 (by rfl) ⟨456054, by rfl⟩ : syracuseStep 1216145 = 912109) B912109
theorem B1216163 : Blo 810345 1216163 := bstep (se 1 (by rfl) ⟨912122, by rfl⟩ : syracuseStep 1216163 = 1824245) B1824245
theorem B1216193 : Blo 810345 1216193 := bstep (se 2 (by rfl) ⟨456072, by rfl⟩ : syracuseStep 1216193 = 912145) B912145
theorem B1216211 : Blo 810345 1216211 := bstep (se 1 (by rfl) ⟨912158, by rfl⟩ : syracuseStep 1216211 = 1824317) B1824317
theorem B20811491 : Blo 810345 20811491 := bstep (se 1 (by rfl) ⟨15608618, by rfl⟩ : syracuseStep 20811491 = 31217237) B31217237
theorem B1216241 : Blo 810345 1216241 := bstep (se 2 (by rfl) ⟨456090, by rfl⟩ : syracuseStep 1216241 = 912181) B912181
theorem B1216259 : Blo 810345 1216259 := bstep (se 1 (by rfl) ⟨912194, by rfl⟩ : syracuseStep 1216259 = 1824389) B1824389
theorem B1216289 : Blo 810345 1216289 := bstep (se 2 (by rfl) ⟨456108, by rfl⟩ : syracuseStep 1216289 = 912217) B912217
theorem B1216307 : Blo 810345 1216307 := bstep (se 1 (by rfl) ⟨912230, by rfl⟩ : syracuseStep 1216307 = 1824461) B1824461
theorem B1216337 : Blo 810345 1216337 := bstep (se 2 (by rfl) ⟨456126, by rfl⟩ : syracuseStep 1216337 = 912253) B912253
theorem B1216355 : Blo 810345 1216355 := bstep (se 1 (by rfl) ⟨912266, by rfl⟩ : syracuseStep 1216355 = 1824533) B1824533
theorem B1216385 : Blo 810345 1216385 := bstep (se 2 (by rfl) ⟨456144, by rfl⟩ : syracuseStep 1216385 = 912289) B912289
theorem B1216403 : Blo 810345 1216403 := bstep (se 1 (by rfl) ⟨912302, by rfl⟩ : syracuseStep 1216403 = 1824605) B1824605
theorem B1216433 : Blo 810345 1216433 := bstep (se 2 (by rfl) ⟨456162, by rfl⟩ : syracuseStep 1216433 = 912325) B912325
theorem B1544113 : Blo 810345 1544113 := bstep (se 2 (by rfl) ⟨579042, by rfl⟩ : syracuseStep 1544113 = 1158085) B1158085
theorem B1216451 : Blo 810345 1216451 := bstep (se 1 (by rfl) ⟨912338, by rfl⟩ : syracuseStep 1216451 = 1824677) B1824677
theorem B1216481 : Blo 810345 1216481 := bstep (se 2 (by rfl) ⟨456180, by rfl⟩ : syracuseStep 1216481 = 912361) B912361
theorem B7802851 : Blo 810345 7802851 := bstep (se 1 (by rfl) ⟨5852138, by rfl⟩ : syracuseStep 7802851 = 11704277) B11704277
theorem B1216499 : Blo 810345 1216499 := bstep (se 1 (by rfl) ⟨912374, by rfl⟩ : syracuseStep 1216499 = 1824749) B1824749
theorem B1216529 : Blo 810345 1216529 := bstep (se 2 (by rfl) ⟨456198, by rfl⟩ : syracuseStep 1216529 = 912397) B912397
theorem B1216547 : Blo 810345 1216547 := bstep (se 1 (by rfl) ⟨912410, by rfl⟩ : syracuseStep 1216547 = 1824821) B1824821
theorem B1216577 : Blo 810345 1216577 := bstep (se 2 (by rfl) ⟨456216, by rfl⟩ : syracuseStep 1216577 = 912433) B912433
theorem B1216595 : Blo 810345 1216595 := bstep (se 1 (by rfl) ⟨912446, by rfl⟩ : syracuseStep 1216595 = 1824893) B1824893
theorem B1216625 : Blo 810345 1216625 := bstep (se 2 (by rfl) ⟨456234, by rfl⟩ : syracuseStep 1216625 = 912469) B912469
theorem B1216643 : Blo 810345 1216643 := bstep (se 1 (by rfl) ⟨912482, by rfl⟩ : syracuseStep 1216643 = 1824965) B1824965
theorem B1216673 : Blo 810345 1216673 := bstep (se 2 (by rfl) ⟨456252, by rfl⟩ : syracuseStep 1216673 = 912505) B912505
theorem B1216691 : Blo 810345 1216691 := bstep (se 1 (by rfl) ⟨912518, by rfl⟩ : syracuseStep 1216691 = 1825037) B1825037
theorem B1216721 : Blo 810345 1216721 := bstep (se 2 (by rfl) ⟨456270, by rfl⟩ : syracuseStep 1216721 = 912541) B912541
theorem B1216739 : Blo 810345 1216739 := bstep (se 1 (by rfl) ⟨912554, by rfl⟩ : syracuseStep 1216739 = 1825109) B1825109
theorem B1216769 : Blo 810345 1216769 := bstep (se 2 (by rfl) ⟨456288, by rfl⟩ : syracuseStep 1216769 = 912577) B912577
theorem B1216787 : Blo 810345 1216787 := bstep (se 1 (by rfl) ⟨912590, by rfl⟩ : syracuseStep 1216787 = 1825181) B1825181
theorem B1216817 : Blo 810345 1216817 := bstep (se 2 (by rfl) ⟨456306, by rfl⟩ : syracuseStep 1216817 = 912613) B912613
theorem B3477809 : Blo 810345 3477809 := bstep (se 2 (by rfl) ⟨1304178, by rfl⟩ : syracuseStep 3477809 = 2608357) B2608357
theorem B1216835 : Blo 810345 1216835 := bstep (se 1 (by rfl) ⟨912626, by rfl⟩ : syracuseStep 1216835 = 1825253) B1825253
theorem B1216865 : Blo 810345 1216865 := bstep (se 2 (by rfl) ⟨456324, by rfl⟩ : syracuseStep 1216865 = 912649) B912649
theorem B1216883 : Blo 810345 1216883 := bstep (se 1 (by rfl) ⟨912662, by rfl⟩ : syracuseStep 1216883 = 1825325) B1825325
theorem B1216913 : Blo 810345 1216913 := bstep (se 2 (by rfl) ⟨456342, by rfl⟩ : syracuseStep 1216913 = 912685) B912685
theorem B1216931 : Blo 810345 1216931 := bstep (se 1 (by rfl) ⟨912698, by rfl⟩ : syracuseStep 1216931 = 1825397) B1825397
theorem B1216961 : Blo 810345 1216961 := bstep (se 2 (by rfl) ⟨456360, by rfl⟩ : syracuseStep 1216961 = 912721) B912721
theorem B3084749 : Blo 810345 3084749 := bstep (se 3 (by rfl) ⟨578390, by rfl⟩ : syracuseStep 3084749 = 1156781) B1156781
theorem B1216979 : Blo 810345 1216979 := bstep (se 1 (by rfl) ⟨912734, by rfl⟩ : syracuseStep 1216979 = 1825469) B1825469
theorem B1217009 : Blo 810345 1217009 := bstep (se 2 (by rfl) ⟨456378, by rfl⟩ : syracuseStep 1217009 = 912757) B912757
theorem B1217027 : Blo 810345 1217027 := bstep (se 1 (by rfl) ⟨912770, by rfl⟩ : syracuseStep 1217027 = 1825541) B1825541
theorem B1217057 : Blo 810345 1217057 := bstep (se 2 (by rfl) ⟨456396, by rfl⟩ : syracuseStep 1217057 = 912793) B912793
theorem B1217075 : Blo 810345 1217075 := bstep (se 1 (by rfl) ⟨912806, by rfl⟩ : syracuseStep 1217075 = 1825613) B1825613
theorem B987715 : Blo 810345 987715 := bstep (se 1 (by rfl) ⟨740786, by rfl⟩ : syracuseStep 987715 = 1481573) B1481573
theorem B1217105 : Blo 810345 1217105 := bstep (se 2 (by rfl) ⟨456414, by rfl⟩ : syracuseStep 1217105 = 912829) B912829
theorem B1217123 : Blo 810345 1217123 := bstep (se 1 (by rfl) ⟨912842, by rfl⟩ : syracuseStep 1217123 = 1825685) B1825685
theorem B1217153 : Blo 810345 1217153 := bstep (se 2 (by rfl) ⟨456432, by rfl⟩ : syracuseStep 1217153 = 912865) B912865
theorem B1217171 : Blo 810345 1217171 := bstep (se 1 (by rfl) ⟨912878, by rfl⟩ : syracuseStep 1217171 = 1825757) B1825757
theorem B1217201 : Blo 810345 1217201 := bstep (se 2 (by rfl) ⟨456450, by rfl⟩ : syracuseStep 1217201 = 912901) B912901
theorem B1217219 : Blo 810345 1217219 := bstep (se 1 (by rfl) ⟨912914, by rfl⟩ : syracuseStep 1217219 = 1825829) B1825829
theorem B1217249 : Blo 810345 1217249 := bstep (se 2 (by rfl) ⟨456468, by rfl⟩ : syracuseStep 1217249 = 912937) B912937
theorem B1217267 : Blo 810345 1217267 := bstep (se 1 (by rfl) ⟨912950, by rfl⟩ : syracuseStep 1217267 = 1825901) B1825901
theorem B1217297 : Blo 810345 1217297 := bstep (se 2 (by rfl) ⟨456486, by rfl⟩ : syracuseStep 1217297 = 912973) B912973
theorem B1217315 : Blo 810345 1217315 := bstep (se 1 (by rfl) ⟨912986, by rfl⟩ : syracuseStep 1217315 = 1825973) B1825973
theorem B1217345 : Blo 810345 1217345 := bstep (se 2 (by rfl) ⟨456504, by rfl⟩ : syracuseStep 1217345 = 913009) B913009
theorem B1217363 : Blo 810345 1217363 := bstep (se 1 (by rfl) ⟨913022, by rfl⟩ : syracuseStep 1217363 = 1826045) B1826045
theorem B1217393 : Blo 810345 1217393 := bstep (se 2 (by rfl) ⟨456522, by rfl⟩ : syracuseStep 1217393 = 913045) B913045
theorem B1217411 : Blo 810345 1217411 := bstep (se 1 (by rfl) ⟨913058, by rfl⟩ : syracuseStep 1217411 = 1826117) B1826117
theorem B1217441 : Blo 810345 1217441 := bstep (se 2 (by rfl) ⟨456540, by rfl⟩ : syracuseStep 1217441 = 913081) B913081
theorem B1217459 : Blo 810345 1217459 := bstep (se 1 (by rfl) ⟨913094, by rfl⟩ : syracuseStep 1217459 = 1826189) B1826189
theorem B1217489 : Blo 810345 1217489 := bstep (se 2 (by rfl) ⟨456558, by rfl⟩ : syracuseStep 1217489 = 913117) B913117
theorem B1545169 : Blo 810345 1545169 := bstep (se 2 (by rfl) ⟨579438, by rfl⟩ : syracuseStep 1545169 = 1158877) B1158877
theorem B1217507 : Blo 810345 1217507 := bstep (se 1 (by rfl) ⟨913130, by rfl⟩ : syracuseStep 1217507 = 1826261) B1826261
theorem B1217537 : Blo 810345 1217537 := bstep (se 2 (by rfl) ⟨456576, by rfl⟩ : syracuseStep 1217537 = 913153) B913153
theorem B1217555 : Blo 810345 1217555 := bstep (se 1 (by rfl) ⟨913166, by rfl⟩ : syracuseStep 1217555 = 1826333) B1826333
theorem B1217585 : Blo 810345 1217585 := bstep (se 2 (by rfl) ⟨456594, by rfl⟩ : syracuseStep 1217585 = 913189) B913189
theorem B1217603 : Blo 810345 1217603 := bstep (se 1 (by rfl) ⟨913202, by rfl⟩ : syracuseStep 1217603 = 1826405) B1826405
theorem B1315921 : Blo 810345 1315921 := bstep (se 2 (by rfl) ⟨493470, by rfl⟩ : syracuseStep 1315921 = 986941) B986941
theorem B1217633 : Blo 810345 1217633 := bstep (se 2 (by rfl) ⟨456612, by rfl⟩ : syracuseStep 1217633 = 913225) B913225
theorem B1217651 : Blo 810345 1217651 := bstep (se 1 (by rfl) ⟨913238, by rfl⟩ : syracuseStep 1217651 = 1826477) B1826477
theorem B1217681 : Blo 810345 1217681 := bstep (se 2 (by rfl) ⟨456630, by rfl⟩ : syracuseStep 1217681 = 913261) B913261
theorem B1217699 : Blo 810345 1217699 := bstep (se 1 (by rfl) ⟨913274, by rfl⟩ : syracuseStep 1217699 = 1826549) B1826549
theorem B1217729 : Blo 810345 1217729 := bstep (se 2 (by rfl) ⟨456648, by rfl⟩ : syracuseStep 1217729 = 913297) B913297
theorem B1217747 : Blo 810345 1217747 := bstep (se 1 (by rfl) ⟨913310, by rfl⟩ : syracuseStep 1217747 = 1826621) B1826621
theorem B1217777 : Blo 810345 1217777 := bstep (se 2 (by rfl) ⟨456666, by rfl⟩ : syracuseStep 1217777 = 913333) B913333
theorem B3085553 : Blo 810345 3085553 := bstep (se 2 (by rfl) ⟨1157082, by rfl⟩ : syracuseStep 3085553 = 2314165) B2314165
theorem B1217795 : Blo 810345 1217795 := bstep (se 1 (by rfl) ⟨913346, by rfl⟩ : syracuseStep 1217795 = 1826693) B1826693
theorem B1217825 : Blo 810345 1217825 := bstep (se 2 (by rfl) ⟨456684, by rfl⟩ : syracuseStep 1217825 = 913369) B913369
theorem B1217843 : Blo 810345 1217843 := bstep (se 1 (by rfl) ⟨913382, by rfl⟩ : syracuseStep 1217843 = 1826765) B1826765
theorem B1217873 : Blo 810345 1217873 := bstep (se 2 (by rfl) ⟨456702, by rfl⟩ : syracuseStep 1217873 = 913405) B913405
theorem B1217891 : Blo 810345 1217891 := bstep (se 1 (by rfl) ⟨913418, by rfl⟩ : syracuseStep 1217891 = 1826837) B1826837
theorem B1545571 : Blo 810345 1545571 := bstep (se 1 (by rfl) ⟨1159178, by rfl⟩ : syracuseStep 1545571 = 2318357) B2318357
theorem B1217921 : Blo 810345 1217921 := bstep (se 2 (by rfl) ⟨456720, by rfl⟩ : syracuseStep 1217921 = 913441) B913441
theorem B1545617 : Blo 810345 1545617 := bstep (se 2 (by rfl) ⟨579606, by rfl⟩ : syracuseStep 1545617 = 1159213) B1159213
theorem B1217939 : Blo 810345 1217939 := bstep (se 1 (by rfl) ⟨913454, by rfl⟩ : syracuseStep 1217939 = 1826909) B1826909
theorem B1217969 : Blo 810345 1217969 := bstep (se 2 (by rfl) ⟨456738, by rfl⟩ : syracuseStep 1217969 = 913477) B913477
theorem B1217987 : Blo 810345 1217987 := bstep (se 1 (by rfl) ⟨913490, by rfl⟩ : syracuseStep 1217987 = 1826981) B1826981
theorem B4625869 : Blo 810345 4625869 := bstep (se 3 (by rfl) ⟨867350, by rfl⟩ : syracuseStep 4625869 = 1734701) B1734701
theorem B1218017 : Blo 810345 1218017 := bstep (se 2 (by rfl) ⟨456756, by rfl⟩ : syracuseStep 1218017 = 913513) B913513
theorem B1218035 : Blo 810345 1218035 := bstep (se 1 (by rfl) ⟨913526, by rfl⟩ : syracuseStep 1218035 = 1827053) B1827053
theorem B1218065 : Blo 810345 1218065 := bstep (se 2 (by rfl) ⟨456774, by rfl⟩ : syracuseStep 1218065 = 913549) B913549
theorem B1218083 : Blo 810345 1218083 := bstep (se 1 (by rfl) ⟨913562, by rfl⟩ : syracuseStep 1218083 = 1827125) B1827125
theorem B1218113 : Blo 810345 1218113 := bstep (se 2 (by rfl) ⟨456792, by rfl⟩ : syracuseStep 1218113 = 913585) B913585
theorem B1218131 : Blo 810345 1218131 := bstep (se 1 (by rfl) ⟨913598, by rfl⟩ : syracuseStep 1218131 = 1827197) B1827197
theorem B988771 : Blo 810345 988771 := bstep (se 1 (by rfl) ⟨741578, by rfl⟩ : syracuseStep 988771 = 1483157) B1483157
theorem B1218161 : Blo 810345 1218161 := bstep (se 2 (by rfl) ⟨456810, by rfl⟩ : syracuseStep 1218161 = 913621) B913621
theorem B4691569 : Blo 810345 4691569 := bstep (se 2 (by rfl) ⟨1759338, by rfl⟩ : syracuseStep 4691569 = 3518677) B3518677
theorem B1218179 : Blo 810345 1218179 := bstep (se 1 (by rfl) ⟨913634, by rfl⟩ : syracuseStep 1218179 = 1827269) B1827269
theorem B1218209 : Blo 810345 1218209 := bstep (se 2 (by rfl) ⟨456828, by rfl⟩ : syracuseStep 1218209 = 913657) B913657
theorem B1545905 : Blo 810345 1545905 := bstep (se 2 (by rfl) ⟨579714, by rfl⟩ : syracuseStep 1545905 = 1159429) B1159429
theorem B1218227 : Blo 810345 1218227 := bstep (se 1 (by rfl) ⟨913670, by rfl⟩ : syracuseStep 1218227 = 1827341) B1827341
theorem B1218257 : Blo 810345 1218257 := bstep (se 2 (by rfl) ⟨456846, by rfl⟩ : syracuseStep 1218257 = 913693) B913693
theorem B1218275 : Blo 810345 1218275 := bstep (se 1 (by rfl) ⟨913706, by rfl⟩ : syracuseStep 1218275 = 1827413) B1827413
theorem B1218305 : Blo 810345 1218305 := bstep (se 2 (by rfl) ⟨456864, by rfl⟩ : syracuseStep 1218305 = 913729) B913729
theorem B1218323 : Blo 810345 1218323 := bstep (se 1 (by rfl) ⟨913742, by rfl⟩ : syracuseStep 1218323 = 1827485) B1827485
theorem B1218353 : Blo 810345 1218353 := bstep (se 2 (by rfl) ⟨456882, by rfl⟩ : syracuseStep 1218353 = 913765) B913765
theorem B1218371 : Blo 810345 1218371 := bstep (se 1 (by rfl) ⟨913778, by rfl⟩ : syracuseStep 1218371 = 1827557) B1827557
theorem B1218401 : Blo 810345 1218401 := bstep (se 2 (by rfl) ⟨456900, by rfl⟩ : syracuseStep 1218401 = 913801) B913801
theorem B1218419 : Blo 810345 1218419 := bstep (se 1 (by rfl) ⟨913814, by rfl⟩ : syracuseStep 1218419 = 1827629) B1827629
theorem B3086221 : Blo 810345 3086221 := bstep (se 3 (by rfl) ⟨578666, by rfl⟩ : syracuseStep 3086221 = 1157333) B1157333
theorem B1218449 : Blo 810345 1218449 := bstep (se 2 (by rfl) ⟨456918, by rfl⟩ : syracuseStep 1218449 = 913837) B913837
theorem B1218467 : Blo 810345 1218467 := bstep (se 1 (by rfl) ⟨913850, by rfl⟩ : syracuseStep 1218467 = 1827701) B1827701
theorem B5216177 : Blo 810345 5216177 := bstep (se 2 (by rfl) ⟨1956066, by rfl⟩ : syracuseStep 5216177 = 3912133) B3912133
theorem B1218497 : Blo 810345 1218497 := bstep (se 2 (by rfl) ⟨456936, by rfl⟩ : syracuseStep 1218497 = 913873) B913873
theorem B1218515 : Blo 810345 1218515 := bstep (se 1 (by rfl) ⟨913886, by rfl⟩ : syracuseStep 1218515 = 1827773) B1827773
theorem B1218545 : Blo 810345 1218545 := bstep (se 2 (by rfl) ⟨456954, by rfl⟩ : syracuseStep 1218545 = 913909) B913909
theorem B1218563 : Blo 810345 1218563 := bstep (se 1 (by rfl) ⟨913922, by rfl⟩ : syracuseStep 1218563 = 1827845) B1827845
theorem B1218593 : Blo 810345 1218593 := bstep (se 2 (by rfl) ⟨456972, by rfl⟩ : syracuseStep 1218593 = 913945) B913945
theorem B1218611 : Blo 810345 1218611 := bstep (se 1 (by rfl) ⟨913958, by rfl⟩ : syracuseStep 1218611 = 1827917) B1827917
theorem B1218641 : Blo 810345 1218641 := bstep (se 2 (by rfl) ⟨456990, by rfl⟩ : syracuseStep 1218641 = 913981) B913981
theorem B1218659 : Blo 810345 1218659 := bstep (se 1 (by rfl) ⟨913994, by rfl⟩ : syracuseStep 1218659 = 1827989) B1827989
theorem B1218689 : Blo 810345 1218689 := bstep (se 2 (by rfl) ⟨457008, by rfl⟩ : syracuseStep 1218689 = 914017) B914017
theorem B1218707 : Blo 810345 1218707 := bstep (se 1 (by rfl) ⟨914030, by rfl⟩ : syracuseStep 1218707 = 1828061) B1828061
theorem B1218737 : Blo 810345 1218737 := bstep (se 2 (by rfl) ⟨457026, by rfl⟩ : syracuseStep 1218737 = 914053) B914053
theorem B1218755 : Blo 810345 1218755 := bstep (se 1 (by rfl) ⟨914066, by rfl⟩ : syracuseStep 1218755 = 1828133) B1828133
theorem B1218785 : Blo 810345 1218785 := bstep (se 2 (by rfl) ⟨457044, by rfl⟩ : syracuseStep 1218785 = 914089) B914089
theorem B1218803 : Blo 810345 1218803 := bstep (se 1 (by rfl) ⟨914102, by rfl⟩ : syracuseStep 1218803 = 1828205) B1828205
theorem B1218833 : Blo 810345 1218833 := bstep (se 2 (by rfl) ⟨457062, by rfl⟩ : syracuseStep 1218833 = 914125) B914125
theorem B1218851 : Blo 810345 1218851 := bstep (se 1 (by rfl) ⟨914138, by rfl⟩ : syracuseStep 1218851 = 1828277) B1828277
theorem B1218881 : Blo 810345 1218881 := bstep (se 2 (by rfl) ⟨457080, by rfl⟩ : syracuseStep 1218881 = 914161) B914161
theorem B6166853 : Blo 810345 6166853 := bstep (se 4 (by rfl) ⟨578142, by rfl⟩ : syracuseStep 6166853 = 1156285) B1156285
theorem B1218899 : Blo 810345 1218899 := bstep (se 1 (by rfl) ⟨914174, by rfl⟩ : syracuseStep 1218899 = 1828349) B1828349
theorem B1218929 : Blo 810345 1218929 := bstep (se 2 (by rfl) ⟨457098, by rfl⟩ : syracuseStep 1218929 = 914197) B914197
theorem B1218947 : Blo 810345 1218947 := bstep (se 1 (by rfl) ⟨914210, by rfl⟩ : syracuseStep 1218947 = 1828421) B1828421
theorem B1218977 : Blo 810345 1218977 := bstep (se 2 (by rfl) ⟨457116, by rfl⟩ : syracuseStep 1218977 = 914233) B914233
theorem B1218995 : Blo 810345 1218995 := bstep (se 1 (by rfl) ⟨914246, by rfl⟩ : syracuseStep 1218995 = 1828493) B1828493
theorem B1219025 : Blo 810345 1219025 := bstep (se 2 (by rfl) ⟨457134, by rfl⟩ : syracuseStep 1219025 = 914269) B914269
theorem B1219043 : Blo 810345 1219043 := bstep (se 1 (by rfl) ⟨914282, by rfl⟩ : syracuseStep 1219043 = 1828565) B1828565
theorem B1219073 : Blo 810345 1219073 := bstep (se 2 (by rfl) ⟨457152, by rfl⟩ : syracuseStep 1219073 = 914305) B914305
theorem B1219091 : Blo 810345 1219091 := bstep (se 1 (by rfl) ⟨914318, by rfl⟩ : syracuseStep 1219091 = 1828637) B1828637
theorem B1219121 : Blo 810345 1219121 := bstep (se 2 (by rfl) ⟨457170, by rfl⟩ : syracuseStep 1219121 = 914341) B914341
theorem B1219139 : Blo 810345 1219139 := bstep (se 1 (by rfl) ⟨914354, by rfl⟩ : syracuseStep 1219139 = 1828709) B1828709
theorem B1219169 : Blo 810345 1219169 := bstep (se 2 (by rfl) ⟨457188, by rfl⟩ : syracuseStep 1219169 = 914377) B914377
theorem B1219187 : Blo 810345 1219187 := bstep (se 1 (by rfl) ⟨914390, by rfl⟩ : syracuseStep 1219187 = 1828781) B1828781
theorem B1219217 : Blo 810345 1219217 := bstep (se 2 (by rfl) ⟨457206, by rfl⟩ : syracuseStep 1219217 = 914413) B914413
theorem B1219235 : Blo 810345 1219235 := bstep (se 1 (by rfl) ⟨914426, by rfl⟩ : syracuseStep 1219235 = 1828853) B1828853
theorem B3087011 : Blo 810345 3087011 := bstep (se 1 (by rfl) ⟨2315258, by rfl⟩ : syracuseStep 3087011 = 4630517) B4630517
theorem B1219265 : Blo 810345 1219265 := bstep (se 2 (by rfl) ⟨457224, by rfl⟩ : syracuseStep 1219265 = 914449) B914449
theorem B1219283 : Blo 810345 1219283 := bstep (se 1 (by rfl) ⟨914462, by rfl⟩ : syracuseStep 1219283 = 1828925) B1828925
theorem B1219313 : Blo 810345 1219313 := bstep (se 2 (by rfl) ⟨457242, by rfl⟩ : syracuseStep 1219313 = 914485) B914485
theorem B1219331 : Blo 810345 1219331 := bstep (se 1 (by rfl) ⟨914498, by rfl⟩ : syracuseStep 1219331 = 1828997) B1828997
theorem B1219361 : Blo 810345 1219361 := bstep (se 2 (by rfl) ⟨457260, by rfl⟩ : syracuseStep 1219361 = 914521) B914521
theorem B1219379 : Blo 810345 1219379 := bstep (se 1 (by rfl) ⟨914534, by rfl⟩ : syracuseStep 1219379 = 1829069) B1829069
theorem B1219409 : Blo 810345 1219409 := bstep (se 2 (by rfl) ⟨457278, by rfl⟩ : syracuseStep 1219409 = 914557) B914557
theorem B1219427 : Blo 810345 1219427 := bstep (se 1 (by rfl) ⟨914570, by rfl⟩ : syracuseStep 1219427 = 1829141) B1829141
theorem B1219457 : Blo 810345 1219457 := bstep (se 2 (by rfl) ⟨457296, by rfl⟩ : syracuseStep 1219457 = 914593) B914593
theorem B1153939 : Blo 810345 1153939 := bstep (se 1 (by rfl) ⟨865454, by rfl⟩ : syracuseStep 1153939 = 1730909) B1730909
theorem B1219475 : Blo 810345 1219475 := bstep (se 1 (by rfl) ⟨914606, by rfl⟩ : syracuseStep 1219475 = 1829213) B1829213
theorem B1219505 : Blo 810345 1219505 := bstep (se 2 (by rfl) ⟨457314, by rfl⟩ : syracuseStep 1219505 = 914629) B914629
theorem B1219523 : Blo 810345 1219523 := bstep (se 1 (by rfl) ⟨914642, by rfl⟩ : syracuseStep 1219523 = 1829285) B1829285
theorem B1219553 : Blo 810345 1219553 := bstep (se 2 (by rfl) ⟨457332, by rfl⟩ : syracuseStep 1219553 = 914665) B914665
theorem B1219571 : Blo 810345 1219571 := bstep (se 1 (by rfl) ⟨914678, by rfl⟩ : syracuseStep 1219571 = 1829357) B1829357
theorem B1219601 : Blo 810345 1219601 := bstep (se 2 (by rfl) ⟨457350, by rfl⟩ : syracuseStep 1219601 = 914701) B914701
theorem B1219619 : Blo 810345 1219619 := bstep (se 1 (by rfl) ⟨914714, by rfl⟩ : syracuseStep 1219619 = 1829429) B1829429
theorem B1219649 : Blo 810345 1219649 := bstep (se 2 (by rfl) ⟨457368, by rfl⟩ : syracuseStep 1219649 = 914737) B914737
theorem B1219667 : Blo 810345 1219667 := bstep (se 1 (by rfl) ⟨914750, by rfl⟩ : syracuseStep 1219667 = 1829501) B1829501
theorem B1219697 : Blo 810345 1219697 := bstep (se 2 (by rfl) ⟨457386, by rfl⟩ : syracuseStep 1219697 = 914773) B914773
theorem B1219715 : Blo 810345 1219715 := bstep (se 1 (by rfl) ⟨914786, by rfl⟩ : syracuseStep 1219715 = 1829573) B1829573
theorem B1219745 : Blo 810345 1219745 := bstep (se 2 (by rfl) ⟨457404, by rfl⟩ : syracuseStep 1219745 = 914809) B914809
theorem B1219763 : Blo 810345 1219763 := bstep (se 1 (by rfl) ⟨914822, by rfl⟩ : syracuseStep 1219763 = 1829645) B1829645
theorem B1219793 : Blo 810345 1219793 := bstep (se 2 (by rfl) ⟨457422, by rfl⟩ : syracuseStep 1219793 = 914845) B914845
theorem B1219811 : Blo 810345 1219811 := bstep (se 1 (by rfl) ⟨914858, by rfl⟩ : syracuseStep 1219811 = 1829717) B1829717
theorem B1219841 : Blo 810345 1219841 := bstep (se 2 (by rfl) ⟨457440, by rfl⟩ : syracuseStep 1219841 = 914881) B914881
theorem B1219859 : Blo 810345 1219859 := bstep (se 1 (by rfl) ⟨914894, by rfl⟩ : syracuseStep 1219859 = 1829789) B1829789
theorem B4103459 : Blo 810345 4103459 := bstep (se 1 (by rfl) ⟨3077594, by rfl⟩ : syracuseStep 4103459 = 6155189) B6155189
theorem B3087665 : Blo 810345 3087665 := bstep (se 2 (by rfl) ⟨1157874, by rfl⟩ : syracuseStep 3087665 = 2315749) B2315749
theorem B1219889 : Blo 810345 1219889 := bstep (se 2 (by rfl) ⟨457458, by rfl⟩ : syracuseStep 1219889 = 914917) B914917
theorem B1219907 : Blo 810345 1219907 := bstep (se 1 (by rfl) ⟨914930, by rfl⟩ : syracuseStep 1219907 = 1829861) B1829861
theorem B1219937 : Blo 810345 1219937 := bstep (se 2 (by rfl) ⟨457476, by rfl⟩ : syracuseStep 1219937 = 914953) B914953
theorem B5217635 : Blo 810345 5217635 := bstep (se 1 (by rfl) ⟨3913226, by rfl⟩ : syracuseStep 5217635 = 7826453) B7826453
theorem B1154417 : Blo 810345 1154417 := bstep (se 2 (by rfl) ⟨432906, by rfl⟩ : syracuseStep 1154417 = 865813) B865813
theorem B1219955 : Blo 810345 1219955 := bstep (se 1 (by rfl) ⟨914966, by rfl⟩ : syracuseStep 1219955 = 1829933) B1829933
theorem B4627853 : Blo 810345 4627853 := bstep (se 3 (by rfl) ⟨867722, by rfl⟩ : syracuseStep 4627853 = 1735445) B1735445
theorem B1219985 : Blo 810345 1219985 := bstep (se 2 (by rfl) ⟨457494, by rfl⟩ : syracuseStep 1219985 = 914989) B914989
theorem B1220003 : Blo 810345 1220003 := bstep (se 1 (by rfl) ⟨915002, by rfl⟩ : syracuseStep 1220003 = 1830005) B1830005
theorem B1220033 : Blo 810345 1220033 := bstep (se 2 (by rfl) ⟨457512, by rfl⟩ : syracuseStep 1220033 = 915025) B915025
theorem B1220051 : Blo 810345 1220051 := bstep (se 1 (by rfl) ⟨915038, by rfl⟩ : syracuseStep 1220051 = 1830077) B1830077
theorem B1154531 : Blo 810345 1154531 := bstep (se 1 (by rfl) ⟨865898, by rfl⟩ : syracuseStep 1154531 = 1731797) B1731797
theorem B1220081 : Blo 810345 1220081 := bstep (se 2 (by rfl) ⟨457530, by rfl⟩ : syracuseStep 1220081 = 915061) B915061
theorem B1220099 : Blo 810345 1220099 := bstep (se 1 (by rfl) ⟨915074, by rfl⟩ : syracuseStep 1220099 = 1830149) B1830149
theorem B1220129 : Blo 810345 1220129 := bstep (se 2 (by rfl) ⟨457548, by rfl⟩ : syracuseStep 1220129 = 915097) B915097
theorem B1154611 : Blo 810345 1154611 := bstep (se 1 (by rfl) ⟨865958, by rfl⟩ : syracuseStep 1154611 = 1731917) B1731917
theorem B1220147 : Blo 810345 1220147 := bstep (se 1 (by rfl) ⟨915110, by rfl⟩ : syracuseStep 1220147 = 1830221) B1830221
theorem B1220177 : Blo 810345 1220177 := bstep (se 2 (by rfl) ⟨457566, by rfl⟩ : syracuseStep 1220177 = 915133) B915133
theorem B5283427 : Blo 810345 5283427 := bstep (se 1 (by rfl) ⟨3962570, by rfl⟩ : syracuseStep 5283427 = 7925141) B7925141
theorem B1220195 : Blo 810345 1220195 := bstep (se 1 (by rfl) ⟨915146, by rfl⟩ : syracuseStep 1220195 = 1830293) B1830293
theorem B2596465 : Blo 810345 2596465 := bstep (se 2 (by rfl) ⟨973674, by rfl⟩ : syracuseStep 2596465 = 1947349) B1947349
theorem B1220225 : Blo 810345 1220225 := bstep (se 2 (by rfl) ⟨457584, by rfl⟩ : syracuseStep 1220225 = 915169) B915169
theorem B1220243 : Blo 810345 1220243 := bstep (se 1 (by rfl) ⟨915182, by rfl⟩ : syracuseStep 1220243 = 1830365) B1830365
theorem B1220273 : Blo 810345 1220273 := bstep (se 2 (by rfl) ⟨457602, by rfl⟩ : syracuseStep 1220273 = 915205) B915205
theorem B1220291 : Blo 810345 1220291 := bstep (se 1 (by rfl) ⟨915218, by rfl⟩ : syracuseStep 1220291 = 1830437) B1830437
theorem B1220321 : Blo 810345 1220321 := bstep (se 2 (by rfl) ⟨457620, by rfl⟩ : syracuseStep 1220321 = 915241) B915241
theorem B1220339 : Blo 810345 1220339 := bstep (se 1 (by rfl) ⟨915254, by rfl⟩ : syracuseStep 1220339 = 1830509) B1830509
theorem B1220369 : Blo 810345 1220369 := bstep (se 2 (by rfl) ⟨457638, by rfl⟩ : syracuseStep 1220369 = 915277) B915277
theorem B1220387 : Blo 810345 1220387 := bstep (se 1 (by rfl) ⟨915290, by rfl⟩ : syracuseStep 1220387 = 1830581) B1830581
theorem B1220417 : Blo 810345 1220417 := bstep (se 2 (by rfl) ⟨457656, by rfl⟩ : syracuseStep 1220417 = 915313) B915313
theorem B1220435 : Blo 810345 1220435 := bstep (se 1 (by rfl) ⟨915326, by rfl⟩ : syracuseStep 1220435 = 1830653) B1830653
theorem B1220465 : Blo 810345 1220465 := bstep (se 2 (by rfl) ⟨457674, by rfl⟩ : syracuseStep 1220465 = 915349) B915349
theorem B1220483 : Blo 810345 1220483 := bstep (se 1 (by rfl) ⟨915362, by rfl⟩ : syracuseStep 1220483 = 1830725) B1830725
theorem B3710861 : Blo 810345 3710861 := bstep (se 3 (by rfl) ⟨695786, by rfl⟩ : syracuseStep 3710861 = 1391573) B1391573
theorem B1220513 : Blo 810345 1220513 := bstep (se 2 (by rfl) ⟨457692, by rfl⟩ : syracuseStep 1220513 = 915385) B915385
theorem B1220531 : Blo 810345 1220531 := bstep (se 1 (by rfl) ⟨915398, by rfl⟩ : syracuseStep 1220531 = 1830797) B1830797
theorem B5644237 : Blo 810345 5644237 := bstep (se 3 (by rfl) ⟨1058294, by rfl⟩ : syracuseStep 5644237 = 2116589) B2116589
theorem B1220561 : Blo 810345 1220561 := bstep (se 2 (by rfl) ⟨457710, by rfl⟩ : syracuseStep 1220561 = 915421) B915421
theorem B1220579 : Blo 810345 1220579 := bstep (se 1 (by rfl) ⟨915434, by rfl⟩ : syracuseStep 1220579 = 1830869) B1830869
theorem B1220609 : Blo 810345 1220609 := bstep (se 2 (by rfl) ⟨457728, by rfl⟩ : syracuseStep 1220609 = 915457) B915457
theorem B1220627 : Blo 810345 1220627 := bstep (se 1 (by rfl) ⟨915470, by rfl⟩ : syracuseStep 1220627 = 1830941) B1830941
theorem B1220657 : Blo 810345 1220657 := bstep (se 2 (by rfl) ⟨457746, by rfl⟩ : syracuseStep 1220657 = 915493) B915493
theorem B10395701 : Blo 810345 10395701 := bstep (se 5 (by rfl) ⟨487298, by rfl⟩ : syracuseStep 10395701 = 974597) B974597
theorem B1220675 : Blo 810345 1220675 := bstep (se 1 (by rfl) ⟨915506, by rfl⟩ : syracuseStep 1220675 = 1831013) B1831013
theorem B4104269 : Blo 810345 4104269 := bstep (se 3 (by rfl) ⟨769550, by rfl⟩ : syracuseStep 4104269 = 1539101) B1539101
theorem B1155169 : Blo 810345 1155169 := bstep (se 2 (by rfl) ⟨433188, by rfl⟩ : syracuseStep 1155169 = 866377) B866377
theorem B1220705 : Blo 810345 1220705 := bstep (se 2 (by rfl) ⟨457764, by rfl⟩ : syracuseStep 1220705 = 915529) B915529
theorem B2924657 : Blo 810345 2924657 := bstep (se 2 (by rfl) ⟨1096746, by rfl⟩ : syracuseStep 2924657 = 2193493) B2193493
theorem B1220723 : Blo 810345 1220723 := bstep (se 1 (by rfl) ⟨915542, by rfl⟩ : syracuseStep 1220723 = 1831085) B1831085
theorem B1220753 : Blo 810345 1220753 := bstep (se 2 (by rfl) ⟨457782, by rfl⟩ : syracuseStep 1220753 = 915565) B915565
theorem B4399267 : Blo 810345 4399267 := bstep (se 1 (by rfl) ⟨3299450, by rfl⟩ : syracuseStep 4399267 = 6598901) B6598901
theorem B1220771 : Blo 810345 1220771 := bstep (se 1 (by rfl) ⟨915578, by rfl⟩ : syracuseStep 1220771 = 1831157) B1831157
theorem B1220801 : Blo 810345 1220801 := bstep (se 2 (by rfl) ⟨457800, by rfl⟩ : syracuseStep 1220801 = 915601) B915601
theorem B1220819 : Blo 810345 1220819 := bstep (se 1 (by rfl) ⟨915614, by rfl⟩ : syracuseStep 1220819 = 1831229) B1831229
theorem B1220849 : Blo 810345 1220849 := bstep (se 2 (by rfl) ⟨457818, by rfl⟩ : syracuseStep 1220849 = 915637) B915637
theorem B1220867 : Blo 810345 1220867 := bstep (se 1 (by rfl) ⟨915650, by rfl⟩ : syracuseStep 1220867 = 1831301) B1831301
theorem B1220897 : Blo 810345 1220897 := bstep (se 2 (by rfl) ⟨457836, by rfl⟩ : syracuseStep 1220897 = 915673) B915673
theorem B4628785 : Blo 810345 4628785 := bstep (se 2 (by rfl) ⟨1735794, by rfl⟩ : syracuseStep 4628785 = 3471589) B3471589
theorem B1220915 : Blo 810345 1220915 := bstep (se 1 (by rfl) ⟨915686, by rfl⟩ : syracuseStep 1220915 = 1831373) B1831373
theorem B1220945 : Blo 810345 1220945 := bstep (se 2 (by rfl) ⟨457854, by rfl⟩ : syracuseStep 1220945 = 915709) B915709
theorem B1220963 : Blo 810345 1220963 := bstep (se 1 (by rfl) ⟨915722, by rfl⟩ : syracuseStep 1220963 = 1831445) B1831445
theorem B1220993 : Blo 810345 1220993 := bstep (se 2 (by rfl) ⟨457872, by rfl⟩ : syracuseStep 1220993 = 915745) B915745
theorem B1221011 : Blo 810345 1221011 := bstep (se 1 (by rfl) ⟨915758, by rfl⟩ : syracuseStep 1221011 = 1831517) B1831517
theorem B991651 : Blo 810345 991651 := bstep (se 1 (by rfl) ⟨743738, by rfl⟩ : syracuseStep 991651 = 1487477) B1487477
theorem B1221041 : Blo 810345 1221041 := bstep (se 2 (by rfl) ⟨457890, by rfl⟩ : syracuseStep 1221041 = 915781) B915781
theorem B1221059 : Blo 810345 1221059 := bstep (se 1 (by rfl) ⟨915794, by rfl⟩ : syracuseStep 1221059 = 1831589) B1831589
theorem B1221089 : Blo 810345 1221089 := bstep (se 2 (by rfl) ⟨457908, by rfl⟩ : syracuseStep 1221089 = 915817) B915817
theorem B1221107 : Blo 810345 1221107 := bstep (se 1 (by rfl) ⟨915830, by rfl⟩ : syracuseStep 1221107 = 1831661) B1831661
theorem B1221137 : Blo 810345 1221137 := bstep (se 2 (by rfl) ⟨457926, by rfl⟩ : syracuseStep 1221137 = 915853) B915853
theorem B1221155 : Blo 810345 1221155 := bstep (se 1 (by rfl) ⟨915866, by rfl⟩ : syracuseStep 1221155 = 1831733) B1831733
theorem B1221185 : Blo 810345 1221185 := bstep (se 2 (by rfl) ⟨457944, by rfl⟩ : syracuseStep 1221185 = 915889) B915889
theorem B1221203 : Blo 810345 1221203 := bstep (se 1 (by rfl) ⟨915902, by rfl⟩ : syracuseStep 1221203 = 1831805) B1831805
theorem B1221233 : Blo 810345 1221233 := bstep (se 2 (by rfl) ⟨457962, by rfl⟩ : syracuseStep 1221233 = 915925) B915925
theorem B1221251 : Blo 810345 1221251 := bstep (se 1 (by rfl) ⟨915938, by rfl⟩ : syracuseStep 1221251 = 1831877) B1831877
theorem B1221281 : Blo 810345 1221281 := bstep (se 2 (by rfl) ⟨457980, by rfl⟩ : syracuseStep 1221281 = 915961) B915961
theorem B1221299 : Blo 810345 1221299 := bstep (se 1 (by rfl) ⟨915974, by rfl⟩ : syracuseStep 1221299 = 1831949) B1831949
theorem B1221329 : Blo 810345 1221329 := bstep (se 2 (by rfl) ⟨457998, by rfl⟩ : syracuseStep 1221329 = 915997) B915997
theorem B3089123 : Blo 810345 3089123 := bstep (se 1 (by rfl) ⟨2316842, by rfl⟩ : syracuseStep 3089123 = 4633685) B4633685
theorem B1221347 : Blo 810345 1221347 := bstep (se 1 (by rfl) ⟨916010, by rfl⟩ : syracuseStep 1221347 = 1832021) B1832021
theorem B3089137 : Blo 810345 3089137 := bstep (se 2 (by rfl) ⟨1158426, by rfl⟩ : syracuseStep 3089137 = 2316853) B2316853
theorem B1221377 : Blo 810345 1221377 := bstep (se 2 (by rfl) ⟨458016, by rfl⟩ : syracuseStep 1221377 = 916033) B916033
theorem B1221395 : Blo 810345 1221395 := bstep (se 1 (by rfl) ⟨916046, by rfl⟩ : syracuseStep 1221395 = 1832093) B1832093
theorem B1155875 : Blo 810345 1155875 := bstep (se 1 (by rfl) ⟨866906, by rfl⟩ : syracuseStep 1155875 = 1733813) B1733813
theorem B1221425 : Blo 810345 1221425 := bstep (se 2 (by rfl) ⟨458034, by rfl⟩ : syracuseStep 1221425 = 916069) B916069
theorem B1221443 : Blo 810345 1221443 := bstep (se 1 (by rfl) ⟨916082, by rfl⟩ : syracuseStep 1221443 = 1832165) B1832165
theorem B1221473 : Blo 810345 1221473 := bstep (se 2 (by rfl) ⟨458052, by rfl⟩ : syracuseStep 1221473 = 916105) B916105
theorem B1221491 : Blo 810345 1221491 := bstep (se 1 (by rfl) ⟨916118, by rfl⟩ : syracuseStep 1221491 = 1832237) B1832237
theorem B1647683 : Blo 810345 1647683 := bstep (se 1 (by rfl) ⟨1235762, by rfl⟩ : syracuseStep 1647683 = 2471525) B2471525
theorem B1156513 : Blo 810345 1156513 := bstep (se 2 (by rfl) ⟨433692, by rfl⟩ : syracuseStep 1156513 = 867385) B867385
theorem B1156627 : Blo 810345 1156627 := bstep (se 1 (by rfl) ⟨867470, by rfl⟩ : syracuseStep 1156627 = 1734941) B1734941
theorem B4630243 : Blo 810345 4630243 := bstep (se 1 (by rfl) ⟨3472682, by rfl⟩ : syracuseStep 4630243 = 6945365) B6945365
theorem B1025779 : Blo 810345 1025779 := bstep (se 1 (by rfl) ⟨769334, by rfl⟩ : syracuseStep 1025779 = 1538669) B1538669
theorem B1025875 : Blo 810345 1025875 := bstep (se 1 (by rfl) ⟨769406, by rfl⟩ : syracuseStep 1025875 = 1538813) B1538813
theorem B1484867 : Blo 810345 1484867 := bstep (se 1 (by rfl) ⟨1113650, by rfl⟩ : syracuseStep 1484867 = 2227301) B2227301
theorem B1648721 : Blo 810345 1648721 := bstep (se 2 (by rfl) ⟨618270, by rfl⟩ : syracuseStep 1648721 = 1236541) B1236541
theorem B3090595 : Blo 810345 3090595 := bstep (se 1 (by rfl) ⟨2317946, by rfl⟩ : syracuseStep 3090595 = 4635893) B4635893
theorem B7416035 : Blo 810345 7416035 := bstep (se 1 (by rfl) ⟨5562026, by rfl⟩ : syracuseStep 7416035 = 11124053) B11124053
theorem B4630769 : Blo 810345 4630769 := bstep (se 2 (by rfl) ⟨1736538, by rfl⟩ : syracuseStep 4630769 = 3473077) B3473077
theorem B1026371 : Blo 810345 1026371 := bstep (se 1 (by rfl) ⟨769778, by rfl⟩ : syracuseStep 1026371 = 1539557) B1539557
theorem B6596963 : Blo 810345 6596963 := bstep (se 1 (by rfl) ⟨4947722, by rfl⟩ : syracuseStep 6596963 = 9895445) B9895445
theorem B1878563 : Blo 810345 1878563 := bstep (se 1 (by rfl) ⟨1408922, by rfl⟩ : syracuseStep 1878563 = 2817845) B2817845
theorem B1387139 : Blo 810345 1387139 := bstep (se 1 (by rfl) ⟨1040354, by rfl⟩ : syracuseStep 1387139 = 2080709) B2080709
theorem B2468483 : Blo 810345 2468483 := bstep (se 1 (by rfl) ⟨1851362, by rfl⟩ : syracuseStep 2468483 = 3702725) B3702725
theorem B1157971 : Blo 810345 1157971 := bstep (se 1 (by rfl) ⟨868478, by rfl⟩ : syracuseStep 1157971 = 1736957) B1736957
theorem B4107185 : Blo 810345 4107185 := bstep (se 2 (by rfl) ⟨1540194, by rfl⟩ : syracuseStep 4107185 = 3080389) B3080389
theorem B1387523 : Blo 810345 1387523 := bstep (se 1 (by rfl) ⟨1040642, by rfl⟩ : syracuseStep 1387523 = 2081285) B2081285
theorem B1027075 : Blo 810345 1027075 := bstep (se 1 (by rfl) ⟨770306, by rfl⟩ : syracuseStep 1027075 = 1540613) B1540613
theorem B1027171 : Blo 810345 1027171 := bstep (se 1 (by rfl) ⟨770378, by rfl⟩ : syracuseStep 1027171 = 1540757) B1540757
theorem B1387633 : Blo 810345 1387633 := bstep (se 2 (by rfl) ⟨520362, by rfl⟩ : syracuseStep 1387633 = 1040725) B1040725
theorem B1387811 : Blo 810345 1387811 := bstep (se 1 (by rfl) ⟨1040858, by rfl⟩ : syracuseStep 1387811 = 2081717) B2081717
theorem B3911075 : Blo 810345 3911075 := bstep (se 1 (by rfl) ⟨2933306, by rfl⟩ : syracuseStep 3911075 = 5866613) B5866613
theorem B3517987 : Blo 810345 3517987 := bstep (se 1 (by rfl) ⟨2638490, by rfl⟩ : syracuseStep 3517987 = 5276981) B5276981
theorem B1027667 : Blo 810345 1027667 := bstep (se 1 (by rfl) ⟨770750, by rfl⟩ : syracuseStep 1027667 = 1541501) B1541501
theorem B3911267 : Blo 810345 3911267 := bstep (se 1 (by rfl) ⟨2933450, by rfl⟩ : syracuseStep 3911267 = 5866901) B5866901
theorem B4632227 : Blo 810345 4632227 := bstep (se 1 (by rfl) ⟨3474170, by rfl⟩ : syracuseStep 4632227 = 6948341) B6948341
theorem B6926093 : Blo 810345 6926093 := bstep (se 3 (by rfl) ⟨1298642, by rfl⟩ : syracuseStep 6926093 = 2597285) B2597285
theorem B2404163 : Blo 810345 2404163 := bstep (se 1 (by rfl) ⟨1803122, by rfl⟩ : syracuseStep 2404163 = 3606245) B3606245
theorem B2600849 : Blo 810345 2600849 := bstep (se 2 (by rfl) ⟨975318, by rfl⟩ : syracuseStep 2600849 = 1950637) B1950637
theorem B1159105 : Blo 810345 1159105 := bstep (se 2 (by rfl) ⟨434664, by rfl⟩ : syracuseStep 1159105 = 869329) B869329
theorem B6172685 : Blo 810345 6172685 := bstep (se 3 (by rfl) ⟨1157378, by rfl⟩ : syracuseStep 6172685 = 2314757) B2314757
theorem B21082133 : Blo 810345 21082133 := bstep (se 6 (by rfl) ⟨494112, by rfl⟩ : syracuseStep 21082133 = 988225) B988225
theorem B1159201 : Blo 810345 1159201 := bstep (se 2 (by rfl) ⟨434700, by rfl⟩ : syracuseStep 1159201 = 869401) B869401
theorem B2633969 : Blo 810345 2633969 := bstep (se 2 (by rfl) ⟨987738, by rfl⟩ : syracuseStep 2633969 = 1975477) B1975477
theorem B3911921 : Blo 810345 3911921 := bstep (se 2 (by rfl) ⟨1466970, by rfl⟩ : syracuseStep 3911921 = 2933941) B2933941
theorem B1028371 : Blo 810345 1028371 := bstep (se 1 (by rfl) ⟨771278, by rfl⟩ : syracuseStep 1028371 = 1542557) B1542557
theorem B4108643 : Blo 810345 4108643 := bstep (se 1 (by rfl) ⟨3081482, by rfl⟩ : syracuseStep 4108643 = 6162965) B6162965
theorem B1028467 : Blo 810345 1028467 := bstep (se 1 (by rfl) ⟨771350, by rfl⟩ : syracuseStep 1028467 = 1542701) B1542701
theorem B1388947 : Blo 810345 1388947 := bstep (se 1 (by rfl) ⟨1041710, by rfl⟩ : syracuseStep 1388947 = 2083421) B2083421
theorem B44970773 : Blo 810345 44970773 := bstep (se 6 (by rfl) ⟨1054002, by rfl⟩ : syracuseStep 44970773 = 2108005) B2108005
theorem B1028963 : Blo 810345 1028963 := bstep (se 1 (by rfl) ⟨771722, by rfl⟩ : syracuseStep 1028963 = 1543445) B1543445
theorem B1586161 : Blo 810345 1586161 := bstep (se 2 (by rfl) ⟨594810, by rfl⟩ : syracuseStep 1586161 = 1189621) B1189621
theorem B1389617 : Blo 810345 1389617 := bstep (se 2 (by rfl) ⟨521106, by rfl⟩ : syracuseStep 1389617 = 1042213) B1042213
theorem B4109453 : Blo 810345 4109453 := bstep (se 3 (by rfl) ⟨770522, by rfl⟩ : syracuseStep 4109453 = 1541045) B1541045
theorem B2634947 : Blo 810345 2634947 := bstep (se 1 (by rfl) ⟨1976210, by rfl⟩ : syracuseStep 2634947 = 3952421) B3952421
theorem B1357249 : Blo 810345 1357249 := bstep (se 2 (by rfl) ⟨508968, by rfl⟩ : syracuseStep 1357249 = 1017937) B1017937
theorem B2471377 : Blo 810345 2471377 := bstep (se 2 (by rfl) ⟨926766, by rfl⟩ : syracuseStep 2471377 = 1853533) B1853533
theorem B4634117 : Blo 810345 4634117 := bstep (se 4 (by rfl) ⟨434448, by rfl⟩ : syracuseStep 4634117 = 868897) B868897
theorem B1029667 : Blo 810345 1029667 := bstep (se 1 (by rfl) ⟨772250, by rfl⟩ : syracuseStep 1029667 = 1544501) B1544501
theorem B35599985 : Blo 810345 35599985 := bstep (se 2 (by rfl) ⟨13349994, by rfl⟩ : syracuseStep 35599985 = 26699989) B26699989
theorem B1029763 : Blo 810345 1029763 := bstep (se 1 (by rfl) ⟨772322, by rfl⟩ : syracuseStep 1029763 = 1544645) B1544645
theorem B866035 : Blo 810345 866035 := bstep (se 1 (by rfl) ⟨649526, by rfl⟩ : syracuseStep 866035 = 1299053) B1299053
theorem B2602925 : Blo 810345 2602925 := bstep (se 3 (by rfl) ⟨488048, by rfl⟩ : syracuseStep 2602925 = 976097) B976097
theorem B1095617 : Blo 810345 1095617 := bstep (se 2 (by rfl) ⟨410856, by rfl⟩ : syracuseStep 1095617 = 821713) B821713
theorem B1095665 : Blo 810345 1095665 := bstep (se 2 (by rfl) ⟨410874, by rfl⟩ : syracuseStep 1095665 = 821749) B821749
theorem B1030259 : Blo 810345 1030259 := bstep (se 1 (by rfl) ⟨772694, by rfl⟩ : syracuseStep 1030259 = 1545389) B1545389
theorem B16890083 : Blo 810345 16890083 := bstep (se 1 (by rfl) ⟨12667562, by rfl⟩ : syracuseStep 16890083 = 25335125) B25335125
theorem B2308333 : Blo 810345 2308333 := bstep (se 3 (by rfl) ⟨432812, by rfl⟩ : syracuseStep 2308333 = 865625) B865625
theorem B2308493 : Blo 810345 2308493 := bstep (se 3 (by rfl) ⟨432842, by rfl⟩ : syracuseStep 2308493 = 865685) B865685
theorem B2308675 : Blo 810345 2308675 := bstep (se 1 (by rfl) ⟨1731506, by rfl⟩ : syracuseStep 2308675 = 3463013) B3463013
theorem B2079313 : Blo 810345 2079313 := bstep (se 2 (by rfl) ⟨779742, by rfl⟩ : syracuseStep 2079313 = 1559485) B1559485
theorem B1391185 : Blo 810345 1391185 := bstep (se 2 (by rfl) ⟨521694, by rfl⟩ : syracuseStep 1391185 = 1043389) B1043389
theorem B2472643 : Blo 810345 2472643 := bstep (se 1 (by rfl) ⟨1854482, by rfl⟩ : syracuseStep 2472643 = 3708965) B3708965
theorem B1948387 : Blo 810345 1948387 := bstep (se 1 (by rfl) ⟨1461290, by rfl⟩ : syracuseStep 1948387 = 2922581) B2922581
theorem B867043 : Blo 810345 867043 := bstep (se 1 (by rfl) ⟨650282, by rfl⟩ : syracuseStep 867043 = 1300565) B1300565
theorem B2931491 : Blo 810345 2931491 := bstep (se 1 (by rfl) ⟨2198618, by rfl⟩ : syracuseStep 2931491 = 4397237) B4397237
theorem B2603821 : Blo 810345 2603821 := bstep (se 3 (by rfl) ⟨488216, by rfl⟩ : syracuseStep 2603821 = 976433) B976433
theorem B6175601 : Blo 810345 6175601 := bstep (se 2 (by rfl) ⟨2315850, by rfl⟩ : syracuseStep 6175601 = 4631701) B4631701
theorem B10402829 : Blo 810345 10402829 := bstep (se 3 (by rfl) ⟨1950530, by rfl⟩ : syracuseStep 10402829 = 3901061) B3901061
theorem B2735153 : Blo 810345 2735153 := bstep (se 2 (by rfl) ⟨1025682, by rfl⟩ : syracuseStep 2735153 = 2051365) B2051365
theorem B2964593 : Blo 810345 2964593 := bstep (se 2 (by rfl) ⟨1111722, by rfl⟩ : syracuseStep 2964593 = 2223445) B2223445
theorem B1096915 : Blo 810345 1096915 := bstep (se 1 (by rfl) ⟨822686, by rfl⟩ : syracuseStep 1096915 = 1645373) B1645373
theorem B2079971 : Blo 810345 2079971 := bstep (se 1 (by rfl) ⟨1559978, by rfl⟩ : syracuseStep 2079971 = 3119957) B3119957
theorem B4930865 : Blo 810345 4930865 := bstep (se 2 (by rfl) ⟨1849074, by rfl⟩ : syracuseStep 4930865 = 3698149) B3698149
theorem B867667 : Blo 810345 867667 := bstep (se 1 (by rfl) ⟨650750, by rfl⟩ : syracuseStep 867667 = 1301501) B1301501
theorem B2113091 : Blo 810345 2113091 := bstep (se 1 (by rfl) ⟨1584818, by rfl⟩ : syracuseStep 2113091 = 3169637) B3169637
theorem B2735693 : Blo 810345 2735693 := bstep (se 3 (by rfl) ⟨512942, by rfl⟩ : syracuseStep 2735693 = 1025885) B1025885
theorem B2735747 : Blo 810345 2735747 := bstep (se 1 (by rfl) ⟨2051810, by rfl⟩ : syracuseStep 2735747 = 4103621) B4103621
theorem B2604707 : Blo 810345 2604707 := bstep (se 1 (by rfl) ⟨1953530, by rfl⟩ : syracuseStep 2604707 = 3907061) B3907061
theorem B13188977 : Blo 810345 13188977 := bstep (se 2 (by rfl) ⟨4945866, by rfl⟩ : syracuseStep 13188977 = 9891733) B9891733
theorem B2736017 : Blo 810345 2736017 := bstep (se 2 (by rfl) ⟨1026006, by rfl⟩ : syracuseStep 2736017 = 2052013) B2052013
theorem B2310065 : Blo 810345 2310065 := bstep (se 2 (by rfl) ⟨866274, by rfl⟩ : syracuseStep 2310065 = 1732549) B1732549
theorem B1949617 : Blo 810345 1949617 := bstep (se 2 (by rfl) ⟨731106, by rfl⟩ : syracuseStep 1949617 = 1462213) B1462213
theorem B4112369 : Blo 810345 4112369 := bstep (se 2 (by rfl) ⟨1542138, by rfl⟩ : syracuseStep 4112369 = 3084277) B3084277
theorem B2638001 : Blo 810345 2638001 := bstep (se 2 (by rfl) ⟨989250, by rfl⟩ : syracuseStep 2638001 = 1978501) B1978501
theorem B2736557 : Blo 810345 2736557 := bstep (se 3 (by rfl) ⟨513104, by rfl⟩ : syracuseStep 2736557 = 1026209) B1026209
theorem B2736611 : Blo 810345 2736611 := bstep (se 1 (by rfl) ⟨2052458, by rfl⟩ : syracuseStep 2736611 = 4104917) B4104917
theorem B2736881 : Blo 810345 2736881 := bstep (se 2 (by rfl) ⟨1026330, by rfl⟩ : syracuseStep 2736881 = 2052661) B2052661
theorem B2081521 : Blo 810345 2081521 := bstep (se 2 (by rfl) ⟨780570, by rfl⟩ : syracuseStep 2081521 = 1561141) B1561141
theorem B2081603 : Blo 810345 2081603 := bstep (se 1 (by rfl) ⟨1561202, by rfl⟩ : syracuseStep 2081603 = 3122405) B3122405
theorem B2311021 : Blo 810345 2311021 := bstep (se 3 (by rfl) ⟨433316, by rfl⟩ : syracuseStep 2311021 = 866633) B866633
theorem B9290821 : Blo 810345 9290821 := bstep (se 4 (by rfl) ⟨871014, by rfl⟩ : syracuseStep 9290821 = 1742029) B1742029
theorem B2311249 : Blo 810345 2311249 := bstep (se 2 (by rfl) ⟨866718, by rfl⟩ : syracuseStep 2311249 = 1733437) B1733437
theorem B869555 : Blo 810345 869555 := bstep (se 1 (by rfl) ⟨652166, by rfl⟩ : syracuseStep 869555 = 1304333) B1304333
theorem B2311409 : Blo 810345 2311409 := bstep (se 2 (by rfl) ⟨866778, by rfl⟩ : syracuseStep 2311409 = 1733557) B1733557
theorem B2737421 : Blo 810345 2737421 := bstep (se 3 (by rfl) ⟨513266, by rfl⟩ : syracuseStep 2737421 = 1026533) B1026533
theorem B2737475 : Blo 810345 2737475 := bstep (se 1 (by rfl) ⟨2053106, by rfl⟩ : syracuseStep 2737475 = 4106213) B4106213
theorem B2311523 : Blo 810345 2311523 := bstep (se 1 (by rfl) ⟨1733642, by rfl⟩ : syracuseStep 2311523 = 3467285) B3467285
theorem B4113827 : Blo 810345 4113827 := bstep (se 1 (by rfl) ⟨3085370, by rfl⟩ : syracuseStep 4113827 = 6170741) B6170741
theorem B2737745 : Blo 810345 2737745 := bstep (se 2 (by rfl) ⟨1026654, by rfl⟩ : syracuseStep 2737745 = 2053309) B2053309
theorem B2606897 : Blo 810345 2606897 := bstep (se 2 (by rfl) ⟨977586, by rfl⟩ : syracuseStep 2606897 = 1955173) B1955173
theorem B2934605 : Blo 810345 2934605 := bstep (se 3 (by rfl) ⟨550238, by rfl⟩ : syracuseStep 2934605 = 1100477) B1100477
theorem B2607025 : Blo 810345 2607025 := bstep (se 2 (by rfl) ⟨977634, by rfl⟩ : syracuseStep 2607025 = 1955269) B1955269
theorem B2639843 : Blo 810345 2639843 := bstep (se 1 (by rfl) ⟨1979882, by rfl⟩ : syracuseStep 2639843 = 3959765) B3959765
theorem B19810325 : Blo 810345 19810325 := bstep (se 6 (by rfl) ⟨464304, by rfl⟩ : syracuseStep 19810325 = 928609) B928609
theorem B2738285 : Blo 810345 2738285 := bstep (se 3 (by rfl) ⟨513428, by rfl⟩ : syracuseStep 2738285 = 1026857) B1026857
theorem B2738339 : Blo 810345 2738339 := bstep (se 1 (by rfl) ⟨2053754, by rfl⟩ : syracuseStep 2738339 = 4107509) B4107509
theorem B2607281 : Blo 810345 2607281 := bstep (se 2 (by rfl) ⟨977730, by rfl⟩ : syracuseStep 2607281 = 1955461) B1955461
theorem B4114637 : Blo 810345 4114637 := bstep (se 3 (by rfl) ⟨771494, by rfl⟩ : syracuseStep 4114637 = 1542989) B1542989
theorem B3131597 : Blo 810345 3131597 := bstep (se 3 (by rfl) ⟨587174, by rfl⟩ : syracuseStep 3131597 = 1174349) B1174349
theorem B2312525 : Blo 810345 2312525 := bstep (se 3 (by rfl) ⟨433598, by rfl⟩ : syracuseStep 2312525 = 867197) B867197
theorem B2738609 : Blo 810345 2738609 := bstep (se 2 (by rfl) ⟨1026978, by rfl⟩ : syracuseStep 2738609 = 2053957) B2053957
theorem B2312707 : Blo 810345 2312707 := bstep (se 1 (by rfl) ⟨1734530, by rfl⟩ : syracuseStep 2312707 = 3469061) B3469061
theorem B2312867 : Blo 810345 2312867 := bstep (se 1 (by rfl) ⟨1734650, by rfl⟩ : syracuseStep 2312867 = 3469301) B3469301
theorem B1461169 : Blo 810345 1461169 := bstep (se 2 (by rfl) ⟨547938, by rfl⟩ : syracuseStep 1461169 = 1095877) B1095877
theorem B2739149 : Blo 810345 2739149 := bstep (se 3 (by rfl) ⟨513590, by rfl⟩ : syracuseStep 2739149 = 1027181) B1027181
theorem B1461233 : Blo 810345 1461233 := bstep (se 2 (by rfl) ⟨547962, by rfl⟩ : syracuseStep 1461233 = 1095925) B1095925
theorem B2739203 : Blo 810345 2739203 := bstep (se 1 (by rfl) ⟨2054402, by rfl⟩ : syracuseStep 2739203 = 4108805) B4108805
theorem B2051203 : Blo 810345 2051203 := bstep (se 1 (by rfl) ⟨1538402, by rfl⟩ : syracuseStep 2051203 = 3076805) B3076805
theorem B9358577 : Blo 810345 9358577 := bstep (se 2 (by rfl) ⟨3509466, by rfl⟩ : syracuseStep 9358577 = 7018933) B7018933
theorem B2051345 : Blo 810345 2051345 := bstep (se 2 (by rfl) ⟨769254, by rfl⟩ : syracuseStep 2051345 = 1538509) B1538509
theorem B1461521 : Blo 810345 1461521 := bstep (se 2 (by rfl) ⟨548070, by rfl⟩ : syracuseStep 1461521 = 1096141) B1096141
theorem B2739473 : Blo 810345 2739473 := bstep (se 2 (by rfl) ⟨1027302, by rfl⟩ : syracuseStep 2739473 = 2054605) B2054605
theorem B1854883 : Blo 810345 1854883 := bstep (se 1 (by rfl) ⟨1391162, by rfl⟩ : syracuseStep 1854883 = 2782325) B2782325
theorem B6934157 : Blo 810345 6934157 := bstep (se 3 (by rfl) ⟨1300154, by rfl⟩ : syracuseStep 6934157 = 2600309) B2600309
theorem B1298099 : Blo 810345 1298099 := bstep (se 1 (by rfl) ⟨973574, by rfl⟩ : syracuseStep 1298099 = 1947149) B1947149
theorem B2313937 : Blo 810345 2313937 := bstep (se 2 (by rfl) ⟨867726, by rfl⟩ : syracuseStep 2313937 = 1735453) B1735453
theorem B2740013 : Blo 810345 2740013 := bstep (se 3 (by rfl) ⟨513752, by rfl⟩ : syracuseStep 2740013 = 1027505) B1027505
theorem B2740067 : Blo 810345 2740067 := bstep (se 1 (by rfl) ⟨2055050, by rfl⟩ : syracuseStep 2740067 = 4110101) B4110101
theorem B1953713 : Blo 810345 1953713 := bstep (se 2 (by rfl) ⟨732642, by rfl⟩ : syracuseStep 1953713 = 1465285) B1465285
theorem B2740337 : Blo 810345 2740337 := bstep (se 2 (by rfl) ⟨1027626, by rfl⟩ : syracuseStep 2740337 = 2055253) B2055253
theorem B1855715 : Blo 810345 1855715 := bstep (se 1 (by rfl) ⟨1391786, by rfl⟩ : syracuseStep 1855715 = 2783573) B2783573
theorem B2052337 : Blo 810345 2052337 := bstep (se 2 (by rfl) ⟨769626, by rfl⟩ : syracuseStep 2052337 = 1539253) B1539253
theorem B1954097 : Blo 810345 1954097 := bstep (se 2 (by rfl) ⟨732786, by rfl⟩ : syracuseStep 1954097 = 1465573) B1465573
theorem B1298771 : Blo 810345 1298771 := bstep (se 1 (by rfl) ⟨974078, by rfl⟩ : syracuseStep 1298771 = 1948157) B1948157
theorem B3297635 : Blo 810345 3297635 := bstep (se 1 (by rfl) ⟨2473226, by rfl⟩ : syracuseStep 3297635 = 4946453) B4946453
theorem B2052611 : Blo 810345 2052611 := bstep (se 1 (by rfl) ⟨1539458, by rfl⟩ : syracuseStep 2052611 = 3078917) B3078917
theorem B1954307 : Blo 810345 1954307 := bstep (se 1 (by rfl) ⟨1465730, by rfl⟩ : syracuseStep 1954307 = 2931461) B2931461
theorem B1823345 : Blo 810345 1823345 := bstep (se 2 (by rfl) ⟨683754, by rfl⟩ : syracuseStep 1823345 = 1367509) B1367509
theorem B1299073 : Blo 810345 1299073 := bstep (se 2 (by rfl) ⟨487152, by rfl⟩ : syracuseStep 1299073 = 974305) B974305
theorem B1823363 : Blo 810345 1823363 := bstep (se 1 (by rfl) ⟨1367522, by rfl⟩ : syracuseStep 1823363 = 2735045) B2735045
theorem B2740877 : Blo 810345 2740877 := bstep (se 3 (by rfl) ⟨513914, by rfl⟩ : syracuseStep 2740877 = 1027829) B1027829
theorem B2052803 : Blo 810345 2052803 := bstep (se 1 (by rfl) ⟨1539602, by rfl⟩ : syracuseStep 2052803 = 3079205) B3079205
theorem B2740931 : Blo 810345 2740931 := bstep (se 1 (by rfl) ⟨2055698, by rfl⟩ : syracuseStep 2740931 = 4111397) B4111397
theorem B15586019 : Blo 810345 15586019 := bstep (se 1 (by rfl) ⟨11689514, by rfl⟩ : syracuseStep 15586019 = 23379029) B23379029
theorem B1299283 : Blo 810345 1299283 := bstep (se 1 (by rfl) ⟨974462, by rfl⟩ : syracuseStep 1299283 = 1948925) B1948925
theorem B1299329 : Blo 810345 1299329 := bstep (se 2 (by rfl) ⟨487248, by rfl⟩ : syracuseStep 1299329 = 974497) B974497
theorem B1823633 : Blo 810345 1823633 := bstep (se 2 (by rfl) ⟨683862, by rfl⟩ : syracuseStep 1823633 = 1367725) B1367725
theorem B1823651 : Blo 810345 1823651 := bstep (se 1 (by rfl) ⟨1367738, by rfl⟩ : syracuseStep 1823651 = 2735477) B2735477
theorem B2315213 : Blo 810345 2315213 := bstep (se 3 (by rfl) ⟨434102, by rfl⟩ : syracuseStep 2315213 = 868205) B868205
theorem B2741201 : Blo 810345 2741201 := bstep (se 2 (by rfl) ⟨1027950, by rfl⟩ : syracuseStep 2741201 = 2055901) B2055901
theorem B4510691 : Blo 810345 4510691 := bstep (se 1 (by rfl) ⟨3383018, by rfl⟩ : syracuseStep 4510691 = 6766037) B6766037
theorem B4117553 : Blo 810345 4117553 := bstep (se 2 (by rfl) ⟨1544082, by rfl⟩ : syracuseStep 4117553 = 3088165) B3088165
theorem B2315395 : Blo 810345 2315395 := bstep (se 1 (by rfl) ⟨1736546, by rfl⟩ : syracuseStep 2315395 = 3473093) B3473093
theorem B1823921 : Blo 810345 1823921 := bstep (se 2 (by rfl) ⟨683970, by rfl⟩ : syracuseStep 1823921 = 1367941) B1367941
theorem B2315441 : Blo 810345 2315441 := bstep (se 2 (by rfl) ⟨868290, by rfl⟩ : syracuseStep 2315441 = 1736581) B1736581
theorem B1823939 : Blo 810345 1823939 := bstep (se 1 (by rfl) ⟨1367954, by rfl⟩ : syracuseStep 1823939 = 2735909) B2735909
theorem B1955153 : Blo 810345 1955153 := bstep (se 2 (by rfl) ⟨733182, by rfl⟩ : syracuseStep 1955153 = 1466365) B1466365
theorem B1234273 : Blo 810345 1234273 := bstep (se 2 (by rfl) ⟨462852, by rfl⟩ : syracuseStep 1234273 = 925705) B925705
theorem B1824209 : Blo 810345 1824209 := bstep (se 2 (by rfl) ⟨684078, by rfl⟩ : syracuseStep 1824209 = 1368157) B1368157
theorem B1824227 : Blo 810345 1824227 := bstep (se 1 (by rfl) ⟨1368170, by rfl⟩ : syracuseStep 1824227 = 2736341) B2736341
theorem B2741741 : Blo 810345 2741741 := bstep (se 3 (by rfl) ⟨514076, by rfl⟩ : syracuseStep 2741741 = 1028153) B1028153
theorem B1955345 : Blo 810345 1955345 := bstep (se 2 (by rfl) ⟨733254, by rfl⟩ : syracuseStep 1955345 = 1466509) B1466509
theorem B2741795 : Blo 810345 2741795 := bstep (se 1 (by rfl) ⟨2056346, by rfl⟩ : syracuseStep 2741795 = 4112693) B4112693
theorem B2053745 : Blo 810345 2053745 := bstep (se 2 (by rfl) ⟨770154, by rfl⟩ : syracuseStep 2053745 = 1540309) B1540309
theorem B2053795 : Blo 810345 2053795 := bstep (se 1 (by rfl) ⟨1540346, by rfl⟩ : syracuseStep 2053795 = 3080693) B3080693
theorem B1824497 : Blo 810345 1824497 := bstep (se 2 (by rfl) ⟨684186, by rfl⟩ : syracuseStep 1824497 = 1368373) B1368373
theorem B1824515 : Blo 810345 1824515 := bstep (se 1 (by rfl) ⟨1368386, by rfl⟩ : syracuseStep 1824515 = 2736773) B2736773
theorem B2053937 : Blo 810345 2053937 := bstep (se 2 (by rfl) ⟨770226, by rfl⟩ : syracuseStep 2053937 = 1540453) B1540453
theorem B2742065 : Blo 810345 2742065 := bstep (se 2 (by rfl) ⟨1028274, by rfl⟩ : syracuseStep 2742065 = 2056549) B2056549
theorem B1824785 : Blo 810345 1824785 := bstep (se 2 (by rfl) ⟨684294, by rfl⟩ : syracuseStep 1824785 = 1368589) B1368589
theorem B1824803 : Blo 810345 1824803 := bstep (se 1 (by rfl) ⟨1368602, by rfl⟩ : syracuseStep 1824803 = 2737205) B2737205
theorem B1464419 : Blo 810345 1464419 := bstep (se 1 (by rfl) ⟨1098314, by rfl⟩ : syracuseStep 1464419 = 2196629) B2196629
theorem B1825073 : Blo 810345 1825073 := bstep (se 2 (by rfl) ⟨684402, by rfl⟩ : syracuseStep 1825073 = 1368805) B1368805
theorem B1235251 : Blo 810345 1235251 := bstep (se 1 (by rfl) ⟨926438, by rfl⟩ : syracuseStep 1235251 = 1852877) B1852877
theorem B1825091 : Blo 810345 1825091 := bstep (se 1 (by rfl) ⟨1368818, by rfl⟩ : syracuseStep 1825091 = 2737637) B2737637
theorem B2742605 : Blo 810345 2742605 := bstep (se 3 (by rfl) ⟨514238, by rfl⟩ : syracuseStep 2742605 = 1028477) B1028477
theorem B1300835 : Blo 810345 1300835 := bstep (se 1 (by rfl) ⟨975626, by rfl⟩ : syracuseStep 1300835 = 1951253) B1951253
theorem B2742659 : Blo 810345 2742659 := bstep (se 1 (by rfl) ⟨2056994, by rfl⟩ : syracuseStep 2742659 = 4113989) B4113989
theorem B4119011 : Blo 810345 4119011 := bstep (se 1 (by rfl) ⟨3089258, by rfl⟩ : syracuseStep 4119011 = 6178517) B6178517
theorem B1169905 : Blo 810345 1169905 := bstep (se 2 (by rfl) ⟨438714, by rfl⟩ : syracuseStep 1169905 = 877429) B877429
theorem B3299825 : Blo 810345 3299825 := bstep (se 2 (by rfl) ⟨1237434, by rfl⟩ : syracuseStep 3299825 = 2474869) B2474869
theorem B1825361 : Blo 810345 1825361 := bstep (se 2 (by rfl) ⟨684510, by rfl⟩ : syracuseStep 1825361 = 1369021) B1369021
theorem B1825379 : Blo 810345 1825379 := bstep (se 1 (by rfl) ⟨1369034, by rfl⟩ : syracuseStep 1825379 = 2738069) B2738069
theorem B2316899 : Blo 810345 2316899 := bstep (se 1 (by rfl) ⟨1737674, by rfl⟩ : syracuseStep 2316899 = 3475349) B3475349
theorem B1301123 : Blo 810345 1301123 := bstep (se 1 (by rfl) ⟨975842, by rfl⟩ : syracuseStep 1301123 = 1951685) B1951685
theorem B1235587 : Blo 810345 1235587 := bstep (se 1 (by rfl) ⟨926690, by rfl⟩ : syracuseStep 1235587 = 1853381) B1853381
theorem B2742929 : Blo 810345 2742929 := bstep (se 2 (by rfl) ⟨1028598, by rfl⟩ : syracuseStep 2742929 = 2057197) B2057197
theorem B1170163 : Blo 810345 1170163 := bstep (se 1 (by rfl) ⟨877622, by rfl⟩ : syracuseStep 1170163 = 1755245) B1755245
theorem B2054929 : Blo 810345 2054929 := bstep (se 2 (by rfl) ⟨770598, by rfl⟩ : syracuseStep 2054929 = 1541197) B1541197
theorem B1825649 : Blo 810345 1825649 := bstep (se 2 (by rfl) ⟨684618, by rfl⟩ : syracuseStep 1825649 = 1369237) B1369237
theorem B1825667 : Blo 810345 1825667 := bstep (se 1 (by rfl) ⟨1369250, by rfl⟩ : syracuseStep 1825667 = 2738501) B2738501
theorem B2055203 : Blo 810345 2055203 := bstep (se 1 (by rfl) ⟨1541402, by rfl⟩ : syracuseStep 2055203 = 3082805) B3082805
theorem B1465457 : Blo 810345 1465457 := bstep (se 2 (by rfl) ⟨549546, by rfl⟩ : syracuseStep 1465457 = 1099093) B1099093
theorem B1825937 : Blo 810345 1825937 := bstep (se 2 (by rfl) ⟨684726, by rfl⟩ : syracuseStep 1825937 = 1369453) B1369453
theorem B1825955 : Blo 810345 1825955 := bstep (se 1 (by rfl) ⟨1369466, by rfl⟩ : syracuseStep 1825955 = 2738933) B2738933
theorem B2743469 : Blo 810345 2743469 := bstep (se 3 (by rfl) ⟨514400, by rfl⟩ : syracuseStep 2743469 = 1028801) B1028801
theorem B2055395 : Blo 810345 2055395 := bstep (se 1 (by rfl) ⟨1541546, by rfl⟩ : syracuseStep 2055395 = 3083093) B3083093
theorem B2743523 : Blo 810345 2743523 := bstep (se 1 (by rfl) ⟨2057642, by rfl⟩ : syracuseStep 2743523 = 4115285) B4115285
theorem B4119821 : Blo 810345 4119821 := bstep (se 3 (by rfl) ⟨772466, by rfl⟩ : syracuseStep 4119821 = 1544933) B1544933
theorem B810355 : Blo 810345 810355 := bstep (se 1 (by rfl) ⟨607766, by rfl⟩ : syracuseStep 810355 = 1215533) B1215533
theorem B810371 : Blo 810345 810371 := bstep (se 1 (by rfl) ⟨607778, by rfl⟩ : syracuseStep 810371 = 1215557) B1215557
theorem B810387 : Blo 810345 810387 := bstep (se 1 (by rfl) ⟨607790, by rfl⟩ : syracuseStep 810387 = 1215581) B1215581
theorem B810403 : Blo 810345 810403 := bstep (se 1 (by rfl) ⟨607802, by rfl⟩ : syracuseStep 810403 = 1215605) B1215605
theorem B1301923 : Blo 810345 1301923 := bstep (se 1 (by rfl) ⟨976442, by rfl⟩ : syracuseStep 1301923 = 1952885) B1952885
theorem B1826225 : Blo 810345 1826225 := bstep (se 2 (by rfl) ⟨684834, by rfl⟩ : syracuseStep 1826225 = 1369669) B1369669
theorem B810419 : Blo 810345 810419 := bstep (se 1 (by rfl) ⟨607814, by rfl⟩ : syracuseStep 810419 = 1215629) B1215629
theorem B1367489 : Blo 810345 1367489 := bstep (se 2 (by rfl) ⟨512808, by rfl⟩ : syracuseStep 1367489 = 1025617) B1025617
theorem B810435 : Blo 810345 810435 := bstep (se 1 (by rfl) ⟨607826, by rfl⟩ : syracuseStep 810435 = 1215653) B1215653
theorem B1826243 : Blo 810345 1826243 := bstep (se 1 (by rfl) ⟨1369682, by rfl⟩ : syracuseStep 1826243 = 2739365) B2739365
theorem B3464653 : Blo 810345 3464653 := bstep (se 3 (by rfl) ⟨649622, by rfl⟩ : syracuseStep 3464653 = 1299245) B1299245
theorem B810451 : Blo 810345 810451 := bstep (se 1 (by rfl) ⟨607838, by rfl⟩ : syracuseStep 810451 = 1215677) B1215677
theorem B810467 : Blo 810345 810467 := bstep (se 1 (by rfl) ⟨607850, by rfl⟩ : syracuseStep 810467 = 1215701) B1215701
theorem B2743793 : Blo 810345 2743793 := bstep (se 2 (by rfl) ⟨1028922, by rfl⟩ : syracuseStep 2743793 = 2057845) B2057845
theorem B810483 : Blo 810345 810483 := bstep (se 1 (by rfl) ⟨607862, by rfl⟩ : syracuseStep 810483 = 1215725) B1215725
theorem B810499 : Blo 810345 810499 := bstep (se 1 (by rfl) ⟨607874, by rfl⟩ : syracuseStep 810499 = 1215749) B1215749
theorem B810515 : Blo 810345 810515 := bstep (se 1 (by rfl) ⟨607886, by rfl⟩ : syracuseStep 810515 = 1215773) B1215773
theorem B810531 : Blo 810345 810531 := bstep (se 1 (by rfl) ⟨607898, by rfl⟩ : syracuseStep 810531 = 1215797) B1215797
theorem B1302065 : Blo 810345 1302065 := bstep (se 2 (by rfl) ⟨488274, by rfl⟩ : syracuseStep 1302065 = 976549) B976549
theorem B810547 : Blo 810345 810547 := bstep (se 1 (by rfl) ⟨607910, by rfl⟩ : syracuseStep 810547 = 1215821) B1215821
theorem B1367617 : Blo 810345 1367617 := bstep (se 2 (by rfl) ⟨512856, by rfl⟩ : syracuseStep 1367617 = 1025713) B1025713
theorem B810563 : Blo 810345 810563 := bstep (se 1 (by rfl) ⟨607922, by rfl⟩ : syracuseStep 810563 = 1215845) B1215845
theorem B1302097 : Blo 810345 1302097 := bstep (se 2 (by rfl) ⟨488286, by rfl⟩ : syracuseStep 1302097 = 976573) B976573
theorem B810579 : Blo 810345 810579 := bstep (se 1 (by rfl) ⟨607934, by rfl⟩ : syracuseStep 810579 = 1215869) B1215869
theorem B1367651 : Blo 810345 1367651 := bstep (se 1 (by rfl) ⟨1025738, by rfl⟩ : syracuseStep 1367651 = 2051477) B2051477
theorem B810595 : Blo 810345 810595 := bstep (se 1 (by rfl) ⟨607946, by rfl⟩ : syracuseStep 810595 = 1215893) B1215893
theorem B810611 : Blo 810345 810611 := bstep (se 1 (by rfl) ⟨607958, by rfl⟩ : syracuseStep 810611 = 1215917) B1215917
theorem B810627 : Blo 810345 810627 := bstep (se 1 (by rfl) ⟨607970, by rfl⟩ : syracuseStep 810627 = 1215941) B1215941
theorem B810643 : Blo 810345 810643 := bstep (se 1 (by rfl) ⟨607982, by rfl⟩ : syracuseStep 810643 = 1215965) B1215965
theorem B810659 : Blo 810345 810659 := bstep (se 1 (by rfl) ⟨607994, by rfl⟩ : syracuseStep 810659 = 1215989) B1215989
theorem B810675 : Blo 810345 810675 := bstep (se 1 (by rfl) ⟨608006, by rfl⟩ : syracuseStep 810675 = 1216013) B1216013
theorem B810691 : Blo 810345 810691 := bstep (se 1 (by rfl) ⟨608018, by rfl⟩ : syracuseStep 810691 = 1216037) B1216037
theorem B1826513 : Blo 810345 1826513 := bstep (se 2 (by rfl) ⟨684942, by rfl⟩ : syracuseStep 1826513 = 1369885) B1369885
theorem B810707 : Blo 810345 810707 := bstep (se 1 (by rfl) ⟨608030, by rfl⟩ : syracuseStep 810707 = 1216061) B1216061
theorem B1367779 : Blo 810345 1367779 := bstep (se 1 (by rfl) ⟨1025834, by rfl⟩ : syracuseStep 1367779 = 2051669) B2051669
theorem B810723 : Blo 810345 810723 := bstep (se 1 (by rfl) ⟨608042, by rfl⟩ : syracuseStep 810723 = 1216085) B1216085
theorem B1826531 : Blo 810345 1826531 := bstep (se 1 (by rfl) ⟨1369898, by rfl⟩ : syracuseStep 1826531 = 2739797) B2739797
theorem B810739 : Blo 810345 810739 := bstep (se 1 (by rfl) ⟨608054, by rfl⟩ : syracuseStep 810739 = 1216109) B1216109
theorem B810755 : Blo 810345 810755 := bstep (se 1 (by rfl) ⟨608066, by rfl⟩ : syracuseStep 810755 = 1216133) B1216133
theorem B810771 : Blo 810345 810771 := bstep (se 1 (by rfl) ⟨608078, by rfl⟩ : syracuseStep 810771 = 1216157) B1216157
theorem B810787 : Blo 810345 810787 := bstep (se 1 (by rfl) ⟨608090, by rfl⟩ : syracuseStep 810787 = 1216181) B1216181
theorem B2318129 : Blo 810345 2318129 := bstep (se 2 (by rfl) ⟨869298, by rfl⟩ : syracuseStep 2318129 = 1738597) B1738597
theorem B810803 : Blo 810345 810803 := bstep (se 1 (by rfl) ⟨608102, by rfl⟩ : syracuseStep 810803 = 1216205) B1216205
theorem B810819 : Blo 810345 810819 := bstep (se 1 (by rfl) ⟨608114, by rfl⟩ : syracuseStep 810819 = 1216229) B1216229
theorem B810835 : Blo 810345 810835 := bstep (se 1 (by rfl) ⟨608126, by rfl⟩ : syracuseStep 810835 = 1216253) B1216253
theorem B810851 : Blo 810345 810851 := bstep (se 1 (by rfl) ⟨608138, by rfl⟩ : syracuseStep 810851 = 1216277) B1216277
theorem B1367921 : Blo 810345 1367921 := bstep (se 2 (by rfl) ⟨512970, by rfl⟩ : syracuseStep 1367921 = 1025941) B1025941
theorem B810867 : Blo 810345 810867 := bstep (se 1 (by rfl) ⟨608150, by rfl⟩ : syracuseStep 810867 = 1216301) B1216301
theorem B810883 : Blo 810345 810883 := bstep (se 1 (by rfl) ⟨608162, by rfl⟩ : syracuseStep 810883 = 1216325) B1216325
theorem B810899 : Blo 810345 810899 := bstep (se 1 (by rfl) ⟨608174, by rfl⟩ : syracuseStep 810899 = 1216349) B1216349
theorem B810915 : Blo 810345 810915 := bstep (se 1 (by rfl) ⟨608186, by rfl⟩ : syracuseStep 810915 = 1216373) B1216373
theorem B810931 : Blo 810345 810931 := bstep (se 1 (by rfl) ⟨608198, by rfl⟩ : syracuseStep 810931 = 1216397) B1216397
theorem B810947 : Blo 810345 810947 := bstep (se 1 (by rfl) ⟨608210, by rfl⟩ : syracuseStep 810947 = 1216421) B1216421
theorem B810963 : Blo 810345 810963 := bstep (se 1 (by rfl) ⟨608222, by rfl⟩ : syracuseStep 810963 = 1216445) B1216445
theorem B810979 : Blo 810345 810979 := bstep (se 1 (by rfl) ⟨608234, by rfl⟩ : syracuseStep 810979 = 1216469) B1216469
theorem B1368049 : Blo 810345 1368049 := bstep (se 2 (by rfl) ⟨513018, by rfl⟩ : syracuseStep 1368049 = 1026037) B1026037
theorem B1826801 : Blo 810345 1826801 := bstep (se 2 (by rfl) ⟨685050, by rfl⟩ : syracuseStep 1826801 = 1370101) B1370101
theorem B810995 : Blo 810345 810995 := bstep (se 1 (by rfl) ⟨608246, by rfl⟩ : syracuseStep 810995 = 1216493) B1216493
theorem B811011 : Blo 810345 811011 := bstep (se 1 (by rfl) ⟨608258, by rfl⟩ : syracuseStep 811011 = 1216517) B1216517
theorem B1826819 : Blo 810345 1826819 := bstep (se 1 (by rfl) ⟨1370114, by rfl⟩ : syracuseStep 1826819 = 2740229) B2740229
theorem B2744333 : Blo 810345 2744333 := bstep (se 3 (by rfl) ⟨514562, by rfl⟩ : syracuseStep 2744333 = 1029125) B1029125
theorem B1368083 : Blo 810345 1368083 := bstep (se 1 (by rfl) ⟨1026062, by rfl⟩ : syracuseStep 1368083 = 2052125) B2052125
theorem B811027 : Blo 810345 811027 := bstep (se 1 (by rfl) ⟨608270, by rfl⟩ : syracuseStep 811027 = 1216541) B1216541
theorem B811043 : Blo 810345 811043 := bstep (se 1 (by rfl) ⟨608282, by rfl⟩ : syracuseStep 811043 = 1216565) B1216565
theorem B811059 : Blo 810345 811059 := bstep (se 1 (by rfl) ⟨608294, by rfl⟩ : syracuseStep 811059 = 1216589) B1216589
theorem B811075 : Blo 810345 811075 := bstep (se 1 (by rfl) ⟨608306, by rfl⟩ : syracuseStep 811075 = 1216613) B1216613
theorem B2744387 : Blo 810345 2744387 := bstep (se 1 (by rfl) ⟨2058290, by rfl⟩ : syracuseStep 2744387 = 4116581) B4116581
theorem B811091 : Blo 810345 811091 := bstep (se 1 (by rfl) ⟨608318, by rfl⟩ : syracuseStep 811091 = 1216637) B1216637
theorem B811107 : Blo 810345 811107 := bstep (se 1 (by rfl) ⟨608330, by rfl⟩ : syracuseStep 811107 = 1216661) B1216661
theorem B811123 : Blo 810345 811123 := bstep (se 1 (by rfl) ⟨608342, by rfl⟩ : syracuseStep 811123 = 1216685) B1216685
theorem B811139 : Blo 810345 811139 := bstep (se 1 (by rfl) ⟨608354, by rfl⟩ : syracuseStep 811139 = 1216709) B1216709
theorem B5202053 : Blo 810345 5202053 := bstep (se 4 (by rfl) ⟨487692, by rfl⟩ : syracuseStep 5202053 = 975385) B975385
theorem B18735245 : Blo 810345 18735245 := bstep (se 3 (by rfl) ⟨3512858, by rfl⟩ : syracuseStep 18735245 = 7025717) B7025717
theorem B2056337 : Blo 810345 2056337 := bstep (se 2 (by rfl) ⟨771126, by rfl⟩ : syracuseStep 2056337 = 1542253) B1542253
theorem B1368211 : Blo 810345 1368211 := bstep (se 1 (by rfl) ⟨1026158, by rfl⟩ : syracuseStep 1368211 = 2052317) B2052317
theorem B811155 : Blo 810345 811155 := bstep (se 1 (by rfl) ⟨608366, by rfl⟩ : syracuseStep 811155 = 1216733) B1216733
theorem B811171 : Blo 810345 811171 := bstep (se 1 (by rfl) ⟨608378, by rfl⟩ : syracuseStep 811171 = 1216757) B1216757
theorem B811187 : Blo 810345 811187 := bstep (se 1 (by rfl) ⟨608390, by rfl⟩ : syracuseStep 811187 = 1216781) B1216781
theorem B811203 : Blo 810345 811203 := bstep (se 1 (by rfl) ⟨608402, by rfl⟩ : syracuseStep 811203 = 1216805) B1216805
theorem B2056387 : Blo 810345 2056387 := bstep (se 1 (by rfl) ⟨1542290, by rfl⟩ : syracuseStep 2056387 = 3084581) B3084581
theorem B811219 : Blo 810345 811219 := bstep (se 1 (by rfl) ⟨608414, by rfl⟩ : syracuseStep 811219 = 1216829) B1216829
theorem B811235 : Blo 810345 811235 := bstep (se 1 (by rfl) ⟨608426, by rfl⟩ : syracuseStep 811235 = 1216853) B1216853
theorem B811251 : Blo 810345 811251 := bstep (se 1 (by rfl) ⟨608438, by rfl⟩ : syracuseStep 811251 = 1216877) B1216877
theorem B811267 : Blo 810345 811267 := bstep (se 1 (by rfl) ⟨608450, by rfl⟩ : syracuseStep 811267 = 1216901) B1216901
theorem B1827089 : Blo 810345 1827089 := bstep (se 2 (by rfl) ⟨685158, by rfl⟩ : syracuseStep 1827089 = 1370317) B1370317
theorem B811283 : Blo 810345 811283 := bstep (se 1 (by rfl) ⟨608462, by rfl⟩ : syracuseStep 811283 = 1216925) B1216925
theorem B26665237 : Blo 810345 26665237 := bstep (se 6 (by rfl) ⟨624966, by rfl⟩ : syracuseStep 26665237 = 1249933) B1249933
theorem B1368353 : Blo 810345 1368353 := bstep (se 2 (by rfl) ⟨513132, by rfl⟩ : syracuseStep 1368353 = 1026265) B1026265
theorem B811299 : Blo 810345 811299 := bstep (se 1 (by rfl) ⟨608474, by rfl⟩ : syracuseStep 811299 = 1216949) B1216949
theorem B1827107 : Blo 810345 1827107 := bstep (se 1 (by rfl) ⟨1370330, by rfl⟩ : syracuseStep 1827107 = 2740661) B2740661
theorem B811315 : Blo 810345 811315 := bstep (se 1 (by rfl) ⟨608486, by rfl⟩ : syracuseStep 811315 = 1216973) B1216973
theorem B811331 : Blo 810345 811331 := bstep (se 1 (by rfl) ⟨608498, by rfl⟩ : syracuseStep 811331 = 1216997) B1216997
theorem B2056529 : Blo 810345 2056529 := bstep (se 2 (by rfl) ⟨771198, by rfl⟩ : syracuseStep 2056529 = 1542397) B1542397
theorem B2744657 : Blo 810345 2744657 := bstep (se 2 (by rfl) ⟨1029246, by rfl⟩ : syracuseStep 2744657 = 2058493) B2058493
theorem B811347 : Blo 810345 811347 := bstep (se 1 (by rfl) ⟨608510, by rfl⟩ : syracuseStep 811347 = 1217021) B1217021
theorem B811363 : Blo 810345 811363 := bstep (se 1 (by rfl) ⟨608522, by rfl⟩ : syracuseStep 811363 = 1217045) B1217045
theorem B811379 : Blo 810345 811379 := bstep (se 1 (by rfl) ⟨608534, by rfl⟩ : syracuseStep 811379 = 1217069) B1217069
theorem B811395 : Blo 810345 811395 := bstep (se 1 (by rfl) ⟨608546, by rfl⟩ : syracuseStep 811395 = 1217093) B1217093
theorem B811411 : Blo 810345 811411 := bstep (se 1 (by rfl) ⟨608558, by rfl⟩ : syracuseStep 811411 = 1217117) B1217117
theorem B1368481 : Blo 810345 1368481 := bstep (se 2 (by rfl) ⟨513180, by rfl⟩ : syracuseStep 1368481 = 1026361) B1026361
theorem B811427 : Blo 810345 811427 := bstep (se 1 (by rfl) ⟨608570, by rfl⟩ : syracuseStep 811427 = 1217141) B1217141
theorem B811443 : Blo 810345 811443 := bstep (se 1 (by rfl) ⟨608582, by rfl⟩ : syracuseStep 811443 = 1217165) B1217165
theorem B9265589 : Blo 810345 9265589 := bstep (se 5 (by rfl) ⟨434324, by rfl⟩ : syracuseStep 9265589 = 868649) B868649
theorem B1368515 : Blo 810345 1368515 := bstep (se 1 (by rfl) ⟨1026386, by rfl⟩ : syracuseStep 1368515 = 2052773) B2052773
theorem B811459 : Blo 810345 811459 := bstep (se 1 (by rfl) ⟨608594, by rfl⟩ : syracuseStep 811459 = 1217189) B1217189
theorem B811475 : Blo 810345 811475 := bstep (se 1 (by rfl) ⟨608606, by rfl⟩ : syracuseStep 811475 = 1217213) B1217213
theorem B811491 : Blo 810345 811491 := bstep (se 1 (by rfl) ⟨608618, by rfl⟩ : syracuseStep 811491 = 1217237) B1217237
theorem B1303025 : Blo 810345 1303025 := bstep (se 2 (by rfl) ⟨488634, by rfl⟩ : syracuseStep 1303025 = 977269) B977269
theorem B811507 : Blo 810345 811507 := bstep (se 1 (by rfl) ⟨608630, by rfl⟩ : syracuseStep 811507 = 1217261) B1217261
theorem B811523 : Blo 810345 811523 := bstep (se 1 (by rfl) ⟨608642, by rfl⟩ : syracuseStep 811523 = 1217285) B1217285
theorem B811539 : Blo 810345 811539 := bstep (se 1 (by rfl) ⟨608654, by rfl⟩ : syracuseStep 811539 = 1217309) B1217309
theorem B811555 : Blo 810345 811555 := bstep (se 1 (by rfl) ⟨608666, by rfl⟩ : syracuseStep 811555 = 1217333) B1217333
theorem B1827377 : Blo 810345 1827377 := bstep (se 2 (by rfl) ⟨685266, by rfl⟩ : syracuseStep 1827377 = 1370533) B1370533
theorem B811571 : Blo 810345 811571 := bstep (se 1 (by rfl) ⟨608678, by rfl⟩ : syracuseStep 811571 = 1217357) B1217357
theorem B1368643 : Blo 810345 1368643 := bstep (se 1 (by rfl) ⟨1026482, by rfl⟩ : syracuseStep 1368643 = 2052965) B2052965
theorem B811587 : Blo 810345 811587 := bstep (se 1 (by rfl) ⟨608690, by rfl⟩ : syracuseStep 811587 = 1217381) B1217381
theorem B1827395 : Blo 810345 1827395 := bstep (se 1 (by rfl) ⟨1370546, by rfl⟩ : syracuseStep 1827395 = 2741093) B2741093
theorem B811603 : Blo 810345 811603 := bstep (se 1 (by rfl) ⟨608702, by rfl⟩ : syracuseStep 811603 = 1217405) B1217405
theorem B811619 : Blo 810345 811619 := bstep (se 1 (by rfl) ⟨608714, by rfl⟩ : syracuseStep 811619 = 1217429) B1217429
theorem B811635 : Blo 810345 811635 := bstep (se 1 (by rfl) ⟨608726, by rfl⟩ : syracuseStep 811635 = 1217453) B1217453
theorem B811651 : Blo 810345 811651 := bstep (se 1 (by rfl) ⟨608738, by rfl⟩ : syracuseStep 811651 = 1217477) B1217477
theorem B811667 : Blo 810345 811667 := bstep (se 1 (by rfl) ⟨608750, by rfl⟩ : syracuseStep 811667 = 1217501) B1217501
theorem B811683 : Blo 810345 811683 := bstep (se 1 (by rfl) ⟨608762, by rfl⟩ : syracuseStep 811683 = 1217525) B1217525
theorem B811699 : Blo 810345 811699 := bstep (se 1 (by rfl) ⟨608774, by rfl⟩ : syracuseStep 811699 = 1217549) B1217549
theorem B811715 : Blo 810345 811715 := bstep (se 1 (by rfl) ⟨608786, by rfl⟩ : syracuseStep 811715 = 1217573) B1217573
theorem B1368785 : Blo 810345 1368785 := bstep (se 2 (by rfl) ⟨513294, by rfl⟩ : syracuseStep 1368785 = 1026589) B1026589
theorem B811731 : Blo 810345 811731 := bstep (se 1 (by rfl) ⟨608798, by rfl⟩ : syracuseStep 811731 = 1217597) B1217597
theorem B811747 : Blo 810345 811747 := bstep (se 1 (by rfl) ⟨608810, by rfl⟩ : syracuseStep 811747 = 1217621) B1217621
theorem B811763 : Blo 810345 811763 := bstep (se 1 (by rfl) ⟨608822, by rfl⟩ : syracuseStep 811763 = 1217645) B1217645
theorem B811779 : Blo 810345 811779 := bstep (se 1 (by rfl) ⟨608834, by rfl⟩ : syracuseStep 811779 = 1217669) B1217669
theorem B811795 : Blo 810345 811795 := bstep (se 1 (by rfl) ⟨608846, by rfl⟩ : syracuseStep 811795 = 1217693) B1217693
theorem B811811 : Blo 810345 811811 := bstep (se 1 (by rfl) ⟨608858, by rfl⟩ : syracuseStep 811811 = 1217717) B1217717
theorem B811827 : Blo 810345 811827 := bstep (se 1 (by rfl) ⟨608870, by rfl⟩ : syracuseStep 811827 = 1217741) B1217741
theorem B811843 : Blo 810345 811843 := bstep (se 1 (by rfl) ⟨608882, by rfl⟩ : syracuseStep 811843 = 1217765) B1217765
theorem B1368913 : Blo 810345 1368913 := bstep (se 2 (by rfl) ⟨513342, by rfl⟩ : syracuseStep 1368913 = 1026685) B1026685
theorem B1827665 : Blo 810345 1827665 := bstep (se 2 (by rfl) ⟨685374, by rfl⟩ : syracuseStep 1827665 = 1370749) B1370749
theorem B811859 : Blo 810345 811859 := bstep (se 1 (by rfl) ⟨608894, by rfl⟩ : syracuseStep 811859 = 1217789) B1217789
theorem B811875 : Blo 810345 811875 := bstep (se 1 (by rfl) ⟨608906, by rfl⟩ : syracuseStep 811875 = 1217813) B1217813
theorem B1827683 : Blo 810345 1827683 := bstep (se 1 (by rfl) ⟨1370762, by rfl⟩ : syracuseStep 1827683 = 2741525) B2741525
theorem B2745197 : Blo 810345 2745197 := bstep (se 3 (by rfl) ⟨514724, by rfl⟩ : syracuseStep 2745197 = 1029449) B1029449
theorem B1368947 : Blo 810345 1368947 := bstep (se 1 (by rfl) ⟨1026710, by rfl⟩ : syracuseStep 1368947 = 2053421) B2053421
theorem B811891 : Blo 810345 811891 := bstep (se 1 (by rfl) ⟨608918, by rfl⟩ : syracuseStep 811891 = 1217837) B1217837
theorem B975731 : Blo 810345 975731 := bstep (se 1 (by rfl) ⟨731798, by rfl⟩ : syracuseStep 975731 = 1463597) B1463597
theorem B811907 : Blo 810345 811907 := bstep (se 1 (by rfl) ⟨608930, by rfl⟩ : syracuseStep 811907 = 1217861) B1217861
theorem B1467281 : Blo 810345 1467281 := bstep (se 2 (by rfl) ⟨550230, by rfl⟩ : syracuseStep 1467281 = 1100461) B1100461
theorem B811923 : Blo 810345 811923 := bstep (se 1 (by rfl) ⟨608942, by rfl⟩ : syracuseStep 811923 = 1217885) B1217885
theorem B811939 : Blo 810345 811939 := bstep (se 1 (by rfl) ⟨608954, by rfl⟩ : syracuseStep 811939 = 1217909) B1217909
theorem B2745251 : Blo 810345 2745251 := bstep (se 1 (by rfl) ⟨2058938, by rfl⟩ : syracuseStep 2745251 = 4117877) B4117877
theorem B811955 : Blo 810345 811955 := bstep (se 1 (by rfl) ⟨608966, by rfl⟩ : syracuseStep 811955 = 1217933) B1217933
theorem B811971 : Blo 810345 811971 := bstep (se 1 (by rfl) ⟨608978, by rfl⟩ : syracuseStep 811971 = 1217957) B1217957
theorem B811987 : Blo 810345 811987 := bstep (se 1 (by rfl) ⟨608990, by rfl⟩ : syracuseStep 811987 = 1217981) B1217981
theorem B812003 : Blo 810345 812003 := bstep (se 1 (by rfl) ⟨609002, by rfl⟩ : syracuseStep 812003 = 1218005) B1218005
theorem B1369075 : Blo 810345 1369075 := bstep (se 1 (by rfl) ⟨1026806, by rfl⟩ : syracuseStep 1369075 = 2053613) B2053613
theorem B812019 : Blo 810345 812019 := bstep (se 1 (by rfl) ⟨609014, by rfl⟩ : syracuseStep 812019 = 1218029) B1218029
theorem B812035 : Blo 810345 812035 := bstep (se 1 (by rfl) ⟨609026, by rfl⟩ : syracuseStep 812035 = 1218053) B1218053
theorem B812051 : Blo 810345 812051 := bstep (se 1 (by rfl) ⟨609038, by rfl⟩ : syracuseStep 812051 = 1218077) B1218077
theorem B812067 : Blo 810345 812067 := bstep (se 1 (by rfl) ⟨609050, by rfl⟩ : syracuseStep 812067 = 1218101) B1218101
theorem B812083 : Blo 810345 812083 := bstep (se 1 (by rfl) ⟨609062, by rfl⟩ : syracuseStep 812083 = 1218125) B1218125
theorem B812099 : Blo 810345 812099 := bstep (se 1 (by rfl) ⟨609074, by rfl⟩ : syracuseStep 812099 = 1218149) B1218149
theorem B812115 : Blo 810345 812115 := bstep (se 1 (by rfl) ⟨609086, by rfl⟩ : syracuseStep 812115 = 1218173) B1218173
theorem B812131 : Blo 810345 812131 := bstep (se 1 (by rfl) ⟨609098, by rfl⟩ : syracuseStep 812131 = 1218197) B1218197
theorem B1827953 : Blo 810345 1827953 := bstep (se 2 (by rfl) ⟨685482, by rfl⟩ : syracuseStep 1827953 = 1370965) B1370965
theorem B812147 : Blo 810345 812147 := bstep (se 1 (by rfl) ⟨609110, by rfl⟩ : syracuseStep 812147 = 1218221) B1218221
theorem B1369217 : Blo 810345 1369217 := bstep (se 2 (by rfl) ⟨513456, by rfl⟩ : syracuseStep 1369217 = 1026913) B1026913
theorem B812163 : Blo 810345 812163 := bstep (se 1 (by rfl) ⟨609122, by rfl⟩ : syracuseStep 812163 = 1218245) B1218245
theorem B1827971 : Blo 810345 1827971 := bstep (se 1 (by rfl) ⟨1370978, by rfl⟩ : syracuseStep 1827971 = 2741957) B2741957
theorem B812179 : Blo 810345 812179 := bstep (se 1 (by rfl) ⟨609134, by rfl⟩ : syracuseStep 812179 = 1218269) B1218269
theorem B812195 : Blo 810345 812195 := bstep (se 1 (by rfl) ⟨609146, by rfl⟩ : syracuseStep 812195 = 1218293) B1218293
theorem B2745521 : Blo 810345 2745521 := bstep (se 2 (by rfl) ⟨1029570, by rfl⟩ : syracuseStep 2745521 = 2059141) B2059141
theorem B812211 : Blo 810345 812211 := bstep (se 1 (by rfl) ⟨609158, by rfl⟩ : syracuseStep 812211 = 1218317) B1218317
theorem B8774837 : Blo 810345 8774837 := bstep (se 5 (by rfl) ⟨411320, by rfl⟩ : syracuseStep 8774837 = 822641) B822641
theorem B812227 : Blo 810345 812227 := bstep (se 1 (by rfl) ⟨609170, by rfl⟩ : syracuseStep 812227 = 1218341) B1218341
theorem B812243 : Blo 810345 812243 := bstep (se 1 (by rfl) ⟨609182, by rfl⟩ : syracuseStep 812243 = 1218365) B1218365
theorem B812259 : Blo 810345 812259 := bstep (se 1 (by rfl) ⟨609194, by rfl⟩ : syracuseStep 812259 = 1218389) B1218389
theorem B812275 : Blo 810345 812275 := bstep (se 1 (by rfl) ⟨609206, by rfl⟩ : syracuseStep 812275 = 1218413) B1218413
theorem B1369345 : Blo 810345 1369345 := bstep (se 2 (by rfl) ⟨513504, by rfl⟩ : syracuseStep 1369345 = 1027009) B1027009
theorem B812291 : Blo 810345 812291 := bstep (se 1 (by rfl) ⟨609218, by rfl⟩ : syracuseStep 812291 = 1218437) B1218437
theorem B812307 : Blo 810345 812307 := bstep (se 1 (by rfl) ⟨609230, by rfl⟩ : syracuseStep 812307 = 1218461) B1218461
theorem B1369379 : Blo 810345 1369379 := bstep (se 1 (by rfl) ⟨1027034, by rfl⟩ : syracuseStep 1369379 = 2054069) B2054069
theorem B812323 : Blo 810345 812323 := bstep (se 1 (by rfl) ⟨609242, by rfl⟩ : syracuseStep 812323 = 1218485) B1218485
theorem B2057521 : Blo 810345 2057521 := bstep (se 2 (by rfl) ⟨771570, by rfl⟩ : syracuseStep 2057521 = 1543141) B1543141
theorem B812339 : Blo 810345 812339 := bstep (se 1 (by rfl) ⟨609254, by rfl⟩ : syracuseStep 812339 = 1218509) B1218509
theorem B1303859 : Blo 810345 1303859 := bstep (se 1 (by rfl) ⟨977894, by rfl⟩ : syracuseStep 1303859 = 1955789) B1955789
theorem B812355 : Blo 810345 812355 := bstep (se 1 (by rfl) ⟨609266, by rfl⟩ : syracuseStep 812355 = 1218533) B1218533
theorem B812371 : Blo 810345 812371 := bstep (se 1 (by rfl) ⟨609278, by rfl⟩ : syracuseStep 812371 = 1218557) B1218557
theorem B812387 : Blo 810345 812387 := bstep (se 1 (by rfl) ⟨609290, by rfl⟩ : syracuseStep 812387 = 1218581) B1218581
theorem B812403 : Blo 810345 812403 := bstep (se 1 (by rfl) ⟨609302, by rfl⟩ : syracuseStep 812403 = 1218605) B1218605
theorem B812419 : Blo 810345 812419 := bstep (se 1 (by rfl) ⟨609314, by rfl⟩ : syracuseStep 812419 = 1218629) B1218629
theorem B1828241 : Blo 810345 1828241 := bstep (se 2 (by rfl) ⟨685590, by rfl⟩ : syracuseStep 1828241 = 1371181) B1371181
theorem B812435 : Blo 810345 812435 := bstep (se 1 (by rfl) ⟨609326, by rfl⟩ : syracuseStep 812435 = 1218653) B1218653
theorem B1369507 : Blo 810345 1369507 := bstep (se 1 (by rfl) ⟨1027130, by rfl⟩ : syracuseStep 1369507 = 2054261) B2054261
theorem B812451 : Blo 810345 812451 := bstep (se 1 (by rfl) ⟨609338, by rfl⟩ : syracuseStep 812451 = 1218677) B1218677
theorem B1828259 : Blo 810345 1828259 := bstep (se 1 (by rfl) ⟨1371194, by rfl⟩ : syracuseStep 1828259 = 2742389) B2742389
theorem B812467 : Blo 810345 812467 := bstep (se 1 (by rfl) ⟨609350, by rfl⟩ : syracuseStep 812467 = 1218701) B1218701
theorem B812483 : Blo 810345 812483 := bstep (se 1 (by rfl) ⟨609362, by rfl⟩ : syracuseStep 812483 = 1218725) B1218725
theorem B812499 : Blo 810345 812499 := bstep (se 1 (by rfl) ⟨609374, by rfl⟩ : syracuseStep 812499 = 1218749) B1218749
theorem B878051 : Blo 810345 878051 := bstep (se 1 (by rfl) ⟨658538, by rfl⟩ : syracuseStep 878051 = 1317077) B1317077
theorem B812515 : Blo 810345 812515 := bstep (se 1 (by rfl) ⟨609386, by rfl⟩ : syracuseStep 812515 = 1218773) B1218773
theorem B812531 : Blo 810345 812531 := bstep (se 1 (by rfl) ⟨609398, by rfl⟩ : syracuseStep 812531 = 1218797) B1218797
theorem B812547 : Blo 810345 812547 := bstep (se 1 (by rfl) ⟨609410, by rfl⟩ : syracuseStep 812547 = 1218821) B1218821
theorem B812563 : Blo 810345 812563 := bstep (se 1 (by rfl) ⟨609422, by rfl⟩ : syracuseStep 812563 = 1218845) B1218845
theorem B812579 : Blo 810345 812579 := bstep (se 1 (by rfl) ⟨609434, by rfl⟩ : syracuseStep 812579 = 1218869) B1218869
theorem B1369649 : Blo 810345 1369649 := bstep (se 2 (by rfl) ⟨513618, by rfl⟩ : syracuseStep 1369649 = 1027237) B1027237
theorem B812595 : Blo 810345 812595 := bstep (se 1 (by rfl) ⟨609446, by rfl⟩ : syracuseStep 812595 = 1218893) B1218893
theorem B812611 : Blo 810345 812611 := bstep (se 1 (by rfl) ⟨609458, by rfl⟩ : syracuseStep 812611 = 1218917) B1218917
theorem B2057795 : Blo 810345 2057795 := bstep (se 1 (by rfl) ⟨1543346, by rfl⟩ : syracuseStep 2057795 = 3086693) B3086693
theorem B812627 : Blo 810345 812627 := bstep (se 1 (by rfl) ⟨609470, by rfl⟩ : syracuseStep 812627 = 1218941) B1218941
theorem B1304147 : Blo 810345 1304147 := bstep (se 1 (by rfl) ⟨978110, by rfl⟩ : syracuseStep 1304147 = 1956221) B1956221
theorem B812643 : Blo 810345 812643 := bstep (se 1 (by rfl) ⟨609482, by rfl⟩ : syracuseStep 812643 = 1218965) B1218965
theorem B7824995 : Blo 810345 7824995 := bstep (se 1 (by rfl) ⟨5868746, by rfl⟩ : syracuseStep 7824995 = 11737493) B11737493
theorem B812659 : Blo 810345 812659 := bstep (se 1 (by rfl) ⟨609494, by rfl⟩ : syracuseStep 812659 = 1218989) B1218989
theorem B1205875 : Blo 810345 1205875 := bstep (se 1 (by rfl) ⟨904406, by rfl⟩ : syracuseStep 1205875 = 1808813) B1808813
theorem B812675 : Blo 810345 812675 := bstep (se 1 (by rfl) ⟨609506, by rfl⟩ : syracuseStep 812675 = 1219013) B1219013
theorem B812691 : Blo 810345 812691 := bstep (se 1 (by rfl) ⟨609518, by rfl⟩ : syracuseStep 812691 = 1219037) B1219037
theorem B812707 : Blo 810345 812707 := bstep (se 1 (by rfl) ⟨609530, by rfl⟩ : syracuseStep 812707 = 1219061) B1219061
theorem B1369777 : Blo 810345 1369777 := bstep (se 2 (by rfl) ⟨513666, by rfl⟩ : syracuseStep 1369777 = 1027333) B1027333
theorem B1828529 : Blo 810345 1828529 := bstep (se 2 (by rfl) ⟨685698, by rfl⟩ : syracuseStep 1828529 = 1371397) B1371397
theorem B812723 : Blo 810345 812723 := bstep (se 1 (by rfl) ⟨609542, by rfl⟩ : syracuseStep 812723 = 1219085) B1219085
theorem B1828547 : Blo 810345 1828547 := bstep (se 1 (by rfl) ⟨1371410, by rfl⟩ : syracuseStep 1828547 = 2742821) B2742821
theorem B812739 : Blo 810345 812739 := bstep (se 1 (by rfl) ⟨609554, by rfl⟩ : syracuseStep 812739 = 1219109) B1219109
theorem B2746061 : Blo 810345 2746061 := bstep (se 3 (by rfl) ⟨514886, by rfl⟩ : syracuseStep 2746061 = 1029773) B1029773
theorem B1369811 : Blo 810345 1369811 := bstep (se 1 (by rfl) ⟨1027358, by rfl⟩ : syracuseStep 1369811 = 2054717) B2054717
theorem B812755 : Blo 810345 812755 := bstep (se 1 (by rfl) ⟨609566, by rfl⟩ : syracuseStep 812755 = 1219133) B1219133
theorem B812771 : Blo 810345 812771 := bstep (se 1 (by rfl) ⟨609578, by rfl⟩ : syracuseStep 812771 = 1219157) B1219157
theorem B812787 : Blo 810345 812787 := bstep (se 1 (by rfl) ⟨609590, by rfl⟩ : syracuseStep 812787 = 1219181) B1219181
theorem B812803 : Blo 810345 812803 := bstep (se 1 (by rfl) ⟨609602, by rfl⟩ : syracuseStep 812803 = 1219205) B1219205
theorem B2057987 : Blo 810345 2057987 := bstep (se 1 (by rfl) ⟨1543490, by rfl⟩ : syracuseStep 2057987 = 3086981) B3086981
theorem B2746115 : Blo 810345 2746115 := bstep (se 1 (by rfl) ⟨2059586, by rfl⟩ : syracuseStep 2746115 = 4119173) B4119173
theorem B812819 : Blo 810345 812819 := bstep (se 1 (by rfl) ⟨609614, by rfl⟩ : syracuseStep 812819 = 1219229) B1219229
theorem B812835 : Blo 810345 812835 := bstep (se 1 (by rfl) ⟨609626, by rfl⟩ : syracuseStep 812835 = 1219253) B1219253
theorem B812851 : Blo 810345 812851 := bstep (se 1 (by rfl) ⟨609638, by rfl⟩ : syracuseStep 812851 = 1219277) B1219277
theorem B1304371 : Blo 810345 1304371 := bstep (se 1 (by rfl) ⟨978278, by rfl⟩ : syracuseStep 1304371 = 1956557) B1956557
theorem B812867 : Blo 810345 812867 := bstep (se 1 (by rfl) ⟨609650, by rfl⟩ : syracuseStep 812867 = 1219301) B1219301
theorem B1369939 : Blo 810345 1369939 := bstep (se 1 (by rfl) ⟨1027454, by rfl⟩ : syracuseStep 1369939 = 2054909) B2054909
theorem B812883 : Blo 810345 812883 := bstep (se 1 (by rfl) ⟨609662, by rfl⟩ : syracuseStep 812883 = 1219325) B1219325
theorem B812899 : Blo 810345 812899 := bstep (se 1 (by rfl) ⟨609674, by rfl⟩ : syracuseStep 812899 = 1219349) B1219349
theorem B812915 : Blo 810345 812915 := bstep (se 1 (by rfl) ⟨609686, by rfl⟩ : syracuseStep 812915 = 1219373) B1219373
theorem B812931 : Blo 810345 812931 := bstep (se 1 (by rfl) ⟨609698, by rfl⟩ : syracuseStep 812931 = 1219397) B1219397
theorem B812947 : Blo 810345 812947 := bstep (se 1 (by rfl) ⟨609710, by rfl⟩ : syracuseStep 812947 = 1219421) B1219421
theorem B812963 : Blo 810345 812963 := bstep (se 1 (by rfl) ⟨609722, by rfl⟩ : syracuseStep 812963 = 1219445) B1219445
theorem B812979 : Blo 810345 812979 := bstep (se 1 (by rfl) ⟨609734, by rfl⟩ : syracuseStep 812979 = 1219469) B1219469
theorem B812995 : Blo 810345 812995 := bstep (se 1 (by rfl) ⟨609746, by rfl⟩ : syracuseStep 812995 = 1219493) B1219493
theorem B1828817 : Blo 810345 1828817 := bstep (se 2 (by rfl) ⟨685806, by rfl⟩ : syracuseStep 1828817 = 1371613) B1371613
theorem B813011 : Blo 810345 813011 := bstep (se 1 (by rfl) ⟨609758, by rfl⟩ : syracuseStep 813011 = 1219517) B1219517
theorem B1370081 : Blo 810345 1370081 := bstep (se 2 (by rfl) ⟨513780, by rfl⟩ : syracuseStep 1370081 = 1027561) B1027561
theorem B1828835 : Blo 810345 1828835 := bstep (se 1 (by rfl) ⟨1371626, by rfl⟩ : syracuseStep 1828835 = 2743253) B2743253
theorem B813027 : Blo 810345 813027 := bstep (se 1 (by rfl) ⟨609770, by rfl⟩ : syracuseStep 813027 = 1219541) B1219541
theorem B813043 : Blo 810345 813043 := bstep (se 1 (by rfl) ⟨609782, by rfl⟩ : syracuseStep 813043 = 1219565) B1219565
theorem B813059 : Blo 810345 813059 := bstep (se 1 (by rfl) ⟨609794, by rfl⟩ : syracuseStep 813059 = 1219589) B1219589
theorem B2746385 : Blo 810345 2746385 := bstep (se 2 (by rfl) ⟨1029894, by rfl⟩ : syracuseStep 2746385 = 2059789) B2059789
theorem B813075 : Blo 810345 813075 := bstep (se 1 (by rfl) ⟨609806, by rfl⟩ : syracuseStep 813075 = 1219613) B1219613
theorem B813091 : Blo 810345 813091 := bstep (se 1 (by rfl) ⟨609818, by rfl⟩ : syracuseStep 813091 = 1219637) B1219637
theorem B813107 : Blo 810345 813107 := bstep (se 1 (by rfl) ⟨609830, by rfl⟩ : syracuseStep 813107 = 1219661) B1219661
theorem B813123 : Blo 810345 813123 := bstep (se 1 (by rfl) ⟨609842, by rfl⟩ : syracuseStep 813123 = 1219685) B1219685
theorem B813139 : Blo 810345 813139 := bstep (se 1 (by rfl) ⟨609854, by rfl⟩ : syracuseStep 813139 = 1219709) B1219709
theorem B1370209 : Blo 810345 1370209 := bstep (se 2 (by rfl) ⟨513828, by rfl⟩ : syracuseStep 1370209 = 1027657) B1027657
theorem B813155 : Blo 810345 813155 := bstep (se 1 (by rfl) ⟨609866, by rfl⟩ : syracuseStep 813155 = 1219733) B1219733
theorem B813171 : Blo 810345 813171 := bstep (se 1 (by rfl) ⟨609878, by rfl⟩ : syracuseStep 813171 = 1219757) B1219757
theorem B1370243 : Blo 810345 1370243 := bstep (se 1 (by rfl) ⟨1027682, by rfl⟩ : syracuseStep 1370243 = 2055365) B2055365
theorem B813187 : Blo 810345 813187 := bstep (se 1 (by rfl) ⟨609890, by rfl⟩ : syracuseStep 813187 = 1219781) B1219781
theorem B813203 : Blo 810345 813203 := bstep (se 1 (by rfl) ⟨609902, by rfl⟩ : syracuseStep 813203 = 1219805) B1219805
theorem B813219 : Blo 810345 813219 := bstep (se 1 (by rfl) ⟨609914, by rfl⟩ : syracuseStep 813219 = 1219829) B1219829
theorem B1730737 : Blo 810345 1730737 := bstep (se 2 (by rfl) ⟨649026, by rfl⟩ : syracuseStep 1730737 = 1298053) B1298053
theorem B813235 : Blo 810345 813235 := bstep (se 1 (by rfl) ⟨609926, by rfl⟩ : syracuseStep 813235 = 1219853) B1219853
theorem B813251 : Blo 810345 813251 := bstep (se 1 (by rfl) ⟨609938, by rfl⟩ : syracuseStep 813251 = 1219877) B1219877
theorem B813267 : Blo 810345 813267 := bstep (se 1 (by rfl) ⟨609950, by rfl⟩ : syracuseStep 813267 = 1219901) B1219901
theorem B813283 : Blo 810345 813283 := bstep (se 1 (by rfl) ⟨609962, by rfl⟩ : syracuseStep 813283 = 1219925) B1219925
theorem B1829105 : Blo 810345 1829105 := bstep (se 2 (by rfl) ⟨685914, by rfl⟩ : syracuseStep 1829105 = 1371829) B1371829
theorem B813299 : Blo 810345 813299 := bstep (se 1 (by rfl) ⟨609974, by rfl⟩ : syracuseStep 813299 = 1219949) B1219949
theorem B1370371 : Blo 810345 1370371 := bstep (se 1 (by rfl) ⟨1027778, by rfl⟩ : syracuseStep 1370371 = 2055557) B2055557
theorem B1829123 : Blo 810345 1829123 := bstep (se 1 (by rfl) ⟨1371842, by rfl⟩ : syracuseStep 1829123 = 2743685) B2743685
theorem B813315 : Blo 810345 813315 := bstep (se 1 (by rfl) ⟨609986, by rfl⟩ : syracuseStep 813315 = 1219973) B1219973
theorem B813331 : Blo 810345 813331 := bstep (se 1 (by rfl) ⟨609998, by rfl⟩ : syracuseStep 813331 = 1219997) B1219997
theorem B813347 : Blo 810345 813347 := bstep (se 1 (by rfl) ⟨610010, by rfl⟩ : syracuseStep 813347 = 1220021) B1220021
theorem B813363 : Blo 810345 813363 := bstep (se 1 (by rfl) ⟨610022, by rfl⟩ : syracuseStep 813363 = 1220045) B1220045
theorem B813379 : Blo 810345 813379 := bstep (se 1 (by rfl) ⟨610034, by rfl⟩ : syracuseStep 813379 = 1220069) B1220069
theorem B813395 : Blo 810345 813395 := bstep (se 1 (by rfl) ⟨610046, by rfl⟩ : syracuseStep 813395 = 1220093) B1220093
theorem B813411 : Blo 810345 813411 := bstep (se 1 (by rfl) ⟨610058, by rfl⟩ : syracuseStep 813411 = 1220117) B1220117
theorem B911731 : Blo 810345 911731 := bstep (se 1 (by rfl) ⟨683798, by rfl⟩ : syracuseStep 911731 = 1367597) B1367597
theorem B813427 : Blo 810345 813427 := bstep (se 1 (by rfl) ⟨610070, by rfl⟩ : syracuseStep 813427 = 1220141) B1220141
theorem B813443 : Blo 810345 813443 := bstep (se 1 (by rfl) ⟨610082, by rfl⟩ : syracuseStep 813443 = 1220165) B1220165
theorem B1370513 : Blo 810345 1370513 := bstep (se 2 (by rfl) ⟨513942, by rfl⟩ : syracuseStep 1370513 = 1027885) B1027885
theorem B813459 : Blo 810345 813459 := bstep (se 1 (by rfl) ⟨610094, by rfl⟩ : syracuseStep 813459 = 1220189) B1220189
theorem B813475 : Blo 810345 813475 := bstep (se 1 (by rfl) ⟨610106, by rfl⟩ : syracuseStep 813475 = 1220213) B1220213
theorem B813491 : Blo 810345 813491 := bstep (se 1 (by rfl) ⟨610118, by rfl⟩ : syracuseStep 813491 = 1220237) B1220237
theorem B813507 : Blo 810345 813507 := bstep (se 1 (by rfl) ⟨610130, by rfl⟩ : syracuseStep 813507 = 1220261) B1220261
theorem B813523 : Blo 810345 813523 := bstep (se 1 (by rfl) ⟨610142, by rfl⟩ : syracuseStep 813523 = 1220285) B1220285
theorem B813539 : Blo 810345 813539 := bstep (se 1 (by rfl) ⟨610154, by rfl⟩ : syracuseStep 813539 = 1220309) B1220309
theorem B813555 : Blo 810345 813555 := bstep (se 1 (by rfl) ⟨610166, by rfl⟩ : syracuseStep 813555 = 1220333) B1220333
theorem B911875 : Blo 810345 911875 := bstep (se 1 (by rfl) ⟨683906, by rfl⟩ : syracuseStep 911875 = 1367813) B1367813
theorem B813571 : Blo 810345 813571 := bstep (se 1 (by rfl) ⟨610178, by rfl⟩ : syracuseStep 813571 = 1220357) B1220357
theorem B1370641 : Blo 810345 1370641 := bstep (se 2 (by rfl) ⟨513990, by rfl⟩ : syracuseStep 1370641 = 1027981) B1027981
theorem B1829393 : Blo 810345 1829393 := bstep (se 2 (by rfl) ⟨686022, by rfl⟩ : syracuseStep 1829393 = 1372045) B1372045
theorem B813587 : Blo 810345 813587 := bstep (se 1 (by rfl) ⟨610190, by rfl⟩ : syracuseStep 813587 = 1220381) B1220381
theorem B1829411 : Blo 810345 1829411 := bstep (se 1 (by rfl) ⟨1372058, by rfl⟩ : syracuseStep 1829411 = 2744117) B2744117
theorem B813603 : Blo 810345 813603 := bstep (se 1 (by rfl) ⟨610202, by rfl⟩ : syracuseStep 813603 = 1220405) B1220405
theorem B2746925 : Blo 810345 2746925 := bstep (se 3 (by rfl) ⟨515048, by rfl⟩ : syracuseStep 2746925 = 1030097) B1030097
theorem B1370675 : Blo 810345 1370675 := bstep (se 1 (by rfl) ⟨1028006, by rfl⟩ : syracuseStep 1370675 = 2056013) B2056013
theorem B813619 : Blo 810345 813619 := bstep (se 1 (by rfl) ⟨610214, by rfl⟩ : syracuseStep 813619 = 1220429) B1220429
theorem B813635 : Blo 810345 813635 := bstep (se 1 (by rfl) ⟨610226, by rfl⟩ : syracuseStep 813635 = 1220453) B1220453
theorem B813651 : Blo 810345 813651 := bstep (se 1 (by rfl) ⟨610238, by rfl⟩ : syracuseStep 813651 = 1220477) B1220477
theorem B813667 : Blo 810345 813667 := bstep (se 1 (by rfl) ⟨610250, by rfl⟩ : syracuseStep 813667 = 1220501) B1220501
theorem B2746979 : Blo 810345 2746979 := bstep (se 1 (by rfl) ⟨2060234, by rfl⟩ : syracuseStep 2746979 = 4120469) B4120469
theorem B813683 : Blo 810345 813683 := bstep (se 1 (by rfl) ⟨610262, by rfl⟩ : syracuseStep 813683 = 1220525) B1220525
theorem B813699 : Blo 810345 813699 := bstep (se 1 (by rfl) ⟨610274, by rfl⟩ : syracuseStep 813699 = 1220549) B1220549
theorem B912019 : Blo 810345 912019 := bstep (se 1 (by rfl) ⟨684014, by rfl⟩ : syracuseStep 912019 = 1368029) B1368029
theorem B813715 : Blo 810345 813715 := bstep (se 1 (by rfl) ⟨610286, by rfl⟩ : syracuseStep 813715 = 1220573) B1220573
theorem B813731 : Blo 810345 813731 := bstep (se 1 (by rfl) ⟨610298, by rfl⟩ : syracuseStep 813731 = 1220597) B1220597
theorem B2058929 : Blo 810345 2058929 := bstep (se 2 (by rfl) ⟨772098, by rfl⟩ : syracuseStep 2058929 = 1544197) B1544197
theorem B1370803 : Blo 810345 1370803 := bstep (se 1 (by rfl) ⟨1028102, by rfl⟩ : syracuseStep 1370803 = 2056205) B2056205
theorem B813747 : Blo 810345 813747 := bstep (se 1 (by rfl) ⟨610310, by rfl⟩ : syracuseStep 813747 = 1220621) B1220621
theorem B813763 : Blo 810345 813763 := bstep (se 1 (by rfl) ⟨610322, by rfl⟩ : syracuseStep 813763 = 1220645) B1220645
theorem B813779 : Blo 810345 813779 := bstep (se 1 (by rfl) ⟨610334, by rfl⟩ : syracuseStep 813779 = 1220669) B1220669
theorem B2058979 : Blo 810345 2058979 := bstep (se 1 (by rfl) ⟨1544234, by rfl⟩ : syracuseStep 2058979 = 3088469) B3088469
theorem B813795 : Blo 810345 813795 := bstep (se 1 (by rfl) ⟨610346, by rfl⟩ : syracuseStep 813795 = 1220693) B1220693
theorem B813811 : Blo 810345 813811 := bstep (se 1 (by rfl) ⟨610358, by rfl⟩ : syracuseStep 813811 = 1220717) B1220717
theorem B813827 : Blo 810345 813827 := bstep (se 1 (by rfl) ⟨610370, by rfl⟩ : syracuseStep 813827 = 1220741) B1220741
theorem B813843 : Blo 810345 813843 := bstep (se 1 (by rfl) ⟨610382, by rfl⟩ : syracuseStep 813843 = 1220765) B1220765
theorem B912163 : Blo 810345 912163 := bstep (se 1 (by rfl) ⟨684122, by rfl⟩ : syracuseStep 912163 = 1368245) B1368245
theorem B813859 : Blo 810345 813859 := bstep (se 1 (by rfl) ⟨610394, by rfl⟩ : syracuseStep 813859 = 1220789) B1220789
theorem B1829681 : Blo 810345 1829681 := bstep (se 2 (by rfl) ⟨686130, by rfl⟩ : syracuseStep 1829681 = 1372261) B1372261
theorem B813875 : Blo 810345 813875 := bstep (se 1 (by rfl) ⟨610406, by rfl⟩ : syracuseStep 813875 = 1220813) B1220813
theorem B1370945 : Blo 810345 1370945 := bstep (se 2 (by rfl) ⟨514104, by rfl⟩ : syracuseStep 1370945 = 1028209) B1028209
theorem B1829699 : Blo 810345 1829699 := bstep (se 1 (by rfl) ⟨1372274, by rfl⟩ : syracuseStep 1829699 = 2744549) B2744549
theorem B813891 : Blo 810345 813891 := bstep (se 1 (by rfl) ⟨610418, by rfl⟩ : syracuseStep 813891 = 1220837) B1220837
theorem B813907 : Blo 810345 813907 := bstep (se 1 (by rfl) ⟨610430, by rfl⟩ : syracuseStep 813907 = 1220861) B1220861
theorem B813923 : Blo 810345 813923 := bstep (se 1 (by rfl) ⟨610442, by rfl⟩ : syracuseStep 813923 = 1220885) B1220885
theorem B2059121 : Blo 810345 2059121 := bstep (se 2 (by rfl) ⟨772170, by rfl⟩ : syracuseStep 2059121 = 1544341) B1544341
theorem B2747249 : Blo 810345 2747249 := bstep (se 2 (by rfl) ⟨1030218, by rfl⟩ : syracuseStep 2747249 = 2060437) B2060437
theorem B977779 : Blo 810345 977779 := bstep (se 1 (by rfl) ⟨733334, by rfl⟩ : syracuseStep 977779 = 1466669) B1466669
theorem B813939 : Blo 810345 813939 := bstep (se 1 (by rfl) ⟨610454, by rfl⟩ : syracuseStep 813939 = 1220909) B1220909
theorem B813955 : Blo 810345 813955 := bstep (se 1 (by rfl) ⟨610466, by rfl⟩ : syracuseStep 813955 = 1220933) B1220933
theorem B813971 : Blo 810345 813971 := bstep (se 1 (by rfl) ⟨610478, by rfl⟩ : syracuseStep 813971 = 1220957) B1220957
theorem B977827 : Blo 810345 977827 := bstep (se 1 (by rfl) ⟨733370, by rfl⟩ : syracuseStep 977827 = 1466741) B1466741
theorem B813987 : Blo 810345 813987 := bstep (se 1 (by rfl) ⟨610490, by rfl⟩ : syracuseStep 813987 = 1220981) B1220981
theorem B912307 : Blo 810345 912307 := bstep (se 1 (by rfl) ⟨684230, by rfl⟩ : syracuseStep 912307 = 1368461) B1368461
theorem B814003 : Blo 810345 814003 := bstep (se 1 (by rfl) ⟨610502, by rfl⟩ : syracuseStep 814003 = 1221005) B1221005
theorem B1371073 : Blo 810345 1371073 := bstep (se 2 (by rfl) ⟨514152, by rfl⟩ : syracuseStep 1371073 = 1028305) B1028305
theorem B814019 : Blo 810345 814019 := bstep (se 1 (by rfl) ⟨610514, by rfl⟩ : syracuseStep 814019 = 1221029) B1221029
theorem B814035 : Blo 810345 814035 := bstep (se 1 (by rfl) ⟨610526, by rfl⟩ : syracuseStep 814035 = 1221053) B1221053
theorem B1371107 : Blo 810345 1371107 := bstep (se 1 (by rfl) ⟨1028330, by rfl⟩ : syracuseStep 1371107 = 2056661) B2056661
theorem B814051 : Blo 810345 814051 := bstep (se 1 (by rfl) ⟨610538, by rfl⟩ : syracuseStep 814051 = 1221077) B1221077
theorem B814067 : Blo 810345 814067 := bstep (se 1 (by rfl) ⟨610550, by rfl⟩ : syracuseStep 814067 = 1221101) B1221101
theorem B814083 : Blo 810345 814083 := bstep (se 1 (by rfl) ⟨610562, by rfl⟩ : syracuseStep 814083 = 1221125) B1221125
theorem B814099 : Blo 810345 814099 := bstep (se 1 (by rfl) ⟨610574, by rfl⟩ : syracuseStep 814099 = 1221149) B1221149
theorem B814115 : Blo 810345 814115 := bstep (se 1 (by rfl) ⟨610586, by rfl⟩ : syracuseStep 814115 = 1221173) B1221173
theorem B814131 : Blo 810345 814131 := bstep (se 1 (by rfl) ⟨610598, by rfl⟩ : syracuseStep 814131 = 1221197) B1221197
theorem B912451 : Blo 810345 912451 := bstep (se 1 (by rfl) ⟨684338, by rfl⟩ : syracuseStep 912451 = 1368677) B1368677
theorem B814147 : Blo 810345 814147 := bstep (se 1 (by rfl) ⟨610610, by rfl⟩ : syracuseStep 814147 = 1221221) B1221221
theorem B1829969 : Blo 810345 1829969 := bstep (se 2 (by rfl) ⟨686238, by rfl⟩ : syracuseStep 1829969 = 1372477) B1372477
theorem B814163 : Blo 810345 814163 := bstep (se 1 (by rfl) ⟨610622, by rfl⟩ : syracuseStep 814163 = 1221245) B1221245
theorem B1371235 : Blo 810345 1371235 := bstep (se 1 (by rfl) ⟨1028426, by rfl⟩ : syracuseStep 1371235 = 2056853) B2056853
theorem B1829987 : Blo 810345 1829987 := bstep (se 1 (by rfl) ⟨1372490, by rfl⟩ : syracuseStep 1829987 = 2744981) B2744981
theorem B814179 : Blo 810345 814179 := bstep (se 1 (by rfl) ⟨610634, by rfl⟩ : syracuseStep 814179 = 1221269) B1221269
theorem B814195 : Blo 810345 814195 := bstep (se 1 (by rfl) ⟨610646, by rfl⟩ : syracuseStep 814195 = 1221293) B1221293
theorem B814211 : Blo 810345 814211 := bstep (se 1 (by rfl) ⟨610658, by rfl⟩ : syracuseStep 814211 = 1221317) B1221317
theorem B814227 : Blo 810345 814227 := bstep (se 1 (by rfl) ⟨610670, by rfl⟩ : syracuseStep 814227 = 1221341) B1221341
theorem B814243 : Blo 810345 814243 := bstep (se 1 (by rfl) ⟨610682, by rfl⟩ : syracuseStep 814243 = 1221365) B1221365
theorem B814259 : Blo 810345 814259 := bstep (se 1 (by rfl) ⟨610694, by rfl⟩ : syracuseStep 814259 = 1221389) B1221389
theorem B814275 : Blo 810345 814275 := bstep (se 1 (by rfl) ⟨610706, by rfl⟩ : syracuseStep 814275 = 1221413) B1221413
theorem B11136197 : Blo 810345 11136197 := bstep (se 4 (by rfl) ⟨1044018, by rfl⟩ : syracuseStep 11136197 = 2088037) B2088037
theorem B912595 : Blo 810345 912595 := bstep (se 1 (by rfl) ⟨684446, by rfl⟩ : syracuseStep 912595 = 1368893) B1368893
theorem B814291 : Blo 810345 814291 := bstep (se 1 (by rfl) ⟨610718, by rfl⟩ : syracuseStep 814291 = 1221437) B1221437
theorem B814307 : Blo 810345 814307 := bstep (se 1 (by rfl) ⟨610730, by rfl⟩ : syracuseStep 814307 = 1221461) B1221461
theorem B1371377 : Blo 810345 1371377 := bstep (se 2 (by rfl) ⟨514266, by rfl⟩ : syracuseStep 1371377 = 1028533) B1028533
theorem B814323 : Blo 810345 814323 := bstep (se 1 (by rfl) ⟨610742, by rfl⟩ : syracuseStep 814323 = 1221485) B1221485
theorem B814339 : Blo 810345 814339 := bstep (se 1 (by rfl) ⟨610754, by rfl⟩ : syracuseStep 814339 = 1221509) B1221509
theorem B912739 : Blo 810345 912739 := bstep (se 1 (by rfl) ⟨684554, by rfl⟩ : syracuseStep 912739 = 1369109) B1369109
theorem B1371505 : Blo 810345 1371505 := bstep (se 2 (by rfl) ⟨514314, by rfl⟩ : syracuseStep 1371505 = 1028629) B1028629
theorem B1830257 : Blo 810345 1830257 := bstep (se 2 (by rfl) ⟨686346, by rfl⟩ : syracuseStep 1830257 = 1372693) B1372693
theorem B1830275 : Blo 810345 1830275 := bstep (se 1 (by rfl) ⟨1372706, by rfl⟩ : syracuseStep 1830275 = 2745413) B2745413
theorem B2747789 : Blo 810345 2747789 := bstep (se 3 (by rfl) ⟨515210, by rfl⟩ : syracuseStep 2747789 = 1030421) B1030421
theorem B1371539 : Blo 810345 1371539 := bstep (se 1 (by rfl) ⟨1028654, by rfl⟩ : syracuseStep 1371539 = 2057309) B2057309
theorem B2747843 : Blo 810345 2747843 := bstep (se 1 (by rfl) ⟨2060882, by rfl⟩ : syracuseStep 2747843 = 4121765) B4121765
theorem B10415587 : Blo 810345 10415587 := bstep (se 1 (by rfl) ⟨7811690, by rfl⟩ : syracuseStep 10415587 = 15623381) B15623381
theorem B912883 : Blo 810345 912883 := bstep (se 1 (by rfl) ⟨684662, by rfl⟩ : syracuseStep 912883 = 1369325) B1369325
theorem B6581773 : Blo 810345 6581773 := bstep (se 3 (by rfl) ⟨1234082, by rfl⟩ : syracuseStep 6581773 = 2468165) B2468165
theorem B1371667 : Blo 810345 1371667 := bstep (se 1 (by rfl) ⟨1028750, by rfl⟩ : syracuseStep 1371667 = 2057501) B2057501
theorem B5205539 : Blo 810345 5205539 := bstep (se 1 (by rfl) ⟨3904154, by rfl⟩ : syracuseStep 5205539 = 7808309) B7808309
theorem B913027 : Blo 810345 913027 := bstep (se 1 (by rfl) ⟨684770, by rfl⟩ : syracuseStep 913027 = 1369541) B1369541
theorem B1732241 : Blo 810345 1732241 := bstep (se 2 (by rfl) ⟨649590, by rfl⟩ : syracuseStep 1732241 = 1299181) B1299181
theorem B1830545 : Blo 810345 1830545 := bstep (se 2 (by rfl) ⟨686454, by rfl⟩ : syracuseStep 1830545 = 1372909) B1372909
theorem B1371809 : Blo 810345 1371809 := bstep (se 2 (by rfl) ⟨514428, by rfl⟩ : syracuseStep 1371809 = 1028857) B1028857
theorem B1732259 : Blo 810345 1732259 := bstep (se 1 (by rfl) ⟨1299194, by rfl⟩ : syracuseStep 1732259 = 2598389) B2598389
theorem B1830563 : Blo 810345 1830563 := bstep (se 1 (by rfl) ⟨1372922, by rfl⟩ : syracuseStep 1830563 = 2745845) B2745845
theorem B3468977 : Blo 810345 3468977 := bstep (se 2 (by rfl) ⟨1300866, by rfl⟩ : syracuseStep 3468977 = 2601733) B2601733
theorem B2748113 : Blo 810345 2748113 := bstep (se 2 (by rfl) ⟨1030542, by rfl⟩ : syracuseStep 2748113 = 2061085) B2061085
theorem B3469027 : Blo 810345 3469027 := bstep (se 1 (by rfl) ⟨2601770, by rfl⟩ : syracuseStep 3469027 = 5203541) B5203541
theorem B913171 : Blo 810345 913171 := bstep (se 1 (by rfl) ⟨684878, by rfl⟩ : syracuseStep 913171 = 1369757) B1369757
theorem B1371937 : Blo 810345 1371937 := bstep (se 2 (by rfl) ⟨514476, by rfl⟩ : syracuseStep 1371937 = 1028953) B1028953
theorem B1371971 : Blo 810345 1371971 := bstep (se 1 (by rfl) ⟨1028978, by rfl⟩ : syracuseStep 1371971 = 2057957) B2057957
theorem B2060113 : Blo 810345 2060113 := bstep (se 2 (by rfl) ⟨772542, by rfl⟩ : syracuseStep 2060113 = 1545085) B1545085
theorem B913315 : Blo 810345 913315 := bstep (se 1 (by rfl) ⟨684986, by rfl⟩ : syracuseStep 913315 = 1369973) B1369973
theorem B1830833 : Blo 810345 1830833 := bstep (se 2 (by rfl) ⟨686562, by rfl⟩ : syracuseStep 1830833 = 1373125) B1373125
theorem B1372099 : Blo 810345 1372099 := bstep (se 1 (by rfl) ⟨1029074, by rfl⟩ : syracuseStep 1372099 = 2058149) B2058149
theorem B1830851 : Blo 810345 1830851 := bstep (se 1 (by rfl) ⟨1373138, by rfl⟩ : syracuseStep 1830851 = 2746277) B2746277
theorem B1044419 : Blo 810345 1044419 := bstep (se 1 (by rfl) ⟨783314, by rfl⟩ : syracuseStep 1044419 = 1566629) B1566629
theorem B913459 : Blo 810345 913459 := bstep (se 1 (by rfl) ⟨685094, by rfl⟩ : syracuseStep 913459 = 1370189) B1370189
theorem B1372241 : Blo 810345 1372241 := bstep (se 2 (by rfl) ⟨514590, by rfl⟩ : syracuseStep 1372241 = 1029181) B1029181
theorem B2060387 : Blo 810345 2060387 := bstep (se 1 (by rfl) ⟨1545290, by rfl⟩ : syracuseStep 2060387 = 3090581) B3090581
theorem B913603 : Blo 810345 913603 := bstep (se 1 (by rfl) ⟨685202, by rfl⟩ : syracuseStep 913603 = 1370405) B1370405
theorem B1372369 : Blo 810345 1372369 := bstep (se 2 (by rfl) ⟨514638, by rfl⟩ : syracuseStep 1372369 = 1029277) B1029277
theorem B1831121 : Blo 810345 1831121 := bstep (se 2 (by rfl) ⟨686670, by rfl⟩ : syracuseStep 1831121 = 1373341) B1373341
theorem B1831139 : Blo 810345 1831139 := bstep (se 1 (by rfl) ⟨1373354, by rfl⟩ : syracuseStep 1831139 = 2746709) B2746709
theorem B1372403 : Blo 810345 1372403 := bstep (se 1 (by rfl) ⟨1029302, by rfl⟩ : syracuseStep 1372403 = 2058605) B2058605
theorem B2060579 : Blo 810345 2060579 := bstep (se 1 (by rfl) ⟨1545434, by rfl⟩ : syracuseStep 2060579 = 3090869) B3090869
theorem B913747 : Blo 810345 913747 := bstep (se 1 (by rfl) ⟨685310, by rfl⟩ : syracuseStep 913747 = 1370621) B1370621
theorem B1372531 : Blo 810345 1372531 := bstep (se 1 (by rfl) ⟨1029398, by rfl⟩ : syracuseStep 1372531 = 2058797) B2058797
theorem B913891 : Blo 810345 913891 := bstep (se 1 (by rfl) ⟨685418, by rfl⟩ : syracuseStep 913891 = 1370837) B1370837
theorem B1831409 : Blo 810345 1831409 := bstep (se 2 (by rfl) ⟨686778, by rfl⟩ : syracuseStep 1831409 = 1373557) B1373557
theorem B1372673 : Blo 810345 1372673 := bstep (se 2 (by rfl) ⟨514752, by rfl⟩ : syracuseStep 1372673 = 1029505) B1029505
theorem B1831427 : Blo 810345 1831427 := bstep (se 1 (by rfl) ⟨1373570, by rfl⟩ : syracuseStep 1831427 = 2747141) B2747141
theorem B4682245 : Blo 810345 4682245 := bstep (se 4 (by rfl) ⟨438960, by rfl⟩ : syracuseStep 4682245 = 877921) B877921
theorem B11301389 : Blo 810345 11301389 := bstep (se 3 (by rfl) ⟨2119010, by rfl⟩ : syracuseStep 11301389 = 4238021) B4238021
theorem B914035 : Blo 810345 914035 := bstep (se 1 (by rfl) ⟨685526, by rfl⟩ : syracuseStep 914035 = 1371053) B1371053
theorem B1372801 : Blo 810345 1372801 := bstep (se 2 (by rfl) ⟨514800, by rfl⟩ : syracuseStep 1372801 = 1029601) B1029601
theorem B1372835 : Blo 810345 1372835 := bstep (se 1 (by rfl) ⟨1029626, by rfl⟩ : syracuseStep 1372835 = 2059253) B2059253
theorem B1405649 : Blo 810345 1405649 := bstep (se 2 (by rfl) ⟨527118, by rfl⟩ : syracuseStep 1405649 = 1054237) B1054237
theorem B914179 : Blo 810345 914179 := bstep (se 1 (by rfl) ⟨685634, by rfl⟩ : syracuseStep 914179 = 1371269) B1371269
theorem B1831697 : Blo 810345 1831697 := bstep (se 2 (by rfl) ⟨686886, by rfl⟩ : syracuseStep 1831697 = 1373773) B1373773
theorem B1372963 : Blo 810345 1372963 := bstep (se 1 (by rfl) ⟨1029722, by rfl⟩ : syracuseStep 1372963 = 2059445) B2059445
theorem B1831715 : Blo 810345 1831715 := bstep (se 1 (by rfl) ⟨1373786, by rfl⟩ : syracuseStep 1831715 = 2747573) B2747573
theorem B914323 : Blo 810345 914323 := bstep (se 1 (by rfl) ⟨685742, by rfl⟩ : syracuseStep 914323 = 1371485) B1371485
theorem B1373105 : Blo 810345 1373105 := bstep (se 2 (by rfl) ⟨514914, by rfl⟩ : syracuseStep 1373105 = 1029829) B1029829
theorem B914467 : Blo 810345 914467 := bstep (se 1 (by rfl) ⟨685850, by rfl⟩ : syracuseStep 914467 = 1371701) B1371701
theorem B1373233 : Blo 810345 1373233 := bstep (se 2 (by rfl) ⟨514962, by rfl⟩ : syracuseStep 1373233 = 1029925) B1029925
theorem B1831985 : Blo 810345 1831985 := bstep (se 2 (by rfl) ⟨686994, by rfl⟩ : syracuseStep 1831985 = 1373989) B1373989
theorem B1832003 : Blo 810345 1832003 := bstep (se 1 (by rfl) ⟨1374002, by rfl⟩ : syracuseStep 1832003 = 2748005) B2748005
theorem B1373267 : Blo 810345 1373267 := bstep (se 1 (by rfl) ⟨1029950, by rfl⟩ : syracuseStep 1373267 = 2059901) B2059901
theorem B3077261 : Blo 810345 3077261 := bstep (se 3 (by rfl) ⟨576986, by rfl⟩ : syracuseStep 3077261 = 1153973) B1153973
theorem B4388003 : Blo 810345 4388003 := bstep (se 1 (by rfl) ⟨3291002, by rfl⟩ : syracuseStep 4388003 = 6582005) B6582005
theorem B914611 : Blo 810345 914611 := bstep (se 1 (by rfl) ⟨685958, by rfl⟩ : syracuseStep 914611 = 1371917) B1371917
theorem B1373395 : Blo 810345 1373395 := bstep (se 1 (by rfl) ⟨1030046, by rfl⟩ : syracuseStep 1373395 = 2060093) B2060093
theorem B914755 : Blo 810345 914755 := bstep (se 1 (by rfl) ⟨686066, by rfl⟩ : syracuseStep 914755 = 1372133) B1372133
theorem B1832273 : Blo 810345 1832273 := bstep (se 2 (by rfl) ⟨687102, by rfl⟩ : syracuseStep 1832273 = 1374205) B1374205
theorem B1373537 : Blo 810345 1373537 := bstep (se 2 (by rfl) ⟨515076, by rfl⟩ : syracuseStep 1373537 = 1030153) B1030153
theorem B4388195 : Blo 810345 4388195 := bstep (se 1 (by rfl) ⟨3291146, by rfl⟩ : syracuseStep 4388195 = 6582293) B6582293
theorem B914899 : Blo 810345 914899 := bstep (se 1 (by rfl) ⟨686174, by rfl⟩ : syracuseStep 914899 = 1372349) B1372349
theorem B1373665 : Blo 810345 1373665 := bstep (se 2 (by rfl) ⟨515124, by rfl⟩ : syracuseStep 1373665 = 1030249) B1030249
theorem B1373699 : Blo 810345 1373699 := bstep (se 1 (by rfl) ⟨1030274, by rfl⟩ : syracuseStep 1373699 = 2060549) B2060549
theorem B9369101 : Blo 810345 9369101 := bstep (se 3 (by rfl) ⟨1756706, by rfl⟩ : syracuseStep 9369101 = 3513413) B3513413
theorem B4945457 : Blo 810345 4945457 := bstep (se 2 (by rfl) ⟨1854546, by rfl⟩ : syracuseStep 4945457 = 3709093) B3709093
theorem B915043 : Blo 810345 915043 := bstep (se 1 (by rfl) ⟨686282, by rfl⟩ : syracuseStep 915043 = 1372565) B1372565
theorem B1734257 : Blo 810345 1734257 := bstep (se 2 (by rfl) ⟨650346, by rfl⟩ : syracuseStep 1734257 = 1300693) B1300693
theorem B1373827 : Blo 810345 1373827 := bstep (se 1 (by rfl) ⟨1030370, by rfl⟩ : syracuseStep 1373827 = 2060741) B2060741
theorem B4159117 : Blo 810345 4159117 := bstep (se 3 (by rfl) ⟨779834, by rfl⟩ : syracuseStep 4159117 = 1559669) B1559669
theorem B915187 : Blo 810345 915187 := bstep (se 1 (by rfl) ⟨686390, by rfl⟩ : syracuseStep 915187 = 1372781) B1372781
theorem B2193169 : Blo 810345 2193169 := bstep (se 2 (by rfl) ⟨822438, by rfl⟩ : syracuseStep 2193169 = 1644877) B1644877
theorem B1373969 : Blo 810345 1373969 := bstep (se 2 (by rfl) ⟨515238, by rfl⟩ : syracuseStep 1373969 = 1030477) B1030477
theorem B915331 : Blo 810345 915331 := bstep (se 1 (by rfl) ⟨686498, by rfl⟩ : syracuseStep 915331 = 1372997) B1372997
theorem B1374097 : Blo 810345 1374097 := bstep (se 2 (by rfl) ⟨515286, by rfl⟩ : syracuseStep 1374097 = 1030573) B1030573
theorem B1374131 : Blo 810345 1374131 := bstep (se 1 (by rfl) ⟨1030598, by rfl⟩ : syracuseStep 1374131 = 2061197) B2061197
theorem B915475 : Blo 810345 915475 := bstep (se 1 (by rfl) ⟨686606, by rfl⟩ : syracuseStep 915475 = 1373213) B1373213
theorem B3471437 : Blo 810345 3471437 := bstep (se 3 (by rfl) ⟨650894, by rfl⟩ : syracuseStep 3471437 = 1301789) B1301789
theorem B1734787 : Blo 810345 1734787 := bstep (se 1 (by rfl) ⟨1301090, by rfl⟩ : syracuseStep 1734787 = 2602181) B2602181
theorem B915619 : Blo 810345 915619 := bstep (se 1 (by rfl) ⟨686714, by rfl⟩ : syracuseStep 915619 = 1373429) B1373429
theorem B915763 : Blo 810345 915763 := bstep (se 1 (by rfl) ⟨686822, by rfl⟩ : syracuseStep 915763 = 1373645) B1373645
theorem B915907 : Blo 810345 915907 := bstep (se 1 (by rfl) ⟨686930, by rfl⟩ : syracuseStep 915907 = 1373861) B1373861
theorem B2783693 : Blo 810345 2783693 := bstep (se 3 (by rfl) ⟨521942, by rfl⟩ : syracuseStep 2783693 = 1043885) B1043885
theorem B916051 : Blo 810345 916051 := bstep (se 1 (by rfl) ⟨687038, by rfl⟩ : syracuseStep 916051 = 1374077) B1374077
theorem B1538851 : Blo 810345 1538851 := bstep (se 1 (by rfl) ⟨1154138, by rfl⟩ : syracuseStep 1538851 = 2308277) B2308277
theorem B11140021 : Blo 810345 11140021 := bstep (se 5 (by rfl) ⟨522188, by rfl⟩ : syracuseStep 11140021 = 1044377) B1044377
theorem B2194445 : Blo 810345 2194445 := bstep (se 3 (by rfl) ⟨411458, by rfl⟩ : syracuseStep 2194445 = 822917) B822917
theorem B4947085 : Blo 810345 4947085 := bstep (se 3 (by rfl) ⟨927578, by rfl⟩ : syracuseStep 4947085 = 1855157) B1855157
theorem B1539299 : Blo 810345 1539299 := bstep (se 1 (by rfl) ⟨1154474, by rfl⟩ : syracuseStep 1539299 = 2308949) B2308949
theorem B1408369 : Blo 810345 1408369 := bstep (se 2 (by rfl) ⟨528138, by rfl⟩ : syracuseStep 1408369 = 1056277) B1056277
theorem B1539587 : Blo 810345 1539587 := bstep (se 1 (by rfl) ⟨1154690, by rfl⟩ : syracuseStep 1539587 = 2309381) B2309381
theorem B1736273 : Blo 810345 1736273 := bstep (se 2 (by rfl) ⟨651102, by rfl⟩ : syracuseStep 1736273 = 1302205) B1302205
theorem B1736291 : Blo 810345 1736291 := bstep (se 1 (by rfl) ⟨1302218, by rfl⟩ : syracuseStep 1736291 = 2604437) B2604437
theorem B2817677 : Blo 810345 2817677 := bstep (se 3 (by rfl) ⟨528314, by rfl⟩ : syracuseStep 2817677 = 1056629) B1056629
theorem B4620037 : Blo 810345 4620037 := bstep (se 4 (by rfl) ⟨433128, by rfl⟩ : syracuseStep 4620037 = 866257) B866257
theorem B2228003 : Blo 810345 2228003 := bstep (se 1 (by rfl) ⟨1671002, by rfl⟩ : syracuseStep 2228003 = 3342005) B3342005
theorem B2195309 : Blo 810345 2195309 := bstep (se 3 (by rfl) ⟨411620, by rfl⟩ : syracuseStep 2195309 = 823241) B823241
theorem B3080177 : Blo 810345 3080177 := bstep (se 2 (by rfl) ⟨1155066, by rfl⟩ : syracuseStep 3080177 = 2310133) B2310133
theorem B1540225 : Blo 810345 1540225 := bstep (se 2 (by rfl) ⟨577584, by rfl⟩ : syracuseStep 1540225 = 1155169) B1155169
theorem B6160535 : Blo 810345 6160535 := bstep (se 1 (by rfl) ⟨4620401, by rfl⟩ : syracuseStep 6160535 = 9240803) B9240803
theorem B5865689 : Blo 810345 5865689 := bstep (se 2 (by rfl) ⟨2199633, by rfl⟩ : syracuseStep 5865689 = 4399267) B4399267
theorem B35553649 : Blo 810345 35553649 := bstep (se 2 (by rfl) ⟨13332618, by rfl⟩ : syracuseStep 35553649 = 26665237) B26665237
theorem B10551883 : Blo 810345 10551883 := bstep (se 1 (by rfl) ⟨7913912, by rfl⟩ : syracuseStep 10551883 = 15827825) B15827825
theorem B4948573 : Blo 810345 4948573 := bstep (se 3 (by rfl) ⟨927857, by rfl⟩ : syracuseStep 4948573 = 1855715) B1855715
theorem B1540939 : Blo 810345 1540939 := bstep (se 1 (by rfl) ⟨1155704, by rfl⟩ : syracuseStep 1540939 = 2311409) B2311409
theorem B6030155 : Blo 810345 6030155 := bstep (se 1 (by rfl) ⟨4522616, by rfl⟩ : syracuseStep 6030155 = 9045233) B9045233
theorem B1541015 : Blo 810345 1541015 := bstep (se 1 (by rfl) ⟨1155761, by rfl⟩ : syracuseStep 1541015 = 2311523) B2311523
theorem B3081347 : Blo 810345 3081347 := bstep (se 1 (by rfl) ⟨2311010, by rfl⟩ : syracuseStep 3081347 = 4622021) B4622021
theorem B3081361 : Blo 810345 3081361 := bstep (se 2 (by rfl) ⟨1155510, by rfl⟩ : syracuseStep 3081361 = 2311021) B2311021
theorem B1737931 : Blo 810345 1737931 := bstep (se 1 (by rfl) ⟨1303448, by rfl⟩ : syracuseStep 1737931 = 2606897) B2606897
theorem B3474733 : Blo 810345 3474733 := bstep (se 3 (by rfl) ⟨651512, by rfl⟩ : syracuseStep 3474733 = 1303025) B1303025
theorem B5211485 : Blo 810345 5211485 := bstep (se 3 (by rfl) ⟨977153, by rfl⟩ : syracuseStep 5211485 = 1954307) B1954307
theorem B13206883 : Blo 810345 13206883 := bstep (se 1 (by rfl) ⟨9905162, by rfl⟩ : syracuseStep 13206883 = 19810325) B19810325
theorem B12387761 : Blo 810345 12387761 := bstep (se 2 (by rfl) ⟨4645410, by rfl⟩ : syracuseStep 12387761 = 9290821) B9290821
theorem B3081665 : Blo 810345 3081665 := bstep (se 2 (by rfl) ⟨1155624, by rfl⟩ : syracuseStep 3081665 = 2311249) B2311249
theorem B1738187 : Blo 810345 1738187 := bstep (se 1 (by rfl) ⟨1303640, by rfl⟩ : syracuseStep 1738187 = 2607281) B2607281
theorem B1541683 : Blo 810345 1541683 := bstep (se 1 (by rfl) ⟨1156262, by rfl⟩ : syracuseStep 1541683 = 2312525) B2312525
theorem B2229811 : Blo 810345 2229811 := bstep (se 1 (by rfl) ⟨1672358, by rfl⟩ : syracuseStep 2229811 = 3344717) B3344717
theorem B3475075 : Blo 810345 3475075 := bstep (se 1 (by rfl) ⟨2606306, by rfl⟩ : syracuseStep 3475075 = 5212613) B5212613
theorem B1541911 : Blo 810345 1541911 := bstep (se 1 (by rfl) ⟨1156433, by rfl⟩ : syracuseStep 1541911 = 2312867) B2312867
theorem B1542017 : Blo 810345 1542017 := bstep (se 2 (by rfl) ⟨578256, by rfl⟩ : syracuseStep 1542017 = 1156513) B1156513
theorem B1542169 : Blo 810345 1542169 := bstep (se 2 (by rfl) ⟨578313, by rfl⟩ : syracuseStep 1542169 = 1156627) B1156627
theorem B3082333 : Blo 810345 3082333 := bstep (se 3 (by rfl) ⟨577937, by rfl⟩ : syracuseStep 3082333 = 1155875) B1155875
theorem B1739161 : Blo 810345 1739161 := bstep (se 2 (by rfl) ⟨652185, by rfl⟩ : syracuseStep 1739161 = 1304371) B1304371
theorem B4622771 : Blo 810345 4622771 := bstep (se 1 (by rfl) ⟨3467078, by rfl⟩ : syracuseStep 4622771 = 6934157) B6934157
theorem B3476033 : Blo 810345 3476033 := bstep (se 2 (by rfl) ⟨1303512, by rfl⟩ : syracuseStep 3476033 = 2607025) B2607025
theorem B2198423 : Blo 810345 2198423 := bstep (se 1 (by rfl) ⟨1648817, by rfl⟩ : syracuseStep 2198423 = 3297635) B3297635
theorem B1215563 : Blo 810345 1215563 := bstep (se 1 (by rfl) ⟨911672, by rfl⟩ : syracuseStep 1215563 = 1823345) B1823345
theorem B1215575 : Blo 810345 1215575 := bstep (se 1 (by rfl) ⟨911681, by rfl⟩ : syracuseStep 1215575 = 1823363) B1823363
theorem B10390679 : Blo 810345 10390679 := bstep (se 1 (by rfl) ⟨7793009, by rfl⟩ : syracuseStep 10390679 = 15586019) B15586019
theorem B1215641 : Blo 810345 1215641 := bstep (se 2 (by rfl) ⟨455865, by rfl⟩ : syracuseStep 1215641 = 911731) B911731
theorem B1215755 : Blo 810345 1215755 := bstep (se 1 (by rfl) ⟨911816, by rfl⟩ : syracuseStep 1215755 = 1823633) B1823633
theorem B1215767 : Blo 810345 1215767 := bstep (se 1 (by rfl) ⟨911825, by rfl⟩ : syracuseStep 1215767 = 1823651) B1823651
theorem B1543475 : Blo 810345 1543475 := bstep (se 1 (by rfl) ⟨1157606, by rfl⟩ : syracuseStep 1543475 = 2315213) B2315213
theorem B1215833 : Blo 810345 1215833 := bstep (se 2 (by rfl) ⟨455937, by rfl⟩ : syracuseStep 1215833 = 911875) B911875
theorem B3083609 : Blo 810345 3083609 := bstep (se 2 (by rfl) ⟨1156353, by rfl⟩ : syracuseStep 3083609 = 2312707) B2312707
theorem B1215947 : Blo 810345 1215947 := bstep (se 1 (by rfl) ⟨911960, by rfl⟩ : syracuseStep 1215947 = 1823921) B1823921
theorem B1543627 : Blo 810345 1543627 := bstep (se 1 (by rfl) ⟨1157720, by rfl⟩ : syracuseStep 1543627 = 2315441) B2315441
theorem B1215959 : Blo 810345 1215959 := bstep (se 1 (by rfl) ⟨911969, by rfl⟩ : syracuseStep 1215959 = 1823939) B1823939
theorem B1216025 : Blo 810345 1216025 := bstep (se 2 (by rfl) ⟨456009, by rfl⟩ : syracuseStep 1216025 = 912019) B912019
theorem B11701853 : Blo 810345 11701853 := bstep (se 3 (by rfl) ⟨2194097, by rfl⟩ : syracuseStep 11701853 = 4388195) B4388195
theorem B1216139 : Blo 810345 1216139 := bstep (se 1 (by rfl) ⟨912104, by rfl⟩ : syracuseStep 1216139 = 1824209) B1824209
theorem B1216151 : Blo 810345 1216151 := bstep (se 1 (by rfl) ⟨912113, by rfl⟩ : syracuseStep 1216151 = 1824227) B1824227
theorem B1216217 : Blo 810345 1216217 := bstep (se 2 (by rfl) ⟨456081, by rfl⟩ : syracuseStep 1216217 = 912163) B912163
theorem B1543961 : Blo 810345 1543961 := bstep (se 2 (by rfl) ⟨578985, by rfl⟩ : syracuseStep 1543961 = 1157971) B1157971
theorem B1216331 : Blo 810345 1216331 := bstep (se 1 (by rfl) ⟨912248, by rfl⟩ : syracuseStep 1216331 = 1824497) B1824497
theorem B1216343 : Blo 810345 1216343 := bstep (se 1 (by rfl) ⟨912257, by rfl⟩ : syracuseStep 1216343 = 1824515) B1824515
theorem B4624229 : Blo 810345 4624229 := bstep (se 4 (by rfl) ⟨433521, by rfl⟩ : syracuseStep 4624229 = 867043) B867043
theorem B1216409 : Blo 810345 1216409 := bstep (se 2 (by rfl) ⟨456153, by rfl⟩ : syracuseStep 1216409 = 912307) B912307
theorem B3477451 : Blo 810345 3477451 := bstep (se 1 (by rfl) ⟨2608088, by rfl⟩ : syracuseStep 3477451 = 5216177) B5216177
theorem B1216523 : Blo 810345 1216523 := bstep (se 1 (by rfl) ⟨912392, by rfl⟩ : syracuseStep 1216523 = 1824785) B1824785
theorem B1216535 : Blo 810345 1216535 := bstep (se 1 (by rfl) ⟨912401, by rfl⟩ : syracuseStep 1216535 = 1824803) B1824803
theorem B5214253 : Blo 810345 5214253 := bstep (se 3 (by rfl) ⟨977672, by rfl⟩ : syracuseStep 5214253 = 1955345) B1955345
theorem B1216601 : Blo 810345 1216601 := bstep (se 2 (by rfl) ⟨456225, by rfl⟩ : syracuseStep 1216601 = 912451) B912451
theorem B1216715 : Blo 810345 1216715 := bstep (se 1 (by rfl) ⟨912536, by rfl⟩ : syracuseStep 1216715 = 1825073) B1825073
theorem B1216727 : Blo 810345 1216727 := bstep (se 1 (by rfl) ⟨912545, by rfl⟩ : syracuseStep 1216727 = 1825091) B1825091
theorem B3477725 : Blo 810345 3477725 := bstep (se 3 (by rfl) ⟨652073, by rfl⟩ : syracuseStep 3477725 = 1304147) B1304147
theorem B1216793 : Blo 810345 1216793 := bstep (se 2 (by rfl) ⟨456297, by rfl⟩ : syracuseStep 1216793 = 912595) B912595
theorem B4624685 : Blo 810345 4624685 := bstep (se 3 (by rfl) ⟨867128, by rfl⟩ : syracuseStep 4624685 = 1734257) B1734257
theorem B2199883 : Blo 810345 2199883 := bstep (se 1 (by rfl) ⟨1649912, by rfl⟩ : syracuseStep 2199883 = 3299825) B3299825
theorem B1216907 : Blo 810345 1216907 := bstep (se 1 (by rfl) ⟨912680, by rfl⟩ : syracuseStep 1216907 = 1825361) B1825361
theorem B1216919 : Blo 810345 1216919 := bstep (se 1 (by rfl) ⟨912689, by rfl⟩ : syracuseStep 1216919 = 1825379) B1825379
theorem B1544599 : Blo 810345 1544599 := bstep (se 1 (by rfl) ⟨1158449, by rfl⟩ : syracuseStep 1544599 = 2316899) B2316899
theorem B1216985 : Blo 810345 1216985 := bstep (se 2 (by rfl) ⟨456369, by rfl⟩ : syracuseStep 1216985 = 912739) B912739
theorem B1217099 : Blo 810345 1217099 := bstep (se 1 (by rfl) ⟨912824, by rfl⟩ : syracuseStep 1217099 = 1825649) B1825649
theorem B1217111 : Blo 810345 1217111 := bstep (se 1 (by rfl) ⟨912833, by rfl⟩ : syracuseStep 1217111 = 1825667) B1825667
theorem B1217177 : Blo 810345 1217177 := bstep (se 2 (by rfl) ⟨456441, by rfl⟩ : syracuseStep 1217177 = 912883) B912883
theorem B4690649 : Blo 810345 4690649 := bstep (se 2 (by rfl) ⟨1758993, by rfl⟩ : syracuseStep 4690649 = 3517987) B3517987
theorem B1217291 : Blo 810345 1217291 := bstep (se 1 (by rfl) ⟨912968, by rfl⟩ : syracuseStep 1217291 = 1825937) B1825937
theorem B1217303 : Blo 810345 1217303 := bstep (se 1 (by rfl) ⟨912977, by rfl⟩ : syracuseStep 1217303 = 1825955) B1825955
theorem B1217369 : Blo 810345 1217369 := bstep (se 2 (by rfl) ⟨456513, by rfl⟩ : syracuseStep 1217369 = 913027) B913027
theorem B3085235 : Blo 810345 3085235 := bstep (se 1 (by rfl) ⟨2313926, by rfl⟩ : syracuseStep 3085235 = 4627853) B4627853
theorem B3085249 : Blo 810345 3085249 := bstep (se 2 (by rfl) ⟨1156968, by rfl⟩ : syracuseStep 3085249 = 2313937) B2313937
theorem B59413445 : Blo 810345 59413445 := bstep (se 4 (by rfl) ⟨5570010, by rfl⟩ : syracuseStep 59413445 = 11140021) B11140021
theorem B1217483 : Blo 810345 1217483 := bstep (se 1 (by rfl) ⟨913112, by rfl⟩ : syracuseStep 1217483 = 1826225) B1826225
theorem B1217495 : Blo 810345 1217495 := bstep (se 1 (by rfl) ⟨913121, by rfl⟩ : syracuseStep 1217495 = 1826243) B1826243
theorem B4625369 : Blo 810345 4625369 := bstep (se 2 (by rfl) ⟨1734513, by rfl⟩ : syracuseStep 4625369 = 3469027) B3469027
theorem B1217561 : Blo 810345 1217561 := bstep (se 2 (by rfl) ⟨456585, by rfl⟩ : syracuseStep 1217561 = 913171) B913171
theorem B1217675 : Blo 810345 1217675 := bstep (se 1 (by rfl) ⟨913256, by rfl⟩ : syracuseStep 1217675 = 1826513) B1826513
theorem B1217687 : Blo 810345 1217687 := bstep (se 1 (by rfl) ⟨913265, by rfl⟩ : syracuseStep 1217687 = 1826531) B1826531
theorem B2921645 : Blo 810345 2921645 := bstep (se 3 (by rfl) ⟨547808, by rfl⟩ : syracuseStep 2921645 = 1095617) B1095617
theorem B1545419 : Blo 810345 1545419 := bstep (se 1 (by rfl) ⟨1159064, by rfl⟩ : syracuseStep 1545419 = 2318129) B2318129
theorem B1217753 : Blo 810345 1217753 := bstep (se 2 (by rfl) ⟨456657, by rfl⟩ : syracuseStep 1217753 = 913315) B913315
theorem B1545473 : Blo 810345 1545473 := bstep (se 2 (by rfl) ⟨579552, by rfl⟩ : syracuseStep 1545473 = 1159105) B1159105
theorem B2921773 : Blo 810345 2921773 := bstep (se 3 (by rfl) ⟨547832, by rfl⟩ : syracuseStep 2921773 = 1095665) B1095665
theorem B1217867 : Blo 810345 1217867 := bstep (se 1 (by rfl) ⟨913400, by rfl⟩ : syracuseStep 1217867 = 1826801) B1826801
theorem B1217879 : Blo 810345 1217879 := bstep (se 1 (by rfl) ⟨913409, by rfl⟩ : syracuseStep 1217879 = 1826819) B1826819
theorem B1217945 : Blo 810345 1217945 := bstep (se 2 (by rfl) ⟨456729, by rfl⟩ : syracuseStep 1217945 = 913459) B913459
theorem B12490163 : Blo 810345 12490163 := bstep (se 1 (by rfl) ⟨9367622, by rfl⟩ : syracuseStep 12490163 = 18735245) B18735245
theorem B1218059 : Blo 810345 1218059 := bstep (se 1 (by rfl) ⟨913544, by rfl⟩ : syracuseStep 1218059 = 1827089) B1827089
theorem B1218071 : Blo 810345 1218071 := bstep (se 1 (by rfl) ⟨913553, by rfl⟩ : syracuseStep 1218071 = 1827107) B1827107
theorem B4396589 : Blo 810345 4396589 := bstep (se 3 (by rfl) ⟨824360, by rfl⟩ : syracuseStep 4396589 = 1648721) B1648721
theorem B1218137 : Blo 810345 1218137 := bstep (se 2 (by rfl) ⟨456801, by rfl⟩ : syracuseStep 1218137 = 913603) B913603
theorem B3905117 : Blo 810345 3905117 := bstep (se 3 (by rfl) ⟨732209, by rfl⟩ : syracuseStep 3905117 = 1464419) B1464419
theorem B1218251 : Blo 810345 1218251 := bstep (se 1 (by rfl) ⟨913688, by rfl⟩ : syracuseStep 1218251 = 1827377) B1827377
theorem B1218263 : Blo 810345 1218263 := bstep (se 1 (by rfl) ⟨913697, by rfl⟩ : syracuseStep 1218263 = 1827395) B1827395
theorem B1218329 : Blo 810345 1218329 := bstep (se 2 (by rfl) ⟨456873, by rfl⟩ : syracuseStep 1218329 = 913747) B913747
theorem B1218443 : Blo 810345 1218443 := bstep (se 1 (by rfl) ⟨913832, by rfl⟩ : syracuseStep 1218443 = 1827665) B1827665
theorem B1218455 : Blo 810345 1218455 := bstep (se 1 (by rfl) ⟨913841, by rfl⟩ : syracuseStep 1218455 = 1827683) B1827683
theorem B1218521 : Blo 810345 1218521 := bstep (se 2 (by rfl) ⟨456945, by rfl⟩ : syracuseStep 1218521 = 913891) B913891
theorem B1218635 : Blo 810345 1218635 := bstep (se 1 (by rfl) ⟨913976, by rfl⟩ : syracuseStep 1218635 = 1827953) B1827953
theorem B1218647 : Blo 810345 1218647 := bstep (se 1 (by rfl) ⟨913985, by rfl⟩ : syracuseStep 1218647 = 1827971) B1827971
theorem B1316953 : Blo 810345 1316953 := bstep (se 2 (by rfl) ⟨493857, by rfl⟩ : syracuseStep 1316953 = 987715) B987715
theorem B1218713 : Blo 810345 1218713 := bstep (se 2 (by rfl) ⟨457017, by rfl⟩ : syracuseStep 1218713 = 914035) B914035
theorem B1218827 : Blo 810345 1218827 := bstep (se 1 (by rfl) ⟨914120, by rfl⟩ : syracuseStep 1218827 = 1828241) B1828241
theorem B1218839 : Blo 810345 1218839 := bstep (se 1 (by rfl) ⟨914129, by rfl⟩ : syracuseStep 1218839 = 1828259) B1828259
theorem B1218905 : Blo 810345 1218905 := bstep (se 2 (by rfl) ⟨457089, by rfl⟩ : syracuseStep 1218905 = 914179) B914179
theorem B5216663 : Blo 810345 5216663 := bstep (se 1 (by rfl) ⟨3912497, by rfl⟩ : syracuseStep 5216663 = 7824995) B7824995
theorem B1219019 : Blo 810345 1219019 := bstep (se 1 (by rfl) ⟨914264, by rfl⟩ : syracuseStep 1219019 = 1828529) B1828529
theorem B1219031 : Blo 810345 1219031 := bstep (se 1 (by rfl) ⟨914273, by rfl⟩ : syracuseStep 1219031 = 1828547) B1828547
theorem B1219097 : Blo 810345 1219097 := bstep (se 2 (by rfl) ⟨457161, by rfl⟩ : syracuseStep 1219097 = 914323) B914323
theorem B1219211 : Blo 810345 1219211 := bstep (se 1 (by rfl) ⟨914408, by rfl⟩ : syracuseStep 1219211 = 1828817) B1828817
theorem B1219223 : Blo 810345 1219223 := bstep (se 1 (by rfl) ⟨914417, by rfl⟩ : syracuseStep 1219223 = 1828835) B1828835
theorem B989911 : Blo 810345 989911 := bstep (se 1 (by rfl) ⟨742433, by rfl⟩ : syracuseStep 989911 = 1484867) B1484867
theorem B1219289 : Blo 810345 1219289 := bstep (se 2 (by rfl) ⟨457233, by rfl⟩ : syracuseStep 1219289 = 914467) B914467
theorem B1219403 : Blo 810345 1219403 := bstep (se 1 (by rfl) ⟨914552, by rfl⟩ : syracuseStep 1219403 = 1829105) B1829105
theorem B3087179 : Blo 810345 3087179 := bstep (se 1 (by rfl) ⟨2315384, by rfl⟩ : syracuseStep 3087179 = 4630769) B4630769
theorem B1219415 : Blo 810345 1219415 := bstep (se 1 (by rfl) ⟨914561, by rfl⟩ : syracuseStep 1219415 = 1829123) B1829123
theorem B3087193 : Blo 810345 3087193 := bstep (se 2 (by rfl) ⟨1157697, by rfl⟩ : syracuseStep 3087193 = 2315395) B2315395
theorem B4397975 : Blo 810345 4397975 := bstep (se 1 (by rfl) ⟨3298481, by rfl⟩ : syracuseStep 4397975 = 6596963) B6596963
theorem B1219481 : Blo 810345 1219481 := bstep (se 2 (by rfl) ⟨457305, by rfl⟩ : syracuseStep 1219481 = 914611) B914611
theorem B1219595 : Blo 810345 1219595 := bstep (se 1 (by rfl) ⟨914696, by rfl⟩ : syracuseStep 1219595 = 1829393) B1829393
theorem B1219607 : Blo 810345 1219607 := bstep (se 1 (by rfl) ⟨914705, by rfl⟩ : syracuseStep 1219607 = 1829411) B1829411
theorem B1645655 : Blo 810345 1645655 := bstep (se 1 (by rfl) ⟨1234241, by rfl⟩ : syracuseStep 1645655 = 2468483) B2468483
theorem B1219673 : Blo 810345 1219673 := bstep (se 2 (by rfl) ⟨457377, by rfl⟩ : syracuseStep 1219673 = 914755) B914755
theorem B1645697 : Blo 810345 1645697 := bstep (se 2 (by rfl) ⟨617136, by rfl⟩ : syracuseStep 1645697 = 1234273) B1234273
theorem B1219787 : Blo 810345 1219787 := bstep (se 1 (by rfl) ⟨914840, by rfl⟩ : syracuseStep 1219787 = 1829681) B1829681
theorem B1219799 : Blo 810345 1219799 := bstep (se 1 (by rfl) ⟨914849, by rfl⟩ : syracuseStep 1219799 = 1829699) B1829699
theorem B1809665 : Blo 810345 1809665 := bstep (se 2 (by rfl) ⟨678624, by rfl⟩ : syracuseStep 1809665 = 1357249) B1357249
theorem B6167825 : Blo 810345 6167825 := bstep (se 2 (by rfl) ⟨2312934, by rfl⟩ : syracuseStep 6167825 = 4625869) B4625869
theorem B1219865 : Blo 810345 1219865 := bstep (se 2 (by rfl) ⟨457449, by rfl⟩ : syracuseStep 1219865 = 914899) B914899
theorem B925015 : Blo 810345 925015 := bstep (se 1 (by rfl) ⟨693761, by rfl⟩ : syracuseStep 925015 = 1387523) B1387523
theorem B1219979 : Blo 810345 1219979 := bstep (se 1 (by rfl) ⟨914984, by rfl⟩ : syracuseStep 1219979 = 1829969) B1829969
theorem B1219991 : Blo 810345 1219991 := bstep (se 1 (by rfl) ⟨914993, by rfl⟩ : syracuseStep 1219991 = 1829987) B1829987
theorem B1318361 : Blo 810345 1318361 := bstep (se 2 (by rfl) ⟨494385, by rfl⟩ : syracuseStep 1318361 = 988771) B988771
theorem B1220057 : Blo 810345 1220057 := bstep (se 2 (by rfl) ⟨457521, by rfl⟩ : syracuseStep 1220057 = 915043) B915043
theorem B1220171 : Blo 810345 1220171 := bstep (se 1 (by rfl) ⟨915128, by rfl⟩ : syracuseStep 1220171 = 1830257) B1830257
theorem B1220183 : Blo 810345 1220183 := bstep (se 1 (by rfl) ⟨915137, by rfl⟩ : syracuseStep 1220183 = 1830275) B1830275
theorem B1220249 : Blo 810345 1220249 := bstep (se 2 (by rfl) ⟨457593, by rfl⟩ : syracuseStep 1220249 = 915187) B915187
theorem B2924225 : Blo 810345 2924225 := bstep (se 2 (by rfl) ⟨1096584, by rfl⟩ : syracuseStep 2924225 = 2193169) B2193169
theorem B1154827 : Blo 810345 1154827 := bstep (se 1 (by rfl) ⟨866120, by rfl⟩ : syracuseStep 1154827 = 1732241) B1732241
theorem B1220363 : Blo 810345 1220363 := bstep (se 1 (by rfl) ⟨915272, by rfl⟩ : syracuseStep 1220363 = 1830545) B1830545
theorem B1220375 : Blo 810345 1220375 := bstep (se 1 (by rfl) ⟨915281, by rfl⟩ : syracuseStep 1220375 = 1830563) B1830563
theorem B3088151 : Blo 810345 3088151 := bstep (se 1 (by rfl) ⟨2316113, by rfl⟩ : syracuseStep 3088151 = 4632227) B4632227
theorem B1154839 : Blo 810345 1154839 := bstep (se 1 (by rfl) ⟨866129, by rfl⟩ : syracuseStep 1154839 = 1732259) B1732259
theorem B1220441 : Blo 810345 1220441 := bstep (se 2 (by rfl) ⟨457665, by rfl⟩ : syracuseStep 1220441 = 915331) B915331
theorem B1220555 : Blo 810345 1220555 := bstep (se 1 (by rfl) ⟨915416, by rfl⟩ : syracuseStep 1220555 = 1830833) B1830833
theorem B1220567 : Blo 810345 1220567 := bstep (se 1 (by rfl) ⟨915425, by rfl⟩ : syracuseStep 1220567 = 1830851) B1830851
theorem B1220633 : Blo 810345 1220633 := bstep (se 2 (by rfl) ⟨457737, by rfl⟩ : syracuseStep 1220633 = 915475) B915475
theorem B1220747 : Blo 810345 1220747 := bstep (se 1 (by rfl) ⟨915560, by rfl⟩ : syracuseStep 1220747 = 1831121) B1831121
theorem B1220759 : Blo 810345 1220759 := bstep (se 1 (by rfl) ⟨915569, by rfl⟩ : syracuseStep 1220759 = 1831139) B1831139
theorem B1220825 : Blo 810345 1220825 := bstep (se 2 (by rfl) ⟨457809, by rfl⟩ : syracuseStep 1220825 = 915619) B915619
theorem B3907885 : Blo 810345 3907885 := bstep (se 3 (by rfl) ⟨732728, by rfl⟩ : syracuseStep 3907885 = 1465457) B1465457
theorem B1220939 : Blo 810345 1220939 := bstep (se 1 (by rfl) ⟨915704, by rfl⟩ : syracuseStep 1220939 = 1831409) B1831409
theorem B1220951 : Blo 810345 1220951 := bstep (se 1 (by rfl) ⟨915713, by rfl⟩ : syracuseStep 1220951 = 1831427) B1831427
theorem B1647001 : Blo 810345 1647001 := bstep (se 2 (by rfl) ⟨617625, by rfl⟩ : syracuseStep 1647001 = 1235251) B1235251
theorem B1221017 : Blo 810345 1221017 := bstep (se 2 (by rfl) ⟨457881, by rfl⟩ : syracuseStep 1221017 = 915763) B915763
theorem B1221131 : Blo 810345 1221131 := bstep (se 1 (by rfl) ⟨915848, by rfl⟩ : syracuseStep 1221131 = 1831697) B1831697
theorem B1221143 : Blo 810345 1221143 := bstep (se 1 (by rfl) ⟨915857, by rfl⟩ : syracuseStep 1221143 = 1831715) B1831715
theorem B1221209 : Blo 810345 1221209 := bstep (se 2 (by rfl) ⟨457953, by rfl⟩ : syracuseStep 1221209 = 915907) B915907
theorem B6431333 : Blo 810345 6431333 := bstep (se 4 (by rfl) ⟨602937, by rfl⟩ : syracuseStep 6431333 = 1205875) B1205875
theorem B926411 : Blo 810345 926411 := bstep (se 1 (by rfl) ⟨694808, by rfl⟩ : syracuseStep 926411 = 1389617) B1389617
theorem B1221323 : Blo 810345 1221323 := bstep (se 1 (by rfl) ⟨915992, by rfl⟩ : syracuseStep 1221323 = 1831985) B1831985
theorem B1221335 : Blo 810345 1221335 := bstep (se 1 (by rfl) ⟨916001, by rfl⟩ : syracuseStep 1221335 = 1832003) B1832003
theorem B2925335 : Blo 810345 2925335 := bstep (se 1 (by rfl) ⟨2194001, by rfl⟩ : syracuseStep 2925335 = 4388003) B4388003
theorem B1221401 : Blo 810345 1221401 := bstep (se 2 (by rfl) ⟨458025, by rfl⟩ : syracuseStep 1221401 = 916051) B916051
theorem B1647449 : Blo 810345 1647449 := bstep (se 2 (by rfl) ⟨617793, by rfl⟩ : syracuseStep 1647449 = 1235587) B1235587
theorem B1221515 : Blo 810345 1221515 := bstep (se 1 (by rfl) ⟨916136, by rfl⟩ : syracuseStep 1221515 = 1832273) B1832273
theorem B2597849 : Blo 810345 2597849 := bstep (se 2 (by rfl) ⟨974193, by rfl⟩ : syracuseStep 2597849 = 1948387) B1948387
theorem B3089411 : Blo 810345 3089411 := bstep (se 1 (by rfl) ⟨2317058, by rfl⟩ : syracuseStep 3089411 = 4634117) B4634117
theorem B23733323 : Blo 810345 23733323 := bstep (se 1 (by rfl) ⟨17799992, by rfl⟩ : syracuseStep 23733323 = 35599985) B35599985
theorem B4105565 : Blo 810345 4105565 := bstep (se 3 (by rfl) ⟨769793, by rfl⟩ : syracuseStep 4105565 = 1539587) B1539587
theorem B6596113 : Blo 810345 6596113 := bstep (se 2 (by rfl) ⟨2473542, by rfl⟩ : syracuseStep 6596113 = 4947085) B4947085
theorem B4630061 : Blo 810345 4630061 := bstep (se 3 (by rfl) ⟨868136, by rfl⟩ : syracuseStep 4630061 = 1736273) B1736273
theorem B10430045 : Blo 810345 10430045 := bstep (se 3 (by rfl) ⟨1955633, by rfl⟩ : syracuseStep 10430045 = 3911267) B3911267
theorem B7513805 : Blo 810345 7513805 := bstep (se 3 (by rfl) ⟨1408838, by rfl⟩ : syracuseStep 7513805 = 2817677) B2817677
theorem B1156889 : Blo 810345 1156889 := bstep (se 2 (by rfl) ⟨433833, by rfl⟩ : syracuseStep 1156889 = 867667) B867667
theorem B1877825 : Blo 810345 1877825 := bstep (se 2 (by rfl) ⟨704184, by rfl⟩ : syracuseStep 1877825 = 1408369) B1408369
theorem B1976395 : Blo 810345 1976395 := bstep (se 1 (by rfl) ⟨1482296, by rfl⟩ : syracuseStep 1976395 = 2964593) B2964593
theorem B1386647 : Blo 810345 1386647 := bstep (se 1 (by rfl) ⟨1039985, by rfl⟩ : syracuseStep 1386647 = 2079971) B2079971
theorem B1026199 : Blo 810345 1026199 := bstep (se 1 (by rfl) ⟨769649, by rfl⟩ : syracuseStep 1026199 = 1539299) B1539299
theorem B3287243 : Blo 810345 3287243 := bstep (se 1 (by rfl) ⟨2465432, by rfl⟩ : syracuseStep 3287243 = 4930865) B4930865
theorem B1157527 : Blo 810345 1157527 := bstep (se 1 (by rfl) ⟨868145, by rfl⟩ : syracuseStep 1157527 = 1736291) B1736291
theorem B1485335 : Blo 810345 1485335 := bstep (se 1 (by rfl) ⟨1114001, by rfl⟩ : syracuseStep 1485335 = 2228003) B2228003
theorem B2599489 : Blo 810345 2599489 := bstep (se 2 (by rfl) ⟨974808, by rfl⟩ : syracuseStep 2599489 = 1949617) B1949617
theorem B8792651 : Blo 810345 8792651 := bstep (se 1 (by rfl) ⟨6594488, by rfl⟩ : syracuseStep 8792651 = 13188977) B13188977
theorem B2927539 : Blo 810345 2927539 := bstep (se 1 (by rfl) ⟨2195654, by rfl⟩ : syracuseStep 2927539 = 4391309) B4391309
theorem B1027019 : Blo 810345 1027019 := bstep (se 1 (by rfl) ⟨770264, by rfl⟩ : syracuseStep 1027019 = 1540529) B1540529
theorem B3714071 : Blo 810345 3714071 := bstep (se 1 (by rfl) ⟨2785553, by rfl⟩ : syracuseStep 3714071 = 5571107) B5571107
theorem B6171713 : Blo 810345 6171713 := bstep (se 2 (by rfl) ⟨2314392, by rfl⟩ : syracuseStep 6171713 = 4628785) B4628785
theorem B1485899 : Blo 810345 1485899 := bstep (se 1 (by rfl) ⟨1114424, by rfl⟩ : syracuseStep 1485899 = 2228849) B2228849
theorem B1158347 : Blo 810345 1158347 := bstep (se 1 (by rfl) ⟨868760, by rfl⟩ : syracuseStep 1158347 = 1737521) B1737521
theorem B1387735 : Blo 810345 1387735 := bstep (se 1 (by rfl) ⟨1040801, by rfl⟩ : syracuseStep 1387735 = 2081603) B2081603
theorem B1322201 : Blo 810345 1322201 := bstep (se 2 (by rfl) ⟨495825, by rfl⟩ : syracuseStep 1322201 = 991651) B991651
theorem B7023917 : Blo 810345 7023917 := bstep (se 3 (by rfl) ⟨1316984, by rfl⟩ : syracuseStep 7023917 = 2633969) B2633969
theorem B4107671 : Blo 810345 4107671 := bstep (se 1 (by rfl) ⟨3080753, by rfl⟩ : syracuseStep 4107671 = 6161507) B6161507
theorem B1027723 : Blo 810345 1027723 := bstep (se 1 (by rfl) ⟨770792, by rfl⟩ : syracuseStep 1027723 = 1541585) B1541585
theorem B1027991 : Blo 810345 1027991 := bstep (se 1 (by rfl) ⟨770993, by rfl⟩ : syracuseStep 1027991 = 1541987) B1541987
theorem B2469811 : Blo 810345 2469811 := bstep (se 1 (by rfl) ⟨1852358, by rfl⟩ : syracuseStep 2469811 = 3704717) B3704717
theorem B23376023 : Blo 810345 23376023 := bstep (se 1 (by rfl) ⟨17532017, by rfl⟩ : syracuseStep 23376023 = 35064035) B35064035
theorem B7516433 : Blo 810345 7516433 := bstep (se 2 (by rfl) ⟨2818662, by rfl⟩ : syracuseStep 7516433 = 5637325) B5637325
theorem B22196753 : Blo 810345 22196753 := bstep (se 2 (by rfl) ⟨8323782, by rfl⟩ : syracuseStep 22196753 = 16647565) B16647565
theorem B1028695 : Blo 810345 1028695 := bstep (se 1 (by rfl) ⟨771521, by rfl⟩ : syracuseStep 1028695 = 1543043) B1543043
theorem B6239051 : Blo 810345 6239051 := bstep (se 1 (by rfl) ⟨4679288, by rfl⟩ : syracuseStep 6239051 = 9358577) B9358577
theorem B6173657 : Blo 810345 6173657 := bstep (se 2 (by rfl) ⟨2315121, by rfl⟩ : syracuseStep 6173657 = 4630243) B4630243
theorem B3912749 : Blo 810345 3912749 := bstep (se 3 (by rfl) ⟨733640, by rfl⟩ : syracuseStep 3912749 = 1467281) B1467281
theorem B3126347 : Blo 810345 3126347 := bstep (se 1 (by rfl) ⟨2344760, by rfl⟩ : syracuseStep 3126347 = 4689521) B4689521
theorem B865399 : Blo 810345 865399 := bstep (se 1 (by rfl) ⟨649049, by rfl⟩ : syracuseStep 865399 = 1298099) B1298099
theorem B13874327 : Blo 810345 13874327 := bstep (se 1 (by rfl) ⟨10405745, by rfl⟩ : syracuseStep 13874327 = 20811491) B20811491
theorem B865847 : Blo 810345 865847 := bstep (se 1 (by rfl) ⟨649385, by rfl⟩ : syracuseStep 865847 = 1298771) B1298771
theorem B11089669 : Blo 810345 11089669 := bstep (se 4 (by rfl) ⟨1039656, by rfl⟩ : syracuseStep 11089669 = 2079313) B2079313
theorem B1095449 : Blo 810345 1095449 := bstep (se 2 (by rfl) ⟨410793, by rfl⟩ : syracuseStep 1095449 = 821587) B821587
theorem B866219 : Blo 810345 866219 := bstep (se 1 (by rfl) ⟨649664, by rfl⟩ : syracuseStep 866219 = 1299329) B1299329
theorem B1030411 : Blo 810345 1030411 := bstep (se 1 (by rfl) ⟨772808, by rfl⟩ : syracuseStep 1030411 = 1545617) B1545617
theorem B6600977 : Blo 810345 6600977 := bstep (se 2 (by rfl) ⟨2475366, by rfl⟩ : syracuseStep 6600977 = 4950733) B4950733
theorem B1948225 : Blo 810345 1948225 := bstep (se 2 (by rfl) ⟨730584, by rfl⟩ : syracuseStep 1948225 = 1461169) B1461169
theorem B2341469 : Blo 810345 2341469 := bstep (se 3 (by rfl) ⟨439025, by rfl⟩ : syracuseStep 2341469 = 878051) B878051
theorem B1850177 : Blo 810345 1850177 := bstep (se 2 (by rfl) ⟨693816, by rfl⟩ : syracuseStep 1850177 = 1387633) B1387633
theorem B2734937 : Blo 810345 2734937 := bstep (se 2 (by rfl) ⟨1025601, by rfl⟩ : syracuseStep 2734937 = 2051203) B2051203
theorem B4111235 : Blo 810345 4111235 := bstep (se 1 (by rfl) ⟨3083426, by rfl⟩ : syracuseStep 4111235 = 6166853) B6166853
theorem B867223 : Blo 810345 867223 := bstep (se 1 (by rfl) ⟨650417, by rfl⟩ : syracuseStep 867223 = 1300835) B1300835
theorem B6929509 : Blo 810345 6929509 := bstep (se 4 (by rfl) ⟨649641, by rfl⟩ : syracuseStep 6929509 = 1299283) B1299283
theorem B2473177 : Blo 810345 2473177 := bstep (se 2 (by rfl) ⟨927441, by rfl⟩ : syracuseStep 2473177 = 1854883) B1854883
theorem B2735639 : Blo 810345 2735639 := bstep (se 1 (by rfl) ⟨2051729, by rfl⟩ : syracuseStep 2735639 = 4103459) B4103459
theorem B868043 : Blo 810345 868043 := bstep (se 1 (by rfl) ⟨651032, by rfl⟩ : syracuseStep 868043 = 1302065) B1302065
theorem B2473907 : Blo 810345 2473907 := bstep (se 1 (by rfl) ⟨1855430, by rfl⟩ : syracuseStep 2473907 = 3710861) B3710861
theorem B10403801 : Blo 810345 10403801 := bstep (se 2 (by rfl) ⟨3901425, by rfl⟩ : syracuseStep 10403801 = 7802851) B7802851
theorem B6930467 : Blo 810345 6930467 := bstep (se 1 (by rfl) ⟨5197850, by rfl⟩ : syracuseStep 6930467 = 10395701) B10395701
theorem B2736179 : Blo 810345 2736179 := bstep (se 1 (by rfl) ⟨2052134, by rfl⟩ : syracuseStep 2736179 = 4104269) B4104269
theorem B1949771 : Blo 810345 1949771 := bstep (se 1 (by rfl) ⟨1462328, by rfl⟩ : syracuseStep 1949771 = 2924657) B2924657
theorem B6177059 : Blo 810345 6177059 := bstep (se 1 (by rfl) ⟨4632794, by rfl⟩ : syracuseStep 6177059 = 9265589) B9265589
theorem B2736449 : Blo 810345 2736449 := bstep (se 2 (by rfl) ⟨1026168, by rfl⟩ : syracuseStep 2736449 = 2052337) B2052337
theorem B1851929 : Blo 810345 1851929 := bstep (se 2 (by rfl) ⟨694473, by rfl⟩ : syracuseStep 1851929 = 1388947) B1388947
theorem B6242993 : Blo 810345 6242993 := bstep (se 2 (by rfl) ⟨2341122, by rfl⟩ : syracuseStep 6242993 = 4682245) B4682245
theorem B1098455 : Blo 810345 1098455 := bstep (se 1 (by rfl) ⟨823841, by rfl⟩ : syracuseStep 1098455 = 1647683) B1647683
theorem B5849891 : Blo 810345 5849891 := bstep (se 1 (by rfl) ⟨4387418, by rfl⟩ : syracuseStep 5849891 = 8774837) B8774837
theorem B2736989 : Blo 810345 2736989 := bstep (se 3 (by rfl) ⟨513185, by rfl⟩ : syracuseStep 2736989 = 1026371) B1026371
theorem B4637533 : Blo 810345 4637533 := bstep (se 3 (by rfl) ⟨869537, by rfl⟩ : syracuseStep 4637533 = 1739075) B1739075
theorem B869239 : Blo 810345 869239 := bstep (se 1 (by rfl) ⟨651929, by rfl⟩ : syracuseStep 869239 = 1303859) B1303859
theorem B2114881 : Blo 810345 2114881 := bstep (se 2 (by rfl) ⟨793080, by rfl⟩ : syracuseStep 2114881 = 1586161) B1586161
theorem B1754561 : Blo 810345 1754561 := bstep (se 2 (by rfl) ⟨657960, by rfl⟩ : syracuseStep 1754561 = 1315921) B1315921
theorem B3295169 : Blo 810345 3295169 := bstep (se 2 (by rfl) ⟨1235688, by rfl⟩ : syracuseStep 3295169 = 2471377) B2471377
theorem B2738123 : Blo 810345 2738123 := bstep (se 1 (by rfl) ⟨2053592, by rfl⟩ : syracuseStep 2738123 = 4107185) B4107185
theorem B7817309 : Blo 810345 7817309 := bstep (se 3 (by rfl) ⟨1465745, by rfl⟩ : syracuseStep 7817309 = 2931491) B2931491
theorem B7424131 : Blo 810345 7424131 := bstep (se 1 (by rfl) ⟨5568098, by rfl⟩ : syracuseStep 7424131 = 11136197) B11136197
theorem B2738393 : Blo 810345 2738393 := bstep (se 2 (by rfl) ⟨1026897, by rfl⟩ : syracuseStep 2738393 = 2053795) B2053795
theorem B2607383 : Blo 810345 2607383 := bstep (se 1 (by rfl) ⟨1955537, by rfl⟩ : syracuseStep 2607383 = 3911075) B3911075
theorem B2312651 : Blo 810345 2312651 := bstep (se 1 (by rfl) ⟨1734488, by rfl⟩ : syracuseStep 2312651 = 3468977) B3468977
theorem B4114961 : Blo 810345 4114961 := bstep (se 2 (by rfl) ⟨1543110, by rfl⟩ : syracuseStep 4114961 = 3086221) B3086221
theorem B4115123 : Blo 810345 4115123 := bstep (se 1 (by rfl) ⟨3086342, by rfl⟩ : syracuseStep 4115123 = 6172685) B6172685
theorem B2607947 : Blo 810345 2607947 := bstep (se 1 (by rfl) ⟨1955960, by rfl⟩ : syracuseStep 2607947 = 3911921) B3911921
theorem B2313049 : Blo 810345 2313049 := bstep (se 2 (by rfl) ⟨867393, by rfl⟩ : syracuseStep 2313049 = 1734787) B1734787
theorem B2739095 : Blo 810345 2739095 := bstep (se 1 (by rfl) ⟨2054321, by rfl⟩ : syracuseStep 2739095 = 4108643) B4108643
theorem B937099 : Blo 810345 937099 := bstep (se 1 (by rfl) ⟨702824, by rfl⟩ : syracuseStep 937099 = 1405649) B1405649
theorem B1559873 : Blo 810345 1559873 := bstep (se 2 (by rfl) ⟨584952, by rfl⟩ : syracuseStep 1559873 = 1169905) B1169905
theorem B2051507 : Blo 810345 2051507 := bstep (se 1 (by rfl) ⟨1538630, by rfl⟩ : syracuseStep 2051507 = 3077261) B3077261
theorem B2739635 : Blo 810345 2739635 := bstep (se 1 (by rfl) ⟨2054726, by rfl⟩ : syracuseStep 2739635 = 4109453) B4109453
theorem B1854913 : Blo 810345 1854913 := bstep (se 2 (by rfl) ⟨695592, by rfl⟩ : syracuseStep 1854913 = 1391185) B1391185
theorem B1756631 : Blo 810345 1756631 := bstep (se 1 (by rfl) ⟨1317473, by rfl⟩ : syracuseStep 1756631 = 2634947) B2634947
theorem B3296857 : Blo 810345 3296857 := bstep (se 2 (by rfl) ⟨1236321, by rfl⟩ : syracuseStep 3296857 = 2472643) B2472643
theorem B13913693 : Blo 810345 13913693 := bstep (se 3 (by rfl) ⟨2608817, by rfl⟩ : syracuseStep 13913693 = 5217635) B5217635
theorem B1560217 : Blo 810345 1560217 := bstep (se 2 (by rfl) ⟨585081, by rfl⟩ : syracuseStep 1560217 = 1170163) B1170163
theorem B6246067 : Blo 810345 6246067 := bstep (se 1 (by rfl) ⟨4684550, by rfl⟩ : syracuseStep 6246067 = 9369101) B9369101
theorem B2739905 : Blo 810345 2739905 := bstep (se 2 (by rfl) ⟨1027464, by rfl⟩ : syracuseStep 2739905 = 2054929) B2054929
theorem B3296971 : Blo 810345 3296971 := bstep (se 1 (by rfl) ⟨2472728, by rfl⟩ : syracuseStep 3296971 = 4945457) B4945457
theorem B2051801 : Blo 810345 2051801 := bstep (se 2 (by rfl) ⟨769425, by rfl⟩ : syracuseStep 2051801 = 1538851) B1538851
theorem B10407797 : Blo 810345 10407797 := bstep (se 5 (by rfl) ⟨487865, by rfl⟩ : syracuseStep 10407797 = 975731) B975731
theorem B2314291 : Blo 810345 2314291 := bstep (se 1 (by rfl) ⟨1735718, by rfl⟩ : syracuseStep 2314291 = 3471437) B3471437
theorem B11260055 : Blo 810345 11260055 := bstep (se 1 (by rfl) ⟨8445041, by rfl⟩ : syracuseStep 11260055 = 16890083) B16890083
theorem B2740445 : Blo 810345 2740445 := bstep (se 3 (by rfl) ⟨513833, by rfl⟩ : syracuseStep 2740445 = 1027667) B1027667
theorem B1462553 : Blo 810345 1462553 := bstep (se 2 (by rfl) ⟨548457, by rfl⟩ : syracuseStep 1462553 = 1096915) B1096915
theorem B1855795 : Blo 810345 1855795 := bstep (se 1 (by rfl) ⟨1391846, by rfl⟩ : syracuseStep 1855795 = 2783693) B2783693
theorem B4117067 : Blo 810345 4117067 := bstep (se 1 (by rfl) ⟨3087800, by rfl⟩ : syracuseStep 4117067 = 6175601) B6175601
theorem B6935219 : Blo 810345 6935219 := bstep (se 1 (by rfl) ⟨5201414, by rfl⟩ : syracuseStep 6935219 = 10402829) B10402829
theorem B1462963 : Blo 810345 1462963 := bstep (se 1 (by rfl) ⟨1097222, by rfl⟩ : syracuseStep 1462963 = 2194445) B2194445
theorem B1823435 : Blo 810345 1823435 := bstep (se 1 (by rfl) ⟨1367576, by rfl⟩ : syracuseStep 1823435 = 2735153) B2735153
theorem B1823489 : Blo 810345 1823489 := bstep (se 2 (by rfl) ⟨683808, by rfl⟩ : syracuseStep 1823489 = 1367617) B1367617
theorem B3461953 : Blo 810345 3461953 := bstep (se 2 (by rfl) ⟨1298232, by rfl⟩ : syracuseStep 3461953 = 2596465) B2596465
theorem B1823705 : Blo 810345 1823705 := bstep (se 2 (by rfl) ⟨683889, by rfl⟩ : syracuseStep 1823705 = 1367779) B1367779
theorem B1823795 : Blo 810345 1823795 := bstep (se 1 (by rfl) ⟨1367846, by rfl⟩ : syracuseStep 1823795 = 2735693) B2735693
theorem B1823831 : Blo 810345 1823831 := bstep (se 1 (by rfl) ⟨1367873, by rfl⟩ : syracuseStep 1823831 = 2735747) B2735747
theorem B1463539 : Blo 810345 1463539 := bstep (se 1 (by rfl) ⟨1097654, by rfl⟩ : syracuseStep 1463539 = 2195309) B2195309
theorem B1824011 : Blo 810345 1824011 := bstep (se 1 (by rfl) ⟨1368008, by rfl⟩ : syracuseStep 1824011 = 2736017) B2736017
theorem B7525649 : Blo 810345 7525649 := bstep (se 2 (by rfl) ⟨2822118, by rfl⟩ : syracuseStep 7525649 = 5644237) B5644237
theorem B1824065 : Blo 810345 1824065 := bstep (se 2 (by rfl) ⟨684024, by rfl⟩ : syracuseStep 1824065 = 1368049) B1368049
theorem B2053451 : Blo 810345 2053451 := bstep (se 1 (by rfl) ⟨1540088, by rfl⟩ : syracuseStep 2053451 = 3080177) B3080177
theorem B2741579 : Blo 810345 2741579 := bstep (se 1 (by rfl) ⟨2056184, by rfl⟩ : syracuseStep 2741579 = 4112369) B4112369
theorem B56219021 : Blo 810345 56219021 := bstep (se 3 (by rfl) ⟨10541066, by rfl⟩ : syracuseStep 56219021 = 21082133) B21082133
theorem B3954071 : Blo 810345 3954071 := bstep (se 1 (by rfl) ⟨2965553, by rfl⟩ : syracuseStep 3954071 = 5931107) B5931107
theorem B1758667 : Blo 810345 1758667 := bstep (se 1 (by rfl) ⟨1319000, by rfl⟩ : syracuseStep 1758667 = 2638001) B2638001
theorem B6182405 : Blo 810345 6182405 := bstep (se 4 (by rfl) ⟨579600, by rfl⟩ : syracuseStep 6182405 = 1159201) B1159201
theorem B1824281 : Blo 810345 1824281 := bstep (se 2 (by rfl) ⟨684105, by rfl⟩ : syracuseStep 1824281 = 1368211) B1368211
theorem B2741849 : Blo 810345 2741849 := bstep (se 2 (by rfl) ⟨1028193, by rfl⟩ : syracuseStep 2741849 = 2056387) B2056387
theorem B1824371 : Blo 810345 1824371 := bstep (se 1 (by rfl) ⟨1368278, by rfl⟩ : syracuseStep 1824371 = 2736557) B2736557
theorem B5199491 : Blo 810345 5199491 := bstep (se 1 (by rfl) ⟨3899618, by rfl⟩ : syracuseStep 5199491 = 7799237) B7799237
theorem B1824407 : Blo 810345 1824407 := bstep (se 1 (by rfl) ⟨1368305, by rfl⟩ : syracuseStep 1824407 = 2736611) B2736611
theorem B1824587 : Blo 810345 1824587 := bstep (se 1 (by rfl) ⟨1368440, by rfl⟩ : syracuseStep 1824587 = 2736881) B2736881
theorem B1824641 : Blo 810345 1824641 := bstep (se 2 (by rfl) ⟨684240, by rfl⟩ : syracuseStep 1824641 = 1368481) B1368481
theorem B1464203 : Blo 810345 1464203 := bstep (se 1 (by rfl) ⟨1098152, by rfl⟩ : syracuseStep 1464203 = 2196305) B2196305
theorem B1824857 : Blo 810345 1824857 := bstep (se 2 (by rfl) ⟨684321, by rfl⟩ : syracuseStep 1824857 = 1368643) B1368643
theorem B1824947 : Blo 810345 1824947 := bstep (se 1 (by rfl) ⟨1368710, by rfl⟩ : syracuseStep 1824947 = 2737421) B2737421
theorem B1824983 : Blo 810345 1824983 := bstep (se 1 (by rfl) ⟨1368737, by rfl⟩ : syracuseStep 1824983 = 2737475) B2737475
theorem B9230597 : Blo 810345 9230597 := bstep (se 4 (by rfl) ⟨865368, by rfl⟩ : syracuseStep 9230597 = 1730737) B1730737
theorem B2054423 : Blo 810345 2054423 := bstep (se 1 (by rfl) ⟨1540817, by rfl⟩ : syracuseStep 2054423 = 3081635) B3081635
theorem B2742551 : Blo 810345 2742551 := bstep (se 1 (by rfl) ⟨2056913, by rfl⟩ : syracuseStep 2742551 = 4113827) B4113827
theorem B4118849 : Blo 810345 4118849 := bstep (se 2 (by rfl) ⟨1544568, by rfl⟩ : syracuseStep 4118849 = 3089137) B3089137
theorem B1825163 : Blo 810345 1825163 := bstep (se 1 (by rfl) ⟨1368872, by rfl⟩ : syracuseStep 1825163 = 2737745) B2737745
theorem B1825217 : Blo 810345 1825217 := bstep (se 2 (by rfl) ⟨684456, by rfl⟩ : syracuseStep 1825217 = 1368913) B1368913
theorem B1956403 : Blo 810345 1956403 := bstep (se 1 (by rfl) ⟨1467302, by rfl⟩ : syracuseStep 1956403 = 2934605) B2934605
theorem B7494275 : Blo 810345 7494275 := bstep (se 1 (by rfl) ⟨5620706, by rfl⟩ : syracuseStep 7494275 = 11241413) B11241413
theorem B1759895 : Blo 810345 1759895 := bstep (se 1 (by rfl) ⟨1319921, by rfl⟩ : syracuseStep 1759895 = 2639843) B2639843
theorem B1825433 : Blo 810345 1825433 := bstep (se 2 (by rfl) ⟨684537, by rfl⟩ : syracuseStep 1825433 = 1369075) B1369075
theorem B1825523 : Blo 810345 1825523 := bstep (se 1 (by rfl) ⟨1369142, by rfl⟩ : syracuseStep 1825523 = 2738285) B2738285
theorem B1825559 : Blo 810345 1825559 := bstep (se 1 (by rfl) ⟨1369169, by rfl⟩ : syracuseStep 1825559 = 2738339) B2738339
theorem B6249251 : Blo 810345 6249251 := bstep (se 1 (by rfl) ⟨4686938, by rfl⟩ : syracuseStep 6249251 = 9373877) B9373877
theorem B2743091 : Blo 810345 2743091 := bstep (se 1 (by rfl) ⟨2057318, by rfl⟩ : syracuseStep 2743091 = 4114637) B4114637
theorem B2087731 : Blo 810345 2087731 := bstep (se 1 (by rfl) ⟨1565798, by rfl⟩ : syracuseStep 2087731 = 3131597) B3131597
theorem B2317207 : Blo 810345 2317207 := bstep (se 1 (by rfl) ⟨1737905, by rfl⟩ : syracuseStep 2317207 = 3475811) B3475811
theorem B2055091 : Blo 810345 2055091 := bstep (se 1 (by rfl) ⟨1541318, by rfl⟩ : syracuseStep 2055091 = 3082637) B3082637
theorem B1825739 : Blo 810345 1825739 := bstep (se 1 (by rfl) ⟨1369304, by rfl⟩ : syracuseStep 1825739 = 2738609) B2738609
theorem B1825793 : Blo 810345 1825793 := bstep (se 2 (by rfl) ⟨684672, by rfl⟩ : syracuseStep 1825793 = 1369345) B1369345
theorem B2055233 : Blo 810345 2055233 := bstep (se 2 (by rfl) ⟨770712, by rfl⟩ : syracuseStep 2055233 = 1541425) B1541425
theorem B2743361 : Blo 810345 2743361 := bstep (se 2 (by rfl) ⟨1028760, by rfl⟩ : syracuseStep 2743361 = 2057521) B2057521
theorem B1826009 : Blo 810345 1826009 := bstep (se 2 (by rfl) ⟨684753, by rfl⟩ : syracuseStep 1826009 = 1369507) B1369507
theorem B1826099 : Blo 810345 1826099 := bstep (se 1 (by rfl) ⟨1369574, by rfl⟩ : syracuseStep 1826099 = 2739149) B2739149
theorem B974155 : Blo 810345 974155 := bstep (se 1 (by rfl) ⟨730616, by rfl⟩ : syracuseStep 974155 = 1461233) B1461233
theorem B1826135 : Blo 810345 1826135 := bstep (se 1 (by rfl) ⟨1369601, by rfl⟩ : syracuseStep 1826135 = 2739203) B2739203
theorem B810347 : Blo 810345 810347 := bstep (se 1 (by rfl) ⟨607760, by rfl⟩ : syracuseStep 810347 = 1215521) B1215521
theorem B810359 : Blo 810345 810359 := bstep (se 1 (by rfl) ⟨607769, by rfl⟩ : syracuseStep 810359 = 1215539) B1215539
theorem B810379 : Blo 810345 810379 := bstep (se 1 (by rfl) ⟨607784, by rfl⟩ : syracuseStep 810379 = 1215569) B1215569
theorem B119922061 : Blo 810345 119922061 := bstep (se 3 (by rfl) ⟨22485386, by rfl⟩ : syracuseStep 119922061 = 44970773) B44970773
theorem B810391 : Blo 810345 810391 := bstep (se 1 (by rfl) ⟨607793, by rfl⟩ : syracuseStep 810391 = 1215587) B1215587
theorem B810411 : Blo 810345 810411 := bstep (se 1 (by rfl) ⟨607808, by rfl⟩ : syracuseStep 810411 = 1215617) B1215617
theorem B810423 : Blo 810345 810423 := bstep (se 1 (by rfl) ⟨607817, by rfl⟩ : syracuseStep 810423 = 1215635) B1215635
theorem B810443 : Blo 810345 810443 := bstep (se 1 (by rfl) ⟨607832, by rfl⟩ : syracuseStep 810443 = 1215665) B1215665
theorem B810455 : Blo 810345 810455 := bstep (se 1 (by rfl) ⟨607841, by rfl⟩ : syracuseStep 810455 = 1215683) B1215683
theorem B810475 : Blo 810345 810475 := bstep (se 1 (by rfl) ⟨607856, by rfl⟩ : syracuseStep 810475 = 1215713) B1215713
theorem B810487 : Blo 810345 810487 := bstep (se 1 (by rfl) ⟨607865, by rfl⟩ : syracuseStep 810487 = 1215731) B1215731
theorem B1367563 : Blo 810345 1367563 := bstep (se 1 (by rfl) ⟨1025672, by rfl⟩ : syracuseStep 1367563 = 2051345) B2051345
theorem B810507 : Blo 810345 810507 := bstep (se 1 (by rfl) ⟨607880, by rfl⟩ : syracuseStep 810507 = 1215761) B1215761
theorem B1826315 : Blo 810345 1826315 := bstep (se 1 (by rfl) ⟨1369736, by rfl⟩ : syracuseStep 1826315 = 2739473) B2739473
theorem B810519 : Blo 810345 810519 := bstep (se 1 (by rfl) ⟨607889, by rfl⟩ : syracuseStep 810519 = 1215779) B1215779
theorem B810539 : Blo 810345 810539 := bstep (se 1 (by rfl) ⟨607904, by rfl⟩ : syracuseStep 810539 = 1215809) B1215809
theorem B810551 : Blo 810345 810551 := bstep (se 1 (by rfl) ⟨607913, by rfl⟩ : syracuseStep 810551 = 1215827) B1215827
theorem B1826369 : Blo 810345 1826369 := bstep (se 2 (by rfl) ⟨684888, by rfl⟩ : syracuseStep 1826369 = 1369777) B1369777
theorem B810571 : Blo 810345 810571 := bstep (se 1 (by rfl) ⟨607928, by rfl⟩ : syracuseStep 810571 = 1215857) B1215857
theorem B810583 : Blo 810345 810583 := bstep (se 1 (by rfl) ⟨607937, by rfl⟩ : syracuseStep 810583 = 1215875) B1215875
theorem B2743901 : Blo 810345 2743901 := bstep (se 3 (by rfl) ⟨514481, by rfl⟩ : syracuseStep 2743901 = 1028963) B1028963
theorem B810603 : Blo 810345 810603 := bstep (se 1 (by rfl) ⟨607952, by rfl⟩ : syracuseStep 810603 = 1215905) B1215905
theorem B810615 : Blo 810345 810615 := bstep (se 1 (by rfl) ⟨607961, by rfl⟩ : syracuseStep 810615 = 1215923) B1215923
theorem B810635 : Blo 810345 810635 := bstep (se 1 (by rfl) ⟨607976, by rfl⟩ : syracuseStep 810635 = 1215953) B1215953
theorem B810647 : Blo 810345 810647 := bstep (se 1 (by rfl) ⟨607985, by rfl⟩ : syracuseStep 810647 = 1215971) B1215971
theorem B1367705 : Blo 810345 1367705 := bstep (se 2 (by rfl) ⟨512889, by rfl⟩ : syracuseStep 1367705 = 1025779) B1025779
theorem B810667 : Blo 810345 810667 := bstep (se 1 (by rfl) ⟨608000, by rfl⟩ : syracuseStep 810667 = 1216001) B1216001
theorem B810679 : Blo 810345 810679 := bstep (se 1 (by rfl) ⟨608009, by rfl⟩ : syracuseStep 810679 = 1216019) B1216019
theorem B810699 : Blo 810345 810699 := bstep (se 1 (by rfl) ⟨608024, by rfl⟩ : syracuseStep 810699 = 1216049) B1216049
theorem B810711 : Blo 810345 810711 := bstep (se 1 (by rfl) ⟨608033, by rfl⟩ : syracuseStep 810711 = 1216067) B1216067
theorem B810731 : Blo 810345 810731 := bstep (se 1 (by rfl) ⟨608048, by rfl⟩ : syracuseStep 810731 = 1216097) B1216097
theorem B810743 : Blo 810345 810743 := bstep (se 1 (by rfl) ⟨608057, by rfl⟩ : syracuseStep 810743 = 1216115) B1216115
theorem B810763 : Blo 810345 810763 := bstep (se 1 (by rfl) ⟨608072, by rfl⟩ : syracuseStep 810763 = 1216145) B1216145
theorem B810775 : Blo 810345 810775 := bstep (se 1 (by rfl) ⟨608081, by rfl⟩ : syracuseStep 810775 = 1216163) B1216163
theorem B1367833 : Blo 810345 1367833 := bstep (se 2 (by rfl) ⟨512937, by rfl⟩ : syracuseStep 1367833 = 1025875) B1025875
theorem B1826585 : Blo 810345 1826585 := bstep (se 2 (by rfl) ⟨684969, by rfl⟩ : syracuseStep 1826585 = 1369939) B1369939
theorem B810795 : Blo 810345 810795 := bstep (se 1 (by rfl) ⟨608096, by rfl⟩ : syracuseStep 810795 = 1216193) B1216193
theorem B810807 : Blo 810345 810807 := bstep (se 1 (by rfl) ⟨608105, by rfl⟩ : syracuseStep 810807 = 1216211) B1216211
theorem B810827 : Blo 810345 810827 := bstep (se 1 (by rfl) ⟨608120, by rfl⟩ : syracuseStep 810827 = 1216241) B1216241
theorem B810839 : Blo 810345 810839 := bstep (se 1 (by rfl) ⟨608129, by rfl⟩ : syracuseStep 810839 = 1216259) B1216259
theorem B810859 : Blo 810345 810859 := bstep (se 1 (by rfl) ⟨608144, by rfl⟩ : syracuseStep 810859 = 1216289) B1216289
theorem B1826675 : Blo 810345 1826675 := bstep (se 1 (by rfl) ⟨1370006, by rfl⟩ : syracuseStep 1826675 = 2740013) B2740013
theorem B810871 : Blo 810345 810871 := bstep (se 1 (by rfl) ⟨608153, by rfl⟩ : syracuseStep 810871 = 1216307) B1216307
theorem B810891 : Blo 810345 810891 := bstep (se 1 (by rfl) ⟨608168, by rfl⟩ : syracuseStep 810891 = 1216337) B1216337
theorem B810903 : Blo 810345 810903 := bstep (se 1 (by rfl) ⟨608177, by rfl⟩ : syracuseStep 810903 = 1216355) B1216355
theorem B1826711 : Blo 810345 1826711 := bstep (se 1 (by rfl) ⟨1370033, by rfl⟩ : syracuseStep 1826711 = 2740067) B2740067
theorem B810923 : Blo 810345 810923 := bstep (se 1 (by rfl) ⟨608192, by rfl⟩ : syracuseStep 810923 = 1216385) B1216385
theorem B810935 : Blo 810345 810935 := bstep (se 1 (by rfl) ⟨608201, by rfl⟩ : syracuseStep 810935 = 1216403) B1216403
theorem B810955 : Blo 810345 810955 := bstep (se 1 (by rfl) ⟨608216, by rfl⟩ : syracuseStep 810955 = 1216433) B1216433
theorem B1302475 : Blo 810345 1302475 := bstep (se 1 (by rfl) ⟨976856, by rfl⟩ : syracuseStep 1302475 = 1953713) B1953713
theorem B810967 : Blo 810345 810967 := bstep (se 1 (by rfl) ⟨608225, by rfl⟩ : syracuseStep 810967 = 1216451) B1216451
theorem B810987 : Blo 810345 810987 := bstep (se 1 (by rfl) ⟨608240, by rfl⟩ : syracuseStep 810987 = 1216481) B1216481
theorem B810999 : Blo 810345 810999 := bstep (se 1 (by rfl) ⟨608249, by rfl⟩ : syracuseStep 810999 = 1216499) B1216499
theorem B811019 : Blo 810345 811019 := bstep (se 1 (by rfl) ⟨608264, by rfl⟩ : syracuseStep 811019 = 1216529) B1216529
theorem B811031 : Blo 810345 811031 := bstep (se 1 (by rfl) ⟨608273, by rfl⟩ : syracuseStep 811031 = 1216547) B1216547
theorem B811051 : Blo 810345 811051 := bstep (se 1 (by rfl) ⟨608288, by rfl⟩ : syracuseStep 811051 = 1216577) B1216577
theorem B811063 : Blo 810345 811063 := bstep (se 1 (by rfl) ⟨608297, by rfl⟩ : syracuseStep 811063 = 1216595) B1216595
theorem B811083 : Blo 810345 811083 := bstep (se 1 (by rfl) ⟨608312, by rfl⟩ : syracuseStep 811083 = 1216625) B1216625
theorem B1826891 : Blo 810345 1826891 := bstep (se 1 (by rfl) ⟨1370168, by rfl⟩ : syracuseStep 1826891 = 2740337) B2740337
theorem B811095 : Blo 810345 811095 := bstep (se 1 (by rfl) ⟨608321, by rfl⟩ : syracuseStep 811095 = 1216643) B1216643
theorem B811115 : Blo 810345 811115 := bstep (se 1 (by rfl) ⟨608336, by rfl⟩ : syracuseStep 811115 = 1216673) B1216673
theorem B811127 : Blo 810345 811127 := bstep (se 1 (by rfl) ⟨608345, by rfl⟩ : syracuseStep 811127 = 1216691) B1216691
theorem B1826945 : Blo 810345 1826945 := bstep (se 2 (by rfl) ⟨685104, by rfl⟩ : syracuseStep 1826945 = 1370209) B1370209
theorem B811147 : Blo 810345 811147 := bstep (se 1 (by rfl) ⟨608360, by rfl⟩ : syracuseStep 811147 = 1216721) B1216721
theorem B811159 : Blo 810345 811159 := bstep (se 1 (by rfl) ⟨608369, by rfl⟩ : syracuseStep 811159 = 1216739) B1216739
theorem B811179 : Blo 810345 811179 := bstep (se 1 (by rfl) ⟨608384, by rfl⟩ : syracuseStep 811179 = 1216769) B1216769
theorem B811191 : Blo 810345 811191 := bstep (se 1 (by rfl) ⟨608393, by rfl⟩ : syracuseStep 811191 = 1216787) B1216787
theorem B811211 : Blo 810345 811211 := bstep (se 1 (by rfl) ⟨608408, by rfl⟩ : syracuseStep 811211 = 1216817) B1216817
theorem B1302731 : Blo 810345 1302731 := bstep (se 1 (by rfl) ⟨977048, by rfl⟩ : syracuseStep 1302731 = 1954097) B1954097
theorem B2318539 : Blo 810345 2318539 := bstep (se 1 (by rfl) ⟨1738904, by rfl⟩ : syracuseStep 2318539 = 3477809) B3477809
theorem B811223 : Blo 810345 811223 := bstep (se 1 (by rfl) ⟨608417, by rfl⟩ : syracuseStep 811223 = 1216835) B1216835
theorem B4120793 : Blo 810345 4120793 := bstep (se 2 (by rfl) ⟨1545297, by rfl⟩ : syracuseStep 4120793 = 3090595) B3090595
theorem B811243 : Blo 810345 811243 := bstep (se 1 (by rfl) ⟨608432, by rfl⟩ : syracuseStep 811243 = 1216865) B1216865
theorem B811255 : Blo 810345 811255 := bstep (se 1 (by rfl) ⟨608441, by rfl⟩ : syracuseStep 811255 = 1216883) B1216883
theorem B811275 : Blo 810345 811275 := bstep (se 1 (by rfl) ⟨608456, by rfl⟩ : syracuseStep 811275 = 1216913) B1216913
theorem B811287 : Blo 810345 811287 := bstep (se 1 (by rfl) ⟨608465, by rfl⟩ : syracuseStep 811287 = 1216931) B1216931
theorem B811307 : Blo 810345 811307 := bstep (se 1 (by rfl) ⟨608480, by rfl⟩ : syracuseStep 811307 = 1216961) B1216961
theorem B2056499 : Blo 810345 2056499 := bstep (se 1 (by rfl) ⟨1542374, by rfl⟩ : syracuseStep 2056499 = 3084749) B3084749
theorem B811319 : Blo 810345 811319 := bstep (se 1 (by rfl) ⟨608489, by rfl⟩ : syracuseStep 811319 = 1216979) B1216979
theorem B811339 : Blo 810345 811339 := bstep (se 1 (by rfl) ⟨608504, by rfl⟩ : syracuseStep 811339 = 1217009) B1217009
theorem B1368407 : Blo 810345 1368407 := bstep (se 1 (by rfl) ⟨1026305, by rfl⟩ : syracuseStep 1368407 = 2052611) B2052611
theorem B811351 : Blo 810345 811351 := bstep (se 1 (by rfl) ⟨608513, by rfl⟩ : syracuseStep 811351 = 1217027) B1217027
theorem B1827161 : Blo 810345 1827161 := bstep (se 2 (by rfl) ⟨685185, by rfl⟩ : syracuseStep 1827161 = 1370371) B1370371
theorem B811371 : Blo 810345 811371 := bstep (se 1 (by rfl) ⟨608528, by rfl⟩ : syracuseStep 811371 = 1217057) B1217057
theorem B811383 : Blo 810345 811383 := bstep (se 1 (by rfl) ⟨608537, by rfl⟩ : syracuseStep 811383 = 1217075) B1217075
theorem B811403 : Blo 810345 811403 := bstep (se 1 (by rfl) ⟨608552, by rfl⟩ : syracuseStep 811403 = 1217105) B1217105
theorem B811415 : Blo 810345 811415 := bstep (se 1 (by rfl) ⟨608561, by rfl⟩ : syracuseStep 811415 = 1217123) B1217123
theorem B811435 : Blo 810345 811435 := bstep (se 1 (by rfl) ⟨608576, by rfl⟩ : syracuseStep 811435 = 1217153) B1217153
theorem B1827251 : Blo 810345 1827251 := bstep (se 1 (by rfl) ⟨1370438, by rfl⟩ : syracuseStep 1827251 = 2740877) B2740877
theorem B811447 : Blo 810345 811447 := bstep (se 1 (by rfl) ⟨608585, by rfl⟩ : syracuseStep 811447 = 1217171) B1217171
theorem B811467 : Blo 810345 811467 := bstep (se 1 (by rfl) ⟨608600, by rfl⟩ : syracuseStep 811467 = 1217201) B1217201
theorem B1368535 : Blo 810345 1368535 := bstep (se 1 (by rfl) ⟨1026401, by rfl⟩ : syracuseStep 1368535 = 2052803) B2052803
theorem B811479 : Blo 810345 811479 := bstep (se 1 (by rfl) ⟨608609, by rfl⟩ : syracuseStep 811479 = 1217219) B1217219
theorem B1827287 : Blo 810345 1827287 := bstep (se 1 (by rfl) ⟨1370465, by rfl⟩ : syracuseStep 1827287 = 2740931) B2740931
theorem B2318813 : Blo 810345 2318813 := bstep (se 3 (by rfl) ⟨434777, by rfl⟩ : syracuseStep 2318813 = 869555) B869555
theorem B811499 : Blo 810345 811499 := bstep (se 1 (by rfl) ⟨608624, by rfl⟩ : syracuseStep 811499 = 1217249) B1217249
theorem B811511 : Blo 810345 811511 := bstep (se 1 (by rfl) ⟨608633, by rfl⟩ : syracuseStep 811511 = 1217267) B1217267
theorem B811531 : Blo 810345 811531 := bstep (se 1 (by rfl) ⟨608648, by rfl⟩ : syracuseStep 811531 = 1217297) B1217297
theorem B811543 : Blo 810345 811543 := bstep (se 1 (by rfl) ⟨608657, by rfl⟩ : syracuseStep 811543 = 1217315) B1217315
theorem B811563 : Blo 810345 811563 := bstep (se 1 (by rfl) ⟨608672, by rfl⟩ : syracuseStep 811563 = 1217345) B1217345
theorem B811575 : Blo 810345 811575 := bstep (se 1 (by rfl) ⟨608681, by rfl⟩ : syracuseStep 811575 = 1217363) B1217363
theorem B811595 : Blo 810345 811595 := bstep (se 1 (by rfl) ⟨608696, by rfl⟩ : syracuseStep 811595 = 1217393) B1217393
theorem B811607 : Blo 810345 811607 := bstep (se 1 (by rfl) ⟨608705, by rfl⟩ : syracuseStep 811607 = 1217411) B1217411
theorem B811627 : Blo 810345 811627 := bstep (se 1 (by rfl) ⟨608720, by rfl⟩ : syracuseStep 811627 = 1217441) B1217441
theorem B811639 : Blo 810345 811639 := bstep (se 1 (by rfl) ⟨608729, by rfl⟩ : syracuseStep 811639 = 1217459) B1217459
theorem B811659 : Blo 810345 811659 := bstep (se 1 (by rfl) ⟨608744, by rfl⟩ : syracuseStep 811659 = 1217489) B1217489
theorem B1827467 : Blo 810345 1827467 := bstep (se 1 (by rfl) ⟨1370600, by rfl⟩ : syracuseStep 1827467 = 2741201) B2741201
theorem B811671 : Blo 810345 811671 := bstep (se 1 (by rfl) ⟨608753, by rfl⟩ : syracuseStep 811671 = 1217507) B1217507
theorem B3007127 : Blo 810345 3007127 := bstep (se 1 (by rfl) ⟨2255345, by rfl⟩ : syracuseStep 3007127 = 4510691) B4510691
theorem B811691 : Blo 810345 811691 := bstep (se 1 (by rfl) ⟨608768, by rfl⟩ : syracuseStep 811691 = 1217537) B1217537
theorem B811703 : Blo 810345 811703 := bstep (se 1 (by rfl) ⟨608777, by rfl⟩ : syracuseStep 811703 = 1217555) B1217555
theorem B1827521 : Blo 810345 1827521 := bstep (se 2 (by rfl) ⟨685320, by rfl⟩ : syracuseStep 1827521 = 1370641) B1370641
theorem B811723 : Blo 810345 811723 := bstep (se 1 (by rfl) ⟨608792, by rfl⟩ : syracuseStep 811723 = 1217585) B1217585
theorem B2745035 : Blo 810345 2745035 := bstep (se 1 (by rfl) ⟨2058776, by rfl⟩ : syracuseStep 2745035 = 4117553) B4117553
theorem B811735 : Blo 810345 811735 := bstep (se 1 (by rfl) ⟨608801, by rfl⟩ : syracuseStep 811735 = 1217603) B1217603
theorem B811755 : Blo 810345 811755 := bstep (se 1 (by rfl) ⟨608816, by rfl⟩ : syracuseStep 811755 = 1217633) B1217633
theorem B811767 : Blo 810345 811767 := bstep (se 1 (by rfl) ⟨608825, by rfl⟩ : syracuseStep 811767 = 1217651) B1217651
theorem B811787 : Blo 810345 811787 := bstep (se 1 (by rfl) ⟨608840, by rfl⟩ : syracuseStep 811787 = 1217681) B1217681
theorem B811799 : Blo 810345 811799 := bstep (se 1 (by rfl) ⟨608849, by rfl⟩ : syracuseStep 811799 = 1217699) B1217699
theorem B811819 : Blo 810345 811819 := bstep (se 1 (by rfl) ⟨608864, by rfl⟩ : syracuseStep 811819 = 1217729) B1217729
theorem B811831 : Blo 810345 811831 := bstep (se 1 (by rfl) ⟨608873, by rfl⟩ : syracuseStep 811831 = 1217747) B1217747
theorem B811851 : Blo 810345 811851 := bstep (se 1 (by rfl) ⟨608888, by rfl⟩ : syracuseStep 811851 = 1217777) B1217777
theorem B2057035 : Blo 810345 2057035 := bstep (se 1 (by rfl) ⟨1542776, by rfl⟩ : syracuseStep 2057035 = 3085553) B3085553
theorem B811863 : Blo 810345 811863 := bstep (se 1 (by rfl) ⟨608897, by rfl⟩ : syracuseStep 811863 = 1217795) B1217795
theorem B811883 : Blo 810345 811883 := bstep (se 1 (by rfl) ⟨608912, by rfl⟩ : syracuseStep 811883 = 1217825) B1217825
theorem B811895 : Blo 810345 811895 := bstep (se 1 (by rfl) ⟨608921, by rfl⟩ : syracuseStep 811895 = 1217843) B1217843
theorem B811915 : Blo 810345 811915 := bstep (se 1 (by rfl) ⟨608936, by rfl⟩ : syracuseStep 811915 = 1217873) B1217873
theorem B1303435 : Blo 810345 1303435 := bstep (se 1 (by rfl) ⟨977576, by rfl⟩ : syracuseStep 1303435 = 1955153) B1955153
theorem B811927 : Blo 810345 811927 := bstep (se 1 (by rfl) ⟨608945, by rfl⟩ : syracuseStep 811927 = 1217891) B1217891
theorem B1827737 : Blo 810345 1827737 := bstep (se 2 (by rfl) ⟨685401, by rfl⟩ : syracuseStep 1827737 = 1370803) B1370803
theorem B811947 : Blo 810345 811947 := bstep (se 1 (by rfl) ⟨608960, by rfl⟩ : syracuseStep 811947 = 1217921) B1217921
theorem B811959 : Blo 810345 811959 := bstep (se 1 (by rfl) ⟨608969, by rfl⟩ : syracuseStep 811959 = 1217939) B1217939
theorem B811979 : Blo 810345 811979 := bstep (se 1 (by rfl) ⟨608984, by rfl⟩ : syracuseStep 811979 = 1217969) B1217969
theorem B811991 : Blo 810345 811991 := bstep (se 1 (by rfl) ⟨608993, by rfl⟩ : syracuseStep 811991 = 1217987) B1217987
theorem B2057177 : Blo 810345 2057177 := bstep (se 2 (by rfl) ⟨771441, by rfl⟩ : syracuseStep 2057177 = 1542883) B1542883
theorem B2745305 : Blo 810345 2745305 := bstep (se 2 (by rfl) ⟨1029489, by rfl⟩ : syracuseStep 2745305 = 2058979) B2058979
theorem B812011 : Blo 810345 812011 := bstep (se 1 (by rfl) ⟨609008, by rfl⟩ : syracuseStep 812011 = 1218017) B1218017
theorem B1827827 : Blo 810345 1827827 := bstep (se 1 (by rfl) ⟨1370870, by rfl⟩ : syracuseStep 1827827 = 2741741) B2741741
theorem B812023 : Blo 810345 812023 := bstep (se 1 (by rfl) ⟨609017, by rfl⟩ : syracuseStep 812023 = 1218035) B1218035
theorem B812043 : Blo 810345 812043 := bstep (se 1 (by rfl) ⟨609032, by rfl⟩ : syracuseStep 812043 = 1218065) B1218065
theorem B812055 : Blo 810345 812055 := bstep (se 1 (by rfl) ⟨609041, by rfl⟩ : syracuseStep 812055 = 1218083) B1218083
theorem B1827863 : Blo 810345 1827863 := bstep (se 1 (by rfl) ⟨1370897, by rfl⟩ : syracuseStep 1827863 = 2741795) B2741795
theorem B812075 : Blo 810345 812075 := bstep (se 1 (by rfl) ⟨609056, by rfl⟩ : syracuseStep 812075 = 1218113) B1218113
theorem B812087 : Blo 810345 812087 := bstep (se 1 (by rfl) ⟨609065, by rfl⟩ : syracuseStep 812087 = 1218131) B1218131
theorem B1369163 : Blo 810345 1369163 := bstep (se 1 (by rfl) ⟨1026872, by rfl⟩ : syracuseStep 1369163 = 2053745) B2053745
theorem B812107 : Blo 810345 812107 := bstep (se 1 (by rfl) ⟨609080, by rfl⟩ : syracuseStep 812107 = 1218161) B1218161
theorem B812119 : Blo 810345 812119 := bstep (se 1 (by rfl) ⟨609089, by rfl⟩ : syracuseStep 812119 = 1218179) B1218179
theorem B812139 : Blo 810345 812139 := bstep (se 1 (by rfl) ⟨609104, by rfl⟩ : syracuseStep 812139 = 1218209) B1218209
theorem B812151 : Blo 810345 812151 := bstep (se 1 (by rfl) ⟨609113, by rfl⟩ : syracuseStep 812151 = 1218227) B1218227
theorem B812171 : Blo 810345 812171 := bstep (se 1 (by rfl) ⟨609128, by rfl⟩ : syracuseStep 812171 = 1218257) B1218257
theorem B812183 : Blo 810345 812183 := bstep (se 1 (by rfl) ⟨609137, by rfl⟩ : syracuseStep 812183 = 1218275) B1218275
theorem B1303705 : Blo 810345 1303705 := bstep (se 2 (by rfl) ⟨488889, by rfl⟩ : syracuseStep 1303705 = 977779) B977779
theorem B812203 : Blo 810345 812203 := bstep (se 1 (by rfl) ⟨609152, by rfl⟩ : syracuseStep 812203 = 1218305) B1218305
theorem B812215 : Blo 810345 812215 := bstep (se 1 (by rfl) ⟨609161, by rfl⟩ : syracuseStep 812215 = 1218323) B1218323
theorem B1369291 : Blo 810345 1369291 := bstep (se 1 (by rfl) ⟨1026968, by rfl⟩ : syracuseStep 1369291 = 2053937) B2053937
theorem B812235 : Blo 810345 812235 := bstep (se 1 (by rfl) ⟨609176, by rfl⟩ : syracuseStep 812235 = 1218353) B1218353
theorem B1828043 : Blo 810345 1828043 := bstep (se 1 (by rfl) ⟨1371032, by rfl⟩ : syracuseStep 1828043 = 2742065) B2742065
theorem B812247 : Blo 810345 812247 := bstep (se 1 (by rfl) ⟨609185, by rfl⟩ : syracuseStep 812247 = 1218371) B1218371
theorem B1303769 : Blo 810345 1303769 := bstep (se 2 (by rfl) ⟨488913, by rfl⟩ : syracuseStep 1303769 = 977827) B977827
theorem B812267 : Blo 810345 812267 := bstep (se 1 (by rfl) ⟨609200, by rfl⟩ : syracuseStep 812267 = 1218401) B1218401
theorem B812279 : Blo 810345 812279 := bstep (se 1 (by rfl) ⟨609209, by rfl⟩ : syracuseStep 812279 = 1218419) B1218419
theorem B1828097 : Blo 810345 1828097 := bstep (se 2 (by rfl) ⟨685536, by rfl⟩ : syracuseStep 1828097 = 1371073) B1371073
theorem B11101445 : Blo 810345 11101445 := bstep (se 4 (by rfl) ⟨1040760, by rfl⟩ : syracuseStep 11101445 = 2081521) B2081521
theorem B812299 : Blo 810345 812299 := bstep (se 1 (by rfl) ⟨609224, by rfl⟩ : syracuseStep 812299 = 1218449) B1218449
theorem B812311 : Blo 810345 812311 := bstep (se 1 (by rfl) ⟨609233, by rfl⟩ : syracuseStep 812311 = 1218467) B1218467
theorem B812331 : Blo 810345 812331 := bstep (se 1 (by rfl) ⟨609248, by rfl⟩ : syracuseStep 812331 = 1218497) B1218497
theorem B812343 : Blo 810345 812343 := bstep (se 1 (by rfl) ⟨609257, by rfl⟩ : syracuseStep 812343 = 1218515) B1218515
theorem B812363 : Blo 810345 812363 := bstep (se 1 (by rfl) ⟨609272, by rfl⟩ : syracuseStep 812363 = 1218545) B1218545
theorem B812375 : Blo 810345 812375 := bstep (se 1 (by rfl) ⟨609281, by rfl⟩ : syracuseStep 812375 = 1218563) B1218563
theorem B1369433 : Blo 810345 1369433 := bstep (se 2 (by rfl) ⟨513537, by rfl⟩ : syracuseStep 1369433 = 1027075) B1027075
theorem B812395 : Blo 810345 812395 := bstep (se 1 (by rfl) ⟨609296, by rfl⟩ : syracuseStep 812395 = 1218593) B1218593
theorem B812407 : Blo 810345 812407 := bstep (se 1 (by rfl) ⟨609305, by rfl⟩ : syracuseStep 812407 = 1218611) B1218611
theorem B812427 : Blo 810345 812427 := bstep (se 1 (by rfl) ⟨609320, by rfl⟩ : syracuseStep 812427 = 1218641) B1218641
theorem B812439 : Blo 810345 812439 := bstep (se 1 (by rfl) ⟨609329, by rfl⟩ : syracuseStep 812439 = 1218659) B1218659
theorem B812459 : Blo 810345 812459 := bstep (se 1 (by rfl) ⟨609344, by rfl⟩ : syracuseStep 812459 = 1218689) B1218689
theorem B812471 : Blo 810345 812471 := bstep (se 1 (by rfl) ⟨609353, by rfl⟩ : syracuseStep 812471 = 1218707) B1218707
theorem B812491 : Blo 810345 812491 := bstep (se 1 (by rfl) ⟨609368, by rfl⟩ : syracuseStep 812491 = 1218737) B1218737
theorem B812503 : Blo 810345 812503 := bstep (se 1 (by rfl) ⟨609377, by rfl⟩ : syracuseStep 812503 = 1218755) B1218755
theorem B1369561 : Blo 810345 1369561 := bstep (se 2 (by rfl) ⟨513585, by rfl⟩ : syracuseStep 1369561 = 1027171) B1027171
theorem B1828313 : Blo 810345 1828313 := bstep (se 2 (by rfl) ⟨685617, by rfl⟩ : syracuseStep 1828313 = 1371235) B1371235
theorem B812523 : Blo 810345 812523 := bstep (se 1 (by rfl) ⟨609392, by rfl⟩ : syracuseStep 812523 = 1218785) B1218785
theorem B812535 : Blo 810345 812535 := bstep (se 1 (by rfl) ⟨609401, by rfl⟩ : syracuseStep 812535 = 1218803) B1218803
theorem B812555 : Blo 810345 812555 := bstep (se 1 (by rfl) ⟨609416, by rfl⟩ : syracuseStep 812555 = 1218833) B1218833
theorem B812567 : Blo 810345 812567 := bstep (se 1 (by rfl) ⟨609425, by rfl⟩ : syracuseStep 812567 = 1218851) B1218851
theorem B812587 : Blo 810345 812587 := bstep (se 1 (by rfl) ⟨609440, by rfl⟩ : syracuseStep 812587 = 1218881) B1218881
theorem B1828403 : Blo 810345 1828403 := bstep (se 1 (by rfl) ⟨1371302, by rfl⟩ : syracuseStep 1828403 = 2742605) B2742605
theorem B812599 : Blo 810345 812599 := bstep (se 1 (by rfl) ⟨609449, by rfl⟩ : syracuseStep 812599 = 1218899) B1218899
theorem B812619 : Blo 810345 812619 := bstep (se 1 (by rfl) ⟨609464, by rfl⟩ : syracuseStep 812619 = 1218929) B1218929
theorem B812631 : Blo 810345 812631 := bstep (se 1 (by rfl) ⟨609473, by rfl⟩ : syracuseStep 812631 = 1218947) B1218947
theorem B1828439 : Blo 810345 1828439 := bstep (se 1 (by rfl) ⟨1371329, by rfl⟩ : syracuseStep 1828439 = 2742659) B2742659
theorem B812651 : Blo 810345 812651 := bstep (se 1 (by rfl) ⟨609488, by rfl⟩ : syracuseStep 812651 = 1218977) B1218977
theorem B812663 : Blo 810345 812663 := bstep (se 1 (by rfl) ⟨609497, by rfl⟩ : syracuseStep 812663 = 1218995) B1218995
theorem B812683 : Blo 810345 812683 := bstep (se 1 (by rfl) ⟨609512, by rfl⟩ : syracuseStep 812683 = 1219025) B1219025
theorem B812695 : Blo 810345 812695 := bstep (se 1 (by rfl) ⟨609521, by rfl⟩ : syracuseStep 812695 = 1219043) B1219043
theorem B2746007 : Blo 810345 2746007 := bstep (se 1 (by rfl) ⟨2059505, by rfl⟩ : syracuseStep 2746007 = 4119011) B4119011
theorem B812715 : Blo 810345 812715 := bstep (se 1 (by rfl) ⟨609536, by rfl⟩ : syracuseStep 812715 = 1219073) B1219073
theorem B812727 : Blo 810345 812727 := bstep (se 1 (by rfl) ⟨609545, by rfl⟩ : syracuseStep 812727 = 1219091) B1219091
theorem B812747 : Blo 810345 812747 := bstep (se 1 (by rfl) ⟨609560, by rfl⟩ : syracuseStep 812747 = 1219121) B1219121
theorem B812759 : Blo 810345 812759 := bstep (se 1 (by rfl) ⟨609569, by rfl⟩ : syracuseStep 812759 = 1219139) B1219139
theorem B812779 : Blo 810345 812779 := bstep (se 1 (by rfl) ⟨609584, by rfl⟩ : syracuseStep 812779 = 1219169) B1219169
theorem B812791 : Blo 810345 812791 := bstep (se 1 (by rfl) ⟨609593, by rfl⟩ : syracuseStep 812791 = 1219187) B1219187
theorem B1828619 : Blo 810345 1828619 := bstep (se 1 (by rfl) ⟨1371464, by rfl⟩ : syracuseStep 1828619 = 2742929) B2742929
theorem B812811 : Blo 810345 812811 := bstep (se 1 (by rfl) ⟨609608, by rfl⟩ : syracuseStep 812811 = 1219217) B1219217
theorem B812823 : Blo 810345 812823 := bstep (se 1 (by rfl) ⟨609617, by rfl⟩ : syracuseStep 812823 = 1219235) B1219235
theorem B2058007 : Blo 810345 2058007 := bstep (se 1 (by rfl) ⟨1543505, by rfl⟩ : syracuseStep 2058007 = 3087011) B3087011
theorem B812843 : Blo 810345 812843 := bstep (se 1 (by rfl) ⟨609632, by rfl⟩ : syracuseStep 812843 = 1219265) B1219265
theorem B4122413 : Blo 810345 4122413 := bstep (se 3 (by rfl) ⟨772952, by rfl⟩ : syracuseStep 4122413 = 1545905) B1545905
theorem B812855 : Blo 810345 812855 := bstep (se 1 (by rfl) ⟨609641, by rfl⟩ : syracuseStep 812855 = 1219283) B1219283
theorem B1828673 : Blo 810345 1828673 := bstep (se 2 (by rfl) ⟨685752, by rfl⟩ : syracuseStep 1828673 = 1371505) B1371505
theorem B812875 : Blo 810345 812875 := bstep (se 1 (by rfl) ⟨609656, by rfl⟩ : syracuseStep 812875 = 1219313) B1219313
theorem B812887 : Blo 810345 812887 := bstep (se 1 (by rfl) ⟨609665, by rfl⟩ : syracuseStep 812887 = 1219331) B1219331
theorem B812907 : Blo 810345 812907 := bstep (se 1 (by rfl) ⟨609680, by rfl⟩ : syracuseStep 812907 = 1219361) B1219361
theorem B812919 : Blo 810345 812919 := bstep (se 1 (by rfl) ⟨609689, by rfl⟩ : syracuseStep 812919 = 1219379) B1219379
theorem B812939 : Blo 810345 812939 := bstep (se 1 (by rfl) ⟨609704, by rfl⟩ : syracuseStep 812939 = 1219409) B1219409
theorem B812951 : Blo 810345 812951 := bstep (se 1 (by rfl) ⟨609713, by rfl⟩ : syracuseStep 812951 = 1219427) B1219427
theorem B812971 : Blo 810345 812971 := bstep (se 1 (by rfl) ⟨609728, by rfl⟩ : syracuseStep 812971 = 1219457) B1219457
theorem B812983 : Blo 810345 812983 := bstep (se 1 (by rfl) ⟨609737, by rfl⟩ : syracuseStep 812983 = 1219475) B1219475
theorem B813003 : Blo 810345 813003 := bstep (se 1 (by rfl) ⟨609752, by rfl⟩ : syracuseStep 813003 = 1219505) B1219505
theorem B813015 : Blo 810345 813015 := bstep (se 1 (by rfl) ⟨609761, by rfl⟩ : syracuseStep 813015 = 1219523) B1219523
theorem B13887449 : Blo 810345 13887449 := bstep (se 2 (by rfl) ⟨5207793, by rfl⟩ : syracuseStep 13887449 = 10415587) B10415587
theorem B813035 : Blo 810345 813035 := bstep (se 1 (by rfl) ⟨609776, by rfl⟩ : syracuseStep 813035 = 1219553) B1219553
theorem B813047 : Blo 810345 813047 := bstep (se 1 (by rfl) ⟨609785, by rfl⟩ : syracuseStep 813047 = 1219571) B1219571
theorem B813067 : Blo 810345 813067 := bstep (se 1 (by rfl) ⟨609800, by rfl⟩ : syracuseStep 813067 = 1219601) B1219601
theorem B8775697 : Blo 810345 8775697 := bstep (se 2 (by rfl) ⟨3290886, by rfl⟩ : syracuseStep 8775697 = 6581773) B6581773
theorem B1370135 : Blo 810345 1370135 := bstep (se 1 (by rfl) ⟨1027601, by rfl⟩ : syracuseStep 1370135 = 2055203) B2055203
theorem B813079 : Blo 810345 813079 := bstep (se 1 (by rfl) ⟨609809, by rfl⟩ : syracuseStep 813079 = 1219619) B1219619
theorem B1828889 : Blo 810345 1828889 := bstep (se 2 (by rfl) ⟨685833, by rfl⟩ : syracuseStep 1828889 = 1371667) B1371667
theorem B813099 : Blo 810345 813099 := bstep (se 1 (by rfl) ⟨609824, by rfl⟩ : syracuseStep 813099 = 1219649) B1219649
theorem B813111 : Blo 810345 813111 := bstep (se 1 (by rfl) ⟨609833, by rfl⟩ : syracuseStep 813111 = 1219667) B1219667
theorem B813131 : Blo 810345 813131 := bstep (se 1 (by rfl) ⟨609848, by rfl⟩ : syracuseStep 813131 = 1219697) B1219697
theorem B813143 : Blo 810345 813143 := bstep (se 1 (by rfl) ⟨609857, by rfl⟩ : syracuseStep 813143 = 1219715) B1219715
theorem B813163 : Blo 810345 813163 := bstep (se 1 (by rfl) ⟨609872, by rfl⟩ : syracuseStep 813163 = 1219745) B1219745
theorem B1828979 : Blo 810345 1828979 := bstep (se 1 (by rfl) ⟨1371734, by rfl⟩ : syracuseStep 1828979 = 2743469) B2743469
theorem B813175 : Blo 810345 813175 := bstep (se 1 (by rfl) ⟨609881, by rfl⟩ : syracuseStep 813175 = 1219763) B1219763
theorem B813195 : Blo 810345 813195 := bstep (se 1 (by rfl) ⟨609896, by rfl⟩ : syracuseStep 813195 = 1219793) B1219793
theorem B1370263 : Blo 810345 1370263 := bstep (se 1 (by rfl) ⟨1027697, by rfl⟩ : syracuseStep 1370263 = 2055395) B2055395
theorem B1829015 : Blo 810345 1829015 := bstep (se 1 (by rfl) ⟨1371761, by rfl⟩ : syracuseStep 1829015 = 2743523) B2743523
theorem B813207 : Blo 810345 813207 := bstep (se 1 (by rfl) ⟨609905, by rfl⟩ : syracuseStep 813207 = 1219811) B1219811
theorem B813227 : Blo 810345 813227 := bstep (se 1 (by rfl) ⟨609920, by rfl⟩ : syracuseStep 813227 = 1219841) B1219841
theorem B2746547 : Blo 810345 2746547 := bstep (se 1 (by rfl) ⟨2059910, by rfl⟩ : syracuseStep 2746547 = 4119821) B4119821
theorem B813239 : Blo 810345 813239 := bstep (se 1 (by rfl) ⟨609929, by rfl⟩ : syracuseStep 813239 = 1219859) B1219859
theorem B2058443 : Blo 810345 2058443 := bstep (se 1 (by rfl) ⟨1543832, by rfl⟩ : syracuseStep 2058443 = 3087665) B3087665
theorem B813259 : Blo 810345 813259 := bstep (se 1 (by rfl) ⟨609944, by rfl⟩ : syracuseStep 813259 = 1219889) B1219889
theorem B813271 : Blo 810345 813271 := bstep (se 1 (by rfl) ⟨609953, by rfl⟩ : syracuseStep 813271 = 1219907) B1219907
theorem B813291 : Blo 810345 813291 := bstep (se 1 (by rfl) ⟨609968, by rfl⟩ : syracuseStep 813291 = 1219937) B1219937
theorem B813303 : Blo 810345 813303 := bstep (se 1 (by rfl) ⟨609977, by rfl⟩ : syracuseStep 813303 = 1219955) B1219955
theorem B813323 : Blo 810345 813323 := bstep (se 1 (by rfl) ⟨609992, by rfl⟩ : syracuseStep 813323 = 1219985) B1219985
theorem B813335 : Blo 810345 813335 := bstep (se 1 (by rfl) ⟨610001, by rfl⟩ : syracuseStep 813335 = 1220003) B1220003
theorem B911659 : Blo 810345 911659 := bstep (se 1 (by rfl) ⟨683744, by rfl⟩ : syracuseStep 911659 = 1367489) B1367489
theorem B813355 : Blo 810345 813355 := bstep (se 1 (by rfl) ⟨610016, by rfl⟩ : syracuseStep 813355 = 1220033) B1220033
theorem B813367 : Blo 810345 813367 := bstep (se 1 (by rfl) ⟨610025, by rfl⟩ : syracuseStep 813367 = 1220051) B1220051
theorem B1829195 : Blo 810345 1829195 := bstep (se 1 (by rfl) ⟨1371896, by rfl⟩ : syracuseStep 1829195 = 2743793) B2743793
theorem B813387 : Blo 810345 813387 := bstep (se 1 (by rfl) ⟨610040, by rfl⟩ : syracuseStep 813387 = 1220081) B1220081
theorem B813399 : Blo 810345 813399 := bstep (se 1 (by rfl) ⟨610049, by rfl⟩ : syracuseStep 813399 = 1220099) B1220099
theorem B813419 : Blo 810345 813419 := bstep (se 1 (by rfl) ⟨610064, by rfl⟩ : syracuseStep 813419 = 1220129) B1220129
theorem B813431 : Blo 810345 813431 := bstep (se 1 (by rfl) ⟨610073, by rfl⟩ : syracuseStep 813431 = 1220147) B1220147
theorem B1829249 : Blo 810345 1829249 := bstep (se 2 (by rfl) ⟨685968, by rfl⟩ : syracuseStep 1829249 = 1371937) B1371937
theorem B813451 : Blo 810345 813451 := bstep (se 1 (by rfl) ⟨610088, by rfl⟩ : syracuseStep 813451 = 1220177) B1220177
theorem B911767 : Blo 810345 911767 := bstep (se 1 (by rfl) ⟨683825, by rfl⟩ : syracuseStep 911767 = 1367651) B1367651
theorem B813463 : Blo 810345 813463 := bstep (se 1 (by rfl) ⟨610097, by rfl⟩ : syracuseStep 813463 = 1220195) B1220195
theorem B813483 : Blo 810345 813483 := bstep (se 1 (by rfl) ⟨610112, by rfl⟩ : syracuseStep 813483 = 1220225) B1220225
theorem B813495 : Blo 810345 813495 := bstep (se 1 (by rfl) ⟨610121, by rfl⟩ : syracuseStep 813495 = 1220243) B1220243
theorem B2746817 : Blo 810345 2746817 := bstep (se 2 (by rfl) ⟨1030056, by rfl⟩ : syracuseStep 2746817 = 2060113) B2060113
theorem B813515 : Blo 810345 813515 := bstep (se 1 (by rfl) ⟨610136, by rfl⟩ : syracuseStep 813515 = 1220273) B1220273
theorem B813527 : Blo 810345 813527 := bstep (se 1 (by rfl) ⟨610145, by rfl⟩ : syracuseStep 813527 = 1220291) B1220291
theorem B813547 : Blo 810345 813547 := bstep (se 1 (by rfl) ⟨610160, by rfl⟩ : syracuseStep 813547 = 1220321) B1220321
theorem B813559 : Blo 810345 813559 := bstep (se 1 (by rfl) ⟨610169, by rfl⟩ : syracuseStep 813559 = 1220339) B1220339
theorem B813579 : Blo 810345 813579 := bstep (se 1 (by rfl) ⟨610184, by rfl⟩ : syracuseStep 813579 = 1220369) B1220369
theorem B813591 : Blo 810345 813591 := bstep (se 1 (by rfl) ⟨610193, by rfl⟩ : syracuseStep 813591 = 1220387) B1220387
theorem B813611 : Blo 810345 813611 := bstep (se 1 (by rfl) ⟨610208, by rfl⟩ : syracuseStep 813611 = 1220417) B1220417
theorem B813623 : Blo 810345 813623 := bstep (se 1 (by rfl) ⟨610217, by rfl⟩ : syracuseStep 813623 = 1220435) B1220435
theorem B2058817 : Blo 810345 2058817 := bstep (se 2 (by rfl) ⟨772056, by rfl⟩ : syracuseStep 2058817 = 1544113) B1544113
theorem B911947 : Blo 810345 911947 := bstep (se 1 (by rfl) ⟨683960, by rfl⟩ : syracuseStep 911947 = 1367921) B1367921
theorem B813643 : Blo 810345 813643 := bstep (se 1 (by rfl) ⟨610232, by rfl⟩ : syracuseStep 813643 = 1220465) B1220465
theorem B813655 : Blo 810345 813655 := bstep (se 1 (by rfl) ⟨610241, by rfl⟩ : syracuseStep 813655 = 1220483) B1220483
theorem B1829465 : Blo 810345 1829465 := bstep (se 2 (by rfl) ⟨686049, by rfl⟩ : syracuseStep 1829465 = 1372099) B1372099
theorem B813675 : Blo 810345 813675 := bstep (se 1 (by rfl) ⟨610256, by rfl⟩ : syracuseStep 813675 = 1220513) B1220513
theorem B813687 : Blo 810345 813687 := bstep (se 1 (by rfl) ⟨610265, by rfl⟩ : syracuseStep 813687 = 1220531) B1220531
theorem B813707 : Blo 810345 813707 := bstep (se 1 (by rfl) ⟨610280, by rfl⟩ : syracuseStep 813707 = 1220561) B1220561
theorem B813719 : Blo 810345 813719 := bstep (se 1 (by rfl) ⟨610289, by rfl⟩ : syracuseStep 813719 = 1220579) B1220579
theorem B813739 : Blo 810345 813739 := bstep (se 1 (by rfl) ⟨610304, by rfl⟩ : syracuseStep 813739 = 1220609) B1220609
theorem B1829555 : Blo 810345 1829555 := bstep (se 1 (by rfl) ⟨1372166, by rfl⟩ : syracuseStep 1829555 = 2744333) B2744333
theorem B912055 : Blo 810345 912055 := bstep (se 1 (by rfl) ⟨684041, by rfl⟩ : syracuseStep 912055 = 1368083) B1368083
theorem B813751 : Blo 810345 813751 := bstep (se 1 (by rfl) ⟨610313, by rfl⟩ : syracuseStep 813751 = 1220627) B1220627
theorem B813771 : Blo 810345 813771 := bstep (se 1 (by rfl) ⟨610328, by rfl⟩ : syracuseStep 813771 = 1220657) B1220657
theorem B1829591 : Blo 810345 1829591 := bstep (se 1 (by rfl) ⟨1372193, by rfl⟩ : syracuseStep 1829591 = 2744387) B2744387
theorem B813783 : Blo 810345 813783 := bstep (se 1 (by rfl) ⟨610337, by rfl⟩ : syracuseStep 813783 = 1220675) B1220675
theorem B813803 : Blo 810345 813803 := bstep (se 1 (by rfl) ⟨610352, by rfl⟩ : syracuseStep 813803 = 1220705) B1220705
theorem B813815 : Blo 810345 813815 := bstep (se 1 (by rfl) ⟨610361, by rfl⟩ : syracuseStep 813815 = 1220723) B1220723
theorem B3468035 : Blo 810345 3468035 := bstep (se 1 (by rfl) ⟨2601026, by rfl⟩ : syracuseStep 3468035 = 5202053) B5202053
theorem B1370891 : Blo 810345 1370891 := bstep (se 1 (by rfl) ⟨1028168, by rfl⟩ : syracuseStep 1370891 = 2056337) B2056337
theorem B813835 : Blo 810345 813835 := bstep (se 1 (by rfl) ⟨610376, by rfl⟩ : syracuseStep 813835 = 1220753) B1220753
theorem B813847 : Blo 810345 813847 := bstep (se 1 (by rfl) ⟨610385, by rfl⟩ : syracuseStep 813847 = 1220771) B1220771
theorem B813867 : Blo 810345 813867 := bstep (se 1 (by rfl) ⟨610400, by rfl⟩ : syracuseStep 813867 = 1220801) B1220801
theorem B813879 : Blo 810345 813879 := bstep (se 1 (by rfl) ⟨610409, by rfl⟩ : syracuseStep 813879 = 1220819) B1220819
theorem B813899 : Blo 810345 813899 := bstep (se 1 (by rfl) ⟨610424, by rfl⟩ : syracuseStep 813899 = 1220849) B1220849
theorem B813911 : Blo 810345 813911 := bstep (se 1 (by rfl) ⟨610433, by rfl⟩ : syracuseStep 813911 = 1220867) B1220867
theorem B912235 : Blo 810345 912235 := bstep (se 1 (by rfl) ⟨684176, by rfl⟩ : syracuseStep 912235 = 1368353) B1368353
theorem B813931 : Blo 810345 813931 := bstep (se 1 (by rfl) ⟨610448, by rfl⟩ : syracuseStep 813931 = 1220897) B1220897
theorem B813943 : Blo 810345 813943 := bstep (se 1 (by rfl) ⟨610457, by rfl⟩ : syracuseStep 813943 = 1220915) B1220915
theorem B1371019 : Blo 810345 1371019 := bstep (se 1 (by rfl) ⟨1028264, by rfl⟩ : syracuseStep 1371019 = 2056529) B2056529
theorem B1829771 : Blo 810345 1829771 := bstep (se 1 (by rfl) ⟨1372328, by rfl⟩ : syracuseStep 1829771 = 2744657) B2744657
theorem B813963 : Blo 810345 813963 := bstep (se 1 (by rfl) ⟨610472, by rfl⟩ : syracuseStep 813963 = 1220945) B1220945
theorem B813975 : Blo 810345 813975 := bstep (se 1 (by rfl) ⟨610481, by rfl⟩ : syracuseStep 813975 = 1220963) B1220963
theorem B813995 : Blo 810345 813995 := bstep (se 1 (by rfl) ⟨610496, by rfl⟩ : syracuseStep 813995 = 1220993) B1220993
theorem B814007 : Blo 810345 814007 := bstep (se 1 (by rfl) ⟨610505, by rfl⟩ : syracuseStep 814007 = 1221011) B1221011
theorem B1829825 : Blo 810345 1829825 := bstep (se 2 (by rfl) ⟨686184, by rfl⟩ : syracuseStep 1829825 = 1372369) B1372369
theorem B814027 : Blo 810345 814027 := bstep (se 1 (by rfl) ⟨610520, by rfl⟩ : syracuseStep 814027 = 1221041) B1221041
theorem B912343 : Blo 810345 912343 := bstep (se 1 (by rfl) ⟨684257, by rfl⟩ : syracuseStep 912343 = 1368515) B1368515
theorem B814039 : Blo 810345 814039 := bstep (se 1 (by rfl) ⟨610529, by rfl⟩ : syracuseStep 814039 = 1221059) B1221059
theorem B2747357 : Blo 810345 2747357 := bstep (se 3 (by rfl) ⟨515129, by rfl⟩ : syracuseStep 2747357 = 1030259) B1030259
theorem B814059 : Blo 810345 814059 := bstep (se 1 (by rfl) ⟨610544, by rfl⟩ : syracuseStep 814059 = 1221089) B1221089
theorem B814071 : Blo 810345 814071 := bstep (se 1 (by rfl) ⟨610553, by rfl⟩ : syracuseStep 814071 = 1221107) B1221107
theorem B814091 : Blo 810345 814091 := bstep (se 1 (by rfl) ⟨610568, by rfl⟩ : syracuseStep 814091 = 1221137) B1221137
theorem B814103 : Blo 810345 814103 := bstep (se 1 (by rfl) ⟨610577, by rfl⟩ : syracuseStep 814103 = 1221155) B1221155
theorem B1371161 : Blo 810345 1371161 := bstep (se 2 (by rfl) ⟨514185, by rfl⟩ : syracuseStep 1371161 = 1028371) B1028371
theorem B814123 : Blo 810345 814123 := bstep (se 1 (by rfl) ⟨610592, by rfl⟩ : syracuseStep 814123 = 1221185) B1221185
theorem B814135 : Blo 810345 814135 := bstep (se 1 (by rfl) ⟨610601, by rfl⟩ : syracuseStep 814135 = 1221203) B1221203
theorem B814155 : Blo 810345 814155 := bstep (se 1 (by rfl) ⟨610616, by rfl⟩ : syracuseStep 814155 = 1221233) B1221233
theorem B814167 : Blo 810345 814167 := bstep (se 1 (by rfl) ⟨610625, by rfl⟩ : syracuseStep 814167 = 1221251) B1221251
theorem B814187 : Blo 810345 814187 := bstep (se 1 (by rfl) ⟨610640, by rfl⟩ : syracuseStep 814187 = 1221281) B1221281
theorem B814199 : Blo 810345 814199 := bstep (se 1 (by rfl) ⟨610649, by rfl⟩ : syracuseStep 814199 = 1221299) B1221299
theorem B912523 : Blo 810345 912523 := bstep (se 1 (by rfl) ⟨684392, by rfl⟩ : syracuseStep 912523 = 1368785) B1368785
theorem B814219 : Blo 810345 814219 := bstep (se 1 (by rfl) ⟨610664, by rfl⟩ : syracuseStep 814219 = 1221329) B1221329
theorem B2059415 : Blo 810345 2059415 := bstep (se 1 (by rfl) ⟨1544561, by rfl⟩ : syracuseStep 2059415 = 3089123) B3089123
theorem B814231 : Blo 810345 814231 := bstep (se 1 (by rfl) ⟨610673, by rfl⟩ : syracuseStep 814231 = 1221347) B1221347
theorem B1371289 : Blo 810345 1371289 := bstep (se 2 (by rfl) ⟨514233, by rfl⟩ : syracuseStep 1371289 = 1028467) B1028467
theorem B1830041 : Blo 810345 1830041 := bstep (se 2 (by rfl) ⟨686265, by rfl⟩ : syracuseStep 1830041 = 1372531) B1372531
theorem B814251 : Blo 810345 814251 := bstep (se 1 (by rfl) ⟨610688, by rfl⟩ : syracuseStep 814251 = 1221377) B1221377
theorem B814263 : Blo 810345 814263 := bstep (se 1 (by rfl) ⟨610697, by rfl⟩ : syracuseStep 814263 = 1221395) B1221395
theorem B814283 : Blo 810345 814283 := bstep (se 1 (by rfl) ⟨610712, by rfl⟩ : syracuseStep 814283 = 1221425) B1221425
theorem B814295 : Blo 810345 814295 := bstep (se 1 (by rfl) ⟨610721, by rfl⟩ : syracuseStep 814295 = 1221443) B1221443
theorem B814315 : Blo 810345 814315 := bstep (se 1 (by rfl) ⟨610736, by rfl⟩ : syracuseStep 814315 = 1221473) B1221473
theorem B1830131 : Blo 810345 1830131 := bstep (se 1 (by rfl) ⟨1372598, by rfl⟩ : syracuseStep 1830131 = 2745197) B2745197
theorem B912631 : Blo 810345 912631 := bstep (se 1 (by rfl) ⟨684473, by rfl⟩ : syracuseStep 912631 = 1368947) B1368947
theorem B814327 : Blo 810345 814327 := bstep (se 1 (by rfl) ⟨610745, by rfl⟩ : syracuseStep 814327 = 1221491) B1221491
theorem B1830167 : Blo 810345 1830167 := bstep (se 1 (by rfl) ⟨1372625, by rfl⟩ : syracuseStep 1830167 = 2745251) B2745251
theorem B912811 : Blo 810345 912811 := bstep (se 1 (by rfl) ⟨684608, by rfl⟩ : syracuseStep 912811 = 1369217) B1369217
theorem B1830347 : Blo 810345 1830347 := bstep (se 1 (by rfl) ⟨1372760, by rfl⟩ : syracuseStep 1830347 = 2745521) B2745521
theorem B1732097 : Blo 810345 1732097 := bstep (se 2 (by rfl) ⟨649536, by rfl⟩ : syracuseStep 1732097 = 1299073) B1299073
theorem B1830401 : Blo 810345 1830401 := bstep (se 2 (by rfl) ⟨686400, by rfl⟩ : syracuseStep 1830401 = 1372801) B1372801
theorem B912919 : Blo 810345 912919 := bstep (se 1 (by rfl) ⟨684689, by rfl⟩ : syracuseStep 912919 = 1369379) B1369379
theorem B913099 : Blo 810345 913099 := bstep (se 1 (by rfl) ⟨684824, by rfl⟩ : syracuseStep 913099 = 1369649) B1369649
theorem B1371863 : Blo 810345 1371863 := bstep (se 1 (by rfl) ⟨1028897, by rfl⟩ : syracuseStep 1371863 = 2057795) B2057795
theorem B1830617 : Blo 810345 1830617 := bstep (se 2 (by rfl) ⟨686481, by rfl⟩ : syracuseStep 1830617 = 1372963) B1372963
theorem B1830707 : Blo 810345 1830707 := bstep (se 1 (by rfl) ⟨1373030, by rfl⟩ : syracuseStep 1830707 = 2746061) B2746061
theorem B913207 : Blo 810345 913207 := bstep (se 1 (by rfl) ⟨684905, by rfl⟩ : syracuseStep 913207 = 1369811) B1369811
theorem B1371991 : Blo 810345 1371991 := bstep (se 1 (by rfl) ⟨1028993, by rfl⟩ : syracuseStep 1371991 = 2057987) B2057987
theorem B1830743 : Blo 810345 1830743 := bstep (se 1 (by rfl) ⟨1373057, by rfl⟩ : syracuseStep 1830743 = 2746115) B2746115
theorem B2060225 : Blo 810345 2060225 := bstep (se 2 (by rfl) ⟨772584, by rfl⟩ : syracuseStep 2060225 = 1545169) B1545169
theorem B913387 : Blo 810345 913387 := bstep (se 1 (by rfl) ⟨685040, by rfl⟩ : syracuseStep 913387 = 1370081) B1370081
theorem B1830923 : Blo 810345 1830923 := bstep (se 1 (by rfl) ⟨1373192, by rfl⟩ : syracuseStep 1830923 = 2746385) B2746385
theorem B1830977 : Blo 810345 1830977 := bstep (se 2 (by rfl) ⟨686616, by rfl⟩ : syracuseStep 1830977 = 1373233) B1373233
theorem B913495 : Blo 810345 913495 := bstep (se 1 (by rfl) ⟨685121, by rfl⟩ : syracuseStep 913495 = 1370243) B1370243
theorem B5009501 : Blo 810345 5009501 := bstep (se 3 (by rfl) ⟨939281, by rfl⟩ : syracuseStep 5009501 = 1878563) B1878563
theorem B4944023 : Blo 810345 4944023 := bstep (se 1 (by rfl) ⟨3708017, by rfl⟩ : syracuseStep 4944023 = 7416035) B7416035
theorem B913675 : Blo 810345 913675 := bstep (se 1 (by rfl) ⟨685256, by rfl⟩ : syracuseStep 913675 = 1370513) B1370513
theorem B1831193 : Blo 810345 1831193 := bstep (se 2 (by rfl) ⟨686697, by rfl⟩ : syracuseStep 1831193 = 1373395) B1373395
theorem B3699037 : Blo 810345 3699037 := bstep (se 3 (by rfl) ⟨693569, by rfl⟩ : syracuseStep 3699037 = 1387139) B1387139
theorem B3469661 : Blo 810345 3469661 := bstep (se 3 (by rfl) ⟨650561, by rfl⟩ : syracuseStep 3469661 = 1301123) B1301123
theorem B1831283 : Blo 810345 1831283 := bstep (se 1 (by rfl) ⟨1373462, by rfl⟩ : syracuseStep 1831283 = 2746925) B2746925
theorem B913783 : Blo 810345 913783 := bstep (se 1 (by rfl) ⟨685337, by rfl⟩ : syracuseStep 913783 = 1370675) B1370675
theorem B1831319 : Blo 810345 1831319 := bstep (se 1 (by rfl) ⟨1373489, by rfl⟩ : syracuseStep 1831319 = 2746979) B2746979
theorem B1372619 : Blo 810345 1372619 := bstep (se 1 (by rfl) ⟨1029464, by rfl⟩ : syracuseStep 1372619 = 2058929) B2058929
theorem B2060761 : Blo 810345 2060761 := bstep (se 2 (by rfl) ⟨772785, by rfl⟩ : syracuseStep 2060761 = 1545571) B1545571
theorem B913963 : Blo 810345 913963 := bstep (se 1 (by rfl) ⟨685472, by rfl⟩ : syracuseStep 913963 = 1370945) B1370945
theorem B1372747 : Blo 810345 1372747 := bstep (se 1 (by rfl) ⟨1029560, by rfl⟩ : syracuseStep 1372747 = 2059121) B2059121
theorem B1831499 : Blo 810345 1831499 := bstep (se 1 (by rfl) ⟨1373624, by rfl⟩ : syracuseStep 1831499 = 2747249) B2747249
theorem B1831553 : Blo 810345 1831553 := bstep (se 2 (by rfl) ⟨686832, by rfl⟩ : syracuseStep 1831553 = 1373665) B1373665
theorem B914071 : Blo 810345 914071 := bstep (se 1 (by rfl) ⟨685553, by rfl⟩ : syracuseStep 914071 = 1371107) B1371107
theorem B1372889 : Blo 810345 1372889 := bstep (se 2 (by rfl) ⟨514833, by rfl⟩ : syracuseStep 1372889 = 1029667) B1029667
theorem B6255425 : Blo 810345 6255425 := bstep (se 2 (by rfl) ⟨2345784, by rfl⟩ : syracuseStep 6255425 = 4691569) B4691569
theorem B914251 : Blo 810345 914251 := bstep (se 1 (by rfl) ⟨685688, by rfl⟩ : syracuseStep 914251 = 1371377) B1371377
theorem B1373017 : Blo 810345 1373017 := bstep (se 2 (by rfl) ⟨514881, by rfl⟩ : syracuseStep 1373017 = 1029763) B1029763
theorem B1831769 : Blo 810345 1831769 := bstep (se 2 (by rfl) ⟨686913, by rfl⟩ : syracuseStep 1831769 = 1373827) B1373827
theorem B6943589 : Blo 810345 6943589 := bstep (se 4 (by rfl) ⟨650961, by rfl⟩ : syracuseStep 6943589 = 1301923) B1301923
theorem B1831859 : Blo 810345 1831859 := bstep (se 1 (by rfl) ⟨1373894, by rfl⟩ : syracuseStep 1831859 = 2747789) B2747789
theorem B914359 : Blo 810345 914359 := bstep (se 1 (by rfl) ⟨685769, by rfl⟩ : syracuseStep 914359 = 1371539) B1371539
theorem B1831895 : Blo 810345 1831895 := bstep (se 1 (by rfl) ⟨1373921, by rfl⟩ : syracuseStep 1831895 = 2747843) B2747843
theorem B3470359 : Blo 810345 3470359 := bstep (se 1 (by rfl) ⟨2602769, by rfl⟩ : syracuseStep 3470359 = 5205539) B5205539
theorem B914539 : Blo 810345 914539 := bstep (se 1 (by rfl) ⟨685904, by rfl⟩ : syracuseStep 914539 = 1371809) B1371809
theorem B1832075 : Blo 810345 1832075 := bstep (se 1 (by rfl) ⟨1374056, by rfl⟩ : syracuseStep 1832075 = 2748113) B2748113
theorem B4617395 : Blo 810345 4617395 := bstep (se 1 (by rfl) ⟨3463046, by rfl⟩ : syracuseStep 4617395 = 6926093) B6926093
theorem B1832129 : Blo 810345 1832129 := bstep (se 2 (by rfl) ⟨687048, by rfl⟩ : syracuseStep 1832129 = 1374097) B1374097
theorem B1602775 : Blo 810345 1602775 := bstep (se 1 (by rfl) ⟨1202081, by rfl⟩ : syracuseStep 1602775 = 2404163) B2404163
theorem B914647 : Blo 810345 914647 := bstep (se 1 (by rfl) ⟨685985, by rfl⟩ : syracuseStep 914647 = 1371971) B1371971
theorem B1733899 : Blo 810345 1733899 := bstep (se 1 (by rfl) ⟨1300424, by rfl⟩ : syracuseStep 1733899 = 2600849) B2600849
theorem B914827 : Blo 810345 914827 := bstep (se 1 (by rfl) ⟨686120, by rfl⟩ : syracuseStep 914827 = 1372241) B1372241
theorem B1373591 : Blo 810345 1373591 := bstep (se 1 (by rfl) ⟨1030193, by rfl⟩ : syracuseStep 1373591 = 2060387) B2060387
theorem B914935 : Blo 810345 914935 := bstep (se 1 (by rfl) ⟨686201, by rfl⟩ : syracuseStep 914935 = 1372403) B1372403
theorem B1373719 : Blo 810345 1373719 := bstep (se 1 (by rfl) ⟨1030289, by rfl⟩ : syracuseStep 1373719 = 2060579) B2060579
theorem B3077777 : Blo 810345 3077777 := bstep (se 2 (by rfl) ⟨1154166, by rfl⟩ : syracuseStep 3077777 = 2308333) B2308333
theorem B915115 : Blo 810345 915115 := bstep (se 1 (by rfl) ⟨686336, by rfl⟩ : syracuseStep 915115 = 1372673) B1372673
theorem B7534259 : Blo 810345 7534259 := bstep (se 1 (by rfl) ⟨5650694, by rfl⟩ : syracuseStep 7534259 = 11301389) B11301389
theorem B915223 : Blo 810345 915223 := bstep (se 1 (by rfl) ⟨686417, by rfl⟩ : syracuseStep 915223 = 1372835) B1372835
theorem B915403 : Blo 810345 915403 := bstep (se 1 (by rfl) ⟨686552, by rfl⟩ : syracuseStep 915403 = 1373105) B1373105
theorem B3897389 : Blo 810345 3897389 := bstep (se 3 (by rfl) ⟨730760, by rfl⟩ : syracuseStep 3897389 = 1461521) B1461521
theorem B915511 : Blo 810345 915511 := bstep (se 1 (by rfl) ⟨686633, by rfl⟩ : syracuseStep 915511 = 1373267) B1373267
theorem B22181957 : Blo 810345 22181957 := bstep (se 4 (by rfl) ⟨2079558, by rfl⟩ : syracuseStep 22181957 = 4159117) B4159117
theorem B3078233 : Blo 810345 3078233 := bstep (se 2 (by rfl) ⟨1154337, by rfl⟩ : syracuseStep 3078233 = 2308675) B2308675
theorem B3700829 : Blo 810345 3700829 := bstep (se 3 (by rfl) ⟨693905, by rfl⟩ : syracuseStep 3700829 = 1387811) B1387811
theorem B915691 : Blo 810345 915691 := bstep (se 1 (by rfl) ⟨686768, by rfl⟩ : syracuseStep 915691 = 1373537) B1373537
theorem B3078445 : Blo 810345 3078445 := bstep (se 3 (by rfl) ⟨577208, by rfl⟩ : syracuseStep 3078445 = 1154417) B1154417
theorem B915799 : Blo 810345 915799 := bstep (se 1 (by rfl) ⟨686849, by rfl⟩ : syracuseStep 915799 = 1373699) B1373699
theorem B3471761 : Blo 810345 3471761 := bstep (se 2 (by rfl) ⟨1301910, by rfl⟩ : syracuseStep 3471761 = 2603821) B2603821
theorem B915979 : Blo 810345 915979 := bstep (se 1 (by rfl) ⟨686984, by rfl⟩ : syracuseStep 915979 = 1373969) B1373969
theorem B1538585 : Blo 810345 1538585 := bstep (se 2 (by rfl) ⟨576969, by rfl⟩ : syracuseStep 1538585 = 1153939) B1153939
theorem B3078749 : Blo 810345 3078749 := bstep (se 3 (by rfl) ⟨577265, by rfl⟩ : syracuseStep 3078749 = 1154531) B1154531
theorem B4618853 : Blo 810345 4618853 := bstep (se 4 (by rfl) ⟨433017, by rfl⟩ : syracuseStep 4618853 = 866035) B866035
theorem B1735283 : Blo 810345 1735283 := bstep (se 1 (by rfl) ⟨1301462, by rfl⟩ : syracuseStep 1735283 = 2602925) B2602925
theorem B916087 : Blo 810345 916087 := bstep (se 1 (by rfl) ⟨687065, by rfl⟩ : syracuseStep 916087 = 1374131) B1374131
theorem B1538995 : Blo 810345 1538995 := bstep (se 1 (by rfl) ⟨1154246, by rfl⟩ : syracuseStep 1538995 = 2308493) B2308493
theorem B4619537 : Blo 810345 4619537 := bstep (se 2 (by rfl) ⟨1732326, by rfl⟩ : syracuseStep 4619537 = 3464653) B3464653
theorem B1539481 : Blo 810345 1539481 := bstep (se 2 (by rfl) ⟨577305, by rfl⟩ : syracuseStep 1539481 = 1154611) B1154611
theorem B1736129 : Blo 810345 1736129 := bstep (se 2 (by rfl) ⟨651048, by rfl⟩ : syracuseStep 1736129 = 1302097) B1302097
theorem B7044569 : Blo 810345 7044569 := bstep (se 2 (by rfl) ⟨2641713, by rfl⟩ : syracuseStep 7044569 = 5283427) B5283427
theorem B6160049 : Blo 810345 6160049 := bstep (se 2 (by rfl) ⟨2310018, by rfl⟩ : syracuseStep 6160049 = 4620037) B4620037
theorem B1408727 : Blo 810345 1408727 := bstep (se 1 (by rfl) ⟨1056545, by rfl⟩ : syracuseStep 1408727 = 2113091) B2113091
theorem B1736471 : Blo 810345 1736471 := bstep (se 1 (by rfl) ⟨1302353, by rfl⟩ : syracuseStep 1736471 = 2604707) B2604707
theorem B2785117 : Blo 810345 2785117 := bstep (se 3 (by rfl) ⟨522209, by rfl⟩ : syracuseStep 2785117 = 1044419) B1044419
theorem B1540043 : Blo 810345 1540043 := bstep (se 1 (by rfl) ⟨1155032, by rfl⟩ : syracuseStep 1540043 = 2310065) B2310065
theorem B4620311 : Blo 810345 4620311 := bstep (se 1 (by rfl) ⟨3465233, by rfl⟩ : syracuseStep 4620311 = 6930467) B6930467
theorem B5210513 : Blo 810345 5210513 := bstep (se 2 (by rfl) ⟨1953942, by rfl⟩ : syracuseStep 5210513 = 3907885) B3907885
theorem B4161995 : Blo 810345 4161995 := bstep (se 1 (by rfl) ⟨3121496, by rfl⟩ : syracuseStep 4161995 = 6242993) B6242993
theorem B3899927 : Blo 810345 3899927 := bstep (se 1 (by rfl) ⟨2924945, by rfl⟩ : syracuseStep 3899927 = 5849891) B5849891
theorem B2196001 : Blo 810345 2196001 := bstep (se 2 (by rfl) ⟨823500, by rfl⟩ : syracuseStep 2196001 = 1647001) B1647001
theorem B3474323 : Blo 810345 3474323 := bstep (se 1 (by rfl) ⟨2605742, by rfl⟩ : syracuseStep 3474323 = 5211485) B5211485
theorem B8258507 : Blo 810345 8258507 := bstep (se 1 (by rfl) ⟨6193880, by rfl⟩ : syracuseStep 8258507 = 12387761) B12387761
theorem B2196779 : Blo 810345 2196779 := bstep (se 1 (by rfl) ⟨1647584, by rfl⟩ : syracuseStep 2196779 = 3295169) B3295169
theorem B5211539 : Blo 810345 5211539 := bstep (se 1 (by rfl) ⟨3908654, by rfl⟩ : syracuseStep 5211539 = 7817309) B7817309
theorem B1738255 : Blo 810345 1738255 := bstep (se 1 (by rfl) ⟨1303691, by rfl⟩ : syracuseStep 1738255 = 2607383) B2607383
theorem B1738273 : Blo 810345 1738273 := bstep (se 2 (by rfl) ⟨651852, by rfl⟩ : syracuseStep 1738273 = 1303705) B1303705
theorem B3081847 : Blo 810345 3081847 := bstep (se 1 (by rfl) ⟨2311385, by rfl⟩ : syracuseStep 3081847 = 4622771) B4622771
theorem B1541767 : Blo 810345 1541767 := bstep (se 1 (by rfl) ⟨1156325, by rfl⟩ : syracuseStep 1541767 = 2312651) B2312651
theorem B19728197 : Blo 810345 19728197 := bstep (se 4 (by rfl) ⟨1849518, by rfl⟩ : syracuseStep 19728197 = 3699037) B3699037
theorem B1738631 : Blo 810345 1738631 := bstep (se 1 (by rfl) ⟨1303973, by rfl⟩ : syracuseStep 1738631 = 2607947) B2607947
theorem B7800893 : Blo 810345 7800893 := bstep (se 3 (by rfl) ⟨1462667, by rfl⟩ : syracuseStep 7800893 = 2925335) B2925335
theorem B16681133 : Blo 810345 16681133 := bstep (se 3 (by rfl) ⟨3127712, by rfl⟩ : syracuseStep 16681133 = 6255425) B6255425
theorem B7801235 : Blo 810345 7801235 := bstep (se 1 (by rfl) ⟨5850926, by rfl⟩ : syracuseStep 7801235 = 11701853) B11701853
theorem B9275795 : Blo 810345 9275795 := bstep (se 1 (by rfl) ⟨6956846, by rfl⟩ : syracuseStep 9275795 = 13913693) B13913693
theorem B3082819 : Blo 810345 3082819 := bstep (se 1 (by rfl) ⟨2312114, by rfl⟩ : syracuseStep 3082819 = 4624229) B4624229
theorem B19303093 : Blo 810345 19303093 := bstep (se 5 (by rfl) ⟨904832, by rfl⟩ : syracuseStep 19303093 = 1809665) B1809665
theorem B11700929 : Blo 810345 11700929 := bstep (se 2 (by rfl) ⟨4387848, by rfl⟩ : syracuseStep 11700929 = 8775697) B8775697
theorem B7506703 : Blo 810345 7506703 := bstep (se 1 (by rfl) ⟨5630027, by rfl⟩ : syracuseStep 7506703 = 11260055) B11260055
theorem B9898841 : Blo 810345 9898841 := bstep (se 2 (by rfl) ⟨3712065, by rfl⟩ : syracuseStep 9898841 = 7424131) B7424131
theorem B3083123 : Blo 810345 3083123 := bstep (se 1 (by rfl) ⟨2312342, by rfl⟩ : syracuseStep 3083123 = 4624685) B4624685
theorem B1215545 : Blo 810345 1215545 := bstep (se 2 (by rfl) ⟨455829, by rfl⟩ : syracuseStep 1215545 = 911659) B911659
theorem B4623479 : Blo 810345 4623479 := bstep (se 1 (by rfl) ⟨3467609, by rfl⟩ : syracuseStep 4623479 = 6935219) B6935219
theorem B1215623 : Blo 810345 1215623 := bstep (se 1 (by rfl) ⟨911717, by rfl⟩ : syracuseStep 1215623 = 1823435) B1823435
theorem B1215659 : Blo 810345 1215659 := bstep (se 1 (by rfl) ⟨911744, by rfl⟩ : syracuseStep 1215659 = 1823489) B1823489
theorem B1215689 : Blo 810345 1215689 := bstep (se 2 (by rfl) ⟨455883, by rfl⟩ : syracuseStep 1215689 = 911767) B911767
theorem B1543369 : Blo 810345 1543369 := bstep (se 2 (by rfl) ⟨578763, by rfl⟩ : syracuseStep 1543369 = 1157527) B1157527
theorem B1215803 : Blo 810345 1215803 := bstep (se 1 (by rfl) ⟨911852, by rfl⟩ : syracuseStep 1215803 = 1823705) B1823705
theorem B3083579 : Blo 810345 3083579 := bstep (se 1 (by rfl) ⟨2312684, by rfl⟩ : syracuseStep 3083579 = 4625369) B4625369
theorem B1215863 : Blo 810345 1215863 := bstep (se 1 (by rfl) ⟨911897, by rfl⟩ : syracuseStep 1215863 = 1823795) B1823795
theorem B1215887 : Blo 810345 1215887 := bstep (se 1 (by rfl) ⟨911915, by rfl⟩ : syracuseStep 1215887 = 1823831) B1823831
theorem B1215929 : Blo 810345 1215929 := bstep (se 2 (by rfl) ⟨455973, by rfl⟩ : syracuseStep 1215929 = 911947) B911947
theorem B1216007 : Blo 810345 1216007 := bstep (se 1 (by rfl) ⟨912005, by rfl⟩ : syracuseStep 1216007 = 1824011) B1824011
theorem B5017099 : Blo 810345 5017099 := bstep (se 1 (by rfl) ⟨3762824, by rfl⟩ : syracuseStep 5017099 = 7525649) B7525649
theorem B1216043 : Blo 810345 1216043 := bstep (se 1 (by rfl) ⟨912032, by rfl⟩ : syracuseStep 1216043 = 1824065) B1824065
theorem B1216073 : Blo 810345 1216073 := bstep (se 2 (by rfl) ⟨456027, by rfl⟩ : syracuseStep 1216073 = 912055) B912055
theorem B8326775 : Blo 810345 8326775 := bstep (se 1 (by rfl) ⟨6245081, by rfl⟩ : syracuseStep 8326775 = 12490163) B12490163
theorem B1216187 : Blo 810345 1216187 := bstep (se 1 (by rfl) ⟨912140, by rfl⟩ : syracuseStep 1216187 = 1824281) B1824281
theorem B1216247 : Blo 810345 1216247 := bstep (se 1 (by rfl) ⟨912185, by rfl⟩ : syracuseStep 1216247 = 1824371) B1824371
theorem B1216271 : Blo 810345 1216271 := bstep (se 1 (by rfl) ⟨912203, by rfl⟩ : syracuseStep 1216271 = 1824407) B1824407
theorem B3084065 : Blo 810345 3084065 := bstep (se 2 (by rfl) ⟨1156524, by rfl⟩ : syracuseStep 3084065 = 2313049) B2313049
theorem B5279525 : Blo 810345 5279525 := bstep (se 4 (by rfl) ⟨494955, by rfl⟩ : syracuseStep 5279525 = 989911) B989911
theorem B1216313 : Blo 810345 1216313 := bstep (se 2 (by rfl) ⟨456117, by rfl⟩ : syracuseStep 1216313 = 912235) B912235
theorem B240422741 : Blo 810345 240422741 := bstep (se 9 (by rfl) ⟨704363, by rfl⟩ : syracuseStep 240422741 = 1408727) B1408727
theorem B1216391 : Blo 810345 1216391 := bstep (se 1 (by rfl) ⟨912293, by rfl⟩ : syracuseStep 1216391 = 1824587) B1824587
theorem B3903385 : Blo 810345 3903385 := bstep (se 2 (by rfl) ⟨1463769, by rfl⟩ : syracuseStep 3903385 = 2927539) B2927539
theorem B1216427 : Blo 810345 1216427 := bstep (se 1 (by rfl) ⟨912320, by rfl⟩ : syracuseStep 1216427 = 1824641) B1824641
theorem B1216457 : Blo 810345 1216457 := bstep (se 2 (by rfl) ⟨456171, by rfl⟩ : syracuseStep 1216457 = 912343) B912343
theorem B1216571 : Blo 810345 1216571 := bstep (se 1 (by rfl) ⟨912428, by rfl⟩ : syracuseStep 1216571 = 1824857) B1824857
theorem B1216631 : Blo 810345 1216631 := bstep (se 1 (by rfl) ⟨912473, by rfl⟩ : syracuseStep 1216631 = 1824947) B1824947
theorem B1216655 : Blo 810345 1216655 := bstep (se 1 (by rfl) ⟨912491, by rfl⟩ : syracuseStep 1216655 = 1824983) B1824983
theorem B1216697 : Blo 810345 1216697 := bstep (se 2 (by rfl) ⟨456261, by rfl⟩ : syracuseStep 1216697 = 912523) B912523
theorem B1216775 : Blo 810345 1216775 := bstep (se 1 (by rfl) ⟨912581, by rfl⟩ : syracuseStep 1216775 = 1825163) B1825163
theorem B3477775 : Blo 810345 3477775 := bstep (se 1 (by rfl) ⟨2608331, by rfl⟩ : syracuseStep 3477775 = 5216663) B5216663
theorem B1216811 : Blo 810345 1216811 := bstep (se 1 (by rfl) ⟨912608, by rfl⟩ : syracuseStep 1216811 = 1825217) B1825217
theorem B1216841 : Blo 810345 1216841 := bstep (se 2 (by rfl) ⟨456315, by rfl⟩ : syracuseStep 1216841 = 912631) B912631
theorem B1216955 : Blo 810345 1216955 := bstep (se 1 (by rfl) ⟨912716, by rfl⟩ : syracuseStep 1216955 = 1825433) B1825433
theorem B1217015 : Blo 810345 1217015 := bstep (se 1 (by rfl) ⟨912761, by rfl⟩ : syracuseStep 1217015 = 1825523) B1825523
theorem B1217039 : Blo 810345 1217039 := bstep (se 1 (by rfl) ⟨912779, by rfl⟩ : syracuseStep 1217039 = 1825559) B1825559
theorem B4166167 : Blo 810345 4166167 := bstep (se 1 (by rfl) ⟨3124625, by rfl⟩ : syracuseStep 4166167 = 6249251) B6249251
theorem B1217081 : Blo 810345 1217081 := bstep (se 2 (by rfl) ⟨456405, by rfl⟩ : syracuseStep 1217081 = 912811) B912811
theorem B1217159 : Blo 810345 1217159 := bstep (se 1 (by rfl) ⟨912869, by rfl⟩ : syracuseStep 1217159 = 1825739) B1825739
theorem B1217195 : Blo 810345 1217195 := bstep (se 1 (by rfl) ⟨912896, by rfl⟩ : syracuseStep 1217195 = 1825793) B1825793
theorem B1217225 : Blo 810345 1217225 := bstep (se 2 (by rfl) ⟨456459, by rfl⟩ : syracuseStep 1217225 = 912919) B912919
theorem B6951653 : Blo 810345 6951653 := bstep (se 4 (by rfl) ⟨651717, by rfl⟩ : syracuseStep 6951653 = 1303435) B1303435
theorem B2921197 : Blo 810345 2921197 := bstep (se 3 (by rfl) ⟨547724, by rfl⟩ : syracuseStep 2921197 = 1095449) B1095449
theorem B3085037 : Blo 810345 3085037 := bstep (se 3 (by rfl) ⟨578444, by rfl⟩ : syracuseStep 3085037 = 1156889) B1156889
theorem B4395809 : Blo 810345 4395809 := bstep (se 2 (by rfl) ⟨1648428, by rfl⟩ : syracuseStep 4395809 = 3296857) B3296857
theorem B1217339 : Blo 810345 1217339 := bstep (se 1 (by rfl) ⟨913004, by rfl⟩ : syracuseStep 1217339 = 1826009) B1826009
theorem B1217399 : Blo 810345 1217399 := bstep (se 1 (by rfl) ⟨913049, by rfl⟩ : syracuseStep 1217399 = 1826099) B1826099
theorem B1217423 : Blo 810345 1217423 := bstep (se 1 (by rfl) ⟨913067, by rfl⟩ : syracuseStep 1217423 = 1826135) B1826135
theorem B8328089 : Blo 810345 8328089 := bstep (se 2 (by rfl) ⟨3123033, by rfl⟩ : syracuseStep 8328089 = 6246067) B6246067
theorem B14062517 : Blo 810345 14062517 := bstep (se 5 (by rfl) ⟨659180, by rfl⟩ : syracuseStep 14062517 = 1318361) B1318361
theorem B1217465 : Blo 810345 1217465 := bstep (se 2 (by rfl) ⟨456549, by rfl⟩ : syracuseStep 1217465 = 913099) B913099
theorem B4395961 : Blo 810345 4395961 := bstep (se 2 (by rfl) ⟨1648485, by rfl⟩ : syracuseStep 4395961 = 3296971) B3296971
theorem B1217543 : Blo 810345 1217543 := bstep (se 1 (by rfl) ⟨913157, by rfl⟩ : syracuseStep 1217543 = 1826315) B1826315
theorem B1217579 : Blo 810345 1217579 := bstep (se 1 (by rfl) ⟨913184, by rfl⟩ : syracuseStep 1217579 = 1826369) B1826369
theorem B1217609 : Blo 810345 1217609 := bstep (se 2 (by rfl) ⟨456603, by rfl⟩ : syracuseStep 1217609 = 913207) B913207
theorem B1217723 : Blo 810345 1217723 := bstep (se 1 (by rfl) ⟨913292, by rfl⟩ : syracuseStep 1217723 = 1826585) B1826585
theorem B1217783 : Blo 810345 1217783 := bstep (se 1 (by rfl) ⟨913337, by rfl⟩ : syracuseStep 1217783 = 1826675) B1826675
theorem B1217807 : Blo 810345 1217807 := bstep (se 1 (by rfl) ⟨913355, by rfl⟩ : syracuseStep 1217807 = 1826711) B1826711
theorem B1217849 : Blo 810345 1217849 := bstep (se 2 (by rfl) ⟨456693, by rfl⟩ : syracuseStep 1217849 = 913387) B913387
theorem B1217927 : Blo 810345 1217927 := bstep (se 1 (by rfl) ⟨913445, by rfl⟩ : syracuseStep 1217927 = 1826891) B1826891
theorem B6952337 : Blo 810345 6952337 := bstep (se 2 (by rfl) ⟨2607126, by rfl⟩ : syracuseStep 6952337 = 5214253) B5214253
theorem B3085721 : Blo 810345 3085721 := bstep (se 2 (by rfl) ⟨1157145, by rfl⟩ : syracuseStep 3085721 = 2314291) B2314291
theorem B1217963 : Blo 810345 1217963 := bstep (se 1 (by rfl) ⟨913472, by rfl⟩ : syracuseStep 1217963 = 1826945) B1826945
theorem B1217993 : Blo 810345 1217993 := bstep (se 2 (by rfl) ⟨456747, by rfl⟩ : syracuseStep 1217993 = 913495) B913495
theorem B1218107 : Blo 810345 1218107 := bstep (se 1 (by rfl) ⟨913580, by rfl⟩ : syracuseStep 1218107 = 1827161) B1827161
theorem B1218167 : Blo 810345 1218167 := bstep (se 1 (by rfl) ⟨913625, by rfl⟩ : syracuseStep 1218167 = 1827251) B1827251
theorem B1218191 : Blo 810345 1218191 := bstep (se 1 (by rfl) ⟨913643, by rfl⟩ : syracuseStep 1218191 = 1827287) B1827287
theorem B1545875 : Blo 810345 1545875 := bstep (se 1 (by rfl) ⟨1159406, by rfl⟩ : syracuseStep 1545875 = 2318813) B2318813
theorem B1218233 : Blo 810345 1218233 := bstep (se 2 (by rfl) ⟨456837, by rfl⟩ : syracuseStep 1218233 = 913675) B913675
theorem B1218311 : Blo 810345 1218311 := bstep (se 1 (by rfl) ⟨913733, by rfl⟩ : syracuseStep 1218311 = 1827467) B1827467
theorem B2004751 : Blo 810345 2004751 := bstep (se 1 (by rfl) ⟨1503563, by rfl⟩ : syracuseStep 2004751 = 3007127) B3007127
theorem B1218347 : Blo 810345 1218347 := bstep (se 1 (by rfl) ⟨913760, by rfl⟩ : syracuseStep 1218347 = 1827521) B1827521
theorem B1218377 : Blo 810345 1218377 := bstep (se 2 (by rfl) ⟨456891, by rfl⟩ : syracuseStep 1218377 = 913783) B913783
theorem B1218491 : Blo 810345 1218491 := bstep (se 1 (by rfl) ⟨913868, by rfl⟩ : syracuseStep 1218491 = 1827737) B1827737
theorem B1218551 : Blo 810345 1218551 := bstep (se 1 (by rfl) ⟨913913, by rfl⟩ : syracuseStep 1218551 = 1827827) B1827827
theorem B1218575 : Blo 810345 1218575 := bstep (se 1 (by rfl) ⟨913931, by rfl⟩ : syracuseStep 1218575 = 1827863) B1827863
theorem B1218617 : Blo 810345 1218617 := bstep (se 2 (by rfl) ⟨456981, by rfl⟩ : syracuseStep 1218617 = 913963) B913963
theorem B1218695 : Blo 810345 1218695 := bstep (se 1 (by rfl) ⟨914021, by rfl⟩ : syracuseStep 1218695 = 1828043) B1828043
theorem B1218731 : Blo 810345 1218731 := bstep (se 1 (by rfl) ⟨914048, by rfl⟩ : syracuseStep 1218731 = 1828097) B1828097
theorem B1218761 : Blo 810345 1218761 := bstep (se 2 (by rfl) ⟨457035, by rfl⟩ : syracuseStep 1218761 = 914071) B914071
theorem B1218875 : Blo 810345 1218875 := bstep (se 1 (by rfl) ⟨914156, by rfl⟩ : syracuseStep 1218875 = 1828313) B1828313
theorem B3086707 : Blo 810345 3086707 := bstep (se 1 (by rfl) ⟨2315030, by rfl⟩ : syracuseStep 3086707 = 4630061) B4630061
theorem B1218935 : Blo 810345 1218935 := bstep (se 1 (by rfl) ⟨914201, by rfl⟩ : syracuseStep 1218935 = 1828403) B1828403
theorem B1218959 : Blo 810345 1218959 := bstep (se 1 (by rfl) ⟨914219, by rfl⟩ : syracuseStep 1218959 = 1828439) B1828439
theorem B6953363 : Blo 810345 6953363 := bstep (se 1 (by rfl) ⟨5215022, by rfl⟩ : syracuseStep 6953363 = 10430045) B10430045
theorem B1219001 : Blo 810345 1219001 := bstep (se 2 (by rfl) ⟨457125, by rfl⟩ : syracuseStep 1219001 = 914251) B914251
theorem B1219079 : Blo 810345 1219079 := bstep (se 1 (by rfl) ⟨914309, by rfl⟩ : syracuseStep 1219079 = 1828619) B1828619
theorem B1251883 : Blo 810345 1251883 := bstep (se 1 (by rfl) ⟨938912, by rfl⟩ : syracuseStep 1251883 = 1877825) B1877825
theorem B1219115 : Blo 810345 1219115 := bstep (se 1 (by rfl) ⟨914336, by rfl⟩ : syracuseStep 1219115 = 1828673) B1828673
theorem B1219145 : Blo 810345 1219145 := bstep (se 2 (by rfl) ⟨457179, by rfl⟩ : syracuseStep 1219145 = 914359) B914359
theorem B1219259 : Blo 810345 1219259 := bstep (se 1 (by rfl) ⟨914444, by rfl⟩ : syracuseStep 1219259 = 1828889) B1828889
theorem B4627145 : Blo 810345 4627145 := bstep (se 2 (by rfl) ⟨1735179, by rfl⟩ : syracuseStep 4627145 = 3470359) B3470359
theorem B1219319 : Blo 810345 1219319 := bstep (se 1 (by rfl) ⟨914489, by rfl⟩ : syracuseStep 1219319 = 1828979) B1828979
theorem B924431 : Blo 810345 924431 := bstep (se 1 (by rfl) ⟨693323, by rfl⟩ : syracuseStep 924431 = 1386647) B1386647
theorem B1219343 : Blo 810345 1219343 := bstep (se 1 (by rfl) ⟨914507, by rfl⟩ : syracuseStep 1219343 = 1829015) B1829015
theorem B1219385 : Blo 810345 1219385 := bstep (se 2 (by rfl) ⟨457269, by rfl⟩ : syracuseStep 1219385 = 914539) B914539
theorem B1153865 : Blo 810345 1153865 := bstep (se 2 (by rfl) ⟨432699, by rfl⟩ : syracuseStep 1153865 = 865399) B865399
theorem B1219463 : Blo 810345 1219463 := bstep (se 1 (by rfl) ⟨914597, by rfl⟩ : syracuseStep 1219463 = 1829195) B1829195
theorem B1219499 : Blo 810345 1219499 := bstep (se 1 (by rfl) ⟨914624, by rfl⟩ : syracuseStep 1219499 = 1829249) B1829249
theorem B2137033 : Blo 810345 2137033 := bstep (se 2 (by rfl) ⟨801387, by rfl⟩ : syracuseStep 2137033 = 1602775) B1602775
theorem B1219529 : Blo 810345 1219529 := bstep (se 2 (by rfl) ⟨457323, by rfl⟩ : syracuseStep 1219529 = 914647) B914647
theorem B1219643 : Blo 810345 1219643 := bstep (se 1 (by rfl) ⟨914732, by rfl⟩ : syracuseStep 1219643 = 1829465) B1829465
theorem B1219703 : Blo 810345 1219703 := bstep (se 1 (by rfl) ⟨914777, by rfl⟩ : syracuseStep 1219703 = 1829555) B1829555
theorem B1219727 : Blo 810345 1219727 := bstep (se 1 (by rfl) ⟨914795, by rfl⟩ : syracuseStep 1219727 = 1829591) B1829591
theorem B1219769 : Blo 810345 1219769 := bstep (se 2 (by rfl) ⟨457413, by rfl⟩ : syracuseStep 1219769 = 914827) B914827
theorem B1219847 : Blo 810345 1219847 := bstep (se 1 (by rfl) ⟨914885, by rfl⟩ : syracuseStep 1219847 = 1829771) B1829771
theorem B1219883 : Blo 810345 1219883 := bstep (se 1 (by rfl) ⟨914912, by rfl⟩ : syracuseStep 1219883 = 1829825) B1829825
theorem B1219913 : Blo 810345 1219913 := bstep (se 2 (by rfl) ⟨457467, by rfl⟩ : syracuseStep 1219913 = 914935) B914935
theorem B9248093 : Blo 810345 9248093 := bstep (se 3 (by rfl) ⟨1734017, by rfl⟩ : syracuseStep 9248093 = 3468035) B3468035
theorem B990599 : Blo 810345 990599 := bstep (se 1 (by rfl) ⟨742949, by rfl⟩ : syracuseStep 990599 = 1485899) B1485899
theorem B1220027 : Blo 810345 1220027 := bstep (se 1 (by rfl) ⟨915020, by rfl⟩ : syracuseStep 1220027 = 1830041) B1830041
theorem B1220087 : Blo 810345 1220087 := bstep (se 1 (by rfl) ⟨915065, by rfl⟩ : syracuseStep 1220087 = 1830131) B1830131
theorem B1220111 : Blo 810345 1220111 := bstep (se 1 (by rfl) ⟨915083, by rfl⟩ : syracuseStep 1220111 = 1830167) B1830167
theorem B1220153 : Blo 810345 1220153 := bstep (se 2 (by rfl) ⟨457557, by rfl⟩ : syracuseStep 1220153 = 915115) B915115
theorem B1220231 : Blo 810345 1220231 := bstep (se 1 (by rfl) ⟨915173, by rfl⟩ : syracuseStep 1220231 = 1830347) B1830347
theorem B1220267 : Blo 810345 1220267 := bstep (se 1 (by rfl) ⟨915200, by rfl⟩ : syracuseStep 1220267 = 1830401) B1830401
theorem B1154731 : Blo 810345 1154731 := bstep (se 1 (by rfl) ⟨866048, by rfl⟩ : syracuseStep 1154731 = 1732097) B1732097
theorem B14786225 : Blo 810345 14786225 := bstep (se 2 (by rfl) ⟨5544834, by rfl⟩ : syracuseStep 14786225 = 11089669) B11089669
theorem B1220297 : Blo 810345 1220297 := bstep (se 2 (by rfl) ⟨457611, by rfl⟩ : syracuseStep 1220297 = 915223) B915223
theorem B1220411 : Blo 810345 1220411 := bstep (se 1 (by rfl) ⟨915308, by rfl⟩ : syracuseStep 1220411 = 1830617) B1830617
theorem B1220471 : Blo 810345 1220471 := bstep (se 1 (by rfl) ⟨915353, by rfl⟩ : syracuseStep 1220471 = 1830707) B1830707
theorem B1220495 : Blo 810345 1220495 := bstep (se 1 (by rfl) ⟨915371, by rfl⟩ : syracuseStep 1220495 = 1830743) B1830743
theorem B1220537 : Blo 810345 1220537 := bstep (se 2 (by rfl) ⟨457701, by rfl⟩ : syracuseStep 1220537 = 915403) B915403
theorem B1220615 : Blo 810345 1220615 := bstep (se 1 (by rfl) ⟨915461, by rfl⟩ : syracuseStep 1220615 = 1830923) B1830923
theorem B1220651 : Blo 810345 1220651 := bstep (se 1 (by rfl) ⟨915488, by rfl⟩ : syracuseStep 1220651 = 1830977) B1830977
theorem B9904189 : Blo 810345 9904189 := bstep (se 3 (by rfl) ⟨1857035, by rfl⟩ : syracuseStep 9904189 = 3714071) B3714071
theorem B1220681 : Blo 810345 1220681 := bstep (se 2 (by rfl) ⟨457755, by rfl⟩ : syracuseStep 1220681 = 915511) B915511
theorem B1220795 : Blo 810345 1220795 := bstep (se 1 (by rfl) ⟨915596, by rfl⟩ : syracuseStep 1220795 = 1831193) B1831193
theorem B1220855 : Blo 810345 1220855 := bstep (se 1 (by rfl) ⟨915641, by rfl⟩ : syracuseStep 1220855 = 1831283) B1831283
theorem B1220879 : Blo 810345 1220879 := bstep (se 1 (by rfl) ⟨915659, by rfl⟩ : syracuseStep 1220879 = 1831319) B1831319
theorem B1220921 : Blo 810345 1220921 := bstep (se 2 (by rfl) ⟨457845, by rfl⟩ : syracuseStep 1220921 = 915691) B915691
theorem B1220999 : Blo 810345 1220999 := bstep (se 1 (by rfl) ⟨915749, by rfl⟩ : syracuseStep 1220999 = 1831499) B1831499
theorem B4104593 : Blo 810345 4104593 := bstep (se 2 (by rfl) ⟨1539222, by rfl⟩ : syracuseStep 4104593 = 3078445) B3078445
theorem B1221035 : Blo 810345 1221035 := bstep (se 1 (by rfl) ⟨915776, by rfl⟩ : syracuseStep 1221035 = 1831553) B1831553
theorem B1221065 : Blo 810345 1221065 := bstep (se 2 (by rfl) ⟨457899, by rfl⟩ : syracuseStep 1221065 = 915799) B915799
theorem B3088925 : Blo 810345 3088925 := bstep (se 3 (by rfl) ⟨579173, by rfl⟩ : syracuseStep 3088925 = 1158347) B1158347
theorem B1221179 : Blo 810345 1221179 := bstep (se 1 (by rfl) ⟨915884, by rfl⟩ : syracuseStep 1221179 = 1831769) B1831769
theorem B4629059 : Blo 810345 4629059 := bstep (se 1 (by rfl) ⟨3471794, by rfl⟩ : syracuseStep 4629059 = 6943589) B6943589
theorem B1221239 : Blo 810345 1221239 := bstep (se 1 (by rfl) ⟨915929, by rfl⟩ : syracuseStep 1221239 = 1831859) B1831859
theorem B1221263 : Blo 810345 1221263 := bstep (se 1 (by rfl) ⟨915947, by rfl⟩ : syracuseStep 1221263 = 1831895) B1831895
theorem B1221305 : Blo 810345 1221305 := bstep (se 2 (by rfl) ⟨457989, by rfl⟩ : syracuseStep 1221305 = 915979) B915979
theorem B2597633 : Blo 810345 2597633 := bstep (se 2 (by rfl) ⟨974112, by rfl⟩ : syracuseStep 2597633 = 1948225) B1948225
theorem B1221383 : Blo 810345 1221383 := bstep (se 1 (by rfl) ⟨916037, by rfl⟩ : syracuseStep 1221383 = 1832075) B1832075
theorem B9249551 : Blo 810345 9249551 := bstep (se 1 (by rfl) ⟨6937163, by rfl⟩ : syracuseStep 9249551 = 13874327) B13874327
theorem B1221419 : Blo 810345 1221419 := bstep (se 1 (by rfl) ⟨916064, by rfl⟩ : syracuseStep 1221419 = 1832129) B1832129
theorem B1221449 : Blo 810345 1221449 := bstep (se 2 (by rfl) ⟨458043, by rfl⟩ : syracuseStep 1221449 = 916087) B916087
theorem B5022839 : Blo 810345 5022839 := bstep (se 1 (by rfl) ⟨3767129, by rfl⟩ : syracuseStep 5022839 = 7534259) B7534259
theorem B1156297 : Blo 810345 1156297 := bstep (se 2 (by rfl) ⟨433611, by rfl⟩ : syracuseStep 1156297 = 867223) B867223
theorem B3089609 : Blo 810345 3089609 := bstep (se 2 (by rfl) ⟨1158603, by rfl⟩ : syracuseStep 3089609 = 2317207) B2317207
theorem B2598259 : Blo 810345 2598259 := bstep (se 1 (by rfl) ⟨1948694, by rfl⟩ : syracuseStep 2598259 = 3897389) B3897389
theorem B14787971 : Blo 810345 14787971 := bstep (se 1 (by rfl) ⟨11090978, by rfl⟩ : syracuseStep 14787971 = 22181957) B22181957
theorem B2467219 : Blo 810345 2467219 := bstep (se 1 (by rfl) ⟨1850414, by rfl⟩ : syracuseStep 2467219 = 3700829) B3700829
theorem B4400651 : Blo 810345 4400651 := bstep (se 1 (by rfl) ⟨3300488, by rfl⟩ : syracuseStep 4400651 = 6600977) B6600977
theorem B1025723 : Blo 810345 1025723 := bstep (se 1 (by rfl) ⟨769292, by rfl⟩ : syracuseStep 1025723 = 1538585) B1538585
theorem B1156855 : Blo 810345 1156855 := bstep (se 1 (by rfl) ⟨867641, by rfl⟩ : syracuseStep 1156855 = 1735283) B1735283
theorem B26388341 : Blo 810345 26388341 := bstep (se 5 (by rfl) ⟨1236953, by rfl⟩ : syracuseStep 26388341 = 2473907) B2473907
theorem B1157419 : Blo 810345 1157419 := bstep (se 1 (by rfl) ⟨868064, by rfl⟩ : syracuseStep 1157419 = 1736129) B1736129
theorem B4696379 : Blo 810345 4696379 := bstep (se 1 (by rfl) ⟨3522284, by rfl⟩ : syracuseStep 4696379 = 7044569) B7044569
theorem B4106699 : Blo 810345 4106699 := bstep (se 1 (by rfl) ⟨3080024, by rfl⟩ : syracuseStep 4106699 = 6160049) B6160049
theorem B3713489 : Blo 810345 3713489 := bstep (se 2 (by rfl) ⟨1392558, by rfl⟩ : syracuseStep 3713489 = 2785117) B2785117
theorem B1157647 : Blo 810345 1157647 := bstep (se 1 (by rfl) ⟨868235, by rfl⟩ : syracuseStep 1157647 = 1736471) B1736471
theorem B1026695 : Blo 810345 1026695 := bstep (se 1 (by rfl) ⟨770021, by rfl⟩ : syracuseStep 1026695 = 1540043) B1540043
theorem B4107023 : Blo 810345 4107023 := bstep (se 1 (by rfl) ⟨3080267, by rfl⟩ : syracuseStep 4107023 = 6160535) B6160535
theorem B3910459 : Blo 810345 3910459 := bstep (se 1 (by rfl) ⟨2932844, by rfl⟩ : syracuseStep 3910459 = 5865689) B5865689
theorem B3091385 : Blo 810345 3091385 := bstep (se 2 (by rfl) ⟨1159269, by rfl⟩ : syracuseStep 3091385 = 2318539) B2318539
theorem B1027343 : Blo 810345 1027343 := bstep (se 1 (by rfl) ⟨770507, by rfl⟩ : syracuseStep 1027343 = 1541015) B1541015
theorem B14069177 : Blo 810345 14069177 := bstep (se 2 (by rfl) ⟨5275941, by rfl⟩ : syracuseStep 14069177 = 10551883) B10551883
theorem B6598097 : Blo 810345 6598097 := bstep (se 2 (by rfl) ⟨2474286, by rfl⟩ : syracuseStep 6598097 = 4948573) B4948573
theorem B1158791 : Blo 810345 1158791 := bstep (se 1 (by rfl) ⟨869093, by rfl⟩ : syracuseStep 1158791 = 1738187) B1738187
theorem B1158985 : Blo 810345 1158985 := bstep (se 2 (by rfl) ⟨434619, by rfl⟩ : syracuseStep 1158985 = 869239) B869239
theorem B4108481 : Blo 810345 4108481 := bstep (se 2 (by rfl) ⟨1540680, by rfl⟩ : syracuseStep 4108481 = 3081361) B3081361
theorem B17150221 : Blo 810345 17150221 := bstep (se 3 (by rfl) ⟨3215666, by rfl⟩ : syracuseStep 17150221 = 6431333) B6431333
theorem B4632977 : Blo 810345 4632977 := bstep (se 2 (by rfl) ⟨1737366, by rfl⟩ : syracuseStep 4632977 = 3474733) B3474733
theorem B17609177 : Blo 810345 17609177 := bstep (se 2 (by rfl) ⟨6603441, by rfl⟩ : syracuseStep 17609177 = 13206883) B13206883
theorem B2470429 : Blo 810345 2470429 := bstep (se 3 (by rfl) ⟨463205, by rfl⟩ : syracuseStep 2470429 = 926411) B926411
theorem B2929213 : Blo 810345 2929213 := bstep (se 3 (by rfl) ⟨549227, by rfl⟩ : syracuseStep 2929213 = 1098455) B1098455
theorem B8794817 : Blo 810345 8794817 := bstep (se 2 (by rfl) ⟨3298056, by rfl⟩ : syracuseStep 8794817 = 6596113) B6596113
theorem B6927119 : Blo 810345 6927119 := bstep (se 1 (by rfl) ⟨5195339, by rfl⟩ : syracuseStep 6927119 = 10390679) B10390679
theorem B4633433 : Blo 810345 4633433 := bstep (se 2 (by rfl) ⟨1737537, by rfl⟩ : syracuseStep 4633433 = 3475075) B3475075
theorem B2635193 : Blo 810345 2635193 := bstep (se 2 (by rfl) ⟨988197, by rfl⟩ : syracuseStep 2635193 = 1976395) B1976395
theorem B4109777 : Blo 810345 4109777 := bstep (se 2 (by rfl) ⟨1541166, by rfl⟩ : syracuseStep 4109777 = 3082333) B3082333
theorem B3127099 : Blo 810345 3127099 := bstep (se 1 (by rfl) ⟨2345324, by rfl⟩ : syracuseStep 3127099 = 4690649) B4690649
theorem B1947763 : Blo 810345 1947763 := bstep (se 1 (by rfl) ⟨1460822, by rfl⟩ : syracuseStep 1947763 = 2921645) B2921645
theorem B1030315 : Blo 810345 1030315 := bstep (se 1 (by rfl) ⟨772736, by rfl⟩ : syracuseStep 1030315 = 1545473) B1545473
theorem B2636047 : Blo 810345 2636047 := bstep (se 1 (by rfl) ⟨1977035, by rfl⟩ : syracuseStep 2636047 = 3954071) B3954071
theorem B2931059 : Blo 810345 2931059 := bstep (se 1 (by rfl) ⟨2198294, by rfl⟩ : syracuseStep 2931059 = 4396589) B4396589
theorem B2603411 : Blo 810345 2603411 := bstep (se 1 (by rfl) ⟨1952558, by rfl⟩ : syracuseStep 2603411 = 3905117) B3905117
theorem B2308925 : Blo 810345 2308925 := bstep (se 3 (by rfl) ⟨432923, by rfl⟩ : syracuseStep 2308925 = 865847) B865847
theorem B4996183 : Blo 810345 4996183 := bstep (se 1 (by rfl) ⟨3747137, by rfl⟩ : syracuseStep 4996183 = 7494275) B7494275
theorem B2473217 : Blo 810345 2473217 := bstep (se 2 (by rfl) ⟨927456, by rfl⟩ : syracuseStep 2473217 = 1854913) B1854913
theorem B2931983 : Blo 810345 2931983 := bstep (se 1 (by rfl) ⟨2198987, by rfl⟩ : syracuseStep 2931983 = 4397975) B4397975
theorem B4111883 : Blo 810345 4111883 := bstep (se 1 (by rfl) ⟨3083912, by rfl⟩ : syracuseStep 4111883 = 6167825) B6167825
theorem B2080289 : Blo 810345 2080289 := bstep (se 2 (by rfl) ⟨780108, by rfl⟩ : syracuseStep 2080289 = 1560217) B1560217
theorem B4112045 : Blo 810345 4112045 := bstep (se 3 (by rfl) ⟨771008, by rfl⟩ : syracuseStep 4112045 = 1542017) B1542017
theorem B2309917 : Blo 810345 2309917 := bstep (se 3 (by rfl) ⟨433109, by rfl⟩ : syracuseStep 2309917 = 866219) B866219
theorem B1949483 : Blo 810345 1949483 := bstep (se 1 (by rfl) ⟨1462112, by rfl⟩ : syracuseStep 1949483 = 2924225) B2924225
theorem B3293081 : Blo 810345 3293081 := bstep (se 2 (by rfl) ⟨1234905, by rfl⟩ : syracuseStep 3293081 = 2469811) B2469811
theorem B4636601 : Blo 810345 4636601 := bstep (se 2 (by rfl) ⟨1738725, by rfl⟩ : syracuseStep 4636601 = 3477451) B3477451
theorem B868487 : Blo 810345 868487 := bstep (se 1 (by rfl) ⟨651365, by rfl⟩ : syracuseStep 868487 = 1302731) B1302731
theorem B2474393 : Blo 810345 2474393 := bstep (se 2 (by rfl) ⟨927897, by rfl⟩ : syracuseStep 2474393 = 1855795) B1855795
theorem B2933177 : Blo 810345 2933177 := bstep (se 2 (by rfl) ⟨1099941, by rfl⟩ : syracuseStep 2933177 = 2199883) B2199883
theorem B1098299 : Blo 810345 1098299 := bstep (se 1 (by rfl) ⟨823724, by rfl⟩ : syracuseStep 1098299 = 1647449) B1647449
theorem B4997861 : Blo 810345 4997861 := bstep (se 4 (by rfl) ⟨468549, by rfl⟩ : syracuseStep 4997861 = 937099) B937099
theorem B869179 : Blo 810345 869179 := bstep (se 1 (by rfl) ⟨651884, by rfl⟩ : syracuseStep 869179 = 1303769) B1303769
theorem B2737043 : Blo 810345 2737043 := bstep (se 1 (by rfl) ⟨2052782, by rfl⟩ : syracuseStep 2737043 = 4105565) B4105565
theorem B1950617 : Blo 810345 1950617 := bstep (se 2 (by rfl) ⟨731481, by rfl⟩ : syracuseStep 1950617 = 1462963) B1462963
theorem B4113665 : Blo 810345 4113665 := bstep (se 2 (by rfl) ⟨1542624, by rfl⟩ : syracuseStep 4113665 = 3085249) B3085249
theorem B9258299 : Blo 810345 9258299 := bstep (se 1 (by rfl) ⟨6943724, by rfl⟩ : syracuseStep 9258299 = 13887449) B13887449
theorem B23447069 : Blo 810345 23447069 := bstep (se 3 (by rfl) ⟨4396325, by rfl⟩ : syracuseStep 23447069 = 8792651) B8792651
theorem B1951385 : Blo 810345 1951385 := bstep (se 2 (by rfl) ⟨731769, by rfl⟩ : syracuseStep 1951385 = 1463539) B1463539
theorem B2311865 : Blo 810345 2311865 := bstep (se 2 (by rfl) ⟨866949, by rfl⟩ : syracuseStep 2311865 = 1733899) B1733899
theorem B2344889 : Blo 810345 2344889 := bstep (se 2 (by rfl) ⟨879333, by rfl⟩ : syracuseStep 2344889 = 1758667) B1758667
theorem B4114475 : Blo 810345 4114475 := bstep (se 1 (by rfl) ⟨3085856, by rfl⟩ : syracuseStep 4114475 = 6171713) B6171713
theorem B2738447 : Blo 810345 2738447 := bstep (se 1 (by rfl) ⟨2053835, by rfl⟩ : syracuseStep 2738447 = 4107671) B4107671
theorem B2738717 : Blo 810345 2738717 := bstep (se 3 (by rfl) ⟨513509, by rfl⟩ : syracuseStep 2738717 = 1027019) B1027019
theorem B15584015 : Blo 810345 15584015 := bstep (se 1 (by rfl) ⟨11688011, by rfl⟩ : syracuseStep 15584015 = 23376023) B23376023
theorem B3296015 : Blo 810345 3296015 := bstep (se 1 (by rfl) ⟨2472011, by rfl⟩ : syracuseStep 3296015 = 4944023) B4944023
theorem B1755937 : Blo 810345 1755937 := bstep (se 2 (by rfl) ⟨658476, by rfl⟩ : syracuseStep 1755937 = 1316953) B1316953
theorem B2313107 : Blo 810345 2313107 := bstep (se 1 (by rfl) ⟨1734830, by rfl⟩ : syracuseStep 2313107 = 3469661) B3469661
theorem B14797835 : Blo 810345 14797835 := bstep (se 1 (by rfl) ⟨11098376, by rfl⟩ : syracuseStep 14797835 = 22196753) B22196753
theorem B3525869 : Blo 810345 3525869 := bstep (se 3 (by rfl) ⟨661100, by rfl⟩ : syracuseStep 3525869 = 1322201) B1322201
theorem B4115771 : Blo 810345 4115771 := bstep (se 1 (by rfl) ⟨3086828, by rfl⟩ : syracuseStep 4115771 = 6173657) B6173657
theorem B2608499 : Blo 810345 2608499 := bstep (se 1 (by rfl) ⟨1956374, by rfl⟩ : syracuseStep 2608499 = 3912749) B3912749
theorem B2084231 : Blo 810345 2084231 := bstep (se 1 (by rfl) ⟨1563173, by rfl⟩ : syracuseStep 2084231 = 3126347) B3126347
theorem B2608537 : Blo 810345 2608537 := bstep (se 2 (by rfl) ⟨978201, by rfl⟩ : syracuseStep 2608537 = 1956403) B1956403
theorem B4115933 : Blo 810345 4115933 := bstep (se 3 (by rfl) ⟨771737, by rfl⟩ : syracuseStep 4115933 = 1543475) B1543475
theorem B2051851 : Blo 810345 2051851 := bstep (se 1 (by rfl) ⟨1538888, by rfl⟩ : syracuseStep 2051851 = 3077777) B3077777
theorem B4116257 : Blo 810345 4116257 := bstep (se 2 (by rfl) ⟨1543596, by rfl⟩ : syracuseStep 4116257 = 3087193) B3087193
theorem B2051993 : Blo 810345 2051993 := bstep (se 2 (by rfl) ⟨769497, by rfl⟩ : syracuseStep 2051993 = 1538995) B1538995
theorem B2740121 : Blo 810345 2740121 := bstep (se 2 (by rfl) ⟨1027545, by rfl⟩ : syracuseStep 2740121 = 2055091) B2055091
theorem B2052155 : Blo 810345 2052155 := bstep (se 1 (by rfl) ⟨1539116, by rfl⟩ : syracuseStep 2052155 = 3078233) B3078233
theorem B2314507 : Blo 810345 2314507 := bstep (se 1 (by rfl) ⟨1735880, by rfl⟩ : syracuseStep 2314507 = 3471761) B3471761
theorem B3297569 : Blo 810345 3297569 := bstep (se 2 (by rfl) ⟨1236588, by rfl⟩ : syracuseStep 3297569 = 2473177) B2473177
theorem B2052499 : Blo 810345 2052499 := bstep (se 1 (by rfl) ⟨1539374, by rfl⟩ : syracuseStep 2052499 = 3078749) B3078749
theorem B1560979 : Blo 810345 1560979 := bstep (se 1 (by rfl) ⟨1170734, by rfl⟩ : syracuseStep 1560979 = 2341469) B2341469
theorem B1298873 : Blo 810345 1298873 := bstep (se 2 (by rfl) ⟨487077, by rfl⟩ : syracuseStep 1298873 = 974155) B974155
theorem B1233353 : Blo 810345 1233353 := bstep (se 2 (by rfl) ⟨462507, by rfl⟩ : syracuseStep 1233353 = 925015) B925015
theorem B159896081 : Blo 810345 159896081 := bstep (se 2 (by rfl) ⟨59961030, by rfl⟩ : syracuseStep 159896081 = 119922061) B119922061
theorem B2314781 : Blo 810345 2314781 := bstep (se 3 (by rfl) ⟨434021, by rfl⟩ : syracuseStep 2314781 = 868043) B868043
theorem B2052641 : Blo 810345 2052641 := bstep (se 2 (by rfl) ⟨769740, by rfl⟩ : syracuseStep 2052641 = 1539481) B1539481
theorem B1233451 : Blo 810345 1233451 := bstep (se 1 (by rfl) ⟨925088, by rfl⟩ : syracuseStep 1233451 = 1850177) B1850177
theorem B1823291 : Blo 810345 1823291 := bstep (se 1 (by rfl) ⟨1367468, by rfl⟩ : syracuseStep 1823291 = 2734937) B2734937
theorem B2740823 : Blo 810345 2740823 := bstep (se 1 (by rfl) ⟨2055617, by rfl⟩ : syracuseStep 2740823 = 4111235) B4111235
theorem B1823417 : Blo 810345 1823417 := bstep (se 2 (by rfl) ⟨683781, by rfl⟩ : syracuseStep 1823417 = 1367563) B1367563
theorem B4117229 : Blo 810345 4117229 := bstep (se 3 (by rfl) ⟨771980, by rfl⟩ : syracuseStep 4117229 = 1543961) B1543961
theorem B1823759 : Blo 810345 1823759 := bstep (se 1 (by rfl) ⟨1367819, by rfl⟩ : syracuseStep 1823759 = 2735639) B2735639
theorem B1823777 : Blo 810345 1823777 := bstep (se 2 (by rfl) ⟨683916, by rfl⟩ : syracuseStep 1823777 = 1367833) B1367833
theorem B2741309 : Blo 810345 2741309 := bstep (se 3 (by rfl) ⟨513995, by rfl⟩ : syracuseStep 2741309 = 1027991) B1027991
theorem B6935867 : Blo 810345 6935867 := bstep (se 1 (by rfl) ⟨5201900, by rfl⟩ : syracuseStep 6935867 = 10403801) B10403801
theorem B1824119 : Blo 810345 1824119 := bstep (se 1 (by rfl) ⟨1368089, by rfl⟩ : syracuseStep 1824119 = 2736179) B2736179
theorem B2053633 : Blo 810345 2053633 := bstep (se 2 (by rfl) ⟨770112, by rfl⟩ : syracuseStep 2053633 = 1540225) B1540225
theorem B4118039 : Blo 810345 4118039 := bstep (se 1 (by rfl) ⟨3088529, by rfl⟩ : syracuseStep 4118039 = 6177059) B6177059
theorem B5199389 : Blo 810345 5199389 := bstep (se 3 (by rfl) ⟨974885, by rfl⟩ : syracuseStep 5199389 = 1949771) B1949771
theorem B1824299 : Blo 810345 1824299 := bstep (se 1 (by rfl) ⟨1368224, by rfl⟩ : syracuseStep 1824299 = 2736449) B2736449
theorem B1234619 : Blo 810345 1234619 := bstep (se 1 (by rfl) ⟨925964, by rfl⟩ : syracuseStep 1234619 = 1851929) B1851929
theorem B47404865 : Blo 810345 47404865 := bstep (se 2 (by rfl) ⟨17776824, by rfl⟩ : syracuseStep 47404865 = 35553649) B35553649
theorem B1824659 : Blo 810345 1824659 := bstep (se 1 (by rfl) ⟨1368494, by rfl⟩ : syracuseStep 1824659 = 2736989) B2736989
theorem B1824713 : Blo 810345 1824713 := bstep (se 2 (by rfl) ⟨684267, by rfl⟩ : syracuseStep 1824713 = 1368535) B1368535
theorem B20043821 : Blo 810345 20043821 := bstep (se 3 (by rfl) ⟨3758216, by rfl⟩ : syracuseStep 20043821 = 7516433) B7516433
theorem B2054231 : Blo 810345 2054231 := bstep (se 1 (by rfl) ⟨1540673, by rfl⟩ : syracuseStep 2054231 = 3081347) B3081347
theorem B2054443 : Blo 810345 2054443 := bstep (se 1 (by rfl) ⟨1540832, by rfl⟩ : syracuseStep 2054443 = 3081665) B3081665
theorem B47569301 : Blo 810345 47569301 := bstep (se 6 (by rfl) ⟨1114905, by rfl⟩ : syracuseStep 47569301 = 2229811) B2229811
theorem B2054585 : Blo 810345 2054585 := bstep (se 2 (by rfl) ⟨770469, by rfl⟩ : syracuseStep 2054585 = 1540939) B1540939
theorem B2742713 : Blo 810345 2742713 := bstep (se 2 (by rfl) ⟨1028517, by rfl⟩ : syracuseStep 2742713 = 2057035) B2057035
theorem B6183377 : Blo 810345 6183377 := bstep (se 2 (by rfl) ⟨2318766, by rfl⟩ : syracuseStep 6183377 = 4637533) B4637533
theorem B1825415 : Blo 810345 1825415 := bstep (se 1 (by rfl) ⟨1369061, by rfl⟩ : syracuseStep 1825415 = 2738123) B2738123
theorem B1825595 : Blo 810345 1825595 := bstep (se 1 (by rfl) ⟨1369196, by rfl⟩ : syracuseStep 1825595 = 2738393) B2738393
theorem B1825721 : Blo 810345 1825721 := bstep (se 2 (by rfl) ⟨684645, by rfl⟩ : syracuseStep 1825721 = 1369291) B1369291
theorem B2317241 : Blo 810345 2317241 := bstep (se 2 (by rfl) ⟨868965, by rfl⟩ : syracuseStep 2317241 = 1737931) B1737931
theorem B2743307 : Blo 810345 2743307 := bstep (se 1 (by rfl) ⟨2057480, by rfl⟩ : syracuseStep 2743307 = 4114961) B4114961
theorem B2317355 : Blo 810345 2317355 := bstep (se 1 (by rfl) ⟨1738016, by rfl⟩ : syracuseStep 2317355 = 3476033) B3476033
theorem B2743415 : Blo 810345 2743415 := bstep (se 1 (by rfl) ⟨2057561, by rfl⟩ : syracuseStep 2743415 = 4115123) B4115123
theorem B1826063 : Blo 810345 1826063 := bstep (se 1 (by rfl) ⟨1369547, by rfl⟩ : syracuseStep 1826063 = 2739095) B2739095
theorem B1465615 : Blo 810345 1465615 := bstep (se 1 (by rfl) ⟨1099211, by rfl⟩ : syracuseStep 1465615 = 2198423) B2198423
theorem B1826081 : Blo 810345 1826081 := bstep (se 2 (by rfl) ⟨684780, by rfl⟩ : syracuseStep 1826081 = 1369561) B1369561
theorem B810375 : Blo 810345 810375 := bstep (se 1 (by rfl) ⟨607781, by rfl⟩ : syracuseStep 810375 = 1215563) B1215563
theorem B810383 : Blo 810345 810383 := bstep (se 1 (by rfl) ⟨607787, by rfl⟩ : syracuseStep 810383 = 1215575) B1215575
theorem B2055577 : Blo 810345 2055577 := bstep (se 2 (by rfl) ⟨770841, by rfl⟩ : syracuseStep 2055577 = 1541683) B1541683
theorem B810427 : Blo 810345 810427 := bstep (se 1 (by rfl) ⟨607820, by rfl⟩ : syracuseStep 810427 = 1215641) B1215641
theorem B810503 : Blo 810345 810503 := bstep (se 1 (by rfl) ⟨607877, by rfl⟩ : syracuseStep 810503 = 1215755) B1215755
theorem B810511 : Blo 810345 810511 := bstep (se 1 (by rfl) ⟨607883, by rfl⟩ : syracuseStep 810511 = 1215767) B1215767
theorem B16080413 : Blo 810345 16080413 := bstep (se 3 (by rfl) ⟨3015077, by rfl⟩ : syracuseStep 16080413 = 6030155) B6030155
theorem B1039915 : Blo 810345 1039915 := bstep (se 1 (by rfl) ⟨779936, by rfl⟩ : syracuseStep 1039915 = 1559873) B1559873
theorem B810555 : Blo 810345 810555 := bstep (se 1 (by rfl) ⟨607916, by rfl⟩ : syracuseStep 810555 = 1215833) B1215833
theorem B2055739 : Blo 810345 2055739 := bstep (se 1 (by rfl) ⟨1541804, by rfl⟩ : syracuseStep 2055739 = 3083609) B3083609
theorem B1367671 : Blo 810345 1367671 := bstep (se 1 (by rfl) ⟨1025753, by rfl⟩ : syracuseStep 1367671 = 2051507) B2051507
theorem B1826423 : Blo 810345 1826423 := bstep (se 1 (by rfl) ⟨1369817, by rfl⟩ : syracuseStep 1826423 = 2739635) B2739635
theorem B810631 : Blo 810345 810631 := bstep (se 1 (by rfl) ⟨607973, by rfl⟩ : syracuseStep 810631 = 1215947) B1215947
theorem B810639 : Blo 810345 810639 := bstep (se 1 (by rfl) ⟨607979, by rfl⟩ : syracuseStep 810639 = 1215959) B1215959
theorem B810683 : Blo 810345 810683 := bstep (se 1 (by rfl) ⟨608012, by rfl⟩ : syracuseStep 810683 = 1216025) B1216025
theorem B2055881 : Blo 810345 2055881 := bstep (se 2 (by rfl) ⟨770955, by rfl⟩ : syracuseStep 2055881 = 1541911) B1541911
theorem B2744009 : Blo 810345 2744009 := bstep (se 2 (by rfl) ⟨1029003, by rfl⟩ : syracuseStep 2744009 = 2058007) B2058007
theorem B810759 : Blo 810345 810759 := bstep (se 1 (by rfl) ⟨608069, by rfl⟩ : syracuseStep 810759 = 1216139) B1216139
theorem B810767 : Blo 810345 810767 := bstep (se 1 (by rfl) ⟨608075, by rfl⟩ : syracuseStep 810767 = 1216151) B1216151
theorem B1826603 : Blo 810345 1826603 := bstep (se 1 (by rfl) ⟨1369952, by rfl⟩ : syracuseStep 1826603 = 2739905) B2739905
theorem B1367867 : Blo 810345 1367867 := bstep (se 1 (by rfl) ⟨1025900, by rfl⟩ : syracuseStep 1367867 = 2051801) B2051801
theorem B810811 : Blo 810345 810811 := bstep (se 1 (by rfl) ⟨608108, by rfl⟩ : syracuseStep 810811 = 1216217) B1216217
theorem B810887 : Blo 810345 810887 := bstep (se 1 (by rfl) ⟨608165, by rfl⟩ : syracuseStep 810887 = 1216331) B1216331
theorem B810895 : Blo 810345 810895 := bstep (se 1 (by rfl) ⟨608171, by rfl⟩ : syracuseStep 810895 = 1216343) B1216343
theorem B6938531 : Blo 810345 6938531 := bstep (se 1 (by rfl) ⟨5203898, by rfl⟩ : syracuseStep 6938531 = 10407797) B10407797
theorem B810939 : Blo 810345 810939 := bstep (se 1 (by rfl) ⟨608204, by rfl⟩ : syracuseStep 810939 = 1216409) B1216409
theorem B811015 : Blo 810345 811015 := bstep (se 1 (by rfl) ⟨608261, by rfl⟩ : syracuseStep 811015 = 1216523) B1216523
theorem B811023 : Blo 810345 811023 := bstep (se 1 (by rfl) ⟨608267, by rfl⟩ : syracuseStep 811023 = 1216535) B1216535
theorem B2056225 : Blo 810345 2056225 := bstep (se 2 (by rfl) ⟨771084, by rfl⟩ : syracuseStep 2056225 = 1542169) B1542169
theorem B811067 : Blo 810345 811067 := bstep (se 1 (by rfl) ⟨608300, by rfl⟩ : syracuseStep 811067 = 1216601) B1216601
theorem B811143 : Blo 810345 811143 := bstep (se 1 (by rfl) ⟨608357, by rfl⟩ : syracuseStep 811143 = 1216715) B1216715
theorem B811151 : Blo 810345 811151 := bstep (se 1 (by rfl) ⟨608363, by rfl⟩ : syracuseStep 811151 = 1216727) B1216727
theorem B1826963 : Blo 810345 1826963 := bstep (se 1 (by rfl) ⟨1370222, by rfl⟩ : syracuseStep 1826963 = 2740445) B2740445
theorem B2318483 : Blo 810345 2318483 := bstep (se 1 (by rfl) ⟨1738862, by rfl⟩ : syracuseStep 2318483 = 3477725) B3477725
theorem B811195 : Blo 810345 811195 := bstep (se 1 (by rfl) ⟨608396, by rfl⟩ : syracuseStep 811195 = 1216793) B1216793
theorem B975035 : Blo 810345 975035 := bstep (se 1 (by rfl) ⟨731276, by rfl⟩ : syracuseStep 975035 = 1462553) B1462553
theorem B1368265 : Blo 810345 1368265 := bstep (se 2 (by rfl) ⟨513099, by rfl⟩ : syracuseStep 1368265 = 1026199) B1026199
theorem B1827017 : Blo 810345 1827017 := bstep (se 2 (by rfl) ⟨685131, by rfl⟩ : syracuseStep 1827017 = 1370263) B1370263
theorem B811271 : Blo 810345 811271 := bstep (se 1 (by rfl) ⟨608453, by rfl⟩ : syracuseStep 811271 = 1216907) B1216907
theorem B811279 : Blo 810345 811279 := bstep (se 1 (by rfl) ⟨608459, by rfl⟩ : syracuseStep 811279 = 1216919) B1216919
theorem B811323 : Blo 810345 811323 := bstep (se 1 (by rfl) ⟨608492, by rfl⟩ : syracuseStep 811323 = 1216985) B1216985
theorem B811399 : Blo 810345 811399 := bstep (se 1 (by rfl) ⟨608549, by rfl⟩ : syracuseStep 811399 = 1217099) B1217099
theorem B2744711 : Blo 810345 2744711 := bstep (se 1 (by rfl) ⟨2058533, by rfl⟩ : syracuseStep 2744711 = 4117067) B4117067
theorem B811407 : Blo 810345 811407 := bstep (se 1 (by rfl) ⟨608555, by rfl⟩ : syracuseStep 811407 = 1217111) B1217111
theorem B811451 : Blo 810345 811451 := bstep (se 1 (by rfl) ⟨608588, by rfl⟩ : syracuseStep 811451 = 1217177) B1217177
theorem B811527 : Blo 810345 811527 := bstep (se 1 (by rfl) ⟨608645, by rfl⟩ : syracuseStep 811527 = 1217291) B1217291
theorem B811535 : Blo 810345 811535 := bstep (se 1 (by rfl) ⟨608651, by rfl⟩ : syracuseStep 811535 = 1217303) B1217303
theorem B4121117 : Blo 810345 4121117 := bstep (se 3 (by rfl) ⟨772709, by rfl⟩ : syracuseStep 4121117 = 1545419) B1545419
theorem B2318881 : Blo 810345 2318881 := bstep (se 2 (by rfl) ⟨869580, by rfl⟩ : syracuseStep 2318881 = 1739161) B1739161
theorem B811579 : Blo 810345 811579 := bstep (se 1 (by rfl) ⟨608684, by rfl⟩ : syracuseStep 811579 = 1217369) B1217369
theorem B2056823 : Blo 810345 2056823 := bstep (se 1 (by rfl) ⟨1542617, by rfl⟩ : syracuseStep 2056823 = 3085235) B3085235
theorem B39608963 : Blo 810345 39608963 := bstep (se 1 (by rfl) ⟨29706722, by rfl⟩ : syracuseStep 39608963 = 59413445) B59413445
theorem B811655 : Blo 810345 811655 := bstep (se 1 (by rfl) ⟨608741, by rfl⟩ : syracuseStep 811655 = 1217483) B1217483
theorem B811663 : Blo 810345 811663 := bstep (se 1 (by rfl) ⟨608747, by rfl⟩ : syracuseStep 811663 = 1217495) B1217495
theorem B811707 : Blo 810345 811707 := bstep (se 1 (by rfl) ⟨608780, by rfl⟩ : syracuseStep 811707 = 1217561) B1217561
theorem B3465985 : Blo 810345 3465985 := bstep (se 2 (by rfl) ⟨1299744, by rfl⟩ : syracuseStep 3465985 = 2599489) B2599489
theorem B2745089 : Blo 810345 2745089 := bstep (se 2 (by rfl) ⟨1029408, by rfl⟩ : syracuseStep 2745089 = 2058817) B2058817
theorem B811783 : Blo 810345 811783 := bstep (se 1 (by rfl) ⟨608837, by rfl⟩ : syracuseStep 811783 = 1217675) B1217675
theorem B811791 : Blo 810345 811791 := bstep (se 1 (by rfl) ⟨608843, by rfl⟩ : syracuseStep 811791 = 1217687) B1217687
theorem B811835 : Blo 810345 811835 := bstep (se 1 (by rfl) ⟨608876, by rfl⟩ : syracuseStep 811835 = 1217753) B1217753
theorem B1368967 : Blo 810345 1368967 := bstep (se 1 (by rfl) ⟨1026725, by rfl⟩ : syracuseStep 1368967 = 2053451) B2053451
theorem B811911 : Blo 810345 811911 := bstep (se 1 (by rfl) ⟨608933, by rfl⟩ : syracuseStep 811911 = 1217867) B1217867
theorem B1827719 : Blo 810345 1827719 := bstep (se 1 (by rfl) ⟨1370789, by rfl⟩ : syracuseStep 1827719 = 2741579) B2741579
theorem B811919 : Blo 810345 811919 := bstep (se 1 (by rfl) ⟨608939, by rfl⟩ : syracuseStep 811919 = 1217879) B1217879
theorem B37479347 : Blo 810345 37479347 := bstep (se 1 (by rfl) ⟨28109510, by rfl⟩ : syracuseStep 37479347 = 56219021) B56219021
theorem B811963 : Blo 810345 811963 := bstep (se 1 (by rfl) ⟨608972, by rfl⟩ : syracuseStep 811963 = 1217945) B1217945
theorem B4121603 : Blo 810345 4121603 := bstep (se 1 (by rfl) ⟨3091202, by rfl⟩ : syracuseStep 4121603 = 6182405) B6182405
theorem B812039 : Blo 810345 812039 := bstep (se 1 (by rfl) ⟨609029, by rfl⟩ : syracuseStep 812039 = 1218059) B1218059
theorem B812047 : Blo 810345 812047 := bstep (se 1 (by rfl) ⟨609035, by rfl⟩ : syracuseStep 812047 = 1218071) B1218071
theorem B812091 : Blo 810345 812091 := bstep (se 1 (by rfl) ⟨609068, by rfl⟩ : syracuseStep 812091 = 1218137) B1218137
theorem B1827899 : Blo 810345 1827899 := bstep (se 1 (by rfl) ⟨1370924, by rfl⟩ : syracuseStep 1827899 = 2741849) B2741849
theorem B3466327 : Blo 810345 3466327 := bstep (se 1 (by rfl) ⟨2599745, by rfl⟩ : syracuseStep 3466327 = 5199491) B5199491
theorem B812167 : Blo 810345 812167 := bstep (se 1 (by rfl) ⟨609125, by rfl⟩ : syracuseStep 812167 = 1218251) B1218251
theorem B812175 : Blo 810345 812175 := bstep (se 1 (by rfl) ⟨609131, by rfl⟩ : syracuseStep 812175 = 1218263) B1218263
theorem B4678829 : Blo 810345 4678829 := bstep (se 3 (by rfl) ⟨877280, by rfl⟩ : syracuseStep 4678829 = 1754561) B1754561
theorem B1828025 : Blo 810345 1828025 := bstep (se 2 (by rfl) ⟨685509, by rfl⟩ : syracuseStep 1828025 = 1371019) B1371019
theorem B812219 : Blo 810345 812219 := bstep (se 1 (by rfl) ⟨609164, by rfl⟩ : syracuseStep 812219 = 1218329) B1218329
theorem B812295 : Blo 810345 812295 := bstep (se 1 (by rfl) ⟨609221, by rfl⟩ : syracuseStep 812295 = 1218443) B1218443
theorem B976135 : Blo 810345 976135 := bstep (se 1 (by rfl) ⟨732101, by rfl⟩ : syracuseStep 976135 = 1464203) B1464203
theorem B812303 : Blo 810345 812303 := bstep (se 1 (by rfl) ⟨609227, by rfl⟩ : syracuseStep 812303 = 1218455) B1218455
theorem B812347 : Blo 810345 812347 := bstep (se 1 (by rfl) ⟨609260, by rfl⟩ : syracuseStep 812347 = 1218521) B1218521
theorem B812423 : Blo 810345 812423 := bstep (se 1 (by rfl) ⟨609317, by rfl⟩ : syracuseStep 812423 = 1218635) B1218635
theorem B812431 : Blo 810345 812431 := bstep (se 1 (by rfl) ⟨609323, by rfl⟩ : syracuseStep 812431 = 1218647) B1218647
theorem B812475 : Blo 810345 812475 := bstep (se 1 (by rfl) ⟨609356, by rfl⟩ : syracuseStep 812475 = 1218713) B1218713
theorem B6153731 : Blo 810345 6153731 := bstep (se 1 (by rfl) ⟨4615298, by rfl⟩ : syracuseStep 6153731 = 9230597) B9230597
theorem B812551 : Blo 810345 812551 := bstep (se 1 (by rfl) ⟨609413, by rfl⟩ : syracuseStep 812551 = 1218827) B1218827
theorem B1369615 : Blo 810345 1369615 := bstep (se 1 (by rfl) ⟨1027211, by rfl⟩ : syracuseStep 1369615 = 2054423) B2054423
theorem B812559 : Blo 810345 812559 := bstep (se 1 (by rfl) ⟨609419, by rfl⟩ : syracuseStep 812559 = 1218839) B1218839
theorem B1828367 : Blo 810345 1828367 := bstep (se 1 (by rfl) ⟨1371275, by rfl⟩ : syracuseStep 1828367 = 2742551) B2742551
theorem B1828385 : Blo 810345 1828385 := bstep (se 2 (by rfl) ⟨685644, by rfl⟩ : syracuseStep 1828385 = 1371289) B1371289
theorem B2745899 : Blo 810345 2745899 := bstep (se 1 (by rfl) ⟨2059424, by rfl⟩ : syracuseStep 2745899 = 4118849) B4118849
theorem B812603 : Blo 810345 812603 := bstep (se 1 (by rfl) ⟨609452, by rfl⟩ : syracuseStep 812603 = 1218905) B1218905
theorem B812679 : Blo 810345 812679 := bstep (se 1 (by rfl) ⟨609509, by rfl⟩ : syracuseStep 812679 = 1219019) B1219019
theorem B812687 : Blo 810345 812687 := bstep (se 1 (by rfl) ⟨609515, by rfl⟩ : syracuseStep 812687 = 1219031) B1219031
theorem B812731 : Blo 810345 812731 := bstep (se 1 (by rfl) ⟨609548, by rfl⟩ : syracuseStep 812731 = 1219097) B1219097
theorem B812807 : Blo 810345 812807 := bstep (se 1 (by rfl) ⟨609605, by rfl⟩ : syracuseStep 812807 = 1219211) B1219211
theorem B812815 : Blo 810345 812815 := bstep (se 1 (by rfl) ⟨609611, by rfl⟩ : syracuseStep 812815 = 1219223) B1219223
theorem B1173263 : Blo 810345 1173263 := bstep (se 1 (by rfl) ⟨879947, by rfl⟩ : syracuseStep 1173263 = 1759895) B1759895
theorem B812859 : Blo 810345 812859 := bstep (se 1 (by rfl) ⟨609644, by rfl⟩ : syracuseStep 812859 = 1219289) B1219289
theorem B1828727 : Blo 810345 1828727 := bstep (se 1 (by rfl) ⟨1371545, by rfl⟩ : syracuseStep 1828727 = 2743091) B2743091
theorem B812935 : Blo 810345 812935 := bstep (se 1 (by rfl) ⟨609701, by rfl⟩ : syracuseStep 812935 = 1219403) B1219403
theorem B2058119 : Blo 810345 2058119 := bstep (se 1 (by rfl) ⟨1543589, by rfl⟩ : syracuseStep 2058119 = 3087179) B3087179
theorem B812943 : Blo 810345 812943 := bstep (se 1 (by rfl) ⟨609707, by rfl⟩ : syracuseStep 812943 = 1219415) B1219415
theorem B2058169 : Blo 810345 2058169 := bstep (se 2 (by rfl) ⟨771813, by rfl⟩ : syracuseStep 2058169 = 1543627) B1543627
theorem B812987 : Blo 810345 812987 := bstep (se 1 (by rfl) ⟨609740, by rfl⟩ : syracuseStep 812987 = 1219481) B1219481
theorem B813063 : Blo 810345 813063 := bstep (se 1 (by rfl) ⟨609797, by rfl⟩ : syracuseStep 813063 = 1219595) B1219595
theorem B813071 : Blo 810345 813071 := bstep (se 1 (by rfl) ⟨609803, by rfl⟩ : syracuseStep 813071 = 1219607) B1219607
theorem B1370155 : Blo 810345 1370155 := bstep (se 1 (by rfl) ⟨1027616, by rfl⟩ : syracuseStep 1370155 = 2055233) B2055233
theorem B1828907 : Blo 810345 1828907 := bstep (se 1 (by rfl) ⟨1371680, by rfl⟩ : syracuseStep 1828907 = 2743361) B2743361
theorem B813115 : Blo 810345 813115 := bstep (se 1 (by rfl) ⟨609836, by rfl⟩ : syracuseStep 813115 = 1219673) B1219673
theorem B813191 : Blo 810345 813191 := bstep (se 1 (by rfl) ⟨609893, by rfl⟩ : syracuseStep 813191 = 1219787) B1219787
theorem B813199 : Blo 810345 813199 := bstep (se 1 (by rfl) ⟨609899, by rfl⟩ : syracuseStep 813199 = 1219799) B1219799
theorem B1370297 : Blo 810345 1370297 := bstep (se 2 (by rfl) ⟨513861, by rfl⟩ : syracuseStep 1370297 = 1027723) B1027723
theorem B813243 : Blo 810345 813243 := bstep (se 1 (by rfl) ⟨609932, by rfl⟩ : syracuseStep 813243 = 1219865) B1219865
theorem B813319 : Blo 810345 813319 := bstep (se 1 (by rfl) ⟨609989, by rfl⟩ : syracuseStep 813319 = 1219979) B1219979
theorem B813327 : Blo 810345 813327 := bstep (se 1 (by rfl) ⟨609995, by rfl⟩ : syracuseStep 813327 = 1219991) B1219991
theorem B813371 : Blo 810345 813371 := bstep (se 1 (by rfl) ⟨610028, by rfl⟩ : syracuseStep 813371 = 1220057) B1220057
theorem B813447 : Blo 810345 813447 := bstep (se 1 (by rfl) ⟨610085, by rfl⟩ : syracuseStep 813447 = 1220171) B1220171
theorem B813455 : Blo 810345 813455 := bstep (se 1 (by rfl) ⟨610091, by rfl⟩ : syracuseStep 813455 = 1220183) B1220183
theorem B1829267 : Blo 810345 1829267 := bstep (se 1 (by rfl) ⟨1371950, by rfl⟩ : syracuseStep 1829267 = 2743901) B2743901
theorem B911803 : Blo 810345 911803 := bstep (se 1 (by rfl) ⟨683852, by rfl⟩ : syracuseStep 911803 = 1367705) B1367705
theorem B813499 : Blo 810345 813499 := bstep (se 1 (by rfl) ⟨610124, by rfl⟩ : syracuseStep 813499 = 1220249) B1220249
theorem B1829321 : Blo 810345 1829321 := bstep (se 2 (by rfl) ⟨685995, by rfl⟩ : syracuseStep 1829321 = 1371991) B1371991
theorem B813575 : Blo 810345 813575 := bstep (se 1 (by rfl) ⟨610181, by rfl⟩ : syracuseStep 813575 = 1220363) B1220363
theorem B2058767 : Blo 810345 2058767 := bstep (se 1 (by rfl) ⟨1544075, by rfl⟩ : syracuseStep 2058767 = 3088151) B3088151
theorem B813583 : Blo 810345 813583 := bstep (se 1 (by rfl) ⟨610187, by rfl⟩ : syracuseStep 813583 = 1220375) B1220375
theorem B813627 : Blo 810345 813627 := bstep (se 1 (by rfl) ⟨610220, by rfl⟩ : syracuseStep 813627 = 1220441) B1220441
theorem B813703 : Blo 810345 813703 := bstep (se 1 (by rfl) ⟨610277, by rfl⟩ : syracuseStep 813703 = 1220555) B1220555
theorem B813711 : Blo 810345 813711 := bstep (se 1 (by rfl) ⟨610283, by rfl⟩ : syracuseStep 813711 = 1220567) B1220567
theorem B813755 : Blo 810345 813755 := bstep (se 1 (by rfl) ⟨610316, by rfl⟩ : syracuseStep 813755 = 1220633) B1220633
theorem B813831 : Blo 810345 813831 := bstep (se 1 (by rfl) ⟨610373, by rfl⟩ : syracuseStep 813831 = 1220747) B1220747
theorem B813839 : Blo 810345 813839 := bstep (se 1 (by rfl) ⟨610379, by rfl⟩ : syracuseStep 813839 = 1220759) B1220759
theorem B813883 : Blo 810345 813883 := bstep (se 1 (by rfl) ⟨610412, by rfl⟩ : syracuseStep 813883 = 1220825) B1220825
theorem B2747195 : Blo 810345 2747195 := bstep (se 1 (by rfl) ⟨2060396, by rfl⟩ : syracuseStep 2747195 = 4120793) B4120793
theorem B1370999 : Blo 810345 1370999 := bstep (se 1 (by rfl) ⟨1028249, by rfl⟩ : syracuseStep 1370999 = 2056499) B2056499
theorem B813959 : Blo 810345 813959 := bstep (se 1 (by rfl) ⟨610469, by rfl⟩ : syracuseStep 813959 = 1220939) B1220939
theorem B912271 : Blo 810345 912271 := bstep (se 1 (by rfl) ⟨684203, by rfl⟩ : syracuseStep 912271 = 1368407) B1368407
theorem B813967 : Blo 810345 813967 := bstep (se 1 (by rfl) ⟨610475, by rfl⟩ : syracuseStep 813967 = 1220951) B1220951
theorem B814011 : Blo 810345 814011 := bstep (se 1 (by rfl) ⟨610508, by rfl⟩ : syracuseStep 814011 = 1221017) B1221017
theorem B814087 : Blo 810345 814087 := bstep (se 1 (by rfl) ⟨610565, by rfl⟩ : syracuseStep 814087 = 1221131) B1221131
theorem B814095 : Blo 810345 814095 := bstep (se 1 (by rfl) ⟨610571, by rfl⟩ : syracuseStep 814095 = 1221143) B1221143
theorem B814139 : Blo 810345 814139 := bstep (se 1 (by rfl) ⟨610604, by rfl⟩ : syracuseStep 814139 = 1221209) B1221209
theorem B1830023 : Blo 810345 1830023 := bstep (se 1 (by rfl) ⟨1372517, by rfl⟩ : syracuseStep 1830023 = 2745035) B2745035
theorem B814215 : Blo 810345 814215 := bstep (se 1 (by rfl) ⟨610661, by rfl⟩ : syracuseStep 814215 = 1221323) B1221323
theorem B814223 : Blo 810345 814223 := bstep (se 1 (by rfl) ⟨610667, by rfl⟩ : syracuseStep 814223 = 1221335) B1221335
theorem B814267 : Blo 810345 814267 := bstep (se 1 (by rfl) ⟨610700, by rfl⟩ : syracuseStep 814267 = 1221401) B1221401
theorem B2059465 : Blo 810345 2059465 := bstep (se 2 (by rfl) ⟨772299, by rfl⟩ : syracuseStep 2059465 = 1544599) B1544599
theorem B814343 : Blo 810345 814343 := bstep (se 1 (by rfl) ⟨610757, by rfl⟩ : syracuseStep 814343 = 1221515) B1221515
theorem B2747681 : Blo 810345 2747681 := bstep (se 2 (by rfl) ⟨1030380, by rfl⟩ : syracuseStep 2747681 = 2060761) B2060761
theorem B1731899 : Blo 810345 1731899 := bstep (se 1 (by rfl) ⟨1298924, by rfl⟩ : syracuseStep 1731899 = 2597849) B2597849
theorem B1371451 : Blo 810345 1371451 := bstep (se 1 (by rfl) ⟨1028588, by rfl⟩ : syracuseStep 1371451 = 2057177) B2057177
theorem B1830203 : Blo 810345 1830203 := bstep (se 1 (by rfl) ⟨1372652, by rfl⟩ : syracuseStep 1830203 = 2745305) B2745305
theorem B2059607 : Blo 810345 2059607 := bstep (se 1 (by rfl) ⟨1544705, by rfl⟩ : syracuseStep 2059607 = 3089411) B3089411
theorem B912775 : Blo 810345 912775 := bstep (se 1 (by rfl) ⟨684581, by rfl⟩ : syracuseStep 912775 = 1369163) B1369163
theorem B15822215 : Blo 810345 15822215 := bstep (se 1 (by rfl) ⟨11866661, by rfl⟩ : syracuseStep 15822215 = 23733323) B23733323
theorem B1830329 : Blo 810345 1830329 := bstep (se 2 (by rfl) ⟨686373, by rfl⟩ : syracuseStep 1830329 = 1372747) B1372747
theorem B1371593 : Blo 810345 1371593 := bstep (se 2 (by rfl) ⟨514347, by rfl⟩ : syracuseStep 1371593 = 1028695) B1028695
theorem B7400963 : Blo 810345 7400963 := bstep (se 1 (by rfl) ⟨5550722, by rfl⟩ : syracuseStep 7400963 = 11101445) B11101445
theorem B912955 : Blo 810345 912955 := bstep (se 1 (by rfl) ⟨684716, by rfl⟩ : syracuseStep 912955 = 1369433) B1369433
theorem B4615937 : Blo 810345 4615937 := bstep (se 2 (by rfl) ⟨1730976, by rfl⟩ : syracuseStep 4615937 = 3461953) B3461953
theorem B1830671 : Blo 810345 1830671 := bstep (se 1 (by rfl) ⟨1373003, by rfl⟩ : syracuseStep 1830671 = 2746007) B2746007
theorem B1830689 : Blo 810345 1830689 := bstep (se 2 (by rfl) ⟨686508, by rfl⟩ : syracuseStep 1830689 = 1373017) B1373017
theorem B7401253 : Blo 810345 7401253 := bstep (se 4 (by rfl) ⟨693867, by rfl⟩ : syracuseStep 7401253 = 1387735) B1387735
theorem B5009203 : Blo 810345 5009203 := bstep (se 1 (by rfl) ⟨3756902, by rfl⟩ : syracuseStep 5009203 = 7513805) B7513805
theorem B2748275 : Blo 810345 2748275 := bstep (se 1 (by rfl) ⟨2061206, by rfl⟩ : syracuseStep 2748275 = 4122413) B4122413
theorem B913423 : Blo 810345 913423 := bstep (se 1 (by rfl) ⟨685067, by rfl⟩ : syracuseStep 913423 = 1370135) B1370135
theorem B45117461 : Blo 810345 45117461 := bstep (se 6 (by rfl) ⟨1057440, by rfl⟩ : syracuseStep 45117461 = 2114881) B2114881
theorem B3960893 : Blo 810345 3960893 := bstep (se 3 (by rfl) ⟨742667, by rfl⟩ : syracuseStep 3960893 = 1485335) B1485335
theorem B1831031 : Blo 810345 1831031 := bstep (se 1 (by rfl) ⟨1373273, by rfl⟩ : syracuseStep 1831031 = 2746547) B2746547
theorem B2191495 : Blo 810345 2191495 := bstep (se 1 (by rfl) ⟨1643621, by rfl⟩ : syracuseStep 2191495 = 3287243) B3287243
theorem B1372295 : Blo 810345 1372295 := bstep (se 1 (by rfl) ⟨1029221, by rfl⟩ : syracuseStep 1372295 = 2058443) B2058443
theorem B1831211 : Blo 810345 1831211 := bstep (se 1 (by rfl) ⟨1373408, by rfl⟩ : syracuseStep 1831211 = 2746817) B2746817
theorem B3895697 : Blo 810345 3895697 := bstep (se 2 (by rfl) ⟨1460886, by rfl⟩ : syracuseStep 3895697 = 2921773) B2921773
theorem B913927 : Blo 810345 913927 := bstep (se 1 (by rfl) ⟨685445, by rfl⟩ : syracuseStep 913927 = 1370891) B1370891
theorem B1831571 : Blo 810345 1831571 := bstep (se 1 (by rfl) ⟨1373678, by rfl⟩ : syracuseStep 1831571 = 2747357) B2747357
theorem B914107 : Blo 810345 914107 := bstep (se 1 (by rfl) ⟨685580, by rfl⟩ : syracuseStep 914107 = 1371161) B1371161
theorem B1831625 : Blo 810345 1831625 := bstep (se 2 (by rfl) ⟨686859, by rfl⟩ : syracuseStep 1831625 = 1373719) B1373719
theorem B1372943 : Blo 810345 1372943 := bstep (se 1 (by rfl) ⟨1029707, by rfl⟩ : syracuseStep 1372943 = 2059415) B2059415
theorem B4682611 : Blo 810345 4682611 := bstep (se 1 (by rfl) ⟨3511958, by rfl⟩ : syracuseStep 4682611 = 7023917) B7023917
theorem B914575 : Blo 810345 914575 := bstep (se 1 (by rfl) ⟨685931, by rfl⟩ : syracuseStep 914575 = 1371863) B1371863
theorem B1373483 : Blo 810345 1373483 := bstep (se 1 (by rfl) ⟨1030112, by rfl⟩ : syracuseStep 1373483 = 2060225) B2060225
theorem B3339667 : Blo 810345 3339667 := bstep (se 1 (by rfl) ⟨2504750, by rfl⟩ : syracuseStep 3339667 = 5009501) B5009501
theorem B4388413 : Blo 810345 4388413 := bstep (se 3 (by rfl) ⟨822827, by rfl⟩ : syracuseStep 4388413 = 1645655) B1645655
theorem B915079 : Blo 810345 915079 := bstep (se 1 (by rfl) ⟨686309, by rfl⟩ : syracuseStep 915079 = 1372619) B1372619
theorem B4388525 : Blo 810345 4388525 := bstep (se 3 (by rfl) ⟨822848, by rfl⟩ : syracuseStep 4388525 = 1645697) B1645697
theorem B1373881 : Blo 810345 1373881 := bstep (se 2 (by rfl) ⟨515205, by rfl⟩ : syracuseStep 1373881 = 1030411) B1030411
theorem B915259 : Blo 810345 915259 := bstep (se 1 (by rfl) ⟨686444, by rfl⟩ : syracuseStep 915259 = 1372889) B1372889
theorem B4159367 : Blo 810345 4159367 := bstep (se 1 (by rfl) ⟨3119525, by rfl⟩ : syracuseStep 4159367 = 6239051) B6239051
theorem B3078263 : Blo 810345 3078263 := bstep (se 1 (by rfl) ⟨2308697, by rfl⟩ : syracuseStep 3078263 = 4617395) B4617395
theorem B915727 : Blo 810345 915727 := bstep (se 1 (by rfl) ⟨686795, by rfl⟩ : syracuseStep 915727 = 1373591) B1373591
theorem B2783641 : Blo 810345 2783641 := bstep (se 2 (by rfl) ⟨1043865, by rfl⟩ : syracuseStep 2783641 = 2087731) B2087731
theorem B4684349 : Blo 810345 4684349 := bstep (se 3 (by rfl) ⟨878315, by rfl⟩ : syracuseStep 4684349 = 1756631) B1756631
theorem B6159077 : Blo 810345 6159077 := bstep (se 4 (by rfl) ⟨577413, by rfl⟩ : syracuseStep 6159077 = 1154827) B1154827
theorem B9239345 : Blo 810345 9239345 := bstep (se 2 (by rfl) ⟨3464754, by rfl⟩ : syracuseStep 9239345 = 6929509) B6929509
theorem B3079235 : Blo 810345 3079235 := bstep (se 1 (by rfl) ⟨2309426, by rfl⟩ : syracuseStep 3079235 = 4618853) B4618853
theorem B3079691 : Blo 810345 3079691 := bstep (se 1 (by rfl) ⟨2309768, by rfl⟩ : syracuseStep 3079691 = 4619537) B4619537
theorem B1539785 : Blo 810345 1539785 := bstep (se 2 (by rfl) ⟨577419, by rfl⟩ : syracuseStep 1539785 = 1154839) B1154839
theorem B1736633 : Blo 810345 1736633 := bstep (se 2 (by rfl) ⟨651237, by rfl⟩ : syracuseStep 1736633 = 1302475) B1302475
theorem B3080207 : Blo 810345 3080207 := bstep (se 1 (by rfl) ⟨2310155, by rfl⟩ : syracuseStep 3080207 = 4620311) B4620311
theorem B13205585 : Blo 810345 13205585 := bstep (se 2 (by rfl) ⟨4952094, by rfl⟩ : syracuseStep 13205585 = 9904189) B9904189
theorem B3473675 : Blo 810345 3473675 := bstep (se 1 (by rfl) ⟨2605256, by rfl⟩ : syracuseStep 3473675 = 5210513) B5210513
theorem B5505671 : Blo 810345 5505671 := bstep (se 1 (by rfl) ⟨4129253, by rfl⟩ : syracuseStep 5505671 = 8258507) B8258507
theorem B3474359 : Blo 810345 3474359 := bstep (se 1 (by rfl) ⟨2605769, by rfl⟩ : syracuseStep 3474359 = 5211539) B5211539
theorem B4621313 : Blo 810345 4621313 := bstep (se 2 (by rfl) ⟨1732992, by rfl⟩ : syracuseStep 4621313 = 3465985) B3465985
theorem B15631379 : Blo 810345 15631379 := bstep (se 1 (by rfl) ⟨11723534, by rfl⟩ : syracuseStep 15631379 = 23447069) B23447069
theorem B1541243 : Blo 810345 1541243 := bstep (se 1 (by rfl) ⟨1155932, by rfl⟩ : syracuseStep 1541243 = 2311865) B2311865
theorem B14058917 : Blo 810345 14058917 := bstep (se 4 (by rfl) ⟨1318023, by rfl⟩ : syracuseStep 14058917 = 2636047) B2636047
theorem B4621769 : Blo 810345 4621769 := bstep (se 2 (by rfl) ⟨1733163, by rfl⟩ : syracuseStep 4621769 = 3466327) B3466327
theorem B1541729 : Blo 810345 1541729 := bstep (se 2 (by rfl) ⟨578148, by rfl⟩ : syracuseStep 1541729 = 1156297) B1156297
theorem B7800619 : Blo 810345 7800619 := bstep (se 1 (by rfl) ⟨5850464, by rfl⟩ : syracuseStep 7800619 = 11700929) B11700929
theorem B10389343 : Blo 810345 10389343 := bstep (se 1 (by rfl) ⟨7792007, by rfl⟩ : syracuseStep 10389343 = 15584015) B15584015
theorem B2197343 : Blo 810345 2197343 := bstep (se 1 (by rfl) ⟨1648007, by rfl⟩ : syracuseStep 2197343 = 3296015) B3296015
theorem B1542071 : Blo 810345 1542071 := bstep (se 1 (by rfl) ⟨1156553, by rfl⟩ : syracuseStep 1542071 = 2313107) B2313107
theorem B9865223 : Blo 810345 9865223 := bstep (se 1 (by rfl) ⟨7398917, by rfl⟩ : syracuseStep 9865223 = 14797835) B14797835
theorem B3082319 : Blo 810345 3082319 := bstep (se 1 (by rfl) ⟨2311739, by rfl⟩ : syracuseStep 3082319 = 4623479) B4623479
theorem B1738999 : Blo 810345 1738999 := bstep (se 1 (by rfl) ⟨1304249, by rfl⟩ : syracuseStep 1738999 = 2608499) B2608499
theorem B1542473 : Blo 810345 1542473 := bstep (se 2 (by rfl) ⟨578427, by rfl⟩ : syracuseStep 1542473 = 1156855) B1156855
theorem B106597387 : Blo 810345 106597387 := bstep (se 1 (by rfl) ⟨79948040, by rfl⟩ : syracuseStep 106597387 = 159896081) B159896081
theorem B1543187 : Blo 810345 1543187 := bstep (se 1 (by rfl) ⟨1157390, by rfl⟩ : syracuseStep 1543187 = 2314781) B2314781
theorem B1215527 : Blo 810345 1215527 := bstep (se 1 (by rfl) ⟨911645, by rfl⟩ : syracuseStep 1215527 = 1823291) B1823291
theorem B1543225 : Blo 810345 1543225 := bstep (se 2 (by rfl) ⟨578709, by rfl⟩ : syracuseStep 1543225 = 1157419) B1157419
theorem B1215611 : Blo 810345 1215611 := bstep (se 1 (by rfl) ⟨911708, by rfl⟩ : syracuseStep 1215611 = 1823417) B1823417
theorem B1215737 : Blo 810345 1215737 := bstep (se 2 (by rfl) ⟨455901, by rfl⟩ : syracuseStep 1215737 = 911803) B911803
theorem B9375011 : Blo 810345 9375011 := bstep (se 1 (by rfl) ⟨7031258, by rfl⟩ : syracuseStep 9375011 = 14062517) B14062517
theorem B1215839 : Blo 810345 1215839 := bstep (se 1 (by rfl) ⟨911879, by rfl⟩ : syracuseStep 1215839 = 1823759) B1823759
theorem B1543529 : Blo 810345 1543529 := bstep (se 2 (by rfl) ⟨578823, by rfl⟩ : syracuseStep 1543529 = 1157647) B1157647
theorem B1215851 : Blo 810345 1215851 := bstep (se 1 (by rfl) ⟨911888, by rfl⟩ : syracuseStep 1215851 = 1823777) B1823777
theorem B4623911 : Blo 810345 4623911 := bstep (se 1 (by rfl) ⟨3467933, by rfl⟩ : syracuseStep 4623911 = 6935867) B6935867
theorem B1216079 : Blo 810345 1216079 := bstep (se 1 (by rfl) ⟨912059, by rfl⟩ : syracuseStep 1216079 = 1824119) B1824119
theorem B1216199 : Blo 810345 1216199 := bstep (se 1 (by rfl) ⟨912149, by rfl⟩ : syracuseStep 1216199 = 1824299) B1824299
theorem B5213945 : Blo 810345 5213945 := bstep (se 2 (by rfl) ⟨1955229, by rfl⟩ : syracuseStep 5213945 = 3910459) B3910459
theorem B823079 : Blo 810345 823079 := bstep (se 1 (by rfl) ⟨617309, by rfl⟩ : syracuseStep 823079 = 1234619) B1234619
theorem B1216361 : Blo 810345 1216361 := bstep (se 2 (by rfl) ⟨456135, by rfl⟩ : syracuseStep 1216361 = 912271) B912271
theorem B1216439 : Blo 810345 1216439 := bstep (se 1 (by rfl) ⟨912329, by rfl⟩ : syracuseStep 1216439 = 1824659) B1824659
theorem B1216475 : Blo 810345 1216475 := bstep (se 1 (by rfl) ⟨912356, by rfl⟩ : syracuseStep 1216475 = 1824713) B1824713
theorem B1216943 : Blo 810345 1216943 := bstep (se 1 (by rfl) ⟨912707, by rfl⟩ : syracuseStep 1216943 = 1825415) B1825415
theorem B3084763 : Blo 810345 3084763 := bstep (se 1 (by rfl) ⟨2313572, by rfl⟩ : syracuseStep 3084763 = 4627145) B4627145
theorem B1217033 : Blo 810345 1217033 := bstep (se 2 (by rfl) ⟨456387, by rfl⟩ : syracuseStep 1217033 = 912775) B912775
theorem B3478049 : Blo 810345 3478049 := bstep (se 2 (by rfl) ⟨1304268, by rfl⟩ : syracuseStep 3478049 = 2608537) B2608537
theorem B1217063 : Blo 810345 1217063 := bstep (se 1 (by rfl) ⟨912797, by rfl⟩ : syracuseStep 1217063 = 1825595) B1825595
theorem B1217147 : Blo 810345 1217147 := bstep (se 1 (by rfl) ⟨912860, by rfl⟩ : syracuseStep 1217147 = 1825721) B1825721
theorem B1544827 : Blo 810345 1544827 := bstep (se 1 (by rfl) ⟨1158620, by rfl⟩ : syracuseStep 1544827 = 2317241) B2317241
theorem B6689465 : Blo 810345 6689465 := bstep (se 2 (by rfl) ⟨2508549, by rfl⟩ : syracuseStep 6689465 = 5017099) B5017099
theorem B1544903 : Blo 810345 1544903 := bstep (se 1 (by rfl) ⟨1158677, by rfl⟩ : syracuseStep 1544903 = 2317355) B2317355
theorem B1217273 : Blo 810345 1217273 := bstep (se 2 (by rfl) ⟨456477, by rfl⟩ : syracuseStep 1217273 = 912955) B912955
theorem B1217375 : Blo 810345 1217375 := bstep (se 1 (by rfl) ⟨913031, by rfl⟩ : syracuseStep 1217375 = 1826063) B1826063
theorem B1217387 : Blo 810345 1217387 := bstep (se 1 (by rfl) ⟨913040, by rfl⟩ : syracuseStep 1217387 = 1826081) B1826081
theorem B6165395 : Blo 810345 6165395 := bstep (se 1 (by rfl) ⟨4624046, by rfl⟩ : syracuseStep 6165395 = 9248093) B9248093
theorem B9868337 : Blo 810345 9868337 := bstep (se 2 (by rfl) ⟨3700626, by rfl⟩ : syracuseStep 9868337 = 7401253) B7401253
theorem B1217615 : Blo 810345 1217615 := bstep (se 1 (by rfl) ⟨913211, by rfl⟩ : syracuseStep 1217615 = 1826423) B1826423
theorem B1545313 : Blo 810345 1545313 := bstep (se 2 (by rfl) ⟨579492, by rfl⟩ : syracuseStep 1545313 = 1158985) B1158985
theorem B1217735 : Blo 810345 1217735 := bstep (se 1 (by rfl) ⟨913301, by rfl⟩ : syracuseStep 1217735 = 1826603) B1826603
theorem B4625687 : Blo 810345 4625687 := bstep (se 1 (by rfl) ⟨3469265, by rfl⟩ : syracuseStep 4625687 = 6938531) B6938531
theorem B1217897 : Blo 810345 1217897 := bstep (se 2 (by rfl) ⟨456711, by rfl⟩ : syracuseStep 1217897 = 913423) B913423
theorem B1217975 : Blo 810345 1217975 := bstep (se 1 (by rfl) ⟨913481, by rfl⟩ : syracuseStep 1217975 = 1826963) B1826963
theorem B1545655 : Blo 810345 1545655 := bstep (se 1 (by rfl) ⟨1159241, by rfl⟩ : syracuseStep 1545655 = 2318483) B2318483
theorem B53450189 : Blo 810345 53450189 := bstep (se 3 (by rfl) ⟨10021910, by rfl⟩ : syracuseStep 53450189 = 20043821) B20043821
theorem B1218011 : Blo 810345 1218011 := bstep (se 1 (by rfl) ⟨913508, by rfl⟩ : syracuseStep 1218011 = 1827017) B1827017
theorem B2921993 : Blo 810345 2921993 := bstep (se 2 (by rfl) ⟨1095747, by rfl⟩ : syracuseStep 2921993 = 2191495) B2191495
theorem B3086009 : Blo 810345 3086009 := bstep (se 2 (by rfl) ⟨1157253, by rfl⟩ : syracuseStep 3086009 = 2314507) B2314507
theorem B3086039 : Blo 810345 3086039 := bstep (se 1 (by rfl) ⟨2314529, by rfl⟩ : syracuseStep 3086039 = 4629059) B4629059
theorem B6166367 : Blo 810345 6166367 := bstep (se 1 (by rfl) ⟨4624775, by rfl⟩ : syracuseStep 6166367 = 9249551) B9249551
theorem B1218479 : Blo 810345 1218479 := bstep (se 1 (by rfl) ⟨913859, by rfl⟩ : syracuseStep 1218479 = 1827719) B1827719
theorem B1218569 : Blo 810345 1218569 := bstep (se 2 (by rfl) ⟨456963, by rfl⟩ : syracuseStep 1218569 = 913927) B913927
theorem B1218599 : Blo 810345 1218599 := bstep (se 1 (by rfl) ⟨913949, by rfl⟩ : syracuseStep 1218599 = 1827899) B1827899
theorem B3348559 : Blo 810345 3348559 := bstep (se 1 (by rfl) ⟨2511419, by rfl⟩ : syracuseStep 3348559 = 5022839) B5022839
theorem B3905617 : Blo 810345 3905617 := bstep (se 2 (by rfl) ⟨1464606, by rfl⟩ : syracuseStep 3905617 = 2929213) B2929213
theorem B3119219 : Blo 810345 3119219 := bstep (se 1 (by rfl) ⟨2339414, by rfl⟩ : syracuseStep 3119219 = 4678829) B4678829
theorem B1218683 : Blo 810345 1218683 := bstep (se 1 (by rfl) ⟨914012, by rfl⟩ : syracuseStep 1218683 = 1828025) B1828025
theorem B1218809 : Blo 810345 1218809 := bstep (se 2 (by rfl) ⟨457053, by rfl⟩ : syracuseStep 1218809 = 914107) B914107
theorem B4102487 : Blo 810345 4102487 := bstep (se 1 (by rfl) ⟨3076865, by rfl⟩ : syracuseStep 4102487 = 6153731) B6153731
theorem B1218911 : Blo 810345 1218911 := bstep (se 1 (by rfl) ⟨914183, by rfl⟩ : syracuseStep 1218911 = 1828367) B1828367
theorem B1218923 : Blo 810345 1218923 := bstep (se 1 (by rfl) ⟨914192, by rfl⟩ : syracuseStep 1218923 = 1828385) B1828385
theorem B1219151 : Blo 810345 1219151 := bstep (se 1 (by rfl) ⟨914363, by rfl⟩ : syracuseStep 1219151 = 1828727) B1828727
theorem B1219271 : Blo 810345 1219271 := bstep (se 1 (by rfl) ⟨914453, by rfl⟩ : syracuseStep 1219271 = 1828907) B1828907
theorem B12491597 : Blo 810345 12491597 := bstep (se 3 (by rfl) ⟨2342174, by rfl⟩ : syracuseStep 12491597 = 4684349) B4684349
theorem B1219433 : Blo 810345 1219433 := bstep (se 2 (by rfl) ⟨457287, by rfl⟩ : syracuseStep 1219433 = 914575) B914575
theorem B1219511 : Blo 810345 1219511 := bstep (se 1 (by rfl) ⟨914633, by rfl⟩ : syracuseStep 1219511 = 1829267) B1829267
theorem B1219547 : Blo 810345 1219547 := bstep (se 1 (by rfl) ⟨914660, by rfl⟩ : syracuseStep 1219547 = 1829321) B1829321
theorem B2465149 : Blo 810345 2465149 := bstep (se 3 (by rfl) ⟨462215, by rfl⟩ : syracuseStep 2465149 = 924431) B924431
theorem B1220015 : Blo 810345 1220015 := bstep (se 1 (by rfl) ⟨915011, by rfl⟩ : syracuseStep 1220015 = 1830023) B1830023
theorem B1220105 : Blo 810345 1220105 := bstep (se 2 (by rfl) ⟨457539, by rfl⟩ : syracuseStep 1220105 = 915079) B915079
theorem B1220135 : Blo 810345 1220135 := bstep (se 1 (by rfl) ⟨915101, by rfl⟩ : syracuseStep 1220135 = 1830203) B1830203
theorem B9379451 : Blo 810345 9379451 := bstep (se 1 (by rfl) ⟨7034588, by rfl⟩ : syracuseStep 9379451 = 14069177) B14069177
theorem B1220219 : Blo 810345 1220219 := bstep (se 1 (by rfl) ⟨915164, by rfl⟩ : syracuseStep 1220219 = 1830329) B1830329
theorem B4398731 : Blo 810345 4398731 := bstep (se 1 (by rfl) ⟨3299048, by rfl⟩ : syracuseStep 4398731 = 6598097) B6598097
theorem B4169465 : Blo 810345 4169465 := bstep (se 2 (by rfl) ⟨1563549, by rfl⟩ : syracuseStep 4169465 = 3127099) B3127099
theorem B1220345 : Blo 810345 1220345 := bstep (se 2 (by rfl) ⟨457629, by rfl⟩ : syracuseStep 1220345 = 915259) B915259
theorem B1220447 : Blo 810345 1220447 := bstep (se 1 (by rfl) ⟨915335, by rfl⟩ : syracuseStep 1220447 = 1830671) B1830671
theorem B1220459 : Blo 810345 1220459 := bstep (se 1 (by rfl) ⟨915344, by rfl⟩ : syracuseStep 1220459 = 1830689) B1830689
theorem B1220687 : Blo 810345 1220687 := bstep (se 1 (by rfl) ⟨915515, by rfl⟩ : syracuseStep 1220687 = 1831031) B1831031
theorem B2597017 : Blo 810345 2597017 := bstep (se 2 (by rfl) ⟨973881, by rfl⟩ : syracuseStep 2597017 = 1947763) B1947763
theorem B1220807 : Blo 810345 1220807 := bstep (se 1 (by rfl) ⟨915605, by rfl⟩ : syracuseStep 1220807 = 1831211) B1831211
theorem B2597131 : Blo 810345 2597131 := bstep (se 1 (by rfl) ⟨1947848, by rfl⟩ : syracuseStep 2597131 = 3895697) B3895697
theorem B3088651 : Blo 810345 3088651 := bstep (se 1 (by rfl) ⟨2316488, by rfl⟩ : syracuseStep 3088651 = 4632977) B4632977
theorem B11739451 : Blo 810345 11739451 := bstep (se 1 (by rfl) ⟨8804588, by rfl⟩ : syracuseStep 11739451 = 17609177) B17609177
theorem B1220969 : Blo 810345 1220969 := bstep (se 2 (by rfl) ⟨457863, by rfl⟩ : syracuseStep 1220969 = 915727) B915727
theorem B1221047 : Blo 810345 1221047 := bstep (se 1 (by rfl) ⟨915785, by rfl⟩ : syracuseStep 1221047 = 1831571) B1831571
theorem B1221083 : Blo 810345 1221083 := bstep (se 1 (by rfl) ⟨915812, by rfl⟩ : syracuseStep 1221083 = 1831625) B1831625
theorem B3711521 : Blo 810345 3711521 := bstep (se 2 (by rfl) ⟨1391820, by rfl⟩ : syracuseStep 3711521 = 2783641) B2783641
theorem B3088955 : Blo 810345 3088955 := bstep (se 1 (by rfl) ⟨2316716, by rfl⟩ : syracuseStep 3088955 = 4633433) B4633433
theorem B2925683 : Blo 810345 2925683 := bstep (se 1 (by rfl) ⟨2194262, by rfl⟩ : syracuseStep 2925683 = 4388525) B4388525
theorem B5547437 : Blo 810345 5547437 := bstep (se 3 (by rfl) ⟨1040144, by rfl⟩ : syracuseStep 5547437 = 2080289) B2080289
theorem B6661577 : Blo 810345 6661577 := bstep (se 2 (by rfl) ⟨2498091, by rfl⟩ : syracuseStep 6661577 = 4996183) B4996183
theorem B3090109 : Blo 810345 3090109 := bstep (se 3 (by rfl) ⟨579395, by rfl⟩ : syracuseStep 3090109 = 1158791) B1158791
theorem B4106051 : Blo 810345 4106051 := bstep (se 1 (by rfl) ⟨3079538, by rfl⟩ : syracuseStep 4106051 = 6159077) B6159077
theorem B1386553 : Blo 810345 1386553 := bstep (se 2 (by rfl) ⟨519957, by rfl⟩ : syracuseStep 1386553 = 1039915) B1039915
theorem B1648811 : Blo 810345 1648811 := bstep (se 1 (by rfl) ⟨1236608, by rfl⟩ : syracuseStep 1648811 = 2473217) B2473217
theorem B1026523 : Blo 810345 1026523 := bstep (se 1 (by rfl) ⟨769892, by rfl⟩ : syracuseStep 1026523 = 1539785) B1539785
theorem B1157755 : Blo 810345 1157755 := bstep (se 1 (by rfl) ⟨868316, by rfl⟩ : syracuseStep 1157755 = 1736633) B1736633
theorem B3091067 : Blo 810345 3091067 := bstep (se 1 (by rfl) ⟨2318300, by rfl⟩ : syracuseStep 3091067 = 4636601) B4636601
theorem B2599951 : Blo 810345 2599951 := bstep (se 1 (by rfl) ⟨1949963, by rfl⟩ : syracuseStep 2599951 = 3899927) B3899927
theorem B2600093 : Blo 810345 2600093 := bstep (se 3 (by rfl) ⟨487517, by rfl⟩ : syracuseStep 2600093 = 975035) B975035
theorem B2928001 : Blo 810345 2928001 := bstep (se 2 (by rfl) ⟨1098000, by rfl⟩ : syracuseStep 2928001 = 2196001) B2196001
theorem B3091841 : Blo 810345 3091841 := bstep (se 2 (by rfl) ⟨1159440, by rfl⟩ : syracuseStep 3091841 = 2318881) B2318881
theorem B8793517 : Blo 810345 8793517 := bstep (se 3 (by rfl) ⟨1648784, by rfl⟩ : syracuseStep 8793517 = 3297569) B3297569
theorem B6172199 : Blo 810345 6172199 := bstep (se 1 (by rfl) ⟨4629149, by rfl⟩ : syracuseStep 6172199 = 9258299) B9258299
theorem B6598381 : Blo 810345 6598381 := bstep (se 3 (by rfl) ⟨1237196, by rfl⟩ : syracuseStep 6598381 = 2474393) B2474393
theorem B1158905 : Blo 810345 1158905 := bstep (se 2 (by rfl) ⟨434589, by rfl⟩ : syracuseStep 1158905 = 869179) B869179
theorem B3288941 : Blo 810345 3288941 := bstep (se 3 (by rfl) ⟨616676, by rfl⟩ : syracuseStep 3288941 = 1233353) B1233353
theorem B13152131 : Blo 810345 13152131 := bstep (se 1 (by rfl) ⟨9864098, by rfl⟩ : syracuseStep 13152131 = 19728197) B19728197
theorem B11120755 : Blo 810345 11120755 := bstep (se 1 (by rfl) ⟨8340566, by rfl⟩ : syracuseStep 11120755 = 16681133) B16681133
theorem B2928797 : Blo 810345 2928797 := bstep (se 3 (by rfl) ⟨549149, by rfl⟩ : syracuseStep 2928797 = 1098299) B1098299
theorem B3289625 : Blo 810345 3289625 := bstep (se 2 (by rfl) ⟨1233609, by rfl⟩ : syracuseStep 3289625 = 2467219) B2467219
theorem B6599227 : Blo 810345 6599227 := bstep (se 1 (by rfl) ⟨4949420, by rfl⟩ : syracuseStep 6599227 = 9898841) B9898841
theorem B4109129 : Blo 810345 4109129 := bstep (se 2 (by rfl) ⟨1540923, by rfl⟩ : syracuseStep 4109129 = 3081847) B3081847
theorem B1389487 : Blo 810345 1389487 := bstep (se 1 (by rfl) ⟨1042115, by rfl⟩ : syracuseStep 1389487 = 2084231) B2084231
theorem B5551183 : Blo 810345 5551183 := bstep (se 1 (by rfl) ⟨4163387, by rfl⟩ : syracuseStep 5551183 = 8326775) B8326775
theorem B3519683 : Blo 810345 3519683 := bstep (se 1 (by rfl) ⟨2639762, by rfl⟩ : syracuseStep 3519683 = 5279525) B5279525
theorem B160281827 : Blo 810345 160281827 := bstep (se 1 (by rfl) ⟨120211370, by rfl⟩ : syracuseStep 160281827 = 240422741) B240422741
theorem B4634435 : Blo 810345 4634435 := bstep (se 1 (by rfl) ⟨3475826, by rfl⟩ : syracuseStep 4634435 = 6951653) B6951653
theorem B2930539 : Blo 810345 2930539 := bstep (se 1 (by rfl) ⟨2197904, by rfl⟩ : syracuseStep 2930539 = 4395809) B4395809
theorem B5552059 : Blo 810345 5552059 := bstep (se 1 (by rfl) ⟨4164044, by rfl⟩ : syracuseStep 5552059 = 8328089) B8328089
theorem B4110425 : Blo 810345 4110425 := bstep (se 2 (by rfl) ⟨1541409, by rfl⟩ : syracuseStep 4110425 = 3082819) B3082819
theorem B4634891 : Blo 810345 4634891 := bstep (se 1 (by rfl) ⟨3476168, by rfl⟩ : syracuseStep 4634891 = 6952337) B6952337
theorem B10008937 : Blo 810345 10008937 := bstep (se 2 (by rfl) ⟨3753351, by rfl⟩ : syracuseStep 10008937 = 7506703) B7506703
theorem B1030583 : Blo 810345 1030583 := bstep (se 1 (by rfl) ⟨772937, by rfl⟩ : syracuseStep 1030583 = 1545875) B1545875
theorem B7027181 : Blo 810345 7027181 := bstep (se 3 (by rfl) ⟨1317596, by rfl⟩ : syracuseStep 7027181 = 2635193) B2635193
theorem B10566389 : Blo 810345 10566389 := bstep (se 5 (by rfl) ⟨495299, by rfl⟩ : syracuseStep 10566389 = 990599) B990599
theorem B4635575 : Blo 810345 4635575 := bstep (se 1 (by rfl) ⟨3476681, by rfl⟩ : syracuseStep 4635575 = 6953363) B6953363
theorem B2735261 : Blo 810345 2735261 := bstep (se 3 (by rfl) ⟨512861, by rfl⟩ : syracuseStep 2735261 = 1025723) B1025723
theorem B3128701 : Blo 810345 3128701 := bstep (se 3 (by rfl) ⟨586631, by rfl⟩ : syracuseStep 3128701 = 1173263) B1173263
theorem B2735801 : Blo 810345 2735801 := bstep (se 2 (by rfl) ⟨1025925, by rfl⟩ : syracuseStep 2735801 = 2051851) B2051851
theorem B4636349 : Blo 810345 4636349 := bstep (se 3 (by rfl) ⟨869315, by rfl⟩ : syracuseStep 4636349 = 1738631) B1738631
theorem B2736395 : Blo 810345 2736395 := bstep (se 1 (by rfl) ⟨2052296, by rfl⟩ : syracuseStep 2736395 = 4104593) B4104593
theorem B171524405 : Blo 810345 171524405 := bstep (se 5 (by rfl) ⟨8040206, by rfl⟩ : syracuseStep 171524405 = 16080413) B16080413
theorem B4637033 : Blo 810345 4637033 := bstep (se 2 (by rfl) ⟨1738887, by rfl⟩ : syracuseStep 4637033 = 3477775) B3477775
theorem B2736665 : Blo 810345 2736665 := bstep (se 2 (by rfl) ⟨1026249, by rfl⟩ : syracuseStep 2736665 = 2052499) B2052499
theorem B2081305 : Blo 810345 2081305 := bstep (se 2 (by rfl) ⟨780489, by rfl⟩ : syracuseStep 2081305 = 1560979) B1560979
theorem B24986231 : Blo 810345 24986231 := bstep (se 1 (by rfl) ⟨18739673, by rfl⟩ : syracuseStep 24986231 = 37479347) B37479347
theorem B5554889 : Blo 810345 5554889 := bstep (se 2 (by rfl) ⟨2083083, by rfl⟩ : syracuseStep 5554889 = 4166167) B4166167
theorem B3293905 : Blo 810345 3293905 := bstep (se 2 (by rfl) ⟨1235214, by rfl⟩ : syracuseStep 3293905 = 2470429) B2470429
theorem B2933767 : Blo 810345 2933767 := bstep (se 1 (by rfl) ⟨2200325, by rfl⟩ : syracuseStep 2933767 = 4400651) B4400651
theorem B6243481 : Blo 810345 6243481 := bstep (se 2 (by rfl) ⟨2341305, by rfl⟩ : syracuseStep 6243481 = 4682611) B4682611
theorem B3130919 : Blo 810345 3130919 := bstep (se 1 (by rfl) ⟨2348189, by rfl⟩ : syracuseStep 3130919 = 4696379) B4696379
theorem B2737799 : Blo 810345 2737799 := bstep (se 1 (by rfl) ⟨2053349, by rfl⟩ : syracuseStep 2737799 = 4106699) B4106699
theorem B2475659 : Blo 810345 2475659 := bstep (se 1 (by rfl) ⟨1856744, by rfl⟩ : syracuseStep 2475659 = 3713489) B3713489
theorem B2737853 : Blo 810345 2737853 := bstep (se 3 (by rfl) ⟨513347, by rfl⟩ : syracuseStep 2737853 = 1026695) B1026695
theorem B2738015 : Blo 810345 2738015 := bstep (se 1 (by rfl) ⟨2053511, by rfl⟩ : syracuseStep 2738015 = 4107023) B4107023
theorem B2738177 : Blo 810345 2738177 := bstep (se 2 (by rfl) ⟨1026816, by rfl⟩ : syracuseStep 2738177 = 2053633) B2053633
theorem B5851217 : Blo 810345 5851217 := bstep (se 2 (by rfl) ⟨2194206, by rfl⟩ : syracuseStep 5851217 = 4388413) B4388413
theorem B4933975 : Blo 810345 4933975 := bstep (se 1 (by rfl) ⟨3700481, by rfl⟩ : syracuseStep 4933975 = 7400963) B7400963
theorem B2673001 : Blo 810345 2673001 := bstep (se 2 (by rfl) ⟨1002375, by rfl⟩ : syracuseStep 2673001 = 2004751) B2004751
theorem B2640595 : Blo 810345 2640595 := bstep (se 1 (by rfl) ⟨1980446, by rfl⟩ : syracuseStep 2640595 = 3960893) B3960893
theorem B2738987 : Blo 810345 2738987 := bstep (se 1 (by rfl) ⟨2054240, by rfl⟩ : syracuseStep 2738987 = 4108481) B4108481
theorem B2739257 : Blo 810345 2739257 := bstep (se 2 (by rfl) ⟨1027221, by rfl⟩ : syracuseStep 2739257 = 2054443) B2054443
theorem B4115609 : Blo 810345 4115609 := bstep (se 2 (by rfl) ⟨1543353, by rfl⟩ : syracuseStep 4115609 = 3086707) B3086707
theorem B2739581 : Blo 810345 2739581 := bstep (se 3 (by rfl) ⟨513671, by rfl⟩ : syracuseStep 2739581 = 1027343) B1027343
theorem B2739851 : Blo 810345 2739851 := bstep (se 1 (by rfl) ⟨2054888, by rfl⟩ : syracuseStep 2739851 = 4109777) B4109777
theorem B2772911 : Blo 810345 2772911 := bstep (se 1 (by rfl) ⟨2079683, by rfl⟩ : syracuseStep 2772911 = 4159367) B4159367
theorem B2052175 : Blo 810345 2052175 := bstep (se 1 (by rfl) ⟨1539131, by rfl⟩ : syracuseStep 2052175 = 3078263) B3078263
theorem B1954039 : Blo 810345 1954039 := bstep (se 1 (by rfl) ⟨1465529, by rfl⟩ : syracuseStep 1954039 = 2931059) B2931059
theorem B1954153 : Blo 810345 1954153 := bstep (se 2 (by rfl) ⟨732807, by rfl⟩ : syracuseStep 1954153 = 1465615) B1465615
theorem B2740769 : Blo 810345 2740769 := bstep (se 2 (by rfl) ⟨1027788, by rfl⟩ : syracuseStep 2740769 = 2055577) B2055577
theorem B2052823 : Blo 810345 2052823 := bstep (se 1 (by rfl) ⟨1539617, by rfl⟩ : syracuseStep 2052823 = 3079235) B3079235
theorem B2740985 : Blo 810345 2740985 := bstep (se 2 (by rfl) ⟨1027869, by rfl⟩ : syracuseStep 2740985 = 2055739) B2055739
theorem B1823561 : Blo 810345 1823561 := bstep (se 2 (by rfl) ⟨683835, by rfl⟩ : syracuseStep 1823561 = 1367671) B1367671
theorem B1954655 : Blo 810345 1954655 := bstep (se 1 (by rfl) ⟨1465991, by rfl⟩ : syracuseStep 1954655 = 2931983) B2931983
theorem B2053127 : Blo 810345 2053127 := bstep (se 1 (by rfl) ⟨1539845, by rfl⟩ : syracuseStep 2053127 = 3079691) B3079691
theorem B2741255 : Blo 810345 2741255 := bstep (se 1 (by rfl) ⟨2055941, by rfl⟩ : syracuseStep 2741255 = 4111883) B4111883
theorem B2741363 : Blo 810345 2741363 := bstep (se 1 (by rfl) ⟨2056022, by rfl⟩ : syracuseStep 2741363 = 4112045) B4112045
theorem B1299655 : Blo 810345 1299655 := bstep (se 1 (by rfl) ⟨974741, by rfl⟩ : syracuseStep 1299655 = 1949483) B1949483
theorem B2741633 : Blo 810345 2741633 := bstep (se 2 (by rfl) ⟨1028112, by rfl⟩ : syracuseStep 2741633 = 2056225) B2056225
theorem B1824353 : Blo 810345 1824353 := bstep (se 2 (by rfl) ⟨684132, by rfl⟩ : syracuseStep 1824353 = 1368265) B1368265
theorem B2774663 : Blo 810345 2774663 := bstep (se 1 (by rfl) ⟨2080997, by rfl⟩ : syracuseStep 2774663 = 4161995) B4161995
theorem B2315965 : Blo 810345 2315965 := bstep (se 3 (by rfl) ⟨434243, by rfl⟩ : syracuseStep 2315965 = 868487) B868487
theorem B1824695 : Blo 810345 1824695 := bstep (se 1 (by rfl) ⟨1368521, by rfl⟩ : syracuseStep 1824695 = 2737043) B2737043
theorem B2316215 : Blo 810345 2316215 := bstep (se 1 (by rfl) ⟨1737161, by rfl⟩ : syracuseStep 2316215 = 3474323) B3474323
theorem B1300411 : Blo 810345 1300411 := bstep (se 1 (by rfl) ⟨975308, by rfl⟩ : syracuseStep 1300411 = 1950617) B1950617
theorem B2742443 : Blo 810345 2742443 := bstep (se 1 (by rfl) ⟨2056832, by rfl⟩ : syracuseStep 2742443 = 4113665) B4113665
theorem B3463661 : Blo 810345 3463661 := bstep (se 3 (by rfl) ⟨649436, by rfl⟩ : syracuseStep 3463661 = 1298873) B1298873
theorem B7821805 : Blo 810345 7821805 := bstep (se 3 (by rfl) ⟨1466588, by rfl⟩ : syracuseStep 7821805 = 2933177) B2933177
theorem B1825289 : Blo 810345 1825289 := bstep (se 2 (by rfl) ⟨684483, by rfl⟩ : syracuseStep 1825289 = 1368967) B1368967
theorem B1563259 : Blo 810345 1563259 := bstep (se 1 (by rfl) ⟨1172444, by rfl⟩ : syracuseStep 1563259 = 2344889) B2344889
theorem B2742983 : Blo 810345 2742983 := bstep (se 1 (by rfl) ⟨2057237, by rfl⟩ : syracuseStep 2742983 = 4114475) B4114475
theorem B5200595 : Blo 810345 5200595 := bstep (se 1 (by rfl) ⟨3900446, by rfl⟩ : syracuseStep 5200595 = 7800893) B7800893
theorem B1825631 : Blo 810345 1825631 := bstep (se 1 (by rfl) ⟨1369223, by rfl⟩ : syracuseStep 1825631 = 2738447) B2738447
theorem B5200823 : Blo 810345 5200823 := bstep (se 1 (by rfl) ⟨3900617, by rfl⟩ : syracuseStep 5200823 = 7801235) B7801235
theorem B6183863 : Blo 810345 6183863 := bstep (se 1 (by rfl) ⟨4637897, by rfl⟩ : syracuseStep 6183863 = 9275795) B9275795
theorem B1301513 : Blo 810345 1301513 := bstep (se 2 (by rfl) ⟨488067, by rfl⟩ : syracuseStep 1301513 = 976135) B976135
theorem B1825811 : Blo 810345 1825811 := bstep (se 1 (by rfl) ⟨1369358, by rfl⟩ : syracuseStep 1825811 = 2738717) B2738717
theorem B3464345 : Blo 810345 3464345 := bstep (se 2 (by rfl) ⟨1299129, by rfl⟩ : syracuseStep 3464345 = 2598259) B2598259
theorem B2055415 : Blo 810345 2055415 := bstep (se 1 (by rfl) ⟨1541561, by rfl⟩ : syracuseStep 2055415 = 3083123) B3083123
theorem B1826153 : Blo 810345 1826153 := bstep (se 2 (by rfl) ⟨684807, by rfl⟩ : syracuseStep 1826153 = 1369615) B1369615
theorem B2317673 : Blo 810345 2317673 := bstep (se 2 (by rfl) ⟨869127, by rfl⟩ : syracuseStep 2317673 = 1738255) B1738255
theorem B810363 : Blo 810345 810363 := bstep (se 1 (by rfl) ⟨607772, by rfl⟩ : syracuseStep 810363 = 1215545) B1215545
theorem B2317697 : Blo 810345 2317697 := bstep (se 2 (by rfl) ⟨869136, by rfl⟩ : syracuseStep 2317697 = 1738273) B1738273
theorem B810415 : Blo 810345 810415 := bstep (se 1 (by rfl) ⟨607811, by rfl⟩ : syracuseStep 810415 = 1215623) B1215623
theorem B810439 : Blo 810345 810439 := bstep (se 1 (by rfl) ⟨607829, by rfl⟩ : syracuseStep 810439 = 1215659) B1215659
theorem B810459 : Blo 810345 810459 := bstep (se 1 (by rfl) ⟨607844, by rfl⟩ : syracuseStep 810459 = 1215689) B1215689
theorem B2055689 : Blo 810345 2055689 := bstep (se 2 (by rfl) ⟨770883, by rfl⟩ : syracuseStep 2055689 = 1541767) B1541767
theorem B810535 : Blo 810345 810535 := bstep (se 1 (by rfl) ⟨607901, by rfl⟩ : syracuseStep 810535 = 1215803) B1215803
theorem B2055719 : Blo 810345 2055719 := bstep (se 1 (by rfl) ⟨1541789, by rfl⟩ : syracuseStep 2055719 = 3083579) B3083579
theorem B2743847 : Blo 810345 2743847 := bstep (se 1 (by rfl) ⟨2057885, by rfl⟩ : syracuseStep 2743847 = 4115771) B4115771
theorem B810575 : Blo 810345 810575 := bstep (se 1 (by rfl) ⟨607931, by rfl⟩ : syracuseStep 810575 = 1215863) B1215863
theorem B810591 : Blo 810345 810591 := bstep (se 1 (by rfl) ⟨607943, by rfl⟩ : syracuseStep 810591 = 1215887) B1215887
theorem B810619 : Blo 810345 810619 := bstep (se 1 (by rfl) ⟨607964, by rfl⟩ : syracuseStep 810619 = 1215929) B1215929
theorem B2743955 : Blo 810345 2743955 := bstep (se 1 (by rfl) ⟨2057966, by rfl⟩ : syracuseStep 2743955 = 4115933) B4115933
theorem B810671 : Blo 810345 810671 := bstep (se 1 (by rfl) ⟨608003, by rfl⟩ : syracuseStep 810671 = 1216007) B1216007
theorem B810695 : Blo 810345 810695 := bstep (se 1 (by rfl) ⟨608021, by rfl⟩ : syracuseStep 810695 = 1216043) B1216043
theorem B810715 : Blo 810345 810715 := bstep (se 1 (by rfl) ⟨608036, by rfl⟩ : syracuseStep 810715 = 1216073) B1216073
theorem B810791 : Blo 810345 810791 := bstep (se 1 (by rfl) ⟨608093, by rfl⟩ : syracuseStep 810791 = 1216187) B1216187
theorem B810831 : Blo 810345 810831 := bstep (se 1 (by rfl) ⟨608123, by rfl⟩ : syracuseStep 810831 = 1216247) B1216247
theorem B810847 : Blo 810345 810847 := bstep (se 1 (by rfl) ⟨608135, by rfl⟩ : syracuseStep 810847 = 1216271) B1216271
theorem B2056043 : Blo 810345 2056043 := bstep (se 1 (by rfl) ⟨1542032, by rfl⟩ : syracuseStep 2056043 = 3084065) B3084065
theorem B2744171 : Blo 810345 2744171 := bstep (se 1 (by rfl) ⟨2058128, by rfl⟩ : syracuseStep 2744171 = 4116257) B4116257
theorem B810875 : Blo 810345 810875 := bstep (se 1 (by rfl) ⟨608156, by rfl⟩ : syracuseStep 810875 = 1216313) B1216313
theorem B2744225 : Blo 810345 2744225 := bstep (se 2 (by rfl) ⟨1029084, by rfl⟩ : syracuseStep 2744225 = 2058169) B2058169
theorem B810927 : Blo 810345 810927 := bstep (se 1 (by rfl) ⟨608195, by rfl⟩ : syracuseStep 810927 = 1216391) B1216391
theorem B1367995 : Blo 810345 1367995 := bstep (se 1 (by rfl) ⟨1025996, by rfl⟩ : syracuseStep 1367995 = 2051993) B2051993
theorem B1826747 : Blo 810345 1826747 := bstep (se 1 (by rfl) ⟨1370060, by rfl⟩ : syracuseStep 1826747 = 2740121) B2740121
theorem B810951 : Blo 810345 810951 := bstep (se 1 (by rfl) ⟨608213, by rfl⟩ : syracuseStep 810951 = 1216427) B1216427
theorem B810971 : Blo 810345 810971 := bstep (se 1 (by rfl) ⟨608228, by rfl⟩ : syracuseStep 810971 = 1216457) B1216457
theorem B1368103 : Blo 810345 1368103 := bstep (se 1 (by rfl) ⟨1026077, by rfl⟩ : syracuseStep 1368103 = 2052155) B2052155
theorem B811047 : Blo 810345 811047 := bstep (se 1 (by rfl) ⟨608285, by rfl⟩ : syracuseStep 811047 = 1216571) B1216571
theorem B1826873 : Blo 810345 1826873 := bstep (se 2 (by rfl) ⟨685077, by rfl⟩ : syracuseStep 1826873 = 1370155) B1370155
theorem B811087 : Blo 810345 811087 := bstep (se 1 (by rfl) ⟨608315, by rfl⟩ : syracuseStep 811087 = 1216631) B1216631
theorem B811103 : Blo 810345 811103 := bstep (se 1 (by rfl) ⟨608327, by rfl⟩ : syracuseStep 811103 = 1216655) B1216655
theorem B811131 : Blo 810345 811131 := bstep (se 1 (by rfl) ⟨608348, by rfl⟩ : syracuseStep 811131 = 1216697) B1216697
theorem B811183 : Blo 810345 811183 := bstep (se 1 (by rfl) ⟨608387, by rfl⟩ : syracuseStep 811183 = 1216775) B1216775
theorem B811207 : Blo 810345 811207 := bstep (se 1 (by rfl) ⟨608405, by rfl⟩ : syracuseStep 811207 = 1216811) B1216811
theorem B811227 : Blo 810345 811227 := bstep (se 1 (by rfl) ⟨608420, by rfl⟩ : syracuseStep 811227 = 1216841) B1216841
theorem B6578405 : Blo 810345 6578405 := bstep (se 4 (by rfl) ⟨616725, by rfl⟩ : syracuseStep 6578405 = 1233451) B1233451
theorem B811303 : Blo 810345 811303 := bstep (se 1 (by rfl) ⟨608477, by rfl⟩ : syracuseStep 811303 = 1216955) B1216955
theorem B811343 : Blo 810345 811343 := bstep (se 1 (by rfl) ⟨608507, by rfl⟩ : syracuseStep 811343 = 1217015) B1217015
theorem B811359 : Blo 810345 811359 := bstep (se 1 (by rfl) ⟨608519, by rfl⟩ : syracuseStep 811359 = 1217039) B1217039
theorem B1368427 : Blo 810345 1368427 := bstep (se 1 (by rfl) ⟨1026320, by rfl⟩ : syracuseStep 1368427 = 2052641) B2052641
theorem B811387 : Blo 810345 811387 := bstep (se 1 (by rfl) ⟨608540, by rfl⟩ : syracuseStep 811387 = 1217081) B1217081
theorem B1827215 : Blo 810345 1827215 := bstep (se 1 (by rfl) ⟨1370411, by rfl⟩ : syracuseStep 1827215 = 2740823) B2740823
theorem B811439 : Blo 810345 811439 := bstep (se 1 (by rfl) ⟨608579, by rfl⟩ : syracuseStep 811439 = 1217159) B1217159
theorem B811463 : Blo 810345 811463 := bstep (se 1 (by rfl) ⟨608597, by rfl⟩ : syracuseStep 811463 = 1217195) B1217195
theorem B811483 : Blo 810345 811483 := bstep (se 1 (by rfl) ⟨608612, by rfl⟩ : syracuseStep 811483 = 1217225) B1217225
theorem B2056691 : Blo 810345 2056691 := bstep (se 1 (by rfl) ⟨1542518, by rfl⟩ : syracuseStep 2056691 = 3085037) B3085037
theorem B2744819 : Blo 810345 2744819 := bstep (se 1 (by rfl) ⟨2058614, by rfl⟩ : syracuseStep 2744819 = 4117229) B4117229
theorem B811559 : Blo 810345 811559 := bstep (se 1 (by rfl) ⟨608669, by rfl⟩ : syracuseStep 811559 = 1217339) B1217339
theorem B811599 : Blo 810345 811599 := bstep (se 1 (by rfl) ⟨608699, by rfl⟩ : syracuseStep 811599 = 1217399) B1217399
theorem B811615 : Blo 810345 811615 := bstep (se 1 (by rfl) ⟨608711, by rfl⟩ : syracuseStep 811615 = 1217423) B1217423
theorem B811643 : Blo 810345 811643 := bstep (se 1 (by rfl) ⟨608732, by rfl⟩ : syracuseStep 811643 = 1217465) B1217465
theorem B811695 : Blo 810345 811695 := bstep (se 1 (by rfl) ⟨608771, by rfl⟩ : syracuseStep 811695 = 1217543) B1217543
theorem B811719 : Blo 810345 811719 := bstep (se 1 (by rfl) ⟨608789, by rfl⟩ : syracuseStep 811719 = 1217579) B1217579
theorem B1827539 : Blo 810345 1827539 := bstep (se 1 (by rfl) ⟨1370654, by rfl⟩ : syracuseStep 1827539 = 2741309) B2741309
theorem B811739 : Blo 810345 811739 := bstep (se 1 (by rfl) ⟨608804, by rfl⟩ : syracuseStep 811739 = 1217609) B1217609
theorem B5858077 : Blo 810345 5858077 := bstep (se 3 (by rfl) ⟨1098389, by rfl⟩ : syracuseStep 5858077 = 2196779) B2196779
theorem B811815 : Blo 810345 811815 := bstep (se 1 (by rfl) ⟨608861, by rfl⟩ : syracuseStep 811815 = 1217723) B1217723
theorem B811855 : Blo 810345 811855 := bstep (se 1 (by rfl) ⟨608891, by rfl⟩ : syracuseStep 811855 = 1217783) B1217783
theorem B811871 : Blo 810345 811871 := bstep (se 1 (by rfl) ⟨608903, by rfl⟩ : syracuseStep 811871 = 1217807) B1217807
theorem B811899 : Blo 810345 811899 := bstep (se 1 (by rfl) ⟨608924, by rfl⟩ : syracuseStep 811899 = 1217849) B1217849
theorem B811951 : Blo 810345 811951 := bstep (se 1 (by rfl) ⟨608963, by rfl⟩ : syracuseStep 811951 = 1217927) B1217927
theorem B2057147 : Blo 810345 2057147 := bstep (se 1 (by rfl) ⟨1542860, by rfl⟩ : syracuseStep 2057147 = 3085721) B3085721
theorem B102949829 : Blo 810345 102949829 := bstep (se 4 (by rfl) ⟨9651546, by rfl⟩ : syracuseStep 102949829 = 19303093) B19303093
theorem B811975 : Blo 810345 811975 := bstep (se 1 (by rfl) ⟨608981, by rfl⟩ : syracuseStep 811975 = 1217963) B1217963
theorem B811995 : Blo 810345 811995 := bstep (se 1 (by rfl) ⟨608996, by rfl⟩ : syracuseStep 811995 = 1217993) B1217993
theorem B2745359 : Blo 810345 2745359 := bstep (se 1 (by rfl) ⟨2059019, by rfl⟩ : syracuseStep 2745359 = 4118039) B4118039
theorem B3466259 : Blo 810345 3466259 := bstep (se 1 (by rfl) ⟨2599694, by rfl⟩ : syracuseStep 3466259 = 5199389) B5199389
theorem B812071 : Blo 810345 812071 := bstep (se 1 (by rfl) ⟨609053, by rfl⟩ : syracuseStep 812071 = 1218107) B1218107
theorem B812111 : Blo 810345 812111 := bstep (se 1 (by rfl) ⟨609083, by rfl⟩ : syracuseStep 812111 = 1218167) B1218167
theorem B812127 : Blo 810345 812127 := bstep (se 1 (by rfl) ⟨609095, by rfl⟩ : syracuseStep 812127 = 1218191) B1218191
theorem B812155 : Blo 810345 812155 := bstep (se 1 (by rfl) ⟨609116, by rfl⟩ : syracuseStep 812155 = 1218233) B1218233
theorem B812207 : Blo 810345 812207 := bstep (se 1 (by rfl) ⟨609155, by rfl⟩ : syracuseStep 812207 = 1218311) B1218311
theorem B812231 : Blo 810345 812231 := bstep (se 1 (by rfl) ⟨609173, by rfl⟩ : syracuseStep 812231 = 1218347) B1218347
theorem B812251 : Blo 810345 812251 := bstep (se 1 (by rfl) ⟨609188, by rfl⟩ : syracuseStep 812251 = 1218377) B1218377
theorem B812327 : Blo 810345 812327 := bstep (se 1 (by rfl) ⟨609245, by rfl⟩ : syracuseStep 812327 = 1218491) B1218491
theorem B812367 : Blo 810345 812367 := bstep (se 1 (by rfl) ⟨609275, by rfl⟩ : syracuseStep 812367 = 1218551) B1218551
theorem B812383 : Blo 810345 812383 := bstep (se 1 (by rfl) ⟨609287, by rfl⟩ : syracuseStep 812383 = 1218575) B1218575
theorem B812411 : Blo 810345 812411 := bstep (se 1 (by rfl) ⟨609308, by rfl⟩ : syracuseStep 812411 = 1218617) B1218617
theorem B1369487 : Blo 810345 1369487 := bstep (se 1 (by rfl) ⟨1027115, by rfl⟩ : syracuseStep 1369487 = 2054231) B2054231
theorem B812463 : Blo 810345 812463 := bstep (se 1 (by rfl) ⟨609347, by rfl⟩ : syracuseStep 812463 = 1218695) B1218695
theorem B812487 : Blo 810345 812487 := bstep (se 1 (by rfl) ⟨609365, by rfl⟩ : syracuseStep 812487 = 1218731) B1218731
theorem B812507 : Blo 810345 812507 := bstep (se 1 (by rfl) ⟨609380, by rfl⟩ : syracuseStep 812507 = 1218761) B1218761
theorem B9364997 : Blo 810345 9364997 := bstep (se 4 (by rfl) ⟨877968, by rfl⟩ : syracuseStep 9364997 = 1755937) B1755937
theorem B812583 : Blo 810345 812583 := bstep (se 1 (by rfl) ⟨609437, by rfl⟩ : syracuseStep 812583 = 1218875) B1218875
theorem B812623 : Blo 810345 812623 := bstep (se 1 (by rfl) ⟨609467, by rfl⟩ : syracuseStep 812623 = 1218935) B1218935
theorem B812639 : Blo 810345 812639 := bstep (se 1 (by rfl) ⟨609479, by rfl⟩ : syracuseStep 812639 = 1218959) B1218959
theorem B2057825 : Blo 810345 2057825 := bstep (se 2 (by rfl) ⟨771684, by rfl⟩ : syracuseStep 2057825 = 1543369) B1543369
theorem B2745953 : Blo 810345 2745953 := bstep (se 2 (by rfl) ⟨1029732, by rfl⟩ : syracuseStep 2745953 = 2059465) B2059465
theorem B31712867 : Blo 810345 31712867 := bstep (se 1 (by rfl) ⟨23784650, by rfl⟩ : syracuseStep 31712867 = 47569301) B47569301
theorem B1369723 : Blo 810345 1369723 := bstep (se 1 (by rfl) ⟨1027292, by rfl⟩ : syracuseStep 1369723 = 2054585) B2054585
theorem B1828475 : Blo 810345 1828475 := bstep (se 1 (by rfl) ⟨1371356, by rfl⟩ : syracuseStep 1828475 = 2742713) B2742713
theorem B812667 : Blo 810345 812667 := bstep (se 1 (by rfl) ⟨609500, by rfl⟩ : syracuseStep 812667 = 1219001) B1219001
theorem B4122251 : Blo 810345 4122251 := bstep (se 1 (by rfl) ⟨3091688, by rfl⟩ : syracuseStep 4122251 = 6183377) B6183377
theorem B812719 : Blo 810345 812719 := bstep (se 1 (by rfl) ⟨609539, by rfl⟩ : syracuseStep 812719 = 1219079) B1219079
theorem B812743 : Blo 810345 812743 := bstep (se 1 (by rfl) ⟨609557, by rfl⟩ : syracuseStep 812743 = 1219115) B1219115
theorem B812763 : Blo 810345 812763 := bstep (se 1 (by rfl) ⟨609572, by rfl⟩ : syracuseStep 812763 = 1219145) B1219145
theorem B5203693 : Blo 810345 5203693 := bstep (se 3 (by rfl) ⟨975692, by rfl⟩ : syracuseStep 5203693 = 1951385) B1951385
theorem B1828601 : Blo 810345 1828601 := bstep (se 2 (by rfl) ⟨685725, by rfl⟩ : syracuseStep 1828601 = 1371451) B1371451
theorem B812839 : Blo 810345 812839 := bstep (se 1 (by rfl) ⟨609629, by rfl⟩ : syracuseStep 812839 = 1219259) B1219259
theorem B812879 : Blo 810345 812879 := bstep (se 1 (by rfl) ⟨609659, by rfl⟩ : syracuseStep 812879 = 1219319) B1219319
theorem B812895 : Blo 810345 812895 := bstep (se 1 (by rfl) ⟨609671, by rfl⟩ : syracuseStep 812895 = 1219343) B1219343
theorem B812923 : Blo 810345 812923 := bstep (se 1 (by rfl) ⟨609692, by rfl⟩ : syracuseStep 812923 = 1219385) B1219385
theorem B812975 : Blo 810345 812975 := bstep (se 1 (by rfl) ⟨609731, by rfl⟩ : syracuseStep 812975 = 1219463) B1219463
theorem B812999 : Blo 810345 812999 := bstep (se 1 (by rfl) ⟨609749, by rfl⟩ : syracuseStep 812999 = 1219499) B1219499
theorem B813019 : Blo 810345 813019 := bstep (se 1 (by rfl) ⟨609764, by rfl⟩ : syracuseStep 813019 = 1219529) B1219529
theorem B1828871 : Blo 810345 1828871 := bstep (se 1 (by rfl) ⟨1371653, by rfl⟩ : syracuseStep 1828871 = 2743307) B2743307
theorem B813095 : Blo 810345 813095 := bstep (se 1 (by rfl) ⟨609821, by rfl⟩ : syracuseStep 813095 = 1219643) B1219643
theorem B1828943 : Blo 810345 1828943 := bstep (se 1 (by rfl) ⟨1371707, by rfl⟩ : syracuseStep 1828943 = 2743415) B2743415
theorem B813135 : Blo 810345 813135 := bstep (se 1 (by rfl) ⟨609851, by rfl⟩ : syracuseStep 813135 = 1219703) B1219703
theorem B813151 : Blo 810345 813151 := bstep (se 1 (by rfl) ⟨609863, by rfl⟩ : syracuseStep 813151 = 1219727) B1219727
theorem B813179 : Blo 810345 813179 := bstep (se 1 (by rfl) ⟨609884, by rfl⟩ : syracuseStep 813179 = 1219769) B1219769
theorem B126412973 : Blo 810345 126412973 := bstep (se 3 (by rfl) ⟨23702432, by rfl⟩ : syracuseStep 126412973 = 47404865) B47404865
theorem B813231 : Blo 810345 813231 := bstep (se 1 (by rfl) ⟨609923, by rfl⟩ : syracuseStep 813231 = 1219847) B1219847
theorem B813255 : Blo 810345 813255 := bstep (se 1 (by rfl) ⟨609941, by rfl⟩ : syracuseStep 813255 = 1219883) B1219883
theorem B813275 : Blo 810345 813275 := bstep (se 1 (by rfl) ⟨609956, by rfl⟩ : syracuseStep 813275 = 1219913) B1219913
theorem B813351 : Blo 810345 813351 := bstep (se 1 (by rfl) ⟨610013, by rfl⟩ : syracuseStep 813351 = 1220027) B1220027
theorem B813391 : Blo 810345 813391 := bstep (se 1 (by rfl) ⟨610043, by rfl⟩ : syracuseStep 813391 = 1220087) B1220087
theorem B813407 : Blo 810345 813407 := bstep (se 1 (by rfl) ⟨610055, by rfl⟩ : syracuseStep 813407 = 1220111) B1220111
theorem B813435 : Blo 810345 813435 := bstep (se 1 (by rfl) ⟨610076, by rfl⟩ : syracuseStep 813435 = 1220153) B1220153
theorem B6678937 : Blo 810345 6678937 := bstep (se 2 (by rfl) ⟨2504601, by rfl⟩ : syracuseStep 6678937 = 5009203) B5009203
theorem B813487 : Blo 810345 813487 := bstep (se 1 (by rfl) ⟨610115, by rfl⟩ : syracuseStep 813487 = 1220231) B1220231
theorem B813511 : Blo 810345 813511 := bstep (se 1 (by rfl) ⟨610133, by rfl⟩ : syracuseStep 813511 = 1220267) B1220267
theorem B9857483 : Blo 810345 9857483 := bstep (se 1 (by rfl) ⟨7393112, by rfl⟩ : syracuseStep 9857483 = 14786225) B14786225
theorem B1370587 : Blo 810345 1370587 := bstep (se 1 (by rfl) ⟨1027940, by rfl⟩ : syracuseStep 1370587 = 2055881) B2055881
theorem B1829339 : Blo 810345 1829339 := bstep (se 1 (by rfl) ⟨1372004, by rfl⟩ : syracuseStep 1829339 = 2744009) B2744009
theorem B813531 : Blo 810345 813531 := bstep (se 1 (by rfl) ⟨610148, by rfl⟩ : syracuseStep 813531 = 1220297) B1220297
theorem B5204513 : Blo 810345 5204513 := bstep (se 2 (by rfl) ⟨1951692, by rfl⟩ : syracuseStep 5204513 = 3903385) B3903385
theorem B911911 : Blo 810345 911911 := bstep (se 1 (by rfl) ⟨683933, by rfl⟩ : syracuseStep 911911 = 1367867) B1367867
theorem B813607 : Blo 810345 813607 := bstep (se 1 (by rfl) ⟨610205, by rfl⟩ : syracuseStep 813607 = 1220411) B1220411
theorem B813647 : Blo 810345 813647 := bstep (se 1 (by rfl) ⟨610235, by rfl⟩ : syracuseStep 813647 = 1220471) B1220471
theorem B813663 : Blo 810345 813663 := bstep (se 1 (by rfl) ⟨610247, by rfl⟩ : syracuseStep 813663 = 1220495) B1220495
theorem B813691 : Blo 810345 813691 := bstep (se 1 (by rfl) ⟨610268, by rfl⟩ : syracuseStep 813691 = 1220537) B1220537
theorem B813743 : Blo 810345 813743 := bstep (se 1 (by rfl) ⟨610307, by rfl⟩ : syracuseStep 813743 = 1220615) B1220615
theorem B813767 : Blo 810345 813767 := bstep (se 1 (by rfl) ⟨610325, by rfl⟩ : syracuseStep 813767 = 1220651) B1220651
theorem B813787 : Blo 810345 813787 := bstep (se 1 (by rfl) ⟨610340, by rfl⟩ : syracuseStep 813787 = 1220681) B1220681
theorem B813863 : Blo 810345 813863 := bstep (se 1 (by rfl) ⟨610397, by rfl⟩ : syracuseStep 813863 = 1220795) B1220795
theorem B813903 : Blo 810345 813903 := bstep (se 1 (by rfl) ⟨610427, by rfl⟩ : syracuseStep 813903 = 1220855) B1220855
theorem B813919 : Blo 810345 813919 := bstep (se 1 (by rfl) ⟨610439, by rfl⟩ : syracuseStep 813919 = 1220879) B1220879
theorem B813947 : Blo 810345 813947 := bstep (se 1 (by rfl) ⟨610460, by rfl⟩ : syracuseStep 813947 = 1220921) B1220921
theorem B1829807 : Blo 810345 1829807 := bstep (se 1 (by rfl) ⟨1372355, by rfl⟩ : syracuseStep 1829807 = 2744711) B2744711
theorem B813999 : Blo 810345 813999 := bstep (se 1 (by rfl) ⟨610499, by rfl⟩ : syracuseStep 813999 = 1220999) B1220999
theorem B814023 : Blo 810345 814023 := bstep (se 1 (by rfl) ⟨610517, by rfl⟩ : syracuseStep 814023 = 1221035) B1221035
theorem B814043 : Blo 810345 814043 := bstep (se 1 (by rfl) ⟨610532, by rfl⟩ : syracuseStep 814043 = 1221065) B1221065
theorem B22866961 : Blo 810345 22866961 := bstep (se 2 (by rfl) ⟨8575110, by rfl⟩ : syracuseStep 22866961 = 17150221) B17150221
theorem B2059283 : Blo 810345 2059283 := bstep (se 1 (by rfl) ⟨1544462, by rfl⟩ : syracuseStep 2059283 = 3088925) B3088925
theorem B2747411 : Blo 810345 2747411 := bstep (se 1 (by rfl) ⟨2060558, by rfl⟩ : syracuseStep 2747411 = 4121117) B4121117
theorem B814119 : Blo 810345 814119 := bstep (se 1 (by rfl) ⟨610589, by rfl⟩ : syracuseStep 814119 = 1221179) B1221179
theorem B1371215 : Blo 810345 1371215 := bstep (se 1 (by rfl) ⟨1028411, by rfl⟩ : syracuseStep 1371215 = 2056823) B2056823
theorem B814159 : Blo 810345 814159 := bstep (se 1 (by rfl) ⟨610619, by rfl⟩ : syracuseStep 814159 = 1221239) B1221239
theorem B26405975 : Blo 810345 26405975 := bstep (se 1 (by rfl) ⟨19804481, by rfl⟩ : syracuseStep 26405975 = 39608963) B39608963
theorem B814175 : Blo 810345 814175 := bstep (se 1 (by rfl) ⟨610631, by rfl⟩ : syracuseStep 814175 = 1221263) B1221263
theorem B814203 : Blo 810345 814203 := bstep (se 1 (by rfl) ⟨610652, by rfl⟩ : syracuseStep 814203 = 1221305) B1221305
theorem B1731755 : Blo 810345 1731755 := bstep (se 1 (by rfl) ⟨1298816, by rfl⟩ : syracuseStep 1731755 = 2597633) B2597633
theorem B1830059 : Blo 810345 1830059 := bstep (se 1 (by rfl) ⟨1372544, by rfl⟩ : syracuseStep 1830059 = 2745089) B2745089
theorem B814255 : Blo 810345 814255 := bstep (se 1 (by rfl) ⟨610691, by rfl⟩ : syracuseStep 814255 = 1221383) B1221383
theorem B814279 : Blo 810345 814279 := bstep (se 1 (by rfl) ⟨610709, by rfl⟩ : syracuseStep 814279 = 1221419) B1221419
theorem B814299 : Blo 810345 814299 := bstep (se 1 (by rfl) ⟨610724, by rfl⟩ : syracuseStep 814299 = 1221449) B1221449
theorem B2747735 : Blo 810345 2747735 := bstep (se 1 (by rfl) ⟨2060801, by rfl⟩ : syracuseStep 2747735 = 4121603) B4121603
theorem B2059739 : Blo 810345 2059739 := bstep (se 1 (by rfl) ⟨1544804, by rfl⟩ : syracuseStep 2059739 = 3089609) B3089609
theorem B9858647 : Blo 810345 9858647 := bstep (se 1 (by rfl) ⟨7393985, by rfl⟩ : syracuseStep 9858647 = 14787971) B14787971
theorem B3894929 : Blo 810345 3894929 := bstep (se 2 (by rfl) ⟨1460598, by rfl⟩ : syracuseStep 3894929 = 2921197) B2921197
theorem B1830599 : Blo 810345 1830599 := bstep (se 1 (by rfl) ⟨1372949, by rfl⟩ : syracuseStep 1830599 = 2745899) B2745899
theorem B5861281 : Blo 810345 5861281 := bstep (se 2 (by rfl) ⟨2197980, by rfl⟩ : syracuseStep 5861281 = 4395961) B4395961
theorem B17592227 : Blo 810345 17592227 := bstep (se 1 (by rfl) ⟨13194170, by rfl⟩ : syracuseStep 17592227 = 26388341) B26388341
theorem B1372079 : Blo 810345 1372079 := bstep (se 1 (by rfl) ⟨1029059, by rfl⟩ : syracuseStep 1372079 = 2058119) B2058119
theorem B913531 : Blo 810345 913531 := bstep (se 1 (by rfl) ⟨685148, by rfl⟩ : syracuseStep 913531 = 1370297) B1370297
theorem B1372511 : Blo 810345 1372511 := bstep (se 1 (by rfl) ⟨1029383, by rfl⟩ : syracuseStep 1372511 = 2058767) B2058767
theorem B4452889 : Blo 810345 4452889 := bstep (se 2 (by rfl) ⟨1669833, by rfl⟩ : syracuseStep 4452889 = 3339667) B3339667
theorem B1831463 : Blo 810345 1831463 := bstep (se 1 (by rfl) ⟨1373597, by rfl⟩ : syracuseStep 1831463 = 2747195) B2747195
theorem B913999 : Blo 810345 913999 := bstep (se 1 (by rfl) ⟨685499, by rfl⟩ : syracuseStep 913999 = 1370999) B1370999
theorem B2060923 : Blo 810345 2060923 := bstep (se 1 (by rfl) ⟨1545692, by rfl⟩ : syracuseStep 2060923 = 3091385) B3091385
theorem B6157133 : Blo 810345 6157133 := bstep (se 3 (by rfl) ⟨1154462, by rfl⟩ : syracuseStep 6157133 = 2308925) B2308925
theorem B1831787 : Blo 810345 1831787 := bstep (se 1 (by rfl) ⟨1373840, by rfl⟩ : syracuseStep 1831787 = 2747681) B2747681
theorem B3076973 : Blo 810345 3076973 := bstep (se 3 (by rfl) ⟨576932, by rfl⟩ : syracuseStep 3076973 = 1153865) B1153865
theorem B1373071 : Blo 810345 1373071 := bstep (se 1 (by rfl) ⟨1029803, by rfl⟩ : syracuseStep 1373071 = 2059607) B2059607
theorem B1831841 : Blo 810345 1831841 := bstep (se 2 (by rfl) ⟨686940, by rfl⟩ : syracuseStep 1831841 = 1373881) B1373881
theorem B10548143 : Blo 810345 10548143 := bstep (se 1 (by rfl) ⟨7911107, by rfl⟩ : syracuseStep 10548143 = 15822215) B15822215
theorem B914395 : Blo 810345 914395 := bstep (se 1 (by rfl) ⟨685796, by rfl⟩ : syracuseStep 914395 = 1371593) B1371593
theorem B53310517 : Blo 810345 53310517 := bstep (se 5 (by rfl) ⟨2498930, by rfl⟩ : syracuseStep 53310517 = 4997861) B4997861
theorem B3077291 : Blo 810345 3077291 := bstep (se 1 (by rfl) ⟨2307968, by rfl⟩ : syracuseStep 3077291 = 4615937) B4615937
theorem B1832183 : Blo 810345 1832183 := bstep (se 1 (by rfl) ⟨1374137, by rfl⟩ : syracuseStep 1832183 = 2748275) B2748275
theorem B30078307 : Blo 810345 30078307 := bstep (se 1 (by rfl) ⟨22558730, by rfl⟩ : syracuseStep 30078307 = 45117461) B45117461
theorem B914863 : Blo 810345 914863 := bstep (se 1 (by rfl) ⟨686147, by rfl⟩ : syracuseStep 914863 = 1372295) B1372295
theorem B1373753 : Blo 810345 1373753 := bstep (se 2 (by rfl) ⟨515157, by rfl⟩ : syracuseStep 1373753 = 1030315) B1030315
theorem B5863211 : Blo 810345 5863211 := bstep (se 1 (by rfl) ⟨4397408, by rfl⟩ : syracuseStep 5863211 = 8794817) B8794817
theorem B4618079 : Blo 810345 4618079 := bstep (se 1 (by rfl) ⟨3463559, by rfl⟩ : syracuseStep 4618079 = 6927119) B6927119
theorem B915295 : Blo 810345 915295 := bstep (se 1 (by rfl) ⟨686471, by rfl⟩ : syracuseStep 915295 = 1372943) B1372943
theorem B9402317 : Blo 810345 9402317 := bstep (se 3 (by rfl) ⟨1762934, by rfl⟩ : syracuseStep 9402317 = 3525869) B3525869
theorem B1669177 : Blo 810345 1669177 := bstep (se 2 (by rfl) ⟨625941, by rfl⟩ : syracuseStep 1669177 = 1251883) B1251883
theorem B4618397 : Blo 810345 4618397 := bstep (se 3 (by rfl) ⟨865949, by rfl⟩ : syracuseStep 4618397 = 1731899) B1731899
theorem B915655 : Blo 810345 915655 := bstep (se 1 (by rfl) ⟨686741, by rfl⟩ : syracuseStep 915655 = 1373483) B1373483
theorem B2849377 : Blo 810345 2849377 := bstep (se 2 (by rfl) ⟨1068516, by rfl⟩ : syracuseStep 2849377 = 2137033) B2137033
theorem B1735607 : Blo 810345 1735607 := bstep (se 1 (by rfl) ⟨1301705, by rfl⟩ : syracuseStep 1735607 = 2603411) B2603411
theorem B6159563 : Blo 810345 6159563 := bstep (se 1 (by rfl) ⟨4619672, by rfl⟩ : syracuseStep 6159563 = 9239345) B9239345
theorem B1539641 : Blo 810345 1539641 := bstep (se 2 (by rfl) ⟨577365, by rfl⟩ : syracuseStep 1539641 = 1154731) B1154731
theorem B3079889 : Blo 810345 3079889 := bstep (se 2 (by rfl) ⟨1154958, by rfl⟩ : syracuseStep 3079889 = 2309917) B2309917
theorem B2195387 : Blo 810345 2195387 := bstep (se 1 (by rfl) ⟨1646540, by rfl⟩ : syracuseStep 2195387 = 3293081) B3293081
theorem B17858981 : Blo 810345 17858981 := bstep (se 4 (by rfl) ⟨1674279, by rfl⟩ : syracuseStep 17858981 = 3348559) B3348559
theorem B3670447 : Blo 810345 3670447 := bstep (se 1 (by rfl) ⟨2752835, by rfl⟩ : syracuseStep 3670447 = 5505671) B5505671
theorem B3703259 : Blo 810345 3703259 := bstep (se 1 (by rfl) ⟨2777444, by rfl⟩ : syracuseStep 3703259 = 5554889) B5554889
theorem B3080875 : Blo 810345 3080875 := bstep (se 1 (by rfl) ⟨2310656, by rfl⟩ : syracuseStep 3080875 = 4621313) B4621313
theorem B10420919 : Blo 810345 10420919 := bstep (se 1 (by rfl) ⟨7815689, by rfl⟩ : syracuseStep 10420919 = 15631379) B15631379
theorem B4391873 : Blo 810345 4391873 := bstep (se 2 (by rfl) ⟨1646952, by rfl⟩ : syracuseStep 4391873 = 3293905) B3293905
theorem B9372611 : Blo 810345 9372611 := bstep (se 1 (by rfl) ⟨7029458, by rfl⟩ : syracuseStep 9372611 = 14058917) B14058917
theorem B3081179 : Blo 810345 3081179 := bstep (se 1 (by rfl) ⟨2310884, by rfl⟩ : syracuseStep 3081179 = 4621769) B4621769
theorem B3900811 : Blo 810345 3900811 := bstep (se 1 (by rfl) ⟨2925608, by rfl⟩ : syracuseStep 3900811 = 5851217) B5851217
theorem B8324641 : Blo 810345 8324641 := bstep (se 2 (by rfl) ⟨3121740, by rfl⟩ : syracuseStep 8324641 = 6243481) B6243481
theorem B3082607 : Blo 810345 3082607 := bstep (se 1 (by rfl) ⟨2311955, by rfl⟩ : syracuseStep 3082607 = 4623911) B4623911
theorem B3475963 : Blo 810345 3475963 := bstep (se 1 (by rfl) ⟨2606972, by rfl⟩ : syracuseStep 3475963 = 5213945) B5213945
theorem B4459643 : Blo 810345 4459643 := bstep (se 1 (by rfl) ⟨3344732, by rfl⟩ : syracuseStep 4459643 = 6689465) B6689465
theorem B1215707 : Blo 810345 1215707 := bstep (se 1 (by rfl) ⟨911780, by rfl⟩ : syracuseStep 1215707 = 1823561) B1823561
theorem B1215881 : Blo 810345 1215881 := bstep (se 2 (by rfl) ⟨455955, by rfl⟩ : syracuseStep 1215881 = 911911) B911911
theorem B1543673 : Blo 810345 1543673 := bstep (se 2 (by rfl) ⟨578877, by rfl⟩ : syracuseStep 1543673 = 1157755) B1157755
theorem B3083791 : Blo 810345 3083791 := bstep (se 1 (by rfl) ⟨2312843, by rfl⟩ : syracuseStep 3083791 = 4625687) B4625687
theorem B1216235 : Blo 810345 1216235 := bstep (se 1 (by rfl) ⟨912176, by rfl⟩ : syracuseStep 1216235 = 1824353) B1824353
theorem B1216463 : Blo 810345 1216463 := bstep (se 1 (by rfl) ⟨912347, by rfl⟩ : syracuseStep 1216463 = 1824695) B1824695
theorem B1216859 : Blo 810345 1216859 := bstep (se 1 (by rfl) ⟨912644, by rfl⟩ : syracuseStep 1216859 = 1825289) B1825289
theorem B3904001 : Blo 810345 3904001 := bstep (se 2 (by rfl) ⟨1464000, by rfl⟩ : syracuseStep 3904001 = 2928001) B2928001
theorem B8327731 : Blo 810345 8327731 := bstep (se 1 (by rfl) ⟨6245798, by rfl⟩ : syracuseStep 8327731 = 12491597) B12491597
theorem B1217087 : Blo 810345 1217087 := bstep (se 1 (by rfl) ⟨912815, by rfl⟩ : syracuseStep 1217087 = 1825631) B1825631
theorem B1217207 : Blo 810345 1217207 := bstep (se 1 (by rfl) ⟨912905, by rfl⟩ : syracuseStep 1217207 = 1825811) B1825811
theorem B1217435 : Blo 810345 1217435 := bstep (se 1 (by rfl) ⟨913076, by rfl⟩ : syracuseStep 1217435 = 1826153) B1826153
theorem B1545131 : Blo 810345 1545131 := bstep (se 1 (by rfl) ⟨1158848, by rfl⟩ : syracuseStep 1545131 = 2317697) B2317697
theorem B1217831 : Blo 810345 1217831 := bstep (se 1 (by rfl) ⟨913373, by rfl⟩ : syracuseStep 1217831 = 1826747) B1826747
theorem B1217915 : Blo 810345 1217915 := bstep (se 1 (by rfl) ⟨913436, by rfl⟩ : syracuseStep 1217915 = 1826873) B1826873
theorem B1218041 : Blo 810345 1218041 := bstep (se 2 (by rfl) ⟨456765, by rfl⟩ : syracuseStep 1218041 = 913531) B913531
theorem B1218143 : Blo 810345 1218143 := bstep (se 1 (by rfl) ⟨913607, by rfl⟩ : syracuseStep 1218143 = 1827215) B1827215
theorem B1218359 : Blo 810345 1218359 := bstep (se 1 (by rfl) ⟨913769, by rfl⟩ : syracuseStep 1218359 = 1827539) B1827539
theorem B5937185 : Blo 810345 5937185 := bstep (se 2 (by rfl) ⟨2226444, by rfl⟩ : syracuseStep 5937185 = 4452889) B4452889
theorem B1218665 : Blo 810345 1218665 := bstep (se 2 (by rfl) ⟨456999, by rfl⟩ : syracuseStep 1218665 = 913999) B913999
theorem B21141911 : Blo 810345 21141911 := bstep (se 1 (by rfl) ⟨15856433, by rfl⟩ : syracuseStep 21141911 = 31712867) B31712867
theorem B1218983 : Blo 810345 1218983 := bstep (se 1 (by rfl) ⟨914237, by rfl⟩ : syracuseStep 1218983 = 1828475) B1828475
theorem B1219067 : Blo 810345 1219067 := bstep (se 1 (by rfl) ⟨914300, by rfl⟩ : syracuseStep 1219067 = 1828601) B1828601
theorem B1219193 : Blo 810345 1219193 := bstep (se 2 (by rfl) ⟨457197, by rfl⟩ : syracuseStep 1219193 = 914395) B914395
theorem B1219247 : Blo 810345 1219247 := bstep (se 1 (by rfl) ⟨914435, by rfl⟩ : syracuseStep 1219247 = 1828871) B1828871
theorem B1219295 : Blo 810345 1219295 := bstep (se 1 (by rfl) ⟨914471, by rfl⟩ : syracuseStep 1219295 = 1828943) B1828943
theorem B1219559 : Blo 810345 1219559 := bstep (se 1 (by rfl) ⟨914669, by rfl⟩ : syracuseStep 1219559 = 1829339) B1829339
theorem B1219817 : Blo 810345 1219817 := bstep (se 2 (by rfl) ⟨457431, by rfl⟩ : syracuseStep 1219817 = 914863) B914863
theorem B1219871 : Blo 810345 1219871 := bstep (se 1 (by rfl) ⟨914903, by rfl⟩ : syracuseStep 1219871 = 1829807) B1829807
theorem B17603983 : Blo 810345 17603983 := bstep (se 1 (by rfl) ⟨13202987, by rfl⟩ : syracuseStep 17603983 = 26405975) B26405975
theorem B1154503 : Blo 810345 1154503 := bstep (se 1 (by rfl) ⟨865877, by rfl⟩ : syracuseStep 1154503 = 1731755) B1731755
theorem B1220039 : Blo 810345 1220039 := bstep (se 1 (by rfl) ⟨915029, by rfl⟩ : syracuseStep 1220039 = 1830059) B1830059
theorem B3087953 : Blo 810345 3087953 := bstep (se 2 (by rfl) ⟨1157982, by rfl⟩ : syracuseStep 3087953 = 2315965) B2315965
theorem B2596619 : Blo 810345 2596619 := bstep (se 1 (by rfl) ⟨1947464, by rfl⟩ : syracuseStep 2596619 = 3894929) B3894929
theorem B1220393 : Blo 810345 1220393 := bstep (se 2 (by rfl) ⟨457647, by rfl⟩ : syracuseStep 1220393 = 915295) B915295
theorem B1220399 : Blo 810345 1220399 := bstep (se 1 (by rfl) ⟨915299, by rfl⟩ : syracuseStep 1220399 = 1830599) B1830599
theorem B3907385 : Blo 810345 3907385 := bstep (se 2 (by rfl) ⟨1465269, by rfl⟩ : syracuseStep 3907385 = 2930539) B2930539
theorem B4628285 : Blo 810345 4628285 := bstep (se 3 (by rfl) ⟨867803, by rfl⟩ : syracuseStep 4628285 = 1735607) B1735607
theorem B1220873 : Blo 810345 1220873 := bstep (se 2 (by rfl) ⟨457827, by rfl⟩ : syracuseStep 1220873 = 915655) B915655
theorem B1220975 : Blo 810345 1220975 := bstep (se 1 (by rfl) ⟨915731, by rfl⟩ : syracuseStep 1220975 = 1831463) B1831463
theorem B13345249 : Blo 810345 13345249 := bstep (se 2 (by rfl) ⟨5004468, by rfl⟩ : syracuseStep 13345249 = 10008937) B10008937
theorem B4104755 : Blo 810345 4104755 := bstep (se 1 (by rfl) ⟨3078566, by rfl⟩ : syracuseStep 4104755 = 6157133) B6157133
theorem B1221191 : Blo 810345 1221191 := bstep (se 1 (by rfl) ⟨915893, by rfl⟩ : syracuseStep 1221191 = 1831787) B1831787
theorem B1221227 : Blo 810345 1221227 := bstep (se 1 (by rfl) ⟨915920, by rfl⟩ : syracuseStep 1221227 = 1831841) B1831841
theorem B10429073 : Blo 810345 10429073 := bstep (se 2 (by rfl) ⟨3910902, by rfl⟩ : syracuseStep 10429073 = 7821805) B7821805
theorem B1221455 : Blo 810345 1221455 := bstep (se 1 (by rfl) ⟨916091, by rfl⟩ : syracuseStep 1221455 = 1832183) B1832183
theorem B3908807 : Blo 810345 3908807 := bstep (se 1 (by rfl) ⟨2931605, by rfl⟩ : syracuseStep 3908807 = 5863211) B5863211
theorem B3089623 : Blo 810345 3089623 := bstep (se 1 (by rfl) ⟨2317217, by rfl⟩ : syracuseStep 3089623 = 4634435) B4634435
theorem B6268211 : Blo 810345 6268211 := bstep (se 1 (by rfl) ⟨4701158, by rfl⟩ : syracuseStep 6268211 = 9402317) B9402317
theorem B3089927 : Blo 810345 3089927 := bstep (se 1 (by rfl) ⟨2317445, by rfl⟩ : syracuseStep 3089927 = 4634891) B4634891
theorem B3286865 : Blo 810345 3286865 := bstep (se 2 (by rfl) ⟨1232574, by rfl⟩ : syracuseStep 3286865 = 2465149) B2465149
theorem B4171601 : Blo 810345 4171601 := bstep (se 2 (by rfl) ⟨1564350, by rfl⟩ : syracuseStep 4171601 = 3128701) B3128701
theorem B3090383 : Blo 810345 3090383 := bstep (se 1 (by rfl) ⟨2317787, by rfl⟩ : syracuseStep 3090383 = 4635575) B4635575
theorem B3090413 : Blo 810345 3090413 := bstep (se 3 (by rfl) ⟨579452, by rfl⟩ : syracuseStep 3090413 = 1158905) B1158905
theorem B4106375 : Blo 810345 4106375 := bstep (se 1 (by rfl) ⟨3079781, by rfl⟩ : syracuseStep 4106375 = 6159563) B6159563
theorem B1026427 : Blo 810345 1026427 := bstep (se 1 (by rfl) ⟨769820, by rfl⟩ : syracuseStep 1026427 = 1539641) B1539641
theorem B3090899 : Blo 810345 3090899 := bstep (se 1 (by rfl) ⟨2318174, by rfl⟩ : syracuseStep 3090899 = 4636349) B4636349
theorem B3091355 : Blo 810345 3091355 := bstep (se 1 (by rfl) ⟨2318516, by rfl⟩ : syracuseStep 3091355 = 4637033) B4637033
theorem B16657487 : Blo 810345 16657487 := bstep (se 1 (by rfl) ⟨12493115, by rfl⟩ : syracuseStep 16657487 = 24986231) B24986231
theorem B1027495 : Blo 810345 1027495 := bstep (se 1 (by rfl) ⟨770621, by rfl⟩ : syracuseStep 1027495 = 1541243) B1541243
theorem B7810769 : Blo 810345 7810769 := bstep (se 2 (by rfl) ⟨2929038, by rfl⟩ : syracuseStep 7810769 = 5858077) B5858077
theorem B1027819 : Blo 810345 1027819 := bstep (se 1 (by rfl) ⟨770864, by rfl⟩ : syracuseStep 1027819 = 1541729) B1541729
theorem B1650439 : Blo 810345 1650439 := bstep (se 1 (by rfl) ⟨1237829, by rfl⟩ : syracuseStep 1650439 = 2475659) B2475659
theorem B1028047 : Blo 810345 1028047 := bstep (se 1 (by rfl) ⟨771035, by rfl⟩ : syracuseStep 1028047 = 1542071) B1542071
theorem B3911689 : Blo 810345 3911689 := bstep (se 2 (by rfl) ⟨1466883, by rfl⟩ : syracuseStep 3911689 = 2933767) B2933767
theorem B1028315 : Blo 810345 1028315 := bstep (se 1 (by rfl) ⟨771236, by rfl⟩ : syracuseStep 1028315 = 1542473) B1542473
theorem B1028791 : Blo 810345 1028791 := bstep (se 1 (by rfl) ⟨771593, by rfl⟩ : syracuseStep 1028791 = 1543187) B1543187
theorem B1029019 : Blo 810345 1029019 := bstep (se 1 (by rfl) ⟨771764, by rfl⟩ : syracuseStep 1029019 = 1543529) B1543529
theorem B10400825 : Blo 810345 10400825 := bstep (se 2 (by rfl) ⟨3900309, by rfl⟩ : syracuseStep 10400825 = 7800619) B7800619
theorem B1848737 : Blo 810345 1848737 := bstep (se 2 (by rfl) ⟨693276, by rfl⟩ : syracuseStep 1848737 = 1386553) B1386553
theorem B1029935 : Blo 810345 1029935 := bstep (se 1 (by rfl) ⟨772451, by rfl⟩ : syracuseStep 1029935 = 1544903) B1544903
theorem B4110263 : Blo 810345 4110263 := bstep (se 1 (by rfl) ⟨3082697, by rfl⟩ : syracuseStep 4110263 = 6165395) B6165395
theorem B3520793 : Blo 810345 3520793 := bstep (se 2 (by rfl) ⟨1320297, by rfl⟩ : syracuseStep 3520793 = 2640595) B2640595
theorem B35633459 : Blo 810345 35633459 := bstep (se 1 (by rfl) ⟨26725094, by rfl⟩ : syracuseStep 35633459 = 53450189) B53450189
theorem B1947995 : Blo 810345 1947995 := bstep (se 1 (by rfl) ⟨1460996, by rfl⟩ : syracuseStep 1947995 = 2921993) B2921993
theorem B1849775 : Blo 810345 1849775 := bstep (se 1 (by rfl) ⟨1387331, by rfl⟩ : syracuseStep 1849775 = 2774663) B2774663
theorem B4110911 : Blo 810345 4110911 := bstep (se 1 (by rfl) ⟨3083183, by rfl⟩ : syracuseStep 4110911 = 6166367) B6166367
theorem B30489281 : Blo 810345 30489281 := bstep (se 2 (by rfl) ⟨11433480, by rfl⟩ : syracuseStep 30489281 = 22866961) B22866961
theorem B2079479 : Blo 810345 2079479 := bstep (se 1 (by rfl) ⟨1559609, by rfl⟩ : syracuseStep 2079479 = 3119219) B3119219
theorem B2734991 : Blo 810345 2734991 := bstep (se 1 (by rfl) ⟨2051243, by rfl⟩ : syracuseStep 2734991 = 4102487) B4102487
theorem B2309563 : Blo 810345 2309563 := bstep (se 1 (by rfl) ⟨1732172, by rfl⟩ : syracuseStep 2309563 = 3464345) B3464345
theorem B8797841 : Blo 810345 8797841 := bstep (se 2 (by rfl) ⟨3299190, by rfl⟩ : syracuseStep 8797841 = 6598381) B6598381
theorem B2932487 : Blo 810345 2932487 := bstep (se 1 (by rfl) ⟨2199365, by rfl⟩ : syracuseStep 2932487 = 4398731) B4398731
theorem B6176573 : Blo 810345 6176573 := bstep (se 3 (by rfl) ⟨1158107, by rfl⟩ : syracuseStep 6176573 = 2316215) B2316215
theorem B7815041 : Blo 810345 7815041 := bstep (se 2 (by rfl) ⟨2930640, by rfl⟩ : syracuseStep 7815041 = 5861281) B5861281
theorem B2736233 : Blo 810345 2736233 := bstep (se 2 (by rfl) ⟨1026087, by rfl⟩ : syracuseStep 2736233 = 2052175) B2052175
theorem B14827673 : Blo 810345 14827673 := bstep (se 2 (by rfl) ⟨5560377, by rfl⟩ : syracuseStep 14827673 = 11120755) B11120755
theorem B2605385 : Blo 810345 2605385 := bstep (se 2 (by rfl) ⟨977019, by rfl⟩ : syracuseStep 2605385 = 1954039) B1954039
theorem B2474347 : Blo 810345 2474347 := bstep (se 1 (by rfl) ⟨1855760, by rfl⟩ : syracuseStep 2474347 = 3711521) B3711521
theorem B29606309 : Blo 810345 29606309 := bstep (se 4 (by rfl) ⟨2775591, by rfl⟩ : syracuseStep 29606309 = 5551183) B5551183
theorem B2605537 : Blo 810345 2605537 := bstep (se 2 (by rfl) ⟨977076, by rfl⟩ : syracuseStep 2605537 = 1954153) B1954153
theorem B4113017 : Blo 810345 4113017 := bstep (se 2 (by rfl) ⟨1542381, by rfl⟩ : syracuseStep 4113017 = 3084763) B3084763
theorem B68633219 : Blo 810345 68633219 := bstep (se 1 (by rfl) ⟨51474914, by rfl⟩ : syracuseStep 68633219 = 102949829) B102949829
theorem B2310839 : Blo 810345 2310839 := bstep (se 1 (by rfl) ⟨1733129, by rfl⟩ : syracuseStep 2310839 = 3466259) B3466259
theorem B1950455 : Blo 810345 1950455 := bstep (se 1 (by rfl) ⟨1462841, by rfl⟩ : syracuseStep 1950455 = 2925683) B2925683
theorem B8798969 : Blo 810345 8798969 := bstep (se 2 (by rfl) ⟨3299613, by rfl⟩ : syracuseStep 8798969 = 6599227) B6599227
theorem B2737097 : Blo 810345 2737097 := bstep (se 2 (by rfl) ⟨1026411, by rfl⟩ : syracuseStep 2737097 = 2052823) B2052823
theorem B4441051 : Blo 810345 4441051 := bstep (se 1 (by rfl) ⟨3330788, by rfl⟩ : syracuseStep 4441051 = 6661577) B6661577
theorem B6243331 : Blo 810345 6243331 := bstep (se 1 (by rfl) ⟨4682498, by rfl⟩ : syracuseStep 6243331 = 9364997) B9364997
theorem B6931493 : Blo 810345 6931493 := bstep (se 4 (by rfl) ⟨649827, by rfl⟩ : syracuseStep 6931493 = 1299655) B1299655
theorem B2737367 : Blo 810345 2737367 := bstep (se 1 (by rfl) ⟨2053025, by rfl⟩ : syracuseStep 2737367 = 4106051) B4106051
theorem B1852649 : Blo 810345 1852649 := bstep (se 2 (by rfl) ⟨694743, by rfl⟩ : syracuseStep 1852649 = 1389487) B1389487
theorem B13878701 : Blo 810345 13878701 := bstep (se 3 (by rfl) ⟨2602256, by rfl⟩ : syracuseStep 13878701 = 5204513) B5204513
theorem B1099207 : Blo 810345 1099207 := bstep (se 1 (by rfl) ⟨824405, by rfl⟩ : syracuseStep 1099207 = 1648811) B1648811
theorem B6571655 : Blo 810345 6571655 := bstep (se 1 (by rfl) ⟨4928741, by rfl⟩ : syracuseStep 6571655 = 9857483) B9857483
theorem B4114799 : Blo 810345 4114799 := bstep (se 1 (by rfl) ⟨3086099, by rfl⟩ : syracuseStep 4114799 = 6172199) B6172199
theorem B6572431 : Blo 810345 6572431 := bstep (se 1 (by rfl) ⟨4929323, by rfl⟩ : syracuseStep 6572431 = 9858647) B9858647
theorem B8768087 : Blo 810345 8768087 := bstep (se 1 (by rfl) ⟨6576065, by rfl⟩ : syracuseStep 8768087 = 13152131) B13152131
theorem B1952531 : Blo 810345 1952531 := bstep (se 1 (by rfl) ⟨1464398, by rfl⟩ : syracuseStep 1952531 = 2928797) B2928797
theorem B2739419 : Blo 810345 2739419 := bstep (se 1 (by rfl) ⟨2054564, by rfl⟩ : syracuseStep 2739419 = 4109129) B4109129
theorem B2051315 : Blo 810345 2051315 := bstep (se 1 (by rfl) ⟨1538486, by rfl⟩ : syracuseStep 2051315 = 3076973) B3076973
theorem B7032095 : Blo 810345 7032095 := bstep (se 1 (by rfl) ⟨5274071, by rfl⟩ : syracuseStep 7032095 = 10548143) B10548143
theorem B2051527 : Blo 810345 2051527 := bstep (se 1 (by rfl) ⟨1538645, by rfl⟩ : syracuseStep 2051527 = 3077291) B3077291
theorem B2346455 : Blo 810345 2346455 := bstep (se 1 (by rfl) ⟨1759841, by rfl⟩ : syracuseStep 2346455 = 3519683) B3519683
theorem B2084345 : Blo 810345 2084345 := bstep (se 2 (by rfl) ⟨781629, by rfl⟩ : syracuseStep 2084345 = 1563259) B1563259
theorem B6180461 : Blo 810345 6180461 := bstep (se 3 (by rfl) ⟨1158836, by rfl⟩ : syracuseStep 6180461 = 2317673) B2317673
theorem B2740283 : Blo 810345 2740283 := bstep (se 1 (by rfl) ⟨2055212, by rfl⟩ : syracuseStep 2740283 = 4110425) B4110425
theorem B2740553 : Blo 810345 2740553 := bstep (se 2 (by rfl) ⟨1027707, by rfl⟩ : syracuseStep 2740553 = 2055415) B2055415
theorem B1823507 : Blo 810345 1823507 := bstep (se 1 (by rfl) ⟨1367630, by rfl⟩ : syracuseStep 1823507 = 2735261) B2735261
theorem B1823867 : Blo 810345 1823867 := bstep (se 1 (by rfl) ⟨1367900, by rfl⟩ : syracuseStep 1823867 = 2735801) B2735801
theorem B7394429 : Blo 810345 7394429 := bstep (se 3 (by rfl) ⟨1386455, by rfl⟩ : syracuseStep 7394429 = 2772911) B2772911
theorem B2053259 : Blo 810345 2053259 := bstep (se 1 (by rfl) ⟨1539944, by rfl⟩ : syracuseStep 2053259 = 3079889) B3079889
theorem B1823993 : Blo 810345 1823993 := bstep (se 2 (by rfl) ⟨683997, by rfl⟩ : syracuseStep 1823993 = 1367995) B1367995
theorem B1463591 : Blo 810345 1463591 := bstep (se 1 (by rfl) ⟨1097693, by rfl⟩ : syracuseStep 1463591 = 2195387) B2195387
theorem B2053471 : Blo 810345 2053471 := bstep (se 1 (by rfl) ⟨1540103, by rfl⟩ : syracuseStep 2053471 = 3080207) B3080207
theorem B1824137 : Blo 810345 1824137 := bstep (se 2 (by rfl) ⟨684051, by rfl⟩ : syracuseStep 1824137 = 1368103) B1368103
theorem B8803723 : Blo 810345 8803723 := bstep (se 1 (by rfl) ⟨6602792, by rfl⟩ : syracuseStep 8803723 = 13205585) B13205585
theorem B1824263 : Blo 810345 1824263 := bstep (se 1 (by rfl) ⟨1368197, by rfl⟩ : syracuseStep 1824263 = 2736395) B2736395
theorem B2315783 : Blo 810345 2315783 := bstep (se 1 (by rfl) ⟨1736837, by rfl⟩ : syracuseStep 2315783 = 3473675) B3473675
theorem B3462689 : Blo 810345 3462689 := bstep (se 2 (by rfl) ⟨1298508, by rfl⟩ : syracuseStep 3462689 = 2597017) B2597017
theorem B114349603 : Blo 810345 114349603 := bstep (se 1 (by rfl) ⟨85762202, by rfl⟩ : syracuseStep 114349603 = 171524405) B171524405
theorem B3462841 : Blo 810345 3462841 := bstep (se 2 (by rfl) ⟨1298565, by rfl⟩ : syracuseStep 3462841 = 2597131) B2597131
theorem B4118201 : Blo 810345 4118201 := bstep (se 2 (by rfl) ⟨1544325, by rfl⟩ : syracuseStep 4118201 = 3088651) B3088651
theorem B1824443 : Blo 810345 1824443 := bstep (se 1 (by rfl) ⟨1368332, by rfl⟩ : syracuseStep 1824443 = 2736665) B2736665
theorem B15652601 : Blo 810345 15652601 := bstep (se 2 (by rfl) ⟨5869725, by rfl⟩ : syracuseStep 15652601 = 11739451) B11739451
theorem B1824569 : Blo 810345 1824569 := bstep (se 2 (by rfl) ⟨684213, by rfl⟩ : syracuseStep 1824569 = 1368427) B1368427
theorem B2316239 : Blo 810345 2316239 := bstep (se 1 (by rfl) ⟨1737179, by rfl⟩ : syracuseStep 2316239 = 3474359) B3474359
theorem B2775073 : Blo 810345 2775073 := bstep (se 2 (by rfl) ⟨1040652, by rfl⟩ : syracuseStep 2775073 = 2081305) B2081305
theorem B2087279 : Blo 810345 2087279 := bstep (se 1 (by rfl) ⟨1565459, by rfl⟩ : syracuseStep 2087279 = 3130919) B3130919
theorem B1825199 : Blo 810345 1825199 := bstep (se 1 (by rfl) ⟨1368899, by rfl⟩ : syracuseStep 1825199 = 2737799) B2737799
theorem B1825235 : Blo 810345 1825235 := bstep (se 1 (by rfl) ⟨1368926, by rfl⟩ : syracuseStep 1825235 = 2737853) B2737853
theorem B1825343 : Blo 810345 1825343 := bstep (se 1 (by rfl) ⟨1369007, by rfl⟩ : syracuseStep 1825343 = 2738015) B2738015
theorem B1464895 : Blo 810345 1464895 := bstep (se 1 (by rfl) ⟨1098671, by rfl⟩ : syracuseStep 1464895 = 2197343) B2197343
theorem B1825451 : Blo 810345 1825451 := bstep (se 1 (by rfl) ⟨1369088, by rfl⟩ : syracuseStep 1825451 = 2738177) B2738177
theorem B6576815 : Blo 810345 6576815 := bstep (se 1 (by rfl) ⟨4932611, by rfl⟩ : syracuseStep 6576815 = 9865223) B9865223
theorem B2054879 : Blo 810345 2054879 := bstep (se 1 (by rfl) ⟨1541159, by rfl⟩ : syracuseStep 2054879 = 3082319) B3082319
theorem B1825991 : Blo 810345 1825991 := bstep (se 1 (by rfl) ⟨1369493, by rfl⟩ : syracuseStep 1825991 = 2738987) B2738987
theorem B810351 : Blo 810345 810351 := bstep (se 1 (by rfl) ⟨607763, by rfl⟩ : syracuseStep 810351 = 1215527) B1215527
theorem B1826171 : Blo 810345 1826171 := bstep (se 1 (by rfl) ⟨1369628, by rfl⟩ : syracuseStep 1826171 = 2739257) B2739257
theorem B810407 : Blo 810345 810407 := bstep (se 1 (by rfl) ⟨607805, by rfl⟩ : syracuseStep 810407 = 1215611) B1215611
theorem B2743739 : Blo 810345 2743739 := bstep (se 1 (by rfl) ⟨2057804, by rfl⟩ : syracuseStep 2743739 = 4115609) B4115609
theorem B1826297 : Blo 810345 1826297 := bstep (se 2 (by rfl) ⟨684861, by rfl⟩ : syracuseStep 1826297 = 1369723) B1369723
theorem B810491 : Blo 810345 810491 := bstep (se 1 (by rfl) ⟨607868, by rfl⟩ : syracuseStep 810491 = 1215737) B1215737
theorem B6250007 : Blo 810345 6250007 := bstep (se 1 (by rfl) ⟨4687505, by rfl⟩ : syracuseStep 6250007 = 9375011) B9375011
theorem B810559 : Blo 810345 810559 := bstep (se 1 (by rfl) ⟨607919, by rfl⟩ : syracuseStep 810559 = 1215839) B1215839
theorem B810567 : Blo 810345 810567 := bstep (se 1 (by rfl) ⟨607925, by rfl⟩ : syracuseStep 810567 = 1215851) B1215851
theorem B4120145 : Blo 810345 4120145 := bstep (se 2 (by rfl) ⟨1545054, by rfl⟩ : syracuseStep 4120145 = 3090109) B3090109
theorem B1826387 : Blo 810345 1826387 := bstep (se 1 (by rfl) ⟨1369790, by rfl⟩ : syracuseStep 1826387 = 2739581) B2739581
theorem B6938257 : Blo 810345 6938257 := bstep (se 2 (by rfl) ⟨2601846, by rfl⟩ : syracuseStep 6938257 = 5203693) B5203693
theorem B810719 : Blo 810345 810719 := bstep (se 1 (by rfl) ⟨608039, by rfl⟩ : syracuseStep 810719 = 1216079) B1216079
theorem B1826567 : Blo 810345 1826567 := bstep (se 1 (by rfl) ⟨1369925, by rfl⟩ : syracuseStep 1826567 = 2739851) B2739851
theorem B13852457 : Blo 810345 13852457 := bstep (se 2 (by rfl) ⟨5194671, by rfl⟩ : syracuseStep 13852457 = 10389343) B10389343
theorem B810799 : Blo 810345 810799 := bstep (se 1 (by rfl) ⟨608099, by rfl⟩ : syracuseStep 810799 = 1216199) B1216199
theorem B810907 : Blo 810345 810907 := bstep (se 1 (by rfl) ⟨608180, by rfl⟩ : syracuseStep 810907 = 1216361) B1216361
theorem B810959 : Blo 810345 810959 := bstep (se 1 (by rfl) ⟨608219, by rfl⟩ : syracuseStep 810959 = 1216439) B1216439
theorem B810983 : Blo 810345 810983 := bstep (se 1 (by rfl) ⟨608237, by rfl⟩ : syracuseStep 810983 = 1216475) B1216475
theorem B811295 : Blo 810345 811295 := bstep (se 1 (by rfl) ⟨608471, by rfl⟩ : syracuseStep 811295 = 1216943) B1216943
theorem B2318665 : Blo 810345 2318665 := bstep (se 2 (by rfl) ⟨869499, by rfl⟩ : syracuseStep 2318665 = 1738999) B1738999
theorem B811355 : Blo 810345 811355 := bstep (se 1 (by rfl) ⟨608516, by rfl⟩ : syracuseStep 811355 = 1217033) B1217033
theorem B1827179 : Blo 810345 1827179 := bstep (se 1 (by rfl) ⟨1370384, by rfl⟩ : syracuseStep 1827179 = 2740769) B2740769
theorem B2318699 : Blo 810345 2318699 := bstep (se 1 (by rfl) ⟨1739024, by rfl⟩ : syracuseStep 2318699 = 3478049) B3478049
theorem B811375 : Blo 810345 811375 := bstep (se 1 (by rfl) ⟨608531, by rfl⟩ : syracuseStep 811375 = 1217063) B1217063
theorem B811431 : Blo 810345 811431 := bstep (se 1 (by rfl) ⟨608573, by rfl⟩ : syracuseStep 811431 = 1217147) B1217147
theorem B6578633 : Blo 810345 6578633 := bstep (se 2 (by rfl) ⟨2466987, by rfl⟩ : syracuseStep 6578633 = 4933975) B4933975
theorem B3564001 : Blo 810345 3564001 := bstep (se 2 (by rfl) ⟨1336500, by rfl⟩ : syracuseStep 3564001 = 2673001) B2673001
theorem B811515 : Blo 810345 811515 := bstep (se 1 (by rfl) ⟨608636, by rfl⟩ : syracuseStep 811515 = 1217273) B1217273
theorem B1827323 : Blo 810345 1827323 := bstep (se 1 (by rfl) ⟨1370492, by rfl⟩ : syracuseStep 1827323 = 2740985) B2740985
theorem B8905249 : Blo 810345 8905249 := bstep (se 2 (by rfl) ⟨3339468, by rfl⟩ : syracuseStep 8905249 = 6678937) B6678937
theorem B811583 : Blo 810345 811583 := bstep (se 1 (by rfl) ⟨608687, by rfl⟩ : syracuseStep 811583 = 1217375) B1217375
theorem B1303103 : Blo 810345 1303103 := bstep (se 1 (by rfl) ⟨977327, by rfl⟩ : syracuseStep 1303103 = 1954655) B1954655
theorem B811591 : Blo 810345 811591 := bstep (se 1 (by rfl) ⟨608693, by rfl⟩ : syracuseStep 811591 = 1217387) B1217387
theorem B1368697 : Blo 810345 1368697 := bstep (se 2 (by rfl) ⟨513261, by rfl⟩ : syracuseStep 1368697 = 1026523) B1026523
theorem B1827449 : Blo 810345 1827449 := bstep (se 2 (by rfl) ⟨685293, by rfl⟩ : syracuseStep 1827449 = 1370587) B1370587
theorem B1368751 : Blo 810345 1368751 := bstep (se 1 (by rfl) ⟨1026563, by rfl⟩ : syracuseStep 1368751 = 2053127) B2053127
theorem B1827503 : Blo 810345 1827503 := bstep (se 1 (by rfl) ⟨1370627, by rfl⟩ : syracuseStep 1827503 = 2741255) B2741255
theorem B6578891 : Blo 810345 6578891 := bstep (se 1 (by rfl) ⟨4934168, by rfl⟩ : syracuseStep 6578891 = 9868337) B9868337
theorem B811743 : Blo 810345 811743 := bstep (se 1 (by rfl) ⟨608807, by rfl⟩ : syracuseStep 811743 = 1217615) B1217615
theorem B1827575 : Blo 810345 1827575 := bstep (se 1 (by rfl) ⟨1370681, by rfl⟩ : syracuseStep 1827575 = 2741363) B2741363
theorem B811823 : Blo 810345 811823 := bstep (se 1 (by rfl) ⟨608867, by rfl⟩ : syracuseStep 811823 = 1217735) B1217735
theorem B811931 : Blo 810345 811931 := bstep (se 1 (by rfl) ⟨608948, by rfl⟩ : syracuseStep 811931 = 1217897) B1217897
theorem B1827755 : Blo 810345 1827755 := bstep (se 1 (by rfl) ⟨1370816, by rfl⟩ : syracuseStep 1827755 = 2741633) B2741633
theorem B811983 : Blo 810345 811983 := bstep (se 1 (by rfl) ⟨608987, by rfl⟩ : syracuseStep 811983 = 1217975) B1217975
theorem B812007 : Blo 810345 812007 := bstep (se 1 (by rfl) ⟨609005, by rfl⟩ : syracuseStep 812007 = 1218011) B1218011
theorem B2057339 : Blo 810345 2057339 := bstep (se 1 (by rfl) ⟨1543004, by rfl⟩ : syracuseStep 2057339 = 3086009) B3086009
theorem B2057359 : Blo 810345 2057359 := bstep (se 1 (by rfl) ⟨1543019, by rfl⟩ : syracuseStep 2057359 = 3086039) B3086039
theorem B812319 : Blo 810345 812319 := bstep (se 1 (by rfl) ⟨609239, by rfl⟩ : syracuseStep 812319 = 1218479) B1218479
theorem B812379 : Blo 810345 812379 := bstep (se 1 (by rfl) ⟨609284, by rfl⟩ : syracuseStep 812379 = 1218569) B1218569
theorem B3466601 : Blo 810345 3466601 := bstep (se 2 (by rfl) ⟨1299975, by rfl⟩ : syracuseStep 3466601 = 2599951) B2599951
theorem B812399 : Blo 810345 812399 := bstep (se 1 (by rfl) ⟨609299, by rfl⟩ : syracuseStep 812399 = 1218599) B1218599
theorem B2057633 : Blo 810345 2057633 := bstep (se 2 (by rfl) ⟨771612, by rfl⟩ : syracuseStep 2057633 = 1543225) B1543225
theorem B812455 : Blo 810345 812455 := bstep (se 1 (by rfl) ⟨609341, by rfl⟩ : syracuseStep 812455 = 1218683) B1218683
theorem B1828295 : Blo 810345 1828295 := bstep (se 1 (by rfl) ⟨1371221, by rfl⟩ : syracuseStep 1828295 = 2742443) B2742443
theorem B812539 : Blo 810345 812539 := bstep (se 1 (by rfl) ⟨609404, by rfl⟩ : syracuseStep 812539 = 1218809) B1218809
theorem B812607 : Blo 810345 812607 := bstep (se 1 (by rfl) ⟨609455, by rfl⟩ : syracuseStep 812607 = 1218911) B1218911
theorem B812615 : Blo 810345 812615 := bstep (se 1 (by rfl) ⟨609461, by rfl⟩ : syracuseStep 812615 = 1218923) B1218923
theorem B812767 : Blo 810345 812767 := bstep (se 1 (by rfl) ⟨609575, by rfl⟩ : syracuseStep 812767 = 1219151) B1219151
theorem B1828655 : Blo 810345 1828655 := bstep (se 1 (by rfl) ⟨1371491, by rfl⟩ : syracuseStep 1828655 = 2742983) B2742983
theorem B812847 : Blo 810345 812847 := bstep (se 1 (by rfl) ⟨609635, by rfl⟩ : syracuseStep 812847 = 1219271) B1219271
theorem B3467063 : Blo 810345 3467063 := bstep (se 1 (by rfl) ⟨2600297, by rfl⟩ : syracuseStep 3467063 = 5200595) B5200595
theorem B11724689 : Blo 810345 11724689 := bstep (se 2 (by rfl) ⟨4396758, by rfl⟩ : syracuseStep 11724689 = 8793517) B8793517
theorem B812955 : Blo 810345 812955 := bstep (se 1 (by rfl) ⟨609716, by rfl⟩ : syracuseStep 812955 = 1219433) B1219433
theorem B3467215 : Blo 810345 3467215 := bstep (se 1 (by rfl) ⟨2600411, by rfl⟩ : syracuseStep 3467215 = 5200823) B5200823
theorem B813007 : Blo 810345 813007 := bstep (se 1 (by rfl) ⟨609755, by rfl⟩ : syracuseStep 813007 = 1219511) B1219511
theorem B4122575 : Blo 810345 4122575 := bstep (se 1 (by rfl) ⟨3091931, by rfl⟩ : syracuseStep 4122575 = 6183863) B6183863
theorem B813031 : Blo 810345 813031 := bstep (se 1 (by rfl) ⟨609773, by rfl⟩ : syracuseStep 813031 = 1219547) B1219547
theorem B813343 : Blo 810345 813343 := bstep (se 1 (by rfl) ⟨610007, by rfl⟩ : syracuseStep 813343 = 1220015) B1220015
theorem B1370459 : Blo 810345 1370459 := bstep (se 1 (by rfl) ⟨1027844, by rfl⟩ : syracuseStep 1370459 = 2055689) B2055689
theorem B813403 : Blo 810345 813403 := bstep (se 1 (by rfl) ⟨610052, by rfl⟩ : syracuseStep 813403 = 1220105) B1220105
theorem B1370479 : Blo 810345 1370479 := bstep (se 1 (by rfl) ⟨1027859, by rfl⟩ : syracuseStep 1370479 = 2055719) B2055719
theorem B1829231 : Blo 810345 1829231 := bstep (se 1 (by rfl) ⟨1371923, by rfl⟩ : syracuseStep 1829231 = 2743847) B2743847
theorem B813423 : Blo 810345 813423 := bstep (se 1 (by rfl) ⟨610067, by rfl⟩ : syracuseStep 813423 = 1220135) B1220135
theorem B6252967 : Blo 810345 6252967 := bstep (se 1 (by rfl) ⟨4689725, by rfl⟩ : syracuseStep 6252967 = 9379451) B9379451
theorem B813479 : Blo 810345 813479 := bstep (se 1 (by rfl) ⟨610109, by rfl⟩ : syracuseStep 813479 = 1220219) B1220219
theorem B1829303 : Blo 810345 1829303 := bstep (se 1 (by rfl) ⟨1371977, by rfl⟩ : syracuseStep 1829303 = 2743955) B2743955
theorem B2779643 : Blo 810345 2779643 := bstep (se 1 (by rfl) ⟨2084732, by rfl⟩ : syracuseStep 2779643 = 4169465) B4169465
theorem B813563 : Blo 810345 813563 := bstep (se 1 (by rfl) ⟨610172, by rfl⟩ : syracuseStep 813563 = 1220345) B1220345
theorem B813631 : Blo 810345 813631 := bstep (se 1 (by rfl) ⟨610223, by rfl⟩ : syracuseStep 813631 = 1220447) B1220447
theorem B1370695 : Blo 810345 1370695 := bstep (se 1 (by rfl) ⟨1028021, by rfl⟩ : syracuseStep 1370695 = 2056043) B2056043
theorem B1829447 : Blo 810345 1829447 := bstep (se 1 (by rfl) ⟨1372085, by rfl⟩ : syracuseStep 1829447 = 2744171) B2744171
theorem B813639 : Blo 810345 813639 := bstep (se 1 (by rfl) ⟨610229, by rfl⟩ : syracuseStep 813639 = 1220459) B1220459
theorem B1829483 : Blo 810345 1829483 := bstep (se 1 (by rfl) ⟨1372112, by rfl⟩ : syracuseStep 1829483 = 2744225) B2744225
theorem B813791 : Blo 810345 813791 := bstep (se 1 (by rfl) ⟨610343, by rfl⟩ : syracuseStep 813791 = 1220687) B1220687
theorem B568519397 : Blo 810345 568519397 := bstep (se 4 (by rfl) ⟨53298693, by rfl⟩ : syracuseStep 568519397 = 106597387) B106597387
theorem B813871 : Blo 810345 813871 := bstep (se 1 (by rfl) ⟨610403, by rfl⟩ : syracuseStep 813871 = 1220807) B1220807
theorem B4385603 : Blo 810345 4385603 := bstep (se 1 (by rfl) ⟨3289202, by rfl⟩ : syracuseStep 4385603 = 6578405) B6578405
theorem B813979 : Blo 810345 813979 := bstep (se 1 (by rfl) ⟨610484, by rfl⟩ : syracuseStep 813979 = 1220969) B1220969
theorem B284322757 : Blo 810345 284322757 := bstep (se 4 (by rfl) ⟨26655258, by rfl⟩ : syracuseStep 284322757 = 53310517) B53310517
theorem B814031 : Blo 810345 814031 := bstep (se 1 (by rfl) ⟨610523, by rfl⟩ : syracuseStep 814031 = 1221047) B1221047
theorem B814055 : Blo 810345 814055 := bstep (se 1 (by rfl) ⟨610541, by rfl⟩ : syracuseStep 814055 = 1221083) B1221083
theorem B1371127 : Blo 810345 1371127 := bstep (se 1 (by rfl) ⟨1028345, by rfl⟩ : syracuseStep 1371127 = 2056691) B2056691
theorem B1829879 : Blo 810345 1829879 := bstep (se 1 (by rfl) ⟨1372409, by rfl⟩ : syracuseStep 1829879 = 2744819) B2744819
theorem B2059303 : Blo 810345 2059303 := bstep (se 1 (by rfl) ⟨1544477, by rfl⟩ : syracuseStep 2059303 = 3088955) B3088955
theorem B1371431 : Blo 810345 1371431 := bstep (se 1 (by rfl) ⟨1028573, by rfl⟩ : syracuseStep 1371431 = 2057147) B2057147
theorem B1830239 : Blo 810345 1830239 := bstep (se 1 (by rfl) ⟨1372679, by rfl⟩ : syracuseStep 1830239 = 2745359) B2745359
theorem B2059769 : Blo 810345 2059769 := bstep (se 2 (by rfl) ⟨772413, by rfl⟩ : syracuseStep 2059769 = 1544827) B1544827
theorem B2747897 : Blo 810345 2747897 := bstep (se 2 (by rfl) ⟨1030461, by rfl⟩ : syracuseStep 2747897 = 2060923) B2060923
theorem B912991 : Blo 810345 912991 := bstep (se 1 (by rfl) ⟨684743, by rfl⟩ : syracuseStep 912991 = 1369487) B1369487
theorem B3698291 : Blo 810345 3698291 := bstep (se 1 (by rfl) ⟨2773718, by rfl⟩ : syracuseStep 3698291 = 5547437) B5547437
theorem B1371883 : Blo 810345 1371883 := bstep (se 1 (by rfl) ⟨1028912, by rfl⟩ : syracuseStep 1371883 = 2057825) B2057825
theorem B1830635 : Blo 810345 1830635 := bstep (se 1 (by rfl) ⟨1372976, by rfl⟩ : syracuseStep 1830635 = 2745953) B2745953
theorem B2748167 : Blo 810345 2748167 := bstep (se 1 (by rfl) ⟨2061125, by rfl⟩ : syracuseStep 2748167 = 4122251) B4122251
theorem B2748221 : Blo 810345 2748221 := bstep (se 3 (by rfl) ⟨515291, by rfl⟩ : syracuseStep 2748221 = 1030583) B1030583
theorem B1830761 : Blo 810345 1830761 := bstep (se 2 (by rfl) ⟨686535, by rfl⟩ : syracuseStep 1830761 = 1373071) B1373071
theorem B9236429 : Blo 810345 9236429 := bstep (se 3 (by rfl) ⟨1731830, by rfl⟩ : syracuseStep 9236429 = 3463661) B3463661
theorem B84275315 : Blo 810345 84275315 := bstep (se 1 (by rfl) ⟨63206486, by rfl⟩ : syracuseStep 84275315 = 126412973) B126412973
theorem B2060417 : Blo 810345 2060417 := bstep (se 2 (by rfl) ⟨772656, by rfl⟩ : syracuseStep 2060417 = 1545313) B1545313
theorem B2060711 : Blo 810345 2060711 := bstep (se 1 (by rfl) ⟨1545533, by rfl⟩ : syracuseStep 2060711 = 3091067) B3091067
theorem B40104409 : Blo 810345 40104409 := bstep (se 2 (by rfl) ⟨15039153, by rfl⟩ : syracuseStep 40104409 = 30078307) B30078307
theorem B2060873 : Blo 810345 2060873 := bstep (se 2 (by rfl) ⟨772827, by rfl⟩ : syracuseStep 2060873 = 1545655) B1545655
theorem B1372855 : Blo 810345 1372855 := bstep (se 1 (by rfl) ⟨1029641, by rfl⟩ : syracuseStep 1372855 = 2059283) B2059283
theorem B1831607 : Blo 810345 1831607 := bstep (se 1 (by rfl) ⟨1373705, by rfl⟩ : syracuseStep 1831607 = 2747411) B2747411
theorem B914143 : Blo 810345 914143 := bstep (se 1 (by rfl) ⟨685607, by rfl⟩ : syracuseStep 914143 = 1371215) B1371215
theorem B1733395 : Blo 810345 1733395 := bstep (se 1 (by rfl) ⟨1300046, by rfl⟩ : syracuseStep 1733395 = 2600093) B2600093
theorem B1831823 : Blo 810345 1831823 := bstep (se 1 (by rfl) ⟨1373867, by rfl⟩ : syracuseStep 1831823 = 2747735) B2747735
theorem B2061227 : Blo 810345 2061227 := bstep (se 1 (by rfl) ⟨1545920, by rfl⟩ : syracuseStep 2061227 = 3091841) B3091841
theorem B1373159 : Blo 810345 1373159 := bstep (se 1 (by rfl) ⟨1029869, by rfl⟩ : syracuseStep 1373159 = 2059739) B2059739
theorem B2192627 : Blo 810345 2192627 := bstep (se 1 (by rfl) ⟨1644470, by rfl⟩ : syracuseStep 2192627 = 3288941) B3288941
theorem B7402745 : Blo 810345 7402745 := bstep (se 2 (by rfl) ⟨2776029, by rfl⟩ : syracuseStep 7402745 = 5552059) B5552059
theorem B1733881 : Blo 810345 1733881 := bstep (se 2 (by rfl) ⟨650205, by rfl⟩ : syracuseStep 1733881 = 1300411) B1300411
theorem B11728151 : Blo 810345 11728151 := bstep (se 1 (by rfl) ⟨8796113, by rfl⟩ : syracuseStep 11728151 = 17592227) B17592227
theorem B914719 : Blo 810345 914719 := bstep (se 1 (by rfl) ⟨686039, by rfl⟩ : syracuseStep 914719 = 1372079) B1372079
theorem B3470701 : Blo 810345 3470701 := bstep (se 3 (by rfl) ⟨650756, by rfl⟩ : syracuseStep 3470701 = 1301513) B1301513
theorem B2225569 : Blo 810345 2225569 := bstep (se 2 (by rfl) ⟨834588, by rfl⟩ : syracuseStep 2225569 = 1669177) B1669177
theorem B5207489 : Blo 810345 5207489 := bstep (se 2 (by rfl) ⟨1952808, by rfl⟩ : syracuseStep 5207489 = 3905617) B3905617
theorem B915007 : Blo 810345 915007 := bstep (se 1 (by rfl) ⟨686255, by rfl⟩ : syracuseStep 915007 = 1372511) B1372511
theorem B2193083 : Blo 810345 2193083 := bstep (se 1 (by rfl) ⟨1644812, by rfl⟩ : syracuseStep 2193083 = 3289625) B3289625
theorem B3799169 : Blo 810345 3799169 := bstep (se 2 (by rfl) ⟨1424688, by rfl⟩ : syracuseStep 3799169 = 2849377) B2849377
theorem B106854551 : Blo 810345 106854551 := bstep (se 1 (by rfl) ⟨80140913, by rfl⟩ : syracuseStep 106854551 = 160281827) B160281827
theorem B915835 : Blo 810345 915835 := bstep (se 1 (by rfl) ⟨686876, by rfl⟩ : syracuseStep 915835 = 1373753) B1373753
theorem B3078719 : Blo 810345 3078719 := bstep (se 1 (by rfl) ⟨2309039, by rfl⟩ : syracuseStep 3078719 = 4618079) B4618079
theorem B3078931 : Blo 810345 3078931 := bstep (se 1 (by rfl) ⟨2309198, by rfl⟩ : syracuseStep 3078931 = 4618397) B4618397
theorem B4684787 : Blo 810345 4684787 := bstep (se 1 (by rfl) ⟨3513590, by rfl⟩ : syracuseStep 4684787 = 7027181) B7027181
theorem B7044259 : Blo 810345 7044259 := bstep (se 1 (by rfl) ⟨5283194, by rfl⟩ : syracuseStep 7044259 = 10566389) B10566389
theorem B2194877 : Blo 810345 2194877 := bstep (se 3 (by rfl) ⟨411539, by rfl⟩ : syracuseStep 2194877 = 823079) B823079
theorem B1736923 : Blo 810345 1736923 := bstep (se 1 (by rfl) ⟨1302692, by rfl⟩ : syracuseStep 1736923 = 2605385) B2605385
theorem B1540559 : Blo 810345 1540559 := bstep (se 1 (by rfl) ⟨1155419, by rfl⟩ : syracuseStep 1540559 = 2310839) B2310839
theorem B6947279 : Blo 810345 6947279 := bstep (se 1 (by rfl) ⟨5210459, by rfl⟩ : syracuseStep 6947279 = 10420919) B10420919
theorem B5865979 : Blo 810345 5865979 := bstep (se 1 (by rfl) ⟨4399484, by rfl⟩ : syracuseStep 5865979 = 8798969) B8798969
theorem B17793665 : Blo 810345 17793665 := bstep (se 2 (by rfl) ⟨6672624, by rfl⟩ : syracuseStep 17793665 = 13345249) B13345249
theorem B4752001 : Blo 810345 4752001 := bstep (se 2 (by rfl) ⟨1782000, by rfl⟩ : syracuseStep 4752001 = 3564001) B3564001
theorem B4620995 : Blo 810345 4620995 := bstep (se 1 (by rfl) ⟨3465746, by rfl⟩ : syracuseStep 4620995 = 6931493) B6931493
theorem B8324441 : Blo 810345 8324441 := bstep (se 2 (by rfl) ⟨3121665, by rfl⟩ : syracuseStep 8324441 = 6243331) B6243331
theorem B4688063 : Blo 810345 4688063 := bstep (se 1 (by rfl) ⟨3516047, by rfl⟩ : syracuseStep 4688063 = 7032095) B7032095
theorem B13896197 : Blo 810345 13896197 := bstep (se 4 (by rfl) ⟨1302768, by rfl⟩ : syracuseStep 13896197 = 2605537) B2605537
theorem B4622953 : Blo 810345 4622953 := bstep (se 2 (by rfl) ⟨1733607, by rfl⟩ : syracuseStep 4622953 = 3467215) B3467215
theorem B1215671 : Blo 810345 1215671 := bstep (se 1 (by rfl) ⟨911753, by rfl⟩ : syracuseStep 1215671 = 1823507) B1823507
theorem B1215911 : Blo 810345 1215911 := bstep (se 1 (by rfl) ⟨911933, by rfl⟩ : syracuseStep 1215911 = 1823867) B1823867
theorem B1215995 : Blo 810345 1215995 := bstep (se 1 (by rfl) ⟨911996, by rfl⟩ : syracuseStep 1215995 = 1823993) B1823993
theorem B1216091 : Blo 810345 1216091 := bstep (se 1 (by rfl) ⟨912068, by rfl⟩ : syracuseStep 1216091 = 1824137) B1824137
theorem B1216175 : Blo 810345 1216175 := bstep (se 1 (by rfl) ⟨912131, by rfl⟩ : syracuseStep 1216175 = 1824263) B1824263
theorem B1543855 : Blo 810345 1543855 := bstep (se 1 (by rfl) ⟨1157891, by rfl⟩ : syracuseStep 1543855 = 2315783) B2315783
theorem B1216295 : Blo 810345 1216295 := bstep (se 1 (by rfl) ⟨912221, by rfl⟩ : syracuseStep 1216295 = 1824443) B1824443
theorem B1216379 : Blo 810345 1216379 := bstep (se 1 (by rfl) ⟨912284, by rfl⟩ : syracuseStep 1216379 = 1824569) B1824569
theorem B379097009 : Blo 810345 379097009 := bstep (se 2 (by rfl) ⟨142161378, by rfl⟩ : syracuseStep 379097009 = 284322757) B284322757
theorem B1544159 : Blo 810345 1544159 := bstep (se 1 (by rfl) ⟨1158119, by rfl⟩ : syracuseStep 1544159 = 2316239) B2316239
theorem B14094607 : Blo 810345 14094607 := bstep (se 1 (by rfl) ⟨10570955, by rfl⟩ : syracuseStep 14094607 = 21141911) B21141911
theorem B1216799 : Blo 810345 1216799 := bstep (se 1 (by rfl) ⟨912599, by rfl⟩ : syracuseStep 1216799 = 1825199) B1825199
theorem B1216823 : Blo 810345 1216823 := bstep (se 1 (by rfl) ⟨912617, by rfl⟩ : syracuseStep 1216823 = 1825235) B1825235
theorem B1216895 : Blo 810345 1216895 := bstep (se 1 (by rfl) ⟨912671, by rfl⟩ : syracuseStep 1216895 = 1825343) B1825343
theorem B1216967 : Blo 810345 1216967 := bstep (se 1 (by rfl) ⟨912725, by rfl⟩ : syracuseStep 1216967 = 1825451) B1825451
theorem B1217321 : Blo 810345 1217321 := bstep (se 2 (by rfl) ⟨456495, by rfl⟩ : syracuseStep 1217321 = 912991) B912991
theorem B1217327 : Blo 810345 1217327 := bstep (se 1 (by rfl) ⟨912995, by rfl⟩ : syracuseStep 1217327 = 1825991) B1825991
theorem B1217447 : Blo 810345 1217447 := bstep (se 1 (by rfl) ⟨913085, by rfl⟩ : syracuseStep 1217447 = 1826171) B1826171
theorem B1217531 : Blo 810345 1217531 := bstep (se 1 (by rfl) ⟨913148, by rfl⟩ : syracuseStep 1217531 = 1826297) B1826297
theorem B4166671 : Blo 810345 4166671 := bstep (se 1 (by rfl) ⟨3125003, by rfl⟩ : syracuseStep 4166671 = 6250007) B6250007
theorem B1217591 : Blo 810345 1217591 := bstep (se 1 (by rfl) ⟨913193, by rfl⟩ : syracuseStep 1217591 = 1826387) B1826387
theorem B1217711 : Blo 810345 1217711 := bstep (se 1 (by rfl) ⟨913283, by rfl⟩ : syracuseStep 1217711 = 1826567) B1826567
theorem B3085523 : Blo 810345 3085523 := bstep (se 1 (by rfl) ⟨2314142, by rfl⟩ : syracuseStep 3085523 = 4628285) B4628285
theorem B5215585 : Blo 810345 5215585 := bstep (se 2 (by rfl) ⟨1955844, by rfl⟩ : syracuseStep 5215585 = 3911689) B3911689
theorem B15832493 : Blo 810345 15832493 := bstep (se 3 (by rfl) ⟨2968592, by rfl⟩ : syracuseStep 15832493 = 5937185) B5937185
theorem B1218119 : Blo 810345 1218119 := bstep (se 1 (by rfl) ⟨913589, by rfl⟩ : syracuseStep 1218119 = 1827179) B1827179
theorem B1545799 : Blo 810345 1545799 := bstep (se 1 (by rfl) ⟨1159349, by rfl⟩ : syracuseStep 1545799 = 2318699) B2318699
theorem B1218215 : Blo 810345 1218215 := bstep (se 1 (by rfl) ⟨913661, by rfl⟩ : syracuseStep 1218215 = 1827323) B1827323
theorem B1218299 : Blo 810345 1218299 := bstep (se 1 (by rfl) ⟨913724, by rfl⟩ : syracuseStep 1218299 = 1827449) B1827449
theorem B6952715 : Blo 810345 6952715 := bstep (se 1 (by rfl) ⟨5214536, by rfl⟩ : syracuseStep 6952715 = 10429073) B10429073
theorem B1218335 : Blo 810345 1218335 := bstep (se 1 (by rfl) ⟨913751, by rfl⟩ : syracuseStep 1218335 = 1827503) B1827503
theorem B1218383 : Blo 810345 1218383 := bstep (se 1 (by rfl) ⟨913787, by rfl⟩ : syracuseStep 1218383 = 1827575) B1827575
theorem B1218503 : Blo 810345 1218503 := bstep (se 1 (by rfl) ⟨913877, by rfl⟩ : syracuseStep 1218503 = 1827755) B1827755
theorem B1218857 : Blo 810345 1218857 := bstep (se 2 (by rfl) ⟨457071, by rfl⟩ : syracuseStep 1218857 = 914143) B914143
theorem B1218863 : Blo 810345 1218863 := bstep (se 1 (by rfl) ⟨914147, by rfl⟩ : syracuseStep 1218863 = 1828295) B1828295
theorem B1219103 : Blo 810345 1219103 := bstep (se 1 (by rfl) ⟨914327, by rfl⟩ : syracuseStep 1219103 = 1828655) B1828655
theorem B7412381 : Blo 810345 7412381 := bstep (se 3 (by rfl) ⟨1389821, by rfl⟩ : syracuseStep 7412381 = 2779643) B2779643
theorem B1219487 : Blo 810345 1219487 := bstep (se 1 (by rfl) ⟨914615, by rfl⟩ : syracuseStep 1219487 = 1829231) B1829231
theorem B1219535 : Blo 810345 1219535 := bstep (se 1 (by rfl) ⟨914651, by rfl⟩ : syracuseStep 1219535 = 1829303) B1829303
theorem B1219625 : Blo 810345 1219625 := bstep (se 2 (by rfl) ⟨457359, by rfl⟩ : syracuseStep 1219625 = 914719) B914719
theorem B1219631 : Blo 810345 1219631 := bstep (se 1 (by rfl) ⟨914723, by rfl⟩ : syracuseStep 1219631 = 1829447) B1829447
theorem B1219655 : Blo 810345 1219655 := bstep (se 1 (by rfl) ⟨914741, by rfl⟩ : syracuseStep 1219655 = 1829483) B1829483
theorem B4627601 : Blo 810345 4627601 := bstep (se 2 (by rfl) ⟨1735350, by rfl⟩ : syracuseStep 4627601 = 3470701) B3470701
theorem B11738297 : Blo 810345 11738297 := bstep (se 2 (by rfl) ⟨4401861, by rfl⟩ : syracuseStep 11738297 = 8803723) B8803723
theorem B2923735 : Blo 810345 2923735 := bstep (se 1 (by rfl) ⟨2192801, by rfl⟩ : syracuseStep 2923735 = 4385603) B4385603
theorem B1219919 : Blo 810345 1219919 := bstep (se 1 (by rfl) ⟨914939, by rfl⟩ : syracuseStep 1219919 = 1829879) B1829879
theorem B1220009 : Blo 810345 1220009 := bstep (se 2 (by rfl) ⟨457503, by rfl⟩ : syracuseStep 1220009 = 915007) B915007
theorem B1220159 : Blo 810345 1220159 := bstep (se 1 (by rfl) ⟨915119, by rfl⟩ : syracuseStep 1220159 = 1830239) B1830239
theorem B2465527 : Blo 810345 2465527 := bstep (se 1 (by rfl) ⟨1849145, by rfl⟩ : syracuseStep 2465527 = 3698291) B3698291
theorem B1220423 : Blo 810345 1220423 := bstep (se 1 (by rfl) ⟨915317, by rfl⟩ : syracuseStep 1220423 = 1830635) B1830635
theorem B1220507 : Blo 810345 1220507 := bstep (se 1 (by rfl) ⟨915380, by rfl⟩ : syracuseStep 1220507 = 1830761) B1830761
theorem B1221071 : Blo 810345 1221071 := bstep (se 1 (by rfl) ⟨915803, by rfl⟩ : syracuseStep 1221071 = 1831607) B1831607
theorem B1221113 : Blo 810345 1221113 := bstep (se 2 (by rfl) ⟨457917, by rfl⟩ : syracuseStep 1221113 = 915835) B915835
theorem B1221215 : Blo 810345 1221215 := bstep (se 1 (by rfl) ⟨915911, by rfl⟩ : syracuseStep 1221215 = 1831823) B1831823
theorem B4105241 : Blo 810345 4105241 := bstep (se 2 (by rfl) ⟨1539465, by rfl⟩ : syracuseStep 4105241 = 3078931) B3078931
theorem B2532779 : Blo 810345 2532779 := bstep (se 1 (by rfl) ⟨1899584, by rfl⟩ : syracuseStep 2532779 = 3799169) B3799169
theorem B20326187 : Blo 810345 20326187 := bstep (se 1 (by rfl) ⟨15244640, by rfl⟩ : syracuseStep 20326187 = 30489281) B30489281
theorem B1386319 : Blo 810345 1386319 := bstep (se 1 (by rfl) ⟨1039739, by rfl⟩ : syracuseStep 1386319 = 2079479) B2079479
theorem B23471977 : Blo 810345 23471977 := bstep (se 2 (by rfl) ⟨8801991, by rfl⟩ : syracuseStep 23471977 = 17603983) B17603983
theorem B3123191 : Blo 810345 3123191 := bstep (se 1 (by rfl) ⟨2342393, by rfl⟩ : syracuseStep 3123191 = 4684787) B4684787
theorem B9251009 : Blo 810345 9251009 := bstep (se 2 (by rfl) ⟨3469128, by rfl⟩ : syracuseStep 9251009 = 6938257) B6938257
theorem B19737539 : Blo 810345 19737539 := bstep (se 1 (by rfl) ⟨14803154, by rfl⟩ : syracuseStep 19737539 = 29606309) B29606309
theorem B11905987 : Blo 810345 11905987 := bstep (se 1 (by rfl) ⟨8929490, by rfl⟩ : syracuseStep 11905987 = 17858981) B17858981
theorem B2468839 : Blo 810345 2468839 := bstep (se 1 (by rfl) ⟨1851629, by rfl⟩ : syracuseStep 2468839 = 3703259) B3703259
theorem B45755479 : Blo 810345 45755479 := bstep (se 1 (by rfl) ⟨34316609, by rfl⟩ : syracuseStep 45755479 = 68633219) B68633219
theorem B3091553 : Blo 810345 3091553 := bstep (se 2 (by rfl) ⟨1159332, by rfl⟩ : syracuseStep 3091553 = 2318665) B2318665
theorem B4893929 : Blo 810345 4893929 := bstep (se 2 (by rfl) ⟨1835223, by rfl⟩ : syracuseStep 4893929 = 3670447) B3670447
theorem B2927915 : Blo 810345 2927915 := bstep (se 1 (by rfl) ⟨2195936, by rfl⟩ : syracuseStep 2927915 = 4391873) B4391873
theorem B11873665 : Blo 810345 11873665 := bstep (se 2 (by rfl) ⟨4452624, by rfl⟩ : syracuseStep 11873665 = 8905249) B8905249
theorem B4107833 : Blo 810345 4107833 := bstep (se 2 (by rfl) ⟨1540437, by rfl⟩ : syracuseStep 4107833 = 3080875) B3080875
theorem B9252467 : Blo 810345 9252467 := bstep (se 1 (by rfl) ⟨6939350, by rfl⟩ : syracuseStep 9252467 = 13878701) B13878701
theorem B5845391 : Blo 810345 5845391 := bstep (se 1 (by rfl) ⟨4384043, by rfl⟩ : syracuseStep 5845391 = 8768087) B8768087
theorem B1389563 : Blo 810345 1389563 := bstep (se 1 (by rfl) ⟨1042172, by rfl⟩ : syracuseStep 1389563 = 2084345) B2084345
theorem B1029115 : Blo 810345 1029115 := bstep (se 1 (by rfl) ⟨771836, by rfl⟩ : syracuseStep 1029115 = 1543673) B1543673
theorem B2602667 : Blo 810345 2602667 := bstep (se 1 (by rfl) ⟨1952000, by rfl⟩ : syracuseStep 2602667 = 3904001) B3904001
theorem B8763241 : Blo 810345 8763241 := bstep (se 2 (by rfl) ⟨3286215, by rfl⟩ : syracuseStep 8763241 = 6572431) B6572431
theorem B8337289 : Blo 810345 8337289 := bstep (se 2 (by rfl) ⟨3126483, by rfl⟩ : syracuseStep 8337289 = 6252967) B6252967
theorem B1030087 : Blo 810345 1030087 := bstep (se 1 (by rfl) ⟨772565, by rfl⟩ : syracuseStep 1030087 = 1545131) B1545131
theorem B5847005 : Blo 810345 5847005 := bstep (se 3 (by rfl) ⟨1096313, by rfl⟩ : syracuseStep 5847005 = 2192627) B2192627
theorem B4634617 : Blo 810345 4634617 := bstep (se 2 (by rfl) ⟨1737981, by rfl⟩ : syracuseStep 4634617 = 3475963) B3475963
theorem B4929619 : Blo 810345 4929619 := bstep (se 1 (by rfl) ⟨3697214, by rfl⟩ : syracuseStep 4929619 = 7394429) B7394429
theorem B2308459 : Blo 810345 2308459 := bstep (se 1 (by rfl) ⟨1731344, by rfl⟩ : syracuseStep 2308459 = 3462689) B3462689
theorem B10435067 : Blo 810345 10435067 := bstep (se 1 (by rfl) ⟨7826300, by rfl⟩ : syracuseStep 10435067 = 15652601) B15652601
theorem B1391519 : Blo 810345 1391519 := bstep (se 1 (by rfl) ⟨1043639, by rfl⟩ : syracuseStep 1391519 = 2087279) B2087279
theorem B2735369 : Blo 810345 2735369 := bstep (se 2 (by rfl) ⟨1025763, by rfl⟩ : syracuseStep 2735369 = 2051527) B2051527
theorem B4111721 : Blo 810345 4111721 := bstep (se 2 (by rfl) ⟨1541895, by rfl⟩ : syracuseStep 4111721 = 3083791) B3083791
theorem B8764973 : Blo 810345 8764973 := bstep (se 3 (by rfl) ⟨1643432, by rfl⟩ : syracuseStep 8764973 = 3286865) B3286865
theorem B2604923 : Blo 810345 2604923 := bstep (se 1 (by rfl) ⟨1953692, by rfl⟩ : syracuseStep 2604923 = 3907385) B3907385
theorem B2736503 : Blo 810345 2736503 := bstep (se 1 (by rfl) ⟨2052377, by rfl⟩ : syracuseStep 2736503 = 4104755) B4104755
theorem B868735 : Blo 810345 868735 := bstep (se 1 (by rfl) ⟨651551, by rfl⟩ : syracuseStep 868735 = 1303103) B1303103
theorem B9388781 : Blo 810345 9388781 := bstep (se 3 (by rfl) ⟨1760396, by rfl⟩ : syracuseStep 9388781 = 3520793) B3520793
theorem B2605871 : Blo 810345 2605871 := bstep (se 1 (by rfl) ⟨1954403, by rfl⟩ : syracuseStep 2605871 = 3908807) B3908807
theorem B4178807 : Blo 810345 4178807 := bstep (se 1 (by rfl) ⟨3134105, by rfl⟩ : syracuseStep 4178807 = 6268211) B6268211
theorem B2311067 : Blo 810345 2311067 := bstep (se 1 (by rfl) ⟨1733300, by rfl⟩ : syracuseStep 2311067 = 3466601) B3466601
theorem B2311193 : Blo 810345 2311193 := bstep (se 2 (by rfl) ⟨866697, by rfl⟩ : syracuseStep 2311193 = 1733395) B1733395
theorem B4932733 : Blo 810345 4932733 := bstep (se 3 (by rfl) ⟨924887, by rfl⟩ : syracuseStep 4932733 = 1849775) B1849775
theorem B2311375 : Blo 810345 2311375 := bstep (se 1 (by rfl) ⟨1733531, by rfl⟩ : syracuseStep 2311375 = 3467063) B3467063
theorem B7816459 : Blo 810345 7816459 := bstep (se 1 (by rfl) ⟨5862344, by rfl⟩ : syracuseStep 7816459 = 11724689) B11724689
theorem B2737583 : Blo 810345 2737583 := bstep (se 1 (by rfl) ⟨2053187, by rfl⟩ : syracuseStep 2737583 = 4106375) B4106375
theorem B2311841 : Blo 810345 2311841 := bstep (se 2 (by rfl) ⟨866940, by rfl⟩ : syracuseStep 2311841 = 1733881) B1733881
theorem B2737961 : Blo 810345 2737961 := bstep (se 2 (by rfl) ⟨1026735, by rfl⟩ : syracuseStep 2737961 = 2053471) B2053471
theorem B379012931 : Blo 810345 379012931 := bstep (se 1 (by rfl) ⟨284259698, by rfl⟩ : syracuseStep 379012931 = 568519397) B568519397
theorem B2967425 : Blo 810345 2967425 := bstep (se 2 (by rfl) ⟨1112784, by rfl⟩ : syracuseStep 2967425 = 2225569) B2225569
theorem B56183543 : Blo 810345 56183543 := bstep (se 1 (by rfl) ⟨42137657, by rfl⟩ : syracuseStep 56183543 = 84275315) B84275315
theorem B6933883 : Blo 810345 6933883 := bstep (se 1 (by rfl) ⟨5200412, by rfl⟩ : syracuseStep 6933883 = 10400825) B10400825
theorem B1953193 : Blo 810345 1953193 := bstep (se 2 (by rfl) ⟨732447, by rfl⟩ : syracuseStep 1953193 = 1464895) B1464895
theorem B4935163 : Blo 810345 4935163 := bstep (se 1 (by rfl) ⟨3701372, by rfl⟩ : syracuseStep 4935163 = 7402745) B7402745
theorem B7818767 : Blo 810345 7818767 := bstep (se 1 (by rfl) ⟨5864075, by rfl⟩ : syracuseStep 7818767 = 11728151) B11728151
theorem B1232491 : Blo 810345 1232491 := bstep (se 1 (by rfl) ⟨924368, by rfl⟩ : syracuseStep 1232491 = 1848737) B1848737
theorem B1462055 : Blo 810345 1462055 := bstep (se 1 (by rfl) ⟨1096541, by rfl⟩ : syracuseStep 1462055 = 2193083) B2193083
theorem B5853005 : Blo 810345 5853005 := bstep (se 3 (by rfl) ⟨1097438, by rfl⟩ : syracuseStep 5853005 = 2194877) B2194877
theorem B2740175 : Blo 810345 2740175 := bstep (se 1 (by rfl) ⟨2055131, by rfl⟩ : syracuseStep 2740175 = 4110263) B4110263
theorem B8802341 : Blo 810345 8802341 := bstep (se 4 (by rfl) ⟨825219, by rfl⟩ : syracuseStep 8802341 = 1650439) B1650439
theorem B9392345 : Blo 810345 9392345 := bstep (se 2 (by rfl) ⟨3522129, by rfl⟩ : syracuseStep 9392345 = 7044259) B7044259
theorem B1298663 : Blo 810345 1298663 := bstep (se 1 (by rfl) ⟨973997, by rfl⟩ : syracuseStep 1298663 = 1947995) B1947995
theorem B2052479 : Blo 810345 2052479 := bstep (se 1 (by rfl) ⟨1539359, by rfl⟩ : syracuseStep 2052479 = 3078719) B3078719
theorem B2740607 : Blo 810345 2740607 := bstep (se 1 (by rfl) ⟨2055455, by rfl⟩ : syracuseStep 2740607 = 4110911) B4110911
theorem B1823327 : Blo 810345 1823327 := bstep (se 1 (by rfl) ⟨1367495, by rfl⟩ : syracuseStep 1823327 = 2734991) B2734991
theorem B1954991 : Blo 810345 1954991 := bstep (se 1 (by rfl) ⟨1466243, by rfl⟩ : syracuseStep 1954991 = 2932487) B2932487
theorem B4117715 : Blo 810345 4117715 := bstep (se 1 (by rfl) ⟨3088286, by rfl⟩ : syracuseStep 4117715 = 6176573) B6176573
theorem B1824155 : Blo 810345 1824155 := bstep (se 1 (by rfl) ⟨1368116, by rfl⟩ : syracuseStep 1824155 = 2736233) B2736233
theorem B9885115 : Blo 810345 9885115 := bstep (se 1 (by rfl) ⟨7413836, by rfl⟩ : syracuseStep 9885115 = 14827673) B14827673
theorem B2742011 : Blo 810345 2742011 := bstep (se 1 (by rfl) ⟨2056508, by rfl⟩ : syracuseStep 2742011 = 4113017) B4113017
theorem B3299129 : Blo 810345 3299129 := bstep (se 2 (by rfl) ⟨1237173, by rfl⟩ : syracuseStep 3299129 = 2474347) B2474347
theorem B1300303 : Blo 810345 1300303 := bstep (se 1 (by rfl) ⟨975227, by rfl⟩ : syracuseStep 1300303 = 1950455) B1950455
theorem B2742173 : Blo 810345 2742173 := bstep (se 3 (by rfl) ⟨514157, by rfl⟩ : syracuseStep 2742173 = 1028315) B1028315
theorem B1824731 : Blo 810345 1824731 := bstep (se 1 (by rfl) ⟨1368548, by rfl⟩ : syracuseStep 1824731 = 2737097) B2737097
theorem B2054119 : Blo 810345 2054119 := bstep (se 1 (by rfl) ⟨1540589, by rfl⟩ : syracuseStep 2054119 = 3081179) B3081179
theorem B1824911 : Blo 810345 1824911 := bstep (se 1 (by rfl) ⟨1368683, by rfl⟩ : syracuseStep 1824911 = 2737367) B2737367
theorem B1235099 : Blo 810345 1235099 := bstep (se 1 (by rfl) ⟨926324, by rfl⟩ : syracuseStep 1235099 = 1852649) B1852649
theorem B1824929 : Blo 810345 1824929 := bstep (se 2 (by rfl) ⟨684348, by rfl⟩ : syracuseStep 1824929 = 1368697) B1368697
theorem B1825001 : Blo 810345 1825001 := bstep (se 2 (by rfl) ⟨684375, by rfl⟩ : syracuseStep 1825001 = 1368751) B1368751
theorem B4381103 : Blo 810345 4381103 := bstep (se 1 (by rfl) ⟨3285827, by rfl⟩ : syracuseStep 4381103 = 6571655) B6571655
theorem B2743145 : Blo 810345 2743145 := bstep (se 2 (by rfl) ⟨1028679, by rfl⟩ : syracuseStep 2743145 = 2057359) B2057359
theorem B2055071 : Blo 810345 2055071 := bstep (se 1 (by rfl) ⟨1541303, by rfl⟩ : syracuseStep 2055071 = 3082607) B3082607
theorem B2743199 : Blo 810345 2743199 := bstep (se 1 (by rfl) ⟨2057399, by rfl⟩ : syracuseStep 2743199 = 4114799) B4114799
theorem B4119497 : Blo 810345 4119497 := bstep (se 2 (by rfl) ⟨1544811, by rfl⟩ : syracuseStep 4119497 = 3089623) B3089623
theorem B1301687 : Blo 810345 1301687 := bstep (se 1 (by rfl) ⟨976265, by rfl⟩ : syracuseStep 1301687 = 1952531) B1952531
theorem B5201081 : Blo 810345 5201081 := bstep (se 2 (by rfl) ⟨1950405, by rfl⟩ : syracuseStep 5201081 = 3900811) B3900811
theorem B1465609 : Blo 810345 1465609 := bstep (se 2 (by rfl) ⟨549603, by rfl⟩ : syracuseStep 1465609 = 1099207) B1099207
theorem B11099521 : Blo 810345 11099521 := bstep (se 2 (by rfl) ⟨4162320, by rfl⟩ : syracuseStep 11099521 = 8324641) B8324641
theorem B2973095 : Blo 810345 2973095 := bstep (se 1 (by rfl) ⟨2229821, by rfl⟩ : syracuseStep 2973095 = 4459643) B4459643
theorem B810471 : Blo 810345 810471 := bstep (se 1 (by rfl) ⟨607853, by rfl⟩ : syracuseStep 810471 = 1215707) B1215707
theorem B1826279 : Blo 810345 1826279 := bstep (se 1 (by rfl) ⟨1369709, by rfl⟩ : syracuseStep 1826279 = 2739419) B2739419
theorem B1367543 : Blo 810345 1367543 := bstep (se 1 (by rfl) ⟨1025657, by rfl⟩ : syracuseStep 1367543 = 2051315) B2051315
theorem B810587 : Blo 810345 810587 := bstep (se 1 (by rfl) ⟨607940, by rfl⟩ : syracuseStep 810587 = 1215881) B1215881
theorem B1564303 : Blo 810345 1564303 := bstep (se 1 (by rfl) ⟨1173227, by rfl⟩ : syracuseStep 1564303 = 2346455) B2346455
theorem B4120307 : Blo 810345 4120307 := bstep (se 1 (by rfl) ⟨3090230, by rfl⟩ : syracuseStep 4120307 = 6180461) B6180461
theorem B810823 : Blo 810345 810823 := bstep (se 1 (by rfl) ⟨608117, by rfl⟩ : syracuseStep 810823 = 1216235) B1216235
theorem B24993629 : Blo 810345 24993629 := bstep (se 3 (by rfl) ⟨4686305, by rfl⟩ : syracuseStep 24993629 = 9372611) B9372611
theorem B810975 : Blo 810345 810975 := bstep (se 1 (by rfl) ⟨608231, by rfl⟩ : syracuseStep 810975 = 1216463) B1216463
theorem B1826855 : Blo 810345 1826855 := bstep (se 1 (by rfl) ⟨1370141, by rfl⟩ : syracuseStep 1826855 = 2740283) B2740283
theorem B1827035 : Blo 810345 1827035 := bstep (se 1 (by rfl) ⟨1370276, by rfl⟩ : syracuseStep 1827035 = 2740553) B2740553
theorem B811239 : Blo 810345 811239 := bstep (se 1 (by rfl) ⟨608429, by rfl⟩ : syracuseStep 811239 = 1216859) B1216859
theorem B811391 : Blo 810345 811391 := bstep (se 1 (by rfl) ⟨608543, by rfl⟩ : syracuseStep 811391 = 1217087) B1217087
theorem B811471 : Blo 810345 811471 := bstep (se 1 (by rfl) ⟨608603, by rfl⟩ : syracuseStep 811471 = 1217207) B1217207
theorem B1827305 : Blo 810345 1827305 := bstep (se 2 (by rfl) ⟨685239, by rfl⟩ : syracuseStep 1827305 = 1370479) B1370479
theorem B1368569 : Blo 810345 1368569 := bstep (se 2 (by rfl) ⟨513213, by rfl⟩ : syracuseStep 1368569 = 1026427) B1026427
theorem B811623 : Blo 810345 811623 := bstep (se 1 (by rfl) ⟨608717, by rfl⟩ : syracuseStep 811623 = 1217435) B1217435
theorem B1368839 : Blo 810345 1368839 := bstep (se 1 (by rfl) ⟨1026629, by rfl⟩ : syracuseStep 1368839 = 2053259) B2053259
theorem B1827593 : Blo 810345 1827593 := bstep (se 2 (by rfl) ⟨685347, by rfl⟩ : syracuseStep 1827593 = 1370695) B1370695
theorem B811887 : Blo 810345 811887 := bstep (se 1 (by rfl) ⟨608915, by rfl⟩ : syracuseStep 811887 = 1217831) B1217831
theorem B975727 : Blo 810345 975727 := bstep (se 1 (by rfl) ⟨731795, by rfl⟩ : syracuseStep 975727 = 1463591) B1463591
theorem B811943 : Blo 810345 811943 := bstep (se 1 (by rfl) ⟨608957, by rfl⟩ : syracuseStep 811943 = 1217915) B1217915
theorem B812027 : Blo 810345 812027 := bstep (se 1 (by rfl) ⟨609020, by rfl⟩ : syracuseStep 812027 = 1218041) B1218041
theorem B812095 : Blo 810345 812095 := bstep (se 1 (by rfl) ⟨609071, by rfl⟩ : syracuseStep 812095 = 1218143) B1218143
theorem B2745467 : Blo 810345 2745467 := bstep (se 1 (by rfl) ⟨2059100, by rfl⟩ : syracuseStep 2745467 = 4118201) B4118201
theorem B812239 : Blo 810345 812239 := bstep (se 1 (by rfl) ⟨609179, by rfl⟩ : syracuseStep 812239 = 1218359) B1218359
theorem B1828169 : Blo 810345 1828169 := bstep (se 2 (by rfl) ⟨685563, by rfl⟩ : syracuseStep 1828169 = 1371127) B1371127
theorem B2745737 : Blo 810345 2745737 := bstep (se 2 (by rfl) ⟨1029651, by rfl⟩ : syracuseStep 2745737 = 2059303) B2059303
theorem B812443 : Blo 810345 812443 := bstep (se 1 (by rfl) ⟨609332, by rfl⟩ : syracuseStep 812443 = 1218665) B1218665
theorem B812655 : Blo 810345 812655 := bstep (se 1 (by rfl) ⟨609491, by rfl⟩ : syracuseStep 812655 = 1218983) B1218983
theorem B812711 : Blo 810345 812711 := bstep (se 1 (by rfl) ⟨609533, by rfl⟩ : syracuseStep 812711 = 1219067) B1219067
theorem B812795 : Blo 810345 812795 := bstep (se 1 (by rfl) ⟨609596, by rfl⟩ : syracuseStep 812795 = 1219193) B1219193
theorem B4384543 : Blo 810345 4384543 := bstep (se 1 (by rfl) ⟨3288407, by rfl⟩ : syracuseStep 4384543 = 6576815) B6576815
theorem B812831 : Blo 810345 812831 := bstep (se 1 (by rfl) ⟨609623, by rfl⟩ : syracuseStep 812831 = 1219247) B1219247
theorem B1369919 : Blo 810345 1369919 := bstep (se 1 (by rfl) ⟨1027439, by rfl⟩ : syracuseStep 1369919 = 2054879) B2054879
theorem B812863 : Blo 810345 812863 := bstep (se 1 (by rfl) ⟨609647, by rfl⟩ : syracuseStep 812863 = 1219295) B1219295
theorem B1369993 : Blo 810345 1369993 := bstep (se 2 (by rfl) ⟨513747, by rfl⟩ : syracuseStep 1369993 = 1027495) B1027495
theorem B813039 : Blo 810345 813039 := bstep (se 1 (by rfl) ⟨609779, by rfl⟩ : syracuseStep 813039 = 1219559) B1219559
theorem B2746493 : Blo 810345 2746493 := bstep (se 3 (by rfl) ⟨514967, by rfl⟩ : syracuseStep 2746493 = 1029935) B1029935
theorem B813211 : Blo 810345 813211 := bstep (se 1 (by rfl) ⟨609908, by rfl⟩ : syracuseStep 813211 = 1219817) B1219817
theorem B813247 : Blo 810345 813247 := bstep (se 1 (by rfl) ⟨609935, by rfl⟩ : syracuseStep 813247 = 1219871) B1219871
theorem B1829159 : Blo 810345 1829159 := bstep (se 1 (by rfl) ⟨1371869, by rfl⟩ : syracuseStep 1829159 = 2743739) B2743739
theorem B813359 : Blo 810345 813359 := bstep (se 1 (by rfl) ⟨610019, by rfl⟩ : syracuseStep 813359 = 1220039) B1220039
theorem B1370425 : Blo 810345 1370425 := bstep (se 2 (by rfl) ⟨513909, by rfl⟩ : syracuseStep 1370425 = 1027819) B1027819
theorem B1829177 : Blo 810345 1829177 := bstep (se 2 (by rfl) ⟨685941, by rfl⟩ : syracuseStep 1829177 = 1371883) B1371883
theorem B2058635 : Blo 810345 2058635 := bstep (se 1 (by rfl) ⟨1543976, by rfl⟩ : syracuseStep 2058635 = 3087953) B3087953
theorem B2746763 : Blo 810345 2746763 := bstep (se 1 (by rfl) ⟨2060072, by rfl⟩ : syracuseStep 2746763 = 4120145) B4120145
theorem B23685605 : Blo 810345 23685605 := bstep (se 4 (by rfl) ⟨2220525, by rfl⟩ : syracuseStep 23685605 = 4441051) B4441051
theorem B1731079 : Blo 810345 1731079 := bstep (se 1 (by rfl) ⟨1298309, by rfl⟩ : syracuseStep 1731079 = 2596619) B2596619
theorem B9234971 : Blo 810345 9234971 := bstep (se 1 (by rfl) ⟨6926228, by rfl⟩ : syracuseStep 9234971 = 13852457) B13852457
theorem B813595 : Blo 810345 813595 := bstep (se 1 (by rfl) ⟨610196, by rfl⟩ : syracuseStep 813595 = 1220393) B1220393
theorem B813599 : Blo 810345 813599 := bstep (se 1 (by rfl) ⟨610199, by rfl⟩ : syracuseStep 813599 = 1220399) B1220399
theorem B1370729 : Blo 810345 1370729 := bstep (se 2 (by rfl) ⟨514023, by rfl⟩ : syracuseStep 1370729 = 1028047) B1028047
theorem B813915 : Blo 810345 813915 := bstep (se 1 (by rfl) ⟨610436, by rfl⟩ : syracuseStep 813915 = 1220873) B1220873
theorem B813983 : Blo 810345 813983 := bstep (se 1 (by rfl) ⟨610487, by rfl⟩ : syracuseStep 813983 = 1220975) B1220975
theorem B4385755 : Blo 810345 4385755 := bstep (se 1 (by rfl) ⟨3289316, by rfl⟩ : syracuseStep 4385755 = 6578633) B6578633
theorem B814127 : Blo 810345 814127 := bstep (se 1 (by rfl) ⟨610595, by rfl⟩ : syracuseStep 814127 = 1221191) B1221191
theorem B814151 : Blo 810345 814151 := bstep (se 1 (by rfl) ⟨610613, by rfl⟩ : syracuseStep 814151 = 1221227) B1221227
theorem B4385927 : Blo 810345 4385927 := bstep (se 1 (by rfl) ⟨3289445, by rfl⟩ : syracuseStep 4385927 = 6578891) B6578891
theorem B814303 : Blo 810345 814303 := bstep (se 1 (by rfl) ⟨610727, by rfl⟩ : syracuseStep 814303 = 1221455) B1221455
theorem B53472545 : Blo 810345 53472545 := bstep (se 2 (by rfl) ⟨20052204, by rfl⟩ : syracuseStep 53472545 = 40104409) B40104409
theorem B11103641 : Blo 810345 11103641 := bstep (se 2 (by rfl) ⟨4163865, by rfl⟩ : syracuseStep 11103641 = 8327731) B8327731
theorem B1371559 : Blo 810345 1371559 := bstep (se 1 (by rfl) ⟨1028669, by rfl⟩ : syracuseStep 1371559 = 2057339) B2057339
theorem B1371721 : Blo 810345 1371721 := bstep (se 2 (by rfl) ⟨514395, by rfl⟩ : syracuseStep 1371721 = 1028791) B1028791
theorem B1830473 : Blo 810345 1830473 := bstep (se 2 (by rfl) ⟨686427, by rfl⟩ : syracuseStep 1830473 = 1372855) B1372855
theorem B1371755 : Blo 810345 1371755 := bstep (se 1 (by rfl) ⟨1028816, by rfl⟩ : syracuseStep 1371755 = 2057633) B2057633
theorem B2059951 : Blo 810345 2059951 := bstep (se 1 (by rfl) ⟨1544963, by rfl⟩ : syracuseStep 2059951 = 3089927) B3089927
theorem B1372025 : Blo 810345 1372025 := bstep (se 2 (by rfl) ⟨514509, by rfl⟩ : syracuseStep 1372025 = 1029019) B1029019
theorem B2781067 : Blo 810345 2781067 := bstep (se 1 (by rfl) ⟨2085800, by rfl⟩ : syracuseStep 2781067 = 4171601) B4171601
theorem B2060255 : Blo 810345 2060255 := bstep (se 1 (by rfl) ⟨1545191, by rfl⟩ : syracuseStep 2060255 = 3090383) B3090383
theorem B2748383 : Blo 810345 2748383 := bstep (se 1 (by rfl) ⟨2061287, by rfl⟩ : syracuseStep 2748383 = 4122575) B4122575
theorem B2060275 : Blo 810345 2060275 := bstep (se 1 (by rfl) ⟨1545206, by rfl⟩ : syracuseStep 2060275 = 3090413) B3090413
theorem B913639 : Blo 810345 913639 := bstep (se 1 (by rfl) ⟨685229, by rfl⟩ : syracuseStep 913639 = 1370459) B1370459
theorem B2060599 : Blo 810345 2060599 := bstep (se 1 (by rfl) ⟨1545449, by rfl⟩ : syracuseStep 2060599 = 3090899) B3090899
theorem B2060903 : Blo 810345 2060903 := bstep (se 1 (by rfl) ⟨1545677, by rfl⟩ : syracuseStep 2060903 = 3091355) B3091355
theorem B152466137 : Blo 810345 152466137 := bstep (se 2 (by rfl) ⟨57174801, by rfl⟩ : syracuseStep 152466137 = 114349603) B114349603
theorem B11104991 : Blo 810345 11104991 := bstep (se 1 (by rfl) ⟨8328743, by rfl⟩ : syracuseStep 11104991 = 16657487) B16657487
theorem B914287 : Blo 810345 914287 := bstep (se 1 (by rfl) ⟨685715, by rfl⟩ : syracuseStep 914287 = 1371431) B1371431
theorem B4617121 : Blo 810345 4617121 := bstep (se 2 (by rfl) ⟨1731420, by rfl⟩ : syracuseStep 4617121 = 3462841) B3462841
theorem B1373179 : Blo 810345 1373179 := bstep (se 1 (by rfl) ⟨1029884, by rfl⟩ : syracuseStep 1373179 = 2059769) B2059769
theorem B1831931 : Blo 810345 1831931 := bstep (se 1 (by rfl) ⟨1373948, by rfl⟩ : syracuseStep 1831931 = 2747897) B2747897
theorem B5207179 : Blo 810345 5207179 := bstep (se 1 (by rfl) ⟨3905384, by rfl⟩ : syracuseStep 5207179 = 7810769) B7810769
theorem B1832111 : Blo 810345 1832111 := bstep (se 1 (by rfl) ⟨1374083, by rfl⟩ : syracuseStep 1832111 = 2748167) B2748167
theorem B1832147 : Blo 810345 1832147 := bstep (se 1 (by rfl) ⟨1374110, by rfl⟩ : syracuseStep 1832147 = 2748221) B2748221
theorem B6157619 : Blo 810345 6157619 := bstep (se 1 (by rfl) ⟨4618214, by rfl⟩ : syracuseStep 6157619 = 9236429) B9236429
theorem B3700097 : Blo 810345 3700097 := bstep (se 2 (by rfl) ⟨1387536, by rfl⟩ : syracuseStep 3700097 = 2775073) B2775073
theorem B1373611 : Blo 810345 1373611 := bstep (se 1 (by rfl) ⟨1030208, by rfl⟩ : syracuseStep 1373611 = 2060417) B2060417
theorem B1373807 : Blo 810345 1373807 := bstep (se 1 (by rfl) ⟨1030355, by rfl⟩ : syracuseStep 1373807 = 2060711) B2060711
theorem B1373915 : Blo 810345 1373915 := bstep (se 1 (by rfl) ⟨1030436, by rfl⟩ : syracuseStep 1373915 = 2060873) B2060873
theorem B1374151 : Blo 810345 1374151 := bstep (se 1 (by rfl) ⟨1030613, by rfl⟩ : syracuseStep 1374151 = 2061227) B2061227
theorem B915439 : Blo 810345 915439 := bstep (se 1 (by rfl) ⟨686579, by rfl⟩ : syracuseStep 915439 = 1373159) B1373159
theorem B3471659 : Blo 810345 3471659 := bstep (se 1 (by rfl) ⟨2603744, by rfl⟩ : syracuseStep 3471659 = 5207489) B5207489
theorem B71236367 : Blo 810345 71236367 := bstep (se 1 (by rfl) ⟨53427275, by rfl⟩ : syracuseStep 71236367 = 106854551) B106854551
theorem B23755639 : Blo 810345 23755639 := bstep (se 1 (by rfl) ⟨17816729, by rfl⟩ : syracuseStep 23755639 = 35633459) B35633459
theorem B3079417 : Blo 810345 3079417 := bstep (se 2 (by rfl) ⟨1154781, by rfl⟩ : syracuseStep 3079417 = 2309563) B2309563
theorem B1539337 : Blo 810345 1539337 := bstep (se 2 (by rfl) ⟨577251, by rfl⟩ : syracuseStep 1539337 = 1154503) B1154503
theorem B5865227 : Blo 810345 5865227 := bstep (se 1 (by rfl) ⟨4398920, by rfl⟩ : syracuseStep 5865227 = 8797841) B8797841
theorem B5210027 : Blo 810345 5210027 := bstep (se 1 (by rfl) ⟨3907520, by rfl⟩ : syracuseStep 5210027 = 7815041) B7815041
theorem B11862443 : Blo 810345 11862443 := bstep (se 1 (by rfl) ⟨8896832, by rfl⟩ : syracuseStep 11862443 = 17793665) B17793665
theorem B3080663 : Blo 810345 3080663 := bstep (se 1 (by rfl) ⟨2310497, by rfl⟩ : syracuseStep 3080663 = 4620995) B4620995
theorem B6259187 : Blo 810345 6259187 := bstep (se 1 (by rfl) ⟨4694390, by rfl⟩ : syracuseStep 6259187 = 9388781) B9388781
theorem B2785871 : Blo 810345 2785871 := bstep (se 1 (by rfl) ⟨2089403, by rfl⟩ : syracuseStep 2785871 = 4178807) B4178807
theorem B1540711 : Blo 810345 1540711 := bstep (se 1 (by rfl) ⟨1155533, by rfl⟩ : syracuseStep 1540711 = 2311067) B2311067
theorem B1540795 : Blo 810345 1540795 := bstep (se 1 (by rfl) ⟨1155596, by rfl⟩ : syracuseStep 1540795 = 2311193) B2311193
theorem B252675287 : Blo 810345 252675287 := bstep (se 1 (by rfl) ⟨189506465, by rfl⟩ : syracuseStep 252675287 = 379012931) B379012931
theorem B3081833 : Blo 810345 3081833 := bstep (se 2 (by rfl) ⟨1155687, by rfl⟩ : syracuseStep 3081833 = 2311375) B2311375
theorem B10421945 : Blo 810345 10421945 := bstep (se 2 (by rfl) ⟨3908229, by rfl⟩ : syracuseStep 10421945 = 7816459) B7816459
theorem B37455695 : Blo 810345 37455695 := bstep (se 1 (by rfl) ⟨28091771, by rfl⟩ : syracuseStep 37455695 = 56183543) B56183543
theorem B6948989 : Blo 810345 6948989 := bstep (se 3 (by rfl) ⟨1302935, by rfl⟩ : syracuseStep 6948989 = 2605871) B2605871
theorem B5212511 : Blo 810345 5212511 := bstep (se 1 (by rfl) ⟨3909383, by rfl⟩ : syracuseStep 5212511 = 7818767) B7818767
theorem B31295969 : Blo 810345 31295969 := bstep (se 2 (by rfl) ⟨11735988, by rfl⟩ : syracuseStep 31295969 = 23471977) B23471977
theorem B3902003 : Blo 810345 3902003 := bstep (se 1 (by rfl) ⟨2926502, by rfl⟩ : syracuseStep 3902003 = 5853005) B5853005
theorem B5868227 : Blo 810345 5868227 := bstep (se 1 (by rfl) ⟨4401170, by rfl⟩ : syracuseStep 5868227 = 8802341) B8802341
theorem B6261563 : Blo 810345 6261563 := bstep (se 1 (by rfl) ⟨4696172, by rfl⟩ : syracuseStep 6261563 = 9392345) B9392345
theorem B1215551 : Blo 810345 1215551 := bstep (se 1 (by rfl) ⟨911663, by rfl⟩ : syracuseStep 1215551 = 1823327) B1823327
theorem B6163937 : Blo 810345 6163937 := bstep (se 2 (by rfl) ⟨2311476, by rfl⟩ : syracuseStep 6163937 = 4622953) B4622953
theorem B1216103 : Blo 810345 1216103 := bstep (se 1 (by rfl) ⟨912077, by rfl⟩ : syracuseStep 1216103 = 1824155) B1824155
theorem B10554995 : Blo 810345 10554995 := bstep (se 1 (by rfl) ⟨7916246, by rfl⟩ : syracuseStep 10554995 = 15832493) B15832493
theorem B2199419 : Blo 810345 2199419 := bstep (se 1 (by rfl) ⟨1649564, by rfl⟩ : syracuseStep 2199419 = 3299129) B3299129
theorem B1216487 : Blo 810345 1216487 := bstep (se 1 (by rfl) ⟨912365, by rfl⟩ : syracuseStep 1216487 = 1824731) B1824731
theorem B1216607 : Blo 810345 1216607 := bstep (se 1 (by rfl) ⟨912455, by rfl⟩ : syracuseStep 1216607 = 1824911) B1824911
theorem B1216619 : Blo 810345 1216619 := bstep (se 1 (by rfl) ⟨912464, by rfl⟩ : syracuseStep 1216619 = 1824929) B1824929
theorem B1216667 : Blo 810345 1216667 := bstep (se 1 (by rfl) ⟨912500, by rfl⟩ : syracuseStep 1216667 = 1825001) B1825001
theorem B2920735 : Blo 810345 2920735 := bstep (se 1 (by rfl) ⟨2190551, by rfl⟩ : syracuseStep 2920735 = 4381103) B4381103
theorem B6164909 : Blo 810345 6164909 := bstep (se 3 (by rfl) ⟨1155920, by rfl⟩ : syracuseStep 6164909 = 2311841) B2311841
theorem B9245177 : Blo 810345 9245177 := bstep (se 2 (by rfl) ⟨3466941, by rfl⟩ : syracuseStep 9245177 = 6933883) B6933883
theorem B15831553 : Blo 810345 15831553 := bstep (se 2 (by rfl) ⟨5936832, by rfl⟩ : syracuseStep 15831553 = 11873665) B11873665
theorem B3085067 : Blo 810345 3085067 := bstep (se 1 (by rfl) ⟨2313800, by rfl⟩ : syracuseStep 3085067 = 4627601) B4627601
theorem B54203165 : Blo 810345 54203165 := bstep (se 3 (by rfl) ⟨10163093, by rfl⟩ : syracuseStep 54203165 = 20326187) B20326187
theorem B1643321 : Blo 810345 1643321 := bstep (se 2 (by rfl) ⟨616245, by rfl⟩ : syracuseStep 1643321 = 1232491) B1232491
theorem B1217519 : Blo 810345 1217519 := bstep (se 1 (by rfl) ⟨913139, by rfl⟩ : syracuseStep 1217519 = 1826279) B1826279
theorem B3708089 : Blo 810345 3708089 := bstep (se 2 (by rfl) ⟨1390533, by rfl⟩ : syracuseStep 3708089 = 2781067) B2781067
theorem B1217903 : Blo 810345 1217903 := bstep (se 1 (by rfl) ⟨913427, by rfl⟩ : syracuseStep 1217903 = 1826855) B1826855
theorem B1218023 : Blo 810345 1218023 := bstep (se 1 (by rfl) ⟨913517, by rfl⟩ : syracuseStep 1218023 = 1827035) B1827035
theorem B1218185 : Blo 810345 1218185 := bstep (se 2 (by rfl) ⟨456819, by rfl⟩ : syracuseStep 1218185 = 913639) B913639
theorem B1218203 : Blo 810345 1218203 := bstep (se 1 (by rfl) ⟨913652, by rfl⟩ : syracuseStep 1218203 = 1827305) B1827305
theorem B1218395 : Blo 810345 1218395 := bstep (se 1 (by rfl) ⟨913796, by rfl⟩ : syracuseStep 1218395 = 1827593) B1827593
theorem B1218779 : Blo 810345 1218779 := bstep (se 1 (by rfl) ⟨914084, by rfl⟩ : syracuseStep 1218779 = 1828169) B1828169
theorem B1219049 : Blo 810345 1219049 := bstep (se 2 (by rfl) ⟨457143, by rfl⟩ : syracuseStep 1219049 = 914287) B914287
theorem B6167339 : Blo 810345 6167339 := bstep (se 1 (by rfl) ⟨4625504, by rfl⟩ : syracuseStep 6167339 = 9251009) B9251009
theorem B1219439 : Blo 810345 1219439 := bstep (se 1 (by rfl) ⟨914579, by rfl⟩ : syracuseStep 1219439 = 1829159) B1829159
theorem B1219451 : Blo 810345 1219451 := bstep (se 1 (by rfl) ⟨914588, by rfl⟩ : syracuseStep 1219451 = 1829177) B1829177
theorem B6954113 : Blo 810345 6954113 := bstep (se 2 (by rfl) ⟨2607792, by rfl⟩ : syracuseStep 6954113 = 5215585) B5215585
theorem B13180153 : Blo 810345 13180153 := bstep (se 2 (by rfl) ⟨4942557, by rfl⟩ : syracuseStep 13180153 = 9885115) B9885115
theorem B2923951 : Blo 810345 2923951 := bstep (se 1 (by rfl) ⟨2192963, by rfl⟩ : syracuseStep 2923951 = 4385927) B4385927
theorem B1220315 : Blo 810345 1220315 := bstep (se 1 (by rfl) ⟨915236, by rfl⟩ : syracuseStep 1220315 = 1830473) B1830473
theorem B6168311 : Blo 810345 6168311 := bstep (se 1 (by rfl) ⟨4626233, by rfl⟩ : syracuseStep 6168311 = 9252467) B9252467
theorem B11116385 : Blo 810345 11116385 := bstep (se 2 (by rfl) ⟨4168644, by rfl⟩ : syracuseStep 11116385 = 8337289) B8337289
theorem B1220585 : Blo 810345 1220585 := bstep (se 2 (by rfl) ⟨457719, by rfl⟩ : syracuseStep 1220585 = 915439) B915439
theorem B926375 : Blo 810345 926375 := bstep (se 1 (by rfl) ⟨694781, by rfl⟩ : syracuseStep 926375 = 1389563) B1389563
theorem B1221287 : Blo 810345 1221287 := bstep (se 1 (by rfl) ⟨915965, by rfl⟩ : syracuseStep 1221287 = 1831931) B1831931
theorem B1221407 : Blo 810345 1221407 := bstep (se 1 (by rfl) ⟨916055, by rfl⟩ : syracuseStep 1221407 = 1832111) B1832111
theorem B1221431 : Blo 810345 1221431 := bstep (se 1 (by rfl) ⟨916073, by rfl⟩ : syracuseStep 1221431 = 1832147) B1832147
theorem B4105079 : Blo 810345 4105079 := bstep (se 1 (by rfl) ⟨3078809, by rfl⟩ : syracuseStep 4105079 = 6157619) B6157619
theorem B2466731 : Blo 810345 2466731 := bstep (se 1 (by rfl) ⟨1850048, by rfl⟩ : syracuseStep 2466731 = 3700097) B3700097
theorem B4105889 : Blo 810345 4105889 := bstep (se 2 (by rfl) ⟨1539708, by rfl⟩ : syracuseStep 4105889 = 3079417) B3079417
theorem B6956711 : Blo 810345 6956711 := bstep (se 1 (by rfl) ⟨5217533, by rfl⟩ : syracuseStep 6956711 = 10435067) B10435067
theorem B47490911 : Blo 810345 47490911 := bstep (se 1 (by rfl) ⟨35618183, by rfl⟩ : syracuseStep 47490911 = 71236367) B71236367
theorem B927679 : Blo 810345 927679 := bstep (se 1 (by rfl) ⟨695759, by rfl⟩ : syracuseStep 927679 = 1391519) B1391519
theorem B3287369 : Blo 810345 3287369 := bstep (se 2 (by rfl) ⟨1232763, by rfl⟩ : syracuseStep 3287369 = 2465527) B2465527
theorem B5843315 : Blo 810345 5843315 := bstep (se 1 (by rfl) ⟨4382486, by rfl⟩ : syracuseStep 5843315 = 8764973) B8764973
theorem B3910151 : Blo 810345 3910151 := bstep (se 1 (by rfl) ⟨2932613, by rfl⟩ : syracuseStep 3910151 = 5865227) B5865227
theorem B4631519 : Blo 810345 4631519 := bstep (se 1 (by rfl) ⟨3473639, by rfl⟩ : syracuseStep 4631519 = 6947279) B6947279
theorem B1158313 : Blo 810345 1158313 := bstep (se 2 (by rfl) ⟨434367, by rfl⟩ : syracuseStep 1158313 = 868735) B868735
theorem B6336001 : Blo 810345 6336001 := bstep (se 2 (by rfl) ⟨2376000, by rfl⟩ : syracuseStep 6336001 = 4752001) B4752001
theorem B5549627 : Blo 810345 5549627 := bstep (se 1 (by rfl) ⟨4162220, by rfl⟩ : syracuseStep 5549627 = 8324441) B8324441
theorem B4108157 : Blo 810345 4108157 := bstep (se 3 (by rfl) ⟨770279, by rfl⟩ : syracuseStep 4108157 = 1540559) B1540559
theorem B1978283 : Blo 810345 1978283 := bstep (se 1 (by rfl) ⟨1483712, by rfl⟩ : syracuseStep 1978283 = 2967425) B2967425
theorem B3125375 : Blo 810345 3125375 := bstep (se 1 (by rfl) ⟨2344031, by rfl⟩ : syracuseStep 3125375 = 4688063) B4688063
theorem B5846057 : Blo 810345 5846057 := bstep (se 2 (by rfl) ⟨2192271, by rfl⟩ : syracuseStep 5846057 = 4384543) B4384543
theorem B1848425 : Blo 810345 1848425 := bstep (se 2 (by rfl) ⟨693159, by rfl⟩ : syracuseStep 1848425 = 1386319) B1386319
theorem B1029439 : Blo 810345 1029439 := bstep (se 1 (by rfl) ⟨772079, by rfl⟩ : syracuseStep 1029439 = 1544159) B1544159
theorem B865775 : Blo 810345 865775 := bstep (se 1 (by rfl) ⟨649331, by rfl⟩ : syracuseStep 865775 = 1298663) B1298663
theorem B2308105 : Blo 810345 2308105 := bstep (se 2 (by rfl) ⟨865539, by rfl⟩ : syracuseStep 2308105 = 1731079) B1731079
theorem B4635143 : Blo 810345 4635143 := bstep (se 1 (by rfl) ⟨3476357, by rfl⟩ : syracuseStep 4635143 = 6952715) B6952715
theorem B15874649 : Blo 810345 15874649 := bstep (se 2 (by rfl) ⟨5952993, by rfl⟩ : syracuseStep 15874649 = 11905987) B11905987
theorem B5847673 : Blo 810345 5847673 := bstep (se 2 (by rfl) ⟨2192877, by rfl⟩ : syracuseStep 5847673 = 4385755) B4385755
theorem B3291785 : Blo 810345 3291785 := bstep (se 2 (by rfl) ⟨1234419, by rfl⟩ : syracuseStep 3291785 = 2468839) B2468839
theorem B2604257 : Blo 810345 2604257 := bstep (se 2 (by rfl) ⟨976596, by rfl⟩ : syracuseStep 2604257 = 1953193) B1953193
theorem B867791 : Blo 810345 867791 := bstep (se 1 (by rfl) ⟨650843, by rfl⟩ : syracuseStep 867791 = 1301687) B1301687
theorem B1982063 : Blo 810345 1982063 := bstep (se 1 (by rfl) ⟨1486547, by rfl⟩ : syracuseStep 1982063 = 2973095) B2973095
theorem B16662419 : Blo 810345 16662419 := bstep (se 1 (by rfl) ⟨12496814, by rfl⟩ : syracuseStep 16662419 = 24993629) B24993629
theorem B18792809 : Blo 810345 18792809 := bstep (se 2 (by rfl) ⟨7047303, by rfl⟩ : syracuseStep 18792809 = 14094607) B14094607
theorem B3293597 : Blo 810345 3293597 := bstep (se 3 (by rfl) ⟨617549, by rfl⟩ : syracuseStep 3293597 = 1235099) B1235099
theorem B2736827 : Blo 810345 2736827 := bstep (se 1 (by rfl) ⟨2052620, by rfl⟩ : syracuseStep 2736827 = 4105241) B4105241
theorem B1688519 : Blo 810345 1688519 := bstep (se 1 (by rfl) ⟨1266389, by rfl⟩ : syracuseStep 1688519 = 2532779) B2532779
theorem B2082127 : Blo 810345 2082127 := bstep (se 1 (by rfl) ⟨1561595, by rfl⟩ : syracuseStep 2082127 = 3123191) B3123191
theorem B5555561 : Blo 810345 5555561 := bstep (se 2 (by rfl) ⟨2083335, by rfl⟩ : syracuseStep 5555561 = 4166671) B4166671
theorem B13158359 : Blo 810345 13158359 := bstep (se 1 (by rfl) ⟨9868769, by rfl⟩ : syracuseStep 13158359 = 19737539) B19737539
theorem B3262619 : Blo 810345 3262619 := bstep (se 1 (by rfl) ⟨2446964, by rfl⟩ : syracuseStep 3262619 = 4893929) B4893929
theorem B1951943 : Blo 810345 1951943 := bstep (se 1 (by rfl) ⟨1463957, by rfl⟩ : syracuseStep 1951943 = 2927915) B2927915
theorem B2738555 : Blo 810345 2738555 := bstep (se 1 (by rfl) ⟨2053916, by rfl⟩ : syracuseStep 2738555 = 4107833) B4107833
theorem B11684321 : Blo 810345 11684321 := bstep (se 2 (by rfl) ⟨4381620, by rfl⟩ : syracuseStep 11684321 = 8763241) B8763241
theorem B2738825 : Blo 810345 2738825 := bstep (se 2 (by rfl) ⟨1027059, by rfl⟩ : syracuseStep 2738825 = 2054119) B2054119
theorem B6179489 : Blo 810345 6179489 := bstep (se 2 (by rfl) ⟨2317308, by rfl⟩ : syracuseStep 6179489 = 4634617) B4634617
theorem B6572825 : Blo 810345 6572825 := bstep (se 2 (by rfl) ⟨2464809, by rfl⟩ : syracuseStep 6572825 = 4929619) B4929619
theorem B31674185 : Blo 810345 31674185 := bstep (se 2 (by rfl) ⟨11877819, by rfl⟩ : syracuseStep 31674185 = 23755639) B23755639
theorem B2314439 : Blo 810345 2314439 := bstep (se 1 (by rfl) ⟨1735829, by rfl⟩ : syracuseStep 2314439 = 3471659) B3471659
theorem B2052449 : Blo 810345 2052449 := bstep (se 2 (by rfl) ⟨769668, by rfl⟩ : syracuseStep 2052449 = 1539337) B1539337
theorem B1954145 : Blo 810345 1954145 := bstep (se 2 (by rfl) ⟨732804, by rfl⟩ : syracuseStep 1954145 = 1465609) B1465609
theorem B14799361 : Blo 810345 14799361 := bstep (se 2 (by rfl) ⟨5549760, by rfl⟩ : syracuseStep 14799361 = 11099521) B11099521
theorem B1823579 : Blo 810345 1823579 := bstep (se 1 (by rfl) ⟨1367684, by rfl⟩ : syracuseStep 1823579 = 2735369) B2735369
theorem B2741147 : Blo 810345 2741147 := bstep (se 1 (by rfl) ⟨2055860, by rfl⟩ : syracuseStep 2741147 = 4111721) B4111721
theorem B1824335 : Blo 810345 1824335 := bstep (se 1 (by rfl) ⟨1368251, by rfl⟩ : syracuseStep 1824335 = 2736503) B2736503
theorem B2315897 : Blo 810345 2315897 := bstep (se 2 (by rfl) ⟨868461, by rfl⟩ : syracuseStep 2315897 = 1736923) B1736923
theorem B7821305 : Blo 810345 7821305 := bstep (se 2 (by rfl) ⟨2932989, by rfl⟩ : syracuseStep 7821305 = 5865979) B5865979
theorem B1825055 : Blo 810345 1825055 := bstep (se 1 (by rfl) ⟨1368791, by rfl⟩ : syracuseStep 1825055 = 2737583) B2737583
theorem B1300969 : Blo 810345 1300969 := bstep (se 2 (by rfl) ⟨487863, by rfl⟩ : syracuseStep 1300969 = 975727) B975727
theorem B1825307 : Blo 810345 1825307 := bstep (se 1 (by rfl) ⟨1368980, by rfl⟩ : syracuseStep 1825307 = 2737961) B2737961
theorem B133487189 : Blo 810345 133487189 := bstep (se 8 (by rfl) ⟨782151, by rfl⟩ : syracuseStep 133487189 = 1564303) B1564303
theorem B6576977 : Blo 810345 6576977 := bstep (se 2 (by rfl) ⟨2466366, by rfl⟩ : syracuseStep 6576977 = 4932733) B4932733
theorem B9264131 : Blo 810345 9264131 := bstep (se 1 (by rfl) ⟨6948098, by rfl⟩ : syracuseStep 9264131 = 13896197) B13896197
theorem B810447 : Blo 810345 810447 := bstep (se 1 (by rfl) ⟨607835, by rfl⟩ : syracuseStep 810447 = 1215671) B1215671
theorem B810607 : Blo 810345 810607 := bstep (se 1 (by rfl) ⟨607955, by rfl⟩ : syracuseStep 810607 = 1215911) B1215911
theorem B810663 : Blo 810345 810663 := bstep (se 1 (by rfl) ⟨607997, by rfl⟩ : syracuseStep 810663 = 1215995) B1215995
theorem B810727 : Blo 810345 810727 := bstep (se 1 (by rfl) ⟨608045, by rfl⟩ : syracuseStep 810727 = 1216091) B1216091
theorem B810783 : Blo 810345 810783 := bstep (se 1 (by rfl) ⟨608087, by rfl⟩ : syracuseStep 810783 = 1216175) B1216175
theorem B1826657 : Blo 810345 1826657 := bstep (se 2 (by rfl) ⟨684996, by rfl⟩ : syracuseStep 1826657 = 1369993) B1369993
theorem B810863 : Blo 810345 810863 := bstep (se 1 (by rfl) ⟨608147, by rfl⟩ : syracuseStep 810863 = 1216295) B1216295
theorem B810919 : Blo 810345 810919 := bstep (se 1 (by rfl) ⟨608189, by rfl⟩ : syracuseStep 810919 = 1216379) B1216379
theorem B252731339 : Blo 810345 252731339 := bstep (se 1 (by rfl) ⟨189548504, by rfl⟩ : syracuseStep 252731339 = 379097009) B379097009
theorem B1826783 : Blo 810345 1826783 := bstep (se 1 (by rfl) ⟨1370087, by rfl⟩ : syracuseStep 1826783 = 2740175) B2740175
theorem B811199 : Blo 810345 811199 := bstep (se 1 (by rfl) ⟨608399, by rfl⟩ : syracuseStep 811199 = 1216799) B1216799
theorem B811215 : Blo 810345 811215 := bstep (se 1 (by rfl) ⟨608411, by rfl⟩ : syracuseStep 811215 = 1216823) B1216823
theorem B1368319 : Blo 810345 1368319 := bstep (se 1 (by rfl) ⟨1026239, by rfl⟩ : syracuseStep 1368319 = 2052479) B2052479
theorem B811263 : Blo 810345 811263 := bstep (se 1 (by rfl) ⟨608447, by rfl⟩ : syracuseStep 811263 = 1216895) B1216895
theorem B1827071 : Blo 810345 1827071 := bstep (se 1 (by rfl) ⟨1370303, by rfl⟩ : syracuseStep 1827071 = 2740607) B2740607
theorem B811311 : Blo 810345 811311 := bstep (se 1 (by rfl) ⟨608483, by rfl⟩ : syracuseStep 811311 = 1216967) B1216967
theorem B1827233 : Blo 810345 1827233 := bstep (se 2 (by rfl) ⟨685212, by rfl⟩ : syracuseStep 1827233 = 1370425) B1370425
theorem B811547 : Blo 810345 811547 := bstep (se 1 (by rfl) ⟨608660, by rfl⟩ : syracuseStep 811547 = 1217321) B1217321
theorem B811551 : Blo 810345 811551 := bstep (se 1 (by rfl) ⟨608663, by rfl⟩ : syracuseStep 811551 = 1217327) B1217327
theorem B811631 : Blo 810345 811631 := bstep (se 1 (by rfl) ⟨608723, by rfl⟩ : syracuseStep 811631 = 1217447) B1217447
theorem B811687 : Blo 810345 811687 := bstep (se 1 (by rfl) ⟨608765, by rfl⟩ : syracuseStep 811687 = 1217531) B1217531
theorem B811727 : Blo 810345 811727 := bstep (se 1 (by rfl) ⟨608795, by rfl⟩ : syracuseStep 811727 = 1217591) B1217591
theorem B811807 : Blo 810345 811807 := bstep (se 1 (by rfl) ⟨608855, by rfl⟩ : syracuseStep 811807 = 1217711) B1217711
theorem B1303327 : Blo 810345 1303327 := bstep (se 1 (by rfl) ⟨977495, by rfl⟩ : syracuseStep 1303327 = 1954991) B1954991
theorem B2057015 : Blo 810345 2057015 := bstep (se 1 (by rfl) ⟨1542761, by rfl⟩ : syracuseStep 2057015 = 3085523) B3085523
theorem B2745143 : Blo 810345 2745143 := bstep (se 1 (by rfl) ⟨2058857, by rfl⟩ : syracuseStep 2745143 = 4117715) B4117715
theorem B812079 : Blo 810345 812079 := bstep (se 1 (by rfl) ⟨609059, by rfl⟩ : syracuseStep 812079 = 1218119) B1218119
theorem B812143 : Blo 810345 812143 := bstep (se 1 (by rfl) ⟨609107, by rfl⟩ : syracuseStep 812143 = 1218215) B1218215
theorem B812199 : Blo 810345 812199 := bstep (se 1 (by rfl) ⟨609149, by rfl⟩ : syracuseStep 812199 = 1218299) B1218299
theorem B1828007 : Blo 810345 1828007 := bstep (se 1 (by rfl) ⟨1371005, by rfl⟩ : syracuseStep 1828007 = 2742011) B2742011
theorem B812223 : Blo 810345 812223 := bstep (se 1 (by rfl) ⟨609167, by rfl⟩ : syracuseStep 812223 = 1218335) B1218335
theorem B812255 : Blo 810345 812255 := bstep (se 1 (by rfl) ⟨609191, by rfl⟩ : syracuseStep 812255 = 1218383) B1218383
theorem B1828115 : Blo 810345 1828115 := bstep (se 1 (by rfl) ⟨1371086, by rfl⟩ : syracuseStep 1828115 = 2742173) B2742173
theorem B812335 : Blo 810345 812335 := bstep (se 1 (by rfl) ⟨609251, by rfl⟩ : syracuseStep 812335 = 1218503) B1218503
theorem B61007305 : Blo 810345 61007305 := bstep (se 2 (by rfl) ⟨22877739, by rfl⟩ : syracuseStep 61007305 = 45755479) B45755479
theorem B812571 : Blo 810345 812571 := bstep (se 1 (by rfl) ⟨609428, by rfl⟩ : syracuseStep 812571 = 1218857) B1218857
theorem B812575 : Blo 810345 812575 := bstep (se 1 (by rfl) ⟨609431, by rfl⟩ : syracuseStep 812575 = 1218863) B1218863
theorem B812735 : Blo 810345 812735 := bstep (se 1 (by rfl) ⟨609551, by rfl⟩ : syracuseStep 812735 = 1219103) B1219103
theorem B4941587 : Blo 810345 4941587 := bstep (se 1 (by rfl) ⟨3706190, by rfl⟩ : syracuseStep 4941587 = 7412381) B7412381
theorem B1828745 : Blo 810345 1828745 := bstep (se 2 (by rfl) ⟨685779, by rfl⟩ : syracuseStep 1828745 = 1371559) B1371559
theorem B1828763 : Blo 810345 1828763 := bstep (se 1 (by rfl) ⟨1371572, by rfl⟩ : syracuseStep 1828763 = 2743145) B2743145
theorem B1370047 : Blo 810345 1370047 := bstep (se 1 (by rfl) ⟨1027535, by rfl⟩ : syracuseStep 1370047 = 2055071) B2055071
theorem B1828799 : Blo 810345 1828799 := bstep (se 1 (by rfl) ⟨1371599, by rfl⟩ : syracuseStep 1828799 = 2743199) B2743199
theorem B812991 : Blo 810345 812991 := bstep (se 1 (by rfl) ⟨609743, by rfl⟩ : syracuseStep 812991 = 1219487) B1219487
theorem B2746331 : Blo 810345 2746331 := bstep (se 1 (by rfl) ⟨2059748, by rfl⟩ : syracuseStep 2746331 = 4119497) B4119497
theorem B813023 : Blo 810345 813023 := bstep (se 1 (by rfl) ⟨609767, by rfl⟩ : syracuseStep 813023 = 1219535) B1219535
theorem B6580217 : Blo 810345 6580217 := bstep (se 2 (by rfl) ⟨2467581, by rfl⟩ : syracuseStep 6580217 = 4935163) B4935163
theorem B813083 : Blo 810345 813083 := bstep (se 1 (by rfl) ⟨609812, by rfl⟩ : syracuseStep 813083 = 1219625) B1219625
theorem B813087 : Blo 810345 813087 := bstep (se 1 (by rfl) ⟨609815, by rfl⟩ : syracuseStep 813087 = 1219631) B1219631
theorem B813103 : Blo 810345 813103 := bstep (se 1 (by rfl) ⟨609827, by rfl⟩ : syracuseStep 813103 = 1219655) B1219655
theorem B1828961 : Blo 810345 1828961 := bstep (se 2 (by rfl) ⟨685860, by rfl⟩ : syracuseStep 1828961 = 1371721) B1371721
theorem B3467387 : Blo 810345 3467387 := bstep (se 1 (by rfl) ⟨2600540, by rfl⟩ : syracuseStep 3467387 = 5201081) B5201081
theorem B7825531 : Blo 810345 7825531 := bstep (se 1 (by rfl) ⟨5869148, by rfl⟩ : syracuseStep 7825531 = 11738297) B11738297
theorem B813279 : Blo 810345 813279 := bstep (se 1 (by rfl) ⟨609959, by rfl⟩ : syracuseStep 813279 = 1219919) B1219919
theorem B2058473 : Blo 810345 2058473 := bstep (se 2 (by rfl) ⟨771927, by rfl⟩ : syracuseStep 2058473 = 1543855) B1543855
theorem B2746601 : Blo 810345 2746601 := bstep (se 2 (by rfl) ⟨1029975, by rfl⟩ : syracuseStep 2746601 = 2059951) B2059951
theorem B813339 : Blo 810345 813339 := bstep (se 1 (by rfl) ⟨610004, by rfl⟩ : syracuseStep 813339 = 1220009) B1220009
theorem B911695 : Blo 810345 911695 := bstep (se 1 (by rfl) ⟨683771, by rfl⟩ : syracuseStep 911695 = 1367543) B1367543
theorem B813439 : Blo 810345 813439 := bstep (se 1 (by rfl) ⟨610079, by rfl⟩ : syracuseStep 813439 = 1220159) B1220159
theorem B2746871 : Blo 810345 2746871 := bstep (se 1 (by rfl) ⟨2060153, by rfl⟩ : syracuseStep 2746871 = 4120307) B4120307
theorem B813615 : Blo 810345 813615 := bstep (se 1 (by rfl) ⟨610211, by rfl⟩ : syracuseStep 813615 = 1220423) B1220423
theorem B15592013 : Blo 810345 15592013 := bstep (se 3 (by rfl) ⟨2923502, by rfl⟩ : syracuseStep 15592013 = 5847005) B5847005
theorem B813671 : Blo 810345 813671 := bstep (se 1 (by rfl) ⟨610253, by rfl⟩ : syracuseStep 813671 = 1220507) B1220507
theorem B2747033 : Blo 810345 2747033 := bstep (se 2 (by rfl) ⟨1030137, by rfl⟩ : syracuseStep 2747033 = 2060275) B2060275
theorem B814047 : Blo 810345 814047 := bstep (se 1 (by rfl) ⟨610535, by rfl⟩ : syracuseStep 814047 = 1221071) B1221071
theorem B912379 : Blo 810345 912379 := bstep (se 1 (by rfl) ⟨684284, by rfl⟩ : syracuseStep 912379 = 1368569) B1368569
theorem B814075 : Blo 810345 814075 := bstep (se 1 (by rfl) ⟨610556, by rfl⟩ : syracuseStep 814075 = 1221113) B1221113
theorem B814143 : Blo 810345 814143 := bstep (se 1 (by rfl) ⟨610607, by rfl⟩ : syracuseStep 814143 = 1221215) B1221215
theorem B2747465 : Blo 810345 2747465 := bstep (se 2 (by rfl) ⟨1030299, by rfl⟩ : syracuseStep 2747465 = 2060599) B2060599
theorem B912559 : Blo 810345 912559 := bstep (se 1 (by rfl) ⟨684419, by rfl⟩ : syracuseStep 912559 = 1368839) B1368839
theorem B1830311 : Blo 810345 1830311 := bstep (se 1 (by rfl) ⟨1372733, by rfl⟩ : syracuseStep 1830311 = 2745467) B2745467
theorem B1830491 : Blo 810345 1830491 := bstep (se 1 (by rfl) ⟨1372868, by rfl⟩ : syracuseStep 1830491 = 2745737) B2745737
theorem B913279 : Blo 810345 913279 := bstep (se 1 (by rfl) ⟨684959, by rfl⟩ : syracuseStep 913279 = 1369919) B1369919
theorem B6156161 : Blo 810345 6156161 := bstep (se 2 (by rfl) ⟨2308560, by rfl⟩ : syracuseStep 6156161 = 4617121) B4617121
theorem B1372153 : Blo 810345 1372153 := bstep (se 2 (by rfl) ⟨514557, by rfl⟩ : syracuseStep 1372153 = 1029115) B1029115
theorem B1830905 : Blo 810345 1830905 := bstep (se 2 (by rfl) ⟨686589, by rfl⟩ : syracuseStep 1830905 = 1373179) B1373179
theorem B1830995 : Blo 810345 1830995 := bstep (se 1 (by rfl) ⟨1373246, by rfl⟩ : syracuseStep 1830995 = 2746493) B2746493
theorem B6942905 : Blo 810345 6942905 := bstep (se 2 (by rfl) ⟨2603589, by rfl⟩ : syracuseStep 6942905 = 5207179) B5207179
theorem B1372423 : Blo 810345 1372423 := bstep (se 1 (by rfl) ⟨1029317, by rfl⟩ : syracuseStep 1372423 = 2058635) B2058635
theorem B1831175 : Blo 810345 1831175 := bstep (se 1 (by rfl) ⟨1373381, by rfl⟩ : syracuseStep 1831175 = 2746763) B2746763
theorem B15790403 : Blo 810345 15790403 := bstep (se 1 (by rfl) ⟨11842802, by rfl⟩ : syracuseStep 15790403 = 23685605) B23685605
theorem B6156647 : Blo 810345 6156647 := bstep (se 1 (by rfl) ⟨4617485, by rfl⟩ : syracuseStep 6156647 = 9234971) B9234971
theorem B913819 : Blo 810345 913819 := bstep (se 1 (by rfl) ⟨685364, by rfl⟩ : syracuseStep 913819 = 1370729) B1370729
theorem B1831481 : Blo 810345 1831481 := bstep (se 2 (by rfl) ⟨686805, by rfl⟩ : syracuseStep 1831481 = 1373611) B1373611
theorem B2061035 : Blo 810345 2061035 := bstep (se 1 (by rfl) ⟨1545776, by rfl⟩ : syracuseStep 2061035 = 3091553) B3091553
theorem B2061065 : Blo 810345 2061065 := bstep (se 2 (by rfl) ⟨772899, by rfl⟩ : syracuseStep 2061065 = 1545799) B1545799
theorem B35648363 : Blo 810345 35648363 := bstep (se 1 (by rfl) ⟨26736272, by rfl⟩ : syracuseStep 35648363 = 53472545) B53472545
theorem B7402427 : Blo 810345 7402427 := bstep (se 1 (by rfl) ⟨5551820, by rfl⟩ : syracuseStep 7402427 = 11103641) B11103641
theorem B914503 : Blo 810345 914503 := bstep (se 1 (by rfl) ⟨685877, by rfl⟩ : syracuseStep 914503 = 1371755) B1371755
theorem B1733737 : Blo 810345 1733737 := bstep (se 2 (by rfl) ⟨650151, by rfl⟩ : syracuseStep 1733737 = 1300303) B1300303
theorem B914683 : Blo 810345 914683 := bstep (se 1 (by rfl) ⟨686012, by rfl⟩ : syracuseStep 914683 = 1372025) B1372025
theorem B1373449 : Blo 810345 1373449 := bstep (se 2 (by rfl) ⟨515043, by rfl⟩ : syracuseStep 1373449 = 1030087) B1030087
theorem B1832201 : Blo 810345 1832201 := bstep (se 2 (by rfl) ⟨687075, by rfl⟩ : syracuseStep 1832201 = 1374151) B1374151
theorem B1373503 : Blo 810345 1373503 := bstep (se 1 (by rfl) ⟨1030127, by rfl⟩ : syracuseStep 1373503 = 2060255) B2060255
theorem B1832255 : Blo 810345 1832255 := bstep (se 1 (by rfl) ⟨1374191, by rfl⟩ : syracuseStep 1832255 = 2748383) B2748383
theorem B3896927 : Blo 810345 3896927 := bstep (se 1 (by rfl) ⟨2922695, by rfl⟩ : syracuseStep 3896927 = 5845391) B5845391
theorem B1373935 : Blo 810345 1373935 := bstep (se 1 (by rfl) ⟨1030451, by rfl⟩ : syracuseStep 1373935 = 2060903) B2060903
theorem B3077945 : Blo 810345 3077945 := bstep (se 2 (by rfl) ⟨1154229, by rfl⟩ : syracuseStep 3077945 = 2308459) B2308459
theorem B101644091 : Blo 810345 101644091 := bstep (se 1 (by rfl) ⟨76233068, by rfl⟩ : syracuseStep 101644091 = 152466137) B152466137
theorem B7403327 : Blo 810345 7403327 := bstep (se 1 (by rfl) ⟨5552495, by rfl⟩ : syracuseStep 7403327 = 11104991) B11104991
theorem B915871 : Blo 810345 915871 := bstep (se 1 (by rfl) ⟨686903, by rfl⟩ : syracuseStep 915871 = 1373807) B1373807
theorem B1735111 : Blo 810345 1735111 := bstep (se 1 (by rfl) ⟨1301333, by rfl⟩ : syracuseStep 1735111 = 2602667) B2602667
theorem B915943 : Blo 810345 915943 := bstep (se 1 (by rfl) ⟨686957, by rfl⟩ : syracuseStep 915943 = 1373915) B1373915
theorem B3898313 : Blo 810345 3898313 := bstep (se 2 (by rfl) ⟨1461867, by rfl⟩ : syracuseStep 3898313 = 2923735) B2923735
theorem B3898813 : Blo 810345 3898813 := bstep (se 3 (by rfl) ⟨731027, by rfl⟩ : syracuseStep 3898813 = 1462055) B1462055
theorem B1736615 : Blo 810345 1736615 := bstep (se 1 (by rfl) ⟨1302461, by rfl⟩ : syracuseStep 1736615 = 2604923) B2604923
theorem B3473351 : Blo 810345 3473351 := bstep (se 1 (by rfl) ⟨2605013, by rfl⟩ : syracuseStep 3473351 = 5210027) B5210027
theorem B2195731 : Blo 810345 2195731 := bstep (se 1 (by rfl) ⟨1646798, by rfl⟩ : syracuseStep 2195731 = 3293597) B3293597
theorem B5211053 : Blo 810345 5211053 := bstep (se 3 (by rfl) ⟨977072, by rfl⟩ : syracuseStep 5211053 = 1954145) B1954145
theorem B1737769 : Blo 810345 1737769 := bstep (se 2 (by rfl) ⟨651663, by rfl⟩ : syracuseStep 1737769 = 1303327) B1303327
theorem B6947963 : Blo 810345 6947963 := bstep (se 1 (by rfl) ⟨5210972, by rfl⟩ : syracuseStep 6947963 = 10421945) B10421945
theorem B24970463 : Blo 810345 24970463 := bstep (se 1 (by rfl) ⟨18727847, by rfl⟩ : syracuseStep 24970463 = 37455695) B37455695
theorem B3475007 : Blo 810345 3475007 := bstep (se 1 (by rfl) ⟨2606255, by rfl⟩ : syracuseStep 3475007 = 5212511) B5212511
theorem B1542959 : Blo 810345 1542959 := bstep (se 1 (by rfl) ⟨1157219, by rfl⟩ : syracuseStep 1542959 = 2314439) B2314439
theorem B6163451 : Blo 810345 6163451 := bstep (se 1 (by rfl) ⟨4622588, by rfl⟩ : syracuseStep 6163451 = 9245177) B9245177
theorem B1215593 : Blo 810345 1215593 := bstep (se 2 (by rfl) ⟨455847, by rfl⟩ : syracuseStep 1215593 = 911695) B911695
theorem B1215719 : Blo 810345 1215719 := bstep (se 1 (by rfl) ⟨911789, by rfl⟩ : syracuseStep 1215719 = 1823579) B1823579
theorem B14814829 : Blo 810345 14814829 := bstep (se 3 (by rfl) ⟨2777780, by rfl⟩ : syracuseStep 14814829 = 5555561) B5555561
theorem B1216223 : Blo 810345 1216223 := bstep (se 1 (by rfl) ⟨912167, by rfl⟩ : syracuseStep 1216223 = 1824335) B1824335
theorem B1543931 : Blo 810345 1543931 := bstep (se 1 (by rfl) ⟨1157948, by rfl⟩ : syracuseStep 1543931 = 2315897) B2315897
theorem B1216505 : Blo 810345 1216505 := bstep (se 2 (by rfl) ⟨456189, by rfl⟩ : syracuseStep 1216505 = 912379) B912379
theorem B5214203 : Blo 810345 5214203 := bstep (se 1 (by rfl) ⟨3910652, by rfl⟩ : syracuseStep 5214203 = 7821305) B7821305
theorem B1216703 : Blo 810345 1216703 := bstep (se 1 (by rfl) ⟨912527, by rfl⟩ : syracuseStep 1216703 = 1825055) B1825055
theorem B1544417 : Blo 810345 1544417 := bstep (se 2 (by rfl) ⟨579156, by rfl⟩ : syracuseStep 1544417 = 1158313) B1158313
theorem B1216745 : Blo 810345 1216745 := bstep (se 2 (by rfl) ⟨456279, by rfl⟩ : syracuseStep 1216745 = 912559) B912559
theorem B1216871 : Blo 810345 1216871 := bstep (se 1 (by rfl) ⟨912653, by rfl⟩ : syracuseStep 1216871 = 1825307) B1825307
theorem B13177565 : Blo 810345 13177565 := bstep (se 3 (by rfl) ⟨2470793, by rfl⟩ : syracuseStep 13177565 = 4941587) B4941587
theorem B1217705 : Blo 810345 1217705 := bstep (se 2 (by rfl) ⟨456639, by rfl⟩ : syracuseStep 1217705 = 913279) B913279
theorem B1217771 : Blo 810345 1217771 := bstep (se 1 (by rfl) ⟨913328, by rfl⟩ : syracuseStep 1217771 = 1826657) B1826657
theorem B7410923 : Blo 810345 7410923 := bstep (se 1 (by rfl) ⟨5558192, by rfl⟩ : syracuseStep 7410923 = 11116385) B11116385
theorem B1217855 : Blo 810345 1217855 := bstep (se 1 (by rfl) ⟨913391, by rfl⟩ : syracuseStep 1217855 = 1826783) B1826783
theorem B1218047 : Blo 810345 1218047 := bstep (se 1 (by rfl) ⟨913535, by rfl⟩ : syracuseStep 1218047 = 1827071) B1827071
theorem B1218155 : Blo 810345 1218155 := bstep (se 1 (by rfl) ⟨913616, by rfl⟩ : syracuseStep 1218155 = 1827233) B1827233
theorem B1218425 : Blo 810345 1218425 := bstep (se 2 (by rfl) ⟨456909, by rfl⟩ : syracuseStep 1218425 = 913819) B913819
theorem B19732481 : Blo 810345 19732481 := bstep (se 2 (by rfl) ⟨7399680, by rfl⟩ : syracuseStep 19732481 = 14799361) B14799361
theorem B21108737 : Blo 810345 21108737 := bstep (se 2 (by rfl) ⟨7915776, by rfl⟩ : syracuseStep 21108737 = 15831553) B15831553
theorem B1218671 : Blo 810345 1218671 := bstep (se 1 (by rfl) ⟨914003, by rfl⟩ : syracuseStep 1218671 = 1828007) B1828007
theorem B1218743 : Blo 810345 1218743 := bstep (se 1 (by rfl) ⟨914057, by rfl⟩ : syracuseStep 1218743 = 1828115) B1828115
theorem B31660607 : Blo 810345 31660607 := bstep (se 1 (by rfl) ⟨23745455, by rfl⟩ : syracuseStep 31660607 = 47490911) B47490911
theorem B1219163 : Blo 810345 1219163 := bstep (se 1 (by rfl) ⟨914372, by rfl⟩ : syracuseStep 1219163 = 1828745) B1828745
theorem B1219175 : Blo 810345 1219175 := bstep (se 1 (by rfl) ⟨914381, by rfl⟩ : syracuseStep 1219175 = 1828763) B1828763
theorem B1219199 : Blo 810345 1219199 := bstep (se 1 (by rfl) ⟨914399, by rfl⟩ : syracuseStep 1219199 = 1828799) B1828799
theorem B10427069 : Blo 810345 10427069 := bstep (se 3 (by rfl) ⟨1955075, by rfl⟩ : syracuseStep 10427069 = 3910151) B3910151
theorem B1219307 : Blo 810345 1219307 := bstep (se 1 (by rfl) ⟨914480, by rfl⟩ : syracuseStep 1219307 = 1828961) B1828961
theorem B1219337 : Blo 810345 1219337 := bstep (se 2 (by rfl) ⟨457251, by rfl⟩ : syracuseStep 1219337 = 914503) B914503
theorem B1219577 : Blo 810345 1219577 := bstep (se 2 (by rfl) ⟨457341, by rfl⟩ : syracuseStep 1219577 = 914683) B914683
theorem B10394675 : Blo 810345 10394675 := bstep (se 1 (by rfl) ⟨7796006, by rfl⟩ : syracuseStep 10394675 = 15592013) B15592013
theorem B3087679 : Blo 810345 3087679 := bstep (se 1 (by rfl) ⟨2315759, by rfl⟩ : syracuseStep 3087679 = 4631519) B4631519
theorem B1220207 : Blo 810345 1220207 := bstep (se 1 (by rfl) ⟨915155, by rfl⟩ : syracuseStep 1220207 = 1830311) B1830311
theorem B1220327 : Blo 810345 1220327 := bstep (se 1 (by rfl) ⟨915245, by rfl⟩ : syracuseStep 1220327 = 1830491) B1830491
theorem B4104107 : Blo 810345 4104107 := bstep (se 1 (by rfl) ⟨3078080, by rfl⟩ : syracuseStep 4104107 = 6156161) B6156161
theorem B1220603 : Blo 810345 1220603 := bstep (se 1 (by rfl) ⟨915452, by rfl⟩ : syracuseStep 1220603 = 1830905) B1830905
theorem B33792005 : Blo 810345 33792005 := bstep (se 4 (by rfl) ⟨3168000, by rfl⟩ : syracuseStep 33792005 = 6336001) B6336001
theorem B1220663 : Blo 810345 1220663 := bstep (se 1 (by rfl) ⟨915497, by rfl⟩ : syracuseStep 1220663 = 1830995) B1830995
theorem B4628603 : Blo 810345 4628603 := bstep (se 1 (by rfl) ⟨3471452, by rfl⟩ : syracuseStep 4628603 = 6942905) B6942905
theorem B1220783 : Blo 810345 1220783 := bstep (se 1 (by rfl) ⟨915587, by rfl⟩ : syracuseStep 1220783 = 1831175) B1831175
theorem B10526935 : Blo 810345 10526935 := bstep (se 1 (by rfl) ⟨7895201, by rfl⟩ : syracuseStep 10526935 = 15790403) B15790403
theorem B4104431 : Blo 810345 4104431 := bstep (se 1 (by rfl) ⟨3078323, by rfl⟩ : syracuseStep 4104431 = 6156647) B6156647
theorem B1220987 : Blo 810345 1220987 := bstep (se 1 (by rfl) ⟨915740, by rfl⟩ : syracuseStep 1220987 = 1831481) B1831481
theorem B1221161 : Blo 810345 1221161 := bstep (se 2 (by rfl) ⟨457935, by rfl⟩ : syracuseStep 1221161 = 915871) B915871
theorem B23765575 : Blo 810345 23765575 := bstep (se 1 (by rfl) ⟨17824181, by rfl⟩ : syracuseStep 23765575 = 35648363) B35648363
theorem B1221257 : Blo 810345 1221257 := bstep (se 2 (by rfl) ⟨457971, by rfl⟩ : syracuseStep 1221257 = 915943) B915943
theorem B1221467 : Blo 810345 1221467 := bstep (se 1 (by rfl) ⟨916100, by rfl⟩ : syracuseStep 1221467 = 1832201) B1832201
theorem B1221503 : Blo 810345 1221503 := bstep (se 1 (by rfl) ⟨916127, by rfl⟩ : syracuseStep 1221503 = 1832255) B1832255
theorem B2597951 : Blo 810345 2597951 := bstep (se 1 (by rfl) ⟨1948463, by rfl⟩ : syracuseStep 2597951 = 3896927) B3896927
theorem B5285501 : Blo 810345 5285501 := bstep (se 3 (by rfl) ⟨991031, by rfl⟩ : syracuseStep 5285501 = 1982063) B1982063
theorem B17573537 : Blo 810345 17573537 := bstep (se 2 (by rfl) ⟨6590076, by rfl⟩ : syracuseStep 17573537 = 13180153) B13180153
theorem B3090095 : Blo 810345 3090095 := bstep (se 1 (by rfl) ⟨2317571, by rfl⟩ : syracuseStep 3090095 = 4635143) B4635143
theorem B2598875 : Blo 810345 2598875 := bstep (se 1 (by rfl) ⟨1949156, by rfl⟩ : syracuseStep 2598875 = 3898313) B3898313
theorem B1157743 : Blo 810345 1157743 := bstep (se 1 (by rfl) ⟨868307, by rfl⟩ : syracuseStep 1157743 = 1736615) B1736615
theorem B12528539 : Blo 810345 12528539 := bstep (se 1 (by rfl) ⟨9396404, by rfl⟩ : syracuseStep 12528539 = 18792809) B18792809
theorem B7908295 : Blo 810345 7908295 := bstep (se 1 (by rfl) ⟨5931221, by rfl⟩ : syracuseStep 7908295 = 11862443) B11862443
theorem B4172791 : Blo 810345 4172791 := bstep (se 1 (by rfl) ⟨3129593, by rfl⟩ : syracuseStep 4172791 = 6259187) B6259187
theorem B1125679 : Blo 810345 1125679 := bstep (se 1 (by rfl) ⟨844259, by rfl⟩ : syracuseStep 1125679 = 1688519) B1688519
theorem B4632659 : Blo 810345 4632659 := bstep (se 1 (by rfl) ⟨3474494, by rfl⟩ : syracuseStep 4632659 = 6948989) B6948989
theorem B2601335 : Blo 810345 2601335 := bstep (se 1 (by rfl) ⟨1951001, by rfl⟩ : syracuseStep 2601335 = 3902003) B3902003
theorem B2470333 : Blo 810345 2470333 := bstep (se 3 (by rfl) ⟨463187, by rfl⟩ : syracuseStep 2470333 = 926375) B926375
theorem B3912151 : Blo 810345 3912151 := bstep (se 1 (by rfl) ⟨2934113, by rfl⟩ : syracuseStep 3912151 = 5868227) B5868227
theorem B4174375 : Blo 810345 4174375 := bstep (se 1 (by rfl) ⟨3130781, by rfl⟩ : syracuseStep 4174375 = 6261563) B6261563
theorem B81343073 : Blo 810345 81343073 := bstep (se 2 (by rfl) ⟨30503652, by rfl⟩ : syracuseStep 81343073 = 61007305) B61007305
theorem B4109291 : Blo 810345 4109291 := bstep (se 1 (by rfl) ⟨3081968, by rfl⟩ : syracuseStep 4109291 = 6163937) B6163937
theorem B9253925 : Blo 810345 9253925 := bstep (se 4 (by rfl) ⟨867555, by rfl⟩ : syracuseStep 9253925 = 1735111) B1735111
theorem B21116123 : Blo 810345 21116123 := bstep (se 1 (by rfl) ⟨15837092, by rfl⟩ : syracuseStep 21116123 = 31674185) B31674185
theorem B10434041 : Blo 810345 10434041 := bstep (se 2 (by rfl) ⟨3912765, by rfl⟩ : syracuseStep 10434041 = 7825531) B7825531
theorem B4929133 : Blo 810345 4929133 := bstep (se 3 (by rfl) ⟨924212, by rfl⟩ : syracuseStep 4929133 = 1848425) B1848425
theorem B4109939 : Blo 810345 4109939 := bstep (se 1 (by rfl) ⟨3082454, by rfl⟩ : syracuseStep 4109939 = 6164909) B6164909
theorem B1095547 : Blo 810345 1095547 := bstep (se 1 (by rfl) ⟨821660, by rfl⟩ : syracuseStep 1095547 = 1643321) B1643321
theorem B2472059 : Blo 810345 2472059 := bstep (se 1 (by rfl) ⟨1854044, by rfl⟩ : syracuseStep 2472059 = 3708089) B3708089
theorem B2308733 : Blo 810345 2308733 := bstep (se 3 (by rfl) ⟨432887, by rfl⟩ : syracuseStep 2308733 = 865775) B865775
theorem B4111559 : Blo 810345 4111559 := bstep (se 1 (by rfl) ⟨3083669, by rfl⟩ : syracuseStep 4111559 = 6167339) B6167339
theorem B6176087 : Blo 810345 6176087 := bstep (se 1 (by rfl) ⟨4632065, by rfl⟩ : syracuseStep 6176087 = 9264131) B9264131
theorem B4636075 : Blo 810345 4636075 := bstep (se 1 (by rfl) ⟨3477056, by rfl⟩ : syracuseStep 4636075 = 6954113) B6954113
theorem B4112207 : Blo 810345 4112207 := bstep (se 1 (by rfl) ⟨3084155, by rfl⟩ : syracuseStep 4112207 = 6168311) B6168311
theorem B8700317 : Blo 810345 8700317 := bstep (se 3 (by rfl) ⟨1631309, by rfl⟩ : syracuseStep 8700317 = 3262619) B3262619
theorem B2736719 : Blo 810345 2736719 := bstep (se 1 (by rfl) ⟨2052539, by rfl⟩ : syracuseStep 2736719 = 4105079) B4105079
theorem B2737259 : Blo 810345 2737259 := bstep (se 1 (by rfl) ⟨2052944, by rfl⟩ : syracuseStep 2737259 = 4105889) B4105889
theorem B4637807 : Blo 810345 4637807 := bstep (se 1 (by rfl) ⟨3478355, by rfl⟩ : syracuseStep 4637807 = 6956711) B6956711
theorem B2311591 : Blo 810345 2311591 := bstep (se 1 (by rfl) ⟨1733693, by rfl⟩ : syracuseStep 2311591 = 3467387) B3467387
theorem B2311649 : Blo 810345 2311649 := bstep (se 2 (by rfl) ⟨866868, by rfl⟩ : syracuseStep 2311649 = 1733737) B1733737
theorem B2738771 : Blo 810345 2738771 := bstep (se 1 (by rfl) ⟨2054078, by rfl⟩ : syracuseStep 2738771 = 4108157) B4108157
theorem B2083583 : Blo 810345 2083583 := bstep (se 1 (by rfl) ⟨1562687, by rfl⟩ : syracuseStep 2083583 = 3125375) B3125375
theorem B4934951 : Blo 810345 4934951 := bstep (se 1 (by rfl) ⟨3701213, by rfl⟩ : syracuseStep 4934951 = 7402427) B7402427
theorem B2051963 : Blo 810345 2051963 := bstep (se 1 (by rfl) ⟨1538972, by rfl⟩ : syracuseStep 2051963 = 3077945) B3077945
theorem B2314109 : Blo 810345 2314109 := bstep (se 3 (by rfl) ⟨433895, by rfl⟩ : syracuseStep 2314109 = 867791) B867791
theorem B4935551 : Blo 810345 4935551 := bstep (se 1 (by rfl) ⟨3701663, by rfl⟩ : syracuseStep 4935551 = 7403327) B7403327
theorem B5198417 : Blo 810345 5198417 := bstep (se 2 (by rfl) ⟨1949406, by rfl⟩ : syracuseStep 5198417 = 3898813) B3898813
theorem B2315567 : Blo 810345 2315567 := bstep (se 1 (by rfl) ⟨1736675, by rfl⟩ : syracuseStep 2315567 = 3473351) B3473351
theorem B2053775 : Blo 810345 2053775 := bstep (se 1 (by rfl) ⟨1540331, by rfl⟩ : syracuseStep 2053775 = 3080663) B3080663
theorem B1824425 : Blo 810345 1824425 := bstep (se 2 (by rfl) ⟨684159, by rfl⟩ : syracuseStep 1824425 = 1368319) B1368319
theorem B1824551 : Blo 810345 1824551 := bstep (se 1 (by rfl) ⟨1368413, by rfl⟩ : syracuseStep 1824551 = 2736827) B2736827
theorem B2054281 : Blo 810345 2054281 := bstep (se 2 (by rfl) ⟨770355, by rfl⟩ : syracuseStep 2054281 = 1540711) B1540711
theorem B168450191 : Blo 810345 168450191 := bstep (se 1 (by rfl) ⟨126337643, by rfl⟩ : syracuseStep 168450191 = 252675287) B252675287
theorem B2054393 : Blo 810345 2054393 := bstep (se 2 (by rfl) ⟨770397, by rfl⟩ : syracuseStep 2054393 = 1540795) B1540795
theorem B2054555 : Blo 810345 2054555 := bstep (se 1 (by rfl) ⟨1540916, by rfl⟩ : syracuseStep 2054555 = 3081833) B3081833
theorem B8772239 : Blo 810345 8772239 := bstep (se 1 (by rfl) ⟨6579179, by rfl⟩ : syracuseStep 8772239 = 13158359) B13158359
theorem B7428989 : Blo 810345 7428989 := bstep (se 3 (by rfl) ⟨1392935, by rfl⟩ : syracuseStep 7428989 = 2785871) B2785871
theorem B1825703 : Blo 810345 1825703 := bstep (se 1 (by rfl) ⟨1369277, by rfl⟩ : syracuseStep 1825703 = 2738555) B2738555
theorem B7789547 : Blo 810345 7789547 := bstep (se 1 (by rfl) ⟨5842160, by rfl⟩ : syracuseStep 7789547 = 11684321) B11684321
theorem B20863979 : Blo 810345 20863979 := bstep (se 1 (by rfl) ⟨15647984, by rfl⟩ : syracuseStep 20863979 = 31295969) B31295969
theorem B1825883 : Blo 810345 1825883 := bstep (se 1 (by rfl) ⟨1369412, by rfl⟩ : syracuseStep 1825883 = 2738825) B2738825
theorem B2776169 : Blo 810345 2776169 := bstep (se 2 (by rfl) ⟨1041063, by rfl⟩ : syracuseStep 2776169 = 2082127) B2082127
theorem B4119659 : Blo 810345 4119659 := bstep (se 1 (by rfl) ⟨3089744, by rfl⟩ : syracuseStep 4119659 = 6179489) B6179489
theorem B4381883 : Blo 810345 4381883 := bstep (se 1 (by rfl) ⟨3286412, by rfl⟩ : syracuseStep 4381883 = 6572825) B6572825
theorem B810367 : Blo 810345 810367 := bstep (se 1 (by rfl) ⟨607775, by rfl⟩ : syracuseStep 810367 = 1215551) B1215551
theorem B810735 : Blo 810345 810735 := bstep (se 1 (by rfl) ⟨608051, by rfl⟩ : syracuseStep 810735 = 1216103) B1216103
theorem B6577949 : Blo 810345 6577949 := bstep (se 3 (by rfl) ⟨1233365, by rfl⟩ : syracuseStep 6577949 = 2466731) B2466731
theorem B1236905 : Blo 810345 1236905 := bstep (se 2 (by rfl) ⟨463839, by rfl⟩ : syracuseStep 1236905 = 927679) B927679
theorem B1826729 : Blo 810345 1826729 := bstep (se 2 (by rfl) ⟨685023, by rfl⟩ : syracuseStep 1826729 = 1370047) B1370047
theorem B1466279 : Blo 810345 1466279 := bstep (se 1 (by rfl) ⟨1099709, by rfl⟩ : syracuseStep 1466279 = 2199419) B2199419
theorem B810991 : Blo 810345 810991 := bstep (se 1 (by rfl) ⟨608243, by rfl⟩ : syracuseStep 810991 = 1216487) B1216487
theorem B811071 : Blo 810345 811071 := bstep (se 1 (by rfl) ⟨608303, by rfl⟩ : syracuseStep 811071 = 1216607) B1216607
theorem B811079 : Blo 810345 811079 := bstep (se 1 (by rfl) ⟨608309, by rfl⟩ : syracuseStep 811079 = 1216619) B1216619
theorem B811111 : Blo 810345 811111 := bstep (se 1 (by rfl) ⟨608333, by rfl⟩ : syracuseStep 811111 = 1216667) B1216667
theorem B1368299 : Blo 810345 1368299 := bstep (se 1 (by rfl) ⟨1026224, by rfl⟩ : syracuseStep 1368299 = 2052449) B2052449
theorem B2056711 : Blo 810345 2056711 := bstep (se 1 (by rfl) ⟨1542533, by rfl⟩ : syracuseStep 2056711 = 3085067) B3085067
theorem B36135443 : Blo 810345 36135443 := bstep (se 1 (by rfl) ⟨27101582, by rfl⟩ : syracuseStep 36135443 = 54203165) B54203165
theorem B1827431 : Blo 810345 1827431 := bstep (se 1 (by rfl) ⟨1370573, by rfl⟩ : syracuseStep 1827431 = 2741147) B2741147
theorem B811679 : Blo 810345 811679 := bstep (se 1 (by rfl) ⟨608759, by rfl⟩ : syracuseStep 811679 = 1217519) B1217519
theorem B811935 : Blo 810345 811935 := bstep (se 1 (by rfl) ⟨608951, by rfl⟩ : syracuseStep 811935 = 1217903) B1217903
theorem B812015 : Blo 810345 812015 := bstep (se 1 (by rfl) ⟨609011, by rfl⟩ : syracuseStep 812015 = 1218023) B1218023
theorem B812123 : Blo 810345 812123 := bstep (se 1 (by rfl) ⟨609092, by rfl⟩ : syracuseStep 812123 = 1218185) B1218185
theorem B812135 : Blo 810345 812135 := bstep (se 1 (by rfl) ⟨609101, by rfl⟩ : syracuseStep 812135 = 1218203) B1218203
theorem B812263 : Blo 810345 812263 := bstep (se 1 (by rfl) ⟨609197, by rfl⟩ : syracuseStep 812263 = 1218395) B1218395
theorem B812519 : Blo 810345 812519 := bstep (se 1 (by rfl) ⟨609389, by rfl⟩ : syracuseStep 812519 = 1218779) B1218779
theorem B812699 : Blo 810345 812699 := bstep (se 1 (by rfl) ⟨609524, by rfl⟩ : syracuseStep 812699 = 1219049) B1219049
theorem B88991459 : Blo 810345 88991459 := bstep (se 1 (by rfl) ⟨66743594, by rfl⟩ : syracuseStep 88991459 = 133487189) B133487189
theorem B4384651 : Blo 810345 4384651 := bstep (se 1 (by rfl) ⟨3288488, by rfl⟩ : syracuseStep 4384651 = 6576977) B6576977
theorem B812959 : Blo 810345 812959 := bstep (se 1 (by rfl) ⟨609719, by rfl⟩ : syracuseStep 812959 = 1219439) B1219439
theorem B812967 : Blo 810345 812967 := bstep (se 1 (by rfl) ⟨609725, by rfl⟩ : syracuseStep 812967 = 1219451) B1219451
theorem B813543 : Blo 810345 813543 := bstep (se 1 (by rfl) ⟨610157, by rfl⟩ : syracuseStep 813543 = 1220315) B1220315
theorem B168487559 : Blo 810345 168487559 := bstep (se 1 (by rfl) ⟨126365669, by rfl⟩ : syracuseStep 168487559 = 252731339) B252731339
theorem B813723 : Blo 810345 813723 := bstep (se 1 (by rfl) ⟨610292, by rfl⟩ : syracuseStep 813723 = 1220585) B1220585
theorem B1829537 : Blo 810345 1829537 := bstep (se 2 (by rfl) ⟨686076, by rfl⟩ : syracuseStep 1829537 = 1372153) B1372153
theorem B1829897 : Blo 810345 1829897 := bstep (se 2 (by rfl) ⟨686211, by rfl⟩ : syracuseStep 1829897 = 1372423) B1372423
theorem B3894313 : Blo 810345 3894313 := bstep (se 2 (by rfl) ⟨1460367, by rfl⟩ : syracuseStep 3894313 = 2920735) B2920735
theorem B814191 : Blo 810345 814191 := bstep (se 1 (by rfl) ⟨610643, by rfl⟩ : syracuseStep 814191 = 1221287) B1221287
theorem B5205181 : Blo 810345 5205181 := bstep (se 3 (by rfl) ⟨975971, by rfl⟩ : syracuseStep 5205181 = 1951943) B1951943
theorem B814271 : Blo 810345 814271 := bstep (se 1 (by rfl) ⟨610703, by rfl⟩ : syracuseStep 814271 = 1221407) B1221407
theorem B1371343 : Blo 810345 1371343 := bstep (se 1 (by rfl) ⟨1028507, by rfl⟩ : syracuseStep 1371343 = 2057015) B2057015
theorem B1830095 : Blo 810345 1830095 := bstep (se 1 (by rfl) ⟨1372571, by rfl⟩ : syracuseStep 1830095 = 2745143) B2745143
theorem B814287 : Blo 810345 814287 := bstep (se 1 (by rfl) ⟨610715, by rfl⟩ : syracuseStep 814287 = 1221431) B1221431
theorem B1830887 : Blo 810345 1830887 := bstep (se 1 (by rfl) ⟨1373165, by rfl⟩ : syracuseStep 1830887 = 2746331) B2746331
theorem B4386811 : Blo 810345 4386811 := bstep (se 1 (by rfl) ⟨3290108, by rfl⟩ : syracuseStep 4386811 = 6580217) B6580217
theorem B1372315 : Blo 810345 1372315 := bstep (se 1 (by rfl) ⟨1029236, by rfl⟩ : syracuseStep 1372315 = 2058473) B2058473
theorem B1831067 : Blo 810345 1831067 := bstep (se 1 (by rfl) ⟨1373300, by rfl⟩ : syracuseStep 1831067 = 2746601) B2746601
theorem B2191579 : Blo 810345 2191579 := bstep (se 1 (by rfl) ⟨1643684, by rfl⟩ : syracuseStep 2191579 = 3287369) B3287369
theorem B3895543 : Blo 810345 3895543 := bstep (se 1 (by rfl) ⟨2921657, by rfl⟩ : syracuseStep 3895543 = 5843315) B5843315
theorem B1831247 : Blo 810345 1831247 := bstep (se 1 (by rfl) ⟨1373435, by rfl⟩ : syracuseStep 1831247 = 2746871) B2746871
theorem B1831265 : Blo 810345 1831265 := bstep (se 2 (by rfl) ⟨686724, by rfl⟩ : syracuseStep 1831265 = 1373449) B1373449
theorem B1372585 : Blo 810345 1372585 := bstep (se 2 (by rfl) ⟨514719, by rfl⟩ : syracuseStep 1372585 = 1029439) B1029439
theorem B1831337 : Blo 810345 1831337 := bstep (se 2 (by rfl) ⟨686751, by rfl⟩ : syracuseStep 1831337 = 1373503) B1373503
theorem B1831355 : Blo 810345 1831355 := bstep (se 1 (by rfl) ⟨1373516, by rfl⟩ : syracuseStep 1831355 = 2747033) B2747033
theorem B1831643 : Blo 810345 1831643 := bstep (se 1 (by rfl) ⟨1373732, by rfl⟩ : syracuseStep 1831643 = 2747465) B2747465
theorem B1831913 : Blo 810345 1831913 := bstep (se 2 (by rfl) ⟨686967, by rfl⟩ : syracuseStep 1831913 = 1373935) B1373935
theorem B3699751 : Blo 810345 3699751 := bstep (se 1 (by rfl) ⟨2774813, by rfl⟩ : syracuseStep 3699751 = 5549627) B5549627
theorem B3077473 : Blo 810345 3077473 := bstep (se 2 (by rfl) ⟨1154052, by rfl⟩ : syracuseStep 3077473 = 2308105) B2308105
theorem B1374023 : Blo 810345 1374023 := bstep (se 1 (by rfl) ⟨1030517, by rfl⟩ : syracuseStep 1374023 = 2061035) B2061035
theorem B1374043 : Blo 810345 1374043 := bstep (se 1 (by rfl) ⟨1030532, by rfl⟩ : syracuseStep 1374043 = 2061065) B2061065
theorem B1734625 : Blo 810345 1734625 := bstep (se 2 (by rfl) ⟨650484, by rfl⟩ : syracuseStep 1734625 = 1300969) B1300969
theorem B3897371 : Blo 810345 3897371 := bstep (se 1 (by rfl) ⟨2923028, by rfl⟩ : syracuseStep 3897371 = 5846057) B5846057
theorem B7796897 : Blo 810345 7796897 := bstep (se 2 (by rfl) ⟨2923836, by rfl⟩ : syracuseStep 7796897 = 5847673) B5847673
theorem B67762727 : Blo 810345 67762727 := bstep (se 1 (by rfl) ⟨50822045, by rfl⟩ : syracuseStep 67762727 = 101644091) B101644091
theorem B28146653 : Blo 810345 28146653 := bstep (se 3 (by rfl) ⟨5277497, by rfl⟩ : syracuseStep 28146653 = 10554995) B10554995
theorem B10583099 : Blo 810345 10583099 := bstep (se 1 (by rfl) ⟨7937324, by rfl⟩ : syracuseStep 10583099 = 15874649) B15874649
theorem B2194523 : Blo 810345 2194523 := bstep (se 1 (by rfl) ⟨1645892, by rfl⟩ : syracuseStep 2194523 = 3291785) B3291785
theorem B3898601 : Blo 810345 3898601 := bstep (se 2 (by rfl) ⟨1461975, by rfl⟩ : syracuseStep 3898601 = 2923951) B2923951
theorem B1736171 : Blo 810345 1736171 := bstep (se 1 (by rfl) ⟨1302128, by rfl⟩ : syracuseStep 1736171 = 2604257) B2604257
theorem B5275421 : Blo 810345 5275421 := bstep (se 3 (by rfl) ⟨989141, by rfl⟩ : syracuseStep 5275421 = 1978283) B1978283
theorem B11108279 : Blo 810345 11108279 := bstep (se 1 (by rfl) ⟨8331209, by rfl⟩ : syracuseStep 11108279 = 16662419) B16662419
theorem B5800211 : Blo 810345 5800211 := bstep (se 1 (by rfl) ⟨4350158, by rfl⟩ : syracuseStep 5800211 = 8700317) B8700317
theorem B3474035 : Blo 810345 3474035 := bstep (se 1 (by rfl) ⟨2605526, by rfl⟩ : syracuseStep 3474035 = 5211053) B5211053
theorem B31687433 : Blo 810345 31687433 := bstep (se 2 (by rfl) ⟨11882787, by rfl⟩ : syracuseStep 31687433 = 23765575) B23765575
theorem B16646975 : Blo 810345 16646975 := bstep (se 1 (by rfl) ⟨12485231, by rfl⟩ : syracuseStep 16646975 = 24970463) B24970463
theorem B1541099 : Blo 810345 1541099 := bstep (se 1 (by rfl) ⟨1155824, by rfl⟩ : syracuseStep 1541099 = 2311649) B2311649
theorem B3082121 : Blo 810345 3082121 := bstep (se 2 (by rfl) ⟨1155795, by rfl⟩ : syracuseStep 3082121 = 2311591) B2311591
theorem B1542739 : Blo 810345 1542739 := bstep (se 1 (by rfl) ⟨1157054, by rfl⟩ : syracuseStep 1542739 = 2314109) B2314109
theorem B3476135 : Blo 810345 3476135 := bstep (se 1 (by rfl) ⟨2607101, by rfl⟩ : syracuseStep 3476135 = 5214203) B5214203
theorem B8785043 : Blo 810345 8785043 := bstep (se 1 (by rfl) ⟨6588782, by rfl⟩ : syracuseStep 8785043 = 13177565) B13177565
theorem B1543711 : Blo 810345 1543711 := bstep (se 1 (by rfl) ⟨1157783, by rfl⟩ : syracuseStep 1543711 = 2315567) B2315567
theorem B1216283 : Blo 810345 1216283 := bstep (se 1 (by rfl) ⟨912212, by rfl⟩ : syracuseStep 1216283 = 1824425) B1824425
theorem B1216367 : Blo 810345 1216367 := bstep (se 1 (by rfl) ⟨912275, by rfl⟩ : syracuseStep 1216367 = 1824551) B1824551
theorem B112300127 : Blo 810345 112300127 := bstep (se 1 (by rfl) ⟨84225095, by rfl⟩ : syracuseStep 112300127 = 168450191) B168450191
theorem B21107071 : Blo 810345 21107071 := bstep (se 1 (by rfl) ⟨15830303, by rfl⟩ : syracuseStep 21107071 = 31660607) B31660607
theorem B6951379 : Blo 810345 6951379 := bstep (se 1 (by rfl) ⟨5213534, by rfl⟩ : syracuseStep 6951379 = 10427069) B10427069
theorem B4952659 : Blo 810345 4952659 := bstep (se 1 (by rfl) ⟨3714494, by rfl⟩ : syracuseStep 4952659 = 7428989) B7428989
theorem B1217135 : Blo 810345 1217135 := bstep (se 1 (by rfl) ⟨912851, by rfl⟩ : syracuseStep 1217135 = 1825703) B1825703
theorem B1217255 : Blo 810345 1217255 := bstep (se 1 (by rfl) ⟨912941, by rfl⟩ : syracuseStep 1217255 = 1825883) B1825883
theorem B2921255 : Blo 810345 2921255 := bstep (se 1 (by rfl) ⟨2190941, by rfl⟩ : syracuseStep 2921255 = 4381883) B4381883
theorem B1217819 : Blo 810345 1217819 := bstep (se 1 (by rfl) ⟨913364, by rfl⟩ : syracuseStep 1217819 = 1826729) B1826729
theorem B824603 : Blo 810345 824603 := bstep (se 1 (by rfl) ⟨618452, by rfl⟩ : syracuseStep 824603 = 1236905) B1236905
theorem B3085735 : Blo 810345 3085735 := bstep (se 1 (by rfl) ⟨2314301, by rfl⟩ : syracuseStep 3085735 = 4628603) B4628603
theorem B24090295 : Blo 810345 24090295 := bstep (se 1 (by rfl) ⟨18067721, by rfl⟩ : syracuseStep 24090295 = 36135443) B36135443
theorem B1218287 : Blo 810345 1218287 := bstep (se 1 (by rfl) ⟨913715, by rfl⟩ : syracuseStep 1218287 = 1827431) B1827431
theorem B5216201 : Blo 810345 5216201 := bstep (se 2 (by rfl) ⟨1956075, by rfl⟩ : syracuseStep 5216201 = 3912151) B3912151
theorem B1219691 : Blo 810345 1219691 := bstep (se 1 (by rfl) ⟨914768, by rfl⟩ : syracuseStep 1219691 = 1829537) B1829537
theorem B4103297 : Blo 810345 4103297 := bstep (se 2 (by rfl) ⟨1538736, by rfl⟩ : syracuseStep 4103297 = 3077473) B3077473
theorem B1219931 : Blo 810345 1219931 := bstep (se 1 (by rfl) ⟨914948, by rfl⟩ : syracuseStep 1219931 = 1829897) B1829897
theorem B1220063 : Blo 810345 1220063 := bstep (se 1 (by rfl) ⟨915047, by rfl⟩ : syracuseStep 1220063 = 1830095) B1830095
theorem B1220591 : Blo 810345 1220591 := bstep (se 1 (by rfl) ⟨915443, by rfl⟩ : syracuseStep 1220591 = 1830887) B1830887
theorem B3088439 : Blo 810345 3088439 := bstep (se 1 (by rfl) ⟨2316329, by rfl⟩ : syracuseStep 3088439 = 4632659) B4632659
theorem B1220711 : Blo 810345 1220711 := bstep (se 1 (by rfl) ⟨915533, by rfl⟩ : syracuseStep 1220711 = 1831067) B1831067
theorem B1220831 : Blo 810345 1220831 := bstep (se 1 (by rfl) ⟨915623, by rfl⟩ : syracuseStep 1220831 = 1831247) B1831247
theorem B1220843 : Blo 810345 1220843 := bstep (se 1 (by rfl) ⟨915632, by rfl⟩ : syracuseStep 1220843 = 1831265) B1831265
theorem B1220891 : Blo 810345 1220891 := bstep (se 1 (by rfl) ⟨915668, by rfl⟩ : syracuseStep 1220891 = 1831337) B1831337
theorem B1220903 : Blo 810345 1220903 := bstep (se 1 (by rfl) ⟨915677, by rfl⟩ : syracuseStep 1220903 = 1831355) B1831355
theorem B1221095 : Blo 810345 1221095 := bstep (se 1 (by rfl) ⟨915821, by rfl⟩ : syracuseStep 1221095 = 1831643) B1831643
theorem B1221275 : Blo 810345 1221275 := bstep (se 1 (by rfl) ⟨915956, by rfl⟩ : syracuseStep 1221275 = 1831913) B1831913
theorem B6169283 : Blo 810345 6169283 := bstep (se 1 (by rfl) ⟨4626962, by rfl⟩ : syracuseStep 6169283 = 9253925) B9253925
theorem B6956027 : Blo 810345 6956027 := bstep (se 1 (by rfl) ⟨5217020, by rfl⟩ : syracuseStep 6956027 = 10434041) B10434041
theorem B2598247 : Blo 810345 2598247 := bstep (se 1 (by rfl) ⟨1948685, by rfl⟩ : syracuseStep 2598247 = 3897371) B3897371
theorem B1648039 : Blo 810345 1648039 := bstep (se 1 (by rfl) ⟨1236029, by rfl⟩ : syracuseStep 1648039 = 2472059) B2472059
theorem B7055399 : Blo 810345 7055399 := bstep (se 1 (by rfl) ⟨5291549, by rfl⟩ : syracuseStep 7055399 = 10583099) B10583099
theorem B17541197 : Blo 810345 17541197 := bstep (se 3 (by rfl) ⟨3288974, by rfl⟩ : syracuseStep 17541197 = 6577949) B6577949
theorem B2599067 : Blo 810345 2599067 := bstep (se 1 (by rfl) ⟨1949300, by rfl⟩ : syracuseStep 2599067 = 3898601) B3898601
theorem B1157447 : Blo 810345 1157447 := bstep (se 1 (by rfl) ⟨868085, by rfl⟩ : syracuseStep 1157447 = 1736171) B1736171
theorem B3516947 : Blo 810345 3516947 := bstep (se 1 (by rfl) ⟨2637710, by rfl⟩ : syracuseStep 3516947 = 5275421) B5275421
theorem B14035913 : Blo 810345 14035913 := bstep (se 2 (by rfl) ⟨5263467, by rfl⟩ : syracuseStep 14035913 = 10526935) B10526935
theorem B3091871 : Blo 810345 3091871 := bstep (se 1 (by rfl) ⟨2318903, by rfl⟩ : syracuseStep 3091871 = 4637807) B4637807
theorem B4631975 : Blo 810345 4631975 := bstep (se 1 (by rfl) ⟨3473981, by rfl⟩ : syracuseStep 4631975 = 6947963) B6947963
theorem B11710565 : Blo 810345 11710565 := bstep (se 4 (by rfl) ⟨1097865, by rfl⟩ : syracuseStep 11710565 = 2195731) B2195731
theorem B1028639 : Blo 810345 1028639 := bstep (se 1 (by rfl) ⟨771479, by rfl⟩ : syracuseStep 1028639 = 1542959) B1542959
theorem B4108967 : Blo 810345 4108967 := bstep (se 1 (by rfl) ⟨3081725, by rfl⟩ : syracuseStep 4108967 = 6163451) B6163451
theorem B3289967 : Blo 810345 3289967 := bstep (se 1 (by rfl) ⟨2467475, by rfl⟩ : syracuseStep 3289967 = 4934951) B4934951
theorem B1029287 : Blo 810345 1029287 := bstep (se 1 (by rfl) ⟨771965, by rfl⟩ : syracuseStep 1029287 = 1543931) B1543931
theorem B5846201 : Blo 810345 5846201 := bstep (se 2 (by rfl) ⟨2192325, by rfl⟩ : syracuseStep 5846201 = 4384651) B4384651
theorem B1029611 : Blo 810345 1029611 := bstep (se 1 (by rfl) ⟨772208, by rfl⟩ : syracuseStep 1029611 = 1544417) B1544417
theorem B6927869 : Blo 810345 6927869 := bstep (se 3 (by rfl) ⟨1298975, by rfl⟩ : syracuseStep 6927869 = 2597951) B2597951
theorem B6174629 : Blo 810345 6174629 := bstep (se 4 (by rfl) ⟨578871, by rfl⟩ : syracuseStep 6174629 = 1157743) B1157743
theorem B13154987 : Blo 810345 13154987 := bstep (se 1 (by rfl) ⟨9866240, by rfl⟩ : syracuseStep 13154987 = 19732481) B19732481
theorem B14072491 : Blo 810345 14072491 := bstep (se 1 (by rfl) ⟨10554368, by rfl⟩ : syracuseStep 14072491 = 21108737) B21108737
theorem B5192417 : Blo 810345 5192417 := bstep (se 2 (by rfl) ⟨1947156, by rfl⟩ : syracuseStep 5192417 = 3894313) B3894313
theorem B5848159 : Blo 810345 5848159 := bstep (se 1 (by rfl) ⟨4386119, by rfl⟩ : syracuseStep 5848159 = 8772239) B8772239
theorem B13909319 : Blo 810345 13909319 := bstep (se 1 (by rfl) ⟨10431989, by rfl⟩ : syracuseStep 13909319 = 20863979) B20863979
theorem B6929783 : Blo 810345 6929783 := bstep (se 1 (by rfl) ⟨5197337, by rfl⟩ : syracuseStep 6929783 = 10394675) B10394675
theorem B1850779 : Blo 810345 1850779 := bstep (se 1 (by rfl) ⟨1388084, by rfl⟩ : syracuseStep 1850779 = 2776169) B2776169
theorem B2736071 : Blo 810345 2736071 := bstep (se 1 (by rfl) ⟨2052053, by rfl⟩ : syracuseStep 2736071 = 4104107) B4104107
theorem B5849081 : Blo 810345 5849081 := bstep (se 2 (by rfl) ⟨2193405, by rfl⟩ : syracuseStep 5849081 = 4386811) B4386811
theorem B22528003 : Blo 810345 22528003 := bstep (se 1 (by rfl) ⟨16896002, by rfl⟩ : syracuseStep 22528003 = 33792005) B33792005
theorem B2736287 : Blo 810345 2736287 := bstep (se 1 (by rfl) ⟨2052215, by rfl⟩ : syracuseStep 2736287 = 4104431) B4104431
theorem B5194057 : Blo 810345 5194057 := bstep (se 2 (by rfl) ⟨1947771, by rfl⟩ : syracuseStep 5194057 = 3895543) B3895543
theorem B3293777 : Blo 810345 3293777 := bstep (se 2 (by rfl) ⟨1235166, by rfl⟩ : syracuseStep 3293777 = 2470333) B2470333
theorem B3523667 : Blo 810345 3523667 := bstep (se 1 (by rfl) ⟨2642750, by rfl⟩ : syracuseStep 3523667 = 5285501) B5285501
theorem B11715691 : Blo 810345 11715691 := bstep (se 1 (by rfl) ⟨8786768, by rfl⟩ : syracuseStep 11715691 = 17573537) B17573537
theorem B59327639 : Blo 810345 59327639 := bstep (se 1 (by rfl) ⟨44495729, by rfl⟩ : syracuseStep 59327639 = 88991459) B88991459
theorem B4933001 : Blo 810345 4933001 := bstep (se 2 (by rfl) ⟨1849875, by rfl⟩ : syracuseStep 4933001 = 3699751) B3699751
theorem B5556221 : Blo 810345 5556221 := bstep (se 3 (by rfl) ⟨1041791, by rfl⟩ : syracuseStep 5556221 = 2083583) B2083583
theorem B6572177 : Blo 810345 6572177 := bstep (se 2 (by rfl) ⟨2464566, by rfl⟩ : syracuseStep 6572177 = 4929133) B4929133
theorem B1460729 : Blo 810345 1460729 := bstep (se 2 (by rfl) ⟨547773, by rfl⟩ : syracuseStep 1460729 = 1095547) B1095547
theorem B2312833 : Blo 810345 2312833 := bstep (se 2 (by rfl) ⟨867312, by rfl⟩ : syracuseStep 2312833 = 1734625) B1734625
theorem B2739041 : Blo 810345 2739041 := bstep (se 2 (by rfl) ⟨1027140, by rfl⟩ : syracuseStep 2739041 = 2054281) B2054281
theorem B2739527 : Blo 810345 2739527 := bstep (se 1 (by rfl) ⟨2054645, by rfl⟩ : syracuseStep 2739527 = 4109291) B4109291
theorem B14077415 : Blo 810345 14077415 := bstep (se 1 (by rfl) ⟨10558061, by rfl⟩ : syracuseStep 14077415 = 21116123) B21116123
theorem B2739959 : Blo 810345 2739959 := bstep (se 1 (by rfl) ⟨2054969, by rfl⟩ : syracuseStep 2739959 = 4109939) B4109939
theorem B5197931 : Blo 810345 5197931 := bstep (se 1 (by rfl) ⟨3898448, by rfl⟩ : syracuseStep 5197931 = 7796897) B7796897
theorem B45175151 : Blo 810345 45175151 := bstep (se 1 (by rfl) ⟨33881363, by rfl⟩ : syracuseStep 45175151 = 67762727) B67762727
theorem B4116905 : Blo 810345 4116905 := bstep (se 2 (by rfl) ⟨1543839, by rfl⟩ : syracuseStep 4116905 = 3087679) B3087679
theorem B6181433 : Blo 810345 6181433 := bstep (se 2 (by rfl) ⟨2318037, by rfl⟩ : syracuseStep 6181433 = 4636075) B4636075
theorem B18764435 : Blo 810345 18764435 := bstep (se 1 (by rfl) ⟨14073326, by rfl⟩ : syracuseStep 18764435 = 28146653) B28146653
theorem B1463015 : Blo 810345 1463015 := bstep (se 1 (by rfl) ⟨1097261, by rfl⟩ : syracuseStep 1463015 = 2194523) B2194523
theorem B2741039 : Blo 810345 2741039 := bstep (se 1 (by rfl) ⟨2055779, by rfl⟩ : syracuseStep 2741039 = 4111559) B4111559
theorem B4117391 : Blo 810345 4117391 := bstep (se 1 (by rfl) ⟨3088043, by rfl⟩ : syracuseStep 4117391 = 6176087) B6176087
theorem B13161469 : Blo 810345 13161469 := bstep (se 3 (by rfl) ⟨2467775, by rfl⟩ : syracuseStep 13161469 = 4935551) B4935551
theorem B2741471 : Blo 810345 2741471 := bstep (se 1 (by rfl) ⟨2056103, by rfl⟩ : syracuseStep 2741471 = 4112207) B4112207
theorem B1824479 : Blo 810345 1824479 := bstep (se 1 (by rfl) ⟨1368359, by rfl⟩ : syracuseStep 1824479 = 2736719) B2736719
theorem B2742281 : Blo 810345 2742281 := bstep (se 2 (by rfl) ⟨1028355, by rfl⟩ : syracuseStep 2742281 = 2056711) B2056711
theorem B1824839 : Blo 810345 1824839 := bstep (se 1 (by rfl) ⟨1368629, by rfl⟩ : syracuseStep 1824839 = 2737259) B2737259
theorem B2316671 : Blo 810345 2316671 := bstep (se 1 (by rfl) ⟨1737503, by rfl⟩ : syracuseStep 2316671 = 3475007) B3475007
theorem B11688421 : Blo 810345 11688421 := bstep (se 4 (by rfl) ⟨1095789, by rfl⟩ : syracuseStep 11688421 = 2191579) B2191579
theorem B2317025 : Blo 810345 2317025 := bstep (se 2 (by rfl) ⟨868884, by rfl⟩ : syracuseStep 2317025 = 1737769) B1737769
theorem B216914861 : Blo 810345 216914861 := bstep (se 3 (by rfl) ⟨40671536, by rfl⟩ : syracuseStep 216914861 = 81343073) B81343073
theorem B1825847 : Blo 810345 1825847 := bstep (se 1 (by rfl) ⟨1369385, by rfl⟩ : syracuseStep 1825847 = 2738771) B2738771
theorem B810395 : Blo 810345 810395 := bstep (se 1 (by rfl) ⟨607796, by rfl⟩ : syracuseStep 810395 = 1215593) B1215593
theorem B810479 : Blo 810345 810479 := bstep (se 1 (by rfl) ⟨607859, by rfl⟩ : syracuseStep 810479 = 1215719) B1215719
theorem B810815 : Blo 810345 810815 := bstep (se 1 (by rfl) ⟨608111, by rfl⟩ : syracuseStep 810815 = 1216223) B1216223
theorem B1367975 : Blo 810345 1367975 := bstep (se 1 (by rfl) ⟨1025981, by rfl⟩ : syracuseStep 1367975 = 2051963) B2051963
theorem B811003 : Blo 810345 811003 := bstep (se 1 (by rfl) ⟨608252, by rfl⟩ : syracuseStep 811003 = 1216505) B1216505
theorem B811135 : Blo 810345 811135 := bstep (se 1 (by rfl) ⟨608351, by rfl⟩ : syracuseStep 811135 = 1216703) B1216703
theorem B811163 : Blo 810345 811163 := bstep (se 1 (by rfl) ⟨608372, by rfl⟩ : syracuseStep 811163 = 1216745) B1216745
theorem B811247 : Blo 810345 811247 := bstep (se 1 (by rfl) ⟨608435, by rfl⟩ : syracuseStep 811247 = 1216871) B1216871
theorem B3465611 : Blo 810345 3465611 := bstep (se 1 (by rfl) ⟨2599208, by rfl⟩ : syracuseStep 3465611 = 5198417) B5198417
theorem B811803 : Blo 810345 811803 := bstep (se 1 (by rfl) ⟨608852, by rfl⟩ : syracuseStep 811803 = 1217705) B1217705
theorem B811847 : Blo 810345 811847 := bstep (se 1 (by rfl) ⟨608885, by rfl⟩ : syracuseStep 811847 = 1217771) B1217771
theorem B4940615 : Blo 810345 4940615 := bstep (se 1 (by rfl) ⟨3705461, by rfl⟩ : syracuseStep 4940615 = 7410923) B7410923
theorem B811903 : Blo 810345 811903 := bstep (se 1 (by rfl) ⟨608927, by rfl⟩ : syracuseStep 811903 = 1217855) B1217855
theorem B812031 : Blo 810345 812031 := bstep (se 1 (by rfl) ⟨609023, by rfl⟩ : syracuseStep 812031 = 1218047) B1218047
theorem B812103 : Blo 810345 812103 := bstep (se 1 (by rfl) ⟨609077, by rfl⟩ : syracuseStep 812103 = 1218155) B1218155
theorem B1369183 : Blo 810345 1369183 := bstep (se 1 (by rfl) ⟨1026887, by rfl⟩ : syracuseStep 1369183 = 2053775) B2053775
theorem B812283 : Blo 810345 812283 := bstep (se 1 (by rfl) ⟨609212, by rfl⟩ : syracuseStep 812283 = 1218425) B1218425
theorem B10544393 : Blo 810345 10544393 := bstep (se 2 (by rfl) ⟨3954147, by rfl⟩ : syracuseStep 10544393 = 7908295) B7908295
theorem B5563721 : Blo 810345 5563721 := bstep (se 2 (by rfl) ⟨2086395, by rfl⟩ : syracuseStep 5563721 = 4172791) B4172791
theorem B812447 : Blo 810345 812447 := bstep (se 1 (by rfl) ⟨609335, by rfl⟩ : syracuseStep 812447 = 1218671) B1218671
theorem B812495 : Blo 810345 812495 := bstep (se 1 (by rfl) ⟨609371, by rfl⟩ : syracuseStep 812495 = 1218743) B1218743
theorem B1369595 : Blo 810345 1369595 := bstep (se 1 (by rfl) ⟨1027196, by rfl⟩ : syracuseStep 1369595 = 2054393) B2054393
theorem B6940241 : Blo 810345 6940241 := bstep (se 2 (by rfl) ⟨2602590, by rfl⟩ : syracuseStep 6940241 = 5205181) B5205181
theorem B1369703 : Blo 810345 1369703 := bstep (se 1 (by rfl) ⟨1027277, by rfl⟩ : syracuseStep 1369703 = 2054555) B2054555
theorem B1828457 : Blo 810345 1828457 := bstep (se 2 (by rfl) ⟨685671, by rfl⟩ : syracuseStep 1828457 = 1371343) B1371343
theorem B1500905 : Blo 810345 1500905 := bstep (se 2 (by rfl) ⟨562839, by rfl⟩ : syracuseStep 1500905 = 1125679) B1125679
theorem B812775 : Blo 810345 812775 := bstep (se 1 (by rfl) ⟨609581, by rfl⟩ : syracuseStep 812775 = 1219163) B1219163
theorem B812783 : Blo 810345 812783 := bstep (se 1 (by rfl) ⟨609587, by rfl⟩ : syracuseStep 812783 = 1219175) B1219175
theorem B812799 : Blo 810345 812799 := bstep (se 1 (by rfl) ⟨609599, by rfl⟩ : syracuseStep 812799 = 1219199) B1219199
theorem B812871 : Blo 810345 812871 := bstep (se 1 (by rfl) ⟨609653, by rfl⟩ : syracuseStep 812871 = 1219307) B1219307
theorem B812891 : Blo 810345 812891 := bstep (se 1 (by rfl) ⟨609668, by rfl⟩ : syracuseStep 812891 = 1219337) B1219337
theorem B813051 : Blo 810345 813051 := bstep (se 1 (by rfl) ⟨609788, by rfl⟩ : syracuseStep 813051 = 1219577) B1219577
theorem B2746439 : Blo 810345 2746439 := bstep (se 1 (by rfl) ⟨2059829, by rfl⟩ : syracuseStep 2746439 = 4119659) B4119659
theorem B19753105 : Blo 810345 19753105 := bstep (se 2 (by rfl) ⟨7407414, by rfl⟩ : syracuseStep 19753105 = 14814829) B14814829
theorem B813471 : Blo 810345 813471 := bstep (se 1 (by rfl) ⟨610103, by rfl⟩ : syracuseStep 813471 = 1220207) B1220207
theorem B813551 : Blo 810345 813551 := bstep (se 1 (by rfl) ⟨610163, by rfl⟩ : syracuseStep 813551 = 1220327) B1220327
theorem B977519 : Blo 810345 977519 := bstep (se 1 (by rfl) ⟨733139, by rfl⟩ : syracuseStep 977519 = 1466279) B1466279
theorem B813735 : Blo 810345 813735 := bstep (se 1 (by rfl) ⟨610301, by rfl⟩ : syracuseStep 813735 = 1220603) B1220603
theorem B813775 : Blo 810345 813775 := bstep (se 1 (by rfl) ⟨610331, by rfl⟩ : syracuseStep 813775 = 1220663) B1220663
theorem B813855 : Blo 810345 813855 := bstep (se 1 (by rfl) ⟨610391, by rfl⟩ : syracuseStep 813855 = 1220783) B1220783
theorem B912199 : Blo 810345 912199 := bstep (se 1 (by rfl) ⟨684149, by rfl⟩ : syracuseStep 912199 = 1368299) B1368299
theorem B1829753 : Blo 810345 1829753 := bstep (se 2 (by rfl) ⟨686157, by rfl⟩ : syracuseStep 1829753 = 1372315) B1372315
theorem B813991 : Blo 810345 813991 := bstep (se 1 (by rfl) ⟨610493, by rfl⟩ : syracuseStep 813991 = 1220987) B1220987
theorem B814107 : Blo 810345 814107 := bstep (se 1 (by rfl) ⟨610580, by rfl⟩ : syracuseStep 814107 = 1221161) B1221161
theorem B814171 : Blo 810345 814171 := bstep (se 1 (by rfl) ⟨610628, by rfl⟩ : syracuseStep 814171 = 1221257) B1221257
theorem B1830113 : Blo 810345 1830113 := bstep (se 2 (by rfl) ⟨686292, by rfl⟩ : syracuseStep 1830113 = 1372585) B1372585
theorem B814311 : Blo 810345 814311 := bstep (se 1 (by rfl) ⟨610733, by rfl⟩ : syracuseStep 814311 = 1221467) B1221467
theorem B814335 : Blo 810345 814335 := bstep (se 1 (by rfl) ⟨610751, by rfl⟩ : syracuseStep 814335 = 1221503) B1221503
theorem B5565833 : Blo 810345 5565833 := bstep (se 2 (by rfl) ⟨2087187, by rfl⟩ : syracuseStep 5565833 = 4174375) B4174375
theorem B2060063 : Blo 810345 2060063 := bstep (se 1 (by rfl) ⟨1545047, by rfl⟩ : syracuseStep 2060063 = 3090095) B3090095
theorem B1732583 : Blo 810345 1732583 := bstep (se 1 (by rfl) ⟨1299437, by rfl⟩ : syracuseStep 1732583 = 2598875) B2598875
theorem B112325039 : Blo 810345 112325039 := bstep (se 1 (by rfl) ⟨84243779, by rfl⟩ : syracuseStep 112325039 = 168487559) B168487559
theorem B8352359 : Blo 810345 8352359 := bstep (se 1 (by rfl) ⟨6264269, by rfl⟩ : syracuseStep 8352359 = 12528539) B12528539
theorem B1832057 : Blo 810345 1832057 := bstep (se 2 (by rfl) ⟨687021, by rfl⟩ : syracuseStep 1832057 = 1374043) B1374043
theorem B20772125 : Blo 810345 20772125 := bstep (se 3 (by rfl) ⟨3894773, by rfl⟩ : syracuseStep 20772125 = 7789547) B7789547
theorem B1734223 : Blo 810345 1734223 := bstep (se 1 (by rfl) ⟨1300667, by rfl⟩ : syracuseStep 1734223 = 2601335) B2601335
theorem B916015 : Blo 810345 916015 := bstep (se 1 (by rfl) ⟨687011, by rfl⟩ : syracuseStep 916015 = 1374023) B1374023
theorem B1539155 : Blo 810345 1539155 := bstep (se 1 (by rfl) ⟨1154366, by rfl⟩ : syracuseStep 1539155 = 2308733) B2308733
theorem B7405519 : Blo 810345 7405519 := bstep (se 1 (by rfl) ⟨5554139, by rfl⟩ : syracuseStep 7405519 = 11108279) B11108279
theorem B3866807 : Blo 810345 3866807 := bstep (se 1 (by rfl) ⟨2900105, by rfl⟩ : syracuseStep 3866807 = 5800211) B5800211
theorem B2195851 : Blo 810345 2195851 := bstep (se 1 (by rfl) ⟨1646888, by rfl⟩ : syracuseStep 2195851 = 3293777) B3293777
theorem B39551759 : Blo 810345 39551759 := bstep (se 1 (by rfl) ⟨29663819, by rfl⟩ : syracuseStep 39551759 = 59327639) B59327639
theorem B3704147 : Blo 810345 3704147 := bstep (se 1 (by rfl) ⟨2778110, by rfl⟩ : syracuseStep 3704147 = 5556221) B5556221
theorem B2197385 : Blo 810345 2197385 := bstep (se 2 (by rfl) ⟨824019, by rfl⟩ : syracuseStep 2197385 = 1648039) B1648039
theorem B30116767 : Blo 810345 30116767 := bstep (se 1 (by rfl) ⟨22587575, by rfl⟩ : syracuseStep 30116767 = 45175151) B45175151
theorem B3083777 : Blo 810345 3083777 := bstep (se 2 (by rfl) ⟨1156416, by rfl⟩ : syracuseStep 3083777 = 2312833) B2312833
theorem B1216265 : Blo 810345 1216265 := bstep (se 2 (by rfl) ⟨456099, by rfl⟩ : syracuseStep 1216265 = 912199) B912199
theorem B1216319 : Blo 810345 1216319 := bstep (se 1 (by rfl) ⟨912239, by rfl⟩ : syracuseStep 1216319 = 1824479) B1824479
theorem B3477467 : Blo 810345 3477467 := bstep (se 1 (by rfl) ⟨2608100, by rfl⟩ : syracuseStep 3477467 = 5216201) B5216201
theorem B1216559 : Blo 810345 1216559 := bstep (se 1 (by rfl) ⟨912419, by rfl⟩ : syracuseStep 1216559 = 1824839) B1824839
theorem B1544447 : Blo 810345 1544447 := bstep (se 1 (by rfl) ⟨1158335, by rfl⟩ : syracuseStep 1544447 = 2316671) B2316671
theorem B1544683 : Blo 810345 1544683 := bstep (se 1 (by rfl) ⟨1158512, by rfl⟩ : syracuseStep 1544683 = 2317025) B2317025
theorem B1217231 : Blo 810345 1217231 := bstep (se 1 (by rfl) ⟨912923, by rfl⟩ : syracuseStep 1217231 = 1825847) B1825847
theorem B3086525 : Blo 810345 3086525 := bstep (se 3 (by rfl) ⟨578723, by rfl⟩ : syracuseStep 3086525 = 1157447) B1157447
theorem B3709147 : Blo 810345 3709147 := bstep (se 1 (by rfl) ⟨2781860, by rfl⟩ : syracuseStep 3709147 = 5563721) B5563721
theorem B4626827 : Blo 810345 4626827 := bstep (se 1 (by rfl) ⟨3470120, by rfl⟩ : syracuseStep 4626827 = 6940241) B6940241
theorem B1218971 : Blo 810345 1218971 := bstep (se 1 (by rfl) ⟨914228, by rfl⟩ : syracuseStep 1218971 = 1828457) B1828457
theorem B1219835 : Blo 810345 1219835 := bstep (se 1 (by rfl) ⟨914876, by rfl⟩ : syracuseStep 1219835 = 1829753) B1829753
theorem B9870821 : Blo 810345 9870821 := bstep (se 4 (by rfl) ⟨925389, by rfl⟩ : syracuseStep 9870821 = 1850779) B1850779
theorem B1220075 : Blo 810345 1220075 := bstep (se 1 (by rfl) ⟨915056, by rfl⟩ : syracuseStep 1220075 = 1830113) B1830113
theorem B32120393 : Blo 810345 32120393 := bstep (se 2 (by rfl) ⟨12045147, by rfl⟩ : syracuseStep 32120393 = 24090295) B24090295
theorem B3710555 : Blo 810345 3710555 := bstep (se 1 (by rfl) ⟨2782916, by rfl⟩ : syracuseStep 3710555 = 5565833) B5565833
theorem B3087983 : Blo 810345 3087983 := bstep (se 1 (by rfl) ⟨2315987, by rfl⟩ : syracuseStep 3087983 = 4631975) B4631975
theorem B1155055 : Blo 810345 1155055 := bstep (se 1 (by rfl) ⟨866291, by rfl⟩ : syracuseStep 1155055 = 1732583) B1732583
theorem B7807043 : Blo 810345 7807043 := bstep (se 1 (by rfl) ⟨5855282, by rfl⟩ : syracuseStep 7807043 = 11710565) B11710565
theorem B74883359 : Blo 810345 74883359 := bstep (se 1 (by rfl) ⟨56162519, by rfl⟩ : syracuseStep 74883359 = 112325039) B112325039
theorem B1221353 : Blo 810345 1221353 := bstep (se 2 (by rfl) ⟨458007, by rfl⟩ : syracuseStep 1221353 = 916015) B916015
theorem B1221371 : Blo 810345 1221371 := bstep (se 1 (by rfl) ⟨916028, by rfl⟩ : syracuseStep 1221371 = 1832057) B1832057
theorem B1026103 : Blo 810345 1026103 := bstep (se 1 (by rfl) ⟨769577, by rfl⟩ : syracuseStep 1026103 = 1539155) B1539155
theorem B9874025 : Blo 810345 9874025 := bstep (se 2 (by rfl) ⟨3702759, by rfl⟩ : syracuseStep 9874025 = 7405519) B7405519
theorem B6925409 : Blo 810345 6925409 := bstep (se 2 (by rfl) ⟨2597028, by rfl⟩ : syracuseStep 6925409 = 5194057) B5194057
theorem B1027399 : Blo 810345 1027399 := bstep (se 1 (by rfl) ⟨770549, by rfl⟩ : syracuseStep 1027399 = 1541099) B1541099
theorem B8795765 : Blo 810345 8795765 := bstep (se 5 (by rfl) ⟨412301, by rfl⟩ : syracuseStep 8795765 = 824603) B824603
theorem B1947503 : Blo 810345 1947503 := bstep (se 1 (by rfl) ⟨1460627, by rfl⟩ : syracuseStep 1947503 = 2921255) B2921255
theorem B13154669 : Blo 810345 13154669 := bstep (se 3 (by rfl) ⟨2466500, by rfl⟩ : syracuseStep 13154669 = 4933001) B4933001
theorem B2735531 : Blo 810345 2735531 := bstep (se 1 (by rfl) ⟨2051648, by rfl⟩ : syracuseStep 2735531 = 4103297) B4103297
theorem B2310407 : Blo 810345 2310407 := bstep (se 1 (by rfl) ⟨1732805, by rfl⟩ : syracuseStep 2310407 = 3465611) B3465611
theorem B6930845 : Blo 810345 6930845 := bstep (se 3 (by rfl) ⟨1299533, by rfl⟩ : syracuseStep 6930845 = 2599067) B2599067
theorem B4112855 : Blo 810345 4112855 := bstep (se 1 (by rfl) ⟨3084641, by rfl⟩ : syracuseStep 4112855 = 6169283) B6169283
theorem B3293743 : Blo 810345 3293743 := bstep (se 1 (by rfl) ⟨2470307, by rfl⟩ : syracuseStep 3293743 = 4940615) B4940615
theorem B4637351 : Blo 810345 4637351 := bstep (se 1 (by rfl) ⟨3478013, by rfl⟩ : syracuseStep 4637351 = 6956027) B6956027
theorem B6603545 : Blo 810345 6603545 := bstep (se 2 (by rfl) ⟨2476329, by rfl⟩ : syracuseStep 6603545 = 4952659) B4952659
theorem B7029595 : Blo 810345 7029595 := bstep (se 1 (by rfl) ⟨5272196, by rfl⟩ : syracuseStep 7029595 = 10544393) B10544393
theorem B1000603 : Blo 810345 1000603 := bstep (se 1 (by rfl) ⟨750452, by rfl⟩ : syracuseStep 1000603 = 1500905) B1500905
theorem B17548625 : Blo 810345 17548625 := bstep (se 2 (by rfl) ⟨6580734, by rfl⟩ : syracuseStep 17548625 = 13161469) B13161469
theorem B4703599 : Blo 810345 4703599 := bstep (se 1 (by rfl) ⟨3527699, by rfl⟩ : syracuseStep 4703599 = 7055399) B7055399
theorem B2606717 : Blo 810345 2606717 := bstep (se 3 (by rfl) ⟨488759, by rfl⟩ : syracuseStep 2606717 = 977519) B977519
theorem B2344631 : Blo 810345 2344631 := bstep (se 1 (by rfl) ⟨1758473, by rfl⟩ : syracuseStep 2344631 = 3516947) B3516947
theorem B4114313 : Blo 810345 4114313 := bstep (se 2 (by rfl) ⟨1542867, by rfl⟩ : syracuseStep 4114313 = 3085735) B3085735
theorem B9357275 : Blo 810345 9357275 := bstep (se 1 (by rfl) ⟨7017956, by rfl⟩ : syracuseStep 9357275 = 14035913) B14035913
theorem B2312297 : Blo 810345 2312297 := bstep (se 2 (by rfl) ⟨867111, by rfl⟩ : syracuseStep 2312297 = 1734223) B1734223
theorem B578439629 : Blo 810345 578439629 := bstep (se 3 (by rfl) ⟨108457430, by rfl⟩ : syracuseStep 578439629 = 216914861) B216914861
theorem B2739311 : Blo 810345 2739311 := bstep (se 1 (by rfl) ⟨2054483, by rfl⟩ : syracuseStep 2739311 = 4108967) B4108967
theorem B15584561 : Blo 810345 15584561 := bstep (se 2 (by rfl) ⟨5844210, by rfl⟩ : syracuseStep 15584561 = 11688421) B11688421
theorem B13848083 : Blo 810345 13848083 := bstep (se 1 (by rfl) ⟨10386062, by rfl⟩ : syracuseStep 13848083 = 20772125) B20772125
theorem B18763321 : Blo 810345 18763321 := bstep (se 2 (by rfl) ⟨7036245, by rfl⟩ : syracuseStep 18763321 = 14072491) B14072491
theorem B37539773 : Blo 810345 37539773 := bstep (se 3 (by rfl) ⟨7038707, by rfl⟩ : syracuseStep 37539773 = 14077415) B14077415
theorem B4116419 : Blo 810345 4116419 := bstep (se 1 (by rfl) ⟨3087314, by rfl⟩ : syracuseStep 4116419 = 6174629) B6174629
theorem B8769991 : Blo 810345 8769991 := bstep (se 1 (by rfl) ⟨6577493, by rfl⟩ : syracuseStep 8769991 = 13154987) B13154987
theorem B3461611 : Blo 810345 3461611 := bstep (se 1 (by rfl) ⟨2596208, by rfl⟩ : syracuseStep 3461611 = 5192417) B5192417
theorem B1824047 : Blo 810345 1824047 := bstep (se 1 (by rfl) ⟨1368035, by rfl⟩ : syracuseStep 1824047 = 2736071) B2736071
theorem B30037337 : Blo 810345 30037337 := bstep (se 2 (by rfl) ⟨11264001, by rfl⟩ : syracuseStep 30037337 = 22528003) B22528003
theorem B1824191 : Blo 810345 1824191 := bstep (se 1 (by rfl) ⟨1368143, by rfl⟩ : syracuseStep 1824191 = 2736287) B2736287
theorem B2316023 : Blo 810345 2316023 := bstep (se 1 (by rfl) ⟨1737017, by rfl⟩ : syracuseStep 2316023 = 3474035) B3474035
theorem B21124955 : Blo 810345 21124955 := bstep (se 1 (by rfl) ⟨15843716, by rfl⟩ : syracuseStep 21124955 = 31687433) B31687433
theorem B11097983 : Blo 810345 11097983 := bstep (se 1 (by rfl) ⟨8323487, by rfl⟩ : syracuseStep 11097983 = 16646975) B16646975
theorem B2054747 : Blo 810345 2054747 := bstep (se 1 (by rfl) ⟨1541060, by rfl⟩ : syracuseStep 2054747 = 3082121) B3082121
theorem B2743037 : Blo 810345 2743037 := bstep (se 3 (by rfl) ⟨514319, by rfl⟩ : syracuseStep 2743037 = 1028639) B1028639
theorem B4381451 : Blo 810345 4381451 := bstep (se 1 (by rfl) ⟨3286088, by rfl⟩ : syracuseStep 4381451 = 6572177) B6572177
theorem B1825577 : Blo 810345 1825577 := bstep (se 2 (by rfl) ⟨684591, by rfl⟩ : syracuseStep 1825577 = 1369183) B1369183
theorem B15620921 : Blo 810345 15620921 := bstep (se 2 (by rfl) ⟨5857845, by rfl⟩ : syracuseStep 15620921 = 11715691) B11715691
theorem B973819 : Blo 810345 973819 := bstep (se 1 (by rfl) ⟨730364, by rfl⟩ : syracuseStep 973819 = 1460729) B1460729
theorem B2317423 : Blo 810345 2317423 := bstep (se 1 (by rfl) ⟨1738067, by rfl⟩ : syracuseStep 2317423 = 3476135) B3476135
theorem B3464329 : Blo 810345 3464329 := bstep (se 2 (by rfl) ⟨1299123, by rfl⟩ : syracuseStep 3464329 = 2598247) B2598247
theorem B1826027 : Blo 810345 1826027 := bstep (se 1 (by rfl) ⟨1369520, by rfl⟩ : syracuseStep 1826027 = 2739041) B2739041
theorem B5856695 : Blo 810345 5856695 := bstep (se 1 (by rfl) ⟨4392521, by rfl⟩ : syracuseStep 5856695 = 8785043) B8785043
theorem B1826351 : Blo 810345 1826351 := bstep (se 1 (by rfl) ⟨1369763, by rfl⟩ : syracuseStep 1826351 = 2739527) B2739527
theorem B1826639 : Blo 810345 1826639 := bstep (se 1 (by rfl) ⟨1369979, by rfl⟩ : syracuseStep 1826639 = 2739959) B2739959
theorem B810855 : Blo 810345 810855 := bstep (se 1 (by rfl) ⟨608141, by rfl⟩ : syracuseStep 810855 = 1216283) B1216283
theorem B810911 : Blo 810345 810911 := bstep (se 1 (by rfl) ⟨608183, by rfl⟩ : syracuseStep 810911 = 1216367) B1216367
theorem B74866751 : Blo 810345 74866751 := bstep (se 1 (by rfl) ⟨56150063, by rfl⟩ : syracuseStep 74866751 = 112300127) B112300127
theorem B3465287 : Blo 810345 3465287 := bstep (se 1 (by rfl) ⟨2598965, by rfl⟩ : syracuseStep 3465287 = 5197931) B5197931
theorem B26337473 : Blo 810345 26337473 := bstep (se 2 (by rfl) ⟨9876552, by rfl⟩ : syracuseStep 26337473 = 19753105) B19753105
theorem B9396445 : Blo 810345 9396445 := bstep (se 3 (by rfl) ⟨1761833, by rfl⟩ : syracuseStep 9396445 = 3523667) B3523667
theorem B2744603 : Blo 810345 2744603 := bstep (se 1 (by rfl) ⟨2058452, by rfl⟩ : syracuseStep 2744603 = 4116905) B4116905
theorem B4120955 : Blo 810345 4120955 := bstep (se 1 (by rfl) ⟨3090716, by rfl⟩ : syracuseStep 4120955 = 6181433) B6181433
theorem B811423 : Blo 810345 811423 := bstep (se 1 (by rfl) ⟨608567, by rfl⟩ : syracuseStep 811423 = 1217135) B1217135
theorem B12509623 : Blo 810345 12509623 := bstep (se 1 (by rfl) ⟨9382217, by rfl⟩ : syracuseStep 12509623 = 18764435) B18764435
theorem B2744765 : Blo 810345 2744765 := bstep (se 3 (by rfl) ⟨514643, by rfl⟩ : syracuseStep 2744765 = 1029287) B1029287
theorem B811503 : Blo 810345 811503 := bstep (se 1 (by rfl) ⟨608627, by rfl⟩ : syracuseStep 811503 = 1217255) B1217255
theorem B975343 : Blo 810345 975343 := bstep (se 1 (by rfl) ⟨731507, by rfl⟩ : syracuseStep 975343 = 1463015) B1463015
theorem B1827359 : Blo 810345 1827359 := bstep (se 1 (by rfl) ⟨1370519, by rfl⟩ : syracuseStep 1827359 = 2741039) B2741039
theorem B2744927 : Blo 810345 2744927 := bstep (se 1 (by rfl) ⟨2058695, by rfl⟩ : syracuseStep 2744927 = 4117391) B4117391
theorem B2056985 : Blo 810345 2056985 := bstep (se 2 (by rfl) ⟨771369, by rfl⟩ : syracuseStep 2056985 = 1542739) B1542739
theorem B1827647 : Blo 810345 1827647 := bstep (se 1 (by rfl) ⟨1370735, by rfl⟩ : syracuseStep 1827647 = 2741471) B2741471
theorem B811879 : Blo 810345 811879 := bstep (se 1 (by rfl) ⟨608909, by rfl⟩ : syracuseStep 811879 = 1217819) B1217819
theorem B812191 : Blo 810345 812191 := bstep (se 1 (by rfl) ⟨609143, by rfl⟩ : syracuseStep 812191 = 1218287) B1218287
theorem B2745629 : Blo 810345 2745629 := bstep (se 3 (by rfl) ⟨514805, by rfl⟩ : syracuseStep 2745629 = 1029611) B1029611
theorem B1828187 : Blo 810345 1828187 := bstep (se 1 (by rfl) ⟨1371140, by rfl⟩ : syracuseStep 1828187 = 2742281) B2742281
theorem B2058281 : Blo 810345 2058281 := bstep (se 2 (by rfl) ⟨771855, by rfl⟩ : syracuseStep 2058281 = 1543711) B1543711
theorem B813127 : Blo 810345 813127 := bstep (se 1 (by rfl) ⟨609845, by rfl⟩ : syracuseStep 813127 = 1219691) B1219691
theorem B813287 : Blo 810345 813287 := bstep (se 1 (by rfl) ⟨609965, by rfl⟩ : syracuseStep 813287 = 1219931) B1219931
theorem B813375 : Blo 810345 813375 := bstep (se 1 (by rfl) ⟨610031, by rfl⟩ : syracuseStep 813375 = 1220063) B1220063
theorem B911983 : Blo 810345 911983 := bstep (se 1 (by rfl) ⟨683987, by rfl⟩ : syracuseStep 911983 = 1367975) B1367975
theorem B813727 : Blo 810345 813727 := bstep (se 1 (by rfl) ⟨610295, by rfl⟩ : syracuseStep 813727 = 1220591) B1220591
theorem B2058959 : Blo 810345 2058959 := bstep (se 1 (by rfl) ⟨1544219, by rfl⟩ : syracuseStep 2058959 = 3088439) B3088439
theorem B813807 : Blo 810345 813807 := bstep (se 1 (by rfl) ⟨610355, by rfl⟩ : syracuseStep 813807 = 1220711) B1220711
theorem B813887 : Blo 810345 813887 := bstep (se 1 (by rfl) ⟨610415, by rfl⟩ : syracuseStep 813887 = 1220831) B1220831
theorem B813895 : Blo 810345 813895 := bstep (se 1 (by rfl) ⟨610421, by rfl⟩ : syracuseStep 813895 = 1220843) B1220843
theorem B813927 : Blo 810345 813927 := bstep (se 1 (by rfl) ⟨610445, by rfl⟩ : syracuseStep 813927 = 1220891) B1220891
theorem B813935 : Blo 810345 813935 := bstep (se 1 (by rfl) ⟨610451, by rfl⟩ : syracuseStep 813935 = 1220903) B1220903
theorem B814063 : Blo 810345 814063 := bstep (se 1 (by rfl) ⟨610547, by rfl⟩ : syracuseStep 814063 = 1221095) B1221095
theorem B814183 : Blo 810345 814183 := bstep (se 1 (by rfl) ⟨610637, by rfl⟩ : syracuseStep 814183 = 1221275) B1221275
theorem B28142761 : Blo 810345 28142761 := bstep (se 2 (by rfl) ⟨10553535, by rfl⟩ : syracuseStep 28142761 = 21107071) B21107071
theorem B9268505 : Blo 810345 9268505 := bstep (se 2 (by rfl) ⟨3475689, by rfl⟩ : syracuseStep 9268505 = 6951379) B6951379
theorem B913063 : Blo 810345 913063 := bstep (se 1 (by rfl) ⟨684797, by rfl⟩ : syracuseStep 913063 = 1369595) B1369595
theorem B913135 : Blo 810345 913135 := bstep (se 1 (by rfl) ⟨684851, by rfl⟩ : syracuseStep 913135 = 1369703) B1369703
theorem B1830959 : Blo 810345 1830959 := bstep (se 1 (by rfl) ⟨1373219, by rfl⟩ : syracuseStep 1830959 = 2746439) B2746439
theorem B11694131 : Blo 810345 11694131 := bstep (se 1 (by rfl) ⟨8770598, by rfl⟩ : syracuseStep 11694131 = 17541197) B17541197
theorem B2061247 : Blo 810345 2061247 := bstep (se 1 (by rfl) ⟨1545935, by rfl⟩ : syracuseStep 2061247 = 3091871) B3091871
theorem B1373375 : Blo 810345 1373375 := bstep (se 1 (by rfl) ⟨1030031, by rfl⟩ : syracuseStep 1373375 = 2060063) B2060063
theorem B5568239 : Blo 810345 5568239 := bstep (se 1 (by rfl) ⟨4176179, by rfl⟩ : syracuseStep 5568239 = 8352359) B8352359
theorem B2193311 : Blo 810345 2193311 := bstep (se 1 (by rfl) ⟨1644983, by rfl⟩ : syracuseStep 2193311 = 3289967) B3289967
theorem B3897467 : Blo 810345 3897467 := bstep (se 1 (by rfl) ⟨2923100, by rfl⟩ : syracuseStep 3897467 = 5846201) B5846201
theorem B4618579 : Blo 810345 4618579 := bstep (se 1 (by rfl) ⟨3463934, by rfl⟩ : syracuseStep 4618579 = 6927869) B6927869
theorem B7797545 : Blo 810345 7797545 := bstep (se 2 (by rfl) ⟨2924079, by rfl⟩ : syracuseStep 7797545 = 5848159) B5848159
theorem B9272879 : Blo 810345 9272879 := bstep (se 1 (by rfl) ⟨6954659, by rfl⟩ : syracuseStep 9272879 = 13909319) B13909319
theorem B4619855 : Blo 810345 4619855 := bstep (se 1 (by rfl) ⟨3464891, by rfl⟩ : syracuseStep 4619855 = 6929783) B6929783
theorem B3899387 : Blo 810345 3899387 := bstep (se 1 (by rfl) ⟨2924540, by rfl⟩ : syracuseStep 3899387 = 5849081) B5849081
theorem B1540271 : Blo 810345 1540271 := bstep (se 1 (by rfl) ⟨1155203, by rfl⟩ : syracuseStep 1540271 = 2310407) B2310407
theorem B4620563 : Blo 810345 4620563 := bstep (se 1 (by rfl) ⟨3465422, by rfl⟩ : syracuseStep 4620563 = 6930845) B6930845
theorem B4391657 : Blo 810345 4391657 := bstep (se 2 (by rfl) ⟨1646871, by rfl⟩ : syracuseStep 4391657 = 3293743) B3293743
theorem B11699083 : Blo 810345 11699083 := bstep (se 1 (by rfl) ⟨8774312, by rfl⟩ : syracuseStep 11699083 = 17548625) B17548625
theorem B1737811 : Blo 810345 1737811 := bstep (se 1 (by rfl) ⟨1303358, by rfl⟩ : syracuseStep 1737811 = 2606717) B2606717
theorem B1541531 : Blo 810345 1541531 := bstep (se 1 (by rfl) ⟨1156148, by rfl⟩ : syracuseStep 1541531 = 2312297) B2312297
theorem B10389707 : Blo 810345 10389707 := bstep (se 1 (by rfl) ⟨7792280, by rfl⟩ : syracuseStep 10389707 = 15584561) B15584561
theorem B66717989 : Blo 810345 66717989 := bstep (se 4 (by rfl) ⟨6254811, by rfl⟩ : syracuseStep 66717989 = 12509623) B12509623
theorem B1215977 : Blo 810345 1215977 := bstep (se 2 (by rfl) ⟨455991, by rfl⟩ : syracuseStep 1215977 = 911983) B911983
theorem B1216031 : Blo 810345 1216031 := bstep (se 1 (by rfl) ⟨912023, by rfl⟩ : syracuseStep 1216031 = 1824047) B1824047
theorem B20024891 : Blo 810345 20024891 := bstep (se 1 (by rfl) ⟨15018668, by rfl⟩ : syracuseStep 20024891 = 30037337) B30037337
theorem B1216127 : Blo 810345 1216127 := bstep (se 1 (by rfl) ⟨912095, by rfl⟩ : syracuseStep 1216127 = 1824191) B1824191
theorem B1544015 : Blo 810345 1544015 := bstep (se 1 (by rfl) ⟨1158011, by rfl⟩ : syracuseStep 1544015 = 2316023) B2316023
theorem B37523681 : Blo 810345 37523681 := bstep (se 2 (by rfl) ⟨14071380, by rfl⟩ : syracuseStep 37523681 = 28142761) B28142761
theorem B3084551 : Blo 810345 3084551 := bstep (se 1 (by rfl) ⟨2313413, by rfl⟩ : syracuseStep 3084551 = 4626827) B4626827
theorem B37491173 : Blo 810345 37491173 := bstep (se 4 (by rfl) ⟨3514797, by rfl⟩ : syracuseStep 37491173 = 7029595) B7029595
theorem B2920967 : Blo 810345 2920967 := bstep (se 1 (by rfl) ⟨2190725, by rfl⟩ : syracuseStep 2920967 = 4381451) B4381451
theorem B1217051 : Blo 810345 1217051 := bstep (se 1 (by rfl) ⟨912788, by rfl⟩ : syracuseStep 1217051 = 1825577) B1825577
theorem B1217351 : Blo 810345 1217351 := bstep (se 1 (by rfl) ⟨913013, by rfl⟩ : syracuseStep 1217351 = 1826027) B1826027
theorem B1217417 : Blo 810345 1217417 := bstep (se 2 (by rfl) ⟨456531, by rfl⟩ : syracuseStep 1217417 = 913063) B913063
theorem B3904463 : Blo 810345 3904463 := bstep (se 1 (by rfl) ⟨2928347, by rfl⟩ : syracuseStep 3904463 = 5856695) B5856695
theorem B1217513 : Blo 810345 1217513 := bstep (se 2 (by rfl) ⟨456567, by rfl⟩ : syracuseStep 1217513 = 913135) B913135
theorem B29594621 : Blo 810345 29594621 := bstep (se 3 (by rfl) ⟨5548991, by rfl⟩ : syracuseStep 29594621 = 11097983) B11097983
theorem B1217567 : Blo 810345 1217567 := bstep (se 1 (by rfl) ⟨913175, by rfl⟩ : syracuseStep 1217567 = 1826351) B1826351
theorem B1217759 : Blo 810345 1217759 := bstep (se 1 (by rfl) ⟨913319, by rfl⟩ : syracuseStep 1217759 = 1826639) B1826639
theorem B49911167 : Blo 810345 49911167 := bstep (se 1 (by rfl) ⟨37433375, by rfl⟩ : syracuseStep 49911167 = 74866751) B74866751
theorem B1218239 : Blo 810345 1218239 := bstep (se 1 (by rfl) ⟨913679, by rfl⟩ : syracuseStep 1218239 = 1827359) B1827359
theorem B1218431 : Blo 810345 1218431 := bstep (se 1 (by rfl) ⟨913823, by rfl⟩ : syracuseStep 1218431 = 1827647) B1827647
theorem B1218791 : Blo 810345 1218791 := bstep (se 1 (by rfl) ⟨914093, by rfl⟩ : syracuseStep 1218791 = 1828187) B1828187
theorem B1220639 : Blo 810345 1220639 := bstep (se 1 (by rfl) ⟨915479, by rfl⟩ : syracuseStep 1220639 = 1830959) B1830959
theorem B3712159 : Blo 810345 3712159 := bstep (se 1 (by rfl) ⟨2784119, by rfl⟩ : syracuseStep 3712159 = 5568239) B5568239
theorem B2598311 : Blo 810345 2598311 := bstep (se 1 (by rfl) ⟨1948733, by rfl⟩ : syracuseStep 2598311 = 3897467) B3897467
theorem B3089897 : Blo 810345 3089897 := bstep (se 2 (by rfl) ⟨1158711, by rfl⟩ : syracuseStep 3089897 = 2317423) B2317423
theorem B10398365 : Blo 810345 10398365 := bstep (se 3 (by rfl) ⟨1949693, by rfl⟩ : syracuseStep 10398365 = 3899387) B3899387
theorem B12528593 : Blo 810345 12528593 := bstep (se 2 (by rfl) ⟨4698222, by rfl⟩ : syracuseStep 12528593 = 9396445) B9396445
theorem B3091567 : Blo 810345 3091567 := bstep (se 1 (by rfl) ⟨2318675, by rfl⟩ : syracuseStep 3091567 = 4637351) B4637351
theorem B2927801 : Blo 810345 2927801 := bstep (se 2 (by rfl) ⟨1097925, by rfl⟩ : syracuseStep 2927801 = 2195851) B2195851
theorem B4402363 : Blo 810345 4402363 := bstep (se 1 (by rfl) ⟨3301772, by rfl⟩ : syracuseStep 4402363 = 6603545) B6603545
theorem B2469431 : Blo 810345 2469431 := bstep (se 1 (by rfl) ⟨1852073, by rfl⟩ : syracuseStep 2469431 = 3704147) B3704147
theorem B6238183 : Blo 810345 6238183 := bstep (se 1 (by rfl) ⟨4678637, by rfl⟩ : syracuseStep 6238183 = 9357275) B9357275
theorem B385626419 : Blo 810345 385626419 := bstep (se 1 (by rfl) ⟨289219814, by rfl⟩ : syracuseStep 385626419 = 578439629) B578439629
theorem B40155689 : Blo 810345 40155689 := bstep (se 2 (by rfl) ⟨15058383, by rfl⟩ : syracuseStep 40155689 = 30116767) B30116767
theorem B25017761 : Blo 810345 25017761 := bstep (se 2 (by rfl) ⟨9381660, by rfl⟩ : syracuseStep 25017761 = 18763321) B18763321
theorem B5193341 : Blo 810345 5193341 := bstep (se 3 (by rfl) ⟨973751, by rfl⟩ : syracuseStep 5193341 = 1947503) B1947503
theorem B2473703 : Blo 810345 2473703 := bstep (se 1 (by rfl) ⟨1855277, by rfl⟩ : syracuseStep 2473703 = 3710555) B3710555
theorem B2310191 : Blo 810345 2310191 := bstep (se 1 (by rfl) ⟨1732643, by rfl⟩ : syracuseStep 2310191 = 3465287) B3465287
theorem B49922239 : Blo 810345 49922239 := bstep (se 1 (by rfl) ⟨37441679, by rfl⟩ : syracuseStep 49922239 = 74883359) B74883359
theorem B25085861 : Blo 810345 25085861 := bstep (se 4 (by rfl) ⟨2351799, by rfl⟩ : syracuseStep 25085861 = 4703599) B4703599
theorem B6179003 : Blo 810345 6179003 := bstep (se 1 (by rfl) ⟨4634252, by rfl⟩ : syracuseStep 6179003 = 9268505) B9268505
theorem B1462207 : Blo 810345 1462207 := bstep (se 1 (by rfl) ⟨1096655, by rfl⟩ : syracuseStep 1462207 = 2193311) B2193311
theorem B1298425 : Blo 810345 1298425 := bstep (se 2 (by rfl) ⟨486909, by rfl⟩ : syracuseStep 1298425 = 973819) B973819
theorem B8769779 : Blo 810345 8769779 := bstep (se 1 (by rfl) ⟨6577334, by rfl⟩ : syracuseStep 8769779 = 13154669) B13154669
theorem B5198363 : Blo 810345 5198363 := bstep (se 1 (by rfl) ⟨3898772, by rfl⟩ : syracuseStep 5198363 = 7797545) B7797545
theorem B1823687 : Blo 810345 1823687 := bstep (se 1 (by rfl) ⟨1367765, by rfl⟩ : syracuseStep 1823687 = 2735531) B2735531
theorem B6181919 : Blo 810345 6181919 := bstep (se 1 (by rfl) ⟨4636439, by rfl⟩ : syracuseStep 6181919 = 9272879) B9272879
theorem B2577871 : Blo 810345 2577871 := bstep (se 1 (by rfl) ⟨1933403, by rfl⟩ : syracuseStep 2577871 = 3866807) B3866807
theorem B2741903 : Blo 810345 2741903 := bstep (se 1 (by rfl) ⟨2056427, by rfl⟩ : syracuseStep 2741903 = 4112855) B4112855
theorem B26367839 : Blo 810345 26367839 := bstep (se 1 (by rfl) ⟨19775879, by rfl⟩ : syracuseStep 26367839 = 39551759) B39551759
theorem B1300457 : Blo 810345 1300457 := bstep (se 2 (by rfl) ⟨487671, by rfl⟩ : syracuseStep 1300457 = 975343) B975343
theorem B4118525 : Blo 810345 4118525 := bstep (se 3 (by rfl) ⟨772223, by rfl⟩ : syracuseStep 4118525 = 1544447) B1544447
theorem B2742875 : Blo 810345 2742875 := bstep (se 1 (by rfl) ⟨2057156, by rfl⟩ : syracuseStep 2742875 = 4114313) B4114313
theorem B1464923 : Blo 810345 1464923 := bstep (se 1 (by rfl) ⟨1098692, by rfl⟩ : syracuseStep 1464923 = 2197385) B2197385
theorem B1826207 : Blo 810345 1826207 := bstep (se 1 (by rfl) ⟨1369655, by rfl⟩ : syracuseStep 1826207 = 2739311) B2739311
theorem B2055851 : Blo 810345 2055851 := bstep (se 1 (by rfl) ⟨1541888, by rfl⟩ : syracuseStep 2055851 = 3083777) B3083777
theorem B9232055 : Blo 810345 9232055 := bstep (se 1 (by rfl) ⟨6924041, by rfl⟩ : syracuseStep 9232055 = 13848083) B13848083
theorem B810843 : Blo 810345 810843 := bstep (se 1 (by rfl) ⟨608132, by rfl⟩ : syracuseStep 810843 = 1216265) B1216265
theorem B810879 : Blo 810345 810879 := bstep (se 1 (by rfl) ⟨608159, by rfl⟩ : syracuseStep 810879 = 1216319) B1216319
theorem B25026515 : Blo 810345 25026515 := bstep (se 1 (by rfl) ⟨18769886, by rfl⟩ : syracuseStep 25026515 = 37539773) B37539773
theorem B2744279 : Blo 810345 2744279 := bstep (se 1 (by rfl) ⟨2058209, by rfl⟩ : syracuseStep 2744279 = 4116419) B4116419
theorem B2318311 : Blo 810345 2318311 := bstep (se 1 (by rfl) ⟨1738733, by rfl⟩ : syracuseStep 2318311 = 3477467) B3477467
theorem B811039 : Blo 810345 811039 := bstep (se 1 (by rfl) ⟨608279, by rfl⟩ : syracuseStep 811039 = 1216559) B1216559
theorem B1368137 : Blo 810345 1368137 := bstep (se 2 (by rfl) ⟨513051, by rfl⟩ : syracuseStep 1368137 = 1026103) B1026103
theorem B811487 : Blo 810345 811487 := bstep (se 1 (by rfl) ⟨608615, by rfl⟩ : syracuseStep 811487 = 1217231) B1217231
theorem B14083303 : Blo 810345 14083303 := bstep (se 1 (by rfl) ⟨10562477, by rfl⟩ : syracuseStep 14083303 = 21124955) B21124955
theorem B2057683 : Blo 810345 2057683 := bstep (se 1 (by rfl) ⟨1543262, by rfl⟩ : syracuseStep 2057683 = 3086525) B3086525
theorem B812647 : Blo 810345 812647 := bstep (se 1 (by rfl) ⟨609485, by rfl⟩ : syracuseStep 812647 = 1218971) B1218971
theorem B1369831 : Blo 810345 1369831 := bstep (se 1 (by rfl) ⟨1027373, by rfl⟩ : syracuseStep 1369831 = 2054747) B2054747
theorem B1369865 : Blo 810345 1369865 := bstep (se 2 (by rfl) ⟨513699, by rfl⟩ : syracuseStep 1369865 = 1027399) B1027399
theorem B6252349 : Blo 810345 6252349 := bstep (se 3 (by rfl) ⟨1172315, by rfl⟩ : syracuseStep 6252349 = 2344631) B2344631
theorem B1828691 : Blo 810345 1828691 := bstep (se 1 (by rfl) ⟨1371518, by rfl⟩ : syracuseStep 1828691 = 2743037) B2743037
theorem B10413947 : Blo 810345 10413947 := bstep (se 1 (by rfl) ⟨7810460, by rfl⟩ : syracuseStep 10413947 = 15620921) B15620921
theorem B813223 : Blo 810345 813223 := bstep (se 1 (by rfl) ⟨609917, by rfl⟩ : syracuseStep 813223 = 1219835) B1219835
theorem B6580547 : Blo 810345 6580547 := bstep (se 1 (by rfl) ⟨4935410, by rfl⟩ : syracuseStep 6580547 = 9870821) B9870821
theorem B813383 : Blo 810345 813383 := bstep (se 1 (by rfl) ⟨610037, by rfl⟩ : syracuseStep 813383 = 1220075) B1220075
theorem B2058655 : Blo 810345 2058655 := bstep (se 1 (by rfl) ⟨1543991, by rfl⟩ : syracuseStep 2058655 = 3087983) B3087983
theorem B5204695 : Blo 810345 5204695 := bstep (se 1 (by rfl) ⟨3903521, by rfl⟩ : syracuseStep 5204695 = 7807043) B7807043
theorem B17558315 : Blo 810345 17558315 := bstep (se 1 (by rfl) ⟨13168736, by rfl⟩ : syracuseStep 17558315 = 26337473) B26337473
theorem B1829735 : Blo 810345 1829735 := bstep (se 1 (by rfl) ⟨1372301, by rfl⟩ : syracuseStep 1829735 = 2744603) B2744603
theorem B2747303 : Blo 810345 2747303 := bstep (se 1 (by rfl) ⟨2060477, by rfl⟩ : syracuseStep 2747303 = 4120955) B4120955
theorem B1829843 : Blo 810345 1829843 := bstep (se 1 (by rfl) ⟨1372382, by rfl⟩ : syracuseStep 1829843 = 2744765) B2744765
theorem B1829951 : Blo 810345 1829951 := bstep (se 1 (by rfl) ⟨1372463, by rfl⟩ : syracuseStep 1829951 = 2744927) B2744927
theorem B814235 : Blo 810345 814235 := bstep (se 1 (by rfl) ⟨610676, by rfl⟩ : syracuseStep 814235 = 1221353) B1221353
theorem B814247 : Blo 810345 814247 := bstep (se 1 (by rfl) ⟨610685, by rfl⟩ : syracuseStep 814247 = 1221371) B1221371
theorem B1371323 : Blo 810345 1371323 := bstep (se 1 (by rfl) ⟨1028492, by rfl⟩ : syracuseStep 1371323 = 2056985) B2056985
theorem B11693321 : Blo 810345 11693321 := bstep (se 2 (by rfl) ⟨4384995, by rfl⟩ : syracuseStep 11693321 = 8769991) B8769991
theorem B4615481 : Blo 810345 4615481 := bstep (se 2 (by rfl) ⟨1730805, by rfl⟩ : syracuseStep 4615481 = 3461611) B3461611
theorem B2059577 : Blo 810345 2059577 := bstep (se 2 (by rfl) ⟨772341, by rfl⟩ : syracuseStep 2059577 = 1544683) B1544683
theorem B342617525 : Blo 810345 342617525 := bstep (se 5 (by rfl) ⟨16060196, by rfl⟩ : syracuseStep 342617525 = 32120393) B32120393
theorem B5336549 : Blo 810345 5336549 := bstep (se 4 (by rfl) ⟨500301, by rfl⟩ : syracuseStep 5336549 = 1000603) B1000603
theorem B1830419 : Blo 810345 1830419 := bstep (se 1 (by rfl) ⟨1372814, by rfl⟩ : syracuseStep 1830419 = 2745629) B2745629
theorem B2748329 : Blo 810345 2748329 := bstep (se 2 (by rfl) ⟨1030623, by rfl⟩ : syracuseStep 2748329 = 2061247) B2061247
theorem B1372187 : Blo 810345 1372187 := bstep (se 1 (by rfl) ⟨1029140, by rfl⟩ : syracuseStep 1372187 = 2058281) B2058281
theorem B6582683 : Blo 810345 6582683 := bstep (se 1 (by rfl) ⟨4937012, by rfl⟩ : syracuseStep 6582683 = 9874025) B9874025
theorem B1372639 : Blo 810345 1372639 := bstep (se 1 (by rfl) ⟨1029479, by rfl⟩ : syracuseStep 1372639 = 2058959) B2058959
theorem B4616939 : Blo 810345 4616939 := bstep (se 1 (by rfl) ⟨3462704, by rfl⟩ : syracuseStep 4616939 = 6925409) B6925409
theorem B7796087 : Blo 810345 7796087 := bstep (se 1 (by rfl) ⟨5847065, by rfl⟩ : syracuseStep 7796087 = 11694131) B11694131
theorem B4945529 : Blo 810345 4945529 := bstep (se 2 (by rfl) ⟨1854573, by rfl⟩ : syracuseStep 4945529 = 3709147) B3709147
theorem B6158105 : Blo 810345 6158105 := bstep (se 2 (by rfl) ⟨2309289, by rfl⟩ : syracuseStep 6158105 = 4618579) B4618579
theorem B915583 : Blo 810345 915583 := bstep (se 1 (by rfl) ⟨686687, by rfl⟩ : syracuseStep 915583 = 1373375) B1373375
theorem B5863843 : Blo 810345 5863843 := bstep (se 1 (by rfl) ⟨4397882, by rfl⟩ : syracuseStep 5863843 = 8795765) B8795765
theorem B4619105 : Blo 810345 4619105 := bstep (se 2 (by rfl) ⟨1732164, by rfl⟩ : syracuseStep 4619105 = 3464329) B3464329
theorem B3079903 : Blo 810345 3079903 := bstep (se 1 (by rfl) ⟨2309927, by rfl⟩ : syracuseStep 3079903 = 4619855) B4619855
theorem B1540073 : Blo 810345 1540073 := bstep (se 2 (by rfl) ⟨577527, by rfl⟩ : syracuseStep 1540073 = 1155055) B1155055
theorem B1540127 : Blo 810345 1540127 := bstep (se 1 (by rfl) ⟨1155095, by rfl⟩ : syracuseStep 1540127 = 2310191) B2310191
theorem B3080375 : Blo 810345 3080375 := bstep (se 1 (by rfl) ⟨2310281, by rfl⟩ : syracuseStep 3080375 = 4620563) B4620563
theorem B15598777 : Blo 810345 15598777 := bstep (se 2 (by rfl) ⟨5849541, by rfl⟩ : syracuseStep 15598777 = 11699083) B11699083
theorem B18777737 : Blo 810345 18777737 := bstep (se 2 (by rfl) ⟨7041651, by rfl⟩ : syracuseStep 18777737 = 14083303) B14083303
theorem B1215791 : Blo 810345 1215791 := bstep (se 1 (by rfl) ⟨911843, by rfl⟩ : syracuseStep 1215791 = 1823687) B1823687
theorem B19729747 : Blo 810345 19729747 := bstep (se 1 (by rfl) ⟨14797310, by rfl⟩ : syracuseStep 19729747 = 29594621) B29594621
theorem B5869817 : Blo 810345 5869817 := bstep (se 2 (by rfl) ⟨2201181, by rfl⟩ : syracuseStep 5869817 = 4402363) B4402363
theorem B1217471 : Blo 810345 1217471 := bstep (se 1 (by rfl) ⟨913103, by rfl⟩ : syracuseStep 1217471 = 1826207) B1826207
theorem B16684343 : Blo 810345 16684343 := bstep (se 1 (by rfl) ⟨12513257, by rfl⟩ : syracuseStep 16684343 = 25026515) B25026515
theorem B19798181 : Blo 810345 19798181 := bstep (se 4 (by rfl) ⟨1856079, by rfl⟩ : syracuseStep 19798181 = 3712159) B3712159
theorem B1219127 : Blo 810345 1219127 := bstep (se 1 (by rfl) ⟨914345, by rfl⟩ : syracuseStep 1219127 = 1828691) B1828691
theorem B3906461 : Blo 810345 3906461 := bstep (se 3 (by rfl) ⟨732461, by rfl⟩ : syracuseStep 3906461 = 1464923) B1464923
theorem B11705543 : Blo 810345 11705543 := bstep (se 1 (by rfl) ⟨8779157, by rfl⟩ : syracuseStep 11705543 = 17558315) B17558315
theorem B1219823 : Blo 810345 1219823 := bstep (se 1 (by rfl) ⟨914867, by rfl⟩ : syracuseStep 1219823 = 1829735) B1829735
theorem B1219895 : Blo 810345 1219895 := bstep (se 1 (by rfl) ⟨914921, by rfl⟩ : syracuseStep 1219895 = 1829843) B1829843
theorem B1219967 : Blo 810345 1219967 := bstep (se 1 (by rfl) ⟨914975, by rfl⟩ : syracuseStep 1219967 = 1829951) B1829951
theorem B1220279 : Blo 810345 1220279 := bstep (se 1 (by rfl) ⟨915209, by rfl⟩ : syracuseStep 1220279 = 1830419) B1830419
theorem B1646287 : Blo 810345 1646287 := bstep (se 1 (by rfl) ⟨1234715, by rfl⟩ : syracuseStep 1646287 = 2469431) B2469431
theorem B1220777 : Blo 810345 1220777 := bstep (se 2 (by rfl) ⟨457791, by rfl⟩ : syracuseStep 1220777 = 915583) B915583
theorem B4105403 : Blo 810345 4105403 := bstep (se 1 (by rfl) ⟨3079052, by rfl⟩ : syracuseStep 4105403 = 6158105) B6158105
theorem B4106537 : Blo 810345 4106537 := bstep (se 2 (by rfl) ⟨1539951, by rfl⟩ : syracuseStep 4106537 = 3079903) B3079903
theorem B1649135 : Blo 810345 1649135 := bstep (se 1 (by rfl) ⟨1236851, by rfl⟩ : syracuseStep 1649135 = 2473703) B2473703
theorem B4106861 : Blo 810345 4106861 := bstep (se 3 (by rfl) ⟨770036, by rfl⟩ : syracuseStep 4106861 = 1540073) B1540073
theorem B3091081 : Blo 810345 3091081 := bstep (se 2 (by rfl) ⟨1159155, by rfl⟩ : syracuseStep 3091081 = 2318311) B2318311
theorem B1026847 : Blo 810345 1026847 := bstep (se 1 (by rfl) ⟨770135, by rfl⟩ : syracuseStep 1026847 = 1540271) B1540271
theorem B66562985 : Blo 810345 66562985 := bstep (se 2 (by rfl) ⟨24961119, by rfl⟩ : syracuseStep 66562985 = 49922239) B49922239
theorem B2927771 : Blo 810345 2927771 := bstep (se 1 (by rfl) ⟨2195828, by rfl⟩ : syracuseStep 2927771 = 4391657) B4391657
theorem B16723907 : Blo 810345 16723907 := bstep (se 1 (by rfl) ⟨12542930, by rfl⟩ : syracuseStep 16723907 = 25085861) B25085861
theorem B6926471 : Blo 810345 6926471 := bstep (se 1 (by rfl) ⟨5194853, by rfl⟩ : syracuseStep 6926471 = 10389707) B10389707
theorem B44478659 : Blo 810345 44478659 := bstep (se 1 (by rfl) ⟨33358994, by rfl⟩ : syracuseStep 44478659 = 66717989) B66717989
theorem B13349927 : Blo 810345 13349927 := bstep (se 1 (by rfl) ⟨10012445, by rfl⟩ : syracuseStep 13349927 = 20024891) B20024891
theorem B8336465 : Blo 810345 8336465 := bstep (se 2 (by rfl) ⟨3126174, by rfl⟩ : syracuseStep 8336465 = 6252349) B6252349
theorem B1029343 : Blo 810345 1029343 := bstep (se 1 (by rfl) ⟨772007, by rfl⟩ : syracuseStep 1029343 = 1544015) B1544015
theorem B25015787 : Blo 810345 25015787 := bstep (se 1 (by rfl) ⟨18761840, by rfl⟩ : syracuseStep 25015787 = 37523681) B37523681
theorem B5846519 : Blo 810345 5846519 := bstep (se 1 (by rfl) ⟨4384889, by rfl⟩ : syracuseStep 5846519 = 8769779) B8769779
theorem B1947311 : Blo 810345 1947311 := bstep (se 1 (by rfl) ⟨1460483, by rfl⟩ : syracuseStep 1947311 = 2920967) B2920967
theorem B2602975 : Blo 810345 2602975 := bstep (se 1 (by rfl) ⟨1952231, by rfl⟩ : syracuseStep 2602975 = 3904463) B3904463
theorem B33274111 : Blo 810345 33274111 := bstep (se 1 (by rfl) ⟨24955583, by rfl⟩ : syracuseStep 33274111 = 49911167) B49911167
theorem B4110749 : Blo 810345 4110749 := bstep (se 3 (by rfl) ⟨770765, by rfl⟩ : syracuseStep 4110749 = 1541531) B1541531
theorem B17578559 : Blo 810345 17578559 := bstep (se 1 (by rfl) ⟨13183919, by rfl⟩ : syracuseStep 17578559 = 26367839) B26367839
theorem B866971 : Blo 810345 866971 := bstep (se 1 (by rfl) ⟨650228, by rfl⟩ : syracuseStep 866971 = 1300457) B1300457
theorem B1949609 : Blo 810345 1949609 := bstep (se 2 (by rfl) ⟨731103, by rfl⟩ : syracuseStep 1949609 = 1462207) B1462207
theorem B6932243 : Blo 810345 6932243 := bstep (se 1 (by rfl) ⟨5199182, by rfl⟩ : syracuseStep 6932243 = 10398365) B10398365
theorem B1951867 : Blo 810345 1951867 := bstep (se 1 (by rfl) ⟨1463900, by rfl⟩ : syracuseStep 1951867 = 2927801) B2927801
theorem B228411683 : Blo 810345 228411683 := bstep (se 1 (by rfl) ⟨171308762, by rfl⟩ : syracuseStep 228411683 = 342617525) B342617525
theorem B3557699 : Blo 810345 3557699 := bstep (se 1 (by rfl) ⟨2668274, by rfl⟩ : syracuseStep 3557699 = 5336549) B5336549
theorem B257084279 : Blo 810345 257084279 := bstep (se 1 (by rfl) ⟨192813209, by rfl⟩ : syracuseStep 257084279 = 385626419) B385626419
theorem B7818457 : Blo 810345 7818457 := bstep (se 2 (by rfl) ⟨2931921, by rfl⟩ : syracuseStep 7818457 = 5863843) B5863843
theorem B5197391 : Blo 810345 5197391 := bstep (se 1 (by rfl) ⟨3898043, by rfl⟩ : syracuseStep 5197391 = 7796087) B7796087
theorem B3297019 : Blo 810345 3297019 := bstep (se 1 (by rfl) ⟨2472764, by rfl⟩ : syracuseStep 3297019 = 4945529) B4945529
theorem B3462227 : Blo 810345 3462227 := bstep (se 1 (by rfl) ⟨2596670, by rfl⟩ : syracuseStep 3462227 = 5193341) B5193341
theorem B2317081 : Blo 810345 2317081 := bstep (se 2 (by rfl) ⟨868905, by rfl⟩ : syracuseStep 2317081 = 1737811) B1737811
theorem B4119335 : Blo 810345 4119335 := bstep (se 1 (by rfl) ⟨3089501, by rfl⟩ : syracuseStep 4119335 = 6179003) B6179003
theorem B2743577 : Blo 810345 2743577 := bstep (se 2 (by rfl) ⟨1028841, by rfl⟩ : syracuseStep 2743577 = 2057683) B2057683
theorem B1826441 : Blo 810345 1826441 := bstep (se 2 (by rfl) ⟨684915, by rfl⟩ : syracuseStep 1826441 = 1369831) B1369831
theorem B810651 : Blo 810345 810651 := bstep (se 1 (by rfl) ⟨607988, by rfl⟩ : syracuseStep 810651 = 1215977) B1215977
theorem B810687 : Blo 810345 810687 := bstep (se 1 (by rfl) ⟨608015, by rfl⟩ : syracuseStep 810687 = 1216031) B1216031
theorem B810751 : Blo 810345 810751 := bstep (se 1 (by rfl) ⟨608063, by rfl⟩ : syracuseStep 810751 = 1216127) B1216127
theorem B2056367 : Blo 810345 2056367 := bstep (se 1 (by rfl) ⟨1542275, by rfl⟩ : syracuseStep 2056367 = 3084551) B3084551
theorem B24994115 : Blo 810345 24994115 := bstep (se 1 (by rfl) ⟨18745586, by rfl⟩ : syracuseStep 24994115 = 37491173) B37491173
theorem B3465575 : Blo 810345 3465575 := bstep (se 1 (by rfl) ⟨2599181, by rfl⟩ : syracuseStep 3465575 = 5198363) B5198363
theorem B811367 : Blo 810345 811367 := bstep (se 1 (by rfl) ⟨608525, by rfl⟩ : syracuseStep 811367 = 1217051) B1217051
theorem B2744873 : Blo 810345 2744873 := bstep (se 2 (by rfl) ⟨1029327, by rfl⟩ : syracuseStep 2744873 = 2058655) B2058655
theorem B811567 : Blo 810345 811567 := bstep (se 1 (by rfl) ⟨608675, by rfl⟩ : syracuseStep 811567 = 1217351) B1217351
theorem B811611 : Blo 810345 811611 := bstep (se 1 (by rfl) ⟨608708, by rfl⟩ : syracuseStep 811611 = 1217417) B1217417
theorem B811675 : Blo 810345 811675 := bstep (se 1 (by rfl) ⟨608756, by rfl⟩ : syracuseStep 811675 = 1217513) B1217513
theorem B811711 : Blo 810345 811711 := bstep (se 1 (by rfl) ⟨608783, by rfl⟩ : syracuseStep 811711 = 1217567) B1217567
theorem B4121279 : Blo 810345 4121279 := bstep (se 1 (by rfl) ⟨3090959, by rfl⟩ : syracuseStep 4121279 = 6181919) B6181919
theorem B811839 : Blo 810345 811839 := bstep (se 1 (by rfl) ⟨608879, by rfl⟩ : syracuseStep 811839 = 1217759) B1217759
theorem B6939593 : Blo 810345 6939593 := bstep (se 2 (by rfl) ⟨2602347, by rfl⟩ : syracuseStep 6939593 = 5204695) B5204695
theorem B1827935 : Blo 810345 1827935 := bstep (se 1 (by rfl) ⟨1370951, by rfl⟩ : syracuseStep 1827935 = 2741903) B2741903
theorem B812159 : Blo 810345 812159 := bstep (se 1 (by rfl) ⟨609119, by rfl⟩ : syracuseStep 812159 = 1218239) B1218239
theorem B812287 : Blo 810345 812287 := bstep (se 1 (by rfl) ⟨609215, by rfl⟩ : syracuseStep 812287 = 1218431) B1218431
theorem B2745683 : Blo 810345 2745683 := bstep (se 1 (by rfl) ⟨2059262, by rfl⟩ : syracuseStep 2745683 = 4118525) B4118525
theorem B4122089 : Blo 810345 4122089 := bstep (se 2 (by rfl) ⟨1545783, by rfl⟩ : syracuseStep 4122089 = 3091567) B3091567
theorem B812527 : Blo 810345 812527 := bstep (se 1 (by rfl) ⟨609395, by rfl⟩ : syracuseStep 812527 = 1218791) B1218791
theorem B1828583 : Blo 810345 1828583 := bstep (se 1 (by rfl) ⟨1371437, by rfl⟩ : syracuseStep 1828583 = 2742875) B2742875
theorem B1370567 : Blo 810345 1370567 := bstep (se 1 (by rfl) ⟨1027925, by rfl⟩ : syracuseStep 1370567 = 2055851) B2055851
theorem B6154703 : Blo 810345 6154703 := bstep (se 1 (by rfl) ⟨4616027, by rfl⟩ : syracuseStep 6154703 = 9232055) B9232055
theorem B8317577 : Blo 810345 8317577 := bstep (se 2 (by rfl) ⟨3119091, by rfl⟩ : syracuseStep 8317577 = 6238183) B6238183
theorem B1829519 : Blo 810345 1829519 := bstep (se 1 (by rfl) ⟨1372139, by rfl⟩ : syracuseStep 1829519 = 2744279) B2744279
theorem B1731233 : Blo 810345 1731233 := bstep (se 2 (by rfl) ⟨649212, by rfl⟩ : syracuseStep 1731233 = 1298425) B1298425
theorem B813759 : Blo 810345 813759 := bstep (se 1 (by rfl) ⟨610319, by rfl⟩ : syracuseStep 813759 = 1220639) B1220639
theorem B912091 : Blo 810345 912091 := bstep (se 1 (by rfl) ⟨684068, by rfl⟩ : syracuseStep 912091 = 1368137) B1368137
theorem B1830185 : Blo 810345 1830185 := bstep (se 2 (by rfl) ⟨686319, by rfl⟩ : syracuseStep 1830185 = 1372639) B1372639
theorem B1732207 : Blo 810345 1732207 := bstep (se 1 (by rfl) ⟨1299155, by rfl⟩ : syracuseStep 1732207 = 2598311) B2598311
theorem B2059931 : Blo 810345 2059931 := bstep (se 1 (by rfl) ⟨1544948, by rfl⟩ : syracuseStep 2059931 = 3089897) B3089897
theorem B913243 : Blo 810345 913243 := bstep (se 1 (by rfl) ⟨684932, by rfl⟩ : syracuseStep 913243 = 1369865) B1369865
theorem B6942631 : Blo 810345 6942631 := bstep (se 1 (by rfl) ⟨5206973, by rfl⟩ : syracuseStep 6942631 = 10413947) B10413947
theorem B4387031 : Blo 810345 4387031 := bstep (se 1 (by rfl) ⟨3290273, by rfl⟩ : syracuseStep 4387031 = 6580547) B6580547
theorem B3437161 : Blo 810345 3437161 := bstep (se 2 (by rfl) ⟨1288935, by rfl⟩ : syracuseStep 3437161 = 2577871) B2577871
theorem B1831535 : Blo 810345 1831535 := bstep (se 1 (by rfl) ⟨1373651, by rfl⟩ : syracuseStep 1831535 = 2747303) B2747303
theorem B8352395 : Blo 810345 8352395 := bstep (se 1 (by rfl) ⟨6264296, by rfl⟩ : syracuseStep 8352395 = 12528593) B12528593
theorem B914215 : Blo 810345 914215 := bstep (se 1 (by rfl) ⟨685661, by rfl⟩ : syracuseStep 914215 = 1371323) B1371323
theorem B7795547 : Blo 810345 7795547 := bstep (se 1 (by rfl) ⟨5846660, by rfl⟩ : syracuseStep 7795547 = 11693321) B11693321
theorem B3076987 : Blo 810345 3076987 := bstep (se 1 (by rfl) ⟨2307740, by rfl⟩ : syracuseStep 3076987 = 4615481) B4615481
theorem B1373051 : Blo 810345 1373051 := bstep (se 1 (by rfl) ⟨1029788, by rfl⟩ : syracuseStep 1373051 = 2059577) B2059577
theorem B1832219 : Blo 810345 1832219 := bstep (se 1 (by rfl) ⟨1374164, by rfl⟩ : syracuseStep 1832219 = 2748329) B2748329
theorem B914791 : Blo 810345 914791 := bstep (se 1 (by rfl) ⟨686093, by rfl⟩ : syracuseStep 914791 = 1372187) B1372187
theorem B4388455 : Blo 810345 4388455 := bstep (se 1 (by rfl) ⟨3291341, by rfl⟩ : syracuseStep 4388455 = 6582683) B6582683
theorem B3077959 : Blo 810345 3077959 := bstep (se 1 (by rfl) ⟨2308469, by rfl⟩ : syracuseStep 3077959 = 4616939) B4616939
theorem B26770459 : Blo 810345 26770459 := bstep (se 1 (by rfl) ⟨20077844, by rfl⟩ : syracuseStep 26770459 = 40155689) B40155689
theorem B3079403 : Blo 810345 3079403 := bstep (se 1 (by rfl) ⟨2309552, by rfl⟩ : syracuseStep 3079403 = 4619105) B4619105
theorem B16678507 : Blo 810345 16678507 := bstep (se 1 (by rfl) ⟨12508880, by rfl⟩ : syracuseStep 16678507 = 25017761) B25017761
theorem B12518491 : Blo 810345 12518491 := bstep (se 1 (by rfl) ⟨9388868, by rfl⟩ : syracuseStep 12518491 = 18777737) B18777737
theorem B4621495 : Blo 810345 4621495 := bstep (se 1 (by rfl) ⟨3466121, by rfl⟩ : syracuseStep 4621495 = 6932243) B6932243
theorem B152274455 : Blo 810345 152274455 := bstep (se 1 (by rfl) ⟨114205841, by rfl⟩ : syracuseStep 152274455 = 228411683) B228411683
theorem B1216121 : Blo 810345 1216121 := bstep (se 2 (by rfl) ⟨456045, by rfl⟩ : syracuseStep 1216121 = 912091) B912091
theorem B10424609 : Blo 810345 10424609 := bstep (se 2 (by rfl) ⟨3909228, by rfl⟩ : syracuseStep 10424609 = 7818457) B7818457
theorem B7803695 : Blo 810345 7803695 := bstep (se 1 (by rfl) ⟨5852771, by rfl⟩ : syracuseStep 7803695 = 11705543) B11705543
theorem B4396025 : Blo 810345 4396025 := bstep (se 2 (by rfl) ⟨1648509, by rfl⟩ : syracuseStep 4396025 = 3297019) B3297019
theorem B1217627 : Blo 810345 1217627 := bstep (se 1 (by rfl) ⟨913220, by rfl⟩ : syracuseStep 1217627 = 1826441) B1826441
theorem B1217657 : Blo 810345 1217657 := bstep (se 2 (by rfl) ⟨456621, by rfl⟩ : syracuseStep 1217657 = 913243) B913243
theorem B4626395 : Blo 810345 4626395 := bstep (se 1 (by rfl) ⟨3469796, by rfl⟩ : syracuseStep 4626395 = 6939593) B6939593
theorem B1218623 : Blo 810345 1218623 := bstep (se 1 (by rfl) ⟨913967, by rfl⟩ : syracuseStep 1218623 = 1827935) B1827935
theorem B1218953 : Blo 810345 1218953 := bstep (se 2 (by rfl) ⟨457107, by rfl⟩ : syracuseStep 1218953 = 914215) B914215
theorem B1219055 : Blo 810345 1219055 := bstep (se 1 (by rfl) ⟨914291, by rfl⟩ : syracuseStep 1219055 = 1828583) B1828583
theorem B4102649 : Blo 810345 4102649 := bstep (se 2 (by rfl) ⟨1538493, by rfl⟩ : syracuseStep 4102649 = 3076987) B3076987
theorem B4103135 : Blo 810345 4103135 := bstep (se 1 (by rfl) ⟨3077351, by rfl⟩ : syracuseStep 4103135 = 6154703) B6154703
theorem B1219679 : Blo 810345 1219679 := bstep (se 1 (by rfl) ⟨914759, by rfl⟩ : syracuseStep 1219679 = 1829519) B1829519
theorem B105225317 : Blo 810345 105225317 := bstep (se 4 (by rfl) ⟨9864873, by rfl⟩ : syracuseStep 105225317 = 19729747) B19729747
theorem B1219721 : Blo 810345 1219721 := bstep (se 2 (by rfl) ⟨457395, by rfl⟩ : syracuseStep 1219721 = 914791) B914791
theorem B44375323 : Blo 810345 44375323 := bstep (se 1 (by rfl) ⟨33281492, by rfl⟩ : syracuseStep 44375323 = 66562985) B66562985
theorem B1220123 : Blo 810345 1220123 := bstep (se 1 (by rfl) ⟨915092, by rfl⟩ : syracuseStep 1220123 = 1830185) B1830185
theorem B4103945 : Blo 810345 4103945 := bstep (se 2 (by rfl) ⟨1538979, by rfl⟩ : syracuseStep 4103945 = 3077959) B3077959
theorem B11149271 : Blo 810345 11149271 := bstep (se 1 (by rfl) ⟨8361953, by rfl⟩ : syracuseStep 11149271 = 16723907) B16723907
theorem B2924687 : Blo 810345 2924687 := bstep (se 1 (by rfl) ⟨2193515, by rfl⟩ : syracuseStep 2924687 = 4387031) B4387031
theorem B1221023 : Blo 810345 1221023 := bstep (se 1 (by rfl) ⟨915767, by rfl⟩ : syracuseStep 1221023 = 1831535) B1831535
theorem B1221479 : Blo 810345 1221479 := bstep (se 1 (by rfl) ⟨916109, by rfl⟩ : syracuseStep 1221479 = 1832219) B1832219
theorem B1155961 : Blo 810345 1155961 := bstep (se 2 (by rfl) ⟨433485, by rfl⟩ : syracuseStep 1155961 = 866971) B866971
theorem B3089441 : Blo 810345 3089441 := bstep (se 2 (by rfl) ⟨1158540, by rfl⟩ : syracuseStep 3089441 = 2317081) B2317081
theorem B35693945 : Blo 810345 35693945 := bstep (se 2 (by rfl) ⟨13385229, by rfl⟩ : syracuseStep 35693945 = 26770459) B26770459
theorem B1026751 : Blo 810345 1026751 := bstep (se 1 (by rfl) ⟨770063, by rfl⟩ : syracuseStep 1026751 = 1540127) B1540127
theorem B2371799 : Blo 810345 2371799 := bstep (se 1 (by rfl) ⟨1778849, by rfl⟩ : syracuseStep 2371799 = 3557699) B3557699
theorem B171389519 : Blo 810345 171389519 := bstep (se 1 (by rfl) ⟨128542139, by rfl⟩ : syracuseStep 171389519 = 257084279) B257084279
theorem B2602489 : Blo 810345 2602489 := bstep (se 2 (by rfl) ⟨975933, by rfl⟩ : syracuseStep 2602489 = 1951867) B1951867
theorem B3913211 : Blo 810345 3913211 := bstep (se 1 (by rfl) ⟨2934908, by rfl⟩ : syracuseStep 3913211 = 5869817) B5869817
theorem B18331525 : Blo 810345 18331525 := bstep (se 4 (by rfl) ⟨1718580, by rfl⟩ : syracuseStep 18331525 = 3437161) B3437161
theorem B2308151 : Blo 810345 2308151 := bstep (se 1 (by rfl) ⟨1731113, by rfl⟩ : syracuseStep 2308151 = 3462227) B3462227
theorem B11122895 : Blo 810345 11122895 := bstep (se 1 (by rfl) ⟨8342171, by rfl⟩ : syracuseStep 11122895 = 16684343) B16684343
theorem B2604307 : Blo 810345 2604307 := bstep (se 1 (by rfl) ⟨1953230, by rfl⟩ : syracuseStep 2604307 = 3906461) B3906461
theorem B2309609 : Blo 810345 2309609 := bstep (se 2 (by rfl) ⟨866103, by rfl⟩ : syracuseStep 2309609 = 1732207) B1732207
theorem B9256841 : Blo 810345 9256841 := bstep (se 2 (by rfl) ⟨3471315, by rfl⟩ : syracuseStep 9256841 = 6942631) B6942631
theorem B16662743 : Blo 810345 16662743 := bstep (se 1 (by rfl) ⟨12497057, by rfl⟩ : syracuseStep 16662743 = 24994115) B24994115
theorem B2310383 : Blo 810345 2310383 := bstep (se 1 (by rfl) ⟨1732787, by rfl⟩ : syracuseStep 2310383 = 3465575) B3465575
theorem B2736935 : Blo 810345 2736935 := bstep (se 1 (by rfl) ⟨2052701, by rfl⟩ : syracuseStep 2736935 = 4105403) B4105403
theorem B2737691 : Blo 810345 2737691 := bstep (se 1 (by rfl) ⟨2053268, by rfl⟩ : syracuseStep 2737691 = 4106537) B4106537
theorem B1099423 : Blo 810345 1099423 := bstep (se 1 (by rfl) ⟨824567, by rfl⟩ : syracuseStep 1099423 = 1649135) B1649135
theorem B2737907 : Blo 810345 2737907 := bstep (se 1 (by rfl) ⟨2053430, by rfl⟩ : syracuseStep 2737907 = 4106861) B4106861
theorem B1951847 : Blo 810345 1951847 := bstep (se 1 (by rfl) ⟨1463885, by rfl⟩ : syracuseStep 1951847 = 2927771) B2927771
theorem B5851273 : Blo 810345 5851273 := bstep (se 2 (by rfl) ⟨2194227, by rfl⟩ : syracuseStep 5851273 = 4388455) B4388455
theorem B5197031 : Blo 810345 5197031 := bstep (se 1 (by rfl) ⟨3897773, by rfl⟩ : syracuseStep 5197031 = 7795547) B7795547
theorem B8899951 : Blo 810345 8899951 := bstep (se 1 (by rfl) ⟨6674963, by rfl⟩ : syracuseStep 8899951 = 13349927) B13349927
theorem B5557643 : Blo 810345 5557643 := bstep (se 1 (by rfl) ⟨4168232, by rfl⟩ : syracuseStep 5557643 = 8336465) B8336465
theorem B1298207 : Blo 810345 1298207 := bstep (se 1 (by rfl) ⟨973655, by rfl⟩ : syracuseStep 1298207 = 1947311) B1947311
theorem B2740499 : Blo 810345 2740499 := bstep (se 1 (by rfl) ⟨2055374, by rfl⟩ : syracuseStep 2740499 = 4110749) B4110749
theorem B11719039 : Blo 810345 11719039 := bstep (se 1 (by rfl) ⟨8789279, by rfl⟩ : syracuseStep 11719039 = 17578559) B17578559
theorem B22238009 : Blo 810345 22238009 := bstep (se 2 (by rfl) ⟨8339253, by rfl⟩ : syracuseStep 22238009 = 16678507) B16678507
theorem B2052935 : Blo 810345 2052935 := bstep (se 1 (by rfl) ⟨1539701, by rfl⟩ : syracuseStep 2052935 = 3079403) B3079403
theorem B1299739 : Blo 810345 1299739 := bstep (se 1 (by rfl) ⟨974804, by rfl⟩ : syracuseStep 1299739 = 1949609) B1949609
theorem B2053583 : Blo 810345 2053583 := bstep (se 1 (by rfl) ⟨1540187, by rfl⟩ : syracuseStep 2053583 = 3080375) B3080375
theorem B20798369 : Blo 810345 20798369 := bstep (se 2 (by rfl) ⟨7799388, by rfl⟩ : syracuseStep 20798369 = 15598777) B15598777
theorem B810527 : Blo 810345 810527 := bstep (se 1 (by rfl) ⟨607895, by rfl⟩ : syracuseStep 810527 = 1215791) B1215791
theorem B3464927 : Blo 810345 3464927 := bstep (se 1 (by rfl) ⟨2598695, by rfl⟩ : syracuseStep 3464927 = 5197391) B5197391
theorem B811647 : Blo 810345 811647 := bstep (se 1 (by rfl) ⟨608735, by rfl⟩ : syracuseStep 811647 = 1217471) B1217471
theorem B4121441 : Blo 810345 4121441 := bstep (se 2 (by rfl) ⟨1545540, by rfl⟩ : syracuseStep 4121441 = 3091081) B3091081
theorem B1369129 : Blo 810345 1369129 := bstep (se 2 (by rfl) ⟨513423, by rfl⟩ : syracuseStep 1369129 = 1026847) B1026847
theorem B13198787 : Blo 810345 13198787 := bstep (se 1 (by rfl) ⟨9899090, by rfl⟩ : syracuseStep 13198787 = 19798181) B19798181
theorem B812751 : Blo 810345 812751 := bstep (se 1 (by rfl) ⟨609563, by rfl⟩ : syracuseStep 812751 = 1219127) B1219127
theorem B2746223 : Blo 810345 2746223 := bstep (se 1 (by rfl) ⟨2059667, by rfl⟩ : syracuseStep 2746223 = 4119335) B4119335
theorem B813215 : Blo 810345 813215 := bstep (se 1 (by rfl) ⟨609911, by rfl⟩ : syracuseStep 813215 = 1219823) B1219823
theorem B1829051 : Blo 810345 1829051 := bstep (se 1 (by rfl) ⟨1371788, by rfl⟩ : syracuseStep 1829051 = 2743577) B2743577
theorem B813263 : Blo 810345 813263 := bstep (se 1 (by rfl) ⟨609947, by rfl⟩ : syracuseStep 813263 = 1219895) B1219895
theorem B813311 : Blo 810345 813311 := bstep (se 1 (by rfl) ⟨609983, by rfl⟩ : syracuseStep 813311 = 1219967) B1219967
theorem B813519 : Blo 810345 813519 := bstep (se 1 (by rfl) ⟨610139, by rfl⟩ : syracuseStep 813519 = 1220279) B1220279
theorem B813851 : Blo 810345 813851 := bstep (se 1 (by rfl) ⟨610388, by rfl⟩ : syracuseStep 813851 = 1220777) B1220777
theorem B1370911 : Blo 810345 1370911 := bstep (se 1 (by rfl) ⟨1028183, by rfl⟩ : syracuseStep 1370911 = 2056367) B2056367
theorem B1829915 : Blo 810345 1829915 := bstep (se 1 (by rfl) ⟨1372436, by rfl⟩ : syracuseStep 1829915 = 2744873) B2744873
theorem B2747519 : Blo 810345 2747519 := bstep (se 1 (by rfl) ⟨2060639, by rfl⟩ : syracuseStep 2747519 = 4121279) B4121279
theorem B1830455 : Blo 810345 1830455 := bstep (se 1 (by rfl) ⟨1372841, by rfl⟩ : syracuseStep 1830455 = 2745683) B2745683
theorem B2748059 : Blo 810345 2748059 := bstep (se 1 (by rfl) ⟨2061044, by rfl⟩ : syracuseStep 2748059 = 4122089) B4122089
theorem B1372457 : Blo 810345 1372457 := bstep (se 2 (by rfl) ⟨514671, by rfl⟩ : syracuseStep 1372457 = 1029343) B1029343
theorem B913711 : Blo 810345 913711 := bstep (se 1 (by rfl) ⟨685283, by rfl⟩ : syracuseStep 913711 = 1370567) B1370567
theorem B22180205 : Blo 810345 22180205 := bstep (se 3 (by rfl) ⟨4158788, by rfl⟩ : syracuseStep 22180205 = 8317577) B8317577
theorem B4616621 : Blo 810345 4616621 := bstep (se 3 (by rfl) ⟨865616, by rfl⟩ : syracuseStep 4616621 = 1731233) B1731233
theorem B1373287 : Blo 810345 1373287 := bstep (se 1 (by rfl) ⟨1029965, by rfl⟩ : syracuseStep 1373287 = 2059931) B2059931
theorem B3470633 : Blo 810345 3470633 := bstep (se 2 (by rfl) ⟨1301487, by rfl⟩ : syracuseStep 3470633 = 2602975) B2602975
theorem B4617647 : Blo 810345 4617647 := bstep (se 1 (by rfl) ⟨3463235, by rfl⟩ : syracuseStep 4617647 = 6926471) B6926471
theorem B29652439 : Blo 810345 29652439 := bstep (se 1 (by rfl) ⟨22239329, by rfl⟩ : syracuseStep 29652439 = 44478659) B44478659
theorem B44365481 : Blo 810345 44365481 := bstep (se 2 (by rfl) ⟨16637055, by rfl⟩ : syracuseStep 44365481 = 33274111) B33274111
theorem B5568263 : Blo 810345 5568263 := bstep (se 1 (by rfl) ⟨4176197, by rfl⟩ : syracuseStep 5568263 = 8352395) B8352395
theorem B915367 : Blo 810345 915367 := bstep (se 1 (by rfl) ⟨686525, by rfl⟩ : syracuseStep 915367 = 1373051) B1373051
theorem B16677191 : Blo 810345 16677191 := bstep (se 1 (by rfl) ⟨12507893, by rfl⟩ : syracuseStep 16677191 = 25015787) B25015787
theorem B3897679 : Blo 810345 3897679 := bstep (se 1 (by rfl) ⟨2923259, by rfl⟩ : syracuseStep 3897679 = 5846519) B5846519
theorem B8780197 : Blo 810345 8780197 := bstep (se 4 (by rfl) ⟨823143, by rfl⟩ : syracuseStep 8780197 = 1646287) B1646287
theorem B11108495 : Blo 810345 11108495 := bstep (se 1 (by rfl) ⟨8331371, by rfl⟩ : syracuseStep 11108495 = 16662743) B16662743
theorem B6324797 : Blo 810345 6324797 := bstep (se 3 (by rfl) ⟨1185899, by rfl⟩ : syracuseStep 6324797 = 2371799) B2371799
theorem B6161021 : Blo 810345 6161021 := bstep (se 3 (by rfl) ⟨1155191, by rfl⟩ : syracuseStep 6161021 = 2310383) B2310383
theorem B101516303 : Blo 810345 101516303 := bstep (se 1 (by rfl) ⟨76137227, by rfl⟩ : syracuseStep 101516303 = 152274455) B152274455
theorem B1541281 : Blo 810345 1541281 := bstep (se 2 (by rfl) ⟨577980, by rfl⟩ : syracuseStep 1541281 = 1155961) B1155961
theorem B6161993 : Blo 810345 6161993 := bstep (se 2 (by rfl) ⟨2310747, by rfl⟩ : syracuseStep 6161993 = 4621495) B4621495
theorem B3705095 : Blo 810345 3705095 := bstep (se 1 (by rfl) ⟨2778821, by rfl⟩ : syracuseStep 3705095 = 5557643) B5557643
theorem B7801697 : Blo 810345 7801697 := bstep (se 2 (by rfl) ⟨2925636, by rfl⟩ : syracuseStep 7801697 = 5851273) B5851273
theorem B6949739 : Blo 810345 6949739 := bstep (se 1 (by rfl) ⟨5212304, by rfl⟩ : syracuseStep 6949739 = 10424609) B10424609
theorem B3084263 : Blo 810345 3084263 := bstep (se 1 (by rfl) ⟨2313197, by rfl⟩ : syracuseStep 3084263 = 4626395) B4626395
theorem B11866601 : Blo 810345 11866601 := bstep (se 2 (by rfl) ⟨4449975, by rfl⟩ : syracuseStep 11866601 = 8899951) B8899951
theorem B13865579 : Blo 810345 13865579 := bstep (se 1 (by rfl) ⟨10399184, by rfl⟩ : syracuseStep 13865579 = 20798369) B20798369
theorem B1218281 : Blo 810345 1218281 := bstep (se 2 (by rfl) ⟨456855, by rfl⟩ : syracuseStep 1218281 = 913711) B913711
theorem B44472509 : Blo 810345 44472509 := bstep (se 3 (by rfl) ⟨8338595, by rfl⟩ : syracuseStep 44472509 = 16677191) B16677191
theorem B23795963 : Blo 810345 23795963 := bstep (se 1 (by rfl) ⟨17846972, by rfl⟩ : syracuseStep 23795963 = 35693945) B35693945
theorem B1219367 : Blo 810345 1219367 := bstep (se 1 (by rfl) ⟨914525, by rfl⟩ : syracuseStep 1219367 = 1829051) B1829051
theorem B1219943 : Blo 810345 1219943 := bstep (se 1 (by rfl) ⟨914957, by rfl⟩ : syracuseStep 1219943 = 1829915) B1829915
theorem B1220303 : Blo 810345 1220303 := bstep (se 1 (by rfl) ⟨915227, by rfl⟩ : syracuseStep 1220303 = 1830455) B1830455
theorem B1220489 : Blo 810345 1220489 := bstep (se 2 (by rfl) ⟨457683, by rfl⟩ : syracuseStep 1220489 = 915367) B915367
theorem B14786803 : Blo 810345 14786803 := bstep (se 1 (by rfl) ⟨11090102, by rfl⟩ : syracuseStep 14786803 = 22180205) B22180205
theorem B11706929 : Blo 810345 11706929 := bstep (se 2 (by rfl) ⟨4390098, by rfl⟩ : syracuseStep 11706929 = 8780197) B8780197
theorem B3712175 : Blo 810345 3712175 := bstep (se 1 (by rfl) ⟨2784131, by rfl⟩ : syracuseStep 3712175 = 5568263) B5568263
theorem B7415263 : Blo 810345 7415263 := bstep (se 1 (by rfl) ⟨5561447, by rfl⟩ : syracuseStep 7415263 = 11122895) B11122895
theorem B6171227 : Blo 810345 6171227 := bstep (se 1 (by rfl) ⟨4628420, by rfl⟩ : syracuseStep 6171227 = 9256841) B9256841
theorem B16691321 : Blo 810345 16691321 := bstep (se 2 (by rfl) ⟨6259245, by rfl⟩ : syracuseStep 16691321 = 12518491) B12518491
theorem B14825339 : Blo 810345 14825339 := bstep (se 1 (by rfl) ⟨11119004, by rfl⟩ : syracuseStep 14825339 = 22238009) B22238009
theorem B2930683 : Blo 810345 2930683 := bstep (se 1 (by rfl) ⟨2198012, by rfl⟩ : syracuseStep 2930683 = 4396025) B4396025
theorem B2735099 : Blo 810345 2735099 := bstep (se 1 (by rfl) ⟨2051324, by rfl⟩ : syracuseStep 2735099 = 4102649) B4102649
theorem B2735423 : Blo 810345 2735423 := bstep (se 1 (by rfl) ⟨2051567, by rfl⟩ : syracuseStep 2735423 = 4103135) B4103135
theorem B2309951 : Blo 810345 2309951 := bstep (se 1 (by rfl) ⟨1732463, by rfl⟩ : syracuseStep 2309951 = 3464927) B3464927
theorem B2735963 : Blo 810345 2735963 := bstep (se 1 (by rfl) ⟨2051972, by rfl⟩ : syracuseStep 2735963 = 4103945) B4103945
theorem B1949791 : Blo 810345 1949791 := bstep (se 1 (by rfl) ⟨1462343, by rfl⟩ : syracuseStep 1949791 = 2924687) B2924687
theorem B8799191 : Blo 810345 8799191 := bstep (se 1 (by rfl) ⟨6599393, by rfl⟩ : syracuseStep 8799191 = 13198787) B13198787
theorem B39536585 : Blo 810345 39536585 := bstep (se 2 (by rfl) ⟨14826219, by rfl⟩ : syracuseStep 39536585 = 29652439) B29652439
theorem B5196905 : Blo 810345 5196905 := bstep (se 2 (by rfl) ⟨1948839, by rfl⟩ : syracuseStep 5196905 = 3897679) B3897679
theorem B2313755 : Blo 810345 2313755 := bstep (se 1 (by rfl) ⟨1735316, by rfl⟩ : syracuseStep 2313755 = 3470633) B3470633
theorem B2608807 : Blo 810345 2608807 := bstep (se 1 (by rfl) ⟨1956605, by rfl⟩ : syracuseStep 2608807 = 3913211) B3913211
theorem B29576987 : Blo 810345 29576987 := bstep (se 1 (by rfl) ⟨22182740, by rfl⟩ : syracuseStep 29576987 = 44365481) B44365481
theorem B59167097 : Blo 810345 59167097 := bstep (se 2 (by rfl) ⟨22187661, by rfl⟩ : syracuseStep 59167097 = 44375323) B44375323
theorem B3461885 : Blo 810345 3461885 := bstep (se 3 (by rfl) ⟨649103, by rfl⟩ : syracuseStep 3461885 = 1298207) B1298207
theorem B1824623 : Blo 810345 1824623 := bstep (se 1 (by rfl) ⟨1368467, by rfl⟩ : syracuseStep 1824623 = 2736935) B2736935
theorem B1825127 : Blo 810345 1825127 := bstep (se 1 (by rfl) ⟨1368845, by rfl⟩ : syracuseStep 1825127 = 2737691) B2737691
theorem B1825271 : Blo 810345 1825271 := bstep (se 1 (by rfl) ⟨1368953, by rfl⟩ : syracuseStep 1825271 = 2737907) B2737907
theorem B1825505 : Blo 810345 1825505 := bstep (se 2 (by rfl) ⟨684564, by rfl⟩ : syracuseStep 1825505 = 1369129) B1369129
theorem B1301231 : Blo 810345 1301231 := bstep (se 1 (by rfl) ⟨975923, by rfl⟩ : syracuseStep 1301231 = 1951847) B1951847
theorem B3464687 : Blo 810345 3464687 := bstep (se 1 (by rfl) ⟨2598515, by rfl⟩ : syracuseStep 3464687 = 5197031) B5197031
theorem B810747 : Blo 810345 810747 := bstep (se 1 (by rfl) ⟨608060, by rfl⟩ : syracuseStep 810747 = 1216121) B1216121
theorem B1826999 : Blo 810345 1826999 := bstep (se 1 (by rfl) ⟨1370249, by rfl⟩ : syracuseStep 1826999 = 2740499) B2740499
theorem B5202463 : Blo 810345 5202463 := bstep (se 1 (by rfl) ⟨3901847, by rfl⟩ : syracuseStep 5202463 = 7803695) B7803695
theorem B1368623 : Blo 810345 1368623 := bstep (se 1 (by rfl) ⟨1026467, by rfl⟩ : syracuseStep 1368623 = 2052935) B2052935
theorem B811751 : Blo 810345 811751 := bstep (se 1 (by rfl) ⟨608813, by rfl⟩ : syracuseStep 811751 = 1217627) B1217627
theorem B811771 : Blo 810345 811771 := bstep (se 1 (by rfl) ⟨608828, by rfl⟩ : syracuseStep 811771 = 1217657) B1217657
theorem B1369001 : Blo 810345 1369001 := bstep (se 2 (by rfl) ⟨513375, by rfl⟩ : syracuseStep 1369001 = 1026751) B1026751
theorem B1369055 : Blo 810345 1369055 := bstep (se 1 (by rfl) ⟨1026791, by rfl⟩ : syracuseStep 1369055 = 2053583) B2053583
theorem B1827881 : Blo 810345 1827881 := bstep (se 2 (by rfl) ⟨685455, by rfl⟩ : syracuseStep 1827881 = 1370911) B1370911
theorem B812415 : Blo 810345 812415 := bstep (se 1 (by rfl) ⟨609311, by rfl⟩ : syracuseStep 812415 = 1218623) B1218623
theorem B812635 : Blo 810345 812635 := bstep (se 1 (by rfl) ⟨609476, by rfl⟩ : syracuseStep 812635 = 1218953) B1218953
theorem B812703 : Blo 810345 812703 := bstep (se 1 (by rfl) ⟨609527, by rfl⟩ : syracuseStep 812703 = 1219055) B1219055
theorem B813119 : Blo 810345 813119 := bstep (se 1 (by rfl) ⟨609839, by rfl⟩ : syracuseStep 813119 = 1219679) B1219679
theorem B70150211 : Blo 810345 70150211 := bstep (se 1 (by rfl) ⟨52612658, by rfl⟩ : syracuseStep 70150211 = 105225317) B105225317
theorem B813147 : Blo 810345 813147 := bstep (se 1 (by rfl) ⟨609860, by rfl⟩ : syracuseStep 813147 = 1219721) B1219721
theorem B813415 : Blo 810345 813415 := bstep (se 1 (by rfl) ⟨610061, by rfl⟩ : syracuseStep 813415 = 1220123) B1220123
theorem B7432847 : Blo 810345 7432847 := bstep (se 1 (by rfl) ⟨5574635, by rfl⟩ : syracuseStep 7432847 = 11149271) B11149271
theorem B814015 : Blo 810345 814015 := bstep (se 1 (by rfl) ⟨610511, by rfl⟩ : syracuseStep 814015 = 1221023) B1221023
theorem B15625385 : Blo 810345 15625385 := bstep (se 2 (by rfl) ⟨5859519, by rfl⟩ : syracuseStep 15625385 = 11719039) B11719039
theorem B2747627 : Blo 810345 2747627 := bstep (se 1 (by rfl) ⟨2060720, by rfl⟩ : syracuseStep 2747627 = 4121441) B4121441
theorem B814319 : Blo 810345 814319 := bstep (se 1 (by rfl) ⟨610739, by rfl⟩ : syracuseStep 814319 = 1221479) B1221479
theorem B2059627 : Blo 810345 2059627 := bstep (se 1 (by rfl) ⟨1544720, by rfl⟩ : syracuseStep 2059627 = 3089441) B3089441
theorem B1830815 : Blo 810345 1830815 := bstep (se 1 (by rfl) ⟨1373111, by rfl⟩ : syracuseStep 1830815 = 2746223) B2746223
theorem B1831049 : Blo 810345 1831049 := bstep (se 2 (by rfl) ⟨686643, by rfl⟩ : syracuseStep 1831049 = 1373287) B1373287
theorem B1732985 : Blo 810345 1732985 := bstep (se 2 (by rfl) ⟨649869, by rfl⟩ : syracuseStep 1732985 = 1299739) B1299739
theorem B3469985 : Blo 810345 3469985 := bstep (se 2 (by rfl) ⟨1301244, by rfl⟩ : syracuseStep 3469985 = 2602489) B2602489
theorem B1831679 : Blo 810345 1831679 := bstep (se 1 (by rfl) ⟨1373759, by rfl⟩ : syracuseStep 1831679 = 2747519) B2747519
theorem B1832039 : Blo 810345 1832039 := bstep (se 1 (by rfl) ⟨1374029, by rfl⟩ : syracuseStep 1832039 = 2748059) B2748059
theorem B24442033 : Blo 810345 24442033 := bstep (se 2 (by rfl) ⟨9165762, by rfl⟩ : syracuseStep 24442033 = 18331525) B18331525
theorem B914971 : Blo 810345 914971 := bstep (se 1 (by rfl) ⟨686228, by rfl⟩ : syracuseStep 914971 = 1372457) B1372457
theorem B3077747 : Blo 810345 3077747 := bstep (se 1 (by rfl) ⟨2308310, by rfl⟩ : syracuseStep 3077747 = 4616621) B4616621
theorem B114259679 : Blo 810345 114259679 := bstep (se 1 (by rfl) ⟨85694759, by rfl⟩ : syracuseStep 114259679 = 171389519) B171389519
theorem B5863589 : Blo 810345 5863589 := bstep (se 4 (by rfl) ⟨549711, by rfl⟩ : syracuseStep 5863589 = 1099423) B1099423
theorem B3078431 : Blo 810345 3078431 := bstep (se 1 (by rfl) ⟨2308823, by rfl⟩ : syracuseStep 3078431 = 4617647) B4617647
theorem B1538767 : Blo 810345 1538767 := bstep (se 1 (by rfl) ⟨1154075, by rfl⟩ : syracuseStep 1538767 = 2308151) B2308151
theorem B3472409 : Blo 810345 3472409 := bstep (se 2 (by rfl) ⟨1302153, by rfl⟩ : syracuseStep 3472409 = 2604307) B2604307
theorem B1539739 : Blo 810345 1539739 := bstep (se 1 (by rfl) ⟨1154804, by rfl⟩ : syracuseStep 1539739 = 2309609) B2309609
theorem B7405663 : Blo 810345 7405663 := bstep (se 1 (by rfl) ⟨5554247, by rfl⟩ : syracuseStep 7405663 = 11108495) B11108495
theorem B5866127 : Blo 810345 5866127 := bstep (se 1 (by rfl) ⟨4399595, by rfl⟩ : syracuseStep 5866127 = 8799191) B8799191
theorem B1542503 : Blo 810345 1542503 := bstep (se 1 (by rfl) ⟨1156877, by rfl⟩ : syracuseStep 1542503 = 2313755) B2313755
theorem B9243719 : Blo 810345 9243719 := bstep (se 1 (by rfl) ⟨6932789, by rfl⟩ : syracuseStep 9243719 = 13865579) B13865579
theorem B1216415 : Blo 810345 1216415 := bstep (se 1 (by rfl) ⟨912311, by rfl⟩ : syracuseStep 1216415 = 1824623) B1824623
theorem B15863975 : Blo 810345 15863975 := bstep (se 1 (by rfl) ⟨11897981, by rfl⟩ : syracuseStep 15863975 = 23795963) B23795963
theorem B1216751 : Blo 810345 1216751 := bstep (se 1 (by rfl) ⟨912563, by rfl⟩ : syracuseStep 1216751 = 1825127) B1825127
theorem B1216847 : Blo 810345 1216847 := bstep (se 1 (by rfl) ⟨912635, by rfl⟩ : syracuseStep 1216847 = 1825271) B1825271
theorem B1217003 : Blo 810345 1217003 := bstep (se 1 (by rfl) ⟨912752, by rfl⟩ : syracuseStep 1217003 = 1825505) B1825505
theorem B3478409 : Blo 810345 3478409 := bstep (se 2 (by rfl) ⟨1304403, by rfl⟩ : syracuseStep 3478409 = 2608807) B2608807
theorem B1217999 : Blo 810345 1217999 := bstep (se 1 (by rfl) ⟨913499, by rfl⟩ : syracuseStep 1217999 = 1826999) B1826999
theorem B7804619 : Blo 810345 7804619 := bstep (se 1 (by rfl) ⟨5853464, by rfl⟩ : syracuseStep 7804619 = 11706929) B11706929
theorem B1218587 : Blo 810345 1218587 := bstep (se 1 (by rfl) ⟨913940, by rfl⟩ : syracuseStep 1218587 = 1827881) B1827881
theorem B46766807 : Blo 810345 46766807 := bstep (se 1 (by rfl) ⟨35075105, by rfl⟩ : syracuseStep 46766807 = 70150211) B70150211
theorem B4955231 : Blo 810345 4955231 := bstep (se 1 (by rfl) ⟨3716423, by rfl⟩ : syracuseStep 4955231 = 7432847) B7432847
theorem B1219961 : Blo 810345 1219961 := bstep (se 2 (by rfl) ⟨457485, by rfl⟩ : syracuseStep 1219961 = 914971) B914971
theorem B1220543 : Blo 810345 1220543 := bstep (se 1 (by rfl) ⟨915407, by rfl⟩ : syracuseStep 1220543 = 1830815) B1830815
theorem B3907577 : Blo 810345 3907577 := bstep (se 2 (by rfl) ⟨1465341, by rfl⟩ : syracuseStep 3907577 = 2930683) B2930683
theorem B1220699 : Blo 810345 1220699 := bstep (se 1 (by rfl) ⟨915524, by rfl⟩ : syracuseStep 1220699 = 1831049) B1831049
theorem B1155323 : Blo 810345 1155323 := bstep (se 1 (by rfl) ⟨866492, by rfl⟩ : syracuseStep 1155323 = 1732985) B1732985
theorem B1221119 : Blo 810345 1221119 := bstep (se 1 (by rfl) ⟨915839, by rfl⟩ : syracuseStep 1221119 = 1831679) B1831679
theorem B1221359 : Blo 810345 1221359 := bstep (se 1 (by rfl) ⟨916019, by rfl⟩ : syracuseStep 1221359 = 1832039) B1832039
theorem B3909059 : Blo 810345 3909059 := bstep (se 1 (by rfl) ⟨2931794, by rfl⟩ : syracuseStep 3909059 = 5863589) B5863589
theorem B2599721 : Blo 810345 2599721 := bstep (se 2 (by rfl) ⟨974895, by rfl⟩ : syracuseStep 2599721 = 1949791) B1949791
theorem B4107347 : Blo 810345 4107347 := bstep (se 1 (by rfl) ⟨3080510, by rfl⟩ : syracuseStep 4107347 = 6161021) B6161021
theorem B67677535 : Blo 810345 67677535 := bstep (se 1 (by rfl) ⟨50758151, by rfl⟩ : syracuseStep 67677535 = 101516303) B101516303
theorem B4107995 : Blo 810345 4107995 := bstep (se 1 (by rfl) ⟨3080996, by rfl⟩ : syracuseStep 4107995 = 6161993) B6161993
theorem B26357723 : Blo 810345 26357723 := bstep (se 1 (by rfl) ⟨19768292, by rfl⟩ : syracuseStep 26357723 = 39536585) B39536585
theorem B2470063 : Blo 810345 2470063 := bstep (se 1 (by rfl) ⟨1852547, by rfl⟩ : syracuseStep 2470063 = 3705095) B3705095
theorem B4633159 : Blo 810345 4633159 := bstep (se 1 (by rfl) ⟨3474869, by rfl⟩ : syracuseStep 4633159 = 6949739) B6949739
theorem B7911067 : Blo 810345 7911067 := bstep (se 1 (by rfl) ⟨5933300, by rfl⟩ : syracuseStep 7911067 = 11866601) B11866601
theorem B2307923 : Blo 810345 2307923 := bstep (se 1 (by rfl) ⟨1730942, by rfl⟩ : syracuseStep 2307923 = 3461885) B3461885
theorem B2309791 : Blo 810345 2309791 := bstep (se 1 (by rfl) ⟨1732343, by rfl⟩ : syracuseStep 2309791 = 3464687) B3464687
theorem B2474783 : Blo 810345 2474783 := bstep (se 1 (by rfl) ⟨1856087, by rfl⟩ : syracuseStep 2474783 = 3712175) B3712175
theorem B32589377 : Blo 810345 32589377 := bstep (se 2 (by rfl) ⟨12221016, by rfl⟩ : syracuseStep 32589377 = 24442033) B24442033
theorem B4114151 : Blo 810345 4114151 := bstep (se 1 (by rfl) ⟨3085613, by rfl⟩ : syracuseStep 4114151 = 6171227) B6171227
theorem B9259757 : Blo 810345 9259757 := bstep (se 3 (by rfl) ⟨1736204, by rfl⟩ : syracuseStep 9259757 = 3472409) B3472409
theorem B11127547 : Blo 810345 11127547 := bstep (se 1 (by rfl) ⟨8345660, by rfl⟩ : syracuseStep 11127547 = 16691321) B16691321
theorem B2313323 : Blo 810345 2313323 := bstep (se 1 (by rfl) ⟨1734992, by rfl⟩ : syracuseStep 2313323 = 3469985) B3469985
theorem B2051689 : Blo 810345 2051689 := bstep (se 2 (by rfl) ⟨769383, by rfl⟩ : syracuseStep 2051689 = 1538767) B1538767
theorem B2051831 : Blo 810345 2051831 := bstep (se 1 (by rfl) ⟨1538873, by rfl⟩ : syracuseStep 2051831 = 3077747) B3077747
theorem B76173119 : Blo 810345 76173119 := bstep (se 1 (by rfl) ⟨57129839, by rfl⟩ : syracuseStep 76173119 = 114259679) B114259679
theorem B9883559 : Blo 810345 9883559 := bstep (se 1 (by rfl) ⟨7412669, by rfl⟩ : syracuseStep 9883559 = 14825339) B14825339
theorem B2052287 : Blo 810345 2052287 := bstep (se 1 (by rfl) ⟨1539215, by rfl⟩ : syracuseStep 2052287 = 3078431) B3078431
theorem B1823399 : Blo 810345 1823399 := bstep (se 1 (by rfl) ⟨1367549, by rfl⟩ : syracuseStep 1823399 = 2735099) B2735099
theorem B2052985 : Blo 810345 2052985 := bstep (se 2 (by rfl) ⟨769869, by rfl⟩ : syracuseStep 2052985 = 1539739) B1539739
theorem B1823615 : Blo 810345 1823615 := bstep (se 1 (by rfl) ⟨1367711, by rfl⟩ : syracuseStep 1823615 = 2735423) B2735423
theorem B1823975 : Blo 810345 1823975 := bstep (se 1 (by rfl) ⟨1367981, by rfl⟩ : syracuseStep 1823975 = 2735963) B2735963
theorem B19715737 : Blo 810345 19715737 := bstep (se 2 (by rfl) ⟨7393401, by rfl⟩ : syracuseStep 19715737 = 14786803) B14786803
theorem B4216531 : Blo 810345 4216531 := bstep (se 1 (by rfl) ⟨3162398, by rfl⟩ : syracuseStep 4216531 = 6324797) B6324797
theorem B6936617 : Blo 810345 6936617 := bstep (se 2 (by rfl) ⟨2601231, by rfl⟩ : syracuseStep 6936617 = 5202463) B5202463
theorem B2055041 : Blo 810345 2055041 := bstep (se 2 (by rfl) ⟨770640, by rfl⟩ : syracuseStep 2055041 = 1541281) B1541281
theorem B5201131 : Blo 810345 5201131 := bstep (se 1 (by rfl) ⟨3900848, by rfl⟩ : syracuseStep 5201131 = 7801697) B7801697
theorem B9887017 : Blo 810345 9887017 := bstep (se 2 (by rfl) ⟨3707631, by rfl⟩ : syracuseStep 9887017 = 7415263) B7415263
theorem B3464603 : Blo 810345 3464603 := bstep (se 1 (by rfl) ⟨2598452, by rfl⟩ : syracuseStep 3464603 = 5196905) B5196905
theorem B19717991 : Blo 810345 19717991 := bstep (se 1 (by rfl) ⟨14788493, by rfl⟩ : syracuseStep 19717991 = 29576987) B29576987
theorem B2056175 : Blo 810345 2056175 := bstep (se 1 (by rfl) ⟨1542131, by rfl⟩ : syracuseStep 2056175 = 3084263) B3084263
theorem B39444731 : Blo 810345 39444731 := bstep (se 1 (by rfl) ⟨29583548, by rfl⟩ : syracuseStep 39444731 = 59167097) B59167097
theorem B812187 : Blo 810345 812187 := bstep (se 1 (by rfl) ⟨609140, by rfl⟩ : syracuseStep 812187 = 1218281) B1218281
theorem B29648339 : Blo 810345 29648339 := bstep (se 1 (by rfl) ⟨22236254, by rfl⟩ : syracuseStep 29648339 = 44472509) B44472509
theorem B2746169 : Blo 810345 2746169 := bstep (se 2 (by rfl) ⟨1029813, by rfl⟩ : syracuseStep 2746169 = 2059627) B2059627
theorem B812911 : Blo 810345 812911 := bstep (se 1 (by rfl) ⟨609683, by rfl⟩ : syracuseStep 812911 = 1219367) B1219367
theorem B813295 : Blo 810345 813295 := bstep (se 1 (by rfl) ⟨609971, by rfl⟩ : syracuseStep 813295 = 1219943) B1219943
theorem B813535 : Blo 810345 813535 := bstep (se 1 (by rfl) ⟨610151, by rfl⟩ : syracuseStep 813535 = 1220303) B1220303
theorem B813659 : Blo 810345 813659 := bstep (se 1 (by rfl) ⟨610244, by rfl⟩ : syracuseStep 813659 = 1220489) B1220489
theorem B912415 : Blo 810345 912415 := bstep (se 1 (by rfl) ⟨684311, by rfl⟩ : syracuseStep 912415 = 1368623) B1368623
theorem B912667 : Blo 810345 912667 := bstep (se 1 (by rfl) ⟨684500, by rfl⟩ : syracuseStep 912667 = 1369001) B1369001
theorem B912703 : Blo 810345 912703 := bstep (se 1 (by rfl) ⟨684527, by rfl⟩ : syracuseStep 912703 = 1369055) B1369055
theorem B3469949 : Blo 810345 3469949 := bstep (se 3 (by rfl) ⟨650615, by rfl⟩ : syracuseStep 3469949 = 1301231) B1301231
theorem B10416923 : Blo 810345 10416923 := bstep (se 1 (by rfl) ⟨7812692, by rfl⟩ : syracuseStep 10416923 = 15625385) B15625385
theorem B1831751 : Blo 810345 1831751 := bstep (se 1 (by rfl) ⟨1373813, by rfl⟩ : syracuseStep 1831751 = 2747627) B2747627
theorem B1539967 : Blo 810345 1539967 := bstep (se 1 (by rfl) ⟨1154975, by rfl⟩ : syracuseStep 1539967 = 2309951) B2309951
theorem B3080861 : Blo 810345 3080861 := bstep (se 3 (by rfl) ⟨577661, by rfl⟩ : syracuseStep 3080861 = 1155323) B1155323
theorem B21726251 : Blo 810345 21726251 := bstep (se 1 (by rfl) ⟨16294688, by rfl⟩ : syracuseStep 21726251 = 32589377) B32589377
theorem B6162479 : Blo 810345 6162479 := bstep (se 1 (by rfl) ⟨4621859, by rfl⟩ : syracuseStep 6162479 = 9243719) B9243719
theorem B1542215 : Blo 810345 1542215 := bstep (se 1 (by rfl) ⟨1156661, by rfl⟩ : syracuseStep 1542215 = 2313323) B2313323
theorem B6589039 : Blo 810345 6589039 := bstep (se 1 (by rfl) ⟨4941779, by rfl⟩ : syracuseStep 6589039 = 9883559) B9883559
theorem B1215599 : Blo 810345 1215599 := bstep (se 1 (by rfl) ⟨911699, by rfl⟩ : syracuseStep 1215599 = 1823399) B1823399
theorem B1215743 : Blo 810345 1215743 := bstep (se 1 (by rfl) ⟨911807, by rfl⟩ : syracuseStep 1215743 = 1823615) B1823615
theorem B1215983 : Blo 810345 1215983 := bstep (se 1 (by rfl) ⟨911987, by rfl⟩ : syracuseStep 1215983 = 1823975) B1823975
theorem B4624411 : Blo 810345 4624411 := bstep (se 1 (by rfl) ⟨3468308, by rfl⟩ : syracuseStep 4624411 = 6936617) B6936617
theorem B1216553 : Blo 810345 1216553 := bstep (se 2 (by rfl) ⟨456207, by rfl⟩ : syracuseStep 1216553 = 912415) B912415
theorem B1216889 : Blo 810345 1216889 := bstep (se 2 (by rfl) ⟨456333, by rfl⟩ : syracuseStep 1216889 = 912667) B912667
theorem B1216937 : Blo 810345 1216937 := bstep (se 2 (by rfl) ⟨456351, by rfl⟩ : syracuseStep 1216937 = 912703) B912703
theorem B13145327 : Blo 810345 13145327 := bstep (se 1 (by rfl) ⟨9858995, by rfl⟩ : syracuseStep 13145327 = 19717991) B19717991
theorem B19765559 : Blo 810345 19765559 := bstep (se 1 (by rfl) ⟨14824169, by rfl⟩ : syracuseStep 19765559 = 29648339) B29648339
theorem B26287649 : Blo 810345 26287649 := bstep (se 2 (by rfl) ⟨9857868, by rfl⟩ : syracuseStep 26287649 = 19715737) B19715737
theorem B17571815 : Blo 810345 17571815 := bstep (se 1 (by rfl) ⟨13178861, by rfl⟩ : syracuseStep 17571815 = 26357723) B26357723
theorem B13213949 : Blo 810345 13213949 := bstep (se 3 (by rfl) ⟨2477615, by rfl⟩ : syracuseStep 13213949 = 4955231) B4955231
theorem B1221167 : Blo 810345 1221167 := bstep (se 1 (by rfl) ⟨915875, by rfl⟩ : syracuseStep 1221167 = 1831751) B1831751
theorem B13182689 : Blo 810345 13182689 := bstep (se 2 (by rfl) ⟨4943508, by rfl⟩ : syracuseStep 13182689 = 9887017) B9887017
theorem B9874217 : Blo 810345 9874217 := bstep (se 2 (by rfl) ⟨3702831, by rfl⟩ : syracuseStep 9874217 = 7405663) B7405663
theorem B3910751 : Blo 810345 3910751 := bstep (se 1 (by rfl) ⟨2933063, by rfl⟩ : syracuseStep 3910751 = 5866127) B5866127
theorem B1649855 : Blo 810345 1649855 := bstep (se 1 (by rfl) ⟨1237391, by rfl⟩ : syracuseStep 1649855 = 2474783) B2474783
theorem B6173171 : Blo 810345 6173171 := bstep (se 1 (by rfl) ⟨4629878, by rfl⟩ : syracuseStep 6173171 = 9259757) B9259757
theorem B31177871 : Blo 810345 31177871 := bstep (se 1 (by rfl) ⟨23383403, by rfl⟩ : syracuseStep 31177871 = 46766807) B46766807
theorem B2735585 : Blo 810345 2735585 := bstep (se 2 (by rfl) ⟨1025844, by rfl⟩ : syracuseStep 2735585 = 2051689) B2051689
theorem B2309735 : Blo 810345 2309735 := bstep (se 1 (by rfl) ⟨1732301, by rfl⟩ : syracuseStep 2309735 = 3464603) B3464603
theorem B2605051 : Blo 810345 2605051 := bstep (se 1 (by rfl) ⟨1953788, by rfl⟩ : syracuseStep 2605051 = 3907577) B3907577
theorem B26296487 : Blo 810345 26296487 := bstep (se 1 (by rfl) ⟨19722365, by rfl⟩ : syracuseStep 26296487 = 39444731) B39444731
theorem B3293417 : Blo 810345 3293417 := bstep (se 2 (by rfl) ⟨1235031, by rfl⟩ : syracuseStep 3293417 = 2470063) B2470063
theorem B6177545 : Blo 810345 6177545 := bstep (se 2 (by rfl) ⟨2316579, by rfl⟩ : syracuseStep 6177545 = 4633159) B4633159
theorem B4113341 : Blo 810345 4113341 := bstep (se 3 (by rfl) ⟨771251, by rfl⟩ : syracuseStep 4113341 = 1542503) B1542503
theorem B2606039 : Blo 810345 2606039 := bstep (se 1 (by rfl) ⟨1954529, by rfl⟩ : syracuseStep 2606039 = 3909059) B3909059
theorem B2737313 : Blo 810345 2737313 := bstep (se 2 (by rfl) ⟨1026492, by rfl⟩ : syracuseStep 2737313 = 2052985) B2052985
theorem B2738231 : Blo 810345 2738231 := bstep (se 1 (by rfl) ⟨2053673, by rfl⟩ : syracuseStep 2738231 = 4107347) B4107347
theorem B5622041 : Blo 810345 5622041 := bstep (se 2 (by rfl) ⟨2108265, by rfl⟩ : syracuseStep 5622041 = 4216531) B4216531
theorem B2738663 : Blo 810345 2738663 := bstep (se 1 (by rfl) ⟨2053997, by rfl⟩ : syracuseStep 2738663 = 4107995) B4107995
theorem B2313299 : Blo 810345 2313299 := bstep (se 1 (by rfl) ⟨1734974, by rfl⟩ : syracuseStep 2313299 = 3469949) B3469949
theorem B6934841 : Blo 810345 6934841 := bstep (se 2 (by rfl) ⟨2600565, by rfl⟩ : syracuseStep 6934841 = 5201131) B5201131
theorem B2053289 : Blo 810345 2053289 := bstep (se 2 (by rfl) ⟨769983, by rfl⟩ : syracuseStep 2053289 = 1539967) B1539967
theorem B2742767 : Blo 810345 2742767 := bstep (se 1 (by rfl) ⟨2057075, by rfl⟩ : syracuseStep 2742767 = 4114151) B4114151
theorem B1367887 : Blo 810345 1367887 := bstep (se 1 (by rfl) ⟨1025915, by rfl⟩ : syracuseStep 1367887 = 2051831) B2051831
theorem B50782079 : Blo 810345 50782079 := bstep (se 1 (by rfl) ⟨38086559, by rfl⟩ : syracuseStep 50782079 = 76173119) B76173119
theorem B810943 : Blo 810345 810943 := bstep (se 1 (by rfl) ⟨608207, by rfl⟩ : syracuseStep 810943 = 1216415) B1216415
theorem B10575983 : Blo 810345 10575983 := bstep (se 1 (by rfl) ⟨7931987, by rfl⟩ : syracuseStep 10575983 = 15863975) B15863975
theorem B1368191 : Blo 810345 1368191 := bstep (se 1 (by rfl) ⟨1026143, by rfl⟩ : syracuseStep 1368191 = 2052287) B2052287
theorem B811167 : Blo 810345 811167 := bstep (se 1 (by rfl) ⟨608375, by rfl⟩ : syracuseStep 811167 = 1216751) B1216751
theorem B811231 : Blo 810345 811231 := bstep (se 1 (by rfl) ⟨608423, by rfl⟩ : syracuseStep 811231 = 1216847) B1216847
theorem B811335 : Blo 810345 811335 := bstep (se 1 (by rfl) ⟨608501, by rfl⟩ : syracuseStep 811335 = 1217003) B1217003
theorem B2318939 : Blo 810345 2318939 := bstep (se 1 (by rfl) ⟨1739204, by rfl⟩ : syracuseStep 2318939 = 3478409) B3478409
theorem B811999 : Blo 810345 811999 := bstep (se 1 (by rfl) ⟨608999, by rfl⟩ : syracuseStep 811999 = 1217999) B1217999
theorem B14836729 : Blo 810345 14836729 := bstep (se 2 (by rfl) ⟨5563773, by rfl⟩ : syracuseStep 14836729 = 11127547) B11127547
theorem B5203079 : Blo 810345 5203079 := bstep (se 1 (by rfl) ⟨3902309, by rfl⟩ : syracuseStep 5203079 = 7804619) B7804619
theorem B812391 : Blo 810345 812391 := bstep (se 1 (by rfl) ⟨609293, by rfl⟩ : syracuseStep 812391 = 1218587) B1218587
theorem B90236713 : Blo 810345 90236713 := bstep (se 2 (by rfl) ⟨33838767, by rfl⟩ : syracuseStep 90236713 = 67677535) B67677535
theorem B1370027 : Blo 810345 1370027 := bstep (se 1 (by rfl) ⟨1027520, by rfl⟩ : syracuseStep 1370027 = 2055041) B2055041
theorem B813307 : Blo 810345 813307 := bstep (se 1 (by rfl) ⟨609980, by rfl⟩ : syracuseStep 813307 = 1219961) B1219961
theorem B813695 : Blo 810345 813695 := bstep (se 1 (by rfl) ⟨610271, by rfl⟩ : syracuseStep 813695 = 1220543) B1220543
theorem B1370783 : Blo 810345 1370783 := bstep (se 1 (by rfl) ⟨1028087, by rfl⟩ : syracuseStep 1370783 = 2056175) B2056175
theorem B813799 : Blo 810345 813799 := bstep (se 1 (by rfl) ⟨610349, by rfl⟩ : syracuseStep 813799 = 1220699) B1220699
theorem B814079 : Blo 810345 814079 := bstep (se 1 (by rfl) ⟨610559, by rfl⟩ : syracuseStep 814079 = 1221119) B1221119
theorem B814239 : Blo 810345 814239 := bstep (se 1 (by rfl) ⟨610679, by rfl⟩ : syracuseStep 814239 = 1221359) B1221359
theorem B1830779 : Blo 810345 1830779 := bstep (se 1 (by rfl) ⟨1373084, by rfl⟩ : syracuseStep 1830779 = 2746169) B2746169
theorem B1733147 : Blo 810345 1733147 := bstep (se 1 (by rfl) ⟨1299860, by rfl⟩ : syracuseStep 1733147 = 2599721) B2599721
theorem B10548089 : Blo 810345 10548089 := bstep (se 2 (by rfl) ⟨3955533, by rfl⟩ : syracuseStep 10548089 = 7911067) B7911067
theorem B6944615 : Blo 810345 6944615 := bstep (se 1 (by rfl) ⟨5208461, by rfl⟩ : syracuseStep 6944615 = 10416923) B10416923
theorem B1538615 : Blo 810345 1538615 := bstep (se 1 (by rfl) ⟨1153961, by rfl⟩ : syracuseStep 1538615 = 2307923) B2307923
theorem B3079721 : Blo 810345 3079721 := bstep (se 2 (by rfl) ⟨1154895, by rfl⟩ : syracuseStep 3079721 = 2309791) B2309791
theorem B17530991 : Blo 810345 17530991 := bstep (se 1 (by rfl) ⟨13148243, by rfl⟩ : syracuseStep 17530991 = 26296487) B26296487
theorem B8782445 : Blo 810345 8782445 := bstep (se 3 (by rfl) ⟨1646708, by rfl⟩ : syracuseStep 8782445 = 3293417) B3293417
theorem B1737359 : Blo 810345 1737359 := bstep (se 1 (by rfl) ⟨1303019, by rfl⟩ : syracuseStep 1737359 = 2606039) B2606039
theorem B14484167 : Blo 810345 14484167 := bstep (se 1 (by rfl) ⟨10863125, by rfl⟩ : syracuseStep 14484167 = 21726251) B21726251
theorem B4623227 : Blo 810345 4623227 := bstep (se 1 (by rfl) ⟨3467420, by rfl⟩ : syracuseStep 4623227 = 6934841) B6934841
theorem B8785385 : Blo 810345 8785385 := bstep (se 2 (by rfl) ⟨3294519, by rfl⟩ : syracuseStep 8785385 = 6589039) B6589039
theorem B33854719 : Blo 810345 33854719 := bstep (se 1 (by rfl) ⟨25391039, by rfl⟩ : syracuseStep 33854719 = 50782079) B50782079
theorem B6165881 : Blo 810345 6165881 := bstep (se 2 (by rfl) ⟨2312205, by rfl⟩ : syracuseStep 6165881 = 4624411) B4624411
theorem B7050655 : Blo 810345 7050655 := bstep (se 1 (by rfl) ⟨5287991, by rfl⟩ : syracuseStep 7050655 = 10575983) B10575983
theorem B1545959 : Blo 810345 1545959 := bstep (se 1 (by rfl) ⟨1159469, by rfl⟩ : syracuseStep 1545959 = 2318939) B2318939
theorem B4102973 : Blo 810345 4102973 := bstep (se 3 (by rfl) ⟨769307, by rfl⟩ : syracuseStep 4102973 = 1538615) B1538615
theorem B1220519 : Blo 810345 1220519 := bstep (se 1 (by rfl) ⟨915389, by rfl⟩ : syracuseStep 1220519 = 1830779) B1830779
theorem B6168797 : Blo 810345 6168797 := bstep (se 3 (by rfl) ⟨1156649, by rfl⟩ : syracuseStep 6168797 = 2313299) B2313299
theorem B1155431 : Blo 810345 1155431 := bstep (se 1 (by rfl) ⟨866573, by rfl⟩ : syracuseStep 1155431 = 1733147) B1733147
theorem B4399613 : Blo 810345 4399613 := bstep (se 3 (by rfl) ⟨824927, by rfl⟩ : syracuseStep 4399613 = 1649855) B1649855
theorem B4629743 : Blo 810345 4629743 := bstep (se 1 (by rfl) ⟨3472307, by rfl⟩ : syracuseStep 4629743 = 6944615) B6944615
theorem B20785247 : Blo 810345 20785247 := bstep (se 1 (by rfl) ⟨15588935, by rfl⟩ : syracuseStep 20785247 = 31177871) B31177871
theorem B35237197 : Blo 810345 35237197 := bstep (se 3 (by rfl) ⟨6606974, by rfl⟩ : syracuseStep 35237197 = 13213949) B13213949
theorem B4108319 : Blo 810345 4108319 := bstep (se 1 (by rfl) ⟨3081239, by rfl⟩ : syracuseStep 4108319 = 6162479) B6162479
theorem B1028143 : Blo 810345 1028143 := bstep (se 1 (by rfl) ⟨771107, by rfl⟩ : syracuseStep 1028143 = 1542215) B1542215
theorem B3748027 : Blo 810345 3748027 := bstep (se 1 (by rfl) ⟨2811020, by rfl⟩ : syracuseStep 3748027 = 5622041) B5622041
theorem B8763551 : Blo 810345 8763551 := bstep (se 1 (by rfl) ⟨6572663, by rfl⟩ : syracuseStep 8763551 = 13145327) B13145327
theorem B11714543 : Blo 810345 11714543 := bstep (se 1 (by rfl) ⟨8785907, by rfl⟩ : syracuseStep 11714543 = 17571815) B17571815
theorem B52708157 : Blo 810345 52708157 := bstep (se 3 (by rfl) ⟨9882779, by rfl⟩ : syracuseStep 52708157 = 19765559) B19765559
theorem B2607167 : Blo 810345 2607167 := bstep (se 1 (by rfl) ⟨1955375, by rfl⟩ : syracuseStep 2607167 = 3910751) B3910751
theorem B4115447 : Blo 810345 4115447 := bstep (se 1 (by rfl) ⟨3086585, by rfl⟩ : syracuseStep 4115447 = 6173171) B6173171
theorem B7032059 : Blo 810345 7032059 := bstep (se 1 (by rfl) ⟨5274044, by rfl⟩ : syracuseStep 7032059 = 10548089) B10548089
theorem B1823723 : Blo 810345 1823723 := bstep (se 1 (by rfl) ⟨1367792, by rfl⟩ : syracuseStep 1823723 = 2735585) B2735585
theorem B2053147 : Blo 810345 2053147 := bstep (se 1 (by rfl) ⟨1539860, by rfl⟩ : syracuseStep 2053147 = 3079721) B3079721
theorem B1823849 : Blo 810345 1823849 := bstep (se 2 (by rfl) ⟨683943, by rfl⟩ : syracuseStep 1823849 = 1367887) B1367887
theorem B2053907 : Blo 810345 2053907 := bstep (se 1 (by rfl) ⟨1540430, by rfl⟩ : syracuseStep 2053907 = 3080861) B3080861
theorem B4118363 : Blo 810345 4118363 := bstep (se 1 (by rfl) ⟨3088772, by rfl⟩ : syracuseStep 4118363 = 6177545) B6177545
theorem B2742227 : Blo 810345 2742227 := bstep (se 1 (by rfl) ⟨2056670, by rfl⟩ : syracuseStep 2742227 = 4113341) B4113341
theorem B1824875 : Blo 810345 1824875 := bstep (se 1 (by rfl) ⟨1368656, by rfl⟩ : syracuseStep 1824875 = 2737313) B2737313
theorem B19782305 : Blo 810345 19782305 := bstep (se 2 (by rfl) ⟨7418364, by rfl⟩ : syracuseStep 19782305 = 14836729) B14836729
theorem B1825487 : Blo 810345 1825487 := bstep (se 1 (by rfl) ⟨1369115, by rfl⟩ : syracuseStep 1825487 = 2738231) B2738231
theorem B1825775 : Blo 810345 1825775 := bstep (se 1 (by rfl) ⟨1369331, by rfl⟩ : syracuseStep 1825775 = 2738663) B2738663
theorem B810399 : Blo 810345 810399 := bstep (se 1 (by rfl) ⟨607799, by rfl⟩ : syracuseStep 810399 = 1215599) B1215599
theorem B810495 : Blo 810345 810495 := bstep (se 1 (by rfl) ⟨607871, by rfl⟩ : syracuseStep 810495 = 1215743) B1215743
theorem B810655 : Blo 810345 810655 := bstep (se 1 (by rfl) ⟨607991, by rfl⟩ : syracuseStep 810655 = 1215983) B1215983
theorem B120315617 : Blo 810345 120315617 := bstep (se 2 (by rfl) ⟨45118356, by rfl⟩ : syracuseStep 120315617 = 90236713) B90236713
theorem B811035 : Blo 810345 811035 := bstep (se 1 (by rfl) ⟨608276, by rfl⟩ : syracuseStep 811035 = 1216553) B1216553
theorem B811259 : Blo 810345 811259 := bstep (se 1 (by rfl) ⟨608444, by rfl⟩ : syracuseStep 811259 = 1216889) B1216889
theorem B811291 : Blo 810345 811291 := bstep (se 1 (by rfl) ⟨608468, by rfl⟩ : syracuseStep 811291 = 1216937) B1216937
theorem B1368859 : Blo 810345 1368859 := bstep (se 1 (by rfl) ⟨1026644, by rfl⟩ : syracuseStep 1368859 = 2053289) B2053289
theorem B1828511 : Blo 810345 1828511 := bstep (se 1 (by rfl) ⟨1371383, by rfl⟩ : syracuseStep 1828511 = 2742767) B2742767
theorem B35153837 : Blo 810345 35153837 := bstep (se 3 (by rfl) ⟨6591344, by rfl⟩ : syracuseStep 35153837 = 13182689) B13182689
theorem B17525099 : Blo 810345 17525099 := bstep (se 1 (by rfl) ⟨13143824, by rfl⟩ : syracuseStep 17525099 = 26287649) B26287649
theorem B912127 : Blo 810345 912127 := bstep (se 1 (by rfl) ⟨684095, by rfl⟩ : syracuseStep 912127 = 1368191) B1368191
theorem B814111 : Blo 810345 814111 := bstep (se 1 (by rfl) ⟨610583, by rfl⟩ : syracuseStep 814111 = 1221167) B1221167
theorem B3468719 : Blo 810345 3468719 := bstep (se 1 (by rfl) ⟨2601539, by rfl⟩ : syracuseStep 3468719 = 5203079) B5203079
theorem B913351 : Blo 810345 913351 := bstep (se 1 (by rfl) ⟨685013, by rfl⟩ : syracuseStep 913351 = 1370027) B1370027
theorem B913855 : Blo 810345 913855 := bstep (se 1 (by rfl) ⟨685391, by rfl⟩ : syracuseStep 913855 = 1370783) B1370783
theorem B6582811 : Blo 810345 6582811 := bstep (se 1 (by rfl) ⟨4937108, by rfl⟩ : syracuseStep 6582811 = 9874217) B9874217
theorem B1539823 : Blo 810345 1539823 := bstep (se 1 (by rfl) ⟨1154867, by rfl⟩ : syracuseStep 1539823 = 2309735) B2309735
theorem B3473401 : Blo 810345 3473401 := bstep (se 2 (by rfl) ⟨1302525, by rfl⟩ : syracuseStep 3473401 = 2605051) B2605051
theorem B3081149 : Blo 810345 3081149 := bstep (se 3 (by rfl) ⟨577715, by rfl⟩ : syracuseStep 3081149 = 1155431) B1155431
theorem B1738111 : Blo 810345 1738111 := bstep (se 1 (by rfl) ⟨1303583, by rfl⟩ : syracuseStep 1738111 = 2607167) B2607167
theorem B3082151 : Blo 810345 3082151 := bstep (se 1 (by rfl) ⟨2311613, by rfl⟩ : syracuseStep 3082151 = 4623227) B4623227
theorem B4688039 : Blo 810345 4688039 := bstep (se 1 (by rfl) ⟨3516029, by rfl⟩ : syracuseStep 4688039 = 7032059) B7032059
theorem B1215815 : Blo 810345 1215815 := bstep (se 1 (by rfl) ⟨911861, by rfl⟩ : syracuseStep 1215815 = 1823723) B1823723
theorem B1215899 : Blo 810345 1215899 := bstep (se 1 (by rfl) ⟨911924, by rfl⟩ : syracuseStep 1215899 = 1823849) B1823849
theorem B1216169 : Blo 810345 1216169 := bstep (se 2 (by rfl) ⟨456063, by rfl⟩ : syracuseStep 1216169 = 912127) B912127
theorem B1216583 : Blo 810345 1216583 := bstep (se 1 (by rfl) ⟨912437, by rfl⟩ : syracuseStep 1216583 = 1824875) B1824875
theorem B1216991 : Blo 810345 1216991 := bstep (se 1 (by rfl) ⟨912743, by rfl⟩ : syracuseStep 1216991 = 1825487) B1825487
theorem B1217183 : Blo 810345 1217183 := bstep (se 1 (by rfl) ⟨912887, by rfl⟩ : syracuseStep 1217183 = 1825775) B1825775
theorem B1217801 : Blo 810345 1217801 := bstep (se 2 (by rfl) ⟨456675, by rfl⟩ : syracuseStep 1217801 = 913351) B913351
theorem B1218473 : Blo 810345 1218473 := bstep (se 2 (by rfl) ⟨456927, by rfl⟩ : syracuseStep 1218473 = 913855) B913855
theorem B3086495 : Blo 810345 3086495 := bstep (se 1 (by rfl) ⟨2314871, by rfl⟩ : syracuseStep 3086495 = 4629743) B4629743
theorem B1219007 : Blo 810345 1219007 := bstep (se 1 (by rfl) ⟨914255, by rfl⟩ : syracuseStep 1219007 = 1828511) B1828511
theorem B23435891 : Blo 810345 23435891 := bstep (se 1 (by rfl) ⟨17576918, by rfl⟩ : syracuseStep 23435891 = 35153837) B35153837
theorem B5842367 : Blo 810345 5842367 := bstep (se 1 (by rfl) ⟨4381775, by rfl⟩ : syracuseStep 5842367 = 8763551) B8763551
theorem B7809695 : Blo 810345 7809695 := bstep (se 1 (by rfl) ⟨5857271, by rfl⟩ : syracuseStep 7809695 = 11714543) B11714543
theorem B4631201 : Blo 810345 4631201 := bstep (se 2 (by rfl) ⟨1736700, by rfl⟩ : syracuseStep 4631201 = 3473401) B3473401
theorem B1158239 : Blo 810345 1158239 := bstep (se 1 (by rfl) ⟨868679, by rfl⟩ : syracuseStep 1158239 = 1737359) B1737359
theorem B35138771 : Blo 810345 35138771 := bstep (se 1 (by rfl) ⟨26354078, by rfl⟩ : syracuseStep 35138771 = 52708157) B52708157
theorem B4110587 : Blo 810345 4110587 := bstep (se 1 (by rfl) ⟨3082940, by rfl⟩ : syracuseStep 4110587 = 6165881) B6165881
theorem B1030639 : Blo 810345 1030639 := bstep (se 1 (by rfl) ⟨772979, by rfl⟩ : syracuseStep 1030639 = 1545959) B1545959
theorem B13188203 : Blo 810345 13188203 := bstep (se 1 (by rfl) ⟨9891152, by rfl⟩ : syracuseStep 13188203 = 19782305) B19782305
theorem B2735315 : Blo 810345 2735315 := bstep (se 1 (by rfl) ⟨2051486, by rfl⟩ : syracuseStep 2735315 = 4102973) B4102973
theorem B4112531 : Blo 810345 4112531 := bstep (se 1 (by rfl) ⟨3084398, by rfl⟩ : syracuseStep 4112531 = 6168797) B6168797
theorem B4997369 : Blo 810345 4997369 := bstep (se 2 (by rfl) ⟨1874013, by rfl⟩ : syracuseStep 4997369 = 3748027) B3748027
theorem B2933075 : Blo 810345 2933075 := bstep (se 1 (by rfl) ⟨2199806, by rfl⟩ : syracuseStep 2933075 = 4399613) B4399613
theorem B2737529 : Blo 810345 2737529 := bstep (se 2 (by rfl) ⟨1026573, by rfl⟩ : syracuseStep 2737529 = 2053147) B2053147
theorem B11683399 : Blo 810345 11683399 := bstep (se 1 (by rfl) ⟨8762549, by rfl⟩ : syracuseStep 11683399 = 17525099) B17525099
theorem B45139625 : Blo 810345 45139625 := bstep (se 2 (by rfl) ⟨16927359, by rfl⟩ : syracuseStep 45139625 = 33854719) B33854719
theorem B2312479 : Blo 810345 2312479 := bstep (se 1 (by rfl) ⟨1734359, by rfl⟩ : syracuseStep 2312479 = 3468719) B3468719
theorem B2738879 : Blo 810345 2738879 := bstep (se 1 (by rfl) ⟨2054159, by rfl⟩ : syracuseStep 2738879 = 4108319) B4108319
theorem B2053097 : Blo 810345 2053097 := bstep (se 2 (by rfl) ⟨769911, by rfl⟩ : syracuseStep 2053097 = 1539823) B1539823
theorem B11687327 : Blo 810345 11687327 := bstep (se 1 (by rfl) ⟨8765495, by rfl⟩ : syracuseStep 11687327 = 17530991) B17530991
theorem B9656111 : Blo 810345 9656111 := bstep (se 1 (by rfl) ⟨7242083, by rfl⟩ : syracuseStep 9656111 = 14484167) B14484167
theorem B1825145 : Blo 810345 1825145 := bstep (se 2 (by rfl) ⟨684429, by rfl⟩ : syracuseStep 1825145 = 1368859) B1368859
theorem B23419853 : Blo 810345 23419853 := bstep (se 3 (by rfl) ⟨4391222, by rfl⟩ : syracuseStep 23419853 = 8782445) B8782445
theorem B2743631 : Blo 810345 2743631 := bstep (se 1 (by rfl) ⟨2057723, by rfl⟩ : syracuseStep 2743631 = 4115447) B4115447
theorem B5856923 : Blo 810345 5856923 := bstep (se 1 (by rfl) ⟨4392692, by rfl⟩ : syracuseStep 5856923 = 8785385) B8785385
theorem B1369271 : Blo 810345 1369271 := bstep (se 1 (by rfl) ⟨1026953, by rfl⟩ : syracuseStep 1369271 = 2053907) B2053907
theorem B2745575 : Blo 810345 2745575 := bstep (se 1 (by rfl) ⟨2059181, by rfl⟩ : syracuseStep 2745575 = 4118363) B4118363
theorem B1828151 : Blo 810345 1828151 := bstep (se 1 (by rfl) ⟨1371113, by rfl⟩ : syracuseStep 1828151 = 2742227) B2742227
theorem B46982929 : Blo 810345 46982929 := bstep (se 2 (by rfl) ⟨17618598, by rfl⟩ : syracuseStep 46982929 = 35237197) B35237197
theorem B80210411 : Blo 810345 80210411 := bstep (se 1 (by rfl) ⟨60157808, by rfl⟩ : syracuseStep 80210411 = 120315617) B120315617
theorem B813679 : Blo 810345 813679 := bstep (se 1 (by rfl) ⟨610259, by rfl⟩ : syracuseStep 813679 = 1220519) B1220519
theorem B1370857 : Blo 810345 1370857 := bstep (se 2 (by rfl) ⟨514071, by rfl⟩ : syracuseStep 1370857 = 1028143) B1028143
theorem B8777081 : Blo 810345 8777081 := bstep (se 2 (by rfl) ⟨3291405, by rfl⟩ : syracuseStep 8777081 = 6582811) B6582811
theorem B13856831 : Blo 810345 13856831 := bstep (se 1 (by rfl) ⟨10392623, by rfl⟩ : syracuseStep 13856831 = 20785247) B20785247
theorem B9400873 : Blo 810345 9400873 := bstep (se 2 (by rfl) ⟨3525327, by rfl⟩ : syracuseStep 9400873 = 7050655) B7050655
theorem B3083305 : Blo 810345 3083305 := bstep (se 2 (by rfl) ⟨1156239, by rfl⟩ : syracuseStep 3083305 = 2312479) B2312479
theorem B1216763 : Blo 810345 1216763 := bstep (se 1 (by rfl) ⟨912572, by rfl⟩ : syracuseStep 1216763 = 1825145) B1825145
theorem B3904615 : Blo 810345 3904615 := bstep (se 1 (by rfl) ⟨2928461, by rfl⟩ : syracuseStep 3904615 = 5856923) B5856923
theorem B1218767 : Blo 810345 1218767 := bstep (se 1 (by rfl) ⟨914075, by rfl⟩ : syracuseStep 1218767 = 1828151) B1828151
theorem B3087467 : Blo 810345 3087467 := bstep (se 1 (by rfl) ⟨2315600, by rfl⟩ : syracuseStep 3087467 = 4631201) B4631201
theorem B3088637 : Blo 810345 3088637 := bstep (se 3 (by rfl) ⟨579119, by rfl⟩ : syracuseStep 3088637 = 1158239) B1158239
theorem B8792135 : Blo 810345 8792135 := bstep (se 1 (by rfl) ⟨6594101, by rfl⟩ : syracuseStep 8792135 = 13188203) B13188203
theorem B30093083 : Blo 810345 30093083 := bstep (se 1 (by rfl) ⟨22569812, by rfl⟩ : syracuseStep 30093083 = 45139625) B45139625
theorem B3125359 : Blo 810345 3125359 := bstep (se 1 (by rfl) ⟨2344019, by rfl⟩ : syracuseStep 3125359 = 4688039) B4688039
theorem B15577865 : Blo 810345 15577865 := bstep (se 2 (by rfl) ⟨5841699, by rfl⟩ : syracuseStep 15577865 = 11683399) B11683399
theorem B6437407 : Blo 810345 6437407 := bstep (se 1 (by rfl) ⟨4828055, by rfl⟩ : syracuseStep 6437407 = 9656111) B9656111
theorem B15613235 : Blo 810345 15613235 := bstep (se 1 (by rfl) ⟨11709926, by rfl⟩ : syracuseStep 15613235 = 23419853) B23419853
theorem B12534497 : Blo 810345 12534497 := bstep (se 2 (by rfl) ⟨4700436, by rfl⟩ : syracuseStep 12534497 = 9400873) B9400873
theorem B5851387 : Blo 810345 5851387 := bstep (se 1 (by rfl) ⟨4388540, by rfl⟩ : syracuseStep 5851387 = 8777081) B8777081
theorem B2740391 : Blo 810345 2740391 := bstep (se 1 (by rfl) ⟨2055293, by rfl⟩ : syracuseStep 2740391 = 4110587) B4110587
theorem B1823543 : Blo 810345 1823543 := bstep (se 1 (by rfl) ⟨1367657, by rfl⟩ : syracuseStep 1823543 = 2735315) B2735315
theorem B2741687 : Blo 810345 2741687 := bstep (se 1 (by rfl) ⟨2056265, by rfl⟩ : syracuseStep 2741687 = 4112531) B4112531
theorem B3331579 : Blo 810345 3331579 := bstep (se 1 (by rfl) ⟨2498684, by rfl⟩ : syracuseStep 3331579 = 4997369) B4997369
theorem B1955383 : Blo 810345 1955383 := bstep (se 1 (by rfl) ⟨1466537, by rfl⟩ : syracuseStep 1955383 = 2933075) B2933075
theorem B2054099 : Blo 810345 2054099 := bstep (se 1 (by rfl) ⟨1540574, by rfl⟩ : syracuseStep 2054099 = 3081149) B3081149
theorem B1825019 : Blo 810345 1825019 := bstep (se 1 (by rfl) ⟨1368764, by rfl⟩ : syracuseStep 1825019 = 2737529) B2737529
theorem B2054767 : Blo 810345 2054767 := bstep (se 1 (by rfl) ⟨1541075, by rfl⟩ : syracuseStep 2054767 = 3082151) B3082151
theorem B1825919 : Blo 810345 1825919 := bstep (se 1 (by rfl) ⟨1369439, by rfl⟩ : syracuseStep 1825919 = 2738879) B2738879
theorem B2317481 : Blo 810345 2317481 := bstep (se 2 (by rfl) ⟨869055, by rfl⟩ : syracuseStep 2317481 = 1738111) B1738111
theorem B810543 : Blo 810345 810543 := bstep (se 1 (by rfl) ⟨607907, by rfl⟩ : syracuseStep 810543 = 1215815) B1215815
theorem B810599 : Blo 810345 810599 := bstep (se 1 (by rfl) ⟨607949, by rfl⟩ : syracuseStep 810599 = 1215899) B1215899
theorem B62643905 : Blo 810345 62643905 := bstep (se 2 (by rfl) ⟨23491464, by rfl⟩ : syracuseStep 62643905 = 46982929) B46982929
theorem B810779 : Blo 810345 810779 := bstep (se 1 (by rfl) ⟨608084, by rfl⟩ : syracuseStep 810779 = 1216169) B1216169
theorem B811055 : Blo 810345 811055 := bstep (se 1 (by rfl) ⟨608291, by rfl⟩ : syracuseStep 811055 = 1216583) B1216583
theorem B811327 : Blo 810345 811327 := bstep (se 1 (by rfl) ⟨608495, by rfl⟩ : syracuseStep 811327 = 1216991) B1216991
theorem B811455 : Blo 810345 811455 := bstep (se 1 (by rfl) ⟨608591, by rfl⟩ : syracuseStep 811455 = 1217183) B1217183
theorem B1368731 : Blo 810345 1368731 := bstep (se 1 (by rfl) ⟨1026548, by rfl⟩ : syracuseStep 1368731 = 2053097) B2053097
theorem B811867 : Blo 810345 811867 := bstep (se 1 (by rfl) ⟨608900, by rfl⟩ : syracuseStep 811867 = 1217801) B1217801
theorem B7791551 : Blo 810345 7791551 := bstep (se 1 (by rfl) ⟨5843663, by rfl⟩ : syracuseStep 7791551 = 11687327) B11687327
theorem B1827809 : Blo 810345 1827809 := bstep (se 2 (by rfl) ⟨685428, by rfl⟩ : syracuseStep 1827809 = 1370857) B1370857
theorem B812315 : Blo 810345 812315 := bstep (se 1 (by rfl) ⟨609236, by rfl⟩ : syracuseStep 812315 = 1218473) B1218473
theorem B2057663 : Blo 810345 2057663 := bstep (se 1 (by rfl) ⟨1543247, by rfl⟩ : syracuseStep 2057663 = 3086495) B3086495
theorem B812671 : Blo 810345 812671 := bstep (se 1 (by rfl) ⟨609503, by rfl⟩ : syracuseStep 812671 = 1219007) B1219007
theorem B15623927 : Blo 810345 15623927 := bstep (se 1 (by rfl) ⟨11717945, by rfl⟩ : syracuseStep 15623927 = 23435891) B23435891
theorem B1829087 : Blo 810345 1829087 := bstep (se 1 (by rfl) ⟨1371815, by rfl⟩ : syracuseStep 1829087 = 2743631) B2743631
theorem B912847 : Blo 810345 912847 := bstep (se 1 (by rfl) ⟨684635, by rfl⟩ : syracuseStep 912847 = 1369271) B1369271
theorem B1830383 : Blo 810345 1830383 := bstep (se 1 (by rfl) ⟨1372787, by rfl⟩ : syracuseStep 1830383 = 2745575) B2745575
theorem B3894911 : Blo 810345 3894911 := bstep (se 1 (by rfl) ⟨2921183, by rfl⟩ : syracuseStep 3894911 = 5842367) B5842367
theorem B53473607 : Blo 810345 53473607 := bstep (se 1 (by rfl) ⟨40105205, by rfl⟩ : syracuseStep 53473607 = 80210411) B80210411
theorem B5206463 : Blo 810345 5206463 := bstep (se 1 (by rfl) ⟨3904847, by rfl⟩ : syracuseStep 5206463 = 7809695) B7809695
theorem B23425847 : Blo 810345 23425847 := bstep (se 1 (by rfl) ⟨17569385, by rfl⟩ : syracuseStep 23425847 = 35138771) B35138771
theorem B9237887 : Blo 810345 9237887 := bstep (se 1 (by rfl) ⟨6928415, by rfl⟩ : syracuseStep 9237887 = 13856831) B13856831
theorem B1374185 : Blo 810345 1374185 := bstep (se 2 (by rfl) ⟨515319, by rfl⟩ : syracuseStep 1374185 = 1030639) B1030639
theorem B8356331 : Blo 810345 8356331 := bstep (se 1 (by rfl) ⟨6267248, by rfl⟩ : syracuseStep 8356331 = 12534497) B12534497
theorem B7801849 : Blo 810345 7801849 := bstep (se 2 (by rfl) ⟨2925693, by rfl⟩ : syracuseStep 7801849 = 5851387) B5851387
theorem B1215695 : Blo 810345 1215695 := bstep (se 1 (by rfl) ⟨911771, by rfl⟩ : syracuseStep 1215695 = 1823543) B1823543
theorem B1216679 : Blo 810345 1216679 := bstep (se 1 (by rfl) ⟨912509, by rfl⟩ : syracuseStep 1216679 = 1825019) B1825019
theorem B1217129 : Blo 810345 1217129 := bstep (se 2 (by rfl) ⟨456423, by rfl⟩ : syracuseStep 1217129 = 912847) B912847
theorem B1217279 : Blo 810345 1217279 := bstep (se 1 (by rfl) ⟨912959, by rfl⟩ : syracuseStep 1217279 = 1825919) B1825919
theorem B1544987 : Blo 810345 1544987 := bstep (se 1 (by rfl) ⟨1158740, by rfl⟩ : syracuseStep 1544987 = 2317481) B2317481
theorem B4167145 : Blo 810345 4167145 := bstep (se 2 (by rfl) ⟨1562679, by rfl⟩ : syracuseStep 4167145 = 3125359) B3125359
theorem B1218539 : Blo 810345 1218539 := bstep (se 1 (by rfl) ⟨913904, by rfl⟩ : syracuseStep 1218539 = 1827809) B1827809
theorem B1219391 : Blo 810345 1219391 := bstep (se 1 (by rfl) ⟨914543, by rfl⟩ : syracuseStep 1219391 = 1829087) B1829087
theorem B1220255 : Blo 810345 1220255 := bstep (se 1 (by rfl) ⟨915191, by rfl⟩ : syracuseStep 1220255 = 1830383) B1830383
theorem B2596607 : Blo 810345 2596607 := bstep (se 1 (by rfl) ⟨1947455, by rfl⟩ : syracuseStep 2596607 = 3894911) B3894911
theorem B20062055 : Blo 810345 20062055 := bstep (se 1 (by rfl) ⟨15046541, by rfl⟩ : syracuseStep 20062055 = 30093083) B30093083
theorem B10428709 : Blo 810345 10428709 := bstep (se 4 (by rfl) ⟨977691, by rfl⟩ : syracuseStep 10428709 = 1955383) B1955383
theorem B4111073 : Blo 810345 4111073 := bstep (se 2 (by rfl) ⟨1541652, by rfl⟩ : syracuseStep 4111073 = 3083305) B3083305
theorem B41762603 : Blo 810345 41762603 := bstep (se 1 (by rfl) ⟨31321952, by rfl⟩ : syracuseStep 41762603 = 62643905) B62643905
theorem B20824613 : Blo 810345 20824613 := bstep (se 4 (by rfl) ⟨1952307, by rfl⟩ : syracuseStep 20824613 = 3904615) B3904615
theorem B5194367 : Blo 810345 5194367 := bstep (se 1 (by rfl) ⟨3895775, by rfl⟩ : syracuseStep 5194367 = 7791551) B7791551
theorem B4442105 : Blo 810345 4442105 := bstep (se 2 (by rfl) ⟨1665789, by rfl⟩ : syracuseStep 4442105 = 3331579) B3331579
theorem B15617231 : Blo 810345 15617231 := bstep (se 1 (by rfl) ⟨11712923, by rfl⟩ : syracuseStep 15617231 = 23425847) B23425847
theorem B2739689 : Blo 810345 2739689 := bstep (se 2 (by rfl) ⟨1027383, by rfl⟩ : syracuseStep 2739689 = 2054767) B2054767
theorem B10408823 : Blo 810345 10408823 := bstep (se 1 (by rfl) ⟨7806617, by rfl⟩ : syracuseStep 10408823 = 15613235) B15613235
theorem B1826927 : Blo 810345 1826927 := bstep (se 1 (by rfl) ⟨1370195, by rfl⟩ : syracuseStep 1826927 = 2740391) B2740391
theorem B811175 : Blo 810345 811175 := bstep (se 1 (by rfl) ⟨608381, by rfl⟩ : syracuseStep 811175 = 1216763) B1216763
theorem B1827791 : Blo 810345 1827791 := bstep (se 1 (by rfl) ⟨1370843, by rfl⟩ : syracuseStep 1827791 = 2741687) B2741687
theorem B1369399 : Blo 810345 1369399 := bstep (se 1 (by rfl) ⟨1027049, by rfl⟩ : syracuseStep 1369399 = 2054099) B2054099
theorem B812511 : Blo 810345 812511 := bstep (se 1 (by rfl) ⟨609383, by rfl⟩ : syracuseStep 812511 = 1218767) B1218767
theorem B2058311 : Blo 810345 2058311 := bstep (se 1 (by rfl) ⟨1543733, by rfl⟩ : syracuseStep 2058311 = 3087467) B3087467
theorem B2059091 : Blo 810345 2059091 := bstep (se 1 (by rfl) ⟨1544318, by rfl⟩ : syracuseStep 2059091 = 3088637) B3088637
theorem B912487 : Blo 810345 912487 := bstep (se 1 (by rfl) ⟨684365, by rfl⟩ : syracuseStep 912487 = 1368731) B1368731
theorem B1371775 : Blo 810345 1371775 := bstep (se 1 (by rfl) ⟨1028831, by rfl⟩ : syracuseStep 1371775 = 2057663) B2057663
theorem B10415951 : Blo 810345 10415951 := bstep (se 1 (by rfl) ⟨7811963, by rfl⟩ : syracuseStep 10415951 = 15623927) B15623927
theorem B5861423 : Blo 810345 5861423 := bstep (se 1 (by rfl) ⟨4396067, by rfl⟩ : syracuseStep 5861423 = 8792135) B8792135
theorem B35649071 : Blo 810345 35649071 := bstep (se 1 (by rfl) ⟨26736803, by rfl⟩ : syracuseStep 35649071 = 53473607) B53473607
theorem B3470975 : Blo 810345 3470975 := bstep (se 1 (by rfl) ⟨2603231, by rfl⟩ : syracuseStep 3470975 = 5206463) B5206463
theorem B10385243 : Blo 810345 10385243 := bstep (se 1 (by rfl) ⟨7788932, by rfl⟩ : syracuseStep 10385243 = 15577865) B15577865
theorem B8583209 : Blo 810345 8583209 := bstep (se 2 (by rfl) ⟨3218703, by rfl⟩ : syracuseStep 8583209 = 6437407) B6437407
theorem B6158591 : Blo 810345 6158591 := bstep (se 1 (by rfl) ⟨4618943, by rfl⟩ : syracuseStep 6158591 = 9237887) B9237887
theorem B916123 : Blo 810345 916123 := bstep (se 1 (by rfl) ⟨687092, by rfl⟩ : syracuseStep 916123 = 1374185) B1374185
theorem B22283549 : Blo 810345 22283549 := bstep (se 3 (by rfl) ⟨4178165, by rfl⟩ : syracuseStep 22283549 = 8356331) B8356331
theorem B1216649 : Blo 810345 1216649 := bstep (se 2 (by rfl) ⟨456243, by rfl⟩ : syracuseStep 1216649 = 912487) B912487
theorem B13374703 : Blo 810345 13374703 := bstep (se 1 (by rfl) ⟨10031027, by rfl⟩ : syracuseStep 13374703 = 20062055) B20062055
theorem B1217951 : Blo 810345 1217951 := bstep (se 1 (by rfl) ⟨913463, by rfl⟩ : syracuseStep 1217951 = 1826927) B1826927
theorem B1218527 : Blo 810345 1218527 := bstep (se 1 (by rfl) ⟨913895, by rfl⟩ : syracuseStep 1218527 = 1827791) B1827791
theorem B22224773 : Blo 810345 22224773 := bstep (se 4 (by rfl) ⟨2083572, by rfl⟩ : syracuseStep 22224773 = 4167145) B4167145
theorem B3907615 : Blo 810345 3907615 := bstep (se 1 (by rfl) ⟨2930711, by rfl⟩ : syracuseStep 3907615 = 5861423) B5861423
theorem B1221497 : Blo 810345 1221497 := bstep (se 2 (by rfl) ⟨458061, by rfl⟩ : syracuseStep 1221497 = 916123) B916123
theorem B23766047 : Blo 810345 23766047 := bstep (se 1 (by rfl) ⟨17824535, by rfl⟩ : syracuseStep 23766047 = 35649071) B35649071
theorem B6923495 : Blo 810345 6923495 := bstep (se 1 (by rfl) ⟨5192621, by rfl⟩ : syracuseStep 6923495 = 10385243) B10385243
theorem B4105727 : Blo 810345 4105727 := bstep (se 1 (by rfl) ⟨3079295, by rfl⟩ : syracuseStep 4105727 = 6158591) B6158591
theorem B13904945 : Blo 810345 13904945 := bstep (se 2 (by rfl) ⟨5214354, by rfl⟩ : syracuseStep 13904945 = 10428709) B10428709
theorem B2961403 : Blo 810345 2961403 := bstep (se 1 (by rfl) ⟨2221052, by rfl⟩ : syracuseStep 2961403 = 4442105) B4442105
theorem B1029991 : Blo 810345 1029991 := bstep (se 1 (by rfl) ⟨772493, by rfl⟩ : syracuseStep 1029991 = 1544987) B1544987
theorem B10402465 : Blo 810345 10402465 := bstep (se 2 (by rfl) ⟨3900924, by rfl⟩ : syracuseStep 10402465 = 7801849) B7801849
theorem B2313983 : Blo 810345 2313983 := bstep (se 1 (by rfl) ⟨1735487, by rfl⟩ : syracuseStep 2313983 = 3470975) B3470975
theorem B5722139 : Blo 810345 5722139 := bstep (se 1 (by rfl) ⟨4291604, by rfl⟩ : syracuseStep 5722139 = 8583209) B8583209
theorem B2740715 : Blo 810345 2740715 := bstep (se 1 (by rfl) ⟨2055536, by rfl⟩ : syracuseStep 2740715 = 4111073) B4111073
theorem B27841735 : Blo 810345 27841735 := bstep (se 1 (by rfl) ⟨20881301, by rfl⟩ : syracuseStep 27841735 = 41762603) B41762603
theorem B13883075 : Blo 810345 13883075 := bstep (se 1 (by rfl) ⟨10412306, by rfl⟩ : syracuseStep 13883075 = 20824613) B20824613
theorem B3462911 : Blo 810345 3462911 := bstep (se 1 (by rfl) ⟨2597183, by rfl⟩ : syracuseStep 3462911 = 5194367) B5194367
theorem B1825865 : Blo 810345 1825865 := bstep (se 2 (by rfl) ⟨684699, by rfl⟩ : syracuseStep 1825865 = 1369399) B1369399
theorem B810463 : Blo 810345 810463 := bstep (se 1 (by rfl) ⟨607847, by rfl⟩ : syracuseStep 810463 = 1215695) B1215695
theorem B10411487 : Blo 810345 10411487 := bstep (se 1 (by rfl) ⟨7808615, by rfl⟩ : syracuseStep 10411487 = 15617231) B15617231
theorem B1826459 : Blo 810345 1826459 := bstep (se 1 (by rfl) ⟨1369844, by rfl⟩ : syracuseStep 1826459 = 2739689) B2739689
theorem B811119 : Blo 810345 811119 := bstep (se 1 (by rfl) ⟨608339, by rfl⟩ : syracuseStep 811119 = 1216679) B1216679
theorem B811419 : Blo 810345 811419 := bstep (se 1 (by rfl) ⟨608564, by rfl⟩ : syracuseStep 811419 = 1217129) B1217129
theorem B811519 : Blo 810345 811519 := bstep (se 1 (by rfl) ⟨608639, by rfl⟩ : syracuseStep 811519 = 1217279) B1217279
theorem B6939215 : Blo 810345 6939215 := bstep (se 1 (by rfl) ⟨5204411, by rfl⟩ : syracuseStep 6939215 = 10408823) B10408823
theorem B812359 : Blo 810345 812359 := bstep (se 1 (by rfl) ⟨609269, by rfl⟩ : syracuseStep 812359 = 1218539) B1218539
theorem B812927 : Blo 810345 812927 := bstep (se 1 (by rfl) ⟨609695, by rfl⟩ : syracuseStep 812927 = 1219391) B1219391
theorem B1829033 : Blo 810345 1829033 := bstep (se 2 (by rfl) ⟨685887, by rfl⟩ : syracuseStep 1829033 = 1371775) B1371775
theorem B813503 : Blo 810345 813503 := bstep (se 1 (by rfl) ⟨610127, by rfl⟩ : syracuseStep 813503 = 1220255) B1220255
theorem B1731071 : Blo 810345 1731071 := bstep (se 1 (by rfl) ⟨1298303, by rfl⟩ : syracuseStep 1731071 = 2596607) B2596607
theorem B1372207 : Blo 810345 1372207 := bstep (se 1 (by rfl) ⟨1029155, by rfl⟩ : syracuseStep 1372207 = 2058311) B2058311
theorem B1372727 : Blo 810345 1372727 := bstep (se 1 (by rfl) ⟨1029545, by rfl⟩ : syracuseStep 1372727 = 2059091) B2059091
theorem B6943967 : Blo 810345 6943967 := bstep (se 1 (by rfl) ⟨5207975, by rfl⟩ : syracuseStep 6943967 = 10415951) B10415951
theorem B5210153 : Blo 810345 5210153 := bstep (se 2 (by rfl) ⟨1953807, by rfl⟩ : syracuseStep 5210153 = 3907615) B3907615
theorem B1542655 : Blo 810345 1542655 := bstep (se 1 (by rfl) ⟨1156991, by rfl⟩ : syracuseStep 1542655 = 2313983) B2313983
theorem B1217243 : Blo 810345 1217243 := bstep (se 1 (by rfl) ⟨912932, by rfl⟩ : syracuseStep 1217243 = 1825865) B1825865
theorem B1217639 : Blo 810345 1217639 := bstep (se 1 (by rfl) ⟨913229, by rfl⟩ : syracuseStep 1217639 = 1826459) B1826459
theorem B14816515 : Blo 810345 14816515 := bstep (se 1 (by rfl) ⟨11112386, by rfl⟩ : syracuseStep 14816515 = 22224773) B22224773
theorem B4626143 : Blo 810345 4626143 := bstep (se 1 (by rfl) ⟨3469607, by rfl⟩ : syracuseStep 4626143 = 6939215) B6939215
theorem B1219355 : Blo 810345 1219355 := bstep (se 1 (by rfl) ⟨914516, by rfl⟩ : syracuseStep 1219355 = 1829033) B1829033
theorem B4629311 : Blo 810345 4629311 := bstep (se 1 (by rfl) ⟨3471983, by rfl⟩ : syracuseStep 4629311 = 6943967) B6943967
theorem B13869953 : Blo 810345 13869953 := bstep (se 2 (by rfl) ⟨5201232, by rfl⟩ : syracuseStep 13869953 = 10402465) B10402465
theorem B14855699 : Blo 810345 14855699 := bstep (se 1 (by rfl) ⟨11141774, by rfl⟩ : syracuseStep 14855699 = 22283549) B22283549
theorem B3814759 : Blo 810345 3814759 := bstep (se 1 (by rfl) ⟨2861069, by rfl⟩ : syracuseStep 3814759 = 5722139) B5722139
theorem B9255383 : Blo 810345 9255383 := bstep (se 1 (by rfl) ⟨6941537, by rfl⟩ : syracuseStep 9255383 = 13883075) B13883075
theorem B2308607 : Blo 810345 2308607 := bstep (se 1 (by rfl) ⟨1731455, by rfl⟩ : syracuseStep 2308607 = 3462911) B3462911
theorem B15844031 : Blo 810345 15844031 := bstep (se 1 (by rfl) ⟨11883023, by rfl⟩ : syracuseStep 15844031 = 23766047) B23766047
theorem B2737151 : Blo 810345 2737151 := bstep (se 1 (by rfl) ⟨2052863, by rfl⟩ : syracuseStep 2737151 = 4105727) B4105727
theorem B811099 : Blo 810345 811099 := bstep (se 1 (by rfl) ⟨608324, by rfl⟩ : syracuseStep 811099 = 1216649) B1216649
theorem B1827143 : Blo 810345 1827143 := bstep (se 1 (by rfl) ⟨1370357, by rfl⟩ : syracuseStep 1827143 = 2740715) B2740715
theorem B811967 : Blo 810345 811967 := bstep (se 1 (by rfl) ⟨608975, by rfl⟩ : syracuseStep 811967 = 1217951) B1217951
theorem B812351 : Blo 810345 812351 := bstep (se 1 (by rfl) ⟨609263, by rfl⟩ : syracuseStep 812351 = 1218527) B1218527
theorem B6940991 : Blo 810345 6940991 := bstep (se 1 (by rfl) ⟨5205743, by rfl⟩ : syracuseStep 6940991 = 10411487) B10411487
theorem B1829609 : Blo 810345 1829609 := bstep (se 2 (by rfl) ⟨686103, by rfl⟩ : syracuseStep 1829609 = 1372207) B1372207
theorem B814331 : Blo 810345 814331 := bstep (se 1 (by rfl) ⟨610748, by rfl⟩ : syracuseStep 814331 = 1221497) B1221497
theorem B4615663 : Blo 810345 4615663 := bstep (se 1 (by rfl) ⟨3461747, by rfl⟩ : syracuseStep 4615663 = 6923495) B6923495
theorem B71331749 : Blo 810345 71331749 := bstep (se 4 (by rfl) ⟨6687351, by rfl⟩ : syracuseStep 71331749 = 13374703) B13374703
theorem B4616189 : Blo 810345 4616189 := bstep (se 3 (by rfl) ⟨865535, by rfl⟩ : syracuseStep 4616189 = 1731071) B1731071
theorem B37122313 : Blo 810345 37122313 := bstep (se 2 (by rfl) ⟨13920867, by rfl⟩ : syracuseStep 37122313 = 27841735) B27841735
theorem B9269963 : Blo 810345 9269963 := bstep (se 1 (by rfl) ⟨6952472, by rfl⟩ : syracuseStep 9269963 = 13904945) B13904945
theorem B1373321 : Blo 810345 1373321 := bstep (se 2 (by rfl) ⟨514995, by rfl⟩ : syracuseStep 1373321 = 1029991) B1029991
theorem B915151 : Blo 810345 915151 := bstep (se 1 (by rfl) ⟨686363, by rfl⟩ : syracuseStep 915151 = 1372727) B1372727
theorem B15794149 : Blo 810345 15794149 := bstep (se 4 (by rfl) ⟨1480701, by rfl⟩ : syracuseStep 15794149 = 2961403) B2961403
theorem B3473435 : Blo 810345 3473435 := bstep (se 1 (by rfl) ⟨2605076, by rfl⟩ : syracuseStep 3473435 = 5210153) B5210153
theorem B3084095 : Blo 810345 3084095 := bstep (se 1 (by rfl) ⟨2313071, by rfl⟩ : syracuseStep 3084095 = 4626143) B4626143
theorem B1218095 : Blo 810345 1218095 := bstep (se 1 (by rfl) ⟨913571, by rfl⟩ : syracuseStep 1218095 = 1827143) B1827143
theorem B3086207 : Blo 810345 3086207 := bstep (se 1 (by rfl) ⟨2314655, by rfl⟩ : syracuseStep 3086207 = 4629311) B4629311
theorem B9246635 : Blo 810345 9246635 := bstep (se 1 (by rfl) ⟨6934976, by rfl⟩ : syracuseStep 9246635 = 13869953) B13869953
theorem B4627327 : Blo 810345 4627327 := bstep (se 1 (by rfl) ⟨3470495, by rfl⟩ : syracuseStep 4627327 = 6940991) B6940991
theorem B1219739 : Blo 810345 1219739 := bstep (se 1 (by rfl) ⟨914804, by rfl⟩ : syracuseStep 1219739 = 1829609) B1829609
theorem B1220201 : Blo 810345 1220201 := bstep (se 2 (by rfl) ⟨457575, by rfl⟩ : syracuseStep 1220201 = 915151) B915151
theorem B9903799 : Blo 810345 9903799 := bstep (se 1 (by rfl) ⟨7427849, by rfl⟩ : syracuseStep 9903799 = 14855699) B14855699
theorem B47554499 : Blo 810345 47554499 := bstep (se 1 (by rfl) ⟨35665874, by rfl⟩ : syracuseStep 47554499 = 71331749) B71331749
theorem B6170255 : Blo 810345 6170255 := bstep (se 1 (by rfl) ⟨4627691, by rfl⟩ : syracuseStep 6170255 = 9255383) B9255383
theorem B10562687 : Blo 810345 10562687 := bstep (se 1 (by rfl) ⟨7922015, by rfl⟩ : syracuseStep 10562687 = 15844031) B15844031
theorem B49496417 : Blo 810345 49496417 := bstep (se 2 (by rfl) ⟨18561156, by rfl⟩ : syracuseStep 49496417 = 37122313) B37122313
theorem B6179975 : Blo 810345 6179975 := bstep (se 1 (by rfl) ⟨4634981, by rfl⟩ : syracuseStep 6179975 = 9269963) B9269963
theorem B21058865 : Blo 810345 21058865 := bstep (se 2 (by rfl) ⟨7897074, by rfl⟩ : syracuseStep 21058865 = 15794149) B15794149
theorem B1824767 : Blo 810345 1824767 := bstep (se 1 (by rfl) ⟨1368575, by rfl⟩ : syracuseStep 1824767 = 2737151) B2737151
theorem B811495 : Blo 810345 811495 := bstep (se 1 (by rfl) ⟨608621, by rfl⟩ : syracuseStep 811495 = 1217243) B1217243
theorem B2056873 : Blo 810345 2056873 := bstep (se 2 (by rfl) ⟨771327, by rfl⟩ : syracuseStep 2056873 = 1542655) B1542655
theorem B811759 : Blo 810345 811759 := bstep (se 1 (by rfl) ⟨608819, by rfl⟩ : syracuseStep 811759 = 1217639) B1217639
theorem B812903 : Blo 810345 812903 := bstep (se 1 (by rfl) ⟨609677, by rfl⟩ : syracuseStep 812903 = 1219355) B1219355
theorem B6154217 : Blo 810345 6154217 := bstep (se 2 (by rfl) ⟨2307831, by rfl⟩ : syracuseStep 6154217 = 4615663) B4615663
theorem B19755353 : Blo 810345 19755353 := bstep (se 2 (by rfl) ⟨7408257, by rfl⟩ : syracuseStep 19755353 = 14816515) B14816515
theorem B20345381 : Blo 810345 20345381 := bstep (se 4 (by rfl) ⟨1907379, by rfl⟩ : syracuseStep 20345381 = 3814759) B3814759
theorem B3077459 : Blo 810345 3077459 := bstep (se 1 (by rfl) ⟨2308094, by rfl⟩ : syracuseStep 3077459 = 4616189) B4616189
theorem B915547 : Blo 810345 915547 := bstep (se 1 (by rfl) ⟨686660, by rfl⟩ : syracuseStep 915547 = 1373321) B1373321
theorem B1539071 : Blo 810345 1539071 := bstep (se 1 (by rfl) ⟨1154303, by rfl⟩ : syracuseStep 1539071 = 2308607) B2308607
theorem B32997611 : Blo 810345 32997611 := bstep (se 1 (by rfl) ⟨24748208, by rfl⟩ : syracuseStep 32997611 = 49496417) B49496417
theorem B6164423 : Blo 810345 6164423 := bstep (se 1 (by rfl) ⟨4623317, by rfl⟩ : syracuseStep 6164423 = 9246635) B9246635
theorem B1216511 : Blo 810345 1216511 := bstep (se 1 (by rfl) ⟨912383, by rfl⟩ : syracuseStep 1216511 = 1824767) B1824767
theorem B4102811 : Blo 810345 4102811 := bstep (se 1 (by rfl) ⟨3077108, by rfl⟩ : syracuseStep 4102811 = 6154217) B6154217
theorem B1220729 : Blo 810345 1220729 := bstep (se 2 (by rfl) ⟨457773, by rfl⟩ : syracuseStep 1220729 = 915547) B915547
theorem B6169769 : Blo 810345 6169769 := bstep (se 2 (by rfl) ⟨2313663, by rfl⟩ : syracuseStep 6169769 = 4627327) B4627327
theorem B1026047 : Blo 810345 1026047 := bstep (se 1 (by rfl) ⟨769535, by rfl⟩ : syracuseStep 1026047 = 1539071) B1539071
theorem B14039243 : Blo 810345 14039243 := bstep (se 1 (by rfl) ⟨10529432, by rfl⟩ : syracuseStep 14039243 = 21058865) B21058865
theorem B31702999 : Blo 810345 31702999 := bstep (se 1 (by rfl) ⟨23777249, by rfl⟩ : syracuseStep 31702999 = 47554499) B47554499
theorem B4113503 : Blo 810345 4113503 := bstep (se 1 (by rfl) ⟨3085127, by rfl⟩ : syracuseStep 4113503 = 6170255) B6170255
theorem B2051639 : Blo 810345 2051639 := bstep (se 1 (by rfl) ⟨1538729, by rfl⟩ : syracuseStep 2051639 = 3077459) B3077459
theorem B2315623 : Blo 810345 2315623 := bstep (se 1 (by rfl) ⟨1736717, by rfl⟩ : syracuseStep 2315623 = 3473435) B3473435
theorem B2742497 : Blo 810345 2742497 := bstep (se 2 (by rfl) ⟨1028436, by rfl⟩ : syracuseStep 2742497 = 2056873) B2056873
theorem B4119983 : Blo 810345 4119983 := bstep (se 1 (by rfl) ⟨3089987, by rfl⟩ : syracuseStep 4119983 = 6179975) B6179975
theorem B2056063 : Blo 810345 2056063 := bstep (se 1 (by rfl) ⟨1542047, by rfl⟩ : syracuseStep 2056063 = 3084095) B3084095
theorem B812063 : Blo 810345 812063 := bstep (se 1 (by rfl) ⟨609047, by rfl⟩ : syracuseStep 812063 = 1218095) B1218095
theorem B2057471 : Blo 810345 2057471 := bstep (se 1 (by rfl) ⟨1543103, by rfl⟩ : syracuseStep 2057471 = 3086207) B3086207
theorem B813159 : Blo 810345 813159 := bstep (se 1 (by rfl) ⟨609869, by rfl⟩ : syracuseStep 813159 = 1219739) B1219739
theorem B813467 : Blo 810345 813467 := bstep (se 1 (by rfl) ⟨610100, by rfl⟩ : syracuseStep 813467 = 1220201) B1220201
theorem B7041791 : Blo 810345 7041791 := bstep (se 1 (by rfl) ⟨5281343, by rfl⟩ : syracuseStep 7041791 = 10562687) B10562687
theorem B13170235 : Blo 810345 13170235 := bstep (se 1 (by rfl) ⟨9877676, by rfl⟩ : syracuseStep 13170235 = 19755353) B19755353
theorem B13563587 : Blo 810345 13563587 := bstep (se 1 (by rfl) ⟨10172690, by rfl⟩ : syracuseStep 13563587 = 20345381) B20345381
theorem B13205065 : Blo 810345 13205065 := bstep (se 2 (by rfl) ⟨4951899, by rfl⟩ : syracuseStep 13205065 = 9903799) B9903799
theorem B3087497 : Blo 810345 3087497 := bstep (se 2 (by rfl) ⟨1157811, by rfl⟩ : syracuseStep 3087497 = 2315623) B2315623
theorem B4694527 : Blo 810345 4694527 := bstep (se 1 (by rfl) ⟨3520895, by rfl⟩ : syracuseStep 4694527 = 7041791) B7041791
theorem B17606753 : Blo 810345 17606753 := bstep (se 2 (by rfl) ⟨6602532, by rfl⟩ : syracuseStep 17606753 = 13205065) B13205065
theorem B21998407 : Blo 810345 21998407 := bstep (se 1 (by rfl) ⟨16498805, by rfl⟩ : syracuseStep 21998407 = 32997611) B32997611
theorem B4109615 : Blo 810345 4109615 := bstep (se 1 (by rfl) ⟨3082211, by rfl⟩ : syracuseStep 4109615 = 6164423) B6164423
theorem B2735207 : Blo 810345 2735207 := bstep (se 1 (by rfl) ⟨2051405, by rfl⟩ : syracuseStep 2735207 = 4102811) B4102811
theorem B2736125 : Blo 810345 2736125 := bstep (se 3 (by rfl) ⟨513023, by rfl⟩ : syracuseStep 2736125 = 1026047) B1026047
theorem B4113179 : Blo 810345 4113179 := bstep (se 1 (by rfl) ⟨3084884, by rfl⟩ : syracuseStep 4113179 = 6169769) B6169769
theorem B9359495 : Blo 810345 9359495 := bstep (se 1 (by rfl) ⟨7019621, by rfl⟩ : syracuseStep 9359495 = 14039243) B14039243
theorem B2741417 : Blo 810345 2741417 := bstep (se 2 (by rfl) ⟨1028031, by rfl⟩ : syracuseStep 2741417 = 2056063) B2056063
theorem B2742335 : Blo 810345 2742335 := bstep (se 1 (by rfl) ⟨2056751, by rfl⟩ : syracuseStep 2742335 = 4113503) B4113503
theorem B1367759 : Blo 810345 1367759 := bstep (se 1 (by rfl) ⟨1025819, by rfl⟩ : syracuseStep 1367759 = 2051639) B2051639
theorem B811007 : Blo 810345 811007 := bstep (se 1 (by rfl) ⟨608255, by rfl⟩ : syracuseStep 811007 = 1216511) B1216511
theorem B1828331 : Blo 810345 1828331 := bstep (se 1 (by rfl) ⟨1371248, by rfl⟩ : syracuseStep 1828331 = 2742497) B2742497
theorem B2746655 : Blo 810345 2746655 := bstep (se 1 (by rfl) ⟨2059991, by rfl⟩ : syracuseStep 2746655 = 4119983) B4119983
theorem B813819 : Blo 810345 813819 := bstep (se 1 (by rfl) ⟨610364, by rfl⟩ : syracuseStep 813819 = 1220729) B1220729
theorem B1371647 : Blo 810345 1371647 := bstep (se 1 (by rfl) ⟨1028735, by rfl⟩ : syracuseStep 1371647 = 2057471) B2057471
theorem B17560313 : Blo 810345 17560313 := bstep (se 2 (by rfl) ⟨6585117, by rfl⟩ : syracuseStep 17560313 = 13170235) B13170235
theorem B9042391 : Blo 810345 9042391 := bstep (se 1 (by rfl) ⟨6781793, by rfl⟩ : syracuseStep 9042391 = 13563587) B13563587
theorem B42270665 : Blo 810345 42270665 := bstep (se 2 (by rfl) ⟨15851499, by rfl⟩ : syracuseStep 42270665 = 31702999) B31702999
theorem B6259369 : Blo 810345 6259369 := bstep (se 2 (by rfl) ⟨2347263, by rfl⟩ : syracuseStep 6259369 = 4694527) B4694527
theorem B29331209 : Blo 810345 29331209 := bstep (se 2 (by rfl) ⟨10999203, by rfl⟩ : syracuseStep 29331209 = 21998407) B21998407
theorem B1218887 : Blo 810345 1218887 := bstep (se 1 (by rfl) ⟨914165, by rfl⟩ : syracuseStep 1218887 = 1828331) B1828331
theorem B11737835 : Blo 810345 11737835 := bstep (se 1 (by rfl) ⟨8803376, by rfl⟩ : syracuseStep 11737835 = 17606753) B17606753
theorem B11706875 : Blo 810345 11706875 := bstep (se 1 (by rfl) ⟨8780156, by rfl⟩ : syracuseStep 11706875 = 17560313) B17560313
theorem B6239663 : Blo 810345 6239663 := bstep (se 1 (by rfl) ⟨4679747, by rfl⟩ : syracuseStep 6239663 = 9359495) B9359495
theorem B2739743 : Blo 810345 2739743 := bstep (se 1 (by rfl) ⟨2054807, by rfl⟩ : syracuseStep 2739743 = 4109615) B4109615
theorem B1823471 : Blo 810345 1823471 := bstep (se 1 (by rfl) ⟨1367603, by rfl⟩ : syracuseStep 1823471 = 2735207) B2735207
theorem B1824083 : Blo 810345 1824083 := bstep (se 1 (by rfl) ⟨1368062, by rfl⟩ : syracuseStep 1824083 = 2736125) B2736125
theorem B2742119 : Blo 810345 2742119 := bstep (se 1 (by rfl) ⟨2056589, by rfl⟩ : syracuseStep 2742119 = 4113179) B4113179
theorem B1827611 : Blo 810345 1827611 := bstep (se 1 (by rfl) ⟨1370708, by rfl⟩ : syracuseStep 1827611 = 2741417) B2741417
theorem B1828223 : Blo 810345 1828223 := bstep (se 1 (by rfl) ⟨1371167, by rfl⟩ : syracuseStep 1828223 = 2742335) B2742335
theorem B2058331 : Blo 810345 2058331 := bstep (se 1 (by rfl) ⟨1543748, by rfl⟩ : syracuseStep 2058331 = 3087497) B3087497
theorem B911839 : Blo 810345 911839 := bstep (se 1 (by rfl) ⟨683879, by rfl⟩ : syracuseStep 911839 = 1367759) B1367759
theorem B1831103 : Blo 810345 1831103 := bstep (se 1 (by rfl) ⟨1373327, by rfl⟩ : syracuseStep 1831103 = 2746655) B2746655
theorem B914431 : Blo 810345 914431 := bstep (se 1 (by rfl) ⟨685823, by rfl⟩ : syracuseStep 914431 = 1371647) B1371647
theorem B12056521 : Blo 810345 12056521 := bstep (se 2 (by rfl) ⟨4521195, by rfl⟩ : syracuseStep 12056521 = 9042391) B9042391
theorem B450887093 : Blo 810345 450887093 := bstep (se 5 (by rfl) ⟨21135332, by rfl⟩ : syracuseStep 450887093 = 42270665) B42270665
theorem B1215647 : Blo 810345 1215647 := bstep (se 1 (by rfl) ⟨911735, by rfl⟩ : syracuseStep 1215647 = 1823471) B1823471
theorem B1215785 : Blo 810345 1215785 := bstep (se 2 (by rfl) ⟨455919, by rfl⟩ : syracuseStep 1215785 = 911839) B911839
theorem B1216055 : Blo 810345 1216055 := bstep (se 1 (by rfl) ⟨912041, by rfl⟩ : syracuseStep 1216055 = 1824083) B1824083
theorem B7804583 : Blo 810345 7804583 := bstep (se 1 (by rfl) ⟨5853437, by rfl⟩ : syracuseStep 7804583 = 11706875) B11706875
theorem B1218407 : Blo 810345 1218407 := bstep (se 1 (by rfl) ⟨913805, by rfl⟩ : syracuseStep 1218407 = 1827611) B1827611
theorem B1218815 : Blo 810345 1218815 := bstep (se 1 (by rfl) ⟨914111, by rfl⟩ : syracuseStep 1218815 = 1828223) B1828223
theorem B1219241 : Blo 810345 1219241 := bstep (se 2 (by rfl) ⟨457215, by rfl⟩ : syracuseStep 1219241 = 914431) B914431
theorem B1220735 : Blo 810345 1220735 := bstep (se 1 (by rfl) ⟨915551, by rfl⟩ : syracuseStep 1220735 = 1831103) B1831103
theorem B300591395 : Blo 810345 300591395 := bstep (se 1 (by rfl) ⟨225443546, by rfl⟩ : syracuseStep 300591395 = 450887093) B450887093
theorem B16075361 : Blo 810345 16075361 := bstep (se 2 (by rfl) ⟨6028260, by rfl⟩ : syracuseStep 16075361 = 12056521) B12056521
theorem B8345825 : Blo 810345 8345825 := bstep (se 2 (by rfl) ⟨3129684, by rfl⟩ : syracuseStep 8345825 = 6259369) B6259369
theorem B1826495 : Blo 810345 1826495 := bstep (se 1 (by rfl) ⟨1369871, by rfl⟩ : syracuseStep 1826495 = 2739743) B2739743
theorem B19554139 : Blo 810345 19554139 := bstep (se 1 (by rfl) ⟨14665604, by rfl⟩ : syracuseStep 19554139 = 29331209) B29331209
theorem B2744441 : Blo 810345 2744441 := bstep (se 2 (by rfl) ⟨1029165, by rfl⟩ : syracuseStep 2744441 = 2058331) B2058331
theorem B1828079 : Blo 810345 1828079 := bstep (se 1 (by rfl) ⟨1371059, by rfl⟩ : syracuseStep 1828079 = 2742119) B2742119
theorem B812591 : Blo 810345 812591 := bstep (se 1 (by rfl) ⟨609443, by rfl⟩ : syracuseStep 812591 = 1218887) B1218887
theorem B7825223 : Blo 810345 7825223 := bstep (se 1 (by rfl) ⟨5868917, by rfl⟩ : syracuseStep 7825223 = 11737835) B11737835
theorem B4159775 : Blo 810345 4159775 := bstep (se 1 (by rfl) ⟨3119831, by rfl⟩ : syracuseStep 4159775 = 6239663) B6239663
theorem B10716907 : Blo 810345 10716907 := bstep (se 1 (by rfl) ⟨8037680, by rfl⟩ : syracuseStep 10716907 = 16075361) B16075361
theorem B1217663 : Blo 810345 1217663 := bstep (se 1 (by rfl) ⟨913247, by rfl⟩ : syracuseStep 1217663 = 1826495) B1826495
theorem B1218719 : Blo 810345 1218719 := bstep (se 1 (by rfl) ⟨914039, by rfl⟩ : syracuseStep 1218719 = 1828079) B1828079
theorem B5216815 : Blo 810345 5216815 := bstep (se 1 (by rfl) ⟨3912611, by rfl⟩ : syracuseStep 5216815 = 7825223) B7825223
theorem B200394263 : Blo 810345 200394263 := bstep (se 1 (by rfl) ⟨150295697, by rfl⟩ : syracuseStep 200394263 = 300591395) B300591395
theorem B2773183 : Blo 810345 2773183 := bstep (se 1 (by rfl) ⟨2079887, by rfl⟩ : syracuseStep 2773183 = 4159775) B4159775
theorem B104288741 : Blo 810345 104288741 := bstep (se 4 (by rfl) ⟨9777069, by rfl⟩ : syracuseStep 104288741 = 19554139) B19554139
theorem B810431 : Blo 810345 810431 := bstep (se 1 (by rfl) ⟨607823, by rfl⟩ : syracuseStep 810431 = 1215647) B1215647
theorem B810523 : Blo 810345 810523 := bstep (se 1 (by rfl) ⟨607892, by rfl⟩ : syracuseStep 810523 = 1215785) B1215785
theorem B810703 : Blo 810345 810703 := bstep (se 1 (by rfl) ⟨608027, by rfl⟩ : syracuseStep 810703 = 1216055) B1216055
theorem B5203055 : Blo 810345 5203055 := bstep (se 1 (by rfl) ⟨3902291, by rfl⟩ : syracuseStep 5203055 = 7804583) B7804583
theorem B812271 : Blo 810345 812271 := bstep (se 1 (by rfl) ⟨609203, by rfl⟩ : syracuseStep 812271 = 1218407) B1218407
theorem B5563883 : Blo 810345 5563883 := bstep (se 1 (by rfl) ⟨4172912, by rfl⟩ : syracuseStep 5563883 = 8345825) B8345825
theorem B812543 : Blo 810345 812543 := bstep (se 1 (by rfl) ⟨609407, by rfl⟩ : syracuseStep 812543 = 1218815) B1218815
theorem B812827 : Blo 810345 812827 := bstep (se 1 (by rfl) ⟨609620, by rfl⟩ : syracuseStep 812827 = 1219241) B1219241
theorem B1829627 : Blo 810345 1829627 := bstep (se 1 (by rfl) ⟨1372220, by rfl⟩ : syracuseStep 1829627 = 2744441) B2744441
theorem B813823 : Blo 810345 813823 := bstep (se 1 (by rfl) ⟨610367, by rfl⟩ : syracuseStep 813823 = 1220735) B1220735
theorem B133596175 : Blo 810345 133596175 := bstep (se 1 (by rfl) ⟨100197131, by rfl⟩ : syracuseStep 133596175 = 200394263) B200394263
theorem B14289209 : Blo 810345 14289209 := bstep (se 2 (by rfl) ⟨5358453, by rfl⟩ : syracuseStep 14289209 = 10716907) B10716907
theorem B3709255 : Blo 810345 3709255 := bstep (se 1 (by rfl) ⟨2781941, by rfl⟩ : syracuseStep 3709255 = 5563883) B5563883
theorem B1219751 : Blo 810345 1219751 := bstep (se 1 (by rfl) ⟨914813, by rfl⟩ : syracuseStep 1219751 = 1829627) B1829627
theorem B6955753 : Blo 810345 6955753 := bstep (se 2 (by rfl) ⟨2608407, by rfl⟩ : syracuseStep 6955753 = 5216815) B5216815
theorem B69525827 : Blo 810345 69525827 := bstep (se 1 (by rfl) ⟨52144370, by rfl⟩ : syracuseStep 69525827 = 104288741) B104288741
theorem B811775 : Blo 810345 811775 := bstep (se 1 (by rfl) ⟨608831, by rfl⟩ : syracuseStep 811775 = 1217663) B1217663
theorem B812479 : Blo 810345 812479 := bstep (se 1 (by rfl) ⟨609359, by rfl⟩ : syracuseStep 812479 = 1218719) B1218719
theorem B3697577 : Blo 810345 3697577 := bstep (se 2 (by rfl) ⟨1386591, by rfl⟩ : syracuseStep 3697577 = 2773183) B2773183
theorem B3468703 : Blo 810345 3468703 := bstep (se 1 (by rfl) ⟨2601527, by rfl⟩ : syracuseStep 3468703 = 5203055) B5203055
theorem B9274337 : Blo 810345 9274337 := bstep (se 2 (by rfl) ⟨3477876, by rfl⟩ : syracuseStep 9274337 = 6955753) B6955753
theorem B178128233 : Blo 810345 178128233 := bstep (se 2 (by rfl) ⟨66798087, by rfl⟩ : syracuseStep 178128233 = 133596175) B133596175
theorem B4624937 : Blo 810345 4624937 := bstep (se 2 (by rfl) ⟨1734351, by rfl⟩ : syracuseStep 4624937 = 3468703) B3468703
theorem B2465051 : Blo 810345 2465051 := bstep (se 1 (by rfl) ⟨1848788, by rfl⟩ : syracuseStep 2465051 = 3697577) B3697577
theorem B46350551 : Blo 810345 46350551 := bstep (se 1 (by rfl) ⟨34762913, by rfl⟩ : syracuseStep 46350551 = 69525827) B69525827
theorem B9526139 : Blo 810345 9526139 := bstep (se 1 (by rfl) ⟨7144604, by rfl⟩ : syracuseStep 9526139 = 14289209) B14289209
theorem B813167 : Blo 810345 813167 := bstep (se 1 (by rfl) ⟨609875, by rfl⟩ : syracuseStep 813167 = 1219751) B1219751
theorem B4945673 : Blo 810345 4945673 := bstep (se 2 (by rfl) ⟨1854627, by rfl⟩ : syracuseStep 4945673 = 3709255) B3709255
theorem B30900367 : Blo 810345 30900367 := bstep (se 1 (by rfl) ⟨23175275, by rfl⟩ : syracuseStep 30900367 = 46350551) B46350551
theorem B118752155 : Blo 810345 118752155 := bstep (se 1 (by rfl) ⟨89064116, by rfl⟩ : syracuseStep 118752155 = 178128233) B178128233
theorem B3083291 : Blo 810345 3083291 := bstep (se 1 (by rfl) ⟨2312468, by rfl⟩ : syracuseStep 3083291 = 4624937) B4624937
theorem B6573469 : Blo 810345 6573469 := bstep (se 3 (by rfl) ⟨1232525, by rfl⟩ : syracuseStep 6573469 = 2465051) B2465051
theorem B3297115 : Blo 810345 3297115 := bstep (se 1 (by rfl) ⟨2472836, by rfl⟩ : syracuseStep 3297115 = 4945673) B4945673
theorem B6182891 : Blo 810345 6182891 := bstep (se 1 (by rfl) ⟨4637168, by rfl⟩ : syracuseStep 6182891 = 9274337) B9274337
theorem B6350759 : Blo 810345 6350759 := bstep (se 1 (by rfl) ⟨4763069, by rfl⟩ : syracuseStep 6350759 = 9526139) B9526139
theorem B79168103 : Blo 810345 79168103 := bstep (se 1 (by rfl) ⟨59376077, by rfl⟩ : syracuseStep 79168103 = 118752155) B118752155
theorem B4396153 : Blo 810345 4396153 := bstep (se 2 (by rfl) ⟨1648557, by rfl⟩ : syracuseStep 4396153 = 3297115) B3297115
theorem B67741429 : Blo 810345 67741429 := bstep (se 5 (by rfl) ⟨3175379, by rfl⟩ : syracuseStep 67741429 = 6350759) B6350759
theorem B41200489 : Blo 810345 41200489 := bstep (se 2 (by rfl) ⟨15450183, by rfl⟩ : syracuseStep 41200489 = 30900367) B30900367
theorem B8764625 : Blo 810345 8764625 := bstep (se 2 (by rfl) ⟨3286734, by rfl⟩ : syracuseStep 8764625 = 6573469) B6573469
theorem B2055527 : Blo 810345 2055527 := bstep (se 1 (by rfl) ⟨1541645, by rfl⟩ : syracuseStep 2055527 = 3083291) B3083291
theorem B4121927 : Blo 810345 4121927 := bstep (se 1 (by rfl) ⟨3091445, by rfl⟩ : syracuseStep 4121927 = 6182891) B6182891
theorem B23372333 : Blo 810345 23372333 := bstep (se 3 (by rfl) ⟨4382312, by rfl⟩ : syracuseStep 23372333 = 8764625) B8764625
theorem B90321905 : Blo 810345 90321905 := bstep (se 2 (by rfl) ⟨33870714, by rfl⟩ : syracuseStep 90321905 = 67741429) B67741429
theorem B54933985 : Blo 810345 54933985 := bstep (se 2 (by rfl) ⟨20600244, by rfl⟩ : syracuseStep 54933985 = 41200489) B41200489
theorem B52778735 : Blo 810345 52778735 := bstep (se 1 (by rfl) ⟨39584051, by rfl⟩ : syracuseStep 52778735 = 79168103) B79168103
theorem B1370351 : Blo 810345 1370351 := bstep (se 1 (by rfl) ⟨1027763, by rfl⟩ : syracuseStep 1370351 = 2055527) B2055527
theorem B2747951 : Blo 810345 2747951 := bstep (se 1 (by rfl) ⟨2060963, by rfl⟩ : syracuseStep 2747951 = 4121927) B4121927
theorem B5861537 : Blo 810345 5861537 := bstep (se 2 (by rfl) ⟨2198076, by rfl⟩ : syracuseStep 5861537 = 4396153) B4396153
theorem B3907691 : Blo 810345 3907691 := bstep (se 1 (by rfl) ⟨2930768, by rfl⟩ : syracuseStep 3907691 = 5861537) B5861537
theorem B73245313 : Blo 810345 73245313 := bstep (se 2 (by rfl) ⟨27466992, by rfl⟩ : syracuseStep 73245313 = 54933985) B54933985
theorem B15581555 : Blo 810345 15581555 := bstep (se 1 (by rfl) ⟨11686166, by rfl⟩ : syracuseStep 15581555 = 23372333) B23372333
theorem B60214603 : Blo 810345 60214603 := bstep (se 1 (by rfl) ⟨45160952, by rfl⟩ : syracuseStep 60214603 = 90321905) B90321905
theorem B35185823 : Blo 810345 35185823 := bstep (se 1 (by rfl) ⟨26389367, by rfl⟩ : syracuseStep 35185823 = 52778735) B52778735
theorem B913567 : Blo 810345 913567 := bstep (se 1 (by rfl) ⟨685175, by rfl⟩ : syracuseStep 913567 = 1370351) B1370351
theorem B1831967 : Blo 810345 1831967 := bstep (se 1 (by rfl) ⟨1373975, by rfl⟩ : syracuseStep 1831967 = 2747951) B2747951
theorem B10387703 : Blo 810345 10387703 := bstep (se 1 (by rfl) ⟨7790777, by rfl⟩ : syracuseStep 10387703 = 15581555) B15581555
theorem B80286137 : Blo 810345 80286137 := bstep (se 2 (by rfl) ⟨30107301, by rfl⟩ : syracuseStep 80286137 = 60214603) B60214603
theorem B1218089 : Blo 810345 1218089 := bstep (se 2 (by rfl) ⟨456783, by rfl⟩ : syracuseStep 1218089 = 913567) B913567
theorem B1221311 : Blo 810345 1221311 := bstep (se 1 (by rfl) ⟨915983, by rfl⟩ : syracuseStep 1221311 = 1831967) B1831967
theorem B97660417 : Blo 810345 97660417 := bstep (se 2 (by rfl) ⟨36622656, by rfl⟩ : syracuseStep 97660417 = 73245313) B73245313
theorem B2605127 : Blo 810345 2605127 := bstep (se 1 (by rfl) ⟨1953845, by rfl⟩ : syracuseStep 2605127 = 3907691) B3907691
theorem B23457215 : Blo 810345 23457215 := bstep (se 1 (by rfl) ⟨17592911, by rfl⟩ : syracuseStep 23457215 = 35185823) B35185823
theorem B6947005 : Blo 810345 6947005 := bstep (se 3 (by rfl) ⟨1302563, by rfl⟩ : syracuseStep 6947005 = 2605127) B2605127
theorem B15638143 : Blo 810345 15638143 := bstep (se 1 (by rfl) ⟨11728607, by rfl⟩ : syracuseStep 15638143 = 23457215) B23457215
theorem B6925135 : Blo 810345 6925135 := bstep (se 1 (by rfl) ⟨5193851, by rfl⟩ : syracuseStep 6925135 = 10387703) B10387703
theorem B53524091 : Blo 810345 53524091 := bstep (se 1 (by rfl) ⟨40143068, by rfl⟩ : syracuseStep 53524091 = 80286137) B80286137
theorem B812059 : Blo 810345 812059 := bstep (se 1 (by rfl) ⟨609044, by rfl⟩ : syracuseStep 812059 = 1218089) B1218089
theorem B130213889 : Blo 810345 130213889 := bstep (se 2 (by rfl) ⟨48830208, by rfl⟩ : syracuseStep 130213889 = 97660417) B97660417
theorem B814207 : Blo 810345 814207 := bstep (se 1 (by rfl) ⟨610655, by rfl⟩ : syracuseStep 814207 = 1221311) B1221311
theorem B86809259 : Blo 810345 86809259 := bstep (se 1 (by rfl) ⟨65106944, by rfl⟩ : syracuseStep 86809259 = 130213889) B130213889
theorem B20850857 : Blo 810345 20850857 := bstep (se 2 (by rfl) ⟨7819071, by rfl⟩ : syracuseStep 20850857 = 15638143) B15638143
theorem B9262673 : Blo 810345 9262673 := bstep (se 2 (by rfl) ⟨3473502, by rfl⟩ : syracuseStep 9262673 = 6947005) B6947005
theorem B9233513 : Blo 810345 9233513 := bstep (se 2 (by rfl) ⟨3462567, by rfl⟩ : syracuseStep 9233513 = 6925135) B6925135
theorem B35682727 : Blo 810345 35682727 := bstep (se 1 (by rfl) ⟨26762045, by rfl⟩ : syracuseStep 35682727 = 53524091) B53524091
theorem B57872839 : Blo 810345 57872839 := bstep (se 1 (by rfl) ⟨43404629, by rfl⟩ : syracuseStep 57872839 = 86809259) B86809259
theorem B13900571 : Blo 810345 13900571 := bstep (se 1 (by rfl) ⟨10425428, by rfl⟩ : syracuseStep 13900571 = 20850857) B20850857
theorem B6175115 : Blo 810345 6175115 := bstep (se 1 (by rfl) ⟨4631336, by rfl⟩ : syracuseStep 6175115 = 9262673) B9262673
theorem B6155675 : Blo 810345 6155675 := bstep (se 1 (by rfl) ⟨4616756, by rfl⟩ : syracuseStep 6155675 = 9233513) B9233513
theorem B47576969 : Blo 810345 47576969 := bstep (se 2 (by rfl) ⟨17841363, by rfl⟩ : syracuseStep 47576969 = 35682727) B35682727
theorem B4103783 : Blo 810345 4103783 := bstep (se 1 (by rfl) ⟨3077837, by rfl⟩ : syracuseStep 4103783 = 6155675) B6155675
theorem B4116743 : Blo 810345 4116743 := bstep (se 1 (by rfl) ⟨3087557, by rfl⟩ : syracuseStep 4116743 = 6175115) B6175115
theorem B9267047 : Blo 810345 9267047 := bstep (se 1 (by rfl) ⟨6950285, by rfl⟩ : syracuseStep 9267047 = 13900571) B13900571
theorem B77163785 : Blo 810345 77163785 := bstep (se 2 (by rfl) ⟨28936419, by rfl⟩ : syracuseStep 77163785 = 57872839) B57872839
theorem B31717979 : Blo 810345 31717979 := bstep (se 1 (by rfl) ⟨23788484, by rfl⟩ : syracuseStep 31717979 = 47576969) B47576969
theorem B21145319 : Blo 810345 21145319 := bstep (se 1 (by rfl) ⟨15858989, by rfl⟩ : syracuseStep 21145319 = 31717979) B31717979
theorem B2735855 : Blo 810345 2735855 := bstep (se 1 (by rfl) ⟨2051891, by rfl⟩ : syracuseStep 2735855 = 4103783) B4103783
theorem B6178031 : Blo 810345 6178031 := bstep (se 1 (by rfl) ⟨4633523, by rfl⟩ : syracuseStep 6178031 = 9267047) B9267047
theorem B2744495 : Blo 810345 2744495 := bstep (se 1 (by rfl) ⟨2058371, by rfl⟩ : syracuseStep 2744495 = 4116743) B4116743
theorem B51442523 : Blo 810345 51442523 := bstep (se 1 (by rfl) ⟨38581892, by rfl⟩ : syracuseStep 51442523 = 77163785) B77163785
theorem B14096879 : Blo 810345 14096879 := bstep (se 1 (by rfl) ⟨10572659, by rfl⟩ : syracuseStep 14096879 = 21145319) B21145319
theorem B34295015 : Blo 810345 34295015 := bstep (se 1 (by rfl) ⟨25721261, by rfl⟩ : syracuseStep 34295015 = 51442523) B51442523
theorem B1823903 : Blo 810345 1823903 := bstep (se 1 (by rfl) ⟨1367927, by rfl⟩ : syracuseStep 1823903 = 2735855) B2735855
theorem B4118687 : Blo 810345 4118687 := bstep (se 1 (by rfl) ⟨3089015, by rfl⟩ : syracuseStep 4118687 = 6178031) B6178031
theorem B1829663 : Blo 810345 1829663 := bstep (se 1 (by rfl) ⟨1372247, by rfl⟩ : syracuseStep 1829663 = 2744495) B2744495
theorem B1215935 : Blo 810345 1215935 := bstep (se 1 (by rfl) ⟨911951, by rfl⟩ : syracuseStep 1215935 = 1823903) B1823903
theorem B1219775 : Blo 810345 1219775 := bstep (se 1 (by rfl) ⟨914831, by rfl⟩ : syracuseStep 1219775 = 1829663) B1829663
theorem B22863343 : Blo 810345 22863343 := bstep (se 1 (by rfl) ⟨17147507, by rfl⟩ : syracuseStep 22863343 = 34295015) B34295015
theorem B2745791 : Blo 810345 2745791 := bstep (se 1 (by rfl) ⟨2059343, by rfl⟩ : syracuseStep 2745791 = 4118687) B4118687
theorem B9397919 : Blo 810345 9397919 := bstep (se 1 (by rfl) ⟨7048439, by rfl⟩ : syracuseStep 9397919 = 14096879) B14096879
theorem B6265279 : Blo 810345 6265279 := bstep (se 1 (by rfl) ⟨4698959, by rfl⟩ : syracuseStep 6265279 = 9397919) B9397919
theorem B30484457 : Blo 810345 30484457 := bstep (se 2 (by rfl) ⟨11431671, by rfl⟩ : syracuseStep 30484457 = 22863343) B22863343
theorem B810623 : Blo 810345 810623 := bstep (se 1 (by rfl) ⟨607967, by rfl⟩ : syracuseStep 810623 = 1215935) B1215935
theorem B813183 : Blo 810345 813183 := bstep (se 1 (by rfl) ⟨609887, by rfl⟩ : syracuseStep 813183 = 1219775) B1219775
theorem B1830527 : Blo 810345 1830527 := bstep (se 1 (by rfl) ⟨1372895, by rfl⟩ : syracuseStep 1830527 = 2745791) B2745791
theorem B20322971 : Blo 810345 20322971 := bstep (se 1 (by rfl) ⟨15242228, by rfl⟩ : syracuseStep 20322971 = 30484457) B30484457
theorem B1220351 : Blo 810345 1220351 := bstep (se 1 (by rfl) ⟨915263, by rfl⟩ : syracuseStep 1220351 = 1830527) B1830527
theorem B8353705 : Blo 810345 8353705 := bstep (se 2 (by rfl) ⟨3132639, by rfl⟩ : syracuseStep 8353705 = 6265279) B6265279
theorem B13548647 : Blo 810345 13548647 := bstep (se 1 (by rfl) ⟨10161485, by rfl⟩ : syracuseStep 13548647 = 20322971) B20322971
theorem B813567 : Blo 810345 813567 := bstep (se 1 (by rfl) ⟨610175, by rfl⟩ : syracuseStep 813567 = 1220351) B1220351
theorem B11138273 : Blo 810345 11138273 := bstep (se 2 (by rfl) ⟨4176852, by rfl⟩ : syracuseStep 11138273 = 8353705) B8353705
theorem B36129725 : Blo 810345 36129725 := bstep (se 3 (by rfl) ⟨6774323, by rfl⟩ : syracuseStep 36129725 = 13548647) B13548647
theorem B7425515 : Blo 810345 7425515 := bstep (se 1 (by rfl) ⟨5569136, by rfl⟩ : syracuseStep 7425515 = 11138273) B11138273
theorem B24086483 : Blo 810345 24086483 := bstep (se 1 (by rfl) ⟨18064862, by rfl⟩ : syracuseStep 24086483 = 36129725) B36129725
theorem B4950343 : Blo 810345 4950343 := bstep (se 1 (by rfl) ⟨3712757, by rfl⟩ : syracuseStep 4950343 = 7425515) B7425515
theorem B16057655 : Blo 810345 16057655 := bstep (se 1 (by rfl) ⟨12043241, by rfl⟩ : syracuseStep 16057655 = 24086483) B24086483
theorem B6600457 : Blo 810345 6600457 := bstep (se 2 (by rfl) ⟨2475171, by rfl⟩ : syracuseStep 6600457 = 4950343) B4950343
theorem B8800609 : Blo 810345 8800609 := bstep (se 2 (by rfl) ⟨3300228, by rfl⟩ : syracuseStep 8800609 = 6600457) B6600457
theorem B10705103 : Blo 810345 10705103 := bstep (se 1 (by rfl) ⟨8028827, by rfl⟩ : syracuseStep 10705103 = 16057655) B16057655
theorem B11734145 : Blo 810345 11734145 := bstep (se 2 (by rfl) ⟨4400304, by rfl⟩ : syracuseStep 11734145 = 8800609) B8800609
theorem B114187765 : Blo 810345 114187765 := bstep (se 5 (by rfl) ⟨5352551, by rfl⟩ : syracuseStep 114187765 = 10705103) B10705103
theorem B152250353 : Blo 810345 152250353 := bstep (se 2 (by rfl) ⟨57093882, by rfl⟩ : syracuseStep 152250353 = 114187765) B114187765
theorem B7822763 : Blo 810345 7822763 := bstep (se 1 (by rfl) ⟨5867072, by rfl⟩ : syracuseStep 7822763 = 11734145) B11734145
theorem B5215175 : Blo 810345 5215175 := bstep (se 1 (by rfl) ⟨3911381, by rfl⟩ : syracuseStep 5215175 = 7822763) B7822763
theorem B101500235 : Blo 810345 101500235 := bstep (se 1 (by rfl) ⟨76125176, by rfl⟩ : syracuseStep 101500235 = 152250353) B152250353
theorem B67666823 : Blo 810345 67666823 := bstep (se 1 (by rfl) ⟨50750117, by rfl⟩ : syracuseStep 67666823 = 101500235) B101500235
theorem B3476783 : Blo 810345 3476783 := bstep (se 1 (by rfl) ⟨2607587, by rfl⟩ : syracuseStep 3476783 = 5215175) B5215175
theorem B45111215 : Blo 810345 45111215 := bstep (se 1 (by rfl) ⟨33833411, by rfl⟩ : syracuseStep 45111215 = 67666823) B67666823
theorem B9271421 : Blo 810345 9271421 := bstep (se 3 (by rfl) ⟨1738391, by rfl⟩ : syracuseStep 9271421 = 3476783) B3476783
theorem B120296573 : Blo 810345 120296573 := bstep (se 3 (by rfl) ⟨22555607, by rfl⟩ : syracuseStep 120296573 = 45111215) B45111215
theorem B6180947 : Blo 810345 6180947 := bstep (se 1 (by rfl) ⟨4635710, by rfl⟩ : syracuseStep 6180947 = 9271421) B9271421
theorem B80197715 : Blo 810345 80197715 := bstep (se 1 (by rfl) ⟨60148286, by rfl⟩ : syracuseStep 80197715 = 120296573) B120296573
theorem B4120631 : Blo 810345 4120631 := bstep (se 1 (by rfl) ⟨3090473, by rfl⟩ : syracuseStep 4120631 = 6180947) B6180947
theorem B53465143 : Blo 810345 53465143 := bstep (se 1 (by rfl) ⟨40098857, by rfl⟩ : syracuseStep 53465143 = 80197715) B80197715
theorem B2747087 : Blo 810345 2747087 := bstep (se 1 (by rfl) ⟨2060315, by rfl⟩ : syracuseStep 2747087 = 4120631) B4120631
theorem B71286857 : Blo 810345 71286857 := bstep (se 2 (by rfl) ⟨26732571, by rfl⟩ : syracuseStep 71286857 = 53465143) B53465143
theorem B1831391 : Blo 810345 1831391 := bstep (se 1 (by rfl) ⟨1373543, by rfl⟩ : syracuseStep 1831391 = 2747087) B2747087
theorem B1220927 : Blo 810345 1220927 := bstep (se 1 (by rfl) ⟨915695, by rfl⟩ : syracuseStep 1220927 = 1831391) B1831391
theorem B47524571 : Blo 810345 47524571 := bstep (se 1 (by rfl) ⟨35643428, by rfl⟩ : syracuseStep 47524571 = 71286857) B71286857
theorem B813951 : Blo 810345 813951 := bstep (se 1 (by rfl) ⟨610463, by rfl⟩ : syracuseStep 813951 = 1220927) B1220927
theorem B31683047 : Blo 810345 31683047 := bstep (se 1 (by rfl) ⟨23762285, by rfl⟩ : syracuseStep 31683047 = 47524571) B47524571
theorem B84488125 : Blo 810345 84488125 := bstep (se 3 (by rfl) ⟨15841523, by rfl⟩ : syracuseStep 84488125 = 31683047) B31683047
theorem B112650833 : Blo 810345 112650833 := bstep (se 2 (by rfl) ⟨42244062, by rfl⟩ : syracuseStep 112650833 = 84488125) B84488125
theorem B75100555 : Blo 810345 75100555 := bstep (se 1 (by rfl) ⟨56325416, by rfl⟩ : syracuseStep 75100555 = 112650833) B112650833
theorem B100134073 : Blo 810345 100134073 := bstep (se 2 (by rfl) ⟨37550277, by rfl⟩ : syracuseStep 100134073 = 75100555) B75100555
theorem B133512097 : Blo 810345 133512097 := bstep (se 2 (by rfl) ⟨50067036, by rfl⟩ : syracuseStep 133512097 = 100134073) B100134073
theorem B178016129 : Blo 810345 178016129 := bstep (se 2 (by rfl) ⟨66756048, by rfl⟩ : syracuseStep 178016129 = 133512097) B133512097
theorem B118677419 : Blo 810345 118677419 := bstep (se 1 (by rfl) ⟨89008064, by rfl⟩ : syracuseStep 118677419 = 178016129) B178016129
theorem B79118279 : Blo 810345 79118279 := bstep (se 1 (by rfl) ⟨59338709, by rfl⟩ : syracuseStep 79118279 = 118677419) B118677419
theorem B52745519 : Blo 810345 52745519 := bstep (se 1 (by rfl) ⟨39559139, by rfl⟩ : syracuseStep 52745519 = 79118279) B79118279
theorem B35163679 : Blo 810345 35163679 := bstep (se 1 (by rfl) ⟨26372759, by rfl⟩ : syracuseStep 35163679 = 52745519) B52745519
theorem B46884905 : Blo 810345 46884905 := bstep (se 2 (by rfl) ⟨17581839, by rfl⟩ : syracuseStep 46884905 = 35163679) B35163679
theorem B31256603 : Blo 810345 31256603 := bstep (se 1 (by rfl) ⟨23442452, by rfl⟩ : syracuseStep 31256603 = 46884905) B46884905
theorem B20837735 : Blo 810345 20837735 := bstep (se 1 (by rfl) ⟨15628301, by rfl⟩ : syracuseStep 20837735 = 31256603) B31256603
theorem B13891823 : Blo 810345 13891823 := bstep (se 1 (by rfl) ⟨10418867, by rfl⟩ : syracuseStep 13891823 = 20837735) B20837735
theorem B9261215 : Blo 810345 9261215 := bstep (se 1 (by rfl) ⟨6945911, by rfl⟩ : syracuseStep 9261215 = 13891823) B13891823
theorem B6174143 : Blo 810345 6174143 := bstep (se 1 (by rfl) ⟨4630607, by rfl⟩ : syracuseStep 6174143 = 9261215) B9261215
theorem B4116095 : Blo 810345 4116095 := bstep (se 1 (by rfl) ⟨3087071, by rfl⟩ : syracuseStep 4116095 = 6174143) B6174143
theorem B2744063 : Blo 810345 2744063 := bstep (se 1 (by rfl) ⟨2058047, by rfl⟩ : syracuseStep 2744063 = 4116095) B4116095
theorem B1829375 : Blo 810345 1829375 := bstep (se 1 (by rfl) ⟨1372031, by rfl⟩ : syracuseStep 1829375 = 2744063) B2744063
theorem B1219583 : Blo 810345 1219583 := bstep (se 1 (by rfl) ⟨914687, by rfl⟩ : syracuseStep 1219583 = 1829375) B1829375
theorem B813055 : Blo 810345 813055 := bstep (se 1 (by rfl) ⟨609791, by rfl⟩ : syracuseStep 813055 = 1219583) B1219583

theorem C0 (j : ℕ) (h1 : 202586 ≤ j) (h2 : j ≤ 203285) : Blo 810345 (4 * j + 3) := by
  interval_cases j
  · exact B810347
  · exact B810351
  · exact B810355
  · exact B810359
  · exact B810363
  · exact B810367
  · exact B810371
  · exact B810375
  · exact B810379
  · exact B810383
  · exact B810387
  · exact B810391
  · exact B810395
  · exact B810399
  · exact B810403
  · exact B810407
  · exact B810411
  · exact B810415
  · exact B810419
  · exact B810423
  · exact B810427
  · exact B810431
  · exact B810435
  · exact B810439
  · exact B810443
  · exact B810447
  · exact B810451
  · exact B810455
  · exact B810459
  · exact B810463
  · exact B810467
  · exact B810471
  · exact B810475
  · exact B810479
  · exact B810483
  · exact B810487
  · exact B810491
  · exact B810495
  · exact B810499
  · exact B810503
  · exact B810507
  · exact B810511
  · exact B810515
  · exact B810519
  · exact B810523
  · exact B810527
  · exact B810531
  · exact B810535
  · exact B810539
  · exact B810543
  · exact B810547
  · exact B810551
  · exact B810555
  · exact B810559
  · exact B810563
  · exact B810567
  · exact B810571
  · exact B810575
  · exact B810579
  · exact B810583
  · exact B810587
  · exact B810591
  · exact B810595
  · exact B810599
  · exact B810603
  · exact B810607
  · exact B810611
  · exact B810615
  · exact B810619
  · exact B810623
  · exact B810627
  · exact B810631
  · exact B810635
  · exact B810639
  · exact B810643
  · exact B810647
  · exact B810651
  · exact B810655
  · exact B810659
  · exact B810663
  · exact B810667
  · exact B810671
  · exact B810675
  · exact B810679
  · exact B810683
  · exact B810687
  · exact B810691
  · exact B810695
  · exact B810699
  · exact B810703
  · exact B810707
  · exact B810711
  · exact B810715
  · exact B810719
  · exact B810723
  · exact B810727
  · exact B810731
  · exact B810735
  · exact B810739
  · exact B810743
  · exact B810747
  · exact B810751
  · exact B810755
  · exact B810759
  · exact B810763
  · exact B810767
  · exact B810771
  · exact B810775
  · exact B810779
  · exact B810783
  · exact B810787
  · exact B810791
  · exact B810795
  · exact B810799
  · exact B810803
  · exact B810807
  · exact B810811
  · exact B810815
  · exact B810819
  · exact B810823
  · exact B810827
  · exact B810831
  · exact B810835
  · exact B810839
  · exact B810843
  · exact B810847
  · exact B810851
  · exact B810855
  · exact B810859
  · exact B810863
  · exact B810867
  · exact B810871
  · exact B810875
  · exact B810879
  · exact B810883
  · exact B810887
  · exact B810891
  · exact B810895
  · exact B810899
  · exact B810903
  · exact B810907
  · exact B810911
  · exact B810915
  · exact B810919
  · exact B810923
  · exact B810927
  · exact B810931
  · exact B810935
  · exact B810939
  · exact B810943
  · exact B810947
  · exact B810951
  · exact B810955
  · exact B810959
  · exact B810963
  · exact B810967
  · exact B810971
  · exact B810975
  · exact B810979
  · exact B810983
  · exact B810987
  · exact B810991
  · exact B810995
  · exact B810999
  · exact B811003
  · exact B811007
  · exact B811011
  · exact B811015
  · exact B811019
  · exact B811023
  · exact B811027
  · exact B811031
  · exact B811035
  · exact B811039
  · exact B811043
  · exact B811047
  · exact B811051
  · exact B811055
  · exact B811059
  · exact B811063
  · exact B811067
  · exact B811071
  · exact B811075
  · exact B811079
  · exact B811083
  · exact B811087
  · exact B811091
  · exact B811095
  · exact B811099
  · exact B811103
  · exact B811107
  · exact B811111
  · exact B811115
  · exact B811119
  · exact B811123
  · exact B811127
  · exact B811131
  · exact B811135
  · exact B811139
  · exact B811143
  · exact B811147
  · exact B811151
  · exact B811155
  · exact B811159
  · exact B811163
  · exact B811167
  · exact B811171
  · exact B811175
  · exact B811179
  · exact B811183
  · exact B811187
  · exact B811191
  · exact B811195
  · exact B811199
  · exact B811203
  · exact B811207
  · exact B811211
  · exact B811215
  · exact B811219
  · exact B811223
  · exact B811227
  · exact B811231
  · exact B811235
  · exact B811239
  · exact B811243
  · exact B811247
  · exact B811251
  · exact B811255
  · exact B811259
  · exact B811263
  · exact B811267
  · exact B811271
  · exact B811275
  · exact B811279
  · exact B811283
  · exact B811287
  · exact B811291
  · exact B811295
  · exact B811299
  · exact B811303
  · exact B811307
  · exact B811311
  · exact B811315
  · exact B811319
  · exact B811323
  · exact B811327
  · exact B811331
  · exact B811335
  · exact B811339
  · exact B811343
  · exact B811347
  · exact B811351
  · exact B811355
  · exact B811359
  · exact B811363
  · exact B811367
  · exact B811371
  · exact B811375
  · exact B811379
  · exact B811383
  · exact B811387
  · exact B811391
  · exact B811395
  · exact B811399
  · exact B811403
  · exact B811407
  · exact B811411
  · exact B811415
  · exact B811419
  · exact B811423
  · exact B811427
  · exact B811431
  · exact B811435
  · exact B811439
  · exact B811443
  · exact B811447
  · exact B811451
  · exact B811455
  · exact B811459
  · exact B811463
  · exact B811467
  · exact B811471
  · exact B811475
  · exact B811479
  · exact B811483
  · exact B811487
  · exact B811491
  · exact B811495
  · exact B811499
  · exact B811503
  · exact B811507
  · exact B811511
  · exact B811515
  · exact B811519
  · exact B811523
  · exact B811527
  · exact B811531
  · exact B811535
  · exact B811539
  · exact B811543
  · exact B811547
  · exact B811551
  · exact B811555
  · exact B811559
  · exact B811563
  · exact B811567
  · exact B811571
  · exact B811575
  · exact B811579
  · exact B811583
  · exact B811587
  · exact B811591
  · exact B811595
  · exact B811599
  · exact B811603
  · exact B811607
  · exact B811611
  · exact B811615
  · exact B811619
  · exact B811623
  · exact B811627
  · exact B811631
  · exact B811635
  · exact B811639
  · exact B811643
  · exact B811647
  · exact B811651
  · exact B811655
  · exact B811659
  · exact B811663
  · exact B811667
  · exact B811671
  · exact B811675
  · exact B811679
  · exact B811683
  · exact B811687
  · exact B811691
  · exact B811695
  · exact B811699
  · exact B811703
  · exact B811707
  · exact B811711
  · exact B811715
  · exact B811719
  · exact B811723
  · exact B811727
  · exact B811731
  · exact B811735
  · exact B811739
  · exact B811743
  · exact B811747
  · exact B811751
  · exact B811755
  · exact B811759
  · exact B811763
  · exact B811767
  · exact B811771
  · exact B811775
  · exact B811779
  · exact B811783
  · exact B811787
  · exact B811791
  · exact B811795
  · exact B811799
  · exact B811803
  · exact B811807
  · exact B811811
  · exact B811815
  · exact B811819
  · exact B811823
  · exact B811827
  · exact B811831
  · exact B811835
  · exact B811839
  · exact B811843
  · exact B811847
  · exact B811851
  · exact B811855
  · exact B811859
  · exact B811863
  · exact B811867
  · exact B811871
  · exact B811875
  · exact B811879
  · exact B811883
  · exact B811887
  · exact B811891
  · exact B811895
  · exact B811899
  · exact B811903
  · exact B811907
  · exact B811911
  · exact B811915
  · exact B811919
  · exact B811923
  · exact B811927
  · exact B811931
  · exact B811935
  · exact B811939
  · exact B811943
  · exact B811947
  · exact B811951
  · exact B811955
  · exact B811959
  · exact B811963
  · exact B811967
  · exact B811971
  · exact B811975
  · exact B811979
  · exact B811983
  · exact B811987
  · exact B811991
  · exact B811995
  · exact B811999
  · exact B812003
  · exact B812007
  · exact B812011
  · exact B812015
  · exact B812019
  · exact B812023
  · exact B812027
  · exact B812031
  · exact B812035
  · exact B812039
  · exact B812043
  · exact B812047
  · exact B812051
  · exact B812055
  · exact B812059
  · exact B812063
  · exact B812067
  · exact B812071
  · exact B812075
  · exact B812079
  · exact B812083
  · exact B812087
  · exact B812091
  · exact B812095
  · exact B812099
  · exact B812103
  · exact B812107
  · exact B812111
  · exact B812115
  · exact B812119
  · exact B812123
  · exact B812127
  · exact B812131
  · exact B812135
  · exact B812139
  · exact B812143
  · exact B812147
  · exact B812151
  · exact B812155
  · exact B812159
  · exact B812163
  · exact B812167
  · exact B812171
  · exact B812175
  · exact B812179
  · exact B812183
  · exact B812187
  · exact B812191
  · exact B812195
  · exact B812199
  · exact B812203
  · exact B812207
  · exact B812211
  · exact B812215
  · exact B812219
  · exact B812223
  · exact B812227
  · exact B812231
  · exact B812235
  · exact B812239
  · exact B812243
  · exact B812247
  · exact B812251
  · exact B812255
  · exact B812259
  · exact B812263
  · exact B812267
  · exact B812271
  · exact B812275
  · exact B812279
  · exact B812283
  · exact B812287
  · exact B812291
  · exact B812295
  · exact B812299
  · exact B812303
  · exact B812307
  · exact B812311
  · exact B812315
  · exact B812319
  · exact B812323
  · exact B812327
  · exact B812331
  · exact B812335
  · exact B812339
  · exact B812343
  · exact B812347
  · exact B812351
  · exact B812355
  · exact B812359
  · exact B812363
  · exact B812367
  · exact B812371
  · exact B812375
  · exact B812379
  · exact B812383
  · exact B812387
  · exact B812391
  · exact B812395
  · exact B812399
  · exact B812403
  · exact B812407
  · exact B812411
  · exact B812415
  · exact B812419
  · exact B812423
  · exact B812427
  · exact B812431
  · exact B812435
  · exact B812439
  · exact B812443
  · exact B812447
  · exact B812451
  · exact B812455
  · exact B812459
  · exact B812463
  · exact B812467
  · exact B812471
  · exact B812475
  · exact B812479
  · exact B812483
  · exact B812487
  · exact B812491
  · exact B812495
  · exact B812499
  · exact B812503
  · exact B812507
  · exact B812511
  · exact B812515
  · exact B812519
  · exact B812523
  · exact B812527
  · exact B812531
  · exact B812535
  · exact B812539
  · exact B812543
  · exact B812547
  · exact B812551
  · exact B812555
  · exact B812559
  · exact B812563
  · exact B812567
  · exact B812571
  · exact B812575
  · exact B812579
  · exact B812583
  · exact B812587
  · exact B812591
  · exact B812595
  · exact B812599
  · exact B812603
  · exact B812607
  · exact B812611
  · exact B812615
  · exact B812619
  · exact B812623
  · exact B812627
  · exact B812631
  · exact B812635
  · exact B812639
  · exact B812643
  · exact B812647
  · exact B812651
  · exact B812655
  · exact B812659
  · exact B812663
  · exact B812667
  · exact B812671
  · exact B812675
  · exact B812679
  · exact B812683
  · exact B812687
  · exact B812691
  · exact B812695
  · exact B812699
  · exact B812703
  · exact B812707
  · exact B812711
  · exact B812715
  · exact B812719
  · exact B812723
  · exact B812727
  · exact B812731
  · exact B812735
  · exact B812739
  · exact B812743
  · exact B812747
  · exact B812751
  · exact B812755
  · exact B812759
  · exact B812763
  · exact B812767
  · exact B812771
  · exact B812775
  · exact B812779
  · exact B812783
  · exact B812787
  · exact B812791
  · exact B812795
  · exact B812799
  · exact B812803
  · exact B812807
  · exact B812811
  · exact B812815
  · exact B812819
  · exact B812823
  · exact B812827
  · exact B812831
  · exact B812835
  · exact B812839
  · exact B812843
  · exact B812847
  · exact B812851
  · exact B812855
  · exact B812859
  · exact B812863
  · exact B812867
  · exact B812871
  · exact B812875
  · exact B812879
  · exact B812883
  · exact B812887
  · exact B812891
  · exact B812895
  · exact B812899
  · exact B812903
  · exact B812907
  · exact B812911
  · exact B812915
  · exact B812919
  · exact B812923
  · exact B812927
  · exact B812931
  · exact B812935
  · exact B812939
  · exact B812943
  · exact B812947
  · exact B812951
  · exact B812955
  · exact B812959
  · exact B812963
  · exact B812967
  · exact B812971
  · exact B812975
  · exact B812979
  · exact B812983
  · exact B812987
  · exact B812991
  · exact B812995
  · exact B812999
  · exact B813003
  · exact B813007
  · exact B813011
  · exact B813015
  · exact B813019
  · exact B813023
  · exact B813027
  · exact B813031
  · exact B813035
  · exact B813039
  · exact B813043
  · exact B813047
  · exact B813051
  · exact B813055
  · exact B813059
  · exact B813063
  · exact B813067
  · exact B813071
  · exact B813075
  · exact B813079
  · exact B813083
  · exact B813087
  · exact B813091
  · exact B813095
  · exact B813099
  · exact B813103
  · exact B813107
  · exact B813111
  · exact B813115
  · exact B813119
  · exact B813123
  · exact B813127
  · exact B813131
  · exact B813135
  · exact B813139
  · exact B813143

theorem C1 (j : ℕ) (h1 : 203286 ≤ j) (h2 : j ≤ 203585) : Blo 810345 (4 * j + 3) := by
  interval_cases j
  · exact B813147
  · exact B813151
  · exact B813155
  · exact B813159
  · exact B813163
  · exact B813167
  · exact B813171
  · exact B813175
  · exact B813179
  · exact B813183
  · exact B813187
  · exact B813191
  · exact B813195
  · exact B813199
  · exact B813203
  · exact B813207
  · exact B813211
  · exact B813215
  · exact B813219
  · exact B813223
  · exact B813227
  · exact B813231
  · exact B813235
  · exact B813239
  · exact B813243
  · exact B813247
  · exact B813251
  · exact B813255
  · exact B813259
  · exact B813263
  · exact B813267
  · exact B813271
  · exact B813275
  · exact B813279
  · exact B813283
  · exact B813287
  · exact B813291
  · exact B813295
  · exact B813299
  · exact B813303
  · exact B813307
  · exact B813311
  · exact B813315
  · exact B813319
  · exact B813323
  · exact B813327
  · exact B813331
  · exact B813335
  · exact B813339
  · exact B813343
  · exact B813347
  · exact B813351
  · exact B813355
  · exact B813359
  · exact B813363
  · exact B813367
  · exact B813371
  · exact B813375
  · exact B813379
  · exact B813383
  · exact B813387
  · exact B813391
  · exact B813395
  · exact B813399
  · exact B813403
  · exact B813407
  · exact B813411
  · exact B813415
  · exact B813419
  · exact B813423
  · exact B813427
  · exact B813431
  · exact B813435
  · exact B813439
  · exact B813443
  · exact B813447
  · exact B813451
  · exact B813455
  · exact B813459
  · exact B813463
  · exact B813467
  · exact B813471
  · exact B813475
  · exact B813479
  · exact B813483
  · exact B813487
  · exact B813491
  · exact B813495
  · exact B813499
  · exact B813503
  · exact B813507
  · exact B813511
  · exact B813515
  · exact B813519
  · exact B813523
  · exact B813527
  · exact B813531
  · exact B813535
  · exact B813539
  · exact B813543
  · exact B813547
  · exact B813551
  · exact B813555
  · exact B813559
  · exact B813563
  · exact B813567
  · exact B813571
  · exact B813575
  · exact B813579
  · exact B813583
  · exact B813587
  · exact B813591
  · exact B813595
  · exact B813599
  · exact B813603
  · exact B813607
  · exact B813611
  · exact B813615
  · exact B813619
  · exact B813623
  · exact B813627
  · exact B813631
  · exact B813635
  · exact B813639
  · exact B813643
  · exact B813647
  · exact B813651
  · exact B813655
  · exact B813659
  · exact B813663
  · exact B813667
  · exact B813671
  · exact B813675
  · exact B813679
  · exact B813683
  · exact B813687
  · exact B813691
  · exact B813695
  · exact B813699
  · exact B813703
  · exact B813707
  · exact B813711
  · exact B813715
  · exact B813719
  · exact B813723
  · exact B813727
  · exact B813731
  · exact B813735
  · exact B813739
  · exact B813743
  · exact B813747
  · exact B813751
  · exact B813755
  · exact B813759
  · exact B813763
  · exact B813767
  · exact B813771
  · exact B813775
  · exact B813779
  · exact B813783
  · exact B813787
  · exact B813791
  · exact B813795
  · exact B813799
  · exact B813803
  · exact B813807
  · exact B813811
  · exact B813815
  · exact B813819
  · exact B813823
  · exact B813827
  · exact B813831
  · exact B813835
  · exact B813839
  · exact B813843
  · exact B813847
  · exact B813851
  · exact B813855
  · exact B813859
  · exact B813863
  · exact B813867
  · exact B813871
  · exact B813875
  · exact B813879
  · exact B813883
  · exact B813887
  · exact B813891
  · exact B813895
  · exact B813899
  · exact B813903
  · exact B813907
  · exact B813911
  · exact B813915
  · exact B813919
  · exact B813923
  · exact B813927
  · exact B813931
  · exact B813935
  · exact B813939
  · exact B813943
  · exact B813947
  · exact B813951
  · exact B813955
  · exact B813959
  · exact B813963
  · exact B813967
  · exact B813971
  · exact B813975
  · exact B813979
  · exact B813983
  · exact B813987
  · exact B813991
  · exact B813995
  · exact B813999
  · exact B814003
  · exact B814007
  · exact B814011
  · exact B814015
  · exact B814019
  · exact B814023
  · exact B814027
  · exact B814031
  · exact B814035
  · exact B814039
  · exact B814043
  · exact B814047
  · exact B814051
  · exact B814055
  · exact B814059
  · exact B814063
  · exact B814067
  · exact B814071
  · exact B814075
  · exact B814079
  · exact B814083
  · exact B814087
  · exact B814091
  · exact B814095
  · exact B814099
  · exact B814103
  · exact B814107
  · exact B814111
  · exact B814115
  · exact B814119
  · exact B814123
  · exact B814127
  · exact B814131
  · exact B814135
  · exact B814139
  · exact B814143
  · exact B814147
  · exact B814151
  · exact B814155
  · exact B814159
  · exact B814163
  · exact B814167
  · exact B814171
  · exact B814175
  · exact B814179
  · exact B814183
  · exact B814187
  · exact B814191
  · exact B814195
  · exact B814199
  · exact B814203
  · exact B814207
  · exact B814211
  · exact B814215
  · exact B814219
  · exact B814223
  · exact B814227
  · exact B814231
  · exact B814235
  · exact B814239
  · exact B814243
  · exact B814247
  · exact B814251
  · exact B814255
  · exact B814259
  · exact B814263
  · exact B814267
  · exact B814271
  · exact B814275
  · exact B814279
  · exact B814283
  · exact B814287
  · exact B814291
  · exact B814295
  · exact B814299
  · exact B814303
  · exact B814307
  · exact B814311
  · exact B814315
  · exact B814319
  · exact B814323
  · exact B814327
  · exact B814331
  · exact B814335
  · exact B814339
  · exact B814343

theorem solution (m : ℕ) (hlo : 810345 ≤ m) (hhi : m ≤ 814345) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 202586 ≤ j := by omega
    have hj2 : j ≤ 203585 := by omega
    have hb : Blo 810345 (4 * j + 3) := by
      rcases Nat.lt_or_ge j 203286 with hc0 | hc0
      · exact C0 j (by omega) (by omega)
      exact C1 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
