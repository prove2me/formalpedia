-- Prove2me | solution 1 for syracuse_descends_range_491791_495791
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-09T17:48:12.690267+00:00
-- url     : https://prove2.me/submissions/1d4cdb09-f54b-48d9-a41f-6daa1957aa76

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


theorem B1441813 : Blo 491791 1441813 := bbase (se 6 (by rfl) ⟨33792, by rfl⟩ : syracuseStep 1441813 = 67585) (by norm_num)
theorem B557077 : Blo 491791 557077 := bbase (se 6 (by rfl) ⟨13056, by rfl⟩ : syracuseStep 557077 = 26113) (by norm_num)
theorem B557113 : Blo 491791 557113 := bbase (se 2 (by rfl) ⟨208917, by rfl⟩ : syracuseStep 557113 = 417835) (by norm_num)
theorem B622657 : Blo 491791 622657 := bbase (se 2 (by rfl) ⟨233496, by rfl⟩ : syracuseStep 622657 = 466993) (by norm_num)
theorem B1245253 : Blo 491791 1245253 := bbase (se 4 (by rfl) ⟨116742, by rfl⟩ : syracuseStep 1245253 = 233485) (by norm_num)
theorem B1114181 : Blo 491791 1114181 := bbase (se 4 (by rfl) ⟨104454, by rfl⟩ : syracuseStep 1114181 = 208909) (by norm_num)
theorem B557149 : Blo 491791 557149 := bbase (se 3 (by rfl) ⟨104465, by rfl⟩ : syracuseStep 557149 = 208931) (by norm_num)
theorem B557185 : Blo 491791 557185 := bbase (se 2 (by rfl) ⟨208944, by rfl⟩ : syracuseStep 557185 = 417889) (by norm_num)
theorem B1114253 : Blo 491791 1114253 := bbase (se 3 (by rfl) ⟨208922, by rfl⟩ : syracuseStep 1114253 = 417845) (by norm_num)
theorem B557221 : Blo 491791 557221 := bbase (se 4 (by rfl) ⟨52239, by rfl⟩ : syracuseStep 557221 = 104479) (by norm_num)
theorem B1245365 : Blo 491791 1245365 := bbase (se 5 (by rfl) ⟨58376, by rfl⟩ : syracuseStep 1245365 = 116753) (by norm_num)
theorem B557257 : Blo 491791 557257 := bbase (se 2 (by rfl) ⟨208971, by rfl⟩ : syracuseStep 557257 = 417943) (by norm_num)
theorem B1114325 : Blo 491791 1114325 := bbase (se 7 (by rfl) ⟨13058, by rfl⟩ : syracuseStep 1114325 = 26117) (by norm_num)
theorem B622829 : Blo 491791 622829 := bbase (se 3 (by rfl) ⟨116780, by rfl⟩ : syracuseStep 622829 = 233561) (by norm_num)
theorem B557293 : Blo 491791 557293 := bbase (se 3 (by rfl) ⟨104492, by rfl⟩ : syracuseStep 557293 = 208985) (by norm_num)
theorem B557329 : Blo 491791 557329 := bbase (se 2 (by rfl) ⟨208998, by rfl⟩ : syracuseStep 557329 = 417997) (by norm_num)
theorem B1114397 : Blo 491791 1114397 := bbase (se 3 (by rfl) ⟨208949, by rfl⟩ : syracuseStep 1114397 = 417899) (by norm_num)
theorem B622885 : Blo 491791 622885 := bbase (se 4 (by rfl) ⟨58395, by rfl⟩ : syracuseStep 622885 = 116791) (by norm_num)
theorem B1671461 : Blo 491791 1671461 := bbase (se 4 (by rfl) ⟨156699, by rfl⟩ : syracuseStep 1671461 = 313399) (by norm_num)
theorem B1507621 : Blo 491791 1507621 := bbase (se 4 (by rfl) ⟨141339, by rfl⟩ : syracuseStep 1507621 = 282679) (by norm_num)
theorem B557365 : Blo 491791 557365 := bbase (se 5 (by rfl) ⟨26126, by rfl⟩ : syracuseStep 557365 = 52253) (by norm_num)
theorem B557401 : Blo 491791 557401 := bbase (se 2 (by rfl) ⟨209025, by rfl⟩ : syracuseStep 557401 = 418051) (by norm_num)
theorem B1114469 : Blo 491791 1114469 := bbase (se 4 (by rfl) ⟨104481, by rfl⟩ : syracuseStep 1114469 = 208963) (by norm_num)
theorem B1245557 : Blo 491791 1245557 := bbase (se 5 (by rfl) ⟨58385, by rfl⟩ : syracuseStep 1245557 = 116771) (by norm_num)
theorem B557437 : Blo 491791 557437 := bbase (se 3 (by rfl) ⟨104519, by rfl⟩ : syracuseStep 557437 = 209039) (by norm_num)
theorem B622981 : Blo 491791 622981 := bbase (se 4 (by rfl) ⟨58404, by rfl⟩ : syracuseStep 622981 = 116809) (by norm_num)
theorem B557473 : Blo 491791 557473 := bbase (se 2 (by rfl) ⟨209052, by rfl⟩ : syracuseStep 557473 = 418105) (by norm_num)
theorem B1114541 : Blo 491791 1114541 := bbase (se 3 (by rfl) ⟨208976, by rfl⟩ : syracuseStep 1114541 = 417953) (by norm_num)
theorem B950717 : Blo 491791 950717 := bbase (se 3 (by rfl) ⟨178259, by rfl⟩ : syracuseStep 950717 = 356519) (by norm_num)
theorem B557509 : Blo 491791 557509 := bbase (se 4 (by rfl) ⟨52266, by rfl⟩ : syracuseStep 557509 = 104533) (by norm_num)
theorem B557545 : Blo 491791 557545 := bbase (se 2 (by rfl) ⟨209079, by rfl⟩ : syracuseStep 557545 = 418159) (by norm_num)
theorem B1114613 : Blo 491791 1114613 := bbase (se 5 (by rfl) ⟨52247, by rfl⟩ : syracuseStep 1114613 = 104495) (by norm_num)
theorem B557581 : Blo 491791 557581 := bbase (se 3 (by rfl) ⟨104546, by rfl⟩ : syracuseStep 557581 = 209093) (by norm_num)
theorem B623153 : Blo 491791 623153 := bbase (se 2 (by rfl) ⟨233682, by rfl⟩ : syracuseStep 623153 = 467365) (by norm_num)
theorem B557617 : Blo 491791 557617 := bbase (se 2 (by rfl) ⟨209106, by rfl⟩ : syracuseStep 557617 = 418213) (by norm_num)
theorem B1114685 : Blo 491791 1114685 := bbase (se 3 (by rfl) ⟨209003, by rfl⟩ : syracuseStep 1114685 = 418007) (by norm_num)
theorem B557653 : Blo 491791 557653 := bbase (se 8 (by rfl) ⟨3267, by rfl⟩ : syracuseStep 557653 = 6535) (by norm_num)
theorem B623209 : Blo 491791 623209 := bbase (se 2 (by rfl) ⟨233703, by rfl⟩ : syracuseStep 623209 = 467407) (by norm_num)
theorem B557689 : Blo 491791 557689 := bbase (se 2 (by rfl) ⟨209133, by rfl⟩ : syracuseStep 557689 = 418267) (by norm_num)
theorem B1114757 : Blo 491791 1114757 := bbase (se 4 (by rfl) ⟨104508, by rfl⟩ : syracuseStep 1114757 = 209017) (by norm_num)
theorem B557725 : Blo 491791 557725 := bbase (se 3 (by rfl) ⟨104573, by rfl⟩ : syracuseStep 557725 = 209147) (by norm_num)
theorem B557761 : Blo 491791 557761 := bbase (se 2 (by rfl) ⟨209160, by rfl⟩ : syracuseStep 557761 = 418321) (by norm_num)
theorem B623305 : Blo 491791 623305 := bbase (se 2 (by rfl) ⟨233739, by rfl⟩ : syracuseStep 623305 = 467479) (by norm_num)
theorem B1245901 : Blo 491791 1245901 := bbase (se 3 (by rfl) ⟨233606, by rfl⟩ : syracuseStep 1245901 = 467213) (by norm_num)
theorem B1114829 : Blo 491791 1114829 := bbase (se 3 (by rfl) ⟨209030, by rfl⟩ : syracuseStep 1114829 = 418061) (by norm_num)
theorem B1671893 : Blo 491791 1671893 := bbase (se 7 (by rfl) ⟨19592, by rfl⟩ : syracuseStep 1671893 = 39185) (by norm_num)
theorem B1114901 : Blo 491791 1114901 := bbase (se 6 (by rfl) ⟨26130, by rfl⟩ : syracuseStep 1114901 = 52261) (by norm_num)
theorem B1246013 : Blo 491791 1246013 := bbase (se 3 (by rfl) ⟨233627, by rfl⟩ : syracuseStep 1246013 = 467255) (by norm_num)
theorem B1114973 : Blo 491791 1114973 := bbase (se 3 (by rfl) ⟨209057, by rfl⟩ : syracuseStep 1114973 = 418115) (by norm_num)
theorem B623477 : Blo 491791 623477 := bbase (se 5 (by rfl) ⟨29225, by rfl⟩ : syracuseStep 623477 = 58451) (by norm_num)
theorem B525205 : Blo 491791 525205 := bbase (se 6 (by rfl) ⟨12309, by rfl⟩ : syracuseStep 525205 = 24619) (by norm_num)
theorem B1115045 : Blo 491791 1115045 := bbase (se 4 (by rfl) ⟨104535, by rfl⟩ : syracuseStep 1115045 = 209071) (by norm_num)
theorem B623533 : Blo 491791 623533 := bbase (se 3 (by rfl) ⟨116912, by rfl⟩ : syracuseStep 623533 = 233825) (by norm_num)
theorem B1115117 : Blo 491791 1115117 := bbase (se 3 (by rfl) ⟨209084, by rfl⟩ : syracuseStep 1115117 = 418169) (by norm_num)
theorem B1246205 : Blo 491791 1246205 := bbase (se 3 (by rfl) ⟨233663, by rfl⟩ : syracuseStep 1246205 = 467327) (by norm_num)
theorem B2491397 : Blo 491791 2491397 := bbase (se 4 (by rfl) ⟨233568, by rfl⟩ : syracuseStep 2491397 = 467137) (by norm_num)
theorem B623629 : Blo 491791 623629 := bbase (se 3 (by rfl) ⟨116930, by rfl⟩ : syracuseStep 623629 = 233861) (by norm_num)
theorem B1115189 : Blo 491791 1115189 := bbase (se 5 (by rfl) ⟨52274, by rfl⟩ : syracuseStep 1115189 = 104549) (by norm_num)
theorem B1410149 : Blo 491791 1410149 := bbase (se 4 (by rfl) ⟨132201, by rfl⟩ : syracuseStep 1410149 = 264403) (by norm_num)
theorem B1115261 : Blo 491791 1115261 := bbase (se 3 (by rfl) ⟨209111, by rfl⟩ : syracuseStep 1115261 = 418223) (by norm_num)
theorem B1672325 : Blo 491791 1672325 := bbase (se 4 (by rfl) ⟨156780, by rfl⟩ : syracuseStep 1672325 = 313561) (by norm_num)
theorem B525457 : Blo 491791 525457 := bbase (se 2 (by rfl) ⟨197046, by rfl⟩ : syracuseStep 525457 = 394093) (by norm_num)
theorem B525461 : Blo 491791 525461 := bbase (se 6 (by rfl) ⟨12315, by rfl⟩ : syracuseStep 525461 = 24631) (by norm_num)
theorem B623801 : Blo 491791 623801 := bbase (se 2 (by rfl) ⟨233925, by rfl⟩ : syracuseStep 623801 = 467851) (by norm_num)
theorem B1115333 : Blo 491791 1115333 := bbase (se 4 (by rfl) ⟨104562, by rfl⟩ : syracuseStep 1115333 = 209125) (by norm_num)
theorem B951517 : Blo 491791 951517 := bbase (se 3 (by rfl) ⟨178409, by rfl⟩ : syracuseStep 951517 = 356819) (by norm_num)
theorem B591077 : Blo 491791 591077 := bbase (se 4 (by rfl) ⟨55413, by rfl⟩ : syracuseStep 591077 = 110827) (by norm_num)
theorem B623857 : Blo 491791 623857 := bbase (se 2 (by rfl) ⟨233946, by rfl⟩ : syracuseStep 623857 = 467893) (by norm_num)
theorem B1115405 : Blo 491791 1115405 := bbase (se 3 (by rfl) ⟨209138, by rfl⟩ : syracuseStep 1115405 = 418277) (by norm_num)
theorem B3736853 : Blo 491791 3736853 := bbase (se 6 (by rfl) ⟨87582, by rfl⟩ : syracuseStep 3736853 = 175165) (by norm_num)
theorem B623953 : Blo 491791 623953 := bbase (se 2 (by rfl) ⟨233982, by rfl⟩ : syracuseStep 623953 = 467965) (by norm_num)
theorem B1246549 : Blo 491791 1246549 := bbase (se 12 (by rfl) ⟨456, by rfl⟩ : syracuseStep 1246549 = 913) (by norm_num)
theorem B1115477 : Blo 491791 1115477 := bbase (se 12 (by rfl) ⟨408, by rfl⟩ : syracuseStep 1115477 = 817) (by norm_num)
theorem B951733 : Blo 491791 951733 := bbase (se 5 (by rfl) ⟨44612, by rfl⟩ : syracuseStep 951733 = 89225) (by norm_num)
theorem B1246661 : Blo 491791 1246661 := bbase (se 4 (by rfl) ⟨116874, by rfl⟩ : syracuseStep 1246661 = 233749) (by norm_num)
theorem B1705445 : Blo 491791 1705445 := bbase (se 4 (by rfl) ⟨159885, by rfl⟩ : syracuseStep 1705445 = 319771) (by norm_num)
theorem B624125 : Blo 491791 624125 := bbase (se 3 (by rfl) ⟨117023, by rfl⟩ : syracuseStep 624125 = 234047) (by norm_num)
theorem B787981 : Blo 491791 787981 := bbase (se 3 (by rfl) ⟨147746, by rfl⟩ : syracuseStep 787981 = 295493) (by norm_num)
theorem B591409 : Blo 491791 591409 := bbase (se 2 (by rfl) ⟨221778, by rfl⟩ : syracuseStep 591409 = 443557) (by norm_num)
theorem B624181 : Blo 491791 624181 := bbase (se 5 (by rfl) ⟨29258, by rfl⟩ : syracuseStep 624181 = 58517) (by norm_num)
theorem B1672757 : Blo 491791 1672757 := bbase (se 5 (by rfl) ⟨78410, by rfl⟩ : syracuseStep 1672757 = 156821) (by norm_num)
theorem B1246853 : Blo 491791 1246853 := bbase (se 4 (by rfl) ⟨116892, by rfl⟩ : syracuseStep 1246853 = 233785) (by norm_num)
theorem B624277 : Blo 491791 624277 := bbase (se 6 (by rfl) ⟨14631, by rfl⟩ : syracuseStep 624277 = 29263) (by norm_num)
theorem B526025 : Blo 491791 526025 := bbase (se 2 (by rfl) ⟨197259, by rfl⟩ : syracuseStep 526025 = 394519) (by norm_num)
theorem B1410821 : Blo 491791 1410821 := bbase (se 4 (by rfl) ⟨132264, by rfl⟩ : syracuseStep 1410821 = 264529) (by norm_num)
theorem B624449 : Blo 491791 624449 := bbase (se 2 (by rfl) ⟨234168, by rfl⟩ : syracuseStep 624449 = 468337) (by norm_num)
theorem B624505 : Blo 491791 624505 := bbase (se 2 (by rfl) ⟨234189, by rfl⟩ : syracuseStep 624505 = 468379) (by norm_num)
theorem B526213 : Blo 491791 526213 := bbase (se 4 (by rfl) ⟨49332, by rfl⟩ : syracuseStep 526213 = 98665) (by norm_num)
theorem B1869749 : Blo 491791 1869749 := bbase (se 5 (by rfl) ⟨87644, by rfl⟩ : syracuseStep 1869749 = 175289) (by norm_num)
theorem B2000821 : Blo 491791 2000821 := bbase (se 5 (by rfl) ⟨93788, by rfl⟩ : syracuseStep 2000821 = 187577) (by norm_num)
theorem B624601 : Blo 491791 624601 := bbase (se 2 (by rfl) ⟨234225, by rfl⟩ : syracuseStep 624601 = 468451) (by norm_num)
theorem B1247197 : Blo 491791 1247197 := bbase (se 3 (by rfl) ⟨233849, by rfl⟩ : syracuseStep 1247197 = 467699) (by norm_num)
theorem B1673189 : Blo 491791 1673189 := bbase (se 4 (by rfl) ⟨156861, by rfl⟩ : syracuseStep 1673189 = 313723) (by norm_num)
theorem B1114109 : Blo 491791 1114109 := bbase (se 3 (by rfl) ⟨208895, by rfl⟩ : syracuseStep 1114109 = 417791) (by norm_num)
theorem B1247309 : Blo 491791 1247309 := bbase (se 3 (by rfl) ⟨233870, by rfl⟩ : syracuseStep 1247309 = 467741) (by norm_num)
theorem B624773 : Blo 491791 624773 := bbase (se 4 (by rfl) ⟨58572, by rfl⟩ : syracuseStep 624773 = 117145) (by norm_num)
theorem B788653 : Blo 491791 788653 := bbase (se 3 (by rfl) ⟨147872, by rfl⟩ : syracuseStep 788653 = 295745) (by norm_num)
theorem B1411253 : Blo 491791 1411253 := bbase (se 5 (by rfl) ⟨66152, by rfl⟩ : syracuseStep 1411253 = 132305) (by norm_num)
theorem B624829 : Blo 491791 624829 := bbase (se 3 (by rfl) ⟨117155, by rfl⟩ : syracuseStep 624829 = 234311) (by norm_num)
theorem B1870037 : Blo 491791 1870037 := bbase (se 7 (by rfl) ⟨21914, by rfl⟩ : syracuseStep 1870037 = 43829) (by norm_num)
theorem B592105 : Blo 491791 592105 := bbase (se 2 (by rfl) ⟨222039, by rfl⟩ : syracuseStep 592105 = 444079) (by norm_num)
theorem B1247501 : Blo 491791 1247501 := bbase (se 3 (by rfl) ⟨233906, by rfl⟩ : syracuseStep 1247501 = 467813) (by norm_num)
theorem B2492693 : Blo 491791 2492693 := bbase (se 6 (by rfl) ⟨58422, by rfl⟩ : syracuseStep 2492693 = 116845) (by norm_num)
theorem B592153 : Blo 491791 592153 := bbase (se 2 (by rfl) ⟨222057, by rfl⟩ : syracuseStep 592153 = 444115) (by norm_num)
theorem B624925 : Blo 491791 624925 := bbase (se 3 (by rfl) ⟨117173, by rfl⟩ : syracuseStep 624925 = 234347) (by norm_num)
theorem B625097 : Blo 491791 625097 := bbase (se 2 (by rfl) ⟨234411, by rfl⟩ : syracuseStep 625097 = 468823) (by norm_num)
theorem B1051093 : Blo 491791 1051093 := bbase (se 7 (by rfl) ⟨12317, by rfl⟩ : syracuseStep 1051093 = 24635) (by norm_num)
theorem B625153 : Blo 491791 625153 := bbase (se 2 (by rfl) ⟨234432, by rfl⟩ : syracuseStep 625153 = 468865) (by norm_num)
theorem B1051213 : Blo 491791 1051213 := bbase (se 3 (by rfl) ⟨197102, by rfl⟩ : syracuseStep 1051213 = 394205) (by norm_num)
theorem B789077 : Blo 491791 789077 := bbase (se 8 (by rfl) ⟨4623, by rfl⟩ : syracuseStep 789077 = 9247) (by norm_num)
theorem B625249 : Blo 491791 625249 := bbase (se 2 (by rfl) ⟨234468, by rfl⟩ : syracuseStep 625249 = 468937) (by norm_num)
theorem B1247845 : Blo 491791 1247845 := bbase (se 4 (by rfl) ⟨116985, by rfl⟩ : syracuseStep 1247845 = 233971) (by norm_num)
theorem B527033 : Blo 491791 527033 := bbase (se 2 (by rfl) ⟨197637, by rfl⟩ : syracuseStep 527033 = 395275) (by norm_num)
theorem B1247957 : Blo 491791 1247957 := bbase (se 7 (by rfl) ⟨14624, by rfl⟩ : syracuseStep 1247957 = 29249) (by norm_num)
theorem B625421 : Blo 491791 625421 := bbase (se 3 (by rfl) ⟨117266, by rfl⟩ : syracuseStep 625421 = 234533) (by norm_num)
theorem B625477 : Blo 491791 625477 := bbase (se 4 (by rfl) ⟨58638, by rfl⟩ : syracuseStep 625477 = 117277) (by norm_num)
theorem B1051469 : Blo 491791 1051469 := bbase (se 3 (by rfl) ⟨197150, by rfl⟩ : syracuseStep 1051469 = 394301) (by norm_num)
theorem B789365 : Blo 491791 789365 := bbase (se 5 (by rfl) ⟨37001, by rfl⟩ : syracuseStep 789365 = 74003) (by norm_num)
theorem B1248149 : Blo 491791 1248149 := bbase (se 6 (by rfl) ⟨29253, by rfl⟩ : syracuseStep 1248149 = 58507) (by norm_num)
theorem B625573 : Blo 491791 625573 := bbase (se 4 (by rfl) ⟨58647, by rfl⟩ : syracuseStep 625573 = 117295) (by norm_num)
theorem B1575973 : Blo 491791 1575973 := bbase (se 4 (by rfl) ⟨147747, by rfl⟩ : syracuseStep 1575973 = 295495) (by norm_num)
theorem B887869 : Blo 491791 887869 := bbase (se 3 (by rfl) ⟨166475, by rfl⟩ : syracuseStep 887869 = 332951) (by norm_num)
theorem B625745 : Blo 491791 625745 := bbase (se 2 (by rfl) ⟨234654, by rfl⟩ : syracuseStep 625745 = 469309) (by norm_num)
theorem B527477 : Blo 491791 527477 := bbase (se 5 (by rfl) ⟨24725, by rfl⟩ : syracuseStep 527477 = 49451) (by norm_num)
theorem B625801 : Blo 491791 625801 := bbase (se 2 (by rfl) ⟨234675, by rfl⟩ : syracuseStep 625801 = 469351) (by norm_num)
theorem B625897 : Blo 491791 625897 := bbase (se 2 (by rfl) ⟨234711, by rfl⟩ : syracuseStep 625897 = 469423) (by norm_num)
theorem B1248493 : Blo 491791 1248493 := bbase (se 3 (by rfl) ⟨234092, by rfl⟩ : syracuseStep 1248493 = 468185) (by norm_num)
theorem B593201 : Blo 491791 593201 := bbase (se 2 (by rfl) ⟨222450, by rfl⟩ : syracuseStep 593201 = 444901) (by norm_num)
theorem B1248605 : Blo 491791 1248605 := bbase (se 3 (by rfl) ⟨234113, by rfl⟩ : syracuseStep 1248605 = 468227) (by norm_num)
theorem B888173 : Blo 491791 888173 := bbase (se 3 (by rfl) ⟨166532, by rfl⟩ : syracuseStep 888173 = 333065) (by norm_num)
theorem B527725 : Blo 491791 527725 := bbase (se 3 (by rfl) ⟨98948, by rfl⟩ : syracuseStep 527725 = 197897) (by norm_num)
theorem B1871221 : Blo 491791 1871221 := bbase (se 5 (by rfl) ⟨87713, by rfl⟩ : syracuseStep 1871221 = 175427) (by norm_num)
theorem B626069 : Blo 491791 626069 := bbase (se 6 (by rfl) ⟨14673, by rfl⟩ : syracuseStep 626069 = 29347) (by norm_num)
theorem B1183133 : Blo 491791 1183133 := bbase (se 3 (by rfl) ⟨221837, by rfl⟩ : syracuseStep 1183133 = 443675) (by norm_num)
theorem B626125 : Blo 491791 626125 := bbase (se 3 (by rfl) ⟨117398, by rfl⟩ : syracuseStep 626125 = 234797) (by norm_num)
theorem B855517 : Blo 491791 855517 := bbase (se 3 (by rfl) ⟨160409, by rfl⟩ : syracuseStep 855517 = 320819) (by norm_num)
theorem B1248797 : Blo 491791 1248797 := bbase (se 3 (by rfl) ⟨234149, by rfl⟩ : syracuseStep 1248797 = 468299) (by norm_num)
theorem B2493989 : Blo 491791 2493989 := bbase (se 4 (by rfl) ⟨233811, by rfl⟩ : syracuseStep 2493989 = 467623) (by norm_num)
theorem B626221 : Blo 491791 626221 := bbase (se 3 (by rfl) ⟨117416, by rfl⟩ : syracuseStep 626221 = 234833) (by norm_num)
theorem B593509 : Blo 491791 593509 := bbase (se 4 (by rfl) ⟨55641, by rfl⟩ : syracuseStep 593509 = 111283) (by norm_num)
theorem B790165 : Blo 491791 790165 := bbase (se 6 (by rfl) ⟨18519, by rfl⟩ : syracuseStep 790165 = 37039) (by norm_num)
theorem B1871525 : Blo 491791 1871525 := bbase (se 4 (by rfl) ⟨175455, by rfl⟩ : syracuseStep 1871525 = 350911) (by norm_num)
theorem B1052357 : Blo 491791 1052357 := bbase (se 4 (by rfl) ⟨98658, by rfl⟩ : syracuseStep 1052357 = 197317) (by norm_num)
theorem B626393 : Blo 491791 626393 := bbase (se 2 (by rfl) ⟨234897, by rfl⟩ : syracuseStep 626393 = 469795) (by norm_num)
theorem B593677 : Blo 491791 593677 := bbase (se 3 (by rfl) ⟨111314, by rfl⟩ : syracuseStep 593677 = 222629) (by norm_num)
theorem B626449 : Blo 491791 626449 := bbase (se 2 (by rfl) ⟨234918, by rfl⟩ : syracuseStep 626449 = 469837) (by norm_num)
theorem B528157 : Blo 491791 528157 := bbase (se 3 (by rfl) ⟨99029, by rfl⟩ : syracuseStep 528157 = 198059) (by norm_num)
theorem B528229 : Blo 491791 528229 := bbase (se 4 (by rfl) ⟨49521, by rfl⟩ : syracuseStep 528229 = 99043) (by norm_num)
theorem B626545 : Blo 491791 626545 := bbase (se 2 (by rfl) ⟨234954, by rfl⟩ : syracuseStep 626545 = 469909) (by norm_num)
theorem B1249141 : Blo 491791 1249141 := bbase (se 5 (by rfl) ⟨58553, by rfl⟩ : syracuseStep 1249141 = 117107) (by norm_num)
theorem B561053 : Blo 491791 561053 := bbase (se 3 (by rfl) ⟨105197, by rfl⟩ : syracuseStep 561053 = 210395) (by norm_num)
theorem B1052597 : Blo 491791 1052597 := bbase (se 5 (by rfl) ⟨49340, by rfl⟩ : syracuseStep 1052597 = 98681) (by norm_num)
theorem B593873 : Blo 491791 593873 := bbase (se 2 (by rfl) ⟨222702, by rfl⟩ : syracuseStep 593873 = 445405) (by norm_num)
theorem B1249253 : Blo 491791 1249253 := bbase (se 4 (by rfl) ⟨117117, by rfl⟩ : syracuseStep 1249253 = 234235) (by norm_num)
theorem B626717 : Blo 491791 626717 := bbase (se 3 (by rfl) ⟨117509, by rfl⟩ : syracuseStep 626717 = 235019) (by norm_num)
theorem B626773 : Blo 491791 626773 := bbase (se 8 (by rfl) ⟨3672, by rfl⟩ : syracuseStep 626773 = 7345) (by norm_num)
theorem B1249445 : Blo 491791 1249445 := bbase (se 4 (by rfl) ⟨117135, by rfl⟩ : syracuseStep 1249445 = 234271) (by norm_num)
theorem B626869 : Blo 491791 626869 := bbase (se 5 (by rfl) ⟨29384, by rfl⟩ : syracuseStep 626869 = 58769) (by norm_num)
theorem B790717 : Blo 491791 790717 := bbase (se 3 (by rfl) ⟨148259, by rfl⟩ : syracuseStep 790717 = 296519) (by norm_num)
theorem B528601 : Blo 491791 528601 := bbase (se 2 (by rfl) ⟨198225, by rfl⟩ : syracuseStep 528601 = 396451) (by norm_num)
theorem B1773893 : Blo 491791 1773893 := bbase (se 4 (by rfl) ⟨166302, by rfl⟩ : syracuseStep 1773893 = 332605) (by norm_num)
theorem B627041 : Blo 491791 627041 := bbase (se 2 (by rfl) ⟨235140, by rfl⟩ : syracuseStep 627041 = 470281) (by norm_num)
theorem B1577333 : Blo 491791 1577333 := bbase (se 5 (by rfl) ⟨73937, by rfl⟩ : syracuseStep 1577333 = 147875) (by norm_num)
theorem B627097 : Blo 491791 627097 := bbase (se 2 (by rfl) ⟨235161, by rfl⟩ : syracuseStep 627097 = 470323) (by norm_num)
theorem B1053101 : Blo 491791 1053101 := bbase (se 3 (by rfl) ⟨197456, by rfl⟩ : syracuseStep 1053101 = 394913) (by norm_num)
theorem B1053109 : Blo 491791 1053109 := bbase (se 5 (by rfl) ⟨49364, by rfl⟩ : syracuseStep 1053109 = 98729) (by norm_num)
theorem B790973 : Blo 491791 790973 := bbase (se 3 (by rfl) ⟨148307, by rfl⟩ : syracuseStep 790973 = 296615) (by norm_num)
theorem B627193 : Blo 491791 627193 := bbase (se 2 (by rfl) ⟨235197, by rfl⟩ : syracuseStep 627193 = 470395) (by norm_num)
theorem B1249789 : Blo 491791 1249789 := bbase (se 3 (by rfl) ⟨234335, by rfl⟩ : syracuseStep 1249789 = 468671) (by norm_num)
theorem B561709 : Blo 491791 561709 := bbase (se 3 (by rfl) ⟨105320, by rfl⟩ : syracuseStep 561709 = 210641) (by norm_num)
theorem B528977 : Blo 491791 528977 := bbase (se 2 (by rfl) ⟨198366, by rfl⟩ : syracuseStep 528977 = 396733) (by norm_num)
theorem B1774181 : Blo 491791 1774181 := bbase (se 4 (by rfl) ⟨166329, by rfl⟩ : syracuseStep 1774181 = 332659) (by norm_num)
theorem B1249901 : Blo 491791 1249901 := bbase (se 3 (by rfl) ⟨234356, by rfl⟩ : syracuseStep 1249901 = 468713) (by norm_num)
theorem B529049 : Blo 491791 529049 := bbase (se 2 (by rfl) ⟨198393, by rfl⟩ : syracuseStep 529049 = 396787) (by norm_num)
theorem B627365 : Blo 491791 627365 := bbase (se 4 (by rfl) ⟨58815, by rfl⟩ : syracuseStep 627365 = 117631) (by norm_num)
theorem B3609269 : Blo 491791 3609269 := bbase (se 5 (by rfl) ⟨169184, by rfl⟩ : syracuseStep 3609269 = 338369) (by norm_num)
theorem B627421 : Blo 491791 627421 := bbase (se 3 (by rfl) ⟨117641, by rfl⟩ : syracuseStep 627421 = 235283) (by norm_num)
theorem B1184557 : Blo 491791 1184557 := bbase (se 3 (by rfl) ⟨222104, by rfl⟩ : syracuseStep 1184557 = 444209) (by norm_num)
theorem B1250093 : Blo 491791 1250093 := bbase (se 3 (by rfl) ⟨234392, by rfl⟩ : syracuseStep 1250093 = 468785) (by norm_num)
theorem B2495285 : Blo 491791 2495285 := bbase (se 5 (by rfl) ⟨116966, by rfl⟩ : syracuseStep 2495285 = 233933) (by norm_num)
theorem B529237 : Blo 491791 529237 := bbase (se 9 (by rfl) ⟨1550, by rfl⟩ : syracuseStep 529237 = 3101) (by norm_num)
theorem B529421 : Blo 491791 529421 := bbase (se 3 (by rfl) ⟨99266, by rfl⟩ : syracuseStep 529421 = 198533) (by norm_num)
theorem B791677 : Blo 491791 791677 := bbase (se 3 (by rfl) ⟨148439, by rfl⟩ : syracuseStep 791677 = 296879) (by norm_num)
theorem B1250437 : Blo 491791 1250437 := bbase (se 4 (by rfl) ⟨117228, by rfl⟩ : syracuseStep 1250437 = 234457) (by norm_num)
theorem B1250549 : Blo 491791 1250549 := bbase (se 5 (by rfl) ⟨58619, by rfl⟩ : syracuseStep 1250549 = 117239) (by norm_num)
theorem B2102597 : Blo 491791 2102597 := bbase (se 4 (by rfl) ⟨197118, by rfl⟩ : syracuseStep 2102597 = 394237) (by norm_num)
theorem B5051765 : Blo 491791 5051765 := bbase (se 5 (by rfl) ⟨236801, by rfl⟩ : syracuseStep 5051765 = 473603) (by norm_num)
theorem B1250741 : Blo 491791 1250741 := bbase (se 5 (by rfl) ⟨58628, by rfl⟩ : syracuseStep 1250741 = 117257) (by norm_num)
theorem B1185229 : Blo 491791 1185229 := bbase (se 3 (by rfl) ⟨222230, by rfl⟩ : syracuseStep 1185229 = 444461) (by norm_num)
theorem B2004437 : Blo 491791 2004437 := bbase (se 7 (by rfl) ⟨23489, by rfl⟩ : syracuseStep 2004437 = 46979) (by norm_num)
theorem B595445 : Blo 491791 595445 := bbase (se 5 (by rfl) ⟨27911, by rfl⟩ : syracuseStep 595445 = 55823) (by norm_num)
theorem B595469 : Blo 491791 595469 := bbase (se 3 (by rfl) ⟨111650, by rfl⟩ : syracuseStep 595469 = 223301) (by norm_num)
theorem B1054237 : Blo 491791 1054237 := bbase (se 3 (by rfl) ⟨197669, by rfl⟩ : syracuseStep 1054237 = 395339) (by norm_num)
theorem B792101 : Blo 491791 792101 := bbase (se 4 (by rfl) ⟨74259, by rfl⟩ : syracuseStep 792101 = 148519) (by norm_num)
theorem B562837 : Blo 491791 562837 := bbase (se 6 (by rfl) ⟨13191, by rfl⟩ : syracuseStep 562837 = 26383) (by norm_num)
theorem B1185461 : Blo 491791 1185461 := bbase (se 5 (by rfl) ⟨55568, by rfl⟩ : syracuseStep 1185461 = 111137) (by norm_num)
theorem B1185509 : Blo 491791 1185509 := bbase (se 4 (by rfl) ⟨111141, by rfl⟩ : syracuseStep 1185509 = 222283) (by norm_num)
theorem B1873637 : Blo 491791 1873637 := bbase (se 4 (by rfl) ⟨175653, by rfl⟩ : syracuseStep 1873637 = 351307) (by norm_num)
theorem B1251085 : Blo 491791 1251085 := bbase (se 3 (by rfl) ⟨234578, by rfl⟩ : syracuseStep 1251085 = 469157) (by norm_num)
theorem B792389 : Blo 491791 792389 := bbase (se 4 (by rfl) ⟨74286, by rfl⟩ : syracuseStep 792389 = 148573) (by norm_num)
theorem B1251197 : Blo 491791 1251197 := bbase (se 3 (by rfl) ⟨234599, by rfl⟩ : syracuseStep 1251197 = 469199) (by norm_num)
theorem B1054613 : Blo 491791 1054613 := bbase (se 6 (by rfl) ⟨24717, by rfl⟩ : syracuseStep 1054613 = 49435) (by norm_num)
theorem B1873925 : Blo 491791 1873925 := bbase (se 4 (by rfl) ⟨175680, by rfl⟩ : syracuseStep 1873925 = 351361) (by norm_num)
theorem B792613 : Blo 491791 792613 := bbase (se 4 (by rfl) ⟨74307, by rfl⟩ : syracuseStep 792613 = 148615) (by norm_num)
theorem B759869 : Blo 491791 759869 := bbase (se 3 (by rfl) ⟨142475, by rfl⟩ : syracuseStep 759869 = 284951) (by norm_num)
theorem B1251389 : Blo 491791 1251389 := bbase (se 3 (by rfl) ⟨234635, by rfl⟩ : syracuseStep 1251389 = 469271) (by norm_num)
theorem B890941 : Blo 491791 890941 := bbase (se 3 (by rfl) ⟨167051, by rfl⟩ : syracuseStep 890941 = 334103) (by norm_num)
theorem B2496581 : Blo 491791 2496581 := bbase (se 4 (by rfl) ⟨234054, by rfl⟩ : syracuseStep 2496581 = 468109) (by norm_num)
theorem B891013 : Blo 491791 891013 := bbase (se 4 (by rfl) ⟨83532, by rfl⟩ : syracuseStep 891013 = 167065) (by norm_num)
theorem B1251733 : Blo 491791 1251733 := bbase (se 6 (by rfl) ⟨29337, by rfl⟩ : syracuseStep 1251733 = 58675) (by norm_num)
theorem B563689 : Blo 491791 563689 := bbase (se 2 (by rfl) ⟨211383, by rfl⟩ : syracuseStep 563689 = 422767) (by norm_num)
theorem B1251845 : Blo 491791 1251845 := bbase (se 4 (by rfl) ⟨117360, by rfl⟩ : syracuseStep 1251845 = 234721) (by norm_num)
theorem B6396565 : Blo 491791 6396565 := bbase (se 6 (by rfl) ⟨149919, by rfl⟩ : syracuseStep 6396565 = 299839) (by norm_num)
theorem B1252037 : Blo 491791 1252037 := bbase (se 4 (by rfl) ⟨117378, by rfl⟩ : syracuseStep 1252037 = 234757) (by norm_num)
theorem B1252381 : Blo 491791 1252381 := bbase (se 3 (by rfl) ⟨234821, by rfl⟩ : syracuseStep 1252381 = 469643) (by norm_num)
theorem B2104373 : Blo 491791 2104373 := bbase (se 5 (by rfl) ⟨98642, by rfl⟩ : syracuseStep 2104373 = 197285) (by norm_num)
theorem B498745 : Blo 491791 498745 := bbase (se 2 (by rfl) ⟨187029, by rfl⟩ : syracuseStep 498745 = 374059) (by norm_num)
theorem B1186901 : Blo 491791 1186901 := bbase (se 8 (by rfl) ⟨6954, by rfl⟩ : syracuseStep 1186901 = 13909) (by norm_num)
theorem B892021 : Blo 491791 892021 := bbase (se 5 (by rfl) ⟨41813, by rfl⟩ : syracuseStep 892021 = 83627) (by norm_num)
theorem B1252493 : Blo 491791 1252493 := bbase (se 3 (by rfl) ⟨234842, by rfl⟩ : syracuseStep 1252493 = 469685) (by norm_num)
theorem B793741 : Blo 491791 793741 := bbase (se 3 (by rfl) ⟨148826, by rfl⟩ : syracuseStep 793741 = 297653) (by norm_num)
theorem B1875109 : Blo 491791 1875109 := bbase (se 4 (by rfl) ⟨175791, by rfl⟩ : syracuseStep 1875109 = 351583) (by norm_num)
theorem B892109 : Blo 491791 892109 := bbase (se 3 (by rfl) ⟨167270, by rfl⟩ : syracuseStep 892109 = 334541) (by norm_num)
theorem B1187093 : Blo 491791 1187093 := bbase (se 6 (by rfl) ⟨27822, by rfl⟩ : syracuseStep 1187093 = 55645) (by norm_num)
theorem B2104613 : Blo 491791 2104613 := bbase (se 4 (by rfl) ⟨197307, by rfl⟩ : syracuseStep 2104613 = 394615) (by norm_num)
theorem B1252685 : Blo 491791 1252685 := bbase (se 3 (by rfl) ⟨234878, by rfl⟩ : syracuseStep 1252685 = 469757) (by norm_num)
theorem B2497877 : Blo 491791 2497877 := bbase (se 11 (by rfl) ⟨1829, by rfl⟩ : syracuseStep 2497877 = 3659) (by norm_num)
theorem B3546517 : Blo 491791 3546517 := bbase (se 6 (by rfl) ⟨83121, by rfl⟩ : syracuseStep 3546517 = 166243) (by norm_num)
theorem B1875413 : Blo 491791 1875413 := bbase (se 7 (by rfl) ⟨21977, by rfl⟩ : syracuseStep 1875413 = 43955) (by norm_num)
theorem B892397 : Blo 491791 892397 := bbase (se 3 (by rfl) ⟨167324, by rfl⟩ : syracuseStep 892397 = 334649) (by norm_num)
theorem B1056253 : Blo 491791 1056253 := bbase (se 3 (by rfl) ⟨198047, by rfl⟩ : syracuseStep 1056253 = 396095) (by norm_num)
theorem B1253029 : Blo 491791 1253029 := bbase (se 4 (by rfl) ⟨117471, by rfl⟩ : syracuseStep 1253029 = 234943) (by norm_num)
theorem B1580741 : Blo 491791 1580741 := bbase (se 4 (by rfl) ⟨148194, by rfl⟩ : syracuseStep 1580741 = 296389) (by norm_num)
theorem B892613 : Blo 491791 892613 := bbase (se 4 (by rfl) ⟨83682, by rfl⟩ : syracuseStep 892613 = 167365) (by norm_num)
theorem B1253141 : Blo 491791 1253141 := bbase (se 6 (by rfl) ⟨29370, by rfl⟩ : syracuseStep 1253141 = 58741) (by norm_num)
theorem B4235125 : Blo 491791 4235125 := bbase (se 5 (by rfl) ⟨198521, by rfl⟩ : syracuseStep 4235125 = 397043) (by norm_num)
theorem B1253333 : Blo 491791 1253333 := bbase (se 7 (by rfl) ⟨14687, by rfl⟩ : syracuseStep 1253333 = 29375) (by norm_num)
theorem B565213 : Blo 491791 565213 := bbase (se 3 (by rfl) ⟨105977, by rfl⟩ : syracuseStep 565213 = 211955) (by norm_num)
theorem B499889 : Blo 491791 499889 := bbase (se 2 (by rfl) ⟨187458, by rfl⟩ : syracuseStep 499889 = 374917) (by norm_num)
theorem B4726997 : Blo 491791 4726997 := bbase (se 7 (by rfl) ⟨55394, by rfl⟩ : syracuseStep 4726997 = 110789) (by norm_num)
theorem B532697 : Blo 491791 532697 := bbase (se 2 (by rfl) ⟨199761, by rfl⟩ : syracuseStep 532697 = 399523) (by norm_num)
theorem B532765 : Blo 491791 532765 := bbase (se 3 (by rfl) ⟨99893, by rfl⟩ : syracuseStep 532765 = 199787) (by norm_num)
theorem B1253677 : Blo 491791 1253677 := bbase (se 3 (by rfl) ⟨235064, by rfl⟩ : syracuseStep 1253677 = 470129) (by norm_num)
theorem B2662741 : Blo 491791 2662741 := bbase (se 10 (by rfl) ⟨3900, by rfl⟩ : syracuseStep 2662741 = 7801) (by norm_num)
theorem B12165461 : Blo 491791 12165461 := bbase (se 10 (by rfl) ⟨17820, by rfl⟩ : syracuseStep 12165461 = 35641) (by norm_num)
theorem B1057141 : Blo 491791 1057141 := bbase (se 5 (by rfl) ⟨49553, by rfl⟩ : syracuseStep 1057141 = 99107) (by norm_num)
theorem B1253789 : Blo 491791 1253789 := bbase (se 3 (by rfl) ⟨235085, by rfl⟩ : syracuseStep 1253789 = 470171) (by norm_num)
theorem B1253981 : Blo 491791 1253981 := bbase (se 3 (by rfl) ⟨235121, by rfl⟩ : syracuseStep 1253981 = 470243) (by norm_num)
theorem B2499173 : Blo 491791 2499173 := bbase (se 4 (by rfl) ⟨234297, by rfl⟩ : syracuseStep 2499173 = 468595) (by norm_num)
theorem B1352341 : Blo 491791 1352341 := bbase (se 6 (by rfl) ⟨31695, by rfl⟩ : syracuseStep 1352341 = 63391) (by norm_num)
theorem B500473 : Blo 491791 500473 := bbase (se 2 (by rfl) ⟨187677, by rfl⟩ : syracuseStep 500473 = 375355) (by norm_num)
theorem B1057637 : Blo 491791 1057637 := bbase (se 4 (by rfl) ⟨99153, by rfl⟩ : syracuseStep 1057637 = 198307) (by norm_num)
theorem B3744629 : Blo 491791 3744629 := bbase (se 5 (by rfl) ⟨175529, by rfl⟩ : syracuseStep 3744629 = 351059) (by norm_num)
theorem B1352629 : Blo 491791 1352629 := bbase (se 5 (by rfl) ⟨63404, by rfl⟩ : syracuseStep 1352629 = 126809) (by norm_num)
theorem B1254325 : Blo 491791 1254325 := bbase (se 5 (by rfl) ⟨58796, by rfl⟩ : syracuseStep 1254325 = 117593) (by norm_num)
theorem B1582021 : Blo 491791 1582021 := bbase (se 4 (by rfl) ⟨148314, by rfl⟩ : syracuseStep 1582021 = 296629) (by norm_num)
theorem B631841 : Blo 491791 631841 := bbase (se 2 (by rfl) ⟨236940, by rfl⟩ : syracuseStep 631841 = 473881) (by norm_num)
theorem B1254437 : Blo 491791 1254437 := bbase (se 4 (by rfl) ⟨117603, by rfl⟩ : syracuseStep 1254437 = 235207) (by norm_num)
theorem B664789 : Blo 491791 664789 := bbase (se 7 (by rfl) ⟨7790, by rfl⟩ : syracuseStep 664789 = 15581) (by norm_num)
theorem B1189093 : Blo 491791 1189093 := bbase (se 4 (by rfl) ⟨111477, by rfl⟩ : syracuseStep 1189093 = 222955) (by norm_num)
theorem B1254629 : Blo 491791 1254629 := bbase (se 4 (by rfl) ⟨117621, by rfl⟩ : syracuseStep 1254629 = 235243) (by norm_num)
theorem B763301 : Blo 491791 763301 := bbase (se 4 (by rfl) ⟨71559, by rfl⟩ : syracuseStep 763301 = 143119) (by norm_num)
theorem B4498901 : Blo 491791 4498901 := bbase (se 7 (by rfl) ⟨52721, by rfl⟩ : syracuseStep 4498901 = 105443) (by norm_num)
theorem B2106901 : Blo 491791 2106901 := bbase (se 6 (by rfl) ⟨49380, by rfl⟩ : syracuseStep 2106901 = 98761) (by norm_num)
theorem B1877525 : Blo 491791 1877525 := bbase (se 6 (by rfl) ⟨44004, by rfl⟩ : syracuseStep 1877525 = 88009) (by norm_num)
theorem B1254973 : Blo 491791 1254973 := bbase (se 3 (by rfl) ⟨235307, by rfl⟩ : syracuseStep 1254973 = 470615) (by norm_num)
theorem B501373 : Blo 491791 501373 := bbase (se 3 (by rfl) ⟨94007, by rfl⟩ : syracuseStep 501373 = 188015) (by norm_num)
theorem B2369189 : Blo 491791 2369189 := bbase (se 4 (by rfl) ⟨222111, by rfl⟩ : syracuseStep 2369189 = 444223) (by norm_num)
theorem B1058501 : Blo 491791 1058501 := bbase (se 4 (by rfl) ⟨99234, by rfl⟩ : syracuseStep 1058501 = 198469) (by norm_num)
theorem B1189669 : Blo 491791 1189669 := bbase (se 4 (by rfl) ⟨111531, by rfl⟩ : syracuseStep 1189669 = 223063) (by norm_num)
theorem B1877813 : Blo 491791 1877813 := bbase (se 5 (by rfl) ⟨88022, by rfl⟩ : syracuseStep 1877813 = 176045) (by norm_num)
theorem B1058645 : Blo 491791 1058645 := bbase (se 9 (by rfl) ⟨3101, by rfl⟩ : syracuseStep 1058645 = 6203) (by norm_num)
theorem B2500469 : Blo 491791 2500469 := bbase (se 5 (by rfl) ⟨117209, by rfl⟩ : syracuseStep 2500469 = 234419) (by norm_num)
theorem B1124221 : Blo 491791 1124221 := bbase (se 3 (by rfl) ⟨210791, by rfl⟩ : syracuseStep 1124221 = 421583) (by norm_num)
theorem B12036053 : Blo 491791 12036053 := bbase (se 7 (by rfl) ⟨141047, by rfl⟩ : syracuseStep 12036053 = 282095) (by norm_num)
theorem B4499509 : Blo 491791 4499509 := bbase (se 5 (by rfl) ⟨210914, by rfl⟩ : syracuseStep 4499509 = 421829) (by norm_num)
theorem B1189997 : Blo 491791 1189997 := bbase (se 3 (by rfl) ⟨223124, by rfl⟩ : syracuseStep 1189997 = 446249) (by norm_num)
theorem B1190053 : Blo 491791 1190053 := bbase (se 4 (by rfl) ⟨111567, by rfl⟩ : syracuseStep 1190053 = 223135) (by norm_num)
theorem B600301 : Blo 491791 600301 := bbase (se 3 (by rfl) ⟨112556, by rfl⟩ : syracuseStep 600301 = 225113) (by norm_num)
theorem B1583381 : Blo 491791 1583381 := bbase (se 6 (by rfl) ⟨37110, by rfl⟩ : syracuseStep 1583381 = 74221) (by norm_num)
theorem B1190285 : Blo 491791 1190285 := bbase (se 3 (by rfl) ⟨223178, by rfl⟩ : syracuseStep 1190285 = 446357) (by norm_num)
theorem B1583509 : Blo 491791 1583509 := bbase (se 6 (by rfl) ⟨37113, by rfl⟩ : syracuseStep 1583509 = 74227) (by norm_num)
theorem B829973 : Blo 491791 829973 := bbase (se 6 (by rfl) ⟨19452, by rfl⟩ : syracuseStep 829973 = 38905) (by norm_num)
theorem B1190477 : Blo 491791 1190477 := bbase (se 3 (by rfl) ⟨223214, by rfl⟩ : syracuseStep 1190477 = 446429) (by norm_num)
theorem B830101 : Blo 491791 830101 := bbase (se 6 (by rfl) ⟨19455, by rfl⟩ : syracuseStep 830101 = 38911) (by norm_num)
theorem B1583765 : Blo 491791 1583765 := bbase (se 6 (by rfl) ⟨37119, by rfl⟩ : syracuseStep 1583765 = 74239) (by norm_num)
theorem B3156661 : Blo 491791 3156661 := bbase (se 5 (by rfl) ⟨147968, by rfl⟩ : syracuseStep 3156661 = 295937) (by norm_num)
theorem B830189 : Blo 491791 830189 := bbase (se 3 (by rfl) ⟨155660, by rfl⟩ : syracuseStep 830189 = 311321) (by norm_num)
theorem B830317 : Blo 491791 830317 := bbase (se 3 (by rfl) ⟨155684, by rfl⟩ : syracuseStep 830317 = 311369) (by norm_num)
theorem B1780613 : Blo 491791 1780613 := bbase (se 4 (by rfl) ⟨166932, by rfl⟩ : syracuseStep 1780613 = 333865) (by norm_num)
theorem B830405 : Blo 491791 830405 := bbase (se 4 (by rfl) ⟨77850, by rfl⟩ : syracuseStep 830405 = 155701) (by norm_num)
theorem B1878997 : Blo 491791 1878997 := bbase (se 7 (by rfl) ⟨22019, by rfl⟩ : syracuseStep 1878997 = 44039) (by norm_num)
theorem B2108389 : Blo 491791 2108389 := bbase (se 4 (by rfl) ⟨197661, by rfl⟩ : syracuseStep 2108389 = 395323) (by norm_num)
theorem B2108405 : Blo 491791 2108405 := bbase (se 5 (by rfl) ⟨98831, by rfl⟩ : syracuseStep 2108405 = 197663) (by norm_num)
theorem B1125389 : Blo 491791 1125389 := bbase (se 3 (by rfl) ⟨211010, by rfl⟩ : syracuseStep 1125389 = 422021) (by norm_num)
theorem B830533 : Blo 491791 830533 := bbase (se 4 (by rfl) ⟨77862, by rfl⟩ : syracuseStep 830533 = 155725) (by norm_num)
theorem B2501765 : Blo 491791 2501765 := bbase (se 4 (by rfl) ⟨234540, by rfl⟩ : syracuseStep 2501765 = 469081) (by norm_num)
theorem B633997 : Blo 491791 633997 := bbase (se 3 (by rfl) ⟨118874, by rfl⟩ : syracuseStep 633997 = 237749) (by norm_num)
theorem B830621 : Blo 491791 830621 := bbase (se 3 (by rfl) ⟨155741, by rfl⟩ : syracuseStep 830621 = 311483) (by norm_num)
theorem B1879301 : Blo 491791 1879301 := bbase (se 4 (by rfl) ⟨176184, by rfl⟩ : syracuseStep 1879301 = 352369) (by norm_num)
theorem B830749 : Blo 491791 830749 := bbase (se 3 (by rfl) ⟨155765, by rfl⟩ : syracuseStep 830749 = 311531) (by norm_num)
theorem B830837 : Blo 491791 830837 := bbase (se 5 (by rfl) ⟨38945, by rfl⟩ : syracuseStep 830837 = 77891) (by norm_num)
theorem B830965 : Blo 491791 830965 := bbase (se 5 (by rfl) ⟨38951, by rfl⟩ : syracuseStep 830965 = 77903) (by norm_num)
theorem B831053 : Blo 491791 831053 := bbase (se 3 (by rfl) ⟨155822, by rfl⟩ : syracuseStep 831053 = 311645) (by norm_num)
theorem B7614101 : Blo 491791 7614101 := bbase (se 6 (by rfl) ⟨178455, by rfl⟩ : syracuseStep 7614101 = 356911) (by norm_num)
theorem B831181 : Blo 491791 831181 := bbase (se 3 (by rfl) ⟨155846, by rfl⟩ : syracuseStep 831181 = 311693) (by norm_num)
theorem B1421077 : Blo 491791 1421077 := bbase (se 6 (by rfl) ⟨33306, by rfl⟩ : syracuseStep 1421077 = 66613) (by norm_num)
theorem B831269 : Blo 491791 831269 := bbase (se 4 (by rfl) ⟨77931, by rfl⟩ : syracuseStep 831269 = 155863) (by norm_num)
theorem B634673 : Blo 491791 634673 := bbase (se 2 (by rfl) ⟨238002, by rfl⟩ : syracuseStep 634673 = 476005) (by norm_num)
theorem B2666357 : Blo 491791 2666357 := bbase (se 5 (by rfl) ⟨124985, by rfl⟩ : syracuseStep 2666357 = 249971) (by norm_num)
theorem B831397 : Blo 491791 831397 := bbase (se 4 (by rfl) ⟨77943, by rfl⟩ : syracuseStep 831397 = 155887) (by norm_num)
theorem B831485 : Blo 491791 831485 := bbase (se 3 (by rfl) ⟨155903, by rfl⟩ : syracuseStep 831485 = 311807) (by norm_num)
theorem B1126429 : Blo 491791 1126429 := bbase (se 3 (by rfl) ⟨211205, by rfl⟩ : syracuseStep 1126429 = 422411) (by norm_num)
theorem B700501 : Blo 491791 700501 := bbase (se 8 (by rfl) ⟨4104, by rfl⟩ : syracuseStep 700501 = 8209) (by norm_num)
theorem B831613 : Blo 491791 831613 := bbase (se 3 (by rfl) ⟨155927, by rfl⟩ : syracuseStep 831613 = 311855) (by norm_num)
theorem B831701 : Blo 491791 831701 := bbase (se 7 (by rfl) ⟨9746, by rfl⟩ : syracuseStep 831701 = 19493) (by norm_num)
theorem B5353685 : Blo 491791 5353685 := bbase (se 7 (by rfl) ⟨62738, by rfl⟩ : syracuseStep 5353685 = 125477) (by norm_num)
theorem B667973 : Blo 491791 667973 := bbase (se 4 (by rfl) ⟨62622, by rfl⟩ : syracuseStep 667973 = 125245) (by norm_num)
theorem B831829 : Blo 491791 831829 := bbase (se 10 (by rfl) ⟨1218, by rfl⟩ : syracuseStep 831829 = 2437) (by norm_num)
theorem B668021 : Blo 491791 668021 := bbase (se 5 (by rfl) ⟨31313, by rfl⟩ : syracuseStep 668021 = 62627) (by norm_num)
theorem B2503061 : Blo 491791 2503061 := bbase (se 6 (by rfl) ⟨58665, by rfl⟩ : syracuseStep 2503061 = 117331) (by norm_num)
theorem B831917 : Blo 491791 831917 := bbase (se 3 (by rfl) ⟨155984, by rfl⟩ : syracuseStep 831917 = 311969) (by norm_num)
theorem B602581 : Blo 491791 602581 := bbase (se 7 (by rfl) ⟨7061, by rfl⟩ : syracuseStep 602581 = 14123) (by norm_num)
theorem B832045 : Blo 491791 832045 := bbase (se 3 (by rfl) ⟨156008, by rfl⟩ : syracuseStep 832045 = 312017) (by norm_num)
theorem B832133 : Blo 491791 832133 := bbase (se 4 (by rfl) ⟨78012, by rfl⟩ : syracuseStep 832133 = 156025) (by norm_num)
theorem B701093 : Blo 491791 701093 := bbase (se 4 (by rfl) ⟨65727, by rfl⟩ : syracuseStep 701093 = 131455) (by norm_num)
theorem B1127141 : Blo 491791 1127141 := bbase (se 4 (by rfl) ⟨105669, by rfl⟩ : syracuseStep 1127141 = 211339) (by norm_num)
theorem B701173 : Blo 491791 701173 := bbase (se 5 (by rfl) ⟨32867, by rfl⟩ : syracuseStep 701173 = 65735) (by norm_num)
theorem B2372341 : Blo 491791 2372341 := bbase (se 5 (by rfl) ⟨111203, by rfl⟩ : syracuseStep 2372341 = 222407) (by norm_num)
theorem B832261 : Blo 491791 832261 := bbase (se 4 (by rfl) ⟨78024, by rfl⟩ : syracuseStep 832261 = 156049) (by norm_num)
theorem B832349 : Blo 491791 832349 := bbase (se 3 (by rfl) ⟨156065, by rfl⟩ : syracuseStep 832349 = 312131) (by norm_num)
theorem B701293 : Blo 491791 701293 := bbase (se 3 (by rfl) ⟨131492, by rfl⟩ : syracuseStep 701293 = 262985) (by norm_num)
theorem B799621 : Blo 491791 799621 := bbase (se 4 (by rfl) ⟨74964, by rfl⟩ : syracuseStep 799621 = 149929) (by norm_num)
theorem B701389 : Blo 491791 701389 := bbase (se 3 (by rfl) ⟨131510, by rfl⟩ : syracuseStep 701389 = 263021) (by norm_num)
theorem B832477 : Blo 491791 832477 := bbase (se 3 (by rfl) ⟨156089, by rfl⟩ : syracuseStep 832477 = 312179) (by norm_num)
theorem B1586213 : Blo 491791 1586213 := bbase (se 4 (by rfl) ⟨148707, by rfl⟩ : syracuseStep 1586213 = 297415) (by norm_num)
theorem B832565 : Blo 491791 832565 := bbase (se 5 (by rfl) ⟨39026, by rfl⟩ : syracuseStep 832565 = 78053) (by norm_num)
theorem B832693 : Blo 491791 832693 := bbase (se 5 (by rfl) ⟨39032, by rfl⟩ : syracuseStep 832693 = 78065) (by norm_num)
theorem B2110661 : Blo 491791 2110661 := bbase (se 4 (by rfl) ⟨197874, by rfl⟩ : syracuseStep 2110661 = 395749) (by norm_num)
theorem B603337 : Blo 491791 603337 := bbase (se 2 (by rfl) ⟨226251, by rfl⟩ : syracuseStep 603337 = 452503) (by norm_num)
theorem B4568309 : Blo 491791 4568309 := bbase (se 5 (by rfl) ⟨214139, by rfl⟩ : syracuseStep 4568309 = 428279) (by norm_num)
theorem B832781 : Blo 491791 832781 := bbase (se 3 (by rfl) ⟨156146, by rfl⟩ : syracuseStep 832781 = 312293) (by norm_num)
theorem B1881413 : Blo 491791 1881413 := bbase (se 4 (by rfl) ⟨176382, by rfl⟩ : syracuseStep 1881413 = 352765) (by norm_num)
theorem B832909 : Blo 491791 832909 := bbase (se 3 (by rfl) ⟨156170, by rfl⟩ : syracuseStep 832909 = 312341) (by norm_num)
theorem B701885 : Blo 491791 701885 := bbase (se 3 (by rfl) ⟨131603, by rfl⟩ : syracuseStep 701885 = 263207) (by norm_num)
theorem B832997 : Blo 491791 832997 := bbase (se 4 (by rfl) ⟨78093, by rfl⟩ : syracuseStep 832997 = 156187) (by norm_num)
theorem B3814933 : Blo 491791 3814933 := bbase (se 6 (by rfl) ⟨89412, by rfl⟩ : syracuseStep 3814933 = 178825) (by norm_num)
theorem B1226285 : Blo 491791 1226285 := bbase (se 3 (by rfl) ⟨229928, by rfl⟩ : syracuseStep 1226285 = 459857) (by norm_num)
theorem B833125 : Blo 491791 833125 := bbase (se 4 (by rfl) ⟨78105, by rfl⟩ : syracuseStep 833125 = 156211) (by norm_num)
theorem B1881701 : Blo 491791 1881701 := bbase (se 4 (by rfl) ⟨176409, by rfl⟩ : syracuseStep 1881701 = 352819) (by norm_num)
theorem B2504357 : Blo 491791 2504357 := bbase (se 4 (by rfl) ⟨234783, by rfl⟩ : syracuseStep 2504357 = 469567) (by norm_num)
theorem B833213 : Blo 491791 833213 := bbase (se 3 (by rfl) ⟨156227, by rfl⟩ : syracuseStep 833213 = 312455) (by norm_num)
theorem B833341 : Blo 491791 833341 := bbase (se 3 (by rfl) ⟨156251, by rfl⟩ : syracuseStep 833341 = 312503) (by norm_num)
theorem B1128253 : Blo 491791 1128253 := bbase (se 3 (by rfl) ⟨211547, by rfl⟩ : syracuseStep 1128253 = 423095) (by norm_num)
theorem B833429 : Blo 491791 833429 := bbase (se 6 (by rfl) ⟨19533, by rfl⟩ : syracuseStep 833429 = 39067) (by norm_num)
theorem B2996149 : Blo 491791 2996149 := bbase (se 5 (by rfl) ⟨140444, by rfl⟩ : syracuseStep 2996149 = 280889) (by norm_num)
theorem B702437 : Blo 491791 702437 := bbase (se 4 (by rfl) ⟨65853, by rfl⟩ : syracuseStep 702437 = 131707) (by norm_num)
theorem B833557 : Blo 491791 833557 := bbase (se 6 (by rfl) ⟨19536, by rfl⟩ : syracuseStep 833557 = 39073) (by norm_num)
theorem B833645 : Blo 491791 833645 := bbase (se 3 (by rfl) ⟨156308, by rfl⟩ : syracuseStep 833645 = 312617) (by norm_num)
theorem B997589 : Blo 491791 997589 := bbase (se 7 (by rfl) ⟨11690, by rfl⟩ : syracuseStep 997589 = 23381) (by norm_num)
theorem B833773 : Blo 491791 833773 := bbase (se 3 (by rfl) ⟨156332, by rfl⟩ : syracuseStep 833773 = 312665) (by norm_num)
theorem B669989 : Blo 491791 669989 := bbase (se 4 (by rfl) ⟨62811, by rfl⟩ : syracuseStep 669989 = 125623) (by norm_num)
theorem B833861 : Blo 491791 833861 := bbase (se 4 (by rfl) ⟨78174, by rfl⟩ : syracuseStep 833861 = 156349) (by norm_num)
theorem B1587557 : Blo 491791 1587557 := bbase (se 4 (by rfl) ⟨148833, by rfl⟩ : syracuseStep 1587557 = 297667) (by norm_num)
theorem B1849717 : Blo 491791 1849717 := bbase (se 5 (by rfl) ⟨86705, by rfl⟩ : syracuseStep 1849717 = 173411) (by norm_num)
theorem B1423813 : Blo 491791 1423813 := bbase (se 4 (by rfl) ⟨133482, by rfl⟩ : syracuseStep 1423813 = 266965) (by norm_num)
theorem B833989 : Blo 491791 833989 := bbase (se 4 (by rfl) ⟨78186, by rfl⟩ : syracuseStep 833989 = 156373) (by norm_num)
theorem B834077 : Blo 491791 834077 := bbase (se 3 (by rfl) ⟨156389, by rfl⟩ : syracuseStep 834077 = 312779) (by norm_num)
theorem B1129037 : Blo 491791 1129037 := bbase (se 3 (by rfl) ⟨211694, by rfl⟩ : syracuseStep 1129037 = 423389) (by norm_num)
theorem B834205 : Blo 491791 834205 := bbase (se 3 (by rfl) ⟨156413, by rfl⟩ : syracuseStep 834205 = 312827) (by norm_num)
theorem B703189 : Blo 491791 703189 := bbase (se 7 (by rfl) ⟨8240, by rfl⟩ : syracuseStep 703189 = 16481) (by norm_num)
theorem B834293 : Blo 491791 834293 := bbase (se 5 (by rfl) ⟨39107, by rfl⟩ : syracuseStep 834293 = 78215) (by norm_num)
theorem B834421 : Blo 491791 834421 := bbase (se 5 (by rfl) ⟨39113, by rfl⟩ : syracuseStep 834421 = 78227) (by norm_num)
theorem B2505653 : Blo 491791 2505653 := bbase (se 5 (by rfl) ⟨117452, by rfl⟩ : syracuseStep 2505653 = 234905) (by norm_num)
theorem B834509 : Blo 491791 834509 := bbase (se 3 (by rfl) ⟨156470, by rfl⟩ : syracuseStep 834509 = 312941) (by norm_num)
theorem B834637 : Blo 491791 834637 := bbase (se 3 (by rfl) ⟨156494, by rfl⟩ : syracuseStep 834637 = 312989) (by norm_num)
theorem B834725 : Blo 491791 834725 := bbase (se 4 (by rfl) ⟨78255, by rfl⟩ : syracuseStep 834725 = 156511) (by norm_num)
theorem B834853 : Blo 491791 834853 := bbase (se 4 (by rfl) ⟨78267, by rfl⟩ : syracuseStep 834853 = 156535) (by norm_num)
theorem B834941 : Blo 491791 834941 := bbase (se 3 (by rfl) ⟨156551, by rfl⟩ : syracuseStep 834941 = 313103) (by norm_num)
theorem B1785253 : Blo 491791 1785253 := bbase (se 4 (by rfl) ⟨167367, by rfl⟩ : syracuseStep 1785253 = 334735) (by norm_num)
theorem B769517 : Blo 491791 769517 := bbase (se 3 (by rfl) ⟨144284, by rfl⟩ : syracuseStep 769517 = 288569) (by norm_num)
theorem B703981 : Blo 491791 703981 := bbase (se 3 (by rfl) ⟨131996, by rfl⟩ : syracuseStep 703981 = 263993) (by norm_num)
theorem B835069 : Blo 491791 835069 := bbase (se 3 (by rfl) ⟨156575, by rfl⟩ : syracuseStep 835069 = 313151) (by norm_num)
theorem B900629 : Blo 491791 900629 := bbase (se 6 (by rfl) ⟨21108, by rfl⟩ : syracuseStep 900629 = 42217) (by norm_num)
theorem B835157 : Blo 491791 835157 := bbase (se 8 (by rfl) ⟨4893, by rfl⟩ : syracuseStep 835157 = 9787) (by norm_num)
theorem B835285 : Blo 491791 835285 := bbase (se 7 (by rfl) ⟨9788, by rfl⟩ : syracuseStep 835285 = 19577) (by norm_num)
theorem B835373 : Blo 491791 835373 := bbase (se 3 (by rfl) ⟨156632, by rfl⟩ : syracuseStep 835373 = 313265) (by norm_num)
theorem B2375477 : Blo 491791 2375477 := bbase (se 5 (by rfl) ⟨111350, by rfl⟩ : syracuseStep 2375477 = 222701) (by norm_num)
theorem B704317 : Blo 491791 704317 := bbase (se 3 (by rfl) ⟨132059, by rfl⟩ : syracuseStep 704317 = 264119) (by norm_num)
theorem B933781 : Blo 491791 933781 := bbase (se 6 (by rfl) ⟨21885, by rfl⟩ : syracuseStep 933781 = 43771) (by norm_num)
theorem B835501 : Blo 491791 835501 := bbase (se 3 (by rfl) ⟨156656, by rfl⟩ : syracuseStep 835501 = 313313) (by norm_num)
theorem B835589 : Blo 491791 835589 := bbase (se 4 (by rfl) ⟨78336, by rfl⟩ : syracuseStep 835589 = 156673) (by norm_num)
theorem B704533 : Blo 491791 704533 := bbase (se 6 (by rfl) ⟨16512, by rfl⟩ : syracuseStep 704533 = 33025) (by norm_num)
theorem B933925 : Blo 491791 933925 := bbase (se 4 (by rfl) ⟨87555, by rfl⟩ : syracuseStep 933925 = 175111) (by norm_num)
theorem B508025 : Blo 491791 508025 := bbase (se 2 (by rfl) ⟨190509, by rfl⟩ : syracuseStep 508025 = 381019) (by norm_num)
theorem B835717 : Blo 491791 835717 := bbase (se 4 (by rfl) ⟨78348, by rfl⟩ : syracuseStep 835717 = 156697) (by norm_num)
theorem B934085 : Blo 491791 934085 := bbase (se 4 (by rfl) ⟨87570, by rfl⟩ : syracuseStep 934085 = 175141) (by norm_num)
theorem B2506949 : Blo 491791 2506949 := bbase (se 4 (by rfl) ⟨235026, by rfl⟩ : syracuseStep 2506949 = 470053) (by norm_num)
theorem B835805 : Blo 491791 835805 := bbase (se 3 (by rfl) ⟨156713, by rfl⟩ : syracuseStep 835805 = 313427) (by norm_num)
theorem B934229 : Blo 491791 934229 := bbase (se 10 (by rfl) ⟨1368, by rfl⟩ : syracuseStep 934229 = 2737) (by norm_num)
theorem B835933 : Blo 491791 835933 := bbase (se 3 (by rfl) ⟨156737, by rfl⟩ : syracuseStep 835933 = 313475) (by norm_num)
theorem B704909 : Blo 491791 704909 := bbase (se 3 (by rfl) ⟨132170, by rfl⟩ : syracuseStep 704909 = 264341) (by norm_num)
theorem B737693 : Blo 491791 737693 := bbase (se 3 (by rfl) ⟨138317, by rfl⟩ : syracuseStep 737693 = 276635) (by norm_num)
theorem B737717 : Blo 491791 737717 := bbase (se 5 (by rfl) ⟨34580, by rfl⟩ : syracuseStep 737717 = 69161) (by norm_num)
theorem B836021 : Blo 491791 836021 := bbase (se 5 (by rfl) ⟨39188, by rfl⟩ : syracuseStep 836021 = 78377) (by norm_num)
theorem B737741 : Blo 491791 737741 := bbase (se 3 (by rfl) ⟨138326, by rfl⟩ : syracuseStep 737741 = 276653) (by norm_num)
theorem B3752405 : Blo 491791 3752405 := bbase (se 7 (by rfl) ⟨43973, by rfl⟩ : syracuseStep 3752405 = 87947) (by norm_num)
theorem B737765 : Blo 491791 737765 := bbase (se 4 (by rfl) ⟨69165, by rfl⟩ : syracuseStep 737765 = 138331) (by norm_num)
theorem B737789 : Blo 491791 737789 := bbase (se 3 (by rfl) ⟨138335, by rfl⟩ : syracuseStep 737789 = 276671) (by norm_num)
theorem B1065469 : Blo 491791 1065469 := bbase (se 3 (by rfl) ⟨199775, by rfl⟩ : syracuseStep 1065469 = 399551) (by norm_num)
theorem B737813 : Blo 491791 737813 := bbase (se 6 (by rfl) ⟨17292, by rfl⟩ : syracuseStep 737813 = 34585) (by norm_num)
theorem B737837 : Blo 491791 737837 := bbase (se 3 (by rfl) ⟨138344, by rfl⟩ : syracuseStep 737837 = 276689) (by norm_num)
theorem B836149 : Blo 491791 836149 := bbase (se 5 (by rfl) ⟨39194, by rfl⟩ : syracuseStep 836149 = 78389) (by norm_num)
theorem B737861 : Blo 491791 737861 := bbase (se 4 (by rfl) ⟨69174, by rfl⟩ : syracuseStep 737861 = 138349) (by norm_num)
theorem B737885 : Blo 491791 737885 := bbase (se 3 (by rfl) ⟨138353, by rfl⟩ : syracuseStep 737885 = 276707) (by norm_num)
theorem B737909 : Blo 491791 737909 := bbase (se 5 (by rfl) ⟨34589, by rfl⟩ : syracuseStep 737909 = 69179) (by norm_num)
theorem B934517 : Blo 491791 934517 := bbase (se 5 (by rfl) ⟨43805, by rfl⟩ : syracuseStep 934517 = 87611) (by norm_num)
theorem B737933 : Blo 491791 737933 := bbase (se 3 (by rfl) ⟨138362, by rfl⟩ : syracuseStep 737933 = 276725) (by norm_num)
theorem B836237 : Blo 491791 836237 := bbase (se 3 (by rfl) ⟨156794, by rfl⟩ : syracuseStep 836237 = 313589) (by norm_num)
theorem B1000085 : Blo 491791 1000085 := bbase (se 6 (by rfl) ⟨23439, by rfl⟩ : syracuseStep 1000085 = 46879) (by norm_num)
theorem B737957 : Blo 491791 737957 := bbase (se 4 (by rfl) ⟨69183, by rfl⟩ : syracuseStep 737957 = 138367) (by norm_num)
theorem B737981 : Blo 491791 737981 := bbase (se 3 (by rfl) ⟨138371, by rfl⟩ : syracuseStep 737981 = 276743) (by norm_num)
theorem B738005 : Blo 491791 738005 := bbase (se 7 (by rfl) ⟨8648, by rfl⟩ : syracuseStep 738005 = 17297) (by norm_num)
theorem B738029 : Blo 491791 738029 := bbase (se 3 (by rfl) ⟨138380, by rfl⟩ : syracuseStep 738029 = 276761) (by norm_num)
theorem B738053 : Blo 491791 738053 := bbase (se 4 (by rfl) ⟨69192, by rfl⟩ : syracuseStep 738053 = 138385) (by norm_num)
theorem B934669 : Blo 491791 934669 := bbase (se 3 (by rfl) ⟨175250, by rfl⟩ : syracuseStep 934669 = 350501) (by norm_num)
theorem B836365 : Blo 491791 836365 := bbase (se 3 (by rfl) ⟨156818, by rfl⟩ : syracuseStep 836365 = 313637) (by norm_num)
theorem B738077 : Blo 491791 738077 := bbase (se 3 (by rfl) ⟨138389, by rfl⟩ : syracuseStep 738077 = 276779) (by norm_num)
theorem B738101 : Blo 491791 738101 := bbase (se 5 (by rfl) ⟨34598, by rfl⟩ : syracuseStep 738101 = 69197) (by norm_num)
theorem B738125 : Blo 491791 738125 := bbase (se 3 (by rfl) ⟨138398, by rfl⟩ : syracuseStep 738125 = 276797) (by norm_num)
theorem B738149 : Blo 491791 738149 := bbase (se 4 (by rfl) ⟨69201, by rfl⟩ : syracuseStep 738149 = 138403) (by norm_num)
theorem B836453 : Blo 491791 836453 := bbase (se 4 (by rfl) ⟨78417, by rfl⟩ : syracuseStep 836453 = 156835) (by norm_num)
theorem B738173 : Blo 491791 738173 := bbase (se 3 (by rfl) ⟨138407, by rfl⟩ : syracuseStep 738173 = 276815) (by norm_num)
theorem B738197 : Blo 491791 738197 := bbase (se 6 (by rfl) ⟨17301, by rfl⟩ : syracuseStep 738197 = 34603) (by norm_num)
theorem B1524629 : Blo 491791 1524629 := bbase (se 6 (by rfl) ⟨35733, by rfl⟩ : syracuseStep 1524629 = 71467) (by norm_num)
theorem B738221 : Blo 491791 738221 := bbase (se 3 (by rfl) ⟨138416, by rfl⟩ : syracuseStep 738221 = 276833) (by norm_num)
theorem B738245 : Blo 491791 738245 := bbase (se 4 (by rfl) ⟨69210, by rfl⟩ : syracuseStep 738245 = 138421) (by norm_num)
theorem B738269 : Blo 491791 738269 := bbase (se 3 (by rfl) ⟨138425, by rfl⟩ : syracuseStep 738269 = 276851) (by norm_num)
theorem B836581 : Blo 491791 836581 := bbase (se 4 (by rfl) ⟨78429, by rfl⟩ : syracuseStep 836581 = 156859) (by norm_num)
theorem B738293 : Blo 491791 738293 := bbase (se 5 (by rfl) ⟨34607, by rfl⟩ : syracuseStep 738293 = 69215) (by norm_num)
theorem B1065973 : Blo 491791 1065973 := bbase (se 5 (by rfl) ⟨49967, by rfl⟩ : syracuseStep 1065973 = 99935) (by norm_num)
theorem B738317 : Blo 491791 738317 := bbase (se 3 (by rfl) ⟨138434, by rfl⟩ : syracuseStep 738317 = 276869) (by norm_num)
theorem B738341 : Blo 491791 738341 := bbase (se 4 (by rfl) ⟨69219, by rfl⟩ : syracuseStep 738341 = 138439) (by norm_num)
theorem B738365 : Blo 491791 738365 := bbase (se 3 (by rfl) ⟨138443, by rfl⟩ : syracuseStep 738365 = 276887) (by norm_num)
theorem B934973 : Blo 491791 934973 := bbase (se 3 (by rfl) ⟨175307, by rfl⟩ : syracuseStep 934973 = 350615) (by norm_num)
theorem B738389 : Blo 491791 738389 := bbase (se 8 (by rfl) ⟨4326, by rfl⟩ : syracuseStep 738389 = 8653) (by norm_num)
theorem B738413 : Blo 491791 738413 := bbase (se 3 (by rfl) ⟨138452, by rfl⟩ : syracuseStep 738413 = 276905) (by norm_num)
theorem B738437 : Blo 491791 738437 := bbase (se 4 (by rfl) ⟨69228, by rfl⟩ : syracuseStep 738437 = 138457) (by norm_num)
theorem B2114693 : Blo 491791 2114693 := bbase (se 4 (by rfl) ⟨198252, by rfl⟩ : syracuseStep 2114693 = 396505) (by norm_num)
theorem B738461 : Blo 491791 738461 := bbase (se 3 (by rfl) ⟨138461, by rfl⟩ : syracuseStep 738461 = 276923) (by norm_num)
theorem B1688741 : Blo 491791 1688741 := bbase (se 4 (by rfl) ⟨158319, by rfl⟩ : syracuseStep 1688741 = 316639) (by norm_num)
theorem B2802869 : Blo 491791 2802869 := bbase (se 5 (by rfl) ⟨131384, by rfl⟩ : syracuseStep 2802869 = 262769) (by norm_num)
theorem B738485 : Blo 491791 738485 := bbase (se 5 (by rfl) ⟨34616, by rfl⟩ : syracuseStep 738485 = 69233) (by norm_num)
theorem B2999477 : Blo 491791 2999477 := bbase (se 5 (by rfl) ⟨140600, by rfl⟩ : syracuseStep 2999477 = 281201) (by norm_num)
theorem B738509 : Blo 491791 738509 := bbase (se 3 (by rfl) ⟨138470, by rfl⟩ : syracuseStep 738509 = 276941) (by norm_num)
theorem B738533 : Blo 491791 738533 := bbase (se 4 (by rfl) ⟨69237, by rfl⟩ : syracuseStep 738533 = 138475) (by norm_num)
theorem B738557 : Blo 491791 738557 := bbase (se 3 (by rfl) ⟨138479, by rfl⟩ : syracuseStep 738557 = 276959) (by norm_num)
theorem B738581 : Blo 491791 738581 := bbase (se 6 (by rfl) ⟨17310, by rfl⟩ : syracuseStep 738581 = 34621) (by norm_num)
theorem B738605 : Blo 491791 738605 := bbase (se 3 (by rfl) ⟨138488, by rfl⟩ : syracuseStep 738605 = 276977) (by norm_num)
theorem B738629 : Blo 491791 738629 := bbase (se 4 (by rfl) ⟨69246, by rfl⟩ : syracuseStep 738629 = 138493) (by norm_num)
theorem B738653 : Blo 491791 738653 := bbase (se 3 (by rfl) ⟨138497, by rfl⟩ : syracuseStep 738653 = 276995) (by norm_num)
theorem B738677 : Blo 491791 738677 := bbase (se 5 (by rfl) ⟨34625, by rfl⟩ : syracuseStep 738677 = 69251) (by norm_num)
theorem B738701 : Blo 491791 738701 := bbase (se 3 (by rfl) ⟨138506, by rfl⟩ : syracuseStep 738701 = 277013) (by norm_num)
theorem B738725 : Blo 491791 738725 := bbase (se 4 (by rfl) ⟨69255, by rfl⟩ : syracuseStep 738725 = 138511) (by norm_num)
theorem B738749 : Blo 491791 738749 := bbase (se 3 (by rfl) ⟨138515, by rfl⟩ : syracuseStep 738749 = 277031) (by norm_num)
theorem B738773 : Blo 491791 738773 := bbase (se 7 (by rfl) ⟨8657, by rfl⟩ : syracuseStep 738773 = 17315) (by norm_num)
theorem B2508245 : Blo 491791 2508245 := bbase (se 7 (by rfl) ⟨29393, by rfl⟩ : syracuseStep 2508245 = 58787) (by norm_num)
theorem B738797 : Blo 491791 738797 := bbase (se 3 (by rfl) ⟨138524, by rfl⟩ : syracuseStep 738797 = 277049) (by norm_num)
theorem B738821 : Blo 491791 738821 := bbase (se 4 (by rfl) ⟨69264, by rfl⟩ : syracuseStep 738821 = 138529) (by norm_num)
theorem B738845 : Blo 491791 738845 := bbase (se 3 (by rfl) ⟨138533, by rfl⟩ : syracuseStep 738845 = 277067) (by norm_num)
theorem B738869 : Blo 491791 738869 := bbase (se 5 (by rfl) ⟨34634, by rfl⟩ : syracuseStep 738869 = 69269) (by norm_num)
theorem B738893 : Blo 491791 738893 := bbase (se 3 (by rfl) ⟨138542, by rfl⟩ : syracuseStep 738893 = 277085) (by norm_num)
theorem B738917 : Blo 491791 738917 := bbase (se 4 (by rfl) ⟨69273, by rfl⟩ : syracuseStep 738917 = 138547) (by norm_num)
theorem B738941 : Blo 491791 738941 := bbase (se 3 (by rfl) ⟨138551, by rfl⟩ : syracuseStep 738941 = 277103) (by norm_num)
theorem B738965 : Blo 491791 738965 := bbase (se 6 (by rfl) ⟨17319, by rfl⟩ : syracuseStep 738965 = 34639) (by norm_num)
theorem B738989 : Blo 491791 738989 := bbase (se 3 (by rfl) ⟨138560, by rfl⟩ : syracuseStep 738989 = 277121) (by norm_num)
theorem B739013 : Blo 491791 739013 := bbase (se 4 (by rfl) ⟨69282, by rfl⟩ : syracuseStep 739013 = 138565) (by norm_num)
theorem B739037 : Blo 491791 739037 := bbase (se 3 (by rfl) ⟨138569, by rfl⟩ : syracuseStep 739037 = 277139) (by norm_num)
theorem B739061 : Blo 491791 739061 := bbase (se 5 (by rfl) ⟨34643, by rfl⟩ : syracuseStep 739061 = 69287) (by norm_num)
theorem B739085 : Blo 491791 739085 := bbase (se 3 (by rfl) ⟨138578, by rfl⟩ : syracuseStep 739085 = 277157) (by norm_num)
theorem B739109 : Blo 491791 739109 := bbase (se 4 (by rfl) ⟨69291, by rfl⟩ : syracuseStep 739109 = 138583) (by norm_num)
theorem B935725 : Blo 491791 935725 := bbase (se 3 (by rfl) ⟨175448, by rfl⟩ : syracuseStep 935725 = 350897) (by norm_num)
theorem B739133 : Blo 491791 739133 := bbase (se 3 (by rfl) ⟨138587, by rfl⟩ : syracuseStep 739133 = 277175) (by norm_num)
theorem B739157 : Blo 491791 739157 := bbase (se 9 (by rfl) ⟨2165, by rfl⟩ : syracuseStep 739157 = 4331) (by norm_num)
theorem B739181 : Blo 491791 739181 := bbase (se 3 (by rfl) ⟨138596, by rfl⟩ : syracuseStep 739181 = 277193) (by norm_num)
theorem B3164021 : Blo 491791 3164021 := bbase (se 5 (by rfl) ⟨148313, by rfl⟩ : syracuseStep 3164021 = 296627) (by norm_num)
theorem B739205 : Blo 491791 739205 := bbase (se 4 (by rfl) ⟨69300, by rfl⟩ : syracuseStep 739205 = 138601) (by norm_num)
theorem B739229 : Blo 491791 739229 := bbase (se 3 (by rfl) ⟨138605, by rfl⟩ : syracuseStep 739229 = 277211) (by norm_num)
theorem B739253 : Blo 491791 739253 := bbase (se 5 (by rfl) ⟨34652, by rfl⟩ : syracuseStep 739253 = 69305) (by norm_num)
theorem B935869 : Blo 491791 935869 := bbase (se 3 (by rfl) ⟨175475, by rfl⟩ : syracuseStep 935869 = 350951) (by norm_num)
theorem B739277 : Blo 491791 739277 := bbase (se 3 (by rfl) ⟨138614, by rfl⟩ : syracuseStep 739277 = 277229) (by norm_num)
theorem B739301 : Blo 491791 739301 := bbase (se 4 (by rfl) ⟨69309, by rfl⟩ : syracuseStep 739301 = 138619) (by norm_num)
theorem B739325 : Blo 491791 739325 := bbase (se 3 (by rfl) ⟨138623, by rfl⟩ : syracuseStep 739325 = 277247) (by norm_num)
theorem B739349 : Blo 491791 739349 := bbase (se 6 (by rfl) ⟨17328, by rfl⟩ : syracuseStep 739349 = 34657) (by norm_num)
theorem B739373 : Blo 491791 739373 := bbase (se 3 (by rfl) ⟨138632, by rfl⟩ : syracuseStep 739373 = 277265) (by norm_num)
theorem B739397 : Blo 491791 739397 := bbase (se 4 (by rfl) ⟨69318, by rfl⟩ : syracuseStep 739397 = 138637) (by norm_num)
theorem B739421 : Blo 491791 739421 := bbase (se 3 (by rfl) ⟨138641, by rfl⟩ : syracuseStep 739421 = 277283) (by norm_num)
theorem B936029 : Blo 491791 936029 := bbase (se 3 (by rfl) ⟨175505, by rfl⟩ : syracuseStep 936029 = 351011) (by norm_num)
theorem B1263725 : Blo 491791 1263725 := bbase (se 3 (by rfl) ⟨236948, by rfl⟩ : syracuseStep 1263725 = 473897) (by norm_num)
theorem B739445 : Blo 491791 739445 := bbase (se 5 (by rfl) ⟨34661, by rfl⟩ : syracuseStep 739445 = 69323) (by norm_num)
theorem B739469 : Blo 491791 739469 := bbase (se 3 (by rfl) ⟨138650, by rfl⟩ : syracuseStep 739469 = 277301) (by norm_num)
theorem B739493 : Blo 491791 739493 := bbase (se 4 (by rfl) ⟨69327, by rfl⟩ : syracuseStep 739493 = 138655) (by norm_num)
theorem B739517 : Blo 491791 739517 := bbase (se 3 (by rfl) ⟨138659, by rfl⟩ : syracuseStep 739517 = 277319) (by norm_num)
theorem B739541 : Blo 491791 739541 := bbase (se 7 (by rfl) ⟨8666, by rfl⟩ : syracuseStep 739541 = 17333) (by norm_num)
theorem B739565 : Blo 491791 739565 := bbase (se 3 (by rfl) ⟨138668, by rfl⟩ : syracuseStep 739565 = 277337) (by norm_num)
theorem B936173 : Blo 491791 936173 := bbase (se 3 (by rfl) ⟨175532, by rfl⟩ : syracuseStep 936173 = 351065) (by norm_num)
theorem B739589 : Blo 491791 739589 := bbase (se 4 (by rfl) ⟨69336, by rfl⟩ : syracuseStep 739589 = 138673) (by norm_num)
theorem B739613 : Blo 491791 739613 := bbase (se 3 (by rfl) ⟨138677, by rfl⟩ : syracuseStep 739613 = 277355) (by norm_num)
theorem B739637 : Blo 491791 739637 := bbase (se 5 (by rfl) ⟨34670, by rfl⟩ : syracuseStep 739637 = 69341) (by norm_num)
theorem B739661 : Blo 491791 739661 := bbase (se 3 (by rfl) ⟨138686, by rfl⟩ : syracuseStep 739661 = 277373) (by norm_num)
theorem B739685 : Blo 491791 739685 := bbase (se 4 (by rfl) ⟨69345, by rfl⟩ : syracuseStep 739685 = 138691) (by norm_num)
theorem B739709 : Blo 491791 739709 := bbase (se 3 (by rfl) ⟨138695, by rfl⟩ : syracuseStep 739709 = 277391) (by norm_num)
theorem B739733 : Blo 491791 739733 := bbase (se 6 (by rfl) ⟨17337, by rfl⟩ : syracuseStep 739733 = 34675) (by norm_num)
theorem B739757 : Blo 491791 739757 := bbase (se 3 (by rfl) ⟨138704, by rfl⟩ : syracuseStep 739757 = 277409) (by norm_num)
theorem B739781 : Blo 491791 739781 := bbase (se 4 (by rfl) ⟨69354, by rfl⟩ : syracuseStep 739781 = 138709) (by norm_num)
theorem B739805 : Blo 491791 739805 := bbase (se 3 (by rfl) ⟨138713, by rfl⟩ : syracuseStep 739805 = 277427) (by norm_num)
theorem B739829 : Blo 491791 739829 := bbase (se 5 (by rfl) ⟨34679, by rfl⟩ : syracuseStep 739829 = 69359) (by norm_num)
theorem B739853 : Blo 491791 739853 := bbase (se 3 (by rfl) ⟨138722, by rfl⟩ : syracuseStep 739853 = 277445) (by norm_num)
theorem B936461 : Blo 491791 936461 := bbase (se 3 (by rfl) ⟨175586, by rfl⟩ : syracuseStep 936461 = 351173) (by norm_num)
theorem B2378261 : Blo 491791 2378261 := bbase (se 6 (by rfl) ⟨55740, by rfl⟩ : syracuseStep 2378261 = 111481) (by norm_num)
theorem B739877 : Blo 491791 739877 := bbase (se 4 (by rfl) ⟨69363, by rfl⟩ : syracuseStep 739877 = 138727) (by norm_num)
theorem B739901 : Blo 491791 739901 := bbase (se 3 (by rfl) ⟨138731, by rfl⟩ : syracuseStep 739901 = 277463) (by norm_num)
theorem B739925 : Blo 491791 739925 := bbase (se 8 (by rfl) ⟨4335, by rfl⟩ : syracuseStep 739925 = 8671) (by norm_num)
theorem B739949 : Blo 491791 739949 := bbase (se 3 (by rfl) ⟨138740, by rfl⟩ : syracuseStep 739949 = 277481) (by norm_num)
theorem B739973 : Blo 491791 739973 := bbase (se 4 (by rfl) ⟨69372, by rfl⟩ : syracuseStep 739973 = 138745) (by norm_num)
theorem B1428101 : Blo 491791 1428101 := bbase (se 4 (by rfl) ⟨133884, by rfl⟩ : syracuseStep 1428101 = 267769) (by norm_num)
theorem B739997 : Blo 491791 739997 := bbase (se 3 (by rfl) ⟨138749, by rfl⟩ : syracuseStep 739997 = 277499) (by norm_num)
theorem B936613 : Blo 491791 936613 := bbase (se 4 (by rfl) ⟨87807, by rfl⟩ : syracuseStep 936613 = 175615) (by norm_num)
theorem B740021 : Blo 491791 740021 := bbase (se 5 (by rfl) ⟨34688, by rfl⟩ : syracuseStep 740021 = 69377) (by norm_num)
theorem B740045 : Blo 491791 740045 := bbase (se 3 (by rfl) ⟨138758, by rfl⟩ : syracuseStep 740045 = 277517) (by norm_num)
theorem B740069 : Blo 491791 740069 := bbase (se 4 (by rfl) ⟨69381, by rfl⟩ : syracuseStep 740069 = 138763) (by norm_num)
theorem B2509541 : Blo 491791 2509541 := bbase (se 4 (by rfl) ⟨235269, by rfl⟩ : syracuseStep 2509541 = 470539) (by norm_num)
theorem B740093 : Blo 491791 740093 := bbase (se 3 (by rfl) ⟨138767, by rfl⟩ : syracuseStep 740093 = 277535) (by norm_num)
theorem B740117 : Blo 491791 740117 := bbase (se 6 (by rfl) ⟨17346, by rfl⟩ : syracuseStep 740117 = 34693) (by norm_num)
theorem B740141 : Blo 491791 740141 := bbase (se 3 (by rfl) ⟨138776, by rfl⟩ : syracuseStep 740141 = 277553) (by norm_num)
theorem B740165 : Blo 491791 740165 := bbase (se 4 (by rfl) ⟨69390, by rfl⟩ : syracuseStep 740165 = 138781) (by norm_num)
theorem B740189 : Blo 491791 740189 := bbase (se 3 (by rfl) ⟨138785, by rfl⟩ : syracuseStep 740189 = 277571) (by norm_num)
theorem B740213 : Blo 491791 740213 := bbase (se 5 (by rfl) ⟨34697, by rfl⟩ : syracuseStep 740213 = 69395) (by norm_num)
theorem B2116469 : Blo 491791 2116469 := bbase (se 5 (by rfl) ⟨99209, by rfl⟩ : syracuseStep 2116469 = 198419) (by norm_num)
theorem B740237 : Blo 491791 740237 := bbase (se 3 (by rfl) ⟨138794, by rfl⟩ : syracuseStep 740237 = 277589) (by norm_num)
theorem B543629 : Blo 491791 543629 := bbase (se 3 (by rfl) ⟨101930, by rfl⟩ : syracuseStep 543629 = 203861) (by norm_num)
theorem B740261 : Blo 491791 740261 := bbase (se 4 (by rfl) ⟨69399, by rfl⟩ : syracuseStep 740261 = 138799) (by norm_num)
theorem B740285 : Blo 491791 740285 := bbase (se 3 (by rfl) ⟨138803, by rfl⟩ : syracuseStep 740285 = 277607) (by norm_num)
theorem B936917 : Blo 491791 936917 := bbase (se 7 (by rfl) ⟨10979, by rfl⟩ : syracuseStep 936917 = 21959) (by norm_num)
theorem B740309 : Blo 491791 740309 := bbase (se 7 (by rfl) ⟨8675, by rfl⟩ : syracuseStep 740309 = 17351) (by norm_num)
theorem B740333 : Blo 491791 740333 := bbase (se 3 (by rfl) ⟨138812, by rfl⟩ : syracuseStep 740333 = 277625) (by norm_num)
theorem B740357 : Blo 491791 740357 := bbase (se 4 (by rfl) ⟨69408, by rfl⟩ : syracuseStep 740357 = 138817) (by norm_num)
theorem B9522197 : Blo 491791 9522197 := bbase (se 6 (by rfl) ⟨223176, by rfl⟩ : syracuseStep 9522197 = 446353) (by norm_num)
theorem B740381 : Blo 491791 740381 := bbase (se 3 (by rfl) ⟨138821, by rfl⟩ : syracuseStep 740381 = 277643) (by norm_num)
theorem B740405 : Blo 491791 740405 := bbase (se 5 (by rfl) ⟨34706, by rfl⟩ : syracuseStep 740405 = 69413) (by norm_num)
theorem B740429 : Blo 491791 740429 := bbase (se 3 (by rfl) ⟨138830, by rfl⟩ : syracuseStep 740429 = 277661) (by norm_num)
theorem B740453 : Blo 491791 740453 := bbase (se 4 (by rfl) ⟨69417, by rfl⟩ : syracuseStep 740453 = 138835) (by norm_num)
theorem B740477 : Blo 491791 740477 := bbase (se 3 (by rfl) ⟨138839, by rfl⟩ : syracuseStep 740477 = 277679) (by norm_num)
theorem B740501 : Blo 491791 740501 := bbase (se 6 (by rfl) ⟨17355, by rfl⟩ : syracuseStep 740501 = 34711) (by norm_num)
theorem B740525 : Blo 491791 740525 := bbase (se 3 (by rfl) ⟨138848, by rfl⟩ : syracuseStep 740525 = 277697) (by norm_num)
theorem B740549 : Blo 491791 740549 := bbase (se 4 (by rfl) ⟨69426, by rfl⟩ : syracuseStep 740549 = 138853) (by norm_num)
theorem B740573 : Blo 491791 740573 := bbase (se 3 (by rfl) ⟨138857, by rfl⟩ : syracuseStep 740573 = 277715) (by norm_num)
theorem B740597 : Blo 491791 740597 := bbase (se 5 (by rfl) ⟨34715, by rfl⟩ : syracuseStep 740597 = 69431) (by norm_num)
theorem B740621 : Blo 491791 740621 := bbase (se 3 (by rfl) ⟨138866, by rfl⟩ : syracuseStep 740621 = 277733) (by norm_num)
theorem B740645 : Blo 491791 740645 := bbase (se 4 (by rfl) ⟨69435, by rfl⟩ : syracuseStep 740645 = 138871) (by norm_num)
theorem B740669 : Blo 491791 740669 := bbase (se 3 (by rfl) ⟨138875, by rfl⟩ : syracuseStep 740669 = 277751) (by norm_num)
theorem B740693 : Blo 491791 740693 := bbase (se 11 (by rfl) ⟨542, by rfl⟩ : syracuseStep 740693 = 1085) (by norm_num)
theorem B740717 : Blo 491791 740717 := bbase (se 3 (by rfl) ⟨138884, by rfl⟩ : syracuseStep 740717 = 277769) (by norm_num)
theorem B740741 : Blo 491791 740741 := bbase (se 4 (by rfl) ⟨69444, by rfl⟩ : syracuseStep 740741 = 138889) (by norm_num)
theorem B740765 : Blo 491791 740765 := bbase (se 3 (by rfl) ⟨138893, by rfl⟩ : syracuseStep 740765 = 277787) (by norm_num)
theorem B740789 : Blo 491791 740789 := bbase (se 5 (by rfl) ⟨34724, by rfl⟩ : syracuseStep 740789 = 69449) (by norm_num)
theorem B740813 : Blo 491791 740813 := bbase (se 3 (by rfl) ⟨138902, by rfl⟩ : syracuseStep 740813 = 277805) (by norm_num)
theorem B740837 : Blo 491791 740837 := bbase (se 4 (by rfl) ⟨69453, by rfl⟩ : syracuseStep 740837 = 138907) (by norm_num)
theorem B740861 : Blo 491791 740861 := bbase (se 3 (by rfl) ⟨138911, by rfl⟩ : syracuseStep 740861 = 277823) (by norm_num)
theorem B740885 : Blo 491791 740885 := bbase (se 6 (by rfl) ⟨17364, by rfl⟩ : syracuseStep 740885 = 34729) (by norm_num)
theorem B740909 : Blo 491791 740909 := bbase (se 3 (by rfl) ⟨138920, by rfl⟩ : syracuseStep 740909 = 277841) (by norm_num)
theorem B740933 : Blo 491791 740933 := bbase (se 4 (by rfl) ⟨69462, by rfl⟩ : syracuseStep 740933 = 138925) (by norm_num)
theorem B740957 : Blo 491791 740957 := bbase (se 3 (by rfl) ⟨138929, by rfl⟩ : syracuseStep 740957 = 277859) (by norm_num)
theorem B740981 : Blo 491791 740981 := bbase (se 5 (by rfl) ⟨34733, by rfl⟩ : syracuseStep 740981 = 69467) (by norm_num)
theorem B741005 : Blo 491791 741005 := bbase (se 3 (by rfl) ⟨138938, by rfl⟩ : syracuseStep 741005 = 277877) (by norm_num)
theorem B741029 : Blo 491791 741029 := bbase (se 4 (by rfl) ⟨69471, by rfl⟩ : syracuseStep 741029 = 138943) (by norm_num)
theorem B741053 : Blo 491791 741053 := bbase (se 3 (by rfl) ⟨138947, by rfl⟩ : syracuseStep 741053 = 277895) (by norm_num)
theorem B937669 : Blo 491791 937669 := bbase (se 4 (by rfl) ⟨87906, by rfl⟩ : syracuseStep 937669 = 175813) (by norm_num)
theorem B741077 : Blo 491791 741077 := bbase (se 7 (by rfl) ⟨8684, by rfl⟩ : syracuseStep 741077 = 17369) (by norm_num)
theorem B741101 : Blo 491791 741101 := bbase (se 3 (by rfl) ⟨138956, by rfl⟩ : syracuseStep 741101 = 277913) (by norm_num)
theorem B2674421 : Blo 491791 2674421 := bbase (se 5 (by rfl) ⟨125363, by rfl⟩ : syracuseStep 2674421 = 250727) (by norm_num)
theorem B741125 : Blo 491791 741125 := bbase (se 4 (by rfl) ⟨69480, by rfl⟩ : syracuseStep 741125 = 138961) (by norm_num)
theorem B741149 : Blo 491791 741149 := bbase (se 3 (by rfl) ⟨138965, by rfl⟩ : syracuseStep 741149 = 277931) (by norm_num)
theorem B741173 : Blo 491791 741173 := bbase (se 5 (by rfl) ⟨34742, by rfl⟩ : syracuseStep 741173 = 69485) (by norm_num)
theorem B741197 : Blo 491791 741197 := bbase (se 3 (by rfl) ⟨138974, by rfl⟩ : syracuseStep 741197 = 277949) (by norm_num)
theorem B937813 : Blo 491791 937813 := bbase (se 9 (by rfl) ⟨2747, by rfl⟩ : syracuseStep 937813 = 5495) (by norm_num)
theorem B2117461 : Blo 491791 2117461 := bbase (se 9 (by rfl) ⟨6203, by rfl⟩ : syracuseStep 2117461 = 12407) (by norm_num)
theorem B741221 : Blo 491791 741221 := bbase (se 4 (by rfl) ⟨69489, by rfl⟩ : syracuseStep 741221 = 138979) (by norm_num)
theorem B741245 : Blo 491791 741245 := bbase (se 3 (by rfl) ⟨138983, by rfl⟩ : syracuseStep 741245 = 277967) (by norm_num)
theorem B741269 : Blo 491791 741269 := bbase (se 6 (by rfl) ⟨17373, by rfl⟩ : syracuseStep 741269 = 34747) (by norm_num)
theorem B741293 : Blo 491791 741293 := bbase (se 3 (by rfl) ⟨138992, by rfl⟩ : syracuseStep 741293 = 277985) (by norm_num)
theorem B741317 : Blo 491791 741317 := bbase (se 4 (by rfl) ⟨69498, by rfl⟩ : syracuseStep 741317 = 138997) (by norm_num)
theorem B741341 : Blo 491791 741341 := bbase (se 3 (by rfl) ⟨139001, by rfl⟩ : syracuseStep 741341 = 278003) (by norm_num)
theorem B937973 : Blo 491791 937973 := bbase (se 5 (by rfl) ⟨43967, by rfl⟩ : syracuseStep 937973 = 87935) (by norm_num)
theorem B741365 : Blo 491791 741365 := bbase (se 5 (by rfl) ⟨34751, by rfl⟩ : syracuseStep 741365 = 69503) (by norm_num)
theorem B741389 : Blo 491791 741389 := bbase (se 3 (by rfl) ⟨139010, by rfl⟩ : syracuseStep 741389 = 278021) (by norm_num)
theorem B741413 : Blo 491791 741413 := bbase (se 4 (by rfl) ⟨69507, by rfl⟩ : syracuseStep 741413 = 139015) (by norm_num)
theorem B741437 : Blo 491791 741437 := bbase (se 3 (by rfl) ⟨139019, by rfl⟩ : syracuseStep 741437 = 278039) (by norm_num)
theorem B741461 : Blo 491791 741461 := bbase (se 8 (by rfl) ⟨4344, by rfl⟩ : syracuseStep 741461 = 8689) (by norm_num)
theorem B741485 : Blo 491791 741485 := bbase (se 3 (by rfl) ⟨139028, by rfl⟩ : syracuseStep 741485 = 278057) (by norm_num)
theorem B938117 : Blo 491791 938117 := bbase (se 4 (by rfl) ⟨87948, by rfl⟩ : syracuseStep 938117 = 175897) (by norm_num)
theorem B741509 : Blo 491791 741509 := bbase (se 4 (by rfl) ⟨69516, by rfl⟩ : syracuseStep 741509 = 139033) (by norm_num)
theorem B741533 : Blo 491791 741533 := bbase (se 3 (by rfl) ⟨139037, by rfl⟩ : syracuseStep 741533 = 278075) (by norm_num)
theorem B741557 : Blo 491791 741557 := bbase (se 5 (by rfl) ⟨34760, by rfl⟩ : syracuseStep 741557 = 69521) (by norm_num)
theorem B741581 : Blo 491791 741581 := bbase (se 3 (by rfl) ⟨139046, by rfl⟩ : syracuseStep 741581 = 278093) (by norm_num)
theorem B741605 : Blo 491791 741605 := bbase (se 4 (by rfl) ⟨69525, by rfl⟩ : syracuseStep 741605 = 139051) (by norm_num)
theorem B741629 : Blo 491791 741629 := bbase (se 3 (by rfl) ⟨139055, by rfl⟩ : syracuseStep 741629 = 278111) (by norm_num)
theorem B741653 : Blo 491791 741653 := bbase (se 6 (by rfl) ⟨17382, by rfl⟩ : syracuseStep 741653 = 34765) (by norm_num)
theorem B741677 : Blo 491791 741677 := bbase (se 3 (by rfl) ⟨139064, by rfl⟩ : syracuseStep 741677 = 278129) (by norm_num)
theorem B741701 : Blo 491791 741701 := bbase (se 4 (by rfl) ⟨69534, by rfl⟩ : syracuseStep 741701 = 139069) (by norm_num)
theorem B741725 : Blo 491791 741725 := bbase (se 3 (by rfl) ⟨139073, by rfl⟩ : syracuseStep 741725 = 278147) (by norm_num)
theorem B741749 : Blo 491791 741749 := bbase (se 5 (by rfl) ⟨34769, by rfl⟩ : syracuseStep 741749 = 69539) (by norm_num)
theorem B741773 : Blo 491791 741773 := bbase (se 3 (by rfl) ⟨139082, by rfl⟩ : syracuseStep 741773 = 278165) (by norm_num)
theorem B938405 : Blo 491791 938405 := bbase (se 4 (by rfl) ⟨87975, by rfl⟩ : syracuseStep 938405 = 175951) (by norm_num)
theorem B741797 : Blo 491791 741797 := bbase (se 4 (by rfl) ⟨69543, by rfl⟩ : syracuseStep 741797 = 139087) (by norm_num)
theorem B741821 : Blo 491791 741821 := bbase (se 3 (by rfl) ⟨139091, by rfl⟩ : syracuseStep 741821 = 278183) (by norm_num)
theorem B1331653 : Blo 491791 1331653 := bbase (se 4 (by rfl) ⟨124842, by rfl⟩ : syracuseStep 1331653 = 249685) (by norm_num)
theorem B741845 : Blo 491791 741845 := bbase (se 7 (by rfl) ⟨8693, by rfl⟩ : syracuseStep 741845 = 17387) (by norm_num)
theorem B741869 : Blo 491791 741869 := bbase (se 3 (by rfl) ⟨139100, by rfl⟩ : syracuseStep 741869 = 278201) (by norm_num)
theorem B741893 : Blo 491791 741893 := bbase (se 4 (by rfl) ⟨69552, by rfl⟩ : syracuseStep 741893 = 139105) (by norm_num)
theorem B741917 : Blo 491791 741917 := bbase (se 3 (by rfl) ⟨139109, by rfl⟩ : syracuseStep 741917 = 278219) (by norm_num)
theorem B741941 : Blo 491791 741941 := bbase (se 5 (by rfl) ⟨34778, by rfl⟩ : syracuseStep 741941 = 69557) (by norm_num)
theorem B938557 : Blo 491791 938557 := bbase (se 3 (by rfl) ⟨175979, by rfl⟩ : syracuseStep 938557 = 351959) (by norm_num)
theorem B741965 : Blo 491791 741965 := bbase (se 3 (by rfl) ⟨139118, by rfl⟩ : syracuseStep 741965 = 278237) (by norm_num)
theorem B741989 : Blo 491791 741989 := bbase (se 4 (by rfl) ⟨69561, by rfl⟩ : syracuseStep 741989 = 139123) (by norm_num)
theorem B1004141 : Blo 491791 1004141 := bbase (se 3 (by rfl) ⟨188276, by rfl⟩ : syracuseStep 1004141 = 376553) (by norm_num)
theorem B742013 : Blo 491791 742013 := bbase (se 3 (by rfl) ⟨139127, by rfl⟩ : syracuseStep 742013 = 278255) (by norm_num)
theorem B742037 : Blo 491791 742037 := bbase (se 6 (by rfl) ⟨17391, by rfl⟩ : syracuseStep 742037 = 34783) (by norm_num)
theorem B742061 : Blo 491791 742061 := bbase (se 3 (by rfl) ⟨139136, by rfl⟩ : syracuseStep 742061 = 278273) (by norm_num)
theorem B742085 : Blo 491791 742085 := bbase (se 4 (by rfl) ⟨69570, by rfl⟩ : syracuseStep 742085 = 139141) (by norm_num)
theorem B742109 : Blo 491791 742109 := bbase (se 3 (by rfl) ⟨139145, by rfl⟩ : syracuseStep 742109 = 278291) (by norm_num)
theorem B742133 : Blo 491791 742133 := bbase (se 5 (by rfl) ⟨34787, by rfl⟩ : syracuseStep 742133 = 69575) (by norm_num)
theorem B742157 : Blo 491791 742157 := bbase (se 3 (by rfl) ⟨139154, by rfl⟩ : syracuseStep 742157 = 278309) (by norm_num)
theorem B742181 : Blo 491791 742181 := bbase (se 4 (by rfl) ⟨69579, by rfl⟩ : syracuseStep 742181 = 139159) (by norm_num)
theorem B742205 : Blo 491791 742205 := bbase (se 3 (by rfl) ⟨139163, by rfl⟩ : syracuseStep 742205 = 278327) (by norm_num)
theorem B742229 : Blo 491791 742229 := bbase (se 9 (by rfl) ⟨2174, by rfl⟩ : syracuseStep 742229 = 4349) (by norm_num)
theorem B938861 : Blo 491791 938861 := bbase (se 3 (by rfl) ⟨176036, by rfl⟩ : syracuseStep 938861 = 352073) (by norm_num)
theorem B742253 : Blo 491791 742253 := bbase (se 3 (by rfl) ⟨139172, by rfl⟩ : syracuseStep 742253 = 278345) (by norm_num)
theorem B742277 : Blo 491791 742277 := bbase (se 4 (by rfl) ⟨69588, by rfl⟩ : syracuseStep 742277 = 139177) (by norm_num)
theorem B1659797 : Blo 491791 1659797 := bbase (se 6 (by rfl) ⟨38901, by rfl⟩ : syracuseStep 1659797 = 77803) (by norm_num)
theorem B742301 : Blo 491791 742301 := bbase (se 3 (by rfl) ⟨139181, by rfl⟩ : syracuseStep 742301 = 278363) (by norm_num)
theorem B742325 : Blo 491791 742325 := bbase (se 5 (by rfl) ⟨34796, by rfl⟩ : syracuseStep 742325 = 69593) (by norm_num)
theorem B742349 : Blo 491791 742349 := bbase (se 3 (by rfl) ⟨139190, by rfl⟩ : syracuseStep 742349 = 278381) (by norm_num)
theorem B742373 : Blo 491791 742373 := bbase (se 4 (by rfl) ⟨69597, by rfl⟩ : syracuseStep 742373 = 139195) (by norm_num)
theorem B3167221 : Blo 491791 3167221 := bbase (se 5 (by rfl) ⟨148463, by rfl⟩ : syracuseStep 3167221 = 296927) (by norm_num)
theorem B742397 : Blo 491791 742397 := bbase (se 3 (by rfl) ⟨139199, by rfl⟩ : syracuseStep 742397 = 278399) (by norm_num)
theorem B742421 : Blo 491791 742421 := bbase (se 6 (by rfl) ⟨17400, by rfl⟩ : syracuseStep 742421 = 34801) (by norm_num)
theorem B742445 : Blo 491791 742445 := bbase (se 3 (by rfl) ⟨139208, by rfl⟩ : syracuseStep 742445 = 278417) (by norm_num)
theorem B742469 : Blo 491791 742469 := bbase (se 4 (by rfl) ⟨69606, by rfl⟩ : syracuseStep 742469 = 139213) (by norm_num)
theorem B742493 : Blo 491791 742493 := bbase (se 3 (by rfl) ⟨139217, by rfl⟩ : syracuseStep 742493 = 278435) (by norm_num)
theorem B742517 : Blo 491791 742517 := bbase (se 5 (by rfl) ⟨34805, by rfl⟩ : syracuseStep 742517 = 69611) (by norm_num)
theorem B742541 : Blo 491791 742541 := bbase (se 3 (by rfl) ⟨139226, by rfl⟩ : syracuseStep 742541 = 278453) (by norm_num)
theorem B742565 : Blo 491791 742565 := bbase (se 4 (by rfl) ⟨69615, by rfl⟩ : syracuseStep 742565 = 139231) (by norm_num)
theorem B4215989 : Blo 491791 4215989 := bbase (se 5 (by rfl) ⟨197624, by rfl⟩ : syracuseStep 4215989 = 395249) (by norm_num)
theorem B742589 : Blo 491791 742589 := bbase (se 3 (by rfl) ⟨139235, by rfl⟩ : syracuseStep 742589 = 278471) (by norm_num)
theorem B742613 : Blo 491791 742613 := bbase (se 7 (by rfl) ⟨8702, by rfl⟩ : syracuseStep 742613 = 17405) (by norm_num)
theorem B742637 : Blo 491791 742637 := bbase (se 3 (by rfl) ⟨139244, by rfl⟩ : syracuseStep 742637 = 278489) (by norm_num)
theorem B742661 : Blo 491791 742661 := bbase (se 4 (by rfl) ⟨69624, by rfl⟩ : syracuseStep 742661 = 139249) (by norm_num)
theorem B742685 : Blo 491791 742685 := bbase (se 3 (by rfl) ⟨139253, by rfl⟩ : syracuseStep 742685 = 278507) (by norm_num)
theorem B742709 : Blo 491791 742709 := bbase (se 5 (by rfl) ⟨34814, by rfl⟩ : syracuseStep 742709 = 69629) (by norm_num)
theorem B1660229 : Blo 491791 1660229 := bbase (se 4 (by rfl) ⟨155646, by rfl⟩ : syracuseStep 1660229 = 311293) (by norm_num)
theorem B742733 : Blo 491791 742733 := bbase (se 3 (by rfl) ⟨139262, by rfl⟩ : syracuseStep 742733 = 278525) (by norm_num)
theorem B742757 : Blo 491791 742757 := bbase (se 4 (by rfl) ⟨69633, by rfl⟩ : syracuseStep 742757 = 139267) (by norm_num)
theorem B742781 : Blo 491791 742781 := bbase (se 3 (by rfl) ⟨139271, by rfl⟩ : syracuseStep 742781 = 278543) (by norm_num)
theorem B742805 : Blo 491791 742805 := bbase (se 6 (by rfl) ⟨17409, by rfl⟩ : syracuseStep 742805 = 34819) (by norm_num)
theorem B742829 : Blo 491791 742829 := bbase (se 3 (by rfl) ⟨139280, by rfl⟩ : syracuseStep 742829 = 278561) (by norm_num)
theorem B742853 : Blo 491791 742853 := bbase (se 4 (by rfl) ⟨69642, by rfl⟩ : syracuseStep 742853 = 139285) (by norm_num)
theorem B742877 : Blo 491791 742877 := bbase (se 3 (by rfl) ⟨139289, by rfl⟩ : syracuseStep 742877 = 278579) (by norm_num)
theorem B742901 : Blo 491791 742901 := bbase (se 5 (by rfl) ⟨34823, by rfl⟩ : syracuseStep 742901 = 69647) (by norm_num)
theorem B742925 : Blo 491791 742925 := bbase (se 3 (by rfl) ⟨139298, by rfl⟩ : syracuseStep 742925 = 278597) (by norm_num)
theorem B742949 : Blo 491791 742949 := bbase (se 4 (by rfl) ⟨69651, by rfl⟩ : syracuseStep 742949 = 139303) (by norm_num)
theorem B742973 : Blo 491791 742973 := bbase (se 3 (by rfl) ⟨139307, by rfl⟩ : syracuseStep 742973 = 278615) (by norm_num)
theorem B742997 : Blo 491791 742997 := bbase (se 8 (by rfl) ⟨4353, by rfl⟩ : syracuseStep 742997 = 8707) (by norm_num)
theorem B939613 : Blo 491791 939613 := bbase (se 3 (by rfl) ⟨176177, by rfl⟩ : syracuseStep 939613 = 352355) (by norm_num)
theorem B743021 : Blo 491791 743021 := bbase (se 3 (by rfl) ⟨139316, by rfl⟩ : syracuseStep 743021 = 278633) (by norm_num)
theorem B743045 : Blo 491791 743045 := bbase (se 4 (by rfl) ⟨69660, by rfl⟩ : syracuseStep 743045 = 139321) (by norm_num)
theorem B743069 : Blo 491791 743069 := bbase (se 3 (by rfl) ⟨139325, by rfl⟩ : syracuseStep 743069 = 278651) (by norm_num)
theorem B743093 : Blo 491791 743093 := bbase (se 5 (by rfl) ⟨34832, by rfl⟩ : syracuseStep 743093 = 69665) (by norm_num)
theorem B743117 : Blo 491791 743117 := bbase (se 3 (by rfl) ⟨139334, by rfl⟩ : syracuseStep 743117 = 278669) (by norm_num)
theorem B743141 : Blo 491791 743141 := bbase (se 4 (by rfl) ⟨69669, by rfl⟩ : syracuseStep 743141 = 139339) (by norm_num)
theorem B939757 : Blo 491791 939757 := bbase (se 3 (by rfl) ⟨176204, by rfl⟩ : syracuseStep 939757 = 352409) (by norm_num)
theorem B1660661 : Blo 491791 1660661 := bbase (se 5 (by rfl) ⟨77843, by rfl⟩ : syracuseStep 1660661 = 155687) (by norm_num)
theorem B4511477 : Blo 491791 4511477 := bbase (se 5 (by rfl) ⟨211475, by rfl⟩ : syracuseStep 4511477 = 422951) (by norm_num)
theorem B743165 : Blo 491791 743165 := bbase (se 3 (by rfl) ⟨139343, by rfl⟩ : syracuseStep 743165 = 278687) (by norm_num)
theorem B743189 : Blo 491791 743189 := bbase (se 6 (by rfl) ⟨17418, by rfl⟩ : syracuseStep 743189 = 34837) (by norm_num)
theorem B743213 : Blo 491791 743213 := bbase (se 3 (by rfl) ⟨139352, by rfl⟩ : syracuseStep 743213 = 278705) (by norm_num)
theorem B743237 : Blo 491791 743237 := bbase (se 4 (by rfl) ⟨69678, by rfl⟩ : syracuseStep 743237 = 139357) (by norm_num)
theorem B743261 : Blo 491791 743261 := bbase (se 3 (by rfl) ⟨139361, by rfl⟩ : syracuseStep 743261 = 278723) (by norm_num)
theorem B743285 : Blo 491791 743285 := bbase (se 5 (by rfl) ⟨34841, by rfl⟩ : syracuseStep 743285 = 69683) (by norm_num)
theorem B939917 : Blo 491791 939917 := bbase (se 3 (by rfl) ⟨176234, by rfl⟩ : syracuseStep 939917 = 352469) (by norm_num)
theorem B743309 : Blo 491791 743309 := bbase (se 3 (by rfl) ⟨139370, by rfl⟩ : syracuseStep 743309 = 278741) (by norm_num)
theorem B743333 : Blo 491791 743333 := bbase (se 4 (by rfl) ⟨69687, by rfl⟩ : syracuseStep 743333 = 139375) (by norm_num)
theorem B743357 : Blo 491791 743357 := bbase (se 3 (by rfl) ⟨139379, by rfl⟩ : syracuseStep 743357 = 278759) (by norm_num)
theorem B743381 : Blo 491791 743381 := bbase (se 7 (by rfl) ⟨8711, by rfl⟩ : syracuseStep 743381 = 17423) (by norm_num)
theorem B743405 : Blo 491791 743405 := bbase (se 3 (by rfl) ⟨139388, by rfl⟩ : syracuseStep 743405 = 278777) (by norm_num)
theorem B1366021 : Blo 491791 1366021 := bbase (se 4 (by rfl) ⟨128064, by rfl⟩ : syracuseStep 1366021 = 256129) (by norm_num)
theorem B743429 : Blo 491791 743429 := bbase (se 4 (by rfl) ⟨69696, by rfl⟩ : syracuseStep 743429 = 139393) (by norm_num)
theorem B940061 : Blo 491791 940061 := bbase (se 3 (by rfl) ⟨176261, by rfl⟩ : syracuseStep 940061 = 352523) (by norm_num)
theorem B743453 : Blo 491791 743453 := bbase (se 3 (by rfl) ⟨139397, by rfl⟩ : syracuseStep 743453 = 278795) (by norm_num)
theorem B743477 : Blo 491791 743477 := bbase (se 5 (by rfl) ⟨34850, by rfl⟩ : syracuseStep 743477 = 69701) (by norm_num)
theorem B743501 : Blo 491791 743501 := bbase (se 3 (by rfl) ⟨139406, by rfl⟩ : syracuseStep 743501 = 278813) (by norm_num)
theorem B743525 : Blo 491791 743525 := bbase (se 4 (by rfl) ⟨69705, by rfl⟩ : syracuseStep 743525 = 139411) (by norm_num)
theorem B743549 : Blo 491791 743549 := bbase (se 3 (by rfl) ⟨139415, by rfl⟩ : syracuseStep 743549 = 278831) (by norm_num)
theorem B743573 : Blo 491791 743573 := bbase (se 6 (by rfl) ⟨17427, by rfl⟩ : syracuseStep 743573 = 34855) (by norm_num)
theorem B1661093 : Blo 491791 1661093 := bbase (se 4 (by rfl) ⟨155727, by rfl⟩ : syracuseStep 1661093 = 311455) (by norm_num)
theorem B743597 : Blo 491791 743597 := bbase (se 3 (by rfl) ⟨139424, by rfl⟩ : syracuseStep 743597 = 278849) (by norm_num)
theorem B743621 : Blo 491791 743621 := bbase (se 4 (by rfl) ⟨69714, by rfl⟩ : syracuseStep 743621 = 139429) (by norm_num)
theorem B743645 : Blo 491791 743645 := bbase (se 3 (by rfl) ⟨139433, by rfl⟩ : syracuseStep 743645 = 278867) (by norm_num)
theorem B743669 : Blo 491791 743669 := bbase (se 5 (by rfl) ⟨34859, by rfl⟩ : syracuseStep 743669 = 69719) (by norm_num)
theorem B940349 : Blo 491791 940349 := bbase (se 3 (by rfl) ⟨176315, by rfl⟩ : syracuseStep 940349 = 352631) (by norm_num)
theorem B6019541 : Blo 491791 6019541 := bbase (se 7 (by rfl) ⟨70541, by rfl⟩ : syracuseStep 6019541 = 141083) (by norm_num)
theorem B940501 : Blo 491791 940501 := bbase (se 7 (by rfl) ⟨11021, by rfl⟩ : syracuseStep 940501 = 22043) (by norm_num)
theorem B1694213 : Blo 491791 1694213 := bbase (se 4 (by rfl) ⟨158832, by rfl⟩ : syracuseStep 1694213 = 317665) (by norm_num)
theorem B1661525 : Blo 491791 1661525 := bbase (se 8 (by rfl) ⟨9735, by rfl⟩ : syracuseStep 1661525 = 19471) (by norm_num)
theorem B5331541 : Blo 491791 5331541 := bbase (se 8 (by rfl) ⟨31239, by rfl⟩ : syracuseStep 5331541 = 62479) (by norm_num)
theorem B940805 : Blo 491791 940805 := bbase (se 4 (by rfl) ⟨88200, by rfl⟩ : syracuseStep 940805 = 176401) (by norm_num)
theorem B1661957 : Blo 491791 1661957 := bbase (se 4 (by rfl) ⟨155808, by rfl⟩ : syracuseStep 1661957 = 311617) (by norm_num)
theorem B1334389 : Blo 491791 1334389 := bbase (se 5 (by rfl) ⟨62549, by rfl⟩ : syracuseStep 1334389 = 125099) (by norm_num)
theorem B1334485 : Blo 491791 1334485 := bbase (se 7 (by rfl) ⟨15638, by rfl⟩ : syracuseStep 1334485 = 31277) (by norm_num)
theorem B1662389 : Blo 491791 1662389 := bbase (se 5 (by rfl) ⟨77924, by rfl⟩ : syracuseStep 1662389 = 155849) (by norm_num)
theorem B1662821 : Blo 491791 1662821 := bbase (se 4 (by rfl) ⟨155889, by rfl⟩ : syracuseStep 1662821 = 311779) (by norm_num)
theorem B974845 : Blo 491791 974845 := bbase (se 3 (by rfl) ⟨182783, by rfl⟩ : syracuseStep 974845 = 365567) (by norm_num)
theorem B3760181 : Blo 491791 3760181 := bbase (se 5 (by rfl) ⟨176258, by rfl⟩ : syracuseStep 3760181 = 352517) (by norm_num)
theorem B4218965 : Blo 491791 4218965 := bbase (se 8 (by rfl) ⟨24720, by rfl⟩ : syracuseStep 4218965 = 49441) (by norm_num)
theorem B1663253 : Blo 491791 1663253 := bbase (se 6 (by rfl) ⟨38982, by rfl⟩ : syracuseStep 1663253 = 77965) (by norm_num)
theorem B1106549 : Blo 491791 1106549 := bbase (se 5 (by rfl) ⟨51869, by rfl⟩ : syracuseStep 1106549 = 103739) (by norm_num)
theorem B1106621 : Blo 491791 1106621 := bbase (se 3 (by rfl) ⟨207491, by rfl⟩ : syracuseStep 1106621 = 414983) (by norm_num)
theorem B1663685 : Blo 491791 1663685 := bbase (se 4 (by rfl) ⟨155970, by rfl⟩ : syracuseStep 1663685 = 311941) (by norm_num)
theorem B1106693 : Blo 491791 1106693 := bbase (se 4 (by rfl) ⟨103752, by rfl⟩ : syracuseStep 1106693 = 207505) (by norm_num)
theorem B1106765 : Blo 491791 1106765 := bbase (se 3 (by rfl) ⟨207518, by rfl⟩ : syracuseStep 1106765 = 415037) (by norm_num)
theorem B1106837 : Blo 491791 1106837 := bbase (se 6 (by rfl) ⟨25941, by rfl⟩ : syracuseStep 1106837 = 51883) (by norm_num)
theorem B1106909 : Blo 491791 1106909 := bbase (se 3 (by rfl) ⟨207545, by rfl⟩ : syracuseStep 1106909 = 415091) (by norm_num)
theorem B1106981 : Blo 491791 1106981 := bbase (se 4 (by rfl) ⟨103779, by rfl⟩ : syracuseStep 1106981 = 207559) (by norm_num)
theorem B2810933 : Blo 491791 2810933 := bbase (se 5 (by rfl) ⟨131762, by rfl⟩ : syracuseStep 2810933 = 263525) (by norm_num)
theorem B844877 : Blo 491791 844877 := bbase (se 3 (by rfl) ⟨158414, by rfl⟩ : syracuseStep 844877 = 316829) (by norm_num)
theorem B1107053 : Blo 491791 1107053 := bbase (se 3 (by rfl) ⟨207572, by rfl⟩ : syracuseStep 1107053 = 415145) (by norm_num)
theorem B1664117 : Blo 491791 1664117 := bbase (se 5 (by rfl) ⟨78005, by rfl⟩ : syracuseStep 1664117 = 156011) (by norm_num)
theorem B1107125 : Blo 491791 1107125 := bbase (se 5 (by rfl) ⟨51896, by rfl⟩ : syracuseStep 1107125 = 103793) (by norm_num)
theorem B1205453 : Blo 491791 1205453 := bbase (se 3 (by rfl) ⟨226022, by rfl⟩ : syracuseStep 1205453 = 452045) (by norm_num)
theorem B4515061 : Blo 491791 4515061 := bbase (se 5 (by rfl) ⟨211643, by rfl⟩ : syracuseStep 4515061 = 423287) (by norm_num)
theorem B1107197 : Blo 491791 1107197 := bbase (se 3 (by rfl) ⟨207599, by rfl⟩ : syracuseStep 1107197 = 415199) (by norm_num)
theorem B1107269 : Blo 491791 1107269 := bbase (se 4 (by rfl) ⟨103806, by rfl⟩ : syracuseStep 1107269 = 207613) (by norm_num)
theorem B976205 : Blo 491791 976205 := bbase (se 3 (by rfl) ⟨183038, by rfl⟩ : syracuseStep 976205 = 366077) (by norm_num)
theorem B714101 : Blo 491791 714101 := bbase (se 5 (by rfl) ⟨33473, by rfl⟩ : syracuseStep 714101 = 66947) (by norm_num)
theorem B1107341 : Blo 491791 1107341 := bbase (se 3 (by rfl) ⟨207626, by rfl⟩ : syracuseStep 1107341 = 415253) (by norm_num)
theorem B1107413 : Blo 491791 1107413 := bbase (se 7 (by rfl) ⟨12977, by rfl⟩ : syracuseStep 1107413 = 25955) (by norm_num)
theorem B1107485 : Blo 491791 1107485 := bbase (se 3 (by rfl) ⟨207653, by rfl⟩ : syracuseStep 1107485 = 415307) (by norm_num)
theorem B1664549 : Blo 491791 1664549 := bbase (se 4 (by rfl) ⟨156051, by rfl⟩ : syracuseStep 1664549 = 312103) (by norm_num)
theorem B1107557 : Blo 491791 1107557 := bbase (se 4 (by rfl) ⟨103833, by rfl⟩ : syracuseStep 1107557 = 207667) (by norm_num)
theorem B1107629 : Blo 491791 1107629 := bbase (se 3 (by rfl) ⟨207680, by rfl⟩ : syracuseStep 1107629 = 415361) (by norm_num)
theorem B1107701 : Blo 491791 1107701 := bbase (se 5 (by rfl) ⟨51923, by rfl⟩ : syracuseStep 1107701 = 103847) (by norm_num)
theorem B1107773 : Blo 491791 1107773 := bbase (se 3 (by rfl) ⟨207707, by rfl⟩ : syracuseStep 1107773 = 415415) (by norm_num)
theorem B1107845 : Blo 491791 1107845 := bbase (se 4 (by rfl) ⟨103860, by rfl⟩ : syracuseStep 1107845 = 207721) (by norm_num)
theorem B1107917 : Blo 491791 1107917 := bbase (se 3 (by rfl) ⟨207734, by rfl⟩ : syracuseStep 1107917 = 415469) (by norm_num)
theorem B1664981 : Blo 491791 1664981 := bbase (se 7 (by rfl) ⟨19511, by rfl⟩ : syracuseStep 1664981 = 39023) (by norm_num)
theorem B1107989 : Blo 491791 1107989 := bbase (se 6 (by rfl) ⟨25968, by rfl⟩ : syracuseStep 1107989 = 51937) (by norm_num)
theorem B1108061 : Blo 491791 1108061 := bbase (se 3 (by rfl) ⟨207761, by rfl⟩ : syracuseStep 1108061 = 415523) (by norm_num)
theorem B1108133 : Blo 491791 1108133 := bbase (se 4 (by rfl) ⟨103887, by rfl⟩ : syracuseStep 1108133 = 207775) (by norm_num)
theorem B2812117 : Blo 491791 2812117 := bbase (se 7 (by rfl) ⟨32954, by rfl⟩ : syracuseStep 2812117 = 65909) (by norm_num)
theorem B1108205 : Blo 491791 1108205 := bbase (se 3 (by rfl) ⟨207788, by rfl⟩ : syracuseStep 1108205 = 415577) (by norm_num)
theorem B1894661 : Blo 491791 1894661 := bbase (se 4 (by rfl) ⟨177624, by rfl⟩ : syracuseStep 1894661 = 355249) (by norm_num)
theorem B1272077 : Blo 491791 1272077 := bbase (se 3 (by rfl) ⟨238514, by rfl⟩ : syracuseStep 1272077 = 477029) (by norm_num)
theorem B1108277 : Blo 491791 1108277 := bbase (se 5 (by rfl) ⟨51950, by rfl⟩ : syracuseStep 1108277 = 103901) (by norm_num)
theorem B1403189 : Blo 491791 1403189 := bbase (se 5 (by rfl) ⟨65774, by rfl⟩ : syracuseStep 1403189 = 131549) (by norm_num)
theorem B1108349 : Blo 491791 1108349 := bbase (se 3 (by rfl) ⟨207815, by rfl⟩ : syracuseStep 1108349 = 415631) (by norm_num)
theorem B1665413 : Blo 491791 1665413 := bbase (se 4 (by rfl) ⟨156132, by rfl⟩ : syracuseStep 1665413 = 312265) (by norm_num)
theorem B1108421 : Blo 491791 1108421 := bbase (se 4 (by rfl) ⟨103914, by rfl⟩ : syracuseStep 1108421 = 207829) (by norm_num)
theorem B846301 : Blo 491791 846301 := bbase (se 3 (by rfl) ⟨158681, by rfl⟩ : syracuseStep 846301 = 317363) (by norm_num)
theorem B748021 : Blo 491791 748021 := bbase (se 5 (by rfl) ⟨35063, by rfl⟩ : syracuseStep 748021 = 70127) (by norm_num)
theorem B1108493 : Blo 491791 1108493 := bbase (se 3 (by rfl) ⟨207842, by rfl⟩ : syracuseStep 1108493 = 415685) (by norm_num)
theorem B1108565 : Blo 491791 1108565 := bbase (se 8 (by rfl) ⟨6495, by rfl⟩ : syracuseStep 1108565 = 12991) (by norm_num)
theorem B846445 : Blo 491791 846445 := bbase (se 3 (by rfl) ⟨158708, by rfl⟩ : syracuseStep 846445 = 317417) (by norm_num)
theorem B1108637 : Blo 491791 1108637 := bbase (se 3 (by rfl) ⟨207869, by rfl⟩ : syracuseStep 1108637 = 415739) (by norm_num)
theorem B1108709 : Blo 491791 1108709 := bbase (se 4 (by rfl) ⟨103941, by rfl⟩ : syracuseStep 1108709 = 207883) (by norm_num)
theorem B1108781 : Blo 491791 1108781 := bbase (se 3 (by rfl) ⟨207896, by rfl⟩ : syracuseStep 1108781 = 415793) (by norm_num)
theorem B1665845 : Blo 491791 1665845 := bbase (se 5 (by rfl) ⟨78086, by rfl⟩ : syracuseStep 1665845 = 156173) (by norm_num)
theorem B1108853 : Blo 491791 1108853 := bbase (se 5 (by rfl) ⟨51977, by rfl⟩ : syracuseStep 1108853 = 103955) (by norm_num)
theorem B3173269 : Blo 491791 3173269 := bbase (se 6 (by rfl) ⟨74373, by rfl⟩ : syracuseStep 3173269 = 148747) (by norm_num)
theorem B1108925 : Blo 491791 1108925 := bbase (se 3 (by rfl) ⟨207923, by rfl⟩ : syracuseStep 1108925 = 415847) (by norm_num)
theorem B1108997 : Blo 491791 1108997 := bbase (se 4 (by rfl) ⟨103968, by rfl⟩ : syracuseStep 1108997 = 207937) (by norm_num)
theorem B1109069 : Blo 491791 1109069 := bbase (se 3 (by rfl) ⟨207950, by rfl⟩ : syracuseStep 1109069 = 415901) (by norm_num)
theorem B912493 : Blo 491791 912493 := bbase (se 3 (by rfl) ⟨171092, by rfl⟩ : syracuseStep 912493 = 342185) (by norm_num)
theorem B1109141 : Blo 491791 1109141 := bbase (se 6 (by rfl) ⟨25995, by rfl⟩ : syracuseStep 1109141 = 51991) (by norm_num)
theorem B1109213 : Blo 491791 1109213 := bbase (se 3 (by rfl) ⟨207977, by rfl⟩ : syracuseStep 1109213 = 415955) (by norm_num)
theorem B1666277 : Blo 491791 1666277 := bbase (se 4 (by rfl) ⟨156213, by rfl⟩ : syracuseStep 1666277 = 312427) (by norm_num)
theorem B1109285 : Blo 491791 1109285 := bbase (se 4 (by rfl) ⟨103995, by rfl⟩ : syracuseStep 1109285 = 207991) (by norm_num)
theorem B814429 : Blo 491791 814429 := bbase (se 3 (by rfl) ⟨152705, by rfl⟩ : syracuseStep 814429 = 305411) (by norm_num)
theorem B1109357 : Blo 491791 1109357 := bbase (se 3 (by rfl) ⟨208004, by rfl⟩ : syracuseStep 1109357 = 416009) (by norm_num)
theorem B912797 : Blo 491791 912797 := bbase (se 3 (by rfl) ⟨171149, by rfl⟩ : syracuseStep 912797 = 342299) (by norm_num)
theorem B1109429 : Blo 491791 1109429 := bbase (se 5 (by rfl) ⟨52004, by rfl⟩ : syracuseStep 1109429 = 104009) (by norm_num)
theorem B1404373 : Blo 491791 1404373 := bbase (se 7 (by rfl) ⟨16457, by rfl⟩ : syracuseStep 1404373 = 32915) (by norm_num)
theorem B847325 : Blo 491791 847325 := bbase (se 3 (by rfl) ⟨158873, by rfl⟩ : syracuseStep 847325 = 317747) (by norm_num)
theorem B1109501 : Blo 491791 1109501 := bbase (se 3 (by rfl) ⟨208031, by rfl⟩ : syracuseStep 1109501 = 416063) (by norm_num)
theorem B1109573 : Blo 491791 1109573 := bbase (se 4 (by rfl) ⟨104022, by rfl⟩ : syracuseStep 1109573 = 208045) (by norm_num)
theorem B1404533 : Blo 491791 1404533 := bbase (se 5 (by rfl) ⟨65837, by rfl⟩ : syracuseStep 1404533 = 131675) (by norm_num)
theorem B1109645 : Blo 491791 1109645 := bbase (se 3 (by rfl) ⟨208058, by rfl⟩ : syracuseStep 1109645 = 416117) (by norm_num)
theorem B1666709 : Blo 491791 1666709 := bbase (se 6 (by rfl) ⟨39063, by rfl⟩ : syracuseStep 1666709 = 78127) (by norm_num)
theorem B1109717 : Blo 491791 1109717 := bbase (se 7 (by rfl) ⟨13004, by rfl⟩ : syracuseStep 1109717 = 26009) (by norm_num)
theorem B1109789 : Blo 491791 1109789 := bbase (se 3 (by rfl) ⟨208085, by rfl⟩ : syracuseStep 1109789 = 416171) (by norm_num)
theorem B1109861 : Blo 491791 1109861 := bbase (se 4 (by rfl) ⟨104049, by rfl⟩ : syracuseStep 1109861 = 208099) (by norm_num)
theorem B1404773 : Blo 491791 1404773 := bbase (se 4 (by rfl) ⟨131697, by rfl⟩ : syracuseStep 1404773 = 263395) (by norm_num)
theorem B1109933 : Blo 491791 1109933 := bbase (se 3 (by rfl) ⟨208112, by rfl⟩ : syracuseStep 1109933 = 416225) (by norm_num)
theorem B1110005 : Blo 491791 1110005 := bbase (se 5 (by rfl) ⟨52031, by rfl⟩ : syracuseStep 1110005 = 104063) (by norm_num)
theorem B1404965 : Blo 491791 1404965 := bbase (se 4 (by rfl) ⟨131715, by rfl⟩ : syracuseStep 1404965 = 263431) (by norm_num)
theorem B1110077 : Blo 491791 1110077 := bbase (se 3 (by rfl) ⟨208139, by rfl⟩ : syracuseStep 1110077 = 416279) (by norm_num)
theorem B1667141 : Blo 491791 1667141 := bbase (se 4 (by rfl) ⟨156294, by rfl⟩ : syracuseStep 1667141 = 312589) (by norm_num)
theorem B1110149 : Blo 491791 1110149 := bbase (se 4 (by rfl) ⟨104076, by rfl⟩ : syracuseStep 1110149 = 208153) (by norm_num)
theorem B2814101 : Blo 491791 2814101 := bbase (se 6 (by rfl) ⟨65955, by rfl⟩ : syracuseStep 2814101 = 131911) (by norm_num)
theorem B1896629 : Blo 491791 1896629 := bbase (se 5 (by rfl) ⟨88904, by rfl⟩ : syracuseStep 1896629 = 177809) (by norm_num)
theorem B1110221 : Blo 491791 1110221 := bbase (se 3 (by rfl) ⟨208166, by rfl⟩ : syracuseStep 1110221 = 416333) (by norm_num)
theorem B1110293 : Blo 491791 1110293 := bbase (se 6 (by rfl) ⟨26022, by rfl⟩ : syracuseStep 1110293 = 52045) (by norm_num)
theorem B553297 : Blo 491791 553297 := bbase (se 2 (by rfl) ⟨207486, by rfl⟩ : syracuseStep 553297 = 414973) (by norm_num)
theorem B1110365 : Blo 491791 1110365 := bbase (se 3 (by rfl) ⟨208193, by rfl⟩ : syracuseStep 1110365 = 416387) (by norm_num)
theorem B553333 : Blo 491791 553333 := bbase (se 5 (by rfl) ⟨25937, by rfl⟩ : syracuseStep 553333 = 51875) (by norm_num)
theorem B553369 : Blo 491791 553369 := bbase (se 2 (by rfl) ⟨207513, by rfl⟩ : syracuseStep 553369 = 415027) (by norm_num)
theorem B1110437 : Blo 491791 1110437 := bbase (se 4 (by rfl) ⟨104103, by rfl⟩ : syracuseStep 1110437 = 208207) (by norm_num)
theorem B651689 : Blo 491791 651689 := bbase (se 2 (by rfl) ⟨244383, by rfl⟩ : syracuseStep 651689 = 488767) (by norm_num)
theorem B553405 : Blo 491791 553405 := bbase (se 3 (by rfl) ⟨103763, by rfl⟩ : syracuseStep 553405 = 207527) (by norm_num)
theorem B553441 : Blo 491791 553441 := bbase (se 2 (by rfl) ⟨207540, by rfl⟩ : syracuseStep 553441 = 415081) (by norm_num)
theorem B1110509 : Blo 491791 1110509 := bbase (se 3 (by rfl) ⟨208220, by rfl⟩ : syracuseStep 1110509 = 416441) (by norm_num)
theorem B1667573 : Blo 491791 1667573 := bbase (se 5 (by rfl) ⟨78167, by rfl⟩ : syracuseStep 1667573 = 156335) (by norm_num)
theorem B553477 : Blo 491791 553477 := bbase (se 4 (by rfl) ⟨51888, by rfl⟩ : syracuseStep 553477 = 103777) (by norm_num)
theorem B553513 : Blo 491791 553513 := bbase (se 2 (by rfl) ⟨207567, by rfl⟩ : syracuseStep 553513 = 415135) (by norm_num)
theorem B1110581 : Blo 491791 1110581 := bbase (se 5 (by rfl) ⟨52058, by rfl⟩ : syracuseStep 1110581 = 104117) (by norm_num)
theorem B553549 : Blo 491791 553549 := bbase (se 3 (by rfl) ⟨103790, by rfl⟩ : syracuseStep 553549 = 207581) (by norm_num)
theorem B553585 : Blo 491791 553585 := bbase (se 2 (by rfl) ⟨207594, by rfl⟩ : syracuseStep 553585 = 415189) (by norm_num)
theorem B1110653 : Blo 491791 1110653 := bbase (se 3 (by rfl) ⟨208247, by rfl⟩ : syracuseStep 1110653 = 416495) (by norm_num)
theorem B553621 : Blo 491791 553621 := bbase (se 6 (by rfl) ⟨12975, by rfl⟩ : syracuseStep 553621 = 25951) (by norm_num)
theorem B553657 : Blo 491791 553657 := bbase (se 2 (by rfl) ⟨207621, by rfl⟩ : syracuseStep 553657 = 415243) (by norm_num)
theorem B1110725 : Blo 491791 1110725 := bbase (se 4 (by rfl) ⟨104130, by rfl⟩ : syracuseStep 1110725 = 208261) (by norm_num)
theorem B553693 : Blo 491791 553693 := bbase (se 3 (by rfl) ⟨103817, by rfl⟩ : syracuseStep 553693 = 207635) (by norm_num)
theorem B553729 : Blo 491791 553729 := bbase (se 2 (by rfl) ⟨207648, by rfl⟩ : syracuseStep 553729 = 415297) (by norm_num)
theorem B1110797 : Blo 491791 1110797 := bbase (se 3 (by rfl) ⟨208274, by rfl⟩ : syracuseStep 1110797 = 416549) (by norm_num)
theorem B553765 : Blo 491791 553765 := bbase (se 4 (by rfl) ⟨51915, by rfl⟩ : syracuseStep 553765 = 103831) (by norm_num)
theorem B553801 : Blo 491791 553801 := bbase (se 2 (by rfl) ⟨207675, by rfl⟩ : syracuseStep 553801 = 415351) (by norm_num)
theorem B1110869 : Blo 491791 1110869 := bbase (se 9 (by rfl) ⟨3254, by rfl⟩ : syracuseStep 1110869 = 6509) (by norm_num)
theorem B553837 : Blo 491791 553837 := bbase (se 3 (by rfl) ⟨103844, by rfl⟩ : syracuseStep 553837 = 207689) (by norm_num)
theorem B914309 : Blo 491791 914309 := bbase (se 4 (by rfl) ⟨85716, by rfl⟩ : syracuseStep 914309 = 171433) (by norm_num)
theorem B553873 : Blo 491791 553873 := bbase (se 2 (by rfl) ⟨207702, by rfl⟩ : syracuseStep 553873 = 415405) (by norm_num)
theorem B1110941 : Blo 491791 1110941 := bbase (se 3 (by rfl) ⟨208301, by rfl⟩ : syracuseStep 1110941 = 416603) (by norm_num)
theorem B1668005 : Blo 491791 1668005 := bbase (se 4 (by rfl) ⟨156375, by rfl⟩ : syracuseStep 1668005 = 312751) (by norm_num)
theorem B553909 : Blo 491791 553909 := bbase (se 5 (by rfl) ⟨25964, by rfl⟩ : syracuseStep 553909 = 51929) (by norm_num)
theorem B553945 : Blo 491791 553945 := bbase (se 2 (by rfl) ⟨207729, by rfl⟩ : syracuseStep 553945 = 415459) (by norm_num)
theorem B1111013 : Blo 491791 1111013 := bbase (se 4 (by rfl) ⟨104157, by rfl⟩ : syracuseStep 1111013 = 208315) (by norm_num)
theorem B553981 : Blo 491791 553981 := bbase (se 3 (by rfl) ⟨103871, by rfl⟩ : syracuseStep 553981 = 207743) (by norm_num)
theorem B1405957 : Blo 491791 1405957 := bbase (se 4 (by rfl) ⟨131808, by rfl⟩ : syracuseStep 1405957 = 263617) (by norm_num)
theorem B3568661 : Blo 491791 3568661 := bbase (se 6 (by rfl) ⟨83640, by rfl⟩ : syracuseStep 3568661 = 167281) (by norm_num)
theorem B554017 : Blo 491791 554017 := bbase (se 2 (by rfl) ⟨207756, by rfl⟩ : syracuseStep 554017 = 415513) (by norm_num)
theorem B1111085 : Blo 491791 1111085 := bbase (se 3 (by rfl) ⟨208328, by rfl⟩ : syracuseStep 1111085 = 416657) (by norm_num)
theorem B554053 : Blo 491791 554053 := bbase (se 4 (by rfl) ⟨51942, by rfl⟩ : syracuseStep 554053 = 103885) (by norm_num)
theorem B947285 : Blo 491791 947285 := bbase (se 8 (by rfl) ⟨5550, by rfl⟩ : syracuseStep 947285 = 11101) (by norm_num)
theorem B554089 : Blo 491791 554089 := bbase (se 2 (by rfl) ⟨207783, by rfl⟩ : syracuseStep 554089 = 415567) (by norm_num)
theorem B1111157 : Blo 491791 1111157 := bbase (se 5 (by rfl) ⟨52085, by rfl⟩ : syracuseStep 1111157 = 104171) (by norm_num)
theorem B554125 : Blo 491791 554125 := bbase (se 3 (by rfl) ⟨103898, by rfl⟩ : syracuseStep 554125 = 207797) (by norm_num)
theorem B554161 : Blo 491791 554161 := bbase (se 2 (by rfl) ⟨207810, by rfl⟩ : syracuseStep 554161 = 415621) (by norm_num)
theorem B1111229 : Blo 491791 1111229 := bbase (se 3 (by rfl) ⟨208355, by rfl⟩ : syracuseStep 1111229 = 416711) (by norm_num)
theorem B554197 : Blo 491791 554197 := bbase (se 7 (by rfl) ⟨6494, by rfl⟩ : syracuseStep 554197 = 12989) (by norm_num)
theorem B554233 : Blo 491791 554233 := bbase (se 2 (by rfl) ⟨207837, by rfl⟩ : syracuseStep 554233 = 415675) (by norm_num)
theorem B1111301 : Blo 491791 1111301 := bbase (se 4 (by rfl) ⟨104184, by rfl⟩ : syracuseStep 1111301 = 208369) (by norm_num)
theorem B554269 : Blo 491791 554269 := bbase (se 3 (by rfl) ⟨103925, by rfl⟩ : syracuseStep 554269 = 207851) (by norm_num)
theorem B554305 : Blo 491791 554305 := bbase (se 2 (by rfl) ⟨207864, by rfl⟩ : syracuseStep 554305 = 415729) (by norm_num)
theorem B1111373 : Blo 491791 1111373 := bbase (se 3 (by rfl) ⟨208382, by rfl⟩ : syracuseStep 1111373 = 416765) (by norm_num)
theorem B1668437 : Blo 491791 1668437 := bbase (se 13 (by rfl) ⟨305, by rfl⟩ : syracuseStep 1668437 = 611) (by norm_num)
theorem B750941 : Blo 491791 750941 := bbase (se 3 (by rfl) ⟨140801, by rfl⟩ : syracuseStep 750941 = 281603) (by norm_num)
theorem B554341 : Blo 491791 554341 := bbase (se 4 (by rfl) ⟨51969, by rfl⟩ : syracuseStep 554341 = 103939) (by norm_num)
theorem B554377 : Blo 491791 554377 := bbase (se 2 (by rfl) ⟨207891, by rfl⟩ : syracuseStep 554377 = 415783) (by norm_num)
theorem B1111445 : Blo 491791 1111445 := bbase (se 6 (by rfl) ⟨26049, by rfl⟩ : syracuseStep 1111445 = 52099) (by norm_num)
theorem B554413 : Blo 491791 554413 := bbase (se 3 (by rfl) ⟨103952, by rfl⟩ : syracuseStep 554413 = 207905) (by norm_num)
theorem B554449 : Blo 491791 554449 := bbase (se 2 (by rfl) ⟨207918, by rfl⟩ : syracuseStep 554449 = 415837) (by norm_num)
theorem B1111517 : Blo 491791 1111517 := bbase (se 3 (by rfl) ⟨208409, by rfl⟩ : syracuseStep 1111517 = 416819) (by norm_num)
theorem B554485 : Blo 491791 554485 := bbase (se 5 (by rfl) ⟨25991, by rfl⟩ : syracuseStep 554485 = 51983) (by norm_num)
theorem B554521 : Blo 491791 554521 := bbase (se 2 (by rfl) ⟨207945, by rfl⟩ : syracuseStep 554521 = 415891) (by norm_num)
theorem B1111589 : Blo 491791 1111589 := bbase (se 4 (by rfl) ⟨104211, by rfl⟩ : syracuseStep 1111589 = 208423) (by norm_num)
theorem B554557 : Blo 491791 554557 := bbase (se 3 (by rfl) ⟨103979, by rfl⟩ : syracuseStep 554557 = 207959) (by norm_num)
theorem B554593 : Blo 491791 554593 := bbase (se 2 (by rfl) ⟨207972, by rfl⟩ : syracuseStep 554593 = 415945) (by norm_num)
theorem B1111661 : Blo 491791 1111661 := bbase (se 3 (by rfl) ⟨208436, by rfl⟩ : syracuseStep 1111661 = 416873) (by norm_num)
theorem B554629 : Blo 491791 554629 := bbase (se 4 (by rfl) ⟨51996, by rfl⟩ : syracuseStep 554629 = 103993) (by norm_num)
theorem B554665 : Blo 491791 554665 := bbase (se 2 (by rfl) ⟨207999, by rfl⟩ : syracuseStep 554665 = 415999) (by norm_num)
theorem B1111733 : Blo 491791 1111733 := bbase (se 5 (by rfl) ⟨52112, by rfl⟩ : syracuseStep 1111733 = 104225) (by norm_num)
theorem B3176117 : Blo 491791 3176117 := bbase (se 5 (by rfl) ⟨148880, by rfl⟩ : syracuseStep 3176117 = 297761) (by norm_num)
theorem B554701 : Blo 491791 554701 := bbase (se 3 (by rfl) ⟨104006, by rfl⟩ : syracuseStep 554701 = 208013) (by norm_num)
theorem B554737 : Blo 491791 554737 := bbase (se 2 (by rfl) ⟨208026, by rfl⟩ : syracuseStep 554737 = 416053) (by norm_num)
theorem B1111805 : Blo 491791 1111805 := bbase (se 3 (by rfl) ⟨208463, by rfl⟩ : syracuseStep 1111805 = 416927) (by norm_num)
theorem B1668869 : Blo 491791 1668869 := bbase (se 4 (by rfl) ⟨156456, by rfl⟩ : syracuseStep 1668869 = 312913) (by norm_num)
theorem B554773 : Blo 491791 554773 := bbase (se 6 (by rfl) ⟨13002, by rfl⟩ : syracuseStep 554773 = 26005) (by norm_num)
theorem B554809 : Blo 491791 554809 := bbase (se 2 (by rfl) ⟨208053, by rfl⟩ : syracuseStep 554809 = 416107) (by norm_num)
theorem B1111877 : Blo 491791 1111877 := bbase (se 4 (by rfl) ⟨104238, by rfl⟩ : syracuseStep 1111877 = 208477) (by norm_num)
theorem B554845 : Blo 491791 554845 := bbase (se 3 (by rfl) ⟨104033, by rfl⟩ : syracuseStep 554845 = 208067) (by norm_num)
theorem B554881 : Blo 491791 554881 := bbase (se 2 (by rfl) ⟨208080, by rfl⟩ : syracuseStep 554881 = 416161) (by norm_num)
theorem B1111949 : Blo 491791 1111949 := bbase (se 3 (by rfl) ⟨208490, by rfl⟩ : syracuseStep 1111949 = 416981) (by norm_num)
theorem B948125 : Blo 491791 948125 := bbase (se 3 (by rfl) ⟨177773, by rfl⟩ : syracuseStep 948125 = 355547) (by norm_num)
theorem B554917 : Blo 491791 554917 := bbase (se 4 (by rfl) ⟨52023, by rfl⟩ : syracuseStep 554917 = 104047) (by norm_num)
theorem B554953 : Blo 491791 554953 := bbase (se 2 (by rfl) ⟨208107, by rfl⟩ : syracuseStep 554953 = 416215) (by norm_num)
theorem B1112021 : Blo 491791 1112021 := bbase (se 7 (by rfl) ⟨13031, by rfl⟩ : syracuseStep 1112021 = 26063) (by norm_num)
theorem B554989 : Blo 491791 554989 := bbase (se 3 (by rfl) ⟨104060, by rfl⟩ : syracuseStep 554989 = 208121) (by norm_num)
theorem B555025 : Blo 491791 555025 := bbase (se 2 (by rfl) ⟨208134, by rfl⟩ : syracuseStep 555025 = 416269) (by norm_num)
theorem B1112093 : Blo 491791 1112093 := bbase (se 3 (by rfl) ⟨208517, by rfl⟩ : syracuseStep 1112093 = 417035) (by norm_num)
theorem B555061 : Blo 491791 555061 := bbase (se 5 (by rfl) ⟨26018, by rfl⟩ : syracuseStep 555061 = 52037) (by norm_num)
theorem B1407061 : Blo 491791 1407061 := bbase (se 8 (by rfl) ⟨8244, by rfl⟩ : syracuseStep 1407061 = 16489) (by norm_num)
theorem B555097 : Blo 491791 555097 := bbase (se 2 (by rfl) ⟨208161, by rfl⟩ : syracuseStep 555097 = 416323) (by norm_num)
theorem B1112165 : Blo 491791 1112165 := bbase (se 4 (by rfl) ⟨104265, by rfl⟩ : syracuseStep 1112165 = 208531) (by norm_num)
theorem B555133 : Blo 491791 555133 := bbase (se 3 (by rfl) ⟨104087, by rfl⟩ : syracuseStep 555133 = 208175) (by norm_num)
theorem B555169 : Blo 491791 555169 := bbase (se 2 (by rfl) ⟨208188, by rfl⟩ : syracuseStep 555169 = 416377) (by norm_num)
theorem B1112237 : Blo 491791 1112237 := bbase (se 3 (by rfl) ⟨208544, by rfl⟩ : syracuseStep 1112237 = 417089) (by norm_num)
theorem B1669301 : Blo 491791 1669301 := bbase (se 5 (by rfl) ⟨78248, by rfl⟩ : syracuseStep 1669301 = 156497) (by norm_num)
theorem B555205 : Blo 491791 555205 := bbase (se 4 (by rfl) ⟨52050, by rfl⟩ : syracuseStep 555205 = 104101) (by norm_num)
theorem B555241 : Blo 491791 555241 := bbase (se 2 (by rfl) ⟨208215, by rfl⟩ : syracuseStep 555241 = 416431) (by norm_num)
theorem B1112309 : Blo 491791 1112309 := bbase (se 5 (by rfl) ⟨52139, by rfl⟩ : syracuseStep 1112309 = 104279) (by norm_num)
theorem B555277 : Blo 491791 555277 := bbase (se 3 (by rfl) ⟨104114, by rfl⟩ : syracuseStep 555277 = 208229) (by norm_num)
theorem B555313 : Blo 491791 555313 := bbase (se 2 (by rfl) ⟨208242, by rfl⟩ : syracuseStep 555313 = 416485) (by norm_num)
theorem B2816309 : Blo 491791 2816309 := bbase (se 5 (by rfl) ⟨132014, by rfl⟩ : syracuseStep 2816309 = 264029) (by norm_num)
theorem B1112381 : Blo 491791 1112381 := bbase (se 3 (by rfl) ⟨208571, by rfl⟩ : syracuseStep 1112381 = 417143) (by norm_num)
theorem B555349 : Blo 491791 555349 := bbase (se 10 (by rfl) ⟨813, by rfl⟩ : syracuseStep 555349 = 1627) (by norm_num)
theorem B555385 : Blo 491791 555385 := bbase (se 2 (by rfl) ⟨208269, by rfl⟩ : syracuseStep 555385 = 416539) (by norm_num)
theorem B1112453 : Blo 491791 1112453 := bbase (se 4 (by rfl) ⟨104292, by rfl⟩ : syracuseStep 1112453 = 208585) (by norm_num)
theorem B555421 : Blo 491791 555421 := bbase (se 3 (by rfl) ⟨104141, by rfl⟩ : syracuseStep 555421 = 208283) (by norm_num)
theorem B555457 : Blo 491791 555457 := bbase (se 2 (by rfl) ⟨208296, by rfl⟩ : syracuseStep 555457 = 416593) (by norm_num)
theorem B1112525 : Blo 491791 1112525 := bbase (se 3 (by rfl) ⟨208598, by rfl⟩ : syracuseStep 1112525 = 417197) (by norm_num)
theorem B555493 : Blo 491791 555493 := bbase (se 4 (by rfl) ⟨52077, by rfl⟩ : syracuseStep 555493 = 104155) (by norm_num)
theorem B555529 : Blo 491791 555529 := bbase (se 2 (by rfl) ⟨208323, by rfl⟩ : syracuseStep 555529 = 416647) (by norm_num)
theorem B1112597 : Blo 491791 1112597 := bbase (se 6 (by rfl) ⟨26076, by rfl⟩ : syracuseStep 1112597 = 52153) (by norm_num)
theorem B555565 : Blo 491791 555565 := bbase (se 3 (by rfl) ⟨104168, by rfl⟩ : syracuseStep 555565 = 208337) (by norm_num)
theorem B555601 : Blo 491791 555601 := bbase (se 2 (by rfl) ⟨208350, by rfl⟩ : syracuseStep 555601 = 416701) (by norm_num)
theorem B1112669 : Blo 491791 1112669 := bbase (se 3 (by rfl) ⟨208625, by rfl⟩ : syracuseStep 1112669 = 417251) (by norm_num)
theorem B1669733 : Blo 491791 1669733 := bbase (se 4 (by rfl) ⟨156537, by rfl⟩ : syracuseStep 1669733 = 313075) (by norm_num)
theorem B555637 : Blo 491791 555637 := bbase (se 5 (by rfl) ⟨26045, by rfl⟩ : syracuseStep 555637 = 52091) (by norm_num)
theorem B555673 : Blo 491791 555673 := bbase (se 2 (by rfl) ⟨208377, by rfl⟩ : syracuseStep 555673 = 416755) (by norm_num)
theorem B1112741 : Blo 491791 1112741 := bbase (se 4 (by rfl) ⟨104319, by rfl⟩ : syracuseStep 1112741 = 208639) (by norm_num)
theorem B555709 : Blo 491791 555709 := bbase (se 3 (by rfl) ⟨104195, by rfl⟩ : syracuseStep 555709 = 208391) (by norm_num)
theorem B555745 : Blo 491791 555745 := bbase (se 2 (by rfl) ⟨208404, by rfl⟩ : syracuseStep 555745 = 416809) (by norm_num)
theorem B1112813 : Blo 491791 1112813 := bbase (se 3 (by rfl) ⟨208652, by rfl⟩ : syracuseStep 1112813 = 417305) (by norm_num)
theorem B555781 : Blo 491791 555781 := bbase (se 4 (by rfl) ⟨52104, by rfl⟩ : syracuseStep 555781 = 104209) (by norm_num)
theorem B555817 : Blo 491791 555817 := bbase (se 2 (by rfl) ⟨208431, by rfl⟩ : syracuseStep 555817 = 416863) (by norm_num)
theorem B1112885 : Blo 491791 1112885 := bbase (se 5 (by rfl) ⟨52166, by rfl⟩ : syracuseStep 1112885 = 104333) (by norm_num)
theorem B555853 : Blo 491791 555853 := bbase (se 3 (by rfl) ⟨104222, by rfl⟩ : syracuseStep 555853 = 208445) (by norm_num)
theorem B1604437 : Blo 491791 1604437 := bbase (se 9 (by rfl) ⟨4700, by rfl⟩ : syracuseStep 1604437 = 9401) (by norm_num)
theorem B555889 : Blo 491791 555889 := bbase (se 2 (by rfl) ⟨208458, by rfl⟩ : syracuseStep 555889 = 416917) (by norm_num)
theorem B1112957 : Blo 491791 1112957 := bbase (se 3 (by rfl) ⟨208679, by rfl⟩ : syracuseStep 1112957 = 417359) (by norm_num)
theorem B1440661 : Blo 491791 1440661 := bbase (se 6 (by rfl) ⟨33765, by rfl⟩ : syracuseStep 1440661 = 67531) (by norm_num)
theorem B555925 : Blo 491791 555925 := bbase (se 6 (by rfl) ⟨13029, by rfl⟩ : syracuseStep 555925 = 26059) (by norm_num)
theorem B555961 : Blo 491791 555961 := bbase (se 2 (by rfl) ⟨208485, by rfl⟩ : syracuseStep 555961 = 416971) (by norm_num)
theorem B1113029 : Blo 491791 1113029 := bbase (se 4 (by rfl) ⟨104346, by rfl⟩ : syracuseStep 1113029 = 208693) (by norm_num)
theorem B555997 : Blo 491791 555997 := bbase (se 3 (by rfl) ⟨104249, by rfl⟩ : syracuseStep 555997 = 208499) (by norm_num)
theorem B556033 : Blo 491791 556033 := bbase (se 2 (by rfl) ⟨208512, by rfl⟩ : syracuseStep 556033 = 417025) (by norm_num)
theorem B687109 : Blo 491791 687109 := bbase (se 4 (by rfl) ⟨64416, by rfl⟩ : syracuseStep 687109 = 128833) (by norm_num)
theorem B1113101 : Blo 491791 1113101 := bbase (se 3 (by rfl) ⟨208706, by rfl⟩ : syracuseStep 1113101 = 417413) (by norm_num)
theorem B1670165 : Blo 491791 1670165 := bbase (se 6 (by rfl) ⟨39144, by rfl⟩ : syracuseStep 1670165 = 78289) (by norm_num)
theorem B556069 : Blo 491791 556069 := bbase (se 4 (by rfl) ⟨52131, by rfl⟩ : syracuseStep 556069 = 104263) (by norm_num)
theorem B556105 : Blo 491791 556105 := bbase (se 2 (by rfl) ⟨208539, by rfl⟩ : syracuseStep 556105 = 417079) (by norm_num)
theorem B1113173 : Blo 491791 1113173 := bbase (se 8 (by rfl) ⟨6522, by rfl⟩ : syracuseStep 1113173 = 13045) (by norm_num)
theorem B556141 : Blo 491791 556141 := bbase (se 3 (by rfl) ⟨104276, by rfl⟩ : syracuseStep 556141 = 208553) (by norm_num)
theorem B556177 : Blo 491791 556177 := bbase (se 2 (by rfl) ⟨208566, by rfl⟩ : syracuseStep 556177 = 417133) (by norm_num)
theorem B752789 : Blo 491791 752789 := bbase (se 6 (by rfl) ⟨17643, by rfl⟩ : syracuseStep 752789 = 35287) (by norm_num)
theorem B1113245 : Blo 491791 1113245 := bbase (se 3 (by rfl) ⟨208733, by rfl⟩ : syracuseStep 1113245 = 417467) (by norm_num)
theorem B556213 : Blo 491791 556213 := bbase (se 5 (by rfl) ⟨26072, by rfl⟩ : syracuseStep 556213 = 52145) (by norm_num)
theorem B556249 : Blo 491791 556249 := bbase (se 2 (by rfl) ⟨208593, by rfl⟩ : syracuseStep 556249 = 417187) (by norm_num)
theorem B1113317 : Blo 491791 1113317 := bbase (se 4 (by rfl) ⟨104373, by rfl⟩ : syracuseStep 1113317 = 208747) (by norm_num)
theorem B556285 : Blo 491791 556285 := bbase (se 3 (by rfl) ⟨104303, by rfl⟩ : syracuseStep 556285 = 208607) (by norm_num)
theorem B556321 : Blo 491791 556321 := bbase (se 2 (by rfl) ⟨208620, by rfl⟩ : syracuseStep 556321 = 417241) (by norm_num)
theorem B1113389 : Blo 491791 1113389 := bbase (se 3 (by rfl) ⟨208760, by rfl⟩ : syracuseStep 1113389 = 417521) (by norm_num)
theorem B556357 : Blo 491791 556357 := bbase (se 4 (by rfl) ⟨52158, by rfl⟩ : syracuseStep 556357 = 104317) (by norm_num)
theorem B556393 : Blo 491791 556393 := bbase (se 2 (by rfl) ⟨208647, by rfl⟩ : syracuseStep 556393 = 417295) (by norm_num)
theorem B1113461 : Blo 491791 1113461 := bbase (se 5 (by rfl) ⟨52193, by rfl⟩ : syracuseStep 1113461 = 104387) (by norm_num)
theorem B556429 : Blo 491791 556429 := bbase (se 3 (by rfl) ⟨104330, by rfl⟩ : syracuseStep 556429 = 208661) (by norm_num)
theorem B556465 : Blo 491791 556465 := bbase (se 2 (by rfl) ⟨208674, by rfl⟩ : syracuseStep 556465 = 417349) (by norm_num)
theorem B1113533 : Blo 491791 1113533 := bbase (se 3 (by rfl) ⟨208787, by rfl⟩ : syracuseStep 1113533 = 417575) (by norm_num)
theorem B1670597 : Blo 491791 1670597 := bbase (se 4 (by rfl) ⟨156618, by rfl⟩ : syracuseStep 1670597 = 313237) (by norm_num)
theorem B556501 : Blo 491791 556501 := bbase (se 7 (by rfl) ⟨6521, by rfl⟩ : syracuseStep 556501 = 13043) (by norm_num)
theorem B556537 : Blo 491791 556537 := bbase (se 2 (by rfl) ⟨208701, by rfl⟩ : syracuseStep 556537 = 417403) (by norm_num)
theorem B1113605 : Blo 491791 1113605 := bbase (se 4 (by rfl) ⟨104400, by rfl⟩ : syracuseStep 1113605 = 208801) (by norm_num)
theorem B556573 : Blo 491791 556573 := bbase (se 3 (by rfl) ⟨104357, by rfl⟩ : syracuseStep 556573 = 208715) (by norm_num)
theorem B1408565 : Blo 491791 1408565 := bbase (se 5 (by rfl) ⟨66026, by rfl⟩ : syracuseStep 1408565 = 132053) (by norm_num)
theorem B556609 : Blo 491791 556609 := bbase (se 2 (by rfl) ⟨208728, by rfl⟩ : syracuseStep 556609 = 417457) (by norm_num)
theorem B1867333 : Blo 491791 1867333 := bbase (se 4 (by rfl) ⟨175062, by rfl⟩ : syracuseStep 1867333 = 350125) (by norm_num)
theorem B1113677 : Blo 491791 1113677 := bbase (se 3 (by rfl) ⟨208814, by rfl⟩ : syracuseStep 1113677 = 417629) (by norm_num)
theorem B556645 : Blo 491791 556645 := bbase (se 4 (by rfl) ⟨52185, by rfl⟩ : syracuseStep 556645 = 104371) (by norm_num)
theorem B556681 : Blo 491791 556681 := bbase (se 2 (by rfl) ⟨208755, by rfl⟩ : syracuseStep 556681 = 417511) (by norm_num)
theorem B1113749 : Blo 491791 1113749 := bbase (se 6 (by rfl) ⟨26103, by rfl⟩ : syracuseStep 1113749 = 52207) (by norm_num)
theorem B556717 : Blo 491791 556717 := bbase (se 3 (by rfl) ⟨104384, by rfl⟩ : syracuseStep 556717 = 208769) (by norm_num)
theorem B556753 : Blo 491791 556753 := bbase (se 2 (by rfl) ⟨208782, by rfl⟩ : syracuseStep 556753 = 417565) (by norm_num)
theorem B1113821 : Blo 491791 1113821 := bbase (se 3 (by rfl) ⟨208841, by rfl⟩ : syracuseStep 1113821 = 417683) (by norm_num)
theorem B1244909 : Blo 491791 1244909 := bbase (se 3 (by rfl) ⟨233420, by rfl⟩ : syracuseStep 1244909 = 466841) (by norm_num)
theorem B2490101 : Blo 491791 2490101 := bbase (se 5 (by rfl) ⟨116723, by rfl⟩ : syracuseStep 2490101 = 233447) (by norm_num)
theorem B556789 : Blo 491791 556789 := bbase (se 5 (by rfl) ⟨26099, by rfl⟩ : syracuseStep 556789 = 52199) (by norm_num)
theorem B5603093 : Blo 491791 5603093 := bbase (se 6 (by rfl) ⟨131322, by rfl⟩ : syracuseStep 5603093 = 262645) (by norm_num)
theorem B556825 : Blo 491791 556825 := bbase (se 2 (by rfl) ⟨208809, by rfl⟩ : syracuseStep 556825 = 417619) (by norm_num)
theorem B1113893 : Blo 491791 1113893 := bbase (se 4 (by rfl) ⟨104427, by rfl⟩ : syracuseStep 1113893 = 208855) (by norm_num)
theorem B556861 : Blo 491791 556861 := bbase (se 3 (by rfl) ⟨104411, by rfl⟩ : syracuseStep 556861 = 208823) (by norm_num)
theorem B556897 : Blo 491791 556897 := bbase (se 2 (by rfl) ⟨208836, by rfl⟩ : syracuseStep 556897 = 417673) (by norm_num)
theorem B1113965 : Blo 491791 1113965 := bbase (se 3 (by rfl) ⟨208868, by rfl⟩ : syracuseStep 1113965 = 417737) (by norm_num)
theorem B1867637 : Blo 491791 1867637 := bbase (se 5 (by rfl) ⟨87545, by rfl⟩ : syracuseStep 1867637 = 175091) (by norm_num)
theorem B1671029 : Blo 491791 1671029 := bbase (se 5 (by rfl) ⟨78329, by rfl⟩ : syracuseStep 1671029 = 156659) (by norm_num)
theorem B556933 : Blo 491791 556933 := bbase (se 4 (by rfl) ⟨52212, by rfl⟩ : syracuseStep 556933 = 104425) (by norm_num)
theorem B622505 : Blo 491791 622505 := bbase (se 2 (by rfl) ⟨233439, by rfl⟩ : syracuseStep 622505 = 466879) (by norm_num)
theorem B556969 : Blo 491791 556969 := bbase (se 2 (by rfl) ⟨208863, by rfl⟩ : syracuseStep 556969 = 417727) (by norm_num)
theorem B1114037 : Blo 491791 1114037 := bbase (se 5 (by rfl) ⟨52220, by rfl⟩ : syracuseStep 1114037 = 104441) (by norm_num)
theorem B557005 : Blo 491791 557005 := bbase (se 3 (by rfl) ⟨104438, by rfl⟩ : syracuseStep 557005 = 208877) (by norm_num)
theorem B622561 : Blo 491791 622561 := bbase (se 2 (by rfl) ⟨233460, by rfl⟩ : syracuseStep 622561 = 466921) (by norm_num)
theorem B917477 : Blo 491791 917477 := bbase (se 4 (by rfl) ⟨86013, by rfl⟩ : syracuseStep 917477 = 172027) (by norm_num)
theorem B557041 : Blo 491791 557041 := bbase (se 2 (by rfl) ⟨208890, by rfl⟩ : syracuseStep 557041 = 417781) (by norm_num)
theorem B557059 : Blo 491791 557059 := bstep (se 1 (by rfl) ⟨417794, by rfl⟩ : syracuseStep 557059 = 835589) B835589
theorem B1245233 : Blo 491791 1245233 := bstep (se 2 (by rfl) ⟨466962, by rfl⟩ : syracuseStep 1245233 = 933925) B933925
theorem B1671245 : Blo 491791 1671245 := bstep (se 3 (by rfl) ⟨313358, by rfl⟩ : syracuseStep 1671245 = 626717) B626717
theorem B622723 : Blo 491791 622723 := bstep (se 1 (by rfl) ⟨467042, by rfl⟩ : syracuseStep 622723 = 934085) B934085
theorem B1671299 : Blo 491791 1671299 := bstep (se 1 (by rfl) ⟨1253474, by rfl⟩ : syracuseStep 1671299 = 2506949) B2506949
theorem B557203 : Blo 491791 557203 := bstep (se 1 (by rfl) ⟨417902, by rfl⟩ : syracuseStep 557203 = 835805) B835805
theorem B1114289 : Blo 491791 1114289 := bstep (se 2 (by rfl) ⟨417858, by rfl⟩ : syracuseStep 1114289 = 835717) B835717
theorem B1114307 : Blo 491791 1114307 := bstep (se 1 (by rfl) ⟨835730, by rfl⟩ : syracuseStep 1114307 = 1671461) B1671461
theorem B622819 : Blo 491791 622819 := bstep (se 1 (by rfl) ⟨467114, by rfl⟩ : syracuseStep 622819 = 934229) B934229
theorem B491795 : Blo 491791 491795 := bstep (se 1 (by rfl) ⟨368846, by rfl⟩ : syracuseStep 491795 = 737693) B737693
theorem B491811 : Blo 491791 491811 := bstep (se 1 (by rfl) ⟨368858, by rfl⟩ : syracuseStep 491811 = 737717) B737717
theorem B557347 : Blo 491791 557347 := bstep (se 1 (by rfl) ⟨418010, by rfl⟩ : syracuseStep 557347 = 836021) B836021
theorem B491827 : Blo 491791 491827 := bstep (se 1 (by rfl) ⟨368870, by rfl⟩ : syracuseStep 491827 = 737741) B737741
theorem B491843 : Blo 491791 491843 := bstep (se 1 (by rfl) ⟨368882, by rfl⟩ : syracuseStep 491843 = 737765) B737765
theorem B491859 : Blo 491791 491859 := bstep (se 1 (by rfl) ⟨368894, by rfl⟩ : syracuseStep 491859 = 737789) B737789
theorem B491875 : Blo 491791 491875 := bstep (se 1 (by rfl) ⟨368906, by rfl⟩ : syracuseStep 491875 = 737813) B737813
theorem B491891 : Blo 491791 491891 := bstep (se 1 (by rfl) ⟨368918, by rfl⟩ : syracuseStep 491891 = 737837) B737837
theorem B491907 : Blo 491791 491907 := bstep (se 1 (by rfl) ⟨368930, by rfl⟩ : syracuseStep 491907 = 737861) B737861
theorem B1671569 : Blo 491791 1671569 := bstep (se 2 (by rfl) ⟨626838, by rfl⟩ : syracuseStep 1671569 = 1253677) B1253677
theorem B491923 : Blo 491791 491923 := bstep (se 1 (by rfl) ⟨368942, by rfl⟩ : syracuseStep 491923 = 737885) B737885
theorem B491939 : Blo 491791 491939 := bstep (se 1 (by rfl) ⟨368954, by rfl⟩ : syracuseStep 491939 = 737909) B737909
theorem B491955 : Blo 491791 491955 := bstep (se 1 (by rfl) ⟨368966, by rfl⟩ : syracuseStep 491955 = 737933) B737933
theorem B557491 : Blo 491791 557491 := bstep (se 1 (by rfl) ⟨418118, by rfl⟩ : syracuseStep 557491 = 836237) B836237
theorem B491971 : Blo 491791 491971 := bstep (se 1 (by rfl) ⟨368978, by rfl⟩ : syracuseStep 491971 = 737957) B737957
theorem B1114577 : Blo 491791 1114577 := bstep (se 2 (by rfl) ⟨417966, by rfl⟩ : syracuseStep 1114577 = 835933) B835933
theorem B491987 : Blo 491791 491987 := bstep (se 1 (by rfl) ⟨368990, by rfl⟩ : syracuseStep 491987 = 737981) B737981
theorem B492003 : Blo 491791 492003 := bstep (se 1 (by rfl) ⟨369002, by rfl⟩ : syracuseStep 492003 = 738005) B738005
theorem B1114595 : Blo 491791 1114595 := bstep (se 1 (by rfl) ⟨835946, by rfl⟩ : syracuseStep 1114595 = 1671893) B1671893
theorem B492019 : Blo 491791 492019 := bstep (se 1 (by rfl) ⟨369014, by rfl⟩ : syracuseStep 492019 = 738029) B738029
theorem B492035 : Blo 491791 492035 := bstep (se 1 (by rfl) ⟨369026, by rfl⟩ : syracuseStep 492035 = 738053) B738053
theorem B492051 : Blo 491791 492051 := bstep (se 1 (by rfl) ⟨369038, by rfl⟩ : syracuseStep 492051 = 738077) B738077
theorem B492067 : Blo 491791 492067 := bstep (se 1 (by rfl) ⟨369050, by rfl⟩ : syracuseStep 492067 = 738101) B738101
theorem B492083 : Blo 491791 492083 := bstep (se 1 (by rfl) ⟨369062, by rfl⟩ : syracuseStep 492083 = 738125) B738125
theorem B492099 : Blo 491791 492099 := bstep (se 1 (by rfl) ⟨369074, by rfl⟩ : syracuseStep 492099 = 738149) B738149
theorem B557635 : Blo 491791 557635 := bstep (se 1 (by rfl) ⟨418226, by rfl⟩ : syracuseStep 557635 = 836453) B836453
theorem B492115 : Blo 491791 492115 := bstep (se 1 (by rfl) ⟨369086, by rfl⟩ : syracuseStep 492115 = 738173) B738173
theorem B492131 : Blo 491791 492131 := bstep (se 1 (by rfl) ⟨369098, by rfl⟩ : syracuseStep 492131 = 738197) B738197
theorem B492147 : Blo 491791 492147 := bstep (se 1 (by rfl) ⟨369110, by rfl⟩ : syracuseStep 492147 = 738221) B738221
theorem B492163 : Blo 491791 492163 := bstep (se 1 (by rfl) ⟨369122, by rfl⟩ : syracuseStep 492163 = 738245) B738245
theorem B492179 : Blo 491791 492179 := bstep (se 1 (by rfl) ⟨369134, by rfl⟩ : syracuseStep 492179 = 738269) B738269
theorem B492195 : Blo 491791 492195 := bstep (se 1 (by rfl) ⟨369146, by rfl⟩ : syracuseStep 492195 = 738293) B738293
theorem B492211 : Blo 491791 492211 := bstep (se 1 (by rfl) ⟨369158, by rfl⟩ : syracuseStep 492211 = 738317) B738317
theorem B492227 : Blo 491791 492227 := bstep (se 1 (by rfl) ⟨369170, by rfl⟩ : syracuseStep 492227 = 738341) B738341
theorem B492243 : Blo 491791 492243 := bstep (se 1 (by rfl) ⟨369182, by rfl⟩ : syracuseStep 492243 = 738365) B738365
theorem B623315 : Blo 491791 623315 := bstep (se 1 (by rfl) ⟨467486, by rfl⟩ : syracuseStep 623315 = 934973) B934973
theorem B492259 : Blo 491791 492259 := bstep (se 1 (by rfl) ⟨369194, by rfl⟩ : syracuseStep 492259 = 738389) B738389
theorem B1114865 : Blo 491791 1114865 := bstep (se 2 (by rfl) ⟨418074, by rfl⟩ : syracuseStep 1114865 = 836149) B836149
theorem B492275 : Blo 491791 492275 := bstep (se 1 (by rfl) ⟨369206, by rfl⟩ : syracuseStep 492275 = 738413) B738413
theorem B492291 : Blo 491791 492291 := bstep (se 1 (by rfl) ⟨369218, by rfl⟩ : syracuseStep 492291 = 738437) B738437
theorem B1409795 : Blo 491791 1409795 := bstep (se 1 (by rfl) ⟨1057346, by rfl⟩ : syracuseStep 1409795 = 2114693) B2114693
theorem B1114883 : Blo 491791 1114883 := bstep (se 1 (by rfl) ⟨836162, by rfl⟩ : syracuseStep 1114883 = 1672325) B1672325
theorem B492307 : Blo 491791 492307 := bstep (se 1 (by rfl) ⟨369230, by rfl⟩ : syracuseStep 492307 = 738461) B738461
theorem B1868579 : Blo 491791 1868579 := bstep (se 1 (by rfl) ⟨1401434, by rfl⟩ : syracuseStep 1868579 = 2802869) B2802869
theorem B492323 : Blo 491791 492323 := bstep (se 1 (by rfl) ⟨369242, by rfl⟩ : syracuseStep 492323 = 738485) B738485
theorem B1999651 : Blo 491791 1999651 := bstep (se 1 (by rfl) ⟨1499738, by rfl⟩ : syracuseStep 1999651 = 2999477) B2999477
theorem B492339 : Blo 491791 492339 := bstep (se 1 (by rfl) ⟨369254, by rfl⟩ : syracuseStep 492339 = 738509) B738509
theorem B492355 : Blo 491791 492355 := bstep (se 1 (by rfl) ⟨369266, by rfl⟩ : syracuseStep 492355 = 738533) B738533
theorem B492371 : Blo 491791 492371 := bstep (se 1 (by rfl) ⟨369278, by rfl⟩ : syracuseStep 492371 = 738557) B738557
theorem B2491235 : Blo 491791 2491235 := bstep (se 1 (by rfl) ⟨1868426, by rfl⟩ : syracuseStep 2491235 = 3736853) B3736853
theorem B492387 : Blo 491791 492387 := bstep (se 1 (by rfl) ⟨369290, by rfl⟩ : syracuseStep 492387 = 738581) B738581
theorem B492403 : Blo 491791 492403 := bstep (se 1 (by rfl) ⟨369302, by rfl⟩ : syracuseStep 492403 = 738605) B738605
theorem B492419 : Blo 491791 492419 := bstep (se 1 (by rfl) ⟨369314, by rfl⟩ : syracuseStep 492419 = 738629) B738629
theorem B492435 : Blo 491791 492435 := bstep (se 1 (by rfl) ⟨369326, by rfl⟩ : syracuseStep 492435 = 738653) B738653
theorem B492451 : Blo 491791 492451 := bstep (se 1 (by rfl) ⟨369338, by rfl⟩ : syracuseStep 492451 = 738677) B738677
theorem B1672109 : Blo 491791 1672109 := bstep (se 3 (by rfl) ⟨313520, by rfl⟩ : syracuseStep 1672109 = 627041) B627041
theorem B492467 : Blo 491791 492467 := bstep (se 1 (by rfl) ⟨369350, by rfl⟩ : syracuseStep 492467 = 738701) B738701
theorem B492483 : Blo 491791 492483 := bstep (se 1 (by rfl) ⟨369362, by rfl⟩ : syracuseStep 492483 = 738725) B738725
theorem B492499 : Blo 491791 492499 := bstep (se 1 (by rfl) ⟨369374, by rfl⟩ : syracuseStep 492499 = 738749) B738749
theorem B492515 : Blo 491791 492515 := bstep (se 1 (by rfl) ⟨369386, by rfl⟩ : syracuseStep 492515 = 738773) B738773
theorem B1672163 : Blo 491791 1672163 := bstep (se 1 (by rfl) ⟨1254122, by rfl⟩ : syracuseStep 1672163 = 2508245) B2508245
theorem B492531 : Blo 491791 492531 := bstep (se 1 (by rfl) ⟨369398, by rfl⟩ : syracuseStep 492531 = 738797) B738797
theorem B492547 : Blo 491791 492547 := bstep (se 1 (by rfl) ⟨369410, by rfl⟩ : syracuseStep 492547 = 738821) B738821
theorem B1246225 : Blo 491791 1246225 := bstep (se 2 (by rfl) ⟨467334, by rfl⟩ : syracuseStep 1246225 = 934669) B934669
theorem B1115153 : Blo 491791 1115153 := bstep (se 2 (by rfl) ⟨418182, by rfl⟩ : syracuseStep 1115153 = 836365) B836365
theorem B492563 : Blo 491791 492563 := bstep (se 1 (by rfl) ⟨369422, by rfl⟩ : syracuseStep 492563 = 738845) B738845
theorem B492579 : Blo 491791 492579 := bstep (se 1 (by rfl) ⟨369434, by rfl⟩ : syracuseStep 492579 = 738869) B738869
theorem B1115171 : Blo 491791 1115171 := bstep (se 1 (by rfl) ⟨836378, by rfl⟩ : syracuseStep 1115171 = 1672757) B1672757
theorem B492595 : Blo 491791 492595 := bstep (se 1 (by rfl) ⟨369446, by rfl⟩ : syracuseStep 492595 = 738893) B738893
theorem B492611 : Blo 491791 492611 := bstep (se 1 (by rfl) ⟨369458, by rfl⟩ : syracuseStep 492611 = 738917) B738917
theorem B492627 : Blo 491791 492627 := bstep (se 1 (by rfl) ⟨369470, by rfl⟩ : syracuseStep 492627 = 738941) B738941
theorem B492643 : Blo 491791 492643 := bstep (se 1 (by rfl) ⟨369482, by rfl⟩ : syracuseStep 492643 = 738965) B738965
theorem B492659 : Blo 491791 492659 := bstep (se 1 (by rfl) ⟨369494, by rfl⟩ : syracuseStep 492659 = 738989) B738989
theorem B492675 : Blo 491791 492675 := bstep (se 1 (by rfl) ⟨369506, by rfl⟩ : syracuseStep 492675 = 739013) B739013
theorem B492691 : Blo 491791 492691 := bstep (se 1 (by rfl) ⟨369518, by rfl⟩ : syracuseStep 492691 = 739037) B739037
theorem B492707 : Blo 491791 492707 := bstep (se 1 (by rfl) ⟨369530, by rfl⟩ : syracuseStep 492707 = 739061) B739061
theorem B492723 : Blo 491791 492723 := bstep (se 1 (by rfl) ⟨369542, by rfl⟩ : syracuseStep 492723 = 739085) B739085
theorem B492739 : Blo 491791 492739 := bstep (se 1 (by rfl) ⟨369554, by rfl⟩ : syracuseStep 492739 = 739109) B739109
theorem B492755 : Blo 491791 492755 := bstep (se 1 (by rfl) ⟨369566, by rfl⟩ : syracuseStep 492755 = 739133) B739133
theorem B492771 : Blo 491791 492771 := bstep (se 1 (by rfl) ⟨369578, by rfl⟩ : syracuseStep 492771 = 739157) B739157
theorem B1803505 : Blo 491791 1803505 := bstep (se 2 (by rfl) ⟨676314, by rfl⟩ : syracuseStep 1803505 = 1352629) B1352629
theorem B492787 : Blo 491791 492787 := bstep (se 1 (by rfl) ⟨369590, by rfl⟩ : syracuseStep 492787 = 739181) B739181
theorem B1672433 : Blo 491791 1672433 := bstep (se 2 (by rfl) ⟨627162, by rfl⟩ : syracuseStep 1672433 = 1254325) B1254325
theorem B492803 : Blo 491791 492803 := bstep (se 1 (by rfl) ⟨369602, by rfl⟩ : syracuseStep 492803 = 739205) B739205
theorem B492819 : Blo 491791 492819 := bstep (se 1 (by rfl) ⟨369614, by rfl⟩ : syracuseStep 492819 = 739229) B739229
theorem B1246499 : Blo 491791 1246499 := bstep (se 1 (by rfl) ⟨934874, by rfl⟩ : syracuseStep 1246499 = 1869749) B1869749
theorem B492835 : Blo 491791 492835 := bstep (se 1 (by rfl) ⟨369626, by rfl⟩ : syracuseStep 492835 = 739253) B739253
theorem B1115441 : Blo 491791 1115441 := bstep (se 2 (by rfl) ⟨418290, by rfl⟩ : syracuseStep 1115441 = 836581) B836581
theorem B492851 : Blo 491791 492851 := bstep (se 1 (by rfl) ⟨369638, by rfl⟩ : syracuseStep 492851 = 739277) B739277
theorem B492867 : Blo 491791 492867 := bstep (se 1 (by rfl) ⟨369650, by rfl⟩ : syracuseStep 492867 = 739301) B739301
theorem B1115459 : Blo 491791 1115459 := bstep (se 1 (by rfl) ⟨836594, by rfl⟩ : syracuseStep 1115459 = 1673189) B1673189
theorem B492883 : Blo 491791 492883 := bstep (se 1 (by rfl) ⟨369662, by rfl⟩ : syracuseStep 492883 = 739325) B739325
theorem B492899 : Blo 491791 492899 := bstep (se 1 (by rfl) ⟨369674, by rfl⟩ : syracuseStep 492899 = 739349) B739349
theorem B492915 : Blo 491791 492915 := bstep (se 1 (by rfl) ⟨369686, by rfl⟩ : syracuseStep 492915 = 739373) B739373
theorem B492931 : Blo 491791 492931 := bstep (se 1 (by rfl) ⟨369698, by rfl⟩ : syracuseStep 492931 = 739397) B739397
theorem B492947 : Blo 491791 492947 := bstep (se 1 (by rfl) ⟨369710, by rfl⟩ : syracuseStep 492947 = 739421) B739421
theorem B624019 : Blo 491791 624019 := bstep (se 1 (by rfl) ⟨468014, by rfl⟩ : syracuseStep 624019 = 936029) B936029
theorem B492963 : Blo 491791 492963 := bstep (se 1 (by rfl) ⟨369722, by rfl⟩ : syracuseStep 492963 = 739445) B739445
theorem B492979 : Blo 491791 492979 := bstep (se 1 (by rfl) ⟨369734, by rfl⟩ : syracuseStep 492979 = 739469) B739469
theorem B492995 : Blo 491791 492995 := bstep (se 1 (by rfl) ⟨369746, by rfl⟩ : syracuseStep 492995 = 739493) B739493
theorem B493011 : Blo 491791 493011 := bstep (se 1 (by rfl) ⟨369758, by rfl⟩ : syracuseStep 493011 = 739517) B739517
theorem B1246691 : Blo 491791 1246691 := bstep (se 1 (by rfl) ⟨935018, by rfl⟩ : syracuseStep 1246691 = 1870037) B1870037
theorem B493027 : Blo 491791 493027 := bstep (se 1 (by rfl) ⟨369770, by rfl⟩ : syracuseStep 493027 = 739541) B739541
theorem B493043 : Blo 491791 493043 := bstep (se 1 (by rfl) ⟨369782, by rfl⟩ : syracuseStep 493043 = 739565) B739565
theorem B624115 : Blo 491791 624115 := bstep (se 1 (by rfl) ⟨468086, by rfl⟩ : syracuseStep 624115 = 936173) B936173
theorem B493059 : Blo 491791 493059 := bstep (se 1 (by rfl) ⟨369794, by rfl⟩ : syracuseStep 493059 = 739589) B739589
theorem B493075 : Blo 491791 493075 := bstep (se 1 (by rfl) ⟨369806, by rfl⟩ : syracuseStep 493075 = 739613) B739613
theorem B493091 : Blo 491791 493091 := bstep (se 1 (by rfl) ⟨369818, by rfl⟩ : syracuseStep 493091 = 739637) B739637
theorem B1410605 : Blo 491791 1410605 := bstep (se 3 (by rfl) ⟨264488, by rfl⟩ : syracuseStep 1410605 = 528977) B528977
theorem B493107 : Blo 491791 493107 := bstep (se 1 (by rfl) ⟨369830, by rfl⟩ : syracuseStep 493107 = 739661) B739661
theorem B493123 : Blo 491791 493123 := bstep (se 1 (by rfl) ⟨369842, by rfl⟩ : syracuseStep 493123 = 739685) B739685
theorem B493139 : Blo 491791 493139 := bstep (se 1 (by rfl) ⟨369854, by rfl⟩ : syracuseStep 493139 = 739709) B739709
theorem B493155 : Blo 491791 493155 := bstep (se 1 (by rfl) ⟨369866, by rfl⟩ : syracuseStep 493155 = 739733) B739733
theorem B886385 : Blo 491791 886385 := bstep (se 2 (by rfl) ⟨332394, by rfl⟩ : syracuseStep 886385 = 664789) B664789
theorem B493171 : Blo 491791 493171 := bstep (se 1 (by rfl) ⟨369878, by rfl⟩ : syracuseStep 493171 = 739757) B739757
theorem B493187 : Blo 491791 493187 := bstep (se 1 (by rfl) ⟨369890, by rfl⟩ : syracuseStep 493187 = 739781) B739781
theorem B2492045 : Blo 491791 2492045 := bstep (se 3 (by rfl) ⟨467258, by rfl⟩ : syracuseStep 2492045 = 934517) B934517
theorem B493203 : Blo 491791 493203 := bstep (se 1 (by rfl) ⟨369902, by rfl⟩ : syracuseStep 493203 = 739805) B739805
theorem B493219 : Blo 491791 493219 := bstep (se 1 (by rfl) ⟨369914, by rfl⟩ : syracuseStep 493219 = 739829) B739829
theorem B493235 : Blo 491791 493235 := bstep (se 1 (by rfl) ⟨369926, by rfl⟩ : syracuseStep 493235 = 739853) B739853
theorem B493251 : Blo 491791 493251 := bstep (se 1 (by rfl) ⟨369938, by rfl⟩ : syracuseStep 493251 = 739877) B739877
theorem B493267 : Blo 491791 493267 := bstep (se 1 (by rfl) ⟨369950, by rfl⟩ : syracuseStep 493267 = 739901) B739901
theorem B526051 : Blo 491791 526051 := bstep (se 1 (by rfl) ⟨394538, by rfl⟩ : syracuseStep 526051 = 789077) B789077
theorem B493283 : Blo 491791 493283 := bstep (se 1 (by rfl) ⟨369962, by rfl⟩ : syracuseStep 493283 = 739925) B739925
theorem B1410797 : Blo 491791 1410797 := bstep (se 3 (by rfl) ⟨264524, by rfl⟩ : syracuseStep 1410797 = 529049) B529049
theorem B493299 : Blo 491791 493299 := bstep (se 1 (by rfl) ⟨369974, by rfl⟩ : syracuseStep 493299 = 739949) B739949
theorem B493315 : Blo 491791 493315 := bstep (se 1 (by rfl) ⟨369986, by rfl⟩ : syracuseStep 493315 = 739973) B739973
theorem B952067 : Blo 491791 952067 := bstep (se 1 (by rfl) ⟨714050, by rfl⟩ : syracuseStep 952067 = 1428101) B1428101
theorem B1869581 : Blo 491791 1869581 := bstep (se 3 (by rfl) ⟨350546, by rfl⟩ : syracuseStep 1869581 = 701093) B701093
theorem B1672973 : Blo 491791 1672973 := bstep (se 3 (by rfl) ⟨313682, by rfl⟩ : syracuseStep 1672973 = 627365) B627365
theorem B493331 : Blo 491791 493331 := bstep (se 1 (by rfl) ⟨369998, by rfl⟩ : syracuseStep 493331 = 739997) B739997
theorem B493347 : Blo 491791 493347 := bstep (se 1 (by rfl) ⟨370010, by rfl⟩ : syracuseStep 493347 = 740021) B740021
theorem B493363 : Blo 491791 493363 := bstep (se 1 (by rfl) ⟨370022, by rfl⟩ : syracuseStep 493363 = 740045) B740045
theorem B493379 : Blo 491791 493379 := bstep (se 1 (by rfl) ⟨370034, by rfl⟩ : syracuseStep 493379 = 740069) B740069
theorem B1673027 : Blo 491791 1673027 := bstep (se 1 (by rfl) ⟨1254770, by rfl⟩ : syracuseStep 1673027 = 2509541) B2509541
theorem B493395 : Blo 491791 493395 := bstep (se 1 (by rfl) ⟨370046, by rfl⟩ : syracuseStep 493395 = 740093) B740093
theorem B493411 : Blo 491791 493411 := bstep (se 1 (by rfl) ⟨370058, by rfl⟩ : syracuseStep 493411 = 740117) B740117
theorem B493427 : Blo 491791 493427 := bstep (se 1 (by rfl) ⟨370070, by rfl⟩ : syracuseStep 493427 = 740141) B740141
theorem B493443 : Blo 491791 493443 := bstep (se 1 (by rfl) ⟨370082, by rfl⟩ : syracuseStep 493443 = 740165) B740165
theorem B493459 : Blo 491791 493459 := bstep (se 1 (by rfl) ⟨370094, by rfl⟩ : syracuseStep 493459 = 740189) B740189
theorem B493475 : Blo 491791 493475 := bstep (se 1 (by rfl) ⟨370106, by rfl⟩ : syracuseStep 493475 = 740213) B740213
theorem B493491 : Blo 491791 493491 := bstep (se 1 (by rfl) ⟨370118, by rfl⟩ : syracuseStep 493491 = 740237) B740237
theorem B493507 : Blo 491791 493507 := bstep (se 1 (by rfl) ⟨370130, by rfl⟩ : syracuseStep 493507 = 740261) B740261
theorem B5638085 : Blo 491791 5638085 := bstep (se 4 (by rfl) ⟨528570, by rfl⟩ : syracuseStep 5638085 = 1057141) B1057141
theorem B493523 : Blo 491791 493523 := bstep (se 1 (by rfl) ⟨370142, by rfl⟩ : syracuseStep 493523 = 740285) B740285
theorem B624611 : Blo 491791 624611 := bstep (se 1 (by rfl) ⟨468458, by rfl⟩ : syracuseStep 624611 = 936917) B936917
theorem B493539 : Blo 491791 493539 := bstep (se 1 (by rfl) ⟨370154, by rfl⟩ : syracuseStep 493539 = 740309) B740309
theorem B493555 : Blo 491791 493555 := bstep (se 1 (by rfl) ⟨370166, by rfl⟩ : syracuseStep 493555 = 740333) B740333
theorem B493571 : Blo 491791 493571 := bstep (se 1 (by rfl) ⟨370178, by rfl⟩ : syracuseStep 493571 = 740357) B740357
theorem B1050641 : Blo 491791 1050641 := bstep (se 2 (by rfl) ⟨393990, by rfl⟩ : syracuseStep 1050641 = 787981) B787981
theorem B493587 : Blo 491791 493587 := bstep (se 1 (by rfl) ⟨370190, by rfl⟩ : syracuseStep 493587 = 740381) B740381
theorem B493603 : Blo 491791 493603 := bstep (se 1 (by rfl) ⟨370202, by rfl⟩ : syracuseStep 493603 = 740405) B740405
theorem B493619 : Blo 491791 493619 := bstep (se 1 (by rfl) ⟨370214, by rfl⟩ : syracuseStep 493619 = 740429) B740429
theorem B788545 : Blo 491791 788545 := bstep (se 2 (by rfl) ⟨295704, by rfl⟩ : syracuseStep 788545 = 591409) B591409
theorem B493635 : Blo 491791 493635 := bstep (se 1 (by rfl) ⟨370226, by rfl⟩ : syracuseStep 493635 = 740453) B740453
theorem B1673297 : Blo 491791 1673297 := bstep (se 2 (by rfl) ⟨627486, by rfl⟩ : syracuseStep 1673297 = 1254973) B1254973
theorem B493651 : Blo 491791 493651 := bstep (se 1 (by rfl) ⟨370238, by rfl⟩ : syracuseStep 493651 = 740477) B740477
theorem B493667 : Blo 491791 493667 := bstep (se 1 (by rfl) ⟨370250, by rfl⟩ : syracuseStep 493667 = 740501) B740501
theorem B493683 : Blo 491791 493683 := bstep (se 1 (by rfl) ⟨370262, by rfl⟩ : syracuseStep 493683 = 740525) B740525
theorem B493699 : Blo 491791 493699 := bstep (se 1 (by rfl) ⟨370274, by rfl⟩ : syracuseStep 493699 = 740549) B740549
theorem B493715 : Blo 491791 493715 := bstep (se 1 (by rfl) ⟨370286, by rfl⟩ : syracuseStep 493715 = 740573) B740573
theorem B493731 : Blo 491791 493731 := bstep (se 1 (by rfl) ⟨370298, by rfl⟩ : syracuseStep 493731 = 740597) B740597
theorem B493747 : Blo 491791 493747 := bstep (se 1 (by rfl) ⟨370310, by rfl⟩ : syracuseStep 493747 = 740621) B740621
theorem B493763 : Blo 491791 493763 := bstep (se 1 (by rfl) ⟨370322, by rfl⟩ : syracuseStep 493763 = 740645) B740645
theorem B493779 : Blo 491791 493779 := bstep (se 1 (by rfl) ⟨370334, by rfl⟩ : syracuseStep 493779 = 740669) B740669
theorem B493795 : Blo 491791 493795 := bstep (se 1 (by rfl) ⟨370346, by rfl⟩ : syracuseStep 493795 = 740693) B740693
theorem B592115 : Blo 491791 592115 := bstep (se 1 (by rfl) ⟨444086, by rfl⟩ : syracuseStep 592115 = 888173) B888173
theorem B493811 : Blo 491791 493811 := bstep (se 1 (by rfl) ⟨370358, by rfl⟩ : syracuseStep 493811 = 740717) B740717
theorem B493827 : Blo 491791 493827 := bstep (se 1 (by rfl) ⟨370370, by rfl⟩ : syracuseStep 493827 = 740741) B740741
theorem B2820365 : Blo 491791 2820365 := bstep (se 3 (by rfl) ⟨528818, by rfl⟩ : syracuseStep 2820365 = 1057637) B1057637
theorem B493843 : Blo 491791 493843 := bstep (se 1 (by rfl) ⟨370382, by rfl⟩ : syracuseStep 493843 = 740765) B740765
theorem B493859 : Blo 491791 493859 := bstep (se 1 (by rfl) ⟨370394, by rfl⟩ : syracuseStep 493859 = 740789) B740789
theorem B493875 : Blo 491791 493875 := bstep (se 1 (by rfl) ⟨370406, by rfl⟩ : syracuseStep 493875 = 740813) B740813
theorem B493891 : Blo 491791 493891 := bstep (se 1 (by rfl) ⟨370418, by rfl⟩ : syracuseStep 493891 = 740837) B740837
theorem B493907 : Blo 491791 493907 := bstep (se 1 (by rfl) ⟨370430, by rfl⟩ : syracuseStep 493907 = 740861) B740861
theorem B493923 : Blo 491791 493923 := bstep (se 1 (by rfl) ⟨370442, by rfl⟩ : syracuseStep 493923 = 740885) B740885
theorem B493939 : Blo 491791 493939 := bstep (se 1 (by rfl) ⟨370454, by rfl⟩ : syracuseStep 493939 = 740909) B740909
theorem B493955 : Blo 491791 493955 := bstep (se 1 (by rfl) ⟨370466, by rfl⟩ : syracuseStep 493955 = 740933) B740933
theorem B4065677 : Blo 491791 4065677 := bstep (se 3 (by rfl) ⟨762314, by rfl⟩ : syracuseStep 4065677 = 1524629) B1524629
theorem B1247633 : Blo 491791 1247633 := bstep (se 2 (by rfl) ⟨467862, by rfl⟩ : syracuseStep 1247633 = 935725) B935725
theorem B493971 : Blo 491791 493971 := bstep (se 1 (by rfl) ⟨370478, by rfl⟩ : syracuseStep 493971 = 740957) B740957
theorem B493987 : Blo 491791 493987 := bstep (se 1 (by rfl) ⟨370490, by rfl⟩ : syracuseStep 493987 = 740981) B740981
theorem B494003 : Blo 491791 494003 := bstep (se 1 (by rfl) ⟨370502, by rfl⟩ : syracuseStep 494003 = 741005) B741005
theorem B1247683 : Blo 491791 1247683 := bstep (se 1 (by rfl) ⟨935762, by rfl⟩ : syracuseStep 1247683 = 1871525) B1871525
theorem B494019 : Blo 491791 494019 := bstep (se 1 (by rfl) ⟨370514, by rfl⟩ : syracuseStep 494019 = 741029) B741029
theorem B494035 : Blo 491791 494035 := bstep (se 1 (by rfl) ⟨370526, by rfl⟩ : syracuseStep 494035 = 741053) B741053
theorem B494051 : Blo 491791 494051 := bstep (se 1 (by rfl) ⟨370538, by rfl⟩ : syracuseStep 494051 = 741077) B741077
theorem B494067 : Blo 491791 494067 := bstep (se 1 (by rfl) ⟨370550, by rfl⟩ : syracuseStep 494067 = 741101) B741101
theorem B494083 : Blo 491791 494083 := bstep (se 1 (by rfl) ⟨370562, by rfl⟩ : syracuseStep 494083 = 741125) B741125
theorem B494099 : Blo 491791 494099 := bstep (se 1 (by rfl) ⟨370574, by rfl⟩ : syracuseStep 494099 = 741149) B741149
theorem B494115 : Blo 491791 494115 := bstep (se 1 (by rfl) ⟨370586, by rfl⟩ : syracuseStep 494115 = 741173) B741173
theorem B494131 : Blo 491791 494131 := bstep (se 1 (by rfl) ⟨370598, by rfl⟩ : syracuseStep 494131 = 741197) B741197
theorem B494147 : Blo 491791 494147 := bstep (se 1 (by rfl) ⟨370610, by rfl⟩ : syracuseStep 494147 = 741221) B741221
theorem B1247825 : Blo 491791 1247825 := bstep (se 2 (by rfl) ⟨467934, by rfl⟩ : syracuseStep 1247825 = 935869) B935869
theorem B494163 : Blo 491791 494163 := bstep (se 1 (by rfl) ⟨370622, by rfl⟩ : syracuseStep 494163 = 741245) B741245
theorem B494179 : Blo 491791 494179 := bstep (se 1 (by rfl) ⟨370634, by rfl⟩ : syracuseStep 494179 = 741269) B741269
theorem B494195 : Blo 491791 494195 := bstep (se 1 (by rfl) ⟨370646, by rfl⟩ : syracuseStep 494195 = 741293) B741293
theorem B494211 : Blo 491791 494211 := bstep (se 1 (by rfl) ⟨370658, by rfl⟩ : syracuseStep 494211 = 741317) B741317
theorem B494227 : Blo 491791 494227 := bstep (se 1 (by rfl) ⟨370670, by rfl⟩ : syracuseStep 494227 = 741341) B741341
theorem B625315 : Blo 491791 625315 := bstep (se 1 (by rfl) ⟨468986, by rfl⟩ : syracuseStep 625315 = 937973) B937973
theorem B494243 : Blo 491791 494243 := bstep (se 1 (by rfl) ⟨370682, by rfl⟩ : syracuseStep 494243 = 741365) B741365
theorem B494259 : Blo 491791 494259 := bstep (se 1 (by rfl) ⟨370694, by rfl⟩ : syracuseStep 494259 = 741389) B741389
theorem B494275 : Blo 491791 494275 := bstep (se 1 (by rfl) ⟨370706, by rfl⟩ : syracuseStep 494275 = 741413) B741413
theorem B1411789 : Blo 491791 1411789 := bstep (se 3 (by rfl) ⟨264710, by rfl⟩ : syracuseStep 1411789 = 529421) B529421
theorem B494291 : Blo 491791 494291 := bstep (se 1 (by rfl) ⟨370718, by rfl⟩ : syracuseStep 494291 = 741437) B741437
theorem B494307 : Blo 491791 494307 := bstep (se 1 (by rfl) ⟨370730, by rfl⟩ : syracuseStep 494307 = 741461) B741461
theorem B5999345 : Blo 491791 5999345 := bstep (se 2 (by rfl) ⟨2249754, by rfl⟩ : syracuseStep 5999345 = 4499509) B4499509
theorem B494323 : Blo 491791 494323 := bstep (se 1 (by rfl) ⟨370742, by rfl⟩ : syracuseStep 494323 = 741485) B741485
theorem B625411 : Blo 491791 625411 := bstep (se 1 (by rfl) ⟨469058, by rfl⟩ : syracuseStep 625411 = 938117) B938117
theorem B494339 : Blo 491791 494339 := bstep (se 1 (by rfl) ⟨370754, by rfl⟩ : syracuseStep 494339 = 741509) B741509
theorem B494355 : Blo 491791 494355 := bstep (se 1 (by rfl) ⟨370766, by rfl⟩ : syracuseStep 494355 = 741533) B741533
theorem B494371 : Blo 491791 494371 := bstep (se 1 (by rfl) ⟨370778, by rfl⟩ : syracuseStep 494371 = 741557) B741557
theorem B494387 : Blo 491791 494387 := bstep (se 1 (by rfl) ⟨370790, by rfl⟩ : syracuseStep 494387 = 741581) B741581
theorem B494403 : Blo 491791 494403 := bstep (se 1 (by rfl) ⟨370802, by rfl⟩ : syracuseStep 494403 = 741605) B741605
theorem B494419 : Blo 491791 494419 := bstep (se 1 (by rfl) ⟨370814, by rfl⟩ : syracuseStep 494419 = 741629) B741629
theorem B494435 : Blo 491791 494435 := bstep (se 1 (by rfl) ⟨370826, by rfl⟩ : syracuseStep 494435 = 741653) B741653
theorem B494451 : Blo 491791 494451 := bstep (se 1 (by rfl) ⟨370838, by rfl⟩ : syracuseStep 494451 = 741677) B741677
theorem B1182595 : Blo 491791 1182595 := bstep (se 1 (by rfl) ⟨886946, by rfl⟩ : syracuseStep 1182595 = 1773893) B1773893
theorem B494467 : Blo 491791 494467 := bstep (se 1 (by rfl) ⟨370850, by rfl⟩ : syracuseStep 494467 = 741701) B741701
theorem B1051537 : Blo 491791 1051537 := bstep (se 2 (by rfl) ⟨394326, by rfl⟩ : syracuseStep 1051537 = 788653) B788653
theorem B494483 : Blo 491791 494483 := bstep (se 1 (by rfl) ⟨370862, by rfl⟩ : syracuseStep 494483 = 741725) B741725
theorem B1051555 : Blo 491791 1051555 := bstep (se 1 (by rfl) ⟨788666, by rfl⟩ : syracuseStep 1051555 = 1577333) B1577333
theorem B494499 : Blo 491791 494499 := bstep (se 1 (by rfl) ⟨370874, by rfl⟩ : syracuseStep 494499 = 741749) B741749
theorem B494515 : Blo 491791 494515 := bstep (se 1 (by rfl) ⟨370886, by rfl⟩ : syracuseStep 494515 = 741773) B741773
theorem B494531 : Blo 491791 494531 := bstep (se 1 (by rfl) ⟨370898, by rfl⟩ : syracuseStep 494531 = 741797) B741797
theorem B527315 : Blo 491791 527315 := bstep (se 1 (by rfl) ⟨395486, by rfl⟩ : syracuseStep 527315 = 790973) B790973
theorem B494547 : Blo 491791 494547 := bstep (se 1 (by rfl) ⟨370910, by rfl⟩ : syracuseStep 494547 = 741821) B741821
theorem B789473 : Blo 491791 789473 := bstep (se 2 (by rfl) ⟨296052, by rfl⟩ : syracuseStep 789473 = 592105) B592105
theorem B494563 : Blo 491791 494563 := bstep (se 1 (by rfl) ⟨370922, by rfl⟩ : syracuseStep 494563 = 741845) B741845
theorem B494579 : Blo 491791 494579 := bstep (se 1 (by rfl) ⟨370934, by rfl⟩ : syracuseStep 494579 = 741869) B741869
theorem B494595 : Blo 491791 494595 := bstep (se 1 (by rfl) ⟨370946, by rfl⟩ : syracuseStep 494595 = 741893) B741893
theorem B494611 : Blo 491791 494611 := bstep (se 1 (by rfl) ⟨370958, by rfl⟩ : syracuseStep 494611 = 741917) B741917
theorem B494627 : Blo 491791 494627 := bstep (se 1 (by rfl) ⟨370970, by rfl⟩ : syracuseStep 494627 = 741941) B741941
theorem B494643 : Blo 491791 494643 := bstep (se 1 (by rfl) ⟨370982, by rfl⟩ : syracuseStep 494643 = 741965) B741965
theorem B494659 : Blo 491791 494659 := bstep (se 1 (by rfl) ⟨370994, by rfl⟩ : syracuseStep 494659 = 741989) B741989
theorem B494675 : Blo 491791 494675 := bstep (se 1 (by rfl) ⟨371006, by rfl⟩ : syracuseStep 494675 = 742013) B742013
theorem B494691 : Blo 491791 494691 := bstep (se 1 (by rfl) ⟨371018, by rfl⟩ : syracuseStep 494691 = 742037) B742037
theorem B494707 : Blo 491791 494707 := bstep (se 1 (by rfl) ⟨371030, by rfl⟩ : syracuseStep 494707 = 742061) B742061
theorem B494723 : Blo 491791 494723 := bstep (se 1 (by rfl) ⟨371042, by rfl⟩ : syracuseStep 494723 = 742085) B742085
theorem B494739 : Blo 491791 494739 := bstep (se 1 (by rfl) ⟨371054, by rfl⟩ : syracuseStep 494739 = 742109) B742109
theorem B494755 : Blo 491791 494755 := bstep (se 1 (by rfl) ⟨371066, by rfl⟩ : syracuseStep 494755 = 742133) B742133
theorem B494771 : Blo 491791 494771 := bstep (se 1 (by rfl) ⟨371078, by rfl⟩ : syracuseStep 494771 = 742157) B742157
theorem B494787 : Blo 491791 494787 := bstep (se 1 (by rfl) ⟨371090, by rfl⟩ : syracuseStep 494787 = 742181) B742181
theorem B3214541 : Blo 491791 3214541 := bstep (se 3 (by rfl) ⟨602726, by rfl⟩ : syracuseStep 3214541 = 1205453) B1205453
theorem B494803 : Blo 491791 494803 := bstep (se 1 (by rfl) ⟨371102, by rfl⟩ : syracuseStep 494803 = 742205) B742205
theorem B494819 : Blo 491791 494819 := bstep (se 1 (by rfl) ⟨371114, by rfl⟩ : syracuseStep 494819 = 742229) B742229
theorem B625907 : Blo 491791 625907 := bstep (se 1 (by rfl) ⟨469430, by rfl⟩ : syracuseStep 625907 = 938861) B938861
theorem B494835 : Blo 491791 494835 := bstep (se 1 (by rfl) ⟨371126, by rfl⟩ : syracuseStep 494835 = 742253) B742253
theorem B494851 : Blo 491791 494851 := bstep (se 1 (by rfl) ⟨371138, by rfl⟩ : syracuseStep 494851 = 742277) B742277
theorem B1576205 : Blo 491791 1576205 := bstep (se 3 (by rfl) ⟨295538, by rfl⟩ : syracuseStep 1576205 = 591077) B591077
theorem B494867 : Blo 491791 494867 := bstep (se 1 (by rfl) ⟨371150, by rfl⟩ : syracuseStep 494867 = 742301) B742301
theorem B494883 : Blo 491791 494883 := bstep (se 1 (by rfl) ⟨371162, by rfl⟩ : syracuseStep 494883 = 742325) B742325
theorem B494899 : Blo 491791 494899 := bstep (se 1 (by rfl) ⟨371174, by rfl⟩ : syracuseStep 494899 = 742349) B742349
theorem B494915 : Blo 491791 494915 := bstep (se 1 (by rfl) ⟨371186, by rfl⟩ : syracuseStep 494915 = 742373) B742373
theorem B494931 : Blo 491791 494931 := bstep (se 1 (by rfl) ⟨371198, by rfl⟩ : syracuseStep 494931 = 742397) B742397
theorem B494947 : Blo 491791 494947 := bstep (se 1 (by rfl) ⟨371210, by rfl⟩ : syracuseStep 494947 = 742421) B742421
theorem B494963 : Blo 491791 494963 := bstep (se 1 (by rfl) ⟨371222, by rfl⟩ : syracuseStep 494963 = 742445) B742445
theorem B494979 : Blo 491791 494979 := bstep (se 1 (by rfl) ⟨371234, by rfl⟩ : syracuseStep 494979 = 742469) B742469
theorem B494995 : Blo 491791 494995 := bstep (se 1 (by rfl) ⟨371246, by rfl⟩ : syracuseStep 494995 = 742493) B742493
theorem B495011 : Blo 491791 495011 := bstep (se 1 (by rfl) ⟨371258, by rfl⟩ : syracuseStep 495011 = 742517) B742517
theorem B495027 : Blo 491791 495027 := bstep (se 1 (by rfl) ⟨371270, by rfl⟩ : syracuseStep 495027 = 742541) B742541
theorem B495043 : Blo 491791 495043 := bstep (se 1 (by rfl) ⟨371282, by rfl⟩ : syracuseStep 495043 = 742565) B742565
theorem B7212485 : Blo 491791 7212485 := bstep (se 4 (by rfl) ⟨676170, by rfl⟩ : syracuseStep 7212485 = 1352341) B1352341
theorem B495059 : Blo 491791 495059 := bstep (se 1 (by rfl) ⟨371294, by rfl⟩ : syracuseStep 495059 = 742589) B742589
theorem B495075 : Blo 491791 495075 := bstep (se 1 (by rfl) ⟨371306, by rfl⟩ : syracuseStep 495075 = 742613) B742613
theorem B495091 : Blo 491791 495091 := bstep (se 1 (by rfl) ⟨371318, by rfl⟩ : syracuseStep 495091 = 742637) B742637
theorem B495107 : Blo 491791 495107 := bstep (se 1 (by rfl) ⟨371330, by rfl⟩ : syracuseStep 495107 = 742661) B742661
theorem B495123 : Blo 491791 495123 := bstep (se 1 (by rfl) ⟨371342, by rfl⟩ : syracuseStep 495123 = 742685) B742685
theorem B495139 : Blo 491791 495139 := bstep (se 1 (by rfl) ⟨371354, by rfl⟩ : syracuseStep 495139 = 742709) B742709
theorem B1248817 : Blo 491791 1248817 := bstep (se 2 (by rfl) ⟨468306, by rfl⟩ : syracuseStep 1248817 = 936613) B936613
theorem B495155 : Blo 491791 495155 := bstep (se 1 (by rfl) ⟨371366, by rfl⟩ : syracuseStep 495155 = 742733) B742733
theorem B495171 : Blo 491791 495171 := bstep (se 1 (by rfl) ⟨371378, by rfl⟩ : syracuseStep 495171 = 742757) B742757
theorem B495187 : Blo 491791 495187 := bstep (se 1 (by rfl) ⟨371390, by rfl⟩ : syracuseStep 495187 = 742781) B742781
theorem B495203 : Blo 491791 495203 := bstep (se 1 (by rfl) ⟨371402, by rfl⟩ : syracuseStep 495203 = 742805) B742805
theorem B495219 : Blo 491791 495219 := bstep (se 1 (by rfl) ⟨371414, by rfl⟩ : syracuseStep 495219 = 742829) B742829
theorem B495235 : Blo 491791 495235 := bstep (se 1 (by rfl) ⟨371426, by rfl⟩ : syracuseStep 495235 = 742853) B742853
theorem B13471373 : Blo 491791 13471373 := bstep (se 3 (by rfl) ⟨2525882, by rfl⟩ : syracuseStep 13471373 = 5051765) B5051765
theorem B1904269 : Blo 491791 1904269 := bstep (se 3 (by rfl) ⟨357050, by rfl⟩ : syracuseStep 1904269 = 714101) B714101
theorem B495251 : Blo 491791 495251 := bstep (se 1 (by rfl) ⟨371438, by rfl⟩ : syracuseStep 495251 = 742877) B742877
theorem B495267 : Blo 491791 495267 := bstep (se 1 (by rfl) ⟨371450, by rfl⟩ : syracuseStep 495267 = 742901) B742901
theorem B495283 : Blo 491791 495283 := bstep (se 1 (by rfl) ⟨371462, by rfl⟩ : syracuseStep 495283 = 742925) B742925
theorem B528067 : Blo 491791 528067 := bstep (se 1 (by rfl) ⟨396050, by rfl⟩ : syracuseStep 528067 = 792101) B792101
theorem B495299 : Blo 491791 495299 := bstep (se 1 (by rfl) ⟨371474, by rfl⟩ : syracuseStep 495299 = 742949) B742949
theorem B495315 : Blo 491791 495315 := bstep (se 1 (by rfl) ⟨371486, by rfl⟩ : syracuseStep 495315 = 742973) B742973
theorem B495331 : Blo 491791 495331 := bstep (se 1 (by rfl) ⟨371498, by rfl⟩ : syracuseStep 495331 = 742997) B742997
theorem B495347 : Blo 491791 495347 := bstep (se 1 (by rfl) ⟨371510, by rfl⟩ : syracuseStep 495347 = 743021) B743021
theorem B495363 : Blo 491791 495363 := bstep (se 1 (by rfl) ⟨371522, by rfl⟩ : syracuseStep 495363 = 743045) B743045
theorem B495379 : Blo 491791 495379 := bstep (se 1 (by rfl) ⟨371534, by rfl⟩ : syracuseStep 495379 = 743069) B743069
theorem B790307 : Blo 491791 790307 := bstep (se 1 (by rfl) ⟨592730, by rfl⟩ : syracuseStep 790307 = 1185461) B1185461
theorem B495395 : Blo 491791 495395 := bstep (se 1 (by rfl) ⟨371546, by rfl⟩ : syracuseStep 495395 = 743093) B743093
theorem B495411 : Blo 491791 495411 := bstep (se 1 (by rfl) ⟨371558, by rfl⟩ : syracuseStep 495411 = 743117) B743117
theorem B790339 : Blo 491791 790339 := bstep (se 1 (by rfl) ⟨592754, by rfl⟩ : syracuseStep 790339 = 1185509) B1185509
theorem B1249091 : Blo 491791 1249091 := bstep (se 1 (by rfl) ⟨936818, by rfl⟩ : syracuseStep 1249091 = 1873637) B1873637
theorem B495427 : Blo 491791 495427 := bstep (se 1 (by rfl) ⟨371570, by rfl⟩ : syracuseStep 495427 = 743141) B743141
theorem B1871693 : Blo 491791 1871693 := bstep (se 3 (by rfl) ⟨350942, by rfl⟩ : syracuseStep 1871693 = 701885) B701885
theorem B495443 : Blo 491791 495443 := bstep (se 1 (by rfl) ⟨371582, by rfl⟩ : syracuseStep 495443 = 743165) B743165
theorem B495459 : Blo 491791 495459 := bstep (se 1 (by rfl) ⟨371594, by rfl⟩ : syracuseStep 495459 = 743189) B743189
theorem B4231025 : Blo 491791 4231025 := bstep (se 2 (by rfl) ⟨1586634, by rfl⟩ : syracuseStep 4231025 = 3173269) B3173269
theorem B495475 : Blo 491791 495475 := bstep (se 1 (by rfl) ⟨371606, by rfl⟩ : syracuseStep 495475 = 743213) B743213
theorem B495491 : Blo 491791 495491 := bstep (se 1 (by rfl) ⟨371618, by rfl⟩ : syracuseStep 495491 = 743237) B743237
theorem B5345165 : Blo 491791 5345165 := bstep (se 3 (by rfl) ⟨1002218, by rfl⟩ : syracuseStep 5345165 = 2004437) B2004437
theorem B495507 : Blo 491791 495507 := bstep (se 1 (by rfl) ⟨371630, by rfl⟩ : syracuseStep 495507 = 743261) B743261
theorem B495523 : Blo 491791 495523 := bstep (se 1 (by rfl) ⟨371642, by rfl⟩ : syracuseStep 495523 = 743285) B743285
theorem B626611 : Blo 491791 626611 := bstep (se 1 (by rfl) ⟨469958, by rfl⟩ : syracuseStep 626611 = 939917) B939917
theorem B495539 : Blo 491791 495539 := bstep (se 1 (by rfl) ⟨371654, by rfl⟩ : syracuseStep 495539 = 743309) B743309
theorem B495555 : Blo 491791 495555 := bstep (se 1 (by rfl) ⟨371666, by rfl⟩ : syracuseStep 495555 = 743333) B743333
theorem B495571 : Blo 491791 495571 := bstep (se 1 (by rfl) ⟨371678, by rfl⟩ : syracuseStep 495571 = 743357) B743357
theorem B495587 : Blo 491791 495587 := bstep (se 1 (by rfl) ⟨371690, by rfl⟩ : syracuseStep 495587 = 743381) B743381
theorem B495603 : Blo 491791 495603 := bstep (se 1 (by rfl) ⟨371702, by rfl⟩ : syracuseStep 495603 = 743405) B743405
theorem B1249283 : Blo 491791 1249283 := bstep (se 1 (by rfl) ⟨936962, by rfl⟩ : syracuseStep 1249283 = 1873925) B1873925
theorem B495619 : Blo 491791 495619 := bstep (se 1 (by rfl) ⟨371714, by rfl⟩ : syracuseStep 495619 = 743429) B743429
theorem B626707 : Blo 491791 626707 := bstep (se 1 (by rfl) ⟨470030, by rfl⟩ : syracuseStep 626707 = 940061) B940061
theorem B495635 : Blo 491791 495635 := bstep (se 1 (by rfl) ⟨371726, by rfl⟩ : syracuseStep 495635 = 743453) B743453
theorem B495651 : Blo 491791 495651 := bstep (se 1 (by rfl) ⟨371738, by rfl⟩ : syracuseStep 495651 = 743477) B743477
theorem B2101297 : Blo 491791 2101297 := bstep (se 2 (by rfl) ⟨787986, by rfl⟩ : syracuseStep 2101297 = 1575973) B1575973
theorem B495667 : Blo 491791 495667 := bstep (se 1 (by rfl) ⟨371750, by rfl⟩ : syracuseStep 495667 = 743501) B743501
theorem B495683 : Blo 491791 495683 := bstep (se 1 (by rfl) ⟨371762, by rfl⟩ : syracuseStep 495683 = 743525) B743525
theorem B1183825 : Blo 491791 1183825 := bstep (se 2 (by rfl) ⟨443934, by rfl⟩ : syracuseStep 1183825 = 887869) B887869
theorem B495699 : Blo 491791 495699 := bstep (se 1 (by rfl) ⟨371774, by rfl⟩ : syracuseStep 495699 = 743549) B743549
theorem B495715 : Blo 491791 495715 := bstep (se 1 (by rfl) ⟨371786, by rfl⟩ : syracuseStep 495715 = 743573) B743573
theorem B495731 : Blo 491791 495731 := bstep (se 1 (by rfl) ⟨371798, by rfl⟩ : syracuseStep 495731 = 743597) B743597
theorem B495747 : Blo 491791 495747 := bstep (se 1 (by rfl) ⟨371810, by rfl⟩ : syracuseStep 495747 = 743621) B743621
theorem B1216657 : Blo 491791 1216657 := bstep (se 2 (by rfl) ⟨456246, by rfl⟩ : syracuseStep 1216657 = 912493) B912493
theorem B495763 : Blo 491791 495763 := bstep (se 1 (by rfl) ⟨371822, by rfl⟩ : syracuseStep 495763 = 743645) B743645
theorem B495779 : Blo 491791 495779 := bstep (se 1 (by rfl) ⟨371834, by rfl⟩ : syracuseStep 495779 = 743669) B743669
theorem B6951349 : Blo 491791 6951349 := bstep (se 5 (by rfl) ⟨325844, by rfl⟩ : syracuseStep 6951349 = 651689) B651689
theorem B8556997 : Blo 491791 8556997 := bstep (se 4 (by rfl) ⟨802218, by rfl⟩ : syracuseStep 8556997 = 1604437) B1604437
theorem B2822597 : Blo 491791 2822597 := bstep (se 4 (by rfl) ⟨264618, by rfl⟩ : syracuseStep 2822597 = 529237) B529237
theorem B1085905 : Blo 491791 1085905 := bstep (se 2 (by rfl) ⟨407214, by rfl⟩ : syracuseStep 1085905 = 814429) B814429
theorem B2494961 : Blo 491791 2494961 := bstep (se 2 (by rfl) ⟨935610, by rfl⟩ : syracuseStep 2494961 = 1871221) B1871221
theorem B627203 : Blo 491791 627203 := bstep (se 1 (by rfl) ⟨470402, by rfl⟩ : syracuseStep 627203 = 940805) B940805
theorem B1872497 : Blo 491791 1872497 := bstep (se 2 (by rfl) ⟨702186, by rfl⟩ : syracuseStep 1872497 = 1404373) B1404373
theorem B12030605 : Blo 491791 12030605 := bstep (se 3 (by rfl) ⟨2255738, by rfl⟩ : syracuseStep 12030605 = 4511477) B4511477
theorem B4264645 : Blo 491791 4264645 := bstep (se 4 (by rfl) ⟨399810, by rfl⟩ : syracuseStep 4264645 = 799621) B799621
theorem B791267 : Blo 491791 791267 := bstep (se 1 (by rfl) ⟨593450, by rfl⟩ : syracuseStep 791267 = 1186901) B1186901
theorem B791345 : Blo 491791 791345 := bstep (se 2 (by rfl) ⟨296754, by rfl⟩ : syracuseStep 791345 = 593509) B593509
theorem B594739 : Blo 491791 594739 := bstep (se 1 (by rfl) ⟨446054, by rfl⟩ : syracuseStep 594739 = 892109) B892109
theorem B1250225 : Blo 491791 1250225 := bstep (se 2 (by rfl) ⟨468834, by rfl⟩ : syracuseStep 1250225 = 937669) B937669
theorem B1250275 : Blo 491791 1250275 := bstep (se 1 (by rfl) ⟨937706, by rfl⟩ : syracuseStep 1250275 = 1875413) B1875413
theorem B594931 : Blo 491791 594931 := bstep (se 1 (by rfl) ⟨446198, by rfl⟩ : syracuseStep 594931 = 892397) B892397
theorem B791569 : Blo 491791 791569 := bstep (se 2 (by rfl) ⟨296838, by rfl⟩ : syracuseStep 791569 = 593677) B593677
theorem B3740741 : Blo 491791 3740741 := bstep (se 4 (by rfl) ⟨350694, by rfl⟩ : syracuseStep 3740741 = 701389) B701389
theorem B2528333 : Blo 491791 2528333 := bstep (se 3 (by rfl) ⟨474062, by rfl⟩ : syracuseStep 2528333 = 948125) B948125
theorem B1250417 : Blo 491791 1250417 := bstep (se 2 (by rfl) ⟨468906, by rfl⟩ : syracuseStep 1250417 = 937813) B937813
theorem B2823281 : Blo 491791 2823281 := bstep (se 2 (by rfl) ⟨1058730, by rfl⟩ : syracuseStep 2823281 = 2117461) B2117461
theorem B1053827 : Blo 491791 1053827 := bstep (se 1 (by rfl) ⟨790370, by rfl⟩ : syracuseStep 1053827 = 1580741) B1580741
theorem B595075 : Blo 491791 595075 := bstep (se 1 (by rfl) ⟨446306, by rfl⟩ : syracuseStep 595075 = 892613) B892613
theorem B1873165 : Blo 491791 1873165 := bstep (se 3 (by rfl) ⟨351218, by rfl⟩ : syracuseStep 1873165 = 702437) B702437
theorem B3151331 : Blo 491791 3151331 := bstep (se 1 (by rfl) ⟨2363498, by rfl⟩ : syracuseStep 3151331 = 4726997) B4726997
theorem B1054289 : Blo 491791 1054289 := bstep (se 2 (by rfl) ⟨395358, by rfl⟩ : syracuseStep 1054289 = 790717) B790717
theorem B2659973 : Blo 491791 2659973 := bstep (se 4 (by rfl) ⟨249372, by rfl⟩ : syracuseStep 2659973 = 498745) B498745
theorem B2496419 : Blo 491791 2496419 := bstep (se 1 (by rfl) ⟨1872314, by rfl⟩ : syracuseStep 2496419 = 3744629) B3744629
theorem B1775537 : Blo 491791 1775537 := bstep (se 2 (by rfl) ⟨665826, by rfl⟩ : syracuseStep 1775537 = 1331653) B1331653
theorem B1873955 : Blo 491791 1873955 := bstep (se 1 (by rfl) ⟨1405466, by rfl⟩ : syracuseStep 1873955 = 2810933) B2810933
theorem B1251409 : Blo 491791 1251409 := bstep (se 2 (by rfl) ⟨469278, by rfl⟩ : syracuseStep 1251409 = 938557) B938557
theorem B4233485 : Blo 491791 4233485 := bstep (se 3 (by rfl) ⟨793778, by rfl⟩ : syracuseStep 4233485 = 1587557) B1587557
theorem B1251683 : Blo 491791 1251683 := bstep (se 1 (by rfl) ⟨938762, by rfl⟩ : syracuseStep 1251683 = 1877525) B1877525
theorem B1579409 : Blo 491791 1579409 := bstep (se 2 (by rfl) ⟨592278, by rfl⟩ : syracuseStep 1579409 = 1184557) B1184557
theorem B1579459 : Blo 491791 1579459 := bstep (se 1 (by rfl) ⟨1184594, by rfl⟩ : syracuseStep 1579459 = 2369189) B2369189
theorem B1251875 : Blo 491791 1251875 := bstep (se 1 (by rfl) ⟨938906, by rfl⟩ : syracuseStep 1251875 = 1877813) B1877813
theorem B1874609 : Blo 491791 1874609 := bstep (se 2 (by rfl) ⟨702978, by rfl⟩ : syracuseStep 1874609 = 1405957) B1405957
theorem B2497229 : Blo 491791 2497229 := bstep (se 3 (by rfl) ⟨468230, by rfl⟩ : syracuseStep 2497229 = 936461) B936461
theorem B793331 : Blo 491791 793331 := bstep (se 1 (by rfl) ⟨594998, by rfl⟩ : syracuseStep 793331 = 1189997) B1189997
theorem B1055587 : Blo 491791 1055587 := bstep (se 1 (by rfl) ⟨791690, by rfl⟩ : syracuseStep 1055587 = 1583381) B1583381
theorem B793523 : Blo 491791 793523 := bstep (se 1 (by rfl) ⟨595142, by rfl⟩ : syracuseStep 793523 = 1190285) B1190285
theorem B793651 : Blo 491791 793651 := bstep (se 1 (by rfl) ⟨595238, by rfl⟩ : syracuseStep 793651 = 1190477) B1190477
theorem B1055843 : Blo 491791 1055843 := bstep (se 1 (by rfl) ⟨791882, by rfl⟩ : syracuseStep 1055843 = 1583765) B1583765
theorem B1187075 : Blo 491791 1187075 := bstep (se 1 (by rfl) ⟨890306, by rfl⟩ : syracuseStep 1187075 = 1780613) B1780613
theorem B1580305 : Blo 491791 1580305 := bstep (se 2 (by rfl) ⟨592614, by rfl⟩ : syracuseStep 1580305 = 1185229) B1185229
theorem B5086577 : Blo 491791 5086577 := bstep (se 2 (by rfl) ⟨1907466, by rfl⟩ : syracuseStep 5086577 = 3814933) B3814933
theorem B1252817 : Blo 491791 1252817 := bstep (se 2 (by rfl) ⟨469806, by rfl⟩ : syracuseStep 1252817 = 939613) B939613
theorem B1252867 : Blo 491791 1252867 := bstep (se 1 (by rfl) ⟨939650, by rfl⟩ : syracuseStep 1252867 = 1879301) B1879301
theorem B2104973 : Blo 491791 2104973 := bstep (se 3 (by rfl) ⟨394682, by rfl⟩ : syracuseStep 2104973 = 789365) B789365
theorem B5643917 : Blo 491791 5643917 := bstep (se 3 (by rfl) ⟨1058234, by rfl⟩ : syracuseStep 5643917 = 2116469) B2116469
theorem B1253009 : Blo 491791 1253009 := bstep (se 2 (by rfl) ⟨469878, by rfl⟩ : syracuseStep 1253009 = 939757) B939757
theorem B1449677 : Blo 491791 1449677 := bstep (se 3 (by rfl) ⟨271814, by rfl⟩ : syracuseStep 1449677 = 543629) B543629
theorem B1777571 : Blo 491791 1777571 := bstep (se 1 (by rfl) ⟨1333178, by rfl⟩ : syracuseStep 1777571 = 2666357) B2666357
theorem B1056817 : Blo 491791 1056817 := bstep (se 2 (by rfl) ⟨396306, by rfl⟩ : syracuseStep 1056817 = 792613) B792613
theorem B1187921 : Blo 491791 1187921 := bstep (se 2 (by rfl) ⟨445470, by rfl⟩ : syracuseStep 1187921 = 890941) B890941
theorem B1876067 : Blo 491791 1876067 := bstep (se 1 (by rfl) ⟨1407050, by rfl⟩ : syracuseStep 1876067 = 2814101) B2814101
theorem B1876081 : Blo 491791 1876081 := bstep (se 2 (by rfl) ⟨703530, by rfl⟩ : syracuseStep 1876081 = 1407061) B1407061
theorem B1188017 : Blo 491791 1188017 := bstep (se 2 (by rfl) ⟨445506, by rfl⟩ : syracuseStep 1188017 = 891013) B891013
theorem B2466289 : Blo 491791 2466289 := bstep (se 2 (by rfl) ⟨924858, by rfl⟩ : syracuseStep 2466289 = 1849717) B1849717
theorem B1254001 : Blo 491791 1254001 := bstep (se 2 (by rfl) ⟨470250, by rfl⟩ : syracuseStep 1254001 = 940501) B940501
theorem B1057475 : Blo 491791 1057475 := bstep (se 1 (by rfl) ⟨793106, by rfl⟩ : syracuseStep 1057475 = 1586213) B1586213
theorem B631523 : Blo 491791 631523 := bstep (se 1 (by rfl) ⟨473642, by rfl⟩ : syracuseStep 631523 = 947285) B947285
theorem B1581869 : Blo 491791 1581869 := bstep (se 3 (by rfl) ⟨296600, by rfl⟩ : syracuseStep 1581869 = 593201) B593201
theorem B8528753 : Blo 491791 8528753 := bstep (se 2 (by rfl) ⟨3198282, by rfl⟩ : syracuseStep 8528753 = 6396565) B6396565
theorem B1254275 : Blo 491791 1254275 := bstep (se 1 (by rfl) ⟨940706, by rfl⟩ : syracuseStep 1254275 = 1881413) B1881413
theorem B500627 : Blo 491791 500627 := bstep (se 1 (by rfl) ⟨375470, by rfl⟩ : syracuseStep 500627 = 750941) B750941
theorem B1254467 : Blo 491791 1254467 := bstep (se 1 (by rfl) ⟨940850, by rfl⟩ : syracuseStep 1254467 = 1881701) B1881701
theorem B3155021 : Blo 491791 3155021 := bstep (se 3 (by rfl) ⟨591566, by rfl⟩ : syracuseStep 3155021 = 1183133) B1183133
theorem B665059 : Blo 491791 665059 := bstep (se 1 (by rfl) ⟨498794, by rfl⟩ : syracuseStep 665059 = 997589) B997589
theorem B1189361 : Blo 491791 1189361 := bstep (se 2 (by rfl) ⟨446010, by rfl⟩ : syracuseStep 1189361 = 892021) B892021
theorem B1779185 : Blo 491791 1779185 := bstep (se 2 (by rfl) ⟨667194, by rfl⟩ : syracuseStep 1779185 = 1334389) B1334389
theorem B1058321 : Blo 491791 1058321 := bstep (se 2 (by rfl) ⟨396870, by rfl⟩ : syracuseStep 1058321 = 793741) B793741
theorem B1877539 : Blo 491791 1877539 := bstep (se 1 (by rfl) ⟨1408154, by rfl⟩ : syracuseStep 1877539 = 2816309) B2816309
theorem B2500145 : Blo 491791 2500145 := bstep (se 2 (by rfl) ⟨937554, by rfl⟩ : syracuseStep 2500145 = 1875109) B1875109
theorem B1779313 : Blo 491791 1779313 := bstep (se 2 (by rfl) ⟨667242, by rfl⟩ : syracuseStep 1779313 = 1334485) B1334485
theorem B4728689 : Blo 491791 4728689 := bstep (se 2 (by rfl) ⟨1773258, by rfl⟩ : syracuseStep 4728689 = 3546517) B3546517
theorem B501859 : Blo 491791 501859 := bstep (se 1 (by rfl) ⟨376394, by rfl⟩ : syracuseStep 501859 = 752789) B752789
theorem B6334645 : Blo 491791 6334645 := bstep (se 5 (by rfl) ⟨296936, by rfl⟩ : syracuseStep 6334645 = 593873) B593873
theorem B600419 : Blo 491791 600419 := bstep (se 1 (by rfl) ⟨450314, by rfl⟩ : syracuseStep 600419 = 900629) B900629
theorem B5646833 : Blo 491791 5646833 := bstep (se 2 (by rfl) ⟨2117562, by rfl⟩ : syracuseStep 5646833 = 4235125) B4235125
theorem B829939 : Blo 491791 829939 := bstep (se 1 (by rfl) ⟨622454, by rfl⟩ : syracuseStep 829939 = 1244909) B1244909
theorem B1583651 : Blo 491791 1583651 := bstep (se 1 (by rfl) ⟨1187738, by rfl⟩ : syracuseStep 1583651 = 2375477) B2375477
theorem B830081 : Blo 491791 830081 := bstep (se 2 (by rfl) ⟨311280, by rfl⟩ : syracuseStep 830081 = 622561) B622561
theorem B830209 : Blo 491791 830209 := bstep (se 2 (by rfl) ⟨311328, by rfl⟩ : syracuseStep 830209 = 622657) B622657
theorem B3746573 : Blo 491791 3746573 := bstep (se 3 (by rfl) ⟨702482, by rfl⟩ : syracuseStep 3746573 = 1404965) B1404965
theorem B830243 : Blo 491791 830243 := bstep (se 1 (by rfl) ⟨622682, by rfl⟩ : syracuseStep 830243 = 1245365) B1245365
theorem B6007621 : Blo 491791 6007621 := bstep (se 4 (by rfl) ⟨563214, by rfl⟩ : syracuseStep 6007621 = 1126429) B1126429
theorem B830371 : Blo 491791 830371 := bstep (se 1 (by rfl) ⟨622778, by rfl⟩ : syracuseStep 830371 = 1245557) B1245557
theorem B2501603 : Blo 491791 2501603 := bstep (se 1 (by rfl) ⟨1876202, by rfl⟩ : syracuseStep 2501603 = 3752405) B3752405
theorem B1354733 : Blo 491791 1354733 := bstep (se 3 (by rfl) ⟨254012, by rfl⟩ : syracuseStep 1354733 = 508025) B508025
theorem B830513 : Blo 491791 830513 := bstep (se 2 (by rfl) ⟨311442, by rfl⟩ : syracuseStep 830513 = 622885) B622885
theorem B2010161 : Blo 491791 2010161 := bstep (se 2 (by rfl) ⟨753810, by rfl⟩ : syracuseStep 2010161 = 1507621) B1507621
theorem B3550321 : Blo 491791 3550321 := bstep (se 2 (by rfl) ⟨1331370, by rfl⟩ : syracuseStep 3550321 = 2662741) B2662741
theorem B5057677 : Blo 491791 5057677 := bstep (se 3 (by rfl) ⟨948314, by rfl⟩ : syracuseStep 5057677 = 1896629) B1896629
theorem B830641 : Blo 491791 830641 := bstep (se 2 (by rfl) ⟨311490, by rfl⟩ : syracuseStep 830641 = 622981) B622981
theorem B830675 : Blo 491791 830675 := bstep (se 1 (by rfl) ⟨623006, by rfl⟩ : syracuseStep 830675 = 1246013) B1246013
theorem B1420525 : Blo 491791 1420525 := bstep (se 3 (by rfl) ⟨266348, by rfl⟩ : syracuseStep 1420525 = 532697) B532697
theorem B1420625 : Blo 491791 1420625 := bstep (se 2 (by rfl) ⟨532734, by rfl⟩ : syracuseStep 1420625 = 1065469) B1065469
theorem B830803 : Blo 491791 830803 := bstep (se 1 (by rfl) ⟨623102, by rfl⟩ : syracuseStep 830803 = 1246205) B1246205
theorem B1125827 : Blo 491791 1125827 := bstep (se 1 (by rfl) ⟨844370, by rfl⟩ : syracuseStep 1125827 = 1688741) B1688741
theorem B830945 : Blo 491791 830945 := bstep (se 2 (by rfl) ⟨311604, by rfl⟩ : syracuseStep 830945 = 623209) B623209
theorem B1781261 : Blo 491791 1781261 := bstep (se 3 (by rfl) ⟨333986, by rfl⟩ : syracuseStep 1781261 = 667973) B667973
theorem B831073 : Blo 491791 831073 := bstep (se 2 (by rfl) ⟨311652, by rfl⟩ : syracuseStep 831073 = 623305) B623305
theorem B831107 : Blo 491791 831107 := bstep (se 1 (by rfl) ⟨623330, by rfl⟩ : syracuseStep 831107 = 1246661) B1246661
theorem B1781389 : Blo 491791 1781389 := bstep (se 3 (by rfl) ⟨334010, by rfl⟩ : syracuseStep 1781389 = 668021) B668021
theorem B667297 : Blo 491791 667297 := bstep (se 2 (by rfl) ⟨250236, by rfl⟩ : syracuseStep 667297 = 500473) B500473
theorem B1879757 : Blo 491791 1879757 := bstep (se 3 (by rfl) ⟨352454, by rfl⟩ : syracuseStep 1879757 = 704909) B704909
theorem B831235 : Blo 491791 831235 := bstep (se 1 (by rfl) ⟨623426, by rfl⟩ : syracuseStep 831235 = 1246853) B1246853
theorem B2502413 : Blo 491791 2502413 := bstep (se 3 (by rfl) ⟨469202, by rfl⟩ : syracuseStep 2502413 = 938405) B938405
theorem B2535245 : Blo 491791 2535245 := bstep (se 3 (by rfl) ⟨475358, by rfl⟩ : syracuseStep 2535245 = 950717) B950717
theorem B700273 : Blo 491791 700273 := bstep (se 2 (by rfl) ⟨262602, by rfl⟩ : syracuseStep 700273 = 525205) B525205
theorem B831377 : Blo 491791 831377 := bstep (se 2 (by rfl) ⟨311766, by rfl⟩ : syracuseStep 831377 = 623533) B623533
theorem B2109347 : Blo 491791 2109347 := bstep (se 1 (by rfl) ⟨1582010, by rfl⟩ : syracuseStep 2109347 = 3164021) B3164021
theorem B1421297 : Blo 491791 1421297 := bstep (se 2 (by rfl) ⟨532986, by rfl⟩ : syracuseStep 1421297 = 1065973) B1065973
theorem B831505 : Blo 491791 831505 := bstep (se 2 (by rfl) ⟨311814, by rfl⟩ : syracuseStep 831505 = 623629) B623629
theorem B831539 : Blo 491791 831539 := bstep (se 1 (by rfl) ⟨623654, by rfl⟩ : syracuseStep 831539 = 1247309) B1247309
theorem B3158149 : Blo 491791 3158149 := bstep (se 4 (by rfl) ⟨296076, by rfl⟩ : syracuseStep 3158149 = 592153) B592153
theorem B831667 : Blo 491791 831667 := bstep (se 1 (by rfl) ⟨623750, by rfl⟩ : syracuseStep 831667 = 1247501) B1247501
theorem B4731149 : Blo 491791 4731149 := bstep (se 3 (by rfl) ⟨887090, by rfl⟩ : syracuseStep 4731149 = 1774181) B1774181
theorem B1585457 : Blo 491791 1585457 := bstep (se 2 (by rfl) ⟨594546, by rfl⟩ : syracuseStep 1585457 = 1189093) B1189093
theorem B831809 : Blo 491791 831809 := bstep (se 2 (by rfl) ⟨311928, by rfl⟩ : syracuseStep 831809 = 623857) B623857
theorem B1585507 : Blo 491791 1585507 := bstep (se 1 (by rfl) ⟨1189130, by rfl⟩ : syracuseStep 1585507 = 2378261) B2378261
theorem B2666893 : Blo 491791 2666893 := bstep (se 3 (by rfl) ⟨500042, by rfl⟩ : syracuseStep 2666893 = 1000085) B1000085
theorem B831937 : Blo 491791 831937 := bstep (se 2 (by rfl) ⟨311976, by rfl⟩ : syracuseStep 831937 = 623953) B623953
theorem B831971 : Blo 491791 831971 := bstep (se 1 (by rfl) ⟨623978, by rfl⟩ : syracuseStep 831971 = 1247957) B1247957
theorem B700979 : Blo 491791 700979 := bstep (se 1 (by rfl) ⟨525734, by rfl⟩ : syracuseStep 700979 = 1051469) B1051469
theorem B832099 : Blo 491791 832099 := bstep (se 1 (by rfl) ⟨624074, by rfl⟩ : syracuseStep 832099 = 1248149) B1248149
theorem B832241 : Blo 491791 832241 := bstep (se 2 (by rfl) ⟨312090, by rfl⟩ : syracuseStep 832241 = 624181) B624181
theorem B668497 : Blo 491791 668497 := bstep (se 2 (by rfl) ⟨250686, by rfl⟩ : syracuseStep 668497 = 501373) B501373
theorem B832369 : Blo 491791 832369 := bstep (se 2 (by rfl) ⟨312138, by rfl⟩ : syracuseStep 832369 = 624277) B624277
theorem B832403 : Blo 491791 832403 := bstep (se 1 (by rfl) ⟨624302, by rfl⟩ : syracuseStep 832403 = 1248605) B1248605
theorem B832531 : Blo 491791 832531 := bstep (se 1 (by rfl) ⟨624398, by rfl⟩ : syracuseStep 832531 = 1248797) B1248797
theorem B1586225 : Blo 491791 1586225 := bstep (se 2 (by rfl) ⟨594834, by rfl⟩ : syracuseStep 1586225 = 1189669) B1189669
theorem B832673 : Blo 491791 832673 := bstep (se 2 (by rfl) ⟨312252, by rfl⟩ : syracuseStep 832673 = 624505) B624505
theorem B1782947 : Blo 491791 1782947 := bstep (se 1 (by rfl) ⟨1337210, by rfl⟩ : syracuseStep 1782947 = 2674421) B2674421
theorem B701617 : Blo 491791 701617 := bstep (se 2 (by rfl) ⟨263106, by rfl⟩ : syracuseStep 701617 = 526213) B526213
theorem B2667761 : Blo 491791 2667761 := bstep (se 2 (by rfl) ⟨1000410, by rfl⟩ : syracuseStep 2667761 = 2000821) B2000821
theorem B832801 : Blo 491791 832801 := bstep (se 2 (by rfl) ⟨312300, by rfl⟩ : syracuseStep 832801 = 624601) B624601
theorem B701731 : Blo 491791 701731 := bstep (se 1 (by rfl) ⟨526298, by rfl⟩ : syracuseStep 701731 = 1052597) B1052597
theorem B832835 : Blo 491791 832835 := bstep (se 1 (by rfl) ⟨624626, by rfl⟩ : syracuseStep 832835 = 1249253) B1249253
theorem B1684909 : Blo 491791 1684909 := bstep (se 3 (by rfl) ⟨315920, by rfl⟩ : syracuseStep 1684909 = 631841) B631841
theorem B832963 : Blo 491791 832963 := bstep (se 1 (by rfl) ⟨624722, by rfl⟩ : syracuseStep 832963 = 1249445) B1249445
theorem B1586737 : Blo 491791 1586737 := bstep (se 2 (by rfl) ⟨595026, by rfl⟩ : syracuseStep 1586737 = 1190053) B1190053
theorem B833105 : Blo 491791 833105 := bstep (se 2 (by rfl) ⟨312414, by rfl⟩ : syracuseStep 833105 = 624829) B624829
theorem B3749489 : Blo 491791 3749489 := bstep (se 2 (by rfl) ⟨1406058, by rfl⟩ : syracuseStep 3749489 = 2812117) B2812117
theorem B800401 : Blo 491791 800401 := bstep (se 2 (by rfl) ⟨300150, by rfl⟩ : syracuseStep 800401 = 600301) B600301
theorem B833233 : Blo 491791 833233 := bstep (se 2 (by rfl) ⟨312462, by rfl⟩ : syracuseStep 833233 = 624925) B624925
theorem B833267 : Blo 491791 833267 := bstep (se 1 (by rfl) ⟨624950, by rfl⟩ : syracuseStep 833267 = 1249901) B1249901
theorem B669427 : Blo 491791 669427 := bstep (se 1 (by rfl) ⟨502070, by rfl⟩ : syracuseStep 669427 = 1004141) B1004141
theorem B2406179 : Blo 491791 2406179 := bstep (se 1 (by rfl) ⟨1804634, by rfl⟩ : syracuseStep 2406179 = 3609269) B3609269
theorem B2111345 : Blo 491791 2111345 := bstep (se 2 (by rfl) ⟨791754, by rfl⟩ : syracuseStep 2111345 = 1583509) B1583509
theorem B833395 : Blo 491791 833395 := bstep (se 1 (by rfl) ⟨625046, by rfl⟩ : syracuseStep 833395 = 1250093) B1250093
theorem B1128401 : Blo 491791 1128401 := bstep (se 2 (by rfl) ⟨423150, by rfl⟩ : syracuseStep 1128401 = 846301) B846301
theorem B997361 : Blo 491791 997361 := bstep (se 2 (by rfl) ⟨374010, by rfl⟩ : syracuseStep 997361 = 748021) B748021
theorem B833537 : Blo 491791 833537 := bstep (se 2 (by rfl) ⟨312576, by rfl⟩ : syracuseStep 833537 = 625153) B625153
theorem B833665 : Blo 491791 833665 := bstep (se 2 (by rfl) ⟨312624, by rfl⟩ : syracuseStep 833665 = 625249) B625249
theorem B1128593 : Blo 491791 1128593 := bstep (se 2 (by rfl) ⟨423222, by rfl⟩ : syracuseStep 1128593 = 846445) B846445
theorem B833699 : Blo 491791 833699 := bstep (se 1 (by rfl) ⟨625274, by rfl⟩ : syracuseStep 833699 = 1250549) B1250549
theorem B4208881 : Blo 491791 4208881 := bstep (se 2 (by rfl) ⟨1578330, by rfl⟩ : syracuseStep 4208881 = 3156661) B3156661
theorem B833827 : Blo 491791 833827 := bstep (se 1 (by rfl) ⟨625370, by rfl⟩ : syracuseStep 833827 = 1250741) B1250741
theorem B833969 : Blo 491791 833969 := bstep (se 2 (by rfl) ⟨312738, by rfl⟩ : syracuseStep 833969 = 625477) B625477
theorem B834097 : Blo 491791 834097 := bstep (se 2 (by rfl) ⟨312786, by rfl⟩ : syracuseStep 834097 = 625573) B625573
theorem B834131 : Blo 491791 834131 := bstep (se 1 (by rfl) ⟨625598, by rfl⟩ : syracuseStep 834131 = 1251197) B1251197
theorem B703075 : Blo 491791 703075 := bstep (se 1 (by rfl) ⟨527306, by rfl⟩ : syracuseStep 703075 = 1054613) B1054613
theorem B2505329 : Blo 491791 2505329 := bstep (se 2 (by rfl) ⟨939498, by rfl⟩ : syracuseStep 2505329 = 1878997) B1878997
theorem B1587853 : Blo 491791 1587853 := bstep (se 3 (by rfl) ⟨297722, by rfl⟩ : syracuseStep 1587853 = 595445) B595445
theorem B1587917 : Blo 491791 1587917 := bstep (se 3 (by rfl) ⟨297734, by rfl⟩ : syracuseStep 1587917 = 595469) B595469
theorem B506579 : Blo 491791 506579 := bstep (se 1 (by rfl) ⟨379934, by rfl⟩ : syracuseStep 506579 = 759869) B759869
theorem B834259 : Blo 491791 834259 := bstep (se 1 (by rfl) ⟨625694, by rfl⟩ : syracuseStep 834259 = 1251389) B1251389
theorem B834401 : Blo 491791 834401 := bstep (se 2 (by rfl) ⟨312900, by rfl⟩ : syracuseStep 834401 = 625801) B625801
theorem B834529 : Blo 491791 834529 := bstep (se 2 (by rfl) ⟨312948, by rfl⟩ : syracuseStep 834529 = 625897) B625897
theorem B4013027 : Blo 491791 4013027 := bstep (se 1 (by rfl) ⟨3009770, by rfl⟩ : syracuseStep 4013027 = 6019541) B6019541
theorem B834563 : Blo 491791 834563 := bstep (se 1 (by rfl) ⟨625922, by rfl⟩ : syracuseStep 834563 = 1251845) B1251845
theorem B1129475 : Blo 491791 1129475 := bstep (se 1 (by rfl) ⟨847106, by rfl⟩ : syracuseStep 1129475 = 1694213) B1694213
theorem B834691 : Blo 491791 834691 := bstep (se 1 (by rfl) ⟨626018, by rfl⟩ : syracuseStep 834691 = 1252037) B1252037
theorem B834833 : Blo 491791 834833 := bstep (se 2 (by rfl) ⟨313062, by rfl⟩ : syracuseStep 834833 = 626125) B626125
theorem B834961 : Blo 491791 834961 := bstep (se 2 (by rfl) ⟨313110, by rfl⟩ : syracuseStep 834961 = 626221) B626221
theorem B834995 : Blo 491791 834995 := bstep (se 1 (by rfl) ⟨626246, by rfl⟩ : syracuseStep 834995 = 1252493) B1252493
theorem B2113037 : Blo 491791 2113037 := bstep (se 3 (by rfl) ⟨396194, by rfl⟩ : syracuseStep 2113037 = 792389) B792389
theorem B835123 : Blo 491791 835123 := bstep (se 1 (by rfl) ⟨626342, by rfl⟩ : syracuseStep 835123 = 1252685) B1252685
theorem B835265 : Blo 491791 835265 := bstep (se 2 (by rfl) ⟨313224, by rfl⟩ : syracuseStep 835265 = 626449) B626449
theorem B8437445 : Blo 491791 8437445 := bstep (se 4 (by rfl) ⟨791010, by rfl⟩ : syracuseStep 8437445 = 1582021) B1582021
theorem B704209 : Blo 491791 704209 := bstep (se 2 (by rfl) ⟨264078, by rfl⟩ : syracuseStep 704209 = 528157) B528157
theorem B704305 : Blo 491791 704305 := bstep (se 2 (by rfl) ⟨264114, by rfl⟩ : syracuseStep 704305 = 528229) B528229
theorem B835393 : Blo 491791 835393 := bstep (se 2 (by rfl) ⟨313272, by rfl⟩ : syracuseStep 835393 = 626545) B626545
theorem B835427 : Blo 491791 835427 := bstep (se 1 (by rfl) ⟨626570, by rfl⟩ : syracuseStep 835427 = 1253141) B1253141
theorem B835555 : Blo 491791 835555 := bstep (se 1 (by rfl) ⟨626666, by rfl⟩ : syracuseStep 835555 = 1253333) B1253333
theorem B2506787 : Blo 491791 2506787 := bstep (se 1 (by rfl) ⟨1880090, by rfl⟩ : syracuseStep 2506787 = 3760181) B3760181
theorem B934001 : Blo 491791 934001 := bstep (se 2 (by rfl) ⟨350250, by rfl⟩ : syracuseStep 934001 = 700501) B700501
theorem B835697 : Blo 491791 835697 := bstep (se 2 (by rfl) ⟨313386, by rfl⟩ : syracuseStep 835697 = 626773) B626773
theorem B8110307 : Blo 491791 8110307 := bstep (se 1 (by rfl) ⟨6082730, by rfl⟩ : syracuseStep 8110307 = 12165461) B12165461
theorem B835825 : Blo 491791 835825 := bstep (se 2 (by rfl) ⟨313434, by rfl⟩ : syracuseStep 835825 = 626869) B626869
theorem B835859 : Blo 491791 835859 := bstep (se 1 (by rfl) ⟨626894, by rfl⟩ : syracuseStep 835859 = 1253789) B1253789
theorem B704801 : Blo 491791 704801 := bstep (se 2 (by rfl) ⟨264300, by rfl⟩ : syracuseStep 704801 = 528601) B528601
theorem B835987 : Blo 491791 835987 := bstep (se 1 (by rfl) ⟨626990, by rfl⟩ : syracuseStep 835987 = 1253981) B1253981
theorem B737699 : Blo 491791 737699 := bstep (se 1 (by rfl) ⟨553274, by rfl⟩ : syracuseStep 737699 = 1106549) B1106549
theorem B737729 : Blo 491791 737729 := bstep (se 2 (by rfl) ⟨276648, by rfl⟩ : syracuseStep 737729 = 553297) B553297
theorem B737747 : Blo 491791 737747 := bstep (se 1 (by rfl) ⟨553310, by rfl⟩ : syracuseStep 737747 = 1106621) B1106621
theorem B737777 : Blo 491791 737777 := bstep (se 2 (by rfl) ⟨276666, by rfl⟩ : syracuseStep 737777 = 553333) B553333
theorem B737795 : Blo 491791 737795 := bstep (se 1 (by rfl) ⟨553346, by rfl⟩ : syracuseStep 737795 = 1106693) B1106693
theorem B737825 : Blo 491791 737825 := bstep (se 2 (by rfl) ⟨276684, by rfl⟩ : syracuseStep 737825 = 553369) B553369
theorem B836129 : Blo 491791 836129 := bstep (se 2 (by rfl) ⟨313548, by rfl⟩ : syracuseStep 836129 = 627097) B627097
theorem B737843 : Blo 491791 737843 := bstep (se 1 (by rfl) ⟨553382, by rfl⟩ : syracuseStep 737843 = 1106765) B1106765
theorem B737873 : Blo 491791 737873 := bstep (se 2 (by rfl) ⟨276702, by rfl⟩ : syracuseStep 737873 = 553405) B553405
theorem B737891 : Blo 491791 737891 := bstep (se 1 (by rfl) ⟨553418, by rfl⟩ : syracuseStep 737891 = 1106837) B1106837
theorem B803441 : Blo 491791 803441 := bstep (se 2 (by rfl) ⟨301290, by rfl⟩ : syracuseStep 803441 = 602581) B602581
theorem B737921 : Blo 491791 737921 := bstep (se 2 (by rfl) ⟨276720, by rfl⟩ : syracuseStep 737921 = 553441) B553441
theorem B737939 : Blo 491791 737939 := bstep (se 1 (by rfl) ⟨553454, by rfl⟩ : syracuseStep 737939 = 1106909) B1106909
theorem B836257 : Blo 491791 836257 := bstep (se 2 (by rfl) ⟨313596, by rfl⟩ : syracuseStep 836257 = 627193) B627193
theorem B737969 : Blo 491791 737969 := bstep (se 2 (by rfl) ⟨276738, by rfl⟩ : syracuseStep 737969 = 553477) B553477
theorem B737987 : Blo 491791 737987 := bstep (se 1 (by rfl) ⟨553490, by rfl⟩ : syracuseStep 737987 = 1106981) B1106981
theorem B836291 : Blo 491791 836291 := bstep (se 1 (by rfl) ⟨627218, by rfl⟩ : syracuseStep 836291 = 1254437) B1254437
theorem B738017 : Blo 491791 738017 := bstep (se 2 (by rfl) ⟨276756, by rfl⟩ : syracuseStep 738017 = 553513) B553513
theorem B738035 : Blo 491791 738035 := bstep (se 1 (by rfl) ⟨553526, by rfl⟩ : syracuseStep 738035 = 1107053) B1107053
theorem B2802437 : Blo 491791 2802437 := bstep (se 4 (by rfl) ⟨262728, by rfl⟩ : syracuseStep 2802437 = 525457) B525457
theorem B1786637 : Blo 491791 1786637 := bstep (se 3 (by rfl) ⟨334994, by rfl⟩ : syracuseStep 1786637 = 669989) B669989
theorem B738065 : Blo 491791 738065 := bstep (se 2 (by rfl) ⟨276774, by rfl⟩ : syracuseStep 738065 = 553549) B553549
theorem B738083 : Blo 491791 738083 := bstep (se 1 (by rfl) ⟨553562, by rfl⟩ : syracuseStep 738083 = 1107125) B1107125
theorem B738113 : Blo 491791 738113 := bstep (se 2 (by rfl) ⟨276792, by rfl⟩ : syracuseStep 738113 = 553585) B553585
theorem B836419 : Blo 491791 836419 := bstep (se 1 (by rfl) ⟨627314, by rfl⟩ : syracuseStep 836419 = 1254629) B1254629
theorem B2507597 : Blo 491791 2507597 := bstep (se 3 (by rfl) ⟨470174, by rfl⟩ : syracuseStep 2507597 = 940349) B940349
theorem B738131 : Blo 491791 738131 := bstep (se 1 (by rfl) ⟨553598, by rfl⟩ : syracuseStep 738131 = 1107197) B1107197
theorem B738161 : Blo 491791 738161 := bstep (se 2 (by rfl) ⟨276810, by rfl⟩ : syracuseStep 738161 = 553621) B553621
theorem B738179 : Blo 491791 738179 := bstep (se 1 (by rfl) ⟨553634, by rfl⟩ : syracuseStep 738179 = 1107269) B1107269
theorem B738209 : Blo 491791 738209 := bstep (se 2 (by rfl) ⟨276828, by rfl⟩ : syracuseStep 738209 = 553657) B553657
theorem B738227 : Blo 491791 738227 := bstep (se 1 (by rfl) ⟨553670, by rfl⟩ : syracuseStep 738227 = 1107341) B1107341
theorem B508867 : Blo 491791 508867 := bstep (se 1 (by rfl) ⟨381650, by rfl⟩ : syracuseStep 508867 = 763301) B763301
theorem B738257 : Blo 491791 738257 := bstep (se 2 (by rfl) ⟨276846, by rfl⟩ : syracuseStep 738257 = 553693) B553693
theorem B836561 : Blo 491791 836561 := bstep (se 2 (by rfl) ⟨313710, by rfl⟩ : syracuseStep 836561 = 627421) B627421
theorem B738275 : Blo 491791 738275 := bstep (se 1 (by rfl) ⟨553706, by rfl⟩ : syracuseStep 738275 = 1107413) B1107413
theorem B2999267 : Blo 491791 2999267 := bstep (se 1 (by rfl) ⟨2249450, by rfl⟩ : syracuseStep 2999267 = 4498901) B4498901
theorem B934897 : Blo 491791 934897 := bstep (se 2 (by rfl) ⟨350586, by rfl⟩ : syracuseStep 934897 = 701173) B701173
theorem B3163121 : Blo 491791 3163121 := bstep (se 2 (by rfl) ⟨1186170, by rfl⟩ : syracuseStep 3163121 = 2372341) B2372341
theorem B738305 : Blo 491791 738305 := bstep (se 2 (by rfl) ⟨276864, by rfl⟩ : syracuseStep 738305 = 553729) B553729
theorem B738323 : Blo 491791 738323 := bstep (se 1 (by rfl) ⟨553742, by rfl⟩ : syracuseStep 738323 = 1107485) B1107485
theorem B738353 : Blo 491791 738353 := bstep (se 2 (by rfl) ⟨276882, by rfl⟩ : syracuseStep 738353 = 553765) B553765
theorem B738371 : Blo 491791 738371 := bstep (se 1 (by rfl) ⟨553778, by rfl⟩ : syracuseStep 738371 = 1107557) B1107557
theorem B738401 : Blo 491791 738401 := bstep (se 2 (by rfl) ⟨276900, by rfl⟩ : syracuseStep 738401 = 553801) B553801
theorem B738419 : Blo 491791 738419 := bstep (se 1 (by rfl) ⟨553814, by rfl⟩ : syracuseStep 738419 = 1107629) B1107629
theorem B705667 : Blo 491791 705667 := bstep (se 1 (by rfl) ⟨529250, by rfl⟩ : syracuseStep 705667 = 1058501) B1058501
theorem B738449 : Blo 491791 738449 := bstep (se 2 (by rfl) ⟨276918, by rfl⟩ : syracuseStep 738449 = 553837) B553837
theorem B935057 : Blo 491791 935057 := bstep (se 2 (by rfl) ⟨350646, by rfl⟩ : syracuseStep 935057 = 701293) B701293
theorem B738467 : Blo 491791 738467 := bstep (se 1 (by rfl) ⟨553850, by rfl⟩ : syracuseStep 738467 = 1107701) B1107701
theorem B738497 : Blo 491791 738497 := bstep (se 2 (by rfl) ⟨276936, by rfl⟩ : syracuseStep 738497 = 553873) B553873
theorem B738515 : Blo 491791 738515 := bstep (se 1 (by rfl) ⟨553886, by rfl⟩ : syracuseStep 738515 = 1107773) B1107773
theorem B705763 : Blo 491791 705763 := bstep (se 1 (by rfl) ⟨529322, by rfl⟩ : syracuseStep 705763 = 1058645) B1058645
theorem B738545 : Blo 491791 738545 := bstep (se 2 (by rfl) ⟨276954, by rfl⟩ : syracuseStep 738545 = 553909) B553909
theorem B738563 : Blo 491791 738563 := bstep (se 1 (by rfl) ⟨553922, by rfl⟩ : syracuseStep 738563 = 1107845) B1107845
theorem B738593 : Blo 491791 738593 := bstep (se 2 (by rfl) ⟨276972, by rfl⟩ : syracuseStep 738593 = 553945) B553945
theorem B738611 : Blo 491791 738611 := bstep (se 1 (by rfl) ⟨553958, by rfl⟩ : syracuseStep 738611 = 1107917) B1107917
theorem B738641 : Blo 491791 738641 := bstep (se 2 (by rfl) ⟨276990, by rfl⟩ : syracuseStep 738641 = 553981) B553981
theorem B738659 : Blo 491791 738659 := bstep (se 1 (by rfl) ⟨553994, by rfl⟩ : syracuseStep 738659 = 1107989) B1107989
theorem B738689 : Blo 491791 738689 := bstep (se 2 (by rfl) ⟨277008, by rfl⟩ : syracuseStep 738689 = 554017) B554017
theorem B738707 : Blo 491791 738707 := bstep (se 1 (by rfl) ⟨554030, by rfl⟩ : syracuseStep 738707 = 1108061) B1108061
theorem B738737 : Blo 491791 738737 := bstep (se 2 (by rfl) ⟨277026, by rfl⟩ : syracuseStep 738737 = 554053) B554053
theorem B738755 : Blo 491791 738755 := bstep (se 1 (by rfl) ⟨554066, by rfl⟩ : syracuseStep 738755 = 1108133) B1108133
theorem B738785 : Blo 491791 738785 := bstep (se 2 (by rfl) ⟨277044, by rfl⟩ : syracuseStep 738785 = 554089) B554089
theorem B738803 : Blo 491791 738803 := bstep (se 1 (by rfl) ⟨554102, by rfl⟩ : syracuseStep 738803 = 1108205) B1108205
theorem B1263107 : Blo 491791 1263107 := bstep (se 1 (by rfl) ⟨947330, by rfl⟩ : syracuseStep 1263107 = 1894661) B1894661
theorem B738833 : Blo 491791 738833 := bstep (se 2 (by rfl) ⟨277062, by rfl⟩ : syracuseStep 738833 = 554125) B554125
theorem B738851 : Blo 491791 738851 := bstep (se 1 (by rfl) ⟨554138, by rfl⟩ : syracuseStep 738851 = 1108277) B1108277
theorem B935459 : Blo 491791 935459 := bstep (se 1 (by rfl) ⟨701594, by rfl⟩ : syracuseStep 935459 = 1403189) B1403189
theorem B738881 : Blo 491791 738881 := bstep (se 2 (by rfl) ⟨277080, by rfl⟩ : syracuseStep 738881 = 554161) B554161
theorem B738899 : Blo 491791 738899 := bstep (se 1 (by rfl) ⟨554174, by rfl⟩ : syracuseStep 738899 = 1108349) B1108349
theorem B804449 : Blo 491791 804449 := bstep (se 2 (by rfl) ⟨301668, by rfl⟩ : syracuseStep 804449 = 603337) B603337
theorem B738929 : Blo 491791 738929 := bstep (se 2 (by rfl) ⟨277098, by rfl⟩ : syracuseStep 738929 = 554197) B554197
theorem B738947 : Blo 491791 738947 := bstep (se 1 (by rfl) ⟨554210, by rfl⟩ : syracuseStep 738947 = 1108421) B1108421
theorem B738977 : Blo 491791 738977 := bstep (se 2 (by rfl) ⟨277116, by rfl⟩ : syracuseStep 738977 = 554233) B554233
theorem B738995 : Blo 491791 738995 := bstep (se 1 (by rfl) ⟨554246, by rfl⟩ : syracuseStep 738995 = 1108493) B1108493
theorem B739025 : Blo 491791 739025 := bstep (se 2 (by rfl) ⟨277134, by rfl⟩ : syracuseStep 739025 = 554269) B554269
theorem B739043 : Blo 491791 739043 := bstep (se 1 (by rfl) ⟨554282, by rfl⟩ : syracuseStep 739043 = 1108565) B1108565
theorem B739073 : Blo 491791 739073 := bstep (se 2 (by rfl) ⟨277152, by rfl⟩ : syracuseStep 739073 = 554305) B554305
theorem B739091 : Blo 491791 739091 := bstep (se 1 (by rfl) ⟨554318, by rfl⟩ : syracuseStep 739091 = 1108637) B1108637
theorem B739121 : Blo 491791 739121 := bstep (se 2 (by rfl) ⟨277170, by rfl⟩ : syracuseStep 739121 = 554341) B554341
theorem B739139 : Blo 491791 739139 := bstep (se 1 (by rfl) ⟨554354, by rfl⟩ : syracuseStep 739139 = 1108709) B1108709
theorem B739169 : Blo 491791 739169 := bstep (se 2 (by rfl) ⟨277188, by rfl⟩ : syracuseStep 739169 = 554377) B554377
theorem B739187 : Blo 491791 739187 := bstep (se 1 (by rfl) ⟨554390, by rfl⟩ : syracuseStep 739187 = 1108781) B1108781
theorem B739217 : Blo 491791 739217 := bstep (se 2 (by rfl) ⟨277206, by rfl⟩ : syracuseStep 739217 = 554413) B554413
theorem B739235 : Blo 491791 739235 := bstep (se 1 (by rfl) ⟨554426, by rfl⟩ : syracuseStep 739235 = 1108853) B1108853
theorem B739265 : Blo 491791 739265 := bstep (se 2 (by rfl) ⟨277224, by rfl⟩ : syracuseStep 739265 = 554449) B554449
theorem B739283 : Blo 491791 739283 := bstep (se 1 (by rfl) ⟨554462, by rfl⟩ : syracuseStep 739283 = 1108925) B1108925
theorem B739313 : Blo 491791 739313 := bstep (se 2 (by rfl) ⟨277242, by rfl⟩ : syracuseStep 739313 = 554485) B554485
theorem B739331 : Blo 491791 739331 := bstep (se 1 (by rfl) ⟨554498, by rfl⟩ : syracuseStep 739331 = 1108997) B1108997
theorem B739361 : Blo 491791 739361 := bstep (se 2 (by rfl) ⟨277260, by rfl⟩ : syracuseStep 739361 = 554521) B554521
theorem B739379 : Blo 491791 739379 := bstep (se 1 (by rfl) ⟨554534, by rfl⟩ : syracuseStep 739379 = 1109069) B1109069
theorem B739409 : Blo 491791 739409 := bstep (se 2 (by rfl) ⟨277278, by rfl⟩ : syracuseStep 739409 = 554557) B554557
theorem B739427 : Blo 491791 739427 := bstep (se 1 (by rfl) ⟨554570, by rfl⟩ : syracuseStep 739427 = 1109141) B1109141
theorem B739457 : Blo 491791 739457 := bstep (se 2 (by rfl) ⟨277296, by rfl⟩ : syracuseStep 739457 = 554593) B554593
theorem B739475 : Blo 491791 739475 := bstep (se 1 (by rfl) ⟨554606, by rfl⟩ : syracuseStep 739475 = 1109213) B1109213
theorem B739505 : Blo 491791 739505 := bstep (se 2 (by rfl) ⟨277314, by rfl⟩ : syracuseStep 739505 = 554629) B554629
theorem B739523 : Blo 491791 739523 := bstep (se 1 (by rfl) ⟨554642, by rfl⟩ : syracuseStep 739523 = 1109285) B1109285
theorem B739553 : Blo 491791 739553 := bstep (se 2 (by rfl) ⟨277332, by rfl⟩ : syracuseStep 739553 = 554665) B554665
theorem B739571 : Blo 491791 739571 := bstep (se 1 (by rfl) ⟨554678, by rfl⟩ : syracuseStep 739571 = 1109357) B1109357
theorem B739601 : Blo 491791 739601 := bstep (se 2 (by rfl) ⟨277350, by rfl⟩ : syracuseStep 739601 = 554701) B554701
theorem B608531 : Blo 491791 608531 := bstep (se 1 (by rfl) ⟨456398, by rfl⟩ : syracuseStep 608531 = 912797) B912797
theorem B739619 : Blo 491791 739619 := bstep (se 1 (by rfl) ⟨554714, by rfl⟩ : syracuseStep 739619 = 1109429) B1109429
theorem B739649 : Blo 491791 739649 := bstep (se 2 (by rfl) ⟨277368, by rfl⟩ : syracuseStep 739649 = 554737) B554737
theorem B739667 : Blo 491791 739667 := bstep (se 1 (by rfl) ⟨554750, by rfl⟩ : syracuseStep 739667 = 1109501) B1109501
theorem B739697 : Blo 491791 739697 := bstep (se 2 (by rfl) ⟨277386, by rfl⟩ : syracuseStep 739697 = 554773) B554773
theorem B739715 : Blo 491791 739715 := bstep (se 1 (by rfl) ⟨554786, by rfl⟩ : syracuseStep 739715 = 1109573) B1109573
theorem B739745 : Blo 491791 739745 := bstep (se 2 (by rfl) ⟨277404, by rfl⟩ : syracuseStep 739745 = 554809) B554809
theorem B936355 : Blo 491791 936355 := bstep (se 1 (by rfl) ⟨702266, by rfl⟩ : syracuseStep 936355 = 1404533) B1404533
theorem B739763 : Blo 491791 739763 := bstep (se 1 (by rfl) ⟨554822, by rfl⟩ : syracuseStep 739763 = 1109645) B1109645
theorem B739793 : Blo 491791 739793 := bstep (se 2 (by rfl) ⟨277422, by rfl⟩ : syracuseStep 739793 = 554845) B554845
theorem B739811 : Blo 491791 739811 := bstep (se 1 (by rfl) ⟨554858, by rfl⟩ : syracuseStep 739811 = 1109717) B1109717
theorem B739841 : Blo 491791 739841 := bstep (se 2 (by rfl) ⟨277440, by rfl⟩ : syracuseStep 739841 = 554881) B554881
theorem B739859 : Blo 491791 739859 := bstep (se 1 (by rfl) ⟨554894, by rfl⟩ : syracuseStep 739859 = 1109789) B1109789
theorem B739889 : Blo 491791 739889 := bstep (se 2 (by rfl) ⟨277458, by rfl⟩ : syracuseStep 739889 = 554917) B554917
theorem B739907 : Blo 491791 739907 := bstep (se 1 (by rfl) ⟨554930, by rfl⟩ : syracuseStep 739907 = 1109861) B1109861
theorem B936515 : Blo 491791 936515 := bstep (se 1 (by rfl) ⟨702386, by rfl⟩ : syracuseStep 936515 = 1404773) B1404773
theorem B739937 : Blo 491791 739937 := bstep (se 2 (by rfl) ⟨277476, by rfl⟩ : syracuseStep 739937 = 554953) B554953
theorem B739955 : Blo 491791 739955 := bstep (se 1 (by rfl) ⟨554966, by rfl⟩ : syracuseStep 739955 = 1109933) B1109933
theorem B739985 : Blo 491791 739985 := bstep (se 2 (by rfl) ⟨277494, by rfl⟩ : syracuseStep 739985 = 554989) B554989
theorem B740003 : Blo 491791 740003 := bstep (se 1 (by rfl) ⟨555002, by rfl⟩ : syracuseStep 740003 = 1110005) B1110005
theorem B1821361 : Blo 491791 1821361 := bstep (se 2 (by rfl) ⟨683010, by rfl⟩ : syracuseStep 1821361 = 1366021) B1366021
theorem B740033 : Blo 491791 740033 := bstep (se 2 (by rfl) ⟨277512, by rfl⟩ : syracuseStep 740033 = 555025) B555025
theorem B740051 : Blo 491791 740051 := bstep (se 1 (by rfl) ⟨555038, by rfl⟩ : syracuseStep 740051 = 1110077) B1110077
theorem B740081 : Blo 491791 740081 := bstep (se 2 (by rfl) ⟨277530, by rfl⟩ : syracuseStep 740081 = 555061) B555061
theorem B740099 : Blo 491791 740099 := bstep (se 1 (by rfl) ⟨555074, by rfl⟩ : syracuseStep 740099 = 1110149) B1110149
theorem B740129 : Blo 491791 740129 := bstep (se 2 (by rfl) ⟨277548, by rfl⟩ : syracuseStep 740129 = 555097) B555097
theorem B740147 : Blo 491791 740147 := bstep (se 1 (by rfl) ⟨555110, by rfl⟩ : syracuseStep 740147 = 1110221) B1110221
theorem B740177 : Blo 491791 740177 := bstep (se 2 (by rfl) ⟨277566, by rfl⟩ : syracuseStep 740177 = 555133) B555133
theorem B740195 : Blo 491791 740195 := bstep (se 1 (by rfl) ⟨555146, by rfl⟩ : syracuseStep 740195 = 1110293) B1110293
theorem B740225 : Blo 491791 740225 := bstep (se 2 (by rfl) ⟨277584, by rfl⟩ : syracuseStep 740225 = 555169) B555169
theorem B740243 : Blo 491791 740243 := bstep (se 1 (by rfl) ⟨555182, by rfl⟩ : syracuseStep 740243 = 1110365) B1110365
theorem B740273 : Blo 491791 740273 := bstep (se 2 (by rfl) ⟨277602, by rfl⟩ : syracuseStep 740273 = 555205) B555205
theorem B740291 : Blo 491791 740291 := bstep (se 1 (by rfl) ⟨555218, by rfl⟩ : syracuseStep 740291 = 1110437) B1110437
theorem B740321 : Blo 491791 740321 := bstep (se 2 (by rfl) ⟨277620, by rfl⟩ : syracuseStep 740321 = 555241) B555241
theorem B740339 : Blo 491791 740339 := bstep (se 1 (by rfl) ⟨555254, by rfl⟩ : syracuseStep 740339 = 1110509) B1110509
theorem B740369 : Blo 491791 740369 := bstep (se 2 (by rfl) ⟨277638, by rfl⟩ : syracuseStep 740369 = 555277) B555277
theorem B740387 : Blo 491791 740387 := bstep (se 1 (by rfl) ⟨555290, by rfl⟩ : syracuseStep 740387 = 1110581) B1110581
theorem B740417 : Blo 491791 740417 := bstep (se 2 (by rfl) ⟨277656, by rfl⟩ : syracuseStep 740417 = 555313) B555313
theorem B740435 : Blo 491791 740435 := bstep (se 1 (by rfl) ⟨555326, by rfl⟩ : syracuseStep 740435 = 1110653) B1110653
theorem B740465 : Blo 491791 740465 := bstep (se 2 (by rfl) ⟨277674, by rfl⟩ : syracuseStep 740465 = 555349) B555349
theorem B740483 : Blo 491791 740483 := bstep (se 1 (by rfl) ⟨555362, by rfl⟩ : syracuseStep 740483 = 1110725) B1110725
theorem B740513 : Blo 491791 740513 := bstep (se 2 (by rfl) ⟨277692, by rfl⟩ : syracuseStep 740513 = 555385) B555385
theorem B740531 : Blo 491791 740531 := bstep (se 1 (by rfl) ⟨555398, by rfl⟩ : syracuseStep 740531 = 1110797) B1110797
theorem B740561 : Blo 491791 740561 := bstep (se 2 (by rfl) ⟨277710, by rfl⟩ : syracuseStep 740561 = 555421) B555421
theorem B740579 : Blo 491791 740579 := bstep (se 1 (by rfl) ⟨555434, by rfl⟩ : syracuseStep 740579 = 1110869) B1110869
theorem B740609 : Blo 491791 740609 := bstep (se 2 (by rfl) ⟨277728, by rfl⟩ : syracuseStep 740609 = 555457) B555457
theorem B609539 : Blo 491791 609539 := bstep (se 1 (by rfl) ⟨457154, by rfl⟩ : syracuseStep 609539 = 914309) B914309
theorem B740627 : Blo 491791 740627 := bstep (se 1 (by rfl) ⟨555470, by rfl⟩ : syracuseStep 740627 = 1110941) B1110941
theorem B740657 : Blo 491791 740657 := bstep (se 2 (by rfl) ⟨277746, by rfl⟩ : syracuseStep 740657 = 555493) B555493
theorem B740675 : Blo 491791 740675 := bstep (se 1 (by rfl) ⟨555506, by rfl⟩ : syracuseStep 740675 = 1111013) B1111013
theorem B740705 : Blo 491791 740705 := bstep (se 2 (by rfl) ⟨277764, by rfl⟩ : syracuseStep 740705 = 555529) B555529
theorem B2379107 : Blo 491791 2379107 := bstep (se 1 (by rfl) ⟨1784330, by rfl⟩ : syracuseStep 2379107 = 3568661) B3568661
theorem B740723 : Blo 491791 740723 := bstep (se 1 (by rfl) ⟨555542, by rfl⟩ : syracuseStep 740723 = 1111085) B1111085
theorem B3165581 : Blo 491791 3165581 := bstep (se 3 (by rfl) ⟨593546, by rfl⟩ : syracuseStep 3165581 = 1187093) B1187093
theorem B740753 : Blo 491791 740753 := bstep (se 2 (by rfl) ⟨277782, by rfl⟩ : syracuseStep 740753 = 555565) B555565
theorem B740771 : Blo 491791 740771 := bstep (se 1 (by rfl) ⟨555578, by rfl⟩ : syracuseStep 740771 = 1111157) B1111157
theorem B740801 : Blo 491791 740801 := bstep (se 2 (by rfl) ⟨277800, by rfl⟩ : syracuseStep 740801 = 555601) B555601
theorem B4214213 : Blo 491791 4214213 := bstep (se 4 (by rfl) ⟨395082, by rfl⟩ : syracuseStep 4214213 = 790165) B790165
theorem B740819 : Blo 491791 740819 := bstep (se 1 (by rfl) ⟨555614, by rfl⟩ : syracuseStep 740819 = 1111229) B1111229
theorem B740849 : Blo 491791 740849 := bstep (se 2 (by rfl) ⟨277818, by rfl⟩ : syracuseStep 740849 = 555637) B555637
theorem B740867 : Blo 491791 740867 := bstep (se 1 (by rfl) ⟨555650, by rfl⟩ : syracuseStep 740867 = 1111301) B1111301
theorem B740897 : Blo 491791 740897 := bstep (se 2 (by rfl) ⟨277836, by rfl⟩ : syracuseStep 740897 = 555673) B555673
theorem B740915 : Blo 491791 740915 := bstep (se 1 (by rfl) ⟨555686, by rfl⟩ : syracuseStep 740915 = 1111373) B1111373
theorem B740945 : Blo 491791 740945 := bstep (se 2 (by rfl) ⟨277854, by rfl⟩ : syracuseStep 740945 = 555709) B555709
theorem B740963 : Blo 491791 740963 := bstep (se 1 (by rfl) ⟨555722, by rfl⟩ : syracuseStep 740963 = 1111445) B1111445
theorem B937585 : Blo 491791 937585 := bstep (se 2 (by rfl) ⟨351594, by rfl⟩ : syracuseStep 937585 = 703189) B703189
theorem B740993 : Blo 491791 740993 := bstep (se 2 (by rfl) ⟨277872, by rfl⟩ : syracuseStep 740993 = 555745) B555745
theorem B741011 : Blo 491791 741011 := bstep (se 1 (by rfl) ⟨555758, by rfl⟩ : syracuseStep 741011 = 1111517) B1111517
theorem B741041 : Blo 491791 741041 := bstep (se 2 (by rfl) ⟨277890, by rfl⟩ : syracuseStep 741041 = 555781) B555781
theorem B741059 : Blo 491791 741059 := bstep (se 1 (by rfl) ⟨555794, by rfl⟩ : syracuseStep 741059 = 1111589) B1111589
theorem B741089 : Blo 491791 741089 := bstep (se 2 (by rfl) ⟨277908, by rfl⟩ : syracuseStep 741089 = 555817) B555817
theorem B741107 : Blo 491791 741107 := bstep (se 1 (by rfl) ⟨555830, by rfl⟩ : syracuseStep 741107 = 1111661) B1111661
theorem B741137 : Blo 491791 741137 := bstep (se 2 (by rfl) ⟨277926, by rfl⟩ : syracuseStep 741137 = 555853) B555853
theorem B741155 : Blo 491791 741155 := bstep (se 1 (by rfl) ⟨555866, by rfl⟩ : syracuseStep 741155 = 1111733) B1111733
theorem B2117411 : Blo 491791 2117411 := bstep (se 1 (by rfl) ⟨1588058, by rfl⟩ : syracuseStep 2117411 = 3176117) B3176117
theorem B741185 : Blo 491791 741185 := bstep (se 2 (by rfl) ⟨277944, by rfl⟩ : syracuseStep 741185 = 555889) B555889
theorem B741203 : Blo 491791 741203 := bstep (se 1 (by rfl) ⟨555902, by rfl⟩ : syracuseStep 741203 = 1111805) B1111805
theorem B1920881 : Blo 491791 1920881 := bstep (se 2 (by rfl) ⟨720330, by rfl⟩ : syracuseStep 1920881 = 1440661) B1440661
theorem B741233 : Blo 491791 741233 := bstep (se 2 (by rfl) ⟨277962, by rfl⟩ : syracuseStep 741233 = 555925) B555925
theorem B741251 : Blo 491791 741251 := bstep (se 1 (by rfl) ⟨555938, by rfl⟩ : syracuseStep 741251 = 1111877) B1111877
theorem B741281 : Blo 491791 741281 := bstep (se 2 (by rfl) ⟨277980, by rfl⟩ : syracuseStep 741281 = 555961) B555961
theorem B741299 : Blo 491791 741299 := bstep (se 1 (by rfl) ⟨555974, by rfl⟩ : syracuseStep 741299 = 1111949) B1111949
theorem B741329 : Blo 491791 741329 := bstep (se 2 (by rfl) ⟨277998, by rfl⟩ : syracuseStep 741329 = 555997) B555997
theorem B741347 : Blo 491791 741347 := bstep (se 1 (by rfl) ⟨556010, by rfl⟩ : syracuseStep 741347 = 1112021) B1112021
theorem B741377 : Blo 491791 741377 := bstep (se 2 (by rfl) ⟨278016, by rfl⟩ : syracuseStep 741377 = 556033) B556033
theorem B741395 : Blo 491791 741395 := bstep (se 1 (by rfl) ⟨556046, by rfl⟩ : syracuseStep 741395 = 1112093) B1112093
theorem B741425 : Blo 491791 741425 := bstep (se 2 (by rfl) ⟨278034, by rfl⟩ : syracuseStep 741425 = 556069) B556069
theorem B741443 : Blo 491791 741443 := bstep (se 1 (by rfl) ⟨556082, by rfl⟩ : syracuseStep 741443 = 1112165) B1112165
theorem B741473 : Blo 491791 741473 := bstep (se 2 (by rfl) ⟨278052, by rfl⟩ : syracuseStep 741473 = 556105) B556105
theorem B741491 : Blo 491791 741491 := bstep (se 1 (by rfl) ⟨556118, by rfl⟩ : syracuseStep 741491 = 1112237) B1112237
theorem B741521 : Blo 491791 741521 := bstep (se 2 (by rfl) ⟨278070, by rfl⟩ : syracuseStep 741521 = 556141) B556141
theorem B741539 : Blo 491791 741539 := bstep (se 1 (by rfl) ⟨556154, by rfl⟩ : syracuseStep 741539 = 1112309) B1112309
theorem B741569 : Blo 491791 741569 := bstep (se 2 (by rfl) ⟨278088, by rfl⟩ : syracuseStep 741569 = 556177) B556177
theorem B741587 : Blo 491791 741587 := bstep (se 1 (by rfl) ⟨556190, by rfl⟩ : syracuseStep 741587 = 1112381) B1112381
theorem B741617 : Blo 491791 741617 := bstep (se 2 (by rfl) ⟨278106, by rfl⟩ : syracuseStep 741617 = 556213) B556213
theorem B741635 : Blo 491791 741635 := bstep (se 1 (by rfl) ⟨556226, by rfl⟩ : syracuseStep 741635 = 1112453) B1112453
theorem B741665 : Blo 491791 741665 := bstep (se 2 (by rfl) ⟨278124, by rfl⟩ : syracuseStep 741665 = 556249) B556249
theorem B741683 : Blo 491791 741683 := bstep (se 1 (by rfl) ⟨556262, by rfl⟩ : syracuseStep 741683 = 1112525) B1112525
theorem B741713 : Blo 491791 741713 := bstep (se 2 (by rfl) ⟨278142, by rfl⟩ : syracuseStep 741713 = 556285) B556285
theorem B741731 : Blo 491791 741731 := bstep (se 1 (by rfl) ⟨556298, by rfl⟩ : syracuseStep 741731 = 1112597) B1112597
theorem B741761 : Blo 491791 741761 := bstep (se 2 (by rfl) ⟨278160, by rfl⟩ : syracuseStep 741761 = 556321) B556321
theorem B20304269 : Blo 491791 20304269 := bstep (se 3 (by rfl) ⟨3807050, by rfl⟩ : syracuseStep 20304269 = 7614101) B7614101
theorem B741779 : Blo 491791 741779 := bstep (se 1 (by rfl) ⟨556334, by rfl⟩ : syracuseStep 741779 = 1112669) B1112669
theorem B741809 : Blo 491791 741809 := bstep (se 2 (by rfl) ⟨278178, by rfl⟩ : syracuseStep 741809 = 556357) B556357
theorem B741827 : Blo 491791 741827 := bstep (se 1 (by rfl) ⟨556370, by rfl⟩ : syracuseStep 741827 = 1112741) B1112741
theorem B741857 : Blo 491791 741857 := bstep (se 2 (by rfl) ⟨278196, by rfl⟩ : syracuseStep 741857 = 556393) B556393
theorem B741875 : Blo 491791 741875 := bstep (se 1 (by rfl) ⟨556406, by rfl⟩ : syracuseStep 741875 = 1112813) B1112813
theorem B2806285 : Blo 491791 2806285 := bstep (se 3 (by rfl) ⟨526178, by rfl⟩ : syracuseStep 2806285 = 1052357) B1052357
theorem B741905 : Blo 491791 741905 := bstep (se 2 (by rfl) ⟨278214, by rfl⟩ : syracuseStep 741905 = 556429) B556429
theorem B741923 : Blo 491791 741923 := bstep (se 1 (by rfl) ⟨556442, by rfl⟩ : syracuseStep 741923 = 1112885) B1112885
theorem B2380337 : Blo 491791 2380337 := bstep (se 2 (by rfl) ⟨892626, by rfl⟩ : syracuseStep 2380337 = 1785253) B1785253
theorem B741953 : Blo 491791 741953 := bstep (se 2 (by rfl) ⟨278232, by rfl⟩ : syracuseStep 741953 = 556465) B556465
theorem B741971 : Blo 491791 741971 := bstep (se 1 (by rfl) ⟨556478, by rfl⟩ : syracuseStep 741971 = 1112957) B1112957
theorem B742001 : Blo 491791 742001 := bstep (se 2 (by rfl) ⟨278250, by rfl⟩ : syracuseStep 742001 = 556501) B556501
theorem B742019 : Blo 491791 742019 := bstep (se 1 (by rfl) ⟨556514, by rfl⟩ : syracuseStep 742019 = 1113029) B1113029
theorem B938641 : Blo 491791 938641 := bstep (se 2 (by rfl) ⟨351990, by rfl⟩ : syracuseStep 938641 = 703981) B703981
theorem B742049 : Blo 491791 742049 := bstep (se 2 (by rfl) ⟨278268, by rfl⟩ : syracuseStep 742049 = 556537) B556537
theorem B742067 : Blo 491791 742067 := bstep (se 1 (by rfl) ⟨556550, by rfl⟩ : syracuseStep 742067 = 1113101) B1113101
theorem B742097 : Blo 491791 742097 := bstep (se 2 (by rfl) ⟨278286, by rfl⟩ : syracuseStep 742097 = 556573) B556573
theorem B742115 : Blo 491791 742115 := bstep (se 1 (by rfl) ⟨556586, by rfl⟩ : syracuseStep 742115 = 1113173) B1113173
theorem B742145 : Blo 491791 742145 := bstep (se 2 (by rfl) ⟨278304, by rfl⟩ : syracuseStep 742145 = 556609) B556609
theorem B742163 : Blo 491791 742163 := bstep (se 1 (by rfl) ⟨556622, by rfl⟩ : syracuseStep 742163 = 1113245) B1113245
theorem B1692461 : Blo 491791 1692461 := bstep (se 3 (by rfl) ⟨317336, by rfl⟩ : syracuseStep 1692461 = 634673) B634673
theorem B742193 : Blo 491791 742193 := bstep (se 2 (by rfl) ⟨278322, by rfl⟩ : syracuseStep 742193 = 556645) B556645
theorem B742211 : Blo 491791 742211 := bstep (se 1 (by rfl) ⟨556658, by rfl⟩ : syracuseStep 742211 = 1113317) B1113317
theorem B742241 : Blo 491791 742241 := bstep (se 2 (by rfl) ⟨278340, by rfl⟩ : syracuseStep 742241 = 556681) B556681
theorem B742259 : Blo 491791 742259 := bstep (se 1 (by rfl) ⟨556694, by rfl⟩ : syracuseStep 742259 = 1113389) B1113389
theorem B742289 : Blo 491791 742289 := bstep (se 2 (by rfl) ⟨278358, by rfl⟩ : syracuseStep 742289 = 556717) B556717
theorem B742307 : Blo 491791 742307 := bstep (se 1 (by rfl) ⟨556730, by rfl⟩ : syracuseStep 742307 = 1113461) B1113461
theorem B742337 : Blo 491791 742337 := bstep (se 2 (by rfl) ⟨278376, by rfl⟩ : syracuseStep 742337 = 556753) B556753
theorem B742355 : Blo 491791 742355 := bstep (se 1 (by rfl) ⟨556766, by rfl⟩ : syracuseStep 742355 = 1113533) B1113533
theorem B742385 : Blo 491791 742385 := bstep (se 2 (by rfl) ⟨278394, by rfl⟩ : syracuseStep 742385 = 556789) B556789
theorem B513011 : Blo 491791 513011 := bstep (se 1 (by rfl) ⟨384758, by rfl⟩ : syracuseStep 513011 = 769517) B769517
theorem B742403 : Blo 491791 742403 := bstep (se 1 (by rfl) ⟨556802, by rfl⟩ : syracuseStep 742403 = 1113605) B1113605
theorem B742433 : Blo 491791 742433 := bstep (se 2 (by rfl) ⟨278412, by rfl⟩ : syracuseStep 742433 = 556825) B556825
theorem B939043 : Blo 491791 939043 := bstep (se 1 (by rfl) ⟨704282, by rfl⟩ : syracuseStep 939043 = 1408565) B1408565
theorem B742451 : Blo 491791 742451 := bstep (se 1 (by rfl) ⟨556838, by rfl⟩ : syracuseStep 742451 = 1113677) B1113677
theorem B1496141 : Blo 491791 1496141 := bstep (se 3 (by rfl) ⟨280526, by rfl⟩ : syracuseStep 1496141 = 561053) B561053
theorem B939089 : Blo 491791 939089 := bstep (se 2 (by rfl) ⟨352158, by rfl⟩ : syracuseStep 939089 = 704317) B704317
theorem B742481 : Blo 491791 742481 := bstep (se 2 (by rfl) ⟨278430, by rfl⟩ : syracuseStep 742481 = 556861) B556861
theorem B742499 : Blo 491791 742499 := bstep (se 1 (by rfl) ⟨556874, by rfl⟩ : syracuseStep 742499 = 1113749) B1113749
theorem B1660013 : Blo 491791 1660013 := bstep (se 3 (by rfl) ⟨311252, by rfl⟩ : syracuseStep 1660013 = 622505) B622505
theorem B742529 : Blo 491791 742529 := bstep (se 2 (by rfl) ⟨278448, by rfl⟩ : syracuseStep 742529 = 556897) B556897
theorem B742547 : Blo 491791 742547 := bstep (se 1 (by rfl) ⟨556910, by rfl⟩ : syracuseStep 742547 = 1113821) B1113821
theorem B1660067 : Blo 491791 1660067 := bstep (se 1 (by rfl) ⟨1245050, by rfl⟩ : syracuseStep 1660067 = 2490101) B2490101
theorem B742577 : Blo 491791 742577 := bstep (se 2 (by rfl) ⟨278466, by rfl⟩ : syracuseStep 742577 = 556933) B556933
theorem B742595 : Blo 491791 742595 := bstep (se 1 (by rfl) ⟨556946, by rfl⟩ : syracuseStep 742595 = 1113893) B1113893
theorem B742625 : Blo 491791 742625 := bstep (se 2 (by rfl) ⟨278484, by rfl⟩ : syracuseStep 742625 = 556969) B556969
theorem B742643 : Blo 491791 742643 := bstep (se 1 (by rfl) ⟨556982, by rfl⟩ : syracuseStep 742643 = 1113965) B1113965
theorem B742673 : Blo 491791 742673 := bstep (se 2 (by rfl) ⟨278502, by rfl⟩ : syracuseStep 742673 = 557005) B557005
theorem B742691 : Blo 491791 742691 := bstep (se 1 (by rfl) ⟨557018, by rfl⟩ : syracuseStep 742691 = 1114037) B1114037
theorem B742721 : Blo 491791 742721 := bstep (se 2 (by rfl) ⟨278520, by rfl⟩ : syracuseStep 742721 = 557041) B557041
theorem B611651 : Blo 491791 611651 := bstep (se 1 (by rfl) ⟨458738, by rfl⟩ : syracuseStep 611651 = 917477) B917477
theorem B5199173 : Blo 491791 5199173 := bstep (se 4 (by rfl) ⟨487422, by rfl⟩ : syracuseStep 5199173 = 974845) B974845
theorem B742739 : Blo 491791 742739 := bstep (se 1 (by rfl) ⟨557054, by rfl⟩ : syracuseStep 742739 = 1114109) B1114109
theorem B1922417 : Blo 491791 1922417 := bstep (se 2 (by rfl) ⟨720906, by rfl⟩ : syracuseStep 1922417 = 1441813) B1441813
theorem B939377 : Blo 491791 939377 := bstep (se 2 (by rfl) ⟨352266, by rfl⟩ : syracuseStep 939377 = 704533) B704533
theorem B742769 : Blo 491791 742769 := bstep (se 2 (by rfl) ⟨278538, by rfl⟩ : syracuseStep 742769 = 557077) B557077
theorem B742787 : Blo 491791 742787 := bstep (se 1 (by rfl) ⟨557090, by rfl⟩ : syracuseStep 742787 = 1114181) B1114181
theorem B742817 : Blo 491791 742817 := bstep (se 2 (by rfl) ⟨278556, by rfl⟩ : syracuseStep 742817 = 557113) B557113
theorem B1660337 : Blo 491791 1660337 := bstep (se 2 (by rfl) ⟨622626, by rfl⟩ : syracuseStep 1660337 = 1245253) B1245253
theorem B742835 : Blo 491791 742835 := bstep (se 1 (by rfl) ⟨557126, by rfl⟩ : syracuseStep 742835 = 1114253) B1114253
theorem B742865 : Blo 491791 742865 := bstep (se 2 (by rfl) ⟨278574, by rfl⟩ : syracuseStep 742865 = 557149) B557149
theorem B742883 : Blo 491791 742883 := bstep (se 1 (by rfl) ⟨557162, by rfl⟩ : syracuseStep 742883 = 1114325) B1114325
theorem B742913 : Blo 491791 742913 := bstep (se 2 (by rfl) ⟨278592, by rfl⟩ : syracuseStep 742913 = 557185) B557185
theorem B742931 : Blo 491791 742931 := bstep (se 1 (by rfl) ⟨557198, by rfl⟩ : syracuseStep 742931 = 1114397) B1114397
theorem B742961 : Blo 491791 742961 := bstep (se 2 (by rfl) ⟨278610, by rfl⟩ : syracuseStep 742961 = 557221) B557221
theorem B742979 : Blo 491791 742979 := bstep (se 1 (by rfl) ⟨557234, by rfl⟩ : syracuseStep 742979 = 1114469) B1114469
theorem B743009 : Blo 491791 743009 := bstep (se 2 (by rfl) ⟨278628, by rfl⟩ : syracuseStep 743009 = 557257) B557257
theorem B743027 : Blo 491791 743027 := bstep (se 1 (by rfl) ⟨557270, by rfl⟩ : syracuseStep 743027 = 1114541) B1114541
theorem B743057 : Blo 491791 743057 := bstep (se 2 (by rfl) ⟨278646, by rfl⟩ : syracuseStep 743057 = 557293) B557293
theorem B743075 : Blo 491791 743075 := bstep (se 1 (by rfl) ⟨557306, by rfl⟩ : syracuseStep 743075 = 1114613) B1114613
theorem B743105 : Blo 491791 743105 := bstep (se 2 (by rfl) ⟨278664, by rfl⟩ : syracuseStep 743105 = 557329) B557329
theorem B743123 : Blo 491791 743123 := bstep (se 1 (by rfl) ⟨557342, by rfl⟩ : syracuseStep 743123 = 1114685) B1114685
theorem B743153 : Blo 491791 743153 := bstep (se 2 (by rfl) ⟨278682, by rfl⟩ : syracuseStep 743153 = 557365) B557365
theorem B743171 : Blo 491791 743171 := bstep (se 1 (by rfl) ⟨557378, by rfl⟩ : syracuseStep 743171 = 1114757) B1114757
theorem B743201 : Blo 491791 743201 := bstep (se 2 (by rfl) ⟨278700, by rfl⟩ : syracuseStep 743201 = 557401) B557401
theorem B1333037 : Blo 491791 1333037 := bstep (se 3 (by rfl) ⟨249944, by rfl⟩ : syracuseStep 1333037 = 499889) B499889
theorem B743219 : Blo 491791 743219 := bstep (se 1 (by rfl) ⟨557414, by rfl⟩ : syracuseStep 743219 = 1114829) B1114829
theorem B743249 : Blo 491791 743249 := bstep (se 2 (by rfl) ⟨278718, by rfl⟩ : syracuseStep 743249 = 557437) B557437
theorem B743267 : Blo 491791 743267 := bstep (se 1 (by rfl) ⟨557450, by rfl⟩ : syracuseStep 743267 = 1114901) B1114901
theorem B743297 : Blo 491791 743297 := bstep (se 2 (by rfl) ⟨278736, by rfl⟩ : syracuseStep 743297 = 557473) B557473
theorem B743315 : Blo 491791 743315 := bstep (se 1 (by rfl) ⟨557486, by rfl⟩ : syracuseStep 743315 = 1114973) B1114973
theorem B743345 : Blo 491791 743345 := bstep (se 2 (by rfl) ⟨278754, by rfl⟩ : syracuseStep 743345 = 557509) B557509
theorem B743363 : Blo 491791 743363 := bstep (se 1 (by rfl) ⟨557522, by rfl⟩ : syracuseStep 743363 = 1115045) B1115045
theorem B1660877 : Blo 491791 1660877 := bstep (se 3 (by rfl) ⟨311414, by rfl⟩ : syracuseStep 1660877 = 622829) B622829
theorem B743393 : Blo 491791 743393 := bstep (se 2 (by rfl) ⟨278772, by rfl⟩ : syracuseStep 743393 = 557545) B557545
theorem B743411 : Blo 491791 743411 := bstep (se 1 (by rfl) ⟨557558, by rfl⟩ : syracuseStep 743411 = 1115117) B1115117
theorem B1660931 : Blo 491791 1660931 := bstep (se 1 (by rfl) ⟨1245698, by rfl⟩ : syracuseStep 1660931 = 2491397) B2491397
theorem B743441 : Blo 491791 743441 := bstep (se 2 (by rfl) ⟨278790, by rfl⟩ : syracuseStep 743441 = 557581) B557581
theorem B743459 : Blo 491791 743459 := bstep (se 1 (by rfl) ⟨557594, by rfl⟩ : syracuseStep 743459 = 1115189) B1115189
theorem B743489 : Blo 491791 743489 := bstep (se 2 (by rfl) ⟨278808, by rfl⟩ : syracuseStep 743489 = 557617) B557617
theorem B940099 : Blo 491791 940099 := bstep (se 1 (by rfl) ⟨705074, by rfl⟩ : syracuseStep 940099 = 1410149) B1410149
theorem B743507 : Blo 491791 743507 := bstep (se 1 (by rfl) ⟨557630, by rfl⟩ : syracuseStep 743507 = 1115261) B1115261
theorem B743537 : Blo 491791 743537 := bstep (se 2 (by rfl) ⟨278826, by rfl⟩ : syracuseStep 743537 = 557653) B557653
theorem B743555 : Blo 491791 743555 := bstep (se 1 (by rfl) ⟨557666, by rfl⟩ : syracuseStep 743555 = 1115333) B1115333
theorem B743585 : Blo 491791 743585 := bstep (se 2 (by rfl) ⟨278844, by rfl⟩ : syracuseStep 743585 = 557689) B557689
theorem B743603 : Blo 491791 743603 := bstep (se 1 (by rfl) ⟨557702, by rfl⟩ : syracuseStep 743603 = 1115405) B1115405
theorem B743633 : Blo 491791 743633 := bstep (se 2 (by rfl) ⟨278862, by rfl⟩ : syracuseStep 743633 = 557725) B557725
theorem B743651 : Blo 491791 743651 := bstep (se 1 (by rfl) ⟨557738, by rfl⟩ : syracuseStep 743651 = 1115477) B1115477
theorem B743681 : Blo 491791 743681 := bstep (se 2 (by rfl) ⟨278880, by rfl⟩ : syracuseStep 743681 = 557761) B557761
theorem B1661201 : Blo 491791 1661201 := bstep (se 2 (by rfl) ⟨622950, by rfl⟩ : syracuseStep 1661201 = 1245901) B1245901
theorem B1136963 : Blo 491791 1136963 := bstep (se 1 (by rfl) ⟨852722, by rfl⟩ : syracuseStep 1136963 = 1705445) B1705445
theorem B2808269 : Blo 491791 2808269 := bstep (se 3 (by rfl) ⟨526550, by rfl⟩ : syracuseStep 2808269 = 1053101) B1053101
theorem B940547 : Blo 491791 940547 := bstep (se 1 (by rfl) ⟨705410, by rfl⟩ : syracuseStep 940547 = 1410821) B1410821
theorem B5626421 : Blo 491791 5626421 := bstep (se 5 (by rfl) ⟨263738, by rfl⟩ : syracuseStep 5626421 = 527477) B527477
theorem B842483 : Blo 491791 842483 := bstep (se 1 (by rfl) ⟨631862, by rfl⟩ : syracuseStep 842483 = 1263725) B1263725
theorem B940835 : Blo 491791 940835 := bstep (se 1 (by rfl) ⟨705626, by rfl⟩ : syracuseStep 940835 = 1411253) B1411253
theorem B1661741 : Blo 491791 1661741 := bstep (se 3 (by rfl) ⟨311576, by rfl⟩ : syracuseStep 1661741 = 623153) B623153
theorem B2841413 : Blo 491791 2841413 := bstep (se 4 (by rfl) ⟨266382, by rfl⟩ : syracuseStep 2841413 = 532765) B532765
theorem B1661795 : Blo 491791 1661795 := bstep (se 1 (by rfl) ⟨1246346, by rfl⟩ : syracuseStep 1661795 = 2492693) B2492693
theorem B6020081 : Blo 491791 6020081 := bstep (se 2 (by rfl) ⟨2257530, by rfl⟩ : syracuseStep 6020081 = 4515061) B4515061
theorem B1662065 : Blo 491791 1662065 := bstep (se 2 (by rfl) ⟨623274, by rfl⟩ : syracuseStep 1662065 = 1246549) B1246549
theorem B6348131 : Blo 491791 6348131 := bstep (se 1 (by rfl) ⟨4761098, by rfl⟩ : syracuseStep 6348131 = 9522197) B9522197
theorem B2809201 : Blo 491791 2809201 := bstep (se 2 (by rfl) ⟨1053450, by rfl⟩ : syracuseStep 2809201 = 2106901) B2106901
theorem B1662605 : Blo 491791 1662605 := bstep (se 3 (by rfl) ⟨311738, by rfl⟩ : syracuseStep 1662605 = 623477) B623477
theorem B1662659 : Blo 491791 1662659 := bstep (se 1 (by rfl) ⟨1246994, by rfl⟩ : syracuseStep 1662659 = 2493989) B2493989
theorem B1498961 : Blo 491791 1498961 := bstep (se 2 (by rfl) ⟨562110, by rfl⟩ : syracuseStep 1498961 = 1124221) B1124221
theorem B3006341 : Blo 491791 3006341 := bstep (se 4 (by rfl) ⟨281844, by rfl⟩ : syracuseStep 3006341 = 563689) B563689
theorem B1662929 : Blo 491791 1662929 := bstep (se 2 (by rfl) ⟨623598, by rfl⟩ : syracuseStep 1662929 = 1247197) B1247197
theorem B2253005 : Blo 491791 2253005 := bstep (se 3 (by rfl) ⟨422438, by rfl⟩ : syracuseStep 2253005 = 844877) B844877
theorem B1401229 : Blo 491791 1401229 := bstep (se 3 (by rfl) ⟨262730, by rfl⟩ : syracuseStep 1401229 = 525461) B525461
theorem B1663469 : Blo 491791 1663469 := bstep (se 3 (by rfl) ⟨311900, by rfl⟩ : syracuseStep 1663469 = 623801) B623801
theorem B1663523 : Blo 491791 1663523 := bstep (se 1 (by rfl) ⟨1247642, by rfl⟩ : syracuseStep 1663523 = 2495285) B2495285
theorem B1106531 : Blo 491791 1106531 := bstep (se 1 (by rfl) ⟨829898, by rfl⟩ : syracuseStep 1106531 = 1659797) B1659797
theorem B1401457 : Blo 491791 1401457 := bstep (se 2 (by rfl) ⟨525546, by rfl⟩ : syracuseStep 1401457 = 1051093) B1051093
theorem B1401617 : Blo 491791 1401617 := bstep (se 2 (by rfl) ⟨525606, by rfl⟩ : syracuseStep 1401617 = 1051213) B1051213
theorem B2810659 : Blo 491791 2810659 := bstep (se 1 (by rfl) ⟨2107994, by rfl⟩ : syracuseStep 2810659 = 4215989) B4215989
theorem B1663793 : Blo 491791 1663793 := bstep (se 2 (by rfl) ⟨623922, by rfl⟩ : syracuseStep 1663793 = 1247845) B1247845
theorem B1106801 : Blo 491791 1106801 := bstep (se 2 (by rfl) ⟨415050, by rfl⟩ : syracuseStep 1106801 = 830101) B830101
theorem B1106819 : Blo 491791 1106819 := bstep (se 1 (by rfl) ⟨830114, by rfl⟩ : syracuseStep 1106819 = 1660229) B1660229
theorem B1401731 : Blo 491791 1401731 := bstep (se 1 (by rfl) ⟨1051298, by rfl⟩ : syracuseStep 1401731 = 2102597) B2102597
theorem B1107089 : Blo 491791 1107089 := bstep (se 2 (by rfl) ⟨415158, by rfl⟩ : syracuseStep 1107089 = 830317) B830317
theorem B1107107 : Blo 491791 1107107 := bstep (se 1 (by rfl) ⟨830330, by rfl⟩ : syracuseStep 1107107 = 1660661) B1660661
theorem B2811185 : Blo 491791 2811185 := bstep (se 2 (by rfl) ⟨1054194, by rfl⟩ : syracuseStep 2811185 = 2108389) B2108389
theorem B1664333 : Blo 491791 1664333 := bstep (se 3 (by rfl) ⟨312062, by rfl⟩ : syracuseStep 1664333 = 624125) B624125
theorem B1664387 : Blo 491791 1664387 := bstep (se 1 (by rfl) ⟨1248290, by rfl⟩ : syracuseStep 1664387 = 2496581) B2496581
theorem B1107377 : Blo 491791 1107377 := bstep (se 2 (by rfl) ⟨415266, by rfl⟩ : syracuseStep 1107377 = 830533) B830533
theorem B1107395 : Blo 491791 1107395 := bstep (se 1 (by rfl) ⟨830546, by rfl⟩ : syracuseStep 1107395 = 1661093) B1661093
theorem B845329 : Blo 491791 845329 := bstep (se 2 (by rfl) ⟨316998, by rfl⟩ : syracuseStep 845329 = 633997) B633997
theorem B1664657 : Blo 491791 1664657 := bstep (se 2 (by rfl) ⟨624246, by rfl⟩ : syracuseStep 1664657 = 1248493) B1248493
theorem B1107665 : Blo 491791 1107665 := bstep (se 2 (by rfl) ⟨415374, by rfl⟩ : syracuseStep 1107665 = 830749) B830749
theorem B1107683 : Blo 491791 1107683 := bstep (se 1 (by rfl) ⟨830762, by rfl⟩ : syracuseStep 1107683 = 1661525) B1661525
theorem B1402733 : Blo 491791 1402733 := bstep (se 3 (by rfl) ⟨263012, by rfl⟩ : syracuseStep 1402733 = 526025) B526025
theorem B1140689 : Blo 491791 1140689 := bstep (se 2 (by rfl) ⟨427758, by rfl⟩ : syracuseStep 1140689 = 855517) B855517
theorem B1107953 : Blo 491791 1107953 := bstep (se 2 (by rfl) ⟨415482, by rfl⟩ : syracuseStep 1107953 = 830965) B830965
theorem B1107971 : Blo 491791 1107971 := bstep (se 1 (by rfl) ⟨830978, by rfl⟩ : syracuseStep 1107971 = 1661957) B1661957
theorem B1402915 : Blo 491791 1402915 := bstep (se 1 (by rfl) ⟨1052186, by rfl⟩ : syracuseStep 1402915 = 2104373) B2104373
theorem B1665197 : Blo 491791 1665197 := bstep (se 3 (by rfl) ⟨312224, by rfl⟩ : syracuseStep 1665197 = 624449) B624449
theorem B1403075 : Blo 491791 1403075 := bstep (se 1 (by rfl) ⟨1052306, by rfl⟩ : syracuseStep 1403075 = 2104613) B2104613
theorem B1665251 : Blo 491791 1665251 := bstep (se 1 (by rfl) ⟨1248938, by rfl⟩ : syracuseStep 1665251 = 2497877) B2497877
theorem B1108241 : Blo 491791 1108241 := bstep (se 2 (by rfl) ⟨415590, by rfl⟩ : syracuseStep 1108241 = 831181) B831181
theorem B1108259 : Blo 491791 1108259 := bstep (se 1 (by rfl) ⟨831194, by rfl⟩ : syracuseStep 1108259 = 1662389) B1662389
theorem B1894769 : Blo 491791 1894769 := bstep (se 2 (by rfl) ⟨710538, by rfl⟩ : syracuseStep 1894769 = 1421077) B1421077
theorem B1665521 : Blo 491791 1665521 := bstep (se 2 (by rfl) ⟨624570, by rfl⟩ : syracuseStep 1665521 = 1249141) B1249141
theorem B1108529 : Blo 491791 1108529 := bstep (se 2 (by rfl) ⟨415698, by rfl⟩ : syracuseStep 1108529 = 831397) B831397
theorem B1108547 : Blo 491791 1108547 := bstep (se 1 (by rfl) ⟨831410, by rfl⟩ : syracuseStep 1108547 = 1662821) B1662821
theorem B2812643 : Blo 491791 2812643 := bstep (se 1 (by rfl) ⟨2109482, by rfl⟩ : syracuseStep 2812643 = 4218965) B4218965
theorem B1108817 : Blo 491791 1108817 := bstep (se 2 (by rfl) ⟨415806, by rfl⟩ : syracuseStep 1108817 = 831613) B831613
theorem B1108835 : Blo 491791 1108835 := bstep (se 1 (by rfl) ⟨831626, by rfl⟩ : syracuseStep 1108835 = 1663253) B1663253
theorem B1666061 : Blo 491791 1666061 := bstep (se 3 (by rfl) ⟨312386, by rfl⟩ : syracuseStep 1666061 = 624773) B624773
theorem B1666115 : Blo 491791 1666115 := bstep (se 1 (by rfl) ⟨1249586, by rfl⟩ : syracuseStep 1666115 = 2499173) B2499173
theorem B1109105 : Blo 491791 1109105 := bstep (se 2 (by rfl) ⟨415914, by rfl⟩ : syracuseStep 1109105 = 831829) B831829
theorem B1109123 : Blo 491791 1109123 := bstep (se 1 (by rfl) ⟨831842, by rfl⟩ : syracuseStep 1109123 = 1663685) B1663685
theorem B1404145 : Blo 491791 1404145 := bstep (se 2 (by rfl) ⟨526554, by rfl⟩ : syracuseStep 1404145 = 1053109) B1053109
theorem B4222277 : Blo 491791 4222277 := bstep (se 4 (by rfl) ⟨395838, by rfl⟩ : syracuseStep 4222277 = 791677) B791677
theorem B1666385 : Blo 491791 1666385 := bstep (se 2 (by rfl) ⟨624894, by rfl⟩ : syracuseStep 1666385 = 1249789) B1249789
theorem B748945 : Blo 491791 748945 := bstep (se 2 (by rfl) ⟨280854, by rfl⟩ : syracuseStep 748945 = 561709) B561709
theorem B1109393 : Blo 491791 1109393 := bstep (se 2 (by rfl) ⟨416022, by rfl⟩ : syracuseStep 1109393 = 832045) B832045
theorem B1109411 : Blo 491791 1109411 := bstep (se 1 (by rfl) ⟨832058, by rfl⟩ : syracuseStep 1109411 = 1664117) B1664117
theorem B650803 : Blo 491791 650803 := bstep (se 1 (by rfl) ⟨488102, by rfl⟩ : syracuseStep 650803 = 976205) B976205
theorem B1109681 : Blo 491791 1109681 := bstep (se 2 (by rfl) ⟨416130, by rfl⟩ : syracuseStep 1109681 = 832261) B832261
theorem B1109699 : Blo 491791 1109699 := bstep (se 1 (by rfl) ⟨832274, by rfl⟩ : syracuseStep 1109699 = 1664549) B1664549
theorem B5074757 : Blo 491791 5074757 := bstep (se 4 (by rfl) ⟨475758, by rfl⟩ : syracuseStep 5074757 = 951517) B951517
theorem B1666925 : Blo 491791 1666925 := bstep (se 3 (by rfl) ⟨312548, by rfl⟩ : syracuseStep 1666925 = 625097) B625097
theorem B1666979 : Blo 491791 1666979 := bstep (se 1 (by rfl) ⟨1250234, by rfl⟩ : syracuseStep 1666979 = 2500469) B2500469
theorem B1109969 : Blo 491791 1109969 := bstep (se 2 (by rfl) ⟨416238, by rfl⟩ : syracuseStep 1109969 = 832477) B832477
theorem B1109987 : Blo 491791 1109987 := bstep (se 1 (by rfl) ⟨832490, by rfl⟩ : syracuseStep 1109987 = 1664981) B1664981
theorem B8024035 : Blo 491791 8024035 := bstep (se 1 (by rfl) ⟨6018026, by rfl⟩ : syracuseStep 8024035 = 12036053) B12036053
theorem B4222961 : Blo 491791 4222961 := bstep (se 2 (by rfl) ⟨1583610, by rfl⟩ : syracuseStep 4222961 = 3167221) B3167221
theorem B1667249 : Blo 491791 1667249 := bstep (se 2 (by rfl) ⟨625218, by rfl⟩ : syracuseStep 1667249 = 1250437) B1250437
theorem B848051 : Blo 491791 848051 := bstep (se 1 (by rfl) ⟨636038, by rfl⟩ : syracuseStep 848051 = 1272077) B1272077
theorem B3010765 : Blo 491791 3010765 := bstep (se 3 (by rfl) ⟨564518, by rfl⟩ : syracuseStep 3010765 = 1129037) B1129037
theorem B1110257 : Blo 491791 1110257 := bstep (se 2 (by rfl) ⟨416346, by rfl⟩ : syracuseStep 1110257 = 832693) B832693
theorem B1110275 : Blo 491791 1110275 := bstep (se 1 (by rfl) ⟨832706, by rfl⟩ : syracuseStep 1110275 = 1665413) B1665413
theorem B553315 : Blo 491791 553315 := bstep (se 1 (by rfl) ⟨414986, by rfl⟩ : syracuseStep 553315 = 829973) B829973
theorem B1405421 : Blo 491791 1405421 := bstep (se 3 (by rfl) ⟨263516, by rfl⟩ : syracuseStep 1405421 = 527033) B527033
theorem B553459 : Blo 491791 553459 := bstep (se 1 (by rfl) ⟨415094, by rfl⟩ : syracuseStep 553459 = 830189) B830189
theorem B1110545 : Blo 491791 1110545 := bstep (se 2 (by rfl) ⟨416454, by rfl⟩ : syracuseStep 1110545 = 832909) B832909
theorem B1110563 : Blo 491791 1110563 := bstep (se 1 (by rfl) ⟨832922, by rfl⟩ : syracuseStep 1110563 = 1665845) B1665845
theorem B2814533 : Blo 491791 2814533 := bstep (se 4 (by rfl) ⟨263862, by rfl⟩ : syracuseStep 2814533 = 527725) B527725
theorem B553603 : Blo 491791 553603 := bstep (se 1 (by rfl) ⟨415202, by rfl⟩ : syracuseStep 553603 = 830405) B830405
theorem B1405603 : Blo 491791 1405603 := bstep (se 1 (by rfl) ⟨1054202, by rfl⟩ : syracuseStep 1405603 = 2108405) B2108405
theorem B750259 : Blo 491791 750259 := bstep (se 1 (by rfl) ⟨562694, by rfl⟩ : syracuseStep 750259 = 1125389) B1125389
theorem B1667789 : Blo 491791 1667789 := bstep (se 3 (by rfl) ⟨312710, by rfl⟩ : syracuseStep 1667789 = 625421) B625421
theorem B1405649 : Blo 491791 1405649 := bstep (se 2 (by rfl) ⟨527118, by rfl⟩ : syracuseStep 1405649 = 1054237) B1054237
theorem B1667843 : Blo 491791 1667843 := bstep (se 1 (by rfl) ⟨1250882, by rfl⟩ : syracuseStep 1667843 = 2501765) B2501765
theorem B553747 : Blo 491791 553747 := bstep (se 1 (by rfl) ⟨415310, by rfl⟩ : syracuseStep 553747 = 830621) B830621
theorem B1110833 : Blo 491791 1110833 := bstep (se 2 (by rfl) ⟨416562, by rfl⟩ : syracuseStep 1110833 = 833125) B833125
theorem B1110851 : Blo 491791 1110851 := bstep (se 1 (by rfl) ⟨833138, by rfl⟩ : syracuseStep 1110851 = 1666277) B1666277
theorem B750449 : Blo 491791 750449 := bstep (se 2 (by rfl) ⟨281418, by rfl⟩ : syracuseStep 750449 = 562837) B562837
theorem B553891 : Blo 491791 553891 := bstep (se 1 (by rfl) ⟨415418, by rfl⟩ : syracuseStep 553891 = 830837) B830837
theorem B5075909 : Blo 491791 5075909 := bstep (se 4 (by rfl) ⟨475866, by rfl⟩ : syracuseStep 5075909 = 951733) B951733
theorem B1668113 : Blo 491791 1668113 := bstep (se 2 (by rfl) ⟨625542, by rfl⟩ : syracuseStep 1668113 = 1251085) B1251085
theorem B554035 : Blo 491791 554035 := bstep (se 1 (by rfl) ⟨415526, by rfl⟩ : syracuseStep 554035 = 831053) B831053
theorem B1111121 : Blo 491791 1111121 := bstep (se 2 (by rfl) ⟨416670, by rfl⟩ : syracuseStep 1111121 = 833341) B833341
theorem B1504337 : Blo 491791 1504337 := bstep (se 2 (by rfl) ⟨564126, by rfl⟩ : syracuseStep 1504337 = 1128253) B1128253
theorem B1111139 : Blo 491791 1111139 := bstep (se 1 (by rfl) ⟨833354, by rfl⟩ : syracuseStep 1111139 = 1666709) B1666709
theorem B554179 : Blo 491791 554179 := bstep (se 1 (by rfl) ⟨415634, by rfl⟩ : syracuseStep 554179 = 831269) B831269
theorem B3994865 : Blo 491791 3994865 := bstep (se 2 (by rfl) ⟨1498074, by rfl⟩ : syracuseStep 3994865 = 2996149) B2996149
theorem B554323 : Blo 491791 554323 := bstep (se 1 (by rfl) ⟨415742, by rfl⟩ : syracuseStep 554323 = 831485) B831485
theorem B1111409 : Blo 491791 1111409 := bstep (se 2 (by rfl) ⟨416778, by rfl⟩ : syracuseStep 1111409 = 833557) B833557
theorem B1111427 : Blo 491791 1111427 := bstep (se 1 (by rfl) ⟨833570, by rfl⟩ : syracuseStep 1111427 = 1667141) B1667141
theorem B554467 : Blo 491791 554467 := bstep (se 1 (by rfl) ⟨415850, by rfl⟩ : syracuseStep 554467 = 831701) B831701
theorem B3569123 : Blo 491791 3569123 := bstep (se 1 (by rfl) ⟨2676842, by rfl⟩ : syracuseStep 3569123 = 5353685) B5353685
theorem B1668653 : Blo 491791 1668653 := bstep (se 3 (by rfl) ⟨312872, by rfl⟩ : syracuseStep 1668653 = 625745) B625745
theorem B1668707 : Blo 491791 1668707 := bstep (se 1 (by rfl) ⟨1251530, by rfl⟩ : syracuseStep 1668707 = 2503061) B2503061
theorem B554611 : Blo 491791 554611 := bstep (se 1 (by rfl) ⟨415958, by rfl⟩ : syracuseStep 554611 = 831917) B831917
theorem B1111697 : Blo 491791 1111697 := bstep (se 2 (by rfl) ⟨416886, by rfl⟩ : syracuseStep 1111697 = 833773) B833773
theorem B1111715 : Blo 491791 1111715 := bstep (se 1 (by rfl) ⟨833786, by rfl⟩ : syracuseStep 1111715 = 1667573) B1667573
theorem B554755 : Blo 491791 554755 := bstep (se 1 (by rfl) ⟨416066, by rfl⟩ : syracuseStep 554755 = 832133) B832133
theorem B751427 : Blo 491791 751427 := bstep (se 1 (by rfl) ⟨563570, by rfl⟩ : syracuseStep 751427 = 1127141) B1127141
theorem B1668977 : Blo 491791 1668977 := bstep (se 2 (by rfl) ⟨625866, by rfl⟩ : syracuseStep 1668977 = 1251733) B1251733
theorem B554899 : Blo 491791 554899 := bstep (se 1 (by rfl) ⟨416174, by rfl⟩ : syracuseStep 554899 = 832349) B832349
theorem B1898417 : Blo 491791 1898417 := bstep (se 2 (by rfl) ⟨711906, by rfl⟩ : syracuseStep 1898417 = 1423813) B1423813
theorem B1111985 : Blo 491791 1111985 := bstep (se 2 (by rfl) ⟨416994, by rfl⟩ : syracuseStep 1111985 = 833989) B833989
theorem B1112003 : Blo 491791 1112003 := bstep (se 1 (by rfl) ⟨834002, by rfl⟩ : syracuseStep 1112003 = 1668005) B1668005
theorem B555043 : Blo 491791 555043 := bstep (se 1 (by rfl) ⟨416282, by rfl⟩ : syracuseStep 555043 = 832565) B832565
theorem B7108721 : Blo 491791 7108721 := bstep (se 2 (by rfl) ⟨2665770, by rfl⟩ : syracuseStep 7108721 = 5331541) B5331541
theorem B1407107 : Blo 491791 1407107 := bstep (se 1 (by rfl) ⟨1055330, by rfl⟩ : syracuseStep 1407107 = 2110661) B2110661
theorem B3045539 : Blo 491791 3045539 := bstep (se 1 (by rfl) ⟨2284154, by rfl⟩ : syracuseStep 3045539 = 4568309) B4568309
theorem B555187 : Blo 491791 555187 := bstep (se 1 (by rfl) ⟨416390, by rfl⟩ : syracuseStep 555187 = 832781) B832781
theorem B1112273 : Blo 491791 1112273 := bstep (se 2 (by rfl) ⟨417102, by rfl⟩ : syracuseStep 1112273 = 834205) B834205
theorem B1112291 : Blo 491791 1112291 := bstep (se 1 (by rfl) ⟨834218, by rfl⟩ : syracuseStep 1112291 = 1668437) B1668437
theorem B555331 : Blo 491791 555331 := bstep (se 1 (by rfl) ⟨416498, by rfl⟩ : syracuseStep 555331 = 832997) B832997
theorem B817523 : Blo 491791 817523 := bstep (se 1 (by rfl) ⟨613142, by rfl⟩ : syracuseStep 817523 = 1226285) B1226285
theorem B1669517 : Blo 491791 1669517 := bstep (se 3 (by rfl) ⟨313034, by rfl⟩ : syracuseStep 1669517 = 626069) B626069
theorem B1669571 : Blo 491791 1669571 := bstep (se 1 (by rfl) ⟨1252178, by rfl⟩ : syracuseStep 1669571 = 2504357) B2504357
theorem B555475 : Blo 491791 555475 := bstep (se 1 (by rfl) ⟨416606, by rfl⟩ : syracuseStep 555475 = 833213) B833213
theorem B1112561 : Blo 491791 1112561 := bstep (se 2 (by rfl) ⟨417210, by rfl⟩ : syracuseStep 1112561 = 834421) B834421
theorem B1112579 : Blo 491791 1112579 := bstep (se 1 (by rfl) ⟨834434, by rfl⟩ : syracuseStep 1112579 = 1668869) B1668869
theorem B2259533 : Blo 491791 2259533 := bstep (se 3 (by rfl) ⟨423662, by rfl⟩ : syracuseStep 2259533 = 847325) B847325
theorem B555619 : Blo 491791 555619 := bstep (se 1 (by rfl) ⟨416714, by rfl⟩ : syracuseStep 555619 = 833429) B833429
theorem B916145 : Blo 491791 916145 := bstep (se 2 (by rfl) ⟨343554, by rfl⟩ : syracuseStep 916145 = 687109) B687109
theorem B1669841 : Blo 491791 1669841 := bstep (se 2 (by rfl) ⟨626190, by rfl⟩ : syracuseStep 1669841 = 1252381) B1252381
theorem B555763 : Blo 491791 555763 := bstep (se 1 (by rfl) ⟨416822, by rfl⟩ : syracuseStep 555763 = 833645) B833645
theorem B1112849 : Blo 491791 1112849 := bstep (se 2 (by rfl) ⟨417318, by rfl⟩ : syracuseStep 1112849 = 834637) B834637
theorem B1112867 : Blo 491791 1112867 := bstep (se 1 (by rfl) ⟨834650, by rfl⟩ : syracuseStep 1112867 = 1669301) B1669301
theorem B555907 : Blo 491791 555907 := bstep (se 1 (by rfl) ⟨416930, by rfl⟩ : syracuseStep 555907 = 833861) B833861
theorem B556051 : Blo 491791 556051 := bstep (se 1 (by rfl) ⟨417038, by rfl⟩ : syracuseStep 556051 = 834077) B834077
theorem B1113137 : Blo 491791 1113137 := bstep (se 2 (by rfl) ⟨417426, by rfl⟩ : syracuseStep 1113137 = 834853) B834853
theorem B1113155 : Blo 491791 1113155 := bstep (se 1 (by rfl) ⟨834866, by rfl⟩ : syracuseStep 1113155 = 1669733) B1669733
theorem B556195 : Blo 491791 556195 := bstep (se 1 (by rfl) ⟨417146, by rfl⟩ : syracuseStep 556195 = 834293) B834293
theorem B1670381 : Blo 491791 1670381 := bstep (se 3 (by rfl) ⟨313196, by rfl⟩ : syracuseStep 1670381 = 626393) B626393
theorem B1670435 : Blo 491791 1670435 := bstep (se 1 (by rfl) ⟨1252826, by rfl⟩ : syracuseStep 1670435 = 2505653) B2505653
theorem B556339 : Blo 491791 556339 := bstep (se 1 (by rfl) ⟨417254, by rfl⟩ : syracuseStep 556339 = 834509) B834509
theorem B1408337 : Blo 491791 1408337 := bstep (se 2 (by rfl) ⟨528126, by rfl⟩ : syracuseStep 1408337 = 1056253) B1056253
theorem B1113425 : Blo 491791 1113425 := bstep (se 2 (by rfl) ⟨417534, by rfl⟩ : syracuseStep 1113425 = 835069) B835069
theorem B1113443 : Blo 491791 1113443 := bstep (se 1 (by rfl) ⟨835082, by rfl⟩ : syracuseStep 1113443 = 1670165) B1670165
theorem B2489777 : Blo 491791 2489777 := bstep (se 2 (by rfl) ⟨933666, by rfl⟩ : syracuseStep 2489777 = 1867333) B1867333
theorem B556483 : Blo 491791 556483 := bstep (se 1 (by rfl) ⟨417362, by rfl⟩ : syracuseStep 556483 = 834725) B834725
theorem B1670705 : Blo 491791 1670705 := bstep (se 2 (by rfl) ⟨626514, by rfl⟩ : syracuseStep 1670705 = 1253029) B1253029
theorem B556627 : Blo 491791 556627 := bstep (se 1 (by rfl) ⟨417470, by rfl⟩ : syracuseStep 556627 = 834941) B834941
theorem B1113713 : Blo 491791 1113713 := bstep (se 2 (by rfl) ⟨417642, by rfl⟩ : syracuseStep 1113713 = 835285) B835285
theorem B1113731 : Blo 491791 1113731 := bstep (se 1 (by rfl) ⟨835298, by rfl⟩ : syracuseStep 1113731 = 1670597) B1670597
theorem B556771 : Blo 491791 556771 := bstep (se 1 (by rfl) ⟨417578, by rfl⟩ : syracuseStep 556771 = 835157) B835157
theorem B3735395 : Blo 491791 3735395 := bstep (se 1 (by rfl) ⟨2801546, by rfl⟩ : syracuseStep 3735395 = 5603093) B5603093
theorem B1245041 : Blo 491791 1245041 := bstep (se 2 (by rfl) ⟨466890, by rfl⟩ : syracuseStep 1245041 = 933781) B933781
theorem B556915 : Blo 491791 556915 := bstep (se 1 (by rfl) ⟨417686, by rfl⟩ : syracuseStep 556915 = 835373) B835373
theorem B1114001 : Blo 491791 1114001 := bstep (se 2 (by rfl) ⟨417750, by rfl⟩ : syracuseStep 1114001 = 835501) B835501
theorem B1245091 : Blo 491791 1245091 := bstep (se 1 (by rfl) ⟨933818, by rfl⟩ : syracuseStep 1245091 = 1867637) B1867637
theorem B1114019 : Blo 491791 1114019 := bstep (se 1 (by rfl) ⟨835514, by rfl⟩ : syracuseStep 1114019 = 1671029) B1671029
theorem B753617 : Blo 491791 753617 := bstep (se 2 (by rfl) ⟨282606, by rfl⟩ : syracuseStep 753617 = 565213) B565213
theorem B1671191 : Blo 491791 1671191 := bstep (se 1 (by rfl) ⟨1253393, by rfl⟩ : syracuseStep 1671191 = 2506787) B2506787
theorem B1114163 : Blo 491791 1114163 := bstep (se 1 (by rfl) ⟨835622, by rfl⟩ : syracuseStep 1114163 = 1671245) B1671245
theorem B1409089 : Blo 491791 1409089 := bstep (se 2 (by rfl) ⟨528408, by rfl⟩ : syracuseStep 1409089 = 1056817) B1056817
theorem B622667 : Blo 491791 622667 := bstep (se 1 (by rfl) ⟨467000, by rfl⟩ : syracuseStep 622667 = 934001) B934001
theorem B557131 : Blo 491791 557131 := bstep (se 1 (by rfl) ⟨417848, by rfl⟩ : syracuseStep 557131 = 835697) B835697
theorem B1114199 : Blo 491791 1114199 := bstep (se 1 (by rfl) ⟨835649, by rfl⟩ : syracuseStep 1114199 = 1671299) B1671299
theorem B557239 : Blo 491791 557239 := bstep (se 1 (by rfl) ⟨417929, by rfl⟩ : syracuseStep 557239 = 835859) B835859
theorem B1114379 : Blo 491791 1114379 := bstep (se 1 (by rfl) ⟨835784, by rfl⟩ : syracuseStep 1114379 = 1671569) B1671569
theorem B491799 : Blo 491791 491799 := bstep (se 1 (by rfl) ⟨368849, by rfl⟩ : syracuseStep 491799 = 737699) B737699
theorem B491819 : Blo 491791 491819 := bstep (se 1 (by rfl) ⟨368864, by rfl⟩ : syracuseStep 491819 = 737729) B737729
theorem B491831 : Blo 491791 491831 := bstep (se 1 (by rfl) ⟨368873, by rfl⟩ : syracuseStep 491831 = 737747) B737747
theorem B1114433 : Blo 491791 1114433 := bstep (se 2 (by rfl) ⟨417912, by rfl⟩ : syracuseStep 1114433 = 835825) B835825
theorem B491851 : Blo 491791 491851 := bstep (se 1 (by rfl) ⟨368888, by rfl⟩ : syracuseStep 491851 = 737777) B737777
theorem B491863 : Blo 491791 491863 := bstep (se 1 (by rfl) ⟨368897, by rfl⟩ : syracuseStep 491863 = 737795) B737795
theorem B491883 : Blo 491791 491883 := bstep (se 1 (by rfl) ⟨368912, by rfl⟩ : syracuseStep 491883 = 737825) B737825
theorem B557419 : Blo 491791 557419 := bstep (se 1 (by rfl) ⟨418064, by rfl⟩ : syracuseStep 557419 = 836129) B836129
theorem B491895 : Blo 491791 491895 := bstep (se 1 (by rfl) ⟨368921, by rfl⟩ : syracuseStep 491895 = 737843) B737843
theorem B491915 : Blo 491791 491915 := bstep (se 1 (by rfl) ⟨368936, by rfl⟩ : syracuseStep 491915 = 737873) B737873
theorem B491927 : Blo 491791 491927 := bstep (se 1 (by rfl) ⟨368945, by rfl⟩ : syracuseStep 491927 = 737891) B737891
theorem B491947 : Blo 491791 491947 := bstep (se 1 (by rfl) ⟨368960, by rfl⟩ : syracuseStep 491947 = 737921) B737921
theorem B491959 : Blo 491791 491959 := bstep (se 1 (by rfl) ⟨368969, by rfl⟩ : syracuseStep 491959 = 737939) B737939
theorem B491979 : Blo 491791 491979 := bstep (se 1 (by rfl) ⟨368984, by rfl⟩ : syracuseStep 491979 = 737969) B737969
theorem B491991 : Blo 491791 491991 := bstep (se 1 (by rfl) ⟨368993, by rfl⟩ : syracuseStep 491991 = 737987) B737987
theorem B557527 : Blo 491791 557527 := bstep (se 1 (by rfl) ⟨418145, by rfl⟩ : syracuseStep 557527 = 836291) B836291
theorem B492011 : Blo 491791 492011 := bstep (se 1 (by rfl) ⟨369008, by rfl⟩ : syracuseStep 492011 = 738017) B738017
theorem B492023 : Blo 491791 492023 := bstep (se 1 (by rfl) ⟨369017, by rfl⟩ : syracuseStep 492023 = 738035) B738035
theorem B1868291 : Blo 491791 1868291 := bstep (se 1 (by rfl) ⟨1401218, by rfl⟩ : syracuseStep 1868291 = 2802437) B2802437
theorem B492043 : Blo 491791 492043 := bstep (se 1 (by rfl) ⟨369032, by rfl⟩ : syracuseStep 492043 = 738065) B738065
theorem B1868305 : Blo 491791 1868305 := bstep (se 2 (by rfl) ⟨700614, by rfl⟩ : syracuseStep 1868305 = 1401229) B1401229
theorem B492055 : Blo 491791 492055 := bstep (se 1 (by rfl) ⟨369041, by rfl⟩ : syracuseStep 492055 = 738083) B738083
theorem B1245719 : Blo 491791 1245719 := bstep (se 1 (by rfl) ⟨934289, by rfl⟩ : syracuseStep 1245719 = 1868579) B1868579
theorem B1114649 : Blo 491791 1114649 := bstep (se 2 (by rfl) ⟨417993, by rfl⟩ : syracuseStep 1114649 = 835987) B835987
theorem B492075 : Blo 491791 492075 := bstep (se 1 (by rfl) ⟨369056, by rfl⟩ : syracuseStep 492075 = 738113) B738113
theorem B1671731 : Blo 491791 1671731 := bstep (se 1 (by rfl) ⟨1253798, by rfl⟩ : syracuseStep 1671731 = 2507597) B2507597
theorem B492087 : Blo 491791 492087 := bstep (se 1 (by rfl) ⟨369065, by rfl⟩ : syracuseStep 492087 = 738131) B738131
theorem B492107 : Blo 491791 492107 := bstep (se 1 (by rfl) ⟨369080, by rfl⟩ : syracuseStep 492107 = 738161) B738161
theorem B492119 : Blo 491791 492119 := bstep (se 1 (by rfl) ⟨369089, by rfl⟩ : syracuseStep 492119 = 738179) B738179
theorem B21627485 : Blo 491791 21627485 := bstep (se 3 (by rfl) ⟨4055153, by rfl⟩ : syracuseStep 21627485 = 8110307) B8110307
theorem B492139 : Blo 491791 492139 := bstep (se 1 (by rfl) ⟨369104, by rfl⟩ : syracuseStep 492139 = 738209) B738209
theorem B1114739 : Blo 491791 1114739 := bstep (se 1 (by rfl) ⟨836054, by rfl⟩ : syracuseStep 1114739 = 1672109) B1672109
theorem B492151 : Blo 491791 492151 := bstep (se 1 (by rfl) ⟨369113, by rfl⟩ : syracuseStep 492151 = 738227) B738227
theorem B492171 : Blo 491791 492171 := bstep (se 1 (by rfl) ⟨369128, by rfl⟩ : syracuseStep 492171 = 738257) B738257
theorem B557707 : Blo 491791 557707 := bstep (se 1 (by rfl) ⟨418280, by rfl⟩ : syracuseStep 557707 = 836561) B836561
theorem B492183 : Blo 491791 492183 := bstep (se 1 (by rfl) ⟨369137, by rfl⟩ : syracuseStep 492183 = 738275) B738275
theorem B1999511 : Blo 491791 1999511 := bstep (se 1 (by rfl) ⟨1499633, by rfl⟩ : syracuseStep 1999511 = 2999267) B2999267
theorem B1114775 : Blo 491791 1114775 := bstep (se 1 (by rfl) ⟨836081, by rfl⟩ : syracuseStep 1114775 = 1672163) B1672163
theorem B492203 : Blo 491791 492203 := bstep (se 1 (by rfl) ⟨369152, by rfl⟩ : syracuseStep 492203 = 738305) B738305
theorem B492215 : Blo 491791 492215 := bstep (se 1 (by rfl) ⟨369161, by rfl⟩ : syracuseStep 492215 = 738323) B738323
theorem B492235 : Blo 491791 492235 := bstep (se 1 (by rfl) ⟨369176, by rfl⟩ : syracuseStep 492235 = 738353) B738353
theorem B492247 : Blo 491791 492247 := bstep (se 1 (by rfl) ⟨369185, by rfl⟩ : syracuseStep 492247 = 738371) B738371
theorem B492267 : Blo 491791 492267 := bstep (se 1 (by rfl) ⟨369200, by rfl⟩ : syracuseStep 492267 = 738401) B738401
theorem B492279 : Blo 491791 492279 := bstep (se 1 (by rfl) ⟨369209, by rfl⟩ : syracuseStep 492279 = 738419) B738419
theorem B492299 : Blo 491791 492299 := bstep (se 1 (by rfl) ⟨369224, by rfl⟩ : syracuseStep 492299 = 738449) B738449
theorem B623371 : Blo 491791 623371 := bstep (se 1 (by rfl) ⟨467528, by rfl⟩ : syracuseStep 623371 = 935057) B935057
theorem B492311 : Blo 491791 492311 := bstep (se 1 (by rfl) ⟨369233, by rfl⟩ : syracuseStep 492311 = 738467) B738467
theorem B492331 : Blo 491791 492331 := bstep (se 1 (by rfl) ⟨369248, by rfl⟩ : syracuseStep 492331 = 738497) B738497
theorem B492343 : Blo 491791 492343 := bstep (se 1 (by rfl) ⟨369257, by rfl⟩ : syracuseStep 492343 = 738515) B738515
theorem B1868609 : Blo 491791 1868609 := bstep (se 2 (by rfl) ⟨700728, by rfl⟩ : syracuseStep 1868609 = 1401457) B1401457
theorem B1672001 : Blo 491791 1672001 := bstep (se 2 (by rfl) ⟨627000, by rfl⟩ : syracuseStep 1672001 = 1254001) B1254001
theorem B492363 : Blo 491791 492363 := bstep (se 1 (by rfl) ⟨369272, by rfl⟩ : syracuseStep 492363 = 738545) B738545
theorem B1114955 : Blo 491791 1114955 := bstep (se 1 (by rfl) ⟨836216, by rfl⟩ : syracuseStep 1114955 = 1672433) B1672433
theorem B492375 : Blo 491791 492375 := bstep (se 1 (by rfl) ⟨369281, by rfl⟩ : syracuseStep 492375 = 738563) B738563
theorem B492395 : Blo 491791 492395 := bstep (se 1 (by rfl) ⟨369296, by rfl⟩ : syracuseStep 492395 = 738593) B738593
theorem B492407 : Blo 491791 492407 := bstep (se 1 (by rfl) ⟨369305, by rfl⟩ : syracuseStep 492407 = 738611) B738611
theorem B1115009 : Blo 491791 1115009 := bstep (se 2 (by rfl) ⟨418128, by rfl⟩ : syracuseStep 1115009 = 836257) B836257
theorem B492427 : Blo 491791 492427 := bstep (se 1 (by rfl) ⟨369320, by rfl⟩ : syracuseStep 492427 = 738641) B738641
theorem B492439 : Blo 491791 492439 := bstep (se 1 (by rfl) ⟨369329, by rfl⟩ : syracuseStep 492439 = 738659) B738659
theorem B492459 : Blo 491791 492459 := bstep (se 1 (by rfl) ⟨369344, by rfl⟩ : syracuseStep 492459 = 738689) B738689
theorem B492471 : Blo 491791 492471 := bstep (se 1 (by rfl) ⟨369353, by rfl⟩ : syracuseStep 492471 = 738707) B738707
theorem B492491 : Blo 491791 492491 := bstep (se 1 (by rfl) ⟨369368, by rfl⟩ : syracuseStep 492491 = 738737) B738737
theorem B492503 : Blo 491791 492503 := bstep (se 1 (by rfl) ⟨369377, by rfl⟩ : syracuseStep 492503 = 738755) B738755
theorem B492523 : Blo 491791 492523 := bstep (se 1 (by rfl) ⟨369392, by rfl⟩ : syracuseStep 492523 = 738785) B738785
theorem B492535 : Blo 491791 492535 := bstep (se 1 (by rfl) ⟨369401, by rfl⟩ : syracuseStep 492535 = 738803) B738803
theorem B492555 : Blo 491791 492555 := bstep (se 1 (by rfl) ⟨369416, by rfl⟩ : syracuseStep 492555 = 738833) B738833
theorem B492567 : Blo 491791 492567 := bstep (se 1 (by rfl) ⟨369425, by rfl⟩ : syracuseStep 492567 = 738851) B738851
theorem B623639 : Blo 491791 623639 := bstep (se 1 (by rfl) ⟨467729, by rfl⟩ : syracuseStep 623639 = 935459) B935459
theorem B492587 : Blo 491791 492587 := bstep (se 1 (by rfl) ⟨369440, by rfl⟩ : syracuseStep 492587 = 738881) B738881
theorem B492599 : Blo 491791 492599 := bstep (se 1 (by rfl) ⟨369449, by rfl⟩ : syracuseStep 492599 = 738899) B738899
theorem B590923 : Blo 491791 590923 := bstep (se 1 (by rfl) ⟨443192, by rfl⟩ : syracuseStep 590923 = 886385) B886385
theorem B492619 : Blo 491791 492619 := bstep (se 1 (by rfl) ⟨369464, by rfl⟩ : syracuseStep 492619 = 738929) B738929
theorem B492631 : Blo 491791 492631 := bstep (se 1 (by rfl) ⟨369473, by rfl⟩ : syracuseStep 492631 = 738947) B738947
theorem B1115225 : Blo 491791 1115225 := bstep (se 2 (by rfl) ⟨418209, by rfl⟩ : syracuseStep 1115225 = 836419) B836419
theorem B492651 : Blo 491791 492651 := bstep (se 1 (by rfl) ⟨369488, by rfl⟩ : syracuseStep 492651 = 738977) B738977
theorem B492663 : Blo 491791 492663 := bstep (se 1 (by rfl) ⟨369497, by rfl⟩ : syracuseStep 492663 = 738995) B738995
theorem B492683 : Blo 491791 492683 := bstep (se 1 (by rfl) ⟨369512, by rfl⟩ : syracuseStep 492683 = 739025) B739025
theorem B492695 : Blo 491791 492695 := bstep (se 1 (by rfl) ⟨369521, by rfl⟩ : syracuseStep 492695 = 739043) B739043
theorem B492715 : Blo 491791 492715 := bstep (se 1 (by rfl) ⟨369536, by rfl⟩ : syracuseStep 492715 = 739073) B739073
theorem B1246387 : Blo 491791 1246387 := bstep (se 1 (by rfl) ⟨934790, by rfl⟩ : syracuseStep 1246387 = 1869581) B1869581
theorem B1115315 : Blo 491791 1115315 := bstep (se 1 (by rfl) ⟨836486, by rfl⟩ : syracuseStep 1115315 = 1672973) B1672973
theorem B492727 : Blo 491791 492727 := bstep (se 1 (by rfl) ⟨369545, by rfl⟩ : syracuseStep 492727 = 739091) B739091
theorem B492747 : Blo 491791 492747 := bstep (se 1 (by rfl) ⟨369560, by rfl⟩ : syracuseStep 492747 = 739121) B739121
theorem B492759 : Blo 491791 492759 := bstep (se 1 (by rfl) ⟨369569, by rfl⟩ : syracuseStep 492759 = 739139) B739139
theorem B1115351 : Blo 491791 1115351 := bstep (se 1 (by rfl) ⟨836513, by rfl⟩ : syracuseStep 1115351 = 1673027) B1673027
theorem B492779 : Blo 491791 492779 := bstep (se 1 (by rfl) ⟨369584, by rfl⟩ : syracuseStep 492779 = 739169) B739169
theorem B492791 : Blo 491791 492791 := bstep (se 1 (by rfl) ⟨369593, by rfl⟩ : syracuseStep 492791 = 739187) B739187
theorem B492811 : Blo 491791 492811 := bstep (se 1 (by rfl) ⟨369608, by rfl⟩ : syracuseStep 492811 = 739217) B739217
theorem B492823 : Blo 491791 492823 := bstep (se 1 (by rfl) ⟨369617, by rfl⟩ : syracuseStep 492823 = 739235) B739235
theorem B492843 : Blo 491791 492843 := bstep (se 1 (by rfl) ⟨369632, by rfl⟩ : syracuseStep 492843 = 739265) B739265
theorem B492855 : Blo 491791 492855 := bstep (se 1 (by rfl) ⟨369641, by rfl⟩ : syracuseStep 492855 = 739283) B739283
theorem B1246529 : Blo 491791 1246529 := bstep (se 2 (by rfl) ⟨467448, by rfl⟩ : syracuseStep 1246529 = 934897) B934897
theorem B492875 : Blo 491791 492875 := bstep (se 1 (by rfl) ⟨369656, by rfl⟩ : syracuseStep 492875 = 739313) B739313
theorem B492887 : Blo 491791 492887 := bstep (se 1 (by rfl) ⟨369665, by rfl⟩ : syracuseStep 492887 = 739331) B739331
theorem B1672541 : Blo 491791 1672541 := bstep (se 3 (by rfl) ⟨313601, by rfl⟩ : syracuseStep 1672541 = 627203) B627203
theorem B492907 : Blo 491791 492907 := bstep (se 1 (by rfl) ⟨369680, by rfl⟩ : syracuseStep 492907 = 739361) B739361
theorem B492919 : Blo 491791 492919 := bstep (se 1 (by rfl) ⟨369689, by rfl⟩ : syracuseStep 492919 = 739379) B739379
theorem B492939 : Blo 491791 492939 := bstep (se 1 (by rfl) ⟨369704, by rfl⟩ : syracuseStep 492939 = 739409) B739409
theorem B1115531 : Blo 491791 1115531 := bstep (se 1 (by rfl) ⟨836648, by rfl⟩ : syracuseStep 1115531 = 1673297) B1673297
theorem B492951 : Blo 491791 492951 := bstep (se 1 (by rfl) ⟨369713, by rfl⟩ : syracuseStep 492951 = 739427) B739427
theorem B492971 : Blo 491791 492971 := bstep (se 1 (by rfl) ⟨369728, by rfl⟩ : syracuseStep 492971 = 739457) B739457
theorem B492983 : Blo 491791 492983 := bstep (se 1 (by rfl) ⟨369737, by rfl⟩ : syracuseStep 492983 = 739475) B739475
theorem B493003 : Blo 491791 493003 := bstep (se 1 (by rfl) ⟨369752, by rfl⟩ : syracuseStep 493003 = 739505) B739505
theorem B493015 : Blo 491791 493015 := bstep (se 1 (by rfl) ⟨369761, by rfl⟩ : syracuseStep 493015 = 739523) B739523
theorem B1869277 : Blo 491791 1869277 := bstep (se 3 (by rfl) ⟨350489, by rfl⟩ : syracuseStep 1869277 = 700979) B700979
theorem B493035 : Blo 491791 493035 := bstep (se 1 (by rfl) ⟨369776, by rfl⟩ : syracuseStep 493035 = 739553) B739553
theorem B493047 : Blo 491791 493047 := bstep (se 1 (by rfl) ⟨369785, by rfl⟩ : syracuseStep 493047 = 739571) B739571
theorem B493067 : Blo 491791 493067 := bstep (se 1 (by rfl) ⟨369800, by rfl⟩ : syracuseStep 493067 = 739601) B739601
theorem B493079 : Blo 491791 493079 := bstep (se 1 (by rfl) ⟨369809, by rfl⟩ : syracuseStep 493079 = 739619) B739619
theorem B493099 : Blo 491791 493099 := bstep (se 1 (by rfl) ⟨369824, by rfl⟩ : syracuseStep 493099 = 739649) B739649
theorem B493111 : Blo 491791 493111 := bstep (se 1 (by rfl) ⟨369833, by rfl⟩ : syracuseStep 493111 = 739667) B739667
theorem B493131 : Blo 491791 493131 := bstep (se 1 (by rfl) ⟨369848, by rfl⟩ : syracuseStep 493131 = 739697) B739697
theorem B493143 : Blo 491791 493143 := bstep (se 1 (by rfl) ⟨369857, by rfl⟩ : syracuseStep 493143 = 739715) B739715
theorem B493163 : Blo 491791 493163 := bstep (se 1 (by rfl) ⟨369872, by rfl⟩ : syracuseStep 493163 = 739745) B739745
theorem B493175 : Blo 491791 493175 := bstep (se 1 (by rfl) ⟨369881, by rfl⟩ : syracuseStep 493175 = 739763) B739763
theorem B493195 : Blo 491791 493195 := bstep (se 1 (by rfl) ⟨369896, by rfl⟩ : syracuseStep 493195 = 739793) B739793
theorem B493207 : Blo 491791 493207 := bstep (se 1 (by rfl) ⟨369905, by rfl⟩ : syracuseStep 493207 = 739811) B739811
theorem B493227 : Blo 491791 493227 := bstep (se 1 (by rfl) ⟨369920, by rfl⟩ : syracuseStep 493227 = 739841) B739841
theorem B493239 : Blo 491791 493239 := bstep (se 1 (by rfl) ⟨369929, by rfl⟩ : syracuseStep 493239 = 739859) B739859
theorem B493259 : Blo 491791 493259 := bstep (se 1 (by rfl) ⟨369944, by rfl⟩ : syracuseStep 493259 = 739889) B739889
theorem B493271 : Blo 491791 493271 := bstep (se 1 (by rfl) ⟨369953, by rfl⟩ : syracuseStep 493271 = 739907) B739907
theorem B624343 : Blo 491791 624343 := bstep (se 1 (by rfl) ⟨468257, by rfl⟩ : syracuseStep 624343 = 936515) B936515
theorem B493291 : Blo 491791 493291 := bstep (se 1 (by rfl) ⟨369968, by rfl⟩ : syracuseStep 493291 = 739937) B739937
theorem B493303 : Blo 491791 493303 := bstep (se 1 (by rfl) ⟨369977, by rfl⟩ : syracuseStep 493303 = 739955) B739955
theorem B493323 : Blo 491791 493323 := bstep (se 1 (by rfl) ⟨369992, by rfl⟩ : syracuseStep 493323 = 739985) B739985
theorem B493335 : Blo 491791 493335 := bstep (se 1 (by rfl) ⟨370001, by rfl⟩ : syracuseStep 493335 = 740003) B740003
theorem B493355 : Blo 491791 493355 := bstep (se 1 (by rfl) ⟨370016, by rfl⟩ : syracuseStep 493355 = 740033) B740033
theorem B493367 : Blo 491791 493367 := bstep (se 1 (by rfl) ⟨370025, by rfl⟩ : syracuseStep 493367 = 740051) B740051
theorem B3999563 : Blo 491791 3999563 := bstep (se 1 (by rfl) ⟨2999672, by rfl⟩ : syracuseStep 3999563 = 5999345) B5999345
theorem B493387 : Blo 491791 493387 := bstep (se 1 (by rfl) ⟨370040, by rfl⟩ : syracuseStep 493387 = 740081) B740081
theorem B493399 : Blo 491791 493399 := bstep (se 1 (by rfl) ⟨370049, by rfl⟩ : syracuseStep 493399 = 740099) B740099
theorem B2819933 : Blo 491791 2819933 := bstep (se 3 (by rfl) ⟨528737, by rfl⟩ : syracuseStep 2819933 = 1057475) B1057475
theorem B493419 : Blo 491791 493419 := bstep (se 1 (by rfl) ⟨370064, by rfl⟩ : syracuseStep 493419 = 740129) B740129
theorem B9045877 : Blo 491791 9045877 := bstep (se 5 (by rfl) ⟨424025, by rfl⟩ : syracuseStep 9045877 = 848051) B848051
theorem B493431 : Blo 491791 493431 := bstep (se 1 (by rfl) ⟨370073, by rfl⟩ : syracuseStep 493431 = 740147) B740147
theorem B493451 : Blo 491791 493451 := bstep (se 1 (by rfl) ⟨370088, by rfl⟩ : syracuseStep 493451 = 740177) B740177
theorem B493463 : Blo 491791 493463 := bstep (se 1 (by rfl) ⟨370097, by rfl⟩ : syracuseStep 493463 = 740195) B740195
theorem B493483 : Blo 491791 493483 := bstep (se 1 (by rfl) ⟨370112, by rfl⟩ : syracuseStep 493483 = 740225) B740225
theorem B493495 : Blo 491791 493495 := bstep (se 1 (by rfl) ⟨370121, by rfl⟩ : syracuseStep 493495 = 740243) B740243
theorem B493515 : Blo 491791 493515 := bstep (se 1 (by rfl) ⟨370136, by rfl⟩ : syracuseStep 493515 = 740273) B740273
theorem B493527 : Blo 491791 493527 := bstep (se 1 (by rfl) ⟨370145, by rfl⟩ : syracuseStep 493527 = 740291) B740291
theorem B886745 : Blo 491791 886745 := bstep (se 2 (by rfl) ⟨332529, by rfl⟩ : syracuseStep 886745 = 665059) B665059
theorem B493547 : Blo 491791 493547 := bstep (se 1 (by rfl) ⟨370160, by rfl⟩ : syracuseStep 493547 = 740321) B740321
theorem B493559 : Blo 491791 493559 := bstep (se 1 (by rfl) ⟨370169, by rfl⟩ : syracuseStep 493559 = 740339) B740339
theorem B493579 : Blo 491791 493579 := bstep (se 1 (by rfl) ⟨370184, by rfl⟩ : syracuseStep 493579 = 740369) B740369
theorem B493591 : Blo 491791 493591 := bstep (se 1 (by rfl) ⟨370193, by rfl⟩ : syracuseStep 493591 = 740387) B740387
theorem B493611 : Blo 491791 493611 := bstep (se 1 (by rfl) ⟨370208, by rfl⟩ : syracuseStep 493611 = 740417) B740417
theorem B493623 : Blo 491791 493623 := bstep (se 1 (by rfl) ⟨370217, by rfl⟩ : syracuseStep 493623 = 740435) B740435
theorem B493643 : Blo 491791 493643 := bstep (se 1 (by rfl) ⟨370232, by rfl⟩ : syracuseStep 493643 = 740465) B740465
theorem B493655 : Blo 491791 493655 := bstep (se 1 (by rfl) ⟨370241, by rfl⟩ : syracuseStep 493655 = 740483) B740483
theorem B493675 : Blo 491791 493675 := bstep (se 1 (by rfl) ⟨370256, by rfl⟩ : syracuseStep 493675 = 740513) B740513
theorem B493687 : Blo 491791 493687 := bstep (se 1 (by rfl) ⟨370265, by rfl⟩ : syracuseStep 493687 = 740531) B740531
theorem B493707 : Blo 491791 493707 := bstep (se 1 (by rfl) ⟨370280, by rfl⟩ : syracuseStep 493707 = 740561) B740561
theorem B493719 : Blo 491791 493719 := bstep (se 1 (by rfl) ⟨370289, by rfl⟩ : syracuseStep 493719 = 740579) B740579
theorem B493739 : Blo 491791 493739 := bstep (se 1 (by rfl) ⟨370304, by rfl⟩ : syracuseStep 493739 = 740609) B740609
theorem B1050803 : Blo 491791 1050803 := bstep (se 1 (by rfl) ⟨788102, by rfl⟩ : syracuseStep 1050803 = 1576205) B1576205
theorem B493751 : Blo 491791 493751 := bstep (se 1 (by rfl) ⟨370313, by rfl⟩ : syracuseStep 493751 = 740627) B740627
theorem B493771 : Blo 491791 493771 := bstep (se 1 (by rfl) ⟨370328, by rfl⟩ : syracuseStep 493771 = 740657) B740657
theorem B493783 : Blo 491791 493783 := bstep (se 1 (by rfl) ⟨370337, by rfl⟩ : syracuseStep 493783 = 740675) B740675
theorem B493803 : Blo 491791 493803 := bstep (se 1 (by rfl) ⟨370352, by rfl⟩ : syracuseStep 493803 = 740705) B740705
theorem B493815 : Blo 491791 493815 := bstep (se 1 (by rfl) ⟨370361, by rfl⟩ : syracuseStep 493815 = 740723) B740723
theorem B493835 : Blo 491791 493835 := bstep (se 1 (by rfl) ⟨370376, by rfl⟩ : syracuseStep 493835 = 740753) B740753
theorem B493847 : Blo 491791 493847 := bstep (se 1 (by rfl) ⟨370385, by rfl⟩ : syracuseStep 493847 = 740771) B740771
theorem B493867 : Blo 491791 493867 := bstep (se 1 (by rfl) ⟨370400, by rfl⟩ : syracuseStep 493867 = 740801) B740801
theorem B493879 : Blo 491791 493879 := bstep (se 1 (by rfl) ⟨370409, by rfl⟩ : syracuseStep 493879 = 740819) B740819
theorem B493899 : Blo 491791 493899 := bstep (se 1 (by rfl) ⟨370424, by rfl⟩ : syracuseStep 493899 = 740849) B740849
theorem B493911 : Blo 491791 493911 := bstep (se 1 (by rfl) ⟨370433, by rfl⟩ : syracuseStep 493911 = 740867) B740867
theorem B493931 : Blo 491791 493931 := bstep (se 1 (by rfl) ⟨370448, by rfl⟩ : syracuseStep 493931 = 740897) B740897
theorem B493943 : Blo 491791 493943 := bstep (se 1 (by rfl) ⟨370457, by rfl⟩ : syracuseStep 493943 = 740915) B740915
theorem B493963 : Blo 491791 493963 := bstep (se 1 (by rfl) ⟨370472, by rfl⟩ : syracuseStep 493963 = 740945) B740945
theorem B493975 : Blo 491791 493975 := bstep (se 1 (by rfl) ⟨370481, by rfl⟩ : syracuseStep 493975 = 740963) B740963
theorem B493995 : Blo 491791 493995 := bstep (se 1 (by rfl) ⟨370496, by rfl⟩ : syracuseStep 493995 = 740993) B740993
theorem B494007 : Blo 491791 494007 := bstep (se 1 (by rfl) ⟨370505, by rfl⟩ : syracuseStep 494007 = 741011) B741011
theorem B494027 : Blo 491791 494027 := bstep (se 1 (by rfl) ⟨370520, by rfl⟩ : syracuseStep 494027 = 741041) B741041
theorem B494039 : Blo 491791 494039 := bstep (se 1 (by rfl) ⟨370529, by rfl⟩ : syracuseStep 494039 = 741059) B741059
theorem B494059 : Blo 491791 494059 := bstep (se 1 (by rfl) ⟨370544, by rfl⟩ : syracuseStep 494059 = 741089) B741089
theorem B494071 : Blo 491791 494071 := bstep (se 1 (by rfl) ⟨370553, by rfl⟩ : syracuseStep 494071 = 741107) B741107
theorem B494091 : Blo 491791 494091 := bstep (se 1 (by rfl) ⟨370568, by rfl⟩ : syracuseStep 494091 = 741137) B741137
theorem B526871 : Blo 491791 526871 := bstep (se 1 (by rfl) ⟨395153, by rfl⟩ : syracuseStep 526871 = 790307) B790307
theorem B494103 : Blo 491791 494103 := bstep (se 1 (by rfl) ⟨370577, by rfl⟩ : syracuseStep 494103 = 741155) B741155
theorem B1411607 : Blo 491791 1411607 := bstep (se 1 (by rfl) ⟨1058705, by rfl⟩ : syracuseStep 1411607 = 2117411) B2117411
theorem B494123 : Blo 491791 494123 := bstep (se 1 (by rfl) ⟨370592, by rfl⟩ : syracuseStep 494123 = 741185) B741185
theorem B1247795 : Blo 491791 1247795 := bstep (se 1 (by rfl) ⟨935846, by rfl⟩ : syracuseStep 1247795 = 1871693) B1871693
theorem B494135 : Blo 491791 494135 := bstep (se 1 (by rfl) ⟨370601, by rfl⟩ : syracuseStep 494135 = 741203) B741203
theorem B494155 : Blo 491791 494155 := bstep (se 1 (by rfl) ⟨370616, by rfl⟩ : syracuseStep 494155 = 741233) B741233
theorem B2820683 : Blo 491791 2820683 := bstep (se 1 (by rfl) ⟨2115512, by rfl⟩ : syracuseStep 2820683 = 4231025) B4231025
theorem B494167 : Blo 491791 494167 := bstep (se 1 (by rfl) ⟨370625, by rfl⟩ : syracuseStep 494167 = 741251) B741251
theorem B494187 : Blo 491791 494187 := bstep (se 1 (by rfl) ⟨370640, by rfl⟩ : syracuseStep 494187 = 741281) B741281
theorem B494199 : Blo 491791 494199 := bstep (se 1 (by rfl) ⟨370649, by rfl⟩ : syracuseStep 494199 = 741299) B741299
theorem B494219 : Blo 491791 494219 := bstep (se 1 (by rfl) ⟨370664, by rfl⟩ : syracuseStep 494219 = 741329) B741329
theorem B494231 : Blo 491791 494231 := bstep (se 1 (by rfl) ⟨370673, by rfl⟩ : syracuseStep 494231 = 741347) B741347
theorem B494251 : Blo 491791 494251 := bstep (se 1 (by rfl) ⟨370688, by rfl⟩ : syracuseStep 494251 = 741377) B741377
theorem B494263 : Blo 491791 494263 := bstep (se 1 (by rfl) ⟨370697, by rfl⟩ : syracuseStep 494263 = 741395) B741395
theorem B494283 : Blo 491791 494283 := bstep (se 1 (by rfl) ⟨370712, by rfl⟩ : syracuseStep 494283 = 741425) B741425
theorem B494295 : Blo 491791 494295 := bstep (se 1 (by rfl) ⟨370721, by rfl⟩ : syracuseStep 494295 = 741443) B741443
theorem B1870553 : Blo 491791 1870553 := bstep (se 2 (by rfl) ⟨701457, by rfl⟩ : syracuseStep 1870553 = 1402915) B1402915
theorem B494315 : Blo 491791 494315 := bstep (se 1 (by rfl) ⟨370736, by rfl⟩ : syracuseStep 494315 = 741473) B741473
theorem B494327 : Blo 491791 494327 := bstep (se 1 (by rfl) ⟨370745, by rfl⟩ : syracuseStep 494327 = 741491) B741491
theorem B1051393 : Blo 491791 1051393 := bstep (se 2 (by rfl) ⟨394272, by rfl⟩ : syracuseStep 1051393 = 788545) B788545
theorem B494347 : Blo 491791 494347 := bstep (se 1 (by rfl) ⟨370760, by rfl⟩ : syracuseStep 494347 = 741521) B741521
theorem B494359 : Blo 491791 494359 := bstep (se 1 (by rfl) ⟨370769, by rfl⟩ : syracuseStep 494359 = 741539) B741539
theorem B494379 : Blo 491791 494379 := bstep (se 1 (by rfl) ⟨370784, by rfl⟩ : syracuseStep 494379 = 741569) B741569
theorem B494391 : Blo 491791 494391 := bstep (se 1 (by rfl) ⟨370793, by rfl⟩ : syracuseStep 494391 = 741587) B741587
theorem B494411 : Blo 491791 494411 := bstep (se 1 (by rfl) ⟨370808, by rfl⟩ : syracuseStep 494411 = 741617) B741617
theorem B494423 : Blo 491791 494423 := bstep (se 1 (by rfl) ⟨370817, by rfl⟩ : syracuseStep 494423 = 741635) B741635
theorem B494443 : Blo 491791 494443 := bstep (se 1 (by rfl) ⟨370832, by rfl⟩ : syracuseStep 494443 = 741665) B741665
theorem B494455 : Blo 491791 494455 := bstep (se 1 (by rfl) ⟨370841, by rfl⟩ : syracuseStep 494455 = 741683) B741683
theorem B494475 : Blo 491791 494475 := bstep (se 1 (by rfl) ⟨370856, by rfl⟩ : syracuseStep 494475 = 741713) B741713
theorem B494487 : Blo 491791 494487 := bstep (se 1 (by rfl) ⟨370865, by rfl⟩ : syracuseStep 494487 = 741731) B741731
theorem B494507 : Blo 491791 494507 := bstep (se 1 (by rfl) ⟨370880, by rfl⟩ : syracuseStep 494507 = 741761) B741761
theorem B13536179 : Blo 491791 13536179 := bstep (se 1 (by rfl) ⟨10152134, by rfl⟩ : syracuseStep 13536179 = 20304269) B20304269
theorem B494519 : Blo 491791 494519 := bstep (se 1 (by rfl) ⟨370889, by rfl⟩ : syracuseStep 494519 = 741779) B741779
theorem B494539 : Blo 491791 494539 := bstep (se 1 (by rfl) ⟨370904, by rfl⟩ : syracuseStep 494539 = 741809) B741809
theorem B494551 : Blo 491791 494551 := bstep (se 1 (by rfl) ⟨370913, by rfl⟩ : syracuseStep 494551 = 741827) B741827
theorem B494571 : Blo 491791 494571 := bstep (se 1 (by rfl) ⟨370928, by rfl⟩ : syracuseStep 494571 = 741857) B741857
theorem B494583 : Blo 491791 494583 := bstep (se 1 (by rfl) ⟨370937, by rfl⟩ : syracuseStep 494583 = 741875) B741875
theorem B494603 : Blo 491791 494603 := bstep (se 1 (by rfl) ⟨370952, by rfl⟩ : syracuseStep 494603 = 741905) B741905
theorem B494615 : Blo 491791 494615 := bstep (se 1 (by rfl) ⟨370961, by rfl⟩ : syracuseStep 494615 = 741923) B741923
theorem B494635 : Blo 491791 494635 := bstep (se 1 (by rfl) ⟨370976, by rfl⟩ : syracuseStep 494635 = 741953) B741953
theorem B494647 : Blo 491791 494647 := bstep (se 1 (by rfl) ⟨370985, by rfl⟩ : syracuseStep 494647 = 741971) B741971
theorem B1248331 : Blo 491791 1248331 := bstep (se 1 (by rfl) ⟨936248, by rfl⟩ : syracuseStep 1248331 = 1872497) B1872497
theorem B494667 : Blo 491791 494667 := bstep (se 1 (by rfl) ⟨371000, by rfl⟩ : syracuseStep 494667 = 742001) B742001
theorem B494679 : Blo 491791 494679 := bstep (se 1 (by rfl) ⟨371009, by rfl⟩ : syracuseStep 494679 = 742019) B742019
theorem B494699 : Blo 491791 494699 := bstep (se 1 (by rfl) ⟨371024, by rfl⟩ : syracuseStep 494699 = 742049) B742049
theorem B494711 : Blo 491791 494711 := bstep (se 1 (by rfl) ⟨371033, by rfl⟩ : syracuseStep 494711 = 742067) B742067
theorem B494731 : Blo 491791 494731 := bstep (se 1 (by rfl) ⟨371048, by rfl⟩ : syracuseStep 494731 = 742097) B742097
theorem B494743 : Blo 491791 494743 := bstep (se 1 (by rfl) ⟨371057, by rfl⟩ : syracuseStep 494743 = 742115) B742115
theorem B494763 : Blo 491791 494763 := bstep (se 1 (by rfl) ⟨371072, by rfl⟩ : syracuseStep 494763 = 742145) B742145
theorem B494775 : Blo 491791 494775 := bstep (se 1 (by rfl) ⟨371081, by rfl⟩ : syracuseStep 494775 = 742163) B742163
theorem B527563 : Blo 491791 527563 := bstep (se 1 (by rfl) ⟨395672, by rfl⟩ : syracuseStep 527563 = 791345) B791345
theorem B494795 : Blo 491791 494795 := bstep (se 1 (by rfl) ⟨371096, by rfl⟩ : syracuseStep 494795 = 742193) B742193
theorem B494807 : Blo 491791 494807 := bstep (se 1 (by rfl) ⟨371105, by rfl⟩ : syracuseStep 494807 = 742211) B742211
theorem B1248473 : Blo 491791 1248473 := bstep (se 2 (by rfl) ⟨468177, by rfl⟩ : syracuseStep 1248473 = 936355) B936355
theorem B494827 : Blo 491791 494827 := bstep (se 1 (by rfl) ⟨371120, by rfl⟩ : syracuseStep 494827 = 742241) B742241
theorem B494839 : Blo 491791 494839 := bstep (se 1 (by rfl) ⟨371129, by rfl⟩ : syracuseStep 494839 = 742259) B742259
theorem B494859 : Blo 491791 494859 := bstep (se 1 (by rfl) ⟨371144, by rfl⟩ : syracuseStep 494859 = 742289) B742289
theorem B494871 : Blo 491791 494871 := bstep (se 1 (by rfl) ⟨371153, by rfl⟩ : syracuseStep 494871 = 742307) B742307
theorem B494891 : Blo 491791 494891 := bstep (se 1 (by rfl) ⟨371168, by rfl⟩ : syracuseStep 494891 = 742337) B742337
theorem B494903 : Blo 491791 494903 := bstep (se 1 (by rfl) ⟨371177, by rfl⟩ : syracuseStep 494903 = 742355) B742355
theorem B494923 : Blo 491791 494923 := bstep (se 1 (by rfl) ⟨371192, by rfl⟩ : syracuseStep 494923 = 742385) B742385
theorem B494935 : Blo 491791 494935 := bstep (se 1 (by rfl) ⟨371201, by rfl⟩ : syracuseStep 494935 = 742403) B742403
theorem B494955 : Blo 491791 494955 := bstep (se 1 (by rfl) ⟨371216, by rfl⟩ : syracuseStep 494955 = 742433) B742433
theorem B494967 : Blo 491791 494967 := bstep (se 1 (by rfl) ⟨371225, by rfl⟩ : syracuseStep 494967 = 742451) B742451
theorem B2493827 : Blo 491791 2493827 := bstep (se 1 (by rfl) ⟨1870370, by rfl⟩ : syracuseStep 2493827 = 3740741) B3740741
theorem B626059 : Blo 491791 626059 := bstep (se 1 (by rfl) ⟨469544, by rfl⟩ : syracuseStep 626059 = 939089) B939089
theorem B494987 : Blo 491791 494987 := bstep (se 1 (by rfl) ⟨371240, by rfl⟩ : syracuseStep 494987 = 742481) B742481
theorem B494999 : Blo 491791 494999 := bstep (se 1 (by rfl) ⟨371249, by rfl⟩ : syracuseStep 494999 = 742499) B742499
theorem B495019 : Blo 491791 495019 := bstep (se 1 (by rfl) ⟨371264, by rfl⟩ : syracuseStep 495019 = 742529) B742529
theorem B495031 : Blo 491791 495031 := bstep (se 1 (by rfl) ⟨371273, by rfl⟩ : syracuseStep 495031 = 742547) B742547
theorem B495051 : Blo 491791 495051 := bstep (se 1 (by rfl) ⟨371288, by rfl⟩ : syracuseStep 495051 = 742577) B742577
theorem B495063 : Blo 491791 495063 := bstep (se 1 (by rfl) ⟨371297, by rfl⟩ : syracuseStep 495063 = 742595) B742595
theorem B495083 : Blo 491791 495083 := bstep (se 1 (by rfl) ⟨371312, by rfl⟩ : syracuseStep 495083 = 742625) B742625
theorem B495095 : Blo 491791 495095 := bstep (se 1 (by rfl) ⟨371321, by rfl⟩ : syracuseStep 495095 = 742643) B742643
theorem B495115 : Blo 491791 495115 := bstep (se 1 (by rfl) ⟨371336, by rfl⟩ : syracuseStep 495115 = 742673) B742673
theorem B495127 : Blo 491791 495127 := bstep (se 1 (by rfl) ⟨371345, by rfl⟩ : syracuseStep 495127 = 742691) B742691
theorem B495147 : Blo 491791 495147 := bstep (se 1 (by rfl) ⟨371360, by rfl⟩ : syracuseStep 495147 = 742721) B742721
theorem B495159 : Blo 491791 495159 := bstep (se 1 (by rfl) ⟨371369, by rfl⟩ : syracuseStep 495159 = 742739) B742739
theorem B2428481 : Blo 491791 2428481 := bstep (se 2 (by rfl) ⟨910680, by rfl⟩ : syracuseStep 2428481 = 1821361) B1821361
theorem B1281611 : Blo 491791 1281611 := bstep (se 1 (by rfl) ⟨961208, by rfl⟩ : syracuseStep 1281611 = 1922417) B1922417
theorem B495179 : Blo 491791 495179 := bstep (se 1 (by rfl) ⟨371384, by rfl⟩ : syracuseStep 495179 = 742769) B742769
theorem B495191 : Blo 491791 495191 := bstep (se 1 (by rfl) ⟨371393, by rfl⟩ : syracuseStep 495191 = 742787) B742787
theorem B495211 : Blo 491791 495211 := bstep (se 1 (by rfl) ⟨371408, by rfl⟩ : syracuseStep 495211 = 742817) B742817
theorem B495223 : Blo 491791 495223 := bstep (se 1 (by rfl) ⟨371417, by rfl⟩ : syracuseStep 495223 = 742835) B742835
theorem B495243 : Blo 491791 495243 := bstep (se 1 (by rfl) ⟨371432, by rfl⟩ : syracuseStep 495243 = 742865) B742865
theorem B2100887 : Blo 491791 2100887 := bstep (se 1 (by rfl) ⟨1575665, by rfl⟩ : syracuseStep 2100887 = 3151331) B3151331
theorem B495255 : Blo 491791 495255 := bstep (se 1 (by rfl) ⟨371441, by rfl⟩ : syracuseStep 495255 = 742883) B742883
theorem B495275 : Blo 491791 495275 := bstep (se 1 (by rfl) ⟨371456, by rfl⟩ : syracuseStep 495275 = 742913) B742913
theorem B495287 : Blo 491791 495287 := bstep (se 1 (by rfl) ⟨371465, by rfl⟩ : syracuseStep 495287 = 742931) B742931
theorem B495307 : Blo 491791 495307 := bstep (se 1 (by rfl) ⟨371480, by rfl⟩ : syracuseStep 495307 = 742961) B742961
theorem B495319 : Blo 491791 495319 := bstep (se 1 (by rfl) ⟨371489, by rfl⟩ : syracuseStep 495319 = 742979) B742979
theorem B495339 : Blo 491791 495339 := bstep (se 1 (by rfl) ⟨371504, by rfl⟩ : syracuseStep 495339 = 743009) B743009
theorem B495351 : Blo 491791 495351 := bstep (se 1 (by rfl) ⟨371513, by rfl⟩ : syracuseStep 495351 = 743027) B743027
theorem B495371 : Blo 491791 495371 := bstep (se 1 (by rfl) ⟨371528, by rfl⟩ : syracuseStep 495371 = 743057) B743057
theorem B495383 : Blo 491791 495383 := bstep (se 1 (by rfl) ⟨371537, by rfl⟩ : syracuseStep 495383 = 743075) B743075
theorem B495403 : Blo 491791 495403 := bstep (se 1 (by rfl) ⟨371552, by rfl⟩ : syracuseStep 495403 = 743105) B743105
theorem B495415 : Blo 491791 495415 := bstep (se 1 (by rfl) ⟨371561, by rfl⟩ : syracuseStep 495415 = 743123) B743123
theorem B495435 : Blo 491791 495435 := bstep (se 1 (by rfl) ⟨371576, by rfl⟩ : syracuseStep 495435 = 743153) B743153
theorem B495447 : Blo 491791 495447 := bstep (se 1 (by rfl) ⟨371585, by rfl⟩ : syracuseStep 495447 = 743171) B743171
theorem B1576793 : Blo 491791 1576793 := bstep (se 2 (by rfl) ⟨591297, by rfl⟩ : syracuseStep 1576793 = 1182595) B1182595
theorem B495467 : Blo 491791 495467 := bstep (se 1 (by rfl) ⟨371600, by rfl⟩ : syracuseStep 495467 = 743201) B743201
theorem B495479 : Blo 491791 495479 := bstep (se 1 (by rfl) ⟨371609, by rfl⟩ : syracuseStep 495479 = 743219) B743219
theorem B495499 : Blo 491791 495499 := bstep (se 1 (by rfl) ⟨371624, by rfl⟩ : syracuseStep 495499 = 743249) B743249
theorem B495511 : Blo 491791 495511 := bstep (se 1 (by rfl) ⟨371633, by rfl⟩ : syracuseStep 495511 = 743267) B743267
theorem B495531 : Blo 491791 495531 := bstep (se 1 (by rfl) ⟨371648, by rfl⟩ : syracuseStep 495531 = 743297) B743297
theorem B495543 : Blo 491791 495543 := bstep (se 1 (by rfl) ⟨371657, by rfl⟩ : syracuseStep 495543 = 743315) B743315
theorem B1183691 : Blo 491791 1183691 := bstep (se 1 (by rfl) ⟨887768, by rfl⟩ : syracuseStep 1183691 = 1775537) B1775537
theorem B495563 : Blo 491791 495563 := bstep (se 1 (by rfl) ⟨371672, by rfl⟩ : syracuseStep 495563 = 743345) B743345
theorem B495575 : Blo 491791 495575 := bstep (se 1 (by rfl) ⟨371681, by rfl⟩ : syracuseStep 495575 = 743363) B743363
theorem B495595 : Blo 491791 495595 := bstep (se 1 (by rfl) ⟨371696, by rfl⟩ : syracuseStep 495595 = 743393) B743393
theorem B495607 : Blo 491791 495607 := bstep (se 1 (by rfl) ⟨371705, by rfl⟩ : syracuseStep 495607 = 743411) B743411
theorem B495627 : Blo 491791 495627 := bstep (se 1 (by rfl) ⟨371720, by rfl⟩ : syracuseStep 495627 = 743441) B743441
theorem B1249303 : Blo 491791 1249303 := bstep (se 1 (by rfl) ⟨936977, by rfl⟩ : syracuseStep 1249303 = 1873955) B1873955
theorem B495639 : Blo 491791 495639 := bstep (se 1 (by rfl) ⟨371729, by rfl⟩ : syracuseStep 495639 = 743459) B743459
theorem B495659 : Blo 491791 495659 := bstep (se 1 (by rfl) ⟨371744, by rfl⟩ : syracuseStep 495659 = 743489) B743489
theorem B495671 : Blo 491791 495671 := bstep (se 1 (by rfl) ⟨371753, by rfl⟩ : syracuseStep 495671 = 743507) B743507
theorem B495691 : Blo 491791 495691 := bstep (se 1 (by rfl) ⟨371768, by rfl⟩ : syracuseStep 495691 = 743537) B743537
theorem B495703 : Blo 491791 495703 := bstep (se 1 (by rfl) ⟨371777, by rfl⟩ : syracuseStep 495703 = 743555) B743555
theorem B495723 : Blo 491791 495723 := bstep (se 1 (by rfl) ⟨371792, by rfl⟩ : syracuseStep 495723 = 743585) B743585
theorem B495735 : Blo 491791 495735 := bstep (se 1 (by rfl) ⟨371801, by rfl⟩ : syracuseStep 495735 = 743603) B743603
theorem B495755 : Blo 491791 495755 := bstep (se 1 (by rfl) ⟨371816, by rfl⟩ : syracuseStep 495755 = 743633) B743633
theorem B495767 : Blo 491791 495767 := bstep (se 1 (by rfl) ⟨371825, by rfl⟩ : syracuseStep 495767 = 743651) B743651
theorem B495787 : Blo 491791 495787 := bstep (se 1 (by rfl) ⟨371840, by rfl⟩ : syracuseStep 495787 = 743681) B743681
theorem B2822323 : Blo 491791 2822323 := bstep (se 1 (by rfl) ⟨2116742, by rfl⟩ : syracuseStep 2822323 = 4233485) B4233485
theorem B1052939 : Blo 491791 1052939 := bstep (se 1 (by rfl) ⟨789704, by rfl⟩ : syracuseStep 1052939 = 1579409) B1579409
theorem B1872179 : Blo 491791 1872179 := bstep (se 1 (by rfl) ⟨1404134, by rfl⟩ : syracuseStep 1872179 = 2808269) B2808269
theorem B1872193 : Blo 491791 1872193 := bstep (se 2 (by rfl) ⟨702072, by rfl⟩ : syracuseStep 1872193 = 1404145) B1404145
theorem B627031 : Blo 491791 627031 := bstep (se 1 (by rfl) ⟨470273, by rfl⟩ : syracuseStep 627031 = 940547) B940547
theorem B1249739 : Blo 491791 1249739 := bstep (se 1 (by rfl) ⟨937304, by rfl⟩ : syracuseStep 1249739 = 1874609) B1874609
theorem B561655 : Blo 491791 561655 := bstep (se 1 (by rfl) ⟨421241, by rfl⟩ : syracuseStep 561655 = 842483) B842483
theorem B528887 : Blo 491791 528887 := bstep (se 1 (by rfl) ⟨396665, by rfl⟩ : syracuseStep 528887 = 793331) B793331
theorem B529015 : Blo 491791 529015 := bstep (se 1 (by rfl) ⟨396761, by rfl⟩ : syracuseStep 529015 = 793523) B793523
theorem B1250113 : Blo 491791 1250113 := bstep (se 2 (by rfl) ⟨468792, by rfl⟩ : syracuseStep 1250113 = 937585) B937585
theorem B791383 : Blo 491791 791383 := bstep (se 1 (by rfl) ⟨593537, by rfl⟩ : syracuseStep 791383 = 1187075) B1187075
theorem B4232087 : Blo 491791 4232087 := bstep (se 1 (by rfl) ⟨3174065, by rfl⟩ : syracuseStep 4232087 = 6348131) B6348131
theorem B1053785 : Blo 491791 1053785 := bstep (se 2 (by rfl) ⟨395169, by rfl⟩ : syracuseStep 1053785 = 790339) B790339
theorem B2004227 : Blo 491791 2004227 := bstep (se 1 (by rfl) ⟨1503170, by rfl⟩ : syracuseStep 2004227 = 3006341) B3006341
theorem B1185047 : Blo 491791 1185047 := bstep (se 1 (by rfl) ⟨888785, by rfl⟩ : syracuseStep 1185047 = 1777571) B1777571
theorem B791947 : Blo 491791 791947 := bstep (se 1 (by rfl) ⟨593960, by rfl⟩ : syracuseStep 791947 = 1187921) B1187921
theorem B1250711 : Blo 491791 1250711 := bstep (se 1 (by rfl) ⟨938033, by rfl⟩ : syracuseStep 1250711 = 1876067) B1876067
theorem B792011 : Blo 491791 792011 := bstep (se 1 (by rfl) ⟨594008, by rfl⟩ : syracuseStep 792011 = 1188017) B1188017
theorem B1054579 : Blo 491791 1054579 := bstep (se 1 (by rfl) ⟨790934, by rfl⟩ : syracuseStep 1054579 = 1581869) B1581869
theorem B11409329 : Blo 491791 11409329 := bstep (se 2 (by rfl) ⟨4278498, by rfl⟩ : syracuseStep 11409329 = 8556997) B8556997
theorem B1578973 : Blo 491791 1578973 := bstep (se 3 (by rfl) ⟨296057, by rfl⟩ : syracuseStep 1578973 = 592115) B592115
theorem B3741713 : Blo 491791 3741713 := bstep (se 2 (by rfl) ⟨1403142, by rfl⟩ : syracuseStep 3741713 = 2806285) B2806285
theorem B2103347 : Blo 491791 2103347 := bstep (se 1 (by rfl) ⟨1577510, by rfl⟩ : syracuseStep 2103347 = 3155021) B3155021
theorem B1251521 : Blo 491791 1251521 := bstep (se 2 (by rfl) ⟨469320, by rfl⟩ : syracuseStep 1251521 = 938641) B938641
theorem B1874123 : Blo 491791 1874123 := bstep (se 1 (by rfl) ⟨1405592, by rfl⟩ : syracuseStep 1874123 = 2811185) B2811185
theorem B1874137 : Blo 491791 1874137 := bstep (se 2 (by rfl) ⟨702801, by rfl⟩ : syracuseStep 1874137 = 1405603) B1405603
theorem B792985 : Blo 491791 792985 := bstep (se 2 (by rfl) ⟨297369, by rfl⟩ : syracuseStep 792985 = 594739) B594739
theorem B891329 : Blo 491791 891329 := bstep (se 2 (by rfl) ⟨334248, by rfl⟩ : syracuseStep 891329 = 668497) B668497
theorem B3152459 : Blo 491791 3152459 := bstep (se 1 (by rfl) ⟨2364344, by rfl⟩ : syracuseStep 3152459 = 4728689) B4728689
theorem B793241 : Blo 491791 793241 := bstep (se 2 (by rfl) ⟨297465, by rfl⟩ : syracuseStep 793241 = 594931) B594931
theorem B1055425 : Blo 491791 1055425 := bstep (se 2 (by rfl) ⟨395784, by rfl⟩ : syracuseStep 1055425 = 791569) B791569
theorem B1252057 : Blo 491791 1252057 := bstep (se 2 (by rfl) ⟨469521, by rfl⟩ : syracuseStep 1252057 = 939043) B939043
theorem B793433 : Blo 491791 793433 := bstep (se 2 (by rfl) ⟨297537, by rfl⟩ : syracuseStep 793433 = 595075) B595075
theorem B2497553 : Blo 491791 2497553 := bstep (se 2 (by rfl) ⟨936582, by rfl⟩ : syracuseStep 2497553 = 1873165) B1873165
theorem B1055767 : Blo 491791 1055767 := bstep (se 1 (by rfl) ⟨791825, by rfl⟩ : syracuseStep 1055767 = 1583651) B1583651
theorem B1875095 : Blo 491791 1875095 := bstep (se 1 (by rfl) ⟨1406321, by rfl⟩ : syracuseStep 1875095 = 2812643) B2812643
theorem B2497715 : Blo 491791 2497715 := bstep (se 1 (by rfl) ⟨1873286, by rfl⟩ : syracuseStep 2497715 = 3746573) B3746573
theorem B1350877 : Blo 491791 1350877 := bstep (se 3 (by rfl) ⟨253289, by rfl⟩ : syracuseStep 1350877 = 506579) B506579
theorem B7577101 : Blo 491791 7577101 := bstep (se 3 (by rfl) ⟨1420706, by rfl⟩ : syracuseStep 7577101 = 2841413) B2841413
theorem B1187507 : Blo 491791 1187507 := bstep (se 1 (by rfl) ⟨890630, by rfl⟩ : syracuseStep 1187507 = 1781261) B1781261
theorem B1253171 : Blo 491791 1253171 := bstep (se 1 (by rfl) ⟨939878, by rfl⟩ : syracuseStep 1253171 = 1879757) B1879757
theorem B3383171 : Blo 491791 3383171 := bstep (se 1 (by rfl) ⟨2537378, by rfl⟩ : syracuseStep 3383171 = 5074757) B5074757
theorem B2105261 : Blo 491791 2105261 := bstep (se 3 (by rfl) ⟨394736, by rfl⟩ : syracuseStep 2105261 = 789473) B789473
theorem B1253465 : Blo 491791 1253465 := bstep (se 2 (by rfl) ⟨470049, by rfl⟩ : syracuseStep 1253465 = 940099) B940099
theorem B3154099 : Blo 491791 3154099 := bstep (se 1 (by rfl) ⟨2365574, by rfl⟩ : syracuseStep 3154099 = 4731149) B4731149
theorem B1056971 : Blo 491791 1056971 := bstep (se 1 (by rfl) ⟨792728, by rfl⟩ : syracuseStep 1056971 = 1585457) B1585457
theorem B5611841 : Blo 491791 5611841 := bstep (se 2 (by rfl) ⟨2104440, by rfl⟩ : syracuseStep 5611841 = 4208881) B4208881
theorem B1876355 : Blo 491791 1876355 := bstep (se 1 (by rfl) ⟨1407266, by rfl⟩ : syracuseStep 1876355 = 2814533) B2814533
theorem B500299 : Blo 491791 500299 := bstep (se 1 (by rfl) ⟨375224, by rfl⟩ : syracuseStep 500299 = 750449) B750449
theorem B2105945 : Blo 491791 2105945 := bstep (se 2 (by rfl) ⟨789729, by rfl⟩ : syracuseStep 2105945 = 1579459) B1579459
theorem B3383939 : Blo 491791 3383939 := bstep (se 1 (by rfl) ⟨2537954, by rfl⟩ : syracuseStep 3383939 = 5075909) B5075909
theorem B1057483 : Blo 491791 1057483 := bstep (se 1 (by rfl) ⟨793112, by rfl⟩ : syracuseStep 1057483 = 1586225) B1586225
theorem B1188631 : Blo 491791 1188631 := bstep (se 1 (by rfl) ⟨891473, by rfl⟩ : syracuseStep 1188631 = 1782947) B1782947
theorem B2663243 : Blo 491791 2663243 := bstep (se 1 (by rfl) ⟨1997432, by rfl⟩ : syracuseStep 2663243 = 3994865) B3994865
theorem B1778507 : Blo 491791 1778507 := bstep (se 1 (by rfl) ⟨1333880, by rfl⟩ : syracuseStep 1778507 = 2667761) B2667761
theorem B2499659 : Blo 491791 2499659 := bstep (se 1 (by rfl) ⟨1874744, by rfl⟩ : syracuseStep 2499659 = 3749489) B3749489
theorem B500951 : Blo 491791 500951 := bstep (se 1 (by rfl) ⟨375713, by rfl⟩ : syracuseStep 500951 = 751427) B751427
theorem B664907 : Blo 491791 664907 := bstep (se 1 (by rfl) ⟨498680, by rfl⟩ : syracuseStep 664907 = 997361) B997361
theorem B10855829 : Blo 491791 10855829 := bstep (se 6 (by rfl) ⟨254433, by rfl⟩ : syracuseStep 10855829 = 508867) B508867
theorem B1058201 : Blo 491791 1058201 := bstep (se 2 (by rfl) ⟨396825, by rfl⟩ : syracuseStep 1058201 = 793651) B793651
theorem B2107073 : Blo 491791 2107073 := bstep (se 2 (by rfl) ⟨790152, by rfl⟩ : syracuseStep 2107073 = 1580305) B1580305
theorem B35923661 : Blo 491791 35923661 := bstep (se 3 (by rfl) ⟨6735686, by rfl⟩ : syracuseStep 35923661 = 13471373) B13471373
theorem B1058611 : Blo 491791 1058611 := bstep (se 1 (by rfl) ⟨793958, by rfl⟩ : syracuseStep 1058611 = 1587917) B1587917
theorem B3745601 : Blo 491791 3745601 := bstep (se 2 (by rfl) ⟨1404600, by rfl⟩ : syracuseStep 3745601 = 2809201) B2809201
theorem B5122349 : Blo 491791 5122349 := bstep (se 3 (by rfl) ⟨960440, by rfl⟩ : syracuseStep 5122349 = 1920881) B1920881
theorem B830027 : Blo 491791 830027 := bstep (se 1 (by rfl) ⟨622520, by rfl⟩ : syracuseStep 830027 = 1245041) B1245041
theorem B502411 : Blo 491791 502411 := bstep (se 1 (by rfl) ⟨376808, by rfl⟩ : syracuseStep 502411 = 753617) B753617
theorem B830155 : Blo 491791 830155 := bstep (se 1 (by rfl) ⟨622616, by rfl⟩ : syracuseStep 830155 = 1245233) B1245233
theorem B2501441 : Blo 491791 2501441 := bstep (se 2 (by rfl) ⟨938040, by rfl⟩ : syracuseStep 2501441 = 1876081) B1876081
theorem B830297 : Blo 491791 830297 := bstep (se 2 (by rfl) ⟨311361, by rfl⟩ : syracuseStep 830297 = 622723) B622723
theorem B830425 : Blo 491791 830425 := bstep (se 2 (by rfl) ⟨311409, by rfl⟩ : syracuseStep 830425 = 622819) B622819
theorem B535627 : Blo 491791 535627 := bstep (se 1 (by rfl) ⟨401720, by rfl⟩ : syracuseStep 535627 = 803441) B803441
theorem B3288385 : Blo 491791 3288385 := bstep (se 2 (by rfl) ⟨1233144, by rfl⟩ : syracuseStep 3288385 = 2466289) B2466289
theorem B2108747 : Blo 491791 2108747 := bstep (se 1 (by rfl) ⟨1581560, by rfl⟩ : syracuseStep 2108747 = 3163121) B3163121
theorem B1879469 : Blo 491791 1879469 := bstep (se 3 (by rfl) ⟨352400, by rfl⟩ : syracuseStep 1879469 = 704801) B704801
theorem B830999 : Blo 491791 830999 := bstep (se 1 (by rfl) ⟨623249, by rfl⟩ : syracuseStep 830999 = 1246499) B1246499
theorem B831127 : Blo 491791 831127 := bstep (se 1 (by rfl) ⟨623345, by rfl⟩ : syracuseStep 831127 = 1246691) B1246691
theorem B2666201 : Blo 491791 2666201 := bstep (se 2 (by rfl) ⟨999825, by rfl⟩ : syracuseStep 2666201 = 1999651) B1999651
theorem B3747545 : Blo 491791 3747545 := bstep (se 2 (by rfl) ⟨1405329, by rfl⟩ : syracuseStep 3747545 = 2810659) B2810659
theorem B634711 : Blo 491791 634711 := bstep (se 1 (by rfl) ⟨476033, by rfl⟩ : syracuseStep 634711 = 952067) B952067
theorem B700427 : Blo 491791 700427 := bstep (se 1 (by rfl) ⟨525320, by rfl⟩ : syracuseStep 700427 = 1050641) B1050641
theorem B1880243 : Blo 491791 1880243 := bstep (se 1 (by rfl) ⟨1410182, by rfl⟩ : syracuseStep 1880243 = 2820365) B2820365
theorem B831755 : Blo 491791 831755 := bstep (se 1 (by rfl) ⟨623816, by rfl⟩ : syracuseStep 831755 = 1247633) B1247633
theorem B2404673 : Blo 491791 2404673 := bstep (se 2 (by rfl) ⟨901752, by rfl⟩ : syracuseStep 2404673 = 1803505) B1803505
theorem B831883 : Blo 491791 831883 := bstep (se 1 (by rfl) ⟨623912, by rfl⟩ : syracuseStep 831883 = 1247825) B1247825
theorem B832025 : Blo 491791 832025 := bstep (se 2 (by rfl) ⟨312009, by rfl⟩ : syracuseStep 832025 = 624019) B624019
theorem B1684061 : Blo 491791 1684061 := bstep (se 3 (by rfl) ⟨315761, by rfl⟩ : syracuseStep 1684061 = 631523) B631523
theorem B2110045 : Blo 491791 2110045 := bstep (se 3 (by rfl) ⟨395633, by rfl⟩ : syracuseStep 2110045 = 791267) B791267
theorem B832153 : Blo 491791 832153 := bstep (se 2 (by rfl) ⟨312057, by rfl⟩ : syracuseStep 832153 = 624115) B624115
theorem B1127105 : Blo 491791 1127105 := bstep (se 2 (by rfl) ⟨422664, by rfl⟩ : syracuseStep 1127105 = 845329) B845329
theorem B4764365 : Blo 491791 4764365 := bstep (se 3 (by rfl) ⟨893318, by rfl⟩ : syracuseStep 4764365 = 1786637) B1786637
theorem B2503385 : Blo 491791 2503385 := bstep (se 2 (by rfl) ⟨938769, by rfl⟩ : syracuseStep 2503385 = 1877539) B1877539
theorem B2143027 : Blo 491791 2143027 := bstep (se 1 (by rfl) ⟨1607270, by rfl⟩ : syracuseStep 2143027 = 3214541) B3214541
theorem B2372417 : Blo 491791 2372417 := bstep (se 2 (by rfl) ⟨889656, by rfl⟩ : syracuseStep 2372417 = 1779313) B1779313
theorem B1586071 : Blo 491791 1586071 := bstep (se 1 (by rfl) ⟨1189553, by rfl⟩ : syracuseStep 1586071 = 2379107) B2379107
theorem B2110387 : Blo 491791 2110387 := bstep (se 1 (by rfl) ⟨1582790, by rfl⟩ : syracuseStep 2110387 = 3165581) B3165581
theorem B701401 : Blo 491791 701401 := bstep (se 2 (by rfl) ⟨263025, by rfl⟩ : syracuseStep 701401 = 526051) B526051
theorem B832727 : Blo 491791 832727 := bstep (se 1 (by rfl) ⟨624545, by rfl⟩ : syracuseStep 832727 = 1249091) B1249091
theorem B832855 : Blo 491791 832855 := bstep (se 1 (by rfl) ⟨624641, by rfl⟩ : syracuseStep 832855 = 1249283) B1249283
theorem B1881731 : Blo 491791 1881731 := bstep (se 1 (by rfl) ⟨1411298, by rfl⟩ : syracuseStep 1881731 = 2822597) B2822597
theorem B1586891 : Blo 491791 1586891 := bstep (se 1 (by rfl) ⟨1190168, by rfl⟩ : syracuseStep 1586891 = 2380337) B2380337
theorem B833483 : Blo 491791 833483 := bstep (se 1 (by rfl) ⟨625112, by rfl⟩ : syracuseStep 833483 = 1250225) B1250225
theorem B997427 : Blo 491791 997427 := bstep (se 1 (by rfl) ⟨748070, by rfl⟩ : syracuseStep 997427 = 1496141) B1496141
theorem B1685555 : Blo 491791 1685555 := bstep (se 1 (by rfl) ⟨1264166, by rfl⟩ : syracuseStep 1685555 = 2528333) B2528333
theorem B833611 : Blo 491791 833611 := bstep (se 1 (by rfl) ⟨625208, by rfl⟩ : syracuseStep 833611 = 1250417) B1250417
theorem B1882187 : Blo 491791 1882187 := bstep (se 1 (by rfl) ⟨1411640, by rfl⟩ : syracuseStep 1882187 = 2823281) B2823281
theorem B702551 : Blo 491791 702551 := bstep (se 1 (by rfl) ⟨526913, by rfl⟩ : syracuseStep 702551 = 1053827) B1053827
theorem B833753 : Blo 491791 833753 := bstep (se 2 (by rfl) ⟨312657, by rfl⟩ : syracuseStep 833753 = 625315) B625315
theorem B1882385 : Blo 491791 1882385 := bstep (se 2 (by rfl) ⟨705894, by rfl⟩ : syracuseStep 1882385 = 1411789) B1411789
theorem B2505005 : Blo 491791 2505005 := bstep (se 3 (by rfl) ⟨469688, by rfl⟩ : syracuseStep 2505005 = 939377) B939377
theorem B833881 : Blo 491791 833881 := bstep (se 2 (by rfl) ⟨312705, by rfl⟩ : syracuseStep 833881 = 625411) B625411
theorem B702859 : Blo 491791 702859 := bstep (se 1 (by rfl) ⟨527144, by rfl⟩ : syracuseStep 702859 = 1054289) B1054289
theorem B8010161 : Blo 491791 8010161 := bstep (se 2 (by rfl) ⟨3003810, by rfl⟩ : syracuseStep 8010161 = 6007621) B6007621
theorem B834455 : Blo 491791 834455 := bstep (se 1 (by rfl) ⟨625841, by rfl⟩ : syracuseStep 834455 = 1251683) B1251683
theorem B2145197 : Blo 491791 2145197 := bstep (se 3 (by rfl) ⟨402224, by rfl⟩ : syracuseStep 2145197 = 804449) B804449
theorem B7093261 : Blo 491791 7093261 := bstep (se 3 (by rfl) ⟨1329986, by rfl⟩ : syracuseStep 7093261 = 2659973) B2659973
theorem B834583 : Blo 491791 834583 := bstep (se 1 (by rfl) ⟨625937, by rfl⟩ : syracuseStep 834583 = 1251875) B1251875
theorem B3750947 : Blo 491791 3750947 := bstep (se 1 (by rfl) ⟨2813210, by rfl⟩ : syracuseStep 3750947 = 5626421) B5626421
theorem B4013387 : Blo 491791 4013387 := bstep (se 1 (by rfl) ⟨3010040, by rfl⟩ : syracuseStep 4013387 = 6020081) B6020081
theorem B703895 : Blo 491791 703895 := bstep (se 1 (by rfl) ⟨527921, by rfl⟩ : syracuseStep 703895 = 1055843) B1055843
theorem B867737 : Blo 491791 867737 := bstep (se 2 (by rfl) ⟨325401, by rfl⟩ : syracuseStep 867737 = 650803) B650803
theorem B3554765 : Blo 491791 3554765 := bstep (se 3 (by rfl) ⟨666518, by rfl⟩ : syracuseStep 3554765 = 1333037) B1333037
theorem B2375185 : Blo 491791 2375185 := bstep (se 2 (by rfl) ⟨890694, by rfl⟩ : syracuseStep 2375185 = 1781389) B1781389
theorem B2539025 : Blo 491791 2539025 := bstep (se 2 (by rfl) ⟨952134, by rfl⟩ : syracuseStep 2539025 = 1904269) B1904269
theorem B3391051 : Blo 491791 3391051 := bstep (se 1 (by rfl) ⟨2543288, by rfl⟩ : syracuseStep 3391051 = 5086577) B5086577
theorem B704089 : Blo 491791 704089 := bstep (se 2 (by rfl) ⟨264033, by rfl⟩ : syracuseStep 704089 = 528067) B528067
theorem B2637413 : Blo 491791 2637413 := bstep (se 4 (by rfl) ⟨247257, by rfl⟩ : syracuseStep 2637413 = 494515) B494515
theorem B835211 : Blo 491791 835211 := bstep (se 1 (by rfl) ⟨626408, by rfl⟩ : syracuseStep 835211 = 1252817) B1252817
theorem B835339 : Blo 491791 835339 := bstep (se 1 (by rfl) ⟨626504, by rfl⟩ : syracuseStep 835339 = 1253009) B1253009
theorem B5062445 : Blo 491791 5062445 := bstep (se 3 (by rfl) ⟨949208, by rfl⟩ : syracuseStep 5062445 = 1898417) B1898417
theorem B966451 : Blo 491791 966451 := bstep (se 1 (by rfl) ⟨724838, by rfl⟩ : syracuseStep 966451 = 1449677) B1449677
theorem B933697 : Blo 491791 933697 := bstep (se 2 (by rfl) ⟨350136, by rfl⟩ : syracuseStep 933697 = 700273) B700273
theorem B999307 : Blo 491791 999307 := bstep (se 1 (by rfl) ⟨749480, by rfl⟩ : syracuseStep 999307 = 1498961) B1498961
theorem B835481 : Blo 491791 835481 := bstep (se 2 (by rfl) ⟨313305, by rfl⟩ : syracuseStep 835481 = 626611) B626611
theorem B10698713 : Blo 491791 10698713 := bstep (se 2 (by rfl) ⟨4012017, by rfl⟩ : syracuseStep 10698713 = 8024035) B8024035
theorem B835609 : Blo 491791 835609 := bstep (se 2 (by rfl) ⟨313353, by rfl⟩ : syracuseStep 835609 = 626707) B626707
theorem B2801729 : Blo 491791 2801729 := bstep (se 2 (by rfl) ⟨1050648, by rfl⟩ : syracuseStep 2801729 = 2101297) B2101297
theorem B4210865 : Blo 491791 4210865 := bstep (se 2 (by rfl) ⟨1579074, by rfl⟩ : syracuseStep 4210865 = 3158149) B3158149
theorem B1622209 : Blo 491791 1622209 := bstep (se 2 (by rfl) ⟨608328, by rfl⟩ : syracuseStep 1622209 = 1216657) B1216657
theorem B4014353 : Blo 491791 4014353 := bstep (se 2 (by rfl) ⟨1505382, by rfl⟩ : syracuseStep 4014353 = 3010765) B3010765
theorem B737687 : Blo 491791 737687 := bstep (se 1 (by rfl) ⟨553265, by rfl⟩ : syracuseStep 737687 = 1106531) B1106531
theorem B737753 : Blo 491791 737753 := bstep (se 2 (by rfl) ⟨276657, by rfl⟩ : syracuseStep 737753 = 553315) B553315
theorem B2114009 : Blo 491791 2114009 := bstep (se 2 (by rfl) ⟨792753, by rfl⟩ : syracuseStep 2114009 = 1585507) B1585507
theorem B934411 : Blo 491791 934411 := bstep (se 1 (by rfl) ⟨700808, by rfl⟩ : syracuseStep 934411 = 1401617) B1401617
theorem B3555857 : Blo 491791 3555857 := bstep (se 2 (by rfl) ⟨1333446, by rfl⟩ : syracuseStep 3555857 = 2666893) B2666893
theorem B5685835 : Blo 491791 5685835 := bstep (se 1 (by rfl) ⟨4264376, by rfl⟩ : syracuseStep 5685835 = 8528753) B8528753
theorem B737867 : Blo 491791 737867 := bstep (se 1 (by rfl) ⟨553400, by rfl⟩ : syracuseStep 737867 = 1106801) B1106801
theorem B737879 : Blo 491791 737879 := bstep (se 1 (by rfl) ⟨553409, by rfl⟩ : syracuseStep 737879 = 1106819) B1106819
theorem B934487 : Blo 491791 934487 := bstep (se 1 (by rfl) ⟨700865, by rfl⟩ : syracuseStep 934487 = 1401731) B1401731
theorem B836183 : Blo 491791 836183 := bstep (se 1 (by rfl) ⟨627137, by rfl⟩ : syracuseStep 836183 = 1254275) B1254275
theorem B737945 : Blo 491791 737945 := bstep (se 2 (by rfl) ⟨276729, by rfl⟩ : syracuseStep 737945 = 553459) B553459
theorem B836311 : Blo 491791 836311 := bstep (se 1 (by rfl) ⟨627233, by rfl⟩ : syracuseStep 836311 = 1254467) B1254467
theorem B1622749 : Blo 491791 1622749 := bstep (se 3 (by rfl) ⟨304265, by rfl⟩ : syracuseStep 1622749 = 608531) B608531
theorem B738059 : Blo 491791 738059 := bstep (se 1 (by rfl) ⟨553544, by rfl⟩ : syracuseStep 738059 = 1107089) B1107089
theorem B738071 : Blo 491791 738071 := bstep (se 1 (by rfl) ⟨553553, by rfl⟩ : syracuseStep 738071 = 1107107) B1107107
theorem B738137 : Blo 491791 738137 := bstep (se 2 (by rfl) ⟨276801, by rfl⟩ : syracuseStep 738137 = 553603) B553603
theorem B3031901 : Blo 491791 3031901 := bstep (se 3 (by rfl) ⟨568481, by rfl⟩ : syracuseStep 3031901 = 1136963) B1136963
theorem B1000345 : Blo 491791 1000345 := bstep (se 2 (by rfl) ⟨375129, by rfl⟩ : syracuseStep 1000345 = 750259) B750259
theorem B5686193 : Blo 491791 5686193 := bstep (se 2 (by rfl) ⟨2132322, by rfl⟩ : syracuseStep 5686193 = 4264645) B4264645
theorem B738251 : Blo 491791 738251 := bstep (se 1 (by rfl) ⟨553688, by rfl⟩ : syracuseStep 738251 = 1107377) B1107377
theorem B738263 : Blo 491791 738263 := bstep (se 1 (by rfl) ⟨553697, by rfl⟩ : syracuseStep 738263 = 1107395) B1107395
theorem B705547 : Blo 491791 705547 := bstep (se 1 (by rfl) ⟨529160, by rfl⟩ : syracuseStep 705547 = 1058321) B1058321
theorem B738329 : Blo 491791 738329 := bstep (se 2 (by rfl) ⟨276873, by rfl⟩ : syracuseStep 738329 = 553747) B553747
theorem B738443 : Blo 491791 738443 := bstep (se 1 (by rfl) ⟨553832, by rfl⟩ : syracuseStep 738443 = 1107665) B1107665
theorem B738455 : Blo 491791 738455 := bstep (se 1 (by rfl) ⟨553841, by rfl⟩ : syracuseStep 738455 = 1107683) B1107683
theorem B738521 : Blo 491791 738521 := bstep (se 2 (by rfl) ⟨276945, by rfl⟩ : syracuseStep 738521 = 553891) B553891
theorem B935155 : Blo 491791 935155 := bstep (se 1 (by rfl) ⟨701366, by rfl⟩ : syracuseStep 935155 = 1402733) B1402733
theorem B738635 : Blo 491791 738635 := bstep (se 1 (by rfl) ⟨553976, by rfl⟩ : syracuseStep 738635 = 1107953) B1107953
theorem B738647 : Blo 491791 738647 := bstep (se 1 (by rfl) ⟨553985, by rfl⟩ : syracuseStep 738647 = 1107971) B1107971
theorem B738713 : Blo 491791 738713 := bstep (se 2 (by rfl) ⟨277017, by rfl⟩ : syracuseStep 738713 = 554035) B554035
theorem B935383 : Blo 491791 935383 := bstep (se 1 (by rfl) ⟨701537, by rfl⟩ : syracuseStep 935383 = 1403075) B1403075
theorem B738827 : Blo 491791 738827 := bstep (se 1 (by rfl) ⟨554120, by rfl⟩ : syracuseStep 738827 = 1108241) B1108241
theorem B738839 : Blo 491791 738839 := bstep (se 1 (by rfl) ⟨554129, by rfl⟩ : syracuseStep 738839 = 1108259) B1108259
theorem B935489 : Blo 491791 935489 := bstep (se 2 (by rfl) ⟨350808, by rfl⟩ : syracuseStep 935489 = 701617) B701617
theorem B1263179 : Blo 491791 1263179 := bstep (se 1 (by rfl) ⟨947384, by rfl⟩ : syracuseStep 1263179 = 1894769) B1894769
theorem B738905 : Blo 491791 738905 := bstep (se 2 (by rfl) ⟨277089, by rfl⟩ : syracuseStep 738905 = 554179) B554179
theorem B739019 : Blo 491791 739019 := bstep (se 1 (by rfl) ⟨554264, by rfl⟩ : syracuseStep 739019 = 1108529) B1108529
theorem B739031 : Blo 491791 739031 := bstep (se 1 (by rfl) ⟨554273, by rfl⟩ : syracuseStep 739031 = 1108547) B1108547
theorem B935641 : Blo 491791 935641 := bstep (se 2 (by rfl) ⟨350865, by rfl⟩ : syracuseStep 935641 = 701731) B701731
theorem B739097 : Blo 491791 739097 := bstep (se 2 (by rfl) ⟨277161, by rfl⟩ : syracuseStep 739097 = 554323) B554323
theorem B739211 : Blo 491791 739211 := bstep (se 1 (by rfl) ⟨554408, by rfl⟩ : syracuseStep 739211 = 1108817) B1108817
theorem B2246545 : Blo 491791 2246545 := bstep (se 2 (by rfl) ⟨842454, by rfl⟩ : syracuseStep 2246545 = 1684909) B1684909
theorem B739223 : Blo 491791 739223 := bstep (se 1 (by rfl) ⟨554417, by rfl⟩ : syracuseStep 739223 = 1108835) B1108835
theorem B739289 : Blo 491791 739289 := bstep (se 2 (by rfl) ⟨277233, by rfl⟩ : syracuseStep 739289 = 554467) B554467
theorem B903155 : Blo 491791 903155 := bstep (se 1 (by rfl) ⟨677366, by rfl⟩ : syracuseStep 903155 = 1354733) B1354733
theorem B2115649 : Blo 491791 2115649 := bstep (se 2 (by rfl) ⟨793368, by rfl⟩ : syracuseStep 2115649 = 1586737) B1586737
theorem B739403 : Blo 491791 739403 := bstep (se 1 (by rfl) ⟨554552, by rfl⟩ : syracuseStep 739403 = 1109105) B1109105
theorem B739415 : Blo 491791 739415 := bstep (se 1 (by rfl) ⟨554561, by rfl⟩ : syracuseStep 739415 = 1109123) B1109123
theorem B2508893 : Blo 491791 2508893 := bstep (se 3 (by rfl) ⟨470417, by rfl⟩ : syracuseStep 2508893 = 940835) B940835
theorem B739481 : Blo 491791 739481 := bstep (se 2 (by rfl) ⟨277305, by rfl⟩ : syracuseStep 739481 = 554611) B554611
theorem B1067201 : Blo 491791 1067201 := bstep (se 2 (by rfl) ⟨400200, by rfl⟩ : syracuseStep 1067201 = 800401) B800401
theorem B739595 : Blo 491791 739595 := bstep (se 1 (by rfl) ⟨554696, by rfl⟩ : syracuseStep 739595 = 1109393) B1109393
theorem B739607 : Blo 491791 739607 := bstep (se 1 (by rfl) ⟨554705, by rfl⟩ : syracuseStep 739607 = 1109411) B1109411
theorem B739673 : Blo 491791 739673 := bstep (se 2 (by rfl) ⟨277377, by rfl⟩ : syracuseStep 739673 = 554755) B554755
theorem B739787 : Blo 491791 739787 := bstep (se 1 (by rfl) ⟨554840, by rfl⟩ : syracuseStep 739787 = 1109681) B1109681
theorem B739799 : Blo 491791 739799 := bstep (se 1 (by rfl) ⟨554849, by rfl⟩ : syracuseStep 739799 = 1109699) B1109699
theorem B739865 : Blo 491791 739865 := bstep (se 2 (by rfl) ⟨277449, by rfl⟩ : syracuseStep 739865 = 554899) B554899
theorem B1690163 : Blo 491791 1690163 := bstep (se 1 (by rfl) ⟨1267622, by rfl⟩ : syracuseStep 1690163 = 2535245) B2535245
theorem B739979 : Blo 491791 739979 := bstep (se 1 (by rfl) ⟨554984, by rfl⟩ : syracuseStep 739979 = 1109969) B1109969
theorem B739991 : Blo 491791 739991 := bstep (se 1 (by rfl) ⟨554993, by rfl⟩ : syracuseStep 739991 = 1109987) B1109987
theorem B740057 : Blo 491791 740057 := bstep (se 2 (by rfl) ⟨277521, by rfl⟩ : syracuseStep 740057 = 555043) B555043
theorem B740171 : Blo 491791 740171 := bstep (se 1 (by rfl) ⟨555128, by rfl⟩ : syracuseStep 740171 = 1110257) B1110257
theorem B740183 : Blo 491791 740183 := bstep (se 1 (by rfl) ⟨555137, by rfl⟩ : syracuseStep 740183 = 1110275) B1110275
theorem B740249 : Blo 491791 740249 := bstep (se 2 (by rfl) ⟨277593, by rfl⟩ : syracuseStep 740249 = 555187) B555187
theorem B936947 : Blo 491791 936947 := bstep (se 1 (by rfl) ⟨702710, by rfl⟩ : syracuseStep 936947 = 1405421) B1405421
theorem B740363 : Blo 491791 740363 := bstep (se 1 (by rfl) ⟨555272, by rfl⟩ : syracuseStep 740363 = 1110545) B1110545
theorem B740375 : Blo 491791 740375 := bstep (se 1 (by rfl) ⟨555281, by rfl⟩ : syracuseStep 740375 = 1110563) B1110563
theorem B740441 : Blo 491791 740441 := bstep (se 2 (by rfl) ⟨277665, by rfl⟩ : syracuseStep 740441 = 555331) B555331
theorem B937099 : Blo 491791 937099 := bstep (se 1 (by rfl) ⟨702824, by rfl⟩ : syracuseStep 937099 = 1405649) B1405649
theorem B740555 : Blo 491791 740555 := bstep (se 1 (by rfl) ⟨555416, by rfl⟩ : syracuseStep 740555 = 1110833) B1110833
theorem B740567 : Blo 491791 740567 := bstep (se 1 (by rfl) ⟨555425, by rfl⟩ : syracuseStep 740567 = 1110851) B1110851
theorem B740633 : Blo 491791 740633 := bstep (se 2 (by rfl) ⟨277737, by rfl⟩ : syracuseStep 740633 = 555475) B555475
theorem B1625437 : Blo 491791 1625437 := bstep (se 3 (by rfl) ⟨304769, by rfl⟩ : syracuseStep 1625437 = 609539) B609539
theorem B740747 : Blo 491791 740747 := bstep (se 1 (by rfl) ⟨555560, by rfl⟩ : syracuseStep 740747 = 1111121) B1111121
theorem B740759 : Blo 491791 740759 := bstep (se 1 (by rfl) ⟨555569, by rfl⟩ : syracuseStep 740759 = 1111139) B1111139
theorem B937433 : Blo 491791 937433 := bstep (se 2 (by rfl) ⟨351537, by rfl⟩ : syracuseStep 937433 = 703075) B703075
theorem B740825 : Blo 491791 740825 := bstep (se 2 (by rfl) ⟨277809, by rfl⟩ : syracuseStep 740825 = 555619) B555619
theorem B3558917 : Blo 491791 3558917 := bstep (se 4 (by rfl) ⟨333648, by rfl⟩ : syracuseStep 3558917 = 667297) B667297
theorem B2117137 : Blo 491791 2117137 := bstep (se 2 (by rfl) ⟨793926, by rfl⟩ : syracuseStep 2117137 = 1587853) B1587853
theorem B3788333 : Blo 491791 3788333 := bstep (se 3 (by rfl) ⟨710312, by rfl⟩ : syracuseStep 3788333 = 1420625) B1420625
theorem B740939 : Blo 491791 740939 := bstep (se 1 (by rfl) ⟨555704, by rfl⟩ : syracuseStep 740939 = 1111409) B1111409
theorem B740951 : Blo 491791 740951 := bstep (se 1 (by rfl) ⟨555713, by rfl⟩ : syracuseStep 740951 = 1111427) B1111427
theorem B2379415 : Blo 491791 2379415 := bstep (se 1 (by rfl) ⟨1784561, by rfl⟩ : syracuseStep 2379415 = 3569123) B3569123
theorem B741017 : Blo 491791 741017 := bstep (se 2 (by rfl) ⟨277881, by rfl⟩ : syracuseStep 741017 = 555763) B555763
theorem B741131 : Blo 491791 741131 := bstep (se 1 (by rfl) ⟨555848, by rfl⟩ : syracuseStep 741131 = 1111697) B1111697
theorem B741143 : Blo 491791 741143 := bstep (se 1 (by rfl) ⟨555857, by rfl⟩ : syracuseStep 741143 = 1111715) B1111715
theorem B741209 : Blo 491791 741209 := bstep (se 2 (by rfl) ⟨277953, by rfl⟩ : syracuseStep 741209 = 555907) B555907
theorem B741323 : Blo 491791 741323 := bstep (se 1 (by rfl) ⟨555992, by rfl⟩ : syracuseStep 741323 = 1111985) B1111985
theorem B741335 : Blo 491791 741335 := bstep (se 1 (by rfl) ⟨556001, by rfl⟩ : syracuseStep 741335 = 1112003) B1112003
theorem B741401 : Blo 491791 741401 := bstep (se 2 (by rfl) ⟨278025, by rfl⟩ : syracuseStep 741401 = 556051) B556051
theorem B4739147 : Blo 491791 4739147 := bstep (se 1 (by rfl) ⟨3554360, by rfl⟩ : syracuseStep 4739147 = 7108721) B7108721
theorem B938071 : Blo 491791 938071 := bstep (se 1 (by rfl) ⟨703553, by rfl⟩ : syracuseStep 938071 = 1407107) B1407107
theorem B741515 : Blo 491791 741515 := bstep (se 1 (by rfl) ⟨556136, by rfl⟩ : syracuseStep 741515 = 1112273) B1112273
theorem B741527 : Blo 491791 741527 := bstep (se 1 (by rfl) ⟨556145, by rfl⟩ : syracuseStep 741527 = 1112291) B1112291
theorem B741593 : Blo 491791 741593 := bstep (se 2 (by rfl) ⟨278097, by rfl⟩ : syracuseStep 741593 = 556195) B556195
theorem B545015 : Blo 491791 545015 := bstep (se 1 (by rfl) ⟨408761, by rfl⟩ : syracuseStep 545015 = 817523) B817523
theorem B3756293 : Blo 491791 3756293 := bstep (se 4 (by rfl) ⟨352152, by rfl⟩ : syracuseStep 3756293 = 704305) B704305
theorem B741707 : Blo 491791 741707 := bstep (se 1 (by rfl) ⟨556280, by rfl⟩ : syracuseStep 741707 = 1112561) B1112561
theorem B741719 : Blo 491791 741719 := bstep (se 1 (by rfl) ⟨556289, by rfl⟩ : syracuseStep 741719 = 1112579) B1112579
theorem B741785 : Blo 491791 741785 := bstep (se 2 (by rfl) ⟨278169, by rfl⟩ : syracuseStep 741785 = 556339) B556339
theorem B610763 : Blo 491791 610763 := bstep (se 1 (by rfl) ⟨458072, by rfl⟩ : syracuseStep 610763 = 916145) B916145
theorem B741899 : Blo 491791 741899 := bstep (se 1 (by rfl) ⟨556424, by rfl⟩ : syracuseStep 741899 = 1112849) B1112849
theorem B741911 : Blo 491791 741911 := bstep (se 1 (by rfl) ⟨556433, by rfl⟩ : syracuseStep 741911 = 1112867) B1112867
theorem B741977 : Blo 491791 741977 := bstep (se 2 (by rfl) ⟨278241, by rfl⟩ : syracuseStep 741977 = 556483) B556483
theorem B2675351 : Blo 491791 2675351 := bstep (se 1 (by rfl) ⟨2006513, by rfl⟩ : syracuseStep 2675351 = 4013027) B4013027
theorem B742091 : Blo 491791 742091 := bstep (se 1 (by rfl) ⟨556568, by rfl⟩ : syracuseStep 742091 = 1113137) B1113137
theorem B742103 : Blo 491791 742103 := bstep (se 1 (by rfl) ⟨556577, by rfl⟩ : syracuseStep 742103 = 1113155) B1113155
theorem B742169 : Blo 491791 742169 := bstep (se 2 (by rfl) ⟨278313, by rfl⟩ : syracuseStep 742169 = 556627) B556627
theorem B938891 : Blo 491791 938891 := bstep (se 1 (by rfl) ⟨704168, by rfl⟩ : syracuseStep 938891 = 1408337) B1408337
theorem B742283 : Blo 491791 742283 := bstep (se 1 (by rfl) ⟨556712, by rfl⟩ : syracuseStep 742283 = 1113425) B1113425
theorem B742295 : Blo 491791 742295 := bstep (se 1 (by rfl) ⟨556721, by rfl⟩ : syracuseStep 742295 = 1113443) B1113443
theorem B938945 : Blo 491791 938945 := bstep (se 2 (by rfl) ⟨352104, by rfl⟩ : syracuseStep 938945 = 704209) B704209
theorem B1659851 : Blo 491791 1659851 := bstep (se 1 (by rfl) ⟨1244888, by rfl⟩ : syracuseStep 1659851 = 2489777) B2489777
theorem B742361 : Blo 491791 742361 := bstep (se 2 (by rfl) ⟨278385, by rfl⟩ : syracuseStep 742361 = 556771) B556771
theorem B742475 : Blo 491791 742475 := bstep (se 1 (by rfl) ⟨556856, by rfl⟩ : syracuseStep 742475 = 1113713) B1113713
theorem B742487 : Blo 491791 742487 := bstep (se 1 (by rfl) ⟨556865, by rfl⟩ : syracuseStep 742487 = 1113731) B1113731
theorem B5624963 : Blo 491791 5624963 := bstep (se 1 (by rfl) ⟨4218722, by rfl⟩ : syracuseStep 5624963 = 8437445) B8437445
theorem B742553 : Blo 491791 742553 := bstep (se 2 (by rfl) ⟨278457, by rfl⟩ : syracuseStep 742553 = 556915) B556915
theorem B1660121 : Blo 491791 1660121 := bstep (se 2 (by rfl) ⟨622545, by rfl⟩ : syracuseStep 1660121 = 1245091) B1245091
theorem B742667 : Blo 491791 742667 := bstep (se 1 (by rfl) ⟨557000, by rfl⟩ : syracuseStep 742667 = 1114001) B1114001
theorem B742679 : Blo 491791 742679 := bstep (se 1 (by rfl) ⟨557009, by rfl⟩ : syracuseStep 742679 = 1114019) B1114019
theorem B742745 : Blo 491791 742745 := bstep (se 2 (by rfl) ⟨278529, by rfl⟩ : syracuseStep 742745 = 557059) B557059
theorem B742859 : Blo 491791 742859 := bstep (se 1 (by rfl) ⟨557144, by rfl⟩ : syracuseStep 742859 = 1114289) B1114289
theorem B742871 : Blo 491791 742871 := bstep (se 1 (by rfl) ⟨557153, by rfl⟩ : syracuseStep 742871 = 1114307) B1114307
theorem B742937 : Blo 491791 742937 := bstep (se 2 (by rfl) ⟨278601, by rfl⟩ : syracuseStep 742937 = 557203) B557203
theorem B743051 : Blo 491791 743051 := bstep (se 1 (by rfl) ⟨557288, by rfl⟩ : syracuseStep 743051 = 1114577) B1114577
theorem B743063 : Blo 491791 743063 := bstep (se 1 (by rfl) ⟨557297, by rfl⟩ : syracuseStep 743063 = 1114595) B1114595
theorem B743129 : Blo 491791 743129 := bstep (se 2 (by rfl) ⟨278673, by rfl⟩ : syracuseStep 743129 = 557347) B557347
theorem B6313733 : Blo 491791 6313733 := bstep (se 4 (by rfl) ⟨591912, by rfl⟩ : syracuseStep 6313733 = 1183825) B1183825
theorem B743243 : Blo 491791 743243 := bstep (se 1 (by rfl) ⟨557432, by rfl⟩ : syracuseStep 743243 = 1114865) B1114865
theorem B939863 : Blo 491791 939863 := bstep (se 1 (by rfl) ⟨704897, by rfl⟩ : syracuseStep 939863 = 1409795) B1409795
theorem B743255 : Blo 491791 743255 := bstep (se 1 (by rfl) ⟨557441, by rfl⟩ : syracuseStep 743255 = 1114883) B1114883
theorem B2676581 : Blo 491791 2676581 := bstep (se 4 (by rfl) ⟨250929, by rfl⟩ : syracuseStep 2676581 = 501859) B501859
theorem B1660823 : Blo 491791 1660823 := bstep (se 1 (by rfl) ⟨1245617, by rfl⟩ : syracuseStep 1660823 = 2491235) B2491235
theorem B743321 : Blo 491791 743321 := bstep (se 2 (by rfl) ⟨278745, by rfl⟩ : syracuseStep 743321 = 557491) B557491
theorem B743435 : Blo 491791 743435 := bstep (se 1 (by rfl) ⟨557576, by rfl⟩ : syracuseStep 743435 = 1115153) B1115153
theorem B743447 : Blo 491791 743447 := bstep (se 1 (by rfl) ⟨557585, by rfl⟩ : syracuseStep 743447 = 1115171) B1115171
theorem B743513 : Blo 491791 743513 := bstep (se 2 (by rfl) ⟨278817, by rfl⟩ : syracuseStep 743513 = 557635) B557635
theorem B16046261 : Blo 491791 16046261 := bstep (se 5 (by rfl) ⟨752168, by rfl⟩ : syracuseStep 16046261 = 1504337) B1504337
theorem B743627 : Blo 491791 743627 := bstep (se 1 (by rfl) ⟨557720, by rfl⟩ : syracuseStep 743627 = 1115441) B1115441
theorem B743639 : Blo 491791 743639 := bstep (se 1 (by rfl) ⟨557729, by rfl⟩ : syracuseStep 743639 = 1115459) B1115459
theorem B842071 : Blo 491791 842071 := bstep (se 1 (by rfl) ⟨631553, by rfl⟩ : syracuseStep 842071 = 1263107) B1263107
theorem B940403 : Blo 491791 940403 := bstep (se 1 (by rfl) ⟨705302, by rfl⟩ : syracuseStep 940403 = 1410605) B1410605
theorem B1661363 : Blo 491791 1661363 := bstep (se 1 (by rfl) ⟨1246022, by rfl⟩ : syracuseStep 1661363 = 2492045) B2492045
theorem B3758723 : Blo 491791 3758723 := bstep (se 1 (by rfl) ⟨2819042, by rfl⟩ : syracuseStep 3758723 = 5638085) B5638085
theorem B1661633 : Blo 491791 1661633 := bstep (se 2 (by rfl) ⟨623112, by rfl⟩ : syracuseStep 1661633 = 1246225) B1246225
theorem B940889 : Blo 491791 940889 := bstep (se 2 (by rfl) ⟨352833, by rfl⟩ : syracuseStep 940889 = 705667) B705667
theorem B2710451 : Blo 491791 2710451 := bstep (se 1 (by rfl) ⟨2032838, by rfl⟩ : syracuseStep 2710451 = 4065677) B4065677
theorem B1662173 : Blo 491791 1662173 := bstep (se 3 (by rfl) ⟨311657, by rfl⟩ : syracuseStep 1662173 = 623315) B623315
theorem B4513229 : Blo 491791 4513229 := bstep (se 3 (by rfl) ⟨846230, by rfl⟩ : syracuseStep 4513229 = 1692461) B1692461
theorem B2809475 : Blo 491791 2809475 := bstep (se 1 (by rfl) ⟨2107106, by rfl⟩ : syracuseStep 2809475 = 4214213) B4214213
theorem B4808323 : Blo 491791 4808323 := bstep (se 1 (by rfl) ⟨3606242, by rfl⟩ : syracuseStep 4808323 = 7212485) B7212485
theorem B1335005 : Blo 491791 1335005 := bstep (se 3 (by rfl) ⟨250313, by rfl⟩ : syracuseStep 1335005 = 500627) B500627
theorem B5791493 : Blo 491791 5791493 := bstep (se 4 (by rfl) ⟨542952, by rfl⟩ : syracuseStep 5791493 = 1085905) B1085905
theorem B3563443 : Blo 491791 3563443 := bstep (se 1 (by rfl) ⟨2672582, by rfl⟩ : syracuseStep 3563443 = 5345165) B5345165
theorem B1368029 : Blo 491791 1368029 := bstep (se 3 (by rfl) ⟨256505, by rfl⟩ : syracuseStep 1368029 = 513011) B513011
theorem B8446193 : Blo 491791 8446193 := bstep (se 2 (by rfl) ⟨3167322, by rfl⟩ : syracuseStep 8446193 = 6334645) B6334645
theorem B1663307 : Blo 491791 1663307 := bstep (se 1 (by rfl) ⟨1247480, by rfl⟩ : syracuseStep 1663307 = 2494961) B2494961
theorem B8020403 : Blo 491791 8020403 := bstep (se 1 (by rfl) ⟨6015302, by rfl⟩ : syracuseStep 8020403 = 12030605) B12030605
theorem B1663577 : Blo 491791 1663577 := bstep (se 2 (by rfl) ⟨623841, by rfl⟩ : syracuseStep 1663577 = 1247683) B1247683
theorem B1106585 : Blo 491791 1106585 := bstep (se 2 (by rfl) ⟨414969, by rfl⟩ : syracuseStep 1106585 = 829939) B829939
theorem B1106675 : Blo 491791 1106675 := bstep (se 1 (by rfl) ⟨830006, by rfl⟩ : syracuseStep 1106675 = 1660013) B1660013
theorem B1106711 : Blo 491791 1106711 := bstep (se 1 (by rfl) ⟨830033, by rfl⟩ : syracuseStep 1106711 = 1660067) B1660067
theorem B1631069 : Blo 491791 1631069 := bstep (se 3 (by rfl) ⟨305825, by rfl⟩ : syracuseStep 1631069 = 611651) B611651
theorem B3466115 : Blo 491791 3466115 := bstep (se 1 (by rfl) ⟨2599586, by rfl⟩ : syracuseStep 3466115 = 5199173) B5199173
theorem B1106891 : Blo 491791 1106891 := bstep (se 1 (by rfl) ⟨830168, by rfl⟩ : syracuseStep 1106891 = 1660337) B1660337
theorem B1106945 : Blo 491791 1106945 := bstep (se 2 (by rfl) ⟨415104, by rfl⟩ : syracuseStep 1106945 = 830209) B830209
theorem B1402049 : Blo 491791 1402049 := bstep (se 2 (by rfl) ⟨525768, by rfl⟩ : syracuseStep 1402049 = 1051537) B1051537
theorem B1107161 : Blo 491791 1107161 := bstep (se 2 (by rfl) ⟨415185, by rfl⟩ : syracuseStep 1107161 = 830371) B830371
theorem B1402073 : Blo 491791 1402073 := bstep (se 2 (by rfl) ⟨525777, by rfl⟩ : syracuseStep 1402073 = 1051555) B1051555
theorem B1664279 : Blo 491791 1664279 := bstep (se 1 (by rfl) ⟨1248209, by rfl⟩ : syracuseStep 1664279 = 2496419) B2496419
theorem B4744493 : Blo 491791 4744493 := bstep (se 3 (by rfl) ⟨889592, by rfl⟩ : syracuseStep 4744493 = 1779185) B1779185
theorem B3171629 : Blo 491791 3171629 := bstep (se 3 (by rfl) ⟨594680, by rfl⟩ : syracuseStep 3171629 = 1189361) B1189361
theorem B1107251 : Blo 491791 1107251 := bstep (se 1 (by rfl) ⟨830438, by rfl⟩ : syracuseStep 1107251 = 1660877) B1660877
theorem B1107287 : Blo 491791 1107287 := bstep (se 1 (by rfl) ⟨830465, by rfl⟩ : syracuseStep 1107287 = 1660931) B1660931
theorem B1107467 : Blo 491791 1107467 := bstep (se 1 (by rfl) ⟨830600, by rfl⟩ : syracuseStep 1107467 = 1661201) B1661201
theorem B6743569 : Blo 491791 6743569 := bstep (se 2 (by rfl) ⟨2528838, by rfl⟩ : syracuseStep 6743569 = 5057677) B5057677
theorem B1107521 : Blo 491791 1107521 := bstep (se 2 (by rfl) ⟨415320, by rfl⟩ : syracuseStep 1107521 = 830641) B830641
theorem B1894033 : Blo 491791 1894033 := bstep (se 2 (by rfl) ⟨710262, by rfl⟩ : syracuseStep 1894033 = 1420525) B1420525
theorem B1107737 : Blo 491791 1107737 := bstep (se 2 (by rfl) ⟨415401, by rfl⟩ : syracuseStep 1107737 = 830803) B830803
theorem B1664819 : Blo 491791 1664819 := bstep (se 1 (by rfl) ⟨1248614, by rfl⟩ : syracuseStep 1664819 = 2497229) B2497229
theorem B1107827 : Blo 491791 1107827 := bstep (se 1 (by rfl) ⟨830870, by rfl⟩ : syracuseStep 1107827 = 1661741) B1661741
theorem B1107863 : Blo 491791 1107863 := bstep (se 1 (by rfl) ⟨830897, by rfl⟩ : syracuseStep 1107863 = 1661795) B1661795
theorem B3762125 : Blo 491791 3762125 := bstep (se 3 (by rfl) ⟨705398, by rfl⟩ : syracuseStep 3762125 = 1410797) B1410797
theorem B1665089 : Blo 491791 1665089 := bstep (se 2 (by rfl) ⟨624408, by rfl⟩ : syracuseStep 1665089 = 1248817) B1248817
theorem B1108043 : Blo 491791 1108043 := bstep (se 1 (by rfl) ⟨831032, by rfl⟩ : syracuseStep 1108043 = 1662065) B1662065
theorem B1108097 : Blo 491791 1108097 := bstep (se 2 (by rfl) ⟨415536, by rfl⟩ : syracuseStep 1108097 = 831073) B831073
theorem B1108313 : Blo 491791 1108313 := bstep (se 2 (by rfl) ⟨415617, by rfl⟩ : syracuseStep 1108313 = 831235) B831235
theorem B1108403 : Blo 491791 1108403 := bstep (se 1 (by rfl) ⟨831302, by rfl⟩ : syracuseStep 1108403 = 1662605) B1662605
theorem B1403315 : Blo 491791 1403315 := bstep (se 1 (by rfl) ⟨1052486, by rfl⟩ : syracuseStep 1403315 = 2104973) B2104973
theorem B3762611 : Blo 491791 3762611 := bstep (se 1 (by rfl) ⟨2821958, by rfl⟩ : syracuseStep 3762611 = 5643917) B5643917
theorem B1108439 : Blo 491791 1108439 := bstep (se 1 (by rfl) ⟨831329, by rfl⟩ : syracuseStep 1108439 = 1662659) B1662659
theorem B3041837 : Blo 491791 3041837 := bstep (se 3 (by rfl) ⟨570344, by rfl⟩ : syracuseStep 3041837 = 1140689) B1140689
theorem B1665629 : Blo 491791 1665629 := bstep (se 3 (by rfl) ⟨312305, by rfl⟩ : syracuseStep 1665629 = 624611) B624611
theorem B1108619 : Blo 491791 1108619 := bstep (se 1 (by rfl) ⟨831464, by rfl⟩ : syracuseStep 1108619 = 1662929) B1662929
theorem B1108673 : Blo 491791 1108673 := bstep (se 2 (by rfl) ⟨415752, by rfl⟩ : syracuseStep 1108673 = 831505) B831505
theorem B1502003 : Blo 491791 1502003 := bstep (se 1 (by rfl) ⟨1126502, by rfl⟩ : syracuseStep 1502003 = 2253005) B2253005
theorem B1108889 : Blo 491791 1108889 := bstep (se 2 (by rfl) ⟨415833, by rfl⟩ : syracuseStep 1108889 = 831667) B831667
theorem B1108979 : Blo 491791 1108979 := bstep (se 1 (by rfl) ⟨831734, by rfl⟩ : syracuseStep 1108979 = 1663469) B1663469
theorem B1109015 : Blo 491791 1109015 := bstep (se 1 (by rfl) ⟨831761, by rfl⟩ : syracuseStep 1109015 = 1663523) B1663523
theorem B1109195 : Blo 491791 1109195 := bstep (se 1 (by rfl) ⟨831896, by rfl⟩ : syracuseStep 1109195 = 1663793) B1663793
theorem B9268465 : Blo 491791 9268465 := bstep (se 2 (by rfl) ⟨3475674, by rfl⟩ : syracuseStep 9268465 = 6951349) B6951349
theorem B1109249 : Blo 491791 1109249 := bstep (se 2 (by rfl) ⟨415968, by rfl⟩ : syracuseStep 1109249 = 831937) B831937
theorem B18935045 : Blo 491791 18935045 := bstep (se 4 (by rfl) ⟨1775160, by rfl⟩ : syracuseStep 18935045 = 3550321) B3550321
theorem B1109465 : Blo 491791 1109465 := bstep (se 2 (by rfl) ⟨416049, by rfl⟩ : syracuseStep 1109465 = 832099) B832099
theorem B1109555 : Blo 491791 1109555 := bstep (se 1 (by rfl) ⟨832166, by rfl⟩ : syracuseStep 1109555 = 1664333) B1664333
theorem B1109591 : Blo 491791 1109591 := bstep (se 1 (by rfl) ⟨832193, by rfl⟩ : syracuseStep 1109591 = 1664387) B1664387
theorem B1601117 : Blo 491791 1601117 := bstep (se 3 (by rfl) ⟨300209, by rfl⟩ : syracuseStep 1601117 = 600419) B600419
theorem B1666763 : Blo 491791 1666763 := bstep (se 1 (by rfl) ⟨1250072, by rfl⟩ : syracuseStep 1666763 = 2500145) B2500145
theorem B1109771 : Blo 491791 1109771 := bstep (se 1 (by rfl) ⟨832328, by rfl⟩ : syracuseStep 1109771 = 1664657) B1664657
theorem B1109825 : Blo 491791 1109825 := bstep (se 2 (by rfl) ⟨416184, by rfl⟩ : syracuseStep 1109825 = 832369) B832369
theorem B3764069 : Blo 491791 3764069 := bstep (se 4 (by rfl) ⟨352881, by rfl⟩ : syracuseStep 3764069 = 705763) B705763
theorem B1667033 : Blo 491791 1667033 := bstep (se 2 (by rfl) ⟨625137, by rfl⟩ : syracuseStep 1667033 = 1250275) B1250275
theorem B1110041 : Blo 491791 1110041 := bstep (se 2 (by rfl) ⟨416265, by rfl⟩ : syracuseStep 1110041 = 832531) B832531
theorem B1110131 : Blo 491791 1110131 := bstep (se 1 (by rfl) ⟨832598, by rfl⟩ : syracuseStep 1110131 = 1665197) B1665197
theorem B1110167 : Blo 491791 1110167 := bstep (se 1 (by rfl) ⟨832625, by rfl⟩ : syracuseStep 1110167 = 1665251) B1665251
theorem B6025421 : Blo 491791 6025421 := bstep (se 3 (by rfl) ⟨1129766, by rfl⟩ : syracuseStep 6025421 = 2259533) B2259533
theorem B1110347 : Blo 491791 1110347 := bstep (se 1 (by rfl) ⟨832760, by rfl⟩ : syracuseStep 1110347 = 1665521) B1665521
theorem B3764555 : Blo 491791 3764555 := bstep (se 1 (by rfl) ⟨2823416, by rfl⟩ : syracuseStep 3764555 = 5646833) B5646833
theorem B1110401 : Blo 491791 1110401 := bstep (se 2 (by rfl) ⟨416400, by rfl⟩ : syracuseStep 1110401 = 832801) B832801
theorem B553387 : Blo 491791 553387 := bstep (se 1 (by rfl) ⟨415040, by rfl⟩ : syracuseStep 553387 = 830081) B830081
theorem B553495 : Blo 491791 553495 := bstep (se 1 (by rfl) ⟨415121, by rfl⟩ : syracuseStep 553495 = 830243) B830243
theorem B1110617 : Blo 491791 1110617 := bstep (se 2 (by rfl) ⟨416481, by rfl⟩ : syracuseStep 1110617 = 832963) B832963
theorem B1667735 : Blo 491791 1667735 := bstep (se 1 (by rfl) ⟨1250801, by rfl⟩ : syracuseStep 1667735 = 2501603) B2501603
theorem B1110707 : Blo 491791 1110707 := bstep (se 1 (by rfl) ⟨833030, by rfl⟩ : syracuseStep 1110707 = 1666061) B1666061
theorem B553675 : Blo 491791 553675 := bstep (se 1 (by rfl) ⟨415256, by rfl⟩ : syracuseStep 553675 = 830513) B830513
theorem B1340107 : Blo 491791 1340107 := bstep (se 1 (by rfl) ⟨1005080, by rfl⟩ : syracuseStep 1340107 = 2010161) B2010161
theorem B1110743 : Blo 491791 1110743 := bstep (se 1 (by rfl) ⟨833057, by rfl⟩ : syracuseStep 1110743 = 1666115) B1666115
theorem B3994373 : Blo 491791 3994373 := bstep (se 4 (by rfl) ⟨374472, by rfl⟩ : syracuseStep 3994373 = 748945) B748945
theorem B553783 : Blo 491791 553783 := bstep (se 1 (by rfl) ⟨415337, by rfl⟩ : syracuseStep 553783 = 830675) B830675
theorem B2814851 : Blo 491791 2814851 := bstep (se 1 (by rfl) ⟨2111138, by rfl⟩ : syracuseStep 2814851 = 4222277) B4222277
theorem B1110923 : Blo 491791 1110923 := bstep (se 1 (by rfl) ⟨833192, by rfl⟩ : syracuseStep 1110923 = 1666385) B1666385
theorem B1110977 : Blo 491791 1110977 := bstep (se 2 (by rfl) ⟨416616, by rfl⟩ : syracuseStep 1110977 = 833233) B833233
theorem B750551 : Blo 491791 750551 := bstep (se 1 (by rfl) ⟨562913, by rfl⟩ : syracuseStep 750551 = 1125827) B1125827
theorem B553963 : Blo 491791 553963 := bstep (se 1 (by rfl) ⟨415472, by rfl⟩ : syracuseStep 553963 = 830945) B830945
theorem B554071 : Blo 491791 554071 := bstep (se 1 (by rfl) ⟨415553, by rfl⟩ : syracuseStep 554071 = 831107) B831107
theorem B1111193 : Blo 491791 1111193 := bstep (se 2 (by rfl) ⟨416697, by rfl⟩ : syracuseStep 1111193 = 833395) B833395
theorem B1668275 : Blo 491791 1668275 := bstep (se 1 (by rfl) ⟨1251206, by rfl⟩ : syracuseStep 1668275 = 2502413) B2502413
theorem B1406173 : Blo 491791 1406173 := bstep (se 3 (by rfl) ⟨263657, by rfl⟩ : syracuseStep 1406173 = 527315) B527315
theorem B1111283 : Blo 491791 1111283 := bstep (se 1 (by rfl) ⟨833462, by rfl⟩ : syracuseStep 1111283 = 1666925) B1666925
theorem B554251 : Blo 491791 554251 := bstep (se 1 (by rfl) ⟨415688, by rfl⟩ : syracuseStep 554251 = 831377) B831377
theorem B1406231 : Blo 491791 1406231 := bstep (se 1 (by rfl) ⟨1054673, by rfl⟩ : syracuseStep 1406231 = 2109347) B2109347
theorem B1111319 : Blo 491791 1111319 := bstep (se 1 (by rfl) ⟨833489, by rfl⟩ : syracuseStep 1111319 = 1666979) B1666979
theorem B947531 : Blo 491791 947531 := bstep (se 1 (by rfl) ⟨710648, by rfl⟩ : syracuseStep 947531 = 1421297) B1421297
theorem B2815307 : Blo 491791 2815307 := bstep (se 1 (by rfl) ⟨2111480, by rfl⟩ : syracuseStep 2815307 = 4222961) B4222961
theorem B554359 : Blo 491791 554359 := bstep (se 1 (by rfl) ⟨415769, by rfl⟩ : syracuseStep 554359 = 831539) B831539
theorem B1668545 : Blo 491791 1668545 := bstep (se 2 (by rfl) ⟨625704, by rfl⟩ : syracuseStep 1668545 = 1251409) B1251409
theorem B1111499 : Blo 491791 1111499 := bstep (se 1 (by rfl) ⟨833624, by rfl⟩ : syracuseStep 1111499 = 1667249) B1667249
theorem B1111553 : Blo 491791 1111553 := bstep (se 2 (by rfl) ⟨416832, by rfl⟩ : syracuseStep 1111553 = 833665) B833665
theorem B554539 : Blo 491791 554539 := bstep (se 1 (by rfl) ⟨415904, by rfl⟩ : syracuseStep 554539 = 831809) B831809
theorem B554647 : Blo 491791 554647 := bstep (se 1 (by rfl) ⟨415985, by rfl⟩ : syracuseStep 554647 = 831971) B831971
theorem B1111769 : Blo 491791 1111769 := bstep (se 2 (by rfl) ⟨416913, by rfl⟩ : syracuseStep 1111769 = 833827) B833827
theorem B1111859 : Blo 491791 1111859 := bstep (se 1 (by rfl) ⟨833894, by rfl⟩ : syracuseStep 1111859 = 1667789) B1667789
theorem B554827 : Blo 491791 554827 := bstep (se 1 (by rfl) ⟨416120, by rfl⟩ : syracuseStep 554827 = 832241) B832241
theorem B1111895 : Blo 491791 1111895 := bstep (se 1 (by rfl) ⟨833921, by rfl⟩ : syracuseStep 1111895 = 1667843) B1667843
theorem B554935 : Blo 491791 554935 := bstep (se 1 (by rfl) ⟨416201, by rfl⟩ : syracuseStep 554935 = 832403) B832403
theorem B1669085 : Blo 491791 1669085 := bstep (se 3 (by rfl) ⟨312953, by rfl⟩ : syracuseStep 1669085 = 625907) B625907
theorem B1112075 : Blo 491791 1112075 := bstep (se 1 (by rfl) ⟨834056, by rfl⟩ : syracuseStep 1112075 = 1668113) B1668113
theorem B1112129 : Blo 491791 1112129 := bstep (se 2 (by rfl) ⟨417048, by rfl⟩ : syracuseStep 1112129 = 834097) B834097
theorem B555115 : Blo 491791 555115 := bstep (se 1 (by rfl) ⟨416336, by rfl⟩ : syracuseStep 555115 = 832673) B832673
theorem B555223 : Blo 491791 555223 := bstep (se 1 (by rfl) ⟨416417, by rfl⟩ : syracuseStep 555223 = 832835) B832835
theorem B1112345 : Blo 491791 1112345 := bstep (se 2 (by rfl) ⟨417129, by rfl⟩ : syracuseStep 1112345 = 834259) B834259
theorem B1112435 : Blo 491791 1112435 := bstep (se 1 (by rfl) ⟨834326, by rfl⟩ : syracuseStep 1112435 = 1668653) B1668653
theorem B555403 : Blo 491791 555403 := bstep (se 1 (by rfl) ⟨416552, by rfl⟩ : syracuseStep 555403 = 833105) B833105
theorem B1112471 : Blo 491791 1112471 := bstep (se 1 (by rfl) ⟨834353, by rfl⟩ : syracuseStep 1112471 = 1668707) B1668707
theorem B1407449 : Blo 491791 1407449 := bstep (se 2 (by rfl) ⟨527793, by rfl⟩ : syracuseStep 1407449 = 1055587) B1055587
theorem B555511 : Blo 491791 555511 := bstep (se 1 (by rfl) ⟨416633, by rfl⟩ : syracuseStep 555511 = 833267) B833267
theorem B1604119 : Blo 491791 1604119 := bstep (se 1 (by rfl) ⟨1203089, by rfl⟩ : syracuseStep 1604119 = 2406179) B2406179
theorem B1407563 : Blo 491791 1407563 := bstep (se 1 (by rfl) ⟨1055672, by rfl⟩ : syracuseStep 1407563 = 2111345) B2111345
theorem B1112651 : Blo 491791 1112651 := bstep (se 1 (by rfl) ⟨834488, by rfl⟩ : syracuseStep 1112651 = 1668977) B1668977
theorem B3570277 : Blo 491791 3570277 := bstep (se 4 (by rfl) ⟨334713, by rfl⟩ : syracuseStep 3570277 = 669427) B669427
theorem B1112705 : Blo 491791 1112705 := bstep (se 2 (by rfl) ⟨417264, by rfl⟩ : syracuseStep 1112705 = 834529) B834529
theorem B752267 : Blo 491791 752267 := bstep (se 1 (by rfl) ⟨564200, by rfl⟩ : syracuseStep 752267 = 1128401) B1128401
theorem B555691 : Blo 491791 555691 := bstep (se 1 (by rfl) ⟨416768, by rfl⟩ : syracuseStep 555691 = 833537) B833537
theorem B752395 : Blo 491791 752395 := bstep (se 1 (by rfl) ⟨564296, by rfl⟩ : syracuseStep 752395 = 1128593) B1128593
theorem B2030359 : Blo 491791 2030359 := bstep (se 1 (by rfl) ⟨1522769, by rfl⟩ : syracuseStep 2030359 = 3045539) B3045539
theorem B555799 : Blo 491791 555799 := bstep (se 1 (by rfl) ⟨416849, by rfl⟩ : syracuseStep 555799 = 833699) B833699
theorem B1112921 : Blo 491791 1112921 := bstep (se 2 (by rfl) ⟨417345, by rfl⟩ : syracuseStep 1112921 = 834691) B834691
theorem B1113011 : Blo 491791 1113011 := bstep (se 1 (by rfl) ⟨834758, by rfl⟩ : syracuseStep 1113011 = 1669517) B1669517
theorem B555979 : Blo 491791 555979 := bstep (se 1 (by rfl) ⟨416984, by rfl⟩ : syracuseStep 555979 = 833969) B833969
theorem B1113047 : Blo 491791 1113047 := bstep (se 1 (by rfl) ⟨834785, by rfl⟩ : syracuseStep 1113047 = 1669571) B1669571
theorem B556087 : Blo 491791 556087 := bstep (se 1 (by rfl) ⟨417065, by rfl⟩ : syracuseStep 556087 = 834131) B834131
theorem B1670219 : Blo 491791 1670219 := bstep (se 1 (by rfl) ⟨1252664, by rfl⟩ : syracuseStep 1670219 = 2505329) B2505329
theorem B1113227 : Blo 491791 1113227 := bstep (se 1 (by rfl) ⟨834920, by rfl⟩ : syracuseStep 1113227 = 1669841) B1669841
theorem B1113281 : Blo 491791 1113281 := bstep (se 2 (by rfl) ⟨417480, by rfl⟩ : syracuseStep 1113281 = 834961) B834961
theorem B556267 : Blo 491791 556267 := bstep (se 1 (by rfl) ⟨417200, by rfl⟩ : syracuseStep 556267 = 834401) B834401
theorem B556375 : Blo 491791 556375 := bstep (se 1 (by rfl) ⟨417281, by rfl⟩ : syracuseStep 556375 = 834563) B834563
theorem B752983 : Blo 491791 752983 := bstep (se 1 (by rfl) ⟨564737, by rfl⟩ : syracuseStep 752983 = 1129475) B1129475
theorem B1670489 : Blo 491791 1670489 := bstep (se 2 (by rfl) ⟨626433, by rfl⟩ : syracuseStep 1670489 = 1252867) B1252867
theorem B1113497 : Blo 491791 1113497 := bstep (se 2 (by rfl) ⟨417561, by rfl⟩ : syracuseStep 1113497 = 835123) B835123
theorem B1113587 : Blo 491791 1113587 := bstep (se 1 (by rfl) ⟨835190, by rfl⟩ : syracuseStep 1113587 = 1670381) B1670381
theorem B556555 : Blo 491791 556555 := bstep (se 1 (by rfl) ⟨417416, by rfl⟩ : syracuseStep 556555 = 834833) B834833
theorem B1113623 : Blo 491791 1113623 := bstep (se 1 (by rfl) ⟨835217, by rfl⟩ : syracuseStep 1113623 = 1670435) B1670435
theorem B556663 : Blo 491791 556663 := bstep (se 1 (by rfl) ⟨417497, by rfl⟩ : syracuseStep 556663 = 834995) B834995
theorem B1408691 : Blo 491791 1408691 := bstep (se 1 (by rfl) ⟨1056518, by rfl⟩ : syracuseStep 1408691 = 2113037) B2113037
theorem B1113803 : Blo 491791 1113803 := bstep (se 1 (by rfl) ⟨835352, by rfl⟩ : syracuseStep 1113803 = 1670705) B1670705
theorem B1113857 : Blo 491791 1113857 := bstep (se 2 (by rfl) ⟨417696, by rfl⟩ : syracuseStep 1113857 = 835393) B835393
theorem B556843 : Blo 491791 556843 := bstep (se 1 (by rfl) ⟨417632, by rfl⟩ : syracuseStep 556843 = 835265) B835265
theorem B2490263 : Blo 491791 2490263 := bstep (se 1 (by rfl) ⟨1867697, by rfl⟩ : syracuseStep 2490263 = 3735395) B3735395
theorem B556951 : Blo 491791 556951 := bstep (se 1 (by rfl) ⟨417713, by rfl⟩ : syracuseStep 556951 = 835427) B835427
theorem B1114073 : Blo 491791 1114073 := bstep (se 2 (by rfl) ⟨417777, by rfl⟩ : syracuseStep 1114073 = 835555) B835555
theorem B1114127 : Blo 491791 1114127 := bstep (se 1 (by rfl) ⟨835595, by rfl⟩ : syracuseStep 1114127 = 1671191) B1671191
theorem B1867805 : Blo 491791 1867805 := bstep (se 3 (by rfl) ⟨350213, by rfl⟩ : syracuseStep 1867805 = 700427) B700427
theorem B1114145 : Blo 491791 1114145 := bstep (se 2 (by rfl) ⟨417804, by rfl⟩ : syracuseStep 1114145 = 835609) B835609
theorem B1867819 : Blo 491791 1867819 := bstep (se 1 (by rfl) ⟨1400864, by rfl⟩ : syracuseStep 1867819 = 2801729) B2801729
theorem B2162945 : Blo 491791 2162945 := bstep (se 2 (by rfl) ⟨811104, by rfl⟩ : syracuseStep 2162945 = 1622209) B1622209
theorem B491791 : Blo 491791 491791 := bstep (se 1 (by rfl) ⟨368843, by rfl⟩ : syracuseStep 491791 = 737687) B737687
theorem B491835 : Blo 491791 491835 := bstep (se 1 (by rfl) ⟨368876, by rfl⟩ : syracuseStep 491835 = 737753) B737753
theorem B1409339 : Blo 491791 1409339 := bstep (se 1 (by rfl) ⟨1057004, by rfl⟩ : syracuseStep 1409339 = 2114009) B2114009
theorem B1245527 : Blo 491791 1245527 := bstep (se 1 (by rfl) ⟨934145, by rfl⟩ : syracuseStep 1245527 = 1868291) B1868291
theorem B1114487 : Blo 491791 1114487 := bstep (se 1 (by rfl) ⟨835865, by rfl⟩ : syracuseStep 1114487 = 1671731) B1671731
theorem B491911 : Blo 491791 491911 := bstep (se 1 (by rfl) ⟨368933, by rfl⟩ : syracuseStep 491911 = 737867) B737867
theorem B491919 : Blo 491791 491919 := bstep (se 1 (by rfl) ⟨368939, by rfl⟩ : syracuseStep 491919 = 737879) B737879
theorem B622991 : Blo 491791 622991 := bstep (se 1 (by rfl) ⟨467243, by rfl⟩ : syracuseStep 622991 = 934487) B934487
theorem B14418323 : Blo 491791 14418323 := bstep (se 1 (by rfl) ⟨10813742, by rfl⟩ : syracuseStep 14418323 = 21627485) B21627485
theorem B557455 : Blo 491791 557455 := bstep (se 1 (by rfl) ⟨418091, by rfl⟩ : syracuseStep 557455 = 836183) B836183
theorem B491963 : Blo 491791 491963 := bstep (se 1 (by rfl) ⟨368972, by rfl⟩ : syracuseStep 491963 = 737945) B737945
theorem B492039 : Blo 491791 492039 := bstep (se 1 (by rfl) ⟨369029, by rfl⟩ : syracuseStep 492039 = 738059) B738059
theorem B492047 : Blo 491791 492047 := bstep (se 1 (by rfl) ⟨369035, by rfl⟩ : syracuseStep 492047 = 738071) B738071
theorem B1245739 : Blo 491791 1245739 := bstep (se 1 (by rfl) ⟨934304, by rfl⟩ : syracuseStep 1245739 = 1868609) B1868609
theorem B1114667 : Blo 491791 1114667 := bstep (se 1 (by rfl) ⟨836000, by rfl⟩ : syracuseStep 1114667 = 1672001) B1672001
theorem B492091 : Blo 491791 492091 := bstep (se 1 (by rfl) ⟨369068, by rfl⟩ : syracuseStep 492091 = 738137) B738137
theorem B492167 : Blo 491791 492167 := bstep (se 1 (by rfl) ⟨369125, by rfl⟩ : syracuseStep 492167 = 738251) B738251
theorem B492175 : Blo 491791 492175 := bstep (se 1 (by rfl) ⟨369131, by rfl⟩ : syracuseStep 492175 = 738263) B738263
theorem B1245881 : Blo 491791 1245881 := bstep (se 2 (by rfl) ⟨467205, by rfl⟩ : syracuseStep 1245881 = 934411) B934411
theorem B492219 : Blo 491791 492219 := bstep (se 1 (by rfl) ⟨369164, by rfl⟩ : syracuseStep 492219 = 738329) B738329
theorem B2491073 : Blo 491791 2491073 := bstep (se 2 (by rfl) ⟨934152, by rfl⟩ : syracuseStep 2491073 = 1868305) B1868305
theorem B492295 : Blo 491791 492295 := bstep (se 1 (by rfl) ⟨369221, by rfl⟩ : syracuseStep 492295 = 738443) B738443
theorem B492303 : Blo 491791 492303 := bstep (se 1 (by rfl) ⟨369227, by rfl⟩ : syracuseStep 492303 = 738455) B738455
theorem B492347 : Blo 491791 492347 := bstep (se 1 (by rfl) ⟨369260, by rfl⟩ : syracuseStep 492347 = 738521) B738521
theorem B492423 : Blo 491791 492423 := bstep (se 1 (by rfl) ⟨369317, by rfl⟩ : syracuseStep 492423 = 738635) B738635
theorem B492431 : Blo 491791 492431 := bstep (se 1 (by rfl) ⟨369323, by rfl⟩ : syracuseStep 492431 = 738647) B738647
theorem B1115027 : Blo 491791 1115027 := bstep (se 1 (by rfl) ⟨836270, by rfl⟩ : syracuseStep 1115027 = 1672541) B1672541
theorem B1409977 : Blo 491791 1409977 := bstep (se 2 (by rfl) ⟨528741, by rfl⟩ : syracuseStep 1409977 = 1057483) B1057483
theorem B492475 : Blo 491791 492475 := bstep (se 1 (by rfl) ⟨369356, by rfl⟩ : syracuseStep 492475 = 738713) B738713
theorem B1115081 : Blo 491791 1115081 := bstep (se 2 (by rfl) ⟨418155, by rfl⟩ : syracuseStep 1115081 = 836311) B836311
theorem B2163665 : Blo 491791 2163665 := bstep (se 2 (by rfl) ⟨811374, by rfl⟩ : syracuseStep 2163665 = 1622749) B1622749
theorem B492551 : Blo 491791 492551 := bstep (se 1 (by rfl) ⟨369413, by rfl⟩ : syracuseStep 492551 = 738827) B738827
theorem B492559 : Blo 491791 492559 := bstep (se 1 (by rfl) ⟨369419, by rfl⟩ : syracuseStep 492559 = 738839) B738839
theorem B492603 : Blo 491791 492603 := bstep (se 1 (by rfl) ⟨369452, by rfl⟩ : syracuseStep 492603 = 738905) B738905
theorem B492679 : Blo 491791 492679 := bstep (se 1 (by rfl) ⟨369509, by rfl⟩ : syracuseStep 492679 = 739019) B739019
theorem B492687 : Blo 491791 492687 := bstep (se 1 (by rfl) ⟨369515, by rfl⟩ : syracuseStep 492687 = 739031) B739031
theorem B492731 : Blo 491791 492731 := bstep (se 1 (by rfl) ⟨369548, by rfl⟩ : syracuseStep 492731 = 739097) B739097
theorem B492807 : Blo 491791 492807 := bstep (se 1 (by rfl) ⟨369605, by rfl⟩ : syracuseStep 492807 = 739211) B739211
theorem B492815 : Blo 491791 492815 := bstep (se 1 (by rfl) ⟨369611, by rfl⟩ : syracuseStep 492815 = 739223) B739223
theorem B492859 : Blo 491791 492859 := bstep (se 1 (by rfl) ⟨369644, by rfl⟩ : syracuseStep 492859 = 739289) B739289
theorem B1410365 : Blo 491791 1410365 := bstep (se 3 (by rfl) ⟨264443, by rfl⟩ : syracuseStep 1410365 = 528887) B528887
theorem B492935 : Blo 491791 492935 := bstep (se 1 (by rfl) ⟨369701, by rfl⟩ : syracuseStep 492935 = 739403) B739403
theorem B492943 : Blo 491791 492943 := bstep (se 1 (by rfl) ⟨369707, by rfl⟩ : syracuseStep 492943 = 739415) B739415
theorem B1672595 : Blo 491791 1672595 := bstep (se 1 (by rfl) ⟨1254446, by rfl⟩ : syracuseStep 1672595 = 2508893) B2508893
theorem B787897 : Blo 491791 787897 := bstep (se 2 (by rfl) ⟨295461, by rfl⟩ : syracuseStep 787897 = 590923) B590923
theorem B492987 : Blo 491791 492987 := bstep (se 1 (by rfl) ⟨369740, by rfl⟩ : syracuseStep 492987 = 739481) B739481
theorem B493063 : Blo 491791 493063 := bstep (se 1 (by rfl) ⟨369797, by rfl⟩ : syracuseStep 493063 = 739595) B739595
theorem B493071 : Blo 491791 493071 := bstep (se 1 (by rfl) ⟨369803, by rfl⟩ : syracuseStep 493071 = 739607) B739607
theorem B493115 : Blo 491791 493115 := bstep (se 1 (by rfl) ⟨369836, by rfl⟩ : syracuseStep 493115 = 739673) B739673
theorem B493191 : Blo 491791 493191 := bstep (se 1 (by rfl) ⟨369893, by rfl⟩ : syracuseStep 493191 = 739787) B739787
theorem B493199 : Blo 491791 493199 := bstep (se 1 (by rfl) ⟨369899, by rfl⟩ : syracuseStep 493199 = 739799) B739799
theorem B1246873 : Blo 491791 1246873 := bstep (se 2 (by rfl) ⟨467577, by rfl⟩ : syracuseStep 1246873 = 935155) B935155
theorem B493243 : Blo 491791 493243 := bstep (se 1 (by rfl) ⟨369932, by rfl⟩ : syracuseStep 493243 = 739865) B739865
theorem B493319 : Blo 491791 493319 := bstep (se 1 (by rfl) ⟨369989, by rfl⟩ : syracuseStep 493319 = 739979) B739979
theorem B493327 : Blo 491791 493327 := bstep (se 1 (by rfl) ⟨369995, by rfl⟩ : syracuseStep 493327 = 739991) B739991
theorem B1247035 : Blo 491791 1247035 := bstep (se 1 (by rfl) ⟨935276, by rfl⟩ : syracuseStep 1247035 = 1870553) B1870553
theorem B493371 : Blo 491791 493371 := bstep (se 1 (by rfl) ⟨370028, by rfl⟩ : syracuseStep 493371 = 740057) B740057
theorem B493447 : Blo 491791 493447 := bstep (se 1 (by rfl) ⟨370085, by rfl⟩ : syracuseStep 493447 = 740171) B740171
theorem B493455 : Blo 491791 493455 := bstep (se 1 (by rfl) ⟨370091, by rfl⟩ : syracuseStep 493455 = 740183) B740183
theorem B493499 : Blo 491791 493499 := bstep (se 1 (by rfl) ⟨370124, by rfl⟩ : syracuseStep 493499 = 740249) B740249
theorem B1247177 : Blo 491791 1247177 := bstep (se 2 (by rfl) ⟨467691, by rfl⟩ : syracuseStep 1247177 = 935383) B935383
theorem B2492369 : Blo 491791 2492369 := bstep (se 2 (by rfl) ⟨934638, by rfl⟩ : syracuseStep 2492369 = 1869277) B1869277
theorem B493575 : Blo 491791 493575 := bstep (se 1 (by rfl) ⟨370181, by rfl⟩ : syracuseStep 493575 = 740363) B740363
theorem B10651661 : Blo 491791 10651661 := bstep (se 3 (by rfl) ⟨1997186, by rfl⟩ : syracuseStep 10651661 = 3994373) B3994373
theorem B493583 : Blo 491791 493583 := bstep (se 1 (by rfl) ⟨370187, by rfl⟩ : syracuseStep 493583 = 740375) B740375
theorem B493627 : Blo 491791 493627 := bstep (se 1 (by rfl) ⟨370220, by rfl⟩ : syracuseStep 493627 = 740441) B740441
theorem B493703 : Blo 491791 493703 := bstep (se 1 (by rfl) ⟨370277, by rfl⟩ : syracuseStep 493703 = 740555) B740555
theorem B493711 : Blo 491791 493711 := bstep (se 1 (by rfl) ⟨370283, by rfl⟩ : syracuseStep 493711 = 740567) B740567
theorem B493755 : Blo 491791 493755 := bstep (se 1 (by rfl) ⟨370316, by rfl⟩ : syracuseStep 493755 = 740633) B740633
theorem B2525377 : Blo 491791 2525377 := bstep (se 2 (by rfl) ⟨947016, by rfl⟩ : syracuseStep 2525377 = 1894033) B1894033
theorem B493831 : Blo 491791 493831 := bstep (se 1 (by rfl) ⟨370373, by rfl⟩ : syracuseStep 493831 = 740747) B740747
theorem B493839 : Blo 491791 493839 := bstep (se 1 (by rfl) ⟨370379, by rfl⟩ : syracuseStep 493839 = 740759) B740759
theorem B1247521 : Blo 491791 1247521 := bstep (se 2 (by rfl) ⟨467820, by rfl⟩ : syracuseStep 1247521 = 935641) B935641
theorem B493883 : Blo 491791 493883 := bstep (se 1 (by rfl) ⟨370412, by rfl⟩ : syracuseStep 493883 = 740825) B740825
theorem B2525555 : Blo 491791 2525555 := bstep (se 1 (by rfl) ⟨1894166, by rfl⟩ : syracuseStep 2525555 = 3788333) B3788333
theorem B854407 : Blo 491791 854407 := bstep (se 1 (by rfl) ⟨640805, by rfl⟩ : syracuseStep 854407 = 1281611) B1281611
theorem B493959 : Blo 491791 493959 := bstep (se 1 (by rfl) ⟨370469, by rfl⟩ : syracuseStep 493959 = 740939) B740939
theorem B493967 : Blo 491791 493967 := bstep (se 1 (by rfl) ⟨370475, by rfl⟩ : syracuseStep 493967 = 740951) B740951
theorem B1411481 : Blo 491791 1411481 := bstep (se 2 (by rfl) ⟨529305, by rfl⟩ : syracuseStep 1411481 = 1058611) B1058611
theorem B494011 : Blo 491791 494011 := bstep (se 1 (by rfl) ⟨370508, by rfl⟩ : syracuseStep 494011 = 741017) B741017
theorem B12061169 : Blo 491791 12061169 := bstep (se 2 (by rfl) ⟨4522938, by rfl⟩ : syracuseStep 12061169 = 9045877) B9045877
theorem B494087 : Blo 491791 494087 := bstep (se 1 (by rfl) ⟨370565, by rfl⟩ : syracuseStep 494087 = 741131) B741131
theorem B494095 : Blo 491791 494095 := bstep (se 1 (by rfl) ⟨370571, by rfl⟩ : syracuseStep 494095 = 741143) B741143
theorem B494139 : Blo 491791 494139 := bstep (se 1 (by rfl) ⟨370604, by rfl⟩ : syracuseStep 494139 = 741209) B741209
theorem B494215 : Blo 491791 494215 := bstep (se 1 (by rfl) ⟨370661, by rfl⟩ : syracuseStep 494215 = 741323) B741323
theorem B494223 : Blo 491791 494223 := bstep (se 1 (by rfl) ⟨370667, by rfl⟩ : syracuseStep 494223 = 741335) B741335
theorem B494267 : Blo 491791 494267 := bstep (se 1 (by rfl) ⟨370700, by rfl⟩ : syracuseStep 494267 = 741401) B741401
theorem B2820865 : Blo 491791 2820865 := bstep (se 2 (by rfl) ⟨1057824, by rfl⟩ : syracuseStep 2820865 = 2115649) B2115649
theorem B494343 : Blo 491791 494343 := bstep (se 1 (by rfl) ⟨370757, by rfl⟩ : syracuseStep 494343 = 741515) B741515
theorem B494351 : Blo 491791 494351 := bstep (se 1 (by rfl) ⟨370763, by rfl⟩ : syracuseStep 494351 = 741527) B741527
theorem B494395 : Blo 491791 494395 := bstep (se 1 (by rfl) ⟨370796, by rfl⟩ : syracuseStep 494395 = 741593) B741593
theorem B1248119 : Blo 491791 1248119 := bstep (se 1 (by rfl) ⟨936089, by rfl⟩ : syracuseStep 1248119 = 1872179) B1872179
theorem B494471 : Blo 491791 494471 := bstep (se 1 (by rfl) ⟨370853, by rfl⟩ : syracuseStep 494471 = 741707) B741707
theorem B494479 : Blo 491791 494479 := bstep (se 1 (by rfl) ⟨370859, by rfl⟩ : syracuseStep 494479 = 741719) B741719
theorem B494523 : Blo 491791 494523 := bstep (se 1 (by rfl) ⟨370892, by rfl⟩ : syracuseStep 494523 = 741785) B741785
theorem B494599 : Blo 491791 494599 := bstep (se 1 (by rfl) ⟨370949, by rfl⟩ : syracuseStep 494599 = 741899) B741899
theorem B494607 : Blo 491791 494607 := bstep (se 1 (by rfl) ⟨370955, by rfl⟩ : syracuseStep 494607 = 741911) B741911
theorem B494651 : Blo 491791 494651 := bstep (se 1 (by rfl) ⟨370988, by rfl⟩ : syracuseStep 494651 = 741977) B741977
theorem B494727 : Blo 491791 494727 := bstep (se 1 (by rfl) ⟨371045, by rfl⟩ : syracuseStep 494727 = 742091) B742091
theorem B494735 : Blo 491791 494735 := bstep (se 1 (by rfl) ⟨371051, by rfl⟩ : syracuseStep 494735 = 742103) B742103
theorem B3738797 : Blo 491791 3738797 := bstep (se 3 (by rfl) ⟨701024, by rfl⟩ : syracuseStep 3738797 = 1402049) B1402049
theorem B494779 : Blo 491791 494779 := bstep (se 1 (by rfl) ⟨371084, by rfl⟩ : syracuseStep 494779 = 742169) B742169
theorem B494855 : Blo 491791 494855 := bstep (se 1 (by rfl) ⟨371141, by rfl⟩ : syracuseStep 494855 = 742283) B742283
theorem B494863 : Blo 491791 494863 := bstep (se 1 (by rfl) ⟨371147, by rfl⟩ : syracuseStep 494863 = 742295) B742295
theorem B2821391 : Blo 491791 2821391 := bstep (se 1 (by rfl) ⟨2116043, by rfl⟩ : syracuseStep 2821391 = 4232087) B4232087
theorem B625963 : Blo 491791 625963 := bstep (se 1 (by rfl) ⟨469472, by rfl⟩ : syracuseStep 625963 = 938945) B938945
theorem B494907 : Blo 491791 494907 := bstep (se 1 (by rfl) ⟨371180, by rfl⟩ : syracuseStep 494907 = 742361) B742361
theorem B494983 : Blo 491791 494983 := bstep (se 1 (by rfl) ⟨371237, by rfl⟩ : syracuseStep 494983 = 742475) B742475
theorem B494991 : Blo 491791 494991 := bstep (se 1 (by rfl) ⟨371243, by rfl⟩ : syracuseStep 494991 = 742487) B742487
theorem B495035 : Blo 491791 495035 := bstep (se 1 (by rfl) ⟨371276, by rfl⟩ : syracuseStep 495035 = 742553) B742553
theorem B495111 : Blo 491791 495111 := bstep (se 1 (by rfl) ⟨371333, by rfl⟩ : syracuseStep 495111 = 742667) B742667
theorem B790031 : Blo 491791 790031 := bstep (se 1 (by rfl) ⟨592523, by rfl⟩ : syracuseStep 790031 = 1185047) B1185047
theorem B495119 : Blo 491791 495119 := bstep (se 1 (by rfl) ⟨371339, by rfl⟩ : syracuseStep 495119 = 742679) B742679
theorem B1773085 : Blo 491791 1773085 := bstep (se 3 (by rfl) ⟨332453, by rfl⟩ : syracuseStep 1773085 = 664907) B664907
theorem B495163 : Blo 491791 495163 := bstep (se 1 (by rfl) ⟨371372, by rfl⟩ : syracuseStep 495163 = 742745) B742745
theorem B528007 : Blo 491791 528007 := bstep (se 1 (by rfl) ⟨396005, by rfl⟩ : syracuseStep 528007 = 792011) B792011
theorem B495239 : Blo 491791 495239 := bstep (se 1 (by rfl) ⟨371429, by rfl⟩ : syracuseStep 495239 = 742859) B742859
theorem B495247 : Blo 491791 495247 := bstep (se 1 (by rfl) ⟨371435, by rfl⟩ : syracuseStep 495247 = 742871) B742871
theorem B495291 : Blo 491791 495291 := bstep (se 1 (by rfl) ⟨371468, by rfl⟩ : syracuseStep 495291 = 742937) B742937
theorem B7147237 : Blo 491791 7147237 := bstep (se 4 (by rfl) ⟨670053, by rfl⟩ : syracuseStep 7147237 = 1340107) B1340107
theorem B495367 : Blo 491791 495367 := bstep (se 1 (by rfl) ⟨371525, by rfl⟩ : syracuseStep 495367 = 743051) B743051
theorem B495375 : Blo 491791 495375 := bstep (se 1 (by rfl) ⟨371531, by rfl⟩ : syracuseStep 495375 = 743063) B743063
theorem B495419 : Blo 491791 495419 := bstep (se 1 (by rfl) ⟨371564, by rfl⟩ : syracuseStep 495419 = 743129) B743129
theorem B495495 : Blo 491791 495495 := bstep (se 1 (by rfl) ⟨371621, by rfl⟩ : syracuseStep 495495 = 743243) B743243
theorem B495503 : Blo 491791 495503 := bstep (se 1 (by rfl) ⟨371627, by rfl⟩ : syracuseStep 495503 = 743255) B743255
theorem B495547 : Blo 491791 495547 := bstep (se 1 (by rfl) ⟨371660, by rfl⟩ : syracuseStep 495547 = 743321) B743321
theorem B7606219 : Blo 491791 7606219 := bstep (se 1 (by rfl) ⟨5704664, by rfl⟩ : syracuseStep 7606219 = 11409329) B11409329
theorem B495623 : Blo 491791 495623 := bstep (se 1 (by rfl) ⟨371717, by rfl⟩ : syracuseStep 495623 = 743435) B743435
theorem B2494475 : Blo 491791 2494475 := bstep (se 1 (by rfl) ⟨1870856, by rfl⟩ : syracuseStep 2494475 = 3741713) B3741713
theorem B495631 : Blo 491791 495631 := bstep (se 1 (by rfl) ⟨371723, by rfl⟩ : syracuseStep 495631 = 743447) B743447
theorem B495675 : Blo 491791 495675 := bstep (se 1 (by rfl) ⟨371756, by rfl⟩ : syracuseStep 495675 = 743513) B743513
theorem B1249415 : Blo 491791 1249415 := bstep (se 1 (by rfl) ⟨937061, by rfl⟩ : syracuseStep 1249415 = 1874123) B1874123
theorem B495751 : Blo 491791 495751 := bstep (se 1 (by rfl) ⟨371813, by rfl⟩ : syracuseStep 495751 = 743627) B743627
theorem B495759 : Blo 491791 495759 := bstep (se 1 (by rfl) ⟨371819, by rfl⟩ : syracuseStep 495759 = 743639) B743639
theorem B2494637 : Blo 491791 2494637 := bstep (se 3 (by rfl) ⟨467744, by rfl⟩ : syracuseStep 2494637 = 935489) B935489
theorem B1249465 : Blo 491791 1249465 := bstep (se 2 (by rfl) ⟨468549, by rfl⟩ : syracuseStep 1249465 = 937099) B937099
theorem B626935 : Blo 491791 626935 := bstep (se 1 (by rfl) ⟨470201, by rfl⟩ : syracuseStep 626935 = 940403) B940403
theorem B12357953 : Blo 491791 12357953 := bstep (se 2 (by rfl) ⟨4634232, by rfl⟩ : syracuseStep 12357953 = 9268465) B9268465
theorem B2101639 : Blo 491791 2101639 := bstep (se 1 (by rfl) ⟨1576229, by rfl⟩ : syracuseStep 2101639 = 3152459) B3152459
theorem B528827 : Blo 491791 528827 := bstep (se 1 (by rfl) ⟨396620, by rfl⟩ : syracuseStep 528827 = 793241) B793241
theorem B2167249 : Blo 491791 2167249 := bstep (se 2 (by rfl) ⟨812718, by rfl⟩ : syracuseStep 2167249 = 1625437) B1625437
theorem B4231709 : Blo 491791 4231709 := bstep (se 3 (by rfl) ⟨793445, by rfl⟩ : syracuseStep 4231709 = 1586891) B1586891
theorem B627259 : Blo 491791 627259 := bstep (se 1 (by rfl) ⟨470444, by rfl⟩ : syracuseStep 627259 = 940889) B940889
theorem B1806967 : Blo 491791 1806967 := bstep (se 1 (by rfl) ⟨1355225, by rfl⟩ : syracuseStep 1806967 = 2710451) B2710451
theorem B2822849 : Blo 491791 2822849 := bstep (se 2 (by rfl) ⟨1058568, by rfl⟩ : syracuseStep 2822849 = 2117137) B2117137
theorem B1250063 : Blo 491791 1250063 := bstep (se 1 (by rfl) ⟨937547, by rfl⟩ : syracuseStep 1250063 = 1875095) B1875095
theorem B1872983 : Blo 491791 1872983 := bstep (se 1 (by rfl) ⟨1404737, by rfl⟩ : syracuseStep 1872983 = 2809475) B2809475
theorem B890003 : Blo 491791 890003 := bstep (se 1 (by rfl) ⟨667502, by rfl⟩ : syracuseStep 890003 = 1335005) B1335005
theorem B2364653 : Blo 491791 2364653 := bstep (se 3 (by rfl) ⟨443372, by rfl⟩ : syracuseStep 2364653 = 886745) B886745
theorem B1250761 : Blo 491791 1250761 := bstep (se 2 (by rfl) ⟨469035, by rfl⟩ : syracuseStep 1250761 = 938071) B938071
theorem B5608925 : Blo 491791 5608925 := bstep (se 3 (by rfl) ⟨1051673, by rfl⟩ : syracuseStep 5608925 = 2103347) B2103347
theorem B3741227 : Blo 491791 3741227 := bstep (se 1 (by rfl) ⟨2805920, by rfl⟩ : syracuseStep 3741227 = 5611841) B5611841
theorem B1873469 : Blo 491791 1873469 := bstep (se 3 (by rfl) ⟨351275, by rfl⟩ : syracuseStep 1873469 = 702551) B702551
theorem B1250903 : Blo 491791 1250903 := bstep (se 1 (by rfl) ⟨938177, by rfl⟩ : syracuseStep 1250903 = 1876355) B1876355
theorem B5346935 : Blo 491791 5346935 := bstep (se 1 (by rfl) ⟨4010201, by rfl⟩ : syracuseStep 5346935 = 8020403) B8020403
theorem B2496257 : Blo 491791 2496257 := bstep (se 2 (by rfl) ⟨936096, by rfl⟩ : syracuseStep 2496257 = 1872193) B1872193
theorem B1775495 : Blo 491791 1775495 := bstep (se 1 (by rfl) ⟨1331621, by rfl⟩ : syracuseStep 1775495 = 2663243) B2663243
theorem B1185671 : Blo 491791 1185671 := bstep (se 1 (by rfl) ⟨889253, by rfl⟩ : syracuseStep 1185671 = 1778507) B1778507
theorem B1087379 : Blo 491791 1087379 := bstep (se 1 (by rfl) ⟨815534, by rfl⟩ : syracuseStep 1087379 = 1631069) B1631069
theorem B2857369 : Blo 491791 2857369 := bstep (se 2 (by rfl) ⟨1071513, by rfl⟩ : syracuseStep 2857369 = 2143027) B2143027
theorem B1055177 : Blo 491791 1055177 := bstep (se 2 (by rfl) ⟨395691, by rfl⟩ : syracuseStep 1055177 = 791383) B791383
theorem B2497067 : Blo 491791 2497067 := bstep (se 1 (by rfl) ⟨1872800, by rfl⟩ : syracuseStep 2497067 = 3745601) B3745601
theorem B3414899 : Blo 491791 3414899 := bstep (se 1 (by rfl) ⟨2561174, by rfl⟩ : syracuseStep 3414899 = 5122349) B5122349
theorem B1874897 : Blo 491791 1874897 := bstep (se 2 (by rfl) ⟨703086, by rfl⟩ : syracuseStep 1874897 = 1406173) B1406173
theorem B17538053 : Blo 491791 17538053 := bstep (se 4 (by rfl) ⟨1644192, by rfl⟩ : syracuseStep 17538053 = 3288385) B3288385
theorem B2006045 : Blo 491791 2006045 := bstep (se 3 (by rfl) ⟨376133, by rfl⟩ : syracuseStep 2006045 = 752267) B752267
theorem B1055929 : Blo 491791 1055929 := bstep (se 2 (by rfl) ⟨395973, by rfl⟩ : syracuseStep 1055929 = 791947) B791947
theorem B12623363 : Blo 491791 12623363 := bstep (se 1 (by rfl) ⟨9467522, by rfl⟩ : syracuseStep 12623363 = 18935045) B18935045
theorem B1252979 : Blo 491791 1252979 := bstep (se 1 (by rfl) ⟨939734, by rfl⟩ : syracuseStep 1252979 = 1879469) B1879469
theorem B2498363 : Blo 491791 2498363 := bstep (se 1 (by rfl) ⟨1873772, by rfl⟩ : syracuseStep 2498363 = 3747545) B3747545
theorem B2105297 : Blo 491791 2105297 := bstep (se 2 (by rfl) ⟨789486, by rfl⟩ : syracuseStep 2105297 = 1578973) B1578973
theorem B2498525 : Blo 491791 2498525 := bstep (se 3 (by rfl) ⟨468473, by rfl⟩ : syracuseStep 2498525 = 936947) B936947
theorem B1253495 : Blo 491791 1253495 := bstep (se 1 (by rfl) ⟨940121, by rfl⟩ : syracuseStep 1253495 = 1880243) B1880243
theorem B2498849 : Blo 491791 2498849 := bstep (se 2 (by rfl) ⟨937068, by rfl⟩ : syracuseStep 2498849 = 1874137) B1874137
theorem B1122707 : Blo 491791 1122707 := bstep (se 1 (by rfl) ⟨842030, by rfl⟩ : syracuseStep 1122707 = 1684061) B1684061
theorem B1122761 : Blo 491791 1122761 := bstep (se 2 (by rfl) ⟨421035, by rfl⟩ : syracuseStep 1122761 = 842071) B842071
theorem B1057313 : Blo 491791 1057313 := bstep (se 2 (by rfl) ⟨396492, by rfl⟩ : syracuseStep 1057313 = 792985) B792985
theorem B1581611 : Blo 491791 1581611 := bstep (se 1 (by rfl) ⟨1186208, by rfl⟩ : syracuseStep 1581611 = 2372417) B2372417
theorem B1876567 : Blo 491791 1876567 := bstep (se 1 (by rfl) ⟨1407425, by rfl⟩ : syracuseStep 1876567 = 2814851) B2814851
theorem B2138825 : Blo 491791 2138825 := bstep (se 2 (by rfl) ⟨802059, by rfl⟩ : syracuseStep 2138825 = 1604119) B1604119
theorem B4760369 : Blo 491791 4760369 := bstep (se 2 (by rfl) ⟨1785138, by rfl⟩ : syracuseStep 4760369 = 3570277) B3570277
theorem B631687 : Blo 491791 631687 := bstep (se 1 (by rfl) ⟨473765, by rfl⟩ : syracuseStep 631687 = 947531) B947531
theorem B1876871 : Blo 491791 1876871 := bstep (se 1 (by rfl) ⟨1407653, by rfl⟩ : syracuseStep 1876871 = 2815307) B2815307
theorem B1877053 : Blo 491791 1877053 := bstep (se 3 (by rfl) ⟨351947, by rfl⟩ : syracuseStep 1877053 = 703895) B703895
theorem B1254487 : Blo 491791 1254487 := bstep (se 1 (by rfl) ⟨940865, by rfl⟩ : syracuseStep 1254487 = 1881731) B1881731
theorem B2499821 : Blo 491791 2499821 := bstep (se 3 (by rfl) ⟨468716, by rfl⟩ : syracuseStep 2499821 = 937433) B937433
theorem B664951 : Blo 491791 664951 := bstep (se 1 (by rfl) ⟨498713, by rfl⟩ : syracuseStep 664951 = 997427) B997427
theorem B1123703 : Blo 491791 1123703 := bstep (se 1 (by rfl) ⟨842777, by rfl⟩ : syracuseStep 1123703 = 1685555) B1685555
theorem B1254791 : Blo 491791 1254791 := bstep (se 1 (by rfl) ⟨941093, by rfl⟩ : syracuseStep 1254791 = 1882187) B1882187
theorem B1254923 : Blo 491791 1254923 := bstep (se 1 (by rfl) ⟨941192, by rfl⟩ : syracuseStep 1254923 = 1882385) B1882385
theorem B10102801 : Blo 491791 10102801 := bstep (se 2 (by rfl) ⟨3788550, by rfl⟩ : syracuseStep 10102801 = 7577101) B7577101
theorem B2500631 : Blo 491791 2500631 := bstep (se 1 (by rfl) ⟨1875473, by rfl⟩ : syracuseStep 2500631 = 3750947) B3750947
theorem B4204781 : Blo 491791 4204781 := bstep (se 3 (by rfl) ⟨788396, by rfl⟩ : syracuseStep 4204781 = 1576793) B1576793
theorem B8005877 : Blo 491791 8005877 := bstep (se 5 (by rfl) ⟨375275, by rfl⟩ : syracuseStep 8005877 = 750551) B750551
theorem B2369843 : Blo 491791 2369843 := bstep (se 1 (by rfl) ⟨1777382, by rfl⟩ : syracuseStep 2369843 = 3554765) B3554765
theorem B1288601 : Blo 491791 1288601 := bstep (se 2 (by rfl) ⟨483225, by rfl⟩ : syracuseStep 1288601 = 966451) B966451
theorem B3156509 : Blo 491791 3156509 := bstep (se 3 (by rfl) ⟨591845, by rfl⟩ : syracuseStep 3156509 = 1183691) B1183691
theorem B3648077 : Blo 491791 3648077 := bstep (se 3 (by rfl) ⟨684014, by rfl⟩ : syracuseStep 3648077 = 1368029) B1368029
theorem B1878785 : Blo 491791 1878785 := bstep (se 2 (by rfl) ⟨704544, by rfl⟩ : syracuseStep 1878785 = 1409089) B1409089
theorem B4205465 : Blo 491791 4205465 := bstep (se 2 (by rfl) ⟨1577049, by rfl⟩ : syracuseStep 4205465 = 3154099) B3154099
theorem B830479 : Blo 491791 830479 := bstep (se 1 (by rfl) ⟨622859, by rfl⟩ : syracuseStep 830479 = 1245719) B1245719
theorem B1453373 : Blo 491791 1453373 := bstep (se 3 (by rfl) ⟨272507, by rfl⟩ : syracuseStep 1453373 = 545015) B545015
theorem B7581113 : Blo 491791 7581113 := bstep (se 2 (by rfl) ⟨2842917, by rfl⟩ : syracuseStep 7581113 = 5685835) B5685835
theorem B831019 : Blo 491791 831019 := bstep (se 1 (by rfl) ⟨623264, by rfl⟩ : syracuseStep 831019 = 1246529) B1246529
theorem B831161 : Blo 491791 831161 := bstep (se 2 (by rfl) ⟨311685, by rfl⟩ : syracuseStep 831161 = 623371) B623371
theorem B1584841 : Blo 491791 1584841 := bstep (se 2 (by rfl) ⟨594315, by rfl⟩ : syracuseStep 1584841 = 1188631) B1188631
theorem B2666375 : Blo 491791 2666375 := bstep (se 1 (by rfl) ⟨1999781, by rfl⟩ : syracuseStep 2666375 = 3999563) B3999563
theorem B1879955 : Blo 491791 1879955 := bstep (se 1 (by rfl) ⟨1409966, by rfl⟩ : syracuseStep 1879955 = 2819933) B2819933
theorem B9482285 : Blo 491791 9482285 := bstep (se 3 (by rfl) ⟨1777928, by rfl⟩ : syracuseStep 9482285 = 3555857) B3555857
theorem B700535 : Blo 491791 700535 := bstep (se 1 (by rfl) ⟨525401, by rfl⟩ : syracuseStep 700535 = 1050803) B1050803
theorem B831863 : Blo 491791 831863 := bstep (se 1 (by rfl) ⟨623897, by rfl⟩ : syracuseStep 831863 = 1247795) B1247795
theorem B1126775 : Blo 491791 1126775 := bstep (se 1 (by rfl) ⟨845081, by rfl⟩ : syracuseStep 1126775 = 1690163) B1690163
theorem B1880455 : Blo 491791 1880455 := bstep (se 1 (by rfl) ⟨1410341, by rfl⟩ : syracuseStep 1880455 = 2820683) B2820683
theorem B9024119 : Blo 491791 9024119 := bstep (se 1 (by rfl) ⟨6768089, by rfl⟩ : syracuseStep 9024119 = 13536179) B13536179
theorem B8991425 : Blo 491791 8991425 := bstep (se 2 (by rfl) ⟨3371784, by rfl⟩ : syracuseStep 8991425 = 6743569) B6743569
theorem B832315 : Blo 491791 832315 := bstep (se 1 (by rfl) ⟨624236, by rfl⟩ : syracuseStep 832315 = 1248473) B1248473
theorem B832457 : Blo 491791 832457 := bstep (se 2 (by rfl) ⟨312171, by rfl⟩ : syracuseStep 832457 = 624343) B624343
theorem B2372611 : Blo 491791 2372611 := bstep (se 1 (by rfl) ⟨1779458, by rfl⟩ : syracuseStep 2372611 = 3558917) B3558917
theorem B2503709 : Blo 491791 2503709 := bstep (se 3 (by rfl) ⟨469445, by rfl⟩ : syracuseStep 2503709 = 938891) B938891
theorem B2995393 : Blo 491791 2995393 := bstep (se 2 (by rfl) ⟨1123272, by rfl⟩ : syracuseStep 2995393 = 2246545) B2246545
theorem B3159431 : Blo 491791 3159431 := bstep (se 1 (by rfl) ⟨2369573, by rfl⟩ : syracuseStep 3159431 = 4739147) B4739147
theorem B2504195 : Blo 491791 2504195 := bstep (se 1 (by rfl) ⟨1878146, by rfl⟩ : syracuseStep 2504195 = 3756293) B3756293
theorem B701959 : Blo 491791 701959 := bstep (se 1 (by rfl) ⟨526469, by rfl⟩ : syracuseStep 701959 = 1052939) B1052939
theorem B833159 : Blo 491791 833159 := bstep (se 1 (by rfl) ⟨624869, by rfl⟩ : syracuseStep 833159 = 1249739) B1249739
theorem B2668261 : Blo 491791 2668261 := bstep (se 4 (by rfl) ⟨250149, by rfl⟩ : syracuseStep 2668261 = 500299) B500299
theorem B1783567 : Blo 491791 1783567 := bstep (se 1 (by rfl) ⟨1337675, by rfl⟩ : syracuseStep 1783567 = 2675351) B2675351
theorem B702523 : Blo 491791 702523 := bstep (se 1 (by rfl) ⟨526892, by rfl⟩ : syracuseStep 702523 = 1053785) B1053785
theorem B3749975 : Blo 491791 3749975 := bstep (se 1 (by rfl) ⟨2812481, by rfl⟩ : syracuseStep 3749975 = 5624963) B5624963
theorem B669881 : Blo 491791 669881 := bstep (se 2 (by rfl) ⟨251205, by rfl⟩ : syracuseStep 669881 = 502411) B502411
theorem B833807 : Blo 491791 833807 := bstep (se 1 (by rfl) ⟨625355, by rfl⟩ : syracuseStep 833807 = 1250711) B1250711
theorem B4209155 : Blo 491791 4209155 := bstep (se 1 (by rfl) ⟨3156866, by rfl⟩ : syracuseStep 4209155 = 6313733) B6313733
theorem B1784387 : Blo 491791 1784387 := bstep (se 1 (by rfl) ⟨1338290, by rfl⟩ : syracuseStep 1784387 = 2676581) B2676581
theorem B10697507 : Blo 491791 10697507 := bstep (se 1 (by rfl) ⟨8023130, by rfl⟩ : syracuseStep 10697507 = 16046261) B16046261
theorem B834347 : Blo 491791 834347 := bstep (se 1 (by rfl) ⟨625760, by rfl⟩ : syracuseStep 834347 = 1251521) B1251521
theorem B703417 : Blo 491791 703417 := bstep (se 2 (by rfl) ⟨263781, by rfl⟩ : syracuseStep 703417 = 527563) B527563
theorem B2505815 : Blo 491791 2505815 := bstep (se 1 (by rfl) ⟨1879361, by rfl⟩ : syracuseStep 2505815 = 3758723) B3758723
theorem B834745 : Blo 491791 834745 := bstep (se 2 (by rfl) ⟨313029, by rfl⟩ : syracuseStep 834745 = 626059) B626059
theorem B2506301 : Blo 491791 2506301 := bstep (se 3 (by rfl) ⟨469931, by rfl⟩ : syracuseStep 2506301 = 939863) B939863
theorem B835447 : Blo 491791 835447 := bstep (se 1 (by rfl) ⟨626585, by rfl⟩ : syracuseStep 835447 = 1253171) B1253171
theorem B835643 : Blo 491791 835643 := bstep (se 1 (by rfl) ⟨626732, by rfl⟩ : syracuseStep 835643 = 1253465) B1253465
theorem B704647 : Blo 491791 704647 := bstep (se 1 (by rfl) ⟨528485, by rfl⟩ : syracuseStep 704647 = 1056971) B1056971
theorem B737723 : Blo 491791 737723 := bstep (se 1 (by rfl) ⟨553292, by rfl⟩ : syracuseStep 737723 = 1106585) B1106585
theorem B836041 : Blo 491791 836041 := bstep (se 2 (by rfl) ⟨313515, by rfl⟩ : syracuseStep 836041 = 627031) B627031
theorem B737783 : Blo 491791 737783 := bstep (se 1 (by rfl) ⟨553337, by rfl⟩ : syracuseStep 737783 = 1106675) B1106675
theorem B737807 : Blo 491791 737807 := bstep (se 1 (by rfl) ⟨553355, by rfl⟩ : syracuseStep 737807 = 1106711) B1106711
theorem B737849 : Blo 491791 737849 := bstep (se 2 (by rfl) ⟨276693, by rfl⟩ : syracuseStep 737849 = 553387) B553387
theorem B2310743 : Blo 491791 2310743 := bstep (se 1 (by rfl) ⟨1733057, by rfl⟩ : syracuseStep 2310743 = 3466115) B3466115
theorem B737927 : Blo 491791 737927 := bstep (se 1 (by rfl) ⟨553445, by rfl⟩ : syracuseStep 737927 = 1106891) B1106891
theorem B737963 : Blo 491791 737963 := bstep (se 1 (by rfl) ⟨553472, by rfl⟩ : syracuseStep 737963 = 1106945) B1106945
theorem B737993 : Blo 491791 737993 := bstep (se 2 (by rfl) ⟨276747, by rfl⟩ : syracuseStep 737993 = 553495) B553495
theorem B738107 : Blo 491791 738107 := bstep (se 1 (by rfl) ⟨553580, by rfl⟩ : syracuseStep 738107 = 1107161) B1107161
theorem B934715 : Blo 491791 934715 := bstep (se 1 (by rfl) ⟨701036, by rfl⟩ : syracuseStep 934715 = 1402073) B1402073
theorem B705353 : Blo 491791 705353 := bstep (se 2 (by rfl) ⟨264507, by rfl⟩ : syracuseStep 705353 = 529015) B529015
theorem B3162995 : Blo 491791 3162995 := bstep (se 1 (by rfl) ⟨2372246, by rfl⟩ : syracuseStep 3162995 = 4744493) B4744493
theorem B2114419 : Blo 491791 2114419 := bstep (se 1 (by rfl) ⟨1585814, by rfl⟩ : syracuseStep 2114419 = 3171629) B3171629
theorem B738167 : Blo 491791 738167 := bstep (se 1 (by rfl) ⟨553625, by rfl⟩ : syracuseStep 738167 = 1107251) B1107251
theorem B738191 : Blo 491791 738191 := bstep (se 1 (by rfl) ⟨553643, by rfl⟩ : syracuseStep 738191 = 1107287) B1107287
theorem B738233 : Blo 491791 738233 := bstep (se 2 (by rfl) ⟨276837, by rfl⟩ : syracuseStep 738233 = 553675) B553675
theorem B705467 : Blo 491791 705467 := bstep (se 1 (by rfl) ⟨529100, by rfl⟩ : syracuseStep 705467 = 1058201) B1058201
theorem B738311 : Blo 491791 738311 := bstep (se 1 (by rfl) ⟨553733, by rfl⟩ : syracuseStep 738311 = 1107467) B1107467
theorem B738347 : Blo 491791 738347 := bstep (se 1 (by rfl) ⟨553760, by rfl⟩ : syracuseStep 738347 = 1107521) B1107521
theorem B738377 : Blo 491791 738377 := bstep (se 2 (by rfl) ⟨276891, by rfl⟩ : syracuseStep 738377 = 553783) B553783
theorem B2376877 : Blo 491791 2376877 := bstep (se 3 (by rfl) ⟨445664, by rfl⟩ : syracuseStep 2376877 = 891329) B891329
theorem B738491 : Blo 491791 738491 := bstep (se 1 (by rfl) ⟨553868, by rfl⟩ : syracuseStep 738491 = 1107737) B1107737
theorem B2114761 : Blo 491791 2114761 := bstep (se 2 (by rfl) ⟨793035, by rfl⟩ : syracuseStep 2114761 = 1586071) B1586071
theorem B738551 : Blo 491791 738551 := bstep (se 1 (by rfl) ⟨553913, by rfl⟩ : syracuseStep 738551 = 1107827) B1107827
theorem B738575 : Blo 491791 738575 := bstep (se 1 (by rfl) ⟨553931, by rfl⟩ : syracuseStep 738575 = 1107863) B1107863
theorem B935201 : Blo 491791 935201 := bstep (se 2 (by rfl) ⟨350700, by rfl⟩ : syracuseStep 935201 = 701401) B701401
theorem B2508083 : Blo 491791 2508083 := bstep (se 1 (by rfl) ⟨1881062, by rfl⟩ : syracuseStep 2508083 = 3762125) B3762125
theorem B738617 : Blo 491791 738617 := bstep (se 2 (by rfl) ⟨276981, by rfl⟩ : syracuseStep 738617 = 553963) B553963
theorem B738695 : Blo 491791 738695 := bstep (se 1 (by rfl) ⟨554021, by rfl⟩ : syracuseStep 738695 = 1108043) B1108043
theorem B738731 : Blo 491791 738731 := bstep (se 1 (by rfl) ⟨554048, by rfl⟩ : syracuseStep 738731 = 1108097) B1108097
theorem B738761 : Blo 491791 738761 := bstep (se 2 (by rfl) ⟨277035, by rfl⟩ : syracuseStep 738761 = 554071) B554071
theorem B738875 : Blo 491791 738875 := bstep (se 1 (by rfl) ⟨554156, by rfl⟩ : syracuseStep 738875 = 1108313) B1108313
theorem B738935 : Blo 491791 738935 := bstep (se 1 (by rfl) ⟨554201, by rfl⟩ : syracuseStep 738935 = 1108403) B1108403
theorem B935543 : Blo 491791 935543 := bstep (se 1 (by rfl) ⟨701657, by rfl⟩ : syracuseStep 935543 = 1403315) B1403315
theorem B2508407 : Blo 491791 2508407 := bstep (se 1 (by rfl) ⟨1881305, by rfl⟩ : syracuseStep 2508407 = 3762611) B3762611
theorem B738959 : Blo 491791 738959 := bstep (se 1 (by rfl) ⟨554219, by rfl⟩ : syracuseStep 738959 = 1108439) B1108439
theorem B739001 : Blo 491791 739001 := bstep (se 2 (by rfl) ⟨277125, by rfl⟩ : syracuseStep 739001 = 554251) B554251
theorem B739079 : Blo 491791 739079 := bstep (se 1 (by rfl) ⟨554309, by rfl⟩ : syracuseStep 739079 = 1108619) B1108619
theorem B4015909 : Blo 491791 4015909 := bstep (se 4 (by rfl) ⟨376491, by rfl⟩ : syracuseStep 4015909 = 752983) B752983
theorem B739115 : Blo 491791 739115 := bstep (se 1 (by rfl) ⟨554336, by rfl⟩ : syracuseStep 739115 = 1108673) B1108673
theorem B739145 : Blo 491791 739145 := bstep (se 2 (by rfl) ⟨277179, by rfl⟩ : syracuseStep 739145 = 554359) B554359
theorem B1001335 : Blo 491791 1001335 := bstep (se 1 (by rfl) ⟨751001, by rfl⟩ : syracuseStep 1001335 = 1502003) B1502003
theorem B739259 : Blo 491791 739259 := bstep (se 1 (by rfl) ⟨554444, by rfl⟩ : syracuseStep 739259 = 1108889) B1108889
theorem B739319 : Blo 491791 739319 := bstep (se 1 (by rfl) ⟨554489, by rfl⟩ : syracuseStep 739319 = 1108979) B1108979
theorem B739343 : Blo 491791 739343 := bstep (se 1 (by rfl) ⟨554507, by rfl⟩ : syracuseStep 739343 = 1109015) B1109015
theorem B739385 : Blo 491791 739385 := bstep (se 2 (by rfl) ⟨277269, by rfl⟩ : syracuseStep 739385 = 554539) B554539
theorem B739463 : Blo 491791 739463 := bstep (se 1 (by rfl) ⟨554597, by rfl⟩ : syracuseStep 739463 = 1109195) B1109195
theorem B739499 : Blo 491791 739499 := bstep (se 1 (by rfl) ⟨554624, by rfl⟩ : syracuseStep 739499 = 1109249) B1109249
theorem B739529 : Blo 491791 739529 := bstep (se 2 (by rfl) ⟨277323, by rfl⟩ : syracuseStep 739529 = 554647) B554647
theorem B2115821 : Blo 491791 2115821 := bstep (se 3 (by rfl) ⟨396716, by rfl⟩ : syracuseStep 2115821 = 793433) B793433
theorem B739643 : Blo 491791 739643 := bstep (se 1 (by rfl) ⟨554732, by rfl⟩ : syracuseStep 739643 = 1109465) B1109465
theorem B739703 : Blo 491791 739703 := bstep (se 1 (by rfl) ⟨554777, by rfl⟩ : syracuseStep 739703 = 1109555) B1109555
theorem B739727 : Blo 491791 739727 := bstep (se 1 (by rfl) ⟨554795, by rfl⟩ : syracuseStep 739727 = 1109591) B1109591
theorem B1067411 : Blo 491791 1067411 := bstep (se 1 (by rfl) ⟨800558, by rfl⟩ : syracuseStep 1067411 = 1601117) B1601117
theorem B739769 : Blo 491791 739769 := bstep (se 2 (by rfl) ⟨277413, by rfl⟩ : syracuseStep 739769 = 554827) B554827
theorem B739847 : Blo 491791 739847 := bstep (se 1 (by rfl) ⟨554885, by rfl⟩ : syracuseStep 739847 = 1109771) B1109771
theorem B739883 : Blo 491791 739883 := bstep (se 1 (by rfl) ⟨554912, by rfl⟩ : syracuseStep 739883 = 1109825) B1109825
theorem B2509379 : Blo 491791 2509379 := bstep (se 1 (by rfl) ⟨1882034, by rfl⟩ : syracuseStep 2509379 = 3764069) B3764069
theorem B739913 : Blo 491791 739913 := bstep (se 2 (by rfl) ⟨277467, by rfl⟩ : syracuseStep 739913 = 554935) B554935
theorem B740027 : Blo 491791 740027 := bstep (se 1 (by rfl) ⟨555020, by rfl⟩ : syracuseStep 740027 = 1110041) B1110041
theorem B740087 : Blo 491791 740087 := bstep (se 1 (by rfl) ⟨555065, by rfl⟩ : syracuseStep 740087 = 1110131) B1110131
theorem B740111 : Blo 491791 740111 := bstep (se 1 (by rfl) ⟨555083, by rfl⟩ : syracuseStep 740111 = 1110167) B1110167
theorem B4016947 : Blo 491791 4016947 := bstep (se 1 (by rfl) ⟨3012710, by rfl⟩ : syracuseStep 4016947 = 6025421) B6025421
theorem B740153 : Blo 491791 740153 := bstep (se 2 (by rfl) ⟨277557, by rfl⟩ : syracuseStep 740153 = 555115) B555115
theorem B740231 : Blo 491791 740231 := bstep (se 1 (by rfl) ⟨555173, by rfl⟩ : syracuseStep 740231 = 1110347) B1110347
theorem B2509703 : Blo 491791 2509703 := bstep (se 1 (by rfl) ⟨1882277, by rfl⟩ : syracuseStep 2509703 = 3764555) B3764555
theorem B740267 : Blo 491791 740267 := bstep (se 1 (by rfl) ⟨555200, by rfl⟩ : syracuseStep 740267 = 1110401) B1110401
theorem B740297 : Blo 491791 740297 := bstep (se 2 (by rfl) ⟨277611, by rfl⟩ : syracuseStep 740297 = 555223) B555223
theorem B740411 : Blo 491791 740411 := bstep (se 1 (by rfl) ⟨555308, by rfl⟩ : syracuseStep 740411 = 1110617) B1110617
theorem B740471 : Blo 491791 740471 := bstep (se 1 (by rfl) ⟨555353, by rfl⟩ : syracuseStep 740471 = 1110707) B1110707
theorem B740495 : Blo 491791 740495 := bstep (se 1 (by rfl) ⟨555371, by rfl⟩ : syracuseStep 740495 = 1110743) B1110743
theorem B937145 : Blo 491791 937145 := bstep (se 2 (by rfl) ⟨351429, by rfl⟩ : syracuseStep 937145 = 702859) B702859
theorem B740537 : Blo 491791 740537 := bstep (se 2 (by rfl) ⟨277701, by rfl⟩ : syracuseStep 740537 = 555403) B555403
theorem B740615 : Blo 491791 740615 := bstep (se 1 (by rfl) ⟨555461, by rfl⟩ : syracuseStep 740615 = 1110923) B1110923
theorem B740651 : Blo 491791 740651 := bstep (se 1 (by rfl) ⟨555488, by rfl⟩ : syracuseStep 740651 = 1110977) B1110977
theorem B740681 : Blo 491791 740681 := bstep (se 2 (by rfl) ⟨277755, by rfl⟩ : syracuseStep 740681 = 555511) B555511
theorem B740795 : Blo 491791 740795 := bstep (se 1 (by rfl) ⟨555596, by rfl⟩ : syracuseStep 740795 = 1111193) B1111193
theorem B740855 : Blo 491791 740855 := bstep (se 1 (by rfl) ⟨555641, by rfl⟩ : syracuseStep 740855 = 1111283) B1111283
theorem B937487 : Blo 491791 937487 := bstep (se 1 (by rfl) ⟨703115, by rfl⟩ : syracuseStep 937487 = 1406231) B1406231
theorem B740879 : Blo 491791 740879 := bstep (se 1 (by rfl) ⟨555659, by rfl⟩ : syracuseStep 740879 = 1111319) B1111319
theorem B740921 : Blo 491791 740921 := bstep (se 2 (by rfl) ⟨277845, by rfl⟩ : syracuseStep 740921 = 555691) B555691
theorem B740999 : Blo 491791 740999 := bstep (se 1 (by rfl) ⟨555749, by rfl⟩ : syracuseStep 740999 = 1111499) B1111499
theorem B741035 : Blo 491791 741035 := bstep (se 1 (by rfl) ⟨555776, by rfl⟩ : syracuseStep 741035 = 1111553) B1111553
theorem B1003193 : Blo 491791 1003193 := bstep (se 2 (by rfl) ⟨376197, by rfl⟩ : syracuseStep 1003193 = 752395) B752395
theorem B2707145 : Blo 491791 2707145 := bstep (se 2 (by rfl) ⟨1015179, by rfl⟩ : syracuseStep 2707145 = 2030359) B2030359
theorem B741065 : Blo 491791 741065 := bstep (se 2 (by rfl) ⟨277899, by rfl⟩ : syracuseStep 741065 = 555799) B555799
theorem B741179 : Blo 491791 741179 := bstep (se 1 (by rfl) ⟨555884, by rfl⟩ : syracuseStep 741179 = 1111769) B1111769
theorem B741239 : Blo 491791 741239 := bstep (se 1 (by rfl) ⟨555929, by rfl⟩ : syracuseStep 741239 = 1111859) B1111859
theorem B741263 : Blo 491791 741263 := bstep (se 1 (by rfl) ⟨555947, by rfl⟩ : syracuseStep 741263 = 1111895) B1111895
theorem B741305 : Blo 491791 741305 := bstep (se 2 (by rfl) ⟨277989, by rfl⟩ : syracuseStep 741305 = 555979) B555979
theorem B741383 : Blo 491791 741383 := bstep (se 1 (by rfl) ⟨556037, by rfl⟩ : syracuseStep 741383 = 1112075) B1112075
theorem B9457681 : Blo 491791 9457681 := bstep (se 2 (by rfl) ⟨3546630, by rfl⟩ : syracuseStep 9457681 = 7093261) B7093261
theorem B741419 : Blo 491791 741419 := bstep (se 1 (by rfl) ⟨556064, by rfl⟩ : syracuseStep 741419 = 1112129) B1112129
theorem B741449 : Blo 491791 741449 := bstep (se 2 (by rfl) ⟨278043, by rfl⟩ : syracuseStep 741449 = 556087) B556087
theorem B6475949 : Blo 491791 6475949 := bstep (se 3 (by rfl) ⟨1214240, by rfl⟩ : syracuseStep 6475949 = 2428481) B2428481
theorem B741563 : Blo 491791 741563 := bstep (se 1 (by rfl) ⟨556172, by rfl⟩ : syracuseStep 741563 = 1112345) B1112345
theorem B741623 : Blo 491791 741623 := bstep (se 1 (by rfl) ⟨556217, by rfl⟩ : syracuseStep 741623 = 1112435) B1112435
theorem B741647 : Blo 491791 741647 := bstep (se 1 (by rfl) ⟨556235, by rfl⟩ : syracuseStep 741647 = 1112471) B1112471
theorem B741689 : Blo 491791 741689 := bstep (se 2 (by rfl) ⟨278133, by rfl⟩ : syracuseStep 741689 = 556267) B556267
theorem B938299 : Blo 491791 938299 := bstep (se 1 (by rfl) ⟨703724, by rfl⟩ : syracuseStep 938299 = 1407449) B1407449
theorem B938375 : Blo 491791 938375 := bstep (se 1 (by rfl) ⟨703781, by rfl⟩ : syracuseStep 938375 = 1407563) B1407563
theorem B741767 : Blo 491791 741767 := bstep (se 1 (by rfl) ⟨556325, by rfl⟩ : syracuseStep 741767 = 1112651) B1112651
theorem B741803 : Blo 491791 741803 := bstep (se 1 (by rfl) ⟨556352, by rfl⟩ : syracuseStep 741803 = 1112705) B1112705
theorem B741833 : Blo 491791 741833 := bstep (se 2 (by rfl) ⟨278187, by rfl⟩ : syracuseStep 741833 = 556375) B556375
theorem B3166685 : Blo 491791 3166685 := bstep (se 3 (by rfl) ⟨593753, by rfl⟩ : syracuseStep 3166685 = 1187507) B1187507
theorem B741947 : Blo 491791 741947 := bstep (se 1 (by rfl) ⟨556460, by rfl⟩ : syracuseStep 741947 = 1112921) B1112921
theorem B1430131 : Blo 491791 1430131 := bstep (se 1 (by rfl) ⟨1072598, by rfl⟩ : syracuseStep 1430131 = 2145197) B2145197
theorem B742007 : Blo 491791 742007 := bstep (se 1 (by rfl) ⟨556505, by rfl⟩ : syracuseStep 742007 = 1113011) B1113011
theorem B742031 : Blo 491791 742031 := bstep (se 1 (by rfl) ⟨556523, by rfl⟩ : syracuseStep 742031 = 1113047) B1113047
theorem B742073 : Blo 491791 742073 := bstep (se 2 (by rfl) ⟨278277, by rfl⟩ : syracuseStep 742073 = 556555) B556555
theorem B3166913 : Blo 491791 3166913 := bstep (se 2 (by rfl) ⟨1187592, by rfl⟩ : syracuseStep 3166913 = 2375185) B2375185
theorem B5329637 : Blo 491791 5329637 := bstep (se 4 (by rfl) ⟨499653, by rfl⟩ : syracuseStep 5329637 = 999307) B999307
theorem B742151 : Blo 491791 742151 := bstep (se 1 (by rfl) ⟨556613, by rfl⟩ : syracuseStep 742151 = 1113227) B1113227
theorem B938785 : Blo 491791 938785 := bstep (se 2 (by rfl) ⟨352044, by rfl⟩ : syracuseStep 938785 = 704089) B704089
theorem B742187 : Blo 491791 742187 := bstep (se 1 (by rfl) ⟨556640, by rfl⟩ : syracuseStep 742187 = 1113281) B1113281
theorem B742217 : Blo 491791 742217 := bstep (se 2 (by rfl) ⟨278331, by rfl⟩ : syracuseStep 742217 = 556663) B556663
theorem B6411097 : Blo 491791 6411097 := bstep (se 2 (by rfl) ⟨2404161, by rfl⟩ : syracuseStep 6411097 = 4808323) B4808323
theorem B2675591 : Blo 491791 2675591 := bstep (se 1 (by rfl) ⟨2006693, by rfl⟩ : syracuseStep 2675591 = 4013387) B4013387
theorem B578491 : Blo 491791 578491 := bstep (se 1 (by rfl) ⟨433868, by rfl⟩ : syracuseStep 578491 = 867737) B867737
theorem B742331 : Blo 491791 742331 := bstep (se 1 (by rfl) ⟨556748, by rfl⟩ : syracuseStep 742331 = 1113497) B1113497
theorem B742391 : Blo 491791 742391 := bstep (se 1 (by rfl) ⟨556793, by rfl⟩ : syracuseStep 742391 = 1113587) B1113587
theorem B1692683 : Blo 491791 1692683 := bstep (se 1 (by rfl) ⟨1269512, by rfl⟩ : syracuseStep 1692683 = 2539025) B2539025
theorem B742415 : Blo 491791 742415 := bstep (se 1 (by rfl) ⟨556811, by rfl⟩ : syracuseStep 742415 = 1113623) B1113623
theorem B742457 : Blo 491791 742457 := bstep (se 2 (by rfl) ⟨278421, by rfl⟩ : syracuseStep 742457 = 556843) B556843
theorem B1758275 : Blo 491791 1758275 := bstep (se 1 (by rfl) ⟨1318706, by rfl⟩ : syracuseStep 1758275 = 2637413) B2637413
theorem B939127 : Blo 491791 939127 := bstep (se 1 (by rfl) ⟨704345, by rfl⟩ : syracuseStep 939127 = 1408691) B1408691
theorem B742535 : Blo 491791 742535 := bstep (se 1 (by rfl) ⟨556901, by rfl⟩ : syracuseStep 742535 = 1113803) B1113803
theorem B742571 : Blo 491791 742571 := bstep (se 1 (by rfl) ⟨556928, by rfl⟩ : syracuseStep 742571 = 1113857) B1113857
theorem B742601 : Blo 491791 742601 := bstep (se 2 (by rfl) ⟨278475, by rfl⟩ : syracuseStep 742601 = 556951) B556951
theorem B1660175 : Blo 491791 1660175 := bstep (se 1 (by rfl) ⟨1245131, by rfl⟩ : syracuseStep 1660175 = 2490263) B2490263
theorem B7132475 : Blo 491791 7132475 := bstep (se 1 (by rfl) ⟨5349356, by rfl⟩ : syracuseStep 7132475 = 10698713) B10698713
theorem B742715 : Blo 491791 742715 := bstep (se 1 (by rfl) ⟨557036, by rfl⟩ : syracuseStep 742715 = 1114073) B1114073
theorem B742775 : Blo 491791 742775 := bstep (se 1 (by rfl) ⟨557081, by rfl⟩ : syracuseStep 742775 = 1114163) B1114163
theorem B742799 : Blo 491791 742799 := bstep (se 1 (by rfl) ⟨557099, by rfl⟩ : syracuseStep 742799 = 1114199) B1114199
theorem B742841 : Blo 491791 742841 := bstep (se 2 (by rfl) ⟨278565, by rfl⟩ : syracuseStep 742841 = 557131) B557131
theorem B2807243 : Blo 491791 2807243 := bstep (se 1 (by rfl) ⟨2105432, by rfl⟩ : syracuseStep 2807243 = 4210865) B4210865
theorem B742919 : Blo 491791 742919 := bstep (se 1 (by rfl) ⟨557189, by rfl⟩ : syracuseStep 742919 = 1114379) B1114379
theorem B2676235 : Blo 491791 2676235 := bstep (se 1 (by rfl) ⟨2007176, by rfl⟩ : syracuseStep 2676235 = 4014353) B4014353
theorem B1660445 : Blo 491791 1660445 := bstep (se 3 (by rfl) ⟨311333, by rfl⟩ : syracuseStep 1660445 = 622667) B622667
theorem B742955 : Blo 491791 742955 := bstep (se 1 (by rfl) ⟨557216, by rfl⟩ : syracuseStep 742955 = 1114433) B1114433
theorem B742985 : Blo 491791 742985 := bstep (se 2 (by rfl) ⟨278619, by rfl⟩ : syracuseStep 742985 = 557239) B557239
theorem B743099 : Blo 491791 743099 := bstep (se 1 (by rfl) ⟨557324, by rfl⟩ : syracuseStep 743099 = 1114649) B1114649
theorem B743159 : Blo 491791 743159 := bstep (se 1 (by rfl) ⟨557369, by rfl⟩ : syracuseStep 743159 = 1114739) B1114739
theorem B1333007 : Blo 491791 1333007 := bstep (se 1 (by rfl) ⟨999755, by rfl⟩ : syracuseStep 1333007 = 1999511) B1999511
theorem B743183 : Blo 491791 743183 := bstep (se 1 (by rfl) ⟨557387, by rfl⟩ : syracuseStep 743183 = 1114775) B1114775
theorem B743225 : Blo 491791 743225 := bstep (se 2 (by rfl) ⟨278709, by rfl⟩ : syracuseStep 743225 = 557419) B557419
theorem B743303 : Blo 491791 743303 := bstep (se 1 (by rfl) ⟨557477, by rfl⟩ : syracuseStep 743303 = 1114955) B1114955
theorem B2021267 : Blo 491791 2021267 := bstep (se 1 (by rfl) ⟨1515950, by rfl⟩ : syracuseStep 2021267 = 3031901) B3031901
theorem B743339 : Blo 491791 743339 := bstep (se 1 (by rfl) ⟨557504, by rfl⟩ : syracuseStep 743339 = 1115009) B1115009
theorem B743369 : Blo 491791 743369 := bstep (se 2 (by rfl) ⟨278763, by rfl⟩ : syracuseStep 743369 = 557527) B557527
theorem B3790795 : Blo 491791 3790795 := bstep (se 1 (by rfl) ⟨2843096, by rfl⟩ : syracuseStep 3790795 = 5686193) B5686193
theorem B743483 : Blo 491791 743483 := bstep (se 1 (by rfl) ⟨557612, by rfl⟩ : syracuseStep 743483 = 1115225) B1115225
theorem B743543 : Blo 491791 743543 := bstep (se 1 (by rfl) ⟨557657, by rfl⟩ : syracuseStep 743543 = 1115315) B1115315
theorem B743567 : Blo 491791 743567 := bstep (se 1 (by rfl) ⟨557675, by rfl⟩ : syracuseStep 743567 = 1115351) B1115351
theorem B743609 : Blo 491791 743609 := bstep (se 2 (by rfl) ⟨278853, by rfl⟩ : syracuseStep 743609 = 557707) B557707
theorem B743687 : Blo 491791 743687 := bstep (se 1 (by rfl) ⟨557765, by rfl⟩ : syracuseStep 743687 = 1115531) B1115531
theorem B842119 : Blo 491791 842119 := bstep (se 1 (by rfl) ⟨631589, by rfl⟩ : syracuseStep 842119 = 1263179) B1263179
theorem B1333793 : Blo 491791 1333793 := bstep (se 2 (by rfl) ⟨500172, by rfl⟩ : syracuseStep 1333793 = 1000345) B1000345
theorem B940729 : Blo 491791 940729 := bstep (se 2 (by rfl) ⟨352773, by rfl⟩ : syracuseStep 940729 = 705547) B705547
theorem B711467 : Blo 491791 711467 := bstep (se 1 (by rfl) ⟨533600, by rfl⟩ : syracuseStep 711467 = 1067201) B1067201
theorem B1661849 : Blo 491791 1661849 := bstep (se 2 (by rfl) ⟨623193, by rfl⟩ : syracuseStep 1661849 = 1246387) B1246387
theorem B941071 : Blo 491791 941071 := bstep (se 1 (by rfl) ⟨705803, by rfl⟩ : syracuseStep 941071 = 1411607) B1411607
theorem B1662551 : Blo 491791 1662551 := bstep (se 1 (by rfl) ⟨1246913, by rfl⟩ : syracuseStep 1662551 = 2493827) B2493827
theorem B1400591 : Blo 491791 1400591 := bstep (se 1 (by rfl) ⟨1050443, by rfl⟩ : syracuseStep 1400591 = 2100887) B2100887
theorem B1663037 : Blo 491791 1663037 := bstep (se 3 (by rfl) ⟨311819, by rfl⟩ : syracuseStep 1663037 = 623639) B623639
theorem B1335869 : Blo 491791 1335869 := bstep (se 3 (by rfl) ⟨250475, by rfl⟩ : syracuseStep 1335869 = 500951) B500951
theorem B1106567 : Blo 491791 1106567 := bstep (se 1 (by rfl) ⟨829925, by rfl⟩ : syracuseStep 1106567 = 1659851) B1659851
theorem B1106747 : Blo 491791 1106747 := bstep (se 1 (by rfl) ⟨830060, by rfl⟩ : syracuseStep 1106747 = 1660121) B1660121
theorem B1336151 : Blo 491791 1336151 := bstep (se 1 (by rfl) ⟨1002113, by rfl⟩ : syracuseStep 1336151 = 2004227) B2004227
theorem B1106873 : Blo 491791 1106873 := bstep (se 2 (by rfl) ⟨415077, by rfl⟩ : syracuseStep 1106873 = 830155) B830155
theorem B1401857 : Blo 491791 1401857 := bstep (se 2 (by rfl) ⟨525696, by rfl⟩ : syracuseStep 1401857 = 1051393) B1051393
theorem B1107215 : Blo 491791 1107215 := bstep (se 1 (by rfl) ⟨830411, by rfl⟩ : syracuseStep 1107215 = 1660823) B1660823
theorem B1107233 : Blo 491791 1107233 := bstep (se 2 (by rfl) ⟨415212, by rfl⟩ : syracuseStep 1107233 = 830425) B830425
theorem B1664441 : Blo 491791 1664441 := bstep (se 2 (by rfl) ⟨624165, by rfl⟩ : syracuseStep 1664441 = 1248331) B1248331
theorem B714169 : Blo 491791 714169 := bstep (se 2 (by rfl) ⟨267813, by rfl⟩ : syracuseStep 714169 = 535627) B535627
theorem B1107575 : Blo 491791 1107575 := bstep (se 1 (by rfl) ⟨830681, by rfl⟩ : syracuseStep 1107575 = 1661363) B1661363
theorem B1107755 : Blo 491791 1107755 := bstep (se 1 (by rfl) ⟨830816, by rfl⟩ : syracuseStep 1107755 = 1661633) B1661633
theorem B1665035 : Blo 491791 1665035 := bstep (se 1 (by rfl) ⟨1248776, by rfl⟩ : syracuseStep 1665035 = 2497553) B2497553
theorem B6514805 : Blo 491791 6514805 := bstep (se 5 (by rfl) ⟨305381, by rfl⟩ : syracuseStep 6514805 = 610763) B610763
theorem B1665143 : Blo 491791 1665143 := bstep (se 1 (by rfl) ⟨1248857, by rfl⟩ : syracuseStep 1665143 = 2497715) B2497715
theorem B1108115 : Blo 491791 1108115 := bstep (se 1 (by rfl) ⟨831086, by rfl⟩ : syracuseStep 1108115 = 1662173) B1662173
theorem B1108169 : Blo 491791 1108169 := bstep (se 2 (by rfl) ⟨415563, by rfl⟩ : syracuseStep 1108169 = 831127) B831127
theorem B3172553 : Blo 491791 3172553 := bstep (se 2 (by rfl) ⟨1189707, by rfl⟩ : syracuseStep 3172553 = 2379415) B2379415
theorem B3008819 : Blo 491791 3008819 := bstep (se 1 (by rfl) ⟨2256614, by rfl⟩ : syracuseStep 3008819 = 4513229) B4513229
theorem B846281 : Blo 491791 846281 := bstep (se 2 (by rfl) ⟨317355, by rfl⟩ : syracuseStep 846281 = 634711) B634711
theorem B3860995 : Blo 491791 3860995 := bstep (se 1 (by rfl) ⟨2895746, by rfl⟩ : syracuseStep 3860995 = 5791493) B5791493
theorem B2255447 : Blo 491791 2255447 := bstep (se 1 (by rfl) ⟨1691585, by rfl⟩ : syracuseStep 2255447 = 3383171) B3383171
theorem B1403507 : Blo 491791 1403507 := bstep (se 1 (by rfl) ⟨1052630, by rfl⟩ : syracuseStep 1403507 = 2105261) B2105261
theorem B1665737 : Blo 491791 1665737 := bstep (se 2 (by rfl) ⟨624651, by rfl⟩ : syracuseStep 1665737 = 1249303) B1249303
theorem B5630795 : Blo 491791 5630795 := bstep (se 1 (by rfl) ⟨4223096, by rfl⟩ : syracuseStep 5630795 = 8446193) B8446193
theorem B1108871 : Blo 491791 1108871 := bstep (se 1 (by rfl) ⟨831653, by rfl⟩ : syracuseStep 1108871 = 1663307) B1663307
theorem B3763097 : Blo 491791 3763097 := bstep (se 2 (by rfl) ⟨1411161, by rfl⟩ : syracuseStep 3763097 = 2822323) B2822323
theorem B1109051 : Blo 491791 1109051 := bstep (se 1 (by rfl) ⟨831788, by rfl⟩ : syracuseStep 1109051 = 1663577) B1663577
theorem B1403963 : Blo 491791 1403963 := bstep (se 1 (by rfl) ⟨1052972, by rfl⟩ : syracuseStep 1403963 = 2105945) B2105945
theorem B2255959 : Blo 491791 2255959 := bstep (se 1 (by rfl) ⟨1691969, by rfl⟩ : syracuseStep 2255959 = 3383939) B3383939
theorem B1109177 : Blo 491791 1109177 := bstep (se 2 (by rfl) ⟨415941, by rfl⟩ : syracuseStep 1109177 = 831883) B831883
theorem B748873 : Blo 491791 748873 := bstep (se 2 (by rfl) ⟨280827, by rfl⟩ : syracuseStep 748873 = 561655) B561655
theorem B1666439 : Blo 491791 1666439 := bstep (se 1 (by rfl) ⟨1249829, by rfl⟩ : syracuseStep 1666439 = 2499659) B2499659
theorem B2813393 : Blo 491791 2813393 := bstep (se 2 (by rfl) ⟨1055022, by rfl⟩ : syracuseStep 2813393 = 2110045) B2110045
theorem B1109519 : Blo 491791 1109519 := bstep (se 1 (by rfl) ⟨832139, by rfl⟩ : syracuseStep 1109519 = 1664279) B1664279
theorem B1109537 : Blo 491791 1109537 := bstep (se 2 (by rfl) ⟨416076, by rfl⟩ : syracuseStep 1109537 = 832153) B832153
theorem B7237219 : Blo 491791 7237219 := bstep (se 1 (by rfl) ⟨5427914, by rfl⟩ : syracuseStep 7237219 = 10855829) B10855829
theorem B1666817 : Blo 491791 1666817 := bstep (se 2 (by rfl) ⟨625056, by rfl⟩ : syracuseStep 1666817 = 1250113) B1250113
theorem B1404715 : Blo 491791 1404715 := bstep (se 1 (by rfl) ⟨1053536, by rfl⟩ : syracuseStep 1404715 = 2107073) B2107073
theorem B23949107 : Blo 491791 23949107 := bstep (se 1 (by rfl) ⟨17961830, by rfl⟩ : syracuseStep 23949107 = 35923661) B35923661
theorem B1109879 : Blo 491791 1109879 := bstep (se 1 (by rfl) ⟨832409, by rfl⟩ : syracuseStep 1109879 = 1664819) B1664819
theorem B2813849 : Blo 491791 2813849 := bstep (se 2 (by rfl) ⟨1055193, by rfl⟩ : syracuseStep 2813849 = 2110387) B2110387
theorem B1110059 : Blo 491791 1110059 := bstep (se 1 (by rfl) ⟨832544, by rfl⟩ : syracuseStep 1110059 = 1665089) B1665089
theorem B1404989 : Blo 491791 1404989 := bstep (se 3 (by rfl) ⟨263435, by rfl⟩ : syracuseStep 1404989 = 526871) B526871
theorem B2027891 : Blo 491791 2027891 := bstep (se 1 (by rfl) ⟨1520918, by rfl⟩ : syracuseStep 2027891 = 3041837) B3041837
theorem B553351 : Blo 491791 553351 := bstep (se 1 (by rfl) ⟨415013, by rfl⟩ : syracuseStep 553351 = 830027) B830027
theorem B1110419 : Blo 491791 1110419 := bstep (se 1 (by rfl) ⟨832814, by rfl⟩ : syracuseStep 1110419 = 1665629) B1665629
theorem B1110473 : Blo 491791 1110473 := bstep (se 2 (by rfl) ⟨416427, by rfl⟩ : syracuseStep 1110473 = 832855) B832855
theorem B1667627 : Blo 491791 1667627 := bstep (se 1 (by rfl) ⟨1250720, by rfl⟩ : syracuseStep 1667627 = 2501441) B2501441
theorem B553531 : Blo 491791 553531 := bstep (se 1 (by rfl) ⟨415148, by rfl⟩ : syracuseStep 553531 = 830297) B830297
theorem B1405831 : Blo 491791 1405831 := bstep (se 1 (by rfl) ⟨1054373, by rfl⟩ : syracuseStep 1405831 = 2108747) B2108747
theorem B553999 : Blo 491791 553999 := bstep (se 1 (by rfl) ⟨415499, by rfl⟩ : syracuseStep 553999 = 830999) B830999
theorem B1111175 : Blo 491791 1111175 := bstep (se 1 (by rfl) ⟨833381, by rfl⟩ : syracuseStep 1111175 = 1666763) B1666763
theorem B1406105 : Blo 491791 1406105 := bstep (se 2 (by rfl) ⟨527289, by rfl⟩ : syracuseStep 1406105 = 1054579) B1054579
theorem B1111355 : Blo 491791 1111355 := bstep (se 1 (by rfl) ⟨833516, by rfl⟩ : syracuseStep 1111355 = 1667033) B1667033
theorem B1111481 : Blo 491791 1111481 := bstep (se 2 (by rfl) ⟨416805, by rfl⟩ : syracuseStep 1111481 = 833611) B833611
theorem B554503 : Blo 491791 554503 := bstep (se 1 (by rfl) ⟨415877, by rfl⟩ : syracuseStep 554503 = 831755) B831755
theorem B1603115 : Blo 491791 1603115 := bstep (se 1 (by rfl) ⟨1202336, by rfl⟩ : syracuseStep 1603115 = 2404673) B2404673
theorem B554683 : Blo 491791 554683 := bstep (se 1 (by rfl) ⟨416012, by rfl⟩ : syracuseStep 554683 = 832025) B832025
theorem B1111823 : Blo 491791 1111823 := bstep (se 1 (by rfl) ⟨833867, by rfl⟩ : syracuseStep 1111823 = 1667735) B1667735
theorem B1111841 : Blo 491791 1111841 := bstep (se 2 (by rfl) ⟨416940, by rfl⟩ : syracuseStep 1111841 = 833881) B833881
theorem B751403 : Blo 491791 751403 := bstep (se 1 (by rfl) ⟨563552, by rfl⟩ : syracuseStep 751403 = 1127105) B1127105
theorem B3176243 : Blo 491791 3176243 := bstep (se 1 (by rfl) ⟨2382182, by rfl⟩ : syracuseStep 3176243 = 4764365) B4764365
theorem B1668923 : Blo 491791 1668923 := bstep (se 1 (by rfl) ⟨1251692, by rfl⟩ : syracuseStep 1668923 = 2503385) B2503385
theorem B1112183 : Blo 491791 1112183 := bstep (se 1 (by rfl) ⟨834137, by rfl⟩ : syracuseStep 1112183 = 1668275) B1668275
theorem B555151 : Blo 491791 555151 := bstep (se 1 (by rfl) ⟨416363, by rfl⟩ : syracuseStep 555151 = 832727) B832727
theorem B1407233 : Blo 491791 1407233 := bstep (se 2 (by rfl) ⟨527712, by rfl⟩ : syracuseStep 1407233 = 1055425) B1055425
theorem B1669409 : Blo 491791 1669409 := bstep (se 2 (by rfl) ⟨626028, by rfl⟩ : syracuseStep 1669409 = 1252057) B1252057
theorem B1112363 : Blo 491791 1112363 := bstep (se 1 (by rfl) ⟨834272, by rfl⟩ : syracuseStep 1112363 = 1668545) B1668545
theorem B555655 : Blo 491791 555655 := bstep (se 1 (by rfl) ⟨416741, by rfl⟩ : syracuseStep 555655 = 833483) B833483
theorem B1112723 : Blo 491791 1112723 := bstep (se 1 (by rfl) ⟨834542, by rfl⟩ : syracuseStep 1112723 = 1669085) B1669085
theorem B1407689 : Blo 491791 1407689 := bstep (se 2 (by rfl) ⟨527883, by rfl⟩ : syracuseStep 1407689 = 1055767) B1055767
theorem B1112777 : Blo 491791 1112777 := bstep (se 2 (by rfl) ⟨417291, by rfl⟩ : syracuseStep 1112777 = 834583) B834583
theorem B555835 : Blo 491791 555835 := bstep (se 1 (by rfl) ⟨416876, by rfl⟩ : syracuseStep 555835 = 833753) B833753
theorem B1670003 : Blo 491791 1670003 := bstep (se 1 (by rfl) ⟨1252502, by rfl⟩ : syracuseStep 1670003 = 2505005) B2505005
theorem B5340107 : Blo 491791 5340107 := bstep (se 1 (by rfl) ⟨4005080, by rfl⟩ : syracuseStep 5340107 = 8010161) B8010161
theorem B1801169 : Blo 491791 1801169 := bstep (se 2 (by rfl) ⟨675438, by rfl⟩ : syracuseStep 1801169 = 1350877) B1350877
theorem B7109869 : Blo 491791 7109869 := bstep (se 3 (by rfl) ⟨1333100, by rfl⟩ : syracuseStep 7109869 = 2666201) B2666201
theorem B556303 : Blo 491791 556303 := bstep (se 1 (by rfl) ⟨417227, by rfl⟩ : syracuseStep 556303 = 834455) B834455
theorem B1113479 : Blo 491791 1113479 := bstep (se 1 (by rfl) ⟨835109, by rfl⟩ : syracuseStep 1113479 = 1670219) B1670219
theorem B4521401 : Blo 491791 4521401 := bstep (se 2 (by rfl) ⟨1695525, by rfl⟩ : syracuseStep 4521401 = 3391051) B3391051
theorem B1113659 : Blo 491791 1113659 := bstep (se 1 (by rfl) ⟨835244, by rfl⟩ : syracuseStep 1113659 = 1670489) B1670489
theorem B1113785 : Blo 491791 1113785 := bstep (se 2 (by rfl) ⟨417669, by rfl⟩ : syracuseStep 1113785 = 835339) B835339
theorem B1244929 : Blo 491791 1244929 := bstep (se 2 (by rfl) ⟨466848, by rfl⟩ : syracuseStep 1244929 = 933697) B933697
theorem B556807 : Blo 491791 556807 := bstep (se 1 (by rfl) ⟨417605, by rfl⟩ : syracuseStep 556807 = 835211) B835211
theorem B3374963 : Blo 491791 3374963 := bstep (se 1 (by rfl) ⟨2531222, by rfl⟩ : syracuseStep 3374963 = 5062445) B5062445
theorem B9633653 : Blo 491791 9633653 := bstep (se 5 (by rfl) ⟨451577, by rfl⟩ : syracuseStep 9633653 = 903155) B903155
theorem B4751257 : Blo 491791 4751257 := bstep (se 2 (by rfl) ⟨1781721, by rfl⟩ : syracuseStep 4751257 = 3563443) B3563443
theorem B556987 : Blo 491791 556987 := bstep (se 1 (by rfl) ⟨417740, by rfl⟩ : syracuseStep 556987 = 835481) B835481
theorem B1245203 : Blo 491791 1245203 := bstep (se 1 (by rfl) ⟨933902, by rfl⟩ : syracuseStep 1245203 = 1867805) B1867805
theorem B557095 : Blo 491791 557095 := bstep (se 1 (by rfl) ⟨417821, by rfl⟩ : syracuseStep 557095 = 835643) B835643
theorem B2490425 : Blo 491791 2490425 := bstep (se 2 (by rfl) ⟨933909, by rfl⟩ : syracuseStep 2490425 = 1867819) B1867819
theorem B1441963 : Blo 491791 1441963 := bstep (se 1 (by rfl) ⟨1081472, by rfl⟩ : syracuseStep 1441963 = 2162945) B2162945
theorem B491815 : Blo 491791 491815 := bstep (se 1 (by rfl) ⟨368861, by rfl⟩ : syracuseStep 491815 = 737723) B737723
theorem B1868093 : Blo 491791 1868093 := bstep (se 3 (by rfl) ⟨350267, by rfl⟩ : syracuseStep 1868093 = 700535) B700535
theorem B491855 : Blo 491791 491855 := bstep (se 1 (by rfl) ⟨368891, by rfl⟩ : syracuseStep 491855 = 737783) B737783
theorem B491871 : Blo 491791 491871 := bstep (se 1 (by rfl) ⟨368903, by rfl⟩ : syracuseStep 491871 = 737807) B737807
theorem B491899 : Blo 491791 491899 := bstep (se 1 (by rfl) ⟨368924, by rfl⟩ : syracuseStep 491899 = 737849) B737849
theorem B1540495 : Blo 491791 1540495 := bstep (se 1 (by rfl) ⟨1155371, by rfl⟩ : syracuseStep 1540495 = 2310743) B2310743
theorem B491951 : Blo 491791 491951 := bstep (se 1 (by rfl) ⟨368963, by rfl⟩ : syracuseStep 491951 = 737927) B737927
theorem B491975 : Blo 491791 491975 := bstep (se 1 (by rfl) ⟨368981, by rfl⟩ : syracuseStep 491975 = 737963) B737963
theorem B491995 : Blo 491791 491995 := bstep (se 1 (by rfl) ⟨368996, by rfl⟩ : syracuseStep 491995 = 737993) B737993
theorem B492071 : Blo 491791 492071 := bstep (se 1 (by rfl) ⟨369053, by rfl⟩ : syracuseStep 492071 = 738107) B738107
theorem B623143 : Blo 491791 623143 := bstep (se 1 (by rfl) ⟨467357, by rfl⟩ : syracuseStep 623143 = 934715) B934715
theorem B492111 : Blo 491791 492111 := bstep (se 1 (by rfl) ⟨369083, by rfl⟩ : syracuseStep 492111 = 738167) B738167
theorem B492127 : Blo 491791 492127 := bstep (se 1 (by rfl) ⟨369095, by rfl⟩ : syracuseStep 492127 = 738191) B738191
theorem B1114721 : Blo 491791 1114721 := bstep (se 2 (by rfl) ⟨418020, by rfl⟩ : syracuseStep 1114721 = 836041) B836041
theorem B492155 : Blo 491791 492155 := bstep (se 1 (by rfl) ⟨369116, by rfl⟩ : syracuseStep 492155 = 738233) B738233
theorem B1442443 : Blo 491791 1442443 := bstep (se 1 (by rfl) ⟨1081832, by rfl⟩ : syracuseStep 1442443 = 2163665) B2163665
theorem B492207 : Blo 491791 492207 := bstep (se 1 (by rfl) ⟨369155, by rfl⟩ : syracuseStep 492207 = 738311) B738311
theorem B492231 : Blo 491791 492231 := bstep (se 1 (by rfl) ⟨369173, by rfl⟩ : syracuseStep 492231 = 738347) B738347
theorem B492251 : Blo 491791 492251 := bstep (se 1 (by rfl) ⟨369188, by rfl⟩ : syracuseStep 492251 = 738377) B738377
theorem B492327 : Blo 491791 492327 := bstep (se 1 (by rfl) ⟨369245, by rfl⟩ : syracuseStep 492327 = 738491) B738491
theorem B492367 : Blo 491791 492367 := bstep (se 1 (by rfl) ⟨369275, by rfl⟩ : syracuseStep 492367 = 738551) B738551
theorem B492383 : Blo 491791 492383 := bstep (se 1 (by rfl) ⟨369287, by rfl⟩ : syracuseStep 492383 = 738575) B738575
theorem B623467 : Blo 491791 623467 := bstep (se 1 (by rfl) ⟨467600, by rfl⟩ : syracuseStep 623467 = 935201) B935201
theorem B1672055 : Blo 491791 1672055 := bstep (se 1 (by rfl) ⟨1254041, by rfl⟩ : syracuseStep 1672055 = 2508083) B2508083
theorem B492411 : Blo 491791 492411 := bstep (se 1 (by rfl) ⟨369308, by rfl⟩ : syracuseStep 492411 = 738617) B738617
theorem B492463 : Blo 491791 492463 := bstep (se 1 (by rfl) ⟨369347, by rfl⟩ : syracuseStep 492463 = 738695) B738695
theorem B1115063 : Blo 491791 1115063 := bstep (se 1 (by rfl) ⟨836297, by rfl⟩ : syracuseStep 1115063 = 1672595) B1672595
theorem B492487 : Blo 491791 492487 := bstep (se 1 (by rfl) ⟨369365, by rfl⟩ : syracuseStep 492487 = 738731) B738731
theorem B492507 : Blo 491791 492507 := bstep (se 1 (by rfl) ⟨369380, by rfl⟩ : syracuseStep 492507 = 738761) B738761
theorem B492583 : Blo 491791 492583 := bstep (se 1 (by rfl) ⟨369437, by rfl⟩ : syracuseStep 492583 = 738875) B738875
theorem B492623 : Blo 491791 492623 := bstep (se 1 (by rfl) ⟨369467, by rfl⟩ : syracuseStep 492623 = 738935) B738935
theorem B623695 : Blo 491791 623695 := bstep (se 1 (by rfl) ⟨467771, by rfl⟩ : syracuseStep 623695 = 935543) B935543
theorem B1672271 : Blo 491791 1672271 := bstep (se 1 (by rfl) ⟨1254203, by rfl⟩ : syracuseStep 1672271 = 2508407) B2508407
theorem B492639 : Blo 491791 492639 := bstep (se 1 (by rfl) ⟨369479, by rfl⟩ : syracuseStep 492639 = 738959) B738959
theorem B492667 : Blo 491791 492667 := bstep (se 1 (by rfl) ⟨369500, by rfl⟩ : syracuseStep 492667 = 739001) B739001
theorem B2819225 : Blo 491791 2819225 := bstep (se 2 (by rfl) ⟨1057209, by rfl⟩ : syracuseStep 2819225 = 2114419) B2114419
theorem B1410205 : Blo 491791 1410205 := bstep (se 3 (by rfl) ⟨264413, by rfl⟩ : syracuseStep 1410205 = 528827) B528827
theorem B492719 : Blo 491791 492719 := bstep (se 1 (by rfl) ⟨369539, by rfl⟩ : syracuseStep 492719 = 739079) B739079
theorem B492743 : Blo 491791 492743 := bstep (se 1 (by rfl) ⟨369557, by rfl⟩ : syracuseStep 492743 = 739115) B739115
theorem B492763 : Blo 491791 492763 := bstep (se 1 (by rfl) ⟨369572, by rfl⟩ : syracuseStep 492763 = 739145) B739145
theorem B492839 : Blo 491791 492839 := bstep (se 1 (by rfl) ⟨369629, by rfl⟩ : syracuseStep 492839 = 739259) B739259
theorem B492879 : Blo 491791 492879 := bstep (se 1 (by rfl) ⟨369659, by rfl⟩ : syracuseStep 492879 = 739319) B739319
theorem B492895 : Blo 491791 492895 := bstep (se 1 (by rfl) ⟨369671, by rfl⟩ : syracuseStep 492895 = 739343) B739343
theorem B492923 : Blo 491791 492923 := bstep (se 1 (by rfl) ⟨369692, by rfl⟩ : syracuseStep 492923 = 739385) B739385
theorem B492975 : Blo 491791 492975 := bstep (se 1 (by rfl) ⟨369731, by rfl⟩ : syracuseStep 492975 = 739463) B739463
theorem B492999 : Blo 491791 492999 := bstep (se 1 (by rfl) ⟨369749, by rfl⟩ : syracuseStep 492999 = 739499) B739499
theorem B1672649 : Blo 491791 1672649 := bstep (se 2 (by rfl) ⟨627243, by rfl⟩ : syracuseStep 1672649 = 1254487) B1254487
theorem B493019 : Blo 491791 493019 := bstep (se 1 (by rfl) ⟨369764, by rfl⟩ : syracuseStep 493019 = 739529) B739529
theorem B1410547 : Blo 491791 1410547 := bstep (se 1 (by rfl) ⟨1057910, by rfl⟩ : syracuseStep 1410547 = 2115821) B2115821
theorem B493095 : Blo 491791 493095 := bstep (se 1 (by rfl) ⟨369821, by rfl⟩ : syracuseStep 493095 = 739643) B739643
theorem B493135 : Blo 491791 493135 := bstep (se 1 (by rfl) ⟨369851, by rfl⟩ : syracuseStep 493135 = 739703) B739703
theorem B493151 : Blo 491791 493151 := bstep (se 1 (by rfl) ⟨369863, by rfl⟩ : syracuseStep 493151 = 739727) B739727
theorem B2819681 : Blo 491791 2819681 := bstep (se 2 (by rfl) ⟨1057380, by rfl⟩ : syracuseStep 2819681 = 2114761) B2114761
theorem B493179 : Blo 491791 493179 := bstep (se 1 (by rfl) ⟨369884, by rfl⟩ : syracuseStep 493179 = 739769) B739769
theorem B493231 : Blo 491791 493231 := bstep (se 1 (by rfl) ⟨369923, by rfl⟩ : syracuseStep 493231 = 739847) B739847
theorem B493255 : Blo 491791 493255 := bstep (se 1 (by rfl) ⟨369941, by rfl⟩ : syracuseStep 493255 = 739883) B739883
theorem B1672919 : Blo 491791 1672919 := bstep (se 1 (by rfl) ⟨1254689, by rfl⟩ : syracuseStep 1672919 = 2509379) B2509379
theorem B493275 : Blo 491791 493275 := bstep (se 1 (by rfl) ⟨369956, by rfl⟩ : syracuseStep 493275 = 739913) B739913
theorem B493351 : Blo 491791 493351 := bstep (se 1 (by rfl) ⟨370013, by rfl⟩ : syracuseStep 493351 = 740027) B740027
theorem B886601 : Blo 491791 886601 := bstep (se 2 (by rfl) ⟨332475, by rfl⟩ : syracuseStep 886601 = 664951) B664951
theorem B493391 : Blo 491791 493391 := bstep (se 1 (by rfl) ⟨370043, by rfl⟩ : syracuseStep 493391 = 740087) B740087
theorem B493407 : Blo 491791 493407 := bstep (se 1 (by rfl) ⟨370055, by rfl⟩ : syracuseStep 493407 = 740111) B740111
theorem B493435 : Blo 491791 493435 := bstep (se 1 (by rfl) ⟨370076, by rfl⟩ : syracuseStep 493435 = 740153) B740153
theorem B952225 : Blo 491791 952225 := bstep (se 2 (by rfl) ⟨357084, by rfl⟩ : syracuseStep 952225 = 714169) B714169
theorem B493487 : Blo 491791 493487 := bstep (se 1 (by rfl) ⟨370115, by rfl⟩ : syracuseStep 493487 = 740231) B740231
theorem B1673135 : Blo 491791 1673135 := bstep (se 1 (by rfl) ⟨1254851, by rfl⟩ : syracuseStep 1673135 = 2509703) B2509703
theorem B493511 : Blo 491791 493511 := bstep (se 1 (by rfl) ⟨370133, by rfl⟩ : syracuseStep 493511 = 740267) B740267
theorem B493531 : Blo 491791 493531 := bstep (se 1 (by rfl) ⟨370148, by rfl⟩ : syracuseStep 493531 = 740297) B740297
theorem B4491301 : Blo 491791 4491301 := bstep (se 4 (by rfl) ⟨421059, by rfl⟩ : syracuseStep 4491301 = 842119) B842119
theorem B4556837 : Blo 491791 4556837 := bstep (se 4 (by rfl) ⟨427203, by rfl⟩ : syracuseStep 4556837 = 854407) B854407
theorem B493607 : Blo 491791 493607 := bstep (se 1 (by rfl) ⟨370205, by rfl⟩ : syracuseStep 493607 = 740411) B740411
theorem B493647 : Blo 491791 493647 := bstep (se 1 (by rfl) ⟨370235, by rfl⟩ : syracuseStep 493647 = 740471) B740471
theorem B493663 : Blo 491791 493663 := bstep (se 1 (by rfl) ⟨370247, by rfl⟩ : syracuseStep 493663 = 740495) B740495
theorem B2492531 : Blo 491791 2492531 := bstep (se 1 (by rfl) ⟨1869398, by rfl⟩ : syracuseStep 2492531 = 3738797) B3738797
theorem B624763 : Blo 491791 624763 := bstep (se 1 (by rfl) ⟨468572, by rfl⟩ : syracuseStep 624763 = 937145) B937145
theorem B493691 : Blo 491791 493691 := bstep (se 1 (by rfl) ⟨370268, by rfl⟩ : syracuseStep 493691 = 740537) B740537
theorem B493743 : Blo 491791 493743 := bstep (se 1 (by rfl) ⟨370307, by rfl⟩ : syracuseStep 493743 = 740615) B740615
theorem B493767 : Blo 491791 493767 := bstep (se 1 (by rfl) ⟨370325, by rfl⟩ : syracuseStep 493767 = 740651) B740651
theorem B493787 : Blo 491791 493787 := bstep (se 1 (by rfl) ⟨370340, by rfl⟩ : syracuseStep 493787 = 740681) B740681
theorem B493863 : Blo 491791 493863 := bstep (se 1 (by rfl) ⟨370397, by rfl⟩ : syracuseStep 493863 = 740795) B740795
theorem B493903 : Blo 491791 493903 := bstep (se 1 (by rfl) ⟨370427, by rfl⟩ : syracuseStep 493903 = 740855) B740855
theorem B624991 : Blo 491791 624991 := bstep (se 1 (by rfl) ⟨468743, by rfl⟩ : syracuseStep 624991 = 937487) B937487
theorem B493919 : Blo 491791 493919 := bstep (se 1 (by rfl) ⟨370439, by rfl⟩ : syracuseStep 493919 = 740879) B740879
theorem B493947 : Blo 491791 493947 := bstep (se 1 (by rfl) ⟨370460, by rfl⟩ : syracuseStep 493947 = 740921) B740921
theorem B493999 : Blo 491791 493999 := bstep (se 1 (by rfl) ⟨370499, by rfl⟩ : syracuseStep 493999 = 740999) B740999
theorem B494023 : Blo 491791 494023 := bstep (se 1 (by rfl) ⟨370517, by rfl⟩ : syracuseStep 494023 = 741035) B741035
theorem B1804763 : Blo 491791 1804763 := bstep (se 1 (by rfl) ⟨1353572, by rfl⟩ : syracuseStep 1804763 = 2707145) B2707145
theorem B494043 : Blo 491791 494043 := bstep (se 1 (by rfl) ⟨370532, by rfl⟩ : syracuseStep 494043 = 741065) B741065
theorem B494119 : Blo 491791 494119 := bstep (se 1 (by rfl) ⟨370589, by rfl⟩ : syracuseStep 494119 = 741179) B741179
theorem B494159 : Blo 491791 494159 := bstep (se 1 (by rfl) ⟨370619, by rfl⟩ : syracuseStep 494159 = 741239) B741239
theorem B494175 : Blo 491791 494175 := bstep (se 1 (by rfl) ⟨370631, by rfl⟩ : syracuseStep 494175 = 741263) B741263
theorem B494203 : Blo 491791 494203 := bstep (se 1 (by rfl) ⟨370652, by rfl⟩ : syracuseStep 494203 = 741305) B741305
theorem B494255 : Blo 491791 494255 := bstep (se 1 (by rfl) ⟨370691, by rfl⟩ : syracuseStep 494255 = 741383) B741383
theorem B13470401 : Blo 491791 13470401 := bstep (se 2 (by rfl) ⟨5051400, by rfl⟩ : syracuseStep 13470401 = 10102801) B10102801
theorem B494279 : Blo 491791 494279 := bstep (se 1 (by rfl) ⟨370709, by rfl⟩ : syracuseStep 494279 = 741419) B741419
theorem B494299 : Blo 491791 494299 := bstep (se 1 (by rfl) ⟨370724, by rfl⟩ : syracuseStep 494299 = 741449) B741449
theorem B494375 : Blo 491791 494375 := bstep (se 1 (by rfl) ⟨370781, by rfl⟩ : syracuseStep 494375 = 741563) B741563
theorem B494415 : Blo 491791 494415 := bstep (se 1 (by rfl) ⟨370811, by rfl⟩ : syracuseStep 494415 = 741623) B741623
theorem B494431 : Blo 491791 494431 := bstep (se 1 (by rfl) ⟨370823, by rfl⟩ : syracuseStep 494431 = 741647) B741647
theorem B494459 : Blo 491791 494459 := bstep (se 1 (by rfl) ⟨370844, by rfl⟩ : syracuseStep 494459 = 741689) B741689
theorem B625583 : Blo 491791 625583 := bstep (se 1 (by rfl) ⟨469187, by rfl⟩ : syracuseStep 625583 = 938375) B938375
theorem B494511 : Blo 491791 494511 := bstep (se 1 (by rfl) ⟨370883, by rfl⟩ : syracuseStep 494511 = 741767) B741767
theorem B494535 : Blo 491791 494535 := bstep (se 1 (by rfl) ⟨370901, by rfl⟩ : syracuseStep 494535 = 741803) B741803
theorem B494555 : Blo 491791 494555 := bstep (se 1 (by rfl) ⟨370916, by rfl⟩ : syracuseStep 494555 = 741833) B741833
theorem B2821139 : Blo 491791 2821139 := bstep (se 1 (by rfl) ⟨2115854, by rfl⟩ : syracuseStep 2821139 = 4231709) B4231709
theorem B494631 : Blo 491791 494631 := bstep (se 1 (by rfl) ⟨370973, by rfl⟩ : syracuseStep 494631 = 741947) B741947
theorem B494671 : Blo 491791 494671 := bstep (se 1 (by rfl) ⟨371003, by rfl⟩ : syracuseStep 494671 = 742007) B742007
theorem B494687 : Blo 491791 494687 := bstep (se 1 (by rfl) ⟨371015, by rfl⟩ : syracuseStep 494687 = 742031) B742031
theorem B494715 : Blo 491791 494715 := bstep (se 1 (by rfl) ⟨371036, by rfl⟩ : syracuseStep 494715 = 742073) B742073
theorem B494767 : Blo 491791 494767 := bstep (se 1 (by rfl) ⟨371075, by rfl⟩ : syracuseStep 494767 = 742151) B742151
theorem B494791 : Blo 491791 494791 := bstep (se 1 (by rfl) ⟨371093, by rfl⟩ : syracuseStep 494791 = 742187) B742187
theorem B494811 : Blo 491791 494811 := bstep (se 1 (by rfl) ⟨371108, by rfl⟩ : syracuseStep 494811 = 742217) B742217
theorem B9637157 : Blo 491791 9637157 := bstep (se 4 (by rfl) ⟨903483, by rfl⟩ : syracuseStep 9637157 = 1806967) B1806967
theorem B494887 : Blo 491791 494887 := bstep (se 1 (by rfl) ⟨371165, by rfl⟩ : syracuseStep 494887 = 742331) B742331
theorem B494927 : Blo 491791 494927 := bstep (se 1 (by rfl) ⟨371195, by rfl⟩ : syracuseStep 494927 = 742391) B742391
theorem B5147993 : Blo 491791 5147993 := bstep (se 2 (by rfl) ⟨1930497, by rfl⟩ : syracuseStep 5147993 = 3860995) B3860995
theorem B494943 : Blo 491791 494943 := bstep (se 1 (by rfl) ⟨371207, by rfl⟩ : syracuseStep 494943 = 742415) B742415
theorem B494971 : Blo 491791 494971 := bstep (se 1 (by rfl) ⟨371228, by rfl⟩ : syracuseStep 494971 = 742457) B742457
theorem B1248655 : Blo 491791 1248655 := bstep (se 1 (by rfl) ⟨936491, by rfl⟩ : syracuseStep 1248655 = 1872983) B1872983
theorem B495023 : Blo 491791 495023 := bstep (se 1 (by rfl) ⟨371267, by rfl⟩ : syracuseStep 495023 = 742535) B742535
theorem B593335 : Blo 491791 593335 := bstep (se 1 (by rfl) ⟨445001, by rfl⟩ : syracuseStep 593335 = 890003) B890003
theorem B495047 : Blo 491791 495047 := bstep (se 1 (by rfl) ⟨371285, by rfl⟩ : syracuseStep 495047 = 742571) B742571
theorem B495067 : Blo 491791 495067 := bstep (se 1 (by rfl) ⟨371300, by rfl⟩ : syracuseStep 495067 = 742601) B742601
theorem B1576435 : Blo 491791 1576435 := bstep (se 1 (by rfl) ⟨1182326, by rfl⟩ : syracuseStep 1576435 = 2364653) B2364653
theorem B4754983 : Blo 491791 4754983 := bstep (se 1 (by rfl) ⟨3566237, by rfl⟩ : syracuseStep 4754983 = 7132475) B7132475
theorem B495143 : Blo 491791 495143 := bstep (se 1 (by rfl) ⟨371357, by rfl⟩ : syracuseStep 495143 = 742715) B742715
theorem B495183 : Blo 491791 495183 := bstep (se 1 (by rfl) ⟨371387, by rfl⟩ : syracuseStep 495183 = 742775) B742775
theorem B495199 : Blo 491791 495199 := bstep (se 1 (by rfl) ⟨371399, by rfl⟩ : syracuseStep 495199 = 742799) B742799
theorem B495227 : Blo 491791 495227 := bstep (se 1 (by rfl) ⟨371420, by rfl⟩ : syracuseStep 495227 = 742841) B742841
theorem B1871495 : Blo 491791 1871495 := bstep (se 1 (by rfl) ⟨1403621, by rfl⟩ : syracuseStep 1871495 = 2807243) B2807243
theorem B3739283 : Blo 491791 3739283 := bstep (se 1 (by rfl) ⟨2804462, by rfl⟩ : syracuseStep 3739283 = 5608925) B5608925
theorem B495279 : Blo 491791 495279 := bstep (se 1 (by rfl) ⟨371459, by rfl⟩ : syracuseStep 495279 = 742919) B742919
theorem B2494151 : Blo 491791 2494151 := bstep (se 1 (by rfl) ⟨1870613, by rfl⟩ : syracuseStep 2494151 = 3741227) B3741227
theorem B495303 : Blo 491791 495303 := bstep (se 1 (by rfl) ⟨371477, by rfl⟩ : syracuseStep 495303 = 742955) B742955
theorem B1248979 : Blo 491791 1248979 := bstep (se 1 (by rfl) ⟨936734, by rfl⟩ : syracuseStep 1248979 = 1873469) B1873469
theorem B495323 : Blo 491791 495323 := bstep (se 1 (by rfl) ⟨371492, by rfl⟩ : syracuseStep 495323 = 742985) B742985
theorem B495399 : Blo 491791 495399 := bstep (se 1 (by rfl) ⟨371549, by rfl⟩ : syracuseStep 495399 = 743099) B743099
theorem B495439 : Blo 491791 495439 := bstep (se 1 (by rfl) ⟨371579, by rfl⟩ : syracuseStep 495439 = 743159) B743159
theorem B888671 : Blo 491791 888671 := bstep (se 1 (by rfl) ⟨666503, by rfl⟩ : syracuseStep 888671 = 1333007) B1333007
theorem B495455 : Blo 491791 495455 := bstep (se 1 (by rfl) ⟨371591, by rfl⟩ : syracuseStep 495455 = 743183) B743183
theorem B495483 : Blo 491791 495483 := bstep (se 1 (by rfl) ⟨371612, by rfl⟩ : syracuseStep 495483 = 743225) B743225
theorem B1183663 : Blo 491791 1183663 := bstep (se 1 (by rfl) ⟨887747, by rfl⟩ : syracuseStep 1183663 = 1775495) B1775495
theorem B790447 : Blo 491791 790447 := bstep (se 1 (by rfl) ⟨592835, by rfl⟩ : syracuseStep 790447 = 1185671) B1185671
theorem B495535 : Blo 491791 495535 := bstep (se 1 (by rfl) ⟨371651, by rfl⟩ : syracuseStep 495535 = 743303) B743303
theorem B1347511 : Blo 491791 1347511 := bstep (se 1 (by rfl) ⟨1010633, by rfl⟩ : syracuseStep 1347511 = 2021267) B2021267
theorem B495559 : Blo 491791 495559 := bstep (se 1 (by rfl) ⟨371669, by rfl⟩ : syracuseStep 495559 = 743339) B743339
theorem B495579 : Blo 491791 495579 := bstep (se 1 (by rfl) ⟨371684, by rfl⟩ : syracuseStep 495579 = 743369) B743369
theorem B495655 : Blo 491791 495655 := bstep (se 1 (by rfl) ⟨371741, by rfl⟩ : syracuseStep 495655 = 743483) B743483
theorem B495695 : Blo 491791 495695 := bstep (se 1 (by rfl) ⟨371771, by rfl⟩ : syracuseStep 495695 = 743543) B743543
theorem B495711 : Blo 491791 495711 := bstep (se 1 (by rfl) ⟨371783, by rfl⟩ : syracuseStep 495711 = 743567) B743567
theorem B495739 : Blo 491791 495739 := bstep (se 1 (by rfl) ⟨371804, by rfl⟩ : syracuseStep 495739 = 743609) B743609
theorem B495791 : Blo 491791 495791 := bstep (se 1 (by rfl) ⟨371843, by rfl⟩ : syracuseStep 495791 = 743687) B743687
theorem B1249931 : Blo 491791 1249931 := bstep (se 1 (by rfl) ⟨937448, by rfl⟩ : syracuseStep 1249931 = 1874897) B1874897
theorem B2364113 : Blo 491791 2364113 := bstep (se 2 (by rfl) ⟨886542, by rfl⟩ : syracuseStep 2364113 = 1773085) B1773085
theorem B2003741 : Blo 491791 2003741 := bstep (se 3 (by rfl) ⟨375701, by rfl⟩ : syracuseStep 2003741 = 751403) B751403
theorem B3085285 : Blo 491791 3085285 := bstep (se 4 (by rfl) ⟨289245, by rfl⟩ : syracuseStep 3085285 = 578491) B578491
theorem B1872953 : Blo 491791 1872953 := bstep (se 2 (by rfl) ⟨702357, by rfl⟩ : syracuseStep 1872953 = 1404715) B1404715
theorem B890579 : Blo 491791 890579 := bstep (se 1 (by rfl) ⟨667934, by rfl⟩ : syracuseStep 890579 = 1335869) B1335869
theorem B1251065 : Blo 491791 1251065 := bstep (se 2 (by rfl) ⟨469149, by rfl⟩ : syracuseStep 1251065 = 938299) B938299
theorem B890767 : Blo 491791 890767 := bstep (se 1 (by rfl) ⟨668075, by rfl⟩ : syracuseStep 890767 = 1336151) B1336151
theorem B1251247 : Blo 491791 1251247 := bstep (se 1 (by rfl) ⟨938435, by rfl⟩ : syracuseStep 1251247 = 1876871) B1876871
theorem B2889665 : Blo 491791 2889665 := bstep (se 2 (by rfl) ⟨1083624, by rfl⟩ : syracuseStep 2889665 = 2167249) B2167249
theorem B1906841 : Blo 491791 1906841 := bstep (se 2 (by rfl) ⟨715065, by rfl⟩ : syracuseStep 1906841 = 1430131) B1430131
theorem B1251713 : Blo 491791 1251713 := bstep (se 2 (by rfl) ⟨469392, by rfl⟩ : syracuseStep 1251713 = 938785) B938785
theorem B1874441 : Blo 491791 1874441 := bstep (se 2 (by rfl) ⟨702915, by rfl⟩ : syracuseStep 1874441 = 1405831) B1405831
theorem B1252169 : Blo 491791 1252169 := bstep (se 2 (by rfl) ⟨469563, by rfl⟩ : syracuseStep 1252169 = 939127) B939127
theorem B4758365 : Blo 491791 4758365 := bstep (se 3 (by rfl) ⟨892193, by rfl⟩ : syracuseStep 4758365 = 1784387) B1784387
theorem B1579895 : Blo 491791 1579895 := bstep (se 1 (by rfl) ⟨1184921, by rfl⟩ : syracuseStep 1579895 = 2369843) B2369843
theorem B2005879 : Blo 491791 2005879 := bstep (se 1 (by rfl) ⟨1504409, by rfl⟩ : syracuseStep 2005879 = 3008819) B3008819
theorem B859067 : Blo 491791 859067 := bstep (se 1 (by rfl) ⟨644300, by rfl⟩ : syracuseStep 859067 = 1288601) B1288601
theorem B564187 : Blo 491791 564187 := bstep (se 1 (by rfl) ⟨423140, by rfl⟩ : syracuseStep 564187 = 846281) B846281
theorem B3742685 : Blo 491791 3742685 := bstep (se 3 (by rfl) ⟨701753, by rfl⟩ : syracuseStep 3742685 = 1403507) B1403507
theorem B2104339 : Blo 491791 2104339 := bstep (se 1 (by rfl) ⟨1578254, by rfl⟩ : syracuseStep 2104339 = 3156509) B3156509
theorem B2432051 : Blo 491791 2432051 := bstep (se 1 (by rfl) ⟨1824038, by rfl⟩ : syracuseStep 2432051 = 3648077) B3648077
theorem B1252523 : Blo 491791 1252523 := bstep (se 1 (by rfl) ⟨939392, by rfl⟩ : syracuseStep 1252523 = 1878785) B1878785
theorem B5054075 : Blo 491791 5054075 := bstep (se 1 (by rfl) ⟨3790556, by rfl⟩ : syracuseStep 5054075 = 7581113) B7581113
theorem B4202117 : Blo 491791 4202117 := bstep (se 4 (by rfl) ⟨393948, by rfl⟩ : syracuseStep 4202117 = 787897) B787897
theorem B1875595 : Blo 491791 1875595 := bstep (se 1 (by rfl) ⟨1406696, by rfl⟩ : syracuseStep 1875595 = 2813393) B2813393
theorem B15966071 : Blo 491791 15966071 := bstep (se 1 (by rfl) ⟨11974553, by rfl⟩ : syracuseStep 15966071 = 23949107) B23949107
theorem B1777583 : Blo 491791 1777583 := bstep (se 1 (by rfl) ⟨1333187, by rfl⟩ : syracuseStep 1777583 = 2666375) B2666375
theorem B1253303 : Blo 491791 1253303 := bstep (se 1 (by rfl) ⟨939977, by rfl⟩ : syracuseStep 1253303 = 1879955) B1879955
theorem B5054393 : Blo 491791 5054393 := bstep (se 2 (by rfl) ⟨1895397, by rfl⟩ : syracuseStep 5054393 = 3790795) B3790795
theorem B1875899 : Blo 491791 1875899 := bstep (se 1 (by rfl) ⟨1406924, by rfl⟩ : syracuseStep 1875899 = 2813849) B2813849
theorem B46768141 : Blo 491791 46768141 := bstep (se 3 (by rfl) ⟨8769026, by rfl⟩ : syracuseStep 46768141 = 17538053) B17538053
theorem B1351927 : Blo 491791 1351927 := bstep (se 1 (by rfl) ⟨1013945, by rfl⟩ : syracuseStep 1351927 = 2027891) B2027891
theorem B3809825 : Blo 491791 3809825 := bstep (se 2 (by rfl) ⟨1428684, by rfl⟩ : syracuseStep 3809825 = 2857369) B2857369
theorem B1254305 : Blo 491791 1254305 := bstep (se 2 (by rfl) ⟨470364, by rfl⟩ : syracuseStep 1254305 = 940729) B940729
theorem B2106287 : Blo 491791 2106287 := bstep (se 1 (by rfl) ⟨1579715, by rfl⟩ : syracuseStep 2106287 = 3159431) B3159431
theorem B1254761 : Blo 491791 1254761 := bstep (se 2 (by rfl) ⟨470535, by rfl⟩ : syracuseStep 1254761 = 941071) B941071
theorem B2106749 : Blo 491791 2106749 := bstep (se 3 (by rfl) ⟨395015, by rfl⟩ : syracuseStep 2106749 = 790031) B790031
theorem B2499983 : Blo 491791 2499983 := bstep (se 1 (by rfl) ⟨1874987, by rfl⟩ : syracuseStep 2499983 = 3749975) B3749975
theorem B9479825 : Blo 491791 9479825 := bstep (se 2 (by rfl) ⟨3554934, by rfl⟩ : syracuseStep 9479825 = 7109869) B7109869
theorem B6335009 : Blo 491791 6335009 := bstep (se 2 (by rfl) ⟨2375628, by rfl⟩ : syracuseStep 6335009 = 4751257) B4751257
theorem B830351 : Blo 491791 830351 := bstep (se 1 (by rfl) ⟨622763, by rfl⟩ : syracuseStep 830351 = 1245527) B1245527
theorem B9612215 : Blo 491791 9612215 := bstep (se 1 (by rfl) ⟨7209161, by rfl⟩ : syracuseStep 9612215 = 14418323) B14418323
theorem B830587 : Blo 491791 830587 := bstep (se 1 (by rfl) ⟨622940, by rfl⟩ : syracuseStep 830587 = 1245881) B1245881
theorem B2108663 : Blo 491791 2108663 := bstep (se 1 (by rfl) ⟨1581497, by rfl⟩ : syracuseStep 2108663 = 3162995) B3162995
theorem B2502089 : Blo 491791 2502089 := bstep (se 2 (by rfl) ⟨938283, by rfl⟩ : syracuseStep 2502089 = 1876567) B1876567
theorem B2993885 : Blo 491791 2993885 := bstep (se 3 (by rfl) ⟨561353, by rfl⟩ : syracuseStep 2993885 = 1122707) B1122707
theorem B2994029 : Blo 491791 2994029 := bstep (se 3 (by rfl) ⟨561380, by rfl⟩ : syracuseStep 2994029 = 1122761) B1122761
theorem B1879969 : Blo 491791 1879969 := bstep (se 2 (by rfl) ⟨704988, by rfl⟩ : syracuseStep 1879969 = 1409977) B1409977
theorem B831451 : Blo 491791 831451 := bstep (se 1 (by rfl) ⟨623588, by rfl⟩ : syracuseStep 831451 = 1247177) B1247177
theorem B2502737 : Blo 491791 2502737 := bstep (se 2 (by rfl) ⟨938526, by rfl⟩ : syracuseStep 2502737 = 1877053) B1877053
theorem B1683703 : Blo 491791 1683703 := bstep (se 1 (by rfl) ⟨1262777, by rfl⟩ : syracuseStep 1683703 = 2525555) B2525555
theorem B8040779 : Blo 491791 8040779 := bstep (se 1 (by rfl) ⟨6030584, by rfl⟩ : syracuseStep 8040779 = 12061169) B12061169
theorem B832079 : Blo 491791 832079 := bstep (se 1 (by rfl) ⟨624059, by rfl⟩ : syracuseStep 832079 = 1248119) B1248119
theorem B1880927 : Blo 491791 1880927 := bstep (se 1 (by rfl) ⟨1410695, by rfl⟩ : syracuseStep 1880927 = 2821391) B2821391
theorem B1880941 : Blo 491791 1880941 := bstep (se 3 (by rfl) ⟨352676, by rfl⟩ : syracuseStep 1880941 = 705353) B705353
theorem B668795 : Blo 491791 668795 := bstep (se 1 (by rfl) ⟨501596, by rfl⟩ : syracuseStep 668795 = 1003193) B1003193
theorem B1881245 : Blo 491791 1881245 := bstep (se 3 (by rfl) ⟨352733, by rfl⟩ : syracuseStep 1881245 = 705467) B705467
theorem B832943 : Blo 491791 832943 := bstep (se 1 (by rfl) ⟨624707, by rfl⟩ : syracuseStep 832943 = 1249415) B1249415
theorem B8238635 : Blo 491791 8238635 := bstep (se 1 (by rfl) ⟨6178976, by rfl⟩ : syracuseStep 8238635 = 12357953) B12357953
theorem B2111123 : Blo 491791 2111123 := bstep (se 1 (by rfl) ⟨1583342, by rfl⟩ : syracuseStep 2111123 = 3166685) B3166685
theorem B2111275 : Blo 491791 2111275 := bstep (se 1 (by rfl) ⟨1583456, by rfl⟩ : syracuseStep 2111275 = 3166913) B3166913
theorem B1881899 : Blo 491791 1881899 := bstep (se 1 (by rfl) ⟨1411424, by rfl⟩ : syracuseStep 1881899 = 2822849) B2822849
theorem B3553091 : Blo 491791 3553091 := bstep (se 1 (by rfl) ⟨2664818, by rfl⟩ : syracuseStep 3553091 = 5329637) B5329637
theorem B833375 : Blo 491791 833375 := bstep (se 1 (by rfl) ⟨625031, by rfl⟩ : syracuseStep 833375 = 1250063) B1250063
theorem B1783727 : Blo 491791 1783727 := bstep (se 1 (by rfl) ⟨1337795, by rfl⟩ : syracuseStep 1783727 = 2675591) B2675591
theorem B1128455 : Blo 491791 1128455 := bstep (se 1 (by rfl) ⟨846341, by rfl⟩ : syracuseStep 1128455 = 1692683) B1692683
theorem B833935 : Blo 491791 833935 := bstep (se 1 (by rfl) ⟨625451, by rfl⟩ : syracuseStep 833935 = 1250903) B1250903
theorem B5355929 : Blo 491791 5355929 := bstep (se 2 (by rfl) ⟨2008473, by rfl⟩ : syracuseStep 5355929 = 4016947) B4016947
theorem B703451 : Blo 491791 703451 := bstep (se 1 (by rfl) ⟨527588, by rfl⟩ : syracuseStep 703451 = 1055177) B1055177
theorem B834617 : Blo 491791 834617 := bstep (se 2 (by rfl) ⟨312981, by rfl⟩ : syracuseStep 834617 = 625963) B625963
theorem B998497 : Blo 491791 998497 := bstep (se 2 (by rfl) ⟨374436, by rfl⟩ : syracuseStep 998497 = 748873) B748873
theorem B2276599 : Blo 491791 2276599 := bstep (se 1 (by rfl) ⟨1707449, by rfl⟩ : syracuseStep 2276599 = 3414899) B3414899
theorem B9649625 : Blo 491791 9649625 := bstep (se 2 (by rfl) ⟨3618609, by rfl⟩ : syracuseStep 9649625 = 7237219) B7237219
theorem B704009 : Blo 491791 704009 := bstep (se 2 (by rfl) ⟨264003, by rfl⟩ : syracuseStep 704009 = 528007) B528007
theorem B2113121 : Blo 491791 2113121 := bstep (se 2 (by rfl) ⟨792420, by rfl⟩ : syracuseStep 2113121 = 1584841) B1584841
theorem B835319 : Blo 491791 835319 := bstep (se 1 (by rfl) ⟨626489, by rfl⟩ : syracuseStep 835319 = 1252979) B1252979
theorem B10141625 : Blo 491791 10141625 := bstep (se 2 (by rfl) ⟨3803109, by rfl⟩ : syracuseStep 10141625 = 7606219) B7606219
theorem B835663 : Blo 491791 835663 := bstep (se 1 (by rfl) ⟨626747, by rfl⟩ : syracuseStep 835663 = 1253495) B1253495
theorem B835913 : Blo 491791 835913 := bstep (se 2 (by rfl) ⟨313467, by rfl⟩ : syracuseStep 835913 = 626935) B626935
theorem B704875 : Blo 491791 704875 := bstep (se 1 (by rfl) ⟨528656, by rfl⟩ : syracuseStep 704875 = 1057313) B1057313
theorem B737711 : Blo 491791 737711 := bstep (se 1 (by rfl) ⟨553283, by rfl⟩ : syracuseStep 737711 = 1106567) B1106567
theorem B1425883 : Blo 491791 1425883 := bstep (se 1 (by rfl) ⟨1069412, by rfl⟩ : syracuseStep 1425883 = 2138825) B2138825
theorem B1786349 : Blo 491791 1786349 := bstep (se 3 (by rfl) ⟨334940, by rfl⟩ : syracuseStep 1786349 = 669881) B669881
theorem B737801 : Blo 491791 737801 := bstep (se 2 (by rfl) ⟨276675, by rfl⟩ : syracuseStep 737801 = 553351) B553351
theorem B2802185 : Blo 491791 2802185 := bstep (se 2 (by rfl) ⟨1050819, by rfl⟩ : syracuseStep 2802185 = 2101639) B2101639
theorem B2507273 : Blo 491791 2507273 := bstep (se 2 (by rfl) ⟨940227, by rfl⟩ : syracuseStep 2507273 = 1880455) B1880455
theorem B737831 : Blo 491791 737831 := bstep (se 1 (by rfl) ⟨553373, by rfl⟩ : syracuseStep 737831 = 1106747) B1106747
theorem B737915 : Blo 491791 737915 := bstep (se 1 (by rfl) ⟨553436, by rfl⟩ : syracuseStep 737915 = 1106873) B1106873
theorem B934571 : Blo 491791 934571 := bstep (se 1 (by rfl) ⟨700928, by rfl⟩ : syracuseStep 934571 = 1401857) B1401857
theorem B738041 : Blo 491791 738041 := bstep (se 2 (by rfl) ⟨276765, by rfl⟩ : syracuseStep 738041 = 553531) B553531
theorem B836345 : Blo 491791 836345 := bstep (se 2 (by rfl) ⟨313629, by rfl⟩ : syracuseStep 836345 = 627259) B627259
theorem B738143 : Blo 491791 738143 := bstep (se 1 (by rfl) ⟨553607, by rfl⟩ : syracuseStep 738143 = 1107215) B1107215
theorem B738155 : Blo 491791 738155 := bstep (se 1 (by rfl) ⟨553616, by rfl⟩ : syracuseStep 738155 = 1107233) B1107233
theorem B836527 : Blo 491791 836527 := bstep (se 1 (by rfl) ⟨627395, by rfl⟩ : syracuseStep 836527 = 1254791) B1254791
theorem B836615 : Blo 491791 836615 := bstep (se 1 (by rfl) ⟨627461, by rfl⟩ : syracuseStep 836615 = 1254923) B1254923
theorem B738383 : Blo 491791 738383 := bstep (se 1 (by rfl) ⟨553787, by rfl⟩ : syracuseStep 738383 = 1107575) B1107575
theorem B738503 : Blo 491791 738503 := bstep (se 1 (by rfl) ⟨553877, by rfl⟩ : syracuseStep 738503 = 1107755) B1107755
theorem B3163481 : Blo 491791 3163481 := bstep (se 2 (by rfl) ⟨1186305, by rfl⟩ : syracuseStep 3163481 = 2372611) B2372611
theorem B738665 : Blo 491791 738665 := bstep (se 2 (by rfl) ⟨276999, by rfl⟩ : syracuseStep 738665 = 553999) B553999
theorem B4343203 : Blo 491791 4343203 := bstep (se 1 (by rfl) ⟨3257402, by rfl⟩ : syracuseStep 4343203 = 6514805) B6514805
theorem B3556781 : Blo 491791 3556781 := bstep (se 3 (by rfl) ⟨666896, by rfl⟩ : syracuseStep 3556781 = 1333793) B1333793
theorem B738743 : Blo 491791 738743 := bstep (se 1 (by rfl) ⟨554057, by rfl⟩ : syracuseStep 738743 = 1108115) B1108115
theorem B738779 : Blo 491791 738779 := bstep (se 1 (by rfl) ⟨554084, by rfl⟩ : syracuseStep 738779 = 1108169) B1108169
theorem B2115035 : Blo 491791 2115035 := bstep (se 1 (by rfl) ⟨1586276, by rfl⟩ : syracuseStep 2115035 = 3172553) B3172553
theorem B2803187 : Blo 491791 2803187 := bstep (se 1 (by rfl) ⟨2102390, by rfl⟩ : syracuseStep 2803187 = 4204781) B4204781
theorem B3753863 : Blo 491791 3753863 := bstep (se 1 (by rfl) ⟨2815397, by rfl⟩ : syracuseStep 3753863 = 5630795) B5630795
theorem B739247 : Blo 491791 739247 := bstep (se 1 (by rfl) ⟨554435, by rfl⟩ : syracuseStep 739247 = 1108871) B1108871
theorem B2803643 : Blo 491791 2803643 := bstep (se 1 (by rfl) ⟨2102732, by rfl⟩ : syracuseStep 2803643 = 4205465) B4205465
theorem B2508731 : Blo 491791 2508731 := bstep (se 1 (by rfl) ⟨1881548, by rfl⟩ : syracuseStep 2508731 = 3763097) B3763097
theorem B739337 : Blo 491791 739337 := bstep (se 2 (by rfl) ⟨277251, by rfl⟩ : syracuseStep 739337 = 554503) B554503
theorem B935945 : Blo 491791 935945 := bstep (se 2 (by rfl) ⟨350979, by rfl⟩ : syracuseStep 935945 = 701959) B701959
theorem B739367 : Blo 491791 739367 := bstep (se 1 (by rfl) ⟨554525, by rfl⟩ : syracuseStep 739367 = 1109051) B1109051
theorem B935975 : Blo 491791 935975 := bstep (se 1 (by rfl) ⟨701981, by rfl⟩ : syracuseStep 935975 = 1403963) B1403963
theorem B739451 : Blo 491791 739451 := bstep (se 1 (by rfl) ⟨554588, by rfl⟩ : syracuseStep 739451 = 1109177) B1109177
theorem B968915 : Blo 491791 968915 := bstep (se 1 (by rfl) ⟨726686, by rfl⟩ : syracuseStep 968915 = 1453373) B1453373
theorem B739577 : Blo 491791 739577 := bstep (se 2 (by rfl) ⟨277341, by rfl⟩ : syracuseStep 739577 = 554683) B554683
theorem B3557681 : Blo 491791 3557681 := bstep (se 2 (by rfl) ⟨1334130, by rfl⟩ : syracuseStep 3557681 = 2668261) B2668261
theorem B739679 : Blo 491791 739679 := bstep (se 1 (by rfl) ⟨554759, by rfl⟩ : syracuseStep 739679 = 1109519) B1109519
theorem B2378089 : Blo 491791 2378089 := bstep (se 2 (by rfl) ⟨891783, by rfl⟩ : syracuseStep 2378089 = 1783567) B1783567
theorem B739691 : Blo 491791 739691 := bstep (se 1 (by rfl) ⟨554768, by rfl⟩ : syracuseStep 739691 = 1109537) B1109537
theorem B739919 : Blo 491791 739919 := bstep (se 1 (by rfl) ⟨554939, by rfl⟩ : syracuseStep 739919 = 1109879) B1109879
theorem B740039 : Blo 491791 740039 := bstep (se 1 (by rfl) ⟨555029, by rfl⟩ : syracuseStep 740039 = 1110059) B1110059
theorem B936659 : Blo 491791 936659 := bstep (se 1 (by rfl) ⟨702494, by rfl⟩ : syracuseStep 936659 = 1404989) B1404989
theorem B936697 : Blo 491791 936697 := bstep (se 2 (by rfl) ⟨351261, by rfl⟩ : syracuseStep 936697 = 702523) B702523
theorem B740201 : Blo 491791 740201 := bstep (se 2 (by rfl) ⟨277575, by rfl⟩ : syracuseStep 740201 = 555151) B555151
theorem B740279 : Blo 491791 740279 := bstep (se 1 (by rfl) ⟨555209, by rfl⟩ : syracuseStep 740279 = 1110419) B1110419
theorem B740315 : Blo 491791 740315 := bstep (se 1 (by rfl) ⟨555236, by rfl⟩ : syracuseStep 740315 = 1110473) B1110473
theorem B6016079 : Blo 491791 6016079 := bstep (se 1 (by rfl) ⟨4512059, by rfl⟩ : syracuseStep 6016079 = 9024119) B9024119
theorem B7588981 : Blo 491791 7588981 := bstep (se 5 (by rfl) ⟨355733, by rfl⟩ : syracuseStep 7588981 = 711467) B711467
theorem B740783 : Blo 491791 740783 := bstep (se 1 (by rfl) ⟨555587, by rfl⟩ : syracuseStep 740783 = 1111175) B1111175
theorem B937403 : Blo 491791 937403 := bstep (se 1 (by rfl) ⟨703052, by rfl⟩ : syracuseStep 937403 = 1406105) B1406105
theorem B740873 : Blo 491791 740873 := bstep (se 2 (by rfl) ⟨277827, by rfl⟩ : syracuseStep 740873 = 555655) B555655
theorem B740903 : Blo 491791 740903 := bstep (se 1 (by rfl) ⟨555677, by rfl⟩ : syracuseStep 740903 = 1111355) B1111355
theorem B740987 : Blo 491791 740987 := bstep (se 1 (by rfl) ⟨555740, by rfl⟩ : syracuseStep 740987 = 1111481) B1111481
theorem B1068743 : Blo 491791 1068743 := bstep (se 1 (by rfl) ⟨801557, by rfl⟩ : syracuseStep 1068743 = 1603115) B1603115
theorem B741113 : Blo 491791 741113 := bstep (se 2 (by rfl) ⟨277917, by rfl⟩ : syracuseStep 741113 = 555835) B555835
theorem B741215 : Blo 491791 741215 := bstep (se 1 (by rfl) ⟨555911, by rfl⟩ : syracuseStep 741215 = 1111823) B1111823
theorem B741227 : Blo 491791 741227 := bstep (se 1 (by rfl) ⟨555920, by rfl⟩ : syracuseStep 741227 = 1111841) B1111841
theorem B2117495 : Blo 491791 2117495 := bstep (se 1 (by rfl) ⟨1588121, by rfl⟩ : syracuseStep 2117495 = 3176243) B3176243
theorem B937889 : Blo 491791 937889 := bstep (se 2 (by rfl) ⟨351708, by rfl⟩ : syracuseStep 937889 = 703417) B703417
theorem B741455 : Blo 491791 741455 := bstep (se 1 (by rfl) ⟨556091, by rfl⟩ : syracuseStep 741455 = 1112183) B1112183
theorem B938155 : Blo 491791 938155 := bstep (se 1 (by rfl) ⟨703616, by rfl⟩ : syracuseStep 938155 = 1407233) B1407233
theorem B21418181 : Blo 491791 21418181 := bstep (se 4 (by rfl) ⟨2007954, by rfl⟩ : syracuseStep 21418181 = 4015909) B4015909
theorem B741575 : Blo 491791 741575 := bstep (se 1 (by rfl) ⟨556181, by rfl⟩ : syracuseStep 741575 = 1112363) B1112363
theorem B2806103 : Blo 491791 2806103 := bstep (se 1 (by rfl) ⟨2104577, by rfl⟩ : syracuseStep 2806103 = 4209155) B4209155
theorem B741737 : Blo 491791 741737 := bstep (se 2 (by rfl) ⟨278151, by rfl⟩ : syracuseStep 741737 = 556303) B556303
theorem B741815 : Blo 491791 741815 := bstep (se 1 (by rfl) ⟨556361, by rfl⟩ : syracuseStep 741815 = 1112723) B1112723
theorem B938459 : Blo 491791 938459 := bstep (se 1 (by rfl) ⟨703844, by rfl⟩ : syracuseStep 938459 = 1407689) B1407689
theorem B741851 : Blo 491791 741851 := bstep (se 1 (by rfl) ⟨556388, by rfl⟩ : syracuseStep 741851 = 1112777) B1112777
theorem B7131671 : Blo 491791 7131671 := bstep (se 1 (by rfl) ⟨5348753, by rfl⟩ : syracuseStep 7131671 = 10697507) B10697507
theorem B3560071 : Blo 491791 3560071 := bstep (se 1 (by rfl) ⟨2670053, by rfl⟩ : syracuseStep 3560071 = 5340107) B5340107
theorem B1200779 : Blo 491791 1200779 := bstep (se 1 (by rfl) ⟨900584, by rfl⟩ : syracuseStep 1200779 = 1801169) B1801169
theorem B742319 : Blo 491791 742319 := bstep (se 1 (by rfl) ⟨556739, by rfl⟩ : syracuseStep 742319 = 1113479) B1113479
theorem B1659905 : Blo 491791 1659905 := bstep (se 2 (by rfl) ⟨622464, by rfl⟩ : syracuseStep 1659905 = 1244929) B1244929
theorem B742409 : Blo 491791 742409 := bstep (se 2 (by rfl) ⟨278403, by rfl⟩ : syracuseStep 742409 = 556807) B556807
theorem B742439 : Blo 491791 742439 := bstep (se 1 (by rfl) ⟨556829, by rfl⟩ : syracuseStep 742439 = 1113659) B1113659
theorem B742523 : Blo 491791 742523 := bstep (se 1 (by rfl) ⟨556892, by rfl⟩ : syracuseStep 742523 = 1113785) B1113785
theorem B2249975 : Blo 491791 2249975 := bstep (se 1 (by rfl) ⟨1687481, by rfl⟩ : syracuseStep 2249975 = 3374963) B3374963
theorem B742649 : Blo 491791 742649 := bstep (se 2 (by rfl) ⟨278493, by rfl⟩ : syracuseStep 742649 = 556987) B556987
theorem B742751 : Blo 491791 742751 := bstep (se 1 (by rfl) ⟨557063, by rfl⟩ : syracuseStep 742751 = 1114127) B1114127
theorem B742763 : Blo 491791 742763 := bstep (se 1 (by rfl) ⟨557072, by rfl⟩ : syracuseStep 742763 = 1114145) B1114145
theorem B939529 : Blo 491791 939529 := bstep (se 2 (by rfl) ⟨352323, by rfl⟩ : syracuseStep 939529 = 704647) B704647
theorem B742991 : Blo 491791 742991 := bstep (se 1 (by rfl) ⟨557243, by rfl⟩ : syracuseStep 742991 = 1114487) B1114487
theorem B743111 : Blo 491791 743111 := bstep (se 1 (by rfl) ⟨557333, by rfl⟩ : syracuseStep 743111 = 1114667) B1114667
theorem B1660715 : Blo 491791 1660715 := bstep (se 1 (by rfl) ⟨1245536, by rfl⟩ : syracuseStep 1660715 = 2491073) B2491073
theorem B743273 : Blo 491791 743273 := bstep (se 2 (by rfl) ⟨278727, by rfl⟩ : syracuseStep 743273 = 557455) B557455
theorem B743351 : Blo 491791 743351 := bstep (se 1 (by rfl) ⟨557513, by rfl⟩ : syracuseStep 743351 = 1115027) B1115027
theorem B743387 : Blo 491791 743387 := bstep (se 1 (by rfl) ⟨557540, by rfl⟩ : syracuseStep 743387 = 1115081) B1115081
theorem B1660985 : Blo 491791 1660985 := bstep (se 2 (by rfl) ⟨622869, by rfl⟩ : syracuseStep 1660985 = 1245739) B1245739
theorem B3758237 : Blo 491791 3758237 := bstep (se 3 (by rfl) ⟨704669, by rfl⟩ : syracuseStep 3758237 = 1409339) B1409339
theorem B940243 : Blo 491791 940243 := bstep (se 1 (by rfl) ⟨705182, by rfl⟩ : syracuseStep 940243 = 1410365) B1410365
theorem B3004733 : Blo 491791 3004733 := bstep (se 3 (by rfl) ⟨563387, by rfl⟩ : syracuseStep 3004733 = 1126775) B1126775
theorem B1661309 : Blo 491791 1661309 := bstep (se 3 (by rfl) ⟨311495, by rfl⟩ : syracuseStep 1661309 = 622991) B622991
theorem B842249 : Blo 491791 842249 := bstep (se 2 (by rfl) ⟨315843, by rfl⟩ : syracuseStep 842249 = 631687) B631687
theorem B1661579 : Blo 491791 1661579 := bstep (se 1 (by rfl) ⟨1246184, by rfl⟩ : syracuseStep 1661579 = 2492369) B2492369
theorem B7101107 : Blo 491791 7101107 := bstep (se 1 (by rfl) ⟨5325830, by rfl⟩ : syracuseStep 7101107 = 10651661) B10651661
theorem B4217629 : Blo 491791 4217629 := bstep (se 3 (by rfl) ⟨790805, by rfl⟩ : syracuseStep 4217629 = 1581611) B1581611
theorem B3169169 : Blo 491791 3169169 := bstep (se 2 (by rfl) ⟨1188438, by rfl⟩ : syracuseStep 3169169 = 2376877) B2376877
theorem B711607 : Blo 491791 711607 := bstep (se 1 (by rfl) ⟨533705, by rfl⟩ : syracuseStep 711607 = 1067411) B1067411
theorem B940987 : Blo 491791 940987 := bstep (se 1 (by rfl) ⟨705740, by rfl⟩ : syracuseStep 940987 = 1411481) B1411481
theorem B1662497 : Blo 491791 1662497 := bstep (se 2 (by rfl) ⟨623436, by rfl⟩ : syracuseStep 1662497 = 1246873) B1246873
theorem B1662713 : Blo 491791 1662713 := bstep (se 2 (by rfl) ⟨623517, by rfl⟩ : syracuseStep 1662713 = 1247035) B1247035
theorem B1335113 : Blo 491791 1335113 := bstep (se 2 (by rfl) ⟨500667, by rfl⟩ : syracuseStep 1335113 = 1001335) B1001335
theorem B1662983 : Blo 491791 1662983 := bstep (se 1 (by rfl) ⟨1247237, by rfl⟩ : syracuseStep 1662983 = 2494475) B2494475
theorem B4317299 : Blo 491791 4317299 := bstep (se 1 (by rfl) ⟨3237974, by rfl⟩ : syracuseStep 4317299 = 6475949) B6475949
theorem B1663091 : Blo 491791 1663091 := bstep (se 1 (by rfl) ⟨1247318, by rfl⟩ : syracuseStep 1663091 = 2494637) B2494637
theorem B3367169 : Blo 491791 3367169 := bstep (se 2 (by rfl) ⟨1262688, by rfl⟩ : syracuseStep 3367169 = 2525377) B2525377
theorem B1663361 : Blo 491791 1663361 := bstep (se 2 (by rfl) ⟨623760, by rfl⟩ : syracuseStep 1663361 = 1247521) B1247521
theorem B1172183 : Blo 491791 1172183 := bstep (se 1 (by rfl) ⟨879137, by rfl⟩ : syracuseStep 1172183 = 1758275) B1758275
theorem B1106783 : Blo 491791 1106783 := bstep (se 1 (by rfl) ⟨830087, by rfl⟩ : syracuseStep 1106783 = 1660175) B1660175
theorem B3761153 : Blo 491791 3761153 := bstep (se 2 (by rfl) ⟨1410432, by rfl⟩ : syracuseStep 3761153 = 2820865) B2820865
theorem B1106963 : Blo 491791 1106963 := bstep (se 1 (by rfl) ⟨830222, by rfl⟩ : syracuseStep 1106963 = 1660445) B1660445
theorem B3564623 : Blo 491791 3564623 := bstep (se 1 (by rfl) ⟨2673467, by rfl⟩ : syracuseStep 3564623 = 5346935) B5346935
theorem B1664171 : Blo 491791 1664171 := bstep (se 1 (by rfl) ⟨1248128, by rfl⟩ : syracuseStep 1664171 = 2496257) B2496257
theorem B1107305 : Blo 491791 1107305 := bstep (se 2 (by rfl) ⟨415239, by rfl⟩ : syracuseStep 1107305 = 830479) B830479
theorem B3007945 : Blo 491791 3007945 := bstep (se 2 (by rfl) ⟨1127979, by rfl⟩ : syracuseStep 3007945 = 2255959) B2255959
theorem B1664711 : Blo 491791 1664711 := bstep (se 1 (by rfl) ⟨1248533, by rfl⟩ : syracuseStep 1664711 = 2497067) B2497067
theorem B1107899 : Blo 491791 1107899 := bstep (se 1 (by rfl) ⟨830924, by rfl⟩ : syracuseStep 1107899 = 1661849) B1661849
theorem B1337363 : Blo 491791 1337363 := bstep (se 1 (by rfl) ⟨1003022, by rfl⟩ : syracuseStep 1337363 = 2006045) B2006045
theorem B1108025 : Blo 491791 1108025 := bstep (se 2 (by rfl) ⟨415509, by rfl⟩ : syracuseStep 1108025 = 831019) B831019
theorem B9529649 : Blo 491791 9529649 := bstep (se 2 (by rfl) ⟨3573618, by rfl⟩ : syracuseStep 9529649 = 7147237) B7147237
theorem B8415575 : Blo 491791 8415575 := bstep (se 1 (by rfl) ⟨6311681, by rfl⟩ : syracuseStep 8415575 = 12623363) B12623363
theorem B1108367 : Blo 491791 1108367 := bstep (se 1 (by rfl) ⟨831275, by rfl⟩ : syracuseStep 1108367 = 1662551) B1662551
theorem B1665575 : Blo 491791 1665575 := bstep (se 1 (by rfl) ⟨1249181, by rfl⟩ : syracuseStep 1665575 = 2498363) B2498363
theorem B1403531 : Blo 491791 1403531 := bstep (se 1 (by rfl) ⟨1052648, by rfl⟩ : syracuseStep 1403531 = 2105297) B2105297
theorem B1665683 : Blo 491791 1665683 := bstep (se 1 (by rfl) ⟨1249262, by rfl⟩ : syracuseStep 1665683 = 2498525) B2498525
theorem B12610241 : Blo 491791 12610241 := bstep (se 2 (by rfl) ⟨4728840, by rfl⟩ : syracuseStep 12610241 = 9457681) B9457681
theorem B1108691 : Blo 491791 1108691 := bstep (se 1 (by rfl) ⟨831518, by rfl⟩ : syracuseStep 1108691 = 1663037) B1663037
theorem B1665899 : Blo 491791 1665899 := bstep (se 1 (by rfl) ⟨1249424, by rfl⟩ : syracuseStep 1665899 = 2498849) B2498849
theorem B1665953 : Blo 491791 1665953 := bstep (se 2 (by rfl) ⟨624732, by rfl⟩ : syracuseStep 1665953 = 1249465) B1249465
theorem B3173579 : Blo 491791 3173579 := bstep (se 1 (by rfl) ⟨2380184, by rfl⟩ : syracuseStep 3173579 = 4760369) B4760369
theorem B1666547 : Blo 491791 1666547 := bstep (se 1 (by rfl) ⟨1249910, by rfl⟩ : syracuseStep 1666547 = 2499821) B2499821
theorem B749135 : Blo 491791 749135 := bstep (se 1 (by rfl) ⟨561851, by rfl⟩ : syracuseStep 749135 = 1123703) B1123703
theorem B1109627 : Blo 491791 1109627 := bstep (se 1 (by rfl) ⟨832220, by rfl⟩ : syracuseStep 1109627 = 1664441) B1664441
theorem B1109753 : Blo 491791 1109753 := bstep (se 2 (by rfl) ⟨416157, by rfl⟩ : syracuseStep 1109753 = 832315) B832315
theorem B8548129 : Blo 491791 8548129 := bstep (se 2 (by rfl) ⟨3205548, by rfl⟩ : syracuseStep 8548129 = 6411097) B6411097
theorem B1110023 : Blo 491791 1110023 := bstep (se 1 (by rfl) ⟨832517, by rfl⟩ : syracuseStep 1110023 = 1665035) B1665035
theorem B1667087 : Blo 491791 1667087 := bstep (se 1 (by rfl) ⟨1250315, by rfl⟩ : syracuseStep 1667087 = 2500631) B2500631
theorem B1110095 : Blo 491791 1110095 := bstep (se 1 (by rfl) ⟨832571, by rfl⟩ : syracuseStep 1110095 = 1665143) B1665143
theorem B5337251 : Blo 491791 5337251 := bstep (se 1 (by rfl) ⟨4002938, by rfl⟩ : syracuseStep 5337251 = 8005877) B8005877
theorem B3993857 : Blo 491791 3993857 := bstep (se 2 (by rfl) ⟨1497696, by rfl⟩ : syracuseStep 3993857 = 2995393) B2995393
theorem B1503631 : Blo 491791 1503631 := bstep (se 1 (by rfl) ⟨1127723, by rfl⟩ : syracuseStep 1503631 = 2255447) B2255447
theorem B1110491 : Blo 491791 1110491 := bstep (se 1 (by rfl) ⟨832868, by rfl⟩ : syracuseStep 1110491 = 1665737) B1665737
theorem B1667681 : Blo 491791 1667681 := bstep (se 2 (by rfl) ⟨625380, by rfl⟩ : syracuseStep 1667681 = 1250761) B1250761
theorem B3568313 : Blo 491791 3568313 := bstep (se 2 (by rfl) ⟨1338117, by rfl⟩ : syracuseStep 3568313 = 2676235) B2676235
theorem B1110959 : Blo 491791 1110959 := bstep (se 1 (by rfl) ⟨833219, by rfl⟩ : syracuseStep 1110959 = 1666439) B1666439
theorem B554107 : Blo 491791 554107 := bstep (se 1 (by rfl) ⟨415580, by rfl⟩ : syracuseStep 554107 = 831161) B831161
theorem B1111211 : Blo 491791 1111211 := bstep (se 1 (by rfl) ⟨833408, by rfl⟩ : syracuseStep 1111211 = 1666817) B1666817
theorem B6321523 : Blo 491791 6321523 := bstep (se 1 (by rfl) ⟨4741142, by rfl⟩ : syracuseStep 6321523 = 9482285) B9482285
theorem B554575 : Blo 491791 554575 := bstep (se 1 (by rfl) ⟨415931, by rfl⟩ : syracuseStep 554575 = 831863) B831863
theorem B1111751 : Blo 491791 1111751 := bstep (se 1 (by rfl) ⟨833813, by rfl⟩ : syracuseStep 1111751 = 1667627) B1667627
theorem B5994283 : Blo 491791 5994283 := bstep (se 1 (by rfl) ⟨4495712, by rfl⟩ : syracuseStep 5994283 = 8991425) B8991425
theorem B554971 : Blo 491791 554971 := bstep (se 1 (by rfl) ⟨416228, by rfl⟩ : syracuseStep 554971 = 832457) B832457
theorem B1669139 : Blo 491791 1669139 := bstep (se 1 (by rfl) ⟨1251854, by rfl⟩ : syracuseStep 1669139 = 2503709) B2503709
theorem B1669463 : Blo 491791 1669463 := bstep (se 1 (by rfl) ⟨1252097, by rfl⟩ : syracuseStep 1669463 = 2504195) B2504195
theorem B555439 : Blo 491791 555439 := bstep (se 1 (by rfl) ⟨416579, by rfl⟩ : syracuseStep 555439 = 833159) B833159
theorem B1112615 : Blo 491791 1112615 := bstep (se 1 (by rfl) ⟨834461, by rfl⟩ : syracuseStep 1112615 = 1668923) B1668923
theorem B555871 : Blo 491791 555871 := bstep (se 1 (by rfl) ⟨416903, by rfl⟩ : syracuseStep 555871 = 833807) B833807
theorem B1112939 : Blo 491791 1112939 := bstep (se 1 (by rfl) ⟨834704, by rfl⟩ : syracuseStep 1112939 = 1669409) B1669409
theorem B11598709 : Blo 491791 11598709 := bstep (se 5 (by rfl) ⟨543689, by rfl⟩ : syracuseStep 11598709 = 1087379) B1087379
theorem B1407905 : Blo 491791 1407905 := bstep (se 2 (by rfl) ⟨527964, by rfl⟩ : syracuseStep 1407905 = 1055929) B1055929
theorem B1112993 : Blo 491791 1112993 := bstep (se 2 (by rfl) ⟨417372, by rfl⟩ : syracuseStep 1112993 = 834745) B834745
theorem B556231 : Blo 491791 556231 := bstep (se 1 (by rfl) ⟨417173, by rfl⟩ : syracuseStep 556231 = 834347) B834347
theorem B1113335 : Blo 491791 1113335 := bstep (se 1 (by rfl) ⟨835001, by rfl⟩ : syracuseStep 1113335 = 1670003) B1670003
theorem B3734909 : Blo 491791 3734909 := bstep (se 3 (by rfl) ⟨700295, by rfl⟩ : syracuseStep 3734909 = 1400591) B1400591
theorem B1670543 : Blo 491791 1670543 := bstep (se 1 (by rfl) ⟨1252907, by rfl⟩ : syracuseStep 1670543 = 2505815) B2505815
theorem B3014267 : Blo 491791 3014267 := bstep (se 1 (by rfl) ⟨2260700, by rfl⟩ : syracuseStep 3014267 = 4521401) B4521401
theorem B1670867 : Blo 491791 1670867 := bstep (se 1 (by rfl) ⟨1253150, by rfl⟩ : syracuseStep 1670867 = 2506301) B2506301
theorem B1113929 : Blo 491791 1113929 := bstep (se 2 (by rfl) ⟨417723, by rfl⟩ : syracuseStep 1113929 = 835447) B835447
theorem B6422435 : Blo 491791 6422435 := bstep (se 1 (by rfl) ⟨4816826, by rfl⟩ : syracuseStep 6422435 = 9633653) B9633653
theorem B62357521 : Blo 491791 62357521 := bstep (se 2 (by rfl) ⟨23384070, by rfl⟩ : syracuseStep 62357521 = 46768141) B46768141
theorem B1114217 : Blo 491791 1114217 := bstep (se 2 (by rfl) ⟨417831, by rfl⟩ : syracuseStep 1114217 = 835663) B835663
theorem B1245395 : Blo 491791 1245395 := bstep (se 1 (by rfl) ⟨934046, by rfl⟩ : syracuseStep 1245395 = 1868093) B1868093
theorem B557275 : Blo 491791 557275 := bstep (se 1 (by rfl) ⟨417956, by rfl⟩ : syracuseStep 557275 = 835913) B835913
theorem B491807 : Blo 491791 491807 := bstep (se 1 (by rfl) ⟨368855, by rfl⟩ : syracuseStep 491807 = 737711) B737711
theorem B1802569 : Blo 491791 1802569 := bstep (se 2 (by rfl) ⟨675963, by rfl⟩ : syracuseStep 1802569 = 1351927) B1351927
theorem B491867 : Blo 491791 491867 := bstep (se 1 (by rfl) ⟨368900, by rfl⟩ : syracuseStep 491867 = 737801) B737801
theorem B1868123 : Blo 491791 1868123 := bstep (se 1 (by rfl) ⟨1401092, by rfl⟩ : syracuseStep 1868123 = 2802185) B2802185
theorem B1671515 : Blo 491791 1671515 := bstep (se 1 (by rfl) ⟨1253636, by rfl⟩ : syracuseStep 1671515 = 2507273) B2507273
theorem B491887 : Blo 491791 491887 := bstep (se 1 (by rfl) ⟨368915, by rfl⟩ : syracuseStep 491887 = 737831) B737831
theorem B491943 : Blo 491791 491943 := bstep (se 1 (by rfl) ⟨368957, by rfl⟩ : syracuseStep 491943 = 737915) B737915
theorem B623047 : Blo 491791 623047 := bstep (se 1 (by rfl) ⟨467285, by rfl⟩ : syracuseStep 623047 = 934571) B934571
theorem B492027 : Blo 491791 492027 := bstep (se 1 (by rfl) ⟨369020, by rfl⟩ : syracuseStep 492027 = 738041) B738041
theorem B557563 : Blo 491791 557563 := bstep (se 1 (by rfl) ⟨418172, by rfl⟩ : syracuseStep 557563 = 836345) B836345
theorem B492095 : Blo 491791 492095 := bstep (se 1 (by rfl) ⟨369071, by rfl⟩ : syracuseStep 492095 = 738143) B738143
theorem B492103 : Blo 491791 492103 := bstep (se 1 (by rfl) ⟨369077, by rfl⟩ : syracuseStep 492103 = 738155) B738155
theorem B1114703 : Blo 491791 1114703 := bstep (se 1 (by rfl) ⟨836027, by rfl⟩ : syracuseStep 1114703 = 1672055) B1672055
theorem B1901177 : Blo 491791 1901177 := bstep (se 2 (by rfl) ⟨712941, by rfl⟩ : syracuseStep 1901177 = 1425883) B1425883
theorem B557743 : Blo 491791 557743 := bstep (se 1 (by rfl) ⟨418307, by rfl⟩ : syracuseStep 557743 = 836615) B836615
theorem B492255 : Blo 491791 492255 := bstep (se 1 (by rfl) ⟨369191, by rfl⟩ : syracuseStep 492255 = 738383) B738383
theorem B1114847 : Blo 491791 1114847 := bstep (se 1 (by rfl) ⟨836135, by rfl⟩ : syracuseStep 1114847 = 1672271) B1672271
theorem B492335 : Blo 491791 492335 := bstep (se 1 (by rfl) ⟨369251, by rfl⟩ : syracuseStep 492335 = 738503) B738503
theorem B492443 : Blo 491791 492443 := bstep (se 1 (by rfl) ⟨369332, by rfl⟩ : syracuseStep 492443 = 738665) B738665
theorem B492495 : Blo 491791 492495 := bstep (se 1 (by rfl) ⟨369371, by rfl⟩ : syracuseStep 492495 = 738743) B738743
theorem B1115099 : Blo 491791 1115099 := bstep (se 1 (by rfl) ⟨836324, by rfl⟩ : syracuseStep 1115099 = 1672649) B1672649
theorem B492519 : Blo 491791 492519 := bstep (se 1 (by rfl) ⟨369389, by rfl⟩ : syracuseStep 492519 = 738779) B738779
theorem B1410023 : Blo 491791 1410023 := bstep (se 1 (by rfl) ⟨1057517, by rfl⟩ : syracuseStep 1410023 = 2115035) B2115035
theorem B1868791 : Blo 491791 1868791 := bstep (se 1 (by rfl) ⟨1401593, by rfl⟩ : syracuseStep 1868791 = 2803187) B2803187
theorem B1115279 : Blo 491791 1115279 := bstep (se 1 (by rfl) ⟨836459, by rfl⟩ : syracuseStep 1115279 = 1672919) B1672919
theorem B591067 : Blo 491791 591067 := bstep (se 1 (by rfl) ⟨443300, by rfl⟩ : syracuseStep 591067 = 886601) B886601
theorem B1115369 : Blo 491791 1115369 := bstep (se 2 (by rfl) ⟨418263, by rfl⟩ : syracuseStep 1115369 = 836527) B836527
theorem B492831 : Blo 491791 492831 := bstep (se 1 (by rfl) ⟨369623, by rfl⟩ : syracuseStep 492831 = 739247) B739247
theorem B1115423 : Blo 491791 1115423 := bstep (se 1 (by rfl) ⟨836567, by rfl⟩ : syracuseStep 1115423 = 1673135) B1673135
theorem B1869095 : Blo 491791 1869095 := bstep (se 1 (by rfl) ⟨1401821, by rfl⟩ : syracuseStep 1869095 = 2803643) B2803643
theorem B1672487 : Blo 491791 1672487 := bstep (se 1 (by rfl) ⟨1254365, by rfl⟩ : syracuseStep 1672487 = 2508731) B2508731
theorem B492891 : Blo 491791 492891 := bstep (se 1 (by rfl) ⟨369668, by rfl⟩ : syracuseStep 492891 = 739337) B739337
theorem B623963 : Blo 491791 623963 := bstep (se 1 (by rfl) ⟨467972, by rfl⟩ : syracuseStep 623963 = 935945) B935945
theorem B492911 : Blo 491791 492911 := bstep (se 1 (by rfl) ⟨369683, by rfl⟩ : syracuseStep 492911 = 739367) B739367
theorem B492967 : Blo 491791 492967 := bstep (se 1 (by rfl) ⟨369725, by rfl⟩ : syracuseStep 492967 = 739451) B739451
theorem B493051 : Blo 491791 493051 := bstep (se 1 (by rfl) ⟨369788, by rfl⟩ : syracuseStep 493051 = 739577) B739577
theorem B493119 : Blo 491791 493119 := bstep (se 1 (by rfl) ⟨369839, by rfl⟩ : syracuseStep 493119 = 739679) B739679
theorem B493127 : Blo 491791 493127 := bstep (se 1 (by rfl) ⟨369845, by rfl⟩ : syracuseStep 493127 = 739691) B739691
theorem B493279 : Blo 491791 493279 := bstep (se 1 (by rfl) ⟨369959, by rfl⟩ : syracuseStep 493279 = 739919) B739919
theorem B8980267 : Blo 491791 8980267 := bstep (se 1 (by rfl) ⟨6735200, by rfl⟩ : syracuseStep 8980267 = 13470401) B13470401
theorem B493359 : Blo 491791 493359 := bstep (se 1 (by rfl) ⟨370019, by rfl⟩ : syracuseStep 493359 = 740039) B740039
theorem B624439 : Blo 491791 624439 := bstep (se 1 (by rfl) ⟨468329, by rfl⟩ : syracuseStep 624439 = 936659) B936659
theorem B493467 : Blo 491791 493467 := bstep (se 1 (by rfl) ⟨370100, by rfl⟩ : syracuseStep 493467 = 740201) B740201
theorem B493519 : Blo 491791 493519 := bstep (se 1 (by rfl) ⟨370139, by rfl⟩ : syracuseStep 493519 = 740279) B740279
theorem B493543 : Blo 491791 493543 := bstep (se 1 (by rfl) ⟨370157, by rfl⟩ : syracuseStep 493543 = 740315) B740315
theorem B6424771 : Blo 491791 6424771 := bstep (se 1 (by rfl) ⟨4818578, by rfl⟩ : syracuseStep 6424771 = 9637157) B9637157
theorem B493855 : Blo 491791 493855 := bstep (se 1 (by rfl) ⟨370391, by rfl⟩ : syracuseStep 493855 = 740783) B740783
theorem B624935 : Blo 491791 624935 := bstep (se 1 (by rfl) ⟨468701, by rfl⟩ : syracuseStep 624935 = 937403) B937403
theorem B493915 : Blo 491791 493915 := bstep (se 1 (by rfl) ⟨370436, by rfl⟩ : syracuseStep 493915 = 740873) B740873
theorem B493935 : Blo 491791 493935 := bstep (se 1 (by rfl) ⟨370451, by rfl⟩ : syracuseStep 493935 = 740903) B740903
theorem B493991 : Blo 491791 493991 := bstep (se 1 (by rfl) ⟨370493, by rfl⟩ : syracuseStep 493991 = 740987) B740987
theorem B1247663 : Blo 491791 1247663 := bstep (se 1 (by rfl) ⟨935747, by rfl⟩ : syracuseStep 1247663 = 1871495) B1871495
theorem B2492855 : Blo 491791 2492855 := bstep (se 1 (by rfl) ⟨1869641, by rfl⟩ : syracuseStep 2492855 = 3739283) B3739283
theorem B494075 : Blo 491791 494075 := bstep (se 1 (by rfl) ⟨370556, by rfl⟩ : syracuseStep 494075 = 741113) B741113
theorem B592447 : Blo 491791 592447 := bstep (se 1 (by rfl) ⟨444335, by rfl⟩ : syracuseStep 592447 = 888671) B888671
theorem B494143 : Blo 491791 494143 := bstep (se 1 (by rfl) ⟨370607, by rfl⟩ : syracuseStep 494143 = 741215) B741215
theorem B494151 : Blo 491791 494151 := bstep (se 1 (by rfl) ⟨370613, by rfl⟩ : syracuseStep 494151 = 741227) B741227
theorem B1411663 : Blo 491791 1411663 := bstep (se 1 (by rfl) ⟨1058747, by rfl⟩ : syracuseStep 1411663 = 2117495) B2117495
theorem B625259 : Blo 491791 625259 := bstep (se 1 (by rfl) ⟨468944, by rfl⟩ : syracuseStep 625259 = 937889) B937889
theorem B494303 : Blo 491791 494303 := bstep (se 1 (by rfl) ⟨370727, by rfl⟩ : syracuseStep 494303 = 741455) B741455
theorem B494383 : Blo 491791 494383 := bstep (se 1 (by rfl) ⟨370787, by rfl⟩ : syracuseStep 494383 = 741575) B741575
theorem B1870735 : Blo 491791 1870735 := bstep (se 1 (by rfl) ⟨1403051, by rfl⟩ : syracuseStep 1870735 = 2806103) B2806103
theorem B494491 : Blo 491791 494491 := bstep (se 1 (by rfl) ⟨370868, by rfl⟩ : syracuseStep 494491 = 741737) B741737
theorem B494543 : Blo 491791 494543 := bstep (se 1 (by rfl) ⟨370907, by rfl⟩ : syracuseStep 494543 = 741815) B741815
theorem B625639 : Blo 491791 625639 := bstep (se 1 (by rfl) ⟨469229, by rfl⟩ : syracuseStep 625639 = 938459) B938459
theorem B494567 : Blo 491791 494567 := bstep (se 1 (by rfl) ⟨370925, by rfl⟩ : syracuseStep 494567 = 741851) B741851
theorem B4754447 : Blo 491791 4754447 := bstep (se 1 (by rfl) ⟨3565835, by rfl⟩ : syracuseStep 4754447 = 7131671) B7131671
theorem B494879 : Blo 491791 494879 := bstep (se 1 (by rfl) ⟨371159, by rfl⟩ : syracuseStep 494879 = 742319) B742319
theorem B5999933 : Blo 491791 5999933 := bstep (se 3 (by rfl) ⟨1124987, by rfl⟩ : syracuseStep 5999933 = 2249975) B2249975
theorem B494939 : Blo 491791 494939 := bstep (se 1 (by rfl) ⟨371204, by rfl⟩ : syracuseStep 494939 = 742409) B742409
theorem B494959 : Blo 491791 494959 := bstep (se 1 (by rfl) ⟨371219, by rfl⟩ : syracuseStep 494959 = 742439) B742439
theorem B1248635 : Blo 491791 1248635 := bstep (se 1 (by rfl) ⟨936476, by rfl⟩ : syracuseStep 1248635 = 1872953) B1872953
theorem B495015 : Blo 491791 495015 := bstep (se 1 (by rfl) ⟨371261, by rfl⟩ : syracuseStep 495015 = 742523) B742523
theorem B495099 : Blo 491791 495099 := bstep (se 1 (by rfl) ⟨371324, by rfl⟩ : syracuseStep 495099 = 742649) B742649
theorem B495167 : Blo 491791 495167 := bstep (se 1 (by rfl) ⟨371375, by rfl⟩ : syracuseStep 495167 = 742751) B742751
theorem B495175 : Blo 491791 495175 := bstep (se 1 (by rfl) ⟨371381, by rfl⟩ : syracuseStep 495175 = 742763) B742763
theorem B1248929 : Blo 491791 1248929 := bstep (se 2 (by rfl) ⟨468348, by rfl⟩ : syracuseStep 1248929 = 936697) B936697
theorem B495327 : Blo 491791 495327 := bstep (se 1 (by rfl) ⟨371495, by rfl⟩ : syracuseStep 495327 = 742991) B742991
theorem B495407 : Blo 491791 495407 := bstep (se 1 (by rfl) ⟨371555, by rfl⟩ : syracuseStep 495407 = 743111) B743111
theorem B495515 : Blo 491791 495515 := bstep (se 1 (by rfl) ⟨371636, by rfl⟩ : syracuseStep 495515 = 743273) B743273
theorem B495567 : Blo 491791 495567 := bstep (se 1 (by rfl) ⟨371675, by rfl⟩ : syracuseStep 495567 = 743351) B743351
theorem B495591 : Blo 491791 495591 := bstep (se 1 (by rfl) ⟨371693, by rfl⟩ : syracuseStep 495591 = 743387) B743387
theorem B561499 : Blo 491791 561499 := bstep (se 1 (by rfl) ⟨421124, by rfl⟩ : syracuseStep 561499 = 842249) B842249
theorem B1249627 : Blo 491791 1249627 := bstep (se 1 (by rfl) ⟨937220, by rfl⟩ : syracuseStep 1249627 = 1874441) B1874441
theorem B1053263 : Blo 491791 1053263 := bstep (se 1 (by rfl) ⟨789947, by rfl⟩ : syracuseStep 1053263 = 1579895) B1579895
theorem B2495123 : Blo 491791 2495123 := bstep (se 1 (by rfl) ⟨1871342, by rfl⟩ : syracuseStep 2495123 = 3742685) B3742685
theorem B2101913 : Blo 491791 2101913 := bstep (se 2 (by rfl) ⟨788217, by rfl⟩ : syracuseStep 2101913 = 1576435) B1576435
theorem B890075 : Blo 491791 890075 := bstep (se 1 (by rfl) ⟨667556, by rfl⟩ : syracuseStep 890075 = 1335113) B1335113
theorem B1578217 : Blo 491791 1578217 := bstep (se 2 (by rfl) ⟨591831, by rfl⟩ : syracuseStep 1578217 = 1183663) B1183663
theorem B1053929 : Blo 491791 1053929 := bstep (se 2 (by rfl) ⟨395223, by rfl⟩ : syracuseStep 1053929 = 790447) B790447
theorem B1250599 : Blo 491791 1250599 := bstep (se 1 (by rfl) ⟨937949, by rfl⟩ : syracuseStep 1250599 = 1875899) B1875899
theorem B2495933 : Blo 491791 2495933 := bstep (se 3 (by rfl) ⟨467987, by rfl⟩ : syracuseStep 2495933 = 935975) B935975
theorem B1250873 : Blo 491791 1250873 := bstep (se 2 (by rfl) ⟨469077, by rfl⟩ : syracuseStep 1250873 = 938155) B938155
theorem B2004841 : Blo 491791 2004841 := bstep (se 2 (by rfl) ⟨751815, by rfl⟩ : syracuseStep 2004841 = 1503631) B1503631
theorem B891575 : Blo 491791 891575 := bstep (se 1 (by rfl) ⟨668681, by rfl⟩ : syracuseStep 891575 = 1337363) B1337363
theorem B5610383 : Blo 491791 5610383 := bstep (se 1 (by rfl) ⟨4207787, by rfl⟩ : syracuseStep 5610383 = 8415575) B8415575
theorem B8428697 : Blo 491791 8428697 := bstep (se 2 (by rfl) ⟨3160761, by rfl⟩ : syracuseStep 8428697 = 6321523) B6321523
theorem B1252705 : Blo 491791 1252705 := bstep (se 2 (by rfl) ⟨469764, by rfl⟩ : syracuseStep 1252705 = 939529) B939529
theorem B12688973 : Blo 491791 12688973 := bstep (se 3 (by rfl) ⟨2379182, by rfl⟩ : syracuseStep 12688973 = 4758365) B4758365
theorem B1875869 : Blo 491791 1875869 := bstep (se 3 (by rfl) ⟨351725, by rfl⟩ : syracuseStep 1875869 = 703451) B703451
theorem B2662571 : Blo 491791 2662571 := bstep (se 1 (by rfl) ⟨1996928, by rfl⟩ : syracuseStep 2662571 = 3993857) B3993857
theorem B1253657 : Blo 491791 1253657 := bstep (se 2 (by rfl) ⟨470121, by rfl⟩ : syracuseStep 1253657 = 940243) B940243
theorem B1253951 : Blo 491791 1253951 := bstep (se 1 (by rfl) ⟨940463, by rfl⟩ : syracuseStep 1253951 = 1880927) B1880927
theorem B1254163 : Blo 491791 1254163 := bstep (se 1 (by rfl) ⟨940622, by rfl⟩ : syracuseStep 1254163 = 1881245) B1881245
theorem B1254599 : Blo 491791 1254599 := bstep (se 1 (by rfl) ⟨940949, by rfl⟩ : syracuseStep 1254599 = 1881899) B1881899
theorem B2368727 : Blo 491791 2368727 := bstep (se 1 (by rfl) ⟨1776545, by rfl⟩ : syracuseStep 2368727 = 3553091) B3553091
theorem B25732333 : Blo 491791 25732333 := bstep (se 3 (by rfl) ⟨4824812, by rfl⟩ : syracuseStep 25732333 = 9649625) B9649625
theorem B1254649 : Blo 491791 1254649 := bstep (se 2 (by rfl) ⟨470493, by rfl⟩ : syracuseStep 1254649 = 940987) B940987
theorem B1189151 : Blo 491791 1189151 := bstep (se 1 (by rfl) ⟨891863, by rfl⟩ : syracuseStep 1189151 = 1783727) B1783727
theorem B1877357 : Blo 491791 1877357 := bstep (se 3 (by rfl) ⟨352004, by rfl⟩ : syracuseStep 1877357 = 704009) B704009
theorem B8038045 : Blo 491791 8038045 := bstep (se 3 (by rfl) ⟨1507133, by rfl⟩ : syracuseStep 8038045 = 3014267) B3014267
theorem B2500793 : Blo 491791 2500793 := bstep (se 2 (by rfl) ⟨937797, by rfl⟩ : syracuseStep 2500793 = 1875595) B1875595
theorem B6761083 : Blo 491791 6761083 := bstep (se 1 (by rfl) ⟨5070812, by rfl⟩ : syracuseStep 6761083 = 10141625) B10141625
theorem B830135 : Blo 491791 830135 := bstep (se 1 (by rfl) ⟨622601, by rfl⟩ : syracuseStep 830135 = 1245203) B1245203
theorem B1190899 : Blo 491791 1190899 := bstep (se 1 (by rfl) ⟨893174, by rfl⟩ : syracuseStep 1190899 = 1786349) B1786349
theorem B830857 : Blo 491791 830857 := bstep (se 2 (by rfl) ⟨311571, by rfl⟩ : syracuseStep 830857 = 623143) B623143
theorem B1879483 : Blo 491791 1879483 := bstep (se 1 (by rfl) ⟨1409612, by rfl⟩ : syracuseStep 1879483 = 2819225) B2819225
theorem B2108987 : Blo 491791 2108987 := bstep (se 1 (by rfl) ⟨1581740, by rfl⟩ : syracuseStep 2108987 = 3163481) B3163481
theorem B2371187 : Blo 491791 2371187 := bstep (se 1 (by rfl) ⟨1778390, by rfl⟩ : syracuseStep 2371187 = 3556781) B3556781
theorem B1879787 : Blo 491791 1879787 := bstep (se 1 (by rfl) ⟨1409840, by rfl⟩ : syracuseStep 1879787 = 2819681) B2819681
theorem B831289 : Blo 491791 831289 := bstep (se 2 (by rfl) ⟨311733, by rfl⟩ : syracuseStep 831289 = 623467) B623467
theorem B2502575 : Blo 491791 2502575 := bstep (se 1 (by rfl) ⟨1876931, by rfl⟩ : syracuseStep 2502575 = 3753863) B3753863
theorem B831593 : Blo 491791 831593 := bstep (se 2 (by rfl) ⟨311847, by rfl⟩ : syracuseStep 831593 = 623695) B623695
theorem B2371787 : Blo 491791 2371787 := bstep (se 1 (by rfl) ⟨1778840, by rfl⟩ : syracuseStep 2371787 = 3557681) B3557681
theorem B1880273 : Blo 491791 1880273 := bstep (se 2 (by rfl) ⟨705102, by rfl⟩ : syracuseStep 1880273 = 1410205) B1410205
theorem B9515501 : Blo 491791 9515501 := bstep (se 3 (by rfl) ⟨1784156, by rfl⟩ : syracuseStep 9515501 = 3568313) B3568313
theorem B6304301 : Blo 491791 6304301 := bstep (se 3 (by rfl) ⟨1182056, by rfl⟩ : syracuseStep 6304301 = 2364113) B2364113
theorem B4010593 : Blo 491791 4010593 := bstep (se 2 (by rfl) ⟨1503972, by rfl⟩ : syracuseStep 4010593 = 3007945) B3007945
theorem B1880729 : Blo 491791 1880729 := bstep (se 2 (by rfl) ⟨705273, by rfl⟩ : syracuseStep 1880729 = 1410547) B1410547
theorem B1880759 : Blo 491791 1880759 := bstep (se 1 (by rfl) ⟨1410569, by rfl⟩ : syracuseStep 1880759 = 2821139) B2821139
theorem B4010719 : Blo 491791 4010719 := bstep (se 1 (by rfl) ⟨3008039, by rfl⟩ : syracuseStep 4010719 = 6016079) B6016079
theorem B833017 : Blo 491791 833017 := bstep (se 2 (by rfl) ⟨312381, by rfl⟩ : syracuseStep 833017 = 624763) B624763
theorem B1783453 : Blo 491791 1783453 := bstep (se 3 (by rfl) ⟨334397, by rfl⟩ : syracuseStep 1783453 = 668795) B668795
theorem B800519 : Blo 491791 800519 := bstep (se 1 (by rfl) ⟨600389, by rfl⟩ : syracuseStep 800519 = 1200779) B1200779
theorem B833287 : Blo 491791 833287 := bstep (se 1 (by rfl) ⟨624965, by rfl⟩ : syracuseStep 833287 = 1249931) B1249931
theorem B833321 : Blo 491791 833321 := bstep (se 2 (by rfl) ⟨312495, by rfl⟩ : syracuseStep 833321 = 624991) B624991
theorem B834043 : Blo 491791 834043 := bstep (se 1 (by rfl) ⟨625532, by rfl⟩ : syracuseStep 834043 = 1251065) B1251065
theorem B2505491 : Blo 491791 2505491 := bstep (se 1 (by rfl) ⟨1879118, by rfl⟩ : syracuseStep 2505491 = 3758237) B3758237
theorem B834475 : Blo 491791 834475 := bstep (se 1 (by rfl) ⟨625856, by rfl⟩ : syracuseStep 834475 = 1251713) B1251713
theorem B4734071 : Blo 491791 4734071 := bstep (se 1 (by rfl) ⟨3550553, by rfl⟩ : syracuseStep 4734071 = 7101107) B7101107
theorem B834779 : Blo 491791 834779 := bstep (se 1 (by rfl) ⟨626084, by rfl⟩ : syracuseStep 834779 = 1252169) B1252169
theorem B2374877 : Blo 491791 2374877 := bstep (se 3 (by rfl) ⟨445289, by rfl⟩ : syracuseStep 2374877 = 890579) B890579
theorem B2112779 : Blo 491791 2112779 := bstep (se 1 (by rfl) ⟨1584584, by rfl⟩ : syracuseStep 2112779 = 3169169) B3169169
theorem B572711 : Blo 491791 572711 := bstep (se 1 (by rfl) ⟨429533, by rfl⟩ : syracuseStep 572711 = 859067) B859067
theorem B1621367 : Blo 491791 1621367 := bstep (se 1 (by rfl) ⟨1216025, by rfl⟩ : syracuseStep 1621367 = 2432051) B2432051
theorem B6339977 : Blo 491791 6339977 := bstep (se 2 (by rfl) ⟨2377491, by rfl⟩ : syracuseStep 6339977 = 4754983) B4754983
theorem B835015 : Blo 491791 835015 := bstep (se 1 (by rfl) ⟨626261, by rfl⟩ : syracuseStep 835015 = 1252523) B1252523
theorem B2801411 : Blo 491791 2801411 := bstep (se 1 (by rfl) ⟨2101058, by rfl⟩ : syracuseStep 2801411 = 4202117) B4202117
theorem B2506625 : Blo 491791 2506625 := bstep (se 2 (by rfl) ⟨939984, by rfl⟩ : syracuseStep 2506625 = 1879969) B1879969
theorem B835535 : Blo 491791 835535 := bstep (se 1 (by rfl) ⟨626651, by rfl⟩ : syracuseStep 835535 = 1253303) B1253303
theorem B2244779 : Blo 491791 2244779 := bstep (se 1 (by rfl) ⟨1683584, by rfl⟩ : syracuseStep 2244779 = 3367169) B3367169
theorem B2244937 : Blo 491791 2244937 := bstep (se 2 (by rfl) ⟨841851, by rfl⟩ : syracuseStep 2244937 = 1683703) B1683703
theorem B2539883 : Blo 491791 2539883 := bstep (se 1 (by rfl) ⟨1904912, by rfl⟩ : syracuseStep 2539883 = 3809825) B3809825
theorem B737855 : Blo 491791 737855 := bstep (se 1 (by rfl) ⟨553391, by rfl⟩ : syracuseStep 737855 = 1106783) B1106783
theorem B836203 : Blo 491791 836203 := bstep (se 1 (by rfl) ⟨627152, by rfl⟩ : syracuseStep 836203 = 1254305) B1254305
theorem B2507435 : Blo 491791 2507435 := bstep (se 1 (by rfl) ⟨1880576, by rfl⟩ : syracuseStep 2507435 = 3761153) B3761153
theorem B737975 : Blo 491791 737975 := bstep (se 1 (by rfl) ⟨553481, by rfl⟩ : syracuseStep 737975 = 1106963) B1106963
theorem B2376415 : Blo 491791 2376415 := bstep (se 1 (by rfl) ⟨1782311, by rfl⟩ : syracuseStep 2376415 = 3564623) B3564623
theorem B8012621 : Blo 491791 8012621 := bstep (se 3 (by rfl) ⟨1502366, by rfl⟩ : syracuseStep 8012621 = 3004733) B3004733
theorem B738203 : Blo 491791 738203 := bstep (se 1 (by rfl) ⟨553652, by rfl⟩ : syracuseStep 738203 = 1107305) B1107305
theorem B836507 : Blo 491791 836507 := bstep (se 1 (by rfl) ⟨627380, by rfl⟩ : syracuseStep 836507 = 1254761) B1254761
theorem B2507921 : Blo 491791 2507921 := bstep (se 2 (by rfl) ⟨940470, by rfl⟩ : syracuseStep 2507921 = 1880941) B1880941
theorem B738599 : Blo 491791 738599 := bstep (se 1 (by rfl) ⟨553949, by rfl⟩ : syracuseStep 738599 = 1107899) B1107899
theorem B4113713 : Blo 491791 4113713 := bstep (se 2 (by rfl) ⟨1542642, by rfl⟩ : syracuseStep 4113713 = 3085285) B3085285
theorem B738683 : Blo 491791 738683 := bstep (se 1 (by rfl) ⟨554012, by rfl⟩ : syracuseStep 738683 = 1108025) B1108025
theorem B738809 : Blo 491791 738809 := bstep (se 2 (by rfl) ⟨277053, by rfl⟩ : syracuseStep 738809 = 554107) B554107
theorem B738911 : Blo 491791 738911 := bstep (se 1 (by rfl) ⟨554183, by rfl⟩ : syracuseStep 738911 = 1108367) B1108367
theorem B935687 : Blo 491791 935687 := bstep (se 1 (by rfl) ⟨701765, by rfl⟩ : syracuseStep 935687 = 1403531) B1403531
theorem B8406827 : Blo 491791 8406827 := bstep (se 1 (by rfl) ⟨6305120, by rfl⟩ : syracuseStep 8406827 = 12610241) B12610241
theorem B739127 : Blo 491791 739127 := bstep (se 1 (by rfl) ⟨554345, by rfl⟩ : syracuseStep 739127 = 1108691) B1108691
theorem B6408143 : Blo 491791 6408143 := bstep (se 1 (by rfl) ⟨4806107, by rfl⟩ : syracuseStep 6408143 = 9612215) B9612215
theorem B739433 : Blo 491791 739433 := bstep (se 2 (by rfl) ⟨277287, by rfl⟩ : syracuseStep 739433 = 554575) B554575
theorem B2115719 : Blo 491791 2115719 := bstep (se 1 (by rfl) ⟨1586789, by rfl⟩ : syracuseStep 2115719 = 3173579) B3173579
theorem B12503285 : Blo 491791 12503285 := bstep (se 5 (by rfl) ⟨586091, by rfl⟩ : syracuseStep 12503285 = 1172183) B1172183
theorem B3164453 : Blo 491791 3164453 := bstep (se 4 (by rfl) ⟨296667, by rfl⟩ : syracuseStep 3164453 = 593335) B593335
theorem B739751 : Blo 491791 739751 := bstep (se 1 (by rfl) ⟨554813, by rfl⟩ : syracuseStep 739751 = 1109627) B1109627
theorem B739835 : Blo 491791 739835 := bstep (se 1 (by rfl) ⟨554876, by rfl⟩ : syracuseStep 739835 = 1109753) B1109753
theorem B739961 : Blo 491791 739961 := bstep (se 2 (by rfl) ⟨277485, by rfl⟩ : syracuseStep 739961 = 554971) B554971
theorem B740015 : Blo 491791 740015 := bstep (se 1 (by rfl) ⟨555011, by rfl⟩ : syracuseStep 740015 = 1110023) B1110023
theorem B740063 : Blo 491791 740063 := bstep (se 1 (by rfl) ⟨555047, by rfl⟩ : syracuseStep 740063 = 1110095) B1110095
theorem B3558167 : Blo 491791 3558167 := bstep (se 1 (by rfl) ⟨2668625, by rfl⟩ : syracuseStep 3558167 = 5337251) B5337251
theorem B5360519 : Blo 491791 5360519 := bstep (se 1 (by rfl) ⟨4020389, by rfl⟩ : syracuseStep 5360519 = 8040779) B8040779
theorem B740327 : Blo 491791 740327 := bstep (se 1 (by rfl) ⟨555245, by rfl⟩ : syracuseStep 740327 = 1110491) B1110491
theorem B740585 : Blo 491791 740585 := bstep (se 2 (by rfl) ⟨277719, by rfl⟩ : syracuseStep 740585 = 555439) B555439
theorem B740639 : Blo 491791 740639 := bstep (se 1 (by rfl) ⟨555479, by rfl⟩ : syracuseStep 740639 = 1110959) B1110959
theorem B740807 : Blo 491791 740807 := bstep (se 1 (by rfl) ⟨555605, by rfl⟩ : syracuseStep 740807 = 1111211) B1111211
theorem B5492423 : Blo 491791 5492423 := bstep (se 1 (by rfl) ⟨4119317, by rfl⟩ : syracuseStep 5492423 = 8238635) B8238635
theorem B5623505 : Blo 491791 5623505 := bstep (se 2 (by rfl) ⟨2108814, by rfl⟩ : syracuseStep 5623505 = 4217629) B4217629
theorem B741161 : Blo 491791 741161 := bstep (se 2 (by rfl) ⟨277935, by rfl⟩ : syracuseStep 741161 = 555871) B555871
theorem B741167 : Blo 491791 741167 := bstep (se 1 (by rfl) ⟨555875, by rfl⟩ : syracuseStep 741167 = 1111751) B1111751
theorem B2674505 : Blo 491791 2674505 := bstep (se 2 (by rfl) ⟨1002939, by rfl⟩ : syracuseStep 2674505 = 2005879) B2005879
theorem B2805785 : Blo 491791 2805785 := bstep (se 2 (by rfl) ⟨1052169, by rfl⟩ : syracuseStep 2805785 = 2104339) B2104339
theorem B1331329 : Blo 491791 1331329 := bstep (se 2 (by rfl) ⟨499248, by rfl⟩ : syracuseStep 1331329 = 998497) B998497
theorem B741641 : Blo 491791 741641 := bstep (se 2 (by rfl) ⟨278115, by rfl⟩ : syracuseStep 741641 = 556231) B556231
theorem B3035465 : Blo 491791 3035465 := bstep (se 2 (by rfl) ⟨1138299, by rfl⟩ : syracuseStep 3035465 = 2276599) B2276599
theorem B741743 : Blo 491791 741743 := bstep (se 1 (by rfl) ⟨556307, by rfl⟩ : syracuseStep 741743 = 1112615) B1112615
theorem B741959 : Blo 491791 741959 := bstep (se 1 (by rfl) ⟨556469, by rfl⟩ : syracuseStep 741959 = 1112939) B1112939
theorem B938603 : Blo 491791 938603 := bstep (se 1 (by rfl) ⟨703952, by rfl⟩ : syracuseStep 938603 = 1407905) B1407905
theorem B741995 : Blo 491791 741995 := bstep (se 1 (by rfl) ⟨556496, by rfl⟩ : syracuseStep 741995 = 1112993) B1112993
theorem B742223 : Blo 491791 742223 := bstep (se 1 (by rfl) ⟨556667, by rfl⟩ : syracuseStep 742223 = 1113335) B1113335
theorem B4740221 : Blo 491791 4740221 := bstep (se 3 (by rfl) ⟨888791, by rfl⟩ : syracuseStep 4740221 = 1777583) B1777583
theorem B742619 : Blo 491791 742619 := bstep (se 1 (by rfl) ⟨556964, by rfl⟩ : syracuseStep 742619 = 1113929) B1113929
theorem B4281623 : Blo 491791 4281623 := bstep (se 1 (by rfl) ⟨3211217, by rfl⟩ : syracuseStep 4281623 = 6422435) B6422435
theorem B1660283 : Blo 491791 1660283 := bstep (se 1 (by rfl) ⟨1245212, by rfl⟩ : syracuseStep 1660283 = 2490425) B2490425
theorem B742793 : Blo 491791 742793 := bstep (se 2 (by rfl) ⟨278547, by rfl⟩ : syracuseStep 742793 = 557095) B557095
theorem B1922617 : Blo 491791 1922617 := bstep (se 2 (by rfl) ⟨720981, by rfl⟩ : syracuseStep 1922617 = 1441963) B1441963
theorem B743147 : Blo 491791 743147 := bstep (se 1 (by rfl) ⟨557360, by rfl⟩ : syracuseStep 743147 = 1114721) B1114721
theorem B939833 : Blo 491791 939833 := bstep (se 2 (by rfl) ⟨352437, by rfl⟩ : syracuseStep 939833 = 704875) B704875
theorem B2053993 : Blo 491791 2053993 := bstep (se 2 (by rfl) ⟨770247, by rfl⟩ : syracuseStep 2053993 = 1540495) B1540495
theorem B743375 : Blo 491791 743375 := bstep (se 1 (by rfl) ⟨557531, by rfl⟩ : syracuseStep 743375 = 1115063) B1115063
theorem B1923257 : Blo 491791 1923257 := bstep (se 2 (by rfl) ⟨721221, by rfl⟩ : syracuseStep 1923257 = 1442443) B1442443
theorem B1661687 : Blo 491791 1661687 := bstep (se 1 (by rfl) ⟨1246265, by rfl⟩ : syracuseStep 1661687 = 2492531) B2492531
theorem B645943 : Blo 491791 645943 := bstep (se 1 (by rfl) ⟨484457, by rfl⟩ : syracuseStep 645943 = 968915) B968915
theorem B1203175 : Blo 491791 1203175 := bstep (se 1 (by rfl) ⟨902381, by rfl⟩ : syracuseStep 1203175 = 1804763) B1804763
theorem B5790937 : Blo 491791 5790937 := bstep (se 2 (by rfl) ⟨2171601, by rfl⟩ : syracuseStep 5790937 = 4343203) B4343203
theorem B1662767 : Blo 491791 1662767 := bstep (se 1 (by rfl) ⟨1247075, by rfl⟩ : syracuseStep 1662767 = 2494151) B2494151
theorem B712495 : Blo 491791 712495 := bstep (se 1 (by rfl) ⟨534371, by rfl⟩ : syracuseStep 712495 = 1068743) B1068743
theorem B5988401 : Blo 491791 5988401 := bstep (se 2 (by rfl) ⟨2245650, by rfl⟩ : syracuseStep 5988401 = 4491301) B4491301
theorem B14278787 : Blo 491791 14278787 := bstep (se 1 (by rfl) ⟨10709090, by rfl⟩ : syracuseStep 14278787 = 21418181) B21418181
theorem B3170785 : Blo 491791 3170785 := bstep (se 2 (by rfl) ⟨1189044, by rfl⟩ : syracuseStep 3170785 = 2378089) B2378089
theorem B1335827 : Blo 491791 1335827 := bstep (se 1 (by rfl) ⟨1001870, by rfl⟩ : syracuseStep 1335827 = 2003741) B2003741
theorem B1106603 : Blo 491791 1106603 := bstep (se 1 (by rfl) ⟨829952, by rfl⟩ : syracuseStep 1106603 = 1659905) B1659905
theorem B1107143 : Blo 491791 1107143 := bstep (se 1 (by rfl) ⟨830357, by rfl⟩ : syracuseStep 1107143 = 1660715) B1660715
theorem B1926443 : Blo 491791 1926443 := bstep (se 1 (by rfl) ⟨1444832, by rfl⟩ : syracuseStep 1926443 = 2889665) B2889665
theorem B1107323 : Blo 491791 1107323 := bstep (se 1 (by rfl) ⟨830492, by rfl⟩ : syracuseStep 1107323 = 1660985) B1660985
theorem B1271227 : Blo 491791 1271227 := bstep (se 1 (by rfl) ⟨953420, by rfl⟩ : syracuseStep 1271227 = 1906841) B1906841
theorem B10118641 : Blo 491791 10118641 := bstep (se 2 (by rfl) ⟨3794490, by rfl⟩ : syracuseStep 10118641 = 7588981) B7588981
theorem B1107449 : Blo 491791 1107449 := bstep (se 2 (by rfl) ⟨415293, by rfl⟩ : syracuseStep 1107449 = 830587) B830587
theorem B1107539 : Blo 491791 1107539 := bstep (se 1 (by rfl) ⟨830654, by rfl⟩ : syracuseStep 1107539 = 1661309) B1661309
theorem B1107719 : Blo 491791 1107719 := bstep (se 1 (by rfl) ⟨830789, by rfl⟩ : syracuseStep 1107719 = 1661579) B1661579
theorem B1664873 : Blo 491791 1664873 := bstep (se 2 (by rfl) ⟨624327, by rfl⟩ : syracuseStep 1664873 = 1248655) B1248655
theorem B1665305 : Blo 491791 1665305 := bstep (se 2 (by rfl) ⟨624489, by rfl⟩ : syracuseStep 1665305 = 1248979) B1248979
theorem B1108331 : Blo 491791 1108331 := bstep (se 1 (by rfl) ⟨831248, by rfl⟩ : syracuseStep 1108331 = 1662497) B1662497
theorem B11397505 : Blo 491791 11397505 := bstep (se 2 (by rfl) ⟨4274064, by rfl⟩ : syracuseStep 11397505 = 8548129) B8548129
theorem B3369383 : Blo 491791 3369383 := bstep (se 1 (by rfl) ⟨2527037, by rfl⟩ : syracuseStep 3369383 = 5054075) B5054075
theorem B1108475 : Blo 491791 1108475 := bstep (se 1 (by rfl) ⟨831356, by rfl⟩ : syracuseStep 1108475 = 1662713) B1662713
theorem B1796681 : Blo 491791 1796681 := bstep (se 2 (by rfl) ⟨673755, by rfl⟩ : syracuseStep 1796681 = 1347511) B1347511
theorem B10644047 : Blo 491791 10644047 := bstep (se 1 (by rfl) ⟨7983035, by rfl⟩ : syracuseStep 10644047 = 15966071) B15966071
theorem B1108601 : Blo 491791 1108601 := bstep (se 2 (by rfl) ⟨415725, by rfl⟩ : syracuseStep 1108601 = 831451) B831451
theorem B3369595 : Blo 491791 3369595 := bstep (se 1 (by rfl) ⟨2527196, by rfl⟩ : syracuseStep 3369595 = 5054393) B5054393
theorem B1108655 : Blo 491791 1108655 := bstep (se 1 (by rfl) ⟨831491, by rfl⟩ : syracuseStep 1108655 = 1662983) B1662983
theorem B2878199 : Blo 491791 2878199 := bstep (se 1 (by rfl) ⟨2158649, by rfl⟩ : syracuseStep 2878199 = 4317299) B4317299
theorem B1108727 : Blo 491791 1108727 := bstep (se 1 (by rfl) ⟨831545, by rfl⟩ : syracuseStep 1108727 = 1663091) B1663091
theorem B12151565 : Blo 491791 12151565 := bstep (se 3 (by rfl) ⟨2278418, by rfl⟩ : syracuseStep 12151565 = 4556837) B4556837
theorem B1108907 : Blo 491791 1108907 := bstep (se 1 (by rfl) ⟨831680, by rfl⟩ : syracuseStep 1108907 = 1663361) B1663361
theorem B1404191 : Blo 491791 1404191 := bstep (se 1 (by rfl) ⟨1053143, by rfl⟩ : syracuseStep 1404191 = 2106287) B2106287
theorem B1109447 : Blo 491791 1109447 := bstep (se 1 (by rfl) ⟨832085, by rfl⟩ : syracuseStep 1109447 = 1664171) B1664171
theorem B4746761 : Blo 491791 4746761 := bstep (se 2 (by rfl) ⟨1780035, by rfl⟩ : syracuseStep 4746761 = 3560071) B3560071
theorem B1404499 : Blo 491791 1404499 := bstep (se 1 (by rfl) ⟨1053374, by rfl⟩ : syracuseStep 1404499 = 2106749) B2106749
theorem B1666655 : Blo 491791 1666655 := bstep (se 1 (by rfl) ⟨1249991, by rfl⟩ : syracuseStep 1666655 = 2499983) B2499983
theorem B14282477 : Blo 491791 14282477 := bstep (se 3 (by rfl) ⟨2677964, by rfl⟩ : syracuseStep 14282477 = 5355929) B5355929
theorem B6319883 : Blo 491791 6319883 := bstep (se 1 (by rfl) ⟨4739912, by rfl⟩ : syracuseStep 6319883 = 9479825) B9479825
theorem B1109807 : Blo 491791 1109807 := bstep (se 1 (by rfl) ⟨832355, by rfl⟩ : syracuseStep 1109807 = 1664711) B1664711
theorem B6353099 : Blo 491791 6353099 := bstep (se 1 (by rfl) ⟨4764824, by rfl⟩ : syracuseStep 6353099 = 9529649) B9529649
theorem B4223339 : Blo 491791 4223339 := bstep (se 1 (by rfl) ⟨3167504, by rfl⟩ : syracuseStep 4223339 = 6335009) B6335009
theorem B1110383 : Blo 491791 1110383 := bstep (se 1 (by rfl) ⟨832787, by rfl⟩ : syracuseStep 1110383 = 1665575) B1665575
theorem B1110455 : Blo 491791 1110455 := bstep (se 1 (by rfl) ⟨832841, by rfl⟩ : syracuseStep 1110455 = 1665683) B1665683
theorem B1110599 : Blo 491791 1110599 := bstep (se 1 (by rfl) ⟨832949, by rfl⟩ : syracuseStep 1110599 = 1665899) B1665899
theorem B553567 : Blo 491791 553567 := bstep (se 1 (by rfl) ⟨415175, by rfl⟩ : syracuseStep 553567 = 830351) B830351
theorem B1110635 : Blo 491791 1110635 := bstep (se 1 (by rfl) ⟨832976, by rfl⟩ : syracuseStep 1110635 = 1665953) B1665953
theorem B1405775 : Blo 491791 1405775 := bstep (se 1 (by rfl) ⟨1054331, by rfl⟩ : syracuseStep 1405775 = 2108663) B2108663
theorem B1668059 : Blo 491791 1668059 := bstep (se 1 (by rfl) ⟨1251044, by rfl⟩ : syracuseStep 1668059 = 2502089) B2502089
theorem B1111031 : Blo 491791 1111031 := bstep (se 1 (by rfl) ⟨833273, by rfl⟩ : syracuseStep 1111031 = 1666547) B1666547
theorem B7992377 : Blo 491791 7992377 := bstep (se 2 (by rfl) ⟨2997141, by rfl⟩ : syracuseStep 7992377 = 5994283) B5994283
theorem B2815033 : Blo 491791 2815033 := bstep (se 2 (by rfl) ⟨1055637, by rfl⟩ : syracuseStep 2815033 = 2111275) B2111275
theorem B1668221 : Blo 491791 1668221 := bstep (se 3 (by rfl) ⟨312791, by rfl⟩ : syracuseStep 1668221 = 625583) B625583
theorem B1995923 : Blo 491791 1995923 := bstep (se 1 (by rfl) ⟨1496942, by rfl⟩ : syracuseStep 1995923 = 2993885) B2993885
theorem B1668329 : Blo 491791 1668329 := bstep (se 2 (by rfl) ⟨625623, by rfl⟩ : syracuseStep 1668329 = 1251247) B1251247
theorem B1996019 : Blo 491791 1996019 := bstep (se 1 (by rfl) ⟨1497014, by rfl⟩ : syracuseStep 1996019 = 2994029) B2994029
theorem B1111391 : Blo 491791 1111391 := bstep (se 1 (by rfl) ⟨833543, by rfl⟩ : syracuseStep 1111391 = 1667087) B1667087
theorem B1668491 : Blo 491791 1668491 := bstep (se 1 (by rfl) ⟨1251368, by rfl⟩ : syracuseStep 1668491 = 2502737) B2502737
theorem B554719 : Blo 491791 554719 := bstep (se 1 (by rfl) ⟨416039, by rfl⟩ : syracuseStep 554719 = 832079) B832079
theorem B1111787 : Blo 491791 1111787 := bstep (se 1 (by rfl) ⟨833840, by rfl⟩ : syracuseStep 1111787 = 1667681) B1667681
theorem B1111913 : Blo 491791 1111913 := bstep (se 2 (by rfl) ⟨416967, by rfl⟩ : syracuseStep 1111913 = 833935) B833935
theorem B13727981 : Blo 491791 13727981 := bstep (se 3 (by rfl) ⟨2573996, by rfl⟩ : syracuseStep 13727981 = 5147993) B5147993
theorem B555295 : Blo 491791 555295 := bstep (se 1 (by rfl) ⟨416471, by rfl⟩ : syracuseStep 555295 = 832943) B832943
theorem B1407415 : Blo 491791 1407415 := bstep (se 1 (by rfl) ⟨1055561, by rfl⟩ : syracuseStep 1407415 = 2111123) B2111123
theorem B15464945 : Blo 491791 15464945 := bstep (se 2 (by rfl) ⟨5799354, by rfl⟩ : syracuseStep 15464945 = 11598709) B11598709
theorem B555583 : Blo 491791 555583 := bstep (se 1 (by rfl) ⟨416687, by rfl⟩ : syracuseStep 555583 = 833375) B833375
theorem B948809 : Blo 491791 948809 := bstep (se 2 (by rfl) ⟨355803, by rfl⟩ : syracuseStep 948809 = 711607) B711607
theorem B752249 : Blo 491791 752249 := bstep (se 2 (by rfl) ⟨282093, by rfl⟩ : syracuseStep 752249 = 564187) B564187
theorem B752303 : Blo 491791 752303 := bstep (se 1 (by rfl) ⟨564227, by rfl⟩ : syracuseStep 752303 = 1128455) B1128455
theorem B1112759 : Blo 491791 1112759 := bstep (se 1 (by rfl) ⟨834569, by rfl⟩ : syracuseStep 1112759 = 1669139) B1669139
theorem B1997693 : Blo 491791 1997693 := bstep (se 3 (by rfl) ⟨374567, by rfl⟩ : syracuseStep 1997693 = 749135) B749135
theorem B1112975 : Blo 491791 1112975 := bstep (se 1 (by rfl) ⟨834731, by rfl⟩ : syracuseStep 1112975 = 1669463) B1669463
theorem B556411 : Blo 491791 556411 := bstep (se 1 (by rfl) ⟨417308, by rfl⟩ : syracuseStep 556411 = 834617) B834617
theorem B4750757 : Blo 491791 4750757 := bstep (se 4 (by rfl) ⟨445383, by rfl⟩ : syracuseStep 4750757 = 890767) B890767
theorem B5078533 : Blo 491791 5078533 := bstep (se 4 (by rfl) ⟨476112, by rfl⟩ : syracuseStep 5078533 = 952225) B952225
theorem B2489939 : Blo 491791 2489939 := bstep (se 1 (by rfl) ⟨1867454, by rfl⟩ : syracuseStep 2489939 = 3734909) B3734909
theorem B1113695 : Blo 491791 1113695 := bstep (se 1 (by rfl) ⟨835271, by rfl⟩ : syracuseStep 1113695 = 1670543) B1670543
theorem B1408747 : Blo 491791 1408747 := bstep (se 1 (by rfl) ⟨1056560, by rfl⟩ : syracuseStep 1408747 = 2113121) B2113121
theorem B1113911 : Blo 491791 1113911 := bstep (se 1 (by rfl) ⟨835433, by rfl⟩ : syracuseStep 1113911 = 1670867) B1670867
theorem B556879 : Blo 491791 556879 := bstep (se 1 (by rfl) ⟨417659, by rfl⟩ : syracuseStep 556879 = 835319) B835319
theorem B1245415 : Blo 491791 1245415 := bstep (se 1 (by rfl) ⟨934061, by rfl⟩ : syracuseStep 1245415 = 1868123) B1868123
theorem B1114343 : Blo 491791 1114343 := bstep (se 1 (by rfl) ⟨835757, by rfl⟩ : syracuseStep 1114343 = 1671515) B1671515
theorem B491903 : Blo 491791 491903 := bstep (se 1 (by rfl) ⟨368927, by rfl⟩ : syracuseStep 491903 = 737855) B737855
theorem B1671623 : Blo 491791 1671623 := bstep (se 1 (by rfl) ⟨1253717, by rfl⟩ : syracuseStep 1671623 = 2507435) B2507435
theorem B491983 : Blo 491791 491983 := bstep (se 1 (by rfl) ⟨368987, by rfl⟩ : syracuseStep 491983 = 737975) B737975
theorem B5341747 : Blo 491791 5341747 := bstep (se 1 (by rfl) ⟨4006310, by rfl⟩ : syracuseStep 5341747 = 8012621) B8012621
theorem B492135 : Blo 491791 492135 := bstep (se 1 (by rfl) ⟨369101, by rfl⟩ : syracuseStep 492135 = 738203) B738203
theorem B557671 : Blo 491791 557671 := bstep (se 1 (by rfl) ⟨418253, by rfl⟩ : syracuseStep 557671 = 836507) B836507
theorem B4227713 : Blo 491791 4227713 := bstep (se 2 (by rfl) ⟨1585392, by rfl⟩ : syracuseStep 4227713 = 3170785) B3170785
theorem B1671947 : Blo 491791 1671947 := bstep (se 1 (by rfl) ⟨1253960, by rfl⟩ : syracuseStep 1671947 = 2507921) B2507921
theorem B1114937 : Blo 491791 1114937 := bstep (se 2 (by rfl) ⟨418101, by rfl⟩ : syracuseStep 1114937 = 836203) B836203
theorem B1246063 : Blo 491791 1246063 := bstep (se 1 (by rfl) ⟨934547, by rfl⟩ : syracuseStep 1246063 = 1869095) B1869095
theorem B492399 : Blo 491791 492399 := bstep (se 1 (by rfl) ⟨369299, by rfl⟩ : syracuseStep 492399 = 738599) B738599
theorem B1114991 : Blo 491791 1114991 := bstep (se 1 (by rfl) ⟨836243, by rfl⟩ : syracuseStep 1114991 = 1672487) B1672487
theorem B492455 : Blo 491791 492455 := bstep (se 1 (by rfl) ⟨369341, by rfl⟩ : syracuseStep 492455 = 738683) B738683
theorem B492539 : Blo 491791 492539 := bstep (se 1 (by rfl) ⟨369404, by rfl⟩ : syracuseStep 492539 = 738809) B738809
theorem B1672217 : Blo 491791 1672217 := bstep (se 2 (by rfl) ⟨627081, by rfl⟩ : syracuseStep 1672217 = 1254163) B1254163
theorem B492607 : Blo 491791 492607 := bstep (se 1 (by rfl) ⟨369455, by rfl⟩ : syracuseStep 492607 = 738911) B738911
theorem B623791 : Blo 491791 623791 := bstep (se 1 (by rfl) ⟨467843, by rfl⟩ : syracuseStep 623791 = 935687) B935687
theorem B5604551 : Blo 491791 5604551 := bstep (se 1 (by rfl) ⟨4203413, by rfl⟩ : syracuseStep 5604551 = 8406827) B8406827
theorem B492751 : Blo 491791 492751 := bstep (se 1 (by rfl) ⟨369563, by rfl⟩ : syracuseStep 492751 = 739127) B739127
theorem B2491721 : Blo 491791 2491721 := bstep (se 2 (by rfl) ⟨934395, by rfl⟩ : syracuseStep 2491721 = 1868791) B1868791
theorem B492955 : Blo 491791 492955 := bstep (se 1 (by rfl) ⟨369716, by rfl⟩ : syracuseStep 492955 = 739433) B739433
theorem B1410479 : Blo 491791 1410479 := bstep (se 1 (by rfl) ⟨1057859, by rfl⟩ : syracuseStep 1410479 = 2115719) B2115719
theorem B493167 : Blo 491791 493167 := bstep (se 1 (by rfl) ⟨369875, by rfl⟩ : syracuseStep 493167 = 739751) B739751
theorem B34309777 : Blo 491791 34309777 := bstep (se 2 (by rfl) ⟨12866166, by rfl⟩ : syracuseStep 34309777 = 25732333) B25732333
theorem B1672865 : Blo 491791 1672865 := bstep (se 2 (by rfl) ⟨627324, by rfl⟩ : syracuseStep 1672865 = 1254649) B1254649
theorem B493223 : Blo 491791 493223 := bstep (se 1 (by rfl) ⟨369917, by rfl⟩ : syracuseStep 493223 = 739835) B739835
theorem B493307 : Blo 491791 493307 := bstep (se 1 (by rfl) ⟨369980, by rfl⟩ : syracuseStep 493307 = 739961) B739961
theorem B493343 : Blo 491791 493343 := bstep (se 1 (by rfl) ⟨370007, by rfl⟩ : syracuseStep 493343 = 740015) B740015
theorem B493375 : Blo 491791 493375 := bstep (se 1 (by rfl) ⟨370031, by rfl⟩ : syracuseStep 493375 = 740063) B740063
theorem B3573679 : Blo 491791 3573679 := bstep (se 1 (by rfl) ⟨2680259, by rfl⟩ : syracuseStep 3573679 = 5360519) B5360519
theorem B493551 : Blo 491791 493551 := bstep (se 1 (by rfl) ⟨370163, by rfl⟩ : syracuseStep 493551 = 740327) B740327
theorem B493723 : Blo 491791 493723 := bstep (se 1 (by rfl) ⟨370292, by rfl⟩ : syracuseStep 493723 = 740585) B740585
theorem B493759 : Blo 491791 493759 := bstep (se 1 (by rfl) ⟨370319, by rfl⟩ : syracuseStep 493759 = 740639) B740639
theorem B3999955 : Blo 491791 3999955 := bstep (se 1 (by rfl) ⟨2999966, by rfl⟩ : syracuseStep 3999955 = 5999933) B5999933
theorem B493871 : Blo 491791 493871 := bstep (se 1 (by rfl) ⟨370403, by rfl⟩ : syracuseStep 493871 = 740807) B740807
theorem B494107 : Blo 491791 494107 := bstep (se 1 (by rfl) ⟨370580, by rfl⟩ : syracuseStep 494107 = 741161) B741161
theorem B494111 : Blo 491791 494111 := bstep (se 1 (by rfl) ⟨370583, by rfl⟩ : syracuseStep 494111 = 741167) B741167
theorem B1870523 : Blo 491791 1870523 := bstep (se 1 (by rfl) ⟨1402892, by rfl⟩ : syracuseStep 1870523 = 2805785) B2805785
theorem B494427 : Blo 491791 494427 := bstep (se 1 (by rfl) ⟨370820, by rfl⟩ : syracuseStep 494427 = 741641) B741641
theorem B494495 : Blo 491791 494495 := bstep (se 1 (by rfl) ⟨370871, by rfl⟩ : syracuseStep 494495 = 741743) B741743
theorem B494639 : Blo 491791 494639 := bstep (se 1 (by rfl) ⟨370979, by rfl⟩ : syracuseStep 494639 = 741959) B741959
theorem B625735 : Blo 491791 625735 := bstep (se 1 (by rfl) ⟨469301, by rfl⟩ : syracuseStep 625735 = 938603) B938603
theorem B494663 : Blo 491791 494663 := bstep (se 1 (by rfl) ⟨370997, by rfl⟩ : syracuseStep 494663 = 741995) B741995
theorem B494815 : Blo 491791 494815 := bstep (se 1 (by rfl) ⟨371111, by rfl⟩ : syracuseStep 494815 = 742223) B742223
theorem B789929 : Blo 491791 789929 := bstep (se 2 (by rfl) ⟨296223, by rfl⟩ : syracuseStep 789929 = 592447) B592447
theorem B495079 : Blo 491791 495079 := bstep (se 1 (by rfl) ⟨371309, by rfl⟩ : syracuseStep 495079 = 742619) B742619
theorem B4492793 : Blo 491791 4492793 := bstep (se 2 (by rfl) ⟨1684797, by rfl⟩ : syracuseStep 4492793 = 3369595) B3369595
theorem B9014777 : Blo 491791 9014777 := bstep (se 2 (by rfl) ⟨3380541, by rfl⟩ : syracuseStep 9014777 = 6761083) B6761083
theorem B2854415 : Blo 491791 2854415 := bstep (se 1 (by rfl) ⟨2140811, by rfl⟩ : syracuseStep 2854415 = 4281623) B4281623
theorem B495195 : Blo 491791 495195 := bstep (se 1 (by rfl) ⟨371396, by rfl⟩ : syracuseStep 495195 = 742793) B742793
theorem B495431 : Blo 491791 495431 := bstep (se 1 (by rfl) ⟨371573, by rfl⟩ : syracuseStep 495431 = 743147) B743147
theorem B2494313 : Blo 491791 2494313 := bstep (se 2 (by rfl) ⟨935367, by rfl⟩ : syracuseStep 2494313 = 1870735) B1870735
theorem B626555 : Blo 491791 626555 := bstep (se 1 (by rfl) ⟨469916, by rfl⟩ : syracuseStep 626555 = 939833) B939833
theorem B495583 : Blo 491791 495583 := bstep (se 1 (by rfl) ⟨371687, by rfl⟩ : syracuseStep 495583 = 743375) B743375
theorem B1282171 : Blo 491791 1282171 := bstep (se 1 (by rfl) ⟨961628, by rfl⟩ : syracuseStep 1282171 = 1923257) B1923257
theorem B594383 : Blo 491791 594383 := bstep (se 1 (by rfl) ⟨445787, by rfl⟩ : syracuseStep 594383 = 891575) B891575
theorem B3740255 : Blo 491791 3740255 := bstep (se 1 (by rfl) ⟨2805191, by rfl⟩ : syracuseStep 3740255 = 5610383) B5610383
theorem B2134717 : Blo 491791 2134717 := bstep (se 3 (by rfl) ⟨400259, by rfl⟩ : syracuseStep 2134717 = 800519) B800519
theorem B1872665 : Blo 491791 1872665 := bstep (se 2 (by rfl) ⟨702249, by rfl⟩ : syracuseStep 1872665 = 1404499) B1404499
theorem B8459315 : Blo 491791 8459315 := bstep (se 1 (by rfl) ⟨6344486, by rfl⟩ : syracuseStep 8459315 = 12688973) B12688973
theorem B1250579 : Blo 491791 1250579 := bstep (se 1 (by rfl) ⟨937934, by rfl⟩ : syracuseStep 1250579 = 1875869) B1875869
theorem B1775047 : Blo 491791 1775047 := bstep (se 1 (by rfl) ⟨1331285, by rfl⟩ : syracuseStep 1775047 = 2662571) B2662571
theorem B1775105 : Blo 491791 1775105 := bstep (se 2 (by rfl) ⟨665664, by rfl⟩ : syracuseStep 1775105 = 1331329) B1331329
theorem B890551 : Blo 491791 890551 := bstep (se 1 (by rfl) ⟨667913, by rfl⟩ : syracuseStep 890551 = 1335827) B1335827
theorem B5347457 : Blo 491791 5347457 := bstep (se 2 (by rfl) ⟨2005296, by rfl⟩ : syracuseStep 5347457 = 4010593) B4010593
theorem B1579151 : Blo 491791 1579151 := bstep (se 1 (by rfl) ⟨1184363, by rfl⟩ : syracuseStep 1579151 = 2368727) B2368727
theorem B792767 : Blo 491791 792767 := bstep (se 1 (by rfl) ⟨594575, by rfl⟩ : syracuseStep 792767 = 1189151) B1189151
theorem B1251571 : Blo 491791 1251571 := bstep (se 1 (by rfl) ⟨938678, by rfl⟩ : syracuseStep 1251571 = 1877357) B1877357
theorem B5347625 : Blo 491791 5347625 := bstep (se 2 (by rfl) ⟨2005359, by rfl⟩ : syracuseStep 5347625 = 4010719) B4010719
theorem B3152357 : Blo 491791 3152357 := bstep (se 4 (by rfl) ⟨295533, by rfl⟩ : syracuseStep 3152357 = 591067) B591067
theorem B2104289 : Blo 491791 2104289 := bstep (se 2 (by rfl) ⟨789108, by rfl⟩ : syracuseStep 2104289 = 1578217) B1578217
theorem B8101043 : Blo 491791 8101043 := bstep (se 1 (by rfl) ⟨6075782, by rfl⟩ : syracuseStep 8101043 = 12151565) B12151565
theorem B2563489 : Blo 491791 2563489 := bstep (se 2 (by rfl) ⟨961308, by rfl⟩ : syracuseStep 2563489 = 1922617) B1922617
theorem B1580791 : Blo 491791 1580791 := bstep (se 1 (by rfl) ⟨1185593, by rfl⟩ : syracuseStep 1580791 = 2371187) B2371187
theorem B1253191 : Blo 491791 1253191 := bstep (se 1 (by rfl) ⟨939893, by rfl⟩ : syracuseStep 1253191 = 1879787) B1879787
theorem B1581191 : Blo 491791 1581191 := bstep (se 1 (by rfl) ⟨1185893, by rfl⟩ : syracuseStep 1581191 = 2371787) B2371787
theorem B4235399 : Blo 491791 4235399 := bstep (se 1 (by rfl) ⟨3176549, by rfl⟩ : syracuseStep 4235399 = 6353099) B6353099
theorem B1253515 : Blo 491791 1253515 := bstep (se 1 (by rfl) ⟨940136, by rfl⟩ : syracuseStep 1253515 = 1880273) B1880273
theorem B4202867 : Blo 491791 4202867 := bstep (se 1 (by rfl) ⟨3152150, by rfl⟩ : syracuseStep 4202867 = 6304301) B6304301
theorem B1253819 : Blo 491791 1253819 := bstep (se 1 (by rfl) ⟨940364, by rfl⟩ : syracuseStep 1253819 = 1880729) B1880729
theorem B1253839 : Blo 491791 1253839 := bstep (se 1 (by rfl) ⟨940379, by rfl⟩ : syracuseStep 1253839 = 1880759) B1880759
theorem B1876553 : Blo 491791 1876553 := bstep (se 2 (by rfl) ⟨703707, by rfl⟩ : syracuseStep 1876553 = 1407415) B1407415
theorem B6333005 : Blo 491791 6333005 := bstep (se 3 (by rfl) ⟨1187438, by rfl⟩ : syracuseStep 6333005 = 2374877) B2374877
theorem B42869573 : Blo 491791 42869573 := bstep (se 4 (by rfl) ⟨4019022, by rfl⟩ : syracuseStep 42869573 = 8038045) B8038045
theorem B861257 : Blo 491791 861257 := bstep (se 2 (by rfl) ⟨322971, by rfl⟩ : syracuseStep 861257 = 645943) B645943
theorem B9151987 : Blo 491791 9151987 := bstep (se 1 (by rfl) ⟨6863990, by rfl⟩ : syracuseStep 9151987 = 13727981) B13727981
theorem B632539 : Blo 491791 632539 := bstep (se 1 (by rfl) ⟨474404, by rfl⟩ : syracuseStep 632539 = 948809) B948809
theorem B501499 : Blo 491791 501499 := bstep (se 1 (by rfl) ⟨376124, by rfl⟩ : syracuseStep 501499 = 752249) B752249
theorem B501535 : Blo 491791 501535 := bstep (se 1 (by rfl) ⟨376151, by rfl⟩ : syracuseStep 501535 = 752303) B752303
theorem B10692485 : Blo 491791 10692485 := bstep (se 4 (by rfl) ⟨1002420, by rfl⟩ : syracuseStep 10692485 = 2004841) B2004841
theorem B3156047 : Blo 491791 3156047 := bstep (se 1 (by rfl) ⟨2367035, by rfl⟩ : syracuseStep 3156047 = 4734071) B4734071
theorem B1878329 : Blo 491791 1878329 := bstep (se 2 (by rfl) ⟨704373, by rfl⟩ : syracuseStep 1878329 = 1408747) B1408747
theorem B83143361 : Blo 491791 83143361 := bstep (se 2 (by rfl) ⟨31178760, by rfl⟩ : syracuseStep 83143361 = 62357521) B62357521
theorem B830263 : Blo 491791 830263 := bstep (se 1 (by rfl) ⟨622697, by rfl⟩ : syracuseStep 830263 = 1245395) B1245395
theorem B2993249 : Blo 491791 2993249 := bstep (se 2 (by rfl) ⟨1122468, by rfl⟩ : syracuseStep 2993249 = 2244937) B2244937
theorem B2403425 : Blo 491791 2403425 := bstep (se 2 (by rfl) ⟨901284, by rfl⟩ : syracuseStep 2403425 = 1802569) B1802569
theorem B830729 : Blo 491791 830729 := bstep (se 2 (by rfl) ⟨311523, by rfl⟩ : syracuseStep 830729 = 623047) B623047
theorem B4272095 : Blo 491791 4272095 := bstep (se 1 (by rfl) ⟨3204071, by rfl⟩ : syracuseStep 4272095 = 6408143) B6408143
theorem B8335523 : Blo 491791 8335523 := bstep (se 1 (by rfl) ⟨6251642, by rfl⟩ : syracuseStep 8335523 = 12503285) B12503285
theorem B2109635 : Blo 491791 2109635 := bstep (se 1 (by rfl) ⟨1582226, by rfl⟩ : syracuseStep 2109635 = 3164453) B3164453
theorem B831775 : Blo 491791 831775 := bstep (se 1 (by rfl) ⟨623831, by rfl⟩ : syracuseStep 831775 = 1247663) B1247663
theorem B2994661 : Blo 491791 2994661 := bstep (se 4 (by rfl) ⟨280749, by rfl⟩ : syracuseStep 2994661 = 561499) B561499
theorem B2372111 : Blo 491791 2372111 := bstep (se 1 (by rfl) ⟨1779083, by rfl⟩ : syracuseStep 2372111 = 3558167) B3558167
theorem B832423 : Blo 491791 832423 := bstep (se 1 (by rfl) ⟨624317, by rfl⟩ : syracuseStep 832423 = 1248635) B1248635
theorem B11973689 : Blo 491791 11973689 := bstep (se 2 (by rfl) ⟨4490133, by rfl⟩ : syracuseStep 11973689 = 8980267) B8980267
theorem B832585 : Blo 491791 832585 := bstep (se 2 (by rfl) ⟨312219, by rfl⟩ : syracuseStep 832585 = 624439) B624439
theorem B832619 : Blo 491791 832619 := bstep (se 1 (by rfl) ⟨624464, by rfl⟩ : syracuseStep 832619 = 1248929) B1248929
theorem B3749003 : Blo 491791 3749003 := bstep (se 1 (by rfl) ⟨2811752, by rfl⟩ : syracuseStep 3749003 = 5623505) B5623505
theorem B8566361 : Blo 491791 8566361 := bstep (se 2 (by rfl) ⟨3212385, by rfl⟩ : syracuseStep 8566361 = 6424771) B6424771
theorem B2373533 : Blo 491791 2373533 := bstep (se 3 (by rfl) ⟨445037, by rfl⟩ : syracuseStep 2373533 = 890075) B890075
theorem B3160147 : Blo 491791 3160147 := bstep (se 1 (by rfl) ⟨2370110, by rfl⟩ : syracuseStep 3160147 = 4740221) B4740221
theorem B1882217 : Blo 491791 1882217 := bstep (se 2 (by rfl) ⟨705831, by rfl⟩ : syracuseStep 1882217 = 1411663) B1411663
theorem B833915 : Blo 491791 833915 := bstep (se 1 (by rfl) ⟨625436, by rfl⟩ : syracuseStep 833915 = 1250873) B1250873
theorem B834185 : Blo 491791 834185 := bstep (se 2 (by rfl) ⟨312819, by rfl⟩ : syracuseStep 834185 = 625639) B625639
theorem B1587865 : Blo 491791 1587865 := bstep (se 2 (by rfl) ⟨595449, by rfl⟩ : syracuseStep 1587865 = 1190899) B1190899
theorem B2505977 : Blo 491791 2505977 := bstep (se 2 (by rfl) ⟨939741, by rfl⟩ : syracuseStep 2505977 = 1879483) B1879483
theorem B5619131 : Blo 491791 5619131 := bstep (se 1 (by rfl) ⟨4214348, by rfl⟩ : syracuseStep 5619131 = 8428697) B8428697
theorem B9519191 : Blo 491791 9519191 := bstep (se 1 (by rfl) ⟨7139393, by rfl⟩ : syracuseStep 9519191 = 14278787) B14278787
theorem B835771 : Blo 491791 835771 := bstep (se 1 (by rfl) ⟨626828, by rfl⟩ : syracuseStep 835771 = 1253657) B1253657
theorem B835967 : Blo 491791 835967 := bstep (se 1 (by rfl) ⟨626975, by rfl⟩ : syracuseStep 835967 = 1253951) B1253951
theorem B737735 : Blo 491791 737735 := bstep (se 1 (by rfl) ⟨553301, by rfl⟩ : syracuseStep 737735 = 1106603) B1106603
theorem B738089 : Blo 491791 738089 := bstep (se 2 (by rfl) ⟨276783, by rfl⟩ : syracuseStep 738089 = 553567) B553567
theorem B738095 : Blo 491791 738095 := bstep (se 1 (by rfl) ⟨553571, by rfl⟩ : syracuseStep 738095 = 1107143) B1107143
theorem B836399 : Blo 491791 836399 := bstep (se 1 (by rfl) ⟨627299, by rfl⟩ : syracuseStep 836399 = 1254599) B1254599
theorem B738215 : Blo 491791 738215 := bstep (se 1 (by rfl) ⟨553661, by rfl⟩ : syracuseStep 738215 = 1107323) B1107323
theorem B738299 : Blo 491791 738299 := bstep (se 1 (by rfl) ⟨553724, by rfl⟩ : syracuseStep 738299 = 1107449) B1107449
theorem B738359 : Blo 491791 738359 := bstep (se 1 (by rfl) ⟨553769, by rfl⟩ : syracuseStep 738359 = 1107539) B1107539
theorem B738479 : Blo 491791 738479 := bstep (se 1 (by rfl) ⟨553859, by rfl⟩ : syracuseStep 738479 = 1107719) B1107719
theorem B3753377 : Blo 491791 3753377 := bstep (se 2 (by rfl) ⟨1407516, by rfl⟩ : syracuseStep 3753377 = 2815033) B2815033
theorem B738887 : Blo 491791 738887 := bstep (se 1 (by rfl) ⟨554165, by rfl⟩ : syracuseStep 738887 = 1108331) B1108331
theorem B2246255 : Blo 491791 2246255 := bstep (se 1 (by rfl) ⟨1684691, by rfl⟩ : syracuseStep 2246255 = 3369383) B3369383
theorem B738983 : Blo 491791 738983 := bstep (se 1 (by rfl) ⟨554237, by rfl⟩ : syracuseStep 738983 = 1108475) B1108475
theorem B1197787 : Blo 491791 1197787 := bstep (se 1 (by rfl) ⟨898340, by rfl⟩ : syracuseStep 1197787 = 1796681) B1796681
theorem B7096031 : Blo 491791 7096031 := bstep (se 1 (by rfl) ⟨5322023, by rfl⟩ : syracuseStep 7096031 = 10644047) B10644047
theorem B739067 : Blo 491791 739067 := bstep (se 1 (by rfl) ⟨554300, by rfl⟩ : syracuseStep 739067 = 1108601) B1108601
theorem B739103 : Blo 491791 739103 := bstep (se 1 (by rfl) ⟨554327, by rfl⟩ : syracuseStep 739103 = 1108655) B1108655
theorem B1918799 : Blo 491791 1918799 := bstep (se 1 (by rfl) ⟨1439099, by rfl⟩ : syracuseStep 1918799 = 2878199) B2878199
theorem B739151 : Blo 491791 739151 := bstep (se 1 (by rfl) ⟨554363, by rfl⟩ : syracuseStep 739151 = 1108727) B1108727
theorem B739271 : Blo 491791 739271 := bstep (se 1 (by rfl) ⟨554453, by rfl⟩ : syracuseStep 739271 = 1108907) B1108907
theorem B936127 : Blo 491791 936127 := bstep (se 1 (by rfl) ⟨702095, by rfl⟩ : syracuseStep 936127 = 1404191) B1404191
theorem B2377937 : Blo 491791 2377937 := bstep (se 2 (by rfl) ⟨891726, by rfl⟩ : syracuseStep 2377937 = 1783453) B1783453
theorem B739625 : Blo 491791 739625 := bstep (se 2 (by rfl) ⟨277359, by rfl⟩ : syracuseStep 739625 = 554719) B554719
theorem B739631 : Blo 491791 739631 := bstep (se 1 (by rfl) ⟨554723, by rfl⟩ : syracuseStep 739631 = 1109447) B1109447
theorem B3164507 : Blo 491791 3164507 := bstep (se 1 (by rfl) ⟨2373380, by rfl⟩ : syracuseStep 3164507 = 4746761) B4746761
theorem B2738657 : Blo 491791 2738657 := bstep (se 2 (by rfl) ⟨1026996, by rfl⟩ : syracuseStep 2738657 = 2053993) B2053993
theorem B9521651 : Blo 491791 9521651 := bstep (se 1 (by rfl) ⟨7141238, by rfl⟩ : syracuseStep 9521651 = 14282477) B14282477
theorem B4213255 : Blo 491791 4213255 := bstep (se 1 (by rfl) ⟨3159941, by rfl⟩ : syracuseStep 4213255 = 6319883) B6319883
theorem B739871 : Blo 491791 739871 := bstep (se 1 (by rfl) ⟨554903, by rfl⟩ : syracuseStep 739871 = 1109807) B1109807
theorem B740255 : Blo 491791 740255 := bstep (se 1 (by rfl) ⟨555191, by rfl⟩ : syracuseStep 740255 = 1110383) B1110383
theorem B740303 : Blo 491791 740303 := bstep (se 1 (by rfl) ⟨555227, by rfl⟩ : syracuseStep 740303 = 1110455) B1110455
theorem B6343667 : Blo 491791 6343667 := bstep (se 1 (by rfl) ⟨4757750, by rfl⟩ : syracuseStep 6343667 = 9515501) B9515501
theorem B740393 : Blo 491791 740393 := bstep (se 2 (by rfl) ⟨277647, by rfl⟩ : syracuseStep 740393 = 555295) B555295
theorem B740399 : Blo 491791 740399 := bstep (se 1 (by rfl) ⟨555299, by rfl⟩ : syracuseStep 740399 = 1110599) B1110599
theorem B740423 : Blo 491791 740423 := bstep (se 1 (by rfl) ⟨555317, by rfl⟩ : syracuseStep 740423 = 1110635) B1110635
theorem B937183 : Blo 491791 937183 := bstep (se 1 (by rfl) ⟨702887, by rfl⟩ : syracuseStep 937183 = 1405775) B1405775
theorem B740687 : Blo 491791 740687 := bstep (se 1 (by rfl) ⟨555515, by rfl⟩ : syracuseStep 740687 = 1111031) B1111031
theorem B5328251 : Blo 491791 5328251 := bstep (se 1 (by rfl) ⟨3996188, by rfl⟩ : syracuseStep 5328251 = 7992377) B7992377
theorem B740777 : Blo 491791 740777 := bstep (se 2 (by rfl) ⟨277791, by rfl⟩ : syracuseStep 740777 = 555583) B555583
theorem B1330615 : Blo 491791 1330615 := bstep (se 1 (by rfl) ⟨997961, by rfl⟩ : syracuseStep 1330615 = 1995923) B1995923
theorem B1527229 : Blo 491791 1527229 := bstep (se 3 (by rfl) ⟨286355, by rfl⟩ : syracuseStep 1527229 = 572711) B572711
theorem B1330679 : Blo 491791 1330679 := bstep (se 1 (by rfl) ⟨998009, by rfl⟩ : syracuseStep 1330679 = 1996019) B1996019
theorem B740927 : Blo 491791 740927 := bstep (se 1 (by rfl) ⟨555695, by rfl⟩ : syracuseStep 740927 = 1111391) B1111391
theorem B741191 : Blo 491791 741191 := bstep (se 1 (by rfl) ⟨555893, by rfl⟩ : syracuseStep 741191 = 1111787) B1111787
theorem B741275 : Blo 491791 741275 := bstep (se 1 (by rfl) ⟨555956, by rfl⟩ : syracuseStep 741275 = 1111913) B1111913
theorem B7721249 : Blo 491791 7721249 := bstep (se 2 (by rfl) ⟨2895468, by rfl⟩ : syracuseStep 7721249 = 5790937) B5790937
theorem B10309963 : Blo 491791 10309963 := bstep (se 1 (by rfl) ⟨7732472, by rfl⟩ : syracuseStep 10309963 = 15464945) B15464945
theorem B741839 : Blo 491791 741839 := bstep (se 1 (by rfl) ⟨556379, by rfl⟩ : syracuseStep 741839 = 1112759) B1112759
theorem B741881 : Blo 491791 741881 := bstep (se 2 (by rfl) ⟨278205, by rfl⟩ : syracuseStep 741881 = 556411) B556411
theorem B1331795 : Blo 491791 1331795 := bstep (se 1 (by rfl) ⟨998846, by rfl⟩ : syracuseStep 1331795 = 1997693) B1997693
theorem B741983 : Blo 491791 741983 := bstep (se 1 (by rfl) ⟨556487, by rfl⟩ : syracuseStep 741983 = 1112975) B1112975
theorem B6771377 : Blo 491791 6771377 := bstep (se 2 (by rfl) ⟨2539266, by rfl⟩ : syracuseStep 6771377 = 5078533) B5078533
theorem B7132013 : Blo 491791 7132013 := bstep (se 3 (by rfl) ⟨1337252, by rfl⟩ : syracuseStep 7132013 = 2674505) B2674505
theorem B3167171 : Blo 491791 3167171 := bstep (se 1 (by rfl) ⟨2375378, by rfl⟩ : syracuseStep 3167171 = 4750757) B4750757
theorem B1659959 : Blo 491791 1659959 := bstep (se 1 (by rfl) ⟨1244969, by rfl⟩ : syracuseStep 1659959 = 2489939) B2489939
theorem B742463 : Blo 491791 742463 := bstep (se 1 (by rfl) ⟨556847, by rfl⟩ : syracuseStep 742463 = 1113695) B1113695
theorem B742505 : Blo 491791 742505 := bstep (se 2 (by rfl) ⟨278439, by rfl⟩ : syracuseStep 742505 = 556879) B556879
theorem B742607 : Blo 491791 742607 := bstep (se 1 (by rfl) ⟨556955, by rfl⟩ : syracuseStep 742607 = 1113911) B1113911
theorem B742811 : Blo 491791 742811 := bstep (se 1 (by rfl) ⟨557108, by rfl⟩ : syracuseStep 742811 = 1114217) B1114217
theorem B1496519 : Blo 491791 1496519 := bstep (se 1 (by rfl) ⟨1122389, by rfl⟩ : syracuseStep 1496519 = 2244779) B2244779
theorem B743033 : Blo 491791 743033 := bstep (se 2 (by rfl) ⟨278637, by rfl⟩ : syracuseStep 743033 = 557275) B557275
theorem B743135 : Blo 491791 743135 := bstep (se 1 (by rfl) ⟨557351, by rfl⟩ : syracuseStep 743135 = 1114703) B1114703
theorem B1267451 : Blo 491791 1267451 := bstep (se 1 (by rfl) ⟨950588, by rfl⟩ : syracuseStep 1267451 = 1901177) B1901177
theorem B743231 : Blo 491791 743231 := bstep (se 1 (by rfl) ⟨557423, by rfl⟩ : syracuseStep 743231 = 1114847) B1114847
theorem B743399 : Blo 491791 743399 := bstep (se 1 (by rfl) ⟨557549, by rfl⟩ : syracuseStep 743399 = 1115099) B1115099
theorem B940015 : Blo 491791 940015 := bstep (se 1 (by rfl) ⟨705011, by rfl⟩ : syracuseStep 940015 = 1410023) B1410023
theorem B743417 : Blo 491791 743417 := bstep (se 2 (by rfl) ⟨278781, by rfl⟩ : syracuseStep 743417 = 557563) B557563
theorem B743519 : Blo 491791 743519 := bstep (se 1 (by rfl) ⟨557639, by rfl⟩ : syracuseStep 743519 = 1115279) B1115279
theorem B743579 : Blo 491791 743579 := bstep (se 1 (by rfl) ⟨557684, by rfl⟩ : syracuseStep 743579 = 1115369) B1115369
theorem B743615 : Blo 491791 743615 := bstep (se 1 (by rfl) ⟨557711, by rfl⟩ : syracuseStep 743615 = 1115423) B1115423
theorem B743657 : Blo 491791 743657 := bstep (se 2 (by rfl) ⟨278871, by rfl⟩ : syracuseStep 743657 = 557743) B557743
theorem B6773021 : Blo 491791 6773021 := bstep (se 3 (by rfl) ⟨1269941, by rfl⟩ : syracuseStep 6773021 = 2539883) B2539883
theorem B3168553 : Blo 491791 3168553 := bstep (se 2 (by rfl) ⟨1188207, by rfl⟩ : syracuseStep 3168553 = 2376415) B2376415
theorem B2808701 : Blo 491791 2808701 := bstep (se 3 (by rfl) ⟨526631, by rfl⟩ : syracuseStep 2808701 = 1053263) B1053263
theorem B1661903 : Blo 491791 1661903 := bstep (se 1 (by rfl) ⟨1246427, by rfl⟩ : syracuseStep 1661903 = 2492855) B2492855
theorem B1694969 : Blo 491791 1694969 := bstep (se 2 (by rfl) ⟨635613, by rfl⟩ : syracuseStep 1694969 = 1271227) B1271227
theorem B13491521 : Blo 491791 13491521 := bstep (se 2 (by rfl) ⟨5059320, by rfl⟩ : syracuseStep 13491521 = 10118641) B10118641
theorem B3169631 : Blo 491791 3169631 := bstep (se 1 (by rfl) ⟨2377223, by rfl⟩ : syracuseStep 3169631 = 4754447) B4754447
theorem B3661615 : Blo 491791 3661615 := bstep (se 1 (by rfl) ⟨2746211, by rfl⟩ : syracuseStep 3661615 = 5492423) B5492423
theorem B2023643 : Blo 491791 2023643 := bstep (se 1 (by rfl) ⟨1517732, by rfl⟩ : syracuseStep 2023643 = 3035465) B3035465
theorem B1663415 : Blo 491791 1663415 := bstep (se 1 (by rfl) ⟨1247561, by rfl⟩ : syracuseStep 1663415 = 2495123) B2495123
theorem B1401275 : Blo 491791 1401275 := bstep (se 1 (by rfl) ⟨1050956, by rfl⟩ : syracuseStep 1401275 = 2101913) B2101913
theorem B15196673 : Blo 491791 15196673 := bstep (se 2 (by rfl) ⟨5698752, by rfl⟩ : syracuseStep 15196673 = 11397505) B11397505
theorem B2810477 : Blo 491791 2810477 := bstep (se 3 (by rfl) ⟨526964, by rfl⟩ : syracuseStep 2810477 = 1053929) B1053929
theorem B5137181 : Blo 491791 5137181 := bstep (se 3 (by rfl) ⟨963221, by rfl⟩ : syracuseStep 5137181 = 1926443) B1926443
theorem B10969901 : Blo 491791 10969901 := bstep (se 3 (by rfl) ⟨2056856, by rfl⟩ : syracuseStep 10969901 = 4113713) B4113713
theorem B1663901 : Blo 491791 1663901 := bstep (se 3 (by rfl) ⟨311981, by rfl⟩ : syracuseStep 1663901 = 623963) B623963
theorem B1106855 : Blo 491791 1106855 := bstep (se 1 (by rfl) ⟨830141, by rfl⟩ : syracuseStep 1106855 = 1660283) B1660283
theorem B1663955 : Blo 491791 1663955 := bstep (se 1 (by rfl) ⟨1247966, by rfl⟩ : syracuseStep 1663955 = 2495933) B2495933
theorem B1107791 : Blo 491791 1107791 := bstep (se 1 (by rfl) ⟨830843, by rfl⟩ : syracuseStep 1107791 = 1661687) B1661687
theorem B1107809 : Blo 491791 1107809 := bstep (se 2 (by rfl) ⟨415428, by rfl⟩ : syracuseStep 1107809 = 830857) B830857
theorem B1108385 : Blo 491791 1108385 := bstep (se 2 (by rfl) ⟨415644, by rfl⟩ : syracuseStep 1108385 = 831289) B831289
theorem B1108511 : Blo 491791 1108511 := bstep (se 1 (by rfl) ⟨831383, by rfl⟩ : syracuseStep 1108511 = 1662767) B1662767
theorem B3992267 : Blo 491791 3992267 := bstep (se 1 (by rfl) ⟨2994200, by rfl⟩ : syracuseStep 3992267 = 5988401) B5988401
theorem B1666169 : Blo 491791 1666169 := bstep (se 2 (by rfl) ⟨624813, by rfl⟩ : syracuseStep 1666169 = 1249627) B1249627
theorem B1666493 : Blo 491791 1666493 := bstep (se 3 (by rfl) ⟨312467, by rfl⟩ : syracuseStep 1666493 = 624935) B624935
theorem B1109915 : Blo 491791 1109915 := bstep (se 1 (by rfl) ⟨832436, by rfl⟩ : syracuseStep 1109915 = 1664873) B1664873
theorem B1667195 : Blo 491791 1667195 := bstep (se 1 (by rfl) ⟨1250396, by rfl⟩ : syracuseStep 1667195 = 2500793) B2500793
theorem B1110203 : Blo 491791 1110203 := bstep (se 1 (by rfl) ⟨832652, by rfl⟩ : syracuseStep 1110203 = 1665305) B1665305
theorem B1667357 : Blo 491791 1667357 := bstep (se 3 (by rfl) ⟨312629, by rfl⟩ : syracuseStep 1667357 = 625259) B625259
theorem B1667465 : Blo 491791 1667465 := bstep (se 2 (by rfl) ⟨625299, by rfl⟩ : syracuseStep 1667465 = 1250599) B1250599
theorem B553423 : Blo 491791 553423 := bstep (se 1 (by rfl) ⟨415067, by rfl⟩ : syracuseStep 553423 = 830135) B830135
theorem B1110689 : Blo 491791 1110689 := bstep (se 2 (by rfl) ⟨416508, by rfl⟩ : syracuseStep 1110689 = 833017) B833017
theorem B1111049 : Blo 491791 1111049 := bstep (se 2 (by rfl) ⟨416643, by rfl⟩ : syracuseStep 1111049 = 833287) B833287
theorem B1405991 : Blo 491791 1405991 := bstep (se 1 (by rfl) ⟨1054493, by rfl⟩ : syracuseStep 1405991 = 2108987) B2108987
theorem B1111103 : Blo 491791 1111103 := bstep (se 1 (by rfl) ⟨833327, by rfl⟩ : syracuseStep 1111103 = 1666655) B1666655
theorem B1668383 : Blo 491791 1668383 := bstep (se 1 (by rfl) ⟨1251287, by rfl⟩ : syracuseStep 1668383 = 2502575) B2502575
theorem B554395 : Blo 491791 554395 := bstep (se 1 (by rfl) ⟨415796, by rfl⟩ : syracuseStep 554395 = 831593) B831593
theorem B2815559 : Blo 491791 2815559 := bstep (se 1 (by rfl) ⟨2111669, by rfl⟩ : syracuseStep 2815559 = 4223339) B4223339
theorem B1112039 : Blo 491791 1112039 := bstep (se 1 (by rfl) ⟨834029, by rfl⟩ : syracuseStep 1112039 = 1668059) B1668059
theorem B1112057 : Blo 491791 1112057 := bstep (se 2 (by rfl) ⟨417021, by rfl⟩ : syracuseStep 1112057 = 834043) B834043
theorem B1112147 : Blo 491791 1112147 := bstep (se 1 (by rfl) ⟨834110, by rfl⟩ : syracuseStep 1112147 = 1668221) B1668221
theorem B1112219 : Blo 491791 1112219 := bstep (se 1 (by rfl) ⟨834164, by rfl⟩ : syracuseStep 1112219 = 1668329) B1668329
theorem B1112327 : Blo 491791 1112327 := bstep (se 1 (by rfl) ⟨834245, by rfl⟩ : syracuseStep 1112327 = 1668491) B1668491
theorem B555547 : Blo 491791 555547 := bstep (se 1 (by rfl) ⟨416660, by rfl⟩ : syracuseStep 555547 = 833321) B833321
theorem B1112633 : Blo 491791 1112633 := bstep (se 2 (by rfl) ⟨417237, by rfl⟩ : syracuseStep 1112633 = 834475) B834475
theorem B1604233 : Blo 491791 1604233 := bstep (se 2 (by rfl) ⟨601587, by rfl⟩ : syracuseStep 1604233 = 1203175) B1203175
theorem B3799973 : Blo 491791 3799973 := bstep (se 4 (by rfl) ⟨356247, by rfl⟩ : syracuseStep 3799973 = 712495) B712495
theorem B1670273 : Blo 491791 1670273 := bstep (se 2 (by rfl) ⟨626352, by rfl⟩ : syracuseStep 1670273 = 1252705) B1252705
theorem B1670327 : Blo 491791 1670327 := bstep (se 1 (by rfl) ⟨1252745, by rfl⟩ : syracuseStep 1670327 = 2505491) B2505491
theorem B1113353 : Blo 491791 1113353 := bstep (se 2 (by rfl) ⟨417507, by rfl⟩ : syracuseStep 1113353 = 835015) B835015
theorem B556519 : Blo 491791 556519 := bstep (se 1 (by rfl) ⟨417389, by rfl⟩ : syracuseStep 556519 = 834779) B834779
theorem B1408519 : Blo 491791 1408519 := bstep (se 1 (by rfl) ⟨1056389, by rfl⟩ : syracuseStep 1408519 = 2112779) B2112779
theorem B1080911 : Blo 491791 1080911 := bstep (se 1 (by rfl) ⟨810683, by rfl⟩ : syracuseStep 1080911 = 1621367) B1621367
theorem B4226651 : Blo 491791 4226651 := bstep (se 1 (by rfl) ⟨3169988, by rfl⟩ : syracuseStep 4226651 = 6339977) B6339977
theorem B1867607 : Blo 491791 1867607 := bstep (se 1 (by rfl) ⟨1400705, by rfl⟩ : syracuseStep 1867607 = 2801411) B2801411
theorem B1671083 : Blo 491791 1671083 := bstep (se 1 (by rfl) ⟨1253312, by rfl⟩ : syracuseStep 1671083 = 2506625) B2506625
theorem B557023 : Blo 491791 557023 := bstep (se 1 (by rfl) ⟨417767, by rfl⟩ : syracuseStep 557023 = 835535) B835535
theorem B1671353 : Blo 491791 1671353 := bstep (se 2 (by rfl) ⟨626757, by rfl⟩ : syracuseStep 1671353 = 1253515) B1253515
theorem B1114361 : Blo 491791 1114361 := bstep (se 2 (by rfl) ⟨417885, by rfl⟩ : syracuseStep 1114361 = 835771) B835771
theorem B557311 : Blo 491791 557311 := bstep (se 1 (by rfl) ⟨417983, by rfl⟩ : syracuseStep 557311 = 835967) B835967
theorem B491823 : Blo 491791 491823 := bstep (se 1 (by rfl) ⟨368867, by rfl⟩ : syracuseStep 491823 = 737735) B737735
theorem B1114415 : Blo 491791 1114415 := bstep (se 1 (by rfl) ⟨835811, by rfl⟩ : syracuseStep 1114415 = 1671623) B1671623
theorem B2818475 : Blo 491791 2818475 := bstep (se 1 (by rfl) ⟨2113856, by rfl⟩ : syracuseStep 2818475 = 4227713) B4227713
theorem B1114631 : Blo 491791 1114631 := bstep (se 1 (by rfl) ⟨835973, by rfl⟩ : syracuseStep 1114631 = 1671947) B1671947
theorem B492059 : Blo 491791 492059 := bstep (se 1 (by rfl) ⟨369044, by rfl⟩ : syracuseStep 492059 = 738089) B738089
theorem B492063 : Blo 491791 492063 := bstep (se 1 (by rfl) ⟨369047, by rfl⟩ : syracuseStep 492063 = 738095) B738095
theorem B557599 : Blo 491791 557599 := bstep (se 1 (by rfl) ⟨418199, by rfl⟩ : syracuseStep 557599 = 836399) B836399
theorem B1671785 : Blo 491791 1671785 := bstep (se 2 (by rfl) ⟨626919, by rfl⟩ : syracuseStep 1671785 = 1253839) B1253839
theorem B492143 : Blo 491791 492143 := bstep (se 1 (by rfl) ⟨369107, by rfl⟩ : syracuseStep 492143 = 738215) B738215
theorem B492199 : Blo 491791 492199 := bstep (se 1 (by rfl) ⟨369149, by rfl⟩ : syracuseStep 492199 = 738299) B738299
theorem B1114811 : Blo 491791 1114811 := bstep (se 1 (by rfl) ⟨836108, by rfl⟩ : syracuseStep 1114811 = 1672217) B1672217
theorem B492239 : Blo 491791 492239 := bstep (se 1 (by rfl) ⟨369179, by rfl⟩ : syracuseStep 492239 = 738359) B738359
theorem B492319 : Blo 491791 492319 := bstep (se 1 (by rfl) ⟨369239, by rfl⟩ : syracuseStep 492319 = 738479) B738479
theorem B3736367 : Blo 491791 3736367 := bstep (se 1 (by rfl) ⟨2802275, by rfl⟩ : syracuseStep 3736367 = 5604551) B5604551
theorem B492591 : Blo 491791 492591 := bstep (se 1 (by rfl) ⟨369443, by rfl⟩ : syracuseStep 492591 = 738887) B738887
theorem B1115243 : Blo 491791 1115243 := bstep (se 1 (by rfl) ⟨836432, by rfl⟩ : syracuseStep 1115243 = 1672865) B1672865
theorem B492655 : Blo 491791 492655 := bstep (se 1 (by rfl) ⟨369491, by rfl⟩ : syracuseStep 492655 = 738983) B738983
theorem B492711 : Blo 491791 492711 := bstep (se 1 (by rfl) ⟨369533, by rfl⟩ : syracuseStep 492711 = 739067) B739067
theorem B492735 : Blo 491791 492735 := bstep (se 1 (by rfl) ⟨369551, by rfl⟩ : syracuseStep 492735 = 739103) B739103
theorem B1279199 : Blo 491791 1279199 := bstep (se 1 (by rfl) ⟨959399, by rfl⟩ : syracuseStep 1279199 = 1918799) B1918799
theorem B492767 : Blo 491791 492767 := bstep (se 1 (by rfl) ⟨369575, by rfl⟩ : syracuseStep 492767 = 739151) B739151
theorem B492847 : Blo 491791 492847 := bstep (se 1 (by rfl) ⟨369635, by rfl⟩ : syracuseStep 492847 = 739271) B739271
theorem B493083 : Blo 491791 493083 := bstep (se 1 (by rfl) ⟨369812, by rfl⟩ : syracuseStep 493083 = 739625) B739625
theorem B493087 : Blo 491791 493087 := bstep (se 1 (by rfl) ⟨369815, by rfl⟩ : syracuseStep 493087 = 739631) B739631
theorem B493247 : Blo 491791 493247 := bstep (se 1 (by rfl) ⟨369935, by rfl⟩ : syracuseStep 493247 = 739871) B739871
theorem B1247015 : Blo 491791 1247015 := bstep (se 1 (by rfl) ⟨935261, by rfl⟩ : syracuseStep 1247015 = 1870523) B1870523
theorem B493503 : Blo 491791 493503 := bstep (se 1 (by rfl) ⟨370127, by rfl⟩ : syracuseStep 493503 = 740255) B740255
theorem B493535 : Blo 491791 493535 := bstep (se 1 (by rfl) ⟨370151, by rfl⟩ : syracuseStep 493535 = 740303) B740303
theorem B4229111 : Blo 491791 4229111 := bstep (se 1 (by rfl) ⟨3171833, by rfl⟩ : syracuseStep 4229111 = 6343667) B6343667
theorem B493595 : Blo 491791 493595 := bstep (se 1 (by rfl) ⟨370196, by rfl⟩ : syracuseStep 493595 = 740393) B740393
theorem B493599 : Blo 491791 493599 := bstep (se 1 (by rfl) ⟨370199, by rfl⟩ : syracuseStep 493599 = 740399) B740399
theorem B493615 : Blo 491791 493615 := bstep (se 1 (by rfl) ⟨370211, by rfl⟩ : syracuseStep 493615 = 740423) B740423
theorem B45746369 : Blo 491791 45746369 := bstep (se 2 (by rfl) ⟨17154888, by rfl⟩ : syracuseStep 45746369 = 34309777) B34309777
theorem B493791 : Blo 491791 493791 := bstep (se 1 (by rfl) ⟨370343, by rfl⟩ : syracuseStep 493791 = 740687) B740687
theorem B526619 : Blo 491791 526619 := bstep (se 1 (by rfl) ⟨394964, by rfl⟩ : syracuseStep 526619 = 789929) B789929
theorem B493851 : Blo 491791 493851 := bstep (se 1 (by rfl) ⟨370388, by rfl⟩ : syracuseStep 493851 = 740777) B740777
theorem B887119 : Blo 491791 887119 := bstep (se 1 (by rfl) ⟨665339, by rfl⟩ : syracuseStep 887119 = 1330679) B1330679
theorem B1902943 : Blo 491791 1902943 := bstep (se 1 (by rfl) ⟨1427207, by rfl⟩ : syracuseStep 1902943 = 2854415) B2854415
theorem B493951 : Blo 491791 493951 := bstep (se 1 (by rfl) ⟨370463, by rfl⟩ : syracuseStep 493951 = 740927) B740927
theorem B494127 : Blo 491791 494127 := bstep (se 1 (by rfl) ⟨370595, by rfl⟩ : syracuseStep 494127 = 741191) B741191
theorem B494183 : Blo 491791 494183 := bstep (se 1 (by rfl) ⟨370637, by rfl⟩ : syracuseStep 494183 = 741275) B741275
theorem B1248169 : Blo 491791 1248169 := bstep (se 2 (by rfl) ⟨468063, by rfl⟩ : syracuseStep 1248169 = 936127) B936127
theorem B494559 : Blo 491791 494559 := bstep (se 1 (by rfl) ⟨370919, by rfl⟩ : syracuseStep 494559 = 741839) B741839
theorem B494587 : Blo 491791 494587 := bstep (se 1 (by rfl) ⟨370940, by rfl⟩ : syracuseStep 494587 = 741881) B741881
theorem B887863 : Blo 491791 887863 := bstep (se 1 (by rfl) ⟨665897, by rfl⟩ : syracuseStep 887863 = 1331795) B1331795
theorem B2493503 : Blo 491791 2493503 := bstep (se 1 (by rfl) ⟨1870127, by rfl⟩ : syracuseStep 2493503 = 3740255) B3740255
theorem B494655 : Blo 491791 494655 := bstep (se 1 (by rfl) ⟨370991, by rfl⟩ : syracuseStep 494655 = 741983) B741983
theorem B1248443 : Blo 491791 1248443 := bstep (se 1 (by rfl) ⟨936332, by rfl⟩ : syracuseStep 1248443 = 1872665) B1872665
theorem B4754675 : Blo 491791 4754675 := bstep (se 1 (by rfl) ⟨3566006, by rfl⟩ : syracuseStep 4754675 = 7132013) B7132013
theorem B5639543 : Blo 491791 5639543 := bstep (se 1 (by rfl) ⟨4229657, by rfl⟩ : syracuseStep 5639543 = 8459315) B8459315
theorem B494975 : Blo 491791 494975 := bstep (se 1 (by rfl) ⟨371231, by rfl⟩ : syracuseStep 494975 = 742463) B742463
theorem B495003 : Blo 491791 495003 := bstep (se 1 (by rfl) ⟨371252, by rfl⟩ : syracuseStep 495003 = 742505) B742505
theorem B495071 : Blo 491791 495071 := bstep (se 1 (by rfl) ⟨371303, by rfl⟩ : syracuseStep 495071 = 742607) B742607
theorem B495207 : Blo 491791 495207 := bstep (se 1 (by rfl) ⟨371405, by rfl⟩ : syracuseStep 495207 = 742811) B742811
theorem B1183403 : Blo 491791 1183403 := bstep (se 1 (by rfl) ⟨887552, by rfl⟩ : syracuseStep 1183403 = 1775105) B1775105
theorem B495355 : Blo 491791 495355 := bstep (se 1 (by rfl) ⟨371516, by rfl⟩ : syracuseStep 495355 = 743033) B743033
theorem B495423 : Blo 491791 495423 := bstep (se 1 (by rfl) ⟨371567, by rfl⟩ : syracuseStep 495423 = 743135) B743135
theorem B495487 : Blo 491791 495487 := bstep (se 1 (by rfl) ⟨371615, by rfl⟩ : syracuseStep 495487 = 743231) B743231
theorem B495599 : Blo 491791 495599 := bstep (se 1 (by rfl) ⟨371699, by rfl⟩ : syracuseStep 495599 = 743399) B743399
theorem B495611 : Blo 491791 495611 := bstep (se 1 (by rfl) ⟨371708, by rfl⟩ : syracuseStep 495611 = 743417) B743417
theorem B495679 : Blo 491791 495679 := bstep (se 1 (by rfl) ⟨371759, by rfl⟩ : syracuseStep 495679 = 743519) B743519
theorem B1052767 : Blo 491791 1052767 := bstep (se 1 (by rfl) ⟨789575, by rfl⟩ : syracuseStep 1052767 = 1579151) B1579151
theorem B495719 : Blo 491791 495719 := bstep (se 1 (by rfl) ⟨371789, by rfl⟩ : syracuseStep 495719 = 743579) B743579
theorem B495743 : Blo 491791 495743 := bstep (se 1 (by rfl) ⟨371807, by rfl⟩ : syracuseStep 495743 = 743615) B743615
theorem B495771 : Blo 491791 495771 := bstep (se 1 (by rfl) ⟨371828, by rfl⟩ : syracuseStep 495771 = 743657) B743657
theorem B1249577 : Blo 491791 1249577 := bstep (se 2 (by rfl) ⟨468591, by rfl⟩ : syracuseStep 1249577 = 937183) B937183
theorem B2101571 : Blo 491791 2101571 := bstep (se 1 (by rfl) ⟨1576178, by rfl⟩ : syracuseStep 2101571 = 3152357) B3152357
theorem B1774153 : Blo 491791 1774153 := bstep (se 2 (by rfl) ⟨665307, by rfl⟩ : syracuseStep 1774153 = 1330615) B1330615
theorem B2036305 : Blo 491791 2036305 := bstep (se 2 (by rfl) ⟨763614, by rfl⟩ : syracuseStep 2036305 = 1527229) B1527229
theorem B1872467 : Blo 491791 1872467 := bstep (se 1 (by rfl) ⟨1404350, by rfl⟩ : syracuseStep 1872467 = 2808701) B2808701
theorem B1054127 : Blo 491791 1054127 := bstep (se 1 (by rfl) ⟨790595, by rfl⟩ : syracuseStep 1054127 = 1581191) B1581191
theorem B2823599 : Blo 491791 2823599 := bstep (se 1 (by rfl) ⟨2117699, by rfl⟩ : syracuseStep 2823599 = 4235399) B4235399
theorem B1349095 : Blo 491791 1349095 := bstep (se 1 (by rfl) ⟨1011821, by rfl⟩ : syracuseStep 1349095 = 2023643) B2023643
theorem B1709561 : Blo 491791 1709561 := bstep (se 2 (by rfl) ⟨641085, by rfl⟩ : syracuseStep 1709561 = 1282171) B1282171
theorem B10131115 : Blo 491791 10131115 := bstep (se 1 (by rfl) ⟨7598336, by rfl⟩ : syracuseStep 10131115 = 15196673) B15196673
theorem B1251035 : Blo 491791 1251035 := bstep (se 1 (by rfl) ⟨938276, by rfl⟩ : syracuseStep 1251035 = 1876553) B1876553
theorem B1873651 : Blo 491791 1873651 := bstep (se 1 (by rfl) ⟨1405238, by rfl⟩ : syracuseStep 1873651 = 2810477) B2810477
theorem B7313267 : Blo 491791 7313267 := bstep (se 1 (by rfl) ⟨5484950, by rfl⟩ : syracuseStep 7313267 = 10969901) B10969901
theorem B28579715 : Blo 491791 28579715 := bstep (se 1 (by rfl) ⟨21434786, by rfl⟩ : syracuseStep 28579715 = 42869573) B42869573
theorem B14260333 : Blo 491791 14260333 := bstep (se 3 (by rfl) ⟨2673812, by rfl⟩ : syracuseStep 14260333 = 5347625) B5347625
theorem B2104031 : Blo 491791 2104031 := bstep (se 1 (by rfl) ⟨1578023, by rfl⟩ : syracuseStep 2104031 = 3156047) B3156047
theorem B1252219 : Blo 491791 1252219 := bstep (se 1 (by rfl) ⟨939164, by rfl⟩ : syracuseStep 1252219 = 1878329) B1878329
theorem B2661511 : Blo 491791 2661511 := bstep (se 1 (by rfl) ⟨1996133, by rfl⟩ : syracuseStep 2661511 = 3992267) B3992267
theorem B2366729 : Blo 491791 2366729 := bstep (se 2 (by rfl) ⟨887523, by rfl⟩ : syracuseStep 2366729 = 1775047) B1775047
theorem B1187401 : Blo 491791 1187401 := bstep (se 2 (by rfl) ⟨445275, by rfl⟩ : syracuseStep 1187401 = 890551) B890551
theorem B10133261 : Blo 491791 10133261 := bstep (se 3 (by rfl) ⟨1899986, by rfl⟩ : syracuseStep 10133261 = 3799973) B3799973
theorem B1253353 : Blo 491791 1253353 := bstep (se 2 (by rfl) ⟨470007, by rfl⟩ : syracuseStep 1253353 = 940015) B940015
theorem B1581407 : Blo 491791 1581407 := bstep (se 1 (by rfl) ⟨1186055, by rfl⟩ : syracuseStep 1581407 = 2372111) B2372111
theorem B2499335 : Blo 491791 2499335 := bstep (se 1 (by rfl) ⟨1874501, by rfl⟩ : syracuseStep 2499335 = 3749003) B3749003
theorem B2138977 : Blo 491791 2138977 := bstep (se 2 (by rfl) ⟨802116, by rfl⟩ : syracuseStep 2138977 = 1604233) B1604233
theorem B1877039 : Blo 491791 1877039 := bstep (se 1 (by rfl) ⟨1407779, by rfl⟩ : syracuseStep 1877039 = 2815559) B2815559
theorem B5710907 : Blo 491791 5710907 := bstep (se 1 (by rfl) ⟨4283180, by rfl⟩ : syracuseStep 5710907 = 8566361) B8566361
theorem B1582355 : Blo 491791 1582355 := bstep (se 1 (by rfl) ⟨1186766, by rfl⟩ : syracuseStep 1582355 = 2373533) B2373533
theorem B1254811 : Blo 491791 1254811 := bstep (se 1 (by rfl) ⟨941108, by rfl⟩ : syracuseStep 1254811 = 1882217) B1882217
theorem B3417985 : Blo 491791 3417985 := bstep (se 2 (by rfl) ⟨1281744, by rfl⟩ : syracuseStep 3417985 = 2563489) B2563489
theorem B1878025 : Blo 491791 1878025 := bstep (se 2 (by rfl) ⟨704259, by rfl⟩ : syracuseStep 1878025 = 1408519) B1408519
theorem B3746087 : Blo 491791 3746087 := bstep (se 1 (by rfl) ⟨2809565, by rfl⟩ : syracuseStep 3746087 = 5619131) B5619131
theorem B2107721 : Blo 491791 2107721 := bstep (se 2 (by rfl) ⟨790395, by rfl⟩ : syracuseStep 2107721 = 1580791) B1580791
theorem B7122329 : Blo 491791 7122329 := bstep (se 2 (by rfl) ⟨2670873, by rfl⟩ : syracuseStep 7122329 = 5341747) B5341747
theorem B20589997 : Blo 491791 20589997 := bstep (se 3 (by rfl) ⟨3860624, by rfl⟩ : syracuseStep 20589997 = 7721249) B7721249
theorem B2502251 : Blo 491791 2502251 := bstep (se 1 (by rfl) ⟨1876688, by rfl⟩ : syracuseStep 2502251 = 3753377) B3753377
theorem B4730687 : Blo 491791 4730687 := bstep (se 1 (by rfl) ⟨3548015, by rfl⟩ : syracuseStep 4730687 = 7096031) B7096031
theorem B1585021 : Blo 491791 1585021 := bstep (se 3 (by rfl) ⟨297191, by rfl⟩ : syracuseStep 1585021 = 594383) B594383
theorem B1585291 : Blo 491791 1585291 := bstep (se 1 (by rfl) ⟨1188968, by rfl⟩ : syracuseStep 1585291 = 2377937) B2377937
theorem B2109671 : Blo 491791 2109671 := bstep (se 1 (by rfl) ⟨1582253, by rfl⟩ : syracuseStep 2109671 = 3164507) B3164507
theorem B831721 : Blo 491791 831721 := bstep (se 2 (by rfl) ⟨311895, by rfl⟩ : syracuseStep 831721 = 623791) B623791
theorem B12202649 : Blo 491791 12202649 := bstep (se 2 (by rfl) ⟨4575993, by rfl⟩ : syracuseStep 12202649 = 9151987) B9151987
theorem B3552167 : Blo 491791 3552167 := bstep (se 1 (by rfl) ⟨2664125, by rfl⟩ : syracuseStep 3552167 = 5328251) B5328251
theorem B668665 : Blo 491791 668665 := bstep (se 2 (by rfl) ⟨250749, by rfl⟩ : syracuseStep 668665 = 501499) B501499
theorem B6009851 : Blo 491791 6009851 := bstep (se 1 (by rfl) ⟨4507388, by rfl⟩ : syracuseStep 6009851 = 9014777) B9014777
theorem B15971525 : Blo 491791 15971525 := bstep (se 4 (by rfl) ⟨1497330, by rfl⟩ : syracuseStep 15971525 = 2994661) B2994661
theorem B4764905 : Blo 491791 4764905 := bstep (se 2 (by rfl) ⟨1786839, by rfl⟩ : syracuseStep 4764905 = 3573679) B3573679
theorem B2111447 : Blo 491791 2111447 := bstep (se 1 (by rfl) ⟨1583585, by rfl⟩ : syracuseStep 2111447 = 3167171) B3167171
theorem B5617673 : Blo 491791 5617673 := bstep (se 2 (by rfl) ⟨2106627, by rfl⟩ : syracuseStep 5617673 = 4213255) B4213255
theorem B833719 : Blo 491791 833719 := bstep (se 1 (by rfl) ⟨625289, by rfl⟩ : syracuseStep 833719 = 1250579) B1250579
theorem B997679 : Blo 491791 997679 := bstep (se 1 (by rfl) ⟨748259, by rfl⟩ : syracuseStep 997679 = 1496519) B1496519
theorem B11385157 : Blo 491791 11385157 := bstep (se 4 (by rfl) ⟨1067358, by rfl⟩ : syracuseStep 11385157 = 2134717) B2134717
theorem B834313 : Blo 491791 834313 := bstep (se 2 (by rfl) ⟨312867, by rfl⟩ : syracuseStep 834313 = 625735) B625735
theorem B1129979 : Blo 491791 1129979 := bstep (se 1 (by rfl) ⟨847484, by rfl⟩ : syracuseStep 1129979 = 1694969) B1694969
theorem B8994347 : Blo 491791 8994347 := bstep (se 1 (by rfl) ⟨6745760, by rfl⟩ : syracuseStep 8994347 = 13491521) B13491521
theorem B2113087 : Blo 491791 2113087 := bstep (se 1 (by rfl) ⟨1584815, by rfl⟩ : syracuseStep 2113087 = 3169631) B3169631
theorem B2801911 : Blo 491791 2801911 := bstep (se 1 (by rfl) ⟨2101433, by rfl⟩ : syracuseStep 2801911 = 4202867) B4202867
theorem B934183 : Blo 491791 934183 := bstep (se 1 (by rfl) ⟨700637, by rfl⟩ : syracuseStep 934183 = 1401275) B1401275
theorem B835879 : Blo 491791 835879 := bstep (se 1 (by rfl) ⟨626909, by rfl⟩ : syracuseStep 835879 = 1253819) B1253819
theorem B13746617 : Blo 491791 13746617 := bstep (se 2 (by rfl) ⟨5154981, by rfl⟩ : syracuseStep 13746617 = 10309963) B10309963
theorem B2114045 : Blo 491791 2114045 := bstep (se 3 (by rfl) ⟨396383, by rfl⟩ : syracuseStep 2114045 = 792767) B792767
theorem B3424787 : Blo 491791 3424787 := bstep (se 1 (by rfl) ⟨2568590, by rfl⟩ : syracuseStep 3424787 = 5137181) B5137181
theorem B737897 : Blo 491791 737897 := bstep (se 2 (by rfl) ⟨276711, by rfl⟩ : syracuseStep 737897 = 553423) B553423
theorem B737903 : Blo 491791 737903 := bstep (se 1 (by rfl) ⟨553427, by rfl⟩ : syracuseStep 737903 = 1106855) B1106855
theorem B574171 : Blo 491791 574171 := bstep (se 1 (by rfl) ⟨430628, by rfl⟩ : syracuseStep 574171 = 861257) B861257
theorem B738527 : Blo 491791 738527 := bstep (se 1 (by rfl) ⟨553895, by rfl⟩ : syracuseStep 738527 = 1107791) B1107791
theorem B738539 : Blo 491791 738539 := bstep (se 1 (by rfl) ⟨553904, by rfl⟩ : syracuseStep 738539 = 1107809) B1107809
theorem B7128323 : Blo 491791 7128323 := bstep (se 1 (by rfl) ⟨5346242, by rfl⟩ : syracuseStep 7128323 = 10692485) B10692485
theorem B738923 : Blo 491791 738923 := bstep (se 1 (by rfl) ⟨554192, by rfl⟩ : syracuseStep 738923 = 1108385) B1108385
theorem B739007 : Blo 491791 739007 := bstep (se 1 (by rfl) ⟨554255, by rfl⟩ : syracuseStep 739007 = 1108511) B1108511
theorem B55428907 : Blo 491791 55428907 := bstep (se 1 (by rfl) ⟨41571680, by rfl⟩ : syracuseStep 55428907 = 83143361) B83143361
theorem B739193 : Blo 491791 739193 := bstep (se 2 (by rfl) ⟨277197, by rfl⟩ : syracuseStep 739193 = 554395) B554395
theorem B739943 : Blo 491791 739943 := bstep (se 1 (by rfl) ⟨554957, by rfl⟩ : syracuseStep 739943 = 1109915) B1109915
theorem B5557015 : Blo 491791 5557015 := bstep (se 1 (by rfl) ⟨4167761, by rfl⟩ : syracuseStep 5557015 = 8335523) B8335523
theorem B4213529 : Blo 491791 4213529 := bstep (se 2 (by rfl) ⟨1580073, by rfl⟩ : syracuseStep 4213529 = 3160147) B3160147
theorem B740135 : Blo 491791 740135 := bstep (se 1 (by rfl) ⟨555101, by rfl⟩ : syracuseStep 740135 = 1110203) B1110203
theorem B740459 : Blo 491791 740459 := bstep (se 1 (by rfl) ⟨555344, by rfl⟩ : syracuseStep 740459 = 1110689) B1110689
theorem B740699 : Blo 491791 740699 := bstep (se 1 (by rfl) ⟨555524, by rfl⟩ : syracuseStep 740699 = 1111049) B1111049
theorem B937327 : Blo 491791 937327 := bstep (se 1 (by rfl) ⟨702995, by rfl⟩ : syracuseStep 937327 = 1405991) B1405991
theorem B740729 : Blo 491791 740729 := bstep (se 2 (by rfl) ⟨277773, by rfl⟩ : syracuseStep 740729 = 555547) B555547
theorem B7982459 : Blo 491791 7982459 := bstep (se 1 (by rfl) ⟨5986844, by rfl⟩ : syracuseStep 7982459 = 11973689) B11973689
theorem B740735 : Blo 491791 740735 := bstep (se 1 (by rfl) ⟨555551, by rfl⟩ : syracuseStep 740735 = 1111103) B1111103
theorem B2117153 : Blo 491791 2117153 := bstep (se 2 (by rfl) ⟨793932, by rfl⟩ : syracuseStep 2117153 = 1587865) B1587865
theorem B11980781 : Blo 491791 11980781 := bstep (se 3 (by rfl) ⟨2246396, by rfl⟩ : syracuseStep 11980781 = 4492793) B4492793
theorem B741359 : Blo 491791 741359 := bstep (se 1 (by rfl) ⟨556019, by rfl⟩ : syracuseStep 741359 = 1112039) B1112039
theorem B741371 : Blo 491791 741371 := bstep (se 1 (by rfl) ⟨556028, by rfl⟩ : syracuseStep 741371 = 1112057) B1112057
theorem B741431 : Blo 491791 741431 := bstep (se 1 (by rfl) ⟨556073, by rfl⟩ : syracuseStep 741431 = 1112147) B1112147
theorem B741479 : Blo 491791 741479 := bstep (se 1 (by rfl) ⟨556109, by rfl⟩ : syracuseStep 741479 = 1112219) B1112219
theorem B2674853 : Blo 491791 2674853 := bstep (se 4 (by rfl) ⟨250767, by rfl⟩ : syracuseStep 2674853 = 501535) B501535
theorem B741551 : Blo 491791 741551 := bstep (se 1 (by rfl) ⟨556163, by rfl⟩ : syracuseStep 741551 = 1112327) B1112327
theorem B741755 : Blo 491791 741755 := bstep (se 1 (by rfl) ⟨556316, by rfl⟩ : syracuseStep 741755 = 1112633) B1112633
theorem B742025 : Blo 491791 742025 := bstep (se 2 (by rfl) ⟨278259, by rfl⟩ : syracuseStep 742025 = 556519) B556519
theorem B742235 : Blo 491791 742235 := bstep (se 1 (by rfl) ⟨556676, by rfl⟩ : syracuseStep 742235 = 1113353) B1113353
theorem B742697 : Blo 491791 742697 := bstep (se 2 (by rfl) ⟨278511, by rfl⟩ : syracuseStep 742697 = 557023) B557023
theorem B6346127 : Blo 491791 6346127 := bstep (se 1 (by rfl) ⟨4759595, by rfl⟩ : syracuseStep 6346127 = 9519191) B9519191
theorem B742895 : Blo 491791 742895 := bstep (se 1 (by rfl) ⟨557171, by rfl⟩ : syracuseStep 742895 = 1114343) B1114343
theorem B1660553 : Blo 491791 1660553 := bstep (se 2 (by rfl) ⟨622707, by rfl⟩ : syracuseStep 1660553 = 1245415) B1245415
theorem B743291 : Blo 491791 743291 := bstep (se 1 (by rfl) ⟨557468, by rfl⟩ : syracuseStep 743291 = 1114937) B1114937
theorem B743327 : Blo 491791 743327 := bstep (se 1 (by rfl) ⟨557495, by rfl⟩ : syracuseStep 743327 = 1114991) B1114991
theorem B743561 : Blo 491791 743561 := bstep (se 2 (by rfl) ⟨278835, by rfl⟩ : syracuseStep 743561 = 557671) B557671
theorem B1661147 : Blo 491791 1661147 := bstep (se 1 (by rfl) ⟨1245860, by rfl⟩ : syracuseStep 1661147 = 2491721) B2491721
theorem B940319 : Blo 491791 940319 := bstep (se 1 (by rfl) ⟨705239, by rfl⟩ : syracuseStep 940319 = 1410479) B1410479
theorem B1497503 : Blo 491791 1497503 := bstep (se 1 (by rfl) ⟨1123127, by rfl⟩ : syracuseStep 1497503 = 2246255) B2246255
theorem B1661417 : Blo 491791 1661417 := bstep (se 2 (by rfl) ⟨623031, by rfl⟩ : syracuseStep 1661417 = 1246063) B1246063
theorem B6347767 : Blo 491791 6347767 := bstep (se 1 (by rfl) ⟨4760825, by rfl⟩ : syracuseStep 6347767 = 9521651) B9521651
theorem B1597049 : Blo 491791 1597049 := bstep (se 2 (by rfl) ⟨598893, by rfl⟩ : syracuseStep 1597049 = 1197787) B1197787
theorem B843385 : Blo 491791 843385 := bstep (se 2 (by rfl) ⟨316269, by rfl⟩ : syracuseStep 843385 = 632539) B632539
theorem B1662875 : Blo 491791 1662875 := bstep (se 1 (by rfl) ⟨1247156, by rfl⟩ : syracuseStep 1662875 = 2494313) B2494313
theorem B5333273 : Blo 491791 5333273 := bstep (se 2 (by rfl) ⟨1999977, by rfl⟩ : syracuseStep 5333273 = 3999955) B3999955
theorem B4514251 : Blo 491791 4514251 := bstep (se 1 (by rfl) ⟨3385688, by rfl⟩ : syracuseStep 4514251 = 6771377) B6771377
theorem B1106639 : Blo 491791 1106639 := bstep (se 1 (by rfl) ⟨829979, by rfl⟩ : syracuseStep 1106639 = 1659959) B1659959
theorem B1107017 : Blo 491791 1107017 := bstep (se 2 (by rfl) ⟨415131, by rfl⟩ : syracuseStep 1107017 = 830263) B830263
theorem B844967 : Blo 491791 844967 := bstep (se 1 (by rfl) ⟨633725, by rfl⟩ : syracuseStep 844967 = 1267451) B1267451
theorem B3564971 : Blo 491791 3564971 := bstep (se 1 (by rfl) ⟨2673728, by rfl⟩ : syracuseStep 3564971 = 5347457) B5347457
theorem B4515347 : Blo 491791 4515347 := bstep (se 1 (by rfl) ⟨3386510, by rfl⟩ : syracuseStep 4515347 = 6773021) B6773021
theorem B1107935 : Blo 491791 1107935 := bstep (se 1 (by rfl) ⟨830951, by rfl⟩ : syracuseStep 1107935 = 1661903) B1661903
theorem B1402859 : Blo 491791 1402859 := bstep (se 1 (by rfl) ⟨1052144, by rfl⟩ : syracuseStep 1402859 = 2104289) B2104289
theorem B5400695 : Blo 491791 5400695 := bstep (se 1 (by rfl) ⟨4050521, by rfl⟩ : syracuseStep 5400695 = 8101043) B8101043
theorem B1108943 : Blo 491791 1108943 := bstep (se 1 (by rfl) ⟨831707, by rfl⟩ : syracuseStep 1108943 = 1663415) B1663415
theorem B1109033 : Blo 491791 1109033 := bstep (se 2 (by rfl) ⟨415887, by rfl⟩ : syracuseStep 1109033 = 831775) B831775
theorem B4222003 : Blo 491791 4222003 := bstep (se 1 (by rfl) ⟨3166502, by rfl⟩ : syracuseStep 4222003 = 6333005) B6333005
theorem B1109267 : Blo 491791 1109267 := bstep (se 1 (by rfl) ⟨831950, by rfl⟩ : syracuseStep 1109267 = 1663901) B1663901
theorem B1109303 : Blo 491791 1109303 := bstep (se 1 (by rfl) ⟨831977, by rfl⟩ : syracuseStep 1109303 = 1663955) B1663955
theorem B1109897 : Blo 491791 1109897 := bstep (se 2 (by rfl) ⟨416211, by rfl⟩ : syracuseStep 1109897 = 832423) B832423
theorem B7303085 : Blo 491791 7303085 := bstep (se 3 (by rfl) ⟨1369328, by rfl⟩ : syracuseStep 7303085 = 2738657) B2738657
theorem B1110113 : Blo 491791 1110113 := bstep (se 2 (by rfl) ⟨416292, by rfl⟩ : syracuseStep 1110113 = 832585) B832585
theorem B1995499 : Blo 491791 1995499 := bstep (se 1 (by rfl) ⟨1496624, by rfl⟩ : syracuseStep 1995499 = 2993249) B2993249
theorem B1602283 : Blo 491791 1602283 := bstep (se 1 (by rfl) ⟨1201712, by rfl⟩ : syracuseStep 1602283 = 2403425) B2403425
theorem B1110779 : Blo 491791 1110779 := bstep (se 1 (by rfl) ⟨833084, by rfl⟩ : syracuseStep 1110779 = 1666169) B1666169
theorem B553819 : Blo 491791 553819 := bstep (se 1 (by rfl) ⟨415364, by rfl⟩ : syracuseStep 553819 = 830729) B830729
theorem B1110995 : Blo 491791 1110995 := bstep (se 1 (by rfl) ⟨833246, by rfl⟩ : syracuseStep 1110995 = 1666493) B1666493
theorem B2848063 : Blo 491791 2848063 := bstep (se 1 (by rfl) ⟨2136047, by rfl⟩ : syracuseStep 2848063 = 4272095) B4272095
theorem B1111463 : Blo 491791 1111463 := bstep (se 1 (by rfl) ⟨833597, by rfl⟩ : syracuseStep 1111463 = 1667195) B1667195
theorem B1406423 : Blo 491791 1406423 := bstep (se 1 (by rfl) ⟨1054817, by rfl⟩ : syracuseStep 1406423 = 2109635) B2109635
theorem B1111571 : Blo 491791 1111571 := bstep (se 1 (by rfl) ⟨833678, by rfl⟩ : syracuseStep 1111571 = 1667357) B1667357
theorem B1111643 : Blo 491791 1111643 := bstep (se 1 (by rfl) ⟨833732, by rfl⟩ : syracuseStep 1111643 = 1667465) B1667465
theorem B1668761 : Blo 491791 1668761 := bstep (se 2 (by rfl) ⟨625785, by rfl⟩ : syracuseStep 1668761 = 1251571) B1251571
theorem B4224737 : Blo 491791 4224737 := bstep (se 2 (by rfl) ⟨1584276, by rfl⟩ : syracuseStep 4224737 = 3168553) B3168553
theorem B555079 : Blo 491791 555079 := bstep (se 1 (by rfl) ⟨416309, by rfl⟩ : syracuseStep 555079 = 832619) B832619
theorem B1112255 : Blo 491791 1112255 := bstep (se 1 (by rfl) ⟨834191, by rfl⟩ : syracuseStep 1112255 = 1668383) B1668383
theorem B2882429 : Blo 491791 2882429 := bstep (se 3 (by rfl) ⟨540455, by rfl⟩ : syracuseStep 2882429 = 1080911) B1080911
theorem B19528613 : Blo 491791 19528613 := bstep (se 4 (by rfl) ⟨1830807, by rfl⟩ : syracuseStep 19528613 = 3661615) B3661615
theorem B555943 : Blo 491791 555943 := bstep (se 1 (by rfl) ⟨416957, by rfl⟩ : syracuseStep 555943 = 833915) B833915
theorem B556123 : Blo 491791 556123 := bstep (se 1 (by rfl) ⟨417092, by rfl⟩ : syracuseStep 556123 = 834185) B834185
theorem B1113515 : Blo 491791 1113515 := bstep (se 1 (by rfl) ⟨835136, by rfl⟩ : syracuseStep 1113515 = 1670273) B1670273
theorem B1113551 : Blo 491791 1113551 := bstep (se 1 (by rfl) ⟨835163, by rfl⟩ : syracuseStep 1113551 = 1670327) B1670327
theorem B1670651 : Blo 491791 1670651 := bstep (se 1 (by rfl) ⟨1252988, by rfl⟩ : syracuseStep 1670651 = 2505977) B2505977
theorem B1670813 : Blo 491791 1670813 := bstep (se 3 (by rfl) ⟨313277, by rfl⟩ : syracuseStep 1670813 = 626555) B626555
theorem B2817767 : Blo 491791 2817767 := bstep (se 1 (by rfl) ⟨2113325, by rfl⟩ : syracuseStep 2817767 = 4226651) B4226651
theorem B1670921 : Blo 491791 1670921 := bstep (se 2 (by rfl) ⟨626595, by rfl⟩ : syracuseStep 1670921 = 1253191) B1253191
theorem B1245071 : Blo 491791 1245071 := bstep (se 1 (by rfl) ⟨933803, by rfl⟩ : syracuseStep 1245071 = 1867607) B1867607
theorem B1114055 : Blo 491791 1114055 := bstep (se 1 (by rfl) ⟨835541, by rfl⟩ : syracuseStep 1114055 = 1671083) B1671083
theorem B1114235 : Blo 491791 1114235 := bstep (se 1 (by rfl) ⟨835676, by rfl⟩ : syracuseStep 1114235 = 1671353) B1671353
theorem B3735881 : Blo 491791 3735881 := bstep (se 2 (by rfl) ⟨1400955, by rfl⟩ : syracuseStep 3735881 = 2801911) B2801911
theorem B1409363 : Blo 491791 1409363 := bstep (se 1 (by rfl) ⟨1057022, by rfl⟩ : syracuseStep 1409363 = 2114045) B2114045
theorem B1245577 : Blo 491791 1245577 := bstep (se 2 (by rfl) ⟨467091, by rfl⟩ : syracuseStep 1245577 = 934183) B934183
theorem B1114505 : Blo 491791 1114505 := bstep (se 2 (by rfl) ⟨417939, by rfl⟩ : syracuseStep 1114505 = 835879) B835879
theorem B491931 : Blo 491791 491931 := bstep (se 1 (by rfl) ⟨368948, by rfl⟩ : syracuseStep 491931 = 737897) B737897
theorem B1114523 : Blo 491791 1114523 := bstep (se 1 (by rfl) ⟨835892, by rfl⟩ : syracuseStep 1114523 = 1671785) B1671785
theorem B491935 : Blo 491791 491935 := bstep (se 1 (by rfl) ⟨368951, by rfl⟩ : syracuseStep 491935 = 737903) B737903
theorem B2490911 : Blo 491791 2490911 := bstep (se 1 (by rfl) ⟨1868183, by rfl⟩ : syracuseStep 2490911 = 3736367) B3736367
theorem B492351 : Blo 491791 492351 := bstep (se 1 (by rfl) ⟨369263, by rfl⟩ : syracuseStep 492351 = 738527) B738527
theorem B492359 : Blo 491791 492359 := bstep (se 1 (by rfl) ⟨369269, by rfl⟩ : syracuseStep 492359 = 738539) B738539
theorem B4752215 : Blo 491791 4752215 := bstep (se 1 (by rfl) ⟨3564161, by rfl⟩ : syracuseStep 4752215 = 7128323) B7128323
theorem B492615 : Blo 491791 492615 := bstep (se 1 (by rfl) ⟨369461, by rfl⟩ : syracuseStep 492615 = 738923) B738923
theorem B492671 : Blo 491791 492671 := bstep (se 1 (by rfl) ⟨369503, by rfl⟩ : syracuseStep 492671 = 739007) B739007
theorem B2851969 : Blo 491791 2851969 := bstep (se 2 (by rfl) ⟨1069488, by rfl⟩ : syracuseStep 2851969 = 2138977) B2138977
theorem B492795 : Blo 491791 492795 := bstep (se 1 (by rfl) ⟨369596, by rfl⟩ : syracuseStep 492795 = 739193) B739193
theorem B2819407 : Blo 491791 2819407 := bstep (se 1 (by rfl) ⟨2114555, by rfl⟩ : syracuseStep 2819407 = 4229111) B4229111
theorem B493295 : Blo 491791 493295 := bstep (se 1 (by rfl) ⟨369971, by rfl⟩ : syracuseStep 493295 = 739943) B739943
theorem B493423 : Blo 491791 493423 := bstep (se 1 (by rfl) ⟨370067, by rfl⟩ : syracuseStep 493423 = 740135) B740135
theorem B1673081 : Blo 491791 1673081 := bstep (se 2 (by rfl) ⟨627405, by rfl⟩ : syracuseStep 1673081 = 1254811) B1254811
theorem B493639 : Blo 491791 493639 := bstep (se 1 (by rfl) ⟨370229, by rfl⟩ : syracuseStep 493639 = 740459) B740459
theorem B493799 : Blo 491791 493799 := bstep (se 1 (by rfl) ⟨370349, by rfl⟩ : syracuseStep 493799 = 740699) B740699
theorem B493819 : Blo 491791 493819 := bstep (se 1 (by rfl) ⟨370364, by rfl⟩ : syracuseStep 493819 = 740729) B740729
theorem B493823 : Blo 491791 493823 := bstep (se 1 (by rfl) ⟨370367, by rfl⟩ : syracuseStep 493823 = 740735) B740735
theorem B1411435 : Blo 491791 1411435 := bstep (se 1 (by rfl) ⟨1058576, by rfl⟩ : syracuseStep 1411435 = 2117153) B2117153
theorem B788935 : Blo 491791 788935 := bstep (se 1 (by rfl) ⟨591701, by rfl⟩ : syracuseStep 788935 = 1183403) B1183403
theorem B4557313 : Blo 491791 4557313 := bstep (se 2 (by rfl) ⟨1708992, by rfl⟩ : syracuseStep 4557313 = 3417985) B3417985
theorem B494239 : Blo 491791 494239 := bstep (se 1 (by rfl) ⟨370679, by rfl⟩ : syracuseStep 494239 = 741359) B741359
theorem B494247 : Blo 491791 494247 := bstep (se 1 (by rfl) ⟨370685, by rfl⟩ : syracuseStep 494247 = 741371) B741371
theorem B494287 : Blo 491791 494287 := bstep (se 1 (by rfl) ⟨370715, by rfl⟩ : syracuseStep 494287 = 741431) B741431
theorem B494319 : Blo 491791 494319 := bstep (se 1 (by rfl) ⟨370739, by rfl⟩ : syracuseStep 494319 = 741479) B741479
theorem B494367 : Blo 491791 494367 := bstep (se 1 (by rfl) ⟨370775, by rfl⟩ : syracuseStep 494367 = 741551) B741551
theorem B494503 : Blo 491791 494503 := bstep (se 1 (by rfl) ⟨370877, by rfl⟩ : syracuseStep 494503 = 741755) B741755
theorem B1248311 : Blo 491791 1248311 := bstep (se 1 (by rfl) ⟨936233, by rfl⟩ : syracuseStep 1248311 = 1872467) B1872467
theorem B494683 : Blo 491791 494683 := bstep (se 1 (by rfl) ⟨371012, by rfl⟩ : syracuseStep 494683 = 742025) B742025
theorem B494823 : Blo 491791 494823 := bstep (se 1 (by rfl) ⟨371117, by rfl⟩ : syracuseStep 494823 = 742235) B742235
theorem B3411197 : Blo 491791 3411197 := bstep (se 3 (by rfl) ⟨639599, by rfl⟩ : syracuseStep 3411197 = 1279199) B1279199
theorem B495131 : Blo 491791 495131 := bstep (se 1 (by rfl) ⟨371348, by rfl⟩ : syracuseStep 495131 = 742697) B742697
theorem B4230751 : Blo 491791 4230751 := bstep (se 1 (by rfl) ⟨3173063, by rfl⟩ : syracuseStep 4230751 = 6346127) B6346127
theorem B495263 : Blo 491791 495263 := bstep (se 1 (by rfl) ⟨371447, by rfl⟩ : syracuseStep 495263 = 742895) B742895
theorem B495527 : Blo 491791 495527 := bstep (se 1 (by rfl) ⟨371645, by rfl⟩ : syracuseStep 495527 = 743291) B743291
theorem B495551 : Blo 491791 495551 := bstep (se 1 (by rfl) ⟨371663, by rfl⟩ : syracuseStep 495551 = 743327) B743327
theorem B1183817 : Blo 491791 1183817 := bstep (se 2 (by rfl) ⟨443931, by rfl⟩ : syracuseStep 1183817 = 887863) B887863
theorem B495707 : Blo 491791 495707 := bstep (se 1 (by rfl) ⟨371780, by rfl⟩ : syracuseStep 495707 = 743561) B743561
theorem B626879 : Blo 491791 626879 := bstep (se 1 (by rfl) ⟨470159, by rfl⟩ : syracuseStep 626879 = 940319) B940319
theorem B1249769 : Blo 491791 1249769 := bstep (se 2 (by rfl) ⟨468663, by rfl⟩ : syracuseStep 1249769 = 937327) B937327
theorem B1577819 : Blo 491791 1577819 := bstep (se 1 (by rfl) ⟨1183364, by rfl⟩ : syracuseStep 1577819 = 2366729) B2366729
theorem B19502045 : Blo 491791 19502045 := bstep (se 3 (by rfl) ⟨3656633, by rfl⟩ : syracuseStep 19502045 = 7313267) B7313267
theorem B6755507 : Blo 491791 6755507 := bstep (se 1 (by rfl) ⟨5066630, by rfl⟩ : syracuseStep 6755507 = 10133261) B10133261
theorem B1054271 : Blo 491791 1054271 := bstep (se 1 (by rfl) ⟨790703, by rfl⟩ : syracuseStep 1054271 = 1581407) B1581407
theorem B1251359 : Blo 491791 1251359 := bstep (se 1 (by rfl) ⟨938519, by rfl⟩ : syracuseStep 1251359 = 1877039) B1877039
theorem B3807271 : Blo 491791 3807271 := bstep (se 1 (by rfl) ⟨2855453, by rfl⟩ : syracuseStep 3807271 = 5710907) B5710907
theorem B2365537 : Blo 491791 2365537 := bstep (se 2 (by rfl) ⟨887076, by rfl⟩ : syracuseStep 2365537 = 1774153) B1774153
theorem B563311 : Blo 491791 563311 := bstep (se 1 (by rfl) ⟨422483, by rfl⟩ : syracuseStep 563311 = 844967) B844967
theorem B2136377 : Blo 491791 2136377 := bstep (se 2 (by rfl) ⟨801141, by rfl⟩ : syracuseStep 2136377 = 1602283) B1602283
theorem B2497391 : Blo 491791 2497391 := bstep (se 1 (by rfl) ⟨1873043, by rfl⟩ : syracuseStep 2497391 = 3746087) B3746087
theorem B13508153 : Blo 491791 13508153 := bstep (se 2 (by rfl) ⟨5065557, by rfl⟩ : syracuseStep 13508153 = 10131115) B10131115
theorem B2498201 : Blo 491791 2498201 := bstep (se 2 (by rfl) ⟨936825, by rfl⟩ : syracuseStep 2498201 = 1873651) B1873651
theorem B3153791 : Blo 491791 3153791 := bstep (se 1 (by rfl) ⟨2365343, by rfl⟩ : syracuseStep 3153791 = 4730687) B4730687
theorem B19013777 : Blo 491791 19013777 := bstep (se 2 (by rfl) ⟨7130166, by rfl⟩ : syracuseStep 19013777 = 14260333) B14260333
theorem B15180209 : Blo 491791 15180209 := bstep (se 2 (by rfl) ⟨5692578, by rfl⟩ : syracuseStep 15180209 = 11385157) B11385157
theorem B8135099 : Blo 491791 8135099 := bstep (se 1 (by rfl) ⟨6101324, by rfl⟩ : syracuseStep 8135099 = 12202649) B12202649
theorem B2368111 : Blo 491791 2368111 := bstep (se 1 (by rfl) ⟨1776083, by rfl⟩ : syracuseStep 2368111 = 3552167) B3552167
theorem B4006567 : Blo 491791 4006567 := bstep (se 1 (by rfl) ⟨3004925, by rfl⟩ : syracuseStep 4006567 = 6009851) B6009851
theorem B8463689 : Blo 491791 8463689 := bstep (se 2 (by rfl) ⟨3173883, by rfl⟩ : syracuseStep 8463689 = 6347767) B6347767
theorem B3745115 : Blo 491791 3745115 := bstep (se 1 (by rfl) ⟨2808836, by rfl⟩ : syracuseStep 3745115 = 5617673) B5617673
theorem B3548681 : Blo 491791 3548681 := bstep (se 2 (by rfl) ⟨1330755, by rfl⟩ : syracuseStep 3548681 = 2661511) B2661511
theorem B665119 : Blo 491791 665119 := bstep (se 1 (by rfl) ⟨498839, by rfl⟩ : syracuseStep 665119 = 997679) B997679
theorem B77899573 : Blo 491791 77899573 := bstep (se 5 (by rfl) ⟨3651542, by rfl⟩ : syracuseStep 77899573 = 7303085) B7303085
theorem B13019075 : Blo 491791 13019075 := bstep (se 1 (by rfl) ⟨9764306, by rfl⟩ : syracuseStep 13019075 = 19528613) B19528613
theorem B1583201 : Blo 491791 1583201 := bstep (se 2 (by rfl) ⟨593700, by rfl⟩ : syracuseStep 1583201 = 1187401) B1187401
theorem B1124513 : Blo 491791 1124513 := bstep (se 2 (by rfl) ⟨421692, by rfl⟩ : syracuseStep 1124513 = 843385) B843385
theorem B1878511 : Blo 491791 1878511 := bstep (se 1 (by rfl) ⟨1408883, by rfl⟩ : syracuseStep 1878511 = 2817767) B2817767
theorem B830047 : Blo 491791 830047 := bstep (se 1 (by rfl) ⟨622535, by rfl⟩ : syracuseStep 830047 = 1245071) B1245071
theorem B1878983 : Blo 491791 1878983 := bstep (se 1 (by rfl) ⟨1409237, by rfl⟩ : syracuseStep 1878983 = 2818475) B2818475
theorem B5614757 : Blo 491791 5614757 := bstep (se 4 (by rfl) ⟨526383, by rfl⟩ : syracuseStep 5614757 = 1052767) B1052767
theorem B831343 : Blo 491791 831343 := bstep (se 1 (by rfl) ⟨623507, by rfl⟩ : syracuseStep 831343 = 1247015) B1247015
theorem B4731301 : Blo 491791 4731301 := bstep (se 4 (by rfl) ⟨443559, by rfl⟩ : syracuseStep 4731301 = 887119) B887119
theorem B832295 : Blo 491791 832295 := bstep (se 1 (by rfl) ⟨624221, by rfl⟩ : syracuseStep 832295 = 1248443) B1248443
theorem B5321639 : Blo 491791 5321639 := bstep (se 1 (by rfl) ⟨3991229, by rfl⟩ : syracuseStep 5321639 = 7982459) B7982459
theorem B73905209 : Blo 491791 73905209 := bstep (se 2 (by rfl) ⟨27714453, by rfl⟩ : syracuseStep 73905209 = 55428907) B55428907
theorem B2504033 : Blo 491791 2504033 := bstep (se 2 (by rfl) ⟨939012, by rfl⟩ : syracuseStep 2504033 = 1878025) B1878025
theorem B1783235 : Blo 491791 1783235 := bstep (se 1 (by rfl) ⟨1337426, by rfl⟩ : syracuseStep 1783235 = 2674853) B2674853
theorem B833051 : Blo 491791 833051 := bstep (se 1 (by rfl) ⟨624788, by rfl⟩ : syracuseStep 833051 = 1249577) B1249577
theorem B10860293 : Blo 491791 10860293 := bstep (se 4 (by rfl) ⟨1018152, by rfl⟩ : syracuseStep 10860293 = 2036305) B2036305
theorem B2537257 : Blo 491791 2537257 := bstep (se 2 (by rfl) ⟨951471, by rfl⟩ : syracuseStep 2537257 = 1902943) B1902943
theorem B702751 : Blo 491791 702751 := bstep (se 1 (by rfl) ⟨527063, by rfl⟩ : syracuseStep 702751 = 1054127) B1054127
theorem B1882399 : Blo 491791 1882399 := bstep (se 1 (by rfl) ⟨1411799, by rfl⟩ : syracuseStep 1882399 = 2823599) B2823599
theorem B3062245 : Blo 491791 3062245 := bstep (se 4 (by rfl) ⟨287085, by rfl⟩ : syracuseStep 3062245 = 574171) B574171
theorem B834023 : Blo 491791 834023 := bstep (se 1 (by rfl) ⟨625517, by rfl⟩ : syracuseStep 834023 = 1251035) B1251035
theorem B3750461 : Blo 491791 3750461 := bstep (se 3 (by rfl) ⟨703211, by rfl⟩ : syracuseStep 3750461 = 1406423) B1406423
theorem B19053143 : Blo 491791 19053143 := bstep (se 1 (by rfl) ⟨14289857, by rfl⟩ : syracuseStep 19053143 = 28579715) B28579715
theorem B29637413 : Blo 491791 29637413 := bstep (se 4 (by rfl) ⟨2778507, by rfl⟩ : syracuseStep 29637413 = 5557015) B5557015
theorem B998335 : Blo 491791 998335 := bstep (se 1 (by rfl) ⟨748751, by rfl⟩ : syracuseStep 998335 = 1497503) B1497503
theorem B1064699 : Blo 491791 1064699 := bstep (se 1 (by rfl) ⟨798524, by rfl⟩ : syracuseStep 1064699 = 1597049) B1597049
theorem B2113361 : Blo 491791 2113361 := bstep (se 2 (by rfl) ⟨792510, by rfl⟩ : syracuseStep 2113361 = 1585021) B1585021
theorem B2113721 : Blo 491791 2113721 := bstep (se 2 (by rfl) ⟨792645, by rfl⟩ : syracuseStep 2113721 = 1585291) B1585291
theorem B3555515 : Blo 491791 3555515 := bstep (se 1 (by rfl) ⟨2666636, by rfl⟩ : syracuseStep 3555515 = 5333273) B5333273
theorem B737759 : Blo 491791 737759 := bstep (se 1 (by rfl) ⟨553319, by rfl⟩ : syracuseStep 737759 = 1106639) B1106639
theorem B738011 : Blo 491791 738011 := bstep (se 1 (by rfl) ⟨553508, by rfl⟩ : syracuseStep 738011 = 1107017) B1107017
theorem B5620589 : Blo 491791 5620589 := bstep (se 3 (by rfl) ⟨1053860, by rfl⟩ : syracuseStep 5620589 = 2107721) B2107721
theorem B2376647 : Blo 491791 2376647 := bstep (se 1 (by rfl) ⟨1782485, by rfl⟩ : syracuseStep 2376647 = 3564971) B3564971
theorem B738425 : Blo 491791 738425 := bstep (se 2 (by rfl) ⟨276909, by rfl⟩ : syracuseStep 738425 = 553819) B553819
theorem B738623 : Blo 491791 738623 := bstep (se 1 (by rfl) ⟨553967, by rfl⟩ : syracuseStep 738623 = 1107935) B1107935
theorem B935239 : Blo 491791 935239 := bstep (se 1 (by rfl) ⟨701429, by rfl⟩ : syracuseStep 935239 = 1402859) B1402859
theorem B739295 : Blo 491791 739295 := bstep (se 1 (by rfl) ⟨554471, by rfl⟩ : syracuseStep 739295 = 1108943) B1108943
theorem B739355 : Blo 491791 739355 := bstep (se 1 (by rfl) ⟨554516, by rfl⟩ : syracuseStep 739355 = 1109033) B1109033
theorem B739511 : Blo 491791 739511 := bstep (se 1 (by rfl) ⟨554633, by rfl⟩ : syracuseStep 739511 = 1109267) B1109267
theorem B739535 : Blo 491791 739535 := bstep (se 1 (by rfl) ⟨554651, by rfl⟩ : syracuseStep 739535 = 1109303) B1109303
theorem B739931 : Blo 491791 739931 := bstep (se 1 (by rfl) ⟨554948, by rfl⟩ : syracuseStep 739931 = 1109897) B1109897
theorem B740075 : Blo 491791 740075 := bstep (se 1 (by rfl) ⟨555056, by rfl⟩ : syracuseStep 740075 = 1110113) B1110113
theorem B740105 : Blo 491791 740105 := bstep (se 2 (by rfl) ⟨277539, by rfl⟩ : syracuseStep 740105 = 555079) B555079
theorem B740519 : Blo 491791 740519 := bstep (se 1 (by rfl) ⟨555389, by rfl⟩ : syracuseStep 740519 = 1110779) B1110779
theorem B740663 : Blo 491791 740663 := bstep (se 1 (by rfl) ⟨555497, by rfl⟩ : syracuseStep 740663 = 1110995) B1110995
theorem B740975 : Blo 491791 740975 := bstep (se 1 (by rfl) ⟨555731, by rfl⟩ : syracuseStep 740975 = 1111463) B1111463
theorem B741047 : Blo 491791 741047 := bstep (se 1 (by rfl) ⟨555785, by rfl⟩ : syracuseStep 741047 = 1111571) B1111571
theorem B741095 : Blo 491791 741095 := bstep (se 1 (by rfl) ⟨555821, by rfl⟩ : syracuseStep 741095 = 1111643) B1111643
theorem B741257 : Blo 491791 741257 := bstep (se 2 (by rfl) ⟨277971, by rfl⟩ : syracuseStep 741257 = 555943) B555943
theorem B741497 : Blo 491791 741497 := bstep (se 2 (by rfl) ⟨278061, by rfl⟩ : syracuseStep 741497 = 556123) B556123
theorem B741503 : Blo 491791 741503 := bstep (se 1 (by rfl) ⟨556127, by rfl⟩ : syracuseStep 741503 = 1112255) B1112255
theorem B1921619 : Blo 491791 1921619 := bstep (se 1 (by rfl) ⟨1441214, by rfl⟩ : syracuseStep 1921619 = 2882429) B2882429
theorem B742343 : Blo 491791 742343 := bstep (se 1 (by rfl) ⟨556757, by rfl⟩ : syracuseStep 742343 = 1113515) B1113515
theorem B742367 : Blo 491791 742367 := bstep (se 1 (by rfl) ⟨556775, by rfl⟩ : syracuseStep 742367 = 1113551) B1113551
theorem B742703 : Blo 491791 742703 := bstep (se 1 (by rfl) ⟨557027, by rfl⟩ : syracuseStep 742703 = 1114055) B1114055
theorem B742907 : Blo 491791 742907 := bstep (se 1 (by rfl) ⟨557180, by rfl⟩ : syracuseStep 742907 = 1114361) B1114361
theorem B742943 : Blo 491791 742943 := bstep (se 1 (by rfl) ⟨557207, by rfl⟩ : syracuseStep 742943 = 1114415) B1114415
theorem B9164411 : Blo 491791 9164411 := bstep (se 1 (by rfl) ⟨6873308, by rfl⟩ : syracuseStep 9164411 = 13746617) B13746617
theorem B743081 : Blo 491791 743081 := bstep (se 2 (by rfl) ⟨278655, by rfl⟩ : syracuseStep 743081 = 557311) B557311
theorem B743087 : Blo 491791 743087 := bstep (se 1 (by rfl) ⟨557315, by rfl⟩ : syracuseStep 743087 = 1114631) B1114631
theorem B2283191 : Blo 491791 2283191 := bstep (se 1 (by rfl) ⟨1712393, by rfl⟩ : syracuseStep 2283191 = 3424787) B3424787
theorem B743207 : Blo 491791 743207 := bstep (se 1 (by rfl) ⟨557405, by rfl⟩ : syracuseStep 743207 = 1114811) B1114811
theorem B6019001 : Blo 491791 6019001 := bstep (se 2 (by rfl) ⟨2257125, by rfl⟩ : syracuseStep 6019001 = 4514251) B4514251
theorem B743465 : Blo 491791 743465 := bstep (se 2 (by rfl) ⟨278799, by rfl⟩ : syracuseStep 743465 = 557599) B557599
theorem B743495 : Blo 491791 743495 := bstep (se 1 (by rfl) ⟨557621, by rfl⟩ : syracuseStep 743495 = 1115243) B1115243
theorem B30497579 : Blo 491791 30497579 := bstep (se 1 (by rfl) ⟨22873184, by rfl⟩ : syracuseStep 30497579 = 45746369) B45746369
theorem B2809019 : Blo 491791 2809019 := bstep (se 1 (by rfl) ⟨2106764, by rfl⟩ : syracuseStep 2809019 = 4213529) B4213529
theorem B1662335 : Blo 491791 1662335 := bstep (se 1 (by rfl) ⟨1246751, by rfl⟩ : syracuseStep 1662335 = 2493503) B2493503
theorem B3169783 : Blo 491791 3169783 := bstep (se 1 (by rfl) ⟨2377337, by rfl⟩ : syracuseStep 3169783 = 4754675) B4754675
theorem B3759695 : Blo 491791 3759695 := bstep (se 1 (by rfl) ⟨2819771, by rfl⟩ : syracuseStep 3759695 = 5639543) B5639543
theorem B7987187 : Blo 491791 7987187 := bstep (se 1 (by rfl) ⟨5990390, by rfl⟩ : syracuseStep 7987187 = 11980781) B11980781
theorem B1401047 : Blo 491791 1401047 := bstep (se 1 (by rfl) ⟨1050785, by rfl⟩ : syracuseStep 1401047 = 2101571) B2101571
theorem B4219613 : Blo 491791 4219613 := bstep (se 3 (by rfl) ⟨791177, by rfl⟩ : syracuseStep 4219613 = 1582355) B1582355
theorem B1139707 : Blo 491791 1139707 := bstep (se 1 (by rfl) ⟨854780, by rfl⟩ : syracuseStep 1139707 = 1709561) B1709561
theorem B1107035 : Blo 491791 1107035 := bstep (se 1 (by rfl) ⟨830276, by rfl⟩ : syracuseStep 1107035 = 1660553) B1660553
theorem B1664225 : Blo 491791 1664225 := bstep (se 2 (by rfl) ⟨624084, by rfl⟩ : syracuseStep 1664225 = 1248169) B1248169
theorem B10642661 : Blo 491791 10642661 := bstep (se 4 (by rfl) ⟨997749, by rfl⟩ : syracuseStep 10642661 = 1995499) B1995499
theorem B5629337 : Blo 491791 5629337 := bstep (se 2 (by rfl) ⟨2111001, by rfl⟩ : syracuseStep 5629337 = 4222003) B4222003
theorem B1107431 : Blo 491791 1107431 := bstep (se 1 (by rfl) ⟨830573, by rfl⟩ : syracuseStep 1107431 = 1661147) B1661147
theorem B1107611 : Blo 491791 1107611 := bstep (se 1 (by rfl) ⟨830708, by rfl⟩ : syracuseStep 1107611 = 1661417) B1661417
theorem B1402687 : Blo 491791 1402687 := bstep (se 1 (by rfl) ⟨1052015, by rfl⟩ : syracuseStep 1402687 = 2104031) B2104031
theorem B27453329 : Blo 491791 27453329 := bstep (se 2 (by rfl) ⟨10294998, by rfl⟩ : syracuseStep 27453329 = 20589997) B20589997
theorem B1108583 : Blo 491791 1108583 := bstep (se 1 (by rfl) ⟨831437, by rfl⟩ : syracuseStep 1108583 = 1662875) B1662875
theorem B3566213 : Blo 491791 3566213 := bstep (se 4 (by rfl) ⟨334332, by rfl⟩ : syracuseStep 3566213 = 668665) B668665
theorem B1108961 : Blo 491791 1108961 := bstep (se 2 (by rfl) ⟨415860, by rfl⟩ : syracuseStep 1108961 = 831721) B831721
theorem B1666223 : Blo 491791 1666223 := bstep (se 1 (by rfl) ⟨1249667, by rfl⟩ : syracuseStep 1666223 = 2499335) B2499335
theorem B1404317 : Blo 491791 1404317 := bstep (se 3 (by rfl) ⟨263309, by rfl⟩ : syracuseStep 1404317 = 526619) B526619
theorem B3010231 : Blo 491791 3010231 := bstep (se 1 (by rfl) ⟨2257673, by rfl⟩ : syracuseStep 3010231 = 4515347) B4515347
theorem B3600463 : Blo 491791 3600463 := bstep (se 1 (by rfl) ⟨2700347, by rfl⟩ : syracuseStep 3600463 = 5400695) B5400695
theorem B3797417 : Blo 491791 3797417 := bstep (se 2 (by rfl) ⟨1424031, by rfl⟩ : syracuseStep 3797417 = 2848063) B2848063
theorem B1798793 : Blo 491791 1798793 := bstep (se 2 (by rfl) ⟨674547, by rfl⟩ : syracuseStep 1798793 = 1349095) B1349095
theorem B4748219 : Blo 491791 4748219 := bstep (se 1 (by rfl) ⟨3561164, by rfl⟩ : syracuseStep 4748219 = 7122329) B7122329
theorem B1668167 : Blo 491791 1668167 := bstep (se 1 (by rfl) ⟨1251125, by rfl⟩ : syracuseStep 1668167 = 2502251) B2502251
theorem B1406447 : Blo 491791 1406447 := bstep (se 1 (by rfl) ⟨1054835, by rfl⟩ : syracuseStep 1406447 = 2109671) B2109671
theorem B1111625 : Blo 491791 1111625 := bstep (se 2 (by rfl) ⟨416859, by rfl⟩ : syracuseStep 1111625 = 833719) B833719
theorem B10647683 : Blo 491791 10647683 := bstep (se 1 (by rfl) ⟨7985762, by rfl⟩ : syracuseStep 10647683 = 15971525) B15971525
theorem B3176603 : Blo 491791 3176603 := bstep (se 1 (by rfl) ⟨2382452, by rfl⟩ : syracuseStep 3176603 = 4764905) B4764905
theorem B1112417 : Blo 491791 1112417 := bstep (se 2 (by rfl) ⟨417156, by rfl⟩ : syracuseStep 1112417 = 834313) B834313
theorem B1112507 : Blo 491791 1112507 := bstep (se 1 (by rfl) ⟨834380, by rfl⟩ : syracuseStep 1112507 = 1668761) B1668761
theorem B2816491 : Blo 491791 2816491 := bstep (se 1 (by rfl) ⟨2112368, by rfl⟩ : syracuseStep 2816491 = 4224737) B4224737
theorem B1669625 : Blo 491791 1669625 := bstep (se 2 (by rfl) ⟨626109, by rfl⟩ : syracuseStep 1669625 = 1252219) B1252219
theorem B1407631 : Blo 491791 1407631 := bstep (se 1 (by rfl) ⟨1055723, by rfl⟩ : syracuseStep 1407631 = 2111447) B2111447
theorem B2817449 : Blo 491791 2817449 := bstep (se 2 (by rfl) ⟨1056543, by rfl⟩ : syracuseStep 2817449 = 2113087) B2113087
theorem B1113767 : Blo 491791 1113767 := bstep (se 1 (by rfl) ⟨835325, by rfl⟩ : syracuseStep 1113767 = 1670651) B1670651
theorem B753319 : Blo 491791 753319 := bstep (se 1 (by rfl) ⟨564989, by rfl⟩ : syracuseStep 753319 = 1129979) B1129979
theorem B5996231 : Blo 491791 5996231 := bstep (se 1 (by rfl) ⟨4497173, by rfl⟩ : syracuseStep 5996231 = 8994347) B8994347
theorem B1113875 : Blo 491791 1113875 := bstep (se 1 (by rfl) ⟨835406, by rfl⟩ : syracuseStep 1113875 = 1670813) B1670813
theorem B1113947 : Blo 491791 1113947 := bstep (se 1 (by rfl) ⟨835460, by rfl⟩ : syracuseStep 1113947 = 1670921) B1670921
theorem B1671137 : Blo 491791 1671137 := bstep (se 2 (by rfl) ⟨626676, by rfl⟩ : syracuseStep 1671137 = 1253353) B1253353
theorem B1409147 : Blo 491791 1409147 := bstep (se 1 (by rfl) ⟨1056860, by rfl⟩ : syracuseStep 1409147 = 2113721) B2113721
theorem B2490587 : Blo 491791 2490587 := bstep (se 1 (by rfl) ⟨1867940, by rfl⟩ : syracuseStep 2490587 = 3735881) B3735881
theorem B491839 : Blo 491791 491839 := bstep (se 1 (by rfl) ⟨368879, by rfl⟩ : syracuseStep 491839 = 737759) B737759
theorem B492007 : Blo 491791 492007 := bstep (se 1 (by rfl) ⟨369005, by rfl⟩ : syracuseStep 492007 = 738011) B738011
theorem B1671677 : Blo 491791 1671677 := bstep (se 3 (by rfl) ⟨313439, by rfl⟩ : syracuseStep 1671677 = 626879) B626879
theorem B492283 : Blo 491791 492283 := bstep (se 1 (by rfl) ⟨369212, by rfl⟩ : syracuseStep 492283 = 738425) B738425
theorem B492415 : Blo 491791 492415 := bstep (se 1 (by rfl) ⟨369311, by rfl⟩ : syracuseStep 492415 = 738623) B738623
theorem B1115387 : Blo 491791 1115387 := bstep (se 1 (by rfl) ⟨836540, by rfl⟩ : syracuseStep 1115387 = 1673081) B1673081
theorem B492863 : Blo 491791 492863 := bstep (se 1 (by rfl) ⟨369647, by rfl⟩ : syracuseStep 492863 = 739295) B739295
theorem B492903 : Blo 491791 492903 := bstep (se 1 (by rfl) ⟨369677, by rfl⟩ : syracuseStep 492903 = 739355) B739355
theorem B493007 : Blo 491791 493007 := bstep (se 1 (by rfl) ⟨369755, by rfl⟩ : syracuseStep 493007 = 739511) B739511
theorem B493023 : Blo 491791 493023 := bstep (se 1 (by rfl) ⟨369767, by rfl⟩ : syracuseStep 493023 = 739535) B739535
theorem B3802625 : Blo 491791 3802625 := bstep (se 2 (by rfl) ⟨1425984, by rfl⟩ : syracuseStep 3802625 = 2851969) B2851969
theorem B493287 : Blo 491791 493287 := bstep (se 1 (by rfl) ⟨369965, by rfl⟩ : syracuseStep 493287 = 739931) B739931
theorem B1246985 : Blo 491791 1246985 := bstep (se 2 (by rfl) ⟨467619, by rfl⟩ : syracuseStep 1246985 = 935239) B935239
theorem B493383 : Blo 491791 493383 := bstep (se 1 (by rfl) ⟨370037, by rfl⟩ : syracuseStep 493383 = 740075) B740075
theorem B493403 : Blo 491791 493403 := bstep (se 1 (by rfl) ⟨370052, by rfl⟩ : syracuseStep 493403 = 740105) B740105
theorem B886825 : Blo 491791 886825 := bstep (se 2 (by rfl) ⟨332559, by rfl⟩ : syracuseStep 886825 = 665119) B665119
theorem B493679 : Blo 491791 493679 := bstep (se 1 (by rfl) ⟨370259, by rfl⟩ : syracuseStep 493679 = 740519) B740519
theorem B493775 : Blo 491791 493775 := bstep (se 1 (by rfl) ⟨370331, by rfl⟩ : syracuseStep 493775 = 740663) B740663
theorem B493983 : Blo 491791 493983 := bstep (se 1 (by rfl) ⟨370487, by rfl⟩ : syracuseStep 493983 = 740975) B740975
theorem B1870249 : Blo 491791 1870249 := bstep (se 2 (by rfl) ⟨701343, by rfl⟩ : syracuseStep 1870249 = 1402687) B1402687
theorem B494031 : Blo 491791 494031 := bstep (se 1 (by rfl) ⟨370523, by rfl⟩ : syracuseStep 494031 = 741047) B741047
theorem B494063 : Blo 491791 494063 := bstep (se 1 (by rfl) ⟨370547, by rfl⟩ : syracuseStep 494063 = 741095) B741095
theorem B494171 : Blo 491791 494171 := bstep (se 1 (by rfl) ⟨370628, by rfl⟩ : syracuseStep 494171 = 741257) B741257
theorem B789211 : Blo 491791 789211 := bstep (se 1 (by rfl) ⟨591908, by rfl⟩ : syracuseStep 789211 = 1183817) B1183817
theorem B494331 : Blo 491791 494331 := bstep (se 1 (by rfl) ⟨370748, by rfl⟩ : syracuseStep 494331 = 741497) B741497
theorem B494335 : Blo 491791 494335 := bstep (se 1 (by rfl) ⟨370751, by rfl⟩ : syracuseStep 494335 = 741503) B741503
theorem B1281079 : Blo 491791 1281079 := bstep (se 1 (by rfl) ⟨960809, by rfl⟩ : syracuseStep 1281079 = 1921619) B1921619
theorem B1051879 : Blo 491791 1051879 := bstep (se 1 (by rfl) ⟨788909, by rfl⟩ : syracuseStep 1051879 = 1577819) B1577819
theorem B1051913 : Blo 491791 1051913 := bstep (se 2 (by rfl) ⟨394467, by rfl⟩ : syracuseStep 1051913 = 788935) B788935
theorem B494895 : Blo 491791 494895 := bstep (se 1 (by rfl) ⟨371171, by rfl⟩ : syracuseStep 494895 = 742343) B742343
theorem B494911 : Blo 491791 494911 := bstep (se 1 (by rfl) ⟨371183, by rfl⟩ : syracuseStep 494911 = 742367) B742367
theorem B495135 : Blo 491791 495135 := bstep (se 1 (by rfl) ⟨371351, by rfl⟩ : syracuseStep 495135 = 742703) B742703
theorem B21368357 : Blo 491791 21368357 := bstep (se 4 (by rfl) ⟨2003283, by rfl⟩ : syracuseStep 21368357 = 4006567) B4006567
theorem B495271 : Blo 491791 495271 := bstep (se 1 (by rfl) ⟨371453, by rfl⟩ : syracuseStep 495271 = 742907) B742907
theorem B495295 : Blo 491791 495295 := bstep (se 1 (by rfl) ⟨371471, by rfl⟩ : syracuseStep 495295 = 742943) B742943
theorem B495387 : Blo 491791 495387 := bstep (se 1 (by rfl) ⟨371540, by rfl⟩ : syracuseStep 495387 = 743081) B743081
theorem B495391 : Blo 491791 495391 := bstep (se 1 (by rfl) ⟨371543, by rfl⟩ : syracuseStep 495391 = 743087) B743087
theorem B495471 : Blo 491791 495471 := bstep (se 1 (by rfl) ⟨371603, by rfl⟩ : syracuseStep 495471 = 743207) B743207
theorem B495643 : Blo 491791 495643 := bstep (se 1 (by rfl) ⟨371732, by rfl⟩ : syracuseStep 495643 = 743465) B743465
theorem B495663 : Blo 491791 495663 := bstep (se 1 (by rfl) ⟨371747, by rfl⟩ : syracuseStep 495663 = 743495) B743495
theorem B1872679 : Blo 491791 1872679 := bstep (se 1 (by rfl) ⟨1404509, by rfl⟩ : syracuseStep 1872679 = 2809019) B2809019
theorem B5641001 : Blo 491791 5641001 := bstep (se 2 (by rfl) ⟨2115375, by rfl⟩ : syracuseStep 5641001 = 4230751) B4230751
theorem B2102527 : Blo 491791 2102527 := bstep (se 1 (by rfl) ⟨1576895, by rfl⟩ : syracuseStep 2102527 = 3153791) B3153791
theorem B5642459 : Blo 491791 5642459 := bstep (se 1 (by rfl) ⟨4231844, by rfl⟩ : syracuseStep 5642459 = 8463689) B8463689
theorem B2496743 : Blo 491791 2496743 := bstep (se 1 (by rfl) ⟨1872557, by rfl⟩ : syracuseStep 2496743 = 3745115) B3745115
theorem B2365787 : Blo 491791 2365787 := bstep (se 1 (by rfl) ⟨1774340, by rfl⟩ : syracuseStep 2365787 = 3548681) B3548681
theorem B1055467 : Blo 491791 1055467 := bstep (se 1 (by rfl) ⟨791600, by rfl⟩ : syracuseStep 1055467 = 1583201) B1583201
theorem B1252655 : Blo 491791 1252655 := bstep (se 1 (by rfl) ⟨939491, by rfl⟩ : syracuseStep 1252655 = 1878983) B1878983
theorem B3743171 : Blo 491791 3743171 := bstep (se 1 (by rfl) ⟨2807378, by rfl⟩ : syracuseStep 3743171 = 5614757) B5614757
theorem B3383009 : Blo 491791 3383009 := bstep (se 2 (by rfl) ⟨1268628, by rfl⟩ : syracuseStep 3383009 = 2537257) B2537257
theorem B3154049 : Blo 491791 3154049 := bstep (se 2 (by rfl) ⟨1182768, by rfl⟩ : syracuseStep 3154049 = 2365537) B2365537
theorem B2531611 : Blo 491791 2531611 := bstep (se 1 (by rfl) ⟨1898708, by rfl⟩ : syracuseStep 2531611 = 3797417) B3797417
theorem B3547759 : Blo 491791 3547759 := bstep (se 1 (by rfl) ⟨2660819, by rfl⟩ : syracuseStep 3547759 = 5321639) B5321639
theorem B1876841 : Blo 491791 1876841 := bstep (se 2 (by rfl) ⟨703815, by rfl⟩ : syracuseStep 1876841 = 1407631) B1407631
theorem B1188823 : Blo 491791 1188823 := bstep (se 1 (by rfl) ⟨891617, by rfl⟩ : syracuseStep 1188823 = 1783235) B1783235
theorem B2500307 : Blo 491791 2500307 := bstep (se 1 (by rfl) ⟨1875230, by rfl⟩ : syracuseStep 2500307 = 3750461) B3750461
theorem B1878299 : Blo 491791 1878299 := bstep (se 1 (by rfl) ⟨1408724, by rfl⟩ : syracuseStep 1878299 = 2817449) B2817449
theorem B2370343 : Blo 491791 2370343 := bstep (se 1 (by rfl) ⟨1777757, by rfl⟩ : syracuseStep 2370343 = 3555515) B3555515
theorem B3747059 : Blo 491791 3747059 := bstep (se 1 (by rfl) ⟨2810294, by rfl⟩ : syracuseStep 3747059 = 5620589) B5620589
theorem B1584431 : Blo 491791 1584431 := bstep (se 1 (by rfl) ⟨1188323, by rfl⟩ : syracuseStep 1584431 = 2376647) B2376647
theorem B3157481 : Blo 491791 3157481 := bstep (se 2 (by rfl) ⟨1184055, by rfl⟩ : syracuseStep 3157481 = 2368111) B2368111
theorem B1519609 : Blo 491791 1519609 := bstep (se 2 (by rfl) ⟨569853, by rfl⟩ : syracuseStep 1519609 = 1139707) B1139707
theorem B832207 : Blo 491791 832207 := bstep (se 1 (by rfl) ⟨624155, by rfl⟩ : syracuseStep 832207 = 1248311) B1248311
theorem B2274131 : Blo 491791 2274131 := bstep (se 1 (by rfl) ⟨1705598, by rfl⟩ : syracuseStep 2274131 = 3411197) B3411197
theorem B833179 : Blo 491791 833179 := bstep (se 1 (by rfl) ⟨624884, by rfl⟩ : syracuseStep 833179 = 1249769) B1249769
theorem B1881913 : Blo 491791 1881913 := bstep (se 2 (by rfl) ⟨705717, by rfl⟩ : syracuseStep 1881913 = 1411435) B1411435
theorem B2504681 : Blo 491791 2504681 := bstep (se 2 (by rfl) ⟨939255, by rfl⟩ : syracuseStep 2504681 = 1878511) B1878511
theorem B6076417 : Blo 491791 6076417 := bstep (se 2 (by rfl) ⟨2278656, by rfl⟩ : syracuseStep 6076417 = 4557313) B4557313
theorem B4503671 : Blo 491791 4503671 := bstep (se 1 (by rfl) ⟨3377753, by rfl⟩ : syracuseStep 4503671 = 6755507) B6755507
theorem B702847 : Blo 491791 702847 := bstep (se 1 (by rfl) ⟨527135, by rfl⟩ : syracuseStep 702847 = 1054271) B1054271
theorem B6109607 : Blo 491791 6109607 := bstep (se 1 (by rfl) ⟨4582205, by rfl⟩ : syracuseStep 6109607 = 9164411) B9164411
theorem B1522127 : Blo 491791 1522127 := bstep (se 1 (by rfl) ⟨1141595, by rfl⟩ : syracuseStep 1522127 = 2283191) B2283191
theorem B4012667 : Blo 491791 4012667 := bstep (se 1 (by rfl) ⟨3009500, by rfl⟩ : syracuseStep 4012667 = 6019001) B6019001
theorem B834239 : Blo 491791 834239 := bstep (se 1 (by rfl) ⟨625679, by rfl⟩ : syracuseStep 834239 = 1251359) B1251359
theorem B1424251 : Blo 491791 1424251 := bstep (se 1 (by rfl) ⟨1068188, by rfl⟩ : syracuseStep 1424251 = 2136377) B2136377
theorem B20331719 : Blo 491791 20331719 := bstep (se 1 (by rfl) ⟨15248789, by rfl⟩ : syracuseStep 20331719 = 30497579) B30497579
theorem B4013641 : Blo 491791 4013641 := bstep (se 2 (by rfl) ⟨1505115, by rfl⟩ : syracuseStep 4013641 = 3010231) B3010231
theorem B2506463 : Blo 491791 2506463 := bstep (se 1 (by rfl) ⟨1879847, by rfl⟩ : syracuseStep 2506463 = 3759695) B3759695
theorem B5324791 : Blo 491791 5324791 := bstep (se 1 (by rfl) ⟨3993593, by rfl⟩ : syracuseStep 5324791 = 7987187) B7987187
theorem B4800617 : Blo 491791 4800617 := bstep (se 2 (by rfl) ⟨1800231, by rfl⟩ : syracuseStep 4800617 = 3600463) B3600463
theorem B934031 : Blo 491791 934031 := bstep (se 1 (by rfl) ⟨700523, by rfl⟩ : syracuseStep 934031 = 1401047) B1401047
theorem B5423399 : Blo 491791 5423399 := bstep (se 1 (by rfl) ⟨4067549, by rfl⟩ : syracuseStep 5423399 = 8135099) B8135099
theorem B6308401 : Blo 491791 6308401 := bstep (se 2 (by rfl) ⟨2365650, by rfl⟩ : syracuseStep 6308401 = 4731301) B4731301
theorem B738023 : Blo 491791 738023 := bstep (se 1 (by rfl) ⟨553517, by rfl⟩ : syracuseStep 738023 = 1107035) B1107035
theorem B7095107 : Blo 491791 7095107 := bstep (se 1 (by rfl) ⟨5321330, by rfl⟩ : syracuseStep 7095107 = 10642661) B10642661
theorem B3752891 : Blo 491791 3752891 := bstep (se 1 (by rfl) ⟨2814668, by rfl⟩ : syracuseStep 3752891 = 5629337) B5629337
theorem B738287 : Blo 491791 738287 := bstep (se 1 (by rfl) ⟨553715, by rfl⟩ : syracuseStep 738287 = 1107431) B1107431
theorem B738407 : Blo 491791 738407 := bstep (se 1 (by rfl) ⟨553805, by rfl⟩ : syracuseStep 738407 = 1107611) B1107611
theorem B18302219 : Blo 491791 18302219 := bstep (se 1 (by rfl) ⟨13726664, by rfl⟩ : syracuseStep 18302219 = 27453329) B27453329
theorem B739055 : Blo 491791 739055 := bstep (se 1 (by rfl) ⟨554291, by rfl⟩ : syracuseStep 739055 = 1108583) B1108583
theorem B2377475 : Blo 491791 2377475 := bstep (se 1 (by rfl) ⟨1783106, by rfl⟩ : syracuseStep 2377475 = 3566213) B3566213
theorem B739307 : Blo 491791 739307 := bstep (se 1 (by rfl) ⟨554480, by rfl⟩ : syracuseStep 739307 = 1108961) B1108961
theorem B936211 : Blo 491791 936211 := bstep (se 1 (by rfl) ⟨702158, by rfl⟩ : syracuseStep 936211 = 1404317) B1404317
theorem B937001 : Blo 491791 937001 := bstep (se 2 (by rfl) ⟨351375, by rfl⟩ : syracuseStep 937001 = 702751) B702751
theorem B2509865 : Blo 491791 2509865 := bstep (se 2 (by rfl) ⟨941199, by rfl⟩ : syracuseStep 2509865 = 1882399) B1882399
theorem B1199195 : Blo 491791 1199195 := bstep (se 1 (by rfl) ⟨899396, by rfl⟩ : syracuseStep 1199195 = 1798793) B1798793
theorem B3165479 : Blo 491791 3165479 := bstep (se 1 (by rfl) ⟨2374109, by rfl⟩ : syracuseStep 3165479 = 4748219) B4748219
theorem B4082993 : Blo 491791 4082993 := bstep (se 2 (by rfl) ⟨1531122, by rfl⟩ : syracuseStep 4082993 = 3062245) B3062245
theorem B3755321 : Blo 491791 3755321 := bstep (se 2 (by rfl) ⟨1408245, by rfl⟩ : syracuseStep 3755321 = 2816491) B2816491
theorem B49270139 : Blo 491791 49270139 := bstep (se 1 (by rfl) ⟨36952604, by rfl⟩ : syracuseStep 49270139 = 73905209) B73905209
theorem B4017701 : Blo 491791 4017701 := bstep (se 4 (by rfl) ⟨376659, by rfl⟩ : syracuseStep 4017701 = 753319) B753319
theorem B937631 : Blo 491791 937631 := bstep (se 1 (by rfl) ⟨703223, by rfl⟩ : syracuseStep 937631 = 1406447) B1406447
theorem B741083 : Blo 491791 741083 := bstep (se 1 (by rfl) ⟨555812, by rfl⟩ : syracuseStep 741083 = 1111625) B1111625
theorem B1331113 : Blo 491791 1331113 := bstep (se 2 (by rfl) ⟨499167, by rfl⟩ : syracuseStep 1331113 = 998335) B998335
theorem B7098455 : Blo 491791 7098455 := bstep (se 1 (by rfl) ⟨5323841, by rfl⟩ : syracuseStep 7098455 = 10647683) B10647683
theorem B2117735 : Blo 491791 2117735 := bstep (se 1 (by rfl) ⟨1588301, by rfl⟩ : syracuseStep 2117735 = 3176603) B3176603
theorem B741611 : Blo 491791 741611 := bstep (se 1 (by rfl) ⟨556208, by rfl⟩ : syracuseStep 741611 = 1112417) B1112417
theorem B741671 : Blo 491791 741671 := bstep (se 1 (by rfl) ⟨556253, by rfl⟩ : syracuseStep 741671 = 1112507) B1112507
theorem B12702095 : Blo 491791 12702095 := bstep (se 1 (by rfl) ⟨9526571, by rfl⟩ : syracuseStep 12702095 = 19053143) B19053143
theorem B742511 : Blo 491791 742511 := bstep (se 1 (by rfl) ⟨556883, by rfl⟩ : syracuseStep 742511 = 1113767) B1113767
theorem B709799 : Blo 491791 709799 := bstep (se 1 (by rfl) ⟨532349, by rfl⟩ : syracuseStep 709799 = 1064699) B1064699
theorem B742583 : Blo 491791 742583 := bstep (se 1 (by rfl) ⟨556937, by rfl⟩ : syracuseStep 742583 = 1113875) B1113875
theorem B742631 : Blo 491791 742631 := bstep (se 1 (by rfl) ⟨556973, by rfl⟩ : syracuseStep 742631 = 1113947) B1113947
theorem B742823 : Blo 491791 742823 := bstep (se 1 (by rfl) ⟨557117, by rfl⟩ : syracuseStep 742823 = 1114235) B1114235
theorem B939575 : Blo 491791 939575 := bstep (se 1 (by rfl) ⟨704681, by rfl⟩ : syracuseStep 939575 = 1409363) B1409363
theorem B743003 : Blo 491791 743003 := bstep (se 1 (by rfl) ⟨557252, by rfl⟩ : syracuseStep 743003 = 1114505) B1114505
theorem B743015 : Blo 491791 743015 := bstep (se 1 (by rfl) ⟨557261, by rfl⟩ : syracuseStep 743015 = 1114523) B1114523
theorem B1660607 : Blo 491791 1660607 := bstep (se 1 (by rfl) ⟨1245455, by rfl⟩ : syracuseStep 1660607 = 2490911) B2490911
theorem B1660769 : Blo 491791 1660769 := bstep (se 2 (by rfl) ⟨622788, by rfl⟩ : syracuseStep 1660769 = 1245577) B1245577
theorem B3168143 : Blo 491791 3168143 := bstep (se 1 (by rfl) ⟨2376107, by rfl⟩ : syracuseStep 3168143 = 4752215) B4752215
theorem B3759209 : Blo 491791 3759209 := bstep (se 2 (by rfl) ⟨1409703, by rfl⟩ : syracuseStep 3759209 = 2819407) B2819407
theorem B13001363 : Blo 491791 13001363 := bstep (se 1 (by rfl) ⟨9751022, by rfl⟩ : syracuseStep 13001363 = 19502045) B19502045
theorem B1106729 : Blo 491791 1106729 := bstep (se 2 (by rfl) ⟨415023, by rfl⟩ : syracuseStep 1106729 = 830047) B830047
theorem B1664927 : Blo 491791 1664927 := bstep (se 1 (by rfl) ⟨1248695, by rfl⟩ : syracuseStep 1664927 = 2497391) B2497391
theorem B1108223 : Blo 491791 1108223 := bstep (se 1 (by rfl) ⟨831167, by rfl⟩ : syracuseStep 1108223 = 1662335) B1662335
theorem B9005435 : Blo 491791 9005435 := bstep (se 1 (by rfl) ⟨6754076, by rfl⟩ : syracuseStep 9005435 = 13508153) B13508153
theorem B1665467 : Blo 491791 1665467 := bstep (se 1 (by rfl) ⟨1249100, by rfl⟩ : syracuseStep 1665467 = 2498201) B2498201
theorem B1108457 : Blo 491791 1108457 := bstep (se 2 (by rfl) ⟨415671, by rfl⟩ : syracuseStep 1108457 = 831343) B831343
theorem B12675851 : Blo 491791 12675851 := bstep (se 1 (by rfl) ⟨9506888, by rfl⟩ : syracuseStep 12675851 = 19013777) B19013777
theorem B10120139 : Blo 491791 10120139 := bstep (se 1 (by rfl) ⟨7590104, by rfl⟩ : syracuseStep 10120139 = 15180209) B15180209
theorem B2813075 : Blo 491791 2813075 := bstep (se 1 (by rfl) ⟨2109806, by rfl⟩ : syracuseStep 2813075 = 4219613) B4219613
theorem B1109483 : Blo 491791 1109483 := bstep (se 1 (by rfl) ⟨832112, by rfl⟩ : syracuseStep 1109483 = 1664225) B1664225
theorem B8679383 : Blo 491791 8679383 := bstep (se 1 (by rfl) ⟨6509537, by rfl⟩ : syracuseStep 8679383 = 13019075) B13019075
theorem B749675 : Blo 491791 749675 := bstep (se 1 (by rfl) ⟨562256, by rfl⟩ : syracuseStep 749675 = 1124513) B1124513
theorem B1110815 : Blo 491791 1110815 := bstep (se 1 (by rfl) ⟨833111, by rfl⟩ : syracuseStep 1110815 = 1666223) B1666223
theorem B5076361 : Blo 491791 5076361 := bstep (se 2 (by rfl) ⟨1903635, by rfl⟩ : syracuseStep 5076361 = 3807271) B3807271
theorem B751081 : Blo 491791 751081 := bstep (se 2 (by rfl) ⟨281655, by rfl⟩ : syracuseStep 751081 = 563311) B563311
theorem B554863 : Blo 491791 554863 := bstep (se 1 (by rfl) ⟨416147, by rfl⟩ : syracuseStep 554863 = 832295) B832295
theorem B1112111 : Blo 491791 1112111 := bstep (se 1 (by rfl) ⟨834083, by rfl⟩ : syracuseStep 1112111 = 1668167) B1668167
theorem B1669355 : Blo 491791 1669355 := bstep (se 1 (by rfl) ⟨1252016, by rfl⟩ : syracuseStep 1669355 = 2504033) B2504033
theorem B555367 : Blo 491791 555367 := bstep (se 1 (by rfl) ⟨416525, by rfl⟩ : syracuseStep 555367 = 833051) B833051
theorem B7240195 : Blo 491791 7240195 := bstep (se 1 (by rfl) ⟨5430146, by rfl⟩ : syracuseStep 7240195 = 10860293) B10860293
theorem B415464389 : Blo 491791 415464389 := bstep (se 4 (by rfl) ⟨38949786, by rfl⟩ : syracuseStep 415464389 = 77899573) B77899573
theorem B556015 : Blo 491791 556015 := bstep (se 1 (by rfl) ⟨417011, by rfl⟩ : syracuseStep 556015 = 834023) B834023
theorem B1113083 : Blo 491791 1113083 := bstep (se 1 (by rfl) ⟨834812, by rfl⟩ : syracuseStep 1113083 = 1669625) B1669625
theorem B19758275 : Blo 491791 19758275 := bstep (se 1 (by rfl) ⟨14818706, by rfl⟩ : syracuseStep 19758275 = 29637413) B29637413
theorem B4226377 : Blo 491791 4226377 := bstep (se 2 (by rfl) ⟨1584891, by rfl⟩ : syracuseStep 4226377 = 3169783) B3169783
theorem B3997487 : Blo 491791 3997487 := bstep (se 1 (by rfl) ⟨2998115, by rfl⟩ : syracuseStep 3997487 = 5996231) B5996231
theorem B1408907 : Blo 491791 1408907 := bstep (se 1 (by rfl) ⟨1056680, by rfl⟩ : syracuseStep 1408907 = 2113361) B2113361
theorem B1114091 : Blo 491791 1114091 := bstep (se 1 (by rfl) ⟨835568, by rfl⟩ : syracuseStep 1114091 = 1671137) B1671137
theorem B1999133 : Blo 491791 1999133 := bstep (se 3 (by rfl) ⟨374837, by rfl⟩ : syracuseStep 1999133 = 749675) B749675
theorem B1114451 : Blo 491791 1114451 := bstep (se 1 (by rfl) ⟨835838, by rfl⟩ : syracuseStep 1114451 = 1671677) B1671677
theorem B3375481 : Blo 491791 3375481 := bstep (se 2 (by rfl) ⟨1265805, by rfl⟩ : syracuseStep 3375481 = 2531611) B2531611
theorem B2490749 : Blo 491791 2490749 := bstep (se 3 (by rfl) ⟨467015, by rfl⟩ : syracuseStep 2490749 = 934031) B934031
theorem B492015 : Blo 491791 492015 := bstep (se 1 (by rfl) ⟨369011, by rfl⟩ : syracuseStep 492015 = 738023) B738023
theorem B492191 : Blo 491791 492191 := bstep (se 1 (by rfl) ⟨369143, by rfl⟩ : syracuseStep 492191 = 738287) B738287
theorem B492271 : Blo 491791 492271 := bstep (se 1 (by rfl) ⟨369203, by rfl⟩ : syracuseStep 492271 = 738407) B738407
theorem B492703 : Blo 491791 492703 := bstep (se 1 (by rfl) ⟨369527, by rfl⟩ : syracuseStep 492703 = 739055) B739055
theorem B492871 : Blo 491791 492871 := bstep (se 1 (by rfl) ⟨369653, by rfl⟩ : syracuseStep 492871 = 739307) B739307
theorem B7571189 : Blo 491791 7571189 := bstep (se 5 (by rfl) ⟨354899, by rfl⟩ : syracuseStep 7571189 = 709799) B709799
theorem B624667 : Blo 491791 624667 := bstep (se 1 (by rfl) ⟨468500, by rfl⟩ : syracuseStep 624667 = 937001) B937001
theorem B1673243 : Blo 491791 1673243 := bstep (se 1 (by rfl) ⟨1254932, by rfl⟩ : syracuseStep 1673243 = 2509865) B2509865
theorem B2721995 : Blo 491791 2721995 := bstep (se 1 (by rfl) ⟨2041496, by rfl⟩ : syracuseStep 2721995 = 4082993) B4082993
theorem B625087 : Blo 491791 625087 := bstep (se 1 (by rfl) ⟨468815, by rfl⟩ : syracuseStep 625087 = 937631) B937631
theorem B494055 : Blo 491791 494055 := bstep (se 1 (by rfl) ⟨370541, by rfl⟩ : syracuseStep 494055 = 741083) B741083
theorem B1182433 : Blo 491791 1182433 := bstep (se 2 (by rfl) ⟨443412, by rfl⟩ : syracuseStep 1182433 = 886825) B886825
theorem B1411823 : Blo 491791 1411823 := bstep (se 1 (by rfl) ⟨1058867, by rfl⟩ : syracuseStep 1411823 = 2117735) B2117735
theorem B494407 : Blo 491791 494407 := bstep (se 1 (by rfl) ⟨370805, by rfl⟩ : syracuseStep 494407 = 741611) B741611
theorem B494447 : Blo 491791 494447 := bstep (se 1 (by rfl) ⟨370835, by rfl⟩ : syracuseStep 494447 = 741671) B741671
theorem B1248281 : Blo 491791 1248281 := bstep (se 2 (by rfl) ⟨468105, by rfl⟩ : syracuseStep 1248281 = 936211) B936211
theorem B2493665 : Blo 491791 2493665 := bstep (se 2 (by rfl) ⟨935124, by rfl⟩ : syracuseStep 2493665 = 1870249) B1870249
theorem B495007 : Blo 491791 495007 := bstep (se 1 (by rfl) ⟨371255, by rfl⟩ : syracuseStep 495007 = 742511) B742511
theorem B495055 : Blo 491791 495055 := bstep (se 1 (by rfl) ⟨371291, by rfl⟩ : syracuseStep 495055 = 742583) B742583
theorem B495087 : Blo 491791 495087 := bstep (se 1 (by rfl) ⟨371315, by rfl⟩ : syracuseStep 495087 = 742631) B742631
theorem B495215 : Blo 491791 495215 := bstep (se 1 (by rfl) ⟨371411, by rfl⟩ : syracuseStep 495215 = 742823) B742823
theorem B1052281 : Blo 491791 1052281 := bstep (se 2 (by rfl) ⟨394605, by rfl⟩ : syracuseStep 1052281 = 789211) B789211
theorem B626383 : Blo 491791 626383 := bstep (se 1 (by rfl) ⟨469787, by rfl⟩ : syracuseStep 626383 = 939575) B939575
theorem B495335 : Blo 491791 495335 := bstep (se 1 (by rfl) ⟨371501, by rfl⟩ : syracuseStep 495335 = 743003) B743003
theorem B495343 : Blo 491791 495343 := bstep (se 1 (by rfl) ⟨371507, by rfl⟩ : syracuseStep 495343 = 743015) B743015
theorem B2495447 : Blo 491791 2495447 := bstep (se 1 (by rfl) ⟨1871585, by rfl⟩ : syracuseStep 2495447 = 3743171) B3743171
theorem B1774817 : Blo 491791 1774817 := bstep (se 2 (by rfl) ⟨665556, by rfl⟩ : syracuseStep 1774817 = 1331113) B1331113
theorem B2102699 : Blo 491791 2102699 := bstep (se 1 (by rfl) ⟨1577024, by rfl⟩ : syracuseStep 2102699 = 3154049) B3154049
theorem B1251227 : Blo 491791 1251227 := bstep (se 1 (by rfl) ⟨938420, by rfl⟩ : syracuseStep 1251227 = 1876841) B1876841
theorem B2496905 : Blo 491791 2496905 := bstep (se 2 (by rfl) ⟨936339, by rfl⟩ : syracuseStep 2496905 = 1872679) B1872679
theorem B16292285 : Blo 491791 16292285 := bstep (se 3 (by rfl) ⟨3054803, by rfl⟩ : syracuseStep 16292285 = 6109607) B6109607
theorem B1252199 : Blo 491791 1252199 := bstep (se 1 (by rfl) ⟨939149, by rfl⟩ : syracuseStep 1252199 = 1878299) B1878299
theorem B6003623 : Blo 491791 6003623 := bstep (se 1 (by rfl) ⟨4502717, by rfl⟩ : syracuseStep 6003623 = 9005435) B9005435
theorem B1875383 : Blo 491791 1875383 := bstep (se 1 (by rfl) ⟨1406537, by rfl⟩ : syracuseStep 1875383 = 2813075) B2813075
theorem B2498039 : Blo 491791 2498039 := bstep (se 1 (by rfl) ⟨1873529, by rfl⟩ : syracuseStep 2498039 = 3747059) B3747059
theorem B1056287 : Blo 491791 1056287 := bstep (se 1 (by rfl) ⟨792215, by rfl⟩ : syracuseStep 1056287 = 1584431) B1584431
theorem B8101889 : Blo 491791 8101889 := bstep (se 2 (by rfl) ⟨3038208, by rfl⟩ : syracuseStep 8101889 = 6076417) B6076417
theorem B1516087 : Blo 491791 1516087 := bstep (se 1 (by rfl) ⟨1137065, by rfl⟩ : syracuseStep 1516087 = 2274131) B2274131
theorem B5351521 : Blo 491791 5351521 := bstep (se 2 (by rfl) ⟨2006820, by rfl⟩ : syracuseStep 5351521 = 4013641) B4013641
theorem B2664991 : Blo 491791 2664991 := bstep (se 1 (by rfl) ⟨1998743, by rfl⟩ : syracuseStep 2664991 = 3997487) B3997487
theorem B3615599 : Blo 491791 3615599 := bstep (se 1 (by rfl) ⟨2711699, by rfl⟩ : syracuseStep 3615599 = 5423399) B5423399
theorem B4730071 : Blo 491791 4730071 := bstep (se 1 (by rfl) ⟨3547553, by rfl⟩ : syracuseStep 4730071 = 7095107) B7095107
theorem B2501927 : Blo 491791 2501927 := bstep (se 1 (by rfl) ⟨1876445, by rfl⟩ : syracuseStep 2501927 = 3752891) B3752891
theorem B4730345 : Blo 491791 4730345 := bstep (se 2 (by rfl) ⟨1773879, by rfl⟩ : syracuseStep 4730345 = 3547759) B3547759
theorem B12201479 : Blo 491791 12201479 := bstep (se 1 (by rfl) ⟨9151109, by rfl⟩ : syracuseStep 12201479 = 18302219) B18302219
theorem B2535083 : Blo 491791 2535083 := bstep (se 1 (by rfl) ⟨1901312, by rfl⟩ : syracuseStep 2535083 = 3802625) B3802625
theorem B1584983 : Blo 491791 1584983 := bstep (se 1 (by rfl) ⟨1188737, by rfl⟩ : syracuseStep 1584983 = 2377475) B2377475
theorem B831323 : Blo 491791 831323 := bstep (se 1 (by rfl) ⟨623492, by rfl⟩ : syracuseStep 831323 = 1246985) B1246985
theorem B1585097 : Blo 491791 1585097 := bstep (se 2 (by rfl) ⟨594411, by rfl⟩ : syracuseStep 1585097 = 1188823) B1188823
theorem B3748517 : Blo 491791 3748517 := bstep (se 4 (by rfl) ⟨351423, by rfl⟩ : syracuseStep 3748517 = 702847) B702847
theorem B799463 : Blo 491791 799463 := bstep (se 1 (by rfl) ⟨599597, by rfl⟩ : syracuseStep 799463 = 1199195) B1199195
theorem B2110319 : Blo 491791 2110319 := bstep (se 1 (by rfl) ⟨1582739, by rfl⟩ : syracuseStep 2110319 = 3165479) B3165479
theorem B2503547 : Blo 491791 2503547 := bstep (se 1 (by rfl) ⟨1877660, by rfl⟩ : syracuseStep 2503547 = 3755321) B3755321
theorem B32846759 : Blo 491791 32846759 := bstep (se 1 (by rfl) ⟨24635069, by rfl⟩ : syracuseStep 32846759 = 49270139) B49270139
theorem B4732303 : Blo 491791 4732303 := bstep (se 1 (by rfl) ⟨3549227, by rfl⟩ : syracuseStep 4732303 = 7098455) B7098455
theorem B8468063 : Blo 491791 8468063 := bstep (se 1 (by rfl) ⟨6351047, by rfl⟩ : syracuseStep 8468063 = 12702095) B12702095
theorem B3160457 : Blo 491791 3160457 := bstep (se 2 (by rfl) ⟨1185171, by rfl⟩ : syracuseStep 3160457 = 2370343) B2370343
theorem B2112095 : Blo 491791 2112095 := bstep (se 1 (by rfl) ⟨1584071, by rfl⟩ : syracuseStep 2112095 = 3168143) B3168143
theorem B2506139 : Blo 491791 2506139 := bstep (se 1 (by rfl) ⟨1879604, by rfl⟩ : syracuseStep 2506139 = 3759209) B3759209
theorem B835103 : Blo 491791 835103 := bstep (se 1 (by rfl) ⟨626327, by rfl⟩ : syracuseStep 835103 = 1252655) B1252655
theorem B6832421 : Blo 491791 6832421 := bstep (se 4 (by rfl) ⟨640539, by rfl⟩ : syracuseStep 6832421 = 1281079) B1281079
theorem B8667575 : Blo 491791 8667575 := bstep (se 1 (by rfl) ⟨6500681, by rfl⟩ : syracuseStep 8667575 = 13001363) B13001363
theorem B737819 : Blo 491791 737819 := bstep (se 1 (by rfl) ⟨553364, by rfl⟩ : syracuseStep 737819 = 1106729) B1106729
theorem B6308765 : Blo 491791 6308765 := bstep (se 3 (by rfl) ⟨1182893, by rfl⟩ : syracuseStep 6308765 = 2365787) B2365787
theorem B738815 : Blo 491791 738815 := bstep (se 1 (by rfl) ⟨554111, by rfl⟩ : syracuseStep 738815 = 1108223) B1108223
theorem B738971 : Blo 491791 738971 := bstep (se 1 (by rfl) ⟨554228, by rfl⟩ : syracuseStep 738971 = 1108457) B1108457
theorem B2803369 : Blo 491791 2803369 := bstep (se 2 (by rfl) ⟨1051263, by rfl⟩ : syracuseStep 2803369 = 2102527) B2102527
theorem B6768481 : Blo 491791 6768481 := bstep (se 2 (by rfl) ⟨2538180, by rfl⟩ : syracuseStep 6768481 = 5076361) B5076361
theorem B1001441 : Blo 491791 1001441 := bstep (se 2 (by rfl) ⟨375540, by rfl⟩ : syracuseStep 1001441 = 751081) B751081
theorem B739655 : Blo 491791 739655 := bstep (se 1 (by rfl) ⟨554741, by rfl⟩ : syracuseStep 739655 = 1109483) B1109483
theorem B2509217 : Blo 491791 2509217 := bstep (se 2 (by rfl) ⟨940956, by rfl⟩ : syracuseStep 2509217 = 1881913) B1881913
theorem B739817 : Blo 491791 739817 := bstep (se 2 (by rfl) ⟨277431, by rfl⟩ : syracuseStep 739817 = 554863) B554863
theorem B5786255 : Blo 491791 5786255 := bstep (se 1 (by rfl) ⟨4339691, by rfl⟩ : syracuseStep 5786255 = 8679383) B8679383
theorem B740489 : Blo 491791 740489 := bstep (se 2 (by rfl) ⟨277683, by rfl⟩ : syracuseStep 740489 = 555367) B555367
theorem B740543 : Blo 491791 740543 := bstep (se 1 (by rfl) ⟨555407, by rfl⟩ : syracuseStep 740543 = 1110815) B1110815
theorem B9653593 : Blo 491791 9653593 := bstep (se 2 (by rfl) ⟨3620097, by rfl⟩ : syracuseStep 9653593 = 7240195) B7240195
theorem B2805101 : Blo 491791 2805101 := bstep (se 3 (by rfl) ⟨525956, by rfl⟩ : syracuseStep 2805101 = 1051913) B1051913
theorem B741353 : Blo 491791 741353 := bstep (se 2 (by rfl) ⟨278007, by rfl⟩ : syracuseStep 741353 = 556015) B556015
theorem B741407 : Blo 491791 741407 := bstep (se 1 (by rfl) ⟨556055, by rfl⟩ : syracuseStep 741407 = 1112111) B1112111
theorem B3002447 : Blo 491791 3002447 := bstep (se 1 (by rfl) ⟨2251835, by rfl⟩ : syracuseStep 3002447 = 4503671) B4503671
theorem B2675111 : Blo 491791 2675111 := bstep (se 1 (by rfl) ⟨2006333, by rfl⟩ : syracuseStep 2675111 = 4012667) B4012667
theorem B276976259 : Blo 491791 276976259 := bstep (se 1 (by rfl) ⟨207732194, by rfl⟩ : syracuseStep 276976259 = 415464389) B415464389
theorem B742055 : Blo 491791 742055 := bstep (se 1 (by rfl) ⟨556541, by rfl⟩ : syracuseStep 742055 = 1113083) B1113083
theorem B13554479 : Blo 491791 13554479 := bstep (se 1 (by rfl) ⟨10165859, by rfl⟩ : syracuseStep 13554479 = 20331719) B20331719
theorem B939271 : Blo 491791 939271 := bstep (se 1 (by rfl) ⟨704453, by rfl⟩ : syracuseStep 939271 = 1408907) B1408907
theorem B742727 : Blo 491791 742727 := bstep (se 1 (by rfl) ⟨557045, by rfl⟩ : syracuseStep 742727 = 1114091) B1114091
theorem B7099721 : Blo 491791 7099721 := bstep (se 2 (by rfl) ⟨2662395, by rfl⟩ : syracuseStep 7099721 = 5324791) B5324791
theorem B3200411 : Blo 491791 3200411 := bstep (se 1 (by rfl) ⟨2400308, by rfl⟩ : syracuseStep 3200411 = 4800617) B4800617
theorem B939431 : Blo 491791 939431 := bstep (se 1 (by rfl) ⟨704573, by rfl⟩ : syracuseStep 939431 = 1409147) B1409147
theorem B1660391 : Blo 491791 1660391 := bstep (se 1 (by rfl) ⟨1245293, by rfl⟩ : syracuseStep 1660391 = 2490587) B2490587
theorem B8411201 : Blo 491791 8411201 := bstep (se 2 (by rfl) ⟨3154200, by rfl⟩ : syracuseStep 8411201 = 6308401) B6308401
theorem B743591 : Blo 491791 743591 := bstep (se 1 (by rfl) ⟨557693, by rfl⟩ : syracuseStep 743591 = 1115387) B1115387
theorem B14245571 : Blo 491791 14245571 := bstep (se 1 (by rfl) ⟨10684178, by rfl⟩ : syracuseStep 14245571 = 21368357) B21368357
theorem B2678467 : Blo 491791 2678467 := bstep (se 1 (by rfl) ⟨2008850, by rfl⟩ : syracuseStep 2678467 = 4017701) B4017701
theorem B3760667 : Blo 491791 3760667 := bstep (se 1 (by rfl) ⟨2820500, by rfl⟩ : syracuseStep 3760667 = 5641001) B5641001
theorem B1107071 : Blo 491791 1107071 := bstep (se 1 (by rfl) ⟨830303, by rfl⟩ : syracuseStep 1107071 = 1660607) B1660607
theorem B1107179 : Blo 491791 1107179 := bstep (se 1 (by rfl) ⟨830384, by rfl⟩ : syracuseStep 1107179 = 1660769) B1660769
theorem B3761639 : Blo 491791 3761639 := bstep (se 1 (by rfl) ⟨2821229, by rfl⟩ : syracuseStep 3761639 = 5642459) B5642459
theorem B1664495 : Blo 491791 1664495 := bstep (se 1 (by rfl) ⟨1248371, by rfl⟩ : syracuseStep 1664495 = 2496743) B2496743
theorem B1402505 : Blo 491791 1402505 := bstep (se 2 (by rfl) ⟨525939, by rfl⟩ : syracuseStep 1402505 = 1051879) B1051879
theorem B2255339 : Blo 491791 2255339 := bstep (se 1 (by rfl) ⟨1691504, by rfl⟩ : syracuseStep 2255339 = 3383009) B3383009
theorem B2026145 : Blo 491791 2026145 := bstep (se 2 (by rfl) ⟨759804, by rfl⟩ : syracuseStep 2026145 = 1519609) B1519609
theorem B1109609 : Blo 491791 1109609 := bstep (se 2 (by rfl) ⟨416103, by rfl⟩ : syracuseStep 1109609 = 832207) B832207
theorem B1666871 : Blo 491791 1666871 := bstep (se 1 (by rfl) ⟨1250153, by rfl⟩ : syracuseStep 1666871 = 2500307) B2500307
theorem B1109951 : Blo 491791 1109951 := bstep (se 1 (by rfl) ⟨832463, by rfl⟩ : syracuseStep 1109951 = 1664927) B1664927
theorem B1110311 : Blo 491791 1110311 := bstep (se 1 (by rfl) ⟨832733, by rfl⟩ : syracuseStep 1110311 = 1665467) B1665467
theorem B8450567 : Blo 491791 8450567 := bstep (se 1 (by rfl) ⟨6337925, by rfl⟩ : syracuseStep 8450567 = 12675851) B12675851
theorem B6746759 : Blo 491791 6746759 := bstep (se 1 (by rfl) ⟨5060069, by rfl⟩ : syracuseStep 6746759 = 10120139) B10120139
theorem B1110905 : Blo 491791 1110905 := bstep (se 2 (by rfl) ⟨416589, by rfl⟩ : syracuseStep 1110905 = 833179) B833179
theorem B1407289 : Blo 491791 1407289 := bstep (se 2 (by rfl) ⟨527733, by rfl⟩ : syracuseStep 1407289 = 1055467) B1055467
theorem B1899001 : Blo 491791 1899001 := bstep (se 2 (by rfl) ⟨712125, by rfl⟩ : syracuseStep 1899001 = 1424251) B1424251
theorem B8419949 : Blo 491791 8419949 := bstep (se 3 (by rfl) ⟨1578740, by rfl⟩ : syracuseStep 8419949 = 3157481) B3157481
theorem B1669787 : Blo 491791 1669787 := bstep (se 1 (by rfl) ⟨1252340, by rfl⟩ : syracuseStep 1669787 = 2504681) B2504681
theorem B1112903 : Blo 491791 1112903 := bstep (se 1 (by rfl) ⟨834677, by rfl⟩ : syracuseStep 1112903 = 1669355) B1669355
theorem B1014751 : Blo 491791 1014751 := bstep (se 1 (by rfl) ⟨761063, by rfl⟩ : syracuseStep 1014751 = 1522127) B1522127
theorem B5635169 : Blo 491791 5635169 := bstep (se 2 (by rfl) ⟨2113188, by rfl⟩ : syracuseStep 5635169 = 4226377) B4226377
theorem B556159 : Blo 491791 556159 := bstep (se 1 (by rfl) ⟨417119, by rfl⟩ : syracuseStep 556159 = 834239) B834239
theorem B13172183 : Blo 491791 13172183 := bstep (se 1 (by rfl) ⟨9879137, by rfl⟩ : syracuseStep 13172183 = 19758275) B19758275
theorem B1670975 : Blo 491791 1670975 := bstep (se 1 (by rfl) ⟨1253231, by rfl⟩ : syracuseStep 1670975 = 2506463) B2506463
theorem B4554947 : Blo 491791 4554947 := bstep (se 1 (by rfl) ⟨3416210, by rfl⟩ : syracuseStep 4554947 = 6832421) B6832421
theorem B491879 : Blo 491791 491879 := bstep (se 1 (by rfl) ⟨368909, by rfl⟩ : syracuseStep 491879 = 737819) B737819
theorem B492543 : Blo 491791 492543 := bstep (se 1 (by rfl) ⟨369407, by rfl⟩ : syracuseStep 492543 = 738815) B738815
theorem B492647 : Blo 491791 492647 := bstep (se 1 (by rfl) ⟨369485, by rfl⟩ : syracuseStep 492647 = 738971) B738971
theorem B1115495 : Blo 491791 1115495 := bstep (se 1 (by rfl) ⟨836621, by rfl⟩ : syracuseStep 1115495 = 1673243) B1673243
theorem B493103 : Blo 491791 493103 := bstep (se 1 (by rfl) ⟨369827, by rfl⟩ : syracuseStep 493103 = 739655) B739655
theorem B1672811 : Blo 491791 1672811 := bstep (se 1 (by rfl) ⟨1254608, by rfl⟩ : syracuseStep 1672811 = 2509217) B2509217
theorem B493211 : Blo 491791 493211 := bstep (se 1 (by rfl) ⟨369908, by rfl⟩ : syracuseStep 493211 = 739817) B739817
theorem B493659 : Blo 491791 493659 := bstep (se 1 (by rfl) ⟨370244, by rfl⟩ : syracuseStep 493659 = 740489) B740489
theorem B493695 : Blo 491791 493695 := bstep (se 1 (by rfl) ⟨370271, by rfl⟩ : syracuseStep 493695 = 740543) B740543
theorem B3737825 : Blo 491791 3737825 := bstep (se 2 (by rfl) ⟨1401684, by rfl⟩ : syracuseStep 3737825 = 2803369) B2803369
theorem B1870067 : Blo 491791 1870067 := bstep (se 1 (by rfl) ⟨1402550, by rfl⟩ : syracuseStep 1870067 = 2805101) B2805101
theorem B494235 : Blo 491791 494235 := bstep (se 1 (by rfl) ⟨370676, by rfl⟩ : syracuseStep 494235 = 741353) B741353
theorem B494271 : Blo 491791 494271 := bstep (se 1 (by rfl) ⟨370703, by rfl⟩ : syracuseStep 494271 = 741407) B741407
theorem B184650839 : Blo 491791 184650839 := bstep (se 1 (by rfl) ⟨138488129, by rfl⟩ : syracuseStep 184650839 = 276976259) B276976259
theorem B494703 : Blo 491791 494703 := bstep (se 1 (by rfl) ⟨371027, by rfl⟩ : syracuseStep 494703 = 742055) B742055
theorem B1183211 : Blo 491791 1183211 := bstep (se 1 (by rfl) ⟨887408, by rfl⟩ : syracuseStep 1183211 = 1774817) B1774817
theorem B495151 : Blo 491791 495151 := bstep (se 1 (by rfl) ⟨371363, by rfl⟩ : syracuseStep 495151 = 742727) B742727
theorem B2133607 : Blo 491791 2133607 := bstep (se 1 (by rfl) ⟨1600205, by rfl⟩ : syracuseStep 2133607 = 3200411) B3200411
theorem B626287 : Blo 491791 626287 := bstep (se 1 (by rfl) ⟨469715, by rfl⟩ : syracuseStep 626287 = 939431) B939431
theorem B1576577 : Blo 491791 1576577 := bstep (se 2 (by rfl) ⟨591216, by rfl⟩ : syracuseStep 1576577 = 1182433) B1182433
theorem B5607467 : Blo 491791 5607467 := bstep (se 1 (by rfl) ⟨4205600, by rfl⟩ : syracuseStep 5607467 = 8411201) B8411201
theorem B495727 : Blo 491791 495727 := bstep (se 1 (by rfl) ⟨371795, by rfl⟩ : syracuseStep 495727 = 743591) B743591
theorem B4002415 : Blo 491791 4002415 := bstep (se 1 (by rfl) ⟨3001811, by rfl⟩ : syracuseStep 4002415 = 6003623) B6003623
theorem B20189837 : Blo 491791 20189837 := bstep (se 3 (by rfl) ⟨3785594, by rfl⟩ : syracuseStep 20189837 = 7571189) B7571189
theorem B1250255 : Blo 491791 1250255 := bstep (se 1 (by rfl) ⟨937691, by rfl⟩ : syracuseStep 1250255 = 1875383) B1875383
theorem B5412005 : Blo 491791 5412005 := bstep (se 4 (by rfl) ⟨507375, by rfl⟩ : syracuseStep 5412005 = 1014751) B1014751
theorem B1252361 : Blo 491791 1252361 := bstep (se 2 (by rfl) ⟨469635, by rfl⟩ : syracuseStep 1252361 = 939271) B939271
theorem B1350763 : Blo 491791 1350763 := bstep (se 1 (by rfl) ⟨1013072, by rfl⟩ : syracuseStep 1350763 = 2026145) B2026145
theorem B3153563 : Blo 491791 3153563 := bstep (se 1 (by rfl) ⟨2365172, by rfl⟩ : syracuseStep 3153563 = 4730345) B4730345
theorem B8134319 : Blo 491791 8134319 := bstep (se 1 (by rfl) ⟨6100739, by rfl⟩ : syracuseStep 8134319 = 12201479) B12201479
theorem B1056655 : Blo 491791 1056655 := bstep (se 1 (by rfl) ⟨792491, by rfl⟩ : syracuseStep 1056655 = 1584983) B1584983
theorem B1056731 : Blo 491791 1056731 := bstep (se 1 (by rfl) ⟨792548, by rfl⟩ : syracuseStep 1056731 = 1585097) B1585097
theorem B1876385 : Blo 491791 1876385 := bstep (se 2 (by rfl) ⟨703644, by rfl⟩ : syracuseStep 1876385 = 1407289) B1407289
theorem B4497839 : Blo 491791 4497839 := bstep (se 1 (by rfl) ⟨3373379, by rfl⟩ : syracuseStep 4497839 = 6746759) B6746759
theorem B2499011 : Blo 491791 2499011 := bstep (se 1 (by rfl) ⟨1874258, by rfl⟩ : syracuseStep 2499011 = 3748517) B3748517
theorem B532975 : Blo 491791 532975 := bstep (se 1 (by rfl) ⟨399731, by rfl⟩ : syracuseStep 532975 = 799463) B799463
theorem B21897839 : Blo 491791 21897839 := bstep (se 1 (by rfl) ⟨16423379, by rfl⟩ : syracuseStep 21897839 = 32846759) B32846759
theorem B2532001 : Blo 491791 2532001 := bstep (se 2 (by rfl) ⟨949500, by rfl⟩ : syracuseStep 2532001 = 1899001) B1899001
theorem B5645375 : Blo 491791 5645375 := bstep (se 1 (by rfl) ⟨4234031, by rfl⟩ : syracuseStep 5645375 = 8468063) B8468063
theorem B2106971 : Blo 491791 2106971 := bstep (se 1 (by rfl) ⟨1580228, by rfl⟩ : syracuseStep 2106971 = 3160457) B3160457
theorem B5613299 : Blo 491791 5613299 := bstep (se 1 (by rfl) ⟨4209974, by rfl⟩ : syracuseStep 5613299 = 8419949) B8419949
theorem B8006525 : Blo 491791 8006525 := bstep (se 3 (by rfl) ⟨1501223, by rfl⟩ : syracuseStep 8006525 = 3002447) B3002447
theorem B5778383 : Blo 491791 5778383 := bstep (se 1 (by rfl) ⟨4333787, by rfl⟩ : syracuseStep 5778383 = 8667575) B8667575
theorem B4500641 : Blo 491791 4500641 := bstep (se 2 (by rfl) ⟨1687740, by rfl⟩ : syracuseStep 4500641 = 3375481) B3375481
theorem B4205843 : Blo 491791 4205843 := bstep (se 1 (by rfl) ⟨3154382, by rfl⟩ : syracuseStep 4205843 = 6308765) B6308765
theorem B1814663 : Blo 491791 1814663 := bstep (se 1 (by rfl) ⟨1360997, by rfl⟩ : syracuseStep 1814663 = 2721995) B2721995
theorem B832187 : Blo 491791 832187 := bstep (se 1 (by rfl) ⟨624140, by rfl⟩ : syracuseStep 832187 = 1248281) B1248281
theorem B9024641 : Blo 491791 9024641 := bstep (se 2 (by rfl) ⟨3384240, by rfl⟩ : syracuseStep 9024641 = 6768481) B6768481
theorem B832889 : Blo 491791 832889 := bstep (se 2 (by rfl) ⟨312333, by rfl⟩ : syracuseStep 832889 = 624667) B624667
theorem B833449 : Blo 491791 833449 := bstep (se 2 (by rfl) ⟨312543, by rfl⟩ : syracuseStep 833449 = 625087) B625087
theorem B3553321 : Blo 491791 3553321 := bstep (se 2 (by rfl) ⟨1332495, by rfl⟩ : syracuseStep 3553321 = 2664991) B2664991
theorem B4733147 : Blo 491791 4733147 := bstep (se 1 (by rfl) ⟨3549860, by rfl⟩ : syracuseStep 4733147 = 7099721) B7099721
theorem B834151 : Blo 491791 834151 := bstep (se 1 (by rfl) ⟨625613, by rfl⟩ : syracuseStep 834151 = 1251227) B1251227
theorem B6306761 : Blo 491791 6306761 := bstep (se 2 (by rfl) ⟨2365035, by rfl⟩ : syracuseStep 6306761 = 4730071) B4730071
theorem B10861523 : Blo 491791 10861523 := bstep (se 1 (by rfl) ⟨8146142, by rfl⟩ : syracuseStep 10861523 = 16292285) B16292285
theorem B834799 : Blo 491791 834799 := bstep (se 1 (by rfl) ⟨626099, by rfl⟩ : syracuseStep 834799 = 1252199) B1252199
theorem B835177 : Blo 491791 835177 := bstep (se 2 (by rfl) ⟨313191, by rfl⟩ : syracuseStep 835177 = 626383) B626383
theorem B2670509 : Blo 491791 2670509 := bstep (se 3 (by rfl) ⟨500720, by rfl⟩ : syracuseStep 2670509 = 1001441) B1001441
theorem B2507111 : Blo 491791 2507111 := bstep (se 1 (by rfl) ⟨1880333, by rfl⟩ : syracuseStep 2507111 = 3760667) B3760667
theorem B738047 : Blo 491791 738047 := bstep (se 1 (by rfl) ⟨553535, by rfl⟩ : syracuseStep 738047 = 1107071) B1107071
theorem B738119 : Blo 491791 738119 := bstep (se 1 (by rfl) ⟨553589, by rfl⟩ : syracuseStep 738119 = 1107179) B1107179
theorem B2507759 : Blo 491791 2507759 := bstep (se 1 (by rfl) ⟨1880819, by rfl⟩ : syracuseStep 2507759 = 3761639) B3761639
theorem B935003 : Blo 491791 935003 := bstep (se 1 (by rfl) ⟨701252, by rfl⟩ : syracuseStep 935003 = 1402505) B1402505
theorem B6309737 : Blo 491791 6309737 := bstep (se 2 (by rfl) ⟨2366151, by rfl⟩ : syracuseStep 6309737 = 4732303) B4732303
theorem B2410399 : Blo 491791 2410399 := bstep (se 1 (by rfl) ⟨1807799, by rfl⟩ : syracuseStep 2410399 = 3615599) B3615599
theorem B739739 : Blo 491791 739739 := bstep (se 1 (by rfl) ⟨554804, by rfl⟩ : syracuseStep 739739 = 1109609) B1109609
theorem B1690055 : Blo 491791 1690055 := bstep (se 1 (by rfl) ⟨1267541, by rfl⟩ : syracuseStep 1690055 = 2535083) B2535083
theorem B739967 : Blo 491791 739967 := bstep (se 1 (by rfl) ⟨554975, by rfl⟩ : syracuseStep 739967 = 1109951) B1109951
theorem B740207 : Blo 491791 740207 := bstep (se 1 (by rfl) ⟨555155, by rfl⟩ : syracuseStep 740207 = 1110311) B1110311
theorem B740603 : Blo 491791 740603 := bstep (se 1 (by rfl) ⟨555452, by rfl⟩ : syracuseStep 740603 = 1110905) B1110905
theorem B741545 : Blo 491791 741545 := bstep (se 2 (by rfl) ⟨278079, by rfl⟩ : syracuseStep 741545 = 556159) B556159
theorem B741935 : Blo 491791 741935 := bstep (se 1 (by rfl) ⟨556451, by rfl⟩ : syracuseStep 741935 = 1112903) B1112903
theorem B3756779 : Blo 491791 3756779 := bstep (se 1 (by rfl) ⟨2817584, by rfl⟩ : syracuseStep 3756779 = 5635169) B5635169
theorem B1332755 : Blo 491791 1332755 := bstep (se 1 (by rfl) ⟨999566, by rfl⟩ : syracuseStep 1332755 = 1999133) B1999133
theorem B742967 : Blo 491791 742967 := bstep (se 1 (by rfl) ⟨557225, by rfl⟩ : syracuseStep 742967 = 1114451) B1114451
theorem B1660499 : Blo 491791 1660499 := bstep (se 1 (by rfl) ⟨1245374, by rfl⟩ : syracuseStep 1660499 = 2490749) B2490749
theorem B2021449 : Blo 491791 2021449 := bstep (se 2 (by rfl) ⟨758043, by rfl⟩ : syracuseStep 2021449 = 1516087) B1516087
theorem B7133629 : Blo 491791 7133629 := bstep (se 3 (by rfl) ⟨1337555, by rfl⟩ : syracuseStep 7133629 = 2675111) B2675111
theorem B3857503 : Blo 491791 3857503 := bstep (se 1 (by rfl) ⟨2893127, by rfl⟩ : syracuseStep 3857503 = 5786255) B5786255
theorem B941215 : Blo 491791 941215 := bstep (se 1 (by rfl) ⟨705911, by rfl⟩ : syracuseStep 941215 = 1411823) B1411823
theorem B1662443 : Blo 491791 1662443 := bstep (se 1 (by rfl) ⟨1246832, by rfl⟩ : syracuseStep 1662443 = 2493665) B2493665
theorem B7135361 : Blo 491791 7135361 := bstep (se 2 (by rfl) ⟨2675760, by rfl⟩ : syracuseStep 7135361 = 5351521) B5351521
theorem B9036319 : Blo 491791 9036319 := bstep (se 1 (by rfl) ⟨6777239, by rfl⟩ : syracuseStep 9036319 = 13554479) B13554479
theorem B1663631 : Blo 491791 1663631 := bstep (se 1 (by rfl) ⟨1247723, by rfl⟩ : syracuseStep 1663631 = 2495447) B2495447
theorem B1401799 : Blo 491791 1401799 := bstep (se 1 (by rfl) ⟨1051349, by rfl⟩ : syracuseStep 1401799 = 2102699) B2102699
theorem B1106927 : Blo 491791 1106927 := bstep (se 1 (by rfl) ⟨830195, by rfl⟩ : syracuseStep 1106927 = 1660391) B1660391
theorem B1664603 : Blo 491791 1664603 := bstep (se 1 (by rfl) ⟨1248452, by rfl⟩ : syracuseStep 1664603 = 2496905) B2496905
theorem B12871457 : Blo 491791 12871457 := bstep (se 2 (by rfl) ⟨4826796, by rfl⟩ : syracuseStep 12871457 = 9653593) B9653593
theorem B1403041 : Blo 491791 1403041 := bstep (se 2 (by rfl) ⟨526140, by rfl⟩ : syracuseStep 1403041 = 1052281) B1052281
theorem B1665359 : Blo 491791 1665359 := bstep (se 1 (by rfl) ⟨1249019, by rfl⟩ : syracuseStep 1665359 = 2498039) B2498039
theorem B9497047 : Blo 491791 9497047 := bstep (se 1 (by rfl) ⟨7122785, by rfl⟩ : syracuseStep 9497047 = 14245571) B14245571
theorem B5401259 : Blo 491791 5401259 := bstep (se 1 (by rfl) ⟨4050944, by rfl⟩ : syracuseStep 5401259 = 8101889) B8101889
theorem B1109663 : Blo 491791 1109663 := bstep (se 1 (by rfl) ⟨832247, by rfl⟩ : syracuseStep 1109663 = 1664495) B1664495
theorem B5632253 : Blo 491791 5632253 := bstep (se 3 (by rfl) ⟨1056047, by rfl⟩ : syracuseStep 5632253 = 2112095) B2112095
theorem B1503559 : Blo 491791 1503559 := bstep (se 1 (by rfl) ⟨1127669, by rfl⟩ : syracuseStep 1503559 = 2255339) B2255339
theorem B1667951 : Blo 491791 1667951 := bstep (se 1 (by rfl) ⟨1250963, by rfl⟩ : syracuseStep 1667951 = 2501927) B2501927
theorem B1111247 : Blo 491791 1111247 := bstep (se 1 (by rfl) ⟨833435, by rfl⟩ : syracuseStep 1111247 = 1666871) B1666871
theorem B554215 : Blo 491791 554215 := bstep (se 1 (by rfl) ⟨415661, by rfl⟩ : syracuseStep 554215 = 831323) B831323
theorem B5633711 : Blo 491791 5633711 := bstep (se 1 (by rfl) ⟨4225283, by rfl⟩ : syracuseStep 5633711 = 8450567) B8450567
theorem B1406879 : Blo 491791 1406879 := bstep (se 1 (by rfl) ⟨1055159, by rfl⟩ : syracuseStep 1406879 = 2110319) B2110319
theorem B1669031 : Blo 491791 1669031 := bstep (se 1 (by rfl) ⟨1251773, by rfl⟩ : syracuseStep 1669031 = 2503547) B2503547
theorem B2816765 : Blo 491791 2816765 := bstep (se 3 (by rfl) ⟨528143, by rfl⟩ : syracuseStep 2816765 = 1056287) B1056287
theorem B1113191 : Blo 491791 1113191 := bstep (se 1 (by rfl) ⟨834893, by rfl⟩ : syracuseStep 1113191 = 1669787) B1669787
theorem B3571289 : Blo 491791 3571289 := bstep (se 2 (by rfl) ⟨1339233, by rfl⟩ : syracuseStep 3571289 = 2678467) B2678467
theorem B1670759 : Blo 491791 1670759 := bstep (se 1 (by rfl) ⟨1253069, by rfl⟩ : syracuseStep 1670759 = 2506139) B2506139
theorem B8781455 : Blo 491791 8781455 := bstep (se 1 (by rfl) ⟨6586091, by rfl⟩ : syracuseStep 8781455 = 13172183) B13172183
theorem B556735 : Blo 491791 556735 := bstep (se 1 (by rfl) ⟨417551, by rfl⟩ : syracuseStep 556735 = 835103) B835103
theorem B1113983 : Blo 491791 1113983 := bstep (se 1 (by rfl) ⟨835487, by rfl⟩ : syracuseStep 1113983 = 1670975) B1670975
theorem B1671407 : Blo 491791 1671407 := bstep (se 1 (by rfl) ⟨1253555, by rfl⟩ : syracuseStep 1671407 = 2507111) B2507111
theorem B492031 : Blo 491791 492031 := bstep (se 1 (by rfl) ⟨369023, by rfl⟩ : syracuseStep 492031 = 738047) B738047
theorem B492079 : Blo 491791 492079 := bstep (se 1 (by rfl) ⟨369059, by rfl⟩ : syracuseStep 492079 = 738119) B738119
theorem B1671839 : Blo 491791 1671839 := bstep (se 1 (by rfl) ⟨1253879, by rfl⟩ : syracuseStep 1671839 = 2507759) B2507759
theorem B3376001 : Blo 491791 3376001 := bstep (se 2 (by rfl) ⟨1266000, by rfl⟩ : syracuseStep 3376001 = 2532001) B2532001
theorem B1115207 : Blo 491791 1115207 := bstep (se 1 (by rfl) ⟨836405, by rfl⟩ : syracuseStep 1115207 = 1672811) B1672811
theorem B1869065 : Blo 491791 1869065 := bstep (se 2 (by rfl) ⟨700899, by rfl⟩ : syracuseStep 1869065 = 1401799) B1401799
theorem B2491883 : Blo 491791 2491883 := bstep (se 1 (by rfl) ⟨1868912, by rfl⟩ : syracuseStep 2491883 = 3737825) B3737825
theorem B1246711 : Blo 491791 1246711 := bstep (se 1 (by rfl) ⟨935033, by rfl⟩ : syracuseStep 1246711 = 1870067) B1870067
theorem B493159 : Blo 491791 493159 := bstep (se 1 (by rfl) ⟨369869, by rfl⟩ : syracuseStep 493159 = 739739) B739739
theorem B493311 : Blo 491791 493311 := bstep (se 1 (by rfl) ⟨369983, by rfl⟩ : syracuseStep 493311 = 739967) B739967
theorem B493471 : Blo 491791 493471 := bstep (se 1 (by rfl) ⟨370103, by rfl⟩ : syracuseStep 493471 = 740207) B740207
theorem B493735 : Blo 491791 493735 := bstep (se 1 (by rfl) ⟨370301, by rfl⟩ : syracuseStep 493735 = 740603) B740603
theorem B788807 : Blo 491791 788807 := bstep (se 1 (by rfl) ⟨591605, by rfl⟩ : syracuseStep 788807 = 1183211) B1183211
theorem B1051051 : Blo 491791 1051051 := bstep (se 1 (by rfl) ⟨788288, by rfl⟩ : syracuseStep 1051051 = 1576577) B1576577
theorem B3213865 : Blo 491791 3213865 := bstep (se 2 (by rfl) ⟨1205199, by rfl⟩ : syracuseStep 3213865 = 2410399) B2410399
theorem B3738311 : Blo 491791 3738311 := bstep (se 1 (by rfl) ⟨2803733, by rfl⟩ : syracuseStep 3738311 = 5607467) B5607467
theorem B494363 : Blo 491791 494363 := bstep (se 1 (by rfl) ⟨370772, by rfl⟩ : syracuseStep 494363 = 741545) B741545
theorem B1870721 : Blo 491791 1870721 := bstep (se 2 (by rfl) ⟨701520, by rfl⟩ : syracuseStep 1870721 = 1403041) B1403041
theorem B2493341 : Blo 491791 2493341 := bstep (se 3 (by rfl) ⟨467501, by rfl⟩ : syracuseStep 2493341 = 935003) B935003
theorem B494623 : Blo 491791 494623 := bstep (se 1 (by rfl) ⟨370967, by rfl⟩ : syracuseStep 494623 = 741935) B741935
theorem B3608003 : Blo 491791 3608003 := bstep (se 1 (by rfl) ⟨2706002, by rfl⟩ : syracuseStep 3608003 = 5412005) B5412005
theorem B888503 : Blo 491791 888503 := bstep (se 1 (by rfl) ⟨666377, by rfl⟩ : syracuseStep 888503 = 1332755) B1332755
theorem B495311 : Blo 491791 495311 := bstep (se 1 (by rfl) ⟨371483, by rfl⟩ : syracuseStep 495311 = 742967) B742967
theorem B2102375 : Blo 491791 2102375 := bstep (se 1 (by rfl) ⟨1576781, by rfl⟩ : syracuseStep 2102375 = 3153563) B3153563
theorem B4756907 : Blo 491791 4756907 := bstep (se 1 (by rfl) ⟨3567680, by rfl⟩ : syracuseStep 4756907 = 7135361) B7135361
theorem B1250923 : Blo 491791 1250923 := bstep (se 1 (by rfl) ⟨938192, by rfl⟩ : syracuseStep 1250923 = 1876385) B1876385
theorem B2004745 : Blo 491791 2004745 := bstep (se 2 (by rfl) ⟨751779, by rfl⟩ : syracuseStep 2004745 = 1503559) B1503559
theorem B3742199 : Blo 491791 3742199 := bstep (se 1 (by rfl) ⟨2806649, by rfl⟩ : syracuseStep 3742199 = 5613299) B5613299
theorem B2695265 : Blo 491791 2695265 := bstep (se 2 (by rfl) ⟨1010724, by rfl⟩ : syracuseStep 2695265 = 2021449) B2021449
theorem B12001709 : Blo 491791 12001709 := bstep (se 3 (by rfl) ⟨2250320, by rfl⟩ : syracuseStep 12001709 = 4500641) B4500641
theorem B9511505 : Blo 491791 9511505 := bstep (se 2 (by rfl) ⟨3566814, by rfl⟩ : syracuseStep 9511505 = 7133629) B7133629
theorem B3155431 : Blo 491791 3155431 := bstep (se 1 (by rfl) ⟨2366573, by rfl⟩ : syracuseStep 3155431 = 4733147) B4733147
theorem B1254953 : Blo 491791 1254953 := bstep (se 2 (by rfl) ⟨470607, by rfl⟩ : syracuseStep 1254953 = 941215) B941215
theorem B1877843 : Blo 491791 1877843 := bstep (se 1 (by rfl) ⟨1408382, by rfl⟩ : syracuseStep 1877843 = 2816765) B2816765
theorem B4204507 : Blo 491791 4204507 := bstep (se 1 (by rfl) ⟨3153380, by rfl⟩ : syracuseStep 4204507 = 6306761) B6306761
theorem B1780339 : Blo 491791 1780339 := bstep (se 1 (by rfl) ⟨1335254, by rfl⟩ : syracuseStep 1780339 = 2670509) B2670509
theorem B4206491 : Blo 491791 4206491 := bstep (se 1 (by rfl) ⟨3154868, by rfl⟩ : syracuseStep 4206491 = 6309737) B6309737
theorem B1126703 : Blo 491791 1126703 := bstep (se 1 (by rfl) ⟨845027, by rfl⟩ : syracuseStep 1126703 = 1690055) B1690055
theorem B2504519 : Blo 491791 2504519 := bstep (se 1 (by rfl) ⟨1878389, by rfl⟩ : syracuseStep 2504519 = 3756779) B3756779
theorem B21346213 : Blo 491791 21346213 := bstep (se 4 (by rfl) ⟨2001207, by rfl⟩ : syracuseStep 21346213 = 4002415) B4002415
theorem B12662729 : Blo 491791 12662729 := bstep (se 2 (by rfl) ⟨4748523, by rfl⟩ : syracuseStep 12662729 = 9497047) B9497047
theorem B833503 : Blo 491791 833503 := bstep (se 1 (by rfl) ⟨625127, by rfl⟩ : syracuseStep 833503 = 1250255) B1250255
theorem B834907 : Blo 491791 834907 := bstep (se 1 (by rfl) ⟨626180, by rfl⟩ : syracuseStep 834907 = 1252361) B1252361
theorem B835049 : Blo 491791 835049 := bstep (se 2 (by rfl) ⟨313143, by rfl⟩ : syracuseStep 835049 = 626287) B626287
theorem B5422879 : Blo 491791 5422879 := bstep (se 1 (by rfl) ⟨4067159, by rfl⟩ : syracuseStep 5422879 = 8134319) B8134319
theorem B2998559 : Blo 491791 2998559 := bstep (se 1 (by rfl) ⟨2248919, by rfl⟩ : syracuseStep 2998559 = 4497839) B4497839
theorem B14598559 : Blo 491791 14598559 := bstep (se 1 (by rfl) ⟨10948919, by rfl⟩ : syracuseStep 14598559 = 21897839) B21897839
theorem B737951 : Blo 491791 737951 := bstep (se 1 (by rfl) ⟨553463, by rfl⟩ : syracuseStep 737951 = 1106927) B1106927
theorem B738953 : Blo 491791 738953 := bstep (se 2 (by rfl) ⟨277107, by rfl⟩ : syracuseStep 738953 = 554215) B554215
theorem B2803895 : Blo 491791 2803895 := bstep (se 1 (by rfl) ⟨2102921, by rfl⟩ : syracuseStep 2803895 = 4205843) B4205843
theorem B739775 : Blo 491791 739775 := bstep (se 1 (by rfl) ⟨554831, by rfl⟩ : syracuseStep 739775 = 1109663) B1109663
theorem B4737761 : Blo 491791 4737761 := bstep (se 2 (by rfl) ⟨1776660, by rfl⟩ : syracuseStep 4737761 = 3553321) B3553321
theorem B3754835 : Blo 491791 3754835 := bstep (se 1 (by rfl) ⟨2816126, by rfl⟩ : syracuseStep 3754835 = 5632253) B5632253
theorem B6016427 : Blo 491791 6016427 := bstep (se 1 (by rfl) ⟨4512320, by rfl⟩ : syracuseStep 6016427 = 9024641) B9024641
theorem B740831 : Blo 491791 740831 := bstep (se 1 (by rfl) ⟨555623, by rfl⟩ : syracuseStep 740831 = 1111247) B1111247
theorem B3755807 : Blo 491791 3755807 := bstep (se 1 (by rfl) ⟨2816855, by rfl⟩ : syracuseStep 3755807 = 5633711) B5633711
theorem B937919 : Blo 491791 937919 := bstep (se 1 (by rfl) ⟨703439, by rfl⟩ : syracuseStep 937919 = 1406879) B1406879
theorem B742127 : Blo 491791 742127 := bstep (se 1 (by rfl) ⟨556595, by rfl⟩ : syracuseStep 742127 = 1113191) B1113191
theorem B742313 : Blo 491791 742313 := bstep (se 2 (by rfl) ⟨278367, by rfl⟩ : syracuseStep 742313 = 556735) B556735
theorem B2380859 : Blo 491791 2380859 := bstep (se 1 (by rfl) ⟨1785644, by rfl⟩ : syracuseStep 2380859 = 3571289) B3571289
theorem B5854303 : Blo 491791 5854303 := bstep (se 1 (by rfl) ⟨4390727, by rfl⟩ : syracuseStep 5854303 = 8781455) B8781455
theorem B742655 : Blo 491791 742655 := bstep (se 1 (by rfl) ⟨556991, by rfl⟩ : syracuseStep 742655 = 1113983) B1113983
theorem B3036631 : Blo 491791 3036631 := bstep (se 1 (by rfl) ⟨2277473, by rfl⟩ : syracuseStep 3036631 = 4554947) B4554947
theorem B4839101 : Blo 491791 4839101 := bstep (se 3 (by rfl) ⟨907331, by rfl⟩ : syracuseStep 4839101 = 1814663) B1814663
theorem B710633 : Blo 491791 710633 := bstep (se 2 (by rfl) ⟨266487, by rfl⟩ : syracuseStep 710633 = 532975) B532975
theorem B12048425 : Blo 491791 12048425 := bstep (se 2 (by rfl) ⟨4518159, by rfl⟩ : syracuseStep 12048425 = 9036319) B9036319
theorem B743663 : Blo 491791 743663 := bstep (se 1 (by rfl) ⟨557747, by rfl⟩ : syracuseStep 743663 = 1115495) B1115495
theorem B123100559 : Blo 491791 123100559 := bstep (se 1 (by rfl) ⟨92325419, by rfl⟩ : syracuseStep 123100559 = 184650839) B184650839
theorem B13459891 : Blo 491791 13459891 := bstep (se 1 (by rfl) ⟨10094918, by rfl⟩ : syracuseStep 13459891 = 20189837) B20189837
theorem B1106999 : Blo 491791 1106999 := bstep (se 1 (by rfl) ⟨830249, by rfl⟩ : syracuseStep 1106999 = 1660499) B1660499
theorem B2844809 : Blo 491791 2844809 := bstep (se 2 (by rfl) ⟨1066803, by rfl⟩ : syracuseStep 2844809 = 2133607) B2133607
theorem B1108295 : Blo 491791 1108295 := bstep (se 1 (by rfl) ⟨831221, by rfl⟩ : syracuseStep 1108295 = 1662443) B1662443
theorem B1666007 : Blo 491791 1666007 := bstep (se 1 (by rfl) ⟨1249505, by rfl⟩ : syracuseStep 1666007 = 2499011) B2499011
theorem B1109087 : Blo 491791 1109087 := bstep (se 1 (by rfl) ⟨831815, by rfl⟩ : syracuseStep 1109087 = 1663631) B1663631
theorem B7204069 : Blo 491791 7204069 := bstep (se 4 (by rfl) ⟨675381, by rfl⟩ : syracuseStep 7204069 = 1350763) B1350763
theorem B3763583 : Blo 491791 3763583 := bstep (se 1 (by rfl) ⟨2822687, by rfl⟩ : syracuseStep 3763583 = 5645375) B5645375
theorem B1109735 : Blo 491791 1109735 := bstep (se 1 (by rfl) ⟨832301, by rfl⟩ : syracuseStep 1109735 = 1664603) B1664603
theorem B1404647 : Blo 491791 1404647 := bstep (se 1 (by rfl) ⟨1053485, by rfl⟩ : syracuseStep 1404647 = 2106971) B2106971
theorem B8580971 : Blo 491791 8580971 := bstep (se 1 (by rfl) ⟨6435728, by rfl⟩ : syracuseStep 8580971 = 12871457) B12871457
theorem B1110239 : Blo 491791 1110239 := bstep (se 1 (by rfl) ⟨832679, by rfl⟩ : syracuseStep 1110239 = 1665359) B1665359
theorem B3600839 : Blo 491791 3600839 := bstep (se 1 (by rfl) ⟨2700629, by rfl⟩ : syracuseStep 3600839 = 5401259) B5401259
theorem B5337683 : Blo 491791 5337683 := bstep (se 1 (by rfl) ⟨4003262, by rfl⟩ : syracuseStep 5337683 = 8006525) B8006525
theorem B1111265 : Blo 491791 1111265 := bstep (se 2 (by rfl) ⟨416724, by rfl⟩ : syracuseStep 1111265 = 833449) B833449
theorem B554791 : Blo 491791 554791 := bstep (se 1 (by rfl) ⟨416093, by rfl⟩ : syracuseStep 554791 = 832187) B832187
theorem B1111967 : Blo 491791 1111967 := bstep (se 1 (by rfl) ⟨833975, by rfl⟩ : syracuseStep 1111967 = 1667951) B1667951
theorem B1112201 : Blo 491791 1112201 := bstep (se 2 (by rfl) ⟨417075, by rfl⟩ : syracuseStep 1112201 = 834151) B834151
theorem B555259 : Blo 491791 555259 := bstep (se 1 (by rfl) ⟨416444, by rfl⟩ : syracuseStep 555259 = 832889) B832889
theorem B1112687 : Blo 491791 1112687 := bstep (se 1 (by rfl) ⟨834515, by rfl⟩ : syracuseStep 1112687 = 1669031) B1669031
theorem B5143337 : Blo 491791 5143337 := bstep (se 2 (by rfl) ⟨1928751, by rfl⟩ : syracuseStep 5143337 = 3857503) B3857503
theorem B1113065 : Blo 491791 1113065 := bstep (se 2 (by rfl) ⟨417399, by rfl⟩ : syracuseStep 1113065 = 834799) B834799
theorem B7241015 : Blo 491791 7241015 := bstep (se 1 (by rfl) ⟨5430761, by rfl⟩ : syracuseStep 7241015 = 10861523) B10861523
theorem B1113569 : Blo 491791 1113569 := bstep (se 2 (by rfl) ⟨417588, by rfl⟩ : syracuseStep 1113569 = 835177) B835177
theorem B61636085 : Blo 491791 61636085 := bstep (se 5 (by rfl) ⟨2889191, by rfl⟩ : syracuseStep 61636085 = 5778383) B5778383
theorem B1113839 : Blo 491791 1113839 := bstep (se 1 (by rfl) ⟨835379, by rfl⟩ : syracuseStep 1113839 = 1670759) B1670759
theorem B1408873 : Blo 491791 1408873 := bstep (se 2 (by rfl) ⟨528327, by rfl⟩ : syracuseStep 1408873 = 1056655) B1056655
theorem B2817949 : Blo 491791 2817949 := bstep (se 3 (by rfl) ⟨528365, by rfl⟩ : syracuseStep 2817949 = 1056731) B1056731
theorem B1114271 : Blo 491791 1114271 := bstep (se 1 (by rfl) ⟨835703, by rfl⟩ : syracuseStep 1114271 = 1671407) B1671407
theorem B1999039 : Blo 491791 1999039 := bstep (se 1 (by rfl) ⟨1499279, by rfl⟩ : syracuseStep 1999039 = 2998559) B2998559
theorem B491967 : Blo 491791 491967 := bstep (se 1 (by rfl) ⟨368975, by rfl⟩ : syracuseStep 491967 = 737951) B737951
theorem B1114559 : Blo 491791 1114559 := bstep (se 1 (by rfl) ⟨835919, by rfl⟩ : syracuseStep 1114559 = 1671839) B1671839
theorem B19464745 : Blo 491791 19464745 := bstep (se 2 (by rfl) ⟨7299279, by rfl⟩ : syracuseStep 19464745 = 14598559) B14598559
theorem B1246043 : Blo 491791 1246043 := bstep (se 1 (by rfl) ⟨934532, by rfl⟩ : syracuseStep 1246043 = 1869065) B1869065
theorem B492635 : Blo 491791 492635 := bstep (se 1 (by rfl) ⟨369476, by rfl⟩ : syracuseStep 492635 = 738953) B738953
theorem B1869263 : Blo 491791 1869263 := bstep (se 1 (by rfl) ⟨1401947, by rfl⟩ : syracuseStep 1869263 = 2803895) B2803895
theorem B525871 : Blo 491791 525871 := bstep (se 1 (by rfl) ⟨394403, by rfl⟩ : syracuseStep 525871 = 788807) B788807
theorem B493183 : Blo 491791 493183 := bstep (se 1 (by rfl) ⟨369887, by rfl⟩ : syracuseStep 493183 = 739775) B739775
theorem B2492207 : Blo 491791 2492207 := bstep (se 1 (by rfl) ⟨1869155, by rfl⟩ : syracuseStep 2492207 = 3738311) B3738311
theorem B1247147 : Blo 491791 1247147 := bstep (se 1 (by rfl) ⟨935360, by rfl⟩ : syracuseStep 1247147 = 1870721) B1870721
theorem B493887 : Blo 491791 493887 := bstep (se 1 (by rfl) ⟨370415, by rfl⟩ : syracuseStep 493887 = 740831) B740831
theorem B5606009 : Blo 491791 5606009 := bstep (se 2 (by rfl) ⟨2102253, by rfl⟩ : syracuseStep 5606009 = 4204507) B4204507
theorem B494751 : Blo 491791 494751 := bstep (se 1 (by rfl) ⟨371063, by rfl⟩ : syracuseStep 494751 = 742127) B742127
theorem B494875 : Blo 491791 494875 := bstep (se 1 (by rfl) ⟨371156, by rfl⟩ : syracuseStep 494875 = 742313) B742313
theorem B495103 : Blo 491791 495103 := bstep (se 1 (by rfl) ⟨371327, by rfl⟩ : syracuseStep 495103 = 742655) B742655
theorem B8032283 : Blo 491791 8032283 := bstep (se 1 (by rfl) ⟨6024212, by rfl⟩ : syracuseStep 8032283 = 12048425) B12048425
theorem B495775 : Blo 491791 495775 := bstep (se 1 (by rfl) ⟨371831, by rfl⟩ : syracuseStep 495775 = 743663) B743663
theorem B9605425 : Blo 491791 9605425 := bstep (se 2 (by rfl) ⟨3602034, by rfl⟩ : syracuseStep 9605425 = 7204069) B7204069
theorem B2494799 : Blo 491791 2494799 := bstep (se 1 (by rfl) ⟨1871099, by rfl⟩ : syracuseStep 2494799 = 3742199) B3742199
theorem B1251895 : Blo 491791 1251895 := bstep (se 1 (by rfl) ⟨938921, by rfl⟩ : syracuseStep 1251895 = 1877843) B1877843
theorem B7805737 : Blo 491791 7805737 := bstep (se 2 (by rfl) ⟨2927151, by rfl⟩ : syracuseStep 7805737 = 5854303) B5854303
theorem B2400559 : Blo 491791 2400559 := bstep (se 1 (by rfl) ⟨1800419, by rfl⟩ : syracuseStep 2400559 = 3600839) B3600839
theorem B19309373 : Blo 491791 19309373 := bstep (se 3 (by rfl) ⟨3620507, by rfl⟩ : syracuseStep 19309373 = 7241015) B7241015
theorem B2369341 : Blo 491791 2369341 := bstep (se 3 (by rfl) ⟨444251, by rfl⟩ : syracuseStep 2369341 = 888503) B888503
theorem B1878497 : Blo 491791 1878497 := bstep (se 2 (by rfl) ⟨704436, by rfl⟩ : syracuseStep 1878497 = 1408873) B1408873
theorem B2501117 : Blo 491791 2501117 := bstep (se 3 (by rfl) ⟨468959, by rfl⟩ : syracuseStep 2501117 = 937919) B937919
theorem B3158507 : Blo 491791 3158507 := bstep (se 1 (by rfl) ⟨2368880, by rfl⟩ : syracuseStep 3158507 = 4737761) B4737761
theorem B2503223 : Blo 491791 2503223 := bstep (se 1 (by rfl) ⟨1877417, by rfl⟩ : syracuseStep 2503223 = 3754835) B3754835
theorem B4207241 : Blo 491791 4207241 := bstep (se 2 (by rfl) ⟨1577715, by rfl⟩ : syracuseStep 4207241 = 3155431) B3155431
theorem B4010951 : Blo 491791 4010951 := bstep (se 1 (by rfl) ⟨3008213, by rfl⟩ : syracuseStep 4010951 = 6016427) B6016427
theorem B2405335 : Blo 491791 2405335 := bstep (se 1 (by rfl) ⟨1804001, by rfl⟩ : syracuseStep 2405335 = 3608003) B3608003
theorem B2503871 : Blo 491791 2503871 := bstep (se 1 (by rfl) ⟨1877903, by rfl⟩ : syracuseStep 2503871 = 3755807) B3755807
theorem B1587239 : Blo 491791 1587239 := bstep (se 1 (by rfl) ⟨1190429, by rfl⟩ : syracuseStep 1587239 = 2380859) B2380859
theorem B2373785 : Blo 491791 2373785 := bstep (se 2 (by rfl) ⟨890169, by rfl⟩ : syracuseStep 2373785 = 1780339) B1780339
theorem B3226067 : Blo 491791 3226067 := bstep (se 1 (by rfl) ⟨2419550, by rfl⟩ : syracuseStep 3226067 = 4839101) B4839101
theorem B82067039 : Blo 491791 82067039 := bstep (se 1 (by rfl) ⟨61550279, by rfl⟩ : syracuseStep 82067039 = 123100559) B123100559
theorem B6341003 : Blo 491791 6341003 := bstep (se 1 (by rfl) ⟨4755752, by rfl⟩ : syracuseStep 6341003 = 9511505) B9511505
theorem B737999 : Blo 491791 737999 := bstep (se 1 (by rfl) ⟨553499, by rfl⟩ : syracuseStep 737999 = 1106999) B1106999
theorem B836635 : Blo 491791 836635 := bstep (se 1 (by rfl) ⟨627476, by rfl⟩ : syracuseStep 836635 = 1254953) B1254953
theorem B738863 : Blo 491791 738863 := bstep (se 1 (by rfl) ⟨554147, by rfl⟩ : syracuseStep 738863 = 1108295) B1108295
theorem B4048841 : Blo 491791 4048841 := bstep (se 2 (by rfl) ⟨1518315, by rfl⟩ : syracuseStep 4048841 = 3036631) B3036631
theorem B739391 : Blo 491791 739391 := bstep (se 1 (by rfl) ⟨554543, by rfl⟩ : syracuseStep 739391 = 1109087) B1109087
theorem B2509055 : Blo 491791 2509055 := bstep (se 1 (by rfl) ⟨1881791, by rfl⟩ : syracuseStep 2509055 = 3763583) B3763583
theorem B2672993 : Blo 491791 2672993 := bstep (se 2 (by rfl) ⟨1002372, by rfl⟩ : syracuseStep 2672993 = 2004745) B2004745
theorem B739721 : Blo 491791 739721 := bstep (se 2 (by rfl) ⟨277395, by rfl⟩ : syracuseStep 739721 = 554791) B554791
theorem B739823 : Blo 491791 739823 := bstep (se 1 (by rfl) ⟨554867, by rfl⟩ : syracuseStep 739823 = 1109735) B1109735
theorem B936431 : Blo 491791 936431 := bstep (se 1 (by rfl) ⟨702323, by rfl⟩ : syracuseStep 936431 = 1404647) B1404647
theorem B28461617 : Blo 491791 28461617 := bstep (se 2 (by rfl) ⟨10673106, by rfl⟩ : syracuseStep 28461617 = 21346213) B21346213
theorem B5720647 : Blo 491791 5720647 := bstep (se 1 (by rfl) ⟨4290485, by rfl⟩ : syracuseStep 5720647 = 8580971) B8580971
theorem B2804327 : Blo 491791 2804327 := bstep (se 1 (by rfl) ⟨2103245, by rfl⟩ : syracuseStep 2804327 = 4206491) B4206491
theorem B740159 : Blo 491791 740159 := bstep (se 1 (by rfl) ⟨555119, by rfl⟩ : syracuseStep 740159 = 1110239) B1110239
theorem B740345 : Blo 491791 740345 := bstep (se 2 (by rfl) ⟨277629, by rfl⟩ : syracuseStep 740345 = 555259) B555259
theorem B3558455 : Blo 491791 3558455 := bstep (se 1 (by rfl) ⟨2668841, by rfl⟩ : syracuseStep 3558455 = 5337683) B5337683
theorem B740843 : Blo 491791 740843 := bstep (se 1 (by rfl) ⟨555632, by rfl⟩ : syracuseStep 740843 = 1111265) B1111265
theorem B741311 : Blo 491791 741311 := bstep (se 1 (by rfl) ⟨555983, by rfl⟩ : syracuseStep 741311 = 1111967) B1111967
theorem B8441819 : Blo 491791 8441819 := bstep (se 1 (by rfl) ⟨6331364, by rfl⟩ : syracuseStep 8441819 = 12662729) B12662729
theorem B741467 : Blo 491791 741467 := bstep (se 1 (by rfl) ⟨556100, by rfl⟩ : syracuseStep 741467 = 1112201) B1112201
theorem B741791 : Blo 491791 741791 := bstep (se 1 (by rfl) ⟨556343, by rfl⟩ : syracuseStep 741791 = 1112687) B1112687
theorem B3428891 : Blo 491791 3428891 := bstep (se 1 (by rfl) ⟨2571668, by rfl⟩ : syracuseStep 3428891 = 5143337) B5143337
theorem B742043 : Blo 491791 742043 := bstep (se 1 (by rfl) ⟨556532, by rfl⟩ : syracuseStep 742043 = 1113065) B1113065
theorem B742379 : Blo 491791 742379 := bstep (se 1 (by rfl) ⟨556784, by rfl⟩ : syracuseStep 742379 = 1113569) B1113569
theorem B7230505 : Blo 491791 7230505 := bstep (se 2 (by rfl) ⟨2711439, by rfl⟩ : syracuseStep 7230505 = 5422879) B5422879
theorem B742559 : Blo 491791 742559 := bstep (se 1 (by rfl) ⟨556919, by rfl⟩ : syracuseStep 742559 = 1113839) B1113839
theorem B3757265 : Blo 491791 3757265 := bstep (se 2 (by rfl) ⟨1408974, by rfl⟩ : syracuseStep 3757265 = 2817949) B2817949
theorem B17946521 : Blo 491791 17946521 := bstep (se 2 (by rfl) ⟨6729945, by rfl⟩ : syracuseStep 17946521 = 13459891) B13459891
theorem B2250667 : Blo 491791 2250667 := bstep (se 1 (by rfl) ⟨1688000, by rfl⟩ : syracuseStep 2250667 = 3376001) B3376001
theorem B743471 : Blo 491791 743471 := bstep (se 1 (by rfl) ⟨557603, by rfl⟩ : syracuseStep 743471 = 1115207) B1115207
theorem B1661255 : Blo 491791 1661255 := bstep (se 1 (by rfl) ⟨1245941, by rfl⟩ : syracuseStep 1661255 = 2491883) B2491883
theorem B32004557 : Blo 491791 32004557 := bstep (se 3 (by rfl) ⟨6000854, by rfl⟩ : syracuseStep 32004557 = 12001709) B12001709
theorem B1662227 : Blo 491791 1662227 := bstep (se 1 (by rfl) ⟨1246670, by rfl⟩ : syracuseStep 1662227 = 2493341) B2493341
theorem B1662281 : Blo 491791 1662281 := bstep (se 2 (by rfl) ⟨623355, by rfl⟩ : syracuseStep 1662281 = 1246711) B1246711
theorem B1401401 : Blo 491791 1401401 := bstep (se 2 (by rfl) ⟨525525, by rfl⟩ : syracuseStep 1401401 = 1051051) B1051051
theorem B4285153 : Blo 491791 4285153 := bstep (se 2 (by rfl) ⟨1606932, by rfl⟩ : syracuseStep 4285153 = 3213865) B3213865
theorem B1401583 : Blo 491791 1401583 := bstep (se 1 (by rfl) ⟨1051187, by rfl⟩ : syracuseStep 1401583 = 2102375) B2102375
theorem B3171271 : Blo 491791 3171271 := bstep (se 1 (by rfl) ⟨2378453, by rfl⟩ : syracuseStep 3171271 = 4756907) B4756907
theorem B1895021 : Blo 491791 1895021 := bstep (se 3 (by rfl) ⟨355316, by rfl⟩ : syracuseStep 1895021 = 710633) B710633
theorem B1796843 : Blo 491791 1796843 := bstep (se 1 (by rfl) ⟨1347632, by rfl⟩ : syracuseStep 1796843 = 2695265) B2695265
theorem B1896539 : Blo 491791 1896539 := bstep (se 1 (by rfl) ⟨1422404, by rfl⟩ : syracuseStep 1896539 = 2844809) B2844809
theorem B1110671 : Blo 491791 1110671 := bstep (se 1 (by rfl) ⟨833003, by rfl⟩ : syracuseStep 1110671 = 1666007) B1666007
theorem B1667897 : Blo 491791 1667897 := bstep (se 2 (by rfl) ⟨625461, by rfl⟩ : syracuseStep 1667897 = 1250923) B1250923
theorem B1111337 : Blo 491791 1111337 := bstep (se 2 (by rfl) ⟨416751, by rfl⟩ : syracuseStep 1111337 = 833503) B833503
theorem B751135 : Blo 491791 751135 := bstep (se 1 (by rfl) ⟨563351, by rfl⟩ : syracuseStep 751135 = 1126703) B1126703
theorem B1669679 : Blo 491791 1669679 := bstep (se 1 (by rfl) ⟨1252259, by rfl⟩ : syracuseStep 1669679 = 2504519) B2504519
theorem B1113209 : Blo 491791 1113209 := bstep (se 2 (by rfl) ⟨417453, by rfl⟩ : syracuseStep 1113209 = 834907) B834907
theorem B556699 : Blo 491791 556699 := bstep (se 1 (by rfl) ⟨417524, by rfl⟩ : syracuseStep 556699 = 835049) B835049
theorem B41090723 : Blo 491791 41090723 := bstep (se 1 (by rfl) ⟨30818042, by rfl⟩ : syracuseStep 41090723 = 61636085) B61636085
theorem B4227335 : Blo 491791 4227335 := bstep (se 1 (by rfl) ⟨3170501, by rfl⟩ : syracuseStep 4227335 = 6341003) B6341003
theorem B491999 : Blo 491791 491999 := bstep (se 1 (by rfl) ⟨368999, by rfl⟩ : syracuseStep 491999 = 737999) B737999
theorem B25952993 : Blo 491791 25952993 := bstep (se 2 (by rfl) ⟨9732372, by rfl⟩ : syracuseStep 25952993 = 19464745) B19464745
theorem B1246175 : Blo 491791 1246175 := bstep (se 1 (by rfl) ⟨934631, by rfl⟩ : syracuseStep 1246175 = 1869263) B1869263
theorem B1868777 : Blo 491791 1868777 := bstep (se 2 (by rfl) ⟨700791, by rfl⟩ : syracuseStep 1868777 = 1401583) B1401583
theorem B492575 : Blo 491791 492575 := bstep (se 1 (by rfl) ⟨369431, by rfl⟩ : syracuseStep 492575 = 738863) B738863
theorem B4228361 : Blo 491791 4228361 := bstep (se 2 (by rfl) ⟨1585635, by rfl⟩ : syracuseStep 4228361 = 3171271) B3171271
theorem B1115513 : Blo 491791 1115513 := bstep (se 2 (by rfl) ⟨418317, by rfl⟩ : syracuseStep 1115513 = 836635) B836635
theorem B492927 : Blo 491791 492927 := bstep (se 1 (by rfl) ⟨369695, by rfl⟩ : syracuseStep 492927 = 739391) B739391
theorem B1672703 : Blo 491791 1672703 := bstep (se 1 (by rfl) ⟨1254527, by rfl⟩ : syracuseStep 1672703 = 2509055) B2509055
theorem B493147 : Blo 491791 493147 := bstep (se 1 (by rfl) ⟨369860, by rfl⟩ : syracuseStep 493147 = 739721) B739721
theorem B493215 : Blo 491791 493215 := bstep (se 1 (by rfl) ⟨369911, by rfl⟩ : syracuseStep 493215 = 739823) B739823
theorem B624287 : Blo 491791 624287 := bstep (se 1 (by rfl) ⟨468215, by rfl⟩ : syracuseStep 624287 = 936431) B936431
theorem B18974411 : Blo 491791 18974411 := bstep (se 1 (by rfl) ⟨14230808, by rfl⟩ : syracuseStep 18974411 = 28461617) B28461617
theorem B1869551 : Blo 491791 1869551 := bstep (se 1 (by rfl) ⟨1402163, by rfl⟩ : syracuseStep 1869551 = 2804327) B2804327
theorem B3737339 : Blo 491791 3737339 := bstep (se 1 (by rfl) ⟨2803004, by rfl⟩ : syracuseStep 3737339 = 5606009) B5606009
theorem B493439 : Blo 491791 493439 := bstep (se 1 (by rfl) ⟨370079, by rfl⟩ : syracuseStep 493439 = 740159) B740159
theorem B493563 : Blo 491791 493563 := bstep (se 1 (by rfl) ⟨370172, by rfl⟩ : syracuseStep 493563 = 740345) B740345
theorem B493895 : Blo 491791 493895 := bstep (se 1 (by rfl) ⟨370421, by rfl⟩ : syracuseStep 493895 = 740843) B740843
theorem B494207 : Blo 491791 494207 := bstep (se 1 (by rfl) ⟨370655, by rfl⟩ : syracuseStep 494207 = 741311) B741311
theorem B494311 : Blo 491791 494311 := bstep (se 1 (by rfl) ⟨370733, by rfl⟩ : syracuseStep 494311 = 741467) B741467
theorem B494527 : Blo 491791 494527 := bstep (se 1 (by rfl) ⟨370895, by rfl⟩ : syracuseStep 494527 = 741791) B741791
theorem B494695 : Blo 491791 494695 := bstep (se 1 (by rfl) ⟨371021, by rfl⟩ : syracuseStep 494695 = 742043) B742043
theorem B494919 : Blo 491791 494919 := bstep (se 1 (by rfl) ⟨371189, by rfl⟩ : syracuseStep 494919 = 742379) B742379
theorem B495039 : Blo 491791 495039 := bstep (se 1 (by rfl) ⟨371279, by rfl⟩ : syracuseStep 495039 = 742559) B742559
theorem B11964347 : Blo 491791 11964347 := bstep (se 1 (by rfl) ⟨8973260, by rfl⟩ : syracuseStep 11964347 = 17946521) B17946521
theorem B495647 : Blo 491791 495647 := bstep (se 1 (by rfl) ⟨371735, by rfl⟩ : syracuseStep 495647 = 743471) B743471
theorem B21336371 : Blo 491791 21336371 := bstep (se 1 (by rfl) ⟨16002278, by rfl⟩ : syracuseStep 21336371 = 32004557) B32004557
theorem B9640673 : Blo 491791 9640673 := bstep (se 2 (by rfl) ⟨3615252, by rfl⟩ : syracuseStep 9640673 = 7230505) B7230505
theorem B1252331 : Blo 491791 1252331 := bstep (se 1 (by rfl) ⟨939248, by rfl⟩ : syracuseStep 1252331 = 1878497) B1878497
theorem B4791581 : Blo 491791 4791581 := bstep (se 3 (by rfl) ⟨898421, by rfl⟩ : syracuseStep 4791581 = 1796843) B1796843
theorem B2105671 : Blo 491791 2105671 := bstep (se 1 (by rfl) ⟨1579253, by rfl⟩ : syracuseStep 2105671 = 3158507) B3158507
theorem B1058159 : Blo 491791 1058159 := bstep (se 1 (by rfl) ⟨793619, by rfl⟩ : syracuseStep 1058159 = 1587239) B1587239
theorem B1582523 : Blo 491791 1582523 := bstep (se 1 (by rfl) ⟨1186892, by rfl⟩ : syracuseStep 1582523 = 2373785) B2373785
theorem B2665385 : Blo 491791 2665385 := bstep (se 2 (by rfl) ⟨999519, by rfl⟩ : syracuseStep 2665385 = 1999039) B1999039
theorem B830695 : Blo 491791 830695 := bstep (se 1 (by rfl) ⟨623021, by rfl⟩ : syracuseStep 830695 = 1246043) B1246043
theorem B20229749 : Blo 491791 20229749 := bstep (se 5 (by rfl) ⟨948269, by rfl⟩ : syracuseStep 20229749 = 1896539) B1896539
theorem B5713537 : Blo 491791 5713537 := bstep (se 2 (by rfl) ⟨2142576, by rfl⟩ : syracuseStep 5713537 = 4285153) B4285153
theorem B831431 : Blo 491791 831431 := bstep (se 1 (by rfl) ⟨623573, by rfl⟩ : syracuseStep 831431 = 1247147) B1247147
theorem B2699227 : Blo 491791 2699227 := bstep (se 1 (by rfl) ⟨2024420, by rfl⟩ : syracuseStep 2699227 = 4048841) B4048841
theorem B1781995 : Blo 491791 1781995 := bstep (se 1 (by rfl) ⟨1336496, by rfl⟩ : syracuseStep 1781995 = 2672993) B2672993
theorem B2372303 : Blo 491791 2372303 := bstep (se 1 (by rfl) ⟨1779227, by rfl⟩ : syracuseStep 2372303 = 3558455) B3558455
theorem B5354855 : Blo 491791 5354855 := bstep (se 1 (by rfl) ⟨4016141, by rfl⟩ : syracuseStep 5354855 = 8032283) B8032283
theorem B2504843 : Blo 491791 2504843 := bstep (se 1 (by rfl) ⟨1878632, by rfl⟩ : syracuseStep 2504843 = 3757265) B3757265
theorem B934267 : Blo 491791 934267 := bstep (se 1 (by rfl) ⟨700700, by rfl⟩ : syracuseStep 934267 = 1401401) B1401401
theorem B1263347 : Blo 491791 1263347 := bstep (se 1 (by rfl) ⟨947510, by rfl⟩ : syracuseStep 1263347 = 1895021) B1895021
theorem B1001513 : Blo 491791 1001513 := bstep (se 2 (by rfl) ⟨375567, by rfl⟩ : syracuseStep 1001513 = 751135) B751135
theorem B3000889 : Blo 491791 3000889 := bstep (se 2 (by rfl) ⟨1125333, by rfl⟩ : syracuseStep 3000889 = 2250667) B2250667
theorem B2804645 : Blo 491791 2804645 := bstep (se 4 (by rfl) ⟨262935, by rfl⟩ : syracuseStep 2804645 = 525871) B525871
theorem B2804827 : Blo 491791 2804827 := bstep (se 1 (by rfl) ⟨2103620, by rfl⟩ : syracuseStep 2804827 = 4207241) B4207241
theorem B740447 : Blo 491791 740447 := bstep (se 1 (by rfl) ⟨555335, by rfl⟩ : syracuseStep 740447 = 1110671) B1110671
theorem B2673967 : Blo 491791 2673967 := bstep (se 1 (by rfl) ⟨2005475, by rfl⟩ : syracuseStep 2673967 = 4010951) B4010951
theorem B740891 : Blo 491791 740891 := bstep (se 1 (by rfl) ⟨555668, by rfl⟩ : syracuseStep 740891 = 1111337) B1111337
theorem B10407649 : Blo 491791 10407649 := bstep (se 2 (by rfl) ⟨3902868, by rfl⟩ : syracuseStep 10407649 = 7805737) B7805737
theorem B2150711 : Blo 491791 2150711 := bstep (se 1 (by rfl) ⟨1613033, by rfl⟩ : syracuseStep 2150711 = 3226067) B3226067
theorem B12636485 : Blo 491791 12636485 := bstep (se 4 (by rfl) ⟨1184670, by rfl⟩ : syracuseStep 12636485 = 2369341) B2369341
theorem B742139 : Blo 491791 742139 := bstep (se 1 (by rfl) ⟨556604, by rfl⟩ : syracuseStep 742139 = 1113209) B1113209
theorem B742265 : Blo 491791 742265 := bstep (se 2 (by rfl) ⟨278349, by rfl⟩ : syracuseStep 742265 = 556699) B556699
theorem B54711359 : Blo 491791 54711359 := bstep (se 1 (by rfl) ⟨41033519, by rfl⟩ : syracuseStep 54711359 = 82067039) B82067039
theorem B742847 : Blo 491791 742847 := bstep (se 1 (by rfl) ⟨557135, by rfl⟩ : syracuseStep 742847 = 1114271) B1114271
theorem B743039 : Blo 491791 743039 := bstep (se 1 (by rfl) ⟨557279, by rfl⟩ : syracuseStep 743039 = 1114559) B1114559
theorem B1661471 : Blo 491791 1661471 := bstep (se 1 (by rfl) ⟨1246103, by rfl⟩ : syracuseStep 1661471 = 2492207) B2492207
theorem B12802981 : Blo 491791 12802981 := bstep (se 4 (by rfl) ⟨1200279, by rfl⟩ : syracuseStep 12802981 = 2400559) B2400559
theorem B5627879 : Blo 491791 5627879 := bstep (se 1 (by rfl) ⟨4220909, by rfl⟩ : syracuseStep 5627879 = 8441819) B8441819
theorem B1663199 : Blo 491791 1663199 := bstep (se 1 (by rfl) ⟨1247399, by rfl⟩ : syracuseStep 1663199 = 2494799) B2494799
theorem B2285927 : Blo 491791 2285927 := bstep (se 1 (by rfl) ⟨1714445, by rfl⟩ : syracuseStep 2285927 = 3428891) B3428891
theorem B7627529 : Blo 491791 7627529 := bstep (se 2 (by rfl) ⟨2860323, by rfl⟩ : syracuseStep 7627529 = 5720647) B5720647
theorem B1107503 : Blo 491791 1107503 := bstep (se 1 (by rfl) ⟨830627, by rfl⟩ : syracuseStep 1107503 = 1661255) B1661255
theorem B1108151 : Blo 491791 1108151 := bstep (se 1 (by rfl) ⟨831113, by rfl⟩ : syracuseStep 1108151 = 1662227) B1662227
theorem B1108187 : Blo 491791 1108187 := bstep (se 1 (by rfl) ⟨831140, by rfl⟩ : syracuseStep 1108187 = 1662281) B1662281
theorem B12807233 : Blo 491791 12807233 := bstep (se 2 (by rfl) ⟨4802712, by rfl⟩ : syracuseStep 12807233 = 9605425) B9605425
theorem B12872915 : Blo 491791 12872915 := bstep (se 1 (by rfl) ⟨9654686, by rfl⟩ : syracuseStep 12872915 = 19309373) B19309373
theorem B3207113 : Blo 491791 3207113 := bstep (se 2 (by rfl) ⟨1202667, by rfl⟩ : syracuseStep 3207113 = 2405335) B2405335
theorem B1667411 : Blo 491791 1667411 := bstep (se 1 (by rfl) ⟨1250558, by rfl⟩ : syracuseStep 1667411 = 2501117) B2501117
theorem B1668815 : Blo 491791 1668815 := bstep (se 1 (by rfl) ⟨1251611, by rfl⟩ : syracuseStep 1668815 = 2503223) B2503223
theorem B1111931 : Blo 491791 1111931 := bstep (se 1 (by rfl) ⟨833948, by rfl⟩ : syracuseStep 1111931 = 1667897) B1667897
theorem B1669193 : Blo 491791 1669193 := bstep (se 2 (by rfl) ⟨625947, by rfl⟩ : syracuseStep 1669193 = 1251895) B1251895
theorem B1669247 : Blo 491791 1669247 := bstep (se 1 (by rfl) ⟨1251935, by rfl⟩ : syracuseStep 1669247 = 2503871) B2503871
theorem B1113119 : Blo 491791 1113119 := bstep (se 1 (by rfl) ⟨834839, by rfl⟩ : syracuseStep 1113119 = 1669679) B1669679
theorem B27393815 : Blo 491791 27393815 := bstep (se 1 (by rfl) ⟨20545361, by rfl⟩ : syracuseStep 27393815 = 41090723) B41090723
theorem B2818223 : Blo 491791 2818223 := bstep (se 1 (by rfl) ⟨2113667, by rfl⟩ : syracuseStep 2818223 = 4227335) B4227335
theorem B17301995 : Blo 491791 17301995 := bstep (se 1 (by rfl) ⟨12976496, by rfl⟩ : syracuseStep 17301995 = 25952993) B25952993
theorem B1245689 : Blo 491791 1245689 := bstep (se 2 (by rfl) ⟨467133, by rfl⟩ : syracuseStep 1245689 = 934267) B934267
theorem B1245851 : Blo 491791 1245851 := bstep (se 1 (by rfl) ⟨934388, by rfl⟩ : syracuseStep 1245851 = 1868777) B1868777
theorem B2818907 : Blo 491791 2818907 := bstep (se 1 (by rfl) ⟨2114180, by rfl⟩ : syracuseStep 2818907 = 4228361) B4228361
theorem B1115135 : Blo 491791 1115135 := bstep (se 1 (by rfl) ⟨836351, by rfl⟩ : syracuseStep 1115135 = 1672703) B1672703
theorem B12649607 : Blo 491791 12649607 := bstep (se 1 (by rfl) ⟨9487205, by rfl⟩ : syracuseStep 12649607 = 18974411) B18974411
theorem B1246367 : Blo 491791 1246367 := bstep (se 1 (by rfl) ⟨934775, by rfl⟩ : syracuseStep 1246367 = 1869551) B1869551
theorem B2491559 : Blo 491791 2491559 := bstep (se 1 (by rfl) ⟨1868669, by rfl⟩ : syracuseStep 2491559 = 3737339) B3737339
theorem B1869763 : Blo 491791 1869763 := bstep (se 1 (by rfl) ⟨1402322, by rfl⟩ : syracuseStep 1869763 = 2804645) B2804645
theorem B493631 : Blo 491791 493631 := bstep (se 1 (by rfl) ⟨370223, by rfl⟩ : syracuseStep 493631 = 740447) B740447
theorem B493927 : Blo 491791 493927 := bstep (se 1 (by rfl) ⟨370445, by rfl⟩ : syracuseStep 493927 = 740891) B740891
theorem B14224247 : Blo 491791 14224247 := bstep (se 1 (by rfl) ⟨10668185, by rfl⟩ : syracuseStep 14224247 = 21336371) B21336371
theorem B8424323 : Blo 491791 8424323 := bstep (se 1 (by rfl) ⟨6318242, by rfl⟩ : syracuseStep 8424323 = 12636485) B12636485
theorem B494759 : Blo 491791 494759 := bstep (se 1 (by rfl) ⟨371069, by rfl⟩ : syracuseStep 494759 = 742139) B742139
theorem B494843 : Blo 491791 494843 := bstep (se 1 (by rfl) ⟨371132, by rfl⟩ : syracuseStep 494843 = 742265) B742265
theorem B36474239 : Blo 491791 36474239 := bstep (se 1 (by rfl) ⟨27355679, by rfl⟩ : syracuseStep 36474239 = 54711359) B54711359
theorem B4001185 : Blo 491791 4001185 := bstep (se 2 (by rfl) ⟨1500444, by rfl⟩ : syracuseStep 4001185 = 3000889) B3000889
theorem B495231 : Blo 491791 495231 := bstep (se 1 (by rfl) ⟨371423, by rfl⟩ : syracuseStep 495231 = 742847) B742847
theorem B495359 : Blo 491791 495359 := bstep (se 1 (by rfl) ⟨371519, by rfl⟩ : syracuseStep 495359 = 743039) B743039
theorem B3739769 : Blo 491791 3739769 := bstep (se 2 (by rfl) ⟨1402413, by rfl⟩ : syracuseStep 3739769 = 2804827) B2804827
theorem B6427115 : Blo 491791 6427115 := bstep (se 1 (by rfl) ⟨4820336, by rfl⟩ : syracuseStep 6427115 = 9640673) B9640673
theorem B5085019 : Blo 491791 5085019 := bstep (se 1 (by rfl) ⟨3813764, by rfl⟩ : syracuseStep 5085019 = 7627529) B7627529
theorem B1055015 : Blo 491791 1055015 := bstep (se 1 (by rfl) ⟨791261, by rfl⟩ : syracuseStep 1055015 = 1582523) B1582523
theorem B1776923 : Blo 491791 1776923 := bstep (se 1 (by rfl) ⟨1332692, by rfl⟩ : syracuseStep 1776923 = 2665385) B2665385
theorem B2138075 : Blo 491791 2138075 := bstep (se 1 (by rfl) ⟨1603556, by rfl⟩ : syracuseStep 2138075 = 3207113) B3207113
theorem B1581535 : Blo 491791 1581535 := bstep (se 1 (by rfl) ⟨1186151, by rfl⟩ : syracuseStep 1581535 = 2372303) B2372303
theorem B14395877 : Blo 491791 14395877 := bstep (se 4 (by rfl) ⟨1349613, by rfl⟩ : syracuseStep 14395877 = 2699227) B2699227
theorem B18262543 : Blo 491791 18262543 := bstep (se 1 (by rfl) ⟨13696907, by rfl⟩ : syracuseStep 18262543 = 27393815) B27393815
theorem B830783 : Blo 491791 830783 := bstep (se 1 (by rfl) ⟨623087, by rfl⟩ : syracuseStep 830783 = 1246175) B1246175
theorem B667675 : Blo 491791 667675 := bstep (se 1 (by rfl) ⟨500756, by rfl⟩ : syracuseStep 667675 = 1001513) B1001513
theorem B7976231 : Blo 491791 7976231 := bstep (se 1 (by rfl) ⟨5982173, by rfl⟩ : syracuseStep 7976231 = 11964347) B11964347
theorem B834887 : Blo 491791 834887 := bstep (se 1 (by rfl) ⟨626165, by rfl⟩ : syracuseStep 834887 = 1252331) B1252331
theorem B7618049 : Blo 491791 7618049 := bstep (se 2 (by rfl) ⟨2856768, by rfl⟩ : syracuseStep 7618049 = 5713537) B5713537
theorem B3194387 : Blo 491791 3194387 := bstep (se 1 (by rfl) ⟨2395790, by rfl⟩ : syracuseStep 3194387 = 4791581) B4791581
theorem B13876865 : Blo 491791 13876865 := bstep (se 2 (by rfl) ⟨5203824, by rfl⟩ : syracuseStep 13876865 = 10407649) B10407649
theorem B3751919 : Blo 491791 3751919 := bstep (se 1 (by rfl) ⟨2813939, by rfl⟩ : syracuseStep 3751919 = 5627879) B5627879
theorem B1523951 : Blo 491791 1523951 := bstep (se 1 (by rfl) ⟨1142963, by rfl⟩ : syracuseStep 1523951 = 2285927) B2285927
theorem B2375993 : Blo 491791 2375993 := bstep (se 2 (by rfl) ⟨890997, by rfl⟩ : syracuseStep 2375993 = 1781995) B1781995
theorem B705439 : Blo 491791 705439 := bstep (se 1 (by rfl) ⟨529079, by rfl⟩ : syracuseStep 705439 = 1058159) B1058159
theorem B738335 : Blo 491791 738335 := bstep (se 1 (by rfl) ⟨553751, by rfl⟩ : syracuseStep 738335 = 1107503) B1107503
theorem B738767 : Blo 491791 738767 := bstep (se 1 (by rfl) ⟨554075, by rfl⟩ : syracuseStep 738767 = 1108151) B1108151
theorem B738791 : Blo 491791 738791 := bstep (se 1 (by rfl) ⟨554093, by rfl⟩ : syracuseStep 738791 = 1108187) B1108187
theorem B8538155 : Blo 491791 8538155 := bstep (se 1 (by rfl) ⟨6403616, by rfl⟩ : syracuseStep 8538155 = 12807233) B12807233
theorem B13486499 : Blo 491791 13486499 := bstep (se 1 (by rfl) ⟨10114874, by rfl⟩ : syracuseStep 13486499 = 20229749) B20229749
theorem B741287 : Blo 491791 741287 := bstep (se 1 (by rfl) ⟨555965, by rfl⟩ : syracuseStep 741287 = 1111931) B1111931
theorem B742079 : Blo 491791 742079 := bstep (se 1 (by rfl) ⟨556559, by rfl⟩ : syracuseStep 742079 = 1113119) B1113119
theorem B2807561 : Blo 491791 2807561 := bstep (se 2 (by rfl) ⟨1052835, by rfl⟩ : syracuseStep 2807561 = 2105671) B2105671
theorem B743675 : Blo 491791 743675 := bstep (se 1 (by rfl) ⟨557756, by rfl⟩ : syracuseStep 743675 = 1115513) B1115513
theorem B842231 : Blo 491791 842231 := bstep (se 1 (by rfl) ⟨631673, by rfl⟩ : syracuseStep 842231 = 1263347) B1263347
theorem B1433807 : Blo 491791 1433807 := bstep (se 1 (by rfl) ⟨1075355, by rfl⟩ : syracuseStep 1433807 = 2150711) B2150711
theorem B1107593 : Blo 491791 1107593 := bstep (se 2 (by rfl) ⟨415347, by rfl⟩ : syracuseStep 1107593 = 830695) B830695
theorem B1107647 : Blo 491791 1107647 := bstep (se 1 (by rfl) ⟨830735, by rfl⟩ : syracuseStep 1107647 = 1661471) B1661471
theorem B3565289 : Blo 491791 3565289 := bstep (se 2 (by rfl) ⟨1336983, by rfl⟩ : syracuseStep 3565289 = 2673967) B2673967
theorem B1664765 : Blo 491791 1664765 := bstep (se 3 (by rfl) ⟨312143, by rfl⟩ : syracuseStep 1664765 = 624287) B624287
theorem B1108799 : Blo 491791 1108799 := bstep (se 1 (by rfl) ⟨831599, by rfl⟩ : syracuseStep 1108799 = 1663199) B1663199
theorem B8581943 : Blo 491791 8581943 := bstep (se 1 (by rfl) ⟨6436457, by rfl⟩ : syracuseStep 8581943 = 12872915) B12872915
theorem B554287 : Blo 491791 554287 := bstep (se 1 (by rfl) ⟨415715, by rfl⟩ : syracuseStep 554287 = 831431) B831431
theorem B1111607 : Blo 491791 1111607 := bstep (se 1 (by rfl) ⟨833705, by rfl⟩ : syracuseStep 1111607 = 1667411) B1667411
theorem B3569903 : Blo 491791 3569903 := bstep (se 1 (by rfl) ⟨2677427, by rfl⟩ : syracuseStep 3569903 = 5354855) B5354855
theorem B1112543 : Blo 491791 1112543 := bstep (se 1 (by rfl) ⟨834407, by rfl⟩ : syracuseStep 1112543 = 1668815) B1668815
theorem B17070641 : Blo 491791 17070641 := bstep (se 2 (by rfl) ⟨6401490, by rfl⟩ : syracuseStep 17070641 = 12802981) B12802981
theorem B1112795 : Blo 491791 1112795 := bstep (se 1 (by rfl) ⟨834596, by rfl⟩ : syracuseStep 1112795 = 1669193) B1669193
theorem B1112831 : Blo 491791 1112831 := bstep (se 1 (by rfl) ⟨834623, by rfl⟩ : syracuseStep 1112831 = 1669247) B1669247
theorem B1669895 : Blo 491791 1669895 := bstep (se 1 (by rfl) ⟨1252421, by rfl⟩ : syracuseStep 1669895 = 2504843) B2504843
theorem B1015967 : Blo 491791 1015967 := bstep (se 1 (by rfl) ⟨761975, by rfl⟩ : syracuseStep 1015967 = 1523951) B1523951
theorem B11534663 : Blo 491791 11534663 := bstep (se 1 (by rfl) ⟨8650997, by rfl⟩ : syracuseStep 11534663 = 17301995) B17301995
theorem B492223 : Blo 491791 492223 := bstep (se 1 (by rfl) ⟨369167, by rfl⟩ : syracuseStep 492223 = 738335) B738335
theorem B492511 : Blo 491791 492511 := bstep (se 1 (by rfl) ⟨369383, by rfl⟩ : syracuseStep 492511 = 738767) B738767
theorem B492527 : Blo 491791 492527 := bstep (se 1 (by rfl) ⟨369395, by rfl⟩ : syracuseStep 492527 = 738791) B738791
theorem B24316159 : Blo 491791 24316159 := bstep (se 1 (by rfl) ⟨18237119, by rfl⟩ : syracuseStep 24316159 = 36474239) B36474239
theorem B2493017 : Blo 491791 2493017 := bstep (se 2 (by rfl) ⟨934881, by rfl⟩ : syracuseStep 2493017 = 1869763) B1869763
theorem B494191 : Blo 491791 494191 := bstep (se 1 (by rfl) ⟨370643, by rfl⟩ : syracuseStep 494191 = 741287) B741287
theorem B2493179 : Blo 491791 2493179 := bstep (se 1 (by rfl) ⟨1869884, by rfl⟩ : syracuseStep 2493179 = 3739769) B3739769
theorem B494719 : Blo 491791 494719 := bstep (se 1 (by rfl) ⟨371039, by rfl⟩ : syracuseStep 494719 = 742079) B742079
theorem B24350057 : Blo 491791 24350057 := bstep (se 2 (by rfl) ⟨9131271, by rfl⟩ : syracuseStep 24350057 = 18262543) B18262543
theorem B1871707 : Blo 491791 1871707 := bstep (se 1 (by rfl) ⟨1403780, by rfl⟩ : syracuseStep 1871707 = 2807561) B2807561
theorem B495783 : Blo 491791 495783 := bstep (se 1 (by rfl) ⟨371837, by rfl⟩ : syracuseStep 495783 = 743675) B743675
theorem B561487 : Blo 491791 561487 := bstep (se 1 (by rfl) ⟨421115, by rfl⟩ : syracuseStep 561487 = 842231) B842231
theorem B1184615 : Blo 491791 1184615 := bstep (se 1 (by rfl) ⟨888461, by rfl⟩ : syracuseStep 1184615 = 1776923) B1776923
theorem B890233 : Blo 491791 890233 := bstep (se 2 (by rfl) ⟨333837, by rfl⟩ : syracuseStep 890233 = 667675) B667675
theorem B955871 : Blo 491791 955871 := bstep (se 1 (by rfl) ⟨716903, by rfl⟩ : syracuseStep 955871 = 1433807) B1433807
theorem B5317487 : Blo 491791 5317487 := bstep (se 1 (by rfl) ⟨3988115, by rfl⟩ : syracuseStep 5317487 = 7976231) B7976231
theorem B11380427 : Blo 491791 11380427 := bstep (se 1 (by rfl) ⟨8535320, by rfl⟩ : syracuseStep 11380427 = 17070641) B17070641
theorem B9251243 : Blo 491791 9251243 := bstep (se 1 (by rfl) ⟨6938432, by rfl⟩ : syracuseStep 9251243 = 13876865) B13876865
theorem B2501279 : Blo 491791 2501279 := bstep (se 1 (by rfl) ⟨1875959, by rfl⟩ : syracuseStep 2501279 = 3751919) B3751919
theorem B1878815 : Blo 491791 1878815 := bstep (se 1 (by rfl) ⟨1409111, by rfl⟩ : syracuseStep 1878815 = 2818223) B2818223
theorem B830459 : Blo 491791 830459 := bstep (se 1 (by rfl) ⟨622844, by rfl⟩ : syracuseStep 830459 = 1245689) B1245689
theorem B830567 : Blo 491791 830567 := bstep (se 1 (by rfl) ⟨622925, by rfl⟩ : syracuseStep 830567 = 1245851) B1245851
theorem B1879271 : Blo 491791 1879271 := bstep (se 1 (by rfl) ⟨1409453, by rfl⟩ : syracuseStep 1879271 = 2818907) B2818907
theorem B2108713 : Blo 491791 2108713 := bstep (se 2 (by rfl) ⟨790767, by rfl⟩ : syracuseStep 2108713 = 1581535) B1581535
theorem B8433071 : Blo 491791 8433071 := bstep (se 1 (by rfl) ⟨6324803, by rfl⟩ : syracuseStep 8433071 = 12649607) B12649607
theorem B830911 : Blo 491791 830911 := bstep (se 1 (by rfl) ⟨623183, by rfl⟩ : syracuseStep 830911 = 1246367) B1246367
theorem B6335981 : Blo 491791 6335981 := bstep (se 3 (by rfl) ⟨1187996, by rfl⟩ : syracuseStep 6335981 = 2375993) B2375993
theorem B8990999 : Blo 491791 8990999 := bstep (se 1 (by rfl) ⟨6743249, by rfl⟩ : syracuseStep 8990999 = 13486499) B13486499
theorem B9482831 : Blo 491791 9482831 := bstep (se 1 (by rfl) ⟨7112123, by rfl⟩ : syracuseStep 9482831 = 14224247) B14224247
theorem B5616215 : Blo 491791 5616215 := bstep (se 1 (by rfl) ⟨4212161, by rfl⟩ : syracuseStep 5616215 = 8424323) B8424323
theorem B703343 : Blo 491791 703343 := bstep (se 1 (by rfl) ⟨527507, by rfl⟩ : syracuseStep 703343 = 1055015) B1055015
theorem B1425383 : Blo 491791 1425383 := bstep (se 1 (by rfl) ⟨1069037, by rfl⟩ : syracuseStep 1425383 = 2138075) B2138075
theorem B738395 : Blo 491791 738395 := bstep (se 1 (by rfl) ⟨553796, by rfl⟩ : syracuseStep 738395 = 1107593) B1107593
theorem B738431 : Blo 491791 738431 := bstep (se 1 (by rfl) ⟨553823, by rfl⟩ : syracuseStep 738431 = 1107647) B1107647
theorem B2376859 : Blo 491791 2376859 := bstep (se 1 (by rfl) ⟨1782644, by rfl⟩ : syracuseStep 2376859 = 3565289) B3565289
theorem B739049 : Blo 491791 739049 := bstep (se 2 (by rfl) ⟨277143, by rfl⟩ : syracuseStep 739049 = 554287) B554287
theorem B739199 : Blo 491791 739199 := bstep (se 1 (by rfl) ⟨554399, by rfl⟩ : syracuseStep 739199 = 1108799) B1108799
theorem B5721295 : Blo 491791 5721295 := bstep (se 1 (by rfl) ⟨4290971, by rfl⟩ : syracuseStep 5721295 = 8581943) B8581943
theorem B741071 : Blo 491791 741071 := bstep (se 1 (by rfl) ⟨555803, by rfl⟩ : syracuseStep 741071 = 1111607) B1111607
theorem B2379935 : Blo 491791 2379935 := bstep (se 1 (by rfl) ⟨1784951, by rfl⟩ : syracuseStep 2379935 = 3569903) B3569903
theorem B741695 : Blo 491791 741695 := bstep (se 1 (by rfl) ⟨556271, by rfl⟩ : syracuseStep 741695 = 1112543) B1112543
theorem B741863 : Blo 491791 741863 := bstep (se 1 (by rfl) ⟨556397, by rfl⟩ : syracuseStep 741863 = 1112795) B1112795
theorem B741887 : Blo 491791 741887 := bstep (se 1 (by rfl) ⟨556415, by rfl⟩ : syracuseStep 741887 = 1112831) B1112831
theorem B743423 : Blo 491791 743423 := bstep (se 1 (by rfl) ⟨557567, by rfl⟩ : syracuseStep 743423 = 1115135) B1115135
theorem B1661039 : Blo 491791 1661039 := bstep (se 1 (by rfl) ⟨1245779, by rfl⟩ : syracuseStep 1661039 = 2491559) B2491559
theorem B940585 : Blo 491791 940585 := bstep (se 2 (by rfl) ⟨352719, by rfl⟩ : syracuseStep 940585 = 705439) B705439
theorem B5692103 : Blo 491791 5692103 := bstep (se 1 (by rfl) ⟨4269077, by rfl⟩ : syracuseStep 5692103 = 8538155) B8538155
theorem B4284743 : Blo 491791 4284743 := bstep (se 1 (by rfl) ⟨3213557, by rfl⟩ : syracuseStep 4284743 = 6427115) B6427115
theorem B5334913 : Blo 491791 5334913 := bstep (se 2 (by rfl) ⟨2000592, by rfl⟩ : syracuseStep 5334913 = 4001185) B4001185
theorem B1109843 : Blo 491791 1109843 := bstep (se 1 (by rfl) ⟨832382, by rfl⟩ : syracuseStep 1109843 = 1664765) B1664765
theorem B9597251 : Blo 491791 9597251 := bstep (se 1 (by rfl) ⟨7197938, by rfl⟩ : syracuseStep 9597251 = 14395877) B14395877
theorem B553855 : Blo 491791 553855 := bstep (se 1 (by rfl) ⟨415391, by rfl⟩ : syracuseStep 553855 = 830783) B830783
theorem B6780025 : Blo 491791 6780025 := bstep (se 2 (by rfl) ⟨2542509, by rfl⟩ : syracuseStep 6780025 = 5085019) B5085019
theorem B1113263 : Blo 491791 1113263 := bstep (se 1 (by rfl) ⟨834947, by rfl⟩ : syracuseStep 1113263 = 1669895) B1669895
theorem B556591 : Blo 491791 556591 := bstep (se 1 (by rfl) ⟨417443, by rfl⟩ : syracuseStep 556591 = 834887) B834887
theorem B5078699 : Blo 491791 5078699 := bstep (se 1 (by rfl) ⟨3809024, by rfl⟩ : syracuseStep 5078699 = 7618049) B7618049
theorem B2129591 : Blo 491791 2129591 := bstep (se 1 (by rfl) ⟨1597193, by rfl⟩ : syracuseStep 2129591 = 3194387) B3194387
theorem B492263 : Blo 491791 492263 := bstep (se 1 (by rfl) ⟨369197, by rfl⟩ : syracuseStep 492263 = 738395) B738395
theorem B492287 : Blo 491791 492287 := bstep (se 1 (by rfl) ⟨369215, by rfl⟩ : syracuseStep 492287 = 738431) B738431
theorem B25592669 : Blo 491791 25592669 := bstep (se 3 (by rfl) ⟨4798625, by rfl⟩ : syracuseStep 25592669 = 9597251) B9597251
theorem B492699 : Blo 491791 492699 := bstep (se 1 (by rfl) ⟨369524, by rfl⟩ : syracuseStep 492699 = 739049) B739049
theorem B492799 : Blo 491791 492799 := bstep (se 1 (by rfl) ⟨369599, by rfl⟩ : syracuseStep 492799 = 739199) B739199
theorem B494047 : Blo 491791 494047 := bstep (se 1 (by rfl) ⟨370535, by rfl⟩ : syracuseStep 494047 = 741071) B741071
theorem B7113217 : Blo 491791 7113217 := bstep (se 2 (by rfl) ⟨2667456, by rfl⟩ : syracuseStep 7113217 = 5334913) B5334913
theorem B494463 : Blo 491791 494463 := bstep (se 1 (by rfl) ⟨370847, by rfl⟩ : syracuseStep 494463 = 741695) B741695
theorem B494575 : Blo 491791 494575 := bstep (se 1 (by rfl) ⟨370931, by rfl⟩ : syracuseStep 494575 = 741863) B741863
theorem B494591 : Blo 491791 494591 := bstep (se 1 (by rfl) ⟨370943, by rfl⟩ : syracuseStep 494591 = 741887) B741887
theorem B789743 : Blo 491791 789743 := bstep (se 1 (by rfl) ⟨592307, by rfl⟩ : syracuseStep 789743 = 1184615) B1184615
theorem B495615 : Blo 491791 495615 := bstep (se 1 (by rfl) ⟨371711, by rfl⟩ : syracuseStep 495615 = 743423) B743423
theorem B2495609 : Blo 491791 2495609 := bstep (se 2 (by rfl) ⟨935853, by rfl⟩ : syracuseStep 2495609 = 1871707) B1871707
theorem B3544991 : Blo 491791 3544991 := bstep (se 1 (by rfl) ⟨2658743, by rfl⟩ : syracuseStep 3544991 = 5317487) B5317487
theorem B6167495 : Blo 491791 6167495 := bstep (se 1 (by rfl) ⟨4625621, by rfl⟩ : syracuseStep 6167495 = 9251243) B9251243
theorem B1252543 : Blo 491791 1252543 := bstep (se 1 (by rfl) ⟨939407, by rfl⟩ : syracuseStep 1252543 = 1878815) B1878815
theorem B1252847 : Blo 491791 1252847 := bstep (se 1 (by rfl) ⟨939635, by rfl⟩ : syracuseStep 1252847 = 1879271) B1879271
theorem B1875581 : Blo 491791 1875581 := bstep (se 3 (by rfl) ⟨351671, by rfl⟩ : syracuseStep 1875581 = 703343) B703343
theorem B3744143 : Blo 491791 3744143 := bstep (se 1 (by rfl) ⟨2808107, by rfl⟩ : syracuseStep 3744143 = 5616215) B5616215
theorem B1254113 : Blo 491791 1254113 := bstep (se 2 (by rfl) ⟨470292, by rfl⟩ : syracuseStep 1254113 = 940585) B940585
theorem B5678909 : Blo 491791 5678909 := bstep (se 3 (by rfl) ⟨1064795, by rfl⟩ : syracuseStep 5678909 = 2129591) B2129591
theorem B3385799 : Blo 491791 3385799 := bstep (se 1 (by rfl) ⟨2539349, by rfl⟩ : syracuseStep 3385799 = 5078699) B5078699
theorem B16233371 : Blo 491791 16233371 := bstep (se 1 (by rfl) ⟨12175028, by rfl⟩ : syracuseStep 16233371 = 24350057) B24350057
theorem B1586623 : Blo 491791 1586623 := bstep (se 1 (by rfl) ⟨1189967, by rfl⟩ : syracuseStep 1586623 = 2379935) B2379935
theorem B32421545 : Blo 491791 32421545 := bstep (se 2 (by rfl) ⟨12158079, by rfl⟩ : syracuseStep 32421545 = 24316159) B24316159
theorem B637247 : Blo 491791 637247 := bstep (se 1 (by rfl) ⟨477935, by rfl⟩ : syracuseStep 637247 = 955871) B955871
theorem B7586951 : Blo 491791 7586951 := bstep (se 1 (by rfl) ⟨5690213, by rfl⟩ : syracuseStep 7586951 = 11380427) B11380427
theorem B738473 : Blo 491791 738473 := bstep (se 2 (by rfl) ⟨276927, by rfl⟩ : syracuseStep 738473 = 553855) B553855
theorem B5622047 : Blo 491791 5622047 := bstep (se 1 (by rfl) ⟨4216535, by rfl⟩ : syracuseStep 5622047 = 8433071) B8433071
theorem B739895 : Blo 491791 739895 := bstep (se 1 (by rfl) ⟨554921, by rfl⟩ : syracuseStep 739895 = 1109843) B1109843
theorem B742121 : Blo 491791 742121 := bstep (se 2 (by rfl) ⟨278295, by rfl⟩ : syracuseStep 742121 = 556591) B556591
theorem B742175 : Blo 491791 742175 := bstep (se 1 (by rfl) ⟨556631, by rfl⟩ : syracuseStep 742175 = 1113263) B1113263
theorem B7689775 : Blo 491791 7689775 := bstep (se 1 (by rfl) ⟨5767331, by rfl⟩ : syracuseStep 7689775 = 11534663) B11534663
theorem B2709245 : Blo 491791 2709245 := bstep (se 3 (by rfl) ⟨507983, by rfl⟩ : syracuseStep 2709245 = 1015967) B1015967
theorem B3169145 : Blo 491791 3169145 := bstep (se 2 (by rfl) ⟨1188429, by rfl⟩ : syracuseStep 3169145 = 2376859) B2376859
theorem B1662011 : Blo 491791 1662011 := bstep (se 1 (by rfl) ⟨1246508, by rfl⟩ : syracuseStep 1662011 = 2493017) B2493017
theorem B1662119 : Blo 491791 1662119 := bstep (se 1 (by rfl) ⟨1246589, by rfl⟩ : syracuseStep 1662119 = 2493179) B2493179
theorem B45703925 : Blo 491791 45703925 := bstep (se 5 (by rfl) ⟨2142371, by rfl⟩ : syracuseStep 45703925 = 4284743) B4284743
theorem B1107359 : Blo 491791 1107359 := bstep (se 1 (by rfl) ⟨830519, by rfl⟩ : syracuseStep 1107359 = 1661039) B1661039
theorem B7628393 : Blo 491791 7628393 := bstep (se 2 (by rfl) ⟨2860647, by rfl⟩ : syracuseStep 7628393 = 5721295) B5721295
theorem B2811617 : Blo 491791 2811617 := bstep (se 2 (by rfl) ⟨1054356, by rfl⟩ : syracuseStep 2811617 = 2108713) B2108713
theorem B3794735 : Blo 491791 3794735 := bstep (se 1 (by rfl) ⟨2846051, by rfl⟩ : syracuseStep 3794735 = 5692103) B5692103
theorem B1107881 : Blo 491791 1107881 := bstep (se 2 (by rfl) ⟨415455, by rfl⟩ : syracuseStep 1107881 = 830911) B830911
theorem B748649 : Blo 491791 748649 := bstep (se 2 (by rfl) ⟨280743, by rfl⟩ : syracuseStep 748649 = 561487) B561487
theorem B9040033 : Blo 491791 9040033 := bstep (se 2 (by rfl) ⟨3390012, by rfl⟩ : syracuseStep 9040033 = 6780025) B6780025
theorem B1667519 : Blo 491791 1667519 := bstep (se 1 (by rfl) ⟨1250639, by rfl⟩ : syracuseStep 1667519 = 2501279) B2501279
theorem B4747909 : Blo 491791 4747909 := bstep (se 4 (by rfl) ⟨445116, by rfl⟩ : syracuseStep 4747909 = 890233) B890233
theorem B553639 : Blo 491791 553639 := bstep (se 1 (by rfl) ⟨415229, by rfl⟩ : syracuseStep 553639 = 830459) B830459
theorem B553711 : Blo 491791 553711 := bstep (se 1 (by rfl) ⟨415283, by rfl⟩ : syracuseStep 553711 = 830567) B830567
theorem B4223987 : Blo 491791 4223987 := bstep (se 1 (by rfl) ⟨3167990, by rfl⟩ : syracuseStep 4223987 = 6335981) B6335981
theorem B5993999 : Blo 491791 5993999 := bstep (se 1 (by rfl) ⟨4495499, by rfl⟩ : syracuseStep 5993999 = 8990999) B8990999
theorem B6321887 : Blo 491791 6321887 := bstep (se 1 (by rfl) ⟨4741415, by rfl⟩ : syracuseStep 6321887 = 9482831) B9482831
theorem B950255 : Blo 491791 950255 := bstep (se 1 (by rfl) ⟨712691, by rfl⟩ : syracuseStep 950255 = 1425383) B1425383
theorem B492315 : Blo 491791 492315 := bstep (se 1 (by rfl) ⟨369236, by rfl⟩ : syracuseStep 492315 = 738473) B738473
theorem B493263 : Blo 491791 493263 := bstep (se 1 (by rfl) ⟨369947, by rfl⟩ : syracuseStep 493263 = 739895) B739895
theorem B526495 : Blo 491791 526495 := bstep (se 1 (by rfl) ⟨394871, by rfl⟩ : syracuseStep 526495 = 789743) B789743
theorem B494747 : Blo 491791 494747 := bstep (se 1 (by rfl) ⟨371060, by rfl⟩ : syracuseStep 494747 = 742121) B742121
theorem B494783 : Blo 491791 494783 := bstep (se 1 (by rfl) ⟨371087, by rfl⟩ : syracuseStep 494783 = 742175) B742175
theorem B2363327 : Blo 491791 2363327 := bstep (se 1 (by rfl) ⟨1772495, by rfl⟩ : syracuseStep 2363327 = 3544991) B3544991
theorem B1250387 : Blo 491791 1250387 := bstep (se 1 (by rfl) ⟨937790, by rfl⟩ : syracuseStep 1250387 = 1875581) B1875581
theorem B2496095 : Blo 491791 2496095 := bstep (se 1 (by rfl) ⟨1872071, by rfl⟩ : syracuseStep 2496095 = 3744143) B3744143
theorem B6330545 : Blo 491791 6330545 := bstep (se 2 (by rfl) ⟨2373954, by rfl⟩ : syracuseStep 6330545 = 4747909) B4747909
theorem B5085595 : Blo 491791 5085595 := bstep (se 1 (by rfl) ⟨3814196, by rfl⟩ : syracuseStep 5085595 = 7628393) B7628393
theorem B1874411 : Blo 491791 1874411 := bstep (se 1 (by rfl) ⟨1405808, by rfl⟩ : syracuseStep 1874411 = 2811617) B2811617
theorem B10822247 : Blo 491791 10822247 := bstep (se 1 (by rfl) ⟨8116685, by rfl⟩ : syracuseStep 10822247 = 16233371) B16233371
theorem B633503 : Blo 491791 633503 := bstep (se 1 (by rfl) ⟨475127, by rfl⟩ : syracuseStep 633503 = 950255) B950255
theorem B3748031 : Blo 491791 3748031 := bstep (se 1 (by rfl) ⟨2811023, by rfl⟩ : syracuseStep 3748031 = 5622047) B5622047
theorem B20231869 : Blo 491791 20231869 := bstep (se 3 (by rfl) ⟨3793475, by rfl⟩ : syracuseStep 20231869 = 7586951) B7586951
theorem B9484289 : Blo 491791 9484289 := bstep (se 2 (by rfl) ⟨3556608, by rfl⟩ : syracuseStep 9484289 = 7113217) B7113217
theorem B2112763 : Blo 491791 2112763 := bstep (se 1 (by rfl) ⟨1584572, by rfl⟩ : syracuseStep 2112763 = 3169145) B3169145
theorem B4111663 : Blo 491791 4111663 := bstep (se 1 (by rfl) ⟨3083747, by rfl⟩ : syracuseStep 4111663 = 6167495) B6167495
theorem B7224653 : Blo 491791 7224653 := bstep (se 3 (by rfl) ⟨1354622, by rfl⟩ : syracuseStep 7224653 = 2709245) B2709245
theorem B835231 : Blo 491791 835231 := bstep (se 1 (by rfl) ⟨626423, by rfl⟩ : syracuseStep 835231 = 1252847) B1252847
theorem B836075 : Blo 491791 836075 := bstep (se 1 (by rfl) ⟨627056, by rfl⟩ : syracuseStep 836075 = 1254113) B1254113
theorem B738185 : Blo 491791 738185 := bstep (se 2 (by rfl) ⟨276819, by rfl⟩ : syracuseStep 738185 = 553639) B553639
theorem B738239 : Blo 491791 738239 := bstep (se 1 (by rfl) ⟨553679, by rfl⟩ : syracuseStep 738239 = 1107359) B1107359
theorem B738281 : Blo 491791 738281 := bstep (se 2 (by rfl) ⟨276855, by rfl⟩ : syracuseStep 738281 = 553711) B553711
theorem B3785939 : Blo 491791 3785939 := bstep (se 1 (by rfl) ⟨2839454, by rfl⟩ : syracuseStep 3785939 = 5678909) B5678909
theorem B738587 : Blo 491791 738587 := bstep (se 1 (by rfl) ⟨553940, by rfl⟩ : syracuseStep 738587 = 1107881) B1107881
theorem B2115497 : Blo 491791 2115497 := bstep (se 2 (by rfl) ⟨793311, by rfl⟩ : syracuseStep 2115497 = 1586623) B1586623
theorem B21614363 : Blo 491791 21614363 := bstep (se 1 (by rfl) ⟨16210772, by rfl⟩ : syracuseStep 21614363 = 32421545) B32421545
theorem B4214591 : Blo 491791 4214591 := bstep (se 1 (by rfl) ⟨3160943, by rfl⟩ : syracuseStep 4214591 = 6321887) B6321887
theorem B17061779 : Blo 491791 17061779 := bstep (se 1 (by rfl) ⟨12796334, by rfl⟩ : syracuseStep 17061779 = 25592669) B25592669
theorem B1663739 : Blo 491791 1663739 := bstep (se 1 (by rfl) ⟨1247804, by rfl⟩ : syracuseStep 1663739 = 2495609) B2495609
theorem B1108007 : Blo 491791 1108007 := bstep (se 1 (by rfl) ⟨831005, by rfl⟩ : syracuseStep 1108007 = 1662011) B1662011
theorem B1108079 : Blo 491791 1108079 := bstep (se 1 (by rfl) ⟨831059, by rfl⟩ : syracuseStep 1108079 = 1662119) B1662119
theorem B10119293 : Blo 491791 10119293 := bstep (se 3 (by rfl) ⟨1897367, by rfl⟩ : syracuseStep 10119293 = 3794735) B3794735
theorem B12053377 : Blo 491791 12053377 := bstep (se 2 (by rfl) ⟨4520016, by rfl⟩ : syracuseStep 12053377 = 9040033) B9040033
theorem B30469283 : Blo 491791 30469283 := bstep (se 1 (by rfl) ⟨22851962, by rfl⟩ : syracuseStep 30469283 = 45703925) B45703925
theorem B1699325 : Blo 491791 1699325 := bstep (se 3 (by rfl) ⟨318623, by rfl⟩ : syracuseStep 1699325 = 637247) B637247
theorem B2257199 : Blo 491791 2257199 := bstep (se 1 (by rfl) ⟨1692899, by rfl⟩ : syracuseStep 2257199 = 3385799) B3385799
theorem B10253033 : Blo 491791 10253033 := bstep (se 2 (by rfl) ⟨3844887, by rfl⟩ : syracuseStep 10253033 = 7689775) B7689775
theorem B1996397 : Blo 491791 1996397 := bstep (se 3 (by rfl) ⟨374324, by rfl⟩ : syracuseStep 1996397 = 748649) B748649
theorem B1111679 : Blo 491791 1111679 := bstep (se 1 (by rfl) ⟨833759, by rfl⟩ : syracuseStep 1111679 = 1667519) B1667519
theorem B2815991 : Blo 491791 2815991 := bstep (se 1 (by rfl) ⟨2111993, by rfl⟩ : syracuseStep 2815991 = 4223987) B4223987
theorem B3995999 : Blo 491791 3995999 := bstep (se 1 (by rfl) ⟨2996999, by rfl⟩ : syracuseStep 3995999 = 5993999) B5993999
theorem B1670057 : Blo 491791 1670057 := bstep (se 2 (by rfl) ⟨626271, by rfl⟩ : syracuseStep 1670057 = 1252543) B1252543
theorem B557383 : Blo 491791 557383 := bstep (se 1 (by rfl) ⟨418037, by rfl⟩ : syracuseStep 557383 = 836075) B836075
theorem B492123 : Blo 491791 492123 := bstep (se 1 (by rfl) ⟨369092, by rfl⟩ : syracuseStep 492123 = 738185) B738185
theorem B492159 : Blo 491791 492159 := bstep (se 1 (by rfl) ⟨369119, by rfl⟩ : syracuseStep 492159 = 738239) B738239
theorem B492187 : Blo 491791 492187 := bstep (se 1 (by rfl) ⟨369140, by rfl⟩ : syracuseStep 492187 = 738281) B738281
theorem B2523959 : Blo 491791 2523959 := bstep (se 1 (by rfl) ⟨1892969, by rfl⟩ : syracuseStep 2523959 = 3785939) B3785939
theorem B492391 : Blo 491791 492391 := bstep (se 1 (by rfl) ⟨369293, by rfl⟩ : syracuseStep 492391 = 738587) B738587
theorem B1410331 : Blo 491791 1410331 := bstep (se 1 (by rfl) ⟨1057748, by rfl⟩ : syracuseStep 1410331 = 2115497) B2115497
theorem B1575551 : Blo 491791 1575551 := bstep (se 1 (by rfl) ⟨1181663, by rfl⟩ : syracuseStep 1575551 = 2363327) B2363327
theorem B11374519 : Blo 491791 11374519 := bstep (se 1 (by rfl) ⟨8530889, by rfl⟩ : syracuseStep 11374519 = 17061779) B17061779
theorem B1249607 : Blo 491791 1249607 := bstep (se 1 (by rfl) ⟨937205, by rfl⟩ : syracuseStep 1249607 = 1874411) B1874411
theorem B7214831 : Blo 491791 7214831 := bstep (se 1 (by rfl) ⟨5411123, by rfl⟩ : syracuseStep 7214831 = 10822247) B10822247
theorem B26975825 : Blo 491791 26975825 := bstep (se 2 (by rfl) ⟨10115934, by rfl⟩ : syracuseStep 26975825 = 20231869) B20231869
theorem B2498687 : Blo 491791 2498687 := bstep (se 1 (by rfl) ⟨1874015, by rfl⟩ : syracuseStep 2498687 = 3748031) B3748031
theorem B1877327 : Blo 491791 1877327 := bstep (se 1 (by rfl) ⟨1407995, by rfl⟩ : syracuseStep 1877327 = 2815991) B2815991
theorem B2663999 : Blo 491791 2663999 := bstep (se 1 (by rfl) ⟨1997999, by rfl⟩ : syracuseStep 2663999 = 3995999) B3995999
theorem B5482217 : Blo 491791 5482217 := bstep (se 2 (by rfl) ⟨2055831, by rfl⟩ : syracuseStep 5482217 = 4111663) B4111663
theorem B701993 : Blo 491791 701993 := bstep (se 2 (by rfl) ⟨263247, by rfl⟩ : syracuseStep 701993 = 526495) B526495
theorem B833591 : Blo 491791 833591 := bstep (se 1 (by rfl) ⟨625193, by rfl⟩ : syracuseStep 833591 = 1250387) B1250387
theorem B16071169 : Blo 491791 16071169 := bstep (se 2 (by rfl) ⟨6026688, by rfl⟩ : syracuseStep 16071169 = 12053377) B12053377
theorem B738671 : Blo 491791 738671 := bstep (se 1 (by rfl) ⟨554003, by rfl⟩ : syracuseStep 738671 = 1108007) B1108007
theorem B738719 : Blo 491791 738719 := bstep (se 1 (by rfl) ⟨554039, by rfl⟩ : syracuseStep 738719 = 1108079) B1108079
theorem B1689341 : Blo 491791 1689341 := bstep (se 3 (by rfl) ⟨316751, by rfl⟩ : syracuseStep 1689341 = 633503) B633503
theorem B1132883 : Blo 491791 1132883 := bstep (se 1 (by rfl) ⟨849662, by rfl⟩ : syracuseStep 1132883 = 1699325) B1699325
theorem B6835355 : Blo 491791 6835355 := bstep (se 1 (by rfl) ⟨5126516, by rfl⟩ : syracuseStep 6835355 = 10253033) B10253033
theorem B1330931 : Blo 491791 1330931 := bstep (se 1 (by rfl) ⟨998198, by rfl⟩ : syracuseStep 1330931 = 1996397) B1996397
theorem B741119 : Blo 491791 741119 := bstep (se 1 (by rfl) ⟨555839, by rfl⟩ : syracuseStep 741119 = 1111679) B1111679
theorem B27123173 : Blo 491791 27123173 := bstep (se 4 (by rfl) ⟨2542797, by rfl⟩ : syracuseStep 27123173 = 5085595) B5085595
theorem B14409575 : Blo 491791 14409575 := bstep (se 1 (by rfl) ⟨10807181, by rfl⟩ : syracuseStep 14409575 = 21614363) B21614363
theorem B2809727 : Blo 491791 2809727 := bstep (se 1 (by rfl) ⟨2107295, by rfl⟩ : syracuseStep 2809727 = 4214591) B4214591
theorem B1664063 : Blo 491791 1664063 := bstep (se 1 (by rfl) ⟨1248047, by rfl⟩ : syracuseStep 1664063 = 2496095) B2496095
theorem B4220363 : Blo 491791 4220363 := bstep (se 1 (by rfl) ⟨3165272, by rfl⟩ : syracuseStep 4220363 = 6330545) B6330545
theorem B1109159 : Blo 491791 1109159 := bstep (se 1 (by rfl) ⟨831869, by rfl⟩ : syracuseStep 1109159 = 1663739) B1663739
theorem B6746195 : Blo 491791 6746195 := bstep (se 1 (by rfl) ⟨5059646, by rfl⟩ : syracuseStep 6746195 = 10119293) B10119293
theorem B20312855 : Blo 491791 20312855 := bstep (se 1 (by rfl) ⟨15234641, by rfl⟩ : syracuseStep 20312855 = 30469283) B30469283
theorem B1504799 : Blo 491791 1504799 := bstep (se 1 (by rfl) ⟨1128599, by rfl⟩ : syracuseStep 1504799 = 2257199) B2257199
theorem B6322859 : Blo 491791 6322859 := bstep (se 1 (by rfl) ⟨4742144, by rfl⟩ : syracuseStep 6322859 = 9484289) B9484289
theorem B2817017 : Blo 491791 2817017 := bstep (se 2 (by rfl) ⟨1056381, by rfl⟩ : syracuseStep 2817017 = 2112763) B2112763
theorem B1113371 : Blo 491791 1113371 := bstep (se 1 (by rfl) ⟨835028, by rfl⟩ : syracuseStep 1113371 = 1670057) B1670057
theorem B1113641 : Blo 491791 1113641 := bstep (se 2 (by rfl) ⟨417615, by rfl⟩ : syracuseStep 1113641 = 835231) B835231
theorem B4816435 : Blo 491791 4816435 := bstep (se 1 (by rfl) ⟨3612326, by rfl⟩ : syracuseStep 4816435 = 7224653) B7224653
theorem B492447 : Blo 491791 492447 := bstep (se 1 (by rfl) ⟨369335, by rfl⟩ : syracuseStep 492447 = 738671) B738671
theorem B492479 : Blo 491791 492479 := bstep (se 1 (by rfl) ⟨369359, by rfl⟩ : syracuseStep 492479 = 738719) B738719
theorem B755255 : Blo 491791 755255 := bstep (se 1 (by rfl) ⟨566441, by rfl⟩ : syracuseStep 755255 = 1132883) B1132883
theorem B4556903 : Blo 491791 4556903 := bstep (se 1 (by rfl) ⟨3417677, by rfl⟩ : syracuseStep 4556903 = 6835355) B6835355
theorem B887287 : Blo 491791 887287 := bstep (se 1 (by rfl) ⟨665465, by rfl⟩ : syracuseStep 887287 = 1330931) B1330931
theorem B494079 : Blo 491791 494079 := bstep (se 1 (by rfl) ⟨370559, by rfl⟩ : syracuseStep 494079 = 741119) B741119
theorem B1871981 : Blo 491791 1871981 := bstep (se 3 (by rfl) ⟨350996, by rfl⟩ : syracuseStep 1871981 = 701993) B701993
theorem B9606383 : Blo 491791 9606383 := bstep (se 1 (by rfl) ⟨7204787, by rfl⟩ : syracuseStep 9606383 = 14409575) B14409575
theorem B1873151 : Blo 491791 1873151 := bstep (se 1 (by rfl) ⟨1404863, by rfl⟩ : syracuseStep 1873151 = 2809727) B2809727
theorem B1251551 : Blo 491791 1251551 := bstep (se 1 (by rfl) ⟨938663, by rfl⟩ : syracuseStep 1251551 = 1877327) B1877327
theorem B1775999 : Blo 491791 1775999 := bstep (se 1 (by rfl) ⟨1331999, by rfl⟩ : syracuseStep 1775999 = 2663999) B2663999
theorem B4201469 : Blo 491791 4201469 := bstep (se 3 (by rfl) ⟨787775, by rfl⟩ : syracuseStep 4201469 = 1575551) B1575551
theorem B4497463 : Blo 491791 4497463 := bstep (se 1 (by rfl) ⟨3373097, by rfl⟩ : syracuseStep 4497463 = 6746195) B6746195
theorem B13541903 : Blo 491791 13541903 := bstep (se 1 (by rfl) ⟨10156427, by rfl⟩ : syracuseStep 13541903 = 20312855) B20312855
theorem B1878011 : Blo 491791 1878011 := bstep (se 1 (by rfl) ⟨1408508, by rfl⟩ : syracuseStep 1878011 = 2817017) B2817017
theorem B1682639 : Blo 491791 1682639 := bstep (se 1 (by rfl) ⟨1261979, by rfl⟩ : syracuseStep 1682639 = 2523959) B2523959
theorem B1880441 : Blo 491791 1880441 := bstep (se 2 (by rfl) ⟨705165, by rfl⟩ : syracuseStep 1880441 = 1410331) B1410331
theorem B833071 : Blo 491791 833071 := bstep (se 1 (by rfl) ⟨624803, by rfl⟩ : syracuseStep 833071 = 1249607) B1249607
theorem B4504909 : Blo 491791 4504909 := bstep (se 3 (by rfl) ⟨844670, by rfl⟩ : syracuseStep 4504909 = 1689341) B1689341
theorem B3654811 : Blo 491791 3654811 := bstep (se 1 (by rfl) ⟨2741108, by rfl⟩ : syracuseStep 3654811 = 5482217) B5482217
theorem B739439 : Blo 491791 739439 := bstep (se 1 (by rfl) ⟨554579, by rfl⟩ : syracuseStep 739439 = 1109159) B1109159
theorem B1003199 : Blo 491791 1003199 := bstep (se 1 (by rfl) ⟨752399, by rfl⟩ : syracuseStep 1003199 = 1504799) B1504799
theorem B4215239 : Blo 491791 4215239 := bstep (se 1 (by rfl) ⟨3161429, by rfl⟩ : syracuseStep 4215239 = 6322859) B6322859
theorem B742247 : Blo 491791 742247 := bstep (se 1 (by rfl) ⟨556685, by rfl⟩ : syracuseStep 742247 = 1113371) B1113371
theorem B742427 : Blo 491791 742427 := bstep (se 1 (by rfl) ⟨556820, by rfl⟩ : syracuseStep 742427 = 1113641) B1113641
theorem B743177 : Blo 491791 743177 := bstep (se 2 (by rfl) ⟨278691, by rfl⟩ : syracuseStep 743177 = 557383) B557383
theorem B4809887 : Blo 491791 4809887 := bstep (se 1 (by rfl) ⟨3607415, by rfl⟩ : syracuseStep 4809887 = 7214831) B7214831
theorem B18082115 : Blo 491791 18082115 := bstep (se 1 (by rfl) ⟨13561586, by rfl⟩ : syracuseStep 18082115 = 27123173) B27123173
theorem B17983883 : Blo 491791 17983883 := bstep (se 1 (by rfl) ⟨13487912, by rfl⟩ : syracuseStep 17983883 = 26975825) B26975825
theorem B15166025 : Blo 491791 15166025 := bstep (se 2 (by rfl) ⟨5687259, by rfl⟩ : syracuseStep 15166025 = 11374519) B11374519
theorem B1665791 : Blo 491791 1665791 := bstep (se 1 (by rfl) ⟨1249343, by rfl⟩ : syracuseStep 1665791 = 2498687) B2498687
theorem B1109375 : Blo 491791 1109375 := bstep (se 1 (by rfl) ⟨832031, by rfl⟩ : syracuseStep 1109375 = 1664063) B1664063
theorem B2813575 : Blo 491791 2813575 := bstep (se 1 (by rfl) ⟨2110181, by rfl⟩ : syracuseStep 2813575 = 4220363) B4220363
theorem B21428225 : Blo 491791 21428225 := bstep (se 2 (by rfl) ⟨8035584, by rfl⟩ : syracuseStep 21428225 = 16071169) B16071169
theorem B555727 : Blo 491791 555727 := bstep (se 1 (by rfl) ⟨416795, by rfl⟩ : syracuseStep 555727 = 833591) B833591
theorem B6421913 : Blo 491791 6421913 := bstep (se 2 (by rfl) ⟨2408217, by rfl⟩ : syracuseStep 6421913 = 4816435) B4816435
theorem B23986469 : Blo 491791 23986469 := bstep (se 4 (by rfl) ⟨2248731, by rfl⟩ : syracuseStep 23986469 = 4497463) B4497463
theorem B492959 : Blo 491791 492959 := bstep (se 1 (by rfl) ⟨369719, by rfl⟩ : syracuseStep 492959 = 739439) B739439
theorem B1247987 : Blo 491791 1247987 := bstep (se 1 (by rfl) ⟨935990, by rfl⟩ : syracuseStep 1247987 = 1871981) B1871981
theorem B494831 : Blo 491791 494831 := bstep (se 1 (by rfl) ⟨371123, by rfl⟩ : syracuseStep 494831 = 742247) B742247
theorem B1183049 : Blo 491791 1183049 := bstep (se 2 (by rfl) ⟨443643, by rfl⟩ : syracuseStep 1183049 = 887287) B887287
theorem B494951 : Blo 491791 494951 := bstep (se 1 (by rfl) ⟨371213, by rfl⟩ : syracuseStep 494951 = 742427) B742427
theorem B1248767 : Blo 491791 1248767 := bstep (se 1 (by rfl) ⟨936575, by rfl⟩ : syracuseStep 1248767 = 1873151) B1873151
theorem B495451 : Blo 491791 495451 := bstep (se 1 (by rfl) ⟨371588, by rfl⟩ : syracuseStep 495451 = 743177) B743177
theorem B1183999 : Blo 491791 1183999 := bstep (se 1 (by rfl) ⟨887999, by rfl⟩ : syracuseStep 1183999 = 1775999) B1775999
theorem B1252007 : Blo 491791 1252007 := bstep (se 1 (by rfl) ⟨939005, by rfl⟩ : syracuseStep 1252007 = 1878011) B1878011
theorem B1121759 : Blo 491791 1121759 := bstep (se 1 (by rfl) ⟨841319, by rfl⟩ : syracuseStep 1121759 = 1682639) B1682639
theorem B1253627 : Blo 491791 1253627 := bstep (se 1 (by rfl) ⟨940220, by rfl⟩ : syracuseStep 1253627 = 1880441) B1880441
theorem B6006545 : Blo 491791 6006545 := bstep (se 2 (by rfl) ⟨2252454, by rfl⟩ : syracuseStep 6006545 = 4504909) B4504909
theorem B503503 : Blo 491791 503503 := bstep (se 1 (by rfl) ⟨377627, by rfl⟩ : syracuseStep 503503 = 755255) B755255
theorem B48606965 : Blo 491791 48606965 := bstep (se 5 (by rfl) ⟨2278451, by rfl⟩ : syracuseStep 48606965 = 4556903) B4556903
theorem B6404255 : Blo 491791 6404255 := bstep (se 1 (by rfl) ⟨4803191, by rfl⟩ : syracuseStep 6404255 = 9606383) B9606383
theorem B834367 : Blo 491791 834367 := bstep (se 1 (by rfl) ⟨625775, by rfl⟩ : syracuseStep 834367 = 1251551) B1251551
theorem B2800979 : Blo 491791 2800979 := bstep (se 1 (by rfl) ⟨2100734, by rfl⟩ : syracuseStep 2800979 = 4201469) B4201469
theorem B3751433 : Blo 491791 3751433 := bstep (se 2 (by rfl) ⟨1406787, by rfl⟩ : syracuseStep 3751433 = 2813575) B2813575
theorem B9027935 : Blo 491791 9027935 := bstep (se 1 (by rfl) ⟨6770951, by rfl⟩ : syracuseStep 9027935 = 13541903) B13541903
theorem B10110683 : Blo 491791 10110683 := bstep (se 1 (by rfl) ⟨7583012, by rfl⟩ : syracuseStep 10110683 = 15166025) B15166025
theorem B739583 : Blo 491791 739583 := bstep (se 1 (by rfl) ⟨554687, by rfl⟩ : syracuseStep 739583 = 1109375) B1109375
theorem B740969 : Blo 491791 740969 := bstep (se 2 (by rfl) ⟨277863, by rfl⟩ : syracuseStep 740969 = 555727) B555727
theorem B2675197 : Blo 491791 2675197 := bstep (se 3 (by rfl) ⟨501599, by rfl⟩ : syracuseStep 2675197 = 1003199) B1003199
theorem B4281275 : Blo 491791 4281275 := bstep (se 1 (by rfl) ⟨3210956, by rfl⟩ : syracuseStep 4281275 = 6421913) B6421913
theorem B4873081 : Blo 491791 4873081 := bstep (se 2 (by rfl) ⟨1827405, by rfl⟩ : syracuseStep 4873081 = 3654811) B3654811
theorem B2810159 : Blo 491791 2810159 := bstep (se 1 (by rfl) ⟨2107619, by rfl⟩ : syracuseStep 2810159 = 4215239) B4215239
theorem B3206591 : Blo 491791 3206591 := bstep (se 1 (by rfl) ⟨2404943, by rfl⟩ : syracuseStep 3206591 = 4809887) B4809887
theorem B12054743 : Blo 491791 12054743 := bstep (se 1 (by rfl) ⟨9041057, by rfl⟩ : syracuseStep 12054743 = 18082115) B18082115
theorem B11989255 : Blo 491791 11989255 := bstep (se 1 (by rfl) ⟨8991941, by rfl⟩ : syracuseStep 11989255 = 17983883) B17983883
theorem B1110527 : Blo 491791 1110527 := bstep (se 1 (by rfl) ⟨832895, by rfl⟩ : syracuseStep 1110527 = 1665791) B1665791
theorem B1110761 : Blo 491791 1110761 := bstep (se 2 (by rfl) ⟨416535, by rfl⟩ : syracuseStep 1110761 = 833071) B833071
theorem B14285483 : Blo 491791 14285483 := bstep (se 1 (by rfl) ⟨10714112, by rfl⟩ : syracuseStep 14285483 = 21428225) B21428225
theorem B15990979 : Blo 491791 15990979 := bstep (se 1 (by rfl) ⟨11993234, by rfl⟩ : syracuseStep 15990979 = 23986469) B23986469
theorem B493055 : Blo 491791 493055 := bstep (se 1 (by rfl) ⟨369791, by rfl⟩ : syracuseStep 493055 = 739583) B739583
theorem B788699 : Blo 491791 788699 := bstep (se 1 (by rfl) ⟨591524, by rfl⟩ : syracuseStep 788699 = 1183049) B1183049
theorem B493979 : Blo 491791 493979 := bstep (se 1 (by rfl) ⟨370484, by rfl⟩ : syracuseStep 493979 = 740969) B740969
theorem B1873439 : Blo 491791 1873439 := bstep (se 1 (by rfl) ⟨1405079, by rfl⟩ : syracuseStep 1873439 = 2810159) B2810159
theorem B1578665 : Blo 491791 1578665 := bstep (se 2 (by rfl) ⟨591999, by rfl⟩ : syracuseStep 1578665 = 1183999) B1183999
theorem B4004363 : Blo 491791 4004363 := bstep (se 1 (by rfl) ⟨3003272, by rfl⟩ : syracuseStep 4004363 = 6006545) B6006545
theorem B2137727 : Blo 491791 2137727 := bstep (se 1 (by rfl) ⟨1603295, by rfl⟩ : syracuseStep 2137727 = 3206591) B3206591
theorem B8036495 : Blo 491791 8036495 := bstep (se 1 (by rfl) ⟨6027371, by rfl⟩ : syracuseStep 8036495 = 12054743) B12054743
theorem B6497441 : Blo 491791 6497441 := bstep (se 2 (by rfl) ⟨2436540, by rfl⟩ : syracuseStep 6497441 = 4873081) B4873081
theorem B4269503 : Blo 491791 4269503 := bstep (se 1 (by rfl) ⟨3202127, by rfl⟩ : syracuseStep 4269503 = 6404255) B6404255
theorem B2500955 : Blo 491791 2500955 := bstep (se 1 (by rfl) ⟨1875716, by rfl⟩ : syracuseStep 2500955 = 3751433) B3751433
theorem B831991 : Blo 491791 831991 := bstep (se 1 (by rfl) ⟨623993, by rfl⟩ : syracuseStep 831991 = 1247987) B1247987
theorem B832511 : Blo 491791 832511 := bstep (se 1 (by rfl) ⟨624383, by rfl⟩ : syracuseStep 832511 = 1248767) B1248767
theorem B11416733 : Blo 491791 11416733 := bstep (se 3 (by rfl) ⟨2140637, by rfl⟩ : syracuseStep 11416733 = 4281275) B4281275
theorem B834671 : Blo 491791 834671 := bstep (se 1 (by rfl) ⟨626003, by rfl⟩ : syracuseStep 834671 = 1252007) B1252007
theorem B835751 : Blo 491791 835751 := bstep (se 1 (by rfl) ⟨626813, by rfl⟩ : syracuseStep 835751 = 1253627) B1253627
theorem B740351 : Blo 491791 740351 := bstep (se 1 (by rfl) ⟨555263, by rfl⟩ : syracuseStep 740351 = 1110527) B1110527
theorem B740507 : Blo 491791 740507 := bstep (se 1 (by rfl) ⟨555380, by rfl⟩ : syracuseStep 740507 = 1110761) B1110761
theorem B9523655 : Blo 491791 9523655 := bstep (se 1 (by rfl) ⟨7142741, by rfl⟩ : syracuseStep 9523655 = 14285483) B14285483
theorem B6018623 : Blo 491791 6018623 := bstep (se 1 (by rfl) ⟨4513967, by rfl⟩ : syracuseStep 6018623 = 9027935) B9027935
theorem B6740455 : Blo 491791 6740455 := bstep (se 1 (by rfl) ⟨5055341, by rfl⟩ : syracuseStep 6740455 = 10110683) B10110683
theorem B747839 : Blo 491791 747839 := bstep (se 1 (by rfl) ⟨560879, by rfl⟩ : syracuseStep 747839 = 1121759) B1121759
theorem B15985673 : Blo 491791 15985673 := bstep (se 2 (by rfl) ⟨5994627, by rfl⟩ : syracuseStep 15985673 = 11989255) B11989255
theorem B3566929 : Blo 491791 3566929 := bstep (se 2 (by rfl) ⟨1337598, by rfl⟩ : syracuseStep 3566929 = 2675197) B2675197
theorem B32404643 : Blo 491791 32404643 := bstep (se 1 (by rfl) ⟨24303482, by rfl⟩ : syracuseStep 32404643 = 48606965) B48606965
theorem B2685349 : Blo 491791 2685349 := bstep (se 4 (by rfl) ⟨251751, by rfl⟩ : syracuseStep 2685349 = 503503) B503503
theorem B1112489 : Blo 491791 1112489 := bstep (se 2 (by rfl) ⟨417183, by rfl⟩ : syracuseStep 1112489 = 834367) B834367
theorem B1867319 : Blo 491791 1867319 := bstep (se 1 (by rfl) ⟨1400489, by rfl⟩ : syracuseStep 1867319 = 2800979) B2800979
theorem B557167 : Blo 491791 557167 := bstep (se 1 (by rfl) ⟨417875, by rfl⟩ : syracuseStep 557167 = 835751) B835751
theorem B525799 : Blo 491791 525799 := bstep (se 1 (by rfl) ⟨394349, by rfl⟩ : syracuseStep 525799 = 788699) B788699
theorem B493567 : Blo 491791 493567 := bstep (se 1 (by rfl) ⟨370175, by rfl⟩ : syracuseStep 493567 = 740351) B740351
theorem B493671 : Blo 491791 493671 := bstep (se 1 (by rfl) ⟨370253, by rfl⟩ : syracuseStep 493671 = 740507) B740507
theorem B1248959 : Blo 491791 1248959 := bstep (se 1 (by rfl) ⟨936719, by rfl⟩ : syracuseStep 1248959 = 1873439) B1873439
theorem B1052443 : Blo 491791 1052443 := bstep (se 1 (by rfl) ⟨789332, by rfl⟩ : syracuseStep 1052443 = 1578665) B1578665
theorem B4755905 : Blo 491791 4755905 := bstep (se 2 (by rfl) ⟨1783464, by rfl⟩ : syracuseStep 4755905 = 3566929) B3566929
theorem B4331627 : Blo 491791 4331627 := bstep (se 1 (by rfl) ⟨3248720, by rfl⟩ : syracuseStep 4331627 = 6497441) B6497441
theorem B10657115 : Blo 491791 10657115 := bstep (se 1 (by rfl) ⟨7992836, by rfl⟩ : syracuseStep 10657115 = 15985673) B15985673
theorem B3580465 : Blo 491791 3580465 := bstep (se 2 (by rfl) ⟨1342674, by rfl⟩ : syracuseStep 3580465 = 2685349) B2685349
theorem B8987273 : Blo 491791 8987273 := bstep (se 2 (by rfl) ⟨3370227, by rfl⟩ : syracuseStep 8987273 = 6740455) B6740455
theorem B7611155 : Blo 491791 7611155 := bstep (se 1 (by rfl) ⟨5708366, by rfl⟩ : syracuseStep 7611155 = 11416733) B11416733
theorem B21603095 : Blo 491791 21603095 := bstep (se 1 (by rfl) ⟨16202321, by rfl⟩ : syracuseStep 21603095 = 32404643) B32404643
theorem B4012415 : Blo 491791 4012415 := bstep (se 1 (by rfl) ⟨3009311, by rfl⟩ : syracuseStep 4012415 = 6018623) B6018623
theorem B1425151 : Blo 491791 1425151 := bstep (se 1 (by rfl) ⟨1068863, by rfl⟩ : syracuseStep 1425151 = 2137727) B2137727
theorem B5357663 : Blo 491791 5357663 := bstep (se 1 (by rfl) ⟨4018247, by rfl⟩ : syracuseStep 5357663 = 8036495) B8036495
theorem B741659 : Blo 491791 741659 := bstep (se 1 (by rfl) ⟨556244, by rfl⟩ : syracuseStep 741659 = 1112489) B1112489
theorem B21321305 : Blo 491791 21321305 := bstep (se 2 (by rfl) ⟨7995489, by rfl⟩ : syracuseStep 21321305 = 15990979) B15990979
theorem B6349103 : Blo 491791 6349103 := bstep (se 1 (by rfl) ⟨4761827, by rfl⟩ : syracuseStep 6349103 = 9523655) B9523655
theorem B1109321 : Blo 491791 1109321 := bstep (se 2 (by rfl) ⟨415995, by rfl⟩ : syracuseStep 1109321 = 831991) B831991
theorem B1994237 : Blo 491791 1994237 := bstep (se 3 (by rfl) ⟨373919, by rfl⟩ : syracuseStep 1994237 = 747839) B747839
theorem B2846335 : Blo 491791 2846335 := bstep (se 1 (by rfl) ⟨2134751, by rfl⟩ : syracuseStep 2846335 = 4269503) B4269503
theorem B10678301 : Blo 491791 10678301 := bstep (se 3 (by rfl) ⟨2002181, by rfl⟩ : syracuseStep 10678301 = 4004363) B4004363
theorem B1667303 : Blo 491791 1667303 := bstep (se 1 (by rfl) ⟨1250477, by rfl⟩ : syracuseStep 1667303 = 2500955) B2500955
theorem B555007 : Blo 491791 555007 := bstep (se 1 (by rfl) ⟨416255, by rfl⟩ : syracuseStep 555007 = 832511) B832511
theorem B556447 : Blo 491791 556447 := bstep (se 1 (by rfl) ⟨417335, by rfl⟩ : syracuseStep 556447 = 834671) B834671
theorem B1244879 : Blo 491791 1244879 := bstep (se 1 (by rfl) ⟨933659, by rfl⟩ : syracuseStep 1244879 = 1867319) B1867319
theorem B3571775 : Blo 491791 3571775 := bstep (se 1 (by rfl) ⟨2678831, by rfl⟩ : syracuseStep 3571775 = 5357663) B5357663
theorem B494439 : Blo 491791 494439 := bstep (se 1 (by rfl) ⟨370829, by rfl⟩ : syracuseStep 494439 = 741659) B741659
theorem B2887751 : Blo 491791 2887751 := bstep (se 1 (by rfl) ⟨2165813, by rfl⟩ : syracuseStep 2887751 = 4331627) B4331627
theorem B4232735 : Blo 491791 4232735 := bstep (se 1 (by rfl) ⟨3174551, by rfl⟩ : syracuseStep 4232735 = 6349103) B6349103
theorem B7118867 : Blo 491791 7118867 := bstep (se 1 (by rfl) ⟨5339150, by rfl⟩ : syracuseStep 7118867 = 10678301) B10678301
theorem B829919 : Blo 491791 829919 := bstep (se 1 (by rfl) ⟨622439, by rfl⟩ : syracuseStep 829919 = 1244879) B1244879
theorem B701065 : Blo 491791 701065 := bstep (se 2 (by rfl) ⟨262899, by rfl⟩ : syracuseStep 701065 = 525799) B525799
theorem B832639 : Blo 491791 832639 := bstep (se 1 (by rfl) ⟨624479, by rfl⟩ : syracuseStep 832639 = 1248959) B1248959
theorem B14402063 : Blo 491791 14402063 := bstep (se 1 (by rfl) ⟨10801547, by rfl⟩ : syracuseStep 14402063 = 21603095) B21603095
theorem B739547 : Blo 491791 739547 := bstep (se 1 (by rfl) ⟨554660, by rfl⟩ : syracuseStep 739547 = 1109321) B1109321
theorem B1329491 : Blo 491791 1329491 := bstep (se 1 (by rfl) ⟨997118, by rfl⟩ : syracuseStep 1329491 = 1994237) B1994237
theorem B740009 : Blo 491791 740009 := bstep (se 2 (by rfl) ⟨277503, by rfl⟩ : syracuseStep 740009 = 555007) B555007
theorem B2674943 : Blo 491791 2674943 := bstep (se 1 (by rfl) ⟨2006207, by rfl⟩ : syracuseStep 2674943 = 4012415) B4012415
theorem B741929 : Blo 491791 741929 := bstep (se 2 (by rfl) ⟨278223, by rfl⟩ : syracuseStep 741929 = 556447) B556447
theorem B742889 : Blo 491791 742889 := bstep (se 2 (by rfl) ⟨278583, by rfl⟩ : syracuseStep 742889 = 557167) B557167
theorem B4773953 : Blo 491791 4773953 := bstep (se 2 (by rfl) ⟨1790232, by rfl⟩ : syracuseStep 4773953 = 3580465) B3580465
theorem B3170603 : Blo 491791 3170603 := bstep (se 1 (by rfl) ⟨2377952, by rfl⟩ : syracuseStep 3170603 = 4755905) B4755905
theorem B14214203 : Blo 491791 14214203 := bstep (se 1 (by rfl) ⟨10660652, by rfl⟩ : syracuseStep 14214203 = 21321305) B21321305
theorem B3795113 : Blo 491791 3795113 := bstep (se 2 (by rfl) ⟨1423167, by rfl⟩ : syracuseStep 3795113 = 2846335) B2846335
theorem B7104743 : Blo 491791 7104743 := bstep (se 1 (by rfl) ⟨5328557, by rfl⟩ : syracuseStep 7104743 = 10657115) B10657115
theorem B1403257 : Blo 491791 1403257 := bstep (se 2 (by rfl) ⟨526221, by rfl⟩ : syracuseStep 1403257 = 1052443) B1052443
theorem B5991515 : Blo 491791 5991515 := bstep (se 1 (by rfl) ⟨4493636, by rfl⟩ : syracuseStep 5991515 = 8987273) B8987273
theorem B5074103 : Blo 491791 5074103 := bstep (se 1 (by rfl) ⟨3805577, by rfl⟩ : syracuseStep 5074103 = 7611155) B7611155
theorem B1111535 : Blo 491791 1111535 := bstep (se 1 (by rfl) ⟨833651, by rfl⟩ : syracuseStep 1111535 = 1667303) B1667303
theorem B1900201 : Blo 491791 1900201 := bstep (se 2 (by rfl) ⟨712575, by rfl⟩ : syracuseStep 1900201 = 1425151) B1425151
theorem B7700669 : Blo 491791 7700669 := bstep (se 3 (by rfl) ⟨1443875, by rfl⟩ : syracuseStep 7700669 = 2887751) B2887751
theorem B9601375 : Blo 491791 9601375 := bstep (se 1 (by rfl) ⟨7201031, by rfl⟩ : syracuseStep 9601375 = 14402063) B14402063
theorem B8454941 : Blo 491791 8454941 := bstep (se 3 (by rfl) ⟨1585301, by rfl⟩ : syracuseStep 8454941 = 3170603) B3170603
theorem B493031 : Blo 491791 493031 := bstep (se 1 (by rfl) ⟨369773, by rfl⟩ : syracuseStep 493031 = 739547) B739547
theorem B493339 : Blo 491791 493339 := bstep (se 1 (by rfl) ⟨370004, by rfl⟩ : syracuseStep 493339 = 740009) B740009
theorem B494619 : Blo 491791 494619 := bstep (se 1 (by rfl) ⟨370964, by rfl⟩ : syracuseStep 494619 = 741929) B741929
theorem B1871009 : Blo 491791 1871009 := bstep (se 2 (by rfl) ⟨701628, by rfl⟩ : syracuseStep 1871009 = 1403257) B1403257
theorem B495259 : Blo 491791 495259 := bstep (se 1 (by rfl) ⟨371444, by rfl⟩ : syracuseStep 495259 = 742889) B742889
theorem B2821823 : Blo 491791 2821823 := bstep (se 1 (by rfl) ⟨2116367, by rfl⟩ : syracuseStep 2821823 = 4232735) B4232735
theorem B3182635 : Blo 491791 3182635 := bstep (se 1 (by rfl) ⟨2386976, by rfl⟩ : syracuseStep 3182635 = 4773953) B4773953
theorem B9476135 : Blo 491791 9476135 := bstep (se 1 (by rfl) ⟨7107101, by rfl⟩ : syracuseStep 9476135 = 14214203) B14214203
theorem B3545309 : Blo 491791 3545309 := bstep (se 3 (by rfl) ⟨664745, by rfl⟩ : syracuseStep 3545309 = 1329491) B1329491
theorem B2530075 : Blo 491791 2530075 := bstep (se 1 (by rfl) ⟨1897556, by rfl⟩ : syracuseStep 2530075 = 3795113) B3795113
theorem B3382735 : Blo 491791 3382735 := bstep (se 1 (by rfl) ⟨2537051, by rfl⟩ : syracuseStep 3382735 = 5074103) B5074103
theorem B2533601 : Blo 491791 2533601 := bstep (se 2 (by rfl) ⟨950100, by rfl⟩ : syracuseStep 2533601 = 1900201) B1900201
theorem B1783295 : Blo 491791 1783295 := bstep (se 1 (by rfl) ⟨1337471, by rfl⟩ : syracuseStep 1783295 = 2674943) B2674943
theorem B934753 : Blo 491791 934753 := bstep (se 2 (by rfl) ⟨350532, by rfl⟩ : syracuseStep 934753 = 701065) B701065
theorem B4736495 : Blo 491791 4736495 := bstep (se 1 (by rfl) ⟨3552371, by rfl⟩ : syracuseStep 4736495 = 7104743) B7104743
theorem B741023 : Blo 491791 741023 := bstep (se 1 (by rfl) ⟨555767, by rfl⟩ : syracuseStep 741023 = 1111535) B1111535
theorem B2381183 : Blo 491791 2381183 := bstep (se 1 (by rfl) ⟨1785887, by rfl⟩ : syracuseStep 2381183 = 3571775) B3571775
theorem B4745911 : Blo 491791 4745911 := bstep (se 1 (by rfl) ⟨3559433, by rfl⟩ : syracuseStep 4745911 = 7118867) B7118867
theorem B1110185 : Blo 491791 1110185 := bstep (se 2 (by rfl) ⟨416319, by rfl⟩ : syracuseStep 1110185 = 832639) B832639
theorem B553279 : Blo 491791 553279 := bstep (se 1 (by rfl) ⟨414959, by rfl⟩ : syracuseStep 553279 = 829919) B829919
theorem B3994343 : Blo 491791 3994343 := bstep (se 1 (by rfl) ⟨2995757, by rfl⟩ : syracuseStep 3994343 = 5991515) B5991515
theorem B5636627 : Blo 491791 5636627 := bstep (se 1 (by rfl) ⟨4227470, by rfl⟩ : syracuseStep 5636627 = 8454941) B8454941
theorem B1246337 : Blo 491791 1246337 := bstep (se 2 (by rfl) ⟨467376, by rfl⟩ : syracuseStep 1246337 = 934753) B934753
theorem B1247339 : Blo 491791 1247339 := bstep (se 1 (by rfl) ⟨935504, by rfl⟩ : syracuseStep 1247339 = 1871009) B1871009
theorem B494015 : Blo 491791 494015 := bstep (se 1 (by rfl) ⟨370511, by rfl⟩ : syracuseStep 494015 = 741023) B741023
theorem B6327881 : Blo 491791 6327881 := bstep (se 2 (by rfl) ⟨2372955, by rfl⟩ : syracuseStep 6327881 = 4745911) B4745911
theorem B2363539 : Blo 491791 2363539 := bstep (se 1 (by rfl) ⟨1772654, by rfl⟩ : syracuseStep 2363539 = 3545309) B3545309
theorem B2662895 : Blo 491791 2662895 := bstep (se 1 (by rfl) ⟨1997171, by rfl⟩ : syracuseStep 2662895 = 3994343) B3994343
theorem B1188863 : Blo 491791 1188863 := bstep (se 1 (by rfl) ⟨891647, by rfl⟩ : syracuseStep 1188863 = 1783295) B1783295
theorem B3157663 : Blo 491791 3157663 := bstep (se 1 (by rfl) ⟨2368247, by rfl⟩ : syracuseStep 3157663 = 4736495) B4736495
theorem B1881215 : Blo 491791 1881215 := bstep (se 1 (by rfl) ⟨1410911, by rfl⟩ : syracuseStep 1881215 = 2821823) B2821823
theorem B1587455 : Blo 491791 1587455 := bstep (se 1 (by rfl) ⟨1190591, by rfl⟩ : syracuseStep 1587455 = 2381183) B2381183
theorem B4243513 : Blo 491791 4243513 := bstep (se 2 (by rfl) ⟨1591317, by rfl⟩ : syracuseStep 4243513 = 3182635) B3182635
theorem B737705 : Blo 491791 737705 := bstep (se 2 (by rfl) ⟨276639, by rfl⟩ : syracuseStep 737705 = 553279) B553279
theorem B1689067 : Blo 491791 1689067 := bstep (se 1 (by rfl) ⟨1266800, by rfl⟩ : syracuseStep 1689067 = 2533601) B2533601
theorem B740123 : Blo 491791 740123 := bstep (se 1 (by rfl) ⟨555092, by rfl⟩ : syracuseStep 740123 = 1110185) B1110185
theorem B4510313 : Blo 491791 4510313 := bstep (se 2 (by rfl) ⟨1691367, by rfl⟩ : syracuseStep 4510313 = 3382735) B3382735
theorem B5133779 : Blo 491791 5133779 := bstep (se 1 (by rfl) ⟨3850334, by rfl⟩ : syracuseStep 5133779 = 7700669) B7700669
theorem B12801833 : Blo 491791 12801833 := bstep (se 2 (by rfl) ⟨4800687, by rfl⟩ : syracuseStep 12801833 = 9601375) B9601375
theorem B6317423 : Blo 491791 6317423 := bstep (se 1 (by rfl) ⟨4738067, by rfl⟩ : syracuseStep 6317423 = 9476135) B9476135
theorem B3373433 : Blo 491791 3373433 := bstep (se 2 (by rfl) ⟨1265037, by rfl⟩ : syracuseStep 3373433 = 2530075) B2530075
theorem B491803 : Blo 491791 491803 := bstep (se 1 (by rfl) ⟨368852, by rfl⟩ : syracuseStep 491803 = 737705) B737705
theorem B493415 : Blo 491791 493415 := bstep (se 1 (by rfl) ⟨370061, by rfl⟩ : syracuseStep 493415 = 740123) B740123
theorem B3151385 : Blo 491791 3151385 := bstep (se 2 (by rfl) ⟨1181769, by rfl⟩ : syracuseStep 3151385 = 2363539) B2363539
theorem B792575 : Blo 491791 792575 := bstep (se 1 (by rfl) ⟨594431, by rfl⟩ : syracuseStep 792575 = 1188863) B1188863
theorem B1254143 : Blo 491791 1254143 := bstep (se 1 (by rfl) ⟨940607, by rfl⟩ : syracuseStep 1254143 = 1881215) B1881215
theorem B1058303 : Blo 491791 1058303 := bstep (se 1 (by rfl) ⟨793727, by rfl⟩ : syracuseStep 1058303 = 1587455) B1587455
theorem B830891 : Blo 491791 830891 := bstep (se 1 (by rfl) ⟨623168, by rfl⟩ : syracuseStep 830891 = 1246337) B1246337
theorem B831559 : Blo 491791 831559 := bstep (se 1 (by rfl) ⟨623669, by rfl⟩ : syracuseStep 831559 = 1247339) B1247339
theorem B3422519 : Blo 491791 3422519 := bstep (se 1 (by rfl) ⟨2566889, by rfl⟩ : syracuseStep 3422519 = 5133779) B5133779
theorem B8534555 : Blo 491791 8534555 := bstep (se 1 (by rfl) ⟨6400916, by rfl⟩ : syracuseStep 8534555 = 12801833) B12801833
theorem B4210217 : Blo 491791 4210217 := bstep (se 2 (by rfl) ⟨1578831, by rfl⟩ : syracuseStep 4210217 = 3157663) B3157663
theorem B4211615 : Blo 491791 4211615 := bstep (se 1 (by rfl) ⟨3158711, by rfl⟩ : syracuseStep 4211615 = 6317423) B6317423
theorem B2248955 : Blo 491791 2248955 := bstep (se 1 (by rfl) ⟨1686716, by rfl⟩ : syracuseStep 2248955 = 3373433) B3373433
theorem B5658017 : Blo 491791 5658017 := bstep (se 2 (by rfl) ⟨2121756, by rfl⟩ : syracuseStep 5658017 = 4243513) B4243513
theorem B3757751 : Blo 491791 3757751 := bstep (se 1 (by rfl) ⟨2818313, by rfl⟩ : syracuseStep 3757751 = 5636627) B5636627
theorem B7101053 : Blo 491791 7101053 := bstep (se 3 (by rfl) ⟨1331447, by rfl⟩ : syracuseStep 7101053 = 2662895) B2662895
theorem B2252089 : Blo 491791 2252089 := bstep (se 2 (by rfl) ⟨844533, by rfl⟩ : syracuseStep 2252089 = 1689067) B1689067
theorem B4218587 : Blo 491791 4218587 := bstep (se 1 (by rfl) ⟨3163940, by rfl⟩ : syracuseStep 4218587 = 6327881) B6327881
theorem B3006875 : Blo 491791 3006875 := bstep (se 1 (by rfl) ⟨2255156, by rfl⟩ : syracuseStep 3006875 = 4510313) B4510313
theorem B2100923 : Blo 491791 2100923 := bstep (se 1 (by rfl) ⟨1575692, by rfl⟩ : syracuseStep 2100923 = 3151385) B3151385
theorem B2822141 : Blo 491791 2822141 := bstep (se 3 (by rfl) ⟨529151, by rfl⟩ : syracuseStep 2822141 = 1058303) B1058303
theorem B528383 : Blo 491791 528383 := bstep (se 1 (by rfl) ⟨396287, by rfl⟩ : syracuseStep 528383 = 792575) B792575
theorem B2004583 : Blo 491791 2004583 := bstep (se 1 (by rfl) ⟨1503437, by rfl⟩ : syracuseStep 2004583 = 3006875) B3006875
theorem B15088045 : Blo 491791 15088045 := bstep (se 3 (by rfl) ⟨2829008, by rfl⟩ : syracuseStep 15088045 = 5658017) B5658017
theorem B2505167 : Blo 491791 2505167 := bstep (se 1 (by rfl) ⟨1878875, by rfl⟩ : syracuseStep 2505167 = 3757751) B3757751
theorem B4734035 : Blo 491791 4734035 := bstep (se 1 (by rfl) ⟨3550526, by rfl⟩ : syracuseStep 4734035 = 7101053) B7101053
theorem B836095 : Blo 491791 836095 := bstep (se 1 (by rfl) ⟨627071, by rfl⟩ : syracuseStep 836095 = 1254143) B1254143
theorem B12011141 : Blo 491791 12011141 := bstep (se 4 (by rfl) ⟨1126044, by rfl⟩ : syracuseStep 12011141 = 2252089) B2252089
theorem B2281679 : Blo 491791 2281679 := bstep (se 1 (by rfl) ⟨1711259, by rfl⟩ : syracuseStep 2281679 = 3422519) B3422519
theorem B5689703 : Blo 491791 5689703 := bstep (se 1 (by rfl) ⟨4267277, by rfl⟩ : syracuseStep 5689703 = 8534555) B8534555
theorem B2806811 : Blo 491791 2806811 := bstep (se 1 (by rfl) ⟨2105108, by rfl⟩ : syracuseStep 2806811 = 4210217) B4210217
theorem B2807743 : Blo 491791 2807743 := bstep (se 1 (by rfl) ⟨2105807, by rfl⟩ : syracuseStep 2807743 = 4211615) B4211615
theorem B1499303 : Blo 491791 1499303 := bstep (se 1 (by rfl) ⟨1124477, by rfl⟩ : syracuseStep 1499303 = 2248955) B2248955
theorem B2812391 : Blo 491791 2812391 := bstep (se 1 (by rfl) ⟨2109293, by rfl⟩ : syracuseStep 2812391 = 4218587) B4218587
theorem B1108745 : Blo 491791 1108745 := bstep (se 2 (by rfl) ⟨415779, by rfl⟩ : syracuseStep 1108745 = 831559) B831559
theorem B553927 : Blo 491791 553927 := bstep (se 1 (by rfl) ⟨415445, by rfl⟩ : syracuseStep 553927 = 830891) B830891
theorem B1114793 : Blo 491791 1114793 := bstep (se 2 (by rfl) ⟨418047, by rfl⟩ : syracuseStep 1114793 = 836095) B836095
theorem B15172541 : Blo 491791 15172541 := bstep (se 3 (by rfl) ⟨2844851, by rfl⟩ : syracuseStep 15172541 = 5689703) B5689703
theorem B1871207 : Blo 491791 1871207 := bstep (se 1 (by rfl) ⟨1403405, by rfl⟩ : syracuseStep 1871207 = 2806811) B2806811
theorem B1874927 : Blo 491791 1874927 := bstep (se 1 (by rfl) ⟨1406195, by rfl⟩ : syracuseStep 1874927 = 2812391) B2812391
theorem B3743657 : Blo 491791 3743657 := bstep (se 2 (by rfl) ⟨1403871, by rfl⟩ : syracuseStep 3743657 = 2807743) B2807743
theorem B3156023 : Blo 491791 3156023 := bstep (se 1 (by rfl) ⟨2367017, by rfl⟩ : syracuseStep 3156023 = 4734035) B4734035
theorem B8007427 : Blo 491791 8007427 := bstep (se 1 (by rfl) ⟨6005570, by rfl⟩ : syracuseStep 8007427 = 12011141) B12011141
theorem B1881427 : Blo 491791 1881427 := bstep (se 1 (by rfl) ⟨1411070, by rfl⟩ : syracuseStep 1881427 = 2822141) B2822141
theorem B1521119 : Blo 491791 1521119 := bstep (se 1 (by rfl) ⟨1140839, by rfl⟩ : syracuseStep 1521119 = 2281679) B2281679
theorem B999535 : Blo 491791 999535 := bstep (se 1 (by rfl) ⟨749651, by rfl⟩ : syracuseStep 999535 = 1499303) B1499303
theorem B738569 : Blo 491791 738569 := bstep (se 2 (by rfl) ⟨276963, by rfl⟩ : syracuseStep 738569 = 553927) B553927
theorem B739163 : Blo 491791 739163 := bstep (se 1 (by rfl) ⟨554372, by rfl⟩ : syracuseStep 739163 = 1108745) B1108745
theorem B2672777 : Blo 491791 2672777 := bstep (se 2 (by rfl) ⟨1002291, by rfl⟩ : syracuseStep 2672777 = 2004583) B2004583
theorem B1400615 : Blo 491791 1400615 := bstep (se 1 (by rfl) ⟨1050461, by rfl⟩ : syracuseStep 1400615 = 2100923) B2100923
theorem B20117393 : Blo 491791 20117393 := bstep (se 2 (by rfl) ⟨7544022, by rfl⟩ : syracuseStep 20117393 = 15088045) B15088045
theorem B1670111 : Blo 491791 1670111 := bstep (se 1 (by rfl) ⟨1252583, by rfl⟩ : syracuseStep 1670111 = 2505167) B2505167
theorem B1409021 : Blo 491791 1409021 := bstep (se 3 (by rfl) ⟨264191, by rfl⟩ : syracuseStep 1409021 = 528383) B528383
theorem B492379 : Blo 491791 492379 := bstep (se 1 (by rfl) ⟨369284, by rfl⟩ : syracuseStep 492379 = 738569) B738569
theorem B492775 : Blo 491791 492775 := bstep (se 1 (by rfl) ⟨369581, by rfl⟩ : syracuseStep 492775 = 739163) B739163
theorem B1247471 : Blo 491791 1247471 := bstep (se 1 (by rfl) ⟨935603, by rfl⟩ : syracuseStep 1247471 = 1871207) B1871207
theorem B1249951 : Blo 491791 1249951 := bstep (se 1 (by rfl) ⟨937463, by rfl⟩ : syracuseStep 1249951 = 1874927) B1874927
theorem B2495771 : Blo 491791 2495771 := bstep (se 1 (by rfl) ⟨1871828, by rfl⟩ : syracuseStep 2495771 = 3743657) B3743657
theorem B2104015 : Blo 491791 2104015 := bstep (se 1 (by rfl) ⟨1578011, by rfl⟩ : syracuseStep 2104015 = 3156023) B3156023
theorem B13411595 : Blo 491791 13411595 := bstep (se 1 (by rfl) ⟨10058696, by rfl⟩ : syracuseStep 13411595 = 20117393) B20117393
theorem B1781851 : Blo 491791 1781851 := bstep (se 1 (by rfl) ⟨1336388, by rfl⟩ : syracuseStep 1781851 = 2672777) B2672777
theorem B933743 : Blo 491791 933743 := bstep (se 1 (by rfl) ⟨700307, by rfl⟩ : syracuseStep 933743 = 1400615) B1400615
theorem B2508569 : Blo 491791 2508569 := bstep (se 2 (by rfl) ⟨940713, by rfl⟩ : syracuseStep 2508569 = 1881427) B1881427
theorem B939347 : Blo 491791 939347 := bstep (se 1 (by rfl) ⟨704510, by rfl⟩ : syracuseStep 939347 = 1409021) B1409021
theorem B1332713 : Blo 491791 1332713 := bstep (se 2 (by rfl) ⟨499767, by rfl⟩ : syracuseStep 1332713 = 999535) B999535
theorem B743195 : Blo 491791 743195 := bstep (se 1 (by rfl) ⟨557396, by rfl⟩ : syracuseStep 743195 = 1114793) B1114793
theorem B10115027 : Blo 491791 10115027 := bstep (se 1 (by rfl) ⟨7586270, by rfl⟩ : syracuseStep 10115027 = 15172541) B15172541
theorem B4056317 : Blo 491791 4056317 := bstep (se 3 (by rfl) ⟨760559, by rfl⟩ : syracuseStep 4056317 = 1521119) B1521119
theorem B10676569 : Blo 491791 10676569 := bstep (se 2 (by rfl) ⟨4003713, by rfl⟩ : syracuseStep 10676569 = 8007427) B8007427
theorem B1113407 : Blo 491791 1113407 := bstep (se 1 (by rfl) ⟨835055, by rfl⟩ : syracuseStep 1113407 = 1670111) B1670111
theorem B1672379 : Blo 491791 1672379 := bstep (se 1 (by rfl) ⟨1254284, by rfl⟩ : syracuseStep 1672379 = 2508569) B2508569
theorem B626231 : Blo 491791 626231 := bstep (se 1 (by rfl) ⟨469673, by rfl⟩ : syracuseStep 626231 = 939347) B939347
theorem B888475 : Blo 491791 888475 := bstep (se 1 (by rfl) ⟨666356, by rfl⟩ : syracuseStep 888475 = 1332713) B1332713
theorem B495463 : Blo 491791 495463 := bstep (se 1 (by rfl) ⟨371597, by rfl⟩ : syracuseStep 495463 = 743195) B743195
theorem B831647 : Blo 491791 831647 := bstep (se 1 (by rfl) ⟨623735, by rfl⟩ : syracuseStep 831647 = 1247471) B1247471
theorem B14235425 : Blo 491791 14235425 := bstep (se 2 (by rfl) ⟨5338284, by rfl⟩ : syracuseStep 14235425 = 10676569) B10676569
theorem B35764253 : Blo 491791 35764253 := bstep (se 3 (by rfl) ⟨6705797, by rfl⟩ : syracuseStep 35764253 = 13411595) B13411595
theorem B2375801 : Blo 491791 2375801 := bstep (se 2 (by rfl) ⟨890925, by rfl⟩ : syracuseStep 2375801 = 1781851) B1781851
theorem B2704211 : Blo 491791 2704211 := bstep (se 1 (by rfl) ⟨2028158, by rfl⟩ : syracuseStep 2704211 = 4056317) B4056317
theorem B2805353 : Blo 491791 2805353 := bstep (se 2 (by rfl) ⟨1052007, by rfl⟩ : syracuseStep 2805353 = 2104015) B2104015
theorem B742271 : Blo 491791 742271 := bstep (se 1 (by rfl) ⟨556703, by rfl⟩ : syracuseStep 742271 = 1113407) B1113407
theorem B1663847 : Blo 491791 1663847 := bstep (se 1 (by rfl) ⟨1247885, by rfl⟩ : syracuseStep 1663847 = 2495771) B2495771
theorem B6743351 : Blo 491791 6743351 := bstep (se 1 (by rfl) ⟨5057513, by rfl⟩ : syracuseStep 6743351 = 10115027) B10115027
theorem B1666601 : Blo 491791 1666601 := bstep (se 2 (by rfl) ⟨624975, by rfl⟩ : syracuseStep 1666601 = 1249951) B1249951
theorem B622495 : Blo 491791 622495 := bstep (se 1 (by rfl) ⟨466871, by rfl⟩ : syracuseStep 622495 = 933743) B933743
theorem B1802807 : Blo 491791 1802807 := bstep (se 1 (by rfl) ⟨1352105, by rfl⟩ : syracuseStep 1802807 = 2704211) B2704211
theorem B1114919 : Blo 491791 1114919 := bstep (se 1 (by rfl) ⟨836189, by rfl⟩ : syracuseStep 1114919 = 1672379) B1672379
theorem B1870235 : Blo 491791 1870235 := bstep (se 1 (by rfl) ⟨1402676, by rfl⟩ : syracuseStep 1870235 = 2805353) B2805353
theorem B494847 : Blo 491791 494847 := bstep (se 1 (by rfl) ⟨371135, by rfl⟩ : syracuseStep 494847 = 742271) B742271
theorem B1184633 : Blo 491791 1184633 := bstep (se 2 (by rfl) ⟨444237, by rfl⟩ : syracuseStep 1184633 = 888475) B888475
theorem B4495567 : Blo 491791 4495567 := bstep (se 1 (by rfl) ⟨3371675, by rfl⟩ : syracuseStep 4495567 = 6743351) B6743351
theorem B829993 : Blo 491791 829993 := bstep (se 2 (by rfl) ⟨311247, by rfl⟩ : syracuseStep 829993 = 622495) B622495
theorem B1583867 : Blo 491791 1583867 := bstep (se 1 (by rfl) ⟨1187900, by rfl⟩ : syracuseStep 1583867 = 2375801) B2375801
theorem B9490283 : Blo 491791 9490283 := bstep (se 1 (by rfl) ⟨7117712, by rfl⟩ : syracuseStep 9490283 = 14235425) B14235425
theorem B23842835 : Blo 491791 23842835 := bstep (se 1 (by rfl) ⟨17882126, by rfl⟩ : syracuseStep 23842835 = 35764253) B35764253
theorem B1109231 : Blo 491791 1109231 := bstep (se 1 (by rfl) ⟨831923, by rfl⟩ : syracuseStep 1109231 = 1663847) B1663847
theorem B1111067 : Blo 491791 1111067 := bstep (se 1 (by rfl) ⟨833300, by rfl⟩ : syracuseStep 1111067 = 1666601) B1666601
theorem B554431 : Blo 491791 554431 := bstep (se 1 (by rfl) ⟨415823, by rfl⟩ : syracuseStep 554431 = 831647) B831647
theorem B1669949 : Blo 491791 1669949 := bstep (se 3 (by rfl) ⟨313115, by rfl⟩ : syracuseStep 1669949 = 626231) B626231
theorem B1246823 : Blo 491791 1246823 := bstep (se 1 (by rfl) ⟨935117, by rfl⟩ : syracuseStep 1246823 = 1870235) B1870235
theorem B6326855 : Blo 491791 6326855 := bstep (se 1 (by rfl) ⟨4745141, by rfl⟩ : syracuseStep 6326855 = 9490283) B9490283
theorem B15895223 : Blo 491791 15895223 := bstep (se 1 (by rfl) ⟨11921417, by rfl⟩ : syracuseStep 15895223 = 23842835) B23842835
theorem B789755 : Blo 491791 789755 := bstep (se 1 (by rfl) ⟨592316, by rfl⟩ : syracuseStep 789755 = 1184633) B1184633
theorem B1055911 : Blo 491791 1055911 := bstep (se 1 (by rfl) ⟨791933, by rfl⟩ : syracuseStep 1055911 = 1583867) B1583867
theorem B739241 : Blo 491791 739241 := bstep (se 2 (by rfl) ⟨277215, by rfl⟩ : syracuseStep 739241 = 554431) B554431
theorem B739487 : Blo 491791 739487 := bstep (se 1 (by rfl) ⟨554615, by rfl⟩ : syracuseStep 739487 = 1109231) B1109231
theorem B740711 : Blo 491791 740711 := bstep (se 1 (by rfl) ⟨555533, by rfl⟩ : syracuseStep 740711 = 1111067) B1111067
theorem B1201871 : Blo 491791 1201871 := bstep (se 1 (by rfl) ⟨901403, by rfl⟩ : syracuseStep 1201871 = 1802807) B1802807
theorem B743279 : Blo 491791 743279 := bstep (se 1 (by rfl) ⟨557459, by rfl⟩ : syracuseStep 743279 = 1114919) B1114919
theorem B1106657 : Blo 491791 1106657 := bstep (se 2 (by rfl) ⟨414996, by rfl⟩ : syracuseStep 1106657 = 829993) B829993
theorem B5994089 : Blo 491791 5994089 := bstep (se 2 (by rfl) ⟨2247783, by rfl⟩ : syracuseStep 5994089 = 4495567) B4495567
theorem B1113299 : Blo 491791 1113299 := bstep (se 1 (by rfl) ⟨834974, by rfl⟩ : syracuseStep 1113299 = 1669949) B1669949
theorem B492827 : Blo 491791 492827 := bstep (se 1 (by rfl) ⟨369620, by rfl⟩ : syracuseStep 492827 = 739241) B739241
theorem B492991 : Blo 491791 492991 := bstep (se 1 (by rfl) ⟨369743, by rfl⟩ : syracuseStep 492991 = 739487) B739487
theorem B493807 : Blo 491791 493807 := bstep (se 1 (by rfl) ⟨370355, by rfl⟩ : syracuseStep 493807 = 740711) B740711
theorem B495519 : Blo 491791 495519 := bstep (se 1 (by rfl) ⟨371639, by rfl⟩ : syracuseStep 495519 = 743279) B743279
theorem B2106013 : Blo 491791 2106013 := bstep (se 3 (by rfl) ⟨394877, by rfl⟩ : syracuseStep 2106013 = 789755) B789755
theorem B831215 : Blo 491791 831215 := bstep (se 1 (by rfl) ⟨623411, by rfl⟩ : syracuseStep 831215 = 1246823) B1246823
theorem B10596815 : Blo 491791 10596815 := bstep (se 1 (by rfl) ⟨7947611, by rfl⟩ : syracuseStep 10596815 = 15895223) B15895223
theorem B801247 : Blo 491791 801247 := bstep (se 1 (by rfl) ⟨600935, by rfl⟩ : syracuseStep 801247 = 1201871) B1201871
theorem B737771 : Blo 491791 737771 := bstep (se 1 (by rfl) ⟨553328, by rfl⟩ : syracuseStep 737771 = 1106657) B1106657
theorem B742199 : Blo 491791 742199 := bstep (se 1 (by rfl) ⟨556649, by rfl⟩ : syracuseStep 742199 = 1113299) B1113299
theorem B4217903 : Blo 491791 4217903 := bstep (se 1 (by rfl) ⟨3163427, by rfl⟩ : syracuseStep 4217903 = 6326855) B6326855
theorem B3996059 : Blo 491791 3996059 := bstep (se 1 (by rfl) ⟨2997044, by rfl⟩ : syracuseStep 3996059 = 5994089) B5994089
theorem B1407881 : Blo 491791 1407881 := bstep (se 2 (by rfl) ⟨527955, by rfl⟩ : syracuseStep 1407881 = 1055911) B1055911
theorem B491847 : Blo 491791 491847 := bstep (se 1 (by rfl) ⟨368885, by rfl⟩ : syracuseStep 491847 = 737771) B737771
theorem B494799 : Blo 491791 494799 := bstep (se 1 (by rfl) ⟨371099, by rfl⟩ : syracuseStep 494799 = 742199) B742199
theorem B10656157 : Blo 491791 10656157 := bstep (se 3 (by rfl) ⟨1998029, by rfl⟩ : syracuseStep 10656157 = 3996059) B3996059
theorem B3754349 : Blo 491791 3754349 := bstep (se 3 (by rfl) ⟨703940, by rfl⟩ : syracuseStep 3754349 = 1407881) B1407881
theorem B7064543 : Blo 491791 7064543 := bstep (se 1 (by rfl) ⟨5298407, by rfl⟩ : syracuseStep 7064543 = 10596815) B10596815
theorem B1068329 : Blo 491791 1068329 := bstep (se 2 (by rfl) ⟨400623, by rfl⟩ : syracuseStep 1068329 = 801247) B801247
theorem B2808017 : Blo 491791 2808017 := bstep (se 2 (by rfl) ⟨1053006, by rfl⟩ : syracuseStep 2808017 = 2106013) B2106013
theorem B2811935 : Blo 491791 2811935 := bstep (se 1 (by rfl) ⟨2108951, by rfl⟩ : syracuseStep 2811935 = 4217903) B4217903
theorem B554143 : Blo 491791 554143 := bstep (se 1 (by rfl) ⟨415607, by rfl⟩ : syracuseStep 554143 = 831215) B831215
theorem B1872011 : Blo 491791 1872011 := bstep (se 1 (by rfl) ⟨1404008, by rfl⟩ : syracuseStep 1872011 = 2808017) B2808017
theorem B1874623 : Blo 491791 1874623 := bstep (se 1 (by rfl) ⟨1405967, by rfl⟩ : syracuseStep 1874623 = 2811935) B2811935
theorem B2502899 : Blo 491791 2502899 := bstep (se 1 (by rfl) ⟨1877174, by rfl⟩ : syracuseStep 2502899 = 3754349) B3754349
theorem B738857 : Blo 491791 738857 := bstep (se 2 (by rfl) ⟨277071, by rfl⟩ : syracuseStep 738857 = 554143) B554143
theorem B14208209 : Blo 491791 14208209 := bstep (se 2 (by rfl) ⟨5328078, by rfl⟩ : syracuseStep 14208209 = 10656157) B10656157
theorem B18838781 : Blo 491791 18838781 := bstep (se 3 (by rfl) ⟨3532271, by rfl⟩ : syracuseStep 18838781 = 7064543) B7064543
theorem B2848877 : Blo 491791 2848877 := bstep (se 3 (by rfl) ⟨534164, by rfl⟩ : syracuseStep 2848877 = 1068329) B1068329
theorem B492571 : Blo 491791 492571 := bstep (se 1 (by rfl) ⟨369428, by rfl⟩ : syracuseStep 492571 = 738857) B738857
theorem B9472139 : Blo 491791 9472139 := bstep (se 1 (by rfl) ⟨7104104, by rfl⟩ : syracuseStep 9472139 = 14208209) B14208209
theorem B1248007 : Blo 491791 1248007 := bstep (se 1 (by rfl) ⟨936005, by rfl⟩ : syracuseStep 1248007 = 1872011) B1872011
theorem B12559187 : Blo 491791 12559187 := bstep (se 1 (by rfl) ⟨9419390, by rfl⟩ : syracuseStep 12559187 = 18838781) B18838781
theorem B2499497 : Blo 491791 2499497 := bstep (se 2 (by rfl) ⟨937311, by rfl⟩ : syracuseStep 2499497 = 1874623) B1874623
theorem B1668599 : Blo 491791 1668599 := bstep (se 1 (by rfl) ⟨1251449, by rfl⟩ : syracuseStep 1668599 = 2502899) B2502899
theorem B1899251 : Blo 491791 1899251 := bstep (se 1 (by rfl) ⟨1424438, by rfl⟩ : syracuseStep 1899251 = 2848877) B2848877
theorem B8372791 : Blo 491791 8372791 := bstep (se 1 (by rfl) ⟨6279593, by rfl⟩ : syracuseStep 8372791 = 12559187) B12559187
theorem B1266167 : Blo 491791 1266167 := bstep (se 1 (by rfl) ⟨949625, by rfl⟩ : syracuseStep 1266167 = 1899251) B1899251
theorem B6314759 : Blo 491791 6314759 := bstep (se 1 (by rfl) ⟨4736069, by rfl⟩ : syracuseStep 6314759 = 9472139) B9472139
theorem B1664009 : Blo 491791 1664009 := bstep (se 2 (by rfl) ⟨624003, by rfl⟩ : syracuseStep 1664009 = 1248007) B1248007
theorem B1666331 : Blo 491791 1666331 := bstep (se 1 (by rfl) ⟨1249748, by rfl⟩ : syracuseStep 1666331 = 2499497) B2499497
theorem B1112399 : Blo 491791 1112399 := bstep (se 1 (by rfl) ⟨834299, by rfl⟩ : syracuseStep 1112399 = 1668599) B1668599
theorem B4209839 : Blo 491791 4209839 := bstep (se 1 (by rfl) ⟨3157379, by rfl⟩ : syracuseStep 4209839 = 6314759) B6314759
theorem B741599 : Blo 491791 741599 := bstep (se 1 (by rfl) ⟨556199, by rfl⟩ : syracuseStep 741599 = 1112399) B1112399
theorem B44654885 : Blo 491791 44654885 := bstep (se 4 (by rfl) ⟨4186395, by rfl⟩ : syracuseStep 44654885 = 8372791) B8372791
theorem B844111 : Blo 491791 844111 := bstep (se 1 (by rfl) ⟨633083, by rfl⟩ : syracuseStep 844111 = 1266167) B1266167
theorem B1109339 : Blo 491791 1109339 := bstep (se 1 (by rfl) ⟨832004, by rfl⟩ : syracuseStep 1109339 = 1664009) B1664009
theorem B1110887 : Blo 491791 1110887 := bstep (se 1 (by rfl) ⟨833165, by rfl⟩ : syracuseStep 1110887 = 1666331) B1666331
theorem B494399 : Blo 491791 494399 := bstep (se 1 (by rfl) ⟨370799, by rfl⟩ : syracuseStep 494399 = 741599) B741599
theorem B4501925 : Blo 491791 4501925 := bstep (se 4 (by rfl) ⟨422055, by rfl⟩ : syracuseStep 4501925 = 844111) B844111
theorem B29769923 : Blo 491791 29769923 := bstep (se 1 (by rfl) ⟨22327442, by rfl⟩ : syracuseStep 29769923 = 44654885) B44654885
theorem B739559 : Blo 491791 739559 := bstep (se 1 (by rfl) ⟨554669, by rfl⟩ : syracuseStep 739559 = 1109339) B1109339
theorem B740591 : Blo 491791 740591 := bstep (se 1 (by rfl) ⟨555443, by rfl⟩ : syracuseStep 740591 = 1110887) B1110887
theorem B2806559 : Blo 491791 2806559 := bstep (se 1 (by rfl) ⟨2104919, by rfl⟩ : syracuseStep 2806559 = 4209839) B4209839
theorem B493039 : Blo 491791 493039 := bstep (se 1 (by rfl) ⟨369779, by rfl⟩ : syracuseStep 493039 = 739559) B739559
theorem B493727 : Blo 491791 493727 := bstep (se 1 (by rfl) ⟨370295, by rfl⟩ : syracuseStep 493727 = 740591) B740591
theorem B1871039 : Blo 491791 1871039 := bstep (se 1 (by rfl) ⟨1403279, by rfl⟩ : syracuseStep 1871039 = 2806559) B2806559
theorem B3001283 : Blo 491791 3001283 := bstep (se 1 (by rfl) ⟨2250962, by rfl⟩ : syracuseStep 3001283 = 4501925) B4501925
theorem B19846615 : Blo 491791 19846615 := bstep (se 1 (by rfl) ⟨14884961, by rfl⟩ : syracuseStep 19846615 = 29769923) B29769923
theorem B2000855 : Blo 491791 2000855 := bstep (se 1 (by rfl) ⟨1500641, by rfl⟩ : syracuseStep 2000855 = 3001283) B3001283
theorem B1247359 : Blo 491791 1247359 := bstep (se 1 (by rfl) ⟨935519, by rfl⟩ : syracuseStep 1247359 = 1871039) B1871039
theorem B26462153 : Blo 491791 26462153 := bstep (se 2 (by rfl) ⟨9923307, by rfl⟩ : syracuseStep 26462153 = 19846615) B19846615
theorem B70565741 : Blo 491791 70565741 := bstep (se 3 (by rfl) ⟨13231076, by rfl⟩ : syracuseStep 70565741 = 26462153) B26462153
theorem B1333903 : Blo 491791 1333903 := bstep (se 1 (by rfl) ⟨1000427, by rfl⟩ : syracuseStep 1333903 = 2000855) B2000855
theorem B1663145 : Blo 491791 1663145 := bstep (se 2 (by rfl) ⟨623679, by rfl⟩ : syracuseStep 1663145 = 1247359) B1247359
theorem B1778537 : Blo 491791 1778537 := bstep (se 2 (by rfl) ⟨666951, by rfl⟩ : syracuseStep 1778537 = 1333903) B1333903
theorem B47043827 : Blo 491791 47043827 := bstep (se 1 (by rfl) ⟨35282870, by rfl⟩ : syracuseStep 47043827 = 70565741) B70565741
theorem B1108763 : Blo 491791 1108763 := bstep (se 1 (by rfl) ⟨831572, by rfl⟩ : syracuseStep 1108763 = 1663145) B1663145
theorem B31362551 : Blo 491791 31362551 := bstep (se 1 (by rfl) ⟨23521913, by rfl⟩ : syracuseStep 31362551 = 47043827) B47043827
theorem B1185691 : Blo 491791 1185691 := bstep (se 1 (by rfl) ⟨889268, by rfl⟩ : syracuseStep 1185691 = 1778537) B1778537
theorem B739175 : Blo 491791 739175 := bstep (se 1 (by rfl) ⟨554381, by rfl⟩ : syracuseStep 739175 = 1108763) B1108763
theorem B492783 : Blo 491791 492783 := bstep (se 1 (by rfl) ⟨369587, by rfl⟩ : syracuseStep 492783 = 739175) B739175
theorem B20908367 : Blo 491791 20908367 := bstep (se 1 (by rfl) ⟨15681275, by rfl⟩ : syracuseStep 20908367 = 31362551) B31362551
theorem B1580921 : Blo 491791 1580921 := bstep (se 2 (by rfl) ⟨592845, by rfl⟩ : syracuseStep 1580921 = 1185691) B1185691
theorem B1053947 : Blo 491791 1053947 := bstep (se 1 (by rfl) ⟨790460, by rfl⟩ : syracuseStep 1053947 = 1580921) B1580921
theorem B13938911 : Blo 491791 13938911 := bstep (se 1 (by rfl) ⟨10454183, by rfl⟩ : syracuseStep 13938911 = 20908367) B20908367
theorem B702631 : Blo 491791 702631 := bstep (se 1 (by rfl) ⟨526973, by rfl⟩ : syracuseStep 702631 = 1053947) B1053947
theorem B9292607 : Blo 491791 9292607 := bstep (se 1 (by rfl) ⟨6969455, by rfl⟩ : syracuseStep 9292607 = 13938911) B13938911
theorem B6195071 : Blo 491791 6195071 := bstep (se 1 (by rfl) ⟨4646303, by rfl⟩ : syracuseStep 6195071 = 9292607) B9292607
theorem B936841 : Blo 491791 936841 := bstep (se 2 (by rfl) ⟨351315, by rfl⟩ : syracuseStep 936841 = 702631) B702631
theorem B4130047 : Blo 491791 4130047 := bstep (se 1 (by rfl) ⟨3097535, by rfl⟩ : syracuseStep 4130047 = 6195071) B6195071
theorem B1249121 : Blo 491791 1249121 := bstep (se 2 (by rfl) ⟨468420, by rfl⟩ : syracuseStep 1249121 = 936841) B936841
theorem B22026917 : Blo 491791 22026917 := bstep (se 4 (by rfl) ⟨2065023, by rfl⟩ : syracuseStep 22026917 = 4130047) B4130047
theorem B832747 : Blo 491791 832747 := bstep (se 1 (by rfl) ⟨624560, by rfl⟩ : syracuseStep 832747 = 1249121) B1249121
theorem B14684611 : Blo 491791 14684611 := bstep (se 1 (by rfl) ⟨11013458, by rfl⟩ : syracuseStep 14684611 = 22026917) B22026917
theorem B1110329 : Blo 491791 1110329 := bstep (se 2 (by rfl) ⟨416373, by rfl⟩ : syracuseStep 1110329 = 832747) B832747
theorem B19579481 : Blo 491791 19579481 := bstep (se 2 (by rfl) ⟨7342305, by rfl⟩ : syracuseStep 19579481 = 14684611) B14684611
theorem B740219 : Blo 491791 740219 := bstep (se 1 (by rfl) ⟨555164, by rfl⟩ : syracuseStep 740219 = 1110329) B1110329
theorem B493479 : Blo 491791 493479 := bstep (se 1 (by rfl) ⟨370109, by rfl⟩ : syracuseStep 493479 = 740219) B740219
theorem B13052987 : Blo 491791 13052987 := bstep (se 1 (by rfl) ⟨9789740, by rfl⟩ : syracuseStep 13052987 = 19579481) B19579481
theorem B8701991 : Blo 491791 8701991 := bstep (se 1 (by rfl) ⟨6526493, by rfl⟩ : syracuseStep 8701991 = 13052987) B13052987
theorem B5801327 : Blo 491791 5801327 := bstep (se 1 (by rfl) ⟨4350995, by rfl⟩ : syracuseStep 5801327 = 8701991) B8701991
theorem B3867551 : Blo 491791 3867551 := bstep (se 1 (by rfl) ⟨2900663, by rfl⟩ : syracuseStep 3867551 = 5801327) B5801327
theorem B41253877 : Blo 491791 41253877 := bstep (se 5 (by rfl) ⟨1933775, by rfl⟩ : syracuseStep 41253877 = 3867551) B3867551
theorem B55005169 : Blo 491791 55005169 := bstep (se 2 (by rfl) ⟨20626938, by rfl⟩ : syracuseStep 55005169 = 41253877) B41253877
theorem B73340225 : Blo 491791 73340225 := bstep (se 2 (by rfl) ⟨27502584, by rfl⟩ : syracuseStep 73340225 = 55005169) B55005169
theorem B48893483 : Blo 491791 48893483 := bstep (se 1 (by rfl) ⟨36670112, by rfl⟩ : syracuseStep 48893483 = 73340225) B73340225
theorem B130382621 : Blo 491791 130382621 := bstep (se 3 (by rfl) ⟨24446741, by rfl⟩ : syracuseStep 130382621 = 48893483) B48893483
theorem B86921747 : Blo 491791 86921747 := bstep (se 1 (by rfl) ⟨65191310, by rfl⟩ : syracuseStep 86921747 = 130382621) B130382621
theorem B57947831 : Blo 491791 57947831 := bstep (se 1 (by rfl) ⟨43460873, by rfl⟩ : syracuseStep 57947831 = 86921747) B86921747
theorem B38631887 : Blo 491791 38631887 := bstep (se 1 (by rfl) ⟨28973915, by rfl⟩ : syracuseStep 38631887 = 57947831) B57947831
theorem B25754591 : Blo 491791 25754591 := bstep (se 1 (by rfl) ⟨19315943, by rfl⟩ : syracuseStep 25754591 = 38631887) B38631887
theorem B17169727 : Blo 491791 17169727 := bstep (se 1 (by rfl) ⟨12877295, by rfl⟩ : syracuseStep 17169727 = 25754591) B25754591
theorem B22892969 : Blo 491791 22892969 := bstep (se 2 (by rfl) ⟨8584863, by rfl⟩ : syracuseStep 22892969 = 17169727) B17169727
theorem B15261979 : Blo 491791 15261979 := bstep (se 1 (by rfl) ⟨11446484, by rfl⟩ : syracuseStep 15261979 = 22892969) B22892969
theorem B20349305 : Blo 491791 20349305 := bstep (se 2 (by rfl) ⟨7630989, by rfl⟩ : syracuseStep 20349305 = 15261979) B15261979
theorem B13566203 : Blo 491791 13566203 := bstep (se 1 (by rfl) ⟨10174652, by rfl⟩ : syracuseStep 13566203 = 20349305) B20349305
theorem B9044135 : Blo 491791 9044135 := bstep (se 1 (by rfl) ⟨6783101, by rfl⟩ : syracuseStep 9044135 = 13566203) B13566203
theorem B6029423 : Blo 491791 6029423 := bstep (se 1 (by rfl) ⟨4522067, by rfl⟩ : syracuseStep 6029423 = 9044135) B9044135
theorem B4019615 : Blo 491791 4019615 := bstep (se 1 (by rfl) ⟨3014711, by rfl⟩ : syracuseStep 4019615 = 6029423) B6029423
theorem B2679743 : Blo 491791 2679743 := bstep (se 1 (by rfl) ⟨2009807, by rfl⟩ : syracuseStep 2679743 = 4019615) B4019615
theorem B1786495 : Blo 491791 1786495 := bstep (se 1 (by rfl) ⟨1339871, by rfl⟩ : syracuseStep 1786495 = 2679743) B2679743
theorem B2381993 : Blo 491791 2381993 := bstep (se 2 (by rfl) ⟨893247, by rfl⟩ : syracuseStep 2381993 = 1786495) B1786495
theorem B1587995 : Blo 491791 1587995 := bstep (se 1 (by rfl) ⟨1190996, by rfl⟩ : syracuseStep 1587995 = 2381993) B2381993
theorem B1058663 : Blo 491791 1058663 := bstep (se 1 (by rfl) ⟨793997, by rfl⟩ : syracuseStep 1058663 = 1587995) B1587995
theorem B705775 : Blo 491791 705775 := bstep (se 1 (by rfl) ⟨529331, by rfl⟩ : syracuseStep 705775 = 1058663) B1058663
theorem B941033 : Blo 491791 941033 := bstep (se 2 (by rfl) ⟨352887, by rfl⟩ : syracuseStep 941033 = 705775) B705775
theorem B627355 : Blo 491791 627355 := bstep (se 1 (by rfl) ⟨470516, by rfl⟩ : syracuseStep 627355 = 941033) B941033
theorem B836473 : Blo 491791 836473 := bstep (se 2 (by rfl) ⟨313677, by rfl⟩ : syracuseStep 836473 = 627355) B627355
theorem B1115297 : Blo 491791 1115297 := bstep (se 2 (by rfl) ⟨418236, by rfl⟩ : syracuseStep 1115297 = 836473) B836473
theorem B743531 : Blo 491791 743531 := bstep (se 1 (by rfl) ⟨557648, by rfl⟩ : syracuseStep 743531 = 1115297) B1115297
theorem B495687 : Blo 491791 495687 := bstep (se 1 (by rfl) ⟨371765, by rfl⟩ : syracuseStep 495687 = 743531) B743531

theorem C0 (j : ℕ) (h1 : 122947 ≤ j) (h2 : j ≤ 123646) : Blo 491791 (4 * j + 3) := by
  interval_cases j
  · exact B491791
  · exact B491795
  · exact B491799
  · exact B491803
  · exact B491807
  · exact B491811
  · exact B491815
  · exact B491819
  · exact B491823
  · exact B491827
  · exact B491831
  · exact B491835
  · exact B491839
  · exact B491843
  · exact B491847
  · exact B491851
  · exact B491855
  · exact B491859
  · exact B491863
  · exact B491867
  · exact B491871
  · exact B491875
  · exact B491879
  · exact B491883
  · exact B491887
  · exact B491891
  · exact B491895
  · exact B491899
  · exact B491903
  · exact B491907
  · exact B491911
  · exact B491915
  · exact B491919
  · exact B491923
  · exact B491927
  · exact B491931
  · exact B491935
  · exact B491939
  · exact B491943
  · exact B491947
  · exact B491951
  · exact B491955
  · exact B491959
  · exact B491963
  · exact B491967
  · exact B491971
  · exact B491975
  · exact B491979
  · exact B491983
  · exact B491987
  · exact B491991
  · exact B491995
  · exact B491999
  · exact B492003
  · exact B492007
  · exact B492011
  · exact B492015
  · exact B492019
  · exact B492023
  · exact B492027
  · exact B492031
  · exact B492035
  · exact B492039
  · exact B492043
  · exact B492047
  · exact B492051
  · exact B492055
  · exact B492059
  · exact B492063
  · exact B492067
  · exact B492071
  · exact B492075
  · exact B492079
  · exact B492083
  · exact B492087
  · exact B492091
  · exact B492095
  · exact B492099
  · exact B492103
  · exact B492107
  · exact B492111
  · exact B492115
  · exact B492119
  · exact B492123
  · exact B492127
  · exact B492131
  · exact B492135
  · exact B492139
  · exact B492143
  · exact B492147
  · exact B492151
  · exact B492155
  · exact B492159
  · exact B492163
  · exact B492167
  · exact B492171
  · exact B492175
  · exact B492179
  · exact B492183
  · exact B492187
  · exact B492191
  · exact B492195
  · exact B492199
  · exact B492203
  · exact B492207
  · exact B492211
  · exact B492215
  · exact B492219
  · exact B492223
  · exact B492227
  · exact B492231
  · exact B492235
  · exact B492239
  · exact B492243
  · exact B492247
  · exact B492251
  · exact B492255
  · exact B492259
  · exact B492263
  · exact B492267
  · exact B492271
  · exact B492275
  · exact B492279
  · exact B492283
  · exact B492287
  · exact B492291
  · exact B492295
  · exact B492299
  · exact B492303
  · exact B492307
  · exact B492311
  · exact B492315
  · exact B492319
  · exact B492323
  · exact B492327
  · exact B492331
  · exact B492335
  · exact B492339
  · exact B492343
  · exact B492347
  · exact B492351
  · exact B492355
  · exact B492359
  · exact B492363
  · exact B492367
  · exact B492371
  · exact B492375
  · exact B492379
  · exact B492383
  · exact B492387
  · exact B492391
  · exact B492395
  · exact B492399
  · exact B492403
  · exact B492407
  · exact B492411
  · exact B492415
  · exact B492419
  · exact B492423
  · exact B492427
  · exact B492431
  · exact B492435
  · exact B492439
  · exact B492443
  · exact B492447
  · exact B492451
  · exact B492455
  · exact B492459
  · exact B492463
  · exact B492467
  · exact B492471
  · exact B492475
  · exact B492479
  · exact B492483
  · exact B492487
  · exact B492491
  · exact B492495
  · exact B492499
  · exact B492503
  · exact B492507
  · exact B492511
  · exact B492515
  · exact B492519
  · exact B492523
  · exact B492527
  · exact B492531
  · exact B492535
  · exact B492539
  · exact B492543
  · exact B492547
  · exact B492551
  · exact B492555
  · exact B492559
  · exact B492563
  · exact B492567
  · exact B492571
  · exact B492575
  · exact B492579
  · exact B492583
  · exact B492587
  · exact B492591
  · exact B492595
  · exact B492599
  · exact B492603
  · exact B492607
  · exact B492611
  · exact B492615
  · exact B492619
  · exact B492623
  · exact B492627
  · exact B492631
  · exact B492635
  · exact B492639
  · exact B492643
  · exact B492647
  · exact B492651
  · exact B492655
  · exact B492659
  · exact B492663
  · exact B492667
  · exact B492671
  · exact B492675
  · exact B492679
  · exact B492683
  · exact B492687
  · exact B492691
  · exact B492695
  · exact B492699
  · exact B492703
  · exact B492707
  · exact B492711
  · exact B492715
  · exact B492719
  · exact B492723
  · exact B492727
  · exact B492731
  · exact B492735
  · exact B492739
  · exact B492743
  · exact B492747
  · exact B492751
  · exact B492755
  · exact B492759
  · exact B492763
  · exact B492767
  · exact B492771
  · exact B492775
  · exact B492779
  · exact B492783
  · exact B492787
  · exact B492791
  · exact B492795
  · exact B492799
  · exact B492803
  · exact B492807
  · exact B492811
  · exact B492815
  · exact B492819
  · exact B492823
  · exact B492827
  · exact B492831
  · exact B492835
  · exact B492839
  · exact B492843
  · exact B492847
  · exact B492851
  · exact B492855
  · exact B492859
  · exact B492863
  · exact B492867
  · exact B492871
  · exact B492875
  · exact B492879
  · exact B492883
  · exact B492887
  · exact B492891
  · exact B492895
  · exact B492899
  · exact B492903
  · exact B492907
  · exact B492911
  · exact B492915
  · exact B492919
  · exact B492923
  · exact B492927
  · exact B492931
  · exact B492935
  · exact B492939
  · exact B492943
  · exact B492947
  · exact B492951
  · exact B492955
  · exact B492959
  · exact B492963
  · exact B492967
  · exact B492971
  · exact B492975
  · exact B492979
  · exact B492983
  · exact B492987
  · exact B492991
  · exact B492995
  · exact B492999
  · exact B493003
  · exact B493007
  · exact B493011
  · exact B493015
  · exact B493019
  · exact B493023
  · exact B493027
  · exact B493031
  · exact B493035
  · exact B493039
  · exact B493043
  · exact B493047
  · exact B493051
  · exact B493055
  · exact B493059
  · exact B493063
  · exact B493067
  · exact B493071
  · exact B493075
  · exact B493079
  · exact B493083
  · exact B493087
  · exact B493091
  · exact B493095
  · exact B493099
  · exact B493103
  · exact B493107
  · exact B493111
  · exact B493115
  · exact B493119
  · exact B493123
  · exact B493127
  · exact B493131
  · exact B493135
  · exact B493139
  · exact B493143
  · exact B493147
  · exact B493151
  · exact B493155
  · exact B493159
  · exact B493163
  · exact B493167
  · exact B493171
  · exact B493175
  · exact B493179
  · exact B493183
  · exact B493187
  · exact B493191
  · exact B493195
  · exact B493199
  · exact B493203
  · exact B493207
  · exact B493211
  · exact B493215
  · exact B493219
  · exact B493223
  · exact B493227
  · exact B493231
  · exact B493235
  · exact B493239
  · exact B493243
  · exact B493247
  · exact B493251
  · exact B493255
  · exact B493259
  · exact B493263
  · exact B493267
  · exact B493271
  · exact B493275
  · exact B493279
  · exact B493283
  · exact B493287
  · exact B493291
  · exact B493295
  · exact B493299
  · exact B493303
  · exact B493307
  · exact B493311
  · exact B493315
  · exact B493319
  · exact B493323
  · exact B493327
  · exact B493331
  · exact B493335
  · exact B493339
  · exact B493343
  · exact B493347
  · exact B493351
  · exact B493355
  · exact B493359
  · exact B493363
  · exact B493367
  · exact B493371
  · exact B493375
  · exact B493379
  · exact B493383
  · exact B493387
  · exact B493391
  · exact B493395
  · exact B493399
  · exact B493403
  · exact B493407
  · exact B493411
  · exact B493415
  · exact B493419
  · exact B493423
  · exact B493427
  · exact B493431
  · exact B493435
  · exact B493439
  · exact B493443
  · exact B493447
  · exact B493451
  · exact B493455
  · exact B493459
  · exact B493463
  · exact B493467
  · exact B493471
  · exact B493475
  · exact B493479
  · exact B493483
  · exact B493487
  · exact B493491
  · exact B493495
  · exact B493499
  · exact B493503
  · exact B493507
  · exact B493511
  · exact B493515
  · exact B493519
  · exact B493523
  · exact B493527
  · exact B493531
  · exact B493535
  · exact B493539
  · exact B493543
  · exact B493547
  · exact B493551
  · exact B493555
  · exact B493559
  · exact B493563
  · exact B493567
  · exact B493571
  · exact B493575
  · exact B493579
  · exact B493583
  · exact B493587
  · exact B493591
  · exact B493595
  · exact B493599
  · exact B493603
  · exact B493607
  · exact B493611
  · exact B493615
  · exact B493619
  · exact B493623
  · exact B493627
  · exact B493631
  · exact B493635
  · exact B493639
  · exact B493643
  · exact B493647
  · exact B493651
  · exact B493655
  · exact B493659
  · exact B493663
  · exact B493667
  · exact B493671
  · exact B493675
  · exact B493679
  · exact B493683
  · exact B493687
  · exact B493691
  · exact B493695
  · exact B493699
  · exact B493703
  · exact B493707
  · exact B493711
  · exact B493715
  · exact B493719
  · exact B493723
  · exact B493727
  · exact B493731
  · exact B493735
  · exact B493739
  · exact B493743
  · exact B493747
  · exact B493751
  · exact B493755
  · exact B493759
  · exact B493763
  · exact B493767
  · exact B493771
  · exact B493775
  · exact B493779
  · exact B493783
  · exact B493787
  · exact B493791
  · exact B493795
  · exact B493799
  · exact B493803
  · exact B493807
  · exact B493811
  · exact B493815
  · exact B493819
  · exact B493823
  · exact B493827
  · exact B493831
  · exact B493835
  · exact B493839
  · exact B493843
  · exact B493847
  · exact B493851
  · exact B493855
  · exact B493859
  · exact B493863
  · exact B493867
  · exact B493871
  · exact B493875
  · exact B493879
  · exact B493883
  · exact B493887
  · exact B493891
  · exact B493895
  · exact B493899
  · exact B493903
  · exact B493907
  · exact B493911
  · exact B493915
  · exact B493919
  · exact B493923
  · exact B493927
  · exact B493931
  · exact B493935
  · exact B493939
  · exact B493943
  · exact B493947
  · exact B493951
  · exact B493955
  · exact B493959
  · exact B493963
  · exact B493967
  · exact B493971
  · exact B493975
  · exact B493979
  · exact B493983
  · exact B493987
  · exact B493991
  · exact B493995
  · exact B493999
  · exact B494003
  · exact B494007
  · exact B494011
  · exact B494015
  · exact B494019
  · exact B494023
  · exact B494027
  · exact B494031
  · exact B494035
  · exact B494039
  · exact B494043
  · exact B494047
  · exact B494051
  · exact B494055
  · exact B494059
  · exact B494063
  · exact B494067
  · exact B494071
  · exact B494075
  · exact B494079
  · exact B494083
  · exact B494087
  · exact B494091
  · exact B494095
  · exact B494099
  · exact B494103
  · exact B494107
  · exact B494111
  · exact B494115
  · exact B494119
  · exact B494123
  · exact B494127
  · exact B494131
  · exact B494135
  · exact B494139
  · exact B494143
  · exact B494147
  · exact B494151
  · exact B494155
  · exact B494159
  · exact B494163
  · exact B494167
  · exact B494171
  · exact B494175
  · exact B494179
  · exact B494183
  · exact B494187
  · exact B494191
  · exact B494195
  · exact B494199
  · exact B494203
  · exact B494207
  · exact B494211
  · exact B494215
  · exact B494219
  · exact B494223
  · exact B494227
  · exact B494231
  · exact B494235
  · exact B494239
  · exact B494243
  · exact B494247
  · exact B494251
  · exact B494255
  · exact B494259
  · exact B494263
  · exact B494267
  · exact B494271
  · exact B494275
  · exact B494279
  · exact B494283
  · exact B494287
  · exact B494291
  · exact B494295
  · exact B494299
  · exact B494303
  · exact B494307
  · exact B494311
  · exact B494315
  · exact B494319
  · exact B494323
  · exact B494327
  · exact B494331
  · exact B494335
  · exact B494339
  · exact B494343
  · exact B494347
  · exact B494351
  · exact B494355
  · exact B494359
  · exact B494363
  · exact B494367
  · exact B494371
  · exact B494375
  · exact B494379
  · exact B494383
  · exact B494387
  · exact B494391
  · exact B494395
  · exact B494399
  · exact B494403
  · exact B494407
  · exact B494411
  · exact B494415
  · exact B494419
  · exact B494423
  · exact B494427
  · exact B494431
  · exact B494435
  · exact B494439
  · exact B494443
  · exact B494447
  · exact B494451
  · exact B494455
  · exact B494459
  · exact B494463
  · exact B494467
  · exact B494471
  · exact B494475
  · exact B494479
  · exact B494483
  · exact B494487
  · exact B494491
  · exact B494495
  · exact B494499
  · exact B494503
  · exact B494507
  · exact B494511
  · exact B494515
  · exact B494519
  · exact B494523
  · exact B494527
  · exact B494531
  · exact B494535
  · exact B494539
  · exact B494543
  · exact B494547
  · exact B494551
  · exact B494555
  · exact B494559
  · exact B494563
  · exact B494567
  · exact B494571
  · exact B494575
  · exact B494579
  · exact B494583
  · exact B494587

theorem C1 (j : ℕ) (h1 : 123647 ≤ j) (h2 : j ≤ 123947) : Blo 491791 (4 * j + 3) := by
  interval_cases j
  · exact B494591
  · exact B494595
  · exact B494599
  · exact B494603
  · exact B494607
  · exact B494611
  · exact B494615
  · exact B494619
  · exact B494623
  · exact B494627
  · exact B494631
  · exact B494635
  · exact B494639
  · exact B494643
  · exact B494647
  · exact B494651
  · exact B494655
  · exact B494659
  · exact B494663
  · exact B494667
  · exact B494671
  · exact B494675
  · exact B494679
  · exact B494683
  · exact B494687
  · exact B494691
  · exact B494695
  · exact B494699
  · exact B494703
  · exact B494707
  · exact B494711
  · exact B494715
  · exact B494719
  · exact B494723
  · exact B494727
  · exact B494731
  · exact B494735
  · exact B494739
  · exact B494743
  · exact B494747
  · exact B494751
  · exact B494755
  · exact B494759
  · exact B494763
  · exact B494767
  · exact B494771
  · exact B494775
  · exact B494779
  · exact B494783
  · exact B494787
  · exact B494791
  · exact B494795
  · exact B494799
  · exact B494803
  · exact B494807
  · exact B494811
  · exact B494815
  · exact B494819
  · exact B494823
  · exact B494827
  · exact B494831
  · exact B494835
  · exact B494839
  · exact B494843
  · exact B494847
  · exact B494851
  · exact B494855
  · exact B494859
  · exact B494863
  · exact B494867
  · exact B494871
  · exact B494875
  · exact B494879
  · exact B494883
  · exact B494887
  · exact B494891
  · exact B494895
  · exact B494899
  · exact B494903
  · exact B494907
  · exact B494911
  · exact B494915
  · exact B494919
  · exact B494923
  · exact B494927
  · exact B494931
  · exact B494935
  · exact B494939
  · exact B494943
  · exact B494947
  · exact B494951
  · exact B494955
  · exact B494959
  · exact B494963
  · exact B494967
  · exact B494971
  · exact B494975
  · exact B494979
  · exact B494983
  · exact B494987
  · exact B494991
  · exact B494995
  · exact B494999
  · exact B495003
  · exact B495007
  · exact B495011
  · exact B495015
  · exact B495019
  · exact B495023
  · exact B495027
  · exact B495031
  · exact B495035
  · exact B495039
  · exact B495043
  · exact B495047
  · exact B495051
  · exact B495055
  · exact B495059
  · exact B495063
  · exact B495067
  · exact B495071
  · exact B495075
  · exact B495079
  · exact B495083
  · exact B495087
  · exact B495091
  · exact B495095
  · exact B495099
  · exact B495103
  · exact B495107
  · exact B495111
  · exact B495115
  · exact B495119
  · exact B495123
  · exact B495127
  · exact B495131
  · exact B495135
  · exact B495139
  · exact B495143
  · exact B495147
  · exact B495151
  · exact B495155
  · exact B495159
  · exact B495163
  · exact B495167
  · exact B495171
  · exact B495175
  · exact B495179
  · exact B495183
  · exact B495187
  · exact B495191
  · exact B495195
  · exact B495199
  · exact B495203
  · exact B495207
  · exact B495211
  · exact B495215
  · exact B495219
  · exact B495223
  · exact B495227
  · exact B495231
  · exact B495235
  · exact B495239
  · exact B495243
  · exact B495247
  · exact B495251
  · exact B495255
  · exact B495259
  · exact B495263
  · exact B495267
  · exact B495271
  · exact B495275
  · exact B495279
  · exact B495283
  · exact B495287
  · exact B495291
  · exact B495295
  · exact B495299
  · exact B495303
  · exact B495307
  · exact B495311
  · exact B495315
  · exact B495319
  · exact B495323
  · exact B495327
  · exact B495331
  · exact B495335
  · exact B495339
  · exact B495343
  · exact B495347
  · exact B495351
  · exact B495355
  · exact B495359
  · exact B495363
  · exact B495367
  · exact B495371
  · exact B495375
  · exact B495379
  · exact B495383
  · exact B495387
  · exact B495391
  · exact B495395
  · exact B495399
  · exact B495403
  · exact B495407
  · exact B495411
  · exact B495415
  · exact B495419
  · exact B495423
  · exact B495427
  · exact B495431
  · exact B495435
  · exact B495439
  · exact B495443
  · exact B495447
  · exact B495451
  · exact B495455
  · exact B495459
  · exact B495463
  · exact B495467
  · exact B495471
  · exact B495475
  · exact B495479
  · exact B495483
  · exact B495487
  · exact B495491
  · exact B495495
  · exact B495499
  · exact B495503
  · exact B495507
  · exact B495511
  · exact B495515
  · exact B495519
  · exact B495523
  · exact B495527
  · exact B495531
  · exact B495535
  · exact B495539
  · exact B495543
  · exact B495547
  · exact B495551
  · exact B495555
  · exact B495559
  · exact B495563
  · exact B495567
  · exact B495571
  · exact B495575
  · exact B495579
  · exact B495583
  · exact B495587
  · exact B495591
  · exact B495595
  · exact B495599
  · exact B495603
  · exact B495607
  · exact B495611
  · exact B495615
  · exact B495619
  · exact B495623
  · exact B495627
  · exact B495631
  · exact B495635
  · exact B495639
  · exact B495643
  · exact B495647
  · exact B495651
  · exact B495655
  · exact B495659
  · exact B495663
  · exact B495667
  · exact B495671
  · exact B495675
  · exact B495679
  · exact B495683
  · exact B495687
  · exact B495691
  · exact B495695
  · exact B495699
  · exact B495703
  · exact B495707
  · exact B495711
  · exact B495715
  · exact B495719
  · exact B495723
  · exact B495727
  · exact B495731
  · exact B495735
  · exact B495739
  · exact B495743
  · exact B495747
  · exact B495751
  · exact B495755
  · exact B495759
  · exact B495763
  · exact B495767
  · exact B495771
  · exact B495775
  · exact B495779
  · exact B495783
  · exact B495787
  · exact B495791

theorem solution (m : ℕ) (hlo : 491791 ≤ m) (hhi : m ≤ 495791) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 122947 ≤ j := by omega
    have hj2 : j ≤ 123947 := by omega
    have hb : Blo 491791 (4 * j + 3) := by
      rcases Nat.lt_or_ge j 123647 with hc0 | hc0
      · exact C0 j (by omega) (by omega)
      exact C1 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
