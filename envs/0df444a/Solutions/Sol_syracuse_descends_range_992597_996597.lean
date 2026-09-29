-- Prove2me | solution 1 for syracuse_descends_range_992597_996597
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-09T20:22:11.279926+00:00
-- url     : https://prove2.me/submissions/e4c67ba8-a94d-4962-84ba-5b496d48f979

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


theorem B3768869 : Blo 992597 3768869 := bbase (se 4 (by rfl) ⟨353331, by rfl⟩ : syracuseStep 3768869 = 706663) (by norm_num)
theorem B1344109 : Blo 992597 1344109 := bbase (se 3 (by rfl) ⟨252020, by rfl⟩ : syracuseStep 1344109 = 504041) (by norm_num)
theorem B5374613 : Blo 992597 5374613 := bbase (se 6 (by rfl) ⟨125967, by rfl⟩ : syracuseStep 5374613 = 251935) (by norm_num)
theorem B1704613 : Blo 992597 1704613 := bbase (se 4 (by rfl) ⟨159807, by rfl⟩ : syracuseStep 1704613 = 319615) (by norm_num)
theorem B2425589 : Blo 992597 2425589 := bbase (se 5 (by rfl) ⟨113699, by rfl⟩ : syracuseStep 2425589 = 227399) (by norm_num)
theorem B2687957 : Blo 992597 2687957 := bbase (se 7 (by rfl) ⟨31499, by rfl⟩ : syracuseStep 2687957 = 62999) (by norm_num)
theorem B1344557 : Blo 992597 1344557 := bbase (se 3 (by rfl) ⟨252104, by rfl⟩ : syracuseStep 1344557 = 504209) (by norm_num)
theorem B8487989 : Blo 992597 8487989 := bbase (se 5 (by rfl) ⟨397874, by rfl⟩ : syracuseStep 8487989 = 795749) (by norm_num)
theorem B2688085 : Blo 992597 2688085 := bbase (se 8 (by rfl) ⟨15750, by rfl⟩ : syracuseStep 2688085 = 31501) (by norm_num)
theorem B41976917 : Blo 992597 41976917 := bbase (se 8 (by rfl) ⟨245958, by rfl⟩ : syracuseStep 41976917 = 491917) (by norm_num)
theorem B4785317 : Blo 992597 4785317 := bbase (se 4 (by rfl) ⟨448623, by rfl⟩ : syracuseStep 4785317 = 897247) (by norm_num)
theorem B10225045 : Blo 992597 10225045 := bbase (se 6 (by rfl) ⟨239649, by rfl⟩ : syracuseStep 10225045 = 479299) (by norm_num)
theorem B3180293 : Blo 992597 3180293 := bbase (se 4 (by rfl) ⟨298152, by rfl⟩ : syracuseStep 3180293 = 596305) (by norm_num)
theorem B2393869 : Blo 992597 2393869 := bbase (se 3 (by rfl) ⟨448850, by rfl⟩ : syracuseStep 2393869 = 897701) (by norm_num)
theorem B7669525 : Blo 992597 7669525 := bbase (se 6 (by rfl) ⟨179754, by rfl⟩ : syracuseStep 7669525 = 359509) (by norm_num)
theorem B7767893 : Blo 992597 7767893 := bbase (se 9 (by rfl) ⟨22757, by rfl⟩ : syracuseStep 7767893 = 45515) (by norm_num)
theorem B2590597 : Blo 992597 2590597 := bbase (se 4 (by rfl) ⟨242868, by rfl⟩ : syracuseStep 2590597 = 485737) (by norm_num)
theorem B4032517 : Blo 992597 4032517 := bbase (se 4 (by rfl) ⟨378048, by rfl⟩ : syracuseStep 4032517 = 756097) (by norm_num)
theorem B8161397 : Blo 992597 8161397 := bbase (se 5 (by rfl) ⟨382565, by rfl⟩ : syracuseStep 8161397 = 765131) (by norm_num)
theorem B1050769 : Blo 992597 1050769 := bbase (se 2 (by rfl) ⟨394038, by rfl⟩ : syracuseStep 1050769 = 788077) (by norm_num)
theorem B8063189 : Blo 992597 8063189 := bbase (se 7 (by rfl) ⟨94490, by rfl⟩ : syracuseStep 8063189 = 188981) (by norm_num)
theorem B2394485 : Blo 992597 2394485 := bbase (se 5 (by rfl) ⟨112241, by rfl⟩ : syracuseStep 2394485 = 224483) (by norm_num)
theorem B1116697 : Blo 992597 1116697 := bbase (se 2 (by rfl) ⟨418761, by rfl⟩ : syracuseStep 1116697 = 837523) (by norm_num)
theorem B1116733 : Blo 992597 1116733 := bbase (se 3 (by rfl) ⟨209387, by rfl⟩ : syracuseStep 1116733 = 418775) (by norm_num)
theorem B1116769 : Blo 992597 1116769 := bbase (se 2 (by rfl) ⟨418788, by rfl⟩ : syracuseStep 1116769 = 837577) (by norm_num)
theorem B3770981 : Blo 992597 3770981 := bbase (se 4 (by rfl) ⟨353529, by rfl⟩ : syracuseStep 3770981 = 707059) (by norm_num)
theorem B7539317 : Blo 992597 7539317 := bbase (se 5 (by rfl) ⟨353405, by rfl⟩ : syracuseStep 7539317 = 706811) (by norm_num)
theorem B1116805 : Blo 992597 1116805 := bbase (se 4 (by rfl) ⟨104700, by rfl⟩ : syracuseStep 1116805 = 209401) (by norm_num)
theorem B3181189 : Blo 992597 3181189 := bbase (se 4 (by rfl) ⟨298236, by rfl⟩ : syracuseStep 3181189 = 596473) (by norm_num)
theorem B1116841 : Blo 992597 1116841 := bbase (se 2 (by rfl) ⟨418815, by rfl⟩ : syracuseStep 1116841 = 837631) (by norm_num)
theorem B1116877 : Blo 992597 1116877 := bbase (se 3 (by rfl) ⟨209414, by rfl⟩ : syracuseStep 1116877 = 418829) (by norm_num)
theorem B1116913 : Blo 992597 1116913 := bbase (se 2 (by rfl) ⟨418842, by rfl⟩ : syracuseStep 1116913 = 837685) (by norm_num)
theorem B1116949 : Blo 992597 1116949 := bbase (se 6 (by rfl) ⟨26178, by rfl⟩ : syracuseStep 1116949 = 52357) (by norm_num)
theorem B1116985 : Blo 992597 1116985 := bbase (se 2 (by rfl) ⟨418869, by rfl⟩ : syracuseStep 1116985 = 837739) (by norm_num)
theorem B1346389 : Blo 992597 1346389 := bbase (se 9 (by rfl) ⟨3944, by rfl⟩ : syracuseStep 1346389 = 7889) (by norm_num)
theorem B1117021 : Blo 992597 1117021 := bbase (se 3 (by rfl) ⟨209441, by rfl⟩ : syracuseStep 1117021 = 418883) (by norm_num)
theorem B1117057 : Blo 992597 1117057 := bbase (se 2 (by rfl) ⟨418896, by rfl⟩ : syracuseStep 1117057 = 837793) (by norm_num)
theorem B3771269 : Blo 992597 3771269 := bbase (se 4 (by rfl) ⟨353556, by rfl⟩ : syracuseStep 3771269 = 707113) (by norm_num)
theorem B1117093 : Blo 992597 1117093 := bbase (se 4 (by rfl) ⟨104727, by rfl⟩ : syracuseStep 1117093 = 209455) (by norm_num)
theorem B1117129 : Blo 992597 1117129 := bbase (se 2 (by rfl) ⟨418923, by rfl⟩ : syracuseStep 1117129 = 837847) (by norm_num)
theorem B1117165 : Blo 992597 1117165 := bbase (se 3 (by rfl) ⟨209468, by rfl⟩ : syracuseStep 1117165 = 418937) (by norm_num)
theorem B1117201 : Blo 992597 1117201 := bbase (se 2 (by rfl) ⟨418950, by rfl⟩ : syracuseStep 1117201 = 837901) (by norm_num)
theorem B1117237 : Blo 992597 1117237 := bbase (se 5 (by rfl) ⟨52370, by rfl⟩ : syracuseStep 1117237 = 104741) (by norm_num)
theorem B1117273 : Blo 992597 1117273 := bbase (se 2 (by rfl) ⟨418977, by rfl⟩ : syracuseStep 1117273 = 837955) (by norm_num)
theorem B1117309 : Blo 992597 1117309 := bbase (se 3 (by rfl) ⟨209495, by rfl⟩ : syracuseStep 1117309 = 418991) (by norm_num)
theorem B1117345 : Blo 992597 1117345 := bbase (se 2 (by rfl) ⟨419004, by rfl⟩ : syracuseStep 1117345 = 838009) (by norm_num)
theorem B1117381 : Blo 992597 1117381 := bbase (se 4 (by rfl) ⟨104754, by rfl⟩ : syracuseStep 1117381 = 209509) (by norm_num)
theorem B1117417 : Blo 992597 1117417 := bbase (se 2 (by rfl) ⟨419031, by rfl⟩ : syracuseStep 1117417 = 838063) (by norm_num)
theorem B1117453 : Blo 992597 1117453 := bbase (se 3 (by rfl) ⟨209522, by rfl⟩ : syracuseStep 1117453 = 419045) (by norm_num)
theorem B5672213 : Blo 992597 5672213 := bbase (se 6 (by rfl) ⟨132942, by rfl⟩ : syracuseStep 5672213 = 265885) (by norm_num)
theorem B1117489 : Blo 992597 1117489 := bbase (se 2 (by rfl) ⟨419058, by rfl⟩ : syracuseStep 1117489 = 838117) (by norm_num)
theorem B1117525 : Blo 992597 1117525 := bbase (se 11 (by rfl) ⟨818, by rfl⟩ : syracuseStep 1117525 = 1637) (by norm_num)
theorem B1117561 : Blo 992597 1117561 := bbase (se 2 (by rfl) ⟨419085, by rfl⟩ : syracuseStep 1117561 = 838171) (by norm_num)
theorem B1117597 : Blo 992597 1117597 := bbase (se 3 (by rfl) ⟨209549, by rfl⟩ : syracuseStep 1117597 = 419099) (by norm_num)
theorem B1117633 : Blo 992597 1117633 := bbase (se 2 (by rfl) ⟨419112, by rfl⟩ : syracuseStep 1117633 = 838225) (by norm_num)
theorem B1117669 : Blo 992597 1117669 := bbase (se 4 (by rfl) ⟨104781, by rfl⟩ : syracuseStep 1117669 = 209563) (by norm_num)
theorem B1117705 : Blo 992597 1117705 := bbase (se 2 (by rfl) ⟨419139, by rfl⟩ : syracuseStep 1117705 = 838279) (by norm_num)
theorem B1117741 : Blo 992597 1117741 := bbase (se 3 (by rfl) ⟨209576, by rfl⟩ : syracuseStep 1117741 = 419153) (by norm_num)
theorem B1117777 : Blo 992597 1117777 := bbase (se 2 (by rfl) ⟨419166, by rfl⟩ : syracuseStep 1117777 = 838333) (by norm_num)
theorem B6131285 : Blo 992597 6131285 := bbase (se 8 (by rfl) ⟨35925, by rfl⟩ : syracuseStep 6131285 = 71851) (by norm_num)
theorem B1117813 : Blo 992597 1117813 := bbase (se 5 (by rfl) ⟨52397, by rfl⟩ : syracuseStep 1117813 = 104795) (by norm_num)
theorem B1117849 : Blo 992597 1117849 := bbase (se 2 (by rfl) ⟨419193, by rfl⟩ : syracuseStep 1117849 = 838387) (by norm_num)
theorem B1117885 : Blo 992597 1117885 := bbase (se 3 (by rfl) ⟨209603, by rfl⟩ : syracuseStep 1117885 = 419207) (by norm_num)
theorem B1117921 : Blo 992597 1117921 := bbase (se 2 (by rfl) ⟨419220, by rfl⟩ : syracuseStep 1117921 = 838441) (by norm_num)
theorem B2723557 : Blo 992597 2723557 := bbase (se 4 (by rfl) ⟨255333, by rfl⟩ : syracuseStep 2723557 = 510667) (by norm_num)
theorem B1117957 : Blo 992597 1117957 := bbase (se 4 (by rfl) ⟨104808, by rfl⟩ : syracuseStep 1117957 = 209617) (by norm_num)
theorem B1117993 : Blo 992597 1117993 := bbase (se 2 (by rfl) ⟨419247, by rfl⟩ : syracuseStep 1117993 = 838495) (by norm_num)
theorem B1511221 : Blo 992597 1511221 := bbase (se 5 (by rfl) ⟨70838, by rfl⟩ : syracuseStep 1511221 = 141677) (by norm_num)
theorem B1118029 : Blo 992597 1118029 := bbase (se 3 (by rfl) ⟨209630, by rfl⟩ : syracuseStep 1118029 = 419261) (by norm_num)
theorem B1675093 : Blo 992597 1675093 := bbase (se 9 (by rfl) ⟨4907, by rfl⟩ : syracuseStep 1675093 = 9815) (by norm_num)
theorem B1118065 : Blo 992597 1118065 := bbase (se 2 (by rfl) ⟨419274, by rfl⟩ : syracuseStep 1118065 = 838549) (by norm_num)
theorem B1118101 : Blo 992597 1118101 := bbase (se 6 (by rfl) ⟨26205, by rfl⟩ : syracuseStep 1118101 = 52411) (by norm_num)
theorem B1675181 : Blo 992597 1675181 := bbase (se 3 (by rfl) ⟨314096, by rfl⟩ : syracuseStep 1675181 = 628193) (by norm_num)
theorem B1118137 : Blo 992597 1118137 := bbase (se 2 (by rfl) ⟨419301, by rfl⟩ : syracuseStep 1118137 = 838603) (by norm_num)
theorem B11341781 : Blo 992597 11341781 := bbase (se 7 (by rfl) ⟨132911, by rfl⟩ : syracuseStep 11341781 = 265823) (by norm_num)
theorem B1118173 : Blo 992597 1118173 := bbase (se 3 (by rfl) ⟨209657, by rfl⟩ : syracuseStep 1118173 = 419315) (by norm_num)
theorem B1118209 : Blo 992597 1118209 := bbase (se 2 (by rfl) ⟨419328, by rfl⟩ : syracuseStep 1118209 = 838657) (by norm_num)
theorem B3772453 : Blo 992597 3772453 := bbase (se 4 (by rfl) ⟨353667, by rfl⟩ : syracuseStep 3772453 = 707335) (by norm_num)
theorem B1118245 : Blo 992597 1118245 := bbase (se 4 (by rfl) ⟨104835, by rfl⟩ : syracuseStep 1118245 = 209671) (by norm_num)
theorem B1675309 : Blo 992597 1675309 := bbase (se 3 (by rfl) ⟨314120, by rfl⟩ : syracuseStep 1675309 = 628241) (by norm_num)
theorem B1118281 : Blo 992597 1118281 := bbase (se 2 (by rfl) ⟨419355, by rfl⟩ : syracuseStep 1118281 = 838711) (by norm_num)
theorem B1118317 : Blo 992597 1118317 := bbase (se 3 (by rfl) ⟨209684, by rfl⟩ : syracuseStep 1118317 = 419369) (by norm_num)
theorem B1675397 : Blo 992597 1675397 := bbase (se 4 (by rfl) ⟨157068, by rfl⟩ : syracuseStep 1675397 = 314137) (by norm_num)
theorem B1118353 : Blo 992597 1118353 := bbase (se 2 (by rfl) ⟨419382, by rfl⟩ : syracuseStep 1118353 = 838765) (by norm_num)
theorem B1118389 : Blo 992597 1118389 := bbase (se 5 (by rfl) ⟨52424, by rfl⟩ : syracuseStep 1118389 = 104849) (by norm_num)
theorem B1118425 : Blo 992597 1118425 := bbase (se 2 (by rfl) ⟨419409, by rfl⟩ : syracuseStep 1118425 = 838819) (by norm_num)
theorem B1118461 : Blo 992597 1118461 := bbase (se 3 (by rfl) ⟨209711, by rfl⟩ : syracuseStep 1118461 = 419423) (by norm_num)
theorem B1675525 : Blo 992597 1675525 := bbase (se 4 (by rfl) ⟨157080, by rfl⟩ : syracuseStep 1675525 = 314161) (by norm_num)
theorem B1413389 : Blo 992597 1413389 := bbase (se 3 (by rfl) ⟨265010, by rfl⟩ : syracuseStep 1413389 = 530021) (by norm_num)
theorem B2265365 : Blo 992597 2265365 := bbase (se 6 (by rfl) ⟨53094, by rfl⟩ : syracuseStep 2265365 = 106189) (by norm_num)
theorem B2298133 : Blo 992597 2298133 := bbase (se 6 (by rfl) ⟨53862, by rfl⟩ : syracuseStep 2298133 = 107725) (by norm_num)
theorem B1118497 : Blo 992597 1118497 := bbase (se 2 (by rfl) ⟨419436, by rfl⟩ : syracuseStep 1118497 = 838873) (by norm_num)
theorem B1118533 : Blo 992597 1118533 := bbase (se 4 (by rfl) ⟨104862, by rfl⟩ : syracuseStep 1118533 = 209725) (by norm_num)
theorem B3772757 : Blo 992597 3772757 := bbase (se 10 (by rfl) ⟨5526, by rfl⟩ : syracuseStep 3772757 = 11053) (by norm_num)
theorem B1675613 : Blo 992597 1675613 := bbase (se 3 (by rfl) ⟨314177, by rfl⟩ : syracuseStep 1675613 = 628355) (by norm_num)
theorem B1118569 : Blo 992597 1118569 := bbase (se 2 (by rfl) ⟨419463, by rfl⟩ : syracuseStep 1118569 = 838927) (by norm_num)
theorem B1118605 : Blo 992597 1118605 := bbase (se 3 (by rfl) ⟨209738, by rfl⟩ : syracuseStep 1118605 = 419477) (by norm_num)
theorem B1118641 : Blo 992597 1118641 := bbase (se 2 (by rfl) ⟨419490, by rfl⟩ : syracuseStep 1118641 = 838981) (by norm_num)
theorem B1118677 : Blo 992597 1118677 := bbase (se 7 (by rfl) ⟨13109, by rfl⟩ : syracuseStep 1118677 = 26219) (by norm_num)
theorem B1675741 : Blo 992597 1675741 := bbase (se 3 (by rfl) ⟨314201, by rfl⟩ : syracuseStep 1675741 = 628403) (by norm_num)
theorem B5247461 : Blo 992597 5247461 := bbase (se 4 (by rfl) ⟨491949, by rfl⟩ : syracuseStep 5247461 = 983899) (by norm_num)
theorem B1118713 : Blo 992597 1118713 := bbase (se 2 (by rfl) ⟨419517, by rfl⟩ : syracuseStep 1118713 = 839035) (by norm_num)
theorem B1118749 : Blo 992597 1118749 := bbase (se 3 (by rfl) ⟨209765, by rfl⟩ : syracuseStep 1118749 = 419531) (by norm_num)
theorem B1675829 : Blo 992597 1675829 := bbase (se 5 (by rfl) ⟨78554, by rfl⟩ : syracuseStep 1675829 = 157109) (by norm_num)
theorem B1118785 : Blo 992597 1118785 := bbase (se 2 (by rfl) ⟨419544, by rfl⟩ : syracuseStep 1118785 = 839089) (by norm_num)
theorem B1118821 : Blo 992597 1118821 := bbase (se 4 (by rfl) ⟨104889, by rfl⟩ : syracuseStep 1118821 = 209779) (by norm_num)
theorem B1118857 : Blo 992597 1118857 := bbase (se 2 (by rfl) ⟨419571, by rfl⟩ : syracuseStep 1118857 = 839143) (by norm_num)
theorem B1118893 : Blo 992597 1118893 := bbase (se 3 (by rfl) ⟨209792, by rfl⟩ : syracuseStep 1118893 = 419585) (by norm_num)
theorem B1675957 : Blo 992597 1675957 := bbase (se 5 (by rfl) ⟨78560, by rfl⟩ : syracuseStep 1675957 = 157121) (by norm_num)
theorem B1118929 : Blo 992597 1118929 := bbase (se 2 (by rfl) ⟨419598, by rfl⟩ : syracuseStep 1118929 = 839197) (by norm_num)
theorem B1118965 : Blo 992597 1118965 := bbase (se 5 (by rfl) ⟨52451, by rfl⟩ : syracuseStep 1118965 = 104903) (by norm_num)
theorem B1676045 : Blo 992597 1676045 := bbase (se 3 (by rfl) ⟨314258, by rfl⟩ : syracuseStep 1676045 = 628517) (by norm_num)
theorem B1119001 : Blo 992597 1119001 := bbase (se 2 (by rfl) ⟨419625, by rfl⟩ : syracuseStep 1119001 = 839251) (by norm_num)
theorem B1413941 : Blo 992597 1413941 := bbase (se 5 (by rfl) ⟨66278, by rfl⟩ : syracuseStep 1413941 = 132557) (by norm_num)
theorem B2691893 : Blo 992597 2691893 := bbase (se 5 (by rfl) ⟨126182, by rfl⟩ : syracuseStep 2691893 = 252365) (by norm_num)
theorem B1119037 : Blo 992597 1119037 := bbase (se 3 (by rfl) ⟨209819, by rfl⟩ : syracuseStep 1119037 = 419639) (by norm_num)
theorem B1151821 : Blo 992597 1151821 := bbase (se 3 (by rfl) ⟨215966, by rfl⟩ : syracuseStep 1151821 = 431933) (by norm_num)
theorem B1119073 : Blo 992597 1119073 := bbase (se 2 (by rfl) ⟨419652, by rfl⟩ : syracuseStep 1119073 = 839305) (by norm_num)
theorem B1119109 : Blo 992597 1119109 := bbase (se 4 (by rfl) ⟨104916, by rfl⟩ : syracuseStep 1119109 = 209833) (by norm_num)
theorem B1676173 : Blo 992597 1676173 := bbase (se 3 (by rfl) ⟨314282, by rfl⟩ : syracuseStep 1676173 = 628565) (by norm_num)
theorem B1119145 : Blo 992597 1119145 := bbase (se 2 (by rfl) ⟨419679, by rfl⟩ : syracuseStep 1119145 = 839359) (by norm_num)
theorem B3019717 : Blo 992597 3019717 := bbase (se 4 (by rfl) ⟨283098, by rfl⟩ : syracuseStep 3019717 = 566197) (by norm_num)
theorem B1119181 : Blo 992597 1119181 := bbase (se 3 (by rfl) ⟨209846, by rfl⟩ : syracuseStep 1119181 = 419693) (by norm_num)
theorem B14521301 : Blo 992597 14521301 := bbase (se 7 (by rfl) ⟨170171, by rfl⟩ : syracuseStep 14521301 = 340343) (by norm_num)
theorem B1676261 : Blo 992597 1676261 := bbase (se 4 (by rfl) ⟨157149, by rfl⟩ : syracuseStep 1676261 = 314299) (by norm_num)
theorem B1119217 : Blo 992597 1119217 := bbase (se 2 (by rfl) ⟨419706, by rfl⟩ : syracuseStep 1119217 = 839413) (by norm_num)
theorem B2233349 : Blo 992597 2233349 := bbase (se 4 (by rfl) ⟨209376, by rfl⟩ : syracuseStep 2233349 = 418753) (by norm_num)
theorem B1119253 : Blo 992597 1119253 := bbase (se 6 (by rfl) ⟨26232, by rfl⟩ : syracuseStep 1119253 = 52465) (by norm_num)
theorem B1119289 : Blo 992597 1119289 := bbase (se 2 (by rfl) ⟨419733, by rfl⟩ : syracuseStep 1119289 = 839467) (by norm_num)
theorem B2233421 : Blo 992597 2233421 := bbase (se 3 (by rfl) ⟨418766, by rfl⟩ : syracuseStep 2233421 = 837533) (by norm_num)
theorem B19141717 : Blo 992597 19141717 := bbase (se 8 (by rfl) ⟨112158, by rfl⟩ : syracuseStep 19141717 = 224317) (by norm_num)
theorem B1119325 : Blo 992597 1119325 := bbase (se 3 (by rfl) ⟨209873, by rfl⟩ : syracuseStep 1119325 = 419747) (by norm_num)
theorem B1676389 : Blo 992597 1676389 := bbase (se 4 (by rfl) ⟨157161, by rfl⟩ : syracuseStep 1676389 = 314323) (by norm_num)
theorem B1119361 : Blo 992597 1119361 := bbase (se 2 (by rfl) ⟨419760, by rfl⟩ : syracuseStep 1119361 = 839521) (by norm_num)
theorem B2233493 : Blo 992597 2233493 := bbase (se 6 (by rfl) ⟨52347, by rfl⟩ : syracuseStep 2233493 = 104695) (by norm_num)
theorem B1119397 : Blo 992597 1119397 := bbase (se 4 (by rfl) ⟨104943, by rfl⟩ : syracuseStep 1119397 = 209887) (by norm_num)
theorem B1676477 : Blo 992597 1676477 := bbase (se 3 (by rfl) ⟨314339, by rfl⟩ : syracuseStep 1676477 = 628679) (by norm_num)
theorem B1119433 : Blo 992597 1119433 := bbase (se 2 (by rfl) ⟨419787, by rfl⟩ : syracuseStep 1119433 = 839575) (by norm_num)
theorem B2233565 : Blo 992597 2233565 := bbase (se 3 (by rfl) ⟨418793, by rfl⟩ : syracuseStep 2233565 = 837587) (by norm_num)
theorem B1119469 : Blo 992597 1119469 := bbase (se 3 (by rfl) ⟨209900, by rfl⟩ : syracuseStep 1119469 = 419801) (by norm_num)
theorem B1119505 : Blo 992597 1119505 := bbase (se 2 (by rfl) ⟨419814, by rfl⟩ : syracuseStep 1119505 = 839629) (by norm_num)
theorem B2233637 : Blo 992597 2233637 := bbase (se 4 (by rfl) ⟨209403, by rfl⟩ : syracuseStep 2233637 = 418807) (by norm_num)
theorem B1119541 : Blo 992597 1119541 := bbase (se 5 (by rfl) ⟨52478, by rfl⟩ : syracuseStep 1119541 = 104957) (by norm_num)
theorem B1676605 : Blo 992597 1676605 := bbase (se 3 (by rfl) ⟨314363, by rfl⟩ : syracuseStep 1676605 = 628727) (by norm_num)
theorem B1119577 : Blo 992597 1119577 := bbase (se 2 (by rfl) ⟨419841, by rfl⟩ : syracuseStep 1119577 = 839683) (by norm_num)
theorem B2233709 : Blo 992597 2233709 := bbase (se 3 (by rfl) ⟨418820, by rfl⟩ : syracuseStep 2233709 = 837641) (by norm_num)
theorem B1119613 : Blo 992597 1119613 := bbase (se 3 (by rfl) ⟨209927, by rfl⟩ : syracuseStep 1119613 = 419855) (by norm_num)
theorem B1676693 : Blo 992597 1676693 := bbase (se 6 (by rfl) ⟨39297, by rfl⟩ : syracuseStep 1676693 = 78595) (by norm_num)
theorem B1119649 : Blo 992597 1119649 := bbase (se 2 (by rfl) ⟨419868, by rfl⟩ : syracuseStep 1119649 = 839737) (by norm_num)
theorem B2233781 : Blo 992597 2233781 := bbase (se 5 (by rfl) ⟨104708, by rfl⟩ : syracuseStep 2233781 = 209417) (by norm_num)
theorem B1119685 : Blo 992597 1119685 := bbase (se 4 (by rfl) ⟨104970, by rfl⟩ : syracuseStep 1119685 = 209941) (by norm_num)
theorem B3184085 : Blo 992597 3184085 := bbase (se 7 (by rfl) ⟨37313, by rfl⟩ : syracuseStep 3184085 = 74627) (by norm_num)
theorem B1119721 : Blo 992597 1119721 := bbase (se 2 (by rfl) ⟨419895, by rfl⟩ : syracuseStep 1119721 = 839791) (by norm_num)
theorem B2233853 : Blo 992597 2233853 := bbase (se 3 (by rfl) ⟨418847, by rfl⟩ : syracuseStep 2233853 = 837695) (by norm_num)
theorem B1119757 : Blo 992597 1119757 := bbase (se 3 (by rfl) ⟨209954, by rfl⟩ : syracuseStep 1119757 = 419909) (by norm_num)
theorem B1676821 : Blo 992597 1676821 := bbase (se 6 (by rfl) ⟨39300, by rfl⟩ : syracuseStep 1676821 = 78601) (by norm_num)
theorem B1021465 : Blo 992597 1021465 := bbase (se 2 (by rfl) ⟨383049, by rfl⟩ : syracuseStep 1021465 = 766099) (by norm_num)
theorem B1414693 : Blo 992597 1414693 := bbase (se 4 (by rfl) ⟨132627, by rfl⟩ : syracuseStep 1414693 = 265255) (by norm_num)
theorem B1119793 : Blo 992597 1119793 := bbase (se 2 (by rfl) ⟨419922, by rfl⟩ : syracuseStep 1119793 = 839845) (by norm_num)
theorem B2233925 : Blo 992597 2233925 := bbase (se 4 (by rfl) ⟨209430, by rfl⟩ : syracuseStep 2233925 = 418861) (by norm_num)
theorem B1119829 : Blo 992597 1119829 := bbase (se 8 (by rfl) ⟨6561, by rfl⟩ : syracuseStep 1119829 = 13123) (by norm_num)
theorem B2692693 : Blo 992597 2692693 := bbase (se 8 (by rfl) ⟨15777, by rfl⟩ : syracuseStep 2692693 = 31555) (by norm_num)
theorem B1676909 : Blo 992597 1676909 := bbase (se 3 (by rfl) ⟨314420, by rfl⟩ : syracuseStep 1676909 = 628841) (by norm_num)
theorem B1119865 : Blo 992597 1119865 := bbase (se 2 (by rfl) ⟨419949, by rfl⟩ : syracuseStep 1119865 = 839899) (by norm_num)
theorem B2233997 : Blo 992597 2233997 := bbase (se 3 (by rfl) ⟨418874, by rfl⟩ : syracuseStep 2233997 = 837749) (by norm_num)
theorem B10753685 : Blo 992597 10753685 := bbase (se 6 (by rfl) ⟨252039, by rfl⟩ : syracuseStep 10753685 = 504079) (by norm_num)
theorem B1119901 : Blo 992597 1119901 := bbase (se 3 (by rfl) ⟨209981, by rfl⟩ : syracuseStep 1119901 = 419963) (by norm_num)
theorem B1119937 : Blo 992597 1119937 := bbase (se 2 (by rfl) ⟨419976, by rfl⟩ : syracuseStep 1119937 = 839953) (by norm_num)
theorem B2234069 : Blo 992597 2234069 := bbase (se 7 (by rfl) ⟨26180, by rfl⟩ : syracuseStep 2234069 = 52361) (by norm_num)
theorem B1119973 : Blo 992597 1119973 := bbase (se 4 (by rfl) ⟨104997, by rfl⟩ : syracuseStep 1119973 = 209995) (by norm_num)
theorem B1677037 : Blo 992597 1677037 := bbase (se 3 (by rfl) ⟨314444, by rfl⟩ : syracuseStep 1677037 = 628889) (by norm_num)
theorem B1120009 : Blo 992597 1120009 := bbase (se 2 (by rfl) ⟨420003, by rfl⟩ : syracuseStep 1120009 = 840007) (by norm_num)
theorem B2234141 : Blo 992597 2234141 := bbase (se 3 (by rfl) ⟨418901, by rfl⟩ : syracuseStep 2234141 = 837803) (by norm_num)
theorem B1021729 : Blo 992597 1021729 := bbase (se 2 (by rfl) ⟨383148, by rfl⟩ : syracuseStep 1021729 = 766297) (by norm_num)
theorem B1120045 : Blo 992597 1120045 := bbase (se 3 (by rfl) ⟨210008, by rfl⟩ : syracuseStep 1120045 = 420017) (by norm_num)
theorem B1677125 : Blo 992597 1677125 := bbase (se 4 (by rfl) ⟨157230, by rfl⟩ : syracuseStep 1677125 = 314461) (by norm_num)
theorem B1120081 : Blo 992597 1120081 := bbase (se 2 (by rfl) ⟨420030, by rfl⟩ : syracuseStep 1120081 = 840061) (by norm_num)
theorem B2234213 : Blo 992597 2234213 := bbase (se 4 (by rfl) ⟨209457, by rfl⟩ : syracuseStep 2234213 = 418915) (by norm_num)
theorem B1120117 : Blo 992597 1120117 := bbase (se 5 (by rfl) ⟨52505, by rfl⟩ : syracuseStep 1120117 = 105011) (by norm_num)
theorem B1120153 : Blo 992597 1120153 := bbase (se 2 (by rfl) ⟨420057, by rfl⟩ : syracuseStep 1120153 = 840115) (by norm_num)
theorem B2234285 : Blo 992597 2234285 := bbase (se 3 (by rfl) ⟨418928, by rfl⟩ : syracuseStep 2234285 = 837857) (by norm_num)
theorem B1120189 : Blo 992597 1120189 := bbase (se 3 (by rfl) ⟨210035, by rfl⟩ : syracuseStep 1120189 = 420071) (by norm_num)
theorem B1677253 : Blo 992597 1677253 := bbase (se 4 (by rfl) ⟨157242, by rfl⟩ : syracuseStep 1677253 = 314485) (by norm_num)
theorem B1120225 : Blo 992597 1120225 := bbase (se 2 (by rfl) ⟨420084, by rfl⟩ : syracuseStep 1120225 = 840169) (by norm_num)
theorem B2234357 : Blo 992597 2234357 := bbase (se 5 (by rfl) ⟨104735, by rfl⟩ : syracuseStep 2234357 = 209471) (by norm_num)
theorem B1120261 : Blo 992597 1120261 := bbase (se 4 (by rfl) ⟨105024, by rfl⟩ : syracuseStep 1120261 = 210049) (by norm_num)
theorem B1677341 : Blo 992597 1677341 := bbase (se 3 (by rfl) ⟨314501, by rfl⟩ : syracuseStep 1677341 = 629003) (by norm_num)
theorem B1120297 : Blo 992597 1120297 := bbase (se 2 (by rfl) ⟨420111, by rfl⟩ : syracuseStep 1120297 = 840223) (by norm_num)
theorem B2234429 : Blo 992597 2234429 := bbase (se 3 (by rfl) ⟨418955, by rfl⟩ : syracuseStep 2234429 = 837911) (by norm_num)
theorem B1120333 : Blo 992597 1120333 := bbase (se 3 (by rfl) ⟨210062, by rfl⟩ : syracuseStep 1120333 = 420125) (by norm_num)
theorem B1120369 : Blo 992597 1120369 := bbase (se 2 (by rfl) ⟨420138, by rfl⟩ : syracuseStep 1120369 = 840277) (by norm_num)
theorem B1022081 : Blo 992597 1022081 := bbase (se 2 (by rfl) ⟨383280, by rfl⟩ : syracuseStep 1022081 = 766561) (by norm_num)
theorem B2234501 : Blo 992597 2234501 := bbase (se 4 (by rfl) ⟨209484, by rfl⟩ : syracuseStep 2234501 = 418969) (by norm_num)
theorem B1120405 : Blo 992597 1120405 := bbase (se 6 (by rfl) ⟨26259, by rfl⟩ : syracuseStep 1120405 = 52519) (by norm_num)
theorem B1677469 : Blo 992597 1677469 := bbase (se 3 (by rfl) ⟨314525, by rfl⟩ : syracuseStep 1677469 = 629051) (by norm_num)
theorem B1120441 : Blo 992597 1120441 := bbase (se 2 (by rfl) ⟨420165, by rfl⟩ : syracuseStep 1120441 = 840331) (by norm_num)
theorem B2234573 : Blo 992597 2234573 := bbase (se 3 (by rfl) ⟨418982, by rfl⟩ : syracuseStep 2234573 = 837965) (by norm_num)
theorem B1611997 : Blo 992597 1611997 := bbase (se 3 (by rfl) ⟨302249, by rfl⟩ : syracuseStep 1611997 = 604499) (by norm_num)
theorem B1120477 : Blo 992597 1120477 := bbase (se 3 (by rfl) ⟨210089, by rfl⟩ : syracuseStep 1120477 = 420179) (by norm_num)
theorem B1677557 : Blo 992597 1677557 := bbase (se 5 (by rfl) ⟨78635, by rfl⟩ : syracuseStep 1677557 = 157271) (by norm_num)
theorem B1120513 : Blo 992597 1120513 := bbase (se 2 (by rfl) ⟨420192, by rfl⟩ : syracuseStep 1120513 = 840385) (by norm_num)
theorem B2234645 : Blo 992597 2234645 := bbase (se 6 (by rfl) ⟨52374, by rfl⟩ : syracuseStep 2234645 = 104749) (by norm_num)
theorem B1120549 : Blo 992597 1120549 := bbase (se 4 (by rfl) ⟨105051, by rfl⟩ : syracuseStep 1120549 = 210103) (by norm_num)
theorem B1415485 : Blo 992597 1415485 := bbase (se 3 (by rfl) ⟨265403, by rfl⟩ : syracuseStep 1415485 = 530807) (by norm_num)
theorem B1120585 : Blo 992597 1120585 := bbase (se 2 (by rfl) ⟨420219, by rfl⟩ : syracuseStep 1120585 = 840439) (by norm_num)
theorem B2234717 : Blo 992597 2234717 := bbase (se 3 (by rfl) ⟨419009, by rfl⟩ : syracuseStep 2234717 = 838019) (by norm_num)
theorem B1120621 : Blo 992597 1120621 := bbase (se 3 (by rfl) ⟨210116, by rfl⟩ : syracuseStep 1120621 = 420233) (by norm_num)
theorem B1677685 : Blo 992597 1677685 := bbase (se 5 (by rfl) ⟨78641, by rfl⟩ : syracuseStep 1677685 = 157283) (by norm_num)
theorem B2267509 : Blo 992597 2267509 := bbase (se 5 (by rfl) ⟨106289, by rfl⟩ : syracuseStep 2267509 = 212579) (by norm_num)
theorem B1120657 : Blo 992597 1120657 := bbase (se 2 (by rfl) ⟨420246, by rfl⟩ : syracuseStep 1120657 = 840493) (by norm_num)
theorem B3774869 : Blo 992597 3774869 := bbase (se 6 (by rfl) ⟨88473, by rfl⟩ : syracuseStep 3774869 = 176947) (by norm_num)
theorem B2234789 : Blo 992597 2234789 := bbase (se 4 (by rfl) ⟨209511, by rfl⟩ : syracuseStep 2234789 = 419023) (by norm_num)
theorem B1120693 : Blo 992597 1120693 := bbase (se 5 (by rfl) ⟨52532, by rfl⟩ : syracuseStep 1120693 = 105065) (by norm_num)
theorem B1677773 : Blo 992597 1677773 := bbase (se 3 (by rfl) ⟨314582, by rfl⟩ : syracuseStep 1677773 = 629165) (by norm_num)
theorem B1120729 : Blo 992597 1120729 := bbase (se 2 (by rfl) ⟨420273, by rfl⟩ : syracuseStep 1120729 = 840547) (by norm_num)
theorem B2234861 : Blo 992597 2234861 := bbase (se 3 (by rfl) ⟨419036, by rfl⟩ : syracuseStep 2234861 = 838073) (by norm_num)
theorem B2693621 : Blo 992597 2693621 := bbase (se 5 (by rfl) ⟨126263, by rfl⟩ : syracuseStep 2693621 = 252527) (by norm_num)
theorem B1120765 : Blo 992597 1120765 := bbase (se 3 (by rfl) ⟨210143, by rfl⟩ : syracuseStep 1120765 = 420287) (by norm_num)
theorem B1120801 : Blo 992597 1120801 := bbase (se 2 (by rfl) ⟨420300, by rfl⟩ : syracuseStep 1120801 = 840601) (by norm_num)
theorem B2234933 : Blo 992597 2234933 := bbase (se 5 (by rfl) ⟨104762, by rfl⟩ : syracuseStep 2234933 = 209525) (by norm_num)
theorem B1120837 : Blo 992597 1120837 := bbase (se 4 (by rfl) ⟨105078, by rfl⟩ : syracuseStep 1120837 = 210157) (by norm_num)
theorem B1677901 : Blo 992597 1677901 := bbase (se 3 (by rfl) ⟨314606, by rfl⟩ : syracuseStep 1677901 = 629213) (by norm_num)
theorem B1120873 : Blo 992597 1120873 := bbase (se 2 (by rfl) ⟨420327, by rfl⟩ : syracuseStep 1120873 = 840655) (by norm_num)
theorem B2235005 : Blo 992597 2235005 := bbase (se 3 (by rfl) ⟨419063, by rfl⟩ : syracuseStep 2235005 = 838127) (by norm_num)
theorem B1415821 : Blo 992597 1415821 := bbase (se 3 (by rfl) ⟨265466, by rfl⟩ : syracuseStep 1415821 = 530933) (by norm_num)
theorem B1120909 : Blo 992597 1120909 := bbase (se 3 (by rfl) ⟨210170, by rfl⟩ : syracuseStep 1120909 = 420341) (by norm_num)
theorem B1677989 : Blo 992597 1677989 := bbase (se 4 (by rfl) ⟨157311, by rfl⟩ : syracuseStep 1677989 = 314623) (by norm_num)
theorem B1120945 : Blo 992597 1120945 := bbase (se 2 (by rfl) ⟨420354, by rfl⟩ : syracuseStep 1120945 = 840709) (by norm_num)
theorem B3775157 : Blo 992597 3775157 := bbase (se 5 (by rfl) ⟨176960, by rfl⟩ : syracuseStep 3775157 = 353921) (by norm_num)
theorem B2235077 : Blo 992597 2235077 := bbase (se 4 (by rfl) ⟨209538, by rfl⟩ : syracuseStep 2235077 = 419077) (by norm_num)
theorem B1120981 : Blo 992597 1120981 := bbase (se 7 (by rfl) ⟨13136, by rfl⟩ : syracuseStep 1120981 = 26273) (by norm_num)
theorem B4528885 : Blo 992597 4528885 := bbase (se 5 (by rfl) ⟨212291, by rfl⟩ : syracuseStep 4528885 = 424583) (by norm_num)
theorem B1121017 : Blo 992597 1121017 := bbase (se 2 (by rfl) ⟨420381, by rfl⟩ : syracuseStep 1121017 = 840763) (by norm_num)
theorem B2235149 : Blo 992597 2235149 := bbase (se 3 (by rfl) ⟨419090, by rfl⟩ : syracuseStep 2235149 = 838181) (by norm_num)
theorem B1121053 : Blo 992597 1121053 := bbase (se 3 (by rfl) ⟨210197, by rfl⟩ : syracuseStep 1121053 = 420395) (by norm_num)
theorem B1678117 : Blo 992597 1678117 := bbase (se 4 (by rfl) ⟨157323, by rfl⟩ : syracuseStep 1678117 = 314647) (by norm_num)
theorem B1121089 : Blo 992597 1121089 := bbase (se 2 (by rfl) ⟨420408, by rfl⟩ : syracuseStep 1121089 = 840817) (by norm_num)
theorem B2235221 : Blo 992597 2235221 := bbase (se 9 (by rfl) ⟨6548, by rfl⟩ : syracuseStep 2235221 = 13097) (by norm_num)
theorem B1416037 : Blo 992597 1416037 := bbase (se 4 (by rfl) ⟨132753, by rfl⟩ : syracuseStep 1416037 = 265507) (by norm_num)
theorem B1121125 : Blo 992597 1121125 := bbase (se 4 (by rfl) ⟨105105, by rfl⟩ : syracuseStep 1121125 = 210211) (by norm_num)
theorem B1678205 : Blo 992597 1678205 := bbase (se 3 (by rfl) ⟨314663, by rfl⟩ : syracuseStep 1678205 = 629327) (by norm_num)
theorem B1121161 : Blo 992597 1121161 := bbase (se 2 (by rfl) ⟨420435, by rfl⟩ : syracuseStep 1121161 = 840871) (by norm_num)
theorem B2235293 : Blo 992597 2235293 := bbase (se 3 (by rfl) ⟨419117, by rfl⟩ : syracuseStep 2235293 = 838235) (by norm_num)
theorem B2235365 : Blo 992597 2235365 := bbase (se 4 (by rfl) ⟨209565, by rfl⟩ : syracuseStep 2235365 = 419131) (by norm_num)
theorem B1678333 : Blo 992597 1678333 := bbase (se 3 (by rfl) ⟨314687, by rfl⟩ : syracuseStep 1678333 = 629375) (by norm_num)
theorem B2235437 : Blo 992597 2235437 := bbase (se 3 (by rfl) ⟨419144, by rfl⟩ : syracuseStep 2235437 = 838289) (by norm_num)
theorem B1678421 : Blo 992597 1678421 := bbase (se 8 (by rfl) ⟨9834, by rfl⟩ : syracuseStep 1678421 = 19669) (by norm_num)
theorem B2235509 : Blo 992597 2235509 := bbase (se 5 (by rfl) ⟨104789, by rfl⟩ : syracuseStep 2235509 = 209579) (by norm_num)
theorem B2235581 : Blo 992597 2235581 := bbase (se 3 (by rfl) ⟨419171, by rfl⟩ : syracuseStep 2235581 = 838343) (by norm_num)
theorem B1678549 : Blo 992597 1678549 := bbase (se 7 (by rfl) ⟨19670, by rfl⟩ : syracuseStep 1678549 = 39341) (by norm_num)
theorem B1416413 : Blo 992597 1416413 := bbase (se 3 (by rfl) ⟨265577, by rfl⟩ : syracuseStep 1416413 = 531155) (by norm_num)
theorem B2235653 : Blo 992597 2235653 := bbase (se 4 (by rfl) ⟨209592, by rfl⟩ : syracuseStep 2235653 = 419185) (by norm_num)
theorem B1678637 : Blo 992597 1678637 := bbase (se 3 (by rfl) ⟨314744, by rfl⟩ : syracuseStep 1678637 = 629489) (by norm_num)
theorem B2235725 : Blo 992597 2235725 := bbase (se 3 (by rfl) ⟨419198, by rfl⟩ : syracuseStep 2235725 = 838397) (by norm_num)
theorem B2235797 : Blo 992597 2235797 := bbase (se 6 (by rfl) ⟨52401, by rfl⟩ : syracuseStep 2235797 = 104803) (by norm_num)
theorem B1678765 : Blo 992597 1678765 := bbase (se 3 (by rfl) ⟨314768, by rfl⟩ : syracuseStep 1678765 = 629537) (by norm_num)
theorem B2235869 : Blo 992597 2235869 := bbase (se 3 (by rfl) ⟨419225, by rfl⟩ : syracuseStep 2235869 = 838451) (by norm_num)
theorem B1678853 : Blo 992597 1678853 := bbase (se 4 (by rfl) ⟨157392, by rfl⟩ : syracuseStep 1678853 = 314785) (by norm_num)
theorem B2235941 : Blo 992597 2235941 := bbase (se 4 (by rfl) ⟨209619, by rfl⟩ : syracuseStep 2235941 = 419239) (by norm_num)
theorem B2236013 : Blo 992597 2236013 := bbase (se 3 (by rfl) ⟨419252, by rfl⟩ : syracuseStep 2236013 = 838505) (by norm_num)
theorem B9576053 : Blo 992597 9576053 := bbase (se 5 (by rfl) ⟨448877, by rfl⟩ : syracuseStep 9576053 = 897755) (by norm_num)
theorem B1678981 : Blo 992597 1678981 := bbase (se 4 (by rfl) ⟨157404, by rfl⟩ : syracuseStep 1678981 = 314809) (by norm_num)
theorem B3186341 : Blo 992597 3186341 := bbase (se 4 (by rfl) ⟨298719, by rfl⟩ : syracuseStep 3186341 = 597439) (by norm_num)
theorem B2236085 : Blo 992597 2236085 := bbase (se 5 (by rfl) ⟨104816, by rfl⟩ : syracuseStep 2236085 = 209633) (by norm_num)
theorem B3350213 : Blo 992597 3350213 := bbase (se 4 (by rfl) ⟨314082, by rfl⟩ : syracuseStep 3350213 = 628165) (by norm_num)
theorem B4038341 : Blo 992597 4038341 := bbase (se 4 (by rfl) ⟨378594, by rfl⟩ : syracuseStep 4038341 = 757189) (by norm_num)
theorem B1679069 : Blo 992597 1679069 := bbase (se 3 (by rfl) ⟨314825, by rfl⟩ : syracuseStep 1679069 = 629651) (by norm_num)
theorem B2236157 : Blo 992597 2236157 := bbase (se 3 (by rfl) ⟨419279, by rfl⟩ : syracuseStep 2236157 = 838559) (by norm_num)
theorem B8625973 : Blo 992597 8625973 := bbase (se 5 (by rfl) ⟨404342, by rfl⟩ : syracuseStep 8625973 = 808685) (by norm_num)
theorem B2236229 : Blo 992597 2236229 := bbase (se 4 (by rfl) ⟨209646, by rfl⟩ : syracuseStep 2236229 = 419293) (by norm_num)
theorem B3776341 : Blo 992597 3776341 := bbase (se 9 (by rfl) ⟨11063, by rfl⟩ : syracuseStep 3776341 = 22127) (by norm_num)
theorem B1679197 : Blo 992597 1679197 := bbase (se 3 (by rfl) ⟨314849, by rfl⟩ : syracuseStep 1679197 = 629699) (by norm_num)
theorem B2236301 : Blo 992597 2236301 := bbase (se 3 (by rfl) ⟨419306, by rfl⟩ : syracuseStep 2236301 = 838613) (by norm_num)
theorem B1679285 : Blo 992597 1679285 := bbase (se 5 (by rfl) ⟨78716, by rfl⟩ : syracuseStep 1679285 = 157433) (by norm_num)
theorem B2236373 : Blo 992597 2236373 := bbase (se 7 (by rfl) ⟨26207, by rfl⟩ : syracuseStep 2236373 = 52415) (by norm_num)
theorem B2236445 : Blo 992597 2236445 := bbase (se 3 (by rfl) ⟨419333, by rfl⟩ : syracuseStep 2236445 = 838667) (by norm_num)
theorem B1679413 : Blo 992597 1679413 := bbase (se 5 (by rfl) ⟨78722, by rfl⟩ : syracuseStep 1679413 = 157445) (by norm_num)
theorem B16162901 : Blo 992597 16162901 := bbase (se 8 (by rfl) ⟨94704, by rfl⟩ : syracuseStep 16162901 = 189409) (by norm_num)
theorem B2236517 : Blo 992597 2236517 := bbase (se 4 (by rfl) ⟨209673, by rfl⟩ : syracuseStep 2236517 = 419347) (by norm_num)
theorem B3350645 : Blo 992597 3350645 := bbase (se 5 (by rfl) ⟨157061, by rfl⟩ : syracuseStep 3350645 = 314123) (by norm_num)
theorem B3776645 : Blo 992597 3776645 := bbase (se 4 (by rfl) ⟨354060, by rfl⟩ : syracuseStep 3776645 = 708121) (by norm_num)
theorem B1679501 : Blo 992597 1679501 := bbase (se 3 (by rfl) ⟨314906, by rfl⟩ : syracuseStep 1679501 = 629813) (by norm_num)
theorem B2236589 : Blo 992597 2236589 := bbase (se 3 (by rfl) ⟨419360, by rfl⟩ : syracuseStep 2236589 = 838721) (by norm_num)
theorem B6037685 : Blo 992597 6037685 := bbase (se 5 (by rfl) ⟨283016, by rfl⟩ : syracuseStep 6037685 = 566033) (by norm_num)
theorem B2236661 : Blo 992597 2236661 := bbase (se 5 (by rfl) ⟨104843, by rfl⟩ : syracuseStep 2236661 = 209687) (by norm_num)
theorem B1679629 : Blo 992597 1679629 := bbase (se 3 (by rfl) ⟨314930, by rfl⟩ : syracuseStep 1679629 = 629861) (by norm_num)
theorem B2236733 : Blo 992597 2236733 := bbase (se 3 (by rfl) ⟨419387, by rfl⟩ : syracuseStep 2236733 = 838775) (by norm_num)
theorem B1679717 : Blo 992597 1679717 := bbase (se 4 (by rfl) ⟨157473, by rfl⟩ : syracuseStep 1679717 = 314947) (by norm_num)
theorem B6037877 : Blo 992597 6037877 := bbase (se 5 (by rfl) ⟨283025, by rfl⟩ : syracuseStep 6037877 = 566051) (by norm_num)
theorem B2236805 : Blo 992597 2236805 := bbase (se 4 (by rfl) ⟨209700, by rfl⟩ : syracuseStep 2236805 = 419401) (by norm_num)
theorem B3187109 : Blo 992597 3187109 := bbase (se 4 (by rfl) ⟨298791, by rfl⟩ : syracuseStep 3187109 = 597583) (by norm_num)
theorem B2236877 : Blo 992597 2236877 := bbase (se 3 (by rfl) ⟨419414, by rfl⟩ : syracuseStep 2236877 = 838829) (by norm_num)
theorem B1679845 : Blo 992597 1679845 := bbase (se 4 (by rfl) ⟨157485, by rfl⟩ : syracuseStep 1679845 = 314971) (by norm_num)
theorem B2236949 : Blo 992597 2236949 := bbase (se 6 (by rfl) ⟨52428, by rfl⟩ : syracuseStep 2236949 = 104857) (by norm_num)
theorem B3351077 : Blo 992597 3351077 := bbase (se 4 (by rfl) ⟨314163, by rfl⟩ : syracuseStep 3351077 = 628327) (by norm_num)
theorem B3580453 : Blo 992597 3580453 := bbase (se 4 (by rfl) ⟨335667, by rfl⟩ : syracuseStep 3580453 = 671335) (by norm_num)
theorem B3875381 : Blo 992597 3875381 := bbase (se 5 (by rfl) ⟨181658, by rfl⟩ : syracuseStep 3875381 = 363317) (by norm_num)
theorem B1679933 : Blo 992597 1679933 := bbase (se 3 (by rfl) ⟨314987, by rfl⟩ : syracuseStep 1679933 = 629975) (by norm_num)
theorem B2237021 : Blo 992597 2237021 := bbase (se 3 (by rfl) ⟨419441, by rfl⟩ : syracuseStep 2237021 = 838883) (by norm_num)
theorem B1417837 : Blo 992597 1417837 := bbase (se 3 (by rfl) ⟨265844, by rfl⟩ : syracuseStep 1417837 = 531689) (by norm_num)
theorem B2237093 : Blo 992597 2237093 := bbase (se 4 (by rfl) ⟨209727, by rfl⟩ : syracuseStep 2237093 = 419455) (by norm_num)
theorem B1680061 : Blo 992597 1680061 := bbase (se 3 (by rfl) ⟨315011, by rfl⟩ : syracuseStep 1680061 = 630023) (by norm_num)
theorem B2237165 : Blo 992597 2237165 := bbase (se 3 (by rfl) ⟨419468, by rfl⟩ : syracuseStep 2237165 = 838937) (by norm_num)
theorem B6791957 : Blo 992597 6791957 := bbase (se 6 (by rfl) ⟨159186, by rfl⟩ : syracuseStep 6791957 = 318373) (by norm_num)
theorem B1680149 : Blo 992597 1680149 := bbase (se 6 (by rfl) ⟨39378, by rfl⟩ : syracuseStep 1680149 = 78757) (by norm_num)
theorem B2237237 : Blo 992597 2237237 := bbase (se 5 (by rfl) ⟨104870, by rfl⟩ : syracuseStep 2237237 = 209741) (by norm_num)
theorem B3580757 : Blo 992597 3580757 := bbase (se 9 (by rfl) ⟨10490, by rfl⟩ : syracuseStep 3580757 = 20981) (by norm_num)
theorem B2237309 : Blo 992597 2237309 := bbase (se 3 (by rfl) ⟨419495, by rfl⟩ : syracuseStep 2237309 = 838991) (by norm_num)
theorem B1680277 : Blo 992597 1680277 := bbase (se 6 (by rfl) ⟨39381, by rfl⟩ : syracuseStep 1680277 = 78763) (by norm_num)
theorem B3187621 : Blo 992597 3187621 := bbase (se 4 (by rfl) ⟨298839, by rfl⟩ : syracuseStep 3187621 = 597679) (by norm_num)
theorem B2237381 : Blo 992597 2237381 := bbase (se 4 (by rfl) ⟨209754, by rfl⟩ : syracuseStep 2237381 = 419509) (by norm_num)
theorem B3351509 : Blo 992597 3351509 := bbase (se 7 (by rfl) ⟨39275, by rfl⟩ : syracuseStep 3351509 = 78551) (by norm_num)
theorem B1680365 : Blo 992597 1680365 := bbase (se 3 (by rfl) ⟨315068, by rfl⟩ : syracuseStep 1680365 = 630137) (by norm_num)
theorem B2237453 : Blo 992597 2237453 := bbase (se 3 (by rfl) ⟨419522, by rfl⟩ : syracuseStep 2237453 = 839045) (by norm_num)
theorem B2237525 : Blo 992597 2237525 := bbase (se 8 (by rfl) ⟨13110, by rfl⟩ : syracuseStep 2237525 = 26221) (by norm_num)
theorem B1680493 : Blo 992597 1680493 := bbase (se 3 (by rfl) ⟨315092, by rfl⟩ : syracuseStep 1680493 = 630185) (by norm_num)
theorem B2827381 : Blo 992597 2827381 := bbase (se 5 (by rfl) ⟨132533, by rfl⟩ : syracuseStep 2827381 = 265067) (by norm_num)
theorem B2237597 : Blo 992597 2237597 := bbase (se 3 (by rfl) ⟨419549, by rfl⟩ : syracuseStep 2237597 = 839099) (by norm_num)
theorem B1418429 : Blo 992597 1418429 := bbase (se 3 (by rfl) ⟨265955, by rfl⟩ : syracuseStep 1418429 = 531911) (by norm_num)
theorem B1680581 : Blo 992597 1680581 := bbase (se 4 (by rfl) ⟨157554, by rfl⟩ : syracuseStep 1680581 = 315109) (by norm_num)
theorem B2237669 : Blo 992597 2237669 := bbase (se 4 (by rfl) ⟨209781, by rfl⟩ : syracuseStep 2237669 = 419563) (by norm_num)
theorem B1418509 : Blo 992597 1418509 := bbase (se 3 (by rfl) ⟨265970, by rfl⟩ : syracuseStep 1418509 = 531941) (by norm_num)
theorem B2827541 : Blo 992597 2827541 := bbase (se 6 (by rfl) ⟨66270, by rfl⟩ : syracuseStep 2827541 = 132541) (by norm_num)
theorem B2237741 : Blo 992597 2237741 := bbase (se 3 (by rfl) ⟨419576, by rfl⟩ : syracuseStep 2237741 = 839153) (by norm_num)
theorem B1680709 : Blo 992597 1680709 := bbase (se 4 (by rfl) ⟨157566, by rfl⟩ : syracuseStep 1680709 = 315133) (by norm_num)
theorem B2237813 : Blo 992597 2237813 := bbase (se 5 (by rfl) ⟨104897, by rfl⟩ : syracuseStep 2237813 = 209795) (by norm_num)
theorem B3351941 : Blo 992597 3351941 := bbase (se 4 (by rfl) ⟨314244, by rfl⟩ : syracuseStep 3351941 = 628489) (by norm_num)
theorem B1418629 : Blo 992597 1418629 := bbase (se 4 (by rfl) ⟨132996, by rfl⟩ : syracuseStep 1418629 = 265993) (by norm_num)
theorem B1680797 : Blo 992597 1680797 := bbase (se 3 (by rfl) ⟨315149, by rfl⟩ : syracuseStep 1680797 = 630299) (by norm_num)
theorem B2237885 : Blo 992597 2237885 := bbase (se 3 (by rfl) ⟨419603, by rfl⟩ : syracuseStep 2237885 = 839207) (by norm_num)
theorem B1418725 : Blo 992597 1418725 := bbase (se 4 (by rfl) ⟨133005, by rfl⟩ : syracuseStep 1418725 = 266011) (by norm_num)
theorem B2827781 : Blo 992597 2827781 := bbase (se 4 (by rfl) ⟨265104, by rfl⟩ : syracuseStep 2827781 = 530209) (by norm_num)
theorem B2237957 : Blo 992597 2237957 := bbase (se 4 (by rfl) ⟨209808, by rfl⟩ : syracuseStep 2237957 = 419617) (by norm_num)
theorem B1680925 : Blo 992597 1680925 := bbase (se 3 (by rfl) ⟨315173, by rfl⟩ : syracuseStep 1680925 = 630347) (by norm_num)
theorem B2238029 : Blo 992597 2238029 := bbase (se 3 (by rfl) ⟨419630, by rfl⟩ : syracuseStep 2238029 = 839261) (by norm_num)
theorem B1681013 : Blo 992597 1681013 := bbase (se 5 (by rfl) ⟨78797, by rfl⟩ : syracuseStep 1681013 = 157595) (by norm_num)
theorem B2238101 : Blo 992597 2238101 := bbase (se 6 (by rfl) ⟨52455, by rfl⟩ : syracuseStep 2238101 = 104911) (by norm_num)
theorem B2827973 : Blo 992597 2827973 := bbase (se 4 (by rfl) ⟨265122, by rfl⟩ : syracuseStep 2827973 = 530245) (by norm_num)
theorem B2238173 : Blo 992597 2238173 := bbase (se 3 (by rfl) ⟨419657, by rfl⟩ : syracuseStep 2238173 = 839315) (by norm_num)
theorem B1681141 : Blo 992597 1681141 := bbase (se 5 (by rfl) ⟨78803, by rfl⟩ : syracuseStep 1681141 = 157607) (by norm_num)
theorem B2238245 : Blo 992597 2238245 := bbase (se 4 (by rfl) ⟨209835, by rfl⟩ : syracuseStep 2238245 = 419671) (by norm_num)
theorem B3352373 : Blo 992597 3352373 := bbase (se 5 (by rfl) ⟨157142, by rfl⟩ : syracuseStep 3352373 = 314285) (by norm_num)
theorem B1681229 : Blo 992597 1681229 := bbase (se 3 (by rfl) ⟨315230, by rfl⟩ : syracuseStep 1681229 = 630461) (by norm_num)
theorem B2238317 : Blo 992597 2238317 := bbase (se 3 (by rfl) ⟨419684, by rfl⟩ : syracuseStep 2238317 = 839369) (by norm_num)
theorem B2238389 : Blo 992597 2238389 := bbase (se 5 (by rfl) ⟨104924, by rfl⟩ : syracuseStep 2238389 = 209849) (by norm_num)
theorem B1681357 : Blo 992597 1681357 := bbase (se 3 (by rfl) ⟨315254, by rfl⟩ : syracuseStep 1681357 = 630509) (by norm_num)
theorem B2238461 : Blo 992597 2238461 := bbase (se 3 (by rfl) ⟨419711, by rfl⟩ : syracuseStep 2238461 = 839423) (by norm_num)
theorem B1681445 : Blo 992597 1681445 := bbase (se 4 (by rfl) ⟨157635, by rfl⟩ : syracuseStep 1681445 = 315271) (by norm_num)
theorem B2238533 : Blo 992597 2238533 := bbase (se 4 (by rfl) ⟨209862, by rfl⟩ : syracuseStep 2238533 = 419725) (by norm_num)
theorem B6367349 : Blo 992597 6367349 := bbase (se 5 (by rfl) ⟨298469, by rfl⟩ : syracuseStep 6367349 = 596939) (by norm_num)
theorem B2238605 : Blo 992597 2238605 := bbase (se 3 (by rfl) ⟨419738, by rfl⟩ : syracuseStep 2238605 = 839477) (by norm_num)
theorem B1681573 : Blo 992597 1681573 := bbase (se 4 (by rfl) ⟨157647, by rfl⟩ : syracuseStep 1681573 = 315295) (by norm_num)
theorem B3778757 : Blo 992597 3778757 := bbase (se 4 (by rfl) ⟨354258, by rfl⟩ : syracuseStep 3778757 = 708517) (by norm_num)
theorem B7547093 : Blo 992597 7547093 := bbase (se 7 (by rfl) ⟨88442, by rfl⟩ : syracuseStep 7547093 = 176885) (by norm_num)
theorem B2238677 : Blo 992597 2238677 := bbase (se 7 (by rfl) ⟨26234, by rfl⟩ : syracuseStep 2238677 = 52469) (by norm_num)
theorem B3352805 : Blo 992597 3352805 := bbase (se 4 (by rfl) ⟨314325, by rfl⟩ : syracuseStep 3352805 = 628651) (by norm_num)
theorem B1681661 : Blo 992597 1681661 := bbase (se 3 (by rfl) ⟨315311, by rfl⟩ : syracuseStep 1681661 = 630623) (by norm_num)
theorem B2238749 : Blo 992597 2238749 := bbase (se 3 (by rfl) ⟨419765, by rfl⟩ : syracuseStep 2238749 = 839531) (by norm_num)
theorem B2238821 : Blo 992597 2238821 := bbase (se 4 (by rfl) ⟨209889, by rfl⟩ : syracuseStep 2238821 = 419779) (by norm_num)
theorem B2238893 : Blo 992597 2238893 := bbase (se 3 (by rfl) ⟨419792, by rfl⟩ : syracuseStep 2238893 = 839585) (by norm_num)
theorem B3779045 : Blo 992597 3779045 := bbase (se 4 (by rfl) ⟨354285, by rfl⟩ : syracuseStep 3779045 = 708571) (by norm_num)
theorem B2238965 : Blo 992597 2238965 := bbase (se 5 (by rfl) ⟨104951, by rfl⟩ : syracuseStep 2238965 = 209903) (by norm_num)
theorem B2239037 : Blo 992597 2239037 := bbase (se 3 (by rfl) ⟨419819, by rfl⟩ : syracuseStep 2239037 = 839639) (by norm_num)
theorem B3189365 : Blo 992597 3189365 := bbase (se 5 (by rfl) ⟨149501, by rfl⟩ : syracuseStep 3189365 = 299003) (by norm_num)
theorem B2239109 : Blo 992597 2239109 := bbase (se 4 (by rfl) ⟨209916, by rfl⟩ : syracuseStep 2239109 = 419833) (by norm_num)
theorem B3353237 : Blo 992597 3353237 := bbase (se 6 (by rfl) ⟨78591, by rfl⟩ : syracuseStep 3353237 = 157183) (by norm_num)
theorem B2828965 : Blo 992597 2828965 := bbase (se 4 (by rfl) ⟨265215, by rfl⟩ : syracuseStep 2828965 = 530431) (by norm_num)
theorem B2239181 : Blo 992597 2239181 := bbase (se 3 (by rfl) ⟨419846, by rfl⟩ : syracuseStep 2239181 = 839693) (by norm_num)
theorem B2239253 : Blo 992597 2239253 := bbase (se 6 (by rfl) ⟨52482, by rfl⟩ : syracuseStep 2239253 = 104965) (by norm_num)
theorem B3189557 : Blo 992597 3189557 := bbase (se 5 (by rfl) ⟨149510, by rfl⟩ : syracuseStep 3189557 = 299021) (by norm_num)
theorem B2239325 : Blo 992597 2239325 := bbase (se 3 (by rfl) ⟨419873, by rfl⟩ : syracuseStep 2239325 = 839747) (by norm_num)
theorem B1256305 : Blo 992597 1256305 := bbase (se 2 (by rfl) ⟨471114, by rfl⟩ : syracuseStep 1256305 = 942229) (by norm_num)
theorem B2239397 : Blo 992597 2239397 := bbase (se 4 (by rfl) ⟨209943, by rfl⟩ : syracuseStep 2239397 = 419887) (by norm_num)
theorem B1256401 : Blo 992597 1256401 := bbase (se 2 (by rfl) ⟨471150, by rfl⟩ : syracuseStep 1256401 = 942301) (by norm_num)
theorem B2239469 : Blo 992597 2239469 := bbase (se 3 (by rfl) ⟨419900, by rfl⟩ : syracuseStep 2239469 = 839801) (by norm_num)
theorem B14363669 : Blo 992597 14363669 := bbase (se 6 (by rfl) ⟨336648, by rfl⟩ : syracuseStep 14363669 = 673297) (by norm_num)
theorem B2239541 : Blo 992597 2239541 := bbase (se 5 (by rfl) ⟨104978, by rfl⟩ : syracuseStep 2239541 = 209957) (by norm_num)
theorem B3353669 : Blo 992597 3353669 := bbase (se 4 (by rfl) ⟨314406, by rfl⟩ : syracuseStep 3353669 = 628813) (by norm_num)
theorem B1256573 : Blo 992597 1256573 := bbase (se 3 (by rfl) ⟨235607, by rfl⟩ : syracuseStep 1256573 = 471215) (by norm_num)
theorem B2239613 : Blo 992597 2239613 := bbase (se 3 (by rfl) ⟨419927, by rfl⟩ : syracuseStep 2239613 = 839855) (by norm_num)
theorem B1256629 : Blo 992597 1256629 := bbase (se 5 (by rfl) ⟨58904, by rfl⟩ : syracuseStep 1256629 = 117809) (by norm_num)
theorem B2239685 : Blo 992597 2239685 := bbase (se 4 (by rfl) ⟨209970, by rfl⟩ : syracuseStep 2239685 = 419941) (by norm_num)
theorem B2239757 : Blo 992597 2239757 := bbase (se 3 (by rfl) ⟨419954, by rfl⟩ : syracuseStep 2239757 = 839909) (by norm_num)
theorem B1256725 : Blo 992597 1256725 := bbase (se 6 (by rfl) ⟨29454, by rfl⟩ : syracuseStep 1256725 = 58909) (by norm_num)
theorem B5025077 : Blo 992597 5025077 := bbase (se 5 (by rfl) ⟨235550, by rfl⟩ : syracuseStep 5025077 = 471101) (by norm_num)
theorem B2239829 : Blo 992597 2239829 := bbase (se 11 (by rfl) ⟨1640, by rfl⟩ : syracuseStep 2239829 = 3281) (by norm_num)
theorem B2239901 : Blo 992597 2239901 := bbase (se 3 (by rfl) ⟨419981, by rfl⟩ : syracuseStep 2239901 = 839963) (by norm_num)
theorem B1256897 : Blo 992597 1256897 := bbase (se 2 (by rfl) ⟨471336, by rfl⟩ : syracuseStep 1256897 = 942673) (by norm_num)
theorem B5385685 : Blo 992597 5385685 := bbase (se 7 (by rfl) ⟨63113, by rfl⟩ : syracuseStep 5385685 = 126227) (by norm_num)
theorem B2239973 : Blo 992597 2239973 := bbase (se 4 (by rfl) ⟨209997, by rfl⟩ : syracuseStep 2239973 = 419995) (by norm_num)
theorem B3354101 : Blo 992597 3354101 := bbase (se 5 (by rfl) ⟨157223, by rfl⟩ : syracuseStep 3354101 = 314447) (by norm_num)
theorem B1256953 : Blo 992597 1256953 := bbase (se 2 (by rfl) ⟨471357, by rfl⟩ : syracuseStep 1256953 = 942715) (by norm_num)
theorem B15543829 : Blo 992597 15543829 := bbase (se 6 (by rfl) ⟨364308, by rfl⟩ : syracuseStep 15543829 = 728617) (by norm_num)
theorem B2240045 : Blo 992597 2240045 := bbase (se 3 (by rfl) ⟨420008, by rfl⟩ : syracuseStep 2240045 = 840017) (by norm_num)
theorem B1257049 : Blo 992597 1257049 := bbase (se 2 (by rfl) ⟨471393, by rfl⟩ : syracuseStep 1257049 = 942787) (by norm_num)
theorem B2240117 : Blo 992597 2240117 := bbase (se 5 (by rfl) ⟨105005, by rfl⟩ : syracuseStep 2240117 = 210011) (by norm_num)
theorem B3780229 : Blo 992597 3780229 := bbase (se 4 (by rfl) ⟨354396, by rfl⟩ : syracuseStep 3780229 = 708793) (by norm_num)
theorem B2240189 : Blo 992597 2240189 := bbase (se 3 (by rfl) ⟨420035, by rfl⟩ : syracuseStep 2240189 = 840071) (by norm_num)
theorem B2830069 : Blo 992597 2830069 := bbase (se 5 (by rfl) ⟨132659, by rfl⟩ : syracuseStep 2830069 = 265319) (by norm_num)
theorem B1257221 : Blo 992597 1257221 := bbase (se 4 (by rfl) ⟨117864, by rfl⟩ : syracuseStep 1257221 = 235729) (by norm_num)
theorem B2240261 : Blo 992597 2240261 := bbase (se 4 (by rfl) ⟨210024, by rfl⟩ : syracuseStep 2240261 = 420049) (by norm_num)
theorem B1060661 : Blo 992597 1060661 := bbase (se 5 (by rfl) ⟨49718, by rfl⟩ : syracuseStep 1060661 = 99437) (by norm_num)
theorem B1257277 : Blo 992597 1257277 := bbase (se 3 (by rfl) ⟨235739, by rfl⟩ : syracuseStep 1257277 = 471479) (by norm_num)
theorem B2240333 : Blo 992597 2240333 := bbase (se 3 (by rfl) ⟨420062, by rfl⟩ : syracuseStep 2240333 = 840125) (by norm_num)
theorem B2240405 : Blo 992597 2240405 := bbase (se 6 (by rfl) ⟨52509, by rfl⟩ : syracuseStep 2240405 = 105019) (by norm_num)
theorem B1257373 : Blo 992597 1257373 := bbase (se 3 (by rfl) ⟨235757, by rfl⟩ : syracuseStep 1257373 = 471515) (by norm_num)
theorem B3354533 : Blo 992597 3354533 := bbase (se 4 (by rfl) ⟨314487, by rfl⟩ : syracuseStep 3354533 = 628975) (by norm_num)
theorem B3780533 : Blo 992597 3780533 := bbase (se 5 (by rfl) ⟨177212, by rfl⟩ : syracuseStep 3780533 = 354425) (by norm_num)
theorem B2240477 : Blo 992597 2240477 := bbase (se 3 (by rfl) ⟨420089, by rfl⟩ : syracuseStep 2240477 = 840179) (by norm_num)
theorem B2240549 : Blo 992597 2240549 := bbase (se 4 (by rfl) ⟨210051, by rfl⟩ : syracuseStep 2240549 = 420103) (by norm_num)
theorem B1257545 : Blo 992597 1257545 := bbase (se 2 (by rfl) ⟨471579, by rfl⟩ : syracuseStep 1257545 = 943159) (by norm_num)
theorem B3584101 : Blo 992597 3584101 := bbase (se 4 (by rfl) ⟨336009, by rfl⟩ : syracuseStep 3584101 = 672019) (by norm_num)
theorem B2240621 : Blo 992597 2240621 := bbase (se 3 (by rfl) ⟨420116, by rfl⟩ : syracuseStep 2240621 = 840233) (by norm_num)
theorem B1257601 : Blo 992597 1257601 := bbase (se 2 (by rfl) ⟨471600, by rfl⟩ : syracuseStep 1257601 = 943201) (by norm_num)
theorem B2240693 : Blo 992597 2240693 := bbase (se 5 (by rfl) ⟨105032, by rfl⟩ : syracuseStep 2240693 = 210065) (by norm_num)
theorem B15282389 : Blo 992597 15282389 := bbase (se 7 (by rfl) ⟨179090, by rfl⟩ : syracuseStep 15282389 = 358181) (by norm_num)
theorem B1257697 : Blo 992597 1257697 := bbase (se 2 (by rfl) ⟨471636, by rfl⟩ : syracuseStep 1257697 = 943273) (by norm_num)
theorem B1061105 : Blo 992597 1061105 := bbase (se 2 (by rfl) ⟨397914, by rfl⟩ : syracuseStep 1061105 = 795829) (by norm_num)
theorem B2240765 : Blo 992597 2240765 := bbase (se 3 (by rfl) ⟨420143, by rfl⟩ : syracuseStep 2240765 = 840287) (by norm_num)
theorem B2240837 : Blo 992597 2240837 := bbase (se 4 (by rfl) ⟨210078, by rfl⟩ : syracuseStep 2240837 = 420157) (by norm_num)
theorem B3354965 : Blo 992597 3354965 := bbase (se 10 (by rfl) ⟨4914, by rfl⟩ : syracuseStep 3354965 = 9829) (by norm_num)
theorem B7647605 : Blo 992597 7647605 := bbase (se 5 (by rfl) ⟨358481, by rfl⟩ : syracuseStep 7647605 = 716963) (by norm_num)
theorem B1257869 : Blo 992597 1257869 := bbase (se 3 (by rfl) ⟨235850, by rfl⟩ : syracuseStep 1257869 = 471701) (by norm_num)
theorem B2240909 : Blo 992597 2240909 := bbase (se 3 (by rfl) ⟨420170, by rfl⟩ : syracuseStep 2240909 = 840341) (by norm_num)
theorem B1257925 : Blo 992597 1257925 := bbase (se 4 (by rfl) ⟨117930, by rfl⟩ : syracuseStep 1257925 = 235861) (by norm_num)
theorem B2240981 : Blo 992597 2240981 := bbase (se 7 (by rfl) ⟨26261, by rfl⟩ : syracuseStep 2240981 = 52523) (by norm_num)
theorem B1061353 : Blo 992597 1061353 := bbase (se 2 (by rfl) ⟨398007, by rfl⟩ : syracuseStep 1061353 = 796015) (by norm_num)
theorem B2241053 : Blo 992597 2241053 := bbase (se 3 (by rfl) ⟨420197, by rfl⟩ : syracuseStep 2241053 = 840395) (by norm_num)
theorem B1258021 : Blo 992597 1258021 := bbase (se 4 (by rfl) ⟨117939, by rfl⟩ : syracuseStep 1258021 = 235879) (by norm_num)
theorem B5026373 : Blo 992597 5026373 := bbase (se 4 (by rfl) ⟨471222, by rfl⟩ : syracuseStep 5026373 = 942445) (by norm_num)
theorem B2241125 : Blo 992597 2241125 := bbase (se 4 (by rfl) ⟨210105, by rfl⟩ : syracuseStep 2241125 = 420211) (by norm_num)
theorem B2241197 : Blo 992597 2241197 := bbase (se 3 (by rfl) ⟨420224, by rfl⟩ : syracuseStep 2241197 = 840449) (by norm_num)
theorem B1258193 : Blo 992597 1258193 := bbase (se 2 (by rfl) ⟨471822, by rfl⟩ : syracuseStep 1258193 = 943645) (by norm_num)
theorem B2241269 : Blo 992597 2241269 := bbase (se 5 (by rfl) ⟨105059, by rfl⟩ : syracuseStep 2241269 = 210119) (by norm_num)
theorem B3355397 : Blo 992597 3355397 := bbase (se 4 (by rfl) ⟨314568, by rfl⟩ : syracuseStep 3355397 = 629137) (by norm_num)
theorem B1258249 : Blo 992597 1258249 := bbase (se 2 (by rfl) ⟨471843, by rfl⟩ : syracuseStep 1258249 = 943687) (by norm_num)
theorem B2241341 : Blo 992597 2241341 := bbase (se 3 (by rfl) ⟨420251, by rfl⟩ : syracuseStep 2241341 = 840503) (by norm_num)
theorem B1258345 : Blo 992597 1258345 := bbase (se 2 (by rfl) ⟨471879, by rfl⟩ : syracuseStep 1258345 = 943759) (by norm_num)
theorem B2241413 : Blo 992597 2241413 := bbase (se 4 (by rfl) ⟨210132, by rfl⟩ : syracuseStep 2241413 = 420265) (by norm_num)
theorem B1061785 : Blo 992597 1061785 := bbase (se 2 (by rfl) ⟨398169, by rfl⟩ : syracuseStep 1061785 = 796339) (by norm_num)
theorem B2241485 : Blo 992597 2241485 := bbase (se 3 (by rfl) ⟨420278, by rfl⟩ : syracuseStep 2241485 = 840557) (by norm_num)
theorem B1061857 : Blo 992597 1061857 := bbase (se 2 (by rfl) ⟨398196, by rfl⟩ : syracuseStep 1061857 = 796393) (by norm_num)
theorem B1258517 : Blo 992597 1258517 := bbase (se 6 (by rfl) ⟨29496, by rfl⟩ : syracuseStep 1258517 = 58993) (by norm_num)
theorem B3027989 : Blo 992597 3027989 := bbase (se 6 (by rfl) ⟨70968, by rfl⟩ : syracuseStep 3027989 = 141937) (by norm_num)
theorem B2241557 : Blo 992597 2241557 := bbase (se 6 (by rfl) ⟨52536, by rfl⟩ : syracuseStep 2241557 = 105073) (by norm_num)
theorem B1258573 : Blo 992597 1258573 := bbase (se 3 (by rfl) ⟨235982, by rfl⟩ : syracuseStep 1258573 = 471965) (by norm_num)
theorem B2241629 : Blo 992597 2241629 := bbase (se 3 (by rfl) ⟨420305, by rfl⟩ : syracuseStep 2241629 = 840611) (by norm_num)
theorem B2241701 : Blo 992597 2241701 := bbase (se 4 (by rfl) ⟨210159, by rfl⟩ : syracuseStep 2241701 = 420319) (by norm_num)
theorem B1258669 : Blo 992597 1258669 := bbase (se 3 (by rfl) ⟨236000, by rfl⟩ : syracuseStep 1258669 = 472001) (by norm_num)
theorem B3355829 : Blo 992597 3355829 := bbase (se 5 (by rfl) ⟨157304, by rfl⟩ : syracuseStep 3355829 = 314609) (by norm_num)
theorem B2831573 : Blo 992597 2831573 := bbase (se 7 (by rfl) ⟨33182, by rfl⟩ : syracuseStep 2831573 = 66365) (by norm_num)
theorem B1193177 : Blo 992597 1193177 := bbase (se 2 (by rfl) ⟨447441, by rfl⟩ : syracuseStep 1193177 = 894883) (by norm_num)
theorem B2241773 : Blo 992597 2241773 := bbase (se 3 (by rfl) ⟨420332, by rfl⟩ : syracuseStep 2241773 = 840665) (by norm_num)
theorem B2241845 : Blo 992597 2241845 := bbase (se 5 (by rfl) ⟨105086, by rfl⟩ : syracuseStep 2241845 = 210173) (by norm_num)
theorem B1062229 : Blo 992597 1062229 := bbase (se 13 (by rfl) ⟨194, by rfl⟩ : syracuseStep 1062229 = 389) (by norm_num)
theorem B1258841 : Blo 992597 1258841 := bbase (se 2 (by rfl) ⟨472065, by rfl⟩ : syracuseStep 1258841 = 944131) (by norm_num)
theorem B2241917 : Blo 992597 2241917 := bbase (se 3 (by rfl) ⟨420359, by rfl⟩ : syracuseStep 2241917 = 840719) (by norm_num)
theorem B1258897 : Blo 992597 1258897 := bbase (se 2 (by rfl) ⟨472086, by rfl⟩ : syracuseStep 1258897 = 944173) (by norm_num)
theorem B2241989 : Blo 992597 2241989 := bbase (se 4 (by rfl) ⟨210186, by rfl⟩ : syracuseStep 2241989 = 420373) (by norm_num)
theorem B1258993 : Blo 992597 1258993 := bbase (se 2 (by rfl) ⟨472122, by rfl⟩ : syracuseStep 1258993 = 944245) (by norm_num)
theorem B2242061 : Blo 992597 2242061 := bbase (se 3 (by rfl) ⟨420386, by rfl⟩ : syracuseStep 2242061 = 840773) (by norm_num)
theorem B2242133 : Blo 992597 2242133 := bbase (se 8 (by rfl) ⟨13137, by rfl⟩ : syracuseStep 2242133 = 26275) (by norm_num)
theorem B3356261 : Blo 992597 3356261 := bbase (se 4 (by rfl) ⟨314649, by rfl⟩ : syracuseStep 3356261 = 629299) (by norm_num)
theorem B1259165 : Blo 992597 1259165 := bbase (se 3 (by rfl) ⟨236093, by rfl⟩ : syracuseStep 1259165 = 472187) (by norm_num)
theorem B2242205 : Blo 992597 2242205 := bbase (se 3 (by rfl) ⟨420413, by rfl⟩ : syracuseStep 2242205 = 840827) (by norm_num)
theorem B1062605 : Blo 992597 1062605 := bbase (se 3 (by rfl) ⟨199238, by rfl⟩ : syracuseStep 1062605 = 398477) (by norm_num)
theorem B1259221 : Blo 992597 1259221 := bbase (se 7 (by rfl) ⟨14756, by rfl⟩ : syracuseStep 1259221 = 29513) (by norm_num)
theorem B2242277 : Blo 992597 2242277 := bbase (se 4 (by rfl) ⟨210213, by rfl⟩ : syracuseStep 2242277 = 420427) (by norm_num)
theorem B1062677 : Blo 992597 1062677 := bbase (se 6 (by rfl) ⟨24906, by rfl⟩ : syracuseStep 1062677 = 49813) (by norm_num)
theorem B1259317 : Blo 992597 1259317 := bbase (se 5 (by rfl) ⟨59030, by rfl⟩ : syracuseStep 1259317 = 118061) (by norm_num)
theorem B5027669 : Blo 992597 5027669 := bbase (se 9 (by rfl) ⟨14729, by rfl⟩ : syracuseStep 5027669 = 29459) (by norm_num)
theorem B1193869 : Blo 992597 1193869 := bbase (se 3 (by rfl) ⟨223850, by rfl⟩ : syracuseStep 1193869 = 447701) (by norm_num)
theorem B1062865 : Blo 992597 1062865 := bbase (se 2 (by rfl) ⟨398574, by rfl⟩ : syracuseStep 1062865 = 797149) (by norm_num)
theorem B1259489 : Blo 992597 1259489 := bbase (se 2 (by rfl) ⟨472308, by rfl⟩ : syracuseStep 1259489 = 944617) (by norm_num)
theorem B3782645 : Blo 992597 3782645 := bbase (se 5 (by rfl) ⟨177311, by rfl⟩ : syracuseStep 3782645 = 354623) (by norm_num)
theorem B4241413 : Blo 992597 4241413 := bbase (se 4 (by rfl) ⟨397632, by rfl⟩ : syracuseStep 4241413 = 795265) (by norm_num)
theorem B1488917 : Blo 992597 1488917 := bbase (se 6 (by rfl) ⟨34896, by rfl⟩ : syracuseStep 1488917 = 69793) (by norm_num)
theorem B3356693 : Blo 992597 3356693 := bbase (se 6 (by rfl) ⟨78672, by rfl⟩ : syracuseStep 3356693 = 157345) (by norm_num)
theorem B8075285 : Blo 992597 8075285 := bbase (se 6 (by rfl) ⟨189264, by rfl⟩ : syracuseStep 8075285 = 378529) (by norm_num)
theorem B1259545 : Blo 992597 1259545 := bbase (se 2 (by rfl) ⟨472329, by rfl⟩ : syracuseStep 1259545 = 944659) (by norm_num)
theorem B1488941 : Blo 992597 1488941 := bbase (se 3 (by rfl) ⟨279176, by rfl⟩ : syracuseStep 1488941 = 558353) (by norm_num)
theorem B1488965 : Blo 992597 1488965 := bbase (se 4 (by rfl) ⟨139590, by rfl⟩ : syracuseStep 1488965 = 279181) (by norm_num)
theorem B3586133 : Blo 992597 3586133 := bbase (se 8 (by rfl) ⟨21012, by rfl⟩ : syracuseStep 3586133 = 42025) (by norm_num)
theorem B1488989 : Blo 992597 1488989 := bbase (se 3 (by rfl) ⟨279185, by rfl⟩ : syracuseStep 1488989 = 558371) (by norm_num)
theorem B1194085 : Blo 992597 1194085 := bbase (se 4 (by rfl) ⟨111945, by rfl⟩ : syracuseStep 1194085 = 223891) (by norm_num)
theorem B1489013 : Blo 992597 1489013 := bbase (se 5 (by rfl) ⟨69797, by rfl⟩ : syracuseStep 1489013 = 139595) (by norm_num)
theorem B1259641 : Blo 992597 1259641 := bbase (se 2 (by rfl) ⟨472365, by rfl⟩ : syracuseStep 1259641 = 944731) (by norm_num)
theorem B1063049 : Blo 992597 1063049 := bbase (se 2 (by rfl) ⟨398643, by rfl⟩ : syracuseStep 1063049 = 797287) (by norm_num)
theorem B1489037 : Blo 992597 1489037 := bbase (se 3 (by rfl) ⟨279194, by rfl⟩ : syracuseStep 1489037 = 558389) (by norm_num)
theorem B1489061 : Blo 992597 1489061 := bbase (se 4 (by rfl) ⟨139599, by rfl⟩ : syracuseStep 1489061 = 279199) (by norm_num)
theorem B1489085 : Blo 992597 1489085 := bbase (se 3 (by rfl) ⟨279203, by rfl⟩ : syracuseStep 1489085 = 558407) (by norm_num)
theorem B2013373 : Blo 992597 2013373 := bbase (se 3 (by rfl) ⟨377507, by rfl⟩ : syracuseStep 2013373 = 755015) (by norm_num)
theorem B1489109 : Blo 992597 1489109 := bbase (se 7 (by rfl) ⟨17450, by rfl⟩ : syracuseStep 1489109 = 34901) (by norm_num)
theorem B1489133 : Blo 992597 1489133 := bbase (se 3 (by rfl) ⟨279212, by rfl⟩ : syracuseStep 1489133 = 558425) (by norm_num)
theorem B1489157 : Blo 992597 1489157 := bbase (se 4 (by rfl) ⟨139608, by rfl⟩ : syracuseStep 1489157 = 279217) (by norm_num)
theorem B3782933 : Blo 992597 3782933 := bbase (se 6 (by rfl) ⟨88662, by rfl⟩ : syracuseStep 3782933 = 177325) (by norm_num)
theorem B1489181 : Blo 992597 1489181 := bbase (se 3 (by rfl) ⟨279221, by rfl⟩ : syracuseStep 1489181 = 558443) (by norm_num)
theorem B1259813 : Blo 992597 1259813 := bbase (se 4 (by rfl) ⟨118107, by rfl⟩ : syracuseStep 1259813 = 236215) (by norm_num)
theorem B1489205 : Blo 992597 1489205 := bbase (se 5 (by rfl) ⟨69806, by rfl⟩ : syracuseStep 1489205 = 139613) (by norm_num)
theorem B1489229 : Blo 992597 1489229 := bbase (se 3 (by rfl) ⟨279230, by rfl⟩ : syracuseStep 1489229 = 558461) (by norm_num)
theorem B1259869 : Blo 992597 1259869 := bbase (se 3 (by rfl) ⟨236225, by rfl⟩ : syracuseStep 1259869 = 472451) (by norm_num)
theorem B1489253 : Blo 992597 1489253 := bbase (se 4 (by rfl) ⟨139617, by rfl⟩ : syracuseStep 1489253 = 279235) (by norm_num)
theorem B1489277 : Blo 992597 1489277 := bbase (se 3 (by rfl) ⟨279239, by rfl⟩ : syracuseStep 1489277 = 558479) (by norm_num)
theorem B1489301 : Blo 992597 1489301 := bbase (se 6 (by rfl) ⟨34905, by rfl⟩ : syracuseStep 1489301 = 69811) (by norm_num)
theorem B1489325 : Blo 992597 1489325 := bbase (se 3 (by rfl) ⟨279248, by rfl⟩ : syracuseStep 1489325 = 558497) (by norm_num)
theorem B1259965 : Blo 992597 1259965 := bbase (se 3 (by rfl) ⟨236243, by rfl⟩ : syracuseStep 1259965 = 472487) (by norm_num)
theorem B1489349 : Blo 992597 1489349 := bbase (se 4 (by rfl) ⟨139626, by rfl⟩ : syracuseStep 1489349 = 279253) (by norm_num)
theorem B3357125 : Blo 992597 3357125 := bbase (se 4 (by rfl) ⟨314730, by rfl⟩ : syracuseStep 3357125 = 629461) (by norm_num)
theorem B1489373 : Blo 992597 1489373 := bbase (se 3 (by rfl) ⟨279257, by rfl⟩ : syracuseStep 1489373 = 558515) (by norm_num)
theorem B1489397 : Blo 992597 1489397 := bbase (se 5 (by rfl) ⟨69815, by rfl⟩ : syracuseStep 1489397 = 139631) (by norm_num)
theorem B1489421 : Blo 992597 1489421 := bbase (se 3 (by rfl) ⟨279266, by rfl⟩ : syracuseStep 1489421 = 558533) (by norm_num)
theorem B1489445 : Blo 992597 1489445 := bbase (se 4 (by rfl) ⟨139635, by rfl⟩ : syracuseStep 1489445 = 279271) (by norm_num)
theorem B1489469 : Blo 992597 1489469 := bbase (se 3 (by rfl) ⟨279275, by rfl⟩ : syracuseStep 1489469 = 558551) (by norm_num)
theorem B1489493 : Blo 992597 1489493 := bbase (se 8 (by rfl) ⟨8727, by rfl⟩ : syracuseStep 1489493 = 17455) (by norm_num)
theorem B4536917 : Blo 992597 4536917 := bbase (se 8 (by rfl) ⟨26583, by rfl⟩ : syracuseStep 4536917 = 53167) (by norm_num)
theorem B1260137 : Blo 992597 1260137 := bbase (se 2 (by rfl) ⟨472551, by rfl⟩ : syracuseStep 1260137 = 945103) (by norm_num)
theorem B1489517 : Blo 992597 1489517 := bbase (se 3 (by rfl) ⟨279284, by rfl⟩ : syracuseStep 1489517 = 558569) (by norm_num)
theorem B1489541 : Blo 992597 1489541 := bbase (se 4 (by rfl) ⟨139644, by rfl⟩ : syracuseStep 1489541 = 279289) (by norm_num)
theorem B1489565 : Blo 992597 1489565 := bbase (se 3 (by rfl) ⟨279293, by rfl⟩ : syracuseStep 1489565 = 558587) (by norm_num)
theorem B1260193 : Blo 992597 1260193 := bbase (se 2 (by rfl) ⟨472572, by rfl⟩ : syracuseStep 1260193 = 945145) (by norm_num)
theorem B1489589 : Blo 992597 1489589 := bbase (se 5 (by rfl) ⟨69824, by rfl⟩ : syracuseStep 1489589 = 139649) (by norm_num)
theorem B1489613 : Blo 992597 1489613 := bbase (se 3 (by rfl) ⟨279302, by rfl⟩ : syracuseStep 1489613 = 558605) (by norm_num)
theorem B1489637 : Blo 992597 1489637 := bbase (se 4 (by rfl) ⟨139653, by rfl⟩ : syracuseStep 1489637 = 279307) (by norm_num)
theorem B1489661 : Blo 992597 1489661 := bbase (se 3 (by rfl) ⟨279311, by rfl⟩ : syracuseStep 1489661 = 558623) (by norm_num)
theorem B1260289 : Blo 992597 1260289 := bbase (se 2 (by rfl) ⟨472608, by rfl⟩ : syracuseStep 1260289 = 945217) (by norm_num)
theorem B2833157 : Blo 992597 2833157 := bbase (se 4 (by rfl) ⟨265608, by rfl⟩ : syracuseStep 2833157 = 531217) (by norm_num)
theorem B1489685 : Blo 992597 1489685 := bbase (se 6 (by rfl) ⟨34914, by rfl⟩ : syracuseStep 1489685 = 69829) (by norm_num)
theorem B1489709 : Blo 992597 1489709 := bbase (se 3 (by rfl) ⟨279320, by rfl⟩ : syracuseStep 1489709 = 558641) (by norm_num)
theorem B1489733 : Blo 992597 1489733 := bbase (se 4 (by rfl) ⟨139662, by rfl⟩ : syracuseStep 1489733 = 279325) (by norm_num)
theorem B1489757 : Blo 992597 1489757 := bbase (se 3 (by rfl) ⟨279329, by rfl⟩ : syracuseStep 1489757 = 558659) (by norm_num)
theorem B1489781 : Blo 992597 1489781 := bbase (se 5 (by rfl) ⟨69833, by rfl⟩ : syracuseStep 1489781 = 139667) (by norm_num)
theorem B3357557 : Blo 992597 3357557 := bbase (se 5 (by rfl) ⟨157385, by rfl⟩ : syracuseStep 3357557 = 314771) (by norm_num)
theorem B1063801 : Blo 992597 1063801 := bbase (se 2 (by rfl) ⟨398925, by rfl⟩ : syracuseStep 1063801 = 797851) (by norm_num)
theorem B1489805 : Blo 992597 1489805 := bbase (se 3 (by rfl) ⟨279338, by rfl⟩ : syracuseStep 1489805 = 558677) (by norm_num)
theorem B1489829 : Blo 992597 1489829 := bbase (se 4 (by rfl) ⟨139671, by rfl⟩ : syracuseStep 1489829 = 279343) (by norm_num)
theorem B1260461 : Blo 992597 1260461 := bbase (se 3 (by rfl) ⟨236336, by rfl⟩ : syracuseStep 1260461 = 472673) (by norm_num)
theorem B3586997 : Blo 992597 3586997 := bbase (se 5 (by rfl) ⟨168140, by rfl⟩ : syracuseStep 3586997 = 336281) (by norm_num)
theorem B1489853 : Blo 992597 1489853 := bbase (se 3 (by rfl) ⟨279347, by rfl⟩ : syracuseStep 1489853 = 558695) (by norm_num)
theorem B1063873 : Blo 992597 1063873 := bbase (se 2 (by rfl) ⟨398952, by rfl⟩ : syracuseStep 1063873 = 797905) (by norm_num)
theorem B1489877 : Blo 992597 1489877 := bbase (se 7 (by rfl) ⟨17459, by rfl⟩ : syracuseStep 1489877 = 34919) (by norm_num)
theorem B1260517 : Blo 992597 1260517 := bbase (se 4 (by rfl) ⟨118173, by rfl⟩ : syracuseStep 1260517 = 236347) (by norm_num)
theorem B1489901 : Blo 992597 1489901 := bbase (se 3 (by rfl) ⟨279356, by rfl⟩ : syracuseStep 1489901 = 558713) (by norm_num)
theorem B1293301 : Blo 992597 1293301 := bbase (se 5 (by rfl) ⟨60623, by rfl⟩ : syracuseStep 1293301 = 121247) (by norm_num)
theorem B1489925 : Blo 992597 1489925 := bbase (se 4 (by rfl) ⟨139680, by rfl⟩ : syracuseStep 1489925 = 279361) (by norm_num)
theorem B1489949 : Blo 992597 1489949 := bbase (se 3 (by rfl) ⟨279365, by rfl⟩ : syracuseStep 1489949 = 558731) (by norm_num)
theorem B1489973 : Blo 992597 1489973 := bbase (se 5 (by rfl) ⟨69842, by rfl⟩ : syracuseStep 1489973 = 139685) (by norm_num)
theorem B1260613 : Blo 992597 1260613 := bbase (se 4 (by rfl) ⟨118182, by rfl⟩ : syracuseStep 1260613 = 236365) (by norm_num)
theorem B1489997 : Blo 992597 1489997 := bbase (se 3 (by rfl) ⟨279374, by rfl⟩ : syracuseStep 1489997 = 558749) (by norm_num)
theorem B1490021 : Blo 992597 1490021 := bbase (se 4 (by rfl) ⟨139689, by rfl⟩ : syracuseStep 1490021 = 279379) (by norm_num)
theorem B5028965 : Blo 992597 5028965 := bbase (se 4 (by rfl) ⟨471465, by rfl⟩ : syracuseStep 5028965 = 942931) (by norm_num)
theorem B1064053 : Blo 992597 1064053 := bbase (se 5 (by rfl) ⟨49877, by rfl⟩ : syracuseStep 1064053 = 99755) (by norm_num)
theorem B1490045 : Blo 992597 1490045 := bbase (se 3 (by rfl) ⟨279383, by rfl⟩ : syracuseStep 1490045 = 558767) (by norm_num)
theorem B1490069 : Blo 992597 1490069 := bbase (se 6 (by rfl) ⟨34923, by rfl⟩ : syracuseStep 1490069 = 69847) (by norm_num)
theorem B1490093 : Blo 992597 1490093 := bbase (se 3 (by rfl) ⟨279392, by rfl⟩ : syracuseStep 1490093 = 558785) (by norm_num)
theorem B1490117 : Blo 992597 1490117 := bbase (se 4 (by rfl) ⟨139698, by rfl⟩ : syracuseStep 1490117 = 279397) (by norm_num)
theorem B1490141 : Blo 992597 1490141 := bbase (se 3 (by rfl) ⟨279401, by rfl⟩ : syracuseStep 1490141 = 558803) (by norm_num)
theorem B1260785 : Blo 992597 1260785 := bbase (se 2 (by rfl) ⟨472794, by rfl⟩ : syracuseStep 1260785 = 945589) (by norm_num)
theorem B1490165 : Blo 992597 1490165 := bbase (se 5 (by rfl) ⟨69851, by rfl⟩ : syracuseStep 1490165 = 139703) (by norm_num)
theorem B1490189 : Blo 992597 1490189 := bbase (se 3 (by rfl) ⟨279410, by rfl⟩ : syracuseStep 1490189 = 558821) (by norm_num)
theorem B1490213 : Blo 992597 1490213 := bbase (se 4 (by rfl) ⟨139707, by rfl⟩ : syracuseStep 1490213 = 279415) (by norm_num)
theorem B3357989 : Blo 992597 3357989 := bbase (se 4 (by rfl) ⟨314811, by rfl⟩ : syracuseStep 3357989 = 629623) (by norm_num)
theorem B1260841 : Blo 992597 1260841 := bbase (se 2 (by rfl) ⟨472815, by rfl⟩ : syracuseStep 1260841 = 945631) (by norm_num)
theorem B1490237 : Blo 992597 1490237 := bbase (se 3 (by rfl) ⟨279419, by rfl⟩ : syracuseStep 1490237 = 558839) (by norm_num)
theorem B1490261 : Blo 992597 1490261 := bbase (se 11 (by rfl) ⟨1091, by rfl⟩ : syracuseStep 1490261 = 2183) (by norm_num)
theorem B1490285 : Blo 992597 1490285 := bbase (se 3 (by rfl) ⟨279428, by rfl⟩ : syracuseStep 1490285 = 558857) (by norm_num)
theorem B1490309 : Blo 992597 1490309 := bbase (se 4 (by rfl) ⟨139716, by rfl⟩ : syracuseStep 1490309 = 279433) (by norm_num)
theorem B1260937 : Blo 992597 1260937 := bbase (se 2 (by rfl) ⟨472851, by rfl⟩ : syracuseStep 1260937 = 945703) (by norm_num)
theorem B1490333 : Blo 992597 1490333 := bbase (se 3 (by rfl) ⟨279437, by rfl⟩ : syracuseStep 1490333 = 558875) (by norm_num)
theorem B2833829 : Blo 992597 2833829 := bbase (se 4 (by rfl) ⟨265671, by rfl⟩ : syracuseStep 2833829 = 531343) (by norm_num)
theorem B2014637 : Blo 992597 2014637 := bbase (se 3 (by rfl) ⟨377744, by rfl⟩ : syracuseStep 2014637 = 755489) (by norm_num)
theorem B1490357 : Blo 992597 1490357 := bbase (se 5 (by rfl) ⟨69860, by rfl⟩ : syracuseStep 1490357 = 139721) (by norm_num)
theorem B1490381 : Blo 992597 1490381 := bbase (se 3 (by rfl) ⟨279446, by rfl⟩ : syracuseStep 1490381 = 558893) (by norm_num)
theorem B4242901 : Blo 992597 4242901 := bbase (se 7 (by rfl) ⟨49721, by rfl⟩ : syracuseStep 4242901 = 99443) (by norm_num)
theorem B4242917 : Blo 992597 4242917 := bbase (se 4 (by rfl) ⟨397773, by rfl⟩ : syracuseStep 4242917 = 795547) (by norm_num)
theorem B1490405 : Blo 992597 1490405 := bbase (se 4 (by rfl) ⟨139725, by rfl⟩ : syracuseStep 1490405 = 279451) (by norm_num)
theorem B1490429 : Blo 992597 1490429 := bbase (se 3 (by rfl) ⟨279455, by rfl⟩ : syracuseStep 1490429 = 558911) (by norm_num)
theorem B1490453 : Blo 992597 1490453 := bbase (se 6 (by rfl) ⟨34932, by rfl⟩ : syracuseStep 1490453 = 69865) (by norm_num)
theorem B1490477 : Blo 992597 1490477 := bbase (se 3 (by rfl) ⟨279464, by rfl⟩ : syracuseStep 1490477 = 558929) (by norm_num)
theorem B1261109 : Blo 992597 1261109 := bbase (se 5 (by rfl) ⟨59114, by rfl⟩ : syracuseStep 1261109 = 118229) (by norm_num)
theorem B1490501 : Blo 992597 1490501 := bbase (se 4 (by rfl) ⟨139734, by rfl⟩ : syracuseStep 1490501 = 279469) (by norm_num)
theorem B1490525 : Blo 992597 1490525 := bbase (se 3 (by rfl) ⟨279473, by rfl⟩ : syracuseStep 1490525 = 558947) (by norm_num)
theorem B1261165 : Blo 992597 1261165 := bbase (se 3 (by rfl) ⟨236468, by rfl⟩ : syracuseStep 1261165 = 472937) (by norm_num)
theorem B1490549 : Blo 992597 1490549 := bbase (se 5 (by rfl) ⟨69869, by rfl⟩ : syracuseStep 1490549 = 139739) (by norm_num)
theorem B1490573 : Blo 992597 1490573 := bbase (se 3 (by rfl) ⟨279482, by rfl⟩ : syracuseStep 1490573 = 558965) (by norm_num)
theorem B1490597 : Blo 992597 1490597 := bbase (se 4 (by rfl) ⟨139743, by rfl⟩ : syracuseStep 1490597 = 279487) (by norm_num)
theorem B1916581 : Blo 992597 1916581 := bbase (se 4 (by rfl) ⟨179679, by rfl⟩ : syracuseStep 1916581 = 359359) (by norm_num)
theorem B1490621 : Blo 992597 1490621 := bbase (se 3 (by rfl) ⟨279491, by rfl⟩ : syracuseStep 1490621 = 558983) (by norm_num)
theorem B1261261 : Blo 992597 1261261 := bbase (se 3 (by rfl) ⟨236486, by rfl⟩ : syracuseStep 1261261 = 472973) (by norm_num)
theorem B1490645 : Blo 992597 1490645 := bbase (se 7 (by rfl) ⟨17468, by rfl⟩ : syracuseStep 1490645 = 34937) (by norm_num)
theorem B3358421 : Blo 992597 3358421 := bbase (se 7 (by rfl) ⟨39356, by rfl⟩ : syracuseStep 3358421 = 78713) (by norm_num)
theorem B1490669 : Blo 992597 1490669 := bbase (se 3 (by rfl) ⟨279500, by rfl⟩ : syracuseStep 1490669 = 559001) (by norm_num)
theorem B1490693 : Blo 992597 1490693 := bbase (se 4 (by rfl) ⟨139752, by rfl⟩ : syracuseStep 1490693 = 279505) (by norm_num)
theorem B1195781 : Blo 992597 1195781 := bbase (se 4 (by rfl) ⟨112104, by rfl⟩ : syracuseStep 1195781 = 224209) (by norm_num)
theorem B1490717 : Blo 992597 1490717 := bbase (se 3 (by rfl) ⟨279509, by rfl⟩ : syracuseStep 1490717 = 559019) (by norm_num)
theorem B1490741 : Blo 992597 1490741 := bbase (se 5 (by rfl) ⟨69878, by rfl⟩ : syracuseStep 1490741 = 139757) (by norm_num)
theorem B1490765 : Blo 992597 1490765 := bbase (se 3 (by rfl) ⟨279518, by rfl⟩ : syracuseStep 1490765 = 559037) (by norm_num)
theorem B2834261 : Blo 992597 2834261 := bbase (se 9 (by rfl) ⟨8303, by rfl⟩ : syracuseStep 2834261 = 16607) (by norm_num)
theorem B1490789 : Blo 992597 1490789 := bbase (se 4 (by rfl) ⟨139761, by rfl⟩ : syracuseStep 1490789 = 279523) (by norm_num)
theorem B1490813 : Blo 992597 1490813 := bbase (se 3 (by rfl) ⟨279527, by rfl⟩ : syracuseStep 1490813 = 559055) (by norm_num)
theorem B1490837 : Blo 992597 1490837 := bbase (se 6 (by rfl) ⟨34941, by rfl⟩ : syracuseStep 1490837 = 69883) (by norm_num)
theorem B1490861 : Blo 992597 1490861 := bbase (se 3 (by rfl) ⟨279536, by rfl⟩ : syracuseStep 1490861 = 559073) (by norm_num)
theorem B1490885 : Blo 992597 1490885 := bbase (se 4 (by rfl) ⟨139770, by rfl⟩ : syracuseStep 1490885 = 279541) (by norm_num)
theorem B2015189 : Blo 992597 2015189 := bbase (se 7 (by rfl) ⟨23615, by rfl⟩ : syracuseStep 2015189 = 47231) (by norm_num)
theorem B1195993 : Blo 992597 1195993 := bbase (se 2 (by rfl) ⟨448497, by rfl⟩ : syracuseStep 1195993 = 896995) (by norm_num)
theorem B1490909 : Blo 992597 1490909 := bbase (se 3 (by rfl) ⟨279545, by rfl⟩ : syracuseStep 1490909 = 559091) (by norm_num)
theorem B1490933 : Blo 992597 1490933 := bbase (se 5 (by rfl) ⟨69887, by rfl⟩ : syracuseStep 1490933 = 139775) (by norm_num)
theorem B2015221 : Blo 992597 2015221 := bbase (se 5 (by rfl) ⟨94463, by rfl⟩ : syracuseStep 2015221 = 188927) (by norm_num)
theorem B1490957 : Blo 992597 1490957 := bbase (se 3 (by rfl) ⟨279554, by rfl⟩ : syracuseStep 1490957 = 559109) (by norm_num)
theorem B6373397 : Blo 992597 6373397 := bbase (se 6 (by rfl) ⟨149376, by rfl⟩ : syracuseStep 6373397 = 298753) (by norm_num)
theorem B1490981 : Blo 992597 1490981 := bbase (se 4 (by rfl) ⟨139779, by rfl⟩ : syracuseStep 1490981 = 279559) (by norm_num)
theorem B1491005 : Blo 992597 1491005 := bbase (se 3 (by rfl) ⟨279563, by rfl⟩ : syracuseStep 1491005 = 559127) (by norm_num)
theorem B1491029 : Blo 992597 1491029 := bbase (se 8 (by rfl) ⟨8736, by rfl⟩ : syracuseStep 1491029 = 17473) (by norm_num)
theorem B1196137 : Blo 992597 1196137 := bbase (se 2 (by rfl) ⟨448551, by rfl⟩ : syracuseStep 1196137 = 897103) (by norm_num)
theorem B1491053 : Blo 992597 1491053 := bbase (se 3 (by rfl) ⟨279572, by rfl⟩ : syracuseStep 1491053 = 559145) (by norm_num)
theorem B1491077 : Blo 992597 1491077 := bbase (se 4 (by rfl) ⟨139788, by rfl⟩ : syracuseStep 1491077 = 279577) (by norm_num)
theorem B3358853 : Blo 992597 3358853 := bbase (se 4 (by rfl) ⟨314892, by rfl⟩ : syracuseStep 3358853 = 629785) (by norm_num)
theorem B1491101 : Blo 992597 1491101 := bbase (se 3 (by rfl) ⟨279581, by rfl⟩ : syracuseStep 1491101 = 559163) (by norm_num)
theorem B1491125 : Blo 992597 1491125 := bbase (se 5 (by rfl) ⟨69896, by rfl⟩ : syracuseStep 1491125 = 139793) (by norm_num)
theorem B1491149 : Blo 992597 1491149 := bbase (se 3 (by rfl) ⟨279590, by rfl⟩ : syracuseStep 1491149 = 559181) (by norm_num)
theorem B1491173 : Blo 992597 1491173 := bbase (se 4 (by rfl) ⟨139797, by rfl⟩ : syracuseStep 1491173 = 279595) (by norm_num)
theorem B1884397 : Blo 992597 1884397 := bbase (se 3 (by rfl) ⟨353324, by rfl⟩ : syracuseStep 1884397 = 706649) (by norm_num)
theorem B1491197 : Blo 992597 1491197 := bbase (se 3 (by rfl) ⟨279599, by rfl⟩ : syracuseStep 1491197 = 559199) (by norm_num)
theorem B1491221 : Blo 992597 1491221 := bbase (se 6 (by rfl) ⟨34950, by rfl⟩ : syracuseStep 1491221 = 69901) (by norm_num)
theorem B1491245 : Blo 992597 1491245 := bbase (se 3 (by rfl) ⟨279608, by rfl⟩ : syracuseStep 1491245 = 559217) (by norm_num)
theorem B1491269 : Blo 992597 1491269 := bbase (se 4 (by rfl) ⟨139806, by rfl⟩ : syracuseStep 1491269 = 279613) (by norm_num)
theorem B1491293 : Blo 992597 1491293 := bbase (se 3 (by rfl) ⟨279617, by rfl⟩ : syracuseStep 1491293 = 559235) (by norm_num)
theorem B5030261 : Blo 992597 5030261 := bbase (se 5 (by rfl) ⟨235793, by rfl⟩ : syracuseStep 5030261 = 471587) (by norm_num)
theorem B1491317 : Blo 992597 1491317 := bbase (se 5 (by rfl) ⟨69905, by rfl⟩ : syracuseStep 1491317 = 139811) (by norm_num)
theorem B1884541 : Blo 992597 1884541 := bbase (se 3 (by rfl) ⟨353351, by rfl⟩ : syracuseStep 1884541 = 706703) (by norm_num)
theorem B1491341 : Blo 992597 1491341 := bbase (se 3 (by rfl) ⟨279626, by rfl⟩ : syracuseStep 1491341 = 559253) (by norm_num)
theorem B1491365 : Blo 992597 1491365 := bbase (se 4 (by rfl) ⟨139815, by rfl⟩ : syracuseStep 1491365 = 279631) (by norm_num)
theorem B1491389 : Blo 992597 1491389 := bbase (se 3 (by rfl) ⟨279635, by rfl⟩ : syracuseStep 1491389 = 559271) (by norm_num)
theorem B1491413 : Blo 992597 1491413 := bbase (se 7 (by rfl) ⟨17477, by rfl⟩ : syracuseStep 1491413 = 34955) (by norm_num)
theorem B1819109 : Blo 992597 1819109 := bbase (se 4 (by rfl) ⟨170541, by rfl⟩ : syracuseStep 1819109 = 341083) (by norm_num)
theorem B1491437 : Blo 992597 1491437 := bbase (se 3 (by rfl) ⟨279644, by rfl⟩ : syracuseStep 1491437 = 559289) (by norm_num)
theorem B1491461 : Blo 992597 1491461 := bbase (se 4 (by rfl) ⟨139824, by rfl⟩ : syracuseStep 1491461 = 279649) (by norm_num)
theorem B1884701 : Blo 992597 1884701 := bbase (se 3 (by rfl) ⟨353381, by rfl⟩ : syracuseStep 1884701 = 706763) (by norm_num)
theorem B1491485 : Blo 992597 1491485 := bbase (se 3 (by rfl) ⟨279653, by rfl⟩ : syracuseStep 1491485 = 559307) (by norm_num)
theorem B1491509 : Blo 992597 1491509 := bbase (se 5 (by rfl) ⟨69914, by rfl⟩ : syracuseStep 1491509 = 139829) (by norm_num)
theorem B3359285 : Blo 992597 3359285 := bbase (se 5 (by rfl) ⟨157466, by rfl⟩ : syracuseStep 3359285 = 314933) (by norm_num)
theorem B3883589 : Blo 992597 3883589 := bbase (se 4 (by rfl) ⟨364086, by rfl⟩ : syracuseStep 3883589 = 728173) (by norm_num)
theorem B2835013 : Blo 992597 2835013 := bbase (se 4 (by rfl) ⟨265782, by rfl⟩ : syracuseStep 2835013 = 531565) (by norm_num)
theorem B1491533 : Blo 992597 1491533 := bbase (se 3 (by rfl) ⟨279662, by rfl⟩ : syracuseStep 1491533 = 559325) (by norm_num)
theorem B1491557 : Blo 992597 1491557 := bbase (se 4 (by rfl) ⟨139833, by rfl⟩ : syracuseStep 1491557 = 279667) (by norm_num)
theorem B1491581 : Blo 992597 1491581 := bbase (se 3 (by rfl) ⟨279671, by rfl⟩ : syracuseStep 1491581 = 559343) (by norm_num)
theorem B1491605 : Blo 992597 1491605 := bbase (se 6 (by rfl) ⟨34959, by rfl⟩ : syracuseStep 1491605 = 69919) (by norm_num)
theorem B1884845 : Blo 992597 1884845 := bbase (se 3 (by rfl) ⟨353408, by rfl⟩ : syracuseStep 1884845 = 706817) (by norm_num)
theorem B1491629 : Blo 992597 1491629 := bbase (se 3 (by rfl) ⟨279680, by rfl⟩ : syracuseStep 1491629 = 559361) (by norm_num)
theorem B7160501 : Blo 992597 7160501 := bbase (se 5 (by rfl) ⟨335648, by rfl⟩ : syracuseStep 7160501 = 671297) (by norm_num)
theorem B1491653 : Blo 992597 1491653 := bbase (se 4 (by rfl) ⟨139842, by rfl⟩ : syracuseStep 1491653 = 279685) (by norm_num)
theorem B1491677 : Blo 992597 1491677 := bbase (se 3 (by rfl) ⟨279689, by rfl⟩ : syracuseStep 1491677 = 559379) (by norm_num)
theorem B1491701 : Blo 992597 1491701 := bbase (se 5 (by rfl) ⟨69923, by rfl⟩ : syracuseStep 1491701 = 139847) (by norm_num)
theorem B1491725 : Blo 992597 1491725 := bbase (se 3 (by rfl) ⟨279698, by rfl⟩ : syracuseStep 1491725 = 559397) (by norm_num)
theorem B1491749 : Blo 992597 1491749 := bbase (se 4 (by rfl) ⟨139851, by rfl⟩ : syracuseStep 1491749 = 279703) (by norm_num)
theorem B1491773 : Blo 992597 1491773 := bbase (se 3 (by rfl) ⟨279707, by rfl⟩ : syracuseStep 1491773 = 559415) (by norm_num)
theorem B1491797 : Blo 992597 1491797 := bbase (se 9 (by rfl) ⟨4370, by rfl⟩ : syracuseStep 1491797 = 8741) (by norm_num)
theorem B8504149 : Blo 992597 8504149 := bbase (se 9 (by rfl) ⟨24914, by rfl⟩ : syracuseStep 8504149 = 49829) (by norm_num)
theorem B1491821 : Blo 992597 1491821 := bbase (se 3 (by rfl) ⟨279716, by rfl⟩ : syracuseStep 1491821 = 559433) (by norm_num)
theorem B1491845 : Blo 992597 1491845 := bbase (se 4 (by rfl) ⟨139860, by rfl⟩ : syracuseStep 1491845 = 279721) (by norm_num)
theorem B1295237 : Blo 992597 1295237 := bbase (se 4 (by rfl) ⟨121428, by rfl⟩ : syracuseStep 1295237 = 242857) (by norm_num)
theorem B1491869 : Blo 992597 1491869 := bbase (se 3 (by rfl) ⟨279725, by rfl⟩ : syracuseStep 1491869 = 559451) (by norm_num)
theorem B1590197 : Blo 992597 1590197 := bbase (se 5 (by rfl) ⟨74540, by rfl⟩ : syracuseStep 1590197 = 149081) (by norm_num)
theorem B1491893 : Blo 992597 1491893 := bbase (se 5 (by rfl) ⟨69932, by rfl⟩ : syracuseStep 1491893 = 139865) (by norm_num)
theorem B1885133 : Blo 992597 1885133 := bbase (se 3 (by rfl) ⟨353462, by rfl⟩ : syracuseStep 1885133 = 706925) (by norm_num)
theorem B1491917 : Blo 992597 1491917 := bbase (se 3 (by rfl) ⟨279734, by rfl⟩ : syracuseStep 1491917 = 559469) (by norm_num)
theorem B1491941 : Blo 992597 1491941 := bbase (se 4 (by rfl) ⟨139869, by rfl⟩ : syracuseStep 1491941 = 279739) (by norm_num)
theorem B3359717 : Blo 992597 3359717 := bbase (se 4 (by rfl) ⟨314973, by rfl⟩ : syracuseStep 3359717 = 629947) (by norm_num)
theorem B1491965 : Blo 992597 1491965 := bbase (se 3 (by rfl) ⟨279743, by rfl⟩ : syracuseStep 1491965 = 559487) (by norm_num)
theorem B1491989 : Blo 992597 1491989 := bbase (se 6 (by rfl) ⟨34968, by rfl⟩ : syracuseStep 1491989 = 69937) (by norm_num)
theorem B1492013 : Blo 992597 1492013 := bbase (se 3 (by rfl) ⟨279752, by rfl⟩ : syracuseStep 1492013 = 559505) (by norm_num)
theorem B1492037 : Blo 992597 1492037 := bbase (se 4 (by rfl) ⟨139878, by rfl⟩ : syracuseStep 1492037 = 279757) (by norm_num)
theorem B1492061 : Blo 992597 1492061 := bbase (se 3 (by rfl) ⟨279761, by rfl⟩ : syracuseStep 1492061 = 559523) (by norm_num)
theorem B1885285 : Blo 992597 1885285 := bbase (se 4 (by rfl) ⟨176745, by rfl⟩ : syracuseStep 1885285 = 353491) (by norm_num)
theorem B1492085 : Blo 992597 1492085 := bbase (se 5 (by rfl) ⟨69941, by rfl⟩ : syracuseStep 1492085 = 139883) (by norm_num)
theorem B2016389 : Blo 992597 2016389 := bbase (se 4 (by rfl) ⟨189036, by rfl⟩ : syracuseStep 2016389 = 378073) (by norm_num)
theorem B1492109 : Blo 992597 1492109 := bbase (se 3 (by rfl) ⟨279770, by rfl⟩ : syracuseStep 1492109 = 559541) (by norm_num)
theorem B1492133 : Blo 992597 1492133 := bbase (se 4 (by rfl) ⟨139887, by rfl⟩ : syracuseStep 1492133 = 279775) (by norm_num)
theorem B3884213 : Blo 992597 3884213 := bbase (se 5 (by rfl) ⟨182072, by rfl⟩ : syracuseStep 3884213 = 364145) (by norm_num)
theorem B1492157 : Blo 992597 1492157 := bbase (se 3 (by rfl) ⟨279779, by rfl⟩ : syracuseStep 1492157 = 559559) (by norm_num)
theorem B1492181 : Blo 992597 1492181 := bbase (se 7 (by rfl) ⟨17486, by rfl⟩ : syracuseStep 1492181 = 34973) (by norm_num)
theorem B1492205 : Blo 992597 1492205 := bbase (se 3 (by rfl) ⟨279788, by rfl⟩ : syracuseStep 1492205 = 559577) (by norm_num)
theorem B1492229 : Blo 992597 1492229 := bbase (se 4 (by rfl) ⟨139896, by rfl⟩ : syracuseStep 1492229 = 279793) (by norm_num)
theorem B1492253 : Blo 992597 1492253 := bbase (se 3 (by rfl) ⟨279797, by rfl⟩ : syracuseStep 1492253 = 559595) (by norm_num)
theorem B1492277 : Blo 992597 1492277 := bbase (se 5 (by rfl) ⟨69950, by rfl⟩ : syracuseStep 1492277 = 139901) (by norm_num)
theorem B1492301 : Blo 992597 1492301 := bbase (se 3 (by rfl) ⟨279806, by rfl⟩ : syracuseStep 1492301 = 559613) (by norm_num)
theorem B1492325 : Blo 992597 1492325 := bbase (se 4 (by rfl) ⟨139905, by rfl⟩ : syracuseStep 1492325 = 279811) (by norm_num)
theorem B1492349 : Blo 992597 1492349 := bbase (se 3 (by rfl) ⟨279815, by rfl⟩ : syracuseStep 1492349 = 559631) (by norm_num)
theorem B1885589 : Blo 992597 1885589 := bbase (se 6 (by rfl) ⟨44193, by rfl⟩ : syracuseStep 1885589 = 88387) (by norm_num)
theorem B1492373 : Blo 992597 1492373 := bbase (se 6 (by rfl) ⟨34977, by rfl⟩ : syracuseStep 1492373 = 69955) (by norm_num)
theorem B3360149 : Blo 992597 3360149 := bbase (se 6 (by rfl) ⟨78753, by rfl⟩ : syracuseStep 3360149 = 157507) (by norm_num)
theorem B1492397 : Blo 992597 1492397 := bbase (se 3 (by rfl) ⟨279824, by rfl⟩ : syracuseStep 1492397 = 559649) (by norm_num)
theorem B1492421 : Blo 992597 1492421 := bbase (se 4 (by rfl) ⟨139914, by rfl⟩ : syracuseStep 1492421 = 279829) (by norm_num)
theorem B1590749 : Blo 992597 1590749 := bbase (se 3 (by rfl) ⟨298265, by rfl⟩ : syracuseStep 1590749 = 596531) (by norm_num)
theorem B1492445 : Blo 992597 1492445 := bbase (se 3 (by rfl) ⟨279833, by rfl⟩ : syracuseStep 1492445 = 559667) (by norm_num)
theorem B1492469 : Blo 992597 1492469 := bbase (se 5 (by rfl) ⟨69959, by rfl⟩ : syracuseStep 1492469 = 139919) (by norm_num)
theorem B1590781 : Blo 992597 1590781 := bbase (se 3 (by rfl) ⟨298271, by rfl⟩ : syracuseStep 1590781 = 596543) (by norm_num)
theorem B1492493 : Blo 992597 1492493 := bbase (se 3 (by rfl) ⟨279842, by rfl⟩ : syracuseStep 1492493 = 559685) (by norm_num)
theorem B1492517 : Blo 992597 1492517 := bbase (se 4 (by rfl) ⟨139923, by rfl⟩ : syracuseStep 1492517 = 279847) (by norm_num)
theorem B1492541 : Blo 992597 1492541 := bbase (se 3 (by rfl) ⟨279851, by rfl⟩ : syracuseStep 1492541 = 559703) (by norm_num)
theorem B1492565 : Blo 992597 1492565 := bbase (se 8 (by rfl) ⟨8745, by rfl⟩ : syracuseStep 1492565 = 17491) (by norm_num)
theorem B1492589 : Blo 992597 1492589 := bbase (se 3 (by rfl) ⟨279860, by rfl⟩ : syracuseStep 1492589 = 559721) (by norm_num)
theorem B5031557 : Blo 992597 5031557 := bbase (se 4 (by rfl) ⟨471708, by rfl⟩ : syracuseStep 5031557 = 943417) (by norm_num)
theorem B1492613 : Blo 992597 1492613 := bbase (se 4 (by rfl) ⟨139932, by rfl⟩ : syracuseStep 1492613 = 279865) (by norm_num)
theorem B1492637 : Blo 992597 1492637 := bbase (se 3 (by rfl) ⟨279869, by rfl⟩ : syracuseStep 1492637 = 559739) (by norm_num)
theorem B4245173 : Blo 992597 4245173 := bbase (se 5 (by rfl) ⟨198992, by rfl⟩ : syracuseStep 4245173 = 397985) (by norm_num)
theorem B1492661 : Blo 992597 1492661 := bbase (se 5 (by rfl) ⟨69968, by rfl⟩ : syracuseStep 1492661 = 139937) (by norm_num)
theorem B1492685 : Blo 992597 1492685 := bbase (se 3 (by rfl) ⟨279878, by rfl⟩ : syracuseStep 1492685 = 559757) (by norm_num)
theorem B1492709 : Blo 992597 1492709 := bbase (se 4 (by rfl) ⟨139941, by rfl⟩ : syracuseStep 1492709 = 279883) (by norm_num)
theorem B1132285 : Blo 992597 1132285 := bbase (se 3 (by rfl) ⟨212303, by rfl⟩ : syracuseStep 1132285 = 424607) (by norm_num)
theorem B1492733 : Blo 992597 1492733 := bbase (se 3 (by rfl) ⟨279887, by rfl⟩ : syracuseStep 1492733 = 559775) (by norm_num)
theorem B1492757 : Blo 992597 1492757 := bbase (se 6 (by rfl) ⟨34986, by rfl⟩ : syracuseStep 1492757 = 69973) (by norm_num)
theorem B1492781 : Blo 992597 1492781 := bbase (se 3 (by rfl) ⟨279896, by rfl⟩ : syracuseStep 1492781 = 559793) (by norm_num)
theorem B7554869 : Blo 992597 7554869 := bbase (se 5 (by rfl) ⟨354134, by rfl⟩ : syracuseStep 7554869 = 708269) (by norm_num)
theorem B1492805 : Blo 992597 1492805 := bbase (se 4 (by rfl) ⟨139950, by rfl⟩ : syracuseStep 1492805 = 279901) (by norm_num)
theorem B3360581 : Blo 992597 3360581 := bbase (se 4 (by rfl) ⟨315054, by rfl⟩ : syracuseStep 3360581 = 630109) (by norm_num)
theorem B1492829 : Blo 992597 1492829 := bbase (se 3 (by rfl) ⟨279905, by rfl⟩ : syracuseStep 1492829 = 559811) (by norm_num)
theorem B1492853 : Blo 992597 1492853 := bbase (se 5 (by rfl) ⟨69977, by rfl⟩ : syracuseStep 1492853 = 139955) (by norm_num)
theorem B1492877 : Blo 992597 1492877 := bbase (se 3 (by rfl) ⟨279914, by rfl⟩ : syracuseStep 1492877 = 559829) (by norm_num)
theorem B1492901 : Blo 992597 1492901 := bbase (se 4 (by rfl) ⟨139959, by rfl⟩ : syracuseStep 1492901 = 279919) (by norm_num)
theorem B1492925 : Blo 992597 1492925 := bbase (se 3 (by rfl) ⟨279923, by rfl⟩ : syracuseStep 1492925 = 559847) (by norm_num)
theorem B1492949 : Blo 992597 1492949 := bbase (se 7 (by rfl) ⟨17495, by rfl⟩ : syracuseStep 1492949 = 34991) (by norm_num)
theorem B1492973 : Blo 992597 1492973 := bbase (se 3 (by rfl) ⟨279932, by rfl⟩ : syracuseStep 1492973 = 559865) (by norm_num)
theorem B9553909 : Blo 992597 9553909 := bbase (se 5 (by rfl) ⟨447839, by rfl⟩ : syracuseStep 9553909 = 895679) (by norm_num)
theorem B1492997 : Blo 992597 1492997 := bbase (se 4 (by rfl) ⟨139968, by rfl⟩ : syracuseStep 1492997 = 279937) (by norm_num)
theorem B1493021 : Blo 992597 1493021 := bbase (se 3 (by rfl) ⟨279941, by rfl⟩ : syracuseStep 1493021 = 559883) (by norm_num)
theorem B1493045 : Blo 992597 1493045 := bbase (se 5 (by rfl) ⟨69986, by rfl⟩ : syracuseStep 1493045 = 139973) (by norm_num)
theorem B1493069 : Blo 992597 1493069 := bbase (se 3 (by rfl) ⟨279950, by rfl⟩ : syracuseStep 1493069 = 559901) (by norm_num)
theorem B1493093 : Blo 992597 1493093 := bbase (se 4 (by rfl) ⟨139977, by rfl⟩ : syracuseStep 1493093 = 279955) (by norm_num)
theorem B1493117 : Blo 992597 1493117 := bbase (se 3 (by rfl) ⟨279959, by rfl⟩ : syracuseStep 1493117 = 559919) (by norm_num)
theorem B1886341 : Blo 992597 1886341 := bbase (se 4 (by rfl) ⟨176844, by rfl⟩ : syracuseStep 1886341 = 353689) (by norm_num)
theorem B1493141 : Blo 992597 1493141 := bbase (se 6 (by rfl) ⟨34995, by rfl⟩ : syracuseStep 1493141 = 69991) (by norm_num)
theorem B1493165 : Blo 992597 1493165 := bbase (se 3 (by rfl) ⟨279968, by rfl⟩ : syracuseStep 1493165 = 559937) (by norm_num)
theorem B1493189 : Blo 992597 1493189 := bbase (se 4 (by rfl) ⟨139986, by rfl⟩ : syracuseStep 1493189 = 279973) (by norm_num)
theorem B1493213 : Blo 992597 1493213 := bbase (se 3 (by rfl) ⟨279977, by rfl⟩ : syracuseStep 1493213 = 559955) (by norm_num)
theorem B1493237 : Blo 992597 1493237 := bbase (se 5 (by rfl) ⟨69995, by rfl⟩ : syracuseStep 1493237 = 139991) (by norm_num)
theorem B3361013 : Blo 992597 3361013 := bbase (se 5 (by rfl) ⟨157547, by rfl⟩ : syracuseStep 3361013 = 315095) (by norm_num)
theorem B4770053 : Blo 992597 4770053 := bbase (se 4 (by rfl) ⟨447192, by rfl⟩ : syracuseStep 4770053 = 894385) (by norm_num)
theorem B1493261 : Blo 992597 1493261 := bbase (se 3 (by rfl) ⟨279986, by rfl⟩ : syracuseStep 1493261 = 559973) (by norm_num)
theorem B1886485 : Blo 992597 1886485 := bbase (se 6 (by rfl) ⟨44214, by rfl⟩ : syracuseStep 1886485 = 88429) (by norm_num)
theorem B1493285 : Blo 992597 1493285 := bbase (se 4 (by rfl) ⟨139995, by rfl⟩ : syracuseStep 1493285 = 279991) (by norm_num)
theorem B1493309 : Blo 992597 1493309 := bbase (se 3 (by rfl) ⟨279995, by rfl⟩ : syracuseStep 1493309 = 559991) (by norm_num)
theorem B1493333 : Blo 992597 1493333 := bbase (se 10 (by rfl) ⟨2187, by rfl⟩ : syracuseStep 1493333 = 4375) (by norm_num)
theorem B1493357 : Blo 992597 1493357 := bbase (se 3 (by rfl) ⟨280004, by rfl⟩ : syracuseStep 1493357 = 560009) (by norm_num)
theorem B1493381 : Blo 992597 1493381 := bbase (se 4 (by rfl) ⟨140004, by rfl⟩ : syracuseStep 1493381 = 280009) (by norm_num)
theorem B1591709 : Blo 992597 1591709 := bbase (se 3 (by rfl) ⟨298445, by rfl⟩ : syracuseStep 1591709 = 596891) (by norm_num)
theorem B1493405 : Blo 992597 1493405 := bbase (se 3 (by rfl) ⟨280013, by rfl⟩ : syracuseStep 1493405 = 560027) (by norm_num)
theorem B1886645 : Blo 992597 1886645 := bbase (se 5 (by rfl) ⟨88436, by rfl⟩ : syracuseStep 1886645 = 176873) (by norm_num)
theorem B1493429 : Blo 992597 1493429 := bbase (se 5 (by rfl) ⟨70004, by rfl⟩ : syracuseStep 1493429 = 140009) (by norm_num)
theorem B1493453 : Blo 992597 1493453 := bbase (se 3 (by rfl) ⟨280022, by rfl⟩ : syracuseStep 1493453 = 560045) (by norm_num)
theorem B1493477 : Blo 992597 1493477 := bbase (se 4 (by rfl) ⟨140013, by rfl⟩ : syracuseStep 1493477 = 280027) (by norm_num)
theorem B1493501 : Blo 992597 1493501 := bbase (se 3 (by rfl) ⟨280031, by rfl⟩ : syracuseStep 1493501 = 560063) (by norm_num)
theorem B1493525 : Blo 992597 1493525 := bbase (se 6 (by rfl) ⟨35004, by rfl⟩ : syracuseStep 1493525 = 70009) (by norm_num)
theorem B1493549 : Blo 992597 1493549 := bbase (se 3 (by rfl) ⟨280040, by rfl⟩ : syracuseStep 1493549 = 560081) (by norm_num)
theorem B1886789 : Blo 992597 1886789 := bbase (se 4 (by rfl) ⟨176886, by rfl⟩ : syracuseStep 1886789 = 353773) (by norm_num)
theorem B1493573 : Blo 992597 1493573 := bbase (se 4 (by rfl) ⟨140022, by rfl⟩ : syracuseStep 1493573 = 280045) (by norm_num)
theorem B1493597 : Blo 992597 1493597 := bbase (se 3 (by rfl) ⟨280049, by rfl⟩ : syracuseStep 1493597 = 560099) (by norm_num)
theorem B1493621 : Blo 992597 1493621 := bbase (se 5 (by rfl) ⟨70013, by rfl⟩ : syracuseStep 1493621 = 140027) (by norm_num)
theorem B1493645 : Blo 992597 1493645 := bbase (se 3 (by rfl) ⟨280058, by rfl⟩ : syracuseStep 1493645 = 560117) (by norm_num)
theorem B1493669 : Blo 992597 1493669 := bbase (se 4 (by rfl) ⟨140031, by rfl⟩ : syracuseStep 1493669 = 280063) (by norm_num)
theorem B3361445 : Blo 992597 3361445 := bbase (se 4 (by rfl) ⟨315135, by rfl⟩ : syracuseStep 3361445 = 630271) (by norm_num)
theorem B1493693 : Blo 992597 1493693 := bbase (se 3 (by rfl) ⟨280067, by rfl⟩ : syracuseStep 1493693 = 560135) (by norm_num)
theorem B1493717 : Blo 992597 1493717 := bbase (se 7 (by rfl) ⟨17504, by rfl⟩ : syracuseStep 1493717 = 35009) (by norm_num)
theorem B1493741 : Blo 992597 1493741 := bbase (se 3 (by rfl) ⟨280076, by rfl⟩ : syracuseStep 1493741 = 560153) (by norm_num)
theorem B1493765 : Blo 992597 1493765 := bbase (se 4 (by rfl) ⟨140040, by rfl⟩ : syracuseStep 1493765 = 280081) (by norm_num)
theorem B8506133 : Blo 992597 8506133 := bbase (se 6 (by rfl) ⟨199362, by rfl⟩ : syracuseStep 8506133 = 398725) (by norm_num)
theorem B1493789 : Blo 992597 1493789 := bbase (se 3 (by rfl) ⟨280085, by rfl⟩ : syracuseStep 1493789 = 560171) (by norm_num)
theorem B1493813 : Blo 992597 1493813 := bbase (se 5 (by rfl) ⟨70022, by rfl⟩ : syracuseStep 1493813 = 140045) (by norm_num)
theorem B1493837 : Blo 992597 1493837 := bbase (se 3 (by rfl) ⟨280094, by rfl⟩ : syracuseStep 1493837 = 560189) (by norm_num)
theorem B1887077 : Blo 992597 1887077 := bbase (se 4 (by rfl) ⟨176913, by rfl⟩ : syracuseStep 1887077 = 353827) (by norm_num)
theorem B1493861 : Blo 992597 1493861 := bbase (se 4 (by rfl) ⟨140049, by rfl⟩ : syracuseStep 1493861 = 280099) (by norm_num)
theorem B1493885 : Blo 992597 1493885 := bbase (se 3 (by rfl) ⟨280103, by rfl⟩ : syracuseStep 1493885 = 560207) (by norm_num)
theorem B1133453 : Blo 992597 1133453 := bbase (se 3 (by rfl) ⟨212522, by rfl⟩ : syracuseStep 1133453 = 425045) (by norm_num)
theorem B5032853 : Blo 992597 5032853 := bbase (se 6 (by rfl) ⟨117957, by rfl⟩ : syracuseStep 5032853 = 235915) (by norm_num)
theorem B1493909 : Blo 992597 1493909 := bbase (se 6 (by rfl) ⟨35013, by rfl⟩ : syracuseStep 1493909 = 70027) (by norm_num)
theorem B1493933 : Blo 992597 1493933 := bbase (se 3 (by rfl) ⟨280112, by rfl⟩ : syracuseStep 1493933 = 560225) (by norm_num)
theorem B1493957 : Blo 992597 1493957 := bbase (se 4 (by rfl) ⟨140058, by rfl⟩ : syracuseStep 1493957 = 280117) (by norm_num)
theorem B1493981 : Blo 992597 1493981 := bbase (se 3 (by rfl) ⟨280121, by rfl⟩ : syracuseStep 1493981 = 560243) (by norm_num)
theorem B1494005 : Blo 992597 1494005 := bbase (se 5 (by rfl) ⟨70031, by rfl⟩ : syracuseStep 1494005 = 140063) (by norm_num)
theorem B1887229 : Blo 992597 1887229 := bbase (se 3 (by rfl) ⟨353855, by rfl⟩ : syracuseStep 1887229 = 707711) (by norm_num)
theorem B1494029 : Blo 992597 1494029 := bbase (se 3 (by rfl) ⟨280130, by rfl⟩ : syracuseStep 1494029 = 560261) (by norm_num)
theorem B1494053 : Blo 992597 1494053 := bbase (se 4 (by rfl) ⟨140067, by rfl⟩ : syracuseStep 1494053 = 280135) (by norm_num)
theorem B1494077 : Blo 992597 1494077 := bbase (se 3 (by rfl) ⟨280139, by rfl⟩ : syracuseStep 1494077 = 560279) (by norm_num)
theorem B1592389 : Blo 992597 1592389 := bbase (se 4 (by rfl) ⟨149286, by rfl⟩ : syracuseStep 1592389 = 298573) (by norm_num)
theorem B1494101 : Blo 992597 1494101 := bbase (se 8 (by rfl) ⟨8754, by rfl⟩ : syracuseStep 1494101 = 17509) (by norm_num)
theorem B3361877 : Blo 992597 3361877 := bbase (se 8 (by rfl) ⟨19698, by rfl⟩ : syracuseStep 3361877 = 39397) (by norm_num)
theorem B1494125 : Blo 992597 1494125 := bbase (se 3 (by rfl) ⟨280148, by rfl⟩ : syracuseStep 1494125 = 560297) (by norm_num)
theorem B1592453 : Blo 992597 1592453 := bbase (se 4 (by rfl) ⟨149292, by rfl⟩ : syracuseStep 1592453 = 298585) (by norm_num)
theorem B1494149 : Blo 992597 1494149 := bbase (se 4 (by rfl) ⟨140076, by rfl⟩ : syracuseStep 1494149 = 280153) (by norm_num)
theorem B1494173 : Blo 992597 1494173 := bbase (se 3 (by rfl) ⟨280157, by rfl⟩ : syracuseStep 1494173 = 560315) (by norm_num)
theorem B1494197 : Blo 992597 1494197 := bbase (se 5 (by rfl) ⟨70040, by rfl⟩ : syracuseStep 1494197 = 140081) (by norm_num)
theorem B1494221 : Blo 992597 1494221 := bbase (se 3 (by rfl) ⟨280166, by rfl⟩ : syracuseStep 1494221 = 560333) (by norm_num)
theorem B1494245 : Blo 992597 1494245 := bbase (se 4 (by rfl) ⟨140085, by rfl⟩ : syracuseStep 1494245 = 280171) (by norm_num)
theorem B1494269 : Blo 992597 1494269 := bbase (se 3 (by rfl) ⟨280175, by rfl⟩ : syracuseStep 1494269 = 560351) (by norm_num)
theorem B1363213 : Blo 992597 1363213 := bbase (se 3 (by rfl) ⟨255602, by rfl⟩ : syracuseStep 1363213 = 511205) (by norm_num)
theorem B1494293 : Blo 992597 1494293 := bbase (se 6 (by rfl) ⟨35022, by rfl⟩ : syracuseStep 1494293 = 70045) (by norm_num)
theorem B1887533 : Blo 992597 1887533 := bbase (se 3 (by rfl) ⟨353912, by rfl⟩ : syracuseStep 1887533 = 707825) (by norm_num)
theorem B1494317 : Blo 992597 1494317 := bbase (se 3 (by rfl) ⟨280184, by rfl⟩ : syracuseStep 1494317 = 560369) (by norm_num)
theorem B1494341 : Blo 992597 1494341 := bbase (se 4 (by rfl) ⟨140094, by rfl⟩ : syracuseStep 1494341 = 280189) (by norm_num)
theorem B1494365 : Blo 992597 1494365 := bbase (se 3 (by rfl) ⟨280193, by rfl⟩ : syracuseStep 1494365 = 560387) (by norm_num)
theorem B2837861 : Blo 992597 2837861 := bbase (se 4 (by rfl) ⟨266049, by rfl⟩ : syracuseStep 2837861 = 532099) (by norm_num)
theorem B1494389 : Blo 992597 1494389 := bbase (se 5 (by rfl) ⟨70049, by rfl⟩ : syracuseStep 1494389 = 140099) (by norm_num)
theorem B1494413 : Blo 992597 1494413 := bbase (se 3 (by rfl) ⟨280202, by rfl⟩ : syracuseStep 1494413 = 560405) (by norm_num)
theorem B1494437 : Blo 992597 1494437 := bbase (se 4 (by rfl) ⟨140103, by rfl⟩ : syracuseStep 1494437 = 280207) (by norm_num)
theorem B1494461 : Blo 992597 1494461 := bbase (se 3 (by rfl) ⟨280211, by rfl⟩ : syracuseStep 1494461 = 560423) (by norm_num)
theorem B2870741 : Blo 992597 2870741 := bbase (se 7 (by rfl) ⟨33641, by rfl⟩ : syracuseStep 2870741 = 67283) (by norm_num)
theorem B1494485 : Blo 992597 1494485 := bbase (se 7 (by rfl) ⟨17513, by rfl⟩ : syracuseStep 1494485 = 35027) (by norm_num)
theorem B1494509 : Blo 992597 1494509 := bbase (se 3 (by rfl) ⟨280220, by rfl⟩ : syracuseStep 1494509 = 560441) (by norm_num)
theorem B3362309 : Blo 992597 3362309 := bbase (se 4 (by rfl) ⟨315216, by rfl⟩ : syracuseStep 3362309 = 630433) (by norm_num)
theorem B1494533 : Blo 992597 1494533 := bbase (se 4 (by rfl) ⟨140112, by rfl⟩ : syracuseStep 1494533 = 280225) (by norm_num)
theorem B1494557 : Blo 992597 1494557 := bbase (se 3 (by rfl) ⟨280229, by rfl⟩ : syracuseStep 1494557 = 560459) (by norm_num)
theorem B1494581 : Blo 992597 1494581 := bbase (se 5 (by rfl) ⟨70058, by rfl⟩ : syracuseStep 1494581 = 140117) (by norm_num)
theorem B1494605 : Blo 992597 1494605 := bbase (se 3 (by rfl) ⟨280238, by rfl⟩ : syracuseStep 1494605 = 560477) (by norm_num)
theorem B1494629 : Blo 992597 1494629 := bbase (se 4 (by rfl) ⟨140121, by rfl⟩ : syracuseStep 1494629 = 280243) (by norm_num)
theorem B1494653 : Blo 992597 1494653 := bbase (se 3 (by rfl) ⟨280247, by rfl⟩ : syracuseStep 1494653 = 560495) (by norm_num)
theorem B1494677 : Blo 992597 1494677 := bbase (se 6 (by rfl) ⟨35031, by rfl⟩ : syracuseStep 1494677 = 70063) (by norm_num)
theorem B1494701 : Blo 992597 1494701 := bbase (se 3 (by rfl) ⟨280256, by rfl⟩ : syracuseStep 1494701 = 560513) (by norm_num)
theorem B1494725 : Blo 992597 1494725 := bbase (se 4 (by rfl) ⟨140130, by rfl⟩ : syracuseStep 1494725 = 280261) (by norm_num)
theorem B1494749 : Blo 992597 1494749 := bbase (se 3 (by rfl) ⟨280265, by rfl⟩ : syracuseStep 1494749 = 560531) (by norm_num)
theorem B1494773 : Blo 992597 1494773 := bbase (se 5 (by rfl) ⟨70067, by rfl⟩ : syracuseStep 1494773 = 140135) (by norm_num)
theorem B1494797 : Blo 992597 1494797 := bbase (se 3 (by rfl) ⟨280274, by rfl⟩ : syracuseStep 1494797 = 560549) (by norm_num)
theorem B4837141 : Blo 992597 4837141 := bbase (se 6 (by rfl) ⟨113370, by rfl⟩ : syracuseStep 4837141 = 226741) (by norm_num)
theorem B1494821 : Blo 992597 1494821 := bbase (se 4 (by rfl) ⟨140139, by rfl⟩ : syracuseStep 1494821 = 280279) (by norm_num)
theorem B1494845 : Blo 992597 1494845 := bbase (se 3 (by rfl) ⟨280283, by rfl⟩ : syracuseStep 1494845 = 560567) (by norm_num)
theorem B4542277 : Blo 992597 4542277 := bbase (se 4 (by rfl) ⟨425838, by rfl⟩ : syracuseStep 4542277 = 851677) (by norm_num)
theorem B4771669 : Blo 992597 4771669 := bbase (se 9 (by rfl) ⟨13979, by rfl⟩ : syracuseStep 4771669 = 27959) (by norm_num)
theorem B1494869 : Blo 992597 1494869 := bbase (se 9 (by rfl) ⟨4379, by rfl⟩ : syracuseStep 1494869 = 8759) (by norm_num)
theorem B1494893 : Blo 992597 1494893 := bbase (se 3 (by rfl) ⟨280292, by rfl⟩ : syracuseStep 1494893 = 560585) (by norm_num)
theorem B3362741 : Blo 992597 3362741 := bbase (se 5 (by rfl) ⟨157628, by rfl⟩ : syracuseStep 3362741 = 315257) (by norm_num)
theorem B2019325 : Blo 992597 2019325 := bbase (se 3 (by rfl) ⟨378623, by rfl⟩ : syracuseStep 2019325 = 757247) (by norm_num)
theorem B1888285 : Blo 992597 1888285 := bbase (se 3 (by rfl) ⟨354053, by rfl⟩ : syracuseStep 1888285 = 708107) (by norm_num)
theorem B5034149 : Blo 992597 5034149 := bbase (se 4 (by rfl) ⟨471951, by rfl⟩ : syracuseStep 5034149 = 943903) (by norm_num)
theorem B1888429 : Blo 992597 1888429 := bbase (se 3 (by rfl) ⟨354080, by rfl⟩ : syracuseStep 1888429 = 708161) (by norm_num)
theorem B1134913 : Blo 992597 1134913 := bbase (se 2 (by rfl) ⟨425592, by rfl⟩ : syracuseStep 1134913 = 851185) (by norm_num)
theorem B1888589 : Blo 992597 1888589 := bbase (se 3 (by rfl) ⟨354110, by rfl⟩ : syracuseStep 1888589 = 708221) (by norm_num)
theorem B3887461 : Blo 992597 3887461 := bbase (se 4 (by rfl) ⟨364449, by rfl⟩ : syracuseStep 3887461 = 728899) (by norm_num)
theorem B3363173 : Blo 992597 3363173 := bbase (se 4 (by rfl) ⟨315297, by rfl⟩ : syracuseStep 3363173 = 630595) (by norm_num)
theorem B5656949 : Blo 992597 5656949 := bbase (se 5 (by rfl) ⟨265169, by rfl⟩ : syracuseStep 5656949 = 530339) (by norm_num)
theorem B1593773 : Blo 992597 1593773 := bbase (se 3 (by rfl) ⟨298832, by rfl⟩ : syracuseStep 1593773 = 597665) (by norm_num)
theorem B18141653 : Blo 992597 18141653 := bbase (se 7 (by rfl) ⟨212597, by rfl⟩ : syracuseStep 18141653 = 425195) (by norm_num)
theorem B1888733 : Blo 992597 1888733 := bbase (se 3 (by rfl) ⟨354137, by rfl⟩ : syracuseStep 1888733 = 708275) (by norm_num)
theorem B1593965 : Blo 992597 1593965 := bbase (se 3 (by rfl) ⟨298868, by rfl⟩ : syracuseStep 1593965 = 597737) (by norm_num)
theorem B3232453 : Blo 992597 3232453 := bbase (se 4 (by rfl) ⟨303042, by rfl⟩ : syracuseStep 3232453 = 606085) (by norm_num)
theorem B1594093 : Blo 992597 1594093 := bbase (se 3 (by rfl) ⟨298892, by rfl⟩ : syracuseStep 1594093 = 597785) (by norm_num)
theorem B1889021 : Blo 992597 1889021 := bbase (se 3 (by rfl) ⟨354191, by rfl⟩ : syracuseStep 1889021 = 708383) (by norm_num)
theorem B1889173 : Blo 992597 1889173 := bbase (se 6 (by rfl) ⟨44277, by rfl⟩ : syracuseStep 1889173 = 88555) (by norm_num)
theorem B1791013 : Blo 992597 1791013 := bbase (se 4 (by rfl) ⟨167907, by rfl⟩ : syracuseStep 1791013 = 335815) (by norm_num)
theorem B1889477 : Blo 992597 1889477 := bbase (se 4 (by rfl) ⟨177138, by rfl⟩ : syracuseStep 1889477 = 354277) (by norm_num)
theorem B7165205 : Blo 992597 7165205 := bbase (se 6 (by rfl) ⟨167934, by rfl⟩ : syracuseStep 7165205 = 335869) (by norm_num)
theorem B1594733 : Blo 992597 1594733 := bbase (se 3 (by rfl) ⟨299012, by rfl⟩ : syracuseStep 1594733 = 598025) (by norm_num)
theorem B5035445 : Blo 992597 5035445 := bbase (se 5 (by rfl) ⟨236036, by rfl⟩ : syracuseStep 5035445 = 472073) (by norm_num)
theorem B5658133 : Blo 992597 5658133 := bbase (se 6 (by rfl) ⟨132612, by rfl⟩ : syracuseStep 5658133 = 265225) (by norm_num)
theorem B4249205 : Blo 992597 4249205 := bbase (se 5 (by rfl) ⟨199181, by rfl⟩ : syracuseStep 4249205 = 398363) (by norm_num)
theorem B1791653 : Blo 992597 1791653 := bbase (se 4 (by rfl) ⟨167967, by rfl⟩ : syracuseStep 1791653 = 335935) (by norm_num)
theorem B1595189 : Blo 992597 1595189 := bbase (se 5 (by rfl) ⟨74774, by rfl⟩ : syracuseStep 1595189 = 149549) (by norm_num)
theorem B2512741 : Blo 992597 2512741 := bbase (se 4 (by rfl) ⟨235569, by rfl⟩ : syracuseStep 2512741 = 471139) (by norm_num)
theorem B1890229 : Blo 992597 1890229 := bbase (se 5 (by rfl) ⟨88604, by rfl⟩ : syracuseStep 1890229 = 177209) (by norm_num)
theorem B2512853 : Blo 992597 2512853 := bbase (se 7 (by rfl) ⟨29447, by rfl⟩ : syracuseStep 2512853 = 58895) (by norm_num)
theorem B3397621 : Blo 992597 3397621 := bbase (se 5 (by rfl) ⟨159263, by rfl⟩ : syracuseStep 3397621 = 318527) (by norm_num)
theorem B1595413 : Blo 992597 1595413 := bbase (se 6 (by rfl) ⟨37392, by rfl⟩ : syracuseStep 1595413 = 74785) (by norm_num)
theorem B1890373 : Blo 992597 1890373 := bbase (se 4 (by rfl) ⟨177222, by rfl⟩ : syracuseStep 1890373 = 354445) (by norm_num)
theorem B1595477 : Blo 992597 1595477 := bbase (se 8 (by rfl) ⟨9348, by rfl⟩ : syracuseStep 1595477 = 18697) (by norm_num)
theorem B3397733 : Blo 992597 3397733 := bbase (se 4 (by rfl) ⟨318537, by rfl⟩ : syracuseStep 3397733 = 637075) (by norm_num)
theorem B2513045 : Blo 992597 2513045 := bbase (se 6 (by rfl) ⟨58899, by rfl⟩ : syracuseStep 2513045 = 117799) (by norm_num)
theorem B1595605 : Blo 992597 1595605 := bbase (se 7 (by rfl) ⟨18698, by rfl⟩ : syracuseStep 1595605 = 37397) (by norm_num)
theorem B1890533 : Blo 992597 1890533 := bbase (se 4 (by rfl) ⟨177237, by rfl⟩ : syracuseStep 1890533 = 354475) (by norm_num)
theorem B1890677 : Blo 992597 1890677 := bbase (se 5 (by rfl) ⟨88625, by rfl⟩ : syracuseStep 1890677 = 177251) (by norm_num)
theorem B4544981 : Blo 992597 4544981 := bbase (se 7 (by rfl) ⟨53261, by rfl⟩ : syracuseStep 4544981 = 106523) (by norm_num)
theorem B3791333 : Blo 992597 3791333 := bbase (se 4 (by rfl) ⟨355437, by rfl⟩ : syracuseStep 3791333 = 710875) (by norm_num)
theorem B2513389 : Blo 992597 2513389 := bbase (se 3 (by rfl) ⟨471260, by rfl⟩ : syracuseStep 2513389 = 942521) (by norm_num)
theorem B2513501 : Blo 992597 2513501 := bbase (se 3 (by rfl) ⟨471281, by rfl⟩ : syracuseStep 2513501 = 942563) (by norm_num)
theorem B1890965 : Blo 992597 1890965 := bbase (se 6 (by rfl) ⟨44319, by rfl⟩ : syracuseStep 1890965 = 88639) (by norm_num)
theorem B2120357 : Blo 992597 2120357 := bbase (se 4 (by rfl) ⟨198783, by rfl⟩ : syracuseStep 2120357 = 397567) (by norm_num)
theorem B2120365 : Blo 992597 2120365 := bbase (se 3 (by rfl) ⟨397568, by rfl⟩ : syracuseStep 2120365 = 795137) (by norm_num)
theorem B5036741 : Blo 992597 5036741 := bbase (se 4 (by rfl) ⟨472194, by rfl⟩ : syracuseStep 5036741 = 944389) (by norm_num)
theorem B3824405 : Blo 992597 3824405 := bbase (se 6 (by rfl) ⟨89634, by rfl⟩ : syracuseStep 3824405 = 179269) (by norm_num)
theorem B2513693 : Blo 992597 2513693 := bbase (se 3 (by rfl) ⟨471317, by rfl⟩ : syracuseStep 2513693 = 942635) (by norm_num)
theorem B1891117 : Blo 992597 1891117 := bbase (se 3 (by rfl) ⟨354584, by rfl⟩ : syracuseStep 1891117 = 709169) (by norm_num)
theorem B2906933 : Blo 992597 2906933 := bbase (se 5 (by rfl) ⟨136262, by rfl⟩ : syracuseStep 2906933 = 272525) (by norm_num)
theorem B1792973 : Blo 992597 1792973 := bbase (se 3 (by rfl) ⟨336182, by rfl⟩ : syracuseStep 1792973 = 672365) (by norm_num)
theorem B1891421 : Blo 992597 1891421 := bbase (se 3 (by rfl) ⟨354641, by rfl⟩ : syracuseStep 1891421 = 709283) (by norm_num)
theorem B2514037 : Blo 992597 2514037 := bbase (se 5 (by rfl) ⟨117845, by rfl⟩ : syracuseStep 2514037 = 235691) (by norm_num)
theorem B3398773 : Blo 992597 3398773 := bbase (se 5 (by rfl) ⟨159317, by rfl⟩ : syracuseStep 3398773 = 318635) (by norm_num)
theorem B3267749 : Blo 992597 3267749 := bbase (se 4 (by rfl) ⟨306351, by rfl⟩ : syracuseStep 3267749 = 612703) (by norm_num)
theorem B2514149 : Blo 992597 2514149 := bbase (se 4 (by rfl) ⟨235701, by rfl⟩ : syracuseStep 2514149 = 471403) (by norm_num)
theorem B4250981 : Blo 992597 4250981 := bbase (se 4 (by rfl) ⟨398529, by rfl⟩ : syracuseStep 4250981 = 797059) (by norm_num)
theorem B2514341 : Blo 992597 2514341 := bbase (se 4 (by rfl) ⟨235719, by rfl⟩ : syracuseStep 2514341 = 471439) (by norm_num)
theorem B5660117 : Blo 992597 5660117 := bbase (se 7 (by rfl) ⟨66329, by rfl⟩ : syracuseStep 5660117 = 132659) (by norm_num)
theorem B3071461 : Blo 992597 3071461 := bbase (se 4 (by rfl) ⟨287949, by rfl⟩ : syracuseStep 3071461 = 575899) (by norm_num)
theorem B1007165 : Blo 992597 1007165 := bbase (se 3 (by rfl) ⟨188843, by rfl⟩ : syracuseStep 1007165 = 377687) (by norm_num)
theorem B1007197 : Blo 992597 1007197 := bbase (se 3 (by rfl) ⟨188849, by rfl⟩ : syracuseStep 1007197 = 377699) (by norm_num)
theorem B1793701 : Blo 992597 1793701 := bbase (se 4 (by rfl) ⟨168159, by rfl⟩ : syracuseStep 1793701 = 336319) (by norm_num)
theorem B2514685 : Blo 992597 2514685 := bbase (se 3 (by rfl) ⟨471503, by rfl⟩ : syracuseStep 2514685 = 943007) (by norm_num)
theorem B2121493 : Blo 992597 2121493 := bbase (se 6 (by rfl) ⟨49722, by rfl⟩ : syracuseStep 2121493 = 99445) (by norm_num)
theorem B2514797 : Blo 992597 2514797 := bbase (se 3 (by rfl) ⟨471524, by rfl⟩ : syracuseStep 2514797 = 943049) (by norm_num)
theorem B1793917 : Blo 992597 1793917 := bbase (se 3 (by rfl) ⟨336359, by rfl⟩ : syracuseStep 1793917 = 672719) (by norm_num)
theorem B5038037 : Blo 992597 5038037 := bbase (se 7 (by rfl) ⟨59039, by rfl⟩ : syracuseStep 5038037 = 118079) (by norm_num)
theorem B2514989 : Blo 992597 2514989 := bbase (se 3 (by rfl) ⟨471560, by rfl⟩ : syracuseStep 2514989 = 943121) (by norm_num)
theorem B2121869 : Blo 992597 2121869 := bbase (se 3 (by rfl) ⟨397850, by rfl⟩ : syracuseStep 2121869 = 795701) (by norm_num)
theorem B4251973 : Blo 992597 4251973 := bbase (se 4 (by rfl) ⟨398622, by rfl⟩ : syracuseStep 4251973 = 797245) (by norm_num)
theorem B1794421 : Blo 992597 1794421 := bbase (se 5 (by rfl) ⟨84113, by rfl⟩ : syracuseStep 1794421 = 168227) (by norm_num)
theorem B2515333 : Blo 992597 2515333 := bbase (se 4 (by rfl) ⟨235812, by rfl⟩ : syracuseStep 2515333 = 471625) (by norm_num)
theorem B1008065 : Blo 992597 1008065 := bbase (se 2 (by rfl) ⟨378024, by rfl⟩ : syracuseStep 1008065 = 756049) (by norm_num)
theorem B2515445 : Blo 992597 2515445 := bbase (se 5 (by rfl) ⟨117911, by rfl⟩ : syracuseStep 2515445 = 235823) (by norm_num)
theorem B2515637 : Blo 992597 2515637 := bbase (se 5 (by rfl) ⟨117920, by rfl⟩ : syracuseStep 2515637 = 235841) (by norm_num)
theorem B1532629 : Blo 992597 1532629 := bbase (se 7 (by rfl) ⟨17960, by rfl⟩ : syracuseStep 1532629 = 35921) (by norm_num)
theorem B1008373 : Blo 992597 1008373 := bbase (se 5 (by rfl) ⟨47267, by rfl⟩ : syracuseStep 1008373 = 94535) (by norm_num)
theorem B2515981 : Blo 992597 2515981 := bbase (se 3 (by rfl) ⟨471746, by rfl⟩ : syracuseStep 2515981 = 943493) (by norm_num)
theorem B1008677 : Blo 992597 1008677 := bbase (se 4 (by rfl) ⟨94563, by rfl⟩ : syracuseStep 1008677 = 189127) (by norm_num)
theorem B2548781 : Blo 992597 2548781 := bbase (se 3 (by rfl) ⟨477896, by rfl⟩ : syracuseStep 2548781 = 955793) (by norm_num)
theorem B2516093 : Blo 992597 2516093 := bbase (se 3 (by rfl) ⟨471767, by rfl⟩ : syracuseStep 2516093 = 943535) (by norm_num)
theorem B1434757 : Blo 992597 1434757 := bbase (se 4 (by rfl) ⟨134508, by rfl⟩ : syracuseStep 1434757 = 269017) (by norm_num)
theorem B5039333 : Blo 992597 5039333 := bbase (se 4 (by rfl) ⟨472437, by rfl⟩ : syracuseStep 5039333 = 944875) (by norm_num)
theorem B1008937 : Blo 992597 1008937 := bbase (se 2 (by rfl) ⟨378351, by rfl⟩ : syracuseStep 1008937 = 756703) (by norm_num)
theorem B2516285 : Blo 992597 2516285 := bbase (se 3 (by rfl) ⟨471803, by rfl⟩ : syracuseStep 2516285 = 943607) (by norm_num)
theorem B7562645 : Blo 992597 7562645 := bbase (se 6 (by rfl) ⟨177249, by rfl⟩ : syracuseStep 7562645 = 354499) (by norm_num)
theorem B1009217 : Blo 992597 1009217 := bbase (se 2 (by rfl) ⟨378456, by rfl⟩ : syracuseStep 1009217 = 756913) (by norm_num)
theorem B5662325 : Blo 992597 5662325 := bbase (se 5 (by rfl) ⟨265421, by rfl⟩ : syracuseStep 5662325 = 530843) (by norm_num)
theorem B2385557 : Blo 992597 2385557 := bbase (se 6 (by rfl) ⟨55911, by rfl⟩ : syracuseStep 2385557 = 111823) (by norm_num)
theorem B2516629 : Blo 992597 2516629 := bbase (se 6 (by rfl) ⟨58983, by rfl⟩ : syracuseStep 2516629 = 117967) (by norm_num)
theorem B2123509 : Blo 992597 2123509 := bbase (se 5 (by rfl) ⟨99539, by rfl⟩ : syracuseStep 2123509 = 199079) (by norm_num)
theorem B2516741 : Blo 992597 2516741 := bbase (se 4 (by rfl) ⟨235944, by rfl⟩ : syracuseStep 2516741 = 471889) (by norm_num)
theorem B4843397 : Blo 992597 4843397 := bbase (se 4 (by rfl) ⟨454068, by rfl⟩ : syracuseStep 4843397 = 908137) (by norm_num)
theorem B1009541 : Blo 992597 1009541 := bbase (se 4 (by rfl) ⟨94644, by rfl⟩ : syracuseStep 1009541 = 189289) (by norm_num)
theorem B1009589 : Blo 992597 1009589 := bbase (se 5 (by rfl) ⟨47324, by rfl⟩ : syracuseStep 1009589 = 94649) (by norm_num)
theorem B1402805 : Blo 992597 1402805 := bbase (se 5 (by rfl) ⟨65756, by rfl⟩ : syracuseStep 1402805 = 131513) (by norm_num)
theorem B2516933 : Blo 992597 2516933 := bbase (se 4 (by rfl) ⟨235962, by rfl⟩ : syracuseStep 2516933 = 471925) (by norm_num)
theorem B4777973 : Blo 992597 4777973 := bbase (se 5 (by rfl) ⟨223967, by rfl⟩ : syracuseStep 4777973 = 447935) (by norm_num)
theorem B2517277 : Blo 992597 2517277 := bbase (se 3 (by rfl) ⟨471989, by rfl⟩ : syracuseStep 2517277 = 943979) (by norm_num)
theorem B2517389 : Blo 992597 2517389 := bbase (se 3 (by rfl) ⟨472010, by rfl⟩ : syracuseStep 2517389 = 944021) (by norm_num)
theorem B1010117 : Blo 992597 1010117 := bbase (se 4 (by rfl) ⟨94698, by rfl⟩ : syracuseStep 1010117 = 189397) (by norm_num)
theorem B5040629 : Blo 992597 5040629 := bbase (se 5 (by rfl) ⟨236279, by rfl⟩ : syracuseStep 5040629 = 472559) (by norm_num)
theorem B2517581 : Blo 992597 2517581 := bbase (se 3 (by rfl) ⟨472046, by rfl⟩ : syracuseStep 2517581 = 944093) (by norm_num)
theorem B2124397 : Blo 992597 2124397 := bbase (se 3 (by rfl) ⟨398324, by rfl⟩ : syracuseStep 2124397 = 796649) (by norm_num)
theorem B1698565 : Blo 992597 1698565 := bbase (se 4 (by rfl) ⟨159240, by rfl⟩ : syracuseStep 1698565 = 318481) (by norm_num)
theorem B2517925 : Blo 992597 2517925 := bbase (se 4 (by rfl) ⟨236055, by rfl⟩ : syracuseStep 2517925 = 472111) (by norm_num)
theorem B2518037 : Blo 992597 2518037 := bbase (se 6 (by rfl) ⟨59016, by rfl⟩ : syracuseStep 2518037 = 118033) (by norm_num)
theorem B5237797 : Blo 992597 5237797 := bbase (se 4 (by rfl) ⟨491043, by rfl⟩ : syracuseStep 5237797 = 982087) (by norm_num)
theorem B2124893 : Blo 992597 2124893 := bbase (se 3 (by rfl) ⟨398417, by rfl⟩ : syracuseStep 2124893 = 796835) (by norm_num)
theorem B2518229 : Blo 992597 2518229 := bbase (se 7 (by rfl) ⟨29510, by rfl⟩ : syracuseStep 2518229 = 59021) (by norm_num)
theorem B2387333 : Blo 992597 2387333 := bbase (se 4 (by rfl) ⟨223812, by rfl⟩ : syracuseStep 2387333 = 447625) (by norm_num)
theorem B2518573 : Blo 992597 2518573 := bbase (se 3 (by rfl) ⟨472232, by rfl⟩ : syracuseStep 2518573 = 944465) (by norm_num)
theorem B1273421 : Blo 992597 1273421 := bbase (se 3 (by rfl) ⟨238766, by rfl⟩ : syracuseStep 1273421 = 477533) (by norm_num)
theorem B2518685 : Blo 992597 2518685 := bbase (se 3 (by rfl) ⟨472253, by rfl⟩ : syracuseStep 2518685 = 944507) (by norm_num)
theorem B5041925 : Blo 992597 5041925 := bbase (se 4 (by rfl) ⟨472680, by rfl⟩ : syracuseStep 5041925 = 945361) (by norm_num)
theorem B2518877 : Blo 992597 2518877 := bbase (se 3 (by rfl) ⟨472289, by rfl⟩ : syracuseStep 2518877 = 944579) (by norm_num)
theorem B6123413 : Blo 992597 6123413 := bbase (se 6 (by rfl) ⟨143517, by rfl⟩ : syracuseStep 6123413 = 287035) (by norm_num)
theorem B2125757 : Blo 992597 2125757 := bbase (se 3 (by rfl) ⟨398579, by rfl⟩ : syracuseStep 2125757 = 797159) (by norm_num)
theorem B2125901 : Blo 992597 2125901 := bbase (se 3 (by rfl) ⟨398606, by rfl⟩ : syracuseStep 2125901 = 797213) (by norm_num)
theorem B2519221 : Blo 992597 2519221 := bbase (se 5 (by rfl) ⟨118088, by rfl⟩ : syracuseStep 2519221 = 236177) (by norm_num)
theorem B1274077 : Blo 992597 1274077 := bbase (se 3 (by rfl) ⟨238889, by rfl⟩ : syracuseStep 1274077 = 477779) (by norm_num)
theorem B1077505 : Blo 992597 1077505 := bbase (se 2 (by rfl) ⟨404064, by rfl⟩ : syracuseStep 1077505 = 808129) (by norm_num)
theorem B2519333 : Blo 992597 2519333 := bbase (se 4 (by rfl) ⟨236187, by rfl⟩ : syracuseStep 2519333 = 472375) (by norm_num)
theorem B2519525 : Blo 992597 2519525 := bbase (se 4 (by rfl) ⟨236205, by rfl⟩ : syracuseStep 2519525 = 472411) (by norm_num)
theorem B2552485 : Blo 992597 2552485 := bbase (se 4 (by rfl) ⟨239295, by rfl⟩ : syracuseStep 2552485 = 478591) (by norm_num)
theorem B4780741 : Blo 992597 4780741 := bbase (se 4 (by rfl) ⟨448194, by rfl⟩ : syracuseStep 4780741 = 896389) (by norm_num)
theorem B2126645 : Blo 992597 2126645 := bbase (se 5 (by rfl) ⟨99686, by rfl⟩ : syracuseStep 2126645 = 199373) (by norm_num)
theorem B2519869 : Blo 992597 2519869 := bbase (se 3 (by rfl) ⟨472475, by rfl⟩ : syracuseStep 2519869 = 944951) (by norm_num)
theorem B2519981 : Blo 992597 2519981 := bbase (se 3 (by rfl) ⟨472496, by rfl⟩ : syracuseStep 2519981 = 944993) (by norm_num)
theorem B2552813 : Blo 992597 2552813 := bbase (se 3 (by rfl) ⟨478652, by rfl⟩ : syracuseStep 2552813 = 957305) (by norm_num)
theorem B1274869 : Blo 992597 1274869 := bbase (se 5 (by rfl) ⟨59759, by rfl⟩ : syracuseStep 1274869 = 119519) (by norm_num)
theorem B2683925 : Blo 992597 2683925 := bbase (se 6 (by rfl) ⟨62904, by rfl⟩ : syracuseStep 2683925 = 125809) (by norm_num)
theorem B5043221 : Blo 992597 5043221 := bbase (se 6 (by rfl) ⟨118200, by rfl⟩ : syracuseStep 5043221 = 236401) (by norm_num)
theorem B2520173 : Blo 992597 2520173 := bbase (se 3 (by rfl) ⟨472532, by rfl⟩ : syracuseStep 2520173 = 945065) (by norm_num)
theorem B4027589 : Blo 992597 4027589 := bbase (se 4 (by rfl) ⟨377586, by rfl⟩ : syracuseStep 4027589 = 755173) (by norm_num)
theorem B1275145 : Blo 992597 1275145 := bbase (se 2 (by rfl) ⟨478179, by rfl⟩ : syracuseStep 1275145 = 956359) (by norm_num)
theorem B2553101 : Blo 992597 2553101 := bbase (se 3 (by rfl) ⟨478706, by rfl⟩ : syracuseStep 2553101 = 957413) (by norm_num)
theorem B2389429 : Blo 992597 2389429 := bbase (se 5 (by rfl) ⟨112004, by rfl⟩ : syracuseStep 2389429 = 224009) (by norm_num)
theorem B2520517 : Blo 992597 2520517 := bbase (se 4 (by rfl) ⟨236298, by rfl⟩ : syracuseStep 2520517 = 472597) (by norm_num)
theorem B2127397 : Blo 992597 2127397 := bbase (se 4 (by rfl) ⟨199443, by rfl⟩ : syracuseStep 2127397 = 398887) (by norm_num)
theorem B2520629 : Blo 992597 2520629 := bbase (se 5 (by rfl) ⟨118154, by rfl⟩ : syracuseStep 2520629 = 236309) (by norm_num)
theorem B2586221 : Blo 992597 2586221 := bbase (se 3 (by rfl) ⟨484916, by rfl⟩ : syracuseStep 2586221 = 969833) (by norm_num)
theorem B2127541 : Blo 992597 2127541 := bbase (se 5 (by rfl) ⟨99728, by rfl⟩ : syracuseStep 2127541 = 199457) (by norm_num)
theorem B2520821 : Blo 992597 2520821 := bbase (se 5 (by rfl) ⟨118163, by rfl⟩ : syracuseStep 2520821 = 236327) (by norm_num)
theorem B2127917 : Blo 992597 2127917 := bbase (se 3 (by rfl) ⟨398984, by rfl⟩ : syracuseStep 2127917 = 797969) (by norm_num)
theorem B1210421 : Blo 992597 1210421 := bbase (se 5 (by rfl) ⟨56738, by rfl⟩ : syracuseStep 1210421 = 113477) (by norm_num)
theorem B2521165 : Blo 992597 2521165 := bbase (se 3 (by rfl) ⟨472718, by rfl⟩ : syracuseStep 2521165 = 945437) (by norm_num)
theorem B2390141 : Blo 992597 2390141 := bbase (se 3 (by rfl) ⟨448151, by rfl⟩ : syracuseStep 2390141 = 896303) (by norm_num)
theorem B8485013 : Blo 992597 8485013 := bbase (se 6 (by rfl) ⟨198867, by rfl⟩ : syracuseStep 8485013 = 397735) (by norm_num)
theorem B2521277 : Blo 992597 2521277 := bbase (se 3 (by rfl) ⟨472739, by rfl⟩ : syracuseStep 2521277 = 945479) (by norm_num)
theorem B2586917 : Blo 992597 2586917 := bbase (se 4 (by rfl) ⟨242523, by rfl⟩ : syracuseStep 2586917 = 485047) (by norm_num)
theorem B5044517 : Blo 992597 5044517 := bbase (se 4 (by rfl) ⟨472923, by rfl⟩ : syracuseStep 5044517 = 945847) (by norm_num)
theorem B3275093 : Blo 992597 3275093 := bbase (se 10 (by rfl) ⟨4797, by rfl⟩ : syracuseStep 3275093 = 9595) (by norm_num)
theorem B1702253 : Blo 992597 1702253 := bbase (se 3 (by rfl) ⟨319172, by rfl⟩ : syracuseStep 1702253 = 638345) (by norm_num)
theorem B2521469 : Blo 992597 2521469 := bbase (se 3 (by rfl) ⟨472775, by rfl⟩ : syracuseStep 2521469 = 945551) (by norm_num)
theorem B2685317 : Blo 992597 2685317 := bbase (se 4 (by rfl) ⟨251748, by rfl⟩ : syracuseStep 2685317 = 503497) (by norm_num)
theorem B2128285 : Blo 992597 2128285 := bbase (se 3 (by rfl) ⟨399053, by rfl⟩ : syracuseStep 2128285 = 798107) (by norm_num)
theorem B2390525 : Blo 992597 2390525 := bbase (se 3 (by rfl) ⟨448223, by rfl⟩ : syracuseStep 2390525 = 896447) (by norm_num)
theorem B2521813 : Blo 992597 2521813 := bbase (se 7 (by rfl) ⟨29552, by rfl⟩ : syracuseStep 2521813 = 59105) (by norm_num)
theorem B2390813 : Blo 992597 2390813 := bbase (se 3 (by rfl) ⟨448277, by rfl⟩ : syracuseStep 2390813 = 896555) (by norm_num)
theorem B2521925 : Blo 992597 2521925 := bbase (se 4 (by rfl) ⟨236430, by rfl⟩ : syracuseStep 2521925 = 472861) (by norm_num)
theorem B2522117 : Blo 992597 2522117 := bbase (se 4 (by rfl) ⟨236448, by rfl⟩ : syracuseStep 2522117 = 472897) (by norm_num)
theorem B6454325 : Blo 992597 6454325 := bbase (se 5 (by rfl) ⟨302546, by rfl⟩ : syracuseStep 6454325 = 605093) (by norm_num)
theorem B1276993 : Blo 992597 1276993 := bbase (se 2 (by rfl) ⟨478872, by rfl⟩ : syracuseStep 1276993 = 957745) (by norm_num)
theorem B1342541 : Blo 992597 1342541 := bbase (se 3 (by rfl) ⟨251726, by rfl⟩ : syracuseStep 1342541 = 503453) (by norm_num)
theorem B1342757 : Blo 992597 1342757 := bbase (se 4 (by rfl) ⟨125883, by rfl⟩ : syracuseStep 1342757 = 251767) (by norm_num)
theorem B2522461 : Blo 992597 2522461 := bbase (se 3 (by rfl) ⟨472961, by rfl⟩ : syracuseStep 2522461 = 945923) (by norm_num)
theorem B2522573 : Blo 992597 2522573 := bbase (se 3 (by rfl) ⟨472982, by rfl⟩ : syracuseStep 2522573 = 945965) (by norm_num)
theorem B15302357 : Blo 992597 15302357 := bbase (se 7 (by rfl) ⟨179324, by rfl⟩ : syracuseStep 15302357 = 358649) (by norm_num)
theorem B4849397 : Blo 992597 4849397 := bbase (se 5 (by rfl) ⟨227315, by rfl⟩ : syracuseStep 4849397 = 454631) (by norm_num)
theorem B1212293 : Blo 992597 1212293 := bbase (se 4 (by rfl) ⟨113652, by rfl⟩ : syracuseStep 1212293 = 227305) (by norm_num)
theorem B2589059 : Blo 992597 2589059 := bstep (se 1 (by rfl) ⟨1941794, by rfl⟩ : syracuseStep 2589059 = 3883589) B3883589
theorem B5669297 : Blo 992597 5669297 := bstep (se 2 (by rfl) ⟨2125986, by rfl⟩ : syracuseStep 5669297 = 4251973) B4251973
theorem B2392561 : Blo 992597 2392561 := bstep (se 2 (by rfl) ⟨897210, by rfl⟩ : syracuseStep 2392561 = 1794421) B1794421
theorem B3769037 : Blo 992597 3769037 := bstep (se 3 (by rfl) ⟨706694, by rfl⟩ : syracuseStep 3769037 = 1413389) B1413389
theorem B27984611 : Blo 992597 27984611 := bstep (se 1 (by rfl) ⟨20988458, by rfl⟩ : syracuseStep 27984611 = 41976917) B41976917
theorem B1344259 : Blo 992597 1344259 := bstep (se 1 (by rfl) ⟨1008194, by rfl⟩ : syracuseStep 1344259 = 2016389) B2016389
theorem B2589475 : Blo 992597 2589475 := bstep (se 1 (by rfl) ⟨1942106, by rfl⟩ : syracuseStep 2589475 = 3884213) B3884213
theorem B1344497 : Blo 992597 1344497 := bstep (se 2 (by rfl) ⟨504186, by rfl⟩ : syracuseStep 1344497 = 1008373) B1008373
theorem B11338865 : Blo 992597 11338865 := bstep (se 2 (by rfl) ⟨4252074, by rfl⟩ : syracuseStep 11338865 = 8504149) B8504149
theorem B2688173 : Blo 992597 2688173 := bstep (se 3 (by rfl) ⟨504032, by rfl⟩ : syracuseStep 2688173 = 1008065) B1008065
theorem B5178595 : Blo 992597 5178595 := bstep (se 1 (by rfl) ⟨3883946, by rfl⟩ : syracuseStep 5178595 = 7767893) B7767893
theorem B13993229 : Blo 992597 13993229 := bstep (se 3 (by rfl) ⟨2623730, by rfl⟩ : syracuseStep 13993229 = 5247461) B5247461
theorem B4850957 : Blo 992597 4850957 := bstep (se 3 (by rfl) ⟨909554, by rfl⟩ : syracuseStep 4850957 = 1819109) B1819109
theorem B5440931 : Blo 992597 5440931 := bstep (se 1 (by rfl) ⟨4080698, by rfl⟩ : syracuseStep 5440931 = 8161397) B8161397
theorem B5375459 : Blo 992597 5375459 := bstep (se 1 (by rfl) ⟨4031594, by rfl⟩ : syracuseStep 5375459 = 8063189) B8063189
theorem B3769841 : Blo 992597 3769841 := bstep (se 2 (by rfl) ⟨1413690, by rfl⟩ : syracuseStep 3769841 = 2827381) B2827381
theorem B3180035 : Blo 992597 3180035 := bstep (se 1 (by rfl) ⟨2385026, by rfl⟩ : syracuseStep 3180035 = 4770053) B4770053
theorem B1345249 : Blo 992597 1345249 := bstep (se 2 (by rfl) ⟨504468, by rfl⟩ : syracuseStep 1345249 = 1008937) B1008937
theorem B5670755 : Blo 992597 5670755 := bstep (se 1 (by rfl) ⟨4253066, by rfl⟩ : syracuseStep 5670755 = 8506133) B8506133
theorem B13633393 : Blo 992597 13633393 := bstep (se 2 (by rfl) ⟨5112522, by rfl⟩ : syracuseStep 13633393 = 10225045) B10225045
theorem B3770509 : Blo 992597 3770509 := bstep (se 3 (by rfl) ⟨706970, by rfl⟩ : syracuseStep 3770509 = 1413941) B1413941
theorem B1509713 : Blo 992597 1509713 := bstep (se 2 (by rfl) ⟨566142, by rfl⟩ : syracuseStep 1509713 = 1132285) B1132285
theorem B10226033 : Blo 992597 10226033 := bstep (se 2 (by rfl) ⟨3834762, by rfl⟩ : syracuseStep 10226033 = 7669525) B7669525
theorem B1116787 : Blo 992597 1116787 := bstep (se 1 (by rfl) ⟨837590, by rfl⟩ : syracuseStep 1116787 = 1675181) B1675181
theorem B5376689 : Blo 992597 5376689 := bstep (se 2 (by rfl) ⟨2016258, by rfl⟩ : syracuseStep 5376689 = 4032517) B4032517
theorem B1116931 : Blo 992597 1116931 := bstep (se 1 (by rfl) ⟨837698, by rfl⟩ : syracuseStep 1116931 = 1675397) B1675397
theorem B2689805 : Blo 992597 2689805 := bstep (se 3 (by rfl) ⟨504338, by rfl⟩ : syracuseStep 2689805 = 1008677) B1008677
theorem B1117075 : Blo 992597 1117075 := bstep (se 1 (by rfl) ⟨837806, by rfl⟩ : syracuseStep 1117075 = 1675613) B1675613
theorem B3771299 : Blo 992597 3771299 := bstep (se 1 (by rfl) ⟨2828474, by rfl⟩ : syracuseStep 3771299 = 5656949) B5656949
theorem B12094435 : Blo 992597 12094435 := bstep (se 1 (by rfl) ⟨9070826, by rfl⟩ : syracuseStep 12094435 = 18141653) B18141653
theorem B1117219 : Blo 992597 1117219 := bstep (se 1 (by rfl) ⟨837914, by rfl⟩ : syracuseStep 1117219 = 1675829) B1675829
theorem B1117363 : Blo 992597 1117363 := bstep (se 1 (by rfl) ⟨838022, by rfl⟩ : syracuseStep 1117363 = 1676045) B1676045
theorem B3181805 : Blo 992597 3181805 := bstep (se 3 (by rfl) ⟨596588, by rfl⟩ : syracuseStep 3181805 = 1193177) B1193177
theorem B1117507 : Blo 992597 1117507 := bstep (se 1 (by rfl) ⟨838130, by rfl⟩ : syracuseStep 1117507 = 1676261) B1676261
theorem B1117651 : Blo 992597 1117651 := bstep (se 1 (by rfl) ⟨838238, by rfl⟩ : syracuseStep 1117651 = 1676477) B1676477
theorem B3771953 : Blo 992597 3771953 := bstep (se 2 (by rfl) ⟨1414482, by rfl⟩ : syracuseStep 3771953 = 2828965) B2828965
theorem B1117795 : Blo 992597 1117795 := bstep (se 1 (by rfl) ⟨838346, by rfl⟩ : syracuseStep 1117795 = 1676693) B1676693
theorem B2264753 : Blo 992597 2264753 := bstep (se 2 (by rfl) ⟨849282, by rfl⟩ : syracuseStep 2264753 = 1698565) B1698565
theorem B1117939 : Blo 992597 1117939 := bstep (se 1 (by rfl) ⟨838454, by rfl⟩ : syracuseStep 1117939 = 1676909) B1676909
theorem B17010485 : Blo 992597 17010485 := bstep (se 5 (by rfl) ⟨797366, by rfl⟩ : syracuseStep 17010485 = 1594733) B1594733
theorem B1675073 : Blo 992597 1675073 := bstep (se 2 (by rfl) ⟨628152, by rfl⟩ : syracuseStep 1675073 = 1256305) B1256305
theorem B1118083 : Blo 992597 1118083 := bstep (se 1 (by rfl) ⟨838562, by rfl⟩ : syracuseStep 1118083 = 1677125) B1677125
theorem B1675201 : Blo 992597 1675201 := bstep (se 2 (by rfl) ⟨628200, by rfl⟩ : syracuseStep 1675201 = 1256401) B1256401
theorem B1675235 : Blo 992597 1675235 := bstep (se 1 (by rfl) ⟨1256426, by rfl⟩ : syracuseStep 1675235 = 2512853) B2512853
theorem B1118227 : Blo 992597 1118227 := bstep (se 1 (by rfl) ⟨838670, by rfl⟩ : syracuseStep 1118227 = 1677341) B1677341
theorem B6983729 : Blo 992597 6983729 := bstep (se 2 (by rfl) ⟨2618898, by rfl⟩ : syracuseStep 6983729 = 5237797) B5237797
theorem B28643381 : Blo 992597 28643381 := bstep (se 5 (by rfl) ⟨1342658, by rfl⟩ : syracuseStep 28643381 = 2685317) B2685317
theorem B2265155 : Blo 992597 2265155 := bstep (se 1 (by rfl) ⟨1698866, by rfl⟩ : syracuseStep 2265155 = 3397733) B3397733
theorem B1675363 : Blo 992597 1675363 := bstep (se 1 (by rfl) ⟨1256522, by rfl⟩ : syracuseStep 1675363 = 2513045) B2513045
theorem B1118371 : Blo 992597 1118371 := bstep (se 1 (by rfl) ⟨838778, by rfl⟩ : syracuseStep 1118371 = 1677557) B1677557
theorem B2691245 : Blo 992597 2691245 := bstep (se 3 (by rfl) ⟨504608, by rfl⟩ : syracuseStep 2691245 = 1009217) B1009217
theorem B1675505 : Blo 992597 1675505 := bstep (se 2 (by rfl) ⟨628314, by rfl⟩ : syracuseStep 1675505 = 1256629) B1256629
theorem B1118515 : Blo 992597 1118515 := bstep (se 1 (by rfl) ⟨838886, by rfl⟩ : syracuseStep 1118515 = 1677773) B1677773
theorem B1675633 : Blo 992597 1675633 := bstep (se 2 (by rfl) ⟨628362, by rfl⟩ : syracuseStep 1675633 = 1256725) B1256725
theorem B1675667 : Blo 992597 1675667 := bstep (se 1 (by rfl) ⟨1256750, by rfl⟩ : syracuseStep 1675667 = 2513501) B2513501
theorem B1118659 : Blo 992597 1118659 := bstep (se 1 (by rfl) ⟨838994, by rfl⟩ : syracuseStep 1118659 = 1677989) B1677989
theorem B7180741 : Blo 992597 7180741 := bstep (se 4 (by rfl) ⟨673194, by rfl⟩ : syracuseStep 7180741 = 1346389) B1346389
theorem B7541261 : Blo 992597 7541261 := bstep (se 3 (by rfl) ⟨1413986, by rfl⟩ : syracuseStep 7541261 = 2827973) B2827973
theorem B1675795 : Blo 992597 1675795 := bstep (se 1 (by rfl) ⟨1256846, by rfl⟩ : syracuseStep 1675795 = 2513693) B2513693
theorem B1118803 : Blo 992597 1118803 := bstep (se 1 (by rfl) ⟨839102, by rfl⟩ : syracuseStep 1118803 = 1678205) B1678205
theorem B7180913 : Blo 992597 7180913 := bstep (se 2 (by rfl) ⟨2692842, by rfl⟩ : syracuseStep 7180913 = 5385685) B5385685
theorem B1675937 : Blo 992597 1675937 := bstep (se 2 (by rfl) ⟨628476, by rfl⟩ : syracuseStep 1675937 = 1256953) B1256953
theorem B1118947 : Blo 992597 1118947 := bstep (se 1 (by rfl) ⟨839210, by rfl⟩ : syracuseStep 1118947 = 1678421) B1678421
theorem B1676065 : Blo 992597 1676065 := bstep (se 2 (by rfl) ⟨628524, by rfl⟩ : syracuseStep 1676065 = 1257049) B1257049
theorem B1676099 : Blo 992597 1676099 := bstep (se 1 (by rfl) ⟨1257074, by rfl⟩ : syracuseStep 1676099 = 2514149) B2514149
theorem B1119091 : Blo 992597 1119091 := bstep (se 1 (by rfl) ⟨839318, by rfl⟩ : syracuseStep 1119091 = 1678637) B1678637
theorem B1676227 : Blo 992597 1676227 := bstep (se 1 (by rfl) ⟨1257170, by rfl⟩ : syracuseStep 1676227 = 2514341) B2514341
theorem B3773411 : Blo 992597 3773411 := bstep (se 1 (by rfl) ⟨2830058, by rfl⟩ : syracuseStep 3773411 = 5660117) B5660117
theorem B3773425 : Blo 992597 3773425 := bstep (se 2 (by rfl) ⟨1415034, by rfl⟩ : syracuseStep 3773425 = 2830069) B2830069
theorem B1119235 : Blo 992597 1119235 := bstep (se 1 (by rfl) ⟨839426, by rfl⟩ : syracuseStep 1119235 = 1678853) B1678853
theorem B5673989 : Blo 992597 5673989 := bstep (se 4 (by rfl) ⟨531936, by rfl⟩ : syracuseStep 5673989 = 1063873) B1063873
theorem B2692109 : Blo 992597 2692109 := bstep (se 3 (by rfl) ⟨504770, by rfl⟩ : syracuseStep 2692109 = 1009541) B1009541
theorem B1676369 : Blo 992597 1676369 := bstep (se 2 (by rfl) ⟨628638, by rfl⟩ : syracuseStep 1676369 = 1257277) B1257277
theorem B2233457 : Blo 992597 2233457 := bstep (se 2 (by rfl) ⟨837546, by rfl⟩ : syracuseStep 2233457 = 1675093) B1675093
theorem B6362225 : Blo 992597 6362225 := bstep (se 2 (by rfl) ⟨2385834, by rfl⟩ : syracuseStep 6362225 = 4771669) B4771669
theorem B2233475 : Blo 992597 2233475 := bstep (se 1 (by rfl) ⟨1675106, by rfl⟩ : syracuseStep 2233475 = 3350213) B3350213
theorem B3740813 : Blo 992597 3740813 := bstep (se 3 (by rfl) ⟨701402, by rfl⟩ : syracuseStep 3740813 = 1402805) B1402805
theorem B1119379 : Blo 992597 1119379 := bstep (se 1 (by rfl) ⟨839534, by rfl⟩ : syracuseStep 1119379 = 1679069) B1679069
theorem B1676497 : Blo 992597 1676497 := bstep (se 2 (by rfl) ⟨628686, by rfl⟩ : syracuseStep 1676497 = 1257373) B1257373
theorem B1676531 : Blo 992597 1676531 := bstep (se 1 (by rfl) ⟨1257398, by rfl⟩ : syracuseStep 1676531 = 2514797) B2514797
theorem B1119523 : Blo 992597 1119523 := bstep (se 1 (by rfl) ⟨839642, by rfl⟩ : syracuseStep 1119523 = 1679285) B1679285
theorem B2692433 : Blo 992597 2692433 := bstep (se 2 (by rfl) ⟨1009662, by rfl⟩ : syracuseStep 2692433 = 2019325) B2019325
theorem B1676659 : Blo 992597 1676659 := bstep (se 1 (by rfl) ⟨1257494, by rfl⟩ : syracuseStep 1676659 = 2514989) B2514989
theorem B2233745 : Blo 992597 2233745 := bstep (se 2 (by rfl) ⟨837654, by rfl⟩ : syracuseStep 2233745 = 1675309) B1675309
theorem B2233763 : Blo 992597 2233763 := bstep (se 1 (by rfl) ⟨1675322, by rfl⟩ : syracuseStep 2233763 = 3350645) B3350645
theorem B1414579 : Blo 992597 1414579 := bstep (se 1 (by rfl) ⟨1060934, by rfl⟩ : syracuseStep 1414579 = 2121869) B2121869
theorem B1119667 : Blo 992597 1119667 := bstep (se 1 (by rfl) ⟨839750, by rfl⟩ : syracuseStep 1119667 = 1679501) B1679501
theorem B5674445 : Blo 992597 5674445 := bstep (se 3 (by rfl) ⟨1063958, by rfl⟩ : syracuseStep 5674445 = 2127917) B2127917
theorem B1676801 : Blo 992597 1676801 := bstep (se 2 (by rfl) ⟨628800, by rfl⟩ : syracuseStep 1676801 = 1257601) B1257601
theorem B1119811 : Blo 992597 1119811 := bstep (se 1 (by rfl) ⟨839858, by rfl⟩ : syracuseStep 1119811 = 1679717) B1679717
theorem B1676929 : Blo 992597 1676929 := bstep (se 2 (by rfl) ⟨628848, by rfl⟩ : syracuseStep 1676929 = 1257697) B1257697
theorem B1676963 : Blo 992597 1676963 := bstep (se 1 (by rfl) ⟨1257722, by rfl⟩ : syracuseStep 1676963 = 2515445) B2515445
theorem B2234033 : Blo 992597 2234033 := bstep (se 2 (by rfl) ⟨837762, by rfl⟩ : syracuseStep 2234033 = 1675525) B1675525
theorem B2234051 : Blo 992597 2234051 := bstep (se 1 (by rfl) ⟨1675538, by rfl⟩ : syracuseStep 2234051 = 3351077) B3351077
theorem B1119955 : Blo 992597 1119955 := bstep (se 1 (by rfl) ⟨839966, by rfl⟩ : syracuseStep 1119955 = 1679933) B1679933
theorem B1513217 : Blo 992597 1513217 := bstep (se 2 (by rfl) ⟨567456, by rfl⟩ : syracuseStep 1513217 = 1134913) B1134913
theorem B1677091 : Blo 992597 1677091 := bstep (se 1 (by rfl) ⟨1257818, by rfl⟩ : syracuseStep 1677091 = 2515637) B2515637
theorem B5183281 : Blo 992597 5183281 := bstep (se 2 (by rfl) ⟨1943730, by rfl⟩ : syracuseStep 5183281 = 3887461) B3887461
theorem B4527971 : Blo 992597 4527971 := bstep (se 1 (by rfl) ⟨3395978, by rfl⟩ : syracuseStep 4527971 = 6791957) B6791957
theorem B1120099 : Blo 992597 1120099 := bstep (se 1 (by rfl) ⟨840074, by rfl⟩ : syracuseStep 1120099 = 1680149) B1680149
theorem B1677233 : Blo 992597 1677233 := bstep (se 2 (by rfl) ⟨628962, by rfl⟩ : syracuseStep 1677233 = 1257925) B1257925
theorem B2234321 : Blo 992597 2234321 := bstep (se 2 (by rfl) ⟨837870, by rfl⟩ : syracuseStep 2234321 = 1675741) B1675741
theorem B2234339 : Blo 992597 2234339 := bstep (se 1 (by rfl) ⟨1675754, by rfl⟩ : syracuseStep 2234339 = 3351509) B3351509
theorem B1120243 : Blo 992597 1120243 := bstep (se 1 (by rfl) ⟨840182, by rfl⟩ : syracuseStep 1120243 = 1680365) B1680365
theorem B1677361 : Blo 992597 1677361 := bstep (se 2 (by rfl) ⟨629010, by rfl⟩ : syracuseStep 1677361 = 1258021) B1258021
theorem B1677395 : Blo 992597 1677395 := bstep (se 1 (by rfl) ⟨1258046, by rfl⟩ : syracuseStep 1677395 = 2516093) B2516093
theorem B1120387 : Blo 992597 1120387 := bstep (se 1 (by rfl) ⟨840290, by rfl⟩ : syracuseStep 1120387 = 1680581) B1680581
theorem B1677523 : Blo 992597 1677523 := bstep (se 1 (by rfl) ⟨1258142, by rfl⟩ : syracuseStep 1677523 = 2516285) B2516285
theorem B2234609 : Blo 992597 2234609 := bstep (se 2 (by rfl) ⟨837978, by rfl⟩ : syracuseStep 2234609 = 1675957) B1675957
theorem B2234627 : Blo 992597 2234627 := bstep (se 1 (by rfl) ⟨1675970, by rfl⟩ : syracuseStep 2234627 = 3351941) B3351941
theorem B1120531 : Blo 992597 1120531 := bstep (se 1 (by rfl) ⟨840398, by rfl⟩ : syracuseStep 1120531 = 1680797) B1680797
theorem B1677665 : Blo 992597 1677665 := bstep (se 2 (by rfl) ⟨629124, by rfl⟩ : syracuseStep 1677665 = 1258249) B1258249
theorem B3774883 : Blo 992597 3774883 := bstep (se 1 (by rfl) ⟨2831162, by rfl⟩ : syracuseStep 3774883 = 5662325) B5662325
theorem B1120675 : Blo 992597 1120675 := bstep (se 1 (by rfl) ⟨840506, by rfl⟩ : syracuseStep 1120675 = 1681013) B1681013
theorem B1677793 : Blo 992597 1677793 := bstep (se 2 (by rfl) ⟨629172, by rfl⟩ : syracuseStep 1677793 = 1258345) B1258345
theorem B1677827 : Blo 992597 1677827 := bstep (se 1 (by rfl) ⟨1258370, by rfl⟩ : syracuseStep 1677827 = 2516741) B2516741
theorem B2693645 : Blo 992597 2693645 := bstep (se 3 (by rfl) ⟨505058, by rfl⟩ : syracuseStep 2693645 = 1010117) B1010117
theorem B2234897 : Blo 992597 2234897 := bstep (se 2 (by rfl) ⟨838086, by rfl⟩ : syracuseStep 2234897 = 1676173) B1676173
theorem B1415713 : Blo 992597 1415713 := bstep (se 2 (by rfl) ⟨530892, by rfl⟩ : syracuseStep 1415713 = 1061785) B1061785
theorem B2234915 : Blo 992597 2234915 := bstep (se 1 (by rfl) ⟨1676186, by rfl⟩ : syracuseStep 2234915 = 3352373) B3352373
theorem B1120819 : Blo 992597 1120819 := bstep (se 1 (by rfl) ⟨840614, by rfl⟩ : syracuseStep 1120819 = 1681229) B1681229
theorem B1415809 : Blo 992597 1415809 := bstep (se 2 (by rfl) ⟨530928, by rfl⟩ : syracuseStep 1415809 = 1061857) B1061857
theorem B1677955 : Blo 992597 1677955 := bstep (se 1 (by rfl) ⟨1258466, by rfl⟩ : syracuseStep 1677955 = 2516933) B2516933
theorem B7182989 : Blo 992597 7182989 := bstep (se 3 (by rfl) ⟨1346810, by rfl⟩ : syracuseStep 7182989 = 2693621) B2693621
theorem B3185315 : Blo 992597 3185315 := bstep (se 1 (by rfl) ⟨2388986, by rfl⟩ : syracuseStep 3185315 = 4777973) B4777973
theorem B1120963 : Blo 992597 1120963 := bstep (se 1 (by rfl) ⟨840722, by rfl⟩ : syracuseStep 1120963 = 1681445) B1681445
theorem B1678097 : Blo 992597 1678097 := bstep (se 2 (by rfl) ⟨629286, by rfl⟩ : syracuseStep 1678097 = 1258573) B1258573
theorem B2235185 : Blo 992597 2235185 := bstep (se 2 (by rfl) ⟨838194, by rfl⟩ : syracuseStep 2235185 = 1676389) B1676389
theorem B2235203 : Blo 992597 2235203 := bstep (se 1 (by rfl) ⟨1676402, by rfl⟩ : syracuseStep 2235203 = 3352805) B3352805
theorem B1121107 : Blo 992597 1121107 := bstep (se 1 (by rfl) ⟨840830, by rfl⟩ : syracuseStep 1121107 = 1681661) B1681661
theorem B1678225 : Blo 992597 1678225 := bstep (se 2 (by rfl) ⟨629334, by rfl⟩ : syracuseStep 1678225 = 1258669) B1258669
theorem B1678259 : Blo 992597 1678259 := bstep (se 1 (by rfl) ⟨1258694, by rfl⟩ : syracuseStep 1678259 = 2517389) B2517389
theorem B1678387 : Blo 992597 1678387 := bstep (se 1 (by rfl) ⟨1258790, by rfl⟩ : syracuseStep 1678387 = 2517581) B2517581
theorem B2235473 : Blo 992597 2235473 := bstep (se 2 (by rfl) ⟨838302, by rfl⟩ : syracuseStep 2235473 = 1676605) B1676605
theorem B2235491 : Blo 992597 2235491 := bstep (se 1 (by rfl) ⟨1676618, by rfl⟩ : syracuseStep 2235491 = 3353237) B3353237
theorem B1416305 : Blo 992597 1416305 := bstep (se 2 (by rfl) ⟨531114, by rfl⟩ : syracuseStep 1416305 = 1062229) B1062229
theorem B1678529 : Blo 992597 1678529 := bstep (se 2 (by rfl) ⟨629448, by rfl⟩ : syracuseStep 1678529 = 1258897) B1258897
theorem B3185905 : Blo 992597 3185905 := bstep (se 2 (by rfl) ⟨1194714, by rfl⟩ : syracuseStep 3185905 = 2389429) B2389429
theorem B1678657 : Blo 992597 1678657 := bstep (se 2 (by rfl) ⟨629496, by rfl⟩ : syracuseStep 1678657 = 1258993) B1258993
theorem B1678691 : Blo 992597 1678691 := bstep (se 1 (by rfl) ⟨1259018, by rfl⟩ : syracuseStep 1678691 = 2518037) B2518037
theorem B7544177 : Blo 992597 7544177 := bstep (se 2 (by rfl) ⟨2829066, by rfl⟩ : syracuseStep 7544177 = 5658133) B5658133
theorem B2235761 : Blo 992597 2235761 := bstep (se 2 (by rfl) ⟨838410, by rfl⟩ : syracuseStep 2235761 = 1676821) B1676821
theorem B2235779 : Blo 992597 2235779 := bstep (se 1 (by rfl) ⟨1676834, by rfl⟩ : syracuseStep 2235779 = 3353669) B3353669
theorem B1678819 : Blo 992597 1678819 := bstep (se 1 (by rfl) ⟨1259114, by rfl⟩ : syracuseStep 1678819 = 2518229) B2518229
theorem B3350051 : Blo 992597 3350051 := bstep (se 1 (by rfl) ⟨2512538, by rfl⟩ : syracuseStep 3350051 = 5025077) B5025077
theorem B1678961 : Blo 992597 1678961 := bstep (se 2 (by rfl) ⟨629610, by rfl⟩ : syracuseStep 1678961 = 1259221) B1259221
theorem B2236049 : Blo 992597 2236049 := bstep (se 2 (by rfl) ⟨838518, by rfl⟩ : syracuseStep 2236049 = 1677037) B1677037
theorem B2236067 : Blo 992597 2236067 := bstep (se 1 (by rfl) ⟨1677050, by rfl⟩ : syracuseStep 2236067 = 3354101) B3354101
theorem B3022541 : Blo 992597 3022541 := bstep (se 3 (by rfl) ⟨566726, by rfl⟩ : syracuseStep 3022541 = 1133453) B1133453
theorem B1679089 : Blo 992597 1679089 := bstep (se 2 (by rfl) ⟨629658, by rfl⟩ : syracuseStep 1679089 = 1259317) B1259317
theorem B1679123 : Blo 992597 1679123 := bstep (se 1 (by rfl) ⟨1259342, by rfl⟩ : syracuseStep 1679123 = 2518685) B2518685
theorem B3350321 : Blo 992597 3350321 := bstep (se 2 (by rfl) ⟨1256370, by rfl⟩ : syracuseStep 3350321 = 2512741) B2512741
theorem B1679251 : Blo 992597 1679251 := bstep (se 1 (by rfl) ⟨1259438, by rfl⟩ : syracuseStep 1679251 = 2518877) B2518877
theorem B2236337 : Blo 992597 2236337 := bstep (se 2 (by rfl) ⟨838626, by rfl⟩ : syracuseStep 2236337 = 1677253) B1677253
theorem B2236355 : Blo 992597 2236355 := bstep (se 1 (by rfl) ⟨1677266, by rfl⟩ : syracuseStep 2236355 = 3354533) B3354533
theorem B1417171 : Blo 992597 1417171 := bstep (se 1 (by rfl) ⟨1062878, by rfl⟩ : syracuseStep 1417171 = 2125757) B2125757
theorem B4530161 : Blo 992597 4530161 := bstep (se 2 (by rfl) ⟨1698810, by rfl⟩ : syracuseStep 4530161 = 3397621) B3397621
theorem B1679393 : Blo 992597 1679393 := bstep (se 2 (by rfl) ⟨629772, by rfl⟩ : syracuseStep 1679393 = 1259545) B1259545
theorem B1417267 : Blo 992597 1417267 := bstep (se 1 (by rfl) ⟨1062950, by rfl⟩ : syracuseStep 1417267 = 2125901) B2125901
theorem B1679521 : Blo 992597 1679521 := bstep (se 2 (by rfl) ⟨629820, by rfl⟩ : syracuseStep 1679521 = 1259641) B1259641
theorem B1679555 : Blo 992597 1679555 := bstep (se 1 (by rfl) ⟨1259666, by rfl⟩ : syracuseStep 1679555 = 2519333) B2519333
theorem B3580109 : Blo 992597 3580109 := bstep (se 3 (by rfl) ⟨671270, by rfl⟩ : syracuseStep 3580109 = 1342541) B1342541
theorem B2236625 : Blo 992597 2236625 := bstep (se 2 (by rfl) ⟨838734, by rfl⟩ : syracuseStep 2236625 = 1677469) B1677469
theorem B2236643 : Blo 992597 2236643 := bstep (se 1 (by rfl) ⟨1677482, by rfl⟩ : syracuseStep 2236643 = 3354965) B3354965
theorem B1679683 : Blo 992597 1679683 := bstep (se 1 (by rfl) ⟨1259762, by rfl⟩ : syracuseStep 1679683 = 2519525) B2519525
theorem B3350861 : Blo 992597 3350861 := bstep (se 3 (by rfl) ⟨628286, by rfl⟩ : syracuseStep 3350861 = 1256573) B1256573
theorem B3350915 : Blo 992597 3350915 := bstep (se 1 (by rfl) ⟨2513186, by rfl⟩ : syracuseStep 3350915 = 5026373) B5026373
theorem B1679825 : Blo 992597 1679825 := bstep (se 2 (by rfl) ⟨629934, by rfl⟩ : syracuseStep 1679825 = 1259869) B1259869
theorem B2236913 : Blo 992597 2236913 := bstep (se 2 (by rfl) ⟨838842, by rfl⟩ : syracuseStep 2236913 = 1677685) B1677685
theorem B3023345 : Blo 992597 3023345 := bstep (se 2 (by rfl) ⟨1133754, by rfl⟩ : syracuseStep 3023345 = 2267509) B2267509
theorem B2236931 : Blo 992597 2236931 := bstep (se 1 (by rfl) ⟨1677698, by rfl⟩ : syracuseStep 2236931 = 3355397) B3355397
theorem B1417763 : Blo 992597 1417763 := bstep (se 1 (by rfl) ⟨1063322, by rfl⟩ : syracuseStep 1417763 = 2126645) B2126645
theorem B31007285 : Blo 992597 31007285 := bstep (se 5 (by rfl) ⟨1453466, by rfl⟩ : syracuseStep 31007285 = 2906933) B2906933
theorem B3777101 : Blo 992597 3777101 := bstep (se 3 (by rfl) ⟨708206, by rfl⟩ : syracuseStep 3777101 = 1416413) B1416413
theorem B1679953 : Blo 992597 1679953 := bstep (se 2 (by rfl) ⟨629982, by rfl⟩ : syracuseStep 1679953 = 1259965) B1259965
theorem B1679987 : Blo 992597 1679987 := bstep (se 1 (by rfl) ⟨1259990, by rfl⟩ : syracuseStep 1679987 = 2519981) B2519981
theorem B3351185 : Blo 992597 3351185 := bstep (se 2 (by rfl) ⟨1256694, by rfl⟩ : syracuseStep 3351185 = 2513389) B2513389
theorem B1680115 : Blo 992597 1680115 := bstep (se 1 (by rfl) ⟨1260086, by rfl⟩ : syracuseStep 1680115 = 2520173) B2520173
theorem B3580685 : Blo 992597 3580685 := bstep (se 3 (by rfl) ⟨671378, by rfl⟩ : syracuseStep 3580685 = 1342757) B1342757
theorem B2237201 : Blo 992597 2237201 := bstep (se 2 (by rfl) ⟨838950, by rfl⟩ : syracuseStep 2237201 = 1677901) B1677901
theorem B2237219 : Blo 992597 2237219 := bstep (se 1 (by rfl) ⟨1677914, by rfl⟩ : syracuseStep 2237219 = 3355829) B3355829
theorem B1680257 : Blo 992597 1680257 := bstep (se 2 (by rfl) ⟨630096, by rfl⟩ : syracuseStep 1680257 = 1260193) B1260193
theorem B2827153 : Blo 992597 2827153 := bstep (se 2 (by rfl) ⟨1060182, by rfl⟩ : syracuseStep 2827153 = 2120365) B2120365
theorem B6038513 : Blo 992597 6038513 := bstep (se 2 (by rfl) ⟨2264442, by rfl⟩ : syracuseStep 6038513 = 4528885) B4528885
theorem B1680385 : Blo 992597 1680385 := bstep (se 2 (by rfl) ⟨630144, by rfl⟩ : syracuseStep 1680385 = 1260289) B1260289
theorem B6366221 : Blo 992597 6366221 := bstep (se 3 (by rfl) ⟨1193666, by rfl⟩ : syracuseStep 6366221 = 2387333) B2387333
theorem B1680419 : Blo 992597 1680419 := bstep (se 1 (by rfl) ⟨1260314, by rfl⟩ : syracuseStep 1680419 = 2520629) B2520629
theorem B2237489 : Blo 992597 2237489 := bstep (se 2 (by rfl) ⟨839058, by rfl⟩ : syracuseStep 2237489 = 1678117) B1678117
theorem B2237507 : Blo 992597 2237507 := bstep (se 1 (by rfl) ⟨1678130, by rfl⟩ : syracuseStep 2237507 = 3356261) B3356261
theorem B1418401 : Blo 992597 1418401 := bstep (se 2 (by rfl) ⟨531900, by rfl⟩ : syracuseStep 1418401 = 1063801) B1063801
theorem B1680547 : Blo 992597 1680547 := bstep (se 1 (by rfl) ⟨1260410, by rfl⟩ : syracuseStep 1680547 = 2520821) B2520821
theorem B3351725 : Blo 992597 3351725 := bstep (se 3 (by rfl) ⟨628448, by rfl⟩ : syracuseStep 3351725 = 1256897) B1256897
theorem B3351779 : Blo 992597 3351779 := bstep (se 1 (by rfl) ⟨2513834, by rfl⟩ : syracuseStep 3351779 = 5027669) B5027669
theorem B1680689 : Blo 992597 1680689 := bstep (se 2 (by rfl) ⟨630258, by rfl⟩ : syracuseStep 1680689 = 1260517) B1260517
theorem B2237777 : Blo 992597 2237777 := bstep (se 2 (by rfl) ⟨839166, by rfl⟩ : syracuseStep 2237777 = 1678333) B1678333
theorem B992611 : Blo 992597 992611 := bstep (se 1 (by rfl) ⟨744458, by rfl⟩ : syracuseStep 992611 = 1488917) B1488917
theorem B2237795 : Blo 992597 2237795 := bstep (se 1 (by rfl) ⟨1678346, by rfl⟩ : syracuseStep 2237795 = 3356693) B3356693
theorem B5383523 : Blo 992597 5383523 := bstep (se 1 (by rfl) ⟨4037642, by rfl⟩ : syracuseStep 5383523 = 8075285) B8075285
theorem B992627 : Blo 992597 992627 := bstep (se 1 (by rfl) ⟨744470, by rfl⟩ : syracuseStep 992627 = 1488941) B1488941
theorem B992643 : Blo 992597 992643 := bstep (se 1 (by rfl) ⟨744482, by rfl⟩ : syracuseStep 992643 = 1488965) B1488965
theorem B992659 : Blo 992597 992659 := bstep (se 1 (by rfl) ⟨744494, by rfl⟩ : syracuseStep 992659 = 1488989) B1488989
theorem B992675 : Blo 992597 992675 := bstep (se 1 (by rfl) ⟨744506, by rfl⟩ : syracuseStep 992675 = 1489013) B1489013
theorem B1680817 : Blo 992597 1680817 := bstep (se 2 (by rfl) ⟨630306, by rfl⟩ : syracuseStep 1680817 = 1260613) B1260613
theorem B992691 : Blo 992597 992691 := bstep (se 1 (by rfl) ⟨744518, by rfl⟩ : syracuseStep 992691 = 1489037) B1489037
theorem B992707 : Blo 992597 992707 := bstep (se 1 (by rfl) ⟨744530, by rfl⟩ : syracuseStep 992707 = 1489061) B1489061
theorem B25798085 : Blo 992597 25798085 := bstep (se 4 (by rfl) ⟨2418570, by rfl⟩ : syracuseStep 25798085 = 4837141) B4837141
theorem B992723 : Blo 992597 992723 := bstep (se 1 (by rfl) ⟨744542, by rfl⟩ : syracuseStep 992723 = 1489085) B1489085
theorem B1680851 : Blo 992597 1680851 := bstep (se 1 (by rfl) ⟨1260638, by rfl⟩ : syracuseStep 1680851 = 2521277) B2521277
theorem B992739 : Blo 992597 992739 := bstep (se 1 (by rfl) ⟨744554, by rfl⟩ : syracuseStep 992739 = 1489109) B1489109
theorem B3352049 : Blo 992597 3352049 := bstep (se 2 (by rfl) ⟨1257018, by rfl⟩ : syracuseStep 3352049 = 2514037) B2514037
theorem B4531697 : Blo 992597 4531697 := bstep (se 2 (by rfl) ⟨1699386, by rfl⟩ : syracuseStep 4531697 = 3398773) B3398773
theorem B992755 : Blo 992597 992755 := bstep (se 1 (by rfl) ⟨744566, by rfl⟩ : syracuseStep 992755 = 1489133) B1489133
theorem B1418737 : Blo 992597 1418737 := bstep (se 2 (by rfl) ⟨532026, by rfl⟩ : syracuseStep 1418737 = 1064053) B1064053
theorem B992771 : Blo 992597 992771 := bstep (se 1 (by rfl) ⟨744578, by rfl⟩ : syracuseStep 992771 = 1489157) B1489157
theorem B992787 : Blo 992597 992787 := bstep (se 1 (by rfl) ⟨744590, by rfl⟩ : syracuseStep 992787 = 1489181) B1489181
theorem B992803 : Blo 992597 992803 := bstep (se 1 (by rfl) ⟨744602, by rfl⟩ : syracuseStep 992803 = 1489205) B1489205
theorem B992819 : Blo 992597 992819 := bstep (se 1 (by rfl) ⟨744614, by rfl⟩ : syracuseStep 992819 = 1489229) B1489229
theorem B992835 : Blo 992597 992835 := bstep (se 1 (by rfl) ⟨744626, by rfl⟩ : syracuseStep 992835 = 1489253) B1489253
theorem B992851 : Blo 992597 992851 := bstep (se 1 (by rfl) ⟨744638, by rfl⟩ : syracuseStep 992851 = 1489277) B1489277
theorem B1680979 : Blo 992597 1680979 := bstep (se 1 (by rfl) ⟨1260734, by rfl⟩ : syracuseStep 1680979 = 2521469) B2521469
theorem B992867 : Blo 992597 992867 := bstep (se 1 (by rfl) ⟨744650, by rfl⟩ : syracuseStep 992867 = 1489301) B1489301
theorem B2238065 : Blo 992597 2238065 := bstep (se 2 (by rfl) ⟨839274, by rfl⟩ : syracuseStep 2238065 = 1678549) B1678549
theorem B992883 : Blo 992597 992883 := bstep (se 1 (by rfl) ⟨744662, by rfl⟩ : syracuseStep 992883 = 1489325) B1489325
theorem B992899 : Blo 992597 992899 := bstep (se 1 (by rfl) ⟨744674, by rfl⟩ : syracuseStep 992899 = 1489349) B1489349
theorem B2238083 : Blo 992597 2238083 := bstep (se 1 (by rfl) ⟨1678562, by rfl⟩ : syracuseStep 2238083 = 3357125) B3357125
theorem B992915 : Blo 992597 992915 := bstep (se 1 (by rfl) ⟨744686, by rfl⟩ : syracuseStep 992915 = 1489373) B1489373
theorem B992931 : Blo 992597 992931 := bstep (se 1 (by rfl) ⟨744698, by rfl⟩ : syracuseStep 992931 = 1489397) B1489397
theorem B992947 : Blo 992597 992947 := bstep (se 1 (by rfl) ⟨744710, by rfl⟩ : syracuseStep 992947 = 1489421) B1489421
theorem B992963 : Blo 992597 992963 := bstep (se 1 (by rfl) ⟨744722, by rfl⟩ : syracuseStep 992963 = 1489445) B1489445
theorem B992979 : Blo 992597 992979 := bstep (se 1 (by rfl) ⟨744734, by rfl⟩ : syracuseStep 992979 = 1489469) B1489469
theorem B1681121 : Blo 992597 1681121 := bstep (se 2 (by rfl) ⟨630420, by rfl⟩ : syracuseStep 1681121 = 1260841) B1260841
theorem B992995 : Blo 992597 992995 := bstep (se 1 (by rfl) ⟨744746, by rfl⟩ : syracuseStep 992995 = 1489493) B1489493
theorem B3024611 : Blo 992597 3024611 := bstep (se 1 (by rfl) ⟨2268458, by rfl⟩ : syracuseStep 3024611 = 4536917) B4536917
theorem B993011 : Blo 992597 993011 := bstep (se 1 (by rfl) ⟨744758, by rfl⟩ : syracuseStep 993011 = 1489517) B1489517
theorem B993027 : Blo 992597 993027 := bstep (se 1 (by rfl) ⟨744770, by rfl⟩ : syracuseStep 993027 = 1489541) B1489541
theorem B993043 : Blo 992597 993043 := bstep (se 1 (by rfl) ⟨744782, by rfl⟩ : syracuseStep 993043 = 1489565) B1489565
theorem B993059 : Blo 992597 993059 := bstep (se 1 (by rfl) ⟨744794, by rfl⟩ : syracuseStep 993059 = 1489589) B1489589
theorem B993075 : Blo 992597 993075 := bstep (se 1 (by rfl) ⟨744806, by rfl⟩ : syracuseStep 993075 = 1489613) B1489613
theorem B993091 : Blo 992597 993091 := bstep (se 1 (by rfl) ⟨744818, by rfl⟩ : syracuseStep 993091 = 1489637) B1489637
theorem B993107 : Blo 992597 993107 := bstep (se 1 (by rfl) ⟨744830, by rfl⟩ : syracuseStep 993107 = 1489661) B1489661
theorem B1681249 : Blo 992597 1681249 := bstep (se 2 (by rfl) ⟨630468, by rfl⟩ : syracuseStep 1681249 = 1260937) B1260937
theorem B993123 : Blo 992597 993123 := bstep (se 1 (by rfl) ⟨744842, by rfl⟩ : syracuseStep 993123 = 1489685) B1489685
theorem B993139 : Blo 992597 993139 := bstep (se 1 (by rfl) ⟨744854, by rfl⟩ : syracuseStep 993139 = 1489709) B1489709
theorem B993155 : Blo 992597 993155 := bstep (se 1 (by rfl) ⟨744866, by rfl⟩ : syracuseStep 993155 = 1489733) B1489733
theorem B1681283 : Blo 992597 1681283 := bstep (se 1 (by rfl) ⟨1260962, by rfl⟩ : syracuseStep 1681283 = 2521925) B2521925
theorem B2238353 : Blo 992597 2238353 := bstep (se 2 (by rfl) ⟨839382, by rfl⟩ : syracuseStep 2238353 = 1678765) B1678765
theorem B993171 : Blo 992597 993171 := bstep (se 1 (by rfl) ⟨744878, by rfl⟩ : syracuseStep 993171 = 1489757) B1489757
theorem B993187 : Blo 992597 993187 := bstep (se 1 (by rfl) ⟨744890, by rfl⟩ : syracuseStep 993187 = 1489781) B1489781
theorem B2238371 : Blo 992597 2238371 := bstep (se 1 (by rfl) ⟨1678778, by rfl⟩ : syracuseStep 2238371 = 3357557) B3357557
theorem B993203 : Blo 992597 993203 := bstep (se 1 (by rfl) ⟨744902, by rfl⟩ : syracuseStep 993203 = 1489805) B1489805
theorem B993219 : Blo 992597 993219 := bstep (se 1 (by rfl) ⟨744914, by rfl⟩ : syracuseStep 993219 = 1489829) B1489829
theorem B993235 : Blo 992597 993235 := bstep (se 1 (by rfl) ⟨744926, by rfl⟩ : syracuseStep 993235 = 1489853) B1489853
theorem B993251 : Blo 992597 993251 := bstep (se 1 (by rfl) ⟨744938, by rfl⟩ : syracuseStep 993251 = 1489877) B1489877
theorem B993267 : Blo 992597 993267 := bstep (se 1 (by rfl) ⟨744950, by rfl⟩ : syracuseStep 993267 = 1489901) B1489901
theorem B993283 : Blo 992597 993283 := bstep (se 1 (by rfl) ⟨744962, by rfl⟩ : syracuseStep 993283 = 1489925) B1489925
theorem B1681411 : Blo 992597 1681411 := bstep (se 1 (by rfl) ⟨1261058, by rfl⟩ : syracuseStep 1681411 = 2522117) B2522117
theorem B3352589 : Blo 992597 3352589 := bstep (se 3 (by rfl) ⟨628610, by rfl⟩ : syracuseStep 3352589 = 1257221) B1257221
theorem B3188749 : Blo 992597 3188749 := bstep (se 3 (by rfl) ⟨597890, by rfl⟩ : syracuseStep 3188749 = 1195781) B1195781
theorem B993299 : Blo 992597 993299 := bstep (se 1 (by rfl) ⟨744974, by rfl⟩ : syracuseStep 993299 = 1489949) B1489949
theorem B993315 : Blo 992597 993315 := bstep (se 1 (by rfl) ⟨744986, by rfl⟩ : syracuseStep 993315 = 1489973) B1489973
theorem B4302883 : Blo 992597 4302883 := bstep (se 1 (by rfl) ⟨3227162, by rfl⟩ : syracuseStep 4302883 = 6454325) B6454325
theorem B993331 : Blo 992597 993331 := bstep (se 1 (by rfl) ⟨744998, by rfl⟩ : syracuseStep 993331 = 1489997) B1489997
theorem B993347 : Blo 992597 993347 := bstep (se 1 (by rfl) ⟨745010, by rfl⟩ : syracuseStep 993347 = 1490021) B1490021
theorem B3352643 : Blo 992597 3352643 := bstep (se 1 (by rfl) ⟨2514482, by rfl⟩ : syracuseStep 3352643 = 5028965) B5028965
theorem B993363 : Blo 992597 993363 := bstep (se 1 (by rfl) ⟨745022, by rfl⟩ : syracuseStep 993363 = 1490045) B1490045
theorem B993379 : Blo 992597 993379 := bstep (se 1 (by rfl) ⟨745034, by rfl⟩ : syracuseStep 993379 = 1490069) B1490069
theorem B993395 : Blo 992597 993395 := bstep (se 1 (by rfl) ⟨745046, by rfl⟩ : syracuseStep 993395 = 1490093) B1490093
theorem B993411 : Blo 992597 993411 := bstep (se 1 (by rfl) ⟨745058, by rfl⟩ : syracuseStep 993411 = 1490117) B1490117
theorem B2828429 : Blo 992597 2828429 := bstep (se 3 (by rfl) ⟨530330, by rfl⟩ : syracuseStep 2828429 = 1060661) B1060661
theorem B1681553 : Blo 992597 1681553 := bstep (se 2 (by rfl) ⟨630582, by rfl⟩ : syracuseStep 1681553 = 1261165) B1261165
theorem B993427 : Blo 992597 993427 := bstep (se 1 (by rfl) ⟨745070, by rfl⟩ : syracuseStep 993427 = 1490141) B1490141
theorem B993443 : Blo 992597 993443 := bstep (se 1 (by rfl) ⟨745082, by rfl⟩ : syracuseStep 993443 = 1490165) B1490165
theorem B2238641 : Blo 992597 2238641 := bstep (se 2 (by rfl) ⟨839490, by rfl⟩ : syracuseStep 2238641 = 1678981) B1678981
theorem B993459 : Blo 992597 993459 := bstep (se 1 (by rfl) ⟨745094, by rfl⟩ : syracuseStep 993459 = 1490189) B1490189
theorem B993475 : Blo 992597 993475 := bstep (se 1 (by rfl) ⟨745106, by rfl⟩ : syracuseStep 993475 = 1490213) B1490213
theorem B2238659 : Blo 992597 2238659 := bstep (se 1 (by rfl) ⟨1678994, by rfl⟩ : syracuseStep 2238659 = 3357989) B3357989
theorem B993491 : Blo 992597 993491 := bstep (se 1 (by rfl) ⟨745118, by rfl⟩ : syracuseStep 993491 = 1490237) B1490237
theorem B993507 : Blo 992597 993507 := bstep (se 1 (by rfl) ⟨745130, by rfl⟩ : syracuseStep 993507 = 1490261) B1490261
theorem B993523 : Blo 992597 993523 := bstep (se 1 (by rfl) ⟨745142, by rfl⟩ : syracuseStep 993523 = 1490285) B1490285
theorem B993539 : Blo 992597 993539 := bstep (se 1 (by rfl) ⟨745154, by rfl⟩ : syracuseStep 993539 = 1490309) B1490309
theorem B1681681 : Blo 992597 1681681 := bstep (se 2 (by rfl) ⟨630630, by rfl⟩ : syracuseStep 1681681 = 1261261) B1261261
theorem B993555 : Blo 992597 993555 := bstep (se 1 (by rfl) ⟨745166, by rfl⟩ : syracuseStep 993555 = 1490333) B1490333
theorem B993571 : Blo 992597 993571 := bstep (se 1 (by rfl) ⟨745178, by rfl⟩ : syracuseStep 993571 = 1490357) B1490357
theorem B993587 : Blo 992597 993587 := bstep (se 1 (by rfl) ⟨745190, by rfl⟩ : syracuseStep 993587 = 1490381) B1490381
theorem B1681715 : Blo 992597 1681715 := bstep (se 1 (by rfl) ⟨1261286, by rfl⟩ : syracuseStep 1681715 = 2522573) B2522573
theorem B2828611 : Blo 992597 2828611 := bstep (se 1 (by rfl) ⟨2121458, by rfl⟩ : syracuseStep 2828611 = 4242917) B4242917
theorem B993603 : Blo 992597 993603 := bstep (se 1 (by rfl) ⟨745202, by rfl⟩ : syracuseStep 993603 = 1490405) B1490405
theorem B3352913 : Blo 992597 3352913 := bstep (se 2 (by rfl) ⟨1257342, by rfl⟩ : syracuseStep 3352913 = 2514685) B2514685
theorem B993619 : Blo 992597 993619 := bstep (se 1 (by rfl) ⟨745214, by rfl⟩ : syracuseStep 993619 = 1490429) B1490429
theorem B993635 : Blo 992597 993635 := bstep (se 1 (by rfl) ⟨745226, by rfl⟩ : syracuseStep 993635 = 1490453) B1490453
theorem B2828657 : Blo 992597 2828657 := bstep (se 2 (by rfl) ⟨1060746, by rfl⟩ : syracuseStep 2828657 = 2121493) B2121493
theorem B993651 : Blo 992597 993651 := bstep (se 1 (by rfl) ⟨745238, by rfl⟩ : syracuseStep 993651 = 1490477) B1490477
theorem B993667 : Blo 992597 993667 := bstep (se 1 (by rfl) ⟨745250, by rfl⟩ : syracuseStep 993667 = 1490501) B1490501
theorem B993683 : Blo 992597 993683 := bstep (se 1 (by rfl) ⟨745262, by rfl⟩ : syracuseStep 993683 = 1490525) B1490525
theorem B993699 : Blo 992597 993699 := bstep (se 1 (by rfl) ⟨745274, by rfl⟩ : syracuseStep 993699 = 1490549) B1490549
theorem B993715 : Blo 992597 993715 := bstep (se 1 (by rfl) ⟨745286, by rfl⟩ : syracuseStep 993715 = 1490573) B1490573
theorem B993731 : Blo 992597 993731 := bstep (se 1 (by rfl) ⟨745298, by rfl⟩ : syracuseStep 993731 = 1490597) B1490597
theorem B2238929 : Blo 992597 2238929 := bstep (se 2 (by rfl) ⟨839598, by rfl⟩ : syracuseStep 2238929 = 1679197) B1679197
theorem B993747 : Blo 992597 993747 := bstep (se 1 (by rfl) ⟨745310, by rfl⟩ : syracuseStep 993747 = 1490621) B1490621
theorem B993763 : Blo 992597 993763 := bstep (se 1 (by rfl) ⟨745322, by rfl⟩ : syracuseStep 993763 = 1490645) B1490645
theorem B10201571 : Blo 992597 10201571 := bstep (se 1 (by rfl) ⟨7651178, by rfl⟩ : syracuseStep 10201571 = 15302357) B15302357
theorem B2238947 : Blo 992597 2238947 := bstep (se 1 (by rfl) ⟨1679210, by rfl⟩ : syracuseStep 2238947 = 3358421) B3358421
theorem B993779 : Blo 992597 993779 := bstep (se 1 (by rfl) ⟨745334, by rfl⟩ : syracuseStep 993779 = 1490669) B1490669
theorem B993795 : Blo 992597 993795 := bstep (se 1 (by rfl) ⟨745346, by rfl⟩ : syracuseStep 993795 = 1490693) B1490693
theorem B993811 : Blo 992597 993811 := bstep (se 1 (by rfl) ⟨745358, by rfl⟩ : syracuseStep 993811 = 1490717) B1490717
theorem B993827 : Blo 992597 993827 := bstep (se 1 (by rfl) ⟨745370, by rfl⟩ : syracuseStep 993827 = 1490741) B1490741
theorem B993843 : Blo 992597 993843 := bstep (se 1 (by rfl) ⟨745382, by rfl⟩ : syracuseStep 993843 = 1490765) B1490765
theorem B993859 : Blo 992597 993859 := bstep (se 1 (by rfl) ⟨745394, by rfl⟩ : syracuseStep 993859 = 1490789) B1490789
theorem B993875 : Blo 992597 993875 := bstep (se 1 (by rfl) ⟨745406, by rfl⟩ : syracuseStep 993875 = 1490813) B1490813
theorem B993891 : Blo 992597 993891 := bstep (se 1 (by rfl) ⟨745418, by rfl⟩ : syracuseStep 993891 = 1490837) B1490837
theorem B993907 : Blo 992597 993907 := bstep (se 1 (by rfl) ⟨745430, by rfl⟩ : syracuseStep 993907 = 1490861) B1490861
theorem B993923 : Blo 992597 993923 := bstep (se 1 (by rfl) ⟨745442, by rfl⟩ : syracuseStep 993923 = 1490885) B1490885
theorem B993939 : Blo 992597 993939 := bstep (se 1 (by rfl) ⟨745454, by rfl⟩ : syracuseStep 993939 = 1490909) B1490909
theorem B993955 : Blo 992597 993955 := bstep (se 1 (by rfl) ⟨745466, by rfl⟩ : syracuseStep 993955 = 1490933) B1490933
theorem B993971 : Blo 992597 993971 := bstep (se 1 (by rfl) ⟨745478, by rfl⟩ : syracuseStep 993971 = 1490957) B1490957
theorem B993987 : Blo 992597 993987 := bstep (se 1 (by rfl) ⟨745490, by rfl⟩ : syracuseStep 993987 = 1490981) B1490981
theorem B994003 : Blo 992597 994003 := bstep (se 1 (by rfl) ⟨745502, by rfl⟩ : syracuseStep 994003 = 1491005) B1491005
theorem B994019 : Blo 992597 994019 := bstep (se 1 (by rfl) ⟨745514, by rfl⟩ : syracuseStep 994019 = 1491029) B1491029
theorem B2239217 : Blo 992597 2239217 := bstep (se 2 (by rfl) ⟨839706, by rfl⟩ : syracuseStep 2239217 = 1679413) B1679413
theorem B994035 : Blo 992597 994035 := bstep (se 1 (by rfl) ⟨745526, by rfl⟩ : syracuseStep 994035 = 1491053) B1491053
theorem B994051 : Blo 992597 994051 := bstep (se 1 (by rfl) ⟨745538, by rfl⟩ : syracuseStep 994051 = 1491077) B1491077
theorem B2239235 : Blo 992597 2239235 := bstep (se 1 (by rfl) ⟨1679426, by rfl⟩ : syracuseStep 2239235 = 3358853) B3358853
theorem B994067 : Blo 992597 994067 := bstep (se 1 (by rfl) ⟨745550, by rfl⟩ : syracuseStep 994067 = 1491101) B1491101
theorem B994083 : Blo 992597 994083 := bstep (se 1 (by rfl) ⟨745562, by rfl⟩ : syracuseStep 994083 = 1491125) B1491125
theorem B994099 : Blo 992597 994099 := bstep (se 1 (by rfl) ⟨745574, by rfl⟩ : syracuseStep 994099 = 1491149) B1491149
theorem B994115 : Blo 992597 994115 := bstep (se 1 (by rfl) ⟨745586, by rfl⟩ : syracuseStep 994115 = 1491173) B1491173
theorem B994131 : Blo 992597 994131 := bstep (se 1 (by rfl) ⟨745598, by rfl⟩ : syracuseStep 994131 = 1491197) B1491197
theorem B994147 : Blo 992597 994147 := bstep (se 1 (by rfl) ⟨745610, by rfl⟩ : syracuseStep 994147 = 1491221) B1491221
theorem B3353453 : Blo 992597 3353453 := bstep (se 3 (by rfl) ⟨628772, by rfl⟩ : syracuseStep 3353453 = 1257545) B1257545
theorem B994163 : Blo 992597 994163 := bstep (se 1 (by rfl) ⟨745622, by rfl⟩ : syracuseStep 994163 = 1491245) B1491245
theorem B994179 : Blo 992597 994179 := bstep (se 1 (by rfl) ⟨745634, by rfl⟩ : syracuseStep 994179 = 1491269) B1491269
theorem B994195 : Blo 992597 994195 := bstep (se 1 (by rfl) ⟨745646, by rfl⟩ : syracuseStep 994195 = 1491293) B1491293
theorem B3353507 : Blo 992597 3353507 := bstep (se 1 (by rfl) ⟨2515130, by rfl⟩ : syracuseStep 3353507 = 5030261) B5030261
theorem B994211 : Blo 992597 994211 := bstep (se 1 (by rfl) ⟨745658, by rfl⟩ : syracuseStep 994211 = 1491317) B1491317
theorem B994227 : Blo 992597 994227 := bstep (se 1 (by rfl) ⟨745670, by rfl⟩ : syracuseStep 994227 = 1491341) B1491341
theorem B994243 : Blo 992597 994243 := bstep (se 1 (by rfl) ⟨745682, by rfl⟩ : syracuseStep 994243 = 1491365) B1491365
theorem B994259 : Blo 992597 994259 := bstep (se 1 (by rfl) ⟨745694, by rfl⟩ : syracuseStep 994259 = 1491389) B1491389
theorem B994275 : Blo 992597 994275 := bstep (se 1 (by rfl) ⟨745706, by rfl⟩ : syracuseStep 994275 = 1491413) B1491413
theorem B994291 : Blo 992597 994291 := bstep (se 1 (by rfl) ⟨745718, by rfl⟩ : syracuseStep 994291 = 1491437) B1491437
theorem B994307 : Blo 992597 994307 := bstep (se 1 (by rfl) ⟨745730, by rfl⟩ : syracuseStep 994307 = 1491461) B1491461
theorem B2239505 : Blo 992597 2239505 := bstep (se 2 (by rfl) ⟨839814, by rfl⟩ : syracuseStep 2239505 = 1679629) B1679629
theorem B1256467 : Blo 992597 1256467 := bstep (se 1 (by rfl) ⟨942350, by rfl⟩ : syracuseStep 1256467 = 1884701) B1884701
theorem B994323 : Blo 992597 994323 := bstep (se 1 (by rfl) ⟨745742, by rfl⟩ : syracuseStep 994323 = 1491485) B1491485
theorem B994339 : Blo 992597 994339 := bstep (se 1 (by rfl) ⟨745754, by rfl⟩ : syracuseStep 994339 = 1491509) B1491509
theorem B2239523 : Blo 992597 2239523 := bstep (se 1 (by rfl) ⟨1679642, by rfl⟩ : syracuseStep 2239523 = 3359285) B3359285
theorem B994355 : Blo 992597 994355 := bstep (se 1 (by rfl) ⟨745766, by rfl⟩ : syracuseStep 994355 = 1491533) B1491533
theorem B994371 : Blo 992597 994371 := bstep (se 1 (by rfl) ⟨745778, by rfl⟩ : syracuseStep 994371 = 1491557) B1491557
theorem B994387 : Blo 992597 994387 := bstep (se 1 (by rfl) ⟨745790, by rfl⟩ : syracuseStep 994387 = 1491581) B1491581
theorem B994403 : Blo 992597 994403 := bstep (se 1 (by rfl) ⟨745802, by rfl⟩ : syracuseStep 994403 = 1491605) B1491605
theorem B1256563 : Blo 992597 1256563 := bstep (se 1 (by rfl) ⟨942422, by rfl⟩ : syracuseStep 1256563 = 1884845) B1884845
theorem B994419 : Blo 992597 994419 := bstep (se 1 (by rfl) ⟨745814, by rfl⟩ : syracuseStep 994419 = 1491629) B1491629
theorem B994435 : Blo 992597 994435 := bstep (se 1 (by rfl) ⟨745826, by rfl⟩ : syracuseStep 994435 = 1491653) B1491653
theorem B994451 : Blo 992597 994451 := bstep (se 1 (by rfl) ⟨745838, by rfl⟩ : syracuseStep 994451 = 1491677) B1491677
theorem B994467 : Blo 992597 994467 := bstep (se 1 (by rfl) ⟨745850, by rfl⟩ : syracuseStep 994467 = 1491701) B1491701
theorem B1617059 : Blo 992597 1617059 := bstep (se 1 (by rfl) ⟨1212794, by rfl⟩ : syracuseStep 1617059 = 2425589) B2425589
theorem B3353777 : Blo 992597 3353777 := bstep (se 2 (by rfl) ⟨1257666, by rfl⟩ : syracuseStep 3353777 = 2515333) B2515333
theorem B994483 : Blo 992597 994483 := bstep (se 1 (by rfl) ⟨745862, by rfl⟩ : syracuseStep 994483 = 1491725) B1491725
theorem B994499 : Blo 992597 994499 := bstep (se 1 (by rfl) ⟨745874, by rfl⟩ : syracuseStep 994499 = 1491749) B1491749
theorem B6368453 : Blo 992597 6368453 := bstep (se 4 (by rfl) ⟨597042, by rfl⟩ : syracuseStep 6368453 = 1194085) B1194085
theorem B994515 : Blo 992597 994515 := bstep (se 1 (by rfl) ⟨745886, by rfl⟩ : syracuseStep 994515 = 1491773) B1491773
theorem B994531 : Blo 992597 994531 := bstep (se 1 (by rfl) ⟨745898, by rfl⟩ : syracuseStep 994531 = 1491797) B1491797
theorem B994547 : Blo 992597 994547 := bstep (se 1 (by rfl) ⟨745910, by rfl⟩ : syracuseStep 994547 = 1491821) B1491821
theorem B994563 : Blo 992597 994563 := bstep (se 1 (by rfl) ⟨745922, by rfl⟩ : syracuseStep 994563 = 1491845) B1491845
theorem B994579 : Blo 992597 994579 := bstep (se 1 (by rfl) ⟨745934, by rfl⟩ : syracuseStep 994579 = 1491869) B1491869
theorem B994595 : Blo 992597 994595 := bstep (se 1 (by rfl) ⟨745946, by rfl⟩ : syracuseStep 994595 = 1491893) B1491893
theorem B2239793 : Blo 992597 2239793 := bstep (se 2 (by rfl) ⟨839922, by rfl⟩ : syracuseStep 2239793 = 1679845) B1679845
theorem B994611 : Blo 992597 994611 := bstep (se 1 (by rfl) ⟨745958, by rfl⟩ : syracuseStep 994611 = 1491917) B1491917
theorem B994627 : Blo 992597 994627 := bstep (se 1 (by rfl) ⟨745970, by rfl⟩ : syracuseStep 994627 = 1491941) B1491941
theorem B2239811 : Blo 992597 2239811 := bstep (se 1 (by rfl) ⟨1679858, by rfl⟩ : syracuseStep 2239811 = 3359717) B3359717
theorem B994643 : Blo 992597 994643 := bstep (se 1 (by rfl) ⟨745982, by rfl⟩ : syracuseStep 994643 = 1491965) B1491965
theorem B994659 : Blo 992597 994659 := bstep (se 1 (by rfl) ⟨745994, by rfl⟩ : syracuseStep 994659 = 1491989) B1491989
theorem B994675 : Blo 992597 994675 := bstep (se 1 (by rfl) ⟨746006, by rfl⟩ : syracuseStep 994675 = 1492013) B1492013
theorem B994691 : Blo 992597 994691 := bstep (se 1 (by rfl) ⟨746018, by rfl⟩ : syracuseStep 994691 = 1492037) B1492037
theorem B6040973 : Blo 992597 6040973 := bstep (se 3 (by rfl) ⟨1132682, by rfl⟩ : syracuseStep 6040973 = 2265365) B2265365
theorem B994707 : Blo 992597 994707 := bstep (se 1 (by rfl) ⟨746030, by rfl⟩ : syracuseStep 994707 = 1492061) B1492061
theorem B994723 : Blo 992597 994723 := bstep (se 1 (by rfl) ⟨746042, by rfl⟩ : syracuseStep 994723 = 1492085) B1492085
theorem B3780017 : Blo 992597 3780017 := bstep (se 2 (by rfl) ⟨1417506, by rfl⟩ : syracuseStep 3780017 = 2835013) B2835013
theorem B994739 : Blo 992597 994739 := bstep (se 1 (by rfl) ⟨746054, by rfl⟩ : syracuseStep 994739 = 1492109) B1492109
theorem B994755 : Blo 992597 994755 := bstep (se 1 (by rfl) ⟨746066, by rfl⟩ : syracuseStep 994755 = 1492133) B1492133
theorem B3190211 : Blo 992597 3190211 := bstep (se 1 (by rfl) ⟨2392658, by rfl⟩ : syracuseStep 3190211 = 4785317) B4785317
theorem B994771 : Blo 992597 994771 := bstep (se 1 (by rfl) ⟨746078, by rfl⟩ : syracuseStep 994771 = 1492157) B1492157
theorem B994787 : Blo 992597 994787 := bstep (se 1 (by rfl) ⟨746090, by rfl⟩ : syracuseStep 994787 = 1492181) B1492181
theorem B994803 : Blo 992597 994803 := bstep (se 1 (by rfl) ⟨746102, by rfl⟩ : syracuseStep 994803 = 1492205) B1492205
theorem B994819 : Blo 992597 994819 := bstep (se 1 (by rfl) ⟨746114, by rfl⟩ : syracuseStep 994819 = 1492229) B1492229
theorem B994835 : Blo 992597 994835 := bstep (se 1 (by rfl) ⟨746126, by rfl⟩ : syracuseStep 994835 = 1492253) B1492253
theorem B994851 : Blo 992597 994851 := bstep (se 1 (by rfl) ⟨746138, by rfl⟩ : syracuseStep 994851 = 1492277) B1492277
theorem B2272817 : Blo 992597 2272817 := bstep (se 2 (by rfl) ⟨852306, by rfl⟩ : syracuseStep 2272817 = 1704613) B1704613
theorem B994867 : Blo 992597 994867 := bstep (se 1 (by rfl) ⟨746150, by rfl⟩ : syracuseStep 994867 = 1492301) B1492301
theorem B994883 : Blo 992597 994883 := bstep (se 1 (by rfl) ⟨746162, by rfl⟩ : syracuseStep 994883 = 1492325) B1492325
theorem B2240081 : Blo 992597 2240081 := bstep (se 2 (by rfl) ⟨840030, by rfl⟩ : syracuseStep 2240081 = 1680061) B1680061
theorem B994899 : Blo 992597 994899 := bstep (se 1 (by rfl) ⟨746174, by rfl⟩ : syracuseStep 994899 = 1492349) B1492349
theorem B1257059 : Blo 992597 1257059 := bstep (se 1 (by rfl) ⟨942794, by rfl⟩ : syracuseStep 1257059 = 1885589) B1885589
theorem B994915 : Blo 992597 994915 := bstep (se 1 (by rfl) ⟨746186, by rfl⟩ : syracuseStep 994915 = 1492373) B1492373
theorem B2240099 : Blo 992597 2240099 := bstep (se 1 (by rfl) ⟨1680074, by rfl⟩ : syracuseStep 2240099 = 3360149) B3360149
theorem B2043505 : Blo 992597 2043505 := bstep (se 2 (by rfl) ⟨766314, by rfl⟩ : syracuseStep 2043505 = 1532629) B1532629
theorem B994931 : Blo 992597 994931 := bstep (se 1 (by rfl) ⟨746198, by rfl⟩ : syracuseStep 994931 = 1492397) B1492397
theorem B994947 : Blo 992597 994947 := bstep (se 1 (by rfl) ⟨746210, by rfl⟩ : syracuseStep 994947 = 1492421) B1492421
theorem B1060499 : Blo 992597 1060499 := bstep (se 1 (by rfl) ⟨795374, by rfl⟩ : syracuseStep 1060499 = 1590749) B1590749
theorem B994963 : Blo 992597 994963 := bstep (se 1 (by rfl) ⟨746222, by rfl⟩ : syracuseStep 994963 = 1492445) B1492445
theorem B994979 : Blo 992597 994979 := bstep (se 1 (by rfl) ⟨746234, by rfl⟩ : syracuseStep 994979 = 1492469) B1492469
theorem B994995 : Blo 992597 994995 := bstep (se 1 (by rfl) ⟨746246, by rfl⟩ : syracuseStep 994995 = 1492493) B1492493
theorem B995011 : Blo 992597 995011 := bstep (se 1 (by rfl) ⟨746258, by rfl⟩ : syracuseStep 995011 = 1492517) B1492517
theorem B3354317 : Blo 992597 3354317 := bstep (se 3 (by rfl) ⟨628934, by rfl⟩ : syracuseStep 3354317 = 1257869) B1257869
theorem B995027 : Blo 992597 995027 := bstep (se 1 (by rfl) ⟨746270, by rfl⟩ : syracuseStep 995027 = 1492541) B1492541
theorem B995043 : Blo 992597 995043 := bstep (se 1 (by rfl) ⟨746282, by rfl⟩ : syracuseStep 995043 = 1492565) B1492565
theorem B995059 : Blo 992597 995059 := bstep (se 1 (by rfl) ⟨746294, by rfl⟩ : syracuseStep 995059 = 1492589) B1492589
theorem B3354371 : Blo 992597 3354371 := bstep (se 1 (by rfl) ⟨2515778, by rfl⟩ : syracuseStep 3354371 = 5031557) B5031557
theorem B995075 : Blo 992597 995075 := bstep (se 1 (by rfl) ⟨746306, by rfl⟩ : syracuseStep 995075 = 1492613) B1492613
theorem B995091 : Blo 992597 995091 := bstep (se 1 (by rfl) ⟨746318, by rfl⟩ : syracuseStep 995091 = 1492637) B1492637
theorem B2830115 : Blo 992597 2830115 := bstep (se 1 (by rfl) ⟨2122586, by rfl⟩ : syracuseStep 2830115 = 4245173) B4245173
theorem B995107 : Blo 992597 995107 := bstep (se 1 (by rfl) ⟨746330, by rfl⟩ : syracuseStep 995107 = 1492661) B1492661
theorem B995123 : Blo 992597 995123 := bstep (se 1 (by rfl) ⟨746342, by rfl⟩ : syracuseStep 995123 = 1492685) B1492685
theorem B995139 : Blo 992597 995139 := bstep (se 1 (by rfl) ⟨746354, by rfl⟩ : syracuseStep 995139 = 1492709) B1492709
theorem B995155 : Blo 992597 995155 := bstep (se 1 (by rfl) ⟨746366, by rfl⟩ : syracuseStep 995155 = 1492733) B1492733
theorem B995171 : Blo 992597 995171 := bstep (se 1 (by rfl) ⟨746378, by rfl⟩ : syracuseStep 995171 = 1492757) B1492757
theorem B2240369 : Blo 992597 2240369 := bstep (se 2 (by rfl) ⟨840138, by rfl⟩ : syracuseStep 2240369 = 1680277) B1680277
theorem B995187 : Blo 992597 995187 := bstep (se 1 (by rfl) ⟨746390, by rfl⟩ : syracuseStep 995187 = 1492781) B1492781
theorem B995203 : Blo 992597 995203 := bstep (se 1 (by rfl) ⟨746402, by rfl⟩ : syracuseStep 995203 = 1492805) B1492805
theorem B2240387 : Blo 992597 2240387 := bstep (se 1 (by rfl) ⟨1680290, by rfl⟩ : syracuseStep 2240387 = 3360581) B3360581
theorem B995219 : Blo 992597 995219 := bstep (se 1 (by rfl) ⟨746414, by rfl⟩ : syracuseStep 995219 = 1492829) B1492829
theorem B995235 : Blo 992597 995235 := bstep (se 1 (by rfl) ⟨746426, by rfl⟩ : syracuseStep 995235 = 1492853) B1492853
theorem B995251 : Blo 992597 995251 := bstep (se 1 (by rfl) ⟨746438, by rfl⟩ : syracuseStep 995251 = 1492877) B1492877
theorem B995267 : Blo 992597 995267 := bstep (se 1 (by rfl) ⟨746450, by rfl⟩ : syracuseStep 995267 = 1492901) B1492901
theorem B995283 : Blo 992597 995283 := bstep (se 1 (by rfl) ⟨746462, by rfl⟩ : syracuseStep 995283 = 1492925) B1492925
theorem B995299 : Blo 992597 995299 := bstep (se 1 (by rfl) ⟨746474, by rfl⟩ : syracuseStep 995299 = 1492949) B1492949
theorem B995315 : Blo 992597 995315 := bstep (se 1 (by rfl) ⟨746486, by rfl⟩ : syracuseStep 995315 = 1492973) B1492973
theorem B995331 : Blo 992597 995331 := bstep (se 1 (by rfl) ⟨746498, by rfl⟩ : syracuseStep 995331 = 1492997) B1492997
theorem B3354641 : Blo 992597 3354641 := bstep (se 2 (by rfl) ⟨1257990, by rfl⟩ : syracuseStep 3354641 = 2515981) B2515981
theorem B995347 : Blo 992597 995347 := bstep (se 1 (by rfl) ⟨746510, by rfl⟩ : syracuseStep 995347 = 1493021) B1493021
theorem B995363 : Blo 992597 995363 := bstep (se 1 (by rfl) ⟨746522, by rfl⟩ : syracuseStep 995363 = 1493045) B1493045
theorem B995379 : Blo 992597 995379 := bstep (se 1 (by rfl) ⟨746534, by rfl⟩ : syracuseStep 995379 = 1493069) B1493069
theorem B995395 : Blo 992597 995395 := bstep (se 1 (by rfl) ⟨746546, by rfl⟩ : syracuseStep 995395 = 1493093) B1493093
theorem B995411 : Blo 992597 995411 := bstep (se 1 (by rfl) ⟨746558, by rfl⟩ : syracuseStep 995411 = 1493117) B1493117
theorem B995427 : Blo 992597 995427 := bstep (se 1 (by rfl) ⟨746570, by rfl⟩ : syracuseStep 995427 = 1493141) B1493141
theorem B995443 : Blo 992597 995443 := bstep (se 1 (by rfl) ⟨746582, by rfl⟩ : syracuseStep 995443 = 1493165) B1493165
theorem B995459 : Blo 992597 995459 := bstep (se 1 (by rfl) ⟨746594, by rfl⟩ : syracuseStep 995459 = 1493189) B1493189
theorem B2240657 : Blo 992597 2240657 := bstep (se 2 (by rfl) ⟨840246, by rfl⟩ : syracuseStep 2240657 = 1680493) B1680493
theorem B995475 : Blo 992597 995475 := bstep (se 1 (by rfl) ⟨746606, by rfl⟩ : syracuseStep 995475 = 1493213) B1493213
theorem B995491 : Blo 992597 995491 := bstep (se 1 (by rfl) ⟨746618, by rfl⟩ : syracuseStep 995491 = 1493237) B1493237
theorem B2240675 : Blo 992597 2240675 := bstep (se 1 (by rfl) ⟨1680506, by rfl⟩ : syracuseStep 2240675 = 3361013) B3361013
theorem B1913009 : Blo 992597 1913009 := bstep (se 2 (by rfl) ⟨717378, by rfl⟩ : syracuseStep 1913009 = 1434757) B1434757
theorem B995507 : Blo 992597 995507 := bstep (se 1 (by rfl) ⟨746630, by rfl⟩ : syracuseStep 995507 = 1493261) B1493261
theorem B995523 : Blo 992597 995523 := bstep (se 1 (by rfl) ⟨746642, by rfl⟩ : syracuseStep 995523 = 1493285) B1493285
theorem B995539 : Blo 992597 995539 := bstep (se 1 (by rfl) ⟨746654, by rfl⟩ : syracuseStep 995539 = 1493309) B1493309
theorem B995555 : Blo 992597 995555 := bstep (se 1 (by rfl) ⟨746666, by rfl⟩ : syracuseStep 995555 = 1493333) B1493333
theorem B995571 : Blo 992597 995571 := bstep (se 1 (by rfl) ⟨746678, by rfl⟩ : syracuseStep 995571 = 1493357) B1493357
theorem B995587 : Blo 992597 995587 := bstep (se 1 (by rfl) ⟨746690, by rfl⟩ : syracuseStep 995587 = 1493381) B1493381
theorem B995603 : Blo 992597 995603 := bstep (se 1 (by rfl) ⟨746702, by rfl⟩ : syracuseStep 995603 = 1493405) B1493405
theorem B1257763 : Blo 992597 1257763 := bstep (se 1 (by rfl) ⟨943322, by rfl⟩ : syracuseStep 1257763 = 1886645) B1886645
theorem B995619 : Blo 992597 995619 := bstep (se 1 (by rfl) ⟨746714, by rfl⟩ : syracuseStep 995619 = 1493429) B1493429
theorem B995635 : Blo 992597 995635 := bstep (se 1 (by rfl) ⟨746726, by rfl⟩ : syracuseStep 995635 = 1493453) B1493453
theorem B995651 : Blo 992597 995651 := bstep (se 1 (by rfl) ⟨746738, by rfl⟩ : syracuseStep 995651 = 1493477) B1493477
theorem B995667 : Blo 992597 995667 := bstep (se 1 (by rfl) ⟨746750, by rfl⟩ : syracuseStep 995667 = 1493501) B1493501
theorem B995683 : Blo 992597 995683 := bstep (se 1 (by rfl) ⟨746762, by rfl⟩ : syracuseStep 995683 = 1493525) B1493525
theorem B995699 : Blo 992597 995699 := bstep (se 1 (by rfl) ⟨746774, by rfl⟩ : syracuseStep 995699 = 1493549) B1493549
theorem B1257859 : Blo 992597 1257859 := bstep (se 1 (by rfl) ⟨943394, by rfl⟩ : syracuseStep 1257859 = 1886789) B1886789
theorem B995715 : Blo 992597 995715 := bstep (se 1 (by rfl) ⟨746786, by rfl⟩ : syracuseStep 995715 = 1493573) B1493573
theorem B14332301 : Blo 992597 14332301 := bstep (se 3 (by rfl) ⟨2687306, by rfl⟩ : syracuseStep 14332301 = 5374613) B5374613
theorem B995731 : Blo 992597 995731 := bstep (se 1 (by rfl) ⟨746798, by rfl⟩ : syracuseStep 995731 = 1493597) B1493597
theorem B5026211 : Blo 992597 5026211 := bstep (se 1 (by rfl) ⟨3769658, by rfl⟩ : syracuseStep 5026211 = 7539317) B7539317
theorem B995747 : Blo 992597 995747 := bstep (se 1 (by rfl) ⟨746810, by rfl⟩ : syracuseStep 995747 = 1493621) B1493621
theorem B2240945 : Blo 992597 2240945 := bstep (se 2 (by rfl) ⟨840354, by rfl⟩ : syracuseStep 2240945 = 1680709) B1680709
theorem B995763 : Blo 992597 995763 := bstep (se 1 (by rfl) ⟨746822, by rfl⟩ : syracuseStep 995763 = 1493645) B1493645
theorem B995779 : Blo 992597 995779 := bstep (se 1 (by rfl) ⟨746834, by rfl⟩ : syracuseStep 995779 = 1493669) B1493669
theorem B2240963 : Blo 992597 2240963 := bstep (se 1 (by rfl) ⟨1680722, by rfl⟩ : syracuseStep 2240963 = 3361445) B3361445
theorem B995795 : Blo 992597 995795 := bstep (se 1 (by rfl) ⟨746846, by rfl⟩ : syracuseStep 995795 = 1493693) B1493693
theorem B995811 : Blo 992597 995811 := bstep (se 1 (by rfl) ⟨746858, by rfl⟩ : syracuseStep 995811 = 1493717) B1493717
theorem B995827 : Blo 992597 995827 := bstep (se 1 (by rfl) ⟨746870, by rfl⟩ : syracuseStep 995827 = 1493741) B1493741
theorem B995843 : Blo 992597 995843 := bstep (se 1 (by rfl) ⟨746882, by rfl⟩ : syracuseStep 995843 = 1493765) B1493765
theorem B995859 : Blo 992597 995859 := bstep (se 1 (by rfl) ⟨746894, by rfl⟩ : syracuseStep 995859 = 1493789) B1493789
theorem B995875 : Blo 992597 995875 := bstep (se 1 (by rfl) ⟨746906, by rfl⟩ : syracuseStep 995875 = 1493813) B1493813
theorem B3355181 : Blo 992597 3355181 := bstep (se 3 (by rfl) ⟨629096, by rfl⟩ : syracuseStep 3355181 = 1258193) B1258193
theorem B995891 : Blo 992597 995891 := bstep (se 1 (by rfl) ⟨746918, by rfl⟩ : syracuseStep 995891 = 1493837) B1493837
theorem B995907 : Blo 992597 995907 := bstep (se 1 (by rfl) ⟨746930, by rfl⟩ : syracuseStep 995907 = 1493861) B1493861
theorem B995923 : Blo 992597 995923 := bstep (se 1 (by rfl) ⟨746942, by rfl⟩ : syracuseStep 995923 = 1493885) B1493885
theorem B3355235 : Blo 992597 3355235 := bstep (se 1 (by rfl) ⟨2516426, by rfl⟩ : syracuseStep 3355235 = 5032853) B5032853
theorem B995939 : Blo 992597 995939 := bstep (se 1 (by rfl) ⟨746954, by rfl⟩ : syracuseStep 995939 = 1493909) B1493909
theorem B995955 : Blo 992597 995955 := bstep (se 1 (by rfl) ⟨746966, by rfl⟩ : syracuseStep 995955 = 1493933) B1493933
theorem B995971 : Blo 992597 995971 := bstep (se 1 (by rfl) ⟨746978, by rfl⟩ : syracuseStep 995971 = 1493957) B1493957
theorem B995987 : Blo 992597 995987 := bstep (se 1 (by rfl) ⟨746990, by rfl⟩ : syracuseStep 995987 = 1493981) B1493981
theorem B996003 : Blo 992597 996003 := bstep (se 1 (by rfl) ⟨747002, by rfl⟩ : syracuseStep 996003 = 1494005) B1494005
theorem B996019 : Blo 992597 996019 := bstep (se 1 (by rfl) ⟨747014, by rfl⟩ : syracuseStep 996019 = 1494029) B1494029
theorem B996035 : Blo 992597 996035 := bstep (se 1 (by rfl) ⟨747026, by rfl⟩ : syracuseStep 996035 = 1494053) B1494053
theorem B2241233 : Blo 992597 2241233 := bstep (se 2 (by rfl) ⟨840462, by rfl⟩ : syracuseStep 2241233 = 1680925) B1680925
theorem B996051 : Blo 992597 996051 := bstep (se 1 (by rfl) ⟨747038, by rfl⟩ : syracuseStep 996051 = 1494077) B1494077
theorem B996067 : Blo 992597 996067 := bstep (se 1 (by rfl) ⟨747050, by rfl⟩ : syracuseStep 996067 = 1494101) B1494101
theorem B2241251 : Blo 992597 2241251 := bstep (se 1 (by rfl) ⟨1680938, by rfl⟩ : syracuseStep 2241251 = 3361877) B3361877
theorem B996083 : Blo 992597 996083 := bstep (se 1 (by rfl) ⟨747062, by rfl⟩ : syracuseStep 996083 = 1494125) B1494125
theorem B1061635 : Blo 992597 1061635 := bstep (se 1 (by rfl) ⟨796226, by rfl⟩ : syracuseStep 1061635 = 1592453) B1592453
theorem B996099 : Blo 992597 996099 := bstep (se 1 (by rfl) ⟨747074, by rfl⟩ : syracuseStep 996099 = 1494149) B1494149
theorem B996115 : Blo 992597 996115 := bstep (se 1 (by rfl) ⟨747086, by rfl⟩ : syracuseStep 996115 = 1494173) B1494173
theorem B996131 : Blo 992597 996131 := bstep (se 1 (by rfl) ⟨747098, by rfl⟩ : syracuseStep 996131 = 1494197) B1494197
theorem B996147 : Blo 992597 996147 := bstep (se 1 (by rfl) ⟨747110, by rfl⟩ : syracuseStep 996147 = 1494221) B1494221
theorem B996163 : Blo 992597 996163 := bstep (se 1 (by rfl) ⟨747122, by rfl⟩ : syracuseStep 996163 = 1494245) B1494245
theorem B996179 : Blo 992597 996179 := bstep (se 1 (by rfl) ⟨747134, by rfl⟩ : syracuseStep 996179 = 1494269) B1494269
theorem B3781475 : Blo 992597 3781475 := bstep (se 1 (by rfl) ⟨2836106, by rfl⟩ : syracuseStep 3781475 = 5672213) B5672213
theorem B996195 : Blo 992597 996195 := bstep (se 1 (by rfl) ⟨747146, by rfl⟩ : syracuseStep 996195 = 1494293) B1494293
theorem B3355505 : Blo 992597 3355505 := bstep (se 2 (by rfl) ⟨1258314, by rfl⟩ : syracuseStep 3355505 = 2516629) B2516629
theorem B1258355 : Blo 992597 1258355 := bstep (se 1 (by rfl) ⟨943766, by rfl⟩ : syracuseStep 1258355 = 1887533) B1887533
theorem B996211 : Blo 992597 996211 := bstep (se 1 (by rfl) ⟨747158, by rfl⟩ : syracuseStep 996211 = 1494317) B1494317
theorem B996227 : Blo 992597 996227 := bstep (se 1 (by rfl) ⟨747170, by rfl⟩ : syracuseStep 996227 = 1494341) B1494341
theorem B996243 : Blo 992597 996243 := bstep (se 1 (by rfl) ⟨747182, by rfl⟩ : syracuseStep 996243 = 1494365) B1494365
theorem B996259 : Blo 992597 996259 := bstep (se 1 (by rfl) ⟨747194, by rfl⟩ : syracuseStep 996259 = 1494389) B1494389
theorem B996275 : Blo 992597 996275 := bstep (se 1 (by rfl) ⟨747206, by rfl⟩ : syracuseStep 996275 = 1494413) B1494413
theorem B996291 : Blo 992597 996291 := bstep (se 1 (by rfl) ⟨747218, by rfl⟩ : syracuseStep 996291 = 1494437) B1494437
theorem B996307 : Blo 992597 996307 := bstep (se 1 (by rfl) ⟨747230, by rfl⟩ : syracuseStep 996307 = 1494461) B1494461
theorem B1913827 : Blo 992597 1913827 := bstep (se 1 (by rfl) ⟨1435370, by rfl⟩ : syracuseStep 1913827 = 2870741) B2870741
theorem B996323 : Blo 992597 996323 := bstep (se 1 (by rfl) ⟨747242, by rfl⟩ : syracuseStep 996323 = 1494485) B1494485
theorem B2831345 : Blo 992597 2831345 := bstep (se 2 (by rfl) ⟨1061754, by rfl⟩ : syracuseStep 2831345 = 2123509) B2123509
theorem B2241521 : Blo 992597 2241521 := bstep (se 2 (by rfl) ⟨840570, by rfl⟩ : syracuseStep 2241521 = 1681141) B1681141
theorem B996339 : Blo 992597 996339 := bstep (se 1 (by rfl) ⟨747254, by rfl⟩ : syracuseStep 996339 = 1494509) B1494509
theorem B2241539 : Blo 992597 2241539 := bstep (se 1 (by rfl) ⟨1681154, by rfl⟩ : syracuseStep 2241539 = 3362309) B3362309
theorem B996355 : Blo 992597 996355 := bstep (se 1 (by rfl) ⟨747266, by rfl⟩ : syracuseStep 996355 = 1494533) B1494533
theorem B3453965 : Blo 992597 3453965 := bstep (se 3 (by rfl) ⟨647618, by rfl⟩ : syracuseStep 3453965 = 1295237) B1295237
theorem B3191825 : Blo 992597 3191825 := bstep (se 2 (by rfl) ⟨1196934, by rfl⟩ : syracuseStep 3191825 = 2393869) B2393869
theorem B996371 : Blo 992597 996371 := bstep (se 1 (by rfl) ⟨747278, by rfl⟩ : syracuseStep 996371 = 1494557) B1494557
theorem B996387 : Blo 992597 996387 := bstep (se 1 (by rfl) ⟨747290, by rfl⟩ : syracuseStep 996387 = 1494581) B1494581
theorem B996403 : Blo 992597 996403 := bstep (se 1 (by rfl) ⟨747302, by rfl⟩ : syracuseStep 996403 = 1494605) B1494605
theorem B996419 : Blo 992597 996419 := bstep (se 1 (by rfl) ⟨747314, by rfl⟩ : syracuseStep 996419 = 1494629) B1494629
theorem B996435 : Blo 992597 996435 := bstep (se 1 (by rfl) ⟨747326, by rfl⟩ : syracuseStep 996435 = 1494653) B1494653
theorem B996451 : Blo 992597 996451 := bstep (se 1 (by rfl) ⟨747338, by rfl⟩ : syracuseStep 996451 = 1494677) B1494677
theorem B996467 : Blo 992597 996467 := bstep (se 1 (by rfl) ⟨747350, by rfl⟩ : syracuseStep 996467 = 1494701) B1494701
theorem B996483 : Blo 992597 996483 := bstep (se 1 (by rfl) ⟨747362, by rfl⟩ : syracuseStep 996483 = 1494725) B1494725
theorem B4240525 : Blo 992597 4240525 := bstep (se 3 (by rfl) ⟨795098, by rfl⟩ : syracuseStep 4240525 = 1590197) B1590197
theorem B996499 : Blo 992597 996499 := bstep (se 1 (by rfl) ⟨747374, by rfl⟩ : syracuseStep 996499 = 1494749) B1494749
theorem B996515 : Blo 992597 996515 := bstep (se 1 (by rfl) ⟨747386, by rfl⟩ : syracuseStep 996515 = 1494773) B1494773
theorem B3454129 : Blo 992597 3454129 := bstep (se 2 (by rfl) ⟨1295298, by rfl⟩ : syracuseStep 3454129 = 2590597) B2590597
theorem B996531 : Blo 992597 996531 := bstep (se 1 (by rfl) ⟨747398, by rfl⟩ : syracuseStep 996531 = 1494797) B1494797
theorem B11318453 : Blo 992597 11318453 := bstep (se 5 (by rfl) ⟨530552, by rfl⟩ : syracuseStep 11318453 = 1061105) B1061105
theorem B996547 : Blo 992597 996547 := bstep (se 1 (by rfl) ⟨747410, by rfl⟩ : syracuseStep 996547 = 1494821) B1494821
theorem B5027021 : Blo 992597 5027021 := bstep (se 3 (by rfl) ⟨942566, by rfl⟩ : syracuseStep 5027021 = 1885133) B1885133
theorem B996563 : Blo 992597 996563 := bstep (se 1 (by rfl) ⟨747422, by rfl⟩ : syracuseStep 996563 = 1494845) B1494845
theorem B996579 : Blo 992597 996579 := bstep (se 1 (by rfl) ⟨747434, by rfl⟩ : syracuseStep 996579 = 1494869) B1494869
theorem B996595 : Blo 992597 996595 := bstep (se 1 (by rfl) ⟨747446, by rfl⟩ : syracuseStep 996595 = 1494893) B1494893
theorem B2241809 : Blo 992597 2241809 := bstep (se 2 (by rfl) ⟨840678, by rfl⟩ : syracuseStep 2241809 = 1681357) B1681357
theorem B2241827 : Blo 992597 2241827 := bstep (se 1 (by rfl) ⟨1681370, by rfl⟩ : syracuseStep 2241827 = 3362741) B3362741
theorem B3356045 : Blo 992597 3356045 := bstep (se 3 (by rfl) ⟨629258, by rfl⟩ : syracuseStep 3356045 = 1258517) B1258517
theorem B8074637 : Blo 992597 8074637 := bstep (se 3 (by rfl) ⟨1513994, by rfl⟩ : syracuseStep 8074637 = 3027989) B3027989
theorem B3356099 : Blo 992597 3356099 := bstep (se 1 (by rfl) ⟨2517074, by rfl⟩ : syracuseStep 3356099 = 5034149) B5034149
theorem B3585485 : Blo 992597 3585485 := bstep (se 3 (by rfl) ⟨672278, by rfl⟩ : syracuseStep 3585485 = 1344557) B1344557
theorem B2242097 : Blo 992597 2242097 := bstep (se 2 (by rfl) ⟨840786, by rfl⟩ : syracuseStep 2242097 = 1681573) B1681573
theorem B1259059 : Blo 992597 1259059 := bstep (se 1 (by rfl) ⟨944294, by rfl⟩ : syracuseStep 1259059 = 1888589) B1888589
theorem B2242115 : Blo 992597 2242115 := bstep (se 1 (by rfl) ⟨1681586, by rfl⟩ : syracuseStep 2242115 = 3363173) B3363173
theorem B1062515 : Blo 992597 1062515 := bstep (se 1 (by rfl) ⟨796886, by rfl⟩ : syracuseStep 1062515 = 1593773) B1593773
theorem B1259155 : Blo 992597 1259155 := bstep (se 1 (by rfl) ⟨944366, by rfl⟩ : syracuseStep 1259155 = 1888733) B1888733
theorem B3356369 : Blo 992597 3356369 := bstep (se 2 (by rfl) ⟨1258638, by rfl⟩ : syracuseStep 3356369 = 2517277) B2517277
theorem B1062643 : Blo 992597 1062643 := bstep (se 1 (by rfl) ⟨796982, by rfl⟩ : syracuseStep 1062643 = 1593965) B1593965
theorem B3782477 : Blo 992597 3782477 := bstep (se 3 (by rfl) ⟨709214, by rfl⟩ : syracuseStep 3782477 = 1418429) B1418429
theorem B9680867 : Blo 992597 9680867 := bstep (se 1 (by rfl) ⟨7260650, by rfl⟩ : syracuseStep 9680867 = 14521301) B14521301
theorem B1488899 : Blo 992597 1488899 := bstep (se 1 (by rfl) ⟨1116674, by rfl⟩ : syracuseStep 1488899 = 2233349) B2233349
theorem B1488929 : Blo 992597 1488929 := bstep (se 2 (by rfl) ⟨558348, by rfl⟩ : syracuseStep 1488929 = 1116697) B1116697
theorem B1488947 : Blo 992597 1488947 := bstep (se 1 (by rfl) ⟨1116710, by rfl⟩ : syracuseStep 1488947 = 2233421) B2233421
theorem B1488977 : Blo 992597 1488977 := bstep (se 2 (by rfl) ⟨558366, by rfl⟩ : syracuseStep 1488977 = 1116733) B1116733
theorem B1488995 : Blo 992597 1488995 := bstep (se 1 (by rfl) ⟨1116746, by rfl⟩ : syracuseStep 1488995 = 2233493) B2233493
theorem B1489025 : Blo 992597 1489025 := bstep (se 2 (by rfl) ⟨558384, by rfl⟩ : syracuseStep 1489025 = 1116769) B1116769
theorem B1259651 : Blo 992597 1259651 := bstep (se 1 (by rfl) ⟨944738, by rfl⟩ : syracuseStep 1259651 = 1889477) B1889477
theorem B1489043 : Blo 992597 1489043 := bstep (se 1 (by rfl) ⟨1116782, by rfl⟩ : syracuseStep 1489043 = 2233565) B2233565
theorem B1489073 : Blo 992597 1489073 := bstep (se 2 (by rfl) ⟨558402, by rfl⟩ : syracuseStep 1489073 = 1116805) B1116805
theorem B4241585 : Blo 992597 4241585 := bstep (se 2 (by rfl) ⟨1590594, by rfl⟩ : syracuseStep 4241585 = 3181189) B3181189
theorem B1489091 : Blo 992597 1489091 := bstep (se 1 (by rfl) ⟨1116818, by rfl⟩ : syracuseStep 1489091 = 2233637) B2233637
theorem B1489121 : Blo 992597 1489121 := bstep (se 2 (by rfl) ⟨558420, by rfl⟩ : syracuseStep 1489121 = 1116841) B1116841
theorem B3356909 : Blo 992597 3356909 := bstep (se 3 (by rfl) ⟨629420, by rfl⟩ : syracuseStep 3356909 = 1258841) B1258841
theorem B1489139 : Blo 992597 1489139 := bstep (se 1 (by rfl) ⟨1116854, by rfl⟩ : syracuseStep 1489139 = 2233709) B2233709
theorem B1489169 : Blo 992597 1489169 := bstep (se 2 (by rfl) ⟨558438, by rfl⟩ : syracuseStep 1489169 = 1116877) B1116877
theorem B1489187 : Blo 992597 1489187 := bstep (se 1 (by rfl) ⟨1116890, by rfl⟩ : syracuseStep 1489187 = 2233781) B2233781
theorem B3356963 : Blo 992597 3356963 := bstep (se 1 (by rfl) ⟨2517722, by rfl⟩ : syracuseStep 3356963 = 5035445) B5035445
theorem B1489217 : Blo 992597 1489217 := bstep (se 2 (by rfl) ⟨558456, by rfl⟩ : syracuseStep 1489217 = 1116913) B1116913
theorem B1489235 : Blo 992597 1489235 := bstep (se 1 (by rfl) ⟨1116926, by rfl⟩ : syracuseStep 1489235 = 2233853) B2233853
theorem B1489265 : Blo 992597 1489265 := bstep (se 2 (by rfl) ⟨558474, by rfl⟩ : syracuseStep 1489265 = 1116949) B1116949
theorem B1489283 : Blo 992597 1489283 := bstep (se 1 (by rfl) ⟨1116962, by rfl⟩ : syracuseStep 1489283 = 2233925) B2233925
theorem B1489313 : Blo 992597 1489313 := bstep (se 2 (by rfl) ⟨558492, by rfl⟩ : syracuseStep 1489313 = 1116985) B1116985
theorem B2832803 : Blo 992597 2832803 := bstep (se 1 (by rfl) ⟨2124602, by rfl⟩ : syracuseStep 2832803 = 4249205) B4249205
theorem B1489331 : Blo 992597 1489331 := bstep (se 1 (by rfl) ⟨1116998, by rfl⟩ : syracuseStep 1489331 = 2233997) B2233997
theorem B1489361 : Blo 992597 1489361 := bstep (se 2 (by rfl) ⟨558510, by rfl⟩ : syracuseStep 1489361 = 1117021) B1117021
theorem B1489379 : Blo 992597 1489379 := bstep (se 1 (by rfl) ⟨1117034, by rfl⟩ : syracuseStep 1489379 = 2234069) B2234069
theorem B1489409 : Blo 992597 1489409 := bstep (se 2 (by rfl) ⟨558528, by rfl⟩ : syracuseStep 1489409 = 1117057) B1117057
theorem B1489427 : Blo 992597 1489427 := bstep (se 1 (by rfl) ⟨1117070, by rfl⟩ : syracuseStep 1489427 = 2234141) B2234141
theorem B1063459 : Blo 992597 1063459 := bstep (se 1 (by rfl) ⟨797594, by rfl⟩ : syracuseStep 1063459 = 1595189) B1595189
theorem B1489457 : Blo 992597 1489457 := bstep (se 2 (by rfl) ⟨558546, by rfl⟩ : syracuseStep 1489457 = 1117093) B1117093
theorem B3357233 : Blo 992597 3357233 := bstep (se 2 (by rfl) ⟨1258962, by rfl⟩ : syracuseStep 3357233 = 2517925) B2517925
theorem B1489475 : Blo 992597 1489475 := bstep (se 1 (by rfl) ⟨1117106, by rfl⟩ : syracuseStep 1489475 = 2234213) B2234213
theorem B1489505 : Blo 992597 1489505 := bstep (se 2 (by rfl) ⟨558564, by rfl⟩ : syracuseStep 1489505 = 1117129) B1117129
theorem B1489523 : Blo 992597 1489523 := bstep (se 1 (by rfl) ⟨1117142, by rfl⟩ : syracuseStep 1489523 = 2234285) B2234285
theorem B1489553 : Blo 992597 1489553 := bstep (se 2 (by rfl) ⟨558582, by rfl⟩ : syracuseStep 1489553 = 1117165) B1117165
theorem B1489571 : Blo 992597 1489571 := bstep (se 1 (by rfl) ⟨1117178, by rfl⟩ : syracuseStep 1489571 = 2234357) B2234357
theorem B1489601 : Blo 992597 1489601 := bstep (se 2 (by rfl) ⟨558600, by rfl⟩ : syracuseStep 1489601 = 1117201) B1117201
theorem B1489619 : Blo 992597 1489619 := bstep (se 1 (by rfl) ⟨1117214, by rfl⟩ : syracuseStep 1489619 = 2234429) B2234429
theorem B1489649 : Blo 992597 1489649 := bstep (se 2 (by rfl) ⟨558618, by rfl⟩ : syracuseStep 1489649 = 1117237) B1117237
theorem B1489667 : Blo 992597 1489667 := bstep (se 1 (by rfl) ⟨1117250, by rfl⟩ : syracuseStep 1489667 = 2234501) B2234501
theorem B1489697 : Blo 992597 1489697 := bstep (se 2 (by rfl) ⟨558636, by rfl⟩ : syracuseStep 1489697 = 1117273) B1117273
theorem B1489715 : Blo 992597 1489715 := bstep (se 1 (by rfl) ⟨1117286, by rfl⟩ : syracuseStep 1489715 = 2234573) B2234573
theorem B1260355 : Blo 992597 1260355 := bstep (se 1 (by rfl) ⟨945266, by rfl⟩ : syracuseStep 1260355 = 1890533) B1890533
theorem B1489745 : Blo 992597 1489745 := bstep (se 2 (by rfl) ⟨558654, by rfl⟩ : syracuseStep 1489745 = 1117309) B1117309
theorem B1489763 : Blo 992597 1489763 := bstep (se 1 (by rfl) ⟨1117322, by rfl⟩ : syracuseStep 1489763 = 2234645) B2234645
theorem B1489793 : Blo 992597 1489793 := bstep (se 2 (by rfl) ⟨558672, by rfl⟩ : syracuseStep 1489793 = 1117345) B1117345
theorem B1489811 : Blo 992597 1489811 := bstep (se 1 (by rfl) ⟨1117358, by rfl⟩ : syracuseStep 1489811 = 2234717) B2234717
theorem B1260451 : Blo 992597 1260451 := bstep (se 1 (by rfl) ⟨945338, by rfl⟩ : syracuseStep 1260451 = 1890677) B1890677
theorem B1489841 : Blo 992597 1489841 := bstep (se 2 (by rfl) ⟨558690, by rfl⟩ : syracuseStep 1489841 = 1117381) B1117381
theorem B1489859 : Blo 992597 1489859 := bstep (se 1 (by rfl) ⟨1117394, by rfl⟩ : syracuseStep 1489859 = 2234789) B2234789
theorem B1489889 : Blo 992597 1489889 := bstep (se 2 (by rfl) ⟨558708, by rfl⟩ : syracuseStep 1489889 = 1117417) B1117417
theorem B3029987 : Blo 992597 3029987 := bstep (se 1 (by rfl) ⟨2272490, by rfl⟩ : syracuseStep 3029987 = 4544981) B4544981
theorem B1489907 : Blo 992597 1489907 := bstep (se 1 (by rfl) ⟨1117430, by rfl⟩ : syracuseStep 1489907 = 2234861) B2234861
theorem B1489937 : Blo 992597 1489937 := bstep (se 2 (by rfl) ⟨558726, by rfl⟩ : syracuseStep 1489937 = 1117453) B1117453
theorem B1489955 : Blo 992597 1489955 := bstep (se 1 (by rfl) ⟨1117466, by rfl⟩ : syracuseStep 1489955 = 2234933) B2234933
theorem B1489985 : Blo 992597 1489985 := bstep (se 2 (by rfl) ⟨558744, by rfl⟩ : syracuseStep 1489985 = 1117489) B1117489
theorem B3357773 : Blo 992597 3357773 := bstep (se 3 (by rfl) ⟨629582, by rfl⟩ : syracuseStep 3357773 = 1259165) B1259165
theorem B1490003 : Blo 992597 1490003 := bstep (se 1 (by rfl) ⟨1117502, by rfl⟩ : syracuseStep 1490003 = 2235005) B2235005
theorem B1490033 : Blo 992597 1490033 := bstep (se 2 (by rfl) ⟨558762, by rfl⟩ : syracuseStep 1490033 = 1117525) B1117525
theorem B1490051 : Blo 992597 1490051 := bstep (se 1 (by rfl) ⟨1117538, by rfl⟩ : syracuseStep 1490051 = 2235077) B2235077
theorem B3357827 : Blo 992597 3357827 := bstep (se 1 (by rfl) ⟨2518370, by rfl⟩ : syracuseStep 3357827 = 5036741) B5036741
theorem B1490081 : Blo 992597 1490081 := bstep (se 2 (by rfl) ⟨558780, by rfl⟩ : syracuseStep 1490081 = 1117561) B1117561
theorem B1490099 : Blo 992597 1490099 := bstep (se 1 (by rfl) ⟨1117574, by rfl⟩ : syracuseStep 1490099 = 2235149) B2235149
theorem B2833613 : Blo 992597 2833613 := bstep (se 3 (by rfl) ⟨531302, by rfl⟩ : syracuseStep 2833613 = 1062605) B1062605
theorem B1490129 : Blo 992597 1490129 := bstep (se 2 (by rfl) ⟨558798, by rfl⟩ : syracuseStep 1490129 = 1117597) B1117597
theorem B1490147 : Blo 992597 1490147 := bstep (se 1 (by rfl) ⟨1117610, by rfl⟩ : syracuseStep 1490147 = 2235221) B2235221
theorem B1490177 : Blo 992597 1490177 := bstep (se 2 (by rfl) ⟨558816, by rfl⟩ : syracuseStep 1490177 = 1117633) B1117633
theorem B1490195 : Blo 992597 1490195 := bstep (se 1 (by rfl) ⟨1117646, by rfl⟩ : syracuseStep 1490195 = 2235293) B2235293
theorem B34389269 : Blo 992597 34389269 := bstep (se 6 (by rfl) ⟨805998, by rfl⟩ : syracuseStep 34389269 = 1611997) B1611997
theorem B1490225 : Blo 992597 1490225 := bstep (se 2 (by rfl) ⟨558834, by rfl⟩ : syracuseStep 1490225 = 1117669) B1117669
theorem B1490243 : Blo 992597 1490243 := bstep (se 1 (by rfl) ⟨1117682, by rfl⟩ : syracuseStep 1490243 = 2235365) B2235365
theorem B1490273 : Blo 992597 1490273 := bstep (se 2 (by rfl) ⟨558852, by rfl⟩ : syracuseStep 1490273 = 1117705) B1117705
theorem B1490291 : Blo 992597 1490291 := bstep (se 1 (by rfl) ⟨1117718, by rfl⟩ : syracuseStep 1490291 = 2235437) B2235437
theorem B2833805 : Blo 992597 2833805 := bstep (se 3 (by rfl) ⟨531338, by rfl⟩ : syracuseStep 2833805 = 1062677) B1062677
theorem B1490321 : Blo 992597 1490321 := bstep (se 2 (by rfl) ⟨558870, by rfl⟩ : syracuseStep 1490321 = 1117741) B1117741
theorem B3358097 : Blo 992597 3358097 := bstep (se 2 (by rfl) ⟨1259286, by rfl⟩ : syracuseStep 3358097 = 2518573) B2518573
theorem B1260947 : Blo 992597 1260947 := bstep (se 1 (by rfl) ⟨945710, by rfl⟩ : syracuseStep 1260947 = 1891421) B1891421
theorem B1490339 : Blo 992597 1490339 := bstep (se 1 (by rfl) ⟨1117754, by rfl⟩ : syracuseStep 1490339 = 2235509) B2235509
theorem B1490369 : Blo 992597 1490369 := bstep (se 2 (by rfl) ⟨558888, by rfl⟩ : syracuseStep 1490369 = 1117777) B1117777
theorem B2178499 : Blo 992597 2178499 := bstep (se 1 (by rfl) ⟨1633874, by rfl⟩ : syracuseStep 2178499 = 3267749) B3267749
theorem B1490387 : Blo 992597 1490387 := bstep (se 1 (by rfl) ⟨1117790, by rfl⟩ : syracuseStep 1490387 = 2235581) B2235581
theorem B1490417 : Blo 992597 1490417 := bstep (se 2 (by rfl) ⟨558906, by rfl⟩ : syracuseStep 1490417 = 1117813) B1117813
theorem B1490435 : Blo 992597 1490435 := bstep (se 1 (by rfl) ⟨1117826, by rfl⟩ : syracuseStep 1490435 = 2235653) B2235653
theorem B1490465 : Blo 992597 1490465 := bstep (se 2 (by rfl) ⟨558924, by rfl⟩ : syracuseStep 1490465 = 1117849) B1117849
theorem B1490483 : Blo 992597 1490483 := bstep (se 1 (by rfl) ⟨1117862, by rfl⟩ : syracuseStep 1490483 = 2235725) B2235725
theorem B1490513 : Blo 992597 1490513 := bstep (se 2 (by rfl) ⟨558942, by rfl⟩ : syracuseStep 1490513 = 1117885) B1117885
theorem B1490531 : Blo 992597 1490531 := bstep (se 1 (by rfl) ⟨1117898, by rfl⟩ : syracuseStep 1490531 = 2235797) B2235797
theorem B1490561 : Blo 992597 1490561 := bstep (se 2 (by rfl) ⟨558960, by rfl⟩ : syracuseStep 1490561 = 1117921) B1117921
theorem B1490579 : Blo 992597 1490579 := bstep (se 1 (by rfl) ⟨1117934, by rfl⟩ : syracuseStep 1490579 = 2235869) B2235869
theorem B1490609 : Blo 992597 1490609 := bstep (se 2 (by rfl) ⟨558978, by rfl⟩ : syracuseStep 1490609 = 1117957) B1117957
theorem B1490627 : Blo 992597 1490627 := bstep (se 1 (by rfl) ⟨1117970, by rfl⟩ : syracuseStep 1490627 = 2235941) B2235941
theorem B1490657 : Blo 992597 1490657 := bstep (se 2 (by rfl) ⟨558996, by rfl⟩ : syracuseStep 1490657 = 1117993) B1117993
theorem B2014961 : Blo 992597 2014961 := bstep (se 2 (by rfl) ⟨755610, by rfl⟩ : syracuseStep 2014961 = 1511221) B1511221
theorem B1490675 : Blo 992597 1490675 := bstep (se 1 (by rfl) ⟨1118006, by rfl⟩ : syracuseStep 1490675 = 2236013) B2236013
theorem B1490705 : Blo 992597 1490705 := bstep (se 2 (by rfl) ⟨559014, by rfl⟩ : syracuseStep 1490705 = 1118029) B1118029
theorem B1490723 : Blo 992597 1490723 := bstep (se 1 (by rfl) ⟨1118042, by rfl⟩ : syracuseStep 1490723 = 2236085) B2236085
theorem B1490753 : Blo 992597 1490753 := bstep (se 2 (by rfl) ⟨559032, by rfl⟩ : syracuseStep 1490753 = 1118065) B1118065
theorem B1490771 : Blo 992597 1490771 := bstep (se 1 (by rfl) ⟨1118078, by rfl⟩ : syracuseStep 1490771 = 2236157) B2236157
theorem B1490801 : Blo 992597 1490801 := bstep (se 2 (by rfl) ⟨559050, by rfl⟩ : syracuseStep 1490801 = 1118101) B1118101
theorem B1490819 : Blo 992597 1490819 := bstep (se 1 (by rfl) ⟨1118114, by rfl⟩ : syracuseStep 1490819 = 2236229) B2236229
theorem B1490849 : Blo 992597 1490849 := bstep (se 2 (by rfl) ⟨559068, by rfl⟩ : syracuseStep 1490849 = 1118137) B1118137
theorem B3358637 : Blo 992597 3358637 := bstep (se 3 (by rfl) ⟨629744, by rfl⟩ : syracuseStep 3358637 = 1259489) B1259489
theorem B1490867 : Blo 992597 1490867 := bstep (se 1 (by rfl) ⟨1118150, by rfl⟩ : syracuseStep 1490867 = 2236301) B2236301
theorem B6799301 : Blo 992597 6799301 := bstep (se 4 (by rfl) ⟨637434, by rfl⟩ : syracuseStep 6799301 = 1274869) B1274869
theorem B1490897 : Blo 992597 1490897 := bstep (se 2 (by rfl) ⟨559086, by rfl⟩ : syracuseStep 1490897 = 1118173) B1118173
theorem B1490915 : Blo 992597 1490915 := bstep (se 1 (by rfl) ⟨1118186, by rfl⟩ : syracuseStep 1490915 = 2236373) B2236373
theorem B3358691 : Blo 992597 3358691 := bstep (se 1 (by rfl) ⟨2519018, by rfl⟩ : syracuseStep 3358691 = 5038037) B5038037
theorem B1490945 : Blo 992597 1490945 := bstep (se 2 (by rfl) ⟨559104, by rfl⟩ : syracuseStep 1490945 = 1118209) B1118209
theorem B1490963 : Blo 992597 1490963 := bstep (se 1 (by rfl) ⟨1118222, by rfl⟩ : syracuseStep 1490963 = 2236445) B2236445
theorem B22986773 : Blo 992597 22986773 := bstep (se 6 (by rfl) ⟨538752, by rfl⟩ : syracuseStep 22986773 = 1077505) B1077505
theorem B5029937 : Blo 992597 5029937 := bstep (se 2 (by rfl) ⟨1886226, by rfl⟩ : syracuseStep 5029937 = 3772453) B3772453
theorem B1490993 : Blo 992597 1490993 := bstep (se 2 (by rfl) ⟨559122, by rfl⟩ : syracuseStep 1490993 = 1118245) B1118245
theorem B1491011 : Blo 992597 1491011 := bstep (se 1 (by rfl) ⟨1118258, by rfl⟩ : syracuseStep 1491011 = 2236517) B2236517
theorem B1491041 : Blo 992597 1491041 := bstep (se 2 (by rfl) ⟨559140, by rfl⟩ : syracuseStep 1491041 = 1118281) B1118281
theorem B1491059 : Blo 992597 1491059 := bstep (se 1 (by rfl) ⟨1118294, by rfl⟩ : syracuseStep 1491059 = 2236589) B2236589
theorem B3227789 : Blo 992597 3227789 := bstep (se 3 (by rfl) ⟨605210, by rfl⟩ : syracuseStep 3227789 = 1210421) B1210421
theorem B1491089 : Blo 992597 1491089 := bstep (se 2 (by rfl) ⟨559158, by rfl⟩ : syracuseStep 1491089 = 1118317) B1118317
theorem B1491107 : Blo 992597 1491107 := bstep (se 1 (by rfl) ⟨1118330, by rfl⟩ : syracuseStep 1491107 = 2236661) B2236661
theorem B1491137 : Blo 992597 1491137 := bstep (se 2 (by rfl) ⟨559176, by rfl⟩ : syracuseStep 1491137 = 1118353) B1118353
theorem B1491155 : Blo 992597 1491155 := bstep (se 1 (by rfl) ⟨1118366, by rfl⟩ : syracuseStep 1491155 = 2236733) B2236733
theorem B1491185 : Blo 992597 1491185 := bstep (se 2 (by rfl) ⟨559194, by rfl⟩ : syracuseStep 1491185 = 1118389) B1118389
theorem B3358961 : Blo 992597 3358961 := bstep (se 2 (by rfl) ⟨1259610, by rfl⟩ : syracuseStep 3358961 = 2519221) B2519221
theorem B1491203 : Blo 992597 1491203 := bstep (se 1 (by rfl) ⟨1118402, by rfl⟩ : syracuseStep 1491203 = 2236805) B2236805
theorem B1491233 : Blo 992597 1491233 := bstep (se 2 (by rfl) ⟨559212, by rfl⟩ : syracuseStep 1491233 = 1118425) B1118425
theorem B1491251 : Blo 992597 1491251 := bstep (se 1 (by rfl) ⟨1118438, by rfl⟩ : syracuseStep 1491251 = 2236877) B2236877
theorem B1491281 : Blo 992597 1491281 := bstep (se 2 (by rfl) ⟨559230, by rfl⟩ : syracuseStep 1491281 = 1118461) B1118461
theorem B1491299 : Blo 992597 1491299 := bstep (se 1 (by rfl) ⟨1118474, by rfl⟩ : syracuseStep 1491299 = 2236949) B2236949
theorem B2834797 : Blo 992597 2834797 := bstep (se 3 (by rfl) ⟨531524, by rfl⟩ : syracuseStep 2834797 = 1063049) B1063049
theorem B3064177 : Blo 992597 3064177 := bstep (se 2 (by rfl) ⟨1149066, by rfl⟩ : syracuseStep 3064177 = 2298133) B2298133
theorem B1491329 : Blo 992597 1491329 := bstep (se 2 (by rfl) ⟨559248, by rfl⟩ : syracuseStep 1491329 = 1118497) B1118497
theorem B1491347 : Blo 992597 1491347 := bstep (se 1 (by rfl) ⟨1118510, by rfl⟩ : syracuseStep 1491347 = 2237021) B2237021
theorem B1491377 : Blo 992597 1491377 := bstep (se 2 (by rfl) ⟨559266, by rfl⟩ : syracuseStep 1491377 = 1118533) B1118533
theorem B1491395 : Blo 992597 1491395 := bstep (se 1 (by rfl) ⟨1118546, by rfl⟩ : syracuseStep 1491395 = 2237093) B2237093
theorem B14336453 : Blo 992597 14336453 := bstep (se 4 (by rfl) ⟨1344042, by rfl⟩ : syracuseStep 14336453 = 2688085) B2688085
theorem B1491425 : Blo 992597 1491425 := bstep (se 2 (by rfl) ⟨559284, by rfl⟩ : syracuseStep 1491425 = 1118569) B1118569
theorem B1491443 : Blo 992597 1491443 := bstep (se 1 (by rfl) ⟨1118582, by rfl⟩ : syracuseStep 1491443 = 2237165) B2237165
theorem B1491473 : Blo 992597 1491473 := bstep (se 2 (by rfl) ⟨559302, by rfl⟩ : syracuseStep 1491473 = 1118605) B1118605
theorem B1491491 : Blo 992597 1491491 := bstep (se 1 (by rfl) ⟨1118618, by rfl⟩ : syracuseStep 1491491 = 2237237) B2237237
theorem B1491521 : Blo 992597 1491521 := bstep (se 2 (by rfl) ⟨559320, by rfl⟩ : syracuseStep 1491521 = 1118641) B1118641
theorem B1491539 : Blo 992597 1491539 := bstep (se 1 (by rfl) ⟨1118654, by rfl⟩ : syracuseStep 1491539 = 2237309) B2237309
theorem B1491569 : Blo 992597 1491569 := bstep (se 2 (by rfl) ⟨559338, by rfl⟩ : syracuseStep 1491569 = 1118677) B1118677
theorem B1491587 : Blo 992597 1491587 := bstep (se 1 (by rfl) ⟨1118690, by rfl⟩ : syracuseStep 1491587 = 2237381) B2237381
theorem B1491617 : Blo 992597 1491617 := bstep (se 2 (by rfl) ⟨559356, by rfl⟩ : syracuseStep 1491617 = 1118713) B1118713
theorem B1491635 : Blo 992597 1491635 := bstep (se 1 (by rfl) ⟨1118726, by rfl⟩ : syracuseStep 1491635 = 2237453) B2237453
theorem B1491665 : Blo 992597 1491665 := bstep (se 2 (by rfl) ⟨559374, by rfl⟩ : syracuseStep 1491665 = 1118749) B1118749
theorem B1491683 : Blo 992597 1491683 := bstep (se 1 (by rfl) ⟨1118762, by rfl⟩ : syracuseStep 1491683 = 2237525) B2237525
theorem B1491713 : Blo 992597 1491713 := bstep (se 2 (by rfl) ⟨559392, by rfl⟩ : syracuseStep 1491713 = 1118785) B1118785
theorem B6898445 : Blo 992597 6898445 := bstep (se 3 (by rfl) ⟨1293458, by rfl⟩ : syracuseStep 6898445 = 2586917) B2586917
theorem B3359501 : Blo 992597 3359501 := bstep (se 3 (by rfl) ⟨629906, by rfl⟩ : syracuseStep 3359501 = 1259813) B1259813
theorem B1491731 : Blo 992597 1491731 := bstep (se 1 (by rfl) ⟨1118798, by rfl⟩ : syracuseStep 1491731 = 2237597) B2237597
theorem B1491761 : Blo 992597 1491761 := bstep (se 2 (by rfl) ⟨559410, by rfl⟩ : syracuseStep 1491761 = 1118821) B1118821
theorem B1491779 : Blo 992597 1491779 := bstep (se 1 (by rfl) ⟨1118834, by rfl⟩ : syracuseStep 1491779 = 2237669) B2237669
theorem B3359555 : Blo 992597 3359555 := bstep (se 1 (by rfl) ⟨2519666, by rfl⟩ : syracuseStep 3359555 = 5039333) B5039333
theorem B1491809 : Blo 992597 1491809 := bstep (se 2 (by rfl) ⟨559428, by rfl⟩ : syracuseStep 1491809 = 1118857) B1118857
theorem B1885027 : Blo 992597 1885027 := bstep (se 1 (by rfl) ⟨1413770, by rfl⟩ : syracuseStep 1885027 = 2827541) B2827541
theorem B1491827 : Blo 992597 1491827 := bstep (se 1 (by rfl) ⟨1118870, by rfl⟩ : syracuseStep 1491827 = 2237741) B2237741
theorem B1491857 : Blo 992597 1491857 := bstep (se 2 (by rfl) ⟨559446, by rfl⟩ : syracuseStep 1491857 = 1118893) B1118893
theorem B1491875 : Blo 992597 1491875 := bstep (se 1 (by rfl) ⟨1118906, by rfl⟩ : syracuseStep 1491875 = 2237813) B2237813
theorem B6374321 : Blo 992597 6374321 := bstep (se 2 (by rfl) ⟨2390370, by rfl⟩ : syracuseStep 6374321 = 4780741) B4780741
theorem B4309937 : Blo 992597 4309937 := bstep (se 2 (by rfl) ⟨1616226, by rfl⟩ : syracuseStep 4309937 = 3232453) B3232453
theorem B1491905 : Blo 992597 1491905 := bstep (se 2 (by rfl) ⟨559464, by rfl⟩ : syracuseStep 1491905 = 1118929) B1118929
theorem B4539341 : Blo 992597 4539341 := bstep (se 3 (by rfl) ⟨851126, by rfl⟩ : syracuseStep 4539341 = 1702253) B1702253
theorem B1491923 : Blo 992597 1491923 := bstep (se 1 (by rfl) ⟨1118942, by rfl⟩ : syracuseStep 1491923 = 2237885) B2237885
theorem B1491953 : Blo 992597 1491953 := bstep (se 2 (by rfl) ⟨559482, by rfl⟩ : syracuseStep 1491953 = 1118965) B1118965
theorem B1885187 : Blo 992597 1885187 := bstep (se 1 (by rfl) ⟨1413890, by rfl⟩ : syracuseStep 1885187 = 2827781) B2827781
theorem B1491971 : Blo 992597 1491971 := bstep (se 1 (by rfl) ⟨1118978, by rfl⟩ : syracuseStep 1491971 = 2237957) B2237957
theorem B1492001 : Blo 992597 1492001 := bstep (se 2 (by rfl) ⟨559500, by rfl⟩ : syracuseStep 1492001 = 1119001) B1119001
theorem B1492019 : Blo 992597 1492019 := bstep (se 1 (by rfl) ⟨1119014, by rfl⟩ : syracuseStep 1492019 = 2238029) B2238029
theorem B4244557 : Blo 992597 4244557 := bstep (se 3 (by rfl) ⟨795854, by rfl⟩ : syracuseStep 4244557 = 1591709) B1591709
theorem B1492049 : Blo 992597 1492049 := bstep (se 2 (by rfl) ⟨559518, by rfl⟩ : syracuseStep 1492049 = 1119037) B1119037
theorem B3359825 : Blo 992597 3359825 := bstep (se 2 (by rfl) ⟨1259934, by rfl⟩ : syracuseStep 3359825 = 2519869) B2519869
theorem B1590371 : Blo 992597 1590371 := bstep (se 1 (by rfl) ⟨1192778, by rfl⟩ : syracuseStep 1590371 = 2385557) B2385557
theorem B1492067 : Blo 992597 1492067 := bstep (se 1 (by rfl) ⟨1119050, by rfl⟩ : syracuseStep 1492067 = 2238101) B2238101
theorem B1492097 : Blo 992597 1492097 := bstep (se 2 (by rfl) ⟨559536, by rfl⟩ : syracuseStep 1492097 = 1119073) B1119073
theorem B1492115 : Blo 992597 1492115 := bstep (se 1 (by rfl) ⟨1119086, by rfl⟩ : syracuseStep 1492115 = 2238173) B2238173
theorem B1492145 : Blo 992597 1492145 := bstep (se 2 (by rfl) ⟨559554, by rfl⟩ : syracuseStep 1492145 = 1119109) B1119109
theorem B1492163 : Blo 992597 1492163 := bstep (se 1 (by rfl) ⟨1119122, by rfl⟩ : syracuseStep 1492163 = 2238245) B2238245
theorem B1492193 : Blo 992597 1492193 := bstep (se 2 (by rfl) ⟨559572, by rfl⟩ : syracuseStep 1492193 = 1119145) B1119145
theorem B1492211 : Blo 992597 1492211 := bstep (se 1 (by rfl) ⟨1119158, by rfl⟩ : syracuseStep 1492211 = 2238317) B2238317
theorem B3228931 : Blo 992597 3228931 := bstep (se 1 (by rfl) ⟨2421698, by rfl⟩ : syracuseStep 3228931 = 4843397) B4843397
theorem B10110221 : Blo 992597 10110221 := bstep (se 3 (by rfl) ⟨1895666, by rfl⟩ : syracuseStep 10110221 = 3791333) B3791333
theorem B1492241 : Blo 992597 1492241 := bstep (se 2 (by rfl) ⟨559590, by rfl⟩ : syracuseStep 1492241 = 1119181) B1119181
theorem B1492259 : Blo 992597 1492259 := bstep (se 1 (by rfl) ⟨1119194, by rfl⟩ : syracuseStep 1492259 = 2238389) B2238389
theorem B1492289 : Blo 992597 1492289 := bstep (se 2 (by rfl) ⟨559608, by rfl⟩ : syracuseStep 1492289 = 1119217) B1119217
theorem B1492307 : Blo 992597 1492307 := bstep (se 1 (by rfl) ⟨1119230, by rfl⟩ : syracuseStep 1492307 = 2238461) B2238461
theorem B1492337 : Blo 992597 1492337 := bstep (se 2 (by rfl) ⟨559626, by rfl⟩ : syracuseStep 1492337 = 1119253) B1119253
theorem B1492355 : Blo 992597 1492355 := bstep (se 1 (by rfl) ⟨1119266, by rfl⟩ : syracuseStep 1492355 = 2238533) B2238533
theorem B6800773 : Blo 992597 6800773 := bstep (se 4 (by rfl) ⟨637572, by rfl⟩ : syracuseStep 6800773 = 1275145) B1275145
theorem B1492385 : Blo 992597 1492385 := bstep (se 2 (by rfl) ⟨559644, by rfl⟩ : syracuseStep 1492385 = 1119289) B1119289
theorem B4244899 : Blo 992597 4244899 := bstep (se 1 (by rfl) ⟨3183674, by rfl⟩ : syracuseStep 4244899 = 6367349) B6367349
theorem B1492403 : Blo 992597 1492403 := bstep (se 1 (by rfl) ⟨1119302, by rfl⟩ : syracuseStep 1492403 = 2238605) B2238605
theorem B1492433 : Blo 992597 1492433 := bstep (se 2 (by rfl) ⟨559662, by rfl⟩ : syracuseStep 1492433 = 1119325) B1119325
theorem B5031395 : Blo 992597 5031395 := bstep (se 1 (by rfl) ⟨3773546, by rfl⟩ : syracuseStep 5031395 = 7547093) B7547093
theorem B1492451 : Blo 992597 1492451 := bstep (se 1 (by rfl) ⟨1119338, by rfl⟩ : syracuseStep 1492451 = 2238677) B2238677
theorem B1492481 : Blo 992597 1492481 := bstep (se 2 (by rfl) ⟨559680, by rfl⟩ : syracuseStep 1492481 = 1119361) B1119361
theorem B1492499 : Blo 992597 1492499 := bstep (se 1 (by rfl) ⟨1119374, by rfl⟩ : syracuseStep 1492499 = 2238749) B2238749
theorem B1492529 : Blo 992597 1492529 := bstep (se 2 (by rfl) ⟨559698, by rfl⟩ : syracuseStep 1492529 = 1119397) B1119397
theorem B1492547 : Blo 992597 1492547 := bstep (se 1 (by rfl) ⟨1119410, by rfl⟩ : syracuseStep 1492547 = 2238821) B2238821
theorem B1492577 : Blo 992597 1492577 := bstep (se 2 (by rfl) ⟨559716, by rfl⟩ : syracuseStep 1492577 = 1119433) B1119433
theorem B3360365 : Blo 992597 3360365 := bstep (se 3 (by rfl) ⟨630068, by rfl⟩ : syracuseStep 3360365 = 1260137) B1260137
theorem B1492595 : Blo 992597 1492595 := bstep (se 1 (by rfl) ⟨1119446, by rfl⟩ : syracuseStep 1492595 = 2238893) B2238893
theorem B1492625 : Blo 992597 1492625 := bstep (se 2 (by rfl) ⟨559734, by rfl⟩ : syracuseStep 1492625 = 1119469) B1119469
theorem B1492643 : Blo 992597 1492643 := bstep (se 1 (by rfl) ⟨1119482, by rfl⟩ : syracuseStep 1492643 = 2238965) B2238965
theorem B3360419 : Blo 992597 3360419 := bstep (se 1 (by rfl) ⟨2520314, by rfl⟩ : syracuseStep 3360419 = 5040629) B5040629
theorem B1492673 : Blo 992597 1492673 := bstep (se 2 (by rfl) ⟨559752, by rfl⟩ : syracuseStep 1492673 = 1119505) B1119505
theorem B1492691 : Blo 992597 1492691 := bstep (se 1 (by rfl) ⟨1119518, by rfl⟩ : syracuseStep 1492691 = 2239037) B2239037
theorem B1492721 : Blo 992597 1492721 := bstep (se 2 (by rfl) ⟨559770, by rfl⟩ : syracuseStep 1492721 = 1119541) B1119541
theorem B1492739 : Blo 992597 1492739 := bstep (se 1 (by rfl) ⟨1119554, by rfl⟩ : syracuseStep 1492739 = 2239109) B2239109
theorem B5654285 : Blo 992597 5654285 := bstep (se 3 (by rfl) ⟨1060178, by rfl⟩ : syracuseStep 5654285 = 2120357) B2120357
theorem B1492769 : Blo 992597 1492769 := bstep (se 2 (by rfl) ⟨559788, by rfl⟩ : syracuseStep 1492769 = 1119577) B1119577
theorem B1492787 : Blo 992597 1492787 := bstep (se 1 (by rfl) ⟨1119590, by rfl⟩ : syracuseStep 1492787 = 2239181) B2239181
theorem B1492817 : Blo 992597 1492817 := bstep (se 2 (by rfl) ⟨559806, by rfl⟩ : syracuseStep 1492817 = 1119613) B1119613
theorem B1492835 : Blo 992597 1492835 := bstep (se 1 (by rfl) ⟨1119626, by rfl⟩ : syracuseStep 1492835 = 2239253) B2239253
theorem B1492865 : Blo 992597 1492865 := bstep (se 2 (by rfl) ⟨559824, by rfl⟩ : syracuseStep 1492865 = 1119649) B1119649
theorem B1492883 : Blo 992597 1492883 := bstep (se 1 (by rfl) ⟨1119662, by rfl⟩ : syracuseStep 1492883 = 2239325) B2239325
theorem B1492913 : Blo 992597 1492913 := bstep (se 2 (by rfl) ⟨559842, by rfl⟩ : syracuseStep 1492913 = 1119685) B1119685
theorem B3360689 : Blo 992597 3360689 := bstep (se 2 (by rfl) ⟨1260258, by rfl⟩ : syracuseStep 3360689 = 2520517) B2520517
theorem B1492931 : Blo 992597 1492931 := bstep (se 1 (by rfl) ⟨1119698, by rfl⟩ : syracuseStep 1492931 = 2239397) B2239397
theorem B1492961 : Blo 992597 1492961 := bstep (se 2 (by rfl) ⟨559860, by rfl⟩ : syracuseStep 1492961 = 1119721) B1119721
theorem B1492979 : Blo 992597 1492979 := bstep (se 1 (by rfl) ⟨1119734, by rfl⟩ : syracuseStep 1492979 = 2239469) B2239469
theorem B1493009 : Blo 992597 1493009 := bstep (se 2 (by rfl) ⟨559878, by rfl⟩ : syracuseStep 1493009 = 1119757) B1119757
theorem B1361953 : Blo 992597 1361953 := bstep (se 2 (by rfl) ⟨510732, by rfl⟩ : syracuseStep 1361953 = 1021465) B1021465
theorem B1493027 : Blo 992597 1493027 := bstep (se 1 (by rfl) ⟨1119770, by rfl⟩ : syracuseStep 1493027 = 2239541) B2239541
theorem B1886257 : Blo 992597 1886257 := bstep (se 2 (by rfl) ⟨707346, by rfl⟩ : syracuseStep 1886257 = 1414693) B1414693
theorem B2836529 : Blo 992597 2836529 := bstep (se 2 (by rfl) ⟨1063698, by rfl⟩ : syracuseStep 2836529 = 2127397) B2127397
theorem B1493057 : Blo 992597 1493057 := bstep (se 2 (by rfl) ⟨559896, by rfl⟩ : syracuseStep 1493057 = 1119793) B1119793
theorem B1493075 : Blo 992597 1493075 := bstep (se 1 (by rfl) ⟨1119806, by rfl⟩ : syracuseStep 1493075 = 2239613) B2239613
theorem B1493105 : Blo 992597 1493105 := bstep (se 2 (by rfl) ⟨559914, by rfl⟩ : syracuseStep 1493105 = 1119829) B1119829
theorem B3590257 : Blo 992597 3590257 := bstep (se 2 (by rfl) ⟨1346346, by rfl⟩ : syracuseStep 3590257 = 2692693) B2692693
theorem B1493123 : Blo 992597 1493123 := bstep (se 1 (by rfl) ⟨1119842, by rfl⟩ : syracuseStep 1493123 = 2239685) B2239685
theorem B8505485 : Blo 992597 8505485 := bstep (se 3 (by rfl) ⟨1594778, by rfl⟩ : syracuseStep 8505485 = 3189557) B3189557
theorem B1493153 : Blo 992597 1493153 := bstep (se 2 (by rfl) ⟨559932, by rfl⟩ : syracuseStep 1493153 = 1119865) B1119865
theorem B1493171 : Blo 992597 1493171 := bstep (se 1 (by rfl) ⟨1119878, by rfl⟩ : syracuseStep 1493171 = 2239757) B2239757
theorem B1493201 : Blo 992597 1493201 := bstep (se 2 (by rfl) ⟨559950, by rfl⟩ : syracuseStep 1493201 = 1119901) B1119901
theorem B1493219 : Blo 992597 1493219 := bstep (se 1 (by rfl) ⟨1119914, by rfl⟩ : syracuseStep 1493219 = 2239829) B2239829
theorem B2836721 : Blo 992597 2836721 := bstep (se 2 (by rfl) ⟨1063770, by rfl⟩ : syracuseStep 2836721 = 2127541) B2127541
theorem B1493249 : Blo 992597 1493249 := bstep (se 2 (by rfl) ⟨559968, by rfl⟩ : syracuseStep 1493249 = 1119937) B1119937
theorem B5032205 : Blo 992597 5032205 := bstep (se 3 (by rfl) ⟨943538, by rfl⟩ : syracuseStep 5032205 = 1887077) B1887077
theorem B1493267 : Blo 992597 1493267 := bstep (se 1 (by rfl) ⟨1119950, by rfl⟩ : syracuseStep 1493267 = 2239901) B2239901
theorem B1493297 : Blo 992597 1493297 := bstep (se 2 (by rfl) ⟨559986, by rfl⟩ : syracuseStep 1493297 = 1119973) B1119973
theorem B1493315 : Blo 992597 1493315 := bstep (se 1 (by rfl) ⟨1119986, by rfl⟩ : syracuseStep 1493315 = 2239973) B2239973
theorem B1493345 : Blo 992597 1493345 := bstep (se 2 (by rfl) ⟨560004, by rfl⟩ : syracuseStep 1493345 = 1120009) B1120009
theorem B1493363 : Blo 992597 1493363 := bstep (se 1 (by rfl) ⟨1120022, by rfl⟩ : syracuseStep 1493363 = 2240045) B2240045
theorem B1362305 : Blo 992597 1362305 := bstep (se 2 (by rfl) ⟨510864, by rfl⟩ : syracuseStep 1362305 = 1021729) B1021729
theorem B1493393 : Blo 992597 1493393 := bstep (se 2 (by rfl) ⟨560022, by rfl⟩ : syracuseStep 1493393 = 1120045) B1120045
theorem B1493411 : Blo 992597 1493411 := bstep (se 1 (by rfl) ⟨1120058, by rfl⟩ : syracuseStep 1493411 = 2240117) B2240117
theorem B1493441 : Blo 992597 1493441 := bstep (se 2 (by rfl) ⟨560040, by rfl⟩ : syracuseStep 1493441 = 1120081) B1120081
theorem B3361229 : Blo 992597 3361229 := bstep (se 3 (by rfl) ⟨630230, by rfl⟩ : syracuseStep 3361229 = 1260461) B1260461
theorem B1493459 : Blo 992597 1493459 := bstep (se 1 (by rfl) ⟨1120094, by rfl⟩ : syracuseStep 1493459 = 2240189) B2240189
theorem B1493489 : Blo 992597 1493489 := bstep (se 2 (by rfl) ⟨560058, by rfl⟩ : syracuseStep 1493489 = 1120117) B1120117
theorem B1493507 : Blo 992597 1493507 := bstep (se 1 (by rfl) ⟨1120130, by rfl⟩ : syracuseStep 1493507 = 2240261) B2240261
theorem B3361283 : Blo 992597 3361283 := bstep (se 1 (by rfl) ⟨2520962, by rfl⟩ : syracuseStep 3361283 = 5041925) B5041925
theorem B1591825 : Blo 992597 1591825 := bstep (se 2 (by rfl) ⟨596934, by rfl⟩ : syracuseStep 1591825 = 1193869) B1193869
theorem B1493537 : Blo 992597 1493537 := bstep (se 2 (by rfl) ⟨560076, by rfl⟩ : syracuseStep 1493537 = 1120153) B1120153
theorem B1493555 : Blo 992597 1493555 := bstep (se 1 (by rfl) ⟨1120166, by rfl⟩ : syracuseStep 1493555 = 2240333) B2240333
theorem B1493585 : Blo 992597 1493585 := bstep (se 2 (by rfl) ⟨560094, by rfl⟩ : syracuseStep 1493585 = 1120189) B1120189
theorem B4082275 : Blo 992597 4082275 := bstep (se 1 (by rfl) ⟨3061706, by rfl⟩ : syracuseStep 4082275 = 6123413) B6123413
theorem B1493603 : Blo 992597 1493603 := bstep (se 1 (by rfl) ⟨1120202, by rfl⟩ : syracuseStep 1493603 = 2240405) B2240405
theorem B1493633 : Blo 992597 1493633 := bstep (se 2 (by rfl) ⟨560112, by rfl⟩ : syracuseStep 1493633 = 1120225) B1120225
theorem B1493651 : Blo 992597 1493651 := bstep (se 1 (by rfl) ⟨1120238, by rfl⟩ : syracuseStep 1493651 = 2240477) B2240477
theorem B5655217 : Blo 992597 5655217 := bstep (se 2 (by rfl) ⟨2120706, by rfl⟩ : syracuseStep 5655217 = 4241413) B4241413
theorem B1493681 : Blo 992597 1493681 := bstep (se 2 (by rfl) ⟨560130, by rfl⟩ : syracuseStep 1493681 = 1120261) B1120261
theorem B1493699 : Blo 992597 1493699 := bstep (se 1 (by rfl) ⟨1120274, by rfl⟩ : syracuseStep 1493699 = 2240549) B2240549
theorem B1493729 : Blo 992597 1493729 := bstep (se 2 (by rfl) ⟨560148, by rfl⟩ : syracuseStep 1493729 = 1120297) B1120297
theorem B1493747 : Blo 992597 1493747 := bstep (se 1 (by rfl) ⟨1120310, by rfl⟩ : syracuseStep 1493747 = 2240621) B2240621
theorem B1493777 : Blo 992597 1493777 := bstep (se 2 (by rfl) ⟨560166, by rfl⟩ : syracuseStep 1493777 = 1120333) B1120333
theorem B3361553 : Blo 992597 3361553 := bstep (se 2 (by rfl) ⟨1260582, by rfl⟩ : syracuseStep 3361553 = 2521165) B2521165
theorem B1493795 : Blo 992597 1493795 := bstep (se 1 (by rfl) ⟨1120346, by rfl⟩ : syracuseStep 1493795 = 2240693) B2240693
theorem B1493825 : Blo 992597 1493825 := bstep (se 2 (by rfl) ⟨560184, by rfl⟩ : syracuseStep 1493825 = 1120369) B1120369
theorem B1493843 : Blo 992597 1493843 := bstep (se 1 (by rfl) ⟨1120382, by rfl⟩ : syracuseStep 1493843 = 2240765) B2240765
theorem B1493873 : Blo 992597 1493873 := bstep (se 2 (by rfl) ⟨560202, by rfl⟩ : syracuseStep 1493873 = 1120405) B1120405
theorem B1493891 : Blo 992597 1493891 := bstep (se 1 (by rfl) ⟨1120418, by rfl⟩ : syracuseStep 1493891 = 2240837) B2240837
theorem B1493921 : Blo 992597 1493921 := bstep (se 2 (by rfl) ⟨560220, by rfl⟩ : syracuseStep 1493921 = 1120441) B1120441
theorem B5098403 : Blo 992597 5098403 := bstep (se 1 (by rfl) ⟨3823802, by rfl⟩ : syracuseStep 5098403 = 7647605) B7647605
theorem B1493939 : Blo 992597 1493939 := bstep (se 1 (by rfl) ⟨1120454, by rfl⟩ : syracuseStep 1493939 = 2240909) B2240909
theorem B1493969 : Blo 992597 1493969 := bstep (se 2 (by rfl) ⟨560238, by rfl⟩ : syracuseStep 1493969 = 1120477) B1120477
theorem B1493987 : Blo 992597 1493987 := bstep (se 1 (by rfl) ⟨1120490, by rfl⟩ : syracuseStep 1493987 = 2240981) B2240981
theorem B1494017 : Blo 992597 1494017 := bstep (se 2 (by rfl) ⟨560256, by rfl⟩ : syracuseStep 1494017 = 1120513) B1120513
theorem B1494035 : Blo 992597 1494035 := bstep (se 1 (by rfl) ⟨1120526, by rfl⟩ : syracuseStep 1494035 = 2241053) B2241053
theorem B1494065 : Blo 992597 1494065 := bstep (se 2 (by rfl) ⟨560274, by rfl⟩ : syracuseStep 1494065 = 1120549) B1120549
theorem B1494083 : Blo 992597 1494083 := bstep (se 1 (by rfl) ⟨1120562, by rfl⟩ : syracuseStep 1494083 = 2241125) B2241125
theorem B1887313 : Blo 992597 1887313 := bstep (se 2 (by rfl) ⟨707742, by rfl⟩ : syracuseStep 1887313 = 1415485) B1415485
theorem B1494113 : Blo 992597 1494113 := bstep (se 2 (by rfl) ⟨560292, by rfl⟩ : syracuseStep 1494113 = 1120585) B1120585
theorem B1494131 : Blo 992597 1494131 := bstep (se 1 (by rfl) ⟨1120598, by rfl⟩ : syracuseStep 1494131 = 2241197) B2241197
theorem B1494161 : Blo 992597 1494161 := bstep (se 2 (by rfl) ⟨560310, by rfl⟩ : syracuseStep 1494161 = 1120621) B1120621
theorem B1494179 : Blo 992597 1494179 := bstep (se 1 (by rfl) ⟨1120634, by rfl⟩ : syracuseStep 1494179 = 2241269) B2241269
theorem B1494209 : Blo 992597 1494209 := bstep (se 2 (by rfl) ⟨560328, by rfl⟩ : syracuseStep 1494209 = 1120657) B1120657
theorem B2837713 : Blo 992597 2837713 := bstep (se 2 (by rfl) ⟨1064142, by rfl⟩ : syracuseStep 2837713 = 2128285) B2128285
theorem B1494227 : Blo 992597 1494227 := bstep (se 1 (by rfl) ⟨1120670, by rfl⟩ : syracuseStep 1494227 = 2241341) B2241341
theorem B1494257 : Blo 992597 1494257 := bstep (se 2 (by rfl) ⟨560346, by rfl⟩ : syracuseStep 1494257 = 1120693) B1120693
theorem B1494275 : Blo 992597 1494275 := bstep (se 1 (by rfl) ⟨1120706, by rfl⟩ : syracuseStep 1494275 = 2241413) B2241413
theorem B1494305 : Blo 992597 1494305 := bstep (se 2 (by rfl) ⟨560364, by rfl⟩ : syracuseStep 1494305 = 1120729) B1120729
theorem B3362093 : Blo 992597 3362093 := bstep (se 3 (by rfl) ⟨630392, by rfl⟩ : syracuseStep 3362093 = 1260785) B1260785
theorem B1494323 : Blo 992597 1494323 := bstep (se 1 (by rfl) ⟨1120742, by rfl⟩ : syracuseStep 1494323 = 2241485) B2241485
theorem B1494353 : Blo 992597 1494353 := bstep (se 2 (by rfl) ⟨560382, by rfl⟩ : syracuseStep 1494353 = 1120765) B1120765
theorem B1789283 : Blo 992597 1789283 := bstep (se 1 (by rfl) ⟨1341962, by rfl⟩ : syracuseStep 1789283 = 2683925) B2683925
theorem B3362147 : Blo 992597 3362147 := bstep (se 1 (by rfl) ⟨2521610, by rfl⟩ : syracuseStep 3362147 = 5043221) B5043221
theorem B1494371 : Blo 992597 1494371 := bstep (se 1 (by rfl) ⟨1120778, by rfl⟩ : syracuseStep 1494371 = 2241557) B2241557
theorem B1494401 : Blo 992597 1494401 := bstep (se 2 (by rfl) ⟨560400, by rfl⟩ : syracuseStep 1494401 = 1120801) B1120801
theorem B1494419 : Blo 992597 1494419 := bstep (se 1 (by rfl) ⟨1120814, by rfl⟩ : syracuseStep 1494419 = 2241629) B2241629
theorem B1494449 : Blo 992597 1494449 := bstep (se 2 (by rfl) ⟨560418, by rfl⟩ : syracuseStep 1494449 = 1120837) B1120837
theorem B1494467 : Blo 992597 1494467 := bstep (se 1 (by rfl) ⟨1120850, by rfl⟩ : syracuseStep 1494467 = 2241701) B2241701
theorem B1494497 : Blo 992597 1494497 := bstep (se 2 (by rfl) ⟨560436, by rfl⟩ : syracuseStep 1494497 = 1120873) B1120873
theorem B1887715 : Blo 992597 1887715 := bstep (se 1 (by rfl) ⟨1415786, by rfl⟩ : syracuseStep 1887715 = 2831573) B2831573
theorem B1494515 : Blo 992597 1494515 := bstep (se 1 (by rfl) ⟨1120886, by rfl⟩ : syracuseStep 1494515 = 2241773) B2241773
theorem B1887761 : Blo 992597 1887761 := bstep (se 2 (by rfl) ⟨707910, by rfl⟩ : syracuseStep 1887761 = 1415821) B1415821
theorem B1494545 : Blo 992597 1494545 := bstep (se 2 (by rfl) ⟨560454, by rfl⟩ : syracuseStep 1494545 = 1120909) B1120909
theorem B1494563 : Blo 992597 1494563 := bstep (se 1 (by rfl) ⟨1120922, by rfl⟩ : syracuseStep 1494563 = 2241845) B2241845
theorem B1494593 : Blo 992597 1494593 := bstep (se 2 (by rfl) ⟨560472, by rfl⟩ : syracuseStep 1494593 = 1120945) B1120945
theorem B1494611 : Blo 992597 1494611 := bstep (se 1 (by rfl) ⟨1120958, by rfl⟩ : syracuseStep 1494611 = 2241917) B2241917
theorem B3362417 : Blo 992597 3362417 := bstep (se 2 (by rfl) ⟨1260906, by rfl⟩ : syracuseStep 3362417 = 2521813) B2521813
theorem B1494641 : Blo 992597 1494641 := bstep (se 2 (by rfl) ⟨560490, by rfl⟩ : syracuseStep 1494641 = 1120981) B1120981
theorem B1494659 : Blo 992597 1494659 := bstep (se 1 (by rfl) ⟨1120994, by rfl⟩ : syracuseStep 1494659 = 2241989) B2241989
theorem B1494689 : Blo 992597 1494689 := bstep (se 2 (by rfl) ⟨560508, by rfl⟩ : syracuseStep 1494689 = 1121017) B1121017
theorem B1494707 : Blo 992597 1494707 := bstep (se 1 (by rfl) ⟨1121030, by rfl⟩ : syracuseStep 1494707 = 2242061) B2242061
theorem B1494737 : Blo 992597 1494737 := bstep (se 2 (by rfl) ⟨560526, by rfl⟩ : syracuseStep 1494737 = 1121053) B1121053
theorem B1494755 : Blo 992597 1494755 := bstep (se 1 (by rfl) ⟨1121066, by rfl⟩ : syracuseStep 1494755 = 2242133) B2242133
theorem B1724147 : Blo 992597 1724147 := bstep (se 1 (by rfl) ⟨1293110, by rfl⟩ : syracuseStep 1724147 = 2586221) B2586221
theorem B1494785 : Blo 992597 1494785 := bstep (se 2 (by rfl) ⟨560544, by rfl⟩ : syracuseStep 1494785 = 1121089) B1121089
theorem B1494803 : Blo 992597 1494803 := bstep (se 1 (by rfl) ⟨1121102, by rfl⟩ : syracuseStep 1494803 = 2242205) B2242205
theorem B1888049 : Blo 992597 1888049 := bstep (se 2 (by rfl) ⟨708018, by rfl⟩ : syracuseStep 1888049 = 1416037) B1416037
theorem B1494833 : Blo 992597 1494833 := bstep (se 2 (by rfl) ⟨560562, by rfl⟩ : syracuseStep 1494833 = 1121125) B1121125
theorem B1494851 : Blo 992597 1494851 := bstep (se 1 (by rfl) ⟨1121138, by rfl⟩ : syracuseStep 1494851 = 2242277) B2242277
theorem B1494881 : Blo 992597 1494881 := bstep (se 2 (by rfl) ⟨560580, by rfl⟩ : syracuseStep 1494881 = 1121161) B1121161
theorem B1724401 : Blo 992597 1724401 := bstep (se 2 (by rfl) ⟨646650, by rfl⟩ : syracuseStep 1724401 = 1293301) B1293301
theorem B1593427 : Blo 992597 1593427 := bstep (se 1 (by rfl) ⟨1195070, by rfl⟩ : syracuseStep 1593427 = 2390141) B2390141
theorem B5656675 : Blo 992597 5656675 := bstep (se 1 (by rfl) ⟨4242506, by rfl⟩ : syracuseStep 5656675 = 8485013) B8485013
theorem B3362957 : Blo 992597 3362957 := bstep (se 3 (by rfl) ⟨630554, by rfl⟩ : syracuseStep 3362957 = 1261109) B1261109
theorem B3363011 : Blo 992597 3363011 := bstep (se 1 (by rfl) ⟨2522258, by rfl⟩ : syracuseStep 3363011 = 5044517) B5044517
theorem B3395789 : Blo 992597 3395789 := bstep (se 3 (by rfl) ⟨636710, by rfl⟩ : syracuseStep 3395789 = 1273421) B1273421
theorem B2183395 : Blo 992597 2183395 := bstep (se 1 (by rfl) ⟨1637546, by rfl⟩ : syracuseStep 2183395 = 3275093) B3275093
theorem B1593683 : Blo 992597 1593683 := bstep (se 1 (by rfl) ⟨1195262, by rfl⟩ : syracuseStep 1593683 = 2390525) B2390525
theorem B3363281 : Blo 992597 3363281 := bstep (se 2 (by rfl) ⟨1261230, by rfl⟩ : syracuseStep 3363281 = 2522461) B2522461
theorem B1888771 : Blo 992597 1888771 := bstep (se 1 (by rfl) ⟨1416578, by rfl⟩ : syracuseStep 1888771 = 2833157) B2833157
theorem B10768909 : Blo 992597 10768909 := bstep (se 3 (by rfl) ⟨2019170, by rfl⟩ : syracuseStep 10768909 = 4038341) B4038341
theorem B1593875 : Blo 992597 1593875 := bstep (se 1 (by rfl) ⟨1195406, by rfl⟩ : syracuseStep 1593875 = 2390813) B2390813
theorem B10768949 : Blo 992597 10768949 := bstep (se 5 (by rfl) ⟨504794, by rfl⟩ : syracuseStep 10768949 = 1009589) B1009589
theorem B5657201 : Blo 992597 5657201 := bstep (se 2 (by rfl) ⟨2121450, by rfl⟩ : syracuseStep 5657201 = 4242901) B4242901
theorem B1889219 : Blo 992597 1889219 := bstep (se 1 (by rfl) ⟨1416914, by rfl⟩ : syracuseStep 1889219 = 2833829) B2833829
theorem B3232781 : Blo 992597 3232781 := bstep (se 3 (by rfl) ⟨606146, by rfl⟩ : syracuseStep 3232781 = 1212293) B1212293
theorem B5035121 : Blo 992597 5035121 := bstep (se 2 (by rfl) ⟨1888170, by rfl⟩ : syracuseStep 5035121 = 3776341) B3776341
theorem B3232931 : Blo 992597 3232931 := bstep (se 1 (by rfl) ⟨2424698, by rfl⟩ : syracuseStep 3232931 = 4849397) B4849397
theorem B1889507 : Blo 992597 1889507 := bstep (se 1 (by rfl) ⟨1417130, by rfl⟩ : syracuseStep 1889507 = 2834261) B2834261
theorem B1594657 : Blo 992597 1594657 := bstep (se 2 (by rfl) ⟨597996, by rfl⟩ : syracuseStep 1594657 = 1195993) B1195993
theorem B4248931 : Blo 992597 4248931 := bstep (se 1 (by rfl) ⟨3186698, by rfl⟩ : syracuseStep 4248931 = 6373397) B6373397
theorem B2512529 : Blo 992597 2512529 := bstep (se 2 (by rfl) ⟨942198, by rfl⟩ : syracuseStep 2512529 = 1884397) B1884397
theorem B2512579 : Blo 992597 2512579 := bstep (se 1 (by rfl) ⟨1884434, by rfl⟩ : syracuseStep 2512579 = 3768869) B3768869
theorem B4773667 : Blo 992597 4773667 := bstep (se 1 (by rfl) ⟨3580250, by rfl⟩ : syracuseStep 4773667 = 7160501) B7160501
theorem B2512721 : Blo 992597 2512721 := bstep (se 2 (by rfl) ⟨942270, by rfl⟩ : syracuseStep 2512721 = 1884541) B1884541
theorem B6379397 : Blo 992597 6379397 := bstep (se 4 (by rfl) ⟨598068, by rfl⟩ : syracuseStep 6379397 = 1196137) B1196137
theorem B40753037 : Blo 992597 40753037 := bstep (se 3 (by rfl) ⟨7641194, by rfl⟩ : syracuseStep 40753037 = 15282389) B15282389
theorem B1791971 : Blo 992597 1791971 := bstep (se 1 (by rfl) ⟨1343978, by rfl⟩ : syracuseStep 1791971 = 2687957) B2687957
theorem B5658659 : Blo 992597 5658659 := bstep (se 1 (by rfl) ⟨4243994, by rfl⟩ : syracuseStep 5658659 = 8487989) B8487989
theorem B4773937 : Blo 992597 4773937 := bstep (se 2 (by rfl) ⟨1790226, by rfl⟩ : syracuseStep 4773937 = 3580453) B3580453
theorem B1792145 : Blo 992597 1792145 := bstep (se 2 (by rfl) ⟨672054, by rfl⟩ : syracuseStep 1792145 = 1344109) B1344109
theorem B1890449 : Blo 992597 1890449 := bstep (se 2 (by rfl) ⟨708918, by rfl⟩ : syracuseStep 1890449 = 1417837) B1417837
theorem B2120195 : Blo 992597 2120195 := bstep (se 1 (by rfl) ⟨1590146, by rfl⟩ : syracuseStep 2120195 = 3180293) B3180293
theorem B5036579 : Blo 992597 5036579 := bstep (se 1 (by rfl) ⟨3777434, by rfl⟩ : syracuseStep 5036579 = 7554869) B7554869
theorem B4250161 : Blo 992597 4250161 := bstep (se 2 (by rfl) ⟨1593810, by rfl⟩ : syracuseStep 4250161 = 3187621) B3187621
theorem B10902197 : Blo 992597 10902197 := bstep (se 5 (by rfl) ⟨511040, by rfl⟩ : syracuseStep 10902197 = 1022081) B1022081
theorem B2513713 : Blo 992597 2513713 := bstep (se 2 (by rfl) ⟨942642, by rfl⟩ : syracuseStep 2513713 = 1885285) B1885285
theorem B1596323 : Blo 992597 1596323 := bstep (se 1 (by rfl) ⟨1197242, by rfl⟩ : syracuseStep 1596323 = 2394485) B2394485
theorem B1891345 : Blo 992597 1891345 := bstep (se 2 (by rfl) ⟨709254, by rfl⟩ : syracuseStep 1891345 = 1418509) B1418509
theorem B2513987 : Blo 992597 2513987 := bstep (se 1 (by rfl) ⟨1885490, by rfl⟩ : syracuseStep 2513987 = 3770981) B3770981
theorem B1891505 : Blo 992597 1891505 := bstep (se 2 (by rfl) ⟨709314, by rfl⟩ : syracuseStep 1891505 = 1418629) B1418629
theorem B2514179 : Blo 992597 2514179 := bstep (se 1 (by rfl) ⟨1885634, by rfl⟩ : syracuseStep 2514179 = 3771269) B3771269
theorem B5037389 : Blo 992597 5037389 := bstep (se 3 (by rfl) ⟨944510, by rfl⟩ : syracuseStep 5037389 = 1889021) B1889021
theorem B2121041 : Blo 992597 2121041 := bstep (se 2 (by rfl) ⟨795390, by rfl⟩ : syracuseStep 2121041 = 1590781) B1590781
theorem B1891907 : Blo 992597 1891907 := bstep (se 1 (by rfl) ⟨1418930, by rfl⟩ : syracuseStep 1891907 = 2837861) B2837861
theorem B4087523 : Blo 992597 4087523 := bstep (se 1 (by rfl) ⟨3065642, by rfl⟩ : syracuseStep 4087523 = 6131285) B6131285
theorem B5660549 : Blo 992597 5660549 := bstep (se 4 (by rfl) ⟨530676, by rfl⟩ : syracuseStep 5660549 = 1061353) B1061353
theorem B7561187 : Blo 992597 7561187 := bstep (se 1 (by rfl) ⟨5670890, by rfl⟩ : syracuseStep 7561187 = 11341781) B11341781
theorem B12738545 : Blo 992597 12738545 := bstep (se 2 (by rfl) ⟨4776954, by rfl⟩ : syracuseStep 12738545 = 9553909) B9553909
theorem B2515121 : Blo 992597 2515121 := bstep (se 2 (by rfl) ⟨943170, by rfl⟩ : syracuseStep 2515121 = 1886341) B1886341
theorem B1401025 : Blo 992597 1401025 := bstep (se 2 (by rfl) ⟨525384, by rfl⟩ : syracuseStep 1401025 = 1050769) B1050769
theorem B2515171 : Blo 992597 2515171 := bstep (se 1 (by rfl) ⟨1886378, by rfl⟩ : syracuseStep 2515171 = 3772757) B3772757
theorem B2515313 : Blo 992597 2515313 := bstep (se 2 (by rfl) ⟨943242, by rfl⟩ : syracuseStep 2515313 = 1886485) B1886485
theorem B1794595 : Blo 992597 1794595 := bstep (se 1 (by rfl) ⟨1345946, by rfl⟩ : syracuseStep 1794595 = 2691893) B2691893
theorem B11330117 : Blo 992597 11330117 := bstep (se 4 (by rfl) ⟨1062198, by rfl⟩ : syracuseStep 11330117 = 2124397) B2124397
theorem B4776803 : Blo 992597 4776803 := bstep (se 1 (by rfl) ⟨3582602, by rfl⟩ : syracuseStep 4776803 = 7165205) B7165205
theorem B2122723 : Blo 992597 2122723 := bstep (se 1 (by rfl) ⟨1592042, by rfl⟩ : syracuseStep 2122723 = 3184085) B3184085
theorem B7169123 : Blo 992597 7169123 := bstep (se 1 (by rfl) ⟨5376842, by rfl⟩ : syracuseStep 7169123 = 10753685) B10753685
theorem B2516305 : Blo 992597 2516305 := bstep (se 2 (by rfl) ⟨943614, by rfl⟩ : syracuseStep 2516305 = 1887229) B1887229
theorem B2123185 : Blo 992597 2123185 := bstep (se 2 (by rfl) ⟨796194, by rfl⟩ : syracuseStep 2123185 = 1592389) B1592389
theorem B2516579 : Blo 992597 2516579 := bstep (se 1 (by rfl) ⟨1887434, by rfl⟩ : syracuseStep 2516579 = 3774869) B3774869
theorem B4777741 : Blo 992597 4777741 := bstep (se 3 (by rfl) ⟨895826, by rfl⟩ : syracuseStep 4777741 = 1791653) B1791653
theorem B2516771 : Blo 992597 2516771 := bstep (se 1 (by rfl) ⟨1887578, by rfl⟩ : syracuseStep 2516771 = 3775157) B3775157
theorem B21489461 : Blo 992597 21489461 := bstep (se 5 (by rfl) ⟨1007318, by rfl⟩ : syracuseStep 21489461 = 2014637) B2014637
theorem B2549603 : Blo 992597 2549603 := bstep (se 1 (by rfl) ⟨1912202, by rfl⟩ : syracuseStep 2549603 = 3824405) B3824405
theorem B5040305 : Blo 992597 5040305 := bstep (se 2 (by rfl) ⟨1890114, by rfl⟩ : syracuseStep 5040305 = 3780229) B3780229
theorem B3631409 : Blo 992597 3631409 := bstep (se 2 (by rfl) ⟨1361778, by rfl⟩ : syracuseStep 3631409 = 2723557) B2723557
theorem B6384035 : Blo 992597 6384035 := bstep (se 1 (by rfl) ⟨4788026, by rfl⟩ : syracuseStep 6384035 = 9576053) B9576053
theorem B6056369 : Blo 992597 6056369 := bstep (se 2 (by rfl) ⟨2271138, by rfl⟩ : syracuseStep 6056369 = 4542277) B4542277
theorem B2124227 : Blo 992597 2124227 := bstep (se 1 (by rfl) ⟨1593170, by rfl⟩ : syracuseStep 2124227 = 3186341) B3186341
theorem B2517713 : Blo 992597 2517713 := bstep (se 2 (by rfl) ⟨944142, by rfl⟩ : syracuseStep 2517713 = 1888285) B1888285
theorem B10775267 : Blo 992597 10775267 := bstep (se 1 (by rfl) ⟨8081450, by rfl⟩ : syracuseStep 10775267 = 16162901) B16162901
theorem B2517763 : Blo 992597 2517763 := bstep (se 1 (by rfl) ⟨1888322, by rfl⟩ : syracuseStep 2517763 = 3776645) B3776645
theorem B4025123 : Blo 992597 4025123 := bstep (se 1 (by rfl) ⟨3018842, by rfl⟩ : syracuseStep 4025123 = 6037685) B6037685
theorem B4778801 : Blo 992597 4778801 := bstep (se 2 (by rfl) ⟨1792050, by rfl⟩ : syracuseStep 4778801 = 3584101) B3584101
theorem B9563021 : Blo 992597 9563021 := bstep (se 3 (by rfl) ⟨1793066, by rfl⟩ : syracuseStep 9563021 = 3586133) B3586133
theorem B4254605 : Blo 992597 4254605 := bstep (se 3 (by rfl) ⟨797738, by rfl⟩ : syracuseStep 4254605 = 1595477) B1595477
theorem B2517905 : Blo 992597 2517905 := bstep (se 2 (by rfl) ⟨944214, by rfl⟩ : syracuseStep 2517905 = 1888429) B1888429
theorem B4025251 : Blo 992597 4025251 := bstep (se 1 (by rfl) ⟨3018938, by rfl⟩ : syracuseStep 4025251 = 6037877) B6037877
theorem B2124739 : Blo 992597 2124739 := bstep (se 1 (by rfl) ⟨1593554, by rfl⟩ : syracuseStep 2124739 = 3187109) B3187109
theorem B1698769 : Blo 992597 1698769 := bstep (se 2 (by rfl) ⟨637038, by rfl⟩ : syracuseStep 1698769 = 1274077) B1274077
theorem B2583587 : Blo 992597 2583587 := bstep (se 1 (by rfl) ⟨1937690, by rfl⟩ : syracuseStep 2583587 = 3875381) B3875381
theorem B2387171 : Blo 992597 2387171 := bstep (se 1 (by rfl) ⟨1790378, by rfl⟩ : syracuseStep 2387171 = 3580757) B3580757
theorem B1699187 : Blo 992597 1699187 := bstep (se 1 (by rfl) ⟨1274390, by rfl⟩ : syracuseStep 1699187 = 2548781) B2548781
theorem B3403313 : Blo 992597 3403313 := bstep (se 2 (by rfl) ⟨1276242, by rfl⟩ : syracuseStep 3403313 = 2552485) B2552485
theorem B5041763 : Blo 992597 5041763 := bstep (se 1 (by rfl) ⟨3781322, by rfl⟩ : syracuseStep 5041763 = 7562645) B7562645
theorem B2125457 : Blo 992597 2125457 := bstep (se 2 (by rfl) ⟨797046, by rfl⟩ : syracuseStep 2125457 = 1594093) B1594093
theorem B1535761 : Blo 992597 1535761 := bstep (se 2 (by rfl) ⟨575910, by rfl⟩ : syracuseStep 1535761 = 1151821) B1151821
theorem B2518897 : Blo 992597 2518897 := bstep (se 2 (by rfl) ⟨944586, by rfl⟩ : syracuseStep 2518897 = 1889173) B1889173
theorem B4026289 : Blo 992597 4026289 := bstep (se 2 (by rfl) ⟨1509858, by rfl⟩ : syracuseStep 4026289 = 3019717) B3019717
theorem B2388017 : Blo 992597 2388017 := bstep (se 2 (by rfl) ⟨895506, by rfl⟩ : syracuseStep 2388017 = 1791013) B1791013
theorem B7270469 : Blo 992597 7270469 := bstep (se 4 (by rfl) ⟨681606, by rfl⟩ : syracuseStep 7270469 = 1363213) B1363213
theorem B25522289 : Blo 992597 25522289 := bstep (se 2 (by rfl) ⟨9570858, by rfl⟩ : syracuseStep 25522289 = 19141717) B19141717
theorem B2519171 : Blo 992597 2519171 := bstep (se 1 (by rfl) ⟨1889378, by rfl⟩ : syracuseStep 2519171 = 3778757) B3778757
theorem B2519363 : Blo 992597 2519363 := bstep (se 1 (by rfl) ⟨1889522, by rfl⟩ : syracuseStep 2519363 = 3779045) B3779045
theorem B5042573 : Blo 992597 5042573 := bstep (se 3 (by rfl) ⟨945482, by rfl⟩ : syracuseStep 5042573 = 1890965) B1890965
theorem B2126243 : Blo 992597 2126243 := bstep (se 1 (by rfl) ⟨1594682, by rfl⟩ : syracuseStep 2126243 = 3189365) B3189365
theorem B7566533 : Blo 992597 7566533 := bstep (se 4 (by rfl) ⟨709362, by rfl⟩ : syracuseStep 7566533 = 1418725) B1418725
theorem B4781261 : Blo 992597 4781261 := bstep (se 3 (by rfl) ⟨896486, by rfl⟩ : syracuseStep 4781261 = 1792973) B1792973
theorem B2520305 : Blo 992597 2520305 := bstep (se 2 (by rfl) ⟨945114, by rfl⟩ : syracuseStep 2520305 = 1890229) B1890229
theorem B2520355 : Blo 992597 2520355 := bstep (se 1 (by rfl) ⟨1890266, by rfl⟩ : syracuseStep 2520355 = 3780533) B3780533
theorem B2127217 : Blo 992597 2127217 := bstep (se 2 (by rfl) ⟨797706, by rfl⟩ : syracuseStep 2127217 = 1595413) B1595413
theorem B38303117 : Blo 992597 38303117 := bstep (se 3 (by rfl) ⟨7181834, by rfl⟩ : syracuseStep 38303117 = 14363669) B14363669
theorem B2520497 : Blo 992597 2520497 := bstep (se 2 (by rfl) ⟨945186, by rfl⟩ : syracuseStep 2520497 = 1890373) B1890373
theorem B82900421 : Blo 992597 82900421 := bstep (se 4 (by rfl) ⟨7771914, by rfl⟩ : syracuseStep 82900421 = 15543829) B15543829
theorem B5666381 : Blo 992597 5666381 := bstep (se 3 (by rfl) ⟨1062446, by rfl⟩ : syracuseStep 5666381 = 2124893) B2124893
theorem B2684497 : Blo 992597 2684497 := bstep (se 2 (by rfl) ⟨1006686, by rfl⟩ : syracuseStep 2684497 = 2013373) B2013373
theorem B2127473 : Blo 992597 2127473 := bstep (se 2 (by rfl) ⟨797802, by rfl⟩ : syracuseStep 2127473 = 1595605) B1595605
theorem B5371717 : Blo 992597 5371717 := bstep (se 4 (by rfl) ⟨503598, by rfl⟩ : syracuseStep 5371717 = 1007197) B1007197
theorem B1701875 : Blo 992597 1701875 := bstep (se 1 (by rfl) ⟨1276406, by rfl⟩ : syracuseStep 1701875 = 2552813) B2552813
theorem B2685059 : Blo 992597 2685059 := bstep (se 1 (by rfl) ⟨2013794, by rfl⟩ : syracuseStep 2685059 = 4027589) B4027589
theorem B1702067 : Blo 992597 1702067 := bstep (se 1 (by rfl) ⟨1276550, by rfl⟩ : syracuseStep 1702067 = 2553101) B2553101
theorem B11335949 : Blo 992597 11335949 := bstep (se 3 (by rfl) ⟨2125490, by rfl⟩ : syracuseStep 11335949 = 4250981) B4250981
theorem B2521489 : Blo 992597 2521489 := bstep (se 2 (by rfl) ⟨945558, by rfl⟩ : syracuseStep 2521489 = 1891117) B1891117
theorem B2521763 : Blo 992597 2521763 := bstep (se 1 (by rfl) ⟨1891322, by rfl⟩ : syracuseStep 2521763 = 3782645) B3782645
theorem B1702657 : Blo 992597 1702657 := bstep (se 2 (by rfl) ⟨638496, by rfl⟩ : syracuseStep 1702657 = 1276993) B1276993
theorem B2685773 : Blo 992597 2685773 := bstep (se 3 (by rfl) ⟨503582, by rfl⟩ : syracuseStep 2685773 = 1007165) B1007165
theorem B2521955 : Blo 992597 2521955 := bstep (se 1 (by rfl) ⟨1891466, by rfl⟩ : syracuseStep 2521955 = 3782933) B3782933
theorem B2391331 : Blo 992597 2391331 := bstep (se 1 (by rfl) ⟨1793498, by rfl⟩ : syracuseStep 2391331 = 3586997) B3586997
theorem B4095281 : Blo 992597 4095281 := bstep (se 2 (by rfl) ⟨1535730, by rfl⟩ : syracuseStep 4095281 = 3071461) B3071461
theorem B9567557 : Blo 992597 9567557 := bstep (se 4 (by rfl) ⟨896958, by rfl⟩ : syracuseStep 9567557 = 1793917) B1793917
theorem B2391601 : Blo 992597 2391601 := bstep (se 2 (by rfl) ⟨896850, by rfl⟩ : syracuseStep 2391601 = 1793701) B1793701
theorem B2555441 : Blo 992597 2555441 := bstep (se 2 (by rfl) ⟨958290, by rfl⟩ : syracuseStep 2555441 = 1916581) B1916581
theorem B11501297 : Blo 992597 11501297 := bstep (se 2 (by rfl) ⟨4312986, by rfl⟩ : syracuseStep 11501297 = 8625973) B8625973
theorem B5668613 : Blo 992597 5668613 := bstep (se 4 (by rfl) ⟨531432, by rfl⟩ : syracuseStep 5668613 = 1062865) B1062865
theorem B1343459 : Blo 992597 1343459 := bstep (se 1 (by rfl) ⟨1007594, by rfl⟩ : syracuseStep 1343459 = 2015189) B2015189
theorem B2686961 : Blo 992597 2686961 := bstep (se 2 (by rfl) ⟨1007610, by rfl⟩ : syracuseStep 2686961 = 2015221) B2015221
theorem B1868033 : Blo 992597 1868033 := bstep (se 2 (by rfl) ⟨700512, by rfl⟩ : syracuseStep 1868033 = 1401025) B1401025
theorem B2392793 : Blo 992597 2392793 := bstep (se 2 (by rfl) ⟨897297, by rfl⟩ : syracuseStep 2392793 = 1794595) B1794595
theorem B3769523 : Blo 992597 3769523 := bstep (se 1 (by rfl) ⟨2827142, by rfl⟩ : syracuseStep 3769523 = 5654285) B5654285
theorem B3769537 : Blo 992597 3769537 := bstep (se 2 (by rfl) ⟨1413576, by rfl⟩ : syracuseStep 3769537 = 2827153) B2827153
theorem B8062253 : Blo 992597 8062253 := bstep (se 3 (by rfl) ⟨1511672, by rfl⟩ : syracuseStep 8062253 = 3023345) B3023345
theorem B5670323 : Blo 992597 5670323 := bstep (se 1 (by rfl) ⟨4252742, by rfl⟩ : syracuseStep 5670323 = 8505485) B8505485
theorem B6817355 : Blo 992597 6817355 := bstep (se 1 (by rfl) ⟨5113016, by rfl⟩ : syracuseStep 6817355 = 10226033) B10226033
theorem B1509835 : Blo 992597 1509835 := bstep (se 1 (by rfl) ⟨1132376, by rfl⟩ : syracuseStep 1509835 = 2264753) B2264753
theorem B1149431 : Blo 992597 1149431 := bstep (se 1 (by rfl) ⟨862073, by rfl⟩ : syracuseStep 1149431 = 1724147) B1724147
theorem B11340323 : Blo 992597 11340323 := bstep (se 1 (by rfl) ⟨8505242, by rfl⟩ : syracuseStep 11340323 = 17010485) B17010485
theorem B1116715 : Blo 992597 1116715 := bstep (se 1 (by rfl) ⟨837536, by rfl⟩ : syracuseStep 1116715 = 1675073) B1675073
theorem B1116823 : Blo 992597 1116823 := bstep (se 1 (by rfl) ⟨837617, by rfl⟩ : syracuseStep 1116823 = 1675235) B1675235
theorem B4655819 : Blo 992597 4655819 := bstep (se 1 (by rfl) ⟨3491864, by rfl⟩ : syracuseStep 4655819 = 6983729) B6983729
theorem B1510103 : Blo 992597 1510103 := bstep (se 1 (by rfl) ⟨1132577, by rfl⟩ : syracuseStep 1510103 = 2265155) B2265155
theorem B5737177 : Blo 992597 5737177 := bstep (se 2 (by rfl) ⟨2151441, by rfl⟩ : syracuseStep 5737177 = 4302883) B4302883
theorem B2263859 : Blo 992597 2263859 := bstep (se 1 (by rfl) ⟨1697894, by rfl⟩ : syracuseStep 2263859 = 3395789) B3395789
theorem B4787009 : Blo 992597 4787009 := bstep (se 2 (by rfl) ⟨1795128, by rfl⟩ : syracuseStep 4787009 = 3590257) B3590257
theorem B1117003 : Blo 992597 1117003 := bstep (se 1 (by rfl) ⟨837752, by rfl⟩ : syracuseStep 1117003 = 1675505) B1675505
theorem B5671781 : Blo 992597 5671781 := bstep (se 4 (by rfl) ⟨531729, by rfl⟩ : syracuseStep 5671781 = 1063459) B1063459
theorem B1117111 : Blo 992597 1117111 := bstep (se 1 (by rfl) ⟨837833, by rfl⟩ : syracuseStep 1117111 = 1675667) B1675667
theorem B7179299 : Blo 992597 7179299 := bstep (se 1 (by rfl) ⟨5384474, by rfl⟩ : syracuseStep 7179299 = 10768949) B10768949
theorem B3771467 : Blo 992597 3771467 := bstep (se 1 (by rfl) ⟨2828600, by rfl⟩ : syracuseStep 3771467 = 5657201) B5657201
theorem B4787275 : Blo 992597 4787275 := bstep (se 1 (by rfl) ⟨3590456, by rfl⟩ : syracuseStep 4787275 = 7180913) B7180913
theorem B3771481 : Blo 992597 3771481 := bstep (se 2 (by rfl) ⟨1414305, by rfl⟩ : syracuseStep 3771481 = 2828611) B2828611
theorem B8621149 : Blo 992597 8621149 := bstep (se 3 (by rfl) ⟨1616465, by rfl⟩ : syracuseStep 8621149 = 3232931) B3232931
theorem B1117291 : Blo 992597 1117291 := bstep (se 1 (by rfl) ⟨837968, by rfl⟩ : syracuseStep 1117291 = 1675937) B1675937
theorem B1117399 : Blo 992597 1117399 := bstep (se 1 (by rfl) ⟨838049, by rfl⟩ : syracuseStep 1117399 = 1676099) B1676099
theorem B1117579 : Blo 992597 1117579 := bstep (se 1 (by rfl) ⟨838184, by rfl⟩ : syracuseStep 1117579 = 1676369) B1676369
theorem B2493875 : Blo 992597 2493875 := bstep (se 1 (by rfl) ⟨1870406, by rfl⟩ : syracuseStep 2493875 = 3740813) B3740813
theorem B5443033 : Blo 992597 5443033 := bstep (se 2 (by rfl) ⟨2041137, by rfl⟩ : syracuseStep 5443033 = 4082275) B4082275
theorem B1117687 : Blo 992597 1117687 := bstep (se 1 (by rfl) ⟨838265, by rfl⟩ : syracuseStep 1117687 = 1676531) B1676531
theorem B7540289 : Blo 992597 7540289 := bstep (se 2 (by rfl) ⟨2827608, by rfl⟩ : syracuseStep 7540289 = 5655217) B5655217
theorem B14356061 : Blo 992597 14356061 := bstep (se 3 (by rfl) ⟨2691761, by rfl⟩ : syracuseStep 14356061 = 5383523) B5383523
theorem B1117867 : Blo 992597 1117867 := bstep (se 1 (by rfl) ⟨838400, by rfl⟩ : syracuseStep 1117867 = 1676801) B1676801
theorem B1675019 : Blo 992597 1675019 := bstep (se 1 (by rfl) ⟨1256264, by rfl⟩ : syracuseStep 1675019 = 2512529) B2512529
theorem B1117975 : Blo 992597 1117975 := bstep (se 1 (by rfl) ⟨838481, by rfl⟩ : syracuseStep 1117975 = 1676963) B1676963
theorem B18124661 : Blo 992597 18124661 := bstep (se 5 (by rfl) ⟨849593, by rfl⟩ : syracuseStep 18124661 = 1699187) B1699187
theorem B1675147 : Blo 992597 1675147 := bstep (se 1 (by rfl) ⟨1256360, by rfl⟩ : syracuseStep 1675147 = 2512721) B2512721
theorem B3018647 : Blo 992597 3018647 := bstep (se 1 (by rfl) ⟨2263985, by rfl⟩ : syracuseStep 3018647 = 4527971) B4527971
theorem B27168691 : Blo 992597 27168691 := bstep (se 1 (by rfl) ⟨20376518, by rfl⟩ : syracuseStep 27168691 = 40753037) B40753037
theorem B1118155 : Blo 992597 1118155 := bstep (se 1 (by rfl) ⟨838616, by rfl⟩ : syracuseStep 1118155 = 1677233) B1677233
theorem B16125913 : Blo 992597 16125913 := bstep (se 2 (by rfl) ⟨6047217, by rfl⟩ : syracuseStep 16125913 = 12094435) B12094435
theorem B3772439 : Blo 992597 3772439 := bstep (se 1 (by rfl) ⟨2829329, by rfl⟩ : syracuseStep 3772439 = 5658659) B5658659
theorem B1675289 : Blo 992597 1675289 := bstep (se 2 (by rfl) ⟨628233, by rfl⟩ : syracuseStep 1675289 = 1256467) B1256467
theorem B1118263 : Blo 992597 1118263 := bstep (se 1 (by rfl) ⟨838697, by rfl⟩ : syracuseStep 1118263 = 1677395) B1677395
theorem B1675417 : Blo 992597 1675417 := bstep (se 2 (by rfl) ⟨628281, by rfl⟩ : syracuseStep 1675417 = 1256563) B1256563
theorem B1118443 : Blo 992597 1118443 := bstep (se 1 (by rfl) ⟨838832, by rfl⟩ : syracuseStep 1118443 = 1677665) B1677665
theorem B1413463 : Blo 992597 1413463 := bstep (se 1 (by rfl) ⟨1060097, by rfl⟩ : syracuseStep 1413463 = 2120195) B2120195
theorem B1118551 : Blo 992597 1118551 := bstep (se 1 (by rfl) ⟨838913, by rfl⟩ : syracuseStep 1118551 = 1677827) B1677827
theorem B4788659 : Blo 992597 4788659 := bstep (se 1 (by rfl) ⟨3591494, by rfl⟩ : syracuseStep 4788659 = 7182989) B7182989
theorem B1118731 : Blo 992597 1118731 := bstep (se 1 (by rfl) ⟨839048, by rfl⟩ : syracuseStep 1118731 = 1678097) B1678097
theorem B1118839 : Blo 992597 1118839 := bstep (se 1 (by rfl) ⟨839129, by rfl⟩ : syracuseStep 1118839 = 1678259) B1678259
theorem B1675991 : Blo 992597 1675991 := bstep (se 1 (by rfl) ⟨1256993, by rfl⟩ : syracuseStep 1675991 = 2513987) B2513987
theorem B1119019 : Blo 992597 1119019 := bstep (se 1 (by rfl) ⟨839264, by rfl⟩ : syracuseStep 1119019 = 1678529) B1678529
theorem B2724673 : Blo 992597 2724673 := bstep (se 2 (by rfl) ⟨1021752, by rfl⟩ : syracuseStep 2724673 = 2043505) B2043505
theorem B1676119 : Blo 992597 1676119 := bstep (se 1 (by rfl) ⟨1257089, by rfl⟩ : syracuseStep 1676119 = 2514179) B2514179
theorem B1414027 : Blo 992597 1414027 := bstep (se 1 (by rfl) ⟨1060520, by rfl⟩ : syracuseStep 1414027 = 2121041) B2121041
theorem B1119127 : Blo 992597 1119127 := bstep (se 1 (by rfl) ⟨839345, by rfl⟩ : syracuseStep 1119127 = 1678691) B1678691
theorem B2233367 : Blo 992597 2233367 := bstep (se 1 (by rfl) ⟨1675025, by rfl⟩ : syracuseStep 2233367 = 3350051) B3350051
theorem B1119307 : Blo 992597 1119307 := bstep (se 1 (by rfl) ⟨839480, by rfl⟩ : syracuseStep 1119307 = 1678961) B1678961
theorem B2725015 : Blo 992597 2725015 := bstep (se 1 (by rfl) ⟨2043761, by rfl⟩ : syracuseStep 2725015 = 4087523) B4087523
theorem B1119415 : Blo 992597 1119415 := bstep (se 1 (by rfl) ⟨839561, by rfl⟩ : syracuseStep 1119415 = 1679123) B1679123
theorem B2233547 : Blo 992597 2233547 := bstep (se 1 (by rfl) ⟨1675160, by rfl⟩ : syracuseStep 2233547 = 3350321) B3350321
theorem B2233601 : Blo 992597 2233601 := bstep (se 2 (by rfl) ⟨837600, by rfl⟩ : syracuseStep 2233601 = 1675201) B1675201
theorem B3773699 : Blo 992597 3773699 := bstep (se 1 (by rfl) ⟨2830274, by rfl⟩ : syracuseStep 3773699 = 5660549) B5660549
theorem B3020107 : Blo 992597 3020107 := bstep (se 1 (by rfl) ⟨2265080, by rfl⟩ : syracuseStep 3020107 = 4530161) B4530161
theorem B8492363 : Blo 992597 8492363 := bstep (se 1 (by rfl) ⟨6369272, by rfl⟩ : syracuseStep 8492363 = 12738545) B12738545
theorem B1119595 : Blo 992597 1119595 := bstep (se 1 (by rfl) ⟨839696, by rfl⟩ : syracuseStep 1119595 = 1679393) B1679393
theorem B1676747 : Blo 992597 1676747 := bstep (se 1 (by rfl) ⟨1257560, by rfl⟩ : syracuseStep 1676747 = 2515121) B2515121
theorem B1119703 : Blo 992597 1119703 := bstep (se 1 (by rfl) ⟨839777, by rfl⟩ : syracuseStep 1119703 = 1679555) B1679555
theorem B2233817 : Blo 992597 2233817 := bstep (se 2 (by rfl) ⟨837681, by rfl⟩ : syracuseStep 2233817 = 1675363) B1675363
theorem B7542233 : Blo 992597 7542233 := bstep (se 2 (by rfl) ⟨2828337, by rfl⟩ : syracuseStep 7542233 = 5656675) B5656675
theorem B2233907 : Blo 992597 2233907 := bstep (se 1 (by rfl) ⟨1675430, by rfl⟩ : syracuseStep 2233907 = 3350861) B3350861
theorem B1676875 : Blo 992597 1676875 := bstep (se 1 (by rfl) ⟨1257656, by rfl⟩ : syracuseStep 1676875 = 2515313) B2515313
theorem B2233943 : Blo 992597 2233943 := bstep (se 1 (by rfl) ⟨1675457, by rfl⟩ : syracuseStep 2233943 = 3350915) B3350915
theorem B1119883 : Blo 992597 1119883 := bstep (se 1 (by rfl) ⟨839912, by rfl⟩ : syracuseStep 1119883 = 1679825) B1679825
theorem B1677017 : Blo 992597 1677017 := bstep (se 2 (by rfl) ⟨628881, by rfl⟩ : syracuseStep 1677017 = 1257763) B1257763
theorem B1119991 : Blo 992597 1119991 := bstep (se 1 (by rfl) ⟨839993, by rfl⟩ : syracuseStep 1119991 = 1679987) B1679987
theorem B2234123 : Blo 992597 2234123 := bstep (se 1 (by rfl) ⟨1675592, by rfl⟩ : syracuseStep 2234123 = 3351185) B3351185
theorem B2234177 : Blo 992597 2234177 := bstep (se 2 (by rfl) ⟨837816, by rfl⟩ : syracuseStep 2234177 = 1675633) B1675633
theorem B1677145 : Blo 992597 1677145 := bstep (se 2 (by rfl) ⟨628929, by rfl⟩ : syracuseStep 1677145 = 1257859) B1257859
theorem B3184535 : Blo 992597 3184535 := bstep (se 1 (by rfl) ⟨2388401, by rfl⟩ : syracuseStep 3184535 = 4776803) B4776803
theorem B1120171 : Blo 992597 1120171 := bstep (se 1 (by rfl) ⟨840128, by rfl⟩ : syracuseStep 1120171 = 1680257) B1680257
theorem B9574321 : Blo 992597 9574321 := bstep (se 2 (by rfl) ⟨3590370, by rfl⟩ : syracuseStep 9574321 = 7180741) B7180741
theorem B14358545 : Blo 992597 14358545 := bstep (se 2 (by rfl) ⟨5384454, by rfl⟩ : syracuseStep 14358545 = 10768909) B10768909
theorem B1120279 : Blo 992597 1120279 := bstep (se 1 (by rfl) ⟨840209, by rfl⟩ : syracuseStep 1120279 = 1680419) B1680419
theorem B2234393 : Blo 992597 2234393 := bstep (se 2 (by rfl) ⟨837897, by rfl⟩ : syracuseStep 2234393 = 1675795) B1675795
theorem B2234483 : Blo 992597 2234483 := bstep (se 1 (by rfl) ⟨1675862, by rfl⟩ : syracuseStep 2234483 = 3351725) B3351725
theorem B2234519 : Blo 992597 2234519 := bstep (se 1 (by rfl) ⟨1675889, by rfl⟩ : syracuseStep 2234519 = 3351779) B3351779
theorem B1120459 : Blo 992597 1120459 := bstep (se 1 (by rfl) ⟨840344, by rfl⟩ : syracuseStep 1120459 = 1680689) B1680689
theorem B1120567 : Blo 992597 1120567 := bstep (se 1 (by rfl) ⟨840425, by rfl⟩ : syracuseStep 1120567 = 1680851) B1680851
theorem B2234699 : Blo 992597 2234699 := bstep (se 1 (by rfl) ⟨1676024, by rfl⟩ : syracuseStep 2234699 = 3352049) B3352049
theorem B3021131 : Blo 992597 3021131 := bstep (se 1 (by rfl) ⟨2265848, by rfl⟩ : syracuseStep 3021131 = 4531697) B4531697
theorem B1415513 : Blo 992597 1415513 := bstep (se 2 (by rfl) ⟨530817, by rfl⟩ : syracuseStep 1415513 = 1061635) B1061635
theorem B2234753 : Blo 992597 2234753 := bstep (se 2 (by rfl) ⟨838032, by rfl⟩ : syracuseStep 2234753 = 1676065) B1676065
theorem B1677719 : Blo 992597 1677719 := bstep (se 1 (by rfl) ⟨1258289, by rfl⟩ : syracuseStep 1677719 = 2516579) B2516579
theorem B1120747 : Blo 992597 1120747 := bstep (se 1 (by rfl) ⟨840560, by rfl⟩ : syracuseStep 1120747 = 1681121) B1681121
theorem B1677847 : Blo 992597 1677847 := bstep (se 1 (by rfl) ⟨1258385, by rfl⟩ : syracuseStep 1677847 = 2516771) B2516771
theorem B14326307 : Blo 992597 14326307 := bstep (se 1 (by rfl) ⟨10744730, by rfl⟩ : syracuseStep 14326307 = 21489461) B21489461
theorem B1120855 : Blo 992597 1120855 := bstep (se 1 (by rfl) ⟨840641, by rfl⟩ : syracuseStep 1120855 = 1681283) B1681283
theorem B2234969 : Blo 992597 2234969 := bstep (se 2 (by rfl) ⟨838113, by rfl⟩ : syracuseStep 2234969 = 1676227) B1676227
theorem B2235059 : Blo 992597 2235059 := bstep (se 1 (by rfl) ⟨1676294, by rfl⟩ : syracuseStep 2235059 = 3352589) B3352589
theorem B2235095 : Blo 992597 2235095 := bstep (se 1 (by rfl) ⟨1676321, by rfl⟩ : syracuseStep 2235095 = 3352643) B3352643
theorem B1121035 : Blo 992597 1121035 := bstep (se 1 (by rfl) ⟨840776, by rfl⟩ : syracuseStep 1121035 = 1681553) B1681553
theorem B1121143 : Blo 992597 1121143 := bstep (se 1 (by rfl) ⟨840857, by rfl⟩ : syracuseStep 1121143 = 1681715) B1681715
theorem B2235275 : Blo 992597 2235275 := bstep (se 1 (by rfl) ⟨1676456, by rfl⟩ : syracuseStep 2235275 = 3352913) B3352913
theorem B2235329 : Blo 992597 2235329 := bstep (se 2 (by rfl) ⟨838248, by rfl⟩ : syracuseStep 2235329 = 1676497) B1676497
theorem B4037579 : Blo 992597 4037579 := bstep (se 1 (by rfl) ⟨3028184, by rfl⟩ : syracuseStep 4037579 = 6056369) B6056369
theorem B1416151 : Blo 992597 1416151 := bstep (se 1 (by rfl) ⟨1062113, by rfl⟩ : syracuseStep 1416151 = 2124227) B2124227
theorem B1678475 : Blo 992597 1678475 := bstep (se 1 (by rfl) ⟨1258856, by rfl⟩ : syracuseStep 1678475 = 2517713) B2517713
theorem B7183511 : Blo 992597 7183511 := bstep (se 1 (by rfl) ⟨5387633, by rfl⟩ : syracuseStep 7183511 = 10775267) B10775267
theorem B2235545 : Blo 992597 2235545 := bstep (se 2 (by rfl) ⟨838329, by rfl⟩ : syracuseStep 2235545 = 1676659) B1676659
theorem B3185867 : Blo 992597 3185867 := bstep (se 1 (by rfl) ⟨2389400, by rfl⟩ : syracuseStep 3185867 = 4778801) B4778801
theorem B2235635 : Blo 992597 2235635 := bstep (se 1 (by rfl) ⟨1676726, by rfl⟩ : syracuseStep 2235635 = 3353453) B3353453
theorem B1678603 : Blo 992597 1678603 := bstep (se 1 (by rfl) ⟨1258952, by rfl⟩ : syracuseStep 1678603 = 2517905) B2517905
theorem B2235671 : Blo 992597 2235671 := bstep (se 1 (by rfl) ⟨1676753, by rfl⟩ : syracuseStep 2235671 = 3353507) B3353507
theorem B1678745 : Blo 992597 1678745 := bstep (se 2 (by rfl) ⟨629529, by rfl⟩ : syracuseStep 1678745 = 1259059) B1259059
theorem B3579329 : Blo 992597 3579329 := bstep (se 2 (by rfl) ⟨1342248, by rfl⟩ : syracuseStep 3579329 = 2684497) B2684497
theorem B2235851 : Blo 992597 2235851 := bstep (se 1 (by rfl) ⟨1676888, by rfl⟩ : syracuseStep 2235851 = 3353777) B3353777
theorem B2235905 : Blo 992597 2235905 := bstep (se 2 (by rfl) ⟨838464, by rfl⟩ : syracuseStep 2235905 = 1676929) B1676929
theorem B1678873 : Blo 992597 1678873 := bstep (se 2 (by rfl) ⟨629577, by rfl⟩ : syracuseStep 1678873 = 1259155) B1259155
theorem B3350105 : Blo 992597 3350105 := bstep (se 2 (by rfl) ⟨1256289, by rfl⟩ : syracuseStep 3350105 = 2512579) B2512579
theorem B1416857 : Blo 992597 1416857 := bstep (se 2 (by rfl) ⟨531321, by rfl⟩ : syracuseStep 1416857 = 1062643) B1062643
theorem B2268875 : Blo 992597 2268875 := bstep (se 1 (by rfl) ⟨1701656, by rfl⟩ : syracuseStep 2268875 = 3403313) B3403313
theorem B6364889 : Blo 992597 6364889 := bstep (se 2 (by rfl) ⟨2386833, by rfl⟩ : syracuseStep 6364889 = 4773667) B4773667
theorem B2236121 : Blo 992597 2236121 := bstep (se 2 (by rfl) ⟨838545, by rfl⟩ : syracuseStep 2236121 = 1677091) B1677091
theorem B1416971 : Blo 992597 1416971 := bstep (se 1 (by rfl) ⟨1062728, by rfl⟩ : syracuseStep 1416971 = 2125457) B2125457
theorem B2236211 : Blo 992597 2236211 := bstep (se 1 (by rfl) ⟨1677158, by rfl⟩ : syracuseStep 2236211 = 3354317) B3354317
theorem B2236247 : Blo 992597 2236247 := bstep (se 1 (by rfl) ⟨1677185, by rfl⟩ : syracuseStep 2236247 = 3354371) B3354371
theorem B2236427 : Blo 992597 2236427 := bstep (se 1 (by rfl) ⟨1677320, by rfl⟩ : syracuseStep 2236427 = 3354641) B3354641
theorem B6365249 : Blo 992597 6365249 := bstep (se 2 (by rfl) ⟨2386968, by rfl⟩ : syracuseStep 6365249 = 4773937) B4773937
theorem B2236481 : Blo 992597 2236481 := bstep (se 2 (by rfl) ⟨838680, by rfl⟩ : syracuseStep 2236481 = 1677361) B1677361
theorem B17014859 : Blo 992597 17014859 := bstep (se 1 (by rfl) ⟨12761144, by rfl⟩ : syracuseStep 17014859 = 25522289) B25522289
theorem B1679447 : Blo 992597 1679447 := bstep (se 1 (by rfl) ⟨1259585, by rfl⟩ : syracuseStep 1679447 = 2519171) B2519171
theorem B1679575 : Blo 992597 1679575 := bstep (se 1 (by rfl) ⟨1259681, by rfl⟩ : syracuseStep 1679575 = 2519363) B2519363
theorem B3350807 : Blo 992597 3350807 := bstep (se 1 (by rfl) ⟨2513105, by rfl⟩ : syracuseStep 3350807 = 5026211) B5026211
theorem B1417495 : Blo 992597 1417495 := bstep (se 1 (by rfl) ⟨1063121, by rfl⟩ : syracuseStep 1417495 = 2126243) B2126243
theorem B2236697 : Blo 992597 2236697 := bstep (se 2 (by rfl) ⟨838761, by rfl⟩ : syracuseStep 2236697 = 1677523) B1677523
theorem B3776813 : Blo 992597 3776813 := bstep (se 3 (by rfl) ⟨708152, by rfl⟩ : syracuseStep 3776813 = 1416305) B1416305
theorem B2236787 : Blo 992597 2236787 := bstep (se 1 (by rfl) ⟨1677590, by rfl⟩ : syracuseStep 2236787 = 3355181) B3355181
theorem B2236823 : Blo 992597 2236823 := bstep (se 1 (by rfl) ⟨1677617, by rfl⟩ : syracuseStep 2236823 = 3355235) B3355235
theorem B2237003 : Blo 992597 2237003 := bstep (se 1 (by rfl) ⟨1677752, by rfl⟩ : syracuseStep 2237003 = 3355505) B3355505
theorem B6365789 : Blo 992597 6365789 := bstep (se 3 (by rfl) ⟨1193585, by rfl⟩ : syracuseStep 6365789 = 2387171) B2387171
theorem B2237057 : Blo 992597 2237057 := bstep (se 2 (by rfl) ⟨838896, by rfl⟩ : syracuseStep 2237057 = 1677793) B1677793
theorem B2302643 : Blo 992597 2302643 := bstep (se 1 (by rfl) ⟨1726982, by rfl⟩ : syracuseStep 2302643 = 3453965) B3453965
theorem B7545635 : Blo 992597 7545635 := bstep (se 1 (by rfl) ⟨5659226, by rfl⟩ : syracuseStep 7545635 = 11318453) B11318453
theorem B3351347 : Blo 992597 3351347 := bstep (se 1 (by rfl) ⟨2513510, by rfl⟩ : syracuseStep 3351347 = 5027021) B5027021
theorem B3187507 : Blo 992597 3187507 := bstep (se 1 (by rfl) ⟨2390630, by rfl⟩ : syracuseStep 3187507 = 4781261) B4781261
theorem B1680203 : Blo 992597 1680203 := bstep (se 1 (by rfl) ⟨1260152, by rfl⟩ : syracuseStep 1680203 = 2520305) B2520305
theorem B2237273 : Blo 992597 2237273 := bstep (se 2 (by rfl) ⟨838977, by rfl⟩ : syracuseStep 2237273 = 1677955) B1677955
theorem B2237363 : Blo 992597 2237363 := bstep (se 1 (by rfl) ⟨1678022, by rfl⟩ : syracuseStep 2237363 = 3356045) B3356045
theorem B5383091 : Blo 992597 5383091 := bstep (se 1 (by rfl) ⟨4037318, by rfl⟩ : syracuseStep 5383091 = 8074637) B8074637
theorem B25535411 : Blo 992597 25535411 := bstep (se 1 (by rfl) ⟨19151558, by rfl⟩ : syracuseStep 25535411 = 38303117) B38303117
theorem B1680331 : Blo 992597 1680331 := bstep (se 1 (by rfl) ⟨1260248, by rfl⟩ : syracuseStep 1680331 = 2520497) B2520497
theorem B2237399 : Blo 992597 2237399 := bstep (se 1 (by rfl) ⟨1678049, by rfl⟩ : syracuseStep 2237399 = 3356099) B3356099
theorem B2270209 : Blo 992597 2270209 := bstep (se 2 (by rfl) ⟨851328, by rfl⟩ : syracuseStep 2270209 = 1702657) B1702657
theorem B3777587 : Blo 992597 3777587 := bstep (se 1 (by rfl) ⟨2833190, by rfl⟩ : syracuseStep 3777587 = 5666381) B5666381
theorem B3351617 : Blo 992597 3351617 := bstep (se 2 (by rfl) ⟨1256856, by rfl⟩ : syracuseStep 3351617 = 2513713) B2513713
theorem B1418315 : Blo 992597 1418315 := bstep (se 1 (by rfl) ⟨1063736, by rfl⟩ : syracuseStep 1418315 = 2127473) B2127473
theorem B1680473 : Blo 992597 1680473 := bstep (se 2 (by rfl) ⟨630177, by rfl⟩ : syracuseStep 1680473 = 1260355) B1260355
theorem B2237579 : Blo 992597 2237579 := bstep (se 1 (by rfl) ⟨1678184, by rfl⟩ : syracuseStep 2237579 = 3356369) B3356369
theorem B2237633 : Blo 992597 2237633 := bstep (se 2 (by rfl) ⟨839112, by rfl⟩ : syracuseStep 2237633 = 1678225) B1678225
theorem B1680601 : Blo 992597 1680601 := bstep (se 2 (by rfl) ⟨630225, by rfl⟩ : syracuseStep 1680601 = 1260451) B1260451
theorem B992599 : Blo 992597 992599 := bstep (se 1 (by rfl) ⟨744449, by rfl⟩ : syracuseStep 992599 = 1488899) B1488899
theorem B992619 : Blo 992597 992619 := bstep (se 1 (by rfl) ⟨744464, by rfl⟩ : syracuseStep 992619 = 1488929) B1488929
theorem B992631 : Blo 992597 992631 := bstep (se 1 (by rfl) ⟨744473, by rfl⟩ : syracuseStep 992631 = 1488947) B1488947
theorem B992651 : Blo 992597 992651 := bstep (se 1 (by rfl) ⟨744488, by rfl⟩ : syracuseStep 992651 = 1488977) B1488977
theorem B992663 : Blo 992597 992663 := bstep (se 1 (by rfl) ⟨744497, by rfl⟩ : syracuseStep 992663 = 1488995) B1488995
theorem B2237849 : Blo 992597 2237849 := bstep (se 2 (by rfl) ⟨839193, by rfl⟩ : syracuseStep 2237849 = 1678387) B1678387
theorem B992683 : Blo 992597 992683 := bstep (se 1 (by rfl) ⟨744512, by rfl⟩ : syracuseStep 992683 = 1489025) B1489025
theorem B992695 : Blo 992597 992695 := bstep (se 1 (by rfl) ⟨744521, by rfl⟩ : syracuseStep 992695 = 1489043) B1489043
theorem B992715 : Blo 992597 992715 := bstep (se 1 (by rfl) ⟨744536, by rfl⟩ : syracuseStep 992715 = 1489073) B1489073
theorem B2827723 : Blo 992597 2827723 := bstep (se 1 (by rfl) ⟨2120792, by rfl⟩ : syracuseStep 2827723 = 4241585) B4241585
theorem B992727 : Blo 992597 992727 := bstep (se 1 (by rfl) ⟨744545, by rfl⟩ : syracuseStep 992727 = 1489091) B1489091
theorem B992747 : Blo 992597 992747 := bstep (se 1 (by rfl) ⟨744560, by rfl⟩ : syracuseStep 992747 = 1489121) B1489121
theorem B2237939 : Blo 992597 2237939 := bstep (se 1 (by rfl) ⟨1678454, by rfl⟩ : syracuseStep 2237939 = 3356909) B3356909
theorem B992759 : Blo 992597 992759 := bstep (se 1 (by rfl) ⟨744569, by rfl⟩ : syracuseStep 992759 = 1489139) B1489139
theorem B992779 : Blo 992597 992779 := bstep (se 1 (by rfl) ⟨744584, by rfl⟩ : syracuseStep 992779 = 1489169) B1489169
theorem B992791 : Blo 992597 992791 := bstep (se 1 (by rfl) ⟨744593, by rfl⟩ : syracuseStep 992791 = 1489187) B1489187
theorem B2237975 : Blo 992597 2237975 := bstep (se 1 (by rfl) ⟨1678481, by rfl⟩ : syracuseStep 2237975 = 3356963) B3356963
theorem B992811 : Blo 992597 992811 := bstep (se 1 (by rfl) ⟨744608, by rfl⟩ : syracuseStep 992811 = 1489217) B1489217
theorem B992823 : Blo 992597 992823 := bstep (se 1 (by rfl) ⟨744617, by rfl⟩ : syracuseStep 992823 = 1489235) B1489235
theorem B992843 : Blo 992597 992843 := bstep (se 1 (by rfl) ⟨744632, by rfl⟩ : syracuseStep 992843 = 1489265) B1489265
theorem B992855 : Blo 992597 992855 := bstep (se 1 (by rfl) ⟨744641, by rfl⟩ : syracuseStep 992855 = 1489283) B1489283
theorem B3352157 : Blo 992597 3352157 := bstep (se 3 (by rfl) ⟨628529, by rfl⟩ : syracuseStep 3352157 = 1257059) B1257059
theorem B992875 : Blo 992597 992875 := bstep (se 1 (by rfl) ⟨744656, by rfl⟩ : syracuseStep 992875 = 1489313) B1489313
theorem B992887 : Blo 992597 992887 := bstep (se 1 (by rfl) ⟨744665, by rfl⟩ : syracuseStep 992887 = 1489331) B1489331
theorem B992907 : Blo 992597 992907 := bstep (se 1 (by rfl) ⟨744680, by rfl⟩ : syracuseStep 992907 = 1489361) B1489361
theorem B992919 : Blo 992597 992919 := bstep (se 1 (by rfl) ⟨744689, by rfl⟩ : syracuseStep 992919 = 1489379) B1489379
theorem B992939 : Blo 992597 992939 := bstep (se 1 (by rfl) ⟨744704, by rfl⟩ : syracuseStep 992939 = 1489409) B1489409
theorem B992951 : Blo 992597 992951 := bstep (se 1 (by rfl) ⟨744713, by rfl⟩ : syracuseStep 992951 = 1489427) B1489427
theorem B992971 : Blo 992597 992971 := bstep (se 1 (by rfl) ⟨744728, by rfl⟩ : syracuseStep 992971 = 1489457) B1489457
theorem B2238155 : Blo 992597 2238155 := bstep (se 1 (by rfl) ⟨1678616, by rfl⟩ : syracuseStep 2238155 = 3357233) B3357233
theorem B992983 : Blo 992597 992983 := bstep (se 1 (by rfl) ⟨744737, by rfl⟩ : syracuseStep 992983 = 1489475) B1489475
theorem B3188441 : Blo 992597 3188441 := bstep (se 2 (by rfl) ⟨1195665, by rfl⟩ : syracuseStep 3188441 = 2391331) B2391331
theorem B2827997 : Blo 992597 2827997 := bstep (se 3 (by rfl) ⟨530249, by rfl⟩ : syracuseStep 2827997 = 1060499) B1060499
theorem B993003 : Blo 992597 993003 := bstep (se 1 (by rfl) ⟨744752, by rfl⟩ : syracuseStep 993003 = 1489505) B1489505
theorem B993015 : Blo 992597 993015 := bstep (se 1 (by rfl) ⟨744761, by rfl⟩ : syracuseStep 993015 = 1489523) B1489523
theorem B2238209 : Blo 992597 2238209 := bstep (se 2 (by rfl) ⟨839328, by rfl⟩ : syracuseStep 2238209 = 1678657) B1678657
theorem B993035 : Blo 992597 993035 := bstep (se 1 (by rfl) ⟨744776, by rfl⟩ : syracuseStep 993035 = 1489553) B1489553
theorem B993047 : Blo 992597 993047 := bstep (se 1 (by rfl) ⟨744785, by rfl⟩ : syracuseStep 993047 = 1489571) B1489571
theorem B1681175 : Blo 992597 1681175 := bstep (se 1 (by rfl) ⟨1260881, by rfl⟩ : syracuseStep 1681175 = 2521763) B2521763
theorem B993067 : Blo 992597 993067 := bstep (se 1 (by rfl) ⟨744800, by rfl⟩ : syracuseStep 993067 = 1489601) B1489601
theorem B993079 : Blo 992597 993079 := bstep (se 1 (by rfl) ⟨744809, by rfl⟩ : syracuseStep 993079 = 1489619) B1489619
theorem B993099 : Blo 992597 993099 := bstep (se 1 (by rfl) ⟨744824, by rfl⟩ : syracuseStep 993099 = 1489649) B1489649
theorem B993111 : Blo 992597 993111 := bstep (se 1 (by rfl) ⟨744833, by rfl⟩ : syracuseStep 993111 = 1489667) B1489667
theorem B993131 : Blo 992597 993131 := bstep (se 1 (by rfl) ⟨744848, by rfl⟩ : syracuseStep 993131 = 1489697) B1489697
theorem B993143 : Blo 992597 993143 := bstep (se 1 (by rfl) ⟨744857, by rfl⟩ : syracuseStep 993143 = 1489715) B1489715
theorem B993163 : Blo 992597 993163 := bstep (se 1 (by rfl) ⟨744872, by rfl⟩ : syracuseStep 993163 = 1489745) B1489745
theorem B993175 : Blo 992597 993175 := bstep (se 1 (by rfl) ⟨744881, by rfl⟩ : syracuseStep 993175 = 1489763) B1489763
theorem B1681303 : Blo 992597 1681303 := bstep (se 1 (by rfl) ⟨1260977, by rfl⟩ : syracuseStep 1681303 = 2521955) B2521955
theorem B993195 : Blo 992597 993195 := bstep (se 1 (by rfl) ⟨744896, by rfl⟩ : syracuseStep 993195 = 1489793) B1489793
theorem B993207 : Blo 992597 993207 := bstep (se 1 (by rfl) ⟨744905, by rfl⟩ : syracuseStep 993207 = 1489811) B1489811
theorem B993227 : Blo 992597 993227 := bstep (se 1 (by rfl) ⟨744920, by rfl⟩ : syracuseStep 993227 = 1489841) B1489841
theorem B993239 : Blo 992597 993239 := bstep (se 1 (by rfl) ⟨744929, by rfl⟩ : syracuseStep 993239 = 1489859) B1489859
theorem B2238425 : Blo 992597 2238425 := bstep (se 2 (by rfl) ⟨839409, by rfl⟩ : syracuseStep 2238425 = 1678819) B1678819
theorem B993259 : Blo 992597 993259 := bstep (se 1 (by rfl) ⟨744944, by rfl⟩ : syracuseStep 993259 = 1489889) B1489889
theorem B993271 : Blo 992597 993271 := bstep (se 1 (by rfl) ⟨744953, by rfl⟩ : syracuseStep 993271 = 1489907) B1489907
theorem B993291 : Blo 992597 993291 := bstep (se 1 (by rfl) ⟨744968, by rfl⟩ : syracuseStep 993291 = 1489937) B1489937
theorem B993303 : Blo 992597 993303 := bstep (se 1 (by rfl) ⟨744977, by rfl⟩ : syracuseStep 993303 = 1489955) B1489955
theorem B993323 : Blo 992597 993323 := bstep (se 1 (by rfl) ⟨744992, by rfl⟩ : syracuseStep 993323 = 1489985) B1489985
theorem B2238515 : Blo 992597 2238515 := bstep (se 1 (by rfl) ⟨1678886, by rfl⟩ : syracuseStep 2238515 = 3357773) B3357773
theorem B993335 : Blo 992597 993335 := bstep (se 1 (by rfl) ⟨745001, by rfl⟩ : syracuseStep 993335 = 1490003) B1490003
theorem B3188801 : Blo 992597 3188801 := bstep (se 2 (by rfl) ⟨1195800, by rfl⟩ : syracuseStep 3188801 = 2391601) B2391601
theorem B993355 : Blo 992597 993355 := bstep (se 1 (by rfl) ⟨745016, by rfl⟩ : syracuseStep 993355 = 1490033) B1490033
theorem B993367 : Blo 992597 993367 := bstep (se 1 (by rfl) ⟨745025, by rfl⟩ : syracuseStep 993367 = 1490051) B1490051
theorem B2238551 : Blo 992597 2238551 := bstep (se 1 (by rfl) ⟨1678913, by rfl⟩ : syracuseStep 2238551 = 3357827) B3357827
theorem B993387 : Blo 992597 993387 := bstep (se 1 (by rfl) ⟨745040, by rfl⟩ : syracuseStep 993387 = 1490081) B1490081
theorem B993399 : Blo 992597 993399 := bstep (se 1 (by rfl) ⟨745049, by rfl⟩ : syracuseStep 993399 = 1490099) B1490099
theorem B993419 : Blo 992597 993419 := bstep (se 1 (by rfl) ⟨745064, by rfl⟩ : syracuseStep 993419 = 1490129) B1490129
theorem B993431 : Blo 992597 993431 := bstep (se 1 (by rfl) ⟨745073, by rfl⟩ : syracuseStep 993431 = 1490147) B1490147
theorem B993451 : Blo 992597 993451 := bstep (se 1 (by rfl) ⟨745088, by rfl⟩ : syracuseStep 993451 = 1490177) B1490177
theorem B993463 : Blo 992597 993463 := bstep (se 1 (by rfl) ⟨745097, by rfl⟩ : syracuseStep 993463 = 1490195) B1490195
theorem B993483 : Blo 992597 993483 := bstep (se 1 (by rfl) ⟨745112, by rfl⟩ : syracuseStep 993483 = 1490225) B1490225
theorem B2730187 : Blo 992597 2730187 := bstep (se 1 (by rfl) ⟨2047640, by rfl⟩ : syracuseStep 2730187 = 4095281) B4095281
theorem B993495 : Blo 992597 993495 := bstep (se 1 (by rfl) ⟨745121, by rfl⟩ : syracuseStep 993495 = 1490243) B1490243
theorem B993515 : Blo 992597 993515 := bstep (se 1 (by rfl) ⟨745136, by rfl⟩ : syracuseStep 993515 = 1490273) B1490273
theorem B993527 : Blo 992597 993527 := bstep (se 1 (by rfl) ⟨745145, by rfl⟩ : syracuseStep 993527 = 1490291) B1490291
theorem B993547 : Blo 992597 993547 := bstep (se 1 (by rfl) ⟨745160, by rfl⟩ : syracuseStep 993547 = 1490321) B1490321
theorem B2238731 : Blo 992597 2238731 := bstep (se 1 (by rfl) ⟨1679048, by rfl⟩ : syracuseStep 2238731 = 3358097) B3358097
theorem B993559 : Blo 992597 993559 := bstep (se 1 (by rfl) ⟨745169, by rfl⟩ : syracuseStep 993559 = 1490339) B1490339
theorem B993579 : Blo 992597 993579 := bstep (se 1 (by rfl) ⟨745184, by rfl⟩ : syracuseStep 993579 = 1490369) B1490369
theorem B993591 : Blo 992597 993591 := bstep (se 1 (by rfl) ⟨745193, by rfl⟩ : syracuseStep 993591 = 1490387) B1490387
theorem B2238785 : Blo 992597 2238785 := bstep (se 2 (by rfl) ⟨839544, by rfl⟩ : syracuseStep 2238785 = 1679089) B1679089
theorem B993611 : Blo 992597 993611 := bstep (se 1 (by rfl) ⟨745208, by rfl⟩ : syracuseStep 993611 = 1490417) B1490417
theorem B993623 : Blo 992597 993623 := bstep (se 1 (by rfl) ⟨745217, by rfl⟩ : syracuseStep 993623 = 1490435) B1490435
theorem B993643 : Blo 992597 993643 := bstep (se 1 (by rfl) ⟨745232, by rfl⟩ : syracuseStep 993643 = 1490465) B1490465
theorem B993655 : Blo 992597 993655 := bstep (se 1 (by rfl) ⟨745241, by rfl⟩ : syracuseStep 993655 = 1490483) B1490483
theorem B993675 : Blo 992597 993675 := bstep (se 1 (by rfl) ⟨745256, by rfl⟩ : syracuseStep 993675 = 1490513) B1490513
theorem B993687 : Blo 992597 993687 := bstep (se 1 (by rfl) ⟨745265, by rfl⟩ : syracuseStep 993687 = 1490531) B1490531
theorem B993707 : Blo 992597 993707 := bstep (se 1 (by rfl) ⟨745280, by rfl⟩ : syracuseStep 993707 = 1490561) B1490561
theorem B993719 : Blo 992597 993719 := bstep (se 1 (by rfl) ⟨745289, by rfl⟩ : syracuseStep 993719 = 1490579) B1490579
theorem B993739 : Blo 992597 993739 := bstep (se 1 (by rfl) ⟨745304, by rfl⟩ : syracuseStep 993739 = 1490609) B1490609
theorem B993751 : Blo 992597 993751 := bstep (se 1 (by rfl) ⟨745313, by rfl⟩ : syracuseStep 993751 = 1490627) B1490627
theorem B993771 : Blo 992597 993771 := bstep (se 1 (by rfl) ⟨745328, by rfl⟩ : syracuseStep 993771 = 1490657) B1490657
theorem B993783 : Blo 992597 993783 := bstep (se 1 (by rfl) ⟨745337, by rfl⟩ : syracuseStep 993783 = 1490675) B1490675
theorem B3779075 : Blo 992597 3779075 := bstep (se 1 (by rfl) ⟨2834306, by rfl⟩ : syracuseStep 3779075 = 5668613) B5668613
theorem B993803 : Blo 992597 993803 := bstep (se 1 (by rfl) ⟨745352, by rfl⟩ : syracuseStep 993803 = 1490705) B1490705
theorem B993815 : Blo 992597 993815 := bstep (se 1 (by rfl) ⟨745361, by rfl⟩ : syracuseStep 993815 = 1490723) B1490723
theorem B2239001 : Blo 992597 2239001 := bstep (se 2 (by rfl) ⟨839625, by rfl⟩ : syracuseStep 2239001 = 1679251) B1679251
theorem B993835 : Blo 992597 993835 := bstep (se 1 (by rfl) ⟨745376, by rfl⟩ : syracuseStep 993835 = 1490753) B1490753
theorem B993847 : Blo 992597 993847 := bstep (se 1 (by rfl) ⟨745385, by rfl⟩ : syracuseStep 993847 = 1490771) B1490771
theorem B993867 : Blo 992597 993867 := bstep (se 1 (by rfl) ⟨745400, by rfl⟩ : syracuseStep 993867 = 1490801) B1490801
theorem B993879 : Blo 992597 993879 := bstep (se 1 (by rfl) ⟨745409, by rfl⟩ : syracuseStep 993879 = 1490819) B1490819
theorem B3582557 : Blo 992597 3582557 := bstep (se 3 (by rfl) ⟨671729, by rfl⟩ : syracuseStep 3582557 = 1343459) B1343459
theorem B993899 : Blo 992597 993899 := bstep (se 1 (by rfl) ⟨745424, by rfl⟩ : syracuseStep 993899 = 1490849) B1490849
theorem B2239091 : Blo 992597 2239091 := bstep (se 1 (by rfl) ⟨1679318, by rfl⟩ : syracuseStep 2239091 = 3358637) B3358637
theorem B993911 : Blo 992597 993911 := bstep (se 1 (by rfl) ⟨745433, by rfl⟩ : syracuseStep 993911 = 1490867) B1490867
theorem B4532867 : Blo 992597 4532867 := bstep (se 1 (by rfl) ⟨3399650, by rfl⟩ : syracuseStep 4532867 = 6799301) B6799301
theorem B993931 : Blo 992597 993931 := bstep (se 1 (by rfl) ⟨745448, by rfl⟩ : syracuseStep 993931 = 1490897) B1490897
theorem B993943 : Blo 992597 993943 := bstep (se 1 (by rfl) ⟨745457, by rfl⟩ : syracuseStep 993943 = 1490915) B1490915
theorem B2239127 : Blo 992597 2239127 := bstep (se 1 (by rfl) ⟨1679345, by rfl⟩ : syracuseStep 2239127 = 3358691) B3358691
theorem B993963 : Blo 992597 993963 := bstep (se 1 (by rfl) ⟨745472, by rfl⟩ : syracuseStep 993963 = 1490945) B1490945
theorem B993975 : Blo 992597 993975 := bstep (se 1 (by rfl) ⟨745481, by rfl⟩ : syracuseStep 993975 = 1490963) B1490963
theorem B3353291 : Blo 992597 3353291 := bstep (se 1 (by rfl) ⟨2514968, by rfl⟩ : syracuseStep 3353291 = 5029937) B5029937
theorem B993995 : Blo 992597 993995 := bstep (se 1 (by rfl) ⟨745496, by rfl⟩ : syracuseStep 993995 = 1490993) B1490993
theorem B994007 : Blo 992597 994007 := bstep (se 1 (by rfl) ⟨745505, by rfl⟩ : syracuseStep 994007 = 1491011) B1491011
theorem B994027 : Blo 992597 994027 := bstep (se 1 (by rfl) ⟨745520, by rfl⟩ : syracuseStep 994027 = 1491041) B1491041
theorem B994039 : Blo 992597 994039 := bstep (se 1 (by rfl) ⟨745529, by rfl⟩ : syracuseStep 994039 = 1491059) B1491059
theorem B994059 : Blo 992597 994059 := bstep (se 1 (by rfl) ⟨745544, by rfl⟩ : syracuseStep 994059 = 1491089) B1491089
theorem B994071 : Blo 992597 994071 := bstep (se 1 (by rfl) ⟨745553, by rfl⟩ : syracuseStep 994071 = 1491107) B1491107
theorem B994091 : Blo 992597 994091 := bstep (se 1 (by rfl) ⟨745568, by rfl⟩ : syracuseStep 994091 = 1491137) B1491137
theorem B994103 : Blo 992597 994103 := bstep (se 1 (by rfl) ⟨745577, by rfl⟩ : syracuseStep 994103 = 1491155) B1491155
theorem B994123 : Blo 992597 994123 := bstep (se 1 (by rfl) ⟨745592, by rfl⟩ : syracuseStep 994123 = 1491185) B1491185
theorem B2239307 : Blo 992597 2239307 := bstep (se 1 (by rfl) ⟨1679480, by rfl⟩ : syracuseStep 2239307 = 3358961) B3358961
theorem B994135 : Blo 992597 994135 := bstep (se 1 (by rfl) ⟨745601, by rfl⟩ : syracuseStep 994135 = 1491203) B1491203
theorem B994155 : Blo 992597 994155 := bstep (se 1 (by rfl) ⟨745616, by rfl⟩ : syracuseStep 994155 = 1491233) B1491233
theorem B994167 : Blo 992597 994167 := bstep (se 1 (by rfl) ⟨745625, by rfl⟩ : syracuseStep 994167 = 1491251) B1491251
theorem B2239361 : Blo 992597 2239361 := bstep (se 2 (by rfl) ⟨839760, by rfl⟩ : syracuseStep 2239361 = 1679521) B1679521
theorem B994187 : Blo 992597 994187 := bstep (se 1 (by rfl) ⟨745640, by rfl⟩ : syracuseStep 994187 = 1491281) B1491281
theorem B994199 : Blo 992597 994199 := bstep (se 1 (by rfl) ⟨745649, by rfl⟩ : syracuseStep 994199 = 1491299) B1491299
theorem B994219 : Blo 992597 994219 := bstep (se 1 (by rfl) ⟨745664, by rfl⟩ : syracuseStep 994219 = 1491329) B1491329
theorem B994231 : Blo 992597 994231 := bstep (se 1 (by rfl) ⟨745673, by rfl⟩ : syracuseStep 994231 = 1491347) B1491347
theorem B994251 : Blo 992597 994251 := bstep (se 1 (by rfl) ⟨745688, by rfl⟩ : syracuseStep 994251 = 1491377) B1491377
theorem B3779531 : Blo 992597 3779531 := bstep (se 1 (by rfl) ⟨2834648, by rfl⟩ : syracuseStep 3779531 = 5669297) B5669297
theorem B994263 : Blo 992597 994263 := bstep (se 1 (by rfl) ⟨745697, by rfl⟩ : syracuseStep 994263 = 1491395) B1491395
theorem B3353561 : Blo 992597 3353561 := bstep (se 2 (by rfl) ⟨1257585, by rfl⟩ : syracuseStep 3353561 = 2515171) B2515171
theorem B994283 : Blo 992597 994283 := bstep (se 1 (by rfl) ⟨745712, by rfl⟩ : syracuseStep 994283 = 1491425) B1491425
theorem B994295 : Blo 992597 994295 := bstep (se 1 (by rfl) ⟨745721, by rfl⟩ : syracuseStep 994295 = 1491443) B1491443
theorem B994315 : Blo 992597 994315 := bstep (se 1 (by rfl) ⟨745736, by rfl⟩ : syracuseStep 994315 = 1491473) B1491473
theorem B994327 : Blo 992597 994327 := bstep (se 1 (by rfl) ⟨745745, by rfl⟩ : syracuseStep 994327 = 1491491) B1491491
theorem B994347 : Blo 992597 994347 := bstep (se 1 (by rfl) ⟨745760, by rfl⟩ : syracuseStep 994347 = 1491521) B1491521
theorem B994359 : Blo 992597 994359 := bstep (se 1 (by rfl) ⟨745769, by rfl⟩ : syracuseStep 994359 = 1491539) B1491539
theorem B994379 : Blo 992597 994379 := bstep (se 1 (by rfl) ⟨745784, by rfl⟩ : syracuseStep 994379 = 1491569) B1491569
theorem B994391 : Blo 992597 994391 := bstep (se 1 (by rfl) ⟨745793, by rfl⟩ : syracuseStep 994391 = 1491587) B1491587
theorem B2239577 : Blo 992597 2239577 := bstep (se 2 (by rfl) ⟨839841, by rfl⟩ : syracuseStep 2239577 = 1679683) B1679683
theorem B994411 : Blo 992597 994411 := bstep (se 1 (by rfl) ⟨745808, by rfl⟩ : syracuseStep 994411 = 1491617) B1491617
theorem B994423 : Blo 992597 994423 := bstep (se 1 (by rfl) ⟨745817, by rfl⟩ : syracuseStep 994423 = 1491635) B1491635
theorem B994443 : Blo 992597 994443 := bstep (se 1 (by rfl) ⟨745832, by rfl⟩ : syracuseStep 994443 = 1491665) B1491665
theorem B3779729 : Blo 992597 3779729 := bstep (se 2 (by rfl) ⟨1417398, by rfl⟩ : syracuseStep 3779729 = 2834797) B2834797
theorem B994455 : Blo 992597 994455 := bstep (se 1 (by rfl) ⟨745841, by rfl⟩ : syracuseStep 994455 = 1491683) B1491683
theorem B18656407 : Blo 992597 18656407 := bstep (se 1 (by rfl) ⟨13992305, by rfl⟩ : syracuseStep 18656407 = 27984611) B27984611
theorem B994475 : Blo 992597 994475 := bstep (se 1 (by rfl) ⟨745856, by rfl⟩ : syracuseStep 994475 = 1491713) B1491713
theorem B4598963 : Blo 992597 4598963 := bstep (se 1 (by rfl) ⟨3449222, by rfl⟩ : syracuseStep 4598963 = 6898445) B6898445
theorem B2239667 : Blo 992597 2239667 := bstep (se 1 (by rfl) ⟨1679750, by rfl⟩ : syracuseStep 2239667 = 3359501) B3359501
theorem B994487 : Blo 992597 994487 := bstep (se 1 (by rfl) ⟨745865, by rfl⟩ : syracuseStep 994487 = 1491731) B1491731
theorem B994507 : Blo 992597 994507 := bstep (se 1 (by rfl) ⟨745880, by rfl⟩ : syracuseStep 994507 = 1491761) B1491761
theorem B994519 : Blo 992597 994519 := bstep (se 1 (by rfl) ⟨745889, by rfl⟩ : syracuseStep 994519 = 1491779) B1491779
theorem B2239703 : Blo 992597 2239703 := bstep (se 1 (by rfl) ⟨1679777, by rfl⟩ : syracuseStep 2239703 = 3359555) B3359555
theorem B994539 : Blo 992597 994539 := bstep (se 1 (by rfl) ⟨745904, by rfl⟩ : syracuseStep 994539 = 1491809) B1491809
theorem B994551 : Blo 992597 994551 := bstep (se 1 (by rfl) ⟨745913, by rfl⟩ : syracuseStep 994551 = 1491827) B1491827
theorem B994571 : Blo 992597 994571 := bstep (se 1 (by rfl) ⟨745928, by rfl⟩ : syracuseStep 994571 = 1491857) B1491857
theorem B994583 : Blo 992597 994583 := bstep (se 1 (by rfl) ⟨745937, by rfl⟩ : syracuseStep 994583 = 1491875) B1491875
theorem B994603 : Blo 992597 994603 := bstep (se 1 (by rfl) ⟨745952, by rfl⟩ : syracuseStep 994603 = 1491905) B1491905
theorem B994615 : Blo 992597 994615 := bstep (se 1 (by rfl) ⟨745961, by rfl⟩ : syracuseStep 994615 = 1491923) B1491923
theorem B994635 : Blo 992597 994635 := bstep (se 1 (by rfl) ⟨745976, by rfl⟩ : syracuseStep 994635 = 1491953) B1491953
theorem B1256791 : Blo 992597 1256791 := bstep (se 1 (by rfl) ⟨942593, by rfl⟩ : syracuseStep 1256791 = 1885187) B1885187
theorem B994647 : Blo 992597 994647 := bstep (se 1 (by rfl) ⟨745985, by rfl⟩ : syracuseStep 994647 = 1491971) B1491971
theorem B994667 : Blo 992597 994667 := bstep (se 1 (by rfl) ⟨746000, by rfl⟩ : syracuseStep 994667 = 1492001) B1492001
theorem B994679 : Blo 992597 994679 := bstep (se 1 (by rfl) ⟨746009, by rfl⟩ : syracuseStep 994679 = 1492019) B1492019
theorem B994699 : Blo 992597 994699 := bstep (se 1 (by rfl) ⟨746024, by rfl⟩ : syracuseStep 994699 = 1492049) B1492049
theorem B2239883 : Blo 992597 2239883 := bstep (se 1 (by rfl) ⟨1679912, by rfl⟩ : syracuseStep 2239883 = 3359825) B3359825
theorem B1060247 : Blo 992597 1060247 := bstep (se 1 (by rfl) ⟨795185, by rfl⟩ : syracuseStep 1060247 = 1590371) B1590371
theorem B994711 : Blo 992597 994711 := bstep (se 1 (by rfl) ⟨746033, by rfl⟩ : syracuseStep 994711 = 1492067) B1492067
theorem B994731 : Blo 992597 994731 := bstep (se 1 (by rfl) ⟨746048, by rfl⟩ : syracuseStep 994731 = 1492097) B1492097
theorem B994743 : Blo 992597 994743 := bstep (se 1 (by rfl) ⟨746057, by rfl⟩ : syracuseStep 994743 = 1492115) B1492115
theorem B2239937 : Blo 992597 2239937 := bstep (se 2 (by rfl) ⟨839976, by rfl⟩ : syracuseStep 2239937 = 1679953) B1679953
theorem B994763 : Blo 992597 994763 := bstep (se 1 (by rfl) ⟨746072, by rfl⟩ : syracuseStep 994763 = 1492145) B1492145
theorem B994775 : Blo 992597 994775 := bstep (se 1 (by rfl) ⟨746081, by rfl⟩ : syracuseStep 994775 = 1492163) B1492163
theorem B994795 : Blo 992597 994795 := bstep (se 1 (by rfl) ⟨746096, by rfl⟩ : syracuseStep 994795 = 1492193) B1492193
theorem B994807 : Blo 992597 994807 := bstep (se 1 (by rfl) ⟨746105, by rfl⟩ : syracuseStep 994807 = 1492211) B1492211
theorem B994827 : Blo 992597 994827 := bstep (se 1 (by rfl) ⟨746120, by rfl⟩ : syracuseStep 994827 = 1492241) B1492241
theorem B994839 : Blo 992597 994839 := bstep (se 1 (by rfl) ⟨746129, by rfl⟩ : syracuseStep 994839 = 1492259) B1492259
theorem B994859 : Blo 992597 994859 := bstep (se 1 (by rfl) ⟨746144, by rfl⟩ : syracuseStep 994859 = 1492289) B1492289
theorem B994871 : Blo 992597 994871 := bstep (se 1 (by rfl) ⟨746153, by rfl⟩ : syracuseStep 994871 = 1492307) B1492307
theorem B994891 : Blo 992597 994891 := bstep (se 1 (by rfl) ⟨746168, by rfl⟩ : syracuseStep 994891 = 1492337) B1492337
theorem B994903 : Blo 992597 994903 := bstep (se 1 (by rfl) ⟨746177, by rfl⟩ : syracuseStep 994903 = 1492355) B1492355
theorem B994923 : Blo 992597 994923 := bstep (se 1 (by rfl) ⟨746192, by rfl⟩ : syracuseStep 994923 = 1492385) B1492385
theorem B994935 : Blo 992597 994935 := bstep (se 1 (by rfl) ⟨746201, by rfl⟩ : syracuseStep 994935 = 1492403) B1492403
theorem B994955 : Blo 992597 994955 := bstep (se 1 (by rfl) ⟨746216, by rfl⟩ : syracuseStep 994955 = 1492433) B1492433
theorem B3354263 : Blo 992597 3354263 := bstep (se 1 (by rfl) ⟨2515697, by rfl⟩ : syracuseStep 3354263 = 5031395) B5031395
theorem B3583639 : Blo 992597 3583639 := bstep (se 1 (by rfl) ⟨2687729, by rfl⟩ : syracuseStep 3583639 = 5375459) B5375459
theorem B994967 : Blo 992597 994967 := bstep (se 1 (by rfl) ⟨746225, by rfl⟩ : syracuseStep 994967 = 1492451) B1492451
theorem B2240153 : Blo 992597 2240153 := bstep (se 2 (by rfl) ⟨840057, by rfl⟩ : syracuseStep 2240153 = 1680115) B1680115
theorem B994987 : Blo 992597 994987 := bstep (se 1 (by rfl) ⟨746240, by rfl⟩ : syracuseStep 994987 = 1492481) B1492481
theorem B994999 : Blo 992597 994999 := bstep (se 1 (by rfl) ⟨746249, by rfl⟩ : syracuseStep 994999 = 1492499) B1492499
theorem B995019 : Blo 992597 995019 := bstep (se 1 (by rfl) ⟨746264, by rfl⟩ : syracuseStep 995019 = 1492529) B1492529
theorem B995031 : Blo 992597 995031 := bstep (se 1 (by rfl) ⟨746273, by rfl⟩ : syracuseStep 995031 = 1492547) B1492547
theorem B3452633 : Blo 992597 3452633 := bstep (se 2 (by rfl) ⟨1294737, by rfl⟩ : syracuseStep 3452633 = 2589475) B2589475
theorem B995051 : Blo 992597 995051 := bstep (se 1 (by rfl) ⟨746288, by rfl⟩ : syracuseStep 995051 = 1492577) B1492577
theorem B2240243 : Blo 992597 2240243 := bstep (se 1 (by rfl) ⟨1680182, by rfl⟩ : syracuseStep 2240243 = 3360365) B3360365
theorem B995063 : Blo 992597 995063 := bstep (se 1 (by rfl) ⟨746297, by rfl⟩ : syracuseStep 995063 = 1492595) B1492595
theorem B995083 : Blo 992597 995083 := bstep (se 1 (by rfl) ⟨746312, by rfl⟩ : syracuseStep 995083 = 1492625) B1492625
theorem B995095 : Blo 992597 995095 := bstep (se 1 (by rfl) ⟨746321, by rfl⟩ : syracuseStep 995095 = 1492643) B1492643
theorem B2240279 : Blo 992597 2240279 := bstep (se 1 (by rfl) ⟨1680209, by rfl⟩ : syracuseStep 2240279 = 3360419) B3360419
theorem B995115 : Blo 992597 995115 := bstep (se 1 (by rfl) ⟨746336, by rfl⟩ : syracuseStep 995115 = 1492673) B1492673
theorem B995127 : Blo 992597 995127 := bstep (se 1 (by rfl) ⟨746345, by rfl⟩ : syracuseStep 995127 = 1492691) B1492691
theorem B995147 : Blo 992597 995147 := bstep (se 1 (by rfl) ⟨746360, by rfl⟩ : syracuseStep 995147 = 1492721) B1492721
theorem B995159 : Blo 992597 995159 := bstep (se 1 (by rfl) ⟨746369, by rfl⟩ : syracuseStep 995159 = 1492739) B1492739
theorem B995179 : Blo 992597 995179 := bstep (se 1 (by rfl) ⟨746384, by rfl⟩ : syracuseStep 995179 = 1492769) B1492769
theorem B995191 : Blo 992597 995191 := bstep (se 1 (by rfl) ⟨746393, by rfl⟩ : syracuseStep 995191 = 1492787) B1492787
theorem B995211 : Blo 992597 995211 := bstep (se 1 (by rfl) ⟨746408, by rfl⟩ : syracuseStep 995211 = 1492817) B1492817
theorem B995223 : Blo 992597 995223 := bstep (se 1 (by rfl) ⟨746417, by rfl⟩ : syracuseStep 995223 = 1492835) B1492835
theorem B3780503 : Blo 992597 3780503 := bstep (se 1 (by rfl) ⟨2835377, by rfl⟩ : syracuseStep 3780503 = 5670755) B5670755
theorem B995243 : Blo 992597 995243 := bstep (se 1 (by rfl) ⟨746432, by rfl⟩ : syracuseStep 995243 = 1492865) B1492865
theorem B995255 : Blo 992597 995255 := bstep (se 1 (by rfl) ⟨746441, by rfl⟩ : syracuseStep 995255 = 1492883) B1492883
theorem B995275 : Blo 992597 995275 := bstep (se 1 (by rfl) ⟨746456, by rfl⟩ : syracuseStep 995275 = 1492913) B1492913
theorem B2240459 : Blo 992597 2240459 := bstep (se 1 (by rfl) ⟨1680344, by rfl⟩ : syracuseStep 2240459 = 3360689) B3360689
theorem B995287 : Blo 992597 995287 := bstep (se 1 (by rfl) ⟨746465, by rfl⟩ : syracuseStep 995287 = 1492931) B1492931
theorem B2830297 : Blo 992597 2830297 := bstep (se 2 (by rfl) ⟨1061361, by rfl⟩ : syracuseStep 2830297 = 2122723) B2122723
theorem B995307 : Blo 992597 995307 := bstep (se 1 (by rfl) ⟨746480, by rfl⟩ : syracuseStep 995307 = 1492961) B1492961
theorem B995319 : Blo 992597 995319 := bstep (se 1 (by rfl) ⟨746489, by rfl⟩ : syracuseStep 995319 = 1492979) B1492979
theorem B2240513 : Blo 992597 2240513 := bstep (se 2 (by rfl) ⟨840192, by rfl⟩ : syracuseStep 2240513 = 1680385) B1680385
theorem B995339 : Blo 992597 995339 := bstep (se 1 (by rfl) ⟨746504, by rfl⟩ : syracuseStep 995339 = 1493009) B1493009
theorem B995351 : Blo 992597 995351 := bstep (se 1 (by rfl) ⟨746513, by rfl⟩ : syracuseStep 995351 = 1493027) B1493027
theorem B995371 : Blo 992597 995371 := bstep (se 1 (by rfl) ⟨746528, by rfl⟩ : syracuseStep 995371 = 1493057) B1493057
theorem B995383 : Blo 992597 995383 := bstep (se 1 (by rfl) ⟨746537, by rfl⟩ : syracuseStep 995383 = 1493075) B1493075
theorem B995403 : Blo 992597 995403 := bstep (se 1 (by rfl) ⟨746552, by rfl⟩ : syracuseStep 995403 = 1493105) B1493105
theorem B995415 : Blo 992597 995415 := bstep (se 1 (by rfl) ⟨746561, by rfl⟩ : syracuseStep 995415 = 1493123) B1493123
theorem B3780701 : Blo 992597 3780701 := bstep (se 3 (by rfl) ⟨708881, by rfl⟩ : syracuseStep 3780701 = 1417763) B1417763
theorem B995435 : Blo 992597 995435 := bstep (se 1 (by rfl) ⟨746576, by rfl⟩ : syracuseStep 995435 = 1493153) B1493153
theorem B995447 : Blo 992597 995447 := bstep (se 1 (by rfl) ⟨746585, by rfl⟩ : syracuseStep 995447 = 1493171) B1493171
theorem B995467 : Blo 992597 995467 := bstep (se 1 (by rfl) ⟨746600, by rfl⟩ : syracuseStep 995467 = 1493201) B1493201
theorem B995479 : Blo 992597 995479 := bstep (se 1 (by rfl) ⟨746609, by rfl⟩ : syracuseStep 995479 = 1493219) B1493219
theorem B995499 : Blo 992597 995499 := bstep (se 1 (by rfl) ⟨746624, by rfl⟩ : syracuseStep 995499 = 1493249) B1493249
theorem B3354803 : Blo 992597 3354803 := bstep (se 1 (by rfl) ⟨2516102, by rfl⟩ : syracuseStep 3354803 = 5032205) B5032205
theorem B995511 : Blo 992597 995511 := bstep (se 1 (by rfl) ⟨746633, by rfl⟩ : syracuseStep 995511 = 1493267) B1493267
theorem B995531 : Blo 992597 995531 := bstep (se 1 (by rfl) ⟨746648, by rfl⟩ : syracuseStep 995531 = 1493297) B1493297
theorem B995543 : Blo 992597 995543 := bstep (se 1 (by rfl) ⟨746657, by rfl⟩ : syracuseStep 995543 = 1493315) B1493315
theorem B2240729 : Blo 992597 2240729 := bstep (se 2 (by rfl) ⟨840273, by rfl⟩ : syracuseStep 2240729 = 1680547) B1680547
theorem B995563 : Blo 992597 995563 := bstep (se 1 (by rfl) ⟨746672, by rfl⟩ : syracuseStep 995563 = 1493345) B1493345
theorem B995575 : Blo 992597 995575 := bstep (se 1 (by rfl) ⟨746681, by rfl⟩ : syracuseStep 995575 = 1493363) B1493363
theorem B995595 : Blo 992597 995595 := bstep (se 1 (by rfl) ⟨746696, by rfl⟩ : syracuseStep 995595 = 1493393) B1493393
theorem B995607 : Blo 992597 995607 := bstep (se 1 (by rfl) ⟨746705, by rfl⟩ : syracuseStep 995607 = 1493411) B1493411
theorem B995627 : Blo 992597 995627 := bstep (se 1 (by rfl) ⟨746720, by rfl⟩ : syracuseStep 995627 = 1493441) B1493441
theorem B2240819 : Blo 992597 2240819 := bstep (se 1 (by rfl) ⟨1680614, by rfl⟩ : syracuseStep 2240819 = 3361229) B3361229
theorem B995639 : Blo 992597 995639 := bstep (se 1 (by rfl) ⟨746729, by rfl⟩ : syracuseStep 995639 = 1493459) B1493459
theorem B995659 : Blo 992597 995659 := bstep (se 1 (by rfl) ⟨746744, by rfl⟩ : syracuseStep 995659 = 1493489) B1493489
theorem B2240855 : Blo 992597 2240855 := bstep (se 1 (by rfl) ⟨1680641, by rfl⟩ : syracuseStep 2240855 = 3361283) B3361283
theorem B995671 : Blo 992597 995671 := bstep (se 1 (by rfl) ⟨746753, by rfl⟩ : syracuseStep 995671 = 1493507) B1493507
theorem B4305241 : Blo 992597 4305241 := bstep (se 2 (by rfl) ⟨1614465, by rfl⟩ : syracuseStep 4305241 = 3228931) B3228931
theorem B995691 : Blo 992597 995691 := bstep (se 1 (by rfl) ⟨746768, by rfl⟩ : syracuseStep 995691 = 1493537) B1493537
theorem B995703 : Blo 992597 995703 := bstep (se 1 (by rfl) ⟨746777, by rfl⟩ : syracuseStep 995703 = 1493555) B1493555
theorem B995723 : Blo 992597 995723 := bstep (se 1 (by rfl) ⟨746792, by rfl⟩ : syracuseStep 995723 = 1493585) B1493585
theorem B995735 : Blo 992597 995735 := bstep (se 1 (by rfl) ⟨746801, by rfl⟩ : syracuseStep 995735 = 1493603) B1493603
theorem B995755 : Blo 992597 995755 := bstep (se 1 (by rfl) ⟨746816, by rfl⟩ : syracuseStep 995755 = 1493633) B1493633
theorem B995767 : Blo 992597 995767 := bstep (se 1 (by rfl) ⟨746825, by rfl⟩ : syracuseStep 995767 = 1493651) B1493651
theorem B3355073 : Blo 992597 3355073 := bstep (se 2 (by rfl) ⟨1258152, by rfl⟩ : syracuseStep 3355073 = 2516305) B2516305
theorem B3584459 : Blo 992597 3584459 := bstep (se 1 (by rfl) ⟨2688344, by rfl⟩ : syracuseStep 3584459 = 5376689) B5376689
theorem B995787 : Blo 992597 995787 := bstep (se 1 (by rfl) ⟨746840, by rfl⟩ : syracuseStep 995787 = 1493681) B1493681
theorem B995799 : Blo 992597 995799 := bstep (se 1 (by rfl) ⟨746849, by rfl⟩ : syracuseStep 995799 = 1493699) B1493699
theorem B995819 : Blo 992597 995819 := bstep (se 1 (by rfl) ⟨746864, by rfl⟩ : syracuseStep 995819 = 1493729) B1493729
theorem B995831 : Blo 992597 995831 := bstep (se 1 (by rfl) ⟨746873, by rfl⟩ : syracuseStep 995831 = 1493747) B1493747
theorem B995851 : Blo 992597 995851 := bstep (se 1 (by rfl) ⟨746888, by rfl⟩ : syracuseStep 995851 = 1493777) B1493777
theorem B2241035 : Blo 992597 2241035 := bstep (se 1 (by rfl) ⟨1680776, by rfl⟩ : syracuseStep 2241035 = 3361553) B3361553
theorem B995863 : Blo 992597 995863 := bstep (se 1 (by rfl) ⟨746897, by rfl⟩ : syracuseStep 995863 = 1493795) B1493795
theorem B995883 : Blo 992597 995883 := bstep (se 1 (by rfl) ⟨746912, by rfl⟩ : syracuseStep 995883 = 1493825) B1493825
theorem B995895 : Blo 992597 995895 := bstep (se 1 (by rfl) ⟨746921, by rfl⟩ : syracuseStep 995895 = 1493843) B1493843
theorem B2830913 : Blo 992597 2830913 := bstep (se 2 (by rfl) ⟨1061592, by rfl⟩ : syracuseStep 2830913 = 2123185) B2123185
theorem B2241089 : Blo 992597 2241089 := bstep (se 2 (by rfl) ⟨840408, by rfl⟩ : syracuseStep 2241089 = 1680817) B1680817
theorem B995915 : Blo 992597 995915 := bstep (se 1 (by rfl) ⟨746936, by rfl⟩ : syracuseStep 995915 = 1493873) B1493873
theorem B995927 : Blo 992597 995927 := bstep (se 1 (by rfl) ⟨746945, by rfl⟩ : syracuseStep 995927 = 1493891) B1493891
theorem B995947 : Blo 992597 995947 := bstep (se 1 (by rfl) ⟨746960, by rfl⟩ : syracuseStep 995947 = 1493921) B1493921
theorem B995959 : Blo 992597 995959 := bstep (se 1 (by rfl) ⟨746969, by rfl⟩ : syracuseStep 995959 = 1493939) B1493939
theorem B995979 : Blo 992597 995979 := bstep (se 1 (by rfl) ⟨746984, by rfl⟩ : syracuseStep 995979 = 1493969) B1493969
theorem B995991 : Blo 992597 995991 := bstep (se 1 (by rfl) ⟨746993, by rfl⟩ : syracuseStep 995991 = 1493987) B1493987
theorem B996011 : Blo 992597 996011 := bstep (se 1 (by rfl) ⟨747008, by rfl⟩ : syracuseStep 996011 = 1494017) B1494017
theorem B996023 : Blo 992597 996023 := bstep (se 1 (by rfl) ⟨747017, by rfl⟩ : syracuseStep 996023 = 1494035) B1494035
theorem B996043 : Blo 992597 996043 := bstep (se 1 (by rfl) ⟨747032, by rfl⟩ : syracuseStep 996043 = 1494065) B1494065
theorem B996055 : Blo 992597 996055 := bstep (se 1 (by rfl) ⟨747041, by rfl⟩ : syracuseStep 996055 = 1494083) B1494083
theorem B996075 : Blo 992597 996075 := bstep (se 1 (by rfl) ⟨747056, by rfl⟩ : syracuseStep 996075 = 1494113) B1494113
theorem B996087 : Blo 992597 996087 := bstep (se 1 (by rfl) ⟨747065, by rfl⟩ : syracuseStep 996087 = 1494131) B1494131
theorem B996107 : Blo 992597 996107 := bstep (se 1 (by rfl) ⟨747080, by rfl⟩ : syracuseStep 996107 = 1494161) B1494161
theorem B996119 : Blo 992597 996119 := bstep (se 1 (by rfl) ⟨747089, by rfl⟩ : syracuseStep 996119 = 1494179) B1494179
theorem B2241305 : Blo 992597 2241305 := bstep (se 2 (by rfl) ⟨840489, by rfl⟩ : syracuseStep 2241305 = 1680979) B1680979
theorem B996139 : Blo 992597 996139 := bstep (se 1 (by rfl) ⟨747104, by rfl⟩ : syracuseStep 996139 = 1494209) B1494209
theorem B996151 : Blo 992597 996151 := bstep (se 1 (by rfl) ⟨747113, by rfl⟩ : syracuseStep 996151 = 1494227) B1494227
theorem B996171 : Blo 992597 996171 := bstep (se 1 (by rfl) ⟨747128, by rfl⟩ : syracuseStep 996171 = 1494257) B1494257
theorem B996183 : Blo 992597 996183 := bstep (se 1 (by rfl) ⟨747137, by rfl⟩ : syracuseStep 996183 = 1494275) B1494275
theorem B996203 : Blo 992597 996203 := bstep (se 1 (by rfl) ⟨747152, by rfl⟩ : syracuseStep 996203 = 1494305) B1494305
theorem B2241395 : Blo 992597 2241395 := bstep (se 1 (by rfl) ⟨1681046, by rfl⟩ : syracuseStep 2241395 = 3362093) B3362093
theorem B996215 : Blo 992597 996215 := bstep (se 1 (by rfl) ⟨747161, by rfl⟩ : syracuseStep 996215 = 1494323) B1494323
theorem B996235 : Blo 992597 996235 := bstep (se 1 (by rfl) ⟨747176, by rfl⟩ : syracuseStep 996235 = 1494353) B1494353
theorem B1192855 : Blo 992597 1192855 := bstep (se 1 (by rfl) ⟨894641, by rfl⟩ : syracuseStep 1192855 = 1789283) B1789283
theorem B2241431 : Blo 992597 2241431 := bstep (se 1 (by rfl) ⟨1681073, by rfl⟩ : syracuseStep 2241431 = 3362147) B3362147
theorem B996247 : Blo 992597 996247 := bstep (se 1 (by rfl) ⟨747185, by rfl⟩ : syracuseStep 996247 = 1494371) B1494371
theorem B996267 : Blo 992597 996267 := bstep (se 1 (by rfl) ⟨747200, by rfl⟩ : syracuseStep 996267 = 1494401) B1494401
theorem B996279 : Blo 992597 996279 := bstep (se 1 (by rfl) ⟨747209, by rfl⟩ : syracuseStep 996279 = 1494419) B1494419
theorem B996299 : Blo 992597 996299 := bstep (se 1 (by rfl) ⟨747224, by rfl⟩ : syracuseStep 996299 = 1494449) B1494449
theorem B996311 : Blo 992597 996311 := bstep (se 1 (by rfl) ⟨747233, by rfl⟩ : syracuseStep 996311 = 1494467) B1494467
theorem B3355613 : Blo 992597 3355613 := bstep (se 3 (by rfl) ⟨629177, by rfl⟩ : syracuseStep 3355613 = 1258355) B1258355
theorem B996331 : Blo 992597 996331 := bstep (se 1 (by rfl) ⟨747248, by rfl⟩ : syracuseStep 996331 = 1494497) B1494497
theorem B996343 : Blo 992597 996343 := bstep (se 1 (by rfl) ⟨747257, by rfl⟩ : syracuseStep 996343 = 1494515) B1494515
theorem B1258507 : Blo 992597 1258507 := bstep (se 1 (by rfl) ⟨943880, by rfl⟩ : syracuseStep 1258507 = 1887761) B1887761
theorem B996363 : Blo 992597 996363 := bstep (se 1 (by rfl) ⟨747272, by rfl⟩ : syracuseStep 996363 = 1494545) B1494545
theorem B6370321 : Blo 992597 6370321 := bstep (se 2 (by rfl) ⟨2388870, by rfl⟩ : syracuseStep 6370321 = 4777741) B4777741
theorem B996375 : Blo 992597 996375 := bstep (se 1 (by rfl) ⟨747281, by rfl⟩ : syracuseStep 996375 = 1494563) B1494563
theorem B996395 : Blo 992597 996395 := bstep (se 1 (by rfl) ⟨747296, by rfl⟩ : syracuseStep 996395 = 1494593) B1494593
theorem B996407 : Blo 992597 996407 := bstep (se 1 (by rfl) ⟨747305, by rfl⟩ : syracuseStep 996407 = 1494611) B1494611
theorem B2241611 : Blo 992597 2241611 := bstep (se 1 (by rfl) ⟨1681208, by rfl⟩ : syracuseStep 2241611 = 3362417) B3362417
theorem B996427 : Blo 992597 996427 := bstep (se 1 (by rfl) ⟨747320, by rfl⟩ : syracuseStep 996427 = 1494641) B1494641
theorem B996439 : Blo 992597 996439 := bstep (se 1 (by rfl) ⟨747329, by rfl⟩ : syracuseStep 996439 = 1494659) B1494659
theorem B996459 : Blo 992597 996459 := bstep (se 1 (by rfl) ⟨747344, by rfl⟩ : syracuseStep 996459 = 1494689) B1494689
theorem B996471 : Blo 992597 996471 := bstep (se 1 (by rfl) ⟨747353, by rfl⟩ : syracuseStep 996471 = 1494707) B1494707
theorem B2241665 : Blo 992597 2241665 := bstep (se 2 (by rfl) ⟨840624, by rfl⟩ : syracuseStep 2241665 = 1681249) B1681249
theorem B996491 : Blo 992597 996491 := bstep (se 1 (by rfl) ⟨747368, by rfl⟩ : syracuseStep 996491 = 1494737) B1494737
theorem B996503 : Blo 992597 996503 := bstep (se 1 (by rfl) ⟨747377, by rfl⟩ : syracuseStep 996503 = 1494755) B1494755
theorem B996523 : Blo 992597 996523 := bstep (se 1 (by rfl) ⟨747392, by rfl⟩ : syracuseStep 996523 = 1494785) B1494785
theorem B996535 : Blo 992597 996535 := bstep (se 1 (by rfl) ⟨747401, by rfl⟩ : syracuseStep 996535 = 1494803) B1494803
theorem B996555 : Blo 992597 996555 := bstep (se 1 (by rfl) ⟨747416, by rfl⟩ : syracuseStep 996555 = 1494833) B1494833
theorem B12104909 : Blo 992597 12104909 := bstep (se 3 (by rfl) ⟨2269670, by rfl⟩ : syracuseStep 12104909 = 4539341) B4539341
theorem B996567 : Blo 992597 996567 := bstep (se 1 (by rfl) ⟨747425, by rfl⟩ : syracuseStep 996567 = 1494851) B1494851
theorem B996587 : Blo 992597 996587 := bstep (se 1 (by rfl) ⟨747440, by rfl⟩ : syracuseStep 996587 = 1494881) B1494881
theorem B12760325 : Blo 992597 12760325 := bstep (se 4 (by rfl) ⟨1196280, by rfl⟩ : syracuseStep 12760325 = 2392561) B2392561
theorem B3585325 : Blo 992597 3585325 := bstep (se 3 (by rfl) ⟨672248, by rfl⟩ : syracuseStep 3585325 = 1344497) B1344497
theorem B2241881 : Blo 992597 2241881 := bstep (se 2 (by rfl) ⟨840705, by rfl⟩ : syracuseStep 2241881 = 1681411) B1681411
theorem B2241971 : Blo 992597 2241971 := bstep (se 1 (by rfl) ⟨1681478, by rfl⟩ : syracuseStep 2241971 = 3362957) B3362957
theorem B2242007 : Blo 992597 2242007 := bstep (se 1 (by rfl) ⟨1681505, by rfl⟩ : syracuseStep 2242007 = 3363011) B3363011
theorem B5027345 : Blo 992597 5027345 := bstep (se 2 (by rfl) ⟨1885254, by rfl⟩ : syracuseStep 5027345 = 3770509) B3770509
theorem B1062455 : Blo 992597 1062455 := bstep (se 1 (by rfl) ⟨796841, by rfl⟩ : syracuseStep 1062455 = 1593683) B1593683
theorem B2242187 : Blo 992597 2242187 := bstep (se 1 (by rfl) ⟨1681640, by rfl⟩ : syracuseStep 2242187 = 3363281) B3363281
theorem B5027507 : Blo 992597 5027507 := bstep (se 1 (by rfl) ⟨3770630, by rfl⟩ : syracuseStep 5027507 = 7541261) B7541261
theorem B2242241 : Blo 992597 2242241 := bstep (se 2 (by rfl) ⟨840840, by rfl⟩ : syracuseStep 2242241 = 1681681) B1681681
theorem B1259479 : Blo 992597 1259479 := bstep (se 1 (by rfl) ⟨944609, by rfl⟩ : syracuseStep 1259479 = 1889219) B1889219
theorem B3782659 : Blo 992597 3782659 := bstep (se 1 (by rfl) ⟨2836994, by rfl⟩ : syracuseStep 3782659 = 5673989) B5673989
theorem B7550981 : Blo 992597 7550981 := bstep (se 4 (by rfl) ⟨707904, by rfl⟩ : syracuseStep 7550981 = 1415809) B1415809
theorem B1488971 : Blo 992597 1488971 := bstep (se 1 (by rfl) ⟨1116728, by rfl⟩ : syracuseStep 1488971 = 2233457) B2233457
theorem B4241483 : Blo 992597 4241483 := bstep (se 1 (by rfl) ⟨3181112, by rfl⟩ : syracuseStep 4241483 = 6362225) B6362225
theorem B3356747 : Blo 992597 3356747 := bstep (se 1 (by rfl) ⟨2517560, by rfl⟩ : syracuseStep 3356747 = 5035121) B5035121
theorem B1488983 : Blo 992597 1488983 := bstep (se 1 (by rfl) ⟨1116737, by rfl⟩ : syracuseStep 1488983 = 2233475) B2233475
theorem B1489049 : Blo 992597 1489049 := bstep (se 2 (by rfl) ⟨558393, by rfl⟩ : syracuseStep 1489049 = 1116787) B1116787
theorem B1489163 : Blo 992597 1489163 := bstep (se 1 (by rfl) ⟨1116872, by rfl⟩ : syracuseStep 1489163 = 2233745) B2233745
theorem B1489175 : Blo 992597 1489175 := bstep (se 1 (by rfl) ⟨1116881, by rfl⟩ : syracuseStep 1489175 = 2233763) B2233763
theorem B3782963 : Blo 992597 3782963 := bstep (se 1 (by rfl) ⟨2837222, by rfl⟩ : syracuseStep 3782963 = 5674445) B5674445
theorem B1489241 : Blo 992597 1489241 := bstep (se 2 (by rfl) ⟨558465, by rfl⟩ : syracuseStep 1489241 = 1116931) B1116931
theorem B3357017 : Blo 992597 3357017 := bstep (se 2 (by rfl) ⟨1258881, by rfl⟩ : syracuseStep 3357017 = 2517763) B2517763
theorem B1489355 : Blo 992597 1489355 := bstep (se 1 (by rfl) ⟨1117016, by rfl⟩ : syracuseStep 1489355 = 2234033) B2234033
theorem B1489367 : Blo 992597 1489367 := bstep (se 1 (by rfl) ⟨1117025, by rfl⟩ : syracuseStep 1489367 = 2234051) B2234051
theorem B1489433 : Blo 992597 1489433 := bstep (se 2 (by rfl) ⟨558537, by rfl⟩ : syracuseStep 1489433 = 1117075) B1117075
theorem B2832985 : Blo 992597 2832985 := bstep (se 2 (by rfl) ⟨1062369, by rfl⟩ : syracuseStep 2832985 = 2124739) B2124739
theorem B1489547 : Blo 992597 1489547 := bstep (se 1 (by rfl) ⟨1117160, by rfl⟩ : syracuseStep 1489547 = 2234321) B2234321
theorem B1489559 : Blo 992597 1489559 := bstep (se 1 (by rfl) ⟨1117169, by rfl⟩ : syracuseStep 1489559 = 2234339) B2234339
theorem B1194647 : Blo 992597 1194647 := bstep (se 1 (by rfl) ⟨895985, by rfl⟩ : syracuseStep 1194647 = 1791971) B1791971
theorem B1489625 : Blo 992597 1489625 := bstep (se 2 (by rfl) ⟨558609, by rfl⟩ : syracuseStep 1489625 = 1117219) B1117219
theorem B1194763 : Blo 992597 1194763 := bstep (se 1 (by rfl) ⟨896072, by rfl⟩ : syracuseStep 1194763 = 1792145) B1792145
theorem B1260299 : Blo 992597 1260299 := bstep (se 1 (by rfl) ⟨945224, by rfl⟩ : syracuseStep 1260299 = 1890449) B1890449
theorem B1489739 : Blo 992597 1489739 := bstep (se 1 (by rfl) ⟨1117304, by rfl⟩ : syracuseStep 1489739 = 2234609) B2234609
theorem B1489751 : Blo 992597 1489751 := bstep (se 1 (by rfl) ⟨1117313, by rfl⟩ : syracuseStep 1489751 = 2234627) B2234627
theorem B1489817 : Blo 992597 1489817 := bstep (se 2 (by rfl) ⟨558681, by rfl⟩ : syracuseStep 1489817 = 1117363) B1117363
theorem B3783617 : Blo 992597 3783617 := bstep (se 2 (by rfl) ⟨1418856, by rfl⟩ : syracuseStep 3783617 = 2837713) B2837713
theorem B2833373 : Blo 992597 2833373 := bstep (se 3 (by rfl) ⟨531257, by rfl⟩ : syracuseStep 2833373 = 1062515) B1062515
theorem B1489931 : Blo 992597 1489931 := bstep (se 1 (by rfl) ⟨1117448, by rfl⟩ : syracuseStep 1489931 = 2234897) B2234897
theorem B1489943 : Blo 992597 1489943 := bstep (se 1 (by rfl) ⟨1117457, by rfl⟩ : syracuseStep 1489943 = 2234915) B2234915
theorem B3357719 : Blo 992597 3357719 := bstep (se 1 (by rfl) ⟨2518289, by rfl⟩ : syracuseStep 3357719 = 5036579) B5036579
theorem B1490009 : Blo 992597 1490009 := bstep (se 2 (by rfl) ⟨558753, by rfl⟩ : syracuseStep 1490009 = 1117507) B1117507
theorem B1490123 : Blo 992597 1490123 := bstep (se 1 (by rfl) ⟨1117592, by rfl⟩ : syracuseStep 1490123 = 2235185) B2235185
theorem B1490135 : Blo 992597 1490135 := bstep (se 1 (by rfl) ⟨1117601, by rfl⟩ : syracuseStep 1490135 = 2235203) B2235203
theorem B1064215 : Blo 992597 1064215 := bstep (se 1 (by rfl) ⟨798161, by rfl⟩ : syracuseStep 1064215 = 1596323) B1596323
theorem B1490201 : Blo 992597 1490201 := bstep (se 2 (by rfl) ⟨558825, by rfl⟩ : syracuseStep 1490201 = 1117651) B1117651
theorem B1490315 : Blo 992597 1490315 := bstep (se 1 (by rfl) ⟨1117736, by rfl⟩ : syracuseStep 1490315 = 2235473) B2235473
theorem B1490327 : Blo 992597 1490327 := bstep (se 1 (by rfl) ⟨1117745, by rfl⟩ : syracuseStep 1490327 = 2235491) B2235491
theorem B1261003 : Blo 992597 1261003 := bstep (se 1 (by rfl) ⟨945752, by rfl⟩ : syracuseStep 1261003 = 1891505) B1891505
theorem B1490393 : Blo 992597 1490393 := bstep (se 2 (by rfl) ⟨558897, by rfl⟩ : syracuseStep 1490393 = 1117795) B1117795
theorem B3358259 : Blo 992597 3358259 := bstep (se 1 (by rfl) ⟨2518694, by rfl⟩ : syracuseStep 3358259 = 5037389) B5037389
theorem B5029451 : Blo 992597 5029451 := bstep (se 1 (by rfl) ⟨3772088, by rfl⟩ : syracuseStep 5029451 = 7544177) B7544177
theorem B1490507 : Blo 992597 1490507 := bstep (se 1 (by rfl) ⟨1117880, by rfl⟩ : syracuseStep 1490507 = 2235761) B2235761
theorem B1490519 : Blo 992597 1490519 := bstep (se 1 (by rfl) ⟨1117889, by rfl⟩ : syracuseStep 1490519 = 2235779) B2235779
theorem B1490585 : Blo 992597 1490585 := bstep (se 2 (by rfl) ⟨558969, by rfl⟩ : syracuseStep 1490585 = 1117939) B1117939
theorem B1261271 : Blo 992597 1261271 := bstep (se 1 (by rfl) ⟨945953, by rfl⟩ : syracuseStep 1261271 = 1891907) B1891907
theorem B9060101 : Blo 992597 9060101 := bstep (se 4 (by rfl) ⟨849384, by rfl⟩ : syracuseStep 9060101 = 1698769) B1698769
theorem B1490699 : Blo 992597 1490699 := bstep (se 1 (by rfl) ⟨1118024, by rfl⟩ : syracuseStep 1490699 = 2236049) B2236049
theorem B1490711 : Blo 992597 1490711 := bstep (se 1 (by rfl) ⟨1118033, by rfl⟩ : syracuseStep 1490711 = 2236067) B2236067
theorem B2015027 : Blo 992597 2015027 := bstep (se 1 (by rfl) ⟨1511270, by rfl⟩ : syracuseStep 2015027 = 3022541) B3022541
theorem B3358529 : Blo 992597 3358529 := bstep (se 2 (by rfl) ⟨1259448, by rfl⟩ : syracuseStep 3358529 = 2518897) B2518897
theorem B1490777 : Blo 992597 1490777 := bstep (se 2 (by rfl) ⟨559041, by rfl⟩ : syracuseStep 1490777 = 1118083) B1118083
theorem B1490891 : Blo 992597 1490891 := bstep (se 1 (by rfl) ⟨1118168, by rfl⟩ : syracuseStep 1490891 = 2236337) B2236337
theorem B1490903 : Blo 992597 1490903 := bstep (se 1 (by rfl) ⟨1118177, by rfl⟩ : syracuseStep 1490903 = 2236355) B2236355
theorem B4538333 : Blo 992597 4538333 := bstep (se 3 (by rfl) ⟨850937, by rfl⟩ : syracuseStep 4538333 = 1701875) B1701875
theorem B1490969 : Blo 992597 1490969 := bstep (se 2 (by rfl) ⟨559113, by rfl⟩ : syracuseStep 1490969 = 1118227) B1118227
theorem B1491083 : Blo 992597 1491083 := bstep (se 1 (by rfl) ⟨1118312, by rfl⟩ : syracuseStep 1491083 = 2236625) B2236625
theorem B1491095 : Blo 992597 1491095 := bstep (se 1 (by rfl) ⟨1118321, by rfl⟩ : syracuseStep 1491095 = 2236643) B2236643
theorem B1491161 : Blo 992597 1491161 := bstep (se 2 (by rfl) ⟨559185, by rfl⟩ : syracuseStep 1491161 = 1118371) B1118371
theorem B1491275 : Blo 992597 1491275 := bstep (se 1 (by rfl) ⟨1118456, by rfl⟩ : syracuseStep 1491275 = 2236913) B2236913
theorem B1491287 : Blo 992597 1491287 := bstep (se 1 (by rfl) ⟨1118465, by rfl⟩ : syracuseStep 1491287 = 2236931) B2236931
theorem B3359069 : Blo 992597 3359069 := bstep (se 3 (by rfl) ⟨629825, by rfl⟩ : syracuseStep 3359069 = 1259651) B1259651
theorem B7553411 : Blo 992597 7553411 := bstep (se 1 (by rfl) ⟨5665058, by rfl⟩ : syracuseStep 7553411 = 11330117) B11330117
theorem B1491353 : Blo 992597 1491353 := bstep (se 2 (by rfl) ⟨559257, by rfl⟩ : syracuseStep 1491353 = 1118515) B1118515
theorem B4538845 : Blo 992597 4538845 := bstep (se 3 (by rfl) ⟨851033, by rfl⟩ : syracuseStep 4538845 = 1702067) B1702067
theorem B1491467 : Blo 992597 1491467 := bstep (se 1 (by rfl) ⟨1118600, by rfl⟩ : syracuseStep 1491467 = 2237201) B2237201
theorem B1491479 : Blo 992597 1491479 := bstep (se 1 (by rfl) ⟨1118609, by rfl⟩ : syracuseStep 1491479 = 2237219) B2237219
theorem B1491545 : Blo 992597 1491545 := bstep (se 2 (by rfl) ⟨559329, by rfl⟩ : syracuseStep 1491545 = 1118659) B1118659
theorem B4244147 : Blo 992597 4244147 := bstep (se 1 (by rfl) ⟨3183110, by rfl⟩ : syracuseStep 4244147 = 6366221) B6366221
theorem B1491659 : Blo 992597 1491659 := bstep (se 1 (by rfl) ⟨1118744, by rfl⟩ : syracuseStep 1491659 = 2237489) B2237489
theorem B1491671 : Blo 992597 1491671 := bstep (se 1 (by rfl) ⟨1118753, by rfl⟩ : syracuseStep 1491671 = 2237507) B2237507
theorem B1491737 : Blo 992597 1491737 := bstep (se 2 (by rfl) ⟨559401, by rfl⟩ : syracuseStep 1491737 = 1118803) B1118803
theorem B1491851 : Blo 992597 1491851 := bstep (se 1 (by rfl) ⟨1118888, by rfl⟩ : syracuseStep 1491851 = 2237777) B2237777
theorem B1491863 : Blo 992597 1491863 := bstep (se 1 (by rfl) ⟨1118897, by rfl⟩ : syracuseStep 1491863 = 2237795) B2237795
theorem B1491929 : Blo 992597 1491929 := bstep (se 2 (by rfl) ⟨559473, by rfl⟩ : syracuseStep 1491929 = 1118947) B1118947
theorem B1492043 : Blo 992597 1492043 := bstep (se 1 (by rfl) ⟨1119032, by rfl⟩ : syracuseStep 1492043 = 2238065) B2238065
theorem B1492055 : Blo 992597 1492055 := bstep (se 1 (by rfl) ⟨1119041, by rfl⟩ : syracuseStep 1492055 = 2238083) B2238083
theorem B2016407 : Blo 992597 2016407 := bstep (se 1 (by rfl) ⟨1512305, by rfl⟩ : syracuseStep 2016407 = 3024611) B3024611
theorem B1492121 : Blo 992597 1492121 := bstep (se 2 (by rfl) ⟨559545, by rfl⟩ : syracuseStep 1492121 = 1119091) B1119091
theorem B1492235 : Blo 992597 1492235 := bstep (se 1 (by rfl) ⟨1119176, by rfl⟩ : syracuseStep 1492235 = 2238353) B2238353
theorem B1492247 : Blo 992597 1492247 := bstep (se 1 (by rfl) ⟨1119185, by rfl⟩ : syracuseStep 1492247 = 2238371) B2238371
theorem B5031233 : Blo 992597 5031233 := bstep (se 2 (by rfl) ⟨1886712, by rfl⟩ : syracuseStep 5031233 = 3773425) B3773425
theorem B1492313 : Blo 992597 1492313 := bstep (se 2 (by rfl) ⟨559617, by rfl⟩ : syracuseStep 1492313 = 1119235) B1119235
theorem B1885619 : Blo 992597 1885619 := bstep (se 1 (by rfl) ⟨1414214, by rfl⟩ : syracuseStep 1885619 = 2828429) B2828429
theorem B1492427 : Blo 992597 1492427 := bstep (se 1 (by rfl) ⟨1119320, by rfl⟩ : syracuseStep 1492427 = 2238641) B2238641
theorem B3360203 : Blo 992597 3360203 := bstep (se 1 (by rfl) ⟨2520152, by rfl⟩ : syracuseStep 3360203 = 5040305) B5040305
theorem B1492439 : Blo 992597 1492439 := bstep (se 1 (by rfl) ⟨1119329, by rfl⟩ : syracuseStep 1492439 = 2238659) B2238659
theorem B5654033 : Blo 992597 5654033 := bstep (se 2 (by rfl) ⟨2120262, by rfl⟩ : syracuseStep 5654033 = 4240525) B4240525
theorem B1492505 : Blo 992597 1492505 := bstep (se 2 (by rfl) ⟨559689, by rfl⟩ : syracuseStep 1492505 = 1119379) B1119379
theorem B4605505 : Blo 992597 4605505 := bstep (se 2 (by rfl) ⟨1727064, by rfl⟩ : syracuseStep 4605505 = 3454129) B3454129
theorem B1885771 : Blo 992597 1885771 := bstep (se 1 (by rfl) ⟨1414328, by rfl⟩ : syracuseStep 1885771 = 2828657) B2828657
theorem B1492619 : Blo 992597 1492619 := bstep (se 1 (by rfl) ⟨1119464, by rfl⟩ : syracuseStep 1492619 = 2238929) B2238929
theorem B6801047 : Blo 992597 6801047 := bstep (se 1 (by rfl) ⟨5100785, by rfl⟩ : syracuseStep 6801047 = 10201571) B10201571
theorem B1492631 : Blo 992597 1492631 := bstep (se 1 (by rfl) ⟨1119473, by rfl⟩ : syracuseStep 1492631 = 2238947) B2238947
theorem B1492697 : Blo 992597 1492697 := bstep (se 2 (by rfl) ⟨559761, by rfl⟩ : syracuseStep 1492697 = 1119523) B1119523
theorem B3360473 : Blo 992597 3360473 := bstep (se 2 (by rfl) ⟨1260177, by rfl⟩ : syracuseStep 3360473 = 2520355) B2520355
theorem B2836289 : Blo 992597 2836289 := bstep (se 2 (by rfl) ⟨1063608, by rfl⟩ : syracuseStep 2836289 = 2127217) B2127217
theorem B1492811 : Blo 992597 1492811 := bstep (se 1 (by rfl) ⟨1119608, by rfl⟩ : syracuseStep 1492811 = 2239217) B2239217
theorem B1492823 : Blo 992597 1492823 := bstep (se 1 (by rfl) ⟨1119617, by rfl⟩ : syracuseStep 1492823 = 2239235) B2239235
theorem B1886105 : Blo 992597 1886105 := bstep (se 2 (by rfl) ⟨707289, by rfl⟩ : syracuseStep 1886105 = 1414579) B1414579
theorem B1492889 : Blo 992597 1492889 := bstep (se 2 (by rfl) ⟨559833, by rfl⟩ : syracuseStep 1492889 = 1119667) B1119667
theorem B6375347 : Blo 992597 6375347 := bstep (se 1 (by rfl) ⟨4781510, by rfl⟩ : syracuseStep 6375347 = 9563021) B9563021
theorem B2836403 : Blo 992597 2836403 := bstep (se 1 (by rfl) ⟨2127302, by rfl⟩ : syracuseStep 2836403 = 4254605) B4254605
theorem B1493003 : Blo 992597 1493003 := bstep (se 1 (by rfl) ⟨1119752, by rfl⟩ : syracuseStep 1493003 = 2239505) B2239505
theorem B1722391 : Blo 992597 1722391 := bstep (se 1 (by rfl) ⟨1291793, by rfl⟩ : syracuseStep 1722391 = 2583587) B2583587
theorem B1493015 : Blo 992597 1493015 := bstep (se 1 (by rfl) ⟨1119761, by rfl⟩ : syracuseStep 1493015 = 2239523) B2239523
theorem B1493081 : Blo 992597 1493081 := bstep (se 2 (by rfl) ⟨559905, by rfl⟩ : syracuseStep 1493081 = 1119811) B1119811
theorem B4245635 : Blo 992597 4245635 := bstep (se 1 (by rfl) ⟨3184226, by rfl⟩ : syracuseStep 4245635 = 6368453) B6368453
theorem B1493195 : Blo 992597 1493195 := bstep (se 1 (by rfl) ⟨1119896, by rfl⟩ : syracuseStep 1493195 = 2239793) B2239793
theorem B1493207 : Blo 992597 1493207 := bstep (se 1 (by rfl) ⟨1119905, by rfl⟩ : syracuseStep 1493207 = 2239811) B2239811
theorem B1493273 : Blo 992597 1493273 := bstep (se 2 (by rfl) ⟨559977, by rfl⟩ : syracuseStep 1493273 = 1119955) B1119955
theorem B1493387 : Blo 992597 1493387 := bstep (se 1 (by rfl) ⟨1120040, by rfl⟩ : syracuseStep 1493387 = 2240081) B2240081
theorem B1493399 : Blo 992597 1493399 := bstep (se 1 (by rfl) ⟨1120049, by rfl⟩ : syracuseStep 1493399 = 2240099) B2240099
theorem B3361175 : Blo 992597 3361175 := bstep (se 1 (by rfl) ⟨2520881, by rfl⟩ : syracuseStep 3361175 = 5041763) B5041763
theorem B7162289 : Blo 992597 7162289 := bstep (se 2 (by rfl) ⟨2685858, by rfl⟩ : syracuseStep 7162289 = 5371717) B5371717
theorem B1493465 : Blo 992597 1493465 := bstep (se 2 (by rfl) ⟨560049, by rfl⟩ : syracuseStep 1493465 = 1120099) B1120099
theorem B1886743 : Blo 992597 1886743 := bstep (se 1 (by rfl) ⟨1415057, by rfl⟩ : syracuseStep 1886743 = 2830115) B2830115
theorem B1493579 : Blo 992597 1493579 := bstep (se 1 (by rfl) ⟨1120184, by rfl⟩ : syracuseStep 1493579 = 2240369) B2240369
theorem B1493591 : Blo 992597 1493591 := bstep (se 1 (by rfl) ⟨1120193, by rfl⟩ : syracuseStep 1493591 = 2240387) B2240387
theorem B1493657 : Blo 992597 1493657 := bstep (se 2 (by rfl) ⟨560121, by rfl⟩ : syracuseStep 1493657 = 1120243) B1120243
theorem B1592011 : Blo 992597 1592011 := bstep (se 1 (by rfl) ⟨1194008, by rfl⟩ : syracuseStep 1592011 = 2388017) B2388017
theorem B1493771 : Blo 992597 1493771 := bstep (se 1 (by rfl) ⟨1120328, by rfl⟩ : syracuseStep 1493771 = 2240657) B2240657
theorem B1493783 : Blo 992597 1493783 := bstep (se 1 (by rfl) ⟨1120337, by rfl⟩ : syracuseStep 1493783 = 2240675) B2240675
theorem B1493849 : Blo 992597 1493849 := bstep (se 2 (by rfl) ⟨560193, by rfl⟩ : syracuseStep 1493849 = 1120387) B1120387
theorem B9554867 : Blo 992597 9554867 := bstep (se 1 (by rfl) ⟨7166150, by rfl⟩ : syracuseStep 9554867 = 14332301) B14332301
theorem B3361715 : Blo 992597 3361715 := bstep (se 1 (by rfl) ⟨2521286, by rfl⟩ : syracuseStep 3361715 = 5042573) B5042573
theorem B1493963 : Blo 992597 1493963 := bstep (se 1 (by rfl) ⟨1120472, by rfl⟩ : syracuseStep 1493963 = 2240945) B2240945
theorem B1493975 : Blo 992597 1493975 := bstep (se 1 (by rfl) ⟨1120481, by rfl⟩ : syracuseStep 1493975 = 2240963) B2240963
theorem B1494041 : Blo 992597 1494041 := bstep (se 2 (by rfl) ⟨560265, by rfl⟩ : syracuseStep 1494041 = 1120531) B1120531
theorem B1494155 : Blo 992597 1494155 := bstep (se 1 (by rfl) ⟨1120616, by rfl⟩ : syracuseStep 1494155 = 2241233) B2241233
theorem B1494167 : Blo 992597 1494167 := bstep (se 1 (by rfl) ⟨1120625, by rfl⟩ : syracuseStep 1494167 = 2241251) B2241251
theorem B3361985 : Blo 992597 3361985 := bstep (se 2 (by rfl) ⟨1260744, by rfl⟩ : syracuseStep 3361985 = 2521489) B2521489
theorem B5033177 : Blo 992597 5033177 := bstep (se 2 (by rfl) ⟨1887441, by rfl⟩ : syracuseStep 5033177 = 3774883) B3774883
theorem B1494233 : Blo 992597 1494233 := bstep (se 2 (by rfl) ⟨560337, by rfl⟩ : syracuseStep 1494233 = 1120675) B1120675
theorem B1887563 : Blo 992597 1887563 := bstep (se 1 (by rfl) ⟨1415672, by rfl⟩ : syracuseStep 1887563 = 2831345) B2831345
theorem B1494347 : Blo 992597 1494347 := bstep (se 1 (by rfl) ⟨1120760, by rfl⟩ : syracuseStep 1494347 = 2241521) B2241521
theorem B1494359 : Blo 992597 1494359 := bstep (se 1 (by rfl) ⟨1120769, by rfl⟩ : syracuseStep 1494359 = 2241539) B2241539
theorem B1887617 : Blo 992597 1887617 := bstep (se 2 (by rfl) ⟨707856, by rfl⟩ : syracuseStep 1887617 = 1415713) B1415713
theorem B1494425 : Blo 992597 1494425 := bstep (se 2 (by rfl) ⟨560409, by rfl⟩ : syracuseStep 1494425 = 1120819) B1120819
theorem B1494539 : Blo 992597 1494539 := bstep (se 1 (by rfl) ⟨1120904, by rfl⟩ : syracuseStep 1494539 = 2241809) B2241809
theorem B1494551 : Blo 992597 1494551 := bstep (se 1 (by rfl) ⟨1120913, by rfl⟩ : syracuseStep 1494551 = 2241827) B2241827
theorem B1494617 : Blo 992597 1494617 := bstep (se 2 (by rfl) ⟨560481, by rfl⟩ : syracuseStep 1494617 = 1120963) B1120963
theorem B55266947 : Blo 992597 55266947 := bstep (se 1 (by rfl) ⟨41450210, by rfl⟩ : syracuseStep 55266947 = 82900421) B82900421
theorem B1494731 : Blo 992597 1494731 := bstep (se 1 (by rfl) ⟨1121048, by rfl⟩ : syracuseStep 1494731 = 2242097) B2242097
theorem B7556813 : Blo 992597 7556813 := bstep (se 3 (by rfl) ⟨1416902, by rfl⟩ : syracuseStep 7556813 = 2833805) B2833805
theorem B1494743 : Blo 992597 1494743 := bstep (se 1 (by rfl) ⟨1121057, by rfl⟩ : syracuseStep 1494743 = 2242115) B2242115
theorem B3362525 : Blo 992597 3362525 := bstep (se 3 (by rfl) ⟨630473, by rfl⟩ : syracuseStep 3362525 = 1260947) B1260947
theorem B1494809 : Blo 992597 1494809 := bstep (se 2 (by rfl) ⟨560553, by rfl⟩ : syracuseStep 1494809 = 1121107) B1121107
theorem B1790039 : Blo 992597 1790039 := bstep (se 1 (by rfl) ⟨1342529, by rfl⟩ : syracuseStep 1790039 = 2685059) B2685059
theorem B7557299 : Blo 992597 7557299 := bstep (se 1 (by rfl) ⟨5667974, by rfl⟩ : syracuseStep 7557299 = 11335949) B11335949
theorem B1888535 : Blo 992597 1888535 := bstep (se 1 (by rfl) ⟨1416401, by rfl⟩ : syracuseStep 1888535 = 2832803) B2832803
theorem B4247873 : Blo 992597 4247873 := bstep (se 2 (by rfl) ⟨1592952, by rfl⟩ : syracuseStep 4247873 = 3185905) B3185905
theorem B1790515 : Blo 992597 1790515 := bstep (se 1 (by rfl) ⟨1342886, by rfl⟩ : syracuseStep 1790515 = 2685773) B2685773
theorem B2904665 : Blo 992597 2904665 := bstep (se 2 (by rfl) ⟨1089249, by rfl⟩ : syracuseStep 2904665 = 2178499) B2178499
theorem B2019991 : Blo 992597 2019991 := bstep (se 1 (by rfl) ⟨1514993, by rfl⟩ : syracuseStep 2019991 = 3029987) B3029987
theorem B5034797 : Blo 992597 5034797 := bstep (se 3 (by rfl) ⟨944024, by rfl⟩ : syracuseStep 5034797 = 1888049) B1888049
theorem B1889075 : Blo 992597 1889075 := bstep (se 1 (by rfl) ⟨1416806, by rfl⟩ : syracuseStep 1889075 = 2833613) B2833613
theorem B22926179 : Blo 992597 22926179 := bstep (se 1 (by rfl) ⟨17194634, by rfl⟩ : syracuseStep 22926179 = 34389269) B34389269
theorem B6378371 : Blo 992597 6378371 := bstep (se 1 (by rfl) ⟨4783778, by rfl⟩ : syracuseStep 6378371 = 9567557) B9567557
theorem B9196805 : Blo 992597 9196805 := bstep (se 4 (by rfl) ⟨862200, by rfl⟩ : syracuseStep 9196805 = 1724401) B1724401
theorem B1889561 : Blo 992597 1889561 := bstep (se 2 (by rfl) ⟨708585, by rfl⟩ : syracuseStep 1889561 = 1417171) B1417171
theorem B1791307 : Blo 992597 1791307 := bstep (se 1 (by rfl) ⟨1343480, by rfl⟩ : syracuseStep 1791307 = 2686961) B2686961
theorem B15324515 : Blo 992597 15324515 := bstep (se 1 (by rfl) ⟨11493386, by rfl⟩ : syracuseStep 15324515 = 22986773) B22986773
theorem B2151859 : Blo 992597 2151859 := bstep (se 1 (by rfl) ⟨1613894, by rfl⟩ : syracuseStep 2151859 = 3227789) B3227789
theorem B7263749 : Blo 992597 7263749 := bstep (se 4 (by rfl) ⟨680976, by rfl⟩ : syracuseStep 7263749 = 1361953) B1361953
theorem B1726039 : Blo 992597 1726039 := bstep (se 1 (by rfl) ⟨1294529, by rfl⟩ : syracuseStep 1726039 = 2589059) B2589059
theorem B7558757 : Blo 992597 7558757 := bstep (se 4 (by rfl) ⟨708633, by rfl⟩ : syracuseStep 7558757 = 1417267) B1417267
theorem B9557635 : Blo 992597 9557635 := bstep (se 1 (by rfl) ⟨7168226, by rfl⟩ : syracuseStep 9557635 = 14336453) B14336453
theorem B2512691 : Blo 992597 2512691 := bstep (se 1 (by rfl) ⟨1884518, by rfl⟩ : syracuseStep 2512691 = 3769037) B3769037
theorem B4085569 : Blo 992597 4085569 := bstep (se 2 (by rfl) ⟨1532088, by rfl⟩ : syracuseStep 4085569 = 3064177) B3064177
theorem B4249547 : Blo 992597 4249547 := bstep (se 1 (by rfl) ⟨3187160, by rfl⟩ : syracuseStep 4249547 = 6374321) B6374321
theorem B2873291 : Blo 992597 2873291 := bstep (se 1 (by rfl) ⟨2154968, by rfl⟩ : syracuseStep 2873291 = 4309937) B4309937
theorem B7559243 : Blo 992597 7559243 := bstep (se 1 (by rfl) ⟨5669432, by rfl⟩ : syracuseStep 7559243 = 11338865) B11338865
theorem B1792115 : Blo 992597 1792115 := bstep (se 1 (by rfl) ⟨1344086, by rfl⟩ : syracuseStep 1792115 = 2688173) B2688173
theorem B9328819 : Blo 992597 9328819 := bstep (se 1 (by rfl) ⟨6996614, by rfl⟩ : syracuseStep 9328819 = 13993229) B13993229
theorem B3233971 : Blo 992597 3233971 := bstep (se 1 (by rfl) ⟨2425478, by rfl⟩ : syracuseStep 3233971 = 4850957) B4850957
theorem B6740147 : Blo 992597 6740147 := bstep (se 1 (by rfl) ⟨5055110, by rfl⟩ : syracuseStep 6740147 = 10110221) B10110221
theorem B3627287 : Blo 992597 3627287 := bstep (se 1 (by rfl) ⟨2720465, by rfl⟩ : syracuseStep 3627287 = 5440931) B5440931
theorem B2513227 : Blo 992597 2513227 := bstep (se 1 (by rfl) ⟨1884920, by rfl⟩ : syracuseStep 2513227 = 3769841) B3769841
theorem B2120023 : Blo 992597 2120023 := bstep (se 1 (by rfl) ⟨1590017, by rfl⟩ : syracuseStep 2120023 = 3180035) B3180035
theorem B2513369 : Blo 992597 2513369 := bstep (se 2 (by rfl) ⟨942513, by rfl⟩ : syracuseStep 2513369 = 1885027) B1885027
theorem B1891019 : Blo 992597 1891019 := bstep (se 1 (by rfl) ⟨1418264, by rfl⟩ : syracuseStep 1891019 = 2836529) B2836529
theorem B4250333 : Blo 992597 4250333 := bstep (se 3 (by rfl) ⟨796937, by rfl⟩ : syracuseStep 4250333 = 1593875) B1593875
theorem B5659409 : Blo 992597 5659409 := bstep (se 2 (by rfl) ⟨2122278, by rfl⟩ : syracuseStep 5659409 = 4244557) B4244557
theorem B1891201 : Blo 992597 1891201 := bstep (se 2 (by rfl) ⟨709200, by rfl⟩ : syracuseStep 1891201 = 1418401) B1418401
theorem B1006475 : Blo 992597 1006475 := bstep (se 1 (by rfl) ⟨754856, by rfl⟩ : syracuseStep 1006475 = 1509713) B1509713
theorem B6904793 : Blo 992597 6904793 := bstep (se 2 (by rfl) ⟨2589297, by rfl⟩ : syracuseStep 6904793 = 5178595) B5178595
theorem B9067697 : Blo 992597 9067697 := bstep (se 2 (by rfl) ⟨3400386, by rfl⟩ : syracuseStep 9067697 = 6800773) B6800773
theorem B20405429 : Blo 992597 20405429 := bstep (se 5 (by rfl) ⟨956504, by rfl⟩ : syracuseStep 20405429 = 1913009) B1913009
theorem B5659865 : Blo 992597 5659865 := bstep (se 2 (by rfl) ⟨2122449, by rfl⟩ : syracuseStep 5659865 = 4244899) B4244899
theorem B2514199 : Blo 992597 2514199 := bstep (se 1 (by rfl) ⟨1885649, by rfl⟩ : syracuseStep 2514199 = 3771299) B3771299
theorem B3398935 : Blo 992597 3398935 := bstep (se 1 (by rfl) ⟨2549201, by rfl⟩ : syracuseStep 3398935 = 5098403) B5098403
theorem B1891649 : Blo 992597 1891649 := bstep (se 2 (by rfl) ⟨709368, by rfl⟩ : syracuseStep 1891649 = 1418737) B1418737
theorem B2121203 : Blo 992597 2121203 := bstep (se 1 (by rfl) ⟨1590902, by rfl⟩ : syracuseStep 2121203 = 3181805) B3181805
theorem B1793665 : Blo 992597 1793665 := bstep (se 2 (by rfl) ⟨672624, by rfl⟩ : syracuseStep 1793665 = 1345249) B1345249
theorem B2514635 : Blo 992597 2514635 := bstep (se 1 (by rfl) ⟨1885976, by rfl⟩ : syracuseStep 2514635 = 3771953) B3771953
theorem B18177857 : Blo 992597 18177857 := bstep (se 2 (by rfl) ⟨6816696, by rfl⟩ : syracuseStep 18177857 = 13633393) B13633393
theorem B4251665 : Blo 992597 4251665 := bstep (se 2 (by rfl) ⟨1594374, by rfl⟩ : syracuseStep 4251665 = 3188749) B3188749
theorem B19095587 : Blo 992597 19095587 := bstep (se 1 (by rfl) ⟨14321690, by rfl⟩ : syracuseStep 19095587 = 28643381) B28643381
theorem B2515009 : Blo 992597 2515009 := bstep (se 2 (by rfl) ⟨943128, by rfl⟩ : syracuseStep 2515009 = 1886257) B1886257
theorem B1794163 : Blo 992597 1794163 := bstep (se 1 (by rfl) ⟨1345622, by rfl⟩ : syracuseStep 1794163 = 2691245) B2691245
theorem B5038685 : Blo 992597 5038685 := bstep (se 3 (by rfl) ⟨944753, by rfl⟩ : syracuseStep 5038685 = 1889507) B1889507
theorem B2515607 : Blo 992597 2515607 := bstep (se 1 (by rfl) ⟨1886705, by rfl⟩ : syracuseStep 2515607 = 3773411) B3773411
theorem B2155187 : Blo 992597 2155187 := bstep (se 1 (by rfl) ⟨1616390, by rfl⟩ : syracuseStep 2155187 = 3232781) B3232781
theorem B1794739 : Blo 992597 1794739 := bstep (se 1 (by rfl) ⟨1346054, by rfl⟩ : syracuseStep 1794739 = 2692109) B2692109
theorem B2122433 : Blo 992597 2122433 := bstep (se 2 (by rfl) ⟨795912, by rfl⟩ : syracuseStep 2122433 = 1591825) B1591825
theorem B1794955 : Blo 992597 1794955 := bstep (se 1 (by rfl) ⟨1346216, by rfl⟩ : syracuseStep 1794955 = 2692433) B2692433
theorem B1008811 : Blo 992597 1008811 := bstep (se 1 (by rfl) ⟨756608, by rfl⟩ : syracuseStep 1008811 = 1513217) B1513217
theorem B5367001 : Blo 992597 5367001 := bstep (se 2 (by rfl) ⟨2012625, by rfl⟩ : syracuseStep 5367001 = 4025251) B4025251
theorem B4252931 : Blo 992597 4252931 := bstep (se 1 (by rfl) ⟨3189698, by rfl⟩ : syracuseStep 4252931 = 6379397) B6379397
theorem B7169381 : Blo 992597 7169381 := bstep (se 4 (by rfl) ⟨672129, by rfl⟩ : syracuseStep 7169381 = 1344259) B1344259
theorem B2516417 : Blo 992597 2516417 := bstep (se 2 (by rfl) ⟨943656, by rfl⟩ : syracuseStep 2516417 = 1887313) B1887313
theorem B1795763 : Blo 992597 1795763 := bstep (se 1 (by rfl) ⟨1346822, by rfl⟩ : syracuseStep 1795763 = 2693645) B2693645
theorem B2123543 : Blo 992597 2123543 := bstep (se 1 (by rfl) ⟨1592657, by rfl⟩ : syracuseStep 2123543 = 3185315) B3185315
theorem B7268131 : Blo 992597 7268131 := bstep (se 1 (by rfl) ⟨5451098, by rfl⟩ : syracuseStep 7268131 = 10902197) B10902197
theorem B2516953 : Blo 992597 2516953 := bstep (se 2 (by rfl) ⟨943857, by rfl⟩ : syracuseStep 2516953 = 1887715) B1887715
theorem B5368385 : Blo 992597 5368385 := bstep (se 2 (by rfl) ⟨2013144, by rfl⟩ : syracuseStep 5368385 = 4026289) B4026289
theorem B5040791 : Blo 992597 5040791 := bstep (se 1 (by rfl) ⟨3780593, by rfl⟩ : syracuseStep 5040791 = 7561187) B7561187
theorem B2124569 : Blo 992597 2124569 := bstep (se 2 (by rfl) ⟨796713, by rfl⟩ : syracuseStep 2124569 = 1593427) B1593427
theorem B2386739 : Blo 992597 2386739 := bstep (se 1 (by rfl) ⟨1790054, by rfl⟩ : syracuseStep 2386739 = 3580109) B3580109
theorem B2911193 : Blo 992597 2911193 := bstep (se 2 (by rfl) ⟨1091697, by rfl⟩ : syracuseStep 2911193 = 2183395) B2183395
theorem B20671523 : Blo 992597 20671523 := bstep (se 1 (by rfl) ⟨15503642, by rfl⟩ : syracuseStep 20671523 = 31007285) B31007285
theorem B2518067 : Blo 992597 2518067 := bstep (se 1 (by rfl) ⟨1888550, by rfl⟩ : syracuseStep 2518067 = 3777101) B3777101
theorem B2387123 : Blo 992597 2387123 := bstep (se 1 (by rfl) ⟨1790342, by rfl⟩ : syracuseStep 2387123 = 3580685) B3580685
theorem B7564589 : Blo 992597 7564589 := bstep (se 3 (by rfl) ⟨1418360, by rfl⟩ : syracuseStep 7564589 = 2836721) B2836721
theorem B4025675 : Blo 992597 4025675 := bstep (se 1 (by rfl) ⟨3019256, by rfl⟩ : syracuseStep 4025675 = 6038513) B6038513
theorem B2518361 : Blo 992597 2518361 := bstep (se 2 (by rfl) ⟨944385, by rfl⟩ : syracuseStep 2518361 = 1888771) B1888771
theorem B4779415 : Blo 992597 4779415 := bstep (se 1 (by rfl) ⟨3584561, by rfl⟩ : syracuseStep 4779415 = 7169123) B7169123
theorem B17198723 : Blo 992597 17198723 := bstep (se 1 (by rfl) ⟨12899042, by rfl⟩ : syracuseStep 17198723 = 25798085) B25798085
theorem B3632813 : Blo 992597 3632813 := bstep (se 3 (by rfl) ⟨681152, by rfl⟩ : syracuseStep 3632813 = 1362305) B1362305
theorem B1699735 : Blo 992597 1699735 := bstep (se 1 (by rfl) ⟨1274801, by rfl⟩ : syracuseStep 1699735 = 2549603) B2549603
theorem B2551769 : Blo 992597 2551769 := bstep (se 2 (by rfl) ⟨956913, by rfl⟩ : syracuseStep 2551769 = 1913827) B1913827
theorem B2420939 : Blo 992597 2420939 := bstep (se 1 (by rfl) ⟨1815704, by rfl⟩ : syracuseStep 2420939 = 3631409) B3631409
theorem B4256023 : Blo 992597 4256023 := bstep (se 1 (by rfl) ⟨3192017, by rfl⟩ : syracuseStep 4256023 = 6384035) B6384035
theorem B2126209 : Blo 992597 2126209 := bstep (se 2 (by rfl) ⟨797328, by rfl⟩ : syracuseStep 2126209 = 1594657) B1594657
theorem B5665241 : Blo 992597 5665241 := bstep (se 2 (by rfl) ⟨2124465, by rfl⟩ : syracuseStep 5665241 = 4248931) B4248931
theorem B2683415 : Blo 992597 2683415 := bstep (se 1 (by rfl) ⟨2012561, by rfl⟩ : syracuseStep 2683415 = 4025123) B4025123
theorem B7172813 : Blo 992597 7172813 := bstep (se 3 (by rfl) ⟨1344902, by rfl⟩ : syracuseStep 7172813 = 2689805) B2689805
theorem B1078039 : Blo 992597 1078039 := bstep (se 1 (by rfl) ⟨808529, by rfl⟩ : syracuseStep 1078039 = 1617059) B1617059
theorem B4027315 : Blo 992597 4027315 := bstep (se 1 (by rfl) ⟨3020486, by rfl⟩ : syracuseStep 4027315 = 6040973) B6040973
theorem B2520011 : Blo 992597 2520011 := bstep (se 1 (by rfl) ⟨1890008, by rfl⟩ : syracuseStep 2520011 = 3780017) B3780017
theorem B2126807 : Blo 992597 2126807 := bstep (se 1 (by rfl) ⟨1595105, by rfl⟩ : syracuseStep 2126807 = 3190211) B3190211
theorem B6911041 : Blo 992597 6911041 := bstep (se 2 (by rfl) ⟨2591640, by rfl⟩ : syracuseStep 6911041 = 5183281) B5183281
theorem B4846979 : Blo 992597 4846979 := bstep (se 1 (by rfl) ⟨3635234, by rfl⟩ : syracuseStep 4846979 = 7270469) B7270469
theorem B2520983 : Blo 992597 2520983 := bstep (se 1 (by rfl) ⟨1890737, by rfl⟩ : syracuseStep 2520983 = 3781475) B3781475
theorem B2127883 : Blo 992597 2127883 := bstep (se 1 (by rfl) ⟨1595912, by rfl⟩ : syracuseStep 2127883 = 3191825) B3191825
theorem B5666881 : Blo 992597 5666881 := bstep (se 2 (by rfl) ⟨2125080, by rfl⟩ : syracuseStep 5666881 = 4250161) B4250161
theorem B5044355 : Blo 992597 5044355 := bstep (se 1 (by rfl) ⟨3783266, by rfl⟩ : syracuseStep 5044355 = 7566533) B7566533
theorem B2390323 : Blo 992597 2390323 := bstep (se 1 (by rfl) ⟨1792742, by rfl⟩ : syracuseStep 2390323 = 3585485) B3585485
theorem B2521651 : Blo 992597 2521651 := bstep (se 1 (by rfl) ⟨1891238, by rfl⟩ : syracuseStep 2521651 = 3782477) B3782477
theorem B6453911 : Blo 992597 6453911 := bstep (se 1 (by rfl) ⟨4840433, by rfl⟩ : syracuseStep 6453911 = 9680867) B9680867
theorem B2521793 : Blo 992597 2521793 := bstep (se 2 (by rfl) ⟨945672, by rfl⟩ : syracuseStep 2521793 = 1891345) B1891345
theorem B8190725 : Blo 992597 8190725 := bstep (se 4 (by rfl) ⟨767880, by rfl⟩ : syracuseStep 8190725 = 1535761) B1535761
theorem B6060845 : Blo 992597 6060845 := bstep (se 3 (by rfl) ⟨1136408, by rfl⟩ : syracuseStep 6060845 = 2272817) B2272817
theorem B5373229 : Blo 992597 5373229 := bstep (se 3 (by rfl) ⟨1007480, by rfl⟩ : syracuseStep 5373229 = 2014961) B2014961
theorem B1703627 : Blo 992597 1703627 := bstep (se 1 (by rfl) ⟨1277720, by rfl⟩ : syracuseStep 1703627 = 2555441) B2555441
theorem B7667531 : Blo 992597 7667531 := bstep (se 1 (by rfl) ⟨5750648, by rfl⟩ : syracuseStep 7667531 = 11501297) B11501297
theorem B2392217 : Blo 992597 2392217 := bstep (se 2 (by rfl) ⟨897081, by rfl⟩ : syracuseStep 2392217 = 1794163) B1794163
theorem B6455837 : Blo 992597 6455837 := bstep (se 3 (by rfl) ⟨1210469, by rfl⟩ : syracuseStep 6455837 = 2420939) B2420939
theorem B4981421 : Blo 992597 4981421 := bstep (se 3 (by rfl) ⟨934016, by rfl⟩ : syracuseStep 4981421 = 1868033) B1868033
theorem B1344271 : Blo 992597 1344271 := bstep (se 1 (by rfl) ⟨1008203, by rfl⟩ : syracuseStep 1344271 = 2016407) B2016407
theorem B5374835 : Blo 992597 5374835 := bstep (se 1 (by rfl) ⟨4031126, by rfl⟩ : syracuseStep 5374835 = 8062253) B8062253
theorem B2392985 : Blo 992597 2392985 := bstep (se 2 (by rfl) ⟨897369, by rfl⟩ : syracuseStep 2392985 = 1794739) B1794739
theorem B3769355 : Blo 992597 3769355 := bstep (se 1 (by rfl) ⟨2827016, by rfl⟩ : syracuseStep 3769355 = 5654033) B5654033
theorem B2393273 : Blo 992597 2393273 := bstep (se 2 (by rfl) ⟨897477, by rfl⟩ : syracuseStep 2393273 = 1794955) B1794955
theorem B1345081 : Blo 992597 1345081 := bstep (se 2 (by rfl) ⟨504405, by rfl⟩ : syracuseStep 1345081 = 1008811) B1008811
theorem B11306789 : Blo 992597 11306789 := bstep (se 4 (by rfl) ⟨1060011, by rfl⟩ : syracuseStep 11306789 = 2120023) B2120023
theorem B1509239 : Blo 992597 1509239 := bstep (se 1 (by rfl) ⟨1131929, by rfl⟩ : syracuseStep 1509239 = 2263859) B2263859
theorem B3770297 : Blo 992597 3770297 := bstep (se 2 (by rfl) ⟨1413861, by rfl⟩ : syracuseStep 3770297 = 2827723) B2827723
theorem B4786199 : Blo 992597 4786199 := bstep (se 1 (by rfl) ⟨3589649, by rfl⟩ : syracuseStep 4786199 = 7179299) B7179299
theorem B9570707 : Blo 992597 9570707 := bstep (se 1 (by rfl) ⟨7178030, by rfl⟩ : syracuseStep 9570707 = 14356061) B14356061
theorem B1116679 : Blo 992597 1116679 := bstep (se 1 (by rfl) ⟨837509, by rfl⟩ : syracuseStep 1116679 = 1675019) B1675019
theorem B1116859 : Blo 992597 1116859 := bstep (se 1 (by rfl) ⟨837644, by rfl⟩ : syracuseStep 1116859 = 1675289) B1675289
theorem B3640249 : Blo 992597 3640249 := bstep (se 2 (by rfl) ⟨1365093, by rfl⟩ : syracuseStep 3640249 = 2730187) B2730187
theorem B1117327 : Blo 992597 1117327 := bstep (se 1 (by rfl) ⟨837995, by rfl⟩ : syracuseStep 1117327 = 1675991) B1675991
theorem B1117831 : Blo 992597 1117831 := bstep (se 1 (by rfl) ⟨838373, by rfl⟩ : syracuseStep 1117831 = 1676747) B1676747
theorem B1118011 : Blo 992597 1118011 := bstep (se 1 (by rfl) ⟨838508, by rfl⟩ : syracuseStep 1118011 = 1677017) B1677017
theorem B1675127 : Blo 992597 1675127 := bstep (se 1 (by rfl) ⟨1256345, by rfl⟩ : syracuseStep 1675127 = 2512691) B2512691
theorem B9572363 : Blo 992597 9572363 := bstep (se 1 (by rfl) ⟨7179272, by rfl⟩ : syracuseStep 9572363 = 14358545) B14358545
theorem B4493431 : Blo 992597 4493431 := bstep (se 1 (by rfl) ⟨3370073, by rfl⟩ : syracuseStep 4493431 = 6740147) B6740147
theorem B24875209 : Blo 992597 24875209 := bstep (se 2 (by rfl) ⟨9328203, by rfl⟩ : syracuseStep 24875209 = 18656407) B18656407
theorem B1118479 : Blo 992597 1118479 := bstep (se 1 (by rfl) ⟨838859, by rfl⟩ : syracuseStep 1118479 = 1677719) B1677719
theorem B1675579 : Blo 992597 1675579 := bstep (se 1 (by rfl) ⟨1256684, by rfl⟩ : syracuseStep 1675579 = 2513369) B2513369
theorem B1675721 : Blo 992597 1675721 := bstep (se 2 (by rfl) ⟨628395, by rfl⟩ : syracuseStep 1675721 = 1256791) B1256791
theorem B3772939 : Blo 992597 3772939 := bstep (se 1 (by rfl) ⟨2829704, by rfl⟩ : syracuseStep 3772939 = 5659409) B5659409
theorem B2691719 : Blo 992597 2691719 := bstep (se 1 (by rfl) ⟨2018789, by rfl⟩ : syracuseStep 2691719 = 4037579) B4037579
theorem B1118983 : Blo 992597 1118983 := bstep (se 1 (by rfl) ⟨839237, by rfl⟩ : syracuseStep 1118983 = 1678475) B1678475
theorem B4789007 : Blo 992597 4789007 := bstep (se 1 (by rfl) ⟨3591755, by rfl⟩ : syracuseStep 4789007 = 7183511) B7183511
theorem B13603619 : Blo 992597 13603619 := bstep (se 1 (by rfl) ⟨10202714, by rfl⟩ : syracuseStep 13603619 = 20405429) B20405429
theorem B3773243 : Blo 992597 3773243 := bstep (se 1 (by rfl) ⟨2829932, by rfl⟩ : syracuseStep 3773243 = 5659865) B5659865
theorem B1119163 : Blo 992597 1119163 := bstep (se 1 (by rfl) ⟨839372, by rfl⟩ : syracuseStep 1119163 = 1678745) B1678745
theorem B1414135 : Blo 992597 1414135 := bstep (se 1 (by rfl) ⟨1060601, by rfl⟩ : syracuseStep 1414135 = 2121203) B2121203
theorem B2233403 : Blo 992597 2233403 := bstep (se 1 (by rfl) ⟨1675052, by rfl⟩ : syracuseStep 2233403 = 3350105) B3350105
theorem B1676423 : Blo 992597 1676423 := bstep (se 1 (by rfl) ⟨1257317, by rfl⟩ : syracuseStep 1676423 = 2514635) B2514635
theorem B1512583 : Blo 992597 1512583 := bstep (se 1 (by rfl) ⟨1134437, by rfl⟩ : syracuseStep 1512583 = 2268875) B2268875
theorem B2233529 : Blo 992597 2233529 := bstep (se 2 (by rfl) ⟨837573, by rfl⟩ : syracuseStep 2233529 = 1675147) B1675147
theorem B2266313 : Blo 992597 2266313 := bstep (se 2 (by rfl) ⟨849867, by rfl⟩ : syracuseStep 2266313 = 1699735) B1699735
theorem B3773729 : Blo 992597 3773729 := bstep (se 2 (by rfl) ⟨1415148, by rfl⟩ : syracuseStep 3773729 = 2830297) B2830297
theorem B21501217 : Blo 992597 21501217 := bstep (se 2 (by rfl) ⟨8062956, by rfl⟩ : syracuseStep 21501217 = 16125913) B16125913
theorem B11343239 : Blo 992597 11343239 := bstep (se 1 (by rfl) ⟨8507429, by rfl⟩ : syracuseStep 11343239 = 17014859) B17014859
theorem B1119631 : Blo 992597 1119631 := bstep (se 1 (by rfl) ⟨839723, by rfl⟩ : syracuseStep 1119631 = 1679447) B1679447
theorem B2233871 : Blo 992597 2233871 := bstep (se 1 (by rfl) ⟨1675403, by rfl⟩ : syracuseStep 2233871 = 3350807) B3350807
theorem B2233889 : Blo 992597 2233889 := bstep (se 2 (by rfl) ⟨837708, by rfl⟩ : syracuseStep 2233889 = 1675417) B1675417
theorem B5674697 : Blo 992597 5674697 := bstep (se 2 (by rfl) ⟨2128011, by rfl⟩ : syracuseStep 5674697 = 4256023) B4256023
theorem B1677071 : Blo 992597 1677071 := bstep (se 1 (by rfl) ⟨1257803, by rfl⟩ : syracuseStep 1677071 = 2515607) B2515607
theorem B5740321 : Blo 992597 5740321 := bstep (se 2 (by rfl) ⟨2152620, by rfl⟩ : syracuseStep 5740321 = 4305241) B4305241
theorem B1414955 : Blo 992597 1414955 := bstep (se 1 (by rfl) ⟨1061216, by rfl⟩ : syracuseStep 1414955 = 2122433) B2122433
theorem B2234231 : Blo 992597 2234231 := bstep (se 1 (by rfl) ⟨1675673, by rfl⟩ : syracuseStep 2234231 = 3351347) B3351347
theorem B1120135 : Blo 992597 1120135 := bstep (se 1 (by rfl) ⟨840101, by rfl⟩ : syracuseStep 1120135 = 1680203) B1680203
theorem B2234411 : Blo 992597 2234411 := bstep (se 1 (by rfl) ⟨1675808, by rfl⟩ : syracuseStep 2234411 = 3351617) B3351617
theorem B1120315 : Blo 992597 1120315 := bstep (se 1 (by rfl) ⟨840236, by rfl⟩ : syracuseStep 1120315 = 1680473) B1680473
theorem B2693321 : Blo 992597 2693321 := bstep (se 2 (by rfl) ⟨1009995, by rfl⟩ : syracuseStep 2693321 = 2019991) B2019991
theorem B3774701 : Blo 992597 3774701 := bstep (se 3 (by rfl) ⟨707756, by rfl⟩ : syracuseStep 3774701 = 1415513) B1415513
theorem B1677611 : Blo 992597 1677611 := bstep (se 1 (by rfl) ⟨1258208, by rfl⟩ : syracuseStep 1677611 = 2516417) B2516417
theorem B2234771 : Blo 992597 2234771 := bstep (se 1 (by rfl) ⟨1676078, by rfl⟩ : syracuseStep 2234771 = 3352157) B3352157
theorem B2234825 : Blo 992597 2234825 := bstep (se 2 (by rfl) ⟨838059, by rfl⟩ : syracuseStep 2234825 = 1676119) B1676119
theorem B1120783 : Blo 992597 1120783 := bstep (se 1 (by rfl) ⟨840587, by rfl⟩ : syracuseStep 1120783 = 1681175) B1681175
theorem B1678009 : Blo 992597 1678009 := bstep (se 2 (by rfl) ⟨629253, by rfl⟩ : syracuseStep 1678009 = 1258507) B1258507
theorem B8493761 : Blo 992597 8493761 := bstep (se 2 (by rfl) ⟨3185160, by rfl⟩ : syracuseStep 8493761 = 6370321) B6370321
theorem B9214721 : Blo 992597 9214721 := bstep (se 2 (by rfl) ⟨3455520, by rfl⟩ : syracuseStep 9214721 = 6911041) B6911041
theorem B3578923 : Blo 992597 3578923 := bstep (se 1 (by rfl) ⟨2684192, by rfl⟩ : syracuseStep 3578923 = 5368385) B5368385
theorem B3185725 : Blo 992597 3185725 := bstep (se 3 (by rfl) ⟨597323, by rfl⟩ : syracuseStep 3185725 = 1194647) B1194647
theorem B3021911 : Blo 992597 3021911 := bstep (se 1 (by rfl) ⟨2266433, by rfl⟩ : syracuseStep 3021911 = 4532867) B4532867
theorem B2235527 : Blo 992597 2235527 := bstep (se 1 (by rfl) ⟨1676645, by rfl⟩ : syracuseStep 2235527 = 3353291) B3353291
theorem B1416379 : Blo 992597 1416379 := bstep (se 1 (by rfl) ⟨1062284, by rfl⟩ : syracuseStep 1416379 = 2124569) B2124569
theorem B2235707 : Blo 992597 2235707 := bstep (se 1 (by rfl) ⟨1676780, by rfl⟩ : syracuseStep 2235707 = 3353561) B3353561
theorem B1940795 : Blo 992597 1940795 := bstep (se 1 (by rfl) ⟨1455596, by rfl⟩ : syracuseStep 1940795 = 2911193) B2911193
theorem B1678711 : Blo 992597 1678711 := bstep (se 1 (by rfl) ⟨1259033, by rfl⟩ : syracuseStep 1678711 = 2518067) B2518067
theorem B2235833 : Blo 992597 2235833 := bstep (se 2 (by rfl) ⟨838437, by rfl⟩ : syracuseStep 2235833 = 1676875) B1676875
theorem B2301385 : Blo 992597 2301385 := bstep (se 2 (by rfl) ⟨863019, by rfl⟩ : syracuseStep 2301385 = 1726039) B1726039
theorem B1678907 : Blo 992597 1678907 := bstep (se 1 (by rfl) ⟨1259180, by rfl⟩ : syracuseStep 1678907 = 2518361) B2518361
theorem B5447425 : Blo 992597 5447425 := bstep (se 2 (by rfl) ⟨2042784, by rfl⟩ : syracuseStep 5447425 = 4085569) B4085569
theorem B2236175 : Blo 992597 2236175 := bstep (se 1 (by rfl) ⟨1677131, by rfl⟩ : syracuseStep 2236175 = 3354263) B3354263
theorem B2236193 : Blo 992597 2236193 := bstep (se 2 (by rfl) ⟨838572, by rfl⟩ : syracuseStep 2236193 = 1677145) B1677145
theorem B2301755 : Blo 992597 2301755 := bstep (se 1 (by rfl) ⟨1726316, by rfl⟩ : syracuseStep 2301755 = 3452633) B3452633
theorem B1679305 : Blo 992597 1679305 := bstep (se 2 (by rfl) ⟨629739, by rfl⟩ : syracuseStep 1679305 = 1259479) B1259479
theorem B87367733 : Blo 992597 87367733 := bstep (se 5 (by rfl) ⟨4095362, by rfl⟩ : syracuseStep 87367733 = 8190725) B8190725
theorem B2236535 : Blo 992597 2236535 := bstep (se 1 (by rfl) ⟨1677401, by rfl⟩ : syracuseStep 2236535 = 3354803) B3354803
theorem B2236715 : Blo 992597 2236715 := bstep (se 1 (by rfl) ⟨1677536, by rfl⟩ : syracuseStep 2236715 = 3355073) B3355073
theorem B3776827 : Blo 992597 3776827 := bstep (se 1 (by rfl) ⟨2832620, by rfl⟩ : syracuseStep 3776827 = 5665241) B5665241
theorem B3187097 : Blo 992597 3187097 := bstep (se 2 (by rfl) ⟨1195161, by rfl⟩ : syracuseStep 3187097 = 2390323) B2390323
theorem B3350969 : Blo 992597 3350969 := bstep (se 2 (by rfl) ⟨1256613, by rfl⟩ : syracuseStep 3350969 = 2513227) B2513227
theorem B1680007 : Blo 992597 1680007 := bstep (se 1 (by rfl) ⟨1260005, by rfl⟩ : syracuseStep 1680007 = 2520011) B2520011
theorem B1417871 : Blo 992597 1417871 := bstep (se 1 (by rfl) ⟨1063403, by rfl⟩ : syracuseStep 1417871 = 2126807) B2126807
theorem B2237075 : Blo 992597 2237075 := bstep (se 1 (by rfl) ⟨1677806, by rfl⟩ : syracuseStep 2237075 = 3355613) B3355613
theorem B2237129 : Blo 992597 2237129 := bstep (se 2 (by rfl) ⟨838923, by rfl⟩ : syracuseStep 2237129 = 1677847) B1677847
theorem B3777313 : Blo 992597 3777313 := bstep (se 2 (by rfl) ⟨1416492, by rfl⟩ : syracuseStep 3777313 = 2832985) B2832985
theorem B8069939 : Blo 992597 8069939 := bstep (se 1 (by rfl) ⟨6052454, by rfl⟩ : syracuseStep 8069939 = 12104909) B12104909
theorem B3351563 : Blo 992597 3351563 := bstep (se 1 (by rfl) ⟨2513672, by rfl⟩ : syracuseStep 3351563 = 5027345) B5027345
theorem B2827325 : Blo 992597 2827325 := bstep (se 3 (by rfl) ⟨530123, by rfl⟩ : syracuseStep 2827325 = 1060247) B1060247
theorem B3351671 : Blo 992597 3351671 := bstep (se 1 (by rfl) ⟨2513753, by rfl⟩ : syracuseStep 3351671 = 5027507) B5027507
theorem B1680655 : Blo 992597 1680655 := bstep (se 1 (by rfl) ⟨1260491, by rfl⟩ : syracuseStep 1680655 = 2520983) B2520983
theorem B992647 : Blo 992597 992647 := bstep (se 1 (by rfl) ⟨744485, by rfl⟩ : syracuseStep 992647 = 1488971) B1488971
theorem B2827655 : Blo 992597 2827655 := bstep (se 1 (by rfl) ⟨2120741, by rfl⟩ : syracuseStep 2827655 = 4241483) B4241483
theorem B2237831 : Blo 992597 2237831 := bstep (se 1 (by rfl) ⟨1678373, by rfl⟩ : syracuseStep 2237831 = 3356747) B3356747
theorem B992655 : Blo 992597 992655 := bstep (se 1 (by rfl) ⟨744491, by rfl⟩ : syracuseStep 992655 = 1488983) B1488983
theorem B992699 : Blo 992597 992699 := bstep (se 1 (by rfl) ⟨744524, by rfl⟩ : syracuseStep 992699 = 1489049) B1489049
theorem B992775 : Blo 992597 992775 := bstep (se 1 (by rfl) ⟨744581, by rfl⟩ : syracuseStep 992775 = 1489163) B1489163
theorem B992783 : Blo 992597 992783 := bstep (se 1 (by rfl) ⟨744587, by rfl⟩ : syracuseStep 992783 = 1489175) B1489175
theorem B992827 : Blo 992597 992827 := bstep (se 1 (by rfl) ⟨744620, by rfl⟩ : syracuseStep 992827 = 1489241) B1489241
theorem B2238011 : Blo 992597 2238011 := bstep (se 1 (by rfl) ⟨1678508, by rfl⟩ : syracuseStep 2238011 = 3357017) B3357017
theorem B992903 : Blo 992597 992903 := bstep (se 1 (by rfl) ⟨744677, by rfl⟩ : syracuseStep 992903 = 1489355) B1489355
theorem B992911 : Blo 992597 992911 := bstep (se 1 (by rfl) ⟨744683, by rfl⟩ : syracuseStep 992911 = 1489367) B1489367
theorem B2238137 : Blo 992597 2238137 := bstep (se 2 (by rfl) ⟨839301, by rfl⟩ : syracuseStep 2238137 = 1678603) B1678603
theorem B992955 : Blo 992597 992955 := bstep (se 1 (by rfl) ⟨744716, by rfl⟩ : syracuseStep 992955 = 1489433) B1489433
theorem B3352265 : Blo 992597 3352265 := bstep (se 2 (by rfl) ⟨1257099, by rfl⟩ : syracuseStep 3352265 = 2514199) B2514199
theorem B4531913 : Blo 992597 4531913 := bstep (se 2 (by rfl) ⟨1699467, by rfl⟩ : syracuseStep 4531913 = 3398935) B3398935
theorem B1418953 : Blo 992597 1418953 := bstep (se 2 (by rfl) ⟨532107, by rfl⟩ : syracuseStep 1418953 = 1064215) B1064215
theorem B3778285 : Blo 992597 3778285 := bstep (se 3 (by rfl) ⟨708428, by rfl⟩ : syracuseStep 3778285 = 1416857) B1416857
theorem B993031 : Blo 992597 993031 := bstep (se 1 (by rfl) ⟨744773, by rfl⟩ : syracuseStep 993031 = 1489547) B1489547
theorem B993039 : Blo 992597 993039 := bstep (se 1 (by rfl) ⟨744779, by rfl⟩ : syracuseStep 993039 = 1489559) B1489559
theorem B4302607 : Blo 992597 4302607 := bstep (se 1 (by rfl) ⟨3226955, by rfl⟩ : syracuseStep 4302607 = 6453911) B6453911
theorem B1681195 : Blo 992597 1681195 := bstep (se 1 (by rfl) ⟨1260896, by rfl⟩ : syracuseStep 1681195 = 2521793) B2521793
theorem B993083 : Blo 992597 993083 := bstep (se 1 (by rfl) ⟨744812, by rfl⟩ : syracuseStep 993083 = 1489625) B1489625
theorem B4040563 : Blo 992597 4040563 := bstep (se 1 (by rfl) ⟨3030422, by rfl⟩ : syracuseStep 4040563 = 6060845) B6060845
theorem B993159 : Blo 992597 993159 := bstep (se 1 (by rfl) ⟨744869, by rfl⟩ : syracuseStep 993159 = 1489739) B1489739
theorem B993167 : Blo 992597 993167 := bstep (se 1 (by rfl) ⟨744875, by rfl⟩ : syracuseStep 993167 = 1489751) B1489751
theorem B1681337 : Blo 992597 1681337 := bstep (se 2 (by rfl) ⟨630501, by rfl⟩ : syracuseStep 1681337 = 1261003) B1261003
theorem B993211 : Blo 992597 993211 := bstep (se 1 (by rfl) ⟨744908, by rfl⟩ : syracuseStep 993211 = 1489817) B1489817
theorem B993287 : Blo 992597 993287 := bstep (se 1 (by rfl) ⟨744965, by rfl⟩ : syracuseStep 993287 = 1489931) B1489931
theorem B993295 : Blo 992597 993295 := bstep (se 1 (by rfl) ⟨744971, by rfl⟩ : syracuseStep 993295 = 1489943) B1489943
theorem B2238479 : Blo 992597 2238479 := bstep (se 1 (by rfl) ⟨1678859, by rfl⟩ : syracuseStep 2238479 = 3357719) B3357719
theorem B3778589 : Blo 992597 3778589 := bstep (se 3 (by rfl) ⟨708485, by rfl⟩ : syracuseStep 3778589 = 1416971) B1416971
theorem B2238497 : Blo 992597 2238497 := bstep (se 2 (by rfl) ⟨839436, by rfl⟩ : syracuseStep 2238497 = 1678873) B1678873
theorem B993339 : Blo 992597 993339 := bstep (se 1 (by rfl) ⟨745004, by rfl⟩ : syracuseStep 993339 = 1490009) B1490009
theorem B993415 : Blo 992597 993415 := bstep (se 1 (by rfl) ⟨745061, by rfl⟩ : syracuseStep 993415 = 1490123) B1490123
theorem B993423 : Blo 992597 993423 := bstep (se 1 (by rfl) ⟨745067, by rfl⟩ : syracuseStep 993423 = 1490135) B1490135
theorem B993467 : Blo 992597 993467 := bstep (se 1 (by rfl) ⟨745100, by rfl⟩ : syracuseStep 993467 = 1490201) B1490201
theorem B993543 : Blo 992597 993543 := bstep (se 1 (by rfl) ⟨745157, by rfl⟩ : syracuseStep 993543 = 1490315) B1490315
theorem B993551 : Blo 992597 993551 := bstep (se 1 (by rfl) ⟨745163, by rfl⟩ : syracuseStep 993551 = 1490327) B1490327
theorem B993595 : Blo 992597 993595 := bstep (se 1 (by rfl) ⟨745196, by rfl⟩ : syracuseStep 993595 = 1490393) B1490393
theorem B2238839 : Blo 992597 2238839 := bstep (se 1 (by rfl) ⟨1679129, by rfl⟩ : syracuseStep 2238839 = 3358259) B3358259
theorem B3352967 : Blo 992597 3352967 := bstep (se 1 (by rfl) ⟨2514725, by rfl⟩ : syracuseStep 3352967 = 5029451) B5029451
theorem B993671 : Blo 992597 993671 := bstep (se 1 (by rfl) ⟨745253, by rfl⟩ : syracuseStep 993671 = 1490507) B1490507
theorem B993679 : Blo 992597 993679 := bstep (se 1 (by rfl) ⟨745259, by rfl⟩ : syracuseStep 993679 = 1490519) B1490519
theorem B993723 : Blo 992597 993723 := bstep (se 1 (by rfl) ⟨745292, by rfl⟩ : syracuseStep 993723 = 1490585) B1490585
theorem B6040067 : Blo 992597 6040067 := bstep (se 1 (by rfl) ⟨4530050, by rfl⟩ : syracuseStep 6040067 = 9060101) B9060101
theorem B993799 : Blo 992597 993799 := bstep (se 1 (by rfl) ⟨745349, by rfl⟩ : syracuseStep 993799 = 1490699) B1490699
theorem B993807 : Blo 992597 993807 := bstep (se 1 (by rfl) ⟨745355, by rfl⟩ : syracuseStep 993807 = 1490711) B1490711
theorem B2239019 : Blo 992597 2239019 := bstep (se 1 (by rfl) ⟨1679264, by rfl⟩ : syracuseStep 2239019 = 3358529) B3358529
theorem B993851 : Blo 992597 993851 := bstep (se 1 (by rfl) ⟨745388, by rfl⟩ : syracuseStep 993851 = 1490777) B1490777
theorem B993927 : Blo 992597 993927 := bstep (se 1 (by rfl) ⟨745445, by rfl⟩ : syracuseStep 993927 = 1490891) B1490891
theorem B993935 : Blo 992597 993935 := bstep (se 1 (by rfl) ⟨745451, by rfl⟩ : syracuseStep 993935 = 1490903) B1490903
theorem B3025555 : Blo 992597 3025555 := bstep (se 1 (by rfl) ⟨2269166, by rfl⟩ : syracuseStep 3025555 = 4538333) B4538333
theorem B993979 : Blo 992597 993979 := bstep (se 1 (by rfl) ⟨745484, by rfl⟩ : syracuseStep 993979 = 1490969) B1490969
theorem B3353345 : Blo 992597 3353345 := bstep (se 2 (by rfl) ⟨1257504, by rfl⟩ : syracuseStep 3353345 = 2515009) B2515009
theorem B994055 : Blo 992597 994055 := bstep (se 1 (by rfl) ⟨745541, by rfl⟩ : syracuseStep 994055 = 1491083) B1491083
theorem B994063 : Blo 992597 994063 := bstep (se 1 (by rfl) ⟨745547, by rfl⟩ : syracuseStep 994063 = 1491095) B1491095
theorem B9186085 : Blo 992597 9186085 := bstep (se 4 (by rfl) ⟨861195, by rfl⟩ : syracuseStep 9186085 = 1722391) B1722391
theorem B994107 : Blo 992597 994107 := bstep (se 1 (by rfl) ⟨745580, by rfl⟩ : syracuseStep 994107 = 1491161) B1491161
theorem B994183 : Blo 992597 994183 := bstep (se 1 (by rfl) ⟨745637, by rfl⟩ : syracuseStep 994183 = 1491275) B1491275
theorem B994191 : Blo 992597 994191 := bstep (se 1 (by rfl) ⟨745643, by rfl⟩ : syracuseStep 994191 = 1491287) B1491287
theorem B2239379 : Blo 992597 2239379 := bstep (se 1 (by rfl) ⟨1679534, by rfl⟩ : syracuseStep 2239379 = 3359069) B3359069
theorem B994235 : Blo 992597 994235 := bstep (se 1 (by rfl) ⟨745676, by rfl⟩ : syracuseStep 994235 = 1491353) B1491353
theorem B2239433 : Blo 992597 2239433 := bstep (se 2 (by rfl) ⟨839787, by rfl⟩ : syracuseStep 2239433 = 1679575) B1679575
theorem B994311 : Blo 992597 994311 := bstep (se 1 (by rfl) ⟨745733, by rfl⟩ : syracuseStep 994311 = 1491467) B1491467
theorem B994319 : Blo 992597 994319 := bstep (se 1 (by rfl) ⟨745739, by rfl⟩ : syracuseStep 994319 = 1491479) B1491479
theorem B994363 : Blo 992597 994363 := bstep (se 1 (by rfl) ⟨745772, by rfl⟩ : syracuseStep 994363 = 1491545) B1491545
theorem B2829431 : Blo 992597 2829431 := bstep (se 1 (by rfl) ⟨2122073, by rfl⟩ : syracuseStep 2829431 = 4244147) B4244147
theorem B994439 : Blo 992597 994439 := bstep (se 1 (by rfl) ⟨745829, by rfl⟩ : syracuseStep 994439 = 1491659) B1491659
theorem B994447 : Blo 992597 994447 := bstep (se 1 (by rfl) ⟨745835, by rfl⟩ : syracuseStep 994447 = 1491671) B1491671
theorem B994491 : Blo 992597 994491 := bstep (se 1 (by rfl) ⟨745868, by rfl⟩ : syracuseStep 994491 = 1491737) B1491737
theorem B994567 : Blo 992597 994567 := bstep (se 1 (by rfl) ⟨745925, by rfl⟩ : syracuseStep 994567 = 1491851) B1491851
theorem B994575 : Blo 992597 994575 := bstep (se 1 (by rfl) ⟨745931, by rfl⟩ : syracuseStep 994575 = 1491863) B1491863
theorem B994619 : Blo 992597 994619 := bstep (se 1 (by rfl) ⟨745964, by rfl⟩ : syracuseStep 994619 = 1491929) B1491929
theorem B994695 : Blo 992597 994695 := bstep (se 1 (by rfl) ⟨746021, by rfl⟩ : syracuseStep 994695 = 1492043) B1492043
theorem B994703 : Blo 992597 994703 := bstep (se 1 (by rfl) ⟨746027, by rfl⟩ : syracuseStep 994703 = 1492055) B1492055
theorem B994747 : Blo 992597 994747 := bstep (se 1 (by rfl) ⟨746060, by rfl⟩ : syracuseStep 994747 = 1492121) B1492121
theorem B994823 : Blo 992597 994823 := bstep (se 1 (by rfl) ⟨746117, by rfl⟩ : syracuseStep 994823 = 1492235) B1492235
theorem B994831 : Blo 992597 994831 := bstep (se 1 (by rfl) ⟨746123, by rfl⟩ : syracuseStep 994831 = 1492247) B1492247
theorem B3354155 : Blo 992597 3354155 := bstep (se 1 (by rfl) ⟨2515616, by rfl⟩ : syracuseStep 3354155 = 5031233) B5031233
theorem B994875 : Blo 992597 994875 := bstep (se 1 (by rfl) ⟨746156, by rfl⟩ : syracuseStep 994875 = 1492313) B1492313
theorem B3780215 : Blo 992597 3780215 := bstep (se 1 (by rfl) ⟨2835161, by rfl⟩ : syracuseStep 3780215 = 5670323) B5670323
theorem B994951 : Blo 992597 994951 := bstep (se 1 (by rfl) ⟨746213, by rfl⟩ : syracuseStep 994951 = 1492427) B1492427
theorem B2240135 : Blo 992597 2240135 := bstep (se 1 (by rfl) ⟨1680101, by rfl⟩ : syracuseStep 2240135 = 3360203) B3360203
theorem B994959 : Blo 992597 994959 := bstep (se 1 (by rfl) ⟨746219, by rfl⟩ : syracuseStep 994959 = 1492439) B1492439
theorem B995003 : Blo 992597 995003 := bstep (se 1 (by rfl) ⟨746252, by rfl⟩ : syracuseStep 995003 = 1492505) B1492505
theorem B995079 : Blo 992597 995079 := bstep (se 1 (by rfl) ⟨746309, by rfl⟩ : syracuseStep 995079 = 1492619) B1492619
theorem B4534031 : Blo 992597 4534031 := bstep (se 1 (by rfl) ⟨3400523, by rfl⟩ : syracuseStep 4534031 = 6801047) B6801047
theorem B995087 : Blo 992597 995087 := bstep (se 1 (by rfl) ⟨746315, by rfl⟩ : syracuseStep 995087 = 1492631) B1492631
theorem B995131 : Blo 992597 995131 := bstep (se 1 (by rfl) ⟨746348, by rfl⟩ : syracuseStep 995131 = 1492697) B1492697
theorem B2240315 : Blo 992597 2240315 := bstep (se 1 (by rfl) ⟨1680236, by rfl⟩ : syracuseStep 2240315 = 3360473) B3360473
theorem B995207 : Blo 992597 995207 := bstep (se 1 (by rfl) ⟨746405, by rfl⟩ : syracuseStep 995207 = 1492811) B1492811
theorem B995215 : Blo 992597 995215 := bstep (se 1 (by rfl) ⟨746411, by rfl⟩ : syracuseStep 995215 = 1492823) B1492823
theorem B2240441 : Blo 992597 2240441 := bstep (se 2 (by rfl) ⟨840165, by rfl⟩ : syracuseStep 2240441 = 1680331) B1680331
theorem B995259 : Blo 992597 995259 := bstep (se 1 (by rfl) ⟨746444, by rfl⟩ : syracuseStep 995259 = 1492889) B1492889
theorem B3026945 : Blo 992597 3026945 := bstep (se 2 (by rfl) ⟨1135104, by rfl⟩ : syracuseStep 3026945 = 2270209) B2270209
theorem B995335 : Blo 992597 995335 := bstep (se 1 (by rfl) ⟨746501, by rfl⟩ : syracuseStep 995335 = 1493003) B1493003
theorem B995343 : Blo 992597 995343 := bstep (se 1 (by rfl) ⟨746507, by rfl⟩ : syracuseStep 995343 = 1493015) B1493015
theorem B995387 : Blo 992597 995387 := bstep (se 1 (by rfl) ⟨746540, by rfl⟩ : syracuseStep 995387 = 1493081) B1493081
theorem B7155773 : Blo 992597 7155773 := bstep (se 3 (by rfl) ⟨1341707, by rfl⟩ : syracuseStep 7155773 = 2683415) B2683415
theorem B2830423 : Blo 992597 2830423 := bstep (se 1 (by rfl) ⟨2122817, by rfl⟩ : syracuseStep 2830423 = 4245635) B4245635
theorem B995463 : Blo 992597 995463 := bstep (se 1 (by rfl) ⟨746597, by rfl⟩ : syracuseStep 995463 = 1493195) B1493195
theorem B995471 : Blo 992597 995471 := bstep (se 1 (by rfl) ⟨746603, by rfl⟩ : syracuseStep 995471 = 1493207) B1493207
theorem B995515 : Blo 992597 995515 := bstep (se 1 (by rfl) ⟨746636, by rfl⟩ : syracuseStep 995515 = 1493273) B1493273
theorem B5026049 : Blo 992597 5026049 := bstep (se 2 (by rfl) ⟨1884768, by rfl⟩ : syracuseStep 5026049 = 3769537) B3769537
theorem B995591 : Blo 992597 995591 := bstep (se 1 (by rfl) ⟨746693, by rfl⟩ : syracuseStep 995591 = 1493387) B1493387
theorem B995599 : Blo 992597 995599 := bstep (se 1 (by rfl) ⟨746699, by rfl⟩ : syracuseStep 995599 = 1493399) B1493399
theorem B2240783 : Blo 992597 2240783 := bstep (se 1 (by rfl) ⟨1680587, by rfl⟩ : syracuseStep 2240783 = 3361175) B3361175
theorem B7156001 : Blo 992597 7156001 := bstep (se 2 (by rfl) ⟨2683500, by rfl⟩ : syracuseStep 7156001 = 5367001) B5367001
theorem B2240801 : Blo 992597 2240801 := bstep (se 2 (by rfl) ⟨840300, by rfl⟩ : syracuseStep 2240801 = 1680601) B1680601
theorem B995643 : Blo 992597 995643 := bstep (se 1 (by rfl) ⟨746732, by rfl⟩ : syracuseStep 995643 = 1493465) B1493465
theorem B995719 : Blo 992597 995719 := bstep (se 1 (by rfl) ⟨746789, by rfl⟩ : syracuseStep 995719 = 1493579) B1493579
theorem B995727 : Blo 992597 995727 := bstep (se 1 (by rfl) ⟨746795, by rfl⟩ : syracuseStep 995727 = 1493591) B1493591
theorem B995771 : Blo 992597 995771 := bstep (se 1 (by rfl) ⟨746828, by rfl⟩ : syracuseStep 995771 = 1493657) B1493657
theorem B995847 : Blo 992597 995847 := bstep (se 1 (by rfl) ⟨746885, by rfl⟩ : syracuseStep 995847 = 1493771) B1493771
theorem B995855 : Blo 992597 995855 := bstep (se 1 (by rfl) ⟨746891, by rfl⟩ : syracuseStep 995855 = 1493783) B1493783
theorem B3191339 : Blo 992597 3191339 := bstep (se 1 (by rfl) ⟨2393504, by rfl⟩ : syracuseStep 3191339 = 4787009) B4787009
theorem B995899 : Blo 992597 995899 := bstep (se 1 (by rfl) ⟨746924, by rfl⟩ : syracuseStep 995899 = 1493849) B1493849
theorem B3781187 : Blo 992597 3781187 := bstep (se 1 (by rfl) ⟨2835890, by rfl⟩ : syracuseStep 3781187 = 5671781) B5671781
theorem B6369911 : Blo 992597 6369911 := bstep (se 1 (by rfl) ⟨4777433, by rfl⟩ : syracuseStep 6369911 = 9554867) B9554867
theorem B2241143 : Blo 992597 2241143 := bstep (se 1 (by rfl) ⟨1680857, by rfl⟩ : syracuseStep 2241143 = 3361715) B3361715
theorem B995975 : Blo 992597 995975 := bstep (se 1 (by rfl) ⟨746981, by rfl⟩ : syracuseStep 995975 = 1493963) B1493963
theorem B995983 : Blo 992597 995983 := bstep (se 1 (by rfl) ⟨746987, by rfl⟩ : syracuseStep 995983 = 1493975) B1493975
theorem B996027 : Blo 992597 996027 := bstep (se 1 (by rfl) ⟨747020, by rfl⟩ : syracuseStep 996027 = 1494041) B1494041
theorem B996103 : Blo 992597 996103 := bstep (se 1 (by rfl) ⟨747077, by rfl⟩ : syracuseStep 996103 = 1494155) B1494155
theorem B996111 : Blo 992597 996111 := bstep (se 1 (by rfl) ⟨747083, by rfl⟩ : syracuseStep 996111 = 1494167) B1494167
theorem B2241323 : Blo 992597 2241323 := bstep (se 1 (by rfl) ⟨1680992, by rfl⟩ : syracuseStep 2241323 = 3361985) B3361985
theorem B3355451 : Blo 992597 3355451 := bstep (se 1 (by rfl) ⟨2516588, by rfl⟩ : syracuseStep 3355451 = 5033177) B5033177
theorem B996155 : Blo 992597 996155 := bstep (se 1 (by rfl) ⟨747116, by rfl⟩ : syracuseStep 996155 = 1494233) B1494233
theorem B996231 : Blo 992597 996231 := bstep (se 1 (by rfl) ⟨747173, by rfl⟩ : syracuseStep 996231 = 1494347) B1494347
theorem B996239 : Blo 992597 996239 := bstep (se 1 (by rfl) ⟨747179, by rfl⟩ : syracuseStep 996239 = 1494359) B1494359
theorem B1258411 : Blo 992597 1258411 := bstep (se 1 (by rfl) ⟨943808, by rfl⟩ : syracuseStep 1258411 = 1887617) B1887617
theorem B996283 : Blo 992597 996283 := bstep (se 1 (by rfl) ⟨747212, by rfl⟩ : syracuseStep 996283 = 1494425) B1494425
theorem B996359 : Blo 992597 996359 := bstep (se 1 (by rfl) ⟨747269, by rfl⟩ : syracuseStep 996359 = 1494539) B1494539
theorem B996367 : Blo 992597 996367 := bstep (se 1 (by rfl) ⟨747275, by rfl⟩ : syracuseStep 996367 = 1494551) B1494551
theorem B5026859 : Blo 992597 5026859 := bstep (se 1 (by rfl) ⟨3770144, by rfl⟩ : syracuseStep 5026859 = 7540289) B7540289
theorem B996411 : Blo 992597 996411 := bstep (se 1 (by rfl) ⟨747308, by rfl⟩ : syracuseStep 996411 = 1494617) B1494617
theorem B36844631 : Blo 992597 36844631 := bstep (se 1 (by rfl) ⟨27633473, by rfl⟩ : syracuseStep 36844631 = 55266947) B55266947
theorem B996487 : Blo 992597 996487 := bstep (se 1 (by rfl) ⟨747365, by rfl⟩ : syracuseStep 996487 = 1494731) B1494731
theorem B996495 : Blo 992597 996495 := bstep (se 1 (by rfl) ⟨747371, by rfl⟩ : syracuseStep 996495 = 1494743) B1494743
theorem B2241683 : Blo 992597 2241683 := bstep (se 1 (by rfl) ⟨1681262, by rfl⟩ : syracuseStep 2241683 = 3362525) B3362525
theorem B996539 : Blo 992597 996539 := bstep (se 1 (by rfl) ⟨747404, by rfl⟩ : syracuseStep 996539 = 1494809) B1494809
theorem B2241737 : Blo 992597 2241737 := bstep (se 2 (by rfl) ⟨840651, by rfl⟩ : syracuseStep 2241737 = 1681303) B1681303
theorem B3355937 : Blo 992597 3355937 := bstep (se 2 (by rfl) ⟨1258476, by rfl⟩ : syracuseStep 3355937 = 2516953) B2516953
theorem B3782173 : Blo 992597 3782173 := bstep (se 3 (by rfl) ⟨709157, by rfl⟩ : syracuseStep 3782173 = 1418315) B1418315
theorem B2831915 : Blo 992597 2831915 := bstep (se 1 (by rfl) ⟨2123936, by rfl⟩ : syracuseStep 2831915 = 4247873) B4247873
theorem B9549413 : Blo 992597 9549413 := bstep (se 4 (by rfl) ⟨895257, by rfl⟩ : syracuseStep 9549413 = 1790515) B1790515
theorem B3356531 : Blo 992597 3356531 := bstep (se 1 (by rfl) ⟨2517398, by rfl⟩ : syracuseStep 3356531 = 5034797) B5034797
theorem B1259383 : Blo 992597 1259383 := bstep (se 1 (by rfl) ⟨944537, by rfl⟩ : syracuseStep 1259383 = 1889075) B1889075
theorem B2013113 : Blo 992597 2013113 := bstep (se 2 (by rfl) ⟨754917, by rfl⟩ : syracuseStep 2013113 = 1509835) B1509835
theorem B24524813 : Blo 992597 24524813 := bstep (se 3 (by rfl) ⟨4598402, by rfl⟩ : syracuseStep 24524813 = 9196805) B9196805
theorem B1488911 : Blo 992597 1488911 := bstep (se 1 (by rfl) ⟨1116683, by rfl⟩ : syracuseStep 1488911 = 2233367) B2233367
theorem B1488953 : Blo 992597 1488953 := bstep (se 2 (by rfl) ⟨558357, by rfl⟩ : syracuseStep 1488953 = 1116715) B1116715
theorem B1489031 : Blo 992597 1489031 := bstep (se 1 (by rfl) ⟨1116773, by rfl⟩ : syracuseStep 1489031 = 2233547) B2233547
theorem B1489067 : Blo 992597 1489067 := bstep (se 1 (by rfl) ⟨1116800, by rfl⟩ : syracuseStep 1489067 = 2233601) B2233601
theorem B1259707 : Blo 992597 1259707 := bstep (se 1 (by rfl) ⟨944780, by rfl⟩ : syracuseStep 1259707 = 1889561) B1889561
theorem B1489097 : Blo 992597 1489097 := bstep (se 2 (by rfl) ⟨558411, by rfl⟩ : syracuseStep 1489097 = 1116823) B1116823
theorem B7649569 : Blo 992597 7649569 := bstep (se 2 (by rfl) ⟨2868588, by rfl⟩ : syracuseStep 7649569 = 5737177) B5737177
theorem B1489211 : Blo 992597 1489211 := bstep (se 1 (by rfl) ⟨1116908, by rfl⟩ : syracuseStep 1489211 = 2233817) B2233817
theorem B5028155 : Blo 992597 5028155 := bstep (se 1 (by rfl) ⟨3771116, by rfl⟩ : syracuseStep 5028155 = 7542233) B7542233
theorem B12925277 : Blo 992597 12925277 := bstep (se 3 (by rfl) ⟨2423489, by rfl⟩ : syracuseStep 12925277 = 4846979) B4846979
theorem B1489271 : Blo 992597 1489271 := bstep (se 1 (by rfl) ⟨1116953, by rfl⟩ : syracuseStep 1489271 = 2233907) B2233907
theorem B1489295 : Blo 992597 1489295 := bstep (se 1 (by rfl) ⟨1116971, by rfl⟩ : syracuseStep 1489295 = 2233943) B2233943
theorem B1489337 : Blo 992597 1489337 := bstep (se 2 (by rfl) ⟨558501, by rfl⟩ : syracuseStep 1489337 = 1117003) B1117003
theorem B5028317 : Blo 992597 5028317 := bstep (se 3 (by rfl) ⟨942809, by rfl⟩ : syracuseStep 5028317 = 1885619) B1885619
theorem B1489415 : Blo 992597 1489415 := bstep (se 1 (by rfl) ⟨1117061, by rfl⟩ : syracuseStep 1489415 = 2234123) B2234123
theorem B1489451 : Blo 992597 1489451 := bstep (se 1 (by rfl) ⟨1117088, by rfl⟩ : syracuseStep 1489451 = 2234177) B2234177
theorem B1489481 : Blo 992597 1489481 := bstep (se 2 (by rfl) ⟨558555, by rfl⟩ : syracuseStep 1489481 = 1117111) B1117111
theorem B2833031 : Blo 992597 2833031 := bstep (se 1 (by rfl) ⟨2124773, by rfl⟩ : syracuseStep 2833031 = 4249547) B4249547
theorem B1489595 : Blo 992597 1489595 := bstep (se 1 (by rfl) ⟨1117196, by rfl⟩ : syracuseStep 1489595 = 2234393) B2234393
theorem B1489655 : Blo 992597 1489655 := bstep (se 1 (by rfl) ⟨1117241, by rfl⟩ : syracuseStep 1489655 = 2234483) B2234483
theorem B1194743 : Blo 992597 1194743 := bstep (se 1 (by rfl) ⟨896057, by rfl⟩ : syracuseStep 1194743 = 1792115) B1792115
theorem B1489679 : Blo 992597 1489679 := bstep (se 1 (by rfl) ⟨1117259, by rfl⟩ : syracuseStep 1489679 = 2234519) B2234519
theorem B5028641 : Blo 992597 5028641 := bstep (se 2 (by rfl) ⟨1885740, by rfl⟩ : syracuseStep 5028641 = 3771481) B3771481
theorem B5749541 : Blo 992597 5749541 := bstep (se 4 (by rfl) ⟨539019, by rfl⟩ : syracuseStep 5749541 = 1078039) B1078039
theorem B1489721 : Blo 992597 1489721 := bstep (se 2 (by rfl) ⟨558645, by rfl⟩ : syracuseStep 1489721 = 1117291) B1117291
theorem B2833213 : Blo 992597 2833213 := bstep (se 3 (by rfl) ⟨531227, by rfl⟩ : syracuseStep 2833213 = 1062455) B1062455
theorem B1489799 : Blo 992597 1489799 := bstep (se 1 (by rfl) ⟨1117349, by rfl⟩ : syracuseStep 1489799 = 2234699) B2234699
theorem B2014087 : Blo 992597 2014087 := bstep (se 1 (by rfl) ⟨1510565, by rfl⟩ : syracuseStep 2014087 = 3021131) B3021131
theorem B1489835 : Blo 992597 1489835 := bstep (se 1 (by rfl) ⟨1117376, by rfl⟩ : syracuseStep 1489835 = 2234753) B2234753
theorem B1489865 : Blo 992597 1489865 := bstep (se 2 (by rfl) ⟨558699, by rfl⟩ : syracuseStep 1489865 = 1117399) B1117399
theorem B9550871 : Blo 992597 9550871 := bstep (se 1 (by rfl) ⟨7163153, by rfl⟩ : syracuseStep 9550871 = 14326307) B14326307
theorem B1489979 : Blo 992597 1489979 := bstep (se 1 (by rfl) ⟨1117484, by rfl⟩ : syracuseStep 1489979 = 2234969) B2234969
theorem B1490039 : Blo 992597 1490039 := bstep (se 1 (by rfl) ⟨1117529, by rfl⟩ : syracuseStep 1490039 = 2235059) B2235059
theorem B1260679 : Blo 992597 1260679 := bstep (se 1 (by rfl) ⟨945509, by rfl⟩ : syracuseStep 1260679 = 1891019) B1891019
theorem B1490063 : Blo 992597 1490063 := bstep (se 1 (by rfl) ⟨1117547, by rfl⟩ : syracuseStep 1490063 = 2235095) B2235095
theorem B2833555 : Blo 992597 2833555 := bstep (se 1 (by rfl) ⟨2125166, by rfl⟩ : syracuseStep 2833555 = 4250333) B4250333
theorem B1490105 : Blo 992597 1490105 := bstep (se 2 (by rfl) ⟨558789, by rfl⟩ : syracuseStep 1490105 = 1117579) B1117579
theorem B6372553 : Blo 992597 6372553 := bstep (se 2 (by rfl) ⟨2389707, by rfl⟩ : syracuseStep 6372553 = 4779415) B4779415
theorem B8502509 : Blo 992597 8502509 := bstep (se 3 (by rfl) ⟨1594220, by rfl⟩ : syracuseStep 8502509 = 3188441) B3188441
theorem B1490183 : Blo 992597 1490183 := bstep (se 1 (by rfl) ⟨1117637, by rfl⟩ : syracuseStep 1490183 = 2235275) B2235275
theorem B7257377 : Blo 992597 7257377 := bstep (se 2 (by rfl) ⟨2721516, by rfl⟩ : syracuseStep 7257377 = 5443033) B5443033
theorem B1490219 : Blo 992597 1490219 := bstep (se 1 (by rfl) ⟨1117664, by rfl⟩ : syracuseStep 1490219 = 2235329) B2235329
theorem B4603195 : Blo 992597 4603195 := bstep (se 1 (by rfl) ⟨3452396, by rfl⟩ : syracuseStep 4603195 = 6904793) B6904793
theorem B1490249 : Blo 992597 1490249 := bstep (se 2 (by rfl) ⟨558843, by rfl⟩ : syracuseStep 1490249 = 1117687) B1117687
theorem B1490363 : Blo 992597 1490363 := bstep (se 1 (by rfl) ⟨1117772, by rfl⟩ : syracuseStep 1490363 = 2235545) B2235545
theorem B6045131 : Blo 992597 6045131 := bstep (se 1 (by rfl) ⟨4533848, by rfl⟩ : syracuseStep 6045131 = 9067697) B9067697
theorem B1490423 : Blo 992597 1490423 := bstep (se 1 (by rfl) ⟨1117817, by rfl⟩ : syracuseStep 1490423 = 2235635) B2235635
theorem B1490447 : Blo 992597 1490447 := bstep (se 1 (by rfl) ⟨1117835, by rfl⟩ : syracuseStep 1490447 = 2235671) B2235671
theorem B1261099 : Blo 992597 1261099 := bstep (se 1 (by rfl) ⟨945824, by rfl⟩ : syracuseStep 1261099 = 1891649) B1891649
theorem B1490489 : Blo 992597 1490489 := bstep (se 2 (by rfl) ⟨558933, by rfl⟩ : syracuseStep 1490489 = 1117867) B1117867
theorem B1490567 : Blo 992597 1490567 := bstep (se 1 (by rfl) ⟨1117925, by rfl⟩ : syracuseStep 1490567 = 2235851) B2235851
theorem B1490603 : Blo 992597 1490603 := bstep (se 1 (by rfl) ⟨1117952, by rfl⟩ : syracuseStep 1490603 = 2235905) B2235905
theorem B1490633 : Blo 992597 1490633 := bstep (se 2 (by rfl) ⟨558987, by rfl⟩ : syracuseStep 1490633 = 1117975) B1117975
theorem B5029613 : Blo 992597 5029613 := bstep (se 3 (by rfl) ⟨943052, by rfl⟩ : syracuseStep 5029613 = 1886105) B1886105
theorem B4243259 : Blo 992597 4243259 := bstep (se 1 (by rfl) ⟨3182444, by rfl⟩ : syracuseStep 4243259 = 6364889) B6364889
theorem B1490747 : Blo 992597 1490747 := bstep (se 1 (by rfl) ⟨1118060, by rfl⟩ : syracuseStep 1490747 = 2236121) B2236121
theorem B1490807 : Blo 992597 1490807 := bstep (se 1 (by rfl) ⟨1118105, by rfl⟩ : syracuseStep 1490807 = 2236211) B2236211
theorem B1490831 : Blo 992597 1490831 := bstep (se 1 (by rfl) ⟨1118123, by rfl⟩ : syracuseStep 1490831 = 2236247) B2236247
theorem B36224921 : Blo 992597 36224921 := bstep (se 2 (by rfl) ⟨13584345, by rfl⟩ : syracuseStep 36224921 = 27168691) B27168691
theorem B1490873 : Blo 992597 1490873 := bstep (se 2 (by rfl) ⟨559077, by rfl⟩ : syracuseStep 1490873 = 1118155) B1118155
theorem B1490951 : Blo 992597 1490951 := bstep (se 1 (by rfl) ⟨1118213, by rfl⟩ : syracuseStep 1490951 = 2236427) B2236427
theorem B2834443 : Blo 992597 2834443 := bstep (se 1 (by rfl) ⟨2125832, by rfl⟩ : syracuseStep 2834443 = 4251665) B4251665
theorem B12730391 : Blo 992597 12730391 := bstep (se 1 (by rfl) ⟨9547793, by rfl⟩ : syracuseStep 12730391 = 19095587) B19095587
theorem B4243499 : Blo 992597 4243499 := bstep (se 1 (by rfl) ⟨3182624, by rfl⟩ : syracuseStep 4243499 = 6365249) B6365249
theorem B1490987 : Blo 992597 1490987 := bstep (se 1 (by rfl) ⟨1118240, by rfl⟩ : syracuseStep 1490987 = 2236481) B2236481
theorem B1491017 : Blo 992597 1491017 := bstep (se 2 (by rfl) ⟨559131, by rfl⟩ : syracuseStep 1491017 = 1118263) B1118263
theorem B1491131 : Blo 992597 1491131 := bstep (se 1 (by rfl) ⟨1118348, by rfl⟩ : syracuseStep 1491131 = 2236697) B2236697
theorem B1491191 : Blo 992597 1491191 := bstep (se 1 (by rfl) ⟨1118393, by rfl⟩ : syracuseStep 1491191 = 2236787) B2236787
theorem B1491215 : Blo 992597 1491215 := bstep (se 1 (by rfl) ⟨1118411, by rfl⟩ : syracuseStep 1491215 = 2236823) B2236823
theorem B1491257 : Blo 992597 1491257 := bstep (se 2 (by rfl) ⟨559221, by rfl⟩ : syracuseStep 1491257 = 1118443) B1118443
theorem B1491335 : Blo 992597 1491335 := bstep (se 1 (by rfl) ⟨1118501, by rfl⟩ : syracuseStep 1491335 = 2237003) B2237003
theorem B4243859 : Blo 992597 4243859 := bstep (se 1 (by rfl) ⟨3182894, by rfl⟩ : syracuseStep 4243859 = 6365789) B6365789
theorem B3359123 : Blo 992597 3359123 := bstep (se 1 (by rfl) ⟨2519342, by rfl⟩ : syracuseStep 3359123 = 5038685) B5038685
theorem B1491371 : Blo 992597 1491371 := bstep (se 1 (by rfl) ⟨1118528, by rfl⟩ : syracuseStep 1491371 = 2237057) B2237057
theorem B1884617 : Blo 992597 1884617 := bstep (se 2 (by rfl) ⟨706731, by rfl⟩ : syracuseStep 1884617 = 1413463) B1413463
theorem B1491401 : Blo 992597 1491401 := bstep (se 2 (by rfl) ⟨559275, by rfl⟩ : syracuseStep 1491401 = 1118551) B1118551
theorem B2834945 : Blo 992597 2834945 := bstep (se 2 (by rfl) ⟨1063104, by rfl⟩ : syracuseStep 2834945 = 2126209) B2126209
theorem B5030423 : Blo 992597 5030423 := bstep (se 1 (by rfl) ⟨3772817, by rfl⟩ : syracuseStep 5030423 = 7545635) B7545635
theorem B1491515 : Blo 992597 1491515 := bstep (se 1 (by rfl) ⟨1118636, by rfl⟩ : syracuseStep 1491515 = 2237273) B2237273
theorem B1491575 : Blo 992597 1491575 := bstep (se 1 (by rfl) ⟨1118681, by rfl⟩ : syracuseStep 1491575 = 2237363) B2237363
theorem B3588727 : Blo 992597 3588727 := bstep (se 1 (by rfl) ⟨2691545, by rfl⟩ : syracuseStep 3588727 = 5383091) B5383091
theorem B17023607 : Blo 992597 17023607 := bstep (se 1 (by rfl) ⟨12767705, by rfl⟩ : syracuseStep 17023607 = 25535411) B25535411
theorem B1491599 : Blo 992597 1491599 := bstep (se 1 (by rfl) ⟨1118699, by rfl⟩ : syracuseStep 1491599 = 2237399) B2237399
theorem B1491641 : Blo 992597 1491641 := bstep (se 2 (by rfl) ⟨559365, by rfl⟩ : syracuseStep 1491641 = 1118731) B1118731
theorem B1491719 : Blo 992597 1491719 := bstep (se 1 (by rfl) ⟨1118789, by rfl⟩ : syracuseStep 1491719 = 2237579) B2237579
theorem B1491755 : Blo 992597 1491755 := bstep (se 1 (by rfl) ⟨1118816, by rfl⟩ : syracuseStep 1491755 = 2237633) B2237633
theorem B1491785 : Blo 992597 1491785 := bstep (se 2 (by rfl) ⟨559419, by rfl⟩ : syracuseStep 1491785 = 1118839) B1118839
theorem B2835287 : Blo 992597 2835287 := bstep (se 1 (by rfl) ⟨2126465, by rfl⟩ : syracuseStep 2835287 = 4252931) B4252931
theorem B30983093 : Blo 992597 30983093 := bstep (se 5 (by rfl) ⟨1452332, by rfl⟩ : syracuseStep 30983093 = 2904665) B2904665
theorem B1491899 : Blo 992597 1491899 := bstep (se 1 (by rfl) ⟨1118924, by rfl⟩ : syracuseStep 1491899 = 2237849) B2237849
theorem B1491959 : Blo 992597 1491959 := bstep (se 1 (by rfl) ⟨1118969, by rfl⟩ : syracuseStep 1491959 = 2237939) B2237939
theorem B1491983 : Blo 992597 1491983 := bstep (se 1 (by rfl) ⟨1118987, by rfl⟩ : syracuseStep 1491983 = 2237975) B2237975
theorem B1492025 : Blo 992597 1492025 := bstep (se 2 (by rfl) ⟨559509, by rfl⟩ : syracuseStep 1492025 = 1119019) B1119019
theorem B1197175 : Blo 992597 1197175 := bstep (se 1 (by rfl) ⟨897881, by rfl⟩ : syracuseStep 1197175 = 1795763) B1795763
theorem B1492103 : Blo 992597 1492103 := bstep (se 1 (by rfl) ⟨1119077, by rfl⟩ : syracuseStep 1492103 = 2238155) B2238155
theorem B1885331 : Blo 992597 1885331 := bstep (se 1 (by rfl) ⟨1413998, by rfl⟩ : syracuseStep 1885331 = 2827997) B2827997
theorem B1492139 : Blo 992597 1492139 := bstep (se 1 (by rfl) ⟨1119104, by rfl⟩ : syracuseStep 1492139 = 2238209) B2238209
theorem B1885369 : Blo 992597 1885369 := bstep (se 2 (by rfl) ⟨707013, by rfl⟩ : syracuseStep 1885369 = 1414027) B1414027
theorem B1590473 : Blo 992597 1590473 := bstep (se 2 (by rfl) ⟨596427, by rfl⟩ : syracuseStep 1590473 = 1192855) B1192855
theorem B1492169 : Blo 992597 1492169 := bstep (se 2 (by rfl) ⟨559563, by rfl⟩ : syracuseStep 1492169 = 1119127) B1119127
theorem B1492283 : Blo 992597 1492283 := bstep (se 1 (by rfl) ⟨1119212, by rfl⟩ : syracuseStep 1492283 = 2238425) B2238425
theorem B3065149 : Blo 992597 3065149 := bstep (se 3 (by rfl) ⟨574715, by rfl⟩ : syracuseStep 3065149 = 1149431) B1149431
theorem B1492343 : Blo 992597 1492343 := bstep (se 1 (by rfl) ⟨1119257, by rfl⟩ : syracuseStep 1492343 = 2238515) B2238515
theorem B1492367 : Blo 992597 1492367 := bstep (se 1 (by rfl) ⟨1119275, by rfl⟩ : syracuseStep 1492367 = 2238551) B2238551
theorem B1492409 : Blo 992597 1492409 := bstep (se 2 (by rfl) ⟨559653, by rfl⟩ : syracuseStep 1492409 = 1119307) B1119307
theorem B1492487 : Blo 992597 1492487 := bstep (se 1 (by rfl) ⟨1119365, by rfl⟩ : syracuseStep 1492487 = 2238731) B2238731
theorem B1492523 : Blo 992597 1492523 := bstep (se 1 (by rfl) ⟨1119392, by rfl⟩ : syracuseStep 1492523 = 2238785) B2238785
theorem B1492553 : Blo 992597 1492553 := bstep (se 2 (by rfl) ⟨559707, by rfl⟩ : syracuseStep 1492553 = 1119415) B1119415
theorem B1492667 : Blo 992597 1492667 := bstep (se 1 (by rfl) ⟨1119500, by rfl⟩ : syracuseStep 1492667 = 2239001) B2239001
theorem B1492727 : Blo 992597 1492727 := bstep (se 1 (by rfl) ⟨1119545, by rfl⟩ : syracuseStep 1492727 = 2239091) B2239091
theorem B1492751 : Blo 992597 1492751 := bstep (se 1 (by rfl) ⟨1119563, by rfl⟩ : syracuseStep 1492751 = 2239127) B2239127
theorem B3360527 : Blo 992597 3360527 := bstep (se 1 (by rfl) ⟨2520395, by rfl⟩ : syracuseStep 3360527 = 5040791) B5040791
theorem B1492793 : Blo 992597 1492793 := bstep (se 2 (by rfl) ⟨559797, by rfl⟩ : syracuseStep 1492793 = 1119595) B1119595
theorem B1591159 : Blo 992597 1591159 := bstep (se 1 (by rfl) ⟨1193369, by rfl⟩ : syracuseStep 1591159 = 2386739) B2386739
theorem B1492871 : Blo 992597 1492871 := bstep (se 1 (by rfl) ⟨1119653, by rfl⟩ : syracuseStep 1492871 = 2239307) B2239307
theorem B2869145 : Blo 992597 2869145 := bstep (se 2 (by rfl) ⟨1075929, by rfl⟩ : syracuseStep 2869145 = 2151859) B2151859
theorem B1492907 : Blo 992597 1492907 := bstep (se 1 (by rfl) ⟨1119680, by rfl⟩ : syracuseStep 1492907 = 2239361) B2239361
theorem B1492937 : Blo 992597 1492937 := bstep (se 2 (by rfl) ⟨559851, by rfl⟩ : syracuseStep 1492937 = 1119703) B1119703
theorem B13781015 : Blo 992597 13781015 := bstep (se 1 (by rfl) ⟨10335761, by rfl⟩ : syracuseStep 13781015 = 20671523) B20671523
theorem B3360797 : Blo 992597 3360797 := bstep (se 3 (by rfl) ⟨630149, by rfl⟩ : syracuseStep 3360797 = 1260299) B1260299
theorem B1493051 : Blo 992597 1493051 := bstep (se 1 (by rfl) ⟨1119788, by rfl⟩ : syracuseStep 1493051 = 2239577) B2239577
theorem B1591415 : Blo 992597 1591415 := bstep (se 1 (by rfl) ⟨1193561, by rfl⟩ : syracuseStep 1591415 = 2387123) B2387123
theorem B3065975 : Blo 992597 3065975 := bstep (se 1 (by rfl) ⟨2299481, by rfl⟩ : syracuseStep 3065975 = 4598963) B4598963
theorem B1493111 : Blo 992597 1493111 := bstep (se 1 (by rfl) ⟨1119833, by rfl⟩ : syracuseStep 1493111 = 2239667) B2239667
theorem B1493135 : Blo 992597 1493135 := bstep (se 1 (by rfl) ⟨1119851, by rfl⟩ : syracuseStep 1493135 = 2239703) B2239703
theorem B1493177 : Blo 992597 1493177 := bstep (se 2 (by rfl) ⟨559941, by rfl⟩ : syracuseStep 1493177 = 1119883) B1119883
theorem B1493255 : Blo 992597 1493255 := bstep (se 1 (by rfl) ⟨1119941, by rfl⟩ : syracuseStep 1493255 = 2239883) B2239883
theorem B1493291 : Blo 992597 1493291 := bstep (se 1 (by rfl) ⟨1119968, by rfl⟩ : syracuseStep 1493291 = 2239937) B2239937
theorem B1493321 : Blo 992597 1493321 := bstep (se 2 (by rfl) ⟨559995, by rfl⟩ : syracuseStep 1493321 = 1119991) B1119991
theorem B1493435 : Blo 992597 1493435 := bstep (se 1 (by rfl) ⟨1120076, by rfl⟩ : syracuseStep 1493435 = 2240153) B2240153
theorem B1493495 : Blo 992597 1493495 := bstep (se 1 (by rfl) ⟨1120121, by rfl⟩ : syracuseStep 1493495 = 2240243) B2240243
theorem B1493519 : Blo 992597 1493519 := bstep (se 1 (by rfl) ⟨1120139, by rfl⟩ : syracuseStep 1493519 = 2240279) B2240279
theorem B1493561 : Blo 992597 1493561 := bstep (se 2 (by rfl) ⟨560085, by rfl⟩ : syracuseStep 1493561 = 1120171) B1120171
theorem B12765761 : Blo 992597 12765761 := bstep (se 2 (by rfl) ⟨4787160, by rfl⟩ : syracuseStep 12765761 = 9574321) B9574321
theorem B1493639 : Blo 992597 1493639 := bstep (se 1 (by rfl) ⟨1120229, by rfl⟩ : syracuseStep 1493639 = 2240459) B2240459
theorem B1493675 : Blo 992597 1493675 := bstep (se 1 (by rfl) ⟨1120256, by rfl⟩ : syracuseStep 1493675 = 2240513) B2240513
theorem B2837177 : Blo 992597 2837177 := bstep (se 2 (by rfl) ⟨1063941, by rfl⟩ : syracuseStep 2837177 = 2127883) B2127883
theorem B1493705 : Blo 992597 1493705 := bstep (se 2 (by rfl) ⟨560139, by rfl⟩ : syracuseStep 1493705 = 1120279) B1120279
theorem B7555841 : Blo 992597 7555841 := bstep (se 2 (by rfl) ⟨2833440, by rfl⟩ : syracuseStep 7555841 = 5666881) B5666881
theorem B1493819 : Blo 992597 1493819 := bstep (se 1 (by rfl) ⟨1120364, by rfl⟩ : syracuseStep 1493819 = 2240729) B2240729
theorem B1493879 : Blo 992597 1493879 := bstep (se 1 (by rfl) ⟨1120409, by rfl⟩ : syracuseStep 1493879 = 2240819) B2240819
theorem B1493903 : Blo 992597 1493903 := bstep (se 1 (by rfl) ⟨1120427, by rfl⟩ : syracuseStep 1493903 = 2240855) B2240855
theorem B12438425 : Blo 992597 12438425 := bstep (se 2 (by rfl) ⟨4664409, by rfl⟩ : syracuseStep 12438425 = 9328819) B9328819
theorem B4311961 : Blo 992597 4311961 := bstep (se 2 (by rfl) ⟨1616985, by rfl⟩ : syracuseStep 4311961 = 3233971) B3233971
theorem B1493945 : Blo 992597 1493945 := bstep (se 2 (by rfl) ⟨560229, by rfl⟩ : syracuseStep 1493945 = 1120459) B1120459
theorem B24562693 : Blo 992597 24562693 := bstep (se 4 (by rfl) ⟨2302752, by rfl⟩ : syracuseStep 24562693 = 4605505) B4605505
theorem B1494023 : Blo 992597 1494023 := bstep (se 1 (by rfl) ⟨1120517, by rfl⟩ : syracuseStep 1494023 = 2241035) B2241035
theorem B1887275 : Blo 992597 1887275 := bstep (se 1 (by rfl) ⟨1415456, by rfl⟩ : syracuseStep 1887275 = 2830913) B2830913
theorem B1494059 : Blo 992597 1494059 := bstep (se 1 (by rfl) ⟨1120544, by rfl⟩ : syracuseStep 1494059 = 2241089) B2241089
theorem B1494089 : Blo 992597 1494089 := bstep (se 2 (by rfl) ⟨560283, by rfl⟩ : syracuseStep 1494089 = 1120567) B1120567
theorem B1494203 : Blo 992597 1494203 := bstep (se 1 (by rfl) ⟨1120652, by rfl⟩ : syracuseStep 1494203 = 2241305) B2241305
theorem B1494263 : Blo 992597 1494263 := bstep (se 1 (by rfl) ⟨1120697, by rfl⟩ : syracuseStep 1494263 = 2241395) B2241395
theorem B1494287 : Blo 992597 1494287 := bstep (se 1 (by rfl) ⟨1120715, by rfl⟩ : syracuseStep 1494287 = 2241431) B2241431
theorem B1494329 : Blo 992597 1494329 := bstep (se 2 (by rfl) ⟨560373, by rfl⟩ : syracuseStep 1494329 = 1120747) B1120747
theorem B1494407 : Blo 992597 1494407 := bstep (se 1 (by rfl) ⟨1120805, by rfl⟩ : syracuseStep 1494407 = 2241611) B2241611
theorem B3362201 : Blo 992597 3362201 := bstep (se 2 (by rfl) ⟨1260825, by rfl⟩ : syracuseStep 3362201 = 2521651) B2521651
theorem B1494443 : Blo 992597 1494443 := bstep (se 1 (by rfl) ⟨1120832, by rfl⟩ : syracuseStep 1494443 = 2241665) B2241665
theorem B1494473 : Blo 992597 1494473 := bstep (se 2 (by rfl) ⟨560427, by rfl⟩ : syracuseStep 1494473 = 1120855) B1120855
theorem B8506883 : Blo 992597 8506883 := bstep (se 1 (by rfl) ⟨6380162, by rfl⟩ : syracuseStep 8506883 = 12760325) B12760325
theorem B5033501 : Blo 992597 5033501 := bstep (se 3 (by rfl) ⟨943781, by rfl⟩ : syracuseStep 5033501 = 1887563) B1887563
theorem B1494587 : Blo 992597 1494587 := bstep (se 1 (by rfl) ⟨1120940, by rfl⟩ : syracuseStep 1494587 = 2241881) B2241881
theorem B1494647 : Blo 992597 1494647 := bstep (se 1 (by rfl) ⟨1120985, by rfl⟩ : syracuseStep 1494647 = 2241971) B2241971
theorem B1494671 : Blo 992597 1494671 := bstep (se 1 (by rfl) ⟨1121003, by rfl⟩ : syracuseStep 1494671 = 2242007) B2242007
theorem B1593017 : Blo 992597 1593017 := bstep (se 2 (by rfl) ⟨597381, by rfl⟩ : syracuseStep 1593017 = 1194763) B1194763
theorem B1494713 : Blo 992597 1494713 := bstep (se 2 (by rfl) ⟨560517, by rfl⟩ : syracuseStep 1494713 = 1121035) B1121035
theorem B1494791 : Blo 992597 1494791 := bstep (se 1 (by rfl) ⟨1121093, by rfl⟩ : syracuseStep 1494791 = 2242187) B2242187
theorem B1494827 : Blo 992597 1494827 := bstep (se 1 (by rfl) ⟨1121120, by rfl⟩ : syracuseStep 1494827 = 2242241) B2242241
theorem B1494857 : Blo 992597 1494857 := bstep (se 2 (by rfl) ⟨560571, by rfl⟩ : syracuseStep 1494857 = 1121143) B1121143
theorem B1888201 : Blo 992597 1888201 := bstep (se 2 (by rfl) ⟨708075, by rfl⟩ : syracuseStep 1888201 = 1416151) B1416151
theorem B5033987 : Blo 992597 5033987 := bstep (se 1 (by rfl) ⟨3775490, by rfl⟩ : syracuseStep 5033987 = 7550981) B7550981
theorem B3362903 : Blo 992597 3362903 := bstep (se 1 (by rfl) ⟨2522177, by rfl⟩ : syracuseStep 3362903 = 5044355) B5044355
theorem B10735733 : Blo 992597 10735733 := bstep (se 5 (by rfl) ⟨503237, by rfl⟩ : syracuseStep 10735733 = 1006475) B1006475
theorem B7164305 : Blo 992597 7164305 := bstep (se 2 (by rfl) ⟨2686614, by rfl⟩ : syracuseStep 7164305 = 5373229) B5373229
theorem B3363389 : Blo 992597 3363389 := bstep (se 3 (by rfl) ⟨630635, by rfl⟩ : syracuseStep 3363389 = 1261271) B1261271
theorem B1888915 : Blo 992597 1888915 := bstep (se 1 (by rfl) ⟨1416686, by rfl⟩ : syracuseStep 1888915 = 2833373) B2833373
theorem B8049725 : Blo 992597 8049725 := bstep (se 3 (by rfl) ⟨1509323, by rfl⟩ : syracuseStep 8049725 = 3018647) B3018647
theorem B1135751 : Blo 992597 1135751 := bstep (se 1 (by rfl) ⟨851813, by rfl⟩ : syracuseStep 1135751 = 1703627) B1703627
theorem B4773437 : Blo 992597 4773437 := bstep (se 3 (by rfl) ⟨895019, by rfl⟩ : syracuseStep 4773437 = 1790039) B1790039
theorem B5035607 : Blo 992597 5035607 := bstep (se 1 (by rfl) ⟨3776705, by rfl⟩ : syracuseStep 5035607 = 7553411) B7553411
theorem B1889993 : Blo 992597 1889993 := bstep (se 2 (by rfl) ⟨708747, by rfl⟩ : syracuseStep 1889993 = 1417495) B1417495
theorem B1595195 : Blo 992597 1595195 := bstep (se 1 (by rfl) ⟨1196396, by rfl⟩ : syracuseStep 1595195 = 2392793) B2392793
theorem B5036093 : Blo 992597 5036093 := bstep (se 3 (by rfl) ⟨944267, by rfl⟩ : syracuseStep 5036093 = 1888535) B1888535
theorem B2513015 : Blo 992597 2513015 := bstep (se 1 (by rfl) ⟨1884761, by rfl⟩ : syracuseStep 2513015 = 3769523) B3769523
theorem B4544903 : Blo 992597 4544903 := bstep (se 1 (by rfl) ⟨3408677, by rfl⟩ : syracuseStep 4544903 = 6817355) B6817355
theorem B4250009 : Blo 992597 4250009 := bstep (se 2 (by rfl) ⟨1593753, by rfl⟩ : syracuseStep 4250009 = 3187507) B3187507
theorem B12769757 : Blo 992597 12769757 := bstep (se 3 (by rfl) ⟨2394329, by rfl⟩ : syracuseStep 12769757 = 4788659) B4788659
theorem B9558557 : Blo 992597 9558557 := bstep (se 3 (by rfl) ⟨1792229, by rfl⟩ : syracuseStep 9558557 = 3584459) B3584459
theorem B1890859 : Blo 992597 1890859 := bstep (se 1 (by rfl) ⟨1418144, by rfl⟩ : syracuseStep 1890859 = 2836289) B2836289
theorem B4250231 : Blo 992597 4250231 := bstep (se 1 (by rfl) ⟨3187673, by rfl⟩ : syracuseStep 4250231 = 6375347) B6375347
theorem B1890935 : Blo 992597 1890935 := bstep (se 1 (by rfl) ⟨1418201, by rfl⟩ : syracuseStep 1890935 = 2836403) B2836403
theorem B4774859 : Blo 992597 4774859 := bstep (se 1 (by rfl) ⟨3581144, by rfl⟩ : syracuseStep 4774859 = 7162289) B7162289
theorem B7560215 : Blo 992597 7560215 := bstep (se 1 (by rfl) ⟨5670161, by rfl⟩ : syracuseStep 7560215 = 11340323) B11340323
theorem B3103879 : Blo 992597 3103879 := bstep (se 1 (by rfl) ⟨2327909, by rfl⟩ : syracuseStep 3103879 = 4655819) B4655819
theorem B19127501 : Blo 992597 19127501 := bstep (se 3 (by rfl) ⟨3586406, by rfl⟩ : syracuseStep 19127501 = 7172813) B7172813
theorem B2514311 : Blo 992597 2514311 := bstep (se 1 (by rfl) ⟨1885733, by rfl⟩ : syracuseStep 2514311 = 3771467) B3771467
theorem B2514361 : Blo 992597 2514361 := bstep (se 2 (by rfl) ⟨942885, by rfl⟩ : syracuseStep 2514361 = 1885771) B1885771
theorem B61136477 : Blo 992597 61136477 := bstep (se 3 (by rfl) ⟨11463089, by rfl⟩ : syracuseStep 61136477 = 22926179) B22926179
theorem B9690841 : Blo 992597 9690841 := bstep (se 2 (by rfl) ⟨3634065, by rfl⟩ : syracuseStep 9690841 = 7268131) B7268131
theorem B5037875 : Blo 992597 5037875 := bstep (se 1 (by rfl) ⟨3778406, by rfl⟩ : syracuseStep 5037875 = 7556813) B7556813
theorem B24207173 : Blo 992597 24207173 := bstep (se 4 (by rfl) ⟨2269422, by rfl⟩ : syracuseStep 24207173 = 4538845) B4538845
theorem B12083107 : Blo 992597 12083107 := bstep (se 1 (by rfl) ⟨9062330, by rfl⟩ : syracuseStep 12083107 = 18124661) B18124661
theorem B2514959 : Blo 992597 2514959 := bstep (se 1 (by rfl) ⟨1886219, by rfl⟩ : syracuseStep 2514959 = 3772439) B3772439
theorem B5038199 : Blo 992597 5038199 := bstep (se 1 (by rfl) ⟨3778649, by rfl⟩ : syracuseStep 5038199 = 7557299) B7557299
theorem B4252247 : Blo 992597 4252247 := bstep (se 1 (by rfl) ⟨3189185, by rfl⟩ : syracuseStep 4252247 = 6378371) B6378371
theorem B2515657 : Blo 992597 2515657 := bstep (se 2 (by rfl) ⟨943371, by rfl⟩ : syracuseStep 2515657 = 1886743) B1886743
theorem B2515799 : Blo 992597 2515799 := bstep (se 1 (by rfl) ⟨1886849, by rfl⟩ : syracuseStep 2515799 = 3773699) B3773699
theorem B5661575 : Blo 992597 5661575 := bstep (se 1 (by rfl) ⟨4246181, by rfl⟩ : syracuseStep 5661575 = 8492363) B8492363
theorem B10216343 : Blo 992597 10216343 := bstep (se 1 (by rfl) ⟨7662257, by rfl⟩ : syracuseStep 10216343 = 15324515) B15324515
theorem B2122681 : Blo 992597 2122681 := bstep (se 2 (by rfl) ⟨796005, by rfl⟩ : syracuseStep 2122681 = 1592011) B1592011
theorem B4842499 : Blo 992597 4842499 := bstep (se 1 (by rfl) ⟨3631874, by rfl⟩ : syracuseStep 4842499 = 7263749) B7263749
theorem B5039171 : Blo 992597 5039171 := bstep (se 1 (by rfl) ⟨3779378, by rfl⟩ : syracuseStep 5039171 = 7558757) B7558757
theorem B2123023 : Blo 992597 2123023 := bstep (se 1 (by rfl) ⟨1592267, by rfl⟩ : syracuseStep 2123023 = 3184535) B3184535
theorem B5039495 : Blo 992597 5039495 := bstep (se 1 (by rfl) ⟨3779621, by rfl⟩ : syracuseStep 5039495 = 7559243) B7559243
theorem B6383033 : Blo 992597 6383033 := bstep (se 2 (by rfl) ⟨2393637, by rfl⟩ : syracuseStep 6383033 = 4787275) B4787275
theorem B11494865 : Blo 992597 11494865 := bstep (se 2 (by rfl) ⟨4310574, by rfl⟩ : syracuseStep 11494865 = 8621149) B8621149
theorem B2418191 : Blo 992597 2418191 := bstep (se 1 (by rfl) ⟨1813643, by rfl⟩ : syracuseStep 2418191 = 3627287) B3627287
theorem B5662781 : Blo 992597 5662781 := bstep (se 3 (by rfl) ⟨1061771, by rfl⟩ : syracuseStep 5662781 = 2123543) B2123543
theorem B2123911 : Blo 992597 2123911 := bstep (se 1 (by rfl) ⟨1592933, by rfl⟩ : syracuseStep 2123911 = 3185867) B3185867
theorem B4778185 : Blo 992597 4778185 := bstep (se 2 (by rfl) ⟨1791819, by rfl⟩ : syracuseStep 4778185 = 3583639) B3583639
theorem B2386219 : Blo 992597 2386219 := bstep (se 1 (by rfl) ⟨1789664, by rfl⟩ : syracuseStep 2386219 = 3579329) B3579329
theorem B7662109 : Blo 992597 7662109 := bstep (se 3 (by rfl) ⟨1436645, by rfl⟩ : syracuseStep 7662109 = 2873291) B2873291
theorem B12118571 : Blo 992597 12118571 := bstep (se 1 (by rfl) ⟨9088928, by rfl⟩ : syracuseStep 12118571 = 18177857) B18177857
theorem B2517875 : Blo 992597 2517875 := bstep (se 1 (by rfl) ⟨1888406, by rfl⟩ : syracuseStep 2517875 = 3776813) B3776813
theorem B1436791 : Blo 992597 1436791 := bstep (se 1 (by rfl) ⟨1077593, by rfl⟩ : syracuseStep 1436791 = 2155187) B2155187
theorem B1535095 : Blo 992597 1535095 := bstep (se 1 (by rfl) ⟨1151321, by rfl⟩ : syracuseStep 1535095 = 2302643) B2302643
theorem B2518391 : Blo 992597 2518391 := bstep (se 1 (by rfl) ⟨1888793, by rfl⟩ : syracuseStep 2518391 = 3777587) B3777587
theorem B4779587 : Blo 992597 4779587 := bstep (se 1 (by rfl) ⟨3584690, by rfl⟩ : syracuseStep 4779587 = 7169381) B7169381
theorem B3632897 : Blo 992597 3632897 := bstep (se 2 (by rfl) ⟨1362336, by rfl⟩ : syracuseStep 3632897 = 2724673) B2724673
theorem B5369753 : Blo 992597 5369753 := bstep (se 2 (by rfl) ⟨2013657, by rfl⟩ : syracuseStep 5369753 = 4027315) B4027315
theorem B2125867 : Blo 992597 2125867 := bstep (se 1 (by rfl) ⟨1594400, by rfl⟩ : syracuseStep 2125867 = 3188801) B3188801
theorem B3633353 : Blo 992597 3633353 := bstep (se 2 (by rfl) ⟨1362507, by rfl⟩ : syracuseStep 3633353 = 2725015) B2725015
theorem B2519383 : Blo 992597 2519383 := bstep (se 1 (by rfl) ⟨1889537, by rfl⟩ : syracuseStep 2519383 = 3779075) B3779075
theorem B4780433 : Blo 992597 4780433 := bstep (se 2 (by rfl) ⟨1792662, by rfl⟩ : syracuseStep 4780433 = 3585325) B3585325
theorem B2388371 : Blo 992597 2388371 := bstep (se 1 (by rfl) ⟨1791278, by rfl⟩ : syracuseStep 2388371 = 3582557) B3582557
theorem B4026809 : Blo 992597 4026809 := bstep (se 2 (by rfl) ⟨1510053, by rfl⟩ : syracuseStep 4026809 = 3020107) B3020107
theorem B2388409 : Blo 992597 2388409 := bstep (se 2 (by rfl) ⟨895653, by rfl⟩ : syracuseStep 2388409 = 1791307) B1791307
theorem B4026941 : Blo 992597 4026941 := bstep (se 3 (by rfl) ⟨755051, by rfl⟩ : syracuseStep 4026941 = 1510103) B1510103
theorem B2519687 : Blo 992597 2519687 := bstep (se 1 (by rfl) ⟨1889765, by rfl⟩ : syracuseStep 2519687 = 3779531) B3779531
theorem B2519819 : Blo 992597 2519819 := bstep (se 1 (by rfl) ⟨1889864, by rfl⟩ : syracuseStep 2519819 = 3779729) B3779729
theorem B12743513 : Blo 992597 12743513 := bstep (se 2 (by rfl) ⟨4778817, by rfl⟩ : syracuseStep 12743513 = 9557635) B9557635
theorem B5043059 : Blo 992597 5043059 := bstep (se 1 (by rfl) ⟨3782294, by rfl⟩ : syracuseStep 5043059 = 7564589) B7564589
theorem B2683783 : Blo 992597 2683783 := bstep (se 1 (by rfl) ⟨2012837, by rfl⟩ : syracuseStep 2683783 = 4025675) B4025675
theorem B11465815 : Blo 992597 11465815 := bstep (se 1 (by rfl) ⟨8599361, by rfl⟩ : syracuseStep 11465815 = 17198723) B17198723
theorem B2421875 : Blo 992597 2421875 := bstep (se 1 (by rfl) ⟨1816406, by rfl⟩ : syracuseStep 2421875 = 3632813) B3632813
theorem B2520335 : Blo 992597 2520335 := bstep (se 1 (by rfl) ⟨1890251, by rfl⟩ : syracuseStep 2520335 = 3780503) B3780503
theorem B1701179 : Blo 992597 1701179 := bstep (se 1 (by rfl) ⟨1275884, by rfl⟩ : syracuseStep 1701179 = 2551769) B2551769
theorem B5043545 : Blo 992597 5043545 := bstep (se 2 (by rfl) ⟨1891329, by rfl⟩ : syracuseStep 5043545 = 3782659) B3782659
theorem B2520467 : Blo 992597 2520467 := bstep (se 1 (by rfl) ⟨1890350, by rfl⟩ : syracuseStep 2520467 = 3780701) B3780701
theorem B6650333 : Blo 992597 6650333 := bstep (se 3 (by rfl) ⟨1246937, by rfl⟩ : syracuseStep 6650333 = 2493875) B2493875
theorem B2521601 : Blo 992597 2521601 := bstep (se 2 (by rfl) ⟨945600, by rfl⟩ : syracuseStep 2521601 = 1891201) B1891201
theorem B2521975 : Blo 992597 2521975 := bstep (se 1 (by rfl) ⟨1891481, by rfl⟩ : syracuseStep 2521975 = 3782963) B3782963
theorem B2522411 : Blo 992597 2522411 := bstep (se 1 (by rfl) ⟨1891808, by rfl⟩ : syracuseStep 2522411 = 3783617) B3783617
theorem B2391553 : Blo 992597 2391553 := bstep (se 2 (by rfl) ⟨896832, by rfl⟩ : syracuseStep 2391553 = 1793665) B1793665
theorem B1343351 : Blo 992597 1343351 := bstep (se 1 (by rfl) ⟨1007513, by rfl⟩ : syracuseStep 1343351 = 2015027) B2015027
theorem B5111687 : Blo 992597 5111687 := bstep (se 1 (by rfl) ⟨3833765, by rfl⟩ : syracuseStep 5111687 = 7667531) B7667531
theorem B8486927 : Blo 992597 8486927 := bstep (se 1 (by rfl) ⟨6365195, by rfl⟩ : syracuseStep 8486927 = 12730391) B12730391
theorem B4784969 : Blo 992597 4784969 := bstep (se 2 (by rfl) ⟨1794363, by rfl⟩ : syracuseStep 4784969 = 3588727) B3588727
theorem B7537859 : Blo 992597 7537859 := bstep (se 1 (by rfl) ⟨5653394, by rfl⟩ : syracuseStep 7537859 = 11306789) B11306789
theorem B6456665 : Blo 992597 6456665 := bstep (se 2 (by rfl) ⟨2421249, by rfl⟩ : syracuseStep 6456665 = 4842499) B4842499
theorem B40797701 : Blo 992597 40797701 := bstep (se 4 (by rfl) ⟨3824784, by rfl⟩ : syracuseStep 40797701 = 7649569) B7649569
theorem B5671255 : Blo 992597 5671255 := bstep (se 1 (by rfl) ⟨4253441, by rfl⟩ : syracuseStep 5671255 = 8506883) B8506883
theorem B5736809 : Blo 992597 5736809 := bstep (se 2 (by rfl) ⟨2151303, by rfl⟩ : syracuseStep 5736809 = 4302607) B4302607
theorem B1116751 : Blo 992597 1116751 := bstep (se 1 (by rfl) ⟨837563, by rfl⟩ : syracuseStep 1116751 = 1675127) B1675127
theorem B1117147 : Blo 992597 1117147 := bstep (se 1 (by rfl) ⟨837860, by rfl⟩ : syracuseStep 1117147 = 1675721) B1675721
theorem B3181625 : Blo 992597 3181625 := bstep (se 2 (by rfl) ⟨1193109, by rfl⟩ : syracuseStep 3181625 = 2386219) B2386219
theorem B1117615 : Blo 992597 1117615 := bstep (se 1 (by rfl) ⟨838211, by rfl⟩ : syracuseStep 1117615 = 1676423) B1676423
theorem B3182291 : Blo 992597 3182291 := bstep (se 1 (by rfl) ⟨2386718, by rfl⟩ : syracuseStep 3182291 = 4773437) B4773437
theorem B1118047 : Blo 992597 1118047 := bstep (se 1 (by rfl) ⟨838535, by rfl⟩ : syracuseStep 1118047 = 1677071) B1677071
theorem B4853665 : Blo 992597 4853665 := bstep (se 2 (by rfl) ⟨1820124, by rfl⟩ : syracuseStep 4853665 = 3640249) B3640249
theorem B1675343 : Blo 992597 1675343 := bstep (se 1 (by rfl) ⟨1256507, by rfl⟩ : syracuseStep 1675343 = 2513015) B2513015
theorem B1118407 : Blo 992597 1118407 := bstep (se 1 (by rfl) ⟨838805, by rfl⟩ : syracuseStep 1118407 = 1677611) B1677611
theorem B3183239 : Blo 992597 3183239 := bstep (se 1 (by rfl) ⟨2387429, by rfl⟩ : syracuseStep 3183239 = 4774859) B4774859
theorem B3773213 : Blo 992597 3773213 := bstep (se 3 (by rfl) ⟨707477, by rfl⟩ : syracuseStep 3773213 = 1414955) B1414955
theorem B12751667 : Blo 992597 12751667 := bstep (se 1 (by rfl) ⟨9563750, by rfl⟩ : syracuseStep 12751667 = 19127501) B19127501
theorem B1676207 : Blo 992597 1676207 := bstep (se 1 (by rfl) ⟨1257155, by rfl⟩ : syracuseStep 1676207 = 2514311) B2514311
theorem B1119271 : Blo 992597 1119271 := bstep (se 1 (by rfl) ⟨839453, by rfl⟩ : syracuseStep 1119271 = 1678907) B1678907
theorem B1676639 : Blo 992597 1676639 := bstep (se 1 (by rfl) ⟨1257479, by rfl⟩ : syracuseStep 1676639 = 2514959) B2514959
theorem B3773897 : Blo 992597 3773897 := bstep (se 2 (by rfl) ⟨1415211, by rfl⟩ : syracuseStep 3773897 = 2830423) B2830423
theorem B33166945 : Blo 992597 33166945 := bstep (se 2 (by rfl) ⟨12437604, by rfl⟩ : syracuseStep 33166945 = 24875209) B24875209
theorem B2233979 : Blo 992597 2233979 := bstep (se 1 (by rfl) ⟨1675484, by rfl⟩ : syracuseStep 2233979 = 3350969) B3350969
theorem B2234105 : Blo 992597 2234105 := bstep (se 2 (by rfl) ⟨837789, by rfl⟩ : syracuseStep 2234105 = 1675579) B1675579
theorem B5379959 : Blo 992597 5379959 := bstep (se 1 (by rfl) ⟨4034969, by rfl⟩ : syracuseStep 5379959 = 8069939) B8069939
theorem B1677199 : Blo 992597 1677199 := bstep (se 1 (by rfl) ⟨1257899, by rfl⟩ : syracuseStep 1677199 = 2515799) B2515799
theorem B3774383 : Blo 992597 3774383 := bstep (se 1 (by rfl) ⟨2830787, by rfl⟩ : syracuseStep 3774383 = 5661575) B5661575
theorem B2234375 : Blo 992597 2234375 := bstep (se 1 (by rfl) ⟨1675781, by rfl⟩ : syracuseStep 2234375 = 3351563) B3351563
theorem B8067109 : Blo 992597 8067109 := bstep (se 4 (by rfl) ⟨756291, by rfl⟩ : syracuseStep 8067109 = 1512583) B1512583
theorem B2234447 : Blo 992597 2234447 := bstep (se 1 (by rfl) ⟨1675835, by rfl⟩ : syracuseStep 2234447 = 3351671) B3351671
theorem B1612127 : Blo 992597 1612127 := bstep (se 1 (by rfl) ⟨1209095, by rfl⟩ : syracuseStep 1612127 = 2418191) B2418191
theorem B2234843 : Blo 992597 2234843 := bstep (se 1 (by rfl) ⟨1676132, by rfl⟩ : syracuseStep 2234843 = 3352265) B3352265
theorem B3021275 : Blo 992597 3021275 := bstep (se 1 (by rfl) ⟨2265956, by rfl⟩ : syracuseStep 3021275 = 4531913) B4531913
theorem B3578377 : Blo 992597 3578377 := bstep (se 2 (by rfl) ⟨1341891, by rfl⟩ : syracuseStep 3578377 = 2683783) B2683783
theorem B1677881 : Blo 992597 1677881 := bstep (se 2 (by rfl) ⟨629205, by rfl⟩ : syracuseStep 1677881 = 1258411) B1258411
theorem B1120891 : Blo 992597 1120891 := bstep (se 1 (by rfl) ⟨840668, by rfl⟩ : syracuseStep 1120891 = 1681337) B1681337
theorem B3775187 : Blo 992597 3775187 := bstep (se 1 (by rfl) ⟨2831390, by rfl⟩ : syracuseStep 3775187 = 5662781) B5662781
theorem B2235311 : Blo 992597 2235311 := bstep (se 1 (by rfl) ⟨1676483, by rfl⟩ : syracuseStep 2235311 = 3352967) B3352967
theorem B2235563 : Blo 992597 2235563 := bstep (se 1 (by rfl) ⟨1676672, by rfl⟩ : syracuseStep 2235563 = 3353345) B3353345
theorem B1678583 : Blo 992597 1678583 := bstep (se 1 (by rfl) ⟨1258937, by rfl⟩ : syracuseStep 1678583 = 2517875) B2517875
theorem B3185981 : Blo 992597 3185981 := bstep (se 3 (by rfl) ⟨597371, by rfl⟩ : syracuseStep 3185981 = 1194743) B1194743
theorem B1678927 : Blo 992597 1678927 := bstep (se 1 (by rfl) ⟨1259195, by rfl⟩ : syracuseStep 1678927 = 2518391) B2518391
theorem B2236103 : Blo 992597 2236103 := bstep (se 1 (by rfl) ⟨1677077, by rfl⟩ : syracuseStep 2236103 = 3354155) B3354155
theorem B3186391 : Blo 992597 3186391 := bstep (se 1 (by rfl) ⟨2389793, by rfl⟩ : syracuseStep 3186391 = 4779587) B4779587
theorem B33169133 : Blo 992597 33169133 := bstep (se 3 (by rfl) ⟨6219212, by rfl⟩ : syracuseStep 33169133 = 12438425) B12438425
theorem B1679177 : Blo 992597 1679177 := bstep (se 2 (by rfl) ⟨629691, by rfl⟩ : syracuseStep 1679177 = 1259383) B1259383
theorem B3022687 : Blo 992597 3022687 := bstep (se 1 (by rfl) ⟨2267015, by rfl⟩ : syracuseStep 3022687 = 4534031) B4534031
theorem B3579835 : Blo 992597 3579835 := bstep (se 1 (by rfl) ⟨2684876, by rfl⟩ : syracuseStep 3579835 = 5369753) B5369753
theorem B3350699 : Blo 992597 3350699 := bstep (se 1 (by rfl) ⟨2513024, by rfl⟩ : syracuseStep 3350699 = 5026049) B5026049
theorem B1679609 : Blo 992597 1679609 := bstep (se 2 (by rfl) ⟨629853, by rfl⟩ : syracuseStep 1679609 = 1259707) B1259707
theorem B3186955 : Blo 992597 3186955 := bstep (se 1 (by rfl) ⟨2390216, by rfl⟩ : syracuseStep 3186955 = 4780433) B4780433
theorem B7545149 : Blo 992597 7545149 := bstep (se 3 (by rfl) ⟨1414715, by rfl⟩ : syracuseStep 7545149 = 2829431) B2829431
theorem B1679791 : Blo 992597 1679791 := bstep (se 1 (by rfl) ⟨1259843, by rfl⟩ : syracuseStep 1679791 = 2519687) B2519687
theorem B1679879 : Blo 992597 1679879 := bstep (se 1 (by rfl) ⟨1259909, by rfl⟩ : syracuseStep 1679879 = 2519819) B2519819
theorem B2236967 : Blo 992597 2236967 := bstep (se 1 (by rfl) ⟨1677725, by rfl⟩ : syracuseStep 2236967 = 3355451) B3355451
theorem B8495675 : Blo 992597 8495675 := bstep (se 1 (by rfl) ⟨6371756, by rfl⟩ : syracuseStep 8495675 = 12743513) B12743513
theorem B3351239 : Blo 992597 3351239 := bstep (se 1 (by rfl) ⟨2513429, by rfl⟩ : syracuseStep 3351239 = 5026859) B5026859
theorem B1614583 : Blo 992597 1614583 := bstep (se 1 (by rfl) ⟨1210937, by rfl⟩ : syracuseStep 1614583 = 2421875) B2421875
theorem B1680223 : Blo 992597 1680223 := bstep (se 1 (by rfl) ⟨1260167, by rfl⟩ : syracuseStep 1680223 = 2520335) B2520335
theorem B2237291 : Blo 992597 2237291 := bstep (se 1 (by rfl) ⟨1677968, by rfl⟩ : syracuseStep 2237291 = 3355937) B3355937
theorem B2237345 : Blo 992597 2237345 := bstep (se 2 (by rfl) ⟨839004, by rfl⟩ : syracuseStep 2237345 = 1678009) B1678009
theorem B1680311 : Blo 992597 1680311 := bstep (se 1 (by rfl) ⟨1260233, by rfl⟩ : syracuseStep 1680311 = 2520467) B2520467
theorem B6366275 : Blo 992597 6366275 := bstep (se 1 (by rfl) ⟨4774706, by rfl⟩ : syracuseStep 6366275 = 9549413) B9549413
theorem B3777617 : Blo 992597 3777617 := bstep (se 2 (by rfl) ⟨1416606, by rfl⟩ : syracuseStep 3777617 = 2833213) B2833213
theorem B2237687 : Blo 992597 2237687 := bstep (se 1 (by rfl) ⟨1678265, by rfl⟩ : syracuseStep 2237687 = 3356531) B3356531
theorem B992607 : Blo 992597 992607 := bstep (se 1 (by rfl) ⟨744455, by rfl⟩ : syracuseStep 992607 = 1488911) B1488911
theorem B992635 : Blo 992597 992635 := bstep (se 1 (by rfl) ⟨744476, by rfl⟩ : syracuseStep 992635 = 1488953) B1488953
theorem B992687 : Blo 992597 992687 := bstep (se 1 (by rfl) ⟨744515, by rfl⟩ : syracuseStep 992687 = 1489031) B1489031
theorem B992711 : Blo 992597 992711 := bstep (se 1 (by rfl) ⟨744533, by rfl⟩ : syracuseStep 992711 = 1489067) B1489067
theorem B992731 : Blo 992597 992731 := bstep (se 1 (by rfl) ⟨744548, by rfl⟩ : syracuseStep 992731 = 1489097) B1489097
theorem B4138505 : Blo 992597 4138505 := bstep (se 2 (by rfl) ⟨1551939, by rfl⟩ : syracuseStep 4138505 = 3103879) B3103879
theorem B1680905 : Blo 992597 1680905 := bstep (se 2 (by rfl) ⟨630339, by rfl⟩ : syracuseStep 1680905 = 1260679) B1260679
theorem B3778073 : Blo 992597 3778073 := bstep (se 2 (by rfl) ⟨1416777, by rfl⟩ : syracuseStep 3778073 = 2833555) B2833555
theorem B992807 : Blo 992597 992807 := bstep (se 1 (by rfl) ⟨744605, by rfl⟩ : syracuseStep 992807 = 1489211) B1489211
theorem B3352103 : Blo 992597 3352103 := bstep (se 1 (by rfl) ⟨2514077, by rfl⟩ : syracuseStep 3352103 = 5028155) B5028155
theorem B992847 : Blo 992597 992847 := bstep (se 1 (by rfl) ⟨744635, by rfl⟩ : syracuseStep 992847 = 1489271) B1489271
theorem B992863 : Blo 992597 992863 := bstep (se 1 (by rfl) ⟨744647, by rfl⟩ : syracuseStep 992863 = 1489295) B1489295
theorem B8496737 : Blo 992597 8496737 := bstep (se 2 (by rfl) ⟨3186276, by rfl⟩ : syracuseStep 8496737 = 6372553) B6372553
theorem B992891 : Blo 992597 992891 := bstep (se 1 (by rfl) ⟨744668, by rfl⟩ : syracuseStep 992891 = 1489337) B1489337
theorem B3352211 : Blo 992597 3352211 := bstep (se 1 (by rfl) ⟨2514158, by rfl⟩ : syracuseStep 3352211 = 5028317) B5028317
theorem B4433555 : Blo 992597 4433555 := bstep (se 1 (by rfl) ⟨3325166, by rfl⟩ : syracuseStep 4433555 = 6650333) B6650333
theorem B1681067 : Blo 992597 1681067 := bstep (se 1 (by rfl) ⟨1260800, by rfl⟩ : syracuseStep 1681067 = 2521601) B2521601
theorem B992943 : Blo 992597 992943 := bstep (se 1 (by rfl) ⟨744707, by rfl⟩ : syracuseStep 992943 = 1489415) B1489415
theorem B992967 : Blo 992597 992967 := bstep (se 1 (by rfl) ⟨744725, by rfl⟩ : syracuseStep 992967 = 1489451) B1489451
theorem B992987 : Blo 992597 992987 := bstep (se 1 (by rfl) ⟨744740, by rfl⟩ : syracuseStep 992987 = 1489481) B1489481
theorem B6137593 : Blo 992597 6137593 := bstep (se 2 (by rfl) ⟨2301597, by rfl⟩ : syracuseStep 6137593 = 4603195) B4603195
theorem B993063 : Blo 992597 993063 := bstep (se 1 (by rfl) ⟨744797, by rfl⟩ : syracuseStep 993063 = 1489595) B1489595
theorem B2238281 : Blo 992597 2238281 := bstep (se 2 (by rfl) ⟨839355, by rfl⟩ : syracuseStep 2238281 = 1678711) B1678711
theorem B993103 : Blo 992597 993103 := bstep (se 1 (by rfl) ⟨744827, by rfl⟩ : syracuseStep 993103 = 1489655) B1489655
theorem B993119 : Blo 992597 993119 := bstep (se 1 (by rfl) ⟨744839, by rfl⟩ : syracuseStep 993119 = 1489679) B1489679
theorem B3352427 : Blo 992597 3352427 := bstep (se 1 (by rfl) ⟨2514320, by rfl⟩ : syracuseStep 3352427 = 5028641) B5028641
theorem B993147 : Blo 992597 993147 := bstep (se 1 (by rfl) ⟨744860, by rfl⟩ : syracuseStep 993147 = 1489721) B1489721
theorem B3352481 : Blo 992597 3352481 := bstep (se 2 (by rfl) ⟨1257180, by rfl⟩ : syracuseStep 3352481 = 2514361) B2514361
theorem B993199 : Blo 992597 993199 := bstep (se 1 (by rfl) ⟨744899, by rfl⟩ : syracuseStep 993199 = 1489799) B1489799
theorem B993223 : Blo 992597 993223 := bstep (se 1 (by rfl) ⟨744917, by rfl⟩ : syracuseStep 993223 = 1489835) B1489835
theorem B993243 : Blo 992597 993243 := bstep (se 1 (by rfl) ⟨744932, by rfl⟩ : syracuseStep 993243 = 1489865) B1489865
theorem B3188737 : Blo 992597 3188737 := bstep (se 2 (by rfl) ⟨1195776, by rfl⟩ : syracuseStep 3188737 = 2391553) B2391553
theorem B6367247 : Blo 992597 6367247 := bstep (se 1 (by rfl) ⟨4775435, by rfl⟩ : syracuseStep 6367247 = 9550871) B9550871
theorem B993319 : Blo 992597 993319 := bstep (se 1 (by rfl) ⟨744989, by rfl⟩ : syracuseStep 993319 = 1489979) B1489979
theorem B1681465 : Blo 992597 1681465 := bstep (se 2 (by rfl) ⟨630549, by rfl⟩ : syracuseStep 1681465 = 1261099) B1261099
theorem B993359 : Blo 992597 993359 := bstep (se 1 (by rfl) ⟨745019, by rfl⟩ : syracuseStep 993359 = 1490039) B1490039
theorem B993375 : Blo 992597 993375 := bstep (se 1 (by rfl) ⟨745031, by rfl⟩ : syracuseStep 993375 = 1490063) B1490063
theorem B993403 : Blo 992597 993403 := bstep (se 1 (by rfl) ⟨745052, by rfl⟩ : syracuseStep 993403 = 1490105) B1490105
theorem B6138013 : Blo 992597 6138013 := bstep (se 3 (by rfl) ⟨1150877, by rfl⟩ : syracuseStep 6138013 = 2301755) B2301755
theorem B993455 : Blo 992597 993455 := bstep (se 1 (by rfl) ⟨745091, by rfl⟩ : syracuseStep 993455 = 1490183) B1490183
theorem B993479 : Blo 992597 993479 := bstep (se 1 (by rfl) ⟨745109, by rfl⟩ : syracuseStep 993479 = 1490219) B1490219
theorem B1681607 : Blo 992597 1681607 := bstep (se 1 (by rfl) ⟨1261205, by rfl⟩ : syracuseStep 1681607 = 2522411) B2522411
theorem B993499 : Blo 992597 993499 := bstep (se 1 (by rfl) ⟨745124, by rfl⟩ : syracuseStep 993499 = 1490249) B1490249
theorem B12921121 : Blo 992597 12921121 := bstep (se 2 (by rfl) ⟨4845420, by rfl⟩ : syracuseStep 12921121 = 9690841) B9690841
theorem B993575 : Blo 992597 993575 := bstep (se 1 (by rfl) ⟨745181, by rfl⟩ : syracuseStep 993575 = 1490363) B1490363
theorem B3582269 : Blo 992597 3582269 := bstep (se 3 (by rfl) ⟨671675, by rfl⟩ : syracuseStep 3582269 = 1343351) B1343351
theorem B993615 : Blo 992597 993615 := bstep (se 1 (by rfl) ⟨745211, by rfl⟩ : syracuseStep 993615 = 1490423) B1490423
theorem B993631 : Blo 992597 993631 := bstep (se 1 (by rfl) ⟨745223, by rfl⟩ : syracuseStep 993631 = 1490447) B1490447
theorem B993659 : Blo 992597 993659 := bstep (se 1 (by rfl) ⟨745244, by rfl⟩ : syracuseStep 993659 = 1490489) B1490489
theorem B993711 : Blo 992597 993711 := bstep (se 1 (by rfl) ⟨745283, by rfl⟩ : syracuseStep 993711 = 1490567) B1490567
theorem B993735 : Blo 992597 993735 := bstep (se 1 (by rfl) ⟨745301, by rfl⟩ : syracuseStep 993735 = 1490603) B1490603
theorem B993755 : Blo 992597 993755 := bstep (se 1 (by rfl) ⟨745316, by rfl⟩ : syracuseStep 993755 = 1490633) B1490633
theorem B3353075 : Blo 992597 3353075 := bstep (se 1 (by rfl) ⟨2514806, by rfl⟩ : syracuseStep 3353075 = 5029613) B5029613
theorem B2828839 : Blo 992597 2828839 := bstep (se 1 (by rfl) ⟨2121629, by rfl⟩ : syracuseStep 2828839 = 4243259) B4243259
theorem B993831 : Blo 992597 993831 := bstep (se 1 (by rfl) ⟨745373, by rfl⟩ : syracuseStep 993831 = 1490747) B1490747
theorem B993871 : Blo 992597 993871 := bstep (se 1 (by rfl) ⟨745403, by rfl⟩ : syracuseStep 993871 = 1490807) B1490807
theorem B993887 : Blo 992597 993887 := bstep (se 1 (by rfl) ⟨745415, by rfl⟩ : syracuseStep 993887 = 1490831) B1490831
theorem B2239073 : Blo 992597 2239073 := bstep (se 2 (by rfl) ⟨839652, by rfl⟩ : syracuseStep 2239073 = 1679305) B1679305
theorem B993915 : Blo 992597 993915 := bstep (se 1 (by rfl) ⟨745436, by rfl⟩ : syracuseStep 993915 = 1490873) B1490873
theorem B993967 : Blo 992597 993967 := bstep (se 1 (by rfl) ⟨745475, by rfl⟩ : syracuseStep 993967 = 1490951) B1490951
theorem B3779257 : Blo 992597 3779257 := bstep (se 2 (by rfl) ⟨1417221, by rfl⟩ : syracuseStep 3779257 = 2834443) B2834443
theorem B2828999 : Blo 992597 2828999 := bstep (se 1 (by rfl) ⟨2121749, by rfl⟩ : syracuseStep 2828999 = 4243499) B4243499
theorem B993991 : Blo 992597 993991 := bstep (se 1 (by rfl) ⟨745493, by rfl⟩ : syracuseStep 993991 = 1490987) B1490987
theorem B994011 : Blo 992597 994011 := bstep (se 1 (by rfl) ⟨745508, by rfl⟩ : syracuseStep 994011 = 1491017) B1491017
theorem B994087 : Blo 992597 994087 := bstep (se 1 (by rfl) ⟨745565, by rfl⟩ : syracuseStep 994087 = 1491131) B1491131
theorem B994127 : Blo 992597 994127 := bstep (se 1 (by rfl) ⟨745595, by rfl⟩ : syracuseStep 994127 = 1491191) B1491191
theorem B994143 : Blo 992597 994143 := bstep (se 1 (by rfl) ⟨745607, by rfl⟩ : syracuseStep 994143 = 1491215) B1491215
theorem B994171 : Blo 992597 994171 := bstep (se 1 (by rfl) ⟨745628, by rfl⟩ : syracuseStep 994171 = 1491257) B1491257
theorem B994223 : Blo 992597 994223 := bstep (se 1 (by rfl) ⟨745667, by rfl⟩ : syracuseStep 994223 = 1491335) B1491335
theorem B2829239 : Blo 992597 2829239 := bstep (se 1 (by rfl) ⟨2121929, by rfl⟩ : syracuseStep 2829239 = 4243859) B4243859
theorem B2239415 : Blo 992597 2239415 := bstep (se 1 (by rfl) ⟨1679561, by rfl⟩ : syracuseStep 2239415 = 3359123) B3359123
theorem B994247 : Blo 992597 994247 := bstep (se 1 (by rfl) ⟨745685, by rfl⟩ : syracuseStep 994247 = 1491371) B1491371
theorem B1256411 : Blo 992597 1256411 := bstep (se 1 (by rfl) ⟨942308, by rfl⟩ : syracuseStep 1256411 = 1884617) B1884617
theorem B994267 : Blo 992597 994267 := bstep (se 1 (by rfl) ⟨745700, by rfl⟩ : syracuseStep 994267 = 1491401) B1491401
theorem B3353615 : Blo 992597 3353615 := bstep (se 1 (by rfl) ⟨2515211, by rfl⟩ : syracuseStep 3353615 = 5030423) B5030423
theorem B4303891 : Blo 992597 4303891 := bstep (se 1 (by rfl) ⟨3227918, by rfl⟩ : syracuseStep 4303891 = 6455837) B6455837
theorem B994343 : Blo 992597 994343 := bstep (se 1 (by rfl) ⟨745757, by rfl⟩ : syracuseStep 994343 = 1491515) B1491515
theorem B994383 : Blo 992597 994383 := bstep (se 1 (by rfl) ⟨745787, by rfl⟩ : syracuseStep 994383 = 1491575) B1491575
theorem B11349071 : Blo 992597 11349071 := bstep (se 1 (by rfl) ⟨8511803, by rfl⟩ : syracuseStep 11349071 = 17023607) B17023607
theorem B994399 : Blo 992597 994399 := bstep (se 1 (by rfl) ⟨745799, by rfl⟩ : syracuseStep 994399 = 1491599) B1491599
theorem B3320947 : Blo 992597 3320947 := bstep (se 1 (by rfl) ⟨2490710, by rfl⟩ : syracuseStep 3320947 = 4981421) B4981421
theorem B994427 : Blo 992597 994427 := bstep (se 1 (by rfl) ⟨745820, by rfl⟩ : syracuseStep 994427 = 1491641) B1491641
theorem B994479 : Blo 992597 994479 := bstep (se 1 (by rfl) ⟨745859, by rfl⟩ : syracuseStep 994479 = 1491719) B1491719
theorem B994503 : Blo 992597 994503 := bstep (se 1 (by rfl) ⟨745877, by rfl⟩ : syracuseStep 994503 = 1491755) B1491755
theorem B994523 : Blo 992597 994523 := bstep (se 1 (by rfl) ⟨745892, by rfl⟩ : syracuseStep 994523 = 1491785) B1491785
theorem B3583223 : Blo 992597 3583223 := bstep (se 1 (by rfl) ⟨2687417, by rfl⟩ : syracuseStep 3583223 = 5374835) B5374835
theorem B20655395 : Blo 992597 20655395 := bstep (se 1 (by rfl) ⟨15491546, by rfl⟩ : syracuseStep 20655395 = 30983093) B30983093
theorem B994599 : Blo 992597 994599 := bstep (se 1 (by rfl) ⟨745949, by rfl⟩ : syracuseStep 994599 = 1491899) B1491899
theorem B994639 : Blo 992597 994639 := bstep (se 1 (by rfl) ⟨745979, by rfl⟩ : syracuseStep 994639 = 1491959) B1491959
theorem B994655 : Blo 992597 994655 := bstep (se 1 (by rfl) ⟨745991, by rfl⟩ : syracuseStep 994655 = 1491983) B1491983
theorem B994683 : Blo 992597 994683 := bstep (se 1 (by rfl) ⟨746012, by rfl⟩ : syracuseStep 994683 = 1492025) B1492025
theorem B994735 : Blo 992597 994735 := bstep (se 1 (by rfl) ⟨746051, by rfl⟩ : syracuseStep 994735 = 1492103) B1492103
theorem B1256887 : Blo 992597 1256887 := bstep (se 1 (by rfl) ⟨942665, by rfl⟩ : syracuseStep 1256887 = 1885331) B1885331
theorem B994759 : Blo 992597 994759 := bstep (se 1 (by rfl) ⟨746069, by rfl⟩ : syracuseStep 994759 = 1492139) B1492139
theorem B994779 : Blo 992597 994779 := bstep (se 1 (by rfl) ⟨746084, by rfl⟩ : syracuseStep 994779 = 1492169) B1492169
theorem B2240009 : Blo 992597 2240009 := bstep (se 2 (by rfl) ⟨840003, by rfl⟩ : syracuseStep 2240009 = 1680007) B1680007
theorem B994855 : Blo 992597 994855 := bstep (se 1 (by rfl) ⟨746141, by rfl⟩ : syracuseStep 994855 = 1492283) B1492283
theorem B994895 : Blo 992597 994895 := bstep (se 1 (by rfl) ⟨746171, by rfl⟩ : syracuseStep 994895 = 1492343) B1492343
theorem B994911 : Blo 992597 994911 := bstep (se 1 (by rfl) ⟨746183, by rfl⟩ : syracuseStep 994911 = 1492367) B1492367
theorem B3354209 : Blo 992597 3354209 := bstep (se 2 (by rfl) ⟨1257828, by rfl⟩ : syracuseStep 3354209 = 2515657) B2515657
theorem B994939 : Blo 992597 994939 := bstep (se 1 (by rfl) ⟨746204, by rfl⟩ : syracuseStep 994939 = 1492409) B1492409
theorem B994991 : Blo 992597 994991 := bstep (se 1 (by rfl) ⟨746243, by rfl⟩ : syracuseStep 994991 = 1492487) B1492487
theorem B995015 : Blo 992597 995015 := bstep (se 1 (by rfl) ⟨746261, by rfl⟩ : syracuseStep 995015 = 1492523) B1492523
theorem B995035 : Blo 992597 995035 := bstep (se 1 (by rfl) ⟨746276, by rfl⟩ : syracuseStep 995035 = 1492553) B1492553
theorem B6368989 : Blo 992597 6368989 := bstep (se 3 (by rfl) ⟨1194185, by rfl⟩ : syracuseStep 6368989 = 2388371) B2388371
theorem B995111 : Blo 992597 995111 := bstep (se 1 (by rfl) ⟨746333, by rfl⟩ : syracuseStep 995111 = 1492667) B1492667
theorem B995151 : Blo 992597 995151 := bstep (se 1 (by rfl) ⟨746363, by rfl⟩ : syracuseStep 995151 = 1492727) B1492727
theorem B995167 : Blo 992597 995167 := bstep (se 1 (by rfl) ⟨746375, by rfl⟩ : syracuseStep 995167 = 1492751) B1492751
theorem B2240351 : Blo 992597 2240351 := bstep (se 1 (by rfl) ⟨1680263, by rfl⟩ : syracuseStep 2240351 = 3360527) B3360527
theorem B995195 : Blo 992597 995195 := bstep (se 1 (by rfl) ⟨746396, by rfl⟩ : syracuseStep 995195 = 1492793) B1492793
theorem B2830241 : Blo 992597 2830241 := bstep (se 2 (by rfl) ⟨1061340, by rfl⟩ : syracuseStep 2830241 = 2122681) B2122681
theorem B995247 : Blo 992597 995247 := bstep (se 1 (by rfl) ⟨746435, by rfl⟩ : syracuseStep 995247 = 1492871) B1492871
theorem B1912763 : Blo 992597 1912763 := bstep (se 1 (by rfl) ⟨1434572, by rfl⟩ : syracuseStep 1912763 = 2869145) B2869145
theorem B995271 : Blo 992597 995271 := bstep (se 1 (by rfl) ⟨746453, by rfl⟩ : syracuseStep 995271 = 1492907) B1492907
theorem B995291 : Blo 992597 995291 := bstep (se 1 (by rfl) ⟨746468, by rfl⟩ : syracuseStep 995291 = 1492937) B1492937
theorem B9187343 : Blo 992597 9187343 := bstep (se 1 (by rfl) ⟨6890507, by rfl⟩ : syracuseStep 9187343 = 13781015) B13781015
theorem B3190799 : Blo 992597 3190799 := bstep (se 1 (by rfl) ⟨2393099, by rfl⟩ : syracuseStep 3190799 = 4786199) B4786199
theorem B2240531 : Blo 992597 2240531 := bstep (se 1 (by rfl) ⟨1680398, by rfl⟩ : syracuseStep 2240531 = 3360797) B3360797
theorem B995367 : Blo 992597 995367 := bstep (se 1 (by rfl) ⟨746525, by rfl⟩ : syracuseStep 995367 = 1493051) B1493051
theorem B1060943 : Blo 992597 1060943 := bstep (se 1 (by rfl) ⟨795707, by rfl⟩ : syracuseStep 1060943 = 1591415) B1591415
theorem B2043983 : Blo 992597 2043983 := bstep (se 1 (by rfl) ⟨1532987, by rfl⟩ : syracuseStep 2043983 = 3065975) B3065975
theorem B995407 : Blo 992597 995407 := bstep (se 1 (by rfl) ⟨746555, by rfl⟩ : syracuseStep 995407 = 1493111) B1493111
theorem B995423 : Blo 992597 995423 := bstep (se 1 (by rfl) ⟨746567, by rfl⟩ : syracuseStep 995423 = 1493135) B1493135
theorem B995451 : Blo 992597 995451 := bstep (se 1 (by rfl) ⟨746588, by rfl⟩ : syracuseStep 995451 = 1493177) B1493177
theorem B995503 : Blo 992597 995503 := bstep (se 1 (by rfl) ⟨746627, by rfl⟩ : syracuseStep 995503 = 1493255) B1493255
theorem B995527 : Blo 992597 995527 := bstep (se 1 (by rfl) ⟨746645, by rfl⟩ : syracuseStep 995527 = 1493291) B1493291
theorem B995547 : Blo 992597 995547 := bstep (se 1 (by rfl) ⟨746660, by rfl⟩ : syracuseStep 995547 = 1493321) B1493321
theorem B995623 : Blo 992597 995623 := bstep (se 1 (by rfl) ⟨746717, by rfl⟩ : syracuseStep 995623 = 1493435) B1493435
theorem B995663 : Blo 992597 995663 := bstep (se 1 (by rfl) ⟨746747, by rfl⟩ : syracuseStep 995663 = 1493495) B1493495
theorem B995679 : Blo 992597 995679 := bstep (se 1 (by rfl) ⟨746759, by rfl⟩ : syracuseStep 995679 = 1493519) B1493519
theorem B2830697 : Blo 992597 2830697 := bstep (se 2 (by rfl) ⟨1061511, by rfl⟩ : syracuseStep 2830697 = 2123023) B2123023
theorem B2240873 : Blo 992597 2240873 := bstep (se 2 (by rfl) ⟨840327, by rfl⟩ : syracuseStep 2240873 = 1680655) B1680655
theorem B995707 : Blo 992597 995707 := bstep (se 1 (by rfl) ⟨746780, by rfl⟩ : syracuseStep 995707 = 1493561) B1493561
theorem B3780989 : Blo 992597 3780989 := bstep (se 3 (by rfl) ⟨708935, by rfl⟩ : syracuseStep 3780989 = 1417871) B1417871
theorem B995759 : Blo 992597 995759 := bstep (se 1 (by rfl) ⟨746819, by rfl⟩ : syracuseStep 995759 = 1493639) B1493639
theorem B995783 : Blo 992597 995783 := bstep (se 1 (by rfl) ⟨746837, by rfl⟩ : syracuseStep 995783 = 1493675) B1493675
theorem B995803 : Blo 992597 995803 := bstep (se 1 (by rfl) ⟨746852, by rfl⟩ : syracuseStep 995803 = 1493705) B1493705
theorem B995879 : Blo 992597 995879 := bstep (se 1 (by rfl) ⟨746909, by rfl⟩ : syracuseStep 995879 = 1493819) B1493819
theorem B995919 : Blo 992597 995919 := bstep (se 1 (by rfl) ⟨746939, by rfl⟩ : syracuseStep 995919 = 1493879) B1493879
theorem B995935 : Blo 992597 995935 := bstep (se 1 (by rfl) ⟨746951, by rfl⟩ : syracuseStep 995935 = 1493903) B1493903
theorem B995963 : Blo 992597 995963 := bstep (se 1 (by rfl) ⟨746972, by rfl⟩ : syracuseStep 995963 = 1493945) B1493945
theorem B996015 : Blo 992597 996015 := bstep (se 1 (by rfl) ⟨747011, by rfl⟩ : syracuseStep 996015 = 1494023) B1494023
theorem B1258183 : Blo 992597 1258183 := bstep (se 1 (by rfl) ⟨943637, by rfl⟩ : syracuseStep 1258183 = 1887275) B1887275
theorem B996039 : Blo 992597 996039 := bstep (se 1 (by rfl) ⟨747029, by rfl⟩ : syracuseStep 996039 = 1494059) B1494059
theorem B996059 : Blo 992597 996059 := bstep (se 1 (by rfl) ⟨747044, by rfl⟩ : syracuseStep 996059 = 1494089) B1494089
theorem B996135 : Blo 992597 996135 := bstep (se 1 (by rfl) ⟨747101, by rfl⟩ : syracuseStep 996135 = 1494203) B1494203
theorem B996175 : Blo 992597 996175 := bstep (se 1 (by rfl) ⟨747131, by rfl⟩ : syracuseStep 996175 = 1494263) B1494263
theorem B996191 : Blo 992597 996191 := bstep (se 1 (by rfl) ⟨747143, by rfl⟩ : syracuseStep 996191 = 1494287) B1494287
theorem B996219 : Blo 992597 996219 := bstep (se 1 (by rfl) ⟨747164, by rfl⟩ : syracuseStep 996219 = 1494329) B1494329
theorem B996271 : Blo 992597 996271 := bstep (se 1 (by rfl) ⟨747203, by rfl⟩ : syracuseStep 996271 = 1494407) B1494407
theorem B2241467 : Blo 992597 2241467 := bstep (se 1 (by rfl) ⟨1681100, by rfl⟩ : syracuseStep 2241467 = 3362201) B3362201
theorem B996295 : Blo 992597 996295 := bstep (se 1 (by rfl) ⟨747221, by rfl⟩ : syracuseStep 996295 = 1494443) B1494443
theorem B996315 : Blo 992597 996315 := bstep (se 1 (by rfl) ⟨747236, by rfl⟩ : syracuseStep 996315 = 1494473) B1494473
theorem B3355667 : Blo 992597 3355667 := bstep (se 1 (by rfl) ⟨2516750, by rfl⟩ : syracuseStep 3355667 = 5033501) B5033501
theorem B996391 : Blo 992597 996391 := bstep (se 1 (by rfl) ⟨747293, by rfl⟩ : syracuseStep 996391 = 1494587) B1494587
theorem B2241593 : Blo 992597 2241593 := bstep (se 2 (by rfl) ⟨840597, by rfl⟩ : syracuseStep 2241593 = 1681195) B1681195
theorem B996431 : Blo 992597 996431 := bstep (se 1 (by rfl) ⟨747323, by rfl⟩ : syracuseStep 996431 = 1494647) B1494647
theorem B996447 : Blo 992597 996447 := bstep (se 1 (by rfl) ⟨747335, by rfl⟩ : syracuseStep 996447 = 1494671) B1494671
theorem B1062011 : Blo 992597 1062011 := bstep (se 1 (by rfl) ⟨796508, by rfl⟩ : syracuseStep 1062011 = 1593017) B1593017
theorem B996475 : Blo 992597 996475 := bstep (se 1 (by rfl) ⟨747356, by rfl⟩ : syracuseStep 996475 = 1494713) B1494713
theorem B5387417 : Blo 992597 5387417 := bstep (se 2 (by rfl) ⟨2020281, by rfl⟩ : syracuseStep 5387417 = 4040563) B4040563
theorem B996527 : Blo 992597 996527 := bstep (se 1 (by rfl) ⟨747395, by rfl⟩ : syracuseStep 996527 = 1494791) B1494791
theorem B996551 : Blo 992597 996551 := bstep (se 1 (by rfl) ⟨747413, by rfl⟩ : syracuseStep 996551 = 1494827) B1494827
theorem B996571 : Blo 992597 996571 := bstep (se 1 (by rfl) ⟨747428, by rfl⟩ : syracuseStep 996571 = 1494857) B1494857
theorem B3355991 : Blo 992597 3355991 := bstep (se 1 (by rfl) ⟨2516993, by rfl⟩ : syracuseStep 3355991 = 5033987) B5033987
theorem B2241935 : Blo 992597 2241935 := bstep (se 1 (by rfl) ⟨1681451, by rfl⟩ : syracuseStep 2241935 = 3362903) B3362903
theorem B7157155 : Blo 992597 7157155 := bstep (se 1 (by rfl) ⟨5367866, by rfl⟩ : syracuseStep 7157155 = 10735733) B10735733
theorem B2831881 : Blo 992597 2831881 := bstep (se 2 (by rfl) ⟨1061955, by rfl⟩ : syracuseStep 2831881 = 2123911) B2123911
theorem B6370913 : Blo 992597 6370913 := bstep (se 2 (by rfl) ⟨2389092, by rfl⟩ : syracuseStep 6370913 = 4778185) B4778185
theorem B2242259 : Blo 992597 2242259 := bstep (se 1 (by rfl) ⟨1681694, by rfl⟩ : syracuseStep 2242259 = 3363389) B3363389
theorem B3192671 : Blo 992597 3192671 := bstep (se 1 (by rfl) ⟨2394503, by rfl⟩ : syracuseStep 3192671 = 4789007) B4789007
theorem B4241261 : Blo 992597 4241261 := bstep (se 3 (by rfl) ⟨795236, by rfl⟩ : syracuseStep 4241261 = 1590473) B1590473
theorem B6043501 : Blo 992597 6043501 := bstep (se 3 (by rfl) ⟨1133156, by rfl⟩ : syracuseStep 6043501 = 2266313) B2266313
theorem B1488905 : Blo 992597 1488905 := bstep (se 2 (by rfl) ⟨558339, by rfl⟩ : syracuseStep 1488905 = 1116679) B1116679
theorem B1488935 : Blo 992597 1488935 := bstep (se 1 (by rfl) ⟨1116701, by rfl⟩ : syracuseStep 1488935 = 2233403) B2233403
theorem B1489019 : Blo 992597 1489019 := bstep (se 1 (by rfl) ⟨1116764, by rfl⟩ : syracuseStep 1489019 = 2233529) B2233529
theorem B1489145 : Blo 992597 1489145 := bstep (se 2 (by rfl) ⟨558429, by rfl⟩ : syracuseStep 1489145 = 1116859) B1116859
theorem B1489247 : Blo 992597 1489247 := bstep (se 1 (by rfl) ⟨1116935, by rfl⟩ : syracuseStep 1489247 = 2233871) B2233871
theorem B1489259 : Blo 992597 1489259 := bstep (se 1 (by rfl) ⟨1116944, by rfl⟩ : syracuseStep 1489259 = 2233889) B2233889
theorem B3357071 : Blo 992597 3357071 := bstep (se 1 (by rfl) ⟨2517803, by rfl⟩ : syracuseStep 3357071 = 5035607) B5035607
theorem B3783131 : Blo 992597 3783131 := bstep (se 1 (by rfl) ⟨2837348, by rfl⟩ : syracuseStep 3783131 = 5674697) B5674697
theorem B1063463 : Blo 992597 1063463 := bstep (se 1 (by rfl) ⟨797597, by rfl⟩ : syracuseStep 1063463 = 1595195) B1595195
theorem B1489487 : Blo 992597 1489487 := bstep (se 1 (by rfl) ⟨1117115, by rfl⟩ : syracuseStep 1489487 = 2234231) B2234231
theorem B32750257 : Blo 992597 32750257 := bstep (se 2 (by rfl) ⟨12281346, by rfl⟩ : syracuseStep 32750257 = 24562693) B24562693
theorem B1489607 : Blo 992597 1489607 := bstep (se 1 (by rfl) ⟨1117205, by rfl⟩ : syracuseStep 1489607 = 2234411) B2234411
theorem B3357395 : Blo 992597 3357395 := bstep (se 1 (by rfl) ⟨2518046, by rfl⟩ : syracuseStep 3357395 = 5036093) B5036093
theorem B1915721 : Blo 992597 1915721 := bstep (se 2 (by rfl) ⟨718395, by rfl⟩ : syracuseStep 1915721 = 1436791) B1436791
theorem B2046793 : Blo 992597 2046793 := bstep (se 2 (by rfl) ⟨767547, by rfl⟩ : syracuseStep 2046793 = 1535095) B1535095
theorem B1489769 : Blo 992597 1489769 := bstep (se 2 (by rfl) ⟨558663, by rfl⟩ : syracuseStep 1489769 = 1117327) B1117327
theorem B3029935 : Blo 992597 3029935 := bstep (se 1 (by rfl) ⟨2272451, by rfl⟩ : syracuseStep 3029935 = 4544903) B4544903
theorem B1489847 : Blo 992597 1489847 := bstep (se 1 (by rfl) ⟨1117385, by rfl⟩ : syracuseStep 1489847 = 2234771) B2234771
theorem B2833339 : Blo 992597 2833339 := bstep (se 1 (by rfl) ⟨2125004, by rfl⟩ : syracuseStep 2833339 = 4250009) B4250009
theorem B1489883 : Blo 992597 1489883 := bstep (se 1 (by rfl) ⟨1117412, by rfl⟩ : syracuseStep 1489883 = 2234825) B2234825
theorem B6372371 : Blo 992597 6372371 := bstep (se 1 (by rfl) ⟨4779278, by rfl⟩ : syracuseStep 6372371 = 9558557) B9558557
theorem B2833487 : Blo 992597 2833487 := bstep (se 1 (by rfl) ⟨2125115, by rfl⟩ : syracuseStep 2833487 = 4250231) B4250231
theorem B1260623 : Blo 992597 1260623 := bstep (se 1 (by rfl) ⟨945467, by rfl⟩ : syracuseStep 1260623 = 1890935) B1890935
theorem B6143147 : Blo 992597 6143147 := bstep (se 1 (by rfl) ⟨4607360, by rfl⟩ : syracuseStep 6143147 = 9214721) B9214721
theorem B2014607 : Blo 992597 2014607 := bstep (se 1 (by rfl) ⟨1510955, by rfl⟩ : syracuseStep 2014607 = 3021911) B3021911
theorem B1490351 : Blo 992597 1490351 := bstep (se 1 (by rfl) ⟨1117763, by rfl⟩ : syracuseStep 1490351 = 2235527) B2235527
theorem B1490441 : Blo 992597 1490441 := bstep (se 2 (by rfl) ⟨558915, by rfl⟩ : syracuseStep 1490441 = 1117831) B1117831
theorem B1490471 : Blo 992597 1490471 := bstep (se 1 (by rfl) ⟨1117853, by rfl⟩ : syracuseStep 1490471 = 2235707) B2235707
theorem B1293863 : Blo 992597 1293863 := bstep (se 1 (by rfl) ⟨970397, by rfl⟩ : syracuseStep 1293863 = 1940795) B1940795
theorem B1490555 : Blo 992597 1490555 := bstep (se 1 (by rfl) ⟨1117916, by rfl⟩ : syracuseStep 1490555 = 2235833) B2235833
theorem B1490681 : Blo 992597 1490681 := bstep (se 2 (by rfl) ⟨559005, by rfl⟩ : syracuseStep 1490681 = 1118011) B1118011
theorem B1490783 : Blo 992597 1490783 := bstep (se 1 (by rfl) ⟨1118087, by rfl⟩ : syracuseStep 1490783 = 2236175) B2236175
theorem B1490795 : Blo 992597 1490795 := bstep (se 1 (by rfl) ⟨1118096, by rfl⟩ : syracuseStep 1490795 = 2236193) B2236193
theorem B3358583 : Blo 992597 3358583 := bstep (se 1 (by rfl) ⟨2518937, by rfl⟩ : syracuseStep 3358583 = 5037875) B5037875
theorem B16138115 : Blo 992597 16138115 := bstep (se 1 (by rfl) ⟨12103586, by rfl⟩ : syracuseStep 16138115 = 24207173) B24207173
theorem B58245155 : Blo 992597 58245155 := bstep (se 1 (by rfl) ⟨43683866, by rfl⟩ : syracuseStep 58245155 = 87367733) B87367733
theorem B2834489 : Blo 992597 2834489 := bstep (se 2 (by rfl) ⟨1062933, by rfl⟩ : syracuseStep 2834489 = 2125867) B2125867
theorem B1491023 : Blo 992597 1491023 := bstep (se 1 (by rfl) ⟨1118267, by rfl⟩ : syracuseStep 1491023 = 2236535) B2236535
theorem B3358799 : Blo 992597 3358799 := bstep (se 1 (by rfl) ⟨2519099, by rfl⟩ : syracuseStep 3358799 = 5038199) B5038199
theorem B1491143 : Blo 992597 1491143 := bstep (se 1 (by rfl) ⟨1118357, by rfl⟩ : syracuseStep 1491143 = 2236715) B2236715
theorem B19087589 : Blo 992597 19087589 := bstep (se 4 (by rfl) ⟨1789461, by rfl⟩ : syracuseStep 19087589 = 3578923) B3578923
theorem B1491305 : Blo 992597 1491305 := bstep (se 2 (by rfl) ⟨559239, by rfl⟩ : syracuseStep 1491305 = 1118479) B1118479
theorem B2834831 : Blo 992597 2834831 := bstep (se 1 (by rfl) ⟨2126123, by rfl⟩ : syracuseStep 2834831 = 4252247) B4252247
theorem B1491383 : Blo 992597 1491383 := bstep (se 1 (by rfl) ⟨1118537, by rfl⟩ : syracuseStep 1491383 = 2237075) B2237075
theorem B3359177 : Blo 992597 3359177 := bstep (se 2 (by rfl) ⟨1259691, by rfl⟩ : syracuseStep 3359177 = 2519383) B2519383
theorem B1491419 : Blo 992597 1491419 := bstep (se 1 (by rfl) ⟨1118564, by rfl⟩ : syracuseStep 1491419 = 2237129) B2237129
theorem B5030585 : Blo 992597 5030585 := bstep (se 2 (by rfl) ⟨1886469, by rfl⟩ : syracuseStep 5030585 = 3772939) B3772939
theorem B1884883 : Blo 992597 1884883 := bstep (se 1 (by rfl) ⟨1413662, by rfl⟩ : syracuseStep 1884883 = 2827325) B2827325
theorem B3359447 : Blo 992597 3359447 := bstep (se 1 (by rfl) ⟨2519585, by rfl⟩ : syracuseStep 3359447 = 5039171) B5039171
theorem B1885103 : Blo 992597 1885103 := bstep (se 1 (by rfl) ⟨1413827, by rfl⟩ : syracuseStep 1885103 = 2827655) B2827655
theorem B1491887 : Blo 992597 1491887 := bstep (se 1 (by rfl) ⟨1118915, by rfl⟩ : syracuseStep 1491887 = 2237831) B2237831
theorem B3359663 : Blo 992597 3359663 := bstep (se 1 (by rfl) ⟨2519747, by rfl⟩ : syracuseStep 3359663 = 5039495) B5039495
theorem B1491977 : Blo 992597 1491977 := bstep (se 2 (by rfl) ⟨559491, by rfl⟩ : syracuseStep 1491977 = 1118983) B1118983
theorem B1492007 : Blo 992597 1492007 := bstep (se 1 (by rfl) ⟨1119005, by rfl⟩ : syracuseStep 1492007 = 2238011) B2238011
theorem B1492091 : Blo 992597 1492091 := bstep (se 1 (by rfl) ⟨1119068, by rfl⟩ : syracuseStep 1492091 = 2238137) B2238137
theorem B1492217 : Blo 992597 1492217 := bstep (se 2 (by rfl) ⟨559581, by rfl⟩ : syracuseStep 1492217 = 1119163) B1119163
theorem B1885513 : Blo 992597 1885513 := bstep (se 2 (by rfl) ⟨707067, by rfl⟩ : syracuseStep 1885513 = 1414135) B1414135
theorem B16106845 : Blo 992597 16106845 := bstep (se 3 (by rfl) ⟨3020033, by rfl⟩ : syracuseStep 16106845 = 6040067) B6040067
theorem B1492319 : Blo 992597 1492319 := bstep (se 1 (by rfl) ⟨1119239, by rfl⟩ : syracuseStep 1492319 = 2238479) B2238479
theorem B1492331 : Blo 992597 1492331 := bstep (se 1 (by rfl) ⟨1119248, by rfl⟩ : syracuseStep 1492331 = 2238497) B2238497
theorem B15287753 : Blo 992597 15287753 := bstep (se 2 (by rfl) ⟨5732907, by rfl⟩ : syracuseStep 15287753 = 11465815) B11465815
theorem B1492559 : Blo 992597 1492559 := bstep (se 1 (by rfl) ⟨1119419, by rfl⟩ : syracuseStep 1492559 = 2238839) B2238839
theorem B1492679 : Blo 992597 1492679 := bstep (se 1 (by rfl) ⟨1119509, by rfl⟩ : syracuseStep 1492679 = 2239019) B2239019
theorem B8079047 : Blo 992597 8079047 := bstep (se 1 (by rfl) ⟨6059285, by rfl⟩ : syracuseStep 8079047 = 12118571) B12118571
theorem B1492841 : Blo 992597 1492841 := bstep (se 2 (by rfl) ⟨559815, by rfl⟩ : syracuseStep 1492841 = 1119631) B1119631
theorem B1492919 : Blo 992597 1492919 := bstep (se 1 (by rfl) ⟨1119689, by rfl⟩ : syracuseStep 1492919 = 2239379) B2239379
theorem B1492955 : Blo 992597 1492955 := bstep (se 1 (by rfl) ⟨1119716, by rfl⟩ : syracuseStep 1492955 = 2239433) B2239433
theorem B7653761 : Blo 992597 7653761 := bstep (se 2 (by rfl) ⟨2870160, by rfl⟩ : syracuseStep 7653761 = 5740321) B5740321
theorem B1493423 : Blo 992597 1493423 := bstep (se 1 (by rfl) ⟨1120067, by rfl⟩ : syracuseStep 1493423 = 2240135) B2240135
theorem B1493513 : Blo 992597 1493513 := bstep (se 2 (by rfl) ⟨560067, by rfl⟩ : syracuseStep 1493513 = 1120135) B1120135
theorem B1493543 : Blo 992597 1493543 := bstep (se 1 (by rfl) ⟨1120157, by rfl⟩ : syracuseStep 1493543 = 2240315) B2240315
theorem B1493627 : Blo 992597 1493627 := bstep (se 1 (by rfl) ⟨1120220, by rfl⟩ : syracuseStep 1493627 = 2240441) B2240441
theorem B2017963 : Blo 992597 2017963 := bstep (se 1 (by rfl) ⟨1513472, by rfl⟩ : syracuseStep 2017963 = 3026945) B3026945
theorem B4770515 : Blo 992597 4770515 := bstep (se 1 (by rfl) ⟨3577886, by rfl⟩ : syracuseStep 4770515 = 7155773) B7155773
theorem B1493753 : Blo 992597 1493753 := bstep (se 2 (by rfl) ⟨560157, by rfl⟩ : syracuseStep 1493753 = 1120315) B1120315
theorem B1493855 : Blo 992597 1493855 := bstep (se 1 (by rfl) ⟨1120391, by rfl⟩ : syracuseStep 1493855 = 2240783) B2240783
theorem B4770667 : Blo 992597 4770667 := bstep (se 1 (by rfl) ⟨3578000, by rfl⟩ : syracuseStep 4770667 = 7156001) B7156001
theorem B1493867 : Blo 992597 1493867 := bstep (se 1 (by rfl) ⟨1120400, by rfl⟩ : syracuseStep 1493867 = 2240801) B2240801
theorem B4246607 : Blo 992597 4246607 := bstep (se 1 (by rfl) ⟨3184955, by rfl⟩ : syracuseStep 4246607 = 6369911) B6369911
theorem B1494095 : Blo 992597 1494095 := bstep (se 1 (by rfl) ⟨1120571, by rfl⟩ : syracuseStep 1494095 = 2241143) B2241143
theorem B1494215 : Blo 992597 1494215 := bstep (se 1 (by rfl) ⟨1120661, by rfl⟩ : syracuseStep 1494215 = 2241323) B2241323
theorem B3362039 : Blo 992597 3362039 := bstep (se 1 (by rfl) ⟨2521529, by rfl⟩ : syracuseStep 3362039 = 5043059) B5043059
theorem B1494377 : Blo 992597 1494377 := bstep (se 2 (by rfl) ⟨560391, by rfl⟩ : syracuseStep 1494377 = 1120783) B1120783
theorem B24563087 : Blo 992597 24563087 := bstep (se 1 (by rfl) ⟨18422315, by rfl⟩ : syracuseStep 24563087 = 36844631) B36844631
theorem B1494455 : Blo 992597 1494455 := bstep (se 1 (by rfl) ⟨1120841, by rfl⟩ : syracuseStep 1494455 = 2241683) B2241683
theorem B1494491 : Blo 992597 1494491 := bstep (se 1 (by rfl) ⟨1120868, by rfl⟩ : syracuseStep 1494491 = 2241737) B2241737
theorem B1134119 : Blo 992597 1134119 := bstep (se 1 (by rfl) ⟨850589, by rfl⟩ : syracuseStep 1134119 = 1701179) B1701179
theorem B3362363 : Blo 992597 3362363 := bstep (se 1 (by rfl) ⟨2521772, by rfl⟩ : syracuseStep 3362363 = 5043545) B5043545
theorem B1887943 : Blo 992597 1887943 := bstep (se 1 (by rfl) ⟨1415957, by rfl⟩ : syracuseStep 1887943 = 2831915) B2831915
theorem B3362633 : Blo 992597 3362633 := bstep (se 2 (by rfl) ⟨1260987, by rfl⟩ : syracuseStep 3362633 = 2521975) B2521975
theorem B4247633 : Blo 992597 4247633 := bstep (se 2 (by rfl) ⟨1592862, by rfl⟩ : syracuseStep 4247633 = 3185725) B3185725
theorem B1888505 : Blo 992597 1888505 := bstep (se 2 (by rfl) ⟨708189, by rfl⟩ : syracuseStep 1888505 = 1416379) B1416379
theorem B1888687 : Blo 992597 1888687 := bstep (se 1 (by rfl) ⟨1416515, by rfl⟩ : syracuseStep 1888687 = 2833031) B2833031
theorem B3068513 : Blo 992597 3068513 := bstep (se 2 (by rfl) ⟨1150692, by rfl⟩ : syracuseStep 3068513 = 2301385) B2301385
theorem B4838251 : Blo 992597 4838251 := bstep (se 1 (by rfl) ⟨3628688, by rfl⟩ : syracuseStep 4838251 = 7257377) B7257377
theorem B7263233 : Blo 992597 7263233 := bstep (se 2 (by rfl) ⟨2723712, by rfl⟩ : syracuseStep 7263233 = 5447425) B5447425
theorem B16110809 : Blo 992597 16110809 := bstep (se 2 (by rfl) ⟨6041553, by rfl⟩ : syracuseStep 16110809 = 12083107) B12083107
theorem B1594811 : Blo 992597 1594811 := bstep (se 1 (by rfl) ⟨1196108, by rfl⟩ : syracuseStep 1594811 = 2392217) B2392217
theorem B1889963 : Blo 992597 1889963 := bstep (se 1 (by rfl) ⟨1417472, by rfl⟩ : syracuseStep 1889963 = 2834945) B2834945
theorem B5035769 : Blo 992597 5035769 := bstep (se 2 (by rfl) ⟨1888413, by rfl⟩ : syracuseStep 5035769 = 3776827) B3776827
theorem B1890191 : Blo 992597 1890191 := bstep (se 1 (by rfl) ⟨1417643, by rfl⟩ : syracuseStep 1890191 = 2835287) B2835287
theorem B1595323 : Blo 992597 1595323 := bstep (se 1 (by rfl) ⟨1196492, by rfl⟩ : syracuseStep 1595323 = 2392985) B2392985
theorem B2512903 : Blo 992597 2512903 := bstep (se 1 (by rfl) ⟨1884677, by rfl⟩ : syracuseStep 2512903 = 3769355) B3769355
theorem B1792361 : Blo 992597 1792361 := bstep (se 2 (by rfl) ⟨672135, by rfl⟩ : syracuseStep 1792361 = 1344271) B1344271
theorem B5036417 : Blo 992597 5036417 := bstep (se 2 (by rfl) ⟨1888656, by rfl⟩ : syracuseStep 5036417 = 3777313) B3777313
theorem B2513531 : Blo 992597 2513531 := bstep (se 1 (by rfl) ⟨1885148, by rfl⟩ : syracuseStep 2513531 = 3770297) B3770297
theorem B12114677 : Blo 992597 12114677 := bstep (se 5 (by rfl) ⟨567875, by rfl⟩ : syracuseStep 12114677 = 1135751) B1135751
theorem B1596233 : Blo 992597 1596233 := bstep (se 2 (by rfl) ⟨598587, by rfl⟩ : syracuseStep 1596233 = 1197175) B1197175
theorem B2513825 : Blo 992597 2513825 := bstep (se 2 (by rfl) ⟨942684, by rfl⟩ : syracuseStep 2513825 = 1885369) B1885369
theorem B6380471 : Blo 992597 6380471 := bstep (se 1 (by rfl) ⟨4785353, by rfl⟩ : syracuseStep 6380471 = 9570707) B9570707
theorem B8510507 : Blo 992597 8510507 := bstep (se 1 (by rfl) ⟨6382880, by rfl⟩ : syracuseStep 8510507 = 12765761) B12765761
theorem B4086865 : Blo 992597 4086865 := bstep (se 2 (by rfl) ⟨1532574, by rfl⟩ : syracuseStep 4086865 = 3065149) B3065149
theorem B1891451 : Blo 992597 1891451 := bstep (se 1 (by rfl) ⟨1418588, by rfl⟩ : syracuseStep 1891451 = 2837177) B2837177
theorem B5037227 : Blo 992597 5037227 := bstep (se 1 (by rfl) ⟨3777920, by rfl⟩ : syracuseStep 5037227 = 7555841) B7555841
theorem B1793441 : Blo 992597 1793441 := bstep (se 2 (by rfl) ⟨672540, by rfl⟩ : syracuseStep 1793441 = 1345081) B1345081
theorem B1891937 : Blo 992597 1891937 := bstep (se 2 (by rfl) ⟨709476, by rfl⟩ : syracuseStep 1891937 = 1418953) B1418953
theorem B12738181 : Blo 992597 12738181 := bstep (se 4 (by rfl) ⟨1194204, by rfl⟩ : syracuseStep 12738181 = 2388409) B2388409
theorem B5037713 : Blo 992597 5037713 := bstep (se 2 (by rfl) ⟨1889142, by rfl⟩ : syracuseStep 5037713 = 3778285) B3778285
theorem B2121545 : Blo 992597 2121545 := bstep (se 2 (by rfl) ⟨795579, by rfl⟩ : syracuseStep 2121545 = 1591159) B1591159
theorem B6381575 : Blo 992597 6381575 := bstep (se 1 (by rfl) ⟨4786181, by rfl⟩ : syracuseStep 6381575 = 9572363) B9572363
theorem B4776203 : Blo 992597 4776203 := bstep (se 1 (by rfl) ⟨3582152, by rfl⟩ : syracuseStep 4776203 = 7164305) B7164305
theorem B64545173 : Blo 992597 64545173 := bstep (se 6 (by rfl) ⟨1512777, by rfl⟩ : syracuseStep 64545173 = 3025555) B3025555
theorem B1794479 : Blo 992597 1794479 := bstep (se 1 (by rfl) ⟨1345859, by rfl⟩ : syracuseStep 1794479 = 2691719) B2691719
theorem B6382061 : Blo 992597 6382061 := bstep (se 3 (by rfl) ⟨1196636, by rfl⟩ : syracuseStep 6382061 = 2393273) B2393273
theorem B9069079 : Blo 992597 9069079 := bstep (se 1 (by rfl) ⟨6801809, by rfl⟩ : syracuseStep 9069079 = 13603619) B13603619
theorem B2515495 : Blo 992597 2515495 := bstep (se 1 (by rfl) ⟨1886621, by rfl⟩ : syracuseStep 2515495 = 3773243) B3773243
theorem B10216145 : Blo 992597 10216145 := bstep (se 2 (by rfl) ⟨3831054, by rfl⟩ : syracuseStep 10216145 = 7662109) B7662109
theorem B5366483 : Blo 992597 5366483 := bstep (se 1 (by rfl) ⟨4024862, by rfl⟩ : syracuseStep 5366483 = 8049725) B8049725
theorem B2515819 : Blo 992597 2515819 := bstep (se 1 (by rfl) ⟨1886864, by rfl⟩ : syracuseStep 2515819 = 3773729) B3773729
theorem B7562159 : Blo 992597 7562159 := bstep (se 1 (by rfl) ⟨5671619, by rfl⟩ : syracuseStep 7562159 = 11343239) B11343239
theorem B12248113 : Blo 992597 12248113 := bstep (se 2 (by rfl) ⟨4593042, by rfl⟩ : syracuseStep 12248113 = 9186085) B9186085
theorem B1795547 : Blo 992597 1795547 := bstep (se 1 (by rfl) ⟨1346660, by rfl⟩ : syracuseStep 1795547 = 2693321) B2693321
theorem B2516467 : Blo 992597 2516467 := bstep (se 1 (by rfl) ⟨1887350, by rfl⟩ : syracuseStep 2516467 = 3774701) B3774701
theorem B8513171 : Blo 992597 8513171 := bstep (se 1 (by rfl) ⟨6384878, by rfl⟩ : syracuseStep 8513171 = 12769757) B12769757
theorem B5662507 : Blo 992597 5662507 := bstep (se 1 (by rfl) ⟨4246880, by rfl⟩ : syracuseStep 5662507 = 8493761) B8493761
theorem B5039981 : Blo 992597 5039981 := bstep (se 3 (by rfl) ⟨944996, by rfl⟩ : syracuseStep 5039981 = 1889993) B1889993
theorem B5040143 : Blo 992597 5040143 := bstep (se 1 (by rfl) ⟨3780107, by rfl⟩ : syracuseStep 5040143 = 7560215) B7560215
theorem B22997125 : Blo 992597 22997125 := bstep (se 4 (by rfl) ⟨2155980, by rfl⟩ : syracuseStep 22997125 = 4311961) B4311961
theorem B4024637 : Blo 992597 4024637 := bstep (se 3 (by rfl) ⟨754619, by rfl⟩ : syracuseStep 4024637 = 1509239) B1509239
theorem B40757651 : Blo 992597 40757651 := bstep (se 1 (by rfl) ⟨30568238, by rfl⟩ : syracuseStep 40757651 = 61136477) B61136477
theorem B5368301 : Blo 992597 5368301 := bstep (se 3 (by rfl) ⟨1006556, by rfl⟩ : syracuseStep 5368301 = 2013113) B2013113
theorem B2517601 : Blo 992597 2517601 := bstep (se 2 (by rfl) ⟨944100, by rfl⟩ : syracuseStep 2517601 = 1888201) B1888201
theorem B65399501 : Blo 992597 65399501 := bstep (se 3 (by rfl) ⟨12262406, by rfl⟩ : syracuseStep 65399501 = 24524813) B24524813
theorem B5991241 : Blo 992597 5991241 := bstep (se 2 (by rfl) ⟨2246715, by rfl⟩ : syracuseStep 5991241 = 4493431) B4493431
theorem B2124731 : Blo 992597 2124731 := bstep (se 1 (by rfl) ⟨1593548, by rfl⟩ : syracuseStep 2124731 = 3187097) B3187097
theorem B6810895 : Blo 992597 6810895 := bstep (se 1 (by rfl) ⟨5108171, by rfl⟩ : syracuseStep 6810895 = 10216343) B10216343
theorem B2518553 : Blo 992597 2518553 := bstep (se 2 (by rfl) ⟨944457, by rfl⟩ : syracuseStep 2518553 = 1888915) B1888915
theorem B4255355 : Blo 992597 4255355 := bstep (se 1 (by rfl) ⟨3191516, by rfl⟩ : syracuseStep 4255355 = 6383033) B6383033
theorem B7663243 : Blo 992597 7663243 := bstep (se 1 (by rfl) ⟨5747432, by rfl⟩ : syracuseStep 7663243 = 11494865) B11494865
theorem B2519059 : Blo 992597 2519059 := bstep (se 1 (by rfl) ⟨1889294, by rfl⟩ : syracuseStep 2519059 = 3778589) B3778589
theorem B28668289 : Blo 992597 28668289 := bstep (se 2 (by rfl) ⟨10750608, by rfl⟩ : syracuseStep 28668289 = 21501217) B21501217
theorem B5042897 : Blo 992597 5042897 := bstep (se 2 (by rfl) ⟨1891086, by rfl⟩ : syracuseStep 5042897 = 3782173) B3782173
theorem B2520143 : Blo 992597 2520143 := bstep (se 1 (by rfl) ⟨1890107, by rfl⟩ : syracuseStep 2520143 = 3780215) B3780215
theorem B2421931 : Blo 992597 2421931 := bstep (se 1 (by rfl) ⟨1816448, by rfl⟩ : syracuseStep 2421931 = 3632897) B3632897
theorem B2422235 : Blo 992597 2422235 := bstep (se 1 (by rfl) ⟨1816676, by rfl⟩ : syracuseStep 2422235 = 3633353) B3633353
theorem B2684539 : Blo 992597 2684539 := bstep (se 1 (by rfl) ⟨2013404, by rfl⟩ : syracuseStep 2684539 = 4026809) B4026809
theorem B2127559 : Blo 992597 2127559 := bstep (se 1 (by rfl) ⟨1595669, by rfl⟩ : syracuseStep 2127559 = 3191339) B3191339
theorem B2684627 : Blo 992597 2684627 := bstep (se 1 (by rfl) ⟨2013470, by rfl⟩ : syracuseStep 2684627 = 4026941) B4026941
theorem B2520791 : Blo 992597 2520791 := bstep (se 1 (by rfl) ⟨1890593, by rfl⟩ : syracuseStep 2520791 = 3781187) B3781187
theorem B2521145 : Blo 992597 2521145 := bstep (se 2 (by rfl) ⟨945429, by rfl⟩ : syracuseStep 2521145 = 1890859) B1890859
theorem B2685449 : Blo 992597 2685449 := bstep (se 2 (by rfl) ⟨1007043, by rfl⟩ : syracuseStep 2685449 = 2014087) B2014087
theorem B8616851 : Blo 992597 8616851 := bstep (se 1 (by rfl) ⟨6462638, by rfl⟩ : syracuseStep 8616851 = 12925277) B12925277
theorem B3833027 : Blo 992597 3833027 := bstep (se 1 (by rfl) ⟨2874770, by rfl⟩ : syracuseStep 3833027 = 5749541) B5749541
theorem B5668339 : Blo 992597 5668339 := bstep (se 1 (by rfl) ⟨4251254, by rfl⟩ : syracuseStep 5668339 = 8502509) B8502509
theorem B4030087 : Blo 992597 4030087 := bstep (se 1 (by rfl) ⟨3022565, by rfl⟩ : syracuseStep 4030087 = 6045131) B6045131
theorem B96599789 : Blo 992597 96599789 := bstep (se 3 (by rfl) ⟨18112460, by rfl⟩ : syracuseStep 96599789 = 36224921) B36224921
theorem B3407791 : Blo 992597 3407791 := bstep (se 1 (by rfl) ⟨2555843, by rfl⟩ : syracuseStep 3407791 = 5111687) B5111687
theorem B38830103 : Blo 992597 38830103 := bstep (se 1 (by rfl) ⟨29122577, by rfl⟩ : syracuseStep 38830103 = 58245155) B58245155
theorem B12092105 : Blo 992597 12092105 := bstep (se 2 (by rfl) ⟨4534539, by rfl⟩ : syracuseStep 12092105 = 9069079) B9069079
theorem B10191835 : Blo 992597 10191835 := bstep (se 1 (by rfl) ⟨7643876, by rfl⟩ : syracuseStep 10191835 = 15287753) B15287753
theorem B27198467 : Blo 992597 27198467 := bstep (se 1 (by rfl) ⟨20398850, by rfl⟩ : syracuseStep 27198467 = 40797701) B40797701
theorem B4785277 : Blo 992597 4785277 := bstep (se 3 (by rfl) ⟨897239, by rfl⟩ : syracuseStep 4785277 = 1794479) B1794479
theorem B8488637 : Blo 992597 8488637 := bstep (se 3 (by rfl) ⟨1591619, by rfl⟩ : syracuseStep 8488637 = 3183239) B3183239
theorem B3180343 : Blo 992597 3180343 := bstep (se 1 (by rfl) ⟨2385257, by rfl⟩ : syracuseStep 3180343 = 4770515) B4770515
theorem B1116895 : Blo 992597 1116895 := bstep (se 1 (by rfl) ⟨837671, by rfl⟩ : syracuseStep 1116895 = 1675343) B1675343
theorem B1117471 : Blo 992597 1117471 := bstep (se 1 (by rfl) ⟨838103, by rfl⟩ : syracuseStep 1117471 = 1676207) B1676207
theorem B3771785 : Blo 992597 3771785 := bstep (se 2 (by rfl) ⟨1414419, by rfl⟩ : syracuseStep 3771785 = 2828839) B2828839
theorem B1117759 : Blo 992597 1117759 := bstep (se 1 (by rfl) ⟨838319, by rfl⟩ : syracuseStep 1117759 = 1676639) B1676639
theorem B5738521 : Blo 992597 5738521 := bstep (se 2 (by rfl) ⟨2151945, by rfl⟩ : syracuseStep 5738521 = 4303891) B4303891
theorem B4427929 : Blo 992597 4427929 := bstep (se 2 (by rfl) ⟨1660473, by rfl⟩ : syracuseStep 4427929 = 3320947) B3320947
theorem B1118587 : Blo 992597 1118587 := bstep (se 1 (by rfl) ⟨838940, by rfl⟩ : syracuseStep 1118587 = 1677881) B1677881
theorem B1675687 : Blo 992597 1675687 := bstep (se 1 (by rfl) ⟨1256765, by rfl⟩ : syracuseStep 1675687 = 2513531) B2513531
theorem B1675849 : Blo 992597 1675849 := bstep (se 2 (by rfl) ⟨628443, by rfl⟩ : syracuseStep 1675849 = 1256887) B1256887
theorem B1675883 : Blo 992597 1675883 := bstep (se 1 (by rfl) ⟨1256912, by rfl⟩ : syracuseStep 1675883 = 2513825) B2513825
theorem B5673671 : Blo 992597 5673671 := bstep (se 1 (by rfl) ⟨4255253, by rfl⟩ : syracuseStep 5673671 = 8510507) B8510507
theorem B1119055 : Blo 992597 1119055 := bstep (se 1 (by rfl) ⟨839291, by rfl⟩ : syracuseStep 1119055 = 1678583) B1678583
theorem B8491985 : Blo 992597 8491985 := bstep (se 2 (by rfl) ⟨3184494, by rfl⟩ : syracuseStep 8491985 = 6368989) B6368989
theorem B1414363 : Blo 992597 1414363 := bstep (se 1 (by rfl) ⟨1060772, by rfl⟩ : syracuseStep 1414363 = 2121545) B2121545
theorem B1119451 : Blo 992597 1119451 := bstep (se 1 (by rfl) ⟨839588, by rfl⟩ : syracuseStep 1119451 = 1679177) B1679177
theorem B2233799 : Blo 992597 2233799 := bstep (se 1 (by rfl) ⟨1675349, by rfl⟩ : syracuseStep 2233799 = 3350699) B3350699
theorem B1119739 : Blo 992597 1119739 := bstep (se 1 (by rfl) ⟨839804, by rfl⟩ : syracuseStep 1119739 = 1679609) B1679609
theorem B43030115 : Blo 992597 43030115 := bstep (se 1 (by rfl) ⟨32272586, by rfl⟩ : syracuseStep 43030115 = 64545173) B64545173
theorem B1119919 : Blo 992597 1119919 := bstep (se 1 (by rfl) ⟨839939, by rfl⟩ : syracuseStep 1119919 = 1679879) B1679879
theorem B13801205 : Blo 992597 13801205 := bstep (se 5 (by rfl) ⟨646931, by rfl⟩ : syracuseStep 13801205 = 1293863) B1293863
theorem B21796613 : Blo 992597 21796613 := bstep (se 4 (by rfl) ⟨2043432, by rfl⟩ : syracuseStep 21796613 = 4086865) B4086865
theorem B2234159 : Blo 992597 2234159 := bstep (se 1 (by rfl) ⟨1675619, by rfl⟩ : syracuseStep 2234159 = 3351239) B3351239
theorem B3577655 : Blo 992597 3577655 := bstep (se 1 (by rfl) ⟨2683241, by rfl⟩ : syracuseStep 3577655 = 5366483) B5366483
theorem B1120207 : Blo 992597 1120207 := bstep (se 1 (by rfl) ⟨840155, by rfl⟩ : syracuseStep 1120207 = 1680311) B1680311
theorem B1677577 : Blo 992597 1677577 := bstep (se 2 (by rfl) ⟨629091, by rfl⟩ : syracuseStep 1677577 = 1258183) B1258183
theorem B2759003 : Blo 992597 2759003 := bstep (se 1 (by rfl) ⟨2069252, by rfl⟩ : syracuseStep 2759003 = 4138505) B4138505
theorem B1120603 : Blo 992597 1120603 := bstep (se 1 (by rfl) ⟨840452, by rfl⟩ : syracuseStep 1120603 = 1680905) B1680905
theorem B2234735 : Blo 992597 2234735 := bstep (se 1 (by rfl) ⟨1676051, by rfl⟩ : syracuseStep 2234735 = 3352103) B3352103
theorem B2234807 : Blo 992597 2234807 := bstep (se 1 (by rfl) ⟨1676105, by rfl⟩ : syracuseStep 2234807 = 3352211) B3352211
theorem B5675447 : Blo 992597 5675447 := bstep (se 1 (by rfl) ⟨4256585, by rfl⟩ : syracuseStep 5675447 = 8513171) B8513171
theorem B2955703 : Blo 992597 2955703 := bstep (se 1 (by rfl) ⟨2216777, by rfl⟩ : syracuseStep 2955703 = 4433555) B4433555
theorem B1120711 : Blo 992597 1120711 := bstep (se 1 (by rfl) ⟨840533, by rfl⟩ : syracuseStep 1120711 = 1681067) B1681067
theorem B2234951 : Blo 992597 2234951 := bstep (se 1 (by rfl) ⟨1676213, by rfl⟩ : syracuseStep 2234951 = 3352427) B3352427
theorem B2234987 : Blo 992597 2234987 := bstep (se 1 (by rfl) ⟨1676240, by rfl⟩ : syracuseStep 2234987 = 3352481) B3352481
theorem B1121071 : Blo 992597 1121071 := bstep (se 1 (by rfl) ⟨840803, by rfl⟩ : syracuseStep 1121071 = 1681607) B1681607
theorem B27171767 : Blo 992597 27171767 := bstep (se 1 (by rfl) ⟨20378825, by rfl⟩ : syracuseStep 27171767 = 40757651) B40757651
theorem B3578867 : Blo 992597 3578867 := bstep (se 1 (by rfl) ⟨2684150, by rfl⟩ : syracuseStep 3578867 = 5368301) B5368301
theorem B2235383 : Blo 992597 2235383 := bstep (se 1 (by rfl) ⟨1676537, by rfl⟩ : syracuseStep 2235383 = 3353075) B3353075
theorem B9542873 : Blo 992597 9542873 := bstep (se 2 (by rfl) ⟨3578577, by rfl⟩ : syracuseStep 9542873 = 7157155) B7157155
theorem B2235743 : Blo 992597 2235743 := bstep (se 1 (by rfl) ⟨1676807, by rfl⟩ : syracuseStep 2235743 = 3353615) B3353615
theorem B3775841 : Blo 992597 3775841 := bstep (se 2 (by rfl) ⟨1415940, by rfl⟩ : syracuseStep 3775841 = 2831881) B2831881
theorem B3579385 : Blo 992597 3579385 := bstep (se 2 (by rfl) ⟨1342269, by rfl⟩ : syracuseStep 3579385 = 2684539) B2684539
theorem B13770263 : Blo 992597 13770263 := bstep (se 1 (by rfl) ⟨10327697, by rfl⟩ : syracuseStep 13770263 = 20655395) B20655395
theorem B1679035 : Blo 992597 1679035 := bstep (se 1 (by rfl) ⟨1259276, by rfl⟩ : syracuseStep 1679035 = 2518553) B2518553
theorem B2236139 : Blo 992597 2236139 := bstep (se 1 (by rfl) ⟨1677104, by rfl⟩ : syracuseStep 2236139 = 3354209) B3354209
theorem B2236265 : Blo 992597 2236265 := bstep (se 2 (by rfl) ⟨838599, by rfl⟩ : syracuseStep 2236265 = 1677199) B1677199
theorem B3350429 : Blo 992597 3350429 := bstep (se 3 (by rfl) ⟨628205, by rfl⟩ : syracuseStep 3350429 = 1256411) B1256411
theorem B3350537 : Blo 992597 3350537 := bstep (se 2 (by rfl) ⟨1256451, by rfl⟩ : syracuseStep 3350537 = 2512903) B2512903
theorem B10756145 : Blo 992597 10756145 := bstep (se 2 (by rfl) ⟨4033554, by rfl⟩ : syracuseStep 10756145 = 8067109) B8067109
theorem B2237111 : Blo 992597 2237111 := bstep (se 1 (by rfl) ⟨1677833, by rfl⟩ : syracuseStep 2237111 = 3355667) B3355667
theorem B1680095 : Blo 992597 1680095 := bstep (se 1 (by rfl) ⟨1260071, by rfl⟩ : syracuseStep 1680095 = 2520143) B2520143
theorem B2237327 : Blo 992597 2237327 := bstep (se 1 (by rfl) ⟨1677995, by rfl⟩ : syracuseStep 2237327 = 3355991) B3355991
theorem B1614823 : Blo 992597 1614823 := bstep (se 1 (by rfl) ⟨1211117, by rfl⟩ : syracuseStep 1614823 = 2422235) B2422235
theorem B2729057 : Blo 992597 2729057 := bstep (se 2 (by rfl) ⟨1023396, by rfl⟩ : syracuseStep 2729057 = 2046793) B2046793
theorem B1680527 : Blo 992597 1680527 := bstep (se 1 (by rfl) ⟨1260395, by rfl⟩ : syracuseStep 1680527 = 2520791) B2520791
theorem B4039913 : Blo 992597 4039913 := bstep (se 2 (by rfl) ⟨1514967, by rfl⟩ : syracuseStep 4039913 = 3029935) B3029935
theorem B2827507 : Blo 992597 2827507 := bstep (se 1 (by rfl) ⟨2120630, by rfl⟩ : syracuseStep 2827507 = 4241261) B4241261
theorem B3777785 : Blo 992597 3777785 := bstep (se 2 (by rfl) ⟨1416669, by rfl⟩ : syracuseStep 3777785 = 2833339) B2833339
theorem B992603 : Blo 992597 992603 := bstep (se 1 (by rfl) ⟨744452, by rfl⟩ : syracuseStep 992603 = 1488905) B1488905
theorem B992623 : Blo 992597 992623 := bstep (se 1 (by rfl) ⟨744467, by rfl⟩ : syracuseStep 992623 = 1488935) B1488935
theorem B1680763 : Blo 992597 1680763 := bstep (se 1 (by rfl) ⟨1260572, by rfl⟩ : syracuseStep 1680763 = 2521145) B2521145
theorem B992679 : Blo 992597 992679 := bstep (se 1 (by rfl) ⟨744509, by rfl⟩ : syracuseStep 992679 = 1489019) B1489019
theorem B3024317 : Blo 992597 3024317 := bstep (se 3 (by rfl) ⟨567059, by rfl⟩ : syracuseStep 3024317 = 1134119) B1134119
theorem B992763 : Blo 992597 992763 := bstep (se 1 (by rfl) ⟨744572, by rfl⟩ : syracuseStep 992763 = 1489145) B1489145
theorem B992831 : Blo 992597 992831 := bstep (se 1 (by rfl) ⟨744623, by rfl⟩ : syracuseStep 992831 = 1489247) B1489247
theorem B992839 : Blo 992597 992839 := bstep (se 1 (by rfl) ⟨744629, by rfl⟩ : syracuseStep 992839 = 1489259) B1489259
theorem B2238047 : Blo 992597 2238047 := bstep (se 1 (by rfl) ⟨1678535, by rfl⟩ : syracuseStep 2238047 = 3357071) B3357071
theorem B11347613 : Blo 992597 11347613 := bstep (se 3 (by rfl) ⟨2127677, by rfl⟩ : syracuseStep 11347613 = 4255355) B4255355
theorem B992991 : Blo 992597 992991 := bstep (se 1 (by rfl) ⟨744743, by rfl⟩ : syracuseStep 992991 = 1489487) B1489487
theorem B993071 : Blo 992597 993071 := bstep (se 1 (by rfl) ⟨744803, by rfl⟩ : syracuseStep 993071 = 1489607) B1489607
theorem B2238263 : Blo 992597 2238263 := bstep (se 1 (by rfl) ⟨1678697, by rfl⟩ : syracuseStep 2238263 = 3357395) B3357395
theorem B993179 : Blo 992597 993179 := bstep (se 1 (by rfl) ⟨744884, by rfl⟩ : syracuseStep 993179 = 1489769) B1489769
theorem B5744567 : Blo 992597 5744567 := bstep (se 1 (by rfl) ⟨4308425, by rfl⟩ : syracuseStep 5744567 = 8616851) B8616851
theorem B88451021 : Blo 992597 88451021 := bstep (se 3 (by rfl) ⟨16584566, by rfl⟩ : syracuseStep 88451021 = 33169133) B33169133
theorem B993231 : Blo 992597 993231 := bstep (se 1 (by rfl) ⟨744923, by rfl⟩ : syracuseStep 993231 = 1489847) B1489847
theorem B993255 : Blo 992597 993255 := bstep (se 1 (by rfl) ⟨744941, by rfl⟩ : syracuseStep 993255 = 1489883) B1489883
theorem B2238569 : Blo 992597 2238569 := bstep (se 2 (by rfl) ⟨839463, by rfl⟩ : syracuseStep 2238569 = 1678927) B1678927
theorem B16984241 : Blo 992597 16984241 := bstep (se 2 (by rfl) ⟨6369090, by rfl⟩ : syracuseStep 16984241 = 12738181) B12738181
theorem B993567 : Blo 992597 993567 := bstep (se 1 (by rfl) ⟨745175, by rfl⟩ : syracuseStep 993567 = 1490351) B1490351
theorem B993627 : Blo 992597 993627 := bstep (se 1 (by rfl) ⟨745220, by rfl⟩ : syracuseStep 993627 = 1490441) B1490441
theorem B993647 : Blo 992597 993647 := bstep (se 1 (by rfl) ⟨745235, by rfl⟩ : syracuseStep 993647 = 1490471) B1490471
theorem B993703 : Blo 992597 993703 := bstep (se 1 (by rfl) ⟨745277, by rfl⟩ : syracuseStep 993703 = 1490555) B1490555
theorem B64399859 : Blo 992597 64399859 := bstep (se 1 (by rfl) ⟨48299894, by rfl⟩ : syracuseStep 64399859 = 96599789) B96599789
theorem B993787 : Blo 992597 993787 := bstep (se 1 (by rfl) ⟨745340, by rfl⟩ : syracuseStep 993787 = 1490681) B1490681
theorem B993855 : Blo 992597 993855 := bstep (se 1 (by rfl) ⟨745391, by rfl⟩ : syracuseStep 993855 = 1490783) B1490783
theorem B993863 : Blo 992597 993863 := bstep (se 1 (by rfl) ⟨745397, by rfl⟩ : syracuseStep 993863 = 1490795) B1490795
theorem B2239055 : Blo 992597 2239055 := bstep (se 1 (by rfl) ⟨1679291, by rfl⟩ : syracuseStep 2239055 = 3358583) B3358583
theorem B10758743 : Blo 992597 10758743 := bstep (se 1 (by rfl) ⟨8069057, by rfl⟩ : syracuseStep 10758743 = 16138115) B16138115
theorem B994015 : Blo 992597 994015 := bstep (se 1 (by rfl) ⟨745511, by rfl⟩ : syracuseStep 994015 = 1491023) B1491023
theorem B2239199 : Blo 992597 2239199 := bstep (se 1 (by rfl) ⟨1679399, by rfl⟩ : syracuseStep 2239199 = 3358799) B3358799
theorem B994095 : Blo 992597 994095 := bstep (se 1 (by rfl) ⟨745571, by rfl⟩ : syracuseStep 994095 = 1491143) B1491143
theorem B12725059 : Blo 992597 12725059 := bstep (se 1 (by rfl) ⟨9543794, by rfl⟩ : syracuseStep 12725059 = 19087589) B19087589
theorem B2829181 : Blo 992597 2829181 := bstep (se 3 (by rfl) ⟨530471, by rfl⟩ : syracuseStep 2829181 = 1060943) B1060943
theorem B994203 : Blo 992597 994203 := bstep (se 1 (by rfl) ⟨745652, by rfl⟩ : syracuseStep 994203 = 1491305) B1491305
theorem B994255 : Blo 992597 994255 := bstep (se 1 (by rfl) ⟨745691, by rfl⟩ : syracuseStep 994255 = 1491383) B1491383
theorem B2239451 : Blo 992597 2239451 := bstep (se 1 (by rfl) ⟨1679588, by rfl⟩ : syracuseStep 2239451 = 3359177) B3359177
theorem B994279 : Blo 992597 994279 := bstep (se 1 (by rfl) ⟨745709, by rfl⟩ : syracuseStep 994279 = 1491419) B1491419
theorem B3353723 : Blo 992597 3353723 := bstep (se 1 (by rfl) ⟨2515292, by rfl⟩ : syracuseStep 3353723 = 5030585) B5030585
theorem B2239631 : Blo 992597 2239631 := bstep (se 1 (by rfl) ⟨1679723, by rfl⟩ : syracuseStep 2239631 = 3359447) B3359447
theorem B3189979 : Blo 992597 3189979 := bstep (se 1 (by rfl) ⟨2392484, by rfl⟩ : syracuseStep 3189979 = 4784969) B4784969
theorem B2239721 : Blo 992597 2239721 := bstep (se 2 (by rfl) ⟨839895, by rfl⟩ : syracuseStep 2239721 = 1679791) B1679791
theorem B1256735 : Blo 992597 1256735 := bstep (se 1 (by rfl) ⟨942551, by rfl⟩ : syracuseStep 1256735 = 1885103) B1885103
theorem B994591 : Blo 992597 994591 := bstep (se 1 (by rfl) ⟨745943, by rfl⟩ : syracuseStep 994591 = 1491887) B1491887
theorem B2239775 : Blo 992597 2239775 := bstep (se 1 (by rfl) ⟨1679831, by rfl⟩ : syracuseStep 2239775 = 3359663) B3359663
theorem B994651 : Blo 992597 994651 := bstep (se 1 (by rfl) ⟨745988, by rfl⟩ : syracuseStep 994651 = 1491977) B1491977
theorem B994671 : Blo 992597 994671 := bstep (se 1 (by rfl) ⟨746003, by rfl⟩ : syracuseStep 994671 = 1492007) B1492007
theorem B3353993 : Blo 992597 3353993 := bstep (se 2 (by rfl) ⟨1257747, by rfl⟩ : syracuseStep 3353993 = 2515495) B2515495
theorem B994727 : Blo 992597 994727 := bstep (se 1 (by rfl) ⟨746045, by rfl⟩ : syracuseStep 994727 = 1492091) B1492091
theorem B5025239 : Blo 992597 5025239 := bstep (se 1 (by rfl) ⟨3768929, by rfl⟩ : syracuseStep 5025239 = 7537859) B7537859
theorem B994811 : Blo 992597 994811 := bstep (se 1 (by rfl) ⟨746108, by rfl⟩ : syracuseStep 994811 = 1492217) B1492217
theorem B994879 : Blo 992597 994879 := bstep (se 1 (by rfl) ⟨746159, by rfl⟩ : syracuseStep 994879 = 1492319) B1492319
theorem B994887 : Blo 992597 994887 := bstep (se 1 (by rfl) ⟨746165, by rfl⟩ : syracuseStep 994887 = 1492331) B1492331
theorem B995039 : Blo 992597 995039 := bstep (se 1 (by rfl) ⟨746279, by rfl⟩ : syracuseStep 995039 = 1492559) B1492559
theorem B2240297 : Blo 992597 2240297 := bstep (se 2 (by rfl) ⟨840111, by rfl⟩ : syracuseStep 2240297 = 1680223) B1680223
theorem B995119 : Blo 992597 995119 := bstep (se 1 (by rfl) ⟨746339, by rfl⟩ : syracuseStep 995119 = 1492679) B1492679
theorem B5386031 : Blo 992597 5386031 := bstep (se 1 (by rfl) ⟨4039523, by rfl⟩ : syracuseStep 5386031 = 8079047) B8079047
theorem B3354425 : Blo 992597 3354425 := bstep (se 2 (by rfl) ⟨1257909, by rfl⟩ : syracuseStep 3354425 = 2515819) B2515819
theorem B995227 : Blo 992597 995227 := bstep (se 1 (by rfl) ⟨746420, by rfl⟩ : syracuseStep 995227 = 1492841) B1492841
theorem B995279 : Blo 992597 995279 := bstep (se 1 (by rfl) ⟨746459, by rfl⟩ : syracuseStep 995279 = 1492919) B1492919
theorem B995303 : Blo 992597 995303 := bstep (se 1 (by rfl) ⟨746477, by rfl⟩ : syracuseStep 995303 = 1492955) B1492955
theorem B16330817 : Blo 992597 16330817 := bstep (se 2 (by rfl) ⟨6124056, by rfl⟩ : syracuseStep 16330817 = 12248113) B12248113
theorem B995615 : Blo 992597 995615 := bstep (se 1 (by rfl) ⟨746711, by rfl⟩ : syracuseStep 995615 = 1493423) B1493423
theorem B995675 : Blo 992597 995675 := bstep (se 1 (by rfl) ⟨746756, by rfl⟩ : syracuseStep 995675 = 1493513) B1493513
theorem B995695 : Blo 992597 995695 := bstep (se 1 (by rfl) ⟨746771, by rfl⟩ : syracuseStep 995695 = 1493543) B1493543
theorem B995751 : Blo 992597 995751 := bstep (se 1 (by rfl) ⟨746813, by rfl⟩ : syracuseStep 995751 = 1493627) B1493627
theorem B21475793 : Blo 992597 21475793 := bstep (se 2 (by rfl) ⟨8053422, by rfl⟩ : syracuseStep 21475793 = 16106845) B16106845
theorem B995835 : Blo 992597 995835 := bstep (se 1 (by rfl) ⟨746876, by rfl⟩ : syracuseStep 995835 = 1493753) B1493753
theorem B995903 : Blo 992597 995903 := bstep (se 1 (by rfl) ⟨746927, by rfl⟩ : syracuseStep 995903 = 1493855) B1493855
theorem B995911 : Blo 992597 995911 := bstep (se 1 (by rfl) ⟨746933, by rfl⟩ : syracuseStep 995911 = 1493867) B1493867
theorem B3355289 : Blo 992597 3355289 := bstep (se 2 (by rfl) ⟨1258233, by rfl⟩ : syracuseStep 3355289 = 2516467) B2516467
theorem B996063 : Blo 992597 996063 := bstep (se 1 (by rfl) ⟨747047, by rfl⟩ : syracuseStep 996063 = 1494095) B1494095
theorem B996143 : Blo 992597 996143 := bstep (se 1 (by rfl) ⟨747107, by rfl⟩ : syracuseStep 996143 = 1494215) B1494215
theorem B2241359 : Blo 992597 2241359 := bstep (se 1 (by rfl) ⟨1681019, by rfl⟩ : syracuseStep 2241359 = 3362039) B3362039
theorem B996251 : Blo 992597 996251 := bstep (se 1 (by rfl) ⟨747188, by rfl⟩ : syracuseStep 996251 = 1494377) B1494377
theorem B996303 : Blo 992597 996303 := bstep (se 1 (by rfl) ⟨747227, by rfl⟩ : syracuseStep 996303 = 1494455) B1494455
theorem B996327 : Blo 992597 996327 := bstep (se 1 (by rfl) ⟨747245, by rfl⟩ : syracuseStep 996327 = 1494491) B1494491
theorem B2241575 : Blo 992597 2241575 := bstep (se 1 (by rfl) ⟨1681181, by rfl⟩ : syracuseStep 2241575 = 3362363) B3362363
theorem B7550009 : Blo 992597 7550009 := bstep (se 2 (by rfl) ⟨2831253, by rfl⟩ : syracuseStep 7550009 = 5662507) B5662507
theorem B2241755 : Blo 992597 2241755 := bstep (se 1 (by rfl) ⟨1681316, by rfl⟩ : syracuseStep 2241755 = 3362633) B3362633
theorem B2831755 : Blo 992597 2831755 := bstep (se 1 (by rfl) ⟨2123816, by rfl⟩ : syracuseStep 2831755 = 4247633) B4247633
theorem B2241953 : Blo 992597 2241953 := bstep (se 2 (by rfl) ⟨840732, by rfl⟩ : syracuseStep 2241953 = 1681465) B1681465
theorem B1259003 : Blo 992597 1259003 := bstep (se 1 (by rfl) ⟨944252, by rfl⟩ : syracuseStep 1259003 = 1888505) B1888505
theorem B2832029 : Blo 992597 2832029 := bstep (se 3 (by rfl) ⟨531005, by rfl⟩ : syracuseStep 2832029 = 1062011) B1062011
theorem B2045675 : Blo 992597 2045675 := bstep (se 1 (by rfl) ⟨1534256, by rfl⟩ : syracuseStep 2045675 = 3068513) B3068513
theorem B8501111 : Blo 992597 8501111 := bstep (se 1 (by rfl) ⟨6375833, by rfl⟩ : syracuseStep 8501111 = 12751667) B12751667
theorem B1489001 : Blo 992597 1489001 := bstep (se 2 (by rfl) ⟨558375, by rfl⟩ : syracuseStep 1489001 = 1116751) B1116751
theorem B3356801 : Blo 992597 3356801 := bstep (se 2 (by rfl) ⟨1258800, by rfl⟩ : syracuseStep 3356801 = 2517601) B2517601
theorem B10762469 : Blo 992597 10762469 := bstep (se 4 (by rfl) ⟨1008981, by rfl⟩ : syracuseStep 10762469 = 2017963) B2017963
theorem B17217773 : Blo 992597 17217773 := bstep (se 3 (by rfl) ⟨3228332, by rfl⟩ : syracuseStep 17217773 = 6456665) B6456665
theorem B1063207 : Blo 992597 1063207 := bstep (se 1 (by rfl) ⟨797405, by rfl⟩ : syracuseStep 1063207 = 1594811) B1594811
theorem B1489319 : Blo 992597 1489319 := bstep (se 1 (by rfl) ⟨1116989, by rfl⟩ : syracuseStep 1489319 = 2233979) B2233979
theorem B1259975 : Blo 992597 1259975 := bstep (se 1 (by rfl) ⟨944981, by rfl⟩ : syracuseStep 1259975 = 1889963) B1889963
theorem B1489403 : Blo 992597 1489403 := bstep (se 1 (by rfl) ⟨1117052, by rfl⟩ : syracuseStep 1489403 = 2234105) B2234105
theorem B3357179 : Blo 992597 3357179 := bstep (se 1 (by rfl) ⟨2517884, by rfl⟩ : syracuseStep 3357179 = 5035769) B5035769
theorem B3586639 : Blo 992597 3586639 := bstep (se 1 (by rfl) ⟨2689979, by rfl⟩ : syracuseStep 3586639 = 5379959) B5379959
theorem B1260127 : Blo 992597 1260127 := bstep (se 1 (by rfl) ⟨945095, by rfl⟩ : syracuseStep 1260127 = 1890191) B1890191
theorem B1489529 : Blo 992597 1489529 := bstep (se 2 (by rfl) ⟨558573, by rfl⟩ : syracuseStep 1489529 = 1117147) B1117147
theorem B1489583 : Blo 992597 1489583 := bstep (se 1 (by rfl) ⟨1117187, by rfl⟩ : syracuseStep 1489583 = 2234375) B2234375
theorem B1489631 : Blo 992597 1489631 := bstep (se 1 (by rfl) ⟨1117223, by rfl⟩ : syracuseStep 1489631 = 2234447) B2234447
theorem B1194907 : Blo 992597 1194907 := bstep (se 1 (by rfl) ⟨896180, by rfl⟩ : syracuseStep 1194907 = 1792361) B1792361
theorem B3357611 : Blo 992597 3357611 := bstep (se 1 (by rfl) ⟨2518208, by rfl⟩ : syracuseStep 3357611 = 5036417) B5036417
theorem B1489895 : Blo 992597 1489895 := bstep (se 1 (by rfl) ⟨1117421, by rfl⟩ : syracuseStep 1489895 = 2234843) B2234843
theorem B2014183 : Blo 992597 2014183 := bstep (se 1 (by rfl) ⟨1510637, by rfl⟩ : syracuseStep 2014183 = 3021275) B3021275
theorem B8076451 : Blo 992597 8076451 := bstep (se 1 (by rfl) ⟨6057338, by rfl⟩ : syracuseStep 8076451 = 12114677) B12114677
theorem B25443557 : Blo 992597 25443557 := bstep (se 4 (by rfl) ⟨2385333, by rfl⟩ : syracuseStep 25443557 = 4770667) B4770667
theorem B1490153 : Blo 992597 1490153 := bstep (se 2 (by rfl) ⟨558807, by rfl⟩ : syracuseStep 1490153 = 1117615) B1117615
theorem B1490207 : Blo 992597 1490207 := bstep (se 1 (by rfl) ⟨1117655, by rfl⟩ : syracuseStep 1490207 = 2235311) B2235311
theorem B1490375 : Blo 992597 1490375 := bstep (se 1 (by rfl) ⟨1117781, by rfl⟩ : syracuseStep 1490375 = 2235563) B2235563
theorem B3358151 : Blo 992597 3358151 := bstep (se 1 (by rfl) ⟨2518613, by rfl⟩ : syracuseStep 3358151 = 5037227) B5037227
theorem B3358475 : Blo 992597 3358475 := bstep (se 1 (by rfl) ⟨2518856, by rfl⟩ : syracuseStep 3358475 = 5037713) B5037713
theorem B1490729 : Blo 992597 1490729 := bstep (se 2 (by rfl) ⟨559023, by rfl⟩ : syracuseStep 1490729 = 1118047) B1118047
theorem B1490735 : Blo 992597 1490735 := bstep (se 1 (by rfl) ⟨1118051, by rfl⟩ : syracuseStep 1490735 = 2236103) B2236103
theorem B3358745 : Blo 992597 3358745 := bstep (se 2 (by rfl) ⟨1259529, by rfl⟩ : syracuseStep 3358745 = 2519059) B2519059
theorem B5030099 : Blo 992597 5030099 := bstep (se 1 (by rfl) ⟨3772574, by rfl⟩ : syracuseStep 5030099 = 7545149) B7545149
theorem B1491209 : Blo 992597 1491209 := bstep (se 2 (by rfl) ⟨559203, by rfl⟩ : syracuseStep 1491209 = 1118407) B1118407
theorem B1491311 : Blo 992597 1491311 := bstep (se 1 (by rfl) ⟨1118483, by rfl⟩ : syracuseStep 1491311 = 2236967) B2236967
theorem B38224385 : Blo 992597 38224385 := bstep (se 2 (by rfl) ⟨14334144, by rfl⟩ : syracuseStep 38224385 = 28668289) B28668289
theorem B1491527 : Blo 992597 1491527 := bstep (se 1 (by rfl) ⟨1118645, by rfl⟩ : syracuseStep 1491527 = 2237291) B2237291
theorem B1491563 : Blo 992597 1491563 := bstep (se 1 (by rfl) ⟨1118672, by rfl⟩ : syracuseStep 1491563 = 2237345) B2237345
theorem B4244183 : Blo 992597 4244183 := bstep (se 1 (by rfl) ⟨3183137, by rfl⟩ : syracuseStep 4244183 = 6366275) B6366275
theorem B1491791 : Blo 992597 1491791 := bstep (se 1 (by rfl) ⟨1118843, by rfl⟩ : syracuseStep 1491791 = 2237687) B2237687
theorem B1197031 : Blo 992597 1197031 := bstep (se 1 (by rfl) ⟨897773, by rfl⟩ : syracuseStep 1197031 = 1795547) B1795547
theorem B1492187 : Blo 992597 1492187 := bstep (se 1 (by rfl) ⟨1119140, by rfl⟩ : syracuseStep 1492187 = 2238281) B2238281
theorem B3359987 : Blo 992597 3359987 := bstep (se 1 (by rfl) ⟨2519990, by rfl⟩ : syracuseStep 3359987 = 5039981) B5039981
theorem B4244831 : Blo 992597 4244831 := bstep (se 1 (by rfl) ⟨3183623, by rfl⟩ : syracuseStep 4244831 = 6367247) B6367247
theorem B3360095 : Blo 992597 3360095 := bstep (se 1 (by rfl) ⟨2520071, by rfl⟩ : syracuseStep 3360095 = 5040143) B5040143
theorem B1492361 : Blo 992597 1492361 := bstep (se 2 (by rfl) ⟨559635, by rfl⟩ : syracuseStep 1492361 = 1119271) B1119271
theorem B36324773 : Blo 992597 36324773 := bstep (se 4 (by rfl) ⟨3405447, by rfl⟩ : syracuseStep 36324773 = 6810895) B6810895
theorem B2835901 : Blo 992597 2835901 := bstep (se 3 (by rfl) ⟨531731, by rfl⟩ : syracuseStep 2835901 = 1063463) B1063463
theorem B3229241 : Blo 992597 3229241 := bstep (se 2 (by rfl) ⟨1210965, by rfl⟩ : syracuseStep 3229241 = 2421931) B2421931
theorem B1492715 : Blo 992597 1492715 := bstep (se 1 (by rfl) ⟨1119536, by rfl⟩ : syracuseStep 1492715 = 2239073) B2239073
theorem B1885999 : Blo 992597 1885999 := bstep (se 1 (by rfl) ⟨1414499, by rfl⟩ : syracuseStep 1885999 = 2828999) B2828999
theorem B43599667 : Blo 992597 43599667 := bstep (se 1 (by rfl) ⟨32699750, by rfl⟩ : syracuseStep 43599667 = 65399501) B65399501
theorem B1886159 : Blo 992597 1886159 := bstep (se 1 (by rfl) ⟨1414619, by rfl⟩ : syracuseStep 1886159 = 2829239) B2829239
theorem B1492943 : Blo 992597 1492943 := bstep (se 1 (by rfl) ⟨1119707, by rfl⟩ : syracuseStep 1492943 = 2239415) B2239415
theorem B44222593 : Blo 992597 44222593 := bstep (se 2 (by rfl) ⟨16583472, by rfl⟩ : syracuseStep 44222593 = 33166945) B33166945
theorem B2836745 : Blo 992597 2836745 := bstep (se 2 (by rfl) ⟨1063779, by rfl⟩ : syracuseStep 2836745 = 2127559) B2127559
theorem B1493339 : Blo 992597 1493339 := bstep (se 1 (by rfl) ⟨1120004, by rfl⟩ : syracuseStep 1493339 = 2240009) B2240009
theorem B1493567 : Blo 992597 1493567 := bstep (se 1 (by rfl) ⟨1120175, by rfl⟩ : syracuseStep 1493567 = 2240351) B2240351
theorem B1886827 : Blo 992597 1886827 := bstep (se 1 (by rfl) ⟨1415120, by rfl⟩ : syracuseStep 1886827 = 2830241) B2830241
theorem B1493687 : Blo 992597 1493687 := bstep (se 1 (by rfl) ⟨1120265, by rfl⟩ : syracuseStep 1493687 = 2240531) B2240531
theorem B16992989 : Blo 992597 16992989 := bstep (se 3 (by rfl) ⟨3186185, by rfl⟩ : syracuseStep 16992989 = 6372371) B6372371
theorem B1362655 : Blo 992597 1362655 := bstep (se 1 (by rfl) ⟨1021991, by rfl⟩ : syracuseStep 1362655 = 2043983) B2043983
theorem B11324285 : Blo 992597 11324285 := bstep (se 3 (by rfl) ⟨2123303, by rfl⟩ : syracuseStep 11324285 = 4246607) B4246607
theorem B3361661 : Blo 992597 3361661 := bstep (se 3 (by rfl) ⟨630311, by rfl⟩ : syracuseStep 3361661 = 1260623) B1260623
theorem B1887131 : Blo 992597 1887131 := bstep (se 1 (by rfl) ⟨1415348, by rfl⟩ : syracuseStep 1887131 = 2830697) B2830697
theorem B1493915 : Blo 992597 1493915 := bstep (se 1 (by rfl) ⟨1120436, by rfl⟩ : syracuseStep 1493915 = 2240873) B2240873
theorem B3361931 : Blo 992597 3361931 := bstep (se 1 (by rfl) ⟨2521448, by rfl⟩ : syracuseStep 3361931 = 5042897) B5042897
theorem B1494311 : Blo 992597 1494311 := bstep (se 1 (by rfl) ⟨1120733, by rfl⟩ : syracuseStep 1494311 = 2241467) B2241467
theorem B4771169 : Blo 992597 4771169 := bstep (se 2 (by rfl) ⟨1789188, by rfl⟩ : syracuseStep 4771169 = 3578377) B3578377
theorem B1494395 : Blo 992597 1494395 := bstep (se 1 (by rfl) ⟨1120796, by rfl⟩ : syracuseStep 1494395 = 2241593) B2241593
theorem B3591611 : Blo 992597 3591611 := bstep (se 1 (by rfl) ⟨2693708, by rfl⟩ : syracuseStep 3591611 = 5387417) B5387417
theorem B1494521 : Blo 992597 1494521 := bstep (se 2 (by rfl) ⟨560445, by rfl⟩ : syracuseStep 1494521 = 1120891) B1120891
theorem B43667009 : Blo 992597 43667009 := bstep (se 2 (by rfl) ⟨16375128, by rfl⟩ : syracuseStep 43667009 = 32750257) B32750257
theorem B1494623 : Blo 992597 1494623 := bstep (se 1 (by rfl) ⟨1120967, by rfl⟩ : syracuseStep 1494623 = 2241935) B2241935
theorem B4247275 : Blo 992597 4247275 := bstep (se 1 (by rfl) ⟨3185456, by rfl⟩ : syracuseStep 4247275 = 6370913) B6370913
theorem B1789751 : Blo 992597 1789751 := bstep (se 1 (by rfl) ⟨1342313, by rfl⟩ : syracuseStep 1789751 = 2684627) B2684627
theorem B1494839 : Blo 992597 1494839 := bstep (se 1 (by rfl) ⟨1121129, by rfl⟩ : syracuseStep 1494839 = 2242259) B2242259
theorem B1790299 : Blo 992597 1790299 := bstep (se 1 (by rfl) ⟨1342724, by rfl⟩ : syracuseStep 1790299 = 2685449) B2685449
theorem B7557785 : Blo 992597 7557785 := bstep (se 2 (by rfl) ⟨2834169, by rfl⟩ : syracuseStep 7557785 = 5668339) B5668339
theorem B1888991 : Blo 992597 1888991 := bstep (se 1 (by rfl) ⟨1416743, by rfl⟩ : syracuseStep 1888991 = 2833487) B2833487
theorem B4248521 : Blo 992597 4248521 := bstep (se 2 (by rfl) ⟨1593195, by rfl⟩ : syracuseStep 4248521 = 3186391) B3186391
theorem B4543721 : Blo 992597 4543721 := bstep (se 2 (by rfl) ⟨1703895, by rfl⟩ : syracuseStep 4543721 = 3407791) B3407791
theorem B4773113 : Blo 992597 4773113 := bstep (se 2 (by rfl) ⟨1789917, by rfl⟩ : syracuseStep 4773113 = 3579835) B3579835
theorem B5657951 : Blo 992597 5657951 := bstep (se 1 (by rfl) ⟨4243463, by rfl⟩ : syracuseStep 5657951 = 8486927) B8486927
theorem B1889659 : Blo 992597 1889659 := bstep (se 1 (by rfl) ⟨1417244, by rfl⟩ : syracuseStep 1889659 = 2834489) B2834489
theorem B8508797 : Blo 992597 8508797 := bstep (se 3 (by rfl) ⟨1595399, by rfl⟩ : syracuseStep 8508797 = 3190799) B3190799
theorem B1889887 : Blo 992597 1889887 := bstep (se 1 (by rfl) ⟨1417415, by rfl⟩ : syracuseStep 1889887 = 2834831) B2834831
theorem B4249273 : Blo 992597 4249273 := bstep (se 2 (by rfl) ⟨1593477, by rfl⟩ : syracuseStep 4249273 = 3186955) B3186955
theorem B12736541 : Blo 992597 12736541 := bstep (se 3 (by rfl) ⟨2388101, by rfl⟩ : syracuseStep 12736541 = 4776203) B4776203
theorem B2513177 : Blo 992597 2513177 := bstep (se 2 (by rfl) ⟨942441, by rfl⟩ : syracuseStep 2513177 = 1884883) B1884883
theorem B2152777 : Blo 992597 2152777 := bstep (se 2 (by rfl) ⟨807291, by rfl⟩ : syracuseStep 2152777 = 1614583) B1614583
theorem B3824539 : Blo 992597 3824539 := bstep (se 1 (by rfl) ⟨2868404, by rfl⟩ : syracuseStep 3824539 = 5736809) B5736809
theorem B5102507 : Blo 992597 5102507 := bstep (se 1 (by rfl) ⟨3826880, by rfl⟩ : syracuseStep 5102507 = 7653761) B7653761
theorem B2514017 : Blo 992597 2514017 := bstep (se 2 (by rfl) ⟨942756, by rfl⟩ : syracuseStep 2514017 = 1885513) B1885513
theorem B2121083 : Blo 992597 2121083 := bstep (se 1 (by rfl) ⟨1590812, by rfl⟩ : syracuseStep 2121083 = 3181625) B3181625
theorem B16375391 : Blo 992597 16375391 := bstep (se 1 (by rfl) ⟨12281543, by rfl⟩ : syracuseStep 16375391 = 24563087) B24563087
theorem B2121527 : Blo 992597 2121527 := bstep (se 1 (by rfl) ⟨1591145, by rfl⟩ : syracuseStep 2121527 = 3182291) B3182291
theorem B4251649 : Blo 992597 4251649 := bstep (se 2 (by rfl) ⟨1594368, by rfl⟩ : syracuseStep 4251649 = 3188737) B3188737
theorem B30662833 : Blo 992597 30662833 := bstep (se 2 (by rfl) ⟨11498562, by rfl⟩ : syracuseStep 30662833 = 22997125) B22997125
theorem B8184017 : Blo 992597 8184017 := bstep (se 2 (by rfl) ⟨3069006, by rfl⟩ : syracuseStep 8184017 = 6138013) B6138013
theorem B17228161 : Blo 992597 17228161 := bstep (se 2 (by rfl) ⟨6460560, by rfl⟩ : syracuseStep 17228161 = 12921121) B12921121
theorem B7561673 : Blo 992597 7561673 := bstep (se 2 (by rfl) ⟨2835627, by rfl⟩ : syracuseStep 7561673 = 5671255) B5671255
theorem B2515475 : Blo 992597 2515475 := bstep (se 1 (by rfl) ⟨1886606, by rfl⟩ : syracuseStep 2515475 = 3773213) B3773213
theorem B4842155 : Blo 992597 4842155 := bstep (se 1 (by rfl) ⟨3631616, by rfl⟩ : syracuseStep 4842155 = 7263233) B7263233
theorem B10740539 : Blo 992597 10740539 := bstep (se 1 (by rfl) ⟨8055404, by rfl⟩ : syracuseStep 10740539 = 16110809) B16110809
theorem B5039009 : Blo 992597 5039009 := bstep (se 2 (by rfl) ⟨1889628, by rfl⟩ : syracuseStep 5039009 = 3779257) B3779257
theorem B2515931 : Blo 992597 2515931 := bstep (se 1 (by rfl) ⟨1886948, by rfl⟩ : syracuseStep 2515931 = 3773897) B3773897
theorem B7988321 : Blo 992597 7988321 := bstep (se 2 (by rfl) ⟨2995620, by rfl⟩ : syracuseStep 7988321 = 5991241) B5991241
theorem B2516255 : Blo 992597 2516255 := bstep (se 1 (by rfl) ⟨1887191, by rfl⟩ : syracuseStep 2516255 = 3774383) B3774383
theorem B1074751 : Blo 992597 1074751 := bstep (se 1 (by rfl) ⟨806063, by rfl⟩ : syracuseStep 1074751 = 1612127) B1612127
theorem B2516791 : Blo 992597 2516791 := bstep (se 1 (by rfl) ⟨1887593, by rfl⟩ : syracuseStep 2516791 = 3775187) B3775187
theorem B4253647 : Blo 992597 4253647 := bstep (se 1 (by rfl) ⟨3190235, by rfl⟩ : syracuseStep 4253647 = 6380471) B6380471
theorem B10217657 : Blo 992597 10217657 := bstep (se 2 (by rfl) ⟨3831621, by rfl⟩ : syracuseStep 10217657 = 7663243) B7663243
theorem B2123987 : Blo 992597 2123987 := bstep (se 1 (by rfl) ⟨1592990, by rfl⟩ : syracuseStep 2123987 = 3185981) B3185981
theorem B2517257 : Blo 992597 2517257 := bstep (se 2 (by rfl) ⟨943971, by rfl⟩ : syracuseStep 2517257 = 1887943) B1887943
theorem B4254383 : Blo 992597 4254383 := bstep (se 1 (by rfl) ⟨3190787, by rfl⟩ : syracuseStep 4254383 = 6381575) B6381575
theorem B4254707 : Blo 992597 4254707 := bstep (se 1 (by rfl) ⟨3191030, by rfl⟩ : syracuseStep 4254707 = 6382061) B6382061
theorem B5663783 : Blo 992597 5663783 := bstep (se 1 (by rfl) ⟨4247837, by rfl⟩ : syracuseStep 5663783 = 8495675) B8495675
theorem B6810763 : Blo 992597 6810763 := bstep (se 1 (by rfl) ⟨5108072, by rfl⟩ : syracuseStep 6810763 = 10216145) B10216145
theorem B2518249 : Blo 992597 2518249 := bstep (se 2 (by rfl) ⟨944343, by rfl⟩ : syracuseStep 2518249 = 1888687) B1888687
theorem B5041439 : Blo 992597 5041439 := bstep (se 1 (by rfl) ⟨3781079, by rfl⟩ : syracuseStep 5041439 = 7562159) B7562159
theorem B2518411 : Blo 992597 2518411 := bstep (se 1 (by rfl) ⟨1888808, by rfl⟩ : syracuseStep 2518411 = 3777617) B3777617
theorem B2518715 : Blo 992597 2518715 := bstep (se 1 (by rfl) ⟨1889036, by rfl⟩ : syracuseStep 2518715 = 3778073) B3778073
theorem B5664491 : Blo 992597 5664491 := bstep (se 1 (by rfl) ⟨4248368, by rfl⟩ : syracuseStep 5664491 = 8496737) B8496737
theorem B6451001 : Blo 992597 6451001 := bstep (se 2 (by rfl) ⟨2419125, by rfl⟩ : syracuseStep 6451001 = 4838251) B4838251
theorem B2683091 : Blo 992597 2683091 := bstep (se 1 (by rfl) ⟨2012318, by rfl⟩ : syracuseStep 2683091 = 4024637) B4024637
theorem B2388179 : Blo 992597 2388179 := bstep (se 1 (by rfl) ⟨1791134, by rfl⟩ : syracuseStep 2388179 = 3582269) B3582269
theorem B7566047 : Blo 992597 7566047 := bstep (se 1 (by rfl) ⟨5674535, by rfl⟩ : syracuseStep 7566047 = 11349071) B11349071
theorem B2388815 : Blo 992597 2388815 := bstep (se 1 (by rfl) ⟨1791611, by rfl⟩ : syracuseStep 2388815 = 3583223) B3583223
theorem B4256621 : Blo 992597 4256621 := bstep (se 3 (by rfl) ⟨798116, by rfl⟩ : syracuseStep 4256621 = 1596233) B1596233
theorem B8058001 : Blo 992597 8058001 := bstep (se 2 (by rfl) ⟨3021750, by rfl⟩ : syracuseStep 8058001 = 6043501) B6043501
theorem B5665949 : Blo 992597 5665949 := bstep (se 3 (by rfl) ⟨1062365, by rfl⟩ : syracuseStep 5665949 = 2124731) B2124731
theorem B2127097 : Blo 992597 2127097 := bstep (se 2 (by rfl) ⟨797661, by rfl⟩ : syracuseStep 2127097 = 1595323) B1595323
theorem B1275175 : Blo 992597 1275175 := bstep (se 1 (by rfl) ⟨956381, by rfl⟩ : syracuseStep 1275175 = 1912763) B1912763
theorem B6124895 : Blo 992597 6124895 := bstep (se 1 (by rfl) ⟨4593671, by rfl⟩ : syracuseStep 6124895 = 9187343) B9187343
theorem B2520659 : Blo 992597 2520659 := bstep (se 1 (by rfl) ⟨1890494, by rfl⟩ : syracuseStep 2520659 = 3780989) B3780989
theorem B5043869 : Blo 992597 5043869 := bstep (se 3 (by rfl) ⟨945725, by rfl⟩ : syracuseStep 5043869 = 1891451) B1891451
theorem B4782509 : Blo 992597 4782509 := bstep (se 3 (by rfl) ⟨896720, by rfl⟩ : syracuseStep 4782509 = 1793441) B1793441
theorem B2128447 : Blo 992597 2128447 := bstep (se 1 (by rfl) ⟨1596335, by rfl⟩ : syracuseStep 2128447 = 3192671) B3192671
theorem B32733829 : Blo 992597 32733829 := bstep (se 4 (by rfl) ⟨3068796, by rfl⟩ : syracuseStep 32733829 = 6137593) B6137593
theorem B5045165 : Blo 992597 5045165 := bstep (se 3 (by rfl) ⟨945968, by rfl⟩ : syracuseStep 5045165 = 1891937) B1891937
theorem B2522087 : Blo 992597 2522087 := bstep (se 1 (by rfl) ⟨1891565, by rfl⟩ : syracuseStep 2522087 = 3783131) B3783131
theorem B1277147 : Blo 992597 1277147 := bstep (se 1 (by rfl) ⟨957860, by rfl⟩ : syracuseStep 1277147 = 1915721) B1915721
theorem B4095431 : Blo 992597 4095431 := bstep (se 1 (by rfl) ⟨3071573, by rfl⟩ : syracuseStep 4095431 = 6143147) B6143147
theorem B2555351 : Blo 992597 2555351 := bstep (se 1 (by rfl) ⟨1916513, by rfl⟩ : syracuseStep 2555351 = 3833027) B3833027
theorem B25886213 : Blo 992597 25886213 := bstep (se 4 (by rfl) ⟨2426832, by rfl⟩ : syracuseStep 25886213 = 4853665) B4853665
theorem B5373449 : Blo 992597 5373449 := bstep (se 2 (by rfl) ⟨2015043, by rfl⟩ : syracuseStep 5373449 = 4030087) B4030087
theorem B1343071 : Blo 992597 1343071 := bstep (se 1 (by rfl) ⟨1007303, by rfl⟩ : syracuseStep 1343071 = 2014607) B2014607
theorem B4030249 : Blo 992597 4030249 := bstep (se 2 (by rfl) ⟨1511343, by rfl⟩ : syracuseStep 4030249 = 3022687) B3022687
theorem B5668865 : Blo 992597 5668865 := bstep (se 2 (by rfl) ⟨2125824, by rfl⟩ : syracuseStep 5668865 = 4251649) B4251649
theorem B25886735 : Blo 992597 25886735 := bstep (se 1 (by rfl) ⟨19415051, by rfl⟩ : syracuseStep 25886735 = 38830103) B38830103
theorem B8061403 : Blo 992597 8061403 := bstep (se 1 (by rfl) ⟨6046052, by rfl⟩ : syracuseStep 8061403 = 12092105) B12092105
theorem B22970881 : Blo 992597 22970881 := bstep (se 2 (by rfl) ⟨8614080, by rfl⟩ : syracuseStep 22970881 = 17228161) B17228161
theorem B24216515 : Blo 992597 24216515 := bstep (se 1 (by rfl) ⟨18162386, by rfl⟩ : syracuseStep 24216515 = 36324773) B36324773
theorem B3770009 : Blo 992597 3770009 := bstep (se 2 (by rfl) ⟨1413753, by rfl⟩ : syracuseStep 3770009 = 2827507) B2827507
theorem B3180779 : Blo 992597 3180779 := bstep (se 1 (by rfl) ⟨2385584, by rfl⟩ : syracuseStep 3180779 = 4771169) B4771169
theorem B2394407 : Blo 992597 2394407 := bstep (se 1 (by rfl) ⟨1795805, by rfl⟩ : syracuseStep 2394407 = 3591611) B3591611
theorem B58132889 : Blo 992597 58132889 := bstep (se 2 (by rfl) ⟨21799833, by rfl⟩ : syracuseStep 58132889 = 43599667) B43599667
theorem B5671529 : Blo 992597 5671529 := bstep (se 2 (by rfl) ⟨2126823, by rfl⟩ : syracuseStep 5671529 = 4253647) B4253647
theorem B1117255 : Blo 992597 1117255 := bstep (se 1 (by rfl) ⟨837941, by rfl⟩ : syracuseStep 1117255 = 1675883) B1675883
theorem B3182075 : Blo 992597 3182075 := bstep (se 1 (by rfl) ⟨2386556, by rfl⟩ : syracuseStep 3182075 = 4773113) B4773113
theorem B3771967 : Blo 992597 3771967 := bstep (se 1 (by rfl) ⟨2828975, by rfl⟩ : syracuseStep 3771967 = 5657951) B5657951
theorem B5672531 : Blo 992597 5672531 := bstep (se 1 (by rfl) ⟨4254398, by rfl⟩ : syracuseStep 5672531 = 8508797) B8508797
theorem B29429365 : Blo 992597 29429365 := bstep (se 5 (by rfl) ⟨1379501, by rfl⟩ : syracuseStep 29429365 = 2759003) B2759003
theorem B8064845 : Blo 992597 8064845 := bstep (se 3 (by rfl) ⟨1512158, by rfl⟩ : syracuseStep 8064845 = 3024317) B3024317
theorem B3772241 : Blo 992597 3772241 := bstep (se 2 (by rfl) ⟨1414590, by rfl⟩ : syracuseStep 3772241 = 2829181) B2829181
theorem B8491027 : Blo 992597 8491027 := bstep (se 1 (by rfl) ⟨6368270, by rfl⟩ : syracuseStep 8491027 = 12736541) B12736541
theorem B9081017 : Blo 992597 9081017 := bstep (se 2 (by rfl) ⟨3405381, by rfl⟩ : syracuseStep 9081017 = 6810763) B6810763
theorem B1675451 : Blo 992597 1675451 := bstep (se 1 (by rfl) ⟨1256588, by rfl⟩ : syracuseStep 1675451 = 2513177) B2513177
theorem B36803213 : Blo 992597 36803213 := bstep (se 3 (by rfl) ⟨6900602, by rfl⟩ : syracuseStep 36803213 = 13801205) B13801205
theorem B1676011 : Blo 992597 1676011 := bstep (se 1 (by rfl) ⟨1257008, by rfl⟩ : syracuseStep 1676011 = 2514017) B2514017
theorem B6361915 : Blo 992597 6361915 := bstep (se 1 (by rfl) ⟨4771436, by rfl⟩ : syracuseStep 6361915 = 9542873) B9542873
theorem B9540413 : Blo 992597 9540413 := bstep (se 3 (by rfl) ⟨1788827, by rfl⟩ : syracuseStep 9540413 = 3577655) B3577655
theorem B1414055 : Blo 992597 1414055 := bstep (se 1 (by rfl) ⟨1060541, by rfl⟩ : syracuseStep 1414055 = 2121083) B2121083
theorem B10916927 : Blo 992597 10916927 := bstep (se 1 (by rfl) ⟨8187695, by rfl⟩ : syracuseStep 10916927 = 16375391) B16375391
theorem B1414351 : Blo 992597 1414351 := bstep (se 1 (by rfl) ⟨1060763, by rfl⟩ : syracuseStep 1414351 = 2121527) B2121527
theorem B2233619 : Blo 992597 2233619 := bstep (se 1 (by rfl) ⟨1675214, by rfl⟩ : syracuseStep 2233619 = 3350429) B3350429
theorem B2233691 : Blo 992597 2233691 := bstep (se 1 (by rfl) ⟨1675268, by rfl⟩ : syracuseStep 2233691 = 3350537) B3350537
theorem B1676983 : Blo 992597 1676983 := bstep (se 1 (by rfl) ⟨1257737, by rfl⟩ : syracuseStep 1676983 = 2515475) B2515475
theorem B1120063 : Blo 992597 1120063 := bstep (se 1 (by rfl) ⟨840047, by rfl⟩ : syracuseStep 1120063 = 1680095) B1680095
theorem B2234249 : Blo 992597 2234249 := bstep (se 2 (by rfl) ⟨837843, by rfl⟩ : syracuseStep 2234249 = 1675687) B1675687
theorem B1677287 : Blo 992597 1677287 := bstep (se 1 (by rfl) ⟨1257965, by rfl⟩ : syracuseStep 1677287 = 2515931) B2515931
theorem B1120351 : Blo 992597 1120351 := bstep (se 1 (by rfl) ⟨840263, by rfl⟩ : syracuseStep 1120351 = 1680527) B1680527
theorem B2234465 : Blo 992597 2234465 := bstep (se 2 (by rfl) ⟨837924, by rfl⟩ : syracuseStep 2234465 = 1675849) B1675849
theorem B1677503 : Blo 992597 1677503 := bstep (se 1 (by rfl) ⟨1258127, by rfl⟩ : syracuseStep 1677503 = 2516255) B2516255
theorem B1678171 : Blo 992597 1678171 := bstep (se 1 (by rfl) ⟨1258628, by rfl⟩ : syracuseStep 1678171 = 2517257) B2517257
theorem B42933239 : Blo 992597 42933239 := bstep (se 1 (by rfl) ⟨32199929, by rfl⟩ : syracuseStep 42933239 = 64399859) B64399859
theorem B3775673 : Blo 992597 3775673 := bstep (se 2 (by rfl) ⟨1415877, by rfl⟩ : syracuseStep 3775673 = 2831755) B2831755
theorem B3775855 : Blo 992597 3775855 := bstep (se 1 (by rfl) ⟨2831891, by rfl⟩ : syracuseStep 3775855 = 5663783) B5663783
theorem B2235815 : Blo 992597 2235815 := bstep (se 1 (by rfl) ⟨1676861, by rfl⟩ : syracuseStep 2235815 = 3353723) B3353723
theorem B2235995 : Blo 992597 2235995 := bstep (se 1 (by rfl) ⟨1676996, by rfl⟩ : syracuseStep 2235995 = 3353993) B3353993
theorem B3350159 : Blo 992597 3350159 := bstep (se 1 (by rfl) ⟨2512619, by rfl⟩ : syracuseStep 3350159 = 5025239) B5025239
theorem B1679143 : Blo 992597 1679143 := bstep (se 1 (by rfl) ⟨1259357, by rfl⟩ : syracuseStep 1679143 = 2518715) B2518715
theorem B3776327 : Blo 992597 3776327 := bstep (se 1 (by rfl) ⟨2832245, by rfl⟩ : syracuseStep 3776327 = 5664491) B5664491
theorem B4300667 : Blo 992597 4300667 := bstep (se 1 (by rfl) ⟨3225500, by rfl⟩ : syracuseStep 4300667 = 6451001) B6451001
theorem B2236283 : Blo 992597 2236283 := bstep (se 1 (by rfl) ⟨1677212, by rfl⟩ : syracuseStep 2236283 = 3354425) B3354425
theorem B10887211 : Blo 992597 10887211 := bstep (se 1 (by rfl) ⟨8165408, by rfl⟩ : syracuseStep 10887211 = 16330817) B16330817
theorem B2236769 : Blo 992597 2236769 := bstep (se 2 (by rfl) ⟨838788, by rfl⟩ : syracuseStep 2236769 = 1677577) B1677577
theorem B1417609 : Blo 992597 1417609 := bstep (se 2 (by rfl) ⟨531603, by rfl⟩ : syracuseStep 1417609 = 1063207) B1063207
theorem B2236859 : Blo 992597 2236859 := bstep (se 1 (by rfl) ⟨1677644, by rfl⟩ : syracuseStep 2236859 = 3355289) B3355289
theorem B3940937 : Blo 992597 3940937 := bstep (se 2 (by rfl) ⟨1477851, by rfl⟩ : syracuseStep 3940937 = 2955703) B2955703
theorem B3351293 : Blo 992597 3351293 := bstep (se 3 (by rfl) ⟨628367, by rfl⟩ : syracuseStep 3351293 = 1256735) B1256735
theorem B3777299 : Blo 992597 3777299 := bstep (se 1 (by rfl) ⟨2832974, by rfl⟩ : syracuseStep 3777299 = 5665949) B5665949
theorem B1680169 : Blo 992597 1680169 := bstep (se 2 (by rfl) ⟨630063, by rfl⟩ : syracuseStep 1680169 = 1260127) B1260127
theorem B1680439 : Blo 992597 1680439 := bstep (se 1 (by rfl) ⟨1260329, by rfl⟩ : syracuseStep 1680439 = 2520659) B2520659
theorem B992667 : Blo 992597 992667 := bstep (se 1 (by rfl) ⟨744500, by rfl⟩ : syracuseStep 992667 = 1489001) B1489001
theorem B2237867 : Blo 992597 2237867 := bstep (se 1 (by rfl) ⟨1678400, by rfl⟩ : syracuseStep 2237867 = 3356801) B3356801
theorem B11478515 : Blo 992597 11478515 := bstep (se 1 (by rfl) ⟨8608886, by rfl⟩ : syracuseStep 11478515 = 17217773) B17217773
theorem B992879 : Blo 992597 992879 := bstep (se 1 (by rfl) ⟨744659, by rfl⟩ : syracuseStep 992879 = 1489319) B1489319
theorem B3188339 : Blo 992597 3188339 := bstep (se 1 (by rfl) ⟨2391254, by rfl⟩ : syracuseStep 3188339 = 4782509) B4782509
theorem B992935 : Blo 992597 992935 := bstep (se 1 (by rfl) ⟨744701, by rfl⟩ : syracuseStep 992935 = 1489403) B1489403
theorem B2238119 : Blo 992597 2238119 := bstep (se 1 (by rfl) ⟨1678589, by rfl⟩ : syracuseStep 2238119 = 3357179) B3357179
theorem B993019 : Blo 992597 993019 := bstep (se 1 (by rfl) ⟨744764, by rfl⟩ : syracuseStep 993019 = 1489529) B1489529
theorem B993055 : Blo 992597 993055 := bstep (se 1 (by rfl) ⟨744791, by rfl⟩ : syracuseStep 993055 = 1489583) B1489583
theorem B993087 : Blo 992597 993087 := bstep (se 1 (by rfl) ⟨744815, by rfl⟩ : syracuseStep 993087 = 1489631) B1489631
theorem B2238407 : Blo 992597 2238407 := bstep (se 1 (by rfl) ⟨1678805, by rfl⟩ : syracuseStep 2238407 = 3357611) B3357611
theorem B993263 : Blo 992597 993263 := bstep (se 1 (by rfl) ⟨744947, by rfl⟩ : syracuseStep 993263 = 1489895) B1489895
theorem B1681391 : Blo 992597 1681391 := bstep (se 1 (by rfl) ⟨1261043, by rfl⟩ : syracuseStep 1681391 = 2522087) B2522087
theorem B993435 : Blo 992597 993435 := bstep (se 1 (by rfl) ⟨745076, by rfl⟩ : syracuseStep 993435 = 1490153) B1490153
theorem B993471 : Blo 992597 993471 := bstep (se 1 (by rfl) ⟨745103, by rfl⟩ : syracuseStep 993471 = 1490207) B1490207
theorem B2238713 : Blo 992597 2238713 := bstep (se 2 (by rfl) ⟨839517, by rfl⟩ : syracuseStep 2238713 = 1679035) B1679035
theorem B993583 : Blo 992597 993583 := bstep (se 1 (by rfl) ⟨745187, by rfl⟩ : syracuseStep 993583 = 1490375) B1490375
theorem B2238767 : Blo 992597 2238767 := bstep (se 1 (by rfl) ⟨1679075, by rfl⟩ : syracuseStep 2238767 = 3358151) B3358151
theorem B2730287 : Blo 992597 2730287 := bstep (se 1 (by rfl) ⟨2047715, by rfl⟩ : syracuseStep 2730287 = 4095431) B4095431
theorem B3582299 : Blo 992597 3582299 := bstep (se 1 (by rfl) ⟨2686724, by rfl⟩ : syracuseStep 3582299 = 5373449) B5373449
theorem B2238983 : Blo 992597 2238983 := bstep (se 1 (by rfl) ⟨1679237, by rfl⟩ : syracuseStep 2238983 = 3358475) B3358475
theorem B993819 : Blo 992597 993819 := bstep (se 1 (by rfl) ⟨745364, by rfl⟩ : syracuseStep 993819 = 1490729) B1490729
theorem B993823 : Blo 992597 993823 := bstep (se 1 (by rfl) ⟨745367, by rfl⟩ : syracuseStep 993823 = 1490735) B1490735
theorem B2239163 : Blo 992597 2239163 := bstep (se 1 (by rfl) ⟨1679372, by rfl⟩ : syracuseStep 2239163 = 3358745) B3358745
theorem B3353399 : Blo 992597 3353399 := bstep (se 1 (by rfl) ⟨2515049, by rfl⟩ : syracuseStep 3353399 = 5030099) B5030099
theorem B994139 : Blo 992597 994139 := bstep (se 1 (by rfl) ⟨745604, by rfl⟩ : syracuseStep 994139 = 1491209) B1491209
theorem B994207 : Blo 992597 994207 := bstep (se 1 (by rfl) ⟨745655, by rfl⟩ : syracuseStep 994207 = 1491311) B1491311
theorem B994351 : Blo 992597 994351 := bstep (se 1 (by rfl) ⟨745763, by rfl⟩ : syracuseStep 994351 = 1491527) B1491527
theorem B994375 : Blo 992597 994375 := bstep (se 1 (by rfl) ⟨745781, by rfl⟩ : syracuseStep 994375 = 1491563) B1491563
theorem B2829455 : Blo 992597 2829455 := bstep (se 1 (by rfl) ⟨2122091, by rfl⟩ : syracuseStep 2829455 = 4244183) B4244183
theorem B994527 : Blo 992597 994527 := bstep (se 1 (by rfl) ⟨745895, by rfl⟩ : syracuseStep 994527 = 1491791) B1491791
theorem B18132311 : Blo 992597 18132311 := bstep (se 1 (by rfl) ⟨13599233, by rfl⟩ : syracuseStep 18132311 = 27198467) B27198467
theorem B994791 : Blo 992597 994791 := bstep (se 1 (by rfl) ⟨746093, by rfl⟩ : syracuseStep 994791 = 1492187) B1492187
theorem B2239991 : Blo 992597 2239991 := bstep (se 1 (by rfl) ⟨1679993, by rfl⟩ : syracuseStep 2239991 = 3359987) B3359987
theorem B2829887 : Blo 992597 2829887 := bstep (se 1 (by rfl) ⟨2122415, by rfl⟩ : syracuseStep 2829887 = 4244831) B4244831
theorem B2240063 : Blo 992597 2240063 := bstep (se 1 (by rfl) ⟨1680047, by rfl⟩ : syracuseStep 2240063 = 3360095) B3360095
theorem B994907 : Blo 992597 994907 := bstep (se 1 (by rfl) ⟨746180, by rfl⟩ : syracuseStep 994907 = 1492361) B1492361
theorem B29109941 : Blo 992597 29109941 := bstep (se 5 (by rfl) ⟨1364528, by rfl⟩ : syracuseStep 29109941 = 2729057) B2729057
theorem B995143 : Blo 992597 995143 := bstep (se 1 (by rfl) ⟨746357, by rfl⟩ : syracuseStep 995143 = 1492715) B1492715
theorem B1257439 : Blo 992597 1257439 := bstep (se 1 (by rfl) ⟨943079, by rfl⟩ : syracuseStep 1257439 = 1886159) B1886159
theorem B995295 : Blo 992597 995295 := bstep (se 1 (by rfl) ⟨746471, by rfl⟩ : syracuseStep 995295 = 1492943) B1492943
theorem B995559 : Blo 992597 995559 := bstep (se 1 (by rfl) ⟨746669, by rfl⟩ : syracuseStep 995559 = 1493339) B1493339
theorem B995711 : Blo 992597 995711 := bstep (se 1 (by rfl) ⟨746783, by rfl⟩ : syracuseStep 995711 = 1493567) B1493567
theorem B995791 : Blo 992597 995791 := bstep (se 1 (by rfl) ⟨746843, by rfl⟩ : syracuseStep 995791 = 1493687) B1493687
theorem B2241017 : Blo 992597 2241017 := bstep (se 2 (by rfl) ⟨840381, by rfl⟩ : syracuseStep 2241017 = 1680763) B1680763
theorem B3781201 : Blo 992597 3781201 := bstep (se 2 (by rfl) ⟨1417950, by rfl⟩ : syracuseStep 3781201 = 2835901) B2835901
theorem B7549523 : Blo 992597 7549523 := bstep (se 1 (by rfl) ⟨5662142, by rfl⟩ : syracuseStep 7549523 = 11324285) B11324285
theorem B2241107 : Blo 992597 2241107 := bstep (se 1 (by rfl) ⟨1680830, by rfl⟩ : syracuseStep 2241107 = 3361661) B3361661
theorem B1258087 : Blo 992597 1258087 := bstep (se 1 (by rfl) ⟨943565, by rfl⟩ : syracuseStep 1258087 = 1887131) B1887131
theorem B995943 : Blo 992597 995943 := bstep (se 1 (by rfl) ⟨746957, by rfl⟩ : syracuseStep 995943 = 1493915) B1493915
theorem B2241287 : Blo 992597 2241287 := bstep (se 1 (by rfl) ⟨1680965, by rfl⟩ : syracuseStep 2241287 = 3361931) B3361931
theorem B996207 : Blo 992597 996207 := bstep (se 1 (by rfl) ⟨747155, by rfl⟩ : syracuseStep 996207 = 1494311) B1494311
theorem B996263 : Blo 992597 996263 := bstep (se 1 (by rfl) ⟨747197, by rfl⟩ : syracuseStep 996263 = 1494395) B1494395
theorem B996347 : Blo 992597 996347 := bstep (se 1 (by rfl) ⟨747260, by rfl⟩ : syracuseStep 996347 = 1494521) B1494521
theorem B29111339 : Blo 992597 29111339 := bstep (se 1 (by rfl) ⟨21833504, by rfl⟩ : syracuseStep 29111339 = 43667009) B43667009
theorem B996415 : Blo 992597 996415 := bstep (se 1 (by rfl) ⟨747311, by rfl⟩ : syracuseStep 996415 = 1494623) B1494623
theorem B4240457 : Blo 992597 4240457 := bstep (se 2 (by rfl) ⟨1590171, by rfl⟩ : syracuseStep 4240457 = 3180343) B3180343
theorem B3355721 : Blo 992597 3355721 := bstep (se 2 (by rfl) ⟨1258395, by rfl⟩ : syracuseStep 3355721 = 2516791) B2516791
theorem B1193167 : Blo 992597 1193167 := bstep (se 1 (by rfl) ⟨894875, by rfl⟩ : syracuseStep 1193167 = 1789751) B1789751
theorem B996559 : Blo 992597 996559 := bstep (se 1 (by rfl) ⟨747419, by rfl⟩ : syracuseStep 996559 = 1494839) B1494839
theorem B58963457 : Blo 992597 58963457 := bstep (se 2 (by rfl) ⟨22111296, by rfl⟩ : syracuseStep 58963457 = 44222593) B44222593
theorem B3782447 : Blo 992597 3782447 := bstep (se 1 (by rfl) ⟨2836835, by rfl⟩ : syracuseStep 3782447 = 5673671) B5673671
theorem B1259327 : Blo 992597 1259327 := bstep (se 1 (by rfl) ⟨944495, by rfl⟩ : syracuseStep 1259327 = 1888991) B1888991
theorem B2832347 : Blo 992597 2832347 := bstep (se 1 (by rfl) ⟨2124260, by rfl⟩ : syracuseStep 2832347 = 4248521) B4248521
theorem B3029147 : Blo 992597 3029147 := bstep (se 1 (by rfl) ⟨2271860, by rfl⟩ : syracuseStep 3029147 = 4543721) B4543721
theorem B1489193 : Blo 992597 1489193 := bstep (se 2 (by rfl) ⟨558447, by rfl⟩ : syracuseStep 1489193 = 1116895) B1116895
theorem B1816873 : Blo 992597 1816873 := bstep (se 2 (by rfl) ⟨681327, by rfl⟩ : syracuseStep 1816873 = 1362655) B1362655
theorem B1489199 : Blo 992597 1489199 := bstep (se 1 (by rfl) ⟨1116899, by rfl⟩ : syracuseStep 1489199 = 2233799) B2233799
theorem B28686743 : Blo 992597 28686743 := bstep (se 1 (by rfl) ⟨21515057, by rfl⟩ : syracuseStep 28686743 = 43030115) B43030115
theorem B14531075 : Blo 992597 14531075 := bstep (se 1 (by rfl) ⟨10898306, by rfl⟩ : syracuseStep 14531075 = 21796613) B21796613
theorem B1489439 : Blo 992597 1489439 := bstep (se 1 (by rfl) ⟨1117079, by rfl⟩ : syracuseStep 1489439 = 2234159) B2234159
theorem B3357341 : Blo 992597 3357341 := bstep (se 3 (by rfl) ⟨629501, by rfl⟩ : syracuseStep 3357341 = 1259003) B1259003
theorem B1489823 : Blo 992597 1489823 := bstep (se 1 (by rfl) ⟨1117367, by rfl⟩ : syracuseStep 1489823 = 2234735) B2234735
theorem B1489871 : Blo 992597 1489871 := bstep (se 1 (by rfl) ⟨1117403, by rfl⟩ : syracuseStep 1489871 = 2234807) B2234807
theorem B3783631 : Blo 992597 3783631 := bstep (se 1 (by rfl) ⟨2837723, by rfl⟩ : syracuseStep 3783631 = 5675447) B5675447
theorem B3357665 : Blo 992597 3357665 := bstep (se 2 (by rfl) ⟨1259124, by rfl⟩ : syracuseStep 3357665 = 2518249) B2518249
theorem B1489961 : Blo 992597 1489961 := bstep (se 2 (by rfl) ⟨558735, by rfl⟩ : syracuseStep 1489961 = 1117471) B1117471
theorem B1489967 : Blo 992597 1489967 := bstep (se 1 (by rfl) ⟨1117475, by rfl⟩ : syracuseStep 1489967 = 2234951) B2234951
theorem B1489991 : Blo 992597 1489991 := bstep (se 1 (by rfl) ⟨1117493, by rfl⟩ : syracuseStep 1489991 = 2234987) B2234987
theorem B3357881 : Blo 992597 3357881 := bstep (se 2 (by rfl) ⟨1259205, by rfl⟩ : syracuseStep 3357881 = 2518411) B2518411
theorem B5455133 : Blo 992597 5455133 := bstep (se 3 (by rfl) ⟨1022837, by rfl⟩ : syracuseStep 5455133 = 2045675) B2045675
theorem B1490255 : Blo 992597 1490255 := bstep (se 1 (by rfl) ⟨1117691, by rfl⟩ : syracuseStep 1490255 = 2235383) B2235383
theorem B1490345 : Blo 992597 1490345 := bstep (se 2 (by rfl) ⟨558879, by rfl⟩ : syracuseStep 1490345 = 1117759) B1117759
theorem B20397541 : Blo 992597 20397541 := bstep (se 4 (by rfl) ⟨1912269, by rfl⟩ : syracuseStep 20397541 = 3824539) B3824539
theorem B1490495 : Blo 992597 1490495 := bstep (se 1 (by rfl) ⟨1117871, by rfl⟩ : syracuseStep 1490495 = 2235743) B2235743
theorem B15318845 : Blo 992597 15318845 := bstep (se 3 (by rfl) ⟨2872283, by rfl⟩ : syracuseStep 15318845 = 5744567) B5744567
theorem B1490759 : Blo 992597 1490759 := bstep (se 1 (by rfl) ⟨1118069, by rfl⟩ : syracuseStep 1490759 = 2236139) B2236139
theorem B1490843 : Blo 992597 1490843 := bstep (se 1 (by rfl) ⟨1118132, by rfl⟩ : syracuseStep 1490843 = 2236265) B2236265
theorem B7651361 : Blo 992597 7651361 := bstep (se 2 (by rfl) ⟨2869260, by rfl⟩ : syracuseStep 7651361 = 5738521) B5738521
theorem B5456011 : Blo 992597 5456011 := bstep (se 1 (by rfl) ⟨4092008, by rfl⟩ : syracuseStep 5456011 = 8184017) B8184017
theorem B3228103 : Blo 992597 3228103 := bstep (se 1 (by rfl) ⟨2421077, by rfl⟩ : syracuseStep 3228103 = 4842155) B4842155
theorem B1491407 : Blo 992597 1491407 := bstep (se 1 (by rfl) ⟨1118555, by rfl⟩ : syracuseStep 1491407 = 2237111) B2237111
theorem B1491449 : Blo 992597 1491449 := bstep (se 2 (by rfl) ⟨559293, by rfl⟩ : syracuseStep 1491449 = 1118587) B1118587
theorem B7160359 : Blo 992597 7160359 := bstep (se 1 (by rfl) ⟨5370269, by rfl⟩ : syracuseStep 7160359 = 10740539) B10740539
theorem B1491551 : Blo 992597 1491551 := bstep (se 1 (by rfl) ⟨1118663, by rfl⟩ : syracuseStep 1491551 = 2237327) B2237327
theorem B3359339 : Blo 992597 3359339 := bstep (se 1 (by rfl) ⟨2519504, by rfl⟩ : syracuseStep 3359339 = 5039009) B5039009
theorem B5325547 : Blo 992597 5325547 := bstep (se 1 (by rfl) ⟨3994160, by rfl⟩ : syracuseStep 5325547 = 7988321) B7988321
theorem B1492031 : Blo 992597 1492031 := bstep (se 1 (by rfl) ⟨1119023, by rfl⟩ : syracuseStep 1492031 = 2238047) B2238047
theorem B1492073 : Blo 992597 1492073 := bstep (se 2 (by rfl) ⟨559527, by rfl⟩ : syracuseStep 1492073 = 1119055) B1119055
theorem B3359933 : Blo 992597 3359933 := bstep (se 3 (by rfl) ⟨629987, by rfl⟩ : syracuseStep 3359933 = 1259975) B1259975
theorem B1492175 : Blo 992597 1492175 := bstep (se 1 (by rfl) ⟨1119131, by rfl⟩ : syracuseStep 1492175 = 2238263) B2238263
theorem B58967347 : Blo 992597 58967347 := bstep (se 1 (by rfl) ⟨44225510, by rfl⟩ : syracuseStep 58967347 = 88451021) B88451021
theorem B1492379 : Blo 992597 1492379 := bstep (se 1 (by rfl) ⟨1119284, by rfl⟩ : syracuseStep 1492379 = 2238569) B2238569
theorem B11322827 : Blo 992597 11322827 := bstep (se 1 (by rfl) ⟨8492120, by rfl⟩ : syracuseStep 11322827 = 16984241) B16984241
theorem B1885817 : Blo 992597 1885817 := bstep (se 2 (by rfl) ⟨707181, by rfl⟩ : syracuseStep 1885817 = 1414363) B1414363
theorem B1492601 : Blo 992597 1492601 := bstep (se 2 (by rfl) ⟨559725, by rfl⟩ : syracuseStep 1492601 = 1119451) B1119451
theorem B2836129 : Blo 992597 2836129 := bstep (se 2 (by rfl) ⟨1063548, by rfl⟩ : syracuseStep 2836129 = 2127097) B2127097
theorem B1492703 : Blo 992597 1492703 := bstep (se 1 (by rfl) ⟨1119527, by rfl⟩ : syracuseStep 1492703 = 2239055) B2239055
theorem B2836255 : Blo 992597 2836255 := bstep (se 1 (by rfl) ⟨2127191, by rfl⟩ : syracuseStep 2836255 = 4254383) B4254383
theorem B1492799 : Blo 992597 1492799 := bstep (se 1 (by rfl) ⟨1119599, by rfl⟩ : syracuseStep 1492799 = 2239199) B2239199
theorem B1492967 : Blo 992597 1492967 := bstep (se 1 (by rfl) ⟨1119725, by rfl⟩ : syracuseStep 1492967 = 2239451) B2239451
theorem B2836471 : Blo 992597 2836471 := bstep (se 1 (by rfl) ⟨2127353, by rfl⟩ : syracuseStep 2836471 = 4254707) B4254707
theorem B1492985 : Blo 992597 1492985 := bstep (se 2 (by rfl) ⟨559869, by rfl⟩ : syracuseStep 1492985 = 1119739) B1119739
theorem B1493087 : Blo 992597 1493087 := bstep (se 1 (by rfl) ⟨1119815, by rfl⟩ : syracuseStep 1493087 = 2239631) B2239631
theorem B1493147 : Blo 992597 1493147 := bstep (se 1 (by rfl) ⟨1119860, by rfl⟩ : syracuseStep 1493147 = 2239721) B2239721
theorem B1493183 : Blo 992597 1493183 := bstep (se 1 (by rfl) ⟨1119887, by rfl⟩ : syracuseStep 1493183 = 2239775) B2239775
theorem B3360959 : Blo 992597 3360959 := bstep (se 1 (by rfl) ⟨2520719, by rfl⟩ : syracuseStep 3360959 = 5041439) B5041439
theorem B1493225 : Blo 992597 1493225 := bstep (se 2 (by rfl) ⟨559959, by rfl⟩ : syracuseStep 1493225 = 1119919) B1119919
theorem B1493531 : Blo 992597 1493531 := bstep (se 1 (by rfl) ⟨1120148, by rfl⟩ : syracuseStep 1493531 = 2240297) B2240297
theorem B3590687 : Blo 992597 3590687 := bstep (se 1 (by rfl) ⟨2693015, by rfl⟩ : syracuseStep 3590687 = 5386031) B5386031
theorem B1493609 : Blo 992597 1493609 := bstep (se 2 (by rfl) ⟨560103, by rfl⟩ : syracuseStep 1493609 = 1120207) B1120207
theorem B1788727 : Blo 992597 1788727 := bstep (se 1 (by rfl) ⟨1341545, by rfl⟩ : syracuseStep 1788727 = 2683091) B2683091
theorem B1592119 : Blo 992597 1592119 := bstep (se 1 (by rfl) ⟨1194089, by rfl⟩ : syracuseStep 1592119 = 2388179) B2388179
theorem B2870369 : Blo 992597 2870369 := bstep (se 2 (by rfl) ⟨1076388, by rfl⟩ : syracuseStep 2870369 = 2152777) B2152777
theorem B1494137 : Blo 992597 1494137 := bstep (se 2 (by rfl) ⟨560301, by rfl⟩ : syracuseStep 1494137 = 1120603) B1120603
theorem B1592543 : Blo 992597 1592543 := bstep (se 1 (by rfl) ⟨1194407, by rfl⟩ : syracuseStep 1592543 = 2388815) B2388815
theorem B1494239 : Blo 992597 1494239 := bstep (se 1 (by rfl) ⟨1120679, by rfl⟩ : syracuseStep 1494239 = 2241359) B2241359
theorem B2837747 : Blo 992597 2837747 := bstep (se 1 (by rfl) ⟨2128310, by rfl⟩ : syracuseStep 2837747 = 4256621) B4256621
theorem B1494281 : Blo 992597 1494281 := bstep (se 2 (by rfl) ⟨560355, by rfl⟩ : syracuseStep 1494281 = 1120711) B1120711
theorem B1494383 : Blo 992597 1494383 := bstep (se 1 (by rfl) ⟨1120787, by rfl⟩ : syracuseStep 1494383 = 2241575) B2241575
theorem B5033339 : Blo 992597 5033339 := bstep (se 1 (by rfl) ⟨3775004, by rfl⟩ : syracuseStep 5033339 = 7550009) B7550009
theorem B2837929 : Blo 992597 2837929 := bstep (se 2 (by rfl) ⟨1064223, by rfl⟩ : syracuseStep 2837929 = 2128447) B2128447
theorem B1494503 : Blo 992597 1494503 := bstep (se 1 (by rfl) ⟨1120877, by rfl⟩ : syracuseStep 1494503 = 2241755) B2241755
theorem B4083263 : Blo 992597 4083263 := bstep (se 1 (by rfl) ⟨3062447, by rfl⟩ : syracuseStep 4083263 = 6124895) B6124895
theorem B1494635 : Blo 992597 1494635 := bstep (se 1 (by rfl) ⟨1120976, by rfl⟩ : syracuseStep 1494635 = 2241953) B2241953
theorem B1494761 : Blo 992597 1494761 := bstep (se 2 (by rfl) ⟨560535, by rfl⟩ : syracuseStep 1494761 = 1121071) B1121071
theorem B1888019 : Blo 992597 1888019 := bstep (se 1 (by rfl) ⟨1416014, by rfl⟩ : syracuseStep 1888019 = 2832029) B2832029
theorem B3362579 : Blo 992597 3362579 := bstep (se 1 (by rfl) ⟨2521934, by rfl⟩ : syracuseStep 3362579 = 5043869) B5043869
theorem B1593209 : Blo 992597 1593209 := bstep (se 2 (by rfl) ⟨597453, by rfl⟩ : syracuseStep 1593209 = 1194907) B1194907
theorem B36720701 : Blo 992597 36720701 := bstep (se 3 (by rfl) ⟨6885131, by rfl⟩ : syracuseStep 36720701 = 13770263) B13770263
theorem B10768601 : Blo 992597 10768601 := bstep (se 2 (by rfl) ⟨4038225, by rfl⟩ : syracuseStep 10768601 = 8076451) B8076451
theorem B3363443 : Blo 992597 3363443 := bstep (se 1 (by rfl) ⟨2522582, by rfl⟩ : syracuseStep 3363443 = 5045165) B5045165
theorem B4772513 : Blo 992597 4772513 := bstep (se 2 (by rfl) ⟨1789692, by rfl⟩ : syracuseStep 4772513 = 3579385) B3579385
theorem B1790761 : Blo 992597 1790761 := bstep (se 2 (by rfl) ⟨671535, by rfl⟩ : syracuseStep 1790761 = 1343071) B1343071
theorem B16962371 : Blo 992597 16962371 := bstep (se 1 (by rfl) ⟨12721778, by rfl⟩ : syracuseStep 16962371 = 25443557) B25443557
theorem B17257475 : Blo 992597 17257475 := bstep (se 1 (by rfl) ⟨12943106, by rfl⟩ : syracuseStep 17257475 = 25886213) B25886213
theorem B40883777 : Blo 992597 40883777 := bstep (se 2 (by rfl) ⟨15331416, by rfl⟩ : syracuseStep 40883777 = 30662833) B30662833
theorem B25482923 : Blo 992597 25482923 := bstep (se 1 (by rfl) ⟨19112192, by rfl⟩ : syracuseStep 25482923 = 38224385) B38224385
theorem B23615621 : Blo 992597 23615621 := bstep (se 4 (by rfl) ⟨2213964, by rfl⟩ : syracuseStep 23615621 = 4427929) B4427929
theorem B5659091 : Blo 992597 5659091 := bstep (se 1 (by rfl) ⟨4244318, by rfl⟩ : syracuseStep 5659091 = 8488637) B8488637
theorem B13589113 : Blo 992597 13589113 := bstep (se 2 (by rfl) ⟨5095917, by rfl⟩ : syracuseStep 13589113 = 10191835) B10191835
theorem B1596041 : Blo 992597 1596041 := bstep (se 2 (by rfl) ⟨598515, by rfl⟩ : syracuseStep 1596041 = 1197031) B1197031
theorem B22928021 : Blo 992597 22928021 := bstep (se 6 (by rfl) ⟨537375, by rfl⟩ : syracuseStep 22928021 = 1074751) B1074751
theorem B6380369 : Blo 992597 6380369 := bstep (se 2 (by rfl) ⟨2392638, by rfl⟩ : syracuseStep 6380369 = 4785277) B4785277
theorem B1891163 : Blo 992597 1891163 := bstep (se 1 (by rfl) ⟨1418372, by rfl⟩ : syracuseStep 1891163 = 2836745) B2836745
theorem B11328659 : Blo 992597 11328659 := bstep (se 1 (by rfl) ⟨8496494, by rfl⟩ : syracuseStep 11328659 = 16992989) B16992989
theorem B2514523 : Blo 992597 2514523 := bstep (se 1 (by rfl) ⟨1885892, by rfl⟩ : syracuseStep 2514523 = 3771785) B3771785
theorem B2514665 : Blo 992597 2514665 := bstep (se 2 (by rfl) ⟨942999, by rfl⟩ : syracuseStep 2514665 = 1885999) B1885999
theorem B5038523 : Blo 992597 5038523 := bstep (se 1 (by rfl) ⟨3778892, by rfl⟩ : syracuseStep 5038523 = 7557785) B7557785
theorem B10773101 : Blo 992597 10773101 := bstep (se 3 (by rfl) ⟨2019956, by rfl⟩ : syracuseStep 10773101 = 4039913) B4039913
theorem B5661323 : Blo 992597 5661323 := bstep (se 1 (by rfl) ⟨4245992, by rfl⟩ : syracuseStep 5661323 = 8491985) B8491985
theorem B2515769 : Blo 992597 2515769 := bstep (se 2 (by rfl) ⟨943413, by rfl⟩ : syracuseStep 2515769 = 1886827) B1886827
theorem B16966745 : Blo 992597 16966745 := bstep (se 2 (by rfl) ⟨6362529, by rfl⟩ : syracuseStep 16966745 = 12725059) B12725059
theorem B8611309 : Blo 992597 8611309 := bstep (se 3 (by rfl) ⟨1614620, by rfl⟩ : syracuseStep 8611309 = 3229241) B3229241
theorem B4253305 : Blo 992597 4253305 := bstep (se 2 (by rfl) ⟨1594989, by rfl⟩ : syracuseStep 4253305 = 3189979) B3189979
theorem B3401671 : Blo 992597 3401671 := bstep (se 1 (by rfl) ⟨2551253, by rfl⟩ : syracuseStep 3401671 = 5102507) B5102507
theorem B18114511 : Blo 992597 18114511 := bstep (se 1 (by rfl) ⟨13585883, by rfl⟩ : syracuseStep 18114511 = 27171767) B27171767
theorem B2385911 : Blo 992597 2385911 := bstep (se 1 (by rfl) ⟨1789433, by rfl⟩ : syracuseStep 2385911 = 3578867) B3578867
theorem B2517227 : Blo 992597 2517227 := bstep (se 1 (by rfl) ⟨1887920, by rfl⟩ : syracuseStep 2517227 = 3775841) B3775841
theorem B5663033 : Blo 992597 5663033 := bstep (se 2 (by rfl) ⟨2123637, by rfl⟩ : syracuseStep 5663033 = 4247275) B4247275
theorem B8612389 : Blo 992597 8612389 := bstep (se 4 (by rfl) ⟨807411, by rfl⟩ : syracuseStep 8612389 = 1614823) B1614823
theorem B7170763 : Blo 992597 7170763 := bstep (se 1 (by rfl) ⟨5378072, by rfl⟩ : syracuseStep 7170763 = 10756145) B10756145
theorem B5041115 : Blo 992597 5041115 := bstep (se 1 (by rfl) ⟨3780836, by rfl⟩ : syracuseStep 5041115 = 7561673) B7561673
theorem B2387065 : Blo 992597 2387065 := bstep (se 2 (by rfl) ⟨895149, by rfl⟩ : syracuseStep 2387065 = 1790299) B1790299
theorem B5663965 : Blo 992597 5663965 := bstep (se 3 (by rfl) ⟨1061993, by rfl⟩ : syracuseStep 5663965 = 2123987) B2123987
theorem B2518523 : Blo 992597 2518523 := bstep (se 1 (by rfl) ⟨1888892, by rfl⟩ : syracuseStep 2518523 = 3777785) B3777785
theorem B7565075 : Blo 992597 7565075 := bstep (se 1 (by rfl) ⟨5673806, by rfl⟩ : syracuseStep 7565075 = 11347613) B11347613
theorem B6811771 : Blo 992597 6811771 := bstep (se 1 (by rfl) ⟨5108828, by rfl⟩ : syracuseStep 6811771 = 10217657) B10217657
theorem B10744001 : Blo 992597 10744001 := bstep (se 2 (by rfl) ⟨4029000, by rfl⟩ : syracuseStep 10744001 = 8058001) B8058001
theorem B1700233 : Blo 992597 1700233 := bstep (se 2 (by rfl) ⟨637587, by rfl⟩ : syracuseStep 1700233 = 1275175) B1275175
theorem B7172495 : Blo 992597 7172495 := bstep (se 1 (by rfl) ⟨5379371, by rfl⟩ : syracuseStep 7172495 = 10758743) B10758743
theorem B2519545 : Blo 992597 2519545 := bstep (se 2 (by rfl) ⟨944829, by rfl⟩ : syracuseStep 2519545 = 1889659) B1889659
theorem B2519849 : Blo 992597 2519849 := bstep (se 2 (by rfl) ⟨944943, by rfl⟩ : syracuseStep 2519849 = 1889887) B1889887
theorem B5665697 : Blo 992597 5665697 := bstep (se 2 (by rfl) ⟨2124636, by rfl⟩ : syracuseStep 5665697 = 4249273) B4249273
theorem B14317195 : Blo 992597 14317195 := bstep (se 1 (by rfl) ⟨10737896, by rfl⟩ : syracuseStep 14317195 = 21475793) B21475793
theorem B5044031 : Blo 992597 5044031 := bstep (se 1 (by rfl) ⟨3783023, by rfl⟩ : syracuseStep 5044031 = 7566047) B7566047
theorem B3405725 : Blo 992597 3405725 := bstep (se 3 (by rfl) ⟨638573, by rfl⟩ : syracuseStep 3405725 = 1277147) B1277147
theorem B4782185 : Blo 992597 4782185 := bstep (se 2 (by rfl) ⟨1793319, by rfl⟩ : syracuseStep 4782185 = 3586639) B3586639
theorem B43645105 : Blo 992597 43645105 := bstep (se 2 (by rfl) ⟨16366914, by rfl⟩ : syracuseStep 43645105 = 32733829) B32733829
theorem B5667407 : Blo 992597 5667407 := bstep (se 1 (by rfl) ⟨4250555, by rfl⟩ : syracuseStep 5667407 = 8501111) B8501111
theorem B2685577 : Blo 992597 2685577 := bstep (se 2 (by rfl) ⟨1007091, by rfl⟩ : syracuseStep 2685577 = 2014183) B2014183
theorem B7174979 : Blo 992597 7174979 := bstep (se 1 (by rfl) ⟨5381234, by rfl⟩ : syracuseStep 7174979 = 10762469) B10762469
theorem B1703567 : Blo 992597 1703567 := bstep (se 1 (by rfl) ⟨1277675, by rfl⟩ : syracuseStep 1703567 = 2555351) B2555351
theorem B5373665 : Blo 992597 5373665 := bstep (se 2 (by rfl) ⟨2015124, by rfl⟩ : syracuseStep 5373665 = 4030249) B4030249
theorem B14516281 : Blo 992597 14516281 := bstep (se 2 (by rfl) ⟨5443605, by rfl⟩ : syracuseStep 14516281 = 10887211) B10887211
theorem B7274681 : Blo 992597 7274681 := bstep (se 2 (by rfl) ⟨2728005, by rfl⟩ : syracuseStep 7274681 = 5456011) B5456011
theorem B10748537 : Blo 992597 10748537 := bstep (se 2 (by rfl) ⟨4030701, by rfl⟩ : syracuseStep 10748537 = 8061403) B8061403
theorem B5671073 : Blo 992597 5671073 := bstep (se 2 (by rfl) ⟨2126652, by rfl⟩ : syracuseStep 5671073 = 4253305) B4253305
theorem B2722175 : Blo 992597 2722175 := bstep (se 1 (by rfl) ⟨2041631, by rfl⟩ : syracuseStep 2722175 = 4083263) B4083263
theorem B3770813 : Blo 992597 3770813 := bstep (se 3 (by rfl) ⟨707027, by rfl⟩ : syracuseStep 3770813 = 1414055) B1414055
theorem B5376563 : Blo 992597 5376563 := bstep (se 1 (by rfl) ⟨4032422, by rfl⟩ : syracuseStep 5376563 = 8064845) B8064845
theorem B24152681 : Blo 992597 24152681 := bstep (se 2 (by rfl) ⟨9057255, by rfl⟩ : syracuseStep 24152681 = 18114511) B18114511
theorem B24480467 : Blo 992597 24480467 := bstep (se 1 (by rfl) ⟨18360350, by rfl⟩ : syracuseStep 24480467 = 36720701) B36720701
theorem B1116967 : Blo 992597 1116967 := bstep (se 1 (by rfl) ⟨837725, by rfl⟩ : syracuseStep 1116967 = 1675451) B1675451
theorem B7179067 : Blo 992597 7179067 := bstep (se 1 (by rfl) ⟨5384300, by rfl⟩ : syracuseStep 7179067 = 10768601) B10768601
theorem B3181675 : Blo 992597 3181675 := bstep (se 1 (by rfl) ⟨2386256, by rfl⟩ : syracuseStep 3181675 = 4772513) B4772513
theorem B6360275 : Blo 992597 6360275 := bstep (se 1 (by rfl) ⟨4770206, by rfl⟩ : syracuseStep 6360275 = 9540413) B9540413
theorem B11308247 : Blo 992597 11308247 := bstep (se 1 (by rfl) ⟨8481185, by rfl⟩ : syracuseStep 11308247 = 16962371) B16962371
theorem B7277951 : Blo 992597 7277951 := bstep (se 1 (by rfl) ⟨5458463, by rfl⟩ : syracuseStep 7277951 = 10916927) B10916927
theorem B30609373 : Blo 992597 30609373 := bstep (se 3 (by rfl) ⟨5739257, by rfl⟩ : syracuseStep 30609373 = 11478515) B11478515
theorem B1118191 : Blo 992597 1118191 := bstep (se 1 (by rfl) ⟨838643, by rfl⟩ : syracuseStep 1118191 = 1677287) B1677287
theorem B1118335 : Blo 992597 1118335 := bstep (se 1 (by rfl) ⟨838751, by rfl⟩ : syracuseStep 1118335 = 1677503) B1677503
theorem B3182753 : Blo 992597 3182753 := bstep (se 2 (by rfl) ⟨1193532, by rfl⟩ : syracuseStep 3182753 = 2387065) B2387065
theorem B8491301 : Blo 992597 8491301 := bstep (se 4 (by rfl) ⟨796059, by rfl⟩ : syracuseStep 8491301 = 1592119) B1592119
theorem B3772727 : Blo 992597 3772727 := bstep (se 1 (by rfl) ⟨2829545, by rfl⟩ : syracuseStep 3772727 = 5659091) B5659091
theorem B2233439 : Blo 992597 2233439 := bstep (se 1 (by rfl) ⟨1675079, by rfl⟩ : syracuseStep 2233439 = 3350159) B3350159
theorem B1676443 : Blo 992597 1676443 := bstep (se 1 (by rfl) ⟨1257332, by rfl⟩ : syracuseStep 1676443 = 2514665) B2514665
theorem B1676585 : Blo 992597 1676585 := bstep (se 2 (by rfl) ⟨628719, by rfl⟩ : syracuseStep 1676585 = 1257439) B1257439
theorem B9082361 : Blo 992597 9082361 := bstep (se 2 (by rfl) ⟨3405885, by rfl⟩ : syracuseStep 9082361 = 6811771) B6811771
theorem B7182067 : Blo 992597 7182067 := bstep (se 1 (by rfl) ⟨5386550, by rfl⟩ : syracuseStep 7182067 = 10773101) B10773101
theorem B3774215 : Blo 992597 3774215 := bstep (se 1 (by rfl) ⟨2830661, by rfl⟩ : syracuseStep 3774215 = 5661323) B5661323
theorem B2234195 : Blo 992597 2234195 := bstep (se 1 (by rfl) ⟨1675646, by rfl⟩ : syracuseStep 2234195 = 3351293) B3351293
theorem B1677179 : Blo 992597 1677179 := bstep (se 1 (by rfl) ⟨1257884, by rfl⟩ : syracuseStep 1677179 = 2515769) B2515769
theorem B11311163 : Blo 992597 11311163 := bstep (se 1 (by rfl) ⟨8483372, by rfl⟩ : syracuseStep 11311163 = 16966745) B16966745
theorem B7280765 : Blo 992597 7280765 := bstep (se 3 (by rfl) ⟨1365143, by rfl⟩ : syracuseStep 7280765 = 2730287) B2730287
theorem B1677449 : Blo 992597 1677449 := bstep (se 2 (by rfl) ⟨629043, by rfl⟩ : syracuseStep 1677449 = 1258087) B1258087
theorem B2234681 : Blo 992597 2234681 := bstep (se 2 (by rfl) ⟨838005, by rfl⟩ : syracuseStep 2234681 = 1676011) B1676011
theorem B7543205 : Blo 992597 7543205 := bstep (se 4 (by rfl) ⟨707175, by rfl⟩ : syracuseStep 7543205 = 1414351) B1414351
theorem B1120927 : Blo 992597 1120927 := bstep (se 1 (by rfl) ⟨840695, by rfl⟩ : syracuseStep 1120927 = 1681391) B1681391
theorem B9575165 : Blo 992597 9575165 := bstep (se 3 (by rfl) ⟨1795343, by rfl⟩ : syracuseStep 9575165 = 3590687) B3590687
theorem B1678151 : Blo 992597 1678151 := bstep (se 1 (by rfl) ⟨1258613, by rfl⟩ : syracuseStep 1678151 = 2517227) B2517227
theorem B3775355 : Blo 992597 3775355 := bstep (se 1 (by rfl) ⟨2831516, by rfl⟩ : syracuseStep 3775355 = 5663033) B5663033
theorem B2235599 : Blo 992597 2235599 := bstep (se 1 (by rfl) ⟨1676699, by rfl⟩ : syracuseStep 2235599 = 3353399) B3353399
theorem B2235977 : Blo 992597 2235977 := bstep (se 2 (by rfl) ⟨838491, by rfl⟩ : syracuseStep 2235977 = 1676983) B1676983
theorem B1679015 : Blo 992597 1679015 := bstep (se 1 (by rfl) ⟨1259261, by rfl⟩ : syracuseStep 1679015 = 2518523) B2518523
theorem B19406627 : Blo 992597 19406627 := bstep (se 1 (by rfl) ⟨14554970, by rfl⟩ : syracuseStep 19406627 = 29109941) B29109941
theorem B1679899 : Blo 992597 1679899 := bstep (se 1 (by rfl) ⟨1259924, by rfl⟩ : syracuseStep 1679899 = 2519849) B2519849
theorem B3777131 : Blo 992597 3777131 := bstep (se 1 (by rfl) ⟨2832848, by rfl⟩ : syracuseStep 3777131 = 5665697) B5665697
theorem B19407559 : Blo 992597 19407559 := bstep (se 1 (by rfl) ⟨14555669, by rfl⟩ : syracuseStep 19407559 = 29111339) B29111339
theorem B2826971 : Blo 992597 2826971 := bstep (se 1 (by rfl) ⟨2120228, by rfl⟩ : syracuseStep 2826971 = 4240457) B4240457
theorem B2237147 : Blo 992597 2237147 := bstep (se 1 (by rfl) ⟨1677860, by rfl⟩ : syracuseStep 2237147 = 3355721) B3355721
theorem B3580769 : Blo 992597 3580769 := bstep (se 2 (by rfl) ⟨1342788, by rfl⟩ : syracuseStep 3580769 = 2685577) B2685577
theorem B2237561 : Blo 992597 2237561 := bstep (se 2 (by rfl) ⟨839085, by rfl⟩ : syracuseStep 2237561 = 1678171) B1678171
theorem B2270483 : Blo 992597 2270483 := bstep (se 1 (by rfl) ⟨1702862, by rfl⟩ : syracuseStep 2270483 = 3405725) B3405725
theorem B3188123 : Blo 992597 3188123 := bstep (se 1 (by rfl) ⟨2391092, by rfl⟩ : syracuseStep 3188123 = 4782185) B4782185
theorem B992795 : Blo 992597 992795 := bstep (se 1 (by rfl) ⟨744596, by rfl⟩ : syracuseStep 992795 = 1489193) B1489193
theorem B992799 : Blo 992597 992799 := bstep (se 1 (by rfl) ⟨744599, by rfl⟩ : syracuseStep 992799 = 1489199) B1489199
theorem B992959 : Blo 992597 992959 := bstep (se 1 (by rfl) ⟨744719, by rfl⟩ : syracuseStep 992959 = 1489439) B1489439
theorem B3778271 : Blo 992597 3778271 := bstep (se 1 (by rfl) ⟨2833703, by rfl⟩ : syracuseStep 3778271 = 5667407) B5667407
theorem B2238227 : Blo 992597 2238227 := bstep (se 1 (by rfl) ⟨1678670, by rfl⟩ : syracuseStep 2238227 = 3357341) B3357341
theorem B993215 : Blo 992597 993215 := bstep (se 1 (by rfl) ⟨744911, by rfl⟩ : syracuseStep 993215 = 1489823) B1489823
theorem B993247 : Blo 992597 993247 := bstep (se 1 (by rfl) ⟨744935, by rfl⟩ : syracuseStep 993247 = 1489871) B1489871
theorem B2238443 : Blo 992597 2238443 := bstep (se 1 (by rfl) ⟨1678832, by rfl⟩ : syracuseStep 2238443 = 3357665) B3357665
theorem B993307 : Blo 992597 993307 := bstep (se 1 (by rfl) ⟨744980, by rfl⟩ : syracuseStep 993307 = 1489961) B1489961
theorem B993311 : Blo 992597 993311 := bstep (se 1 (by rfl) ⟨744983, by rfl⟩ : syracuseStep 993311 = 1489967) B1489967
theorem B993327 : Blo 992597 993327 := bstep (se 1 (by rfl) ⟨744995, by rfl⟩ : syracuseStep 993327 = 1489991) B1489991
theorem B3352697 : Blo 992597 3352697 := bstep (se 2 (by rfl) ⟨1257261, by rfl⟩ : syracuseStep 3352697 = 2514523) B2514523
theorem B2238587 : Blo 992597 2238587 := bstep (se 1 (by rfl) ⟨1678940, by rfl⟩ : syracuseStep 2238587 = 3357881) B3357881
theorem B993503 : Blo 992597 993503 := bstep (se 1 (by rfl) ⟨745127, by rfl⟩ : syracuseStep 993503 = 1490255) B1490255
theorem B993563 : Blo 992597 993563 := bstep (se 1 (by rfl) ⟨745172, by rfl⟩ : syracuseStep 993563 = 1490345) B1490345
theorem B993663 : Blo 992597 993663 := bstep (se 1 (by rfl) ⟨745247, by rfl⟩ : syracuseStep 993663 = 1490495) B1490495
theorem B2238857 : Blo 992597 2238857 := bstep (se 2 (by rfl) ⟨839571, by rfl⟩ : syracuseStep 2238857 = 1679143) B1679143
theorem B3582443 : Blo 992597 3582443 := bstep (se 1 (by rfl) ⟨2686832, by rfl⟩ : syracuseStep 3582443 = 5373665) B5373665
theorem B993839 : Blo 992597 993839 := bstep (se 1 (by rfl) ⟨745379, by rfl⟩ : syracuseStep 993839 = 1490759) B1490759
theorem B993895 : Blo 992597 993895 := bstep (se 1 (by rfl) ⟨745421, by rfl⟩ : syracuseStep 993895 = 1490843) B1490843
theorem B3779243 : Blo 992597 3779243 := bstep (se 1 (by rfl) ⟨2834432, by rfl⟩ : syracuseStep 3779243 = 5668865) B5668865
theorem B994271 : Blo 992597 994271 := bstep (se 1 (by rfl) ⟨745703, by rfl⟩ : syracuseStep 994271 = 1491407) B1491407
theorem B994299 : Blo 992597 994299 := bstep (se 1 (by rfl) ⟨745724, by rfl⟩ : syracuseStep 994299 = 1491449) B1491449
theorem B994367 : Blo 992597 994367 := bstep (se 1 (by rfl) ⟨745775, by rfl⟩ : syracuseStep 994367 = 1491551) B1491551
theorem B2239559 : Blo 992597 2239559 := bstep (se 1 (by rfl) ⟨1679669, by rfl⟩ : syracuseStep 2239559 = 3359339) B3359339
theorem B4304137 : Blo 992597 4304137 := bstep (se 2 (by rfl) ⟨1614051, by rfl⟩ : syracuseStep 4304137 = 3228103) B3228103
theorem B994687 : Blo 992597 994687 := bstep (se 1 (by rfl) ⟨746015, by rfl⟩ : syracuseStep 994687 = 1492031) B1492031
theorem B9547145 : Blo 992597 9547145 := bstep (se 2 (by rfl) ⟨3580179, by rfl⟩ : syracuseStep 9547145 = 7160359) B7160359
theorem B994715 : Blo 992597 994715 := bstep (se 1 (by rfl) ⟨746036, by rfl⟩ : syracuseStep 994715 = 1492073) B1492073
theorem B2239955 : Blo 992597 2239955 := bstep (se 1 (by rfl) ⟨1679966, by rfl⟩ : syracuseStep 2239955 = 3359933) B3359933
theorem B994783 : Blo 992597 994783 := bstep (se 1 (by rfl) ⟨746087, by rfl⟩ : syracuseStep 994783 = 1492175) B1492175
theorem B994919 : Blo 992597 994919 := bstep (se 1 (by rfl) ⟨746189, by rfl⟩ : syracuseStep 994919 = 1492379) B1492379
theorem B7548551 : Blo 992597 7548551 := bstep (se 1 (by rfl) ⟨5661413, by rfl⟩ : syracuseStep 7548551 = 11322827) B11322827
theorem B2240225 : Blo 992597 2240225 := bstep (se 2 (by rfl) ⟨840084, by rfl⟩ : syracuseStep 2240225 = 1680169) B1680169
theorem B1257211 : Blo 992597 1257211 := bstep (se 1 (by rfl) ⟨942908, by rfl⟩ : syracuseStep 1257211 = 1885817) B1885817
theorem B995067 : Blo 992597 995067 := bstep (se 1 (by rfl) ⟨746300, by rfl⟩ : syracuseStep 995067 = 1492601) B1492601
theorem B995135 : Blo 992597 995135 := bstep (se 1 (by rfl) ⟨746351, by rfl⟩ : syracuseStep 995135 = 1492703) B1492703
theorem B995199 : Blo 992597 995199 := bstep (se 1 (by rfl) ⟨746399, by rfl⟩ : syracuseStep 995199 = 1492799) B1492799
theorem B995311 : Blo 992597 995311 := bstep (se 1 (by rfl) ⟨746483, by rfl⟩ : syracuseStep 995311 = 1492967) B1492967
theorem B995323 : Blo 992597 995323 := bstep (se 1 (by rfl) ⟨746492, by rfl⟩ : syracuseStep 995323 = 1492985) B1492985
theorem B995391 : Blo 992597 995391 := bstep (se 1 (by rfl) ⟨746543, by rfl⟩ : syracuseStep 995391 = 1493087) B1493087
theorem B2240585 : Blo 992597 2240585 := bstep (se 2 (by rfl) ⟨840219, by rfl⟩ : syracuseStep 2240585 = 1680439) B1680439
theorem B995431 : Blo 992597 995431 := bstep (se 1 (by rfl) ⟨746573, by rfl⟩ : syracuseStep 995431 = 1493147) B1493147
theorem B995455 : Blo 992597 995455 := bstep (se 1 (by rfl) ⟨746591, by rfl⟩ : syracuseStep 995455 = 1493183) B1493183
theorem B2240639 : Blo 992597 2240639 := bstep (se 1 (by rfl) ⟨1680479, by rfl⟩ : syracuseStep 2240639 = 3360959) B3360959
theorem B995483 : Blo 992597 995483 := bstep (se 1 (by rfl) ⟨746612, by rfl⟩ : syracuseStep 995483 = 1493225) B1493225
theorem B995687 : Blo 992597 995687 := bstep (se 1 (by rfl) ⟨746765, by rfl⟩ : syracuseStep 995687 = 1493531) B1493531
theorem B78623129 : Blo 992597 78623129 := bstep (se 2 (by rfl) ⟨29483673, by rfl⟩ : syracuseStep 78623129 = 58967347) B58967347
theorem B995739 : Blo 992597 995739 := bstep (se 1 (by rfl) ⟨746804, by rfl⟩ : syracuseStep 995739 = 1493609) B1493609
theorem B3781019 : Blo 992597 3781019 := bstep (se 1 (by rfl) ⟨2835764, by rfl⟩ : syracuseStep 3781019 = 5671529) B5671529
theorem B11481745 : Blo 992597 11481745 := bstep (se 2 (by rfl) ⟨4305654, by rfl⟩ : syracuseStep 11481745 = 8611309) B8611309
theorem B1913579 : Blo 992597 1913579 := bstep (se 1 (by rfl) ⟨1435184, by rfl⟩ : syracuseStep 1913579 = 2870369) B2870369
theorem B996091 : Blo 992597 996091 := bstep (se 1 (by rfl) ⟨747068, by rfl⟩ : syracuseStep 996091 = 1494137) B1494137
theorem B1061695 : Blo 992597 1061695 := bstep (se 1 (by rfl) ⟨796271, by rfl⟩ : syracuseStep 1061695 = 1592543) B1592543
theorem B996159 : Blo 992597 996159 := bstep (se 1 (by rfl) ⟨747119, by rfl⟩ : syracuseStep 996159 = 1494239) B1494239
theorem B996187 : Blo 992597 996187 := bstep (se 1 (by rfl) ⟨747140, by rfl⟩ : syracuseStep 996187 = 1494281) B1494281
theorem B3781505 : Blo 992597 3781505 := bstep (se 2 (by rfl) ⟨1418064, by rfl⟩ : syracuseStep 3781505 = 2836129) B2836129
theorem B996255 : Blo 992597 996255 := bstep (se 1 (by rfl) ⟨747191, by rfl⟩ : syracuseStep 996255 = 1494383) B1494383
theorem B3355559 : Blo 992597 3355559 := bstep (se 1 (by rfl) ⟨2516669, by rfl⟩ : syracuseStep 3355559 = 5033339) B5033339
theorem B996335 : Blo 992597 996335 := bstep (se 1 (by rfl) ⟨747251, by rfl⟩ : syracuseStep 996335 = 1494503) B1494503
theorem B3781673 : Blo 992597 3781673 := bstep (se 2 (by rfl) ⟨1418127, by rfl⟩ : syracuseStep 3781673 = 2836255) B2836255
theorem B3781687 : Blo 992597 3781687 := bstep (se 1 (by rfl) ⟨2836265, by rfl⟩ : syracuseStep 3781687 = 5672531) B5672531
theorem B996423 : Blo 992597 996423 := bstep (se 1 (by rfl) ⟨747317, by rfl⟩ : syracuseStep 996423 = 1494635) B1494635
theorem B996507 : Blo 992597 996507 := bstep (se 1 (by rfl) ⟨747380, by rfl⟩ : syracuseStep 996507 = 1494761) B1494761
theorem B1258679 : Blo 992597 1258679 := bstep (se 1 (by rfl) ⟨944009, by rfl⟩ : syracuseStep 1258679 = 1888019) B1888019
theorem B2241719 : Blo 992597 2241719 := bstep (se 1 (by rfl) ⟨1681289, by rfl⟩ : syracuseStep 2241719 = 3362579) B3362579
theorem B4535561 : Blo 992597 4535561 := bstep (se 2 (by rfl) ⟨1700835, by rfl⟩ : syracuseStep 4535561 = 3401671) B3401671
theorem B3781961 : Blo 992597 3781961 := bstep (se 2 (by rfl) ⟨1418235, by rfl⟩ : syracuseStep 3781961 = 2836471) B2836471
theorem B46019933 : Blo 992597 46019933 := bstep (se 3 (by rfl) ⟨8628737, by rfl⟩ : syracuseStep 46019933 = 17257475) B17257475
theorem B2242295 : Blo 992597 2242295 := bstep (se 1 (by rfl) ⟨1681721, by rfl⟩ : syracuseStep 2242295 = 3363443) B3363443
theorem B1489079 : Blo 992597 1489079 := bstep (se 1 (by rfl) ⟨1116809, by rfl⟩ : syracuseStep 1489079 = 2233619) B2233619
theorem B1489127 : Blo 992597 1489127 := bstep (se 1 (by rfl) ⟨1116845, by rfl⟩ : syracuseStep 1489127 = 2233691) B2233691
theorem B16988615 : Blo 992597 16988615 := bstep (se 1 (by rfl) ⟨12741461, by rfl⟩ : syracuseStep 16988615 = 25482923) B25482923
theorem B1489499 : Blo 992597 1489499 := bstep (se 1 (by rfl) ⟨1117124, by rfl⟩ : syracuseStep 1489499 = 2234249) B2234249
theorem B1489643 : Blo 992597 1489643 := bstep (se 1 (by rfl) ⟨1117232, by rfl⟩ : syracuseStep 1489643 = 2234465) B2234465
theorem B15743747 : Blo 992597 15743747 := bstep (se 1 (by rfl) ⟨11807810, by rfl⟩ : syracuseStep 15743747 = 23615621) B23615621
theorem B1489673 : Blo 992597 1489673 := bstep (se 2 (by rfl) ⟨558627, by rfl⟩ : syracuseStep 1489673 = 1117255) B1117255
theorem B7551953 : Blo 992597 7551953 := bstep (se 2 (by rfl) ⟨2831982, by rfl⟩ : syracuseStep 7551953 = 5663965) B5663965
theorem B1064027 : Blo 992597 1064027 := bstep (se 1 (by rfl) ⟨798020, by rfl⟩ : syracuseStep 1064027 = 1596041) B1596041
theorem B15285347 : Blo 992597 15285347 := bstep (se 1 (by rfl) ⟨11464010, by rfl⟩ : syracuseStep 15285347 = 22928021) B22928021
theorem B3783905 : Blo 992597 3783905 := bstep (se 2 (by rfl) ⟨1418964, by rfl⟩ : syracuseStep 3783905 = 2837929) B2837929
theorem B1260775 : Blo 992597 1260775 := bstep (se 1 (by rfl) ⟨945581, by rfl⟩ : syracuseStep 1260775 = 1891163) B1891163
theorem B28622159 : Blo 992597 28622159 := bstep (se 1 (by rfl) ⟨21466619, by rfl⟩ : syracuseStep 28622159 = 42933239) B42933239
theorem B5029289 : Blo 992597 5029289 := bstep (se 2 (by rfl) ⟨1885983, by rfl⟩ : syracuseStep 5029289 = 3771967) B3771967
theorem B7552439 : Blo 992597 7552439 := bstep (se 1 (by rfl) ⟨5664329, by rfl⟩ : syracuseStep 7552439 = 11328659) B11328659
theorem B39239153 : Blo 992597 39239153 := bstep (se 2 (by rfl) ⟨14714682, by rfl⟩ : syracuseStep 39239153 = 29429365) B29429365
theorem B3358205 : Blo 992597 3358205 := bstep (se 3 (by rfl) ⟨629663, by rfl⟩ : syracuseStep 3358205 = 1259327) B1259327
theorem B1490543 : Blo 992597 1490543 := bstep (se 1 (by rfl) ⟨1117907, by rfl⟩ : syracuseStep 1490543 = 2235815) B2235815
theorem B1490663 : Blo 992597 1490663 := bstep (se 1 (by rfl) ⟨1117997, by rfl⟩ : syracuseStep 1490663 = 2235995) B2235995
theorem B7552925 : Blo 992597 7552925 := bstep (se 3 (by rfl) ⟨1416173, by rfl⟩ : syracuseStep 7552925 = 2832347) B2832347
theorem B2867111 : Blo 992597 2867111 := bstep (se 1 (by rfl) ⟨2150333, by rfl⟩ : syracuseStep 2867111 = 4300667) B4300667
theorem B1490855 : Blo 992597 1490855 := bstep (se 1 (by rfl) ⟨1118141, by rfl⟩ : syracuseStep 1490855 = 2236283) B2236283
theorem B11321369 : Blo 992597 11321369 := bstep (se 2 (by rfl) ⟨4245513, by rfl⟩ : syracuseStep 11321369 = 8491027) B8491027
theorem B1491179 : Blo 992597 1491179 := bstep (se 1 (by rfl) ⟨1118384, by rfl⟩ : syracuseStep 1491179 = 2236769) B2236769
theorem B1491239 : Blo 992597 1491239 := bstep (se 1 (by rfl) ⟨1118429, by rfl⟩ : syracuseStep 1491239 = 2236859) B2236859
theorem B3359015 : Blo 992597 3359015 := bstep (se 1 (by rfl) ⟨2519261, by rfl⟩ : syracuseStep 3359015 = 5038523) B5038523
theorem B3359393 : Blo 992597 3359393 := bstep (se 2 (by rfl) ⟨1259772, by rfl⟩ : syracuseStep 3359393 = 2519545) B2519545
theorem B1491911 : Blo 992597 1491911 := bstep (se 1 (by rfl) ⟨1118933, by rfl⟩ : syracuseStep 1491911 = 2237867) B2237867
theorem B1492079 : Blo 992597 1492079 := bstep (se 1 (by rfl) ⟨1119059, by rfl⟩ : syracuseStep 1492079 = 2238119) B2238119
theorem B1492271 : Blo 992597 1492271 := bstep (se 1 (by rfl) ⟨1119203, by rfl⟩ : syracuseStep 1492271 = 2238407) B2238407
theorem B1590607 : Blo 992597 1590607 := bstep (se 1 (by rfl) ⟨1192955, by rfl⟩ : syracuseStep 1590607 = 2385911) B2385911
theorem B1492475 : Blo 992597 1492475 := bstep (se 1 (by rfl) ⟨1119356, by rfl⟩ : syracuseStep 1492475 = 2238713) B2238713
theorem B1492511 : Blo 992597 1492511 := bstep (se 1 (by rfl) ⟨1119383, by rfl⟩ : syracuseStep 1492511 = 2238767) B2238767
theorem B1590889 : Blo 992597 1590889 := bstep (se 2 (by rfl) ⟨596583, by rfl⟩ : syracuseStep 1590889 = 1193167) B1193167
theorem B1492655 : Blo 992597 1492655 := bstep (se 1 (by rfl) ⟨1119491, by rfl⟩ : syracuseStep 1492655 = 2238983) B2238983
theorem B1492775 : Blo 992597 1492775 := bstep (se 1 (by rfl) ⟨1119581, by rfl⟩ : syracuseStep 1492775 = 2239163) B2239163
theorem B3360743 : Blo 992597 3360743 := bstep (se 1 (by rfl) ⟨2520557, by rfl⟩ : syracuseStep 3360743 = 5041115) B5041115
theorem B1886303 : Blo 992597 1886303 := bstep (se 1 (by rfl) ⟨1414727, by rfl⟩ : syracuseStep 1886303 = 2829455) B2829455
theorem B19089593 : Blo 992597 19089593 := bstep (se 2 (by rfl) ⟨7158597, by rfl⟩ : syracuseStep 19089593 = 14317195) B14317195
theorem B1493327 : Blo 992597 1493327 := bstep (se 1 (by rfl) ⟨1119995, by rfl⟩ : syracuseStep 1493327 = 2239991) B2239991
theorem B1886591 : Blo 992597 1886591 := bstep (se 1 (by rfl) ⟨1414943, by rfl⟩ : syracuseStep 1886591 = 2829887) B2829887
theorem B1493375 : Blo 992597 1493375 := bstep (se 1 (by rfl) ⟨1120031, by rfl⟩ : syracuseStep 1493375 = 2240063) B2240063
theorem B1493417 : Blo 992597 1493417 := bstep (se 2 (by rfl) ⟨560031, by rfl⟩ : syracuseStep 1493417 = 1120063) B1120063
theorem B1493801 : Blo 992597 1493801 := bstep (se 2 (by rfl) ⟨560175, by rfl⟩ : syracuseStep 1493801 = 1120351) B1120351
theorem B7162667 : Blo 992597 7162667 := bstep (se 1 (by rfl) ⟨5372000, by rfl⟩ : syracuseStep 7162667 = 10744001) B10744001
theorem B1494011 : Blo 992597 1494011 := bstep (se 1 (by rfl) ⟨1120508, by rfl⟩ : syracuseStep 1494011 = 2241017) B2241017
theorem B5033015 : Blo 992597 5033015 := bstep (se 1 (by rfl) ⟨3774761, by rfl⟩ : syracuseStep 5033015 = 7549523) B7549523
theorem B1494071 : Blo 992597 1494071 := bstep (se 1 (by rfl) ⟨1120553, by rfl⟩ : syracuseStep 1494071 = 2241107) B2241107
theorem B1494191 : Blo 992597 1494191 := bstep (se 1 (by rfl) ⟨1120643, by rfl⟩ : syracuseStep 1494191 = 2241287) B2241287
theorem B39308971 : Blo 992597 39308971 := bstep (se 1 (by rfl) ⟨29481728, by rfl⟩ : syracuseStep 39308971 = 58963457) B58963457
theorem B3362687 : Blo 992597 3362687 := bstep (se 1 (by rfl) ⟨2522015, by rfl⟩ : syracuseStep 3362687 = 5044031) B5044031
theorem B2019431 : Blo 992597 2019431 := bstep (se 1 (by rfl) ⟨1514573, by rfl⟩ : syracuseStep 2019431 = 3029147) B3029147
theorem B19124495 : Blo 992597 19124495 := bstep (se 1 (by rfl) ⟨14343371, by rfl⟩ : syracuseStep 19124495 = 28686743) B28686743
theorem B9687383 : Blo 992597 9687383 := bstep (se 1 (by rfl) ⟨7265537, by rfl⟩ : syracuseStep 9687383 = 14531075) B14531075
theorem B5034473 : Blo 992597 5034473 := bstep (se 2 (by rfl) ⟨1887927, by rfl⟩ : syracuseStep 5034473 = 3775855) B3775855
theorem B4248557 : Blo 992597 4248557 := bstep (se 3 (by rfl) ⟨796604, by rfl⟩ : syracuseStep 4248557 = 1593209) B1593209
theorem B1135711 : Blo 992597 1135711 := bstep (se 1 (by rfl) ⟨851783, by rfl⟩ : syracuseStep 1135711 = 1703567) B1703567
theorem B10212563 : Blo 992597 10212563 := bstep (se 1 (by rfl) ⟨7659422, by rfl⟩ : syracuseStep 10212563 = 15318845) B15318845
theorem B17257823 : Blo 992597 17257823 := bstep (se 1 (by rfl) ⟨12943367, by rfl⟩ : syracuseStep 17257823 = 25886735) B25886735
theorem B5100907 : Blo 992597 5100907 := bstep (se 1 (by rfl) ⟨3825680, by rfl⟩ : syracuseStep 5100907 = 7651361) B7651361
theorem B1890145 : Blo 992597 1890145 := bstep (se 2 (by rfl) ⟨708804, by rfl⟩ : syracuseStep 1890145 = 1417609) B1417609
theorem B16144343 : Blo 992597 16144343 := bstep (se 1 (by rfl) ⟨12108257, by rfl⟩ : syracuseStep 16144343 = 24216515) B24216515
theorem B30627841 : Blo 992597 30627841 := bstep (se 2 (by rfl) ⟨11485440, by rfl⟩ : syracuseStep 30627841 = 22970881) B22970881
theorem B7100729 : Blo 992597 7100729 := bstep (se 2 (by rfl) ⟨2662773, by rfl⟩ : syracuseStep 7100729 = 5325547) B5325547
theorem B2513339 : Blo 992597 2513339 := bstep (se 1 (by rfl) ⟨1885004, by rfl⟩ : syracuseStep 2513339 = 3770009) B3770009
theorem B2120519 : Blo 992597 2120519 := bstep (se 1 (by rfl) ⟨1590389, by rfl⟩ : syracuseStep 2120519 = 3180779) B3180779
theorem B1596271 : Blo 992597 1596271 := bstep (se 1 (by rfl) ⟨1197203, by rfl⟩ : syracuseStep 1596271 = 2394407) B2394407
theorem B9689989 : Blo 992597 9689989 := bstep (se 4 (by rfl) ⟨908436, by rfl⟩ : syracuseStep 9689989 = 1816873) B1816873
theorem B38755259 : Blo 992597 38755259 := bstep (se 1 (by rfl) ⟨29066444, by rfl⟩ : syracuseStep 38755259 = 58132889) B58132889
theorem B1891831 : Blo 992597 1891831 := bstep (se 1 (by rfl) ⟨1418873, by rfl⟩ : syracuseStep 1891831 = 2837747) B2837747
theorem B2121383 : Blo 992597 2121383 := bstep (se 1 (by rfl) ⟨1591037, by rfl⟩ : syracuseStep 2121383 = 3182075) B3182075
theorem B2514827 : Blo 992597 2514827 := bstep (se 1 (by rfl) ⟨1886120, by rfl⟩ : syracuseStep 2514827 = 3772241) B3772241
theorem B6054011 : Blo 992597 6054011 := bstep (se 1 (by rfl) ⟨4540508, by rfl⟩ : syracuseStep 6054011 = 9081017) B9081017
theorem B45932741 : Blo 992597 45932741 := bstep (se 4 (by rfl) ⟨4306194, by rfl⟩ : syracuseStep 45932741 = 8612389) B8612389
theorem B24535475 : Blo 992597 24535475 := bstep (se 1 (by rfl) ⟨18401606, by rfl⟩ : syracuseStep 24535475 = 36803213) B36803213
theorem B9561017 : Blo 992597 9561017 := bstep (se 2 (by rfl) ⟨3585381, by rfl⟩ : syracuseStep 9561017 = 7170763) B7170763
theorem B27255851 : Blo 992597 27255851 := bstep (se 1 (by rfl) ⟨20441888, by rfl⟩ : syracuseStep 27255851 = 40883777) B40883777
theorem B2384969 : Blo 992597 2384969 := bstep (se 2 (by rfl) ⟨894363, by rfl⟩ : syracuseStep 2384969 = 1788727) B1788727
theorem B4253579 : Blo 992597 4253579 := bstep (se 1 (by rfl) ⟨3190184, by rfl⟩ : syracuseStep 4253579 = 6380369) B6380369
theorem B2517115 : Blo 992597 2517115 := bstep (se 1 (by rfl) ⟨1887836, by rfl⟩ : syracuseStep 2517115 = 3775673) B3775673
theorem B2517551 : Blo 992597 2517551 := bstep (se 1 (by rfl) ⟨1888163, by rfl⟩ : syracuseStep 2517551 = 3776327) B3776327
theorem B2518199 : Blo 992597 2518199 := bstep (se 1 (by rfl) ⟨1888649, by rfl⟩ : syracuseStep 2518199 = 3777299) B3777299
theorem B42036661 : Blo 992597 42036661 := bstep (se 5 (by rfl) ⟨1970468, by rfl⟩ : syracuseStep 42036661 = 3940937) B3940937
theorem B5041601 : Blo 992597 5041601 := bstep (se 2 (by rfl) ⟨1890600, by rfl⟩ : syracuseStep 5041601 = 3781201) B3781201
theorem B2387681 : Blo 992597 2387681 := bstep (se 2 (by rfl) ⟨895380, by rfl⟩ : syracuseStep 2387681 = 1790761) B1790761
theorem B2125559 : Blo 992597 2125559 := bstep (se 1 (by rfl) ⟨1594169, by rfl⟩ : syracuseStep 2125559 = 3188339) B3188339
theorem B8482553 : Blo 992597 8482553 := bstep (se 2 (by rfl) ⟨3180957, by rfl⟩ : syracuseStep 8482553 = 6361915) B6361915
theorem B2388199 : Blo 992597 2388199 := bstep (se 1 (by rfl) ⟨1791149, by rfl⟩ : syracuseStep 2388199 = 3582299) B3582299
theorem B12088207 : Blo 992597 12088207 := bstep (se 1 (by rfl) ⟨9066155, by rfl⟩ : syracuseStep 12088207 = 18132311) B18132311
theorem B5043383 : Blo 992597 5043383 := bstep (se 1 (by rfl) ⟨3782537, by rfl⟩ : syracuseStep 5043383 = 7565075) B7565075
theorem B36271637 : Blo 992597 36271637 := bstep (se 6 (by rfl) ⟨850116, by rfl⟩ : syracuseStep 36271637 = 1700233) B1700233
theorem B58193473 : Blo 992597 58193473 := bstep (se 2 (by rfl) ⟨21822552, by rfl⟩ : syracuseStep 58193473 = 43645105) B43645105
theorem B4781663 : Blo 992597 4781663 := bstep (se 1 (by rfl) ⟨3586247, by rfl⟩ : syracuseStep 4781663 = 7172495) B7172495
theorem B18118817 : Blo 992597 18118817 := bstep (se 2 (by rfl) ⟨6794556, by rfl⟩ : syracuseStep 18118817 = 13589113) B13589113
theorem B2521631 : Blo 992597 2521631 := bstep (se 1 (by rfl) ⟨1891223, by rfl⟩ : syracuseStep 2521631 = 3782447) B3782447
theorem B5044841 : Blo 992597 5044841 := bstep (se 2 (by rfl) ⟨1891815, by rfl⟩ : syracuseStep 5044841 = 3783631) B3783631
theorem B4783319 : Blo 992597 4783319 := bstep (se 1 (by rfl) ⟨3587489, by rfl⟩ : syracuseStep 4783319 = 7174979) B7174979
theorem B27196721 : Blo 992597 27196721 := bstep (se 2 (by rfl) ⟨10198770, by rfl⟩ : syracuseStep 27196721 = 20397541) B20397541
theorem B3636755 : Blo 992597 3636755 := bstep (se 1 (by rfl) ⟨2727566, by rfl⟩ : syracuseStep 3636755 = 5455133) B5455133
theorem B4849787 : Blo 992597 4849787 := bstep (se 1 (by rfl) ⟨3637340, by rfl⟩ : syracuseStep 4849787 = 7274681) B7274681
theorem B16320311 : Blo 992597 16320311 := bstep (se 1 (by rfl) ⟨12240233, by rfl⟩ : syracuseStep 16320311 = 24480467) B24480467
theorem B7538831 : Blo 992597 7538831 := bstep (se 1 (by rfl) ⟨5654123, by rfl⟩ : syracuseStep 7538831 = 11308247) B11308247
theorem B4851967 : Blo 992597 4851967 := bstep (se 1 (by rfl) ⟨3638975, by rfl⟩ : syracuseStep 4851967 = 7277951) B7277951
theorem B25496045 : Blo 992597 25496045 := bstep (se 3 (by rfl) ⟨4780508, by rfl⟩ : syracuseStep 25496045 = 9561017) B9561017
theorem B1346287 : Blo 992597 1346287 := bstep (se 1 (by rfl) ⟨1009715, by rfl⟩ : syracuseStep 1346287 = 2019431) B2019431
theorem B12749663 : Blo 992597 12749663 := bstep (se 1 (by rfl) ⟨9562247, by rfl⟩ : syracuseStep 12749663 = 19124495) B19124495
theorem B6359917 : Blo 992597 6359917 := bstep (se 3 (by rfl) ⟨1192484, by rfl⟩ : syracuseStep 6359917 = 2384969) B2384969
theorem B6458255 : Blo 992597 6458255 := bstep (se 1 (by rfl) ⟨4843691, by rfl⟩ : syracuseStep 6458255 = 9687383) B9687383
theorem B12094829 : Blo 992597 12094829 := bstep (se 3 (by rfl) ⟨2267780, by rfl⟩ : syracuseStep 12094829 = 4535561) B4535561
theorem B1117723 : Blo 992597 1117723 := bstep (se 1 (by rfl) ⟨838292, by rfl⟩ : syracuseStep 1117723 = 1676585) B1676585
theorem B11505215 : Blo 992597 11505215 := bstep (se 1 (by rfl) ⟨8628911, by rfl⟩ : syracuseStep 11505215 = 17257823) B17257823
theorem B9572089 : Blo 992597 9572089 := bstep (se 2 (by rfl) ⟨3589533, by rfl⟩ : syracuseStep 9572089 = 7179067) B7179067
theorem B1118119 : Blo 992597 1118119 := bstep (se 1 (by rfl) ⟨838589, by rfl⟩ : syracuseStep 1118119 = 1677179) B1677179
theorem B7540775 : Blo 992597 7540775 := bstep (se 1 (by rfl) ⟨5655581, by rfl⟩ : syracuseStep 7540775 = 11311163) B11311163
theorem B4853843 : Blo 992597 4853843 := bstep (se 1 (by rfl) ⟨3640382, by rfl⟩ : syracuseStep 4853843 = 7280765) B7280765
theorem B1118299 : Blo 992597 1118299 := bstep (se 1 (by rfl) ⟨838724, by rfl⟩ : syracuseStep 1118299 = 1677449) B1677449
theorem B1675559 : Blo 992597 1675559 := bstep (se 1 (by rfl) ⟨1256669, by rfl⟩ : syracuseStep 1675559 = 2513339) B2513339
theorem B5738849 : Blo 992597 5738849 := bstep (se 2 (by rfl) ⟨2152068, by rfl⟩ : syracuseStep 5738849 = 4304137) B4304137
theorem B1118767 : Blo 992597 1118767 := bstep (se 1 (by rfl) ⟨839075, by rfl⟩ : syracuseStep 1118767 = 1678151) B1678151
theorem B1676281 : Blo 992597 1676281 := bstep (se 2 (by rfl) ⟨628605, by rfl⟩ : syracuseStep 1676281 = 1257211) B1257211
theorem B1414255 : Blo 992597 1414255 := bstep (se 1 (by rfl) ⟨1060691, by rfl⟩ : syracuseStep 1414255 = 2121383) B2121383
theorem B1119343 : Blo 992597 1119343 := bstep (se 1 (by rfl) ⟨839507, by rfl⟩ : syracuseStep 1119343 = 1679015) B1679015
theorem B1676551 : Blo 992597 1676551 := bstep (se 1 (by rfl) ⟨1257413, by rfl⟩ : syracuseStep 1676551 = 2514827) B2514827
theorem B4036007 : Blo 992597 4036007 := bstep (se 1 (by rfl) ⟨3027005, by rfl⟩ : syracuseStep 4036007 = 6054011) B6054011
theorem B16356983 : Blo 992597 16356983 := bstep (se 1 (by rfl) ⟨12267737, by rfl⟩ : syracuseStep 16356983 = 24535475) B24535475
theorem B3184265 : Blo 992597 3184265 := bstep (se 2 (by rfl) ⟨1194099, by rfl⟩ : syracuseStep 3184265 = 2388199) B2388199
theorem B1513655 : Blo 992597 1513655 := bstep (se 1 (by rfl) ⟨1135241, by rfl⟩ : syracuseStep 1513655 = 2270483) B2270483
theorem B15308993 : Blo 992597 15308993 := bstep (se 2 (by rfl) ⟨5740872, by rfl⟩ : syracuseStep 15308993 = 11481745) B11481745
theorem B1415593 : Blo 992597 1415593 := bstep (se 2 (by rfl) ⟨530847, by rfl⟩ : syracuseStep 1415593 = 1061695) B1061695
theorem B2235131 : Blo 992597 2235131 := bstep (se 1 (by rfl) ⟨1676348, by rfl⟩ : syracuseStep 2235131 = 3352697) B3352697
theorem B2235257 : Blo 992597 2235257 := bstep (se 2 (by rfl) ⟨838221, by rfl⟩ : syracuseStep 2235257 = 1676443) B1676443
theorem B1678367 : Blo 992597 1678367 := bstep (se 1 (by rfl) ⟨1258775, by rfl⟩ : syracuseStep 1678367 = 2517551) B2517551
theorem B1678799 : Blo 992597 1678799 := bstep (se 1 (by rfl) ⟨1259099, by rfl⟩ : syracuseStep 1678799 = 2518199) B2518199
theorem B6364763 : Blo 992597 6364763 := bstep (se 1 (by rfl) ⟨4773572, by rfl⟩ : syracuseStep 6364763 = 9547145) B9547145
theorem B9576089 : Blo 992597 9576089 := bstep (se 2 (by rfl) ⟨3591033, by rfl⟩ : syracuseStep 9576089 = 7182067) B7182067
theorem B40837121 : Blo 992597 40837121 := bstep (se 2 (by rfl) ⟨15313920, by rfl⟩ : syracuseStep 40837121 = 30627841) B30627841
theorem B2237039 : Blo 992597 2237039 := bstep (se 1 (by rfl) ⟨1677779, by rfl⟩ : syracuseStep 2237039 = 3355559) B3355559
theorem B30679955 : Blo 992597 30679955 := bstep (se 1 (by rfl) ⟨23009966, by rfl⟩ : syracuseStep 30679955 = 46019933) B46019933
theorem B3187775 : Blo 992597 3187775 := bstep (se 1 (by rfl) ⟨2390831, by rfl⟩ : syracuseStep 3187775 = 4781663) B4781663
theorem B12919985 : Blo 992597 12919985 := bstep (se 2 (by rfl) ⟨4844994, by rfl⟩ : syracuseStep 12919985 = 9689989) B9689989
theorem B992719 : Blo 992597 992719 := bstep (se 1 (by rfl) ⟨744539, by rfl⟩ : syracuseStep 992719 = 1489079) B1489079
theorem B992751 : Blo 992597 992751 := bstep (se 1 (by rfl) ⟨744563, by rfl⟩ : syracuseStep 992751 = 1489127) B1489127
theorem B1681033 : Blo 992597 1681033 := bstep (se 2 (by rfl) ⟨630387, by rfl⟩ : syracuseStep 1681033 = 1260775) B1260775
theorem B1681087 : Blo 992597 1681087 := bstep (se 1 (by rfl) ⟨1260815, by rfl⟩ : syracuseStep 1681087 = 2521631) B2521631
theorem B992999 : Blo 992597 992999 := bstep (se 1 (by rfl) ⟨744749, by rfl⟩ : syracuseStep 992999 = 1489499) B1489499
theorem B993095 : Blo 992597 993095 := bstep (se 1 (by rfl) ⟨744821, by rfl⟩ : syracuseStep 993095 = 1489643) B1489643
theorem B10495831 : Blo 992597 10495831 := bstep (se 1 (by rfl) ⟨7871873, by rfl⟩ : syracuseStep 10495831 = 15743747) B15743747
theorem B993115 : Blo 992597 993115 := bstep (se 1 (by rfl) ⟨744836, by rfl⟩ : syracuseStep 993115 = 1489673) B1489673
theorem B3188879 : Blo 992597 3188879 := bstep (se 1 (by rfl) ⟨2391659, by rfl⟩ : syracuseStep 3188879 = 4783319) B4783319
theorem B18131147 : Blo 992597 18131147 := bstep (se 1 (by rfl) ⟨13598360, by rfl⟩ : syracuseStep 18131147 = 27196721) B27196721
theorem B19081439 : Blo 992597 19081439 := bstep (se 1 (by rfl) ⟨14311079, by rfl⟩ : syracuseStep 19081439 = 28622159) B28622159
theorem B3352859 : Blo 992597 3352859 := bstep (se 1 (by rfl) ⟨2514644, by rfl⟩ : syracuseStep 3352859 = 5029289) B5029289
theorem B26159435 : Blo 992597 26159435 := bstep (se 1 (by rfl) ⟨19619576, by rfl⟩ : syracuseStep 26159435 = 39239153) B39239153
theorem B2238803 : Blo 992597 2238803 := bstep (se 1 (by rfl) ⟨1679102, by rfl⟩ : syracuseStep 2238803 = 3358205) B3358205
theorem B993695 : Blo 992597 993695 := bstep (se 1 (by rfl) ⟨745271, by rfl⟩ : syracuseStep 993695 = 1490543) B1490543
theorem B993775 : Blo 992597 993775 := bstep (se 1 (by rfl) ⟨745331, by rfl⟩ : syracuseStep 993775 = 1490663) B1490663
theorem B1911407 : Blo 992597 1911407 := bstep (se 1 (by rfl) ⟨1433555, by rfl⟩ : syracuseStep 1911407 = 2867111) B2867111
theorem B993903 : Blo 992597 993903 := bstep (se 1 (by rfl) ⟨745427, by rfl⟩ : syracuseStep 993903 = 1490855) B1490855
theorem B7547579 : Blo 992597 7547579 := bstep (se 1 (by rfl) ⟨5660684, by rfl⟩ : syracuseStep 7547579 = 11321369) B11321369
theorem B994119 : Blo 992597 994119 := bstep (se 1 (by rfl) ⟨745589, by rfl⟩ : syracuseStep 994119 = 1491179) B1491179
theorem B994159 : Blo 992597 994159 := bstep (se 1 (by rfl) ⟨745619, by rfl⟩ : syracuseStep 994159 = 1491239) B1491239
theorem B2239343 : Blo 992597 2239343 := bstep (se 1 (by rfl) ⟨1679507, by rfl⟩ : syracuseStep 2239343 = 3359015) B3359015
theorem B2239595 : Blo 992597 2239595 := bstep (se 1 (by rfl) ⟨1679696, by rfl⟩ : syracuseStep 2239595 = 3359393) B3359393
theorem B994607 : Blo 992597 994607 := bstep (se 1 (by rfl) ⟨745955, by rfl⟩ : syracuseStep 994607 = 1491911) B1491911
theorem B2239865 : Blo 992597 2239865 := bstep (se 2 (by rfl) ⟨839949, by rfl⟩ : syracuseStep 2239865 = 1679899) B1679899
theorem B994719 : Blo 992597 994719 := bstep (se 1 (by rfl) ⟨746039, by rfl⟩ : syracuseStep 994719 = 1492079) B1492079
theorem B994847 : Blo 992597 994847 := bstep (se 1 (by rfl) ⟨746135, by rfl⟩ : syracuseStep 994847 = 1492271) B1492271
theorem B994983 : Blo 992597 994983 := bstep (se 1 (by rfl) ⟨746237, by rfl⟩ : syracuseStep 994983 = 1492475) B1492475
theorem B995007 : Blo 992597 995007 := bstep (se 1 (by rfl) ⟨746255, by rfl⟩ : syracuseStep 995007 = 1492511) B1492511
theorem B995103 : Blo 992597 995103 := bstep (se 1 (by rfl) ⟨746327, by rfl⟩ : syracuseStep 995103 = 1492655) B1492655
theorem B995183 : Blo 992597 995183 := bstep (se 1 (by rfl) ⟨746387, by rfl⟩ : syracuseStep 995183 = 1492775) B1492775
theorem B2240495 : Blo 992597 2240495 := bstep (se 1 (by rfl) ⟨1680371, by rfl⟩ : syracuseStep 2240495 = 3360743) B3360743
theorem B1257535 : Blo 992597 1257535 := bstep (se 1 (by rfl) ⟨943151, by rfl⟩ : syracuseStep 1257535 = 1886303) B1886303
theorem B3780715 : Blo 992597 3780715 := bstep (se 1 (by rfl) ⟨2835536, by rfl⟩ : syracuseStep 3780715 = 5671073) B5671073
theorem B12726395 : Blo 992597 12726395 := bstep (se 1 (by rfl) ⟨9544796, by rfl⟩ : syracuseStep 12726395 = 19089593) B19089593
theorem B995551 : Blo 992597 995551 := bstep (se 1 (by rfl) ⟨746663, by rfl⟩ : syracuseStep 995551 = 1493327) B1493327
theorem B1814783 : Blo 992597 1814783 := bstep (se 1 (by rfl) ⟨1361087, by rfl⟩ : syracuseStep 1814783 = 2722175) B2722175
theorem B995583 : Blo 992597 995583 := bstep (se 1 (by rfl) ⟨746687, by rfl⟩ : syracuseStep 995583 = 1493375) B1493375
theorem B995611 : Blo 992597 995611 := bstep (se 1 (by rfl) ⟨746708, by rfl⟩ : syracuseStep 995611 = 1493417) B1493417
theorem B3584375 : Blo 992597 3584375 := bstep (se 1 (by rfl) ⟨2688281, by rfl⟩ : syracuseStep 3584375 = 5376563) B5376563
theorem B16101787 : Blo 992597 16101787 := bstep (se 1 (by rfl) ⟨12076340, by rfl⟩ : syracuseStep 16101787 = 24152681) B24152681
theorem B995867 : Blo 992597 995867 := bstep (se 1 (by rfl) ⟨746900, by rfl⟩ : syracuseStep 995867 = 1493801) B1493801
theorem B996007 : Blo 992597 996007 := bstep (se 1 (by rfl) ⟨747005, by rfl⟩ : syracuseStep 996007 = 1494011) B1494011
theorem B3355343 : Blo 992597 3355343 := bstep (se 1 (by rfl) ⟨2516507, by rfl⟩ : syracuseStep 3355343 = 5033015) B5033015
theorem B996047 : Blo 992597 996047 := bstep (se 1 (by rfl) ⟨747035, by rfl⟩ : syracuseStep 996047 = 1494071) B1494071
theorem B996127 : Blo 992597 996127 := bstep (se 1 (by rfl) ⟨747095, by rfl⟩ : syracuseStep 996127 = 1494191) B1494191
theorem B4240183 : Blo 992597 4240183 := bstep (se 1 (by rfl) ⟨3180137, by rfl⟩ : syracuseStep 4240183 = 6360275) B6360275
theorem B2241791 : Blo 992597 2241791 := bstep (se 1 (by rfl) ⟨1681343, by rfl⟩ : syracuseStep 2241791 = 3362687) B3362687
theorem B3356153 : Blo 992597 3356153 := bstep (se 2 (by rfl) ⟨1258557, by rfl⟩ : syracuseStep 3356153 = 2517115) B2517115
theorem B3356315 : Blo 992597 3356315 := bstep (se 1 (by rfl) ⟨2517236, by rfl⟩ : syracuseStep 3356315 = 5034473) B5034473
theorem B3356477 : Blo 992597 3356477 := bstep (se 3 (by rfl) ⟨629339, by rfl⟩ : syracuseStep 3356477 = 1258679) B1258679
theorem B2832371 : Blo 992597 2832371 := bstep (se 1 (by rfl) ⟨2124278, by rfl⟩ : syracuseStep 2832371 = 4248557) B4248557
theorem B1488959 : Blo 992597 1488959 := bstep (se 1 (by rfl) ⟨1116719, by rfl⟩ : syracuseStep 1488959 = 2233439) B2233439
theorem B1489289 : Blo 992597 1489289 := bstep (se 2 (by rfl) ⟨558483, by rfl⟩ : syracuseStep 1489289 = 1116967) B1116967
theorem B1489463 : Blo 992597 1489463 := bstep (se 1 (by rfl) ⟨1117097, by rfl⟩ : syracuseStep 1489463 = 2234195) B2234195
theorem B10762895 : Blo 992597 10762895 := bstep (se 1 (by rfl) ⟨8072171, by rfl⟩ : syracuseStep 10762895 = 16144343) B16144343
theorem B4242233 : Blo 992597 4242233 := bstep (se 2 (by rfl) ⟨1590837, by rfl⟩ : syracuseStep 4242233 = 3181675) B3181675
theorem B1489787 : Blo 992597 1489787 := bstep (se 1 (by rfl) ⟨1117340, by rfl⟩ : syracuseStep 1489787 = 2234681) B2234681
theorem B4733819 : Blo 992597 4733819 := bstep (se 1 (by rfl) ⟨3550364, by rfl⟩ : syracuseStep 4733819 = 7100729) B7100729
theorem B5028803 : Blo 992597 5028803 := bstep (se 1 (by rfl) ⟨3771602, by rfl⟩ : syracuseStep 5028803 = 7543205) B7543205
theorem B56048881 : Blo 992597 56048881 := bstep (se 2 (by rfl) ⟨21018330, by rfl⟩ : syracuseStep 56048881 = 42036661) B42036661
theorem B25836839 : Blo 992597 25836839 := bstep (se 1 (by rfl) ⟨19377629, by rfl⟩ : syracuseStep 25836839 = 38755259) B38755259
theorem B64470437 : Blo 992597 64470437 := bstep (se 4 (by rfl) ⟨6044103, by rfl⟩ : syracuseStep 64470437 = 12088207) B12088207
theorem B1490399 : Blo 992597 1490399 := bstep (se 1 (by rfl) ⟨1117799, by rfl⟩ : syracuseStep 1490399 = 2235599) B2235599
theorem B52411961 : Blo 992597 52411961 := bstep (se 2 (by rfl) ⟨19654485, by rfl⟩ : syracuseStep 52411961 = 39308971) B39308971
theorem B1490651 : Blo 992597 1490651 := bstep (se 1 (by rfl) ⟨1117988, by rfl⟩ : syracuseStep 1490651 = 2235977) B2235977
theorem B40812497 : Blo 992597 40812497 := bstep (se 2 (by rfl) ⟨15304686, by rfl⟩ : syracuseStep 40812497 = 30609373) B30609373
theorem B1490921 : Blo 992597 1490921 := bstep (se 2 (by rfl) ⟨559095, by rfl⟩ : syracuseStep 1490921 = 1118191) B1118191
theorem B30621827 : Blo 992597 30621827 := bstep (se 1 (by rfl) ⟨22966370, by rfl⟩ : syracuseStep 30621827 = 45932741) B45932741
theorem B1491113 : Blo 992597 1491113 := bstep (se 2 (by rfl) ⟨559167, by rfl⟩ : syracuseStep 1491113 = 1118335) B1118335
theorem B1884647 : Blo 992597 1884647 := bstep (se 1 (by rfl) ⟨1413485, by rfl⟩ : syracuseStep 1884647 = 2826971) B2826971
theorem B1491431 : Blo 992597 1491431 := bstep (se 1 (by rfl) ⟨1118573, by rfl⟩ : syracuseStep 1491431 = 2237147) B2237147
theorem B18170567 : Blo 992597 18170567 := bstep (se 1 (by rfl) ⟨13627925, by rfl⟩ : syracuseStep 18170567 = 27255851) B27255851
theorem B1491707 : Blo 992597 1491707 := bstep (se 1 (by rfl) ⟨1118780, by rfl⟩ : syracuseStep 1491707 = 2237561) B2237561
theorem B5030909 : Blo 992597 5030909 := bstep (se 3 (by rfl) ⟨943295, by rfl⟩ : syracuseStep 5030909 = 1886591) B1886591
theorem B1492151 : Blo 992597 1492151 := bstep (se 1 (by rfl) ⟨1119113, by rfl⟩ : syracuseStep 1492151 = 2238227) B2238227
theorem B2835719 : Blo 992597 2835719 := bstep (se 1 (by rfl) ⟨2126789, by rfl⟩ : syracuseStep 2835719 = 4253579) B4253579
theorem B1492295 : Blo 992597 1492295 := bstep (se 1 (by rfl) ⟨1119221, by rfl⟩ : syracuseStep 1492295 = 2238443) B2238443
theorem B1492391 : Blo 992597 1492391 := bstep (se 1 (by rfl) ⟨1119293, by rfl⟩ : syracuseStep 1492391 = 2238587) B2238587
theorem B1492571 : Blo 992597 1492571 := bstep (se 1 (by rfl) ⟨1119428, by rfl⟩ : syracuseStep 1492571 = 2238857) B2238857
theorem B6801209 : Blo 992597 6801209 := bstep (se 2 (by rfl) ⟨2550453, by rfl⟩ : syracuseStep 6801209 = 5100907) B5100907
theorem B1493039 : Blo 992597 1493039 := bstep (se 1 (by rfl) ⟨1119779, by rfl⟩ : syracuseStep 1493039 = 2239559) B2239559
theorem B5654717 : Blo 992597 5654717 := bstep (se 3 (by rfl) ⟨1060259, by rfl⟩ : syracuseStep 5654717 = 2120519) B2120519
theorem B3361067 : Blo 992597 3361067 := bstep (se 1 (by rfl) ⟨2520800, by rfl⟩ : syracuseStep 3361067 = 5041601) B5041601
theorem B1493303 : Blo 992597 1493303 := bstep (se 1 (by rfl) ⟨1119977, by rfl⟩ : syracuseStep 1493303 = 2239955) B2239955
theorem B5032367 : Blo 992597 5032367 := bstep (se 1 (by rfl) ⟨3774275, by rfl⟩ : syracuseStep 5032367 = 7548551) B7548551
theorem B1591787 : Blo 992597 1591787 := bstep (se 1 (by rfl) ⟨1193840, by rfl⟩ : syracuseStep 1591787 = 2387681) B2387681
theorem B1493483 : Blo 992597 1493483 := bstep (se 1 (by rfl) ⟨1120112, by rfl⟩ : syracuseStep 1493483 = 2240225) B2240225
theorem B5655035 : Blo 992597 5655035 := bstep (se 1 (by rfl) ⟨4241276, by rfl⟩ : syracuseStep 5655035 = 8482553) B8482553
theorem B1493723 : Blo 992597 1493723 := bstep (se 1 (by rfl) ⟨1120292, by rfl⟩ : syracuseStep 1493723 = 2240585) B2240585
theorem B1493759 : Blo 992597 1493759 := bstep (se 1 (by rfl) ⟨1120319, by rfl⟩ : syracuseStep 1493759 = 2240639) B2240639
theorem B2837405 : Blo 992597 2837405 := bstep (se 3 (by rfl) ⟨532013, by rfl⟩ : syracuseStep 2837405 = 1064027) B1064027
theorem B52415419 : Blo 992597 52415419 := bstep (se 1 (by rfl) ⟨39311564, by rfl⟩ : syracuseStep 52415419 = 78623129) B78623129
theorem B3362255 : Blo 992597 3362255 := bstep (se 1 (by rfl) ⟨2521691, by rfl⟩ : syracuseStep 3362255 = 5043383) B5043383
theorem B1494479 : Blo 992597 1494479 := bstep (se 1 (by rfl) ⟨1120859, by rfl⟩ : syracuseStep 1494479 = 2241719) B2241719
theorem B1494569 : Blo 992597 1494569 := bstep (se 2 (by rfl) ⟨560463, by rfl⟩ : syracuseStep 1494569 = 1120927) B1120927
theorem B1494863 : Blo 992597 1494863 := bstep (se 1 (by rfl) ⟨1121147, by rfl⟩ : syracuseStep 1494863 = 2242295) B2242295
theorem B12079211 : Blo 992597 12079211 := bstep (se 1 (by rfl) ⟨9059408, by rfl⟩ : syracuseStep 12079211 = 18118817) B18118817
theorem B11325743 : Blo 992597 11325743 := bstep (se 1 (by rfl) ⟨8494307, by rfl⟩ : syracuseStep 11325743 = 16988615) B16988615
theorem B3363227 : Blo 992597 3363227 := bstep (se 1 (by rfl) ⟨2522420, by rfl⟩ : syracuseStep 3363227 = 5044841) B5044841
theorem B5034635 : Blo 992597 5034635 := bstep (se 1 (by rfl) ⟨3775976, by rfl⟩ : syracuseStep 5034635 = 7551953) B7551953
theorem B5034959 : Blo 992597 5034959 := bstep (se 1 (by rfl) ⟨3776219, by rfl⟩ : syracuseStep 5034959 = 7552439) B7552439
theorem B5035283 : Blo 992597 5035283 := bstep (se 1 (by rfl) ⟨3776462, by rfl⟩ : syracuseStep 5035283 = 7552925) B7552925
theorem B19355041 : Blo 992597 19355041 := bstep (se 2 (by rfl) ⟨7258140, by rfl⟩ : syracuseStep 19355041 = 14516281) B14516281
theorem B7165691 : Blo 992597 7165691 := bstep (se 1 (by rfl) ⟨5374268, by rfl⟩ : syracuseStep 7165691 = 10748537) B10748537
theorem B25876745 : Blo 992597 25876745 := bstep (se 2 (by rfl) ⟨9703779, by rfl⟩ : syracuseStep 25876745 = 19407559) B19407559
theorem B2513875 : Blo 992597 2513875 := bstep (se 1 (by rfl) ⟨1885406, by rfl⟩ : syracuseStep 2513875 = 3770813) B3770813
theorem B4775111 : Blo 992597 4775111 := bstep (se 1 (by rfl) ⟨3581333, by rfl⟩ : syracuseStep 4775111 = 7162667) B7162667
theorem B2121185 : Blo 992597 2121185 := bstep (se 2 (by rfl) ⟨795444, by rfl⟩ : syracuseStep 2121185 = 1590889) B1590889
theorem B2121835 : Blo 992597 2121835 := bstep (se 1 (by rfl) ⟨1591376, by rfl⟩ : syracuseStep 2121835 = 3182753) B3182753
theorem B5660867 : Blo 992597 5660867 := bstep (se 1 (by rfl) ⟨4245650, by rfl⟩ : syracuseStep 5660867 = 8491301) B8491301
theorem B2515151 : Blo 992597 2515151 := bstep (se 1 (by rfl) ⟨1886363, by rfl⟩ : syracuseStep 2515151 = 3772727) B3772727
theorem B6808375 : Blo 992597 6808375 := bstep (se 1 (by rfl) ⟨5106281, by rfl⟩ : syracuseStep 6808375 = 10212563) B10212563
theorem B6054907 : Blo 992597 6054907 := bstep (se 1 (by rfl) ⟨4541180, by rfl⟩ : syracuseStep 6054907 = 9082361) B9082361
theorem B2516143 : Blo 992597 2516143 := bstep (se 1 (by rfl) ⟨1887107, by rfl⟩ : syracuseStep 2516143 = 3774215) B3774215
theorem B6383443 : Blo 992597 6383443 := bstep (se 1 (by rfl) ⟨4787582, by rfl⟩ : syracuseStep 6383443 = 9575165) B9575165
theorem B2516903 : Blo 992597 2516903 := bstep (se 1 (by rfl) ⟨1887677, by rfl⟩ : syracuseStep 2516903 = 3775355) B3775355
theorem B12937751 : Blo 992597 12937751 := bstep (se 1 (by rfl) ⟨9703313, by rfl⟩ : syracuseStep 12937751 = 19406627) B19406627
theorem B2518087 : Blo 992597 2518087 := bstep (se 1 (by rfl) ⟨1888565, by rfl⟩ : syracuseStep 2518087 = 3777131) B3777131
theorem B6057125 : Blo 992597 6057125 := bstep (se 4 (by rfl) ⟨567855, by rfl⟩ : syracuseStep 6057125 = 1135711) B1135711
theorem B2387179 : Blo 992597 2387179 := bstep (se 1 (by rfl) ⟨1790384, by rfl⟩ : syracuseStep 2387179 = 3580769) B3580769
theorem B2125415 : Blo 992597 2125415 := bstep (se 1 (by rfl) ⟨1594061, by rfl⟩ : syracuseStep 2125415 = 3188123) B3188123
theorem B2518847 : Blo 992597 2518847 := bstep (se 1 (by rfl) ⟨1889135, by rfl⟩ : syracuseStep 2518847 = 3778271) B3778271
theorem B5042249 : Blo 992597 5042249 := bstep (se 2 (by rfl) ⟨1890843, by rfl⟩ : syracuseStep 5042249 = 3781687) B3781687
theorem B2388295 : Blo 992597 2388295 := bstep (se 1 (by rfl) ⟨1791221, by rfl⟩ : syracuseStep 2388295 = 3582443) B3582443
theorem B8483237 : Blo 992597 8483237 := bstep (se 4 (by rfl) ⟨795303, by rfl⟩ : syracuseStep 8483237 = 1590607) B1590607
theorem B2519495 : Blo 992597 2519495 := bstep (se 1 (by rfl) ⟨1889621, by rfl⟩ : syracuseStep 2519495 = 3779243) B3779243
theorem B77591297 : Blo 992597 77591297 := bstep (se 2 (by rfl) ⟨29096736, by rfl⟩ : syracuseStep 77591297 = 58193473) B58193473
theorem B2520193 : Blo 992597 2520193 := bstep (se 2 (by rfl) ⟨945072, by rfl⟩ : syracuseStep 2520193 = 1890145) B1890145
theorem B2520679 : Blo 992597 2520679 := bstep (se 1 (by rfl) ⟨1890509, by rfl⟩ : syracuseStep 2520679 = 3781019) B3781019
theorem B1275719 : Blo 992597 1275719 := bstep (se 1 (by rfl) ⟨956789, by rfl⟩ : syracuseStep 1275719 = 1913579) B1913579
theorem B2521003 : Blo 992597 2521003 := bstep (se 1 (by rfl) ⟨1890752, by rfl⟩ : syracuseStep 2521003 = 3781505) B3781505
theorem B2521115 : Blo 992597 2521115 := bstep (se 1 (by rfl) ⟨1890836, by rfl⟩ : syracuseStep 2521115 = 3781673) B3781673
theorem B2521307 : Blo 992597 2521307 := bstep (se 1 (by rfl) ⟨1890980, by rfl⟩ : syracuseStep 2521307 = 3781961) B3781961
theorem B24181091 : Blo 992597 24181091 := bstep (se 1 (by rfl) ⟨18135818, by rfl⟩ : syracuseStep 24181091 = 36271637) B36271637
theorem B2128361 : Blo 992597 2128361 := bstep (se 2 (by rfl) ⟨798135, by rfl⟩ : syracuseStep 2128361 = 1596271) B1596271
theorem B5668157 : Blo 992597 5668157 := bstep (se 3 (by rfl) ⟨1062779, by rfl⟩ : syracuseStep 5668157 = 2125559) B2125559
theorem B2522441 : Blo 992597 2522441 := bstep (se 2 (by rfl) ⟨945915, by rfl⟩ : syracuseStep 2522441 = 1891831) B1891831
theorem B10190231 : Blo 992597 10190231 := bstep (se 1 (by rfl) ⟨7642673, by rfl⟩ : syracuseStep 10190231 = 15285347) B15285347
theorem B2522603 : Blo 992597 2522603 := bstep (se 1 (by rfl) ⟨1891952, by rfl⟩ : syracuseStep 2522603 = 3783905) B3783905
theorem B2424503 : Blo 992597 2424503 := bstep (se 1 (by rfl) ⟨1818377, by rfl⟩ : syracuseStep 2424503 = 3636755) B3636755
theorem B32211229 : Blo 992597 32211229 := bstep (se 3 (by rfl) ⟨6039605, by rfl⟩ : syracuseStep 32211229 = 12079211) B12079211
theorem B81658205 : Blo 992597 81658205 := bstep (se 3 (by rfl) ⟨15310913, by rfl⟩ : syracuseStep 81658205 = 30621827) B30621827
theorem B9077833 : Blo 992597 9077833 := bstep (se 2 (by rfl) ⟨3404187, by rfl⟩ : syracuseStep 9077833 = 6808375) B6808375
theorem B10880207 : Blo 992597 10880207 := bstep (se 1 (by rfl) ⟨8160155, by rfl⟩ : syracuseStep 10880207 = 16320311) B16320311
theorem B3769811 : Blo 992597 3769811 := bstep (se 1 (by rfl) ⟨2827358, by rfl⟩ : syracuseStep 3769811 = 5654717) B5654717
theorem B3770023 : Blo 992597 3770023 := bstep (se 1 (by rfl) ⟨2827517, by rfl⟩ : syracuseStep 3770023 = 5655035) B5655035
theorem B8063219 : Blo 992597 8063219 := bstep (se 1 (by rfl) ⟨6047414, by rfl⟩ : syracuseStep 8063219 = 12094829) B12094829
theorem B7670143 : Blo 992597 7670143 := bstep (se 1 (by rfl) ⟨5752607, by rfl⟩ : syracuseStep 7670143 = 11505215) B11505215
theorem B13994441 : Blo 992597 13994441 := bstep (se 2 (by rfl) ⟨5247915, by rfl⟩ : syracuseStep 13994441 = 10495831) B10495831
theorem B1117039 : Blo 992597 1117039 := bstep (se 1 (by rfl) ⟨837779, by rfl⟩ : syracuseStep 1117039 = 1675559) B1675559
theorem B2690671 : Blo 992597 2690671 := bstep (se 1 (by rfl) ⟨2018003, by rfl⟩ : syracuseStep 2690671 = 4036007) B4036007
theorem B3182905 : Blo 992597 3182905 := bstep (se 2 (by rfl) ⟨1193589, by rfl⟩ : syracuseStep 3182905 = 2387179) B2387179
theorem B43618621 : Blo 992597 43618621 := bstep (se 3 (by rfl) ⟨8178491, by rfl⟩ : syracuseStep 43618621 = 16356983) B16356983
theorem B1118911 : Blo 992597 1118911 := bstep (se 1 (by rfl) ⟨839183, by rfl⟩ : syracuseStep 1118911 = 1678367) B1678367
theorem B3183407 : Blo 992597 3183407 := bstep (se 1 (by rfl) ⟨2387555, by rfl⟩ : syracuseStep 3183407 = 4775111) B4775111
theorem B1119199 : Blo 992597 1119199 := bstep (se 1 (by rfl) ⟨839399, by rfl⟩ : syracuseStep 1119199 = 1678799) B1678799
theorem B1676713 : Blo 992597 1676713 := bstep (se 2 (by rfl) ⟨628767, by rfl⟩ : syracuseStep 1676713 = 1257535) B1257535
theorem B3773911 : Blo 992597 3773911 := bstep (se 1 (by rfl) ⟨2830433, by rfl⟩ : syracuseStep 3773911 = 5660867) B5660867
theorem B1676767 : Blo 992597 1676767 := bstep (se 1 (by rfl) ⟨1257575, by rfl⟩ : syracuseStep 1676767 = 2515151) B2515151
theorem B3184393 : Blo 992597 3184393 := bstep (se 2 (by rfl) ⟨1194147, by rfl⟩ : syracuseStep 3184393 = 2388295) B2388295
theorem B21469049 : Blo 992597 21469049 := bstep (se 2 (by rfl) ⟨8050893, by rfl⟩ : syracuseStep 21469049 = 16101787) B16101787
theorem B20453303 : Blo 992597 20453303 := bstep (se 1 (by rfl) ⟨15339977, by rfl⟩ : syracuseStep 20453303 = 30679955) B30679955
theorem B20388341 : Blo 992597 20388341 := bstep (se 5 (by rfl) ⟨955703, by rfl⟩ : syracuseStep 20388341 = 1911407) B1911407
theorem B5675629 : Blo 992597 5675629 := bstep (se 3 (by rfl) ⟨1064180, by rfl⟩ : syracuseStep 5675629 = 2128361) B2128361
theorem B1677935 : Blo 992597 1677935 := bstep (se 1 (by rfl) ⟨1258451, by rfl⟩ : syracuseStep 1677935 = 2516903) B2516903
theorem B2235041 : Blo 992597 2235041 := bstep (se 2 (by rfl) ⟨838140, by rfl⟩ : syracuseStep 2235041 = 1676281) B1676281
theorem B12720959 : Blo 992597 12720959 := bstep (se 1 (by rfl) ⟨9540719, by rfl⟩ : syracuseStep 12720959 = 19081439) B19081439
theorem B2235239 : Blo 992597 2235239 := bstep (se 1 (by rfl) ⟨1676429, by rfl⟩ : syracuseStep 2235239 = 3352859) B3352859
theorem B17439623 : Blo 992597 17439623 := bstep (se 1 (by rfl) ⟨13079717, by rfl⟩ : syracuseStep 17439623 = 26159435) B26159435
theorem B2235401 : Blo 992597 2235401 := bstep (se 2 (by rfl) ⟨838275, by rfl⟩ : syracuseStep 2235401 = 1676551) B1676551
theorem B8625167 : Blo 992597 8625167 := bstep (se 1 (by rfl) ⟨6468875, by rfl⟩ : syracuseStep 8625167 = 12937751) B12937751
theorem B4038083 : Blo 992597 4038083 := bstep (se 1 (by rfl) ⟨3028562, by rfl⟩ : syracuseStep 4038083 = 6057125) B6057125
theorem B11312621 : Blo 992597 11312621 := bstep (se 3 (by rfl) ⟨2121116, by rfl⟩ : syracuseStep 11312621 = 4242233) B4242233
theorem B1416943 : Blo 992597 1416943 := bstep (se 1 (by rfl) ⟨1062707, by rfl⟩ : syracuseStep 1416943 = 2125415) B2125415
theorem B1679231 : Blo 992597 1679231 := bstep (se 1 (by rfl) ⟨1259423, by rfl⟩ : syracuseStep 1679231 = 2518847) B2518847
theorem B1679663 : Blo 992597 1679663 := bstep (se 1 (by rfl) ⟨1259747, by rfl⟩ : syracuseStep 1679663 = 2519495) B2519495
theorem B2236895 : Blo 992597 2236895 := bstep (se 1 (by rfl) ⟨1677671, by rfl⟩ : syracuseStep 2236895 = 3355343) B3355343
theorem B13607669 : Blo 992597 13607669 := bstep (se 5 (by rfl) ⟨637859, by rfl⟩ : syracuseStep 13607669 = 1275719) B1275719
theorem B2237435 : Blo 992597 2237435 := bstep (se 1 (by rfl) ⟨1678076, by rfl⟩ : syracuseStep 2237435 = 3356153) B3356153
theorem B2237543 : Blo 992597 2237543 := bstep (se 1 (by rfl) ⟨1678157, by rfl⟩ : syracuseStep 2237543 = 3356315) B3356315
theorem B2237651 : Blo 992597 2237651 := bstep (se 1 (by rfl) ⟨1678238, by rfl⟩ : syracuseStep 2237651 = 3356477) B3356477
theorem B3351833 : Blo 992597 3351833 := bstep (se 2 (by rfl) ⟨1256937, by rfl⟩ : syracuseStep 3351833 = 2513875) B2513875
theorem B1680743 : Blo 992597 1680743 := bstep (se 1 (by rfl) ⟨1260557, by rfl⟩ : syracuseStep 1680743 = 2521115) B2521115
theorem B992639 : Blo 992597 992639 := bstep (se 1 (by rfl) ⟨744479, by rfl⟩ : syracuseStep 992639 = 1488959) B1488959
theorem B1680871 : Blo 992597 1680871 := bstep (se 1 (by rfl) ⟨1260653, by rfl⟩ : syracuseStep 1680871 = 2521307) B2521307
theorem B992859 : Blo 992597 992859 := bstep (se 1 (by rfl) ⟨744644, by rfl⟩ : syracuseStep 992859 = 1489289) B1489289
theorem B992975 : Blo 992597 992975 := bstep (se 1 (by rfl) ⟨744731, by rfl⟩ : syracuseStep 992975 = 1489463) B1489463
theorem B993191 : Blo 992597 993191 := bstep (se 1 (by rfl) ⟨744893, by rfl⟩ : syracuseStep 993191 = 1489787) B1489787
theorem B3155879 : Blo 992597 3155879 := bstep (se 1 (by rfl) ⟨2366909, by rfl⟩ : syracuseStep 3155879 = 4733819) B4733819
theorem B3352535 : Blo 992597 3352535 := bstep (se 1 (by rfl) ⟨2514401, by rfl⟩ : syracuseStep 3352535 = 5028803) B5028803
theorem B3778771 : Blo 992597 3778771 := bstep (se 1 (by rfl) ⟨2834078, by rfl⟩ : syracuseStep 3778771 = 5668157) B5668157
theorem B1681627 : Blo 992597 1681627 := bstep (se 1 (by rfl) ⟨1261220, by rfl⟩ : syracuseStep 1681627 = 2522441) B2522441
theorem B6793487 : Blo 992597 6793487 := bstep (se 1 (by rfl) ⟨5095115, by rfl⟩ : syracuseStep 6793487 = 10190231) B10190231
theorem B993599 : Blo 992597 993599 := bstep (se 1 (by rfl) ⟨745199, by rfl⟩ : syracuseStep 993599 = 1490399) B1490399
theorem B1681735 : Blo 992597 1681735 := bstep (se 1 (by rfl) ⟨1261301, by rfl⟩ : syracuseStep 1681735 = 2522603) B2522603
theorem B34941307 : Blo 992597 34941307 := bstep (se 1 (by rfl) ⟨26205980, by rfl⟩ : syracuseStep 34941307 = 52411961) B52411961
theorem B1616335 : Blo 992597 1616335 := bstep (se 1 (by rfl) ⟨1212251, by rfl⟩ : syracuseStep 1616335 = 2424503) B2424503
theorem B993767 : Blo 992597 993767 := bstep (se 1 (by rfl) ⟨745325, by rfl⟩ : syracuseStep 993767 = 1490651) B1490651
theorem B27208331 : Blo 992597 27208331 := bstep (se 1 (by rfl) ⟨20406248, by rfl⟩ : syracuseStep 27208331 = 40812497) B40812497
theorem B993947 : Blo 992597 993947 := bstep (se 1 (by rfl) ⟨745460, by rfl⟩ : syracuseStep 993947 = 1490921) B1490921
theorem B994075 : Blo 992597 994075 := bstep (se 1 (by rfl) ⟨745556, by rfl⟩ : syracuseStep 994075 = 1491113) B1491113
theorem B2829113 : Blo 992597 2829113 := bstep (se 2 (by rfl) ⟨1060917, by rfl⟩ : syracuseStep 2829113 = 2121835) B2121835
theorem B994287 : Blo 992597 994287 := bstep (se 1 (by rfl) ⟨745715, by rfl⟩ : syracuseStep 994287 = 1491431) B1491431
theorem B994471 : Blo 992597 994471 := bstep (se 1 (by rfl) ⟨745853, by rfl⟩ : syracuseStep 994471 = 1491707) B1491707
theorem B3353939 : Blo 992597 3353939 := bstep (se 1 (by rfl) ⟨2515454, by rfl⟩ : syracuseStep 3353939 = 5030909) B5030909
theorem B994767 : Blo 992597 994767 := bstep (se 1 (by rfl) ⟨746075, by rfl⟩ : syracuseStep 994767 = 1492151) B1492151
theorem B994863 : Blo 992597 994863 := bstep (se 1 (by rfl) ⟨746147, by rfl⟩ : syracuseStep 994863 = 1492295) B1492295
theorem B994927 : Blo 992597 994927 := bstep (se 1 (by rfl) ⟨746195, by rfl⟩ : syracuseStep 994927 = 1492391) B1492391
theorem B995047 : Blo 992597 995047 := bstep (se 1 (by rfl) ⟨746285, by rfl⟩ : syracuseStep 995047 = 1492571) B1492571
theorem B4534139 : Blo 992597 4534139 := bstep (se 1 (by rfl) ⟨3400604, by rfl⟩ : syracuseStep 4534139 = 6801209) B6801209
theorem B5025725 : Blo 992597 5025725 := bstep (se 3 (by rfl) ⟨942323, by rfl⟩ : syracuseStep 5025725 = 1884647) B1884647
theorem B8073209 : Blo 992597 8073209 := bstep (se 2 (by rfl) ⟨3027453, by rfl⟩ : syracuseStep 8073209 = 6054907) B6054907
theorem B995359 : Blo 992597 995359 := bstep (se 1 (by rfl) ⟨746519, by rfl⟩ : syracuseStep 995359 = 1493039) B1493039
theorem B5025887 : Blo 992597 5025887 := bstep (se 1 (by rfl) ⟨3769415, by rfl⟩ : syracuseStep 5025887 = 7538831) B7538831
theorem B2240711 : Blo 992597 2240711 := bstep (se 1 (by rfl) ⟨1680533, by rfl⟩ : syracuseStep 2240711 = 3361067) B3361067
theorem B995535 : Blo 992597 995535 := bstep (se 1 (by rfl) ⟨746651, by rfl⟩ : syracuseStep 995535 = 1493303) B1493303
theorem B3354857 : Blo 992597 3354857 := bstep (se 2 (by rfl) ⟨1258071, by rfl⟩ : syracuseStep 3354857 = 2516143) B2516143
theorem B3354911 : Blo 992597 3354911 := bstep (se 1 (by rfl) ⟨2516183, by rfl⟩ : syracuseStep 3354911 = 5032367) B5032367
theorem B1061191 : Blo 992597 1061191 := bstep (se 1 (by rfl) ⟨795893, by rfl⟩ : syracuseStep 1061191 = 1591787) B1591787
theorem B995655 : Blo 992597 995655 := bstep (se 1 (by rfl) ⟨746741, by rfl⟩ : syracuseStep 995655 = 1493483) B1493483
theorem B995815 : Blo 992597 995815 := bstep (se 1 (by rfl) ⟨746861, by rfl⟩ : syracuseStep 995815 = 1493723) B1493723
theorem B995839 : Blo 992597 995839 := bstep (se 1 (by rfl) ⟨746879, by rfl⟩ : syracuseStep 995839 = 1493759) B1493759
theorem B8499775 : Blo 992597 8499775 := bstep (se 1 (by rfl) ⟨6374831, by rfl⟩ : syracuseStep 8499775 = 12749663) B12749663
theorem B4305503 : Blo 992597 4305503 := bstep (se 1 (by rfl) ⟨3229127, by rfl⟩ : syracuseStep 4305503 = 6458255) B6458255
theorem B206910125 : Blo 992597 206910125 := bstep (se 3 (by rfl) ⟨38795648, by rfl⟩ : syracuseStep 206910125 = 77591297) B77591297
theorem B2241377 : Blo 992597 2241377 := bstep (se 2 (by rfl) ⟨840516, by rfl⟩ : syracuseStep 2241377 = 1681033) B1681033
theorem B2241449 : Blo 992597 2241449 := bstep (se 2 (by rfl) ⟨840543, by rfl⟩ : syracuseStep 2241449 = 1681087) B1681087
theorem B2241503 : Blo 992597 2241503 := bstep (se 1 (by rfl) ⟨1681127, by rfl⟩ : syracuseStep 2241503 = 3362255) B3362255
theorem B996319 : Blo 992597 996319 := bstep (se 1 (by rfl) ⟨747239, by rfl⟩ : syracuseStep 996319 = 1494479) B1494479
theorem B996379 : Blo 992597 996379 := bstep (se 1 (by rfl) ⟨747284, by rfl⟩ : syracuseStep 996379 = 1494569) B1494569
theorem B996575 : Blo 992597 996575 := bstep (se 1 (by rfl) ⟨747431, by rfl⟩ : syracuseStep 996575 = 1494863) B1494863
theorem B5027183 : Blo 992597 5027183 := bstep (se 1 (by rfl) ⟨3770387, by rfl⟩ : syracuseStep 5027183 = 7540775) B7540775
theorem B8500733 : Blo 992597 8500733 := bstep (se 3 (by rfl) ⟨1593887, by rfl⟩ : syracuseStep 8500733 = 3187775) B3187775
theorem B7550495 : Blo 992597 7550495 := bstep (se 1 (by rfl) ⟨5662871, by rfl⟩ : syracuseStep 7550495 = 11325743) B11325743
theorem B2242151 : Blo 992597 2242151 := bstep (se 1 (by rfl) ⟨1681613, by rfl⟩ : syracuseStep 2242151 = 3363227) B3363227
theorem B6469289 : Blo 992597 6469289 := bstep (se 2 (by rfl) ⟨2425983, by rfl⟩ : syracuseStep 6469289 = 4851967) B4851967
theorem B3356423 : Blo 992597 3356423 := bstep (se 1 (by rfl) ⟨2517317, by rfl⟩ : syracuseStep 3356423 = 5034635) B5034635
theorem B3356639 : Blo 992597 3356639 := bstep (se 1 (by rfl) ⟨2517479, by rfl⟩ : syracuseStep 3356639 = 5034959) B5034959
theorem B3356855 : Blo 992597 3356855 := bstep (se 1 (by rfl) ⟨2517641, by rfl⟩ : syracuseStep 3356855 = 5035283) B5035283
theorem B3357449 : Blo 992597 3357449 := bstep (se 2 (by rfl) ⟨1259043, by rfl⟩ : syracuseStep 3357449 = 2518087) B2518087
theorem B10205995 : Blo 992597 10205995 := bstep (se 1 (by rfl) ⟨7654496, by rfl⟩ : syracuseStep 10205995 = 15308993) B15308993
theorem B17251163 : Blo 992597 17251163 := bstep (se 1 (by rfl) ⟨12938372, by rfl⟩ : syracuseStep 17251163 = 25876745) B25876745
theorem B1490087 : Blo 992597 1490087 := bstep (se 1 (by rfl) ⟨1117565, by rfl⟩ : syracuseStep 1490087 = 2235131) B2235131
theorem B1490171 : Blo 992597 1490171 := bstep (se 1 (by rfl) ⟨1117628, by rfl⟩ : syracuseStep 1490171 = 2235257) B2235257
theorem B1490297 : Blo 992597 1490297 := bstep (se 2 (by rfl) ⟨558861, by rfl⟩ : syracuseStep 1490297 = 1117723) B1117723
theorem B12762785 : Blo 992597 12762785 := bstep (se 2 (by rfl) ⟨4786044, by rfl⟩ : syracuseStep 12762785 = 9572089) B9572089
theorem B4243175 : Blo 992597 4243175 := bstep (se 1 (by rfl) ⟨3182381, by rfl⟩ : syracuseStep 4243175 = 6364763) B6364763
theorem B1490825 : Blo 992597 1490825 := bstep (se 2 (by rfl) ⟨559059, by rfl⟩ : syracuseStep 1490825 = 1118119) B1118119
theorem B1491065 : Blo 992597 1491065 := bstep (se 2 (by rfl) ⟨559149, by rfl⟩ : syracuseStep 1491065 = 1118299) B1118299
theorem B1491359 : Blo 992597 1491359 := bstep (se 1 (by rfl) ⟨1118519, by rfl⟩ : syracuseStep 1491359 = 2237039) B2237039
theorem B1491689 : Blo 992597 1491689 := bstep (se 2 (by rfl) ⟨559383, by rfl⟩ : syracuseStep 1491689 = 1118767) B1118767
theorem B5653577 : Blo 992597 5653577 := bstep (se 2 (by rfl) ⟨2120091, by rfl⟩ : syracuseStep 5653577 = 4240183) B4240183
theorem B1885673 : Blo 992597 1885673 := bstep (se 2 (by rfl) ⟨707127, by rfl⟩ : syracuseStep 1885673 = 1414255) B1414255
theorem B1492457 : Blo 992597 1492457 := bstep (se 2 (by rfl) ⟨559671, by rfl⟩ : syracuseStep 1492457 = 1119343) B1119343
theorem B3360257 : Blo 992597 3360257 := bstep (se 2 (by rfl) ⟨1260096, by rfl⟩ : syracuseStep 3360257 = 2520193) B2520193
theorem B1492535 : Blo 992597 1492535 := bstep (se 1 (by rfl) ⟨1119401, by rfl⟩ : syracuseStep 1492535 = 2238803) B2238803
theorem B5031719 : Blo 992597 5031719 := bstep (se 1 (by rfl) ⟨3773789, by rfl⟩ : syracuseStep 5031719 = 7547579) B7547579
theorem B25806721 : Blo 992597 25806721 := bstep (se 2 (by rfl) ⟨9677520, by rfl⟩ : syracuseStep 25806721 = 19355041) B19355041
theorem B1492895 : Blo 992597 1492895 := bstep (se 1 (by rfl) ⟨1119671, by rfl⟩ : syracuseStep 1492895 = 2239343) B2239343
theorem B1493063 : Blo 992597 1493063 := bstep (se 1 (by rfl) ⟨1119797, by rfl⟩ : syracuseStep 1493063 = 2239595) B2239595
theorem B3360905 : Blo 992597 3360905 := bstep (se 2 (by rfl) ⟨1260339, by rfl⟩ : syracuseStep 3360905 = 2520679) B2520679
theorem B1493243 : Blo 992597 1493243 := bstep (se 1 (by rfl) ⟨1119932, by rfl⟩ : syracuseStep 1493243 = 2239865) B2239865
theorem B3361337 : Blo 992597 3361337 := bstep (se 2 (by rfl) ⟨1260501, by rfl⟩ : syracuseStep 3361337 = 2521003) B2521003
theorem B1493663 : Blo 992597 1493663 := bstep (se 1 (by rfl) ⟨1120247, by rfl⟩ : syracuseStep 1493663 = 2240495) B2240495
theorem B3361499 : Blo 992597 3361499 := bstep (se 1 (by rfl) ⟨2521124, by rfl⟩ : syracuseStep 3361499 = 5042249) B5042249
theorem B5655491 : Blo 992597 5655491 := bstep (se 1 (by rfl) ⟨4241618, by rfl⟩ : syracuseStep 5655491 = 8483237) B8483237
theorem B1887457 : Blo 992597 1887457 := bstep (se 2 (by rfl) ⟨707796, by rfl⟩ : syracuseStep 1887457 = 1415593) B1415593
theorem B1494527 : Blo 992597 1494527 := bstep (se 1 (by rfl) ⟨1120895, by rfl⟩ : syracuseStep 1494527 = 2241791) B2241791
theorem B5656493 : Blo 992597 5656493 := bstep (se 3 (by rfl) ⟨1060592, by rfl⟩ : syracuseStep 5656493 = 2121185) B2121185
theorem B1888247 : Blo 992597 1888247 := bstep (se 1 (by rfl) ⟨1416185, by rfl⟩ : syracuseStep 1888247 = 2832371) B2832371
theorem B74731841 : Blo 992597 74731841 := bstep (se 2 (by rfl) ⟨28024440, by rfl⟩ : syracuseStep 74731841 = 56048881) B56048881
theorem B17224559 : Blo 992597 17224559 := bstep (se 1 (by rfl) ⟨12918419, by rfl⟩ : syracuseStep 17224559 = 25836839) B25836839
theorem B42980291 : Blo 992597 42980291 := bstep (se 1 (by rfl) ⟨32235218, by rfl⟩ : syracuseStep 42980291 = 64470437) B64470437
theorem B3233191 : Blo 992597 3233191 := bstep (se 1 (by rfl) ⟨2424893, by rfl⟩ : syracuseStep 3233191 = 4849787) B4849787
theorem B12113711 : Blo 992597 12113711 := bstep (se 1 (by rfl) ⟨9085283, by rfl⟩ : syracuseStep 12113711 = 18170567) B18170567
theorem B4839421 : Blo 992597 4839421 := bstep (se 3 (by rfl) ⟨907391, by rfl⟩ : syracuseStep 4839421 = 1814783) B1814783
theorem B1890479 : Blo 992597 1890479 := bstep (se 1 (by rfl) ⟨1417859, by rfl⟩ : syracuseStep 1890479 = 2835719) B2835719
theorem B16997363 : Blo 992597 16997363 := bstep (se 1 (by rfl) ⟨12748022, by rfl⟩ : syracuseStep 16997363 = 25496045) B25496045
theorem B1891603 : Blo 992597 1891603 := bstep (se 1 (by rfl) ⟨1418702, by rfl⟩ : syracuseStep 1891603 = 2837405) B2837405
theorem B8511257 : Blo 992597 8511257 := bstep (se 2 (by rfl) ⟨3191721, by rfl⟩ : syracuseStep 8511257 = 6383443) B6383443
theorem B3235895 : Blo 992597 3235895 := bstep (se 1 (by rfl) ⟨2426921, by rfl⟩ : syracuseStep 3235895 = 4853843) B4853843
theorem B3825899 : Blo 992597 3825899 := bstep (se 1 (by rfl) ⟨2869424, by rfl⟩ : syracuseStep 3825899 = 5738849) B5738849
theorem B1795049 : Blo 992597 1795049 := bstep (se 2 (by rfl) ⟨673143, by rfl⟩ : syracuseStep 1795049 = 1346287) B1346287
theorem B2122843 : Blo 992597 2122843 := bstep (se 1 (by rfl) ⟨1592132, by rfl⟩ : syracuseStep 2122843 = 3184265) B3184265
theorem B8479889 : Blo 992597 8479889 := bstep (se 2 (by rfl) ⟨3179958, by rfl⟩ : syracuseStep 8479889 = 6359917) B6359917
theorem B4777127 : Blo 992597 4777127 := bstep (se 1 (by rfl) ⟨3582845, by rfl⟩ : syracuseStep 4777127 = 7165691) B7165691
theorem B69887225 : Blo 992597 69887225 := bstep (se 2 (by rfl) ⟨26207709, by rfl⟩ : syracuseStep 69887225 = 52415419) B52415419
theorem B1009103 : Blo 992597 1009103 := bstep (se 1 (by rfl) ⟨756827, by rfl⟩ : syracuseStep 1009103 = 1513655) B1513655
theorem B6384059 : Blo 992597 6384059 := bstep (se 1 (by rfl) ⟨4788044, by rfl⟩ : syracuseStep 6384059 = 9576089) B9576089
theorem B27224747 : Blo 992597 27224747 := bstep (se 1 (by rfl) ⟨20418560, by rfl⟩ : syracuseStep 27224747 = 40837121) B40837121
theorem B5040953 : Blo 992597 5040953 := bstep (se 2 (by rfl) ⟨1890357, by rfl⟩ : syracuseStep 5040953 = 3780715) B3780715
theorem B8613323 : Blo 992597 8613323 := bstep (se 1 (by rfl) ⟨6459992, by rfl⟩ : syracuseStep 8613323 = 12919985) B12919985
theorem B2125919 : Blo 992597 2125919 := bstep (se 1 (by rfl) ⟨1594439, by rfl⟩ : syracuseStep 2125919 = 3188879) B3188879
theorem B12087431 : Blo 992597 12087431 := bstep (se 1 (by rfl) ⟨9065573, by rfl⟩ : syracuseStep 12087431 = 18131147) B18131147
theorem B8484263 : Blo 992597 8484263 := bstep (se 1 (by rfl) ⟨6363197, by rfl⟩ : syracuseStep 8484263 = 12726395) B12726395
theorem B2389583 : Blo 992597 2389583 := bstep (se 1 (by rfl) ⟨1792187, by rfl⟩ : syracuseStep 2389583 = 3584375) B3584375
theorem B16120727 : Blo 992597 16120727 := bstep (se 1 (by rfl) ⟨12090545, by rfl⟩ : syracuseStep 16120727 = 24181091) B24181091
theorem B7175263 : Blo 992597 7175263 := bstep (se 1 (by rfl) ⟨5381447, by rfl⟩ : syracuseStep 7175263 = 10762895) B10762895
theorem B3769051 : Blo 992597 3769051 := bstep (se 1 (by rfl) ⟨2826788, by rfl⟩ : syracuseStep 3769051 = 5653577) B5653577
theorem B5375479 : Blo 992597 5375479 := bstep (se 1 (by rfl) ⟨4031609, by rfl⟩ : syracuseStep 5375479 = 8063219) B8063219
theorem B16975493 : Blo 992597 16975493 := bstep (se 4 (by rfl) ⟨1591452, by rfl⟩ : syracuseStep 16975493 = 3182905) B3182905
theorem B3770327 : Blo 992597 3770327 := bstep (se 1 (by rfl) ⟨2827745, by rfl⟩ : syracuseStep 3770327 = 5655491) B5655491
theorem B8620453 : Blo 992597 8620453 := bstep (se 4 (by rfl) ⟨808167, by rfl⟩ : syracuseStep 8620453 = 1616335) B1616335
theorem B34408961 : Blo 992597 34408961 := bstep (se 2 (by rfl) ⟨12903360, by rfl⟩ : syracuseStep 34408961 = 25806721) B25806721
theorem B3770995 : Blo 992597 3770995 := bstep (se 1 (by rfl) ⟨2828246, by rfl⟩ : syracuseStep 3770995 = 5656493) B5656493
theorem B10226857 : Blo 992597 10226857 := bstep (se 2 (by rfl) ⟨3835071, by rfl⟩ : syracuseStep 10226857 = 7670143) B7670143
theorem B2690941 : Blo 992597 2690941 := bstep (se 3 (by rfl) ⟨504551, by rfl⟩ : syracuseStep 2690941 = 1009103) B1009103
theorem B13635535 : Blo 992597 13635535 := bstep (se 1 (by rfl) ⟨10226651, by rfl⟩ : syracuseStep 13635535 = 20453303) B20453303
theorem B1118623 : Blo 992597 1118623 := bstep (se 1 (by rfl) ⟨838967, by rfl⟩ : syracuseStep 1118623 = 1677935) B1677935
theorem B2692055 : Blo 992597 2692055 := bstep (se 1 (by rfl) ⟨2019041, by rfl⟩ : syracuseStep 2692055 = 4038083) B4038083
theorem B7541747 : Blo 992597 7541747 := bstep (se 1 (by rfl) ⟨5656310, by rfl⟩ : syracuseStep 7541747 = 11312621) B11312621
theorem B5674171 : Blo 992597 5674171 := bstep (se 1 (by rfl) ⟨4255628, by rfl⟩ : syracuseStep 5674171 = 8511257) B8511257
theorem B1119487 : Blo 992597 1119487 := bstep (se 1 (by rfl) ⟨839615, by rfl⟩ : syracuseStep 1119487 = 1679231) B1679231
theorem B1119775 : Blo 992597 1119775 := bstep (se 1 (by rfl) ⟨839831, by rfl⟩ : syracuseStep 1119775 = 1679663) B1679663
theorem B1414921 : Blo 992597 1414921 := bstep (se 2 (by rfl) ⟨530595, by rfl⟩ : syracuseStep 1414921 = 1061191) B1061191
theorem B3184751 : Blo 992597 3184751 := bstep (se 1 (by rfl) ⟨2388563, by rfl⟩ : syracuseStep 3184751 = 4777127) B4777127
theorem B2234555 : Blo 992597 2234555 := bstep (se 1 (by rfl) ⟨1675916, by rfl⟩ : syracuseStep 2234555 = 3351833) B3351833
theorem B1120495 : Blo 992597 1120495 := bstep (se 1 (by rfl) ⟨840371, by rfl⟩ : syracuseStep 1120495 = 1680743) B1680743
theorem B2235023 : Blo 992597 2235023 := bstep (se 1 (by rfl) ⟨1676267, by rfl⟩ : syracuseStep 2235023 = 3352535) B3352535
theorem B4528991 : Blo 992597 4528991 := bstep (se 1 (by rfl) ⟨3396743, by rfl⟩ : syracuseStep 4528991 = 6793487) B6793487
theorem B2235617 : Blo 992597 2235617 := bstep (se 2 (by rfl) ⟨838356, by rfl⟩ : syracuseStep 2235617 = 1676713) B1676713
theorem B2235689 : Blo 992597 2235689 := bstep (se 2 (by rfl) ⟨838383, by rfl⟩ : syracuseStep 2235689 = 1676767) B1676767
theorem B2235959 : Blo 992597 2235959 := bstep (se 1 (by rfl) ⟨1676969, by rfl⟩ : syracuseStep 2235959 = 3353939) B3353939
theorem B5742215 : Blo 992597 5742215 := bstep (se 1 (by rfl) ⟨4306661, by rfl⟩ : syracuseStep 5742215 = 8613323) B8613323
theorem B3022759 : Blo 992597 3022759 := bstep (se 1 (by rfl) ⟨2267069, by rfl⟩ : syracuseStep 3022759 = 4534139) B4534139
theorem B3350483 : Blo 992597 3350483 := bstep (se 1 (by rfl) ⟨2512862, by rfl⟩ : syracuseStep 3350483 = 5025725) B5025725
theorem B5382139 : Blo 992597 5382139 := bstep (se 1 (by rfl) ⟨4036604, by rfl⟩ : syracuseStep 5382139 = 8073209) B8073209
theorem B3350591 : Blo 992597 3350591 := bstep (se 1 (by rfl) ⟨2512943, by rfl⟩ : syracuseStep 3350591 = 5025887) B5025887
theorem B1417279 : Blo 992597 1417279 := bstep (se 1 (by rfl) ⟨1062959, by rfl⟩ : syracuseStep 1417279 = 2125919) B2125919
theorem B2236571 : Blo 992597 2236571 := bstep (se 1 (by rfl) ⟨1677428, by rfl⟩ : syracuseStep 2236571 = 3354857) B3354857
theorem B2236607 : Blo 992597 2236607 := bstep (se 1 (by rfl) ⟨1677455, by rfl⟩ : syracuseStep 2236607 = 3354911) B3354911
theorem B3351455 : Blo 992597 3351455 := bstep (se 1 (by rfl) ⟨2513591, by rfl⟩ : syracuseStep 3351455 = 5027183) B5027183
theorem B13607993 : Blo 992597 13607993 := bstep (se 2 (by rfl) ⟨5102997, by rfl⟩ : syracuseStep 13607993 = 10205995) B10205995
theorem B2237615 : Blo 992597 2237615 := bstep (se 1 (by rfl) ⟨1678211, by rfl⟩ : syracuseStep 2237615 = 3356423) B3356423
theorem B2237759 : Blo 992597 2237759 := bstep (se 1 (by rfl) ⟨1678319, by rfl⟩ : syracuseStep 2237759 = 3356639) B3356639
theorem B2237903 : Blo 992597 2237903 := bstep (se 1 (by rfl) ⟨1678427, by rfl⟩ : syracuseStep 2237903 = 3356855) B3356855
theorem B2238299 : Blo 992597 2238299 := bstep (se 1 (by rfl) ⟨1678724, by rfl⟩ : syracuseStep 2238299 = 3357449) B3357449
theorem B993391 : Blo 992597 993391 := bstep (se 1 (by rfl) ⟨745043, by rfl⟩ : syracuseStep 993391 = 1490087) B1490087
theorem B993447 : Blo 992597 993447 := bstep (se 1 (by rfl) ⟨745085, by rfl⟩ : syracuseStep 993447 = 1490171) B1490171
theorem B993531 : Blo 992597 993531 := bstep (se 1 (by rfl) ⟨745148, by rfl⟩ : syracuseStep 993531 = 1490297) B1490297
theorem B2828783 : Blo 992597 2828783 := bstep (se 1 (by rfl) ⟨2121587, by rfl⟩ : syracuseStep 2828783 = 4243175) B4243175
theorem B993883 : Blo 992597 993883 := bstep (se 1 (by rfl) ⟨745412, by rfl⟩ : syracuseStep 993883 = 1490825) B1490825
theorem B994043 : Blo 992597 994043 := bstep (se 1 (by rfl) ⟨745532, by rfl⟩ : syracuseStep 994043 = 1491065) B1491065
theorem B54438803 : Blo 992597 54438803 := bstep (se 1 (by rfl) ⟨40829102, by rfl⟩ : syracuseStep 54438803 = 81658205) B81658205
theorem B994239 : Blo 992597 994239 := bstep (se 1 (by rfl) ⟨745679, by rfl⟩ : syracuseStep 994239 = 1491359) B1491359
theorem B994459 : Blo 992597 994459 := bstep (se 1 (by rfl) ⟨745844, by rfl⟩ : syracuseStep 994459 = 1491689) B1491689
theorem B7253471 : Blo 992597 7253471 := bstep (se 1 (by rfl) ⟨5440103, by rfl⟩ : syracuseStep 7253471 = 10880207) B10880207
theorem B1257115 : Blo 992597 1257115 := bstep (se 1 (by rfl) ⟨942836, by rfl⟩ : syracuseStep 1257115 = 1885673) B1885673
theorem B994971 : Blo 992597 994971 := bstep (se 1 (by rfl) ⟨746228, by rfl⟩ : syracuseStep 994971 = 1492457) B1492457
theorem B2240171 : Blo 992597 2240171 := bstep (se 1 (by rfl) ⟨1680128, by rfl⟩ : syracuseStep 2240171 = 3360257) B3360257
theorem B995023 : Blo 992597 995023 := bstep (se 1 (by rfl) ⟨746267, by rfl⟩ : syracuseStep 995023 = 1492535) B1492535
theorem B3354479 : Blo 992597 3354479 := bstep (se 1 (by rfl) ⟨2515859, by rfl⟩ : syracuseStep 3354479 = 5031719) B5031719
theorem B995263 : Blo 992597 995263 := bstep (se 1 (by rfl) ⟨746447, by rfl⟩ : syracuseStep 995263 = 1492895) B1492895
theorem B995375 : Blo 992597 995375 := bstep (se 1 (by rfl) ⟨746531, by rfl⟩ : syracuseStep 995375 = 1493063) B1493063
theorem B2240603 : Blo 992597 2240603 := bstep (se 1 (by rfl) ⟨1680452, by rfl⟩ : syracuseStep 2240603 = 3360905) B3360905
theorem B12103777 : Blo 992597 12103777 := bstep (se 2 (by rfl) ⟨4538916, by rfl⟩ : syracuseStep 12103777 = 9077833) B9077833
theorem B2830457 : Blo 992597 2830457 := bstep (se 2 (by rfl) ⟨1061421, by rfl⟩ : syracuseStep 2830457 = 2122843) B2122843
theorem B995495 : Blo 992597 995495 := bstep (se 1 (by rfl) ⟨746621, by rfl⟩ : syracuseStep 995495 = 1493243) B1493243
theorem B2240891 : Blo 992597 2240891 := bstep (se 1 (by rfl) ⟨1680668, by rfl⟩ : syracuseStep 2240891 = 3361337) B3361337
theorem B995775 : Blo 992597 995775 := bstep (se 1 (by rfl) ⟨746831, by rfl⟩ : syracuseStep 995775 = 1493663) B1493663
theorem B2240999 : Blo 992597 2240999 := bstep (se 1 (by rfl) ⟨1680749, by rfl⟩ : syracuseStep 2240999 = 3361499) B3361499
theorem B2241161 : Blo 992597 2241161 := bstep (se 2 (by rfl) ⟨840435, by rfl⟩ : syracuseStep 2241161 = 1680871) B1680871
theorem B5026697 : Blo 992597 5026697 := bstep (se 2 (by rfl) ⟨1885011, by rfl⟩ : syracuseStep 5026697 = 3770023) B3770023
theorem B996351 : Blo 992597 996351 := bstep (se 1 (by rfl) ⟨747263, by rfl⟩ : syracuseStep 996351 = 1494527) B1494527
theorem B1258831 : Blo 992597 1258831 := bstep (se 1 (by rfl) ⟨944123, by rfl⟩ : syracuseStep 1258831 = 1888247) B1888247
theorem B49821227 : Blo 992597 49821227 := bstep (se 1 (by rfl) ⟨37365920, by rfl⟩ : syracuseStep 49821227 = 74731841) B74731841
theorem B2242169 : Blo 992597 2242169 := bstep (se 2 (by rfl) ⟨840813, by rfl⟩ : syracuseStep 2242169 = 1681627) B1681627
theorem B2242313 : Blo 992597 2242313 := bstep (se 2 (by rfl) ⟨840867, by rfl⟩ : syracuseStep 2242313 = 1681735) B1681735
theorem B11483039 : Blo 992597 11483039 := bstep (se 1 (by rfl) ⟨8612279, by rfl⟩ : syracuseStep 11483039 = 17224559) B17224559
theorem B28653527 : Blo 992597 28653527 := bstep (se 1 (by rfl) ⟨21490145, by rfl⟩ : syracuseStep 28653527 = 42980291) B42980291
theorem B1489385 : Blo 992597 1489385 := bstep (se 2 (by rfl) ⟨558519, by rfl⟩ : syracuseStep 1489385 = 1117039) B1117039
theorem B8075807 : Blo 992597 8075807 := bstep (se 1 (by rfl) ⟨6056855, by rfl⟩ : syracuseStep 8075807 = 12113711) B12113711
theorem B1490027 : Blo 992597 1490027 := bstep (se 1 (by rfl) ⟨1117520, by rfl⟩ : syracuseStep 1490027 = 2235041) B2235041
theorem B1490159 : Blo 992597 1490159 := bstep (se 1 (by rfl) ⟨1117619, by rfl⟩ : syracuseStep 1490159 = 2235239) B2235239
theorem B1490267 : Blo 992597 1490267 := bstep (se 1 (by rfl) ⟨1117700, by rfl⟩ : syracuseStep 1490267 = 2235401) B2235401
theorem B5750111 : Blo 992597 5750111 := bstep (se 1 (by rfl) ⟨4312583, by rfl⟩ : syracuseStep 5750111 = 8625167) B8625167
theorem B3587561 : Blo 992597 3587561 := bstep (se 2 (by rfl) ⟨1345335, by rfl⟩ : syracuseStep 3587561 = 2690671) B2690671
theorem B1491263 : Blo 992597 1491263 := bstep (se 1 (by rfl) ⟨1118447, by rfl⟩ : syracuseStep 1491263 = 2236895) B2236895
theorem B1196699 : Blo 992597 1196699 := bstep (se 1 (by rfl) ⟨897524, by rfl⟩ : syracuseStep 1196699 = 1795049) B1795049
theorem B1491623 : Blo 992597 1491623 := bstep (se 1 (by rfl) ⟨1118717, by rfl⟩ : syracuseStep 1491623 = 2237435) B2237435
theorem B1491695 : Blo 992597 1491695 := bstep (se 1 (by rfl) ⟨1118771, by rfl⟩ : syracuseStep 1491695 = 2237543) B2237543
theorem B5653259 : Blo 992597 5653259 := bstep (se 1 (by rfl) ⟨4239944, by rfl⟩ : syracuseStep 5653259 = 8479889) B8479889
theorem B1491767 : Blo 992597 1491767 := bstep (se 1 (by rfl) ⟨1118825, by rfl⟩ : syracuseStep 1491767 = 2237651) B2237651
theorem B1491881 : Blo 992597 1491881 := bstep (se 2 (by rfl) ⟨559455, by rfl⟩ : syracuseStep 1491881 = 1118911) B1118911
theorem B1492265 : Blo 992597 1492265 := bstep (se 2 (by rfl) ⟨559599, by rfl⟩ : syracuseStep 1492265 = 1119199) B1119199
theorem B18138887 : Blo 992597 18138887 := bstep (se 1 (by rfl) ⟨13604165, by rfl⟩ : syracuseStep 18138887 = 27208331) B27208331
theorem B1886075 : Blo 992597 1886075 := bstep (se 1 (by rfl) ⟨1414556, by rfl⟩ : syracuseStep 1886075 = 2829113) B2829113
theorem B3360635 : Blo 992597 3360635 := bstep (se 1 (by rfl) ⟨2520476, by rfl⟩ : syracuseStep 3360635 = 5040953) B5040953
theorem B4310921 : Blo 992597 4310921 := bstep (se 2 (by rfl) ⟨1616595, by rfl⟩ : syracuseStep 4310921 = 3233191) B3233191
theorem B5031881 : Blo 992597 5031881 := bstep (se 2 (by rfl) ⟨1886955, by rfl⟩ : syracuseStep 5031881 = 3773911) B3773911
theorem B4245857 : Blo 992597 4245857 := bstep (se 2 (by rfl) ⟨1592196, by rfl⟩ : syracuseStep 4245857 = 3184393) B3184393
theorem B1493807 : Blo 992597 1493807 := bstep (se 1 (by rfl) ⟨1120355, by rfl⟩ : syracuseStep 1493807 = 2240711) B2240711
theorem B2870335 : Blo 992597 2870335 := bstep (se 1 (by rfl) ⟨2152751, by rfl⟩ : syracuseStep 2870335 = 4305503) B4305503
theorem B137940083 : Blo 992597 137940083 := bstep (se 1 (by rfl) ⟨103455062, by rfl⟩ : syracuseStep 137940083 = 206910125) B206910125
theorem B1494251 : Blo 992597 1494251 := bstep (se 1 (by rfl) ⟨1120688, by rfl⟩ : syracuseStep 1494251 = 2241377) B2241377
theorem B1494299 : Blo 992597 1494299 := bstep (se 1 (by rfl) ⟨1120724, by rfl⟩ : syracuseStep 1494299 = 2241449) B2241449
theorem B1494335 : Blo 992597 1494335 := bstep (se 1 (by rfl) ⟨1120751, by rfl⟩ : syracuseStep 1494335 = 2241503) B2241503
theorem B5656175 : Blo 992597 5656175 := bstep (se 1 (by rfl) ⟨4242131, by rfl⟩ : syracuseStep 5656175 = 8484263) B8484263
theorem B5033663 : Blo 992597 5033663 := bstep (se 1 (by rfl) ⟨3775247, by rfl⟩ : syracuseStep 5033663 = 7550495) B7550495
theorem B1593055 : Blo 992597 1593055 := bstep (se 1 (by rfl) ⟨1194791, by rfl⟩ : syracuseStep 1593055 = 2389583) B2389583
theorem B1494767 : Blo 992597 1494767 := bstep (se 1 (by rfl) ⟨1121075, by rfl⟩ : syracuseStep 1494767 = 2242151) B2242151
theorem B4312859 : Blo 992597 4312859 := bstep (se 1 (by rfl) ⟨3234644, by rfl⟩ : syracuseStep 4312859 = 6469289) B6469289
theorem B1889257 : Blo 992597 1889257 := bstep (se 2 (by rfl) ⟨708471, by rfl⟩ : syracuseStep 1889257 = 1416943) B1416943
theorem B8508523 : Blo 992597 8508523 := bstep (se 1 (by rfl) ⟨6381392, by rfl⟩ : syracuseStep 8508523 = 12762785) B12762785
theorem B42948305 : Blo 992597 42948305 := bstep (se 2 (by rfl) ⟨16105614, by rfl⟩ : syracuseStep 42948305 = 32211229) B32211229
theorem B2513207 : Blo 992597 2513207 := bstep (se 1 (by rfl) ⟨1884905, by rfl⟩ : syracuseStep 2513207 = 3769811) B3769811
theorem B9329627 : Blo 992597 9329627 := bstep (se 1 (by rfl) ⟨6997220, by rfl⟩ : syracuseStep 9329627 = 13994441) B13994441
theorem B5038361 : Blo 992597 5038361 := bstep (se 2 (by rfl) ⟨1889385, by rfl⟩ : syracuseStep 5038361 = 3778771) B3778771
theorem B46588409 : Blo 992597 46588409 := bstep (se 2 (by rfl) ⟨17470653, by rfl⟩ : syracuseStep 46588409 = 34941307) B34941307
theorem B2122271 : Blo 992597 2122271 := bstep (se 1 (by rfl) ⟨1591703, by rfl⟩ : syracuseStep 2122271 = 3183407) B3183407
theorem B14312699 : Blo 992597 14312699 := bstep (se 1 (by rfl) ⟨10734524, by rfl⟩ : syracuseStep 14312699 = 21469049) B21469049
theorem B2516609 : Blo 992597 2516609 := bstep (se 2 (by rfl) ⟨943728, by rfl⟩ : syracuseStep 2516609 = 1887457) B1887457
theorem B13592227 : Blo 992597 13592227 := bstep (se 1 (by rfl) ⟨10194170, by rfl⟩ : syracuseStep 13592227 = 20388341) B20388341
theorem B8480639 : Blo 992597 8480639 := bstep (se 1 (by rfl) ⟨6360479, by rfl⟩ : syracuseStep 8480639 = 12720959) B12720959
theorem B11626415 : Blo 992597 11626415 := bstep (se 1 (by rfl) ⟨8719811, by rfl⟩ : syracuseStep 11626415 = 17439623) B17439623
theorem B11331575 : Blo 992597 11331575 := bstep (se 1 (by rfl) ⟨8498681, by rfl⟩ : syracuseStep 11331575 = 16997363) B16997363
theorem B8415677 : Blo 992597 8415677 := bstep (se 3 (by rfl) ⟨1577939, by rfl⟩ : syracuseStep 8415677 = 3155879) B3155879
theorem B2157263 : Blo 992597 2157263 := bstep (se 1 (by rfl) ⟨1617947, by rfl⟩ : syracuseStep 2157263 = 3235895) B3235895
theorem B2550599 : Blo 992597 2550599 := bstep (se 1 (by rfl) ⟨1912949, by rfl⟩ : syracuseStep 2550599 = 3825899) B3825899
theorem B58158161 : Blo 992597 58158161 := bstep (se 2 (by rfl) ⟨21809310, by rfl⟩ : syracuseStep 58158161 = 43618621) B43618621
theorem B5041277 : Blo 992597 5041277 := bstep (se 3 (by rfl) ⟨945239, by rfl⟩ : syracuseStep 5041277 = 1890479) B1890479
theorem B9071779 : Blo 992597 9071779 := bstep (se 1 (by rfl) ⟨6803834, by rfl⟩ : syracuseStep 9071779 = 13607669) B13607669
theorem B11333033 : Blo 992597 11333033 := bstep (se 2 (by rfl) ⟨4249887, by rfl⟩ : syracuseStep 11333033 = 8499775) B8499775
theorem B46591483 : Blo 992597 46591483 := bstep (se 1 (by rfl) ⟨34943612, by rfl⟩ : syracuseStep 46591483 = 69887225) B69887225
theorem B4256039 : Blo 992597 4256039 := bstep (se 1 (by rfl) ⟨3192029, by rfl⟩ : syracuseStep 4256039 = 6384059) B6384059
theorem B18149831 : Blo 992597 18149831 := bstep (se 1 (by rfl) ⟨13612373, by rfl⟩ : syracuseStep 18149831 = 27224747) B27224747
theorem B6452561 : Blo 992597 6452561 := bstep (se 2 (by rfl) ⟨2419710, by rfl⟩ : syracuseStep 6452561 = 4839421) B4839421
theorem B8058287 : Blo 992597 8058287 := bstep (se 1 (by rfl) ⟨6043715, by rfl⟩ : syracuseStep 8058287 = 12087431) B12087431
theorem B7567505 : Blo 992597 7567505 := bstep (se 2 (by rfl) ⟨2837814, by rfl⟩ : syracuseStep 7567505 = 5675629) B5675629
theorem B5667155 : Blo 992597 5667155 := bstep (se 1 (by rfl) ⟨4250366, by rfl⟩ : syracuseStep 5667155 = 8500733) B8500733
theorem B9567017 : Blo 992597 9567017 := bstep (se 2 (by rfl) ⟨3587631, by rfl⟩ : syracuseStep 9567017 = 7175263) B7175263
theorem B2522137 : Blo 992597 2522137 := bstep (se 2 (by rfl) ⟨945801, by rfl⟩ : syracuseStep 2522137 = 1891603) B1891603
theorem B11500775 : Blo 992597 11500775 := bstep (se 1 (by rfl) ⟨8625581, by rfl⟩ : syracuseStep 11500775 = 17251163) B17251163
theorem B10747151 : Blo 992597 10747151 := bstep (se 1 (by rfl) ⟨8060363, by rfl⟩ : syracuseStep 10747151 = 16120727) B16120727
theorem B3768839 : Blo 992597 3768839 := bstep (se 1 (by rfl) ⟨2826629, by rfl⟩ : syracuseStep 3768839 = 5653259) B5653259
theorem B12092591 : Blo 992597 12092591 := bstep (se 1 (by rfl) ⟨9069443, by rfl⟩ : syracuseStep 12092591 = 18138887) B18138887
theorem B22939307 : Blo 992597 22939307 := bstep (se 1 (by rfl) ⟨17204480, by rfl⟩ : syracuseStep 22939307 = 34408961) B34408961
theorem B18122969 : Blo 992597 18122969 := bstep (se 2 (by rfl) ⟨6796113, by rfl⟩ : syracuseStep 18122969 = 13592227) B13592227
theorem B3770783 : Blo 992597 3770783 := bstep (se 1 (by rfl) ⟨2828087, by rfl⟩ : syracuseStep 3770783 = 5656175) B5656175
theorem B7178813 : Blo 992597 7178813 := bstep (se 3 (by rfl) ⟨1346027, by rfl⟩ : syracuseStep 7178813 = 2692055) B2692055
theorem B17206829 : Blo 992597 17206829 := bstep (se 3 (by rfl) ⟨3226280, by rfl⟩ : syracuseStep 17206829 = 6452561) B6452561
theorem B1675471 : Blo 992597 1675471 := bstep (se 1 (by rfl) ⟨1256603, by rfl⟩ : syracuseStep 1675471 = 2513207) B2513207
theorem B12095705 : Blo 992597 12095705 := bstep (se 2 (by rfl) ⟨4535889, by rfl⟩ : syracuseStep 12095705 = 9071779) B9071779
theorem B13635809 : Blo 992597 13635809 := bstep (se 2 (by rfl) ⟨5113428, by rfl⟩ : syracuseStep 13635809 = 10226857) B10226857
theorem B1676153 : Blo 992597 1676153 := bstep (se 2 (by rfl) ⟨628557, by rfl⟩ : syracuseStep 1676153 = 1257115) B1257115
theorem B2233655 : Blo 992597 2233655 := bstep (se 1 (by rfl) ⟨1675241, by rfl⟩ : syracuseStep 2233655 = 3350483) B3350483
theorem B2233727 : Blo 992597 2233727 := bstep (se 1 (by rfl) ⟨1675295, by rfl⟩ : syracuseStep 2233727 = 3350591) B3350591
theorem B15308453 : Blo 992597 15308453 := bstep (se 4 (by rfl) ⟨1435167, by rfl⟩ : syracuseStep 15308453 = 2870335) B2870335
theorem B1414847 : Blo 992597 1414847 := bstep (se 1 (by rfl) ⟨1061135, by rfl⟩ : syracuseStep 1414847 = 2122271) B2122271
theorem B2234303 : Blo 992597 2234303 := bstep (se 1 (by rfl) ⟨1675727, by rfl⟩ : syracuseStep 2234303 = 3351455) B3351455
theorem B9541799 : Blo 992597 9541799 := bstep (se 1 (by rfl) ⟨7156349, by rfl⟩ : syracuseStep 9541799 = 14312699) B14312699
theorem B1677739 : Blo 992597 1677739 := bstep (se 1 (by rfl) ⟨1258304, by rfl⟩ : syracuseStep 1677739 = 2516609) B2516609
theorem B11344697 : Blo 992597 11344697 := bstep (se 2 (by rfl) ⟨4254261, by rfl⟩ : syracuseStep 11344697 = 8508523) B8508523
theorem B5610451 : Blo 992597 5610451 := bstep (se 1 (by rfl) ⟨4207838, by rfl⟩ : syracuseStep 5610451 = 8415677) B8415677
theorem B1678441 : Blo 992597 1678441 := bstep (se 2 (by rfl) ⟨629415, by rfl⟩ : syracuseStep 1678441 = 1258831) B1258831
theorem B38772107 : Blo 992597 38772107 := bstep (se 1 (by rfl) ⟨29079080, by rfl⟩ : syracuseStep 38772107 = 58158161) B58158161
theorem B24879005 : Blo 992597 24879005 := bstep (se 3 (by rfl) ⟨4664813, by rfl⟩ : syracuseStep 24879005 = 9329627) B9329627
theorem B2236319 : Blo 992597 2236319 := bstep (se 1 (by rfl) ⟨1677239, by rfl⟩ : syracuseStep 2236319 = 3354479) B3354479
theorem B12099887 : Blo 992597 12099887 := bstep (se 1 (by rfl) ⟨9074915, by rfl⟩ : syracuseStep 12099887 = 18149831) B18149831
theorem B3351131 : Blo 992597 3351131 := bstep (se 1 (by rfl) ⟨2513348, by rfl⟩ : syracuseStep 3351131 = 5026697) B5026697
theorem B3778103 : Blo 992597 3778103 := bstep (se 1 (by rfl) ⟨2833577, by rfl⟩ : syracuseStep 3778103 = 5667155) B5667155
theorem B992923 : Blo 992597 992923 := bstep (se 1 (by rfl) ⟨744692, by rfl⟩ : syracuseStep 992923 = 1489385) B1489385
theorem B5383871 : Blo 992597 5383871 := bstep (se 1 (by rfl) ⟨4037903, by rfl⟩ : syracuseStep 5383871 = 8075807) B8075807
theorem B993351 : Blo 992597 993351 := bstep (se 1 (by rfl) ⟨745013, by rfl⟩ : syracuseStep 993351 = 1490027) B1490027
theorem B993439 : Blo 992597 993439 := bstep (se 1 (by rfl) ⟨745079, by rfl⟩ : syracuseStep 993439 = 1490159) B1490159
theorem B993511 : Blo 992597 993511 := bstep (se 1 (by rfl) ⟨745133, by rfl⟩ : syracuseStep 993511 = 1490267) B1490267
theorem B994175 : Blo 992597 994175 := bstep (se 1 (by rfl) ⟨745631, by rfl⟩ : syracuseStep 994175 = 1491263) B1491263
theorem B994415 : Blo 992597 994415 := bstep (se 1 (by rfl) ⟨745811, by rfl⟩ : syracuseStep 994415 = 1491623) B1491623
theorem B994463 : Blo 992597 994463 := bstep (se 1 (by rfl) ⟨745847, by rfl⟩ : syracuseStep 994463 = 1491695) B1491695
theorem B994511 : Blo 992597 994511 := bstep (se 1 (by rfl) ⟨745883, by rfl⟩ : syracuseStep 994511 = 1491767) B1491767
theorem B994587 : Blo 992597 994587 := bstep (se 1 (by rfl) ⟨745940, by rfl⟩ : syracuseStep 994587 = 1491881) B1491881
theorem B994843 : Blo 992597 994843 := bstep (se 1 (by rfl) ⟨746132, by rfl⟩ : syracuseStep 994843 = 1492265) B1492265
theorem B5025401 : Blo 992597 5025401 := bstep (se 2 (by rfl) ⟨1884525, by rfl⟩ : syracuseStep 5025401 = 3769051) B3769051
theorem B11316995 : Blo 992597 11316995 := bstep (se 1 (by rfl) ⟨8487746, by rfl⟩ : syracuseStep 11316995 = 16975493) B16975493
theorem B1257383 : Blo 992597 1257383 := bstep (se 1 (by rfl) ⟨943037, by rfl⟩ : syracuseStep 1257383 = 1886075) B1886075
theorem B2240423 : Blo 992597 2240423 := bstep (se 1 (by rfl) ⟨1680317, by rfl⟩ : syracuseStep 2240423 = 3360635) B3360635
theorem B3354587 : Blo 992597 3354587 := bstep (se 1 (by rfl) ⟨2515940, by rfl⟩ : syracuseStep 3354587 = 5031881) B5031881
theorem B2830571 : Blo 992597 2830571 := bstep (se 1 (by rfl) ⟨2122928, by rfl⟩ : syracuseStep 2830571 = 4245857) B4245857
theorem B995871 : Blo 992597 995871 := bstep (se 1 (by rfl) ⟨746903, by rfl⟩ : syracuseStep 995871 = 1493807) B1493807
theorem B91960055 : Blo 992597 91960055 := bstep (se 1 (by rfl) ⟨68970041, by rfl⟩ : syracuseStep 91960055 = 137940083) B137940083
theorem B996167 : Blo 992597 996167 := bstep (se 1 (by rfl) ⟨747125, by rfl⟩ : syracuseStep 996167 = 1494251) B1494251
theorem B996199 : Blo 992597 996199 := bstep (se 1 (by rfl) ⟨747149, by rfl⟩ : syracuseStep 996199 = 1494299) B1494299
theorem B996223 : Blo 992597 996223 := bstep (se 1 (by rfl) ⟨747167, by rfl⟩ : syracuseStep 996223 = 1494335) B1494335
theorem B3355775 : Blo 992597 3355775 := bstep (se 1 (by rfl) ⟨2516831, by rfl⟩ : syracuseStep 3355775 = 5033663) B5033663
theorem B996511 : Blo 992597 996511 := bstep (se 1 (by rfl) ⟨747383, by rfl⟩ : syracuseStep 996511 = 1494767) B1494767
theorem B5027831 : Blo 992597 5027831 := bstep (se 1 (by rfl) ⟨3770873, by rfl⟩ : syracuseStep 5027831 = 7541747) B7541747
theorem B5027993 : Blo 992597 5027993 := bstep (se 2 (by rfl) ⟨1885497, by rfl⟩ : syracuseStep 5027993 = 3770995) B3770995
theorem B1489703 : Blo 992597 1489703 := bstep (se 1 (by rfl) ⟨1117277, by rfl⟩ : syracuseStep 1489703 = 2234555) B2234555
theorem B1490015 : Blo 992597 1490015 := bstep (se 1 (by rfl) ⟨1117511, by rfl⟩ : syracuseStep 1490015 = 2235023) B2235023
theorem B1490411 : Blo 992597 1490411 := bstep (se 1 (by rfl) ⟨1117808, by rfl⟩ : syracuseStep 1490411 = 2235617) B2235617
theorem B1490459 : Blo 992597 1490459 := bstep (se 1 (by rfl) ⟨1117844, by rfl⟩ : syracuseStep 1490459 = 2235689) B2235689
theorem B1490639 : Blo 992597 1490639 := bstep (se 1 (by rfl) ⟨1117979, by rfl⟩ : syracuseStep 1490639 = 2235959) B2235959
theorem B3587921 : Blo 992597 3587921 := bstep (se 2 (by rfl) ⟨1345470, by rfl⟩ : syracuseStep 3587921 = 2690941) B2690941
theorem B1491047 : Blo 992597 1491047 := bstep (se 1 (by rfl) ⟨1118285, by rfl⟩ : syracuseStep 1491047 = 2236571) B2236571
theorem B1491071 : Blo 992597 1491071 := bstep (se 1 (by rfl) ⟨1118303, by rfl⟩ : syracuseStep 1491071 = 2236607) B2236607
theorem B16138369 : Blo 992597 16138369 := bstep (se 2 (by rfl) ⟨6051888, by rfl⟩ : syracuseStep 16138369 = 12103777) B12103777
theorem B3358907 : Blo 992597 3358907 := bstep (se 1 (by rfl) ⟨2519180, by rfl⟩ : syracuseStep 3358907 = 5038361) B5038361
theorem B1491497 : Blo 992597 1491497 := bstep (se 2 (by rfl) ⟨559311, by rfl⟩ : syracuseStep 1491497 = 1118623) B1118623
theorem B1491743 : Blo 992597 1491743 := bstep (se 1 (by rfl) ⟨1118807, by rfl⟩ : syracuseStep 1491743 = 2237615) B2237615
theorem B1491839 : Blo 992597 1491839 := bstep (se 1 (by rfl) ⟨1118879, by rfl⟩ : syracuseStep 1491839 = 2237759) B2237759
theorem B1491935 : Blo 992597 1491935 := bstep (se 1 (by rfl) ⟨1118951, by rfl⟩ : syracuseStep 1491935 = 2237903) B2237903
theorem B1492199 : Blo 992597 1492199 := bstep (se 1 (by rfl) ⟨1119149, by rfl⟩ : syracuseStep 1492199 = 2238299) B2238299
theorem B5653759 : Blo 992597 5653759 := bstep (se 1 (by rfl) ⟨4240319, by rfl⟩ : syracuseStep 5653759 = 8480639) B8480639
theorem B7750943 : Blo 992597 7750943 := bstep (se 1 (by rfl) ⟨5813207, by rfl⟩ : syracuseStep 7750943 = 11626415) B11626415
theorem B7554383 : Blo 992597 7554383 := bstep (se 1 (by rfl) ⟨5665787, by rfl⟩ : syracuseStep 7554383 = 11331575) B11331575
theorem B12764789 : Blo 992597 12764789 := bstep (se 5 (by rfl) ⟨598349, by rfl⟩ : syracuseStep 12764789 = 1196699) B1196699
theorem B1885855 : Blo 992597 1885855 := bstep (se 1 (by rfl) ⟨1414391, by rfl⟩ : syracuseStep 1885855 = 2828783) B2828783
theorem B1492649 : Blo 992597 1492649 := bstep (se 2 (by rfl) ⟨559743, by rfl⟩ : syracuseStep 1492649 = 1119487) B1119487
theorem B36292535 : Blo 992597 36292535 := bstep (se 1 (by rfl) ⟨27219401, by rfl⟩ : syracuseStep 36292535 = 54438803) B54438803
theorem B1493033 : Blo 992597 1493033 := bstep (se 2 (by rfl) ⟨559887, by rfl⟩ : syracuseStep 1493033 = 1119775) B1119775
theorem B3360851 : Blo 992597 3360851 := bstep (se 1 (by rfl) ⟨2520638, by rfl⟩ : syracuseStep 3360851 = 5041277) B5041277
theorem B12077309 : Blo 992597 12077309 := bstep (se 3 (by rfl) ⟨2264495, by rfl⟩ : syracuseStep 12077309 = 4528991) B4528991
theorem B7555355 : Blo 992597 7555355 := bstep (se 1 (by rfl) ⟨5666516, by rfl⟩ : syracuseStep 7555355 = 11333033) B11333033
theorem B4835647 : Blo 992597 4835647 := bstep (se 1 (by rfl) ⟨3626735, by rfl⟩ : syracuseStep 4835647 = 7253471) B7253471
theorem B1886561 : Blo 992597 1886561 := bstep (se 2 (by rfl) ⟨707460, by rfl⟩ : syracuseStep 1886561 = 1414921) B1414921
theorem B1493447 : Blo 992597 1493447 := bstep (se 1 (by rfl) ⟨1120085, by rfl⟩ : syracuseStep 1493447 = 2240171) B2240171
theorem B1493735 : Blo 992597 1493735 := bstep (se 1 (by rfl) ⟨1120301, by rfl⟩ : syracuseStep 1493735 = 2240603) B2240603
theorem B1886971 : Blo 992597 1886971 := bstep (se 1 (by rfl) ⟨1415228, by rfl⟩ : syracuseStep 1886971 = 2830457) B2830457
theorem B2837359 : Blo 992597 2837359 := bstep (se 1 (by rfl) ⟨2128019, by rfl⟩ : syracuseStep 2837359 = 4256039) B4256039
theorem B1493927 : Blo 992597 1493927 := bstep (se 1 (by rfl) ⟨1120445, by rfl⟩ : syracuseStep 1493927 = 2240891) B2240891
theorem B1493993 : Blo 992597 1493993 := bstep (se 2 (by rfl) ⟨560247, by rfl⟩ : syracuseStep 1493993 = 1120495) B1120495
theorem B1493999 : Blo 992597 1493999 := bstep (se 1 (by rfl) ⟨1120499, by rfl⟩ : syracuseStep 1493999 = 2240999) B2240999
theorem B1494107 : Blo 992597 1494107 := bstep (se 1 (by rfl) ⟨1120580, by rfl⟩ : syracuseStep 1494107 = 2241161) B2241161
theorem B33214151 : Blo 992597 33214151 := bstep (se 1 (by rfl) ⟨24910613, by rfl⟩ : syracuseStep 33214151 = 49821227) B49821227
theorem B1494779 : Blo 992597 1494779 := bstep (se 1 (by rfl) ⟨1121084, by rfl⟩ : syracuseStep 1494779 = 2242169) B2242169
theorem B1494875 : Blo 992597 1494875 := bstep (se 1 (by rfl) ⟨1121156, by rfl⟩ : syracuseStep 1494875 = 2242313) B2242313
theorem B7655359 : Blo 992597 7655359 := bstep (se 1 (by rfl) ⟨5741519, by rfl⟩ : syracuseStep 7655359 = 11483039) B11483039
theorem B3362849 : Blo 992597 3362849 := bstep (se 2 (by rfl) ⟨1261068, by rfl⟩ : syracuseStep 3362849 = 2522137) B2522137
theorem B6378011 : Blo 992597 6378011 := bstep (se 1 (by rfl) ⟨4783508, by rfl⟩ : syracuseStep 6378011 = 9567017) B9567017
theorem B7164767 : Blo 992597 7164767 := bstep (se 1 (by rfl) ⟨5373575, by rfl⟩ : syracuseStep 7164767 = 10747151) B10747151
theorem B1889705 : Blo 992597 1889705 := bstep (se 2 (by rfl) ⟨708639, by rfl⟩ : syracuseStep 1889705 = 1417279) B1417279
theorem B2513551 : Blo 992597 2513551 := bstep (se 1 (by rfl) ⟨1885163, by rfl⟩ : syracuseStep 2513551 = 3770327) B3770327
theorem B7167305 : Blo 992597 7167305 := bstep (se 2 (by rfl) ⟨2687739, by rfl⟩ : syracuseStep 7167305 = 5375479) B5375479
theorem B11493937 : Blo 992597 11493937 := bstep (se 2 (by rfl) ⟨4310226, by rfl⟩ : syracuseStep 11493937 = 8620453) B8620453
theorem B28632203 : Blo 992597 28632203 := bstep (se 1 (by rfl) ⟨21474152, by rfl⟩ : syracuseStep 28632203 = 42948305) B42948305
theorem B2123167 : Blo 992597 2123167 := bstep (se 1 (by rfl) ⟨1592375, by rfl⟩ : syracuseStep 2123167 = 3184751) B3184751
theorem B62121977 : Blo 992597 62121977 := bstep (se 2 (by rfl) ⟨23295741, by rfl⟩ : syracuseStep 62121977 = 46591483) B46591483
theorem B2124073 : Blo 992597 2124073 := bstep (se 2 (by rfl) ⟨796527, by rfl⟩ : syracuseStep 2124073 = 1593055) B1593055
theorem B11495789 : Blo 992597 11495789 := bstep (se 3 (by rfl) ⟨2155460, by rfl⟩ : syracuseStep 11495789 = 4310921) B4310921
theorem B3828143 : Blo 992597 3828143 := bstep (se 1 (by rfl) ⟨2871107, by rfl⟩ : syracuseStep 3828143 = 5742215) B5742215
theorem B18180713 : Blo 992597 18180713 := bstep (se 2 (by rfl) ⟨6817767, by rfl⟩ : syracuseStep 18180713 = 13635535) B13635535
theorem B31058939 : Blo 992597 31058939 := bstep (se 1 (by rfl) ⟨23294204, by rfl⟩ : syracuseStep 31058939 = 46588409) B46588409
theorem B9071995 : Blo 992597 9071995 := bstep (se 1 (by rfl) ⟨6803996, by rfl⟩ : syracuseStep 9071995 = 13607993) B13607993
theorem B2519009 : Blo 992597 2519009 := bstep (se 2 (by rfl) ⟨944628, by rfl⟩ : syracuseStep 2519009 = 1889257) B1889257
theorem B7565561 : Blo 992597 7565561 := bstep (se 2 (by rfl) ⟨2837085, by rfl⟩ : syracuseStep 7565561 = 5674171) B5674171
theorem B1438175 : Blo 992597 1438175 := bstep (se 1 (by rfl) ⟨1078631, by rfl⟩ : syracuseStep 1438175 = 2157263) B2157263
theorem B1700399 : Blo 992597 1700399 := bstep (se 1 (by rfl) ⟨1275299, by rfl⟩ : syracuseStep 1700399 = 2550599) B2550599
theorem B5372191 : Blo 992597 5372191 := bstep (se 1 (by rfl) ⟨4029143, by rfl⟩ : syracuseStep 5372191 = 8058287) B8058287
theorem B19102351 : Blo 992597 19102351 := bstep (se 1 (by rfl) ⟨14326763, by rfl⟩ : syracuseStep 19102351 = 28653527) B28653527
theorem B5045003 : Blo 992597 5045003 := bstep (se 1 (by rfl) ⟨3783752, by rfl⟩ : syracuseStep 5045003 = 7567505) B7567505
theorem B11500957 : Blo 992597 11500957 := bstep (se 3 (by rfl) ⟨2156429, by rfl⟩ : syracuseStep 11500957 = 4312859) B4312859
theorem B7667183 : Blo 992597 7667183 := bstep (se 1 (by rfl) ⟨5750387, by rfl⟩ : syracuseStep 7667183 = 11500775) B11500775
theorem B3833407 : Blo 992597 3833407 := bstep (se 1 (by rfl) ⟨2875055, by rfl⟩ : syracuseStep 3833407 = 5750111) B5750111
theorem B2391707 : Blo 992597 2391707 := bstep (se 1 (by rfl) ⟨1793780, by rfl⟩ : syracuseStep 2391707 = 3587561) B3587561
theorem B4030345 : Blo 992597 4030345 := bstep (se 2 (by rfl) ⟨1511379, by rfl⟩ : syracuseStep 4030345 = 3022759) B3022759
theorem B7176185 : Blo 992597 7176185 := bstep (se 2 (by rfl) ⟨2691069, by rfl⟩ : syracuseStep 7176185 = 5382139) B5382139
theorem B8061727 : Blo 992597 8061727 := bstep (se 1 (by rfl) ⟨6046295, by rfl⟩ : syracuseStep 8061727 = 12092591) B12092591
theorem B3835133 : Blo 992597 3835133 := bstep (se 3 (by rfl) ⟨719087, by rfl⟩ : syracuseStep 3835133 = 1438175) B1438175
theorem B7538345 : Blo 992597 7538345 := bstep (se 2 (by rfl) ⟨2826879, by rfl⟩ : syracuseStep 7538345 = 5653759) B5653759
theorem B4785875 : Blo 992597 4785875 := bstep (se 1 (by rfl) ⟨3589406, by rfl⟩ : syracuseStep 4785875 = 7178813) B7178813
theorem B11471219 : Blo 992597 11471219 := bstep (se 1 (by rfl) ⟨8603414, by rfl⟩ : syracuseStep 11471219 = 17206829) B17206829
theorem B8063803 : Blo 992597 8063803 := bstep (se 1 (by rfl) ⟨6047852, by rfl⟩ : syracuseStep 8063803 = 12095705) B12095705
theorem B1117435 : Blo 992597 1117435 := bstep (se 1 (by rfl) ⟨838076, by rfl⟩ : syracuseStep 1117435 = 1676153) B1676153
theorem B6361199 : Blo 992597 6361199 := bstep (se 1 (by rfl) ⟨4770899, by rfl⟩ : syracuseStep 6361199 = 9541799) B9541799
theorem B12095993 : Blo 992597 12095993 := bstep (se 2 (by rfl) ⟨4535997, by rfl⟩ : syracuseStep 12095993 = 9071995) B9071995
theorem B3772925 : Blo 992597 3772925 := bstep (se 3 (by rfl) ⟨707423, by rfl⟩ : syracuseStep 3772925 = 1414847) B1414847
theorem B16586003 : Blo 992597 16586003 := bstep (se 1 (by rfl) ⟨12439502, by rfl⟩ : syracuseStep 16586003 = 24879005) B24879005
theorem B8066591 : Blo 992597 8066591 := bstep (se 1 (by rfl) ⟨6049943, by rfl⟩ : syracuseStep 8066591 = 12099887) B12099887
theorem B2233961 : Blo 992597 2233961 := bstep (se 2 (by rfl) ⟨837735, by rfl⟩ : syracuseStep 2233961 = 1675471) B1675471
theorem B2234087 : Blo 992597 2234087 := bstep (se 1 (by rfl) ⟨1675565, by rfl⟩ : syracuseStep 2234087 = 3351131) B3351131
theorem B3350267 : Blo 992597 3350267 := bstep (se 1 (by rfl) ⟨2512700, by rfl⟩ : syracuseStep 3350267 = 5025401) B5025401
theorem B7544663 : Blo 992597 7544663 := bstep (se 1 (by rfl) ⟨5658497, by rfl⟩ : syracuseStep 7544663 = 11316995) B11316995
theorem B2236391 : Blo 992597 2236391 := bstep (se 1 (by rfl) ⟨1677293, by rfl⟩ : syracuseStep 2236391 = 3354587) B3354587
theorem B1679339 : Blo 992597 1679339 := bstep (se 1 (by rfl) ⟨1259504, by rfl⟩ : syracuseStep 1679339 = 2519009) B2519009
theorem B2236985 : Blo 992597 2236985 := bstep (se 2 (by rfl) ⟨838869, by rfl⟩ : syracuseStep 2236985 = 1677739) B1677739
theorem B2237183 : Blo 992597 2237183 := bstep (se 1 (by rfl) ⟨1677887, by rfl⟩ : syracuseStep 2237183 = 3355775) B3355775
theorem B3351401 : Blo 992597 3351401 := bstep (se 2 (by rfl) ⟨1256775, by rfl⟩ : syracuseStep 3351401 = 2513551) B2513551
theorem B25469801 : Blo 992597 25469801 := bstep (se 2 (by rfl) ⟨9551175, by rfl⟩ : syracuseStep 25469801 = 19102351) B19102351
theorem B7480601 : Blo 992597 7480601 := bstep (se 2 (by rfl) ⟨2805225, by rfl⟩ : syracuseStep 7480601 = 5610451) B5610451
theorem B3351887 : Blo 992597 3351887 := bstep (se 1 (by rfl) ⟨2513915, by rfl⟩ : syracuseStep 3351887 = 5027831) B5027831
theorem B3351995 : Blo 992597 3351995 := bstep (se 1 (by rfl) ⟨2513996, by rfl⟩ : syracuseStep 3351995 = 5027993) B5027993
theorem B2237921 : Blo 992597 2237921 := bstep (se 2 (by rfl) ⟨839220, by rfl⟩ : syracuseStep 2237921 = 1678441) B1678441
theorem B993135 : Blo 992597 993135 := bstep (se 1 (by rfl) ⟨744851, by rfl⟩ : syracuseStep 993135 = 1489703) B1489703
theorem B993343 : Blo 992597 993343 := bstep (se 1 (by rfl) ⟨745007, by rfl⟩ : syracuseStep 993343 = 1490015) B1490015
theorem B993607 : Blo 992597 993607 := bstep (se 1 (by rfl) ⟨745205, by rfl⟩ : syracuseStep 993607 = 1490411) B1490411
theorem B993639 : Blo 992597 993639 := bstep (se 1 (by rfl) ⟨745229, by rfl⟩ : syracuseStep 993639 = 1490459) B1490459
theorem B3353021 : Blo 992597 3353021 := bstep (se 3 (by rfl) ⟨628691, by rfl⟩ : syracuseStep 3353021 = 1257383) B1257383
theorem B993759 : Blo 992597 993759 := bstep (se 1 (by rfl) ⟨745319, by rfl⟩ : syracuseStep 993759 = 1490639) B1490639
theorem B994031 : Blo 992597 994031 := bstep (se 1 (by rfl) ⟨745523, by rfl⟩ : syracuseStep 994031 = 1491047) B1491047
theorem B994047 : Blo 992597 994047 := bstep (se 1 (by rfl) ⟨745535, by rfl⟩ : syracuseStep 994047 = 1491071) B1491071
theorem B2239271 : Blo 992597 2239271 := bstep (se 1 (by rfl) ⟨1679453, by rfl⟩ : syracuseStep 2239271 = 3358907) B3358907
theorem B994331 : Blo 992597 994331 := bstep (se 1 (by rfl) ⟨745748, by rfl⟩ : syracuseStep 994331 = 1491497) B1491497
theorem B994495 : Blo 992597 994495 := bstep (se 1 (by rfl) ⟨745871, by rfl⟩ : syracuseStep 994495 = 1491743) B1491743
theorem B994559 : Blo 992597 994559 := bstep (se 1 (by rfl) ⟨745919, by rfl⟩ : syracuseStep 994559 = 1491839) B1491839
theorem B994623 : Blo 992597 994623 := bstep (se 1 (by rfl) ⟨745967, by rfl⟩ : syracuseStep 994623 = 1491935) B1491935
theorem B994799 : Blo 992597 994799 := bstep (se 1 (by rfl) ⟨746099, by rfl⟩ : syracuseStep 994799 = 1492199) B1492199
theorem B995099 : Blo 992597 995099 := bstep (se 1 (by rfl) ⟨746324, by rfl⟩ : syracuseStep 995099 = 1492649) B1492649
theorem B24195023 : Blo 992597 24195023 := bstep (se 1 (by rfl) ⟨18146267, by rfl⟩ : syracuseStep 24195023 = 36292535) B36292535
theorem B995355 : Blo 992597 995355 := bstep (se 1 (by rfl) ⟨746516, by rfl⟩ : syracuseStep 995355 = 1493033) B1493033
theorem B2240567 : Blo 992597 2240567 := bstep (se 1 (by rfl) ⟨1680425, by rfl⟩ : syracuseStep 2240567 = 3360851) B3360851
theorem B1257707 : Blo 992597 1257707 := bstep (se 1 (by rfl) ⟨943280, by rfl⟩ : syracuseStep 1257707 = 1886561) B1886561
theorem B995631 : Blo 992597 995631 := bstep (se 1 (by rfl) ⟨746723, by rfl⟩ : syracuseStep 995631 = 1493447) B1493447
theorem B995823 : Blo 992597 995823 := bstep (se 1 (by rfl) ⟨746867, by rfl⟩ : syracuseStep 995823 = 1493735) B1493735
theorem B2830889 : Blo 992597 2830889 := bstep (se 2 (by rfl) ⟨1061583, by rfl⟩ : syracuseStep 2830889 = 2123167) B2123167
theorem B995951 : Blo 992597 995951 := bstep (se 1 (by rfl) ⟨746963, by rfl⟩ : syracuseStep 995951 = 1493927) B1493927
theorem B995995 : Blo 992597 995995 := bstep (se 1 (by rfl) ⟨746996, by rfl⟩ : syracuseStep 995995 = 1493993) B1493993
theorem B995999 : Blo 992597 995999 := bstep (se 1 (by rfl) ⟨746999, by rfl⟩ : syracuseStep 995999 = 1493999) B1493999
theorem B996071 : Blo 992597 996071 := bstep (se 1 (by rfl) ⟨747053, by rfl⟩ : syracuseStep 996071 = 1494107) B1494107
theorem B996519 : Blo 992597 996519 := bstep (se 1 (by rfl) ⟨747389, by rfl⟩ : syracuseStep 996519 = 1494779) B1494779
theorem B996583 : Blo 992597 996583 := bstep (se 1 (by rfl) ⟨747437, by rfl⟩ : syracuseStep 996583 = 1494875) B1494875
theorem B2241899 : Blo 992597 2241899 := bstep (se 1 (by rfl) ⟨1681424, by rfl⟩ : syracuseStep 2241899 = 3362849) B3362849
theorem B9090539 : Blo 992597 9090539 := bstep (se 1 (by rfl) ⟨6817904, by rfl⟩ : syracuseStep 9090539 = 13635809) B13635809
theorem B2832097 : Blo 992597 2832097 := bstep (se 2 (by rfl) ⟨1062036, by rfl⟩ : syracuseStep 2832097 = 2124073) B2124073
theorem B1489103 : Blo 992597 1489103 := bstep (se 1 (by rfl) ⟨1116827, by rfl⟩ : syracuseStep 1489103 = 2233655) B2233655
theorem B1489151 : Blo 992597 1489151 := bstep (se 1 (by rfl) ⟨1116863, by rfl⟩ : syracuseStep 1489151 = 2233727) B2233727
theorem B1259803 : Blo 992597 1259803 := bstep (se 1 (by rfl) ⟨944852, by rfl⟩ : syracuseStep 1259803 = 1889705) B1889705
theorem B3783145 : Blo 992597 3783145 := bstep (se 2 (by rfl) ⟨1418679, by rfl⟩ : syracuseStep 3783145 = 2837359) B2837359
theorem B1489535 : Blo 992597 1489535 := bstep (se 1 (by rfl) ⟨1117151, by rfl⟩ : syracuseStep 1489535 = 2234303) B2234303
theorem B10207145 : Blo 992597 10207145 := bstep (se 2 (by rfl) ⟨3827679, by rfl⟩ : syracuseStep 10207145 = 7655359) B7655359
theorem B1490879 : Blo 992597 1490879 := bstep (se 1 (by rfl) ⟨1118159, by rfl⟩ : syracuseStep 1490879 = 2236319) B2236319
theorem B19088135 : Blo 992597 19088135 := bstep (se 1 (by rfl) ⟨14316101, by rfl⟩ : syracuseStep 19088135 = 28632203) B28632203
theorem B3589247 : Blo 992597 3589247 := bstep (se 1 (by rfl) ⟨2691935, by rfl⟩ : syracuseStep 3589247 = 5383871) B5383871
theorem B4784123 : Blo 992597 4784123 := bstep (se 1 (by rfl) ⟨3588092, by rfl⟩ : syracuseStep 4784123 = 7176185) B7176185
theorem B1493615 : Blo 992597 1493615 := bstep (se 1 (by rfl) ⟨1120211, by rfl⟩ : syracuseStep 1493615 = 2240423) B2240423
theorem B1887047 : Blo 992597 1887047 := bstep (se 1 (by rfl) ⟨1415285, by rfl⟩ : syracuseStep 1887047 = 2830571) B2830571
theorem B1133599 : Blo 992597 1133599 := bstep (se 1 (by rfl) ⟨850199, by rfl⟩ : syracuseStep 1133599 = 1700399) B1700399
theorem B7162921 : Blo 992597 7162921 := bstep (se 2 (by rfl) ⟨2686095, by rfl⟩ : syracuseStep 7162921 = 5372191) B5372191
theorem B6377885 : Blo 992597 6377885 := bstep (se 3 (by rfl) ⟨1195853, by rfl⟩ : syracuseStep 6377885 = 2391707) B2391707
theorem B3363335 : Blo 992597 3363335 := bstep (se 1 (by rfl) ⟨2522501, by rfl⟩ : syracuseStep 3363335 = 5045003) B5045003
theorem B21517825 : Blo 992597 21517825 := bstep (se 2 (by rfl) ⟨8069184, by rfl⟩ : syracuseStep 21517825 = 16138369) B16138369
theorem B2512559 : Blo 992597 2512559 := bstep (se 1 (by rfl) ⟨1884419, by rfl⟩ : syracuseStep 2512559 = 3768839) B3768839
theorem B15325249 : Blo 992597 15325249 := bstep (se 2 (by rfl) ⟨5746968, by rfl⟩ : syracuseStep 15325249 = 11493937) B11493937
theorem B5167295 : Blo 992597 5167295 := bstep (se 1 (by rfl) ⟨3875471, by rfl⟩ : syracuseStep 5167295 = 7750943) B7750943
theorem B5036255 : Blo 992597 5036255 := bstep (se 1 (by rfl) ⟨3777191, by rfl⟩ : syracuseStep 5036255 = 7554383) B7554383
theorem B8509859 : Blo 992597 8509859 := bstep (se 1 (by rfl) ⟨6382394, by rfl⟩ : syracuseStep 8509859 = 12764789) B12764789
theorem B15292871 : Blo 992597 15292871 := bstep (se 1 (by rfl) ⟨11469653, by rfl⟩ : syracuseStep 15292871 = 22939307) B22939307
theorem B12081979 : Blo 992597 12081979 := bstep (se 1 (by rfl) ⟨9061484, by rfl⟩ : syracuseStep 12081979 = 18122969) B18122969
theorem B5036903 : Blo 992597 5036903 := bstep (se 1 (by rfl) ⟨3777677, by rfl⟩ : syracuseStep 5036903 = 7555355) B7555355
theorem B2513855 : Blo 992597 2513855 := bstep (se 1 (by rfl) ⟨1885391, by rfl⟩ : syracuseStep 2513855 = 3770783) B3770783
theorem B2514473 : Blo 992597 2514473 := bstep (se 2 (by rfl) ⟨942927, by rfl⟩ : syracuseStep 2514473 = 1885855) B1885855
theorem B22142767 : Blo 992597 22142767 := bstep (se 1 (by rfl) ⟨16607075, by rfl⟩ : syracuseStep 22142767 = 33214151) B33214151
theorem B4252007 : Blo 992597 4252007 := bstep (se 1 (by rfl) ⟨3189005, by rfl⟩ : syracuseStep 4252007 = 6378011) B6378011
theorem B6447529 : Blo 992597 6447529 := bstep (se 2 (by rfl) ⟨2417823, by rfl⟩ : syracuseStep 6447529 = 4835647) B4835647
theorem B4776511 : Blo 992597 4776511 := bstep (se 1 (by rfl) ⟨3582383, by rfl⟩ : syracuseStep 4776511 = 7164767) B7164767
theorem B2515961 : Blo 992597 2515961 := bstep (se 2 (by rfl) ⟨943485, by rfl⟩ : syracuseStep 2515961 = 1886971) B1886971
theorem B40822541 : Blo 992597 40822541 := bstep (se 3 (by rfl) ⟨7654226, by rfl⟩ : syracuseStep 40822541 = 15308453) B15308453
theorem B7563131 : Blo 992597 7563131 := bstep (se 1 (by rfl) ⟨5672348, by rfl⟩ : syracuseStep 7563131 = 11344697) B11344697
theorem B4778203 : Blo 992597 4778203 := bstep (se 1 (by rfl) ⟨3583652, by rfl⟩ : syracuseStep 4778203 = 7167305) B7167305
theorem B25848071 : Blo 992597 25848071 := bstep (se 1 (by rfl) ⟨19386053, by rfl⟩ : syracuseStep 25848071 = 38772107) B38772107
theorem B32206157 : Blo 992597 32206157 := bstep (se 3 (by rfl) ⟨6038654, by rfl⟩ : syracuseStep 32206157 = 12077309) B12077309
theorem B2518735 : Blo 992597 2518735 := bstep (se 1 (by rfl) ⟨1889051, by rfl⟩ : syracuseStep 2518735 = 3778103) B3778103
theorem B41414651 : Blo 992597 41414651 := bstep (se 1 (by rfl) ⟨31060988, by rfl⟩ : syracuseStep 41414651 = 62121977) B62121977
theorem B7663859 : Blo 992597 7663859 := bstep (se 1 (by rfl) ⟨5747894, by rfl⟩ : syracuseStep 7663859 = 11495789) B11495789
theorem B2552095 : Blo 992597 2552095 := bstep (se 1 (by rfl) ⟨1914071, by rfl⟩ : syracuseStep 2552095 = 3828143) B3828143
theorem B12120475 : Blo 992597 12120475 := bstep (se 1 (by rfl) ⟨9090356, by rfl⟩ : syracuseStep 12120475 = 18180713) B18180713
theorem B20705959 : Blo 992597 20705959 := bstep (se 1 (by rfl) ⟨15529469, by rfl⟩ : syracuseStep 20705959 = 31058939) B31058939
theorem B5043707 : Blo 992597 5043707 := bstep (se 1 (by rfl) ⟨3782780, by rfl⟩ : syracuseStep 5043707 = 7565561) B7565561
theorem B61306703 : Blo 992597 61306703 := bstep (se 1 (by rfl) ⟨45980027, by rfl⟩ : syracuseStep 61306703 = 91960055) B91960055
theorem B15334609 : Blo 992597 15334609 := bstep (se 2 (by rfl) ⟨5750478, by rfl⟩ : syracuseStep 15334609 = 11500957) B11500957
theorem B5111209 : Blo 992597 5111209 := bstep (se 2 (by rfl) ⟨1916703, by rfl⟩ : syracuseStep 5111209 = 3833407) B3833407
theorem B5111455 : Blo 992597 5111455 := bstep (se 1 (by rfl) ⟨3833591, by rfl⟩ : syracuseStep 5111455 = 7667183) B7667183
theorem B5373793 : Blo 992597 5373793 := bstep (se 2 (by rfl) ⟨2015172, by rfl⟩ : syracuseStep 5373793 = 4030345) B4030345
theorem B2391947 : Blo 992597 2391947 := bstep (se 1 (by rfl) ⟨1793960, by rfl⟩ : syracuseStep 2391947 = 3587921) B3587921
theorem B2392831 : Blo 992597 2392831 := bstep (se 1 (by rfl) ⟨1794623, by rfl⟩ : syracuseStep 2392831 = 3589247) B3589247
theorem B2556755 : Blo 992597 2556755 := bstep (se 1 (by rfl) ⟨1917566, by rfl⟩ : syracuseStep 2556755 = 3835133) B3835133
theorem B10748969 : Blo 992597 10748969 := bstep (se 2 (by rfl) ⟨4030863, by rfl⟩ : syracuseStep 10748969 = 8061727) B8061727
theorem B5377727 : Blo 992597 5377727 := bstep (se 1 (by rfl) ⟨4033295, by rfl⟩ : syracuseStep 5377727 = 8066591) B8066591
theorem B10751737 : Blo 992597 10751737 := bstep (se 2 (by rfl) ⟨4031901, by rfl⟩ : syracuseStep 10751737 = 8063803) B8063803
theorem B1675039 : Blo 992597 1675039 := bstep (se 1 (by rfl) ⟨1256279, by rfl⟩ : syracuseStep 1675039 = 2512559) B2512559
theorem B1511465 : Blo 992597 1511465 := bstep (se 2 (by rfl) ⟨566799, by rfl⟩ : syracuseStep 1511465 = 1133599) B1133599
theorem B3444863 : Blo 992597 3444863 := bstep (se 1 (by rfl) ⟨2583647, by rfl⟩ : syracuseStep 3444863 = 5167295) B5167295
theorem B5673239 : Blo 992597 5673239 := bstep (se 1 (by rfl) ⟨4254929, by rfl⟩ : syracuseStep 5673239 = 8509859) B8509859
theorem B10195247 : Blo 992597 10195247 := bstep (se 1 (by rfl) ⟨7646435, by rfl⟩ : syracuseStep 10195247 = 15292871) B15292871
theorem B1675903 : Blo 992597 1675903 := bstep (se 1 (by rfl) ⟨1256927, by rfl⟩ : syracuseStep 1675903 = 2513855) B2513855
theorem B1676315 : Blo 992597 1676315 := bstep (se 1 (by rfl) ⟨1257236, by rfl⟩ : syracuseStep 1676315 = 2514473) B2514473
theorem B2233511 : Blo 992597 2233511 := bstep (se 1 (by rfl) ⟨1675133, by rfl⟩ : syracuseStep 2233511 = 3350267) B3350267
theorem B1119559 : Blo 992597 1119559 := bstep (se 1 (by rfl) ⟨839669, by rfl⟩ : syracuseStep 1119559 = 1679339) B1679339
theorem B16160633 : Blo 992597 16160633 := bstep (se 2 (by rfl) ⟨6060237, by rfl⟩ : syracuseStep 16160633 = 12120475) B12120475
theorem B2234267 : Blo 992597 2234267 := bstep (se 1 (by rfl) ⟨1675700, by rfl⟩ : syracuseStep 2234267 = 3351401) B3351401
theorem B16979867 : Blo 992597 16979867 := bstep (se 1 (by rfl) ⟨12734900, by rfl⟩ : syracuseStep 16979867 = 25469801) B25469801
theorem B1677307 : Blo 992597 1677307 := bstep (se 1 (by rfl) ⟨1257980, by rfl⟩ : syracuseStep 1677307 = 2515961) B2515961
theorem B4987067 : Blo 992597 4987067 := bstep (se 1 (by rfl) ⟨3740300, by rfl⟩ : syracuseStep 4987067 = 7480601) B7480601
theorem B2234591 : Blo 992597 2234591 := bstep (se 1 (by rfl) ⟨1675943, by rfl⟩ : syracuseStep 2234591 = 3351887) B3351887
theorem B2234663 : Blo 992597 2234663 := bstep (se 1 (by rfl) ⟨1675997, by rfl⟩ : syracuseStep 2234663 = 3351995) B3351995
theorem B2235347 : Blo 992597 2235347 := bstep (se 1 (by rfl) ⟨1676510, by rfl⟩ : syracuseStep 2235347 = 3353021) B3353021
theorem B21470771 : Blo 992597 21470771 := bstep (se 1 (by rfl) ⟨16103078, by rfl⟩ : syracuseStep 21470771 = 32206157) B32206157
theorem B3776129 : Blo 992597 3776129 := bstep (se 2 (by rfl) ⟨1416048, by rfl⟩ : syracuseStep 3776129 = 2832097) B2832097
theorem B16130015 : Blo 992597 16130015 := bstep (se 1 (by rfl) ⟨12097511, by rfl⟩ : syracuseStep 16130015 = 24195023) B24195023
theorem B1679737 : Blo 992597 1679737 := bstep (se 2 (by rfl) ⟨629901, by rfl⟩ : syracuseStep 1679737 = 1259803) B1259803
theorem B40871135 : Blo 992597 40871135 := bstep (se 1 (by rfl) ⟨30653351, by rfl⟩ : syracuseStep 40871135 = 61306703) B61306703
theorem B992735 : Blo 992597 992735 := bstep (se 1 (by rfl) ⟨744551, by rfl⟩ : syracuseStep 992735 = 1489103) B1489103
theorem B992767 : Blo 992597 992767 := bstep (se 1 (by rfl) ⟨744575, by rfl⟩ : syracuseStep 992767 = 1489151) B1489151
theorem B993023 : Blo 992597 993023 := bstep (se 1 (by rfl) ⟨744767, by rfl⟩ : syracuseStep 993023 = 1489535) B1489535
theorem B993919 : Blo 992597 993919 := bstep (se 1 (by rfl) ⟨745439, by rfl⟩ : syracuseStep 993919 = 1490879) B1490879
theorem B12757661 : Blo 992597 12757661 := bstep (se 3 (by rfl) ⟨2392061, by rfl⟩ : syracuseStep 12757661 = 4784123) B4784123
theorem B12725423 : Blo 992597 12725423 := bstep (se 1 (by rfl) ⟨9544067, by rfl⟩ : syracuseStep 12725423 = 19088135) B19088135
theorem B8596705 : Blo 992597 8596705 := bstep (se 2 (by rfl) ⟨3223764, by rfl⟩ : syracuseStep 8596705 = 6447529) B6447529
theorem B3353885 : Blo 992597 3353885 := bstep (se 3 (by rfl) ⟨628853, by rfl⟩ : syracuseStep 3353885 = 1257707) B1257707
theorem B6368681 : Blo 992597 6368681 := bstep (se 2 (by rfl) ⟨2388255, by rfl⟩ : syracuseStep 6368681 = 4776511) B4776511
theorem B5025563 : Blo 992597 5025563 := bstep (se 1 (by rfl) ⟨3769172, by rfl⟩ : syracuseStep 5025563 = 7538345) B7538345
theorem B3190583 : Blo 992597 3190583 := bstep (se 1 (by rfl) ⟨2392937, by rfl⟩ : syracuseStep 3190583 = 4785875) B4785875
theorem B32255981 : Blo 992597 32255981 := bstep (se 3 (by rfl) ⟨6047996, by rfl⟩ : syracuseStep 32255981 = 12095993) B12095993
theorem B7549037 : Blo 992597 7549037 := bstep (se 3 (by rfl) ⟨1415444, by rfl⟩ : syracuseStep 7549037 = 2830889) B2830889
theorem B7647479 : Blo 992597 7647479 := bstep (se 1 (by rfl) ⟨5735609, by rfl⟩ : syracuseStep 7647479 = 11471219) B11471219
theorem B995743 : Blo 992597 995743 := bstep (se 1 (by rfl) ⟨746807, by rfl⟩ : syracuseStep 995743 = 1493615) B1493615
theorem B1258031 : Blo 992597 1258031 := bstep (se 1 (by rfl) ⟨943523, by rfl⟩ : syracuseStep 1258031 = 1887047) B1887047
theorem B4240799 : Blo 992597 4240799 := bstep (se 1 (by rfl) ⟨3180599, by rfl⟩ : syracuseStep 4240799 = 6361199) B6361199
theorem B6370937 : Blo 992597 6370937 := bstep (se 2 (by rfl) ⟨2389101, by rfl⟩ : syracuseStep 6370937 = 4778203) B4778203
theorem B2242223 : Blo 992597 2242223 := bstep (se 1 (by rfl) ⟨1681667, by rfl⟩ : syracuseStep 2242223 = 3363335) B3363335
theorem B1489307 : Blo 992597 1489307 := bstep (se 1 (by rfl) ⟨1116980, by rfl⟩ : syracuseStep 1489307 = 2233961) B2233961
theorem B1489391 : Blo 992597 1489391 := bstep (se 1 (by rfl) ⟨1117043, by rfl⟩ : syracuseStep 1489391 = 2234087) B2234087
theorem B9550561 : Blo 992597 9550561 := bstep (se 2 (by rfl) ⟨3581460, by rfl⟩ : syracuseStep 9550561 = 7162921) B7162921
theorem B3357503 : Blo 992597 3357503 := bstep (se 1 (by rfl) ⟨2518127, by rfl⟩ : syracuseStep 3357503 = 5036255) B5036255
theorem B64437221 : Blo 992597 64437221 := bstep (se 4 (by rfl) ⟨6040989, by rfl⟩ : syracuseStep 64437221 = 12081979) B12081979
theorem B1489913 : Blo 992597 1489913 := bstep (se 2 (by rfl) ⟨558717, by rfl⟩ : syracuseStep 1489913 = 1117435) B1117435
theorem B3357935 : Blo 992597 3357935 := bstep (se 1 (by rfl) ⟨2518451, by rfl⟩ : syracuseStep 3357935 = 5036903) B5036903
theorem B3358313 : Blo 992597 3358313 := bstep (se 2 (by rfl) ⟨1259367, by rfl⟩ : syracuseStep 3358313 = 2518735) B2518735
theorem B5029775 : Blo 992597 5029775 := bstep (se 1 (by rfl) ⟨3772331, by rfl⟩ : syracuseStep 5029775 = 7544663) B7544663
theorem B1490927 : Blo 992597 1490927 := bstep (se 1 (by rfl) ⟨1118195, by rfl⟩ : syracuseStep 1490927 = 2236391) B2236391
theorem B2834671 : Blo 992597 2834671 := bstep (se 1 (by rfl) ⟨2126003, by rfl⟩ : syracuseStep 2834671 = 4252007) B4252007
theorem B1491323 : Blo 992597 1491323 := bstep (se 1 (by rfl) ⟨1118492, by rfl⟩ : syracuseStep 1491323 = 2236985) B2236985
theorem B1491455 : Blo 992597 1491455 := bstep (se 1 (by rfl) ⟨1118591, by rfl⟩ : syracuseStep 1491455 = 2237183) B2237183
theorem B27607945 : Blo 992597 27607945 := bstep (se 2 (by rfl) ⟨10352979, by rfl⟩ : syracuseStep 27607945 = 20705959) B20705959
theorem B1491947 : Blo 992597 1491947 := bstep (se 1 (by rfl) ⟨1118960, by rfl⟩ : syracuseStep 1491947 = 2237921) B2237921
theorem B27215027 : Blo 992597 27215027 := bstep (se 1 (by rfl) ⟨20411270, by rfl⟩ : syracuseStep 27215027 = 40822541) B40822541
theorem B1492847 : Blo 992597 1492847 := bstep (se 1 (by rfl) ⟨1119635, by rfl⟩ : syracuseStep 1492847 = 2239271) B2239271
theorem B28690433 : Blo 992597 28690433 := bstep (se 2 (by rfl) ⟨10758912, by rfl⟩ : syracuseStep 28690433 = 21517825) B21517825
theorem B27609767 : Blo 992597 27609767 := bstep (se 1 (by rfl) ⟨20707325, by rfl⟩ : syracuseStep 27609767 = 41414651) B41414651
theorem B1493711 : Blo 992597 1493711 := bstep (se 1 (by rfl) ⟨1120283, by rfl⟩ : syracuseStep 1493711 = 2240567) B2240567
theorem B20433665 : Blo 992597 20433665 := bstep (se 2 (by rfl) ⟨7662624, by rfl⟩ : syracuseStep 20433665 = 15325249) B15325249
theorem B1494599 : Blo 992597 1494599 := bstep (se 1 (by rfl) ⟨1120949, by rfl⟩ : syracuseStep 1494599 = 2241899) B2241899
theorem B3362471 : Blo 992597 3362471 := bstep (se 1 (by rfl) ⟨2521853, by rfl⟩ : syracuseStep 3362471 = 5043707) B5043707
theorem B27219053 : Blo 992597 27219053 := bstep (se 3 (by rfl) ⟨5103572, by rfl⟩ : syracuseStep 27219053 = 10207145) B10207145
theorem B7165057 : Blo 992597 7165057 := bstep (se 2 (by rfl) ⟨2686896, by rfl⟩ : syracuseStep 7165057 = 5373793) B5373793
theorem B1594631 : Blo 992597 1594631 := bstep (se 1 (by rfl) ⟨1195973, by rfl⟩ : syracuseStep 1594631 = 2391947) B2391947
theorem B4251923 : Blo 992597 4251923 := bstep (se 1 (by rfl) ⟨3188942, by rfl⟩ : syracuseStep 4251923 = 6377885) B6377885
theorem B2515283 : Blo 992597 2515283 := bstep (se 1 (by rfl) ⟨1886462, by rfl⟩ : syracuseStep 2515283 = 3772925) B3772925
theorem B44229341 : Blo 992597 44229341 := bstep (se 3 (by rfl) ⟨8293001, by rfl⟩ : syracuseStep 44229341 = 16586003) B16586003
theorem B3402793 : Blo 992597 3402793 := bstep (se 2 (by rfl) ⟨1276047, by rfl⟩ : syracuseStep 3402793 = 2552095) B2552095
theorem B5042087 : Blo 992597 5042087 := bstep (se 1 (by rfl) ⟨3781565, by rfl⟩ : syracuseStep 5042087 = 7563131) B7563131
theorem B17232047 : Blo 992597 17232047 := bstep (se 1 (by rfl) ⟨12924035, by rfl⟩ : syracuseStep 17232047 = 25848071) B25848071
theorem B5109239 : Blo 992597 5109239 := bstep (se 1 (by rfl) ⟨3831929, by rfl⟩ : syracuseStep 5109239 = 7663859) B7663859
theorem B5044193 : Blo 992597 5044193 := bstep (se 2 (by rfl) ⟨1891572, by rfl⟩ : syracuseStep 5044193 = 3783145) B3783145
theorem B6060359 : Blo 992597 6060359 := bstep (se 1 (by rfl) ⟨4545269, by rfl⟩ : syracuseStep 6060359 = 9090539) B9090539
theorem B20446145 : Blo 992597 20446145 := bstep (se 2 (by rfl) ⟨7667304, by rfl⟩ : syracuseStep 20446145 = 15334609) B15334609
theorem B6814945 : Blo 992597 6814945 := bstep (se 2 (by rfl) ⟨2555604, by rfl⟩ : syracuseStep 6814945 = 5111209) B5111209
theorem B6815273 : Blo 992597 6815273 := bstep (se 2 (by rfl) ⟨2555727, by rfl⟩ : syracuseStep 6815273 = 5111455) B5111455
theorem B29523689 : Blo 992597 29523689 := bstep (se 2 (by rfl) ⟨11071383, by rfl⟩ : syracuseStep 29523689 = 22142767) B22142767
theorem B4030573 : Blo 992597 4030573 := bstep (se 3 (by rfl) ⟨755732, by rfl⟩ : syracuseStep 4030573 = 1511465) B1511465
theorem B1704503 : Blo 992597 1704503 := bstep (se 1 (by rfl) ⟨1278377, by rfl⟩ : syracuseStep 1704503 = 2556755) B2556755
theorem B1117543 : Blo 992597 1117543 := bstep (se 1 (by rfl) ⟨838157, by rfl⟩ : syracuseStep 1117543 = 1676315) B1676315
theorem B2233385 : Blo 992597 2233385 := bstep (se 2 (by rfl) ⟨837519, by rfl⟩ : syracuseStep 2233385 = 1675039) B1675039
theorem B10753343 : Blo 992597 10753343 := bstep (se 1 (by rfl) ⟨8065007, by rfl⟩ : syracuseStep 10753343 = 16130015) B16130015
theorem B1676855 : Blo 992597 1676855 := bstep (se 1 (by rfl) ⟨1257641, by rfl⟩ : syracuseStep 1676855 = 2515283) B2515283
theorem B2234537 : Blo 992597 2234537 := bstep (se 2 (by rfl) ⟨837951, by rfl⟩ : syracuseStep 2234537 = 1675903) B1675903
theorem B2235923 : Blo 992597 2235923 := bstep (se 1 (by rfl) ⟨1676942, by rfl⟩ : syracuseStep 2235923 = 3353885) B3353885
theorem B3350375 : Blo 992597 3350375 := bstep (se 1 (by rfl) ⟨2512781, by rfl⟩ : syracuseStep 3350375 = 5025563) B5025563
theorem B21503987 : Blo 992597 21503987 := bstep (se 1 (by rfl) ⟨16127990, by rfl⟩ : syracuseStep 21503987 = 32255981) B32255981
theorem B2236409 : Blo 992597 2236409 := bstep (se 2 (by rfl) ⟨838653, by rfl⟩ : syracuseStep 2236409 = 1677307) B1677307
theorem B2827199 : Blo 992597 2827199 := bstep (se 1 (by rfl) ⟨2120399, by rfl⟩ : syracuseStep 2827199 = 4240799) B4240799
theorem B4040239 : Blo 992597 4040239 := bstep (se 1 (by rfl) ⟨3030179, by rfl⟩ : syracuseStep 4040239 = 6060359) B6060359
theorem B992871 : Blo 992597 992871 := bstep (se 1 (by rfl) ⟨744653, by rfl⟩ : syracuseStep 992871 = 1489307) B1489307
theorem B9086593 : Blo 992597 9086593 := bstep (se 2 (by rfl) ⟨3407472, by rfl⟩ : syracuseStep 9086593 = 6814945) B6814945
theorem B992927 : Blo 992597 992927 := bstep (se 1 (by rfl) ⟨744695, by rfl⟩ : syracuseStep 992927 = 1489391) B1489391
theorem B2238335 : Blo 992597 2238335 := bstep (se 1 (by rfl) ⟨1678751, by rfl⟩ : syracuseStep 2238335 = 3357503) B3357503
theorem B993275 : Blo 992597 993275 := bstep (se 1 (by rfl) ⟨744956, by rfl⟩ : syracuseStep 993275 = 1489913) B1489913
theorem B2238623 : Blo 992597 2238623 := bstep (se 1 (by rfl) ⟨1678967, by rfl⟩ : syracuseStep 2238623 = 3357935) B3357935
theorem B2238875 : Blo 992597 2238875 := bstep (se 1 (by rfl) ⟨1679156, by rfl⟩ : syracuseStep 2238875 = 3358313) B3358313
theorem B3353183 : Blo 992597 3353183 := bstep (se 1 (by rfl) ⟨2514887, by rfl⟩ : syracuseStep 3353183 = 5029775) B5029775
theorem B993951 : Blo 992597 993951 := bstep (se 1 (by rfl) ⟨745463, by rfl⟩ : syracuseStep 993951 = 1490927) B1490927
theorem B994215 : Blo 992597 994215 := bstep (se 1 (by rfl) ⟨745661, by rfl⟩ : syracuseStep 994215 = 1491323) B1491323
theorem B3779561 : Blo 992597 3779561 := bstep (se 2 (by rfl) ⟨1417335, by rfl⟩ : syracuseStep 3779561 = 2834671) B2834671
theorem B9186301 : Blo 992597 9186301 := bstep (se 3 (by rfl) ⟨1722431, by rfl⟩ : syracuseStep 9186301 = 3444863) B3444863
theorem B994303 : Blo 992597 994303 := bstep (se 1 (by rfl) ⟨745727, by rfl⟩ : syracuseStep 994303 = 1491455) B1491455
theorem B2239649 : Blo 992597 2239649 := bstep (se 2 (by rfl) ⟨839868, by rfl⟩ : syracuseStep 2239649 = 1679737) B1679737
theorem B994631 : Blo 992597 994631 := bstep (se 1 (by rfl) ⟨745973, by rfl⟩ : syracuseStep 994631 = 1491947) B1491947
theorem B3190441 : Blo 992597 3190441 := bstep (se 2 (by rfl) ⟨1196415, by rfl⟩ : syracuseStep 3190441 = 2392831) B2392831
theorem B36810593 : Blo 992597 36810593 := bstep (se 2 (by rfl) ⟨13803972, by rfl⟩ : syracuseStep 36810593 = 27607945) B27607945
theorem B995231 : Blo 992597 995231 := bstep (se 1 (by rfl) ⟨746423, by rfl⟩ : syracuseStep 995231 = 1492847) B1492847
theorem B3354749 : Blo 992597 3354749 := bstep (se 3 (by rfl) ⟨629015, by rfl⟩ : syracuseStep 3354749 = 1258031) B1258031
theorem B995807 : Blo 992597 995807 := bstep (se 1 (by rfl) ⟨746855, by rfl⟩ : syracuseStep 995807 = 1493711) B1493711
theorem B53195381 : Blo 992597 53195381 := bstep (se 5 (by rfl) ⟨2493533, by rfl⟩ : syracuseStep 53195381 = 4987067) B4987067
theorem B996399 : Blo 992597 996399 := bstep (se 1 (by rfl) ⟨747299, by rfl⟩ : syracuseStep 996399 = 1494599) B1494599
theorem B2241647 : Blo 992597 2241647 := bstep (se 1 (by rfl) ⟨1681235, by rfl⟩ : syracuseStep 2241647 = 3362471) B3362471
theorem B3585151 : Blo 992597 3585151 := bstep (se 1 (by rfl) ⟨2688863, by rfl⟩ : syracuseStep 3585151 = 5377727) B5377727
theorem B3782159 : Blo 992597 3782159 := bstep (se 1 (by rfl) ⟨2836619, by rfl⟩ : syracuseStep 3782159 = 5673239) B5673239
theorem B6796831 : Blo 992597 6796831 := bstep (se 1 (by rfl) ⟨5097623, by rfl⟩ : syracuseStep 6796831 = 10195247) B10195247
theorem B1489007 : Blo 992597 1489007 := bstep (se 1 (by rfl) ⟨1116755, by rfl⟩ : syracuseStep 1489007 = 2233511) B2233511
theorem B1063087 : Blo 992597 1063087 := bstep (se 1 (by rfl) ⟨797315, by rfl⟩ : syracuseStep 1063087 = 1594631) B1594631
theorem B1489511 : Blo 992597 1489511 := bstep (se 1 (by rfl) ⟨1117133, by rfl⟩ : syracuseStep 1489511 = 2234267) B2234267
theorem B11319911 : Blo 992597 11319911 := bstep (se 1 (by rfl) ⟨8489933, by rfl⟩ : syracuseStep 11319911 = 16979867) B16979867
theorem B4537057 : Blo 992597 4537057 := bstep (se 2 (by rfl) ⟨1701396, by rfl⟩ : syracuseStep 4537057 = 3402793) B3402793
theorem B1489727 : Blo 992597 1489727 := bstep (se 1 (by rfl) ⟨1117295, by rfl⟩ : syracuseStep 1489727 = 2234591) B2234591
theorem B1489775 : Blo 992597 1489775 := bstep (se 1 (by rfl) ⟨1117331, by rfl⟩ : syracuseStep 1489775 = 2234663) B2234663
theorem B1490231 : Blo 992597 1490231 := bstep (se 1 (by rfl) ⟨1117673, by rfl⟩ : syracuseStep 1490231 = 2235347) B2235347
theorem B14335649 : Blo 992597 14335649 := bstep (se 2 (by rfl) ⟨5375868, by rfl⟩ : syracuseStep 14335649 = 10751737) B10751737
theorem B2834615 : Blo 992597 2834615 := bstep (se 1 (by rfl) ⟨2125961, by rfl⟩ : syracuseStep 2834615 = 4251923) B4251923
theorem B27247423 : Blo 992597 27247423 := bstep (se 1 (by rfl) ⟨20435567, by rfl⟩ : syracuseStep 27247423 = 40871135) B40871135
theorem B9553409 : Blo 992597 9553409 := bstep (se 2 (by rfl) ⟨3582528, by rfl⟩ : syracuseStep 9553409 = 7165057) B7165057
theorem B1492745 : Blo 992597 1492745 := bstep (se 2 (by rfl) ⟨559779, by rfl⟩ : syracuseStep 1492745 = 1119559) B1119559
theorem B8505107 : Blo 992597 8505107 := bstep (se 1 (by rfl) ⟨6378830, by rfl⟩ : syracuseStep 8505107 = 12757661) B12757661
theorem B4245787 : Blo 992597 4245787 := bstep (se 1 (by rfl) ⟨3184340, by rfl⟩ : syracuseStep 4245787 = 6368681) B6368681
theorem B3361391 : Blo 992597 3361391 := bstep (se 1 (by rfl) ⟨2521043, by rfl⟩ : syracuseStep 3361391 = 5042087) B5042087
theorem B5032691 : Blo 992597 5032691 := bstep (se 1 (by rfl) ⟨3774518, by rfl⟩ : syracuseStep 5032691 = 7549037) B7549037
theorem B11488031 : Blo 992597 11488031 := bstep (se 1 (by rfl) ⟨8616023, by rfl⟩ : syracuseStep 11488031 = 17232047) B17232047
theorem B5098319 : Blo 992597 5098319 := bstep (se 1 (by rfl) ⟨3823739, by rfl⟩ : syracuseStep 5098319 = 7647479) B7647479
theorem B12734081 : Blo 992597 12734081 := bstep (se 2 (by rfl) ⟨4775280, by rfl⟩ : syracuseStep 12734081 = 9550561) B9550561
theorem B4247291 : Blo 992597 4247291 := bstep (se 1 (by rfl) ⟨3185468, by rfl⟩ : syracuseStep 4247291 = 6370937) B6370937
theorem B1494815 : Blo 992597 1494815 := bstep (se 1 (by rfl) ⟨1121111, by rfl⟩ : syracuseStep 1494815 = 2242223) B2242223
theorem B3362795 : Blo 992597 3362795 := bstep (se 1 (by rfl) ⟨2522096, by rfl⟩ : syracuseStep 3362795 = 5044193) B5044193
theorem B18174061 : Blo 992597 18174061 := bstep (se 3 (by rfl) ⟨3407636, by rfl⟩ : syracuseStep 18174061 = 6815273) B6815273
theorem B19682459 : Blo 992597 19682459 := bstep (se 1 (by rfl) ⟨14761844, by rfl⟩ : syracuseStep 19682459 = 29523689) B29523689
theorem B7165979 : Blo 992597 7165979 := bstep (se 1 (by rfl) ⟨5374484, by rfl⟩ : syracuseStep 7165979 = 10748969) B10748969
theorem B18143351 : Blo 992597 18143351 := bstep (se 1 (by rfl) ⟨13607513, by rfl⟩ : syracuseStep 18143351 = 27215027) B27215027
theorem B19126955 : Blo 992597 19126955 := bstep (se 1 (by rfl) ⟨14345216, by rfl⟩ : syracuseStep 19126955 = 28690433) B28690433
theorem B18406511 : Blo 992597 18406511 := bstep (se 1 (by rfl) ⟨13804883, by rfl⟩ : syracuseStep 18406511 = 27609767) B27609767
theorem B18146035 : Blo 992597 18146035 := bstep (se 1 (by rfl) ⟨13609526, by rfl⟩ : syracuseStep 18146035 = 27219053) B27219053
theorem B10773755 : Blo 992597 10773755 := bstep (se 1 (by rfl) ⟨8080316, by rfl⟩ : syracuseStep 10773755 = 16160633) B16160633
theorem B11462273 : Blo 992597 11462273 := bstep (se 2 (by rfl) ⟨4298352, by rfl⟩ : syracuseStep 11462273 = 8596705) B8596705
theorem B14313847 : Blo 992597 14313847 := bstep (se 1 (by rfl) ⟨10735385, by rfl⟩ : syracuseStep 14313847 = 21470771) B21470771
theorem B2517419 : Blo 992597 2517419 := bstep (se 1 (by rfl) ⟨1888064, by rfl⟩ : syracuseStep 2517419 = 3776129) B3776129
theorem B29486227 : Blo 992597 29486227 := bstep (se 1 (by rfl) ⟨22114670, by rfl⟩ : syracuseStep 29486227 = 44229341) B44229341
theorem B54489773 : Blo 992597 54489773 := bstep (se 3 (by rfl) ⟨10216832, by rfl⟩ : syracuseStep 54489773 = 20433665) B20433665
theorem B8483615 : Blo 992597 8483615 := bstep (se 1 (by rfl) ⟨6362711, by rfl⟩ : syracuseStep 8483615 = 12725423) B12725423
theorem B2127055 : Blo 992597 2127055 := bstep (se 1 (by rfl) ⟨1595291, by rfl⟩ : syracuseStep 2127055 = 3190583) B3190583
theorem B3406159 : Blo 992597 3406159 := bstep (se 1 (by rfl) ⟨2554619, by rfl⟩ : syracuseStep 3406159 = 5109239) B5109239
theorem B13630763 : Blo 992597 13630763 := bstep (se 1 (by rfl) ⟨10223072, by rfl⟩ : syracuseStep 13630763 = 20446145) B20446145
theorem B42958147 : Blo 992597 42958147 := bstep (se 1 (by rfl) ⟨32218610, by rfl⟩ : syracuseStep 42958147 = 64437221) B64437221
theorem B5374097 : Blo 992597 5374097 := bstep (se 2 (by rfl) ⟨2015286, by rfl⟩ : syracuseStep 5374097 = 4030573) B4030573
theorem B5669797 : Blo 992597 5669797 := bstep (se 4 (by rfl) ⟨531543, by rfl⟩ : syracuseStep 5669797 = 1063087) B1063087
theorem B5670071 : Blo 992597 5670071 := bstep (se 1 (by rfl) ⟨4252553, by rfl⟩ : syracuseStep 5670071 = 8505107) B8505107
theorem B8489387 : Blo 992597 8489387 := bstep (se 1 (by rfl) ⟨6367040, by rfl⟩ : syracuseStep 8489387 = 12734081) B12734081
theorem B1117903 : Blo 992597 1117903 := bstep (se 1 (by rfl) ⟨838427, by rfl⟩ : syracuseStep 1117903 = 1676855) B1676855
theorem B12095567 : Blo 992597 12095567 := bstep (se 1 (by rfl) ⟨9071675, by rfl⟩ : syracuseStep 12095567 = 18143351) B18143351
theorem B12751303 : Blo 992597 12751303 := bstep (se 1 (by rfl) ⟨9563477, by rfl⟩ : syracuseStep 12751303 = 19126955) B19126955
theorem B2233583 : Blo 992597 2233583 := bstep (se 1 (by rfl) ⟨1675187, by rfl⟩ : syracuseStep 2233583 = 3350375) B3350375
theorem B7182503 : Blo 992597 7182503 := bstep (se 1 (by rfl) ⟨5386877, by rfl⟩ : syracuseStep 7182503 = 10773755) B10773755
theorem B7641515 : Blo 992597 7641515 := bstep (se 1 (by rfl) ⟨5731136, by rfl⟩ : syracuseStep 7641515 = 11462273) B11462273
theorem B1678279 : Blo 992597 1678279 := bstep (se 1 (by rfl) ⟨1258709, by rfl⟩ : syracuseStep 1678279 = 2517419) B2517419
theorem B2235455 : Blo 992597 2235455 := bstep (se 1 (by rfl) ⟨1676591, by rfl⟩ : syracuseStep 2235455 = 3353183) B3353183
theorem B2236499 : Blo 992597 2236499 := bstep (se 1 (by rfl) ⟨1677374, by rfl⟩ : syracuseStep 2236499 = 3354749) B3354749
theorem B35463587 : Blo 992597 35463587 := bstep (se 1 (by rfl) ⟨26597690, by rfl⟩ : syracuseStep 35463587 = 53195381) B53195381
theorem B992671 : Blo 992597 992671 := bstep (se 1 (by rfl) ⟨744503, by rfl⟩ : syracuseStep 992671 = 1489007) B1489007
theorem B993007 : Blo 992597 993007 := bstep (se 1 (by rfl) ⟨744755, by rfl⟩ : syracuseStep 993007 = 1489511) B1489511
theorem B7546607 : Blo 992597 7546607 := bstep (se 1 (by rfl) ⟨5659955, by rfl⟩ : syracuseStep 7546607 = 11319911) B11319911
theorem B993151 : Blo 992597 993151 := bstep (se 1 (by rfl) ⟨744863, by rfl⟩ : syracuseStep 993151 = 1489727) B1489727
theorem B993183 : Blo 992597 993183 := bstep (se 1 (by rfl) ⟨744887, by rfl⟩ : syracuseStep 993183 = 1489775) B1489775
theorem B9087175 : Blo 992597 9087175 := bstep (se 1 (by rfl) ⟨6815381, by rfl⟩ : syracuseStep 9087175 = 13630763) B13630763
theorem B993487 : Blo 992597 993487 := bstep (se 1 (by rfl) ⟨745115, by rfl⟩ : syracuseStep 993487 = 1490231) B1490231
theorem B24194713 : Blo 992597 24194713 := bstep (se 2 (by rfl) ⟨9073017, by rfl⟩ : syracuseStep 24194713 = 18146035) B18146035
theorem B6368939 : Blo 992597 6368939 := bstep (se 1 (by rfl) ⟨4776704, by rfl⟩ : syracuseStep 6368939 = 9553409) B9553409
theorem B995163 : Blo 992597 995163 := bstep (se 1 (by rfl) ⟨746372, by rfl⟩ : syracuseStep 995163 = 1492745) B1492745
theorem B2240927 : Blo 992597 2240927 := bstep (se 1 (by rfl) ⟨1680695, by rfl⟩ : syracuseStep 2240927 = 3361391) B3361391
theorem B3355127 : Blo 992597 3355127 := bstep (se 1 (by rfl) ⟨2516345, by rfl⟩ : syracuseStep 3355127 = 5032691) B5032691
theorem B5386985 : Blo 992597 5386985 := bstep (se 2 (by rfl) ⟨2020119, by rfl⟩ : syracuseStep 5386985 = 4040239) B4040239
theorem B2831527 : Blo 992597 2831527 := bstep (se 1 (by rfl) ⟨2123645, by rfl⟩ : syracuseStep 2831527 = 4247291) B4247291
theorem B996543 : Blo 992597 996543 := bstep (se 1 (by rfl) ⟨747407, by rfl⟩ : syracuseStep 996543 = 1494815) B1494815
theorem B2241863 : Blo 992597 2241863 := bstep (se 1 (by rfl) ⟨1681397, by rfl⟩ : syracuseStep 2241863 = 3362795) B3362795
theorem B19085129 : Blo 992597 19085129 := bstep (se 2 (by rfl) ⟨7156923, by rfl⟩ : syracuseStep 19085129 = 14313847) B14313847
theorem B1488923 : Blo 992597 1488923 := bstep (se 1 (by rfl) ⟨1116692, by rfl⟩ : syracuseStep 1488923 = 2233385) B2233385
theorem B13121639 : Blo 992597 13121639 := bstep (se 1 (by rfl) ⟨9841229, by rfl⟩ : syracuseStep 13121639 = 19682459) B19682459
theorem B1489691 : Blo 992597 1489691 := bstep (se 1 (by rfl) ⟨1117268, by rfl⟩ : syracuseStep 1489691 = 2234537) B2234537
theorem B1490057 : Blo 992597 1490057 := bstep (se 2 (by rfl) ⟨558771, by rfl⟩ : syracuseStep 1490057 = 1117543) B1117543
theorem B12271007 : Blo 992597 12271007 := bstep (se 1 (by rfl) ⟨9203255, by rfl⟩ : syracuseStep 12271007 = 18406511) B18406511
theorem B1490615 : Blo 992597 1490615 := bstep (se 1 (by rfl) ⟨1117961, by rfl⟩ : syracuseStep 1490615 = 2235923) B2235923
theorem B14335991 : Blo 992597 14335991 := bstep (se 1 (by rfl) ⟨10751993, by rfl⟩ : syracuseStep 14335991 = 21503987) B21503987
theorem B1490939 : Blo 992597 1490939 := bstep (se 1 (by rfl) ⟨1118204, by rfl⟩ : syracuseStep 1490939 = 2236409) B2236409
theorem B24232081 : Blo 992597 24232081 := bstep (se 2 (by rfl) ⟨9087030, by rfl⟩ : syracuseStep 24232081 = 18174061) B18174061
theorem B1884799 : Blo 992597 1884799 := bstep (se 1 (by rfl) ⟨1413599, by rfl⟩ : syracuseStep 1884799 = 2827199) B2827199
theorem B19120805 : Blo 992597 19120805 := bstep (se 4 (by rfl) ⟨1792575, by rfl⟩ : syracuseStep 19120805 = 3585151) B3585151
theorem B1492223 : Blo 992597 1492223 := bstep (se 1 (by rfl) ⟨1119167, by rfl⟩ : syracuseStep 1492223 = 2238335) B2238335
theorem B1492415 : Blo 992597 1492415 := bstep (se 1 (by rfl) ⟨1119311, by rfl⟩ : syracuseStep 1492415 = 2238623) B2238623
theorem B1492583 : Blo 992597 1492583 := bstep (se 1 (by rfl) ⟨1119437, by rfl⟩ : syracuseStep 1492583 = 2238875) B2238875
theorem B2836073 : Blo 992597 2836073 := bstep (se 2 (by rfl) ⟨1063527, by rfl⟩ : syracuseStep 2836073 = 2127055) B2127055
theorem B9062441 : Blo 992597 9062441 := bstep (se 2 (by rfl) ⟨3398415, by rfl⟩ : syracuseStep 9062441 = 6796831) B6796831
theorem B1493099 : Blo 992597 1493099 := bstep (se 1 (by rfl) ⟨1119824, by rfl⟩ : syracuseStep 1493099 = 2239649) B2239649
theorem B4541545 : Blo 992597 4541545 := bstep (se 2 (by rfl) ⟨1703079, by rfl⟩ : syracuseStep 4541545 = 3406159) B3406159
theorem B36326515 : Blo 992597 36326515 := bstep (se 1 (by rfl) ⟨27244886, by rfl⟩ : syracuseStep 36326515 = 54489773) B54489773
theorem B5655743 : Blo 992597 5655743 := bstep (se 1 (by rfl) ⟨4241807, by rfl⟩ : syracuseStep 5655743 = 8483615) B8483615
theorem B1494431 : Blo 992597 1494431 := bstep (se 1 (by rfl) ⟨1120823, by rfl⟩ : syracuseStep 1494431 = 2241647) B2241647
theorem B6049409 : Blo 992597 6049409 := bstep (se 2 (by rfl) ⟨2268528, by rfl⟩ : syracuseStep 6049409 = 4537057) B4537057
theorem B9557099 : Blo 992597 9557099 := bstep (se 1 (by rfl) ⟨7167824, by rfl⟩ : syracuseStep 9557099 = 14335649) B14335649
theorem B1889743 : Blo 992597 1889743 := bstep (se 1 (by rfl) ⟨1417307, by rfl⟩ : syracuseStep 1889743 = 2834615) B2834615
theorem B36329897 : Blo 992597 36329897 := bstep (se 2 (by rfl) ⟨13623711, by rfl⟩ : syracuseStep 36329897 = 27247423) B27247423
theorem B4545341 : Blo 992597 4545341 := bstep (se 3 (by rfl) ⟨852251, by rfl⟩ : syracuseStep 4545341 = 1704503) B1704503
theorem B7658687 : Blo 992597 7658687 := bstep (se 1 (by rfl) ⟨5744015, by rfl⟩ : syracuseStep 7658687 = 11488031) B11488031
theorem B3398879 : Blo 992597 3398879 := bstep (se 1 (by rfl) ⟨2549159, by rfl⟩ : syracuseStep 3398879 = 5098319) B5098319
theorem B12115457 : Blo 992597 12115457 := bstep (se 2 (by rfl) ⟨4543296, by rfl⟩ : syracuseStep 12115457 = 9086593) B9086593
theorem B5661049 : Blo 992597 5661049 := bstep (se 2 (by rfl) ⟨2122893, by rfl⟩ : syracuseStep 5661049 = 4245787) B4245787
theorem B7168895 : Blo 992597 7168895 := bstep (se 1 (by rfl) ⟨5376671, by rfl⟩ : syracuseStep 7168895 = 10753343) B10753343
theorem B12248401 : Blo 992597 12248401 := bstep (se 2 (by rfl) ⟨4593150, by rfl⟩ : syracuseStep 12248401 = 9186301) B9186301
theorem B4777319 : Blo 992597 4777319 := bstep (se 1 (by rfl) ⟨3582989, by rfl⟩ : syracuseStep 4777319 = 7165979) B7165979
theorem B39314969 : Blo 992597 39314969 := bstep (se 2 (by rfl) ⟨14743113, by rfl⟩ : syracuseStep 39314969 = 29486227) B29486227
theorem B4253921 : Blo 992597 4253921 := bstep (se 2 (by rfl) ⟨1595220, by rfl⟩ : syracuseStep 4253921 = 3190441) B3190441
theorem B2519707 : Blo 992597 2519707 := bstep (se 1 (by rfl) ⟨1889780, by rfl⟩ : syracuseStep 2519707 = 3779561) B3779561
theorem B24540395 : Blo 992597 24540395 := bstep (se 1 (by rfl) ⟨18405296, by rfl⟩ : syracuseStep 24540395 = 36810593) B36810593
theorem B2521439 : Blo 992597 2521439 := bstep (se 1 (by rfl) ⟨1891079, by rfl⟩ : syracuseStep 2521439 = 3782159) B3782159
theorem B57277529 : Blo 992597 57277529 := bstep (se 2 (by rfl) ⟨21479073, by rfl⟩ : syracuseStep 57277529 = 42958147) B42958147
theorem B32309441 : Blo 992597 32309441 := bstep (se 2 (by rfl) ⟨12116040, by rfl⟩ : syracuseStep 32309441 = 24232081) B24232081
theorem B12747203 : Blo 992597 12747203 := bstep (se 1 (by rfl) ⟨9560402, by rfl⟩ : syracuseStep 12747203 = 19120805) B19120805
theorem B3770495 : Blo 992597 3770495 := bstep (se 1 (by rfl) ⟨2827871, by rfl⟩ : syracuseStep 3770495 = 5655743) B5655743
theorem B8063711 : Blo 992597 8063711 := bstep (se 1 (by rfl) ⟨6047783, by rfl⟩ : syracuseStep 8063711 = 12095567) B12095567
theorem B65441053 : Blo 992597 65441053 := bstep (se 3 (by rfl) ⟨12270197, by rfl⟩ : syracuseStep 65441053 = 24540395) B24540395
theorem B4788335 : Blo 992597 4788335 := bstep (se 1 (by rfl) ⟨3591251, by rfl⟩ : syracuseStep 4788335 = 7182503) B7182503
theorem B48435353 : Blo 992597 48435353 := bstep (se 2 (by rfl) ⟨18163257, by rfl⟩ : syracuseStep 48435353 = 36326515) B36326515
theorem B24219931 : Blo 992597 24219931 := bstep (se 1 (by rfl) ⟨18164948, by rfl⟩ : syracuseStep 24219931 = 36329897) B36329897
theorem B378278261 : Blo 992597 378278261 := bstep (se 5 (by rfl) ⟨17731793, by rfl⟩ : syracuseStep 378278261 = 35463587) B35463587
theorem B3775369 : Blo 992597 3775369 := bstep (se 2 (by rfl) ⟨1415763, by rfl⟩ : syracuseStep 3775369 = 2831527) B2831527
theorem B2236751 : Blo 992597 2236751 := bstep (se 1 (by rfl) ⟨1677563, by rfl⟩ : syracuseStep 2236751 = 3355127) B3355127
theorem B12723419 : Blo 992597 12723419 := bstep (se 1 (by rfl) ⟨9542564, by rfl⟩ : syracuseStep 12723419 = 19085129) B19085129
theorem B2237705 : Blo 992597 2237705 := bstep (se 2 (by rfl) ⟨839139, by rfl⟩ : syracuseStep 2237705 = 1678279) B1678279
theorem B992615 : Blo 992597 992615 := bstep (se 1 (by rfl) ⟨744461, by rfl⟩ : syracuseStep 992615 = 1488923) B1488923
theorem B1680959 : Blo 992597 1680959 := bstep (se 1 (by rfl) ⟨1260719, by rfl⟩ : syracuseStep 1680959 = 2521439) B2521439
theorem B16131757 : Blo 992597 16131757 := bstep (se 3 (by rfl) ⟨3024704, by rfl⟩ : syracuseStep 16131757 = 6049409) B6049409
theorem B993127 : Blo 992597 993127 := bstep (se 1 (by rfl) ⟨744845, by rfl⟩ : syracuseStep 993127 = 1489691) B1489691
theorem B38185019 : Blo 992597 38185019 := bstep (se 1 (by rfl) ⟨28638764, by rfl⟩ : syracuseStep 38185019 = 57277529) B57277529
theorem B993371 : Blo 992597 993371 := bstep (se 1 (by rfl) ⟨745028, by rfl⟩ : syracuseStep 993371 = 1490057) B1490057
theorem B993743 : Blo 992597 993743 := bstep (se 1 (by rfl) ⟨745307, by rfl⟩ : syracuseStep 993743 = 1490615) B1490615
theorem B993959 : Blo 992597 993959 := bstep (se 1 (by rfl) ⟨745469, by rfl⟩ : syracuseStep 993959 = 1490939) B1490939
theorem B3582731 : Blo 992597 3582731 := bstep (se 1 (by rfl) ⟨2687048, by rfl⟩ : syracuseStep 3582731 = 5374097) B5374097
theorem B7548065 : Blo 992597 7548065 := bstep (se 2 (by rfl) ⟨2830524, by rfl⟩ : syracuseStep 7548065 = 5661049) B5661049
theorem B3780047 : Blo 992597 3780047 := bstep (se 1 (by rfl) ⟨2835035, by rfl⟩ : syracuseStep 3780047 = 5670071) B5670071
theorem B994815 : Blo 992597 994815 := bstep (se 1 (by rfl) ⟨746111, by rfl⟩ : syracuseStep 994815 = 1492223) B1492223
theorem B994943 : Blo 992597 994943 := bstep (se 1 (by rfl) ⟨746207, by rfl⟩ : syracuseStep 994943 = 1492415) B1492415
theorem B995055 : Blo 992597 995055 := bstep (se 1 (by rfl) ⟨746291, by rfl⟩ : syracuseStep 995055 = 1492583) B1492583
theorem B6041627 : Blo 992597 6041627 := bstep (se 1 (by rfl) ⟨4531220, by rfl⟩ : syracuseStep 6041627 = 9062441) B9062441
theorem B995399 : Blo 992597 995399 := bstep (se 1 (by rfl) ⟨746549, by rfl⟩ : syracuseStep 995399 = 1493099) B1493099
theorem B16331201 : Blo 992597 16331201 := bstep (se 2 (by rfl) ⟨6124200, by rfl⟩ : syracuseStep 16331201 = 12248401) B12248401
theorem B996287 : Blo 992597 996287 := bstep (se 1 (by rfl) ⟨747215, by rfl⟩ : syracuseStep 996287 = 1494431) B1494431
theorem B6371399 : Blo 992597 6371399 := bstep (se 1 (by rfl) ⟨4778549, by rfl⟩ : syracuseStep 6371399 = 9557099) B9557099
theorem B1489055 : Blo 992597 1489055 := bstep (se 1 (by rfl) ⟨1116791, by rfl⟩ : syracuseStep 1489055 = 2233583) B2233583
theorem B5094343 : Blo 992597 5094343 := bstep (se 1 (by rfl) ⟨3820757, by rfl⟩ : syracuseStep 5094343 = 7641515) B7641515
theorem B3030227 : Blo 992597 3030227 := bstep (se 1 (by rfl) ⟨2272670, by rfl⟩ : syracuseStep 3030227 = 4545341) B4545341
theorem B1490303 : Blo 992597 1490303 := bstep (se 1 (by rfl) ⟨1117727, by rfl⟩ : syracuseStep 1490303 = 2235455) B2235455
theorem B32259617 : Blo 992597 32259617 := bstep (se 2 (by rfl) ⟨12097356, by rfl⟩ : syracuseStep 32259617 = 24194713) B24194713
theorem B1490537 : Blo 992597 1490537 := bstep (se 2 (by rfl) ⟨558951, by rfl⟩ : syracuseStep 1490537 = 1117903) B1117903
theorem B8076971 : Blo 992597 8076971 := bstep (se 1 (by rfl) ⟨6057728, by rfl⟩ : syracuseStep 8076971 = 12115457) B12115457
theorem B1490999 : Blo 992597 1490999 := bstep (se 1 (by rfl) ⟨1118249, by rfl⟩ : syracuseStep 1490999 = 2236499) B2236499
theorem B3359609 : Blo 992597 3359609 := bstep (se 2 (by rfl) ⟨1259853, by rfl⟩ : syracuseStep 3359609 = 2519707) B2519707
theorem B5031071 : Blo 992597 5031071 := bstep (se 1 (by rfl) ⟨3773303, by rfl⟩ : syracuseStep 5031071 = 7546607) B7546607
theorem B2835947 : Blo 992597 2835947 := bstep (se 1 (by rfl) ⟨2126960, by rfl⟩ : syracuseStep 2835947 = 4253921) B4253921
theorem B4245959 : Blo 992597 4245959 := bstep (se 1 (by rfl) ⟨3184469, by rfl⟩ : syracuseStep 4245959 = 6368939) B6368939
theorem B1493951 : Blo 992597 1493951 := bstep (se 1 (by rfl) ⟨1120463, by rfl⟩ : syracuseStep 1493951 = 2240927) B2240927
theorem B3591323 : Blo 992597 3591323 := bstep (se 1 (by rfl) ⟨2693492, by rfl⟩ : syracuseStep 3591323 = 5386985) B5386985
theorem B9063677 : Blo 992597 9063677 := bstep (se 3 (by rfl) ⟨1699439, by rfl⟩ : syracuseStep 9063677 = 3398879) B3398879
theorem B1494575 : Blo 992597 1494575 := bstep (se 1 (by rfl) ⟨1120931, by rfl⟩ : syracuseStep 1494575 = 2241863) B2241863
theorem B8180671 : Blo 992597 8180671 := bstep (se 1 (by rfl) ⟨6135503, by rfl⟩ : syracuseStep 8180671 = 12271007) B12271007
theorem B9557327 : Blo 992597 9557327 := bstep (se 1 (by rfl) ⟨7167995, by rfl⟩ : syracuseStep 9557327 = 14335991) B14335991
theorem B2513065 : Blo 992597 2513065 := bstep (se 2 (by rfl) ⟨942399, by rfl⟩ : syracuseStep 2513065 = 1884799) B1884799
theorem B1890715 : Blo 992597 1890715 := bstep (se 1 (by rfl) ⟨1418036, by rfl⟩ : syracuseStep 1890715 = 2836073) B2836073
theorem B7559729 : Blo 992597 7559729 := bstep (se 2 (by rfl) ⟨2834898, by rfl⟩ : syracuseStep 7559729 = 5669797) B5669797
theorem B5659591 : Blo 992597 5659591 := bstep (se 1 (by rfl) ⟨4244693, by rfl⟩ : syracuseStep 5659591 = 8489387) B8489387
theorem B12116233 : Blo 992597 12116233 := bstep (se 2 (by rfl) ⟨4543587, by rfl⟩ : syracuseStep 12116233 = 9087175) B9087175
theorem B12739517 : Blo 992597 12739517 := bstep (se 3 (by rfl) ⟨2388659, by rfl⟩ : syracuseStep 12739517 = 4777319) B4777319
theorem B6055393 : Blo 992597 6055393 := bstep (se 2 (by rfl) ⟨2270772, by rfl⟩ : syracuseStep 6055393 = 4541545) B4541545
theorem B5105791 : Blo 992597 5105791 := bstep (se 1 (by rfl) ⟨3829343, by rfl⟩ : syracuseStep 5105791 = 7658687) B7658687
theorem B4779263 : Blo 992597 4779263 := bstep (se 1 (by rfl) ⟨3584447, by rfl⟩ : syracuseStep 4779263 = 7168895) B7168895
theorem B17001737 : Blo 992597 17001737 := bstep (se 2 (by rfl) ⟨6375651, by rfl⟩ : syracuseStep 17001737 = 12751303) B12751303
theorem B26209979 : Blo 992597 26209979 := bstep (se 1 (by rfl) ⟨19657484, by rfl⟩ : syracuseStep 26209979 = 39314969) B39314969
theorem B2519657 : Blo 992597 2519657 := bstep (se 2 (by rfl) ⟨944871, by rfl⟩ : syracuseStep 2519657 = 1889743) B1889743
theorem B8747759 : Blo 992597 8747759 := bstep (se 1 (by rfl) ⟨6560819, by rfl⟩ : syracuseStep 8747759 = 13121639) B13121639
theorem B16154977 : Blo 992597 16154977 := bstep (se 2 (by rfl) ⟨6058116, by rfl⟩ : syracuseStep 16154977 = 12116233) B12116233
theorem B5375807 : Blo 992597 5375807 := bstep (se 1 (by rfl) ⟨4031855, by rfl⟩ : syracuseStep 5375807 = 8063711) B8063711
theorem B2394215 : Blo 992597 2394215 := bstep (se 1 (by rfl) ⟨1795661, by rfl⟩ : syracuseStep 2394215 = 3591323) B3591323
theorem B252185507 : Blo 992597 252185507 := bstep (se 1 (by rfl) ⟨189139130, by rfl⟩ : syracuseStep 252185507 = 378278261) B378278261
theorem B8493011 : Blo 992597 8493011 := bstep (se 1 (by rfl) ⟨6369758, by rfl⟩ : syracuseStep 8493011 = 12739517) B12739517
theorem B1120639 : Blo 992597 1120639 := bstep (se 1 (by rfl) ⟨840479, by rfl⟩ : syracuseStep 1120639 = 1680959) B1680959
theorem B349018949 : Blo 992597 349018949 := bstep (se 4 (by rfl) ⟨32720526, by rfl⟩ : syracuseStep 349018949 = 65441053) B65441053
theorem B3186175 : Blo 992597 3186175 := bstep (se 1 (by rfl) ⟨2389631, by rfl⟩ : syracuseStep 3186175 = 4779263) B4779263
theorem B17473319 : Blo 992597 17473319 := bstep (se 1 (by rfl) ⟨13104989, by rfl⟩ : syracuseStep 17473319 = 26209979) B26209979
theorem B3350753 : Blo 992597 3350753 := bstep (se 2 (by rfl) ⟨1256532, by rfl⟩ : syracuseStep 3350753 = 2513065) B2513065
theorem B10887467 : Blo 992597 10887467 := bstep (se 1 (by rfl) ⟨8165600, by rfl⟩ : syracuseStep 10887467 = 16331201) B16331201
theorem B1679771 : Blo 992597 1679771 := bstep (se 1 (by rfl) ⟨1259828, by rfl⟩ : syracuseStep 1679771 = 2519657) B2519657
theorem B6792457 : Blo 992597 6792457 := bstep (se 2 (by rfl) ⟨2547171, by rfl⟩ : syracuseStep 6792457 = 5094343) B5094343
theorem B7546121 : Blo 992597 7546121 := bstep (se 2 (by rfl) ⟨2829795, by rfl⟩ : syracuseStep 7546121 = 5659591) B5659591
theorem B992703 : Blo 992597 992703 := bstep (se 1 (by rfl) ⟨744527, by rfl⟩ : syracuseStep 992703 = 1489055) B1489055
theorem B993535 : Blo 992597 993535 := bstep (se 1 (by rfl) ⟨745151, by rfl⟩ : syracuseStep 993535 = 1490303) B1490303
theorem B21506411 : Blo 992597 21506411 := bstep (se 1 (by rfl) ⟨16129808, by rfl⟩ : syracuseStep 21506411 = 32259617) B32259617
theorem B993691 : Blo 992597 993691 := bstep (se 1 (by rfl) ⟨745268, by rfl⟩ : syracuseStep 993691 = 1490537) B1490537
theorem B5384647 : Blo 992597 5384647 := bstep (se 1 (by rfl) ⟨4038485, by rfl⟩ : syracuseStep 5384647 = 8076971) B8076971
theorem B993999 : Blo 992597 993999 := bstep (se 1 (by rfl) ⟨745499, by rfl⟩ : syracuseStep 993999 = 1490999) B1490999
theorem B21539627 : Blo 992597 21539627 := bstep (se 1 (by rfl) ⟨16154720, by rfl⟩ : syracuseStep 21539627 = 32309441) B32309441
theorem B8498135 : Blo 992597 8498135 := bstep (se 1 (by rfl) ⟨6373601, by rfl⟩ : syracuseStep 8498135 = 12747203) B12747203
theorem B2239739 : Blo 992597 2239739 := bstep (se 1 (by rfl) ⟨1679804, by rfl⟩ : syracuseStep 2239739 = 3359609) B3359609
theorem B3354047 : Blo 992597 3354047 := bstep (se 1 (by rfl) ⟨2515535, by rfl⟩ : syracuseStep 3354047 = 5031071) B5031071
theorem B2830639 : Blo 992597 2830639 := bstep (se 1 (by rfl) ⟨2122979, by rfl⟩ : syracuseStep 2830639 = 4245959) B4245959
theorem B995967 : Blo 992597 995967 := bstep (se 1 (by rfl) ⟨746975, by rfl⟩ : syracuseStep 995967 = 1493951) B1493951
theorem B8073857 : Blo 992597 8073857 := bstep (se 2 (by rfl) ⟨3027696, by rfl⟩ : syracuseStep 8073857 = 6055393) B6055393
theorem B6042451 : Blo 992597 6042451 := bstep (se 1 (by rfl) ⟨4531838, by rfl⟩ : syracuseStep 6042451 = 9063677) B9063677
theorem B21509009 : Blo 992597 21509009 := bstep (se 2 (by rfl) ⟨8065878, by rfl⟩ : syracuseStep 21509009 = 16131757) B16131757
theorem B996383 : Blo 992597 996383 := bstep (se 1 (by rfl) ⟨747287, by rfl⟩ : syracuseStep 996383 = 1494575) B1494575
theorem B3192223 : Blo 992597 3192223 := bstep (se 1 (by rfl) ⟨2394167, by rfl⟩ : syracuseStep 3192223 = 4788335) B4788335
theorem B32290235 : Blo 992597 32290235 := bstep (se 1 (by rfl) ⟨24217676, by rfl⟩ : syracuseStep 32290235 = 48435353) B48435353
theorem B6371551 : Blo 992597 6371551 := bstep (se 1 (by rfl) ⟨4778663, by rfl⟩ : syracuseStep 6371551 = 9557327) B9557327
theorem B1491167 : Blo 992597 1491167 := bstep (se 1 (by rfl) ⟨1118375, by rfl⟩ : syracuseStep 1491167 = 2236751) B2236751
theorem B32293241 : Blo 992597 32293241 := bstep (se 2 (by rfl) ⟨12109965, by rfl⟩ : syracuseStep 32293241 = 24219931) B24219931
theorem B1491803 : Blo 992597 1491803 := bstep (se 1 (by rfl) ⟨1118852, by rfl⟩ : syracuseStep 1491803 = 2237705) B2237705
theorem B5032043 : Blo 992597 5032043 := bstep (se 1 (by rfl) ⟨3774032, by rfl⟩ : syracuseStep 5032043 = 7548065) B7548065
theorem B5033825 : Blo 992597 5033825 := bstep (se 2 (by rfl) ⟨1887684, by rfl⟩ : syracuseStep 5033825 = 3775369) B3775369
theorem B4247599 : Blo 992597 4247599 := bstep (se 1 (by rfl) ⟨3185699, by rfl⟩ : syracuseStep 4247599 = 6371399) B6371399
theorem B2020151 : Blo 992597 2020151 := bstep (se 1 (by rfl) ⟨1515113, by rfl⟩ : syracuseStep 2020151 = 3030227) B3030227
theorem B1890631 : Blo 992597 1890631 := bstep (se 1 (by rfl) ⟨1417973, by rfl⟩ : syracuseStep 1890631 = 2835947) B2835947
theorem B2513663 : Blo 992597 2513663 := bstep (se 1 (by rfl) ⟨1885247, by rfl⟩ : syracuseStep 2513663 = 3770495) B3770495
theorem B6807721 : Blo 992597 6807721 := bstep (se 2 (by rfl) ⟨2552895, by rfl⟩ : syracuseStep 6807721 = 5105791) B5105791
theorem B5039819 : Blo 992597 5039819 := bstep (se 1 (by rfl) ⟨3779864, by rfl⟩ : syracuseStep 5039819 = 7559729) B7559729
theorem B8482279 : Blo 992597 8482279 := bstep (se 1 (by rfl) ⟨6361709, by rfl⟩ : syracuseStep 8482279 = 12723419) B12723419
theorem B10907561 : Blo 992597 10907561 := bstep (se 2 (by rfl) ⟨4090335, by rfl⟩ : syracuseStep 10907561 = 8180671) B8180671
theorem B25456679 : Blo 992597 25456679 := bstep (se 1 (by rfl) ⟨19092509, by rfl⟩ : syracuseStep 25456679 = 38185019) B38185019
theorem B2388487 : Blo 992597 2388487 := bstep (se 1 (by rfl) ⟨1791365, by rfl⟩ : syracuseStep 2388487 = 3582731) B3582731
theorem B11334491 : Blo 992597 11334491 := bstep (se 1 (by rfl) ⟨8500868, by rfl⟩ : syracuseStep 11334491 = 17001737) B17001737
theorem B2520031 : Blo 992597 2520031 := bstep (se 1 (by rfl) ⟨1890023, by rfl⟩ : syracuseStep 2520031 = 3780047) B3780047
theorem B4027751 : Blo 992597 4027751 := bstep (se 1 (by rfl) ⟨3020813, by rfl⟩ : syracuseStep 4027751 = 6041627) B6041627
theorem B2520953 : Blo 992597 2520953 := bstep (se 2 (by rfl) ⟨945357, by rfl⟩ : syracuseStep 2520953 = 1890715) B1890715
theorem B5831839 : Blo 992597 5831839 := bstep (se 1 (by rfl) ⟨4373879, by rfl⟩ : syracuseStep 5831839 = 8747759) B8747759
theorem B9076961 : Blo 992597 9076961 := bstep (se 2 (by rfl) ⟨3403860, by rfl⟩ : syracuseStep 9076961 = 6807721) B6807721
theorem B21528827 : Blo 992597 21528827 := bstep (se 1 (by rfl) ⟨16146620, by rfl⟩ : syracuseStep 21528827 = 32293241) B32293241
theorem B29033245 : Blo 992597 29033245 := bstep (se 3 (by rfl) ⟨5443733, by rfl⟩ : syracuseStep 29033245 = 10887467) B10887467
theorem B21530285 : Blo 992597 21530285 := bstep (se 3 (by rfl) ⟨4036928, by rfl⟩ : syracuseStep 21530285 = 8073857) B8073857
theorem B7179529 : Blo 992597 7179529 := bstep (se 2 (by rfl) ⟨2692323, by rfl⟩ : syracuseStep 7179529 = 5384647) B5384647
theorem B1675775 : Blo 992597 1675775 := bstep (se 1 (by rfl) ⟨1256831, by rfl⟩ : syracuseStep 1675775 = 2513663) B2513663
theorem B11309705 : Blo 992597 11309705 := bstep (se 2 (by rfl) ⟨4241139, by rfl⟩ : syracuseStep 11309705 = 8482279) B8482279
theorem B2233835 : Blo 992597 2233835 := bstep (se 1 (by rfl) ⟨1675376, by rfl⟩ : syracuseStep 2233835 = 3350753) B3350753
theorem B1119847 : Blo 992597 1119847 := bstep (se 1 (by rfl) ⟨839885, by rfl⟩ : syracuseStep 1119847 = 1679771) B1679771
theorem B3774185 : Blo 992597 3774185 := bstep (se 2 (by rfl) ⟨1415319, by rfl⟩ : syracuseStep 3774185 = 2830639) B2830639
theorem B3184649 : Blo 992597 3184649 := bstep (se 2 (by rfl) ⟨1194243, by rfl⟩ : syracuseStep 3184649 = 2388487) B2388487
theorem B14359751 : Blo 992597 14359751 := bstep (se 1 (by rfl) ⟨10769813, by rfl⟩ : syracuseStep 14359751 = 21539627) B21539627
theorem B2236031 : Blo 992597 2236031 := bstep (se 1 (by rfl) ⟨1677023, by rfl⟩ : syracuseStep 2236031 = 3354047) B3354047
theorem B8495401 : Blo 992597 8495401 := bstep (se 2 (by rfl) ⟨3185775, by rfl⟩ : syracuseStep 8495401 = 6371551) B6371551
theorem B1680635 : Blo 992597 1680635 := bstep (se 1 (by rfl) ⟨1260476, by rfl⟩ : syracuseStep 1680635 = 2520953) B2520953
theorem B7775785 : Blo 992597 7775785 := bstep (se 2 (by rfl) ⟨2915919, by rfl⟩ : syracuseStep 7775785 = 5831839) B5831839
theorem B994111 : Blo 992597 994111 := bstep (se 1 (by rfl) ⟨745583, by rfl⟩ : syracuseStep 994111 = 1491167) B1491167
theorem B21539969 : Blo 992597 21539969 := bstep (se 2 (by rfl) ⟨8077488, by rfl⟩ : syracuseStep 21539969 = 16154977) B16154977
theorem B994535 : Blo 992597 994535 := bstep (se 1 (by rfl) ⟨745901, by rfl⟩ : syracuseStep 994535 = 1491803) B1491803
theorem B3583871 : Blo 992597 3583871 := bstep (se 1 (by rfl) ⟨2687903, by rfl⟩ : syracuseStep 3583871 = 5375807) B5375807
theorem B3354695 : Blo 992597 3354695 := bstep (se 1 (by rfl) ⟨2516021, by rfl⟩ : syracuseStep 3354695 = 5032043) B5032043
theorem B9056609 : Blo 992597 9056609 := bstep (se 2 (by rfl) ⟨3396228, by rfl⟩ : syracuseStep 9056609 = 6792457) B6792457
theorem B5387069 : Blo 992597 5387069 := bstep (se 3 (by rfl) ⟨1010075, by rfl⟩ : syracuseStep 5387069 = 2020151) B2020151
theorem B3355883 : Blo 992597 3355883 := bstep (se 1 (by rfl) ⟨2516912, by rfl⟩ : syracuseStep 3355883 = 5033825) B5033825
theorem B11648879 : Blo 992597 11648879 := bstep (se 1 (by rfl) ⟨8736659, by rfl⟩ : syracuseStep 11648879 = 17473319) B17473319
theorem B5030747 : Blo 992597 5030747 := bstep (se 1 (by rfl) ⟨3773060, by rfl⟩ : syracuseStep 5030747 = 7546121) B7546121
theorem B3359879 : Blo 992597 3359879 := bstep (se 1 (by rfl) ⟨2519909, by rfl⟩ : syracuseStep 3359879 = 5039819) B5039819
theorem B3360041 : Blo 992597 3360041 := bstep (se 2 (by rfl) ⟨1260015, by rfl⟩ : syracuseStep 3360041 = 2520031) B2520031
theorem B14337607 : Blo 992597 14337607 := bstep (se 1 (by rfl) ⟨10753205, by rfl⟩ : syracuseStep 14337607 = 21506411) B21506411
theorem B1493159 : Blo 992597 1493159 := bstep (se 1 (by rfl) ⟨1119869, by rfl⟩ : syracuseStep 1493159 = 2239739) B2239739
theorem B1494185 : Blo 992597 1494185 := bstep (se 2 (by rfl) ⟨560319, by rfl⟩ : syracuseStep 1494185 = 1120639) B1120639
theorem B7556327 : Blo 992597 7556327 := bstep (se 1 (by rfl) ⟨5667245, by rfl⟩ : syracuseStep 7556327 = 11334491) B11334491
theorem B14339339 : Blo 992597 14339339 := bstep (se 1 (by rfl) ⟨10754504, by rfl⟩ : syracuseStep 14339339 = 21509009) B21509009
theorem B4248233 : Blo 992597 4248233 := bstep (se 2 (by rfl) ⟨1593087, by rfl⟩ : syracuseStep 4248233 = 3186175) B3186175
theorem B1596143 : Blo 992597 1596143 := bstep (se 1 (by rfl) ⟨1197107, by rfl⟩ : syracuseStep 1596143 = 2394215) B2394215
theorem B168123671 : Blo 992597 168123671 := bstep (se 1 (by rfl) ⟨126092753, by rfl⟩ : syracuseStep 168123671 = 252185507) B252185507
theorem B5662007 : Blo 992597 5662007 := bstep (se 1 (by rfl) ⟨4246505, by rfl⟩ : syracuseStep 5662007 = 8493011) B8493011
theorem B232679299 : Blo 992597 232679299 := bstep (se 1 (by rfl) ⟨174509474, by rfl⟩ : syracuseStep 232679299 = 349018949) B349018949
theorem B5663465 : Blo 992597 5663465 := bstep (se 2 (by rfl) ⟨2123799, by rfl⟩ : syracuseStep 5663465 = 4247599) B4247599
theorem B8056601 : Blo 992597 8056601 := bstep (se 2 (by rfl) ⟨3021225, by rfl⟩ : syracuseStep 8056601 = 6042451) B6042451
theorem B4256297 : Blo 992597 4256297 := bstep (se 2 (by rfl) ⟨1596111, by rfl⟩ : syracuseStep 4256297 = 3192223) B3192223
theorem B5665423 : Blo 992597 5665423 := bstep (se 1 (by rfl) ⟨4249067, by rfl⟩ : syracuseStep 5665423 = 8498135) B8498135
theorem B7271707 : Blo 992597 7271707 := bstep (se 1 (by rfl) ⟨5453780, by rfl⟩ : syracuseStep 7271707 = 10907561) B10907561
theorem B16971119 : Blo 992597 16971119 := bstep (se 1 (by rfl) ⟨12728339, by rfl⟩ : syracuseStep 16971119 = 25456679) B25456679
theorem B2520841 : Blo 992597 2520841 := bstep (se 2 (by rfl) ⟨945315, by rfl⟩ : syracuseStep 2520841 = 1890631) B1890631
theorem B2685167 : Blo 992597 2685167 := bstep (se 1 (by rfl) ⟨2013875, by rfl⟩ : syracuseStep 2685167 = 4027751) B4027751
theorem B21526823 : Blo 992597 21526823 := bstep (se 1 (by rfl) ⟨16145117, by rfl⟩ : syracuseStep 21526823 = 32290235) B32290235
theorem B14352551 : Blo 992597 14352551 := bstep (se 1 (by rfl) ⟨10764413, by rfl⟩ : syracuseStep 14352551 = 21528827) B21528827
theorem B14353523 : Blo 992597 14353523 := bstep (se 1 (by rfl) ⟨10765142, by rfl⟩ : syracuseStep 14353523 = 21530285) B21530285
theorem B1117183 : Blo 992597 1117183 := bstep (se 1 (by rfl) ⟨837887, by rfl⟩ : syracuseStep 1117183 = 1675775) B1675775
theorem B7539803 : Blo 992597 7539803 := bstep (se 1 (by rfl) ⟨5654852, by rfl⟩ : syracuseStep 7539803 = 11309705) B11309705
theorem B9572705 : Blo 992597 9572705 := bstep (se 2 (by rfl) ⟨3589764, by rfl⟩ : syracuseStep 9572705 = 7179529) B7179529
theorem B9573167 : Blo 992597 9573167 := bstep (se 1 (by rfl) ⟨7179875, by rfl⟩ : syracuseStep 9573167 = 14359751) B14359751
theorem B1120423 : Blo 992597 1120423 := bstep (se 1 (by rfl) ⟨840317, by rfl⟩ : syracuseStep 1120423 = 1680635) B1680635
theorem B3774671 : Blo 992597 3774671 := bstep (se 1 (by rfl) ⟨2831003, by rfl⟩ : syracuseStep 3774671 = 5662007) B5662007
theorem B3775643 : Blo 992597 3775643 := bstep (se 1 (by rfl) ⟨2831732, by rfl⟩ : syracuseStep 3775643 = 5663465) B5663465
theorem B14359979 : Blo 992597 14359979 := bstep (se 1 (by rfl) ⟨10769984, by rfl⟩ : syracuseStep 14359979 = 21539969) B21539969
theorem B2236463 : Blo 992597 2236463 := bstep (se 1 (by rfl) ⟨1677347, by rfl⟩ : syracuseStep 2236463 = 3354695) B3354695
theorem B6037739 : Blo 992597 6037739 := bstep (se 1 (by rfl) ⟨4528304, by rfl⟩ : syracuseStep 6037739 = 9056609) B9056609
theorem B2237255 : Blo 992597 2237255 := bstep (se 1 (by rfl) ⟨1677941, by rfl⟩ : syracuseStep 2237255 = 3355883) B3355883
theorem B11314079 : Blo 992597 11314079 := bstep (se 1 (by rfl) ⟨8485559, by rfl⟩ : syracuseStep 11314079 = 16971119) B16971119
theorem B3353831 : Blo 992597 3353831 := bstep (se 1 (by rfl) ⟨2515373, by rfl⟩ : syracuseStep 3353831 = 5030747) B5030747
theorem B2239919 : Blo 992597 2239919 := bstep (se 1 (by rfl) ⟨1679939, by rfl⟩ : syracuseStep 2239919 = 3359879) B3359879
theorem B2240027 : Blo 992597 2240027 := bstep (se 1 (by rfl) ⟨1680020, by rfl⟩ : syracuseStep 2240027 = 3360041) B3360041
theorem B38710993 : Blo 992597 38710993 := bstep (se 2 (by rfl) ⟨14516622, by rfl⟩ : syracuseStep 38710993 = 29033245) B29033245
theorem B995439 : Blo 992597 995439 := bstep (se 1 (by rfl) ⟨746579, by rfl⟩ : syracuseStep 995439 = 1493159) B1493159
theorem B10367713 : Blo 992597 10367713 := bstep (se 2 (by rfl) ⟨3887892, by rfl⟩ : syracuseStep 10367713 = 7775785) B7775785
theorem B19116809 : Blo 992597 19116809 := bstep (se 2 (by rfl) ⟨7168803, by rfl⟩ : syracuseStep 19116809 = 14337607) B14337607
theorem B996123 : Blo 992597 996123 := bstep (se 1 (by rfl) ⟨747092, by rfl⟩ : syracuseStep 996123 = 1494185) B1494185
theorem B2832155 : Blo 992597 2832155 := bstep (se 1 (by rfl) ⟨2124116, by rfl⟩ : syracuseStep 2832155 = 4248233) B4248233
theorem B1489223 : Blo 992597 1489223 := bstep (se 1 (by rfl) ⟨1116917, by rfl⟩ : syracuseStep 1489223 = 2233835) B2233835
theorem B112082447 : Blo 992597 112082447 := bstep (se 1 (by rfl) ⟨84061835, by rfl⟩ : syracuseStep 112082447 = 168123671) B168123671
theorem B1490687 : Blo 992597 1490687 := bstep (se 1 (by rfl) ⟨1118015, by rfl⟩ : syracuseStep 1490687 = 2236031) B2236031
theorem B7553897 : Blo 992597 7553897 := bstep (se 2 (by rfl) ⟨2832711, by rfl⟩ : syracuseStep 7553897 = 5665423) B5665423
theorem B1493129 : Blo 992597 1493129 := bstep (se 2 (by rfl) ⟨559923, by rfl⟩ : syracuseStep 1493129 = 1119847) B1119847
theorem B3361121 : Blo 992597 3361121 := bstep (se 2 (by rfl) ⟨1260420, by rfl⟩ : syracuseStep 3361121 = 2520841) B2520841
theorem B2837531 : Blo 992597 2837531 := bstep (se 1 (by rfl) ⟨2128148, by rfl⟩ : syracuseStep 2837531 = 4256297) B4256297
theorem B3591379 : Blo 992597 3591379 := bstep (se 1 (by rfl) ⟨2693534, by rfl⟩ : syracuseStep 3591379 = 5387069) B5387069
theorem B1790111 : Blo 992597 1790111 := bstep (se 1 (by rfl) ⟨1342583, by rfl⟩ : syracuseStep 1790111 = 2685167) B2685167
theorem B6051307 : Blo 992597 6051307 := bstep (se 1 (by rfl) ⟨4538480, by rfl⟩ : syracuseStep 6051307 = 9076961) B9076961
theorem B11327201 : Blo 992597 11327201 := bstep (se 2 (by rfl) ⟨4247700, by rfl⟩ : syracuseStep 11327201 = 8495401) B8495401
theorem B5037551 : Blo 992597 5037551 := bstep (se 1 (by rfl) ⟨3778163, by rfl⟩ : syracuseStep 5037551 = 7556327) B7556327
theorem B9559559 : Blo 992597 9559559 := bstep (se 1 (by rfl) ⟨7169669, by rfl⟩ : syracuseStep 9559559 = 14339339) B14339339
theorem B310239065 : Blo 992597 310239065 := bstep (se 2 (by rfl) ⟨116339649, by rfl⟩ : syracuseStep 310239065 = 232679299) B232679299
theorem B2516123 : Blo 992597 2516123 := bstep (se 1 (by rfl) ⟨1887092, by rfl⟩ : syracuseStep 2516123 = 3774185) B3774185
theorem B2123099 : Blo 992597 2123099 := bstep (se 1 (by rfl) ⟨1592324, by rfl⟩ : syracuseStep 2123099 = 3184649) B3184649
theorem B9695609 : Blo 992597 9695609 := bstep (se 2 (by rfl) ⟨3635853, by rfl⟩ : syracuseStep 9695609 = 7271707) B7271707
theorem B4256381 : Blo 992597 4256381 := bstep (se 3 (by rfl) ⟨798071, by rfl⟩ : syracuseStep 4256381 = 1596143) B1596143
theorem B5371067 : Blo 992597 5371067 := bstep (se 1 (by rfl) ⟨4028300, by rfl⟩ : syracuseStep 5371067 = 8056601) B8056601
theorem B2389247 : Blo 992597 2389247 := bstep (se 1 (by rfl) ⟨1791935, by rfl⟩ : syracuseStep 2389247 = 3583871) B3583871
theorem B14351215 : Blo 992597 14351215 := bstep (se 1 (by rfl) ⟨10763411, by rfl⟩ : syracuseStep 14351215 = 21526823) B21526823
theorem B7765919 : Blo 992597 7765919 := bstep (se 1 (by rfl) ⟨5824439, by rfl⟩ : syracuseStep 7765919 = 11648879) B11648879
theorem B9568367 : Blo 992597 9568367 := bstep (se 1 (by rfl) ⟨7176275, by rfl⟩ : syracuseStep 9568367 = 14352551) B14352551
theorem B9569015 : Blo 992597 9569015 := bstep (se 1 (by rfl) ⟨7176761, by rfl⟩ : syracuseStep 9569015 = 14353523) B14353523
theorem B14322845 : Blo 992597 14322845 := bstep (se 3 (by rfl) ⟨2685533, by rfl⟩ : syracuseStep 14322845 = 5371067) B5371067
theorem B4788505 : Blo 992597 4788505 := bstep (se 2 (by rfl) ⟨1795689, by rfl⟩ : syracuseStep 4788505 = 3591379) B3591379
theorem B51614657 : Blo 992597 51614657 := bstep (se 2 (by rfl) ⟨19355496, by rfl⟩ : syracuseStep 51614657 = 38710993) B38710993
theorem B9573319 : Blo 992597 9573319 := bstep (se 1 (by rfl) ⟨7179989, by rfl⟩ : syracuseStep 9573319 = 14359979) B14359979
theorem B7542719 : Blo 992597 7542719 := bstep (se 1 (by rfl) ⟨5657039, by rfl⟩ : syracuseStep 7542719 = 11314079) B11314079
theorem B1677415 : Blo 992597 1677415 := bstep (se 1 (by rfl) ⟨1258061, by rfl⟩ : syracuseStep 1677415 = 2516123) B2516123
theorem B1415399 : Blo 992597 1415399 := bstep (se 1 (by rfl) ⟨1061549, by rfl⟩ : syracuseStep 1415399 = 2123099) B2123099
theorem B8068409 : Blo 992597 8068409 := bstep (se 2 (by rfl) ⟨3025653, by rfl⟩ : syracuseStep 8068409 = 6051307) B6051307
theorem B2235887 : Blo 992597 2235887 := bstep (se 1 (by rfl) ⟨1676915, by rfl⟩ : syracuseStep 2235887 = 3353831) B3353831
theorem B6463739 : Blo 992597 6463739 := bstep (se 1 (by rfl) ⟨4847804, by rfl⟩ : syracuseStep 6463739 = 9695609) B9695609
theorem B992815 : Blo 992597 992815 := bstep (se 1 (by rfl) ⟨744611, by rfl⟩ : syracuseStep 992815 = 1489223) B1489223
theorem B74721631 : Blo 992597 74721631 := bstep (se 1 (by rfl) ⟨56041223, by rfl⟩ : syracuseStep 74721631 = 112082447) B112082447
theorem B993791 : Blo 992597 993791 := bstep (se 1 (by rfl) ⟨745343, by rfl⟩ : syracuseStep 993791 = 1490687) B1490687
theorem B995419 : Blo 992597 995419 := bstep (se 1 (by rfl) ⟨746564, by rfl⟩ : syracuseStep 995419 = 1493129) B1493129
theorem B2240747 : Blo 992597 2240747 := bstep (se 1 (by rfl) ⟨1680560, by rfl⟩ : syracuseStep 2240747 = 3361121) B3361121
theorem B5026535 : Blo 992597 5026535 := bstep (se 1 (by rfl) ⟨3769901, by rfl⟩ : syracuseStep 5026535 = 7539803) B7539803
theorem B7551467 : Blo 992597 7551467 := bstep (se 1 (by rfl) ⟨5663600, by rfl⟩ : syracuseStep 7551467 = 11327201) B11327201
theorem B1489577 : Blo 992597 1489577 := bstep (se 2 (by rfl) ⟨558591, by rfl⟩ : syracuseStep 1489577 = 1117183) B1117183
theorem B3358367 : Blo 992597 3358367 := bstep (se 1 (by rfl) ⟨2518775, by rfl⟩ : syracuseStep 3358367 = 5037551) B5037551
theorem B6373039 : Blo 992597 6373039 := bstep (se 1 (by rfl) ⟨4779779, by rfl⟩ : syracuseStep 6373039 = 9559559) B9559559
theorem B1490975 : Blo 992597 1490975 := bstep (se 1 (by rfl) ⟨1118231, by rfl⟩ : syracuseStep 1490975 = 2236463) B2236463
theorem B1491503 : Blo 992597 1491503 := bstep (se 1 (by rfl) ⟨1118627, by rfl⟩ : syracuseStep 1491503 = 2237255) B2237255
theorem B1493279 : Blo 992597 1493279 := bstep (se 1 (by rfl) ⟨1119959, by rfl⟩ : syracuseStep 1493279 = 2239919) B2239919
theorem B1493351 : Blo 992597 1493351 := bstep (se 1 (by rfl) ⟨1120013, by rfl⟩ : syracuseStep 1493351 = 2240027) B2240027
theorem B1493897 : Blo 992597 1493897 := bstep (se 2 (by rfl) ⟨560211, by rfl⟩ : syracuseStep 1493897 = 1120423) B1120423
theorem B2837587 : Blo 992597 2837587 := bstep (se 1 (by rfl) ⟨2128190, by rfl⟩ : syracuseStep 2837587 = 4256381) B4256381
theorem B1592831 : Blo 992597 1592831 := bstep (se 1 (by rfl) ⟨1194623, by rfl⟩ : syracuseStep 1592831 = 2389247) B2389247
theorem B1888103 : Blo 992597 1888103 := bstep (se 1 (by rfl) ⟨1416077, by rfl⟩ : syracuseStep 1888103 = 2832155) B2832155
theorem B4773629 : Blo 992597 4773629 := bstep (se 3 (by rfl) ⟨895055, by rfl⟩ : syracuseStep 4773629 = 1790111) B1790111
theorem B5035931 : Blo 992597 5035931 := bstep (se 1 (by rfl) ⟨3776948, by rfl⟩ : syracuseStep 5035931 = 7553897) B7553897
theorem B1891687 : Blo 992597 1891687 := bstep (se 1 (by rfl) ⟨1418765, by rfl⟩ : syracuseStep 1891687 = 2837531) B2837531
theorem B6381803 : Blo 992597 6381803 := bstep (se 1 (by rfl) ⟨4786352, by rfl⟩ : syracuseStep 6381803 = 9572705) B9572705
theorem B6382111 : Blo 992597 6382111 := bstep (se 1 (by rfl) ⟨4786583, by rfl⟩ : syracuseStep 6382111 = 9573167) B9573167
theorem B2516447 : Blo 992597 2516447 := bstep (se 1 (by rfl) ⟨1887335, by rfl⟩ : syracuseStep 2516447 = 3774671) B3774671
theorem B2517095 : Blo 992597 2517095 := bstep (se 1 (by rfl) ⟨1887821, by rfl⟩ : syracuseStep 2517095 = 3775643) B3775643
theorem B206826043 : Blo 992597 206826043 := bstep (se 1 (by rfl) ⟨155119532, by rfl⟩ : syracuseStep 206826043 = 310239065) B310239065
theorem B4025159 : Blo 992597 4025159 := bstep (se 1 (by rfl) ⟨3018869, by rfl⟩ : syracuseStep 4025159 = 6037739) B6037739
theorem B13823617 : Blo 992597 13823617 := bstep (se 2 (by rfl) ⟨5183856, by rfl⟩ : syracuseStep 13823617 = 10367713) B10367713
theorem B12744539 : Blo 992597 12744539 := bstep (se 1 (by rfl) ⟨9558404, by rfl⟩ : syracuseStep 12744539 = 19116809) B19116809
theorem B19134953 : Blo 992597 19134953 := bstep (se 2 (by rfl) ⟨7175607, by rfl⟩ : syracuseStep 19134953 = 14351215) B14351215
theorem B5177279 : Blo 992597 5177279 := bstep (se 1 (by rfl) ⟨3882959, by rfl⟩ : syracuseStep 5177279 = 7765919) B7765919
theorem B17236637 : Blo 992597 17236637 := bstep (se 3 (by rfl) ⟨3231869, by rfl⟩ : syracuseStep 17236637 = 6463739) B6463739
theorem B34409771 : Blo 992597 34409771 := bstep (se 1 (by rfl) ⟨25807328, by rfl⟩ : syracuseStep 34409771 = 51614657) B51614657
theorem B3182419 : Blo 992597 3182419 := bstep (se 1 (by rfl) ⟨2386814, by rfl⟩ : syracuseStep 3182419 = 4773629) B4773629
theorem B5378939 : Blo 992597 5378939 := bstep (se 1 (by rfl) ⟨4034204, by rfl⟩ : syracuseStep 5378939 = 8068409) B8068409
theorem B3774397 : Blo 992597 3774397 := bstep (se 3 (by rfl) ⟨707699, by rfl⟩ : syracuseStep 3774397 = 1415399) B1415399
theorem B1677631 : Blo 992597 1677631 := bstep (se 1 (by rfl) ⟨1258223, by rfl⟩ : syracuseStep 1677631 = 2516447) B2516447
theorem B1678063 : Blo 992597 1678063 := bstep (se 1 (by rfl) ⟨1258547, by rfl⟩ : syracuseStep 1678063 = 2517095) B2517095
theorem B2236553 : Blo 992597 2236553 := bstep (se 2 (by rfl) ⟨838707, by rfl⟩ : syracuseStep 2236553 = 1677415) B1677415
theorem B3351023 : Blo 992597 3351023 := bstep (se 1 (by rfl) ⟨2513267, by rfl⟩ : syracuseStep 3351023 = 5026535) B5026535
theorem B8496359 : Blo 992597 8496359 := bstep (se 1 (by rfl) ⟨6372269, by rfl⟩ : syracuseStep 8496359 = 12744539) B12744539
theorem B12756635 : Blo 992597 12756635 := bstep (se 1 (by rfl) ⟨9567476, by rfl⟩ : syracuseStep 12756635 = 19134953) B19134953
theorem B993051 : Blo 992597 993051 := bstep (se 1 (by rfl) ⟨744788, by rfl⟩ : syracuseStep 993051 = 1489577) B1489577
theorem B8497385 : Blo 992597 8497385 := bstep (se 2 (by rfl) ⟨3186519, by rfl⟩ : syracuseStep 8497385 = 6373039) B6373039
theorem B2238911 : Blo 992597 2238911 := bstep (se 1 (by rfl) ⟨1679183, by rfl⟩ : syracuseStep 2238911 = 3358367) B3358367
theorem B13806077 : Blo 992597 13806077 := bstep (se 3 (by rfl) ⟨2588639, by rfl⟩ : syracuseStep 13806077 = 5177279) B5177279
theorem B993983 : Blo 992597 993983 := bstep (se 1 (by rfl) ⟨745487, by rfl⟩ : syracuseStep 993983 = 1490975) B1490975
theorem B994335 : Blo 992597 994335 := bstep (se 1 (by rfl) ⟨745751, by rfl⟩ : syracuseStep 994335 = 1491503) B1491503
theorem B995519 : Blo 992597 995519 := bstep (se 1 (by rfl) ⟨746639, by rfl⟩ : syracuseStep 995519 = 1493279) B1493279
theorem B995567 : Blo 992597 995567 := bstep (se 1 (by rfl) ⟨746675, by rfl⟩ : syracuseStep 995567 = 1493351) B1493351
theorem B995931 : Blo 992597 995931 := bstep (se 1 (by rfl) ⟨746948, by rfl⟩ : syracuseStep 995931 = 1493897) B1493897
theorem B9548563 : Blo 992597 9548563 := bstep (se 1 (by rfl) ⟨7161422, by rfl⟩ : syracuseStep 9548563 = 14322845) B14322845
theorem B1258735 : Blo 992597 1258735 := bstep (se 1 (by rfl) ⟨944051, by rfl⟩ : syracuseStep 1258735 = 1888103) B1888103
theorem B99628841 : Blo 992597 99628841 := bstep (se 2 (by rfl) ⟨37360815, by rfl⟩ : syracuseStep 99628841 = 74721631) B74721631
theorem B3357287 : Blo 992597 3357287 := bstep (se 1 (by rfl) ⟨2517965, by rfl⟩ : syracuseStep 3357287 = 5035931) B5035931
theorem B5028479 : Blo 992597 5028479 := bstep (se 1 (by rfl) ⟨3771359, by rfl⟩ : syracuseStep 5028479 = 7542719) B7542719
theorem B3783449 : Blo 992597 3783449 := bstep (se 2 (by rfl) ⟨1418793, by rfl⟩ : syracuseStep 3783449 = 2837587) B2837587
theorem B18431489 : Blo 992597 18431489 := bstep (se 2 (by rfl) ⟨6911808, by rfl⟩ : syracuseStep 18431489 = 13823617) B13823617
theorem B1490591 : Blo 992597 1490591 := bstep (se 1 (by rfl) ⟨1117943, by rfl⟩ : syracuseStep 1490591 = 2235887) B2235887
theorem B12764425 : Blo 992597 12764425 := bstep (se 2 (by rfl) ⟨4786659, by rfl⟩ : syracuseStep 12764425 = 9573319) B9573319
theorem B1493831 : Blo 992597 1493831 := bstep (se 1 (by rfl) ⟨1120373, by rfl⟩ : syracuseStep 1493831 = 2240747) B2240747
theorem B4247549 : Blo 992597 4247549 := bstep (se 3 (by rfl) ⟨796415, by rfl⟩ : syracuseStep 4247549 = 1592831) B1592831
theorem B5034311 : Blo 992597 5034311 := bstep (se 1 (by rfl) ⟨3775733, by rfl⟩ : syracuseStep 5034311 = 7551467) B7551467
theorem B6378911 : Blo 992597 6378911 := bstep (se 1 (by rfl) ⟨4784183, by rfl⟩ : syracuseStep 6378911 = 9568367) B9568367
theorem B6379343 : Blo 992597 6379343 := bstep (se 1 (by rfl) ⟨4784507, by rfl⟩ : syracuseStep 6379343 = 9569015) B9569015
theorem B8509481 : Blo 992597 8509481 := bstep (se 2 (by rfl) ⟨3191055, by rfl⟩ : syracuseStep 8509481 = 6382111) B6382111
theorem B275768057 : Blo 992597 275768057 := bstep (se 2 (by rfl) ⟨103413021, by rfl⟩ : syracuseStep 275768057 = 206826043) B206826043
theorem B4254535 : Blo 992597 4254535 := bstep (se 1 (by rfl) ⟨3190901, by rfl⟩ : syracuseStep 4254535 = 6381803) B6381803
theorem B6384673 : Blo 992597 6384673 := bstep (se 2 (by rfl) ⟨2394252, by rfl⟩ : syracuseStep 6384673 = 4788505) B4788505
theorem B2683439 : Blo 992597 2683439 := bstep (se 1 (by rfl) ⟨2012579, by rfl⟩ : syracuseStep 2683439 = 4025159) B4025159
theorem B2522249 : Blo 992597 2522249 := bstep (se 2 (by rfl) ⟨945843, by rfl⟩ : syracuseStep 2522249 = 1891687) B1891687
theorem B22939847 : Blo 992597 22939847 := bstep (se 1 (by rfl) ⟨17204885, by rfl⟩ : syracuseStep 22939847 = 34409771) B34409771
theorem B5672713 : Blo 992597 5672713 := bstep (se 2 (by rfl) ⟨2127267, by rfl⟩ : syracuseStep 5672713 = 4254535) B4254535
theorem B5672987 : Blo 992597 5672987 := bstep (se 1 (by rfl) ⟨4254740, by rfl⟩ : syracuseStep 5672987 = 8509481) B8509481
theorem B2234015 : Blo 992597 2234015 := bstep (se 1 (by rfl) ⟨1675511, by rfl⟩ : syracuseStep 2234015 = 3351023) B3351023
theorem B1678313 : Blo 992597 1678313 := bstep (se 2 (by rfl) ⟨629367, by rfl⟩ : syracuseStep 1678313 = 1258735) B1258735
theorem B2236841 : Blo 992597 2236841 := bstep (se 2 (by rfl) ⟨838815, by rfl⟩ : syracuseStep 2236841 = 1677631) B1677631
theorem B2237417 : Blo 992597 2237417 := bstep (se 2 (by rfl) ⟨839031, by rfl⟩ : syracuseStep 2237417 = 1678063) B1678063
theorem B2238191 : Blo 992597 2238191 := bstep (se 1 (by rfl) ⟨1678643, by rfl⟩ : syracuseStep 2238191 = 3357287) B3357287
theorem B3352319 : Blo 992597 3352319 := bstep (se 1 (by rfl) ⟨2514239, by rfl⟩ : syracuseStep 3352319 = 5028479) B5028479
theorem B1681499 : Blo 992597 1681499 := bstep (se 1 (by rfl) ⟨1261124, by rfl⟩ : syracuseStep 1681499 = 2522249) B2522249
theorem B993727 : Blo 992597 993727 := bstep (se 1 (by rfl) ⟨745295, by rfl⟩ : syracuseStep 993727 = 1490591) B1490591
theorem B17019233 : Blo 992597 17019233 := bstep (se 2 (by rfl) ⟨6382212, by rfl⟩ : syracuseStep 17019233 = 12764425) B12764425
theorem B995887 : Blo 992597 995887 := bstep (se 1 (by rfl) ⟨746915, by rfl⟩ : syracuseStep 995887 = 1493831) B1493831
theorem B2831699 : Blo 992597 2831699 := bstep (se 1 (by rfl) ⟨2123774, by rfl⟩ : syracuseStep 2831699 = 4247549) B4247549
theorem B3356207 : Blo 992597 3356207 := bstep (se 1 (by rfl) ⟨2517155, by rfl⟩ : syracuseStep 3356207 = 5034311) B5034311
theorem B3585959 : Blo 992597 3585959 := bstep (se 1 (by rfl) ⟨2689469, by rfl⟩ : syracuseStep 3585959 = 5378939) B5378939
theorem B4243225 : Blo 992597 4243225 := bstep (se 2 (by rfl) ⟨1591209, by rfl⟩ : syracuseStep 4243225 = 3182419) B3182419
theorem B1491035 : Blo 992597 1491035 := bstep (se 1 (by rfl) ⟨1118276, by rfl⟩ : syracuseStep 1491035 = 2236553) B2236553
theorem B183845371 : Blo 992597 183845371 := bstep (se 1 (by rfl) ⟨137884028, by rfl⟩ : syracuseStep 183845371 = 275768057) B275768057
theorem B12731417 : Blo 992597 12731417 := bstep (se 2 (by rfl) ⟨4774281, by rfl⟩ : syracuseStep 12731417 = 9548563) B9548563
theorem B8504423 : Blo 992597 8504423 := bstep (se 1 (by rfl) ⟨6378317, by rfl⟩ : syracuseStep 8504423 = 12756635) B12756635
theorem B36816205 : Blo 992597 36816205 := bstep (se 3 (by rfl) ⟨6903038, by rfl⟩ : syracuseStep 36816205 = 13806077) B13806077
theorem B1492607 : Blo 992597 1492607 := bstep (se 1 (by rfl) ⟨1119455, by rfl⟩ : syracuseStep 1492607 = 2238911) B2238911
theorem B5032529 : Blo 992597 5032529 := bstep (se 2 (by rfl) ⟨1887198, by rfl⟩ : syracuseStep 5032529 = 3774397) B3774397
theorem B1788959 : Blo 992597 1788959 := bstep (se 1 (by rfl) ⟨1341719, by rfl⟩ : syracuseStep 1788959 = 2683439) B2683439
theorem B11491091 : Blo 992597 11491091 := bstep (se 1 (by rfl) ⟨8618318, by rfl⟩ : syracuseStep 11491091 = 17236637) B17236637
theorem B4252607 : Blo 992597 4252607 := bstep (se 1 (by rfl) ⟨3189455, by rfl⟩ : syracuseStep 4252607 = 6378911) B6378911
theorem B4252895 : Blo 992597 4252895 := bstep (se 1 (by rfl) ⟨3189671, by rfl⟩ : syracuseStep 4252895 = 6379343) B6379343
theorem B8512897 : Blo 992597 8512897 := bstep (se 2 (by rfl) ⟨3192336, by rfl⟩ : syracuseStep 8512897 = 6384673) B6384673
theorem B5664239 : Blo 992597 5664239 := bstep (se 1 (by rfl) ⟨4248179, by rfl⟩ : syracuseStep 5664239 = 8496359) B8496359
theorem B5664923 : Blo 992597 5664923 := bstep (se 1 (by rfl) ⟨4248692, by rfl⟩ : syracuseStep 5664923 = 8497385) B8497385
theorem B66419227 : Blo 992597 66419227 := bstep (se 1 (by rfl) ⟨49814420, by rfl⟩ : syracuseStep 66419227 = 99628841) B99628841
theorem B2522299 : Blo 992597 2522299 := bstep (se 1 (by rfl) ⟨1891724, by rfl⟩ : syracuseStep 2522299 = 3783449) B3783449
theorem B12287659 : Blo 992597 12287659 := bstep (se 1 (by rfl) ⟨9215744, by rfl⟩ : syracuseStep 12287659 = 18431489) B18431489
theorem B8487611 : Blo 992597 8487611 := bstep (se 1 (by rfl) ⟨6365708, by rfl⟩ : syracuseStep 8487611 = 12731417) B12731417
theorem B5669615 : Blo 992597 5669615 := bstep (se 1 (by rfl) ⟨4252211, by rfl⟩ : syracuseStep 5669615 = 8504423) B8504423
theorem B49088273 : Blo 992597 49088273 := bstep (se 2 (by rfl) ⟨18408102, by rfl⟩ : syracuseStep 49088273 = 36816205) B36816205
theorem B1118875 : Blo 992597 1118875 := bstep (se 1 (by rfl) ⟨839156, by rfl⟩ : syracuseStep 1118875 = 1678313) B1678313
theorem B2234879 : Blo 992597 2234879 := bstep (se 1 (by rfl) ⟨1676159, by rfl⟩ : syracuseStep 2234879 = 3352319) B3352319
theorem B1120999 : Blo 992597 1120999 := bstep (se 1 (by rfl) ⟨840749, by rfl⟩ : syracuseStep 1120999 = 1681499) B1681499
theorem B3776159 : Blo 992597 3776159 := bstep (se 1 (by rfl) ⟨2832119, by rfl⟩ : syracuseStep 3776159 = 5664239) B5664239
theorem B3776615 : Blo 992597 3776615 := bstep (se 1 (by rfl) ⟨2832461, by rfl⟩ : syracuseStep 3776615 = 5664923) B5664923
theorem B11346155 : Blo 992597 11346155 := bstep (se 1 (by rfl) ⟨8509616, by rfl⟩ : syracuseStep 11346155 = 17019233) B17019233
theorem B2237471 : Blo 992597 2237471 := bstep (se 1 (by rfl) ⟨1678103, by rfl⟩ : syracuseStep 2237471 = 3356207) B3356207
theorem B994023 : Blo 992597 994023 := bstep (se 1 (by rfl) ⟨745517, by rfl⟩ : syracuseStep 994023 = 1491035) B1491035
theorem B995071 : Blo 992597 995071 := bstep (se 1 (by rfl) ⟨746303, by rfl⟩ : syracuseStep 995071 = 1492607) B1492607
theorem B3355019 : Blo 992597 3355019 := bstep (se 1 (by rfl) ⟨2516264, by rfl⟩ : syracuseStep 3355019 = 5032529) B5032529
theorem B11350529 : Blo 992597 11350529 := bstep (se 2 (by rfl) ⟨4256448, by rfl⟩ : syracuseStep 11350529 = 8512897) B8512897
theorem B1192639 : Blo 992597 1192639 := bstep (se 1 (by rfl) ⟨894479, by rfl⟩ : syracuseStep 1192639 = 1788959) B1788959
theorem B3781991 : Blo 992597 3781991 := bstep (se 1 (by rfl) ⟨2836493, by rfl⟩ : syracuseStep 3781991 = 5672987) B5672987
theorem B1489343 : Blo 992597 1489343 := bstep (se 1 (by rfl) ⟨1117007, by rfl⟩ : syracuseStep 1489343 = 2234015) B2234015
theorem B1491227 : Blo 992597 1491227 := bstep (se 1 (by rfl) ⟨1118420, by rfl⟩ : syracuseStep 1491227 = 2236841) B2236841
theorem B2835071 : Blo 992597 2835071 := bstep (se 1 (by rfl) ⟨2126303, by rfl⟩ : syracuseStep 2835071 = 4252607) B4252607
theorem B1491611 : Blo 992597 1491611 := bstep (se 1 (by rfl) ⟨1118708, by rfl⟩ : syracuseStep 1491611 = 2237417) B2237417
theorem B2835263 : Blo 992597 2835263 := bstep (se 1 (by rfl) ⟨2126447, by rfl⟩ : syracuseStep 2835263 = 4252895) B4252895
theorem B1492127 : Blo 992597 1492127 := bstep (se 1 (by rfl) ⟨1119095, by rfl⟩ : syracuseStep 1492127 = 2238191) B2238191
theorem B88558969 : Blo 992597 88558969 := bstep (se 2 (by rfl) ⟨33209613, by rfl⟩ : syracuseStep 88558969 = 66419227) B66419227
theorem B1887799 : Blo 992597 1887799 := bstep (se 1 (by rfl) ⟨1415849, by rfl⟩ : syracuseStep 1887799 = 2831699) B2831699
theorem B3363065 : Blo 992597 3363065 := bstep (se 2 (by rfl) ⟨1261149, by rfl⟩ : syracuseStep 3363065 = 2522299) B2522299
theorem B5657633 : Blo 992597 5657633 := bstep (se 2 (by rfl) ⟨2121612, by rfl⟩ : syracuseStep 5657633 = 4243225) B4243225
theorem B245127161 : Blo 992597 245127161 := bstep (se 2 (by rfl) ⟨91922685, by rfl⟩ : syracuseStep 245127161 = 183845371) B183845371
theorem B15293231 : Blo 992597 15293231 := bstep (se 1 (by rfl) ⟨11469923, by rfl⟩ : syracuseStep 15293231 = 22939847) B22939847
theorem B7660727 : Blo 992597 7660727 := bstep (se 1 (by rfl) ⟨5745545, by rfl⟩ : syracuseStep 7660727 = 11491091) B11491091
theorem B7563617 : Blo 992597 7563617 := bstep (se 2 (by rfl) ⟨2836356, by rfl⟩ : syracuseStep 7563617 = 5672713) B5672713
theorem B2390639 : Blo 992597 2390639 := bstep (se 1 (by rfl) ⟨1792979, by rfl⟩ : syracuseStep 2390639 = 3585959) B3585959
theorem B16383545 : Blo 992597 16383545 := bstep (se 2 (by rfl) ⟨6143829, by rfl⟩ : syracuseStep 16383545 = 12287659) B12287659
theorem B3771755 : Blo 992597 3771755 := bstep (se 1 (by rfl) ⟨2828816, by rfl⟩ : syracuseStep 3771755 = 5657633) B5657633
theorem B163418107 : Blo 992597 163418107 := bstep (se 1 (by rfl) ⟨122563580, by rfl⟩ : syracuseStep 163418107 = 245127161) B245127161
theorem B10195487 : Blo 992597 10195487 := bstep (se 1 (by rfl) ⟨7646615, by rfl⟩ : syracuseStep 10195487 = 15293231) B15293231
theorem B523608245 : Blo 992597 523608245 := bstep (se 5 (by rfl) ⟨24544136, by rfl⟩ : syracuseStep 523608245 = 49088273) B49088273
theorem B2236679 : Blo 992597 2236679 := bstep (se 1 (by rfl) ⟨1677509, by rfl⟩ : syracuseStep 2236679 = 3355019) B3355019
theorem B992895 : Blo 992597 992895 := bstep (se 1 (by rfl) ⟨744671, by rfl⟩ : syracuseStep 992895 = 1489343) B1489343
theorem B10922363 : Blo 992597 10922363 := bstep (se 1 (by rfl) ⟨8191772, by rfl⟩ : syracuseStep 10922363 = 16383545) B16383545
theorem B994151 : Blo 992597 994151 := bstep (se 1 (by rfl) ⟨745613, by rfl⟩ : syracuseStep 994151 = 1491227) B1491227
theorem B994407 : Blo 992597 994407 := bstep (se 1 (by rfl) ⟨745805, by rfl⟩ : syracuseStep 994407 = 1491611) B1491611
theorem B3779743 : Blo 992597 3779743 := bstep (se 1 (by rfl) ⟨2834807, by rfl⟩ : syracuseStep 3779743 = 5669615) B5669615
theorem B994751 : Blo 992597 994751 := bstep (se 1 (by rfl) ⟨746063, by rfl⟩ : syracuseStep 994751 = 1492127) B1492127
theorem B2242043 : Blo 992597 2242043 := bstep (se 1 (by rfl) ⟨1681532, by rfl⟩ : syracuseStep 2242043 = 3363065) B3363065
theorem B1489919 : Blo 992597 1489919 := bstep (se 1 (by rfl) ⟨1117439, by rfl⟩ : syracuseStep 1489919 = 2234879) B2234879
theorem B118078625 : Blo 992597 118078625 := bstep (se 2 (by rfl) ⟨44279484, by rfl⟩ : syracuseStep 118078625 = 88558969) B88558969
theorem B1491647 : Blo 992597 1491647 := bstep (se 1 (by rfl) ⟨1118735, by rfl⟩ : syracuseStep 1491647 = 2237471) B2237471
theorem B1491833 : Blo 992597 1491833 := bstep (se 2 (by rfl) ⟨559437, by rfl⟩ : syracuseStep 1491833 = 1118875) B1118875
theorem B1590185 : Blo 992597 1590185 := bstep (se 2 (by rfl) ⟨596319, by rfl⟩ : syracuseStep 1590185 = 1192639) B1192639
theorem B6375037 : Blo 992597 6375037 := bstep (se 3 (by rfl) ⟨1195319, by rfl⟩ : syracuseStep 6375037 = 2390639) B2390639
theorem B1494665 : Blo 992597 1494665 := bstep (se 2 (by rfl) ⟨560499, by rfl⟩ : syracuseStep 1494665 = 1120999) B1120999
theorem B1890047 : Blo 992597 1890047 := bstep (se 1 (by rfl) ⟨1417535, by rfl⟩ : syracuseStep 1890047 = 2835071) B2835071
theorem B5658407 : Blo 992597 5658407 := bstep (se 1 (by rfl) ⟨4243805, by rfl⟩ : syracuseStep 5658407 = 8487611) B8487611
theorem B7560701 : Blo 992597 7560701 := bstep (se 3 (by rfl) ⟨1417631, by rfl⟩ : syracuseStep 7560701 = 2835263) B2835263
theorem B2517065 : Blo 992597 2517065 := bstep (se 2 (by rfl) ⟨943899, by rfl⟩ : syracuseStep 2517065 = 1887799) B1887799
theorem B2517439 : Blo 992597 2517439 := bstep (se 1 (by rfl) ⟨1888079, by rfl⟩ : syracuseStep 2517439 = 3776159) B3776159
theorem B2517743 : Blo 992597 2517743 := bstep (se 1 (by rfl) ⟨1888307, by rfl⟩ : syracuseStep 2517743 = 3776615) B3776615
theorem B7564103 : Blo 992597 7564103 := bstep (se 1 (by rfl) ⟨5673077, by rfl⟩ : syracuseStep 7564103 = 11346155) B11346155
theorem B5107151 : Blo 992597 5107151 := bstep (se 1 (by rfl) ⟨3830363, by rfl⟩ : syracuseStep 5107151 = 7660727) B7660727
theorem B5042411 : Blo 992597 5042411 := bstep (se 1 (by rfl) ⟨3781808, by rfl⟩ : syracuseStep 5042411 = 7563617) B7563617
theorem B7567019 : Blo 992597 7567019 := bstep (se 1 (by rfl) ⟨5675264, by rfl⟩ : syracuseStep 7567019 = 11350529) B11350529
theorem B2521327 : Blo 992597 2521327 := bstep (se 1 (by rfl) ⟨1890995, by rfl⟩ : syracuseStep 2521327 = 3781991) B3781991
theorem B3772271 : Blo 992597 3772271 := bstep (se 1 (by rfl) ⟨2829203, by rfl⟩ : syracuseStep 3772271 = 5658407) B5658407
theorem B1678043 : Blo 992597 1678043 := bstep (se 1 (by rfl) ⟨1258532, by rfl⟩ : syracuseStep 1678043 = 2517065) B2517065
theorem B7281575 : Blo 992597 7281575 := bstep (se 1 (by rfl) ⟨5461181, by rfl⟩ : syracuseStep 7281575 = 10922363) B10922363
theorem B1678495 : Blo 992597 1678495 := bstep (se 1 (by rfl) ⟨1258871, by rfl⟩ : syracuseStep 1678495 = 2517743) B2517743
theorem B993279 : Blo 992597 993279 := bstep (se 1 (by rfl) ⟨744959, by rfl⟩ : syracuseStep 993279 = 1489919) B1489919
theorem B78719083 : Blo 992597 78719083 := bstep (se 1 (by rfl) ⟨59039312, by rfl⟩ : syracuseStep 78719083 = 118078625) B118078625
theorem B994431 : Blo 992597 994431 := bstep (se 1 (by rfl) ⟨745823, by rfl⟩ : syracuseStep 994431 = 1491647) B1491647
theorem B994555 : Blo 992597 994555 := bstep (se 1 (by rfl) ⟨745916, by rfl⟩ : syracuseStep 994555 = 1491833) B1491833
theorem B1060123 : Blo 992597 1060123 := bstep (se 1 (by rfl) ⟨795092, by rfl⟩ : syracuseStep 1060123 = 1590185) B1590185
theorem B8500049 : Blo 992597 8500049 := bstep (se 2 (by rfl) ⟨3187518, by rfl⟩ : syracuseStep 8500049 = 6375037) B6375037
theorem B996443 : Blo 992597 996443 := bstep (se 1 (by rfl) ⟨747332, by rfl⟩ : syracuseStep 996443 = 1494665) B1494665
theorem B6796991 : Blo 992597 6796991 := bstep (se 1 (by rfl) ⟨5097743, by rfl⟩ : syracuseStep 6796991 = 10195487) B10195487
theorem B3356585 : Blo 992597 3356585 := bstep (se 2 (by rfl) ⟨1258719, by rfl⟩ : syracuseStep 3356585 = 2517439) B2517439
theorem B1260031 : Blo 992597 1260031 := bstep (se 1 (by rfl) ⟨945023, by rfl⟩ : syracuseStep 1260031 = 1890047) B1890047
theorem B217890809 : Blo 992597 217890809 := bstep (se 2 (by rfl) ⟨81709053, by rfl⟩ : syracuseStep 217890809 = 163418107) B163418107
theorem B1491119 : Blo 992597 1491119 := bstep (se 1 (by rfl) ⟨1118339, by rfl⟩ : syracuseStep 1491119 = 2236679) B2236679
theorem B3361607 : Blo 992597 3361607 := bstep (se 1 (by rfl) ⟨2521205, by rfl⟩ : syracuseStep 3361607 = 5042411) B5042411
theorem B3361769 : Blo 992597 3361769 := bstep (se 2 (by rfl) ⟨1260663, by rfl⟩ : syracuseStep 3361769 = 2521327) B2521327
theorem B1494695 : Blo 992597 1494695 := bstep (se 1 (by rfl) ⟨1121021, by rfl⟩ : syracuseStep 1494695 = 2242043) B2242043
theorem B2514503 : Blo 992597 2514503 := bstep (se 1 (by rfl) ⟨1885877, by rfl⟩ : syracuseStep 2514503 = 3771755) B3771755
theorem B5039657 : Blo 992597 5039657 := bstep (se 2 (by rfl) ⟨1889871, by rfl⟩ : syracuseStep 5039657 = 3779743) B3779743
theorem B5040467 : Blo 992597 5040467 := bstep (se 1 (by rfl) ⟨3780350, by rfl⟩ : syracuseStep 5040467 = 7560701) B7560701
theorem B349072163 : Blo 992597 349072163 := bstep (se 1 (by rfl) ⟨261804122, by rfl⟩ : syracuseStep 349072163 = 523608245) B523608245
theorem B5042735 : Blo 992597 5042735 := bstep (se 1 (by rfl) ⟨3782051, by rfl⟩ : syracuseStep 5042735 = 7564103) B7564103
theorem B3404767 : Blo 992597 3404767 := bstep (se 1 (by rfl) ⟨2553575, by rfl⟩ : syracuseStep 3404767 = 5107151) B5107151
theorem B5044679 : Blo 992597 5044679 := bstep (se 1 (by rfl) ⟨3783509, by rfl⟩ : syracuseStep 5044679 = 7567019) B7567019
theorem B1413497 : Blo 992597 1413497 := bstep (se 2 (by rfl) ⟨530061, by rfl⟩ : syracuseStep 1413497 = 1060123) B1060123
theorem B1118695 : Blo 992597 1118695 := bstep (se 1 (by rfl) ⟨839021, by rfl⟩ : syracuseStep 1118695 = 1678043) B1678043
theorem B18125309 : Blo 992597 18125309 := bstep (se 3 (by rfl) ⟨3398495, by rfl⟩ : syracuseStep 18125309 = 6796991) B6796991
theorem B4854383 : Blo 992597 4854383 := bstep (se 1 (by rfl) ⟨3640787, by rfl⟩ : syracuseStep 4854383 = 7281575) B7281575
theorem B1676335 : Blo 992597 1676335 := bstep (se 1 (by rfl) ⟨1257251, by rfl⟩ : syracuseStep 1676335 = 2514503) B2514503
theorem B1680041 : Blo 992597 1680041 := bstep (se 2 (by rfl) ⟨630015, by rfl⟩ : syracuseStep 1680041 = 1260031) B1260031
theorem B2237723 : Blo 992597 2237723 := bstep (se 1 (by rfl) ⟨1678292, by rfl⟩ : syracuseStep 2237723 = 3356585) B3356585
theorem B2237993 : Blo 992597 2237993 := bstep (se 2 (by rfl) ⟨839247, by rfl⟩ : syracuseStep 2237993 = 1678495) B1678495
theorem B994079 : Blo 992597 994079 := bstep (se 1 (by rfl) ⟨745559, by rfl⟩ : syracuseStep 994079 = 1491119) B1491119
theorem B419835109 : Blo 992597 419835109 := bstep (se 4 (by rfl) ⟨39359541, by rfl⟩ : syracuseStep 419835109 = 78719083) B78719083
theorem B2241071 : Blo 992597 2241071 := bstep (se 1 (by rfl) ⟨1680803, by rfl⟩ : syracuseStep 2241071 = 3361607) B3361607
theorem B2241179 : Blo 992597 2241179 := bstep (se 1 (by rfl) ⟨1680884, by rfl⟩ : syracuseStep 2241179 = 3361769) B3361769
theorem B996463 : Blo 992597 996463 := bstep (se 1 (by rfl) ⟨747347, by rfl⟩ : syracuseStep 996463 = 1494695) B1494695
theorem B3359771 : Blo 992597 3359771 := bstep (se 1 (by rfl) ⟨2519828, by rfl⟩ : syracuseStep 3359771 = 5039657) B5039657
theorem B4539689 : Blo 992597 4539689 := bstep (se 2 (by rfl) ⟨1702383, by rfl⟩ : syracuseStep 4539689 = 3404767) B3404767
theorem B3360311 : Blo 992597 3360311 := bstep (se 1 (by rfl) ⟨2520233, by rfl⟩ : syracuseStep 3360311 = 5040467) B5040467
theorem B3361823 : Blo 992597 3361823 := bstep (se 1 (by rfl) ⟨2521367, by rfl⟩ : syracuseStep 3361823 = 5042735) B5042735
theorem B3363119 : Blo 992597 3363119 := bstep (se 1 (by rfl) ⟨2522339, by rfl⟩ : syracuseStep 3363119 = 5044679) B5044679
theorem B2514847 : Blo 992597 2514847 := bstep (se 1 (by rfl) ⟨1886135, by rfl⟩ : syracuseStep 2514847 = 3772271) B3772271
theorem B232714775 : Blo 992597 232714775 := bstep (se 1 (by rfl) ⟨174536081, by rfl⟩ : syracuseStep 232714775 = 349072163) B349072163
theorem B5666699 : Blo 992597 5666699 := bstep (se 1 (by rfl) ⟨4250024, by rfl⟩ : syracuseStep 5666699 = 8500049) B8500049
theorem B145260539 : Blo 992597 145260539 := bstep (se 1 (by rfl) ⟨108945404, by rfl⟩ : syracuseStep 145260539 = 217890809) B217890809
theorem B3769325 : Blo 992597 3769325 := bstep (se 3 (by rfl) ⟨706748, by rfl⟩ : syracuseStep 3769325 = 1413497) B1413497
theorem B559780145 : Blo 992597 559780145 := bstep (se 2 (by rfl) ⟨209917554, by rfl⟩ : syracuseStep 559780145 = 419835109) B419835109
theorem B1120027 : Blo 992597 1120027 := bstep (se 1 (by rfl) ⟨840020, by rfl⟩ : syracuseStep 1120027 = 1680041) B1680041
theorem B2235113 : Blo 992597 2235113 := bstep (se 2 (by rfl) ⟨838167, by rfl⟩ : syracuseStep 2235113 = 1676335) B1676335
theorem B3777799 : Blo 992597 3777799 := bstep (se 1 (by rfl) ⟨2833349, by rfl⟩ : syracuseStep 3777799 = 5666699) B5666699
theorem B3353129 : Blo 992597 3353129 := bstep (se 2 (by rfl) ⟨1257423, by rfl⟩ : syracuseStep 3353129 = 2514847) B2514847
theorem B96840359 : Blo 992597 96840359 := bstep (se 1 (by rfl) ⟨72630269, by rfl⟩ : syracuseStep 96840359 = 145260539) B145260539
theorem B2239847 : Blo 992597 2239847 := bstep (se 1 (by rfl) ⟨1679885, by rfl⟩ : syracuseStep 2239847 = 3359771) B3359771
theorem B3026459 : Blo 992597 3026459 := bstep (se 1 (by rfl) ⟨2269844, by rfl⟩ : syracuseStep 3026459 = 4539689) B4539689
theorem B2240207 : Blo 992597 2240207 := bstep (se 1 (by rfl) ⟨1680155, by rfl⟩ : syracuseStep 2240207 = 3360311) B3360311
theorem B2241215 : Blo 992597 2241215 := bstep (se 1 (by rfl) ⟨1680911, by rfl⟩ : syracuseStep 2241215 = 3361823) B3361823
theorem B2242079 : Blo 992597 2242079 := bstep (se 1 (by rfl) ⟨1681559, by rfl⟩ : syracuseStep 2242079 = 3363119) B3363119
theorem B1491593 : Blo 992597 1491593 := bstep (se 2 (by rfl) ⟨559347, by rfl⟩ : syracuseStep 1491593 = 1118695) B1118695
theorem B1491815 : Blo 992597 1491815 := bstep (se 1 (by rfl) ⟨1118861, by rfl⟩ : syracuseStep 1491815 = 2237723) B2237723
theorem B1491995 : Blo 992597 1491995 := bstep (se 1 (by rfl) ⟨1118996, by rfl⟩ : syracuseStep 1491995 = 2237993) B2237993
theorem B155143183 : Blo 992597 155143183 := bstep (se 1 (by rfl) ⟨116357387, by rfl⟩ : syracuseStep 155143183 = 232714775) B232714775
theorem B1494047 : Blo 992597 1494047 := bstep (se 1 (by rfl) ⟨1120535, by rfl⟩ : syracuseStep 1494047 = 2241071) B2241071
theorem B1494119 : Blo 992597 1494119 := bstep (se 1 (by rfl) ⟨1120589, by rfl⟩ : syracuseStep 1494119 = 2241179) B2241179
theorem B12083539 : Blo 992597 12083539 := bstep (se 1 (by rfl) ⟨9062654, by rfl⟩ : syracuseStep 12083539 = 18125309) B18125309
theorem B3236255 : Blo 992597 3236255 := bstep (se 1 (by rfl) ⟨2427191, by rfl⟩ : syracuseStep 3236255 = 4854383) B4854383
theorem B2235419 : Blo 992597 2235419 := bstep (se 1 (by rfl) ⟨1676564, by rfl⟩ : syracuseStep 2235419 = 3353129) B3353129
theorem B64560239 : Blo 992597 64560239 := bstep (se 1 (by rfl) ⟨48420179, by rfl⟩ : syracuseStep 64560239 = 96840359) B96840359
theorem B994395 : Blo 992597 994395 := bstep (se 1 (by rfl) ⟨745796, by rfl⟩ : syracuseStep 994395 = 1491593) B1491593
theorem B994543 : Blo 992597 994543 := bstep (se 1 (by rfl) ⟨745907, by rfl⟩ : syracuseStep 994543 = 1491815) B1491815
theorem B994663 : Blo 992597 994663 := bstep (se 1 (by rfl) ⟨745997, by rfl⟩ : syracuseStep 994663 = 1491995) B1491995
theorem B996031 : Blo 992597 996031 := bstep (se 1 (by rfl) ⟨747023, by rfl⟩ : syracuseStep 996031 = 1494047) B1494047
theorem B996079 : Blo 992597 996079 := bstep (se 1 (by rfl) ⟨747059, by rfl⟩ : syracuseStep 996079 = 1494119) B1494119
theorem B34520053 : Blo 992597 34520053 := bstep (se 5 (by rfl) ⟨1618127, by rfl⟩ : syracuseStep 34520053 = 3236255) B3236255
theorem B1490075 : Blo 992597 1490075 := bstep (se 1 (by rfl) ⟨1117556, by rfl⟩ : syracuseStep 1490075 = 2235113) B2235113
theorem B1493231 : Blo 992597 1493231 := bstep (se 1 (by rfl) ⟨1119923, by rfl⟩ : syracuseStep 1493231 = 2239847) B2239847
theorem B2017639 : Blo 992597 2017639 := bstep (se 1 (by rfl) ⟨1513229, by rfl⟩ : syracuseStep 2017639 = 3026459) B3026459
theorem B1493369 : Blo 992597 1493369 := bstep (se 2 (by rfl) ⟨560013, by rfl⟩ : syracuseStep 1493369 = 1120027) B1120027
theorem B1493471 : Blo 992597 1493471 := bstep (se 1 (by rfl) ⟨1120103, by rfl⟩ : syracuseStep 1493471 = 2240207) B2240207
theorem B1494143 : Blo 992597 1494143 := bstep (se 1 (by rfl) ⟨1120607, by rfl⟩ : syracuseStep 1494143 = 2241215) B2241215
theorem B1494719 : Blo 992597 1494719 := bstep (se 1 (by rfl) ⟨1121039, by rfl⟩ : syracuseStep 1494719 = 2242079) B2242079
theorem B16111385 : Blo 992597 16111385 := bstep (se 2 (by rfl) ⟨6041769, by rfl⟩ : syracuseStep 16111385 = 12083539) B12083539
theorem B2512883 : Blo 992597 2512883 := bstep (se 1 (by rfl) ⟨1884662, by rfl⟩ : syracuseStep 2512883 = 3769325) B3769325
theorem B5037065 : Blo 992597 5037065 := bstep (se 2 (by rfl) ⟨1888899, by rfl⟩ : syracuseStep 5037065 = 3777799) B3777799
theorem B373186763 : Blo 992597 373186763 := bstep (se 1 (by rfl) ⟨279890072, by rfl⟩ : syracuseStep 373186763 = 559780145) B559780145
theorem B206857577 : Blo 992597 206857577 := bstep (se 2 (by rfl) ⟨77571591, by rfl⟩ : syracuseStep 206857577 = 155143183) B155143183
theorem B2690185 : Blo 992597 2690185 := bstep (se 2 (by rfl) ⟨1008819, by rfl⟩ : syracuseStep 2690185 = 2017639) B2017639
theorem B1675255 : Blo 992597 1675255 := bstep (se 1 (by rfl) ⟨1256441, by rfl⟩ : syracuseStep 1675255 = 2512883) B2512883
theorem B993383 : Blo 992597 993383 := bstep (se 1 (by rfl) ⟨745037, by rfl⟩ : syracuseStep 993383 = 1490075) B1490075
theorem B995487 : Blo 992597 995487 := bstep (se 1 (by rfl) ⟨746615, by rfl⟩ : syracuseStep 995487 = 1493231) B1493231
theorem B995579 : Blo 992597 995579 := bstep (se 1 (by rfl) ⟨746684, by rfl⟩ : syracuseStep 995579 = 1493369) B1493369
theorem B995647 : Blo 992597 995647 := bstep (se 1 (by rfl) ⟨746735, by rfl⟩ : syracuseStep 995647 = 1493471) B1493471
theorem B996095 : Blo 992597 996095 := bstep (se 1 (by rfl) ⟨747071, by rfl⟩ : syracuseStep 996095 = 1494143) B1494143
theorem B996479 : Blo 992597 996479 := bstep (se 1 (by rfl) ⟨747359, by rfl⟩ : syracuseStep 996479 = 1494719) B1494719
theorem B3358043 : Blo 992597 3358043 := bstep (se 1 (by rfl) ⟨2518532, by rfl⟩ : syracuseStep 3358043 = 5037065) B5037065
theorem B1490279 : Blo 992597 1490279 := bstep (se 1 (by rfl) ⟨1117709, by rfl⟩ : syracuseStep 1490279 = 2235419) B2235419
theorem B43040159 : Blo 992597 43040159 := bstep (se 1 (by rfl) ⟨32280119, by rfl⟩ : syracuseStep 43040159 = 64560239) B64560239
theorem B248791175 : Blo 992597 248791175 := bstep (se 1 (by rfl) ⟨186593381, by rfl⟩ : syracuseStep 248791175 = 373186763) B373186763
theorem B137905051 : Blo 992597 137905051 := bstep (se 1 (by rfl) ⟨103428788, by rfl⟩ : syracuseStep 137905051 = 206857577) B206857577
theorem B46026737 : Blo 992597 46026737 := bstep (se 2 (by rfl) ⟨17260026, by rfl⟩ : syracuseStep 46026737 = 34520053) B34520053
theorem B10740923 : Blo 992597 10740923 := bstep (se 1 (by rfl) ⟨8055692, by rfl⟩ : syracuseStep 10740923 = 16111385) B16111385
theorem B2233673 : Blo 992597 2233673 := bstep (se 2 (by rfl) ⟨837627, by rfl⟩ : syracuseStep 2233673 = 1675255) B1675255
theorem B2238695 : Blo 992597 2238695 := bstep (se 1 (by rfl) ⟨1679021, by rfl⟩ : syracuseStep 2238695 = 3358043) B3358043
theorem B993519 : Blo 992597 993519 := bstep (se 1 (by rfl) ⟨745139, by rfl⟩ : syracuseStep 993519 = 1490279) B1490279
theorem B183873401 : Blo 992597 183873401 := bstep (se 2 (by rfl) ⟨68952525, by rfl⟩ : syracuseStep 183873401 = 137905051) B137905051
theorem B30684491 : Blo 992597 30684491 := bstep (se 1 (by rfl) ⟨23013368, by rfl⟩ : syracuseStep 30684491 = 46026737) B46026737
theorem B3586913 : Blo 992597 3586913 := bstep (se 2 (by rfl) ⟨1345092, by rfl⟩ : syracuseStep 3586913 = 2690185) B2690185
theorem B7160615 : Blo 992597 7160615 := bstep (se 1 (by rfl) ⟨5370461, by rfl⟩ : syracuseStep 7160615 = 10740923) B10740923
theorem B28693439 : Blo 992597 28693439 := bstep (se 1 (by rfl) ⟨21520079, by rfl⟩ : syracuseStep 28693439 = 43040159) B43040159
theorem B165860783 : Blo 992597 165860783 := bstep (se 1 (by rfl) ⟨124395587, by rfl⟩ : syracuseStep 165860783 = 248791175) B248791175
theorem B20456327 : Blo 992597 20456327 := bstep (se 1 (by rfl) ⟨15342245, by rfl⟩ : syracuseStep 20456327 = 30684491) B30684491
theorem B1489115 : Blo 992597 1489115 := bstep (se 1 (by rfl) ⟨1116836, by rfl⟩ : syracuseStep 1489115 = 2233673) B2233673
theorem B110573855 : Blo 992597 110573855 := bstep (se 1 (by rfl) ⟨82930391, by rfl⟩ : syracuseStep 110573855 = 165860783) B165860783
theorem B1492463 : Blo 992597 1492463 := bstep (se 1 (by rfl) ⟨1119347, by rfl⟩ : syracuseStep 1492463 = 2238695) B2238695
theorem B4773743 : Blo 992597 4773743 := bstep (se 1 (by rfl) ⟨3580307, by rfl⟩ : syracuseStep 4773743 = 7160615) B7160615
theorem B19128959 : Blo 992597 19128959 := bstep (se 1 (by rfl) ⟨14346719, by rfl⟩ : syracuseStep 19128959 = 28693439) B28693439
theorem B122582267 : Blo 992597 122582267 := bstep (se 1 (by rfl) ⟨91936700, by rfl⟩ : syracuseStep 122582267 = 183873401) B183873401
theorem B2391275 : Blo 992597 2391275 := bstep (se 1 (by rfl) ⟨1793456, by rfl⟩ : syracuseStep 2391275 = 3586913) B3586913
theorem B3182495 : Blo 992597 3182495 := bstep (se 1 (by rfl) ⟨2386871, by rfl⟩ : syracuseStep 3182495 = 4773743) B4773743
theorem B12752639 : Blo 992597 12752639 := bstep (se 1 (by rfl) ⟨9564479, by rfl⟩ : syracuseStep 12752639 = 19128959) B19128959
theorem B992743 : Blo 992597 992743 := bstep (se 1 (by rfl) ⟨744557, by rfl⟩ : syracuseStep 992743 = 1489115) B1489115
theorem B994975 : Blo 992597 994975 := bstep (se 1 (by rfl) ⟨746231, by rfl⟩ : syracuseStep 994975 = 1492463) B1492463
theorem B73715903 : Blo 992597 73715903 := bstep (se 1 (by rfl) ⟨55286927, by rfl⟩ : syracuseStep 73715903 = 110573855) B110573855
theorem B1594183 : Blo 992597 1594183 := bstep (se 1 (by rfl) ⟨1195637, by rfl⟩ : syracuseStep 1594183 = 2391275) B2391275
theorem B54550205 : Blo 992597 54550205 := bstep (se 3 (by rfl) ⟨10228163, by rfl⟩ : syracuseStep 54550205 = 20456327) B20456327
theorem B81721511 : Blo 992597 81721511 := bstep (se 1 (by rfl) ⟨61291133, by rfl⟩ : syracuseStep 81721511 = 122582267) B122582267
theorem B8501759 : Blo 992597 8501759 := bstep (se 1 (by rfl) ⟨6376319, by rfl⟩ : syracuseStep 8501759 = 12752639) B12752639
theorem B54481007 : Blo 992597 54481007 := bstep (se 1 (by rfl) ⟨40860755, by rfl⟩ : syracuseStep 54481007 = 81721511) B81721511
theorem B49143935 : Blo 992597 49143935 := bstep (se 1 (by rfl) ⟨36857951, by rfl⟩ : syracuseStep 49143935 = 73715903) B73715903
theorem B36366803 : Blo 992597 36366803 := bstep (se 1 (by rfl) ⟨27275102, by rfl⟩ : syracuseStep 36366803 = 54550205) B54550205
theorem B2125577 : Blo 992597 2125577 := bstep (se 2 (by rfl) ⟨797091, by rfl⟩ : syracuseStep 2125577 = 1594183) B1594183
theorem B8486653 : Blo 992597 8486653 := bstep (se 3 (by rfl) ⟨1591247, by rfl⟩ : syracuseStep 8486653 = 3182495) B3182495
theorem B1417051 : Blo 992597 1417051 := bstep (se 1 (by rfl) ⟨1062788, by rfl⟩ : syracuseStep 1417051 = 2125577) B2125577
theorem B11315537 : Blo 992597 11315537 := bstep (se 2 (by rfl) ⟨4243326, by rfl⟩ : syracuseStep 11315537 = 8486653) B8486653
theorem B131050493 : Blo 992597 131050493 := bstep (se 3 (by rfl) ⟨24571967, by rfl⟩ : syracuseStep 131050493 = 49143935) B49143935
theorem B36320671 : Blo 992597 36320671 := bstep (se 1 (by rfl) ⟨27240503, by rfl⟩ : syracuseStep 36320671 = 54481007) B54481007
theorem B24244535 : Blo 992597 24244535 := bstep (se 1 (by rfl) ⟨18183401, by rfl⟩ : syracuseStep 24244535 = 36366803) B36366803
theorem B5667839 : Blo 992597 5667839 := bstep (se 1 (by rfl) ⟨4250879, by rfl⟩ : syracuseStep 5667839 = 8501759) B8501759
theorem B64652093 : Blo 992597 64652093 := bstep (se 3 (by rfl) ⟨12122267, by rfl⟩ : syracuseStep 64652093 = 24244535) B24244535
theorem B7543691 : Blo 992597 7543691 := bstep (se 1 (by rfl) ⟨5657768, by rfl⟩ : syracuseStep 7543691 = 11315537) B11315537
theorem B87366995 : Blo 992597 87366995 := bstep (se 1 (by rfl) ⟨65525246, by rfl⟩ : syracuseStep 87366995 = 131050493) B131050493
theorem B3778559 : Blo 992597 3778559 := bstep (se 1 (by rfl) ⟨2833919, by rfl⟩ : syracuseStep 3778559 = 5667839) B5667839
theorem B1889401 : Blo 992597 1889401 := bstep (se 2 (by rfl) ⟨708525, by rfl⟩ : syracuseStep 1889401 = 1417051) B1417051
theorem B48427561 : Blo 992597 48427561 := bstep (se 2 (by rfl) ⟨18160335, by rfl⟩ : syracuseStep 48427561 = 36320671) B36320671
theorem B43101395 : Blo 992597 43101395 := bstep (se 1 (by rfl) ⟨32326046, by rfl⟩ : syracuseStep 43101395 = 64652093) B64652093
theorem B5029127 : Blo 992597 5029127 := bstep (se 1 (by rfl) ⟨3771845, by rfl⟩ : syracuseStep 5029127 = 7543691) B7543691
theorem B58244663 : Blo 992597 58244663 := bstep (se 1 (by rfl) ⟨43683497, by rfl⟩ : syracuseStep 58244663 = 87366995) B87366995
theorem B64570081 : Blo 992597 64570081 := bstep (se 2 (by rfl) ⟨24213780, by rfl⟩ : syracuseStep 64570081 = 48427561) B48427561
theorem B2519039 : Blo 992597 2519039 := bstep (se 1 (by rfl) ⟨1889279, by rfl⟩ : syracuseStep 2519039 = 3778559) B3778559
theorem B2519201 : Blo 992597 2519201 := bstep (se 2 (by rfl) ⟨944700, by rfl⟩ : syracuseStep 2519201 = 1889401) B1889401
theorem B1679359 : Blo 992597 1679359 := bstep (se 1 (by rfl) ⟨1259519, by rfl⟩ : syracuseStep 1679359 = 2519039) B2519039
theorem B1679467 : Blo 992597 1679467 := bstep (se 1 (by rfl) ⟨1259600, by rfl⟩ : syracuseStep 1679467 = 2519201) B2519201
theorem B3352751 : Blo 992597 3352751 := bstep (se 1 (by rfl) ⟨2514563, by rfl⟩ : syracuseStep 3352751 = 5029127) B5029127
theorem B86093441 : Blo 992597 86093441 := bstep (se 2 (by rfl) ⟨32285040, by rfl⟩ : syracuseStep 86093441 = 64570081) B64570081
theorem B28734263 : Blo 992597 28734263 := bstep (se 1 (by rfl) ⟨21550697, by rfl⟩ : syracuseStep 28734263 = 43101395) B43101395
theorem B38829775 : Blo 992597 38829775 := bstep (se 1 (by rfl) ⟨29122331, by rfl⟩ : syracuseStep 38829775 = 58244663) B58244663
theorem B2235167 : Blo 992597 2235167 := bstep (se 1 (by rfl) ⟨1676375, by rfl⟩ : syracuseStep 2235167 = 3352751) B3352751
theorem B2239145 : Blo 992597 2239145 := bstep (se 2 (by rfl) ⟨839679, by rfl⟩ : syracuseStep 2239145 = 1679359) B1679359
theorem B2239289 : Blo 992597 2239289 := bstep (se 2 (by rfl) ⟨839733, by rfl⟩ : syracuseStep 2239289 = 1679467) B1679467
theorem B57395627 : Blo 992597 57395627 := bstep (se 1 (by rfl) ⟨43046720, by rfl⟩ : syracuseStep 57395627 = 86093441) B86093441
theorem B19156175 : Blo 992597 19156175 := bstep (se 1 (by rfl) ⟨14367131, by rfl⟩ : syracuseStep 19156175 = 28734263) B28734263
theorem B51773033 : Blo 992597 51773033 := bstep (se 2 (by rfl) ⟨19414887, by rfl⟩ : syracuseStep 51773033 = 38829775) B38829775
theorem B34515355 : Blo 992597 34515355 := bstep (se 1 (by rfl) ⟨25886516, by rfl⟩ : syracuseStep 34515355 = 51773033) B51773033
theorem B1490111 : Blo 992597 1490111 := bstep (se 1 (by rfl) ⟨1117583, by rfl⟩ : syracuseStep 1490111 = 2235167) B2235167
theorem B1492763 : Blo 992597 1492763 := bstep (se 1 (by rfl) ⟨1119572, by rfl⟩ : syracuseStep 1492763 = 2239145) B2239145
theorem B1492859 : Blo 992597 1492859 := bstep (se 1 (by rfl) ⟨1119644, by rfl⟩ : syracuseStep 1492859 = 2239289) B2239289
theorem B38263751 : Blo 992597 38263751 := bstep (se 1 (by rfl) ⟨28697813, by rfl⟩ : syracuseStep 38263751 = 57395627) B57395627
theorem B12770783 : Blo 992597 12770783 := bstep (se 1 (by rfl) ⟨9578087, by rfl⟩ : syracuseStep 12770783 = 19156175) B19156175
theorem B993407 : Blo 992597 993407 := bstep (se 1 (by rfl) ⟨745055, by rfl⟩ : syracuseStep 993407 = 1490111) B1490111
theorem B995175 : Blo 992597 995175 := bstep (se 1 (by rfl) ⟨746381, by rfl⟩ : syracuseStep 995175 = 1492763) B1492763
theorem B995239 : Blo 992597 995239 := bstep (se 1 (by rfl) ⟨746429, by rfl⟩ : syracuseStep 995239 = 1492859) B1492859
theorem B46020473 : Blo 992597 46020473 := bstep (se 2 (by rfl) ⟨17257677, by rfl⟩ : syracuseStep 46020473 = 34515355) B34515355
theorem B25509167 : Blo 992597 25509167 := bstep (se 1 (by rfl) ⟨19131875, by rfl⟩ : syracuseStep 25509167 = 38263751) B38263751
theorem B8513855 : Blo 992597 8513855 := bstep (se 1 (by rfl) ⟨6385391, by rfl⟩ : syracuseStep 8513855 = 12770783) B12770783
theorem B5675903 : Blo 992597 5675903 := bstep (se 1 (by rfl) ⟨4256927, by rfl⟩ : syracuseStep 5675903 = 8513855) B8513855
theorem B30680315 : Blo 992597 30680315 := bstep (se 1 (by rfl) ⟨23010236, by rfl⟩ : syracuseStep 30680315 = 46020473) B46020473
theorem B17006111 : Blo 992597 17006111 := bstep (se 1 (by rfl) ⟨12754583, by rfl⟩ : syracuseStep 17006111 = 25509167) B25509167
theorem B20453543 : Blo 992597 20453543 := bstep (se 1 (by rfl) ⟨15340157, by rfl⟩ : syracuseStep 20453543 = 30680315) B30680315
theorem B3783935 : Blo 992597 3783935 := bstep (se 1 (by rfl) ⟨2837951, by rfl⟩ : syracuseStep 3783935 = 5675903) B5675903
theorem B11337407 : Blo 992597 11337407 := bstep (se 1 (by rfl) ⟨8503055, by rfl⟩ : syracuseStep 11337407 = 17006111) B17006111
theorem B13635695 : Blo 992597 13635695 := bstep (se 1 (by rfl) ⟨10226771, by rfl⟩ : syracuseStep 13635695 = 20453543) B20453543
theorem B7558271 : Blo 992597 7558271 := bstep (se 1 (by rfl) ⟨5668703, by rfl⟩ : syracuseStep 7558271 = 11337407) B11337407
theorem B2522623 : Blo 992597 2522623 := bstep (se 1 (by rfl) ⟨1891967, by rfl⟩ : syracuseStep 2522623 = 3783935) B3783935
theorem B9090463 : Blo 992597 9090463 := bstep (se 1 (by rfl) ⟨6817847, by rfl⟩ : syracuseStep 9090463 = 13635695) B13635695
theorem B3363497 : Blo 992597 3363497 := bstep (se 2 (by rfl) ⟨1261311, by rfl⟩ : syracuseStep 3363497 = 2522623) B2522623
theorem B5038847 : Blo 992597 5038847 := bstep (se 1 (by rfl) ⟨3779135, by rfl⟩ : syracuseStep 5038847 = 7558271) B7558271
theorem B2242331 : Blo 992597 2242331 := bstep (se 1 (by rfl) ⟨1681748, by rfl⟩ : syracuseStep 2242331 = 3363497) B3363497
theorem B3359231 : Blo 992597 3359231 := bstep (se 1 (by rfl) ⟨2519423, by rfl⟩ : syracuseStep 3359231 = 5038847) B5038847
theorem B12120617 : Blo 992597 12120617 := bstep (se 2 (by rfl) ⟨4545231, by rfl⟩ : syracuseStep 12120617 = 9090463) B9090463
theorem B2239487 : Blo 992597 2239487 := bstep (se 1 (by rfl) ⟨1679615, by rfl⟩ : syracuseStep 2239487 = 3359231) B3359231
theorem B8080411 : Blo 992597 8080411 := bstep (se 1 (by rfl) ⟨6060308, by rfl⟩ : syracuseStep 8080411 = 12120617) B12120617
theorem B1494887 : Blo 992597 1494887 := bstep (se 1 (by rfl) ⟨1121165, by rfl⟩ : syracuseStep 1494887 = 2242331) B2242331
theorem B996591 : Blo 992597 996591 := bstep (se 1 (by rfl) ⟨747443, by rfl⟩ : syracuseStep 996591 = 1494887) B1494887
theorem B1492991 : Blo 992597 1492991 := bstep (se 1 (by rfl) ⟨1119743, by rfl⟩ : syracuseStep 1492991 = 2239487) B2239487
theorem B10773881 : Blo 992597 10773881 := bstep (se 2 (by rfl) ⟨4040205, by rfl⟩ : syracuseStep 10773881 = 8080411) B8080411
theorem B7182587 : Blo 992597 7182587 := bstep (se 1 (by rfl) ⟨5386940, by rfl⟩ : syracuseStep 7182587 = 10773881) B10773881
theorem B995327 : Blo 992597 995327 := bstep (se 1 (by rfl) ⟨746495, by rfl⟩ : syracuseStep 995327 = 1492991) B1492991
theorem B4788391 : Blo 992597 4788391 := bstep (se 1 (by rfl) ⟨3591293, by rfl⟩ : syracuseStep 4788391 = 7182587) B7182587
theorem B6384521 : Blo 992597 6384521 := bstep (se 2 (by rfl) ⟨2394195, by rfl⟩ : syracuseStep 6384521 = 4788391) B4788391
theorem B4256347 : Blo 992597 4256347 := bstep (se 1 (by rfl) ⟨3192260, by rfl⟩ : syracuseStep 4256347 = 6384521) B6384521
theorem B5675129 : Blo 992597 5675129 := bstep (se 2 (by rfl) ⟨2128173, by rfl⟩ : syracuseStep 5675129 = 4256347) B4256347
theorem B3783419 : Blo 992597 3783419 := bstep (se 1 (by rfl) ⟨2837564, by rfl⟩ : syracuseStep 3783419 = 5675129) B5675129
theorem B2522279 : Blo 992597 2522279 := bstep (se 1 (by rfl) ⟨1891709, by rfl⟩ : syracuseStep 2522279 = 3783419) B3783419
theorem B1681519 : Blo 992597 1681519 := bstep (se 1 (by rfl) ⟨1261139, by rfl⟩ : syracuseStep 1681519 = 2522279) B2522279
theorem B2242025 : Blo 992597 2242025 := bstep (se 2 (by rfl) ⟨840759, by rfl⟩ : syracuseStep 2242025 = 1681519) B1681519
theorem B1494683 : Blo 992597 1494683 := bstep (se 1 (by rfl) ⟨1121012, by rfl⟩ : syracuseStep 1494683 = 2242025) B2242025
theorem B996455 : Blo 992597 996455 := bstep (se 1 (by rfl) ⟨747341, by rfl⟩ : syracuseStep 996455 = 1494683) B1494683

theorem C0 (j : ℕ) (h1 : 248149 ≤ j) (h2 : j ≤ 248848) : Blo 992597 (4 * j + 3) := by
  interval_cases j
  · exact B992599
  · exact B992603
  · exact B992607
  · exact B992611
  · exact B992615
  · exact B992619
  · exact B992623
  · exact B992627
  · exact B992631
  · exact B992635
  · exact B992639
  · exact B992643
  · exact B992647
  · exact B992651
  · exact B992655
  · exact B992659
  · exact B992663
  · exact B992667
  · exact B992671
  · exact B992675
  · exact B992679
  · exact B992683
  · exact B992687
  · exact B992691
  · exact B992695
  · exact B992699
  · exact B992703
  · exact B992707
  · exact B992711
  · exact B992715
  · exact B992719
  · exact B992723
  · exact B992727
  · exact B992731
  · exact B992735
  · exact B992739
  · exact B992743
  · exact B992747
  · exact B992751
  · exact B992755
  · exact B992759
  · exact B992763
  · exact B992767
  · exact B992771
  · exact B992775
  · exact B992779
  · exact B992783
  · exact B992787
  · exact B992791
  · exact B992795
  · exact B992799
  · exact B992803
  · exact B992807
  · exact B992811
  · exact B992815
  · exact B992819
  · exact B992823
  · exact B992827
  · exact B992831
  · exact B992835
  · exact B992839
  · exact B992843
  · exact B992847
  · exact B992851
  · exact B992855
  · exact B992859
  · exact B992863
  · exact B992867
  · exact B992871
  · exact B992875
  · exact B992879
  · exact B992883
  · exact B992887
  · exact B992891
  · exact B992895
  · exact B992899
  · exact B992903
  · exact B992907
  · exact B992911
  · exact B992915
  · exact B992919
  · exact B992923
  · exact B992927
  · exact B992931
  · exact B992935
  · exact B992939
  · exact B992943
  · exact B992947
  · exact B992951
  · exact B992955
  · exact B992959
  · exact B992963
  · exact B992967
  · exact B992971
  · exact B992975
  · exact B992979
  · exact B992983
  · exact B992987
  · exact B992991
  · exact B992995
  · exact B992999
  · exact B993003
  · exact B993007
  · exact B993011
  · exact B993015
  · exact B993019
  · exact B993023
  · exact B993027
  · exact B993031
  · exact B993035
  · exact B993039
  · exact B993043
  · exact B993047
  · exact B993051
  · exact B993055
  · exact B993059
  · exact B993063
  · exact B993067
  · exact B993071
  · exact B993075
  · exact B993079
  · exact B993083
  · exact B993087
  · exact B993091
  · exact B993095
  · exact B993099
  · exact B993103
  · exact B993107
  · exact B993111
  · exact B993115
  · exact B993119
  · exact B993123
  · exact B993127
  · exact B993131
  · exact B993135
  · exact B993139
  · exact B993143
  · exact B993147
  · exact B993151
  · exact B993155
  · exact B993159
  · exact B993163
  · exact B993167
  · exact B993171
  · exact B993175
  · exact B993179
  · exact B993183
  · exact B993187
  · exact B993191
  · exact B993195
  · exact B993199
  · exact B993203
  · exact B993207
  · exact B993211
  · exact B993215
  · exact B993219
  · exact B993223
  · exact B993227
  · exact B993231
  · exact B993235
  · exact B993239
  · exact B993243
  · exact B993247
  · exact B993251
  · exact B993255
  · exact B993259
  · exact B993263
  · exact B993267
  · exact B993271
  · exact B993275
  · exact B993279
  · exact B993283
  · exact B993287
  · exact B993291
  · exact B993295
  · exact B993299
  · exact B993303
  · exact B993307
  · exact B993311
  · exact B993315
  · exact B993319
  · exact B993323
  · exact B993327
  · exact B993331
  · exact B993335
  · exact B993339
  · exact B993343
  · exact B993347
  · exact B993351
  · exact B993355
  · exact B993359
  · exact B993363
  · exact B993367
  · exact B993371
  · exact B993375
  · exact B993379
  · exact B993383
  · exact B993387
  · exact B993391
  · exact B993395
  · exact B993399
  · exact B993403
  · exact B993407
  · exact B993411
  · exact B993415
  · exact B993419
  · exact B993423
  · exact B993427
  · exact B993431
  · exact B993435
  · exact B993439
  · exact B993443
  · exact B993447
  · exact B993451
  · exact B993455
  · exact B993459
  · exact B993463
  · exact B993467
  · exact B993471
  · exact B993475
  · exact B993479
  · exact B993483
  · exact B993487
  · exact B993491
  · exact B993495
  · exact B993499
  · exact B993503
  · exact B993507
  · exact B993511
  · exact B993515
  · exact B993519
  · exact B993523
  · exact B993527
  · exact B993531
  · exact B993535
  · exact B993539
  · exact B993543
  · exact B993547
  · exact B993551
  · exact B993555
  · exact B993559
  · exact B993563
  · exact B993567
  · exact B993571
  · exact B993575
  · exact B993579
  · exact B993583
  · exact B993587
  · exact B993591
  · exact B993595
  · exact B993599
  · exact B993603
  · exact B993607
  · exact B993611
  · exact B993615
  · exact B993619
  · exact B993623
  · exact B993627
  · exact B993631
  · exact B993635
  · exact B993639
  · exact B993643
  · exact B993647
  · exact B993651
  · exact B993655
  · exact B993659
  · exact B993663
  · exact B993667
  · exact B993671
  · exact B993675
  · exact B993679
  · exact B993683
  · exact B993687
  · exact B993691
  · exact B993695
  · exact B993699
  · exact B993703
  · exact B993707
  · exact B993711
  · exact B993715
  · exact B993719
  · exact B993723
  · exact B993727
  · exact B993731
  · exact B993735
  · exact B993739
  · exact B993743
  · exact B993747
  · exact B993751
  · exact B993755
  · exact B993759
  · exact B993763
  · exact B993767
  · exact B993771
  · exact B993775
  · exact B993779
  · exact B993783
  · exact B993787
  · exact B993791
  · exact B993795
  · exact B993799
  · exact B993803
  · exact B993807
  · exact B993811
  · exact B993815
  · exact B993819
  · exact B993823
  · exact B993827
  · exact B993831
  · exact B993835
  · exact B993839
  · exact B993843
  · exact B993847
  · exact B993851
  · exact B993855
  · exact B993859
  · exact B993863
  · exact B993867
  · exact B993871
  · exact B993875
  · exact B993879
  · exact B993883
  · exact B993887
  · exact B993891
  · exact B993895
  · exact B993899
  · exact B993903
  · exact B993907
  · exact B993911
  · exact B993915
  · exact B993919
  · exact B993923
  · exact B993927
  · exact B993931
  · exact B993935
  · exact B993939
  · exact B993943
  · exact B993947
  · exact B993951
  · exact B993955
  · exact B993959
  · exact B993963
  · exact B993967
  · exact B993971
  · exact B993975
  · exact B993979
  · exact B993983
  · exact B993987
  · exact B993991
  · exact B993995
  · exact B993999
  · exact B994003
  · exact B994007
  · exact B994011
  · exact B994015
  · exact B994019
  · exact B994023
  · exact B994027
  · exact B994031
  · exact B994035
  · exact B994039
  · exact B994043
  · exact B994047
  · exact B994051
  · exact B994055
  · exact B994059
  · exact B994063
  · exact B994067
  · exact B994071
  · exact B994075
  · exact B994079
  · exact B994083
  · exact B994087
  · exact B994091
  · exact B994095
  · exact B994099
  · exact B994103
  · exact B994107
  · exact B994111
  · exact B994115
  · exact B994119
  · exact B994123
  · exact B994127
  · exact B994131
  · exact B994135
  · exact B994139
  · exact B994143
  · exact B994147
  · exact B994151
  · exact B994155
  · exact B994159
  · exact B994163
  · exact B994167
  · exact B994171
  · exact B994175
  · exact B994179
  · exact B994183
  · exact B994187
  · exact B994191
  · exact B994195
  · exact B994199
  · exact B994203
  · exact B994207
  · exact B994211
  · exact B994215
  · exact B994219
  · exact B994223
  · exact B994227
  · exact B994231
  · exact B994235
  · exact B994239
  · exact B994243
  · exact B994247
  · exact B994251
  · exact B994255
  · exact B994259
  · exact B994263
  · exact B994267
  · exact B994271
  · exact B994275
  · exact B994279
  · exact B994283
  · exact B994287
  · exact B994291
  · exact B994295
  · exact B994299
  · exact B994303
  · exact B994307
  · exact B994311
  · exact B994315
  · exact B994319
  · exact B994323
  · exact B994327
  · exact B994331
  · exact B994335
  · exact B994339
  · exact B994343
  · exact B994347
  · exact B994351
  · exact B994355
  · exact B994359
  · exact B994363
  · exact B994367
  · exact B994371
  · exact B994375
  · exact B994379
  · exact B994383
  · exact B994387
  · exact B994391
  · exact B994395
  · exact B994399
  · exact B994403
  · exact B994407
  · exact B994411
  · exact B994415
  · exact B994419
  · exact B994423
  · exact B994427
  · exact B994431
  · exact B994435
  · exact B994439
  · exact B994443
  · exact B994447
  · exact B994451
  · exact B994455
  · exact B994459
  · exact B994463
  · exact B994467
  · exact B994471
  · exact B994475
  · exact B994479
  · exact B994483
  · exact B994487
  · exact B994491
  · exact B994495
  · exact B994499
  · exact B994503
  · exact B994507
  · exact B994511
  · exact B994515
  · exact B994519
  · exact B994523
  · exact B994527
  · exact B994531
  · exact B994535
  · exact B994539
  · exact B994543
  · exact B994547
  · exact B994551
  · exact B994555
  · exact B994559
  · exact B994563
  · exact B994567
  · exact B994571
  · exact B994575
  · exact B994579
  · exact B994583
  · exact B994587
  · exact B994591
  · exact B994595
  · exact B994599
  · exact B994603
  · exact B994607
  · exact B994611
  · exact B994615
  · exact B994619
  · exact B994623
  · exact B994627
  · exact B994631
  · exact B994635
  · exact B994639
  · exact B994643
  · exact B994647
  · exact B994651
  · exact B994655
  · exact B994659
  · exact B994663
  · exact B994667
  · exact B994671
  · exact B994675
  · exact B994679
  · exact B994683
  · exact B994687
  · exact B994691
  · exact B994695
  · exact B994699
  · exact B994703
  · exact B994707
  · exact B994711
  · exact B994715
  · exact B994719
  · exact B994723
  · exact B994727
  · exact B994731
  · exact B994735
  · exact B994739
  · exact B994743
  · exact B994747
  · exact B994751
  · exact B994755
  · exact B994759
  · exact B994763
  · exact B994767
  · exact B994771
  · exact B994775
  · exact B994779
  · exact B994783
  · exact B994787
  · exact B994791
  · exact B994795
  · exact B994799
  · exact B994803
  · exact B994807
  · exact B994811
  · exact B994815
  · exact B994819
  · exact B994823
  · exact B994827
  · exact B994831
  · exact B994835
  · exact B994839
  · exact B994843
  · exact B994847
  · exact B994851
  · exact B994855
  · exact B994859
  · exact B994863
  · exact B994867
  · exact B994871
  · exact B994875
  · exact B994879
  · exact B994883
  · exact B994887
  · exact B994891
  · exact B994895
  · exact B994899
  · exact B994903
  · exact B994907
  · exact B994911
  · exact B994915
  · exact B994919
  · exact B994923
  · exact B994927
  · exact B994931
  · exact B994935
  · exact B994939
  · exact B994943
  · exact B994947
  · exact B994951
  · exact B994955
  · exact B994959
  · exact B994963
  · exact B994967
  · exact B994971
  · exact B994975
  · exact B994979
  · exact B994983
  · exact B994987
  · exact B994991
  · exact B994995
  · exact B994999
  · exact B995003
  · exact B995007
  · exact B995011
  · exact B995015
  · exact B995019
  · exact B995023
  · exact B995027
  · exact B995031
  · exact B995035
  · exact B995039
  · exact B995043
  · exact B995047
  · exact B995051
  · exact B995055
  · exact B995059
  · exact B995063
  · exact B995067
  · exact B995071
  · exact B995075
  · exact B995079
  · exact B995083
  · exact B995087
  · exact B995091
  · exact B995095
  · exact B995099
  · exact B995103
  · exact B995107
  · exact B995111
  · exact B995115
  · exact B995119
  · exact B995123
  · exact B995127
  · exact B995131
  · exact B995135
  · exact B995139
  · exact B995143
  · exact B995147
  · exact B995151
  · exact B995155
  · exact B995159
  · exact B995163
  · exact B995167
  · exact B995171
  · exact B995175
  · exact B995179
  · exact B995183
  · exact B995187
  · exact B995191
  · exact B995195
  · exact B995199
  · exact B995203
  · exact B995207
  · exact B995211
  · exact B995215
  · exact B995219
  · exact B995223
  · exact B995227
  · exact B995231
  · exact B995235
  · exact B995239
  · exact B995243
  · exact B995247
  · exact B995251
  · exact B995255
  · exact B995259
  · exact B995263
  · exact B995267
  · exact B995271
  · exact B995275
  · exact B995279
  · exact B995283
  · exact B995287
  · exact B995291
  · exact B995295
  · exact B995299
  · exact B995303
  · exact B995307
  · exact B995311
  · exact B995315
  · exact B995319
  · exact B995323
  · exact B995327
  · exact B995331
  · exact B995335
  · exact B995339
  · exact B995343
  · exact B995347
  · exact B995351
  · exact B995355
  · exact B995359
  · exact B995363
  · exact B995367
  · exact B995371
  · exact B995375
  · exact B995379
  · exact B995383
  · exact B995387
  · exact B995391
  · exact B995395

theorem C1 (j : ℕ) (h1 : 248849 ≤ j) (h2 : j ≤ 249148) : Blo 992597 (4 * j + 3) := by
  interval_cases j
  · exact B995399
  · exact B995403
  · exact B995407
  · exact B995411
  · exact B995415
  · exact B995419
  · exact B995423
  · exact B995427
  · exact B995431
  · exact B995435
  · exact B995439
  · exact B995443
  · exact B995447
  · exact B995451
  · exact B995455
  · exact B995459
  · exact B995463
  · exact B995467
  · exact B995471
  · exact B995475
  · exact B995479
  · exact B995483
  · exact B995487
  · exact B995491
  · exact B995495
  · exact B995499
  · exact B995503
  · exact B995507
  · exact B995511
  · exact B995515
  · exact B995519
  · exact B995523
  · exact B995527
  · exact B995531
  · exact B995535
  · exact B995539
  · exact B995543
  · exact B995547
  · exact B995551
  · exact B995555
  · exact B995559
  · exact B995563
  · exact B995567
  · exact B995571
  · exact B995575
  · exact B995579
  · exact B995583
  · exact B995587
  · exact B995591
  · exact B995595
  · exact B995599
  · exact B995603
  · exact B995607
  · exact B995611
  · exact B995615
  · exact B995619
  · exact B995623
  · exact B995627
  · exact B995631
  · exact B995635
  · exact B995639
  · exact B995643
  · exact B995647
  · exact B995651
  · exact B995655
  · exact B995659
  · exact B995663
  · exact B995667
  · exact B995671
  · exact B995675
  · exact B995679
  · exact B995683
  · exact B995687
  · exact B995691
  · exact B995695
  · exact B995699
  · exact B995703
  · exact B995707
  · exact B995711
  · exact B995715
  · exact B995719
  · exact B995723
  · exact B995727
  · exact B995731
  · exact B995735
  · exact B995739
  · exact B995743
  · exact B995747
  · exact B995751
  · exact B995755
  · exact B995759
  · exact B995763
  · exact B995767
  · exact B995771
  · exact B995775
  · exact B995779
  · exact B995783
  · exact B995787
  · exact B995791
  · exact B995795
  · exact B995799
  · exact B995803
  · exact B995807
  · exact B995811
  · exact B995815
  · exact B995819
  · exact B995823
  · exact B995827
  · exact B995831
  · exact B995835
  · exact B995839
  · exact B995843
  · exact B995847
  · exact B995851
  · exact B995855
  · exact B995859
  · exact B995863
  · exact B995867
  · exact B995871
  · exact B995875
  · exact B995879
  · exact B995883
  · exact B995887
  · exact B995891
  · exact B995895
  · exact B995899
  · exact B995903
  · exact B995907
  · exact B995911
  · exact B995915
  · exact B995919
  · exact B995923
  · exact B995927
  · exact B995931
  · exact B995935
  · exact B995939
  · exact B995943
  · exact B995947
  · exact B995951
  · exact B995955
  · exact B995959
  · exact B995963
  · exact B995967
  · exact B995971
  · exact B995975
  · exact B995979
  · exact B995983
  · exact B995987
  · exact B995991
  · exact B995995
  · exact B995999
  · exact B996003
  · exact B996007
  · exact B996011
  · exact B996015
  · exact B996019
  · exact B996023
  · exact B996027
  · exact B996031
  · exact B996035
  · exact B996039
  · exact B996043
  · exact B996047
  · exact B996051
  · exact B996055
  · exact B996059
  · exact B996063
  · exact B996067
  · exact B996071
  · exact B996075
  · exact B996079
  · exact B996083
  · exact B996087
  · exact B996091
  · exact B996095
  · exact B996099
  · exact B996103
  · exact B996107
  · exact B996111
  · exact B996115
  · exact B996119
  · exact B996123
  · exact B996127
  · exact B996131
  · exact B996135
  · exact B996139
  · exact B996143
  · exact B996147
  · exact B996151
  · exact B996155
  · exact B996159
  · exact B996163
  · exact B996167
  · exact B996171
  · exact B996175
  · exact B996179
  · exact B996183
  · exact B996187
  · exact B996191
  · exact B996195
  · exact B996199
  · exact B996203
  · exact B996207
  · exact B996211
  · exact B996215
  · exact B996219
  · exact B996223
  · exact B996227
  · exact B996231
  · exact B996235
  · exact B996239
  · exact B996243
  · exact B996247
  · exact B996251
  · exact B996255
  · exact B996259
  · exact B996263
  · exact B996267
  · exact B996271
  · exact B996275
  · exact B996279
  · exact B996283
  · exact B996287
  · exact B996291
  · exact B996295
  · exact B996299
  · exact B996303
  · exact B996307
  · exact B996311
  · exact B996315
  · exact B996319
  · exact B996323
  · exact B996327
  · exact B996331
  · exact B996335
  · exact B996339
  · exact B996343
  · exact B996347
  · exact B996351
  · exact B996355
  · exact B996359
  · exact B996363
  · exact B996367
  · exact B996371
  · exact B996375
  · exact B996379
  · exact B996383
  · exact B996387
  · exact B996391
  · exact B996395
  · exact B996399
  · exact B996403
  · exact B996407
  · exact B996411
  · exact B996415
  · exact B996419
  · exact B996423
  · exact B996427
  · exact B996431
  · exact B996435
  · exact B996439
  · exact B996443
  · exact B996447
  · exact B996451
  · exact B996455
  · exact B996459
  · exact B996463
  · exact B996467
  · exact B996471
  · exact B996475
  · exact B996479
  · exact B996483
  · exact B996487
  · exact B996491
  · exact B996495
  · exact B996499
  · exact B996503
  · exact B996507
  · exact B996511
  · exact B996515
  · exact B996519
  · exact B996523
  · exact B996527
  · exact B996531
  · exact B996535
  · exact B996539
  · exact B996543
  · exact B996547
  · exact B996551
  · exact B996555
  · exact B996559
  · exact B996563
  · exact B996567
  · exact B996571
  · exact B996575
  · exact B996579
  · exact B996583
  · exact B996587
  · exact B996591
  · exact B996595

theorem solution (m : ℕ) (hlo : 992597 ≤ m) (hhi : m ≤ 996597) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 248149 ≤ j := by omega
    have hj2 : j ≤ 249148 := by omega
    have hb : Blo 992597 (4 * j + 3) := by
      rcases Nat.lt_or_ge j 248849 with hc0 | hc0
      · exact C0 j (by omega) (by omega)
      exact C1 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
