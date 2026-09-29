-- Prove2me | solution 1 for syracuse_descends_range_527800_531800
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-09T17:48:27.475023+00:00
-- url     : https://prove2.me/submissions/ac153958-fdf3-4e58-8a91-dbcdca476e82

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


theorem B753781 : Blo 527800 753781 := bbase (se 5 (by rfl) ⟨35333, by rfl⟩ : syracuseStep 753781 = 70667) (by norm_num)
theorem B2687093 : Blo 527800 2687093 := bbase (se 5 (by rfl) ⟨125957, by rfl⟩ : syracuseStep 2687093 = 251915) (by norm_num)
theorem B2031797 : Blo 527800 2031797 := bbase (se 5 (by rfl) ⟨95240, by rfl⟩ : syracuseStep 2031797 = 190481) (by norm_num)
theorem B753877 : Blo 527800 753877 := bbase (se 7 (by rfl) ⟨8834, by rfl⟩ : syracuseStep 753877 = 17669) (by norm_num)
theorem B1343749 : Blo 527800 1343749 := bbase (se 4 (by rfl) ⟨125976, by rfl⟩ : syracuseStep 1343749 = 251953) (by norm_num)
theorem B1343861 : Blo 527800 1343861 := bbase (se 5 (by rfl) ⟨62993, by rfl⟩ : syracuseStep 1343861 = 125987) (by norm_num)
theorem B2425349 : Blo 527800 2425349 := bbase (se 4 (by rfl) ⟨227376, by rfl⟩ : syracuseStep 2425349 = 454753) (by norm_num)
theorem B1344053 : Blo 527800 1344053 := bbase (se 5 (by rfl) ⟨63002, by rfl⟩ : syracuseStep 1344053 = 126005) (by norm_num)
theorem B688753 : Blo 527800 688753 := bbase (se 2 (by rfl) ⟨258282, by rfl⟩ : syracuseStep 688753 = 516565) (by norm_num)
theorem B1016477 : Blo 527800 1016477 := bbase (se 3 (by rfl) ⟨190589, by rfl⟩ : syracuseStep 1016477 = 381179) (by norm_num)
theorem B754373 : Blo 527800 754373 := bbase (se 4 (by rfl) ⟨70722, by rfl⟩ : syracuseStep 754373 = 141445) (by norm_num)
theorem B1737509 : Blo 527800 1737509 := bbase (se 4 (by rfl) ⟨162891, by rfl⟩ : syracuseStep 1737509 = 325783) (by norm_num)
theorem B1508165 : Blo 527800 1508165 := bbase (se 4 (by rfl) ⟨141390, by rfl⟩ : syracuseStep 1508165 = 282781) (by norm_num)
theorem B1344397 : Blo 527800 1344397 := bbase (se 3 (by rfl) ⟨252074, by rfl⟩ : syracuseStep 1344397 = 504149) (by norm_num)
theorem B1344509 : Blo 527800 1344509 := bbase (se 3 (by rfl) ⟨252095, by rfl⟩ : syracuseStep 1344509 = 504191) (by norm_num)
theorem B951301 : Blo 527800 951301 := bbase (se 4 (by rfl) ⟨89184, by rfl⟩ : syracuseStep 951301 = 178369) (by norm_num)
theorem B1344701 : Blo 527800 1344701 := bbase (se 3 (by rfl) ⟨252131, by rfl⟩ : syracuseStep 1344701 = 504263) (by norm_num)
theorem B754925 : Blo 527800 754925 := bbase (se 3 (by rfl) ⟨141548, by rfl⟩ : syracuseStep 754925 = 283097) (by norm_num)
theorem B951589 : Blo 527800 951589 := bbase (se 4 (by rfl) ⟨89211, by rfl⟩ : syracuseStep 951589 = 178423) (by norm_num)
theorem B2295125 : Blo 527800 2295125 := bbase (se 12 (by rfl) ⟨840, by rfl⟩ : syracuseStep 2295125 = 1681) (by norm_num)
theorem B2688389 : Blo 527800 2688389 := bbase (se 4 (by rfl) ⟨252036, by rfl⟩ : syracuseStep 2688389 = 504073) (by norm_num)
theorem B2262437 : Blo 527800 2262437 := bbase (se 4 (by rfl) ⟨212103, by rfl⟩ : syracuseStep 2262437 = 424207) (by norm_num)
theorem B1345045 : Blo 527800 1345045 := bbase (se 6 (by rfl) ⟨31524, by rfl⟩ : syracuseStep 1345045 = 63049) (by norm_num)
theorem B1345157 : Blo 527800 1345157 := bbase (se 4 (by rfl) ⟨126108, by rfl⟩ : syracuseStep 1345157 = 252217) (by norm_num)
theorem B1312405 : Blo 527800 1312405 := bbase (se 6 (by rfl) ⟨30759, by rfl⟩ : syracuseStep 1312405 = 61519) (by norm_num)
theorem B2262725 : Blo 527800 2262725 := bbase (se 4 (by rfl) ⟨212130, by rfl⟩ : syracuseStep 2262725 = 424261) (by norm_num)
theorem B1345349 : Blo 527800 1345349 := bbase (se 4 (by rfl) ⟨126126, by rfl⟩ : syracuseStep 1345349 = 252253) (by norm_num)
theorem B4032341 : Blo 527800 4032341 := bbase (se 9 (by rfl) ⟨11813, by rfl⟩ : syracuseStep 4032341 = 23627) (by norm_num)
theorem B1902485 : Blo 527800 1902485 := bbase (se 6 (by rfl) ⟨44589, by rfl⟩ : syracuseStep 1902485 = 89179) (by norm_num)
theorem B952253 : Blo 527800 952253 := bbase (se 3 (by rfl) ⟨178547, by rfl⟩ : syracuseStep 952253 = 357095) (by norm_num)
theorem B755677 : Blo 527800 755677 := bbase (se 3 (by rfl) ⟨141689, by rfl⟩ : syracuseStep 755677 = 283379) (by norm_num)
theorem B1509349 : Blo 527800 1509349 := bbase (se 4 (by rfl) ⟨141501, by rfl⟩ : syracuseStep 1509349 = 283003) (by norm_num)
theorem B1935461 : Blo 527800 1935461 := bbase (se 4 (by rfl) ⟨181449, by rfl⟩ : syracuseStep 1935461 = 362899) (by norm_num)
theorem B1509509 : Blo 527800 1509509 := bbase (se 4 (by rfl) ⟨141516, by rfl⟩ : syracuseStep 1509509 = 283033) (by norm_num)
theorem B1345693 : Blo 527800 1345693 := bbase (se 3 (by rfl) ⟨252317, by rfl⟩ : syracuseStep 1345693 = 504635) (by norm_num)
theorem B1345805 : Blo 527800 1345805 := bbase (se 3 (by rfl) ⟨252338, by rfl⟩ : syracuseStep 1345805 = 504677) (by norm_num)
theorem B1837397 : Blo 527800 1837397 := bbase (se 10 (by rfl) ⟨2691, by rfl⟩ : syracuseStep 1837397 = 5383) (by norm_num)
theorem B1509749 : Blo 527800 1509749 := bbase (se 5 (by rfl) ⟨70769, by rfl⟩ : syracuseStep 1509749 = 141539) (by norm_num)
theorem B2263477 : Blo 527800 2263477 := bbase (se 5 (by rfl) ⟨106100, by rfl⟩ : syracuseStep 2263477 = 212201) (by norm_num)
theorem B1345997 : Blo 527800 1345997 := bbase (se 3 (by rfl) ⟨252374, by rfl⟩ : syracuseStep 1345997 = 504749) (by norm_num)
theorem B1018325 : Blo 527800 1018325 := bbase (se 7 (by rfl) ⟨11933, by rfl⟩ : syracuseStep 1018325 = 23867) (by norm_num)
theorem B2034229 : Blo 527800 2034229 := bbase (se 5 (by rfl) ⟨95354, by rfl⟩ : syracuseStep 2034229 = 190709) (by norm_num)
theorem B1509941 : Blo 527800 1509941 := bbase (se 5 (by rfl) ⟨70778, by rfl⟩ : syracuseStep 1509941 = 141557) (by norm_num)
theorem B952973 : Blo 527800 952973 := bbase (se 3 (by rfl) ⟨178682, by rfl⟩ : syracuseStep 952973 = 357365) (by norm_num)
theorem B2689685 : Blo 527800 2689685 := bbase (se 6 (by rfl) ⟨63039, by rfl⟩ : syracuseStep 2689685 = 126079) (by norm_num)
theorem B1608437 : Blo 527800 1608437 := bbase (se 5 (by rfl) ⟨75395, by rfl⟩ : syracuseStep 1608437 = 150791) (by norm_num)
theorem B756469 : Blo 527800 756469 := bbase (se 5 (by rfl) ⟨35459, by rfl⟩ : syracuseStep 756469 = 70919) (by norm_num)
theorem B1149797 : Blo 527800 1149797 := bbase (se 4 (by rfl) ⟨107793, by rfl⟩ : syracuseStep 1149797 = 215587) (by norm_num)
theorem B756805 : Blo 527800 756805 := bbase (se 4 (by rfl) ⟨70950, by rfl⟩ : syracuseStep 756805 = 141901) (by norm_num)
theorem B2264213 : Blo 527800 2264213 := bbase (se 6 (by rfl) ⟨53067, by rfl⟩ : syracuseStep 2264213 = 106135) (by norm_num)
theorem B757021 : Blo 527800 757021 := bbase (se 3 (by rfl) ⟨141941, by rfl⟩ : syracuseStep 757021 = 283883) (by norm_num)
theorem B1019309 : Blo 527800 1019309 := bbase (se 3 (by rfl) ⟨191120, by rfl⟩ : syracuseStep 1019309 = 382241) (by norm_num)
theorem B1510933 : Blo 527800 1510933 := bbase (se 6 (by rfl) ⟨35412, by rfl⟩ : syracuseStep 1510933 = 70825) (by norm_num)
theorem B2362949 : Blo 527800 2362949 := bbase (se 4 (by rfl) ⟨221526, by rfl⟩ : syracuseStep 2362949 = 443053) (by norm_num)
theorem B593797 : Blo 527800 593797 := bbase (se 4 (by rfl) ⟨55668, by rfl⟩ : syracuseStep 593797 = 111337) (by norm_num)
theorem B2690981 : Blo 527800 2690981 := bbase (se 4 (by rfl) ⟨252279, by rfl⟩ : syracuseStep 2690981 = 504559) (by norm_num)
theorem B593833 : Blo 527800 593833 := bbase (se 2 (by rfl) ⟨222687, by rfl⟩ : syracuseStep 593833 = 445375) (by norm_num)
theorem B593869 : Blo 527800 593869 := bbase (se 3 (by rfl) ⟨111350, by rfl⟩ : syracuseStep 593869 = 222701) (by norm_num)
theorem B593905 : Blo 527800 593905 := bbase (se 2 (by rfl) ⟨222714, by rfl⟩ : syracuseStep 593905 = 445429) (by norm_num)
theorem B593941 : Blo 527800 593941 := bbase (se 6 (by rfl) ⟨13920, by rfl⟩ : syracuseStep 593941 = 27841) (by norm_num)
theorem B593977 : Blo 527800 593977 := bbase (se 2 (by rfl) ⟨222741, by rfl⟩ : syracuseStep 593977 = 445483) (by norm_num)
theorem B594013 : Blo 527800 594013 := bbase (se 3 (by rfl) ⟨111377, by rfl⟩ : syracuseStep 594013 = 222755) (by norm_num)
theorem B594049 : Blo 527800 594049 := bbase (se 2 (by rfl) ⟨222768, by rfl⟩ : syracuseStep 594049 = 445537) (by norm_num)
theorem B594085 : Blo 527800 594085 := bbase (se 4 (by rfl) ⟨55695, by rfl⟩ : syracuseStep 594085 = 111391) (by norm_num)
theorem B594121 : Blo 527800 594121 := bbase (se 2 (by rfl) ⟨222795, by rfl⟩ : syracuseStep 594121 = 445591) (by norm_num)
theorem B594157 : Blo 527800 594157 := bbase (se 3 (by rfl) ⟨111404, by rfl⟩ : syracuseStep 594157 = 222809) (by norm_num)
theorem B594193 : Blo 527800 594193 := bbase (se 2 (by rfl) ⟨222822, by rfl⟩ : syracuseStep 594193 = 445645) (by norm_num)
theorem B594229 : Blo 527800 594229 := bbase (se 5 (by rfl) ⟨27854, by rfl⟩ : syracuseStep 594229 = 55709) (by norm_num)
theorem B594265 : Blo 527800 594265 := bbase (se 2 (by rfl) ⟨222849, by rfl⟩ : syracuseStep 594265 = 445699) (by norm_num)
theorem B594301 : Blo 527800 594301 := bbase (se 3 (by rfl) ⟨111431, by rfl⟩ : syracuseStep 594301 = 222863) (by norm_num)
theorem B594337 : Blo 527800 594337 := bbase (se 2 (by rfl) ⟨222876, by rfl⟩ : syracuseStep 594337 = 445753) (by norm_num)
theorem B594373 : Blo 527800 594373 := bbase (se 4 (by rfl) ⟨55722, by rfl⟩ : syracuseStep 594373 = 111445) (by norm_num)
theorem B594409 : Blo 527800 594409 := bbase (se 2 (by rfl) ⟨222903, by rfl⟩ : syracuseStep 594409 = 445807) (by norm_num)
theorem B594445 : Blo 527800 594445 := bbase (se 3 (by rfl) ⟨111458, by rfl⟩ : syracuseStep 594445 = 222917) (by norm_num)
theorem B594481 : Blo 527800 594481 := bbase (se 2 (by rfl) ⟨222930, by rfl⟩ : syracuseStep 594481 = 445861) (by norm_num)
theorem B594517 : Blo 527800 594517 := bbase (se 8 (by rfl) ⟨3483, by rfl⟩ : syracuseStep 594517 = 6967) (by norm_num)
theorem B1512037 : Blo 527800 1512037 := bbase (se 4 (by rfl) ⟨141753, by rfl⟩ : syracuseStep 1512037 = 283507) (by norm_num)
theorem B594553 : Blo 527800 594553 := bbase (se 2 (by rfl) ⟨222957, by rfl⟩ : syracuseStep 594553 = 445915) (by norm_num)
theorem B594589 : Blo 527800 594589 := bbase (se 3 (by rfl) ⟨111485, by rfl⟩ : syracuseStep 594589 = 222971) (by norm_num)
theorem B594625 : Blo 527800 594625 := bbase (se 2 (by rfl) ⟨222984, by rfl⟩ : syracuseStep 594625 = 445969) (by norm_num)
theorem B594661 : Blo 527800 594661 := bbase (se 4 (by rfl) ⟨55749, by rfl⟩ : syracuseStep 594661 = 111499) (by norm_num)
theorem B594697 : Blo 527800 594697 := bbase (se 2 (by rfl) ⟨223011, by rfl⟩ : syracuseStep 594697 = 446023) (by norm_num)
theorem B594733 : Blo 527800 594733 := bbase (se 3 (by rfl) ⟨111512, by rfl⟩ : syracuseStep 594733 = 223025) (by norm_num)
theorem B594769 : Blo 527800 594769 := bbase (se 2 (by rfl) ⟨223038, by rfl⟩ : syracuseStep 594769 = 446077) (by norm_num)
theorem B594805 : Blo 527800 594805 := bbase (se 5 (by rfl) ⟨27881, by rfl⟩ : syracuseStep 594805 = 55763) (by norm_num)
theorem B594841 : Blo 527800 594841 := bbase (se 2 (by rfl) ⟨223065, by rfl⟩ : syracuseStep 594841 = 446131) (by norm_num)
theorem B955309 : Blo 527800 955309 := bbase (se 3 (by rfl) ⟨179120, by rfl⟩ : syracuseStep 955309 = 358241) (by norm_num)
theorem B594877 : Blo 527800 594877 := bbase (se 3 (by rfl) ⟨111539, by rfl⟩ : syracuseStep 594877 = 223079) (by norm_num)
theorem B594913 : Blo 527800 594913 := bbase (se 2 (by rfl) ⟨223092, by rfl⟩ : syracuseStep 594913 = 446185) (by norm_num)
theorem B1086461 : Blo 527800 1086461 := bbase (se 3 (by rfl) ⟨203711, by rfl⟩ : syracuseStep 1086461 = 407423) (by norm_num)
theorem B726013 : Blo 527800 726013 := bbase (se 3 (by rfl) ⟨136127, by rfl⟩ : syracuseStep 726013 = 272255) (by norm_num)
theorem B594949 : Blo 527800 594949 := bbase (se 4 (by rfl) ⟨55776, by rfl⟩ : syracuseStep 594949 = 111553) (by norm_num)
theorem B594985 : Blo 527800 594985 := bbase (se 2 (by rfl) ⟨223119, by rfl⟩ : syracuseStep 594985 = 446239) (by norm_num)
theorem B595021 : Blo 527800 595021 := bbase (se 3 (by rfl) ⟨111566, by rfl⟩ : syracuseStep 595021 = 223133) (by norm_num)
theorem B595057 : Blo 527800 595057 := bbase (se 2 (by rfl) ⟨223146, by rfl⟩ : syracuseStep 595057 = 446293) (by norm_num)
theorem B595093 : Blo 527800 595093 := bbase (se 6 (by rfl) ⟨13947, by rfl⟩ : syracuseStep 595093 = 27895) (by norm_num)
theorem B791717 : Blo 527800 791717 := bbase (se 4 (by rfl) ⟨74223, by rfl⟩ : syracuseStep 791717 = 148447) (by norm_num)
theorem B595129 : Blo 527800 595129 := bbase (se 2 (by rfl) ⟨223173, by rfl⟩ : syracuseStep 595129 = 446347) (by norm_num)
theorem B791741 : Blo 527800 791741 := bbase (se 3 (by rfl) ⟨148451, by rfl⟩ : syracuseStep 791741 = 296903) (by norm_num)
theorem B1021133 : Blo 527800 1021133 := bbase (se 3 (by rfl) ⟨191462, by rfl⟩ : syracuseStep 1021133 = 382925) (by norm_num)
theorem B791765 : Blo 527800 791765 := bbase (se 7 (by rfl) ⟨9278, by rfl⟩ : syracuseStep 791765 = 18557) (by norm_num)
theorem B595165 : Blo 527800 595165 := bbase (se 3 (by rfl) ⟨111593, by rfl⟩ : syracuseStep 595165 = 223187) (by norm_num)
theorem B791789 : Blo 527800 791789 := bbase (se 3 (by rfl) ⟨148460, by rfl⟩ : syracuseStep 791789 = 296921) (by norm_num)
theorem B595201 : Blo 527800 595201 := bbase (se 2 (by rfl) ⟨223200, by rfl⟩ : syracuseStep 595201 = 446401) (by norm_num)
theorem B791813 : Blo 527800 791813 := bbase (se 4 (by rfl) ⟨74232, by rfl⟩ : syracuseStep 791813 = 148465) (by norm_num)
theorem B791837 : Blo 527800 791837 := bbase (se 3 (by rfl) ⟨148469, by rfl⟩ : syracuseStep 791837 = 296939) (by norm_num)
theorem B595237 : Blo 527800 595237 := bbase (se 4 (by rfl) ⟨55803, by rfl⟩ : syracuseStep 595237 = 111607) (by norm_num)
theorem B791861 : Blo 527800 791861 := bbase (se 5 (by rfl) ⟨37118, by rfl⟩ : syracuseStep 791861 = 74237) (by norm_num)
theorem B595273 : Blo 527800 595273 := bbase (se 2 (by rfl) ⟨223227, by rfl⟩ : syracuseStep 595273 = 446455) (by norm_num)
theorem B791885 : Blo 527800 791885 := bbase (se 3 (by rfl) ⟨148478, by rfl⟩ : syracuseStep 791885 = 296957) (by norm_num)
theorem B955741 : Blo 527800 955741 := bbase (se 3 (by rfl) ⟨179201, by rfl⟩ : syracuseStep 955741 = 358403) (by norm_num)
theorem B791909 : Blo 527800 791909 := bbase (se 4 (by rfl) ⟨74241, by rfl⟩ : syracuseStep 791909 = 148483) (by norm_num)
theorem B595309 : Blo 527800 595309 := bbase (se 3 (by rfl) ⟨111620, by rfl⟩ : syracuseStep 595309 = 223241) (by norm_num)
theorem B791933 : Blo 527800 791933 := bbase (se 3 (by rfl) ⟨148487, by rfl⟩ : syracuseStep 791933 = 296975) (by norm_num)
theorem B595345 : Blo 527800 595345 := bbase (se 2 (by rfl) ⟨223254, by rfl⟩ : syracuseStep 595345 = 446509) (by norm_num)
theorem B791957 : Blo 527800 791957 := bbase (se 6 (by rfl) ⟨18561, by rfl⟩ : syracuseStep 791957 = 37123) (by norm_num)
theorem B1021349 : Blo 527800 1021349 := bbase (se 4 (by rfl) ⟨95751, by rfl⟩ : syracuseStep 1021349 = 191503) (by norm_num)
theorem B791981 : Blo 527800 791981 := bbase (se 3 (by rfl) ⟨148496, by rfl⟩ : syracuseStep 791981 = 296993) (by norm_num)
theorem B595381 : Blo 527800 595381 := bbase (se 5 (by rfl) ⟨27908, by rfl⟩ : syracuseStep 595381 = 55817) (by norm_num)
theorem B792005 : Blo 527800 792005 := bbase (se 4 (by rfl) ⟨74250, by rfl⟩ : syracuseStep 792005 = 148501) (by norm_num)
theorem B857557 : Blo 527800 857557 := bbase (se 7 (by rfl) ⟨10049, by rfl⟩ : syracuseStep 857557 = 20099) (by norm_num)
theorem B595417 : Blo 527800 595417 := bbase (se 2 (by rfl) ⟨223281, by rfl⟩ : syracuseStep 595417 = 446563) (by norm_num)
theorem B792029 : Blo 527800 792029 := bbase (se 3 (by rfl) ⟨148505, by rfl⟩ : syracuseStep 792029 = 297011) (by norm_num)
theorem B792053 : Blo 527800 792053 := bbase (se 5 (by rfl) ⟨37127, by rfl⟩ : syracuseStep 792053 = 74255) (by norm_num)
theorem B595453 : Blo 527800 595453 := bbase (se 3 (by rfl) ⟨111647, by rfl⟩ : syracuseStep 595453 = 223295) (by norm_num)
theorem B792077 : Blo 527800 792077 := bbase (se 3 (by rfl) ⟨148514, by rfl⟩ : syracuseStep 792077 = 297029) (by norm_num)
theorem B595489 : Blo 527800 595489 := bbase (se 2 (by rfl) ⟨223308, by rfl⟩ : syracuseStep 595489 = 446617) (by norm_num)
theorem B792101 : Blo 527800 792101 := bbase (se 4 (by rfl) ⟨74259, by rfl⟩ : syracuseStep 792101 = 148519) (by norm_num)
theorem B792125 : Blo 527800 792125 := bbase (se 3 (by rfl) ⟨148523, by rfl⟩ : syracuseStep 792125 = 297047) (by norm_num)
theorem B595525 : Blo 527800 595525 := bbase (se 4 (by rfl) ⟨55830, by rfl⟩ : syracuseStep 595525 = 111661) (by norm_num)
theorem B792149 : Blo 527800 792149 := bbase (se 8 (by rfl) ⟨4641, by rfl⟩ : syracuseStep 792149 = 9283) (by norm_num)
theorem B595561 : Blo 527800 595561 := bbase (se 2 (by rfl) ⟨223335, by rfl⟩ : syracuseStep 595561 = 446671) (by norm_num)
theorem B792173 : Blo 527800 792173 := bbase (se 3 (by rfl) ⟨148532, by rfl⟩ : syracuseStep 792173 = 297065) (by norm_num)
theorem B792197 : Blo 527800 792197 := bbase (se 4 (by rfl) ⟨74268, by rfl⟩ : syracuseStep 792197 = 148537) (by norm_num)
theorem B595597 : Blo 527800 595597 := bbase (se 3 (by rfl) ⟨111674, by rfl⟩ : syracuseStep 595597 = 223349) (by norm_num)
theorem B792221 : Blo 527800 792221 := bbase (se 3 (by rfl) ⟨148541, by rfl⟩ : syracuseStep 792221 = 297083) (by norm_num)
theorem B595633 : Blo 527800 595633 := bbase (se 2 (by rfl) ⟨223362, by rfl⟩ : syracuseStep 595633 = 446725) (by norm_num)
theorem B792245 : Blo 527800 792245 := bbase (se 5 (by rfl) ⟨37136, by rfl⟩ : syracuseStep 792245 = 74273) (by norm_num)
theorem B792269 : Blo 527800 792269 := bbase (se 3 (by rfl) ⟨148550, by rfl⟩ : syracuseStep 792269 = 297101) (by norm_num)
theorem B595669 : Blo 527800 595669 := bbase (se 7 (by rfl) ⟨6980, by rfl⟩ : syracuseStep 595669 = 13961) (by norm_num)
theorem B792293 : Blo 527800 792293 := bbase (se 4 (by rfl) ⟨74277, by rfl⟩ : syracuseStep 792293 = 148555) (by norm_num)
theorem B595705 : Blo 527800 595705 := bbase (se 2 (by rfl) ⟨223389, by rfl⟩ : syracuseStep 595705 = 446779) (by norm_num)
theorem B792317 : Blo 527800 792317 := bbase (se 3 (by rfl) ⟨148559, by rfl⟩ : syracuseStep 792317 = 297119) (by norm_num)
theorem B792341 : Blo 527800 792341 := bbase (se 6 (by rfl) ⟨18570, by rfl⟩ : syracuseStep 792341 = 37141) (by norm_num)
theorem B595741 : Blo 527800 595741 := bbase (se 3 (by rfl) ⟨111701, by rfl⟩ : syracuseStep 595741 = 223403) (by norm_num)
theorem B890669 : Blo 527800 890669 := bbase (se 3 (by rfl) ⟨167000, by rfl⟩ : syracuseStep 890669 = 334001) (by norm_num)
theorem B792365 : Blo 527800 792365 := bbase (se 3 (by rfl) ⟨148568, by rfl⟩ : syracuseStep 792365 = 297137) (by norm_num)
theorem B5084981 : Blo 527800 5084981 := bbase (se 5 (by rfl) ⟨238358, by rfl⟩ : syracuseStep 5084981 = 476717) (by norm_num)
theorem B595777 : Blo 527800 595777 := bbase (se 2 (by rfl) ⟨223416, by rfl⟩ : syracuseStep 595777 = 446833) (by norm_num)
theorem B792389 : Blo 527800 792389 := bbase (se 4 (by rfl) ⟨74286, by rfl⟩ : syracuseStep 792389 = 148573) (by norm_num)
theorem B792413 : Blo 527800 792413 := bbase (se 3 (by rfl) ⟨148577, by rfl⟩ : syracuseStep 792413 = 297155) (by norm_num)
theorem B595813 : Blo 527800 595813 := bbase (se 4 (by rfl) ⟨55857, by rfl⟩ : syracuseStep 595813 = 111715) (by norm_num)
theorem B956261 : Blo 527800 956261 := bbase (se 4 (by rfl) ⟨89649, by rfl⟩ : syracuseStep 956261 = 179299) (by norm_num)
theorem B792437 : Blo 527800 792437 := bbase (se 5 (by rfl) ⟨37145, by rfl⟩ : syracuseStep 792437 = 74291) (by norm_num)
theorem B1087349 : Blo 527800 1087349 := bbase (se 5 (by rfl) ⟨50969, by rfl⟩ : syracuseStep 1087349 = 101939) (by norm_num)
theorem B595849 : Blo 527800 595849 := bbase (se 2 (by rfl) ⟨223443, by rfl⟩ : syracuseStep 595849 = 446887) (by norm_num)
theorem B792461 : Blo 527800 792461 := bbase (se 3 (by rfl) ⟨148586, by rfl⟩ : syracuseStep 792461 = 297173) (by norm_num)
theorem B792485 : Blo 527800 792485 := bbase (se 4 (by rfl) ⟨74295, by rfl⟩ : syracuseStep 792485 = 148591) (by norm_num)
theorem B890797 : Blo 527800 890797 := bbase (se 3 (by rfl) ⟨167024, by rfl⟩ : syracuseStep 890797 = 334049) (by norm_num)
theorem B595885 : Blo 527800 595885 := bbase (se 3 (by rfl) ⟨111728, by rfl⟩ : syracuseStep 595885 = 223457) (by norm_num)
theorem B792509 : Blo 527800 792509 := bbase (se 3 (by rfl) ⟨148595, by rfl⟩ : syracuseStep 792509 = 297191) (by norm_num)
theorem B595921 : Blo 527800 595921 := bbase (se 2 (by rfl) ⟨223470, by rfl⟩ : syracuseStep 595921 = 446941) (by norm_num)
theorem B792533 : Blo 527800 792533 := bbase (se 7 (by rfl) ⟨9287, by rfl⟩ : syracuseStep 792533 = 18575) (by norm_num)
theorem B792557 : Blo 527800 792557 := bbase (se 3 (by rfl) ⟨148604, by rfl⟩ : syracuseStep 792557 = 297209) (by norm_num)
theorem B595957 : Blo 527800 595957 := bbase (se 5 (by rfl) ⟨27935, by rfl⟩ : syracuseStep 595957 = 55871) (by norm_num)
theorem B890885 : Blo 527800 890885 := bbase (se 4 (by rfl) ⟨83520, by rfl⟩ : syracuseStep 890885 = 167041) (by norm_num)
theorem B792581 : Blo 527800 792581 := bbase (se 4 (by rfl) ⟨74304, by rfl⟩ : syracuseStep 792581 = 148609) (by norm_num)
theorem B595993 : Blo 527800 595993 := bbase (se 2 (by rfl) ⟨223497, by rfl⟩ : syracuseStep 595993 = 446995) (by norm_num)
theorem B792605 : Blo 527800 792605 := bbase (se 3 (by rfl) ⟨148613, by rfl⟩ : syracuseStep 792605 = 297227) (by norm_num)
theorem B792629 : Blo 527800 792629 := bbase (se 5 (by rfl) ⟨37154, by rfl⟩ : syracuseStep 792629 = 74309) (by norm_num)
theorem B596029 : Blo 527800 596029 := bbase (se 3 (by rfl) ⟨111755, by rfl⟩ : syracuseStep 596029 = 223511) (by norm_num)
theorem B1513541 : Blo 527800 1513541 := bbase (se 4 (by rfl) ⟨141894, by rfl⟩ : syracuseStep 1513541 = 283789) (by norm_num)
theorem B792653 : Blo 527800 792653 := bbase (se 3 (by rfl) ⟨148622, by rfl⟩ : syracuseStep 792653 = 297245) (by norm_num)
theorem B3020885 : Blo 527800 3020885 := bbase (se 8 (by rfl) ⟨17700, by rfl⟩ : syracuseStep 3020885 = 35401) (by norm_num)
theorem B596065 : Blo 527800 596065 := bbase (se 2 (by rfl) ⟨223524, by rfl⟩ : syracuseStep 596065 = 447049) (by norm_num)
theorem B792677 : Blo 527800 792677 := bbase (se 4 (by rfl) ⟨74313, by rfl⟩ : syracuseStep 792677 = 148627) (by norm_num)
theorem B792701 : Blo 527800 792701 := bbase (se 3 (by rfl) ⟨148631, by rfl⟩ : syracuseStep 792701 = 297263) (by norm_num)
theorem B956549 : Blo 527800 956549 := bbase (se 4 (by rfl) ⟨89676, by rfl⟩ : syracuseStep 956549 = 179353) (by norm_num)
theorem B891013 : Blo 527800 891013 := bbase (se 4 (by rfl) ⟨83532, by rfl⟩ : syracuseStep 891013 = 167065) (by norm_num)
theorem B596101 : Blo 527800 596101 := bbase (se 4 (by rfl) ⟨55884, by rfl⟩ : syracuseStep 596101 = 111769) (by norm_num)
theorem B792725 : Blo 527800 792725 := bbase (se 6 (by rfl) ⟨18579, by rfl⟩ : syracuseStep 792725 = 37159) (by norm_num)
theorem B596137 : Blo 527800 596137 := bbase (se 2 (by rfl) ⟨223551, by rfl⟩ : syracuseStep 596137 = 447103) (by norm_num)
theorem B792749 : Blo 527800 792749 := bbase (se 3 (by rfl) ⟨148640, by rfl⟩ : syracuseStep 792749 = 297281) (by norm_num)
theorem B792773 : Blo 527800 792773 := bbase (se 4 (by rfl) ⟨74322, by rfl⟩ : syracuseStep 792773 = 148645) (by norm_num)
theorem B596173 : Blo 527800 596173 := bbase (se 3 (by rfl) ⟨111782, by rfl⟩ : syracuseStep 596173 = 223565) (by norm_num)
theorem B891101 : Blo 527800 891101 := bbase (se 3 (by rfl) ⟨167081, by rfl⟩ : syracuseStep 891101 = 334163) (by norm_num)
theorem B792797 : Blo 527800 792797 := bbase (se 3 (by rfl) ⟨148649, by rfl⟩ : syracuseStep 792797 = 297299) (by norm_num)
theorem B596209 : Blo 527800 596209 := bbase (se 2 (by rfl) ⟨223578, by rfl⟩ : syracuseStep 596209 = 447157) (by norm_num)
theorem B792821 : Blo 527800 792821 := bbase (se 5 (by rfl) ⟨37163, by rfl⟩ : syracuseStep 792821 = 74327) (by norm_num)
theorem B792845 : Blo 527800 792845 := bbase (se 3 (by rfl) ⟨148658, by rfl⟩ : syracuseStep 792845 = 297317) (by norm_num)
theorem B596245 : Blo 527800 596245 := bbase (se 6 (by rfl) ⟨13974, by rfl⟩ : syracuseStep 596245 = 27949) (by norm_num)
theorem B792869 : Blo 527800 792869 := bbase (se 4 (by rfl) ⟨74331, by rfl⟩ : syracuseStep 792869 = 148663) (by norm_num)
theorem B596281 : Blo 527800 596281 := bbase (se 2 (by rfl) ⟨223605, by rfl⟩ : syracuseStep 596281 = 447211) (by norm_num)
theorem B792893 : Blo 527800 792893 := bbase (se 3 (by rfl) ⟨148667, by rfl⟩ : syracuseStep 792893 = 297335) (by norm_num)
theorem B792917 : Blo 527800 792917 := bbase (se 10 (by rfl) ⟨1161, by rfl⟩ : syracuseStep 792917 = 2323) (by norm_num)
theorem B891229 : Blo 527800 891229 := bbase (se 3 (by rfl) ⟨167105, by rfl⟩ : syracuseStep 891229 = 334211) (by norm_num)
theorem B596317 : Blo 527800 596317 := bbase (se 3 (by rfl) ⟨111809, by rfl⟩ : syracuseStep 596317 = 223619) (by norm_num)
theorem B792941 : Blo 527800 792941 := bbase (se 3 (by rfl) ⟨148676, by rfl⟩ : syracuseStep 792941 = 297353) (by norm_num)
theorem B2267509 : Blo 527800 2267509 := bbase (se 5 (by rfl) ⟨106289, by rfl⟩ : syracuseStep 2267509 = 212579) (by norm_num)
theorem B596353 : Blo 527800 596353 := bbase (se 2 (by rfl) ⟨223632, by rfl⟩ : syracuseStep 596353 = 447265) (by norm_num)
theorem B792965 : Blo 527800 792965 := bbase (se 4 (by rfl) ⟨74340, by rfl⟩ : syracuseStep 792965 = 148681) (by norm_num)
theorem B792989 : Blo 527800 792989 := bbase (se 3 (by rfl) ⟨148685, by rfl⟩ : syracuseStep 792989 = 297371) (by norm_num)
theorem B596389 : Blo 527800 596389 := bbase (se 4 (by rfl) ⟨55911, by rfl⟩ : syracuseStep 596389 = 111823) (by norm_num)
theorem B891317 : Blo 527800 891317 := bbase (se 5 (by rfl) ⟨41780, by rfl⟩ : syracuseStep 891317 = 83561) (by norm_num)
theorem B793013 : Blo 527800 793013 := bbase (se 5 (by rfl) ⟨37172, by rfl⟩ : syracuseStep 793013 = 74345) (by norm_num)
theorem B596425 : Blo 527800 596425 := bbase (se 2 (by rfl) ⟨223659, by rfl⟩ : syracuseStep 596425 = 447319) (by norm_num)
theorem B793037 : Blo 527800 793037 := bbase (se 3 (by rfl) ⟨148694, by rfl⟩ : syracuseStep 793037 = 297389) (by norm_num)
theorem B793061 : Blo 527800 793061 := bbase (se 4 (by rfl) ⟨74349, by rfl⟩ : syracuseStep 793061 = 148699) (by norm_num)
theorem B596461 : Blo 527800 596461 := bbase (se 3 (by rfl) ⟨111836, by rfl⟩ : syracuseStep 596461 = 223673) (by norm_num)
theorem B793085 : Blo 527800 793085 := bbase (se 3 (by rfl) ⟨148703, by rfl⟩ : syracuseStep 793085 = 297407) (by norm_num)
theorem B596497 : Blo 527800 596497 := bbase (se 2 (by rfl) ⟨223686, by rfl⟩ : syracuseStep 596497 = 447373) (by norm_num)
theorem B793109 : Blo 527800 793109 := bbase (se 6 (by rfl) ⟨18588, by rfl⟩ : syracuseStep 793109 = 37177) (by norm_num)
theorem B793133 : Blo 527800 793133 := bbase (se 3 (by rfl) ⟨148712, by rfl⟩ : syracuseStep 793133 = 297425) (by norm_num)
theorem B891445 : Blo 527800 891445 := bbase (se 5 (by rfl) ⟨41786, by rfl⟩ : syracuseStep 891445 = 83573) (by norm_num)
theorem B596533 : Blo 527800 596533 := bbase (se 5 (by rfl) ⟨27962, by rfl⟩ : syracuseStep 596533 = 55925) (by norm_num)
theorem B956981 : Blo 527800 956981 := bbase (se 5 (by rfl) ⟨44858, by rfl⟩ : syracuseStep 956981 = 89717) (by norm_num)
theorem B793157 : Blo 527800 793157 := bbase (se 4 (by rfl) ⟨74358, by rfl⟩ : syracuseStep 793157 = 148717) (by norm_num)
theorem B596569 : Blo 527800 596569 := bbase (se 2 (by rfl) ⟨223713, by rfl⟩ : syracuseStep 596569 = 447427) (by norm_num)
theorem B793181 : Blo 527800 793181 := bbase (se 3 (by rfl) ⟨148721, by rfl⟩ : syracuseStep 793181 = 297443) (by norm_num)
theorem B793205 : Blo 527800 793205 := bbase (se 5 (by rfl) ⟨37181, by rfl⟩ : syracuseStep 793205 = 74363) (by norm_num)
theorem B596605 : Blo 527800 596605 := bbase (se 3 (by rfl) ⟨111863, by rfl⟩ : syracuseStep 596605 = 223727) (by norm_num)
theorem B891533 : Blo 527800 891533 := bbase (se 3 (by rfl) ⟨167162, by rfl⟩ : syracuseStep 891533 = 334325) (by norm_num)
theorem B793229 : Blo 527800 793229 := bbase (se 3 (by rfl) ⟨148730, by rfl⟩ : syracuseStep 793229 = 297461) (by norm_num)
theorem B727693 : Blo 527800 727693 := bbase (se 3 (by rfl) ⟨136442, by rfl⟩ : syracuseStep 727693 = 272885) (by norm_num)
theorem B3054229 : Blo 527800 3054229 := bbase (se 6 (by rfl) ⟨71583, by rfl⟩ : syracuseStep 3054229 = 143167) (by norm_num)
theorem B596641 : Blo 527800 596641 := bbase (se 2 (by rfl) ⟨223740, by rfl⟩ : syracuseStep 596641 = 447481) (by norm_num)
theorem B793253 : Blo 527800 793253 := bbase (se 4 (by rfl) ⟨74367, by rfl⟩ : syracuseStep 793253 = 148735) (by norm_num)
theorem B793277 : Blo 527800 793277 := bbase (se 3 (by rfl) ⟨148739, by rfl⟩ : syracuseStep 793277 = 297479) (by norm_num)
theorem B596677 : Blo 527800 596677 := bbase (se 4 (by rfl) ⟨55938, by rfl⟩ : syracuseStep 596677 = 111877) (by norm_num)
theorem B957125 : Blo 527800 957125 := bbase (se 4 (by rfl) ⟨89730, by rfl⟩ : syracuseStep 957125 = 179461) (by norm_num)
theorem B793301 : Blo 527800 793301 := bbase (se 7 (by rfl) ⟨9296, by rfl⟩ : syracuseStep 793301 = 18593) (by norm_num)
theorem B596713 : Blo 527800 596713 := bbase (se 2 (by rfl) ⟨223767, by rfl⟩ : syracuseStep 596713 = 447535) (by norm_num)
theorem B793325 : Blo 527800 793325 := bbase (se 3 (by rfl) ⟨148748, by rfl⟩ : syracuseStep 793325 = 297497) (by norm_num)
theorem B563969 : Blo 527800 563969 := bbase (se 2 (by rfl) ⟨211488, by rfl⟩ : syracuseStep 563969 = 422977) (by norm_num)
theorem B793349 : Blo 527800 793349 := bbase (se 4 (by rfl) ⟨74376, by rfl⟩ : syracuseStep 793349 = 148753) (by norm_num)
theorem B891661 : Blo 527800 891661 := bbase (se 3 (by rfl) ⟨167186, by rfl⟩ : syracuseStep 891661 = 334373) (by norm_num)
theorem B596749 : Blo 527800 596749 := bbase (se 3 (by rfl) ⟨111890, by rfl⟩ : syracuseStep 596749 = 223781) (by norm_num)
theorem B793373 : Blo 527800 793373 := bbase (se 3 (by rfl) ⟨148757, by rfl⟩ : syracuseStep 793373 = 297515) (by norm_num)
theorem B596785 : Blo 527800 596785 := bbase (se 2 (by rfl) ⟨223794, by rfl⟩ : syracuseStep 596785 = 447589) (by norm_num)
theorem B793397 : Blo 527800 793397 := bbase (se 5 (by rfl) ⟨37190, by rfl⟩ : syracuseStep 793397 = 74381) (by norm_num)
theorem B2005829 : Blo 527800 2005829 := bbase (se 4 (by rfl) ⟨188046, by rfl⟩ : syracuseStep 2005829 = 376093) (by norm_num)
theorem B564041 : Blo 527800 564041 := bbase (se 2 (by rfl) ⟨211515, by rfl⟩ : syracuseStep 564041 = 423031) (by norm_num)
theorem B793421 : Blo 527800 793421 := bbase (se 3 (by rfl) ⟨148766, by rfl⟩ : syracuseStep 793421 = 297533) (by norm_num)
theorem B596821 : Blo 527800 596821 := bbase (se 9 (by rfl) ⟨1748, by rfl⟩ : syracuseStep 596821 = 3497) (by norm_num)
theorem B891749 : Blo 527800 891749 := bbase (se 4 (by rfl) ⟨83601, by rfl⟩ : syracuseStep 891749 = 167203) (by norm_num)
theorem B793445 : Blo 527800 793445 := bbase (se 4 (by rfl) ⟨74385, by rfl⟩ : syracuseStep 793445 = 148771) (by norm_num)
theorem B596857 : Blo 527800 596857 := bbase (se 2 (by rfl) ⟨223821, by rfl⟩ : syracuseStep 596857 = 447643) (by norm_num)
theorem B793469 : Blo 527800 793469 := bbase (se 3 (by rfl) ⟨148775, by rfl⟩ : syracuseStep 793469 = 297551) (by norm_num)
theorem B793493 : Blo 527800 793493 := bbase (se 6 (by rfl) ⟨18597, by rfl⟩ : syracuseStep 793493 = 37195) (by norm_num)
theorem B596893 : Blo 527800 596893 := bbase (se 3 (by rfl) ⟨111917, by rfl⟩ : syracuseStep 596893 = 223835) (by norm_num)
theorem B793517 : Blo 527800 793517 := bbase (se 3 (by rfl) ⟨148784, by rfl⟩ : syracuseStep 793517 = 297569) (by norm_num)
theorem B596929 : Blo 527800 596929 := bbase (se 2 (by rfl) ⟨223848, by rfl⟩ : syracuseStep 596929 = 447697) (by norm_num)
theorem B793541 : Blo 527800 793541 := bbase (se 4 (by rfl) ⟨74394, by rfl⟩ : syracuseStep 793541 = 148789) (by norm_num)
theorem B793565 : Blo 527800 793565 := bbase (se 3 (by rfl) ⟨148793, by rfl⟩ : syracuseStep 793565 = 297587) (by norm_num)
theorem B891877 : Blo 527800 891877 := bbase (se 4 (by rfl) ⟨83613, by rfl⟩ : syracuseStep 891877 = 167227) (by norm_num)
theorem B596965 : Blo 527800 596965 := bbase (se 4 (by rfl) ⟨55965, by rfl⟩ : syracuseStep 596965 = 111931) (by norm_num)
theorem B793589 : Blo 527800 793589 := bbase (se 5 (by rfl) ⟨37199, by rfl⟩ : syracuseStep 793589 = 74399) (by norm_num)
theorem B4529141 : Blo 527800 4529141 := bbase (se 5 (by rfl) ⟨212303, by rfl⟩ : syracuseStep 4529141 = 424607) (by norm_num)
theorem B564229 : Blo 527800 564229 := bbase (se 4 (by rfl) ⟨52896, by rfl⟩ : syracuseStep 564229 = 105793) (by norm_num)
theorem B597001 : Blo 527800 597001 := bbase (se 2 (by rfl) ⟨223875, by rfl⟩ : syracuseStep 597001 = 447751) (by norm_num)
theorem B793613 : Blo 527800 793613 := bbase (se 3 (by rfl) ⟨148802, by rfl⟩ : syracuseStep 793613 = 297605) (by norm_num)
theorem B793637 : Blo 527800 793637 := bbase (se 4 (by rfl) ⟨74403, by rfl⟩ : syracuseStep 793637 = 148807) (by norm_num)
theorem B597037 : Blo 527800 597037 := bbase (se 3 (by rfl) ⟨111944, by rfl⟩ : syracuseStep 597037 = 223889) (by norm_num)
theorem B891965 : Blo 527800 891965 := bbase (se 3 (by rfl) ⟨167243, by rfl⟩ : syracuseStep 891965 = 334487) (by norm_num)
theorem B793661 : Blo 527800 793661 := bbase (se 3 (by rfl) ⟨148811, by rfl⟩ : syracuseStep 793661 = 297623) (by norm_num)
theorem B597073 : Blo 527800 597073 := bbase (se 2 (by rfl) ⟨223902, by rfl⟩ : syracuseStep 597073 = 447805) (by norm_num)
theorem B793685 : Blo 527800 793685 := bbase (se 8 (by rfl) ⟨4650, by rfl⟩ : syracuseStep 793685 = 9301) (by norm_num)
theorem B2006117 : Blo 527800 2006117 := bbase (se 4 (by rfl) ⟨188073, by rfl⟩ : syracuseStep 2006117 = 376147) (by norm_num)
theorem B793709 : Blo 527800 793709 := bbase (se 3 (by rfl) ⟨148820, by rfl⟩ : syracuseStep 793709 = 297641) (by norm_num)
theorem B597109 : Blo 527800 597109 := bbase (se 5 (by rfl) ⟨27989, by rfl⟩ : syracuseStep 597109 = 55979) (by norm_num)
theorem B793733 : Blo 527800 793733 := bbase (se 4 (by rfl) ⟨74412, by rfl⟩ : syracuseStep 793733 = 148825) (by norm_num)
theorem B597145 : Blo 527800 597145 := bbase (se 2 (by rfl) ⟨223929, by rfl⟩ : syracuseStep 597145 = 447859) (by norm_num)
theorem B793757 : Blo 527800 793757 := bbase (se 3 (by rfl) ⟨148829, by rfl⟩ : syracuseStep 793757 = 297659) (by norm_num)
theorem B793781 : Blo 527800 793781 := bbase (se 5 (by rfl) ⟨37208, by rfl⟩ : syracuseStep 793781 = 74417) (by norm_num)
theorem B564413 : Blo 527800 564413 := bbase (se 3 (by rfl) ⟨105827, by rfl⟩ : syracuseStep 564413 = 211655) (by norm_num)
theorem B892093 : Blo 527800 892093 := bbase (se 3 (by rfl) ⟨167267, by rfl⟩ : syracuseStep 892093 = 334535) (by norm_num)
theorem B597181 : Blo 527800 597181 := bbase (se 3 (by rfl) ⟨111971, by rfl⟩ : syracuseStep 597181 = 223943) (by norm_num)
theorem B793805 : Blo 527800 793805 := bbase (se 3 (by rfl) ⟨148838, by rfl⟩ : syracuseStep 793805 = 297677) (by norm_num)
theorem B597217 : Blo 527800 597217 := bbase (se 2 (by rfl) ⟨223956, by rfl⟩ : syracuseStep 597217 = 447913) (by norm_num)
theorem B793829 : Blo 527800 793829 := bbase (se 4 (by rfl) ⟨74421, by rfl⟩ : syracuseStep 793829 = 148843) (by norm_num)
theorem B3022069 : Blo 527800 3022069 := bbase (se 5 (by rfl) ⟨141659, by rfl⟩ : syracuseStep 3022069 = 283319) (by norm_num)
theorem B793853 : Blo 527800 793853 := bbase (se 3 (by rfl) ⟨148847, by rfl⟩ : syracuseStep 793853 = 297695) (by norm_num)
theorem B597253 : Blo 527800 597253 := bbase (se 4 (by rfl) ⟨55992, by rfl⟩ : syracuseStep 597253 = 111985) (by norm_num)
theorem B892181 : Blo 527800 892181 := bbase (se 6 (by rfl) ⟨20910, by rfl⟩ : syracuseStep 892181 = 41821) (by norm_num)
theorem B793877 : Blo 527800 793877 := bbase (se 6 (by rfl) ⟨18606, by rfl⟩ : syracuseStep 793877 = 37213) (by norm_num)
theorem B597289 : Blo 527800 597289 := bbase (se 2 (by rfl) ⟨223983, by rfl⟩ : syracuseStep 597289 = 447967) (by norm_num)
theorem B793901 : Blo 527800 793901 := bbase (se 3 (by rfl) ⟨148856, by rfl⟩ : syracuseStep 793901 = 297713) (by norm_num)
theorem B793925 : Blo 527800 793925 := bbase (se 4 (by rfl) ⟨74430, by rfl⟩ : syracuseStep 793925 = 148861) (by norm_num)
theorem B597325 : Blo 527800 597325 := bbase (se 3 (by rfl) ⟨111998, by rfl⟩ : syracuseStep 597325 = 223997) (by norm_num)
theorem B793949 : Blo 527800 793949 := bbase (se 3 (by rfl) ⟨148865, by rfl⟩ : syracuseStep 793949 = 297731) (by norm_num)
theorem B597361 : Blo 527800 597361 := bbase (se 2 (by rfl) ⟨224010, by rfl⟩ : syracuseStep 597361 = 448021) (by norm_num)
theorem B793973 : Blo 527800 793973 := bbase (se 5 (by rfl) ⟨37217, by rfl⟩ : syracuseStep 793973 = 74435) (by norm_num)
theorem B793997 : Blo 527800 793997 := bbase (se 3 (by rfl) ⟨148874, by rfl⟩ : syracuseStep 793997 = 297749) (by norm_num)
theorem B892309 : Blo 527800 892309 := bbase (se 6 (by rfl) ⟨20913, by rfl⟩ : syracuseStep 892309 = 41827) (by norm_num)
theorem B597397 : Blo 527800 597397 := bbase (se 6 (by rfl) ⟨14001, by rfl⟩ : syracuseStep 597397 = 28003) (by norm_num)
theorem B794021 : Blo 527800 794021 := bbase (se 4 (by rfl) ⟨74439, by rfl⟩ : syracuseStep 794021 = 148879) (by norm_num)
theorem B597433 : Blo 527800 597433 := bbase (se 2 (by rfl) ⟨224037, by rfl⟩ : syracuseStep 597433 = 448075) (by norm_num)
theorem B794045 : Blo 527800 794045 := bbase (se 3 (by rfl) ⟨148883, by rfl⟩ : syracuseStep 794045 = 297767) (by norm_num)
theorem B794069 : Blo 527800 794069 := bbase (se 7 (by rfl) ⟨9305, by rfl⟩ : syracuseStep 794069 = 18611) (by norm_num)
theorem B597469 : Blo 527800 597469 := bbase (se 3 (by rfl) ⟨112025, by rfl⟩ : syracuseStep 597469 = 224051) (by norm_num)
theorem B1908197 : Blo 527800 1908197 := bbase (se 4 (by rfl) ⟨178893, by rfl⟩ : syracuseStep 1908197 = 357787) (by norm_num)
theorem B892397 : Blo 527800 892397 := bbase (se 3 (by rfl) ⟨167324, by rfl⟩ : syracuseStep 892397 = 334649) (by norm_num)
theorem B794093 : Blo 527800 794093 := bbase (se 3 (by rfl) ⟨148892, by rfl⟩ : syracuseStep 794093 = 297785) (by norm_num)
theorem B597505 : Blo 527800 597505 := bbase (se 2 (by rfl) ⟨224064, by rfl⟩ : syracuseStep 597505 = 448129) (by norm_num)
theorem B794117 : Blo 527800 794117 := bbase (se 4 (by rfl) ⟨74448, by rfl⟩ : syracuseStep 794117 = 148897) (by norm_num)
theorem B794141 : Blo 527800 794141 := bbase (se 3 (by rfl) ⟨148901, by rfl⟩ : syracuseStep 794141 = 297803) (by norm_num)
theorem B597541 : Blo 527800 597541 := bbase (se 4 (by rfl) ⟨56019, by rfl⟩ : syracuseStep 597541 = 112039) (by norm_num)
theorem B794165 : Blo 527800 794165 := bbase (se 5 (by rfl) ⟨37226, by rfl⟩ : syracuseStep 794165 = 74453) (by norm_num)
theorem B597577 : Blo 527800 597577 := bbase (se 2 (by rfl) ⟨224091, by rfl⟩ : syracuseStep 597577 = 448183) (by norm_num)
theorem B794189 : Blo 527800 794189 := bbase (se 3 (by rfl) ⟨148910, by rfl⟩ : syracuseStep 794189 = 297821) (by norm_num)
theorem B794213 : Blo 527800 794213 := bbase (se 4 (by rfl) ⟨74457, by rfl⟩ : syracuseStep 794213 = 148915) (by norm_num)
theorem B892525 : Blo 527800 892525 := bbase (se 3 (by rfl) ⟨167348, by rfl⟩ : syracuseStep 892525 = 334697) (by norm_num)
theorem B597613 : Blo 527800 597613 := bbase (se 3 (by rfl) ⟨112052, by rfl⟩ : syracuseStep 597613 = 224105) (by norm_num)
theorem B794237 : Blo 527800 794237 := bbase (se 3 (by rfl) ⟨148919, by rfl⟩ : syracuseStep 794237 = 297839) (by norm_num)
theorem B597649 : Blo 527800 597649 := bbase (se 2 (by rfl) ⟨224118, by rfl⟩ : syracuseStep 597649 = 448237) (by norm_num)
theorem B794261 : Blo 527800 794261 := bbase (se 6 (by rfl) ⟨18615, by rfl⟩ : syracuseStep 794261 = 37231) (by norm_num)
theorem B2203301 : Blo 527800 2203301 := bbase (se 4 (by rfl) ⟨206559, by rfl⟩ : syracuseStep 2203301 = 413119) (by norm_num)
theorem B794285 : Blo 527800 794285 := bbase (se 3 (by rfl) ⟨148928, by rfl⟩ : syracuseStep 794285 = 297857) (by norm_num)
theorem B597685 : Blo 527800 597685 := bbase (se 5 (by rfl) ⟨28016, by rfl⟩ : syracuseStep 597685 = 56033) (by norm_num)
theorem B892613 : Blo 527800 892613 := bbase (se 4 (by rfl) ⟨83682, by rfl⟩ : syracuseStep 892613 = 167365) (by norm_num)
theorem B794309 : Blo 527800 794309 := bbase (se 4 (by rfl) ⟨74466, by rfl⟩ : syracuseStep 794309 = 148933) (by norm_num)
theorem B958157 : Blo 527800 958157 := bbase (se 3 (by rfl) ⟨179654, by rfl⟩ : syracuseStep 958157 = 359309) (by norm_num)
theorem B597721 : Blo 527800 597721 := bbase (se 2 (by rfl) ⟨224145, by rfl⟩ : syracuseStep 597721 = 448291) (by norm_num)
theorem B794333 : Blo 527800 794333 := bbase (se 3 (by rfl) ⟨148937, by rfl⟩ : syracuseStep 794333 = 297875) (by norm_num)
theorem B794357 : Blo 527800 794357 := bbase (se 5 (by rfl) ⟨37235, by rfl⟩ : syracuseStep 794357 = 74471) (by norm_num)
theorem B597757 : Blo 527800 597757 := bbase (se 3 (by rfl) ⟨112079, by rfl⟩ : syracuseStep 597757 = 224159) (by norm_num)
theorem B794381 : Blo 527800 794381 := bbase (se 3 (by rfl) ⟨148946, by rfl⟩ : syracuseStep 794381 = 297893) (by norm_num)
theorem B597793 : Blo 527800 597793 := bbase (se 2 (by rfl) ⟨224172, by rfl⟩ : syracuseStep 597793 = 448345) (by norm_num)
theorem B1187621 : Blo 527800 1187621 := bbase (se 4 (by rfl) ⟨111339, by rfl⟩ : syracuseStep 1187621 = 222679) (by norm_num)
theorem B794405 : Blo 527800 794405 := bbase (se 4 (by rfl) ⟨74475, by rfl⟩ : syracuseStep 794405 = 148951) (by norm_num)
theorem B794429 : Blo 527800 794429 := bbase (se 3 (by rfl) ⟨148955, by rfl⟩ : syracuseStep 794429 = 297911) (by norm_num)
theorem B892741 : Blo 527800 892741 := bbase (se 4 (by rfl) ⟨83694, by rfl⟩ : syracuseStep 892741 = 167389) (by norm_num)
theorem B597829 : Blo 527800 597829 := bbase (se 4 (by rfl) ⟨56046, by rfl⟩ : syracuseStep 597829 = 112093) (by norm_num)
theorem B794453 : Blo 527800 794453 := bbase (se 9 (by rfl) ⟨2327, by rfl⟩ : syracuseStep 794453 = 4655) (by norm_num)
theorem B597865 : Blo 527800 597865 := bbase (se 2 (by rfl) ⟨224199, by rfl⟩ : syracuseStep 597865 = 448399) (by norm_num)
theorem B1187693 : Blo 527800 1187693 := bbase (se 3 (by rfl) ⟨222692, by rfl⟩ : syracuseStep 1187693 = 445385) (by norm_num)
theorem B794477 : Blo 527800 794477 := bbase (se 3 (by rfl) ⟨148964, by rfl⟩ : syracuseStep 794477 = 297929) (by norm_num)
theorem B794501 : Blo 527800 794501 := bbase (se 4 (by rfl) ⟨74484, by rfl⟩ : syracuseStep 794501 = 148969) (by norm_num)
theorem B597901 : Blo 527800 597901 := bbase (se 3 (by rfl) ⟨112106, by rfl⟩ : syracuseStep 597901 = 224213) (by norm_num)
theorem B1908629 : Blo 527800 1908629 := bbase (se 6 (by rfl) ⟨44733, by rfl⟩ : syracuseStep 1908629 = 89467) (by norm_num)
theorem B892829 : Blo 527800 892829 := bbase (se 3 (by rfl) ⟨167405, by rfl⟩ : syracuseStep 892829 = 334811) (by norm_num)
theorem B794525 : Blo 527800 794525 := bbase (se 3 (by rfl) ⟨148973, by rfl⟩ : syracuseStep 794525 = 297947) (by norm_num)
theorem B565165 : Blo 527800 565165 := bbase (se 3 (by rfl) ⟨105968, by rfl⟩ : syracuseStep 565165 = 211937) (by norm_num)
theorem B597937 : Blo 527800 597937 := bbase (se 2 (by rfl) ⟨224226, by rfl⟩ : syracuseStep 597937 = 448453) (by norm_num)
theorem B1187765 : Blo 527800 1187765 := bbase (se 5 (by rfl) ⟨55676, by rfl⟩ : syracuseStep 1187765 = 111353) (by norm_num)
theorem B3383221 : Blo 527800 3383221 := bbase (se 5 (by rfl) ⟨158588, by rfl⟩ : syracuseStep 3383221 = 317177) (by norm_num)
theorem B794549 : Blo 527800 794549 := bbase (se 5 (by rfl) ⟨37244, by rfl⟩ : syracuseStep 794549 = 74489) (by norm_num)
theorem B794573 : Blo 527800 794573 := bbase (se 3 (by rfl) ⟨148982, by rfl⟩ : syracuseStep 794573 = 297965) (by norm_num)
theorem B597973 : Blo 527800 597973 := bbase (se 7 (by rfl) ⟨7007, by rfl⟩ : syracuseStep 597973 = 14015) (by norm_num)
theorem B794597 : Blo 527800 794597 := bbase (se 4 (by rfl) ⟨74493, by rfl⟩ : syracuseStep 794597 = 148987) (by norm_num)
theorem B565237 : Blo 527800 565237 := bbase (se 5 (by rfl) ⟨26495, by rfl⟩ : syracuseStep 565237 = 52991) (by norm_num)
theorem B598009 : Blo 527800 598009 := bbase (se 2 (by rfl) ⟨224253, by rfl⟩ : syracuseStep 598009 = 448507) (by norm_num)
theorem B794621 : Blo 527800 794621 := bbase (se 3 (by rfl) ⟨148991, by rfl⟩ : syracuseStep 794621 = 297983) (by norm_num)
theorem B1187837 : Blo 527800 1187837 := bbase (se 3 (by rfl) ⟨222719, by rfl⟩ : syracuseStep 1187837 = 445439) (by norm_num)
theorem B794645 : Blo 527800 794645 := bbase (se 6 (by rfl) ⟨18624, by rfl⟩ : syracuseStep 794645 = 37249) (by norm_num)
theorem B892957 : Blo 527800 892957 := bbase (se 3 (by rfl) ⟨167429, by rfl⟩ : syracuseStep 892957 = 334859) (by norm_num)
theorem B598045 : Blo 527800 598045 := bbase (se 3 (by rfl) ⟨112133, by rfl⟩ : syracuseStep 598045 = 224267) (by norm_num)
theorem B794669 : Blo 527800 794669 := bbase (se 3 (by rfl) ⟨149000, by rfl⟩ : syracuseStep 794669 = 298001) (by norm_num)
theorem B598081 : Blo 527800 598081 := bbase (se 2 (by rfl) ⟨224280, by rfl⟩ : syracuseStep 598081 = 448561) (by norm_num)
theorem B1187909 : Blo 527800 1187909 := bbase (se 4 (by rfl) ⟨111366, by rfl⟩ : syracuseStep 1187909 = 222733) (by norm_num)
theorem B794693 : Blo 527800 794693 := bbase (se 4 (by rfl) ⟨74502, by rfl⟩ : syracuseStep 794693 = 149005) (by norm_num)
theorem B630869 : Blo 527800 630869 := bbase (se 8 (by rfl) ⟨3696, by rfl⟩ : syracuseStep 630869 = 7393) (by norm_num)
theorem B794717 : Blo 527800 794717 := bbase (se 3 (by rfl) ⟨149009, by rfl⟩ : syracuseStep 794717 = 298019) (by norm_num)
theorem B598117 : Blo 527800 598117 := bbase (se 4 (by rfl) ⟨56073, by rfl⟩ : syracuseStep 598117 = 112147) (by norm_num)
theorem B893045 : Blo 527800 893045 := bbase (se 5 (by rfl) ⟨41861, by rfl⟩ : syracuseStep 893045 = 83723) (by norm_num)
theorem B794741 : Blo 527800 794741 := bbase (se 5 (by rfl) ⟨37253, by rfl⟩ : syracuseStep 794741 = 74507) (by norm_num)
theorem B598153 : Blo 527800 598153 := bbase (se 2 (by rfl) ⟨224307, by rfl⟩ : syracuseStep 598153 = 448615) (by norm_num)
theorem B1187981 : Blo 527800 1187981 := bbase (se 3 (by rfl) ⟨222746, by rfl⟩ : syracuseStep 1187981 = 445493) (by norm_num)
theorem B794765 : Blo 527800 794765 := bbase (se 3 (by rfl) ⟨149018, by rfl⟩ : syracuseStep 794765 = 298037) (by norm_num)
theorem B794789 : Blo 527800 794789 := bbase (se 4 (by rfl) ⟨74511, by rfl⟩ : syracuseStep 794789 = 149023) (by norm_num)
theorem B565417 : Blo 527800 565417 := bbase (se 2 (by rfl) ⟨212031, by rfl⟩ : syracuseStep 565417 = 424063) (by norm_num)
theorem B598189 : Blo 527800 598189 := bbase (se 3 (by rfl) ⟨112160, by rfl⟩ : syracuseStep 598189 = 224321) (by norm_num)
theorem B1810613 : Blo 527800 1810613 := bbase (se 5 (by rfl) ⟨84872, by rfl⟩ : syracuseStep 1810613 = 169745) (by norm_num)
theorem B794813 : Blo 527800 794813 := bbase (se 3 (by rfl) ⟨149027, by rfl⟩ : syracuseStep 794813 = 298055) (by norm_num)
theorem B598225 : Blo 527800 598225 := bbase (se 2 (by rfl) ⟨224334, by rfl⟩ : syracuseStep 598225 = 448669) (by norm_num)
theorem B1188053 : Blo 527800 1188053 := bbase (se 7 (by rfl) ⟨13922, by rfl⟩ : syracuseStep 1188053 = 27845) (by norm_num)
theorem B794837 : Blo 527800 794837 := bbase (se 7 (by rfl) ⟨9314, by rfl⟩ : syracuseStep 794837 = 18629) (by norm_num)
theorem B794861 : Blo 527800 794861 := bbase (se 3 (by rfl) ⟨149036, by rfl⟩ : syracuseStep 794861 = 298073) (by norm_num)
theorem B893173 : Blo 527800 893173 := bbase (se 5 (by rfl) ⟨41867, by rfl⟩ : syracuseStep 893173 = 83735) (by norm_num)
theorem B598261 : Blo 527800 598261 := bbase (se 5 (by rfl) ⟨28043, by rfl⟩ : syracuseStep 598261 = 56087) (by norm_num)
theorem B2007301 : Blo 527800 2007301 := bbase (se 4 (by rfl) ⟨188184, by rfl⟩ : syracuseStep 2007301 = 376369) (by norm_num)
theorem B794885 : Blo 527800 794885 := bbase (se 4 (by rfl) ⟨74520, by rfl⟩ : syracuseStep 794885 = 149041) (by norm_num)
theorem B1188125 : Blo 527800 1188125 := bbase (se 3 (by rfl) ⟨222773, by rfl⟩ : syracuseStep 1188125 = 445547) (by norm_num)
theorem B794909 : Blo 527800 794909 := bbase (se 3 (by rfl) ⟨149045, by rfl⟩ : syracuseStep 794909 = 298091) (by norm_num)
theorem B794933 : Blo 527800 794933 := bbase (se 5 (by rfl) ⟨37262, by rfl⟩ : syracuseStep 794933 = 74525) (by norm_num)
theorem B893261 : Blo 527800 893261 := bbase (se 3 (by rfl) ⟨167486, by rfl⟩ : syracuseStep 893261 = 334973) (by norm_num)
theorem B794957 : Blo 527800 794957 := bbase (se 3 (by rfl) ⟨149054, by rfl⟩ : syracuseStep 794957 = 298109) (by norm_num)
theorem B1188197 : Blo 527800 1188197 := bbase (se 4 (by rfl) ⟨111393, by rfl⟩ : syracuseStep 1188197 = 222787) (by norm_num)
theorem B794981 : Blo 527800 794981 := bbase (se 4 (by rfl) ⟨74529, by rfl⟩ : syracuseStep 794981 = 149059) (by norm_num)
theorem B795005 : Blo 527800 795005 := bbase (se 3 (by rfl) ⟨149063, by rfl⟩ : syracuseStep 795005 = 298127) (by norm_num)
theorem B795029 : Blo 527800 795029 := bbase (se 6 (by rfl) ⟨18633, by rfl⟩ : syracuseStep 795029 = 37267) (by norm_num)
theorem B1188269 : Blo 527800 1188269 := bbase (se 3 (by rfl) ⟨222800, by rfl⟩ : syracuseStep 1188269 = 445601) (by norm_num)
theorem B795053 : Blo 527800 795053 := bbase (se 3 (by rfl) ⟨149072, by rfl⟩ : syracuseStep 795053 = 298145) (by norm_num)
theorem B795077 : Blo 527800 795077 := bbase (se 4 (by rfl) ⟨74538, by rfl⟩ : syracuseStep 795077 = 149077) (by norm_num)
theorem B893389 : Blo 527800 893389 := bbase (se 3 (by rfl) ⟨167510, by rfl⟩ : syracuseStep 893389 = 335021) (by norm_num)
theorem B795101 : Blo 527800 795101 := bbase (se 3 (by rfl) ⟨149081, by rfl⟩ : syracuseStep 795101 = 298163) (by norm_num)
theorem B1188341 : Blo 527800 1188341 := bbase (se 5 (by rfl) ⟨55703, by rfl⟩ : syracuseStep 1188341 = 111407) (by norm_num)
theorem B795125 : Blo 527800 795125 := bbase (se 5 (by rfl) ⟨37271, by rfl⟩ : syracuseStep 795125 = 74543) (by norm_num)
theorem B795149 : Blo 527800 795149 := bbase (se 3 (by rfl) ⟨149090, by rfl⟩ : syracuseStep 795149 = 298181) (by norm_num)
theorem B893477 : Blo 527800 893477 := bbase (se 4 (by rfl) ⟨83763, by rfl⟩ : syracuseStep 893477 = 167527) (by norm_num)
theorem B795173 : Blo 527800 795173 := bbase (se 4 (by rfl) ⟨74547, by rfl⟩ : syracuseStep 795173 = 149095) (by norm_num)
theorem B2007605 : Blo 527800 2007605 := bbase (se 5 (by rfl) ⟨94106, by rfl⟩ : syracuseStep 2007605 = 188213) (by norm_num)
theorem B1188413 : Blo 527800 1188413 := bbase (se 3 (by rfl) ⟨222827, by rfl⟩ : syracuseStep 1188413 = 445655) (by norm_num)
theorem B795197 : Blo 527800 795197 := bbase (se 3 (by rfl) ⟨149099, by rfl⟩ : syracuseStep 795197 = 298199) (by norm_num)
theorem B795221 : Blo 527800 795221 := bbase (se 8 (by rfl) ⟨4659, by rfl⟩ : syracuseStep 795221 = 9319) (by norm_num)
theorem B565861 : Blo 527800 565861 := bbase (se 4 (by rfl) ⟨53049, by rfl⟩ : syracuseStep 565861 = 106099) (by norm_num)
theorem B795245 : Blo 527800 795245 := bbase (se 3 (by rfl) ⟨149108, by rfl⟩ : syracuseStep 795245 = 298217) (by norm_num)
theorem B1188485 : Blo 527800 1188485 := bbase (se 4 (by rfl) ⟨111420, by rfl⟩ : syracuseStep 1188485 = 222841) (by norm_num)
theorem B795269 : Blo 527800 795269 := bbase (se 4 (by rfl) ⟨74556, by rfl⟩ : syracuseStep 795269 = 149113) (by norm_num)
theorem B795293 : Blo 527800 795293 := bbase (se 3 (by rfl) ⟨149117, by rfl⟩ : syracuseStep 795293 = 298235) (by norm_num)
theorem B893605 : Blo 527800 893605 := bbase (se 4 (by rfl) ⟨83775, by rfl⟩ : syracuseStep 893605 = 167551) (by norm_num)
theorem B795317 : Blo 527800 795317 := bbase (se 5 (by rfl) ⟨37280, by rfl⟩ : syracuseStep 795317 = 74561) (by norm_num)
theorem B1188557 : Blo 527800 1188557 := bbase (se 3 (by rfl) ⟨222854, by rfl⟩ : syracuseStep 1188557 = 445709) (by norm_num)
theorem B795341 : Blo 527800 795341 := bbase (se 3 (by rfl) ⟨149126, by rfl⟩ : syracuseStep 795341 = 298253) (by norm_num)
theorem B565985 : Blo 527800 565985 := bbase (se 2 (by rfl) ⟨212244, by rfl⟩ : syracuseStep 565985 = 424489) (by norm_num)
theorem B795365 : Blo 527800 795365 := bbase (se 4 (by rfl) ⟨74565, by rfl⟩ : syracuseStep 795365 = 149131) (by norm_num)
theorem B893693 : Blo 527800 893693 := bbase (se 3 (by rfl) ⟨167567, by rfl⟩ : syracuseStep 893693 = 335135) (by norm_num)
theorem B795389 : Blo 527800 795389 := bbase (se 3 (by rfl) ⟨149135, by rfl⟩ : syracuseStep 795389 = 298271) (by norm_num)
theorem B1188629 : Blo 527800 1188629 := bbase (se 6 (by rfl) ⟨27858, by rfl⟩ : syracuseStep 1188629 = 55717) (by norm_num)
theorem B795413 : Blo 527800 795413 := bbase (se 6 (by rfl) ⟨18642, by rfl⟩ : syracuseStep 795413 = 37285) (by norm_num)
theorem B795437 : Blo 527800 795437 := bbase (se 3 (by rfl) ⟨149144, by rfl⟩ : syracuseStep 795437 = 298289) (by norm_num)
theorem B795461 : Blo 527800 795461 := bbase (se 4 (by rfl) ⟨74574, by rfl⟩ : syracuseStep 795461 = 149149) (by norm_num)
theorem B1188701 : Blo 527800 1188701 := bbase (se 3 (by rfl) ⟨222881, by rfl⟩ : syracuseStep 1188701 = 445763) (by norm_num)
theorem B795485 : Blo 527800 795485 := bbase (se 3 (by rfl) ⟨149153, by rfl⟩ : syracuseStep 795485 = 298307) (by norm_num)
theorem B795509 : Blo 527800 795509 := bbase (se 5 (by rfl) ⟨37289, by rfl⟩ : syracuseStep 795509 = 74579) (by norm_num)
theorem B893821 : Blo 527800 893821 := bbase (se 3 (by rfl) ⟨167591, by rfl⟩ : syracuseStep 893821 = 335183) (by norm_num)
theorem B795533 : Blo 527800 795533 := bbase (se 3 (by rfl) ⟨149162, by rfl⟩ : syracuseStep 795533 = 298325) (by norm_num)
theorem B1188773 : Blo 527800 1188773 := bbase (se 4 (by rfl) ⟨111447, by rfl⟩ : syracuseStep 1188773 = 222895) (by norm_num)
theorem B795557 : Blo 527800 795557 := bbase (se 4 (by rfl) ⟨74583, by rfl⟩ : syracuseStep 795557 = 149167) (by norm_num)
theorem B795581 : Blo 527800 795581 := bbase (se 3 (by rfl) ⟨149171, by rfl⟩ : syracuseStep 795581 = 298343) (by norm_num)
theorem B893909 : Blo 527800 893909 := bbase (se 7 (by rfl) ⟨10475, by rfl⟩ : syracuseStep 893909 = 20951) (by norm_num)
theorem B795605 : Blo 527800 795605 := bbase (se 7 (by rfl) ⟨9323, by rfl⟩ : syracuseStep 795605 = 18647) (by norm_num)
theorem B566237 : Blo 527800 566237 := bbase (se 3 (by rfl) ⟨106169, by rfl⟩ : syracuseStep 566237 = 212339) (by norm_num)
theorem B1188845 : Blo 527800 1188845 := bbase (se 3 (by rfl) ⟨222908, by rfl⟩ : syracuseStep 1188845 = 445817) (by norm_num)
theorem B795629 : Blo 527800 795629 := bbase (se 3 (by rfl) ⟨149180, by rfl⟩ : syracuseStep 795629 = 298361) (by norm_num)
theorem B795653 : Blo 527800 795653 := bbase (se 4 (by rfl) ⟨74592, by rfl⟩ : syracuseStep 795653 = 149185) (by norm_num)
theorem B795677 : Blo 527800 795677 := bbase (se 3 (by rfl) ⟨149189, by rfl⟩ : syracuseStep 795677 = 298379) (by norm_num)
theorem B1188917 : Blo 527800 1188917 := bbase (se 5 (by rfl) ⟨55730, by rfl⟩ : syracuseStep 1188917 = 111461) (by norm_num)
theorem B795701 : Blo 527800 795701 := bbase (se 5 (by rfl) ⟨37298, by rfl⟩ : syracuseStep 795701 = 74597) (by norm_num)
theorem B795725 : Blo 527800 795725 := bbase (se 3 (by rfl) ⟨149198, by rfl⟩ : syracuseStep 795725 = 298397) (by norm_num)
theorem B894037 : Blo 527800 894037 := bbase (se 8 (by rfl) ⟨5238, by rfl⟩ : syracuseStep 894037 = 10477) (by norm_num)
theorem B795749 : Blo 527800 795749 := bbase (se 4 (by rfl) ⟨74601, by rfl⟩ : syracuseStep 795749 = 149203) (by norm_num)
theorem B1188989 : Blo 527800 1188989 := bbase (se 3 (by rfl) ⟨222935, by rfl⟩ : syracuseStep 1188989 = 445871) (by norm_num)
theorem B795773 : Blo 527800 795773 := bbase (se 3 (by rfl) ⟨149207, by rfl⟩ : syracuseStep 795773 = 298415) (by norm_num)
theorem B1090685 : Blo 527800 1090685 := bbase (se 3 (by rfl) ⟨204503, by rfl⟩ : syracuseStep 1090685 = 409007) (by norm_num)
theorem B795797 : Blo 527800 795797 := bbase (se 6 (by rfl) ⟨18651, by rfl⟩ : syracuseStep 795797 = 37303) (by norm_num)
theorem B894125 : Blo 527800 894125 := bbase (se 3 (by rfl) ⟨167648, by rfl⟩ : syracuseStep 894125 = 335297) (by norm_num)
theorem B795821 : Blo 527800 795821 := bbase (se 3 (by rfl) ⟨149216, by rfl⟩ : syracuseStep 795821 = 298433) (by norm_num)
theorem B3024053 : Blo 527800 3024053 := bbase (se 5 (by rfl) ⟨141752, by rfl⟩ : syracuseStep 3024053 = 283505) (by norm_num)
theorem B1189061 : Blo 527800 1189061 := bbase (se 4 (by rfl) ⟨111474, by rfl⟩ : syracuseStep 1189061 = 222949) (by norm_num)
theorem B828613 : Blo 527800 828613 := bbase (se 4 (by rfl) ⟨77682, by rfl⟩ : syracuseStep 828613 = 155365) (by norm_num)
theorem B795845 : Blo 527800 795845 := bbase (se 4 (by rfl) ⟨74610, by rfl⟩ : syracuseStep 795845 = 149221) (by norm_num)
theorem B795869 : Blo 527800 795869 := bbase (se 3 (by rfl) ⟨149225, by rfl⟩ : syracuseStep 795869 = 298451) (by norm_num)
theorem B795893 : Blo 527800 795893 := bbase (se 5 (by rfl) ⟨37307, by rfl⟩ : syracuseStep 795893 = 74615) (by norm_num)
theorem B1189133 : Blo 527800 1189133 := bbase (se 3 (by rfl) ⟨222962, by rfl⟩ : syracuseStep 1189133 = 445925) (by norm_num)
theorem B795917 : Blo 527800 795917 := bbase (se 3 (by rfl) ⟨149234, by rfl⟩ : syracuseStep 795917 = 298469) (by norm_num)
theorem B795941 : Blo 527800 795941 := bbase (se 4 (by rfl) ⟨74619, by rfl⟩ : syracuseStep 795941 = 149239) (by norm_num)
theorem B2270501 : Blo 527800 2270501 := bbase (se 4 (by rfl) ⟨212859, by rfl⟩ : syracuseStep 2270501 = 425719) (by norm_num)
theorem B894253 : Blo 527800 894253 := bbase (se 3 (by rfl) ⟨167672, by rfl⟩ : syracuseStep 894253 = 335345) (by norm_num)
theorem B795965 : Blo 527800 795965 := bbase (se 3 (by rfl) ⟨149243, by rfl⟩ : syracuseStep 795965 = 298487) (by norm_num)
theorem B1189205 : Blo 527800 1189205 := bbase (se 12 (by rfl) ⟨435, by rfl⟩ : syracuseStep 1189205 = 871) (by norm_num)
theorem B795989 : Blo 527800 795989 := bbase (se 12 (by rfl) ⟨291, by rfl⟩ : syracuseStep 795989 = 583) (by norm_num)
theorem B796013 : Blo 527800 796013 := bbase (se 3 (by rfl) ⟨149252, by rfl⟩ : syracuseStep 796013 = 298505) (by norm_num)
theorem B894341 : Blo 527800 894341 := bbase (se 4 (by rfl) ⟨83844, by rfl⟩ : syracuseStep 894341 = 167689) (by norm_num)
theorem B796037 : Blo 527800 796037 := bbase (se 4 (by rfl) ⟨74628, by rfl⟩ : syracuseStep 796037 = 149257) (by norm_num)
theorem B566681 : Blo 527800 566681 := bbase (se 2 (by rfl) ⟨212505, by rfl⟩ : syracuseStep 566681 = 425011) (by norm_num)
theorem B1189277 : Blo 527800 1189277 := bbase (se 3 (by rfl) ⟨222989, by rfl⟩ : syracuseStep 1189277 = 445979) (by norm_num)
theorem B796061 : Blo 527800 796061 := bbase (se 3 (by rfl) ⟨149261, by rfl⟩ : syracuseStep 796061 = 298523) (by norm_num)
theorem B796085 : Blo 527800 796085 := bbase (se 5 (by rfl) ⟨37316, by rfl⟩ : syracuseStep 796085 = 74633) (by norm_num)
theorem B959941 : Blo 527800 959941 := bbase (se 4 (by rfl) ⟨89994, by rfl⟩ : syracuseStep 959941 = 179989) (by norm_num)
theorem B796109 : Blo 527800 796109 := bbase (se 3 (by rfl) ⟨149270, by rfl⟩ : syracuseStep 796109 = 298541) (by norm_num)
theorem B1189349 : Blo 527800 1189349 := bbase (se 4 (by rfl) ⟨111501, by rfl⟩ : syracuseStep 1189349 = 223003) (by norm_num)
theorem B796133 : Blo 527800 796133 := bbase (se 4 (by rfl) ⟨74637, by rfl⟩ : syracuseStep 796133 = 149275) (by norm_num)
theorem B796157 : Blo 527800 796157 := bbase (se 3 (by rfl) ⟨149279, by rfl⟩ : syracuseStep 796157 = 298559) (by norm_num)
theorem B894469 : Blo 527800 894469 := bbase (se 4 (by rfl) ⟨83856, by rfl⟩ : syracuseStep 894469 = 167713) (by norm_num)
theorem B796181 : Blo 527800 796181 := bbase (se 6 (by rfl) ⟨18660, by rfl⟩ : syracuseStep 796181 = 37321) (by norm_num)
theorem B1189421 : Blo 527800 1189421 := bbase (se 3 (by rfl) ⟨223016, by rfl⟩ : syracuseStep 1189421 = 446033) (by norm_num)
theorem B796205 : Blo 527800 796205 := bbase (se 3 (by rfl) ⟨149288, by rfl⟩ : syracuseStep 796205 = 298577) (by norm_num)
theorem B796229 : Blo 527800 796229 := bbase (se 4 (by rfl) ⟨74646, by rfl⟩ : syracuseStep 796229 = 149293) (by norm_num)
theorem B894557 : Blo 527800 894557 := bbase (se 3 (by rfl) ⟨167729, by rfl⟩ : syracuseStep 894557 = 335459) (by norm_num)
theorem B796253 : Blo 527800 796253 := bbase (se 3 (by rfl) ⟨149297, by rfl⟩ : syracuseStep 796253 = 298595) (by norm_num)
theorem B1189493 : Blo 527800 1189493 := bbase (se 5 (by rfl) ⟨55757, by rfl⟩ : syracuseStep 1189493 = 111515) (by norm_num)
theorem B796277 : Blo 527800 796277 := bbase (se 5 (by rfl) ⟨37325, by rfl⟩ : syracuseStep 796277 = 74651) (by norm_num)
theorem B796301 : Blo 527800 796301 := bbase (se 3 (by rfl) ⟨149306, by rfl⟩ : syracuseStep 796301 = 298613) (by norm_num)
theorem B566929 : Blo 527800 566929 := bbase (se 2 (by rfl) ⟨212598, by rfl⟩ : syracuseStep 566929 = 425197) (by norm_num)
theorem B796325 : Blo 527800 796325 := bbase (se 4 (by rfl) ⟨74655, by rfl⟩ : syracuseStep 796325 = 149311) (by norm_num)
theorem B1189565 : Blo 527800 1189565 := bbase (se 3 (by rfl) ⟨223043, by rfl⟩ : syracuseStep 1189565 = 446087) (by norm_num)
theorem B796349 : Blo 527800 796349 := bbase (se 3 (by rfl) ⟨149315, by rfl⟩ : syracuseStep 796349 = 298631) (by norm_num)
theorem B1287893 : Blo 527800 1287893 := bbase (se 7 (by rfl) ⟨15092, by rfl⟩ : syracuseStep 1287893 = 30185) (by norm_num)
theorem B796373 : Blo 527800 796373 := bbase (se 7 (by rfl) ⟨9332, by rfl⟩ : syracuseStep 796373 = 18665) (by norm_num)
theorem B894685 : Blo 527800 894685 := bbase (se 3 (by rfl) ⟨167753, by rfl⟩ : syracuseStep 894685 = 335507) (by norm_num)
theorem B796397 : Blo 527800 796397 := bbase (se 3 (by rfl) ⟨149324, by rfl⟩ : syracuseStep 796397 = 298649) (by norm_num)
theorem B1189637 : Blo 527800 1189637 := bbase (se 4 (by rfl) ⟨111528, by rfl⟩ : syracuseStep 1189637 = 223057) (by norm_num)
theorem B796421 : Blo 527800 796421 := bbase (se 4 (by rfl) ⟨74664, by rfl⟩ : syracuseStep 796421 = 149329) (by norm_num)
theorem B796445 : Blo 527800 796445 := bbase (se 3 (by rfl) ⟨149333, by rfl⟩ : syracuseStep 796445 = 298667) (by norm_num)
theorem B894773 : Blo 527800 894773 := bbase (se 5 (by rfl) ⟨41942, by rfl⟩ : syracuseStep 894773 = 83885) (by norm_num)
theorem B796469 : Blo 527800 796469 := bbase (se 5 (by rfl) ⟨37334, by rfl⟩ : syracuseStep 796469 = 74669) (by norm_num)
theorem B1189709 : Blo 527800 1189709 := bbase (se 3 (by rfl) ⟨223070, by rfl⟩ : syracuseStep 1189709 = 446141) (by norm_num)
theorem B796493 : Blo 527800 796493 := bbase (se 3 (by rfl) ⟨149342, by rfl⟩ : syracuseStep 796493 = 298685) (by norm_num)
theorem B796517 : Blo 527800 796517 := bbase (se 4 (by rfl) ⟨74673, by rfl⟩ : syracuseStep 796517 = 149347) (by norm_num)
theorem B1288045 : Blo 527800 1288045 := bbase (se 3 (by rfl) ⟨241508, by rfl⟩ : syracuseStep 1288045 = 483017) (by norm_num)
theorem B1615733 : Blo 527800 1615733 := bbase (se 5 (by rfl) ⟨75737, by rfl⟩ : syracuseStep 1615733 = 151475) (by norm_num)
theorem B796541 : Blo 527800 796541 := bbase (se 3 (by rfl) ⟨149351, by rfl⟩ : syracuseStep 796541 = 298703) (by norm_num)
theorem B2140037 : Blo 527800 2140037 := bbase (se 4 (by rfl) ⟨200628, by rfl⟩ : syracuseStep 2140037 = 401257) (by norm_num)
theorem B1189781 : Blo 527800 1189781 := bbase (se 6 (by rfl) ⟨27885, by rfl⟩ : syracuseStep 1189781 = 55771) (by norm_num)
theorem B796565 : Blo 527800 796565 := bbase (se 6 (by rfl) ⟨18669, by rfl⟩ : syracuseStep 796565 = 37339) (by norm_num)
theorem B796589 : Blo 527800 796589 := bbase (se 3 (by rfl) ⟨149360, by rfl⟩ : syracuseStep 796589 = 298721) (by norm_num)
theorem B894901 : Blo 527800 894901 := bbase (se 5 (by rfl) ⟨41948, by rfl⟩ : syracuseStep 894901 = 83897) (by norm_num)
theorem B796613 : Blo 527800 796613 := bbase (se 4 (by rfl) ⟨74682, by rfl⟩ : syracuseStep 796613 = 149365) (by norm_num)
theorem B1189853 : Blo 527800 1189853 := bbase (se 3 (by rfl) ⟨223097, by rfl⟩ : syracuseStep 1189853 = 446195) (by norm_num)
theorem B796637 : Blo 527800 796637 := bbase (se 3 (by rfl) ⟨149369, by rfl⟩ : syracuseStep 796637 = 298739) (by norm_num)
theorem B796661 : Blo 527800 796661 := bbase (se 5 (by rfl) ⟨37343, by rfl⟩ : syracuseStep 796661 = 74687) (by norm_num)
theorem B894989 : Blo 527800 894989 := bbase (se 3 (by rfl) ⟨167810, by rfl⟩ : syracuseStep 894989 = 335621) (by norm_num)
theorem B796685 : Blo 527800 796685 := bbase (se 3 (by rfl) ⟨149378, by rfl⟩ : syracuseStep 796685 = 298757) (by norm_num)
theorem B1189925 : Blo 527800 1189925 := bbase (se 4 (by rfl) ⟨111555, by rfl⟩ : syracuseStep 1189925 = 223111) (by norm_num)
theorem B796709 : Blo 527800 796709 := bbase (se 4 (by rfl) ⟨74691, by rfl⟩ : syracuseStep 796709 = 149383) (by norm_num)
theorem B796733 : Blo 527800 796733 := bbase (se 3 (by rfl) ⟨149387, by rfl⟩ : syracuseStep 796733 = 298775) (by norm_num)
theorem B567373 : Blo 527800 567373 := bbase (se 3 (by rfl) ⟨106382, by rfl⟩ : syracuseStep 567373 = 212765) (by norm_num)
theorem B5711957 : Blo 527800 5711957 := bbase (se 8 (by rfl) ⟨33468, by rfl⟩ : syracuseStep 5711957 = 66937) (by norm_num)
theorem B796757 : Blo 527800 796757 := bbase (se 8 (by rfl) ⟨4668, by rfl⟩ : syracuseStep 796757 = 9337) (by norm_num)
theorem B1189997 : Blo 527800 1189997 := bbase (se 3 (by rfl) ⟨223124, by rfl⟩ : syracuseStep 1189997 = 446249) (by norm_num)
theorem B796781 : Blo 527800 796781 := bbase (se 3 (by rfl) ⟨149396, by rfl⟩ : syracuseStep 796781 = 298793) (by norm_num)
theorem B796805 : Blo 527800 796805 := bbase (se 4 (by rfl) ⟨74700, by rfl⟩ : syracuseStep 796805 = 149401) (by norm_num)
theorem B567433 : Blo 527800 567433 := bbase (se 2 (by rfl) ⟨212787, by rfl⟩ : syracuseStep 567433 = 425575) (by norm_num)
theorem B895117 : Blo 527800 895117 := bbase (se 3 (by rfl) ⟨167834, by rfl⟩ : syracuseStep 895117 = 335669) (by norm_num)
theorem B796829 : Blo 527800 796829 := bbase (se 3 (by rfl) ⟨149405, by rfl⟩ : syracuseStep 796829 = 298811) (by norm_num)
theorem B1190069 : Blo 527800 1190069 := bbase (se 5 (by rfl) ⟨55784, by rfl⟩ : syracuseStep 1190069 = 111569) (by norm_num)
theorem B796853 : Blo 527800 796853 := bbase (se 5 (by rfl) ⟨37352, by rfl⟩ : syracuseStep 796853 = 74705) (by norm_num)
theorem B796877 : Blo 527800 796877 := bbase (se 3 (by rfl) ⟨149414, by rfl⟩ : syracuseStep 796877 = 298829) (by norm_num)
theorem B895205 : Blo 527800 895205 := bbase (se 4 (by rfl) ⟨83925, by rfl⟩ : syracuseStep 895205 = 167851) (by norm_num)
theorem B796901 : Blo 527800 796901 := bbase (se 4 (by rfl) ⟨74709, by rfl⟩ : syracuseStep 796901 = 149419) (by norm_num)
theorem B2894069 : Blo 527800 2894069 := bbase (se 5 (by rfl) ⟨135659, by rfl⟩ : syracuseStep 2894069 = 271319) (by norm_num)
theorem B1190141 : Blo 527800 1190141 := bbase (se 3 (by rfl) ⟨223151, by rfl⟩ : syracuseStep 1190141 = 446303) (by norm_num)
theorem B796925 : Blo 527800 796925 := bbase (se 3 (by rfl) ⟨149423, by rfl⟩ : syracuseStep 796925 = 298847) (by norm_num)
theorem B796949 : Blo 527800 796949 := bbase (se 6 (by rfl) ⟨18678, by rfl⟩ : syracuseStep 796949 = 37357) (by norm_num)
theorem B2271509 : Blo 527800 2271509 := bbase (se 6 (by rfl) ⟨53238, by rfl⟩ : syracuseStep 2271509 = 106477) (by norm_num)
theorem B796973 : Blo 527800 796973 := bbase (se 3 (by rfl) ⟨149432, by rfl⟩ : syracuseStep 796973 = 298865) (by norm_num)
theorem B1190213 : Blo 527800 1190213 := bbase (se 4 (by rfl) ⟨111582, by rfl⟩ : syracuseStep 1190213 = 223165) (by norm_num)
theorem B796997 : Blo 527800 796997 := bbase (se 4 (by rfl) ⟨74718, by rfl⟩ : syracuseStep 796997 = 149437) (by norm_num)
theorem B797021 : Blo 527800 797021 := bbase (se 3 (by rfl) ⟨149441, by rfl⟩ : syracuseStep 797021 = 298883) (by norm_num)
theorem B895333 : Blo 527800 895333 := bbase (se 4 (by rfl) ⟨83937, by rfl⟩ : syracuseStep 895333 = 167875) (by norm_num)
theorem B797045 : Blo 527800 797045 := bbase (se 5 (by rfl) ⟨37361, by rfl⟩ : syracuseStep 797045 = 74723) (by norm_num)
theorem B1190285 : Blo 527800 1190285 := bbase (se 3 (by rfl) ⟨223178, by rfl⟩ : syracuseStep 1190285 = 446357) (by norm_num)
theorem B797069 : Blo 527800 797069 := bbase (se 3 (by rfl) ⟨149450, by rfl⟩ : syracuseStep 797069 = 298901) (by norm_num)
theorem B797093 : Blo 527800 797093 := bbase (se 4 (by rfl) ⟨74727, by rfl⟩ : syracuseStep 797093 = 149455) (by norm_num)
theorem B895421 : Blo 527800 895421 := bbase (se 3 (by rfl) ⟨167891, by rfl⟩ : syracuseStep 895421 = 335783) (by norm_num)
theorem B797117 : Blo 527800 797117 := bbase (se 3 (by rfl) ⟨149459, by rfl⟩ : syracuseStep 797117 = 298919) (by norm_num)
theorem B567749 : Blo 527800 567749 := bbase (se 4 (by rfl) ⟨53226, by rfl⟩ : syracuseStep 567749 = 106453) (by norm_num)
theorem B1190357 : Blo 527800 1190357 := bbase (se 7 (by rfl) ⟨13949, by rfl⟩ : syracuseStep 1190357 = 27899) (by norm_num)
theorem B797141 : Blo 527800 797141 := bbase (se 7 (by rfl) ⟨9341, by rfl⟩ : syracuseStep 797141 = 18683) (by norm_num)
theorem B797165 : Blo 527800 797165 := bbase (se 3 (by rfl) ⟨149468, by rfl⟩ : syracuseStep 797165 = 298937) (by norm_num)
theorem B797189 : Blo 527800 797189 := bbase (se 4 (by rfl) ⟨74736, by rfl⟩ : syracuseStep 797189 = 149473) (by norm_num)
theorem B1190429 : Blo 527800 1190429 := bbase (se 3 (by rfl) ⟨223205, by rfl⟩ : syracuseStep 1190429 = 446411) (by norm_num)
theorem B797213 : Blo 527800 797213 := bbase (se 3 (by rfl) ⟨149477, by rfl⟩ : syracuseStep 797213 = 298955) (by norm_num)
theorem B797237 : Blo 527800 797237 := bbase (se 5 (by rfl) ⟨37370, by rfl⟩ : syracuseStep 797237 = 74741) (by norm_num)
theorem B895549 : Blo 527800 895549 := bbase (se 3 (by rfl) ⟨167915, by rfl⟩ : syracuseStep 895549 = 335831) (by norm_num)
theorem B797261 : Blo 527800 797261 := bbase (se 3 (by rfl) ⟨149486, by rfl⟩ : syracuseStep 797261 = 298973) (by norm_num)
theorem B1190501 : Blo 527800 1190501 := bbase (se 4 (by rfl) ⟨111609, by rfl⟩ : syracuseStep 1190501 = 223219) (by norm_num)
theorem B1911397 : Blo 527800 1911397 := bbase (se 4 (by rfl) ⟨179193, by rfl⟩ : syracuseStep 1911397 = 358387) (by norm_num)
theorem B797285 : Blo 527800 797285 := bbase (se 4 (by rfl) ⟨74745, by rfl⟩ : syracuseStep 797285 = 149491) (by norm_num)
theorem B2009717 : Blo 527800 2009717 := bbase (se 5 (by rfl) ⟨94205, by rfl⟩ : syracuseStep 2009717 = 188411) (by norm_num)
theorem B797309 : Blo 527800 797309 := bbase (se 3 (by rfl) ⟨149495, by rfl⟩ : syracuseStep 797309 = 298991) (by norm_num)
theorem B895637 : Blo 527800 895637 := bbase (se 6 (by rfl) ⟨20991, by rfl⟩ : syracuseStep 895637 = 41983) (by norm_num)
theorem B797333 : Blo 527800 797333 := bbase (se 6 (by rfl) ⟨18687, by rfl⟩ : syracuseStep 797333 = 37375) (by norm_num)
theorem B1190573 : Blo 527800 1190573 := bbase (se 3 (by rfl) ⟨223232, by rfl⟩ : syracuseStep 1190573 = 446465) (by norm_num)
theorem B797357 : Blo 527800 797357 := bbase (se 3 (by rfl) ⟨149504, by rfl⟩ : syracuseStep 797357 = 299009) (by norm_num)
theorem B797381 : Blo 527800 797381 := bbase (se 4 (by rfl) ⟨74754, by rfl⟩ : syracuseStep 797381 = 149509) (by norm_num)
theorem B3386069 : Blo 527800 3386069 := bbase (se 7 (by rfl) ⟨39680, by rfl⟩ : syracuseStep 3386069 = 79361) (by norm_num)
theorem B797405 : Blo 527800 797405 := bbase (se 3 (by rfl) ⟨149513, by rfl⟩ : syracuseStep 797405 = 299027) (by norm_num)
theorem B1190645 : Blo 527800 1190645 := bbase (se 5 (by rfl) ⟨55811, by rfl⟩ : syracuseStep 1190645 = 111623) (by norm_num)
theorem B797429 : Blo 527800 797429 := bbase (se 5 (by rfl) ⟨37379, by rfl⟩ : syracuseStep 797429 = 74759) (by norm_num)
theorem B797453 : Blo 527800 797453 := bbase (se 3 (by rfl) ⟨149522, by rfl⟩ : syracuseStep 797453 = 299045) (by norm_num)
theorem B895765 : Blo 527800 895765 := bbase (se 6 (by rfl) ⟨20994, by rfl⟩ : syracuseStep 895765 = 41989) (by norm_num)
theorem B797477 : Blo 527800 797477 := bbase (se 4 (by rfl) ⟨74763, by rfl⟩ : syracuseStep 797477 = 149527) (by norm_num)
theorem B1190717 : Blo 527800 1190717 := bbase (se 3 (by rfl) ⟨223259, by rfl⟩ : syracuseStep 1190717 = 446519) (by norm_num)
theorem B797501 : Blo 527800 797501 := bbase (se 3 (by rfl) ⟨149531, by rfl⟩ : syracuseStep 797501 = 299063) (by norm_num)
theorem B797525 : Blo 527800 797525 := bbase (se 9 (by rfl) ⟨2336, by rfl⟩ : syracuseStep 797525 = 4673) (by norm_num)
theorem B895853 : Blo 527800 895853 := bbase (se 3 (by rfl) ⟨167972, by rfl⟩ : syracuseStep 895853 = 335945) (by norm_num)
theorem B797549 : Blo 527800 797549 := bbase (se 3 (by rfl) ⟨149540, by rfl⟩ : syracuseStep 797549 = 299081) (by norm_num)
theorem B1190789 : Blo 527800 1190789 := bbase (se 4 (by rfl) ⟨111636, by rfl⟩ : syracuseStep 1190789 = 223273) (by norm_num)
theorem B797573 : Blo 527800 797573 := bbase (se 4 (by rfl) ⟨74772, by rfl⟩ : syracuseStep 797573 = 149545) (by norm_num)
theorem B2010005 : Blo 527800 2010005 := bbase (se 6 (by rfl) ⟨47109, by rfl⟩ : syracuseStep 2010005 = 94219) (by norm_num)
theorem B1911701 : Blo 527800 1911701 := bbase (se 6 (by rfl) ⟨44805, by rfl⟩ : syracuseStep 1911701 = 89611) (by norm_num)
theorem B1092509 : Blo 527800 1092509 := bbase (se 3 (by rfl) ⟨204845, by rfl⟩ : syracuseStep 1092509 = 409691) (by norm_num)
theorem B797597 : Blo 527800 797597 := bbase (se 3 (by rfl) ⟨149549, by rfl⟩ : syracuseStep 797597 = 299099) (by norm_num)
theorem B797621 : Blo 527800 797621 := bbase (se 5 (by rfl) ⟨37388, by rfl⟩ : syracuseStep 797621 = 74777) (by norm_num)
theorem B1190861 : Blo 527800 1190861 := bbase (se 3 (by rfl) ⟨223286, by rfl⟩ : syracuseStep 1190861 = 446573) (by norm_num)
theorem B797645 : Blo 527800 797645 := bbase (se 3 (by rfl) ⟨149558, by rfl⟩ : syracuseStep 797645 = 299117) (by norm_num)
theorem B797669 : Blo 527800 797669 := bbase (se 4 (by rfl) ⟨74781, by rfl⟩ : syracuseStep 797669 = 149563) (by norm_num)
theorem B895981 : Blo 527800 895981 := bbase (se 3 (by rfl) ⟨167996, by rfl⟩ : syracuseStep 895981 = 335993) (by norm_num)
theorem B797693 : Blo 527800 797693 := bbase (se 3 (by rfl) ⟨149567, by rfl⟩ : syracuseStep 797693 = 299135) (by norm_num)
theorem B1190933 : Blo 527800 1190933 := bbase (se 6 (by rfl) ⟨27912, by rfl⟩ : syracuseStep 1190933 = 55825) (by norm_num)
theorem B4009013 : Blo 527800 4009013 := bbase (se 5 (by rfl) ⟨187922, by rfl⟩ : syracuseStep 4009013 = 375845) (by norm_num)
theorem B896069 : Blo 527800 896069 := bbase (se 4 (by rfl) ⟨84006, by rfl⟩ : syracuseStep 896069 = 168013) (by norm_num)
theorem B1191005 : Blo 527800 1191005 := bbase (se 3 (by rfl) ⟨223313, by rfl⟩ : syracuseStep 1191005 = 446627) (by norm_num)
theorem B1191077 : Blo 527800 1191077 := bbase (se 4 (by rfl) ⟨111663, by rfl⟩ : syracuseStep 1191077 = 223327) (by norm_num)
theorem B896197 : Blo 527800 896197 := bbase (se 4 (by rfl) ⟨84018, by rfl⟩ : syracuseStep 896197 = 168037) (by norm_num)
theorem B1191149 : Blo 527800 1191149 := bbase (se 3 (by rfl) ⟨223340, by rfl⟩ : syracuseStep 1191149 = 446681) (by norm_num)
theorem B634105 : Blo 527800 634105 := bbase (se 2 (by rfl) ⟨237789, by rfl⟩ : syracuseStep 634105 = 475579) (by norm_num)
theorem B896285 : Blo 527800 896285 := bbase (se 3 (by rfl) ⟨168053, by rfl⟩ : syracuseStep 896285 = 336107) (by norm_num)
theorem B535853 : Blo 527800 535853 := bbase (se 3 (by rfl) ⟨100472, by rfl⟩ : syracuseStep 535853 = 200945) (by norm_num)
theorem B1191221 : Blo 527800 1191221 := bbase (se 5 (by rfl) ⟨55838, by rfl⟩ : syracuseStep 1191221 = 111677) (by norm_num)
theorem B3026261 : Blo 527800 3026261 := bbase (se 11 (by rfl) ⟨2216, by rfl⟩ : syracuseStep 3026261 = 4433) (by norm_num)
theorem B1191293 : Blo 527800 1191293 := bbase (se 3 (by rfl) ⟨223367, by rfl⟩ : syracuseStep 1191293 = 446735) (by norm_num)
theorem B896413 : Blo 527800 896413 := bbase (se 3 (by rfl) ⟨168077, by rfl⟩ : syracuseStep 896413 = 336155) (by norm_num)
theorem B634297 : Blo 527800 634297 := bbase (se 2 (by rfl) ⟨237861, by rfl⟩ : syracuseStep 634297 = 475723) (by norm_num)
theorem B1191365 : Blo 527800 1191365 := bbase (se 4 (by rfl) ⟨111690, by rfl⟩ : syracuseStep 1191365 = 223381) (by norm_num)
theorem B896501 : Blo 527800 896501 := bbase (se 5 (by rfl) ⟨42023, by rfl⟩ : syracuseStep 896501 = 84047) (by norm_num)
theorem B1191437 : Blo 527800 1191437 := bbase (se 3 (by rfl) ⟨223394, by rfl⟩ : syracuseStep 1191437 = 446789) (by norm_num)
theorem B634441 : Blo 527800 634441 := bbase (se 2 (by rfl) ⟨237915, by rfl⟩ : syracuseStep 634441 = 475831) (by norm_num)
theorem B1191509 : Blo 527800 1191509 := bbase (se 8 (by rfl) ⟨6981, by rfl⟩ : syracuseStep 1191509 = 13963) (by norm_num)
theorem B896629 : Blo 527800 896629 := bbase (se 5 (by rfl) ⟨42029, by rfl⟩ : syracuseStep 896629 = 84059) (by norm_num)
theorem B1191581 : Blo 527800 1191581 := bbase (se 3 (by rfl) ⟨223421, by rfl⟩ : syracuseStep 1191581 = 446843) (by norm_num)
theorem B1814197 : Blo 527800 1814197 := bbase (se 5 (by rfl) ⟨85040, by rfl⟩ : syracuseStep 1814197 = 170081) (by norm_num)
theorem B896717 : Blo 527800 896717 := bbase (se 3 (by rfl) ⟨168134, by rfl⟩ : syracuseStep 896717 = 336269) (by norm_num)
theorem B1191653 : Blo 527800 1191653 := bbase (se 4 (by rfl) ⟨111717, by rfl⟩ : syracuseStep 1191653 = 223435) (by norm_num)
theorem B1191725 : Blo 527800 1191725 := bbase (se 3 (by rfl) ⟨223448, by rfl⟩ : syracuseStep 1191725 = 446897) (by norm_num)
theorem B896845 : Blo 527800 896845 := bbase (se 3 (by rfl) ⟨168158, by rfl⟩ : syracuseStep 896845 = 336317) (by norm_num)
theorem B1781621 : Blo 527800 1781621 := bbase (se 5 (by rfl) ⟨83513, by rfl⟩ : syracuseStep 1781621 = 167027) (by norm_num)
theorem B1191797 : Blo 527800 1191797 := bbase (se 5 (by rfl) ⟨55865, by rfl⟩ : syracuseStep 1191797 = 111731) (by norm_num)
theorem B896933 : Blo 527800 896933 := bbase (se 4 (by rfl) ⟨84087, by rfl⟩ : syracuseStep 896933 = 168175) (by norm_num)
theorem B1191869 : Blo 527800 1191869 := bbase (se 3 (by rfl) ⟨223475, by rfl⟩ : syracuseStep 1191869 = 446951) (by norm_num)
theorem B1191941 : Blo 527800 1191941 := bbase (se 4 (by rfl) ⟨111744, by rfl⟩ : syracuseStep 1191941 = 223489) (by norm_num)
theorem B602137 : Blo 527800 602137 := bbase (se 2 (by rfl) ⟨225801, by rfl⟩ : syracuseStep 602137 = 451603) (by norm_num)
theorem B897061 : Blo 527800 897061 := bbase (se 4 (by rfl) ⟨84099, by rfl⟩ : syracuseStep 897061 = 168199) (by norm_num)
theorem B2011189 : Blo 527800 2011189 := bbase (se 5 (by rfl) ⟨94274, by rfl⟩ : syracuseStep 2011189 = 188549) (by norm_num)
theorem B1192013 : Blo 527800 1192013 := bbase (se 3 (by rfl) ⟨223502, by rfl⟩ : syracuseStep 1192013 = 447005) (by norm_num)
theorem B897149 : Blo 527800 897149 := bbase (se 3 (by rfl) ⟨168215, by rfl⟩ : syracuseStep 897149 = 336431) (by norm_num)
theorem B2044037 : Blo 527800 2044037 := bbase (se 4 (by rfl) ⟨191628, by rfl⟩ : syracuseStep 2044037 = 383257) (by norm_num)
theorem B536725 : Blo 527800 536725 := bbase (se 6 (by rfl) ⟨12579, by rfl⟩ : syracuseStep 536725 = 25159) (by norm_num)
theorem B1192085 : Blo 527800 1192085 := bbase (se 6 (by rfl) ⟨27939, by rfl⟩ : syracuseStep 1192085 = 55879) (by norm_num)
theorem B536737 : Blo 527800 536737 := bbase (se 2 (by rfl) ⟨201276, by rfl⟩ : syracuseStep 536737 = 402553) (by norm_num)
theorem B536761 : Blo 527800 536761 := bbase (se 2 (by rfl) ⟨201285, by rfl⟩ : syracuseStep 536761 = 402571) (by norm_num)
theorem B1192157 : Blo 527800 1192157 := bbase (se 3 (by rfl) ⟨223529, by rfl⟩ : syracuseStep 1192157 = 447059) (by norm_num)
theorem B897277 : Blo 527800 897277 := bbase (se 3 (by rfl) ⟨168239, by rfl⟩ : syracuseStep 897277 = 336479) (by norm_num)
theorem B602369 : Blo 527800 602369 := bbase (se 2 (by rfl) ⟨225888, by rfl⟩ : syracuseStep 602369 = 451777) (by norm_num)
theorem B1782053 : Blo 527800 1782053 := bbase (se 4 (by rfl) ⟨167067, by rfl⟩ : syracuseStep 1782053 = 334135) (by norm_num)
theorem B1192229 : Blo 527800 1192229 := bbase (se 4 (by rfl) ⟨111771, by rfl⟩ : syracuseStep 1192229 = 223543) (by norm_num)
theorem B897365 : Blo 527800 897365 := bbase (se 10 (by rfl) ⟨1314, by rfl⟩ : syracuseStep 897365 = 2629) (by norm_num)
theorem B2011493 : Blo 527800 2011493 := bbase (se 4 (by rfl) ⟨188577, by rfl⟩ : syracuseStep 2011493 = 377155) (by norm_num)
theorem B1192301 : Blo 527800 1192301 := bbase (se 3 (by rfl) ⟨223556, by rfl⟩ : syracuseStep 1192301 = 447113) (by norm_num)
theorem B668017 : Blo 527800 668017 := bbase (se 2 (by rfl) ⟨250506, by rfl⟩ : syracuseStep 668017 = 501013) (by norm_num)
theorem B1192373 : Blo 527800 1192373 := bbase (se 5 (by rfl) ⟨55892, by rfl⟩ : syracuseStep 1192373 = 111785) (by norm_num)
theorem B1192445 : Blo 527800 1192445 := bbase (se 3 (by rfl) ⟨223583, by rfl⟩ : syracuseStep 1192445 = 447167) (by norm_num)
theorem B668189 : Blo 527800 668189 := bbase (se 3 (by rfl) ⟨125285, by rfl⟩ : syracuseStep 668189 = 250571) (by norm_num)
theorem B1192517 : Blo 527800 1192517 := bbase (se 4 (by rfl) ⟨111798, by rfl⟩ : syracuseStep 1192517 = 223597) (by norm_num)
theorem B668245 : Blo 527800 668245 := bbase (se 8 (by rfl) ⟨3915, by rfl⟩ : syracuseStep 668245 = 7831) (by norm_num)
theorem B602725 : Blo 527800 602725 := bbase (se 4 (by rfl) ⟨56505, by rfl⟩ : syracuseStep 602725 = 113011) (by norm_num)
theorem B1192589 : Blo 527800 1192589 := bbase (se 3 (by rfl) ⟨223610, by rfl⟩ : syracuseStep 1192589 = 447221) (by norm_num)
theorem B1225373 : Blo 527800 1225373 := bbase (se 3 (by rfl) ⟨229757, by rfl⟩ : syracuseStep 1225373 = 459515) (by norm_num)
theorem B668341 : Blo 527800 668341 := bbase (se 5 (by rfl) ⟨31328, by rfl⟩ : syracuseStep 668341 = 62657) (by norm_num)
theorem B1782485 : Blo 527800 1782485 := bbase (se 7 (by rfl) ⟨20888, by rfl⟩ : syracuseStep 1782485 = 41777) (by norm_num)
theorem B1192661 : Blo 527800 1192661 := bbase (se 7 (by rfl) ⟨13976, by rfl⟩ : syracuseStep 1192661 = 27953) (by norm_num)
theorem B1192733 : Blo 527800 1192733 := bbase (se 3 (by rfl) ⟨223637, by rfl⟩ : syracuseStep 1192733 = 447275) (by norm_num)
theorem B668513 : Blo 527800 668513 := bbase (se 2 (by rfl) ⟨250692, by rfl⟩ : syracuseStep 668513 = 501385) (by norm_num)
theorem B1192805 : Blo 527800 1192805 := bbase (se 4 (by rfl) ⟨111825, by rfl⟩ : syracuseStep 1192805 = 223651) (by norm_num)
theorem B668569 : Blo 527800 668569 := bbase (se 2 (by rfl) ⟨250713, by rfl⟩ : syracuseStep 668569 = 501427) (by norm_num)
theorem B1192877 : Blo 527800 1192877 := bbase (se 3 (by rfl) ⟨223664, by rfl⟩ : syracuseStep 1192877 = 447329) (by norm_num)
theorem B1192949 : Blo 527800 1192949 := bbase (se 5 (by rfl) ⟨55919, by rfl⟩ : syracuseStep 1192949 = 111839) (by norm_num)
theorem B668665 : Blo 527800 668665 := bbase (se 2 (by rfl) ⟨250749, by rfl⟩ : syracuseStep 668665 = 501499) (by norm_num)
theorem B3224629 : Blo 527800 3224629 := bbase (se 5 (by rfl) ⟨151154, by rfl⟩ : syracuseStep 3224629 = 302309) (by norm_num)
theorem B1193021 : Blo 527800 1193021 := bbase (se 3 (by rfl) ⟨223691, by rfl⟩ : syracuseStep 1193021 = 447383) (by norm_num)
theorem B635969 : Blo 527800 635969 := bbase (se 2 (by rfl) ⟨238488, by rfl⟩ : syracuseStep 635969 = 476977) (by norm_num)
theorem B1782917 : Blo 527800 1782917 := bbase (se 4 (by rfl) ⟨167148, by rfl⟩ : syracuseStep 1782917 = 334297) (by norm_num)
theorem B1193093 : Blo 527800 1193093 := bbase (se 4 (by rfl) ⟨111852, by rfl⟩ : syracuseStep 1193093 = 223705) (by norm_num)
theorem B668837 : Blo 527800 668837 := bbase (se 4 (by rfl) ⟨62703, by rfl⟩ : syracuseStep 668837 = 125407) (by norm_num)
theorem B2143397 : Blo 527800 2143397 := bbase (se 4 (by rfl) ⟨200943, by rfl⟩ : syracuseStep 2143397 = 401887) (by norm_num)
theorem B1127621 : Blo 527800 1127621 := bbase (se 4 (by rfl) ⟨105714, by rfl⟩ : syracuseStep 1127621 = 211429) (by norm_num)
theorem B1193165 : Blo 527800 1193165 := bbase (se 3 (by rfl) ⟨223718, by rfl⟩ : syracuseStep 1193165 = 447437) (by norm_num)
theorem B668893 : Blo 527800 668893 := bbase (se 3 (by rfl) ⟨125417, by rfl⟩ : syracuseStep 668893 = 250835) (by norm_num)
theorem B1193237 : Blo 527800 1193237 := bbase (se 6 (by rfl) ⟨27966, by rfl⟩ : syracuseStep 1193237 = 55933) (by norm_num)
theorem B668989 : Blo 527800 668989 := bbase (se 3 (by rfl) ⟨125435, by rfl⟩ : syracuseStep 668989 = 250871) (by norm_num)
theorem B1193309 : Blo 527800 1193309 := bbase (se 3 (by rfl) ⟨223745, by rfl⟩ : syracuseStep 1193309 = 447491) (by norm_num)
theorem B636277 : Blo 527800 636277 := bbase (se 5 (by rfl) ⟨29825, by rfl⟩ : syracuseStep 636277 = 59651) (by norm_num)
theorem B1193381 : Blo 527800 1193381 := bbase (se 4 (by rfl) ⟨111879, by rfl⟩ : syracuseStep 1193381 = 223759) (by norm_num)
theorem B636373 : Blo 527800 636373 := bbase (se 7 (by rfl) ⟨7457, by rfl⟩ : syracuseStep 636373 = 14915) (by norm_num)
theorem B669161 : Blo 527800 669161 := bbase (se 2 (by rfl) ⟨250935, by rfl⟩ : syracuseStep 669161 = 501871) (by norm_num)
theorem B1193453 : Blo 527800 1193453 := bbase (se 3 (by rfl) ⟨223772, by rfl⟩ : syracuseStep 1193453 = 447545) (by norm_num)
theorem B669217 : Blo 527800 669217 := bbase (se 2 (by rfl) ⟨250956, by rfl⟩ : syracuseStep 669217 = 501913) (by norm_num)
theorem B1783349 : Blo 527800 1783349 := bbase (se 5 (by rfl) ⟨83594, by rfl⟩ : syracuseStep 1783349 = 167189) (by norm_num)
theorem B1193525 : Blo 527800 1193525 := bbase (se 5 (by rfl) ⟨55946, by rfl⟩ : syracuseStep 1193525 = 111893) (by norm_num)
theorem B1193597 : Blo 527800 1193597 := bbase (se 3 (by rfl) ⟨223799, by rfl⟩ : syracuseStep 1193597 = 447599) (by norm_num)
theorem B669313 : Blo 527800 669313 := bbase (se 2 (by rfl) ⟨250992, by rfl⟩ : syracuseStep 669313 = 501985) (by norm_num)
theorem B1193669 : Blo 527800 1193669 := bbase (se 4 (by rfl) ⟨111906, by rfl⟩ : syracuseStep 1193669 = 223813) (by norm_num)
theorem B603893 : Blo 527800 603893 := bbase (se 5 (by rfl) ⟨28307, by rfl⟩ : syracuseStep 603893 = 56615) (by norm_num)
theorem B636661 : Blo 527800 636661 := bbase (se 5 (by rfl) ⟨29843, by rfl⟩ : syracuseStep 636661 = 59687) (by norm_num)
theorem B1193741 : Blo 527800 1193741 := bbase (se 3 (by rfl) ⟨223826, by rfl⟩ : syracuseStep 1193741 = 447653) (by norm_num)
theorem B669485 : Blo 527800 669485 := bbase (se 3 (by rfl) ⟨125528, by rfl⟩ : syracuseStep 669485 = 251057) (by norm_num)
theorem B1193813 : Blo 527800 1193813 := bbase (se 9 (by rfl) ⟨3497, by rfl⟩ : syracuseStep 1193813 = 6995) (by norm_num)
theorem B669541 : Blo 527800 669541 := bbase (se 4 (by rfl) ⟨62769, by rfl⟩ : syracuseStep 669541 = 125539) (by norm_num)
theorem B1193885 : Blo 527800 1193885 := bbase (se 3 (by rfl) ⟨223853, by rfl⟩ : syracuseStep 1193885 = 447707) (by norm_num)
theorem B636853 : Blo 527800 636853 := bbase (se 5 (by rfl) ⟨29852, by rfl⟩ : syracuseStep 636853 = 59705) (by norm_num)
theorem B669637 : Blo 527800 669637 := bbase (se 4 (by rfl) ⟨62778, by rfl⟩ : syracuseStep 669637 = 125557) (by norm_num)
theorem B1783781 : Blo 527800 1783781 := bbase (se 4 (by rfl) ⟨167229, by rfl⟩ : syracuseStep 1783781 = 334459) (by norm_num)
theorem B1193957 : Blo 527800 1193957 := bbase (se 4 (by rfl) ⟨111933, by rfl⟩ : syracuseStep 1193957 = 223867) (by norm_num)
theorem B1128485 : Blo 527800 1128485 := bbase (se 4 (by rfl) ⟨105795, by rfl⟩ : syracuseStep 1128485 = 211591) (by norm_num)
theorem B1194029 : Blo 527800 1194029 := bbase (se 3 (by rfl) ⟨223880, by rfl⟩ : syracuseStep 1194029 = 447761) (by norm_num)
theorem B2046053 : Blo 527800 2046053 := bbase (se 4 (by rfl) ⟨191817, by rfl⟩ : syracuseStep 2046053 = 383635) (by norm_num)
theorem B669809 : Blo 527800 669809 := bbase (se 2 (by rfl) ⟨251178, by rfl⟩ : syracuseStep 669809 = 502357) (by norm_num)
theorem B1194101 : Blo 527800 1194101 := bbase (se 5 (by rfl) ⟨55973, by rfl⟩ : syracuseStep 1194101 = 111947) (by norm_num)
theorem B571529 : Blo 527800 571529 := bbase (se 2 (by rfl) ⟨214323, by rfl⟩ : syracuseStep 571529 = 428647) (by norm_num)
theorem B669865 : Blo 527800 669865 := bbase (se 2 (by rfl) ⟨251199, by rfl⟩ : syracuseStep 669865 = 502399) (by norm_num)
theorem B1128629 : Blo 527800 1128629 := bbase (se 5 (by rfl) ⟨52904, by rfl⟩ : syracuseStep 1128629 = 105809) (by norm_num)
theorem B1194173 : Blo 527800 1194173 := bbase (se 3 (by rfl) ⟨223907, by rfl⟩ : syracuseStep 1194173 = 447815) (by norm_num)
theorem B538813 : Blo 527800 538813 := bbase (se 3 (by rfl) ⟨101027, by rfl⟩ : syracuseStep 538813 = 202055) (by norm_num)
theorem B2865365 : Blo 527800 2865365 := bbase (se 7 (by rfl) ⟨33578, by rfl⟩ : syracuseStep 2865365 = 67157) (by norm_num)
theorem B1194245 : Blo 527800 1194245 := bbase (se 4 (by rfl) ⟨111960, by rfl⟩ : syracuseStep 1194245 = 223921) (by norm_num)
theorem B669961 : Blo 527800 669961 := bbase (se 2 (by rfl) ⟨251235, by rfl⟩ : syracuseStep 669961 = 502471) (by norm_num)
theorem B1194317 : Blo 527800 1194317 := bbase (se 3 (by rfl) ⟨223934, by rfl⟩ : syracuseStep 1194317 = 447869) (by norm_num)
theorem B1784213 : Blo 527800 1784213 := bbase (se 6 (by rfl) ⟨41817, by rfl⟩ : syracuseStep 1784213 = 83635) (by norm_num)
theorem B1194389 : Blo 527800 1194389 := bbase (se 6 (by rfl) ⟨27993, by rfl⟩ : syracuseStep 1194389 = 55987) (by norm_num)
theorem B2013605 : Blo 527800 2013605 := bbase (se 4 (by rfl) ⟨188775, by rfl⟩ : syracuseStep 2013605 = 377551) (by norm_num)
theorem B670133 : Blo 527800 670133 := bbase (se 5 (by rfl) ⟨31412, by rfl⟩ : syracuseStep 670133 = 62825) (by norm_num)
theorem B1194461 : Blo 527800 1194461 := bbase (se 3 (by rfl) ⟨223961, by rfl⟩ : syracuseStep 1194461 = 447923) (by norm_num)
theorem B670189 : Blo 527800 670189 := bbase (se 3 (by rfl) ⟨125660, by rfl⟩ : syracuseStep 670189 = 251321) (by norm_num)
theorem B1194533 : Blo 527800 1194533 := bbase (se 4 (by rfl) ⟨111987, by rfl⟩ : syracuseStep 1194533 = 223975) (by norm_num)
theorem B670285 : Blo 527800 670285 := bbase (se 3 (by rfl) ⟨125678, by rfl⟩ : syracuseStep 670285 = 251357) (by norm_num)
theorem B1194605 : Blo 527800 1194605 := bbase (se 3 (by rfl) ⟨223988, by rfl⟩ : syracuseStep 1194605 = 447977) (by norm_num)
theorem B10074773 : Blo 527800 10074773 := bbase (se 6 (by rfl) ⟨236127, by rfl⟩ : syracuseStep 10074773 = 472255) (by norm_num)
theorem B1194677 : Blo 527800 1194677 := bbase (se 5 (by rfl) ⟨56000, by rfl⟩ : syracuseStep 1194677 = 112001) (by norm_num)
theorem B2013893 : Blo 527800 2013893 := bbase (se 4 (by rfl) ⟨188802, by rfl⟩ : syracuseStep 2013893 = 377605) (by norm_num)
theorem B670457 : Blo 527800 670457 := bbase (se 2 (by rfl) ⟨251421, by rfl⟩ : syracuseStep 670457 = 502843) (by norm_num)
theorem B1194749 : Blo 527800 1194749 := bbase (se 3 (by rfl) ⟨224015, by rfl⟩ : syracuseStep 1194749 = 448031) (by norm_num)
theorem B637733 : Blo 527800 637733 := bbase (se 4 (by rfl) ⟨59787, by rfl⟩ : syracuseStep 637733 = 119575) (by norm_num)
theorem B670513 : Blo 527800 670513 := bbase (se 2 (by rfl) ⟨251442, by rfl⟩ : syracuseStep 670513 = 502885) (by norm_num)
theorem B1784645 : Blo 527800 1784645 := bbase (se 4 (by rfl) ⟨167310, by rfl⟩ : syracuseStep 1784645 = 334621) (by norm_num)
theorem B1194821 : Blo 527800 1194821 := bbase (se 4 (by rfl) ⟨112014, by rfl⟩ : syracuseStep 1194821 = 224029) (by norm_num)
theorem B4537205 : Blo 527800 4537205 := bbase (se 5 (by rfl) ⟨212681, by rfl⟩ : syracuseStep 4537205 = 425363) (by norm_num)
theorem B1194893 : Blo 527800 1194893 := bbase (se 3 (by rfl) ⟨224042, by rfl⟩ : syracuseStep 1194893 = 448085) (by norm_num)
theorem B670609 : Blo 527800 670609 := bbase (se 2 (by rfl) ⟨251478, by rfl⟩ : syracuseStep 670609 = 502957) (by norm_num)
theorem B1129373 : Blo 527800 1129373 := bbase (se 3 (by rfl) ⟨211757, by rfl⟩ : syracuseStep 1129373 = 423515) (by norm_num)
theorem B13581269 : Blo 527800 13581269 := bbase (se 7 (by rfl) ⟨159155, by rfl⟩ : syracuseStep 13581269 = 318311) (by norm_num)
theorem B1194965 : Blo 527800 1194965 := bbase (se 7 (by rfl) ⟨14003, by rfl⟩ : syracuseStep 1194965 = 28007) (by norm_num)
theorem B1195037 : Blo 527800 1195037 := bbase (se 3 (by rfl) ⟨224069, by rfl⟩ : syracuseStep 1195037 = 448139) (by norm_num)
theorem B670781 : Blo 527800 670781 := bbase (se 3 (by rfl) ⟨125771, by rfl⟩ : syracuseStep 670781 = 251543) (by norm_num)
theorem B1195109 : Blo 527800 1195109 := bbase (se 4 (by rfl) ⟨112041, by rfl⟩ : syracuseStep 1195109 = 224083) (by norm_num)
theorem B670837 : Blo 527800 670837 := bbase (se 5 (by rfl) ⟨31445, by rfl⟩ : syracuseStep 670837 = 62891) (by norm_num)
theorem B1195181 : Blo 527800 1195181 := bbase (se 3 (by rfl) ⟨224096, by rfl⟩ : syracuseStep 1195181 = 448193) (by norm_num)
theorem B670933 : Blo 527800 670933 := bbase (se 7 (by rfl) ⟨7862, by rfl⟩ : syracuseStep 670933 = 15725) (by norm_num)
theorem B1785077 : Blo 527800 1785077 := bbase (se 5 (by rfl) ⟨83675, by rfl⟩ : syracuseStep 1785077 = 167351) (by norm_num)
theorem B1195253 : Blo 527800 1195253 := bbase (se 5 (by rfl) ⟨56027, by rfl⟩ : syracuseStep 1195253 = 112055) (by norm_num)
theorem B638237 : Blo 527800 638237 := bbase (se 3 (by rfl) ⟨119669, by rfl⟩ : syracuseStep 638237 = 239339) (by norm_num)
theorem B1195325 : Blo 527800 1195325 := bbase (se 3 (by rfl) ⟨224123, by rfl⟩ : syracuseStep 1195325 = 448247) (by norm_num)
theorem B638285 : Blo 527800 638285 := bbase (se 3 (by rfl) ⟨119678, by rfl⟩ : syracuseStep 638285 = 239357) (by norm_num)
theorem B671105 : Blo 527800 671105 := bbase (se 2 (by rfl) ⟨251664, by rfl⟩ : syracuseStep 671105 = 503329) (by norm_num)
theorem B1195397 : Blo 527800 1195397 := bbase (se 4 (by rfl) ⟨112068, by rfl⟩ : syracuseStep 1195397 = 224137) (by norm_num)
theorem B671161 : Blo 527800 671161 := bbase (se 2 (by rfl) ⟨251685, by rfl⟩ : syracuseStep 671161 = 503371) (by norm_num)
theorem B1195469 : Blo 527800 1195469 := bbase (se 3 (by rfl) ⟨224150, by rfl⟩ : syracuseStep 1195469 = 448301) (by norm_num)
theorem B1818085 : Blo 527800 1818085 := bbase (se 4 (by rfl) ⟨170445, by rfl⟩ : syracuseStep 1818085 = 340891) (by norm_num)
theorem B2145781 : Blo 527800 2145781 := bbase (se 5 (by rfl) ⟨100583, by rfl⟩ : syracuseStep 2145781 = 201167) (by norm_num)
theorem B1195541 : Blo 527800 1195541 := bbase (se 6 (by rfl) ⟨28020, by rfl⟩ : syracuseStep 1195541 = 56041) (by norm_num)
theorem B671257 : Blo 527800 671257 := bbase (se 2 (by rfl) ⟨251721, by rfl⟩ : syracuseStep 671257 = 503443) (by norm_num)
theorem B638545 : Blo 527800 638545 := bbase (se 2 (by rfl) ⟨239454, by rfl⟩ : syracuseStep 638545 = 478909) (by norm_num)
theorem B1195613 : Blo 527800 1195613 := bbase (se 3 (by rfl) ⟨224177, by rfl⟩ : syracuseStep 1195613 = 448355) (by norm_num)
theorem B573053 : Blo 527800 573053 := bbase (se 3 (by rfl) ⟨107447, by rfl⟩ : syracuseStep 573053 = 214895) (by norm_num)
theorem B1130125 : Blo 527800 1130125 := bbase (se 3 (by rfl) ⟨211898, by rfl⟩ : syracuseStep 1130125 = 423797) (by norm_num)
theorem B1785509 : Blo 527800 1785509 := bbase (se 4 (by rfl) ⟨167391, by rfl⟩ : syracuseStep 1785509 = 334783) (by norm_num)
theorem B1195685 : Blo 527800 1195685 := bbase (se 4 (by rfl) ⟨112095, by rfl⟩ : syracuseStep 1195685 = 224191) (by norm_num)
theorem B671429 : Blo 527800 671429 := bbase (se 4 (by rfl) ⟨62946, by rfl⟩ : syracuseStep 671429 = 125893) (by norm_num)
theorem B1195757 : Blo 527800 1195757 := bbase (se 3 (by rfl) ⟨224204, by rfl⟩ : syracuseStep 1195757 = 448409) (by norm_num)
theorem B671485 : Blo 527800 671485 := bbase (se 3 (by rfl) ⟨125903, by rfl⟩ : syracuseStep 671485 = 251807) (by norm_num)
theorem B1130269 : Blo 527800 1130269 := bbase (se 3 (by rfl) ⟨211925, by rfl⟩ : syracuseStep 1130269 = 423851) (by norm_num)
theorem B1195829 : Blo 527800 1195829 := bbase (se 5 (by rfl) ⟨56054, by rfl⟩ : syracuseStep 1195829 = 112109) (by norm_num)
theorem B638809 : Blo 527800 638809 := bbase (se 2 (by rfl) ⟨239553, by rfl⟩ : syracuseStep 638809 = 479107) (by norm_num)
theorem B671581 : Blo 527800 671581 := bbase (se 3 (by rfl) ⟨125921, by rfl⟩ : syracuseStep 671581 = 251843) (by norm_num)
theorem B2015077 : Blo 527800 2015077 := bbase (se 4 (by rfl) ⟨188913, by rfl⟩ : syracuseStep 2015077 = 377827) (by norm_num)
theorem B1195901 : Blo 527800 1195901 := bbase (se 3 (by rfl) ⟨224231, by rfl⟩ : syracuseStep 1195901 = 448463) (by norm_num)
theorem B1195973 : Blo 527800 1195973 := bbase (se 4 (by rfl) ⟨112122, by rfl⟩ : syracuseStep 1195973 = 224245) (by norm_num)
theorem B573409 : Blo 527800 573409 := bbase (se 2 (by rfl) ⟨215028, by rfl⟩ : syracuseStep 573409 = 430057) (by norm_num)
theorem B671753 : Blo 527800 671753 := bbase (se 2 (by rfl) ⟨251907, by rfl⟩ : syracuseStep 671753 = 503815) (by norm_num)
theorem B1196045 : Blo 527800 1196045 := bbase (se 3 (by rfl) ⟨224258, by rfl⟩ : syracuseStep 1196045 = 448517) (by norm_num)
theorem B671809 : Blo 527800 671809 := bbase (se 2 (by rfl) ⟨251928, by rfl⟩ : syracuseStep 671809 = 503857) (by norm_num)
theorem B1785941 : Blo 527800 1785941 := bbase (se 8 (by rfl) ⟨10464, by rfl⟩ : syracuseStep 1785941 = 20929) (by norm_num)
theorem B1196117 : Blo 527800 1196117 := bbase (se 8 (by rfl) ⟨7008, by rfl⟩ : syracuseStep 1196117 = 14017) (by norm_num)
theorem B1130645 : Blo 527800 1130645 := bbase (se 6 (by rfl) ⟨26499, by rfl⟩ : syracuseStep 1130645 = 52999) (by norm_num)
theorem B2015381 : Blo 527800 2015381 := bbase (se 6 (by rfl) ⟨47235, by rfl⟩ : syracuseStep 2015381 = 94471) (by norm_num)
theorem B1196189 : Blo 527800 1196189 := bbase (se 3 (by rfl) ⟨224285, by rfl⟩ : syracuseStep 1196189 = 448571) (by norm_num)
theorem B671905 : Blo 527800 671905 := bbase (se 2 (by rfl) ⟨251964, by rfl⟩ : syracuseStep 671905 = 503929) (by norm_num)
theorem B1196261 : Blo 527800 1196261 := bbase (se 4 (by rfl) ⟨112149, by rfl⟩ : syracuseStep 1196261 = 224299) (by norm_num)
theorem B1196333 : Blo 527800 1196333 := bbase (se 3 (by rfl) ⟨224312, by rfl⟩ : syracuseStep 1196333 = 448625) (by norm_num)
theorem B672077 : Blo 527800 672077 := bbase (se 3 (by rfl) ⟨126014, by rfl⟩ : syracuseStep 672077 = 252029) (by norm_num)
theorem B1196405 : Blo 527800 1196405 := bbase (se 5 (by rfl) ⟨56081, by rfl⟩ : syracuseStep 1196405 = 112163) (by norm_num)
theorem B672133 : Blo 527800 672133 := bbase (se 4 (by rfl) ⟨63012, by rfl⟩ : syracuseStep 672133 = 126025) (by norm_num)
theorem B1196477 : Blo 527800 1196477 := bbase (se 3 (by rfl) ⟨224339, by rfl⟩ : syracuseStep 1196477 = 448679) (by norm_num)
theorem B1524197 : Blo 527800 1524197 := bbase (se 4 (by rfl) ⟨142893, by rfl⟩ : syracuseStep 1524197 = 285787) (by norm_num)
theorem B672229 : Blo 527800 672229 := bbase (se 4 (by rfl) ⟨63021, by rfl⟩ : syracuseStep 672229 = 126043) (by norm_num)
theorem B1786373 : Blo 527800 1786373 := bbase (se 4 (by rfl) ⟨167472, by rfl⟩ : syracuseStep 1786373 = 334945) (by norm_num)
theorem B1131013 : Blo 527800 1131013 := bbase (se 4 (by rfl) ⟨106032, by rfl⟩ : syracuseStep 1131013 = 212065) (by norm_num)
theorem B1196549 : Blo 527800 1196549 := bbase (se 4 (by rfl) ⟨112176, by rfl⟩ : syracuseStep 1196549 = 224353) (by norm_num)
theorem B3195413 : Blo 527800 3195413 := bbase (se 6 (by rfl) ⟨74892, by rfl⟩ : syracuseStep 3195413 = 149785) (by norm_num)
theorem B672401 : Blo 527800 672401 := bbase (se 2 (by rfl) ⟨252150, by rfl⟩ : syracuseStep 672401 = 504301) (by norm_num)
theorem B803501 : Blo 527800 803501 := bbase (se 3 (by rfl) ⟨150656, by rfl⟩ : syracuseStep 803501 = 301313) (by norm_num)
theorem B672457 : Blo 527800 672457 := bbase (se 2 (by rfl) ⟨252171, by rfl⟩ : syracuseStep 672457 = 504343) (by norm_num)
theorem B2540261 : Blo 527800 2540261 := bbase (se 4 (by rfl) ⟨238149, by rfl⟩ : syracuseStep 2540261 = 476299) (by norm_num)
theorem B672553 : Blo 527800 672553 := bbase (se 2 (by rfl) ⟨252207, by rfl⟩ : syracuseStep 672553 = 504415) (by norm_num)
theorem B1786805 : Blo 527800 1786805 := bbase (se 5 (by rfl) ⟨83756, by rfl⟩ : syracuseStep 1786805 = 167513) (by norm_num)
theorem B672725 : Blo 527800 672725 := bbase (se 7 (by rfl) ⟨7883, by rfl⟩ : syracuseStep 672725 = 15767) (by norm_num)
theorem B672781 : Blo 527800 672781 := bbase (se 3 (by rfl) ⟨126146, by rfl⟩ : syracuseStep 672781 = 252293) (by norm_num)
theorem B672877 : Blo 527800 672877 := bbase (se 3 (by rfl) ⟨126164, by rfl⟩ : syracuseStep 672877 = 252329) (by norm_num)
theorem B673049 : Blo 527800 673049 := bbase (se 2 (by rfl) ⟨252393, by rfl⟩ : syracuseStep 673049 = 504787) (by norm_num)
theorem B1787237 : Blo 527800 1787237 := bbase (se 4 (by rfl) ⟨167553, by rfl⟩ : syracuseStep 1787237 = 335107) (by norm_num)
theorem B968053 : Blo 527800 968053 := bbase (se 5 (by rfl) ⟨45377, by rfl⟩ : syracuseStep 968053 = 90755) (by norm_num)
theorem B574993 : Blo 527800 574993 := bbase (se 2 (by rfl) ⟨215622, by rfl⟩ : syracuseStep 574993 = 431245) (by norm_num)
theorem B1787669 : Blo 527800 1787669 := bbase (se 6 (by rfl) ⟨41898, by rfl⟩ : syracuseStep 1787669 = 83797) (by norm_num)
theorem B1165117 : Blo 527800 1165117 := bbase (se 3 (by rfl) ⟨218459, by rfl⟩ : syracuseStep 1165117 = 436919) (by norm_num)
theorem B1132517 : Blo 527800 1132517 := bbase (se 4 (by rfl) ⟨106173, by rfl⟩ : syracuseStep 1132517 = 212347) (by norm_num)
theorem B1132661 : Blo 527800 1132661 := bbase (se 5 (by rfl) ⟨53093, by rfl⟩ : syracuseStep 1132661 = 106187) (by norm_num)
theorem B1722485 : Blo 527800 1722485 := bbase (se 5 (by rfl) ⟨80741, by rfl⟩ : syracuseStep 1722485 = 161483) (by norm_num)
theorem B903349 : Blo 527800 903349 := bbase (se 5 (by rfl) ⟨42344, by rfl⟩ : syracuseStep 903349 = 84689) (by norm_num)
theorem B2672837 : Blo 527800 2672837 := bbase (se 4 (by rfl) ⟨250578, by rfl⟩ : syracuseStep 2672837 = 501157) (by norm_num)
theorem B1788101 : Blo 527800 1788101 := bbase (se 4 (by rfl) ⟨167634, by rfl⟩ : syracuseStep 1788101 = 335269) (by norm_num)
theorem B1362125 : Blo 527800 1362125 := bbase (se 3 (by rfl) ⟨255398, by rfl⟩ : syracuseStep 1362125 = 510797) (by norm_num)
theorem B2017493 : Blo 527800 2017493 := bbase (se 7 (by rfl) ⟨23642, by rfl⟩ : syracuseStep 2017493 = 47285) (by norm_num)
theorem B1427861 : Blo 527800 1427861 := bbase (se 6 (by rfl) ⟨33465, by rfl⟩ : syracuseStep 1427861 = 66931) (by norm_num)
theorem B2574773 : Blo 527800 2574773 := bbase (se 5 (by rfl) ⟨120692, by rfl⟩ : syracuseStep 2574773 = 241385) (by norm_num)
theorem B1133021 : Blo 527800 1133021 := bbase (se 3 (by rfl) ⟨212441, by rfl⟩ : syracuseStep 1133021 = 424883) (by norm_num)
theorem B2017781 : Blo 527800 2017781 := bbase (se 5 (by rfl) ⟨94583, by rfl⟩ : syracuseStep 2017781 = 189167) (by norm_num)
theorem B1788533 : Blo 527800 1788533 := bbase (se 5 (by rfl) ⟨83837, by rfl⟩ : syracuseStep 1788533 = 167675) (by norm_num)
theorem B1002125 : Blo 527800 1002125 := bbase (se 3 (by rfl) ⟨187898, by rfl⟩ : syracuseStep 1002125 = 375797) (by norm_num)
theorem B4016789 : Blo 527800 4016789 := bbase (se 6 (by rfl) ⟨94143, by rfl⟩ : syracuseStep 4016789 = 188287) (by norm_num)
theorem B1002269 : Blo 527800 1002269 := bbase (se 3 (by rfl) ⟨187925, by rfl⟩ : syracuseStep 1002269 = 375851) (by norm_num)
theorem B1526597 : Blo 527800 1526597 := bbase (se 4 (by rfl) ⟨143118, by rfl⟩ : syracuseStep 1526597 = 286237) (by norm_num)
theorem B1788965 : Blo 527800 1788965 := bbase (se 4 (by rfl) ⟨167715, by rfl⟩ : syracuseStep 1788965 = 335431) (by norm_num)
theorem B1002557 : Blo 527800 1002557 := bbase (se 3 (by rfl) ⟨187979, by rfl⟩ : syracuseStep 1002557 = 375959) (by norm_num)
theorem B2411669 : Blo 527800 2411669 := bbase (se 6 (by rfl) ⟨56523, by rfl⟩ : syracuseStep 2411669 = 113047) (by norm_num)
theorem B1526933 : Blo 527800 1526933 := bbase (se 6 (by rfl) ⟨35787, by rfl⟩ : syracuseStep 1526933 = 71575) (by norm_num)
theorem B1002709 : Blo 527800 1002709 := bbase (se 7 (by rfl) ⟨11750, by rfl⟩ : syracuseStep 1002709 = 23501) (by norm_num)
theorem B1133909 : Blo 527800 1133909 := bbase (se 11 (by rfl) ⟨830, by rfl⟩ : syracuseStep 1133909 = 1661) (by norm_num)
theorem B2674133 : Blo 527800 2674133 := bbase (se 7 (by rfl) ⟨31337, by rfl⟩ : syracuseStep 2674133 = 62675) (by norm_num)
theorem B1789397 : Blo 527800 1789397 := bbase (se 7 (by rfl) ⟨20969, by rfl⟩ : syracuseStep 1789397 = 41939) (by norm_num)
theorem B1003013 : Blo 527800 1003013 := bbase (se 4 (by rfl) ⟨94032, by rfl⟩ : syracuseStep 1003013 = 188065) (by norm_num)
theorem B1691189 : Blo 527800 1691189 := bbase (se 5 (by rfl) ⟨79274, by rfl⟩ : syracuseStep 1691189 = 158549) (by norm_num)
theorem B1134157 : Blo 527800 1134157 := bbase (se 3 (by rfl) ⟨212654, by rfl⟩ : syracuseStep 1134157 = 425309) (by norm_num)
theorem B2018965 : Blo 527800 2018965 := bbase (se 6 (by rfl) ⟨47319, by rfl⟩ : syracuseStep 2018965 = 94639) (by norm_num)
theorem B806645 : Blo 527800 806645 := bbase (se 5 (by rfl) ⟨37811, by rfl⟩ : syracuseStep 806645 = 75623) (by norm_num)
theorem B3624725 : Blo 527800 3624725 := bbase (se 6 (by rfl) ⟨84954, by rfl⟩ : syracuseStep 3624725 = 169909) (by norm_num)
theorem B2543413 : Blo 527800 2543413 := bbase (se 5 (by rfl) ⟨119222, by rfl⟩ : syracuseStep 2543413 = 238445) (by norm_num)
theorem B1789829 : Blo 527800 1789829 := bbase (se 4 (by rfl) ⟨167796, by rfl⟩ : syracuseStep 1789829 = 335593) (by norm_num)
theorem B806869 : Blo 527800 806869 := bbase (se 7 (by rfl) ⟨9455, by rfl⟩ : syracuseStep 806869 = 18911) (by norm_num)
theorem B1134661 : Blo 527800 1134661 := bbase (se 4 (by rfl) ⟨106374, by rfl⟩ : syracuseStep 1134661 = 212749) (by norm_num)
theorem B1003765 : Blo 527800 1003765 := bbase (se 5 (by rfl) ⟨47051, by rfl⟩ : syracuseStep 1003765 = 94103) (by norm_num)
theorem B1790261 : Blo 527800 1790261 := bbase (se 5 (by rfl) ⟨83918, by rfl⟩ : syracuseStep 1790261 = 167837) (by norm_num)
theorem B708949 : Blo 527800 708949 := bbase (se 10 (by rfl) ⟨1038, by rfl⟩ : syracuseStep 708949 = 2077) (by norm_num)
theorem B1003909 : Blo 527800 1003909 := bbase (se 4 (by rfl) ⟨94116, by rfl⟩ : syracuseStep 1003909 = 188233) (by norm_num)
theorem B610801 : Blo 527800 610801 := bbase (se 2 (by rfl) ⟨229050, by rfl⟩ : syracuseStep 610801 = 458101) (by norm_num)
theorem B1004069 : Blo 527800 1004069 := bbase (se 4 (by rfl) ⟨94131, by rfl⟩ : syracuseStep 1004069 = 188263) (by norm_num)
theorem B1004213 : Blo 527800 1004213 := bbase (se 5 (by rfl) ⟨47072, by rfl⟩ : syracuseStep 1004213 = 94145) (by norm_num)
theorem B2675429 : Blo 527800 2675429 := bbase (se 4 (by rfl) ⟨250821, by rfl⟩ : syracuseStep 2675429 = 501643) (by norm_num)
theorem B1790693 : Blo 527800 1790693 := bbase (se 4 (by rfl) ⟨167877, by rfl⟩ : syracuseStep 1790693 = 335755) (by norm_num)
theorem B1430261 : Blo 527800 1430261 := bbase (se 5 (by rfl) ⟨67043, by rfl⟩ : syracuseStep 1430261 = 134087) (by norm_num)
theorem B3822389 : Blo 527800 3822389 := bbase (se 5 (by rfl) ⟨179174, by rfl⟩ : syracuseStep 3822389 = 358349) (by norm_num)
theorem B1037125 : Blo 527800 1037125 := bbase (se 4 (by rfl) ⟨97230, by rfl⟩ : syracuseStep 1037125 = 194461) (by norm_num)
theorem B1692533 : Blo 527800 1692533 := bbase (se 5 (by rfl) ⟨79337, by rfl⟩ : syracuseStep 1692533 = 158675) (by norm_num)
theorem B1135549 : Blo 527800 1135549 := bbase (se 3 (by rfl) ⟨212915, by rfl⟩ : syracuseStep 1135549 = 425831) (by norm_num)
theorem B1004501 : Blo 527800 1004501 := bbase (se 7 (by rfl) ⟨11771, by rfl⟩ : syracuseStep 1004501 = 23543) (by norm_num)
theorem B906277 : Blo 527800 906277 := bbase (se 4 (by rfl) ⟨84963, by rfl⟩ : syracuseStep 906277 = 169927) (by norm_num)
theorem B808013 : Blo 527800 808013 := bbase (se 3 (by rfl) ⟨151502, by rfl⟩ : syracuseStep 808013 = 303005) (by norm_num)
theorem B1004653 : Blo 527800 1004653 := bbase (se 3 (by rfl) ⟨188372, by rfl⟩ : syracuseStep 1004653 = 376745) (by norm_num)
theorem B1791125 : Blo 527800 1791125 := bbase (se 6 (by rfl) ⟨41979, by rfl⟩ : syracuseStep 1791125 = 83959) (by norm_num)
theorem B2151701 : Blo 527800 2151701 := bbase (se 6 (by rfl) ⟨50430, by rfl⟩ : syracuseStep 2151701 = 100861) (by norm_num)
theorem B1004957 : Blo 527800 1004957 := bbase (se 3 (by rfl) ⟨188429, by rfl⟩ : syracuseStep 1004957 = 376859) (by norm_num)
theorem B1791557 : Blo 527800 1791557 := bbase (se 4 (by rfl) ⟨167958, by rfl⟩ : syracuseStep 1791557 = 335917) (by norm_num)
theorem B1070725 : Blo 527800 1070725 := bbase (se 4 (by rfl) ⟨100380, by rfl⟩ : syracuseStep 1070725 = 200761) (by norm_num)
theorem B644969 : Blo 527800 644969 := bbase (se 2 (by rfl) ⟨241863, by rfl⟩ : syracuseStep 644969 = 483727) (by norm_num)
theorem B6805397 : Blo 527800 6805397 := bbase (se 6 (by rfl) ⟨159501, by rfl⟩ : syracuseStep 6805397 = 319003) (by norm_num)
theorem B2414549 : Blo 527800 2414549 := bbase (se 7 (by rfl) ⟨28295, by rfl⟩ : syracuseStep 2414549 = 56591) (by norm_num)
theorem B2676725 : Blo 527800 2676725 := bbase (se 5 (by rfl) ⟨125471, by rfl⟩ : syracuseStep 2676725 = 250943) (by norm_num)
theorem B1791989 : Blo 527800 1791989 := bbase (se 5 (by rfl) ⟨83999, by rfl⟩ : syracuseStep 1791989 = 167999) (by norm_num)
theorem B1071245 : Blo 527800 1071245 := bbase (se 3 (by rfl) ⟨200858, by rfl⟩ : syracuseStep 1071245 = 401717) (by norm_num)
theorem B1005709 : Blo 527800 1005709 := bbase (se 3 (by rfl) ⟨188570, by rfl⟩ : syracuseStep 1005709 = 377141) (by norm_num)
theorem B1005853 : Blo 527800 1005853 := bbase (se 3 (by rfl) ⟨188597, by rfl⟩ : syracuseStep 1005853 = 377195) (by norm_num)
theorem B1136941 : Blo 527800 1136941 := bbase (se 3 (by rfl) ⟨213176, by rfl⟩ : syracuseStep 1136941 = 426353) (by norm_num)
theorem B1792421 : Blo 527800 1792421 := bbase (se 4 (by rfl) ⟨168039, by rfl⟩ : syracuseStep 1792421 = 336079) (by norm_num)
theorem B1006013 : Blo 527800 1006013 := bbase (se 3 (by rfl) ⟨188627, by rfl⟩ : syracuseStep 1006013 = 377255) (by norm_num)
theorem B2447941 : Blo 527800 2447941 := bbase (se 4 (by rfl) ⟨229494, by rfl⟩ : syracuseStep 2447941 = 458989) (by norm_num)
theorem B1006157 : Blo 527800 1006157 := bbase (se 3 (by rfl) ⟨188654, by rfl⟩ : syracuseStep 1006157 = 377309) (by norm_num)
theorem B2546261 : Blo 527800 2546261 := bbase (se 8 (by rfl) ⟨14919, by rfl⟩ : syracuseStep 2546261 = 29839) (by norm_num)
theorem B1071805 : Blo 527800 1071805 := bbase (se 3 (by rfl) ⟨200963, by rfl⟩ : syracuseStep 1071805 = 401927) (by norm_num)
theorem B1694533 : Blo 527800 1694533 := bbase (se 4 (by rfl) ⟨158862, by rfl⟩ : syracuseStep 1694533 = 317725) (by norm_num)
theorem B1792853 : Blo 527800 1792853 := bbase (se 9 (by rfl) ⟨5252, by rfl⟩ : syracuseStep 1792853 = 10505) (by norm_num)
theorem B1006445 : Blo 527800 1006445 := bbase (se 3 (by rfl) ⟨188708, by rfl⟩ : syracuseStep 1006445 = 377417) (by norm_num)
theorem B1006597 : Blo 527800 1006597 := bbase (se 4 (by rfl) ⟨94368, by rfl⟩ : syracuseStep 1006597 = 188737) (by norm_num)
theorem B2678021 : Blo 527800 2678021 := bbase (se 4 (by rfl) ⟨251064, by rfl⟩ : syracuseStep 2678021 = 502129) (by norm_num)
theorem B1793285 : Blo 527800 1793285 := bbase (se 4 (by rfl) ⟨168120, by rfl⟩ : syracuseStep 1793285 = 336241) (by norm_num)
theorem B1006901 : Blo 527800 1006901 := bbase (se 5 (by rfl) ⟨47198, by rfl⟩ : syracuseStep 1006901 = 94397) (by norm_num)
theorem B1072453 : Blo 527800 1072453 := bbase (se 4 (by rfl) ⟨100542, by rfl⟩ : syracuseStep 1072453 = 201085) (by norm_num)
theorem B1072549 : Blo 527800 1072549 := bbase (se 4 (by rfl) ⟨100551, by rfl⟩ : syracuseStep 1072549 = 201103) (by norm_num)
theorem B3825269 : Blo 527800 3825269 := bbase (se 5 (by rfl) ⟨179309, by rfl⟩ : syracuseStep 3825269 = 358619) (by norm_num)
theorem B3399317 : Blo 527800 3399317 := bbase (se 6 (by rfl) ⟨79671, by rfl⟩ : syracuseStep 3399317 = 159343) (by norm_num)
theorem B1793717 : Blo 527800 1793717 := bbase (se 5 (by rfl) ⟨84080, by rfl⟩ : syracuseStep 1793717 = 168161) (by norm_num)
theorem B2547605 : Blo 527800 2547605 := bbase (se 6 (by rfl) ⟨59709, by rfl⟩ : syracuseStep 2547605 = 119419) (by norm_num)
theorem B1007653 : Blo 527800 1007653 := bbase (se 4 (by rfl) ⟨94467, by rfl⟩ : syracuseStep 1007653 = 188935) (by norm_num)
theorem B1794149 : Blo 527800 1794149 := bbase (se 4 (by rfl) ⟨168201, by rfl⟩ : syracuseStep 1794149 = 336403) (by norm_num)
theorem B1007797 : Blo 527800 1007797 := bbase (se 5 (by rfl) ⟨47240, by rfl⟩ : syracuseStep 1007797 = 94481) (by norm_num)
theorem B1270093 : Blo 527800 1270093 := bbase (se 3 (by rfl) ⟨238142, by rfl⟩ : syracuseStep 1270093 = 476285) (by norm_num)
theorem B1007957 : Blo 527800 1007957 := bbase (se 10 (by rfl) ⟨1476, by rfl⟩ : syracuseStep 1007957 = 2953) (by norm_num)
theorem B680293 : Blo 527800 680293 := bbase (se 4 (by rfl) ⟨63777, by rfl⟩ : syracuseStep 680293 = 127555) (by norm_num)
theorem B1270237 : Blo 527800 1270237 := bbase (se 3 (by rfl) ⟨238169, by rfl⟩ : syracuseStep 1270237 = 476339) (by norm_num)
theorem B1008101 : Blo 527800 1008101 := bbase (se 4 (by rfl) ⟨94509, by rfl⟩ : syracuseStep 1008101 = 189019) (by norm_num)
theorem B2679317 : Blo 527800 2679317 := bbase (se 6 (by rfl) ⟨62796, by rfl⟩ : syracuseStep 2679317 = 125593) (by norm_num)
theorem B1794581 : Blo 527800 1794581 := bbase (se 6 (by rfl) ⟨42060, by rfl⟩ : syracuseStep 1794581 = 84121) (by norm_num)
theorem B680653 : Blo 527800 680653 := bbase (se 3 (by rfl) ⟨127622, by rfl⟩ : syracuseStep 680653 = 255245) (by norm_num)
theorem B1008389 : Blo 527800 1008389 := bbase (se 4 (by rfl) ⟨94536, by rfl⟩ : syracuseStep 1008389 = 189073) (by norm_num)
theorem B1336085 : Blo 527800 1336085 := bbase (se 6 (by rfl) ⟨31314, by rfl⟩ : syracuseStep 1336085 = 62629) (by norm_num)
theorem B1008541 : Blo 527800 1008541 := bbase (se 3 (by rfl) ⟨189101, by rfl⟩ : syracuseStep 1008541 = 378203) (by norm_num)
theorem B1336277 : Blo 527800 1336277 := bbase (se 7 (by rfl) ⟨15659, by rfl⟩ : syracuseStep 1336277 = 31319) (by norm_num)
theorem B2155477 : Blo 527800 2155477 := bbase (se 7 (by rfl) ⟨25259, by rfl⟩ : syracuseStep 2155477 = 50519) (by norm_num)
theorem B1270853 : Blo 527800 1270853 := bbase (se 4 (by rfl) ⟨119142, by rfl⟩ : syracuseStep 1270853 = 238285) (by norm_num)
theorem B1008845 : Blo 527800 1008845 := bbase (se 3 (by rfl) ⟨189158, by rfl⟩ : syracuseStep 1008845 = 378317) (by norm_num)
theorem B4515061 : Blo 527800 4515061 := bbase (se 5 (by rfl) ⟨211643, by rfl⟩ : syracuseStep 4515061 = 423287) (by norm_num)
theorem B1336621 : Blo 527800 1336621 := bbase (se 3 (by rfl) ⟨250616, by rfl⟩ : syracuseStep 1336621 = 501233) (by norm_num)
theorem B1271189 : Blo 527800 1271189 := bbase (se 6 (by rfl) ⟨29793, by rfl⟩ : syracuseStep 1271189 = 59587) (by norm_num)
theorem B1336733 : Blo 527800 1336733 := bbase (se 3 (by rfl) ⟨250637, by rfl⟩ : syracuseStep 1336733 = 501275) (by norm_num)
theorem B1271285 : Blo 527800 1271285 := bbase (se 5 (by rfl) ⟨59591, by rfl⟩ : syracuseStep 1271285 = 119183) (by norm_num)
theorem B1336925 : Blo 527800 1336925 := bbase (se 3 (by rfl) ⟨250673, by rfl⟩ : syracuseStep 1336925 = 501347) (by norm_num)
theorem B1271477 : Blo 527800 1271477 := bbase (se 5 (by rfl) ⟨59600, by rfl⟩ : syracuseStep 1271477 = 119201) (by norm_num)
theorem B1697557 : Blo 527800 1697557 := bbase (se 6 (by rfl) ⟨39786, by rfl⟩ : syracuseStep 1697557 = 79573) (by norm_num)
theorem B2680613 : Blo 527800 2680613 := bbase (se 4 (by rfl) ⟨251307, by rfl⟩ : syracuseStep 2680613 = 502615) (by norm_num)
theorem B2254661 : Blo 527800 2254661 := bbase (se 4 (by rfl) ⟨211374, by rfl⟩ : syracuseStep 2254661 = 422749) (by norm_num)
theorem B6022997 : Blo 527800 6022997 := bbase (se 9 (by rfl) ⟨17645, by rfl⟩ : syracuseStep 6022997 = 35291) (by norm_num)
theorem B1337269 : Blo 527800 1337269 := bbase (se 5 (by rfl) ⟨62684, by rfl⟩ : syracuseStep 1337269 = 125369) (by norm_num)
theorem B1337381 : Blo 527800 1337381 := bbase (se 4 (by rfl) ⟨125379, by rfl⟩ : syracuseStep 1337381 = 250759) (by norm_num)
theorem B1337573 : Blo 527800 1337573 := bbase (se 4 (by rfl) ⟨125397, by rfl⟩ : syracuseStep 1337573 = 250795) (by norm_num)
theorem B714989 : Blo 527800 714989 := bbase (se 3 (by rfl) ⟨134060, by rfl⟩ : syracuseStep 714989 = 268121) (by norm_num)
theorem B4024565 : Blo 527800 4024565 := bbase (se 5 (by rfl) ⟨188651, by rfl⟩ : syracuseStep 4024565 = 377303) (by norm_num)
theorem B846229 : Blo 527800 846229 := bbase (se 6 (by rfl) ⟨19833, by rfl⟩ : syracuseStep 846229 = 39667) (by norm_num)
theorem B1337917 : Blo 527800 1337917 := bbase (se 3 (by rfl) ⟨250859, by rfl⟩ : syracuseStep 1337917 = 501719) (by norm_num)
theorem B1338029 : Blo 527800 1338029 := bbase (se 3 (by rfl) ⟨250880, by rfl⟩ : syracuseStep 1338029 = 501761) (by norm_num)
theorem B1272629 : Blo 527800 1272629 := bbase (se 5 (by rfl) ⟨59654, by rfl⟩ : syracuseStep 1272629 = 119309) (by norm_num)
theorem B846677 : Blo 527800 846677 := bbase (se 9 (by rfl) ⟨2480, by rfl⟩ : syracuseStep 846677 = 4961) (by norm_num)
theorem B1338221 : Blo 527800 1338221 := bbase (se 3 (by rfl) ⟨250916, by rfl⟩ : syracuseStep 1338221 = 501833) (by norm_num)
theorem B1436629 : Blo 527800 1436629 := bbase (se 7 (by rfl) ⟨16835, by rfl⟩ : syracuseStep 1436629 = 33671) (by norm_num)
theorem B2419733 : Blo 527800 2419733 := bbase (se 6 (by rfl) ⟨56712, by rfl⟩ : syracuseStep 2419733 = 113425) (by norm_num)
theorem B2681909 : Blo 527800 2681909 := bbase (se 5 (by rfl) ⟨125714, by rfl⟩ : syracuseStep 2681909 = 251429) (by norm_num)
theorem B551993 : Blo 527800 551993 := bbase (se 2 (by rfl) ⟨206997, by rfl⟩ : syracuseStep 551993 = 413995) (by norm_num)
theorem B4517045 : Blo 527800 4517045 := bbase (se 5 (by rfl) ⟨211736, by rfl⟩ : syracuseStep 4517045 = 423473) (by norm_num)
theorem B1338565 : Blo 527800 1338565 := bbase (se 4 (by rfl) ⟨125490, by rfl⟩ : syracuseStep 1338565 = 250981) (by norm_num)
theorem B1338677 : Blo 527800 1338677 := bbase (se 5 (by rfl) ⟨62750, by rfl⟩ : syracuseStep 1338677 = 125501) (by norm_num)
theorem B1338869 : Blo 527800 1338869 := bbase (se 5 (by rfl) ⟨62759, by rfl⟩ : syracuseStep 1338869 = 125519) (by norm_num)
theorem B2551333 : Blo 527800 2551333 := bbase (se 4 (by rfl) ⟨239187, by rfl⟩ : syracuseStep 2551333 = 478375) (by norm_num)
theorem B2256437 : Blo 527800 2256437 := bbase (se 5 (by rfl) ⟨105770, by rfl⟩ : syracuseStep 2256437 = 211541) (by norm_num)
theorem B1339213 : Blo 527800 1339213 := bbase (se 3 (by rfl) ⟨251102, by rfl⟩ : syracuseStep 1339213 = 502205) (by norm_num)
theorem B1339325 : Blo 527800 1339325 := bbase (se 3 (by rfl) ⟨251123, by rfl⟩ : syracuseStep 1339325 = 502247) (by norm_num)
theorem B1929205 : Blo 527800 1929205 := bbase (se 5 (by rfl) ⟨90431, by rfl⟩ : syracuseStep 1929205 = 180863) (by norm_num)
theorem B2355317 : Blo 527800 2355317 := bbase (se 5 (by rfl) ⟨110405, by rfl⟩ : syracuseStep 2355317 = 220811) (by norm_num)
theorem B1339517 : Blo 527800 1339517 := bbase (se 3 (by rfl) ⟨251159, by rfl⟩ : syracuseStep 1339517 = 502319) (by norm_num)
theorem B1503461 : Blo 527800 1503461 := bbase (se 4 (by rfl) ⟨140949, by rfl⟩ : syracuseStep 1503461 = 281899) (by norm_num)
theorem B848189 : Blo 527800 848189 := bbase (se 3 (by rfl) ⟨159035, by rfl⟩ : syracuseStep 848189 = 318071) (by norm_num)
theorem B2683205 : Blo 527800 2683205 := bbase (se 4 (by rfl) ⟨251550, by rfl⟩ : syracuseStep 2683205 = 503101) (by norm_num)
theorem B848317 : Blo 527800 848317 := bbase (se 3 (by rfl) ⟨159059, by rfl⟩ : syracuseStep 848317 = 318119) (by norm_num)
theorem B1339861 : Blo 527800 1339861 := bbase (se 7 (by rfl) ⟨15701, by rfl⟩ : syracuseStep 1339861 = 31403) (by norm_num)
theorem B717277 : Blo 527800 717277 := bbase (se 3 (by rfl) ⟨134489, by rfl⟩ : syracuseStep 717277 = 268979) (by norm_num)
theorem B2257429 : Blo 527800 2257429 := bbase (se 6 (by rfl) ⟨52908, by rfl⟩ : syracuseStep 2257429 = 105817) (by norm_num)
theorem B1339973 : Blo 527800 1339973 := bbase (se 4 (by rfl) ⟨125622, by rfl⟩ : syracuseStep 1339973 = 251245) (by norm_num)
theorem B1700453 : Blo 527800 1700453 := bbase (se 4 (by rfl) ⟨159417, by rfl⟩ : syracuseStep 1700453 = 318835) (by norm_num)
theorem B717541 : Blo 527800 717541 := bbase (se 4 (by rfl) ⟨67269, by rfl⟩ : syracuseStep 717541 = 134539) (by norm_num)
theorem B1340165 : Blo 527800 1340165 := bbase (se 4 (by rfl) ⟨125640, by rfl⟩ : syracuseStep 1340165 = 251281) (by norm_num)
theorem B1274629 : Blo 527800 1274629 := bbase (se 4 (by rfl) ⟨119496, by rfl⟩ : syracuseStep 1274629 = 238993) (by norm_num)
theorem B1274725 : Blo 527800 1274725 := bbase (se 4 (by rfl) ⟨119505, by rfl⟩ : syracuseStep 1274725 = 239011) (by norm_num)
theorem B1504133 : Blo 527800 1504133 := bbase (se 4 (by rfl) ⟨141012, by rfl⟩ : syracuseStep 1504133 = 282025) (by norm_num)
theorem B1340509 : Blo 527800 1340509 := bbase (se 3 (by rfl) ⟨251345, by rfl⟩ : syracuseStep 1340509 = 502691) (by norm_num)
theorem B1635509 : Blo 527800 1635509 := bbase (se 5 (by rfl) ⟨76664, by rfl⟩ : syracuseStep 1635509 = 153329) (by norm_num)
theorem B1340621 : Blo 527800 1340621 := bbase (se 3 (by rfl) ⟨251366, by rfl⟩ : syracuseStep 1340621 = 502733) (by norm_num)
theorem B1504565 : Blo 527800 1504565 := bbase (se 5 (by rfl) ⟨70526, by rfl⟩ : syracuseStep 1504565 = 141053) (by norm_num)
theorem B1144133 : Blo 527800 1144133 := bbase (se 4 (by rfl) ⟨107262, by rfl⟩ : syracuseStep 1144133 = 214525) (by norm_num)
theorem B1340813 : Blo 527800 1340813 := bbase (se 3 (by rfl) ⟨251402, by rfl⟩ : syracuseStep 1340813 = 502805) (by norm_num)
theorem B1209821 : Blo 527800 1209821 := bbase (se 3 (by rfl) ⟨226841, by rfl⟩ : syracuseStep 1209821 = 453683) (by norm_num)
theorem B3405365 : Blo 527800 3405365 := bbase (se 5 (by rfl) ⟨159626, by rfl⟩ : syracuseStep 3405365 = 319253) (by norm_num)
theorem B2684501 : Blo 527800 2684501 := bbase (se 8 (by rfl) ⟨15729, by rfl⟩ : syracuseStep 2684501 = 31459) (by norm_num)
theorem B1341157 : Blo 527800 1341157 := bbase (se 4 (by rfl) ⟨125733, by rfl⟩ : syracuseStep 1341157 = 251467) (by norm_num)
theorem B849701 : Blo 527800 849701 := bbase (se 4 (by rfl) ⟨79659, by rfl⟩ : syracuseStep 849701 = 159319) (by norm_num)
theorem B1341269 : Blo 527800 1341269 := bbase (se 9 (by rfl) ⟨3929, by rfl⟩ : syracuseStep 1341269 = 7859) (by norm_num)
theorem B1701749 : Blo 527800 1701749 := bbase (se 5 (by rfl) ⟨79769, by rfl⟩ : syracuseStep 1701749 = 159539) (by norm_num)
theorem B1275821 : Blo 527800 1275821 := bbase (se 3 (by rfl) ⟨239216, by rfl⟩ : syracuseStep 1275821 = 478433) (by norm_num)
theorem B751565 : Blo 527800 751565 := bbase (se 3 (by rfl) ⟨140918, by rfl⟩ : syracuseStep 751565 = 281837) (by norm_num)
theorem B1341461 : Blo 527800 1341461 := bbase (se 6 (by rfl) ⟨31440, by rfl⟩ : syracuseStep 1341461 = 62881) (by norm_num)
theorem B1505317 : Blo 527800 1505317 := bbase (se 4 (by rfl) ⟨141123, by rfl⟩ : syracuseStep 1505317 = 282247) (by norm_num)
theorem B3012821 : Blo 527800 3012821 := bbase (se 7 (by rfl) ⟨35306, by rfl⟩ : syracuseStep 3012821 = 70613) (by norm_num)
theorem B1341805 : Blo 527800 1341805 := bbase (se 3 (by rfl) ⟨251588, by rfl⟩ : syracuseStep 1341805 = 503177) (by norm_num)
theorem B1341917 : Blo 527800 1341917 := bbase (se 3 (by rfl) ⟨251609, by rfl⟩ : syracuseStep 1341917 = 503219) (by norm_num)
theorem B1342109 : Blo 527800 1342109 := bbase (se 3 (by rfl) ⟨251645, by rfl⟩ : syracuseStep 1342109 = 503291) (by norm_num)
theorem B850637 : Blo 527800 850637 := bbase (se 3 (by rfl) ⟨159494, by rfl⟩ : syracuseStep 850637 = 318989) (by norm_num)
theorem B2685797 : Blo 527800 2685797 := bbase (se 4 (by rfl) ⟨251793, by rfl⟩ : syracuseStep 2685797 = 503587) (by norm_num)
theorem B1276781 : Blo 527800 1276781 := bbase (se 3 (by rfl) ⟨239396, by rfl⟩ : syracuseStep 1276781 = 478793) (by norm_num)
theorem B1342453 : Blo 527800 1342453 := bbase (se 5 (by rfl) ⟨62927, by rfl⟩ : syracuseStep 1342453 = 125855) (by norm_num)
theorem B687109 : Blo 527800 687109 := bbase (se 4 (by rfl) ⟨64416, by rfl⟩ : syracuseStep 687109 = 128833) (by norm_num)
theorem B1342565 : Blo 527800 1342565 := bbase (se 4 (by rfl) ⟨125865, by rfl⟩ : syracuseStep 1342565 = 251731) (by norm_num)
theorem B1211581 : Blo 527800 1211581 := bbase (se 3 (by rfl) ⟨227171, by rfl⟩ : syracuseStep 1211581 = 454343) (by norm_num)
theorem B1342757 : Blo 527800 1342757 := bbase (se 4 (by rfl) ⟨125883, by rfl⟩ : syracuseStep 1342757 = 251767) (by norm_num)
theorem B851285 : Blo 527800 851285 := bbase (se 11 (by rfl) ⟨623, by rfl⟩ : syracuseStep 851285 = 1247) (by norm_num)
theorem B752989 : Blo 527800 752989 := bbase (se 3 (by rfl) ⟨141185, by rfl⟩ : syracuseStep 752989 = 282371) (by norm_num)
theorem B10911125 : Blo 527800 10911125 := bbase (se 6 (by rfl) ⟨255729, by rfl⟩ : syracuseStep 10911125 = 511459) (by norm_num)
theorem B2555333 : Blo 527800 2555333 := bbase (se 4 (by rfl) ⟨239562, by rfl⟩ : syracuseStep 2555333 = 479125) (by norm_num)
theorem B1343101 : Blo 527800 1343101 := bbase (se 3 (by rfl) ⟨251831, by rfl⟩ : syracuseStep 1343101 = 503663) (by norm_num)
theorem B1703605 : Blo 527800 1703605 := bbase (se 5 (by rfl) ⟨79856, by rfl⟩ : syracuseStep 1703605 = 159713) (by norm_num)
theorem B1343213 : Blo 527800 1343213 := bbase (se 3 (by rfl) ⟨251852, by rfl⟩ : syracuseStep 1343213 = 503705) (by norm_num)
theorem B753581 : Blo 527800 753581 := bbase (se 3 (by rfl) ⟨141296, by rfl⟩ : syracuseStep 753581 = 282593) (by norm_num)
theorem B1343405 : Blo 527800 1343405 := bbase (se 3 (by rfl) ⟨251888, by rfl⟩ : syracuseStep 1343405 = 503777) (by norm_num)
theorem B917477 : Blo 527800 917477 := bbase (se 4 (by rfl) ⟨86013, by rfl⟩ : syracuseStep 917477 = 172027) (by norm_num)
theorem B753661 : Blo 527800 753661 := bbase (se 3 (by rfl) ⟨141311, by rfl⟩ : syracuseStep 753661 = 282623) (by norm_num)
theorem B1343537 : Blo 527800 1343537 := bstep (se 2 (by rfl) ⟨503826, by rfl⟩ : syracuseStep 1343537 = 1007653) B1007653
theorem B1343587 : Blo 527800 1343587 := bstep (se 1 (by rfl) ⟨1007690, by rfl⟩ : syracuseStep 1343587 = 2015381) B2015381
theorem B3211397 : Blo 527800 3211397 := bstep (se 4 (by rfl) ⟨301068, by rfl⟩ : syracuseStep 3211397 = 602137) B602137
theorem B753889 : Blo 527800 753889 := bstep (se 2 (by rfl) ⟨282708, by rfl⟩ : syracuseStep 753889 = 565417) B565417
theorem B1343729 : Blo 527800 1343729 := bstep (se 2 (by rfl) ⟨503898, by rfl⟩ : syracuseStep 1343729 = 1007797) B1007797
theorem B2130275 : Blo 527800 2130275 := bstep (se 1 (by rfl) ⟨1597706, by rfl⟩ : syracuseStep 2130275 = 3195413) B3195413
theorem B3015053 : Blo 527800 3015053 := bstep (se 3 (by rfl) ⟨565322, by rfl⟩ : syracuseStep 3015053 = 1130645) B1130645
theorem B1508017 : Blo 527800 1508017 := bstep (se 2 (by rfl) ⟨565506, by rfl⟩ : syracuseStep 1508017 = 1131013) B1131013
theorem B754481 : Blo 527800 754481 := bstep (se 2 (by rfl) ⟨282930, by rfl⟩ : syracuseStep 754481 = 565861) B565861
theorem B2261837 : Blo 527800 2261837 := bstep (se 3 (by rfl) ⟨424094, by rfl⟩ : syracuseStep 2261837 = 848189) B848189
theorem B1508291 : Blo 527800 1508291 := bstep (se 1 (by rfl) ⟨1131218, by rfl⟩ : syracuseStep 1508291 = 2262437) B2262437
theorem B1508483 : Blo 527800 1508483 := bstep (se 1 (by rfl) ⟨1131362, by rfl⟩ : syracuseStep 1508483 = 2262725) B2262725
theorem B1344721 : Blo 527800 1344721 := bstep (se 2 (by rfl) ⟨504270, by rfl⟩ : syracuseStep 1344721 = 1008541) B1008541
theorem B2688227 : Blo 527800 2688227 := bstep (se 1 (by rfl) ⟨2016170, by rfl⟩ : syracuseStep 2688227 = 4032341) B4032341
theorem B4064525 : Blo 527800 4064525 := bstep (se 3 (by rfl) ⟨762098, by rfl⟩ : syracuseStep 4064525 = 1524197) B1524197
theorem B755011 : Blo 527800 755011 := bstep (se 1 (by rfl) ⟨566258, by rfl⟩ : syracuseStep 755011 = 1132517) B1132517
theorem B1148323 : Blo 527800 1148323 := bstep (se 1 (by rfl) ⟨861242, by rfl⟩ : syracuseStep 1148323 = 1722485) B1722485
theorem B1344995 : Blo 527800 1344995 := bstep (se 1 (by rfl) ⟨1008746, by rfl⟩ : syracuseStep 1344995 = 2017493) B2017493
theorem B951907 : Blo 527800 951907 := bstep (se 1 (by rfl) ⟨713930, by rfl⟩ : syracuseStep 951907 = 1427861) B1427861
theorem B755347 : Blo 527800 755347 := bstep (se 1 (by rfl) ⟨566510, by rfl⟩ : syracuseStep 755347 = 1133021) B1133021
theorem B1345187 : Blo 527800 1345187 := bstep (se 1 (by rfl) ⟨1008890, by rfl⟩ : syracuseStep 1345187 = 2017781) B2017781
theorem B1017731 : Blo 527800 1017731 := bstep (se 1 (by rfl) ⟨763298, by rfl⟩ : syracuseStep 1017731 = 1526597) B1526597
theorem B1509293 : Blo 527800 1509293 := bstep (se 3 (by rfl) ⟨282992, by rfl⟩ : syracuseStep 1509293 = 565985) B565985
theorem B2689037 : Blo 527800 2689037 := bstep (se 3 (by rfl) ⟨504194, by rfl⟩ : syracuseStep 2689037 = 1008389) B1008389
theorem B1607779 : Blo 527800 1607779 := bstep (se 1 (by rfl) ⟨1205834, by rfl⟩ : syracuseStep 1607779 = 2411669) B2411669
theorem B1017955 : Blo 527800 1017955 := bstep (se 1 (by rfl) ⟨763466, by rfl⟩ : syracuseStep 1017955 = 1526933) B1526933
theorem B1509475 : Blo 527800 1509475 := bstep (se 1 (by rfl) ⟨1132106, by rfl⟩ : syracuseStep 1509475 = 2264213) B2264213
theorem B755905 : Blo 527800 755905 := bstep (se 2 (by rfl) ⟨283464, by rfl⟩ : syracuseStep 755905 = 566929) B566929
theorem B755939 : Blo 527800 755939 := bstep (se 1 (by rfl) ⟨566954, by rfl⟩ : syracuseStep 755939 = 1133909) B1133909
theorem B2263409 : Blo 527800 2263409 := bstep (se 2 (by rfl) ⟨848778, by rfl⟩ : syracuseStep 2263409 = 1697557) B1697557
theorem B1575299 : Blo 527800 1575299 := bstep (se 1 (by rfl) ⟨1181474, by rfl⟩ : syracuseStep 1575299 = 2362949) B2362949
theorem B1509965 : Blo 527800 1509965 := bstep (se 3 (by rfl) ⟨283118, by rfl⟩ : syracuseStep 1509965 = 566237) B566237
theorem B756497 : Blo 527800 756497 := bstep (se 2 (by rfl) ⟨283686, by rfl⟩ : syracuseStep 756497 = 567373) B567373
theorem B756577 : Blo 527800 756577 := bstep (se 2 (by rfl) ⟨283716, by rfl⟩ : syracuseStep 756577 = 567433) B567433
theorem B4361357 : Blo 527800 4361357 := bstep (se 3 (by rfl) ⟨817754, by rfl⟩ : syracuseStep 4361357 = 1635509) B1635509
theorem B953507 : Blo 527800 953507 := bstep (se 1 (by rfl) ⟨715130, by rfl⟩ : syracuseStep 953507 = 1430261) B1430261
theorem B3017969 : Blo 527800 3017969 := bstep (se 2 (by rfl) ⟨1131738, by rfl⟩ : syracuseStep 3017969 = 2263477) B2263477
theorem B3673349 : Blo 527800 3673349 := bstep (se 4 (by rfl) ⟨344376, by rfl⟩ : syracuseStep 3673349 = 688753) B688753
theorem B724307 : Blo 527800 724307 := bstep (se 1 (by rfl) ⟨543230, by rfl⟩ : syracuseStep 724307 = 1086461) B1086461
theorem B527811 : Blo 527800 527811 := bstep (se 1 (by rfl) ⟨395858, by rfl⟩ : syracuseStep 527811 = 791717) B791717
theorem B16289221 : Blo 527800 16289221 := bstep (se 4 (by rfl) ⟨1527114, by rfl⟩ : syracuseStep 16289221 = 3054229) B3054229
theorem B527827 : Blo 527800 527827 := bstep (se 1 (by rfl) ⟨395870, by rfl⟩ : syracuseStep 527827 = 791741) B791741
theorem B527843 : Blo 527800 527843 := bstep (se 1 (by rfl) ⟨395882, by rfl⟩ : syracuseStep 527843 = 791765) B791765
theorem B527859 : Blo 527800 527859 := bstep (se 1 (by rfl) ⟨395894, by rfl⟩ : syracuseStep 527859 = 791789) B791789
theorem B527875 : Blo 527800 527875 := bstep (se 1 (by rfl) ⟨395906, by rfl⟩ : syracuseStep 527875 = 791813) B791813
theorem B527891 : Blo 527800 527891 := bstep (se 1 (by rfl) ⟨395918, by rfl⟩ : syracuseStep 527891 = 791837) B791837
theorem B527907 : Blo 527800 527907 := bstep (se 1 (by rfl) ⟨395930, by rfl⟩ : syracuseStep 527907 = 791861) B791861
theorem B527923 : Blo 527800 527923 := bstep (se 1 (by rfl) ⟨395942, by rfl⟩ : syracuseStep 527923 = 791885) B791885
theorem B527939 : Blo 527800 527939 := bstep (se 1 (by rfl) ⟨395954, by rfl⟩ : syracuseStep 527939 = 791909) B791909
theorem B527955 : Blo 527800 527955 := bstep (se 1 (by rfl) ⟨395966, by rfl⟩ : syracuseStep 527955 = 791933) B791933
theorem B527971 : Blo 527800 527971 := bstep (se 1 (by rfl) ⟨395978, by rfl⟩ : syracuseStep 527971 = 791957) B791957
theorem B527987 : Blo 527800 527987 := bstep (se 1 (by rfl) ⟨395990, by rfl⟩ : syracuseStep 527987 = 791981) B791981
theorem B528003 : Blo 527800 528003 := bstep (se 1 (by rfl) ⟨396002, by rfl⟩ : syracuseStep 528003 = 792005) B792005
theorem B528019 : Blo 527800 528019 := bstep (se 1 (by rfl) ⟨396014, by rfl⟩ : syracuseStep 528019 = 792029) B792029
theorem B528035 : Blo 527800 528035 := bstep (se 1 (by rfl) ⟨396026, by rfl⟩ : syracuseStep 528035 = 792053) B792053
theorem B528051 : Blo 527800 528051 := bstep (se 1 (by rfl) ⟨396038, by rfl⟩ : syracuseStep 528051 = 792077) B792077
theorem B528067 : Blo 527800 528067 := bstep (se 1 (by rfl) ⟨396050, by rfl⟩ : syracuseStep 528067 = 792101) B792101
theorem B528083 : Blo 527800 528083 := bstep (se 1 (by rfl) ⟨396062, by rfl⟩ : syracuseStep 528083 = 792125) B792125
theorem B528099 : Blo 527800 528099 := bstep (se 1 (by rfl) ⟨396074, by rfl⟩ : syracuseStep 528099 = 792149) B792149
theorem B1511149 : Blo 527800 1511149 := bstep (se 3 (by rfl) ⟨283340, by rfl⟩ : syracuseStep 1511149 = 566681) B566681
theorem B528115 : Blo 527800 528115 := bstep (se 1 (by rfl) ⟨396086, by rfl⟩ : syracuseStep 528115 = 792173) B792173
theorem B528131 : Blo 527800 528131 := bstep (se 1 (by rfl) ⟨396098, by rfl⟩ : syracuseStep 528131 = 792197) B792197
theorem B528147 : Blo 527800 528147 := bstep (se 1 (by rfl) ⟨396110, by rfl⟩ : syracuseStep 528147 = 792221) B792221
theorem B528163 : Blo 527800 528163 := bstep (se 1 (by rfl) ⟨396122, by rfl⟩ : syracuseStep 528163 = 792245) B792245
theorem B528179 : Blo 527800 528179 := bstep (se 1 (by rfl) ⟨396134, by rfl⟩ : syracuseStep 528179 = 792269) B792269
theorem B528195 : Blo 527800 528195 := bstep (se 1 (by rfl) ⟨396146, by rfl⟩ : syracuseStep 528195 = 792293) B792293
theorem B528211 : Blo 527800 528211 := bstep (se 1 (by rfl) ⟨396158, by rfl⟩ : syracuseStep 528211 = 792317) B792317
theorem B528227 : Blo 527800 528227 := bstep (se 1 (by rfl) ⟨396170, by rfl⟩ : syracuseStep 528227 = 792341) B792341
theorem B593779 : Blo 527800 593779 := bstep (se 1 (by rfl) ⟨445334, by rfl⟩ : syracuseStep 593779 = 890669) B890669
theorem B528243 : Blo 527800 528243 := bstep (se 1 (by rfl) ⟨396182, by rfl⟩ : syracuseStep 528243 = 792365) B792365
theorem B528259 : Blo 527800 528259 := bstep (se 1 (by rfl) ⟨396194, by rfl⟩ : syracuseStep 528259 = 792389) B792389
theorem B528275 : Blo 527800 528275 := bstep (se 1 (by rfl) ⟨396206, by rfl⟩ : syracuseStep 528275 = 792413) B792413
theorem B528291 : Blo 527800 528291 := bstep (se 1 (by rfl) ⟨396218, by rfl⟩ : syracuseStep 528291 = 792437) B792437
theorem B528307 : Blo 527800 528307 := bstep (se 1 (by rfl) ⟨396230, by rfl⟩ : syracuseStep 528307 = 792461) B792461
theorem B528323 : Blo 527800 528323 := bstep (se 1 (by rfl) ⟨396242, by rfl⟩ : syracuseStep 528323 = 792485) B792485
theorem B528339 : Blo 527800 528339 := bstep (se 1 (by rfl) ⟨396254, by rfl⟩ : syracuseStep 528339 = 792509) B792509
theorem B528355 : Blo 527800 528355 := bstep (se 1 (by rfl) ⟨396266, by rfl⟩ : syracuseStep 528355 = 792533) B792533
theorem B1609699 : Blo 527800 1609699 := bstep (se 1 (by rfl) ⟨1207274, by rfl⟩ : syracuseStep 1609699 = 2414549) B2414549
theorem B528371 : Blo 527800 528371 := bstep (se 1 (by rfl) ⟨396278, by rfl⟩ : syracuseStep 528371 = 792557) B792557
theorem B593923 : Blo 527800 593923 := bstep (se 1 (by rfl) ⟨445442, by rfl⟩ : syracuseStep 593923 = 890885) B890885
theorem B528387 : Blo 527800 528387 := bstep (se 1 (by rfl) ⟨396290, by rfl⟩ : syracuseStep 528387 = 792581) B792581
theorem B528403 : Blo 527800 528403 := bstep (se 1 (by rfl) ⟨396302, by rfl⟩ : syracuseStep 528403 = 792605) B792605
theorem B528419 : Blo 527800 528419 := bstep (se 1 (by rfl) ⟨396314, by rfl⟩ : syracuseStep 528419 = 792629) B792629
theorem B528435 : Blo 527800 528435 := bstep (se 1 (by rfl) ⟨396326, by rfl⟩ : syracuseStep 528435 = 792653) B792653
theorem B528451 : Blo 527800 528451 := bstep (se 1 (by rfl) ⟨396338, by rfl⟩ : syracuseStep 528451 = 792677) B792677
theorem B528467 : Blo 527800 528467 := bstep (se 1 (by rfl) ⟨396350, by rfl⟩ : syracuseStep 528467 = 792701) B792701
theorem B528483 : Blo 527800 528483 := bstep (se 1 (by rfl) ⟨396362, by rfl⟩ : syracuseStep 528483 = 792725) B792725
theorem B528499 : Blo 527800 528499 := bstep (se 1 (by rfl) ⟨396374, by rfl⟩ : syracuseStep 528499 = 792749) B792749
theorem B528515 : Blo 527800 528515 := bstep (se 1 (by rfl) ⟨396386, by rfl⟩ : syracuseStep 528515 = 792773) B792773
theorem B594067 : Blo 527800 594067 := bstep (se 1 (by rfl) ⟨445550, by rfl⟩ : syracuseStep 594067 = 891101) B891101
theorem B528531 : Blo 527800 528531 := bstep (se 1 (by rfl) ⟨396398, by rfl⟩ : syracuseStep 528531 = 792797) B792797
theorem B528547 : Blo 527800 528547 := bstep (se 1 (by rfl) ⟨396410, by rfl⟩ : syracuseStep 528547 = 792821) B792821
theorem B528563 : Blo 527800 528563 := bstep (se 1 (by rfl) ⟨396422, by rfl⟩ : syracuseStep 528563 = 792845) B792845
theorem B528579 : Blo 527800 528579 := bstep (se 1 (by rfl) ⟨396434, by rfl⟩ : syracuseStep 528579 = 792869) B792869
theorem B528595 : Blo 527800 528595 := bstep (se 1 (by rfl) ⟨396446, by rfl⟩ : syracuseStep 528595 = 792893) B792893
theorem B528611 : Blo 527800 528611 := bstep (se 1 (by rfl) ⟨396458, by rfl⟩ : syracuseStep 528611 = 792917) B792917
theorem B528627 : Blo 527800 528627 := bstep (se 1 (by rfl) ⟨396470, by rfl⟩ : syracuseStep 528627 = 792941) B792941
theorem B528643 : Blo 527800 528643 := bstep (se 1 (by rfl) ⟨396482, by rfl⟩ : syracuseStep 528643 = 792965) B792965
theorem B528659 : Blo 527800 528659 := bstep (se 1 (by rfl) ⟨396494, by rfl⟩ : syracuseStep 528659 = 792989) B792989
theorem B594211 : Blo 527800 594211 := bstep (se 1 (by rfl) ⟨445658, by rfl⟩ : syracuseStep 594211 = 891317) B891317
theorem B528675 : Blo 527800 528675 := bstep (se 1 (by rfl) ⟨396506, by rfl⟩ : syracuseStep 528675 = 793013) B793013
theorem B528691 : Blo 527800 528691 := bstep (se 1 (by rfl) ⟨396518, by rfl⟩ : syracuseStep 528691 = 793037) B793037
theorem B528707 : Blo 527800 528707 := bstep (se 1 (by rfl) ⟨396530, by rfl⟩ : syracuseStep 528707 = 793061) B793061
theorem B528723 : Blo 527800 528723 := bstep (se 1 (by rfl) ⟨396542, by rfl⟩ : syracuseStep 528723 = 793085) B793085
theorem B528739 : Blo 527800 528739 := bstep (se 1 (by rfl) ⟨396554, by rfl⟩ : syracuseStep 528739 = 793109) B793109
theorem B528755 : Blo 527800 528755 := bstep (se 1 (by rfl) ⟨396566, by rfl⟩ : syracuseStep 528755 = 793133) B793133
theorem B528771 : Blo 527800 528771 := bstep (se 1 (by rfl) ⟨396578, by rfl⟩ : syracuseStep 528771 = 793157) B793157
theorem B528787 : Blo 527800 528787 := bstep (se 1 (by rfl) ⟨396590, by rfl⟩ : syracuseStep 528787 = 793181) B793181
theorem B528803 : Blo 527800 528803 := bstep (se 1 (by rfl) ⟨396602, by rfl⟩ : syracuseStep 528803 = 793205) B793205
theorem B594355 : Blo 527800 594355 := bstep (se 1 (by rfl) ⟨445766, by rfl⟩ : syracuseStep 594355 = 891533) B891533
theorem B528819 : Blo 527800 528819 := bstep (se 1 (by rfl) ⟨396614, by rfl⟩ : syracuseStep 528819 = 793229) B793229
theorem B528835 : Blo 527800 528835 := bstep (se 1 (by rfl) ⟨396626, by rfl⟩ : syracuseStep 528835 = 793253) B793253
theorem B528851 : Blo 527800 528851 := bstep (se 1 (by rfl) ⟨396638, by rfl⟩ : syracuseStep 528851 = 793277) B793277
theorem B528867 : Blo 527800 528867 := bstep (se 1 (by rfl) ⟨396650, by rfl⟩ : syracuseStep 528867 = 793301) B793301
theorem B528883 : Blo 527800 528883 := bstep (se 1 (by rfl) ⟨396662, by rfl⟩ : syracuseStep 528883 = 793325) B793325
theorem B528899 : Blo 527800 528899 := bstep (se 1 (by rfl) ⟨396674, by rfl⟩ : syracuseStep 528899 = 793349) B793349
theorem B528915 : Blo 527800 528915 := bstep (se 1 (by rfl) ⟨396686, by rfl⟩ : syracuseStep 528915 = 793373) B793373
theorem B528931 : Blo 527800 528931 := bstep (se 1 (by rfl) ⟨396698, by rfl⟩ : syracuseStep 528931 = 793397) B793397
theorem B528947 : Blo 527800 528947 := bstep (se 1 (by rfl) ⟨396710, by rfl⟩ : syracuseStep 528947 = 793421) B793421
theorem B594499 : Blo 527800 594499 := bstep (se 1 (by rfl) ⟨445874, by rfl⟩ : syracuseStep 594499 = 891749) B891749
theorem B528963 : Blo 527800 528963 := bstep (se 1 (by rfl) ⟨396722, by rfl⟩ : syracuseStep 528963 = 793445) B793445
theorem B528979 : Blo 527800 528979 := bstep (se 1 (by rfl) ⟨396734, by rfl⟩ : syracuseStep 528979 = 793469) B793469
theorem B528995 : Blo 527800 528995 := bstep (se 1 (by rfl) ⟨396746, by rfl⟩ : syracuseStep 528995 = 793493) B793493
theorem B529011 : Blo 527800 529011 := bstep (se 1 (by rfl) ⟨396758, by rfl⟩ : syracuseStep 529011 = 793517) B793517
theorem B529027 : Blo 527800 529027 := bstep (se 1 (by rfl) ⟨396770, by rfl⟩ : syracuseStep 529027 = 793541) B793541
theorem B1610381 : Blo 527800 1610381 := bstep (se 3 (by rfl) ⟨301946, by rfl⟩ : syracuseStep 1610381 = 603893) B603893
theorem B529043 : Blo 527800 529043 := bstep (se 1 (by rfl) ⟨396782, by rfl⟩ : syracuseStep 529043 = 793565) B793565
theorem B529059 : Blo 527800 529059 := bstep (se 1 (by rfl) ⟨396794, by rfl⟩ : syracuseStep 529059 = 793589) B793589
theorem B3019427 : Blo 527800 3019427 := bstep (se 1 (by rfl) ⟨2264570, by rfl⟩ : syracuseStep 3019427 = 4529141) B4529141
theorem B529075 : Blo 527800 529075 := bstep (se 1 (by rfl) ⟨396806, by rfl⟩ : syracuseStep 529075 = 793613) B793613
theorem B529091 : Blo 527800 529091 := bstep (se 1 (by rfl) ⟨396818, by rfl⟩ : syracuseStep 529091 = 793637) B793637
theorem B594643 : Blo 527800 594643 := bstep (se 1 (by rfl) ⟨445982, by rfl⟩ : syracuseStep 594643 = 891965) B891965
theorem B529107 : Blo 527800 529107 := bstep (se 1 (by rfl) ⟨396830, by rfl⟩ : syracuseStep 529107 = 793661) B793661
theorem B529123 : Blo 527800 529123 := bstep (se 1 (by rfl) ⟨396842, by rfl⟩ : syracuseStep 529123 = 793685) B793685
theorem B529139 : Blo 527800 529139 := bstep (se 1 (by rfl) ⟨396854, by rfl⟩ : syracuseStep 529139 = 793709) B793709
theorem B529155 : Blo 527800 529155 := bstep (se 1 (by rfl) ⟨396866, by rfl⟩ : syracuseStep 529155 = 793733) B793733
theorem B2265869 : Blo 527800 2265869 := bstep (se 3 (by rfl) ⟨424850, by rfl⟩ : syracuseStep 2265869 = 849701) B849701
theorem B1512209 : Blo 527800 1512209 := bstep (se 2 (by rfl) ⟨567078, by rfl⟩ : syracuseStep 1512209 = 1134157) B1134157
theorem B529171 : Blo 527800 529171 := bstep (se 1 (by rfl) ⟨396878, by rfl⟩ : syracuseStep 529171 = 793757) B793757
theorem B529187 : Blo 527800 529187 := bstep (se 1 (by rfl) ⟨396890, by rfl⟩ : syracuseStep 529187 = 793781) B793781
theorem B529203 : Blo 527800 529203 := bstep (se 1 (by rfl) ⟨396902, by rfl⟩ : syracuseStep 529203 = 793805) B793805
theorem B529219 : Blo 527800 529219 := bstep (se 1 (by rfl) ⟨396914, by rfl⟩ : syracuseStep 529219 = 793829) B793829
theorem B529235 : Blo 527800 529235 := bstep (se 1 (by rfl) ⟨396926, by rfl⟩ : syracuseStep 529235 = 793853) B793853
theorem B594787 : Blo 527800 594787 := bstep (se 1 (by rfl) ⟨446090, by rfl⟩ : syracuseStep 594787 = 892181) B892181
theorem B529251 : Blo 527800 529251 := bstep (se 1 (by rfl) ⟨396938, by rfl⟩ : syracuseStep 529251 = 793877) B793877
theorem B2691953 : Blo 527800 2691953 := bstep (se 2 (by rfl) ⟨1009482, by rfl⟩ : syracuseStep 2691953 = 2018965) B2018965
theorem B529267 : Blo 527800 529267 := bstep (se 1 (by rfl) ⟨396950, by rfl⟩ : syracuseStep 529267 = 793901) B793901
theorem B529283 : Blo 527800 529283 := bstep (se 1 (by rfl) ⟨396962, by rfl⟩ : syracuseStep 529283 = 793925) B793925
theorem B529299 : Blo 527800 529299 := bstep (se 1 (by rfl) ⟨396974, by rfl⟩ : syracuseStep 529299 = 793949) B793949
theorem B529315 : Blo 527800 529315 := bstep (se 1 (by rfl) ⟨396986, by rfl⟩ : syracuseStep 529315 = 793973) B793973
theorem B529331 : Blo 527800 529331 := bstep (se 1 (by rfl) ⟨396998, by rfl⟩ : syracuseStep 529331 = 793997) B793997
theorem B529347 : Blo 527800 529347 := bstep (se 1 (by rfl) ⟨397010, by rfl⟩ : syracuseStep 529347 = 794021) B794021
theorem B529363 : Blo 527800 529363 := bstep (se 1 (by rfl) ⟨397022, by rfl⟩ : syracuseStep 529363 = 794045) B794045
theorem B529379 : Blo 527800 529379 := bstep (se 1 (by rfl) ⟨397034, by rfl⟩ : syracuseStep 529379 = 794069) B794069
theorem B594931 : Blo 527800 594931 := bstep (se 1 (by rfl) ⟨446198, by rfl⟩ : syracuseStep 594931 = 892397) B892397
theorem B529395 : Blo 527800 529395 := bstep (se 1 (by rfl) ⟨397046, by rfl⟩ : syracuseStep 529395 = 794093) B794093
theorem B529411 : Blo 527800 529411 := bstep (se 1 (by rfl) ⟨397058, by rfl⟩ : syracuseStep 529411 = 794117) B794117
theorem B529427 : Blo 527800 529427 := bstep (se 1 (by rfl) ⟨397070, by rfl⟩ : syracuseStep 529427 = 794141) B794141
theorem B529443 : Blo 527800 529443 := bstep (se 1 (by rfl) ⟨397082, by rfl⟩ : syracuseStep 529443 = 794165) B794165
theorem B529459 : Blo 527800 529459 := bstep (se 1 (by rfl) ⟨397094, by rfl⟩ : syracuseStep 529459 = 794189) B794189
theorem B529475 : Blo 527800 529475 := bstep (se 1 (by rfl) ⟨397106, by rfl⟩ : syracuseStep 529475 = 794213) B794213
theorem B529491 : Blo 527800 529491 := bstep (se 1 (by rfl) ⟨397118, by rfl⟩ : syracuseStep 529491 = 794237) B794237
theorem B529507 : Blo 527800 529507 := bstep (se 1 (by rfl) ⟨397130, by rfl⟩ : syracuseStep 529507 = 794261) B794261
theorem B2266211 : Blo 527800 2266211 := bstep (se 1 (by rfl) ⟨1699658, by rfl⟩ : syracuseStep 2266211 = 3399317) B3399317
theorem B529523 : Blo 527800 529523 := bstep (se 1 (by rfl) ⟨397142, by rfl⟩ : syracuseStep 529523 = 794285) B794285
theorem B595075 : Blo 527800 595075 := bstep (se 1 (by rfl) ⟨446306, by rfl⟩ : syracuseStep 595075 = 892613) B892613
theorem B529539 : Blo 527800 529539 := bstep (se 1 (by rfl) ⟨397154, by rfl⟩ : syracuseStep 529539 = 794309) B794309
theorem B529555 : Blo 527800 529555 := bstep (se 1 (by rfl) ⟨397166, by rfl⟩ : syracuseStep 529555 = 794333) B794333
theorem B529571 : Blo 527800 529571 := bstep (se 1 (by rfl) ⟨397178, by rfl⟩ : syracuseStep 529571 = 794357) B794357
theorem B791729 : Blo 527800 791729 := bstep (se 2 (by rfl) ⟨296898, by rfl⟩ : syracuseStep 791729 = 593797) B593797
theorem B529587 : Blo 527800 529587 := bstep (se 1 (by rfl) ⟨397190, by rfl⟩ : syracuseStep 529587 = 794381) B794381
theorem B791747 : Blo 527800 791747 := bstep (se 1 (by rfl) ⟨593810, by rfl⟩ : syracuseStep 791747 = 1187621) B1187621
theorem B529603 : Blo 527800 529603 := bstep (se 1 (by rfl) ⟨397202, by rfl⟩ : syracuseStep 529603 = 794405) B794405
theorem B2004173 : Blo 527800 2004173 := bstep (se 3 (by rfl) ⟨375782, by rfl⟩ : syracuseStep 2004173 = 751565) B751565
theorem B529619 : Blo 527800 529619 := bstep (se 1 (by rfl) ⟨397214, by rfl⟩ : syracuseStep 529619 = 794429) B794429
theorem B791777 : Blo 527800 791777 := bstep (se 2 (by rfl) ⟨296916, by rfl⟩ : syracuseStep 791777 = 593833) B593833
theorem B529635 : Blo 527800 529635 := bstep (se 1 (by rfl) ⟨397226, by rfl⟩ : syracuseStep 529635 = 794453) B794453
theorem B791795 : Blo 527800 791795 := bstep (se 1 (by rfl) ⟨593846, by rfl⟩ : syracuseStep 791795 = 1187693) B1187693
theorem B529651 : Blo 527800 529651 := bstep (se 1 (by rfl) ⟨397238, by rfl⟩ : syracuseStep 529651 = 794477) B794477
theorem B529667 : Blo 527800 529667 := bstep (se 1 (by rfl) ⟨397250, by rfl⟩ : syracuseStep 529667 = 794501) B794501
theorem B791825 : Blo 527800 791825 := bstep (se 2 (by rfl) ⟨296934, by rfl⟩ : syracuseStep 791825 = 593869) B593869
theorem B595219 : Blo 527800 595219 := bstep (se 1 (by rfl) ⟨446414, by rfl⟩ : syracuseStep 595219 = 892829) B892829
theorem B529683 : Blo 527800 529683 := bstep (se 1 (by rfl) ⟨397262, by rfl⟩ : syracuseStep 529683 = 794525) B794525
theorem B791843 : Blo 527800 791843 := bstep (se 1 (by rfl) ⟨593882, by rfl⟩ : syracuseStep 791843 = 1187765) B1187765
theorem B529699 : Blo 527800 529699 := bstep (se 1 (by rfl) ⟨397274, by rfl⟩ : syracuseStep 529699 = 794549) B794549
theorem B529715 : Blo 527800 529715 := bstep (se 1 (by rfl) ⟨397286, by rfl⟩ : syracuseStep 529715 = 794573) B794573
theorem B791873 : Blo 527800 791873 := bstep (se 2 (by rfl) ⟨296952, by rfl⟩ : syracuseStep 791873 = 593905) B593905
theorem B529731 : Blo 527800 529731 := bstep (se 1 (by rfl) ⟨397298, by rfl⟩ : syracuseStep 529731 = 794597) B794597
theorem B3872069 : Blo 527800 3872069 := bstep (se 4 (by rfl) ⟨363006, by rfl⟩ : syracuseStep 3872069 = 726013) B726013
theorem B791891 : Blo 527800 791891 := bstep (se 1 (by rfl) ⟨593918, by rfl⟩ : syracuseStep 791891 = 1187837) B1187837
theorem B529747 : Blo 527800 529747 := bstep (se 1 (by rfl) ⟨397310, by rfl⟩ : syracuseStep 529747 = 794621) B794621
theorem B529763 : Blo 527800 529763 := bstep (se 1 (by rfl) ⟨397322, by rfl⟩ : syracuseStep 529763 = 794645) B794645
theorem B791921 : Blo 527800 791921 := bstep (se 2 (by rfl) ⟨296970, by rfl⟩ : syracuseStep 791921 = 593941) B593941
theorem B529779 : Blo 527800 529779 := bstep (se 1 (by rfl) ⟨397334, by rfl⟩ : syracuseStep 529779 = 794669) B794669
theorem B791939 : Blo 527800 791939 := bstep (se 1 (by rfl) ⟨593954, by rfl⟩ : syracuseStep 791939 = 1187909) B1187909
theorem B529795 : Blo 527800 529795 := bstep (se 1 (by rfl) ⟨397346, by rfl⟩ : syracuseStep 529795 = 794693) B794693
theorem B529811 : Blo 527800 529811 := bstep (se 1 (by rfl) ⟨397358, by rfl⟩ : syracuseStep 529811 = 794717) B794717
theorem B791969 : Blo 527800 791969 := bstep (se 2 (by rfl) ⟨296988, by rfl⟩ : syracuseStep 791969 = 593977) B593977
theorem B595363 : Blo 527800 595363 := bstep (se 1 (by rfl) ⟨446522, by rfl⟩ : syracuseStep 595363 = 893045) B893045
theorem B529827 : Blo 527800 529827 := bstep (se 1 (by rfl) ⟨397370, by rfl⟩ : syracuseStep 529827 = 794741) B794741
theorem B1512881 : Blo 527800 1512881 := bstep (se 2 (by rfl) ⟨567330, by rfl⟩ : syracuseStep 1512881 = 1134661) B1134661
theorem B791987 : Blo 527800 791987 := bstep (se 1 (by rfl) ⟨593990, by rfl⟩ : syracuseStep 791987 = 1187981) B1187981
theorem B529843 : Blo 527800 529843 := bstep (se 1 (by rfl) ⟨397382, by rfl⟩ : syracuseStep 529843 = 794765) B794765
theorem B529859 : Blo 527800 529859 := bstep (se 1 (by rfl) ⟨397394, by rfl⟩ : syracuseStep 529859 = 794789) B794789
theorem B792017 : Blo 527800 792017 := bstep (se 2 (by rfl) ⟨297006, by rfl⟩ : syracuseStep 792017 = 594013) B594013
theorem B529875 : Blo 527800 529875 := bstep (se 1 (by rfl) ⟨397406, by rfl⟩ : syracuseStep 529875 = 794813) B794813
theorem B792035 : Blo 527800 792035 := bstep (se 1 (by rfl) ⟨594026, by rfl⟩ : syracuseStep 792035 = 1188053) B1188053
theorem B529891 : Blo 527800 529891 := bstep (se 1 (by rfl) ⟨397418, by rfl⟩ : syracuseStep 529891 = 794837) B794837
theorem B529907 : Blo 527800 529907 := bstep (se 1 (by rfl) ⟨397430, by rfl⟩ : syracuseStep 529907 = 794861) B794861
theorem B792065 : Blo 527800 792065 := bstep (se 2 (by rfl) ⟨297024, by rfl⟩ : syracuseStep 792065 = 594049) B594049
theorem B529923 : Blo 527800 529923 := bstep (se 1 (by rfl) ⟨397442, by rfl⟩ : syracuseStep 529923 = 794885) B794885
theorem B792083 : Blo 527800 792083 := bstep (se 1 (by rfl) ⟨594062, by rfl⟩ : syracuseStep 792083 = 1188125) B1188125
theorem B529939 : Blo 527800 529939 := bstep (se 1 (by rfl) ⟨397454, by rfl⟩ : syracuseStep 529939 = 794909) B794909
theorem B529955 : Blo 527800 529955 := bstep (se 1 (by rfl) ⟨397466, by rfl⟩ : syracuseStep 529955 = 794933) B794933
theorem B792113 : Blo 527800 792113 := bstep (se 2 (by rfl) ⟨297042, by rfl⟩ : syracuseStep 792113 = 594085) B594085
theorem B595507 : Blo 527800 595507 := bstep (se 1 (by rfl) ⟨446630, by rfl⟩ : syracuseStep 595507 = 893261) B893261
theorem B529971 : Blo 527800 529971 := bstep (se 1 (by rfl) ⟨397478, by rfl⟩ : syracuseStep 529971 = 794957) B794957
theorem B792131 : Blo 527800 792131 := bstep (se 1 (by rfl) ⟨594098, by rfl⟩ : syracuseStep 792131 = 1188197) B1188197
theorem B529987 : Blo 527800 529987 := bstep (se 1 (by rfl) ⟨397490, by rfl⟩ : syracuseStep 529987 = 794981) B794981
theorem B530003 : Blo 527800 530003 := bstep (se 1 (by rfl) ⟨397502, by rfl⟩ : syracuseStep 530003 = 795005) B795005
theorem B792161 : Blo 527800 792161 := bstep (se 2 (by rfl) ⟨297060, by rfl⟩ : syracuseStep 792161 = 594121) B594121
theorem B530019 : Blo 527800 530019 := bstep (se 1 (by rfl) ⟨397514, by rfl⟩ : syracuseStep 530019 = 795029) B795029
theorem B792179 : Blo 527800 792179 := bstep (se 1 (by rfl) ⟨594134, by rfl⟩ : syracuseStep 792179 = 1188269) B1188269
theorem B530035 : Blo 527800 530035 := bstep (se 1 (by rfl) ⟨397526, by rfl⟩ : syracuseStep 530035 = 795053) B795053
theorem B530051 : Blo 527800 530051 := bstep (se 1 (by rfl) ⟨397538, by rfl⟩ : syracuseStep 530051 = 795077) B795077
theorem B3020429 : Blo 527800 3020429 := bstep (se 3 (by rfl) ⟨566330, by rfl⟩ : syracuseStep 3020429 = 1132661) B1132661
theorem B792209 : Blo 527800 792209 := bstep (se 2 (by rfl) ⟨297078, by rfl⟩ : syracuseStep 792209 = 594157) B594157
theorem B530067 : Blo 527800 530067 := bstep (se 1 (by rfl) ⟨397550, by rfl⟩ : syracuseStep 530067 = 795101) B795101
theorem B792227 : Blo 527800 792227 := bstep (se 1 (by rfl) ⟨594170, by rfl⟩ : syracuseStep 792227 = 1188341) B1188341
theorem B530083 : Blo 527800 530083 := bstep (se 1 (by rfl) ⟨397562, by rfl⟩ : syracuseStep 530083 = 795125) B795125
theorem B530099 : Blo 527800 530099 := bstep (se 1 (by rfl) ⟨397574, by rfl⟩ : syracuseStep 530099 = 795149) B795149
theorem B792257 : Blo 527800 792257 := bstep (se 2 (by rfl) ⟨297096, by rfl⟩ : syracuseStep 792257 = 594193) B594193
theorem B595651 : Blo 527800 595651 := bstep (se 1 (by rfl) ⟨446738, by rfl⟩ : syracuseStep 595651 = 893477) B893477
theorem B530115 : Blo 527800 530115 := bstep (se 1 (by rfl) ⟨397586, by rfl⟩ : syracuseStep 530115 = 795173) B795173
theorem B792275 : Blo 527800 792275 := bstep (se 1 (by rfl) ⟨594206, by rfl⟩ : syracuseStep 792275 = 1188413) B1188413
theorem B530131 : Blo 527800 530131 := bstep (se 1 (by rfl) ⟨397598, by rfl⟩ : syracuseStep 530131 = 795197) B795197
theorem B530147 : Blo 527800 530147 := bstep (se 1 (by rfl) ⟨397610, by rfl⟩ : syracuseStep 530147 = 795221) B795221
theorem B792305 : Blo 527800 792305 := bstep (se 2 (by rfl) ⟨297114, by rfl⟩ : syracuseStep 792305 = 594229) B594229
theorem B530163 : Blo 527800 530163 := bstep (se 1 (by rfl) ⟨397622, by rfl⟩ : syracuseStep 530163 = 795245) B795245
theorem B792323 : Blo 527800 792323 := bstep (se 1 (by rfl) ⟨594242, by rfl⟩ : syracuseStep 792323 = 1188485) B1188485
theorem B530179 : Blo 527800 530179 := bstep (se 1 (by rfl) ⟨397634, by rfl⟩ : syracuseStep 530179 = 795269) B795269
theorem B530195 : Blo 527800 530195 := bstep (se 1 (by rfl) ⟨397646, by rfl⟩ : syracuseStep 530195 = 795293) B795293
theorem B792353 : Blo 527800 792353 := bstep (se 2 (by rfl) ⟨297132, by rfl⟩ : syracuseStep 792353 = 594265) B594265
theorem B530211 : Blo 527800 530211 := bstep (se 1 (by rfl) ⟨397658, by rfl⟩ : syracuseStep 530211 = 795317) B795317
theorem B792371 : Blo 527800 792371 := bstep (se 1 (by rfl) ⟨594278, by rfl⟩ : syracuseStep 792371 = 1188557) B1188557
theorem B530227 : Blo 527800 530227 := bstep (se 1 (by rfl) ⟨397670, by rfl⟩ : syracuseStep 530227 = 795341) B795341
theorem B890689 : Blo 527800 890689 := bstep (se 2 (by rfl) ⟨334008, by rfl⟩ : syracuseStep 890689 = 668017) B668017
theorem B530243 : Blo 527800 530243 := bstep (se 1 (by rfl) ⟨397682, by rfl⟩ : syracuseStep 530243 = 795365) B795365
theorem B792401 : Blo 527800 792401 := bstep (se 2 (by rfl) ⟨297150, by rfl⟩ : syracuseStep 792401 = 594301) B594301
theorem B595795 : Blo 527800 595795 := bstep (se 1 (by rfl) ⟨446846, by rfl⟩ : syracuseStep 595795 = 893693) B893693
theorem B530259 : Blo 527800 530259 := bstep (se 1 (by rfl) ⟨397694, by rfl⟩ : syracuseStep 530259 = 795389) B795389
theorem B890723 : Blo 527800 890723 := bstep (se 1 (by rfl) ⟨668042, by rfl⟩ : syracuseStep 890723 = 1336085) B1336085
theorem B792419 : Blo 527800 792419 := bstep (se 1 (by rfl) ⟨594314, by rfl⟩ : syracuseStep 792419 = 1188629) B1188629
theorem B530275 : Blo 527800 530275 := bstep (se 1 (by rfl) ⟨397706, by rfl⟩ : syracuseStep 530275 = 795413) B795413
theorem B530291 : Blo 527800 530291 := bstep (se 1 (by rfl) ⟨397718, by rfl⟩ : syracuseStep 530291 = 795437) B795437
theorem B792449 : Blo 527800 792449 := bstep (se 2 (by rfl) ⟨297168, by rfl⟩ : syracuseStep 792449 = 594337) B594337
theorem B530307 : Blo 527800 530307 := bstep (se 1 (by rfl) ⟨397730, by rfl⟩ : syracuseStep 530307 = 795461) B795461
theorem B792467 : Blo 527800 792467 := bstep (se 1 (by rfl) ⟨594350, by rfl⟩ : syracuseStep 792467 = 1188701) B1188701
theorem B530323 : Blo 527800 530323 := bstep (se 1 (by rfl) ⟨397742, by rfl⟩ : syracuseStep 530323 = 795485) B795485
theorem B530339 : Blo 527800 530339 := bstep (se 1 (by rfl) ⟨397754, by rfl⟩ : syracuseStep 530339 = 795509) B795509
theorem B792497 : Blo 527800 792497 := bstep (se 2 (by rfl) ⟨297186, by rfl⟩ : syracuseStep 792497 = 594373) B594373
theorem B530355 : Blo 527800 530355 := bstep (se 1 (by rfl) ⟨397766, by rfl⟩ : syracuseStep 530355 = 795533) B795533
theorem B792515 : Blo 527800 792515 := bstep (se 1 (by rfl) ⟨594386, by rfl⟩ : syracuseStep 792515 = 1188773) B1188773
theorem B530371 : Blo 527800 530371 := bstep (se 1 (by rfl) ⟨397778, by rfl⟩ : syracuseStep 530371 = 795557) B795557
theorem B1906637 : Blo 527800 1906637 := bstep (se 3 (by rfl) ⟨357494, by rfl⟩ : syracuseStep 1906637 = 714989) B714989
theorem B956369 : Blo 527800 956369 := bstep (se 2 (by rfl) ⟨358638, by rfl⟩ : syracuseStep 956369 = 717277) B717277
theorem B530387 : Blo 527800 530387 := bstep (se 1 (by rfl) ⟨397790, by rfl⟩ : syracuseStep 530387 = 795581) B795581
theorem B792545 : Blo 527800 792545 := bstep (se 2 (by rfl) ⟨297204, by rfl⟩ : syracuseStep 792545 = 594409) B594409
theorem B890851 : Blo 527800 890851 := bstep (se 1 (by rfl) ⟨668138, by rfl⟩ : syracuseStep 890851 = 1336277) B1336277
theorem B595939 : Blo 527800 595939 := bstep (se 1 (by rfl) ⟨446954, by rfl⟩ : syracuseStep 595939 = 893909) B893909
theorem B530403 : Blo 527800 530403 := bstep (se 1 (by rfl) ⟨397802, by rfl⟩ : syracuseStep 530403 = 795605) B795605
theorem B792563 : Blo 527800 792563 := bstep (se 1 (by rfl) ⟨594422, by rfl⟩ : syracuseStep 792563 = 1188845) B1188845
theorem B530419 : Blo 527800 530419 := bstep (se 1 (by rfl) ⟨397814, by rfl⟩ : syracuseStep 530419 = 795629) B795629
theorem B530435 : Blo 527800 530435 := bstep (se 1 (by rfl) ⟨397826, by rfl⟩ : syracuseStep 530435 = 795653) B795653
theorem B792593 : Blo 527800 792593 := bstep (se 2 (by rfl) ⟨297222, by rfl⟩ : syracuseStep 792593 = 594445) B594445
theorem B530451 : Blo 527800 530451 := bstep (se 1 (by rfl) ⟨397838, by rfl⟩ : syracuseStep 530451 = 795677) B795677
theorem B792611 : Blo 527800 792611 := bstep (se 1 (by rfl) ⟨594458, by rfl⟩ : syracuseStep 792611 = 1188917) B1188917
theorem B530467 : Blo 527800 530467 := bstep (se 1 (by rfl) ⟨397850, by rfl⟩ : syracuseStep 530467 = 795701) B795701
theorem B530483 : Blo 527800 530483 := bstep (se 1 (by rfl) ⟨397862, by rfl⟩ : syracuseStep 530483 = 795725) B795725
theorem B792641 : Blo 527800 792641 := bstep (se 2 (by rfl) ⟨297240, by rfl⟩ : syracuseStep 792641 = 594481) B594481
theorem B530499 : Blo 527800 530499 := bstep (se 1 (by rfl) ⟨397874, by rfl⟩ : syracuseStep 530499 = 795749) B795749
theorem B792659 : Blo 527800 792659 := bstep (se 1 (by rfl) ⟨594494, by rfl⟩ : syracuseStep 792659 = 1188989) B1188989
theorem B530515 : Blo 527800 530515 := bstep (se 1 (by rfl) ⟨397886, by rfl⟩ : syracuseStep 530515 = 795773) B795773
theorem B530531 : Blo 527800 530531 := bstep (se 1 (by rfl) ⟨397898, by rfl⟩ : syracuseStep 530531 = 795797) B795797
theorem B890993 : Blo 527800 890993 := bstep (se 2 (by rfl) ⟨334122, by rfl⟩ : syracuseStep 890993 = 668245) B668245
theorem B792689 : Blo 527800 792689 := bstep (se 2 (by rfl) ⟨297258, by rfl⟩ : syracuseStep 792689 = 594517) B594517
theorem B596083 : Blo 527800 596083 := bstep (se 1 (by rfl) ⟨447062, by rfl⟩ : syracuseStep 596083 = 894125) B894125
theorem B530547 : Blo 527800 530547 := bstep (se 1 (by rfl) ⟨397910, by rfl⟩ : syracuseStep 530547 = 795821) B795821
theorem B792707 : Blo 527800 792707 := bstep (se 1 (by rfl) ⟨594530, by rfl⟩ : syracuseStep 792707 = 1189061) B1189061
theorem B530563 : Blo 527800 530563 := bstep (se 1 (by rfl) ⟨397922, by rfl⟩ : syracuseStep 530563 = 795845) B795845
theorem B530579 : Blo 527800 530579 := bstep (se 1 (by rfl) ⟨397934, by rfl⟩ : syracuseStep 530579 = 795869) B795869
theorem B792737 : Blo 527800 792737 := bstep (se 2 (by rfl) ⟨297276, by rfl⟩ : syracuseStep 792737 = 594553) B594553
theorem B530595 : Blo 527800 530595 := bstep (se 1 (by rfl) ⟨397946, by rfl⟩ : syracuseStep 530595 = 795893) B795893
theorem B792755 : Blo 527800 792755 := bstep (se 1 (by rfl) ⟨594566, by rfl⟩ : syracuseStep 792755 = 1189133) B1189133
theorem B530611 : Blo 527800 530611 := bstep (se 1 (by rfl) ⟨397958, by rfl⟩ : syracuseStep 530611 = 795917) B795917
theorem B530627 : Blo 527800 530627 := bstep (se 1 (by rfl) ⟨397970, by rfl⟩ : syracuseStep 530627 = 795941) B795941
theorem B1513667 : Blo 527800 1513667 := bstep (se 1 (by rfl) ⟨1135250, by rfl⟩ : syracuseStep 1513667 = 2270501) B2270501
theorem B792785 : Blo 527800 792785 := bstep (se 2 (by rfl) ⟨297294, by rfl⟩ : syracuseStep 792785 = 594589) B594589
theorem B530643 : Blo 527800 530643 := bstep (se 1 (by rfl) ⟨397982, by rfl⟩ : syracuseStep 530643 = 795965) B795965
theorem B792803 : Blo 527800 792803 := bstep (se 1 (by rfl) ⟨594602, by rfl⟩ : syracuseStep 792803 = 1189205) B1189205
theorem B530659 : Blo 527800 530659 := bstep (se 1 (by rfl) ⟨397994, by rfl⟩ : syracuseStep 530659 = 795989) B795989
theorem B891121 : Blo 527800 891121 := bstep (se 2 (by rfl) ⟨334170, by rfl⟩ : syracuseStep 891121 = 668341) B668341
theorem B530675 : Blo 527800 530675 := bstep (se 1 (by rfl) ⟨398006, by rfl⟩ : syracuseStep 530675 = 796013) B796013
theorem B792833 : Blo 527800 792833 := bstep (se 2 (by rfl) ⟨297312, by rfl⟩ : syracuseStep 792833 = 594625) B594625
theorem B596227 : Blo 527800 596227 := bstep (se 1 (by rfl) ⟨447170, by rfl⟩ : syracuseStep 596227 = 894341) B894341
theorem B530691 : Blo 527800 530691 := bstep (se 1 (by rfl) ⟨398018, by rfl⟩ : syracuseStep 530691 = 796037) B796037
theorem B891155 : Blo 527800 891155 := bstep (se 1 (by rfl) ⟨668366, by rfl⟩ : syracuseStep 891155 = 1336733) B1336733
theorem B792851 : Blo 527800 792851 := bstep (se 1 (by rfl) ⟨594638, by rfl⟩ : syracuseStep 792851 = 1189277) B1189277
theorem B530707 : Blo 527800 530707 := bstep (se 1 (by rfl) ⟨398030, by rfl⟩ : syracuseStep 530707 = 796061) B796061
theorem B24254741 : Blo 527800 24254741 := bstep (se 6 (by rfl) ⟨568470, by rfl⟩ : syracuseStep 24254741 = 1136941) B1136941
theorem B530723 : Blo 527800 530723 := bstep (se 1 (by rfl) ⟨398042, by rfl⟩ : syracuseStep 530723 = 796085) B796085
theorem B792881 : Blo 527800 792881 := bstep (se 2 (by rfl) ⟨297330, by rfl⟩ : syracuseStep 792881 = 594661) B594661
theorem B530739 : Blo 527800 530739 := bstep (se 1 (by rfl) ⟨398054, by rfl⟩ : syracuseStep 530739 = 796109) B796109
theorem B792899 : Blo 527800 792899 := bstep (se 1 (by rfl) ⟨594674, by rfl⟩ : syracuseStep 792899 = 1189349) B1189349
theorem B530755 : Blo 527800 530755 := bstep (se 1 (by rfl) ⟨398066, by rfl⟩ : syracuseStep 530755 = 796133) B796133
theorem B6461765 : Blo 527800 6461765 := bstep (se 4 (by rfl) ⟨605790, by rfl⟩ : syracuseStep 6461765 = 1211581) B1211581
theorem B530771 : Blo 527800 530771 := bstep (se 1 (by rfl) ⟨398078, by rfl⟩ : syracuseStep 530771 = 796157) B796157
theorem B792929 : Blo 527800 792929 := bstep (se 2 (by rfl) ⟨297348, by rfl⟩ : syracuseStep 792929 = 594697) B594697
theorem B530787 : Blo 527800 530787 := bstep (se 1 (by rfl) ⟨398090, by rfl⟩ : syracuseStep 530787 = 796181) B796181
theorem B792947 : Blo 527800 792947 := bstep (se 1 (by rfl) ⟨594710, by rfl⟩ : syracuseStep 792947 = 1189421) B1189421
theorem B530803 : Blo 527800 530803 := bstep (se 1 (by rfl) ⟨398102, by rfl⟩ : syracuseStep 530803 = 796205) B796205
theorem B530819 : Blo 527800 530819 := bstep (se 1 (by rfl) ⟨398114, by rfl⟩ : syracuseStep 530819 = 796229) B796229
theorem B792977 : Blo 527800 792977 := bstep (se 2 (by rfl) ⟨297366, by rfl⟩ : syracuseStep 792977 = 594733) B594733
theorem B891283 : Blo 527800 891283 := bstep (se 1 (by rfl) ⟨668462, by rfl⟩ : syracuseStep 891283 = 1336925) B1336925
theorem B596371 : Blo 527800 596371 := bstep (se 1 (by rfl) ⟨447278, by rfl⟩ : syracuseStep 596371 = 894557) B894557
theorem B530835 : Blo 527800 530835 := bstep (se 1 (by rfl) ⟨398126, by rfl⟩ : syracuseStep 530835 = 796253) B796253
theorem B792995 : Blo 527800 792995 := bstep (se 1 (by rfl) ⟨594746, by rfl⟩ : syracuseStep 792995 = 1189493) B1189493
theorem B530851 : Blo 527800 530851 := bstep (se 1 (by rfl) ⟨398138, by rfl⟩ : syracuseStep 530851 = 796277) B796277
theorem B530867 : Blo 527800 530867 := bstep (se 1 (by rfl) ⟨398150, by rfl⟩ : syracuseStep 530867 = 796301) B796301
theorem B793025 : Blo 527800 793025 := bstep (se 2 (by rfl) ⟨297384, by rfl⟩ : syracuseStep 793025 = 594769) B594769
theorem B530883 : Blo 527800 530883 := bstep (se 1 (by rfl) ⟨398162, by rfl⟩ : syracuseStep 530883 = 796325) B796325
theorem B793043 : Blo 527800 793043 := bstep (se 1 (by rfl) ⟨594782, by rfl⟩ : syracuseStep 793043 = 1189565) B1189565
theorem B530899 : Blo 527800 530899 := bstep (se 1 (by rfl) ⟨398174, by rfl⟩ : syracuseStep 530899 = 796349) B796349
theorem B858595 : Blo 527800 858595 := bstep (se 1 (by rfl) ⟨643946, by rfl⟩ : syracuseStep 858595 = 1287893) B1287893
theorem B530915 : Blo 527800 530915 := bstep (se 1 (by rfl) ⟨398186, by rfl⟩ : syracuseStep 530915 = 796373) B796373
theorem B793073 : Blo 527800 793073 := bstep (se 2 (by rfl) ⟨297402, by rfl⟩ : syracuseStep 793073 = 594805) B594805
theorem B530931 : Blo 527800 530931 := bstep (se 1 (by rfl) ⟨398198, by rfl⟩ : syracuseStep 530931 = 796397) B796397
theorem B793091 : Blo 527800 793091 := bstep (se 1 (by rfl) ⟨594818, by rfl⟩ : syracuseStep 793091 = 1189637) B1189637
theorem B530947 : Blo 527800 530947 := bstep (se 1 (by rfl) ⟨398210, by rfl⟩ : syracuseStep 530947 = 796421) B796421
theorem B1513997 : Blo 527800 1513997 := bstep (se 3 (by rfl) ⟨283874, by rfl⟩ : syracuseStep 1513997 = 567749) B567749
theorem B530963 : Blo 527800 530963 := bstep (se 1 (by rfl) ⟨398222, by rfl⟩ : syracuseStep 530963 = 796445) B796445
theorem B891425 : Blo 527800 891425 := bstep (se 2 (by rfl) ⟨334284, by rfl⟩ : syracuseStep 891425 = 668569) B668569
theorem B793121 : Blo 527800 793121 := bstep (se 2 (by rfl) ⟨297420, by rfl⟩ : syracuseStep 793121 = 594841) B594841
theorem B596515 : Blo 527800 596515 := bstep (se 1 (by rfl) ⟨447386, by rfl⟩ : syracuseStep 596515 = 894773) B894773
theorem B530979 : Blo 527800 530979 := bstep (se 1 (by rfl) ⟨398234, by rfl⟩ : syracuseStep 530979 = 796469) B796469
theorem B793139 : Blo 527800 793139 := bstep (se 1 (by rfl) ⟨594854, by rfl⟩ : syracuseStep 793139 = 1189709) B1189709
theorem B530995 : Blo 527800 530995 := bstep (se 1 (by rfl) ⟨398246, by rfl⟩ : syracuseStep 530995 = 796493) B796493
theorem B531011 : Blo 527800 531011 := bstep (se 1 (by rfl) ⟨398258, by rfl⟩ : syracuseStep 531011 = 796517) B796517
theorem B793169 : Blo 527800 793169 := bstep (se 2 (by rfl) ⟨297438, by rfl⟩ : syracuseStep 793169 = 594877) B594877
theorem B531027 : Blo 527800 531027 := bstep (se 1 (by rfl) ⟨398270, by rfl⟩ : syracuseStep 531027 = 796541) B796541
theorem B1514065 : Blo 527800 1514065 := bstep (se 2 (by rfl) ⟨567774, by rfl⟩ : syracuseStep 1514065 = 1135549) B1135549
theorem B793187 : Blo 527800 793187 := bstep (se 1 (by rfl) ⟨594890, by rfl⟩ : syracuseStep 793187 = 1189781) B1189781
theorem B531043 : Blo 527800 531043 := bstep (se 1 (by rfl) ⟨398282, by rfl⟩ : syracuseStep 531043 = 796565) B796565
theorem B531059 : Blo 527800 531059 := bstep (se 1 (by rfl) ⟨398294, by rfl⟩ : syracuseStep 531059 = 796589) B796589
theorem B793217 : Blo 527800 793217 := bstep (se 2 (by rfl) ⟨297456, by rfl⟩ : syracuseStep 793217 = 594913) B594913
theorem B531075 : Blo 527800 531075 := bstep (se 1 (by rfl) ⟨398306, by rfl⟩ : syracuseStep 531075 = 796613) B796613
theorem B793235 : Blo 527800 793235 := bstep (se 1 (by rfl) ⟨594926, by rfl⟩ : syracuseStep 793235 = 1189853) B1189853
theorem B531091 : Blo 527800 531091 := bstep (se 1 (by rfl) ⟨398318, by rfl⟩ : syracuseStep 531091 = 796637) B796637
theorem B891553 : Blo 527800 891553 := bstep (se 2 (by rfl) ⟨334332, by rfl⟩ : syracuseStep 891553 = 668665) B668665
theorem B531107 : Blo 527800 531107 := bstep (se 1 (by rfl) ⟨398330, by rfl⟩ : syracuseStep 531107 = 796661) B796661
theorem B793265 : Blo 527800 793265 := bstep (se 2 (by rfl) ⟨297474, by rfl⟩ : syracuseStep 793265 = 594949) B594949
theorem B596659 : Blo 527800 596659 := bstep (se 1 (by rfl) ⟨447494, by rfl⟩ : syracuseStep 596659 = 894989) B894989
theorem B531123 : Blo 527800 531123 := bstep (se 1 (by rfl) ⟨398342, by rfl⟩ : syracuseStep 531123 = 796685) B796685
theorem B891587 : Blo 527800 891587 := bstep (se 1 (by rfl) ⟨668690, by rfl⟩ : syracuseStep 891587 = 1337381) B1337381
theorem B793283 : Blo 527800 793283 := bstep (se 1 (by rfl) ⟨594962, by rfl⟩ : syracuseStep 793283 = 1189925) B1189925
theorem B531139 : Blo 527800 531139 := bstep (se 1 (by rfl) ⟨398354, by rfl⟩ : syracuseStep 531139 = 796709) B796709
theorem B531155 : Blo 527800 531155 := bstep (se 1 (by rfl) ⟨398366, by rfl⟩ : syracuseStep 531155 = 796733) B796733
theorem B793313 : Blo 527800 793313 := bstep (se 2 (by rfl) ⟨297492, by rfl⟩ : syracuseStep 793313 = 594985) B594985
theorem B3807971 : Blo 527800 3807971 := bstep (se 1 (by rfl) ⟨2855978, by rfl⟩ : syracuseStep 3807971 = 5711957) B5711957
theorem B531171 : Blo 527800 531171 := bstep (se 1 (by rfl) ⟨398378, by rfl⟩ : syracuseStep 531171 = 796757) B796757
theorem B793331 : Blo 527800 793331 := bstep (se 1 (by rfl) ⟨594998, by rfl⟩ : syracuseStep 793331 = 1189997) B1189997
theorem B531187 : Blo 527800 531187 := bstep (se 1 (by rfl) ⟨398390, by rfl⟩ : syracuseStep 531187 = 796781) B796781
theorem B531203 : Blo 527800 531203 := bstep (se 1 (by rfl) ⟨398402, by rfl⟩ : syracuseStep 531203 = 796805) B796805
theorem B793361 : Blo 527800 793361 := bstep (se 2 (by rfl) ⟨297510, by rfl⟩ : syracuseStep 793361 = 595021) B595021
theorem B531219 : Blo 527800 531219 := bstep (se 1 (by rfl) ⟨398414, by rfl⟩ : syracuseStep 531219 = 796829) B796829
theorem B793379 : Blo 527800 793379 := bstep (se 1 (by rfl) ⟨595034, by rfl⟩ : syracuseStep 793379 = 1190069) B1190069
theorem B531235 : Blo 527800 531235 := bstep (se 1 (by rfl) ⟨398426, by rfl⟩ : syracuseStep 531235 = 796853) B796853
theorem B531251 : Blo 527800 531251 := bstep (se 1 (by rfl) ⟨398438, by rfl⟩ : syracuseStep 531251 = 796877) B796877
theorem B793409 : Blo 527800 793409 := bstep (se 2 (by rfl) ⟨297528, by rfl⟩ : syracuseStep 793409 = 595057) B595057
theorem B891715 : Blo 527800 891715 := bstep (se 1 (by rfl) ⟨668786, by rfl⟩ : syracuseStep 891715 = 1337573) B1337573
theorem B596803 : Blo 527800 596803 := bstep (se 1 (by rfl) ⟨447602, by rfl⟩ : syracuseStep 596803 = 895205) B895205
theorem B531267 : Blo 527800 531267 := bstep (se 1 (by rfl) ⟨398450, by rfl⟩ : syracuseStep 531267 = 796901) B796901
theorem B793427 : Blo 527800 793427 := bstep (se 1 (by rfl) ⟨595070, by rfl⟩ : syracuseStep 793427 = 1190141) B1190141
theorem B531283 : Blo 527800 531283 := bstep (se 1 (by rfl) ⟨398462, by rfl⟩ : syracuseStep 531283 = 796925) B796925
theorem B531299 : Blo 527800 531299 := bstep (se 1 (by rfl) ⟨398474, by rfl⟩ : syracuseStep 531299 = 796949) B796949
theorem B1514339 : Blo 527800 1514339 := bstep (se 1 (by rfl) ⟨1135754, by rfl⟩ : syracuseStep 1514339 = 2271509) B2271509
theorem B793457 : Blo 527800 793457 := bstep (se 2 (by rfl) ⟨297546, by rfl⟩ : syracuseStep 793457 = 595093) B595093
theorem B531315 : Blo 527800 531315 := bstep (se 1 (by rfl) ⟨398486, by rfl⟩ : syracuseStep 531315 = 796973) B796973
theorem B793475 : Blo 527800 793475 := bstep (se 1 (by rfl) ⟨595106, by rfl⟩ : syracuseStep 793475 = 1190213) B1190213
theorem B531331 : Blo 527800 531331 := bstep (se 1 (by rfl) ⟨398498, by rfl⟩ : syracuseStep 531331 = 796997) B796997
theorem B531347 : Blo 527800 531347 := bstep (se 1 (by rfl) ⟨398510, by rfl⟩ : syracuseStep 531347 = 797021) B797021
theorem B793505 : Blo 527800 793505 := bstep (se 2 (by rfl) ⟨297564, by rfl⟩ : syracuseStep 793505 = 595129) B595129
theorem B531363 : Blo 527800 531363 := bstep (se 1 (by rfl) ⟨398522, by rfl⟩ : syracuseStep 531363 = 797045) B797045
theorem B793523 : Blo 527800 793523 := bstep (se 1 (by rfl) ⟨595142, by rfl⟩ : syracuseStep 793523 = 1190285) B1190285
theorem B531379 : Blo 527800 531379 := bstep (se 1 (by rfl) ⟨398534, by rfl⟩ : syracuseStep 531379 = 797069) B797069
theorem B531395 : Blo 527800 531395 := bstep (se 1 (by rfl) ⟨398546, by rfl⟩ : syracuseStep 531395 = 797093) B797093
theorem B891857 : Blo 527800 891857 := bstep (se 2 (by rfl) ⟨334446, by rfl⟩ : syracuseStep 891857 = 668893) B668893
theorem B793553 : Blo 527800 793553 := bstep (se 2 (by rfl) ⟨297582, by rfl⟩ : syracuseStep 793553 = 595165) B595165
theorem B596947 : Blo 527800 596947 := bstep (se 1 (by rfl) ⟨447710, by rfl⟩ : syracuseStep 596947 = 895421) B895421
theorem B531411 : Blo 527800 531411 := bstep (se 1 (by rfl) ⟨398558, by rfl⟩ : syracuseStep 531411 = 797117) B797117
theorem B793571 : Blo 527800 793571 := bstep (se 1 (by rfl) ⟨595178, by rfl⟩ : syracuseStep 793571 = 1190357) B1190357
theorem B531427 : Blo 527800 531427 := bstep (se 1 (by rfl) ⟨398570, by rfl⟩ : syracuseStep 531427 = 797141) B797141
theorem B531443 : Blo 527800 531443 := bstep (se 1 (by rfl) ⟨398582, by rfl⟩ : syracuseStep 531443 = 797165) B797165
theorem B793601 : Blo 527800 793601 := bstep (se 2 (by rfl) ⟨297600, by rfl⟩ : syracuseStep 793601 = 595201) B595201
theorem B531459 : Blo 527800 531459 := bstep (se 1 (by rfl) ⟨398594, by rfl⟩ : syracuseStep 531459 = 797189) B797189
theorem B793619 : Blo 527800 793619 := bstep (se 1 (by rfl) ⟨595214, by rfl⟩ : syracuseStep 793619 = 1190429) B1190429
theorem B531475 : Blo 527800 531475 := bstep (se 1 (by rfl) ⟨398606, by rfl⟩ : syracuseStep 531475 = 797213) B797213
theorem B531491 : Blo 527800 531491 := bstep (se 1 (by rfl) ⟨398618, by rfl⟩ : syracuseStep 531491 = 797237) B797237
theorem B793649 : Blo 527800 793649 := bstep (se 2 (by rfl) ⟨297618, by rfl⟩ : syracuseStep 793649 = 595237) B595237
theorem B531507 : Blo 527800 531507 := bstep (se 1 (by rfl) ⟨398630, by rfl⟩ : syracuseStep 531507 = 797261) B797261
theorem B793667 : Blo 527800 793667 := bstep (se 1 (by rfl) ⟨595250, by rfl⟩ : syracuseStep 793667 = 1190501) B1190501
theorem B531523 : Blo 527800 531523 := bstep (se 1 (by rfl) ⟨398642, by rfl⟩ : syracuseStep 531523 = 797285) B797285
theorem B891985 : Blo 527800 891985 := bstep (se 2 (by rfl) ⟨334494, by rfl⟩ : syracuseStep 891985 = 668989) B668989
theorem B531539 : Blo 527800 531539 := bstep (se 1 (by rfl) ⟨398654, by rfl⟩ : syracuseStep 531539 = 797309) B797309
theorem B793697 : Blo 527800 793697 := bstep (se 2 (by rfl) ⟨297636, by rfl⟩ : syracuseStep 793697 = 595273) B595273
theorem B597091 : Blo 527800 597091 := bstep (se 1 (by rfl) ⟨447818, by rfl⟩ : syracuseStep 597091 = 895637) B895637
theorem B531555 : Blo 527800 531555 := bstep (se 1 (by rfl) ⟨398666, by rfl⟩ : syracuseStep 531555 = 797333) B797333
theorem B892019 : Blo 527800 892019 := bstep (se 1 (by rfl) ⟨669014, by rfl⟩ : syracuseStep 892019 = 1338029) B1338029
theorem B793715 : Blo 527800 793715 := bstep (se 1 (by rfl) ⟨595286, by rfl⟩ : syracuseStep 793715 = 1190573) B1190573
theorem B531571 : Blo 527800 531571 := bstep (se 1 (by rfl) ⟨398678, by rfl⟩ : syracuseStep 531571 = 797357) B797357
theorem B531587 : Blo 527800 531587 := bstep (se 1 (by rfl) ⟨398690, by rfl⟩ : syracuseStep 531587 = 797381) B797381
theorem B793745 : Blo 527800 793745 := bstep (se 2 (by rfl) ⟨297654, by rfl⟩ : syracuseStep 793745 = 595309) B595309
theorem B531603 : Blo 527800 531603 := bstep (se 1 (by rfl) ⟨398702, by rfl⟩ : syracuseStep 531603 = 797405) B797405
theorem B793763 : Blo 527800 793763 := bstep (se 1 (by rfl) ⟨595322, by rfl⟩ : syracuseStep 793763 = 1190645) B1190645
theorem B531619 : Blo 527800 531619 := bstep (se 1 (by rfl) ⟨398714, by rfl⟩ : syracuseStep 531619 = 797429) B797429
theorem B531635 : Blo 527800 531635 := bstep (se 1 (by rfl) ⟨398726, by rfl⟩ : syracuseStep 531635 = 797453) B797453
theorem B793793 : Blo 527800 793793 := bstep (se 2 (by rfl) ⟨297672, by rfl⟩ : syracuseStep 793793 = 595345) B595345
theorem B531651 : Blo 527800 531651 := bstep (se 1 (by rfl) ⟨398738, by rfl⟩ : syracuseStep 531651 = 797477) B797477
theorem B793811 : Blo 527800 793811 := bstep (se 1 (by rfl) ⟨595358, by rfl⟩ : syracuseStep 793811 = 1190717) B1190717
theorem B531667 : Blo 527800 531667 := bstep (se 1 (by rfl) ⟨398750, by rfl⟩ : syracuseStep 531667 = 797501) B797501
theorem B564451 : Blo 527800 564451 := bstep (se 1 (by rfl) ⟨423338, by rfl⟩ : syracuseStep 564451 = 846677) B846677
theorem B531683 : Blo 527800 531683 := bstep (se 1 (by rfl) ⟨398762, by rfl⟩ : syracuseStep 531683 = 797525) B797525
theorem B793841 : Blo 527800 793841 := bstep (se 2 (by rfl) ⟨297690, by rfl⟩ : syracuseStep 793841 = 595381) B595381
theorem B892147 : Blo 527800 892147 := bstep (se 1 (by rfl) ⟨669110, by rfl⟩ : syracuseStep 892147 = 1338221) B1338221
theorem B597235 : Blo 527800 597235 := bstep (se 1 (by rfl) ⟨447926, by rfl⟩ : syracuseStep 597235 = 895853) B895853
theorem B531699 : Blo 527800 531699 := bstep (se 1 (by rfl) ⟨398774, by rfl⟩ : syracuseStep 531699 = 797549) B797549
theorem B793859 : Blo 527800 793859 := bstep (se 1 (by rfl) ⟨595394, by rfl⟩ : syracuseStep 793859 = 1190789) B1190789
theorem B531715 : Blo 527800 531715 := bstep (se 1 (by rfl) ⟨398786, by rfl⟩ : syracuseStep 531715 = 797573) B797573
theorem B531731 : Blo 527800 531731 := bstep (se 1 (by rfl) ⟨398798, by rfl⟩ : syracuseStep 531731 = 797597) B797597
theorem B793889 : Blo 527800 793889 := bstep (se 2 (by rfl) ⟨297708, by rfl⟩ : syracuseStep 793889 = 595417) B595417
theorem B531747 : Blo 527800 531747 := bstep (se 1 (by rfl) ⟨398810, by rfl⟩ : syracuseStep 531747 = 797621) B797621
theorem B793907 : Blo 527800 793907 := bstep (se 1 (by rfl) ⟨595430, by rfl⟩ : syracuseStep 793907 = 1190861) B1190861
theorem B531763 : Blo 527800 531763 := bstep (se 1 (by rfl) ⟨398822, by rfl⟩ : syracuseStep 531763 = 797645) B797645
theorem B531779 : Blo 527800 531779 := bstep (se 1 (by rfl) ⟨398834, by rfl⟩ : syracuseStep 531779 = 797669) B797669
theorem B793937 : Blo 527800 793937 := bstep (se 2 (by rfl) ⟨297726, by rfl⟩ : syracuseStep 793937 = 595453) B595453
theorem B531795 : Blo 527800 531795 := bstep (se 1 (by rfl) ⟨398846, by rfl⟩ : syracuseStep 531795 = 797693) B797693
theorem B793955 : Blo 527800 793955 := bstep (se 1 (by rfl) ⟨595466, by rfl⟩ : syracuseStep 793955 = 1190933) B1190933
theorem B892289 : Blo 527800 892289 := bstep (se 2 (by rfl) ⟨334608, by rfl⟩ : syracuseStep 892289 = 669217) B669217
theorem B793985 : Blo 527800 793985 := bstep (se 2 (by rfl) ⟨297744, by rfl⟩ : syracuseStep 793985 = 595489) B595489
theorem B597379 : Blo 527800 597379 := bstep (se 1 (by rfl) ⟨448034, by rfl⟩ : syracuseStep 597379 = 896069) B896069
theorem B794003 : Blo 527800 794003 := bstep (se 1 (by rfl) ⟨595502, by rfl⟩ : syracuseStep 794003 = 1191005) B1191005
theorem B794033 : Blo 527800 794033 := bstep (se 2 (by rfl) ⟨297762, by rfl⟩ : syracuseStep 794033 = 595525) B595525
theorem B794051 : Blo 527800 794051 := bstep (se 1 (by rfl) ⟨595538, by rfl⟩ : syracuseStep 794051 = 1191077) B1191077
theorem B794081 : Blo 527800 794081 := bstep (se 2 (by rfl) ⟨297780, by rfl⟩ : syracuseStep 794081 = 595561) B595561
theorem B794099 : Blo 527800 794099 := bstep (se 1 (by rfl) ⟨595574, by rfl⟩ : syracuseStep 794099 = 1191149) B1191149
theorem B892417 : Blo 527800 892417 := bstep (se 2 (by rfl) ⟨334656, by rfl⟩ : syracuseStep 892417 = 669313) B669313
theorem B794129 : Blo 527800 794129 := bstep (se 2 (by rfl) ⟨297798, by rfl⟩ : syracuseStep 794129 = 595597) B595597
theorem B597523 : Blo 527800 597523 := bstep (se 1 (by rfl) ⟨448142, by rfl⟩ : syracuseStep 597523 = 896285) B896285
theorem B892451 : Blo 527800 892451 := bstep (se 1 (by rfl) ⟨669338, by rfl⟩ : syracuseStep 892451 = 1338677) B1338677
theorem B794147 : Blo 527800 794147 := bstep (se 1 (by rfl) ⟨595610, by rfl⟩ : syracuseStep 794147 = 1191221) B1191221
theorem B794177 : Blo 527800 794177 := bstep (se 2 (by rfl) ⟨297816, by rfl⟩ : syracuseStep 794177 = 595633) B595633
theorem B794195 : Blo 527800 794195 := bstep (se 1 (by rfl) ⟨595646, by rfl⟩ : syracuseStep 794195 = 1191293) B1191293
theorem B794225 : Blo 527800 794225 := bstep (se 2 (by rfl) ⟨297834, by rfl⟩ : syracuseStep 794225 = 595669) B595669
theorem B794243 : Blo 527800 794243 := bstep (se 1 (by rfl) ⟨595682, by rfl⟩ : syracuseStep 794243 = 1191365) B1191365
theorem B794273 : Blo 527800 794273 := bstep (se 2 (by rfl) ⟨297852, by rfl⟩ : syracuseStep 794273 = 595705) B595705
theorem B892579 : Blo 527800 892579 := bstep (se 1 (by rfl) ⟨669434, by rfl⟩ : syracuseStep 892579 = 1338869) B1338869
theorem B597667 : Blo 527800 597667 := bstep (se 1 (by rfl) ⟨448250, by rfl⟩ : syracuseStep 597667 = 896501) B896501
theorem B794291 : Blo 527800 794291 := bstep (se 1 (by rfl) ⟨595718, by rfl⟩ : syracuseStep 794291 = 1191437) B1191437
theorem B5119685 : Blo 527800 5119685 := bstep (se 4 (by rfl) ⟨479970, by rfl⟩ : syracuseStep 5119685 = 959941) B959941
theorem B794321 : Blo 527800 794321 := bstep (se 2 (by rfl) ⟨297870, by rfl⟩ : syracuseStep 794321 = 595741) B595741
theorem B794339 : Blo 527800 794339 := bstep (se 1 (by rfl) ⟨595754, by rfl⟩ : syracuseStep 794339 = 1191509) B1191509
theorem B794369 : Blo 527800 794369 := bstep (se 2 (by rfl) ⟨297888, by rfl⟩ : syracuseStep 794369 = 595777) B595777
theorem B794387 : Blo 527800 794387 := bstep (se 1 (by rfl) ⟨595790, by rfl⟩ : syracuseStep 794387 = 1191581) B1191581
theorem B892721 : Blo 527800 892721 := bstep (se 2 (by rfl) ⟨334770, by rfl⟩ : syracuseStep 892721 = 669541) B669541
theorem B794417 : Blo 527800 794417 := bstep (se 2 (by rfl) ⟨297906, by rfl⟩ : syracuseStep 794417 = 595813) B595813
theorem B597811 : Blo 527800 597811 := bstep (se 1 (by rfl) ⟨448358, by rfl⟩ : syracuseStep 597811 = 896717) B896717
theorem B794435 : Blo 527800 794435 := bstep (se 1 (by rfl) ⟨595826, by rfl⟩ : syracuseStep 794435 = 1191653) B1191653
theorem B794465 : Blo 527800 794465 := bstep (se 2 (by rfl) ⟨297924, by rfl⟩ : syracuseStep 794465 = 595849) B595849
theorem B794483 : Blo 527800 794483 := bstep (se 1 (by rfl) ⟨595862, by rfl⟩ : syracuseStep 794483 = 1191725) B1191725
theorem B1187729 : Blo 527800 1187729 := bstep (se 2 (by rfl) ⟨445398, by rfl⟩ : syracuseStep 1187729 = 890797) B890797
theorem B794513 : Blo 527800 794513 := bstep (se 2 (by rfl) ⟨297942, by rfl⟩ : syracuseStep 794513 = 595885) B595885
theorem B1187747 : Blo 527800 1187747 := bstep (se 1 (by rfl) ⟨890810, by rfl⟩ : syracuseStep 1187747 = 1781621) B1781621
theorem B794531 : Blo 527800 794531 := bstep (se 1 (by rfl) ⟨595898, by rfl⟩ : syracuseStep 794531 = 1191797) B1191797
theorem B892849 : Blo 527800 892849 := bstep (se 2 (by rfl) ⟨334818, by rfl⟩ : syracuseStep 892849 = 669637) B669637
theorem B794561 : Blo 527800 794561 := bstep (se 2 (by rfl) ⟨297960, by rfl⟩ : syracuseStep 794561 = 595921) B595921
theorem B597955 : Blo 527800 597955 := bstep (se 1 (by rfl) ⟨448466, by rfl⟩ : syracuseStep 597955 = 896933) B896933
theorem B892883 : Blo 527800 892883 := bstep (se 1 (by rfl) ⟨669662, by rfl⟩ : syracuseStep 892883 = 1339325) B1339325
theorem B794579 : Blo 527800 794579 := bstep (se 1 (by rfl) ⟨595934, by rfl⟩ : syracuseStep 794579 = 1191869) B1191869
theorem B794609 : Blo 527800 794609 := bstep (se 2 (by rfl) ⟨297978, by rfl⟩ : syracuseStep 794609 = 595957) B595957
theorem B794627 : Blo 527800 794627 := bstep (se 1 (by rfl) ⟨595970, by rfl⟩ : syracuseStep 794627 = 1191941) B1191941
theorem B794657 : Blo 527800 794657 := bstep (se 2 (by rfl) ⟨297996, by rfl⟩ : syracuseStep 794657 = 595993) B595993
theorem B2007089 : Blo 527800 2007089 := bstep (se 2 (by rfl) ⟨752658, by rfl⟩ : syracuseStep 2007089 = 1505317) B1505317
theorem B794675 : Blo 527800 794675 := bstep (se 1 (by rfl) ⟨596006, by rfl⟩ : syracuseStep 794675 = 1192013) B1192013
theorem B794705 : Blo 527800 794705 := bstep (se 2 (by rfl) ⟨298014, by rfl⟩ : syracuseStep 794705 = 596029) B596029
theorem B893011 : Blo 527800 893011 := bstep (se 1 (by rfl) ⟨669758, by rfl⟩ : syracuseStep 893011 = 1339517) B1339517
theorem B598099 : Blo 527800 598099 := bstep (se 1 (by rfl) ⟨448574, by rfl⟩ : syracuseStep 598099 = 897149) B897149
theorem B794723 : Blo 527800 794723 := bstep (se 1 (by rfl) ⟨596042, by rfl⟩ : syracuseStep 794723 = 1192085) B1192085
theorem B794753 : Blo 527800 794753 := bstep (se 2 (by rfl) ⟨298032, by rfl⟩ : syracuseStep 794753 = 596065) B596065
theorem B794771 : Blo 527800 794771 := bstep (se 1 (by rfl) ⟨596078, by rfl⟩ : syracuseStep 794771 = 1192157) B1192157
theorem B1188017 : Blo 527800 1188017 := bstep (se 2 (by rfl) ⟨445506, by rfl⟩ : syracuseStep 1188017 = 891013) B891013
theorem B794801 : Blo 527800 794801 := bstep (se 2 (by rfl) ⟨298050, by rfl⟩ : syracuseStep 794801 = 596101) B596101
theorem B1188035 : Blo 527800 1188035 := bstep (se 1 (by rfl) ⟨891026, by rfl⟩ : syracuseStep 1188035 = 1782053) B1782053
theorem B794819 : Blo 527800 794819 := bstep (se 1 (by rfl) ⟨596114, by rfl⟩ : syracuseStep 794819 = 1192229) B1192229
theorem B893153 : Blo 527800 893153 := bstep (se 2 (by rfl) ⟨334932, by rfl⟩ : syracuseStep 893153 = 669865) B669865
theorem B794849 : Blo 527800 794849 := bstep (se 2 (by rfl) ⟨298068, by rfl⟩ : syracuseStep 794849 = 596137) B596137
theorem B598243 : Blo 527800 598243 := bstep (se 1 (by rfl) ⟨448682, by rfl⟩ : syracuseStep 598243 = 897365) B897365
theorem B794867 : Blo 527800 794867 := bstep (se 1 (by rfl) ⟨596150, by rfl⟩ : syracuseStep 794867 = 1192301) B1192301
theorem B794897 : Blo 527800 794897 := bstep (se 2 (by rfl) ⟨298086, by rfl⟩ : syracuseStep 794897 = 596173) B596173
theorem B794915 : Blo 527800 794915 := bstep (se 1 (by rfl) ⟨596186, by rfl⟩ : syracuseStep 794915 = 1192373) B1192373
theorem B794945 : Blo 527800 794945 := bstep (se 2 (by rfl) ⟨298104, by rfl⟩ : syracuseStep 794945 = 596209) B596209
theorem B794963 : Blo 527800 794963 := bstep (se 1 (by rfl) ⟨596222, by rfl⟩ : syracuseStep 794963 = 1192445) B1192445
theorem B893281 : Blo 527800 893281 := bstep (se 2 (by rfl) ⟨334980, by rfl⟩ : syracuseStep 893281 = 669961) B669961
theorem B794993 : Blo 527800 794993 := bstep (se 2 (by rfl) ⟨298122, by rfl⟩ : syracuseStep 794993 = 596245) B596245
theorem B893315 : Blo 527800 893315 := bstep (se 1 (by rfl) ⟨669986, by rfl⟩ : syracuseStep 893315 = 1339973) B1339973
theorem B795011 : Blo 527800 795011 := bstep (se 1 (by rfl) ⟨596258, by rfl⟩ : syracuseStep 795011 = 1192517) B1192517
theorem B795041 : Blo 527800 795041 := bstep (se 2 (by rfl) ⟨298140, by rfl⟩ : syracuseStep 795041 = 596281) B596281
theorem B795059 : Blo 527800 795059 := bstep (se 1 (by rfl) ⟨596294, by rfl⟩ : syracuseStep 795059 = 1192589) B1192589
theorem B1188305 : Blo 527800 1188305 := bstep (se 2 (by rfl) ⟨445614, by rfl⟩ : syracuseStep 1188305 = 891229) B891229
theorem B795089 : Blo 527800 795089 := bstep (se 2 (by rfl) ⟨298158, by rfl⟩ : syracuseStep 795089 = 596317) B596317
theorem B1188323 : Blo 527800 1188323 := bstep (se 1 (by rfl) ⟨891242, by rfl⟩ : syracuseStep 1188323 = 1782485) B1782485
theorem B795107 : Blo 527800 795107 := bstep (se 1 (by rfl) ⟨596330, by rfl⟩ : syracuseStep 795107 = 1192661) B1192661
theorem B3023345 : Blo 527800 3023345 := bstep (se 2 (by rfl) ⟨1133754, by rfl⟩ : syracuseStep 3023345 = 2267509) B2267509
theorem B795137 : Blo 527800 795137 := bstep (se 2 (by rfl) ⟨298176, by rfl⟩ : syracuseStep 795137 = 596353) B596353
theorem B893443 : Blo 527800 893443 := bstep (se 1 (by rfl) ⟨670082, by rfl⟩ : syracuseStep 893443 = 1340165) B1340165
theorem B795155 : Blo 527800 795155 := bstep (se 1 (by rfl) ⟨596366, by rfl⟩ : syracuseStep 795155 = 1192733) B1192733
theorem B795185 : Blo 527800 795185 := bstep (se 2 (by rfl) ⟨298194, by rfl⟩ : syracuseStep 795185 = 596389) B596389
theorem B795203 : Blo 527800 795203 := bstep (se 1 (by rfl) ⟨596402, by rfl⟩ : syracuseStep 795203 = 1192805) B1192805
theorem B795233 : Blo 527800 795233 := bstep (se 2 (by rfl) ⟨298212, by rfl⟩ : syracuseStep 795233 = 596425) B596425
theorem B795251 : Blo 527800 795251 := bstep (se 1 (by rfl) ⟨596438, by rfl⟩ : syracuseStep 795251 = 1192877) B1192877
theorem B893585 : Blo 527800 893585 := bstep (se 2 (by rfl) ⟨335094, by rfl⟩ : syracuseStep 893585 = 670189) B670189
theorem B795281 : Blo 527800 795281 := bstep (se 2 (by rfl) ⟨298230, by rfl⟩ : syracuseStep 795281 = 596461) B596461
theorem B795299 : Blo 527800 795299 := bstep (se 1 (by rfl) ⟨596474, by rfl⟩ : syracuseStep 795299 = 1192949) B1192949
theorem B795329 : Blo 527800 795329 := bstep (se 2 (by rfl) ⟨298248, by rfl⟩ : syracuseStep 795329 = 596497) B596497
theorem B795347 : Blo 527800 795347 := bstep (se 1 (by rfl) ⟨596510, by rfl⟩ : syracuseStep 795347 = 1193021) B1193021
theorem B1188593 : Blo 527800 1188593 := bstep (se 2 (by rfl) ⟨445722, by rfl⟩ : syracuseStep 1188593 = 891445) B891445
theorem B795377 : Blo 527800 795377 := bstep (se 2 (by rfl) ⟨298266, by rfl⟩ : syracuseStep 795377 = 596533) B596533
theorem B1188611 : Blo 527800 1188611 := bstep (se 1 (by rfl) ⟨891458, by rfl⟩ : syracuseStep 1188611 = 1782917) B1782917
theorem B795395 : Blo 527800 795395 := bstep (se 1 (by rfl) ⟨596546, by rfl⟩ : syracuseStep 795395 = 1193093) B1193093
theorem B893713 : Blo 527800 893713 := bstep (se 2 (by rfl) ⟨335142, by rfl⟩ : syracuseStep 893713 = 670285) B670285
theorem B795425 : Blo 527800 795425 := bstep (se 2 (by rfl) ⟨298284, by rfl⟩ : syracuseStep 795425 = 596569) B596569
theorem B893747 : Blo 527800 893747 := bstep (se 1 (by rfl) ⟨670310, by rfl⟩ : syracuseStep 893747 = 1340621) B1340621
theorem B795443 : Blo 527800 795443 := bstep (se 1 (by rfl) ⟨596582, by rfl⟩ : syracuseStep 795443 = 1193165) B1193165
theorem B795473 : Blo 527800 795473 := bstep (se 2 (by rfl) ⟨298302, by rfl⟩ : syracuseStep 795473 = 596605) B596605
theorem B795491 : Blo 527800 795491 := bstep (se 1 (by rfl) ⟨596618, by rfl⟩ : syracuseStep 795491 = 1193237) B1193237
theorem B795521 : Blo 527800 795521 := bstep (se 2 (by rfl) ⟨298320, by rfl⟩ : syracuseStep 795521 = 596641) B596641
theorem B762755 : Blo 527800 762755 := bstep (se 1 (by rfl) ⟨572066, by rfl⟩ : syracuseStep 762755 = 1144133) B1144133
theorem B795539 : Blo 527800 795539 := bstep (se 1 (by rfl) ⟨596654, by rfl⟩ : syracuseStep 795539 = 1193309) B1193309
theorem B795569 : Blo 527800 795569 := bstep (se 2 (by rfl) ⟨298338, by rfl⟩ : syracuseStep 795569 = 596677) B596677
theorem B893875 : Blo 527800 893875 := bstep (se 1 (by rfl) ⟨670406, by rfl⟩ : syracuseStep 893875 = 1340813) B1340813
theorem B795587 : Blo 527800 795587 := bstep (se 1 (by rfl) ⟨596690, by rfl⟩ : syracuseStep 795587 = 1193381) B1193381
theorem B795617 : Blo 527800 795617 := bstep (se 2 (by rfl) ⟨298356, by rfl⟩ : syracuseStep 795617 = 596713) B596713
theorem B795635 : Blo 527800 795635 := bstep (se 1 (by rfl) ⟨596726, by rfl⟩ : syracuseStep 795635 = 1193453) B1193453
theorem B1188881 : Blo 527800 1188881 := bstep (se 2 (by rfl) ⟨445830, by rfl⟩ : syracuseStep 1188881 = 891661) B891661
theorem B795665 : Blo 527800 795665 := bstep (se 2 (by rfl) ⟨298374, by rfl⟩ : syracuseStep 795665 = 596749) B596749
theorem B1188899 : Blo 527800 1188899 := bstep (se 1 (by rfl) ⟨891674, by rfl⟩ : syracuseStep 1188899 = 1783349) B1783349
theorem B795683 : Blo 527800 795683 := bstep (se 1 (by rfl) ⟨596762, by rfl⟩ : syracuseStep 795683 = 1193525) B1193525
theorem B2270243 : Blo 527800 2270243 := bstep (se 1 (by rfl) ⟨1702682, by rfl⟩ : syracuseStep 2270243 = 3405365) B3405365
theorem B894017 : Blo 527800 894017 := bstep (se 2 (by rfl) ⟨335256, by rfl⟩ : syracuseStep 894017 = 670513) B670513
theorem B795713 : Blo 527800 795713 := bstep (se 2 (by rfl) ⟨298392, by rfl⟩ : syracuseStep 795713 = 596785) B596785
theorem B795731 : Blo 527800 795731 := bstep (se 1 (by rfl) ⟨596798, by rfl⟩ : syracuseStep 795731 = 1193597) B1193597
theorem B795761 : Blo 527800 795761 := bstep (se 2 (by rfl) ⟨298410, by rfl⟩ : syracuseStep 795761 = 596821) B596821
theorem B795779 : Blo 527800 795779 := bstep (se 1 (by rfl) ⟨596834, by rfl⟩ : syracuseStep 795779 = 1193669) B1193669
theorem B795809 : Blo 527800 795809 := bstep (se 2 (by rfl) ⟨298428, by rfl⟩ : syracuseStep 795809 = 596857) B596857
theorem B795827 : Blo 527800 795827 := bstep (se 1 (by rfl) ⟨596870, by rfl⟩ : syracuseStep 795827 = 1193741) B1193741
theorem B894145 : Blo 527800 894145 := bstep (se 2 (by rfl) ⟨335304, by rfl⟩ : syracuseStep 894145 = 670609) B670609
theorem B795857 : Blo 527800 795857 := bstep (se 2 (by rfl) ⟨298446, by rfl⟩ : syracuseStep 795857 = 596893) B596893
theorem B894179 : Blo 527800 894179 := bstep (se 1 (by rfl) ⟨670634, by rfl⟩ : syracuseStep 894179 = 1341269) B1341269
theorem B795875 : Blo 527800 795875 := bstep (se 1 (by rfl) ⟨596906, by rfl⟩ : syracuseStep 795875 = 1193813) B1193813
theorem B795905 : Blo 527800 795905 := bstep (se 2 (by rfl) ⟨298464, by rfl⟩ : syracuseStep 795905 = 596929) B596929
theorem B795923 : Blo 527800 795923 := bstep (se 1 (by rfl) ⟨596942, by rfl⟩ : syracuseStep 795923 = 1193885) B1193885
theorem B1189169 : Blo 527800 1189169 := bstep (se 2 (by rfl) ⟨445938, by rfl⟩ : syracuseStep 1189169 = 891877) B891877
theorem B795953 : Blo 527800 795953 := bstep (se 2 (by rfl) ⟨298482, by rfl⟩ : syracuseStep 795953 = 596965) B596965
theorem B1189187 : Blo 527800 1189187 := bstep (se 1 (by rfl) ⟨891890, by rfl⟩ : syracuseStep 1189187 = 1783781) B1783781
theorem B795971 : Blo 527800 795971 := bstep (se 1 (by rfl) ⟨596978, by rfl⟩ : syracuseStep 795971 = 1193957) B1193957
theorem B796001 : Blo 527800 796001 := bstep (se 2 (by rfl) ⟨298500, by rfl⟩ : syracuseStep 796001 = 597001) B597001
theorem B894307 : Blo 527800 894307 := bstep (se 1 (by rfl) ⟨670730, by rfl⟩ : syracuseStep 894307 = 1341461) B1341461
theorem B796019 : Blo 527800 796019 := bstep (se 1 (by rfl) ⟨597014, by rfl⟩ : syracuseStep 796019 = 1194029) B1194029
theorem B796049 : Blo 527800 796049 := bstep (se 2 (by rfl) ⟨298518, by rfl⟩ : syracuseStep 796049 = 597037) B597037
theorem B796067 : Blo 527800 796067 := bstep (se 1 (by rfl) ⟨597050, by rfl⟩ : syracuseStep 796067 = 1194101) B1194101
theorem B796097 : Blo 527800 796097 := bstep (se 2 (by rfl) ⟨298536, by rfl⟩ : syracuseStep 796097 = 597073) B597073
theorem B796115 : Blo 527800 796115 := bstep (se 1 (by rfl) ⟨597086, by rfl⟩ : syracuseStep 796115 = 1194173) B1194173
theorem B2008547 : Blo 527800 2008547 := bstep (se 1 (by rfl) ⟨1506410, by rfl⟩ : syracuseStep 2008547 = 3012821) B3012821
theorem B1910243 : Blo 527800 1910243 := bstep (se 1 (by rfl) ⟨1432682, by rfl⟩ : syracuseStep 1910243 = 2865365) B2865365
theorem B894449 : Blo 527800 894449 := bstep (se 2 (by rfl) ⟨335418, by rfl⟩ : syracuseStep 894449 = 670837) B670837
theorem B796145 : Blo 527800 796145 := bstep (se 2 (by rfl) ⟨298554, by rfl⟩ : syracuseStep 796145 = 597109) B597109
theorem B796163 : Blo 527800 796163 := bstep (se 1 (by rfl) ⟨597122, by rfl⟩ : syracuseStep 796163 = 1194245) B1194245
theorem B796193 : Blo 527800 796193 := bstep (se 2 (by rfl) ⟨298572, by rfl⟩ : syracuseStep 796193 = 597145) B597145
theorem B796211 : Blo 527800 796211 := bstep (se 1 (by rfl) ⟨597158, by rfl⟩ : syracuseStep 796211 = 1194317) B1194317
theorem B1189457 : Blo 527800 1189457 := bstep (se 2 (by rfl) ⟨446046, by rfl⟩ : syracuseStep 1189457 = 892093) B892093
theorem B796241 : Blo 527800 796241 := bstep (se 2 (by rfl) ⟨298590, by rfl⟩ : syracuseStep 796241 = 597181) B597181
theorem B1189475 : Blo 527800 1189475 := bstep (se 1 (by rfl) ⟨892106, by rfl⟩ : syracuseStep 1189475 = 1784213) B1784213
theorem B796259 : Blo 527800 796259 := bstep (se 1 (by rfl) ⟨597194, by rfl⟩ : syracuseStep 796259 = 1194389) B1194389
theorem B894577 : Blo 527800 894577 := bstep (se 2 (by rfl) ⟨335466, by rfl⟩ : syracuseStep 894577 = 670933) B670933
theorem B796289 : Blo 527800 796289 := bstep (se 2 (by rfl) ⟨298608, by rfl⟩ : syracuseStep 796289 = 597217) B597217
theorem B894611 : Blo 527800 894611 := bstep (se 1 (by rfl) ⟨670958, by rfl⟩ : syracuseStep 894611 = 1341917) B1341917
theorem B796307 : Blo 527800 796307 := bstep (se 1 (by rfl) ⟨597230, by rfl⟩ : syracuseStep 796307 = 1194461) B1194461
theorem B796337 : Blo 527800 796337 := bstep (se 2 (by rfl) ⟨298626, by rfl⟩ : syracuseStep 796337 = 597253) B597253
theorem B796355 : Blo 527800 796355 := bstep (se 1 (by rfl) ⟨597266, by rfl⟩ : syracuseStep 796355 = 1194533) B1194533
theorem B796385 : Blo 527800 796385 := bstep (se 2 (by rfl) ⟨298644, by rfl⟩ : syracuseStep 796385 = 597289) B597289
theorem B796403 : Blo 527800 796403 := bstep (se 1 (by rfl) ⟨597302, by rfl⟩ : syracuseStep 796403 = 1194605) B1194605
theorem B796433 : Blo 527800 796433 := bstep (se 2 (by rfl) ⟨298662, by rfl⟩ : syracuseStep 796433 = 597325) B597325
theorem B894739 : Blo 527800 894739 := bstep (se 1 (by rfl) ⟨671054, by rfl⟩ : syracuseStep 894739 = 1342109) B1342109
theorem B796451 : Blo 527800 796451 := bstep (se 1 (by rfl) ⟨597338, by rfl⟩ : syracuseStep 796451 = 1194677) B1194677
theorem B567091 : Blo 527800 567091 := bstep (se 1 (by rfl) ⟨425318, by rfl⟩ : syracuseStep 567091 = 850637) B850637
theorem B796481 : Blo 527800 796481 := bstep (se 2 (by rfl) ⟨298680, by rfl⟩ : syracuseStep 796481 = 597361) B597361
theorem B796499 : Blo 527800 796499 := bstep (se 1 (by rfl) ⟨597374, by rfl⟩ : syracuseStep 796499 = 1194749) B1194749
theorem B1189745 : Blo 527800 1189745 := bstep (se 2 (by rfl) ⟨446154, by rfl⟩ : syracuseStep 1189745 = 892309) B892309
theorem B796529 : Blo 527800 796529 := bstep (se 2 (by rfl) ⟨298698, by rfl⟩ : syracuseStep 796529 = 597397) B597397
theorem B1189763 : Blo 527800 1189763 := bstep (se 1 (by rfl) ⟨892322, by rfl⟩ : syracuseStep 1189763 = 1784645) B1784645
theorem B796547 : Blo 527800 796547 := bstep (se 1 (by rfl) ⟨597410, by rfl⟩ : syracuseStep 796547 = 1194821) B1194821
theorem B894881 : Blo 527800 894881 := bstep (se 2 (by rfl) ⟨335580, by rfl⟩ : syracuseStep 894881 = 671161) B671161
theorem B796577 : Blo 527800 796577 := bstep (se 2 (by rfl) ⟨298716, by rfl⟩ : syracuseStep 796577 = 597433) B597433
theorem B3024803 : Blo 527800 3024803 := bstep (se 1 (by rfl) ⟨2268602, by rfl⟩ : syracuseStep 3024803 = 4537205) B4537205
theorem B796595 : Blo 527800 796595 := bstep (se 1 (by rfl) ⟨597446, by rfl⟩ : syracuseStep 796595 = 1194893) B1194893
theorem B796625 : Blo 527800 796625 := bstep (se 2 (by rfl) ⟨298734, by rfl⟩ : syracuseStep 796625 = 597469) B597469
theorem B9054179 : Blo 527800 9054179 := bstep (se 1 (by rfl) ⟨6790634, by rfl⟩ : syracuseStep 9054179 = 13581269) B13581269
theorem B796643 : Blo 527800 796643 := bstep (se 1 (by rfl) ⟨597482, by rfl⟩ : syracuseStep 796643 = 1194965) B1194965
theorem B2861041 : Blo 527800 2861041 := bstep (se 2 (by rfl) ⟨1072890, by rfl⟩ : syracuseStep 2861041 = 2145781) B2145781
theorem B796673 : Blo 527800 796673 := bstep (se 2 (by rfl) ⟨298752, by rfl⟩ : syracuseStep 796673 = 597505) B597505
theorem B796691 : Blo 527800 796691 := bstep (se 1 (by rfl) ⟨597518, by rfl⟩ : syracuseStep 796691 = 1195037) B1195037
theorem B895009 : Blo 527800 895009 := bstep (se 2 (by rfl) ⟨335628, by rfl⟩ : syracuseStep 895009 = 671257) B671257
theorem B796721 : Blo 527800 796721 := bstep (se 2 (by rfl) ⟨298770, by rfl⟩ : syracuseStep 796721 = 597541) B597541
theorem B895043 : Blo 527800 895043 := bstep (se 1 (by rfl) ⟨671282, by rfl⟩ : syracuseStep 895043 = 1342565) B1342565
theorem B796739 : Blo 527800 796739 := bstep (se 1 (by rfl) ⟨597554, by rfl⟩ : syracuseStep 796739 = 1195109) B1195109
theorem B796769 : Blo 527800 796769 := bstep (se 2 (by rfl) ⟨298788, by rfl⟩ : syracuseStep 796769 = 597577) B597577
theorem B796787 : Blo 527800 796787 := bstep (se 1 (by rfl) ⟨597590, by rfl⟩ : syracuseStep 796787 = 1195181) B1195181
theorem B1190033 : Blo 527800 1190033 := bstep (se 2 (by rfl) ⟨446262, by rfl⟩ : syracuseStep 1190033 = 892525) B892525
theorem B796817 : Blo 527800 796817 := bstep (se 2 (by rfl) ⟨298806, by rfl⟩ : syracuseStep 796817 = 597613) B597613
theorem B1190051 : Blo 527800 1190051 := bstep (se 1 (by rfl) ⟨892538, by rfl⟩ : syracuseStep 1190051 = 1785077) B1785077
theorem B796835 : Blo 527800 796835 := bstep (se 1 (by rfl) ⟨597626, by rfl⟩ : syracuseStep 796835 = 1195253) B1195253
theorem B796865 : Blo 527800 796865 := bstep (se 2 (by rfl) ⟨298824, by rfl⟩ : syracuseStep 796865 = 597649) B597649
theorem B895171 : Blo 527800 895171 := bstep (se 1 (by rfl) ⟨671378, by rfl⟩ : syracuseStep 895171 = 1342757) B1342757
theorem B796883 : Blo 527800 796883 := bstep (se 1 (by rfl) ⟨597662, by rfl⟩ : syracuseStep 796883 = 1195325) B1195325
theorem B567523 : Blo 527800 567523 := bstep (se 1 (by rfl) ⟨425642, by rfl⟩ : syracuseStep 567523 = 851285) B851285
theorem B796913 : Blo 527800 796913 := bstep (se 2 (by rfl) ⟨298842, by rfl⟩ : syracuseStep 796913 = 597685) B597685
theorem B2271473 : Blo 527800 2271473 := bstep (se 2 (by rfl) ⟨851802, by rfl⟩ : syracuseStep 2271473 = 1703605) B1703605
theorem B796931 : Blo 527800 796931 := bstep (se 1 (by rfl) ⟨597698, by rfl⟩ : syracuseStep 796931 = 1195397) B1195397
theorem B796961 : Blo 527800 796961 := bstep (se 2 (by rfl) ⟨298860, by rfl⟩ : syracuseStep 796961 = 597721) B597721
theorem B796979 : Blo 527800 796979 := bstep (se 1 (by rfl) ⟨597734, by rfl⟩ : syracuseStep 796979 = 1195469) B1195469
theorem B895313 : Blo 527800 895313 := bstep (se 2 (by rfl) ⟨335742, by rfl⟩ : syracuseStep 895313 = 671485) B671485
theorem B797009 : Blo 527800 797009 := bstep (se 2 (by rfl) ⟨298878, by rfl⟩ : syracuseStep 797009 = 597757) B597757
theorem B797027 : Blo 527800 797027 := bstep (se 1 (by rfl) ⟨597770, by rfl⟩ : syracuseStep 797027 = 1195541) B1195541
theorem B797057 : Blo 527800 797057 := bstep (se 2 (by rfl) ⟨298896, by rfl⟩ : syracuseStep 797057 = 597793) B597793
theorem B797075 : Blo 527800 797075 := bstep (se 1 (by rfl) ⟨597806, by rfl⟩ : syracuseStep 797075 = 1195613) B1195613
theorem B1190321 : Blo 527800 1190321 := bstep (se 2 (by rfl) ⟨446370, by rfl⟩ : syracuseStep 1190321 = 892741) B892741
theorem B797105 : Blo 527800 797105 := bstep (se 2 (by rfl) ⟨298914, by rfl⟩ : syracuseStep 797105 = 597829) B597829
theorem B1190339 : Blo 527800 1190339 := bstep (se 1 (by rfl) ⟨892754, by rfl⟩ : syracuseStep 1190339 = 1785509) B1785509
theorem B797123 : Blo 527800 797123 := bstep (se 1 (by rfl) ⟨597842, by rfl⟩ : syracuseStep 797123 = 1195685) B1195685
theorem B2009549 : Blo 527800 2009549 := bstep (se 3 (by rfl) ⟨376790, by rfl⟩ : syracuseStep 2009549 = 753581) B753581
theorem B895441 : Blo 527800 895441 := bstep (se 2 (by rfl) ⟨335790, by rfl⟩ : syracuseStep 895441 = 671581) B671581
theorem B797153 : Blo 527800 797153 := bstep (se 2 (by rfl) ⟨298932, by rfl⟩ : syracuseStep 797153 = 597865) B597865
theorem B895475 : Blo 527800 895475 := bstep (se 1 (by rfl) ⟨671606, by rfl⟩ : syracuseStep 895475 = 1343213) B1343213
theorem B797171 : Blo 527800 797171 := bstep (se 1 (by rfl) ⟨597878, by rfl⟩ : syracuseStep 797171 = 1195757) B1195757
theorem B3058181 : Blo 527800 3058181 := bstep (se 4 (by rfl) ⟨286704, by rfl⟩ : syracuseStep 3058181 = 573409) B573409
theorem B797201 : Blo 527800 797201 := bstep (se 2 (by rfl) ⟨298950, by rfl⟩ : syracuseStep 797201 = 597901) B597901
theorem B797219 : Blo 527800 797219 := bstep (se 1 (by rfl) ⟨597914, by rfl⟩ : syracuseStep 797219 = 1195829) B1195829
theorem B797249 : Blo 527800 797249 := bstep (se 2 (by rfl) ⟨298968, by rfl⟩ : syracuseStep 797249 = 597937) B597937
theorem B797267 : Blo 527800 797267 := bstep (se 1 (by rfl) ⟨597950, by rfl⟩ : syracuseStep 797267 = 1195901) B1195901
theorem B797297 : Blo 527800 797297 := bstep (se 2 (by rfl) ⟨298986, by rfl⟩ : syracuseStep 797297 = 597973) B597973
theorem B895603 : Blo 527800 895603 := bstep (se 1 (by rfl) ⟨671702, by rfl⟩ : syracuseStep 895603 = 1343405) B1343405
theorem B797315 : Blo 527800 797315 := bstep (se 1 (by rfl) ⟨597986, by rfl⟩ : syracuseStep 797315 = 1195973) B1195973
theorem B797345 : Blo 527800 797345 := bstep (se 2 (by rfl) ⟨299004, by rfl⟩ : syracuseStep 797345 = 598009) B598009
theorem B797363 : Blo 527800 797363 := bstep (se 1 (by rfl) ⟨598022, by rfl⟩ : syracuseStep 797363 = 1196045) B1196045
theorem B1190609 : Blo 527800 1190609 := bstep (se 2 (by rfl) ⟨446478, by rfl⟩ : syracuseStep 1190609 = 892957) B892957
theorem B797393 : Blo 527800 797393 := bstep (se 2 (by rfl) ⟨299022, by rfl⟩ : syracuseStep 797393 = 598045) B598045
theorem B25701077 : Blo 527800 25701077 := bstep (se 7 (by rfl) ⟨301184, by rfl⟩ : syracuseStep 25701077 = 602369) B602369
theorem B1190627 : Blo 527800 1190627 := bstep (se 1 (by rfl) ⟨892970, by rfl⟩ : syracuseStep 1190627 = 1785941) B1785941
theorem B797411 : Blo 527800 797411 := bstep (se 1 (by rfl) ⟨598058, by rfl⟩ : syracuseStep 797411 = 1196117) B1196117
theorem B895745 : Blo 527800 895745 := bstep (se 2 (by rfl) ⟨335904, by rfl⟩ : syracuseStep 895745 = 671809) B671809
theorem B797441 : Blo 527800 797441 := bstep (se 2 (by rfl) ⟨299040, by rfl⟩ : syracuseStep 797441 = 598081) B598081
theorem B797459 : Blo 527800 797459 := bstep (se 1 (by rfl) ⟨598094, by rfl⟩ : syracuseStep 797459 = 1196189) B1196189
theorem B1354531 : Blo 527800 1354531 := bstep (se 1 (by rfl) ⟨1015898, by rfl⟩ : syracuseStep 1354531 = 2031797) B2031797
theorem B797489 : Blo 527800 797489 := bstep (se 2 (by rfl) ⟨299058, by rfl⟩ : syracuseStep 797489 = 598117) B598117
theorem B797507 : Blo 527800 797507 := bstep (se 1 (by rfl) ⟨598130, by rfl⟩ : syracuseStep 797507 = 1196261) B1196261
theorem B797537 : Blo 527800 797537 := bstep (se 2 (by rfl) ⟨299076, by rfl⟩ : syracuseStep 797537 = 598153) B598153
theorem B797555 : Blo 527800 797555 := bstep (se 1 (by rfl) ⟨598166, by rfl⟩ : syracuseStep 797555 = 1196333) B1196333
theorem B895873 : Blo 527800 895873 := bstep (se 2 (by rfl) ⟨335952, by rfl⟩ : syracuseStep 895873 = 671905) B671905
theorem B1682317 : Blo 527800 1682317 := bstep (se 3 (by rfl) ⟨315434, by rfl⟩ : syracuseStep 1682317 = 630869) B630869
theorem B797585 : Blo 527800 797585 := bstep (se 2 (by rfl) ⟨299094, by rfl⟩ : syracuseStep 797585 = 598189) B598189
theorem B895907 : Blo 527800 895907 := bstep (se 1 (by rfl) ⟨671930, by rfl⟩ : syracuseStep 895907 = 1343861) B1343861
theorem B797603 : Blo 527800 797603 := bstep (se 1 (by rfl) ⟨598202, by rfl⟩ : syracuseStep 797603 = 1196405) B1196405
theorem B797633 : Blo 527800 797633 := bstep (se 2 (by rfl) ⟨299112, by rfl⟩ : syracuseStep 797633 = 598225) B598225
theorem B797651 : Blo 527800 797651 := bstep (se 1 (by rfl) ⟨598238, by rfl⟩ : syracuseStep 797651 = 1196477) B1196477
theorem B1190897 : Blo 527800 1190897 := bstep (se 2 (by rfl) ⟨446586, by rfl⟩ : syracuseStep 1190897 = 893173) B893173
theorem B797681 : Blo 527800 797681 := bstep (se 2 (by rfl) ⟨299130, by rfl⟩ : syracuseStep 797681 = 598261) B598261
theorem B1190915 : Blo 527800 1190915 := bstep (se 1 (by rfl) ⟨893186, by rfl⟩ : syracuseStep 1190915 = 1786373) B1786373
theorem B797699 : Blo 527800 797699 := bstep (se 1 (by rfl) ⟨598274, by rfl⟩ : syracuseStep 797699 = 1196549) B1196549
theorem B896035 : Blo 527800 896035 := bstep (se 1 (by rfl) ⟨672026, by rfl⟩ : syracuseStep 896035 = 1344053) B1344053
theorem B535667 : Blo 527800 535667 := bstep (se 1 (by rfl) ⟨401750, by rfl⟩ : syracuseStep 535667 = 803501) B803501
theorem B896177 : Blo 527800 896177 := bstep (se 2 (by rfl) ⟨336066, by rfl⟩ : syracuseStep 896177 = 672133) B672133
theorem B1191185 : Blo 527800 1191185 := bstep (se 2 (by rfl) ⟨446694, by rfl⟩ : syracuseStep 1191185 = 893389) B893389
theorem B1191203 : Blo 527800 1191203 := bstep (se 1 (by rfl) ⟨893402, by rfl⟩ : syracuseStep 1191203 = 1786805) B1786805
theorem B896305 : Blo 527800 896305 := bstep (se 2 (by rfl) ⟨336114, by rfl⟩ : syracuseStep 896305 = 672229) B672229
theorem B896339 : Blo 527800 896339 := bstep (se 1 (by rfl) ⟨672254, by rfl⟩ : syracuseStep 896339 = 1344509) B1344509
theorem B2862533 : Blo 527800 2862533 := bstep (se 4 (by rfl) ⟨268362, by rfl⟩ : syracuseStep 2862533 = 536725) B536725
theorem B896467 : Blo 527800 896467 := bstep (se 1 (by rfl) ⟨672350, by rfl⟩ : syracuseStep 896467 = 1344701) B1344701
theorem B1191473 : Blo 527800 1191473 := bstep (se 2 (by rfl) ⟨446802, by rfl⟩ : syracuseStep 1191473 = 893605) B893605
theorem B1191491 : Blo 527800 1191491 := bstep (se 1 (by rfl) ⟨893618, by rfl⟩ : syracuseStep 1191491 = 1787237) B1787237
theorem B896609 : Blo 527800 896609 := bstep (se 2 (by rfl) ⟨336228, by rfl⟩ : syracuseStep 896609 = 672457) B672457
theorem B896737 : Blo 527800 896737 := bstep (se 2 (by rfl) ⟨336276, by rfl⟩ : syracuseStep 896737 = 672553) B672553
theorem B896771 : Blo 527800 896771 := bstep (se 1 (by rfl) ⟨672578, by rfl⟩ : syracuseStep 896771 = 1345157) B1345157
theorem B1191761 : Blo 527800 1191761 := bstep (se 2 (by rfl) ⟨446910, by rfl⟩ : syracuseStep 1191761 = 893821) B893821
theorem B1191779 : Blo 527800 1191779 := bstep (se 1 (by rfl) ⟨893834, by rfl⟩ : syracuseStep 1191779 = 1787669) B1787669
theorem B896899 : Blo 527800 896899 := bstep (se 1 (by rfl) ⟨672674, by rfl⟩ : syracuseStep 896899 = 1345349) B1345349
theorem B634835 : Blo 527800 634835 := bstep (se 1 (by rfl) ⟨476126, by rfl⟩ : syracuseStep 634835 = 952253) B952253
theorem B6467597 : Blo 527800 6467597 := bstep (se 3 (by rfl) ⟨1212674, by rfl⟩ : syracuseStep 6467597 = 2425349) B2425349
theorem B897041 : Blo 527800 897041 := bstep (se 2 (by rfl) ⟨336390, by rfl⟩ : syracuseStep 897041 = 672781) B672781
theorem B1781837 : Blo 527800 1781837 := bstep (se 3 (by rfl) ⟨334094, by rfl⟩ : syracuseStep 1781837 = 668189) B668189
theorem B1192049 : Blo 527800 1192049 := bstep (se 2 (by rfl) ⟨447018, by rfl⟩ : syracuseStep 1192049 = 894037) B894037
theorem B1781891 : Blo 527800 1781891 := bstep (se 1 (by rfl) ⟨1336418, by rfl⟩ : syracuseStep 1781891 = 2672837) B2672837
theorem B1192067 : Blo 527800 1192067 := bstep (se 1 (by rfl) ⟨894050, by rfl⟩ : syracuseStep 1192067 = 1788101) B1788101
theorem B897169 : Blo 527800 897169 := bstep (se 2 (by rfl) ⟨336438, by rfl⟩ : syracuseStep 897169 = 672877) B672877
theorem B897203 : Blo 527800 897203 := bstep (se 1 (by rfl) ⟨672902, by rfl⟩ : syracuseStep 897203 = 1345805) B1345805
theorem B1224931 : Blo 527800 1224931 := bstep (se 1 (by rfl) ⟨918698, by rfl⟩ : syracuseStep 1224931 = 1837397) B1837397
theorem B4534541 : Blo 527800 4534541 := bstep (se 3 (by rfl) ⟨850226, by rfl⟩ : syracuseStep 4534541 = 1700453) B1700453
theorem B1716515 : Blo 527800 1716515 := bstep (se 1 (by rfl) ⟨1287386, by rfl⟩ : syracuseStep 1716515 = 2574773) B2574773
theorem B897331 : Blo 527800 897331 := bstep (se 1 (by rfl) ⟨672998, by rfl⟩ : syracuseStep 897331 = 1345997) B1345997
theorem B1782161 : Blo 527800 1782161 := bstep (se 2 (by rfl) ⟨668310, by rfl⟩ : syracuseStep 1782161 = 1336621) B1336621
theorem B1192337 : Blo 527800 1192337 := bstep (se 2 (by rfl) ⟨447126, by rfl⟩ : syracuseStep 1192337 = 894253) B894253
theorem B1192355 : Blo 527800 1192355 := bstep (se 1 (by rfl) ⟨894266, by rfl⟩ : syracuseStep 1192355 = 1788533) B1788533
theorem B668083 : Blo 527800 668083 := bstep (se 1 (by rfl) ⟨501062, by rfl⟩ : syracuseStep 668083 = 1002125) B1002125
theorem B635315 : Blo 527800 635315 := bstep (se 1 (by rfl) ⟨476486, by rfl⟩ : syracuseStep 635315 = 952973) B952973
theorem B1290737 : Blo 527800 1290737 := bstep (se 2 (by rfl) ⟨484026, by rfl⟩ : syracuseStep 1290737 = 968053) B968053
theorem B2011661 : Blo 527800 2011661 := bstep (se 3 (by rfl) ⟨377186, by rfl⟩ : syracuseStep 2011661 = 754373) B754373
theorem B668179 : Blo 527800 668179 := bstep (se 1 (by rfl) ⟨501134, by rfl⟩ : syracuseStep 668179 = 1002269) B1002269
theorem B766531 : Blo 527800 766531 := bstep (se 1 (by rfl) ⟨574898, by rfl⟩ : syracuseStep 766531 = 1149797) B1149797
theorem B1192625 : Blo 527800 1192625 := bstep (se 2 (by rfl) ⟨447234, by rfl⟩ : syracuseStep 1192625 = 894469) B894469
theorem B766657 : Blo 527800 766657 := bstep (se 2 (by rfl) ⟨287496, by rfl⟩ : syracuseStep 766657 = 574993) B574993
theorem B1192643 : Blo 527800 1192643 := bstep (se 1 (by rfl) ⟨894482, by rfl⟩ : syracuseStep 1192643 = 1788965) B1788965
theorem B4633357 : Blo 527800 4633357 := bstep (se 3 (by rfl) ⟨868754, by rfl⟩ : syracuseStep 4633357 = 1737509) B1737509
theorem B1782701 : Blo 527800 1782701 := bstep (se 3 (by rfl) ⟨334256, by rfl⟩ : syracuseStep 1782701 = 668513) B668513
theorem B1192913 : Blo 527800 1192913 := bstep (se 2 (by rfl) ⟨447342, by rfl⟩ : syracuseStep 1192913 = 894685) B894685
theorem B1782755 : Blo 527800 1782755 := bstep (se 1 (by rfl) ⟨1337066, by rfl⟩ : syracuseStep 1782755 = 2674133) B2674133
theorem B1192931 : Blo 527800 1192931 := bstep (se 1 (by rfl) ⟨894698, by rfl⟩ : syracuseStep 1192931 = 1789397) B1789397
theorem B668675 : Blo 527800 668675 := bstep (se 1 (by rfl) ⟨501506, by rfl⟩ : syracuseStep 668675 = 1003013) B1003013
theorem B1127459 : Blo 527800 1127459 := bstep (se 1 (by rfl) ⟨845594, by rfl⟩ : syracuseStep 1127459 = 1691189) B1691189
theorem B1553489 : Blo 527800 1553489 := bstep (se 2 (by rfl) ⟨582558, by rfl⟩ : syracuseStep 1553489 = 1165117) B1165117
theorem B1717393 : Blo 527800 1717393 := bstep (se 2 (by rfl) ⟨644022, by rfl⟩ : syracuseStep 1717393 = 1288045) B1288045
theorem B537763 : Blo 527800 537763 := bstep (se 1 (by rfl) ⟨403322, by rfl⟩ : syracuseStep 537763 = 806645) B806645
theorem B1783025 : Blo 527800 1783025 := bstep (se 2 (by rfl) ⟨668634, by rfl⟩ : syracuseStep 1783025 = 1337269) B1337269
theorem B1193201 : Blo 527800 1193201 := bstep (se 2 (by rfl) ⟨447450, by rfl⟩ : syracuseStep 1193201 = 894901) B894901
theorem B1193219 : Blo 527800 1193219 := bstep (se 1 (by rfl) ⟨894914, by rfl⟩ : syracuseStep 1193219 = 1789829) B1789829
theorem B3257605 : Blo 527800 3257605 := bstep (se 4 (by rfl) ⟨305400, by rfl⟩ : syracuseStep 3257605 = 610801) B610801
theorem B2012465 : Blo 527800 2012465 := bstep (se 2 (by rfl) ⟨754674, by rfl⟩ : syracuseStep 2012465 = 1509349) B1509349
theorem B1193489 : Blo 527800 1193489 := bstep (se 2 (by rfl) ⟨447558, by rfl⟩ : syracuseStep 1193489 = 895117) B895117
theorem B1193507 : Blo 527800 1193507 := bstep (se 1 (by rfl) ⟨895130, by rfl⟩ : syracuseStep 1193507 = 1790261) B1790261
theorem B669379 : Blo 527800 669379 := bstep (se 1 (by rfl) ⟨502034, by rfl⟩ : syracuseStep 669379 = 1004069) B1004069
theorem B1783565 : Blo 527800 1783565 := bstep (se 3 (by rfl) ⟨334418, by rfl⟩ : syracuseStep 1783565 = 668837) B668837
theorem B27997973 : Blo 527800 27997973 := bstep (se 6 (by rfl) ⟨656202, by rfl⟩ : syracuseStep 27997973 = 1312405) B1312405
theorem B669475 : Blo 527800 669475 := bstep (se 1 (by rfl) ⟨502106, by rfl⟩ : syracuseStep 669475 = 1004213) B1004213
theorem B1193777 : Blo 527800 1193777 := bstep (se 2 (by rfl) ⟨447666, by rfl⟩ : syracuseStep 1193777 = 895333) B895333
theorem B1783619 : Blo 527800 1783619 := bstep (se 1 (by rfl) ⟨1337714, by rfl⟩ : syracuseStep 1783619 = 2675429) B2675429
theorem B1193795 : Blo 527800 1193795 := bstep (se 1 (by rfl) ⟨895346, by rfl⟩ : syracuseStep 1193795 = 1790693) B1790693
theorem B1128305 : Blo 527800 1128305 := bstep (se 2 (by rfl) ⟨423114, by rfl⟩ : syracuseStep 1128305 = 846229) B846229
theorem B2013133 : Blo 527800 2013133 := bstep (se 3 (by rfl) ⟨377462, by rfl⟩ : syracuseStep 2013133 = 754925) B754925
theorem B3881029 : Blo 527800 3881029 := bstep (se 4 (by rfl) ⟨363846, by rfl⟩ : syracuseStep 3881029 = 727693) B727693
theorem B1783889 : Blo 527800 1783889 := bstep (se 2 (by rfl) ⟨668958, by rfl⟩ : syracuseStep 1783889 = 1337917) B1337917
theorem B1194065 : Blo 527800 1194065 := bstep (se 2 (by rfl) ⟨447774, by rfl⟩ : syracuseStep 1194065 = 895549) B895549
theorem B1194083 : Blo 527800 1194083 := bstep (se 1 (by rfl) ⟨895562, by rfl⟩ : syracuseStep 1194083 = 1791125) B1791125
theorem B669971 : Blo 527800 669971 := bstep (se 1 (by rfl) ⟨502478, by rfl⟩ : syracuseStep 669971 = 1004957) B1004957
theorem B1194353 : Blo 527800 1194353 := bstep (se 2 (by rfl) ⟨447882, by rfl⟩ : syracuseStep 1194353 = 895765) B895765
theorem B1194371 : Blo 527800 1194371 := bstep (se 1 (by rfl) ⟨895778, by rfl⟩ : syracuseStep 1194371 = 1791557) B1791557
theorem B3389987 : Blo 527800 3389987 := bstep (se 1 (by rfl) ⟨2542490, by rfl⟩ : syracuseStep 3389987 = 5084981) B5084981
theorem B637507 : Blo 527800 637507 := bstep (se 1 (by rfl) ⟨478130, by rfl⟩ : syracuseStep 637507 = 956261) B956261
theorem B3226189 : Blo 527800 3226189 := bstep (se 3 (by rfl) ⟨604910, by rfl⟩ : syracuseStep 3226189 = 1209821) B1209821
theorem B4536931 : Blo 527800 4536931 := bstep (se 1 (by rfl) ⟨3402698, by rfl⟩ : syracuseStep 4536931 = 6805397) B6805397
theorem B1784429 : Blo 527800 1784429 := bstep (se 3 (by rfl) ⟨334580, by rfl⟩ : syracuseStep 1784429 = 669161) B669161
theorem B1915505 : Blo 527800 1915505 := bstep (se 2 (by rfl) ⟨718314, by rfl⟩ : syracuseStep 1915505 = 1436629) B1436629
theorem B1194641 : Blo 527800 1194641 := bstep (se 2 (by rfl) ⟨447990, by rfl⟩ : syracuseStep 1194641 = 895981) B895981
theorem B1784483 : Blo 527800 1784483 := bstep (se 1 (by rfl) ⟨1338362, by rfl⟩ : syracuseStep 1784483 = 2676725) B2676725
theorem B1194659 : Blo 527800 1194659 := bstep (se 1 (by rfl) ⟨895994, by rfl⟩ : syracuseStep 1194659 = 1791989) B1791989
theorem B2013923 : Blo 527800 2013923 := bstep (se 1 (by rfl) ⟨1510442, by rfl⟩ : syracuseStep 2013923 = 3020885) B3020885
theorem B637699 : Blo 527800 637699 := bstep (se 1 (by rfl) ⟨478274, by rfl⟩ : syracuseStep 637699 = 956549) B956549
theorem B1784753 : Blo 527800 1784753 := bstep (se 2 (by rfl) ⟨669282, by rfl⟩ : syracuseStep 1784753 = 1338565) B1338565
theorem B1194929 : Blo 527800 1194929 := bstep (se 2 (by rfl) ⟨448098, by rfl⟩ : syracuseStep 1194929 = 896197) B896197
theorem B1194947 : Blo 527800 1194947 := bstep (se 1 (by rfl) ⟨896210, by rfl⟩ : syracuseStep 1194947 = 1792421) B1792421
theorem B670675 : Blo 527800 670675 := bstep (se 1 (by rfl) ⟨503006, by rfl⟩ : syracuseStep 670675 = 1006013) B1006013
theorem B670771 : Blo 527800 670771 := bstep (se 1 (by rfl) ⟨503078, by rfl⟩ : syracuseStep 670771 = 1006157) B1006157
theorem B638083 : Blo 527800 638083 := bstep (se 1 (by rfl) ⟨478562, by rfl⟩ : syracuseStep 638083 = 957125) B957125
theorem B1195217 : Blo 527800 1195217 := bstep (se 2 (by rfl) ⟨448206, by rfl⟩ : syracuseStep 1195217 = 896413) B896413
theorem B1195235 : Blo 527800 1195235 := bstep (se 1 (by rfl) ⟨896426, by rfl⟩ : syracuseStep 1195235 = 1792853) B1792853
theorem B2014577 : Blo 527800 2014577 := bstep (se 2 (by rfl) ⟨755466, by rfl⟩ : syracuseStep 2014577 = 1510933) B1510933
theorem B1785293 : Blo 527800 1785293 := bstep (se 3 (by rfl) ⟨334742, by rfl⟩ : syracuseStep 1785293 = 669485) B669485
theorem B1195505 : Blo 527800 1195505 := bstep (se 2 (by rfl) ⟨448314, by rfl⟩ : syracuseStep 1195505 = 896629) B896629
theorem B1785347 : Blo 527800 1785347 := bstep (se 1 (by rfl) ⟨1339010, by rfl⟩ : syracuseStep 1785347 = 2678021) B2678021
theorem B1195523 : Blo 527800 1195523 := bstep (se 1 (by rfl) ⟨896642, by rfl⟩ : syracuseStep 1195523 = 1793285) B1793285
theorem B671267 : Blo 527800 671267 := bstep (se 1 (by rfl) ⟨503450, by rfl⟩ : syracuseStep 671267 = 1006901) B1006901
theorem B1719917 : Blo 527800 1719917 := bstep (se 3 (by rfl) ⟨322484, by rfl⟩ : syracuseStep 1719917 = 644969) B644969
theorem B2899597 : Blo 527800 2899597 := bstep (se 3 (by rfl) ⟨543674, by rfl⟩ : syracuseStep 2899597 = 1087349) B1087349
theorem B3391217 : Blo 527800 3391217 := bstep (se 2 (by rfl) ⟨1271706, by rfl⟩ : syracuseStep 3391217 = 2543413) B2543413
theorem B1785617 : Blo 527800 1785617 := bstep (se 2 (by rfl) ⟨669606, by rfl⟩ : syracuseStep 1785617 = 1339213) B1339213
theorem B1195793 : Blo 527800 1195793 := bstep (se 2 (by rfl) ⟨448422, by rfl⟩ : syracuseStep 1195793 = 896845) B896845
theorem B1195811 : Blo 527800 1195811 := bstep (se 1 (by rfl) ⟨896858, by rfl⟩ : syracuseStep 1195811 = 1793717) B1793717
theorem B638771 : Blo 527800 638771 := bstep (se 1 (by rfl) ⟨479078, by rfl⟩ : syracuseStep 638771 = 958157) B958157
theorem B2572273 : Blo 527800 2572273 := bstep (se 2 (by rfl) ⟨964602, by rfl⟩ : syracuseStep 2572273 = 1929205) B1929205
theorem B1196081 : Blo 527800 1196081 := bstep (se 2 (by rfl) ⟨448530, by rfl⟩ : syracuseStep 1196081 = 897061) B897061
theorem B1196099 : Blo 527800 1196099 := bstep (se 1 (by rfl) ⟨897074, by rfl⟩ : syracuseStep 1196099 = 1794149) B1794149
theorem B671971 : Blo 527800 671971 := bstep (se 1 (by rfl) ⟨503978, by rfl⟩ : syracuseStep 671971 = 1007957) B1007957
theorem B5161229 : Blo 527800 5161229 := bstep (se 3 (by rfl) ⟨967730, by rfl⟩ : syracuseStep 5161229 = 1935461) B1935461
theorem B1786157 : Blo 527800 1786157 := bstep (se 3 (by rfl) ⟨334904, by rfl⟩ : syracuseStep 1786157 = 669809) B669809
theorem B672067 : Blo 527800 672067 := bstep (se 1 (by rfl) ⟨504050, by rfl⟩ : syracuseStep 672067 = 1008101) B1008101
theorem B1196369 : Blo 527800 1196369 := bstep (se 2 (by rfl) ⟨448638, by rfl⟩ : syracuseStep 1196369 = 897277) B897277
theorem B1786211 : Blo 527800 1786211 := bstep (se 1 (by rfl) ⟨1339658, by rfl⟩ : syracuseStep 1786211 = 2679317) B2679317
theorem B1196387 : Blo 527800 1196387 := bstep (se 1 (by rfl) ⟨897290, by rfl⟩ : syracuseStep 1196387 = 1794581) B1794581
theorem B1524077 : Blo 527800 1524077 := bstep (se 3 (by rfl) ⟨285764, by rfl⟩ : syracuseStep 1524077 = 571529) B571529
theorem B1131089 : Blo 527800 1131089 := bstep (se 2 (by rfl) ⟨424158, by rfl⟩ : syracuseStep 1131089 = 848317) B848317
theorem B1786481 : Blo 527800 1786481 := bstep (se 2 (by rfl) ⟨669930, by rfl⟩ : syracuseStep 1786481 = 1339861) B1339861
theorem B2016035 : Blo 527800 2016035 := bstep (se 1 (by rfl) ⟨1512026, by rfl⟩ : syracuseStep 2016035 = 3024053) B3024053
theorem B803633 : Blo 527800 803633 := bstep (se 2 (by rfl) ⟨301362, by rfl⟩ : syracuseStep 803633 = 602725) B602725
theorem B2016049 : Blo 527800 2016049 := bstep (se 2 (by rfl) ⟨756018, by rfl⟩ : syracuseStep 2016049 = 1512037) B1512037
theorem B672563 : Blo 527800 672563 := bstep (se 1 (by rfl) ⟨504422, by rfl⟩ : syracuseStep 672563 = 1008845) B1008845
theorem B1787021 : Blo 527800 1787021 := bstep (se 3 (by rfl) ⟨335066, by rfl⟩ : syracuseStep 1787021 = 670133) B670133
theorem B1787075 : Blo 527800 1787075 := bstep (se 1 (by rfl) ⟨1340306, by rfl⟩ : syracuseStep 1787075 = 2680613) B2680613
theorem B46613717 : Blo 527800 46613717 := bstep (se 7 (by rfl) ⟨546254, by rfl⟩ : syracuseStep 46613717 = 1092509) B1092509
theorem B4015331 : Blo 527800 4015331 := bstep (se 1 (by rfl) ⟨3011498, by rfl⟩ : syracuseStep 4015331 = 6022997) B6022997
theorem B1426691 : Blo 527800 1426691 := bstep (se 1 (by rfl) ⟨1070018, by rfl⟩ : syracuseStep 1426691 = 2140037) B2140037
theorem B1787345 : Blo 527800 1787345 := bstep (se 2 (by rfl) ⟨670254, by rfl⟩ : syracuseStep 1787345 = 1340509) B1340509
theorem B1787885 : Blo 527800 1787885 := bstep (se 3 (by rfl) ⟨335228, by rfl⟩ : syracuseStep 1787885 = 670457) B670457
theorem B2672675 : Blo 527800 2672675 := bstep (se 1 (by rfl) ⟨2004506, by rfl⟩ : syracuseStep 2672675 = 4009013) B4009013
theorem B1787939 : Blo 527800 1787939 := bstep (se 1 (by rfl) ⟨1340954, by rfl⟩ : syracuseStep 1787939 = 2681909) B2681909
theorem B3393677 : Blo 527800 3393677 := bstep (se 3 (by rfl) ⟨636314, by rfl⟩ : syracuseStep 3393677 = 1272629) B1272629
theorem B1427633 : Blo 527800 1427633 := bstep (se 2 (by rfl) ⟨535362, by rfl⟩ : syracuseStep 1427633 = 1070725) B1070725
theorem B2017507 : Blo 527800 2017507 := bstep (se 1 (by rfl) ⟨1513130, by rfl⟩ : syracuseStep 2017507 = 3026261) B3026261
theorem B1788209 : Blo 527800 1788209 := bstep (se 2 (by rfl) ⟨670578, by rfl⟩ : syracuseStep 1788209 = 1341157) B1341157
theorem B1362691 : Blo 527800 1362691 := bstep (se 1 (by rfl) ⟨1022018, by rfl⟩ : syracuseStep 1362691 = 2044037) B2044037
theorem B1002307 : Blo 527800 1002307 := bstep (se 1 (by rfl) ⟨751730, by rfl⟩ : syracuseStep 1002307 = 1503461) B1503461
theorem B2673485 : Blo 527800 2673485 := bstep (se 3 (by rfl) ⟨501278, by rfl⟩ : syracuseStep 2673485 = 1002557) B1002557
theorem B1788749 : Blo 527800 1788749 := bstep (se 3 (by rfl) ⟨335390, by rfl⟩ : syracuseStep 1788749 = 670781) B670781
theorem B1788803 : Blo 527800 1788803 := bstep (se 1 (by rfl) ⟨1341602, by rfl⟩ : syracuseStep 1788803 = 2683205) B2683205
theorem B1789073 : Blo 527800 1789073 := bstep (se 2 (by rfl) ⟨670902, by rfl⟩ : syracuseStep 1789073 = 1341805) B1341805
theorem B1002755 : Blo 527800 1002755 := bstep (se 1 (by rfl) ⟨752066, by rfl⟩ : syracuseStep 1002755 = 1504133) B1504133
theorem B3263921 : Blo 527800 3263921 := bstep (se 2 (by rfl) ⟨1223970, by rfl⟩ : syracuseStep 3263921 = 2447941) B2447941
theorem B1428931 : Blo 527800 1428931 := bstep (se 1 (by rfl) ⟨1071698, by rfl⟩ : syracuseStep 1428931 = 2143397) B2143397
theorem B1428941 : Blo 527800 1428941 := bstep (se 3 (by rfl) ⟨267926, by rfl⟩ : syracuseStep 1428941 = 535853) B535853
theorem B1003043 : Blo 527800 1003043 := bstep (se 1 (by rfl) ⟨752282, by rfl⟩ : syracuseStep 1003043 = 1504565) B1504565
theorem B1429073 : Blo 527800 1429073 := bstep (se 2 (by rfl) ⟨535902, by rfl⟩ : syracuseStep 1429073 = 1071805) B1071805
theorem B1789613 : Blo 527800 1789613 := bstep (se 3 (by rfl) ⟨335552, by rfl⟩ : syracuseStep 1789613 = 671105) B671105
theorem B1789667 : Blo 527800 1789667 := bstep (se 1 (by rfl) ⟨1342250, by rfl⟩ : syracuseStep 1789667 = 2684501) B2684501
theorem B1134499 : Blo 527800 1134499 := bstep (se 1 (by rfl) ⟨850874, by rfl⟩ : syracuseStep 1134499 = 1701749) B1701749
theorem B1789937 : Blo 527800 1789937 := bstep (se 2 (by rfl) ⟨671226, by rfl⟩ : syracuseStep 1789937 = 1342453) B1342453
theorem B1364035 : Blo 527800 1364035 := bstep (se 1 (by rfl) ⟨1023026, by rfl⟩ : syracuseStep 1364035 = 2046053) B2046053
theorem B6017165 : Blo 527800 6017165 := bstep (se 3 (by rfl) ⟨1128218, by rfl⟩ : syracuseStep 6017165 = 2256437) B2256437
theorem B1528141 : Blo 527800 1528141 := bstep (se 3 (by rfl) ⟨286526, by rfl⟩ : syracuseStep 1528141 = 573053) B573053
theorem B1429937 : Blo 527800 1429937 := bstep (se 2 (by rfl) ⟨536226, by rfl⟩ : syracuseStep 1429937 = 1072453) B1072453
theorem B1003985 : Blo 527800 1003985 := bstep (se 2 (by rfl) ⟨376494, by rfl⟩ : syracuseStep 1003985 = 752989) B752989
theorem B1790477 : Blo 527800 1790477 := bstep (se 3 (by rfl) ⟨335714, by rfl⟩ : syracuseStep 1790477 = 671429) B671429
theorem B1430065 : Blo 527800 1430065 := bstep (se 2 (by rfl) ⟨536274, by rfl⟩ : syracuseStep 1430065 = 1072549) B1072549
theorem B1790531 : Blo 527800 1790531 := bstep (se 1 (by rfl) ⟨1342898, by rfl⟩ : syracuseStep 1790531 = 2685797) B2685797
theorem B1790801 : Blo 527800 1790801 := bstep (se 2 (by rfl) ⟨671550, by rfl⟩ : syracuseStep 1790801 = 1343101) B1343101
theorem B4510961 : Blo 527800 4510961 := bstep (se 2 (by rfl) ⟨1691610, by rfl⟩ : syracuseStep 4510961 = 3383221) B3383221
theorem B611651 : Blo 527800 611651 := bstep (se 1 (by rfl) ⟨458738, by rfl⟩ : syracuseStep 611651 = 917477) B917477
theorem B1004881 : Blo 527800 1004881 := bstep (se 2 (by rfl) ⟨376830, by rfl⟩ : syracuseStep 1004881 = 753661) B753661
theorem B1791341 : Blo 527800 1791341 := bstep (se 3 (by rfl) ⟨335876, by rfl⟩ : syracuseStep 1791341 = 671753) B671753
theorem B1791395 : Blo 527800 1791395 := bstep (se 1 (by rfl) ⟨1343546, by rfl⟩ : syracuseStep 1791395 = 2687093) B2687093
theorem B1005041 : Blo 527800 1005041 := bstep (se 2 (by rfl) ⟨376890, by rfl⟩ : syracuseStep 1005041 = 753781) B753781
theorem B2676401 : Blo 527800 2676401 := bstep (se 2 (by rfl) ⟨1003650, by rfl⟩ : syracuseStep 2676401 = 2007301) B2007301
theorem B1791665 : Blo 527800 1791665 := bstep (se 2 (by rfl) ⟨671874, by rfl⟩ : syracuseStep 1791665 = 1343749) B1343749
theorem B1693457 : Blo 527800 1693457 := bstep (se 2 (by rfl) ⟨635046, by rfl⟩ : syracuseStep 1693457 = 1270093) B1270093
theorem B677651 : Blo 527800 677651 := bstep (se 1 (by rfl) ⟨508238, by rfl⟩ : syracuseStep 677651 = 1016477) B1016477
theorem B907057 : Blo 527800 907057 := bstep (se 2 (by rfl) ⟨340146, by rfl⟩ : syracuseStep 907057 = 680293) B680293
theorem B1005443 : Blo 527800 1005443 := bstep (se 1 (by rfl) ⟨754082, by rfl⟩ : syracuseStep 1005443 = 1508165) B1508165
theorem B1693649 : Blo 527800 1693649 := bstep (se 2 (by rfl) ⟨635118, by rfl⟩ : syracuseStep 1693649 = 1270237) B1270237
theorem B1792205 : Blo 527800 1792205 := bstep (se 3 (by rfl) ⟨336038, by rfl⟩ : syracuseStep 1792205 = 672077) B672077
theorem B1530083 : Blo 527800 1530083 := bstep (se 1 (by rfl) ⟨1147562, by rfl⟩ : syracuseStep 1530083 = 2295125) B2295125
theorem B1792259 : Blo 527800 1792259 := bstep (se 1 (by rfl) ⟨1344194, by rfl⟩ : syracuseStep 1792259 = 2688389) B2688389
theorem B907537 : Blo 527800 907537 := bstep (se 2 (by rfl) ⟨340326, by rfl⟩ : syracuseStep 907537 = 680653) B680653
theorem B4020677 : Blo 527800 4020677 := bstep (se 4 (by rfl) ⟨376938, by rfl⟩ : syracuseStep 4020677 = 753877) B753877
theorem B1792529 : Blo 527800 1792529 := bstep (se 2 (by rfl) ⟨672198, by rfl⟩ : syracuseStep 1792529 = 1344397) B1344397
theorem B2873969 : Blo 527800 2873969 := bstep (se 2 (by rfl) ⟨1077738, by rfl⟩ : syracuseStep 2873969 = 2155477) B2155477
theorem B1268401 : Blo 527800 1268401 := bstep (se 2 (by rfl) ⟨475650, by rfl⟩ : syracuseStep 1268401 = 951301) B951301
theorem B1006339 : Blo 527800 1006339 := bstep (se 1 (by rfl) ⟨754754, by rfl⟩ : syracuseStep 1006339 = 1509509) B1509509
theorem B908083 : Blo 527800 908083 := bstep (se 1 (by rfl) ⟨681062, by rfl⟩ : syracuseStep 908083 = 1362125) B1362125
theorem B1006499 : Blo 527800 1006499 := bstep (se 1 (by rfl) ⟨754874, by rfl⟩ : syracuseStep 1006499 = 1509749) B1509749
theorem B678883 : Blo 527800 678883 := bstep (se 1 (by rfl) ⟨509162, by rfl⟩ : syracuseStep 678883 = 1018325) B1018325
theorem B6020081 : Blo 527800 6020081 := bstep (se 2 (by rfl) ⟨2257530, by rfl⟩ : syracuseStep 6020081 = 4515061) B4515061
theorem B1793069 : Blo 527800 1793069 := bstep (se 3 (by rfl) ⟨336200, by rfl⟩ : syracuseStep 1793069 = 672401) B672401
theorem B1268785 : Blo 527800 1268785 := bstep (se 2 (by rfl) ⟨475794, by rfl⟩ : syracuseStep 1268785 = 951589) B951589
theorem B2677859 : Blo 527800 2677859 := bstep (se 1 (by rfl) ⟨2008394, by rfl⟩ : syracuseStep 2677859 = 4016789) B4016789
theorem B1793123 : Blo 527800 1793123 := bstep (se 1 (by rfl) ⟨1344842, by rfl⟩ : syracuseStep 1793123 = 2689685) B2689685
theorem B1072291 : Blo 527800 1072291 := bstep (se 1 (by rfl) ⟨804218, by rfl⟩ : syracuseStep 1072291 = 1608437) B1608437
theorem B6774029 : Blo 527800 6774029 := bstep (se 3 (by rfl) ⟨1270130, by rfl⟩ : syracuseStep 6774029 = 2540261) B2540261
theorem B1793393 : Blo 527800 1793393 := bstep (se 2 (by rfl) ⟨672522, by rfl⟩ : syracuseStep 1793393 = 1345045) B1345045
theorem B4513421 : Blo 527800 4513421 := bstep (se 3 (by rfl) ⟨846266, by rfl⟩ : syracuseStep 4513421 = 1692533) B1692533
theorem B2416483 : Blo 527800 2416483 := bstep (se 1 (by rfl) ⟨1812362, by rfl⟩ : syracuseStep 2416483 = 3624725) B3624725
theorem B2678669 : Blo 527800 2678669 := bstep (se 3 (by rfl) ⟨502250, by rfl⟩ : syracuseStep 2678669 = 1004501) B1004501
theorem B1793933 : Blo 527800 1793933 := bstep (se 3 (by rfl) ⟨336362, by rfl⟩ : syracuseStep 1793933 = 672725) B672725
theorem B1793987 : Blo 527800 1793987 := bstep (se 1 (by rfl) ⟨1345490, by rfl⟩ : syracuseStep 1793987 = 2690981) B2690981
theorem B1007569 : Blo 527800 1007569 := bstep (se 2 (by rfl) ⟨377838, by rfl⟩ : syracuseStep 1007569 = 755677) B755677
theorem B1695917 : Blo 527800 1695917 := bstep (se 3 (by rfl) ⟨317984, by rfl⟩ : syracuseStep 1695917 = 635969) B635969
theorem B2154701 : Blo 527800 2154701 := bstep (se 3 (by rfl) ⟨404006, by rfl⟩ : syracuseStep 2154701 = 808013) B808013
theorem B1794257 : Blo 527800 1794257 := bstep (se 2 (by rfl) ⟨672846, by rfl⟩ : syracuseStep 1794257 = 1345693) B1345693
theorem B1204465 : Blo 527800 1204465 := bstep (se 2 (by rfl) ⟨451674, by rfl⟩ : syracuseStep 1204465 = 903349) B903349
theorem B2908493 : Blo 527800 2908493 := bstep (se 3 (by rfl) ⟨545342, by rfl⟩ : syracuseStep 2908493 = 1090685) B1090685
theorem B3006989 : Blo 527800 3006989 := bstep (se 3 (by rfl) ⟨563810, by rfl⟩ : syracuseStep 3006989 = 1127621) B1127621
theorem B2548259 : Blo 527800 2548259 := bstep (se 1 (by rfl) ⟨1911194, by rfl⟩ : syracuseStep 2548259 = 3822389) B3822389
theorem B1794797 : Blo 527800 1794797 := bstep (se 3 (by rfl) ⟨336524, by rfl⟩ : syracuseStep 1794797 = 673049) B673049
theorem B2712305 : Blo 527800 2712305 := bstep (se 2 (by rfl) ⟨1017114, by rfl⟩ : syracuseStep 2712305 = 2034229) B2034229
theorem B2548529 : Blo 527800 2548529 := bstep (se 2 (by rfl) ⟨955698, by rfl⟩ : syracuseStep 2548529 = 1911397) B1911397
theorem B680755 : Blo 527800 680755 := bstep (se 1 (by rfl) ⟨510566, by rfl⟩ : syracuseStep 680755 = 1021133) B1021133
theorem B6808373 : Blo 527800 6808373 := bstep (se 5 (by rfl) ⟨319142, by rfl⟩ : syracuseStep 6808373 = 638285) B638285
theorem B1434467 : Blo 527800 1434467 := bstep (se 1 (by rfl) ⟨1075850, by rfl⟩ : syracuseStep 1434467 = 2151701) B2151701
theorem B680899 : Blo 527800 680899 := bstep (se 1 (by rfl) ⟨510674, by rfl⟩ : syracuseStep 680899 = 1021349) B1021349
theorem B1008625 : Blo 527800 1008625 := bstep (se 2 (by rfl) ⟨378234, by rfl⟩ : syracuseStep 1008625 = 756469) B756469
theorem B3826885 : Blo 527800 3826885 := bstep (se 4 (by rfl) ⟨358770, by rfl⟩ : syracuseStep 3826885 = 717541) B717541
theorem B1009027 : Blo 527800 1009027 := bstep (se 1 (by rfl) ⟨756770, by rfl⟩ : syracuseStep 1009027 = 1513541) B1513541
theorem B1009073 : Blo 527800 1009073 := bstep (se 2 (by rfl) ⟨378402, by rfl⟩ : syracuseStep 1009073 = 756805) B756805
theorem B714163 : Blo 527800 714163 := bstep (se 1 (by rfl) ⟨535622, by rfl⟩ : syracuseStep 714163 = 1071245) B1071245
theorem B1336945 : Blo 527800 1336945 := bstep (se 2 (by rfl) ⟨501354, by rfl⟩ : syracuseStep 1336945 = 1002709) B1002709
theorem B845473 : Blo 527800 845473 := bstep (se 2 (by rfl) ⟨317052, by rfl⟩ : syracuseStep 845473 = 634105) B634105
theorem B5531333 : Blo 527800 5531333 := bstep (se 4 (by rfl) ⟨518562, by rfl⟩ : syracuseStep 5531333 = 1037125) B1037125
theorem B1009361 : Blo 527800 1009361 := bstep (se 2 (by rfl) ⟨378510, by rfl⟩ : syracuseStep 1009361 = 757021) B757021
theorem B1697507 : Blo 527800 1697507 := bstep (se 1 (by rfl) ⟨1273130, by rfl⟩ : syracuseStep 1697507 = 2546261) B2546261
theorem B1337219 : Blo 527800 1337219 := bstep (se 1 (by rfl) ⟨1002914, by rfl⟩ : syracuseStep 1337219 = 2005829) B2005829
theorem B845729 : Blo 527800 845729 := bstep (se 2 (by rfl) ⟨317148, by rfl⟩ : syracuseStep 845729 = 634297) B634297
theorem B3401777 : Blo 527800 3401777 := bstep (se 2 (by rfl) ⟨1275666, by rfl⟩ : syracuseStep 3401777 = 2551333) B2551333
theorem B1337411 : Blo 527800 1337411 := bstep (se 1 (by rfl) ⟨1003058, by rfl⟩ : syracuseStep 1337411 = 2006117) B2006117
theorem B845921 : Blo 527800 845921 := bstep (se 2 (by rfl) ⟨317220, by rfl⟩ : syracuseStep 845921 = 634441) B634441
theorem B2418929 : Blo 527800 2418929 := bstep (se 2 (by rfl) ⟨907098, by rfl⟩ : syracuseStep 2418929 = 1814197) B1814197
theorem B1272131 : Blo 527800 1272131 := bstep (se 1 (by rfl) ⟨954098, by rfl⟩ : syracuseStep 1272131 = 1908197) B1908197
theorem B5073293 : Blo 527800 5073293 := bstep (se 3 (by rfl) ⟨951242, by rfl⟩ : syracuseStep 5073293 = 1902485) B1902485
theorem B2550179 : Blo 527800 2550179 := bstep (se 1 (by rfl) ⟨1912634, by rfl⟩ : syracuseStep 2550179 = 3825269) B3825269
theorem B1468867 : Blo 527800 1468867 := bstep (se 1 (by rfl) ⟨1101650, by rfl⟩ : syracuseStep 1468867 = 2203301) B2203301
theorem B1272419 : Blo 527800 1272419 := bstep (se 1 (by rfl) ⟨954314, by rfl⟩ : syracuseStep 1272419 = 1908629) B1908629
theorem B1698403 : Blo 527800 1698403 := bstep (se 1 (by rfl) ⟨1273802, by rfl⟩ : syracuseStep 1698403 = 2547605) B2547605
theorem B1075825 : Blo 527800 1075825 := bstep (se 2 (by rfl) ⟨403434, by rfl⟩ : syracuseStep 1075825 = 806869) B806869
theorem B3009221 : Blo 527800 3009221 := bstep (se 4 (by rfl) ⟨282114, by rfl⟩ : syracuseStep 3009221 = 564229) B564229
theorem B2681585 : Blo 527800 2681585 := bstep (se 2 (by rfl) ⟨1005594, by rfl⟩ : syracuseStep 2681585 = 2011189) B2011189
theorem B1207075 : Blo 527800 1207075 := bstep (se 1 (by rfl) ⟨905306, by rfl⟩ : syracuseStep 1207075 = 1810613) B1810613
theorem B715649 : Blo 527800 715649 := bstep (se 2 (by rfl) ⟨268368, by rfl⟩ : syracuseStep 715649 = 536737) B536737
theorem B715681 : Blo 527800 715681 := bstep (se 2 (by rfl) ⟨268380, by rfl⟩ : syracuseStep 715681 = 536761) B536761
theorem B17198021 : Blo 527800 17198021 := bstep (se 4 (by rfl) ⟨1612314, by rfl⟩ : syracuseStep 17198021 = 3224629) B3224629
theorem B1338353 : Blo 527800 1338353 := bstep (se 2 (by rfl) ⟨501882, by rfl⟩ : syracuseStep 1338353 = 1003765) B1003765
theorem B1338403 : Blo 527800 1338403 := bstep (se 1 (by rfl) ⟨1003802, by rfl⟩ : syracuseStep 1338403 = 2007605) B2007605
theorem B945265 : Blo 527800 945265 := bstep (se 2 (by rfl) ⟨354474, by rfl⟩ : syracuseStep 945265 = 708949) B708949
theorem B1338545 : Blo 527800 1338545 := bstep (se 2 (by rfl) ⟨501954, by rfl⟩ : syracuseStep 1338545 = 1003909) B1003909
theorem B3009905 : Blo 527800 3009905 := bstep (se 2 (by rfl) ⟨1128714, by rfl⟩ : syracuseStep 3009905 = 2257429) B2257429
theorem B847235 : Blo 527800 847235 := bstep (se 1 (by rfl) ⟨635426, by rfl⟩ : syracuseStep 847235 = 1270853) B1270853
theorem B847459 : Blo 527800 847459 := bstep (se 1 (by rfl) ⟨635594, by rfl⟩ : syracuseStep 847459 = 1271189) B1271189
theorem B847523 : Blo 527800 847523 := bstep (se 1 (by rfl) ⟨635642, by rfl⟩ : syracuseStep 847523 = 1271285) B1271285
theorem B1699505 : Blo 527800 1699505 := bstep (se 2 (by rfl) ⟨637314, by rfl⟩ : syracuseStep 1699505 = 1274629) B1274629
theorem B4419269 : Blo 527800 4419269 := bstep (se 4 (by rfl) ⟨414306, by rfl⟩ : syracuseStep 4419269 = 828613) B828613
theorem B847651 : Blo 527800 847651 := bstep (se 1 (by rfl) ⟨635738, by rfl⟩ : syracuseStep 847651 = 1271477) B1271477
theorem B1699633 : Blo 527800 1699633 := bstep (se 2 (by rfl) ⟨637362, by rfl⟩ : syracuseStep 1699633 = 1274725) B1274725
theorem B1503107 : Blo 527800 1503107 := bstep (se 1 (by rfl) ⟨1127330, by rfl⟩ : syracuseStep 1503107 = 2254661) B2254661
theorem B1273745 : Blo 527800 1273745 := bstep (se 2 (by rfl) ⟨477654, by rfl⟩ : syracuseStep 1273745 = 955309) B955309
theorem B1077155 : Blo 527800 1077155 := bstep (se 1 (by rfl) ⟨807866, by rfl⟩ : syracuseStep 1077155 = 1615733) B1615733
theorem B1208369 : Blo 527800 1208369 := bstep (se 2 (by rfl) ⟨453138, by rfl⟩ : syracuseStep 1208369 = 906277) B906277
theorem B4026509 : Blo 527800 4026509 := bstep (se 3 (by rfl) ⟨754970, by rfl⟩ : syracuseStep 4026509 = 1509941) B1509941
theorem B2551949 : Blo 527800 2551949 := bstep (se 3 (by rfl) ⟨478490, by rfl⟩ : syracuseStep 2551949 = 956981) B956981
theorem B1339537 : Blo 527800 1339537 := bstep (se 2 (by rfl) ⟨502326, by rfl⟩ : syracuseStep 1339537 = 1004653) B1004653
theorem B1929379 : Blo 527800 1929379 := bstep (se 1 (by rfl) ⟨1447034, by rfl⟩ : syracuseStep 1929379 = 2894069) B2894069
theorem B2683043 : Blo 527800 2683043 := bstep (se 1 (by rfl) ⟨2012282, by rfl⟩ : syracuseStep 2683043 = 4024565) B4024565
theorem B13070645 : Blo 527800 13070645 := bstep (se 5 (by rfl) ⟨612686, by rfl⟩ : syracuseStep 13070645 = 1225373) B1225373
theorem B1339811 : Blo 527800 1339811 := bstep (se 1 (by rfl) ⟨1004858, by rfl⟩ : syracuseStep 1339811 = 2009717) B2009717
theorem B1274321 : Blo 527800 1274321 := bstep (se 2 (by rfl) ⟨477870, by rfl⟩ : syracuseStep 1274321 = 955741) B955741
theorem B2257379 : Blo 527800 2257379 := bstep (se 1 (by rfl) ⟨1693034, by rfl⟩ : syracuseStep 2257379 = 3386069) B3386069
theorem B848369 : Blo 527800 848369 := bstep (se 2 (by rfl) ⟨318138, by rfl⟩ : syracuseStep 848369 = 636277) B636277
theorem B1340003 : Blo 527800 1340003 := bstep (se 1 (by rfl) ⟨1005002, by rfl⟩ : syracuseStep 1340003 = 2010005) B2010005
theorem B1274467 : Blo 527800 1274467 := bstep (se 1 (by rfl) ⟨955850, by rfl⟩ : syracuseStep 1274467 = 1911701) B1911701
theorem B1143409 : Blo 527800 1143409 := bstep (se 2 (by rfl) ⟨428778, by rfl⟩ : syracuseStep 1143409 = 857557) B857557
theorem B848497 : Blo 527800 848497 := bstep (se 2 (by rfl) ⟨318186, by rfl⟩ : syracuseStep 848497 = 636373) B636373
theorem B1503917 : Blo 527800 1503917 := bstep (se 3 (by rfl) ⟨281984, by rfl⟩ : syracuseStep 1503917 = 563969) B563969
theorem B1700621 : Blo 527800 1700621 := bstep (se 3 (by rfl) ⟨318866, by rfl⟩ : syracuseStep 1700621 = 637733) B637733
theorem B3011363 : Blo 527800 3011363 := bstep (se 1 (by rfl) ⟨2258522, by rfl⟩ : syracuseStep 3011363 = 4517045) B4517045
theorem B1504109 : Blo 527800 1504109 := bstep (se 3 (by rfl) ⟨282020, by rfl⟩ : syracuseStep 1504109 = 564041) B564041
theorem B2683853 : Blo 527800 2683853 := bstep (se 3 (by rfl) ⟨503222, by rfl⟩ : syracuseStep 2683853 = 1006445) B1006445
theorem B3404749 : Blo 527800 3404749 := bstep (se 3 (by rfl) ⟨638390, by rfl⟩ : syracuseStep 3404749 = 1276781) B1276781
theorem B848881 : Blo 527800 848881 := bstep (se 2 (by rfl) ⟨318330, by rfl⟩ : syracuseStep 848881 = 636661) B636661
theorem B849137 : Blo 527800 849137 := bstep (se 2 (by rfl) ⟨318426, by rfl⟩ : syracuseStep 849137 = 636853) B636853
theorem B6452621 : Blo 527800 6452621 := bstep (se 3 (by rfl) ⟨1209866, by rfl⟩ : syracuseStep 6452621 = 2419733) B2419733
theorem B1570211 : Blo 527800 1570211 := bstep (se 1 (by rfl) ⟨1177658, by rfl⟩ : syracuseStep 1570211 = 2355317) B2355317
theorem B1471981 : Blo 527800 1471981 := bstep (se 3 (by rfl) ⟨275996, by rfl⟩ : syracuseStep 1471981 = 551993) B551993
theorem B1340945 : Blo 527800 1340945 := bstep (se 2 (by rfl) ⟨502854, by rfl⟩ : syracuseStep 1340945 = 1005709) B1005709
theorem B1340995 : Blo 527800 1340995 := bstep (se 1 (by rfl) ⟨1005746, by rfl⟩ : syracuseStep 1340995 = 2011493) B2011493
theorem B718417 : Blo 527800 718417 := bstep (se 2 (by rfl) ⟨269406, by rfl⟩ : syracuseStep 718417 = 538813) B538813
theorem B1341137 : Blo 527800 1341137 := bstep (se 2 (by rfl) ⟨502926, by rfl⟩ : syracuseStep 1341137 = 1005853) B1005853
theorem B1505101 : Blo 527800 1505101 := bstep (se 3 (by rfl) ⟨282206, by rfl⟩ : syracuseStep 1505101 = 564413) B564413
theorem B1701965 : Blo 527800 1701965 := bstep (se 3 (by rfl) ⟨319118, by rfl⟩ : syracuseStep 1701965 = 638237) B638237
theorem B2259377 : Blo 527800 2259377 := bstep (se 2 (by rfl) ⟨847266, by rfl⟩ : syracuseStep 2259377 = 1694533) B1694533
theorem B2718157 : Blo 527800 2718157 := bstep (se 3 (by rfl) ⟨509654, by rfl⟩ : syracuseStep 2718157 = 1019309) B1019309
theorem B850547 : Blo 527800 850547 := bstep (se 1 (by rfl) ⟨637910, by rfl⟩ : syracuseStep 850547 = 1275821) B1275821
theorem B916145 : Blo 527800 916145 := bstep (se 2 (by rfl) ⟨343554, by rfl⟩ : syracuseStep 916145 = 687109) B687109
theorem B1342129 : Blo 527800 1342129 := bstep (se 2 (by rfl) ⟨503298, by rfl⟩ : syracuseStep 1342129 = 1006597) B1006597
theorem B752323 : Blo 527800 752323 := bstep (se 1 (by rfl) ⟨564242, by rfl⟩ : syracuseStep 752323 = 1128485) B1128485
theorem B752419 : Blo 527800 752419 := bstep (se 1 (by rfl) ⟨564314, by rfl⟩ : syracuseStep 752419 = 1128629) B1128629
theorem B1342403 : Blo 527800 1342403 := bstep (se 1 (by rfl) ⟨1006802, by rfl⟩ : syracuseStep 1342403 = 2013605) B2013605
theorem B4029425 : Blo 527800 4029425 := bstep (se 2 (by rfl) ⟨1511034, by rfl⟩ : syracuseStep 4029425 = 3022069) B3022069
theorem B6716515 : Blo 527800 6716515 := bstep (se 1 (by rfl) ⟨5037386, by rfl⟩ : syracuseStep 6716515 = 10074773) B10074773
theorem B1342595 : Blo 527800 1342595 := bstep (se 1 (by rfl) ⟨1006946, by rfl⟩ : syracuseStep 1342595 = 2013893) B2013893
theorem B3406981 : Blo 527800 3406981 := bstep (se 4 (by rfl) ⟨319404, by rfl⟩ : syracuseStep 3406981 = 638809) B638809
theorem B752915 : Blo 527800 752915 := bstep (se 1 (by rfl) ⟨564686, by rfl⟩ : syracuseStep 752915 = 1129373) B1129373
theorem B2424113 : Blo 527800 2424113 := bstep (se 2 (by rfl) ⟨909042, by rfl⟩ : syracuseStep 2424113 = 1818085) B1818085
theorem B851393 : Blo 527800 851393 := bstep (se 2 (by rfl) ⟨319272, by rfl⟩ : syracuseStep 851393 = 638545) B638545
theorem B1506833 : Blo 527800 1506833 := bstep (se 2 (by rfl) ⟨565062, by rfl⟩ : syracuseStep 1506833 = 1130125) B1130125
theorem B7274083 : Blo 527800 7274083 := bstep (se 1 (by rfl) ⟨5455562, by rfl⟩ : syracuseStep 7274083 = 10911125) B10911125
theorem B1703555 : Blo 527800 1703555 := bstep (se 1 (by rfl) ⟨1277666, by rfl⟩ : syracuseStep 1703555 = 2555333) B2555333
theorem B1507025 : Blo 527800 1507025 := bstep (se 2 (by rfl) ⟨565134, by rfl⟩ : syracuseStep 1507025 = 1130269) B1130269
theorem B2686769 : Blo 527800 2686769 := bstep (se 2 (by rfl) ⟨1007538, by rfl⟩ : syracuseStep 2686769 = 2015077) B2015077
theorem B753553 : Blo 527800 753553 := bstep (se 2 (by rfl) ⟨282582, by rfl⟩ : syracuseStep 753553 = 565165) B565165
theorem B3014597 : Blo 527800 3014597 := bstep (se 4 (by rfl) ⟨282618, by rfl⟩ : syracuseStep 3014597 = 565237) B565237
theorem B3440819 : Blo 527800 3440819 := bstep (se 1 (by rfl) ⟨2580614, by rfl⟩ : syracuseStep 3440819 = 5161229) B5161229
theorem B1016051 : Blo 527800 1016051 := bstep (se 1 (by rfl) ⟨762038, by rfl⟩ : syracuseStep 1016051 = 1524077) B1524077
theorem B1605953 : Blo 527800 1605953 := bstep (se 2 (by rfl) ⟨602232, by rfl⟩ : syracuseStep 1605953 = 1204465) B1204465
theorem B1344023 : Blo 527800 1344023 := bstep (se 1 (by rfl) ⟨1008017, by rfl⟩ : syracuseStep 1344023 = 2016035) B2016035
theorem B1507891 : Blo 527800 1507891 := bstep (se 1 (by rfl) ⟨1130918, by rfl⟩ : syracuseStep 1507891 = 2261837) B2261837
theorem B2688065 : Blo 527800 2688065 := bstep (se 2 (by rfl) ⟨1008024, by rfl⟩ : syracuseStep 2688065 = 2016049) B2016049
theorem B1344833 : Blo 527800 1344833 := bstep (se 2 (by rfl) ⟨504312, by rfl⟩ : syracuseStep 1344833 = 1008625) B1008625
theorem B951755 : Blo 527800 951755 := bstep (se 1 (by rfl) ⟨713816, by rfl⟩ : syracuseStep 951755 = 1427633) B1427633
theorem B3016237 : Blo 527800 3016237 := bstep (se 3 (by rfl) ⟨565544, by rfl⟩ : syracuseStep 3016237 = 1131089) B1131089
theorem B1508939 : Blo 527800 1508939 := bstep (se 1 (by rfl) ⟨1131704, by rfl⟩ : syracuseStep 1508939 = 2263409) B2263409
theorem B1050199 : Blo 527800 1050199 := bstep (se 1 (by rfl) ⟨787649, by rfl⟩ : syracuseStep 1050199 = 1575299) B1575299
theorem B1345369 : Blo 527800 1345369 := bstep (se 2 (by rfl) ⟨504513, by rfl⟩ : syracuseStep 1345369 = 1009027) B1009027
theorem B952217 : Blo 527800 952217 := bstep (se 2 (by rfl) ⟨357081, by rfl⟩ : syracuseStep 952217 = 714163) B714163
theorem B952627 : Blo 527800 952627 := bstep (se 1 (by rfl) ⟨714470, by rfl⟩ : syracuseStep 952627 = 1428941) B1428941
theorem B2034013 : Blo 527800 2034013 := bstep (se 3 (by rfl) ⟨381377, by rfl⟩ : syracuseStep 2034013 = 762755) B762755
theorem B952715 : Blo 527800 952715 := bstep (se 1 (by rfl) ⟨714536, by rfl⟩ : syracuseStep 952715 = 1429073) B1429073
theorem B953291 : Blo 527800 953291 := bstep (se 1 (by rfl) ⟨714968, by rfl⟩ : syracuseStep 953291 = 1429937) B1429937
theorem B2690009 : Blo 527800 2690009 := bstep (se 2 (by rfl) ⟨1008753, by rfl⟩ : syracuseStep 2690009 = 2017507) B2017507
theorem B756697 : Blo 527800 756697 := bstep (se 2 (by rfl) ⟨283761, by rfl⟩ : syracuseStep 756697 = 567523) B567523
theorem B36637717 : Blo 527800 36637717 := bstep (se 6 (by rfl) ⟨858696, by rfl⟩ : syracuseStep 36637717 = 1717393) B1717393
theorem B1510579 : Blo 527800 1510579 := bstep (se 1 (by rfl) ⟨1132934, by rfl⟩ : syracuseStep 1510579 = 2265869) B2265869
theorem B2264365 : Blo 527800 2264365 := bstep (se 3 (by rfl) ⟨424568, by rfl⟩ : syracuseStep 2264365 = 849137) B849137
theorem B3804509 : Blo 527800 3804509 := bstep (se 3 (by rfl) ⟨713345, by rfl⟩ : syracuseStep 3804509 = 1426691) B1426691
theorem B1510807 : Blo 527800 1510807 := bstep (se 1 (by rfl) ⟨1133105, by rfl⟩ : syracuseStep 1510807 = 2266211) B2266211
theorem B527819 : Blo 527800 527819 := bstep (se 1 (by rfl) ⟨395864, by rfl⟩ : syracuseStep 527819 = 791729) B791729
theorem B527831 : Blo 527800 527831 := bstep (se 1 (by rfl) ⟨395873, by rfl⟩ : syracuseStep 527831 = 791747) B791747
theorem B2264537 : Blo 527800 2264537 := bstep (se 2 (by rfl) ⟨849201, by rfl⟩ : syracuseStep 2264537 = 1698403) B1698403
theorem B527851 : Blo 527800 527851 := bstep (se 1 (by rfl) ⟨395888, by rfl⟩ : syracuseStep 527851 = 791777) B791777
theorem B527863 : Blo 527800 527863 := bstep (se 1 (by rfl) ⟨395897, by rfl⟩ : syracuseStep 527863 = 791795) B791795
theorem B527883 : Blo 527800 527883 := bstep (se 1 (by rfl) ⟨395912, by rfl⟩ : syracuseStep 527883 = 791825) B791825
theorem B527895 : Blo 527800 527895 := bstep (se 1 (by rfl) ⟨395921, by rfl⟩ : syracuseStep 527895 = 791843) B791843
theorem B527915 : Blo 527800 527915 := bstep (se 1 (by rfl) ⟨395936, by rfl⟩ : syracuseStep 527915 = 791873) B791873
theorem B527927 : Blo 527800 527927 := bstep (se 1 (by rfl) ⟨395945, by rfl⟩ : syracuseStep 527927 = 791891) B791891
theorem B527947 : Blo 527800 527947 := bstep (se 1 (by rfl) ⟨395960, by rfl⟩ : syracuseStep 527947 = 791921) B791921
theorem B527959 : Blo 527800 527959 := bstep (se 1 (by rfl) ⟨395969, by rfl⟩ : syracuseStep 527959 = 791939) B791939
theorem B527979 : Blo 527800 527979 := bstep (se 1 (by rfl) ⟨395984, by rfl⟩ : syracuseStep 527979 = 791969) B791969
theorem B527991 : Blo 527800 527991 := bstep (se 1 (by rfl) ⟨395993, by rfl⟩ : syracuseStep 527991 = 791987) B791987
theorem B528011 : Blo 527800 528011 := bstep (se 1 (by rfl) ⟨396008, by rfl⟩ : syracuseStep 528011 = 792017) B792017
theorem B528023 : Blo 527800 528023 := bstep (se 1 (by rfl) ⟨396017, by rfl⟩ : syracuseStep 528023 = 792035) B792035
theorem B528043 : Blo 527800 528043 := bstep (se 1 (by rfl) ⟨396032, by rfl⟩ : syracuseStep 528043 = 792065) B792065
theorem B528055 : Blo 527800 528055 := bstep (se 1 (by rfl) ⟨396041, by rfl⟩ : syracuseStep 528055 = 792083) B792083
theorem B528075 : Blo 527800 528075 := bstep (se 1 (by rfl) ⟨396056, by rfl⟩ : syracuseStep 528075 = 792113) B792113
theorem B528087 : Blo 527800 528087 := bstep (se 1 (by rfl) ⟨396065, by rfl⟩ : syracuseStep 528087 = 792131) B792131
theorem B1806041 : Blo 527800 1806041 := bstep (se 2 (by rfl) ⟨677265, by rfl⟩ : syracuseStep 1806041 = 1354531) B1354531
theorem B1609433 : Blo 527800 1609433 := bstep (se 2 (by rfl) ⟨603537, by rfl⟩ : syracuseStep 1609433 = 1207075) B1207075
theorem B528107 : Blo 527800 528107 := bstep (se 1 (by rfl) ⟨396080, by rfl⟩ : syracuseStep 528107 = 792161) B792161
theorem B528119 : Blo 527800 528119 := bstep (se 1 (by rfl) ⟨396089, by rfl⟩ : syracuseStep 528119 = 792179) B792179
theorem B528139 : Blo 527800 528139 := bstep (se 1 (by rfl) ⟨396104, by rfl⟩ : syracuseStep 528139 = 792209) B792209
theorem B528151 : Blo 527800 528151 := bstep (se 1 (by rfl) ⟨396113, by rfl⟩ : syracuseStep 528151 = 792227) B792227
theorem B528171 : Blo 527800 528171 := bstep (se 1 (by rfl) ⟨396128, by rfl⟩ : syracuseStep 528171 = 792257) B792257
theorem B528183 : Blo 527800 528183 := bstep (se 1 (by rfl) ⟨396137, by rfl⟩ : syracuseStep 528183 = 792275) B792275
theorem B528203 : Blo 527800 528203 := bstep (se 1 (by rfl) ⟨396152, by rfl⟩ : syracuseStep 528203 = 792305) B792305
theorem B528215 : Blo 527800 528215 := bstep (se 1 (by rfl) ⟨396161, by rfl⟩ : syracuseStep 528215 = 792323) B792323
theorem B528235 : Blo 527800 528235 := bstep (se 1 (by rfl) ⟨396176, by rfl⟩ : syracuseStep 528235 = 792353) B792353
theorem B528247 : Blo 527800 528247 := bstep (se 1 (by rfl) ⟨396185, by rfl⟩ : syracuseStep 528247 = 792371) B792371
theorem B528267 : Blo 527800 528267 := bstep (se 1 (by rfl) ⟨396200, by rfl⟩ : syracuseStep 528267 = 792401) B792401
theorem B593815 : Blo 527800 593815 := bstep (se 1 (by rfl) ⟨445361, by rfl⟩ : syracuseStep 593815 = 890723) B890723
theorem B528279 : Blo 527800 528279 := bstep (se 1 (by rfl) ⟨396209, by rfl⟩ : syracuseStep 528279 = 792419) B792419
theorem B528299 : Blo 527800 528299 := bstep (se 1 (by rfl) ⟨396224, by rfl⟩ : syracuseStep 528299 = 792449) B792449
theorem B528311 : Blo 527800 528311 := bstep (se 1 (by rfl) ⟨396233, by rfl⟩ : syracuseStep 528311 = 792467) B792467
theorem B528331 : Blo 527800 528331 := bstep (se 1 (by rfl) ⟨396248, by rfl⟩ : syracuseStep 528331 = 792497) B792497
theorem B528343 : Blo 527800 528343 := bstep (se 1 (by rfl) ⟨396257, by rfl⟩ : syracuseStep 528343 = 792515) B792515
theorem B528363 : Blo 527800 528363 := bstep (se 1 (by rfl) ⟨396272, by rfl⟩ : syracuseStep 528363 = 792545) B792545
theorem B528375 : Blo 527800 528375 := bstep (se 1 (by rfl) ⟨396281, by rfl⟩ : syracuseStep 528375 = 792563) B792563
theorem B528395 : Blo 527800 528395 := bstep (se 1 (by rfl) ⟨396296, by rfl⟩ : syracuseStep 528395 = 792593) B792593
theorem B528407 : Blo 527800 528407 := bstep (se 1 (by rfl) ⟨396305, by rfl⟩ : syracuseStep 528407 = 792611) B792611
theorem B528427 : Blo 527800 528427 := bstep (se 1 (by rfl) ⟨396320, by rfl⟩ : syracuseStep 528427 = 792641) B792641
theorem B528439 : Blo 527800 528439 := bstep (se 1 (by rfl) ⟨396329, by rfl⟩ : syracuseStep 528439 = 792659) B792659
theorem B593995 : Blo 527800 593995 := bstep (se 1 (by rfl) ⟨445496, by rfl⟩ : syracuseStep 593995 = 890993) B890993
theorem B528459 : Blo 527800 528459 := bstep (se 1 (by rfl) ⟨396344, by rfl⟩ : syracuseStep 528459 = 792689) B792689
theorem B528471 : Blo 527800 528471 := bstep (se 1 (by rfl) ⟨396353, by rfl⟩ : syracuseStep 528471 = 792707) B792707
theorem B528491 : Blo 527800 528491 := bstep (se 1 (by rfl) ⟨396368, by rfl⟩ : syracuseStep 528491 = 792737) B792737
theorem B528503 : Blo 527800 528503 := bstep (se 1 (by rfl) ⟨396377, by rfl⟩ : syracuseStep 528503 = 792755) B792755
theorem B528523 : Blo 527800 528523 := bstep (se 1 (by rfl) ⟨396392, by rfl⟩ : syracuseStep 528523 = 792785) B792785
theorem B528535 : Blo 527800 528535 := bstep (se 1 (by rfl) ⟨396401, by rfl⟩ : syracuseStep 528535 = 792803) B792803
theorem B1020055 : Blo 527800 1020055 := bstep (se 1 (by rfl) ⟨765041, by rfl⟩ : syracuseStep 1020055 = 1530083) B1530083
theorem B528555 : Blo 527800 528555 := bstep (se 1 (by rfl) ⟨396416, by rfl⟩ : syracuseStep 528555 = 792833) B792833
theorem B594103 : Blo 527800 594103 := bstep (se 1 (by rfl) ⟨445577, by rfl⟩ : syracuseStep 594103 = 891155) B891155
theorem B528567 : Blo 527800 528567 := bstep (se 1 (by rfl) ⟨396425, by rfl⟩ : syracuseStep 528567 = 792851) B792851
theorem B528587 : Blo 527800 528587 := bstep (se 1 (by rfl) ⟨396440, by rfl⟩ : syracuseStep 528587 = 792881) B792881
theorem B528599 : Blo 527800 528599 := bstep (se 1 (by rfl) ⟨396449, by rfl⟩ : syracuseStep 528599 = 792899) B792899
theorem B528619 : Blo 527800 528619 := bstep (se 1 (by rfl) ⟨396464, by rfl⟩ : syracuseStep 528619 = 792929) B792929
theorem B528631 : Blo 527800 528631 := bstep (se 1 (by rfl) ⟨396473, by rfl⟩ : syracuseStep 528631 = 792947) B792947
theorem B528651 : Blo 527800 528651 := bstep (se 1 (by rfl) ⟨396488, by rfl⟩ : syracuseStep 528651 = 792977) B792977
theorem B528663 : Blo 527800 528663 := bstep (se 1 (by rfl) ⟨396497, by rfl⟩ : syracuseStep 528663 = 792995) B792995
theorem B528683 : Blo 527800 528683 := bstep (se 1 (by rfl) ⟨396512, by rfl⟩ : syracuseStep 528683 = 793025) B793025
theorem B528695 : Blo 527800 528695 := bstep (se 1 (by rfl) ⟨396521, by rfl⟩ : syracuseStep 528695 = 793043) B793043
theorem B528715 : Blo 527800 528715 := bstep (se 1 (by rfl) ⟨396536, by rfl⟩ : syracuseStep 528715 = 793073) B793073
theorem B528727 : Blo 527800 528727 := bstep (se 1 (by rfl) ⟨396545, by rfl⟩ : syracuseStep 528727 = 793091) B793091
theorem B594283 : Blo 527800 594283 := bstep (se 1 (by rfl) ⟨445712, by rfl⟩ : syracuseStep 594283 = 891425) B891425
theorem B528747 : Blo 527800 528747 := bstep (se 1 (by rfl) ⟨396560, by rfl⟩ : syracuseStep 528747 = 793121) B793121
theorem B528759 : Blo 527800 528759 := bstep (se 1 (by rfl) ⟨396569, by rfl⟩ : syracuseStep 528759 = 793139) B793139
theorem B528779 : Blo 527800 528779 := bstep (se 1 (by rfl) ⟨396584, by rfl⟩ : syracuseStep 528779 = 793169) B793169
theorem B528791 : Blo 527800 528791 := bstep (se 1 (by rfl) ⟨396593, by rfl⟩ : syracuseStep 528791 = 793187) B793187
theorem B528811 : Blo 527800 528811 := bstep (se 1 (by rfl) ⟨396608, by rfl⟩ : syracuseStep 528811 = 793217) B793217
theorem B528823 : Blo 527800 528823 := bstep (se 1 (by rfl) ⟨396617, by rfl⟩ : syracuseStep 528823 = 793235) B793235
theorem B528843 : Blo 527800 528843 := bstep (se 1 (by rfl) ⟨396632, by rfl⟩ : syracuseStep 528843 = 793265) B793265
theorem B594391 : Blo 527800 594391 := bstep (se 1 (by rfl) ⟨445793, by rfl⟩ : syracuseStep 594391 = 891587) B891587
theorem B528855 : Blo 527800 528855 := bstep (se 1 (by rfl) ⟨396641, by rfl⟩ : syracuseStep 528855 = 793283) B793283
theorem B528875 : Blo 527800 528875 := bstep (se 1 (by rfl) ⟨396656, by rfl⟩ : syracuseStep 528875 = 793313) B793313
theorem B528887 : Blo 527800 528887 := bstep (se 1 (by rfl) ⟨396665, by rfl⟩ : syracuseStep 528887 = 793331) B793331
theorem B528907 : Blo 527800 528907 := bstep (se 1 (by rfl) ⟨396680, by rfl⟩ : syracuseStep 528907 = 793361) B793361
theorem B14750221 : Blo 527800 14750221 := bstep (se 3 (by rfl) ⟨2765666, by rfl⟩ : syracuseStep 14750221 = 5531333) B5531333
theorem B528919 : Blo 527800 528919 := bstep (se 1 (by rfl) ⟨396689, by rfl⟩ : syracuseStep 528919 = 793379) B793379
theorem B528939 : Blo 527800 528939 := bstep (se 1 (by rfl) ⟨396704, by rfl⟩ : syracuseStep 528939 = 793409) B793409
theorem B2691629 : Blo 527800 2691629 := bstep (se 3 (by rfl) ⟨504680, by rfl⟩ : syracuseStep 2691629 = 1009361) B1009361
theorem B528951 : Blo 527800 528951 := bstep (se 1 (by rfl) ⟨396713, by rfl⟩ : syracuseStep 528951 = 793427) B793427
theorem B528971 : Blo 527800 528971 := bstep (se 1 (by rfl) ⟨396728, by rfl⟩ : syracuseStep 528971 = 793457) B793457
theorem B528983 : Blo 527800 528983 := bstep (se 1 (by rfl) ⟨396737, by rfl⟩ : syracuseStep 528983 = 793475) B793475
theorem B529003 : Blo 527800 529003 := bstep (se 1 (by rfl) ⟨396752, by rfl⟩ : syracuseStep 529003 = 793505) B793505
theorem B529015 : Blo 527800 529015 := bstep (se 1 (by rfl) ⟨396761, by rfl⟩ : syracuseStep 529015 = 793523) B793523
theorem B594571 : Blo 527800 594571 := bstep (se 1 (by rfl) ⟨445928, by rfl⟩ : syracuseStep 594571 = 891857) B891857
theorem B529035 : Blo 527800 529035 := bstep (se 1 (by rfl) ⟨396776, by rfl⟩ : syracuseStep 529035 = 793553) B793553
theorem B529047 : Blo 527800 529047 := bstep (se 1 (by rfl) ⟨396785, by rfl⟩ : syracuseStep 529047 = 793571) B793571
theorem B529067 : Blo 527800 529067 := bstep (se 1 (by rfl) ⟨396800, by rfl⟩ : syracuseStep 529067 = 793601) B793601
theorem B529079 : Blo 527800 529079 := bstep (se 1 (by rfl) ⟨396809, by rfl⟩ : syracuseStep 529079 = 793619) B793619
theorem B529099 : Blo 527800 529099 := bstep (se 1 (by rfl) ⟨396824, by rfl⟩ : syracuseStep 529099 = 793649) B793649
theorem B529111 : Blo 527800 529111 := bstep (se 1 (by rfl) ⟨396833, by rfl⟩ : syracuseStep 529111 = 793667) B793667
theorem B529131 : Blo 527800 529131 := bstep (se 1 (by rfl) ⟨396848, by rfl⟩ : syracuseStep 529131 = 793697) B793697
theorem B594679 : Blo 527800 594679 := bstep (se 1 (by rfl) ⟨446009, by rfl⟩ : syracuseStep 594679 = 892019) B892019
theorem B529143 : Blo 527800 529143 := bstep (se 1 (by rfl) ⟨396857, by rfl⟩ : syracuseStep 529143 = 793715) B793715
theorem B529163 : Blo 527800 529163 := bstep (se 1 (by rfl) ⟨396872, by rfl⟩ : syracuseStep 529163 = 793745) B793745
theorem B529175 : Blo 527800 529175 := bstep (se 1 (by rfl) ⟨396881, by rfl⟩ : syracuseStep 529175 = 793763) B793763
theorem B529195 : Blo 527800 529195 := bstep (se 1 (by rfl) ⟨396896, by rfl⟩ : syracuseStep 529195 = 793793) B793793
theorem B529207 : Blo 527800 529207 := bstep (se 1 (by rfl) ⟨396905, by rfl⟩ : syracuseStep 529207 = 793811) B793811
theorem B529227 : Blo 527800 529227 := bstep (se 1 (by rfl) ⟨396920, by rfl⟩ : syracuseStep 529227 = 793841) B793841
theorem B529239 : Blo 527800 529239 := bstep (se 1 (by rfl) ⟨396929, by rfl⟩ : syracuseStep 529239 = 793859) B793859
theorem B529259 : Blo 527800 529259 := bstep (se 1 (by rfl) ⟨396944, by rfl⟩ : syracuseStep 529259 = 793889) B793889
theorem B529271 : Blo 527800 529271 := bstep (se 1 (by rfl) ⟨396953, by rfl⟩ : syracuseStep 529271 = 793907) B793907
theorem B529291 : Blo 527800 529291 := bstep (se 1 (by rfl) ⟨396968, by rfl⟩ : syracuseStep 529291 = 793937) B793937
theorem B529303 : Blo 527800 529303 := bstep (se 1 (by rfl) ⟨396977, by rfl⟩ : syracuseStep 529303 = 793955) B793955
theorem B594859 : Blo 527800 594859 := bstep (se 1 (by rfl) ⟨446144, by rfl⟩ : syracuseStep 594859 = 892289) B892289
theorem B529323 : Blo 527800 529323 := bstep (se 1 (by rfl) ⟨396992, by rfl⟩ : syracuseStep 529323 = 793985) B793985
theorem B529335 : Blo 527800 529335 := bstep (se 1 (by rfl) ⟨397001, by rfl⟩ : syracuseStep 529335 = 794003) B794003
theorem B529355 : Blo 527800 529355 := bstep (se 1 (by rfl) ⟨397016, by rfl⟩ : syracuseStep 529355 = 794033) B794033
theorem B529367 : Blo 527800 529367 := bstep (se 1 (by rfl) ⟨397025, by rfl⟩ : syracuseStep 529367 = 794051) B794051
theorem B529387 : Blo 527800 529387 := bstep (se 1 (by rfl) ⟨397040, by rfl⟩ : syracuseStep 529387 = 794081) B794081
theorem B529399 : Blo 527800 529399 := bstep (se 1 (by rfl) ⟨397049, by rfl⟩ : syracuseStep 529399 = 794099) B794099
theorem B529419 : Blo 527800 529419 := bstep (se 1 (by rfl) ⟨397064, by rfl⟩ : syracuseStep 529419 = 794129) B794129
theorem B594967 : Blo 527800 594967 := bstep (se 1 (by rfl) ⟨446225, by rfl⟩ : syracuseStep 594967 = 892451) B892451
theorem B529431 : Blo 527800 529431 := bstep (se 1 (by rfl) ⟨397073, by rfl⟩ : syracuseStep 529431 = 794147) B794147
theorem B529451 : Blo 527800 529451 := bstep (se 1 (by rfl) ⟨397088, by rfl⟩ : syracuseStep 529451 = 794177) B794177
theorem B529463 : Blo 527800 529463 := bstep (se 1 (by rfl) ⟨397097, by rfl⟩ : syracuseStep 529463 = 794195) B794195
theorem B2266177 : Blo 527800 2266177 := bstep (se 2 (by rfl) ⟨849816, by rfl⟩ : syracuseStep 2266177 = 1699633) B1699633
theorem B529483 : Blo 527800 529483 := bstep (se 1 (by rfl) ⟨397112, by rfl⟩ : syracuseStep 529483 = 794225) B794225
theorem B529495 : Blo 527800 529495 := bstep (se 1 (by rfl) ⟨397121, by rfl⟩ : syracuseStep 529495 = 794243) B794243
theorem B529515 : Blo 527800 529515 := bstep (se 1 (by rfl) ⟨397136, by rfl⟩ : syracuseStep 529515 = 794273) B794273
theorem B529527 : Blo 527800 529527 := bstep (se 1 (by rfl) ⟨397145, by rfl⟩ : syracuseStep 529527 = 794291) B794291
theorem B3413123 : Blo 527800 3413123 := bstep (se 1 (by rfl) ⟨2559842, by rfl⟩ : syracuseStep 3413123 = 5119685) B5119685
theorem B529547 : Blo 527800 529547 := bstep (se 1 (by rfl) ⟨397160, by rfl⟩ : syracuseStep 529547 = 794321) B794321
theorem B529559 : Blo 527800 529559 := bstep (se 1 (by rfl) ⟨397169, by rfl⟩ : syracuseStep 529559 = 794339) B794339
theorem B791705 : Blo 527800 791705 := bstep (se 2 (by rfl) ⟨296889, by rfl⟩ : syracuseStep 791705 = 593779) B593779
theorem B529579 : Blo 527800 529579 := bstep (se 1 (by rfl) ⟨397184, by rfl⟩ : syracuseStep 529579 = 794369) B794369
theorem B529591 : Blo 527800 529591 := bstep (se 1 (by rfl) ⟨397193, by rfl⟩ : syracuseStep 529591 = 794387) B794387
theorem B595147 : Blo 527800 595147 := bstep (se 1 (by rfl) ⟨446360, by rfl⟩ : syracuseStep 595147 = 892721) B892721
theorem B529611 : Blo 527800 529611 := bstep (se 1 (by rfl) ⟨397208, by rfl⟩ : syracuseStep 529611 = 794417) B794417
theorem B5084365 : Blo 527800 5084365 := bstep (se 3 (by rfl) ⟨953318, by rfl⟩ : syracuseStep 5084365 = 1906637) B1906637
theorem B529623 : Blo 527800 529623 := bstep (se 1 (by rfl) ⟨397217, by rfl⟩ : syracuseStep 529623 = 794435) B794435
theorem B1512665 : Blo 527800 1512665 := bstep (se 2 (by rfl) ⟨567249, by rfl⟩ : syracuseStep 1512665 = 1134499) B1134499
theorem B529643 : Blo 527800 529643 := bstep (se 1 (by rfl) ⟨397232, by rfl⟩ : syracuseStep 529643 = 794465) B794465
theorem B529655 : Blo 527800 529655 := bstep (se 1 (by rfl) ⟨397241, by rfl⟩ : syracuseStep 529655 = 794483) B794483
theorem B791819 : Blo 527800 791819 := bstep (se 1 (by rfl) ⟨593864, by rfl⟩ : syracuseStep 791819 = 1187729) B1187729
theorem B529675 : Blo 527800 529675 := bstep (se 1 (by rfl) ⟨397256, by rfl⟩ : syracuseStep 529675 = 794513) B794513
theorem B791831 : Blo 527800 791831 := bstep (se 1 (by rfl) ⟨593873, by rfl⟩ : syracuseStep 791831 = 1187747) B1187747
theorem B529687 : Blo 527800 529687 := bstep (se 1 (by rfl) ⟨397265, by rfl⟩ : syracuseStep 529687 = 794531) B794531
theorem B529707 : Blo 527800 529707 := bstep (se 1 (by rfl) ⟨397280, by rfl⟩ : syracuseStep 529707 = 794561) B794561
theorem B595255 : Blo 527800 595255 := bstep (se 1 (by rfl) ⟨446441, by rfl⟩ : syracuseStep 595255 = 892883) B892883
theorem B529719 : Blo 527800 529719 := bstep (se 1 (by rfl) ⟨397289, by rfl⟩ : syracuseStep 529719 = 794579) B794579
theorem B529739 : Blo 527800 529739 := bstep (se 1 (by rfl) ⟨397304, by rfl⟩ : syracuseStep 529739 = 794609) B794609
theorem B529751 : Blo 527800 529751 := bstep (se 1 (by rfl) ⟨397313, by rfl⟩ : syracuseStep 529751 = 794627) B794627
theorem B791897 : Blo 527800 791897 := bstep (se 2 (by rfl) ⟨296961, by rfl⟩ : syracuseStep 791897 = 593923) B593923
theorem B529771 : Blo 527800 529771 := bstep (se 1 (by rfl) ⟨397328, by rfl⟩ : syracuseStep 529771 = 794657) B794657
theorem B529783 : Blo 527800 529783 := bstep (se 1 (by rfl) ⟨397337, by rfl⟩ : syracuseStep 529783 = 794675) B794675
theorem B529803 : Blo 527800 529803 := bstep (se 1 (by rfl) ⟨397352, by rfl⟩ : syracuseStep 529803 = 794705) B794705
theorem B529815 : Blo 527800 529815 := bstep (se 1 (by rfl) ⟨397361, by rfl⟩ : syracuseStep 529815 = 794723) B794723
theorem B529835 : Blo 527800 529835 := bstep (se 1 (by rfl) ⟨397376, by rfl⟩ : syracuseStep 529835 = 794753) B794753
theorem B529847 : Blo 527800 529847 := bstep (se 1 (by rfl) ⟨397385, by rfl⟩ : syracuseStep 529847 = 794771) B794771
theorem B792011 : Blo 527800 792011 := bstep (se 1 (by rfl) ⟨594008, by rfl⟩ : syracuseStep 792011 = 1188017) B1188017
theorem B529867 : Blo 527800 529867 := bstep (se 1 (by rfl) ⟨397400, by rfl⟩ : syracuseStep 529867 = 794801) B794801
theorem B792023 : Blo 527800 792023 := bstep (se 1 (by rfl) ⟨594017, by rfl⟩ : syracuseStep 792023 = 1188035) B1188035
theorem B529879 : Blo 527800 529879 := bstep (se 1 (by rfl) ⟨397409, by rfl⟩ : syracuseStep 529879 = 794819) B794819
theorem B595435 : Blo 527800 595435 := bstep (se 1 (by rfl) ⟨446576, by rfl⟩ : syracuseStep 595435 = 893153) B893153
theorem B529899 : Blo 527800 529899 := bstep (se 1 (by rfl) ⟨397424, by rfl⟩ : syracuseStep 529899 = 794849) B794849
theorem B529911 : Blo 527800 529911 := bstep (se 1 (by rfl) ⟨397433, by rfl⟩ : syracuseStep 529911 = 794867) B794867
theorem B529931 : Blo 527800 529931 := bstep (se 1 (by rfl) ⟨397448, by rfl⟩ : syracuseStep 529931 = 794897) B794897
theorem B529943 : Blo 527800 529943 := bstep (se 1 (by rfl) ⟨397457, by rfl⟩ : syracuseStep 529943 = 794915) B794915
theorem B792089 : Blo 527800 792089 := bstep (se 2 (by rfl) ⟨297033, by rfl⟩ : syracuseStep 792089 = 594067) B594067
theorem B529963 : Blo 527800 529963 := bstep (se 1 (by rfl) ⟨397472, by rfl⟩ : syracuseStep 529963 = 794945) B794945
theorem B1938995 : Blo 527800 1938995 := bstep (se 1 (by rfl) ⟨1454246, by rfl⟩ : syracuseStep 1938995 = 2908493) B2908493
theorem B529975 : Blo 527800 529975 := bstep (se 1 (by rfl) ⟨397481, by rfl⟩ : syracuseStep 529975 = 794963) B794963
theorem B529995 : Blo 527800 529995 := bstep (se 1 (by rfl) ⟨397496, by rfl⟩ : syracuseStep 529995 = 794993) B794993
theorem B595543 : Blo 527800 595543 := bstep (se 1 (by rfl) ⟨446657, by rfl⟩ : syracuseStep 595543 = 893315) B893315
theorem B530007 : Blo 527800 530007 := bstep (se 1 (by rfl) ⟨397505, by rfl⟩ : syracuseStep 530007 = 795011) B795011
theorem B530027 : Blo 527800 530027 := bstep (se 1 (by rfl) ⟨397520, by rfl⟩ : syracuseStep 530027 = 795041) B795041
theorem B530039 : Blo 527800 530039 := bstep (se 1 (by rfl) ⟨397529, by rfl⟩ : syracuseStep 530039 = 795059) B795059
theorem B792203 : Blo 527800 792203 := bstep (se 1 (by rfl) ⟨594152, by rfl⟩ : syracuseStep 792203 = 1188305) B1188305
theorem B530059 : Blo 527800 530059 := bstep (se 1 (by rfl) ⟨397544, by rfl⟩ : syracuseStep 530059 = 795089) B795089
theorem B792215 : Blo 527800 792215 := bstep (se 1 (by rfl) ⟨594161, by rfl⟩ : syracuseStep 792215 = 1188323) B1188323
theorem B530071 : Blo 527800 530071 := bstep (se 1 (by rfl) ⟨397553, by rfl⟩ : syracuseStep 530071 = 795107) B795107
theorem B530091 : Blo 527800 530091 := bstep (se 1 (by rfl) ⟨397568, by rfl⟩ : syracuseStep 530091 = 795137) B795137
theorem B2004659 : Blo 527800 2004659 := bstep (se 1 (by rfl) ⟨1503494, by rfl⟩ : syracuseStep 2004659 = 3006989) B3006989
theorem B530103 : Blo 527800 530103 := bstep (se 1 (by rfl) ⟨397577, by rfl⟩ : syracuseStep 530103 = 795155) B795155
theorem B530123 : Blo 527800 530123 := bstep (se 1 (by rfl) ⟨397592, by rfl⟩ : syracuseStep 530123 = 795185) B795185
theorem B9049805 : Blo 527800 9049805 := bstep (se 3 (by rfl) ⟨1696838, by rfl⟩ : syracuseStep 9049805 = 3393677) B3393677
theorem B530135 : Blo 527800 530135 := bstep (se 1 (by rfl) ⟨397601, by rfl⟩ : syracuseStep 530135 = 795203) B795203
theorem B792281 : Blo 527800 792281 := bstep (se 2 (by rfl) ⟨297105, by rfl⟩ : syracuseStep 792281 = 594211) B594211
theorem B530155 : Blo 527800 530155 := bstep (se 1 (by rfl) ⟨397616, by rfl⟩ : syracuseStep 530155 = 795233) B795233
theorem B530167 : Blo 527800 530167 := bstep (se 1 (by rfl) ⟨397625, by rfl⟩ : syracuseStep 530167 = 795251) B795251
theorem B595723 : Blo 527800 595723 := bstep (se 1 (by rfl) ⟨446792, by rfl⟩ : syracuseStep 595723 = 893585) B893585
theorem B530187 : Blo 527800 530187 := bstep (se 1 (by rfl) ⟨397640, by rfl⟩ : syracuseStep 530187 = 795281) B795281
theorem B2037521 : Blo 527800 2037521 := bstep (se 2 (by rfl) ⟨764070, by rfl⟩ : syracuseStep 2037521 = 1528141) B1528141
theorem B530199 : Blo 527800 530199 := bstep (se 1 (by rfl) ⟨397649, by rfl⟩ : syracuseStep 530199 = 795299) B795299
theorem B530219 : Blo 527800 530219 := bstep (se 1 (by rfl) ⟨397664, by rfl⟩ : syracuseStep 530219 = 795329) B795329
theorem B530231 : Blo 527800 530231 := bstep (se 1 (by rfl) ⟨397673, by rfl⟩ : syracuseStep 530231 = 795347) B795347
theorem B792395 : Blo 527800 792395 := bstep (se 1 (by rfl) ⟨594296, by rfl⟩ : syracuseStep 792395 = 1188593) B1188593
theorem B530251 : Blo 527800 530251 := bstep (se 1 (by rfl) ⟨397688, by rfl⟩ : syracuseStep 530251 = 795377) B795377
theorem B792407 : Blo 527800 792407 := bstep (se 1 (by rfl) ⟨594305, by rfl⟩ : syracuseStep 792407 = 1188611) B1188611
theorem B530263 : Blo 527800 530263 := bstep (se 1 (by rfl) ⟨397697, by rfl⟩ : syracuseStep 530263 = 795395) B795395
theorem B530283 : Blo 527800 530283 := bstep (se 1 (by rfl) ⟨397712, by rfl⟩ : syracuseStep 530283 = 795425) B795425
theorem B595831 : Blo 527800 595831 := bstep (se 1 (by rfl) ⟨446873, by rfl⟩ : syracuseStep 595831 = 893747) B893747
theorem B530295 : Blo 527800 530295 := bstep (se 1 (by rfl) ⟨397721, by rfl⟩ : syracuseStep 530295 = 795443) B795443
theorem B530315 : Blo 527800 530315 := bstep (se 1 (by rfl) ⟨397736, by rfl⟩ : syracuseStep 530315 = 795473) B795473
theorem B530327 : Blo 527800 530327 := bstep (se 1 (by rfl) ⟨397745, by rfl⟩ : syracuseStep 530327 = 795491) B795491
theorem B890777 : Blo 527800 890777 := bstep (se 2 (by rfl) ⟨334041, by rfl⟩ : syracuseStep 890777 = 668083) B668083
theorem B792473 : Blo 527800 792473 := bstep (se 2 (by rfl) ⟨297177, by rfl⟩ : syracuseStep 792473 = 594355) B594355
theorem B530347 : Blo 527800 530347 := bstep (se 1 (by rfl) ⟨397760, by rfl⟩ : syracuseStep 530347 = 795521) B795521
theorem B530359 : Blo 527800 530359 := bstep (se 1 (by rfl) ⟨397769, by rfl⟩ : syracuseStep 530359 = 795539) B795539
theorem B530379 : Blo 527800 530379 := bstep (se 1 (by rfl) ⟨397784, by rfl⟩ : syracuseStep 530379 = 795569) B795569
theorem B530391 : Blo 527800 530391 := bstep (se 1 (by rfl) ⟨397793, by rfl⟩ : syracuseStep 530391 = 795587) B795587
theorem B530411 : Blo 527800 530411 := bstep (se 1 (by rfl) ⟨397808, by rfl⟩ : syracuseStep 530411 = 795617) B795617
theorem B530423 : Blo 527800 530423 := bstep (se 1 (by rfl) ⟨397817, by rfl⟩ : syracuseStep 530423 = 795635) B795635
theorem B792587 : Blo 527800 792587 := bstep (se 1 (by rfl) ⟨594440, by rfl⟩ : syracuseStep 792587 = 1188881) B1188881
theorem B530443 : Blo 527800 530443 := bstep (se 1 (by rfl) ⟨397832, by rfl⟩ : syracuseStep 530443 = 795665) B795665
theorem B792599 : Blo 527800 792599 := bstep (se 1 (by rfl) ⟨594449, by rfl⟩ : syracuseStep 792599 = 1188899) B1188899
theorem B530455 : Blo 527800 530455 := bstep (se 1 (by rfl) ⟨397841, by rfl⟩ : syracuseStep 530455 = 795683) B795683
theorem B890905 : Blo 527800 890905 := bstep (se 2 (by rfl) ⟨334089, by rfl⟩ : syracuseStep 890905 = 668179) B668179
theorem B1513495 : Blo 527800 1513495 := bstep (se 1 (by rfl) ⟨1135121, by rfl⟩ : syracuseStep 1513495 = 2270243) B2270243
theorem B596011 : Blo 527800 596011 := bstep (se 1 (by rfl) ⟨447008, by rfl⟩ : syracuseStep 596011 = 894017) B894017
theorem B530475 : Blo 527800 530475 := bstep (se 1 (by rfl) ⟨397856, by rfl⟩ : syracuseStep 530475 = 795713) B795713
theorem B530487 : Blo 527800 530487 := bstep (se 1 (by rfl) ⟨397865, by rfl⟩ : syracuseStep 530487 = 795731) B795731
theorem B1906753 : Blo 527800 1906753 := bstep (se 2 (by rfl) ⟨715032, by rfl⟩ : syracuseStep 1906753 = 1430065) B1430065
theorem B530507 : Blo 527800 530507 := bstep (se 1 (by rfl) ⟨397880, by rfl⟩ : syracuseStep 530507 = 795761) B795761
theorem B530519 : Blo 527800 530519 := bstep (se 1 (by rfl) ⟨397889, by rfl⟩ : syracuseStep 530519 = 795779) B795779
theorem B792665 : Blo 527800 792665 := bstep (se 2 (by rfl) ⟨297249, by rfl⟩ : syracuseStep 792665 = 594499) B594499
theorem B1022041 : Blo 527800 1022041 := bstep (se 2 (by rfl) ⟨383265, by rfl⟩ : syracuseStep 1022041 = 766531) B766531
theorem B530539 : Blo 527800 530539 := bstep (se 1 (by rfl) ⟨397904, by rfl⟩ : syracuseStep 530539 = 795809) B795809
theorem B530551 : Blo 527800 530551 := bstep (se 1 (by rfl) ⟨397913, by rfl⟩ : syracuseStep 530551 = 795827) B795827
theorem B530571 : Blo 527800 530571 := bstep (se 1 (by rfl) ⟨397928, by rfl⟩ : syracuseStep 530571 = 795857) B795857
theorem B596119 : Blo 527800 596119 := bstep (se 1 (by rfl) ⟨447089, by rfl⟩ : syracuseStep 596119 = 894179) B894179
theorem B530583 : Blo 527800 530583 := bstep (se 1 (by rfl) ⟨397937, by rfl⟩ : syracuseStep 530583 = 795875) B795875
theorem B530603 : Blo 527800 530603 := bstep (se 1 (by rfl) ⟨397952, by rfl⟩ : syracuseStep 530603 = 795905) B795905
theorem B530615 : Blo 527800 530615 := bstep (se 1 (by rfl) ⟨397961, by rfl⟩ : syracuseStep 530615 = 795923) B795923
theorem B792779 : Blo 527800 792779 := bstep (se 1 (by rfl) ⟨594584, by rfl⟩ : syracuseStep 792779 = 1189169) B1189169
theorem B530635 : Blo 527800 530635 := bstep (se 1 (by rfl) ⟨397976, by rfl⟩ : syracuseStep 530635 = 795953) B795953
theorem B792791 : Blo 527800 792791 := bstep (se 1 (by rfl) ⟨594593, by rfl⟩ : syracuseStep 792791 = 1189187) B1189187
theorem B530647 : Blo 527800 530647 := bstep (se 1 (by rfl) ⟨397985, by rfl⟩ : syracuseStep 530647 = 795971) B795971
theorem B530667 : Blo 527800 530667 := bstep (se 1 (by rfl) ⟨398000, by rfl⟩ : syracuseStep 530667 = 796001) B796001
theorem B530679 : Blo 527800 530679 := bstep (se 1 (by rfl) ⟨398009, by rfl⟩ : syracuseStep 530679 = 796019) B796019
theorem B1022209 : Blo 527800 1022209 := bstep (se 2 (by rfl) ⟨383328, by rfl⟩ : syracuseStep 1022209 = 766657) B766657
theorem B530699 : Blo 527800 530699 := bstep (se 1 (by rfl) ⟨398024, by rfl⟩ : syracuseStep 530699 = 796049) B796049
theorem B530711 : Blo 527800 530711 := bstep (se 1 (by rfl) ⟨398033, by rfl⟩ : syracuseStep 530711 = 796067) B796067
theorem B792857 : Blo 527800 792857 := bstep (se 2 (by rfl) ⟨297321, by rfl⟩ : syracuseStep 792857 = 594643) B594643
theorem B530731 : Blo 527800 530731 := bstep (se 1 (by rfl) ⟨398048, by rfl⟩ : syracuseStep 530731 = 796097) B796097
theorem B530743 : Blo 527800 530743 := bstep (se 1 (by rfl) ⟨398057, by rfl⟩ : syracuseStep 530743 = 796115) B796115
theorem B596299 : Blo 527800 596299 := bstep (se 1 (by rfl) ⟨447224, by rfl⟩ : syracuseStep 596299 = 894449) B894449
theorem B530763 : Blo 527800 530763 := bstep (se 1 (by rfl) ⟨398072, by rfl⟩ : syracuseStep 530763 = 796145) B796145
theorem B530775 : Blo 527800 530775 := bstep (se 1 (by rfl) ⟨398081, by rfl⟩ : syracuseStep 530775 = 796163) B796163
theorem B530795 : Blo 527800 530795 := bstep (se 1 (by rfl) ⟨398096, by rfl⟩ : syracuseStep 530795 = 796193) B796193
theorem B530807 : Blo 527800 530807 := bstep (se 1 (by rfl) ⟨398105, by rfl⟩ : syracuseStep 530807 = 796211) B796211
theorem B792971 : Blo 527800 792971 := bstep (se 1 (by rfl) ⟨594728, by rfl⟩ : syracuseStep 792971 = 1189457) B1189457
theorem B530827 : Blo 527800 530827 := bstep (se 1 (by rfl) ⟨398120, by rfl⟩ : syracuseStep 530827 = 796241) B796241
theorem B14522773 : Blo 527800 14522773 := bstep (se 6 (by rfl) ⟨340377, by rfl⟩ : syracuseStep 14522773 = 680755) B680755
theorem B792983 : Blo 527800 792983 := bstep (se 1 (by rfl) ⟨594737, by rfl⟩ : syracuseStep 792983 = 1189475) B1189475
theorem B530839 : Blo 527800 530839 := bstep (se 1 (by rfl) ⟨398129, by rfl⟩ : syracuseStep 530839 = 796259) B796259
theorem B530859 : Blo 527800 530859 := bstep (se 1 (by rfl) ⟨398144, by rfl⟩ : syracuseStep 530859 = 796289) B796289
theorem B596407 : Blo 527800 596407 := bstep (se 1 (by rfl) ⟨447305, by rfl⟩ : syracuseStep 596407 = 894611) B894611
theorem B530871 : Blo 527800 530871 := bstep (se 1 (by rfl) ⟨398153, by rfl⟩ : syracuseStep 530871 = 796307) B796307
theorem B530891 : Blo 527800 530891 := bstep (se 1 (by rfl) ⟨398168, by rfl⟩ : syracuseStep 530891 = 796337) B796337
theorem B530903 : Blo 527800 530903 := bstep (se 1 (by rfl) ⟨398177, by rfl⟩ : syracuseStep 530903 = 796355) B796355
theorem B793049 : Blo 527800 793049 := bstep (se 2 (by rfl) ⟨297393, by rfl⟩ : syracuseStep 793049 = 594787) B594787
theorem B530923 : Blo 527800 530923 := bstep (se 1 (by rfl) ⟨398192, by rfl⟩ : syracuseStep 530923 = 796385) B796385
theorem B530935 : Blo 527800 530935 := bstep (se 1 (by rfl) ⟨398201, by rfl⟩ : syracuseStep 530935 = 796403) B796403
theorem B530955 : Blo 527800 530955 := bstep (se 1 (by rfl) ⟨398216, by rfl⟩ : syracuseStep 530955 = 796433) B796433
theorem B530967 : Blo 527800 530967 := bstep (se 1 (by rfl) ⟨398225, by rfl⟩ : syracuseStep 530967 = 796451) B796451
theorem B530987 : Blo 527800 530987 := bstep (se 1 (by rfl) ⟨398240, by rfl⟩ : syracuseStep 530987 = 796481) B796481
theorem B530999 : Blo 527800 530999 := bstep (se 1 (by rfl) ⟨398249, by rfl⟩ : syracuseStep 530999 = 796499) B796499
theorem B793163 : Blo 527800 793163 := bstep (se 1 (by rfl) ⟨594872, by rfl⟩ : syracuseStep 793163 = 1189745) B1189745
theorem B531019 : Blo 527800 531019 := bstep (se 1 (by rfl) ⟨398264, by rfl⟩ : syracuseStep 531019 = 796529) B796529
theorem B891479 : Blo 527800 891479 := bstep (se 1 (by rfl) ⟨668609, by rfl⟩ : syracuseStep 891479 = 1337219) B1337219
theorem B793175 : Blo 527800 793175 := bstep (se 1 (by rfl) ⟨594881, by rfl⟩ : syracuseStep 793175 = 1189763) B1189763
theorem B531031 : Blo 527800 531031 := bstep (se 1 (by rfl) ⟨398273, by rfl⟩ : syracuseStep 531031 = 796547) B796547
theorem B563819 : Blo 527800 563819 := bstep (se 1 (by rfl) ⟨422864, by rfl⟩ : syracuseStep 563819 = 845729) B845729
theorem B596587 : Blo 527800 596587 := bstep (se 1 (by rfl) ⟨447440, by rfl⟩ : syracuseStep 596587 = 894881) B894881
theorem B531051 : Blo 527800 531051 := bstep (se 1 (by rfl) ⟨398288, by rfl⟩ : syracuseStep 531051 = 796577) B796577
theorem B531063 : Blo 527800 531063 := bstep (se 1 (by rfl) ⟨398297, by rfl⟩ : syracuseStep 531063 = 796595) B796595
theorem B531083 : Blo 527800 531083 := bstep (se 1 (by rfl) ⟨398312, by rfl⟩ : syracuseStep 531083 = 796625) B796625
theorem B6036119 : Blo 527800 6036119 := bstep (se 1 (by rfl) ⟨4527089, by rfl⟩ : syracuseStep 6036119 = 9054179) B9054179
theorem B531095 : Blo 527800 531095 := bstep (se 1 (by rfl) ⟨398321, by rfl⟩ : syracuseStep 531095 = 796643) B796643
theorem B793241 : Blo 527800 793241 := bstep (se 2 (by rfl) ⟨297465, by rfl⟩ : syracuseStep 793241 = 594931) B594931
theorem B531115 : Blo 527800 531115 := bstep (se 1 (by rfl) ⟨398336, by rfl⟩ : syracuseStep 531115 = 796673) B796673
theorem B531127 : Blo 527800 531127 := bstep (se 1 (by rfl) ⟨398345, by rfl⟩ : syracuseStep 531127 = 796691) B796691
theorem B2267851 : Blo 527800 2267851 := bstep (se 1 (by rfl) ⟨1700888, by rfl⟩ : syracuseStep 2267851 = 3401777) B3401777
theorem B531147 : Blo 527800 531147 := bstep (se 1 (by rfl) ⟨398360, by rfl⟩ : syracuseStep 531147 = 796721) B796721
theorem B891607 : Blo 527800 891607 := bstep (se 1 (by rfl) ⟨668705, by rfl⟩ : syracuseStep 891607 = 1337411) B1337411
theorem B596695 : Blo 527800 596695 := bstep (se 1 (by rfl) ⟨447521, by rfl⟩ : syracuseStep 596695 = 895043) B895043
theorem B531159 : Blo 527800 531159 := bstep (se 1 (by rfl) ⟨398369, by rfl⟩ : syracuseStep 531159 = 796739) B796739
theorem B531179 : Blo 527800 531179 := bstep (se 1 (by rfl) ⟨398384, by rfl⟩ : syracuseStep 531179 = 796769) B796769
theorem B531191 : Blo 527800 531191 := bstep (se 1 (by rfl) ⟨398393, by rfl⟩ : syracuseStep 531191 = 796787) B796787
theorem B793355 : Blo 527800 793355 := bstep (se 1 (by rfl) ⟨595016, by rfl⟩ : syracuseStep 793355 = 1190033) B1190033
theorem B531211 : Blo 527800 531211 := bstep (se 1 (by rfl) ⟨398408, by rfl⟩ : syracuseStep 531211 = 796817) B796817
theorem B793367 : Blo 527800 793367 := bstep (se 1 (by rfl) ⟨595025, by rfl⟩ : syracuseStep 793367 = 1190051) B1190051
theorem B531223 : Blo 527800 531223 := bstep (se 1 (by rfl) ⟨398417, by rfl⟩ : syracuseStep 531223 = 796835) B796835
theorem B531243 : Blo 527800 531243 := bstep (se 1 (by rfl) ⟨398432, by rfl⟩ : syracuseStep 531243 = 796865) B796865
theorem B531255 : Blo 527800 531255 := bstep (se 1 (by rfl) ⟨398441, by rfl⟩ : syracuseStep 531255 = 796883) B796883
theorem B1612619 : Blo 527800 1612619 := bstep (se 1 (by rfl) ⟨1209464, by rfl⟩ : syracuseStep 1612619 = 2418929) B2418929
theorem B531275 : Blo 527800 531275 := bstep (se 1 (by rfl) ⟨398456, by rfl⟩ : syracuseStep 531275 = 796913) B796913
theorem B1514315 : Blo 527800 1514315 := bstep (se 1 (by rfl) ⟨1135736, by rfl⟩ : syracuseStep 1514315 = 2271473) B2271473
theorem B531287 : Blo 527800 531287 := bstep (se 1 (by rfl) ⟨398465, by rfl⟩ : syracuseStep 531287 = 796931) B796931
theorem B793433 : Blo 527800 793433 := bstep (se 2 (by rfl) ⟨297537, by rfl⟩ : syracuseStep 793433 = 595075) B595075
theorem B531307 : Blo 527800 531307 := bstep (se 1 (by rfl) ⟨398480, by rfl⟩ : syracuseStep 531307 = 796961) B796961
theorem B531319 : Blo 527800 531319 := bstep (se 1 (by rfl) ⟨398489, by rfl⟩ : syracuseStep 531319 = 796979) B796979
theorem B596875 : Blo 527800 596875 := bstep (se 1 (by rfl) ⟨447656, by rfl⟩ : syracuseStep 596875 = 895313) B895313
theorem B531339 : Blo 527800 531339 := bstep (se 1 (by rfl) ⟨398504, by rfl⟩ : syracuseStep 531339 = 797009) B797009
theorem B531351 : Blo 527800 531351 := bstep (se 1 (by rfl) ⟨398513, by rfl⟩ : syracuseStep 531351 = 797027) B797027
theorem B531371 : Blo 527800 531371 := bstep (se 1 (by rfl) ⟨398528, by rfl⟩ : syracuseStep 531371 = 797057) B797057
theorem B531383 : Blo 527800 531383 := bstep (se 1 (by rfl) ⟨398537, by rfl⟩ : syracuseStep 531383 = 797075) B797075
theorem B793547 : Blo 527800 793547 := bstep (se 1 (by rfl) ⟨595160, by rfl⟩ : syracuseStep 793547 = 1190321) B1190321
theorem B531403 : Blo 527800 531403 := bstep (se 1 (by rfl) ⟨398552, by rfl⟩ : syracuseStep 531403 = 797105) B797105
theorem B793559 : Blo 527800 793559 := bstep (se 1 (by rfl) ⟨595169, by rfl⟩ : syracuseStep 793559 = 1190339) B1190339
theorem B531415 : Blo 527800 531415 := bstep (se 1 (by rfl) ⟨398561, by rfl⟩ : syracuseStep 531415 = 797123) B797123
theorem B2268125 : Blo 527800 2268125 := bstep (se 3 (by rfl) ⟨425273, by rfl⟩ : syracuseStep 2268125 = 850547) B850547
theorem B531435 : Blo 527800 531435 := bstep (se 1 (by rfl) ⟨398576, by rfl⟩ : syracuseStep 531435 = 797153) B797153
theorem B596983 : Blo 527800 596983 := bstep (se 1 (by rfl) ⟨447737, by rfl⟩ : syracuseStep 596983 = 895475) B895475
theorem B531447 : Blo 527800 531447 := bstep (se 1 (by rfl) ⟨398585, by rfl⟩ : syracuseStep 531447 = 797171) B797171
theorem B2038787 : Blo 527800 2038787 := bstep (se 1 (by rfl) ⟨1529090, by rfl⟩ : syracuseStep 2038787 = 3058181) B3058181
theorem B531467 : Blo 527800 531467 := bstep (se 1 (by rfl) ⟨398600, by rfl⟩ : syracuseStep 531467 = 797201) B797201
theorem B531479 : Blo 527800 531479 := bstep (se 1 (by rfl) ⟨398609, by rfl⟩ : syracuseStep 531479 = 797219) B797219
theorem B793625 : Blo 527800 793625 := bstep (se 2 (by rfl) ⟨297609, by rfl⟩ : syracuseStep 793625 = 595219) B595219
theorem B531499 : Blo 527800 531499 := bstep (se 1 (by rfl) ⟨398624, by rfl⟩ : syracuseStep 531499 = 797249) B797249
theorem B531511 : Blo 527800 531511 := bstep (se 1 (by rfl) ⟨398633, by rfl⟩ : syracuseStep 531511 = 797267) B797267
theorem B531531 : Blo 527800 531531 := bstep (se 1 (by rfl) ⟨398648, by rfl⟩ : syracuseStep 531531 = 797297) B797297
theorem B531543 : Blo 527800 531543 := bstep (se 1 (by rfl) ⟨398657, by rfl⟩ : syracuseStep 531543 = 797315) B797315
theorem B531563 : Blo 527800 531563 := bstep (se 1 (by rfl) ⟨398672, by rfl⟩ : syracuseStep 531563 = 797345) B797345
theorem B531575 : Blo 527800 531575 := bstep (se 1 (by rfl) ⟨398681, by rfl⟩ : syracuseStep 531575 = 797363) B797363
theorem B2006147 : Blo 527800 2006147 := bstep (se 1 (by rfl) ⟨1504610, by rfl⟩ : syracuseStep 2006147 = 3009221) B3009221
theorem B793739 : Blo 527800 793739 := bstep (se 1 (by rfl) ⟨595304, by rfl⟩ : syracuseStep 793739 = 1190609) B1190609
theorem B531595 : Blo 527800 531595 := bstep (se 1 (by rfl) ⟨398696, by rfl⟩ : syracuseStep 531595 = 797393) B797393
theorem B793751 : Blo 527800 793751 := bstep (se 1 (by rfl) ⟨595313, by rfl⟩ : syracuseStep 793751 = 1190627) B1190627
theorem B531607 : Blo 527800 531607 := bstep (se 1 (by rfl) ⟨398705, by rfl⟩ : syracuseStep 531607 = 797411) B797411
theorem B597163 : Blo 527800 597163 := bstep (se 1 (by rfl) ⟨447872, by rfl⟩ : syracuseStep 597163 = 895745) B895745
theorem B531627 : Blo 527800 531627 := bstep (se 1 (by rfl) ⟨398720, by rfl⟩ : syracuseStep 531627 = 797441) B797441
theorem B531639 : Blo 527800 531639 := bstep (se 1 (by rfl) ⟨398729, by rfl⟩ : syracuseStep 531639 = 797459) B797459
theorem B531659 : Blo 527800 531659 := bstep (se 1 (by rfl) ⟨398744, by rfl⟩ : syracuseStep 531659 = 797489) B797489
theorem B531671 : Blo 527800 531671 := bstep (se 1 (by rfl) ⟨398753, by rfl⟩ : syracuseStep 531671 = 797507) B797507
theorem B793817 : Blo 527800 793817 := bstep (se 2 (by rfl) ⟨297681, by rfl⟩ : syracuseStep 793817 = 595363) B595363
theorem B531691 : Blo 527800 531691 := bstep (se 1 (by rfl) ⟨398768, by rfl⟩ : syracuseStep 531691 = 797537) B797537
theorem B531703 : Blo 527800 531703 := bstep (se 1 (by rfl) ⟨398777, by rfl⟩ : syracuseStep 531703 = 797555) B797555
theorem B531723 : Blo 527800 531723 := bstep (se 1 (by rfl) ⟨398792, by rfl⟩ : syracuseStep 531723 = 797585) B797585
theorem B597271 : Blo 527800 597271 := bstep (se 1 (by rfl) ⟨447953, by rfl⟩ : syracuseStep 597271 = 895907) B895907
theorem B531735 : Blo 527800 531735 := bstep (se 1 (by rfl) ⟨398801, by rfl⟩ : syracuseStep 531735 = 797603) B797603
theorem B531755 : Blo 527800 531755 := bstep (se 1 (by rfl) ⟨398816, by rfl⟩ : syracuseStep 531755 = 797633) B797633
theorem B531767 : Blo 527800 531767 := bstep (se 1 (by rfl) ⟨398825, by rfl⟩ : syracuseStep 531767 = 797651) B797651
theorem B892235 : Blo 527800 892235 := bstep (se 1 (by rfl) ⟨669176, by rfl⟩ : syracuseStep 892235 = 1338353) B1338353
theorem B793931 : Blo 527800 793931 := bstep (se 1 (by rfl) ⟨595448, by rfl⟩ : syracuseStep 793931 = 1190897) B1190897
theorem B531787 : Blo 527800 531787 := bstep (se 1 (by rfl) ⟨398840, by rfl⟩ : syracuseStep 531787 = 797681) B797681
theorem B793943 : Blo 527800 793943 := bstep (se 1 (by rfl) ⟨595457, by rfl⟩ : syracuseStep 793943 = 1190915) B1190915
theorem B531799 : Blo 527800 531799 := bstep (se 1 (by rfl) ⟨398849, by rfl⟩ : syracuseStep 531799 = 797699) B797699
theorem B794009 : Blo 527800 794009 := bstep (se 2 (by rfl) ⟨297753, by rfl⟩ : syracuseStep 794009 = 595507) B595507
theorem B957889 : Blo 527800 957889 := bstep (se 2 (by rfl) ⟨359208, by rfl⟩ : syracuseStep 957889 = 718417) B718417
theorem B892363 : Blo 527800 892363 := bstep (se 1 (by rfl) ⟨669272, by rfl⟩ : syracuseStep 892363 = 1338545) B1338545
theorem B597451 : Blo 527800 597451 := bstep (se 1 (by rfl) ⟨448088, by rfl⟩ : syracuseStep 597451 = 896177) B896177
theorem B794123 : Blo 527800 794123 := bstep (se 1 (by rfl) ⟨595592, by rfl⟩ : syracuseStep 794123 = 1191185) B1191185
theorem B794135 : Blo 527800 794135 := bstep (se 1 (by rfl) ⟨595601, by rfl⟩ : syracuseStep 794135 = 1191203) B1191203
theorem B597559 : Blo 527800 597559 := bstep (se 1 (by rfl) ⟨448169, by rfl⟩ : syracuseStep 597559 = 896339) B896339
theorem B2006603 : Blo 527800 2006603 := bstep (se 1 (by rfl) ⟨1504952, by rfl⟩ : syracuseStep 2006603 = 3009905) B3009905
theorem B564823 : Blo 527800 564823 := bstep (se 1 (by rfl) ⟨423617, by rfl⟩ : syracuseStep 564823 = 847235) B847235
theorem B892505 : Blo 527800 892505 := bstep (se 2 (by rfl) ⟨334689, by rfl⟩ : syracuseStep 892505 = 669379) B669379
theorem B794201 : Blo 527800 794201 := bstep (se 2 (by rfl) ⟨297825, by rfl⟩ : syracuseStep 794201 = 595651) B595651
theorem B1908355 : Blo 527800 1908355 := bstep (se 1 (by rfl) ⟨1431266, by rfl⟩ : syracuseStep 1908355 = 2862533) B2862533
theorem B1908397 : Blo 527800 1908397 := bstep (se 3 (by rfl) ⟨357824, by rfl⟩ : syracuseStep 1908397 = 715649) B715649
theorem B794315 : Blo 527800 794315 := bstep (se 1 (by rfl) ⟨595736, by rfl⟩ : syracuseStep 794315 = 1191473) B1191473
theorem B794327 : Blo 527800 794327 := bstep (se 1 (by rfl) ⟨595745, by rfl⟩ : syracuseStep 794327 = 1191491) B1191491
theorem B892633 : Blo 527800 892633 := bstep (se 2 (by rfl) ⟨334737, by rfl⟩ : syracuseStep 892633 = 669475) B669475
theorem B597739 : Blo 527800 597739 := bstep (se 1 (by rfl) ⟨448304, by rfl⟩ : syracuseStep 597739 = 896609) B896609
theorem B1187585 : Blo 527800 1187585 := bstep (se 2 (by rfl) ⟨445344, by rfl⟩ : syracuseStep 1187585 = 890689) B890689
theorem B2006801 : Blo 527800 2006801 := bstep (se 2 (by rfl) ⟨752550, by rfl⟩ : syracuseStep 2006801 = 1505101) B1505101
theorem B794393 : Blo 527800 794393 := bstep (se 2 (by rfl) ⟨297897, by rfl⟩ : syracuseStep 794393 = 595795) B595795
theorem B597847 : Blo 527800 597847 := bstep (se 1 (by rfl) ⟨448385, by rfl⟩ : syracuseStep 597847 = 896771) B896771
theorem B794507 : Blo 527800 794507 := bstep (se 1 (by rfl) ⟨595880, by rfl⟩ : syracuseStep 794507 = 1191761) B1191761
theorem B794519 : Blo 527800 794519 := bstep (se 1 (by rfl) ⟨595889, by rfl⟩ : syracuseStep 794519 = 1191779) B1191779
theorem B1187801 : Blo 527800 1187801 := bstep (se 2 (by rfl) ⟨445425, by rfl⟩ : syracuseStep 1187801 = 890851) B890851
theorem B794585 : Blo 527800 794585 := bstep (se 2 (by rfl) ⟨297969, by rfl⟩ : syracuseStep 794585 = 595939) B595939
theorem B598027 : Blo 527800 598027 := bstep (se 1 (by rfl) ⟨448520, by rfl⟩ : syracuseStep 598027 = 897041) B897041
theorem B1187891 : Blo 527800 1187891 := bstep (se 1 (by rfl) ⟨890918, by rfl⟩ : syracuseStep 1187891 = 1781837) B1781837
theorem B794699 : Blo 527800 794699 := bstep (se 1 (by rfl) ⟨596024, by rfl⟩ : syracuseStep 794699 = 1192049) B1192049
theorem B1187927 : Blo 527800 1187927 := bstep (se 1 (by rfl) ⟨890945, by rfl⟩ : syracuseStep 1187927 = 1781891) B1781891
theorem B794711 : Blo 527800 794711 := bstep (se 1 (by rfl) ⟨596033, by rfl⟩ : syracuseStep 794711 = 1192067) B1192067
theorem B598135 : Blo 527800 598135 := bstep (se 1 (by rfl) ⟨448601, by rfl⟩ : syracuseStep 598135 = 897203) B897203
theorem B794777 : Blo 527800 794777 := bstep (se 2 (by rfl) ⟨298041, by rfl⟩ : syracuseStep 794777 = 596083) B596083
theorem B3023027 : Blo 527800 3023027 := bstep (se 1 (by rfl) ⟨2267270, by rfl⟩ : syracuseStep 3023027 = 4534541) B4534541
theorem B1188107 : Blo 527800 1188107 := bstep (se 1 (by rfl) ⟨891080, by rfl⟩ : syracuseStep 1188107 = 1782161) B1782161
theorem B794891 : Blo 527800 794891 := bstep (se 1 (by rfl) ⟨596168, by rfl⟩ : syracuseStep 794891 = 1192337) B1192337
theorem B893207 : Blo 527800 893207 := bstep (se 1 (by rfl) ⟨669905, by rfl⟩ : syracuseStep 893207 = 1339811) B1339811
theorem B794903 : Blo 527800 794903 := bstep (se 1 (by rfl) ⟨596177, by rfl⟩ : syracuseStep 794903 = 1192355) B1192355
theorem B1188161 : Blo 527800 1188161 := bstep (se 2 (by rfl) ⟨445560, by rfl⟩ : syracuseStep 1188161 = 891121) B891121
theorem B565579 : Blo 527800 565579 := bstep (se 1 (by rfl) ⟨424184, by rfl⟩ : syracuseStep 565579 = 848369) B848369
theorem B860491 : Blo 527800 860491 := bstep (se 1 (by rfl) ⟨645368, by rfl⟩ : syracuseStep 860491 = 1290737) B1290737
theorem B794969 : Blo 527800 794969 := bstep (se 2 (by rfl) ⟨298113, by rfl⟩ : syracuseStep 794969 = 596227) B596227
theorem B893335 : Blo 527800 893335 := bstep (se 1 (by rfl) ⟨670001, by rfl⟩ : syracuseStep 893335 = 1340003) B1340003
theorem B795083 : Blo 527800 795083 := bstep (se 1 (by rfl) ⟨596312, by rfl⟩ : syracuseStep 795083 = 1192625) B1192625
theorem B795095 : Blo 527800 795095 := bstep (se 1 (by rfl) ⟨596321, by rfl⟩ : syracuseStep 795095 = 1192643) B1192643
theorem B2007575 : Blo 527800 2007575 := bstep (se 1 (by rfl) ⟨1505681, by rfl⟩ : syracuseStep 2007575 = 3011363) B3011363
theorem B1188377 : Blo 527800 1188377 := bstep (se 2 (by rfl) ⟨445641, by rfl⟩ : syracuseStep 1188377 = 891283) B891283
theorem B795161 : Blo 527800 795161 := bstep (se 2 (by rfl) ⟨298185, by rfl⟩ : syracuseStep 795161 = 596371) B596371
theorem B1188467 : Blo 527800 1188467 := bstep (se 1 (by rfl) ⟨891350, by rfl⟩ : syracuseStep 1188467 = 1782701) B1782701
theorem B795275 : Blo 527800 795275 := bstep (se 1 (by rfl) ⟨596456, by rfl⟩ : syracuseStep 795275 = 1192913) B1192913
theorem B1188503 : Blo 527800 1188503 := bstep (se 1 (by rfl) ⟨891377, by rfl⟩ : syracuseStep 1188503 = 1782755) B1782755
theorem B795287 : Blo 527800 795287 := bstep (se 1 (by rfl) ⟨596465, by rfl⟩ : syracuseStep 795287 = 1192931) B1192931
theorem B795353 : Blo 527800 795353 := bstep (se 2 (by rfl) ⟨298257, by rfl⟩ : syracuseStep 795353 = 596515) B596515
theorem B2007773 : Blo 527800 2007773 := bstep (se 3 (by rfl) ⟨376457, by rfl⟩ : syracuseStep 2007773 = 752915) B752915
theorem B4301585 : Blo 527800 4301585 := bstep (se 2 (by rfl) ⟨1613094, by rfl⟩ : syracuseStep 4301585 = 3226189) B3226189
theorem B1188683 : Blo 527800 1188683 := bstep (se 1 (by rfl) ⟨891512, by rfl⟩ : syracuseStep 1188683 = 1783025) B1783025
theorem B795467 : Blo 527800 795467 := bstep (se 1 (by rfl) ⟨596600, by rfl⟩ : syracuseStep 795467 = 1193201) B1193201
theorem B795479 : Blo 527800 795479 := bstep (se 1 (by rfl) ⟨596609, by rfl⟩ : syracuseStep 795479 = 1193219) B1193219
theorem B1188737 : Blo 527800 1188737 := bstep (se 2 (by rfl) ⟨445776, by rfl⟩ : syracuseStep 1188737 = 891553) B891553
theorem B795545 : Blo 527800 795545 := bstep (se 2 (by rfl) ⟨298329, by rfl⟩ : syracuseStep 795545 = 596659) B596659
theorem B4301747 : Blo 527800 4301747 := bstep (se 1 (by rfl) ⟨3226310, by rfl⟩ : syracuseStep 4301747 = 6452621) B6452621
theorem B893963 : Blo 527800 893963 := bstep (se 1 (by rfl) ⟨670472, by rfl⟩ : syracuseStep 893963 = 1340945) B1340945
theorem B795659 : Blo 527800 795659 := bstep (se 1 (by rfl) ⟨596744, by rfl⟩ : syracuseStep 795659 = 1193489) B1193489
theorem B795671 : Blo 527800 795671 := bstep (se 1 (by rfl) ⟨596753, by rfl⟩ : syracuseStep 795671 = 1193507) B1193507
theorem B1188953 : Blo 527800 1188953 := bstep (se 2 (by rfl) ⟨445857, by rfl⟩ : syracuseStep 1188953 = 891715) B891715
theorem B795737 : Blo 527800 795737 := bstep (se 2 (by rfl) ⟨298401, by rfl⟩ : syracuseStep 795737 = 596803) B596803
theorem B894091 : Blo 527800 894091 := bstep (se 1 (by rfl) ⟨670568, by rfl⟩ : syracuseStep 894091 = 1341137) B1341137
theorem B1189043 : Blo 527800 1189043 := bstep (se 1 (by rfl) ⟨891782, by rfl⟩ : syracuseStep 1189043 = 1783565) B1783565
theorem B795851 : Blo 527800 795851 := bstep (se 1 (by rfl) ⟨596888, by rfl⟩ : syracuseStep 795851 = 1193777) B1193777
theorem B1189079 : Blo 527800 1189079 := bstep (se 1 (by rfl) ⟨891809, by rfl⟩ : syracuseStep 1189079 = 1783619) B1783619
theorem B795863 : Blo 527800 795863 := bstep (se 1 (by rfl) ⟨596897, by rfl⟩ : syracuseStep 795863 = 1193795) B1193795
theorem B894233 : Blo 527800 894233 := bstep (se 2 (by rfl) ⟨335337, by rfl⟩ : syracuseStep 894233 = 670675) B670675
theorem B795929 : Blo 527800 795929 := bstep (se 2 (by rfl) ⟨298473, by rfl⟩ : syracuseStep 795929 = 596947) B596947
theorem B1189259 : Blo 527800 1189259 := bstep (se 1 (by rfl) ⟨891944, by rfl⟩ : syracuseStep 1189259 = 1783889) B1783889
theorem B796043 : Blo 527800 796043 := bstep (se 1 (by rfl) ⟨597032, by rfl⟩ : syracuseStep 796043 = 1194065) B1194065
theorem B796055 : Blo 527800 796055 := bstep (se 1 (by rfl) ⟨597041, by rfl⟩ : syracuseStep 796055 = 1194083) B1194083
theorem B894361 : Blo 527800 894361 := bstep (se 2 (by rfl) ⟨335385, by rfl⟩ : syracuseStep 894361 = 670771) B670771
theorem B1189313 : Blo 527800 1189313 := bstep (se 2 (by rfl) ⟨445992, by rfl⟩ : syracuseStep 1189313 = 891985) B891985
theorem B8955353 : Blo 527800 8955353 := bstep (se 2 (by rfl) ⟨3358257, by rfl⟩ : syracuseStep 8955353 = 6716515) B6716515
theorem B796121 : Blo 527800 796121 := bstep (se 2 (by rfl) ⟨298545, by rfl⟩ : syracuseStep 796121 = 597091) B597091
theorem B796235 : Blo 527800 796235 := bstep (se 1 (by rfl) ⟨597176, by rfl⟩ : syracuseStep 796235 = 1194353) B1194353
theorem B796247 : Blo 527800 796247 := bstep (se 1 (by rfl) ⟨597185, by rfl⟩ : syracuseStep 796247 = 1194371) B1194371
theorem B3024485 : Blo 527800 3024485 := bstep (se 4 (by rfl) ⟨283545, by rfl⟩ : syracuseStep 3024485 = 567091) B567091
theorem B1189529 : Blo 527800 1189529 := bstep (se 2 (by rfl) ⟨446073, by rfl⟩ : syracuseStep 1189529 = 892147) B892147
theorem B796313 : Blo 527800 796313 := bstep (se 2 (by rfl) ⟨298617, by rfl⟩ : syracuseStep 796313 = 597235) B597235
theorem B1189619 : Blo 527800 1189619 := bstep (se 1 (by rfl) ⟨892214, by rfl⟩ : syracuseStep 1189619 = 1784429) B1784429
theorem B796427 : Blo 527800 796427 := bstep (se 1 (by rfl) ⟨597320, by rfl⟩ : syracuseStep 796427 = 1194641) B1194641
theorem B1189655 : Blo 527800 1189655 := bstep (se 1 (by rfl) ⟨892241, by rfl⟩ : syracuseStep 1189655 = 1784483) B1784483
theorem B796439 : Blo 527800 796439 := bstep (se 1 (by rfl) ⟨597329, by rfl⟩ : syracuseStep 796439 = 1194659) B1194659
theorem B796505 : Blo 527800 796505 := bstep (se 2 (by rfl) ⟨298689, by rfl⟩ : syracuseStep 796505 = 597379) B597379
theorem B12887909 : Blo 527800 12887909 := bstep (se 4 (by rfl) ⟨1208241, by rfl⟩ : syracuseStep 12887909 = 2416483) B2416483
theorem B1189835 : Blo 527800 1189835 := bstep (se 1 (by rfl) ⟨892376, by rfl⟩ : syracuseStep 1189835 = 1784753) B1784753
theorem B796619 : Blo 527800 796619 := bstep (se 1 (by rfl) ⟨597464, by rfl⟩ : syracuseStep 796619 = 1194929) B1194929
theorem B894935 : Blo 527800 894935 := bstep (se 1 (by rfl) ⟨671201, by rfl⟩ : syracuseStep 894935 = 1342403) B1342403
theorem B796631 : Blo 527800 796631 := bstep (se 1 (by rfl) ⟨597473, by rfl⟩ : syracuseStep 796631 = 1194947) B1194947
theorem B1189889 : Blo 527800 1189889 := bstep (se 2 (by rfl) ⟨446208, by rfl⟩ : syracuseStep 1189889 = 892417) B892417
theorem B796697 : Blo 527800 796697 := bstep (se 2 (by rfl) ⟨298761, by rfl⟩ : syracuseStep 796697 = 597523) B597523
theorem B895063 : Blo 527800 895063 := bstep (se 1 (by rfl) ⟨671297, by rfl⟩ : syracuseStep 895063 = 1342595) B1342595
theorem B796811 : Blo 527800 796811 := bstep (se 1 (by rfl) ⟨597608, by rfl⟩ : syracuseStep 796811 = 1195217) B1195217
theorem B796823 : Blo 527800 796823 := bstep (se 1 (by rfl) ⟨597617, by rfl⟩ : syracuseStep 796823 = 1195235) B1195235
theorem B1616075 : Blo 527800 1616075 := bstep (se 1 (by rfl) ⟨1212056, by rfl⟩ : syracuseStep 1616075 = 2424113) B2424113
theorem B1190105 : Blo 527800 1190105 := bstep (se 2 (by rfl) ⟨446289, by rfl⟩ : syracuseStep 1190105 = 892579) B892579
theorem B796889 : Blo 527800 796889 := bstep (se 2 (by rfl) ⟨298833, by rfl⟩ : syracuseStep 796889 = 597667) B597667
theorem B567595 : Blo 527800 567595 := bstep (se 1 (by rfl) ⟨425696, by rfl⟩ : syracuseStep 567595 = 851393) B851393
theorem B1190195 : Blo 527800 1190195 := bstep (se 1 (by rfl) ⟨892646, by rfl⟩ : syracuseStep 1190195 = 1785293) B1785293
theorem B797003 : Blo 527800 797003 := bstep (se 1 (by rfl) ⟨597752, by rfl⟩ : syracuseStep 797003 = 1195505) B1195505
theorem B1190231 : Blo 527800 1190231 := bstep (se 1 (by rfl) ⟨892673, by rfl⟩ : syracuseStep 1190231 = 1785347) B1785347
theorem B797015 : Blo 527800 797015 := bstep (se 1 (by rfl) ⟨597761, by rfl⟩ : syracuseStep 797015 = 1195523) B1195523
theorem B797081 : Blo 527800 797081 := bstep (se 2 (by rfl) ⟨298905, by rfl⟩ : syracuseStep 797081 = 597811) B597811
theorem B1190411 : Blo 527800 1190411 := bstep (se 1 (by rfl) ⟨892808, by rfl⟩ : syracuseStep 1190411 = 1785617) B1785617
theorem B797195 : Blo 527800 797195 := bstep (se 1 (by rfl) ⟨597896, by rfl⟩ : syracuseStep 797195 = 1195793) B1195793
theorem B797207 : Blo 527800 797207 := bstep (se 1 (by rfl) ⟨597905, by rfl⟩ : syracuseStep 797207 = 1195811) B1195811
theorem B1190465 : Blo 527800 1190465 := bstep (se 2 (by rfl) ⟨446424, by rfl⟩ : syracuseStep 1190465 = 892849) B892849
theorem B797273 : Blo 527800 797273 := bstep (se 2 (by rfl) ⟨298977, by rfl⟩ : syracuseStep 797273 = 597955) B597955
theorem B2009731 : Blo 527800 2009731 := bstep (se 1 (by rfl) ⟨1507298, by rfl⟩ : syracuseStep 2009731 = 3014597) B3014597
theorem B895691 : Blo 527800 895691 := bstep (se 1 (by rfl) ⟨671768, by rfl⟩ : syracuseStep 895691 = 1343537) B1343537
theorem B797387 : Blo 527800 797387 := bstep (se 1 (by rfl) ⟨598040, by rfl⟩ : syracuseStep 797387 = 1196081) B1196081
theorem B797399 : Blo 527800 797399 := bstep (se 1 (by rfl) ⟨598049, by rfl⟩ : syracuseStep 797399 = 1196099) B1196099
theorem B2140931 : Blo 527800 2140931 := bstep (se 1 (by rfl) ⟨1605698, by rfl⟩ : syracuseStep 2140931 = 3211397) B3211397
theorem B1190681 : Blo 527800 1190681 := bstep (se 2 (by rfl) ⟨446505, by rfl⟩ : syracuseStep 1190681 = 893011) B893011
theorem B797465 : Blo 527800 797465 := bstep (se 2 (by rfl) ⟨299049, by rfl⟩ : syracuseStep 797465 = 598099) B598099
theorem B3222317 : Blo 527800 3222317 := bstep (se 3 (by rfl) ⟨604184, by rfl⟩ : syracuseStep 3222317 = 1208369) B1208369
theorem B895819 : Blo 527800 895819 := bstep (se 1 (by rfl) ⟨671864, by rfl⟩ : syracuseStep 895819 = 1343729) B1343729
theorem B1190771 : Blo 527800 1190771 := bstep (se 1 (by rfl) ⟨893078, by rfl⟩ : syracuseStep 1190771 = 1786157) B1786157
theorem B797579 : Blo 527800 797579 := bstep (se 1 (by rfl) ⟨598184, by rfl⟩ : syracuseStep 797579 = 1196369) B1196369
theorem B1190807 : Blo 527800 1190807 := bstep (se 1 (by rfl) ⟨893105, by rfl⟩ : syracuseStep 1190807 = 1786211) B1786211
theorem B1420183 : Blo 527800 1420183 := bstep (se 1 (by rfl) ⟨1065137, by rfl⟩ : syracuseStep 1420183 = 2130275) B2130275
theorem B797591 : Blo 527800 797591 := bstep (se 1 (by rfl) ⟨598193, by rfl⟩ : syracuseStep 797591 = 1196387) B1196387
theorem B2010035 : Blo 527800 2010035 := bstep (se 1 (by rfl) ⟨1507526, by rfl⟩ : syracuseStep 2010035 = 3015053) B3015053
theorem B895961 : Blo 527800 895961 := bstep (se 2 (by rfl) ⟨335985, by rfl⟩ : syracuseStep 895961 = 671971) B671971
theorem B797657 : Blo 527800 797657 := bstep (se 2 (by rfl) ⟨299121, by rfl⟩ : syracuseStep 797657 = 598243) B598243
theorem B1190987 : Blo 527800 1190987 := bstep (se 1 (by rfl) ⟨893240, by rfl⟩ : syracuseStep 1190987 = 1786481) B1786481
theorem B896089 : Blo 527800 896089 := bstep (se 2 (by rfl) ⟨336033, by rfl⟩ : syracuseStep 896089 = 672067) B672067
theorem B1191041 : Blo 527800 1191041 := bstep (se 2 (by rfl) ⟨446640, by rfl⟩ : syracuseStep 1191041 = 893281) B893281
theorem B1191257 : Blo 527800 1191257 := bstep (se 2 (by rfl) ⟨446721, by rfl⟩ : syracuseStep 1191257 = 893443) B893443
theorem B1191347 : Blo 527800 1191347 := bstep (se 1 (by rfl) ⟨893510, by rfl⟩ : syracuseStep 1191347 = 1787021) B1787021
theorem B1191383 : Blo 527800 1191383 := bstep (se 1 (by rfl) ⟨893537, by rfl⟩ : syracuseStep 1191383 = 1787075) B1787075
theorem B31075811 : Blo 527800 31075811 := bstep (se 1 (by rfl) ⟨23306858, by rfl⟩ : syracuseStep 31075811 = 46613717) B46613717
theorem B2010689 : Blo 527800 2010689 := bstep (se 2 (by rfl) ⟨754008, by rfl⟩ : syracuseStep 2010689 = 1508017) B1508017
theorem B1191563 : Blo 527800 1191563 := bstep (se 1 (by rfl) ⟨893672, by rfl⟩ : syracuseStep 1191563 = 1787345) B1787345
theorem B896663 : Blo 527800 896663 := bstep (se 1 (by rfl) ⟨672497, by rfl⟩ : syracuseStep 896663 = 1344995) B1344995
theorem B1191617 : Blo 527800 1191617 := bstep (se 2 (by rfl) ⟨446856, by rfl⟩ : syracuseStep 1191617 = 893713) B893713
theorem B896791 : Blo 527800 896791 := bstep (se 1 (by rfl) ⟨672593, by rfl⟩ : syracuseStep 896791 = 1345187) B1345187
theorem B1191833 : Blo 527800 1191833 := bstep (se 2 (by rfl) ⟨446937, by rfl⟩ : syracuseStep 1191833 = 893875) B893875
theorem B1191923 : Blo 527800 1191923 := bstep (se 1 (by rfl) ⟨893942, by rfl⟩ : syracuseStep 1191923 = 1787885) B1787885
theorem B1781783 : Blo 527800 1781783 := bstep (se 1 (by rfl) ⟨1336337, by rfl⟩ : syracuseStep 1781783 = 2672675) B2672675
theorem B1191959 : Blo 527800 1191959 := bstep (se 1 (by rfl) ⟨893969, by rfl⟩ : syracuseStep 1191959 = 1787939) B1787939
theorem B1192139 : Blo 527800 1192139 := bstep (se 1 (by rfl) ⟨894104, by rfl⟩ : syracuseStep 1192139 = 1788209) B1788209
theorem B1192193 : Blo 527800 1192193 := bstep (se 2 (by rfl) ⟨447072, by rfl⟩ : syracuseStep 1192193 = 894145) B894145
theorem B1192409 : Blo 527800 1192409 := bstep (se 2 (by rfl) ⟨447153, by rfl⟩ : syracuseStep 1192409 = 894307) B894307
theorem B1782323 : Blo 527800 1782323 := bstep (se 1 (by rfl) ⟨1336742, by rfl⟩ : syracuseStep 1782323 = 2673485) B2673485
theorem B1192499 : Blo 527800 1192499 := bstep (se 1 (by rfl) ⟨894374, by rfl⟩ : syracuseStep 1192499 = 1788749) B1788749
theorem B1192535 : Blo 527800 1192535 := bstep (se 1 (by rfl) ⟨894401, by rfl⟩ : syracuseStep 1192535 = 1788803) B1788803
theorem B1192715 : Blo 527800 1192715 := bstep (se 1 (by rfl) ⟨894536, by rfl⟩ : syracuseStep 1192715 = 1789073) B1789073
theorem B635671 : Blo 527800 635671 := bstep (se 1 (by rfl) ⟨476753, by rfl⟩ : syracuseStep 635671 = 953507) B953507
theorem B2143021 : Blo 527800 2143021 := bstep (se 3 (by rfl) ⟨401816, by rfl⟩ : syracuseStep 2143021 = 803633) B803633
theorem B2011949 : Blo 527800 2011949 := bstep (se 3 (by rfl) ⟨377240, by rfl⟩ : syracuseStep 2011949 = 754481) B754481
theorem B1782593 : Blo 527800 1782593 := bstep (se 2 (by rfl) ⟨668472, by rfl⟩ : syracuseStep 1782593 = 1336945) B1336945
theorem B1192769 : Blo 527800 1192769 := bstep (se 2 (by rfl) ⟨447288, by rfl⟩ : syracuseStep 1192769 = 894577) B894577
theorem B2011979 : Blo 527800 2011979 := bstep (se 1 (by rfl) ⟨1508984, by rfl⟩ : syracuseStep 2011979 = 3017969) B3017969
theorem B668503 : Blo 527800 668503 := bstep (se 1 (by rfl) ⟨501377, by rfl⟩ : syracuseStep 668503 = 1002755) B1002755
theorem B1127297 : Blo 527800 1127297 := bstep (se 2 (by rfl) ⟨422736, by rfl⟩ : syracuseStep 1127297 = 845473) B845473
theorem B2175947 : Blo 527800 2175947 := bstep (se 1 (by rfl) ⟨1631960, by rfl⟩ : syracuseStep 2175947 = 3263921) B3263921
theorem B4010957 : Blo 527800 4010957 := bstep (se 3 (by rfl) ⟨752054, by rfl⟩ : syracuseStep 4010957 = 1504109) B1504109
theorem B1192985 : Blo 527800 1192985 := bstep (se 2 (by rfl) ⟨447369, by rfl⟩ : syracuseStep 1192985 = 894739) B894739
theorem B1193075 : Blo 527800 1193075 := bstep (se 1 (by rfl) ⟨894806, by rfl⟩ : syracuseStep 1193075 = 1789613) B1789613
theorem B1193111 : Blo 527800 1193111 := bstep (se 1 (by rfl) ⟨894833, by rfl⟩ : syracuseStep 1193111 = 1789667) B1789667
theorem B3814721 : Blo 527800 3814721 := bstep (se 2 (by rfl) ⟨1430520, by rfl⟩ : syracuseStep 3814721 = 2861041) B2861041
theorem B1193291 : Blo 527800 1193291 := bstep (se 1 (by rfl) ⟨894968, by rfl⟩ : syracuseStep 1193291 = 1789937) B1789937
theorem B1783133 : Blo 527800 1783133 := bstep (se 3 (by rfl) ⟨334337, by rfl⟩ : syracuseStep 1783133 = 668675) B668675
theorem B1193345 : Blo 527800 1193345 := bstep (se 2 (by rfl) ⟨447504, by rfl⟩ : syracuseStep 1193345 = 895009) B895009
theorem B4011443 : Blo 527800 4011443 := bstep (se 1 (by rfl) ⟨3008582, by rfl⟩ : syracuseStep 4011443 = 6017165) B6017165
theorem B2143705 : Blo 527800 2143705 := bstep (se 2 (by rfl) ⟨803889, by rfl⟩ : syracuseStep 2143705 = 1607779) B1607779
theorem B1357273 : Blo 527800 1357273 := bstep (se 2 (by rfl) ⟨508977, by rfl⟩ : syracuseStep 1357273 = 1017955) B1017955
theorem B2012633 : Blo 527800 2012633 := bstep (se 2 (by rfl) ⟨754737, by rfl⟩ : syracuseStep 2012633 = 1509475) B1509475
theorem B1193561 : Blo 527800 1193561 := bstep (se 2 (by rfl) ⟨447585, by rfl⟩ : syracuseStep 1193561 = 895171) B895171
theorem B669323 : Blo 527800 669323 := bstep (se 1 (by rfl) ⟨501992, by rfl⟩ : syracuseStep 669323 = 1003985) B1003985
theorem B1193651 : Blo 527800 1193651 := bstep (se 1 (by rfl) ⟨895238, by rfl⟩ : syracuseStep 1193651 = 1790477) B1790477
theorem B1193687 : Blo 527800 1193687 := bstep (se 1 (by rfl) ⟨895265, by rfl⟩ : syracuseStep 1193687 = 1790531) B1790531
theorem B2012951 : Blo 527800 2012951 := bstep (se 1 (by rfl) ⟨1509713, by rfl⟩ : syracuseStep 2012951 = 3019427) B3019427
theorem B1193867 : Blo 527800 1193867 := bstep (se 1 (by rfl) ⟨895400, by rfl⟩ : syracuseStep 1193867 = 1790801) B1790801
theorem B1193921 : Blo 527800 1193921 := bstep (se 2 (by rfl) ⟨447720, by rfl⟩ : syracuseStep 1193921 = 895441) B895441
theorem B1194137 : Blo 527800 1194137 := bstep (se 2 (by rfl) ⟨447801, by rfl⟩ : syracuseStep 1194137 = 895603) B895603
theorem B1194227 : Blo 527800 1194227 := bstep (se 1 (by rfl) ⟨895670, by rfl⟩ : syracuseStep 1194227 = 1791341) B1791341
theorem B1194263 : Blo 527800 1194263 := bstep (se 1 (by rfl) ⟨895697, by rfl⟩ : syracuseStep 1194263 = 1791395) B1791395
theorem B670027 : Blo 527800 670027 := bstep (se 1 (by rfl) ⟨502520, by rfl⟩ : syracuseStep 670027 = 1005041) B1005041
theorem B1816921 : Blo 527800 1816921 := bstep (se 2 (by rfl) ⟨681345, by rfl⟩ : syracuseStep 1816921 = 1362691) B1362691
theorem B2013619 : Blo 527800 2013619 := bstep (se 1 (by rfl) ⟨1510214, by rfl⟩ : syracuseStep 2013619 = 3020429) B3020429
theorem B1784267 : Blo 527800 1784267 := bstep (se 1 (by rfl) ⟨1338200, by rfl⟩ : syracuseStep 1784267 = 2676401) B2676401
theorem B1194443 : Blo 527800 1194443 := bstep (se 1 (by rfl) ⟨895832, by rfl⟩ : syracuseStep 1194443 = 1791665) B1791665
theorem B1194497 : Blo 527800 1194497 := bstep (se 2 (by rfl) ⟨447936, by rfl⟩ : syracuseStep 1194497 = 895873) B895873
theorem B1128971 : Blo 527800 1128971 := bstep (se 1 (by rfl) ⟨846728, by rfl⟩ : syracuseStep 1128971 = 1693457) B1693457
theorem B2243089 : Blo 527800 2243089 := bstep (se 2 (by rfl) ⟨841158, by rfl⟩ : syracuseStep 2243089 = 1682317) B1682317
theorem B670295 : Blo 527800 670295 := bstep (se 1 (by rfl) ⟨502721, by rfl⟩ : syracuseStep 670295 = 1005443) B1005443
theorem B637579 : Blo 527800 637579 := bstep (se 1 (by rfl) ⟨478184, by rfl⟩ : syracuseStep 637579 = 956369) B956369
theorem B1784537 : Blo 527800 1784537 := bstep (se 2 (by rfl) ⟨669201, by rfl⟩ : syracuseStep 1784537 = 1338403) B1338403
theorem B1194713 : Blo 527800 1194713 := bstep (se 2 (by rfl) ⟨448017, by rfl⟩ : syracuseStep 1194713 = 896035) B896035
theorem B1194803 : Blo 527800 1194803 := bstep (se 1 (by rfl) ⟨896102, by rfl⟩ : syracuseStep 1194803 = 1792205) B1792205
theorem B1260353 : Blo 527800 1260353 := bstep (se 2 (by rfl) ⟨472632, by rfl⟩ : syracuseStep 1260353 = 945265) B945265
theorem B1194839 : Blo 527800 1194839 := bstep (se 1 (by rfl) ⟨896129, by rfl⟩ : syracuseStep 1194839 = 1792259) B1792259
theorem B16169827 : Blo 527800 16169827 := bstep (se 1 (by rfl) ⟨12127370, by rfl⟩ : syracuseStep 16169827 = 24254741) B24254741
theorem B4012901 : Blo 527800 4012901 := bstep (se 4 (by rfl) ⟨376209, by rfl⟩ : syracuseStep 4012901 = 752419) B752419
theorem B4307843 : Blo 527800 4307843 := bstep (se 1 (by rfl) ⟨3230882, by rfl⟩ : syracuseStep 4307843 = 6461765) B6461765
theorem B1195019 : Blo 527800 1195019 := bstep (se 1 (by rfl) ⟨896264, by rfl⟩ : syracuseStep 1195019 = 1792529) B1792529
theorem B1195073 : Blo 527800 1195073 := bstep (se 2 (by rfl) ⟨448152, by rfl⟩ : syracuseStep 1195073 = 896305) B896305
theorem B1915979 : Blo 527800 1915979 := bstep (se 1 (by rfl) ⟨1436984, by rfl⟩ : syracuseStep 1915979 = 2873969) B2873969
theorem B2538647 : Blo 527800 2538647 := bstep (se 1 (by rfl) ⟨1903985, by rfl⟩ : syracuseStep 2538647 = 3807971) B3807971
theorem B670999 : Blo 527800 670999 := bstep (se 1 (by rfl) ⟨503249, by rfl⟩ : syracuseStep 670999 = 1006499) B1006499
theorem B1195289 : Blo 527800 1195289 := bstep (se 2 (by rfl) ⟨448233, by rfl⟩ : syracuseStep 1195289 = 896467) B896467
theorem B4013387 : Blo 527800 4013387 := bstep (se 1 (by rfl) ⟨3010040, by rfl⟩ : syracuseStep 4013387 = 6020081) B6020081
theorem B1195379 : Blo 527800 1195379 := bstep (se 1 (by rfl) ⟨896534, by rfl⟩ : syracuseStep 1195379 = 1793069) B1793069
theorem B1785239 : Blo 527800 1785239 := bstep (se 1 (by rfl) ⟨1338929, by rfl⟩ : syracuseStep 1785239 = 2677859) B2677859
theorem B1195415 : Blo 527800 1195415 := bstep (se 1 (by rfl) ⟨896561, by rfl⟩ : syracuseStep 1195415 = 1793123) B1793123
theorem B1129945 : Blo 527800 1129945 := bstep (se 2 (by rfl) ⟨423729, by rfl⟩ : syracuseStep 1129945 = 847459) B847459
theorem B3816965 : Blo 527800 3816965 := bstep (se 4 (by rfl) ⟨357840, by rfl⟩ : syracuseStep 3816965 = 715681) B715681
theorem B1195595 : Blo 527800 1195595 := bstep (se 1 (by rfl) ⟨896696, by rfl⟩ : syracuseStep 1195595 = 1793393) B1793393
theorem B1195649 : Blo 527800 1195649 := bstep (se 2 (by rfl) ⟨448368, by rfl⟩ : syracuseStep 1195649 = 896737) B896737
theorem B2014865 : Blo 527800 2014865 := bstep (se 2 (by rfl) ⟨755574, by rfl⟩ : syracuseStep 2014865 = 1511149) B1511149
theorem B1130201 : Blo 527800 1130201 := bstep (se 2 (by rfl) ⟨423825, by rfl⟩ : syracuseStep 1130201 = 847651) B847651
theorem B1195865 : Blo 527800 1195865 := bstep (se 2 (by rfl) ⟨448449, by rfl⟩ : syracuseStep 1195865 = 896899) B896899
theorem B1785779 : Blo 527800 1785779 := bstep (se 1 (by rfl) ⟨1339334, by rfl⟩ : syracuseStep 1785779 = 2678669) B2678669
theorem B1195955 : Blo 527800 1195955 := bstep (se 1 (by rfl) ⟨896966, by rfl⟩ : syracuseStep 1195955 = 1793933) B1793933
theorem B1195991 : Blo 527800 1195991 := bstep (se 1 (by rfl) ⟨896993, by rfl⟩ : syracuseStep 1195991 = 1793987) B1793987
theorem B2146265 : Blo 527800 2146265 := bstep (se 2 (by rfl) ⟨804849, by rfl⟩ : syracuseStep 2146265 = 1609699) B1609699
theorem B1818713 : Blo 527800 1818713 := bstep (se 2 (by rfl) ⟨682017, by rfl⟩ : syracuseStep 1818713 = 1364035) B1364035
theorem B1130611 : Blo 527800 1130611 := bstep (se 1 (by rfl) ⟨847958, by rfl⟩ : syracuseStep 1130611 = 1695917) B1695917
theorem B1196171 : Blo 527800 1196171 := bstep (se 1 (by rfl) ⟨897128, by rfl⟩ : syracuseStep 1196171 = 1794257) B1794257
theorem B1786049 : Blo 527800 1786049 := bstep (se 2 (by rfl) ⟨669768, by rfl⟩ : syracuseStep 1786049 = 1339537) B1339537
theorem B1196225 : Blo 527800 1196225 := bstep (se 2 (by rfl) ⟨448584, by rfl⟩ : syracuseStep 1196225 = 897169) B897169
theorem B2572505 : Blo 527800 2572505 := bstep (se 2 (by rfl) ⟨964689, by rfl⟩ : syracuseStep 2572505 = 1929379) B1929379
theorem B2015563 : Blo 527800 2015563 := bstep (se 1 (by rfl) ⟨1511672, by rfl⟩ : syracuseStep 2015563 = 3023345) B3023345
theorem B1196441 : Blo 527800 1196441 := bstep (se 2 (by rfl) ⟨448665, by rfl⟩ : syracuseStep 1196441 = 897331) B897331
theorem B1196531 : Blo 527800 1196531 := bstep (se 1 (by rfl) ⟨897398, by rfl⟩ : syracuseStep 1196531 = 1794797) B1794797
theorem B4538915 : Blo 527800 4538915 := bstep (se 1 (by rfl) ⟨3404186, by rfl⟩ : syracuseStep 4538915 = 6808373) B6808373
theorem B2015837 : Blo 527800 2015837 := bstep (se 3 (by rfl) ⟨377969, by rfl⟩ : syracuseStep 2015837 = 755939) B755939
theorem B1786589 : Blo 527800 1786589 := bstep (se 3 (by rfl) ⟨334985, by rfl⟩ : syracuseStep 1786589 = 669971) B669971
theorem B1524545 : Blo 527800 1524545 := bstep (se 2 (by rfl) ⟨571704, by rfl⟩ : syracuseStep 1524545 = 1143409) B1143409
theorem B1131329 : Blo 527800 1131329 := bstep (se 2 (by rfl) ⟨424248, by rfl⟩ : syracuseStep 1131329 = 848497) B848497
theorem B672715 : Blo 527800 672715 := bstep (se 1 (by rfl) ⟨504536, by rfl⟩ : syracuseStep 672715 = 1009073) B1009073
theorem B6177809 : Blo 527800 6177809 := bstep (se 2 (by rfl) ⟨2316678, by rfl⟩ : syracuseStep 6177809 = 4633357) B4633357
theorem B1131671 : Blo 527800 1131671 := bstep (se 1 (by rfl) ⟨848753, by rfl⟩ : syracuseStep 1131671 = 1697507) B1697507
theorem B4539665 : Blo 527800 4539665 := bstep (se 2 (by rfl) ⟨1702374, by rfl⟩ : syracuseStep 4539665 = 3404749) B3404749
theorem B2016535 : Blo 527800 2016535 := bstep (se 1 (by rfl) ⟨1512401, by rfl⟩ : syracuseStep 2016535 = 3024803) B3024803
theorem B1131841 : Blo 527800 1131841 := bstep (se 2 (by rfl) ⟨424440, by rfl⟩ : syracuseStep 1131841 = 848881) B848881
theorem B4343473 : Blo 527800 4343473 := bstep (se 2 (by rfl) ⟨1628802, by rfl⟩ : syracuseStep 4343473 = 3257605) B3257605
theorem B1787723 : Blo 527800 1787723 := bstep (se 1 (by rfl) ⟨1340792, by rfl⟩ : syracuseStep 1787723 = 2681585) B2681585
theorem B2017325 : Blo 527800 2017325 := bstep (se 3 (by rfl) ⟨378248, by rfl⟩ : syracuseStep 2017325 = 756497) B756497
theorem B1787993 : Blo 527800 1787993 := bstep (se 2 (by rfl) ⟨670497, by rfl⟩ : syracuseStep 1787993 = 1340995) B1340995
theorem B7620965 : Blo 527800 7620965 := bstep (se 4 (by rfl) ⟨714465, by rfl⟩ : syracuseStep 7620965 = 1428931) B1428931
theorem B1133003 : Blo 527800 1133003 := bstep (se 1 (by rfl) ⟨849752, by rfl⟩ : syracuseStep 1133003 = 1699505) B1699505
theorem B1002071 : Blo 527800 1002071 := bstep (se 1 (by rfl) ⟨751553, by rfl⟩ : syracuseStep 1002071 = 1503107) B1503107
theorem B4311731 : Blo 527800 4311731 := bstep (se 1 (by rfl) ⟨3233798, by rfl⟩ : syracuseStep 4311731 = 6467597) B6467597
theorem B1788695 : Blo 527800 1788695 := bstep (se 1 (by rfl) ⟨1341521, by rfl⟩ : syracuseStep 1788695 = 2683043) B2683043
theorem B7228277 : Blo 527800 7228277 := bstep (se 5 (by rfl) ⟨338825, by rfl⟩ : syracuseStep 7228277 = 677651) B677651
theorem B1428445 : Blo 527800 1428445 := bstep (se 3 (by rfl) ⟨267833, by rfl⟩ : syracuseStep 1428445 = 535667) B535667
theorem B1002611 : Blo 527800 1002611 := bstep (se 1 (by rfl) ⟨751958, by rfl⟩ : syracuseStep 1002611 = 1503917) B1503917
theorem B1133747 : Blo 527800 1133747 := bstep (se 1 (by rfl) ⟨850310, by rfl⟩ : syracuseStep 1133747 = 1700621) B1700621
theorem B3624209 : Blo 527800 3624209 := bstep (se 2 (by rfl) ⟨1359078, by rfl⟩ : syracuseStep 3624209 = 2718157) B2718157
theorem B1789235 : Blo 527800 1789235 := bstep (se 1 (by rfl) ⟨1341926, by rfl⟩ : syracuseStep 1789235 = 2683853) B2683853
theorem B1035659 : Blo 527800 1035659 := bstep (se 1 (by rfl) ⟨776744, by rfl⟩ : syracuseStep 1035659 = 1553489) B1553489
theorem B2018753 : Blo 527800 2018753 := bstep (se 2 (by rfl) ⟨757032, by rfl⟩ : syracuseStep 2018753 = 1514065) B1514065
theorem B6049241 : Blo 527800 6049241 := bstep (se 2 (by rfl) ⟨2268465, by rfl⟩ : syracuseStep 6049241 = 4536931) B4536931
theorem B1691201 : Blo 527800 1691201 := bstep (se 2 (by rfl) ⟨634200, by rfl⟩ : syracuseStep 1691201 = 1268401) B1268401
theorem B1789505 : Blo 527800 1789505 := bstep (se 2 (by rfl) ⟨671064, by rfl⟩ : syracuseStep 1789505 = 1342129) B1342129
theorem B1003097 : Blo 527800 1003097 := bstep (se 2 (by rfl) ⟨376161, by rfl⟩ : syracuseStep 1003097 = 752323) B752323
theorem B18665315 : Blo 527800 18665315 := bstep (se 1 (by rfl) ⟨13998986, by rfl⟩ : syracuseStep 18665315 = 27997973) B27997973
theorem B905177 : Blo 527800 905177 := bstep (se 2 (by rfl) ⟨339441, by rfl⟩ : syracuseStep 905177 = 678883) B678883
theorem B1134643 : Blo 527800 1134643 := bstep (se 1 (by rfl) ⟨850982, by rfl⟩ : syracuseStep 1134643 = 1701965) B1701965
theorem B1691713 : Blo 527800 1691713 := bstep (se 2 (by rfl) ⟨634392, by rfl⟩ : syracuseStep 1691713 = 1268785) B1268785
theorem B2674781 : Blo 527800 2674781 := bstep (se 3 (by rfl) ⟨501521, by rfl⟩ : syracuseStep 2674781 = 1003043) B1003043
theorem B1790045 : Blo 527800 1790045 := bstep (se 3 (by rfl) ⟨335633, by rfl⟩ : syracuseStep 1790045 = 671267) B671267
theorem B4542641 : Blo 527800 4542641 := bstep (se 2 (by rfl) ⟨1703490, by rfl⟩ : syracuseStep 4542641 = 3406981) B3406981
theorem B1429721 : Blo 527800 1429721 := bstep (se 2 (by rfl) ⟨536145, by rfl⟩ : syracuseStep 1429721 = 1072291) B1072291
theorem B4837637 : Blo 527800 4837637 := bstep (se 4 (by rfl) ⟨453528, by rfl⟩ : syracuseStep 4837637 = 907057) B907057
theorem B610763 : Blo 527800 610763 := bstep (se 1 (by rfl) ⟨458072, by rfl⟩ : syracuseStep 610763 = 916145) B916145
theorem B4018733 : Blo 527800 4018733 := bstep (se 3 (by rfl) ⟨753512, by rfl⟩ : syracuseStep 4018733 = 1507025) B1507025
theorem B1004555 : Blo 527800 1004555 := bstep (se 1 (by rfl) ⟨753416, by rfl⟩ : syracuseStep 1004555 = 1506833) B1506833
theorem B3396653 : Blo 527800 3396653 := bstep (se 3 (by rfl) ⟨636872, by rfl⟩ : syracuseStep 3396653 = 1273745) B1273745
theorem B1135703 : Blo 527800 1135703 := bstep (se 1 (by rfl) ⟨851777, by rfl⟩ : syracuseStep 1135703 = 1703555) B1703555
theorem B1004737 : Blo 527800 1004737 := bstep (se 2 (by rfl) ⟨376776, by rfl⟩ : syracuseStep 1004737 = 753553) B753553
theorem B1791179 : Blo 527800 1791179 := bstep (se 1 (by rfl) ⟨1343384, by rfl⟩ : syracuseStep 1791179 = 2686769) B2686769
theorem B1692893 : Blo 527800 1692893 := bstep (se 3 (by rfl) ⟨317417, by rfl⟩ : syracuseStep 1692893 = 634835) B634835
theorem B3429697 : Blo 527800 3429697 := bstep (se 2 (by rfl) ⟨1286136, by rfl⟩ : syracuseStep 3429697 = 2572273) B2572273
theorem B1791449 : Blo 527800 1791449 := bstep (se 2 (by rfl) ⟨671793, by rfl⟩ : syracuseStep 1791449 = 1343587) B1343587
theorem B1005185 : Blo 527800 1005185 := bstep (se 2 (by rfl) ⟨376944, by rfl⟩ : syracuseStep 1005185 = 753889) B753889
theorem B1005527 : Blo 527800 1005527 := bstep (se 1 (by rfl) ⟨754145, by rfl⟩ : syracuseStep 1005527 = 1508291) B1508291
theorem B1792151 : Blo 527800 1792151 := bstep (se 1 (by rfl) ⟨1344113, by rfl⟩ : syracuseStep 1792151 = 2688227) B2688227
theorem B2676887 : Blo 527800 2676887 := bstep (se 1 (by rfl) ⟨2007665, by rfl⟩ : syracuseStep 2676887 = 4015331) B4015331
theorem B2709683 : Blo 527800 2709683 := bstep (se 1 (by rfl) ⟨2032262, by rfl⟩ : syracuseStep 2709683 = 4064525) B4064525
theorem B907865 : Blo 527800 907865 := bstep (se 2 (by rfl) ⟨340449, by rfl⟩ : syracuseStep 907865 = 680899) B680899
theorem B1006195 : Blo 527800 1006195 := bstep (se 1 (by rfl) ⟨754646, by rfl⟩ : syracuseStep 1006195 = 1509293) B1509293
theorem B1792691 : Blo 527800 1792691 := bstep (se 1 (by rfl) ⟨1344518, by rfl⟩ : syracuseStep 1792691 = 2689037) B2689037
theorem B5102513 : Blo 527800 5102513 := bstep (se 2 (by rfl) ⟨1913442, by rfl⟩ : syracuseStep 5102513 = 3826885) B3826885
theorem B1792961 : Blo 527800 1792961 := bstep (se 2 (by rfl) ⟨672360, by rfl⟩ : syracuseStep 1792961 = 1344721) B1344721
theorem B1006643 : Blo 527800 1006643 := bstep (se 1 (by rfl) ⟨754982, by rfl⟩ : syracuseStep 1006643 = 1509965) B1509965
theorem B1006681 : Blo 527800 1006681 := bstep (se 2 (by rfl) ⟨377505, by rfl⟩ : syracuseStep 1006681 = 755011) B755011
theorem B1531097 : Blo 527800 1531097 := bstep (se 2 (by rfl) ⟨574161, by rfl⟩ : syracuseStep 1531097 = 1148323) B1148323
theorem B7232813 : Blo 527800 7232813 := bstep (se 3 (by rfl) ⟨1356152, by rfl⟩ : syracuseStep 7232813 = 2712305) B2712305
theorem B2907571 : Blo 527800 2907571 := bstep (se 1 (by rfl) ⟨2180678, by rfl⟩ : syracuseStep 2907571 = 4361357) B4361357
theorem B1269209 : Blo 527800 1269209 := bstep (se 2 (by rfl) ⟨475953, by rfl⟩ : syracuseStep 1269209 = 951907) B951907
theorem B1793501 : Blo 527800 1793501 := bstep (se 3 (by rfl) ⟨336281, by rfl⟩ : syracuseStep 1793501 = 672563) B672563
theorem B2448899 : Blo 527800 2448899 := bstep (se 1 (by rfl) ⟨1836674, by rfl⟩ : syracuseStep 2448899 = 3673349) B3673349
theorem B1007129 : Blo 527800 1007129 := bstep (se 2 (by rfl) ⟨377673, by rfl⟩ : syracuseStep 1007129 = 755347) B755347
theorem B3825245 : Blo 527800 3825245 := bstep (se 3 (by rfl) ⟨717233, by rfl⟩ : syracuseStep 3825245 = 1434467) B1434467
theorem B3006557 : Blo 527800 3006557 := bstep (se 3 (by rfl) ⟨563729, by rfl⟩ : syracuseStep 3006557 = 1127459) B1127459
theorem B1007873 : Blo 527800 1007873 := bstep (se 2 (by rfl) ⟨377952, by rfl⟩ : syracuseStep 1007873 = 755905) B755905
theorem B4022621 : Blo 527800 4022621 := bstep (se 3 (by rfl) ⟨754241, by rfl⟩ : syracuseStep 4022621 = 1508483) B1508483
theorem B1073587 : Blo 527800 1073587 := bstep (se 1 (by rfl) ⟨805190, by rfl⟩ : syracuseStep 1073587 = 1610381) B1610381
theorem B1008139 : Blo 527800 1008139 := bstep (se 1 (by rfl) ⟨756104, by rfl⟩ : syracuseStep 1008139 = 1512209) B1512209
theorem B1794635 : Blo 527800 1794635 := bstep (se 1 (by rfl) ⟨1345976, by rfl⟩ : syracuseStep 1794635 = 2691953) B2691953
theorem B1958489 : Blo 527800 1958489 := bstep (se 2 (by rfl) ⟨734433, by rfl⟩ : syracuseStep 1958489 = 1468867) B1468867
theorem B1336115 : Blo 527800 1336115 := bstep (se 1 (by rfl) ⟨1002086, by rfl⟩ : syracuseStep 1336115 = 2004173) B2004173
theorem B1434433 : Blo 527800 1434433 := bstep (se 2 (by rfl) ⟨537912, by rfl⟩ : syracuseStep 1434433 = 1075825) B1075825
theorem B3007307 : Blo 527800 3007307 := bstep (se 1 (by rfl) ⟨2255480, by rfl⟩ : syracuseStep 3007307 = 4510961) B4510961
theorem B1631069 : Blo 527800 1631069 := bstep (se 3 (by rfl) ⟨305825, by rfl⟩ : syracuseStep 1631069 = 611651) B611651
theorem B7725941 : Blo 527800 7725941 := bstep (se 5 (by rfl) ⟨362153, by rfl⟩ : syracuseStep 7725941 = 724307) B724307
theorem B2581379 : Blo 527800 2581379 := bstep (se 1 (by rfl) ⟨1936034, by rfl⟩ : syracuseStep 2581379 = 3872069) B3872069
theorem B1008587 : Blo 527800 1008587 := bstep (se 1 (by rfl) ⟨756440, by rfl⟩ : syracuseStep 1008587 = 1512881) B1512881
theorem B1336409 : Blo 527800 1336409 := bstep (se 2 (by rfl) ⟨501153, by rfl⟩ : syracuseStep 1336409 = 1002307) B1002307
theorem B1008769 : Blo 527800 1008769 := bstep (se 2 (by rfl) ⟨378288, by rfl⟩ : syracuseStep 1008769 = 756577) B756577
theorem B1009111 : Blo 527800 1009111 := bstep (se 1 (by rfl) ⟨756833, by rfl⟩ : syracuseStep 1009111 = 1513667) B1513667
theorem B2680451 : Blo 527800 2680451 := bstep (se 1 (by rfl) ⟨2010338, by rfl⟩ : syracuseStep 2680451 = 4020677) B4020677
theorem B1009331 : Blo 527800 1009331 := bstep (se 1 (by rfl) ⟨756998, by rfl⟩ : syracuseStep 1009331 = 1513997) B1513997
theorem B6776693 : Blo 527800 6776693 := bstep (se 5 (by rfl) ⟨317657, by rfl⟩ : syracuseStep 6776693 = 635315) B635315
theorem B1009559 : Blo 527800 1009559 := bstep (se 1 (by rfl) ⟨757169, by rfl⟩ : syracuseStep 1009559 = 1514339) B1514339
theorem B21718961 : Blo 527800 21718961 := bstep (se 2 (by rfl) ⟨8144610, by rfl⟩ : syracuseStep 21718961 = 16289221) B16289221
theorem B4516019 : Blo 527800 4516019 := bstep (se 1 (by rfl) ⟨3387014, by rfl⟩ : syracuseStep 4516019 = 6774029) B6774029
theorem B2713949 : Blo 527800 2713949 := bstep (se 3 (by rfl) ⟨508865, by rfl⟩ : syracuseStep 2713949 = 1017731) B1017731
theorem B3008947 : Blo 527800 3008947 := bstep (se 1 (by rfl) ⟨2256710, by rfl⟩ : syracuseStep 3008947 = 4513421) B4513421
theorem B4516397 : Blo 527800 4516397 := bstep (se 3 (by rfl) ⟨846824, by rfl⟩ : syracuseStep 4516397 = 1693649) B1693649
theorem B1338059 : Blo 527800 1338059 := bstep (se 1 (by rfl) ⟨1003544, by rfl⟩ : syracuseStep 1338059 = 2007089) B2007089
theorem B1436467 : Blo 527800 1436467 := bstep (se 1 (by rfl) ⟨1077350, by rfl⟩ : syracuseStep 1436467 = 2154701) B2154701
theorem B2255789 : Blo 527800 2255789 := bstep (se 3 (by rfl) ⟨422960, by rfl⟩ : syracuseStep 2255789 = 845921) B845921
theorem B1633241 : Blo 527800 1633241 := bstep (se 2 (by rfl) ⟨612465, by rfl⟩ : syracuseStep 1633241 = 1224931) B1224931
theorem B1698839 : Blo 527800 1698839 := bstep (se 1 (by rfl) ⟨1274129, by rfl⟩ : syracuseStep 1698839 = 2548259) B2548259
theorem B1699019 : Blo 527800 1699019 := bstep (se 1 (by rfl) ⟨1274264, by rfl⟩ : syracuseStep 1699019 = 2548529) B2548529
theorem B3403109 : Blo 527800 3403109 := bstep (se 4 (by rfl) ⟨319041, by rfl⟩ : syracuseStep 3403109 = 638083) B638083
theorem B1699289 : Blo 527800 1699289 := bstep (se 2 (by rfl) ⟨637233, by rfl⟩ : syracuseStep 1699289 = 1274467) B1274467
theorem B1339031 : Blo 527800 1339031 := bstep (se 1 (by rfl) ⟨1004273, by rfl⟩ : syracuseStep 1339031 = 2008547) B2008547
theorem B1273495 : Blo 527800 1273495 := bstep (se 1 (by rfl) ⟨955121, by rfl⟩ : syracuseStep 1273495 = 1910243) B1910243
theorem B13528781 : Blo 527800 13528781 := bstep (se 3 (by rfl) ⟨2536646, by rfl⟩ : syracuseStep 13528781 = 5073293) B5073293
theorem B3010405 : Blo 527800 3010405 := bstep (se 4 (by rfl) ⟨282225, by rfl⟩ : syracuseStep 3010405 = 564451) B564451
theorem B848087 : Blo 527800 848087 := bstep (se 1 (by rfl) ⟨636065, by rfl⟩ : syracuseStep 848087 = 1272131) B1272131
theorem B717017 : Blo 527800 717017 := bstep (se 2 (by rfl) ⟨268881, by rfl⟩ : syracuseStep 717017 = 537763) B537763
theorem B1700119 : Blo 527800 1700119 := bstep (se 1 (by rfl) ⟨1275089, by rfl⟩ : syracuseStep 1700119 = 2550179) B2550179
theorem B1339699 : Blo 527800 1339699 := bstep (se 1 (by rfl) ⟨1004774, by rfl⟩ : syracuseStep 1339699 = 2009549) B2009549
theorem B848279 : Blo 527800 848279 := bstep (se 1 (by rfl) ⟨636209, by rfl⟩ : syracuseStep 848279 = 1272419) B1272419
theorem B1339841 : Blo 527800 1339841 := bstep (se 2 (by rfl) ⟨502440, by rfl⟩ : syracuseStep 1339841 = 1004881) B1004881
theorem B17134051 : Blo 527800 17134051 := bstep (se 1 (by rfl) ⟨12850538, by rfl⟩ : syracuseStep 17134051 = 25701077) B25701077
theorem B11465347 : Blo 527800 11465347 := bstep (se 1 (by rfl) ⟨8599010, by rfl⟩ : syracuseStep 11465347 = 17198021) B17198021
theorem B1962641 : Blo 527800 1962641 := bstep (se 2 (by rfl) ⟨735990, by rfl⟩ : syracuseStep 1962641 = 1471981) B1471981
theorem B2946179 : Blo 527800 2946179 := bstep (se 1 (by rfl) ⟨2209634, by rfl⟩ : syracuseStep 2946179 = 4419269) B4419269
theorem B2684177 : Blo 527800 2684177 := bstep (se 2 (by rfl) ⟨1006566, by rfl⟩ : syracuseStep 2684177 = 2013133) B2013133
theorem B718103 : Blo 527800 718103 := bstep (se 1 (by rfl) ⟨538577, by rfl⟩ : syracuseStep 718103 = 1077155) B1077155
theorem B5174705 : Blo 527800 5174705 := bstep (se 2 (by rfl) ⟨1940514, by rfl⟩ : syracuseStep 5174705 = 3881029) B3881029
theorem B2684339 : Blo 527800 2684339 := bstep (se 1 (by rfl) ⟨2013254, by rfl⟩ : syracuseStep 2684339 = 4026509) B4026509
theorem B1701299 : Blo 527800 1701299 := bstep (se 1 (by rfl) ⟨1275974, by rfl⟩ : syracuseStep 1701299 = 2551949) B2551949
theorem B1144343 : Blo 527800 1144343 := bstep (se 1 (by rfl) ⟨858257, by rfl⟩ : syracuseStep 1144343 = 1716515) B1716515
theorem B8713763 : Blo 527800 8713763 := bstep (se 1 (by rfl) ⟨6535322, by rfl⟩ : syracuseStep 8713763 = 13070645) B13070645
theorem B849547 : Blo 527800 849547 := bstep (se 1 (by rfl) ⟨637160, by rfl⟩ : syracuseStep 849547 = 1274321) B1274321
theorem B1504919 : Blo 527800 1504919 := bstep (se 1 (by rfl) ⟨1128689, by rfl⟩ : syracuseStep 1504919 = 2257379) B2257379
theorem B1341107 : Blo 527800 1341107 := bstep (se 1 (by rfl) ⟨1005830, by rfl⟩ : syracuseStep 1341107 = 2011661) B2011661
theorem B1210049 : Blo 527800 1210049 := bstep (se 2 (by rfl) ⟨453768, by rfl⟩ : syracuseStep 1210049 = 907537) B907537
theorem B1144793 : Blo 527800 1144793 := bstep (se 2 (by rfl) ⟨429297, by rfl⟩ : syracuseStep 1144793 = 858595) B858595
theorem B850009 : Blo 527800 850009 := bstep (se 2 (by rfl) ⟨318753, by rfl⟩ : syracuseStep 850009 = 637507) B637507
theorem B1341643 : Blo 527800 1341643 := bstep (se 1 (by rfl) ⟨1006232, by rfl⟩ : syracuseStep 1341643 = 2012465) B2012465
theorem B1046807 : Blo 527800 1046807 := bstep (se 1 (by rfl) ⟨785105, by rfl⟩ : syracuseStep 1046807 = 1570211) B1570211
theorem B1341785 : Blo 527800 1341785 := bstep (se 2 (by rfl) ⟨503169, by rfl⟩ : syracuseStep 1341785 = 1006339) B1006339
theorem B850265 : Blo 527800 850265 := bstep (se 2 (by rfl) ⟨318849, by rfl⟩ : syracuseStep 850265 = 637699) B637699
theorem B1210777 : Blo 527800 1210777 := bstep (se 2 (by rfl) ⟨454041, by rfl⟩ : syracuseStep 1210777 = 908083) B908083
theorem B752203 : Blo 527800 752203 := bstep (se 1 (by rfl) ⟨564152, by rfl⟩ : syracuseStep 752203 = 1128305) B1128305
theorem B1506251 : Blo 527800 1506251 := bstep (se 1 (by rfl) ⟨1129688, by rfl⟩ : syracuseStep 1506251 = 2259377) B2259377
theorem B2259991 : Blo 527800 2259991 := bstep (se 1 (by rfl) ⟨1694993, by rfl⟩ : syracuseStep 2259991 = 3389987) B3389987
theorem B1277003 : Blo 527800 1277003 := bstep (se 1 (by rfl) ⟨957752, by rfl⟩ : syracuseStep 1277003 = 1915505) B1915505
theorem B2260061 : Blo 527800 2260061 := bstep (se 3 (by rfl) ⟨423761, by rfl⟩ : syracuseStep 2260061 = 847523) B847523
theorem B1342615 : Blo 527800 1342615 := bstep (se 1 (by rfl) ⟨1006961, by rfl⟩ : syracuseStep 1342615 = 2013923) B2013923
theorem B2686283 : Blo 527800 2686283 := bstep (se 1 (by rfl) ⟨2014712, by rfl⟩ : syracuseStep 2686283 = 4029425) B4029425
theorem B9698777 : Blo 527800 9698777 := bstep (se 2 (by rfl) ⟨3637041, by rfl⟩ : syracuseStep 9698777 = 7274083) B7274083
theorem B1703389 : Blo 527800 1703389 := bstep (se 3 (by rfl) ⟨319385, by rfl⟩ : syracuseStep 1703389 = 638771) B638771
theorem B3866129 : Blo 527800 3866129 := bstep (se 2 (by rfl) ⟨1449798, by rfl⟩ : syracuseStep 3866129 = 2899597) B2899597
theorem B1343051 : Blo 527800 1343051 := bstep (se 1 (by rfl) ⟨1007288, by rfl⟩ : syracuseStep 1343051 = 2014577) B2014577
theorem B1146611 : Blo 527800 1146611 := bstep (se 1 (by rfl) ⟨859958, by rfl⟩ : syracuseStep 1146611 = 1719917) B1719917
theorem B2260811 : Blo 527800 2260811 := bstep (se 1 (by rfl) ⟨1695608, by rfl⟩ : syracuseStep 2260811 = 3391217) B3391217
theorem B1343425 : Blo 527800 1343425 := bstep (se 2 (by rfl) ⟨503784, by rfl⟩ : syracuseStep 1343425 = 1007569) B1007569
theorem B2293879 : Blo 527800 2293879 := bstep (se 1 (by rfl) ⟨1720409, by rfl⟩ : syracuseStep 2293879 = 3440819) B3440819
theorem B1507481 : Blo 527800 1507481 := bstep (se 2 (by rfl) ⟨565305, by rfl⟩ : syracuseStep 1507481 = 1130611) B1130611
theorem B4849901 : Blo 527800 4849901 := bstep (se 3 (by rfl) ⟨909356, by rfl⟩ : syracuseStep 4849901 = 1818713) B1818713
theorem B1343891 : Blo 527800 1343891 := bstep (se 1 (by rfl) ⟨1007918, by rfl⟩ : syracuseStep 1343891 = 2015837) B2015837
theorem B754105 : Blo 527800 754105 := bstep (se 2 (by rfl) ⟨282789, by rfl⟩ : syracuseStep 754105 = 565579) B565579
theorem B1147321 : Blo 527800 1147321 := bstep (se 2 (by rfl) ⟨430245, by rfl⟩ : syracuseStep 1147321 = 860491) B860491
theorem B2687417 : Blo 527800 2687417 := bstep (se 2 (by rfl) ⟨1007781, by rfl⟩ : syracuseStep 2687417 = 2015563) B2015563
theorem B1016363 : Blo 527800 1016363 := bstep (se 1 (by rfl) ⟨762272, by rfl⟩ : syracuseStep 1016363 = 1524545) B1524545
theorem B754219 : Blo 527800 754219 := bstep (se 1 (by rfl) ⟨565664, by rfl⟩ : syracuseStep 754219 = 1131329) B1131329
theorem B1344185 : Blo 527800 1344185 := bstep (se 2 (by rfl) ⟨504069, by rfl⟩ : syracuseStep 1344185 = 1008139) B1008139
theorem B754447 : Blo 527800 754447 := bstep (se 1 (by rfl) ⟨565835, by rfl⟩ : syracuseStep 754447 = 1131671) B1131671
theorem B2262077 : Blo 527800 2262077 := bstep (se 3 (by rfl) ⟨424139, by rfl⟩ : syracuseStep 2262077 = 848279) B848279
theorem B1344883 : Blo 527800 1344883 := bstep (se 1 (by rfl) ⟨1008662, by rfl⟩ : syracuseStep 1344883 = 2017325) B2017325
theorem B1345025 : Blo 527800 1345025 := bstep (se 2 (by rfl) ⟨504384, by rfl⟩ : syracuseStep 1345025 = 1008769) B1008769
theorem B5080643 : Blo 527800 5080643 := bstep (se 1 (by rfl) ⟨3810482, by rfl⟩ : syracuseStep 5080643 = 7620965) B7620965
theorem B755335 : Blo 527800 755335 := bstep (se 1 (by rfl) ⟨566501, by rfl⟩ : syracuseStep 755335 = 1133003) B1133003
theorem B2688713 : Blo 527800 2688713 := bstep (se 2 (by rfl) ⟨1008267, by rfl⟩ : syracuseStep 2688713 = 2016535) B2016535
theorem B1509121 : Blo 527800 1509121 := bstep (se 2 (by rfl) ⟨565920, by rfl⟩ : syracuseStep 1509121 = 1131841) B1131841
theorem B4818851 : Blo 527800 4818851 := bstep (se 1 (by rfl) ⟨3614138, by rfl⟩ : syracuseStep 4818851 = 7228277) B7228277
theorem B1345481 : Blo 527800 1345481 := bstep (se 2 (by rfl) ⟨504555, by rfl⟩ : syracuseStep 1345481 = 1009111) B1009111
theorem B755831 : Blo 527800 755831 := bstep (se 1 (by rfl) ⟨566873, by rfl⟩ : syracuseStep 755831 = 1133747) B1133747
theorem B6457477 : Blo 527800 6457477 := bstep (se 4 (by rfl) ⟨605388, by rfl⟩ : syracuseStep 6457477 = 1210777) B1210777
theorem B690439 : Blo 527800 690439 := bstep (se 1 (by rfl) ⟨517829, by rfl⟩ : syracuseStep 690439 = 1035659) B1035659
theorem B1345835 : Blo 527800 1345835 := bstep (se 1 (by rfl) ⟨1009376, by rfl⟩ : syracuseStep 1345835 = 2018753) B2018753
theorem B1509691 : Blo 527800 1509691 := bstep (se 1 (by rfl) ⟨1132268, by rfl⟩ : syracuseStep 1509691 = 2264537) B2264537
theorem B4032827 : Blo 527800 4032827 := bstep (se 1 (by rfl) ⟨3024620, by rfl⟩ : syracuseStep 4032827 = 6049241) B6049241
theorem B953147 : Blo 527800 953147 := bstep (se 1 (by rfl) ⟨714860, by rfl⟩ : syracuseStep 953147 = 1429721) B1429721
theorem B756793 : Blo 527800 756793 := bstep (se 2 (by rfl) ⟨283797, by rfl⟩ : syracuseStep 756793 = 567595) B567595
theorem B2264435 : Blo 527800 2264435 := bstep (se 1 (by rfl) ⟨1698326, by rfl⟩ : syracuseStep 2264435 = 3396653) B3396653
theorem B757135 : Blo 527800 757135 := bstep (se 1 (by rfl) ⟨567851, by rfl⟩ : syracuseStep 757135 = 1135703) B1135703
theorem B527803 : Blo 527800 527803 := bstep (se 1 (by rfl) ⟨395852, by rfl⟩ : syracuseStep 527803 = 791705) B791705
theorem B527879 : Blo 527800 527879 := bstep (se 1 (by rfl) ⟨395909, by rfl⟩ : syracuseStep 527879 = 791819) B791819
theorem B527887 : Blo 527800 527887 := bstep (se 1 (by rfl) ⟨395915, by rfl⟩ : syracuseStep 527887 = 791831) B791831
theorem B527931 : Blo 527800 527931 := bstep (se 1 (by rfl) ⟨395948, by rfl⟩ : syracuseStep 527931 = 791897) B791897
theorem B528007 : Blo 527800 528007 := bstep (se 1 (by rfl) ⟨396005, by rfl⟩ : syracuseStep 528007 = 792011) B792011
theorem B528015 : Blo 527800 528015 := bstep (se 1 (by rfl) ⟨396011, by rfl⟩ : syracuseStep 528015 = 792023) B792023
theorem B528059 : Blo 527800 528059 := bstep (se 1 (by rfl) ⟨396044, by rfl⟩ : syracuseStep 528059 = 792089) B792089
theorem B528135 : Blo 527800 528135 := bstep (se 1 (by rfl) ⟨396101, by rfl⟩ : syracuseStep 528135 = 792203) B792203
theorem B528143 : Blo 527800 528143 := bstep (se 1 (by rfl) ⟨396107, by rfl⟩ : syracuseStep 528143 = 792215) B792215
theorem B6033203 : Blo 527800 6033203 := bstep (se 1 (by rfl) ⟨4524902, by rfl⟩ : syracuseStep 6033203 = 9049805) B9049805
theorem B528187 : Blo 527800 528187 := bstep (se 1 (by rfl) ⟨396140, by rfl⟩ : syracuseStep 528187 = 792281) B792281
theorem B528263 : Blo 527800 528263 := bstep (se 1 (by rfl) ⟨396197, by rfl⟩ : syracuseStep 528263 = 792395) B792395
theorem B528271 : Blo 527800 528271 := bstep (se 1 (by rfl) ⟨396203, by rfl⟩ : syracuseStep 528271 = 792407) B792407
theorem B593851 : Blo 527800 593851 := bstep (se 1 (by rfl) ⟨445388, by rfl⟩ : syracuseStep 593851 = 890777) B890777
theorem B528315 : Blo 527800 528315 := bstep (se 1 (by rfl) ⟨396236, by rfl⟩ : syracuseStep 528315 = 792473) B792473
theorem B1904593 : Blo 527800 1904593 := bstep (se 2 (by rfl) ⟨714222, by rfl⟩ : syracuseStep 1904593 = 1428445) B1428445
theorem B528391 : Blo 527800 528391 := bstep (se 1 (by rfl) ⟨396293, by rfl⟩ : syracuseStep 528391 = 792587) B792587
theorem B528399 : Blo 527800 528399 := bstep (se 1 (by rfl) ⟨396299, by rfl⟩ : syracuseStep 528399 = 792599) B792599
theorem B528443 : Blo 527800 528443 := bstep (se 1 (by rfl) ⟨396332, by rfl⟩ : syracuseStep 528443 = 792665) B792665
theorem B1806455 : Blo 527800 1806455 := bstep (se 1 (by rfl) ⟨1354841, by rfl⟩ : syracuseStep 1806455 = 2709683) B2709683
theorem B528519 : Blo 527800 528519 := bstep (se 1 (by rfl) ⟨396389, by rfl⟩ : syracuseStep 528519 = 792779) B792779
theorem B528527 : Blo 527800 528527 := bstep (se 1 (by rfl) ⟨396395, by rfl⟩ : syracuseStep 528527 = 792791) B792791
theorem B528571 : Blo 527800 528571 := bstep (se 1 (by rfl) ⟨396428, by rfl⟩ : syracuseStep 528571 = 792857) B792857
theorem B528647 : Blo 527800 528647 := bstep (se 1 (by rfl) ⟨396485, by rfl⟩ : syracuseStep 528647 = 792971) B792971
theorem B528655 : Blo 527800 528655 := bstep (se 1 (by rfl) ⟨396491, by rfl⟩ : syracuseStep 528655 = 792983) B792983
theorem B528699 : Blo 527800 528699 := bstep (se 1 (by rfl) ⟨396524, by rfl⟩ : syracuseStep 528699 = 793049) B793049
theorem B528775 : Blo 527800 528775 := bstep (se 1 (by rfl) ⟨396581, by rfl⟩ : syracuseStep 528775 = 793163) B793163
theorem B594319 : Blo 527800 594319 := bstep (se 1 (by rfl) ⟨445739, by rfl⟩ : syracuseStep 594319 = 891479) B891479
theorem B528783 : Blo 527800 528783 := bstep (se 1 (by rfl) ⟨396587, by rfl⟩ : syracuseStep 528783 = 793175) B793175
theorem B3019153 : Blo 527800 3019153 := bstep (se 2 (by rfl) ⟨1132182, by rfl⟩ : syracuseStep 3019153 = 2264365) B2264365
theorem B528827 : Blo 527800 528827 := bstep (se 1 (by rfl) ⟨396620, by rfl⟩ : syracuseStep 528827 = 793241) B793241
theorem B528903 : Blo 527800 528903 := bstep (se 1 (by rfl) ⟨396677, by rfl⟩ : syracuseStep 528903 = 793355) B793355
theorem B528911 : Blo 527800 528911 := bstep (se 1 (by rfl) ⟨396683, by rfl⟩ : syracuseStep 528911 = 793367) B793367
theorem B528955 : Blo 527800 528955 := bstep (se 1 (by rfl) ⟨396716, by rfl⟩ : syracuseStep 528955 = 793433) B793433
theorem B529031 : Blo 527800 529031 := bstep (se 1 (by rfl) ⟨396773, by rfl⟩ : syracuseStep 529031 = 793547) B793547
theorem B529039 : Blo 527800 529039 := bstep (se 1 (by rfl) ⟨396779, by rfl⟩ : syracuseStep 529039 = 793559) B793559
theorem B1512083 : Blo 527800 1512083 := bstep (se 1 (by rfl) ⟨1134062, by rfl⟩ : syracuseStep 1512083 = 2268125) B2268125
theorem B529083 : Blo 527800 529083 := bstep (se 1 (by rfl) ⟨396812, by rfl⟩ : syracuseStep 529083 = 793625) B793625
theorem B529159 : Blo 527800 529159 := bstep (se 1 (by rfl) ⟨396869, by rfl⟩ : syracuseStep 529159 = 793739) B793739
theorem B529167 : Blo 527800 529167 := bstep (se 1 (by rfl) ⟨396875, by rfl⟩ : syracuseStep 529167 = 793751) B793751
theorem B7574309 : Blo 527800 7574309 := bstep (se 4 (by rfl) ⟨710091, by rfl⟩ : syracuseStep 7574309 = 1420183) B1420183
theorem B529211 : Blo 527800 529211 := bstep (se 1 (by rfl) ⟨396908, by rfl⟩ : syracuseStep 529211 = 793817) B793817
theorem B1020731 : Blo 527800 1020731 := bstep (se 1 (by rfl) ⟨765548, by rfl⟩ : syracuseStep 1020731 = 1531097) B1531097
theorem B4821875 : Blo 527800 4821875 := bstep (se 1 (by rfl) ⟨3616406, by rfl⟩ : syracuseStep 4821875 = 7232813) B7232813
theorem B594823 : Blo 527800 594823 := bstep (se 1 (by rfl) ⟨446117, by rfl⟩ : syracuseStep 594823 = 892235) B892235
theorem B529287 : Blo 527800 529287 := bstep (se 1 (by rfl) ⟨396965, by rfl⟩ : syracuseStep 529287 = 793931) B793931
theorem B529295 : Blo 527800 529295 := bstep (se 1 (by rfl) ⟨396971, by rfl⟩ : syracuseStep 529295 = 793943) B793943
theorem B529339 : Blo 527800 529339 := bstep (se 1 (by rfl) ⟨397004, by rfl⟩ : syracuseStep 529339 = 794009) B794009
theorem B529415 : Blo 527800 529415 := bstep (se 1 (by rfl) ⟨397061, by rfl⟩ : syracuseStep 529415 = 794123) B794123
theorem B529423 : Blo 527800 529423 := bstep (se 1 (by rfl) ⟨397067, by rfl⟩ : syracuseStep 529423 = 794135) B794135
theorem B595003 : Blo 527800 595003 := bstep (se 1 (by rfl) ⟨446252, by rfl⟩ : syracuseStep 595003 = 892505) B892505
theorem B529467 : Blo 527800 529467 := bstep (se 1 (by rfl) ⟨397100, by rfl⟩ : syracuseStep 529467 = 794201) B794201
theorem B529543 : Blo 527800 529543 := bstep (se 1 (by rfl) ⟨397157, by rfl⟩ : syracuseStep 529543 = 794315) B794315
theorem B529551 : Blo 527800 529551 := bstep (se 1 (by rfl) ⟨397163, by rfl⟩ : syracuseStep 529551 = 794327) B794327
theorem B791723 : Blo 527800 791723 := bstep (se 1 (by rfl) ⟨593792, by rfl⟩ : syracuseStep 791723 = 1187585) B1187585
theorem B529595 : Blo 527800 529595 := bstep (se 1 (by rfl) ⟨397196, by rfl⟩ : syracuseStep 529595 = 794393) B794393
theorem B791753 : Blo 527800 791753 := bstep (se 2 (by rfl) ⟨296907, by rfl⟩ : syracuseStep 791753 = 593815) B593815
theorem B529671 : Blo 527800 529671 := bstep (se 1 (by rfl) ⟨397253, by rfl⟩ : syracuseStep 529671 = 794507) B794507
theorem B529679 : Blo 527800 529679 := bstep (se 1 (by rfl) ⟨397259, by rfl⟩ : syracuseStep 529679 = 794519) B794519
theorem B791867 : Blo 527800 791867 := bstep (se 1 (by rfl) ⟨593900, by rfl⟩ : syracuseStep 791867 = 1187801) B1187801
theorem B529723 : Blo 527800 529723 := bstep (se 1 (by rfl) ⟨397292, by rfl⟩ : syracuseStep 529723 = 794585) B794585
theorem B791927 : Blo 527800 791927 := bstep (se 1 (by rfl) ⟨593945, by rfl⟩ : syracuseStep 791927 = 1187891) B1187891
theorem B529799 : Blo 527800 529799 := bstep (se 1 (by rfl) ⟨397349, by rfl⟩ : syracuseStep 529799 = 794699) B794699
theorem B791951 : Blo 527800 791951 := bstep (se 1 (by rfl) ⟨593963, by rfl⟩ : syracuseStep 791951 = 1187927) B1187927
theorem B529807 : Blo 527800 529807 := bstep (se 1 (by rfl) ⟨397355, by rfl⟩ : syracuseStep 529807 = 794711) B794711
theorem B2004371 : Blo 527800 2004371 := bstep (se 1 (by rfl) ⟨1503278, by rfl⟩ : syracuseStep 2004371 = 3006557) B3006557
theorem B1512857 : Blo 527800 1512857 := bstep (se 2 (by rfl) ⟨567321, by rfl⟩ : syracuseStep 1512857 = 1134643) B1134643
theorem B791993 : Blo 527800 791993 := bstep (se 2 (by rfl) ⟨296997, by rfl⟩ : syracuseStep 791993 = 593995) B593995
theorem B529851 : Blo 527800 529851 := bstep (se 1 (by rfl) ⟨397388, by rfl⟩ : syracuseStep 529851 = 794777) B794777
theorem B792071 : Blo 527800 792071 := bstep (se 1 (by rfl) ⟨594053, by rfl⟩ : syracuseStep 792071 = 1188107) B1188107
theorem B529927 : Blo 527800 529927 := bstep (se 1 (by rfl) ⟨397445, by rfl⟩ : syracuseStep 529927 = 794891) B794891
theorem B595471 : Blo 527800 595471 := bstep (se 1 (by rfl) ⟨446603, by rfl⟩ : syracuseStep 595471 = 893207) B893207
theorem B529935 : Blo 527800 529935 := bstep (se 1 (by rfl) ⟨397451, by rfl⟩ : syracuseStep 529935 = 794903) B794903
theorem B792107 : Blo 527800 792107 := bstep (se 1 (by rfl) ⟨594080, by rfl⟩ : syracuseStep 792107 = 1188161) B1188161
theorem B529979 : Blo 527800 529979 := bstep (se 1 (by rfl) ⟨397484, by rfl⟩ : syracuseStep 529979 = 794969) B794969
theorem B792137 : Blo 527800 792137 := bstep (se 2 (by rfl) ⟨297051, by rfl⟩ : syracuseStep 792137 = 594103) B594103
theorem B530055 : Blo 527800 530055 := bstep (se 1 (by rfl) ⟨397541, by rfl⟩ : syracuseStep 530055 = 795083) B795083
theorem B530063 : Blo 527800 530063 := bstep (se 1 (by rfl) ⟨397547, by rfl⟩ : syracuseStep 530063 = 795095) B795095
theorem B792251 : Blo 527800 792251 := bstep (se 1 (by rfl) ⟨594188, by rfl⟩ : syracuseStep 792251 = 1188377) B1188377
theorem B530107 : Blo 527800 530107 := bstep (se 1 (by rfl) ⟨397580, by rfl⟩ : syracuseStep 530107 = 795161) B795161
theorem B792311 : Blo 527800 792311 := bstep (se 1 (by rfl) ⟨594233, by rfl⟩ : syracuseStep 792311 = 1188467) B1188467
theorem B530183 : Blo 527800 530183 := bstep (se 1 (by rfl) ⟨397637, by rfl⟩ : syracuseStep 530183 = 795275) B795275
theorem B792335 : Blo 527800 792335 := bstep (se 1 (by rfl) ⟨594251, by rfl⟩ : syracuseStep 792335 = 1188503) B1188503
theorem B530191 : Blo 527800 530191 := bstep (se 1 (by rfl) ⟨397643, by rfl⟩ : syracuseStep 530191 = 795287) B795287
theorem B792377 : Blo 527800 792377 := bstep (se 2 (by rfl) ⟨297141, by rfl⟩ : syracuseStep 792377 = 594283) B594283
theorem B530235 : Blo 527800 530235 := bstep (se 1 (by rfl) ⟨397676, by rfl⟩ : syracuseStep 530235 = 795353) B795353
theorem B890743 : Blo 527800 890743 := bstep (se 1 (by rfl) ⟨668057, by rfl⟩ : syracuseStep 890743 = 1336115) B1336115
theorem B2004871 : Blo 527800 2004871 := bstep (se 1 (by rfl) ⟨1503653, by rfl⟩ : syracuseStep 2004871 = 3007307) B3007307
theorem B792455 : Blo 527800 792455 := bstep (se 1 (by rfl) ⟨594341, by rfl⟩ : syracuseStep 792455 = 1188683) B1188683
theorem B530311 : Blo 527800 530311 := bstep (se 1 (by rfl) ⟨397733, by rfl⟩ : syracuseStep 530311 = 795467) B795467
theorem B530319 : Blo 527800 530319 := bstep (se 1 (by rfl) ⟨397739, by rfl⟩ : syracuseStep 530319 = 795479) B795479
theorem B1087379 : Blo 527800 1087379 := bstep (se 1 (by rfl) ⟨815534, by rfl⟩ : syracuseStep 1087379 = 1631069) B1631069
theorem B5150627 : Blo 527800 5150627 := bstep (se 1 (by rfl) ⟨3862970, by rfl⟩ : syracuseStep 5150627 = 7725941) B7725941
theorem B792491 : Blo 527800 792491 := bstep (se 1 (by rfl) ⟨594368, by rfl⟩ : syracuseStep 792491 = 1188737) B1188737
theorem B530363 : Blo 527800 530363 := bstep (se 1 (by rfl) ⟨397772, by rfl⟩ : syracuseStep 530363 = 795545) B795545
theorem B792521 : Blo 527800 792521 := bstep (se 2 (by rfl) ⟨297195, by rfl⟩ : syracuseStep 792521 = 594391) B594391
theorem B22845401 : Blo 527800 22845401 := bstep (se 2 (by rfl) ⟨8567025, by rfl⟩ : syracuseStep 22845401 = 17134051) B17134051
theorem B595975 : Blo 527800 595975 := bstep (se 1 (by rfl) ⟨446981, by rfl⟩ : syracuseStep 595975 = 893963) B893963
theorem B530439 : Blo 527800 530439 := bstep (se 1 (by rfl) ⟨397829, by rfl⟩ : syracuseStep 530439 = 795659) B795659
theorem B530447 : Blo 527800 530447 := bstep (se 1 (by rfl) ⟨397835, by rfl⟩ : syracuseStep 530447 = 795671) B795671
theorem B19666961 : Blo 527800 19666961 := bstep (se 2 (by rfl) ⟨7375110, by rfl⟩ : syracuseStep 19666961 = 14750221) B14750221
theorem B890939 : Blo 527800 890939 := bstep (se 1 (by rfl) ⟨668204, by rfl⟩ : syracuseStep 890939 = 1336409) B1336409
theorem B792635 : Blo 527800 792635 := bstep (se 1 (by rfl) ⟨594476, by rfl⟩ : syracuseStep 792635 = 1188953) B1188953
theorem B530491 : Blo 527800 530491 := bstep (se 1 (by rfl) ⟨397868, by rfl⟩ : syracuseStep 530491 = 795737) B795737
theorem B792695 : Blo 527800 792695 := bstep (se 1 (by rfl) ⟨594521, by rfl⟩ : syracuseStep 792695 = 1189043) B1189043
theorem B530567 : Blo 527800 530567 := bstep (se 1 (by rfl) ⟨397925, by rfl⟩ : syracuseStep 530567 = 795851) B795851
theorem B792719 : Blo 527800 792719 := bstep (se 1 (by rfl) ⟨594539, by rfl⟩ : syracuseStep 792719 = 1189079) B1189079
theorem B530575 : Blo 527800 530575 := bstep (se 1 (by rfl) ⟨397931, by rfl⟩ : syracuseStep 530575 = 795863) B795863
theorem B792761 : Blo 527800 792761 := bstep (se 2 (by rfl) ⟨297285, by rfl⟩ : syracuseStep 792761 = 594571) B594571
theorem B596155 : Blo 527800 596155 := bstep (se 1 (by rfl) ⟨447116, by rfl⟩ : syracuseStep 596155 = 894233) B894233
theorem B530619 : Blo 527800 530619 := bstep (se 1 (by rfl) ⟨397964, by rfl⟩ : syracuseStep 530619 = 795929) B795929
theorem B792839 : Blo 527800 792839 := bstep (se 1 (by rfl) ⟨594629, by rfl⟩ : syracuseStep 792839 = 1189259) B1189259
theorem B530695 : Blo 527800 530695 := bstep (se 1 (by rfl) ⟨398021, by rfl⟩ : syracuseStep 530695 = 796043) B796043
theorem B530703 : Blo 527800 530703 := bstep (se 1 (by rfl) ⟨398027, by rfl⟩ : syracuseStep 530703 = 796055) B796055
theorem B792875 : Blo 527800 792875 := bstep (se 1 (by rfl) ⟨594656, by rfl⟩ : syracuseStep 792875 = 1189313) B1189313
theorem B5970235 : Blo 527800 5970235 := bstep (se 1 (by rfl) ⟨4477676, by rfl⟩ : syracuseStep 5970235 = 8955353) B8955353
theorem B530747 : Blo 527800 530747 := bstep (se 1 (by rfl) ⟨398060, by rfl⟩ : syracuseStep 530747 = 796121) B796121
theorem B792905 : Blo 527800 792905 := bstep (se 2 (by rfl) ⟨297339, by rfl⟩ : syracuseStep 792905 = 594679) B594679
theorem B530823 : Blo 527800 530823 := bstep (se 1 (by rfl) ⟨398117, by rfl⟩ : syracuseStep 530823 = 796235) B796235
theorem B530831 : Blo 527800 530831 := bstep (se 1 (by rfl) ⟨398123, by rfl⟩ : syracuseStep 530831 = 796247) B796247
theorem B2857361 : Blo 527800 2857361 := bstep (se 2 (by rfl) ⟨1071510, by rfl⟩ : syracuseStep 2857361 = 2143021) B2143021
theorem B793019 : Blo 527800 793019 := bstep (se 1 (by rfl) ⟨594764, by rfl⟩ : syracuseStep 793019 = 1189529) B1189529
theorem B530875 : Blo 527800 530875 := bstep (se 1 (by rfl) ⟨398156, by rfl⟩ : syracuseStep 530875 = 796313) B796313
theorem B891337 : Blo 527800 891337 := bstep (se 2 (by rfl) ⟨334251, by rfl⟩ : syracuseStep 891337 = 668503) B668503
theorem B793079 : Blo 527800 793079 := bstep (se 1 (by rfl) ⟨594809, by rfl⟩ : syracuseStep 793079 = 1189619) B1189619
theorem B530951 : Blo 527800 530951 := bstep (se 1 (by rfl) ⟨398213, by rfl⟩ : syracuseStep 530951 = 796427) B796427
theorem B793103 : Blo 527800 793103 := bstep (se 1 (by rfl) ⟨594827, by rfl⟩ : syracuseStep 793103 = 1189655) B1189655
theorem B530959 : Blo 527800 530959 := bstep (se 1 (by rfl) ⟨398219, by rfl⟩ : syracuseStep 530959 = 796439) B796439
theorem B793145 : Blo 527800 793145 := bstep (se 2 (by rfl) ⟨297429, by rfl⟩ : syracuseStep 793145 = 594859) B594859
theorem B531003 : Blo 527800 531003 := bstep (se 1 (by rfl) ⟨398252, by rfl⟩ : syracuseStep 531003 = 796505) B796505
theorem B8591939 : Blo 527800 8591939 := bstep (se 1 (by rfl) ⟨6443954, by rfl⟩ : syracuseStep 8591939 = 12887909) B12887909
theorem B793223 : Blo 527800 793223 := bstep (se 1 (by rfl) ⟨594917, by rfl⟩ : syracuseStep 793223 = 1189835) B1189835
theorem B531079 : Blo 527800 531079 := bstep (se 1 (by rfl) ⟨398309, by rfl⟩ : syracuseStep 531079 = 796619) B796619
theorem B596623 : Blo 527800 596623 := bstep (se 1 (by rfl) ⟨447467, by rfl⟩ : syracuseStep 596623 = 894935) B894935
theorem B531087 : Blo 527800 531087 := bstep (se 1 (by rfl) ⟨398315, by rfl⟩ : syracuseStep 531087 = 796631) B796631
theorem B793259 : Blo 527800 793259 := bstep (se 1 (by rfl) ⟨594944, by rfl⟩ : syracuseStep 793259 = 1189889) B1189889
theorem B531131 : Blo 527800 531131 := bstep (se 1 (by rfl) ⟨398348, by rfl⟩ : syracuseStep 531131 = 796697) B796697
theorem B793289 : Blo 527800 793289 := bstep (se 2 (by rfl) ⟨297483, by rfl⟩ : syracuseStep 793289 = 594967) B594967
theorem B3021569 : Blo 527800 3021569 := bstep (se 2 (by rfl) ⟨1133088, by rfl⟩ : syracuseStep 3021569 = 2266177) B2266177
theorem B531207 : Blo 527800 531207 := bstep (se 1 (by rfl) ⟨398405, by rfl⟩ : syracuseStep 531207 = 796811) B796811
theorem B531215 : Blo 527800 531215 := bstep (se 1 (by rfl) ⟨398411, by rfl⟩ : syracuseStep 531215 = 796823) B796823
theorem B793403 : Blo 527800 793403 := bstep (se 1 (by rfl) ⟨595052, by rfl⟩ : syracuseStep 793403 = 1190105) B1190105
theorem B531259 : Blo 527800 531259 := bstep (se 1 (by rfl) ⟨398444, by rfl⟩ : syracuseStep 531259 = 796889) B796889
theorem B793463 : Blo 527800 793463 := bstep (se 1 (by rfl) ⟨595097, by rfl⟩ : syracuseStep 793463 = 1190195) B1190195
theorem B531335 : Blo 527800 531335 := bstep (se 1 (by rfl) ⟨398501, by rfl⟩ : syracuseStep 531335 = 797003) B797003
theorem B793487 : Blo 527800 793487 := bstep (se 1 (by rfl) ⟨595115, by rfl⟩ : syracuseStep 793487 = 1190231) B1190231
theorem B531343 : Blo 527800 531343 := bstep (se 1 (by rfl) ⟨398507, by rfl⟩ : syracuseStep 531343 = 797015) B797015
theorem B1809299 : Blo 527800 1809299 := bstep (se 1 (by rfl) ⟨1356974, by rfl⟩ : syracuseStep 1809299 = 2713949) B2713949
theorem B793529 : Blo 527800 793529 := bstep (se 2 (by rfl) ⟨297573, by rfl⟩ : syracuseStep 793529 = 595147) B595147
theorem B531387 : Blo 527800 531387 := bstep (se 1 (by rfl) ⟨398540, by rfl⟩ : syracuseStep 531387 = 797081) B797081
theorem B793607 : Blo 527800 793607 := bstep (se 1 (by rfl) ⟨595205, by rfl⟩ : syracuseStep 793607 = 1190411) B1190411
theorem B531463 : Blo 527800 531463 := bstep (se 1 (by rfl) ⟨398597, by rfl⟩ : syracuseStep 531463 = 797195) B797195
theorem B531471 : Blo 527800 531471 := bstep (se 1 (by rfl) ⟨398603, by rfl⟩ : syracuseStep 531471 = 797207) B797207
theorem B793643 : Blo 527800 793643 := bstep (se 1 (by rfl) ⟨595232, by rfl⟩ : syracuseStep 793643 = 1190465) B1190465
theorem B531515 : Blo 527800 531515 := bstep (se 1 (by rfl) ⟨398636, by rfl⟩ : syracuseStep 531515 = 797273) B797273
theorem B793673 : Blo 527800 793673 := bstep (se 2 (by rfl) ⟨297627, by rfl⟩ : syracuseStep 793673 = 595255) B595255
theorem B892039 : Blo 527800 892039 := bstep (se 1 (by rfl) ⟨669029, by rfl⟩ : syracuseStep 892039 = 1338059) B1338059
theorem B597127 : Blo 527800 597127 := bstep (se 1 (by rfl) ⟨447845, by rfl⟩ : syracuseStep 597127 = 895691) B895691
theorem B531591 : Blo 527800 531591 := bstep (se 1 (by rfl) ⟨398693, by rfl⟩ : syracuseStep 531591 = 797387) B797387
theorem B531599 : Blo 527800 531599 := bstep (se 1 (by rfl) ⟨398699, by rfl⟩ : syracuseStep 531599 = 797399) B797399
theorem B793787 : Blo 527800 793787 := bstep (se 1 (by rfl) ⟨595340, by rfl⟩ : syracuseStep 793787 = 1190681) B1190681
theorem B531643 : Blo 527800 531643 := bstep (se 1 (by rfl) ⟨398732, by rfl⟩ : syracuseStep 531643 = 797465) B797465
theorem B793847 : Blo 527800 793847 := bstep (se 1 (by rfl) ⟨595385, by rfl⟩ : syracuseStep 793847 = 1190771) B1190771
theorem B531719 : Blo 527800 531719 := bstep (se 1 (by rfl) ⟨398789, by rfl⟩ : syracuseStep 531719 = 797579) B797579
theorem B793871 : Blo 527800 793871 := bstep (se 1 (by rfl) ⟨595403, by rfl⟩ : syracuseStep 793871 = 1190807) B1190807
theorem B531727 : Blo 527800 531727 := bstep (se 1 (by rfl) ⟨398795, by rfl⟩ : syracuseStep 531727 = 797591) B797591
theorem B2858273 : Blo 527800 2858273 := bstep (se 2 (by rfl) ⟨1071852, by rfl⟩ : syracuseStep 2858273 = 2143705) B2143705
theorem B1809697 : Blo 527800 1809697 := bstep (se 2 (by rfl) ⟨678636, by rfl⟩ : syracuseStep 1809697 = 1357273) B1357273
theorem B793913 : Blo 527800 793913 := bstep (se 2 (by rfl) ⟨297717, by rfl⟩ : syracuseStep 793913 = 595435) B595435
theorem B597307 : Blo 527800 597307 := bstep (se 1 (by rfl) ⟨447980, by rfl⟩ : syracuseStep 597307 = 895961) B895961
theorem B531771 : Blo 527800 531771 := bstep (se 1 (by rfl) ⟨398828, by rfl⟩ : syracuseStep 531771 = 797657) B797657
theorem B5709149 : Blo 527800 5709149 := bstep (se 3 (by rfl) ⟨1070465, by rfl⟩ : syracuseStep 5709149 = 2140931) B2140931
theorem B793991 : Blo 527800 793991 := bstep (se 1 (by rfl) ⟨595493, by rfl⟩ : syracuseStep 793991 = 1190987) B1190987
theorem B794027 : Blo 527800 794027 := bstep (se 1 (by rfl) ⟨595520, by rfl⟩ : syracuseStep 794027 = 1191041) B1191041
theorem B794057 : Blo 527800 794057 := bstep (se 2 (by rfl) ⟨297771, by rfl⟩ : syracuseStep 794057 = 595543) B595543
theorem B4038173 : Blo 527800 4038173 := bstep (se 3 (by rfl) ⟨757157, by rfl⟩ : syracuseStep 4038173 = 1514315) B1514315
theorem B794171 : Blo 527800 794171 := bstep (se 1 (by rfl) ⟨595628, by rfl⟩ : syracuseStep 794171 = 1191257) B1191257
theorem B2268739 : Blo 527800 2268739 := bstep (se 1 (by rfl) ⟨1701554, by rfl⟩ : syracuseStep 2268739 = 3403109) B3403109
theorem B794231 : Blo 527800 794231 := bstep (se 1 (by rfl) ⟨595673, by rfl⟩ : syracuseStep 794231 = 1191347) B1191347
theorem B794255 : Blo 527800 794255 := bstep (se 1 (by rfl) ⟨595691, by rfl⟩ : syracuseStep 794255 = 1191383) B1191383
theorem B20717207 : Blo 527800 20717207 := bstep (se 1 (by rfl) ⟨15537905, by rfl⟩ : syracuseStep 20717207 = 31075811) B31075811
theorem B794297 : Blo 527800 794297 := bstep (se 2 (by rfl) ⟨297861, by rfl⟩ : syracuseStep 794297 = 595723) B595723
theorem B794375 : Blo 527800 794375 := bstep (se 1 (by rfl) ⟨595781, by rfl⟩ : syracuseStep 794375 = 1191563) B1191563
theorem B892687 : Blo 527800 892687 := bstep (se 1 (by rfl) ⟨669515, by rfl⟩ : syracuseStep 892687 = 1339031) B1339031
theorem B597775 : Blo 527800 597775 := bstep (se 1 (by rfl) ⟨448331, by rfl⟩ : syracuseStep 597775 = 896663) B896663
theorem B794411 : Blo 527800 794411 := bstep (se 1 (by rfl) ⟨595808, by rfl⟩ : syracuseStep 794411 = 1191617) B1191617
theorem B9019187 : Blo 527800 9019187 := bstep (se 1 (by rfl) ⟨6764390, by rfl⟩ : syracuseStep 9019187 = 13528781) B13528781
theorem B794441 : Blo 527800 794441 := bstep (se 2 (by rfl) ⟨297915, by rfl⟩ : syracuseStep 794441 = 595831) B595831
theorem B794555 : Blo 527800 794555 := bstep (se 1 (by rfl) ⟨595916, by rfl⟩ : syracuseStep 794555 = 1191833) B1191833
theorem B794615 : Blo 527800 794615 := bstep (se 1 (by rfl) ⟨595961, by rfl⟩ : syracuseStep 794615 = 1191923) B1191923
theorem B1187855 : Blo 527800 1187855 := bstep (se 1 (by rfl) ⟨890891, by rfl⟩ : syracuseStep 1187855 = 1781783) B1781783
theorem B794639 : Blo 527800 794639 := bstep (se 1 (by rfl) ⟨595979, by rfl⟩ : syracuseStep 794639 = 1191959) B1191959
theorem B1187873 : Blo 527800 1187873 := bstep (se 2 (by rfl) ⟨445452, by rfl⟩ : syracuseStep 1187873 = 890905) B890905
theorem B794681 : Blo 527800 794681 := bstep (se 2 (by rfl) ⟨298005, by rfl⟩ : syracuseStep 794681 = 596011) B596011
theorem B794759 : Blo 527800 794759 := bstep (se 1 (by rfl) ⟨596069, by rfl⟩ : syracuseStep 794759 = 1192139) B1192139
theorem B565391 : Blo 527800 565391 := bstep (se 1 (by rfl) ⟨424043, by rfl⟩ : syracuseStep 565391 = 848087) B848087
theorem B794795 : Blo 527800 794795 := bstep (se 1 (by rfl) ⟨596096, by rfl⟩ : syracuseStep 794795 = 1192193) B1192193
theorem B794825 : Blo 527800 794825 := bstep (se 2 (by rfl) ⟨298059, by rfl⟩ : syracuseStep 794825 = 596119) B596119
theorem B893227 : Blo 527800 893227 := bstep (se 1 (by rfl) ⟨669920, by rfl⟩ : syracuseStep 893227 = 1339841) B1339841
theorem B794939 : Blo 527800 794939 := bstep (se 1 (by rfl) ⟨596204, by rfl⟩ : syracuseStep 794939 = 1192409) B1192409
theorem B1188215 : Blo 527800 1188215 := bstep (se 1 (by rfl) ⟨891161, by rfl⟩ : syracuseStep 1188215 = 1782323) B1782323
theorem B794999 : Blo 527800 794999 := bstep (se 1 (by rfl) ⟨596249, by rfl⟩ : syracuseStep 794999 = 1192499) B1192499
theorem B795023 : Blo 527800 795023 := bstep (se 1 (by rfl) ⟨596267, by rfl⟩ : syracuseStep 795023 = 1192535) B1192535
theorem B893369 : Blo 527800 893369 := bstep (se 2 (by rfl) ⟨335013, by rfl⟩ : syracuseStep 893369 = 670027) B670027
theorem B795065 : Blo 527800 795065 := bstep (se 2 (by rfl) ⟨298149, by rfl⟩ : syracuseStep 795065 = 596299) B596299
theorem B795143 : Blo 527800 795143 := bstep (se 1 (by rfl) ⟨596357, by rfl⟩ : syracuseStep 795143 = 1192715) B1192715
theorem B1188395 : Blo 527800 1188395 := bstep (se 1 (by rfl) ⟨891296, by rfl⟩ : syracuseStep 1188395 = 1782593) B1782593
theorem B795179 : Blo 527800 795179 := bstep (se 1 (by rfl) ⟨596384, by rfl⟩ : syracuseStep 795179 = 1192769) B1192769
theorem B795209 : Blo 527800 795209 := bstep (se 2 (by rfl) ⟨298203, by rfl⟩ : syracuseStep 795209 = 596407) B596407
theorem B1450631 : Blo 527800 1450631 := bstep (se 1 (by rfl) ⟨1087973, by rfl⟩ : syracuseStep 1450631 = 2175947) B2175947
theorem B795323 : Blo 527800 795323 := bstep (se 1 (by rfl) ⟨596492, by rfl⟩ : syracuseStep 795323 = 1192985) B1192985
theorem B2990785 : Blo 527800 2990785 := bstep (se 2 (by rfl) ⟨1121544, by rfl⟩ : syracuseStep 2990785 = 2243089) B2243089
theorem B4530917 : Blo 527800 4530917 := bstep (se 4 (by rfl) ⟨424773, by rfl⟩ : syracuseStep 4530917 = 849547) B849547
theorem B795383 : Blo 527800 795383 := bstep (se 1 (by rfl) ⟨596537, by rfl⟩ : syracuseStep 795383 = 1193075) B1193075
theorem B795407 : Blo 527800 795407 := bstep (se 1 (by rfl) ⟨596555, by rfl⟩ : syracuseStep 795407 = 1193111) B1193111
theorem B795449 : Blo 527800 795449 := bstep (se 2 (by rfl) ⟨298293, by rfl⟩ : syracuseStep 795449 = 596587) B596587
theorem B795527 : Blo 527800 795527 := bstep (se 1 (by rfl) ⟨596645, by rfl⟩ : syracuseStep 795527 = 1193291) B1193291
theorem B1188755 : Blo 527800 1188755 := bstep (se 1 (by rfl) ⟨891566, by rfl⟩ : syracuseStep 1188755 = 1783133) B1783133
theorem B795563 : Blo 527800 795563 := bstep (se 1 (by rfl) ⟨596672, by rfl⟩ : syracuseStep 795563 = 1193345) B1193345
theorem B3023801 : Blo 527800 3023801 := bstep (se 2 (by rfl) ⟨1133925, by rfl⟩ : syracuseStep 3023801 = 2267851) B2267851
theorem B1188809 : Blo 527800 1188809 := bstep (se 2 (by rfl) ⟨445803, by rfl⟩ : syracuseStep 1188809 = 891607) B891607
theorem B795593 : Blo 527800 795593 := bstep (se 2 (by rfl) ⟨298347, by rfl⟩ : syracuseStep 795593 = 596695) B596695
theorem B3449803 : Blo 527800 3449803 := bstep (se 1 (by rfl) ⟨2587352, by rfl⟩ : syracuseStep 3449803 = 5174705) B5174705
theorem B762895 : Blo 527800 762895 := bstep (se 1 (by rfl) ⟨572171, by rfl⟩ : syracuseStep 762895 = 1144343) B1144343
theorem B5809175 : Blo 527800 5809175 := bstep (se 1 (by rfl) ⟨4356881, by rfl⟩ : syracuseStep 5809175 = 8713763) B8713763
theorem B795707 : Blo 527800 795707 := bstep (se 1 (by rfl) ⟨596780, by rfl⟩ : syracuseStep 795707 = 1193561) B1193561
theorem B894071 : Blo 527800 894071 := bstep (se 1 (by rfl) ⟨670553, by rfl⟩ : syracuseStep 894071 = 1341107) B1341107
theorem B795767 : Blo 527800 795767 := bstep (se 1 (by rfl) ⟨596825, by rfl⟩ : syracuseStep 795767 = 1193651) B1193651
theorem B795791 : Blo 527800 795791 := bstep (se 1 (by rfl) ⟨596843, by rfl⟩ : syracuseStep 795791 = 1193687) B1193687
theorem B795833 : Blo 527800 795833 := bstep (se 2 (by rfl) ⟨298437, by rfl⟩ : syracuseStep 795833 = 596875) B596875
theorem B795911 : Blo 527800 795911 := bstep (se 1 (by rfl) ⟨596933, by rfl⟩ : syracuseStep 795911 = 1193867) B1193867
theorem B795947 : Blo 527800 795947 := bstep (se 1 (by rfl) ⟨596960, by rfl⟩ : syracuseStep 795947 = 1193921) B1193921
theorem B763195 : Blo 527800 763195 := bstep (se 1 (by rfl) ⟨572396, by rfl⟩ : syracuseStep 763195 = 1144793) B1144793
theorem B795977 : Blo 527800 795977 := bstep (se 2 (by rfl) ⟨298491, by rfl⟩ : syracuseStep 795977 = 596983) B596983
theorem B796091 : Blo 527800 796091 := bstep (se 1 (by rfl) ⟨597068, by rfl⟩ : syracuseStep 796091 = 1194137) B1194137
theorem B796151 : Blo 527800 796151 := bstep (se 1 (by rfl) ⟨597113, by rfl⟩ : syracuseStep 796151 = 1194227) B1194227
theorem B697871 : Blo 527800 697871 := bstep (se 1 (by rfl) ⟨523403, by rfl⟩ : syracuseStep 697871 = 1046807) B1046807
theorem B796175 : Blo 527800 796175 := bstep (se 1 (by rfl) ⟨597131, by rfl⟩ : syracuseStep 796175 = 1194263) B1194263
theorem B796217 : Blo 527800 796217 := bstep (se 2 (by rfl) ⟨298581, by rfl⟩ : syracuseStep 796217 = 597163) B597163
theorem B894523 : Blo 527800 894523 := bstep (se 1 (by rfl) ⟨670892, by rfl⟩ : syracuseStep 894523 = 1341785) B1341785
theorem B566843 : Blo 527800 566843 := bstep (se 1 (by rfl) ⟨425132, by rfl⟩ : syracuseStep 566843 = 850265) B850265
theorem B1189511 : Blo 527800 1189511 := bstep (se 1 (by rfl) ⟨892133, by rfl⟩ : syracuseStep 1189511 = 1784267) B1784267
theorem B796295 : Blo 527800 796295 := bstep (se 1 (by rfl) ⟨597221, by rfl⟩ : syracuseStep 796295 = 1194443) B1194443
theorem B796331 : Blo 527800 796331 := bstep (se 1 (by rfl) ⟨597248, by rfl⟩ : syracuseStep 796331 = 1194497) B1194497
theorem B894665 : Blo 527800 894665 := bstep (se 2 (by rfl) ⟨335499, by rfl⟩ : syracuseStep 894665 = 670999) B670999
theorem B796361 : Blo 527800 796361 := bstep (se 2 (by rfl) ⟨298635, by rfl⟩ : syracuseStep 796361 = 597271) B597271
theorem B1189691 : Blo 527800 1189691 := bstep (se 1 (by rfl) ⟨892268, by rfl⟩ : syracuseStep 1189691 = 1784537) B1784537
theorem B796475 : Blo 527800 796475 := bstep (se 1 (by rfl) ⟨597356, by rfl⟩ : syracuseStep 796475 = 1194713) B1194713
theorem B796535 : Blo 527800 796535 := bstep (se 1 (by rfl) ⟨597401, by rfl⟩ : syracuseStep 796535 = 1194803) B1194803
theorem B796559 : Blo 527800 796559 := bstep (se 1 (by rfl) ⟨597419, by rfl⟩ : syracuseStep 796559 = 1194839) B1194839
theorem B3876761 : Blo 527800 3876761 := bstep (se 2 (by rfl) ⟨1453785, by rfl⟩ : syracuseStep 3876761 = 2907571) B2907571
theorem B1189817 : Blo 527800 1189817 := bstep (se 2 (by rfl) ⟨446181, by rfl⟩ : syracuseStep 1189817 = 892363) B892363
theorem B796601 : Blo 527800 796601 := bstep (se 2 (by rfl) ⟨298725, by rfl⟩ : syracuseStep 796601 = 597451) B597451
theorem B2271185 : Blo 527800 2271185 := bstep (se 2 (by rfl) ⟨851694, by rfl⟩ : syracuseStep 2271185 = 1703389) B1703389
theorem B796679 : Blo 527800 796679 := bstep (se 1 (by rfl) ⟨597509, by rfl⟩ : syracuseStep 796679 = 1195019) B1195019
theorem B796715 : Blo 527800 796715 := bstep (se 1 (by rfl) ⟨597536, by rfl⟩ : syracuseStep 796715 = 1195073) B1195073
theorem B796745 : Blo 527800 796745 := bstep (se 2 (by rfl) ⟨298779, by rfl⟩ : syracuseStep 796745 = 597559) B597559
theorem B796859 : Blo 527800 796859 := bstep (se 1 (by rfl) ⟨597644, by rfl⟩ : syracuseStep 796859 = 1195289) B1195289
theorem B796919 : Blo 527800 796919 := bstep (se 1 (by rfl) ⟨597689, by rfl⟩ : syracuseStep 796919 = 1195379) B1195379
theorem B1190159 : Blo 527800 1190159 := bstep (se 1 (by rfl) ⟨892619, by rfl⟩ : syracuseStep 1190159 = 1785239) B1785239
theorem B796943 : Blo 527800 796943 := bstep (se 1 (by rfl) ⟨597707, by rfl⟩ : syracuseStep 796943 = 1195415) B1195415
theorem B1190177 : Blo 527800 1190177 := bstep (se 2 (by rfl) ⟨446316, by rfl⟩ : syracuseStep 1190177 = 892633) B892633
theorem B796985 : Blo 527800 796985 := bstep (se 2 (by rfl) ⟨298869, by rfl⟩ : syracuseStep 796985 = 597739) B597739
theorem B6465851 : Blo 527800 6465851 := bstep (se 1 (by rfl) ⟨4849388, by rfl⟩ : syracuseStep 6465851 = 9698777) B9698777
theorem B895367 : Blo 527800 895367 := bstep (se 1 (by rfl) ⟨671525, by rfl⟩ : syracuseStep 895367 = 1343051) B1343051
theorem B797063 : Blo 527800 797063 := bstep (se 1 (by rfl) ⟨597797, by rfl⟩ : syracuseStep 797063 = 1195595) B1195595
theorem B797099 : Blo 527800 797099 := bstep (se 1 (by rfl) ⟨597824, by rfl⟩ : syracuseStep 797099 = 1195649) B1195649
theorem B797129 : Blo 527800 797129 := bstep (se 2 (by rfl) ⟨298923, by rfl⟩ : syracuseStep 797129 = 597847) B597847
theorem B764407 : Blo 527800 764407 := bstep (se 1 (by rfl) ⟨573305, by rfl⟩ : syracuseStep 764407 = 1146611) B1146611
theorem B797243 : Blo 527800 797243 := bstep (se 1 (by rfl) ⟨597932, by rfl⟩ : syracuseStep 797243 = 1195865) B1195865
theorem B1190519 : Blo 527800 1190519 := bstep (se 1 (by rfl) ⟨892889, by rfl⟩ : syracuseStep 1190519 = 1785779) B1785779
theorem B797303 : Blo 527800 797303 := bstep (se 1 (by rfl) ⟨597977, by rfl⟩ : syracuseStep 797303 = 1195955) B1195955
theorem B797327 : Blo 527800 797327 := bstep (se 1 (by rfl) ⟨597995, by rfl⟩ : syracuseStep 797327 = 1195991) B1195991
theorem B797369 : Blo 527800 797369 := bstep (se 2 (by rfl) ⟨299013, by rfl⟩ : syracuseStep 797369 = 598027) B598027
theorem B797447 : Blo 527800 797447 := bstep (se 1 (by rfl) ⟨598085, by rfl⟩ : syracuseStep 797447 = 1196171) B1196171
theorem B1190699 : Blo 527800 1190699 := bstep (se 1 (by rfl) ⟨893024, by rfl⟩ : syracuseStep 1190699 = 1786049) B1786049
theorem B797483 : Blo 527800 797483 := bstep (se 1 (by rfl) ⟨598112, by rfl⟩ : syracuseStep 797483 = 1196225) B1196225
theorem B1715003 : Blo 527800 1715003 := bstep (se 1 (by rfl) ⟨1286252, by rfl⟩ : syracuseStep 1715003 = 2572505) B2572505
theorem B797513 : Blo 527800 797513 := bstep (se 2 (by rfl) ⟨299067, by rfl⟩ : syracuseStep 797513 = 598135) B598135
theorem B797627 : Blo 527800 797627 := bstep (se 1 (by rfl) ⟨598220, by rfl⟩ : syracuseStep 797627 = 1196441) B1196441
theorem B797687 : Blo 527800 797687 := bstep (se 1 (by rfl) ⟨598265, by rfl⟩ : syracuseStep 797687 = 1196531) B1196531
theorem B896015 : Blo 527800 896015 := bstep (se 1 (by rfl) ⟨672011, by rfl⟩ : syracuseStep 896015 = 1344023) B1344023
theorem B3025943 : Blo 527800 3025943 := bstep (se 1 (by rfl) ⟨2269457, by rfl⟩ : syracuseStep 3025943 = 4538915) B4538915
theorem B5450885 : Blo 527800 5450885 := bstep (se 4 (by rfl) ⟨511020, by rfl⟩ : syracuseStep 5450885 = 1022041) B1022041
theorem B1191059 : Blo 527800 1191059 := bstep (se 1 (by rfl) ⟨893294, by rfl⟩ : syracuseStep 1191059 = 1786589) B1786589
theorem B1191113 : Blo 527800 1191113 := bstep (se 2 (by rfl) ⟨446667, by rfl⟩ : syracuseStep 1191113 = 893335) B893335
theorem B2010521 : Blo 527800 2010521 := bstep (se 2 (by rfl) ⟨753945, by rfl⟩ : syracuseStep 2010521 = 1507891) B1507891
theorem B3026443 : Blo 527800 3026443 := bstep (se 1 (by rfl) ⟨2269832, by rfl⟩ : syracuseStep 3026443 = 4539665) B4539665
theorem B896555 : Blo 527800 896555 := bstep (se 1 (by rfl) ⟨672416, by rfl⟩ : syracuseStep 896555 = 1344833) B1344833
theorem B1912577 : Blo 527800 1912577 := bstep (se 2 (by rfl) ⟨717216, by rfl⟩ : syracuseStep 1912577 = 1434433) B1434433
theorem B1191815 : Blo 527800 1191815 := bstep (se 1 (by rfl) ⟨893861, by rfl⟩ : syracuseStep 1191815 = 1787723) B1787723
theorem B896953 : Blo 527800 896953 := bstep (se 2 (by rfl) ⟨336357, by rfl⟩ : syracuseStep 896953 = 672715) B672715
theorem B634811 : Blo 527800 634811 := bstep (se 1 (by rfl) ⟨476108, by rfl⟩ : syracuseStep 634811 = 952217) B952217
theorem B5451781 : Blo 527800 5451781 := bstep (se 4 (by rfl) ⟨511104, by rfl⟩ : syracuseStep 5451781 = 1022209) B1022209
theorem B1191995 : Blo 527800 1191995 := bstep (se 1 (by rfl) ⟨893996, by rfl⟩ : syracuseStep 1191995 = 1787993) B1787993
theorem B1192121 : Blo 527800 1192121 := bstep (se 2 (by rfl) ⟨447045, by rfl⟩ : syracuseStep 1192121 = 894091) B894091
theorem B635143 : Blo 527800 635143 := bstep (se 1 (by rfl) ⟨476357, by rfl⟩ : syracuseStep 635143 = 952715) B952715
theorem B1192463 : Blo 527800 1192463 := bstep (se 1 (by rfl) ⟨894347, by rfl⟩ : syracuseStep 1192463 = 1788695) B1788695
theorem B1192481 : Blo 527800 1192481 := bstep (se 2 (by rfl) ⟨447180, by rfl⟩ : syracuseStep 1192481 = 894361) B894361
theorem B635527 : Blo 527800 635527 := bstep (se 1 (by rfl) ⟨476645, by rfl⟩ : syracuseStep 635527 = 953291) B953291
theorem B668407 : Blo 527800 668407 := bstep (se 1 (by rfl) ⟨501305, by rfl⟩ : syracuseStep 668407 = 1002611) B1002611
theorem B1192823 : Blo 527800 1192823 := bstep (se 1 (by rfl) ⟨894617, by rfl⟩ : syracuseStep 1192823 = 1789235) B1789235
theorem B7648181 : Blo 527800 7648181 := bstep (se 5 (by rfl) ⟨358508, by rfl⟩ : syracuseStep 7648181 = 717017) B717017
theorem B1127467 : Blo 527800 1127467 := bstep (se 1 (by rfl) ⟨845600, by rfl⟩ : syracuseStep 1127467 = 1691201) B1691201
theorem B1193003 : Blo 527800 1193003 := bstep (se 1 (by rfl) ⟨894752, by rfl⟩ : syracuseStep 1193003 = 1789505) B1789505
theorem B668731 : Blo 527800 668731 := bstep (se 1 (by rfl) ⟨501548, by rfl⟩ : syracuseStep 668731 = 1003097) B1003097
theorem B603451 : Blo 527800 603451 := bstep (se 1 (by rfl) ⟨452588, by rfl⟩ : syracuseStep 603451 = 905177) B905177
theorem B1783187 : Blo 527800 1783187 := bstep (se 1 (by rfl) ⟨1337390, by rfl⟩ : syracuseStep 1783187 = 2674781) B2674781
theorem B1193363 : Blo 527800 1193363 := bstep (se 1 (by rfl) ⟨895022, by rfl⟩ : syracuseStep 1193363 = 1790045) B1790045
theorem B1193417 : Blo 527800 1193417 := bstep (se 2 (by rfl) ⟨447531, by rfl⟩ : syracuseStep 1193417 = 895063) B895063
theorem B3028427 : Blo 527800 3028427 := bstep (se 1 (by rfl) ⟨2271320, by rfl⟩ : syracuseStep 3028427 = 4542641) B4542641
theorem B3225091 : Blo 527800 3225091 := bstep (se 1 (by rfl) ⟨2418818, by rfl⟩ : syracuseStep 3225091 = 4837637) B4837637
theorem B4011929 : Blo 527800 4011929 := bstep (se 2 (by rfl) ⟨1504473, by rfl⟩ : syracuseStep 4011929 = 3008947) B3008947
theorem B669703 : Blo 527800 669703 := bstep (se 1 (by rfl) ⟨502277, by rfl⟩ : syracuseStep 669703 = 1004555) B1004555
theorem B1914941 : Blo 527800 1914941 := bstep (se 3 (by rfl) ⟨359051, by rfl⟩ : syracuseStep 1914941 = 718103) B718103
theorem B2275415 : Blo 527800 2275415 := bstep (se 1 (by rfl) ⟨1706561, by rfl⟩ : syracuseStep 2275415 = 3413123) B3413123
theorem B1194119 : Blo 527800 1194119 := bstep (se 1 (by rfl) ⟨895589, by rfl⟩ : syracuseStep 1194119 = 1791179) B1791179
theorem B1128595 : Blo 527800 1128595 := bstep (se 1 (by rfl) ⟨846446, by rfl⟩ : syracuseStep 1128595 = 1692893) B1692893
theorem B1194299 : Blo 527800 1194299 := bstep (se 1 (by rfl) ⟨895724, by rfl⟩ : syracuseStep 1194299 = 1791449) B1791449
theorem B1292663 : Blo 527800 1292663 := bstep (se 1 (by rfl) ⟨969497, by rfl⟩ : syracuseStep 1292663 = 1938995) B1938995
theorem B1915289 : Blo 527800 1915289 := bstep (se 2 (by rfl) ⟨718233, by rfl⟩ : syracuseStep 1915289 = 1436467) B1436467
theorem B670123 : Blo 527800 670123 := bstep (se 1 (by rfl) ⟨502592, by rfl⟩ : syracuseStep 670123 = 1005185) B1005185
theorem B1194425 : Blo 527800 1194425 := bstep (se 2 (by rfl) ⟨447909, by rfl⟩ : syracuseStep 1194425 = 895819) B895819
theorem B670351 : Blo 527800 670351 := bstep (se 1 (by rfl) ⟨502763, by rfl⟩ : syracuseStep 670351 = 1005527) B1005527
theorem B1784591 : Blo 527800 1784591 := bstep (se 1 (by rfl) ⟨1338443, by rfl⟩ : syracuseStep 1784591 = 2676887) B2676887
theorem B1194767 : Blo 527800 1194767 := bstep (se 1 (by rfl) ⟨896075, by rfl⟩ : syracuseStep 1194767 = 1792151) B1792151
theorem B1194785 : Blo 527800 1194785 := bstep (se 2 (by rfl) ⟨448044, by rfl⟩ : syracuseStep 1194785 = 896089) B896089
theorem B3390245 : Blo 527800 3390245 := bstep (se 4 (by rfl) ⟨317835, by rfl⟩ : syracuseStep 3390245 = 635671) B635671
theorem B2014105 : Blo 527800 2014105 := bstep (se 2 (by rfl) ⟨755289, by rfl⟩ : syracuseStep 2014105 = 1510579) B1510579
theorem B1784861 : Blo 527800 1784861 := bstep (se 3 (by rfl) ⟨334661, by rfl⟩ : syracuseStep 1784861 = 669323) B669323
theorem B605243 : Blo 527800 605243 := bstep (se 1 (by rfl) ⟨453932, by rfl⟩ : syracuseStep 605243 = 907865) B907865
theorem B1195127 : Blo 527800 1195127 := bstep (se 1 (by rfl) ⟨896345, by rfl⟩ : syracuseStep 1195127 = 1792691) B1792691
theorem B2014409 : Blo 527800 2014409 := bstep (se 2 (by rfl) ⟨755403, by rfl⟩ : syracuseStep 2014409 = 1510807) B1510807
theorem B1195307 : Blo 527800 1195307 := bstep (se 1 (by rfl) ⟨896480, by rfl⟩ : syracuseStep 1195307 = 1792961) B1792961
theorem B1359191 : Blo 527800 1359191 := bstep (se 1 (by rfl) ⟨1019393, by rfl⟩ : syracuseStep 1359191 = 2038787) B2038787
theorem B671095 : Blo 527800 671095 := bstep (se 1 (by rfl) ⟨503321, by rfl⟩ : syracuseStep 671095 = 1006643) B1006643
theorem B1195667 : Blo 527800 1195667 := bstep (se 1 (by rfl) ⟨896750, by rfl⟩ : syracuseStep 1195667 = 1793501) B1793501
theorem B671419 : Blo 527800 671419 := bstep (se 1 (by rfl) ⟨503564, by rfl⟩ : syracuseStep 671419 = 1007129) B1007129
theorem B1195721 : Blo 527800 1195721 := bstep (se 2 (by rfl) ⟨448395, by rfl⟩ : syracuseStep 1195721 = 896791) B896791
theorem B4013873 : Blo 527800 4013873 := bstep (se 2 (by rfl) ⟨1505202, by rfl⟩ : syracuseStep 4013873 = 3010405) B3010405
theorem B2015351 : Blo 527800 2015351 := bstep (se 1 (by rfl) ⟨1511513, by rfl⟩ : syracuseStep 2015351 = 3023027) B3023027
theorem B671915 : Blo 527800 671915 := bstep (se 1 (by rfl) ⟨503936, by rfl⟩ : syracuseStep 671915 = 1007873) B1007873
theorem B1360073 : Blo 527800 1360073 := bstep (se 2 (by rfl) ⟨510027, by rfl⟩ : syracuseStep 1360073 = 1020055) B1020055
theorem B1196423 : Blo 527800 1196423 := bstep (se 1 (by rfl) ⟨897317, by rfl⟩ : syracuseStep 1196423 = 1794635) B1794635
theorem B1786265 : Blo 527800 1786265 := bstep (se 2 (by rfl) ⟨669849, by rfl⟩ : syracuseStep 1786265 = 1339699) B1339699
theorem B2867723 : Blo 527800 2867723 := bstep (se 1 (by rfl) ⟨2150792, by rfl⟩ : syracuseStep 2867723 = 4301585) B4301585
theorem B1720919 : Blo 527800 1720919 := bstep (se 1 (by rfl) ⟨1290689, by rfl⟩ : syracuseStep 1720919 = 2581379) B2581379
theorem B2867831 : Blo 527800 2867831 := bstep (se 1 (by rfl) ⟨2150873, by rfl⟩ : syracuseStep 2867831 = 4301747) B4301747
theorem B672391 : Blo 527800 672391 := bstep (se 1 (by rfl) ⟨504293, by rfl⟩ : syracuseStep 672391 = 1008587) B1008587
theorem B15287129 : Blo 527800 15287129 := bstep (se 2 (by rfl) ⟨5732673, by rfl⟩ : syracuseStep 15287129 = 11465347) B11465347
theorem B2016323 : Blo 527800 2016323 := bstep (se 1 (by rfl) ⟨1512242, by rfl⟩ : syracuseStep 2016323 = 3024485) B3024485
theorem B1786967 : Blo 527800 1786967 := bstep (se 1 (by rfl) ⟨1340225, by rfl⟩ : syracuseStep 1786967 = 2680451) B2680451
theorem B672887 : Blo 527800 672887 := bstep (se 1 (by rfl) ⟨504665, by rfl⟩ : syracuseStep 672887 = 1009331) B1009331
theorem B673039 : Blo 527800 673039 := bstep (se 1 (by rfl) ⟨504779, by rfl⟩ : syracuseStep 673039 = 1009559) B1009559
theorem B2672189 : Blo 527800 2672189 := bstep (se 3 (by rfl) ⟨501035, by rfl⟩ : syracuseStep 2672189 = 1002071) B1002071
theorem B1787453 : Blo 527800 1787453 := bstep (se 3 (by rfl) ⟨335147, by rfl⟩ : syracuseStep 1787453 = 670295) B670295
theorem B4572929 : Blo 527800 4572929 := bstep (se 2 (by rfl) ⟨1714848, by rfl⟩ : syracuseStep 4572929 = 3429697) B3429697
theorem B2148211 : Blo 527800 2148211 := bstep (se 1 (by rfl) ⟨1611158, by rfl⟩ : syracuseStep 2148211 = 3222317) B3222317
theorem B1132559 : Blo 527800 1132559 := bstep (se 1 (by rfl) ⟨849419, by rfl⟩ : syracuseStep 1132559 = 1698839) B1698839
theorem B1132679 : Blo 527800 1132679 := bstep (se 1 (by rfl) ⟨849509, by rfl⟩ : syracuseStep 1132679 = 1699019) B1699019
theorem B3360941 : Blo 527800 3360941 := bstep (se 3 (by rfl) ⟨630176, by rfl⟩ : syracuseStep 3360941 = 1260353) B1260353
theorem B1132859 : Blo 527800 1132859 := bstep (se 1 (by rfl) ⟨849644, by rfl⟩ : syracuseStep 1132859 = 1699289) B1699289
theorem B2017993 : Blo 527800 2017993 := bstep (se 2 (by rfl) ⟨756747, by rfl⟩ : syracuseStep 2017993 = 1513495) B1513495
theorem B2542337 : Blo 527800 2542337 := bstep (se 2 (by rfl) ⟨953376, by rfl⟩ : syracuseStep 2542337 = 1906753) B1906753
theorem B1133345 : Blo 527800 1133345 := bstep (se 2 (by rfl) ⟨425004, by rfl⟩ : syracuseStep 1133345 = 850009) B850009
theorem B1788857 : Blo 527800 1788857 := bstep (se 2 (by rfl) ⟨670821, by rfl⟩ : syracuseStep 1788857 = 1341643) B1341643
theorem B2673971 : Blo 527800 2673971 := bstep (se 1 (by rfl) ⟨2005478, by rfl⟩ : syracuseStep 2673971 = 4010957) B4010957
theorem B1002937 : Blo 527800 1002937 := bstep (se 2 (by rfl) ⟨376101, by rfl⟩ : syracuseStep 1002937 = 752203) B752203
theorem B1789451 : Blo 527800 1789451 := bstep (se 1 (by rfl) ⟨1342088, by rfl⟩ : syracuseStep 1789451 = 2684177) B2684177
theorem B2543147 : Blo 527800 2543147 := bstep (se 1 (by rfl) ⟨1907360, by rfl⟩ : syracuseStep 2543147 = 3814721) B3814721
theorem B10145357 : Blo 527800 10145357 := bstep (se 3 (by rfl) ⟨1902254, by rfl⟩ : syracuseStep 10145357 = 3804509) B3804509
theorem B2674295 : Blo 527800 2674295 := bstep (se 1 (by rfl) ⟨2005721, by rfl⟩ : syracuseStep 2674295 = 4011443) B4011443
theorem B1789559 : Blo 527800 1789559 := bstep (se 1 (by rfl) ⟨1342169, by rfl⟩ : syracuseStep 1789559 = 2684339) B2684339
theorem B1134199 : Blo 527800 1134199 := bstep (se 1 (by rfl) ⟨850649, by rfl⟩ : syracuseStep 1134199 = 1701299) B1701299
theorem B1003279 : Blo 527800 1003279 := bstep (se 1 (by rfl) ⟨752459, by rfl⟩ : syracuseStep 1003279 = 1504919) B1504919
theorem B806699 : Blo 527800 806699 := bstep (se 1 (by rfl) ⟨605024, by rfl⟩ : syracuseStep 806699 = 1210049) B1210049
theorem B1790153 : Blo 527800 1790153 := bstep (se 2 (by rfl) ⟨671307, by rfl⟩ : syracuseStep 1790153 = 1342615) B1342615
theorem B2675267 : Blo 527800 2675267 := bstep (se 1 (by rfl) ⟨2006450, by rfl⟩ : syracuseStep 2675267 = 4012901) B4012901
theorem B2871895 : Blo 527800 2871895 := bstep (se 1 (by rfl) ⟨2153921, by rfl⟩ : syracuseStep 2871895 = 4307843) B4307843
theorem B1004167 : Blo 527800 1004167 := bstep (se 1 (by rfl) ⟨753125, by rfl⟩ : syracuseStep 1004167 = 1506251) B1506251
theorem B1692431 : Blo 527800 1692431 := bstep (se 1 (by rfl) ⟨1269323, by rfl⟩ : syracuseStep 1692431 = 2538647) B2538647
theorem B2544473 : Blo 527800 2544473 := bstep (se 2 (by rfl) ⟨954177, by rfl⟩ : syracuseStep 2544473 = 1908355) B1908355
theorem B2675591 : Blo 527800 2675591 := bstep (se 1 (by rfl) ⟨2006693, by rfl⟩ : syracuseStep 2675591 = 4013387) B4013387
theorem B1790855 : Blo 527800 1790855 := bstep (se 1 (by rfl) ⟨1343141, by rfl⟩ : syracuseStep 1790855 = 2686283) B2686283
theorem B2544529 : Blo 527800 2544529 := bstep (se 2 (by rfl) ⟨954198, by rfl⟩ : syracuseStep 2544529 = 1908397) B1908397
theorem B2544643 : Blo 527800 2544643 := bstep (se 1 (by rfl) ⟨1908482, by rfl⟩ : syracuseStep 2544643 = 3816965) B3816965
theorem B2577419 : Blo 527800 2577419 := bstep (se 1 (by rfl) ⟨1933064, by rfl⟩ : syracuseStep 2577419 = 3866129) B3866129
theorem B1791233 : Blo 527800 1791233 := bstep (se 2 (by rfl) ⟨671712, by rfl⟩ : syracuseStep 1791233 = 1343425) B1343425
theorem B1430843 : Blo 527800 1430843 := bstep (se 1 (by rfl) ⟨1073132, by rfl⟩ : syracuseStep 1430843 = 2146265) B2146265
theorem B1431449 : Blo 527800 1431449 := bstep (se 2 (by rfl) ⟨536793, by rfl⟩ : syracuseStep 1431449 = 1073587) B1073587
theorem B2709469 : Blo 527800 2709469 := bstep (se 3 (by rfl) ⟨508025, by rfl⟩ : syracuseStep 2709469 = 1016051) B1016051
theorem B4118539 : Blo 527800 4118539 := bstep (se 1 (by rfl) ⟨3088904, by rfl⟩ : syracuseStep 4118539 = 6177809) B6177809
theorem B1792043 : Blo 527800 1792043 := bstep (se 1 (by rfl) ⟨1344032, by rfl⟩ : syracuseStep 1792043 = 2688065) B2688065
theorem B4282541 : Blo 527800 4282541 := bstep (se 3 (by rfl) ⟨802976, by rfl⟩ : syracuseStep 4282541 = 1605953) B1605953
theorem B1005959 : Blo 527800 1005959 := bstep (se 1 (by rfl) ⟨754469, by rfl⟩ : syracuseStep 1005959 = 1508939) B1508939
theorem B9067301 : Blo 527800 9067301 := bstep (se 4 (by rfl) ⟨850059, by rfl⟩ : syracuseStep 9067301 = 1700119) B1700119
theorem B5233709 : Blo 527800 5233709 := bstep (se 3 (by rfl) ⟨981320, by rfl⟩ : syracuseStep 5233709 = 1962641) B1962641
theorem B1793339 : Blo 527800 1793339 := bstep (se 1 (by rfl) ⟨1345004, by rfl⟩ : syracuseStep 1793339 = 2690009) B2690009
theorem B4021649 : Blo 527800 4021649 := bstep (se 2 (by rfl) ⟨1508118, by rfl⟩ : syracuseStep 4021649 = 3016237) B3016237
theorem B2416139 : Blo 527800 2416139 := bstep (se 1 (by rfl) ⟨1812104, by rfl⟩ : syracuseStep 2416139 = 3624209) B3624209
theorem B5791297 : Blo 527800 5791297 := bstep (se 2 (by rfl) ⟨2171736, by rfl⟩ : syracuseStep 5791297 = 4343473) B4343473
theorem B1793825 : Blo 527800 1793825 := bstep (se 2 (by rfl) ⟨672684, by rfl⟩ : syracuseStep 1793825 = 1345369) B1345369
theorem B1204027 : Blo 527800 1204027 := bstep (se 1 (by rfl) ⟨903020, by rfl⟩ : syracuseStep 1204027 = 1806041) B1806041
theorem B1072955 : Blo 527800 1072955 := bstep (se 1 (by rfl) ⟨804716, by rfl⟩ : syracuseStep 1072955 = 1609433) B1609433
theorem B12443543 : Blo 527800 12443543 := bstep (se 1 (by rfl) ⟨9332657, by rfl⟩ : syracuseStep 12443543 = 18665315) B18665315
theorem B2679155 : Blo 527800 2679155 := bstep (se 1 (by rfl) ⟨2009366, by rfl⟩ : syracuseStep 2679155 = 4018733) B4018733
theorem B1794419 : Blo 527800 1794419 := bstep (se 1 (by rfl) ⟨1345814, by rfl⟩ : syracuseStep 1794419 = 2691629) B2691629
theorem B1270169 : Blo 527800 1270169 := bstep (se 2 (by rfl) ⟨476313, by rfl⟩ : syracuseStep 1270169 = 952627) B952627
theorem B2712017 : Blo 527800 2712017 := bstep (se 2 (by rfl) ⟨1017006, by rfl⟩ : syracuseStep 2712017 = 2034013) B2034013
theorem B1008443 : Blo 527800 1008443 := bstep (se 1 (by rfl) ⟨756332, by rfl⟩ : syracuseStep 1008443 = 1512665) B1512665
theorem B2679641 : Blo 527800 2679641 := bstep (se 2 (by rfl) ⟨1004865, by rfl⟩ : syracuseStep 2679641 = 2009731) B2009731
theorem B1336439 : Blo 527800 1336439 := bstep (se 1 (by rfl) ⟨1002329, by rfl⟩ : syracuseStep 1336439 = 2004659) B2004659
theorem B1008929 : Blo 527800 1008929 := bstep (se 2 (by rfl) ⟨378348, by rfl⟩ : syracuseStep 1008929 = 756697) B756697
theorem B48850289 : Blo 527800 48850289 := bstep (se 2 (by rfl) ⟨18318858, by rfl⟩ : syracuseStep 48850289 = 36637717) B36637717
theorem B4024079 : Blo 527800 4024079 := bstep (se 1 (by rfl) ⟨3018059, by rfl⟩ : syracuseStep 4024079 = 6036119) B6036119
theorem B1075079 : Blo 527800 1075079 := bstep (se 1 (by rfl) ⟨806309, by rfl⟩ : syracuseStep 1075079 = 1612619) B1612619
theorem B3401675 : Blo 527800 3401675 := bstep (se 1 (by rfl) ⟨2551256, by rfl⟩ : syracuseStep 3401675 = 5102513) B5102513
theorem B5433389 : Blo 527800 5433389 := bstep (se 3 (by rfl) ⟨1018760, by rfl⟩ : syracuseStep 5433389 = 2037521) B2037521
theorem B1337431 : Blo 527800 1337431 := bstep (se 1 (by rfl) ⟨1003073, by rfl⟩ : syracuseStep 1337431 = 2006147) B2006147
theorem B10152053 : Blo 527800 10152053 := bstep (se 5 (by rfl) ⟨475877, by rfl⟩ : syracuseStep 10152053 = 951755) B951755
theorem B6514805 : Blo 527800 6514805 := bstep (se 5 (by rfl) ⟨305381, by rfl⟩ : syracuseStep 6514805 = 610763) B610763
theorem B1697993 : Blo 527800 1697993 := bstep (se 2 (by rfl) ⟨636747, by rfl⟩ : syracuseStep 1697993 = 1273495) B1273495
theorem B846139 : Blo 527800 846139 := bstep (se 1 (by rfl) ⟨634604, by rfl⟩ : syracuseStep 846139 = 1269209) B1269209
theorem B1632599 : Blo 527800 1632599 := bstep (se 1 (by rfl) ⟨1224449, by rfl⟩ : syracuseStep 1632599 = 2448899) B2448899
theorem B1337735 : Blo 527800 1337735 := bstep (se 1 (by rfl) ⟨1003301, by rfl⟩ : syracuseStep 1337735 = 2006603) B2006603
theorem B2550163 : Blo 527800 2550163 := bstep (se 1 (by rfl) ⟨1912622, by rfl⟩ : syracuseStep 2550163 = 3825245) B3825245
theorem B1337867 : Blo 527800 1337867 := bstep (se 1 (by rfl) ⟨1003400, by rfl⟩ : syracuseStep 1337867 = 2006801) B2006801
theorem B2255617 : Blo 527800 2255617 := bstep (se 2 (by rfl) ⟨845856, by rfl⟩ : syracuseStep 2255617 = 1691713) B1691713
theorem B2681747 : Blo 527800 2681747 := bstep (se 1 (by rfl) ⟨2011310, by rfl⟩ : syracuseStep 2681747 = 4022621) B4022621
theorem B1338383 : Blo 527800 1338383 := bstep (se 1 (by rfl) ⟨1003787, by rfl⟩ : syracuseStep 1338383 = 2007575) B2007575
theorem B1305659 : Blo 527800 1305659 := bstep (se 1 (by rfl) ⟨979244, by rfl⟩ : syracuseStep 1305659 = 1958489) B1958489
theorem B1338515 : Blo 527800 1338515 := bstep (se 1 (by rfl) ⟨1003886, by rfl⟩ : syracuseStep 1338515 = 2007773) B2007773
theorem B4517795 : Blo 527800 4517795 := bstep (se 1 (by rfl) ⟨3388346, by rfl⟩ : syracuseStep 4517795 = 6776693) B6776693
theorem B14479307 : Blo 527800 14479307 := bstep (se 1 (by rfl) ⟨10859480, by rfl⟩ : syracuseStep 14479307 = 21718961) B21718961
theorem B3010679 : Blo 527800 3010679 := bstep (se 1 (by rfl) ⟨2258009, by rfl⟩ : syracuseStep 3010679 = 4516019) B4516019
theorem B1077383 : Blo 527800 1077383 := bstep (se 1 (by rfl) ⟨808037, by rfl⟩ : syracuseStep 1077383 = 1616075) B1616075
theorem B1339649 : Blo 527800 1339649 := bstep (se 2 (by rfl) ⟨502368, by rfl⟩ : syracuseStep 1339649 = 1004737) B1004737
theorem B6779153 : Blo 527800 6779153 := bstep (se 2 (by rfl) ⟨2542182, by rfl⟩ : syracuseStep 6779153 = 5084365) B5084365
theorem B1503517 : Blo 527800 1503517 := bstep (se 3 (by rfl) ⟨281909, by rfl⟩ : syracuseStep 1503517 = 563819) B563819
theorem B3010931 : Blo 527800 3010931 := bstep (se 1 (by rfl) ⟨2258198, by rfl⟩ : syracuseStep 3010931 = 4516397) B4516397
theorem B11497949 : Blo 527800 11497949 := bstep (se 3 (by rfl) ⟨2155865, by rfl⟩ : syracuseStep 11497949 = 4311731) B4311731
theorem B1503859 : Blo 527800 1503859 := bstep (se 1 (by rfl) ⟨1127894, by rfl⟩ : syracuseStep 1503859 = 2255789) B2255789
theorem B1340023 : Blo 527800 1340023 := bstep (se 1 (by rfl) ⟨1005017, by rfl⟩ : syracuseStep 1340023 = 2010035) B2010035
theorem B5108741 : Blo 527800 5108741 := bstep (se 4 (by rfl) ⟨478944, by rfl⟩ : syracuseStep 5108741 = 957889) B957889
theorem B1340459 : Blo 527800 1340459 := bstep (se 1 (by rfl) ⟨1005344, by rfl⟩ : syracuseStep 1340459 = 2010689) B2010689
theorem B4355309 : Blo 527800 4355309 := bstep (se 3 (by rfl) ⟨816620, by rfl⟩ : syracuseStep 4355309 = 1633241) B1633241
theorem B3405341 : Blo 527800 3405341 := bstep (se 3 (by rfl) ⟨638501, by rfl⟩ : syracuseStep 3405341 = 1277003) B1277003
theorem B5109277 : Blo 527800 5109277 := bstep (se 3 (by rfl) ⟨957989, by rfl⟩ : syracuseStep 5109277 = 1915979) B1915979
theorem B2422561 : Blo 527800 2422561 := bstep (se 2 (by rfl) ⟨908460, by rfl⟩ : syracuseStep 2422561 = 1816921) B1816921
theorem B3012389 : Blo 527800 3012389 := bstep (se 4 (by rfl) ⟨282411, by rfl⟩ : syracuseStep 3012389 = 564823) B564823
theorem B5601061 : Blo 527800 5601061 := bstep (se 4 (by rfl) ⟨525099, by rfl⟩ : syracuseStep 5601061 = 1050199) B1050199
theorem B19363697 : Blo 527800 19363697 := bstep (se 2 (by rfl) ⟨7261386, by rfl⟩ : syracuseStep 19363697 = 14522773) B14522773
theorem B1341299 : Blo 527800 1341299 := bstep (se 1 (by rfl) ⟨1005974, by rfl⟩ : syracuseStep 1341299 = 2011949) B2011949
theorem B1341319 : Blo 527800 1341319 := bstep (se 1 (by rfl) ⟨1005989, by rfl⟩ : syracuseStep 1341319 = 2011979) B2011979
theorem B2684825 : Blo 527800 2684825 := bstep (se 2 (by rfl) ⟨1006809, by rfl⟩ : syracuseStep 2684825 = 2013619) B2013619
theorem B751531 : Blo 527800 751531 := bstep (se 1 (by rfl) ⟨563648, by rfl⟩ : syracuseStep 751531 = 1127297) B1127297
theorem B1964119 : Blo 527800 1964119 := bstep (se 1 (by rfl) ⟨1473089, by rfl⟩ : syracuseStep 1964119 = 2946179) B2946179
theorem B1341593 : Blo 527800 1341593 := bstep (se 2 (by rfl) ⟨503097, by rfl⟩ : syracuseStep 1341593 = 1006195) B1006195
theorem B850105 : Blo 527800 850105 := bstep (se 2 (by rfl) ⟨318789, by rfl⟩ : syracuseStep 850105 = 637579) B637579
theorem B1341755 : Blo 527800 1341755 := bstep (se 1 (by rfl) ⟨1006316, by rfl⟩ : syracuseStep 1341755 = 2012633) B2012633
theorem B21559769 : Blo 527800 21559769 := bstep (se 2 (by rfl) ⟨8084913, by rfl⟩ : syracuseStep 21559769 = 16169827) B16169827
theorem B1341967 : Blo 527800 1341967 := bstep (se 1 (by rfl) ⟨1006475, by rfl⟩ : syracuseStep 1341967 = 2012951) B2012951
theorem B3013321 : Blo 527800 3013321 := bstep (se 2 (by rfl) ⟨1129995, by rfl⟩ : syracuseStep 3013321 = 2259991) B2259991
theorem B1342241 : Blo 527800 1342241 := bstep (se 2 (by rfl) ⟨503340, by rfl⟩ : syracuseStep 1342241 = 1006681) B1006681
theorem B752647 : Blo 527800 752647 := bstep (se 1 (by rfl) ⟨564485, by rfl⟩ : syracuseStep 752647 = 1128971) B1128971
theorem B1506593 : Blo 527800 1506593 := bstep (se 2 (by rfl) ⟨564972, by rfl⟩ : syracuseStep 1506593 = 1129945) B1129945
theorem B1506707 : Blo 527800 1506707 := bstep (se 1 (by rfl) ⟨1130030, by rfl⟩ : syracuseStep 1506707 = 2260061) B2260061
theorem B6028829 : Blo 527800 6028829 := bstep (se 3 (by rfl) ⟨1130405, by rfl⟩ : syracuseStep 6028829 = 2260811) B2260811
theorem B1343243 : Blo 527800 1343243 := bstep (se 1 (by rfl) ⟨1007432, by rfl⟩ : syracuseStep 1343243 = 2014865) B2014865
theorem B753467 : Blo 527800 753467 := bstep (se 1 (by rfl) ⟨565100, by rfl⟩ : syracuseStep 753467 = 1130201) B1130201
theorem B1343567 : Blo 527800 1343567 := bstep (se 1 (by rfl) ⟨1007675, by rfl⟩ : syracuseStep 1343567 = 2015351) B2015351
theorem B1507709 : Blo 527800 1507709 := bstep (se 3 (by rfl) ⟨282695, by rfl⟩ : syracuseStep 1507709 = 565391) B565391
theorem B1147279 : Blo 527800 1147279 := bstep (se 1 (by rfl) ⟨860459, by rfl⟩ : syracuseStep 1147279 = 1720919) B1720919
theorem B10191419 : Blo 527800 10191419 := bstep (se 1 (by rfl) ⟨7643564, by rfl⟩ : syracuseStep 10191419 = 15287129) B15287129
theorem B1508051 : Blo 527800 1508051 := bstep (se 1 (by rfl) ⟨1131038, by rfl⟩ : syracuseStep 1508051 = 2262077) B2262077
theorem B1344215 : Blo 527800 1344215 := bstep (se 1 (by rfl) ⟨1008161, by rfl⟩ : syracuseStep 1344215 = 2016323) B2016323
theorem B3048619 : Blo 527800 3048619 := bstep (se 1 (by rfl) ⟨2286464, by rfl⟩ : syracuseStep 3048619 = 4572929) B4572929
theorem B3212567 : Blo 527800 3212567 := bstep (se 1 (by rfl) ⟨2409425, by rfl⟩ : syracuseStep 3212567 = 4818851) B4818851
theorem B755039 : Blo 527800 755039 := bstep (se 1 (by rfl) ⟨566279, by rfl⟩ : syracuseStep 755039 = 1132559) B1132559
theorem B1017193 : Blo 527800 1017193 := bstep (se 2 (by rfl) ⟨381447, by rfl⟩ : syracuseStep 1017193 = 762895) B762895
theorem B755119 : Blo 527800 755119 := bstep (se 1 (by rfl) ⟨566339, by rfl⟩ : syracuseStep 755119 = 1132679) B1132679
theorem B755239 : Blo 527800 755239 := bstep (se 1 (by rfl) ⟨566429, by rfl⟩ : syracuseStep 755239 = 1132859) B1132859
theorem B2688551 : Blo 527800 2688551 := bstep (se 1 (by rfl) ⟨2016413, by rfl⟩ : syracuseStep 2688551 = 4032827) B4032827
theorem B1017593 : Blo 527800 1017593 := bstep (se 2 (by rfl) ⟨381597, by rfl⟩ : syracuseStep 1017593 = 763195) B763195
theorem B755563 : Blo 527800 755563 := bstep (se 1 (by rfl) ⟨566672, by rfl⟩ : syracuseStep 755563 = 1133345) B1133345
theorem B1509623 : Blo 527800 1509623 := bstep (se 1 (by rfl) ⟨1132217, by rfl⟩ : syracuseStep 1509623 = 2264435) B2264435
theorem B920585 : Blo 527800 920585 := bstep (se 2 (by rfl) ⟨345219, by rfl⟩ : syracuseStep 920585 = 690439) B690439
theorem B5049539 : Blo 527800 5049539 := bstep (se 1 (by rfl) ⟨3787154, by rfl⟩ : syracuseStep 5049539 = 7574309) B7574309
theorem B3214583 : Blo 527800 3214583 := bstep (se 1 (by rfl) ⟨2410937, by rfl⟩ : syracuseStep 3214583 = 4821875) B4821875
theorem B1019209 : Blo 527800 1019209 := bstep (se 2 (by rfl) ⟨382203, by rfl⟩ : syracuseStep 1019209 = 764407) B764407
theorem B527815 : Blo 527800 527815 := bstep (se 1 (by rfl) ⟨395861, by rfl⟩ : syracuseStep 527815 = 791723) B791723
theorem B527835 : Blo 527800 527835 := bstep (se 1 (by rfl) ⟨395876, by rfl⟩ : syracuseStep 527835 = 791753) B791753
theorem B527911 : Blo 527800 527911 := bstep (se 1 (by rfl) ⟨395933, by rfl⟩ : syracuseStep 527911 = 791867) B791867
theorem B527951 : Blo 527800 527951 := bstep (se 1 (by rfl) ⟨395963, by rfl⟩ : syracuseStep 527951 = 791927) B791927
theorem B527967 : Blo 527800 527967 := bstep (se 1 (by rfl) ⟨395975, by rfl⟩ : syracuseStep 527967 = 791951) B791951
theorem B2690657 : Blo 527800 2690657 := bstep (se 2 (by rfl) ⟨1008996, by rfl⟩ : syracuseStep 2690657 = 2017993) B2017993
theorem B527995 : Blo 527800 527995 := bstep (se 1 (by rfl) ⟨395996, by rfl⟩ : syracuseStep 527995 = 791993) B791993
theorem B528047 : Blo 527800 528047 := bstep (se 1 (by rfl) ⟨396035, by rfl⟩ : syracuseStep 528047 = 792071) B792071
theorem B528071 : Blo 527800 528071 := bstep (se 1 (by rfl) ⟨396053, by rfl⟩ : syracuseStep 528071 = 792107) B792107
theorem B528091 : Blo 527800 528091 := bstep (se 1 (by rfl) ⟨396068, by rfl⟩ : syracuseStep 528091 = 792137) B792137
theorem B4034285 : Blo 527800 4034285 := bstep (se 3 (by rfl) ⟨756428, by rfl⟩ : syracuseStep 4034285 = 1512857) B1512857
theorem B528167 : Blo 527800 528167 := bstep (se 1 (by rfl) ⟨396125, by rfl⟩ : syracuseStep 528167 = 792251) B792251
theorem B528207 : Blo 527800 528207 := bstep (se 1 (by rfl) ⟨396155, by rfl⟩ : syracuseStep 528207 = 792311) B792311
theorem B528223 : Blo 527800 528223 := bstep (se 1 (by rfl) ⟨396167, by rfl⟩ : syracuseStep 528223 = 792335) B792335
theorem B528251 : Blo 527800 528251 := bstep (se 1 (by rfl) ⟨396188, by rfl⟩ : syracuseStep 528251 = 792377) B792377
theorem B528303 : Blo 527800 528303 := bstep (se 1 (by rfl) ⟨396227, by rfl⟩ : syracuseStep 528303 = 792455) B792455
theorem B954299 : Blo 527800 954299 := bstep (se 1 (by rfl) ⟨715724, by rfl⟩ : syracuseStep 954299 = 1431449) B1431449
theorem B528327 : Blo 527800 528327 := bstep (se 1 (by rfl) ⟨396245, by rfl⟩ : syracuseStep 528327 = 792491) B792491
theorem B528347 : Blo 527800 528347 := bstep (se 1 (by rfl) ⟨396260, by rfl⟩ : syracuseStep 528347 = 792521) B792521
theorem B13111307 : Blo 527800 13111307 := bstep (se 1 (by rfl) ⟨9833480, by rfl⟩ : syracuseStep 13111307 = 19666961) B19666961
theorem B593959 : Blo 527800 593959 := bstep (se 1 (by rfl) ⟨445469, by rfl⟩ : syracuseStep 593959 = 890939) B890939
theorem B528423 : Blo 527800 528423 := bstep (se 1 (by rfl) ⟨396317, by rfl⟩ : syracuseStep 528423 = 792635) B792635
theorem B528463 : Blo 527800 528463 := bstep (se 1 (by rfl) ⟨396347, by rfl⟩ : syracuseStep 528463 = 792695) B792695
theorem B528479 : Blo 527800 528479 := bstep (se 1 (by rfl) ⟨396359, by rfl⟩ : syracuseStep 528479 = 792719) B792719
theorem B2855027 : Blo 527800 2855027 := bstep (se 1 (by rfl) ⟨2141270, by rfl⟩ : syracuseStep 2855027 = 4282541) B4282541
theorem B528507 : Blo 527800 528507 := bstep (se 1 (by rfl) ⟨396380, by rfl⟩ : syracuseStep 528507 = 792761) B792761
theorem B528559 : Blo 527800 528559 := bstep (se 1 (by rfl) ⟨396419, by rfl⟩ : syracuseStep 528559 = 792839) B792839
theorem B528583 : Blo 527800 528583 := bstep (se 1 (by rfl) ⟨396437, by rfl⟩ : syracuseStep 528583 = 792875) B792875
theorem B528603 : Blo 527800 528603 := bstep (se 1 (by rfl) ⟨396452, by rfl⟩ : syracuseStep 528603 = 792905) B792905
theorem B528679 : Blo 527800 528679 := bstep (se 1 (by rfl) ⟨396509, by rfl⟩ : syracuseStep 528679 = 793019) B793019
theorem B528719 : Blo 527800 528719 := bstep (se 1 (by rfl) ⟨396539, by rfl⟩ : syracuseStep 528719 = 793079) B793079
theorem B528735 : Blo 527800 528735 := bstep (se 1 (by rfl) ⟨396551, by rfl⟩ : syracuseStep 528735 = 793103) B793103
theorem B528763 : Blo 527800 528763 := bstep (se 1 (by rfl) ⟨396572, by rfl⟩ : syracuseStep 528763 = 793145) B793145
theorem B528815 : Blo 527800 528815 := bstep (se 1 (by rfl) ⟨396611, by rfl⟩ : syracuseStep 528815 = 793223) B793223
theorem B528839 : Blo 527800 528839 := bstep (se 1 (by rfl) ⟨396629, by rfl⟩ : syracuseStep 528839 = 793259) B793259
theorem B528859 : Blo 527800 528859 := bstep (se 1 (by rfl) ⟨396644, by rfl⟩ : syracuseStep 528859 = 793289) B793289
theorem B528935 : Blo 527800 528935 := bstep (se 1 (by rfl) ⟨396701, by rfl⟩ : syracuseStep 528935 = 793403) B793403
theorem B528975 : Blo 527800 528975 := bstep (se 1 (by rfl) ⟨396731, by rfl⟩ : syracuseStep 528975 = 793463) B793463
theorem B528991 : Blo 527800 528991 := bstep (se 1 (by rfl) ⟨396743, by rfl⟩ : syracuseStep 528991 = 793487) B793487
theorem B529019 : Blo 527800 529019 := bstep (se 1 (by rfl) ⟨396764, by rfl⟩ : syracuseStep 529019 = 793529) B793529
theorem B529071 : Blo 527800 529071 := bstep (se 1 (by rfl) ⟨396803, by rfl⟩ : syracuseStep 529071 = 793607) B793607
theorem B4035257 : Blo 527800 4035257 := bstep (se 2 (by rfl) ⟨1513221, by rfl⟩ : syracuseStep 4035257 = 3026443) B3026443
theorem B529095 : Blo 527800 529095 := bstep (se 1 (by rfl) ⟨396821, by rfl⟩ : syracuseStep 529095 = 793643) B793643
theorem B529115 : Blo 527800 529115 := bstep (se 1 (by rfl) ⟨396836, by rfl⟩ : syracuseStep 529115 = 793673) B793673
theorem B529191 : Blo 527800 529191 := bstep (se 1 (by rfl) ⟨396893, by rfl⟩ : syracuseStep 529191 = 793787) B793787
theorem B1512265 : Blo 527800 1512265 := bstep (se 2 (by rfl) ⟨567099, by rfl⟩ : syracuseStep 1512265 = 1134199) B1134199
theorem B529231 : Blo 527800 529231 := bstep (se 1 (by rfl) ⟨396923, by rfl⟩ : syracuseStep 529231 = 793847) B793847
theorem B529247 : Blo 527800 529247 := bstep (se 1 (by rfl) ⟨396935, by rfl⟩ : syracuseStep 529247 = 793871) B793871
theorem B1905515 : Blo 527800 1905515 := bstep (se 1 (by rfl) ⟨1429136, by rfl⟩ : syracuseStep 1905515 = 2858273) B2858273
theorem B529275 : Blo 527800 529275 := bstep (se 1 (by rfl) ⟨396956, by rfl⟩ : syracuseStep 529275 = 793913) B793913
theorem B3806099 : Blo 527800 3806099 := bstep (se 1 (by rfl) ⟨2854574, by rfl⟩ : syracuseStep 3806099 = 5709149) B5709149
theorem B529327 : Blo 527800 529327 := bstep (se 1 (by rfl) ⟨396995, by rfl⟩ : syracuseStep 529327 = 793991) B793991
theorem B529351 : Blo 527800 529351 := bstep (se 1 (by rfl) ⟨397013, by rfl⟩ : syracuseStep 529351 = 794027) B794027
theorem B529371 : Blo 527800 529371 := bstep (se 1 (by rfl) ⟨397028, by rfl⟩ : syracuseStep 529371 = 794057) B794057
theorem B1610759 : Blo 527800 1610759 := bstep (se 1 (by rfl) ⟨1208069, by rfl⟩ : syracuseStep 1610759 = 2416139) B2416139
theorem B2692115 : Blo 527800 2692115 := bstep (se 1 (by rfl) ⟨2019086, by rfl⟩ : syracuseStep 2692115 = 4038173) B4038173
theorem B529447 : Blo 527800 529447 := bstep (se 1 (by rfl) ⟨397085, by rfl⟩ : syracuseStep 529447 = 794171) B794171
theorem B529487 : Blo 527800 529487 := bstep (se 1 (by rfl) ⟨397115, by rfl⟩ : syracuseStep 529487 = 794231) B794231
theorem B529503 : Blo 527800 529503 := bstep (se 1 (by rfl) ⟨397127, by rfl⟩ : syracuseStep 529503 = 794255) B794255
theorem B529531 : Blo 527800 529531 := bstep (se 1 (by rfl) ⟨397148, by rfl⟩ : syracuseStep 529531 = 794297) B794297
theorem B529583 : Blo 527800 529583 := bstep (se 1 (by rfl) ⟨397187, by rfl⟩ : syracuseStep 529583 = 794375) B794375
theorem B529607 : Blo 527800 529607 := bstep (se 1 (by rfl) ⟨397205, by rfl⟩ : syracuseStep 529607 = 794411) B794411
theorem B529627 : Blo 527800 529627 := bstep (se 1 (by rfl) ⟨397220, by rfl⟩ : syracuseStep 529627 = 794441) B794441
theorem B791801 : Blo 527800 791801 := bstep (se 2 (by rfl) ⟨296925, by rfl⟩ : syracuseStep 791801 = 593851) B593851
theorem B8295695 : Blo 527800 8295695 := bstep (se 1 (by rfl) ⟨6221771, by rfl⟩ : syracuseStep 8295695 = 12443543) B12443543
theorem B529703 : Blo 527800 529703 := bstep (se 1 (by rfl) ⟨397277, by rfl⟩ : syracuseStep 529703 = 794555) B794555
theorem B529743 : Blo 527800 529743 := bstep (se 1 (by rfl) ⟨397307, by rfl⟩ : syracuseStep 529743 = 794615) B794615
theorem B791903 : Blo 527800 791903 := bstep (se 1 (by rfl) ⟨593927, by rfl⟩ : syracuseStep 791903 = 1187855) B1187855
theorem B529759 : Blo 527800 529759 := bstep (se 1 (by rfl) ⟨397319, by rfl⟩ : syracuseStep 529759 = 794639) B794639
theorem B791915 : Blo 527800 791915 := bstep (se 1 (by rfl) ⟨593936, by rfl⟩ : syracuseStep 791915 = 1187873) B1187873
theorem B529787 : Blo 527800 529787 := bstep (se 1 (by rfl) ⟨397340, by rfl⟩ : syracuseStep 529787 = 794681) B794681
theorem B529839 : Blo 527800 529839 := bstep (se 1 (by rfl) ⟨397379, by rfl⟩ : syracuseStep 529839 = 794759) B794759
theorem B529863 : Blo 527800 529863 := bstep (se 1 (by rfl) ⟨397397, by rfl⟩ : syracuseStep 529863 = 794795) B794795
theorem B529883 : Blo 527800 529883 := bstep (se 1 (by rfl) ⟨397412, by rfl⟩ : syracuseStep 529883 = 794825) B794825
theorem B529959 : Blo 527800 529959 := bstep (se 1 (by rfl) ⟨397469, by rfl⟩ : syracuseStep 529959 = 794939) B794939
theorem B792143 : Blo 527800 792143 := bstep (se 1 (by rfl) ⟨594107, by rfl⟩ : syracuseStep 792143 = 1188215) B1188215
theorem B529999 : Blo 527800 529999 := bstep (se 1 (by rfl) ⟨397499, by rfl⟩ : syracuseStep 529999 = 794999) B794999
theorem B530015 : Blo 527800 530015 := bstep (se 1 (by rfl) ⟨397511, by rfl⟩ : syracuseStep 530015 = 795023) B795023
theorem B595579 : Blo 527800 595579 := bstep (se 1 (by rfl) ⟨446684, by rfl⟩ : syracuseStep 595579 = 893369) B893369
theorem B530043 : Blo 527800 530043 := bstep (se 1 (by rfl) ⟨397532, by rfl⟩ : syracuseStep 530043 = 795065) B795065
theorem B4036229 : Blo 527800 4036229 := bstep (se 4 (by rfl) ⟨378396, by rfl⟩ : syracuseStep 4036229 = 756793) B756793
theorem B1808011 : Blo 527800 1808011 := bstep (se 1 (by rfl) ⟨1356008, by rfl⟩ : syracuseStep 1808011 = 2712017) B2712017
theorem B530095 : Blo 527800 530095 := bstep (se 1 (by rfl) ⟨397571, by rfl⟩ : syracuseStep 530095 = 795143) B795143
theorem B792263 : Blo 527800 792263 := bstep (se 1 (by rfl) ⟨594197, by rfl⟩ : syracuseStep 792263 = 1188395) B1188395
theorem B530119 : Blo 527800 530119 := bstep (se 1 (by rfl) ⟨397589, by rfl⟩ : syracuseStep 530119 = 795179) B795179
theorem B2004689 : Blo 527800 2004689 := bstep (se 2 (by rfl) ⟨751758, by rfl⟩ : syracuseStep 2004689 = 1503517) B1503517
theorem B530139 : Blo 527800 530139 := bstep (se 1 (by rfl) ⟨397604, by rfl⟩ : syracuseStep 530139 = 795209) B795209
theorem B530215 : Blo 527800 530215 := bstep (se 1 (by rfl) ⟨397661, by rfl⟩ : syracuseStep 530215 = 795323) B795323
theorem B3020611 : Blo 527800 3020611 := bstep (se 1 (by rfl) ⟨2265458, by rfl⟩ : syracuseStep 3020611 = 4530917) B4530917
theorem B530255 : Blo 527800 530255 := bstep (se 1 (by rfl) ⟨397691, by rfl⟩ : syracuseStep 530255 = 795383) B795383
theorem B530271 : Blo 527800 530271 := bstep (se 1 (by rfl) ⟨397703, by rfl⟩ : syracuseStep 530271 = 795407) B795407
theorem B792425 : Blo 527800 792425 := bstep (se 2 (by rfl) ⟨297159, by rfl⟩ : syracuseStep 792425 = 594319) B594319
theorem B530299 : Blo 527800 530299 := bstep (se 1 (by rfl) ⟨397724, by rfl⟩ : syracuseStep 530299 = 795449) B795449
theorem B530351 : Blo 527800 530351 := bstep (se 1 (by rfl) ⟨397763, by rfl⟩ : syracuseStep 530351 = 795527) B795527
theorem B792503 : Blo 527800 792503 := bstep (se 1 (by rfl) ⟨594377, by rfl⟩ : syracuseStep 792503 = 1188755) B1188755
theorem B530375 : Blo 527800 530375 := bstep (se 1 (by rfl) ⟨397781, by rfl⟩ : syracuseStep 530375 = 795563) B795563
theorem B792539 : Blo 527800 792539 := bstep (se 1 (by rfl) ⟨594404, by rfl⟩ : syracuseStep 792539 = 1188809) B1188809
theorem B530395 : Blo 527800 530395 := bstep (se 1 (by rfl) ⟨397796, by rfl⟩ : syracuseStep 530395 = 795593) B795593
theorem B3872783 : Blo 527800 3872783 := bstep (se 1 (by rfl) ⟨2904587, by rfl⟩ : syracuseStep 3872783 = 5809175) B5809175
theorem B530471 : Blo 527800 530471 := bstep (se 1 (by rfl) ⟨397853, by rfl⟩ : syracuseStep 530471 = 795707) B795707
theorem B890959 : Blo 527800 890959 := bstep (se 1 (by rfl) ⟨668219, by rfl⟩ : syracuseStep 890959 = 1336439) B1336439
theorem B596047 : Blo 527800 596047 := bstep (se 1 (by rfl) ⟨447035, by rfl⟩ : syracuseStep 596047 = 894071) B894071
theorem B530511 : Blo 527800 530511 := bstep (se 1 (by rfl) ⟨397883, by rfl⟩ : syracuseStep 530511 = 795767) B795767
theorem B530527 : Blo 527800 530527 := bstep (se 1 (by rfl) ⟨397895, by rfl⟩ : syracuseStep 530527 = 795791) B795791
theorem B530555 : Blo 527800 530555 := bstep (se 1 (by rfl) ⟨397916, by rfl⟩ : syracuseStep 530555 = 795833) B795833
theorem B2005145 : Blo 527800 2005145 := bstep (se 2 (by rfl) ⟨751929, by rfl⟩ : syracuseStep 2005145 = 1503859) B1503859
theorem B530607 : Blo 527800 530607 := bstep (se 1 (by rfl) ⟨397955, by rfl⟩ : syracuseStep 530607 = 795911) B795911
theorem B530631 : Blo 527800 530631 := bstep (se 1 (by rfl) ⟨397973, by rfl⟩ : syracuseStep 530631 = 795947) B795947
theorem B530651 : Blo 527800 530651 := bstep (se 1 (by rfl) ⟨397988, by rfl⟩ : syracuseStep 530651 = 795977) B795977
theorem B530727 : Blo 527800 530727 := bstep (se 1 (by rfl) ⟨398045, by rfl⟩ : syracuseStep 530727 = 796091) B796091
theorem B3447101 : Blo 527800 3447101 := bstep (se 3 (by rfl) ⟨646331, by rfl⟩ : syracuseStep 3447101 = 1292663) B1292663
theorem B891209 : Blo 527800 891209 := bstep (se 2 (by rfl) ⟨334203, by rfl⟩ : syracuseStep 891209 = 668407) B668407
theorem B530767 : Blo 527800 530767 := bstep (se 1 (by rfl) ⟨398075, by rfl⟩ : syracuseStep 530767 = 796151) B796151
theorem B530783 : Blo 527800 530783 := bstep (se 1 (by rfl) ⟨398087, by rfl⟩ : syracuseStep 530783 = 796175) B796175
theorem B530811 : Blo 527800 530811 := bstep (se 1 (by rfl) ⟨398108, by rfl⟩ : syracuseStep 530811 = 796217) B796217
theorem B793007 : Blo 527800 793007 := bstep (se 1 (by rfl) ⟨594755, by rfl⟩ : syracuseStep 793007 = 1189511) B1189511
theorem B530863 : Blo 527800 530863 := bstep (se 1 (by rfl) ⟨398147, by rfl⟩ : syracuseStep 530863 = 796295) B796295
theorem B530887 : Blo 527800 530887 := bstep (se 1 (by rfl) ⟨398165, by rfl⟩ : syracuseStep 530887 = 796331) B796331
theorem B596443 : Blo 527800 596443 := bstep (se 1 (by rfl) ⟨447332, by rfl⟩ : syracuseStep 596443 = 894665) B894665
theorem B530907 : Blo 527800 530907 := bstep (se 1 (by rfl) ⟨398180, by rfl⟩ : syracuseStep 530907 = 796361) B796361
theorem B793097 : Blo 527800 793097 := bstep (se 2 (by rfl) ⟨297411, by rfl⟩ : syracuseStep 793097 = 594823) B594823
theorem B793127 : Blo 527800 793127 := bstep (se 1 (by rfl) ⟨594845, by rfl⟩ : syracuseStep 793127 = 1189691) B1189691
theorem B530983 : Blo 527800 530983 := bstep (se 1 (by rfl) ⟨398237, by rfl⟩ : syracuseStep 530983 = 796475) B796475
theorem B531023 : Blo 527800 531023 := bstep (se 1 (by rfl) ⟨398267, by rfl⟩ : syracuseStep 531023 = 796535) B796535
theorem B531039 : Blo 527800 531039 := bstep (se 1 (by rfl) ⟨398279, by rfl⟩ : syracuseStep 531039 = 796559) B796559
theorem B793211 : Blo 527800 793211 := bstep (se 1 (by rfl) ⟨594908, by rfl⟩ : syracuseStep 793211 = 1189817) B1189817
theorem B531067 : Blo 527800 531067 := bstep (se 1 (by rfl) ⟨398300, by rfl⟩ : syracuseStep 531067 = 796601) B796601
theorem B2267783 : Blo 527800 2267783 := bstep (se 1 (by rfl) ⟨1700837, by rfl⟩ : syracuseStep 2267783 = 3401675) B3401675
theorem B1514123 : Blo 527800 1514123 := bstep (se 1 (by rfl) ⟨1135592, by rfl⟩ : syracuseStep 1514123 = 2271185) B2271185
theorem B531119 : Blo 527800 531119 := bstep (se 1 (by rfl) ⟨398339, by rfl⟩ : syracuseStep 531119 = 796679) B796679
theorem B531143 : Blo 527800 531143 := bstep (se 1 (by rfl) ⟨398357, by rfl⟩ : syracuseStep 531143 = 796715) B796715
theorem B531163 : Blo 527800 531163 := bstep (se 1 (by rfl) ⟨398372, by rfl⟩ : syracuseStep 531163 = 796745) B796745
theorem B891641 : Blo 527800 891641 := bstep (se 2 (by rfl) ⟨334365, by rfl⟩ : syracuseStep 891641 = 668731) B668731
theorem B793337 : Blo 527800 793337 := bstep (se 2 (by rfl) ⟨297501, by rfl⟩ : syracuseStep 793337 = 595003) B595003
theorem B531239 : Blo 527800 531239 := bstep (se 1 (by rfl) ⟨398429, by rfl⟩ : syracuseStep 531239 = 796859) B796859
theorem B531279 : Blo 527800 531279 := bstep (se 1 (by rfl) ⟨398459, by rfl⟩ : syracuseStep 531279 = 796919) B796919
theorem B793439 : Blo 527800 793439 := bstep (se 1 (by rfl) ⟨595079, by rfl⟩ : syracuseStep 793439 = 1190159) B1190159
theorem B531295 : Blo 527800 531295 := bstep (se 1 (by rfl) ⟨398471, by rfl⟩ : syracuseStep 531295 = 796943) B796943
theorem B793451 : Blo 527800 793451 := bstep (se 1 (by rfl) ⟨595088, by rfl⟩ : syracuseStep 793451 = 1190177) B1190177
theorem B531323 : Blo 527800 531323 := bstep (se 1 (by rfl) ⟨398492, by rfl⟩ : syracuseStep 531323 = 796985) B796985
theorem B1088399 : Blo 527800 1088399 := bstep (se 1 (by rfl) ⟨816299, by rfl⟩ : syracuseStep 1088399 = 1632599) B1632599
theorem B891823 : Blo 527800 891823 := bstep (se 1 (by rfl) ⟨668867, by rfl⟩ : syracuseStep 891823 = 1337735) B1337735
theorem B596911 : Blo 527800 596911 := bstep (se 1 (by rfl) ⟨447683, by rfl⟩ : syracuseStep 596911 = 895367) B895367
theorem B531375 : Blo 527800 531375 := bstep (se 1 (by rfl) ⟨398531, by rfl⟩ : syracuseStep 531375 = 797063) B797063
theorem B531399 : Blo 527800 531399 := bstep (se 1 (by rfl) ⟨398549, by rfl⟩ : syracuseStep 531399 = 797099) B797099
theorem B531419 : Blo 527800 531419 := bstep (se 1 (by rfl) ⟨398564, by rfl⟩ : syracuseStep 531419 = 797129) B797129
theorem B891911 : Blo 527800 891911 := bstep (se 1 (by rfl) ⟨668933, by rfl⟩ : syracuseStep 891911 = 1337867) B1337867
theorem B531495 : Blo 527800 531495 := bstep (se 1 (by rfl) ⟨398621, by rfl⟩ : syracuseStep 531495 = 797243) B797243
theorem B793679 : Blo 527800 793679 := bstep (se 1 (by rfl) ⟨595259, by rfl⟩ : syracuseStep 793679 = 1190519) B1190519
theorem B531535 : Blo 527800 531535 := bstep (se 1 (by rfl) ⟨398651, by rfl⟩ : syracuseStep 531535 = 797303) B797303
theorem B531551 : Blo 527800 531551 := bstep (se 1 (by rfl) ⟨398663, by rfl⟩ : syracuseStep 531551 = 797327) B797327
theorem B531579 : Blo 527800 531579 := bstep (se 1 (by rfl) ⟨398684, by rfl⟩ : syracuseStep 531579 = 797369) B797369
theorem B531631 : Blo 527800 531631 := bstep (se 1 (by rfl) ⟨398723, by rfl⟩ : syracuseStep 531631 = 797447) B797447
theorem B793799 : Blo 527800 793799 := bstep (se 1 (by rfl) ⟨595349, by rfl⟩ : syracuseStep 793799 = 1190699) B1190699
theorem B531655 : Blo 527800 531655 := bstep (se 1 (by rfl) ⟨398741, by rfl⟩ : syracuseStep 531655 = 797483) B797483
theorem B531675 : Blo 527800 531675 := bstep (se 1 (by rfl) ⟨398756, by rfl⟩ : syracuseStep 531675 = 797513) B797513
theorem B531751 : Blo 527800 531751 := bstep (se 1 (by rfl) ⟨398813, by rfl⟩ : syracuseStep 531751 = 797627) B797627
theorem B531791 : Blo 527800 531791 := bstep (se 1 (by rfl) ⟨398843, by rfl⟩ : syracuseStep 531791 = 797687) B797687
theorem B4300121 : Blo 527800 4300121 := bstep (se 2 (by rfl) ⟨1612545, by rfl⟩ : syracuseStep 4300121 = 3225091) B3225091
theorem B892255 : Blo 527800 892255 := bstep (se 1 (by rfl) ⟨669191, by rfl⟩ : syracuseStep 892255 = 1338383) B1338383
theorem B597343 : Blo 527800 597343 := bstep (se 1 (by rfl) ⟨448007, by rfl⟩ : syracuseStep 597343 = 896015) B896015
theorem B793961 : Blo 527800 793961 := bstep (se 2 (by rfl) ⟨297735, by rfl⟩ : syracuseStep 793961 = 595471) B595471
theorem B892343 : Blo 527800 892343 := bstep (se 1 (by rfl) ⟨669257, by rfl⟩ : syracuseStep 892343 = 1338515) B1338515
theorem B794039 : Blo 527800 794039 := bstep (se 1 (by rfl) ⟨595529, by rfl⟩ : syracuseStep 794039 = 1191059) B1191059
theorem B794075 : Blo 527800 794075 := bstep (se 1 (by rfl) ⟨595556, by rfl⟩ : syracuseStep 794075 = 1191113) B1191113
theorem B597703 : Blo 527800 597703 := bstep (se 1 (by rfl) ⟨448277, by rfl⟩ : syracuseStep 597703 = 896555) B896555
theorem B1187657 : Blo 527800 1187657 := bstep (se 2 (by rfl) ⟨445371, by rfl⟩ : syracuseStep 1187657 = 890743) B890743
theorem B794543 : Blo 527800 794543 := bstep (se 1 (by rfl) ⟨595907, by rfl⟩ : syracuseStep 794543 = 1191815) B1191815
theorem B892937 : Blo 527800 892937 := bstep (se 2 (by rfl) ⟨334851, by rfl⟩ : syracuseStep 892937 = 669703) B669703
theorem B794633 : Blo 527800 794633 := bstep (se 2 (by rfl) ⟨297987, by rfl⟩ : syracuseStep 794633 = 595975) B595975
theorem B794663 : Blo 527800 794663 := bstep (se 1 (by rfl) ⟨595997, by rfl⟩ : syracuseStep 794663 = 1191995) B1191995
theorem B2007119 : Blo 527800 2007119 := bstep (se 1 (by rfl) ⟨1505339, by rfl⟩ : syracuseStep 2007119 = 3010679) B3010679
theorem B794747 : Blo 527800 794747 := bstep (se 1 (by rfl) ⟨596060, by rfl⟩ : syracuseStep 794747 = 1192121) B1192121
theorem B1613981 : Blo 527800 1613981 := bstep (se 3 (by rfl) ⟨302621, by rfl⟩ : syracuseStep 1613981 = 605243) B605243
theorem B893099 : Blo 527800 893099 := bstep (se 1 (by rfl) ⟨669824, by rfl⟩ : syracuseStep 893099 = 1339649) B1339649
theorem B2007287 : Blo 527800 2007287 := bstep (se 1 (by rfl) ⟨1505465, by rfl⟩ : syracuseStep 2007287 = 3010931) B3010931
theorem B794873 : Blo 527800 794873 := bstep (se 2 (by rfl) ⟨298077, by rfl⟩ : syracuseStep 794873 = 596155) B596155
theorem B794975 : Blo 527800 794975 := bstep (se 1 (by rfl) ⟨596231, by rfl⟩ : syracuseStep 794975 = 1192463) B1192463
theorem B794987 : Blo 527800 794987 := bstep (se 1 (by rfl) ⟨596240, by rfl⟩ : syracuseStep 794987 = 1192481) B1192481
theorem B893497 : Blo 527800 893497 := bstep (se 2 (by rfl) ⟨335061, by rfl⟩ : syracuseStep 893497 = 670123) B670123
theorem B795215 : Blo 527800 795215 := bstep (se 1 (by rfl) ⟨596411, by rfl⟩ : syracuseStep 795215 = 1192823) B1192823
theorem B1188449 : Blo 527800 1188449 := bstep (se 2 (by rfl) ⟨445668, by rfl⟩ : syracuseStep 1188449 = 891337) B891337
theorem B10887797 : Blo 527800 10887797 := bstep (se 5 (by rfl) ⟨510365, by rfl⟩ : syracuseStep 10887797 = 1020731) B1020731
theorem B893639 : Blo 527800 893639 := bstep (se 1 (by rfl) ⟨670229, by rfl⟩ : syracuseStep 893639 = 1340459) B1340459
theorem B795335 : Blo 527800 795335 := bstep (se 1 (by rfl) ⟨596501, by rfl⟩ : syracuseStep 795335 = 1193003) B1193003
theorem B893801 : Blo 527800 893801 := bstep (se 2 (by rfl) ⟨335175, by rfl⟩ : syracuseStep 893801 = 670351) B670351
theorem B795497 : Blo 527800 795497 := bstep (se 2 (by rfl) ⟨298311, by rfl⟩ : syracuseStep 795497 = 596623) B596623
theorem B1188791 : Blo 527800 1188791 := bstep (se 1 (by rfl) ⟨891593, by rfl⟩ : syracuseStep 1188791 = 1783187) B1783187
theorem B795575 : Blo 527800 795575 := bstep (se 1 (by rfl) ⟨596681, by rfl⟩ : syracuseStep 795575 = 1193363) B1193363
theorem B795611 : Blo 527800 795611 := bstep (se 1 (by rfl) ⟨596708, by rfl⟩ : syracuseStep 795611 = 1193417) B1193417
theorem B2270227 : Blo 527800 2270227 := bstep (se 1 (by rfl) ⟨1702670, by rfl⟩ : syracuseStep 2270227 = 3405341) B3405341
theorem B2008259 : Blo 527800 2008259 := bstep (se 1 (by rfl) ⟨1506194, by rfl⟩ : syracuseStep 2008259 = 3012389) B3012389
theorem B894199 : Blo 527800 894199 := bstep (se 1 (by rfl) ⟨670649, by rfl⟩ : syracuseStep 894199 = 1341299) B1341299
theorem B1516943 : Blo 527800 1516943 := bstep (se 1 (by rfl) ⟨1137707, by rfl⟩ : syracuseStep 1516943 = 2275415) B2275415
theorem B796079 : Blo 527800 796079 := bstep (se 1 (by rfl) ⟨597059, by rfl⟩ : syracuseStep 796079 = 1194119) B1194119
theorem B894395 : Blo 527800 894395 := bstep (se 1 (by rfl) ⟨670796, by rfl⟩ : syracuseStep 894395 = 1341593) B1341593
theorem B1189385 : Blo 527800 1189385 := bstep (se 2 (by rfl) ⟨446019, by rfl⟩ : syracuseStep 1189385 = 892039) B892039
theorem B796169 : Blo 527800 796169 := bstep (se 2 (by rfl) ⟨298563, by rfl⟩ : syracuseStep 796169 = 597127) B597127
theorem B894503 : Blo 527800 894503 := bstep (se 1 (by rfl) ⟨670877, by rfl⟩ : syracuseStep 894503 = 1341755) B1341755
theorem B796199 : Blo 527800 796199 := bstep (se 1 (by rfl) ⟨597149, by rfl⟩ : syracuseStep 796199 = 1194299) B1194299
theorem B796283 : Blo 527800 796283 := bstep (se 1 (by rfl) ⟨597212, by rfl⟩ : syracuseStep 796283 = 1194425) B1194425
theorem B796409 : Blo 527800 796409 := bstep (se 2 (by rfl) ⟨298653, by rfl⟩ : syracuseStep 796409 = 597307) B597307
theorem B894793 : Blo 527800 894793 := bstep (se 2 (by rfl) ⟨335547, by rfl⟩ : syracuseStep 894793 = 671095) B671095
theorem B1189727 : Blo 527800 1189727 := bstep (se 1 (by rfl) ⟨892295, by rfl⟩ : syracuseStep 1189727 = 1784591) B1784591
theorem B796511 : Blo 527800 796511 := bstep (se 1 (by rfl) ⟨597383, by rfl⟩ : syracuseStep 796511 = 1194767) B1194767
theorem B894827 : Blo 527800 894827 := bstep (se 1 (by rfl) ⟨671120, by rfl⟩ : syracuseStep 894827 = 1342241) B1342241
theorem B796523 : Blo 527800 796523 := bstep (se 1 (by rfl) ⟨597392, by rfl⟩ : syracuseStep 796523 = 1194785) B1194785
theorem B1189907 : Blo 527800 1189907 := bstep (se 1 (by rfl) ⟨892430, by rfl⟩ : syracuseStep 1189907 = 1784861) B1784861
theorem B796751 : Blo 527800 796751 := bstep (se 1 (by rfl) ⟨597563, by rfl⟩ : syracuseStep 796751 = 1195127) B1195127
theorem B3024985 : Blo 527800 3024985 := bstep (se 2 (by rfl) ⟨1134369, by rfl⟩ : syracuseStep 3024985 = 2268739) B2268739
theorem B2009245 : Blo 527800 2009245 := bstep (se 3 (by rfl) ⟨376733, by rfl⟩ : syracuseStep 2009245 = 753467) B753467
theorem B796871 : Blo 527800 796871 := bstep (se 1 (by rfl) ⟨597653, by rfl⟩ : syracuseStep 796871 = 1195307) B1195307
theorem B895225 : Blo 527800 895225 := bstep (se 2 (by rfl) ⟨335709, by rfl⟩ : syracuseStep 895225 = 671419) B671419
theorem B1190249 : Blo 527800 1190249 := bstep (se 2 (by rfl) ⟨446343, by rfl⟩ : syracuseStep 1190249 = 892687) B892687
theorem B797033 : Blo 527800 797033 := bstep (se 2 (by rfl) ⟨298887, by rfl⟩ : syracuseStep 797033 = 597775) B597775
theorem B797111 : Blo 527800 797111 := bstep (se 1 (by rfl) ⟨597833, by rfl⟩ : syracuseStep 797111 = 1195667) B1195667
theorem B797147 : Blo 527800 797147 := bstep (se 1 (by rfl) ⟨597860, by rfl⟩ : syracuseStep 797147 = 1195721) B1195721
theorem B895495 : Blo 527800 895495 := bstep (se 1 (by rfl) ⟨671621, by rfl⟩ : syracuseStep 895495 = 1343243) B1343243
theorem B3058505 : Blo 527800 3058505 := bstep (se 2 (by rfl) ⟨1146939, by rfl⟩ : syracuseStep 3058505 = 2293879) B2293879
theorem B797615 : Blo 527800 797615 := bstep (se 1 (by rfl) ⟨598211, by rfl⟩ : syracuseStep 797615 = 1196423) B1196423
theorem B895927 : Blo 527800 895927 := bstep (se 1 (by rfl) ⟨671945, by rfl⟩ : syracuseStep 895927 = 1343891) B1343891
theorem B1190843 : Blo 527800 1190843 := bstep (se 1 (by rfl) ⟨893132, by rfl⟩ : syracuseStep 1190843 = 1786265) B1786265
theorem B1911815 : Blo 527800 1911815 := bstep (se 1 (by rfl) ⟨1433861, by rfl⟩ : syracuseStep 1911815 = 2867723) B2867723
theorem B1190969 : Blo 527800 1190969 := bstep (se 2 (by rfl) ⟨446613, by rfl⟩ : syracuseStep 1190969 = 893227) B893227
theorem B1911887 : Blo 527800 1911887 := bstep (se 1 (by rfl) ⟨1433915, by rfl⟩ : syracuseStep 1911887 = 2867831) B2867831
theorem B896123 : Blo 527800 896123 := bstep (se 1 (by rfl) ⟨672092, by rfl⟩ : syracuseStep 896123 = 1344185) B1344185
theorem B1191311 : Blo 527800 1191311 := bstep (se 1 (by rfl) ⟨893483, by rfl⟩ : syracuseStep 1191311 = 1786967) B1786967
theorem B896521 : Blo 527800 896521 := bstep (se 2 (by rfl) ⟨336195, by rfl⟩ : syracuseStep 896521 = 672391) B672391
theorem B4533893 : Blo 527800 4533893 := bstep (se 4 (by rfl) ⟨425052, by rfl⟩ : syracuseStep 4533893 = 850105) B850105
theorem B896683 : Blo 527800 896683 := bstep (se 1 (by rfl) ⟨672512, by rfl⟩ : syracuseStep 896683 = 1345025) B1345025
theorem B1781459 : Blo 527800 1781459 := bstep (se 1 (by rfl) ⟨1336094, by rfl⟩ : syracuseStep 1781459 = 2672189) B2672189
theorem B1191635 : Blo 527800 1191635 := bstep (se 1 (by rfl) ⟨893726, by rfl⟩ : syracuseStep 1191635 = 1787453) B1787453
theorem B3387095 : Blo 527800 3387095 := bstep (se 1 (by rfl) ⟨2540321, by rfl⟩ : syracuseStep 3387095 = 5080643) B5080643
theorem B4599737 : Blo 527800 4599737 := bstep (se 2 (by rfl) ⟨1724901, by rfl⟩ : syracuseStep 4599737 = 3449803) B3449803
theorem B896987 : Blo 527800 896987 := bstep (se 1 (by rfl) ⟨672740, by rfl⟩ : syracuseStep 896987 = 1345481) B1345481
theorem B2240627 : Blo 527800 2240627 := bstep (se 1 (by rfl) ⟨1680470, by rfl⟩ : syracuseStep 2240627 = 3360941) B3360941
theorem B897223 : Blo 527800 897223 := bstep (se 1 (by rfl) ⟨672917, by rfl⟩ : syracuseStep 897223 = 1345835) B1345835
theorem B897385 : Blo 527800 897385 := bstep (se 2 (by rfl) ⟨336519, by rfl⟩ : syracuseStep 897385 = 673039) B673039
theorem B635431 : Blo 527800 635431 := bstep (se 1 (by rfl) ⟨476573, by rfl⟩ : syracuseStep 635431 = 953147) B953147
theorem B1192571 : Blo 527800 1192571 := bstep (se 1 (by rfl) ⟨894428, by rfl⟩ : syracuseStep 1192571 = 1788857) B1788857
theorem B1192697 : Blo 527800 1192697 := bstep (se 2 (by rfl) ⟨447261, by rfl⟩ : syracuseStep 1192697 = 894523) B894523
theorem B1782647 : Blo 527800 1782647 := bstep (se 1 (by rfl) ⟨1336985, by rfl⟩ : syracuseStep 1782647 = 2673971) B2673971
theorem B2012161 : Blo 527800 2012161 := bstep (se 2 (by rfl) ⟨754560, by rfl⟩ : syracuseStep 2012161 = 1509121) B1509121
theorem B1192967 : Blo 527800 1192967 := bstep (se 1 (by rfl) ⟨894725, by rfl⟩ : syracuseStep 1192967 = 1789451) B1789451
theorem B6763571 : Blo 527800 6763571 := bstep (se 1 (by rfl) ⟨5072678, by rfl⟩ : syracuseStep 6763571 = 10145357) B10145357
theorem B1782863 : Blo 527800 1782863 := bstep (se 1 (by rfl) ⟨1337147, by rfl⟩ : syracuseStep 1782863 = 2674295) B2674295
theorem B1193039 : Blo 527800 1193039 := bstep (se 1 (by rfl) ⟨894779, by rfl⟩ : syracuseStep 1193039 = 1789559) B1789559
theorem B1783241 : Blo 527800 1783241 := bstep (se 2 (by rfl) ⟨668715, by rfl⟩ : syracuseStep 1783241 = 1337431) B1337431
theorem B1193435 : Blo 527800 1193435 := bstep (se 1 (by rfl) ⟨895076, by rfl⟩ : syracuseStep 1193435 = 1790153) B1790153
theorem B1783511 : Blo 527800 1783511 := bstep (se 1 (by rfl) ⟨1337633, by rfl⟩ : syracuseStep 1783511 = 2675267) B2675267
theorem B1128185 : Blo 527800 1128185 := bstep (se 2 (by rfl) ⟨423069, by rfl⟩ : syracuseStep 1128185 = 846139) B846139
theorem B2012921 : Blo 527800 2012921 := bstep (se 2 (by rfl) ⟨754845, by rfl⟩ : syracuseStep 2012921 = 1509691) B1509691
theorem B1128287 : Blo 527800 1128287 := bstep (se 1 (by rfl) ⟨846215, by rfl⟩ : syracuseStep 1128287 = 1692431) B1692431
theorem B1783727 : Blo 527800 1783727 := bstep (se 1 (by rfl) ⟨1337795, by rfl⟩ : syracuseStep 1783727 = 2675591) B2675591
theorem B1193903 : Blo 527800 1193903 := bstep (se 1 (by rfl) ⟨895427, by rfl⟩ : syracuseStep 1193903 = 1790855) B1790855
theorem B1718279 : Blo 527800 1718279 := bstep (se 1 (by rfl) ⟨1288709, by rfl⟩ : syracuseStep 1718279 = 2577419) B2577419
theorem B3815581 : Blo 527800 3815581 := bstep (se 3 (by rfl) ⟨715421, by rfl⟩ : syracuseStep 3815581 = 1430843) B1430843
theorem B1194155 : Blo 527800 1194155 := bstep (se 1 (by rfl) ⟨895616, by rfl⟩ : syracuseStep 1194155 = 1791233) B1791233
theorem B1194695 : Blo 527800 1194695 := bstep (se 1 (by rfl) ⟨896021, by rfl⟩ : syracuseStep 1194695 = 1792043) B1792043
theorem B2014379 : Blo 527800 2014379 := bstep (se 1 (by rfl) ⟨1510784, by rfl⟩ : syracuseStep 2014379 = 3021569) B3021569
theorem B6044867 : Blo 527800 6044867 := bstep (se 1 (by rfl) ⟨4533650, by rfl⟩ : syracuseStep 6044867 = 9067301) B9067301
theorem B3489139 : Blo 527800 3489139 := bstep (se 1 (by rfl) ⟨2616854, by rfl⟩ : syracuseStep 3489139 = 5233709) B5233709
theorem B1195559 : Blo 527800 1195559 := bstep (se 1 (by rfl) ⟨896669, by rfl⟩ : syracuseStep 1195559 = 1793339) B1793339
theorem B2866877 : Blo 527800 2866877 := bstep (se 3 (by rfl) ⟨537539, by rfl⟩ : syracuseStep 2866877 = 1075079) B1075079
theorem B13811471 : Blo 527800 13811471 := bstep (se 1 (by rfl) ⟨10358603, by rfl⟩ : syracuseStep 13811471 = 20717207) B20717207
theorem B1195883 : Blo 527800 1195883 := bstep (se 1 (by rfl) ⟨896912, by rfl⟩ : syracuseStep 1195883 = 1793825) B1793825
theorem B6012791 : Blo 527800 6012791 := bstep (se 1 (by rfl) ⟨4509593, by rfl⟩ : syracuseStep 6012791 = 9019187) B9019187
theorem B1195937 : Blo 527800 1195937 := bstep (se 2 (by rfl) ⟨448476, by rfl⟩ : syracuseStep 1195937 = 896953) B896953
theorem B2539457 : Blo 527800 2539457 := bstep (se 2 (by rfl) ⟨952296, by rfl⟩ : syracuseStep 2539457 = 1904593) B1904593
theorem B1786103 : Blo 527800 1786103 := bstep (se 1 (by rfl) ⟨1339577, by rfl⟩ : syracuseStep 1786103 = 2679155) B2679155
theorem B1196279 : Blo 527800 1196279 := bstep (se 1 (by rfl) ⟨897209, by rfl⟩ : syracuseStep 1196279 = 1794419) B1794419
theorem B2015549 : Blo 527800 2015549 := bstep (se 3 (by rfl) ⟨377915, by rfl⟩ : syracuseStep 2015549 = 755831) B755831
theorem B967087 : Blo 527800 967087 := bstep (se 1 (by rfl) ⟨725315, by rfl⟩ : syracuseStep 967087 = 1450631) B1450631
theorem B672295 : Blo 527800 672295 := bstep (se 1 (by rfl) ⟨504221, by rfl⟩ : syracuseStep 672295 = 1008443) B1008443
theorem B1786427 : Blo 527800 1786427 := bstep (se 1 (by rfl) ⟨1339820, by rfl⟩ : syracuseStep 1786427 = 2679641) B2679641
theorem B6046325 : Blo 527800 6046325 := bstep (se 5 (by rfl) ⟨283421, by rfl⟩ : syracuseStep 6046325 = 566843) B566843
theorem B2015867 : Blo 527800 2015867 := bstep (se 1 (by rfl) ⟨1511900, by rfl⟩ : syracuseStep 2015867 = 3023801) B3023801
theorem B1786697 : Blo 527800 1786697 := bstep (se 2 (by rfl) ⟨670011, by rfl⟩ : syracuseStep 1786697 = 1340023) B1340023
theorem B672619 : Blo 527800 672619 := bstep (se 1 (by rfl) ⟨504464, by rfl⟩ : syracuseStep 672619 = 1008929) B1008929
theorem B7619629 : Blo 527800 7619629 := bstep (se 3 (by rfl) ⟨1428680, by rfl⟩ : syracuseStep 7619629 = 2857361) B2857361
theorem B3392705 : Blo 527800 3392705 := bstep (se 2 (by rfl) ⟨1272264, by rfl⟩ : syracuseStep 3392705 = 2544529) B2544529
theorem B3392857 : Blo 527800 3392857 := bstep (se 2 (by rfl) ⟨1272321, by rfl⟩ : syracuseStep 3392857 = 2544643) B2544643
theorem B3622259 : Blo 527800 3622259 := bstep (se 1 (by rfl) ⟨2716694, by rfl⟩ : syracuseStep 3622259 = 5433389) B5433389
theorem B6768035 : Blo 527800 6768035 := bstep (se 1 (by rfl) ⟨5076026, by rfl⟩ : syracuseStep 6768035 = 10152053) B10152053
theorem B4343203 : Blo 527800 4343203 := bstep (se 1 (by rfl) ⟨3257402, by rfl⟩ : syracuseStep 4343203 = 6514805) B6514805
theorem B1131995 : Blo 527800 1131995 := bstep (se 1 (by rfl) ⟨848996, by rfl⟩ : syracuseStep 1131995 = 1697993) B1697993
theorem B4310567 : Blo 527800 4310567 := bstep (se 1 (by rfl) ⟨3232925, by rfl⟩ : syracuseStep 4310567 = 6465851) B6465851
theorem B804601 : Blo 527800 804601 := bstep (se 2 (by rfl) ⟨301725, by rfl⟩ : syracuseStep 804601 = 603451) B603451
theorem B1787831 : Blo 527800 1787831 := bstep (se 1 (by rfl) ⟨1340873, by rfl⟩ : syracuseStep 1787831 = 2681747) B2681747
theorem B2017295 : Blo 527800 2017295 := bstep (se 1 (by rfl) ⟨1512971, by rfl⟩ : syracuseStep 2017295 = 3025943) B3025943
theorem B870439 : Blo 527800 870439 := bstep (se 1 (by rfl) ⟨652829, by rfl⟩ : syracuseStep 870439 = 1305659) B1305659
theorem B3230081 : Blo 527800 3230081 := bstep (se 2 (by rfl) ⟨1211280, by rfl⟩ : syracuseStep 3230081 = 2422561) B2422561
theorem B2673161 : Blo 527800 2673161 := bstep (se 2 (by rfl) ⟨1002435, by rfl⟩ : syracuseStep 2673161 = 2004871) B2004871
theorem B1788425 : Blo 527800 1788425 := bstep (se 2 (by rfl) ⟨670659, by rfl⟩ : syracuseStep 1788425 = 1341319) B1341319
theorem B1002041 : Blo 527800 1002041 := bstep (se 2 (by rfl) ⟨375765, by rfl⟩ : syracuseStep 1002041 = 751531) B751531
theorem B9652871 : Blo 527800 9652871 := bstep (se 1 (by rfl) ⟨7239653, by rfl⟩ : syracuseStep 9652871 = 14479307) B14479307
theorem B5491385 : Blo 527800 5491385 := bstep (se 2 (by rfl) ⟨2059269, by rfl⟩ : syracuseStep 5491385 = 4118539) B4118539
theorem B5098787 : Blo 527800 5098787 := bstep (se 1 (by rfl) ⟨3824090, by rfl⟩ : syracuseStep 5098787 = 7648181) B7648181
theorem B1789289 : Blo 527800 1789289 := bstep (se 2 (by rfl) ⟨670983, by rfl⟩ : syracuseStep 1789289 = 1341967) B1341967
theorem B2903539 : Blo 527800 2903539 := bstep (se 1 (by rfl) ⟨2177654, by rfl⟩ : syracuseStep 2903539 = 4355309) B4355309
theorem B3624509 : Blo 527800 3624509 := bstep (se 3 (by rfl) ⟨679595, by rfl⟩ : syracuseStep 3624509 = 1359191) B1359191
theorem B4017761 : Blo 527800 4017761 := bstep (se 2 (by rfl) ⟨1506660, by rfl⟩ : syracuseStep 4017761 = 3013321) B3013321
theorem B2018951 : Blo 527800 2018951 := bstep (se 1 (by rfl) ⟨1514213, by rfl⟩ : syracuseStep 2018951 = 3028427) B3028427
theorem B2674619 : Blo 527800 2674619 := bstep (se 1 (by rfl) ⟨2005964, by rfl⟩ : syracuseStep 2674619 = 4011929) B4011929
theorem B1789883 : Blo 527800 1789883 := bstep (se 1 (by rfl) ⟨1342412, by rfl⟩ : syracuseStep 1789883 = 2684825) B2684825
theorem B1003529 : Blo 527800 1003529 := bstep (se 2 (by rfl) ⟨376323, by rfl⟩ : syracuseStep 1003529 = 752647) B752647
theorem B14373179 : Blo 527800 14373179 := bstep (se 1 (by rfl) ⟨10779884, by rfl⟩ : syracuseStep 14373179 = 21559769) B21559769
theorem B2412929 : Blo 527800 2412929 := bstep (se 2 (by rfl) ⟨904848, by rfl⟩ : syracuseStep 2412929 = 1809697) B1809697
theorem B11457125 : Blo 527800 11457125 := bstep (se 4 (by rfl) ⟨1074105, by rfl⟩ : syracuseStep 11457125 = 2148211) B2148211
theorem B5100205 : Blo 527800 5100205 := bstep (se 3 (by rfl) ⟨956288, by rfl⟩ : syracuseStep 5100205 = 1912577) B1912577
theorem B7721729 : Blo 527800 7721729 := bstep (se 2 (by rfl) ⟨2895648, by rfl⟩ : syracuseStep 7721729 = 5791297) B5791297
theorem B2151197 : Blo 527800 2151197 := bstep (se 3 (by rfl) ⟨403349, by rfl⟩ : syracuseStep 2151197 = 806699) B806699
theorem B1004395 : Blo 527800 1004395 := bstep (se 1 (by rfl) ⟨753296, by rfl⟩ : syracuseStep 1004395 = 1506593) B1506593
theorem B1004471 : Blo 527800 1004471 := bstep (se 1 (by rfl) ⟨753353, by rfl⟩ : syracuseStep 1004471 = 1506707) B1506707
theorem B4019219 : Blo 527800 4019219 := bstep (se 1 (by rfl) ⟨3014414, by rfl⟩ : syracuseStep 4019219 = 6028829) B6028829
theorem B1692829 : Blo 527800 1692829 := bstep (se 3 (by rfl) ⟨317405, by rfl⟩ : syracuseStep 1692829 = 634811) B634811
theorem B2675915 : Blo 527800 2675915 := bstep (se 1 (by rfl) ⟨2006936, by rfl⟩ : syracuseStep 2675915 = 4013873) B4013873
theorem B1004987 : Blo 527800 1004987 := bstep (se 1 (by rfl) ⟨753740, by rfl⟩ : syracuseStep 1004987 = 1507481) B1507481
theorem B906715 : Blo 527800 906715 := bstep (se 1 (by rfl) ⟨680036, by rfl⟩ : syracuseStep 906715 = 1360073) B1360073
theorem B3233267 : Blo 527800 3233267 := bstep (se 1 (by rfl) ⟨2424950, by rfl⟩ : syracuseStep 3233267 = 4849901) B4849901
theorem B1791611 : Blo 527800 1791611 := bstep (se 1 (by rfl) ⟨1343708, by rfl⟩ : syracuseStep 1791611 = 2687417) B2687417
theorem B677575 : Blo 527800 677575 := bstep (se 1 (by rfl) ⟨508181, by rfl⟩ : syracuseStep 677575 = 1016363) B1016363
theorem B1791773 : Blo 527800 1791773 := bstep (se 3 (by rfl) ⟨335957, by rfl⟩ : syracuseStep 1791773 = 671915) B671915
theorem B1005473 : Blo 527800 1005473 := bstep (se 2 (by rfl) ⟨377052, by rfl⟩ : syracuseStep 1005473 = 754105) B754105
theorem B1529761 : Blo 527800 1529761 := bstep (se 2 (by rfl) ⟨573660, by rfl⟩ : syracuseStep 1529761 = 1147321) B1147321
theorem B1005625 : Blo 527800 1005625 := bstep (se 2 (by rfl) ⟨377109, by rfl⟩ : syracuseStep 1005625 = 754219) B754219
theorem B3987713 : Blo 527800 3987713 := bstep (se 2 (by rfl) ⟨1495392, by rfl⟩ : syracuseStep 3987713 = 2990785) B2990785
theorem B1005929 : Blo 527800 1005929 := bstep (se 2 (by rfl) ⟨377223, by rfl⟩ : syracuseStep 1005929 = 754447) B754447
theorem B1792475 : Blo 527800 1792475 := bstep (se 1 (by rfl) ⟨1344356, by rfl⟩ : syracuseStep 1792475 = 2688713) B2688713
theorem B1793177 : Blo 527800 1793177 := bstep (se 2 (by rfl) ⟨672441, by rfl⟩ : syracuseStep 1793177 = 1344883) B1344883
theorem B1694891 : Blo 527800 1694891 := bstep (se 1 (by rfl) ⟨1271168, by rfl⟩ : syracuseStep 1694891 = 2542337) B2542337
theorem B1695431 : Blo 527800 1695431 := bstep (se 1 (by rfl) ⟨1271573, by rfl⟩ : syracuseStep 1695431 = 2543147) B2543147
theorem B4022135 : Blo 527800 4022135 := bstep (se 1 (by rfl) ⟨3016601, by rfl⟩ : syracuseStep 4022135 = 6033203) B6033203
theorem B1204303 : Blo 527800 1204303 := bstep (se 1 (by rfl) ⟨903227, by rfl⟩ : syracuseStep 1204303 = 1806455) B1806455
theorem B8609969 : Blo 527800 8609969 := bstep (se 2 (by rfl) ⟨3228738, by rfl⟩ : syracuseStep 8609969 = 6457477) B6457477
theorem B1794365 : Blo 527800 1794365 := bstep (se 3 (by rfl) ⟨336443, by rfl⟩ : syracuseStep 1794365 = 672887) B672887
theorem B1008055 : Blo 527800 1008055 := bstep (se 1 (by rfl) ⟨756041, by rfl⟩ : syracuseStep 1008055 = 1512083) B1512083
theorem B3400217 : Blo 527800 3400217 := bstep (se 2 (by rfl) ⟨1275081, by rfl⟩ : syracuseStep 3400217 = 2550163) B2550163
theorem B1696315 : Blo 527800 1696315 := bstep (se 1 (by rfl) ⟨1272236, by rfl⟩ : syracuseStep 1696315 = 2544473) B2544473
theorem B1336247 : Blo 527800 1336247 := bstep (se 1 (by rfl) ⟨1002185, by rfl⟩ : syracuseStep 1336247 = 2004371) B2004371
theorem B3007489 : Blo 527800 3007489 := bstep (se 2 (by rfl) ⟨1127808, by rfl⟩ : syracuseStep 3007489 = 2255617) B2255617
theorem B3433751 : Blo 527800 3433751 := bstep (se 1 (by rfl) ⟨2575313, by rfl⟩ : syracuseStep 3433751 = 5150627) B5150627
theorem B15230267 : Blo 527800 15230267 := bstep (se 1 (by rfl) ⟨11422700, by rfl⟩ : syracuseStep 15230267 = 22845401) B22845401
theorem B1860989 : Blo 527800 1860989 := bstep (se 3 (by rfl) ⟨348935, by rfl⟩ : syracuseStep 1860989 = 697871) B697871
theorem B5727959 : Blo 527800 5727959 := bstep (se 1 (by rfl) ⟨4295969, by rfl⟩ : syracuseStep 5727959 = 8591939) B8591939
theorem B1009513 : Blo 527800 1009513 := bstep (se 2 (by rfl) ⟨378567, by rfl⟩ : syracuseStep 1009513 = 757135) B757135
theorem B1337249 : Blo 527800 1337249 := bstep (se 2 (by rfl) ⟨501468, by rfl⟩ : syracuseStep 1337249 = 1002937) B1002937
theorem B1206199 : Blo 527800 1206199 := bstep (se 1 (by rfl) ⟨904649, by rfl⟩ : syracuseStep 1206199 = 1809299) B1809299
theorem B2681099 : Blo 527800 2681099 := bstep (se 1 (by rfl) ⟨2010824, by rfl⟩ : syracuseStep 2681099 = 4021649) B4021649
theorem B1337705 : Blo 527800 1337705 := bstep (se 2 (by rfl) ⟨501639, by rfl⟩ : syracuseStep 1337705 = 1003279) B1003279
theorem B715303 : Blo 527800 715303 := bstep (se 1 (by rfl) ⟨536477, by rfl⟩ : syracuseStep 715303 = 1072955) B1072955
theorem B7269041 : Blo 527800 7269041 := bstep (se 2 (by rfl) ⟨2725890, by rfl⟩ : syracuseStep 7269041 = 5451781) B5451781
theorem B5106509 : Blo 527800 5106509 := bstep (se 3 (by rfl) ⟨957470, by rfl⟩ : syracuseStep 5106509 = 1914941) B1914941
theorem B846779 : Blo 527800 846779 := bstep (se 1 (by rfl) ⟨635084, by rfl⟩ : syracuseStep 846779 = 1270169) B1270169
theorem B846857 : Blo 527800 846857 := bstep (se 2 (by rfl) ⟨317571, by rfl⟩ : syracuseStep 846857 = 635143) B635143
theorem B4025537 : Blo 527800 4025537 := bstep (se 2 (by rfl) ⟨1509576, by rfl⟩ : syracuseStep 4025537 = 3019153) B3019153
theorem B3829193 : Blo 527800 3829193 := bstep (se 2 (by rfl) ⟨1435947, by rfl⟩ : syracuseStep 3829193 = 2871895) B2871895
theorem B1338889 : Blo 527800 1338889 := bstep (se 2 (by rfl) ⟨502083, by rfl⟩ : syracuseStep 1338889 = 1004167) B1004167
theorem B847369 : Blo 527800 847369 := bstep (se 2 (by rfl) ⟨317763, by rfl⟩ : syracuseStep 847369 = 635527) B635527
theorem B32566859 : Blo 527800 32566859 := bstep (se 1 (by rfl) ⟨24425144, by rfl⟩ : syracuseStep 32566859 = 48850289) B48850289
theorem B2682557 : Blo 527800 2682557 := bstep (se 3 (by rfl) ⟨502979, by rfl⟩ : syracuseStep 2682557 = 1005959) B1005959
theorem B2682719 : Blo 527800 2682719 := bstep (se 1 (by rfl) ⟨2012039, by rfl⟩ : syracuseStep 2682719 = 4024079) B4024079
theorem B2584507 : Blo 527800 2584507 := bstep (se 1 (by rfl) ⟨1938380, by rfl⟩ : syracuseStep 2584507 = 3876761) B3876761
theorem B1503289 : Blo 527800 1503289 := bstep (se 2 (by rfl) ⟨563733, by rfl⟩ : syracuseStep 1503289 = 1127467) B1127467
theorem B1143335 : Blo 527800 1143335 := bstep (se 1 (by rfl) ⟨857501, by rfl⟩ : syracuseStep 1143335 = 1715003) B1715003
theorem B6812369 : Blo 527800 6812369 := bstep (se 2 (by rfl) ⟨2554638, by rfl⟩ : syracuseStep 6812369 = 5109277) B5109277
theorem B3633923 : Blo 527800 3633923 := bstep (se 1 (by rfl) ⟨2725442, by rfl⟩ : syracuseStep 3633923 = 5450885) B5450885
theorem B1340347 : Blo 527800 1340347 := bstep (se 1 (by rfl) ⟨1005260, by rfl⟩ : syracuseStep 1340347 = 2010521) B2010521
theorem B7468081 : Blo 527800 7468081 := bstep (se 2 (by rfl) ⟨2800530, by rfl⟩ : syracuseStep 7468081 = 5601061) B5601061
theorem B3011863 : Blo 527800 3011863 := bstep (se 1 (by rfl) ⟨2258897, by rfl⟩ : syracuseStep 3011863 = 4517795) B4517795
theorem B718255 : Blo 527800 718255 := bstep (se 1 (by rfl) ⟨538691, by rfl⟩ : syracuseStep 718255 = 1077383) B1077383
theorem B2618825 : Blo 527800 2618825 := bstep (se 2 (by rfl) ⟨982059, by rfl⟩ : syracuseStep 2618825 = 1964119) B1964119
theorem B4519435 : Blo 527800 4519435 := bstep (se 1 (by rfl) ⟨3389576, by rfl⟩ : syracuseStep 4519435 = 6779153) B6779153
theorem B1504793 : Blo 527800 1504793 := bstep (se 2 (by rfl) ⟨564297, by rfl⟩ : syracuseStep 1504793 = 1128595) B1128595
theorem B7665299 : Blo 527800 7665299 := bstep (se 1 (by rfl) ⟨5748974, by rfl⟩ : syracuseStep 7665299 = 11497949) B11497949
theorem B7960313 : Blo 527800 7960313 := bstep (se 2 (by rfl) ⟨2985117, by rfl⟩ : syracuseStep 7960313 = 5970235) B5970235
theorem B3405827 : Blo 527800 3405827 := bstep (se 1 (by rfl) ⟨2554370, by rfl⟩ : syracuseStep 3405827 = 5108741) B5108741
theorem B4028453 : Blo 527800 4028453 := bstep (se 4 (by rfl) ⟨377667, by rfl⟩ : syracuseStep 4028453 = 755335) B755335
theorem B2685473 : Blo 527800 2685473 := bstep (se 2 (by rfl) ⟨1007052, by rfl⟩ : syracuseStep 2685473 = 2014105) B2014105
theorem B12909131 : Blo 527800 12909131 := bstep (se 1 (by rfl) ⟨9681848, by rfl⟩ : syracuseStep 12909131 = 19363697) B19363697
theorem B11598709 : Blo 527800 11598709 := bstep (se 5 (by rfl) ⟨543689, by rfl⟩ : syracuseStep 11598709 = 1087379) B1087379
theorem B1276859 : Blo 527800 1276859 := bstep (se 1 (by rfl) ⟨957644, by rfl⟩ : syracuseStep 1276859 = 1915289) B1915289
theorem B6421477 : Blo 527800 6421477 := bstep (se 4 (by rfl) ⟨602013, by rfl⟩ : syracuseStep 6421477 = 1204027) B1204027
theorem B2260163 : Blo 527800 2260163 := bstep (se 1 (by rfl) ⟨1695122, by rfl⟩ : syracuseStep 2260163 = 3390245) B3390245
theorem B1342939 : Blo 527800 1342939 := bstep (se 1 (by rfl) ⟨1007204, by rfl⟩ : syracuseStep 1342939 = 2014409) B2014409
theorem B14450501 : Blo 527800 14450501 := bstep (se 4 (by rfl) ⟨1354734, by rfl⟩ : syracuseStep 14450501 = 2709469) B2709469
theorem B1605737 : Blo 527800 1605737 := bstep (se 2 (by rfl) ⟨602151, by rfl⟩ : syracuseStep 1605737 = 1204303) B1204303
theorem B1343699 : Blo 527800 1343699 := bstep (se 1 (by rfl) ⟨1007774, by rfl⟩ : syracuseStep 1343699 = 2015549) B2015549
theorem B4030883 : Blo 527800 4030883 := bstep (se 1 (by rfl) ⟨3023162, by rfl⟩ : syracuseStep 4030883 = 6046325) B6046325
theorem B1343911 : Blo 527800 1343911 := bstep (se 1 (by rfl) ⟨1007933, by rfl⟩ : syracuseStep 1343911 = 2015867) B2015867
theorem B1344073 : Blo 527800 1344073 := bstep (se 2 (by rfl) ⟨504027, by rfl⟩ : syracuseStep 1344073 = 1008055) B1008055
theorem B2261753 : Blo 527800 2261753 := bstep (se 2 (by rfl) ⟨848157, by rfl⟩ : syracuseStep 2261753 = 1696315) B1696315
theorem B2261803 : Blo 527800 2261803 := bstep (se 1 (by rfl) ⟨1696352, by rfl⟩ : syracuseStep 2261803 = 3392705) B3392705
theorem B1344863 : Blo 527800 1344863 := bstep (se 1 (by rfl) ⟨1008647, by rfl⟩ : syracuseStep 1344863 = 2017295) B2017295
theorem B10159505 : Blo 527800 10159505 := bstep (se 2 (by rfl) ⟨3809814, by rfl⟩ : syracuseStep 10159505 = 7619629) B7619629
theorem B3048893 : Blo 527800 3048893 := bstep (se 3 (by rfl) ⟨571667, by rfl⟩ : syracuseStep 3048893 = 1143335) B1143335
theorem B4064825 : Blo 527800 4064825 := bstep (se 2 (by rfl) ⟨1524309, by rfl⟩ : syracuseStep 4064825 = 3048619) B3048619
theorem B4523809 : Blo 527800 4523809 := bstep (se 2 (by rfl) ⟨1696428, by rfl⟩ : syracuseStep 4523809 = 3392857) B3392857
theorem B1345967 : Blo 527800 1345967 := bstep (se 1 (by rfl) ⟨1009475, by rfl⟩ : syracuseStep 1345967 = 2018951) B2018951
theorem B1346017 : Blo 527800 1346017 := bstep (se 2 (by rfl) ⟨504756, by rfl⟩ : syracuseStep 1346017 = 1009513) B1009513
theorem B2689523 : Blo 527800 2689523 := bstep (se 1 (by rfl) ⟨2017142, by rfl⟩ : syracuseStep 2689523 = 4034285) B4034285
theorem B1608265 : Blo 527800 1608265 := bstep (se 2 (by rfl) ⟨603099, by rfl⟩ : syracuseStep 1608265 = 1206199) B1206199
theorem B1903351 : Blo 527800 1903351 := bstep (se 1 (by rfl) ⟨1427513, by rfl⟩ : syracuseStep 1903351 = 2855027) B2855027
theorem B4033313 : Blo 527800 4033313 := bstep (se 2 (by rfl) ⟨1512492, by rfl⟩ : syracuseStep 4033313 = 3024985) B3024985
theorem B1608619 : Blo 527800 1608619 := bstep (se 1 (by rfl) ⟨1206464, by rfl⟩ : syracuseStep 1608619 = 2412929) B2412929
theorem B7638083 : Blo 527800 7638083 := bstep (se 1 (by rfl) ⟨5728562, by rfl⟩ : syracuseStep 7638083 = 11457125) B11457125
theorem B2690171 : Blo 527800 2690171 := bstep (se 1 (by rfl) ⟨2017628, by rfl⟩ : syracuseStep 2690171 = 4035257) B4035257
theorem B5147819 : Blo 527800 5147819 := bstep (se 1 (by rfl) ⟨3860864, by rfl⟩ : syracuseStep 5147819 = 7721729) B7721729
theorem B953737 : Blo 527800 953737 := bstep (se 2 (by rfl) ⟨357651, by rfl⟩ : syracuseStep 953737 = 715303) B715303
theorem B527867 : Blo 527800 527867 := bstep (se 1 (by rfl) ⟨395900, by rfl⟩ : syracuseStep 527867 = 791801) B791801
theorem B527935 : Blo 527800 527935 := bstep (se 1 (by rfl) ⟨395951, by rfl⟩ : syracuseStep 527935 = 791903) B791903
theorem B527943 : Blo 527800 527943 := bstep (se 1 (by rfl) ⟨395957, by rfl⟩ : syracuseStep 527943 = 791915) B791915
theorem B528095 : Blo 527800 528095 := bstep (se 1 (by rfl) ⟨396071, by rfl⟩ : syracuseStep 528095 = 792143) B792143
theorem B2690819 : Blo 527800 2690819 := bstep (se 1 (by rfl) ⟨2018114, by rfl⟩ : syracuseStep 2690819 = 4036229) B4036229
theorem B528175 : Blo 527800 528175 := bstep (se 1 (by rfl) ⟨396131, by rfl⟩ : syracuseStep 528175 = 792263) B792263
theorem B6983533 : Blo 527800 6983533 := bstep (se 3 (by rfl) ⟨1309412, by rfl⟩ : syracuseStep 6983533 = 2618825) B2618825
theorem B528283 : Blo 527800 528283 := bstep (se 1 (by rfl) ⟨396212, by rfl⟩ : syracuseStep 528283 = 792425) B792425
theorem B3018653 : Blo 527800 3018653 := bstep (se 3 (by rfl) ⟨565997, by rfl⟩ : syracuseStep 3018653 = 1131995) B1131995
theorem B528335 : Blo 527800 528335 := bstep (se 1 (by rfl) ⟨396251, by rfl⟩ : syracuseStep 528335 = 792503) B792503
theorem B528359 : Blo 527800 528359 := bstep (se 1 (by rfl) ⟨396269, by rfl⟩ : syracuseStep 528359 = 792539) B792539
theorem B2658475 : Blo 527800 2658475 := bstep (se 1 (by rfl) ⟨1993856, by rfl⟩ : syracuseStep 2658475 = 3987713) B3987713
theorem B594139 : Blo 527800 594139 := bstep (se 1 (by rfl) ⟨445604, by rfl⟩ : syracuseStep 594139 = 891209) B891209
theorem B528671 : Blo 527800 528671 := bstep (se 1 (by rfl) ⟨396503, by rfl⟩ : syracuseStep 528671 = 793007) B793007
theorem B528731 : Blo 527800 528731 := bstep (se 1 (by rfl) ⟨396548, by rfl⟩ : syracuseStep 528731 = 793097) B793097
theorem B528751 : Blo 527800 528751 := bstep (se 1 (by rfl) ⟨396563, by rfl⟩ : syracuseStep 528751 = 793127) B793127
theorem B528807 : Blo 527800 528807 := bstep (se 1 (by rfl) ⟨396605, by rfl⟩ : syracuseStep 528807 = 793211) B793211
theorem B1511855 : Blo 527800 1511855 := bstep (se 1 (by rfl) ⟨1133891, by rfl⟩ : syracuseStep 1511855 = 2267783) B2267783
theorem B594427 : Blo 527800 594427 := bstep (se 1 (by rfl) ⟨445820, by rfl⟩ : syracuseStep 594427 = 891641) B891641
theorem B528891 : Blo 527800 528891 := bstep (se 1 (by rfl) ⟨396668, by rfl⟩ : syracuseStep 528891 = 793337) B793337
theorem B528959 : Blo 527800 528959 := bstep (se 1 (by rfl) ⟨396719, by rfl⟩ : syracuseStep 528959 = 793439) B793439
theorem B528967 : Blo 527800 528967 := bstep (se 1 (by rfl) ⟨396725, by rfl⟩ : syracuseStep 528967 = 793451) B793451
theorem B3871385 : Blo 527800 3871385 := bstep (se 2 (by rfl) ⟨1451769, by rfl⟩ : syracuseStep 3871385 = 2903539) B2903539
theorem B594607 : Blo 527800 594607 := bstep (se 1 (by rfl) ⟨445955, by rfl⟩ : syracuseStep 594607 = 891911) B891911
theorem B529119 : Blo 527800 529119 := bstep (se 1 (by rfl) ⟨396839, by rfl⟩ : syracuseStep 529119 = 793679) B793679
theorem B529199 : Blo 527800 529199 := bstep (se 1 (by rfl) ⟨396899, by rfl⟩ : syracuseStep 529199 = 793799) B793799
theorem B529307 : Blo 527800 529307 := bstep (se 1 (by rfl) ⟨396980, by rfl⟩ : syracuseStep 529307 = 793961) B793961
theorem B594895 : Blo 527800 594895 := bstep (se 1 (by rfl) ⟨446171, by rfl⟩ : syracuseStep 594895 = 892343) B892343
theorem B529359 : Blo 527800 529359 := bstep (se 1 (by rfl) ⟨397019, by rfl⟩ : syracuseStep 529359 = 794039) B794039
theorem B529383 : Blo 527800 529383 := bstep (se 1 (by rfl) ⟨397037, by rfl⟩ : syracuseStep 529383 = 794075) B794075
theorem B791771 : Blo 527800 791771 := bstep (se 1 (by rfl) ⟨593828, by rfl⟩ : syracuseStep 791771 = 1187657) B1187657
theorem B3446009 : Blo 527800 3446009 := bstep (se 2 (by rfl) ⟨1292253, by rfl⟩ : syracuseStep 3446009 = 2584507) B2584507
theorem B529695 : Blo 527800 529695 := bstep (se 1 (by rfl) ⟨397271, by rfl⟩ : syracuseStep 529695 = 794543) B794543
theorem B595291 : Blo 527800 595291 := bstep (se 1 (by rfl) ⟨446468, by rfl⟩ : syracuseStep 595291 = 892937) B892937
theorem B529755 : Blo 527800 529755 := bstep (se 1 (by rfl) ⟨397316, by rfl⟩ : syracuseStep 529755 = 794633) B794633
theorem B529775 : Blo 527800 529775 := bstep (se 1 (by rfl) ⟨397331, by rfl⟩ : syracuseStep 529775 = 794663) B794663
theorem B10327421 : Blo 527800 10327421 := bstep (se 3 (by rfl) ⟨1936391, by rfl⟩ : syracuseStep 10327421 = 3872783) B3872783
theorem B791945 : Blo 527800 791945 := bstep (se 2 (by rfl) ⟨296979, by rfl⟩ : syracuseStep 791945 = 593959) B593959
theorem B2004385 : Blo 527800 2004385 := bstep (se 2 (by rfl) ⟨751644, by rfl⟩ : syracuseStep 2004385 = 1503289) B1503289
theorem B529831 : Blo 527800 529831 := bstep (se 1 (by rfl) ⟨397373, by rfl⟩ : syracuseStep 529831 = 794747) B794747
theorem B595399 : Blo 527800 595399 := bstep (se 1 (by rfl) ⟨446549, by rfl⟩ : syracuseStep 595399 = 893099) B893099
theorem B5739979 : Blo 527800 5739979 := bstep (se 1 (by rfl) ⟨4304984, by rfl⟩ : syracuseStep 5739979 = 8609969) B8609969
theorem B529915 : Blo 527800 529915 := bstep (se 1 (by rfl) ⟨397436, by rfl⟩ : syracuseStep 529915 = 794873) B794873
theorem B529983 : Blo 527800 529983 := bstep (se 1 (by rfl) ⟨397487, by rfl⟩ : syracuseStep 529983 = 794975) B794975
theorem B529991 : Blo 527800 529991 := bstep (se 1 (by rfl) ⟨397493, by rfl⟩ : syracuseStep 529991 = 794987) B794987
theorem B2266811 : Blo 527800 2266811 := bstep (se 1 (by rfl) ⟨1700108, by rfl⟩ : syracuseStep 2266811 = 3400217) B3400217
theorem B530143 : Blo 527800 530143 := bstep (se 1 (by rfl) ⟨397607, by rfl⟩ : syracuseStep 530143 = 795215) B795215
theorem B792299 : Blo 527800 792299 := bstep (se 1 (by rfl) ⟨594224, by rfl⟩ : syracuseStep 792299 = 1188449) B1188449
theorem B595759 : Blo 527800 595759 := bstep (se 1 (by rfl) ⟨446819, by rfl⟩ : syracuseStep 595759 = 893639) B893639
theorem B530223 : Blo 527800 530223 := bstep (se 1 (by rfl) ⟨397667, by rfl⟩ : syracuseStep 530223 = 795335) B795335
theorem B595867 : Blo 527800 595867 := bstep (se 1 (by rfl) ⟨446900, by rfl⟩ : syracuseStep 595867 = 893801) B893801
theorem B530331 : Blo 527800 530331 := bstep (se 1 (by rfl) ⟨397748, by rfl⟩ : syracuseStep 530331 = 795497) B795497
theorem B890831 : Blo 527800 890831 := bstep (se 1 (by rfl) ⟨668123, by rfl⟩ : syracuseStep 890831 = 1336247) B1336247
theorem B792527 : Blo 527800 792527 := bstep (se 1 (by rfl) ⟨594395, by rfl⟩ : syracuseStep 792527 = 1188791) B1188791
theorem B530383 : Blo 527800 530383 := bstep (se 1 (by rfl) ⟨397787, by rfl⟩ : syracuseStep 530383 = 795575) B795575
theorem B530407 : Blo 527800 530407 := bstep (se 1 (by rfl) ⟨397805, by rfl⟩ : syracuseStep 530407 = 795611) B795611
theorem B530719 : Blo 527800 530719 := bstep (se 1 (by rfl) ⟨398039, by rfl⟩ : syracuseStep 530719 = 796079) B796079
theorem B596263 : Blo 527800 596263 := bstep (se 1 (by rfl) ⟨447197, by rfl⟩ : syracuseStep 596263 = 894395) B894395
theorem B792923 : Blo 527800 792923 := bstep (se 1 (by rfl) ⟨594692, by rfl⟩ : syracuseStep 792923 = 1189385) B1189385
theorem B530779 : Blo 527800 530779 := bstep (se 1 (by rfl) ⟨398084, by rfl⟩ : syracuseStep 530779 = 796169) B796169
theorem B596335 : Blo 527800 596335 := bstep (se 1 (by rfl) ⟨447251, by rfl⟩ : syracuseStep 596335 = 894503) B894503
theorem B530799 : Blo 527800 530799 := bstep (se 1 (by rfl) ⟨398099, by rfl⟩ : syracuseStep 530799 = 796199) B796199
theorem B530855 : Blo 527800 530855 := bstep (se 1 (by rfl) ⟨398141, by rfl⟩ : syracuseStep 530855 = 796283) B796283
theorem B530939 : Blo 527800 530939 := bstep (se 1 (by rfl) ⟨398204, by rfl⟩ : syracuseStep 530939 = 796409) B796409
theorem B793151 : Blo 527800 793151 := bstep (se 1 (by rfl) ⟨594863, by rfl⟩ : syracuseStep 793151 = 1189727) B1189727
theorem B531007 : Blo 527800 531007 := bstep (se 1 (by rfl) ⟨398255, by rfl⟩ : syracuseStep 531007 = 796511) B796511
theorem B596551 : Blo 527800 596551 := bstep (se 1 (by rfl) ⟨447413, by rfl⟩ : syracuseStep 596551 = 894827) B894827
theorem B531015 : Blo 527800 531015 := bstep (se 1 (by rfl) ⟨398261, by rfl⟩ : syracuseStep 531015 = 796523) B796523
theorem B891499 : Blo 527800 891499 := bstep (se 1 (by rfl) ⟨668624, by rfl⟩ : syracuseStep 891499 = 1337249) B1337249
theorem B793271 : Blo 527800 793271 := bstep (se 1 (by rfl) ⟨594953, by rfl⟩ : syracuseStep 793271 = 1189907) B1189907
theorem B531167 : Blo 527800 531167 := bstep (se 1 (by rfl) ⟨398375, by rfl⟩ : syracuseStep 531167 = 796751) B796751
theorem B531247 : Blo 527800 531247 := bstep (se 1 (by rfl) ⟨398435, by rfl⟩ : syracuseStep 531247 = 796871) B796871
theorem B891803 : Blo 527800 891803 := bstep (se 1 (by rfl) ⟨668852, by rfl⟩ : syracuseStep 891803 = 1337705) B1337705
theorem B793499 : Blo 527800 793499 := bstep (se 1 (by rfl) ⟨595124, by rfl⟩ : syracuseStep 793499 = 1190249) B1190249
theorem B531355 : Blo 527800 531355 := bstep (se 1 (by rfl) ⟨398516, by rfl⟩ : syracuseStep 531355 = 797033) B797033
theorem B531407 : Blo 527800 531407 := bstep (se 1 (by rfl) ⟨398555, by rfl⟩ : syracuseStep 531407 = 797111) B797111
theorem B531431 : Blo 527800 531431 := bstep (se 1 (by rfl) ⟨398573, by rfl⟩ : syracuseStep 531431 = 797147) B797147
theorem B2039003 : Blo 527800 2039003 := bstep (se 1 (by rfl) ⟨1529252, by rfl⟩ : syracuseStep 2039003 = 3058505) B3058505
theorem B957673 : Blo 527800 957673 := bstep (se 2 (by rfl) ⟨359127, by rfl⟩ : syracuseStep 957673 = 718255) B718255
theorem B531743 : Blo 527800 531743 := bstep (se 1 (by rfl) ⟨398807, by rfl⟩ : syracuseStep 531743 = 797615) B797615
theorem B793895 : Blo 527800 793895 := bstep (se 1 (by rfl) ⟨595421, by rfl⟩ : syracuseStep 793895 = 1190843) B1190843
theorem B564571 : Blo 527800 564571 := bstep (se 1 (by rfl) ⟨423428, by rfl⟩ : syracuseStep 564571 = 846857) B846857
theorem B793979 : Blo 527800 793979 := bstep (se 1 (by rfl) ⟨595484, by rfl⟩ : syracuseStep 793979 = 1190969) B1190969
theorem B597415 : Blo 527800 597415 := bstep (se 1 (by rfl) ⟨448061, by rfl⟩ : syracuseStep 597415 = 896123) B896123
theorem B794105 : Blo 527800 794105 := bstep (se 2 (by rfl) ⟨297789, by rfl⟩ : syracuseStep 794105 = 595579) B595579
theorem B794207 : Blo 527800 794207 := bstep (se 1 (by rfl) ⟨595655, by rfl⟩ : syracuseStep 794207 = 1191311) B1191311
theorem B3022595 : Blo 527800 3022595 := bstep (se 1 (by rfl) ⟨2266946, by rfl⟩ : syracuseStep 3022595 = 4533893) B4533893
theorem B1187639 : Blo 527800 1187639 := bstep (se 1 (by rfl) ⟨890729, by rfl⟩ : syracuseStep 1187639 = 1781459) B1781459
theorem B794423 : Blo 527800 794423 := bstep (se 1 (by rfl) ⟨595817, by rfl⟩ : syracuseStep 794423 = 1191635) B1191635
theorem B2039681 : Blo 527800 2039681 := bstep (se 2 (by rfl) ⟨764880, by rfl⟩ : syracuseStep 2039681 = 1529761) B1529761
theorem B597991 : Blo 527800 597991 := bstep (se 1 (by rfl) ⟨448493, by rfl⟩ : syracuseStep 597991 = 896987) B896987
theorem B1187945 : Blo 527800 1187945 := bstep (se 2 (by rfl) ⟨445479, by rfl⟩ : syracuseStep 1187945 = 890959) B890959
theorem B794729 : Blo 527800 794729 := bstep (se 2 (by rfl) ⟨298023, by rfl⟩ : syracuseStep 794729 = 596047) B596047
theorem B5087441 : Blo 527800 5087441 := bstep (se 2 (by rfl) ⟨1907790, by rfl⟩ : syracuseStep 5087441 = 3815581) B3815581
theorem B795047 : Blo 527800 795047 := bstep (se 1 (by rfl) ⟨596285, by rfl⟩ : syracuseStep 795047 = 1192571) B1192571
theorem B795131 : Blo 527800 795131 := bstep (se 1 (by rfl) ⟨596348, by rfl⟩ : syracuseStep 795131 = 1192697) B1192697
theorem B1188431 : Blo 527800 1188431 := bstep (se 1 (by rfl) ⟨891323, by rfl⟩ : syracuseStep 1188431 = 1782647) B1782647
theorem B795257 : Blo 527800 795257 := bstep (se 2 (by rfl) ⟨298221, by rfl⟩ : syracuseStep 795257 = 596443) B596443
theorem B795311 : Blo 527800 795311 := bstep (se 1 (by rfl) ⟨596483, by rfl⟩ : syracuseStep 795311 = 1192967) B1192967
theorem B1188575 : Blo 527800 1188575 := bstep (se 1 (by rfl) ⟨891431, by rfl⟩ : syracuseStep 1188575 = 1782863) B1782863
theorem B795359 : Blo 527800 795359 := bstep (se 1 (by rfl) ⟨596519, by rfl⟩ : syracuseStep 795359 = 1193039) B1193039
theorem B9642725 : Blo 527800 9642725 := bstep (se 4 (by rfl) ⟨904005, by rfl⟩ : syracuseStep 9642725 = 1808011) B1808011
theorem B1188827 : Blo 527800 1188827 := bstep (se 1 (by rfl) ⟨891620, by rfl⟩ : syracuseStep 1188827 = 1783241) B1783241
theorem B795623 : Blo 527800 795623 := bstep (se 1 (by rfl) ⟨596717, by rfl⟩ : syracuseStep 795623 = 1193435) B1193435
theorem B1189007 : Blo 527800 1189007 := bstep (se 1 (by rfl) ⟨891755, by rfl⟩ : syracuseStep 1189007 = 1783511) B1783511
theorem B1189097 : Blo 527800 1189097 := bstep (se 2 (by rfl) ⟨445911, by rfl⟩ : syracuseStep 1189097 = 891823) B891823
theorem B795881 : Blo 527800 795881 := bstep (se 2 (by rfl) ⟨298455, by rfl⟩ : syracuseStep 795881 = 596911) B596911
theorem B1189151 : Blo 527800 1189151 := bstep (se 1 (by rfl) ⟨891863, by rfl⟩ : syracuseStep 1189151 = 1783727) B1783727
theorem B795935 : Blo 527800 795935 := bstep (se 1 (by rfl) ⟨596951, by rfl⟩ : syracuseStep 795935 = 1193903) B1193903
theorem B8561969 : Blo 527800 8561969 := bstep (se 2 (by rfl) ⟨3210738, by rfl⟩ : syracuseStep 8561969 = 6421477) B6421477
theorem B2270551 : Blo 527800 2270551 := bstep (se 1 (by rfl) ⟨1702913, by rfl⟩ : syracuseStep 2270551 = 3405827) B3405827
theorem B796103 : Blo 527800 796103 := bstep (se 1 (by rfl) ⟨597077, by rfl⟩ : syracuseStep 796103 = 1194155) B1194155
theorem B1189673 : Blo 527800 1189673 := bstep (se 2 (by rfl) ⟨446127, by rfl⟩ : syracuseStep 1189673 = 892255) B892255
theorem B796457 : Blo 527800 796457 := bstep (se 2 (by rfl) ⟨298671, by rfl⟩ : syracuseStep 796457 = 597343) B597343
theorem B796463 : Blo 527800 796463 := bstep (se 1 (by rfl) ⟨597347, by rfl⟩ : syracuseStep 796463 = 1194695) B1194695
theorem B796937 : Blo 527800 796937 := bstep (se 2 (by rfl) ⟨298851, by rfl⟩ : syracuseStep 796937 = 597703) B597703
theorem B797039 : Blo 527800 797039 := bstep (se 1 (by rfl) ⟨597779, by rfl⟩ : syracuseStep 797039 = 1195559) B1195559
theorem B1911251 : Blo 527800 1911251 := bstep (se 1 (by rfl) ⟨1433438, by rfl⟩ : syracuseStep 1911251 = 2866877) B2866877
theorem B797255 : Blo 527800 797255 := bstep (se 1 (by rfl) ⟨597941, by rfl⟩ : syracuseStep 797255 = 1195883) B1195883
theorem B4008527 : Blo 527800 4008527 := bstep (se 1 (by rfl) ⟨3006395, by rfl⟩ : syracuseStep 4008527 = 6012791) B6012791
theorem B797291 : Blo 527800 797291 := bstep (se 1 (by rfl) ⟨597968, by rfl⟩ : syracuseStep 797291 = 1195937) B1195937
theorem B895711 : Blo 527800 895711 := bstep (se 1 (by rfl) ⟨671783, by rfl⟩ : syracuseStep 895711 = 1343567) B1343567
theorem B1190735 : Blo 527800 1190735 := bstep (se 1 (by rfl) ⟨893051, by rfl⟩ : syracuseStep 1190735 = 1786103) B1786103
theorem B797519 : Blo 527800 797519 := bstep (se 1 (by rfl) ⟨598139, by rfl⟩ : syracuseStep 797519 = 1196279) B1196279
theorem B5975005 : Blo 527800 5975005 := bstep (se 3 (by rfl) ⟨1120313, by rfl⟩ : syracuseStep 5975005 = 2240627) B2240627
theorem B1190951 : Blo 527800 1190951 := bstep (se 1 (by rfl) ⟨893213, by rfl⟩ : syracuseStep 1190951 = 1786427) B1786427
theorem B6794279 : Blo 527800 6794279 := bstep (se 1 (by rfl) ⟨5095709, by rfl⟩ : syracuseStep 6794279 = 10191419) B10191419
theorem B896143 : Blo 527800 896143 := bstep (se 1 (by rfl) ⟨672107, by rfl⟩ : syracuseStep 896143 = 1344215) B1344215
theorem B1191131 : Blo 527800 1191131 := bstep (se 1 (by rfl) ⟨893348, by rfl⟩ : syracuseStep 1191131 = 1786697) B1786697
theorem B1289449 : Blo 527800 1289449 := bstep (se 2 (by rfl) ⟨483543, by rfl⟩ : syracuseStep 1289449 = 967087) B967087
theorem B896393 : Blo 527800 896393 := bstep (se 2 (by rfl) ⟨336147, by rfl⟩ : syracuseStep 896393 = 672295) B672295
theorem B1191329 : Blo 527800 1191329 := bstep (se 2 (by rfl) ⟨446748, by rfl⟩ : syracuseStep 1191329 = 893497) B893497
theorem B2141711 : Blo 527800 2141711 := bstep (se 1 (by rfl) ⟨1606283, by rfl⟩ : syracuseStep 2141711 = 3212567) B3212567
theorem B896825 : Blo 527800 896825 := bstep (se 2 (by rfl) ⟨336309, by rfl⟩ : syracuseStep 896825 = 672619) B672619
theorem B1191887 : Blo 527800 1191887 := bstep (se 1 (by rfl) ⟨893915, by rfl⟩ : syracuseStep 1191887 = 1787831) B1787831
theorem B4009985 : Blo 527800 4009985 := bstep (se 2 (by rfl) ⟨1503744, by rfl⟩ : syracuseStep 4009985 = 3007489) B3007489
theorem B3026969 : Blo 527800 3026969 := bstep (se 2 (by rfl) ⟨1135113, by rfl⟩ : syracuseStep 3026969 = 2270227) B2270227
theorem B1192265 : Blo 527800 1192265 := bstep (se 2 (by rfl) ⟨447099, by rfl⟩ : syracuseStep 1192265 = 894199) B894199
theorem B1782107 : Blo 527800 1782107 := bstep (se 1 (by rfl) ⟨1336580, by rfl⟩ : syracuseStep 1782107 = 2673161) B2673161
theorem B1192283 : Blo 527800 1192283 := bstep (se 1 (by rfl) ⟨894212, by rfl⟩ : syracuseStep 1192283 = 1788425) B1788425
theorem B668027 : Blo 527800 668027 := bstep (se 1 (by rfl) ⟨501020, by rfl⟩ : syracuseStep 668027 = 1002041) B1002041
theorem B1356257 : Blo 527800 1356257 := bstep (se 2 (by rfl) ⟨508596, by rfl⟩ : syracuseStep 1356257 = 1017193) B1017193
theorem B2143055 : Blo 527800 2143055 := bstep (se 1 (by rfl) ⟨1607291, by rfl⟩ : syracuseStep 2143055 = 3214583) B3214583
theorem B1192859 : Blo 527800 1192859 := bstep (se 1 (by rfl) ⟨894644, by rfl⟩ : syracuseStep 1192859 = 1789289) B1789289
theorem B1193057 : Blo 527800 1193057 := bstep (se 2 (by rfl) ⟨447396, by rfl⟩ : syracuseStep 1193057 = 894793) B894793
theorem B1783079 : Blo 527800 1783079 := bstep (se 1 (by rfl) ⟨1337309, by rfl⟩ : syracuseStep 1783079 = 2674619) B2674619
theorem B1193255 : Blo 527800 1193255 := bstep (se 1 (by rfl) ⟨894941, by rfl⟩ : syracuseStep 1193255 = 1789883) B1789883
theorem B1160585 : Blo 527800 1160585 := bstep (se 2 (by rfl) ⟨435219, by rfl⟩ : syracuseStep 1160585 = 870439) B870439
theorem B9582119 : Blo 527800 9582119 := bstep (se 1 (by rfl) ⟨7186589, by rfl⟩ : syracuseStep 9582119 = 14373179) B14373179
theorem B1193633 : Blo 527800 1193633 := bstep (se 2 (by rfl) ⟨447612, by rfl⟩ : syracuseStep 1193633 = 895225) B895225
theorem B2537399 : Blo 527800 2537399 := bstep (se 1 (by rfl) ⟨1903049, by rfl⟩ : syracuseStep 2537399 = 3806099) B3806099
theorem B669647 : Blo 527800 669647 := bstep (se 1 (by rfl) ⟨502235, by rfl⟩ : syracuseStep 669647 = 1004471) B1004471
theorem B1193993 : Blo 527800 1193993 := bstep (se 2 (by rfl) ⟨447747, by rfl⟩ : syracuseStep 1193993 = 895495) B895495
theorem B1783943 : Blo 527800 1783943 := bstep (se 1 (by rfl) ⟨1337957, by rfl⟩ : syracuseStep 1783943 = 2675915) B2675915
theorem B2013437 : Blo 527800 2013437 := bstep (se 3 (by rfl) ⟨377519, by rfl⟩ : syracuseStep 2013437 = 755039) B755039
theorem B4962637 : Blo 527800 4962637 := bstep (se 3 (by rfl) ⟨930494, by rfl⟩ : syracuseStep 4962637 = 1860989) B1860989
theorem B1194407 : Blo 527800 1194407 := bstep (se 1 (by rfl) ⟨895805, by rfl⟩ : syracuseStep 1194407 = 1791611) B1791611
theorem B1194515 : Blo 527800 1194515 := bstep (se 1 (by rfl) ⟨895886, by rfl⟩ : syracuseStep 1194515 = 1791773) B1791773
theorem B1194569 : Blo 527800 1194569 := bstep (se 2 (by rfl) ⟨447963, by rfl⟩ : syracuseStep 1194569 = 895927) B895927
theorem B670619 : Blo 527800 670619 := bstep (se 1 (by rfl) ⟨502964, by rfl⟩ : syracuseStep 670619 = 1005929) B1005929
theorem B1194983 : Blo 527800 1194983 := bstep (se 1 (by rfl) ⟨896237, by rfl⟩ : syracuseStep 1194983 = 1792475) B1792475
theorem B1358945 : Blo 527800 1358945 := bstep (se 2 (by rfl) ⟨509604, by rfl⟩ : syracuseStep 1358945 = 1019209) B1019209
theorem B1785185 : Blo 527800 1785185 := bstep (se 2 (by rfl) ⟨669444, by rfl⟩ : syracuseStep 1785185 = 1338889) B1338889
theorem B1129825 : Blo 527800 1129825 := bstep (se 2 (by rfl) ⟨423684, by rfl⟩ : syracuseStep 1129825 = 847369) B847369
theorem B1195361 : Blo 527800 1195361 := bstep (se 2 (by rfl) ⟨448260, by rfl⟩ : syracuseStep 1195361 = 896521) B896521
theorem B1195451 : Blo 527800 1195451 := bstep (se 1 (by rfl) ⟨896588, by rfl⟩ : syracuseStep 1195451 = 1793177) B1793177
theorem B1195577 : Blo 527800 1195577 := bstep (se 2 (by rfl) ⟨448341, by rfl⟩ : syracuseStep 1195577 = 896683) B896683
theorem B2866747 : Blo 527800 2866747 := bstep (se 1 (by rfl) ⟨2150060, by rfl⟩ : syracuseStep 2866747 = 4300121) B4300121
theorem B1130287 : Blo 527800 1130287 := bstep (se 1 (by rfl) ⟨847715, by rfl⟩ : syracuseStep 1130287 = 1695431) B1695431
theorem B1196243 : Blo 527800 1196243 := bstep (se 1 (by rfl) ⟨897182, by rfl⟩ : syracuseStep 1196243 = 1794365) B1794365
theorem B39829765 : Blo 527800 39829765 := bstep (se 4 (by rfl) ⟨3734040, by rfl⟩ : syracuseStep 39829765 = 7468081) B7468081
theorem B1196297 : Blo 527800 1196297 := bstep (se 2 (by rfl) ⟨448611, by rfl⟩ : syracuseStep 1196297 = 897223) B897223
theorem B7258531 : Blo 527800 7258531 := bstep (se 1 (by rfl) ⟨5443898, by rfl⟩ : syracuseStep 7258531 = 10887797) B10887797
theorem B1196513 : Blo 527800 1196513 := bstep (se 2 (by rfl) ⟨448692, by rfl⟩ : syracuseStep 1196513 = 897385) B897385
theorem B9192269 : Blo 527800 9192269 := bstep (se 3 (by rfl) ⟨1723550, by rfl⟩ : syracuseStep 9192269 = 3447101) B3447101
theorem B6800273 : Blo 527800 6800273 := bstep (se 2 (by rfl) ⟨2550102, by rfl⟩ : syracuseStep 6800273 = 5100205) B5100205
theorem B2016353 : Blo 527800 2016353 := bstep (se 2 (by rfl) ⟨756132, by rfl⟩ : syracuseStep 2016353 = 1512265) B1512265
theorem B3818639 : Blo 527800 3818639 := bstep (se 1 (by rfl) ⟨2863979, by rfl⟩ : syracuseStep 3818639 = 5727959) B5727959
theorem B1787129 : Blo 527800 1787129 := bstep (se 2 (by rfl) ⟨670173, by rfl⟩ : syracuseStep 1787129 = 1340347) B1340347
theorem B1787399 : Blo 527800 1787399 := bstep (se 1 (by rfl) ⟨1340549, by rfl⟩ : syracuseStep 1787399 = 2681099) B2681099
theorem B25740989 : Blo 527800 25740989 := bstep (se 3 (by rfl) ⟨4826435, by rfl⟩ : syracuseStep 25740989 = 9652871) B9652871
theorem B4015817 : Blo 527800 4015817 := bstep (se 2 (by rfl) ⟨1505931, by rfl⟩ : syracuseStep 4015817 = 3011863) B3011863
theorem B19384109 : Blo 527800 19384109 := bstep (se 3 (by rfl) ⟨3634520, by rfl⟩ : syracuseStep 19384109 = 7269041) B7269041
theorem B903433 : Blo 527800 903433 := bstep (se 2 (by rfl) ⟨338787, by rfl⟩ : syracuseStep 903433 = 677575) B677575
theorem B2902397 : Blo 527800 2902397 := bstep (se 3 (by rfl) ⟨544199, by rfl⟩ : syracuseStep 2902397 = 1088399) B1088399
theorem B21711239 : Blo 527800 21711239 := bstep (se 1 (by rfl) ⟨16283429, by rfl⟩ : syracuseStep 21711239 = 32566859) B32566859
theorem B1788371 : Blo 527800 1788371 := bstep (se 1 (by rfl) ⟨1341278, by rfl⟩ : syracuseStep 1788371 = 2682557) B2682557
theorem B1788479 : Blo 527800 1788479 := bstep (se 1 (by rfl) ⟨1341359, by rfl⟩ : syracuseStep 1788479 = 2682719) B2682719
theorem B3066491 : Blo 527800 3066491 := bstep (se 1 (by rfl) ⟨2299868, by rfl⟩ : syracuseStep 3066491 = 4599737) B4599737
theorem B4541579 : Blo 527800 4541579 := bstep (se 1 (by rfl) ⟨3406184, by rfl⟩ : syracuseStep 4541579 = 6812369) B6812369
theorem B4509047 : Blo 527800 4509047 := bstep (se 1 (by rfl) ⟨3381785, by rfl⟩ : syracuseStep 4509047 = 6763571) B6763571
theorem B1003195 : Blo 527800 1003195 := bstep (se 1 (by rfl) ⟨752396, by rfl⟩ : syracuseStep 1003195 = 1504793) B1504793
theorem B1790315 : Blo 527800 1790315 := bstep (se 1 (by rfl) ⟨1342736, by rfl⟩ : syracuseStep 1790315 = 2685473) B2685473
theorem B8606087 : Blo 527800 8606087 := bstep (se 1 (by rfl) ⟨6454565, by rfl⟩ : syracuseStep 8606087 = 12909131) B12909131
theorem B9032309 : Blo 527800 9032309 := bstep (se 5 (by rfl) ⟨423389, by rfl⟩ : syracuseStep 9032309 = 846779) B846779
theorem B1790585 : Blo 527800 1790585 := bstep (se 2 (by rfl) ⟨671469, by rfl⟩ : syracuseStep 1790585 = 1342939) B1342939
theorem B2544797 : Blo 527800 2544797 := bstep (se 3 (by rfl) ⟨477149, by rfl⟩ : syracuseStep 2544797 = 954299) B954299
theorem B1692971 : Blo 527800 1692971 := bstep (se 1 (by rfl) ⟨1269728, by rfl⟩ : syracuseStep 1692971 = 2539457) B2539457
theorem B2676077 : Blo 527800 2676077 := bstep (se 3 (by rfl) ⟨501764, by rfl⟩ : syracuseStep 2676077 = 1003529) B1003529
theorem B1005139 : Blo 527800 1005139 := bstep (se 1 (by rfl) ⟨753854, by rfl⟩ : syracuseStep 1005139 = 1507709) B1507709
theorem B1005367 : Blo 527800 1005367 := bstep (se 1 (by rfl) ⟨754025, by rfl⟩ : syracuseStep 1005367 = 1508051) B1508051
theorem B1529705 : Blo 527800 1529705 := bstep (se 2 (by rfl) ⟨573639, by rfl⟩ : syracuseStep 1529705 = 1147279) B1147279
theorem B4512023 : Blo 527800 4512023 := bstep (se 1 (by rfl) ⟨3384017, by rfl⟩ : syracuseStep 4512023 = 6768035) B6768035
theorem B1792367 : Blo 527800 1792367 := bstep (se 1 (by rfl) ⟨1344275, by rfl⟩ : syracuseStep 1792367 = 2688551) B2688551
theorem B2873711 : Blo 527800 2873711 := bstep (se 1 (by rfl) ⟨2155283, by rfl⟩ : syracuseStep 2873711 = 4310567) B4310567
theorem B678395 : Blo 527800 678395 := bstep (se 1 (by rfl) ⟨508796, by rfl⟩ : syracuseStep 678395 = 1017593) B1017593
theorem B1006415 : Blo 527800 1006415 := bstep (se 1 (by rfl) ⟨754811, by rfl⟩ : syracuseStep 1006415 = 1509623) B1509623
theorem B2153387 : Blo 527800 2153387 := bstep (se 1 (by rfl) ⟨1615040, by rfl⟩ : syracuseStep 2153387 = 3230081) B3230081
theorem B3660923 : Blo 527800 3660923 := bstep (se 1 (by rfl) ⟨2745692, by rfl⟩ : syracuseStep 3660923 = 5491385) B5491385
theorem B5790937 : Blo 527800 5790937 := bstep (se 2 (by rfl) ⟨2171601, by rfl⟩ : syracuseStep 5790937 = 4343203) B4343203
theorem B1006825 : Blo 527800 1006825 := bstep (se 2 (by rfl) ⟨377559, by rfl⟩ : syracuseStep 1006825 = 755119) B755119
theorem B9690461 : Blo 527800 9690461 := bstep (se 3 (by rfl) ⟨1816961, by rfl⟩ : syracuseStep 9690461 = 3633923) B3633923
theorem B1006985 : Blo 527800 1006985 := bstep (se 2 (by rfl) ⟨377619, by rfl⟩ : syracuseStep 1006985 = 755239) B755239
theorem B3366359 : Blo 527800 3366359 := bstep (se 1 (by rfl) ⟨2524769, by rfl⟩ : syracuseStep 3366359 = 5049539) B5049539
theorem B3399191 : Blo 527800 3399191 := bstep (se 1 (by rfl) ⟨2549393, by rfl⟩ : syracuseStep 3399191 = 5098787) B5098787
theorem B1072801 : Blo 527800 1072801 := bstep (se 2 (by rfl) ⟨402300, by rfl⟩ : syracuseStep 1072801 = 804601) B804601
theorem B2416339 : Blo 527800 2416339 := bstep (se 1 (by rfl) ⟨1812254, by rfl⟩ : syracuseStep 2416339 = 3624509) B3624509
theorem B2678507 : Blo 527800 2678507 := bstep (se 1 (by rfl) ⟨2008880, by rfl⟩ : syracuseStep 2678507 = 4017761) B4017761
theorem B1793771 : Blo 527800 1793771 := bstep (se 1 (by rfl) ⟨1345328, by rfl⟩ : syracuseStep 1793771 = 2690657) B2690657
theorem B1007417 : Blo 527800 1007417 := bstep (se 2 (by rfl) ⟨377781, by rfl⟩ : syracuseStep 1007417 = 755563) B755563
theorem B8740871 : Blo 527800 8740871 := bstep (se 1 (by rfl) ⟨6555653, by rfl⟩ : syracuseStep 8740871 = 13111307) B13111307
theorem B2678993 : Blo 527800 2678993 := bstep (se 2 (by rfl) ⟨1004622, by rfl⟩ : syracuseStep 2678993 = 2009245) B2009245
theorem B1434131 : Blo 527800 1434131 := bstep (se 1 (by rfl) ⟨1075598, by rfl⟩ : syracuseStep 1434131 = 2151197) B2151197
theorem B1270343 : Blo 527800 1270343 := bstep (se 1 (by rfl) ⟨952757, by rfl⟩ : syracuseStep 1270343 = 1905515) B1905515
theorem B1073839 : Blo 527800 1073839 := bstep (se 1 (by rfl) ⟨805379, by rfl⟩ : syracuseStep 1073839 = 1610759) B1610759
theorem B2679479 : Blo 527800 2679479 := bstep (se 1 (by rfl) ⟨2009609, by rfl⟩ : syracuseStep 2679479 = 4019219) B4019219
theorem B1794743 : Blo 527800 1794743 := bstep (se 1 (by rfl) ⟨1346057, by rfl⟩ : syracuseStep 1794743 = 2692115) B2692115
theorem B5530463 : Blo 527800 5530463 := bstep (se 1 (by rfl) ⟨4147847, by rfl⟩ : syracuseStep 5530463 = 8295695) B8295695
theorem B9659357 : Blo 527800 9659357 := bstep (se 3 (by rfl) ⟨1811129, by rfl⟩ : syracuseStep 9659357 = 3622259) B3622259
theorem B2155511 : Blo 527800 2155511 := bstep (se 1 (by rfl) ⟨1616633, by rfl⟩ : syracuseStep 2155511 = 3233267) B3233267
theorem B1336459 : Blo 527800 1336459 := bstep (se 1 (by rfl) ⟨1002344, by rfl⟩ : syracuseStep 1336459 = 2004689) B2004689
theorem B2679965 : Blo 527800 2679965 := bstep (se 3 (by rfl) ⟨502493, by rfl⟩ : syracuseStep 2679965 = 1004987) B1004987
theorem B1336763 : Blo 527800 1336763 := bstep (se 1 (by rfl) ⟨1002572, by rfl⟩ : syracuseStep 1336763 = 2005145) B2005145
theorem B1009415 : Blo 527800 1009415 := bstep (se 1 (by rfl) ⟨757061, by rfl⟩ : syracuseStep 1009415 = 1514123) B1514123
theorem B21227501 : Blo 527800 21227501 := bstep (se 3 (by rfl) ⟨3980156, by rfl⟩ : syracuseStep 21227501 = 7960313) B7960313
theorem B3008765 : Blo 527800 3008765 := bstep (se 3 (by rfl) ⟨564143, by rfl⟩ : syracuseStep 3008765 = 1128287) B1128287
theorem B2681261 : Blo 527800 2681261 := bstep (se 3 (by rfl) ⟨502736, by rfl⟩ : syracuseStep 2681261 = 1005473) B1005473
theorem B2681423 : Blo 527800 2681423 := bstep (se 1 (by rfl) ⟨2011067, by rfl⟩ : syracuseStep 2681423 = 4022135) B4022135
theorem B1338079 : Blo 527800 1338079 := bstep (se 1 (by rfl) ⟨1003559, by rfl⟩ : syracuseStep 1338079 = 2007119) B2007119
theorem B1075987 : Blo 527800 1075987 := bstep (se 1 (by rfl) ⟨806990, by rfl⟩ : syracuseStep 1075987 = 1613981) B1613981
theorem B1338191 : Blo 527800 1338191 := bstep (se 1 (by rfl) ⟨1003643, by rfl⟩ : syracuseStep 1338191 = 2007287) B2007287
theorem B847241 : Blo 527800 847241 := bstep (se 2 (by rfl) ⟨317715, by rfl⟩ : syracuseStep 847241 = 635431) B635431
theorem B1338839 : Blo 527800 1338839 := bstep (se 1 (by rfl) ⟨1004129, by rfl⟩ : syracuseStep 1338839 = 2008259) B2008259
theorem B2289167 : Blo 527800 2289167 := bstep (se 1 (by rfl) ⟨1716875, by rfl⟩ : syracuseStep 2289167 = 3433751) B3433751
theorem B10153511 : Blo 527800 10153511 := bstep (se 1 (by rfl) ⟨7615133, by rfl⟩ : syracuseStep 10153511 = 15230267) B15230267
theorem B1011295 : Blo 527800 1011295 := bstep (se 1 (by rfl) ⟨758471, by rfl⟩ : syracuseStep 1011295 = 1516943) B1516943
theorem B1339193 : Blo 527800 1339193 := bstep (se 2 (by rfl) ⟨502197, by rfl⟩ : syracuseStep 1339193 = 1004395) B1004395
theorem B2682881 : Blo 527800 2682881 := bstep (se 2 (by rfl) ⟨1006080, by rfl⟩ : syracuseStep 2682881 = 2012161) B2012161
theorem B2257105 : Blo 527800 2257105 := bstep (se 2 (by rfl) ⟨846414, by rfl⟩ : syracuseStep 2257105 = 1692829) B1692829
theorem B3404339 : Blo 527800 3404339 := bstep (se 1 (by rfl) ⟨2553254, by rfl⟩ : syracuseStep 3404339 = 5106509) B5106509
theorem B1208953 : Blo 527800 1208953 := bstep (se 2 (by rfl) ⟨453357, by rfl⟩ : syracuseStep 1208953 = 906715) B906715
theorem B1274543 : Blo 527800 1274543 := bstep (se 1 (by rfl) ⟨955907, by rfl⟩ : syracuseStep 1274543 = 1911815) B1911815
theorem B6025913 : Blo 527800 6025913 := bstep (se 2 (by rfl) ⟨2259717, by rfl⟩ : syracuseStep 6025913 = 4519435) B4519435
theorem B1274591 : Blo 527800 1274591 := bstep (se 1 (by rfl) ⟨955943, by rfl⟩ : syracuseStep 1274591 = 1911887) B1911887
theorem B2683691 : Blo 527800 2683691 := bstep (se 1 (by rfl) ⟨2012768, by rfl⟩ : syracuseStep 2683691 = 4025537) B4025537
theorem B2552795 : Blo 527800 2552795 := bstep (se 1 (by rfl) ⟨1914596, by rfl⟩ : syracuseStep 2552795 = 3829193) B3829193
theorem B4027481 : Blo 527800 4027481 := bstep (se 2 (by rfl) ⟨1510305, by rfl⟩ : syracuseStep 4027481 = 3020611) B3020611
theorem B2258063 : Blo 527800 2258063 := bstep (se 1 (by rfl) ⟨1693547, by rfl⟩ : syracuseStep 2258063 = 3387095) B3387095
theorem B2454893 : Blo 527800 2454893 := bstep (se 3 (by rfl) ⟨460292, by rfl⟩ : syracuseStep 2454893 = 920585) B920585
theorem B1340833 : Blo 527800 1340833 := bstep (se 2 (by rfl) ⟨502812, by rfl⟩ : syracuseStep 1340833 = 1005625) B1005625
theorem B4519709 : Blo 527800 4519709 := bstep (se 3 (by rfl) ⟨847445, by rfl⟩ : syracuseStep 4519709 = 1694891) B1694891
theorem B5110199 : Blo 527800 5110199 := bstep (se 1 (by rfl) ⟨3832649, by rfl⟩ : syracuseStep 5110199 = 7665299) B7665299
theorem B15464945 : Blo 527800 15464945 := bstep (se 2 (by rfl) ⟨5799354, by rfl⟩ : syracuseStep 15464945 = 11598709) B11598709
theorem B752123 : Blo 527800 752123 := bstep (se 1 (by rfl) ⟨564092, by rfl⟩ : syracuseStep 752123 = 1128185) B1128185
theorem B1341947 : Blo 527800 1341947 := bstep (se 1 (by rfl) ⟨1006460, by rfl⟩ : syracuseStep 1341947 = 2012921) B2012921
theorem B1145519 : Blo 527800 1145519 := bstep (se 1 (by rfl) ⟨859139, by rfl⟩ : syracuseStep 1145519 = 1718279) B1718279
theorem B2685635 : Blo 527800 2685635 := bstep (se 1 (by rfl) ⟨2014226, by rfl⟩ : syracuseStep 2685635 = 4028453) B4028453
theorem B4652185 : Blo 527800 4652185 := bstep (se 2 (by rfl) ⟨1744569, by rfl⟩ : syracuseStep 4652185 = 3489139) B3489139
theorem B851239 : Blo 527800 851239 := bstep (se 1 (by rfl) ⟨638429, by rfl⟩ : syracuseStep 851239 = 1276859) B1276859
theorem B1342919 : Blo 527800 1342919 := bstep (se 1 (by rfl) ⟨1007189, by rfl⟩ : syracuseStep 1342919 = 2014379) B2014379
theorem B1506775 : Blo 527800 1506775 := bstep (se 1 (by rfl) ⟨1130081, by rfl⟩ : syracuseStep 1506775 = 2260163) B2260163
theorem B4029911 : Blo 527800 4029911 := bstep (se 1 (by rfl) ⟨3022433, by rfl⟩ : syracuseStep 4029911 = 6044867) B6044867
theorem B9207647 : Blo 527800 9207647 := bstep (se 1 (by rfl) ⟨6905735, by rfl⟩ : syracuseStep 9207647 = 13811471) B13811471
theorem B9633667 : Blo 527800 9633667 := bstep (se 1 (by rfl) ⟨7225250, by rfl⟩ : syracuseStep 9633667 = 14450501) B14450501
theorem B2687255 : Blo 527800 2687255 := bstep (se 1 (by rfl) ⟨2015441, by rfl⟩ : syracuseStep 2687255 = 4030883) B4030883
theorem B1507835 : Blo 527800 1507835 := bstep (se 1 (by rfl) ⟨1130876, by rfl⟩ : syracuseStep 1507835 = 2261753) B2261753
theorem B6128179 : Blo 527800 6128179 := bstep (se 1 (by rfl) ⟨4596134, by rfl⟩ : syracuseStep 6128179 = 9192269) B9192269
theorem B1344235 : Blo 527800 1344235 := bstep (se 1 (by rfl) ⟨1008176, by rfl⟩ : syracuseStep 1344235 = 2016353) B2016353
theorem B2032595 : Blo 527800 2032595 := bstep (se 1 (by rfl) ⟨1524446, by rfl⟩ : syracuseStep 2032595 = 3048893) B3048893
theorem B3015737 : Blo 527800 3015737 := bstep (se 2 (by rfl) ⟨1130901, by rfl⟩ : syracuseStep 3015737 = 2261803) B2261803
theorem B2688875 : Blo 527800 2688875 := bstep (se 1 (by rfl) ⟨2016656, by rfl⟩ : syracuseStep 2688875 = 4033313) B4033313
theorem B6031745 : Blo 527800 6031745 := bstep (se 2 (by rfl) ⟨2261904, by rfl⟩ : syracuseStep 6031745 = 4523809) B4523809
theorem B5737391 : Blo 527800 5737391 := bstep (se 1 (by rfl) ⟨4303043, by rfl⟩ : syracuseStep 5737391 = 8606087) B8606087
theorem B6786125 : Blo 527800 6786125 := bstep (se 3 (by rfl) ⟨1272398, by rfl⟩ : syracuseStep 6786125 = 2544797) B2544797
theorem B527847 : Blo 527800 527847 := bstep (se 1 (by rfl) ⟨395885, by rfl⟩ : syracuseStep 527847 = 791771) B791771
theorem B2297339 : Blo 527800 2297339 := bstep (se 1 (by rfl) ⟨1723004, by rfl⟩ : syracuseStep 2297339 = 3446009) B3446009
theorem B6884947 : Blo 527800 6884947 := bstep (se 1 (by rfl) ⟨5163710, by rfl⟩ : syracuseStep 6884947 = 10327421) B10327421
theorem B527963 : Blo 527800 527963 := bstep (se 1 (by rfl) ⟨395972, by rfl⟩ : syracuseStep 527963 = 791945) B791945
theorem B1511207 : Blo 527800 1511207 := bstep (se 1 (by rfl) ⟨1133405, by rfl⟩ : syracuseStep 1511207 = 2266811) B2266811
theorem B528199 : Blo 527800 528199 := bstep (se 1 (by rfl) ⟨396149, by rfl⟩ : syracuseStep 528199 = 792299) B792299
theorem B1019803 : Blo 527800 1019803 := bstep (se 1 (by rfl) ⟨764852, by rfl⟩ : syracuseStep 1019803 = 1529705) B1529705
theorem B7966673 : Blo 527800 7966673 := bstep (se 2 (by rfl) ⟨2987502, by rfl⟩ : syracuseStep 7966673 = 5975005) B5975005
theorem B593887 : Blo 527800 593887 := bstep (se 1 (by rfl) ⟨445415, by rfl⟩ : syracuseStep 593887 = 890831) B890831
theorem B528351 : Blo 527800 528351 := bstep (se 1 (by rfl) ⟨396263, by rfl⟩ : syracuseStep 528351 = 792527) B792527
theorem B5738597 : Blo 527800 5738597 := bstep (se 4 (by rfl) ⟨537993, by rfl⟩ : syracuseStep 5738597 = 1075987) B1075987
theorem B528615 : Blo 527800 528615 := bstep (se 1 (by rfl) ⟨396461, by rfl⟩ : syracuseStep 528615 = 792923) B792923
theorem B528767 : Blo 527800 528767 := bstep (se 1 (by rfl) ⟨396575, by rfl⟩ : syracuseStep 528767 = 793151) B793151
theorem B528847 : Blo 527800 528847 := bstep (se 1 (by rfl) ⟨396635, by rfl⟩ : syracuseStep 528847 = 793271) B793271
theorem B594535 : Blo 527800 594535 := bstep (se 1 (by rfl) ⟨445901, by rfl⟩ : syracuseStep 594535 = 891803) B891803
theorem B528999 : Blo 527800 528999 := bstep (se 1 (by rfl) ⟨396749, by rfl⟩ : syracuseStep 528999 = 793499) B793499
theorem B1348393 : Blo 527800 1348393 := bstep (se 2 (by rfl) ⟨505647, by rfl⟩ : syracuseStep 1348393 = 1011295) B1011295
theorem B529263 : Blo 527800 529263 := bstep (se 1 (by rfl) ⟨396947, by rfl⟩ : syracuseStep 529263 = 793895) B793895
theorem B6460307 : Blo 527800 6460307 := bstep (se 1 (by rfl) ⟨4845230, by rfl⟩ : syracuseStep 6460307 = 9690461) B9690461
theorem B529319 : Blo 527800 529319 := bstep (se 1 (by rfl) ⟨396989, by rfl⟩ : syracuseStep 529319 = 793979) B793979
theorem B529403 : Blo 527800 529403 := bstep (se 1 (by rfl) ⟨397052, by rfl⟩ : syracuseStep 529403 = 794105) B794105
theorem B2266127 : Blo 527800 2266127 := bstep (se 1 (by rfl) ⟨1699595, by rfl⟩ : syracuseStep 2266127 = 3399191) B3399191
theorem B529471 : Blo 527800 529471 := bstep (se 1 (by rfl) ⟨397103, by rfl⟩ : syracuseStep 529471 = 794207) B794207
theorem B9311377 : Blo 527800 9311377 := bstep (se 2 (by rfl) ⟨3491766, by rfl⟩ : syracuseStep 9311377 = 6983533) B6983533
theorem B791759 : Blo 527800 791759 := bstep (se 1 (by rfl) ⟨593819, by rfl⟩ : syracuseStep 791759 = 1187639) B1187639
theorem B529615 : Blo 527800 529615 := bstep (se 1 (by rfl) ⟨397211, by rfl⟩ : syracuseStep 529615 = 794423) B794423
theorem B791963 : Blo 527800 791963 := bstep (se 1 (by rfl) ⟨593972, by rfl⟩ : syracuseStep 791963 = 1187945) B1187945
theorem B529819 : Blo 527800 529819 := bstep (se 1 (by rfl) ⟨397364, by rfl⟩ : syracuseStep 529819 = 794729) B794729
theorem B3544633 : Blo 527800 3544633 := bstep (se 2 (by rfl) ⟨1329237, by rfl⟩ : syracuseStep 3544633 = 2658475) B2658475
theorem B530031 : Blo 527800 530031 := bstep (se 1 (by rfl) ⟨397523, by rfl⟩ : syracuseStep 530031 = 795047) B795047
theorem B792185 : Blo 527800 792185 := bstep (se 2 (by rfl) ⟨297069, by rfl⟩ : syracuseStep 792185 = 594139) B594139
theorem B530087 : Blo 527800 530087 := bstep (se 1 (by rfl) ⟨397565, by rfl⟩ : syracuseStep 530087 = 795131) B795131
theorem B956087 : Blo 527800 956087 := bstep (se 1 (by rfl) ⟨717065, by rfl⟩ : syracuseStep 956087 = 1434131) B1434131
theorem B792287 : Blo 527800 792287 := bstep (se 1 (by rfl) ⟨594215, by rfl⟩ : syracuseStep 792287 = 1188431) B1188431
theorem B530171 : Blo 527800 530171 := bstep (se 1 (by rfl) ⟨397628, by rfl⟩ : syracuseStep 530171 = 795257) B795257
theorem B530207 : Blo 527800 530207 := bstep (se 1 (by rfl) ⟨397655, by rfl⟩ : syracuseStep 530207 = 795311) B795311
theorem B792383 : Blo 527800 792383 := bstep (se 1 (by rfl) ⟨594287, by rfl⟩ : syracuseStep 792383 = 1188575) B1188575
theorem B530239 : Blo 527800 530239 := bstep (se 1 (by rfl) ⟨397679, by rfl⟩ : syracuseStep 530239 = 795359) B795359
theorem B6428483 : Blo 527800 6428483 := bstep (se 1 (by rfl) ⟨4821362, by rfl⟩ : syracuseStep 6428483 = 9642725) B9642725
theorem B792551 : Blo 527800 792551 := bstep (se 1 (by rfl) ⟨594413, by rfl⟩ : syracuseStep 792551 = 1188827) B1188827
theorem B530415 : Blo 527800 530415 := bstep (se 1 (by rfl) ⟨397811, by rfl⟩ : syracuseStep 530415 = 795623) B795623
theorem B792569 : Blo 527800 792569 := bstep (se 2 (by rfl) ⟨297213, by rfl⟩ : syracuseStep 792569 = 594427) B594427
theorem B792671 : Blo 527800 792671 := bstep (se 1 (by rfl) ⟨594503, by rfl⟩ : syracuseStep 792671 = 1189007) B1189007
theorem B792731 : Blo 527800 792731 := bstep (se 1 (by rfl) ⟨594548, by rfl⟩ : syracuseStep 792731 = 1189097) B1189097
theorem B530587 : Blo 527800 530587 := bstep (se 1 (by rfl) ⟨397940, by rfl⟩ : syracuseStep 530587 = 795881) B795881
theorem B1611937 : Blo 527800 1611937 := bstep (se 2 (by rfl) ⟨604476, by rfl⟩ : syracuseStep 1611937 = 1208953) B1208953
theorem B792767 : Blo 527800 792767 := bstep (se 1 (by rfl) ⟨594575, by rfl⟩ : syracuseStep 792767 = 1189151) B1189151
theorem B530623 : Blo 527800 530623 := bstep (se 1 (by rfl) ⟨397967, by rfl⟩ : syracuseStep 530623 = 795935) B795935
theorem B5707979 : Blo 527800 5707979 := bstep (se 1 (by rfl) ⟨4280984, by rfl⟩ : syracuseStep 5707979 = 8561969) B8561969
theorem B792809 : Blo 527800 792809 := bstep (se 2 (by rfl) ⟨297303, by rfl⟩ : syracuseStep 792809 = 594607) B594607
theorem B891175 : Blo 527800 891175 := bstep (se 1 (by rfl) ⟨668381, by rfl⟩ : syracuseStep 891175 = 1336763) B1336763
theorem B530735 : Blo 527800 530735 := bstep (se 1 (by rfl) ⟨398051, by rfl⟩ : syracuseStep 530735 = 796103) B796103
theorem B7739725 : Blo 527800 7739725 := bstep (se 3 (by rfl) ⟨1451198, by rfl⟩ : syracuseStep 7739725 = 2902397) B2902397
theorem B793115 : Blo 527800 793115 := bstep (se 1 (by rfl) ⟨594836, by rfl⟩ : syracuseStep 793115 = 1189673) B1189673
theorem B530971 : Blo 527800 530971 := bstep (se 1 (by rfl) ⟨398228, by rfl⟩ : syracuseStep 530971 = 796457) B796457
theorem B530975 : Blo 527800 530975 := bstep (se 1 (by rfl) ⟨398231, by rfl⟩ : syracuseStep 530975 = 796463) B796463
theorem B793193 : Blo 527800 793193 := bstep (se 2 (by rfl) ⟨297447, by rfl⟩ : syracuseStep 793193 = 594895) B594895
theorem B2005661 : Blo 527800 2005661 := bstep (se 3 (by rfl) ⟨376061, by rfl⟩ : syracuseStep 2005661 = 752123) B752123
theorem B1809053 : Blo 527800 1809053 := bstep (se 3 (by rfl) ⟨339197, by rfl⟩ : syracuseStep 1809053 = 678395) B678395
theorem B2005843 : Blo 527800 2005843 := bstep (se 1 (by rfl) ⟨1504382, by rfl⟩ : syracuseStep 2005843 = 3008765) B3008765
theorem B531291 : Blo 527800 531291 := bstep (se 1 (by rfl) ⟨398468, by rfl⟩ : syracuseStep 531291 = 796937) B796937
theorem B531359 : Blo 527800 531359 := bstep (se 1 (by rfl) ⟨398519, by rfl⟩ : syracuseStep 531359 = 797039) B797039
theorem B531503 : Blo 527800 531503 := bstep (se 1 (by rfl) ⟨398627, by rfl⟩ : syracuseStep 531503 = 797255) B797255
theorem B531527 : Blo 527800 531527 := bstep (se 1 (by rfl) ⟨398645, by rfl⟩ : syracuseStep 531527 = 797291) B797291
theorem B793721 : Blo 527800 793721 := bstep (se 2 (by rfl) ⟨297645, by rfl⟩ : syracuseStep 793721 = 595291) B595291
theorem B892127 : Blo 527800 892127 := bstep (se 1 (by rfl) ⟨669095, by rfl⟩ : syracuseStep 892127 = 1338191) B1338191
theorem B793823 : Blo 527800 793823 := bstep (se 1 (by rfl) ⟨595367, by rfl⟩ : syracuseStep 793823 = 1190735) B1190735
theorem B531679 : Blo 527800 531679 := bstep (se 1 (by rfl) ⟨398759, by rfl⟩ : syracuseStep 531679 = 797519) B797519
theorem B793865 : Blo 527800 793865 := bstep (se 2 (by rfl) ⟨297699, by rfl⟩ : syracuseStep 793865 = 595399) B595399
theorem B793967 : Blo 527800 793967 := bstep (se 1 (by rfl) ⟨595475, by rfl⟩ : syracuseStep 793967 = 1190951) B1190951
theorem B4529519 : Blo 527800 4529519 := bstep (se 1 (by rfl) ⟨3397139, by rfl⟩ : syracuseStep 4529519 = 6794279) B6794279
theorem B5086597 : Blo 527800 5086597 := bstep (se 4 (by rfl) ⟨476868, by rfl⟩ : syracuseStep 5086597 = 953737) B953737
theorem B794087 : Blo 527800 794087 := bstep (se 1 (by rfl) ⟨595565, by rfl⟩ : syracuseStep 794087 = 1191131) B1191131
theorem B564827 : Blo 527800 564827 := bstep (se 1 (by rfl) ⟨423620, by rfl⟩ : syracuseStep 564827 = 847241) B847241
theorem B597595 : Blo 527800 597595 := bstep (se 1 (by rfl) ⟨448196, by rfl⟩ : syracuseStep 597595 = 896393) B896393
theorem B794219 : Blo 527800 794219 := bstep (se 1 (by rfl) ⟨595664, by rfl⟩ : syracuseStep 794219 = 1191329) B1191329
theorem B892559 : Blo 527800 892559 := bstep (se 1 (by rfl) ⟨669419, by rfl⟩ : syracuseStep 892559 = 1338839) B1338839
theorem B794345 : Blo 527800 794345 := bstep (se 2 (by rfl) ⟨297879, by rfl⟩ : syracuseStep 794345 = 595759) B595759
theorem B794489 : Blo 527800 794489 := bstep (se 2 (by rfl) ⟨297933, by rfl⟩ : syracuseStep 794489 = 595867) B595867
theorem B892795 : Blo 527800 892795 := bstep (se 1 (by rfl) ⟨669596, by rfl⟩ : syracuseStep 892795 = 1339193) B1339193
theorem B597883 : Blo 527800 597883 := bstep (se 1 (by rfl) ⟨448412, by rfl⟩ : syracuseStep 597883 = 896825) B896825
theorem B794591 : Blo 527800 794591 := bstep (se 1 (by rfl) ⟨595943, by rfl⟩ : syracuseStep 794591 = 1191887) B1191887
theorem B794843 : Blo 527800 794843 := bstep (se 1 (by rfl) ⟨596132, by rfl⟩ : syracuseStep 794843 = 1192265) B1192265
theorem B1188071 : Blo 527800 1188071 := bstep (se 1 (by rfl) ⟨891053, by rfl⟩ : syracuseStep 1188071 = 1782107) B1782107
theorem B794855 : Blo 527800 794855 := bstep (se 1 (by rfl) ⟨596141, by rfl⟩ : syracuseStep 794855 = 1192283) B1192283
theorem B2269559 : Blo 527800 2269559 := bstep (se 1 (by rfl) ⟨1702169, by rfl⟩ : syracuseStep 2269559 = 3404339) B3404339
theorem B795017 : Blo 527800 795017 := bstep (se 2 (by rfl) ⟨298131, by rfl⟩ : syracuseStep 795017 = 596263) B596263
theorem B795113 : Blo 527800 795113 := bstep (se 2 (by rfl) ⟨298167, by rfl⟩ : syracuseStep 795113 = 596335) B596335
theorem B795239 : Blo 527800 795239 := bstep (se 1 (by rfl) ⟨596429, by rfl⟩ : syracuseStep 795239 = 1192859) B1192859
theorem B795371 : Blo 527800 795371 := bstep (se 1 (by rfl) ⟨596528, by rfl⟩ : syracuseStep 795371 = 1193057) B1193057
theorem B795401 : Blo 527800 795401 := bstep (se 2 (by rfl) ⟨298275, by rfl⟩ : syracuseStep 795401 = 596551) B596551
theorem B1188665 : Blo 527800 1188665 := bstep (se 2 (by rfl) ⟨445749, by rfl⟩ : syracuseStep 1188665 = 891499) B891499
theorem B1188719 : Blo 527800 1188719 := bstep (se 1 (by rfl) ⟨891539, by rfl⟩ : syracuseStep 1188719 = 1783079) B1783079
theorem B795503 : Blo 527800 795503 := bstep (se 1 (by rfl) ⟨596627, by rfl⟩ : syracuseStep 795503 = 1193255) B1193255
theorem B795755 : Blo 527800 795755 := bstep (se 1 (by rfl) ⟨596816, by rfl⟩ : syracuseStep 795755 = 1193633) B1193633
theorem B795995 : Blo 527800 795995 := bstep (se 1 (by rfl) ⟨596996, by rfl⟩ : syracuseStep 795995 = 1193993) B1193993
theorem B1189295 : Blo 527800 1189295 := bstep (se 1 (by rfl) ⟨891971, by rfl⟩ : syracuseStep 1189295 = 1783943) B1783943
theorem B6202913 : Blo 527800 6202913 := bstep (se 2 (by rfl) ⟨2326092, by rfl⟩ : syracuseStep 6202913 = 4652185) B4652185
theorem B796271 : Blo 527800 796271 := bstep (se 1 (by rfl) ⟨597203, by rfl⟩ : syracuseStep 796271 = 1194407) B1194407
theorem B894631 : Blo 527800 894631 := bstep (se 1 (by rfl) ⟨670973, by rfl⟩ : syracuseStep 894631 = 1341947) B1341947
theorem B796343 : Blo 527800 796343 := bstep (se 1 (by rfl) ⟨597257, by rfl⟩ : syracuseStep 796343 = 1194515) B1194515
theorem B796379 : Blo 527800 796379 := bstep (se 1 (by rfl) ⟨597284, by rfl⟩ : syracuseStep 796379 = 1194569) B1194569
theorem B763679 : Blo 527800 763679 := bstep (se 1 (by rfl) ⟨572759, by rfl⟩ : syracuseStep 763679 = 1145519) B1145519
theorem B796553 : Blo 527800 796553 := bstep (se 2 (by rfl) ⟨298707, by rfl⟩ : syracuseStep 796553 = 597415) B597415
theorem B2009033 : Blo 527800 2009033 := bstep (se 2 (by rfl) ⟨753387, by rfl⟩ : syracuseStep 2009033 = 1506775) B1506775
theorem B796655 : Blo 527800 796655 := bstep (se 1 (by rfl) ⟨597491, by rfl⟩ : syracuseStep 796655 = 1194983) B1194983
theorem B1190123 : Blo 527800 1190123 := bstep (se 1 (by rfl) ⟨892592, by rfl⟩ : syracuseStep 1190123 = 1785185) B1785185
theorem B796907 : Blo 527800 796907 := bstep (se 1 (by rfl) ⟨597680, by rfl⟩ : syracuseStep 796907 = 1195361) B1195361
theorem B3221785 : Blo 527800 3221785 := bstep (se 2 (by rfl) ⟨1208169, by rfl⟩ : syracuseStep 3221785 = 2416339) B2416339
theorem B796967 : Blo 527800 796967 := bstep (se 1 (by rfl) ⟨597725, by rfl⟩ : syracuseStep 796967 = 1195451) B1195451
theorem B895279 : Blo 527800 895279 := bstep (se 1 (by rfl) ⟨671459, by rfl⟩ : syracuseStep 895279 = 1342919) B1342919
theorem B797051 : Blo 527800 797051 := bstep (se 1 (by rfl) ⟨597788, by rfl⟩ : syracuseStep 797051 = 1195577) B1195577
theorem B6138431 : Blo 527800 6138431 := bstep (se 1 (by rfl) ⟨4603823, by rfl⟩ : syracuseStep 6138431 = 9207647) B9207647
theorem B797321 : Blo 527800 797321 := bstep (se 2 (by rfl) ⟨298995, by rfl⟩ : syracuseStep 797321 = 597991) B597991
theorem B895799 : Blo 527800 895799 := bstep (se 1 (by rfl) ⟨671849, by rfl⟩ : syracuseStep 895799 = 1343699) B1343699
theorem B797495 : Blo 527800 797495 := bstep (se 1 (by rfl) ⟨598121, by rfl⟩ : syracuseStep 797495 = 1196243) B1196243
theorem B797531 : Blo 527800 797531 := bstep (se 1 (by rfl) ⟨598148, by rfl⟩ : syracuseStep 797531 = 1196297) B1196297
theorem B797675 : Blo 527800 797675 := bstep (se 1 (by rfl) ⟨598256, by rfl⟩ : syracuseStep 797675 = 1196513) B1196513
theorem B9678041 : Blo 527800 9678041 := bstep (se 2 (by rfl) ⟨3629265, by rfl⟩ : syracuseStep 9678041 = 7258531) B7258531
theorem B4533515 : Blo 527800 4533515 := bstep (se 1 (by rfl) ⟨3400136, by rfl⟩ : syracuseStep 4533515 = 6800273) B6800273
theorem B1191419 : Blo 527800 1191419 := bstep (se 1 (by rfl) ⟨893564, by rfl⟩ : syracuseStep 1191419 = 1787129) B1787129
theorem B896575 : Blo 527800 896575 := bstep (se 1 (by rfl) ⟨672431, by rfl⟩ : syracuseStep 896575 = 1344863) B1344863
theorem B1781405 : Blo 527800 1781405 := bstep (se 3 (by rfl) ⟨334013, by rfl⟩ : syracuseStep 1781405 = 668027) B668027
theorem B1191599 : Blo 527800 1191599 := bstep (se 1 (by rfl) ⟨893699, by rfl⟩ : syracuseStep 1191599 = 1787399) B1787399
theorem B12922739 : Blo 527800 12922739 := bstep (se 1 (by rfl) ⟨9692054, by rfl⟩ : syracuseStep 12922739 = 19384109) B19384109
theorem B1781945 : Blo 527800 1781945 := bstep (se 2 (by rfl) ⟨668229, by rfl⟩ : syracuseStep 1781945 = 1336459) B1336459
theorem B3387581 : Blo 527800 3387581 := bstep (se 3 (by rfl) ⟨635171, by rfl⟩ : syracuseStep 3387581 = 1270343) B1270343
theorem B897311 : Blo 527800 897311 := bstep (se 1 (by rfl) ⟨672983, by rfl⟩ : syracuseStep 897311 = 1345967) B1345967
theorem B1192247 : Blo 527800 1192247 := bstep (se 1 (by rfl) ⟨894185, by rfl⟩ : syracuseStep 1192247 = 1788371) B1788371
theorem B1192319 : Blo 527800 1192319 := bstep (se 1 (by rfl) ⟨894239, by rfl⟩ : syracuseStep 1192319 = 1788479) B1788479
theorem B2044327 : Blo 527800 2044327 := bstep (se 1 (by rfl) ⟨1533245, by rfl⟩ : syracuseStep 2044327 = 3066491) B3066491
theorem B3027401 : Blo 527800 3027401 := bstep (se 2 (by rfl) ⟨1135275, by rfl⟩ : syracuseStep 3027401 = 2270551) B2270551
theorem B5092055 : Blo 527800 5092055 := bstep (se 1 (by rfl) ⟨3819041, by rfl⟩ : syracuseStep 5092055 = 7638083) B7638083
theorem B3027719 : Blo 527800 3027719 := bstep (se 1 (by rfl) ⟨2270789, by rfl⟩ : syracuseStep 3027719 = 4541579) B4541579
theorem B5714813 : Blo 527800 5714813 := bstep (se 3 (by rfl) ⟨1071527, by rfl⟩ : syracuseStep 5714813 = 2143055) B2143055
theorem B2012435 : Blo 527800 2012435 := bstep (se 1 (by rfl) ⟨1509326, by rfl⟩ : syracuseStep 2012435 = 3018653) B3018653
theorem B5748029 : Blo 527800 5748029 := bstep (se 3 (by rfl) ⟨1077755, by rfl⟩ : syracuseStep 5748029 = 2155511) B2155511
theorem B1193543 : Blo 527800 1193543 := bstep (se 1 (by rfl) ⟨895157, by rfl⟩ : syracuseStep 1193543 = 1790315) B1790315
theorem B1193723 : Blo 527800 1193723 := bstep (se 1 (by rfl) ⟨895292, by rfl⟩ : syracuseStep 1193723 = 1790585) B1790585
theorem B1128647 : Blo 527800 1128647 := bstep (se 1 (by rfl) ⟨846485, by rfl⟩ : syracuseStep 1128647 = 1692971) B1692971
theorem B1784051 : Blo 527800 1784051 := bstep (se 1 (by rfl) ⟨1338038, by rfl⟩ : syracuseStep 1784051 = 2676077) B2676077
theorem B1784105 : Blo 527800 1784105 := bstep (se 2 (by rfl) ⟨669039, by rfl⟩ : syracuseStep 1784105 = 1338079) B1338079
theorem B1194281 : Blo 527800 1194281 := bstep (se 2 (by rfl) ⟨447855, by rfl⟩ : syracuseStep 1194281 = 895711) B895711
theorem B2537801 : Blo 527800 2537801 := bstep (se 2 (by rfl) ⟨951675, by rfl⟩ : syracuseStep 2537801 = 1903351) B1903351
theorem B2144825 : Blo 527800 2144825 := bstep (se 2 (by rfl) ⟨804309, by rfl⟩ : syracuseStep 2144825 = 1608619) B1608619
theorem B1194857 : Blo 527800 1194857 := bstep (se 2 (by rfl) ⟨448071, by rfl⟩ : syracuseStep 1194857 = 896143) B896143
theorem B1194911 : Blo 527800 1194911 := bstep (se 1 (by rfl) ⟨896183, by rfl⟩ : syracuseStep 1194911 = 1792367) B1792367
theorem B1915807 : Blo 527800 1915807 := bstep (se 1 (by rfl) ⟨1436855, by rfl⟩ : syracuseStep 1915807 = 2873711) B2873711
theorem B1719265 : Blo 527800 1719265 := bstep (se 2 (by rfl) ⟨644724, by rfl⟩ : syracuseStep 1719265 = 1289449) B1289449
theorem B670943 : Blo 527800 670943 := bstep (se 1 (by rfl) ⟨503207, by rfl⟩ : syracuseStep 670943 = 1006415) B1006415
theorem B1359335 : Blo 527800 1359335 := bstep (se 1 (by rfl) ⟨1019501, by rfl⟩ : syracuseStep 1359335 = 2039003) B2039003
theorem B671323 : Blo 527800 671323 := bstep (se 1 (by rfl) ⟨503492, by rfl⟩ : syracuseStep 671323 = 1006985) B1006985
theorem B2244239 : Blo 527800 2244239 := bstep (se 1 (by rfl) ⟨1683179, by rfl⟩ : syracuseStep 2244239 = 3366359) B3366359
theorem B1785671 : Blo 527800 1785671 := bstep (se 1 (by rfl) ⟨1339253, by rfl⟩ : syracuseStep 1785671 = 2678507) B2678507
theorem B1195847 : Blo 527800 1195847 := bstep (se 1 (by rfl) ⟨896885, by rfl⟩ : syracuseStep 1195847 = 1793771) B1793771
theorem B2015063 : Blo 527800 2015063 := bstep (se 1 (by rfl) ⟨1511297, by rfl⟩ : syracuseStep 2015063 = 3022595) B3022595
theorem B1785725 : Blo 527800 1785725 := bstep (se 3 (by rfl) ⟨334823, by rfl⟩ : syracuseStep 1785725 = 669647) B669647
theorem B1359787 : Blo 527800 1359787 := bstep (se 1 (by rfl) ⟨1019840, by rfl⟩ : syracuseStep 1359787 = 2039681) B2039681
theorem B1785995 : Blo 527800 1785995 := bstep (se 1 (by rfl) ⟨1339496, by rfl⟩ : syracuseStep 1785995 = 2678993) B2678993
theorem B3391627 : Blo 527800 3391627 := bstep (se 1 (by rfl) ⟨2543720, by rfl⟩ : syracuseStep 3391627 = 5087441) B5087441
theorem B1786319 : Blo 527800 1786319 := bstep (se 1 (by rfl) ⟨1339739, by rfl⟩ : syracuseStep 1786319 = 2679479) B2679479
theorem B1196495 : Blo 527800 1196495 := bstep (se 1 (by rfl) ⟨897371, by rfl⟩ : syracuseStep 1196495 = 1794743) B1794743
theorem B3686975 : Blo 527800 3686975 := bstep (se 1 (by rfl) ⟨2765231, by rfl⟩ : syracuseStep 3686975 = 5530463) B5530463
theorem B6439571 : Blo 527800 6439571 := bstep (se 1 (by rfl) ⟨4829678, by rfl⟩ : syracuseStep 6439571 = 9659357) B9659357
theorem B1786643 : Blo 527800 1786643 := bstep (se 1 (by rfl) ⟨1339982, by rfl⟩ : syracuseStep 1786643 = 2679965) B2679965
theorem B672943 : Blo 527800 672943 := bstep (se 1 (by rfl) ⟨504707, by rfl⟩ : syracuseStep 672943 = 1009415) B1009415
theorem B1787507 : Blo 527800 1787507 := bstep (se 1 (by rfl) ⟨1340630, by rfl⟩ : syracuseStep 1787507 = 2681261) B2681261
theorem B2672351 : Blo 527800 2672351 := bstep (se 1 (by rfl) ⟨2004263, by rfl⟩ : syracuseStep 2672351 = 4008527) B4008527
theorem B1787615 : Blo 527800 1787615 := bstep (se 1 (by rfl) ⟨1340711, by rfl⟩ : syracuseStep 1787615 = 2681423) B2681423
theorem B2672513 : Blo 527800 2672513 := bstep (se 2 (by rfl) ⟨1002192, by rfl⟩ : syracuseStep 2672513 = 2004385) B2004385
theorem B1787777 : Blo 527800 1787777 := bstep (se 2 (by rfl) ⟨670416, by rfl⟩ : syracuseStep 1787777 = 1340833) B1340833
theorem B7653305 : Blo 527800 7653305 := bstep (se 2 (by rfl) ⟨2869989, by rfl⟩ : syracuseStep 7653305 = 5739979) B5739979
theorem B1427807 : Blo 527800 1427807 := bstep (se 1 (by rfl) ⟨1070855, by rfl⟩ : syracuseStep 1427807 = 2141711) B2141711
theorem B1526111 : Blo 527800 1526111 := bstep (se 1 (by rfl) ⟨1144583, by rfl⟩ : syracuseStep 1526111 = 2289167) B2289167
theorem B6769007 : Blo 527800 6769007 := bstep (se 1 (by rfl) ⟨5076755, by rfl⟩ : syracuseStep 6769007 = 10153511) B10153511
theorem B1788317 : Blo 527800 1788317 := bstep (se 3 (by rfl) ⟨335309, by rfl⟩ : syracuseStep 1788317 = 670619) B670619
theorem B2673323 : Blo 527800 2673323 := bstep (se 1 (by rfl) ⟨2004992, by rfl⟩ : syracuseStep 2673323 = 4009985) B4009985
theorem B1788587 : Blo 527800 1788587 := bstep (se 1 (by rfl) ⟨1341440, by rfl⟩ : syracuseStep 1788587 = 2682881) B2682881
theorem B2017979 : Blo 527800 2017979 := bstep (se 1 (by rfl) ⟨1513484, by rfl⟩ : syracuseStep 2017979 = 3026969) B3026969
theorem B904171 : Blo 527800 904171 := bstep (se 1 (by rfl) ⟨678128, by rfl⟩ : syracuseStep 904171 = 1356257) B1356257
theorem B4017275 : Blo 527800 4017275 := bstep (se 1 (by rfl) ⟨3012956, by rfl⟩ : syracuseStep 4017275 = 6025913) B6025913
theorem B1789127 : Blo 527800 1789127 := bstep (se 1 (by rfl) ⟨1341845, by rfl⟩ : syracuseStep 1789127 = 2683691) B2683691
theorem B773723 : Blo 527800 773723 := bstep (se 1 (by rfl) ⟨580292, by rfl⟩ : syracuseStep 773723 = 1160585) B1160585
theorem B1691599 : Blo 527800 1691599 := bstep (se 1 (by rfl) ⟨1268699, by rfl⟩ : syracuseStep 1691599 = 2537399) B2537399
theorem B7721249 : Blo 527800 7721249 := bstep (se 2 (by rfl) ⟨2895468, by rfl⟩ : syracuseStep 7721249 = 5790937) B5790937
theorem B10309963 : Blo 527800 10309963 := bstep (se 1 (by rfl) ⟨7732472, by rfl⟩ : syracuseStep 10309963 = 15464945) B15464945
theorem B1134985 : Blo 527800 1134985 := bstep (se 2 (by rfl) ⟨425619, by rfl⟩ : syracuseStep 1134985 = 851239) B851239
theorem B1790423 : Blo 527800 1790423 := bstep (se 1 (by rfl) ⟨1342817, by rfl⟩ : syracuseStep 1790423 = 2685635) B2685635
theorem B905963 : Blo 527800 905963 := bstep (se 1 (by rfl) ⟨679472, by rfl⟩ : syracuseStep 905963 = 1358945) B1358945
theorem B3822329 : Blo 527800 3822329 := bstep (se 2 (by rfl) ⟨1433373, by rfl⟩ : syracuseStep 3822329 = 2866747) B2866747
theorem B1430401 : Blo 527800 1430401 := bstep (se 2 (by rfl) ⟨536400, by rfl⟩ : syracuseStep 1430401 = 1072801) B1072801
theorem B1070491 : Blo 527800 1070491 := bstep (se 1 (by rfl) ⟨802868, by rfl⟩ : syracuseStep 1070491 = 1605737) B1605737
theorem B53106353 : Blo 527800 53106353 := bstep (se 2 (by rfl) ⟨19914882, by rfl⟩ : syracuseStep 53106353 = 39829765) B39829765
theorem B1791881 : Blo 527800 1791881 := bstep (se 2 (by rfl) ⟨671955, by rfl⟩ : syracuseStep 1791881 = 1343911) B1343911
theorem B2545759 : Blo 527800 2545759 := bstep (se 1 (by rfl) ⟨1909319, by rfl⟩ : syracuseStep 2545759 = 3818639) B3818639
theorem B1792097 : Blo 527800 1792097 := bstep (se 2 (by rfl) ⟨672036, by rfl⟩ : syracuseStep 1792097 = 1344073) B1344073
theorem B1431785 : Blo 527800 1431785 := bstep (se 2 (by rfl) ⟨536919, by rfl⟩ : syracuseStep 1431785 = 1073839) B1073839
theorem B6773003 : Blo 527800 6773003 := bstep (se 1 (by rfl) ⟨5079752, by rfl⟩ : syracuseStep 6773003 = 10159505) B10159505
theorem B2709883 : Blo 527800 2709883 := bstep (se 1 (by rfl) ⟨2032412, by rfl⟩ : syracuseStep 2709883 = 4064825) B4064825
theorem B17160659 : Blo 527800 17160659 := bstep (se 1 (by rfl) ⟨12870494, by rfl⟩ : syracuseStep 17160659 = 25740989) B25740989
theorem B2677211 : Blo 527800 2677211 := bstep (se 1 (by rfl) ⟨2007908, by rfl⟩ : syracuseStep 2677211 = 4015817) B4015817
theorem B14474159 : Blo 527800 14474159 := bstep (se 1 (by rfl) ⟨10855619, by rfl⟩ : syracuseStep 14474159 = 21711239) B21711239
theorem B1793015 : Blo 527800 1793015 := bstep (se 1 (by rfl) ⟨1344761, by rfl⟩ : syracuseStep 1793015 = 2689523) B2689523
theorem B1793447 : Blo 527800 1793447 := bstep (se 1 (by rfl) ⟨1345085, by rfl⟩ : syracuseStep 1793447 = 2690171) B2690171
theorem B3431879 : Blo 527800 3431879 := bstep (se 1 (by rfl) ⟨2573909, by rfl⟩ : syracuseStep 3431879 = 5147819) B5147819
theorem B3006031 : Blo 527800 3006031 := bstep (se 1 (by rfl) ⟨2254523, by rfl⟩ : syracuseStep 3006031 = 4509047) B4509047
theorem B1793879 : Blo 527800 1793879 := bstep (se 1 (by rfl) ⟨1345409, by rfl⟩ : syracuseStep 1793879 = 2690819) B2690819
theorem B1007903 : Blo 527800 1007903 := bstep (se 1 (by rfl) ⟨755927, by rfl⟩ : syracuseStep 1007903 = 1511855) B1511855
theorem B1204577 : Blo 527800 1204577 := bstep (se 2 (by rfl) ⟨451716, by rfl⟩ : syracuseStep 1204577 = 903433) B903433
theorem B8577413 : Blo 527800 8577413 := bstep (se 4 (by rfl) ⟨804132, by rfl⟩ : syracuseStep 8577413 = 1608265) B1608265
theorem B6021539 : Blo 527800 6021539 := bstep (se 1 (by rfl) ⟨4516154, by rfl⟩ : syracuseStep 6021539 = 9032309) B9032309
theorem B2580923 : Blo 527800 2580923 := bstep (se 1 (by rfl) ⟨1935692, by rfl⟩ : syracuseStep 2580923 = 3871385) B3871385
theorem B1794689 : Blo 527800 1794689 := bstep (se 2 (by rfl) ⟨673008, by rfl⟩ : syracuseStep 1794689 = 1346017) B1346017
theorem B3008015 : Blo 527800 3008015 := bstep (se 1 (by rfl) ⟨2256011, by rfl⟩ : syracuseStep 3008015 = 4512023) B4512023
theorem B1435591 : Blo 527800 1435591 := bstep (se 1 (by rfl) ⟨1076693, by rfl⟩ : syracuseStep 1435591 = 2153387) B2153387
theorem B1337593 : Blo 527800 1337593 := bstep (se 2 (by rfl) ⟨501597, by rfl⟩ : syracuseStep 1337593 = 1003195) B1003195
theorem B5827247 : Blo 527800 5827247 := bstep (se 1 (by rfl) ⟨4370435, by rfl⟩ : syracuseStep 5827247 = 8740871) B8740871
theorem B3009473 : Blo 527800 3009473 := bstep (se 2 (by rfl) ⟨1128552, by rfl⟩ : syracuseStep 3009473 = 2257105) B2257105
theorem B14151667 : Blo 527800 14151667 := bstep (se 1 (by rfl) ⟨10613750, by rfl⟩ : syracuseStep 14151667 = 21227501) B21227501
theorem B1274167 : Blo 527800 1274167 := bstep (se 1 (by rfl) ⟨955625, by rfl⟩ : syracuseStep 1274167 = 1911251) B1911251
theorem B1340185 : Blo 527800 1340185 := bstep (se 2 (by rfl) ⟨502569, by rfl⟩ : syracuseStep 1340185 = 1005139) B1005139
theorem B1340489 : Blo 527800 1340489 := bstep (se 2 (by rfl) ⟨502683, by rfl⟩ : syracuseStep 1340489 = 1005367) B1005367
theorem B9762461 : Blo 527800 9762461 := bstep (se 3 (by rfl) ⟨1830461, by rfl⟩ : syracuseStep 9762461 = 3660923) B3660923
theorem B6616849 : Blo 527800 6616849 := bstep (se 2 (by rfl) ⟨2481318, by rfl⟩ : syracuseStep 6616849 = 4962637) B4962637
theorem B849695 : Blo 527800 849695 := bstep (se 1 (by rfl) ⟨637271, by rfl⟩ : syracuseStep 849695 = 1274543) B1274543
theorem B849727 : Blo 527800 849727 := bstep (se 1 (by rfl) ⟨637295, by rfl⟩ : syracuseStep 849727 = 1274591) B1274591
theorem B1701863 : Blo 527800 1701863 := bstep (se 1 (by rfl) ⟨1276397, by rfl⟩ : syracuseStep 1701863 = 2552795) B2552795
theorem B2684987 : Blo 527800 2684987 := bstep (se 1 (by rfl) ⟨2013740, by rfl⟩ : syracuseStep 2684987 = 4027481) B4027481
theorem B1505375 : Blo 527800 1505375 := bstep (se 1 (by rfl) ⟨1129031, by rfl⟩ : syracuseStep 1505375 = 2258063) B2258063
theorem B1636595 : Blo 527800 1636595 := bstep (se 1 (by rfl) ⟨1227446, by rfl⟩ : syracuseStep 1636595 = 2454893) B2454893
theorem B6388079 : Blo 527800 6388079 := bstep (se 1 (by rfl) ⟨4791059, by rfl⟩ : syracuseStep 6388079 = 9582119) B9582119
theorem B3013139 : Blo 527800 3013139 := bstep (se 1 (by rfl) ⟨2259854, by rfl⟩ : syracuseStep 3013139 = 4519709) B4519709
theorem B1342291 : Blo 527800 1342291 := bstep (se 1 (by rfl) ⟨1006718, by rfl⟩ : syracuseStep 1342291 = 2013437) B2013437
theorem B3406799 : Blo 527800 3406799 := bstep (se 1 (by rfl) ⟨2555099, by rfl⟩ : syracuseStep 3406799 = 5110199) B5110199
theorem B1342433 : Blo 527800 1342433 := bstep (se 2 (by rfl) ⟨503412, by rfl⟩ : syracuseStep 1342433 = 1006825) B1006825
theorem B1276897 : Blo 527800 1276897 := bstep (se 2 (by rfl) ⟨478836, by rfl⟩ : syracuseStep 1276897 = 957673) B957673
theorem B752761 : Blo 527800 752761 := bstep (se 2 (by rfl) ⟨282285, by rfl⟩ : syracuseStep 752761 = 564571) B564571
theorem B1506433 : Blo 527800 1506433 := bstep (se 2 (by rfl) ⟨564912, by rfl⟩ : syracuseStep 1506433 = 1129825) B1129825
theorem B2686445 : Blo 527800 2686445 := bstep (se 3 (by rfl) ⟨503708, by rfl⟩ : syracuseStep 2686445 = 1007417) B1007417
theorem B2686607 : Blo 527800 2686607 := bstep (se 1 (by rfl) ⟨2014955, by rfl⟩ : syracuseStep 2686607 = 4029911) B4029911
theorem B1507049 : Blo 527800 1507049 := bstep (se 2 (by rfl) ⟨565143, by rfl⟩ : syracuseStep 1507049 = 1130287) B1130287
theorem B12844889 : Blo 527800 12844889 := bstep (se 2 (by rfl) ⟨4816833, by rfl⟩ : syracuseStep 12844889 = 9633667) B9633667
theorem B4522169 : Blo 527800 4522169 := bstep (se 2 (by rfl) ⟨1695813, by rfl⟩ : syracuseStep 4522169 = 3391627) B3391627
theorem B2457983 : Blo 527800 2457983 := bstep (se 1 (by rfl) ⟨1843487, by rfl⟩ : syracuseStep 2457983 = 3686975) B3686975
theorem B4293047 : Blo 527800 4293047 := bstep (se 1 (by rfl) ⟨3219785, by rfl⟩ : syracuseStep 4293047 = 6439571) B6439571
theorem B2687741 : Blo 527800 2687741 := bstep (se 3 (by rfl) ⟨503951, by rfl⟩ : syracuseStep 2687741 = 1007903) B1007903
theorem B1017407 : Blo 527800 1017407 := bstep (se 1 (by rfl) ⟨763055, by rfl⟩ : syracuseStep 1017407 = 1526111) B1526111
theorem B1345319 : Blo 527800 1345319 := bstep (se 1 (by rfl) ⟨1008989, by rfl⟩ : syracuseStep 1345319 = 2017979) B2017979
theorem B10192877 : Blo 527800 10192877 := bstep (se 3 (by rfl) ⟨1911164, by rfl⟩ : syracuseStep 10192877 = 3822329) B3822329
theorem B4524083 : Blo 527800 4524083 := bstep (se 1 (by rfl) ⟨3393062, by rfl⟩ : syracuseStep 4524083 = 6786125) B6786125
theorem B5311115 : Blo 527800 5311115 := bstep (se 1 (by rfl) ⟨3983336, by rfl⟩ : syracuseStep 5311115 = 7966673) B7966673
theorem B4295713 : Blo 527800 4295713 := bstep (se 2 (by rfl) ⟨1610892, by rfl⟩ : syracuseStep 4295713 = 3221785) B3221785
theorem B1510751 : Blo 527800 1510751 := bstep (se 1 (by rfl) ⟨1133063, by rfl⟩ : syracuseStep 1510751 = 2266127) B2266127
theorem B527839 : Blo 527800 527839 := bstep (se 1 (by rfl) ⟨395879, by rfl⟩ : syracuseStep 527839 = 791759) B791759
theorem B527975 : Blo 527800 527975 := bstep (se 1 (by rfl) ⟨395981, by rfl⟩ : syracuseStep 527975 = 791963) B791963
theorem B528123 : Blo 527800 528123 := bstep (se 1 (by rfl) ⟨396092, by rfl⟩ : syracuseStep 528123 = 792185) B792185
theorem B528191 : Blo 527800 528191 := bstep (se 1 (by rfl) ⟨396143, by rfl⟩ : syracuseStep 528191 = 792287) B792287
theorem B528255 : Blo 527800 528255 := bstep (se 1 (by rfl) ⟨396191, by rfl⟩ : syracuseStep 528255 = 792383) B792383
theorem B528367 : Blo 527800 528367 := bstep (se 1 (by rfl) ⟨396275, by rfl⟩ : syracuseStep 528367 = 792551) B792551
theorem B528379 : Blo 527800 528379 := bstep (se 1 (by rfl) ⟨396284, by rfl⟩ : syracuseStep 528379 = 792569) B792569
theorem B528447 : Blo 527800 528447 := bstep (se 1 (by rfl) ⟨396335, by rfl⟩ : syracuseStep 528447 = 792671) B792671
theorem B528487 : Blo 527800 528487 := bstep (se 1 (by rfl) ⟨396365, by rfl⟩ : syracuseStep 528487 = 792731) B792731
theorem B528511 : Blo 527800 528511 := bstep (se 1 (by rfl) ⟨396383, by rfl⟩ : syracuseStep 528511 = 792767) B792767
theorem B3805319 : Blo 527800 3805319 := bstep (se 1 (by rfl) ⟨2853989, by rfl⟩ : syracuseStep 3805319 = 5707979) B5707979
theorem B528539 : Blo 527800 528539 := bstep (se 1 (by rfl) ⟨396404, by rfl⟩ : syracuseStep 528539 = 792809) B792809
theorem B954523 : Blo 527800 954523 := bstep (se 1 (by rfl) ⟨715892, by rfl⟩ : syracuseStep 954523 = 1431785) B1431785
theorem B11440439 : Blo 527800 11440439 := bstep (se 1 (by rfl) ⟨8580329, by rfl⟩ : syracuseStep 11440439 = 17160659) B17160659
theorem B528743 : Blo 527800 528743 := bstep (se 1 (by rfl) ⟨396557, by rfl⟩ : syracuseStep 528743 = 793115) B793115
theorem B528795 : Blo 527800 528795 := bstep (se 1 (by rfl) ⟨396596, by rfl⟩ : syracuseStep 528795 = 793193) B793193
theorem B529147 : Blo 527800 529147 := bstep (se 1 (by rfl) ⟨396860, by rfl⟩ : syracuseStep 529147 = 793721) B793721
theorem B2036477 : Blo 527800 2036477 := bstep (se 3 (by rfl) ⟨381839, by rfl⟩ : syracuseStep 2036477 = 763679) B763679
theorem B2265853 : Blo 527800 2265853 := bstep (se 3 (by rfl) ⟨424847, by rfl⟩ : syracuseStep 2265853 = 849695) B849695
theorem B9179929 : Blo 527800 9179929 := bstep (se 2 (by rfl) ⟨3442473, by rfl⟩ : syracuseStep 9179929 = 6884947) B6884947
theorem B594751 : Blo 527800 594751 := bstep (se 1 (by rfl) ⟨446063, by rfl⟩ : syracuseStep 594751 = 892127) B892127
theorem B529215 : Blo 527800 529215 := bstep (se 1 (by rfl) ⟨396911, by rfl⟩ : syracuseStep 529215 = 793823) B793823
theorem B529243 : Blo 527800 529243 := bstep (se 1 (by rfl) ⟨396932, by rfl⟩ : syracuseStep 529243 = 793865) B793865
theorem B529311 : Blo 527800 529311 := bstep (se 1 (by rfl) ⟨396983, by rfl⟩ : syracuseStep 529311 = 793967) B793967
theorem B3019679 : Blo 527800 3019679 := bstep (se 1 (by rfl) ⟨2264759, by rfl⟩ : syracuseStep 3019679 = 4529519) B4529519
theorem B529391 : Blo 527800 529391 := bstep (se 1 (by rfl) ⟨397043, by rfl⟩ : syracuseStep 529391 = 794087) B794087
theorem B529479 : Blo 527800 529479 := bstep (se 1 (by rfl) ⟨397109, by rfl⟩ : syracuseStep 529479 = 794219) B794219
theorem B595039 : Blo 527800 595039 := bstep (se 1 (by rfl) ⟨446279, by rfl⟩ : syracuseStep 595039 = 892559) B892559
theorem B529563 : Blo 527800 529563 := bstep (se 1 (by rfl) ⟨397172, by rfl⟩ : syracuseStep 529563 = 794345) B794345
theorem B529659 : Blo 527800 529659 := bstep (se 1 (by rfl) ⟨397244, by rfl⟩ : syracuseStep 529659 = 794489) B794489
theorem B791849 : Blo 527800 791849 := bstep (se 2 (by rfl) ⟨296943, by rfl⟩ : syracuseStep 791849 = 593887) B593887
theorem B529727 : Blo 527800 529727 := bstep (se 1 (by rfl) ⟨397295, by rfl⟩ : syracuseStep 529727 = 794591) B794591
theorem B529895 : Blo 527800 529895 := bstep (se 1 (by rfl) ⟨397421, by rfl⟩ : syracuseStep 529895 = 794843) B794843
theorem B792047 : Blo 527800 792047 := bstep (se 1 (by rfl) ⟨594035, by rfl⟩ : syracuseStep 792047 = 1188071) B1188071
theorem B529903 : Blo 527800 529903 := bstep (se 1 (by rfl) ⟨397427, by rfl⟩ : syracuseStep 529903 = 794855) B794855
theorem B530011 : Blo 527800 530011 := bstep (se 1 (by rfl) ⟨397508, by rfl⟩ : syracuseStep 530011 = 795017) B795017
theorem B530075 : Blo 527800 530075 := bstep (se 1 (by rfl) ⟨397556, by rfl⟩ : syracuseStep 530075 = 795113) B795113
theorem B530159 : Blo 527800 530159 := bstep (se 1 (by rfl) ⟨397619, by rfl⟩ : syracuseStep 530159 = 795239) B795239
theorem B530247 : Blo 527800 530247 := bstep (se 1 (by rfl) ⟨397685, by rfl⟩ : syracuseStep 530247 = 795371) B795371
theorem B530267 : Blo 527800 530267 := bstep (se 1 (by rfl) ⟨397700, by rfl⟩ : syracuseStep 530267 = 795401) B795401
theorem B1513313 : Blo 527800 1513313 := bstep (se 2 (by rfl) ⟨567492, by rfl⟩ : syracuseStep 1513313 = 1134985) B1134985
theorem B792443 : Blo 527800 792443 := bstep (se 1 (by rfl) ⟨594332, by rfl⟩ : syracuseStep 792443 = 1188665) B1188665
theorem B2725769 : Blo 527800 2725769 := bstep (se 2 (by rfl) ⟨1022163, by rfl⟩ : syracuseStep 2725769 = 2044327) B2044327
theorem B792479 : Blo 527800 792479 := bstep (se 1 (by rfl) ⟨594359, by rfl⟩ : syracuseStep 792479 = 1188719) B1188719
theorem B530335 : Blo 527800 530335 := bstep (se 1 (by rfl) ⟨397751, by rfl⟩ : syracuseStep 530335 = 795503) B795503
theorem B530503 : Blo 527800 530503 := bstep (se 1 (by rfl) ⟨397877, by rfl⟩ : syracuseStep 530503 = 795755) B795755
theorem B792713 : Blo 527800 792713 := bstep (se 2 (by rfl) ⟨297267, by rfl⟩ : syracuseStep 792713 = 594535) B594535
theorem B530663 : Blo 527800 530663 := bstep (se 1 (by rfl) ⟨397997, by rfl⟩ : syracuseStep 530663 = 795995) B795995
theorem B3807485 : Blo 527800 3807485 := bstep (se 3 (by rfl) ⟨713903, by rfl⟩ : syracuseStep 3807485 = 1427807) B1427807
theorem B792863 : Blo 527800 792863 := bstep (se 1 (by rfl) ⟨594647, by rfl⟩ : syracuseStep 792863 = 1189295) B1189295
theorem B2005343 : Blo 527800 2005343 := bstep (se 1 (by rfl) ⟨1504007, by rfl⟩ : syracuseStep 2005343 = 3008015) B3008015
theorem B530847 : Blo 527800 530847 := bstep (se 1 (by rfl) ⟨398135, by rfl⟩ : syracuseStep 530847 = 796271) B796271
theorem B530895 : Blo 527800 530895 := bstep (se 1 (by rfl) ⟨398171, by rfl⟩ : syracuseStep 530895 = 796343) B796343
theorem B530919 : Blo 527800 530919 := bstep (se 1 (by rfl) ⟨398189, by rfl⟩ : syracuseStep 530919 = 796379) B796379
theorem B1907201 : Blo 527800 1907201 := bstep (se 2 (by rfl) ⟨715200, by rfl⟩ : syracuseStep 1907201 = 1430401) B1430401
theorem B531035 : Blo 527800 531035 := bstep (se 1 (by rfl) ⟨398276, by rfl⟩ : syracuseStep 531035 = 796553) B796553
theorem B531103 : Blo 527800 531103 := bstep (se 1 (by rfl) ⟨398327, by rfl⟩ : syracuseStep 531103 = 796655) B796655
theorem B793415 : Blo 527800 793415 := bstep (se 1 (by rfl) ⟨595061, by rfl⟩ : syracuseStep 793415 = 1190123) B1190123
theorem B531271 : Blo 527800 531271 := bstep (se 1 (by rfl) ⟨398453, by rfl⟩ : syracuseStep 531271 = 796907) B796907
theorem B531311 : Blo 527800 531311 := bstep (se 1 (by rfl) ⟨398483, by rfl⟩ : syracuseStep 531311 = 796967) B796967
theorem B531367 : Blo 527800 531367 := bstep (se 1 (by rfl) ⟨398525, by rfl⟩ : syracuseStep 531367 = 797051) B797051
theorem B531547 : Blo 527800 531547 := bstep (se 1 (by rfl) ⟨398660, by rfl⟩ : syracuseStep 531547 = 797321) B797321
theorem B597199 : Blo 527800 597199 := bstep (se 1 (by rfl) ⟨447899, by rfl⟩ : syracuseStep 597199 = 895799) B895799
theorem B531663 : Blo 527800 531663 := bstep (se 1 (by rfl) ⟨398747, by rfl⟩ : syracuseStep 531663 = 797495) B797495
theorem B531687 : Blo 527800 531687 := bstep (se 1 (by rfl) ⟨398765, by rfl⟩ : syracuseStep 531687 = 797531) B797531
theorem B2006315 : Blo 527800 2006315 := bstep (se 1 (by rfl) ⟨1504736, by rfl⟩ : syracuseStep 2006315 = 3009473) B3009473
theorem B531783 : Blo 527800 531783 := bstep (se 1 (by rfl) ⟨398837, by rfl⟩ : syracuseStep 531783 = 797675) B797675
theorem B3022343 : Blo 527800 3022343 := bstep (se 1 (by rfl) ⟨2266757, by rfl⟩ : syracuseStep 3022343 = 4533515) B4533515
theorem B794279 : Blo 527800 794279 := bstep (se 1 (by rfl) ⟨595709, by rfl⟩ : syracuseStep 794279 = 1191419) B1191419
theorem B8822465 : Blo 527800 8822465 := bstep (se 2 (by rfl) ⟨3308424, by rfl⟩ : syracuseStep 8822465 = 6616849) B6616849
theorem B1187603 : Blo 527800 1187603 := bstep (se 1 (by rfl) ⟨890702, by rfl⟩ : syracuseStep 1187603 = 1781405) B1781405
theorem B794399 : Blo 527800 794399 := bstep (se 1 (by rfl) ⟨595799, by rfl⟩ : syracuseStep 794399 = 1191599) B1191599
theorem B9084797 : Blo 527800 9084797 := bstep (se 3 (by rfl) ⟨1703399, by rfl⟩ : syracuseStep 9084797 = 3406799) B3406799
theorem B1187963 : Blo 527800 1187963 := bstep (se 1 (by rfl) ⟨890972, by rfl⟩ : syracuseStep 1187963 = 1781945) B1781945
theorem B598207 : Blo 527800 598207 := bstep (se 1 (by rfl) ⟨448655, by rfl⟩ : syracuseStep 598207 = 897311) B897311
theorem B794831 : Blo 527800 794831 := bstep (se 1 (by rfl) ⟨596123, by rfl⟩ : syracuseStep 794831 = 1192247) B1192247
theorem B794879 : Blo 527800 794879 := bstep (se 1 (by rfl) ⟨596159, by rfl⟩ : syracuseStep 794879 = 1192319) B1192319
theorem B1188233 : Blo 527800 1188233 := bstep (se 2 (by rfl) ⟨445587, by rfl⟩ : syracuseStep 1188233 = 891175) B891175
theorem B3613177 : Blo 527800 3613177 := bstep (se 2 (by rfl) ⟨1354941, by rfl⟩ : syracuseStep 3613177 = 2709883) B2709883
theorem B3809875 : Blo 527800 3809875 := bstep (se 1 (by rfl) ⟨2857406, by rfl⟩ : syracuseStep 3809875 = 5714813) B5714813
theorem B893659 : Blo 527800 893659 := bstep (se 1 (by rfl) ⟨670244, by rfl⟩ : syracuseStep 893659 = 1340489) B1340489
theorem B795695 : Blo 527800 795695 := bstep (se 1 (by rfl) ⟨596771, by rfl⟩ : syracuseStep 795695 = 1193543) B1193543
theorem B795815 : Blo 527800 795815 := bstep (se 1 (by rfl) ⟨596861, by rfl⟩ : syracuseStep 795815 = 1193723) B1193723
theorem B1189367 : Blo 527800 1189367 := bstep (se 1 (by rfl) ⟨892025, by rfl⟩ : syracuseStep 1189367 = 1784051) B1784051
theorem B1091063 : Blo 527800 1091063 := bstep (se 1 (by rfl) ⟨818297, by rfl⟩ : syracuseStep 1091063 = 1636595) B1636595
theorem B2008577 : Blo 527800 2008577 := bstep (se 2 (by rfl) ⟨753216, by rfl⟩ : syracuseStep 2008577 = 1506433) B1506433
theorem B1189403 : Blo 527800 1189403 := bstep (se 1 (by rfl) ⟨892052, by rfl⟩ : syracuseStep 1189403 = 1784105) B1784105
theorem B796187 : Blo 527800 796187 := bstep (se 1 (by rfl) ⟨597140, by rfl⟩ : syracuseStep 796187 = 1194281) B1194281
theorem B2008759 : Blo 527800 2008759 := bstep (se 1 (by rfl) ⟨1506569, by rfl⟩ : syracuseStep 2008759 = 3013139) B3013139
theorem B796571 : Blo 527800 796571 := bstep (se 1 (by rfl) ⟨597428, by rfl⟩ : syracuseStep 796571 = 1194857) B1194857
theorem B796607 : Blo 527800 796607 := bstep (se 1 (by rfl) ⟨597455, by rfl⟩ : syracuseStep 796607 = 1194911) B1194911
theorem B894955 : Blo 527800 894955 := bstep (se 1 (by rfl) ⟨671216, by rfl⟩ : syracuseStep 894955 = 1342433) B1342433
theorem B4008041 : Blo 527800 4008041 := bstep (se 2 (by rfl) ⟨1503015, by rfl⟩ : syracuseStep 4008041 = 3006031) B3006031
theorem B895097 : Blo 527800 895097 := bstep (se 2 (by rfl) ⟨335661, by rfl⟩ : syracuseStep 895097 = 671323) B671323
theorem B796793 : Blo 527800 796793 := bstep (se 2 (by rfl) ⟨298797, by rfl⟩ : syracuseStep 796793 = 597595) B597595
theorem B1190393 : Blo 527800 1190393 := bstep (se 2 (by rfl) ⟨446397, by rfl⟩ : syracuseStep 1190393 = 892795) B892795
theorem B797177 : Blo 527800 797177 := bstep (se 2 (by rfl) ⟨298941, by rfl⟩ : syracuseStep 797177 = 597883) B597883
theorem B1190447 : Blo 527800 1190447 := bstep (se 1 (by rfl) ⟨892835, by rfl⟩ : syracuseStep 1190447 = 1785671) B1785671
theorem B797231 : Blo 527800 797231 := bstep (se 1 (by rfl) ⟨597923, by rfl⟩ : syracuseStep 797231 = 1195847) B1195847
theorem B1813049 : Blo 527800 1813049 := bstep (se 2 (by rfl) ⟨679893, by rfl⟩ : syracuseStep 1813049 = 1359787) B1359787
theorem B8563259 : Blo 527800 8563259 := bstep (se 1 (by rfl) ⟨6422444, by rfl⟩ : syracuseStep 8563259 = 12844889) B12844889
theorem B1190483 : Blo 527800 1190483 := bstep (se 1 (by rfl) ⟨892862, by rfl⟩ : syracuseStep 1190483 = 1785725) B1785725
theorem B1190663 : Blo 527800 1190663 := bstep (se 1 (by rfl) ⟨892997, by rfl⟩ : syracuseStep 1190663 = 1785995) B1785995
theorem B1190879 : Blo 527800 1190879 := bstep (se 1 (by rfl) ⟨893159, by rfl⟩ : syracuseStep 1190879 = 1786319) B1786319
theorem B797663 : Blo 527800 797663 := bstep (se 1 (by rfl) ⟨598247, by rfl⟩ : syracuseStep 797663 = 1196495) B1196495
theorem B1191095 : Blo 527800 1191095 := bstep (se 1 (by rfl) ⟨893321, by rfl⟩ : syracuseStep 1191095 = 1786643) B1786643
theorem B1355063 : Blo 527800 1355063 := bstep (se 1 (by rfl) ⟨1016297, by rfl⟩ : syracuseStep 1355063 = 2032595) B2032595
theorem B2010491 : Blo 527800 2010491 := bstep (se 1 (by rfl) ⟨1507868, by rfl⟩ : syracuseStep 2010491 = 3015737) B3015737
theorem B20589997 : Blo 527800 20589997 := bstep (se 3 (by rfl) ⟨3860624, by rfl⟩ : syracuseStep 20589997 = 7721249) B7721249
theorem B1191671 : Blo 527800 1191671 := bstep (se 1 (by rfl) ⟨893753, by rfl⟩ : syracuseStep 1191671 = 1787507) B1787507
theorem B1781567 : Blo 527800 1781567 := bstep (se 1 (by rfl) ⟨1336175, by rfl⟩ : syracuseStep 1781567 = 2672351) B2672351
theorem B1191743 : Blo 527800 1191743 := bstep (se 1 (by rfl) ⟨893807, by rfl⟩ : syracuseStep 1191743 = 1787615) B1787615
theorem B1781675 : Blo 527800 1781675 := bstep (se 1 (by rfl) ⟨1336256, by rfl⟩ : syracuseStep 1781675 = 2672513) B2672513
theorem B1191851 : Blo 527800 1191851 := bstep (se 1 (by rfl) ⟨893888, by rfl⟩ : syracuseStep 1191851 = 1787777) B1787777
theorem B897257 : Blo 527800 897257 := bstep (se 2 (by rfl) ⟨336471, by rfl⟩ : syracuseStep 897257 = 672943) B672943
theorem B1192211 : Blo 527800 1192211 := bstep (se 1 (by rfl) ⟨894158, by rfl⟩ : syracuseStep 1192211 = 1788317) B1788317
theorem B1782215 : Blo 527800 1782215 := bstep (se 1 (by rfl) ⟨1336661, by rfl⟩ : syracuseStep 1782215 = 2673323) B2673323
theorem B1192391 : Blo 527800 1192391 := bstep (se 1 (by rfl) ⟨894293, by rfl⟩ : syracuseStep 1192391 = 1788587) B1788587
theorem B1192751 : Blo 527800 1192751 := bstep (se 1 (by rfl) ⟨894563, by rfl⟩ : syracuseStep 1192751 = 1789127) B1789127
theorem B1192841 : Blo 527800 1192841 := bstep (se 2 (by rfl) ⟨447315, by rfl⟩ : syracuseStep 1192841 = 894631) B894631
theorem B1914121 : Blo 527800 1914121 := bstep (se 2 (by rfl) ⟨717795, by rfl⟩ : syracuseStep 1914121 = 1435591) B1435591
theorem B1193615 : Blo 527800 1193615 := bstep (se 1 (by rfl) ⟨895211, by rfl⟩ : syracuseStep 1193615 = 1790423) B1790423
theorem B1783457 : Blo 527800 1783457 := bstep (se 2 (by rfl) ⟨668796, by rfl⟩ : syracuseStep 1783457 = 1337593) B1337593
theorem B1193705 : Blo 527800 1193705 := bstep (se 2 (by rfl) ⟨447639, by rfl⟩ : syracuseStep 1193705 = 895279) B895279
theorem B4306871 : Blo 527800 4306871 := bstep (se 1 (by rfl) ⟨3230153, by rfl⟩ : syracuseStep 4306871 = 6460307) B6460307
theorem B35404235 : Blo 527800 35404235 := bstep (se 1 (by rfl) ⟨26553176, by rfl⟩ : syracuseStep 35404235 = 53106353) B53106353
theorem B637391 : Blo 527800 637391 := bstep (se 1 (by rfl) ⟨478043, by rfl⟩ : syracuseStep 637391 = 956087) B956087
theorem B1194587 : Blo 527800 1194587 := bstep (se 1 (by rfl) ⟨895940, by rfl⟩ : syracuseStep 1194587 = 1791881) B1791881
theorem B1194731 : Blo 527800 1194731 := bstep (se 1 (by rfl) ⟨896048, by rfl⟩ : syracuseStep 1194731 = 1792097) B1792097
theorem B1784807 : Blo 527800 1784807 := bstep (se 1 (by rfl) ⟨1338605, by rfl⟩ : syracuseStep 1784807 = 2677211) B2677211
theorem B9649439 : Blo 527800 9649439 := bstep (se 1 (by rfl) ⟨7237079, by rfl⟩ : syracuseStep 9649439 = 14474159) B14474159
theorem B1195343 : Blo 527800 1195343 := bstep (se 1 (by rfl) ⟨896507, by rfl⟩ : syracuseStep 1195343 = 1793015) B1793015
theorem B1195433 : Blo 527800 1195433 := bstep (se 2 (by rfl) ⟨448287, by rfl⟩ : syracuseStep 1195433 = 896575) B896575
theorem B1195631 : Blo 527800 1195631 := bstep (se 1 (by rfl) ⟨896723, by rfl⟩ : syracuseStep 1195631 = 1793447) B1793447
theorem B1359737 : Blo 527800 1359737 := bstep (se 2 (by rfl) ⟨509901, by rfl⟩ : syracuseStep 1359737 = 1019803) B1019803
theorem B1195919 : Blo 527800 1195919 := bstep (se 1 (by rfl) ⟨896939, by rfl⟩ : syracuseStep 1195919 = 1793879) B1793879
theorem B803051 : Blo 527800 803051 := bstep (se 1 (by rfl) ⟨602288, by rfl⟩ : syracuseStep 803051 = 1204577) B1204577
theorem B5718275 : Blo 527800 5718275 := bstep (se 1 (by rfl) ⟨4288706, by rfl⟩ : syracuseStep 5718275 = 8577413) B8577413
theorem B4014359 : Blo 527800 4014359 := bstep (se 1 (by rfl) ⟨3010769, by rfl⟩ : syracuseStep 4014359 = 6021539) B6021539
theorem B1720615 : Blo 527800 1720615 := bstep (se 1 (by rfl) ⟨1290461, by rfl⟩ : syracuseStep 1720615 = 2580923) B2580923
theorem B1196459 : Blo 527800 1196459 := bstep (se 1 (by rfl) ⟨897344, by rfl⟩ : syracuseStep 1196459 = 1794689) B1794689
theorem B13746617 : Blo 527800 13746617 := bstep (se 2 (by rfl) ⟨5154981, by rfl⟩ : syracuseStep 13746617 = 10309963) B10309963
theorem B1786913 : Blo 527800 1786913 := bstep (se 2 (by rfl) ⟨670092, by rfl⟩ : syracuseStep 1786913 = 1340185) B1340185
theorem B3884831 : Blo 527800 3884831 := bstep (se 1 (by rfl) ⟨2913623, by rfl⟩ : syracuseStep 3884831 = 5827247) B5827247
theorem B1427321 : Blo 527800 1427321 := bstep (se 2 (by rfl) ⟨535245, by rfl⟩ : syracuseStep 1427321 = 1070491) B1070491
theorem B1132969 : Blo 527800 1132969 := bstep (se 2 (by rfl) ⟨424863, by rfl⟩ : syracuseStep 1132969 = 849727) B849727
theorem B3394345 : Blo 527800 3394345 := bstep (se 2 (by rfl) ⟨1272879, by rfl⟩ : syracuseStep 3394345 = 2545759) B2545759
theorem B2149249 : Blo 527800 2149249 := bstep (se 2 (by rfl) ⟨805968, by rfl⟩ : syracuseStep 2149249 = 1611937) B1611937
theorem B2018267 : Blo 527800 2018267 := bstep (se 1 (by rfl) ⟨1513700, by rfl⟩ : syracuseStep 2018267 = 3027401) B3027401
theorem B3394703 : Blo 527800 3394703 := bstep (se 1 (by rfl) ⟨2546027, by rfl⟩ : syracuseStep 3394703 = 5092055) B5092055
theorem B2018479 : Blo 527800 2018479 := bstep (se 1 (by rfl) ⟨1513859, by rfl⟩ : syracuseStep 2018479 = 3027719) B3027719
theorem B1789181 : Blo 527800 1789181 := bstep (se 3 (by rfl) ⟨335471, by rfl⟩ : syracuseStep 1789181 = 670943) B670943
theorem B6508307 : Blo 527800 6508307 := bstep (se 1 (by rfl) ⟨4881230, by rfl⟩ : syracuseStep 6508307 = 9762461) B9762461
theorem B2674457 : Blo 527800 2674457 := bstep (se 2 (by rfl) ⟨1002921, by rfl⟩ : syracuseStep 2674457 = 2005843) B2005843
theorem B1789721 : Blo 527800 1789721 := bstep (se 2 (by rfl) ⟨671145, by rfl⟩ : syracuseStep 1789721 = 1342291) B1342291
theorem B1134575 : Blo 527800 1134575 := bstep (se 1 (by rfl) ⟨850931, by rfl⟩ : syracuseStep 1134575 = 1701863) B1701863
theorem B1789991 : Blo 527800 1789991 := bstep (se 1 (by rfl) ⟨1342493, by rfl⟩ : syracuseStep 1789991 = 2684987) B2684987
theorem B1003583 : Blo 527800 1003583 := bstep (se 1 (by rfl) ⟨752687, by rfl⟩ : syracuseStep 1003583 = 1505375) B1505375
theorem B1003681 : Blo 527800 1003681 := bstep (se 2 (by rfl) ⟨376380, by rfl⟩ : syracuseStep 1003681 = 752761) B752761
theorem B1691867 : Blo 527800 1691867 := bstep (se 1 (by rfl) ⟨1268900, by rfl⟩ : syracuseStep 1691867 = 2537801) B2537801
theorem B1429883 : Blo 527800 1429883 := bstep (se 1 (by rfl) ⟨1072412, by rfl⟩ : syracuseStep 1429883 = 2144825) B2144825
theorem B906223 : Blo 527800 906223 := bstep (se 1 (by rfl) ⟨679667, by rfl⟩ : syracuseStep 906223 = 1359335) B1359335
theorem B1790963 : Blo 527800 1790963 := bstep (se 1 (by rfl) ⟨1343222, by rfl⟩ : syracuseStep 1790963 = 2686445) B2686445
theorem B1791071 : Blo 527800 1791071 := bstep (se 1 (by rfl) ⟨1343303, by rfl⟩ : syracuseStep 1791071 = 2686607) B2686607
theorem B1496159 : Blo 527800 1496159 := bstep (se 1 (by rfl) ⟨1122119, by rfl⟩ : syracuseStep 1496159 = 2244239) B2244239
theorem B1004699 : Blo 527800 1004699 := bstep (se 1 (by rfl) ⟨753524, by rfl⟩ : syracuseStep 1004699 = 1507049) B1507049
theorem B1791503 : Blo 527800 1791503 := bstep (se 1 (by rfl) ⟨1343627, by rfl⟩ : syracuseStep 1791503 = 2687255) B2687255
theorem B1005223 : Blo 527800 1005223 := bstep (se 1 (by rfl) ⟨753917, by rfl⟩ : syracuseStep 1005223 = 1507835) B1507835
theorem B1792313 : Blo 527800 1792313 := bstep (se 2 (by rfl) ⟨672117, by rfl⟩ : syracuseStep 1792313 = 1344235) B1344235
theorem B6052157 : Blo 527800 6052157 := bstep (se 3 (by rfl) ⟨1134779, by rfl⟩ : syracuseStep 6052157 = 2269559) B2269559
theorem B130734485 : Blo 527800 130734485 := bstep (se 6 (by rfl) ⟨3064089, by rfl⟩ : syracuseStep 130734485 = 6128179) B6128179
theorem B1792583 : Blo 527800 1792583 := bstep (se 1 (by rfl) ⟨1344437, by rfl⟩ : syracuseStep 1792583 = 2688875) B2688875
theorem B5102203 : Blo 527800 5102203 := bstep (se 1 (by rfl) ⟨3826652, by rfl⟩ : syracuseStep 5102203 = 7653305) B7653305
theorem B4512671 : Blo 527800 4512671 := bstep (se 1 (by rfl) ⟨3384503, by rfl⟩ : syracuseStep 4512671 = 6769007) B6769007
theorem B4021163 : Blo 527800 4021163 := bstep (se 1 (by rfl) ⟨3015872, by rfl⟩ : syracuseStep 4021163 = 6031745) B6031745
theorem B2415901 : Blo 527800 2415901 := bstep (se 3 (by rfl) ⟨452981, by rfl⟩ : syracuseStep 2415901 = 905963) B905963
theorem B3824927 : Blo 527800 3824927 := bstep (se 1 (by rfl) ⟨2868695, by rfl⟩ : syracuseStep 3824927 = 5737391) B5737391
theorem B2678183 : Blo 527800 2678183 := bstep (se 1 (by rfl) ⟨2008637, by rfl⟩ : syracuseStep 2678183 = 4017275) B4017275
theorem B1531559 : Blo 527800 1531559 := bstep (se 1 (by rfl) ⟨1148669, by rfl⟩ : syracuseStep 1531559 = 2297339) B2297339
theorem B1007471 : Blo 527800 1007471 := bstep (se 1 (by rfl) ⟨755603, by rfl⟩ : syracuseStep 1007471 = 1511207) B1511207
theorem B3825731 : Blo 527800 3825731 := bstep (se 1 (by rfl) ⟨2869298, by rfl⟩ : syracuseStep 3825731 = 5738597) B5738597
theorem B4285655 : Blo 527800 4285655 := bstep (se 1 (by rfl) ⟨3214241, by rfl⟩ : syracuseStep 4285655 = 6428483) B6428483
theorem B1205561 : Blo 527800 1205561 := bstep (se 2 (by rfl) ⟨452085, by rfl⟩ : syracuseStep 1205561 = 904171) B904171
theorem B16541101 : Blo 527800 16541101 := bstep (se 3 (by rfl) ⟨3101456, by rfl⟩ : syracuseStep 16541101 = 6202913) B6202913
theorem B4515335 : Blo 527800 4515335 := bstep (se 1 (by rfl) ⟨3386501, by rfl⟩ : syracuseStep 4515335 = 6773003) B6773003
theorem B1337107 : Blo 527800 1337107 := bstep (se 1 (by rfl) ⟨1002830, by rfl⟩ : syracuseStep 1337107 = 2005661) B2005661
theorem B1206035 : Blo 527800 1206035 := bstep (se 1 (by rfl) ⟨904526, by rfl⟩ : syracuseStep 1206035 = 1809053) B1809053
theorem B2287919 : Blo 527800 2287919 := bstep (se 1 (by rfl) ⟨1715939, by rfl⟩ : syracuseStep 2287919 = 3431879) B3431879
theorem B2255465 : Blo 527800 2255465 := bstep (se 2 (by rfl) ⟨845799, by rfl⟩ : syracuseStep 2255465 = 1691599) B1691599
theorem B18868889 : Blo 527800 18868889 := bstep (se 2 (by rfl) ⟨7075833, by rfl⟩ : syracuseStep 18868889 = 14151667) B14151667
theorem B1698889 : Blo 527800 1698889 := bstep (se 2 (by rfl) ⟨637083, by rfl⟩ : syracuseStep 1698889 = 1274167) B1274167
theorem B17034877 : Blo 527800 17034877 := bstep (se 3 (by rfl) ⟨3194039, by rfl⟩ : syracuseStep 17034877 = 6388079) B6388079
theorem B1797857 : Blo 527800 1797857 := bstep (se 2 (by rfl) ⟨674196, by rfl⟩ : syracuseStep 1797857 = 1348393) B1348393
theorem B1339355 : Blo 527800 1339355 := bstep (se 1 (by rfl) ⟨1004516, by rfl⟩ : syracuseStep 1339355 = 2009033) B2009033
theorem B12415169 : Blo 527800 12415169 := bstep (se 2 (by rfl) ⟨4655688, by rfl⟩ : syracuseStep 12415169 = 9311377) B9311377
theorem B4092287 : Blo 527800 4092287 := bstep (se 1 (by rfl) ⟨3069215, by rfl⟩ : syracuseStep 4092287 = 6138431) B6138431
theorem B6452027 : Blo 527800 6452027 := bstep (se 1 (by rfl) ⟨4839020, by rfl⟩ : syracuseStep 6452027 = 9678041) B9678041
theorem B8615159 : Blo 527800 8615159 := bstep (se 1 (by rfl) ⟨6461369, by rfl⟩ : syracuseStep 8615159 = 12922739) B12922739
theorem B2258387 : Blo 527800 2258387 := bstep (se 1 (by rfl) ⟨1693790, by rfl⟩ : syracuseStep 2258387 = 3387581) B3387581
theorem B18904709 : Blo 527800 18904709 := bstep (se 4 (by rfl) ⟨1772316, by rfl⟩ : syracuseStep 18904709 = 3544633) B3544633
theorem B10319633 : Blo 527800 10319633 := bstep (se 2 (by rfl) ⟨3869862, by rfl⟩ : syracuseStep 10319633 = 7739725) B7739725
theorem B1341623 : Blo 527800 1341623 := bstep (se 1 (by rfl) ⟨1006217, by rfl⟩ : syracuseStep 1341623 = 2012435) B2012435
theorem B3832019 : Blo 527800 3832019 := bstep (se 1 (by rfl) ⟨2874014, by rfl⟩ : syracuseStep 3832019 = 5748029) B5748029
theorem B2554409 : Blo 527800 2554409 := bstep (se 2 (by rfl) ⟨957903, by rfl⟩ : syracuseStep 2554409 = 1915807) B1915807
theorem B2292353 : Blo 527800 2292353 := bstep (se 2 (by rfl) ⟨859632, by rfl⟩ : syracuseStep 2292353 = 1719265) B1719265
theorem B1702529 : Blo 527800 1702529 := bstep (se 2 (by rfl) ⟨638448, by rfl⟩ : syracuseStep 1702529 = 1276897) B1276897
theorem B752431 : Blo 527800 752431 := bstep (se 1 (by rfl) ⟨564323, by rfl⟩ : syracuseStep 752431 = 1128647) B1128647
theorem B2063261 : Blo 527800 2063261 := bstep (se 3 (by rfl) ⟨386861, by rfl⟩ : syracuseStep 2063261 = 773723) B773723
theorem B1506205 : Blo 527800 1506205 := bstep (se 3 (by rfl) ⟨282413, by rfl⟩ : syracuseStep 1506205 = 564827) B564827
theorem B6782129 : Blo 527800 6782129 := bstep (se 2 (by rfl) ⟨2543298, by rfl⟩ : syracuseStep 6782129 = 5086597) B5086597
theorem B1343375 : Blo 527800 1343375 := bstep (se 1 (by rfl) ⟨1007531, by rfl⟩ : syracuseStep 1343375 = 2015063) B2015063
theorem B3014779 : Blo 527800 3014779 := bstep (se 1 (by rfl) ⟨2261084, by rfl⟩ : syracuseStep 3014779 = 4522169) B4522169
theorem B2294153 : Blo 527800 2294153 := bstep (se 2 (by rfl) ⟨860307, by rfl⟩ : syracuseStep 2294153 = 1720615) B1720615
theorem B4817569 : Blo 527800 4817569 := bstep (se 2 (by rfl) ⟨1806588, by rfl⟩ : syracuseStep 4817569 = 3613177) B3613177
theorem B5079833 : Blo 527800 5079833 := bstep (se 2 (by rfl) ⟨1904937, by rfl⟩ : syracuseStep 5079833 = 3809875) B3809875
theorem B6554621 : Blo 527800 6554621 := bstep (se 3 (by rfl) ⟨1228991, by rfl⟩ : syracuseStep 6554621 = 2457983) B2457983
theorem B10912765 : Blo 527800 10912765 := bstep (se 3 (by rfl) ⟨2046143, by rfl⟩ : syracuseStep 10912765 = 4092287) B4092287
theorem B2589887 : Blo 527800 2589887 := bstep (se 1 (by rfl) ⟨1942415, by rfl⟩ : syracuseStep 2589887 = 3884831) B3884831
theorem B951547 : Blo 527800 951547 := bstep (se 1 (by rfl) ⟨713660, by rfl⟩ : syracuseStep 951547 = 1427321) B1427321
theorem B3016055 : Blo 527800 3016055 := bstep (se 1 (by rfl) ⟨2262041, by rfl⟩ : syracuseStep 3016055 = 4524083) B4524083
theorem B3540743 : Blo 527800 3540743 := bstep (se 1 (by rfl) ⟨2655557, by rfl⟩ : syracuseStep 3540743 = 5311115) B5311115
theorem B1345511 : Blo 527800 1345511 := bstep (se 1 (by rfl) ⟨1009133, by rfl⟩ : syracuseStep 1345511 = 2018267) B2018267
theorem B2263135 : Blo 527800 2263135 := bstep (se 1 (by rfl) ⟨1697351, by rfl⟩ : syracuseStep 2263135 = 3394703) B3394703
theorem B756383 : Blo 527800 756383 := bstep (se 1 (by rfl) ⟨567287, by rfl⟩ : syracuseStep 756383 = 1134575) B1134575
theorem B953255 : Blo 527800 953255 := bstep (se 1 (by rfl) ⟨714941, by rfl⟩ : syracuseStep 953255 = 1429883) B1429883
theorem B1510625 : Blo 527800 1510625 := bstep (se 2 (by rfl) ⟨566484, by rfl⟩ : syracuseStep 1510625 = 1132969) B1132969
theorem B3214829 : Blo 527800 3214829 := bstep (se 3 (by rfl) ⟨602780, by rfl⟩ : syracuseStep 3214829 = 1205561) B1205561
theorem B527899 : Blo 527800 527899 := bstep (se 1 (by rfl) ⟨395924, by rfl⟩ : syracuseStep 527899 = 791849) B791849
theorem B528031 : Blo 527800 528031 := bstep (se 1 (by rfl) ⟨396023, by rfl⟩ : syracuseStep 528031 = 792047) B792047
theorem B4525793 : Blo 527800 4525793 := bstep (se 2 (by rfl) ⟨1697172, by rfl⟩ : syracuseStep 4525793 = 3394345) B3394345
theorem B528295 : Blo 527800 528295 := bstep (se 1 (by rfl) ⟨396221, by rfl⟩ : syracuseStep 528295 = 792443) B792443
theorem B528319 : Blo 527800 528319 := bstep (se 1 (by rfl) ⟨396239, by rfl⟩ : syracuseStep 528319 = 792479) B792479
theorem B528475 : Blo 527800 528475 := bstep (se 1 (by rfl) ⟨396356, by rfl⟩ : syracuseStep 528475 = 792713) B792713
theorem B2265185 : Blo 527800 2265185 := bstep (se 2 (by rfl) ⟨849444, by rfl⟩ : syracuseStep 2265185 = 1698889) B1698889
theorem B528575 : Blo 527800 528575 := bstep (se 1 (by rfl) ⟨396431, by rfl⟩ : syracuseStep 528575 = 792863) B792863
theorem B4034771 : Blo 527800 4034771 := bstep (se 1 (by rfl) ⟨3026078, by rfl⟩ : syracuseStep 4034771 = 6052157) B6052157
theorem B2691305 : Blo 527800 2691305 := bstep (se 2 (by rfl) ⟨1009239, by rfl⟩ : syracuseStep 2691305 = 2018479) B2018479
theorem B528943 : Blo 527800 528943 := bstep (se 1 (by rfl) ⟨396707, by rfl⟩ : syracuseStep 528943 = 793415) B793415
theorem B22713169 : Blo 527800 22713169 := bstep (se 2 (by rfl) ⟨8517438, by rfl⟩ : syracuseStep 22713169 = 17034877) B17034877
theorem B529519 : Blo 527800 529519 := bstep (se 1 (by rfl) ⟨397139, by rfl⟩ : syracuseStep 529519 = 794279) B794279
theorem B791735 : Blo 527800 791735 := bstep (se 1 (by rfl) ⟨593801, by rfl⟩ : syracuseStep 791735 = 1187603) B1187603
theorem B529599 : Blo 527800 529599 := bstep (se 1 (by rfl) ⟨397199, by rfl⟩ : syracuseStep 529599 = 794399) B794399
theorem B791975 : Blo 527800 791975 := bstep (se 1 (by rfl) ⟨593981, by rfl⟩ : syracuseStep 791975 = 1187963) B1187963
theorem B529887 : Blo 527800 529887 := bstep (se 1 (by rfl) ⟨397415, by rfl⟩ : syracuseStep 529887 = 794831) B794831
theorem B529919 : Blo 527800 529919 := bstep (se 1 (by rfl) ⟨397439, by rfl⟩ : syracuseStep 529919 = 794879) B794879
theorem B792155 : Blo 527800 792155 := bstep (se 1 (by rfl) ⟨594116, by rfl⟩ : syracuseStep 792155 = 1188233) B1188233
theorem B530463 : Blo 527800 530463 := bstep (se 1 (by rfl) ⟨397847, by rfl⟩ : syracuseStep 530463 = 795695) B795695
theorem B530543 : Blo 527800 530543 := bstep (se 1 (by rfl) ⟨397907, by rfl⟩ : syracuseStep 530543 = 795815) B795815
theorem B2857103 : Blo 527800 2857103 := bstep (se 1 (by rfl) ⟨2142827, by rfl⟩ : syracuseStep 2857103 = 4285655) B4285655
theorem B727375 : Blo 527800 727375 := bstep (se 1 (by rfl) ⟨545531, by rfl⟩ : syracuseStep 727375 = 1091063) B1091063
theorem B792911 : Blo 527800 792911 := bstep (se 1 (by rfl) ⟨594683, by rfl⟩ : syracuseStep 792911 = 1189367) B1189367
theorem B3021137 : Blo 527800 3021137 := bstep (se 2 (by rfl) ⟨1132926, by rfl⟩ : syracuseStep 3021137 = 2265853) B2265853
theorem B792935 : Blo 527800 792935 := bstep (se 1 (by rfl) ⟨594701, by rfl⟩ : syracuseStep 792935 = 1189403) B1189403
theorem B530791 : Blo 527800 530791 := bstep (se 1 (by rfl) ⟨398093, by rfl⟩ : syracuseStep 530791 = 796187) B796187
theorem B793001 : Blo 527800 793001 := bstep (se 2 (by rfl) ⟨297375, by rfl⟩ : syracuseStep 793001 = 594751) B594751
theorem B531047 : Blo 527800 531047 := bstep (se 1 (by rfl) ⟨398285, by rfl⟩ : syracuseStep 531047 = 796571) B796571
theorem B531071 : Blo 527800 531071 := bstep (se 1 (by rfl) ⟨398303, by rfl⟩ : syracuseStep 531071 = 796607) B796607
theorem B596731 : Blo 527800 596731 := bstep (se 1 (by rfl) ⟨447548, by rfl⟩ : syracuseStep 596731 = 895097) B895097
theorem B531195 : Blo 527800 531195 := bstep (se 1 (by rfl) ⟨398396, by rfl⟩ : syracuseStep 531195 = 796793) B796793
theorem B793385 : Blo 527800 793385 := bstep (se 2 (by rfl) ⟨297519, by rfl⟩ : syracuseStep 793385 = 595039) B595039
theorem B793595 : Blo 527800 793595 := bstep (se 1 (by rfl) ⟨595196, by rfl⟩ : syracuseStep 793595 = 1190393) B1190393
theorem B531451 : Blo 527800 531451 := bstep (se 1 (by rfl) ⟨398588, by rfl⟩ : syracuseStep 531451 = 797177) B797177
theorem B793631 : Blo 527800 793631 := bstep (se 1 (by rfl) ⟨595223, by rfl⟩ : syracuseStep 793631 = 1190447) B1190447
theorem B531487 : Blo 527800 531487 := bstep (se 1 (by rfl) ⟨398615, by rfl⟩ : syracuseStep 531487 = 797231) B797231
theorem B793655 : Blo 527800 793655 := bstep (se 1 (by rfl) ⟨595241, by rfl⟩ : syracuseStep 793655 = 1190483) B1190483
theorem B793775 : Blo 527800 793775 := bstep (se 1 (by rfl) ⟨595331, by rfl⟩ : syracuseStep 793775 = 1190663) B1190663
theorem B793919 : Blo 527800 793919 := bstep (se 1 (by rfl) ⟨595439, by rfl⟩ : syracuseStep 793919 = 1190879) B1190879
theorem B531775 : Blo 527800 531775 := bstep (se 1 (by rfl) ⟨398831, by rfl⟩ : syracuseStep 531775 = 797663) B797663
theorem B794063 : Blo 527800 794063 := bstep (se 1 (by rfl) ⟨595547, by rfl⟩ : syracuseStep 794063 = 1191095) B1191095
theorem B88219205 : Blo 527800 88219205 := bstep (se 4 (by rfl) ⟨8270550, by rfl⟩ : syracuseStep 88219205 = 16541101) B16541101
theorem B794447 : Blo 527800 794447 := bstep (se 1 (by rfl) ⟨595835, by rfl⟩ : syracuseStep 794447 = 1191671) B1191671
theorem B1187711 : Blo 527800 1187711 := bstep (se 1 (by rfl) ⟨890783, by rfl⟩ : syracuseStep 1187711 = 1781567) B1781567
theorem B794495 : Blo 527800 794495 := bstep (se 1 (by rfl) ⟨595871, by rfl⟩ : syracuseStep 794495 = 1191743) B1191743
theorem B1187783 : Blo 527800 1187783 := bstep (se 1 (by rfl) ⟨890837, by rfl⟩ : syracuseStep 1187783 = 1781675) B1781675
theorem B794567 : Blo 527800 794567 := bstep (se 1 (by rfl) ⟨595925, by rfl⟩ : syracuseStep 794567 = 1191851) B1191851
theorem B892903 : Blo 527800 892903 := bstep (se 1 (by rfl) ⟨669677, by rfl⟩ : syracuseStep 892903 = 1339355) B1339355
theorem B598171 : Blo 527800 598171 := bstep (se 1 (by rfl) ⟨448628, by rfl⟩ : syracuseStep 598171 = 897257) B897257
theorem B794807 : Blo 527800 794807 := bstep (se 1 (by rfl) ⟨596105, by rfl⟩ : syracuseStep 794807 = 1192211) B1192211
theorem B1188143 : Blo 527800 1188143 := bstep (se 1 (by rfl) ⟨891107, by rfl⟩ : syracuseStep 1188143 = 1782215) B1782215
theorem B794927 : Blo 527800 794927 := bstep (se 1 (by rfl) ⟨596195, by rfl⟩ : syracuseStep 794927 = 1192391) B1192391
theorem B795167 : Blo 527800 795167 := bstep (se 1 (by rfl) ⟨596375, by rfl⟩ : syracuseStep 795167 = 1192751) B1192751
theorem B4301351 : Blo 527800 4301351 := bstep (se 1 (by rfl) ⟨3226013, by rfl⟩ : syracuseStep 4301351 = 6452027) B6452027
theorem B795227 : Blo 527800 795227 := bstep (se 1 (by rfl) ⟨596420, by rfl⟩ : syracuseStep 795227 = 1192841) B1192841
theorem B3613501 : Blo 527800 3613501 := bstep (se 3 (by rfl) ⟨677531, by rfl⟩ : syracuseStep 3613501 = 1355063) B1355063
theorem B5743439 : Blo 527800 5743439 := bstep (se 1 (by rfl) ⟨4307579, by rfl⟩ : syracuseStep 5743439 = 8615159) B8615159
theorem B795743 : Blo 527800 795743 := bstep (se 1 (by rfl) ⟨596807, by rfl⟩ : syracuseStep 795743 = 1193615) B1193615
theorem B1188971 : Blo 527800 1188971 := bstep (se 1 (by rfl) ⟨891728, by rfl⟩ : syracuseStep 1188971 = 1783457) B1783457
theorem B795803 : Blo 527800 795803 := bstep (se 1 (by rfl) ⟨596852, by rfl⟩ : syracuseStep 795803 = 1193705) B1193705
theorem B2008273 : Blo 527800 2008273 := bstep (se 2 (by rfl) ⟨753102, by rfl⟩ : syracuseStep 2008273 = 1506205) B1506205
theorem B894415 : Blo 527800 894415 := bstep (se 1 (by rfl) ⟨670811, by rfl⟩ : syracuseStep 894415 = 1341623) B1341623
theorem B796265 : Blo 527800 796265 := bstep (se 2 (by rfl) ⟨298599, by rfl⟩ : syracuseStep 796265 = 597199) B597199
theorem B23602823 : Blo 527800 23602823 := bstep (se 1 (by rfl) ⟨17702117, by rfl⟩ : syracuseStep 23602823 = 35404235) B35404235
theorem B3221201 : Blo 527800 3221201 := bstep (se 2 (by rfl) ⟨1207950, by rfl⟩ : syracuseStep 3221201 = 2415901) B2415901
theorem B796391 : Blo 527800 796391 := bstep (se 1 (by rfl) ⟨597293, by rfl⟩ : syracuseStep 796391 = 1194587) B1194587
theorem B796487 : Blo 527800 796487 := bstep (se 1 (by rfl) ⟨597365, by rfl⟩ : syracuseStep 796487 = 1194731) B1194731
theorem B1189871 : Blo 527800 1189871 := bstep (se 1 (by rfl) ⟨892403, by rfl⟩ : syracuseStep 1189871 = 1784807) B1784807
theorem B6432959 : Blo 527800 6432959 := bstep (se 1 (by rfl) ⟨4824719, by rfl⟩ : syracuseStep 6432959 = 9649439) B9649439
theorem B796895 : Blo 527800 796895 := bstep (se 1 (by rfl) ⟨597671, by rfl⟩ : syracuseStep 796895 = 1195343) B1195343
theorem B796955 : Blo 527800 796955 := bstep (se 1 (by rfl) ⟨597716, by rfl⟩ : syracuseStep 796955 = 1195433) B1195433
theorem B797087 : Blo 527800 797087 := bstep (se 1 (by rfl) ⟨597815, by rfl⟩ : syracuseStep 797087 = 1195631) B1195631
theorem B895583 : Blo 527800 895583 := bstep (se 1 (by rfl) ⟨671687, by rfl⟩ : syracuseStep 895583 = 1343375) B1343375
theorem B797279 : Blo 527800 797279 := bstep (se 1 (by rfl) ⟨597959, by rfl⟩ : syracuseStep 797279 = 1195919) B1195919
theorem B535367 : Blo 527800 535367 := bstep (se 1 (by rfl) ⟨401525, by rfl⟩ : syracuseStep 535367 = 803051) B803051
theorem B3812183 : Blo 527800 3812183 := bstep (se 1 (by rfl) ⟨2859137, by rfl⟩ : syracuseStep 3812183 = 5718275) B5718275
theorem B797609 : Blo 527800 797609 := bstep (se 2 (by rfl) ⟨299103, by rfl⟩ : syracuseStep 797609 = 598207) B598207
theorem B797639 : Blo 527800 797639 := bstep (se 1 (by rfl) ⟨598229, by rfl⟩ : syracuseStep 797639 = 1196459) B1196459
theorem B1191275 : Blo 527800 1191275 := bstep (se 1 (by rfl) ⟨893456, by rfl⟩ : syracuseStep 1191275 = 1786913) B1786913
theorem B5090789 : Blo 527800 5090789 := bstep (se 4 (by rfl) ⟨477261, by rfl⟩ : syracuseStep 5090789 = 954523) B954523
theorem B1191545 : Blo 527800 1191545 := bstep (se 2 (by rfl) ⟨446829, by rfl⟩ : syracuseStep 1191545 = 893659) B893659
theorem B11448125 : Blo 527800 11448125 := bstep (se 3 (by rfl) ⟨2146523, by rfl⟩ : syracuseStep 11448125 = 4293047) B4293047
theorem B896879 : Blo 527800 896879 := bstep (se 1 (by rfl) ⟨672659, by rfl⟩ : syracuseStep 896879 = 1345319) B1345319
theorem B6795251 : Blo 527800 6795251 := bstep (se 1 (by rfl) ⟨5096438, by rfl⟩ : syracuseStep 6795251 = 10192877) B10192877
theorem B1192787 : Blo 527800 1192787 := bstep (se 1 (by rfl) ⟨894590, by rfl⟩ : syracuseStep 1192787 = 1789181) B1789181
theorem B1782809 : Blo 527800 1782809 := bstep (se 2 (by rfl) ⟨668553, by rfl⟩ : syracuseStep 1782809 = 1337107) B1337107
theorem B1782971 : Blo 527800 1782971 := bstep (se 1 (by rfl) ⟨1337228, by rfl⟩ : syracuseStep 1782971 = 2674457) B2674457
theorem B1193147 : Blo 527800 1193147 := bstep (se 1 (by rfl) ⟨894860, by rfl⟩ : syracuseStep 1193147 = 1789721) B1789721
theorem B1193273 : Blo 527800 1193273 := bstep (se 2 (by rfl) ⟨447477, by rfl⟩ : syracuseStep 1193273 = 894955) B894955
theorem B1193327 : Blo 527800 1193327 := bstep (se 1 (by rfl) ⟨894995, by rfl⟩ : syracuseStep 1193327 = 1789991) B1789991
theorem B669055 : Blo 527800 669055 := bstep (se 1 (by rfl) ⟨501791, by rfl⟩ : syracuseStep 669055 = 1003583) B1003583
theorem B2536879 : Blo 527800 2536879 := bstep (se 1 (by rfl) ⟨1902659, by rfl⟩ : syracuseStep 2536879 = 3805319) B3805319
theorem B1357651 : Blo 527800 1357651 := bstep (se 1 (by rfl) ⟨1018238, by rfl⟩ : syracuseStep 1357651 = 2036477) B2036477
theorem B2013119 : Blo 527800 2013119 := bstep (se 1 (by rfl) ⟨1509839, by rfl⟩ : syracuseStep 2013119 = 3019679) B3019679
theorem B1193975 : Blo 527800 1193975 := bstep (se 1 (by rfl) ⟨895481, by rfl⟩ : syracuseStep 1193975 = 1790963) B1790963
theorem B1194047 : Blo 527800 1194047 := bstep (se 1 (by rfl) ⟨895535, by rfl⟩ : syracuseStep 1194047 = 1791071) B1791071
theorem B997439 : Blo 527800 997439 := bstep (se 1 (by rfl) ⟨748079, by rfl⟩ : syracuseStep 997439 = 1496159) B1496159
theorem B669799 : Blo 527800 669799 := bstep (se 1 (by rfl) ⟨502349, by rfl⟩ : syracuseStep 669799 = 1004699) B1004699
theorem B1194335 : Blo 527800 1194335 := bstep (se 1 (by rfl) ⟨895751, by rfl⟩ : syracuseStep 1194335 = 1791503) B1791503
theorem B2865665 : Blo 527800 2865665 := bstep (se 2 (by rfl) ⟨1074624, by rfl⟩ : syracuseStep 2865665 = 2149249) B2149249
theorem B2538323 : Blo 527800 2538323 := bstep (se 1 (by rfl) ⟨1903742, by rfl⟩ : syracuseStep 2538323 = 3807485) B3807485
theorem B1194875 : Blo 527800 1194875 := bstep (se 1 (by rfl) ⟨896156, by rfl⟩ : syracuseStep 1194875 = 1792313) B1792313
theorem B50412557 : Blo 527800 50412557 := bstep (se 3 (by rfl) ⟨9452354, by rfl⟩ : syracuseStep 50412557 = 18904709) B18904709
theorem B1195055 : Blo 527800 1195055 := bstep (se 1 (by rfl) ⟨896291, by rfl⟩ : syracuseStep 1195055 = 1792583) B1792583
theorem B1785455 : Blo 527800 1785455 := bstep (se 1 (by rfl) ⟨1339091, by rfl⟩ : syracuseStep 1785455 = 2678183) B2678183
theorem B2014895 : Blo 527800 2014895 := bstep (se 1 (by rfl) ⟨1511171, by rfl⟩ : syracuseStep 2014895 = 3022343) B3022343
theorem B5881643 : Blo 527800 5881643 := bstep (se 1 (by rfl) ⟨4411232, by rfl⟩ : syracuseStep 5881643 = 8822465) B8822465
theorem B671647 : Blo 527800 671647 := bstep (se 1 (by rfl) ⟨503735, by rfl⟩ : syracuseStep 671647 = 1007471) B1007471
theorem B12239905 : Blo 527800 12239905 := bstep (se 2 (by rfl) ⟨4589964, by rfl⟩ : syracuseStep 12239905 = 9179929) B9179929
theorem B804023 : Blo 527800 804023 := bstep (se 1 (by rfl) ⟨603017, by rfl⟩ : syracuseStep 804023 = 1206035) B1206035
theorem B2672027 : Blo 527800 2672027 := bstep (se 1 (by rfl) ⟨2004020, by rfl⟩ : syracuseStep 2672027 = 4008041) B4008041
theorem B1525279 : Blo 527800 1525279 := bstep (se 1 (by rfl) ⟨1143959, by rfl⟩ : syracuseStep 1525279 = 2287919) B2287919
theorem B1198571 : Blo 527800 1198571 := bstep (se 1 (by rfl) ⟨898928, by rfl⟩ : syracuseStep 1198571 = 1797857) B1797857
theorem B8276779 : Blo 527800 8276779 := bstep (se 1 (by rfl) ⟨6207584, by rfl⟩ : syracuseStep 8276779 = 12415169) B12415169
theorem B6802937 : Blo 527800 6802937 := bstep (se 2 (by rfl) ⟨2551101, by rfl⟩ : syracuseStep 6802937 = 5102203) B5102203
theorem B1003241 : Blo 527800 1003241 := bstep (se 2 (by rfl) ⟨376215, by rfl⟩ : syracuseStep 1003241 = 752431) B752431
theorem B2871247 : Blo 527800 2871247 := bstep (se 1 (by rfl) ⟨2153435, by rfl⟩ : syracuseStep 2871247 = 4306871) B4306871
theorem B1528235 : Blo 527800 1528235 := bstep (se 1 (by rfl) ⟨1146176, by rfl⟩ : syracuseStep 1528235 = 2292353) B2292353
theorem B1135019 : Blo 527800 1135019 := bstep (se 1 (by rfl) ⟨851264, by rfl⟩ : syracuseStep 1135019 = 1702529) B1702529
theorem B4084157 : Blo 527800 4084157 := bstep (se 3 (by rfl) ⟨765779, by rfl⟩ : syracuseStep 4084157 = 1531559) B1531559
theorem B17355485 : Blo 527800 17355485 := bstep (se 3 (by rfl) ⟨3254153, by rfl⟩ : syracuseStep 17355485 = 6508307) B6508307
theorem B906491 : Blo 527800 906491 := bstep (se 1 (by rfl) ⟨679868, by rfl⟩ : syracuseStep 906491 = 1359737) B1359737
theorem B2676239 : Blo 527800 2676239 := bstep (se 1 (by rfl) ⟨2007179, by rfl⟩ : syracuseStep 2676239 = 4014359) B4014359
theorem B9164411 : Blo 527800 9164411 := bstep (se 1 (by rfl) ⟨6873308, by rfl⟩ : syracuseStep 9164411 = 13746617) B13746617
theorem B1791827 : Blo 527800 1791827 := bstep (se 1 (by rfl) ⟨1343870, by rfl⟩ : syracuseStep 1791827 = 2687741) B2687741
theorem B4511645 : Blo 527800 4511645 := bstep (se 3 (by rfl) ⟨845933, by rfl⟩ : syracuseStep 4511645 = 1691867) B1691867
theorem B1007167 : Blo 527800 1007167 := bstep (se 1 (by rfl) ⟨755375, by rfl⟩ : syracuseStep 1007167 = 1510751) B1510751
theorem B2678345 : Blo 527800 2678345 := bstep (se 2 (by rfl) ⟨1004379, by rfl⟩ : syracuseStep 2678345 = 2008759) B2008759
theorem B7626959 : Blo 527800 7626959 := bstep (se 1 (by rfl) ⟨5720219, by rfl⟩ : syracuseStep 7626959 = 11440439) B11440439
theorem B1008875 : Blo 527800 1008875 := bstep (se 1 (by rfl) ⟨756656, by rfl⟩ : syracuseStep 1008875 = 1513313) B1513313
theorem B5727617 : Blo 527800 5727617 := bstep (se 2 (by rfl) ⟨2147856, by rfl⟩ : syracuseStep 5727617 = 4295713) B4295713
theorem B2713085 : Blo 527800 2713085 := bstep (se 3 (by rfl) ⟨508703, by rfl⟩ : syracuseStep 2713085 = 1017407) B1017407
theorem B1336895 : Blo 527800 1336895 := bstep (se 1 (by rfl) ⟨1002671, by rfl⟩ : syracuseStep 1336895 = 2005343) B2005343
theorem B87156323 : Blo 527800 87156323 := bstep (se 1 (by rfl) ⟨65367242, by rfl⟩ : syracuseStep 87156323 = 130734485) B130734485
theorem B1271467 : Blo 527800 1271467 := bstep (se 1 (by rfl) ⟨953600, by rfl⟩ : syracuseStep 1271467 = 1907201) B1907201
theorem B27453329 : Blo 527800 27453329 := bstep (se 2 (by rfl) ⟨10294998, by rfl⟩ : syracuseStep 27453329 = 20589997) B20589997
theorem B3008447 : Blo 527800 3008447 := bstep (se 1 (by rfl) ⟨2256335, by rfl⟩ : syracuseStep 3008447 = 4512671) B4512671
theorem B2680775 : Blo 527800 2680775 := bstep (se 1 (by rfl) ⟨2010581, by rfl⟩ : syracuseStep 2680775 = 4021163) B4021163
theorem B2549951 : Blo 527800 2549951 := bstep (se 1 (by rfl) ⟨1912463, by rfl⟩ : syracuseStep 2549951 = 3824927) B3824927
theorem B1337543 : Blo 527800 1337543 := bstep (se 1 (by rfl) ⟨1003157, by rfl⟩ : syracuseStep 1337543 = 2006315) B2006315
theorem B7268717 : Blo 527800 7268717 := bstep (se 3 (by rfl) ⟨1362884, by rfl⟩ : syracuseStep 7268717 = 2725769) B2725769
theorem B6056531 : Blo 527800 6056531 := bstep (se 1 (by rfl) ⟨4542398, by rfl⟩ : syracuseStep 6056531 = 9084797) B9084797
theorem B2550487 : Blo 527800 2550487 := bstep (se 1 (by rfl) ⟨1912865, by rfl⟩ : syracuseStep 2550487 = 3825731) B3825731
theorem B1338241 : Blo 527800 1338241 := bstep (se 2 (by rfl) ⟨501840, by rfl⟩ : syracuseStep 1338241 = 1003681) B1003681
theorem B1339051 : Blo 527800 1339051 := bstep (se 1 (by rfl) ⟨1004288, by rfl⟩ : syracuseStep 1339051 = 2008577) B2008577
theorem B3010223 : Blo 527800 3010223 := bstep (se 1 (by rfl) ⟨2257667, by rfl⟩ : syracuseStep 3010223 = 4515335) B4515335
theorem B1699709 : Blo 527800 1699709 := bstep (se 3 (by rfl) ⟨318695, by rfl⟩ : syracuseStep 1699709 = 637391) B637391
theorem B1208297 : Blo 527800 1208297 := bstep (se 2 (by rfl) ⟨453111, by rfl⟩ : syracuseStep 1208297 = 906223) B906223
theorem B22835357 : Blo 527800 22835357 := bstep (se 3 (by rfl) ⟨4281629, by rfl⟩ : syracuseStep 22835357 = 8563259) B8563259
theorem B2552161 : Blo 527800 2552161 := bstep (se 2 (by rfl) ⟨957060, by rfl⟩ : syracuseStep 2552161 = 1914121) B1914121
theorem B1208699 : Blo 527800 1208699 := bstep (se 1 (by rfl) ⟨906524, by rfl⟩ : syracuseStep 1208699 = 1813049) B1813049
theorem B1503643 : Blo 527800 1503643 := bstep (se 1 (by rfl) ⟨1127732, by rfl⟩ : syracuseStep 1503643 = 2255465) B2255465
theorem B12579259 : Blo 527800 12579259 := bstep (se 1 (by rfl) ⟨9434444, by rfl⟩ : syracuseStep 12579259 = 18868889) B18868889
theorem B1340297 : Blo 527800 1340297 := bstep (se 2 (by rfl) ⟨502611, by rfl⟩ : syracuseStep 1340297 = 1005223) B1005223
theorem B1340327 : Blo 527800 1340327 := bstep (se 1 (by rfl) ⟨1005245, by rfl⟩ : syracuseStep 1340327 = 2010491) B2010491
theorem B1505591 : Blo 527800 1505591 := bstep (se 1 (by rfl) ⟨1129193, by rfl⟩ : syracuseStep 1505591 = 2258387) B2258387
theorem B6879755 : Blo 527800 6879755 := bstep (se 1 (by rfl) ⟨5159816, by rfl⟩ : syracuseStep 6879755 = 10319633) B10319633
theorem B2554679 : Blo 527800 2554679 := bstep (se 1 (by rfl) ⟨1916009, by rfl⟩ : syracuseStep 2554679 = 3832019) B3832019
theorem B1702939 : Blo 527800 1702939 := bstep (se 1 (by rfl) ⟨1277204, by rfl⟩ : syracuseStep 1702939 = 2554409) B2554409
theorem B1375507 : Blo 527800 1375507 := bstep (se 1 (by rfl) ⟨1031630, by rfl⟩ : syracuseStep 1375507 = 2063261) B2063261
theorem B4521419 : Blo 527800 4521419 := bstep (se 1 (by rfl) ⟨3391064, by rfl⟩ : syracuseStep 4521419 = 6782129) B6782129
theorem B6423425 : Blo 527800 6423425 := bstep (se 2 (by rfl) ⟨2408784, by rfl⟩ : syracuseStep 6423425 = 4817569) B4817569
theorem B2360495 : Blo 527800 2360495 := bstep (se 1 (by rfl) ⟨1770371, by rfl⟩ : syracuseStep 2360495 = 3540743) B3540743
theorem B14550353 : Blo 527800 14550353 := bstep (se 2 (by rfl) ⟨5456382, by rfl⟩ : syracuseStep 14550353 = 10912765) B10912765
theorem B16319873 : Blo 527800 16319873 := bstep (se 2 (by rfl) ⟨6119952, by rfl⟩ : syracuseStep 16319873 = 12239905) B12239905
theorem B2033705 : Blo 527800 2033705 := bstep (se 2 (by rfl) ⟨762639, by rfl⟩ : syracuseStep 2033705 = 1525279) B1525279
theorem B3017195 : Blo 527800 3017195 := bstep (se 1 (by rfl) ⟨2262896, by rfl⟩ : syracuseStep 3017195 = 4525793) B4525793
theorem B3017513 : Blo 527800 3017513 := bstep (se 2 (by rfl) ⟨1131567, by rfl⟩ : syracuseStep 3017513 = 2263135) B2263135
theorem B2689847 : Blo 527800 2689847 := bstep (se 1 (by rfl) ⟨2017385, by rfl⟩ : syracuseStep 2689847 = 4034771) B4034771
theorem B1018823 : Blo 527800 1018823 := bstep (se 1 (by rfl) ⟨764117, by rfl⟩ : syracuseStep 1018823 = 1528235) B1528235
theorem B2722771 : Blo 527800 2722771 := bstep (se 1 (by rfl) ⟨2042078, by rfl⟩ : syracuseStep 2722771 = 4084157) B4084157
theorem B11570323 : Blo 527800 11570323 := bstep (se 1 (by rfl) ⟨8677742, by rfl⟩ : syracuseStep 11570323 = 17355485) B17355485
theorem B2690333 : Blo 527800 2690333 := bstep (se 3 (by rfl) ⟨504437, by rfl⟩ : syracuseStep 2690333 = 1008875) B1008875
theorem B527823 : Blo 527800 527823 := bstep (se 1 (by rfl) ⟨395867, by rfl⟩ : syracuseStep 527823 = 791735) B791735
theorem B527983 : Blo 527800 527983 := bstep (se 1 (by rfl) ⟨395987, by rfl⟩ : syracuseStep 527983 = 791975) B791975
theorem B528103 : Blo 527800 528103 := bstep (se 1 (by rfl) ⟨396077, by rfl⟩ : syracuseStep 528103 = 792155) B792155
theorem B1904735 : Blo 527800 1904735 := bstep (se 1 (by rfl) ⟨1428551, by rfl⟩ : syracuseStep 1904735 = 2857103) B2857103
theorem B528607 : Blo 527800 528607 := bstep (se 1 (by rfl) ⟨396455, by rfl⟩ : syracuseStep 528607 = 792911) B792911
theorem B528623 : Blo 527800 528623 := bstep (se 1 (by rfl) ⟨396467, by rfl⟩ : syracuseStep 528623 = 792935) B792935
theorem B528667 : Blo 527800 528667 := bstep (se 1 (by rfl) ⟨396500, by rfl⟩ : syracuseStep 528667 = 793001) B793001
theorem B19272005 : Blo 527800 19272005 := bstep (se 4 (by rfl) ⟨1806750, by rfl⟩ : syracuseStep 19272005 = 3613501) B3613501
theorem B528923 : Blo 527800 528923 := bstep (se 1 (by rfl) ⟨396692, by rfl⟩ : syracuseStep 528923 = 793385) B793385
theorem B529063 : Blo 527800 529063 := bstep (se 1 (by rfl) ⟨396797, by rfl⟩ : syracuseStep 529063 = 793595) B793595
theorem B529087 : Blo 527800 529087 := bstep (se 1 (by rfl) ⟨396815, by rfl⟩ : syracuseStep 529087 = 793631) B793631
theorem B529103 : Blo 527800 529103 := bstep (se 1 (by rfl) ⟨396827, by rfl⟩ : syracuseStep 529103 = 793655) B793655
theorem B529183 : Blo 527800 529183 := bstep (se 1 (by rfl) ⟨396887, by rfl⟩ : syracuseStep 529183 = 793775) B793775
theorem B529279 : Blo 527800 529279 := bstep (se 1 (by rfl) ⟨396959, by rfl⟩ : syracuseStep 529279 = 793919) B793919
theorem B529375 : Blo 527800 529375 := bstep (se 1 (by rfl) ⟨397031, by rfl⟩ : syracuseStep 529375 = 794063) B794063
theorem B529631 : Blo 527800 529631 := bstep (se 1 (by rfl) ⟨397223, by rfl⟩ : syracuseStep 529631 = 794447) B794447
theorem B791807 : Blo 527800 791807 := bstep (se 1 (by rfl) ⟨593855, by rfl⟩ : syracuseStep 791807 = 1187711) B1187711
theorem B529663 : Blo 527800 529663 := bstep (se 1 (by rfl) ⟨397247, by rfl⟩ : syracuseStep 529663 = 794495) B794495
theorem B791855 : Blo 527800 791855 := bstep (se 1 (by rfl) ⟨593891, by rfl⟩ : syracuseStep 791855 = 1187783) B1187783
theorem B529711 : Blo 527800 529711 := bstep (se 1 (by rfl) ⟨397283, by rfl⟩ : syracuseStep 529711 = 794567) B794567
theorem B529871 : Blo 527800 529871 := bstep (se 1 (by rfl) ⟨397403, by rfl⟩ : syracuseStep 529871 = 794807) B794807
theorem B5084639 : Blo 527800 5084639 := bstep (se 1 (by rfl) ⟨3813479, by rfl⟩ : syracuseStep 5084639 = 7626959) B7626959
theorem B2659837 : Blo 527800 2659837 := bstep (se 3 (by rfl) ⟨498719, by rfl⟩ : syracuseStep 2659837 = 997439) B997439
theorem B792095 : Blo 527800 792095 := bstep (se 1 (by rfl) ⟨594071, by rfl⟩ : syracuseStep 792095 = 1188143) B1188143
theorem B529951 : Blo 527800 529951 := bstep (se 1 (by rfl) ⟨397463, by rfl⟩ : syracuseStep 529951 = 794927) B794927
theorem B530111 : Blo 527800 530111 := bstep (se 1 (by rfl) ⟨397583, by rfl⟩ : syracuseStep 530111 = 795167) B795167
theorem B530151 : Blo 527800 530151 := bstep (se 1 (by rfl) ⟨397613, by rfl⟩ : syracuseStep 530151 = 795227) B795227
theorem B2004857 : Blo 527800 2004857 := bstep (se 2 (by rfl) ⟨751821, by rfl⟩ : syracuseStep 2004857 = 1503643) B1503643
theorem B530495 : Blo 527800 530495 := bstep (se 1 (by rfl) ⟨397871, by rfl⟩ : syracuseStep 530495 = 795743) B795743
theorem B792647 : Blo 527800 792647 := bstep (se 1 (by rfl) ⟨594485, by rfl⟩ : syracuseStep 792647 = 1188971) B1188971
theorem B530535 : Blo 527800 530535 := bstep (se 1 (by rfl) ⟨397901, by rfl⟩ : syracuseStep 530535 = 795803) B795803
theorem B1808723 : Blo 527800 1808723 := bstep (se 1 (by rfl) ⟨1356542, by rfl⟩ : syracuseStep 1808723 = 2713085) B2713085
theorem B891263 : Blo 527800 891263 := bstep (se 1 (by rfl) ⟨668447, by rfl⟩ : syracuseStep 891263 = 1336895) B1336895
theorem B58104215 : Blo 527800 58104215 := bstep (se 1 (by rfl) ⟨43578161, by rfl⟩ : syracuseStep 58104215 = 87156323) B87156323
theorem B530843 : Blo 527800 530843 := bstep (se 1 (by rfl) ⟨398132, by rfl⟩ : syracuseStep 530843 = 796265) B796265
theorem B15735215 : Blo 527800 15735215 := bstep (se 1 (by rfl) ⟨11801411, by rfl⟩ : syracuseStep 15735215 = 23602823) B23602823
theorem B30284225 : Blo 527800 30284225 := bstep (se 2 (by rfl) ⟨11356584, by rfl⟩ : syracuseStep 30284225 = 22713169) B22713169
theorem B530927 : Blo 527800 530927 := bstep (se 1 (by rfl) ⟨398195, by rfl⟩ : syracuseStep 530927 = 796391) B796391
theorem B530991 : Blo 527800 530991 := bstep (se 1 (by rfl) ⟨398243, by rfl⟩ : syracuseStep 530991 = 796487) B796487
theorem B2005631 : Blo 527800 2005631 := bstep (se 1 (by rfl) ⟨1504223, by rfl⟩ : syracuseStep 2005631 = 3008447) B3008447
theorem B793247 : Blo 527800 793247 := bstep (se 1 (by rfl) ⟨594935, by rfl⟩ : syracuseStep 793247 = 1189871) B1189871
theorem B7641773 : Blo 527800 7641773 := bstep (se 3 (by rfl) ⟨1432832, by rfl⟩ : syracuseStep 7641773 = 2865665) B2865665
theorem B891695 : Blo 527800 891695 := bstep (se 1 (by rfl) ⟨668771, by rfl⟩ : syracuseStep 891695 = 1337543) B1337543
theorem B531263 : Blo 527800 531263 := bstep (se 1 (by rfl) ⟨398447, by rfl⟩ : syracuseStep 531263 = 796895) B796895
theorem B531303 : Blo 527800 531303 := bstep (se 1 (by rfl) ⟨398477, by rfl⟩ : syracuseStep 531303 = 796955) B796955
theorem B531391 : Blo 527800 531391 := bstep (se 1 (by rfl) ⟨398543, by rfl⟩ : syracuseStep 531391 = 797087) B797087
theorem B4037687 : Blo 527800 4037687 := bstep (se 1 (by rfl) ⟨3028265, by rfl⟩ : syracuseStep 4037687 = 6056531) B6056531
theorem B597055 : Blo 527800 597055 := bstep (se 1 (by rfl) ⟨447791, by rfl⟩ : syracuseStep 597055 = 895583) B895583
theorem B531519 : Blo 527800 531519 := bstep (se 1 (by rfl) ⟨398639, by rfl⟩ : syracuseStep 531519 = 797279) B797279
theorem B892073 : Blo 527800 892073 := bstep (se 2 (by rfl) ⟨334527, by rfl⟩ : syracuseStep 892073 = 669055) B669055
theorem B3382505 : Blo 527800 3382505 := bstep (se 2 (by rfl) ⟨1268439, by rfl⟩ : syracuseStep 3382505 = 2536879) B2536879
theorem B531739 : Blo 527800 531739 := bstep (se 1 (by rfl) ⟨398804, by rfl⟩ : syracuseStep 531739 = 797609) B797609
theorem B531759 : Blo 527800 531759 := bstep (se 1 (by rfl) ⟨398819, by rfl⟩ : syracuseStep 531759 = 797639) B797639
theorem B794183 : Blo 527800 794183 := bstep (se 1 (by rfl) ⟨595637, by rfl⟩ : syracuseStep 794183 = 1191275) B1191275
theorem B794363 : Blo 527800 794363 := bstep (se 1 (by rfl) ⟨595772, by rfl⟩ : syracuseStep 794363 = 1191545) B1191545
theorem B1810201 : Blo 527800 1810201 := bstep (se 2 (by rfl) ⟨678825, by rfl⟩ : syracuseStep 1810201 = 1357651) B1357651
theorem B2006815 : Blo 527800 2006815 := bstep (se 1 (by rfl) ⟨1505111, by rfl⟩ : syracuseStep 2006815 = 3010223) B3010223
theorem B597919 : Blo 527800 597919 := bstep (se 1 (by rfl) ⟨448439, by rfl⟩ : syracuseStep 597919 = 896879) B896879
theorem B4530167 : Blo 527800 4530167 := bstep (se 1 (by rfl) ⟨3397625, by rfl⟩ : syracuseStep 4530167 = 6795251) B6795251
theorem B893065 : Blo 527800 893065 := bstep (se 2 (by rfl) ⟨334899, by rfl⟩ : syracuseStep 893065 = 669799) B669799
theorem B795191 : Blo 527800 795191 := bstep (se 1 (by rfl) ⟨596393, by rfl⟩ : syracuseStep 795191 = 1192787) B1192787
theorem B893531 : Blo 527800 893531 := bstep (se 1 (by rfl) ⟨670148, by rfl⟩ : syracuseStep 893531 = 1340297) B1340297
theorem B893551 : Blo 527800 893551 := bstep (se 1 (by rfl) ⟨670163, by rfl⟩ : syracuseStep 893551 = 1340327) B1340327
theorem B1188539 : Blo 527800 1188539 := bstep (se 1 (by rfl) ⟨891404, by rfl⟩ : syracuseStep 1188539 = 1782809) B1782809
theorem B1188647 : Blo 527800 1188647 := bstep (se 1 (by rfl) ⟨891485, by rfl⟩ : syracuseStep 1188647 = 1782971) B1782971
theorem B795431 : Blo 527800 795431 := bstep (se 1 (by rfl) ⟨596573, by rfl⟩ : syracuseStep 795431 = 1193147) B1193147
theorem B795515 : Blo 527800 795515 := bstep (se 1 (by rfl) ⟨596636, by rfl⟩ : syracuseStep 795515 = 1193273) B1193273
theorem B795551 : Blo 527800 795551 := bstep (se 1 (by rfl) ⟨596663, by rfl⟩ : syracuseStep 795551 = 1193327) B1193327
theorem B795641 : Blo 527800 795641 := bstep (se 2 (by rfl) ⟨298365, by rfl⟩ : syracuseStep 795641 = 596731) B596731
theorem B795983 : Blo 527800 795983 := bstep (se 1 (by rfl) ⟨596987, by rfl⟩ : syracuseStep 795983 = 1193975) B1193975
theorem B2270585 : Blo 527800 2270585 := bstep (se 2 (by rfl) ⟨851469, by rfl⟩ : syracuseStep 2270585 = 1702939) B1702939
theorem B796031 : Blo 527800 796031 := bstep (se 1 (by rfl) ⟨597023, by rfl⟩ : syracuseStep 796031 = 1194047) B1194047
theorem B796223 : Blo 527800 796223 := bstep (se 1 (by rfl) ⟨597167, by rfl⟩ : syracuseStep 796223 = 1194335) B1194335
theorem B796583 : Blo 527800 796583 := bstep (se 1 (by rfl) ⟨597437, by rfl⟩ : syracuseStep 796583 = 1194875) B1194875
theorem B796703 : Blo 527800 796703 := bstep (se 1 (by rfl) ⟨597527, by rfl⟩ : syracuseStep 796703 = 1195055) B1195055
theorem B4532557 : Blo 527800 4532557 := bstep (se 3 (by rfl) ⟨849854, by rfl⟩ : syracuseStep 4532557 = 1699709) B1699709
theorem B1190303 : Blo 527800 1190303 := bstep (se 1 (by rfl) ⟨892727, by rfl⟩ : syracuseStep 1190303 = 1785455) B1785455
theorem B895529 : Blo 527800 895529 := bstep (se 2 (by rfl) ⟨335823, by rfl⟩ : syracuseStep 895529 = 671647) B671647
theorem B3222125 : Blo 527800 3222125 := bstep (se 3 (by rfl) ⟨604148, by rfl⟩ : syracuseStep 3222125 = 1208297) B1208297
theorem B1190537 : Blo 527800 1190537 := bstep (se 2 (by rfl) ⟨446451, by rfl⟩ : syracuseStep 1190537 = 892903) B892903
theorem B797561 : Blo 527800 797561 := bstep (se 2 (by rfl) ⟨299085, by rfl⟩ : syracuseStep 797561 = 598171) B598171
theorem B6040493 : Blo 527800 6040493 := bstep (se 3 (by rfl) ⟨1132592, by rfl⟩ : syracuseStep 6040493 = 2265185) B2265185
theorem B3386555 : Blo 527800 3386555 := bstep (se 1 (by rfl) ⟨2539916, by rfl⟩ : syracuseStep 3386555 = 5079833) B5079833
theorem B4369747 : Blo 527800 4369747 := bstep (se 1 (by rfl) ⟨3277310, by rfl⟩ : syracuseStep 4369747 = 6554621) B6554621
theorem B536015 : Blo 527800 536015 := bstep (se 1 (by rfl) ⟨402011, by rfl⟩ : syracuseStep 536015 = 804023) B804023
theorem B2010703 : Blo 527800 2010703 := bstep (se 1 (by rfl) ⟨1508027, by rfl⟩ : syracuseStep 2010703 = 3016055) B3016055
theorem B1781351 : Blo 527800 1781351 := bstep (se 1 (by rfl) ⟨1336013, by rfl⟩ : syracuseStep 1781351 = 2672027) B2672027
theorem B3026717 : Blo 527800 3026717 := bstep (se 3 (by rfl) ⟨567509, by rfl⟩ : syracuseStep 3026717 = 1135019) B1135019
theorem B897007 : Blo 527800 897007 := bstep (se 1 (by rfl) ⟨672755, by rfl⟩ : syracuseStep 897007 = 1345511) B1345511
theorem B1192553 : Blo 527800 1192553 := bstep (se 2 (by rfl) ⟨447207, by rfl⟩ : syracuseStep 1192553 = 894415) B894415
theorem B2143219 : Blo 527800 2143219 := bstep (se 1 (by rfl) ⟨1607414, by rfl⟩ : syracuseStep 2143219 = 3214829) B3214829
theorem B4535291 : Blo 527800 4535291 := bstep (se 1 (by rfl) ⟨3401468, by rfl⟩ : syracuseStep 4535291 = 6802937) B6802937
theorem B668827 : Blo 527800 668827 := bstep (se 1 (by rfl) ⟨501620, by rfl⟩ : syracuseStep 668827 = 1003241) B1003241
theorem B1784159 : Blo 527800 1784159 := bstep (se 1 (by rfl) ⟨1338119, by rfl⟩ : syracuseStep 1784159 = 2676239) B2676239
theorem B6109607 : Blo 527800 6109607 := bstep (se 1 (by rfl) ⟨4582205, by rfl⟩ : syracuseStep 6109607 = 9164411) B9164411
theorem B1784321 : Blo 527800 1784321 := bstep (se 2 (by rfl) ⟨669120, by rfl⟩ : syracuseStep 1784321 = 1338241) B1338241
theorem B1194551 : Blo 527800 1194551 := bstep (se 1 (by rfl) ⟨895913, by rfl⟩ : syracuseStep 1194551 = 1791827) B1791827
theorem B2014091 : Blo 527800 2014091 := bstep (se 1 (by rfl) ⟨1510568, by rfl⟩ : syracuseStep 2014091 = 3021137) B3021137
theorem B1785401 : Blo 527800 1785401 := bstep (se 2 (by rfl) ⟨669525, by rfl⟩ : syracuseStep 1785401 = 1339051) B1339051
theorem B1785563 : Blo 527800 1785563 := bstep (se 1 (by rfl) ⟨1339172, by rfl⟩ : syracuseStep 1785563 = 2678345) B2678345
theorem B2867567 : Blo 527800 2867567 := bstep (se 1 (by rfl) ⟨2150675, by rfl⟩ : syracuseStep 2867567 = 4301351) B4301351
theorem B3818411 : Blo 527800 3818411 := bstep (se 1 (by rfl) ⟨2863808, by rfl⟩ : syracuseStep 3818411 = 5727617) B5727617
theorem B19383245 : Blo 527800 19383245 := bstep (se 3 (by rfl) ⟨3634358, by rfl⟩ : syracuseStep 19383245 = 7268717) B7268717
theorem B2147467 : Blo 527800 2147467 := bstep (se 1 (by rfl) ⟨1610600, by rfl⟩ : syracuseStep 2147467 = 3221201) B3221201
theorem B18302219 : Blo 527800 18302219 := bstep (se 1 (by rfl) ⟨13726664, by rfl⟩ : syracuseStep 18302219 = 27453329) B27453329
theorem B3196189 : Blo 527800 3196189 := bstep (se 3 (by rfl) ⟨599285, by rfl⟩ : syracuseStep 3196189 = 1198571) B1198571
theorem B1787183 : Blo 527800 1787183 := bstep (se 1 (by rfl) ⟨1340387, by rfl⟩ : syracuseStep 1787183 = 2680775) B2680775
theorem B2017021 : Blo 527800 2017021 := bstep (se 3 (by rfl) ⟨378191, by rfl⟩ : syracuseStep 2017021 = 756383) B756383
theorem B2541455 : Blo 527800 2541455 := bstep (se 1 (by rfl) ⟨1906091, by rfl⟩ : syracuseStep 2541455 = 3812183) B3812183
theorem B1427645 : Blo 527800 1427645 := bstep (se 3 (by rfl) ⟨267683, by rfl⟩ : syracuseStep 1427645 = 535367) B535367
theorem B3393859 : Blo 527800 3393859 := bstep (se 1 (by rfl) ⟨2545394, by rfl⟩ : syracuseStep 3393859 = 5090789) B5090789
theorem B2542013 : Blo 527800 2542013 := bstep (se 3 (by rfl) ⟨476627, by rfl⟩ : syracuseStep 2542013 = 953255) B953255
theorem B15223571 : Blo 527800 15223571 := bstep (se 1 (by rfl) ⟨11417678, by rfl⟩ : syracuseStep 15223571 = 22835357) B22835357
theorem B805799 : Blo 527800 805799 := bstep (se 1 (by rfl) ⟨604349, by rfl⟩ : syracuseStep 805799 = 1208699) B1208699
theorem B969833 : Blo 527800 969833 := bstep (se 2 (by rfl) ⟨363687, by rfl⟩ : syracuseStep 969833 = 727375) B727375
theorem B1003727 : Blo 527800 1003727 := bstep (se 1 (by rfl) ⟨752795, by rfl⟩ : syracuseStep 1003727 = 1505591) B1505591
theorem B1692215 : Blo 527800 1692215 := bstep (se 1 (by rfl) ⟨1269161, by rfl⟩ : syracuseStep 1692215 = 2538323) B2538323
theorem B33608371 : Blo 527800 33608371 := bstep (se 1 (by rfl) ⟨25206278, by rfl⟩ : syracuseStep 33608371 = 50412557) B50412557
theorem B3921095 : Blo 527800 3921095 := bstep (se 1 (by rfl) ⟨2940821, by rfl⟩ : syracuseStep 3921095 = 5881643) B5881643
theorem B4019705 : Blo 527800 4019705 := bstep (se 2 (by rfl) ⟨1507389, by rfl⟩ : syracuseStep 4019705 = 3014779) B3014779
theorem B1529435 : Blo 527800 1529435 := bstep (se 1 (by rfl) ⟨1147076, by rfl⟩ : syracuseStep 1529435 = 2294153) B2294153
theorem B1726591 : Blo 527800 1726591 := bstep (se 1 (by rfl) ⟨1294943, by rfl⟩ : syracuseStep 1726591 = 2589887) B2589887
theorem B2677697 : Blo 527800 2677697 := bstep (se 2 (by rfl) ⟨1004136, by rfl⟩ : syracuseStep 2677697 = 2008273) B2008273
theorem B1268729 : Blo 527800 1268729 := bstep (se 2 (by rfl) ⟨475773, by rfl⟩ : syracuseStep 1268729 = 951547) B951547
theorem B1007083 : Blo 527800 1007083 := bstep (se 1 (by rfl) ⟨755312, by rfl⟩ : syracuseStep 1007083 = 1510625) B1510625
theorem B1794203 : Blo 527800 1794203 := bstep (se 1 (by rfl) ⟨1345652, by rfl⟩ : syracuseStep 1794203 = 2691305) B2691305
theorem B2417309 : Blo 527800 2417309 := bstep (se 3 (by rfl) ⟨453245, by rfl⟩ : syracuseStep 2417309 = 906491) B906491
theorem B3400649 : Blo 527800 3400649 := bstep (se 2 (by rfl) ⟨1275243, by rfl⟩ : syracuseStep 3400649 = 2550487) B2550487
theorem B11035705 : Blo 527800 11035705 := bstep (se 2 (by rfl) ⟨4138389, by rfl⟩ : syracuseStep 11035705 = 8276779) B8276779
theorem B3007763 : Blo 527800 3007763 := bstep (se 1 (by rfl) ⟨2255822, by rfl⟩ : syracuseStep 3007763 = 4511645) B4511645
theorem B58812803 : Blo 527800 58812803 := bstep (se 1 (by rfl) ⟨44109602, by rfl⟩ : syracuseStep 58812803 = 88219205) B88219205
theorem B3828329 : Blo 527800 3828329 := bstep (se 2 (by rfl) ⟨1435623, by rfl⟩ : syracuseStep 3828329 = 2871247) B2871247
theorem B3402881 : Blo 527800 3402881 := bstep (se 2 (by rfl) ⟨1276080, by rfl⟩ : syracuseStep 3402881 = 2552161) B2552161
theorem B3828959 : Blo 527800 3828959 := bstep (se 1 (by rfl) ⟨2871719, by rfl⟩ : syracuseStep 3828959 = 5743439) B5743439
theorem B16772345 : Blo 527800 16772345 := bstep (se 2 (by rfl) ⟨6289629, by rfl⟩ : syracuseStep 16772345 = 12579259) B12579259
theorem B18346013 : Blo 527800 18346013 := bstep (se 3 (by rfl) ⟨3439877, by rfl⟩ : syracuseStep 18346013 = 6879755) B6879755
theorem B7336037 : Blo 527800 7336037 := bstep (se 4 (by rfl) ⟨687753, by rfl⟩ : syracuseStep 7336037 = 1375507) B1375507
theorem B4288639 : Blo 527800 4288639 := bstep (se 1 (by rfl) ⟨3216479, by rfl⟩ : syracuseStep 4288639 = 6432959) B6432959
theorem B1699967 : Blo 527800 1699967 := bstep (se 1 (by rfl) ⟨1274975, by rfl⟩ : syracuseStep 1699967 = 2549951) B2549951
theorem B7632083 : Blo 527800 7632083 := bstep (se 1 (by rfl) ⟨5724062, by rfl⟩ : syracuseStep 7632083 = 11448125) B11448125
theorem B6781157 : Blo 527800 6781157 := bstep (se 4 (by rfl) ⟨635733, by rfl⟩ : syracuseStep 6781157 = 1271467) B1271467
theorem B1342079 : Blo 527800 1342079 := bstep (se 1 (by rfl) ⟨1006559, by rfl⟩ : syracuseStep 1342079 = 2013119) B2013119
theorem B1703119 : Blo 527800 1703119 := bstep (se 1 (by rfl) ⟨1277339, by rfl⟩ : syracuseStep 1703119 = 2554679) B2554679
theorem B1342889 : Blo 527800 1342889 := bstep (se 2 (by rfl) ⟨503583, by rfl⟩ : syracuseStep 1342889 = 1007167) B1007167
theorem B3014279 : Blo 527800 3014279 := bstep (se 1 (by rfl) ⟨2260709, by rfl⟩ : syracuseStep 3014279 = 4521419) B4521419
theorem B1343263 : Blo 527800 1343263 := bstep (se 1 (by rfl) ⟨1007447, by rfl⟩ : syracuseStep 1343263 = 2014895) B2014895
theorem B5079293 : Blo 527800 5079293 := bstep (se 3 (by rfl) ⟨952367, by rfl⟩ : syracuseStep 5079293 = 1904735) B1904735
theorem B1573663 : Blo 527800 1573663 := bstep (se 1 (by rfl) ⟨1180247, by rfl⟩ : syracuseStep 1573663 = 2360495) B2360495
theorem B9700235 : Blo 527800 9700235 := bstep (se 1 (by rfl) ⟨7275176, by rfl⟩ : syracuseStep 9700235 = 14550353) B14550353
theorem B10879915 : Blo 527800 10879915 := bstep (se 1 (by rfl) ⟨8159936, by rfl⟩ : syracuseStep 10879915 = 16319873) B16319873
theorem B14714273 : Blo 527800 14714273 := bstep (se 2 (by rfl) ⟨5517852, by rfl⟩ : syracuseStep 14714273 = 11035705) B11035705
theorem B951763 : Blo 527800 951763 := bstep (se 1 (by rfl) ⟨713822, by rfl⟩ : syracuseStep 951763 = 1427645) B1427645
theorem B4261585 : Blo 527800 4261585 := bstep (se 2 (by rfl) ⟨1598094, by rfl⟩ : syracuseStep 4261585 = 3196189) B3196189
theorem B2689361 : Blo 527800 2689361 := bstep (se 2 (by rfl) ⟨1008510, by rfl⟩ : syracuseStep 2689361 = 2017021) B2017021
theorem B12848003 : Blo 527800 12848003 := bstep (se 1 (by rfl) ⟨9636002, by rfl⟩ : syracuseStep 12848003 = 19272005) B19272005
theorem B4525145 : Blo 527800 4525145 := bstep (se 2 (by rfl) ⟨1696929, by rfl⟩ : syracuseStep 4525145 = 3393859) B3393859
theorem B10456253 : Blo 527800 10456253 := bstep (se 3 (by rfl) ⟨1960547, by rfl⟩ : syracuseStep 10456253 = 3921095) B3921095
theorem B20352221 : Blo 527800 20352221 := bstep (se 3 (by rfl) ⟨3816041, by rfl⟩ : syracuseStep 20352221 = 7632083) B7632083
theorem B527871 : Blo 527800 527871 := bstep (se 1 (by rfl) ⟨395903, by rfl⟩ : syracuseStep 527871 = 791807) B791807
theorem B527903 : Blo 527800 527903 := bstep (se 1 (by rfl) ⟨395927, by rfl⟩ : syracuseStep 527903 = 791855) B791855
theorem B528063 : Blo 527800 528063 := bstep (se 1 (by rfl) ⟨396047, by rfl⟩ : syracuseStep 528063 = 792095) B792095
theorem B1019623 : Blo 527800 1019623 := bstep (se 1 (by rfl) ⟨764717, by rfl⟩ : syracuseStep 1019623 = 1529435) B1529435
theorem B528431 : Blo 527800 528431 := bstep (se 1 (by rfl) ⟨396323, by rfl⟩ : syracuseStep 528431 = 792647) B792647
theorem B594175 : Blo 527800 594175 := bstep (se 1 (by rfl) ⟨445631, by rfl⟩ : syracuseStep 594175 = 891263) B891263
theorem B38736143 : Blo 527800 38736143 := bstep (se 1 (by rfl) ⟨29052107, by rfl⟩ : syracuseStep 38736143 = 58104215) B58104215
theorem B10490143 : Blo 527800 10490143 := bstep (se 1 (by rfl) ⟨7867607, by rfl⟩ : syracuseStep 10490143 = 15735215) B15735215
theorem B20189483 : Blo 527800 20189483 := bstep (se 1 (by rfl) ⟨15142112, by rfl⟩ : syracuseStep 20189483 = 30284225) B30284225
theorem B528831 : Blo 527800 528831 := bstep (se 1 (by rfl) ⟨396623, by rfl⟩ : syracuseStep 528831 = 793247) B793247
theorem B594463 : Blo 527800 594463 := bstep (se 1 (by rfl) ⟨445847, by rfl⟩ : syracuseStep 594463 = 891695) B891695
theorem B2691791 : Blo 527800 2691791 := bstep (se 1 (by rfl) ⟨2018843, by rfl⟩ : syracuseStep 2691791 = 4037687) B4037687
theorem B594715 : Blo 527800 594715 := bstep (se 1 (by rfl) ⟨446036, by rfl⟩ : syracuseStep 594715 = 892073) B892073
theorem B529455 : Blo 527800 529455 := bstep (se 1 (by rfl) ⟨397091, by rfl⟩ : syracuseStep 529455 = 794183) B794183
theorem B529575 : Blo 527800 529575 := bstep (se 1 (by rfl) ⟨397181, by rfl⟩ : syracuseStep 529575 = 794363) B794363
theorem B3020111 : Blo 527800 3020111 := bstep (se 1 (by rfl) ⟨2265083, by rfl⟩ : syracuseStep 3020111 = 4530167) B4530167
theorem B530127 : Blo 527800 530127 := bstep (se 1 (by rfl) ⟨397595, by rfl⟩ : syracuseStep 530127 = 795191) B795191
theorem B595687 : Blo 527800 595687 := bstep (se 1 (by rfl) ⟨446765, by rfl⟩ : syracuseStep 595687 = 893531) B893531
theorem B1611539 : Blo 527800 1611539 := bstep (se 1 (by rfl) ⟨1208654, by rfl⟩ : syracuseStep 1611539 = 2417309) B2417309
theorem B792359 : Blo 527800 792359 := bstep (se 1 (by rfl) ⟨594269, by rfl⟩ : syracuseStep 792359 = 1188539) B1188539
theorem B792431 : Blo 527800 792431 := bstep (se 1 (by rfl) ⟨594323, by rfl⟩ : syracuseStep 792431 = 1188647) B1188647
theorem B530287 : Blo 527800 530287 := bstep (se 1 (by rfl) ⟨397715, by rfl⟩ : syracuseStep 530287 = 795431) B795431
theorem B530343 : Blo 527800 530343 := bstep (se 1 (by rfl) ⟨397757, by rfl⟩ : syracuseStep 530343 = 795515) B795515
theorem B530367 : Blo 527800 530367 := bstep (se 1 (by rfl) ⟨397775, by rfl⟩ : syracuseStep 530367 = 795551) B795551
theorem B2267099 : Blo 527800 2267099 := bstep (se 1 (by rfl) ⟨1700324, by rfl⟩ : syracuseStep 2267099 = 3400649) B3400649
theorem B530427 : Blo 527800 530427 := bstep (se 1 (by rfl) ⟨397820, by rfl⟩ : syracuseStep 530427 = 795641) B795641
theorem B2005175 : Blo 527800 2005175 := bstep (se 1 (by rfl) ⟨1503881, by rfl⟩ : syracuseStep 2005175 = 3007763) B3007763
theorem B530655 : Blo 527800 530655 := bstep (se 1 (by rfl) ⟨397991, by rfl⟩ : syracuseStep 530655 = 795983) B795983
theorem B1513723 : Blo 527800 1513723 := bstep (se 1 (by rfl) ⟨1135292, by rfl⟩ : syracuseStep 1513723 = 2270585) B2270585
theorem B530687 : Blo 527800 530687 := bstep (se 1 (by rfl) ⟨398015, by rfl⟩ : syracuseStep 530687 = 796031) B796031
theorem B530815 : Blo 527800 530815 := bstep (se 1 (by rfl) ⟨398111, by rfl⟩ : syracuseStep 530815 = 796223) B796223
theorem B16292285 : Blo 527800 16292285 := bstep (se 3 (by rfl) ⟨3054803, by rfl⟩ : syracuseStep 16292285 = 6109607) B6109607
theorem B531055 : Blo 527800 531055 := bstep (se 1 (by rfl) ⟨398291, by rfl⟩ : syracuseStep 531055 = 796583) B796583
theorem B2857625 : Blo 527800 2857625 := bstep (se 2 (by rfl) ⟨1071609, by rfl⟩ : syracuseStep 2857625 = 2143219) B2143219
theorem B531135 : Blo 527800 531135 := bstep (se 1 (by rfl) ⟨398351, by rfl⟩ : syracuseStep 531135 = 796703) B796703
theorem B891769 : Blo 527800 891769 := bstep (se 2 (by rfl) ⟨334413, by rfl⟩ : syracuseStep 891769 = 668827) B668827
theorem B793535 : Blo 527800 793535 := bstep (se 1 (by rfl) ⟨595151, by rfl⟩ : syracuseStep 793535 = 1190303) B1190303
theorem B597019 : Blo 527800 597019 := bstep (se 1 (by rfl) ⟨447764, by rfl⟩ : syracuseStep 597019 = 895529) B895529
theorem B793691 : Blo 527800 793691 := bstep (se 1 (by rfl) ⟨595268, by rfl⟩ : syracuseStep 793691 = 1190537) B1190537
theorem B531707 : Blo 527800 531707 := bstep (se 1 (by rfl) ⟨398780, by rfl⟩ : syracuseStep 531707 = 797561) B797561
theorem B3546449 : Blo 527800 3546449 := bstep (se 2 (by rfl) ⟨1329918, by rfl⟩ : syracuseStep 3546449 = 2659837) B2659837
theorem B2268587 : Blo 527800 2268587 := bstep (se 1 (by rfl) ⟨1701440, by rfl⟩ : syracuseStep 2268587 = 3402881) B3402881
theorem B11181563 : Blo 527800 11181563 := bstep (se 1 (by rfl) ⟨8386172, by rfl⟩ : syracuseStep 11181563 = 16772345) B16772345
theorem B1187567 : Blo 527800 1187567 := bstep (se 1 (by rfl) ⟨890675, by rfl⟩ : syracuseStep 1187567 = 1781351) B1781351
theorem B12230675 : Blo 527800 12230675 := bstep (se 1 (by rfl) ⟨9173006, by rfl⟩ : syracuseStep 12230675 = 18346013) B18346013
theorem B4890691 : Blo 527800 4890691 := bstep (se 1 (by rfl) ⟨3668018, by rfl⟩ : syracuseStep 4890691 = 7336037) B7336037
theorem B2302121 : Blo 527800 2302121 := bstep (se 2 (by rfl) ⟨863295, by rfl⟩ : syracuseStep 2302121 = 1726591) B1726591
theorem B795035 : Blo 527800 795035 := bstep (se 1 (by rfl) ⟨596276, by rfl⟩ : syracuseStep 795035 = 1192553) B1192553
theorem B3023527 : Blo 527800 3023527 := bstep (se 1 (by rfl) ⟨2267645, by rfl⟩ : syracuseStep 3023527 = 4535291) B4535291
theorem B796073 : Blo 527800 796073 := bstep (se 2 (by rfl) ⟨298527, by rfl⟩ : syracuseStep 796073 = 597055) B597055
theorem B1189439 : Blo 527800 1189439 := bstep (se 1 (by rfl) ⟨892079, by rfl⟩ : syracuseStep 1189439 = 1784159) B1784159
theorem B2270825 : Blo 527800 2270825 := bstep (se 2 (by rfl) ⟨851559, by rfl⟩ : syracuseStep 2270825 = 1703119) B1703119
theorem B1189547 : Blo 527800 1189547 := bstep (se 1 (by rfl) ⟨892160, by rfl⟩ : syracuseStep 1189547 = 1784321) B1784321
theorem B796367 : Blo 527800 796367 := bstep (se 1 (by rfl) ⟨597275, by rfl⟩ : syracuseStep 796367 = 1194551) B1194551
theorem B894719 : Blo 527800 894719 := bstep (se 1 (by rfl) ⟨671039, by rfl⟩ : syracuseStep 894719 = 1342079) B1342079
theorem B895259 : Blo 527800 895259 := bstep (se 1 (by rfl) ⟨671444, by rfl⟩ : syracuseStep 895259 = 1342889) B1342889
theorem B1190267 : Blo 527800 1190267 := bstep (se 1 (by rfl) ⟨892700, by rfl⟩ : syracuseStep 1190267 = 1785401) B1785401
theorem B2009519 : Blo 527800 2009519 := bstep (se 1 (by rfl) ⟨1507139, by rfl⟩ : syracuseStep 2009519 = 3014279) B3014279
theorem B1190375 : Blo 527800 1190375 := bstep (se 1 (by rfl) ⟨892781, by rfl⟩ : syracuseStep 1190375 = 1785563) B1785563
theorem B797225 : Blo 527800 797225 := bstep (se 2 (by rfl) ⟨298959, by rfl⟩ : syracuseStep 797225 = 597919) B597919
theorem B1190753 : Blo 527800 1190753 := bstep (se 2 (by rfl) ⟨446532, by rfl⟩ : syracuseStep 1190753 = 893065) B893065
theorem B12922163 : Blo 527800 12922163 := bstep (se 1 (by rfl) ⟨9691622, by rfl⟩ : syracuseStep 12922163 = 19383245) B19383245
theorem B1191401 : Blo 527800 1191401 := bstep (se 2 (by rfl) ⟨446775, by rfl⟩ : syracuseStep 1191401 = 893551) B893551
theorem B12201479 : Blo 527800 12201479 := bstep (se 1 (by rfl) ⟨9151109, by rfl⟩ : syracuseStep 12201479 = 18302219) B18302219
theorem B1191455 : Blo 527800 1191455 := bstep (se 1 (by rfl) ⟨893591, by rfl⟩ : syracuseStep 1191455 = 1787183) B1787183
theorem B2863289 : Blo 527800 2863289 := bstep (se 2 (by rfl) ⟨1073733, by rfl⟩ : syracuseStep 2863289 = 2147467) B2147467
theorem B2011463 : Blo 527800 2011463 := bstep (se 1 (by rfl) ⟨1508597, by rfl⟩ : syracuseStep 2011463 = 3017195) B3017195
theorem B2011675 : Blo 527800 2011675 := bstep (se 1 (by rfl) ⟨1508756, by rfl⟩ : syracuseStep 2011675 = 3017513) B3017513
theorem B537199 : Blo 527800 537199 := bstep (se 1 (by rfl) ⟨402899, by rfl⟩ : syracuseStep 537199 = 805799) B805799
theorem B669151 : Blo 527800 669151 := bstep (se 1 (by rfl) ⟨501863, by rfl⟩ : syracuseStep 669151 = 1003727) B1003727
theorem B1128143 : Blo 527800 1128143 := bstep (se 1 (by rfl) ⟨846107, by rfl⟩ : syracuseStep 1128143 = 1692215) B1692215
theorem B6043409 : Blo 527800 6043409 := bstep (se 2 (by rfl) ⟨2266278, by rfl⟩ : syracuseStep 6043409 = 4532557) B4532557
theorem B3389759 : Blo 527800 3389759 := bstep (se 1 (by rfl) ⟨2542319, by rfl⟩ : syracuseStep 3389759 = 5084639) B5084639
theorem B30587381 : Blo 527800 30587381 := bstep (se 5 (by rfl) ⟨1433783, by rfl⟩ : syracuseStep 30587381 = 2867567) B2867567
theorem B5094515 : Blo 527800 5094515 := bstep (se 1 (by rfl) ⟨3820886, by rfl⟩ : syracuseStep 5094515 = 7641773) B7641773
theorem B1785131 : Blo 527800 1785131 := bstep (se 1 (by rfl) ⟨1338848, by rfl⟩ : syracuseStep 1785131 = 2677697) B2677697
theorem B1196009 : Blo 527800 1196009 := bstep (se 2 (by rfl) ⟨448503, by rfl⟩ : syracuseStep 1196009 = 897007) B897007
theorem B1196135 : Blo 527800 1196135 := bstep (se 1 (by rfl) ⟨897101, by rfl⟩ : syracuseStep 1196135 = 1794203) B1794203
theorem B5423213 : Blo 527800 5423213 := bstep (se 3 (by rfl) ⟨1016852, by rfl⟩ : syracuseStep 5423213 = 2033705) B2033705
theorem B5718185 : Blo 527800 5718185 := bstep (se 2 (by rfl) ⟨2144319, by rfl⟩ : syracuseStep 5718185 = 4288639) B4288639
theorem B44811161 : Blo 527800 44811161 := bstep (se 2 (by rfl) ⟨16804185, by rfl⟩ : syracuseStep 44811161 = 33608371) B33608371
theorem B39208535 : Blo 527800 39208535 := bstep (se 1 (by rfl) ⟨29406401, by rfl⟩ : syracuseStep 39208535 = 58812803) B58812803
theorem B2148083 : Blo 527800 2148083 := bstep (se 1 (by rfl) ⟨1611062, by rfl⟩ : syracuseStep 2148083 = 3222125) B3222125
theorem B2017811 : Blo 527800 2017811 := bstep (se 1 (by rfl) ⟨1513358, by rfl⟩ : syracuseStep 2017811 = 3026717) B3026717
theorem B1133311 : Blo 527800 1133311 := bstep (se 1 (by rfl) ⟨849983, by rfl⟩ : syracuseStep 1133311 = 1699967) B1699967
theorem B1429373 : Blo 527800 1429373 := bstep (se 3 (by rfl) ⟨268007, by rfl⟩ : syracuseStep 1429373 = 536015) B536015
theorem B10867445 : Blo 527800 10867445 := bstep (se 5 (by rfl) ⟨509411, by rfl⟩ : syracuseStep 10867445 = 1018823) B1018823
theorem B2413601 : Blo 527800 2413601 := bstep (se 2 (by rfl) ⟨905100, by rfl⟩ : syracuseStep 2413601 = 1810201) B1810201
theorem B2675753 : Blo 527800 2675753 := bstep (se 2 (by rfl) ⟨1003407, by rfl⟩ : syracuseStep 2675753 = 2006815) B2006815
theorem B1791017 : Blo 527800 1791017 := bstep (se 2 (by rfl) ⟨671631, by rfl⟩ : syracuseStep 1791017 = 1343263) B1343263
theorem B4282283 : Blo 527800 4282283 := bstep (se 1 (by rfl) ⟨3211712, by rfl⟩ : syracuseStep 4282283 = 6423425) B6423425
theorem B2545607 : Blo 527800 2545607 := bstep (se 1 (by rfl) ⟨1909205, by rfl⟩ : syracuseStep 2545607 = 3818411) B3818411
theorem B1694303 : Blo 527800 1694303 := bstep (se 1 (by rfl) ⟨1270727, by rfl⟩ : syracuseStep 1694303 = 2541455) B2541455
theorem B1694675 : Blo 527800 1694675 := bstep (se 1 (by rfl) ⟨1271006, by rfl⟩ : syracuseStep 1694675 = 2542013) B2542013
theorem B10149047 : Blo 527800 10149047 := bstep (se 1 (by rfl) ⟨7611785, by rfl⟩ : syracuseStep 10149047 = 15223571) B15223571
theorem B1793231 : Blo 527800 1793231 := bstep (se 1 (by rfl) ⟨1344923, by rfl⟩ : syracuseStep 1793231 = 2689847) B2689847
theorem B1793555 : Blo 527800 1793555 := bstep (se 1 (by rfl) ⟨1345166, by rfl⟩ : syracuseStep 1793555 = 2690333) B2690333
theorem B2679803 : Blo 527800 2679803 := bstep (se 1 (by rfl) ⟨2009852, by rfl⟩ : syracuseStep 2679803 = 4019705) B4019705
theorem B1336571 : Blo 527800 1336571 := bstep (se 1 (by rfl) ⟨1002428, by rfl⟩ : syracuseStep 1336571 = 2004857) B2004857
theorem B3630361 : Blo 527800 3630361 := bstep (se 2 (by rfl) ⟨1361385, by rfl⟩ : syracuseStep 3630361 = 2722771) B2722771
theorem B15427097 : Blo 527800 15427097 := bstep (se 2 (by rfl) ⟨5785161, by rfl⟩ : syracuseStep 15427097 = 11570323) B11570323
theorem B1205815 : Blo 527800 1205815 := bstep (se 1 (by rfl) ⟨904361, by rfl⟩ : syracuseStep 1205815 = 1808723) B1808723
theorem B1337087 : Blo 527800 1337087 := bstep (se 1 (by rfl) ⟨1002815, by rfl⟩ : syracuseStep 1337087 = 2005631) B2005631
theorem B5826329 : Blo 527800 5826329 := bstep (se 2 (by rfl) ⟨2184873, by rfl⟩ : syracuseStep 5826329 = 4369747) B4369747
theorem B845819 : Blo 527800 845819 := bstep (se 1 (by rfl) ⟨634364, by rfl⟩ : syracuseStep 845819 = 1268729) B1268729
theorem B2680937 : Blo 527800 2680937 := bstep (se 2 (by rfl) ⟨1005351, by rfl⟩ : syracuseStep 2680937 = 2010703) B2010703
theorem B2255003 : Blo 527800 2255003 := bstep (se 1 (by rfl) ⟨1691252, by rfl⟩ : syracuseStep 2255003 = 3382505) B3382505
theorem B2552219 : Blo 527800 2552219 := bstep (se 1 (by rfl) ⟨1914164, by rfl⟩ : syracuseStep 2552219 = 3828329) B3828329
theorem B4026995 : Blo 527800 4026995 := bstep (se 1 (by rfl) ⟨3020246, by rfl⟩ : syracuseStep 4026995 = 6040493) B6040493
theorem B2257703 : Blo 527800 2257703 := bstep (se 1 (by rfl) ⟨1693277, by rfl⟩ : syracuseStep 2257703 = 3386555) B3386555
theorem B2552639 : Blo 527800 2552639 := bstep (se 1 (by rfl) ⟨1914479, by rfl⟩ : syracuseStep 2552639 = 3828959) B3828959
theorem B2586221 : Blo 527800 2586221 := bstep (se 3 (by rfl) ⟨484916, by rfl⟩ : syracuseStep 2586221 = 969833) B969833
theorem B4520771 : Blo 527800 4520771 := bstep (se 1 (by rfl) ⟨3390578, by rfl⟩ : syracuseStep 4520771 = 6781157) B6781157
theorem B1342727 : Blo 527800 1342727 := bstep (se 1 (by rfl) ⟨1007045, by rfl⟩ : syracuseStep 1342727 = 2014091) B2014091
theorem B1342777 : Blo 527800 1342777 := bstep (se 2 (by rfl) ⟨503541, by rfl⟩ : syracuseStep 1342777 = 1007083) B1007083
theorem B26083685 : Blo 527800 26083685 := bstep (se 4 (by rfl) ⟨2445345, by rfl⟩ : syracuseStep 26083685 = 4890691) B4890691
theorem B4031369 : Blo 527800 4031369 := bstep (se 2 (by rfl) ⟨1511763, by rfl⟩ : syracuseStep 4031369 = 3023527) B3023527
theorem B2098217 : Blo 527800 2098217 := bstep (se 2 (by rfl) ⟨786831, by rfl⟩ : syracuseStep 2098217 = 1573663) B1573663
theorem B1345207 : Blo 527800 1345207 := bstep (se 1 (by rfl) ⟨1008905, by rfl⟩ : syracuseStep 1345207 = 2017811) B2017811
theorem B3016763 : Blo 527800 3016763 := bstep (se 1 (by rfl) ⟨2262572, by rfl⟩ : syracuseStep 3016763 = 4525145) B4525145
theorem B1607753 : Blo 527800 1607753 := bstep (se 2 (by rfl) ⟨602907, by rfl⟩ : syracuseStep 1607753 = 1205815) B1205815
theorem B13568147 : Blo 527800 13568147 := bstep (se 1 (by rfl) ⟨10176110, by rfl⟩ : syracuseStep 13568147 = 20352221) B20352221
theorem B25824095 : Blo 527800 25824095 := bstep (se 1 (by rfl) ⟨19368071, by rfl⟩ : syracuseStep 25824095 = 38736143) B38736143
theorem B7244963 : Blo 527800 7244963 := bstep (se 1 (by rfl) ⟨5433722, by rfl⟩ : syracuseStep 7244963 = 10867445) B10867445
theorem B1609067 : Blo 527800 1609067 := bstep (se 1 (by rfl) ⟨1206800, by rfl⟩ : syracuseStep 1609067 = 2413601) B2413601
theorem B1511081 : Blo 527800 1511081 := bstep (se 2 (by rfl) ⟨566655, by rfl⟩ : syracuseStep 1511081 = 1133311) B1133311
theorem B528239 : Blo 527800 528239 := bstep (se 1 (by rfl) ⟨396179, by rfl⟩ : syracuseStep 528239 = 792359) B792359
theorem B528287 : Blo 527800 528287 := bstep (se 1 (by rfl) ⟨396215, by rfl⟩ : syracuseStep 528287 = 792431) B792431
theorem B2854855 : Blo 527800 2854855 := bstep (se 1 (by rfl) ⟨2141141, by rfl⟩ : syracuseStep 2854855 = 4282283) B4282283
theorem B1511399 : Blo 527800 1511399 := bstep (se 1 (by rfl) ⟨1133549, by rfl⟩ : syracuseStep 1511399 = 2267099) B2267099
theorem B1905083 : Blo 527800 1905083 := bstep (se 1 (by rfl) ⟨1428812, by rfl⟩ : syracuseStep 1905083 = 2857625) B2857625
theorem B529023 : Blo 527800 529023 := bstep (se 1 (by rfl) ⟨396767, by rfl⟩ : syracuseStep 529023 = 793535) B793535
theorem B529127 : Blo 527800 529127 := bstep (se 1 (by rfl) ⟨396845, by rfl⟩ : syracuseStep 529127 = 793691) B793691
theorem B2364299 : Blo 527800 2364299 := bstep (se 1 (by rfl) ⟨1773224, by rfl⟩ : syracuseStep 2364299 = 3546449) B3546449
theorem B1512391 : Blo 527800 1512391 := bstep (se 1 (by rfl) ⟨1134293, by rfl⟩ : syracuseStep 1512391 = 2268587) B2268587
theorem B791711 : Blo 527800 791711 := bstep (se 1 (by rfl) ⟨593783, by rfl⟩ : syracuseStep 791711 = 1187567) B1187567
theorem B530023 : Blo 527800 530023 := bstep (se 1 (by rfl) ⟨397517, by rfl⟩ : syracuseStep 530023 = 795035) B795035
theorem B792233 : Blo 527800 792233 := bstep (se 2 (by rfl) ⟨297087, by rfl⟩ : syracuseStep 792233 = 594175) B594175
theorem B792617 : Blo 527800 792617 := bstep (se 2 (by rfl) ⟨297231, by rfl⟩ : syracuseStep 792617 = 594463) B594463
theorem B891047 : Blo 527800 891047 := bstep (se 1 (by rfl) ⟨668285, by rfl⟩ : syracuseStep 891047 = 1336571) B1336571
theorem B530715 : Blo 527800 530715 := bstep (se 1 (by rfl) ⟨398036, by rfl⟩ : syracuseStep 530715 = 796073) B796073
theorem B792953 : Blo 527800 792953 := bstep (se 2 (by rfl) ⟨297357, by rfl⟩ : syracuseStep 792953 = 594715) B594715
theorem B792959 : Blo 527800 792959 := bstep (se 1 (by rfl) ⟨594719, by rfl⟩ : syracuseStep 792959 = 1189439) B1189439
theorem B1513883 : Blo 527800 1513883 := bstep (se 1 (by rfl) ⟨1135412, by rfl⟩ : syracuseStep 1513883 = 2270825) B2270825
theorem B793031 : Blo 527800 793031 := bstep (se 1 (by rfl) ⟨594773, by rfl⟩ : syracuseStep 793031 = 1189547) B1189547
theorem B530911 : Blo 527800 530911 := bstep (se 1 (by rfl) ⟨398183, by rfl⟩ : syracuseStep 530911 = 796367) B796367
theorem B891391 : Blo 527800 891391 := bstep (se 1 (by rfl) ⟨668543, by rfl⟩ : syracuseStep 891391 = 1337087) B1337087
theorem B596479 : Blo 527800 596479 := bstep (se 1 (by rfl) ⟨447359, by rfl⟩ : syracuseStep 596479 = 894719) B894719
theorem B563879 : Blo 527800 563879 := bstep (se 1 (by rfl) ⟨422909, by rfl⟩ : syracuseStep 563879 = 845819) B845819
theorem B596839 : Blo 527800 596839 := bstep (se 1 (by rfl) ⟨447629, by rfl⟩ : syracuseStep 596839 = 895259) B895259
theorem B793511 : Blo 527800 793511 := bstep (se 1 (by rfl) ⟨595133, by rfl⟩ : syracuseStep 793511 = 1190267) B1190267
theorem B793583 : Blo 527800 793583 := bstep (se 1 (by rfl) ⟨595187, by rfl⟩ : syracuseStep 793583 = 1190375) B1190375
theorem B531483 : Blo 527800 531483 := bstep (se 1 (by rfl) ⟨398612, by rfl⟩ : syracuseStep 531483 = 797225) B797225
theorem B793835 : Blo 527800 793835 := bstep (se 1 (by rfl) ⟨595376, by rfl⟩ : syracuseStep 793835 = 1190753) B1190753
theorem B892201 : Blo 527800 892201 := bstep (se 2 (by rfl) ⟨334575, by rfl⟩ : syracuseStep 892201 = 669151) B669151
theorem B794249 : Blo 527800 794249 := bstep (se 2 (by rfl) ⟨297843, by rfl⟩ : syracuseStep 794249 = 595687) B595687
theorem B794267 : Blo 527800 794267 := bstep (se 1 (by rfl) ⟨595700, by rfl⟩ : syracuseStep 794267 = 1191401) B1191401
theorem B8134319 : Blo 527800 8134319 := bstep (se 1 (by rfl) ⟨6100739, by rfl⟩ : syracuseStep 8134319 = 12201479) B12201479
theorem B794303 : Blo 527800 794303 := bstep (se 1 (by rfl) ⟨595727, by rfl⟩ : syracuseStep 794303 = 1191455) B1191455
theorem B1908859 : Blo 527800 1908859 := bstep (se 1 (by rfl) ⟨1431644, by rfl⟩ : syracuseStep 1908859 = 2863289) B2863289
theorem B1189025 : Blo 527800 1189025 := bstep (se 2 (by rfl) ⟨445884, by rfl⟩ : syracuseStep 1189025 = 891769) B891769
theorem B796025 : Blo 527800 796025 := bstep (se 2 (by rfl) ⟨298509, by rfl⟩ : syracuseStep 796025 = 597019) B597019
theorem B20391587 : Blo 527800 20391587 := bstep (se 1 (by rfl) ⟨15293690, by rfl⟩ : syracuseStep 20391587 = 30587381) B30587381
theorem B895151 : Blo 527800 895151 := bstep (se 1 (by rfl) ⟨671363, by rfl⟩ : syracuseStep 895151 = 1342727) B1342727
theorem B1190087 : Blo 527800 1190087 := bstep (se 1 (by rfl) ⟨892565, by rfl⟩ : syracuseStep 1190087 = 1785131) B1785131
theorem B3811661 : Blo 527800 3811661 := bstep (se 3 (by rfl) ⟨714686, by rfl⟩ : syracuseStep 3811661 = 1429373) B1429373
theorem B797339 : Blo 527800 797339 := bstep (se 1 (by rfl) ⟨598004, by rfl⟩ : syracuseStep 797339 = 1196009) B1196009
theorem B797423 : Blo 527800 797423 := bstep (se 1 (by rfl) ⟨598067, by rfl⟩ : syracuseStep 797423 = 1196135) B1196135
theorem B3812123 : Blo 527800 3812123 := bstep (se 1 (by rfl) ⟨2859092, by rfl⟩ : syracuseStep 3812123 = 5718185) B5718185
theorem B3386195 : Blo 527800 3386195 := bstep (se 1 (by rfl) ⟨2539646, by rfl⟩ : syracuseStep 3386195 = 5079293) B5079293
theorem B14461901 : Blo 527800 14461901 := bstep (se 3 (by rfl) ⟨2711606, by rfl⟩ : syracuseStep 14461901 = 5423213) B5423213
theorem B6466823 : Blo 527800 6466823 := bstep (se 1 (by rfl) ⟨4850117, by rfl⟩ : syracuseStep 6466823 = 9700235) B9700235
theorem B9809515 : Blo 527800 9809515 := bstep (se 1 (by rfl) ⟨7357136, by rfl⟩ : syracuseStep 9809515 = 14714273) B14714273
theorem B8565335 : Blo 527800 8565335 := bstep (se 1 (by rfl) ⟨6424001, by rfl⟩ : syracuseStep 8565335 = 12848003) B12848003
theorem B5682113 : Blo 527800 5682113 := bstep (se 2 (by rfl) ⟨2130792, by rfl⟩ : syracuseStep 5682113 = 4261585) B4261585
theorem B2865061 : Blo 527800 2865061 := bstep (se 4 (by rfl) ⟨268599, by rfl⟩ : syracuseStep 2865061 = 537199) B537199
theorem B1783835 : Blo 527800 1783835 := bstep (se 1 (by rfl) ⟨1337876, by rfl⟩ : syracuseStep 1783835 = 2675753) B2675753
theorem B1194011 : Blo 527800 1194011 := bstep (se 1 (by rfl) ⟨895508, by rfl⟩ : syracuseStep 1194011 = 1791017) B1791017
theorem B2013407 : Blo 527800 2013407 := bstep (se 1 (by rfl) ⟨1510055, by rfl⟩ : syracuseStep 2013407 = 3020111) B3020111
theorem B10861523 : Blo 527800 10861523 := bstep (se 1 (by rfl) ⟨8146142, by rfl⟩ : syracuseStep 10861523 = 16292285) B16292285
theorem B1129535 : Blo 527800 1129535 := bstep (se 1 (by rfl) ⟨847151, by rfl⟩ : syracuseStep 1129535 = 1694303) B1694303
theorem B1129783 : Blo 527800 1129783 := bstep (se 1 (by rfl) ⟨847337, by rfl⟩ : syracuseStep 1129783 = 1694675) B1694675
theorem B6766031 : Blo 527800 6766031 := bstep (se 1 (by rfl) ⟨5074523, by rfl⟩ : syracuseStep 6766031 = 10149047) B10149047
theorem B1195487 : Blo 527800 1195487 := bstep (se 1 (by rfl) ⟨896615, by rfl⟩ : syracuseStep 1195487 = 1793231) B1793231
theorem B1359497 : Blo 527800 1359497 := bstep (se 2 (by rfl) ⟨509811, by rfl⟩ : syracuseStep 1359497 = 1019623) B1019623
theorem B7454375 : Blo 527800 7454375 := bstep (se 1 (by rfl) ⟨5590781, by rfl⟩ : syracuseStep 7454375 = 11181563) B11181563
theorem B1195703 : Blo 527800 1195703 := bstep (se 1 (by rfl) ⟨896777, by rfl⟩ : syracuseStep 1195703 = 1793555) B1793555
theorem B1786535 : Blo 527800 1786535 := bstep (se 1 (by rfl) ⟨1339901, by rfl⟩ : syracuseStep 1786535 = 2679803) B2679803
theorem B3884219 : Blo 527800 3884219 := bstep (se 1 (by rfl) ⟨2913164, by rfl⟩ : syracuseStep 3884219 = 5826329) B5826329
theorem B1787291 : Blo 527800 1787291 := bstep (se 1 (by rfl) ⟨1340468, by rfl⟩ : syracuseStep 1787291 = 2680937) B2680937
theorem B2018297 : Blo 527800 2018297 := bstep (se 2 (by rfl) ⟨756861, by rfl⟩ : syracuseStep 2018297 = 1513723) B1513723
theorem B1724147 : Blo 527800 1724147 := bstep (se 1 (by rfl) ⟨1293110, by rfl⟩ : syracuseStep 1724147 = 2586221) B2586221
theorem B1790369 : Blo 527800 1790369 := bstep (se 2 (by rfl) ⟨671388, by rfl⟩ : syracuseStep 1790369 = 1342777) B1342777
theorem B3396343 : Blo 527800 3396343 := bstep (se 1 (by rfl) ⟨2547257, by rfl⟩ : syracuseStep 3396343 = 5094515) B5094515
theorem B29874107 : Blo 527800 29874107 := bstep (se 1 (by rfl) ⟨22405580, by rfl⟩ : syracuseStep 29874107 = 44811161) B44811161
theorem B26139023 : Blo 527800 26139023 := bstep (se 1 (by rfl) ⟨19604267, by rfl⟩ : syracuseStep 26139023 = 39208535) B39208535
theorem B1432055 : Blo 527800 1432055 := bstep (se 1 (by rfl) ⟨1074041, by rfl⟩ : syracuseStep 1432055 = 2148083) B2148083
theorem B14506553 : Blo 527800 14506553 := bstep (se 2 (by rfl) ⟨5439957, by rfl⟩ : syracuseStep 14506553 = 10879915) B10879915
theorem B1792907 : Blo 527800 1792907 := bstep (se 1 (by rfl) ⟨1344680, by rfl⟩ : syracuseStep 1792907 = 2689361) B2689361
theorem B4840481 : Blo 527800 4840481 := bstep (se 2 (by rfl) ⟨1815180, by rfl⟩ : syracuseStep 4840481 = 3630361) B3630361
theorem B1269017 : Blo 527800 1269017 := bstep (se 2 (by rfl) ⟨475881, by rfl⟩ : syracuseStep 1269017 = 951763) B951763
theorem B6970835 : Blo 527800 6970835 := bstep (se 1 (by rfl) ⟨5228126, by rfl⟩ : syracuseStep 6970835 = 10456253) B10456253
theorem B6807037 : Blo 527800 6807037 := bstep (se 3 (by rfl) ⟨1276319, by rfl⟩ : syracuseStep 6807037 = 2552639) B2552639
theorem B13459655 : Blo 527800 13459655 := bstep (se 1 (by rfl) ⟨10094741, by rfl⟩ : syracuseStep 13459655 = 20189483) B20189483
theorem B1794527 : Blo 527800 1794527 := bstep (se 1 (by rfl) ⟨1345895, by rfl⟩ : syracuseStep 1794527 = 2691791) B2691791
theorem B1074359 : Blo 527800 1074359 := bstep (se 1 (by rfl) ⟨805769, by rfl⟩ : syracuseStep 1074359 = 1611539) B1611539
theorem B1697071 : Blo 527800 1697071 := bstep (se 1 (by rfl) ⟨1272803, by rfl⟩ : syracuseStep 1697071 = 2545607) B2545607
theorem B1336783 : Blo 527800 1336783 := bstep (se 1 (by rfl) ⟨1002587, by rfl⟩ : syracuseStep 1336783 = 2005175) B2005175
theorem B8153783 : Blo 527800 8153783 := bstep (se 1 (by rfl) ⟨6115337, by rfl⟩ : syracuseStep 8153783 = 12230675) B12230675
theorem B1534747 : Blo 527800 1534747 := bstep (se 1 (by rfl) ⟨1151060, by rfl⟩ : syracuseStep 1534747 = 2302121) B2302121
theorem B13986857 : Blo 527800 13986857 := bstep (se 2 (by rfl) ⟨5245071, by rfl⟩ : syracuseStep 13986857 = 10490143) B10490143
theorem B2682233 : Blo 527800 2682233 := bstep (se 2 (by rfl) ⟨1005837, by rfl⟩ : syracuseStep 2682233 = 2011675) B2011675
theorem B10284731 : Blo 527800 10284731 := bstep (se 1 (by rfl) ⟨7713548, by rfl⟩ : syracuseStep 10284731 = 15427097) B15427097
theorem B1503335 : Blo 527800 1503335 := bstep (se 1 (by rfl) ⟨1127501, by rfl⟩ : syracuseStep 1503335 = 2255003) B2255003
theorem B1339679 : Blo 527800 1339679 := bstep (se 1 (by rfl) ⟨1004759, by rfl⟩ : syracuseStep 1339679 = 2009519) B2009519
theorem B8614775 : Blo 527800 8614775 := bstep (se 1 (by rfl) ⟨6461081, by rfl⟩ : syracuseStep 8614775 = 12922163) B12922163
theorem B1340975 : Blo 527800 1340975 := bstep (se 1 (by rfl) ⟨1005731, by rfl⟩ : syracuseStep 1340975 = 2011463) B2011463
theorem B1701479 : Blo 527800 1701479 := bstep (se 1 (by rfl) ⟨1276109, by rfl⟩ : syracuseStep 1701479 = 2552219) B2552219
theorem B2684663 : Blo 527800 2684663 := bstep (se 1 (by rfl) ⟨2013497, by rfl⟩ : syracuseStep 2684663 = 4026995) B4026995
theorem B1505135 : Blo 527800 1505135 := bstep (se 1 (by rfl) ⟨1128851, by rfl⟩ : syracuseStep 1505135 = 2257703) B2257703
theorem B752095 : Blo 527800 752095 := bstep (se 1 (by rfl) ⟨564071, by rfl⟩ : syracuseStep 752095 = 1128143) B1128143
theorem B4028939 : Blo 527800 4028939 := bstep (se 1 (by rfl) ⟨3021704, by rfl⟩ : syracuseStep 4028939 = 6043409) B6043409
theorem B2259839 : Blo 527800 2259839 := bstep (se 1 (by rfl) ⟨1694879, by rfl⟩ : syracuseStep 2259839 = 3389759) B3389759
theorem B3013847 : Blo 527800 3013847 := bstep (se 1 (by rfl) ⟨2260385, by rfl⟩ : syracuseStep 3013847 = 4520771) B4520771
theorem B2687579 : Blo 527800 2687579 := bstep (se 1 (by rfl) ⟨2015684, by rfl⟩ : syracuseStep 2687579 = 4031369) B4031369
theorem B2589479 : Blo 527800 2589479 := bstep (se 1 (by rfl) ⟨1942109, by rfl⟩ : syracuseStep 2589479 = 3884219) B3884219
theorem B9045431 : Blo 527800 9045431 := bstep (se 1 (by rfl) ⟨6784073, by rfl⟩ : syracuseStep 9045431 = 13568147) B13568147
theorem B2262761 : Blo 527800 2262761 := bstep (se 2 (by rfl) ⟨848535, by rfl⟩ : syracuseStep 2262761 = 1697071) B1697071
theorem B1345531 : Blo 527800 1345531 := bstep (se 1 (by rfl) ⟨1009148, by rfl⟩ : syracuseStep 1345531 = 2018297) B2018297
theorem B1149431 : Blo 527800 1149431 := bstep (se 1 (by rfl) ⟨862073, by rfl⟩ : syracuseStep 1149431 = 1724147) B1724147
theorem B1576199 : Blo 527800 1576199 := bstep (se 1 (by rfl) ⟨1182149, by rfl⟩ : syracuseStep 1576199 = 2364299) B2364299
theorem B527807 : Blo 527800 527807 := bstep (se 1 (by rfl) ⟨395855, by rfl⟩ : syracuseStep 527807 = 791711) B791711
theorem B528155 : Blo 527800 528155 := bstep (se 1 (by rfl) ⟨396116, by rfl⟩ : syracuseStep 528155 = 792233) B792233
theorem B528411 : Blo 527800 528411 := bstep (se 1 (by rfl) ⟨396308, by rfl⟩ : syracuseStep 528411 = 792617) B792617
theorem B594031 : Blo 527800 594031 := bstep (se 1 (by rfl) ⟨445523, by rfl⟩ : syracuseStep 594031 = 891047) B891047
theorem B528635 : Blo 527800 528635 := bstep (se 1 (by rfl) ⟨396476, by rfl⟩ : syracuseStep 528635 = 792953) B792953
theorem B528639 : Blo 527800 528639 := bstep (se 1 (by rfl) ⟨396479, by rfl⟩ : syracuseStep 528639 = 792959) B792959
theorem B528687 : Blo 527800 528687 := bstep (se 1 (by rfl) ⟨396515, by rfl⟩ : syracuseStep 528687 = 793031) B793031
theorem B954703 : Blo 527800 954703 := bstep (se 1 (by rfl) ⟨716027, by rfl⟩ : syracuseStep 954703 = 1432055) B1432055
theorem B9671035 : Blo 527800 9671035 := bstep (se 1 (by rfl) ⟨7253276, by rfl⟩ : syracuseStep 9671035 = 14506553) B14506553
theorem B529007 : Blo 527800 529007 := bstep (se 1 (by rfl) ⟨396755, by rfl⟩ : syracuseStep 529007 = 793511) B793511
theorem B529055 : Blo 527800 529055 := bstep (se 1 (by rfl) ⟨396791, by rfl⟩ : syracuseStep 529055 = 793583) B793583
theorem B529223 : Blo 527800 529223 := bstep (se 1 (by rfl) ⟨396917, by rfl⟩ : syracuseStep 529223 = 793835) B793835
theorem B529499 : Blo 527800 529499 := bstep (se 1 (by rfl) ⟨397124, by rfl⟩ : syracuseStep 529499 = 794249) B794249
theorem B529511 : Blo 527800 529511 := bstep (se 1 (by rfl) ⟨397133, by rfl⟩ : syracuseStep 529511 = 794267) B794267
theorem B529535 : Blo 527800 529535 := bstep (se 1 (by rfl) ⟨397151, by rfl⟩ : syracuseStep 529535 = 794303) B794303
theorem B79664285 : Blo 527800 79664285 := bstep (se 3 (by rfl) ⟨14937053, by rfl⟩ : syracuseStep 79664285 = 29874107) B29874107
theorem B3806473 : Blo 527800 3806473 := bstep (se 2 (by rfl) ⟨1427427, by rfl⟩ : syracuseStep 3806473 = 2854855) B2854855
theorem B792683 : Blo 527800 792683 := bstep (se 1 (by rfl) ⟨594512, by rfl⟩ : syracuseStep 792683 = 1189025) B1189025
theorem B530683 : Blo 527800 530683 := bstep (se 1 (by rfl) ⟨398012, by rfl⟩ : syracuseStep 530683 = 796025) B796025
theorem B4528457 : Blo 527800 4528457 := bstep (se 2 (by rfl) ⟨1698171, by rfl⟩ : syracuseStep 4528457 = 3396343) B3396343
theorem B596767 : Blo 527800 596767 := bstep (se 1 (by rfl) ⟨447575, by rfl⟩ : syracuseStep 596767 = 895151) B895151
theorem B793391 : Blo 527800 793391 := bstep (se 1 (by rfl) ⟨595043, by rfl⟩ : syracuseStep 793391 = 1190087) B1190087
theorem B531559 : Blo 527800 531559 := bstep (se 1 (by rfl) ⟨398669, by rfl⟩ : syracuseStep 531559 = 797339) B797339
theorem B531615 : Blo 527800 531615 := bstep (se 1 (by rfl) ⟨398711, by rfl⟩ : syracuseStep 531615 = 797423) B797423
theorem B9641267 : Blo 527800 9641267 := bstep (se 1 (by rfl) ⟨7230950, by rfl⟩ : syracuseStep 9641267 = 14461901) B14461901
theorem B6856487 : Blo 527800 6856487 := bstep (se 1 (by rfl) ⟨5142365, by rfl⟩ : syracuseStep 6856487 = 10284731) B10284731
theorem B893119 : Blo 527800 893119 := bstep (se 1 (by rfl) ⟨669839, by rfl⟩ : syracuseStep 893119 = 1339679) B1339679
theorem B5710223 : Blo 527800 5710223 := bstep (se 1 (by rfl) ⟨4282667, by rfl⟩ : syracuseStep 5710223 = 8565335) B8565335
theorem B5743183 : Blo 527800 5743183 := bstep (se 1 (by rfl) ⟨4307387, by rfl⟩ : syracuseStep 5743183 = 8614775) B8614775
theorem B1188521 : Blo 527800 1188521 := bstep (se 2 (by rfl) ⟨445695, by rfl⟩ : syracuseStep 1188521 = 891391) B891391
theorem B795305 : Blo 527800 795305 := bstep (se 2 (by rfl) ⟨298239, by rfl⟩ : syracuseStep 795305 = 596479) B596479
theorem B893983 : Blo 527800 893983 := bstep (se 1 (by rfl) ⟨670487, by rfl⟩ : syracuseStep 893983 = 1340975) B1340975
theorem B795785 : Blo 527800 795785 := bstep (se 2 (by rfl) ⟨298419, by rfl⟩ : syracuseStep 795785 = 596839) B596839
theorem B1189223 : Blo 527800 1189223 := bstep (se 1 (by rfl) ⟨891917, by rfl⟩ : syracuseStep 1189223 = 1783835) B1783835
theorem B796007 : Blo 527800 796007 := bstep (se 1 (by rfl) ⟨597005, by rfl⟩ : syracuseStep 796007 = 1194011) B1194011
theorem B1189601 : Blo 527800 1189601 := bstep (se 2 (by rfl) ⟨446100, by rfl⟩ : syracuseStep 1189601 = 892201) B892201
theorem B2009231 : Blo 527800 2009231 := bstep (se 1 (by rfl) ⟨1506923, by rfl⟩ : syracuseStep 2009231 = 3013847) B3013847
theorem B796991 : Blo 527800 796991 := bstep (se 1 (by rfl) ⟨597743, by rfl⟩ : syracuseStep 796991 = 1195487) B1195487
theorem B797135 : Blo 527800 797135 := bstep (se 1 (by rfl) ⟨597851, by rfl⟩ : syracuseStep 797135 = 1195703) B1195703
theorem B1191023 : Blo 527800 1191023 := bstep (se 1 (by rfl) ⟨893267, by rfl⟩ : syracuseStep 1191023 = 1786535) B1786535
theorem B35892413 : Blo 527800 35892413 := bstep (se 3 (by rfl) ⟨6729827, by rfl⟩ : syracuseStep 35892413 = 13459655) B13459655
theorem B1191527 : Blo 527800 1191527 := bstep (se 1 (by rfl) ⟨893645, by rfl⟩ : syracuseStep 1191527 = 1787291) B1787291
theorem B2011175 : Blo 527800 2011175 := bstep (se 1 (by rfl) ⟨1508381, by rfl⟩ : syracuseStep 2011175 = 3016763) B3016763
theorem B17216063 : Blo 527800 17216063 := bstep (se 1 (by rfl) ⟨12912047, by rfl⟩ : syracuseStep 17216063 = 25824095) B25824095
theorem B1782377 : Blo 527800 1782377 := bstep (se 2 (by rfl) ⟨668391, by rfl⟩ : syracuseStep 1782377 = 1336783) B1336783
theorem B4829975 : Blo 527800 4829975 := bstep (se 1 (by rfl) ⟨3622481, by rfl⟩ : syracuseStep 4829975 = 7244963) B7244963
theorem B1193579 : Blo 527800 1193579 := bstep (se 1 (by rfl) ⟨895184, by rfl⟩ : syracuseStep 1193579 = 1790369) B1790369
theorem B2046329 : Blo 527800 2046329 := bstep (se 2 (by rfl) ⟨767373, by rfl⟩ : syracuseStep 2046329 = 1534747) B1534747
theorem B1195271 : Blo 527800 1195271 := bstep (se 1 (by rfl) ⟨896453, by rfl⟩ : syracuseStep 1195271 = 1792907) B1792907
theorem B3226987 : Blo 527800 3226987 := bstep (se 1 (by rfl) ⟨2420240, by rfl⟩ : syracuseStep 3226987 = 4840481) B4840481
theorem B5422879 : Blo 527800 5422879 := bstep (se 1 (by rfl) ⟨4067159, by rfl⟩ : syracuseStep 5422879 = 8134319) B8134319
theorem B1196351 : Blo 527800 1196351 := bstep (se 1 (by rfl) ⟨897263, by rfl⟩ : syracuseStep 1196351 = 1794527) B1794527
theorem B2016521 : Blo 527800 2016521 := bstep (se 2 (by rfl) ⟨756195, by rfl⟩ : syracuseStep 2016521 = 1512391) B1512391
theorem B2541107 : Blo 527800 2541107 := bstep (se 1 (by rfl) ⟨1905830, by rfl⟩ : syracuseStep 2541107 = 3811661) B3811661
theorem B2541415 : Blo 527800 2541415 := bstep (se 1 (by rfl) ⟨1906061, by rfl⟩ : syracuseStep 2541415 = 3812123) B3812123
theorem B9324571 : Blo 527800 9324571 := bstep (se 1 (by rfl) ⟨6993428, by rfl⟩ : syracuseStep 9324571 = 13986857) B13986857
theorem B4311215 : Blo 527800 4311215 := bstep (se 1 (by rfl) ⟨3233411, by rfl⟩ : syracuseStep 4311215 = 6466823) B6466823
theorem B1788155 : Blo 527800 1788155 := bstep (se 1 (by rfl) ⟨1341116, by rfl⟩ : syracuseStep 1788155 = 2682233) B2682233
theorem B3820081 : Blo 527800 3820081 := bstep (se 2 (by rfl) ⟨1432530, by rfl⟩ : syracuseStep 3820081 = 2865061) B2865061
theorem B1002223 : Blo 527800 1002223 := bstep (se 1 (by rfl) ⟨751667, by rfl⟩ : syracuseStep 1002223 = 1503335) B1503335
theorem B52317413 : Blo 527800 52317413 := bstep (se 4 (by rfl) ⟨4904757, by rfl⟩ : syracuseStep 52317413 = 9809515) B9809515
theorem B1002793 : Blo 527800 1002793 := bstep (se 2 (by rfl) ⟨376047, by rfl⟩ : syracuseStep 1002793 = 752095) B752095
theorem B3788075 : Blo 527800 3788075 := bstep (se 1 (by rfl) ⟨2841056, by rfl⟩ : syracuseStep 3788075 = 5682113) B5682113
theorem B1134319 : Blo 527800 1134319 := bstep (se 1 (by rfl) ⟨850739, by rfl⟩ : syracuseStep 1134319 = 1701479) B1701479
theorem B1789775 : Blo 527800 1789775 := bstep (se 1 (by rfl) ⟨1342331, by rfl⟩ : syracuseStep 1789775 = 2684663) B2684663
theorem B1003423 : Blo 527800 1003423 := bstep (se 1 (by rfl) ⟨752567, by rfl⟩ : syracuseStep 1003423 = 1505135) B1505135
theorem B3625325 : Blo 527800 3625325 := bstep (se 3 (by rfl) ⟨679748, by rfl⟩ : syracuseStep 3625325 = 1359497) B1359497
theorem B4510687 : Blo 527800 4510687 := bstep (se 1 (by rfl) ⟨3383015, by rfl⟩ : syracuseStep 4510687 = 6766031) B6766031
theorem B4969583 : Blo 527800 4969583 := bstep (se 1 (by rfl) ⟨3727187, by rfl⟩ : syracuseStep 4969583 = 7454375) B7454375
theorem B2545145 : Blo 527800 2545145 := bstep (se 2 (by rfl) ⟨954429, by rfl⟩ : syracuseStep 2545145 = 1908859) B1908859
theorem B1398811 : Blo 527800 1398811 := bstep (se 1 (by rfl) ⟨1049108, by rfl⟩ : syracuseStep 1398811 = 2098217) B2098217
theorem B69556493 : Blo 527800 69556493 := bstep (se 3 (by rfl) ⟨13041842, by rfl⟩ : syracuseStep 69556493 = 26083685) B26083685
theorem B1071835 : Blo 527800 1071835 := bstep (se 1 (by rfl) ⟨803876, by rfl⟩ : syracuseStep 1071835 = 1607753) B1607753
theorem B1072711 : Blo 527800 1072711 := bstep (se 1 (by rfl) ⟨804533, by rfl⟩ : syracuseStep 1072711 = 1609067) B1609067
theorem B1793609 : Blo 527800 1793609 := bstep (se 2 (by rfl) ⟨672603, by rfl⟩ : syracuseStep 1793609 = 1345207) B1345207
theorem B1007387 : Blo 527800 1007387 := bstep (se 1 (by rfl) ⟨755540, by rfl⟩ : syracuseStep 1007387 = 1511081) B1511081
theorem B1270055 : Blo 527800 1270055 := bstep (se 1 (by rfl) ⟨952541, by rfl⟩ : syracuseStep 1270055 = 1905083) B1905083
theorem B17426015 : Blo 527800 17426015 := bstep (se 1 (by rfl) ⟨13069511, by rfl⟩ : syracuseStep 17426015 = 26139023) B26139023
theorem B1009255 : Blo 527800 1009255 := bstep (se 1 (by rfl) ⟨756941, by rfl⟩ : syracuseStep 1009255 = 1513883) B1513883
theorem B846011 : Blo 527800 846011 := bstep (se 1 (by rfl) ⟨634508, by rfl⟩ : syracuseStep 846011 = 1269017) B1269017
theorem B4647223 : Blo 527800 4647223 := bstep (se 1 (by rfl) ⟨3485417, by rfl⟩ : syracuseStep 4647223 = 6970835) B6970835
theorem B716239 : Blo 527800 716239 := bstep (se 1 (by rfl) ⟨537179, by rfl⟩ : syracuseStep 716239 = 1074359) B1074359
theorem B13594391 : Blo 527800 13594391 := bstep (se 1 (by rfl) ⟨10195793, by rfl⟩ : syracuseStep 13594391 = 20391587) B20391587
theorem B1503677 : Blo 527800 1503677 := bstep (se 3 (by rfl) ⟨281939, by rfl⟩ : syracuseStep 1503677 = 563879) B563879
theorem B5435855 : Blo 527800 5435855 := bstep (se 1 (by rfl) ⟨4076891, by rfl⟩ : syracuseStep 5435855 = 8153783) B8153783
theorem B2257463 : Blo 527800 2257463 := bstep (se 1 (by rfl) ⟨1693097, by rfl⟩ : syracuseStep 2257463 = 3386195) B3386195
theorem B1342271 : Blo 527800 1342271 := bstep (se 1 (by rfl) ⟨1006703, by rfl⟩ : syracuseStep 1342271 = 2013407) B2013407
theorem B2685959 : Blo 527800 2685959 := bstep (se 1 (by rfl) ⟨2014469, by rfl⟩ : syracuseStep 2685959 = 4028939) B4028939
theorem B1506377 : Blo 527800 1506377 := bstep (se 2 (by rfl) ⟨564891, by rfl⟩ : syracuseStep 1506377 = 1129783) B1129783
theorem B1506559 : Blo 527800 1506559 := bstep (se 1 (by rfl) ⟨1129919, by rfl⟩ : syracuseStep 1506559 = 2259839) B2259839
theorem B7241015 : Blo 527800 7241015 := bstep (se 1 (by rfl) ⟨5430761, by rfl⟩ : syracuseStep 7241015 = 10861523) B10861523
theorem B9076049 : Blo 527800 9076049 := bstep (se 2 (by rfl) ⟨3403518, by rfl⟩ : syracuseStep 9076049 = 6807037) B6807037
theorem B753023 : Blo 527800 753023 := bstep (se 1 (by rfl) ⟨564767, by rfl⟩ : syracuseStep 753023 = 1129535) B1129535
theorem B4030397 : Blo 527800 4030397 := bstep (se 3 (by rfl) ⟨755699, by rfl⟩ : syracuseStep 4030397 = 1511399) B1511399
theorem B1344347 : Blo 527800 1344347 := bstep (se 1 (by rfl) ⟨1008260, by rfl⟩ : syracuseStep 1344347 = 2016521) B2016521
theorem B6030287 : Blo 527800 6030287 := bstep (se 1 (by rfl) ⟨4522715, by rfl⟩ : syracuseStep 6030287 = 9045431) B9045431
theorem B1508507 : Blo 527800 1508507 := bstep (se 1 (by rfl) ⟨1131380, by rfl⟩ : syracuseStep 1508507 = 2262761) B2262761
theorem B1345673 : Blo 527800 1345673 := bstep (se 2 (by rfl) ⟨504627, by rfl⟩ : syracuseStep 1345673 = 1009255) B1009255
theorem B2525383 : Blo 527800 2525383 := bstep (se 1 (by rfl) ⟨1894037, by rfl⟩ : syracuseStep 2525383 = 3788075) B3788075
theorem B3313055 : Blo 527800 3313055 := bstep (se 1 (by rfl) ⟨2484791, by rfl⟩ : syracuseStep 3313055 = 4969583) B4969583
theorem B528455 : Blo 527800 528455 := bstep (se 1 (by rfl) ⟨396341, by rfl⟩ : syracuseStep 528455 = 792683) B792683
theorem B3018971 : Blo 527800 3018971 := bstep (se 1 (by rfl) ⟨2264228, by rfl⟩ : syracuseStep 3018971 = 4528457) B4528457
theorem B528927 : Blo 527800 528927 := bstep (se 1 (by rfl) ⟨396695, by rfl⟩ : syracuseStep 528927 = 793391) B793391
theorem B954985 : Blo 527800 954985 := bstep (se 2 (by rfl) ⟨358119, by rfl⟩ : syracuseStep 954985 = 716239) B716239
theorem B6427511 : Blo 527800 6427511 := bstep (se 1 (by rfl) ⟨4820633, by rfl⟩ : syracuseStep 6427511 = 9641267) B9641267
theorem B1512425 : Blo 527800 1512425 := bstep (se 2 (by rfl) ⟨567159, by rfl⟩ : syracuseStep 1512425 = 1134319) B1134319
theorem B792041 : Blo 527800 792041 := bstep (se 2 (by rfl) ⟨297015, by rfl⟩ : syracuseStep 792041 = 594031) B594031
theorem B792347 : Blo 527800 792347 := bstep (se 1 (by rfl) ⟨594260, by rfl⟩ : syracuseStep 792347 = 1188521) B1188521
theorem B530203 : Blo 527800 530203 := bstep (se 1 (by rfl) ⟨397652, by rfl⟩ : syracuseStep 530203 = 795305) B795305
theorem B530523 : Blo 527800 530523 := bstep (se 1 (by rfl) ⟨397892, by rfl⟩ : syracuseStep 530523 = 795785) B795785
theorem B792815 : Blo 527800 792815 := bstep (se 1 (by rfl) ⟨594611, by rfl⟩ : syracuseStep 792815 = 1189223) B1189223
theorem B530671 : Blo 527800 530671 := bstep (se 1 (by rfl) ⟨398003, by rfl⟩ : syracuseStep 530671 = 796007) B796007
theorem B793067 : Blo 527800 793067 := bstep (se 1 (by rfl) ⟨594800, by rfl⟩ : syracuseStep 793067 = 1189601) B1189601
theorem B564007 : Blo 527800 564007 := bstep (se 1 (by rfl) ⟨423005, by rfl⟩ : syracuseStep 564007 = 846011) B846011
theorem B531327 : Blo 527800 531327 := bstep (se 1 (by rfl) ⟨398495, by rfl⟩ : syracuseStep 531327 = 796991) B796991
theorem B531423 : Blo 527800 531423 := bstep (se 1 (by rfl) ⟨398567, by rfl⟩ : syracuseStep 531423 = 797135) B797135
theorem B794015 : Blo 527800 794015 := bstep (se 1 (by rfl) ⟨595511, by rfl⟩ : syracuseStep 794015 = 1191023) B1191023
theorem B23928275 : Blo 527800 23928275 := bstep (se 1 (by rfl) ⟨17946206, by rfl⟩ : syracuseStep 23928275 = 35892413) B35892413
theorem B794351 : Blo 527800 794351 := bstep (se 1 (by rfl) ⟨595763, by rfl⟩ : syracuseStep 794351 = 1191527) B1191527
theorem B11477375 : Blo 527800 11477375 := bstep (se 1 (by rfl) ⟨8608031, by rfl⟩ : syracuseStep 11477375 = 17216063) B17216063
theorem B1188251 : Blo 527800 1188251 := bstep (se 1 (by rfl) ⟨891188, by rfl⟩ : syracuseStep 1188251 = 1782377) B1782377
theorem B3219983 : Blo 527800 3219983 := bstep (se 1 (by rfl) ⟨2414987, by rfl⟩ : syracuseStep 3219983 = 4829975) B4829975
theorem B4203197 : Blo 527800 4203197 := bstep (se 3 (by rfl) ⟨788099, by rfl⟩ : syracuseStep 4203197 = 1576199) B1576199
theorem B19309373 : Blo 527800 19309373 := bstep (se 3 (by rfl) ⟨3620507, by rfl⟩ : syracuseStep 19309373 = 7241015) B7241015
theorem B2008061 : Blo 527800 2008061 := bstep (se 3 (by rfl) ⟨376511, by rfl⟩ : syracuseStep 2008061 = 753023) B753023
theorem B795689 : Blo 527800 795689 := bstep (se 2 (by rfl) ⟨298383, by rfl⟩ : syracuseStep 795689 = 596767) B596767
theorem B795719 : Blo 527800 795719 := bstep (se 1 (by rfl) ⟨596789, by rfl⟩ : syracuseStep 795719 = 1193579) B1193579
theorem B2008745 : Blo 527800 2008745 := bstep (se 2 (by rfl) ⟨753279, by rfl⟩ : syracuseStep 2008745 = 1506559) B1506559
theorem B4302649 : Blo 527800 4302649 := bstep (se 2 (by rfl) ⟨1613493, by rfl⟩ : syracuseStep 4302649 = 3226987) B3226987
theorem B894847 : Blo 527800 894847 := bstep (se 1 (by rfl) ⟨671135, by rfl⟩ : syracuseStep 894847 = 1342271) B1342271
theorem B796847 : Blo 527800 796847 := bstep (se 1 (by rfl) ⟨597635, by rfl⟩ : syracuseStep 796847 = 1195271) B1195271
theorem B797567 : Blo 527800 797567 := bstep (se 1 (by rfl) ⟨598175, by rfl⟩ : syracuseStep 797567 = 1196351) B1196351
theorem B1190825 : Blo 527800 1190825 := bstep (se 2 (by rfl) ⟨446559, by rfl⟩ : syracuseStep 1190825 = 893119) B893119
theorem B1191977 : Blo 527800 1191977 := bstep (se 2 (by rfl) ⟨446991, by rfl⟩ : syracuseStep 1191977 = 893983) B893983
theorem B1192103 : Blo 527800 1192103 := bstep (se 1 (by rfl) ⟨894077, by rfl⟩ : syracuseStep 1192103 = 1788155) B1788155
theorem B24785189 : Blo 527800 24785189 := bstep (se 4 (by rfl) ⟨2323611, by rfl⟩ : syracuseStep 24785189 = 4647223) B4647223
theorem B34878275 : Blo 527800 34878275 := bstep (se 1 (by rfl) ⟨26158706, by rfl⟩ : syracuseStep 34878275 = 52317413) B52317413
theorem B3388553 : Blo 527800 3388553 := bstep (se 2 (by rfl) ⟨1270707, by rfl⟩ : syracuseStep 3388553 = 2541415) B2541415
theorem B1193183 : Blo 527800 1193183 := bstep (se 1 (by rfl) ⟨894887, by rfl⟩ : syracuseStep 1193183 = 1789775) B1789775
theorem B12432761 : Blo 527800 12432761 := bstep (se 2 (by rfl) ⟨4662285, by rfl⟩ : syracuseStep 12432761 = 9324571) B9324571
theorem B5093441 : Blo 527800 5093441 := bstep (se 2 (by rfl) ⟨1910040, by rfl⟩ : syracuseStep 5093441 = 3820081) B3820081
theorem B5716453 : Blo 527800 5716453 := bstep (se 4 (by rfl) ⟨535917, by rfl⟩ : syracuseStep 5716453 = 1071835) B1071835
theorem B1195739 : Blo 527800 1195739 := bstep (se 1 (by rfl) ⟨896804, by rfl⟩ : syracuseStep 1195739 = 1793609) B1793609
theorem B671591 : Blo 527800 671591 := bstep (se 1 (by rfl) ⟨503693, by rfl⟩ : syracuseStep 671591 = 1007387) B1007387
theorem B4570991 : Blo 527800 4570991 := bstep (se 1 (by rfl) ⟨3428243, by rfl⟩ : syracuseStep 4570991 = 6856487) B6856487
theorem B12894713 : Blo 527800 12894713 := bstep (se 2 (by rfl) ⟨4835517, by rfl⟩ : syracuseStep 12894713 = 9671035) B9671035
theorem B185483981 : Blo 527800 185483981 := bstep (se 3 (by rfl) ⟨34778246, by rfl⟩ : syracuseStep 185483981 = 69556493) B69556493
theorem B11617343 : Blo 527800 11617343 := bstep (se 1 (by rfl) ⟨8713007, by rfl⟩ : syracuseStep 11617343 = 17426015) B17426015
theorem B6014249 : Blo 527800 6014249 := bstep (se 2 (by rfl) ⟨2255343, by rfl⟩ : syracuseStep 6014249 = 4510687) B4510687
theorem B3065149 : Blo 527800 3065149 := bstep (se 3 (by rfl) ⟨574715, by rfl⟩ : syracuseStep 3065149 = 1149431) B1149431
theorem B9062927 : Blo 527800 9062927 := bstep (se 1 (by rfl) ⟨6797195, by rfl⟩ : syracuseStep 9062927 = 13594391) B13594391
theorem B1002451 : Blo 527800 1002451 := bstep (se 1 (by rfl) ⟨751838, by rfl⟩ : syracuseStep 1002451 = 1503677) B1503677
theorem B3623903 : Blo 527800 3623903 := bstep (se 1 (by rfl) ⟨2717927, by rfl⟩ : syracuseStep 3623903 = 5435855) B5435855
theorem B1364219 : Blo 527800 1364219 := bstep (se 1 (by rfl) ⟨1023164, by rfl⟩ : syracuseStep 1364219 = 2046329) B2046329
theorem B1790639 : Blo 527800 1790639 := bstep (se 1 (by rfl) ⟨1342979, by rfl⟩ : syracuseStep 1790639 = 2685959) B2685959
theorem B1004251 : Blo 527800 1004251 := bstep (se 1 (by rfl) ⟨753188, by rfl⟩ : syracuseStep 1004251 = 1506377) B1506377
theorem B1430281 : Blo 527800 1430281 := bstep (se 2 (by rfl) ⟨536355, by rfl⟩ : syracuseStep 1430281 = 1072711) B1072711
theorem B6050699 : Blo 527800 6050699 := bstep (se 1 (by rfl) ⟨4538024, by rfl⟩ : syracuseStep 6050699 = 9076049) B9076049
theorem B7230505 : Blo 527800 7230505 := bstep (se 2 (by rfl) ⟨2711439, by rfl⟩ : syracuseStep 7230505 = 5422879) B5422879
theorem B1791719 : Blo 527800 1791719 := bstep (se 1 (by rfl) ⟨1343789, by rfl⟩ : syracuseStep 1791719 = 2687579) B2687579
theorem B1726319 : Blo 527800 1726319 := bstep (se 1 (by rfl) ⟨1294739, by rfl⟩ : syracuseStep 1726319 = 2589479) B2589479
theorem B7657577 : Blo 527800 7657577 := bstep (se 2 (by rfl) ⟨2871591, by rfl⟩ : syracuseStep 7657577 = 5743183) B5743183
theorem B1694071 : Blo 527800 1694071 := bstep (se 1 (by rfl) ⟨1270553, by rfl⟩ : syracuseStep 1694071 = 2541107) B2541107
theorem B15227261 : Blo 527800 15227261 := bstep (se 3 (by rfl) ⟨2855111, by rfl⟩ : syracuseStep 15227261 = 5710223) B5710223
theorem B2874143 : Blo 527800 2874143 := bstep (se 1 (by rfl) ⟨2155607, by rfl⟩ : syracuseStep 2874143 = 4311215) B4311215
theorem B1794041 : Blo 527800 1794041 := bstep (se 2 (by rfl) ⟨672765, by rfl⟩ : syracuseStep 1794041 = 1345531) B1345531
theorem B2416883 : Blo 527800 2416883 := bstep (se 1 (by rfl) ⟨1812662, by rfl⟩ : syracuseStep 2416883 = 3625325) B3625325
theorem B53109523 : Blo 527800 53109523 := bstep (se 1 (by rfl) ⟨39832142, by rfl⟩ : syracuseStep 53109523 = 79664285) B79664285
theorem B1336297 : Blo 527800 1336297 := bstep (se 2 (by rfl) ⟨501111, by rfl⟩ : syracuseStep 1336297 = 1002223) B1002223
theorem B1696763 : Blo 527800 1696763 := bstep (se 1 (by rfl) ⟨1272572, by rfl⟩ : syracuseStep 1696763 = 2545145) B2545145
theorem B1337057 : Blo 527800 1337057 := bstep (se 2 (by rfl) ⟨501396, by rfl⟩ : syracuseStep 1337057 = 1002793) B1002793
theorem B1337897 : Blo 527800 1337897 := bstep (se 2 (by rfl) ⟨501711, by rfl⟩ : syracuseStep 1337897 = 1003423) B1003423
theorem B846703 : Blo 527800 846703 := bstep (se 1 (by rfl) ⟨635027, by rfl⟩ : syracuseStep 846703 = 1270055) B1270055
theorem B1272937 : Blo 527800 1272937 := bstep (se 2 (by rfl) ⟨477351, by rfl⟩ : syracuseStep 1272937 = 954703) B954703
theorem B1339487 : Blo 527800 1339487 := bstep (se 1 (by rfl) ⟨1004615, by rfl⟩ : syracuseStep 1339487 = 2009231) B2009231
theorem B5075297 : Blo 527800 5075297 := bstep (se 2 (by rfl) ⟨1903236, by rfl⟩ : syracuseStep 5075297 = 3806473) B3806473
theorem B1340783 : Blo 527800 1340783 := bstep (se 1 (by rfl) ⟨1005587, by rfl⟩ : syracuseStep 1340783 = 2011175) B2011175
theorem B1865081 : Blo 527800 1865081 := bstep (se 2 (by rfl) ⟨699405, by rfl⟩ : syracuseStep 1865081 = 1398811) B1398811
theorem B1504975 : Blo 527800 1504975 := bstep (se 1 (by rfl) ⟨1128731, by rfl⟩ : syracuseStep 1504975 = 2257463) B2257463
theorem B2686931 : Blo 527800 2686931 := bstep (se 1 (by rfl) ⟨2015198, by rfl⟩ : syracuseStep 2686931 = 4030397) B4030397
theorem B4033799 : Blo 527800 4033799 := bstep (se 1 (by rfl) ⟨3025349, by rfl⟩ : syracuseStep 4033799 = 6050699) B6050699
theorem B528027 : Blo 527800 528027 := bstep (se 1 (by rfl) ⟨396020, by rfl⟩ : syracuseStep 528027 = 792041) B792041
theorem B528231 : Blo 527800 528231 := bstep (se 1 (by rfl) ⟨396173, by rfl⟩ : syracuseStep 528231 = 792347) B792347
theorem B283250789 : Blo 527800 283250789 := bstep (se 4 (by rfl) ⟨26554761, by rfl⟩ : syracuseStep 283250789 = 53109523) B53109523
theorem B528543 : Blo 527800 528543 := bstep (se 1 (by rfl) ⟨396407, by rfl⟩ : syracuseStep 528543 = 792815) B792815
theorem B528711 : Blo 527800 528711 := bstep (se 1 (by rfl) ⟨396533, by rfl⟩ : syracuseStep 528711 = 793067) B793067
theorem B529343 : Blo 527800 529343 := bstep (se 1 (by rfl) ⟨397007, by rfl⟩ : syracuseStep 529343 = 794015) B794015
theorem B529567 : Blo 527800 529567 := bstep (se 1 (by rfl) ⟨397175, by rfl⟩ : syracuseStep 529567 = 794351) B794351
theorem B792167 : Blo 527800 792167 := bstep (se 1 (by rfl) ⟨594125, by rfl⟩ : syracuseStep 792167 = 1188251) B1188251
theorem B530459 : Blo 527800 530459 := bstep (se 1 (by rfl) ⟨397844, by rfl⟩ : syracuseStep 530459 = 795689) B795689
theorem B530479 : Blo 527800 530479 := bstep (se 1 (by rfl) ⟨397859, by rfl⟩ : syracuseStep 530479 = 795719) B795719
theorem B891371 : Blo 527800 891371 := bstep (se 1 (by rfl) ⟨668528, by rfl⟩ : syracuseStep 891371 = 1337057) B1337057
theorem B9640673 : Blo 527800 9640673 := bstep (se 2 (by rfl) ⟨3615252, by rfl⟩ : syracuseStep 9640673 = 7230505) B7230505
theorem B531231 : Blo 527800 531231 := bstep (se 1 (by rfl) ⟨398423, by rfl⟩ : syracuseStep 531231 = 796847) B796847
theorem B891931 : Blo 527800 891931 := bstep (se 1 (by rfl) ⟨668948, by rfl⟩ : syracuseStep 891931 = 1337897) B1337897
theorem B531711 : Blo 527800 531711 := bstep (se 1 (by rfl) ⟨398783, by rfl⟩ : syracuseStep 531711 = 797567) B797567
theorem B793883 : Blo 527800 793883 := bstep (se 1 (by rfl) ⟨595412, by rfl⟩ : syracuseStep 793883 = 1190825) B1190825
theorem B2006633 : Blo 527800 2006633 := bstep (se 2 (by rfl) ⟨752487, by rfl⟩ : syracuseStep 2006633 = 1504975) B1504975
theorem B794651 : Blo 527800 794651 := bstep (se 1 (by rfl) ⟨595988, by rfl⟩ : syracuseStep 794651 = 1191977) B1191977
theorem B892991 : Blo 527800 892991 := bstep (se 1 (by rfl) ⟨669743, by rfl⟩ : syracuseStep 892991 = 1339487) B1339487
theorem B794735 : Blo 527800 794735 := bstep (se 1 (by rfl) ⟨596051, by rfl⟩ : syracuseStep 794735 = 1192103) B1192103
theorem B16523459 : Blo 527800 16523459 := bstep (se 1 (by rfl) ⟨12392594, by rfl⟩ : syracuseStep 16523459 = 24785189) B24785189
theorem B3383531 : Blo 527800 3383531 := bstep (se 1 (by rfl) ⟨2537648, by rfl⟩ : syracuseStep 3383531 = 5075297) B5075297
theorem B795455 : Blo 527800 795455 := bstep (se 1 (by rfl) ⟨596591, by rfl⟩ : syracuseStep 795455 = 1193183) B1193183
theorem B893855 : Blo 527800 893855 := bstep (se 1 (by rfl) ⟨670391, by rfl⟩ : syracuseStep 893855 = 1340783) B1340783
theorem B22947461 : Blo 527800 22947461 := bstep (se 4 (by rfl) ⟨2151324, by rfl⟩ : syracuseStep 22947461 = 4302649) B4302649
theorem B797159 : Blo 527800 797159 := bstep (se 1 (by rfl) ⟨597869, by rfl⟩ : syracuseStep 797159 = 1195739) B1195739
theorem B8596475 : Blo 527800 8596475 := bstep (se 1 (by rfl) ⟨6447356, by rfl⟩ : syracuseStep 8596475 = 12894713) B12894713
theorem B896231 : Blo 527800 896231 := bstep (se 1 (by rfl) ⟨672173, by rfl⟩ : syracuseStep 896231 = 1344347) B1344347
theorem B7744895 : Blo 527800 7744895 := bstep (se 1 (by rfl) ⟨5808671, by rfl⟩ : syracuseStep 7744895 = 11617343) B11617343
theorem B4009499 : Blo 527800 4009499 := bstep (se 1 (by rfl) ⟨3007124, by rfl⟩ : syracuseStep 4009499 = 6014249) B6014249
theorem B1781729 : Blo 527800 1781729 := bstep (se 2 (by rfl) ⟨668148, by rfl⟩ : syracuseStep 1781729 = 1336297) B1336297
theorem B897115 : Blo 527800 897115 := bstep (se 1 (by rfl) ⟨672836, by rfl⟩ : syracuseStep 897115 = 1345673) B1345673
theorem B6041951 : Blo 527800 6041951 := bstep (se 1 (by rfl) ⟨4531463, by rfl⟩ : syracuseStep 6041951 = 9062927) B9062927
theorem B2208703 : Blo 527800 2208703 := bstep (se 1 (by rfl) ⟨1656527, by rfl⟩ : syracuseStep 2208703 = 3313055) B3313055
theorem B1193129 : Blo 527800 1193129 := bstep (se 2 (by rfl) ⟨447423, by rfl⟩ : syracuseStep 1193129 = 894847) B894847
theorem B2012647 : Blo 527800 2012647 := bstep (se 1 (by rfl) ⟨1509485, by rfl⟩ : syracuseStep 2012647 = 3018971) B3018971
theorem B1193759 : Blo 527800 1193759 := bstep (se 1 (by rfl) ⟨895319, by rfl⟩ : syracuseStep 1193759 = 1790639) B1790639
theorem B1128937 : Blo 527800 1128937 := bstep (se 2 (by rfl) ⟨423351, by rfl⟩ : syracuseStep 1128937 = 846703) B846703
theorem B1194479 : Blo 527800 1194479 := bstep (se 1 (by rfl) ⟨895859, by rfl⟩ : syracuseStep 1194479 = 1791719) B1791719
theorem B1916095 : Blo 527800 1916095 := bstep (se 1 (by rfl) ⟨1437071, by rfl⟩ : syracuseStep 1916095 = 2874143) B2874143
theorem B4603517 : Blo 527800 4603517 := bstep (se 3 (by rfl) ⟨863159, by rfl⟩ : syracuseStep 4603517 = 1726319) B1726319
theorem B1196027 : Blo 527800 1196027 := bstep (se 1 (by rfl) ⟨897020, by rfl⟩ : syracuseStep 1196027 = 1794041) B1794041
theorem B7651583 : Blo 527800 7651583 := bstep (se 1 (by rfl) ⟨5738687, by rfl⟩ : syracuseStep 7651583 = 11477375) B11477375
theorem B2146655 : Blo 527800 2146655 := bstep (se 1 (by rfl) ⟨1609991, by rfl⟩ : syracuseStep 2146655 = 3219983) B3219983
theorem B2802131 : Blo 527800 2802131 := bstep (se 1 (by rfl) ⟨2101598, by rfl⟩ : syracuseStep 2802131 = 4203197) B4203197
theorem B1131175 : Blo 527800 1131175 := bstep (se 1 (by rfl) ⟨848381, by rfl⟩ : syracuseStep 1131175 = 1696763) B1696763
theorem B23252183 : Blo 527800 23252183 := bstep (se 1 (by rfl) ⟨17439137, by rfl⟩ : syracuseStep 23252183 = 34878275) B34878275
theorem B7621937 : Blo 527800 7621937 := bstep (se 2 (by rfl) ⟨2858226, by rfl⟩ : syracuseStep 7621937 = 5716453) B5716453
theorem B3395627 : Blo 527800 3395627 := bstep (se 1 (by rfl) ⟨2546720, by rfl⟩ : syracuseStep 3395627 = 5093441) B5093441
theorem B1790909 : Blo 527800 1790909 := bstep (se 3 (by rfl) ⟨335795, by rfl⟩ : syracuseStep 1790909 = 671591) B671591
theorem B1791287 : Blo 527800 1791287 := bstep (se 1 (by rfl) ⟨1343465, by rfl⟩ : syracuseStep 1791287 = 2686931) B2686931
theorem B123655987 : Blo 527800 123655987 := bstep (se 1 (by rfl) ⟨92741990, by rfl⟩ : syracuseStep 123655987 = 185483981) B185483981
theorem B6445021 : Blo 527800 6445021 := bstep (se 3 (by rfl) ⟨1208441, by rfl⟩ : syracuseStep 6445021 = 2416883) B2416883
theorem B4020191 : Blo 527800 4020191 := bstep (se 1 (by rfl) ⟨3015143, by rfl⟩ : syracuseStep 4020191 = 6030287) B6030287
theorem B1005671 : Blo 527800 1005671 := bstep (se 1 (by rfl) ⟨754253, by rfl⟩ : syracuseStep 1005671 = 1508507) B1508507
theorem B4086865 : Blo 527800 4086865 := bstep (se 2 (by rfl) ⟨1532574, by rfl⟩ : syracuseStep 4086865 = 3065149) B3065149
theorem B2415935 : Blo 527800 2415935 := bstep (se 1 (by rfl) ⟨1811951, by rfl⟩ : syracuseStep 2415935 = 3623903) B3623903
theorem B909479 : Blo 527800 909479 := bstep (se 1 (by rfl) ⟨682109, by rfl⟩ : syracuseStep 909479 = 1364219) B1364219
theorem B3367177 : Blo 527800 3367177 := bstep (se 2 (by rfl) ⟨1262691, by rfl⟩ : syracuseStep 3367177 = 2525383) B2525383
theorem B4285007 : Blo 527800 4285007 := bstep (se 1 (by rfl) ⟨3213755, by rfl⟩ : syracuseStep 4285007 = 6427511) B6427511
theorem B1008283 : Blo 527800 1008283 := bstep (se 1 (by rfl) ⟨756212, by rfl⟩ : syracuseStep 1008283 = 1512425) B1512425
theorem B1336601 : Blo 527800 1336601 := bstep (se 2 (by rfl) ⟨501225, by rfl⟩ : syracuseStep 1336601 = 1002451) B1002451
theorem B7628165 : Blo 527800 7628165 := bstep (se 4 (by rfl) ⟨715140, by rfl⟩ : syracuseStep 7628165 = 1430281) B1430281
theorem B5105051 : Blo 527800 5105051 := bstep (se 1 (by rfl) ⟨3828788, by rfl⟩ : syracuseStep 5105051 = 7657577) B7657577
theorem B1697249 : Blo 527800 1697249 := bstep (se 2 (by rfl) ⟨636468, by rfl⟩ : syracuseStep 1697249 = 1272937) B1272937
theorem B10151507 : Blo 527800 10151507 := bstep (se 1 (by rfl) ⟨7613630, by rfl⟩ : syracuseStep 10151507 = 15227261) B15227261
theorem B15952183 : Blo 527800 15952183 := bstep (se 1 (by rfl) ⟨11964137, by rfl⟩ : syracuseStep 15952183 = 23928275) B23928275
theorem B12872915 : Blo 527800 12872915 := bstep (se 1 (by rfl) ⟨9654686, by rfl⟩ : syracuseStep 12872915 = 19309373) B19309373
theorem B1338707 : Blo 527800 1338707 := bstep (se 1 (by rfl) ⟨1004030, by rfl⟩ : syracuseStep 1338707 = 2008061) B2008061
theorem B1273313 : Blo 527800 1273313 := bstep (se 2 (by rfl) ⟨477492, by rfl⟩ : syracuseStep 1273313 = 954985) B954985
theorem B1339001 : Blo 527800 1339001 := bstep (se 2 (by rfl) ⟨502125, by rfl⟩ : syracuseStep 1339001 = 1004251) B1004251
theorem B1339163 : Blo 527800 1339163 := bstep (se 1 (by rfl) ⟨1004372, by rfl⟩ : syracuseStep 1339163 = 2008745) B2008745
theorem B2258761 : Blo 527800 2258761 := bstep (se 2 (by rfl) ⟨847035, by rfl⟩ : syracuseStep 2258761 = 1694071) B1694071
theorem B2259035 : Blo 527800 2259035 := bstep (se 1 (by rfl) ⟨1694276, by rfl⟩ : syracuseStep 2259035 = 3388553) B3388553
theorem B1243387 : Blo 527800 1243387 := bstep (se 1 (by rfl) ⟨932540, by rfl⟩ : syracuseStep 1243387 = 1865081) B1865081
theorem B8288507 : Blo 527800 8288507 := bstep (se 1 (by rfl) ⟨6216380, by rfl⟩ : syracuseStep 8288507 = 12432761) B12432761
theorem B752009 : Blo 527800 752009 := bstep (se 2 (by rfl) ⟨282003, by rfl⟩ : syracuseStep 752009 = 564007) B564007
theorem B3047327 : Blo 527800 3047327 := bstep (se 1 (by rfl) ⟨2285495, by rfl⟩ : syracuseStep 3047327 = 4570991) B4570991
theorem B1868087 : Blo 527800 1868087 := bstep (se 1 (by rfl) ⟨1401065, by rfl⟩ : syracuseStep 1868087 = 2802131) B2802131
theorem B2425277 : Blo 527800 2425277 := bstep (se 3 (by rfl) ⟨454739, by rfl⟩ : syracuseStep 2425277 = 909479) B909479
theorem B1344377 : Blo 527800 1344377 := bstep (se 2 (by rfl) ⟨504141, by rfl⟩ : syracuseStep 1344377 = 1008283) B1008283
theorem B1508233 : Blo 527800 1508233 := bstep (se 2 (by rfl) ⟨565587, by rfl⟩ : syracuseStep 1508233 = 1131175) B1131175
theorem B17958277 : Blo 527800 17958277 := bstep (se 4 (by rfl) ⟨1683588, by rfl⟩ : syracuseStep 17958277 = 3367177) B3367177
theorem B15501455 : Blo 527800 15501455 := bstep (se 1 (by rfl) ⟨11626091, by rfl⟩ : syracuseStep 15501455 = 23252183) B23252183
theorem B2689199 : Blo 527800 2689199 := bstep (se 1 (by rfl) ⟨2016899, by rfl⟩ : syracuseStep 2689199 = 4033799) B4033799
theorem B5081291 : Blo 527800 5081291 := bstep (se 1 (by rfl) ⟨3810968, by rfl⟩ : syracuseStep 5081291 = 7621937) B7621937
theorem B2263751 : Blo 527800 2263751 := bstep (se 1 (by rfl) ⟨1697813, by rfl⟩ : syracuseStep 2263751 = 3395627) B3395627
theorem B528111 : Blo 527800 528111 := bstep (se 1 (by rfl) ⟨396083, by rfl⟩ : syracuseStep 528111 = 792167) B792167
theorem B594247 : Blo 527800 594247 := bstep (se 1 (by rfl) ⟨445685, by rfl⟩ : syracuseStep 594247 = 891371) B891371
theorem B6427115 : Blo 527800 6427115 := bstep (se 1 (by rfl) ⟨4820336, by rfl⟩ : syracuseStep 6427115 = 9640673) B9640673
theorem B529255 : Blo 527800 529255 := bstep (se 1 (by rfl) ⟨396941, by rfl⟩ : syracuseStep 529255 = 793883) B793883
theorem B1610623 : Blo 527800 1610623 := bstep (se 1 (by rfl) ⟨1207967, by rfl⟩ : syracuseStep 1610623 = 2415935) B2415935
theorem B529767 : Blo 527800 529767 := bstep (se 1 (by rfl) ⟨397325, by rfl⟩ : syracuseStep 529767 = 794651) B794651
theorem B595327 : Blo 527800 595327 := bstep (se 1 (by rfl) ⟨446495, by rfl⟩ : syracuseStep 595327 = 892991) B892991
theorem B529823 : Blo 527800 529823 := bstep (se 1 (by rfl) ⟨397367, by rfl⟩ : syracuseStep 529823 = 794735) B794735
theorem B11015639 : Blo 527800 11015639 := bstep (se 1 (by rfl) ⟨8261729, by rfl⟩ : syracuseStep 11015639 = 16523459) B16523459
theorem B2856671 : Blo 527800 2856671 := bstep (se 1 (by rfl) ⟨2142503, by rfl⟩ : syracuseStep 2856671 = 4285007) B4285007
theorem B21796613 : Blo 527800 21796613 := bstep (se 4 (by rfl) ⟨2043432, by rfl⟩ : syracuseStep 21796613 = 4086865) B4086865
theorem B530303 : Blo 527800 530303 := bstep (se 1 (by rfl) ⟨397727, by rfl⟩ : syracuseStep 530303 = 795455) B795455
theorem B595903 : Blo 527800 595903 := bstep (se 1 (by rfl) ⟨446927, by rfl⟩ : syracuseStep 595903 = 893855) B893855
theorem B891067 : Blo 527800 891067 := bstep (se 1 (by rfl) ⟨668300, by rfl⟩ : syracuseStep 891067 = 1336601) B1336601
theorem B5085443 : Blo 527800 5085443 := bstep (se 1 (by rfl) ⟨3814082, by rfl⟩ : syracuseStep 5085443 = 7628165) B7628165
theorem B2005357 : Blo 527800 2005357 := bstep (se 3 (by rfl) ⟨376004, by rfl⟩ : syracuseStep 2005357 = 752009) B752009
theorem B531439 : Blo 527800 531439 := bstep (se 1 (by rfl) ⟨398579, by rfl⟩ : syracuseStep 531439 = 797159) B797159
theorem B597487 : Blo 527800 597487 := bstep (se 1 (by rfl) ⟨448115, by rfl⟩ : syracuseStep 597487 = 896231) B896231
theorem B892471 : Blo 527800 892471 := bstep (se 1 (by rfl) ⟨669353, by rfl⟩ : syracuseStep 892471 = 1338707) B1338707
theorem B892667 : Blo 527800 892667 := bstep (se 1 (by rfl) ⟨669500, by rfl⟩ : syracuseStep 892667 = 1339001) B1339001
theorem B892775 : Blo 527800 892775 := bstep (se 1 (by rfl) ⟨669581, by rfl⟩ : syracuseStep 892775 = 1339163) B1339163
theorem B8593361 : Blo 527800 8593361 := bstep (se 2 (by rfl) ⟨3222510, by rfl⟩ : syracuseStep 8593361 = 6445021) B6445021
theorem B1187819 : Blo 527800 1187819 := bstep (se 1 (by rfl) ⟨890864, by rfl⟩ : syracuseStep 1187819 = 1781729) B1781729
theorem B795419 : Blo 527800 795419 := bstep (se 1 (by rfl) ⟨596564, by rfl⟩ : syracuseStep 795419 = 1193129) B1193129
theorem B795839 : Blo 527800 795839 := bstep (se 1 (by rfl) ⟨596879, by rfl⟩ : syracuseStep 795839 = 1193759) B1193759
theorem B1189241 : Blo 527800 1189241 := bstep (se 2 (by rfl) ⟨445965, by rfl⟩ : syracuseStep 1189241 = 891931) B891931
theorem B796319 : Blo 527800 796319 := bstep (se 1 (by rfl) ⟨597239, by rfl⟩ : syracuseStep 796319 = 1194479) B1194479
theorem B797351 : Blo 527800 797351 := bstep (se 1 (by rfl) ⟨598013, by rfl⟩ : syracuseStep 797351 = 1196027) B1196027
theorem B85078309 : Blo 527800 85078309 := bstep (se 4 (by rfl) ⟨7976091, by rfl⟩ : syracuseStep 85078309 = 15952183) B15952183
theorem B1193939 : Blo 527800 1193939 := bstep (se 1 (by rfl) ⟨895454, by rfl⟩ : syracuseStep 1193939 = 1790909) B1790909
theorem B1194191 : Blo 527800 1194191 := bstep (se 1 (by rfl) ⟨895643, by rfl⟩ : syracuseStep 1194191 = 1791287) B1791287
theorem B670447 : Blo 527800 670447 := bstep (se 1 (by rfl) ⟨502835, by rfl⟩ : syracuseStep 670447 = 1005671) B1005671
theorem B1196153 : Blo 527800 1196153 := bstep (se 2 (by rfl) ⟨448557, by rfl⟩ : syracuseStep 1196153 = 897115) B897115
theorem B1131499 : Blo 527800 1131499 := bstep (se 1 (by rfl) ⟨848624, by rfl⟩ : syracuseStep 1131499 = 1697249) B1697249
theorem B6767671 : Blo 527800 6767671 := bstep (se 1 (by rfl) ⟨5075753, by rfl⟩ : syracuseStep 6767671 = 10151507) B10151507
theorem B5163263 : Blo 527800 5163263 := bstep (se 1 (by rfl) ⟨3872447, by rfl⟩ : syracuseStep 5163263 = 7744895) B7744895
theorem B2672999 : Blo 527800 2672999 := bstep (se 1 (by rfl) ⟨2004749, by rfl⟩ : syracuseStep 2672999 = 4009499) B4009499
theorem B164874649 : Blo 527800 164874649 := bstep (se 2 (by rfl) ⟨61827993, by rfl⟩ : syracuseStep 164874649 = 123655987) B123655987
theorem B1657849 : Blo 527800 1657849 := bstep (se 2 (by rfl) ⟨621693, by rfl⟩ : syracuseStep 1657849 = 1243387) B1243387
theorem B5525671 : Blo 527800 5525671 := bstep (se 1 (by rfl) ⟨4144253, by rfl⟩ : syracuseStep 5525671 = 8288507) B8288507
theorem B3069011 : Blo 527800 3069011 := bstep (se 1 (by rfl) ⟨2301758, by rfl⟩ : syracuseStep 3069011 = 4603517) B4603517
theorem B5101055 : Blo 527800 5101055 := bstep (se 1 (by rfl) ⟨3825791, by rfl⟩ : syracuseStep 5101055 = 7651583) B7651583
theorem B1431103 : Blo 527800 1431103 := bstep (se 1 (by rfl) ⟨1073327, by rfl⟩ : syracuseStep 1431103 = 2146655) B2146655
theorem B188833859 : Blo 527800 188833859 := bstep (se 1 (by rfl) ⟨141625394, by rfl⟩ : syracuseStep 188833859 = 283250789) B283250789
theorem B2680127 : Blo 527800 2680127 := bstep (se 1 (by rfl) ⟨2010095, by rfl⟩ : syracuseStep 2680127 = 4020191) B4020191
theorem B1337755 : Blo 527800 1337755 := bstep (se 1 (by rfl) ⟨1003316, by rfl⟩ : syracuseStep 1337755 = 2006633) B2006633
theorem B2255687 : Blo 527800 2255687 := bstep (se 1 (by rfl) ⟨1691765, by rfl⟩ : syracuseStep 2255687 = 3383531) B3383531
theorem B3403367 : Blo 527800 3403367 := bstep (se 1 (by rfl) ⟨2552525, by rfl⟩ : syracuseStep 3403367 = 5105051) B5105051
theorem B15298307 : Blo 527800 15298307 := bstep (se 1 (by rfl) ⟨11473730, by rfl⟩ : syracuseStep 15298307 = 22947461) B22947461
theorem B2944937 : Blo 527800 2944937 := bstep (se 2 (by rfl) ⟨1104351, by rfl⟩ : syracuseStep 2944937 = 2208703) B2208703
theorem B2683529 : Blo 527800 2683529 := bstep (se 2 (by rfl) ⟨1006323, by rfl⟩ : syracuseStep 2683529 = 2012647) B2012647
theorem B5730983 : Blo 527800 5730983 := bstep (se 1 (by rfl) ⟨4298237, by rfl⟩ : syracuseStep 5730983 = 8596475) B8596475
theorem B8581943 : Blo 527800 8581943 := bstep (se 1 (by rfl) ⟨6436457, by rfl⟩ : syracuseStep 8581943 = 12872915) B12872915
theorem B848875 : Blo 527800 848875 := bstep (se 1 (by rfl) ⟨636656, by rfl⟩ : syracuseStep 848875 = 1273313) B1273313
theorem B3011681 : Blo 527800 3011681 := bstep (se 2 (by rfl) ⟨1129380, by rfl⟩ : syracuseStep 3011681 = 2258761) B2258761
theorem B4027967 : Blo 527800 4027967 := bstep (se 1 (by rfl) ⟨3020975, by rfl⟩ : syracuseStep 4027967 = 6041951) B6041951
theorem B1505249 : Blo 527800 1505249 := bstep (se 2 (by rfl) ⟨564468, by rfl⟩ : syracuseStep 1505249 = 1128937) B1128937
theorem B1506023 : Blo 527800 1506023 := bstep (se 1 (by rfl) ⟨1129517, by rfl⟩ : syracuseStep 1506023 = 2259035) B2259035
theorem B2554793 : Blo 527800 2554793 := bstep (se 2 (by rfl) ⟨958047, by rfl⟩ : syracuseStep 2554793 = 1916095) B1916095
theorem B2031551 : Blo 527800 2031551 := bstep (se 1 (by rfl) ⟨1523663, by rfl⟩ : syracuseStep 2031551 = 3047327) B3047327
theorem B4981565 : Blo 527800 4981565 := bstep (se 3 (by rfl) ⟨934043, by rfl⟩ : syracuseStep 4981565 = 1868087) B1868087
theorem B3442175 : Blo 527800 3442175 := bstep (se 1 (by rfl) ⟨2581631, by rfl⟩ : syracuseStep 3442175 = 5163263) B5163263
theorem B1509167 : Blo 527800 1509167 := bstep (se 1 (by rfl) ⟨1131875, by rfl⟩ : syracuseStep 1509167 = 2263751) B2263751
theorem B7343759 : Blo 527800 7343759 := bstep (se 1 (by rfl) ⟨5507819, by rfl⟩ : syracuseStep 7343759 = 11015639) B11015639
theorem B1904447 : Blo 527800 1904447 := bstep (se 1 (by rfl) ⟨1428335, by rfl⟩ : syracuseStep 1904447 = 2856671) B2856671
theorem B8589989 : Blo 527800 8589989 := bstep (se 4 (by rfl) ⟨805311, by rfl⟩ : syracuseStep 8589989 = 1610623) B1610623
theorem B595111 : Blo 527800 595111 := bstep (se 1 (by rfl) ⟨446333, by rfl⟩ : syracuseStep 595111 = 892667) B892667
theorem B6034661 : Blo 527800 6034661 := bstep (se 4 (by rfl) ⟨565749, by rfl⟩ : syracuseStep 6034661 = 1131499) B1131499
theorem B595183 : Blo 527800 595183 := bstep (se 1 (by rfl) ⟨446387, by rfl⟩ : syracuseStep 595183 = 892775) B892775
theorem B791879 : Blo 527800 791879 := bstep (se 1 (by rfl) ⟨593909, by rfl⟩ : syracuseStep 791879 = 1187819) B1187819
theorem B792329 : Blo 527800 792329 := bstep (se 2 (by rfl) ⟨297123, by rfl⟩ : syracuseStep 792329 = 594247) B594247
theorem B530279 : Blo 527800 530279 := bstep (se 1 (by rfl) ⟨397709, by rfl⟩ : syracuseStep 530279 = 795419) B795419
theorem B530559 : Blo 527800 530559 := bstep (se 1 (by rfl) ⟨397919, by rfl⟩ : syracuseStep 530559 = 795839) B795839
theorem B792827 : Blo 527800 792827 := bstep (se 1 (by rfl) ⟨594620, by rfl⟩ : syracuseStep 792827 = 1189241) B1189241
theorem B530879 : Blo 527800 530879 := bstep (se 1 (by rfl) ⟨398159, by rfl⟩ : syracuseStep 530879 = 796319) B796319
theorem B531567 : Blo 527800 531567 := bstep (se 1 (by rfl) ⟨398675, by rfl⟩ : syracuseStep 531567 = 797351) B797351
theorem B793769 : Blo 527800 793769 := bstep (se 2 (by rfl) ⟨297663, by rfl⟩ : syracuseStep 793769 = 595327) B595327
theorem B1908137 : Blo 527800 1908137 := bstep (se 2 (by rfl) ⟨715551, by rfl⟩ : syracuseStep 1908137 = 1431103) B1431103
theorem B2268911 : Blo 527800 2268911 := bstep (se 1 (by rfl) ⟨1701683, by rfl⟩ : syracuseStep 2268911 = 3403367) B3403367
theorem B10198871 : Blo 527800 10198871 := bstep (se 1 (by rfl) ⟨7649153, by rfl⟩ : syracuseStep 10198871 = 15298307) B15298307
theorem B794537 : Blo 527800 794537 := bstep (se 2 (by rfl) ⟨297951, by rfl⟩ : syracuseStep 794537 = 595903) B595903
theorem B1188089 : Blo 527800 1188089 := bstep (se 2 (by rfl) ⟨445533, by rfl⟩ : syracuseStep 1188089 = 891067) B891067
theorem B2007787 : Blo 527800 2007787 := bstep (se 1 (by rfl) ⟨1505840, by rfl⟩ : syracuseStep 2007787 = 3011681) B3011681
theorem B893929 : Blo 527800 893929 := bstep (se 2 (by rfl) ⟨335223, by rfl⟩ : syracuseStep 893929 = 670447) B670447
theorem B795959 : Blo 527800 795959 := bstep (se 1 (by rfl) ⟨596969, by rfl⟩ : syracuseStep 795959 = 1193939) B1193939
theorem B796127 : Blo 527800 796127 := bstep (se 1 (by rfl) ⟨597095, by rfl⟩ : syracuseStep 796127 = 1194191) B1194191
theorem B796649 : Blo 527800 796649 := bstep (se 2 (by rfl) ⟨298743, by rfl⟩ : syracuseStep 796649 = 597487) B597487
theorem B1189961 : Blo 527800 1189961 := bstep (se 2 (by rfl) ⟨446235, by rfl⟩ : syracuseStep 1189961 = 892471) B892471
theorem B1354367 : Blo 527800 1354367 := bstep (se 1 (by rfl) ⟨1015775, by rfl⟩ : syracuseStep 1354367 = 2031551) B2031551
theorem B797435 : Blo 527800 797435 := bstep (se 1 (by rfl) ⟨598076, by rfl⟩ : syracuseStep 797435 = 1196153) B1196153
theorem B1616851 : Blo 527800 1616851 := bstep (se 1 (by rfl) ⟨1212638, by rfl⟩ : syracuseStep 1616851 = 2425277) B2425277
theorem B896251 : Blo 527800 896251 := bstep (se 1 (by rfl) ⟨672188, by rfl⟩ : syracuseStep 896251 = 1344377) B1344377
theorem B2010977 : Blo 527800 2010977 := bstep (se 2 (by rfl) ⟨754116, by rfl⟩ : syracuseStep 2010977 = 1508233) B1508233
theorem B9023561 : Blo 527800 9023561 := bstep (se 2 (by rfl) ⟨3383835, by rfl⟩ : syracuseStep 9023561 = 6767671) B6767671
theorem B10334303 : Blo 527800 10334303 := bstep (se 1 (by rfl) ⟨7750727, by rfl⟩ : syracuseStep 10334303 = 15501455) B15501455
theorem B3387527 : Blo 527800 3387527 := bstep (se 1 (by rfl) ⟨2540645, by rfl⟩ : syracuseStep 3387527 = 5081291) B5081291
theorem B1781999 : Blo 527800 1781999 := bstep (se 1 (by rfl) ⟨1336499, by rfl⟩ : syracuseStep 1781999 = 2672999) B2672999
theorem B1783673 : Blo 527800 1783673 := bstep (se 2 (by rfl) ⟨668877, by rfl⟩ : syracuseStep 1783673 = 1337755) B1337755
theorem B2046007 : Blo 527800 2046007 := bstep (se 1 (by rfl) ⟨1534505, by rfl⟩ : syracuseStep 2046007 = 3069011) B3069011
theorem B14531075 : Blo 527800 14531075 := bstep (se 1 (by rfl) ⟨10898306, by rfl⟩ : syracuseStep 14531075 = 21796613) B21796613
theorem B2210465 : Blo 527800 2210465 := bstep (se 2 (by rfl) ⟨828924, by rfl⟩ : syracuseStep 2210465 = 1657849) B1657849
theorem B3390295 : Blo 527800 3390295 := bstep (se 1 (by rfl) ⟨2542721, by rfl⟩ : syracuseStep 3390295 = 5085443) B5085443
theorem B1786751 : Blo 527800 1786751 := bstep (se 1 (by rfl) ⟨1340063, by rfl⟩ : syracuseStep 1786751 = 2680127) B2680127
theorem B1131833 : Blo 527800 1131833 := bstep (se 2 (by rfl) ⟨424437, by rfl⟩ : syracuseStep 1131833 = 848875) B848875
theorem B1789019 : Blo 527800 1789019 := bstep (se 1 (by rfl) ⟨1341764, by rfl⟩ : syracuseStep 1789019 = 2683529) B2683529
theorem B3820655 : Blo 527800 3820655 := bstep (se 1 (by rfl) ⟨2865491, by rfl⟩ : syracuseStep 3820655 = 5730983) B5730983
theorem B2673809 : Blo 527800 2673809 := bstep (se 2 (by rfl) ⟨1002678, by rfl⟩ : syracuseStep 2673809 = 2005357) B2005357
theorem B5721295 : Blo 527800 5721295 := bstep (se 1 (by rfl) ⟨4290971, by rfl⟩ : syracuseStep 5721295 = 8581943) B8581943
theorem B1003499 : Blo 527800 1003499 := bstep (se 1 (by rfl) ⟨752624, by rfl⟩ : syracuseStep 1003499 = 1505249) B1505249
theorem B1004015 : Blo 527800 1004015 := bstep (se 1 (by rfl) ⟨753011, by rfl⟩ : syracuseStep 1004015 = 1506023) B1506023
theorem B1792799 : Blo 527800 1792799 := bstep (se 1 (by rfl) ⟨1344599, by rfl⟩ : syracuseStep 1792799 = 2689199) B2689199
theorem B4284743 : Blo 527800 4284743 := bstep (se 1 (by rfl) ⟨3213557, by rfl⟩ : syracuseStep 4284743 = 6427115) B6427115
theorem B219832865 : Blo 527800 219832865 := bstep (se 2 (by rfl) ⟨82437324, by rfl⟩ : syracuseStep 219832865 = 164874649) B164874649
theorem B3400703 : Blo 527800 3400703 := bstep (se 1 (by rfl) ⟨2550527, by rfl⟩ : syracuseStep 3400703 = 5101055) B5101055
theorem B5728907 : Blo 527800 5728907 := bstep (se 1 (by rfl) ⟨4296680, by rfl⟩ : syracuseStep 5728907 = 8593361) B8593361
theorem B125889239 : Blo 527800 125889239 := bstep (se 1 (by rfl) ⟨94416929, by rfl⟩ : syracuseStep 125889239 = 188833859) B188833859
theorem B7367561 : Blo 527800 7367561 := bstep (se 2 (by rfl) ⟨2762835, by rfl⟩ : syracuseStep 7367561 = 5525671) B5525671
theorem B113437745 : Blo 527800 113437745 := bstep (se 2 (by rfl) ⟨42539154, by rfl⟩ : syracuseStep 113437745 = 85078309) B85078309
theorem B1503791 : Blo 527800 1503791 := bstep (se 1 (by rfl) ⟨1127843, by rfl⟩ : syracuseStep 1503791 = 2255687) B2255687
theorem B95777477 : Blo 527800 95777477 := bstep (se 4 (by rfl) ⟨8979138, by rfl⟩ : syracuseStep 95777477 = 17958277) B17958277
theorem B1963291 : Blo 527800 1963291 := bstep (se 1 (by rfl) ⟨1472468, by rfl⟩ : syracuseStep 1963291 = 2944937) B2944937
theorem B2685311 : Blo 527800 2685311 := bstep (se 1 (by rfl) ⟨2013983, by rfl⟩ : syracuseStep 2685311 = 4027967) B4027967
theorem B1703195 : Blo 527800 1703195 := bstep (se 1 (by rfl) ⟨1277396, by rfl⟩ : syracuseStep 1703195 = 2554793) B2554793
theorem B2294783 : Blo 527800 2294783 := bstep (se 1 (by rfl) ⟨1721087, by rfl⟩ : syracuseStep 2294783 = 3442175) B3442175
theorem B22906637 : Blo 527800 22906637 := bstep (se 3 (by rfl) ⟨4294994, by rfl⟩ : syracuseStep 22906637 = 8589989) B8589989
theorem B3018221 : Blo 527800 3018221 := bstep (se 3 (by rfl) ⟨565916, by rfl⟩ : syracuseStep 3018221 = 1131833) B1131833
theorem B527919 : Blo 527800 527919 := bstep (se 1 (by rfl) ⟨395939, by rfl⟩ : syracuseStep 527919 = 791879) B791879
theorem B528219 : Blo 527800 528219 := bstep (se 1 (by rfl) ⟨396164, by rfl⟩ : syracuseStep 528219 = 792329) B792329
theorem B528551 : Blo 527800 528551 := bstep (se 1 (by rfl) ⟨396413, by rfl⟩ : syracuseStep 528551 = 792827) B792827
theorem B529179 : Blo 527800 529179 := bstep (se 1 (by rfl) ⟨396884, by rfl⟩ : syracuseStep 529179 = 793769) B793769
theorem B8623205 : Blo 527800 8623205 := bstep (se 4 (by rfl) ⟨808425, by rfl⟩ : syracuseStep 8623205 = 1616851) B1616851
theorem B1512607 : Blo 527800 1512607 := bstep (se 1 (by rfl) ⟨1134455, by rfl⟩ : syracuseStep 1512607 = 2268911) B2268911
theorem B529691 : Blo 527800 529691 := bstep (se 1 (by rfl) ⟨397268, by rfl⟩ : syracuseStep 529691 = 794537) B794537
theorem B792059 : Blo 527800 792059 := bstep (se 1 (by rfl) ⟨594044, by rfl⟩ : syracuseStep 792059 = 1188089) B1188089
theorem B2267135 : Blo 527800 2267135 := bstep (se 1 (by rfl) ⟨1700351, by rfl⟩ : syracuseStep 2267135 = 3400703) B3400703
theorem B530639 : Blo 527800 530639 := bstep (se 1 (by rfl) ⟨397979, by rfl⟩ : syracuseStep 530639 = 795959) B795959
theorem B530751 : Blo 527800 530751 := bstep (se 1 (by rfl) ⟨398063, by rfl⟩ : syracuseStep 530751 = 796127) B796127
theorem B531099 : Blo 527800 531099 := bstep (se 1 (by rfl) ⟨398324, by rfl⟩ : syracuseStep 531099 = 796649) B796649
theorem B793307 : Blo 527800 793307 := bstep (se 1 (by rfl) ⟨594980, by rfl⟩ : syracuseStep 793307 = 1189961) B1189961
theorem B793481 : Blo 527800 793481 := bstep (se 2 (by rfl) ⟨297555, by rfl⟩ : syracuseStep 793481 = 595111) B595111
theorem B793577 : Blo 527800 793577 := bstep (se 2 (by rfl) ⟨297591, by rfl⟩ : syracuseStep 793577 = 595183) B595183
theorem B15277085 : Blo 527800 15277085 := bstep (se 3 (by rfl) ⟨2864453, by rfl⟩ : syracuseStep 15277085 = 5728907) B5728907
theorem B531623 : Blo 527800 531623 := bstep (se 1 (by rfl) ⟨398717, by rfl⟩ : syracuseStep 531623 = 797435) B797435
theorem B6889535 : Blo 527800 6889535 := bstep (se 1 (by rfl) ⟨5167151, by rfl⟩ : syracuseStep 6889535 = 10334303) B10334303
theorem B2728009 : Blo 527800 2728009 := bstep (se 2 (by rfl) ⟨1023003, by rfl⟩ : syracuseStep 2728009 = 2046007) B2046007
theorem B1187999 : Blo 527800 1187999 := bstep (se 1 (by rfl) ⟨890999, by rfl⟩ : syracuseStep 1187999 = 1781999) B1781999
theorem B5088365 : Blo 527800 5088365 := bstep (se 3 (by rfl) ⟨954068, by rfl⟩ : syracuseStep 5088365 = 1908137) B1908137
theorem B1189115 : Blo 527800 1189115 := bstep (se 1 (by rfl) ⟨891836, by rfl⟩ : syracuseStep 1189115 = 1783673) B1783673
theorem B3321043 : Blo 527800 3321043 := bstep (se 1 (by rfl) ⟨2490782, by rfl⟩ : syracuseStep 3321043 = 4981565) B4981565
theorem B1191167 : Blo 527800 1191167 := bstep (se 1 (by rfl) ⟨893375, by rfl⟩ : syracuseStep 1191167 = 1786751) B1786751
theorem B1191905 : Blo 527800 1191905 := bstep (se 2 (by rfl) ⟨446964, by rfl⟩ : syracuseStep 1191905 = 893929) B893929
theorem B1192679 : Blo 527800 1192679 := bstep (se 1 (by rfl) ⟨894509, by rfl⟩ : syracuseStep 1192679 = 1789019) B1789019
theorem B1782539 : Blo 527800 1782539 := bstep (se 1 (by rfl) ⟨1336904, by rfl⟩ : syracuseStep 1782539 = 2673809) B2673809
theorem B4895839 : Blo 527800 4895839 := bstep (se 1 (by rfl) ⟨3671879, by rfl⟩ : syracuseStep 4895839 = 7343759) B7343759
theorem B668999 : Blo 527800 668999 := bstep (se 1 (by rfl) ⟨501749, by rfl⟩ : syracuseStep 668999 = 1003499) B1003499
theorem B1195001 : Blo 527800 1195001 := bstep (se 2 (by rfl) ⟨448125, by rfl⟩ : syracuseStep 1195001 = 896251) B896251
theorem B1195199 : Blo 527800 1195199 := bstep (se 1 (by rfl) ⟨896399, by rfl⟩ : syracuseStep 1195199 = 1792799) B1792799
theorem B6799247 : Blo 527800 6799247 := bstep (se 1 (by rfl) ⟨5099435, by rfl⟩ : syracuseStep 6799247 = 10198871) B10198871
theorem B146555243 : Blo 527800 146555243 := bstep (se 1 (by rfl) ⟨109916432, by rfl⟩ : syracuseStep 146555243 = 219832865) B219832865
theorem B902911 : Blo 527800 902911 := bstep (se 1 (by rfl) ⟨677183, by rfl⟩ : syracuseStep 902911 = 1354367) B1354367
theorem B6015707 : Blo 527800 6015707 := bstep (se 1 (by rfl) ⟨4511780, by rfl⟩ : syracuseStep 6015707 = 9023561) B9023561
theorem B1002527 : Blo 527800 1002527 := bstep (se 1 (by rfl) ⟨751895, by rfl⟩ : syracuseStep 1002527 = 1503791) B1503791
theorem B63851651 : Blo 527800 63851651 := bstep (se 1 (by rfl) ⟨47888738, by rfl⟩ : syracuseStep 63851651 = 95777477) B95777477
theorem B1790207 : Blo 527800 1790207 := bstep (se 1 (by rfl) ⟨1342655, by rfl⟩ : syracuseStep 1790207 = 2685311) B2685311
theorem B9687383 : Blo 527800 9687383 := bstep (se 1 (by rfl) ⟨7265537, by rfl⟩ : syracuseStep 9687383 = 14531075) B14531075
theorem B1135463 : Blo 527800 1135463 := bstep (se 1 (by rfl) ⟨851597, by rfl⟩ : syracuseStep 1135463 = 1703195) B1703195
theorem B2677049 : Blo 527800 2677049 := bstep (se 2 (by rfl) ⟨1003893, by rfl⟩ : syracuseStep 2677049 = 2007787) B2007787
theorem B1006111 : Blo 527800 1006111 := bstep (se 1 (by rfl) ⟨754583, by rfl⟩ : syracuseStep 1006111 = 1509167) B1509167
theorem B2677373 : Blo 527800 2677373 := bstep (se 3 (by rfl) ⟨502007, by rfl⟩ : syracuseStep 2677373 = 1004015) B1004015
theorem B1269631 : Blo 527800 1269631 := bstep (se 1 (by rfl) ⟨952223, by rfl⟩ : syracuseStep 1269631 = 1904447) B1904447
theorem B45703925 : Blo 527800 45703925 := bstep (se 5 (by rfl) ⟨2142371, by rfl⟩ : syracuseStep 45703925 = 4284743) B4284743
theorem B4023107 : Blo 527800 4023107 := bstep (se 1 (by rfl) ⟨3017330, by rfl⟩ : syracuseStep 4023107 = 6034661) B6034661
theorem B7628393 : Blo 527800 7628393 := bstep (se 2 (by rfl) ⟨2860647, by rfl⟩ : syracuseStep 7628393 = 5721295) B5721295
theorem B2617721 : Blo 527800 2617721 := bstep (se 2 (by rfl) ⟨981645, by rfl⟩ : syracuseStep 2617721 = 1963291) B1963291
theorem B335704637 : Blo 527800 335704637 := bstep (se 3 (by rfl) ⟨62944619, by rfl⟩ : syracuseStep 335704637 = 125889239) B125889239
theorem B4911707 : Blo 527800 4911707 := bstep (se 1 (by rfl) ⟨3683780, by rfl⟩ : syracuseStep 4911707 = 7367561) B7367561
theorem B75625163 : Blo 527800 75625163 := bstep (se 1 (by rfl) ⟨56718872, by rfl⟩ : syracuseStep 75625163 = 113437745) B113437745
theorem B1340651 : Blo 527800 1340651 := bstep (se 1 (by rfl) ⟨1005488, by rfl⟩ : syracuseStep 1340651 = 2010977) B2010977
theorem B2258351 : Blo 527800 2258351 := bstep (se 1 (by rfl) ⟨1693763, by rfl⟩ : syracuseStep 2258351 = 3387527) B3387527
theorem B10188413 : Blo 527800 10188413 := bstep (se 3 (by rfl) ⟨1910327, by rfl⟩ : syracuseStep 10188413 = 3820655) B3820655
theorem B4520393 : Blo 527800 4520393 := bstep (se 2 (by rfl) ⟨1695147, by rfl⟩ : syracuseStep 4520393 = 3390295) B3390295
theorem B1473643 : Blo 527800 1473643 := bstep (se 1 (by rfl) ⟨1105232, by rfl⟩ : syracuseStep 1473643 = 2210465) B2210465
theorem B14549381 : Blo 527800 14549381 := bstep (se 4 (by rfl) ⟨1364004, by rfl⟩ : syracuseStep 14549381 = 2728009) B2728009
theorem B15271091 : Blo 527800 15271091 := bstep (se 1 (by rfl) ⟨11453318, by rfl⟩ : syracuseStep 15271091 = 22906637) B22906637
theorem B42567767 : Blo 527800 42567767 := bstep (se 1 (by rfl) ⟨31925825, by rfl⟩ : syracuseStep 42567767 = 63851651) B63851651
theorem B6458255 : Blo 527800 6458255 := bstep (se 1 (by rfl) ⟨4843691, by rfl⟩ : syracuseStep 6458255 = 9687383) B9687383
theorem B528039 : Blo 527800 528039 := bstep (se 1 (by rfl) ⟨396029, by rfl⟩ : syracuseStep 528039 = 792059) B792059
theorem B1511423 : Blo 527800 1511423 := bstep (se 1 (by rfl) ⟨1133567, by rfl⟩ : syracuseStep 1511423 = 2267135) B2267135
theorem B528871 : Blo 527800 528871 := bstep (se 1 (by rfl) ⟨396653, by rfl⟩ : syracuseStep 528871 = 793307) B793307
theorem B528987 : Blo 527800 528987 := bstep (se 1 (by rfl) ⟨396740, by rfl⟩ : syracuseStep 528987 = 793481) B793481
theorem B529051 : Blo 527800 529051 := bstep (se 1 (by rfl) ⟨396788, by rfl⟩ : syracuseStep 529051 = 793577) B793577
theorem B4593023 : Blo 527800 4593023 := bstep (se 1 (by rfl) ⟨3444767, by rfl⟩ : syracuseStep 4593023 = 6889535) B6889535
theorem B791999 : Blo 527800 791999 := bstep (se 1 (by rfl) ⟨593999, by rfl⟩ : syracuseStep 791999 = 1187999) B1187999
theorem B792743 : Blo 527800 792743 := bstep (se 1 (by rfl) ⟨594557, by rfl⟩ : syracuseStep 792743 = 1189115) B1189115
theorem B5085595 : Blo 527800 5085595 := bstep (se 1 (by rfl) ⟨3814196, by rfl⟩ : syracuseStep 5085595 = 7628393) B7628393
theorem B6527785 : Blo 527800 6527785 := bstep (se 2 (by rfl) ⟨2447919, by rfl⟩ : syracuseStep 6527785 = 4895839) B4895839
theorem B794111 : Blo 527800 794111 := bstep (se 1 (by rfl) ⟨595583, by rfl⟩ : syracuseStep 794111 = 1191167) B1191167
theorem B794603 : Blo 527800 794603 := bstep (se 1 (by rfl) ⟨595952, by rfl⟩ : syracuseStep 794603 = 1191905) B1191905
theorem B1745147 : Blo 527800 1745147 := bstep (se 1 (by rfl) ⟨1308860, by rfl⟩ : syracuseStep 1745147 = 2617721) B2617721
theorem B795119 : Blo 527800 795119 := bstep (se 1 (by rfl) ⟨596339, by rfl⟩ : syracuseStep 795119 = 1192679) B1192679
theorem B1188359 : Blo 527800 1188359 := bstep (se 1 (by rfl) ⟨891269, by rfl⟩ : syracuseStep 1188359 = 1782539) B1782539
theorem B893767 : Blo 527800 893767 := bstep (se 1 (by rfl) ⟨670325, by rfl⟩ : syracuseStep 893767 = 1340651) B1340651
theorem B6792275 : Blo 527800 6792275 := bstep (se 1 (by rfl) ⟨5094206, by rfl⟩ : syracuseStep 6792275 = 10188413) B10188413
theorem B796667 : Blo 527800 796667 := bstep (se 1 (by rfl) ⟨597500, by rfl⟩ : syracuseStep 796667 = 1195001) B1195001
theorem B796799 : Blo 527800 796799 := bstep (se 1 (by rfl) ⟨597599, by rfl⟩ : syracuseStep 796799 = 1195199) B1195199
theorem B4532831 : Blo 527800 4532831 := bstep (se 1 (by rfl) ⟨3399623, by rfl⟩ : syracuseStep 4532831 = 6799247) B6799247
theorem B4010471 : Blo 527800 4010471 := bstep (se 1 (by rfl) ⟨3007853, by rfl⟩ : syracuseStep 4010471 = 6015707) B6015707
theorem B668351 : Blo 527800 668351 := bstep (se 1 (by rfl) ⟨501263, by rfl⟩ : syracuseStep 668351 = 1002527) B1002527
theorem B3027901 : Blo 527800 3027901 := bstep (se 3 (by rfl) ⟨567731, by rfl⟩ : syracuseStep 3027901 = 1135463) B1135463
theorem B2012147 : Blo 527800 2012147 := bstep (se 1 (by rfl) ⟨1509110, by rfl⟩ : syracuseStep 2012147 = 3018221) B3018221
theorem B1193471 : Blo 527800 1193471 := bstep (se 1 (by rfl) ⟨895103, by rfl⟩ : syracuseStep 1193471 = 1790207) B1790207
theorem B5748803 : Blo 527800 5748803 := bstep (se 1 (by rfl) ⟨4311602, by rfl⟩ : syracuseStep 5748803 = 8623205) B8623205
theorem B1783997 : Blo 527800 1783997 := bstep (se 3 (by rfl) ⟨334499, by rfl⟩ : syracuseStep 1783997 = 668999) B668999
theorem B1784699 : Blo 527800 1784699 := bstep (se 1 (by rfl) ⟨1338524, by rfl⟩ : syracuseStep 1784699 = 2677049) B2677049
theorem B1784915 : Blo 527800 1784915 := bstep (se 1 (by rfl) ⟨1338686, by rfl⟩ : syracuseStep 1784915 = 2677373) B2677373
theorem B3392243 : Blo 527800 3392243 := bstep (se 1 (by rfl) ⟨2544182, by rfl⟩ : syracuseStep 3392243 = 5088365) B5088365
theorem B17712229 : Blo 527800 17712229 := bstep (se 4 (by rfl) ⟨1660521, by rfl⟩ : syracuseStep 17712229 = 3321043) B3321043
theorem B2016809 : Blo 527800 2016809 := bstep (se 2 (by rfl) ⟨756303, by rfl⟩ : syracuseStep 2016809 = 1512607) B1512607
theorem B50416775 : Blo 527800 50416775 := bstep (se 1 (by rfl) ⟨37812581, by rfl⟩ : syracuseStep 50416775 = 75625163) B75625163
theorem B1692841 : Blo 527800 1692841 := bstep (se 2 (by rfl) ⟨634815, by rfl⟩ : syracuseStep 1692841 = 1269631) B1269631
theorem B97703495 : Blo 527800 97703495 := bstep (se 1 (by rfl) ⟨73277621, by rfl⟩ : syracuseStep 97703495 = 146555243) B146555243
theorem B1529855 : Blo 527800 1529855 := bstep (se 1 (by rfl) ⟨1147391, by rfl⟩ : syracuseStep 1529855 = 2294783) B2294783
theorem B1203881 : Blo 527800 1203881 := bstep (se 2 (by rfl) ⟨451455, by rfl⟩ : syracuseStep 1203881 = 902911) B902911
theorem B10184723 : Blo 527800 10184723 := bstep (se 1 (by rfl) ⟨7638542, by rfl⟩ : syracuseStep 10184723 = 15277085) B15277085
theorem B30469283 : Blo 527800 30469283 := bstep (se 1 (by rfl) ⟨22851962, by rfl⟩ : syracuseStep 30469283 = 45703925) B45703925
theorem B2682071 : Blo 527800 2682071 := bstep (se 1 (by rfl) ⟨2011553, by rfl⟩ : syracuseStep 2682071 = 4023107) B4023107
theorem B7859429 : Blo 527800 7859429 := bstep (se 4 (by rfl) ⟨736821, by rfl⟩ : syracuseStep 7859429 = 1473643) B1473643
theorem B223803091 : Blo 527800 223803091 := bstep (se 1 (by rfl) ⟨167852318, by rfl⟩ : syracuseStep 223803091 = 335704637) B335704637
theorem B3274471 : Blo 527800 3274471 := bstep (se 1 (by rfl) ⟨2455853, by rfl⟩ : syracuseStep 3274471 = 4911707) B4911707
theorem B1341481 : Blo 527800 1341481 := bstep (se 2 (by rfl) ⟨503055, by rfl⟩ : syracuseStep 1341481 = 1006111) B1006111
theorem B1505567 : Blo 527800 1505567 := bstep (se 1 (by rfl) ⟨1129175, by rfl⟩ : syracuseStep 1505567 = 2258351) B2258351
theorem B3013595 : Blo 527800 3013595 := bstep (se 1 (by rfl) ⟨2260196, by rfl⟩ : syracuseStep 3013595 = 4520393) B4520393
theorem B9699587 : Blo 527800 9699587 := bstep (se 1 (by rfl) ⟨7274690, by rfl⟩ : syracuseStep 9699587 = 14549381) B14549381
theorem B2261495 : Blo 527800 2261495 := bstep (se 1 (by rfl) ⟨1696121, by rfl⟩ : syracuseStep 2261495 = 3392243) B3392243
theorem B1344539 : Blo 527800 1344539 := bstep (se 1 (by rfl) ⟨1008404, by rfl⟩ : syracuseStep 1344539 = 2016809) B2016809
theorem B28378511 : Blo 527800 28378511 := bstep (se 1 (by rfl) ⟨21283883, by rfl⟩ : syracuseStep 28378511 = 42567767) B42567767
theorem B527999 : Blo 527800 527999 := bstep (se 1 (by rfl) ⟨395999, by rfl⟩ : syracuseStep 527999 = 791999) B791999
theorem B1019903 : Blo 527800 1019903 := bstep (se 1 (by rfl) ⟨764927, by rfl⟩ : syracuseStep 1019903 = 1529855) B1529855
theorem B528495 : Blo 527800 528495 := bstep (se 1 (by rfl) ⟨396371, by rfl⟩ : syracuseStep 528495 = 792743) B792743
theorem B529407 : Blo 527800 529407 := bstep (se 1 (by rfl) ⟨397055, by rfl⟩ : syracuseStep 529407 = 794111) B794111
theorem B529735 : Blo 527800 529735 := bstep (se 1 (by rfl) ⟨397301, by rfl⟩ : syracuseStep 529735 = 794603) B794603
theorem B530079 : Blo 527800 530079 := bstep (se 1 (by rfl) ⟨397559, by rfl⟩ : syracuseStep 530079 = 795119) B795119
theorem B792239 : Blo 527800 792239 := bstep (se 1 (by rfl) ⟨594179, by rfl⟩ : syracuseStep 792239 = 1188359) B1188359
theorem B4528183 : Blo 527800 4528183 := bstep (se 1 (by rfl) ⟨3396137, by rfl⟩ : syracuseStep 4528183 = 6792275) B6792275
theorem B4037201 : Blo 527800 4037201 := bstep (se 2 (by rfl) ⟨1513950, by rfl⟩ : syracuseStep 4037201 = 3027901) B3027901
theorem B531111 : Blo 527800 531111 := bstep (se 1 (by rfl) ⟨398333, by rfl⟩ : syracuseStep 531111 = 796667) B796667
theorem B6789815 : Blo 527800 6789815 := bstep (se 1 (by rfl) ⟨5092361, by rfl⟩ : syracuseStep 6789815 = 10184723) B10184723
theorem B531199 : Blo 527800 531199 := bstep (se 1 (by rfl) ⟨398399, by rfl⟩ : syracuseStep 531199 = 796799) B796799
theorem B3021887 : Blo 527800 3021887 := bstep (se 1 (by rfl) ⟨2266415, by rfl⟩ : syracuseStep 3021887 = 4532831) B4532831
theorem B795647 : Blo 527800 795647 := bstep (se 1 (by rfl) ⟨596735, by rfl⟩ : syracuseStep 795647 = 1193471) B1193471
theorem B1193616485 : Blo 527800 1193616485 := bstep (se 4 (by rfl) ⟨111901545, by rfl⟩ : syracuseStep 1193616485 = 223803091) B223803091
theorem B1189331 : Blo 527800 1189331 := bstep (se 1 (by rfl) ⟨891998, by rfl⟩ : syracuseStep 1189331 = 1783997) B1783997
theorem B1189799 : Blo 527800 1189799 := bstep (se 1 (by rfl) ⟨892349, by rfl⟩ : syracuseStep 1189799 = 1784699) B1784699
theorem B2009063 : Blo 527800 2009063 := bstep (se 1 (by rfl) ⟨1506797, by rfl⟩ : syracuseStep 2009063 = 3013595) B3013595
theorem B1189943 : Blo 527800 1189943 := bstep (se 1 (by rfl) ⟨892457, by rfl⟩ : syracuseStep 1189943 = 1784915) B1784915
theorem B1191689 : Blo 527800 1191689 := bstep (se 2 (by rfl) ⟨446883, by rfl⟩ : syracuseStep 1191689 = 893767) B893767
theorem B1782269 : Blo 527800 1782269 := bstep (se 3 (by rfl) ⟨334175, by rfl⟩ : syracuseStep 1782269 = 668351) B668351
theorem B4305503 : Blo 527800 4305503 := bstep (se 1 (by rfl) ⟨3229127, by rfl⟩ : syracuseStep 4305503 = 6458255) B6458255
theorem B3062015 : Blo 527800 3062015 := bstep (se 1 (by rfl) ⟨2296511, by rfl⟩ : syracuseStep 3062015 = 4593023) B4593023
theorem B1163431 : Blo 527800 1163431 := bstep (se 1 (by rfl) ⟨872573, by rfl⟩ : syracuseStep 1163431 = 1745147) B1745147
theorem B4014845 : Blo 527800 4014845 := bstep (se 3 (by rfl) ⟨752783, by rfl⟩ : syracuseStep 4014845 = 1505567) B1505567
theorem B1788047 : Blo 527800 1788047 := bstep (se 1 (by rfl) ⟨1341035, by rfl⟩ : syracuseStep 1788047 = 2682071) B2682071
theorem B1788641 : Blo 527800 1788641 := bstep (se 2 (by rfl) ⟨670740, by rfl⟩ : syracuseStep 1788641 = 1341481) B1341481
theorem B2673647 : Blo 527800 2673647 := bstep (se 1 (by rfl) ⟨2005235, by rfl⟩ : syracuseStep 2673647 = 4010471) B4010471
theorem B8703713 : Blo 527800 8703713 := bstep (se 2 (by rfl) ⟨3263892, by rfl⟩ : syracuseStep 8703713 = 6527785) B6527785
theorem B10180727 : Blo 527800 10180727 := bstep (se 1 (by rfl) ⟨7635545, by rfl⟩ : syracuseStep 10180727 = 15271091) B15271091
theorem B23616305 : Blo 527800 23616305 := bstep (se 2 (by rfl) ⟨8856114, by rfl⟩ : syracuseStep 23616305 = 17712229) B17712229
theorem B33611183 : Blo 527800 33611183 := bstep (se 1 (by rfl) ⟨25208387, by rfl⟩ : syracuseStep 33611183 = 50416775) B50416775
theorem B1007615 : Blo 527800 1007615 := bstep (se 1 (by rfl) ⟨755711, by rfl⟩ : syracuseStep 1007615 = 1511423) B1511423
theorem B65135663 : Blo 527800 65135663 := bstep (se 1 (by rfl) ⟨48851747, by rfl⟩ : syracuseStep 65135663 = 97703495) B97703495
theorem B2257121 : Blo 527800 2257121 := bstep (se 2 (by rfl) ⟨846420, by rfl⟩ : syracuseStep 2257121 = 1692841) B1692841
theorem B20312855 : Blo 527800 20312855 := bstep (se 1 (by rfl) ⟨15234641, by rfl⟩ : syracuseStep 20312855 = 30469283) B30469283
theorem B5239619 : Blo 527800 5239619 := bstep (se 1 (by rfl) ⟨3929714, by rfl⟩ : syracuseStep 5239619 = 7859429) B7859429
theorem B6780793 : Blo 527800 6780793 := bstep (se 2 (by rfl) ⟨2542797, by rfl⟩ : syracuseStep 6780793 = 5085595) B5085595
theorem B1341431 : Blo 527800 1341431 := bstep (se 1 (by rfl) ⟨1006073, by rfl⟩ : syracuseStep 1341431 = 2012147) B2012147
theorem B17463845 : Blo 527800 17463845 := bstep (se 4 (by rfl) ⟨1637235, by rfl⟩ : syracuseStep 17463845 = 3274471) B3274471
theorem B3832535 : Blo 527800 3832535 := bstep (se 1 (by rfl) ⟨2874401, by rfl⟩ : syracuseStep 3832535 = 5748803) B5748803
theorem B3210349 : Blo 527800 3210349 := bstep (se 3 (by rfl) ⟨601940, by rfl⟩ : syracuseStep 3210349 = 1203881) B1203881
theorem B1507663 : Blo 527800 1507663 := bstep (se 1 (by rfl) ⟨1130747, by rfl⟩ : syracuseStep 1507663 = 2261495) B2261495
theorem B528159 : Blo 527800 528159 := bstep (se 1 (by rfl) ⟨396119, by rfl⟩ : syracuseStep 528159 = 792239) B792239
theorem B6787151 : Blo 527800 6787151 := bstep (se 1 (by rfl) ⟨5090363, by rfl⟩ : syracuseStep 6787151 = 10180727) B10180727
theorem B2691467 : Blo 527800 2691467 := bstep (se 1 (by rfl) ⟨2018600, by rfl⟩ : syracuseStep 2691467 = 4037201) B4037201
theorem B4526543 : Blo 527800 4526543 := bstep (se 1 (by rfl) ⟨3394907, by rfl⟩ : syracuseStep 4526543 = 6789815) B6789815
theorem B530431 : Blo 527800 530431 := bstep (se 1 (by rfl) ⟨397823, by rfl⟩ : syracuseStep 530431 = 795647) B795647
theorem B43423775 : Blo 527800 43423775 := bstep (se 1 (by rfl) ⟨32567831, by rfl⟩ : syracuseStep 43423775 = 65135663) B65135663
theorem B795744323 : Blo 527800 795744323 := bstep (se 1 (by rfl) ⟨596808242, by rfl⟩ : syracuseStep 795744323 = 1193616485) B1193616485
theorem B792887 : Blo 527800 792887 := bstep (se 1 (by rfl) ⟨594665, by rfl⟩ : syracuseStep 792887 = 1189331) B1189331
theorem B793199 : Blo 527800 793199 := bstep (se 1 (by rfl) ⟨594899, by rfl⟩ : syracuseStep 793199 = 1189799) B1189799
theorem B793295 : Blo 527800 793295 := bstep (se 1 (by rfl) ⟨594971, by rfl⟩ : syracuseStep 793295 = 1189943) B1189943
theorem B794459 : Blo 527800 794459 := bstep (se 1 (by rfl) ⟨595844, by rfl⟩ : syracuseStep 794459 = 1191689) B1191689
theorem B6037577 : Blo 527800 6037577 := bstep (se 2 (by rfl) ⟨2264091, by rfl⟩ : syracuseStep 6037577 = 4528183) B4528183
theorem B1188179 : Blo 527800 1188179 := bstep (se 1 (by rfl) ⟨891134, by rfl⟩ : syracuseStep 1188179 = 1782269) B1782269
theorem B13541903 : Blo 527800 13541903 := bstep (se 1 (by rfl) ⟨10156427, by rfl⟩ : syracuseStep 13541903 = 20312855) B20312855
theorem B894287 : Blo 527800 894287 := bstep (se 1 (by rfl) ⟨670715, by rfl⟩ : syracuseStep 894287 = 1341431) B1341431
theorem B2041343 : Blo 527800 2041343 := bstep (se 1 (by rfl) ⟨1531007, by rfl⟩ : syracuseStep 2041343 = 3062015) B3062015
theorem B11642563 : Blo 527800 11642563 := bstep (se 1 (by rfl) ⟨8731922, by rfl⟩ : syracuseStep 11642563 = 17463845) B17463845
theorem B23209901 : Blo 527800 23209901 := bstep (se 3 (by rfl) ⟨4351856, by rfl⟩ : syracuseStep 23209901 = 8703713) B8703713
theorem B6466391 : Blo 527800 6466391 := bstep (se 1 (by rfl) ⟨4849793, by rfl⟩ : syracuseStep 6466391 = 9699587) B9699587
theorem B1551241 : Blo 527800 1551241 := bstep (se 2 (by rfl) ⟨581715, by rfl⟩ : syracuseStep 1551241 = 1163431) B1163431
theorem B896359 : Blo 527800 896359 := bstep (se 1 (by rfl) ⟨672269, by rfl⟩ : syracuseStep 896359 = 1344539) B1344539
theorem B18919007 : Blo 527800 18919007 := bstep (se 1 (by rfl) ⟨14189255, by rfl⟩ : syracuseStep 18919007 = 28378511) B28378511
theorem B1192031 : Blo 527800 1192031 := bstep (se 1 (by rfl) ⟨894023, by rfl⟩ : syracuseStep 1192031 = 1788047) B1788047
theorem B1192427 : Blo 527800 1192427 := bstep (se 1 (by rfl) ⟨894320, by rfl⟩ : syracuseStep 1192427 = 1788641) B1788641
theorem B1782431 : Blo 527800 1782431 := bstep (se 1 (by rfl) ⟨1336823, by rfl⟩ : syracuseStep 1782431 = 2673647) B2673647
theorem B15744203 : Blo 527800 15744203 := bstep (se 1 (by rfl) ⟨11808152, by rfl⟩ : syracuseStep 15744203 = 23616305) B23616305
theorem B2014591 : Blo 527800 2014591 := bstep (se 1 (by rfl) ⟨1510943, by rfl⟩ : syracuseStep 2014591 = 3021887) B3021887
theorem B671743 : Blo 527800 671743 := bstep (se 1 (by rfl) ⟨503807, by rfl⟩ : syracuseStep 671743 = 1007615) B1007615
theorem B2870335 : Blo 527800 2870335 := bstep (se 1 (by rfl) ⟨2152751, by rfl⟩ : syracuseStep 2870335 = 4305503) B4305503
theorem B3493079 : Blo 527800 3493079 := bstep (se 1 (by rfl) ⟨2619809, by rfl⟩ : syracuseStep 3493079 = 5239619) B5239619
theorem B4280465 : Blo 527800 4280465 := bstep (se 2 (by rfl) ⟨1605174, by rfl⟩ : syracuseStep 4280465 = 3210349) B3210349
theorem B2676563 : Blo 527800 2676563 := bstep (se 1 (by rfl) ⟨2007422, by rfl⟩ : syracuseStep 2676563 = 4014845) B4014845
theorem B22407455 : Blo 527800 22407455 := bstep (se 1 (by rfl) ⟨16805591, by rfl⟩ : syracuseStep 22407455 = 33611183) B33611183
theorem B1339375 : Blo 527800 1339375 := bstep (se 1 (by rfl) ⟨1004531, by rfl⟩ : syracuseStep 1339375 = 2009063) B2009063
theorem B10220093 : Blo 527800 10220093 := bstep (se 3 (by rfl) ⟨1916267, by rfl⟩ : syracuseStep 10220093 = 3832535) B3832535
theorem B9041057 : Blo 527800 9041057 := bstep (se 2 (by rfl) ⟨3390396, by rfl⟩ : syracuseStep 9041057 = 6780793) B6780793
theorem B1504747 : Blo 527800 1504747 := bstep (se 1 (by rfl) ⟨1128560, by rfl⟩ : syracuseStep 1504747 = 2257121) B2257121
theorem B10878965 : Blo 527800 10878965 := bstep (se 5 (by rfl) ⟨509951, by rfl⟩ : syracuseStep 10878965 = 1019903) B1019903
theorem B37259509 : Blo 527800 37259509 := bstep (se 5 (by rfl) ⟨1746539, by rfl⟩ : syracuseStep 37259509 = 3493079) B3493079
theorem B4524767 : Blo 527800 4524767 := bstep (se 1 (by rfl) ⟨3393575, by rfl⟩ : syracuseStep 4524767 = 6787151) B6787151
theorem B2853643 : Blo 527800 2853643 := bstep (se 1 (by rfl) ⟨2140232, by rfl⟩ : syracuseStep 2853643 = 4280465) B4280465
theorem B3017695 : Blo 527800 3017695 := bstep (se 1 (by rfl) ⟨2263271, by rfl⟩ : syracuseStep 3017695 = 4526543) B4526543
theorem B528591 : Blo 527800 528591 := bstep (se 1 (by rfl) ⟨396443, by rfl⟩ : syracuseStep 528591 = 792887) B792887
theorem B528799 : Blo 527800 528799 := bstep (se 1 (by rfl) ⟨396599, by rfl⟩ : syracuseStep 528799 = 793199) B793199
theorem B528863 : Blo 527800 528863 := bstep (se 1 (by rfl) ⟨396647, by rfl⟩ : syracuseStep 528863 = 793295) B793295
theorem B529639 : Blo 527800 529639 := bstep (se 1 (by rfl) ⟨397229, by rfl⟩ : syracuseStep 529639 = 794459) B794459
theorem B792119 : Blo 527800 792119 := bstep (se 1 (by rfl) ⟨594089, by rfl⟩ : syracuseStep 792119 = 1188179) B1188179
theorem B15308453 : Blo 527800 15308453 := bstep (se 4 (by rfl) ⟨1435167, by rfl⟩ : syracuseStep 15308453 = 2870335) B2870335
theorem B596191 : Blo 527800 596191 := bstep (se 1 (by rfl) ⟨447143, by rfl⟩ : syracuseStep 596191 = 894287) B894287
theorem B15473267 : Blo 527800 15473267 := bstep (se 1 (by rfl) ⟨11604950, by rfl⟩ : syracuseStep 15473267 = 23209901) B23209901
theorem B2006329 : Blo 527800 2006329 := bstep (se 2 (by rfl) ⟨752373, by rfl⟩ : syracuseStep 2006329 = 1504747) B1504747
theorem B794687 : Blo 527800 794687 := bstep (se 1 (by rfl) ⟨596015, by rfl⟩ : syracuseStep 794687 = 1192031) B1192031
theorem B794951 : Blo 527800 794951 := bstep (se 1 (by rfl) ⟨596213, by rfl⟩ : syracuseStep 794951 = 1192427) B1192427
theorem B1188287 : Blo 527800 1188287 := bstep (se 1 (by rfl) ⟨891215, by rfl⟩ : syracuseStep 1188287 = 1782431) B1782431
theorem B10496135 : Blo 527800 10496135 := bstep (se 1 (by rfl) ⟨7872101, by rfl⟩ : syracuseStep 10496135 = 15744203) B15744203
theorem B7252643 : Blo 527800 7252643 := bstep (se 1 (by rfl) ⟨5439482, by rfl⟩ : syracuseStep 7252643 = 10878965) B10878965
theorem B895657 : Blo 527800 895657 := bstep (se 2 (by rfl) ⟨335871, by rfl⟩ : syracuseStep 895657 = 671743) B671743
theorem B2010217 : Blo 527800 2010217 := bstep (se 2 (by rfl) ⟨753831, by rfl⟩ : syracuseStep 2010217 = 1507663) B1507663
theorem B1784375 : Blo 527800 1784375 := bstep (se 1 (by rfl) ⟨1338281, by rfl⟩ : syracuseStep 1784375 = 2676563) B2676563
theorem B28949183 : Blo 527800 28949183 := bstep (se 1 (by rfl) ⟨21711887, by rfl⟩ : syracuseStep 28949183 = 43423775) B43423775
theorem B530496215 : Blo 527800 530496215 := bstep (se 1 (by rfl) ⟨397872161, by rfl⟩ : syracuseStep 530496215 = 795744323) B795744323
theorem B1195145 : Blo 527800 1195145 := bstep (se 2 (by rfl) ⟨448179, by rfl⟩ : syracuseStep 1195145 = 896359) B896359
theorem B8273285 : Blo 527800 8273285 := bstep (se 4 (by rfl) ⟨775620, by rfl⟩ : syracuseStep 8273285 = 1551241) B1551241
theorem B1785833 : Blo 527800 1785833 := bstep (se 2 (by rfl) ⟨669687, by rfl⟩ : syracuseStep 1785833 = 1339375) B1339375
theorem B9027935 : Blo 527800 9027935 := bstep (se 1 (by rfl) ⟨6770951, by rfl⟩ : syracuseStep 9027935 = 13541903) B13541903
theorem B59753213 : Blo 527800 59753213 := bstep (se 3 (by rfl) ⟨11203727, by rfl⟩ : syracuseStep 59753213 = 22407455) B22407455
theorem B1360895 : Blo 527800 1360895 := bstep (se 1 (by rfl) ⟨1020671, by rfl⟩ : syracuseStep 1360895 = 2041343) B2041343
theorem B4310927 : Blo 527800 4310927 := bstep (se 1 (by rfl) ⟨3233195, by rfl⟩ : syracuseStep 4310927 = 6466391) B6466391
theorem B15523417 : Blo 527800 15523417 := bstep (se 2 (by rfl) ⟨5821281, by rfl⟩ : syracuseStep 15523417 = 11642563) B11642563
theorem B1794311 : Blo 527800 1794311 := bstep (se 1 (by rfl) ⟨1345733, by rfl⟩ : syracuseStep 1794311 = 2691467) B2691467
theorem B4025051 : Blo 527800 4025051 := bstep (se 1 (by rfl) ⟨3018788, by rfl⟩ : syracuseStep 4025051 = 6037577) B6037577
theorem B12612671 : Blo 527800 12612671 := bstep (se 1 (by rfl) ⟨9459503, by rfl⟩ : syracuseStep 12612671 = 18919007) B18919007
theorem B6813395 : Blo 527800 6813395 := bstep (se 1 (by rfl) ⟨5110046, by rfl⟩ : syracuseStep 6813395 = 10220093) B10220093
theorem B6027371 : Blo 527800 6027371 := bstep (se 1 (by rfl) ⟨4520528, by rfl⟩ : syracuseStep 6027371 = 9041057) B9041057
theorem B2686121 : Blo 527800 2686121 := bstep (se 2 (by rfl) ⟨1007295, by rfl⟩ : syracuseStep 2686121 = 2014591) B2014591
theorem B3016511 : Blo 527800 3016511 := bstep (se 1 (by rfl) ⟨2262383, by rfl⟩ : syracuseStep 3016511 = 4524767) B4524767
theorem B49679345 : Blo 527800 49679345 := bstep (se 2 (by rfl) ⟨18629754, by rfl⟩ : syracuseStep 49679345 = 37259509) B37259509
theorem B3804857 : Blo 527800 3804857 := bstep (se 2 (by rfl) ⟨1426821, by rfl⟩ : syracuseStep 3804857 = 2853643) B2853643
theorem B528079 : Blo 527800 528079 := bstep (se 1 (by rfl) ⟨396059, by rfl⟩ : syracuseStep 528079 = 792119) B792119
theorem B529791 : Blo 527800 529791 := bstep (se 1 (by rfl) ⟨397343, by rfl⟩ : syracuseStep 529791 = 794687) B794687
theorem B529967 : Blo 527800 529967 := bstep (se 1 (by rfl) ⟨397475, by rfl⟩ : syracuseStep 529967 = 794951) B794951
theorem B792191 : Blo 527800 792191 := bstep (se 1 (by rfl) ⟨594143, by rfl⟩ : syracuseStep 792191 = 1188287) B1188287
theorem B794921 : Blo 527800 794921 := bstep (se 2 (by rfl) ⟨298095, by rfl⟩ : syracuseStep 794921 = 596191) B596191
theorem B1189583 : Blo 527800 1189583 := bstep (se 1 (by rfl) ⟨892187, by rfl⟩ : syracuseStep 1189583 = 1784375) B1784375
theorem B796763 : Blo 527800 796763 := bstep (se 1 (by rfl) ⟨597572, by rfl⟩ : syracuseStep 796763 = 1195145) B1195145
theorem B5515523 : Blo 527800 5515523 := bstep (se 1 (by rfl) ⟨4136642, by rfl⟩ : syracuseStep 5515523 = 8273285) B8273285
theorem B1190555 : Blo 527800 1190555 := bstep (se 1 (by rfl) ⟨892916, by rfl⟩ : syracuseStep 1190555 = 1785833) B1785833
theorem B1194209 : Blo 527800 1194209 := bstep (se 2 (by rfl) ⟨447828, by rfl⟩ : syracuseStep 1194209 = 895657) B895657
theorem B10205635 : Blo 527800 10205635 := bstep (se 1 (by rfl) ⟨7654226, by rfl⟩ : syracuseStep 10205635 = 15308453) B15308453
theorem B1196207 : Blo 527800 1196207 := bstep (se 1 (by rfl) ⟨897155, by rfl⟩ : syracuseStep 1196207 = 1794311) B1794311
theorem B6997423 : Blo 527800 6997423 := bstep (se 1 (by rfl) ⟨5248067, by rfl⟩ : syracuseStep 6997423 = 10496135) B10496135
theorem B4835095 : Blo 527800 4835095 := bstep (se 1 (by rfl) ⟨3626321, by rfl⟩ : syracuseStep 4835095 = 7252643) B7252643
theorem B8408447 : Blo 527800 8408447 := bstep (se 1 (by rfl) ⟨6306335, by rfl⟩ : syracuseStep 8408447 = 12612671) B12612671
theorem B4542263 : Blo 527800 4542263 := bstep (se 1 (by rfl) ⟨3406697, by rfl⟩ : syracuseStep 4542263 = 6813395) B6813395
theorem B4018247 : Blo 527800 4018247 := bstep (se 1 (by rfl) ⟨3013685, by rfl⟩ : syracuseStep 4018247 = 6027371) B6027371
theorem B2675105 : Blo 527800 2675105 := bstep (se 2 (by rfl) ⟨1003164, by rfl⟩ : syracuseStep 2675105 = 2006329) B2006329
theorem B1790747 : Blo 527800 1790747 := bstep (se 1 (by rfl) ⟨1343060, by rfl⟩ : syracuseStep 1790747 = 2686121) B2686121
theorem B20697889 : Blo 527800 20697889 := bstep (se 2 (by rfl) ⟨7761708, by rfl⟩ : syracuseStep 20697889 = 15523417) B15523417
theorem B6018623 : Blo 527800 6018623 := bstep (se 1 (by rfl) ⟨4513967, by rfl⟩ : syracuseStep 6018623 = 9027935) B9027935
theorem B39835475 : Blo 527800 39835475 := bstep (se 1 (by rfl) ⟨29876606, by rfl⟩ : syracuseStep 39835475 = 59753213) B59753213
theorem B2873951 : Blo 527800 2873951 := bstep (se 1 (by rfl) ⟨2155463, by rfl⟩ : syracuseStep 2873951 = 4310927) B4310927
theorem B3629053 : Blo 527800 3629053 := bstep (se 3 (by rfl) ⟨680447, by rfl⟩ : syracuseStep 3629053 = 1360895) B1360895
theorem B4023593 : Blo 527800 4023593 := bstep (se 2 (by rfl) ⟨1508847, by rfl⟩ : syracuseStep 4023593 = 3017695) B3017695
theorem B2680289 : Blo 527800 2680289 := bstep (se 2 (by rfl) ⟨1005108, by rfl⟩ : syracuseStep 2680289 = 2010217) B2010217
theorem B10315511 : Blo 527800 10315511 := bstep (se 1 (by rfl) ⟨7736633, by rfl⟩ : syracuseStep 10315511 = 15473267) B15473267
theorem B2683367 : Blo 527800 2683367 := bstep (se 1 (by rfl) ⟨2012525, by rfl⟩ : syracuseStep 2683367 = 4025051) B4025051
theorem B19299455 : Blo 527800 19299455 := bstep (se 1 (by rfl) ⟨14474591, by rfl⟩ : syracuseStep 19299455 = 28949183) B28949183
theorem B353664143 : Blo 527800 353664143 := bstep (se 1 (by rfl) ⟨265248107, by rfl⟩ : syracuseStep 353664143 = 530496215) B530496215
theorem B5605631 : Blo 527800 5605631 := bstep (se 1 (by rfl) ⟨4204223, by rfl⟩ : syracuseStep 5605631 = 8408447) B8408447
theorem B528127 : Blo 527800 528127 := bstep (se 1 (by rfl) ⟨396095, by rfl⟩ : syracuseStep 528127 = 792191) B792191
theorem B529947 : Blo 527800 529947 := bstep (se 1 (by rfl) ⟨397460, by rfl⟩ : syracuseStep 529947 = 794921) B794921
theorem B27597185 : Blo 527800 27597185 := bstep (se 2 (by rfl) ⟨10348944, by rfl⟩ : syracuseStep 27597185 = 20697889) B20697889
theorem B793055 : Blo 527800 793055 := bstep (se 1 (by rfl) ⟨594791, by rfl⟩ : syracuseStep 793055 = 1189583) B1189583
theorem B531175 : Blo 527800 531175 := bstep (se 1 (by rfl) ⟨398381, by rfl⟩ : syracuseStep 531175 = 796763) B796763
theorem B3677015 : Blo 527800 3677015 := bstep (se 1 (by rfl) ⟨2757761, by rfl⟩ : syracuseStep 3677015 = 5515523) B5515523
theorem B793703 : Blo 527800 793703 := bstep (se 1 (by rfl) ⟨595277, by rfl⟩ : syracuseStep 793703 = 1190555) B1190555
theorem B13607513 : Blo 527800 13607513 := bstep (se 2 (by rfl) ⟨5102817, by rfl⟩ : syracuseStep 13607513 = 10205635) B10205635
theorem B796139 : Blo 527800 796139 := bstep (se 1 (by rfl) ⟨597104, by rfl⟩ : syracuseStep 796139 = 1194209) B1194209
theorem B235776095 : Blo 527800 235776095 := bstep (se 1 (by rfl) ⟨176832071, by rfl⟩ : syracuseStep 235776095 = 353664143) B353664143
theorem B797471 : Blo 527800 797471 := bstep (se 1 (by rfl) ⟨598103, by rfl⟩ : syracuseStep 797471 = 1196207) B1196207
theorem B2011007 : Blo 527800 2011007 := bstep (se 1 (by rfl) ⟨1508255, by rfl⟩ : syracuseStep 2011007 = 3016511) B3016511
theorem B2536571 : Blo 527800 2536571 := bstep (se 1 (by rfl) ⟨1902428, by rfl⟩ : syracuseStep 2536571 = 3804857) B3804857
theorem B3028175 : Blo 527800 3028175 := bstep (se 1 (by rfl) ⟨2271131, by rfl⟩ : syracuseStep 3028175 = 4542263) B4542263
theorem B1783403 : Blo 527800 1783403 := bstep (se 1 (by rfl) ⟨1337552, by rfl⟩ : syracuseStep 1783403 = 2675105) B2675105
theorem B1193831 : Blo 527800 1193831 := bstep (se 1 (by rfl) ⟨895373, by rfl⟩ : syracuseStep 1193831 = 1790747) B1790747
theorem B4012415 : Blo 527800 4012415 := bstep (se 1 (by rfl) ⟨3009311, by rfl⟩ : syracuseStep 4012415 = 6018623) B6018623
theorem B26556983 : Blo 527800 26556983 := bstep (se 1 (by rfl) ⟨19917737, by rfl⟩ : syracuseStep 26556983 = 39835475) B39835475
theorem B1915967 : Blo 527800 1915967 := bstep (se 1 (by rfl) ⟨1436975, by rfl⟩ : syracuseStep 1915967 = 2873951) B2873951
theorem B1786859 : Blo 527800 1786859 := bstep (se 1 (by rfl) ⟨1340144, by rfl⟩ : syracuseStep 1786859 = 2680289) B2680289
theorem B1788911 : Blo 527800 1788911 := bstep (se 1 (by rfl) ⟨1341683, by rfl⟩ : syracuseStep 1788911 = 2683367) B2683367
theorem B12866303 : Blo 527800 12866303 := bstep (se 1 (by rfl) ⟨9649727, by rfl⟩ : syracuseStep 12866303 = 19299455) B19299455
theorem B4838737 : Blo 527800 4838737 := bstep (se 2 (by rfl) ⟨1814526, by rfl⟩ : syracuseStep 4838737 = 3629053) B3629053
theorem B9329897 : Blo 527800 9329897 := bstep (se 2 (by rfl) ⟨3498711, by rfl⟩ : syracuseStep 9329897 = 6997423) B6997423
theorem B33119563 : Blo 527800 33119563 := bstep (se 1 (by rfl) ⟨24839672, by rfl⟩ : syracuseStep 33119563 = 49679345) B49679345
theorem B2678831 : Blo 527800 2678831 := bstep (se 1 (by rfl) ⟨2009123, by rfl⟩ : syracuseStep 2678831 = 4018247) B4018247
theorem B2682395 : Blo 527800 2682395 := bstep (se 1 (by rfl) ⟨2011796, by rfl⟩ : syracuseStep 2682395 = 4023593) B4023593
theorem B6877007 : Blo 527800 6877007 := bstep (se 1 (by rfl) ⟨5157755, by rfl⟩ : syracuseStep 6877007 = 10315511) B10315511
theorem B25787173 : Blo 527800 25787173 := bstep (se 4 (by rfl) ⟨2417547, by rfl⟩ : syracuseStep 25787173 = 4835095) B4835095
theorem B3737087 : Blo 527800 3737087 := bstep (se 1 (by rfl) ⟨2802815, by rfl⟩ : syracuseStep 3737087 = 5605631) B5605631
theorem B528703 : Blo 527800 528703 := bstep (se 1 (by rfl) ⟨396527, by rfl⟩ : syracuseStep 528703 = 793055) B793055
theorem B529135 : Blo 527800 529135 := bstep (se 1 (by rfl) ⟨396851, by rfl⟩ : syracuseStep 529135 = 793703) B793703
theorem B530759 : Blo 527800 530759 := bstep (se 1 (by rfl) ⟨398069, by rfl⟩ : syracuseStep 530759 = 796139) B796139
theorem B531647 : Blo 527800 531647 := bstep (se 1 (by rfl) ⟨398735, by rfl⟩ : syracuseStep 531647 = 797471) B797471
theorem B34382897 : Blo 527800 34382897 := bstep (se 2 (by rfl) ⟨12893586, by rfl⟩ : syracuseStep 34382897 = 25787173) B25787173
theorem B1188935 : Blo 527800 1188935 := bstep (se 1 (by rfl) ⟨891701, by rfl⟩ : syracuseStep 1188935 = 1783403) B1783403
theorem B795887 : Blo 527800 795887 := bstep (se 1 (by rfl) ⟨596915, by rfl⟩ : syracuseStep 795887 = 1193831) B1193831
theorem B17704655 : Blo 527800 17704655 := bstep (se 1 (by rfl) ⟨13278491, by rfl⟩ : syracuseStep 17704655 = 26556983) B26556983
theorem B1191239 : Blo 527800 1191239 := bstep (se 1 (by rfl) ⟨893429, by rfl⟩ : syracuseStep 1191239 = 1786859) B1786859
theorem B1192607 : Blo 527800 1192607 := bstep (se 1 (by rfl) ⟨894455, by rfl⟩ : syracuseStep 1192607 = 1788911) B1788911
theorem B18398123 : Blo 527800 18398123 := bstep (se 1 (by rfl) ⟨13798592, by rfl⟩ : syracuseStep 18398123 = 27597185) B27597185
theorem B1785887 : Blo 527800 1785887 := bstep (se 1 (by rfl) ⟨1339415, by rfl⟩ : syracuseStep 1785887 = 2678831) B2678831
theorem B1788263 : Blo 527800 1788263 := bstep (se 1 (by rfl) ⟨1341197, by rfl⟩ : syracuseStep 1788263 = 2682395) B2682395
theorem B1691047 : Blo 527800 1691047 := bstep (se 1 (by rfl) ⟨1268285, by rfl⟩ : syracuseStep 1691047 = 2536571) B2536571
theorem B2018783 : Blo 527800 2018783 := bstep (se 1 (by rfl) ⟨1514087, by rfl⟩ : syracuseStep 2018783 = 3028175) B3028175
theorem B2674943 : Blo 527800 2674943 := bstep (se 1 (by rfl) ⟨2006207, by rfl⟩ : syracuseStep 2674943 = 4012415) B4012415
theorem B44159417 : Blo 527800 44159417 := bstep (se 2 (by rfl) ⟨16559781, by rfl⟩ : syracuseStep 44159417 = 33119563) B33119563
theorem B8577535 : Blo 527800 8577535 := bstep (se 1 (by rfl) ⟨6433151, by rfl⟩ : syracuseStep 8577535 = 12866303) B12866303
theorem B2451343 : Blo 527800 2451343 := bstep (se 1 (by rfl) ⟨1838507, by rfl⟩ : syracuseStep 2451343 = 3677015) B3677015
theorem B6219931 : Blo 527800 6219931 := bstep (se 1 (by rfl) ⟨4664948, by rfl⟩ : syracuseStep 6219931 = 9329897) B9329897
theorem B9071675 : Blo 527800 9071675 := bstep (se 1 (by rfl) ⟨6803756, by rfl⟩ : syracuseStep 9071675 = 13607513) B13607513
theorem B157184063 : Blo 527800 157184063 := bstep (se 1 (by rfl) ⟨117888047, by rfl⟩ : syracuseStep 157184063 = 235776095) B235776095
theorem B6451649 : Blo 527800 6451649 := bstep (se 2 (by rfl) ⟨2419368, by rfl⟩ : syracuseStep 6451649 = 4838737) B4838737
theorem B4584671 : Blo 527800 4584671 := bstep (se 1 (by rfl) ⟨3438503, by rfl⟩ : syracuseStep 4584671 = 6877007) B6877007
theorem B1340671 : Blo 527800 1340671 := bstep (se 1 (by rfl) ⟨1005503, by rfl⟩ : syracuseStep 1340671 = 2011007) B2011007
theorem B1277311 : Blo 527800 1277311 := bstep (se 1 (by rfl) ⟨957983, by rfl⟩ : syracuseStep 1277311 = 1915967) B1915967
theorem B11436713 : Blo 527800 11436713 := bstep (se 2 (by rfl) ⟨4288767, by rfl⟩ : syracuseStep 11436713 = 8577535) B8577535
theorem B2491391 : Blo 527800 2491391 := bstep (se 1 (by rfl) ⟨1868543, by rfl⟩ : syracuseStep 2491391 = 3737087) B3737087
theorem B1345855 : Blo 527800 1345855 := bstep (se 1 (by rfl) ⟨1009391, by rfl⟩ : syracuseStep 1345855 = 2018783) B2018783
theorem B8293241 : Blo 527800 8293241 := bstep (se 2 (by rfl) ⟨3109965, by rfl⟩ : syracuseStep 8293241 = 6219931) B6219931
theorem B792623 : Blo 527800 792623 := bstep (se 1 (by rfl) ⟨594467, by rfl⟩ : syracuseStep 792623 = 1188935) B1188935
theorem B530591 : Blo 527800 530591 := bstep (se 1 (by rfl) ⟨397943, by rfl⟩ : syracuseStep 530591 = 795887) B795887
theorem B11803103 : Blo 527800 11803103 := bstep (se 1 (by rfl) ⟨8852327, by rfl⟩ : syracuseStep 11803103 = 17704655) B17704655
theorem B794159 : Blo 527800 794159 := bstep (se 1 (by rfl) ⟨595619, by rfl⟩ : syracuseStep 794159 = 1191239) B1191239
theorem B4301099 : Blo 527800 4301099 := bstep (se 1 (by rfl) ⟨3225824, by rfl⟩ : syracuseStep 4301099 = 6451649) B6451649
theorem B795071 : Blo 527800 795071 := bstep (se 1 (by rfl) ⟨596303, by rfl⟩ : syracuseStep 795071 = 1192607) B1192607
theorem B3056447 : Blo 527800 3056447 := bstep (se 1 (by rfl) ⟨2292335, by rfl⟩ : syracuseStep 3056447 = 4584671) B4584671
theorem B12265415 : Blo 527800 12265415 := bstep (se 1 (by rfl) ⟨9199061, by rfl⟩ : syracuseStep 12265415 = 18398123) B18398123
theorem B1190591 : Blo 527800 1190591 := bstep (se 1 (by rfl) ⟨892943, by rfl⟩ : syracuseStep 1190591 = 1785887) B1785887
theorem B1192175 : Blo 527800 1192175 := bstep (se 1 (by rfl) ⟨894131, by rfl⟩ : syracuseStep 1192175 = 1788263) B1788263
theorem B1783295 : Blo 527800 1783295 := bstep (se 1 (by rfl) ⟨1337471, by rfl⟩ : syracuseStep 1783295 = 2674943) B2674943
theorem B29439611 : Blo 527800 29439611 := bstep (se 1 (by rfl) ⟨22079708, by rfl⟩ : syracuseStep 29439611 = 44159417) B44159417
theorem B22921931 : Blo 527800 22921931 := bstep (se 1 (by rfl) ⟨17191448, by rfl⟩ : syracuseStep 22921931 = 34382897) B34382897
theorem B1787561 : Blo 527800 1787561 := bstep (se 2 (by rfl) ⟨670335, by rfl⟩ : syracuseStep 1787561 = 1340671) B1340671
theorem B6047783 : Blo 527800 6047783 := bstep (se 1 (by rfl) ⟨4535837, by rfl⟩ : syracuseStep 6047783 = 9071675) B9071675
theorem B3268457 : Blo 527800 3268457 := bstep (se 2 (by rfl) ⟨1225671, by rfl⟩ : syracuseStep 3268457 = 2451343) B2451343
theorem B2254729 : Blo 527800 2254729 := bstep (se 2 (by rfl) ⟨845523, by rfl⟩ : syracuseStep 2254729 = 1691047) B1691047
theorem B104789375 : Blo 527800 104789375 := bstep (se 1 (by rfl) ⟨78592031, by rfl⟩ : syracuseStep 104789375 = 157184063) B157184063
theorem B1703081 : Blo 527800 1703081 := bstep (se 2 (by rfl) ⟨638655, by rfl⟩ : syracuseStep 1703081 = 1277311) B1277311
theorem B4031855 : Blo 527800 4031855 := bstep (se 1 (by rfl) ⟨3023891, by rfl⟩ : syracuseStep 4031855 = 6047783) B6047783
theorem B528415 : Blo 527800 528415 := bstep (se 1 (by rfl) ⟨396311, by rfl⟩ : syracuseStep 528415 = 792623) B792623
theorem B7868735 : Blo 527800 7868735 := bstep (se 1 (by rfl) ⟨5901551, by rfl⟩ : syracuseStep 7868735 = 11803103) B11803103
theorem B529439 : Blo 527800 529439 := bstep (se 1 (by rfl) ⟨397079, by rfl⟩ : syracuseStep 529439 = 794159) B794159
theorem B530047 : Blo 527800 530047 := bstep (se 1 (by rfl) ⟨397535, by rfl⟩ : syracuseStep 530047 = 795071) B795071
theorem B2037631 : Blo 527800 2037631 := bstep (se 1 (by rfl) ⟨1528223, by rfl⟩ : syracuseStep 2037631 = 3056447) B3056447
theorem B793727 : Blo 527800 793727 := bstep (se 1 (by rfl) ⟨595295, by rfl⟩ : syracuseStep 793727 = 1190591) B1190591
theorem B794783 : Blo 527800 794783 := bstep (se 1 (by rfl) ⟨596087, by rfl⟩ : syracuseStep 794783 = 1192175) B1192175
theorem B1188863 : Blo 527800 1188863 := bstep (se 1 (by rfl) ⟨891647, by rfl⟩ : syracuseStep 1188863 = 1783295) B1783295
theorem B15281287 : Blo 527800 15281287 := bstep (se 1 (by rfl) ⟨11460965, by rfl⟩ : syracuseStep 15281287 = 22921931) B22921931
theorem B1191707 : Blo 527800 1191707 := bstep (se 1 (by rfl) ⟨893780, by rfl⟩ : syracuseStep 1191707 = 1787561) B1787561
theorem B2178971 : Blo 527800 2178971 := bstep (se 1 (by rfl) ⟨1634228, by rfl⟩ : syracuseStep 2178971 = 3268457) B3268457
theorem B2867399 : Blo 527800 2867399 := bstep (se 1 (by rfl) ⟨2150549, by rfl⟩ : syracuseStep 2867399 = 4301099) B4301099
theorem B8176943 : Blo 527800 8176943 := bstep (se 1 (by rfl) ⟨6132707, by rfl⟩ : syracuseStep 8176943 = 12265415) B12265415
theorem B1135387 : Blo 527800 1135387 := bstep (se 1 (by rfl) ⟨851540, by rfl⟩ : syracuseStep 1135387 = 1703081) B1703081
theorem B7624475 : Blo 527800 7624475 := bstep (se 1 (by rfl) ⟨5718356, by rfl⟩ : syracuseStep 7624475 = 11436713) B11436713
theorem B1660927 : Blo 527800 1660927 := bstep (se 1 (by rfl) ⟨1245695, by rfl⟩ : syracuseStep 1660927 = 2491391) B2491391
theorem B5528827 : Blo 527800 5528827 := bstep (se 1 (by rfl) ⟨4146620, by rfl⟩ : syracuseStep 5528827 = 8293241) B8293241
theorem B3006305 : Blo 527800 3006305 := bstep (se 2 (by rfl) ⟨1127364, by rfl⟩ : syracuseStep 3006305 = 2254729) B2254729
theorem B1794473 : Blo 527800 1794473 := bstep (se 2 (by rfl) ⟨672927, by rfl⟩ : syracuseStep 1794473 = 1345855) B1345855
theorem B69859583 : Blo 527800 69859583 := bstep (se 1 (by rfl) ⟨52394687, by rfl⟩ : syracuseStep 69859583 = 104789375) B104789375
theorem B19626407 : Blo 527800 19626407 := bstep (se 1 (by rfl) ⟨14719805, by rfl⟩ : syracuseStep 19626407 = 29439611) B29439611
theorem B2687903 : Blo 527800 2687903 := bstep (se 1 (by rfl) ⟨2015927, by rfl⟩ : syracuseStep 2687903 = 4031855) B4031855
theorem B5245823 : Blo 527800 5245823 := bstep (se 1 (by rfl) ⟨3934367, by rfl⟩ : syracuseStep 5245823 = 7868735) B7868735
theorem B5082983 : Blo 527800 5082983 := bstep (se 1 (by rfl) ⟨3812237, by rfl⟩ : syracuseStep 5082983 = 7624475) B7624475
theorem B529151 : Blo 527800 529151 := bstep (se 1 (by rfl) ⟨396863, by rfl⟩ : syracuseStep 529151 = 793727) B793727
theorem B2004203 : Blo 527800 2004203 := bstep (se 1 (by rfl) ⟨1503152, by rfl⟩ : syracuseStep 2004203 = 3006305) B3006305
theorem B529855 : Blo 527800 529855 := bstep (se 1 (by rfl) ⟨397391, by rfl⟩ : syracuseStep 529855 = 794783) B794783
theorem B792575 : Blo 527800 792575 := bstep (se 1 (by rfl) ⟨594431, by rfl⟩ : syracuseStep 792575 = 1188863) B1188863
theorem B81500197 : Blo 527800 81500197 := bstep (se 4 (by rfl) ⟨7640643, by rfl⟩ : syracuseStep 81500197 = 15281287) B15281287
theorem B1513849 : Blo 527800 1513849 := bstep (se 2 (by rfl) ⟨567693, by rfl⟩ : syracuseStep 1513849 = 1135387) B1135387
theorem B794471 : Blo 527800 794471 := bstep (se 1 (by rfl) ⟨595853, by rfl⟩ : syracuseStep 794471 = 1191707) B1191707
theorem B46573055 : Blo 527800 46573055 := bstep (se 1 (by rfl) ⟨34929791, by rfl⟩ : syracuseStep 46573055 = 69859583) B69859583
theorem B13084271 : Blo 527800 13084271 := bstep (se 1 (by rfl) ⟨9813203, by rfl⟩ : syracuseStep 13084271 = 19626407) B19626407
theorem B1452647 : Blo 527800 1452647 := bstep (se 1 (by rfl) ⟨1089485, by rfl⟩ : syracuseStep 1452647 = 2178971) B2178971
theorem B1911599 : Blo 527800 1911599 := bstep (se 1 (by rfl) ⟨1433699, by rfl⟩ : syracuseStep 1911599 = 2867399) B2867399
theorem B5451295 : Blo 527800 5451295 := bstep (se 1 (by rfl) ⟨4088471, by rfl⟩ : syracuseStep 5451295 = 8176943) B8176943
theorem B1196315 : Blo 527800 1196315 := bstep (se 1 (by rfl) ⟨897236, by rfl⟩ : syracuseStep 1196315 = 1794473) B1794473
theorem B2214569 : Blo 527800 2214569 := bstep (se 2 (by rfl) ⟨830463, by rfl⟩ : syracuseStep 2214569 = 1660927) B1660927
theorem B2716841 : Blo 527800 2716841 := bstep (se 2 (by rfl) ⟨1018815, by rfl⟩ : syracuseStep 2716841 = 2037631) B2037631
theorem B7371769 : Blo 527800 7371769 := bstep (se 2 (by rfl) ⟨2764413, by rfl⟩ : syracuseStep 7371769 = 5528827) B5528827
theorem B1476379 : Blo 527800 1476379 := bstep (se 1 (by rfl) ⟨1107284, by rfl⟩ : syracuseStep 1476379 = 2214569) B2214569
theorem B7244909 : Blo 527800 7244909 := bstep (se 3 (by rfl) ⟨1358420, by rfl⟩ : syracuseStep 7244909 = 2716841) B2716841
theorem B528383 : Blo 527800 528383 := bstep (se 1 (by rfl) ⟨396287, by rfl⟩ : syracuseStep 528383 = 792575) B792575
theorem B529647 : Blo 527800 529647 := bstep (se 1 (by rfl) ⟨397235, by rfl⟩ : syracuseStep 529647 = 794471) B794471
theorem B8722847 : Blo 527800 8722847 := bstep (se 1 (by rfl) ⟨6542135, by rfl⟩ : syracuseStep 8722847 = 13084271) B13084271
theorem B108666929 : Blo 527800 108666929 := bstep (se 2 (by rfl) ⟨40750098, by rfl⟩ : syracuseStep 108666929 = 81500197) B81500197
theorem B797543 : Blo 527800 797543 := bstep (se 1 (by rfl) ⟨598157, by rfl⟩ : syracuseStep 797543 = 1196315) B1196315
theorem B3388655 : Blo 527800 3388655 := bstep (se 1 (by rfl) ⟨2541491, by rfl⟩ : syracuseStep 3388655 = 5082983) B5082983
theorem B31048703 : Blo 527800 31048703 := bstep (se 1 (by rfl) ⟨23286527, by rfl⟩ : syracuseStep 31048703 = 46573055) B46573055
theorem B968431 : Blo 527800 968431 := bstep (se 1 (by rfl) ⟨726323, by rfl⟩ : syracuseStep 968431 = 1452647) B1452647
theorem B2018465 : Blo 527800 2018465 := bstep (se 2 (by rfl) ⟨756924, by rfl⟩ : syracuseStep 2018465 = 1513849) B1513849
theorem B1791935 : Blo 527800 1791935 := bstep (se 1 (by rfl) ⟨1343951, by rfl⟩ : syracuseStep 1791935 = 2687903) B2687903
theorem B3497215 : Blo 527800 3497215 := bstep (se 1 (by rfl) ⟨2622911, by rfl⟩ : syracuseStep 3497215 = 5245823) B5245823
theorem B1336135 : Blo 527800 1336135 := bstep (se 1 (by rfl) ⟨1002101, by rfl⟩ : syracuseStep 1336135 = 2004203) B2004203
theorem B7268393 : Blo 527800 7268393 := bstep (se 2 (by rfl) ⟨2725647, by rfl⟩ : syracuseStep 7268393 = 5451295) B5451295
theorem B1274399 : Blo 527800 1274399 := bstep (se 1 (by rfl) ⟨955799, by rfl⟩ : syracuseStep 1274399 = 1911599) B1911599
theorem B9829025 : Blo 527800 9829025 := bstep (se 2 (by rfl) ⟨3685884, by rfl⟩ : syracuseStep 9829025 = 7371769) B7371769
theorem B1345643 : Blo 527800 1345643 := bstep (se 1 (by rfl) ⟨1009232, by rfl⟩ : syracuseStep 1345643 = 2018465) B2018465
theorem B1968505 : Blo 527800 1968505 := bstep (se 2 (by rfl) ⟨738189, by rfl⟩ : syracuseStep 1968505 = 1476379) B1476379
theorem B531695 : Blo 527800 531695 := bstep (se 1 (by rfl) ⟨398771, by rfl⟩ : syracuseStep 531695 = 797543) B797543
theorem B4662953 : Blo 527800 4662953 := bstep (se 2 (by rfl) ⟨1748607, by rfl⟩ : syracuseStep 4662953 = 3497215) B3497215
theorem B1781513 : Blo 527800 1781513 := bstep (se 2 (by rfl) ⟨668067, by rfl⟩ : syracuseStep 1781513 = 1336135) B1336135
theorem B4829939 : Blo 527800 4829939 := bstep (se 1 (by rfl) ⟨3622454, by rfl⟩ : syracuseStep 4829939 = 7244909) B7244909
theorem B1291241 : Blo 527800 1291241 := bstep (se 2 (by rfl) ⟨484215, by rfl⟩ : syracuseStep 1291241 = 968431) B968431
theorem B1194623 : Blo 527800 1194623 := bstep (se 1 (by rfl) ⟨895967, by rfl⟩ : syracuseStep 1194623 = 1791935) B1791935
theorem B20699135 : Blo 527800 20699135 := bstep (se 1 (by rfl) ⟨15524351, by rfl⟩ : syracuseStep 20699135 = 31048703) B31048703
theorem B72444619 : Blo 527800 72444619 := bstep (se 1 (by rfl) ⟨54333464, by rfl⟩ : syracuseStep 72444619 = 108666929) B108666929
theorem B23260925 : Blo 527800 23260925 := bstep (se 3 (by rfl) ⟨4361423, by rfl⟩ : syracuseStep 23260925 = 8722847) B8722847
theorem B4845595 : Blo 527800 4845595 := bstep (se 1 (by rfl) ⟨3634196, by rfl⟩ : syracuseStep 4845595 = 7268393) B7268393
theorem B849599 : Blo 527800 849599 := bstep (se 1 (by rfl) ⟨637199, by rfl⟩ : syracuseStep 849599 = 1274399) B1274399
theorem B2259103 : Blo 527800 2259103 := bstep (se 1 (by rfl) ⟨1694327, by rfl⟩ : syracuseStep 2259103 = 3388655) B3388655
theorem B6552683 : Blo 527800 6552683 := bstep (se 1 (by rfl) ⟨4914512, by rfl⟩ : syracuseStep 6552683 = 9829025) B9829025
theorem B3443309 : Blo 527800 3443309 := bstep (se 3 (by rfl) ⟨645620, by rfl⟩ : syracuseStep 3443309 = 1291241) B1291241
theorem B13799423 : Blo 527800 13799423 := bstep (se 1 (by rfl) ⟨10349567, by rfl⟩ : syracuseStep 13799423 = 20699135) B20699135
theorem B6460793 : Blo 527800 6460793 := bstep (se 2 (by rfl) ⟨2422797, by rfl⟩ : syracuseStep 6460793 = 4845595) B4845595
theorem B15507283 : Blo 527800 15507283 := bstep (se 1 (by rfl) ⟨11630462, by rfl⟩ : syracuseStep 15507283 = 23260925) B23260925
theorem B1187675 : Blo 527800 1187675 := bstep (se 1 (by rfl) ⟨890756, by rfl⟩ : syracuseStep 1187675 = 1781513) B1781513
theorem B3219959 : Blo 527800 3219959 := bstep (se 1 (by rfl) ⟨2414969, by rfl⟩ : syracuseStep 3219959 = 4829939) B4829939
theorem B566399 : Blo 527800 566399 := bstep (se 1 (by rfl) ⟨424799, by rfl⟩ : syracuseStep 566399 = 849599) B849599
theorem B796415 : Blo 527800 796415 := bstep (se 1 (by rfl) ⟨597311, by rfl⟩ : syracuseStep 796415 = 1194623) B1194623
theorem B4368455 : Blo 527800 4368455 := bstep (se 1 (by rfl) ⟨3276341, by rfl⟩ : syracuseStep 4368455 = 6552683) B6552683
theorem B897095 : Blo 527800 897095 := bstep (se 1 (by rfl) ⟨672821, by rfl⟩ : syracuseStep 897095 = 1345643) B1345643
theorem B10498693 : Blo 527800 10498693 := bstep (se 4 (by rfl) ⟨984252, by rfl⟩ : syracuseStep 10498693 = 1968505) B1968505
theorem B96592825 : Blo 527800 96592825 := bstep (se 2 (by rfl) ⟨36222309, by rfl⟩ : syracuseStep 96592825 = 72444619) B72444619
theorem B3108635 : Blo 527800 3108635 := bstep (se 1 (by rfl) ⟨2331476, by rfl⟩ : syracuseStep 3108635 = 4662953) B4662953
theorem B3012137 : Blo 527800 3012137 := bstep (se 2 (by rfl) ⟨1129551, by rfl⟩ : syracuseStep 3012137 = 2259103) B2259103
theorem B8586557 : Blo 527800 8586557 := bstep (se 3 (by rfl) ⟨1609979, by rfl⟩ : syracuseStep 8586557 = 3219959) B3219959
theorem B2295539 : Blo 527800 2295539 := bstep (se 1 (by rfl) ⟨1721654, by rfl⟩ : syracuseStep 2295539 = 3443309) B3443309
theorem B1510397 : Blo 527800 1510397 := bstep (se 3 (by rfl) ⟨283199, by rfl⟩ : syracuseStep 1510397 = 566399) B566399
theorem B791783 : Blo 527800 791783 := bstep (se 1 (by rfl) ⟨593837, by rfl⟩ : syracuseStep 791783 = 1187675) B1187675
theorem B13998257 : Blo 527800 13998257 := bstep (se 2 (by rfl) ⟨5249346, by rfl⟩ : syracuseStep 13998257 = 10498693) B10498693
theorem B530943 : Blo 527800 530943 := bstep (se 1 (by rfl) ⟨398207, by rfl⟩ : syracuseStep 530943 = 796415) B796415
theorem B2072423 : Blo 527800 2072423 := bstep (se 1 (by rfl) ⟨1554317, by rfl⟩ : syracuseStep 2072423 = 3108635) B3108635
theorem B598063 : Blo 527800 598063 := bstep (se 1 (by rfl) ⟨448547, by rfl⟩ : syracuseStep 598063 = 897095) B897095
theorem B2008091 : Blo 527800 2008091 := bstep (se 1 (by rfl) ⟨1506068, by rfl⟩ : syracuseStep 2008091 = 3012137) B3012137
theorem B128790433 : Blo 527800 128790433 := bstep (se 2 (by rfl) ⟨48296412, by rfl⟩ : syracuseStep 128790433 = 96592825) B96592825
theorem B4307195 : Blo 527800 4307195 := bstep (se 1 (by rfl) ⟨3230396, by rfl⟩ : syracuseStep 4307195 = 6460793) B6460793
theorem B9199615 : Blo 527800 9199615 := bstep (se 1 (by rfl) ⟨6899711, by rfl⟩ : syracuseStep 9199615 = 13799423) B13799423
theorem B2912303 : Blo 527800 2912303 := bstep (se 1 (by rfl) ⟨2184227, by rfl⟩ : syracuseStep 2912303 = 4368455) B4368455
theorem B20676377 : Blo 527800 20676377 := bstep (se 2 (by rfl) ⟨7753641, by rfl⟩ : syracuseStep 20676377 = 15507283) B15507283
theorem B527855 : Blo 527800 527855 := bstep (se 1 (by rfl) ⟨395891, by rfl⟩ : syracuseStep 527855 = 791783) B791783
theorem B1941535 : Blo 527800 1941535 := bstep (se 1 (by rfl) ⟨1456151, by rfl⟩ : syracuseStep 1941535 = 2912303) B2912303
theorem B12266153 : Blo 527800 12266153 := bstep (se 2 (by rfl) ⟨4599807, by rfl⟩ : syracuseStep 12266153 = 9199615) B9199615
theorem B797417 : Blo 527800 797417 := bstep (se 2 (by rfl) ⟨299031, by rfl⟩ : syracuseStep 797417 = 598063) B598063
theorem B171720577 : Blo 527800 171720577 := bstep (se 2 (by rfl) ⟨64395216, by rfl⟩ : syracuseStep 171720577 = 128790433) B128790433
theorem B2871463 : Blo 527800 2871463 := bstep (se 1 (by rfl) ⟨2153597, by rfl⟩ : syracuseStep 2871463 = 4307195) B4307195
theorem B5526461 : Blo 527800 5526461 := bstep (se 3 (by rfl) ⟨1036211, by rfl⟩ : syracuseStep 5526461 = 2072423) B2072423
theorem B13784251 : Blo 527800 13784251 := bstep (se 1 (by rfl) ⟨10338188, by rfl⟩ : syracuseStep 13784251 = 20676377) B20676377
theorem B5724371 : Blo 527800 5724371 := bstep (se 1 (by rfl) ⟨4293278, by rfl⟩ : syracuseStep 5724371 = 8586557) B8586557
theorem B1530359 : Blo 527800 1530359 := bstep (se 1 (by rfl) ⟨1147769, by rfl⟩ : syracuseStep 1530359 = 2295539) B2295539
theorem B1006931 : Blo 527800 1006931 := bstep (se 1 (by rfl) ⟨755198, by rfl⟩ : syracuseStep 1006931 = 1510397) B1510397
theorem B9332171 : Blo 527800 9332171 := bstep (se 1 (by rfl) ⟨6999128, by rfl⟩ : syracuseStep 9332171 = 13998257) B13998257
theorem B1338727 : Blo 527800 1338727 := bstep (se 1 (by rfl) ⟨1004045, by rfl⟩ : syracuseStep 1338727 = 2008091) B2008091
theorem B10354853 : Blo 527800 10354853 := bstep (se 4 (by rfl) ⟨970767, by rfl⟩ : syracuseStep 10354853 = 1941535) B1941535
theorem B1020239 : Blo 527800 1020239 := bstep (se 1 (by rfl) ⟨765179, by rfl⟩ : syracuseStep 1020239 = 1530359) B1530359
theorem B531611 : Blo 527800 531611 := bstep (se 1 (by rfl) ⟨398708, by rfl⟩ : syracuseStep 531611 = 797417) B797417
theorem B228960769 : Blo 527800 228960769 := bstep (se 2 (by rfl) ⟨85860288, by rfl⟩ : syracuseStep 228960769 = 171720577) B171720577
theorem B3684307 : Blo 527800 3684307 := bstep (se 1 (by rfl) ⟨2763230, by rfl⟩ : syracuseStep 3684307 = 5526461) B5526461
theorem B3816247 : Blo 527800 3816247 := bstep (se 1 (by rfl) ⟨2862185, by rfl⟩ : syracuseStep 3816247 = 5724371) B5724371
theorem B1784969 : Blo 527800 1784969 := bstep (se 2 (by rfl) ⟨669363, by rfl⟩ : syracuseStep 1784969 = 1338727) B1338727
theorem B8177435 : Blo 527800 8177435 := bstep (se 1 (by rfl) ⟨6133076, by rfl⟩ : syracuseStep 8177435 = 12266153) B12266153
theorem B3828617 : Blo 527800 3828617 := bstep (se 2 (by rfl) ⟨1435731, by rfl⟩ : syracuseStep 3828617 = 2871463) B2871463
theorem B6221447 : Blo 527800 6221447 := bstep (se 1 (by rfl) ⟨4666085, by rfl⟩ : syracuseStep 6221447 = 9332171) B9332171
theorem B18379001 : Blo 527800 18379001 := bstep (se 2 (by rfl) ⟨6892125, by rfl⟩ : syracuseStep 18379001 = 13784251) B13784251
theorem B2685149 : Blo 527800 2685149 := bstep (se 3 (by rfl) ⟨503465, by rfl⟩ : syracuseStep 2685149 = 1006931) B1006931
theorem B5088329 : Blo 527800 5088329 := bstep (se 2 (by rfl) ⟨1908123, by rfl⟩ : syracuseStep 5088329 = 3816247) B3816247
theorem B1189979 : Blo 527800 1189979 := bstep (se 1 (by rfl) ⟨892484, by rfl⟩ : syracuseStep 1189979 = 1784969) B1784969
theorem B5451623 : Blo 527800 5451623 := bstep (se 1 (by rfl) ⟨4088717, by rfl⟩ : syracuseStep 5451623 = 8177435) B8177435
theorem B305281025 : Blo 527800 305281025 := bstep (se 2 (by rfl) ⟨114480384, by rfl⟩ : syracuseStep 305281025 = 228960769) B228960769
theorem B4147631 : Blo 527800 4147631 := bstep (se 1 (by rfl) ⟨3110723, by rfl⟩ : syracuseStep 4147631 = 6221447) B6221447
theorem B1790099 : Blo 527800 1790099 := bstep (se 1 (by rfl) ⟨1342574, by rfl⟩ : syracuseStep 1790099 = 2685149) B2685149
theorem B6903235 : Blo 527800 6903235 := bstep (se 1 (by rfl) ⟨5177426, by rfl⟩ : syracuseStep 6903235 = 10354853) B10354853
theorem B49010669 : Blo 527800 49010669 := bstep (se 3 (by rfl) ⟨9189500, by rfl⟩ : syracuseStep 49010669 = 18379001) B18379001
theorem B680159 : Blo 527800 680159 := bstep (se 1 (by rfl) ⟨510119, by rfl⟩ : syracuseStep 680159 = 1020239) B1020239
theorem B2552411 : Blo 527800 2552411 := bstep (se 1 (by rfl) ⟨1914308, by rfl⟩ : syracuseStep 2552411 = 3828617) B3828617
theorem B4912409 : Blo 527800 4912409 := bstep (se 2 (by rfl) ⟨1842153, by rfl⟩ : syracuseStep 4912409 = 3684307) B3684307
theorem B32673779 : Blo 527800 32673779 := bstep (se 1 (by rfl) ⟨24505334, by rfl⟩ : syracuseStep 32673779 = 49010669) B49010669
theorem B793319 : Blo 527800 793319 := bstep (se 1 (by rfl) ⟨594989, by rfl⟩ : syracuseStep 793319 = 1189979) B1189979
theorem B1813757 : Blo 527800 1813757 := bstep (se 3 (by rfl) ⟨340079, by rfl⟩ : syracuseStep 1813757 = 680159) B680159
theorem B2765087 : Blo 527800 2765087 := bstep (se 1 (by rfl) ⟨2073815, by rfl⟩ : syracuseStep 2765087 = 4147631) B4147631
theorem B1193399 : Blo 527800 1193399 := bstep (se 1 (by rfl) ⟨895049, by rfl⟩ : syracuseStep 1193399 = 1790099) B1790099
theorem B3392219 : Blo 527800 3392219 := bstep (se 1 (by rfl) ⟨2544164, by rfl⟩ : syracuseStep 3392219 = 5088329) B5088329
theorem B9204313 : Blo 527800 9204313 := bstep (se 2 (by rfl) ⟨3451617, by rfl⟩ : syracuseStep 9204313 = 6903235) B6903235
theorem B3634415 : Blo 527800 3634415 := bstep (se 1 (by rfl) ⟨2725811, by rfl⟩ : syracuseStep 3634415 = 5451623) B5451623
theorem B1701607 : Blo 527800 1701607 := bstep (se 1 (by rfl) ⟨1276205, by rfl⟩ : syracuseStep 1701607 = 2552411) B2552411
theorem B3274939 : Blo 527800 3274939 := bstep (se 1 (by rfl) ⟨2456204, by rfl⟩ : syracuseStep 3274939 = 4912409) B4912409
theorem B203520683 : Blo 527800 203520683 := bstep (se 1 (by rfl) ⟨152640512, by rfl⟩ : syracuseStep 203520683 = 305281025) B305281025
theorem B2261479 : Blo 527800 2261479 := bstep (se 1 (by rfl) ⟨1696109, by rfl⟩ : syracuseStep 2261479 = 3392219) B3392219
theorem B528879 : Blo 527800 528879 := bstep (se 1 (by rfl) ⟨396659, by rfl⟩ : syracuseStep 528879 = 793319) B793319
theorem B2268809 : Blo 527800 2268809 := bstep (se 2 (by rfl) ⟨850803, by rfl⟩ : syracuseStep 2268809 = 1701607) B1701607
theorem B1843391 : Blo 527800 1843391 := bstep (se 1 (by rfl) ⟨1382543, by rfl⟩ : syracuseStep 1843391 = 2765087) B2765087
theorem B4366585 : Blo 527800 4366585 := bstep (se 2 (by rfl) ⟨1637469, by rfl⟩ : syracuseStep 4366585 = 3274939) B3274939
theorem B795599 : Blo 527800 795599 := bstep (se 1 (by rfl) ⟨596699, by rfl⟩ : syracuseStep 795599 = 1193399) B1193399
theorem B12272417 : Blo 527800 12272417 := bstep (se 2 (by rfl) ⟨4602156, by rfl⟩ : syracuseStep 12272417 = 9204313) B9204313
theorem B4836685 : Blo 527800 4836685 := bstep (se 3 (by rfl) ⟨906878, by rfl⟩ : syracuseStep 4836685 = 1813757) B1813757
theorem B135680455 : Blo 527800 135680455 := bstep (se 1 (by rfl) ⟨101760341, by rfl⟩ : syracuseStep 135680455 = 203520683) B203520683
theorem B21782519 : Blo 527800 21782519 := bstep (se 1 (by rfl) ⟨16336889, by rfl⟩ : syracuseStep 21782519 = 32673779) B32673779
theorem B2422943 : Blo 527800 2422943 := bstep (se 1 (by rfl) ⟨1817207, by rfl⟩ : syracuseStep 2422943 = 3634415) B3634415
theorem B3015305 : Blo 527800 3015305 := bstep (se 2 (by rfl) ⟨1130739, by rfl⟩ : syracuseStep 3015305 = 2261479) B2261479
theorem B1512539 : Blo 527800 1512539 := bstep (se 1 (by rfl) ⟨1134404, by rfl⟩ : syracuseStep 1512539 = 2268809) B2268809
theorem B14521679 : Blo 527800 14521679 := bstep (se 1 (by rfl) ⟨10891259, by rfl⟩ : syracuseStep 14521679 = 21782519) B21782519
theorem B530399 : Blo 527800 530399 := bstep (se 1 (by rfl) ⟨397799, by rfl⟩ : syracuseStep 530399 = 795599) B795599
theorem B1615295 : Blo 527800 1615295 := bstep (se 1 (by rfl) ⟨1211471, by rfl⟩ : syracuseStep 1615295 = 2422943) B2422943
theorem B1228927 : Blo 527800 1228927 := bstep (se 1 (by rfl) ⟨921695, by rfl⟩ : syracuseStep 1228927 = 1843391) B1843391
theorem B5822113 : Blo 527800 5822113 := bstep (se 2 (by rfl) ⟨2183292, by rfl⟩ : syracuseStep 5822113 = 4366585) B4366585
theorem B8181611 : Blo 527800 8181611 := bstep (se 1 (by rfl) ⟨6136208, by rfl⟩ : syracuseStep 8181611 = 12272417) B12272417
theorem B6448913 : Blo 527800 6448913 := bstep (se 2 (by rfl) ⟨2418342, by rfl⟩ : syracuseStep 6448913 = 4836685) B4836685
theorem B180907273 : Blo 527800 180907273 := bstep (se 2 (by rfl) ⟨67840227, by rfl⟩ : syracuseStep 180907273 = 135680455) B135680455
theorem B1638569 : Blo 527800 1638569 := bstep (se 2 (by rfl) ⟨614463, by rfl⟩ : syracuseStep 1638569 = 1228927) B1228927
theorem B241209697 : Blo 527800 241209697 := bstep (se 2 (by rfl) ⟨90453636, by rfl⟩ : syracuseStep 241209697 = 180907273) B180907273
theorem B4299275 : Blo 527800 4299275 := bstep (se 1 (by rfl) ⟨3224456, by rfl⟩ : syracuseStep 4299275 = 6448913) B6448913
theorem B2010203 : Blo 527800 2010203 := bstep (se 1 (by rfl) ⟨1507652, by rfl⟩ : syracuseStep 2010203 = 3015305) B3015305
theorem B9681119 : Blo 527800 9681119 := bstep (se 1 (by rfl) ⟨7260839, by rfl⟩ : syracuseStep 9681119 = 14521679) B14521679
theorem B5454407 : Blo 527800 5454407 := bstep (se 1 (by rfl) ⟨4090805, by rfl⟩ : syracuseStep 5454407 = 8181611) B8181611
theorem B1008359 : Blo 527800 1008359 := bstep (se 1 (by rfl) ⟨756269, by rfl⟩ : syracuseStep 1008359 = 1512539) B1512539
theorem B1076863 : Blo 527800 1076863 := bstep (se 1 (by rfl) ⟨807647, by rfl⟩ : syracuseStep 1076863 = 1615295) B1615295
theorem B7762817 : Blo 527800 7762817 := bstep (se 2 (by rfl) ⟨2911056, by rfl⟩ : syracuseStep 7762817 = 5822113) B5822113
theorem B1092379 : Blo 527800 1092379 := bstep (se 1 (by rfl) ⟨819284, by rfl⟩ : syracuseStep 1092379 = 1638569) B1638569
theorem B672239 : Blo 527800 672239 := bstep (se 1 (by rfl) ⟨504179, by rfl⟩ : syracuseStep 672239 = 1008359) B1008359
theorem B20700845 : Blo 527800 20700845 := bstep (se 3 (by rfl) ⟨3881408, by rfl⟩ : syracuseStep 20700845 = 7762817) B7762817
theorem B1435817 : Blo 527800 1435817 := bstep (se 2 (by rfl) ⟨538431, by rfl⟩ : syracuseStep 1435817 = 1076863) B1076863
theorem B321612929 : Blo 527800 321612929 := bstep (se 2 (by rfl) ⟨120604848, by rfl⟩ : syracuseStep 321612929 = 241209697) B241209697
theorem B11464733 : Blo 527800 11464733 := bstep (se 3 (by rfl) ⟨2149637, by rfl⟩ : syracuseStep 11464733 = 4299275) B4299275
theorem B1340135 : Blo 527800 1340135 := bstep (se 1 (by rfl) ⟨1005101, by rfl⟩ : syracuseStep 1340135 = 2010203) B2010203
theorem B6454079 : Blo 527800 6454079 := bstep (se 1 (by rfl) ⟨4840559, by rfl⟩ : syracuseStep 6454079 = 9681119) B9681119
theorem B3636271 : Blo 527800 3636271 := bstep (se 1 (by rfl) ⟨2727203, by rfl⟩ : syracuseStep 3636271 = 5454407) B5454407
theorem B13800563 : Blo 527800 13800563 := bstep (se 1 (by rfl) ⟨10350422, by rfl⟩ : syracuseStep 13800563 = 20700845) B20700845
theorem B214408619 : Blo 527800 214408619 := bstep (se 1 (by rfl) ⟨160806464, by rfl⟩ : syracuseStep 214408619 = 321612929) B321612929
theorem B7643155 : Blo 527800 7643155 := bstep (se 1 (by rfl) ⟨5732366, by rfl⟩ : syracuseStep 7643155 = 11464733) B11464733
theorem B893423 : Blo 527800 893423 := bstep (se 1 (by rfl) ⟨670067, by rfl⟩ : syracuseStep 893423 = 1340135) B1340135
theorem B4302719 : Blo 527800 4302719 := bstep (se 1 (by rfl) ⟨3227039, by rfl⟩ : syracuseStep 4302719 = 6454079) B6454079
theorem B1456505 : Blo 527800 1456505 := bstep (se 2 (by rfl) ⟨546189, by rfl⟩ : syracuseStep 1456505 = 1092379) B1092379
theorem B1792637 : Blo 527800 1792637 := bstep (se 3 (by rfl) ⟨336119, by rfl⟩ : syracuseStep 1792637 = 672239) B672239
theorem B19393445 : Blo 527800 19393445 := bstep (se 4 (by rfl) ⟨1818135, by rfl⟩ : syracuseStep 19393445 = 3636271) B3636271
theorem B3828845 : Blo 527800 3828845 := bstep (se 3 (by rfl) ⟨717908, by rfl⟩ : syracuseStep 3828845 = 1435817) B1435817
theorem B10190873 : Blo 527800 10190873 := bstep (se 2 (by rfl) ⟨3821577, by rfl⟩ : syracuseStep 10190873 = 7643155) B7643155
theorem B142939079 : Blo 527800 142939079 := bstep (se 1 (by rfl) ⟨107204309, by rfl⟩ : syracuseStep 142939079 = 214408619) B214408619
theorem B595615 : Blo 527800 595615 := bstep (se 1 (by rfl) ⟨446711, by rfl⟩ : syracuseStep 595615 = 893423) B893423
theorem B51715853 : Blo 527800 51715853 := bstep (se 3 (by rfl) ⟨9696722, by rfl⟩ : syracuseStep 51715853 = 19393445) B19393445
theorem B1195091 : Blo 527800 1195091 := bstep (se 1 (by rfl) ⟨896318, by rfl⟩ : syracuseStep 1195091 = 1792637) B1792637
theorem B2868479 : Blo 527800 2868479 := bstep (se 1 (by rfl) ⟨2151359, by rfl⟩ : syracuseStep 2868479 = 4302719) B4302719
theorem B971003 : Blo 527800 971003 := bstep (se 1 (by rfl) ⟨728252, by rfl⟩ : syracuseStep 971003 = 1456505) B1456505
theorem B9200375 : Blo 527800 9200375 := bstep (se 1 (by rfl) ⟨6900281, by rfl⟩ : syracuseStep 9200375 = 13800563) B13800563
theorem B2552563 : Blo 527800 2552563 := bstep (se 1 (by rfl) ⟨1914422, by rfl⟩ : syracuseStep 2552563 = 3828845) B3828845
theorem B95292719 : Blo 527800 95292719 := bstep (se 1 (by rfl) ⟨71469539, by rfl⟩ : syracuseStep 95292719 = 142939079) B142939079
theorem B34477235 : Blo 527800 34477235 := bstep (se 1 (by rfl) ⟨25857926, by rfl⟩ : syracuseStep 34477235 = 51715853) B51715853
theorem B6133583 : Blo 527800 6133583 := bstep (se 1 (by rfl) ⟨4600187, by rfl⟩ : syracuseStep 6133583 = 9200375) B9200375
theorem B794153 : Blo 527800 794153 := bstep (se 2 (by rfl) ⟨297807, by rfl⟩ : syracuseStep 794153 = 595615) B595615
theorem B796727 : Blo 527800 796727 := bstep (se 1 (by rfl) ⟨597545, by rfl⟩ : syracuseStep 796727 = 1195091) B1195091
theorem B6793915 : Blo 527800 6793915 := bstep (se 1 (by rfl) ⟨5095436, by rfl⟩ : syracuseStep 6793915 = 10190873) B10190873
theorem B1912319 : Blo 527800 1912319 := bstep (se 1 (by rfl) ⟨1434239, by rfl⟩ : syracuseStep 1912319 = 2868479) B2868479
theorem B647335 : Blo 527800 647335 := bstep (se 1 (by rfl) ⟨485501, by rfl⟩ : syracuseStep 647335 = 971003) B971003
theorem B3403417 : Blo 527800 3403417 := bstep (se 2 (by rfl) ⟨1276281, by rfl⟩ : syracuseStep 3403417 = 2552563) B2552563
theorem B529435 : Blo 527800 529435 := bstep (se 1 (by rfl) ⟨397076, by rfl⟩ : syracuseStep 529435 = 794153) B794153
theorem B531151 : Blo 527800 531151 := bstep (se 1 (by rfl) ⟨398363, by rfl⟩ : syracuseStep 531151 = 796727) B796727
theorem B3452453 : Blo 527800 3452453 := bstep (se 4 (by rfl) ⟨323667, by rfl⟩ : syracuseStep 3452453 = 647335) B647335
theorem B22984823 : Blo 527800 22984823 := bstep (se 1 (by rfl) ⟨17238617, by rfl⟩ : syracuseStep 22984823 = 34477235) B34477235
theorem B9058553 : Blo 527800 9058553 := bstep (se 2 (by rfl) ⟨3396957, by rfl⟩ : syracuseStep 9058553 = 6793915) B6793915
theorem B4537889 : Blo 527800 4537889 := bstep (se 2 (by rfl) ⟨1701708, by rfl⟩ : syracuseStep 4537889 = 3403417) B3403417
theorem B63528479 : Blo 527800 63528479 := bstep (se 1 (by rfl) ⟨47646359, by rfl⟩ : syracuseStep 63528479 = 95292719) B95292719
theorem B4089055 : Blo 527800 4089055 := bstep (se 1 (by rfl) ⟨3066791, by rfl⟩ : syracuseStep 4089055 = 6133583) B6133583
theorem B1274879 : Blo 527800 1274879 := bstep (se 1 (by rfl) ⟨956159, by rfl⟩ : syracuseStep 1274879 = 1912319) B1912319
theorem B2301635 : Blo 527800 2301635 := bstep (se 1 (by rfl) ⟨1726226, by rfl⟩ : syracuseStep 2301635 = 3452453) B3452453
theorem B6039035 : Blo 527800 6039035 := bstep (se 1 (by rfl) ⟨4529276, by rfl⟩ : syracuseStep 6039035 = 9058553) B9058553
theorem B3025259 : Blo 527800 3025259 := bstep (se 1 (by rfl) ⟨2268944, by rfl⟩ : syracuseStep 3025259 = 4537889) B4537889
theorem B5452073 : Blo 527800 5452073 := bstep (se 2 (by rfl) ⟨2044527, by rfl⟩ : syracuseStep 5452073 = 4089055) B4089055
theorem B42352319 : Blo 527800 42352319 := bstep (se 1 (by rfl) ⟨31764239, by rfl⟩ : syracuseStep 42352319 = 63528479) B63528479
theorem B15323215 : Blo 527800 15323215 := bstep (se 1 (by rfl) ⟨11492411, by rfl⟩ : syracuseStep 15323215 = 22984823) B22984823
theorem B3399677 : Blo 527800 3399677 := bstep (se 3 (by rfl) ⟨637439, by rfl⟩ : syracuseStep 3399677 = 1274879) B1274879
theorem B2266451 : Blo 527800 2266451 := bstep (se 1 (by rfl) ⟨1699838, by rfl⟩ : syracuseStep 2266451 = 3399677) B3399677
theorem B20430953 : Blo 527800 20430953 := bstep (se 2 (by rfl) ⟨7661607, by rfl⟩ : syracuseStep 20430953 = 15323215) B15323215
theorem B2016839 : Blo 527800 2016839 := bstep (se 1 (by rfl) ⟨1512629, by rfl⟩ : syracuseStep 2016839 = 3025259) B3025259
theorem B112939517 : Blo 527800 112939517 := bstep (se 3 (by rfl) ⟨21176159, by rfl⟩ : syracuseStep 112939517 = 42352319) B42352319
theorem B1534423 : Blo 527800 1534423 := bstep (se 1 (by rfl) ⟨1150817, by rfl⟩ : syracuseStep 1534423 = 2301635) B2301635
theorem B4026023 : Blo 527800 4026023 := bstep (se 1 (by rfl) ⟨3019517, by rfl⟩ : syracuseStep 4026023 = 6039035) B6039035
theorem B3634715 : Blo 527800 3634715 := bstep (se 1 (by rfl) ⟨2726036, by rfl⟩ : syracuseStep 3634715 = 5452073) B5452073
theorem B1344559 : Blo 527800 1344559 := bstep (se 1 (by rfl) ⟨1008419, by rfl⟩ : syracuseStep 1344559 = 2016839) B2016839
theorem B1510967 : Blo 527800 1510967 := bstep (se 1 (by rfl) ⟨1133225, by rfl⟩ : syracuseStep 1510967 = 2266451) B2266451
theorem B2045897 : Blo 527800 2045897 := bstep (se 2 (by rfl) ⟨767211, by rfl⟩ : syracuseStep 2045897 = 1534423) B1534423
theorem B13620635 : Blo 527800 13620635 := bstep (se 1 (by rfl) ⟨10215476, by rfl⟩ : syracuseStep 13620635 = 20430953) B20430953
theorem B75293011 : Blo 527800 75293011 := bstep (se 1 (by rfl) ⟨56469758, by rfl⟩ : syracuseStep 75293011 = 112939517) B112939517
theorem B2684015 : Blo 527800 2684015 := bstep (se 1 (by rfl) ⟨2013011, by rfl⟩ : syracuseStep 2684015 = 4026023) B4026023
theorem B2423143 : Blo 527800 2423143 := bstep (se 1 (by rfl) ⟨1817357, by rfl⟩ : syracuseStep 2423143 = 3634715) B3634715
theorem B9080423 : Blo 527800 9080423 := bstep (se 1 (by rfl) ⟨6810317, by rfl⟩ : syracuseStep 9080423 = 13620635) B13620635
theorem B3230857 : Blo 527800 3230857 := bstep (se 2 (by rfl) ⟨1211571, by rfl⟩ : syracuseStep 3230857 = 2423143) B2423143
theorem B1789343 : Blo 527800 1789343 := bstep (se 1 (by rfl) ⟨1342007, by rfl⟩ : syracuseStep 1789343 = 2684015) B2684015
theorem B1363931 : Blo 527800 1363931 := bstep (se 1 (by rfl) ⟨1022948, by rfl⟩ : syracuseStep 1363931 = 2045897) B2045897
theorem B100390681 : Blo 527800 100390681 := bstep (se 2 (by rfl) ⟨37646505, by rfl⟩ : syracuseStep 100390681 = 75293011) B75293011
theorem B1792745 : Blo 527800 1792745 := bstep (se 2 (by rfl) ⟨672279, by rfl⟩ : syracuseStep 1792745 = 1344559) B1344559
theorem B1007311 : Blo 527800 1007311 := bstep (se 1 (by rfl) ⟨755483, by rfl⟩ : syracuseStep 1007311 = 1510967) B1510967
theorem B1192895 : Blo 527800 1192895 := bstep (se 1 (by rfl) ⟨894671, by rfl⟩ : syracuseStep 1192895 = 1789343) B1789343
theorem B1195163 : Blo 527800 1195163 := bstep (se 1 (by rfl) ⟨896372, by rfl⟩ : syracuseStep 1195163 = 1792745) B1792745
theorem B6053615 : Blo 527800 6053615 := bstep (se 1 (by rfl) ⟨4540211, by rfl⟩ : syracuseStep 6053615 = 9080423) B9080423
theorem B909287 : Blo 527800 909287 := bstep (se 1 (by rfl) ⟨681965, by rfl⟩ : syracuseStep 909287 = 1363931) B1363931
theorem B17231237 : Blo 527800 17231237 := bstep (se 4 (by rfl) ⟨1615428, by rfl⟩ : syracuseStep 17231237 = 3230857) B3230857
theorem B133854241 : Blo 527800 133854241 := bstep (se 2 (by rfl) ⟨50195340, by rfl⟩ : syracuseStep 133854241 = 100390681) B100390681
theorem B1343081 : Blo 527800 1343081 := bstep (se 2 (by rfl) ⟨503655, by rfl⟩ : syracuseStep 1343081 = 1007311) B1007311
theorem B4035743 : Blo 527800 4035743 := bstep (se 1 (by rfl) ⟨3026807, by rfl⟩ : syracuseStep 4035743 = 6053615) B6053615
theorem B795263 : Blo 527800 795263 := bstep (se 1 (by rfl) ⟨596447, by rfl⟩ : syracuseStep 795263 = 1192895) B1192895
theorem B796775 : Blo 527800 796775 := bstep (se 1 (by rfl) ⟨597581, by rfl⟩ : syracuseStep 796775 = 1195163) B1195163
theorem B895387 : Blo 527800 895387 := bstep (se 1 (by rfl) ⟨671540, by rfl⟩ : syracuseStep 895387 = 1343081) B1343081
theorem B178472321 : Blo 527800 178472321 := bstep (se 2 (by rfl) ⟨66927120, by rfl⟩ : syracuseStep 178472321 = 133854241) B133854241
theorem B11487491 : Blo 527800 11487491 := bstep (se 1 (by rfl) ⟨8615618, by rfl⟩ : syracuseStep 11487491 = 17231237) B17231237
theorem B9699061 : Blo 527800 9699061 := bstep (se 5 (by rfl) ⟨454643, by rfl⟩ : syracuseStep 9699061 = 909287) B909287
theorem B118981547 : Blo 527800 118981547 := bstep (se 1 (by rfl) ⟨89236160, by rfl⟩ : syracuseStep 118981547 = 178472321) B178472321
theorem B2690495 : Blo 527800 2690495 := bstep (se 1 (by rfl) ⟨2017871, by rfl⟩ : syracuseStep 2690495 = 4035743) B4035743
theorem B530175 : Blo 527800 530175 := bstep (se 1 (by rfl) ⟨397631, by rfl⟩ : syracuseStep 530175 = 795263) B795263
theorem B531183 : Blo 527800 531183 := bstep (se 1 (by rfl) ⟨398387, by rfl⟩ : syracuseStep 531183 = 796775) B796775
theorem B1193849 : Blo 527800 1193849 := bstep (se 2 (by rfl) ⟨447693, by rfl⟩ : syracuseStep 1193849 = 895387) B895387
theorem B12932081 : Blo 527800 12932081 := bstep (se 2 (by rfl) ⟨4849530, by rfl⟩ : syracuseStep 12932081 = 9699061) B9699061
theorem B7658327 : Blo 527800 7658327 := bstep (se 1 (by rfl) ⟨5743745, by rfl⟩ : syracuseStep 7658327 = 11487491) B11487491
theorem B8621387 : Blo 527800 8621387 := bstep (se 1 (by rfl) ⟨6466040, by rfl⟩ : syracuseStep 8621387 = 12932081) B12932081
theorem B795899 : Blo 527800 795899 := bstep (se 1 (by rfl) ⟨596924, by rfl⟩ : syracuseStep 795899 = 1193849) B1193849
theorem B79321031 : Blo 527800 79321031 := bstep (se 1 (by rfl) ⟨59490773, by rfl⟩ : syracuseStep 79321031 = 118981547) B118981547
theorem B1793663 : Blo 527800 1793663 := bstep (se 1 (by rfl) ⟨1345247, by rfl⟩ : syracuseStep 1793663 = 2690495) B2690495
theorem B5105551 : Blo 527800 5105551 := bstep (se 1 (by rfl) ⟨3829163, by rfl⟩ : syracuseStep 5105551 = 7658327) B7658327
theorem B530599 : Blo 527800 530599 := bstep (se 1 (by rfl) ⟨397949, by rfl⟩ : syracuseStep 530599 = 795899) B795899
theorem B5747591 : Blo 527800 5747591 := bstep (se 1 (by rfl) ⟨4310693, by rfl⟩ : syracuseStep 5747591 = 8621387) B8621387
theorem B1195775 : Blo 527800 1195775 := bstep (se 1 (by rfl) ⟨896831, by rfl⟩ : syracuseStep 1195775 = 1793663) B1793663
theorem B6807401 : Blo 527800 6807401 := bstep (se 2 (by rfl) ⟨2552775, by rfl⟩ : syracuseStep 6807401 = 5105551) B5105551
theorem B52880687 : Blo 527800 52880687 := bstep (se 1 (by rfl) ⟨39660515, by rfl⟩ : syracuseStep 52880687 = 79321031) B79321031
theorem B797183 : Blo 527800 797183 := bstep (se 1 (by rfl) ⟨597887, by rfl⟩ : syracuseStep 797183 = 1195775) B1195775
theorem B4538267 : Blo 527800 4538267 := bstep (se 1 (by rfl) ⟨3403700, by rfl⟩ : syracuseStep 4538267 = 6807401) B6807401
theorem B35253791 : Blo 527800 35253791 := bstep (se 1 (by rfl) ⟨26440343, by rfl⟩ : syracuseStep 35253791 = 52880687) B52880687
theorem B3831727 : Blo 527800 3831727 := bstep (se 1 (by rfl) ⟨2873795, by rfl⟩ : syracuseStep 3831727 = 5747591) B5747591
theorem B531455 : Blo 527800 531455 := bstep (se 1 (by rfl) ⟨398591, by rfl⟩ : syracuseStep 531455 = 797183) B797183
theorem B23502527 : Blo 527800 23502527 := bstep (se 1 (by rfl) ⟨17626895, by rfl⟩ : syracuseStep 23502527 = 35253791) B35253791
theorem B3025511 : Blo 527800 3025511 := bstep (se 1 (by rfl) ⟨2269133, by rfl⟩ : syracuseStep 3025511 = 4538267) B4538267
theorem B5108969 : Blo 527800 5108969 := bstep (se 2 (by rfl) ⟨1915863, by rfl⟩ : syracuseStep 5108969 = 3831727) B3831727
theorem B15668351 : Blo 527800 15668351 := bstep (se 1 (by rfl) ⟨11751263, by rfl⟩ : syracuseStep 15668351 = 23502527) B23502527
theorem B2017007 : Blo 527800 2017007 := bstep (se 1 (by rfl) ⟨1512755, by rfl⟩ : syracuseStep 2017007 = 3025511) B3025511
theorem B3405979 : Blo 527800 3405979 := bstep (se 1 (by rfl) ⟨2554484, by rfl⟩ : syracuseStep 3405979 = 5108969) B5108969
theorem B1344671 : Blo 527800 1344671 := bstep (se 1 (by rfl) ⟨1008503, by rfl⟩ : syracuseStep 1344671 = 2017007) B2017007
theorem B4541305 : Blo 527800 4541305 := bstep (se 2 (by rfl) ⟨1702989, by rfl⟩ : syracuseStep 4541305 = 3405979) B3405979
theorem B10445567 : Blo 527800 10445567 := bstep (se 1 (by rfl) ⟨7834175, by rfl⟩ : syracuseStep 10445567 = 15668351) B15668351
theorem B111419381 : Blo 527800 111419381 := bstep (se 5 (by rfl) ⟨5222783, by rfl⟩ : syracuseStep 111419381 = 10445567) B10445567
theorem B896447 : Blo 527800 896447 := bstep (se 1 (by rfl) ⟨672335, by rfl⟩ : syracuseStep 896447 = 1344671) B1344671
theorem B6055073 : Blo 527800 6055073 := bstep (se 2 (by rfl) ⟨2270652, by rfl⟩ : syracuseStep 6055073 = 4541305) B4541305
theorem B4036715 : Blo 527800 4036715 := bstep (se 1 (by rfl) ⟨3027536, by rfl⟩ : syracuseStep 4036715 = 6055073) B6055073
theorem B597631 : Blo 527800 597631 := bstep (se 1 (by rfl) ⟨448223, by rfl⟩ : syracuseStep 597631 = 896447) B896447
theorem B74279587 : Blo 527800 74279587 := bstep (se 1 (by rfl) ⟨55709690, by rfl⟩ : syracuseStep 74279587 = 111419381) B111419381
theorem B2691143 : Blo 527800 2691143 := bstep (se 1 (by rfl) ⟨2018357, by rfl⟩ : syracuseStep 2691143 = 4036715) B4036715
theorem B796841 : Blo 527800 796841 := bstep (se 2 (by rfl) ⟨298815, by rfl⟩ : syracuseStep 796841 = 597631) B597631
theorem B99039449 : Blo 527800 99039449 := bstep (se 2 (by rfl) ⟨37139793, by rfl⟩ : syracuseStep 99039449 = 74279587) B74279587
theorem B531227 : Blo 527800 531227 := bstep (se 1 (by rfl) ⟨398420, by rfl⟩ : syracuseStep 531227 = 796841) B796841
theorem B1794095 : Blo 527800 1794095 := bstep (se 1 (by rfl) ⟨1345571, by rfl⟩ : syracuseStep 1794095 = 2691143) B2691143
theorem B264105197 : Blo 527800 264105197 := bstep (se 3 (by rfl) ⟨49519724, by rfl⟩ : syracuseStep 264105197 = 99039449) B99039449
theorem B176070131 : Blo 527800 176070131 := bstep (se 1 (by rfl) ⟨132052598, by rfl⟩ : syracuseStep 176070131 = 264105197) B264105197
theorem B1196063 : Blo 527800 1196063 := bstep (se 1 (by rfl) ⟨897047, by rfl⟩ : syracuseStep 1196063 = 1794095) B1794095
theorem B117380087 : Blo 527800 117380087 := bstep (se 1 (by rfl) ⟨88035065, by rfl⟩ : syracuseStep 117380087 = 176070131) B176070131
theorem B797375 : Blo 527800 797375 := bstep (se 1 (by rfl) ⟨598031, by rfl⟩ : syracuseStep 797375 = 1196063) B1196063
theorem B78253391 : Blo 527800 78253391 := bstep (se 1 (by rfl) ⟨58690043, by rfl⟩ : syracuseStep 78253391 = 117380087) B117380087
theorem B531583 : Blo 527800 531583 := bstep (se 1 (by rfl) ⟨398687, by rfl⟩ : syracuseStep 531583 = 797375) B797375
theorem B208675709 : Blo 527800 208675709 := bstep (se 3 (by rfl) ⟨39126695, by rfl⟩ : syracuseStep 208675709 = 78253391) B78253391
theorem B139117139 : Blo 527800 139117139 := bstep (se 1 (by rfl) ⟨104337854, by rfl⟩ : syracuseStep 139117139 = 208675709) B208675709
theorem B92744759 : Blo 527800 92744759 := bstep (se 1 (by rfl) ⟨69558569, by rfl⟩ : syracuseStep 92744759 = 139117139) B139117139
theorem B61829839 : Blo 527800 61829839 := bstep (se 1 (by rfl) ⟨46372379, by rfl⟩ : syracuseStep 61829839 = 92744759) B92744759
theorem B82439785 : Blo 527800 82439785 := bstep (se 2 (by rfl) ⟨30914919, by rfl⟩ : syracuseStep 82439785 = 61829839) B61829839
theorem B109919713 : Blo 527800 109919713 := bstep (se 2 (by rfl) ⟨41219892, by rfl⟩ : syracuseStep 109919713 = 82439785) B82439785
theorem B146559617 : Blo 527800 146559617 := bstep (se 2 (by rfl) ⟨54959856, by rfl⟩ : syracuseStep 146559617 = 109919713) B109919713
theorem B97706411 : Blo 527800 97706411 := bstep (se 1 (by rfl) ⟨73279808, by rfl⟩ : syracuseStep 97706411 = 146559617) B146559617
theorem B65137607 : Blo 527800 65137607 := bstep (se 1 (by rfl) ⟨48853205, by rfl⟩ : syracuseStep 65137607 = 97706411) B97706411
theorem B43425071 : Blo 527800 43425071 := bstep (se 1 (by rfl) ⟨32568803, by rfl⟩ : syracuseStep 43425071 = 65137607) B65137607
theorem B28950047 : Blo 527800 28950047 := bstep (se 1 (by rfl) ⟨21712535, by rfl⟩ : syracuseStep 28950047 = 43425071) B43425071
theorem B19300031 : Blo 527800 19300031 := bstep (se 1 (by rfl) ⟨14475023, by rfl⟩ : syracuseStep 19300031 = 28950047) B28950047
theorem B12866687 : Blo 527800 12866687 := bstep (se 1 (by rfl) ⟨9650015, by rfl⟩ : syracuseStep 12866687 = 19300031) B19300031
theorem B8577791 : Blo 527800 8577791 := bstep (se 1 (by rfl) ⟨6433343, by rfl⟩ : syracuseStep 8577791 = 12866687) B12866687
theorem B5718527 : Blo 527800 5718527 := bstep (se 1 (by rfl) ⟨4288895, by rfl⟩ : syracuseStep 5718527 = 8577791) B8577791
theorem B3812351 : Blo 527800 3812351 := bstep (se 1 (by rfl) ⟨2859263, by rfl⟩ : syracuseStep 3812351 = 5718527) B5718527
theorem B10166269 : Blo 527800 10166269 := bstep (se 3 (by rfl) ⟨1906175, by rfl⟩ : syracuseStep 10166269 = 3812351) B3812351
theorem B13555025 : Blo 527800 13555025 := bstep (se 2 (by rfl) ⟨5083134, by rfl⟩ : syracuseStep 13555025 = 10166269) B10166269
theorem B9036683 : Blo 527800 9036683 := bstep (se 1 (by rfl) ⟨6777512, by rfl⟩ : syracuseStep 9036683 = 13555025) B13555025
theorem B6024455 : Blo 527800 6024455 := bstep (se 1 (by rfl) ⟨4518341, by rfl⟩ : syracuseStep 6024455 = 9036683) B9036683
theorem B4016303 : Blo 527800 4016303 := bstep (se 1 (by rfl) ⟨3012227, by rfl⟩ : syracuseStep 4016303 = 6024455) B6024455
theorem B2677535 : Blo 527800 2677535 := bstep (se 1 (by rfl) ⟨2008151, by rfl⟩ : syracuseStep 2677535 = 4016303) B4016303
theorem B1785023 : Blo 527800 1785023 := bstep (se 1 (by rfl) ⟨1338767, by rfl⟩ : syracuseStep 1785023 = 2677535) B2677535
theorem B1190015 : Blo 527800 1190015 := bstep (se 1 (by rfl) ⟨892511, by rfl⟩ : syracuseStep 1190015 = 1785023) B1785023
theorem B793343 : Blo 527800 793343 := bstep (se 1 (by rfl) ⟨595007, by rfl⟩ : syracuseStep 793343 = 1190015) B1190015
theorem B528895 : Blo 527800 528895 := bstep (se 1 (by rfl) ⟨396671, by rfl⟩ : syracuseStep 528895 = 793343) B793343

theorem C0 (j : ℕ) (h1 : 131950 ≤ j) (h2 : j ≤ 132649) : Blo 527800 (4 * j + 3) := by
  interval_cases j
  · exact B527803
  · exact B527807
  · exact B527811
  · exact B527815
  · exact B527819
  · exact B527823
  · exact B527827
  · exact B527831
  · exact B527835
  · exact B527839
  · exact B527843
  · exact B527847
  · exact B527851
  · exact B527855
  · exact B527859
  · exact B527863
  · exact B527867
  · exact B527871
  · exact B527875
  · exact B527879
  · exact B527883
  · exact B527887
  · exact B527891
  · exact B527895
  · exact B527899
  · exact B527903
  · exact B527907
  · exact B527911
  · exact B527915
  · exact B527919
  · exact B527923
  · exact B527927
  · exact B527931
  · exact B527935
  · exact B527939
  · exact B527943
  · exact B527947
  · exact B527951
  · exact B527955
  · exact B527959
  · exact B527963
  · exact B527967
  · exact B527971
  · exact B527975
  · exact B527979
  · exact B527983
  · exact B527987
  · exact B527991
  · exact B527995
  · exact B527999
  · exact B528003
  · exact B528007
  · exact B528011
  · exact B528015
  · exact B528019
  · exact B528023
  · exact B528027
  · exact B528031
  · exact B528035
  · exact B528039
  · exact B528043
  · exact B528047
  · exact B528051
  · exact B528055
  · exact B528059
  · exact B528063
  · exact B528067
  · exact B528071
  · exact B528075
  · exact B528079
  · exact B528083
  · exact B528087
  · exact B528091
  · exact B528095
  · exact B528099
  · exact B528103
  · exact B528107
  · exact B528111
  · exact B528115
  · exact B528119
  · exact B528123
  · exact B528127
  · exact B528131
  · exact B528135
  · exact B528139
  · exact B528143
  · exact B528147
  · exact B528151
  · exact B528155
  · exact B528159
  · exact B528163
  · exact B528167
  · exact B528171
  · exact B528175
  · exact B528179
  · exact B528183
  · exact B528187
  · exact B528191
  · exact B528195
  · exact B528199
  · exact B528203
  · exact B528207
  · exact B528211
  · exact B528215
  · exact B528219
  · exact B528223
  · exact B528227
  · exact B528231
  · exact B528235
  · exact B528239
  · exact B528243
  · exact B528247
  · exact B528251
  · exact B528255
  · exact B528259
  · exact B528263
  · exact B528267
  · exact B528271
  · exact B528275
  · exact B528279
  · exact B528283
  · exact B528287
  · exact B528291
  · exact B528295
  · exact B528299
  · exact B528303
  · exact B528307
  · exact B528311
  · exact B528315
  · exact B528319
  · exact B528323
  · exact B528327
  · exact B528331
  · exact B528335
  · exact B528339
  · exact B528343
  · exact B528347
  · exact B528351
  · exact B528355
  · exact B528359
  · exact B528363
  · exact B528367
  · exact B528371
  · exact B528375
  · exact B528379
  · exact B528383
  · exact B528387
  · exact B528391
  · exact B528395
  · exact B528399
  · exact B528403
  · exact B528407
  · exact B528411
  · exact B528415
  · exact B528419
  · exact B528423
  · exact B528427
  · exact B528431
  · exact B528435
  · exact B528439
  · exact B528443
  · exact B528447
  · exact B528451
  · exact B528455
  · exact B528459
  · exact B528463
  · exact B528467
  · exact B528471
  · exact B528475
  · exact B528479
  · exact B528483
  · exact B528487
  · exact B528491
  · exact B528495
  · exact B528499
  · exact B528503
  · exact B528507
  · exact B528511
  · exact B528515
  · exact B528519
  · exact B528523
  · exact B528527
  · exact B528531
  · exact B528535
  · exact B528539
  · exact B528543
  · exact B528547
  · exact B528551
  · exact B528555
  · exact B528559
  · exact B528563
  · exact B528567
  · exact B528571
  · exact B528575
  · exact B528579
  · exact B528583
  · exact B528587
  · exact B528591
  · exact B528595
  · exact B528599
  · exact B528603
  · exact B528607
  · exact B528611
  · exact B528615
  · exact B528619
  · exact B528623
  · exact B528627
  · exact B528631
  · exact B528635
  · exact B528639
  · exact B528643
  · exact B528647
  · exact B528651
  · exact B528655
  · exact B528659
  · exact B528663
  · exact B528667
  · exact B528671
  · exact B528675
  · exact B528679
  · exact B528683
  · exact B528687
  · exact B528691
  · exact B528695
  · exact B528699
  · exact B528703
  · exact B528707
  · exact B528711
  · exact B528715
  · exact B528719
  · exact B528723
  · exact B528727
  · exact B528731
  · exact B528735
  · exact B528739
  · exact B528743
  · exact B528747
  · exact B528751
  · exact B528755
  · exact B528759
  · exact B528763
  · exact B528767
  · exact B528771
  · exact B528775
  · exact B528779
  · exact B528783
  · exact B528787
  · exact B528791
  · exact B528795
  · exact B528799
  · exact B528803
  · exact B528807
  · exact B528811
  · exact B528815
  · exact B528819
  · exact B528823
  · exact B528827
  · exact B528831
  · exact B528835
  · exact B528839
  · exact B528843
  · exact B528847
  · exact B528851
  · exact B528855
  · exact B528859
  · exact B528863
  · exact B528867
  · exact B528871
  · exact B528875
  · exact B528879
  · exact B528883
  · exact B528887
  · exact B528891
  · exact B528895
  · exact B528899
  · exact B528903
  · exact B528907
  · exact B528911
  · exact B528915
  · exact B528919
  · exact B528923
  · exact B528927
  · exact B528931
  · exact B528935
  · exact B528939
  · exact B528943
  · exact B528947
  · exact B528951
  · exact B528955
  · exact B528959
  · exact B528963
  · exact B528967
  · exact B528971
  · exact B528975
  · exact B528979
  · exact B528983
  · exact B528987
  · exact B528991
  · exact B528995
  · exact B528999
  · exact B529003
  · exact B529007
  · exact B529011
  · exact B529015
  · exact B529019
  · exact B529023
  · exact B529027
  · exact B529031
  · exact B529035
  · exact B529039
  · exact B529043
  · exact B529047
  · exact B529051
  · exact B529055
  · exact B529059
  · exact B529063
  · exact B529067
  · exact B529071
  · exact B529075
  · exact B529079
  · exact B529083
  · exact B529087
  · exact B529091
  · exact B529095
  · exact B529099
  · exact B529103
  · exact B529107
  · exact B529111
  · exact B529115
  · exact B529119
  · exact B529123
  · exact B529127
  · exact B529131
  · exact B529135
  · exact B529139
  · exact B529143
  · exact B529147
  · exact B529151
  · exact B529155
  · exact B529159
  · exact B529163
  · exact B529167
  · exact B529171
  · exact B529175
  · exact B529179
  · exact B529183
  · exact B529187
  · exact B529191
  · exact B529195
  · exact B529199
  · exact B529203
  · exact B529207
  · exact B529211
  · exact B529215
  · exact B529219
  · exact B529223
  · exact B529227
  · exact B529231
  · exact B529235
  · exact B529239
  · exact B529243
  · exact B529247
  · exact B529251
  · exact B529255
  · exact B529259
  · exact B529263
  · exact B529267
  · exact B529271
  · exact B529275
  · exact B529279
  · exact B529283
  · exact B529287
  · exact B529291
  · exact B529295
  · exact B529299
  · exact B529303
  · exact B529307
  · exact B529311
  · exact B529315
  · exact B529319
  · exact B529323
  · exact B529327
  · exact B529331
  · exact B529335
  · exact B529339
  · exact B529343
  · exact B529347
  · exact B529351
  · exact B529355
  · exact B529359
  · exact B529363
  · exact B529367
  · exact B529371
  · exact B529375
  · exact B529379
  · exact B529383
  · exact B529387
  · exact B529391
  · exact B529395
  · exact B529399
  · exact B529403
  · exact B529407
  · exact B529411
  · exact B529415
  · exact B529419
  · exact B529423
  · exact B529427
  · exact B529431
  · exact B529435
  · exact B529439
  · exact B529443
  · exact B529447
  · exact B529451
  · exact B529455
  · exact B529459
  · exact B529463
  · exact B529467
  · exact B529471
  · exact B529475
  · exact B529479
  · exact B529483
  · exact B529487
  · exact B529491
  · exact B529495
  · exact B529499
  · exact B529503
  · exact B529507
  · exact B529511
  · exact B529515
  · exact B529519
  · exact B529523
  · exact B529527
  · exact B529531
  · exact B529535
  · exact B529539
  · exact B529543
  · exact B529547
  · exact B529551
  · exact B529555
  · exact B529559
  · exact B529563
  · exact B529567
  · exact B529571
  · exact B529575
  · exact B529579
  · exact B529583
  · exact B529587
  · exact B529591
  · exact B529595
  · exact B529599
  · exact B529603
  · exact B529607
  · exact B529611
  · exact B529615
  · exact B529619
  · exact B529623
  · exact B529627
  · exact B529631
  · exact B529635
  · exact B529639
  · exact B529643
  · exact B529647
  · exact B529651
  · exact B529655
  · exact B529659
  · exact B529663
  · exact B529667
  · exact B529671
  · exact B529675
  · exact B529679
  · exact B529683
  · exact B529687
  · exact B529691
  · exact B529695
  · exact B529699
  · exact B529703
  · exact B529707
  · exact B529711
  · exact B529715
  · exact B529719
  · exact B529723
  · exact B529727
  · exact B529731
  · exact B529735
  · exact B529739
  · exact B529743
  · exact B529747
  · exact B529751
  · exact B529755
  · exact B529759
  · exact B529763
  · exact B529767
  · exact B529771
  · exact B529775
  · exact B529779
  · exact B529783
  · exact B529787
  · exact B529791
  · exact B529795
  · exact B529799
  · exact B529803
  · exact B529807
  · exact B529811
  · exact B529815
  · exact B529819
  · exact B529823
  · exact B529827
  · exact B529831
  · exact B529835
  · exact B529839
  · exact B529843
  · exact B529847
  · exact B529851
  · exact B529855
  · exact B529859
  · exact B529863
  · exact B529867
  · exact B529871
  · exact B529875
  · exact B529879
  · exact B529883
  · exact B529887
  · exact B529891
  · exact B529895
  · exact B529899
  · exact B529903
  · exact B529907
  · exact B529911
  · exact B529915
  · exact B529919
  · exact B529923
  · exact B529927
  · exact B529931
  · exact B529935
  · exact B529939
  · exact B529943
  · exact B529947
  · exact B529951
  · exact B529955
  · exact B529959
  · exact B529963
  · exact B529967
  · exact B529971
  · exact B529975
  · exact B529979
  · exact B529983
  · exact B529987
  · exact B529991
  · exact B529995
  · exact B529999
  · exact B530003
  · exact B530007
  · exact B530011
  · exact B530015
  · exact B530019
  · exact B530023
  · exact B530027
  · exact B530031
  · exact B530035
  · exact B530039
  · exact B530043
  · exact B530047
  · exact B530051
  · exact B530055
  · exact B530059
  · exact B530063
  · exact B530067
  · exact B530071
  · exact B530075
  · exact B530079
  · exact B530083
  · exact B530087
  · exact B530091
  · exact B530095
  · exact B530099
  · exact B530103
  · exact B530107
  · exact B530111
  · exact B530115
  · exact B530119
  · exact B530123
  · exact B530127
  · exact B530131
  · exact B530135
  · exact B530139
  · exact B530143
  · exact B530147
  · exact B530151
  · exact B530155
  · exact B530159
  · exact B530163
  · exact B530167
  · exact B530171
  · exact B530175
  · exact B530179
  · exact B530183
  · exact B530187
  · exact B530191
  · exact B530195
  · exact B530199
  · exact B530203
  · exact B530207
  · exact B530211
  · exact B530215
  · exact B530219
  · exact B530223
  · exact B530227
  · exact B530231
  · exact B530235
  · exact B530239
  · exact B530243
  · exact B530247
  · exact B530251
  · exact B530255
  · exact B530259
  · exact B530263
  · exact B530267
  · exact B530271
  · exact B530275
  · exact B530279
  · exact B530283
  · exact B530287
  · exact B530291
  · exact B530295
  · exact B530299
  · exact B530303
  · exact B530307
  · exact B530311
  · exact B530315
  · exact B530319
  · exact B530323
  · exact B530327
  · exact B530331
  · exact B530335
  · exact B530339
  · exact B530343
  · exact B530347
  · exact B530351
  · exact B530355
  · exact B530359
  · exact B530363
  · exact B530367
  · exact B530371
  · exact B530375
  · exact B530379
  · exact B530383
  · exact B530387
  · exact B530391
  · exact B530395
  · exact B530399
  · exact B530403
  · exact B530407
  · exact B530411
  · exact B530415
  · exact B530419
  · exact B530423
  · exact B530427
  · exact B530431
  · exact B530435
  · exact B530439
  · exact B530443
  · exact B530447
  · exact B530451
  · exact B530455
  · exact B530459
  · exact B530463
  · exact B530467
  · exact B530471
  · exact B530475
  · exact B530479
  · exact B530483
  · exact B530487
  · exact B530491
  · exact B530495
  · exact B530499
  · exact B530503
  · exact B530507
  · exact B530511
  · exact B530515
  · exact B530519
  · exact B530523
  · exact B530527
  · exact B530531
  · exact B530535
  · exact B530539
  · exact B530543
  · exact B530547
  · exact B530551
  · exact B530555
  · exact B530559
  · exact B530563
  · exact B530567
  · exact B530571
  · exact B530575
  · exact B530579
  · exact B530583
  · exact B530587
  · exact B530591
  · exact B530595
  · exact B530599

theorem C1 (j : ℕ) (h1 : 132650 ≤ j) (h2 : j ≤ 132949) : Blo 527800 (4 * j + 3) := by
  interval_cases j
  · exact B530603
  · exact B530607
  · exact B530611
  · exact B530615
  · exact B530619
  · exact B530623
  · exact B530627
  · exact B530631
  · exact B530635
  · exact B530639
  · exact B530643
  · exact B530647
  · exact B530651
  · exact B530655
  · exact B530659
  · exact B530663
  · exact B530667
  · exact B530671
  · exact B530675
  · exact B530679
  · exact B530683
  · exact B530687
  · exact B530691
  · exact B530695
  · exact B530699
  · exact B530703
  · exact B530707
  · exact B530711
  · exact B530715
  · exact B530719
  · exact B530723
  · exact B530727
  · exact B530731
  · exact B530735
  · exact B530739
  · exact B530743
  · exact B530747
  · exact B530751
  · exact B530755
  · exact B530759
  · exact B530763
  · exact B530767
  · exact B530771
  · exact B530775
  · exact B530779
  · exact B530783
  · exact B530787
  · exact B530791
  · exact B530795
  · exact B530799
  · exact B530803
  · exact B530807
  · exact B530811
  · exact B530815
  · exact B530819
  · exact B530823
  · exact B530827
  · exact B530831
  · exact B530835
  · exact B530839
  · exact B530843
  · exact B530847
  · exact B530851
  · exact B530855
  · exact B530859
  · exact B530863
  · exact B530867
  · exact B530871
  · exact B530875
  · exact B530879
  · exact B530883
  · exact B530887
  · exact B530891
  · exact B530895
  · exact B530899
  · exact B530903
  · exact B530907
  · exact B530911
  · exact B530915
  · exact B530919
  · exact B530923
  · exact B530927
  · exact B530931
  · exact B530935
  · exact B530939
  · exact B530943
  · exact B530947
  · exact B530951
  · exact B530955
  · exact B530959
  · exact B530963
  · exact B530967
  · exact B530971
  · exact B530975
  · exact B530979
  · exact B530983
  · exact B530987
  · exact B530991
  · exact B530995
  · exact B530999
  · exact B531003
  · exact B531007
  · exact B531011
  · exact B531015
  · exact B531019
  · exact B531023
  · exact B531027
  · exact B531031
  · exact B531035
  · exact B531039
  · exact B531043
  · exact B531047
  · exact B531051
  · exact B531055
  · exact B531059
  · exact B531063
  · exact B531067
  · exact B531071
  · exact B531075
  · exact B531079
  · exact B531083
  · exact B531087
  · exact B531091
  · exact B531095
  · exact B531099
  · exact B531103
  · exact B531107
  · exact B531111
  · exact B531115
  · exact B531119
  · exact B531123
  · exact B531127
  · exact B531131
  · exact B531135
  · exact B531139
  · exact B531143
  · exact B531147
  · exact B531151
  · exact B531155
  · exact B531159
  · exact B531163
  · exact B531167
  · exact B531171
  · exact B531175
  · exact B531179
  · exact B531183
  · exact B531187
  · exact B531191
  · exact B531195
  · exact B531199
  · exact B531203
  · exact B531207
  · exact B531211
  · exact B531215
  · exact B531219
  · exact B531223
  · exact B531227
  · exact B531231
  · exact B531235
  · exact B531239
  · exact B531243
  · exact B531247
  · exact B531251
  · exact B531255
  · exact B531259
  · exact B531263
  · exact B531267
  · exact B531271
  · exact B531275
  · exact B531279
  · exact B531283
  · exact B531287
  · exact B531291
  · exact B531295
  · exact B531299
  · exact B531303
  · exact B531307
  · exact B531311
  · exact B531315
  · exact B531319
  · exact B531323
  · exact B531327
  · exact B531331
  · exact B531335
  · exact B531339
  · exact B531343
  · exact B531347
  · exact B531351
  · exact B531355
  · exact B531359
  · exact B531363
  · exact B531367
  · exact B531371
  · exact B531375
  · exact B531379
  · exact B531383
  · exact B531387
  · exact B531391
  · exact B531395
  · exact B531399
  · exact B531403
  · exact B531407
  · exact B531411
  · exact B531415
  · exact B531419
  · exact B531423
  · exact B531427
  · exact B531431
  · exact B531435
  · exact B531439
  · exact B531443
  · exact B531447
  · exact B531451
  · exact B531455
  · exact B531459
  · exact B531463
  · exact B531467
  · exact B531471
  · exact B531475
  · exact B531479
  · exact B531483
  · exact B531487
  · exact B531491
  · exact B531495
  · exact B531499
  · exact B531503
  · exact B531507
  · exact B531511
  · exact B531515
  · exact B531519
  · exact B531523
  · exact B531527
  · exact B531531
  · exact B531535
  · exact B531539
  · exact B531543
  · exact B531547
  · exact B531551
  · exact B531555
  · exact B531559
  · exact B531563
  · exact B531567
  · exact B531571
  · exact B531575
  · exact B531579
  · exact B531583
  · exact B531587
  · exact B531591
  · exact B531595
  · exact B531599
  · exact B531603
  · exact B531607
  · exact B531611
  · exact B531615
  · exact B531619
  · exact B531623
  · exact B531627
  · exact B531631
  · exact B531635
  · exact B531639
  · exact B531643
  · exact B531647
  · exact B531651
  · exact B531655
  · exact B531659
  · exact B531663
  · exact B531667
  · exact B531671
  · exact B531675
  · exact B531679
  · exact B531683
  · exact B531687
  · exact B531691
  · exact B531695
  · exact B531699
  · exact B531703
  · exact B531707
  · exact B531711
  · exact B531715
  · exact B531719
  · exact B531723
  · exact B531727
  · exact B531731
  · exact B531735
  · exact B531739
  · exact B531743
  · exact B531747
  · exact B531751
  · exact B531755
  · exact B531759
  · exact B531763
  · exact B531767
  · exact B531771
  · exact B531775
  · exact B531779
  · exact B531783
  · exact B531787
  · exact B531791
  · exact B531795
  · exact B531799

theorem solution (m : ℕ) (hlo : 527800 ≤ m) (hhi : m ≤ 531800) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 131950 ≤ j := by omega
    have hj2 : j ≤ 132949 := by omega
    have hb : Blo 527800 (4 * j + 3) := by
      rcases Nat.lt_or_ge j 132650 with hc0 | hc0
      · exact C0 j (by omega) (by omega)
      exact C1 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
