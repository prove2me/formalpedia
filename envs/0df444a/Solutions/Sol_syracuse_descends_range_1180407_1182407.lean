-- Prove2me | solution 1 for syracuse_descends_range_1180407_1182407
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-09T22:10:32.476979+00:00
-- url     : https://prove2.me/submissions/2cb976c5-c0e4-4aa6-b5df-7ecbd8cfa240

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


theorem B1892413 : Blo 1180407 1892413 := bbase (se 3 (by rfl) ⟨354827, by rfl⟩ : syracuseStep 1892413 = 709655) (by norm_num)
theorem B5980229 : Blo 1180407 5980229 := bbase (se 4 (by rfl) ⟨560646, by rfl⟩ : syracuseStep 5980229 = 1121293) (by norm_num)
theorem B3989573 : Blo 1180407 3989573 := bbase (se 4 (by rfl) ⟨374022, by rfl⟩ : syracuseStep 3989573 = 748045) (by norm_num)
theorem B16162901 : Blo 1180407 16162901 := bbase (se 8 (by rfl) ⟨94704, by rfl⟩ : syracuseStep 16162901 = 189409) (by norm_num)
theorem B2695349 : Blo 1180407 2695349 := bbase (se 5 (by rfl) ⟨126344, by rfl⟩ : syracuseStep 2695349 = 252689) (by norm_num)
theorem B2990317 : Blo 1180407 2990317 := bbase (se 3 (by rfl) ⟨560684, by rfl⟩ : syracuseStep 2990317 = 1121369) (by norm_num)
theorem B1515781 : Blo 1180407 1515781 := bbase (se 4 (by rfl) ⟨142104, by rfl⟩ : syracuseStep 1515781 = 284209) (by norm_num)
theorem B2130205 : Blo 1180407 2130205 := bbase (se 3 (by rfl) ⟨399413, by rfl⟩ : syracuseStep 2130205 = 798827) (by norm_num)
theorem B1261865 : Blo 1180407 1261865 := bbase (se 2 (by rfl) ⟨473199, by rfl⟩ : syracuseStep 1261865 = 946399) (by norm_num)
theorem B6472021 : Blo 1180407 6472021 := bbase (se 10 (by rfl) ⟨9480, by rfl⟩ : syracuseStep 6472021 = 18961) (by norm_num)
theorem B2990429 : Blo 1180407 2990429 := bbase (se 3 (by rfl) ⟨560705, by rfl⟩ : syracuseStep 2990429 = 1121411) (by norm_num)
theorem B2130293 : Blo 1180407 2130293 := bbase (se 5 (by rfl) ⟨99857, by rfl⟩ : syracuseStep 2130293 = 199715) (by norm_num)
theorem B2130349 : Blo 1180407 2130349 := bbase (se 3 (by rfl) ⟨399440, by rfl⟩ : syracuseStep 2130349 = 798881) (by norm_num)
theorem B1515989 : Blo 1180407 1515989 := bbase (se 7 (by rfl) ⟨17765, by rfl⟩ : syracuseStep 1515989 = 35531) (by norm_num)
theorem B1597909 : Blo 1180407 1597909 := bbase (se 7 (by rfl) ⟨18725, by rfl⟩ : syracuseStep 1597909 = 37451) (by norm_num)
theorem B3990005 : Blo 1180407 3990005 := bbase (se 5 (by rfl) ⟨187031, by rfl⟩ : syracuseStep 3990005 = 374063) (by norm_num)
theorem B3785237 : Blo 1180407 3785237 := bbase (se 6 (by rfl) ⟨88716, by rfl⟩ : syracuseStep 3785237 = 177433) (by norm_num)
theorem B2990621 : Blo 1180407 2990621 := bbase (se 3 (by rfl) ⟨560741, by rfl⟩ : syracuseStep 2990621 = 1121483) (by norm_num)
theorem B1892965 : Blo 1180407 1892965 := bbase (se 4 (by rfl) ⟨177465, by rfl⟩ : syracuseStep 1892965 = 354931) (by norm_num)
theorem B5186261 : Blo 1180407 5186261 := bbase (se 7 (by rfl) ⟨60776, by rfl⟩ : syracuseStep 5186261 = 121553) (by norm_num)
theorem B1262309 : Blo 1180407 1262309 := bbase (se 4 (by rfl) ⟨118341, by rfl⟩ : syracuseStep 1262309 = 236683) (by norm_num)
theorem B2523901 : Blo 1180407 2523901 := bbase (se 3 (by rfl) ⟨473231, by rfl⟩ : syracuseStep 2523901 = 946463) (by norm_num)
theorem B1893221 : Blo 1180407 1893221 := bbase (se 4 (by rfl) ⟨177489, by rfl⟩ : syracuseStep 1893221 = 354979) (by norm_num)
theorem B1327981 : Blo 1180407 1327981 := bbase (se 3 (by rfl) ⟨248996, by rfl⟩ : syracuseStep 1327981 = 497993) (by norm_num)
theorem B2990965 : Blo 1180407 2990965 := bbase (se 5 (by rfl) ⟨140201, by rfl⟩ : syracuseStep 2990965 = 280403) (by norm_num)
theorem B1328017 : Blo 1180407 1328017 := bbase (se 2 (by rfl) ⟨498006, by rfl⟩ : syracuseStep 1328017 = 996013) (by norm_num)
theorem B3990437 : Blo 1180407 3990437 := bbase (se 4 (by rfl) ⟨374103, by rfl⟩ : syracuseStep 3990437 = 748207) (by norm_num)
theorem B1328053 : Blo 1180407 1328053 := bbase (se 5 (by rfl) ⟨62252, by rfl⟩ : syracuseStep 1328053 = 124505) (by norm_num)
theorem B1328089 : Blo 1180407 1328089 := bbase (se 2 (by rfl) ⟨498033, by rfl⟩ : syracuseStep 1328089 = 996067) (by norm_num)
theorem B1262557 : Blo 1180407 1262557 := bbase (se 3 (by rfl) ⟨236729, by rfl⟩ : syracuseStep 1262557 = 473459) (by norm_num)
theorem B2991077 : Blo 1180407 2991077 := bbase (se 4 (by rfl) ⟨280413, by rfl⟩ : syracuseStep 2991077 = 560827) (by norm_num)
theorem B2556917 : Blo 1180407 2556917 := bbase (se 5 (by rfl) ⟨119855, by rfl⟩ : syracuseStep 2556917 = 239711) (by norm_num)
theorem B1328125 : Blo 1180407 1328125 := bbase (se 3 (by rfl) ⟨249023, by rfl⟩ : syracuseStep 1328125 = 498047) (by norm_num)
theorem B1328161 : Blo 1180407 1328161 := bbase (se 2 (by rfl) ⟨498060, by rfl⟩ : syracuseStep 1328161 = 996121) (by norm_num)
theorem B1328197 : Blo 1180407 1328197 := bbase (se 4 (by rfl) ⟨124518, by rfl⟩ : syracuseStep 1328197 = 249037) (by norm_num)
theorem B1328233 : Blo 1180407 1328233 := bbase (se 2 (by rfl) ⟨498087, by rfl⟩ : syracuseStep 1328233 = 996175) (by norm_num)
theorem B2524277 : Blo 1180407 2524277 := bbase (se 5 (by rfl) ⟨118325, by rfl⟩ : syracuseStep 2524277 = 236651) (by norm_num)
theorem B1770629 : Blo 1180407 1770629 := bbase (se 4 (by rfl) ⟨165996, by rfl⟩ : syracuseStep 1770629 = 331993) (by norm_num)
theorem B1328269 : Blo 1180407 1328269 := bbase (se 3 (by rfl) ⟨249050, by rfl⟩ : syracuseStep 1328269 = 498101) (by norm_num)
theorem B1770653 : Blo 1180407 1770653 := bbase (se 3 (by rfl) ⟨331997, by rfl⟩ : syracuseStep 1770653 = 663995) (by norm_num)
theorem B2991269 : Blo 1180407 2991269 := bbase (se 4 (by rfl) ⟨280431, by rfl⟩ : syracuseStep 2991269 = 560863) (by norm_num)
theorem B1328305 : Blo 1180407 1328305 := bbase (se 2 (by rfl) ⟨498114, by rfl⟩ : syracuseStep 1328305 = 996229) (by norm_num)
theorem B1770677 : Blo 1180407 1770677 := bbase (se 5 (by rfl) ⟨83000, by rfl⟩ : syracuseStep 1770677 = 166001) (by norm_num)
theorem B1770701 : Blo 1180407 1770701 := bbase (se 3 (by rfl) ⟨332006, by rfl⟩ : syracuseStep 1770701 = 664013) (by norm_num)
theorem B1328341 : Blo 1180407 1328341 := bbase (se 7 (by rfl) ⟨15566, by rfl⟩ : syracuseStep 1328341 = 31133) (by norm_num)
theorem B1770725 : Blo 1180407 1770725 := bbase (se 4 (by rfl) ⟨166005, by rfl⟩ : syracuseStep 1770725 = 332011) (by norm_num)
theorem B1328377 : Blo 1180407 1328377 := bbase (se 2 (by rfl) ⟨498141, by rfl⟩ : syracuseStep 1328377 = 996283) (by norm_num)
theorem B1770749 : Blo 1180407 1770749 := bbase (se 3 (by rfl) ⟨332015, by rfl⟩ : syracuseStep 1770749 = 664031) (by norm_num)
theorem B1770773 : Blo 1180407 1770773 := bbase (se 6 (by rfl) ⟨41502, by rfl⟩ : syracuseStep 1770773 = 83005) (by norm_num)
theorem B1991965 : Blo 1180407 1991965 := bbase (se 3 (by rfl) ⟨373493, by rfl⟩ : syracuseStep 1991965 = 746987) (by norm_num)
theorem B1328413 : Blo 1180407 1328413 := bbase (se 3 (by rfl) ⟨249077, by rfl⟩ : syracuseStep 1328413 = 498155) (by norm_num)
theorem B1770797 : Blo 1180407 1770797 := bbase (se 3 (by rfl) ⟨332024, by rfl⟩ : syracuseStep 1770797 = 664049) (by norm_num)
theorem B1328449 : Blo 1180407 1328449 := bbase (se 2 (by rfl) ⟨498168, by rfl⟩ : syracuseStep 1328449 = 996337) (by norm_num)
theorem B1770821 : Blo 1180407 1770821 := bbase (se 4 (by rfl) ⟨166014, by rfl⟩ : syracuseStep 1770821 = 332029) (by norm_num)
theorem B5981525 : Blo 1180407 5981525 := bbase (se 12 (by rfl) ⟨2190, by rfl⟩ : syracuseStep 5981525 = 4381) (by norm_num)
theorem B1770845 : Blo 1180407 1770845 := bbase (se 3 (by rfl) ⟨332033, by rfl⟩ : syracuseStep 1770845 = 664067) (by norm_num)
theorem B1328485 : Blo 1180407 1328485 := bbase (se 4 (by rfl) ⟨124545, by rfl⟩ : syracuseStep 1328485 = 249091) (by norm_num)
theorem B1992053 : Blo 1180407 1992053 := bbase (se 5 (by rfl) ⟨93377, by rfl⟩ : syracuseStep 1992053 = 186755) (by norm_num)
theorem B1770869 : Blo 1180407 1770869 := bbase (se 5 (by rfl) ⟨83009, by rfl⟩ : syracuseStep 1770869 = 166019) (by norm_num)
theorem B1328521 : Blo 1180407 1328521 := bbase (se 2 (by rfl) ⟨498195, by rfl⟩ : syracuseStep 1328521 = 996391) (by norm_num)
theorem B1770893 : Blo 1180407 1770893 := bbase (se 3 (by rfl) ⟨332042, by rfl⟩ : syracuseStep 1770893 = 664085) (by norm_num)
theorem B1213849 : Blo 1180407 1213849 := bbase (se 2 (by rfl) ⟨455193, by rfl⟩ : syracuseStep 1213849 = 910387) (by norm_num)
theorem B1770917 : Blo 1180407 1770917 := bbase (se 4 (by rfl) ⟨166023, by rfl⟩ : syracuseStep 1770917 = 332047) (by norm_num)
theorem B5047717 : Blo 1180407 5047717 := bbase (se 4 (by rfl) ⟨473223, by rfl⟩ : syracuseStep 5047717 = 946447) (by norm_num)
theorem B1328557 : Blo 1180407 1328557 := bbase (se 3 (by rfl) ⟨249104, by rfl⟩ : syracuseStep 1328557 = 498209) (by norm_num)
theorem B4482485 : Blo 1180407 4482485 := bbase (se 5 (by rfl) ⟨210116, by rfl⟩ : syracuseStep 4482485 = 420233) (by norm_num)
theorem B5047733 : Blo 1180407 5047733 := bbase (se 5 (by rfl) ⟨236612, by rfl⟩ : syracuseStep 5047733 = 473225) (by norm_num)
theorem B1770941 : Blo 1180407 1770941 := bbase (se 3 (by rfl) ⟨332051, by rfl⟩ : syracuseStep 1770941 = 664103) (by norm_num)
theorem B1328593 : Blo 1180407 1328593 := bbase (se 2 (by rfl) ⟨498222, by rfl⟩ : syracuseStep 1328593 = 996445) (by norm_num)
theorem B1770965 : Blo 1180407 1770965 := bbase (se 7 (by rfl) ⟨20753, by rfl⟩ : syracuseStep 1770965 = 41507) (by norm_num)
theorem B1680869 : Blo 1180407 1680869 := bbase (se 4 (by rfl) ⟨157581, by rfl⟩ : syracuseStep 1680869 = 315163) (by norm_num)
theorem B1770989 : Blo 1180407 1770989 := bbase (se 3 (by rfl) ⟨332060, by rfl⟩ : syracuseStep 1770989 = 664121) (by norm_num)
theorem B1992181 : Blo 1180407 1992181 := bbase (se 5 (by rfl) ⟨93383, by rfl⟩ : syracuseStep 1992181 = 186767) (by norm_num)
theorem B1328629 : Blo 1180407 1328629 := bbase (se 5 (by rfl) ⟨62279, by rfl⟩ : syracuseStep 1328629 = 124559) (by norm_num)
theorem B2991613 : Blo 1180407 2991613 := bbase (se 3 (by rfl) ⟨560927, by rfl⟩ : syracuseStep 2991613 = 1121855) (by norm_num)
theorem B1771013 : Blo 1180407 1771013 := bbase (se 4 (by rfl) ⟨166032, by rfl⟩ : syracuseStep 1771013 = 332065) (by norm_num)
theorem B1328665 : Blo 1180407 1328665 := bbase (se 2 (by rfl) ⟨498249, by rfl⟩ : syracuseStep 1328665 = 996499) (by norm_num)
theorem B1771037 : Blo 1180407 1771037 := bbase (se 3 (by rfl) ⟨332069, by rfl⟩ : syracuseStep 1771037 = 664139) (by norm_num)
theorem B1893925 : Blo 1180407 1893925 := bbase (se 4 (by rfl) ⟨177555, by rfl⟩ : syracuseStep 1893925 = 355111) (by norm_num)
theorem B1418801 : Blo 1180407 1418801 := bbase (se 2 (by rfl) ⟨532050, by rfl⟩ : syracuseStep 1418801 = 1064101) (by norm_num)
theorem B1680949 : Blo 1180407 1680949 := bbase (se 5 (by rfl) ⟨78794, by rfl⟩ : syracuseStep 1680949 = 157589) (by norm_num)
theorem B1771061 : Blo 1180407 1771061 := bbase (se 5 (by rfl) ⟨83018, by rfl⟩ : syracuseStep 1771061 = 166037) (by norm_num)
theorem B1328701 : Blo 1180407 1328701 := bbase (se 3 (by rfl) ⟨249131, by rfl⟩ : syracuseStep 1328701 = 498263) (by norm_num)
theorem B1992269 : Blo 1180407 1992269 := bbase (se 3 (by rfl) ⟨373550, by rfl⟩ : syracuseStep 1992269 = 747101) (by norm_num)
theorem B1771085 : Blo 1180407 1771085 := bbase (se 3 (by rfl) ⟨332078, by rfl⟩ : syracuseStep 1771085 = 664157) (by norm_num)
theorem B23004757 : Blo 1180407 23004757 := bbase (se 8 (by rfl) ⟨134793, by rfl⟩ : syracuseStep 23004757 = 269587) (by norm_num)
theorem B1328737 : Blo 1180407 1328737 := bbase (se 2 (by rfl) ⟨498276, by rfl⟩ : syracuseStep 1328737 = 996553) (by norm_num)
theorem B1771109 : Blo 1180407 1771109 := bbase (se 4 (by rfl) ⟨166041, by rfl⟩ : syracuseStep 1771109 = 332083) (by norm_num)
theorem B2991725 : Blo 1180407 2991725 := bbase (se 3 (by rfl) ⟨560948, by rfl⟩ : syracuseStep 2991725 = 1121897) (by norm_num)
theorem B1771133 : Blo 1180407 1771133 := bbase (se 3 (by rfl) ⟨332087, by rfl⟩ : syracuseStep 1771133 = 664175) (by norm_num)
theorem B1328773 : Blo 1180407 1328773 := bbase (se 4 (by rfl) ⟨124572, by rfl⟩ : syracuseStep 1328773 = 249145) (by norm_num)
theorem B2393749 : Blo 1180407 2393749 := bbase (se 6 (by rfl) ⟨56103, by rfl⟩ : syracuseStep 2393749 = 112207) (by norm_num)
theorem B1771157 : Blo 1180407 1771157 := bbase (se 6 (by rfl) ⟨41511, by rfl⟩ : syracuseStep 1771157 = 83023) (by norm_num)
theorem B21849749 : Blo 1180407 21849749 := bbase (se 6 (by rfl) ⟨512103, by rfl⟩ : syracuseStep 21849749 = 1024207) (by norm_num)
theorem B1279645 : Blo 1180407 1279645 := bbase (se 3 (by rfl) ⟨239933, by rfl⟩ : syracuseStep 1279645 = 479867) (by norm_num)
theorem B1328809 : Blo 1180407 1328809 := bbase (se 2 (by rfl) ⟨498303, by rfl⟩ : syracuseStep 1328809 = 996607) (by norm_num)
theorem B2655917 : Blo 1180407 2655917 := bbase (se 3 (by rfl) ⟨497984, by rfl⟩ : syracuseStep 2655917 = 995969) (by norm_num)
theorem B1681069 : Blo 1180407 1681069 := bbase (se 3 (by rfl) ⟨315200, by rfl⟩ : syracuseStep 1681069 = 630401) (by norm_num)
theorem B1771181 : Blo 1180407 1771181 := bbase (se 3 (by rfl) ⟨332096, by rfl⟩ : syracuseStep 1771181 = 664193) (by norm_num)
theorem B1771205 : Blo 1180407 1771205 := bbase (se 4 (by rfl) ⟨166050, by rfl⟩ : syracuseStep 1771205 = 332101) (by norm_num)
theorem B1992397 : Blo 1180407 1992397 := bbase (se 3 (by rfl) ⟨373574, by rfl⟩ : syracuseStep 1992397 = 747149) (by norm_num)
theorem B1328845 : Blo 1180407 1328845 := bbase (se 3 (by rfl) ⟨249158, by rfl⟩ : syracuseStep 1328845 = 498317) (by norm_num)
theorem B4482773 : Blo 1180407 4482773 := bbase (se 7 (by rfl) ⟨52532, by rfl⟩ : syracuseStep 4482773 = 105065) (by norm_num)
theorem B7186133 : Blo 1180407 7186133 := bbase (se 7 (by rfl) ⟨84212, by rfl⟩ : syracuseStep 7186133 = 168425) (by norm_num)
theorem B1771229 : Blo 1180407 1771229 := bbase (se 3 (by rfl) ⟨332105, by rfl⟩ : syracuseStep 1771229 = 664211) (by norm_num)
theorem B4548325 : Blo 1180407 4548325 := bbase (se 4 (by rfl) ⟨426405, by rfl⟩ : syracuseStep 4548325 = 852811) (by norm_num)
theorem B1328881 : Blo 1180407 1328881 := bbase (se 2 (by rfl) ⟨498330, by rfl⟩ : syracuseStep 1328881 = 996661) (by norm_num)
theorem B2655989 : Blo 1180407 2655989 := bbase (se 5 (by rfl) ⟨124499, by rfl⟩ : syracuseStep 2655989 = 248999) (by norm_num)
theorem B1771253 : Blo 1180407 1771253 := bbase (se 5 (by rfl) ⟨83027, by rfl⟩ : syracuseStep 1771253 = 166055) (by norm_num)
theorem B3032821 : Blo 1180407 3032821 := bbase (se 5 (by rfl) ⟨142163, by rfl⟩ : syracuseStep 3032821 = 284327) (by norm_num)
theorem B1681165 : Blo 1180407 1681165 := bbase (se 3 (by rfl) ⟨315218, by rfl⟩ : syracuseStep 1681165 = 630437) (by norm_num)
theorem B1771277 : Blo 1180407 1771277 := bbase (se 3 (by rfl) ⟨332114, by rfl⟩ : syracuseStep 1771277 = 664229) (by norm_num)
theorem B1328917 : Blo 1180407 1328917 := bbase (se 6 (by rfl) ⟨31146, by rfl⟩ : syracuseStep 1328917 = 62293) (by norm_num)
theorem B3786517 : Blo 1180407 3786517 := bbase (se 6 (by rfl) ⟨88746, by rfl⟩ : syracuseStep 3786517 = 177493) (by norm_num)
theorem B1992485 : Blo 1180407 1992485 := bbase (se 4 (by rfl) ⟨186795, by rfl⟩ : syracuseStep 1992485 = 373591) (by norm_num)
theorem B1771301 : Blo 1180407 1771301 := bbase (se 4 (by rfl) ⟨166059, by rfl⟩ : syracuseStep 1771301 = 332119) (by norm_num)
theorem B2991917 : Blo 1180407 2991917 := bbase (se 3 (by rfl) ⟨560984, by rfl⟩ : syracuseStep 2991917 = 1121969) (by norm_num)
theorem B1328953 : Blo 1180407 1328953 := bbase (se 2 (by rfl) ⟨498357, by rfl⟩ : syracuseStep 1328953 = 996715) (by norm_num)
theorem B2656061 : Blo 1180407 2656061 := bbase (se 3 (by rfl) ⟨498011, by rfl⟩ : syracuseStep 2656061 = 996023) (by norm_num)
theorem B1771325 : Blo 1180407 1771325 := bbase (se 3 (by rfl) ⟨332123, by rfl⟩ : syracuseStep 1771325 = 664247) (by norm_num)
theorem B1771349 : Blo 1180407 1771349 := bbase (se 9 (by rfl) ⟨5189, by rfl⟩ : syracuseStep 1771349 = 10379) (by norm_num)
theorem B1328989 : Blo 1180407 1328989 := bbase (se 3 (by rfl) ⟨249185, by rfl⟩ : syracuseStep 1328989 = 498371) (by norm_num)
theorem B1771373 : Blo 1180407 1771373 := bbase (se 3 (by rfl) ⟨332132, by rfl⟩ : syracuseStep 1771373 = 664265) (by norm_num)
theorem B1419133 : Blo 1180407 1419133 := bbase (se 3 (by rfl) ⟨266087, by rfl⟩ : syracuseStep 1419133 = 532175) (by norm_num)
theorem B1329025 : Blo 1180407 1329025 := bbase (se 2 (by rfl) ⟨498384, by rfl⟩ : syracuseStep 1329025 = 996769) (by norm_num)
theorem B2656133 : Blo 1180407 2656133 := bbase (se 4 (by rfl) ⟨249012, by rfl⟩ : syracuseStep 2656133 = 498025) (by norm_num)
theorem B1771397 : Blo 1180407 1771397 := bbase (se 4 (by rfl) ⟨166068, by rfl⟩ : syracuseStep 1771397 = 332137) (by norm_num)
theorem B1771421 : Blo 1180407 1771421 := bbase (se 3 (by rfl) ⟨332141, by rfl⟩ : syracuseStep 1771421 = 664283) (by norm_num)
theorem B1992613 : Blo 1180407 1992613 := bbase (se 4 (by rfl) ⟨186807, by rfl⟩ : syracuseStep 1992613 = 373615) (by norm_num)
theorem B1329061 : Blo 1180407 1329061 := bbase (se 4 (by rfl) ⟨124599, by rfl⟩ : syracuseStep 1329061 = 249199) (by norm_num)
theorem B1771445 : Blo 1180407 1771445 := bbase (se 5 (by rfl) ⟨83036, by rfl⟩ : syracuseStep 1771445 = 166073) (by norm_num)
theorem B2836421 : Blo 1180407 2836421 := bbase (se 4 (by rfl) ⟨265914, by rfl⟩ : syracuseStep 2836421 = 531829) (by norm_num)
theorem B1329097 : Blo 1180407 1329097 := bbase (se 2 (by rfl) ⟨498411, by rfl⟩ : syracuseStep 1329097 = 996823) (by norm_num)
theorem B2656205 : Blo 1180407 2656205 := bbase (se 3 (by rfl) ⟨498038, by rfl⟩ : syracuseStep 2656205 = 996077) (by norm_num)
theorem B1771469 : Blo 1180407 1771469 := bbase (se 3 (by rfl) ⟨332150, by rfl⟩ : syracuseStep 1771469 = 664301) (by norm_num)
theorem B1771493 : Blo 1180407 1771493 := bbase (se 4 (by rfl) ⟨166077, by rfl⟩ : syracuseStep 1771493 = 332155) (by norm_num)
theorem B1329133 : Blo 1180407 1329133 := bbase (se 3 (by rfl) ⟨249212, by rfl⟩ : syracuseStep 1329133 = 498425) (by norm_num)
theorem B1771517 : Blo 1180407 1771517 := bbase (se 3 (by rfl) ⟨332159, by rfl⟩ : syracuseStep 1771517 = 664319) (by norm_num)
theorem B1992701 : Blo 1180407 1992701 := bbase (se 3 (by rfl) ⟨373631, by rfl⟩ : syracuseStep 1992701 = 747263) (by norm_num)
theorem B1329169 : Blo 1180407 1329169 := bbase (se 2 (by rfl) ⟨498438, by rfl⟩ : syracuseStep 1329169 = 996877) (by norm_num)
theorem B2656277 : Blo 1180407 2656277 := bbase (se 6 (by rfl) ⟨62256, by rfl⟩ : syracuseStep 2656277 = 124513) (by norm_num)
theorem B1771541 : Blo 1180407 1771541 := bbase (se 6 (by rfl) ⟨41520, by rfl⟩ : syracuseStep 1771541 = 83041) (by norm_num)
theorem B1771565 : Blo 1180407 1771565 := bbase (se 3 (by rfl) ⟨332168, by rfl⟩ : syracuseStep 1771565 = 664337) (by norm_num)
theorem B1329205 : Blo 1180407 1329205 := bbase (se 5 (by rfl) ⟨62306, by rfl⟩ : syracuseStep 1329205 = 124613) (by norm_num)
theorem B10094645 : Blo 1180407 10094645 := bbase (se 5 (by rfl) ⟨473186, by rfl⟩ : syracuseStep 10094645 = 946373) (by norm_num)
theorem B1771589 : Blo 1180407 1771589 := bbase (se 4 (by rfl) ⟨166086, by rfl⟩ : syracuseStep 1771589 = 332173) (by norm_num)
theorem B1329241 : Blo 1180407 1329241 := bbase (se 2 (by rfl) ⟨498465, by rfl⟩ : syracuseStep 1329241 = 996931) (by norm_num)
theorem B2656349 : Blo 1180407 2656349 := bbase (se 3 (by rfl) ⟨498065, by rfl⟩ : syracuseStep 2656349 = 996131) (by norm_num)
theorem B1771613 : Blo 1180407 1771613 := bbase (se 3 (by rfl) ⟨332177, by rfl⟩ : syracuseStep 1771613 = 664355) (by norm_num)
theorem B1771637 : Blo 1180407 1771637 := bbase (se 5 (by rfl) ⟨83045, by rfl⟩ : syracuseStep 1771637 = 166091) (by norm_num)
theorem B1992829 : Blo 1180407 1992829 := bbase (se 3 (by rfl) ⟨373655, by rfl⟩ : syracuseStep 1992829 = 747311) (by norm_num)
theorem B1329277 : Blo 1180407 1329277 := bbase (se 3 (by rfl) ⟨249239, by rfl⟩ : syracuseStep 1329277 = 498479) (by norm_num)
theorem B2992261 : Blo 1180407 2992261 := bbase (se 4 (by rfl) ⟨280524, by rfl⟩ : syracuseStep 2992261 = 561049) (by norm_num)
theorem B1771661 : Blo 1180407 1771661 := bbase (se 3 (by rfl) ⟨332186, by rfl⟩ : syracuseStep 1771661 = 664373) (by norm_num)
theorem B1198237 : Blo 1180407 1198237 := bbase (se 3 (by rfl) ⟨224669, by rfl⟩ : syracuseStep 1198237 = 449339) (by norm_num)
theorem B1329313 : Blo 1180407 1329313 := bbase (se 2 (by rfl) ⟨498492, by rfl⟩ : syracuseStep 1329313 = 996985) (by norm_num)
theorem B2656421 : Blo 1180407 2656421 := bbase (se 4 (by rfl) ⟨249039, by rfl⟩ : syracuseStep 2656421 = 498079) (by norm_num)
theorem B1771685 : Blo 1180407 1771685 := bbase (se 4 (by rfl) ⟨166095, by rfl⟩ : syracuseStep 1771685 = 332191) (by norm_num)
theorem B4548773 : Blo 1180407 4548773 := bbase (se 4 (by rfl) ⟨426447, by rfl⟩ : syracuseStep 4548773 = 852895) (by norm_num)
theorem B1771709 : Blo 1180407 1771709 := bbase (se 3 (by rfl) ⟨332195, by rfl⟩ : syracuseStep 1771709 = 664391) (by norm_num)
theorem B1329349 : Blo 1180407 1329349 := bbase (se 4 (by rfl) ⟨124626, by rfl⟩ : syracuseStep 1329349 = 249253) (by norm_num)
theorem B1992917 : Blo 1180407 1992917 := bbase (se 7 (by rfl) ⟨23354, by rfl⟩ : syracuseStep 1992917 = 46709) (by norm_num)
theorem B1771733 : Blo 1180407 1771733 := bbase (se 7 (by rfl) ⟨20762, by rfl⟩ : syracuseStep 1771733 = 41525) (by norm_num)
theorem B1329385 : Blo 1180407 1329385 := bbase (se 2 (by rfl) ⟨498519, by rfl⟩ : syracuseStep 1329385 = 997039) (by norm_num)
theorem B2656493 : Blo 1180407 2656493 := bbase (se 3 (by rfl) ⟨498092, by rfl⟩ : syracuseStep 2656493 = 996185) (by norm_num)
theorem B1771757 : Blo 1180407 1771757 := bbase (se 3 (by rfl) ⟨332204, by rfl⟩ : syracuseStep 1771757 = 664409) (by norm_num)
theorem B2992373 : Blo 1180407 2992373 := bbase (se 5 (by rfl) ⟨140267, by rfl⟩ : syracuseStep 2992373 = 280535) (by norm_num)
theorem B1681661 : Blo 1180407 1681661 := bbase (se 3 (by rfl) ⟨315311, by rfl⟩ : syracuseStep 1681661 = 630623) (by norm_num)
theorem B1771781 : Blo 1180407 1771781 := bbase (se 4 (by rfl) ⟨166104, by rfl⟩ : syracuseStep 1771781 = 332209) (by norm_num)
theorem B1329421 : Blo 1180407 1329421 := bbase (se 3 (by rfl) ⟨249266, by rfl⟩ : syracuseStep 1329421 = 498533) (by norm_num)
theorem B1771805 : Blo 1180407 1771805 := bbase (se 3 (by rfl) ⟨332213, by rfl⟩ : syracuseStep 1771805 = 664427) (by norm_num)
theorem B1329457 : Blo 1180407 1329457 := bbase (se 2 (by rfl) ⟨498546, by rfl⟩ : syracuseStep 1329457 = 997093) (by norm_num)
theorem B2656565 : Blo 1180407 2656565 := bbase (se 5 (by rfl) ⟨124526, by rfl⟩ : syracuseStep 2656565 = 249053) (by norm_num)
theorem B1771829 : Blo 1180407 1771829 := bbase (se 5 (by rfl) ⟨83054, by rfl⟩ : syracuseStep 1771829 = 166109) (by norm_num)
theorem B1771853 : Blo 1180407 1771853 := bbase (se 3 (by rfl) ⟨332222, by rfl⟩ : syracuseStep 1771853 = 664445) (by norm_num)
theorem B1993045 : Blo 1180407 1993045 := bbase (se 10 (by rfl) ⟨2919, by rfl⟩ : syracuseStep 1993045 = 5839) (by norm_num)
theorem B1329493 : Blo 1180407 1329493 := bbase (se 10 (by rfl) ⟨1947, by rfl⟩ : syracuseStep 1329493 = 3895) (by norm_num)
theorem B1771877 : Blo 1180407 1771877 := bbase (se 4 (by rfl) ⟨166113, by rfl⟩ : syracuseStep 1771877 = 332227) (by norm_num)
theorem B1329529 : Blo 1180407 1329529 := bbase (se 2 (by rfl) ⟨498573, by rfl⟩ : syracuseStep 1329529 = 997147) (by norm_num)
theorem B2656637 : Blo 1180407 2656637 := bbase (se 3 (by rfl) ⟨498119, by rfl⟩ : syracuseStep 2656637 = 996239) (by norm_num)
theorem B1771901 : Blo 1180407 1771901 := bbase (se 3 (by rfl) ⟨332231, by rfl⟩ : syracuseStep 1771901 = 664463) (by norm_num)
theorem B1214849 : Blo 1180407 1214849 := bbase (se 2 (by rfl) ⟨455568, by rfl⟩ : syracuseStep 1214849 = 911137) (by norm_num)
theorem B1771925 : Blo 1180407 1771925 := bbase (se 6 (by rfl) ⟨41529, by rfl⟩ : syracuseStep 1771925 = 83059) (by norm_num)
theorem B1329565 : Blo 1180407 1329565 := bbase (se 3 (by rfl) ⟨249293, by rfl⟩ : syracuseStep 1329565 = 498587) (by norm_num)
theorem B1993133 : Blo 1180407 1993133 := bbase (se 3 (by rfl) ⟨373712, by rfl⟩ : syracuseStep 1993133 = 747425) (by norm_num)
theorem B1771949 : Blo 1180407 1771949 := bbase (se 3 (by rfl) ⟨332240, by rfl⟩ : syracuseStep 1771949 = 664481) (by norm_num)
theorem B2992565 : Blo 1180407 2992565 := bbase (se 5 (by rfl) ⟨140276, by rfl⟩ : syracuseStep 2992565 = 280553) (by norm_num)
theorem B1329601 : Blo 1180407 1329601 := bbase (se 2 (by rfl) ⟨498600, by rfl⟩ : syracuseStep 1329601 = 997201) (by norm_num)
theorem B2656709 : Blo 1180407 2656709 := bbase (se 4 (by rfl) ⟨249066, by rfl⟩ : syracuseStep 2656709 = 498133) (by norm_num)
theorem B1771973 : Blo 1180407 1771973 := bbase (se 4 (by rfl) ⟨166122, by rfl⟩ : syracuseStep 1771973 = 332245) (by norm_num)
theorem B1771997 : Blo 1180407 1771997 := bbase (se 3 (by rfl) ⟨332249, by rfl⟩ : syracuseStep 1771997 = 664499) (by norm_num)
theorem B1329637 : Blo 1180407 1329637 := bbase (se 4 (by rfl) ⟨124653, by rfl⟩ : syracuseStep 1329637 = 249307) (by norm_num)
theorem B1772021 : Blo 1180407 1772021 := bbase (se 5 (by rfl) ⟨83063, by rfl⟩ : syracuseStep 1772021 = 166127) (by norm_num)
theorem B1329673 : Blo 1180407 1329673 := bbase (se 2 (by rfl) ⟨498627, by rfl⟩ : syracuseStep 1329673 = 997255) (by norm_num)
theorem B2656781 : Blo 1180407 2656781 := bbase (se 3 (by rfl) ⟨498146, by rfl⟩ : syracuseStep 2656781 = 996293) (by norm_num)
theorem B1772045 : Blo 1180407 1772045 := bbase (se 3 (by rfl) ⟨332258, by rfl⟩ : syracuseStep 1772045 = 664517) (by norm_num)
theorem B1772069 : Blo 1180407 1772069 := bbase (se 4 (by rfl) ⟨166131, by rfl⟩ : syracuseStep 1772069 = 332263) (by norm_num)
theorem B1993261 : Blo 1180407 1993261 := bbase (se 3 (by rfl) ⟨373736, by rfl⟩ : syracuseStep 1993261 = 747473) (by norm_num)
theorem B1329709 : Blo 1180407 1329709 := bbase (se 3 (by rfl) ⟨249320, by rfl⟩ : syracuseStep 1329709 = 498641) (by norm_num)
theorem B1772093 : Blo 1180407 1772093 := bbase (se 3 (by rfl) ⟨332267, by rfl⟩ : syracuseStep 1772093 = 664535) (by norm_num)
theorem B1329745 : Blo 1180407 1329745 := bbase (se 2 (by rfl) ⟨498654, by rfl⟩ : syracuseStep 1329745 = 997309) (by norm_num)
theorem B3983957 : Blo 1180407 3983957 := bbase (se 8 (by rfl) ⟨23343, by rfl⟩ : syracuseStep 3983957 = 46687) (by norm_num)
theorem B2656853 : Blo 1180407 2656853 := bbase (se 8 (by rfl) ⟨15567, by rfl⟩ : syracuseStep 2656853 = 31135) (by norm_num)
theorem B1772117 : Blo 1180407 1772117 := bbase (se 8 (by rfl) ⟨10383, by rfl⟩ : syracuseStep 1772117 = 20767) (by norm_num)
theorem B5982821 : Blo 1180407 5982821 := bbase (se 4 (by rfl) ⟨560889, by rfl⟩ : syracuseStep 5982821 = 1121779) (by norm_num)
theorem B1772141 : Blo 1180407 1772141 := bbase (se 3 (by rfl) ⟨332276, by rfl⟩ : syracuseStep 1772141 = 664553) (by norm_num)
theorem B1329781 : Blo 1180407 1329781 := bbase (se 5 (by rfl) ⟨62333, by rfl⟩ : syracuseStep 1329781 = 124667) (by norm_num)
theorem B1993349 : Blo 1180407 1993349 := bbase (se 4 (by rfl) ⟨186876, by rfl⟩ : syracuseStep 1993349 = 373753) (by norm_num)
theorem B1772165 : Blo 1180407 1772165 := bbase (se 4 (by rfl) ⟨166140, by rfl⟩ : syracuseStep 1772165 = 332281) (by norm_num)
theorem B1329817 : Blo 1180407 1329817 := bbase (se 2 (by rfl) ⟨498681, by rfl⟩ : syracuseStep 1329817 = 997363) (by norm_num)
theorem B2656925 : Blo 1180407 2656925 := bbase (se 3 (by rfl) ⟨498173, by rfl⟩ : syracuseStep 2656925 = 996347) (by norm_num)
theorem B1772189 : Blo 1180407 1772189 := bbase (se 3 (by rfl) ⟨332285, by rfl⟩ : syracuseStep 1772189 = 664571) (by norm_num)
theorem B1772213 : Blo 1180407 1772213 := bbase (se 5 (by rfl) ⟨83072, by rfl⟩ : syracuseStep 1772213 = 166145) (by norm_num)
theorem B1346233 : Blo 1180407 1346233 := bbase (se 2 (by rfl) ⟨504837, by rfl⟩ : syracuseStep 1346233 = 1009675) (by norm_num)
theorem B1329853 : Blo 1180407 1329853 := bbase (se 3 (by rfl) ⟨249347, by rfl⟩ : syracuseStep 1329853 = 498695) (by norm_num)
theorem B2837189 : Blo 1180407 2837189 := bbase (se 4 (by rfl) ⟨265986, by rfl⟩ : syracuseStep 2837189 = 531973) (by norm_num)
theorem B2837197 : Blo 1180407 2837197 := bbase (se 3 (by rfl) ⟨531974, by rfl⟩ : syracuseStep 2837197 = 1063949) (by norm_num)
theorem B1772237 : Blo 1180407 1772237 := bbase (se 3 (by rfl) ⟨332294, by rfl⟩ : syracuseStep 1772237 = 664589) (by norm_num)
theorem B1329889 : Blo 1180407 1329889 := bbase (se 2 (by rfl) ⟨498708, by rfl⟩ : syracuseStep 1329889 = 997417) (by norm_num)
theorem B2656997 : Blo 1180407 2656997 := bbase (se 4 (by rfl) ⟨249093, by rfl⟩ : syracuseStep 2656997 = 498187) (by norm_num)
theorem B1772261 : Blo 1180407 1772261 := bbase (se 4 (by rfl) ⟨166149, by rfl⟩ : syracuseStep 1772261 = 332299) (by norm_num)
theorem B1420021 : Blo 1180407 1420021 := bbase (se 5 (by rfl) ⟨66563, by rfl⟩ : syracuseStep 1420021 = 133127) (by norm_num)
theorem B1772285 : Blo 1180407 1772285 := bbase (se 3 (by rfl) ⟨332303, by rfl⟩ : syracuseStep 1772285 = 664607) (by norm_num)
theorem B1993477 : Blo 1180407 1993477 := bbase (se 4 (by rfl) ⟨186888, by rfl⟩ : syracuseStep 1993477 = 373777) (by norm_num)
theorem B1329925 : Blo 1180407 1329925 := bbase (se 4 (by rfl) ⟨124680, by rfl⟩ : syracuseStep 1329925 = 249361) (by norm_num)
theorem B2992909 : Blo 1180407 2992909 := bbase (se 3 (by rfl) ⟨561170, by rfl⟩ : syracuseStep 2992909 = 1122341) (by norm_num)
theorem B11504405 : Blo 1180407 11504405 := bbase (se 6 (by rfl) ⟨269634, by rfl⟩ : syracuseStep 11504405 = 539269) (by norm_num)
theorem B1772309 : Blo 1180407 1772309 := bbase (se 6 (by rfl) ⟨41538, by rfl⟩ : syracuseStep 1772309 = 83077) (by norm_num)
theorem B2394917 : Blo 1180407 2394917 := bbase (se 4 (by rfl) ⟨224523, by rfl⟩ : syracuseStep 2394917 = 449047) (by norm_num)
theorem B1682213 : Blo 1180407 1682213 := bbase (se 4 (by rfl) ⟨157707, by rfl⟩ : syracuseStep 1682213 = 315415) (by norm_num)
theorem B1329961 : Blo 1180407 1329961 := bbase (se 2 (by rfl) ⟨498735, by rfl⟩ : syracuseStep 1329961 = 997471) (by norm_num)
theorem B2657069 : Blo 1180407 2657069 := bbase (se 3 (by rfl) ⟨498200, by rfl⟩ : syracuseStep 2657069 = 996401) (by norm_num)
theorem B1772333 : Blo 1180407 1772333 := bbase (se 3 (by rfl) ⟨332312, by rfl⟩ : syracuseStep 1772333 = 664625) (by norm_num)
theorem B1772357 : Blo 1180407 1772357 := bbase (se 4 (by rfl) ⟨166158, by rfl⟩ : syracuseStep 1772357 = 332317) (by norm_num)
theorem B1329997 : Blo 1180407 1329997 := bbase (se 3 (by rfl) ⟨249374, by rfl⟩ : syracuseStep 1329997 = 498749) (by norm_num)
theorem B1993565 : Blo 1180407 1993565 := bbase (se 3 (by rfl) ⟨373793, by rfl⟩ : syracuseStep 1993565 = 747587) (by norm_num)
theorem B1772381 : Blo 1180407 1772381 := bbase (se 3 (by rfl) ⟨332321, by rfl⟩ : syracuseStep 1772381 = 664643) (by norm_num)
theorem B1330033 : Blo 1180407 1330033 := bbase (se 2 (by rfl) ⟨498762, by rfl⟩ : syracuseStep 1330033 = 997525) (by norm_num)
theorem B2657141 : Blo 1180407 2657141 := bbase (se 5 (by rfl) ⟨124553, by rfl⟩ : syracuseStep 2657141 = 249107) (by norm_num)
theorem B4483957 : Blo 1180407 4483957 := bbase (se 5 (by rfl) ⟨210185, by rfl⟩ : syracuseStep 4483957 = 420371) (by norm_num)
theorem B1772405 : Blo 1180407 1772405 := bbase (se 5 (by rfl) ⟨83081, by rfl⟩ : syracuseStep 1772405 = 166163) (by norm_num)
theorem B1772429 : Blo 1180407 1772429 := bbase (se 3 (by rfl) ⟨332330, by rfl⟩ : syracuseStep 1772429 = 664661) (by norm_num)
theorem B1330069 : Blo 1180407 1330069 := bbase (se 6 (by rfl) ⟨31173, by rfl⟩ : syracuseStep 1330069 = 62347) (by norm_num)
theorem B1772453 : Blo 1180407 1772453 := bbase (se 4 (by rfl) ⟨166167, by rfl⟩ : syracuseStep 1772453 = 332335) (by norm_num)
theorem B1330105 : Blo 1180407 1330105 := bbase (se 2 (by rfl) ⟨498789, by rfl⟩ : syracuseStep 1330105 = 997579) (by norm_num)
theorem B2657213 : Blo 1180407 2657213 := bbase (se 3 (by rfl) ⟨498227, by rfl⟩ : syracuseStep 2657213 = 996455) (by norm_num)
theorem B1772477 : Blo 1180407 1772477 := bbase (se 3 (by rfl) ⟨332339, by rfl⟩ : syracuseStep 1772477 = 664679) (by norm_num)
theorem B1772501 : Blo 1180407 1772501 := bbase (se 7 (by rfl) ⟨20771, by rfl⟩ : syracuseStep 1772501 = 41543) (by norm_num)
theorem B2878421 : Blo 1180407 2878421 := bbase (se 7 (by rfl) ⟨33731, by rfl⟩ : syracuseStep 2878421 = 67463) (by norm_num)
theorem B1993693 : Blo 1180407 1993693 := bbase (se 3 (by rfl) ⟨373817, by rfl⟩ : syracuseStep 1993693 = 747635) (by norm_num)
theorem B1330141 : Blo 1180407 1330141 := bbase (se 3 (by rfl) ⟨249401, by rfl⟩ : syracuseStep 1330141 = 498803) (by norm_num)
theorem B1772525 : Blo 1180407 1772525 := bbase (se 3 (by rfl) ⟨332348, by rfl⟩ : syracuseStep 1772525 = 664697) (by norm_num)
theorem B1330177 : Blo 1180407 1330177 := bbase (se 2 (by rfl) ⟨498816, by rfl⟩ : syracuseStep 1330177 = 997633) (by norm_num)
theorem B3984389 : Blo 1180407 3984389 := bbase (se 4 (by rfl) ⟨373536, by rfl⟩ : syracuseStep 3984389 = 747073) (by norm_num)
theorem B5385221 : Blo 1180407 5385221 := bbase (se 4 (by rfl) ⟨504864, by rfl⟩ : syracuseStep 5385221 = 1009729) (by norm_num)
theorem B2657285 : Blo 1180407 2657285 := bbase (se 4 (by rfl) ⟨249120, by rfl⟩ : syracuseStep 2657285 = 498241) (by norm_num)
theorem B1772549 : Blo 1180407 1772549 := bbase (se 4 (by rfl) ⟨166176, by rfl⟩ : syracuseStep 1772549 = 332353) (by norm_num)
theorem B1772573 : Blo 1180407 1772573 := bbase (se 3 (by rfl) ⟨332357, by rfl⟩ : syracuseStep 1772573 = 664715) (by norm_num)
theorem B4787237 : Blo 1180407 4787237 := bbase (se 4 (by rfl) ⟨448803, by rfl⟩ : syracuseStep 4787237 = 897607) (by norm_num)
theorem B1494065 : Blo 1180407 1494065 := bbase (se 2 (by rfl) ⟨560274, by rfl⟩ : syracuseStep 1494065 = 1120549) (by norm_num)
theorem B1993781 : Blo 1180407 1993781 := bbase (se 5 (by rfl) ⟨93458, by rfl⟩ : syracuseStep 1993781 = 186917) (by norm_num)
theorem B1772597 : Blo 1180407 1772597 := bbase (se 5 (by rfl) ⟨83090, by rfl⟩ : syracuseStep 1772597 = 166181) (by norm_num)
theorem B2657357 : Blo 1180407 2657357 := bbase (se 3 (by rfl) ⟨498254, by rfl⟩ : syracuseStep 2657357 = 996509) (by norm_num)
theorem B1772621 : Blo 1180407 1772621 := bbase (se 3 (by rfl) ⟨332366, by rfl⟩ : syracuseStep 1772621 = 664733) (by norm_num)
theorem B1772645 : Blo 1180407 1772645 := bbase (se 4 (by rfl) ⟨166185, by rfl⟩ : syracuseStep 1772645 = 332371) (by norm_num)
theorem B3787877 : Blo 1180407 3787877 := bbase (se 4 (by rfl) ⟨355113, by rfl⟩ : syracuseStep 3787877 = 710227) (by norm_num)
theorem B1494121 : Blo 1180407 1494121 := bbase (se 2 (by rfl) ⟨560295, by rfl⟩ : syracuseStep 1494121 = 1120591) (by norm_num)
theorem B1772669 : Blo 1180407 1772669 := bbase (se 3 (by rfl) ⟨332375, by rfl⟩ : syracuseStep 1772669 = 664751) (by norm_num)
theorem B3591317 : Blo 1180407 3591317 := bbase (se 6 (by rfl) ⟨84171, by rfl⟩ : syracuseStep 3591317 = 168343) (by norm_num)
theorem B2657429 : Blo 1180407 2657429 := bbase (se 6 (by rfl) ⟨62283, by rfl⟩ : syracuseStep 2657429 = 124567) (by norm_num)
theorem B1772693 : Blo 1180407 1772693 := bbase (se 6 (by rfl) ⟨41547, by rfl⟩ : syracuseStep 1772693 = 83095) (by norm_num)
theorem B5680277 : Blo 1180407 5680277 := bbase (se 6 (by rfl) ⟨133131, by rfl⟩ : syracuseStep 5680277 = 266263) (by norm_num)
theorem B4484261 : Blo 1180407 4484261 := bbase (se 4 (by rfl) ⟨420399, by rfl⟩ : syracuseStep 4484261 = 840799) (by norm_num)
theorem B1772717 : Blo 1180407 1772717 := bbase (se 3 (by rfl) ⟨332384, by rfl⟩ : syracuseStep 1772717 = 664769) (by norm_num)
theorem B1993909 : Blo 1180407 1993909 := bbase (se 5 (by rfl) ⟨93464, by rfl⟩ : syracuseStep 1993909 = 186929) (by norm_num)
theorem B1772741 : Blo 1180407 1772741 := bbase (se 4 (by rfl) ⟨166194, by rfl⟩ : syracuseStep 1772741 = 332389) (by norm_num)
theorem B1494217 : Blo 1180407 1494217 := bbase (se 2 (by rfl) ⟨560331, by rfl⟩ : syracuseStep 1494217 = 1120663) (by norm_num)
theorem B2657501 : Blo 1180407 2657501 := bbase (se 3 (by rfl) ⟨498281, by rfl⟩ : syracuseStep 2657501 = 996563) (by norm_num)
theorem B1772765 : Blo 1180407 1772765 := bbase (se 3 (by rfl) ⟨332393, by rfl⟩ : syracuseStep 1772765 = 664787) (by norm_num)
theorem B1772789 : Blo 1180407 1772789 := bbase (se 5 (by rfl) ⟨83099, by rfl⟩ : syracuseStep 1772789 = 166199) (by norm_num)
theorem B1993997 : Blo 1180407 1993997 := bbase (se 3 (by rfl) ⟨373874, by rfl⟩ : syracuseStep 1993997 = 747749) (by norm_num)
theorem B1772813 : Blo 1180407 1772813 := bbase (se 3 (by rfl) ⟨332402, by rfl⟩ : syracuseStep 1772813 = 664805) (by norm_num)
theorem B2657573 : Blo 1180407 2657573 := bbase (se 4 (by rfl) ⟨249147, by rfl⟩ : syracuseStep 2657573 = 498295) (by norm_num)
theorem B1772837 : Blo 1180407 1772837 := bbase (se 4 (by rfl) ⟨166203, by rfl⟩ : syracuseStep 1772837 = 332407) (by norm_num)
theorem B1772861 : Blo 1180407 1772861 := bbase (se 3 (by rfl) ⟨332411, by rfl⟩ : syracuseStep 1772861 = 664823) (by norm_num)
theorem B32320853 : Blo 1180407 32320853 := bbase (se 11 (by rfl) ⟨23672, by rfl⟩ : syracuseStep 32320853 = 47345) (by norm_num)
theorem B1772885 : Blo 1180407 1772885 := bbase (se 11 (by rfl) ⟨1298, by rfl⟩ : syracuseStep 1772885 = 2597) (by norm_num)
theorem B2657645 : Blo 1180407 2657645 := bbase (se 3 (by rfl) ⟨498308, by rfl⟩ : syracuseStep 2657645 = 996617) (by norm_num)
theorem B1772909 : Blo 1180407 1772909 := bbase (se 3 (by rfl) ⟨332420, by rfl⟩ : syracuseStep 1772909 = 664841) (by norm_num)
theorem B1494389 : Blo 1180407 1494389 := bbase (se 5 (by rfl) ⟨70049, by rfl⟩ : syracuseStep 1494389 = 140099) (by norm_num)
theorem B1772933 : Blo 1180407 1772933 := bbase (se 4 (by rfl) ⟨166212, by rfl⟩ : syracuseStep 1772933 = 332425) (by norm_num)
theorem B1994125 : Blo 1180407 1994125 := bbase (se 3 (by rfl) ⟨373898, by rfl⟩ : syracuseStep 1994125 = 747797) (by norm_num)
theorem B1772957 : Blo 1180407 1772957 := bbase (se 3 (by rfl) ⟨332429, by rfl⟩ : syracuseStep 1772957 = 664859) (by norm_num)
theorem B1494445 : Blo 1180407 1494445 := bbase (se 3 (by rfl) ⟨280208, by rfl⟩ : syracuseStep 1494445 = 560417) (by norm_num)
theorem B2657717 : Blo 1180407 2657717 := bbase (se 5 (by rfl) ⟨124580, by rfl⟩ : syracuseStep 2657717 = 249161) (by norm_num)
theorem B3984821 : Blo 1180407 3984821 := bbase (se 5 (by rfl) ⟨186788, by rfl⟩ : syracuseStep 3984821 = 373577) (by norm_num)
theorem B1772981 : Blo 1180407 1772981 := bbase (se 5 (by rfl) ⟨83108, by rfl⟩ : syracuseStep 1772981 = 166217) (by norm_num)
theorem B2305477 : Blo 1180407 2305477 := bbase (se 4 (by rfl) ⟨216138, by rfl⟩ : syracuseStep 2305477 = 432277) (by norm_num)
theorem B1347017 : Blo 1180407 1347017 := bbase (se 2 (by rfl) ⟨505131, by rfl⟩ : syracuseStep 1347017 = 1010263) (by norm_num)
theorem B1773005 : Blo 1180407 1773005 := bbase (se 3 (by rfl) ⟨332438, by rfl⟩ : syracuseStep 1773005 = 664877) (by norm_num)
theorem B1994213 : Blo 1180407 1994213 := bbase (se 4 (by rfl) ⟨186957, by rfl⟩ : syracuseStep 1994213 = 373915) (by norm_num)
theorem B1773029 : Blo 1180407 1773029 := bbase (se 4 (by rfl) ⟨166221, by rfl⟩ : syracuseStep 1773029 = 332443) (by norm_num)
theorem B2838005 : Blo 1180407 2838005 := bbase (se 5 (by rfl) ⟨133031, by rfl⟩ : syracuseStep 2838005 = 266063) (by norm_num)
theorem B2657789 : Blo 1180407 2657789 := bbase (se 3 (by rfl) ⟨498335, by rfl⟩ : syracuseStep 2657789 = 996671) (by norm_num)
theorem B1773053 : Blo 1180407 1773053 := bbase (se 3 (by rfl) ⟨332447, by rfl⟩ : syracuseStep 1773053 = 664895) (by norm_num)
theorem B1494541 : Blo 1180407 1494541 := bbase (se 3 (by rfl) ⟨280226, by rfl⟩ : syracuseStep 1494541 = 560453) (by norm_num)
theorem B7573013 : Blo 1180407 7573013 := bbase (se 6 (by rfl) ⟨177492, by rfl⟩ : syracuseStep 7573013 = 354985) (by norm_num)
theorem B1682965 : Blo 1180407 1682965 := bbase (se 6 (by rfl) ⟨39444, by rfl⟩ : syracuseStep 1682965 = 78889) (by norm_num)
theorem B1773077 : Blo 1180407 1773077 := bbase (se 6 (by rfl) ⟨41556, by rfl⟩ : syracuseStep 1773077 = 83113) (by norm_num)
theorem B1773101 : Blo 1180407 1773101 := bbase (se 3 (by rfl) ⟨332456, by rfl⟩ : syracuseStep 1773101 = 664913) (by norm_num)
theorem B2657861 : Blo 1180407 2657861 := bbase (se 4 (by rfl) ⟨249174, by rfl⟩ : syracuseStep 2657861 = 498349) (by norm_num)
theorem B1773125 : Blo 1180407 1773125 := bbase (se 4 (by rfl) ⟨166230, by rfl⟩ : syracuseStep 1773125 = 332461) (by norm_num)
theorem B1773149 : Blo 1180407 1773149 := bbase (se 3 (by rfl) ⟨332465, by rfl⟩ : syracuseStep 1773149 = 664931) (by norm_num)
theorem B1994341 : Blo 1180407 1994341 := bbase (se 4 (by rfl) ⟨186969, by rfl⟩ : syracuseStep 1994341 = 373939) (by norm_num)
theorem B1773173 : Blo 1180407 1773173 := bbase (se 5 (by rfl) ⟨83117, by rfl⟩ : syracuseStep 1773173 = 166235) (by norm_num)
theorem B5049989 : Blo 1180407 5049989 := bbase (se 4 (by rfl) ⟨473436, by rfl⟩ : syracuseStep 5049989 = 946873) (by norm_num)
theorem B2657933 : Blo 1180407 2657933 := bbase (se 3 (by rfl) ⟨498362, by rfl⟩ : syracuseStep 2657933 = 996725) (by norm_num)
theorem B1773197 : Blo 1180407 1773197 := bbase (se 3 (by rfl) ⟨332474, by rfl⟩ : syracuseStep 1773197 = 664949) (by norm_num)
theorem B1773221 : Blo 1180407 1773221 := bbase (se 4 (by rfl) ⟨166239, by rfl⟩ : syracuseStep 1773221 = 332479) (by norm_num)
theorem B1494713 : Blo 1180407 1494713 := bbase (se 2 (by rfl) ⟨560517, by rfl⟩ : syracuseStep 1494713 = 1121035) (by norm_num)
theorem B1994429 : Blo 1180407 1994429 := bbase (se 3 (by rfl) ⟨373955, by rfl⟩ : syracuseStep 1994429 = 747911) (by norm_num)
theorem B1773245 : Blo 1180407 1773245 := bbase (se 3 (by rfl) ⟨332483, by rfl⟩ : syracuseStep 1773245 = 664967) (by norm_num)
theorem B2658005 : Blo 1180407 2658005 := bbase (se 7 (by rfl) ⟨31148, by rfl⟩ : syracuseStep 2658005 = 62297) (by norm_num)
theorem B1773269 : Blo 1180407 1773269 := bbase (se 7 (by rfl) ⟨20780, by rfl⟩ : syracuseStep 1773269 = 41561) (by norm_num)
theorem B1773293 : Blo 1180407 1773293 := bbase (se 3 (by rfl) ⟨332492, by rfl⟩ : syracuseStep 1773293 = 664985) (by norm_num)
theorem B1494769 : Blo 1180407 1494769 := bbase (se 2 (by rfl) ⟨560538, by rfl⟩ : syracuseStep 1494769 = 1121077) (by norm_num)
theorem B5385989 : Blo 1180407 5385989 := bbase (se 4 (by rfl) ⟨504936, by rfl⟩ : syracuseStep 5385989 = 1009873) (by norm_num)
theorem B1773317 : Blo 1180407 1773317 := bbase (se 4 (by rfl) ⟨166248, by rfl⟩ : syracuseStep 1773317 = 332497) (by norm_num)
theorem B2559757 : Blo 1180407 2559757 := bbase (se 3 (by rfl) ⟨479954, by rfl⟩ : syracuseStep 2559757 = 959909) (by norm_num)
theorem B2658077 : Blo 1180407 2658077 := bbase (se 3 (by rfl) ⟨498389, by rfl⟩ : syracuseStep 2658077 = 996779) (by norm_num)
theorem B1773341 : Blo 1180407 1773341 := bbase (se 3 (by rfl) ⟨332501, by rfl⟩ : syracuseStep 1773341 = 665003) (by norm_num)
theorem B2019125 : Blo 1180407 2019125 := bbase (se 5 (by rfl) ⟨94646, by rfl⟩ : syracuseStep 2019125 = 189293) (by norm_num)
theorem B9711413 : Blo 1180407 9711413 := bbase (se 5 (by rfl) ⟨455222, by rfl⟩ : syracuseStep 9711413 = 910445) (by norm_num)
theorem B1773365 : Blo 1180407 1773365 := bbase (se 5 (by rfl) ⟨83126, by rfl⟩ : syracuseStep 1773365 = 166253) (by norm_num)
theorem B1994557 : Blo 1180407 1994557 := bbase (se 3 (by rfl) ⟨373979, by rfl⟩ : syracuseStep 1994557 = 747959) (by norm_num)
theorem B1773389 : Blo 1180407 1773389 := bbase (se 3 (by rfl) ⟨332510, by rfl⟩ : syracuseStep 1773389 = 665021) (by norm_num)
theorem B1494865 : Blo 1180407 1494865 := bbase (se 2 (by rfl) ⟨560574, by rfl⟩ : syracuseStep 1494865 = 1121149) (by norm_num)
theorem B3985253 : Blo 1180407 3985253 := bbase (se 4 (by rfl) ⟨373617, by rfl⟩ : syracuseStep 3985253 = 747235) (by norm_num)
theorem B2658149 : Blo 1180407 2658149 := bbase (se 4 (by rfl) ⟨249201, by rfl⟩ : syracuseStep 2658149 = 498403) (by norm_num)
theorem B1773413 : Blo 1180407 1773413 := bbase (se 4 (by rfl) ⟨166257, by rfl⟩ : syracuseStep 1773413 = 332515) (by norm_num)
theorem B5984117 : Blo 1180407 5984117 := bbase (se 5 (by rfl) ⟨280505, by rfl⟩ : syracuseStep 5984117 = 561011) (by norm_num)
theorem B1773437 : Blo 1180407 1773437 := bbase (se 3 (by rfl) ⟨332519, by rfl⟩ : syracuseStep 1773437 = 665039) (by norm_num)
theorem B15339413 : Blo 1180407 15339413 := bbase (se 6 (by rfl) ⟨359517, by rfl⟩ : syracuseStep 15339413 = 719035) (by norm_num)
theorem B1994645 : Blo 1180407 1994645 := bbase (se 6 (by rfl) ⟨46749, by rfl⟩ : syracuseStep 1994645 = 93499) (by norm_num)
theorem B1773461 : Blo 1180407 1773461 := bbase (se 6 (by rfl) ⟨41565, by rfl⟩ : syracuseStep 1773461 = 83131) (by norm_num)
theorem B2658221 : Blo 1180407 2658221 := bbase (se 3 (by rfl) ⟨498416, by rfl⟩ : syracuseStep 2658221 = 996833) (by norm_num)
theorem B1773485 : Blo 1180407 1773485 := bbase (se 3 (by rfl) ⟨332528, by rfl⟩ : syracuseStep 1773485 = 665057) (by norm_num)
theorem B3362741 : Blo 1180407 3362741 := bbase (se 5 (by rfl) ⟨157628, by rfl⟩ : syracuseStep 3362741 = 315257) (by norm_num)
theorem B8081333 : Blo 1180407 8081333 := bbase (se 5 (by rfl) ⟨378812, by rfl⟩ : syracuseStep 8081333 = 757625) (by norm_num)
theorem B1773509 : Blo 1180407 1773509 := bbase (se 4 (by rfl) ⟨166266, by rfl⟩ : syracuseStep 1773509 = 332533) (by norm_num)
theorem B1773533 : Blo 1180407 1773533 := bbase (se 3 (by rfl) ⟨332537, by rfl⟩ : syracuseStep 1773533 = 665075) (by norm_num)
theorem B2658293 : Blo 1180407 2658293 := bbase (se 5 (by rfl) ⟨124607, by rfl⟩ : syracuseStep 2658293 = 249215) (by norm_num)
theorem B1773557 : Blo 1180407 1773557 := bbase (se 5 (by rfl) ⟨83135, by rfl⟩ : syracuseStep 1773557 = 166271) (by norm_num)
theorem B1495037 : Blo 1180407 1495037 := bbase (se 3 (by rfl) ⟨280319, by rfl⟩ : syracuseStep 1495037 = 560639) (by norm_num)
theorem B1773581 : Blo 1180407 1773581 := bbase (se 3 (by rfl) ⟨332546, by rfl⟩ : syracuseStep 1773581 = 665093) (by norm_num)
theorem B1994773 : Blo 1180407 1994773 := bbase (se 6 (by rfl) ⟨46752, by rfl⟩ : syracuseStep 1994773 = 93505) (by norm_num)
theorem B1773605 : Blo 1180407 1773605 := bbase (se 4 (by rfl) ⟨166275, by rfl⟩ : syracuseStep 1773605 = 332551) (by norm_num)
theorem B1495093 : Blo 1180407 1495093 := bbase (se 5 (by rfl) ⟨70082, by rfl⟩ : syracuseStep 1495093 = 140165) (by norm_num)
theorem B2658365 : Blo 1180407 2658365 := bbase (se 3 (by rfl) ⟨498443, by rfl⟩ : syracuseStep 2658365 = 996887) (by norm_num)
theorem B1994861 : Blo 1180407 1994861 := bbase (se 3 (by rfl) ⟨374036, by rfl⟩ : syracuseStep 1994861 = 748073) (by norm_num)
theorem B2658437 : Blo 1180407 2658437 := bbase (se 4 (by rfl) ⟨249228, by rfl⟩ : syracuseStep 2658437 = 498457) (by norm_num)
theorem B1495189 : Blo 1180407 1495189 := bbase (se 6 (by rfl) ⟨35043, by rfl⟩ : syracuseStep 1495189 = 70087) (by norm_num)
theorem B2658509 : Blo 1180407 2658509 := bbase (se 3 (by rfl) ⟨498470, by rfl⟩ : syracuseStep 2658509 = 996941) (by norm_num)
theorem B2019541 : Blo 1180407 2019541 := bbase (se 7 (by rfl) ⟨23666, by rfl⟩ : syracuseStep 2019541 = 47333) (by norm_num)
theorem B1994989 : Blo 1180407 1994989 := bbase (se 3 (by rfl) ⟨374060, by rfl⟩ : syracuseStep 1994989 = 748121) (by norm_num)
theorem B5976341 : Blo 1180407 5976341 := bbase (se 6 (by rfl) ⟨140070, by rfl⟩ : syracuseStep 5976341 = 280141) (by norm_num)
theorem B3985685 : Blo 1180407 3985685 := bbase (se 6 (by rfl) ⟨93414, by rfl⟩ : syracuseStep 3985685 = 186829) (by norm_num)
theorem B2658581 : Blo 1180407 2658581 := bbase (se 6 (by rfl) ⟨62310, by rfl⟩ : syracuseStep 2658581 = 124621) (by norm_num)
theorem B6730037 : Blo 1180407 6730037 := bbase (se 5 (by rfl) ⟨315470, by rfl⟩ : syracuseStep 6730037 = 630941) (by norm_num)
theorem B1495361 : Blo 1180407 1495361 := bbase (se 2 (by rfl) ⟨560760, by rfl⟩ : syracuseStep 1495361 = 1121521) (by norm_num)
theorem B1995077 : Blo 1180407 1995077 := bbase (se 4 (by rfl) ⟨187038, by rfl⟩ : syracuseStep 1995077 = 374077) (by norm_num)
theorem B7565653 : Blo 1180407 7565653 := bbase (se 10 (by rfl) ⟨11082, by rfl⟩ : syracuseStep 7565653 = 22165) (by norm_num)
theorem B2658653 : Blo 1180407 2658653 := bbase (se 3 (by rfl) ⟨498497, by rfl⟩ : syracuseStep 2658653 = 996995) (by norm_num)
theorem B1495417 : Blo 1180407 1495417 := bbase (se 2 (by rfl) ⟨560781, by rfl⟩ : syracuseStep 1495417 = 1121563) (by norm_num)
theorem B2429309 : Blo 1180407 2429309 := bbase (se 3 (by rfl) ⟨455495, by rfl⟩ : syracuseStep 2429309 = 910991) (by norm_num)
theorem B2658725 : Blo 1180407 2658725 := bbase (se 4 (by rfl) ⟨249255, by rfl⟩ : syracuseStep 2658725 = 498511) (by norm_num)
theorem B1995205 : Blo 1180407 1995205 := bbase (se 4 (by rfl) ⟨187050, by rfl⟩ : syracuseStep 1995205 = 374101) (by norm_num)
theorem B5681621 : Blo 1180407 5681621 := bbase (se 7 (by rfl) ⟨66581, by rfl⟩ : syracuseStep 5681621 = 133163) (by norm_num)
theorem B1495513 : Blo 1180407 1495513 := bbase (se 2 (by rfl) ⟨560817, by rfl⟩ : syracuseStep 1495513 = 1121635) (by norm_num)
theorem B3412453 : Blo 1180407 3412453 := bbase (se 4 (by rfl) ⟨319917, by rfl⟩ : syracuseStep 3412453 = 639835) (by norm_num)
theorem B2658797 : Blo 1180407 2658797 := bbase (se 3 (by rfl) ⟨498524, by rfl⟩ : syracuseStep 2658797 = 997049) (by norm_num)
theorem B2241037 : Blo 1180407 2241037 := bbase (se 3 (by rfl) ⟨420194, by rfl⟩ : syracuseStep 2241037 = 840389) (by norm_num)
theorem B1995293 : Blo 1180407 1995293 := bbase (se 3 (by rfl) ⟨374117, by rfl⟩ : syracuseStep 1995293 = 748235) (by norm_num)
theorem B10768949 : Blo 1180407 10768949 := bbase (se 5 (by rfl) ⟨504794, by rfl⟩ : syracuseStep 10768949 = 1009589) (by norm_num)
theorem B2658869 : Blo 1180407 2658869 := bbase (se 5 (by rfl) ⟨124634, by rfl⟩ : syracuseStep 2658869 = 249269) (by norm_num)
theorem B2658941 : Blo 1180407 2658941 := bbase (se 3 (by rfl) ⟨498551, by rfl⟩ : syracuseStep 2658941 = 997103) (by norm_num)
theorem B1495685 : Blo 1180407 1495685 := bbase (se 4 (by rfl) ⟨140220, by rfl⟩ : syracuseStep 1495685 = 280441) (by norm_num)
theorem B1495741 : Blo 1180407 1495741 := bbase (se 3 (by rfl) ⟨280451, by rfl⟩ : syracuseStep 1495741 = 560903) (by norm_num)
theorem B3986117 : Blo 1180407 3986117 := bbase (se 4 (by rfl) ⟨373698, by rfl⟩ : syracuseStep 3986117 = 747397) (by norm_num)
theorem B2659013 : Blo 1180407 2659013 := bbase (se 4 (by rfl) ⟨249282, by rfl⟩ : syracuseStep 2659013 = 498565) (by norm_num)
theorem B2659085 : Blo 1180407 2659085 := bbase (se 3 (by rfl) ⟨498578, by rfl⟩ : syracuseStep 2659085 = 997157) (by norm_num)
theorem B1495837 : Blo 1180407 1495837 := bbase (se 3 (by rfl) ⟨280469, by rfl⟩ : syracuseStep 1495837 = 560939) (by norm_num)
theorem B2241341 : Blo 1180407 2241341 := bbase (se 3 (by rfl) ⟨420251, by rfl⟩ : syracuseStep 2241341 = 840503) (by norm_num)
theorem B2659157 : Blo 1180407 2659157 := bbase (se 9 (by rfl) ⟨7790, by rfl⟩ : syracuseStep 2659157 = 15581) (by norm_num)
theorem B2659229 : Blo 1180407 2659229 := bbase (se 3 (by rfl) ⟨498605, by rfl⟩ : syracuseStep 2659229 = 997211) (by norm_num)
theorem B1496009 : Blo 1180407 1496009 := bbase (se 2 (by rfl) ⟨561003, by rfl⟩ : syracuseStep 1496009 = 1122007) (by norm_num)
theorem B10097621 : Blo 1180407 10097621 := bbase (se 7 (by rfl) ⟨118331, by rfl⟩ : syracuseStep 10097621 = 236663) (by norm_num)
theorem B2659301 : Blo 1180407 2659301 := bbase (se 4 (by rfl) ⟨249309, by rfl⟩ : syracuseStep 2659301 = 498619) (by norm_num)
theorem B2274293 : Blo 1180407 2274293 := bbase (se 5 (by rfl) ⟨106607, by rfl⟩ : syracuseStep 2274293 = 213215) (by norm_num)
theorem B1496065 : Blo 1180407 1496065 := bbase (se 2 (by rfl) ⟨561024, by rfl⟩ : syracuseStep 1496065 = 1122049) (by norm_num)
theorem B1365017 : Blo 1180407 1365017 := bbase (se 2 (by rfl) ⟨511881, by rfl⟩ : syracuseStep 1365017 = 1023763) (by norm_num)
theorem B2659373 : Blo 1180407 2659373 := bbase (se 3 (by rfl) ⟨498632, by rfl⟩ : syracuseStep 2659373 = 997265) (by norm_num)
theorem B3363925 : Blo 1180407 3363925 := bbase (se 8 (by rfl) ⟨19710, by rfl⟩ : syracuseStep 3363925 = 39421) (by norm_num)
theorem B1496161 : Blo 1180407 1496161 := bbase (se 2 (by rfl) ⟨561060, by rfl⟩ : syracuseStep 1496161 = 1122121) (by norm_num)
theorem B3986549 : Blo 1180407 3986549 := bbase (se 5 (by rfl) ⟨186869, by rfl⟩ : syracuseStep 3986549 = 373739) (by norm_num)
theorem B2659445 : Blo 1180407 2659445 := bbase (se 5 (by rfl) ⟨124661, by rfl⟩ : syracuseStep 2659445 = 249323) (by norm_num)
theorem B5985413 : Blo 1180407 5985413 := bbase (se 4 (by rfl) ⟨561132, by rfl⟩ : syracuseStep 5985413 = 1122265) (by norm_num)
theorem B2659517 : Blo 1180407 2659517 := bbase (se 3 (by rfl) ⟨498659, by rfl⟩ : syracuseStep 2659517 = 997319) (by norm_num)
theorem B3781829 : Blo 1180407 3781829 := bbase (se 4 (by rfl) ⟨354546, by rfl⟩ : syracuseStep 3781829 = 709093) (by norm_num)
theorem B4256981 : Blo 1180407 4256981 := bbase (se 7 (by rfl) ⟨49886, by rfl⟩ : syracuseStep 4256981 = 99773) (by norm_num)
theorem B4486373 : Blo 1180407 4486373 := bbase (se 4 (by rfl) ⟨420597, by rfl⟩ : syracuseStep 4486373 = 841195) (by norm_num)
theorem B3364085 : Blo 1180407 3364085 := bbase (se 5 (by rfl) ⟨157691, by rfl⟩ : syracuseStep 3364085 = 315383) (by norm_num)
theorem B2659589 : Blo 1180407 2659589 := bbase (se 4 (by rfl) ⟨249336, by rfl⟩ : syracuseStep 2659589 = 498673) (by norm_num)
theorem B1496333 : Blo 1180407 1496333 := bbase (se 3 (by rfl) ⟨280562, by rfl⟩ : syracuseStep 1496333 = 561125) (by norm_num)
theorem B1496389 : Blo 1180407 1496389 := bbase (se 4 (by rfl) ⟨140286, by rfl⟩ : syracuseStep 1496389 = 280573) (by norm_num)
theorem B2659661 : Blo 1180407 2659661 := bbase (se 3 (by rfl) ⟨498686, by rfl⟩ : syracuseStep 2659661 = 997373) (by norm_num)
theorem B2020717 : Blo 1180407 2020717 := bbase (se 3 (by rfl) ⟨378884, by rfl⟩ : syracuseStep 2020717 = 757769) (by norm_num)
theorem B4789621 : Blo 1180407 4789621 := bbase (se 5 (by rfl) ⟨224513, by rfl⟩ : syracuseStep 4789621 = 449027) (by norm_num)
theorem B2659733 : Blo 1180407 2659733 := bbase (se 6 (by rfl) ⟨62337, by rfl⟩ : syracuseStep 2659733 = 124675) (by norm_num)
theorem B1496485 : Blo 1180407 1496485 := bbase (se 4 (by rfl) ⟨140295, by rfl⟩ : syracuseStep 1496485 = 280591) (by norm_num)
theorem B6731221 : Blo 1180407 6731221 := bbase (se 7 (by rfl) ⟨78881, by rfl⟩ : syracuseStep 6731221 = 157763) (by norm_num)
theorem B2659805 : Blo 1180407 2659805 := bbase (se 3 (by rfl) ⟨498713, by rfl⟩ : syracuseStep 2659805 = 997427) (by norm_num)
theorem B3364325 : Blo 1180407 3364325 := bbase (se 4 (by rfl) ⟨315405, by rfl⟩ : syracuseStep 3364325 = 630811) (by norm_num)
theorem B5043701 : Blo 1180407 5043701 := bbase (se 5 (by rfl) ⟨236423, by rfl⟩ : syracuseStep 5043701 = 472847) (by norm_num)
theorem B4486661 : Blo 1180407 4486661 := bbase (se 4 (by rfl) ⟨420624, by rfl⟩ : syracuseStep 4486661 = 841249) (by norm_num)
theorem B5977637 : Blo 1180407 5977637 := bbase (se 4 (by rfl) ⟨560403, by rfl⟩ : syracuseStep 5977637 = 1120807) (by norm_num)
theorem B3986981 : Blo 1180407 3986981 := bbase (se 4 (by rfl) ⟨373779, by rfl⟩ : syracuseStep 3986981 = 747559) (by norm_num)
theorem B2659877 : Blo 1180407 2659877 := bbase (se 4 (by rfl) ⟨249363, by rfl⟩ : syracuseStep 2659877 = 498727) (by norm_num)
theorem B2242093 : Blo 1180407 2242093 := bbase (se 3 (by rfl) ⟨420392, by rfl⟩ : syracuseStep 2242093 = 840785) (by norm_num)
theorem B3192389 : Blo 1180407 3192389 := bbase (se 4 (by rfl) ⟨299286, by rfl⟩ : syracuseStep 3192389 = 598573) (by norm_num)
theorem B2692685 : Blo 1180407 2692685 := bbase (se 3 (by rfl) ⟨504878, by rfl⟩ : syracuseStep 2692685 = 1009757) (by norm_num)
theorem B2659949 : Blo 1180407 2659949 := bbase (se 3 (by rfl) ⟨498740, by rfl⟩ : syracuseStep 2659949 = 997481) (by norm_num)
theorem B3593845 : Blo 1180407 3593845 := bbase (se 5 (by rfl) ⟨168461, by rfl⟩ : syracuseStep 3593845 = 336923) (by norm_num)
theorem B2692757 : Blo 1180407 2692757 := bbase (se 6 (by rfl) ⟨63111, by rfl⟩ : syracuseStep 2692757 = 126223) (by norm_num)
theorem B3364517 : Blo 1180407 3364517 := bbase (se 4 (by rfl) ⟨315423, by rfl⟩ : syracuseStep 3364517 = 630847) (by norm_num)
theorem B2660021 : Blo 1180407 2660021 := bbase (se 5 (by rfl) ⟨124688, by rfl⟩ : syracuseStep 2660021 = 249377) (by norm_num)
theorem B2242237 : Blo 1180407 2242237 := bbase (se 3 (by rfl) ⟨420419, by rfl⟩ : syracuseStep 2242237 = 840839) (by norm_num)
theorem B5043941 : Blo 1180407 5043941 := bbase (se 4 (by rfl) ⟨472869, by rfl⟩ : syracuseStep 5043941 = 945739) (by norm_num)
theorem B2660093 : Blo 1180407 2660093 := bbase (se 3 (by rfl) ⟨498767, by rfl⟩ : syracuseStep 2660093 = 997535) (by norm_num)
theorem B2660165 : Blo 1180407 2660165 := bbase (se 4 (by rfl) ⟨249390, by rfl⟩ : syracuseStep 2660165 = 498781) (by norm_num)
theorem B2242397 : Blo 1180407 2242397 := bbase (se 3 (by rfl) ⟨420449, by rfl⟩ : syracuseStep 2242397 = 840899) (by norm_num)
theorem B2660237 : Blo 1180407 2660237 := bbase (se 3 (by rfl) ⟨498794, by rfl⟩ : syracuseStep 2660237 = 997589) (by norm_num)
theorem B3987413 : Blo 1180407 3987413 := bbase (se 7 (by rfl) ⟨46727, by rfl⟩ : syracuseStep 3987413 = 93455) (by norm_num)
theorem B2660309 : Blo 1180407 2660309 := bbase (se 7 (by rfl) ⟨31175, by rfl⟩ : syracuseStep 2660309 = 62351) (by norm_num)
theorem B2242541 : Blo 1180407 2242541 := bbase (se 3 (by rfl) ⟨420476, by rfl⟩ : syracuseStep 2242541 = 840953) (by norm_num)
theorem B2988029 : Blo 1180407 2988029 := bbase (se 3 (by rfl) ⟨560255, by rfl⟩ : syracuseStep 2988029 = 1120511) (by norm_num)
theorem B2660381 : Blo 1180407 2660381 := bbase (se 3 (by rfl) ⟨498821, by rfl⟩ : syracuseStep 2660381 = 997643) (by norm_num)
theorem B2521133 : Blo 1180407 2521133 := bbase (se 3 (by rfl) ⟨472712, by rfl⟩ : syracuseStep 2521133 = 945425) (by norm_num)
theorem B2021429 : Blo 1180407 2021429 := bbase (se 5 (by rfl) ⟨94754, by rfl⟩ : syracuseStep 2021429 = 189509) (by norm_num)
theorem B6387893 : Blo 1180407 6387893 := bbase (se 5 (by rfl) ⟨299432, by rfl⟩ : syracuseStep 6387893 = 598865) (by norm_num)
theorem B2840773 : Blo 1180407 2840773 := bbase (se 4 (by rfl) ⟨266322, by rfl⟩ : syracuseStep 2840773 = 532645) (by norm_num)
theorem B4856021 : Blo 1180407 4856021 := bbase (se 7 (by rfl) ⟨56906, by rfl⟩ : syracuseStep 4856021 = 113813) (by norm_num)
theorem B2242829 : Blo 1180407 2242829 := bbase (se 3 (by rfl) ⟨420530, by rfl⟩ : syracuseStep 2242829 = 841061) (by norm_num)
theorem B2988373 : Blo 1180407 2988373 := bbase (se 10 (by rfl) ⟨4377, by rfl⟩ : syracuseStep 2988373 = 8755) (by norm_num)
theorem B3987845 : Blo 1180407 3987845 := bbase (se 4 (by rfl) ⟨373860, by rfl⟩ : syracuseStep 3987845 = 747721) (by norm_num)
theorem B2242981 : Blo 1180407 2242981 := bbase (se 4 (by rfl) ⟨210279, by rfl⟩ : syracuseStep 2242981 = 420559) (by norm_num)
theorem B2988485 : Blo 1180407 2988485 := bbase (se 4 (by rfl) ⟨280170, by rfl⟩ : syracuseStep 2988485 = 560341) (by norm_num)
theorem B1890901 : Blo 1180407 1890901 := bbase (se 8 (by rfl) ⟨11079, by rfl⟩ : syracuseStep 1890901 = 22159) (by norm_num)
theorem B2988677 : Blo 1180407 2988677 := bbase (se 4 (by rfl) ⟨280188, by rfl⟩ : syracuseStep 2988677 = 560377) (by norm_num)
theorem B3365509 : Blo 1180407 3365509 := bbase (se 4 (by rfl) ⟨315516, by rfl⟩ : syracuseStep 3365509 = 631033) (by norm_num)
theorem B4487845 : Blo 1180407 4487845 := bbase (se 4 (by rfl) ⟨420735, by rfl⟩ : syracuseStep 4487845 = 841471) (by norm_num)
theorem B2243285 : Blo 1180407 2243285 := bbase (se 7 (by rfl) ⟨26288, by rfl⟩ : syracuseStep 2243285 = 52577) (by norm_num)
theorem B4258565 : Blo 1180407 4258565 := bbase (se 4 (by rfl) ⟨399240, by rfl⟩ : syracuseStep 4258565 = 798481) (by norm_num)
theorem B5978933 : Blo 1180407 5978933 := bbase (se 5 (by rfl) ⟨280262, by rfl⟩ : syracuseStep 5978933 = 560525) (by norm_num)
theorem B3988277 : Blo 1180407 3988277 := bbase (se 5 (by rfl) ⟨186950, by rfl⟩ : syracuseStep 3988277 = 373901) (by norm_num)
theorem B11344789 : Blo 1180407 11344789 := bbase (se 6 (by rfl) ⟨265893, by rfl⟩ : syracuseStep 11344789 = 531787) (by norm_num)
theorem B2522021 : Blo 1180407 2522021 := bbase (se 4 (by rfl) ⟨236439, by rfl⟩ : syracuseStep 2522021 = 472879) (by norm_num)
theorem B17030101 : Blo 1180407 17030101 := bbase (se 7 (by rfl) ⟨199571, by rfl⟩ : syracuseStep 17030101 = 399143) (by norm_num)
theorem B4488149 : Blo 1180407 4488149 := bbase (se 7 (by rfl) ⟨52595, by rfl⟩ : syracuseStep 4488149 = 105191) (by norm_num)
theorem B2989021 : Blo 1180407 2989021 := bbase (se 3 (by rfl) ⟨560441, by rfl⟩ : syracuseStep 2989021 = 1120883) (by norm_num)
theorem B1891325 : Blo 1180407 1891325 := bbase (se 3 (by rfl) ⟨354623, by rfl⟩ : syracuseStep 1891325 = 709247) (by norm_num)
theorem B5676085 : Blo 1180407 5676085 := bbase (se 5 (by rfl) ⟨266066, by rfl⟩ : syracuseStep 5676085 = 532133) (by norm_num)
theorem B2989133 : Blo 1180407 2989133 := bbase (se 3 (by rfl) ⟨560462, by rfl⟩ : syracuseStep 2989133 = 1120925) (by norm_num)
theorem B11361397 : Blo 1180407 11361397 := bbase (se 5 (by rfl) ⟨532565, by rfl⟩ : syracuseStep 11361397 = 1065131) (by norm_num)
theorem B2522261 : Blo 1180407 2522261 := bbase (se 6 (by rfl) ⟨59115, by rfl⟩ : syracuseStep 2522261 = 118231) (by norm_num)
theorem B2129125 : Blo 1180407 2129125 := bbase (se 4 (by rfl) ⟨199605, by rfl⟩ : syracuseStep 2129125 = 399211) (by norm_num)
theorem B3988709 : Blo 1180407 3988709 := bbase (se 4 (by rfl) ⟨373941, by rfl⟩ : syracuseStep 3988709 = 747883) (by norm_num)
theorem B4857077 : Blo 1180407 4857077 := bbase (se 5 (by rfl) ⟨227675, by rfl⟩ : syracuseStep 4857077 = 455351) (by norm_num)
theorem B2989325 : Blo 1180407 2989325 := bbase (se 3 (by rfl) ⟨560498, by rfl⟩ : syracuseStep 2989325 = 1120997) (by norm_num)
theorem B1891613 : Blo 1180407 1891613 := bbase (se 3 (by rfl) ⟨354677, by rfl⟩ : syracuseStep 1891613 = 709355) (by norm_num)
theorem B1260857 : Blo 1180407 1260857 := bbase (se 2 (by rfl) ⟨472821, by rfl⟩ : syracuseStep 1260857 = 945643) (by norm_num)
theorem B4545877 : Blo 1180407 4545877 := bbase (se 11 (by rfl) ⟨3329, by rfl⟩ : syracuseStep 4545877 = 6659) (by norm_num)
theorem B2694509 : Blo 1180407 2694509 := bbase (se 3 (by rfl) ⟨505220, by rfl⟩ : syracuseStep 2694509 = 1010441) (by norm_num)
theorem B6733205 : Blo 1180407 6733205 := bbase (se 6 (by rfl) ⟨157809, by rfl⟩ : syracuseStep 6733205 = 315619) (by norm_num)
theorem B2244037 : Blo 1180407 2244037 := bbase (se 4 (by rfl) ⟨210378, by rfl⟩ : syracuseStep 2244037 = 420757) (by norm_num)
theorem B8977877 : Blo 1180407 8977877 := bbase (se 7 (by rfl) ⟨105209, by rfl⟩ : syracuseStep 8977877 = 210419) (by norm_num)
theorem B1261045 : Blo 1180407 1261045 := bbase (se 5 (by rfl) ⟨59111, by rfl⟩ : syracuseStep 1261045 = 118223) (by norm_num)
theorem B2244181 : Blo 1180407 2244181 := bbase (se 8 (by rfl) ⟨13149, by rfl⟩ : syracuseStep 2244181 = 26299) (by norm_num)
theorem B2989669 : Blo 1180407 2989669 := bbase (se 4 (by rfl) ⟨280281, by rfl⟩ : syracuseStep 2989669 = 560563) (by norm_num)
theorem B2522765 : Blo 1180407 2522765 := bbase (se 3 (by rfl) ⟨473018, by rfl⟩ : syracuseStep 2522765 = 946037) (by norm_num)
theorem B2522773 : Blo 1180407 2522773 := bbase (se 6 (by rfl) ⟨59127, by rfl⟩ : syracuseStep 2522773 = 118255) (by norm_num)
theorem B3989141 : Blo 1180407 3989141 := bbase (se 6 (by rfl) ⟨93495, by rfl⟩ : syracuseStep 3989141 = 186991) (by norm_num)
theorem B2989781 : Blo 1180407 2989781 := bbase (se 7 (by rfl) ⟨35036, by rfl⟩ : syracuseStep 2989781 = 70073) (by norm_num)
theorem B3366613 : Blo 1180407 3366613 := bbase (se 7 (by rfl) ⟨39452, by rfl⟩ : syracuseStep 3366613 = 78905) (by norm_num)
theorem B2244341 : Blo 1180407 2244341 := bbase (se 5 (by rfl) ⟨105203, by rfl⟩ : syracuseStep 2244341 = 210407) (by norm_num)
theorem B1916765 : Blo 1180407 1916765 := bbase (se 3 (by rfl) ⟨359393, by rfl⟩ : syracuseStep 1916765 = 718787) (by norm_num)
theorem B8970101 : Blo 1180407 8970101 := bbase (se 5 (by rfl) ⟨420473, by rfl⟩ : syracuseStep 8970101 = 840947) (by norm_num)
theorem B2244485 : Blo 1180407 2244485 := bbase (se 4 (by rfl) ⟨210420, by rfl⟩ : syracuseStep 2244485 = 420841) (by norm_num)
theorem B2875285 : Blo 1180407 2875285 := bbase (se 6 (by rfl) ⟨67389, by rfl⟩ : syracuseStep 2875285 = 134779) (by norm_num)
theorem B2989973 : Blo 1180407 2989973 := bbase (se 6 (by rfl) ⟨70077, by rfl⟩ : syracuseStep 2989973 = 140155) (by norm_num)
theorem B5046229 : Blo 1180407 5046229 := bbase (se 7 (by rfl) ⟨59135, by rfl⟩ : syracuseStep 5046229 = 118271) (by norm_num)
theorem B5390477 : Blo 1180407 5390477 := bstep (se 3 (by rfl) ⟨1010714, by rfl⟩ : syracuseStep 5390477 = 2021429) B2021429
theorem B3989681 : Blo 1180407 3989681 := bstep (se 2 (by rfl) ⟨1496130, by rfl⟩ : syracuseStep 3989681 = 2992261) B2992261
theorem B10100933 : Blo 1180407 10100933 := bstep (se 4 (by rfl) ⟨946962, by rfl⟩ : syracuseStep 10100933 = 1893925) B1893925
theorem B1597649 : Blo 1180407 1597649 := bstep (se 2 (by rfl) ⟨599118, by rfl⟩ : syracuseStep 1597649 = 1198237) B1198237
theorem B10092869 : Blo 1180407 10092869 := bstep (se 4 (by rfl) ⟨946206, by rfl⟩ : syracuseStep 10092869 = 1892413) B1892413
theorem B2523491 : Blo 1180407 2523491 := bstep (se 1 (by rfl) ⟨1892618, by rfl⟩ : syracuseStep 2523491 = 3785237) B3785237
theorem B3457507 : Blo 1180407 3457507 := bstep (se 1 (by rfl) ⟨2593130, by rfl⟩ : syracuseStep 3457507 = 5186261) B5186261
theorem B2990641 : Blo 1180407 2990641 := bstep (se 2 (by rfl) ⟨1121490, by rfl⟩ : syracuseStep 2990641 = 2242981) B2242981
theorem B1262147 : Blo 1180407 1262147 := bstep (se 1 (by rfl) ⟨946610, by rfl⟩ : syracuseStep 1262147 = 1893221) B1893221
theorem B2130545 : Blo 1180407 2130545 := bstep (se 2 (by rfl) ⟨798954, by rfl⟩ : syracuseStep 2130545 = 1597909) B1597909
theorem B1704611 : Blo 1180407 1704611 := bstep (se 1 (by rfl) ⟨1278458, by rfl⟩ : syracuseStep 1704611 = 2556917) B2556917
theorem B1516195 : Blo 1180407 1516195 := bstep (se 1 (by rfl) ⟨1137146, by rfl⟩ : syracuseStep 1516195 = 2274293) B2274293
theorem B5980877 : Blo 1180407 5980877 := bstep (se 3 (by rfl) ⟨1121414, by rfl⟩ : syracuseStep 5980877 = 2242829) B2242829
theorem B3990221 : Blo 1180407 3990221 := bstep (se 3 (by rfl) ⟨748166, by rfl⟩ : syracuseStep 3990221 = 1496333) B1496333
theorem B1180419 : Blo 1180407 1180419 := bstep (se 1 (by rfl) ⟨885314, by rfl⟩ : syracuseStep 1180419 = 1770629) B1770629
theorem B3990275 : Blo 1180407 3990275 := bstep (se 1 (by rfl) ⟨2992706, by rfl⟩ : syracuseStep 3990275 = 5985413) B5985413
theorem B1180435 : Blo 1180407 1180435 := bstep (se 1 (by rfl) ⟨885326, by rfl⟩ : syracuseStep 1180435 = 1770653) B1770653
theorem B1180451 : Blo 1180407 1180451 := bstep (se 1 (by rfl) ⟨885338, by rfl⟩ : syracuseStep 1180451 = 1770677) B1770677
theorem B2523953 : Blo 1180407 2523953 := bstep (se 2 (by rfl) ⟨946482, by rfl⟩ : syracuseStep 2523953 = 1892965) B1892965
theorem B1180467 : Blo 1180407 1180467 := bstep (se 1 (by rfl) ⟨885350, by rfl⟩ : syracuseStep 1180467 = 1770701) B1770701
theorem B1180483 : Blo 1180407 1180483 := bstep (se 1 (by rfl) ⟨885362, by rfl⟩ : syracuseStep 1180483 = 1770725) B1770725
theorem B2990915 : Blo 1180407 2990915 := bstep (se 1 (by rfl) ⟨2243186, by rfl⟩ : syracuseStep 2990915 = 4486373) B4486373
theorem B6824773 : Blo 1180407 6824773 := bstep (se 4 (by rfl) ⟨639822, by rfl⟩ : syracuseStep 6824773 = 1279645) B1279645
theorem B1180499 : Blo 1180407 1180499 := bstep (se 1 (by rfl) ⟨885374, by rfl⟩ : syracuseStep 1180499 = 1770749) B1770749
theorem B1180515 : Blo 1180407 1180515 := bstep (se 1 (by rfl) ⟨885386, by rfl⟩ : syracuseStep 1180515 = 1770773) B1770773
theorem B1180531 : Blo 1180407 1180531 := bstep (se 1 (by rfl) ⟨885398, by rfl⟩ : syracuseStep 1180531 = 1770797) B1770797
theorem B1180547 : Blo 1180407 1180547 := bstep (se 1 (by rfl) ⟨885410, by rfl⟩ : syracuseStep 1180547 = 1770821) B1770821
theorem B1180563 : Blo 1180407 1180563 := bstep (se 1 (by rfl) ⟨885422, by rfl⟩ : syracuseStep 1180563 = 1770845) B1770845
theorem B1794977 : Blo 1180407 1794977 := bstep (se 2 (by rfl) ⟨673116, by rfl⟩ : syracuseStep 1794977 = 1346233) B1346233
theorem B1328035 : Blo 1180407 1328035 := bstep (se 1 (by rfl) ⟨996026, by rfl⟩ : syracuseStep 1328035 = 1992053) B1992053
theorem B1180579 : Blo 1180407 1180579 := bstep (se 1 (by rfl) ⟨885434, by rfl⟩ : syracuseStep 1180579 = 1770869) B1770869
theorem B1180595 : Blo 1180407 1180595 := bstep (se 1 (by rfl) ⟨885446, by rfl⟩ : syracuseStep 1180595 = 1770893) B1770893
theorem B1180611 : Blo 1180407 1180611 := bstep (se 1 (by rfl) ⟨885458, by rfl⟩ : syracuseStep 1180611 = 1770917) B1770917
theorem B1180627 : Blo 1180407 1180627 := bstep (se 1 (by rfl) ⟨885470, by rfl⟩ : syracuseStep 1180627 = 1770941) B1770941
theorem B1180643 : Blo 1180407 1180643 := bstep (se 1 (by rfl) ⟨885482, by rfl⟩ : syracuseStep 1180643 = 1770965) B1770965
theorem B1180659 : Blo 1180407 1180659 := bstep (se 1 (by rfl) ⟨885494, by rfl⟩ : syracuseStep 1180659 = 1770989) B1770989
theorem B1180675 : Blo 1180407 1180675 := bstep (se 1 (by rfl) ⟨885506, by rfl⟩ : syracuseStep 1180675 = 1771013) B1771013
theorem B2991107 : Blo 1180407 2991107 := bstep (se 1 (by rfl) ⟨2243330, by rfl⟩ : syracuseStep 2991107 = 4486661) B4486661
theorem B3990545 : Blo 1180407 3990545 := bstep (se 2 (by rfl) ⟨1496454, by rfl⟩ : syracuseStep 3990545 = 2992909) B2992909
theorem B1180691 : Blo 1180407 1180691 := bstep (se 1 (by rfl) ⟨885518, by rfl⟩ : syracuseStep 1180691 = 1771037) B1771037
theorem B1180707 : Blo 1180407 1180707 := bstep (se 1 (by rfl) ⟨885530, by rfl⟩ : syracuseStep 1180707 = 1771061) B1771061
theorem B1328179 : Blo 1180407 1328179 := bstep (se 1 (by rfl) ⟨996134, by rfl⟩ : syracuseStep 1328179 = 1992269) B1992269
theorem B1795123 : Blo 1180407 1795123 := bstep (se 1 (by rfl) ⟨1346342, by rfl⟩ : syracuseStep 1795123 = 2692685) B2692685
theorem B1180723 : Blo 1180407 1180723 := bstep (se 1 (by rfl) ⟨885542, by rfl⟩ : syracuseStep 1180723 = 1771085) B1771085
theorem B1180739 : Blo 1180407 1180739 := bstep (se 1 (by rfl) ⟨885554, by rfl⟩ : syracuseStep 1180739 = 1771109) B1771109
theorem B15131717 : Blo 1180407 15131717 := bstep (se 4 (by rfl) ⟨1418598, by rfl⟩ : syracuseStep 15131717 = 2837197) B2837197
theorem B1180755 : Blo 1180407 1180755 := bstep (se 1 (by rfl) ⟨885566, by rfl⟩ : syracuseStep 1180755 = 1771133) B1771133
theorem B1795171 : Blo 1180407 1795171 := bstep (se 1 (by rfl) ⟨1346378, by rfl⟩ : syracuseStep 1795171 = 2692757) B2692757
theorem B1180771 : Blo 1180407 1180771 := bstep (se 1 (by rfl) ⟨885578, by rfl⟩ : syracuseStep 1180771 = 1771157) B1771157
theorem B14566499 : Blo 1180407 14566499 := bstep (se 1 (by rfl) ⟨10924874, by rfl⟩ : syracuseStep 14566499 = 21849749) B21849749
theorem B1770611 : Blo 1180407 1770611 := bstep (se 1 (by rfl) ⟨1327958, by rfl⟩ : syracuseStep 1770611 = 2655917) B2655917
theorem B1180787 : Blo 1180407 1180787 := bstep (se 1 (by rfl) ⟨885590, by rfl⟩ : syracuseStep 1180787 = 1771181) B1771181
theorem B1180803 : Blo 1180407 1180803 := bstep (se 1 (by rfl) ⟨885602, by rfl⟩ : syracuseStep 1180803 = 1771205) B1771205
theorem B1770641 : Blo 1180407 1770641 := bstep (se 2 (by rfl) ⟨663990, by rfl⟩ : syracuseStep 1770641 = 1327981) B1327981
theorem B1180819 : Blo 1180407 1180819 := bstep (se 1 (by rfl) ⟨885614, by rfl⟩ : syracuseStep 1180819 = 1771229) B1771229
theorem B1770659 : Blo 1180407 1770659 := bstep (se 1 (by rfl) ⟨1327994, by rfl⟩ : syracuseStep 1770659 = 2655989) B2655989
theorem B1180835 : Blo 1180407 1180835 := bstep (se 1 (by rfl) ⟨885626, by rfl⟩ : syracuseStep 1180835 = 1771253) B1771253
theorem B1180851 : Blo 1180407 1180851 := bstep (se 1 (by rfl) ⟨885638, by rfl⟩ : syracuseStep 1180851 = 1771277) B1771277
theorem B1770689 : Blo 1180407 1770689 := bstep (se 2 (by rfl) ⟨664008, by rfl⟩ : syracuseStep 1770689 = 1328017) B1328017
theorem B1328323 : Blo 1180407 1328323 := bstep (se 1 (by rfl) ⟨996242, by rfl⟩ : syracuseStep 1328323 = 1992485) B1992485
theorem B1180867 : Blo 1180407 1180867 := bstep (se 1 (by rfl) ⟨885650, by rfl⟩ : syracuseStep 1180867 = 1771301) B1771301
theorem B1770707 : Blo 1180407 1770707 := bstep (se 1 (by rfl) ⟨1328030, by rfl⟩ : syracuseStep 1770707 = 2656061) B2656061
theorem B1180883 : Blo 1180407 1180883 := bstep (se 1 (by rfl) ⟨885662, by rfl⟩ : syracuseStep 1180883 = 1771325) B1771325
theorem B1180899 : Blo 1180407 1180899 := bstep (se 1 (by rfl) ⟨885674, by rfl⟩ : syracuseStep 1180899 = 1771349) B1771349
theorem B1770737 : Blo 1180407 1770737 := bstep (se 2 (by rfl) ⟨664026, by rfl⟩ : syracuseStep 1770737 = 1328053) B1328053
theorem B1180915 : Blo 1180407 1180915 := bstep (se 1 (by rfl) ⟨885686, by rfl⟩ : syracuseStep 1180915 = 1771373) B1771373
theorem B1770755 : Blo 1180407 1770755 := bstep (se 1 (by rfl) ⟨1328066, by rfl⟩ : syracuseStep 1770755 = 2656133) B2656133
theorem B1180931 : Blo 1180407 1180931 := bstep (se 1 (by rfl) ⟨885698, by rfl⟩ : syracuseStep 1180931 = 1771397) B1771397
theorem B4482317 : Blo 1180407 4482317 := bstep (se 3 (by rfl) ⟨840434, by rfl⟩ : syracuseStep 4482317 = 1680869) B1680869
theorem B1180947 : Blo 1180407 1180947 := bstep (se 1 (by rfl) ⟨885710, by rfl⟩ : syracuseStep 1180947 = 1771421) B1771421
theorem B1770785 : Blo 1180407 1770785 := bstep (se 2 (by rfl) ⟨664044, by rfl⟩ : syracuseStep 1770785 = 1328089) B1328089
theorem B1180963 : Blo 1180407 1180963 := bstep (se 1 (by rfl) ⟨885722, by rfl⟩ : syracuseStep 1180963 = 1771445) B1771445
theorem B1770803 : Blo 1180407 1770803 := bstep (se 1 (by rfl) ⟨1328102, by rfl⟩ : syracuseStep 1770803 = 2656205) B2656205
theorem B1180979 : Blo 1180407 1180979 := bstep (se 1 (by rfl) ⟨885734, by rfl⟩ : syracuseStep 1180979 = 1771469) B1771469
theorem B1180995 : Blo 1180407 1180995 := bstep (se 1 (by rfl) ⟨885746, by rfl⟩ : syracuseStep 1180995 = 1771493) B1771493
theorem B1770833 : Blo 1180407 1770833 := bstep (se 2 (by rfl) ⟨664062, by rfl⟩ : syracuseStep 1770833 = 1328125) B1328125
theorem B1992019 : Blo 1180407 1992019 := bstep (se 1 (by rfl) ⟨1494014, by rfl⟩ : syracuseStep 1992019 = 2988029) B2988029
theorem B1328467 : Blo 1180407 1328467 := bstep (se 1 (by rfl) ⟨996350, by rfl⟩ : syracuseStep 1328467 = 1992701) B1992701
theorem B1181011 : Blo 1180407 1181011 := bstep (se 1 (by rfl) ⟨885758, by rfl⟩ : syracuseStep 1181011 = 1771517) B1771517
theorem B1770851 : Blo 1180407 1770851 := bstep (se 1 (by rfl) ⟨1328138, by rfl⟩ : syracuseStep 1770851 = 2656277) B2656277
theorem B1181027 : Blo 1180407 1181027 := bstep (se 1 (by rfl) ⟨885770, by rfl⟩ : syracuseStep 1181027 = 1771541) B1771541
theorem B1680755 : Blo 1180407 1680755 := bstep (se 1 (by rfl) ⟨1260566, by rfl⟩ : syracuseStep 1680755 = 2521133) B2521133
theorem B1181043 : Blo 1180407 1181043 := bstep (se 1 (by rfl) ⟨885782, by rfl⟩ : syracuseStep 1181043 = 1771565) B1771565
theorem B1770881 : Blo 1180407 1770881 := bstep (se 2 (by rfl) ⟨664080, by rfl⟩ : syracuseStep 1770881 = 1328161) B1328161
theorem B1181059 : Blo 1180407 1181059 := bstep (se 1 (by rfl) ⟨885794, by rfl⟩ : syracuseStep 1181059 = 1771589) B1771589
theorem B1770899 : Blo 1180407 1770899 := bstep (se 1 (by rfl) ⟨1328174, by rfl⟩ : syracuseStep 1770899 = 2656349) B2656349
theorem B1181075 : Blo 1180407 1181075 := bstep (se 1 (by rfl) ⟨885806, by rfl⟩ : syracuseStep 1181075 = 1771613) B1771613
theorem B1181091 : Blo 1180407 1181091 := bstep (se 1 (by rfl) ⟨885818, by rfl⟩ : syracuseStep 1181091 = 1771637) B1771637
theorem B1770929 : Blo 1180407 1770929 := bstep (se 2 (by rfl) ⟨664098, by rfl⟩ : syracuseStep 1770929 = 1328197) B1328197
theorem B1181107 : Blo 1180407 1181107 := bstep (se 1 (by rfl) ⟨885830, by rfl⟩ : syracuseStep 1181107 = 1771661) B1771661
theorem B1770947 : Blo 1180407 1770947 := bstep (se 1 (by rfl) ⟨1328210, by rfl⟩ : syracuseStep 1770947 = 2656421) B2656421
theorem B1181123 : Blo 1180407 1181123 := bstep (se 1 (by rfl) ⟨885842, by rfl⟩ : syracuseStep 1181123 = 1771685) B1771685
theorem B3032515 : Blo 1180407 3032515 := bstep (se 1 (by rfl) ⟨2274386, by rfl⟩ : syracuseStep 3032515 = 4548773) B4548773
theorem B20194757 : Blo 1180407 20194757 := bstep (se 4 (by rfl) ⟨1893258, by rfl⟩ : syracuseStep 20194757 = 3786517) B3786517
theorem B1181139 : Blo 1180407 1181139 := bstep (se 1 (by rfl) ⟨885854, by rfl⟩ : syracuseStep 1181139 = 1771709) B1771709
theorem B1992161 : Blo 1180407 1992161 := bstep (se 2 (by rfl) ⟨747060, by rfl⟩ : syracuseStep 1992161 = 1494121) B1494121
theorem B1770977 : Blo 1180407 1770977 := bstep (se 2 (by rfl) ⟨664116, by rfl⟩ : syracuseStep 1770977 = 1328233) B1328233
theorem B1328611 : Blo 1180407 1328611 := bstep (se 1 (by rfl) ⟨996458, by rfl⟩ : syracuseStep 1328611 = 1992917) B1992917
theorem B1181155 : Blo 1180407 1181155 := bstep (se 1 (by rfl) ⟨885866, by rfl⟩ : syracuseStep 1181155 = 1771733) B1771733
theorem B3237347 : Blo 1180407 3237347 := bstep (se 1 (by rfl) ⟨2428010, by rfl⟩ : syracuseStep 3237347 = 4856021) B4856021
theorem B15148529 : Blo 1180407 15148529 := bstep (se 2 (by rfl) ⟨5680698, by rfl⟩ : syracuseStep 15148529 = 11361397) B11361397
theorem B1770995 : Blo 1180407 1770995 := bstep (se 1 (by rfl) ⟨1328246, by rfl⟩ : syracuseStep 1770995 = 2656493) B2656493
theorem B1181171 : Blo 1180407 1181171 := bstep (se 1 (by rfl) ⟨885878, by rfl⟩ : syracuseStep 1181171 = 1771757) B1771757
theorem B1181187 : Blo 1180407 1181187 := bstep (se 1 (by rfl) ⟨885890, by rfl⟩ : syracuseStep 1181187 = 1771781) B1771781
theorem B1771025 : Blo 1180407 1771025 := bstep (se 2 (by rfl) ⟨664134, by rfl⟩ : syracuseStep 1771025 = 1328269) B1328269
theorem B1181203 : Blo 1180407 1181203 := bstep (se 1 (by rfl) ⟨885902, by rfl⟩ : syracuseStep 1181203 = 1771805) B1771805
theorem B1771043 : Blo 1180407 1771043 := bstep (se 1 (by rfl) ⟨1328282, by rfl⟩ : syracuseStep 1771043 = 2656565) B2656565
theorem B1181219 : Blo 1180407 1181219 := bstep (se 1 (by rfl) ⟨885914, by rfl⟩ : syracuseStep 1181219 = 1771829) B1771829
theorem B1181235 : Blo 1180407 1181235 := bstep (se 1 (by rfl) ⟨885926, by rfl⟩ : syracuseStep 1181235 = 1771853) B1771853
theorem B1771073 : Blo 1180407 1771073 := bstep (se 2 (by rfl) ⟨664152, by rfl⟩ : syracuseStep 1771073 = 1328305) B1328305
theorem B1181251 : Blo 1180407 1181251 := bstep (se 1 (by rfl) ⟨885938, by rfl⟩ : syracuseStep 1181251 = 1771877) B1771877
theorem B1771091 : Blo 1180407 1771091 := bstep (se 1 (by rfl) ⟨1328318, by rfl⟩ : syracuseStep 1771091 = 2656637) B2656637
theorem B1181267 : Blo 1180407 1181267 := bstep (se 1 (by rfl) ⟨885950, by rfl⟩ : syracuseStep 1181267 = 1771901) B1771901
theorem B1992289 : Blo 1180407 1992289 := bstep (se 2 (by rfl) ⟨747108, by rfl⟩ : syracuseStep 1992289 = 1494217) B1494217
theorem B1181283 : Blo 1180407 1181283 := bstep (se 1 (by rfl) ⟨885962, by rfl⟩ : syracuseStep 1181283 = 1771925) B1771925
theorem B1771121 : Blo 1180407 1771121 := bstep (se 2 (by rfl) ⟨664170, by rfl⟩ : syracuseStep 1771121 = 1328341) B1328341
theorem B1328755 : Blo 1180407 1328755 := bstep (se 1 (by rfl) ⟨996566, by rfl⟩ : syracuseStep 1328755 = 1993133) B1993133
theorem B1181299 : Blo 1180407 1181299 := bstep (se 1 (by rfl) ⟨885974, by rfl⟩ : syracuseStep 1181299 = 1771949) B1771949
theorem B1992323 : Blo 1180407 1992323 := bstep (se 1 (by rfl) ⟨1494242, by rfl⟩ : syracuseStep 1992323 = 2988485) B2988485
theorem B1771139 : Blo 1180407 1771139 := bstep (se 1 (by rfl) ⟨1328354, by rfl⟩ : syracuseStep 1771139 = 2656709) B2656709
theorem B1181315 : Blo 1180407 1181315 := bstep (se 1 (by rfl) ⟨885986, by rfl⟩ : syracuseStep 1181315 = 1771973) B1771973
theorem B1181331 : Blo 1180407 1181331 := bstep (se 1 (by rfl) ⟨885998, by rfl⟩ : syracuseStep 1181331 = 1771997) B1771997
theorem B1771169 : Blo 1180407 1771169 := bstep (se 2 (by rfl) ⟨664188, by rfl⟩ : syracuseStep 1771169 = 1328377) B1328377
theorem B1181347 : Blo 1180407 1181347 := bstep (se 1 (by rfl) ⟨886010, by rfl⟩ : syracuseStep 1181347 = 1772021) B1772021
theorem B1771187 : Blo 1180407 1771187 := bstep (se 1 (by rfl) ⟨1328390, by rfl⟩ : syracuseStep 1771187 = 2656781) B2656781
theorem B1181363 : Blo 1180407 1181363 := bstep (se 1 (by rfl) ⟨886022, by rfl⟩ : syracuseStep 1181363 = 1772045) B1772045
theorem B1181379 : Blo 1180407 1181379 := bstep (se 1 (by rfl) ⟨886034, by rfl⟩ : syracuseStep 1181379 = 1772069) B1772069
theorem B6727373 : Blo 1180407 6727373 := bstep (se 3 (by rfl) ⟨1261382, by rfl⟩ : syracuseStep 6727373 = 2522765) B2522765
theorem B2655953 : Blo 1180407 2655953 := bstep (se 2 (by rfl) ⟨995982, by rfl⟩ : syracuseStep 2655953 = 1991965) B1991965
theorem B1771217 : Blo 1180407 1771217 := bstep (se 2 (by rfl) ⟨664206, by rfl⟩ : syracuseStep 1771217 = 1328413) B1328413
theorem B1181395 : Blo 1180407 1181395 := bstep (se 1 (by rfl) ⟨886046, by rfl⟩ : syracuseStep 1181395 = 1772093) B1772093
theorem B2655971 : Blo 1180407 2655971 := bstep (se 1 (by rfl) ⟨1991978, by rfl⟩ : syracuseStep 2655971 = 3983957) B3983957
theorem B1771235 : Blo 1180407 1771235 := bstep (se 1 (by rfl) ⟨1328426, by rfl⟩ : syracuseStep 1771235 = 2656853) B2656853
theorem B1181411 : Blo 1180407 1181411 := bstep (se 1 (by rfl) ⟨886058, by rfl⟩ : syracuseStep 1181411 = 1772117) B1772117
theorem B1181427 : Blo 1180407 1181427 := bstep (se 1 (by rfl) ⟨886070, by rfl⟩ : syracuseStep 1181427 = 1772141) B1772141
theorem B1771265 : Blo 1180407 1771265 := bstep (se 2 (by rfl) ⟨664224, by rfl⟩ : syracuseStep 1771265 = 1328449) B1328449
theorem B1992451 : Blo 1180407 1992451 := bstep (se 1 (by rfl) ⟨1494338, by rfl⟩ : syracuseStep 1992451 = 2988677) B2988677
theorem B1328899 : Blo 1180407 1328899 := bstep (se 1 (by rfl) ⟨996674, by rfl⟩ : syracuseStep 1328899 = 1993349) B1993349
theorem B1181443 : Blo 1180407 1181443 := bstep (se 1 (by rfl) ⟨886082, by rfl⟩ : syracuseStep 1181443 = 1772165) B1772165
theorem B8972045 : Blo 1180407 8972045 := bstep (se 3 (by rfl) ⟨1682258, by rfl⟩ : syracuseStep 8972045 = 3364517) B3364517
theorem B1771283 : Blo 1180407 1771283 := bstep (se 1 (by rfl) ⟨1328462, by rfl⟩ : syracuseStep 1771283 = 2656925) B2656925
theorem B1181459 : Blo 1180407 1181459 := bstep (se 1 (by rfl) ⟨886094, by rfl⟩ : syracuseStep 1181459 = 1772189) B1772189
theorem B1181475 : Blo 1180407 1181475 := bstep (se 1 (by rfl) ⟨886106, by rfl⟩ : syracuseStep 1181475 = 1772213) B1772213
theorem B1771313 : Blo 1180407 1771313 := bstep (se 2 (by rfl) ⟨664242, by rfl⟩ : syracuseStep 1771313 = 1328485) B1328485
theorem B1181491 : Blo 1180407 1181491 := bstep (se 1 (by rfl) ⟨886118, by rfl⟩ : syracuseStep 1181491 = 1772237) B1772237
theorem B1771331 : Blo 1180407 1771331 := bstep (se 1 (by rfl) ⟨1328498, by rfl⟩ : syracuseStep 1771331 = 2656997) B2656997
theorem B1181507 : Blo 1180407 1181507 := bstep (se 1 (by rfl) ⟨886130, by rfl⟩ : syracuseStep 1181507 = 1772261) B1772261
theorem B1181523 : Blo 1180407 1181523 := bstep (se 1 (by rfl) ⟨886142, by rfl⟩ : syracuseStep 1181523 = 1772285) B1772285
theorem B1771361 : Blo 1180407 1771361 := bstep (se 2 (by rfl) ⟨664260, by rfl⟩ : syracuseStep 1771361 = 1328521) B1328521
theorem B7669603 : Blo 1180407 7669603 := bstep (se 1 (by rfl) ⟨5752202, by rfl⟩ : syracuseStep 7669603 = 11504405) B11504405
theorem B1181539 : Blo 1180407 1181539 := bstep (se 1 (by rfl) ⟨886154, by rfl⟩ : syracuseStep 1181539 = 1772309) B1772309
theorem B1771379 : Blo 1180407 1771379 := bstep (se 1 (by rfl) ⟨1328534, by rfl⟩ : syracuseStep 1771379 = 2657069) B2657069
theorem B1181555 : Blo 1180407 1181555 := bstep (se 1 (by rfl) ⟨886166, by rfl⟩ : syracuseStep 1181555 = 1772333) B1772333
theorem B1181571 : Blo 1180407 1181571 := bstep (se 1 (by rfl) ⟨886178, by rfl⟩ : syracuseStep 1181571 = 1772357) B1772357
theorem B1992593 : Blo 1180407 1992593 := bstep (se 2 (by rfl) ⟨747222, by rfl⟩ : syracuseStep 1992593 = 1494445) B1494445
theorem B1771409 : Blo 1180407 1771409 := bstep (se 2 (by rfl) ⟨664278, by rfl⟩ : syracuseStep 1771409 = 1328557) B1328557
theorem B1329043 : Blo 1180407 1329043 := bstep (se 1 (by rfl) ⟨996782, by rfl⟩ : syracuseStep 1329043 = 1993565) B1993565
theorem B1181587 : Blo 1180407 1181587 := bstep (se 1 (by rfl) ⟨886190, by rfl⟩ : syracuseStep 1181587 = 1772381) B1772381
theorem B1771427 : Blo 1180407 1771427 := bstep (se 1 (by rfl) ⟨1328570, by rfl⟩ : syracuseStep 1771427 = 2657141) B2657141
theorem B1181603 : Blo 1180407 1181603 := bstep (se 1 (by rfl) ⟨886202, by rfl⟩ : syracuseStep 1181603 = 1772405) B1772405
theorem B3073969 : Blo 1180407 3073969 := bstep (se 2 (by rfl) ⟨1152738, by rfl⟩ : syracuseStep 3073969 = 2305477) B2305477
theorem B2992049 : Blo 1180407 2992049 := bstep (se 2 (by rfl) ⟨1122018, by rfl⟩ : syracuseStep 2992049 = 2244037) B2244037
theorem B1181619 : Blo 1180407 1181619 := bstep (se 1 (by rfl) ⟨886214, by rfl⟩ : syracuseStep 1181619 = 1772429) B1772429
theorem B1771457 : Blo 1180407 1771457 := bstep (se 2 (by rfl) ⟨664296, by rfl⟩ : syracuseStep 1771457 = 1328593) B1328593
theorem B1181635 : Blo 1180407 1181635 := bstep (se 1 (by rfl) ⟨886226, by rfl⟩ : syracuseStep 1181635 = 1772453) B1772453
theorem B1771475 : Blo 1180407 1771475 := bstep (se 1 (by rfl) ⟨1328606, by rfl⟩ : syracuseStep 1771475 = 2657213) B2657213
theorem B1181651 : Blo 1180407 1181651 := bstep (se 1 (by rfl) ⟨886238, by rfl⟩ : syracuseStep 1181651 = 1772477) B1772477
theorem B1181667 : Blo 1180407 1181667 := bstep (se 1 (by rfl) ⟨886250, by rfl⟩ : syracuseStep 1181667 = 1772501) B1772501
theorem B2992099 : Blo 1180407 2992099 := bstep (se 1 (by rfl) ⟨2244074, by rfl⟩ : syracuseStep 2992099 = 4488149) B4488149
theorem B2656241 : Blo 1180407 2656241 := bstep (se 2 (by rfl) ⟨996090, by rfl⟩ : syracuseStep 2656241 = 1992181) B1992181
theorem B1681393 : Blo 1180407 1681393 := bstep (se 2 (by rfl) ⟨630522, by rfl⟩ : syracuseStep 1681393 = 1261045) B1261045
theorem B1771505 : Blo 1180407 1771505 := bstep (se 2 (by rfl) ⟨664314, by rfl⟩ : syracuseStep 1771505 = 1328629) B1328629
theorem B1181683 : Blo 1180407 1181683 := bstep (se 1 (by rfl) ⟨886262, by rfl⟩ : syracuseStep 1181683 = 1772525) B1772525
theorem B2656259 : Blo 1180407 2656259 := bstep (se 1 (by rfl) ⟨1992194, by rfl⟩ : syracuseStep 2656259 = 3984389) B3984389
theorem B3590147 : Blo 1180407 3590147 := bstep (se 1 (by rfl) ⟨2692610, by rfl⟩ : syracuseStep 3590147 = 5385221) B5385221
theorem B1771523 : Blo 1180407 1771523 := bstep (se 1 (by rfl) ⟨1328642, by rfl⟩ : syracuseStep 1771523 = 2657285) B2657285
theorem B1181699 : Blo 1180407 1181699 := bstep (se 1 (by rfl) ⟨886274, by rfl⟩ : syracuseStep 1181699 = 1772549) B1772549
theorem B1992721 : Blo 1180407 1992721 := bstep (se 2 (by rfl) ⟨747270, by rfl⟩ : syracuseStep 1992721 = 1494541) B1494541
theorem B1181715 : Blo 1180407 1181715 := bstep (se 1 (by rfl) ⟨886286, by rfl⟩ : syracuseStep 1181715 = 1772573) B1772573
theorem B1771553 : Blo 1180407 1771553 := bstep (se 2 (by rfl) ⟨664332, by rfl⟩ : syracuseStep 1771553 = 1328665) B1328665
theorem B1329187 : Blo 1180407 1329187 := bstep (se 1 (by rfl) ⟨996890, by rfl⟩ : syracuseStep 1329187 = 1993781) B1993781
theorem B1181731 : Blo 1180407 1181731 := bstep (se 1 (by rfl) ⟨886298, by rfl⟩ : syracuseStep 1181731 = 1772597) B1772597
theorem B1992755 : Blo 1180407 1992755 := bstep (se 1 (by rfl) ⟨1494566, by rfl⟩ : syracuseStep 1992755 = 2989133) B2989133
theorem B1771571 : Blo 1180407 1771571 := bstep (se 1 (by rfl) ⟨1328678, by rfl⟩ : syracuseStep 1771571 = 2657357) B2657357
theorem B1181747 : Blo 1180407 1181747 := bstep (se 1 (by rfl) ⟨886310, by rfl⟩ : syracuseStep 1181747 = 1772621) B1772621
theorem B1181763 : Blo 1180407 1181763 := bstep (se 1 (by rfl) ⟨886322, by rfl⟩ : syracuseStep 1181763 = 1772645) B1772645
theorem B2525251 : Blo 1180407 2525251 := bstep (se 1 (by rfl) ⟨1893938, by rfl⟩ : syracuseStep 2525251 = 3787877) B3787877
theorem B1771601 : Blo 1180407 1771601 := bstep (se 2 (by rfl) ⟨664350, by rfl⟩ : syracuseStep 1771601 = 1328701) B1328701
theorem B1181779 : Blo 1180407 1181779 := bstep (se 1 (by rfl) ⟨886334, by rfl⟩ : syracuseStep 1181779 = 1772669) B1772669
theorem B1681507 : Blo 1180407 1681507 := bstep (se 1 (by rfl) ⟨1261130, by rfl⟩ : syracuseStep 1681507 = 2522261) B2522261
theorem B2394211 : Blo 1180407 2394211 := bstep (se 1 (by rfl) ⟨1795658, by rfl⟩ : syracuseStep 2394211 = 3591317) B3591317
theorem B1771619 : Blo 1180407 1771619 := bstep (se 1 (by rfl) ⟨1328714, by rfl⟩ : syracuseStep 1771619 = 2657429) B2657429
theorem B1181795 : Blo 1180407 1181795 := bstep (se 1 (by rfl) ⟨886346, by rfl⟩ : syracuseStep 1181795 = 1772693) B1772693
theorem B30673009 : Blo 1180407 30673009 := bstep (se 2 (by rfl) ⟨11502378, by rfl⟩ : syracuseStep 30673009 = 23004757) B23004757
theorem B1181811 : Blo 1180407 1181811 := bstep (se 1 (by rfl) ⟨886358, by rfl⟩ : syracuseStep 1181811 = 1772717) B1772717
theorem B2992241 : Blo 1180407 2992241 := bstep (se 2 (by rfl) ⟨1122090, by rfl⟩ : syracuseStep 2992241 = 2244181) B2244181
theorem B1771649 : Blo 1180407 1771649 := bstep (se 2 (by rfl) ⟨664368, by rfl⟩ : syracuseStep 1771649 = 1328737) B1328737
theorem B1181827 : Blo 1180407 1181827 := bstep (se 1 (by rfl) ⟨886370, by rfl⟩ : syracuseStep 1181827 = 1772741) B1772741
theorem B6473861 : Blo 1180407 6473861 := bstep (se 4 (by rfl) ⟨606924, by rfl⟩ : syracuseStep 6473861 = 1213849) B1213849
theorem B5384333 : Blo 1180407 5384333 := bstep (se 3 (by rfl) ⟨1009562, by rfl⟩ : syracuseStep 5384333 = 2019125) B2019125
theorem B1771667 : Blo 1180407 1771667 := bstep (se 1 (by rfl) ⟨1328750, by rfl⟩ : syracuseStep 1771667 = 2657501) B2657501
theorem B1181843 : Blo 1180407 1181843 := bstep (se 1 (by rfl) ⟨886382, by rfl⟩ : syracuseStep 1181843 = 1772765) B1772765
theorem B3238051 : Blo 1180407 3238051 := bstep (se 1 (by rfl) ⟨2428538, by rfl⟩ : syracuseStep 3238051 = 4857077) B4857077
theorem B1181859 : Blo 1180407 1181859 := bstep (se 1 (by rfl) ⟨886394, by rfl⟩ : syracuseStep 1181859 = 1772789) B1772789
theorem B1771697 : Blo 1180407 1771697 := bstep (se 2 (by rfl) ⟨664386, by rfl⟩ : syracuseStep 1771697 = 1328773) B1328773
theorem B1992883 : Blo 1180407 1992883 := bstep (se 1 (by rfl) ⟨1494662, by rfl⟩ : syracuseStep 1992883 = 2989325) B2989325
theorem B1329331 : Blo 1180407 1329331 := bstep (se 1 (by rfl) ⟨996998, by rfl⟩ : syracuseStep 1329331 = 1993997) B1993997
theorem B1181875 : Blo 1180407 1181875 := bstep (se 1 (by rfl) ⟨886406, by rfl⟩ : syracuseStep 1181875 = 1772813) B1772813
theorem B1771715 : Blo 1180407 1771715 := bstep (se 1 (by rfl) ⟨1328786, by rfl⟩ : syracuseStep 1771715 = 2657573) B2657573
theorem B1181891 : Blo 1180407 1181891 := bstep (se 1 (by rfl) ⟨886418, by rfl⟩ : syracuseStep 1181891 = 1772837) B1772837
theorem B1181907 : Blo 1180407 1181907 := bstep (se 1 (by rfl) ⟨886430, by rfl⟩ : syracuseStep 1181907 = 1772861) B1772861
theorem B1771745 : Blo 1180407 1771745 := bstep (se 2 (by rfl) ⟨664404, by rfl⟩ : syracuseStep 1771745 = 1328809) B1328809
theorem B21547235 : Blo 1180407 21547235 := bstep (se 1 (by rfl) ⟨16160426, by rfl⟩ : syracuseStep 21547235 = 32320853) B32320853
theorem B1181923 : Blo 1180407 1181923 := bstep (se 1 (by rfl) ⟨886442, by rfl⟩ : syracuseStep 1181923 = 1772885) B1772885
theorem B1771763 : Blo 1180407 1771763 := bstep (se 1 (by rfl) ⟨1328822, by rfl⟩ : syracuseStep 1771763 = 2657645) B2657645
theorem B1796339 : Blo 1180407 1796339 := bstep (se 1 (by rfl) ⟨1347254, by rfl⟩ : syracuseStep 1796339 = 2694509) B2694509
theorem B1181939 : Blo 1180407 1181939 := bstep (se 1 (by rfl) ⟨886454, by rfl⟩ : syracuseStep 1181939 = 1772909) B1772909
theorem B1181955 : Blo 1180407 1181955 := bstep (se 1 (by rfl) ⟨886466, by rfl⟩ : syracuseStep 1181955 = 1772933) B1772933
theorem B2656529 : Blo 1180407 2656529 := bstep (se 2 (by rfl) ⟨996198, by rfl⟩ : syracuseStep 2656529 = 1992397) B1992397
theorem B1771793 : Blo 1180407 1771793 := bstep (se 2 (by rfl) ⟨664422, by rfl⟩ : syracuseStep 1771793 = 1328845) B1328845
theorem B1181971 : Blo 1180407 1181971 := bstep (se 1 (by rfl) ⟨886478, by rfl⟩ : syracuseStep 1181971 = 1772957) B1772957
theorem B2656547 : Blo 1180407 2656547 := bstep (se 1 (by rfl) ⟨1992410, by rfl⟩ : syracuseStep 2656547 = 3984821) B3984821
theorem B1771811 : Blo 1180407 1771811 := bstep (se 1 (by rfl) ⟨1328858, by rfl⟩ : syracuseStep 1771811 = 2657717) B2657717
theorem B1181987 : Blo 1180407 1181987 := bstep (se 1 (by rfl) ⟨886490, by rfl⟩ : syracuseStep 1181987 = 1772981) B1772981
theorem B6064433 : Blo 1180407 6064433 := bstep (se 2 (by rfl) ⟨2274162, by rfl⟩ : syracuseStep 6064433 = 4548325) B4548325
theorem B1182003 : Blo 1180407 1182003 := bstep (se 1 (by rfl) ⟨886502, by rfl⟩ : syracuseStep 1182003 = 1773005) B1773005
theorem B1993025 : Blo 1180407 1993025 := bstep (se 2 (by rfl) ⟨747384, by rfl⟩ : syracuseStep 1993025 = 1494769) B1494769
theorem B1771841 : Blo 1180407 1771841 := bstep (se 2 (by rfl) ⟨664440, by rfl⟩ : syracuseStep 1771841 = 1328881) B1328881
theorem B1329475 : Blo 1180407 1329475 := bstep (se 1 (by rfl) ⟨997106, by rfl⟩ : syracuseStep 1329475 = 1994213) B1994213
theorem B1182019 : Blo 1180407 1182019 := bstep (se 1 (by rfl) ⟨886514, by rfl⟩ : syracuseStep 1182019 = 1773029) B1773029
theorem B1771859 : Blo 1180407 1771859 := bstep (se 1 (by rfl) ⟨1328894, by rfl⟩ : syracuseStep 1771859 = 2657789) B2657789
theorem B1182035 : Blo 1180407 1182035 := bstep (se 1 (by rfl) ⟨886526, by rfl⟩ : syracuseStep 1182035 = 1773053) B1773053
theorem B5048675 : Blo 1180407 5048675 := bstep (se 1 (by rfl) ⟨3786506, by rfl⟩ : syracuseStep 5048675 = 7573013) B7573013
theorem B1182051 : Blo 1180407 1182051 := bstep (se 1 (by rfl) ⟨886538, by rfl⟩ : syracuseStep 1182051 = 1773077) B1773077
theorem B1771889 : Blo 1180407 1771889 := bstep (se 2 (by rfl) ⟨664458, by rfl⟩ : syracuseStep 1771889 = 1328917) B1328917
theorem B1182067 : Blo 1180407 1182067 := bstep (se 1 (by rfl) ⟨886550, by rfl⟩ : syracuseStep 1182067 = 1773101) B1773101
theorem B1771907 : Blo 1180407 1771907 := bstep (se 1 (by rfl) ⟨1328930, by rfl⟩ : syracuseStep 1771907 = 2657861) B2657861
theorem B1182083 : Blo 1180407 1182083 := bstep (se 1 (by rfl) ⟨886562, by rfl⟩ : syracuseStep 1182083 = 1773125) B1773125
theorem B40905101 : Blo 1180407 40905101 := bstep (se 3 (by rfl) ⟨7669706, by rfl⟩ : syracuseStep 40905101 = 15339413) B15339413
theorem B1182099 : Blo 1180407 1182099 := bstep (se 1 (by rfl) ⟨886574, by rfl⟩ : syracuseStep 1182099 = 1773149) B1773149
theorem B1771937 : Blo 1180407 1771937 := bstep (se 2 (by rfl) ⟨664476, by rfl⟩ : syracuseStep 1771937 = 1328953) B1328953
theorem B1182115 : Blo 1180407 1182115 := bstep (se 1 (by rfl) ⟨886586, by rfl⟩ : syracuseStep 1182115 = 1773173) B1773173
theorem B1771955 : Blo 1180407 1771955 := bstep (se 1 (by rfl) ⟨1328966, by rfl⟩ : syracuseStep 1771955 = 2657933) B2657933
theorem B1182131 : Blo 1180407 1182131 := bstep (se 1 (by rfl) ⟨886598, by rfl⟩ : syracuseStep 1182131 = 1773197) B1773197
theorem B1993153 : Blo 1180407 1993153 := bstep (se 2 (by rfl) ⟨747432, by rfl⟩ : syracuseStep 1993153 = 1494865) B1494865
theorem B1182147 : Blo 1180407 1182147 := bstep (se 1 (by rfl) ⟨886610, by rfl⟩ : syracuseStep 1182147 = 1773221) B1773221
theorem B1771985 : Blo 1180407 1771985 := bstep (se 2 (by rfl) ⟨664494, by rfl⟩ : syracuseStep 1771985 = 1328989) B1328989
theorem B1329619 : Blo 1180407 1329619 := bstep (se 1 (by rfl) ⟨997214, by rfl⟩ : syracuseStep 1329619 = 1994429) B1994429
theorem B1182163 : Blo 1180407 1182163 := bstep (se 1 (by rfl) ⟨886622, by rfl⟩ : syracuseStep 1182163 = 1773245) B1773245
theorem B1993187 : Blo 1180407 1993187 := bstep (se 1 (by rfl) ⟨1494890, by rfl⟩ : syracuseStep 1993187 = 2989781) B2989781
theorem B1772003 : Blo 1180407 1772003 := bstep (se 1 (by rfl) ⟨1329002, by rfl⟩ : syracuseStep 1772003 = 2658005) B2658005
theorem B1182179 : Blo 1180407 1182179 := bstep (se 1 (by rfl) ⟨886634, by rfl⟩ : syracuseStep 1182179 = 1773269) B1773269
theorem B1182195 : Blo 1180407 1182195 := bstep (se 1 (by rfl) ⟨886646, by rfl⟩ : syracuseStep 1182195 = 1773293) B1773293
theorem B1772033 : Blo 1180407 1772033 := bstep (se 2 (by rfl) ⟨664512, by rfl⟩ : syracuseStep 1772033 = 1329025) B1329025
theorem B3590659 : Blo 1180407 3590659 := bstep (se 1 (by rfl) ⟨2692994, by rfl⟩ : syracuseStep 3590659 = 5385989) B5385989
theorem B1182211 : Blo 1180407 1182211 := bstep (se 1 (by rfl) ⟨886658, by rfl⟩ : syracuseStep 1182211 = 1773317) B1773317
theorem B1772051 : Blo 1180407 1772051 := bstep (se 1 (by rfl) ⟨1329038, by rfl⟩ : syracuseStep 1772051 = 2658077) B2658077
theorem B1182227 : Blo 1180407 1182227 := bstep (se 1 (by rfl) ⟨886670, by rfl⟩ : syracuseStep 1182227 = 1773341) B1773341
theorem B6474275 : Blo 1180407 6474275 := bstep (se 1 (by rfl) ⟨4855706, by rfl⟩ : syracuseStep 6474275 = 9711413) B9711413
theorem B1182243 : Blo 1180407 1182243 := bstep (se 1 (by rfl) ⟨886682, by rfl⟩ : syracuseStep 1182243 = 1773365) B1773365
theorem B2656817 : Blo 1180407 2656817 := bstep (se 2 (by rfl) ⟨996306, by rfl⟩ : syracuseStep 2656817 = 1992613) B1992613
theorem B1772081 : Blo 1180407 1772081 := bstep (se 2 (by rfl) ⟨664530, by rfl⟩ : syracuseStep 1772081 = 1329061) B1329061
theorem B1182259 : Blo 1180407 1182259 := bstep (se 1 (by rfl) ⟨886694, by rfl⟩ : syracuseStep 1182259 = 1773389) B1773389
theorem B2656835 : Blo 1180407 2656835 := bstep (se 1 (by rfl) ⟨1992626, by rfl⟩ : syracuseStep 2656835 = 3985253) B3985253
theorem B1772099 : Blo 1180407 1772099 := bstep (se 1 (by rfl) ⟨1329074, by rfl⟩ : syracuseStep 1772099 = 2658149) B2658149
theorem B1182275 : Blo 1180407 1182275 := bstep (se 1 (by rfl) ⟨886706, by rfl⟩ : syracuseStep 1182275 = 1773413) B1773413
theorem B1182291 : Blo 1180407 1182291 := bstep (se 1 (by rfl) ⟨886718, by rfl⟩ : syracuseStep 1182291 = 1773437) B1773437
theorem B1772129 : Blo 1180407 1772129 := bstep (se 2 (by rfl) ⟨664548, by rfl⟩ : syracuseStep 1772129 = 1329097) B1329097
theorem B1993315 : Blo 1180407 1993315 := bstep (se 1 (by rfl) ⟨1494986, by rfl⟩ : syracuseStep 1993315 = 2989973) B2989973
theorem B1329763 : Blo 1180407 1329763 := bstep (se 1 (by rfl) ⟨997322, by rfl⟩ : syracuseStep 1329763 = 1994645) B1994645
theorem B1182307 : Blo 1180407 1182307 := bstep (se 1 (by rfl) ⟨886730, by rfl⟩ : syracuseStep 1182307 = 1773461) B1773461
theorem B6728305 : Blo 1180407 6728305 := bstep (se 2 (by rfl) ⟨2523114, by rfl⟩ : syracuseStep 6728305 = 5046229) B5046229
theorem B1772147 : Blo 1180407 1772147 := bstep (se 1 (by rfl) ⟨1329110, by rfl⟩ : syracuseStep 1772147 = 2658221) B2658221
theorem B1182323 : Blo 1180407 1182323 := bstep (se 1 (by rfl) ⟨886742, by rfl⟩ : syracuseStep 1182323 = 1773485) B1773485
theorem B1182339 : Blo 1180407 1182339 := bstep (se 1 (by rfl) ⟨886754, by rfl⟩ : syracuseStep 1182339 = 1773509) B1773509
theorem B1772177 : Blo 1180407 1772177 := bstep (se 2 (by rfl) ⟨664566, by rfl⟩ : syracuseStep 1772177 = 1329133) B1329133
theorem B1182355 : Blo 1180407 1182355 := bstep (se 1 (by rfl) ⟨886766, by rfl⟩ : syracuseStep 1182355 = 1773533) B1773533
theorem B1772195 : Blo 1180407 1772195 := bstep (se 1 (by rfl) ⟨1329146, by rfl⟩ : syracuseStep 1772195 = 2658293) B2658293
theorem B1182371 : Blo 1180407 1182371 := bstep (se 1 (by rfl) ⟨886778, by rfl⟩ : syracuseStep 1182371 = 1773557) B1773557
theorem B1182387 : Blo 1180407 1182387 := bstep (se 1 (by rfl) ⟨886790, by rfl⟩ : syracuseStep 1182387 = 1773581) B1773581
theorem B1772225 : Blo 1180407 1772225 := bstep (se 2 (by rfl) ⟨664584, by rfl⟩ : syracuseStep 1772225 = 1329169) B1329169
theorem B1182403 : Blo 1180407 1182403 := bstep (se 1 (by rfl) ⟨886802, by rfl⟩ : syracuseStep 1182403 = 1773605) B1773605
theorem B1772243 : Blo 1180407 1772243 := bstep (se 1 (by rfl) ⟨1329182, by rfl⟩ : syracuseStep 1772243 = 2658365) B2658365
theorem B10775267 : Blo 1180407 10775267 := bstep (se 1 (by rfl) ⟨8081450, by rfl⟩ : syracuseStep 10775267 = 16162901) B16162901
theorem B1993457 : Blo 1180407 1993457 := bstep (se 2 (by rfl) ⟨747546, by rfl⟩ : syracuseStep 1993457 = 1495093) B1495093
theorem B1772273 : Blo 1180407 1772273 := bstep (se 2 (by rfl) ⟨664602, by rfl⟩ : syracuseStep 1772273 = 1329205) B1329205
theorem B1329907 : Blo 1180407 1329907 := bstep (se 1 (by rfl) ⟨997430, by rfl⟩ : syracuseStep 1329907 = 1994861) B1994861
theorem B1772291 : Blo 1180407 1772291 := bstep (se 1 (by rfl) ⟨1329218, by rfl⟩ : syracuseStep 1772291 = 2658437) B2658437
theorem B1772321 : Blo 1180407 1772321 := bstep (se 2 (by rfl) ⟨664620, by rfl⟩ : syracuseStep 1772321 = 1329241) B1329241
theorem B1796899 : Blo 1180407 1796899 := bstep (se 1 (by rfl) ⟨1347674, by rfl⟩ : syracuseStep 1796899 = 2695349) B2695349
theorem B3984173 : Blo 1180407 3984173 := bstep (se 3 (by rfl) ⟨747032, by rfl⟩ : syracuseStep 3984173 = 1494065) B1494065
theorem B1772339 : Blo 1180407 1772339 := bstep (se 1 (by rfl) ⟨1329254, by rfl⟩ : syracuseStep 1772339 = 2658509) B2658509
theorem B2657105 : Blo 1180407 2657105 := bstep (se 2 (by rfl) ⟨996414, by rfl⟩ : syracuseStep 2657105 = 1992829) B1992829
theorem B1772369 : Blo 1180407 1772369 := bstep (se 2 (by rfl) ⟨664638, by rfl⟩ : syracuseStep 1772369 = 1329277) B1329277
theorem B3984227 : Blo 1180407 3984227 := bstep (se 1 (by rfl) ⟨2988170, by rfl⟩ : syracuseStep 3984227 = 5976341) B5976341
theorem B2657123 : Blo 1180407 2657123 := bstep (se 1 (by rfl) ⟨1992842, by rfl⟩ : syracuseStep 2657123 = 3985685) B3985685
theorem B1772387 : Blo 1180407 1772387 := bstep (se 1 (by rfl) ⟨1329290, by rfl⟩ : syracuseStep 1772387 = 2658581) B2658581
theorem B1993585 : Blo 1180407 1993585 := bstep (se 2 (by rfl) ⟨747594, by rfl⟩ : syracuseStep 1993585 = 1495189) B1495189
theorem B1772417 : Blo 1180407 1772417 := bstep (se 2 (by rfl) ⟨664656, by rfl⟩ : syracuseStep 1772417 = 1329313) B1329313
theorem B1330051 : Blo 1180407 1330051 := bstep (se 1 (by rfl) ⟨997538, by rfl⟩ : syracuseStep 1330051 = 1995077) B1995077
theorem B1993619 : Blo 1180407 1993619 := bstep (se 1 (by rfl) ⟨1495214, by rfl⟩ : syracuseStep 1993619 = 2990429) B2990429
theorem B1772435 : Blo 1180407 1772435 := bstep (se 1 (by rfl) ⟨1329326, by rfl⟩ : syracuseStep 1772435 = 2658653) B2658653
theorem B1420195 : Blo 1180407 1420195 := bstep (se 1 (by rfl) ⟨1065146, by rfl⟩ : syracuseStep 1420195 = 2130293) B2130293
theorem B1772465 : Blo 1180407 1772465 := bstep (se 2 (by rfl) ⟨664674, by rfl⟩ : syracuseStep 1772465 = 1329349) B1329349
theorem B3787697 : Blo 1180407 3787697 := bstep (se 2 (by rfl) ⟨1420386, by rfl⟩ : syracuseStep 3787697 = 2840773) B2840773
theorem B14560181 : Blo 1180407 14560181 := bstep (se 5 (by rfl) ⟨682508, by rfl⟩ : syracuseStep 14560181 = 1365017) B1365017
theorem B1772483 : Blo 1180407 1772483 := bstep (se 1 (by rfl) ⟨1329362, by rfl⟩ : syracuseStep 1772483 = 2658725) B2658725
theorem B30272453 : Blo 1180407 30272453 := bstep (se 4 (by rfl) ⟨2838042, by rfl⟩ : syracuseStep 30272453 = 5676085) B5676085
theorem B1772513 : Blo 1180407 1772513 := bstep (se 2 (by rfl) ⟨664692, by rfl⟩ : syracuseStep 1772513 = 1329385) B1329385
theorem B1772531 : Blo 1180407 1772531 := bstep (se 1 (by rfl) ⟨1329398, by rfl⟩ : syracuseStep 1772531 = 2658797) B2658797
theorem B1772561 : Blo 1180407 1772561 := bstep (se 2 (by rfl) ⟨664710, by rfl⟩ : syracuseStep 1772561 = 1329421) B1329421
theorem B1993747 : Blo 1180407 1993747 := bstep (se 1 (by rfl) ⟨1495310, by rfl⟩ : syracuseStep 1993747 = 2990621) B2990621
theorem B1330195 : Blo 1180407 1330195 := bstep (se 1 (by rfl) ⟨997646, by rfl⟩ : syracuseStep 1330195 = 1995293) B1995293
theorem B7179299 : Blo 1180407 7179299 := bstep (se 1 (by rfl) ⟨5384474, by rfl⟩ : syracuseStep 7179299 = 10768949) B10768949
theorem B1772579 : Blo 1180407 1772579 := bstep (se 1 (by rfl) ⟨1329434, by rfl⟩ : syracuseStep 1772579 = 2658869) B2658869
theorem B1772609 : Blo 1180407 1772609 := bstep (se 2 (by rfl) ⟨664728, by rfl⟩ : syracuseStep 1772609 = 1329457) B1329457
theorem B1772627 : Blo 1180407 1772627 := bstep (se 1 (by rfl) ⟨1329470, by rfl⟩ : syracuseStep 1772627 = 2658941) B2658941
theorem B3984497 : Blo 1180407 3984497 := bstep (se 2 (by rfl) ⟨1494186, by rfl⟩ : syracuseStep 3984497 = 2988373) B2988373
theorem B10087537 : Blo 1180407 10087537 := bstep (se 2 (by rfl) ⟨3782826, by rfl⟩ : syracuseStep 10087537 = 7565653) B7565653
theorem B8629361 : Blo 1180407 8629361 := bstep (se 2 (by rfl) ⟨3236010, by rfl⟩ : syracuseStep 8629361 = 6472021) B6472021
theorem B2657393 : Blo 1180407 2657393 := bstep (se 2 (by rfl) ⟨996522, by rfl⟩ : syracuseStep 2657393 = 1993045) B1993045
theorem B1772657 : Blo 1180407 1772657 := bstep (se 2 (by rfl) ⟨664746, by rfl⟩ : syracuseStep 1772657 = 1329493) B1329493
theorem B2657411 : Blo 1180407 2657411 := bstep (se 1 (by rfl) ⟨1993058, by rfl⟩ : syracuseStep 2657411 = 3986117) B3986117
theorem B1772675 : Blo 1180407 1772675 := bstep (se 1 (by rfl) ⟨1329506, by rfl⟩ : syracuseStep 1772675 = 2659013) B2659013
theorem B1993889 : Blo 1180407 1993889 := bstep (se 2 (by rfl) ⟨747708, by rfl⟩ : syracuseStep 1993889 = 1495417) B1495417
theorem B1772705 : Blo 1180407 1772705 := bstep (se 2 (by rfl) ⟨664764, by rfl⟩ : syracuseStep 1772705 = 1329529) B1329529
theorem B1772723 : Blo 1180407 1772723 := bstep (se 1 (by rfl) ⟨1329542, by rfl⟩ : syracuseStep 1772723 = 2659085) B2659085
theorem B1772753 : Blo 1180407 1772753 := bstep (se 2 (by rfl) ⟨664782, by rfl⟩ : syracuseStep 1772753 = 1329565) B1329565
theorem B1494227 : Blo 1180407 1494227 := bstep (se 1 (by rfl) ⟨1120670, by rfl⟩ : syracuseStep 1494227 = 2241341) B2241341
theorem B1772771 : Blo 1180407 1772771 := bstep (se 1 (by rfl) ⟨1329578, by rfl⟩ : syracuseStep 1772771 = 2659157) B2659157
theorem B1772801 : Blo 1180407 1772801 := bstep (se 2 (by rfl) ⟨664800, by rfl⟩ : syracuseStep 1772801 = 1329601) B1329601
theorem B1772819 : Blo 1180407 1772819 := bstep (se 1 (by rfl) ⟨1329614, by rfl⟩ : syracuseStep 1772819 = 2659229) B2659229
theorem B1994017 : Blo 1180407 1994017 := bstep (se 2 (by rfl) ⟨747756, by rfl⟩ : syracuseStep 1994017 = 1495513) B1495513
theorem B1772849 : Blo 1180407 1772849 := bstep (se 2 (by rfl) ⟨664818, by rfl⟩ : syracuseStep 1772849 = 1329637) B1329637
theorem B4549937 : Blo 1180407 4549937 := bstep (se 2 (by rfl) ⟨1706226, by rfl⟩ : syracuseStep 4549937 = 3412453) B3412453
theorem B1994051 : Blo 1180407 1994051 := bstep (se 1 (by rfl) ⟨1495538, by rfl⟩ : syracuseStep 1994051 = 2991077) B2991077
theorem B1772867 : Blo 1180407 1772867 := bstep (se 1 (by rfl) ⟨1329650, by rfl⟩ : syracuseStep 1772867 = 2659301) B2659301
theorem B4484429 : Blo 1180407 4484429 := bstep (se 3 (by rfl) ⟨840830, by rfl⟩ : syracuseStep 4484429 = 1681661) B1681661
theorem B1772897 : Blo 1180407 1772897 := bstep (se 2 (by rfl) ⟨664836, by rfl⟩ : syracuseStep 1772897 = 1329673) B1329673
theorem B1772915 : Blo 1180407 1772915 := bstep (se 1 (by rfl) ⟨1329686, by rfl⟩ : syracuseStep 1772915 = 2659373) B2659373
theorem B2657681 : Blo 1180407 2657681 := bstep (se 2 (by rfl) ⟨996630, by rfl⟩ : syracuseStep 2657681 = 1993261) B1993261
theorem B1772945 : Blo 1180407 1772945 := bstep (se 2 (by rfl) ⟨664854, by rfl⟩ : syracuseStep 1772945 = 1329709) B1329709
theorem B2657699 : Blo 1180407 2657699 := bstep (se 1 (by rfl) ⟨1993274, by rfl⟩ : syracuseStep 2657699 = 3986549) B3986549
theorem B1682851 : Blo 1180407 1682851 := bstep (se 1 (by rfl) ⟨1262138, by rfl⟩ : syracuseStep 1682851 = 2524277) B2524277
theorem B1772963 : Blo 1180407 1772963 := bstep (se 1 (by rfl) ⟨1329722, by rfl⟩ : syracuseStep 1772963 = 2659445) B2659445
theorem B1772993 : Blo 1180407 1772993 := bstep (se 2 (by rfl) ⟨664872, by rfl⟩ : syracuseStep 1772993 = 1329745) B1329745
theorem B1994179 : Blo 1180407 1994179 := bstep (se 1 (by rfl) ⟨1495634, by rfl⟩ : syracuseStep 1994179 = 2991269) B2991269
theorem B1773011 : Blo 1180407 1773011 := bstep (se 1 (by rfl) ⟨1329758, by rfl⟩ : syracuseStep 1773011 = 2659517) B2659517
theorem B2837987 : Blo 1180407 2837987 := bstep (se 1 (by rfl) ⟨2128490, by rfl⟩ : syracuseStep 2837987 = 4256981) B4256981
theorem B3362285 : Blo 1180407 3362285 := bstep (se 3 (by rfl) ⟨630428, by rfl⟩ : syracuseStep 3362285 = 1260857) B1260857
theorem B1773041 : Blo 1180407 1773041 := bstep (se 2 (by rfl) ⟨664890, by rfl⟩ : syracuseStep 1773041 = 1329781) B1329781
theorem B1773059 : Blo 1180407 1773059 := bstep (se 1 (by rfl) ⟨1329794, by rfl⟩ : syracuseStep 1773059 = 2659589) B2659589
theorem B1773089 : Blo 1180407 1773089 := bstep (se 2 (by rfl) ⟨664908, by rfl⟩ : syracuseStep 1773089 = 1329817) B1329817
theorem B5983793 : Blo 1180407 5983793 := bstep (se 2 (by rfl) ⟨2243922, by rfl⟩ : syracuseStep 5983793 = 4487845) B4487845
theorem B1773107 : Blo 1180407 1773107 := bstep (se 1 (by rfl) ⟨1329830, by rfl⟩ : syracuseStep 1773107 = 2659661) B2659661
theorem B1994321 : Blo 1180407 1994321 := bstep (se 2 (by rfl) ⟨747870, by rfl⟩ : syracuseStep 1994321 = 1495741) B1495741
theorem B1773137 : Blo 1180407 1773137 := bstep (se 2 (by rfl) ⟨664926, by rfl⟩ : syracuseStep 1773137 = 1329853) B1329853
theorem B1773155 : Blo 1180407 1773155 := bstep (se 1 (by rfl) ⟨1329866, by rfl⟩ : syracuseStep 1773155 = 2659733) B2659733
theorem B1773185 : Blo 1180407 1773185 := bstep (se 2 (by rfl) ⟨664944, by rfl⟩ : syracuseStep 1773185 = 1329889) B1329889
theorem B3985037 : Blo 1180407 3985037 := bstep (se 3 (by rfl) ⟨747194, by rfl⟩ : syracuseStep 3985037 = 1494389) B1494389
theorem B1773203 : Blo 1180407 1773203 := bstep (se 1 (by rfl) ⟨1329902, by rfl⟩ : syracuseStep 1773203 = 2659805) B2659805
theorem B3362467 : Blo 1180407 3362467 := bstep (se 1 (by rfl) ⟨2521850, by rfl⟩ : syracuseStep 3362467 = 5043701) B5043701
theorem B3239597 : Blo 1180407 3239597 := bstep (se 3 (by rfl) ⟨607424, by rfl⟩ : syracuseStep 3239597 = 1214849) B1214849
theorem B2657969 : Blo 1180407 2657969 := bstep (se 2 (by rfl) ⟨996738, by rfl⟩ : syracuseStep 2657969 = 1993477) B1993477
theorem B1773233 : Blo 1180407 1773233 := bstep (se 2 (by rfl) ⟨664962, by rfl⟩ : syracuseStep 1773233 = 1329925) B1329925
theorem B3985091 : Blo 1180407 3985091 := bstep (se 1 (by rfl) ⟨2988818, by rfl⟩ : syracuseStep 3985091 = 5977637) B5977637
theorem B2657987 : Blo 1180407 2657987 := bstep (se 1 (by rfl) ⟨1993490, by rfl⟩ : syracuseStep 2657987 = 3986981) B3986981
theorem B1773251 : Blo 1180407 1773251 := bstep (se 1 (by rfl) ⟨1329938, by rfl⟩ : syracuseStep 1773251 = 2659877) B2659877
theorem B1994449 : Blo 1180407 1994449 := bstep (se 2 (by rfl) ⟨747918, by rfl⟩ : syracuseStep 1994449 = 1495837) B1495837
theorem B1773281 : Blo 1180407 1773281 := bstep (se 2 (by rfl) ⟨664980, by rfl⟩ : syracuseStep 1773281 = 1329961) B1329961
theorem B1994483 : Blo 1180407 1994483 := bstep (se 1 (by rfl) ⟨1495862, by rfl⟩ : syracuseStep 1994483 = 2991725) B2991725
theorem B1773299 : Blo 1180407 1773299 := bstep (se 1 (by rfl) ⟨1329974, by rfl⟩ : syracuseStep 1773299 = 2659949) B2659949
theorem B1773329 : Blo 1180407 1773329 := bstep (se 2 (by rfl) ⟨664998, by rfl⟩ : syracuseStep 1773329 = 1329997) B1329997
theorem B1773347 : Blo 1180407 1773347 := bstep (se 1 (by rfl) ⟨1330010, by rfl⟩ : syracuseStep 1773347 = 2660021) B2660021
theorem B3362627 : Blo 1180407 3362627 := bstep (se 1 (by rfl) ⟨2521970, by rfl⟩ : syracuseStep 3362627 = 5043941) B5043941
theorem B1773377 : Blo 1180407 1773377 := bstep (se 2 (by rfl) ⟨665016, by rfl⟩ : syracuseStep 1773377 = 1330033) B1330033
theorem B1773395 : Blo 1180407 1773395 := bstep (se 1 (by rfl) ⟨1330046, by rfl⟩ : syracuseStep 1773395 = 2660093) B2660093
theorem B3592045 : Blo 1180407 3592045 := bstep (se 3 (by rfl) ⟨673508, by rfl⟩ : syracuseStep 3592045 = 1347017) B1347017
theorem B15126385 : Blo 1180407 15126385 := bstep (se 2 (by rfl) ⟨5672394, by rfl⟩ : syracuseStep 15126385 = 11344789) B11344789
theorem B1773425 : Blo 1180407 1773425 := bstep (se 2 (by rfl) ⟨665034, by rfl⟩ : syracuseStep 1773425 = 1330069) B1330069
theorem B1994611 : Blo 1180407 1994611 := bstep (se 1 (by rfl) ⟨1495958, by rfl⟩ : syracuseStep 1994611 = 2991917) B2991917
theorem B1773443 : Blo 1180407 1773443 := bstep (se 1 (by rfl) ⟨1330082, by rfl⟩ : syracuseStep 1773443 = 2660165) B2660165
theorem B4042637 : Blo 1180407 4042637 := bstep (se 3 (by rfl) ⟨757994, by rfl⟩ : syracuseStep 4042637 = 1515989) B1515989
theorem B15150989 : Blo 1180407 15150989 := bstep (se 3 (by rfl) ⟨2840810, by rfl⟩ : syracuseStep 15150989 = 5681621) B5681621
theorem B1494931 : Blo 1180407 1494931 := bstep (se 1 (by rfl) ⟨1121198, by rfl⟩ : syracuseStep 1494931 = 2242397) B2242397
theorem B1773473 : Blo 1180407 1773473 := bstep (se 2 (by rfl) ⟨665052, by rfl⟩ : syracuseStep 1773473 = 1330105) B1330105
theorem B1773491 : Blo 1180407 1773491 := bstep (se 1 (by rfl) ⟨1330118, by rfl⟩ : syracuseStep 1773491 = 2660237) B2660237
theorem B7573445 : Blo 1180407 7573445 := bstep (se 4 (by rfl) ⟨710010, by rfl⟩ : syracuseStep 7573445 = 1420021) B1420021
theorem B16175045 : Blo 1180407 16175045 := bstep (se 4 (by rfl) ⟨1516410, by rfl⟩ : syracuseStep 16175045 = 3032821) B3032821
theorem B3985361 : Blo 1180407 3985361 := bstep (se 2 (by rfl) ⟨1494510, by rfl⟩ : syracuseStep 3985361 = 2989021) B2989021
theorem B2658257 : Blo 1180407 2658257 := bstep (se 2 (by rfl) ⟨996846, by rfl⟩ : syracuseStep 2658257 = 1993693) B1993693
theorem B1773521 : Blo 1180407 1773521 := bstep (se 2 (by rfl) ⟨665070, by rfl⟩ : syracuseStep 1773521 = 1330141) B1330141
theorem B2658275 : Blo 1180407 2658275 := bstep (se 1 (by rfl) ⟨1993706, by rfl⟩ : syracuseStep 2658275 = 3987413) B3987413
theorem B1773539 : Blo 1180407 1773539 := bstep (se 1 (by rfl) ⟨1330154, by rfl⟩ : syracuseStep 1773539 = 2660309) B2660309
theorem B1495027 : Blo 1180407 1495027 := bstep (se 1 (by rfl) ⟨1121270, by rfl⟩ : syracuseStep 1495027 = 2242541) B2242541
theorem B1994753 : Blo 1180407 1994753 := bstep (se 2 (by rfl) ⟨748032, by rfl⟩ : syracuseStep 1994753 = 1496065) B1496065
theorem B1773569 : Blo 1180407 1773569 := bstep (se 2 (by rfl) ⟨665088, by rfl⟩ : syracuseStep 1773569 = 1330177) B1330177
theorem B1773587 : Blo 1180407 1773587 := bstep (se 1 (by rfl) ⟨1330190, by rfl⟩ : syracuseStep 1773587 = 2660381) B2660381
theorem B6729763 : Blo 1180407 6729763 := bstep (se 1 (by rfl) ⟨5047322, by rfl⟩ : syracuseStep 6729763 = 10094645) B10094645
theorem B8966213 : Blo 1180407 8966213 := bstep (se 4 (by rfl) ⟨840582, by rfl⟩ : syracuseStep 8966213 = 1681165) B1681165
theorem B4485233 : Blo 1180407 4485233 := bstep (se 2 (by rfl) ⟨1681962, by rfl⟩ : syracuseStep 4485233 = 3363925) B3363925
theorem B1994881 : Blo 1180407 1994881 := bstep (se 2 (by rfl) ⟨748080, by rfl⟩ : syracuseStep 1994881 = 1496161) B1496161
theorem B1994915 : Blo 1180407 1994915 := bstep (se 1 (by rfl) ⟨1496186, by rfl⟩ : syracuseStep 1994915 = 2992373) B2992373
theorem B2658545 : Blo 1180407 2658545 := bstep (se 2 (by rfl) ⟨996954, by rfl⟩ : syracuseStep 2658545 = 1993909) B1993909
theorem B2658563 : Blo 1180407 2658563 := bstep (se 1 (by rfl) ⟨1993922, by rfl⟩ : syracuseStep 2658563 = 3987845) B3987845
theorem B1995043 : Blo 1180407 1995043 := bstep (se 1 (by rfl) ⟨1496282, by rfl⟩ : syracuseStep 1995043 = 2992565) B2992565
theorem B2838833 : Blo 1180407 2838833 := bstep (se 2 (by rfl) ⟨1064562, by rfl⟩ : syracuseStep 2838833 = 2129125) B2129125
theorem B1995185 : Blo 1180407 1995185 := bstep (se 2 (by rfl) ⟨748194, by rfl⟩ : syracuseStep 1995185 = 1496389) B1496389
theorem B1495523 : Blo 1180407 1495523 := bstep (se 1 (by rfl) ⟨1121642, by rfl⟩ : syracuseStep 1495523 = 2243285) B2243285
theorem B3985901 : Blo 1180407 3985901 := bstep (se 3 (by rfl) ⟨747356, by rfl⟩ : syracuseStep 3985901 = 1494713) B1494713
theorem B6386161 : Blo 1180407 6386161 := bstep (se 2 (by rfl) ⟨2394810, by rfl⟩ : syracuseStep 6386161 = 4789621) B4789621
theorem B2839043 : Blo 1180407 2839043 := bstep (se 1 (by rfl) ⟨2129282, by rfl⟩ : syracuseStep 2839043 = 4258565) B4258565
theorem B2658833 : Blo 1180407 2658833 := bstep (se 2 (by rfl) ⟨997062, by rfl⟩ : syracuseStep 2658833 = 1994125) B1994125
theorem B3985955 : Blo 1180407 3985955 := bstep (se 1 (by rfl) ⟨2989466, by rfl⟩ : syracuseStep 3985955 = 5978933) B5978933
theorem B2658851 : Blo 1180407 2658851 := bstep (se 1 (by rfl) ⟨1994138, by rfl⟩ : syracuseStep 2658851 = 3988277) B3988277
theorem B6730289 : Blo 1180407 6730289 := bstep (se 2 (by rfl) ⟨2523858, by rfl⟩ : syracuseStep 6730289 = 5047717) B5047717
theorem B1995313 : Blo 1180407 1995313 := bstep (se 2 (by rfl) ⟨748242, by rfl⟩ : syracuseStep 1995313 = 1496485) B1496485
theorem B10777157 : Blo 1180407 10777157 := bstep (se 4 (by rfl) ⟨1010358, by rfl⟩ : syracuseStep 10777157 = 2020717) B2020717
theorem B8974961 : Blo 1180407 8974961 := bstep (se 2 (by rfl) ⟨3365610, by rfl⟩ : syracuseStep 8974961 = 6731221) B6731221
theorem B3191491 : Blo 1180407 3191491 := bstep (se 1 (by rfl) ⟨2393618, by rfl⟩ : syracuseStep 3191491 = 4787237) B4787237
theorem B2241265 : Blo 1180407 2241265 := bstep (se 2 (by rfl) ⟨840474, by rfl⟩ : syracuseStep 2241265 = 1680949) B1680949
theorem B4485901 : Blo 1180407 4485901 := bstep (se 3 (by rfl) ⟨841106, by rfl⟩ : syracuseStep 4485901 = 1682213) B1682213
theorem B3986225 : Blo 1180407 3986225 := bstep (se 2 (by rfl) ⟨1494834, by rfl⟩ : syracuseStep 3986225 = 2989669) B2989669
theorem B2659121 : Blo 1180407 2659121 := bstep (se 2 (by rfl) ⟨997170, by rfl⟩ : syracuseStep 2659121 = 1994341) B1994341
theorem B2659139 : Blo 1180407 2659139 := bstep (se 1 (by rfl) ⟨1994354, by rfl⟩ : syracuseStep 2659139 = 3988709) B3988709
theorem B3191665 : Blo 1180407 3191665 := bstep (se 2 (by rfl) ⟨1196874, by rfl⟩ : syracuseStep 3191665 = 2393749) B2393749
theorem B3363697 : Blo 1180407 3363697 := bstep (se 2 (by rfl) ⟨1261386, by rfl⟩ : syracuseStep 3363697 = 2522773) B2522773
theorem B2241425 : Blo 1180407 2241425 := bstep (se 2 (by rfl) ⟨840534, by rfl⟩ : syracuseStep 2241425 = 1681069) B1681069
theorem B5985251 : Blo 1180407 5985251 := bstep (se 1 (by rfl) ⟨4488938, by rfl⟩ : syracuseStep 5985251 = 8977877) B8977877
theorem B3413009 : Blo 1180407 3413009 := bstep (se 2 (by rfl) ⟨1279878, by rfl⟩ : syracuseStep 3413009 = 2559757) B2559757
theorem B13464629 : Blo 1180407 13464629 := bstep (se 5 (by rfl) ⟨631154, by rfl⟩ : syracuseStep 13464629 = 1262309) B1262309
theorem B2659409 : Blo 1180407 2659409 := bstep (se 2 (by rfl) ⟨997278, by rfl⟩ : syracuseStep 2659409 = 1994557) B1994557
theorem B2659427 : Blo 1180407 2659427 := bstep (se 1 (by rfl) ⟨1994570, by rfl⟩ : syracuseStep 2659427 = 3989141) B3989141
theorem B1496227 : Blo 1180407 1496227 := bstep (se 1 (by rfl) ⟨1122170, by rfl⟩ : syracuseStep 1496227 = 2244341) B2244341
theorem B1496323 : Blo 1180407 1496323 := bstep (se 1 (by rfl) ⟨1122242, by rfl⟩ : syracuseStep 1496323 = 2244485) B2244485
theorem B2241827 : Blo 1180407 2241827 := bstep (se 1 (by rfl) ⟨1681370, by rfl⟩ : syracuseStep 2241827 = 3362741) B3362741
theorem B5387555 : Blo 1180407 5387555 := bstep (se 1 (by rfl) ⟨4040666, by rfl⟩ : syracuseStep 5387555 = 8081333) B8081333
theorem B3986765 : Blo 1180407 3986765 := bstep (se 3 (by rfl) ⟨747518, by rfl⟩ : syracuseStep 3986765 = 1495037) B1495037
theorem B2659697 : Blo 1180407 2659697 := bstep (se 2 (by rfl) ⟨997386, by rfl⟩ : syracuseStep 2659697 = 1994773) B1994773
theorem B3986819 : Blo 1180407 3986819 := bstep (se 1 (by rfl) ⟨2990114, by rfl⟩ : syracuseStep 3986819 = 5980229) B5980229
theorem B2659715 : Blo 1180407 2659715 := bstep (se 1 (by rfl) ⟨1994786, by rfl⟩ : syracuseStep 2659715 = 3989573) B3989573
theorem B4486691 : Blo 1180407 4486691 := bstep (se 1 (by rfl) ⟨3365018, by rfl⟩ : syracuseStep 4486691 = 6730037) B6730037
theorem B1619539 : Blo 1180407 1619539 := bstep (se 1 (by rfl) ⟨1214654, by rfl⟩ : syracuseStep 1619539 = 2429309) B2429309
theorem B2692721 : Blo 1180407 2692721 := bstep (se 2 (by rfl) ⟨1009770, by rfl⟩ : syracuseStep 2692721 = 2019541) B2019541
theorem B3987089 : Blo 1180407 3987089 := bstep (se 2 (by rfl) ⟨1495158, by rfl⟩ : syracuseStep 3987089 = 2990317) B2990317
theorem B2659985 : Blo 1180407 2659985 := bstep (se 2 (by rfl) ⟨997494, by rfl⟩ : syracuseStep 2659985 = 1994989) B1994989
theorem B2660003 : Blo 1180407 2660003 := bstep (se 1 (by rfl) ⟨1995002, by rfl⟩ : syracuseStep 2660003 = 3990005) B3990005
theorem B2021041 : Blo 1180407 2021041 := bstep (se 2 (by rfl) ⟨757890, by rfl⟩ : syracuseStep 2021041 = 1515781) B1515781
theorem B2840273 : Blo 1180407 2840273 := bstep (se 2 (by rfl) ⟨1065102, by rfl⟩ : syracuseStep 2840273 = 2130205) B2130205
theorem B2840465 : Blo 1180407 2840465 := bstep (se 2 (by rfl) ⟨1065174, by rfl⟩ : syracuseStep 2840465 = 2130349) B2130349
theorem B2660273 : Blo 1180407 2660273 := bstep (se 2 (by rfl) ⟨997602, by rfl⟩ : syracuseStep 2660273 = 1995205) B1995205
theorem B2660291 : Blo 1180407 2660291 := bstep (se 1 (by rfl) ⟨1995218, by rfl⟩ : syracuseStep 2660291 = 3990437) B3990437
theorem B6731747 : Blo 1180407 6731747 := bstep (se 1 (by rfl) ⟨5048810, by rfl⟩ : syracuseStep 6731747 = 10097621) B10097621
theorem B2988049 : Blo 1180407 2988049 := bstep (se 2 (by rfl) ⟨1120518, by rfl⟩ : syracuseStep 2988049 = 2241037) B2241037
theorem B3786851 : Blo 1180407 3786851 := bstep (se 1 (by rfl) ⟨2840138, by rfl⟩ : syracuseStep 3786851 = 5680277) B5680277
theorem B5044301 : Blo 1180407 5044301 := bstep (se 3 (by rfl) ⟨945806, by rfl⟩ : syracuseStep 5044301 = 1891613) B1891613
theorem B3364973 : Blo 1180407 3364973 := bstep (se 3 (by rfl) ⟨630932, by rfl⟩ : syracuseStep 3364973 = 1261865) B1261865
theorem B2521201 : Blo 1180407 2521201 := bstep (se 2 (by rfl) ⟨945450, by rfl⟩ : syracuseStep 2521201 = 1890901) B1890901
theorem B2521219 : Blo 1180407 2521219 := bstep (se 1 (by rfl) ⟨1890914, by rfl⟩ : syracuseStep 2521219 = 3781829) B3781829
theorem B2242723 : Blo 1180407 2242723 := bstep (se 1 (by rfl) ⟨1682042, by rfl⟩ : syracuseStep 2242723 = 3364085) B3364085
theorem B3987629 : Blo 1180407 3987629 := bstep (se 3 (by rfl) ⟨747680, by rfl⟩ : syracuseStep 3987629 = 1495361) B1495361
theorem B4487345 : Blo 1180407 4487345 := bstep (se 2 (by rfl) ⟨1682754, by rfl⟩ : syracuseStep 4487345 = 3365509) B3365509
theorem B3987683 : Blo 1180407 3987683 := bstep (se 1 (by rfl) ⟨2990762, by rfl⟩ : syracuseStep 3987683 = 5981525) B5981525
theorem B2988323 : Blo 1180407 2988323 := bstep (se 1 (by rfl) ⟨2241242, by rfl⟩ : syracuseStep 2988323 = 4482485) B4482485
theorem B3365155 : Blo 1180407 3365155 := bstep (se 1 (by rfl) ⟨2523866, by rfl⟩ : syracuseStep 3365155 = 5047733) B5047733
theorem B2242883 : Blo 1180407 2242883 := bstep (se 1 (by rfl) ⟨1682162, by rfl⟩ : syracuseStep 2242883 = 3364325) B3364325
theorem B3365201 : Blo 1180407 3365201 := bstep (se 2 (by rfl) ⟨1261950, by rfl⟩ : syracuseStep 3365201 = 2523901) B2523901
theorem B2128259 : Blo 1180407 2128259 := bstep (se 1 (by rfl) ⟨1596194, by rfl⟩ : syracuseStep 2128259 = 3192389) B3192389
theorem B2988515 : Blo 1180407 2988515 := bstep (se 1 (by rfl) ⟨2241386, by rfl⟩ : syracuseStep 2988515 = 4482773) B4482773
theorem B4790755 : Blo 1180407 4790755 := bstep (se 1 (by rfl) ⟨3593066, by rfl⟩ : syracuseStep 4790755 = 7186133) B7186133
theorem B5978609 : Blo 1180407 5978609 := bstep (se 2 (by rfl) ⟨2241978, by rfl⟩ : syracuseStep 5978609 = 4483957) B4483957
theorem B3987953 : Blo 1180407 3987953 := bstep (se 2 (by rfl) ⟨1495482, by rfl⟩ : syracuseStep 3987953 = 2990965) B2990965
theorem B22706801 : Blo 1180407 22706801 := bstep (se 2 (by rfl) ⟨8515050, by rfl⟩ : syracuseStep 22706801 = 17030101) B17030101
theorem B1890947 : Blo 1180407 1890947 := bstep (se 1 (by rfl) ⟨1418210, by rfl⟩ : syracuseStep 1890947 = 2836421) B2836421
theorem B4258595 : Blo 1180407 4258595 := bstep (se 1 (by rfl) ⟨3193946, by rfl⟩ : syracuseStep 4258595 = 6387893) B6387893
theorem B3783469 : Blo 1180407 3783469 := bstep (se 3 (by rfl) ⟨709400, by rfl⟩ : syracuseStep 3783469 = 1418801) B1418801
theorem B3988493 : Blo 1180407 3988493 := bstep (se 3 (by rfl) ⟨747842, by rfl⟩ : syracuseStep 3988493 = 1495685) B1495685
theorem B3988547 : Blo 1180407 3988547 := bstep (se 1 (by rfl) ⟨2991410, by rfl⟩ : syracuseStep 3988547 = 5982821) B5982821
theorem B6061169 : Blo 1180407 6061169 := bstep (se 2 (by rfl) ⟨2272938, by rfl⟩ : syracuseStep 6061169 = 4545877) B4545877
theorem B1891459 : Blo 1180407 1891459 := bstep (se 1 (by rfl) ⟨1418594, by rfl⟩ : syracuseStep 1891459 = 2837189) B2837189
theorem B1596611 : Blo 1180407 1596611 := bstep (se 1 (by rfl) ⟨1197458, by rfl⟩ : syracuseStep 1596611 = 2394917) B2394917
theorem B3988817 : Blo 1180407 3988817 := bstep (se 2 (by rfl) ⟨1495806, by rfl⟩ : syracuseStep 3988817 = 2991613) B2991613
theorem B1260883 : Blo 1180407 1260883 := bstep (se 1 (by rfl) ⟨945662, by rfl⟩ : syracuseStep 1260883 = 1891325) B1891325
theorem B2243953 : Blo 1180407 2243953 := bstep (se 2 (by rfl) ⟨841482, by rfl⟩ : syracuseStep 2243953 = 1682965) B1682965
theorem B2989457 : Blo 1180407 2989457 := bstep (se 2 (by rfl) ⟨1121046, by rfl⟩ : syracuseStep 2989457 = 2242093) B2242093
theorem B2989507 : Blo 1180407 2989507 := bstep (se 1 (by rfl) ⟨2242130, by rfl⟩ : syracuseStep 2989507 = 4484261) B4484261
theorem B4791793 : Blo 1180407 4791793 := bstep (se 2 (by rfl) ⟨1796922, by rfl⟩ : syracuseStep 4791793 = 3593845) B3593845
theorem B30703157 : Blo 1180407 30703157 := bstep (se 5 (by rfl) ⟨1439210, by rfl⟩ : syracuseStep 30703157 = 2878421) B2878421
theorem B2989649 : Blo 1180407 2989649 := bstep (se 2 (by rfl) ⟨1121118, by rfl⟩ : syracuseStep 2989649 = 2242237) B2242237
theorem B4488803 : Blo 1180407 4488803 := bstep (se 1 (by rfl) ⟨3366602, by rfl⟩ : syracuseStep 4488803 = 6733205) B6733205
theorem B4488817 : Blo 1180407 4488817 := bstep (se 2 (by rfl) ⟨1683306, by rfl⟩ : syracuseStep 4488817 = 3366613) B3366613
theorem B1892003 : Blo 1180407 1892003 := bstep (se 1 (by rfl) ⟨1419002, by rfl⟩ : syracuseStep 1892003 = 2838005) B2838005
theorem B3366659 : Blo 1180407 3366659 := bstep (se 1 (by rfl) ⟨2524994, by rfl⟩ : syracuseStep 3366659 = 5049989) B5049989
theorem B6725389 : Blo 1180407 6725389 := bstep (se 3 (by rfl) ⟨1261010, by rfl⟩ : syracuseStep 6725389 = 2522021) B2522021
theorem B6733637 : Blo 1180407 6733637 := bstep (se 4 (by rfl) ⟨631278, by rfl⟩ : syracuseStep 6733637 = 1262557) B1262557
theorem B1892177 : Blo 1180407 1892177 := bstep (se 2 (by rfl) ⟨709566, by rfl⟩ : syracuseStep 1892177 = 1419133) B1419133
theorem B3989357 : Blo 1180407 3989357 := bstep (se 3 (by rfl) ⟨748004, by rfl⟩ : syracuseStep 3989357 = 1496009) B1496009
theorem B3833713 : Blo 1180407 3833713 := bstep (se 2 (by rfl) ⟨1437642, by rfl⟩ : syracuseStep 3833713 = 2875285) B2875285
theorem B1277843 : Blo 1180407 1277843 := bstep (se 1 (by rfl) ⟨958382, by rfl⟩ : syracuseStep 1277843 = 1916765) B1916765
theorem B5980067 : Blo 1180407 5980067 := bstep (se 1 (by rfl) ⟨4485050, by rfl⟩ : syracuseStep 5980067 = 8970101) B8970101
theorem B3989411 : Blo 1180407 3989411 := bstep (se 1 (by rfl) ⟨2992058, by rfl⟩ : syracuseStep 3989411 = 5984117) B5984117
theorem B2990155 : Blo 1180407 2990155 := bstep (se 1 (by rfl) ⟨2242616, by rfl⟩ : syracuseStep 2990155 = 4485233) B4485233
theorem B3367001 : Blo 1180407 3367001 := bstep (se 2 (by rfl) ⟨1262625, by rfl⟩ : syracuseStep 3367001 = 2525251) B2525251
theorem B6733955 : Blo 1180407 6733955 := bstep (se 1 (by rfl) ⟨5050466, by rfl⟩ : syracuseStep 6733955 = 10100933) B10100933
theorem B1892555 : Blo 1180407 1892555 := bstep (se 1 (by rfl) ⟨1419416, by rfl⟩ : syracuseStep 1892555 = 2838833) B2838833
theorem B2990297 : Blo 1180407 2990297 := bstep (se 2 (by rfl) ⟨1121361, by rfl⟩ : syracuseStep 2990297 = 2242723) B2242723
theorem B4317401 : Blo 1180407 4317401 := bstep (se 2 (by rfl) ⟨1619025, by rfl⟩ : syracuseStep 4317401 = 3238051) B3238051
theorem B1892695 : Blo 1180407 1892695 := bstep (se 1 (by rfl) ⟨1419521, by rfl⟩ : syracuseStep 1892695 = 2839043) B2839043
theorem B7184771 : Blo 1180407 7184771 := bstep (se 1 (by rfl) ⟨5388578, by rfl⟩ : syracuseStep 7184771 = 10777157) B10777157
theorem B4260397 : Blo 1180407 4260397 := bstep (se 3 (by rfl) ⟨798824, by rfl⟩ : syracuseStep 4260397 = 1597649) B1597649
theorem B57459293 : Blo 1180407 57459293 := bstep (se 3 (by rfl) ⟨10773617, by rfl⟩ : syracuseStep 57459293 = 21547235) B21547235
theorem B1196651 : Blo 1180407 1196651 := bstep (se 1 (by rfl) ⟨897488, by rfl⟩ : syracuseStep 1196651 = 1794977) B1794977
theorem B3990167 : Blo 1180407 3990167 := bstep (se 1 (by rfl) ⟨2992625, by rfl⟩ : syracuseStep 3990167 = 5985251) B5985251
theorem B1180407 : Blo 1180407 1180407 := bstep (se 1 (by rfl) ⟨885305, by rfl⟩ : syracuseStep 1180407 = 1770611) B1770611
theorem B1180427 : Blo 1180407 1180427 := bstep (se 1 (by rfl) ⟨885320, by rfl⟩ : syracuseStep 1180427 = 1770641) B1770641
theorem B1180439 : Blo 1180407 1180439 := bstep (se 1 (by rfl) ⟨885329, by rfl⟩ : syracuseStep 1180439 = 1770659) B1770659
theorem B1180459 : Blo 1180407 1180459 := bstep (se 1 (by rfl) ⟨885344, by rfl⟩ : syracuseStep 1180459 = 1770689) B1770689
theorem B12133165 : Blo 1180407 12133165 := bstep (se 3 (by rfl) ⟨2274968, by rfl⟩ : syracuseStep 12133165 = 4549937) B4549937
theorem B1180471 : Blo 1180407 1180471 := bstep (se 1 (by rfl) ⟨885353, by rfl⟩ : syracuseStep 1180471 = 1770707) B1770707
theorem B8971073 : Blo 1180407 8971073 := bstep (se 2 (by rfl) ⟨3364152, by rfl⟩ : syracuseStep 8971073 = 6728305) B6728305
theorem B1180491 : Blo 1180407 1180491 := bstep (se 1 (by rfl) ⟨885368, by rfl⟩ : syracuseStep 1180491 = 1770737) B1770737
theorem B1180503 : Blo 1180407 1180503 := bstep (se 1 (by rfl) ⟨885377, by rfl⟩ : syracuseStep 1180503 = 1770755) B1770755
theorem B1180523 : Blo 1180407 1180523 := bstep (se 1 (by rfl) ⟨885392, by rfl⟩ : syracuseStep 1180523 = 1770785) B1770785
theorem B1180535 : Blo 1180407 1180535 := bstep (se 1 (by rfl) ⟨885401, by rfl⟩ : syracuseStep 1180535 = 1770803) B1770803
theorem B1180555 : Blo 1180407 1180555 := bstep (se 1 (by rfl) ⟨885416, by rfl⟩ : syracuseStep 1180555 = 1770833) B1770833
theorem B1180567 : Blo 1180407 1180567 := bstep (se 1 (by rfl) ⟨885425, by rfl⟩ : syracuseStep 1180567 = 1770851) B1770851
theorem B1180587 : Blo 1180407 1180587 := bstep (se 1 (by rfl) ⟨885440, by rfl⟩ : syracuseStep 1180587 = 1770881) B1770881
theorem B1180599 : Blo 1180407 1180599 := bstep (se 1 (by rfl) ⟨885449, by rfl⟩ : syracuseStep 1180599 = 1770899) B1770899
theorem B1180619 : Blo 1180407 1180619 := bstep (se 1 (by rfl) ⟨885464, by rfl⟩ : syracuseStep 1180619 = 1770929) B1770929
theorem B1180631 : Blo 1180407 1180631 := bstep (se 1 (by rfl) ⟨885473, by rfl⟩ : syracuseStep 1180631 = 1770947) B1770947
theorem B4482013 : Blo 1180407 4482013 := bstep (se 3 (by rfl) ⟨840377, by rfl⟩ : syracuseStep 4482013 = 1680755) B1680755
theorem B1328107 : Blo 1180407 1328107 := bstep (se 1 (by rfl) ⟨996080, by rfl⟩ : syracuseStep 1328107 = 1992161) B1992161
theorem B1180651 : Blo 1180407 1180651 := bstep (se 1 (by rfl) ⟨885488, by rfl⟩ : syracuseStep 1180651 = 1770977) B1770977
theorem B1180663 : Blo 1180407 1180663 := bstep (se 1 (by rfl) ⟨885497, by rfl⟩ : syracuseStep 1180663 = 1770995) B1770995
theorem B1180683 : Blo 1180407 1180683 := bstep (se 1 (by rfl) ⟨885512, by rfl⟩ : syracuseStep 1180683 = 1771025) B1771025
theorem B5981201 : Blo 1180407 5981201 := bstep (se 2 (by rfl) ⟨2242950, by rfl⟩ : syracuseStep 5981201 = 4485901) B4485901
theorem B1180695 : Blo 1180407 1180695 := bstep (se 1 (by rfl) ⟨885521, by rfl⟩ : syracuseStep 1180695 = 1771043) B1771043
theorem B2991127 : Blo 1180407 2991127 := bstep (se 1 (by rfl) ⟨2243345, by rfl⟩ : syracuseStep 2991127 = 4486691) B4486691
theorem B1180715 : Blo 1180407 1180715 := bstep (se 1 (by rfl) ⟨885536, by rfl⟩ : syracuseStep 1180715 = 1771073) B1771073
theorem B1180727 : Blo 1180407 1180727 := bstep (se 1 (by rfl) ⟨885545, by rfl⟩ : syracuseStep 1180727 = 1771091) B1771091
theorem B1180747 : Blo 1180407 1180747 := bstep (se 1 (by rfl) ⟨885560, by rfl⟩ : syracuseStep 1180747 = 1771121) B1771121
theorem B1328215 : Blo 1180407 1328215 := bstep (se 1 (by rfl) ⟨996161, by rfl⟩ : syracuseStep 1328215 = 1992323) B1992323
theorem B1180759 : Blo 1180407 1180759 := bstep (se 1 (by rfl) ⟨885569, by rfl⟩ : syracuseStep 1180759 = 1771139) B1771139
theorem B1180779 : Blo 1180407 1180779 := bstep (se 1 (by rfl) ⟨885584, by rfl⟩ : syracuseStep 1180779 = 1771169) B1771169
theorem B1180791 : Blo 1180407 1180791 := bstep (se 1 (by rfl) ⟨885593, by rfl⟩ : syracuseStep 1180791 = 1771187) B1771187
theorem B1770635 : Blo 1180407 1770635 := bstep (se 1 (by rfl) ⟨1327976, by rfl⟩ : syracuseStep 1770635 = 2655953) B2655953
theorem B1180811 : Blo 1180407 1180811 := bstep (se 1 (by rfl) ⟨885608, by rfl⟩ : syracuseStep 1180811 = 1771217) B1771217
theorem B1893515 : Blo 1180407 1893515 := bstep (se 1 (by rfl) ⟨1420136, by rfl⟩ : syracuseStep 1893515 = 2840273) B2840273
theorem B1770647 : Blo 1180407 1770647 := bstep (se 1 (by rfl) ⟨1327985, by rfl⟩ : syracuseStep 1770647 = 2655971) B2655971
theorem B1180823 : Blo 1180407 1180823 := bstep (se 1 (by rfl) ⟨885617, by rfl⟩ : syracuseStep 1180823 = 1771235) B1771235
theorem B1180843 : Blo 1180407 1180843 := bstep (se 1 (by rfl) ⟨885632, by rfl⟩ : syracuseStep 1180843 = 1771265) B1771265
theorem B5981363 : Blo 1180407 5981363 := bstep (se 1 (by rfl) ⟨4486022, by rfl⟩ : syracuseStep 5981363 = 8972045) B8972045
theorem B1180855 : Blo 1180407 1180855 := bstep (se 1 (by rfl) ⟨885641, by rfl⟩ : syracuseStep 1180855 = 1771283) B1771283
theorem B1180875 : Blo 1180407 1180875 := bstep (se 1 (by rfl) ⟨885656, by rfl⟩ : syracuseStep 1180875 = 1771313) B1771313
theorem B1180887 : Blo 1180407 1180887 := bstep (se 1 (by rfl) ⟨885665, by rfl⟩ : syracuseStep 1180887 = 1771331) B1771331
theorem B1770713 : Blo 1180407 1770713 := bstep (se 2 (by rfl) ⟨664017, by rfl⟩ : syracuseStep 1770713 = 1328035) B1328035
theorem B1893593 : Blo 1180407 1893593 := bstep (se 2 (by rfl) ⟨710097, by rfl⟩ : syracuseStep 1893593 = 1420195) B1420195
theorem B1180907 : Blo 1180407 1180907 := bstep (se 1 (by rfl) ⟨885680, by rfl⟩ : syracuseStep 1180907 = 1771361) B1771361
theorem B1180919 : Blo 1180407 1180919 := bstep (se 1 (by rfl) ⟨885689, by rfl⟩ : syracuseStep 1180919 = 1771379) B1771379
theorem B1328395 : Blo 1180407 1328395 := bstep (se 1 (by rfl) ⟨996296, by rfl⟩ : syracuseStep 1328395 = 1992593) B1992593
theorem B1180939 : Blo 1180407 1180939 := bstep (se 1 (by rfl) ⟨885704, by rfl⟩ : syracuseStep 1180939 = 1771409) B1771409
theorem B1180951 : Blo 1180407 1180951 := bstep (se 1 (by rfl) ⟨885713, by rfl⟩ : syracuseStep 1180951 = 1771427) B1771427
theorem B1180971 : Blo 1180407 1180971 := bstep (se 1 (by rfl) ⟨885728, by rfl⟩ : syracuseStep 1180971 = 1771457) B1771457
theorem B1180983 : Blo 1180407 1180983 := bstep (se 1 (by rfl) ⟨885737, by rfl⟩ : syracuseStep 1180983 = 1771475) B1771475
theorem B1770827 : Blo 1180407 1770827 := bstep (se 1 (by rfl) ⟨1328120, by rfl⟩ : syracuseStep 1770827 = 2656241) B2656241
theorem B1181003 : Blo 1180407 1181003 := bstep (se 1 (by rfl) ⟨885752, by rfl⟩ : syracuseStep 1181003 = 1771505) B1771505
theorem B2393431 : Blo 1180407 2393431 := bstep (se 1 (by rfl) ⟨1795073, by rfl⟩ : syracuseStep 2393431 = 3590147) B3590147
theorem B1770839 : Blo 1180407 1770839 := bstep (se 1 (by rfl) ⟨1328129, by rfl⟩ : syracuseStep 1770839 = 2656259) B2656259
theorem B1181015 : Blo 1180407 1181015 := bstep (se 1 (by rfl) ⟨885761, by rfl⟩ : syracuseStep 1181015 = 1771523) B1771523
theorem B1181035 : Blo 1180407 1181035 := bstep (se 1 (by rfl) ⟨885776, by rfl⟩ : syracuseStep 1181035 = 1771553) B1771553
theorem B1328503 : Blo 1180407 1328503 := bstep (se 1 (by rfl) ⟨996377, by rfl⟩ : syracuseStep 1328503 = 1992755) B1992755
theorem B1181047 : Blo 1180407 1181047 := bstep (se 1 (by rfl) ⟨885785, by rfl⟩ : syracuseStep 1181047 = 1771571) B1771571
theorem B1181067 : Blo 1180407 1181067 := bstep (se 1 (by rfl) ⟨885800, by rfl⟩ : syracuseStep 1181067 = 1771601) B1771601
theorem B1181079 : Blo 1180407 1181079 := bstep (se 1 (by rfl) ⟨885809, by rfl⟩ : syracuseStep 1181079 = 1771619) B1771619
theorem B1770905 : Blo 1180407 1770905 := bstep (se 2 (by rfl) ⟨664089, by rfl⟩ : syracuseStep 1770905 = 1328179) B1328179
theorem B2393497 : Blo 1180407 2393497 := bstep (se 2 (by rfl) ⟨897561, by rfl⟩ : syracuseStep 2393497 = 1795123) B1795123
theorem B1181099 : Blo 1180407 1181099 := bstep (se 1 (by rfl) ⟨885824, by rfl⟩ : syracuseStep 1181099 = 1771649) B1771649
theorem B3589555 : Blo 1180407 3589555 := bstep (se 1 (by rfl) ⟨2692166, by rfl⟩ : syracuseStep 3589555 = 5384333) B5384333
theorem B1181111 : Blo 1180407 1181111 := bstep (se 1 (by rfl) ⟨885833, by rfl⟩ : syracuseStep 1181111 = 1771667) B1771667
theorem B1181131 : Blo 1180407 1181131 := bstep (se 1 (by rfl) ⟨885848, by rfl⟩ : syracuseStep 1181131 = 1771697) B1771697
theorem B2991563 : Blo 1180407 2991563 := bstep (se 1 (by rfl) ⟨2243672, by rfl⟩ : syracuseStep 2991563 = 4487345) B4487345
theorem B276235733 : Blo 1180407 276235733 := bstep (se 7 (by rfl) ⟨3237137, by rfl⟩ : syracuseStep 276235733 = 6474275) B6474275
theorem B1181143 : Blo 1180407 1181143 := bstep (se 1 (by rfl) ⟨885857, by rfl⟩ : syracuseStep 1181143 = 1771715) B1771715
theorem B2393561 : Blo 1180407 2393561 := bstep (se 2 (by rfl) ⟨897585, by rfl⟩ : syracuseStep 2393561 = 1795171) B1795171
theorem B1181163 : Blo 1180407 1181163 := bstep (se 1 (by rfl) ⟨885872, by rfl⟩ : syracuseStep 1181163 = 1771745) B1771745
theorem B1181175 : Blo 1180407 1181175 := bstep (se 1 (by rfl) ⟨885881, by rfl⟩ : syracuseStep 1181175 = 1771763) B1771763
theorem B1197559 : Blo 1180407 1197559 := bstep (se 1 (by rfl) ⟨898169, by rfl⟩ : syracuseStep 1197559 = 1796339) B1796339
theorem B1771019 : Blo 1180407 1771019 := bstep (se 1 (by rfl) ⟨1328264, by rfl⟩ : syracuseStep 1771019 = 2656529) B2656529
theorem B1181195 : Blo 1180407 1181195 := bstep (se 1 (by rfl) ⟨885896, by rfl⟩ : syracuseStep 1181195 = 1771793) B1771793
theorem B1992215 : Blo 1180407 1992215 := bstep (se 1 (by rfl) ⟨1494161, by rfl⟩ : syracuseStep 1992215 = 2988323) B2988323
theorem B1771031 : Blo 1180407 1771031 := bstep (se 1 (by rfl) ⟨1328273, by rfl⟩ : syracuseStep 1771031 = 2656547) B2656547
theorem B1181207 : Blo 1180407 1181207 := bstep (se 1 (by rfl) ⟨885905, by rfl⟩ : syracuseStep 1181207 = 1771811) B1771811
theorem B1328683 : Blo 1180407 1328683 := bstep (se 1 (by rfl) ⟨996512, by rfl⟩ : syracuseStep 1328683 = 1993025) B1993025
theorem B1181227 : Blo 1180407 1181227 := bstep (se 1 (by rfl) ⟨885920, by rfl⟩ : syracuseStep 1181227 = 1771841) B1771841
theorem B1181239 : Blo 1180407 1181239 := bstep (se 1 (by rfl) ⟨885929, by rfl⟩ : syracuseStep 1181239 = 1771859) B1771859
theorem B1181259 : Blo 1180407 1181259 := bstep (se 1 (by rfl) ⟨885944, by rfl⟩ : syracuseStep 1181259 = 1771889) B1771889
theorem B1418839 : Blo 1180407 1418839 := bstep (se 1 (by rfl) ⟨1064129, by rfl⟩ : syracuseStep 1418839 = 2128259) B2128259
theorem B1181271 : Blo 1180407 1181271 := bstep (se 1 (by rfl) ⟨885953, by rfl⟩ : syracuseStep 1181271 = 1771907) B1771907
theorem B1771097 : Blo 1180407 1771097 := bstep (se 2 (by rfl) ⟨664161, by rfl⟩ : syracuseStep 1771097 = 1328323) B1328323
theorem B1181291 : Blo 1180407 1181291 := bstep (se 1 (by rfl) ⟨885968, by rfl⟩ : syracuseStep 1181291 = 1771937) B1771937
theorem B1181303 : Blo 1180407 1181303 := bstep (se 1 (by rfl) ⟨885977, by rfl⟩ : syracuseStep 1181303 = 1771955) B1771955
theorem B1181323 : Blo 1180407 1181323 := bstep (se 1 (by rfl) ⟨885992, by rfl⟩ : syracuseStep 1181323 = 1771985) B1771985
theorem B1992343 : Blo 1180407 1992343 := bstep (se 1 (by rfl) ⟨1494257, by rfl⟩ : syracuseStep 1992343 = 2988515) B2988515
theorem B1328791 : Blo 1180407 1328791 := bstep (se 1 (by rfl) ⟨996593, by rfl⟩ : syracuseStep 1328791 = 1993187) B1993187
theorem B1181335 : Blo 1180407 1181335 := bstep (se 1 (by rfl) ⟨886001, by rfl⟩ : syracuseStep 1181335 = 1772003) B1772003
theorem B1181355 : Blo 1180407 1181355 := bstep (se 1 (by rfl) ⟨886016, by rfl⟩ : syracuseStep 1181355 = 1772033) B1772033
theorem B1181367 : Blo 1180407 1181367 := bstep (se 1 (by rfl) ⟨886025, by rfl⟩ : syracuseStep 1181367 = 1772051) B1772051
theorem B1771211 : Blo 1180407 1771211 := bstep (se 1 (by rfl) ⟨1328408, by rfl⟩ : syracuseStep 1771211 = 2656817) B2656817
theorem B1181387 : Blo 1180407 1181387 := bstep (se 1 (by rfl) ⟨886040, by rfl⟩ : syracuseStep 1181387 = 1772081) B1772081
theorem B1771223 : Blo 1180407 1771223 := bstep (se 1 (by rfl) ⟨1328417, by rfl⟩ : syracuseStep 1771223 = 2656835) B2656835
theorem B1181399 : Blo 1180407 1181399 := bstep (se 1 (by rfl) ⟨886049, by rfl⟩ : syracuseStep 1181399 = 1772099) B1772099
theorem B1181419 : Blo 1180407 1181419 := bstep (se 1 (by rfl) ⟨886064, by rfl⟩ : syracuseStep 1181419 = 1772129) B1772129
theorem B1181431 : Blo 1180407 1181431 := bstep (se 1 (by rfl) ⟨886073, by rfl⟩ : syracuseStep 1181431 = 1772147) B1772147
theorem B1181451 : Blo 1180407 1181451 := bstep (se 1 (by rfl) ⟨886088, by rfl⟩ : syracuseStep 1181451 = 1772177) B1772177
theorem B1181463 : Blo 1180407 1181463 := bstep (se 1 (by rfl) ⟨886097, by rfl⟩ : syracuseStep 1181463 = 1772195) B1772195
theorem B2656025 : Blo 1180407 2656025 := bstep (se 2 (by rfl) ⟨996009, by rfl⟩ : syracuseStep 2656025 = 1992019) B1992019
theorem B1681177 : Blo 1180407 1681177 := bstep (se 2 (by rfl) ⟨630441, by rfl⟩ : syracuseStep 1681177 = 1260883) B1260883
theorem B1771289 : Blo 1180407 1771289 := bstep (se 2 (by rfl) ⟨664233, by rfl⟩ : syracuseStep 1771289 = 1328467) B1328467
theorem B1181483 : Blo 1180407 1181483 := bstep (se 1 (by rfl) ⟨886112, by rfl⟩ : syracuseStep 1181483 = 1772225) B1772225
theorem B1181495 : Blo 1180407 1181495 := bstep (se 1 (by rfl) ⟨886121, by rfl⟩ : syracuseStep 1181495 = 1772243) B1772243
theorem B2991937 : Blo 1180407 2991937 := bstep (se 2 (by rfl) ⟨1121976, by rfl⟩ : syracuseStep 2991937 = 2243953) B2243953
theorem B1328971 : Blo 1180407 1328971 := bstep (se 1 (by rfl) ⟨996728, by rfl⟩ : syracuseStep 1328971 = 1993457) B1993457
theorem B1181515 : Blo 1180407 1181515 := bstep (se 1 (by rfl) ⟨886136, by rfl⟩ : syracuseStep 1181515 = 1772273) B1772273
theorem B1181527 : Blo 1180407 1181527 := bstep (se 1 (by rfl) ⟨886145, by rfl⟩ : syracuseStep 1181527 = 1772291) B1772291
theorem B1181547 : Blo 1180407 1181547 := bstep (se 1 (by rfl) ⟨886160, by rfl⟩ : syracuseStep 1181547 = 1772321) B1772321
theorem B2656115 : Blo 1180407 2656115 := bstep (se 1 (by rfl) ⟨1992086, by rfl⟩ : syracuseStep 2656115 = 3984173) B3984173
theorem B1181559 : Blo 1180407 1181559 := bstep (se 1 (by rfl) ⟨886169, by rfl⟩ : syracuseStep 1181559 = 1772339) B1772339
theorem B1771403 : Blo 1180407 1771403 := bstep (se 1 (by rfl) ⟨1328552, by rfl⟩ : syracuseStep 1771403 = 2657105) B2657105
theorem B1181579 : Blo 1180407 1181579 := bstep (se 1 (by rfl) ⟨886184, by rfl⟩ : syracuseStep 1181579 = 1772369) B1772369
theorem B2656151 : Blo 1180407 2656151 := bstep (se 1 (by rfl) ⟨1992113, by rfl⟩ : syracuseStep 2656151 = 3984227) B3984227
theorem B1771415 : Blo 1180407 1771415 := bstep (se 1 (by rfl) ⟨1328561, by rfl⟩ : syracuseStep 1771415 = 2657123) B2657123
theorem B1181591 : Blo 1180407 1181591 := bstep (se 1 (by rfl) ⟨886193, by rfl⟩ : syracuseStep 1181591 = 1772387) B1772387
theorem B1181611 : Blo 1180407 1181611 := bstep (se 1 (by rfl) ⟨886208, by rfl⟩ : syracuseStep 1181611 = 1772417) B1772417
theorem B1329079 : Blo 1180407 1329079 := bstep (se 1 (by rfl) ⟨996809, by rfl⟩ : syracuseStep 1329079 = 1993619) B1993619
theorem B1181623 : Blo 1180407 1181623 := bstep (se 1 (by rfl) ⟨886217, by rfl⟩ : syracuseStep 1181623 = 1772435) B1772435
theorem B1181643 : Blo 1180407 1181643 := bstep (se 1 (by rfl) ⟨886232, by rfl⟩ : syracuseStep 1181643 = 1772465) B1772465
theorem B1181655 : Blo 1180407 1181655 := bstep (se 1 (by rfl) ⟨886241, by rfl⟩ : syracuseStep 1181655 = 1772483) B1772483
theorem B1771481 : Blo 1180407 1771481 := bstep (se 2 (by rfl) ⟨664305, by rfl⟩ : syracuseStep 1771481 = 1328611) B1328611
theorem B1181675 : Blo 1180407 1181675 := bstep (se 1 (by rfl) ⟨886256, by rfl⟩ : syracuseStep 1181675 = 1772513) B1772513
theorem B1181687 : Blo 1180407 1181687 := bstep (se 1 (by rfl) ⟨886265, by rfl⟩ : syracuseStep 1181687 = 1772531) B1772531
theorem B1181707 : Blo 1180407 1181707 := bstep (se 1 (by rfl) ⟨886280, by rfl⟩ : syracuseStep 1181707 = 1772561) B1772561
theorem B4786199 : Blo 1180407 4786199 := bstep (se 1 (by rfl) ⟨3589649, by rfl⟩ : syracuseStep 4786199 = 7179299) B7179299
theorem B1181719 : Blo 1180407 1181719 := bstep (se 1 (by rfl) ⟨886289, by rfl⟩ : syracuseStep 1181719 = 1772579) B1772579
theorem B1181739 : Blo 1180407 1181739 := bstep (se 1 (by rfl) ⟨886304, by rfl⟩ : syracuseStep 1181739 = 1772609) B1772609
theorem B1181751 : Blo 1180407 1181751 := bstep (se 1 (by rfl) ⟨886313, by rfl⟩ : syracuseStep 1181751 = 1772627) B1772627
theorem B2656331 : Blo 1180407 2656331 := bstep (se 1 (by rfl) ⟨1992248, by rfl⟩ : syracuseStep 2656331 = 3984497) B3984497
theorem B5752907 : Blo 1180407 5752907 := bstep (se 1 (by rfl) ⟨4314680, by rfl⟩ : syracuseStep 5752907 = 8629361) B8629361
theorem B1771595 : Blo 1180407 1771595 := bstep (se 1 (by rfl) ⟨1328696, by rfl⟩ : syracuseStep 1771595 = 2657393) B2657393
theorem B4040779 : Blo 1180407 4040779 := bstep (se 1 (by rfl) ⟨3030584, by rfl⟩ : syracuseStep 4040779 = 6061169) B6061169
theorem B1181771 : Blo 1180407 1181771 := bstep (se 1 (by rfl) ⟨886328, by rfl⟩ : syracuseStep 1181771 = 1772657) B1772657
theorem B1771607 : Blo 1180407 1771607 := bstep (se 1 (by rfl) ⟨1328705, by rfl⟩ : syracuseStep 1771607 = 2657411) B2657411
theorem B1181783 : Blo 1180407 1181783 := bstep (se 1 (by rfl) ⟨886337, by rfl⟩ : syracuseStep 1181783 = 1772675) B1772675
theorem B1329259 : Blo 1180407 1329259 := bstep (se 1 (by rfl) ⟨996944, by rfl⟩ : syracuseStep 1329259 = 1993889) B1993889
theorem B1181803 : Blo 1180407 1181803 := bstep (se 1 (by rfl) ⟨886352, by rfl⟩ : syracuseStep 1181803 = 1772705) B1772705
theorem B1181815 : Blo 1180407 1181815 := bstep (se 1 (by rfl) ⟨886361, by rfl⟩ : syracuseStep 1181815 = 1772723) B1772723
theorem B2656385 : Blo 1180407 2656385 := bstep (se 2 (by rfl) ⟨996144, by rfl⟩ : syracuseStep 2656385 = 1992289) B1992289
theorem B1181835 : Blo 1180407 1181835 := bstep (se 1 (by rfl) ⟨886376, by rfl⟩ : syracuseStep 1181835 = 1772753) B1772753
theorem B1181847 : Blo 1180407 1181847 := bstep (se 1 (by rfl) ⟨886385, by rfl⟩ : syracuseStep 1181847 = 1772771) B1772771
theorem B1771673 : Blo 1180407 1771673 := bstep (se 2 (by rfl) ⟨664377, by rfl⟩ : syracuseStep 1771673 = 1328755) B1328755
theorem B1181867 : Blo 1180407 1181867 := bstep (se 1 (by rfl) ⟨886400, by rfl⟩ : syracuseStep 1181867 = 1772801) B1772801
theorem B1181879 : Blo 1180407 1181879 := bstep (se 1 (by rfl) ⟨886409, by rfl⟩ : syracuseStep 1181879 = 1772819) B1772819
theorem B1181899 : Blo 1180407 1181899 := bstep (se 1 (by rfl) ⟨886424, by rfl⟩ : syracuseStep 1181899 = 1772849) B1772849
theorem B1329367 : Blo 1180407 1329367 := bstep (se 1 (by rfl) ⟨997025, by rfl⟩ : syracuseStep 1329367 = 1994051) B1994051
theorem B1181911 : Blo 1180407 1181911 := bstep (se 1 (by rfl) ⟨886433, by rfl⟩ : syracuseStep 1181911 = 1772867) B1772867
theorem B4483289 : Blo 1180407 4483289 := bstep (se 2 (by rfl) ⟨1681233, by rfl⟩ : syracuseStep 4483289 = 3362467) B3362467
theorem B1181931 : Blo 1180407 1181931 := bstep (se 1 (by rfl) ⟨886448, by rfl⟩ : syracuseStep 1181931 = 1772897) B1772897
theorem B1181943 : Blo 1180407 1181943 := bstep (se 1 (by rfl) ⟨886457, by rfl⟩ : syracuseStep 1181943 = 1772915) B1772915
theorem B16394501 : Blo 1180407 16394501 := bstep (se 4 (by rfl) ⟨1536984, by rfl⟩ : syracuseStep 16394501 = 3073969) B3073969
theorem B1992971 : Blo 1180407 1992971 := bstep (se 1 (by rfl) ⟨1494728, by rfl⟩ : syracuseStep 1992971 = 2989457) B2989457
theorem B1771787 : Blo 1180407 1771787 := bstep (se 1 (by rfl) ⟨1328840, by rfl⟩ : syracuseStep 1771787 = 2657681) B2657681
theorem B1181963 : Blo 1180407 1181963 := bstep (se 1 (by rfl) ⟨886472, by rfl⟩ : syracuseStep 1181963 = 1772945) B1772945
theorem B1771799 : Blo 1180407 1771799 := bstep (se 1 (by rfl) ⟨1328849, by rfl⟩ : syracuseStep 1771799 = 2657699) B2657699
theorem B1181975 : Blo 1180407 1181975 := bstep (se 1 (by rfl) ⟨886481, by rfl⟩ : syracuseStep 1181975 = 1772963) B1772963
theorem B1181995 : Blo 1180407 1181995 := bstep (se 1 (by rfl) ⟨886496, by rfl⟩ : syracuseStep 1181995 = 1772993) B1772993
theorem B1182007 : Blo 1180407 1182007 := bstep (se 1 (by rfl) ⟨886505, by rfl⟩ : syracuseStep 1182007 = 1773011) B1773011
theorem B1182027 : Blo 1180407 1182027 := bstep (se 1 (by rfl) ⟨886520, by rfl⟩ : syracuseStep 1182027 = 1773041) B1773041
theorem B1182039 : Blo 1180407 1182039 := bstep (se 1 (by rfl) ⟨886529, by rfl⟩ : syracuseStep 1182039 = 1773059) B1773059
theorem B2656601 : Blo 1180407 2656601 := bstep (se 2 (by rfl) ⟨996225, by rfl⟩ : syracuseStep 2656601 = 1992451) B1992451
theorem B1771865 : Blo 1180407 1771865 := bstep (se 2 (by rfl) ⟨664449, by rfl⟩ : syracuseStep 1771865 = 1328899) B1328899
theorem B1182059 : Blo 1180407 1182059 := bstep (se 1 (by rfl) ⟨886544, by rfl⟩ : syracuseStep 1182059 = 1773089) B1773089
theorem B1182071 : Blo 1180407 1182071 := bstep (se 1 (by rfl) ⟨886553, by rfl⟩ : syracuseStep 1182071 = 1773107) B1773107
theorem B1993099 : Blo 1180407 1993099 := bstep (se 1 (by rfl) ⟨1494824, by rfl⟩ : syracuseStep 1993099 = 2989649) B2989649
theorem B1329547 : Blo 1180407 1329547 := bstep (se 1 (by rfl) ⟨997160, by rfl⟩ : syracuseStep 1329547 = 1994321) B1994321
theorem B1182091 : Blo 1180407 1182091 := bstep (se 1 (by rfl) ⟨886568, by rfl⟩ : syracuseStep 1182091 = 1773137) B1773137
theorem B1182103 : Blo 1180407 1182103 := bstep (se 1 (by rfl) ⟨886577, by rfl⟩ : syracuseStep 1182103 = 1773155) B1773155
theorem B2992535 : Blo 1180407 2992535 := bstep (se 1 (by rfl) ⟨2244401, by rfl⟩ : syracuseStep 2992535 = 4488803) B4488803
theorem B1182123 : Blo 1180407 1182123 := bstep (se 1 (by rfl) ⟨886592, by rfl⟩ : syracuseStep 1182123 = 1773185) B1773185
theorem B2656691 : Blo 1180407 2656691 := bstep (se 1 (by rfl) ⟨1992518, by rfl⟩ : syracuseStep 2656691 = 3985037) B3985037
theorem B1182135 : Blo 1180407 1182135 := bstep (se 1 (by rfl) ⟨886601, by rfl⟩ : syracuseStep 1182135 = 1773203) B1773203
theorem B1771979 : Blo 1180407 1771979 := bstep (se 1 (by rfl) ⟨1328984, by rfl⟩ : syracuseStep 1771979 = 2657969) B2657969
theorem B1182155 : Blo 1180407 1182155 := bstep (se 1 (by rfl) ⟨886616, by rfl⟩ : syracuseStep 1182155 = 1773233) B1773233
theorem B2656727 : Blo 1180407 2656727 := bstep (se 1 (by rfl) ⟨1992545, by rfl⟩ : syracuseStep 2656727 = 3985091) B3985091
theorem B1771991 : Blo 1180407 1771991 := bstep (se 1 (by rfl) ⟨1328993, by rfl⟩ : syracuseStep 1771991 = 2657987) B2657987
theorem B10226137 : Blo 1180407 10226137 := bstep (se 2 (by rfl) ⟨3834801, by rfl⟩ : syracuseStep 10226137 = 7669603) B7669603
theorem B1182167 : Blo 1180407 1182167 := bstep (se 1 (by rfl) ⟨886625, by rfl⟩ : syracuseStep 1182167 = 1773251) B1773251
theorem B1182187 : Blo 1180407 1182187 := bstep (se 1 (by rfl) ⟨886640, by rfl⟩ : syracuseStep 1182187 = 1773281) B1773281
theorem B1329655 : Blo 1180407 1329655 := bstep (se 1 (by rfl) ⟨997241, by rfl⟩ : syracuseStep 1329655 = 1994483) B1994483
theorem B1182199 : Blo 1180407 1182199 := bstep (se 1 (by rfl) ⟨886649, by rfl⟩ : syracuseStep 1182199 = 1773299) B1773299
theorem B1182219 : Blo 1180407 1182219 := bstep (se 1 (by rfl) ⟨886664, by rfl⟩ : syracuseStep 1182219 = 1773329) B1773329
theorem B1182231 : Blo 1180407 1182231 := bstep (se 1 (by rfl) ⟨886673, by rfl⟩ : syracuseStep 1182231 = 1773347) B1773347
theorem B1993241 : Blo 1180407 1993241 := bstep (se 2 (by rfl) ⟨747465, by rfl⟩ : syracuseStep 1993241 = 1494931) B1494931
theorem B1772057 : Blo 1180407 1772057 := bstep (se 2 (by rfl) ⟨664521, by rfl⟩ : syracuseStep 1772057 = 1329043) B1329043
theorem B1182251 : Blo 1180407 1182251 := bstep (se 1 (by rfl) ⟨886688, by rfl⟩ : syracuseStep 1182251 = 1773377) B1773377
theorem B1182263 : Blo 1180407 1182263 := bstep (se 1 (by rfl) ⟨886697, by rfl⟩ : syracuseStep 1182263 = 1773395) B1773395
theorem B1182283 : Blo 1180407 1182283 := bstep (se 1 (by rfl) ⟨886712, by rfl⟩ : syracuseStep 1182283 = 1773425) B1773425
theorem B1182295 : Blo 1180407 1182295 := bstep (se 1 (by rfl) ⟨886721, by rfl⟩ : syracuseStep 1182295 = 1773443) B1773443
theorem B1182315 : Blo 1180407 1182315 := bstep (se 1 (by rfl) ⟨886736, by rfl⟩ : syracuseStep 1182315 = 1773473) B1773473
theorem B1182327 : Blo 1180407 1182327 := bstep (se 1 (by rfl) ⟨886745, by rfl⟩ : syracuseStep 1182327 = 1773491) B1773491
theorem B5048963 : Blo 1180407 5048963 := bstep (se 1 (by rfl) ⟨3786722, by rfl⟩ : syracuseStep 5048963 = 7573445) B7573445
theorem B10783363 : Blo 1180407 10783363 := bstep (se 1 (by rfl) ⟨8087522, by rfl⟩ : syracuseStep 10783363 = 16175045) B16175045
theorem B2656907 : Blo 1180407 2656907 := bstep (se 1 (by rfl) ⟨1992680, by rfl⟩ : syracuseStep 2656907 = 3985361) B3985361
theorem B1772171 : Blo 1180407 1772171 := bstep (se 1 (by rfl) ⟨1329128, by rfl⟩ : syracuseStep 1772171 = 2658257) B2658257
theorem B1182347 : Blo 1180407 1182347 := bstep (se 1 (by rfl) ⟨886760, by rfl⟩ : syracuseStep 1182347 = 1773521) B1773521
theorem B1772183 : Blo 1180407 1772183 := bstep (se 1 (by rfl) ⟨1329137, by rfl⟩ : syracuseStep 1772183 = 2658275) B2658275
theorem B1182359 : Blo 1180407 1182359 := bstep (se 1 (by rfl) ⟨886769, by rfl⟩ : syracuseStep 1182359 = 1773539) B1773539
theorem B1993369 : Blo 1180407 1993369 := bstep (se 2 (by rfl) ⟨747513, by rfl⟩ : syracuseStep 1993369 = 1495027) B1495027
theorem B1329835 : Blo 1180407 1329835 := bstep (se 1 (by rfl) ⟨997376, by rfl⟩ : syracuseStep 1329835 = 1994753) B1994753
theorem B1182379 : Blo 1180407 1182379 := bstep (se 1 (by rfl) ⟨886784, by rfl⟩ : syracuseStep 1182379 = 1773569) B1773569
theorem B1182391 : Blo 1180407 1182391 := bstep (se 1 (by rfl) ⟨886793, by rfl⟩ : syracuseStep 1182391 = 1773587) B1773587
theorem B3984065 : Blo 1180407 3984065 := bstep (se 2 (by rfl) ⟨1494024, by rfl⟩ : syracuseStep 3984065 = 2988049) B2988049
theorem B2656961 : Blo 1180407 2656961 := bstep (se 2 (by rfl) ⟨996360, by rfl⟩ : syracuseStep 2656961 = 1992721) B1992721
theorem B1772249 : Blo 1180407 1772249 := bstep (se 2 (by rfl) ⟨664593, by rfl⟩ : syracuseStep 1772249 = 1329187) B1329187
theorem B8973017 : Blo 1180407 8973017 := bstep (se 2 (by rfl) ⟨3364881, by rfl⟩ : syracuseStep 8973017 = 6729763) B6729763
theorem B1329943 : Blo 1180407 1329943 := bstep (se 1 (by rfl) ⟨997457, by rfl⟩ : syracuseStep 1329943 = 1994915) B1994915
theorem B3361601 : Blo 1180407 3361601 := bstep (se 2 (by rfl) ⟨1260600, by rfl⟩ : syracuseStep 3361601 = 2521201) B2521201
theorem B40897345 : Blo 1180407 40897345 := bstep (se 2 (by rfl) ⟨15336504, by rfl⟩ : syracuseStep 40897345 = 30673009) B30673009
theorem B1772363 : Blo 1180407 1772363 := bstep (se 1 (by rfl) ⟨1329272, by rfl⟩ : syracuseStep 1772363 = 2658545) B2658545
theorem B1772375 : Blo 1180407 1772375 := bstep (se 1 (by rfl) ⟨1329281, by rfl⟩ : syracuseStep 1772375 = 2658563) B2658563
theorem B3361625 : Blo 1180407 3361625 := bstep (se 2 (by rfl) ⟨1260609, by rfl⟩ : syracuseStep 3361625 = 2521219) B2521219
theorem B6728579 : Blo 1180407 6728579 := bstep (se 1 (by rfl) ⟨5046434, by rfl⟩ : syracuseStep 6728579 = 10092869) B10092869
theorem B1682327 : Blo 1180407 1682327 := bstep (se 1 (by rfl) ⟨1261745, by rfl⟩ : syracuseStep 1682327 = 2523491) B2523491
theorem B2657177 : Blo 1180407 2657177 := bstep (se 2 (by rfl) ⟨996441, by rfl⟩ : syracuseStep 2657177 = 1992883) B1992883
theorem B1772441 : Blo 1180407 1772441 := bstep (se 2 (by rfl) ⟨664665, by rfl⟩ : syracuseStep 1772441 = 1329331) B1329331
theorem B1330123 : Blo 1180407 1330123 := bstep (se 1 (by rfl) ⟨997592, by rfl⟩ : syracuseStep 1330123 = 1995185) B1995185
theorem B2657267 : Blo 1180407 2657267 := bstep (se 1 (by rfl) ⟨1992950, by rfl⟩ : syracuseStep 2657267 = 3985901) B3985901
theorem B1772555 : Blo 1180407 1772555 := bstep (se 1 (by rfl) ⟨1329416, by rfl⟩ : syracuseStep 1772555 = 2658833) B2658833
theorem B2657303 : Blo 1180407 2657303 := bstep (se 1 (by rfl) ⟨1992977, by rfl⟩ : syracuseStep 2657303 = 3985955) B3985955
theorem B1772567 : Blo 1180407 1772567 := bstep (se 1 (by rfl) ⟨1329425, by rfl⟩ : syracuseStep 1772567 = 2658851) B2658851
theorem B5983307 : Blo 1180407 5983307 := bstep (se 1 (by rfl) ⟨4487480, by rfl⟩ : syracuseStep 5983307 = 8974961) B8974961
theorem B1420363 : Blo 1180407 1420363 := bstep (se 1 (by rfl) ⟨1065272, by rfl⟩ : syracuseStep 1420363 = 2130545) B2130545
theorem B1772633 : Blo 1180407 1772633 := bstep (se 2 (by rfl) ⟨664737, by rfl⟩ : syracuseStep 1772633 = 1329475) B1329475
theorem B2657483 : Blo 1180407 2657483 := bstep (se 1 (by rfl) ⟨1993112, by rfl⟩ : syracuseStep 2657483 = 3986225) B3986225
theorem B1682635 : Blo 1180407 1682635 := bstep (se 1 (by rfl) ⟨1261976, by rfl⟩ : syracuseStep 1682635 = 2523953) B2523953
theorem B1772747 : Blo 1180407 1772747 := bstep (se 1 (by rfl) ⟨1329560, by rfl⟩ : syracuseStep 1772747 = 2659121) B2659121
theorem B1993943 : Blo 1180407 1993943 := bstep (se 1 (by rfl) ⟨1495457, by rfl⟩ : syracuseStep 1993943 = 2990915) B2990915
theorem B1772759 : Blo 1180407 1772759 := bstep (se 1 (by rfl) ⟨1329569, by rfl⟩ : syracuseStep 1772759 = 2659139) B2659139
theorem B3984605 : Blo 1180407 3984605 := bstep (se 3 (by rfl) ⟨747113, by rfl⟩ : syracuseStep 3984605 = 1494227) B1494227
theorem B2657537 : Blo 1180407 2657537 := bstep (se 2 (by rfl) ⟨996576, by rfl⟩ : syracuseStep 2657537 = 1993153) B1993153
theorem B1494283 : Blo 1180407 1494283 := bstep (se 1 (by rfl) ⟨1120712, by rfl⟩ : syracuseStep 1494283 = 2241425) B2241425
theorem B1772825 : Blo 1180407 1772825 := bstep (se 2 (by rfl) ⟨664809, by rfl⟩ : syracuseStep 1772825 = 1329619) B1329619
theorem B8514881 : Blo 1180407 8514881 := bstep (se 2 (by rfl) ⟨3193080, by rfl⟩ : syracuseStep 8514881 = 6386161) B6386161
theorem B1994071 : Blo 1180407 1994071 := bstep (se 1 (by rfl) ⟨1495553, by rfl⟩ : syracuseStep 1994071 = 2991107) B2991107
theorem B4787545 : Blo 1180407 4787545 := bstep (se 2 (by rfl) ⟨1795329, by rfl⟩ : syracuseStep 4787545 = 3590659) B3590659
theorem B10087811 : Blo 1180407 10087811 := bstep (se 1 (by rfl) ⟨7565858, by rfl⟩ : syracuseStep 10087811 = 15131717) B15131717
theorem B1772939 : Blo 1180407 1772939 := bstep (se 1 (by rfl) ⟨1329704, by rfl⟩ : syracuseStep 1772939 = 2659409) B2659409
theorem B9710999 : Blo 1180407 9710999 := bstep (se 1 (by rfl) ⟨7283249, by rfl⟩ : syracuseStep 9710999 = 14566499) B14566499
theorem B1772951 : Blo 1180407 1772951 := bstep (se 1 (by rfl) ⟨1329713, by rfl⟩ : syracuseStep 1772951 = 2659427) B2659427
theorem B2657753 : Blo 1180407 2657753 := bstep (se 2 (by rfl) ⟨996657, by rfl⟩ : syracuseStep 2657753 = 1993315) B1993315
theorem B1773017 : Blo 1180407 1773017 := bstep (se 2 (by rfl) ⟨664881, by rfl⟩ : syracuseStep 1773017 = 1329763) B1329763
theorem B1494551 : Blo 1180407 1494551 := bstep (se 1 (by rfl) ⟨1120913, by rfl⟩ : syracuseStep 1494551 = 2241827) B2241827
theorem B2657843 : Blo 1180407 2657843 := bstep (se 1 (by rfl) ⟨1993382, by rfl⟩ : syracuseStep 2657843 = 3986765) B3986765
theorem B1773131 : Blo 1180407 1773131 := bstep (se 1 (by rfl) ⟨1329848, by rfl⟩ : syracuseStep 1773131 = 2659697) B2659697
theorem B2657879 : Blo 1180407 2657879 := bstep (se 1 (by rfl) ⟨1993409, by rfl⟩ : syracuseStep 2657879 = 3986819) B3986819
theorem B1773143 : Blo 1180407 1773143 := bstep (se 1 (by rfl) ⟨1329857, by rfl⟩ : syracuseStep 1773143 = 2659715) B2659715
theorem B13463171 : Blo 1180407 13463171 := bstep (se 1 (by rfl) ⟨10097378, by rfl⟩ : syracuseStep 13463171 = 20194757) B20194757
theorem B1773209 : Blo 1180407 1773209 := bstep (se 2 (by rfl) ⟨664953, by rfl⟩ : syracuseStep 1773209 = 1329907) B1329907
theorem B109080269 : Blo 1180407 109080269 := bstep (se 3 (by rfl) ⟨20452550, by rfl⟩ : syracuseStep 109080269 = 40905101) B40905101
theorem B2395865 : Blo 1180407 2395865 := bstep (se 2 (by rfl) ⟨898449, by rfl⟩ : syracuseStep 2395865 = 1796899) B1796899
theorem B2658059 : Blo 1180407 2658059 := bstep (se 1 (by rfl) ⟨1993544, by rfl⟩ : syracuseStep 2658059 = 3987089) B3987089
theorem B1773323 : Blo 1180407 1773323 := bstep (se 1 (by rfl) ⟨1329992, by rfl⟩ : syracuseStep 1773323 = 2659985) B2659985
theorem B1773335 : Blo 1180407 1773335 := bstep (se 1 (by rfl) ⟨1330001, by rfl⟩ : syracuseStep 1773335 = 2660003) B2660003
theorem B4484915 : Blo 1180407 4484915 := bstep (se 1 (by rfl) ⟨3363686, by rfl⟩ : syracuseStep 4484915 = 6727373) B6727373
theorem B4255553 : Blo 1180407 4255553 := bstep (se 2 (by rfl) ⟨1595832, by rfl⟩ : syracuseStep 4255553 = 3191665) B3191665
theorem B4484929 : Blo 1180407 4484929 := bstep (se 2 (by rfl) ⟨1681848, by rfl⟩ : syracuseStep 4484929 = 3363697) B3363697
theorem B2658113 : Blo 1180407 2658113 := bstep (se 2 (by rfl) ⟨996792, by rfl⟩ : syracuseStep 2658113 = 1993585) B1993585
theorem B1773401 : Blo 1180407 1773401 := bstep (se 2 (by rfl) ⟨665025, by rfl⟩ : syracuseStep 1773401 = 1330051) B1330051
theorem B1994699 : Blo 1180407 1994699 := bstep (se 1 (by rfl) ⟨1496024, by rfl⟩ : syracuseStep 1994699 = 2992049) B2992049
theorem B1773515 : Blo 1180407 1773515 := bstep (se 1 (by rfl) ⟨1330136, by rfl⟩ : syracuseStep 1773515 = 2660273) B2660273
theorem B1773527 : Blo 1180407 1773527 := bstep (se 1 (by rfl) ⟨1330145, by rfl⟩ : syracuseStep 1773527 = 2660291) B2660291
theorem B2658329 : Blo 1180407 2658329 := bstep (se 2 (by rfl) ⟨996873, by rfl⟩ : syracuseStep 2658329 = 1993747) B1993747
theorem B1773593 : Blo 1180407 1773593 := bstep (se 2 (by rfl) ⟨665097, by rfl⟩ : syracuseStep 1773593 = 1330195) B1330195
theorem B3362867 : Blo 1180407 3362867 := bstep (se 1 (by rfl) ⟨2522150, by rfl⟩ : syracuseStep 3362867 = 5044301) B5044301
theorem B1994827 : Blo 1180407 1994827 := bstep (se 1 (by rfl) ⟨1496120, by rfl⟩ : syracuseStep 1994827 = 2992241) B2992241
theorem B2658419 : Blo 1180407 2658419 := bstep (se 1 (by rfl) ⟨1993814, by rfl⟩ : syracuseStep 2658419 = 3987629) B3987629
theorem B2658455 : Blo 1180407 2658455 := bstep (se 1 (by rfl) ⟨1993841, by rfl⟩ : syracuseStep 2658455 = 3987683) B3987683
theorem B4042955 : Blo 1180407 4042955 := bstep (se 1 (by rfl) ⟨3032216, by rfl⟩ : syracuseStep 4042955 = 6064433) B6064433
theorem B1495255 : Blo 1180407 1495255 := bstep (se 1 (by rfl) ⟨1121441, by rfl⟩ : syracuseStep 1495255 = 2242883) B2242883
theorem B1994969 : Blo 1180407 1994969 := bstep (se 2 (by rfl) ⟨748113, by rfl⟩ : syracuseStep 1994969 = 1496227) B1496227
theorem B7180589 : Blo 1180407 7180589 := bstep (se 3 (by rfl) ⟨1346360, by rfl⟩ : syracuseStep 7180589 = 2692721) B2692721
theorem B3985739 : Blo 1180407 3985739 := bstep (se 1 (by rfl) ⟨2989304, by rfl⟩ : syracuseStep 3985739 = 5978609) B5978609
theorem B2658635 : Blo 1180407 2658635 := bstep (se 1 (by rfl) ⟨1993976, by rfl⟩ : syracuseStep 2658635 = 3987953) B3987953
theorem B1995097 : Blo 1180407 1995097 := bstep (se 2 (by rfl) ⟨748161, by rfl⟩ : syracuseStep 1995097 = 1496323) B1496323
theorem B2658689 : Blo 1180407 2658689 := bstep (se 2 (by rfl) ⟨997008, by rfl⟩ : syracuseStep 2658689 = 1994017) B1994017
theorem B34550165 : Blo 1180407 34550165 := bstep (se 6 (by rfl) ⟨809769, by rfl⟩ : syracuseStep 34550165 = 1619539) B1619539
theorem B2839063 : Blo 1180407 2839063 := bstep (se 1 (by rfl) ⟨2129297, by rfl⟩ : syracuseStep 2839063 = 4258595) B4258595
theorem B19157573 : Blo 1180407 19157573 := bstep (se 4 (by rfl) ⟨1796022, by rfl⟩ : syracuseStep 19157573 = 3592045) B3592045
theorem B3986009 : Blo 1180407 3986009 := bstep (se 2 (by rfl) ⟨1494753, by rfl⟩ : syracuseStep 3986009 = 2989507) B2989507
theorem B2658905 : Blo 1180407 2658905 := bstep (se 2 (by rfl) ⟨997089, by rfl⟩ : syracuseStep 2658905 = 1994179) B1994179
theorem B4043353 : Blo 1180407 4043353 := bstep (se 2 (by rfl) ⟨1516257, by rfl⟩ : syracuseStep 4043353 = 3032515) B3032515
theorem B20181635 : Blo 1180407 20181635 := bstep (se 1 (by rfl) ⟨15136226, by rfl⟩ : syracuseStep 20181635 = 30272453) B30272453
theorem B2658995 : Blo 1180407 2658995 := bstep (se 1 (by rfl) ⟨1994246, by rfl⟩ : syracuseStep 2658995 = 3988493) B3988493
theorem B2659031 : Blo 1180407 2659031 := bstep (se 1 (by rfl) ⟨1994273, by rfl⟩ : syracuseStep 2659031 = 3988547) B3988547
theorem B5985089 : Blo 1180407 5985089 := bstep (se 2 (by rfl) ⟨2244408, by rfl⟩ : syracuseStep 5985089 = 4488817) B4488817
theorem B2659211 : Blo 1180407 2659211 := bstep (se 1 (by rfl) ⟨1994408, by rfl⟩ : syracuseStep 2659211 = 3988817) B3988817
theorem B2659265 : Blo 1180407 2659265 := bstep (se 2 (by rfl) ⟨997224, by rfl⟩ : syracuseStep 2659265 = 1994449) B1994449
theorem B2241523 : Blo 1180407 2241523 := bstep (se 1 (by rfl) ⟨1681142, by rfl⟩ : syracuseStep 2241523 = 3362285) B3362285
theorem B8967185 : Blo 1180407 8967185 := bstep (se 2 (by rfl) ⟨3362694, by rfl⟩ : syracuseStep 8967185 = 6725389) B6725389
theorem B20468771 : Blo 1180407 20468771 := bstep (se 1 (by rfl) ⟨15351578, by rfl⟩ : syracuseStep 20468771 = 30703157) B30703157
theorem B7574573 : Blo 1180407 7574573 := bstep (se 3 (by rfl) ⟨1420232, by rfl⟩ : syracuseStep 7574573 = 2840465) B2840465
theorem B2159731 : Blo 1180407 2159731 := bstep (se 1 (by rfl) ⟨1619798, by rfl⟩ : syracuseStep 2159731 = 3239597) B3239597
theorem B2659481 : Blo 1180407 2659481 := bstep (se 2 (by rfl) ⟨997305, by rfl⟩ : syracuseStep 2659481 = 1994611) B1994611
theorem B2241751 : Blo 1180407 2241751 := bstep (se 1 (by rfl) ⟨1681313, by rfl⟩ : syracuseStep 2241751 = 3362627) B3362627
theorem B2659571 : Blo 1180407 2659571 := bstep (se 1 (by rfl) ⟨1994678, by rfl⟩ : syracuseStep 2659571 = 3989357) B3989357
theorem B3986711 : Blo 1180407 3986711 := bstep (se 1 (by rfl) ⟨2990033, by rfl⟩ : syracuseStep 3986711 = 5980067) B5980067
theorem B2659607 : Blo 1180407 2659607 := bstep (se 1 (by rfl) ⟨1994705, by rfl⟩ : syracuseStep 2659607 = 3989411) B3989411
theorem B2241857 : Blo 1180407 2241857 := bstep (se 2 (by rfl) ⟨840696, by rfl⟩ : syracuseStep 2241857 = 1681393) B1681393
theorem B5977475 : Blo 1180407 5977475 := bstep (se 1 (by rfl) ⟨4483106, by rfl⟩ : syracuseStep 5977475 = 8966213) B8966213
theorem B3593651 : Blo 1180407 3593651 := bstep (se 1 (by rfl) ⟨2695238, by rfl⟩ : syracuseStep 3593651 = 5390477) B5390477
theorem B2659787 : Blo 1180407 2659787 := bstep (se 1 (by rfl) ⟨1994840, by rfl⟩ : syracuseStep 2659787 = 3989681) B3989681
theorem B2242009 : Blo 1180407 2242009 := bstep (se 2 (by rfl) ⟨840753, by rfl⟩ : syracuseStep 2242009 = 1681507) B1681507
theorem B3192281 : Blo 1180407 3192281 := bstep (se 2 (by rfl) ⟨1197105, by rfl⟩ : syracuseStep 3192281 = 2394211) B2394211
theorem B2659841 : Blo 1180407 2659841 := bstep (se 2 (by rfl) ⟨997440, by rfl⟩ : syracuseStep 2659841 = 1994881) B1994881
theorem B10098269 : Blo 1180407 10098269 := bstep (se 3 (by rfl) ⟨1893425, by rfl⟩ : syracuseStep 10098269 = 3786851) B3786851
theorem B4486859 : Blo 1180407 4486859 := bstep (se 1 (by rfl) ⟨3365144, by rfl⟩ : syracuseStep 4486859 = 6730289) B6730289
theorem B4486873 : Blo 1180407 4486873 := bstep (se 2 (by rfl) ⟨1682577, by rfl⟩ : syracuseStep 4486873 = 3365155) B3365155
theorem B2660057 : Blo 1180407 2660057 := bstep (se 2 (by rfl) ⟨997521, by rfl⟩ : syracuseStep 2660057 = 1995043) B1995043
theorem B3987251 : Blo 1180407 3987251 := bstep (se 1 (by rfl) ⟨2990438, by rfl⟩ : syracuseStep 3987251 = 5980877) B5980877
theorem B2660147 : Blo 1180407 2660147 := bstep (se 1 (by rfl) ⟨1995110, by rfl⟩ : syracuseStep 2660147 = 3990221) B3990221
theorem B2660183 : Blo 1180407 2660183 := bstep (se 1 (by rfl) ⟨1995137, by rfl⟩ : syracuseStep 2660183 = 3990275) B3990275
theorem B4257629 : Blo 1180407 4257629 := bstep (se 3 (by rfl) ⟨798305, by rfl⟩ : syracuseStep 4257629 = 1596611) B1596611
theorem B6387673 : Blo 1180407 6387673 := bstep (se 2 (by rfl) ⟨2395377, by rfl⟩ : syracuseStep 6387673 = 4790755) B4790755
theorem B4610009 : Blo 1180407 4610009 := bstep (se 2 (by rfl) ⟨1728753, by rfl⟩ : syracuseStep 4610009 = 3457507) B3457507
theorem B2660363 : Blo 1180407 2660363 := bstep (se 1 (by rfl) ⟨1995272, by rfl⟩ : syracuseStep 2660363 = 3990545) B3990545
theorem B2275339 : Blo 1180407 2275339 := bstep (se 1 (by rfl) ⟨1706504, by rfl⟩ : syracuseStep 2275339 = 3413009) B3413009
theorem B8976419 : Blo 1180407 8976419 := bstep (se 1 (by rfl) ⟨6732314, by rfl⟩ : syracuseStep 8976419 = 13464629) B13464629
theorem B3987521 : Blo 1180407 3987521 := bstep (se 2 (by rfl) ⟨1495320, by rfl⟩ : syracuseStep 3987521 = 2990641) B2990641
theorem B2660417 : Blo 1180407 2660417 := bstep (se 2 (by rfl) ⟨997656, by rfl⟩ : syracuseStep 2660417 = 1995313) B1995313
theorem B14366813 : Blo 1180407 14366813 := bstep (se 3 (by rfl) ⟨2693777, by rfl⟩ : syracuseStep 14366813 = 5387555) B5387555
theorem B2988211 : Blo 1180407 2988211 := bstep (se 1 (by rfl) ⟨2241158, by rfl⟩ : syracuseStep 2988211 = 4482317) B4482317
theorem B2021593 : Blo 1180407 2021593 := bstep (se 2 (by rfl) ⟨758097, by rfl⟩ : syracuseStep 2021593 = 1516195) B1516195
theorem B2988353 : Blo 1180407 2988353 := bstep (se 2 (by rfl) ⟨1120632, by rfl⟩ : syracuseStep 2988353 = 2241265) B2241265
theorem B10099019 : Blo 1180407 10099019 := bstep (se 1 (by rfl) ⟨7574264, by rfl⟩ : syracuseStep 10099019 = 15148529) B15148529
theorem B17021285 : Blo 1180407 17021285 := bstep (se 4 (by rfl) ⟨1595745, by rfl⟩ : syracuseStep 17021285 = 3191491) B3191491
theorem B5044625 : Blo 1180407 5044625 := bstep (se 2 (by rfl) ⟨1891734, by rfl⟩ : syracuseStep 5044625 = 3783469) B3783469
theorem B9099697 : Blo 1180407 9099697 := bstep (se 2 (by rfl) ⟨3412386, by rfl⟩ : syracuseStep 9099697 = 6824773) B6824773
theorem B8632925 : Blo 1180407 8632925 := bstep (se 3 (by rfl) ⟨1618673, by rfl⟩ : syracuseStep 8632925 = 3237347) B3237347
theorem B3988061 : Blo 1180407 3988061 := bstep (se 3 (by rfl) ⟨747761, by rfl⟩ : syracuseStep 3988061 = 1495523) B1495523
theorem B4487831 : Blo 1180407 4487831 := bstep (se 1 (by rfl) ⟨3365873, by rfl⟩ : syracuseStep 4487831 = 6731747) B6731747
theorem B2243315 : Blo 1180407 2243315 := bstep (se 1 (by rfl) ⟨1682486, by rfl⟩ : syracuseStep 2243315 = 3364973) B3364973
theorem B4315907 : Blo 1180407 4315907 := bstep (se 1 (by rfl) ⟨3236930, by rfl⟩ : syracuseStep 4315907 = 6473861) B6473861
theorem B2525131 : Blo 1180407 2525131 := bstep (se 1 (by rfl) ⟨1893848, by rfl⟩ : syracuseStep 2525131 = 3787697) B3787697
theorem B13450049 : Blo 1180407 13450049 := bstep (se 2 (by rfl) ⟨5043768, by rfl⟩ : syracuseStep 13450049 = 10087537) B10087537
theorem B2521945 : Blo 1180407 2521945 := bstep (se 2 (by rfl) ⟨945729, by rfl⟩ : syracuseStep 2521945 = 1891459) B1891459
theorem B3365725 : Blo 1180407 3365725 := bstep (se 3 (by rfl) ⟨631073, by rfl⟩ : syracuseStep 3365725 = 1262147) B1262147
theorem B2243467 : Blo 1180407 2243467 := bstep (se 1 (by rfl) ⟨1682600, by rfl⟩ : syracuseStep 2243467 = 3365201) B3365201
theorem B3365783 : Blo 1180407 3365783 := bstep (se 1 (by rfl) ⟨2524337, by rfl⟩ : syracuseStep 3365783 = 5048675) B5048675
theorem B15137867 : Blo 1180407 15137867 := bstep (se 1 (by rfl) ⟨11353400, by rfl⟩ : syracuseStep 15137867 = 22706801) B22706801
theorem B1260631 : Blo 1180407 1260631 := bstep (se 1 (by rfl) ⟨945473, by rfl⟩ : syracuseStep 1260631 = 1890947) B1890947
theorem B4545629 : Blo 1180407 4545629 := bstep (se 3 (by rfl) ⟨852305, by rfl⟩ : syracuseStep 4545629 = 1704611) B1704611
theorem B5045341 : Blo 1180407 5045341 := bstep (se 3 (by rfl) ⟨946001, by rfl⟩ : syracuseStep 5045341 = 1892003) B1892003
theorem B7183511 : Blo 1180407 7183511 := bstep (se 1 (by rfl) ⟨5387633, by rfl⟩ : syracuseStep 7183511 = 10775267) B10775267
theorem B2243801 : Blo 1180407 2243801 := bstep (se 2 (by rfl) ⟨841425, by rfl⟩ : syracuseStep 2243801 = 1682851) B1682851
theorem B20446469 : Blo 1180407 20446469 := bstep (se 4 (by rfl) ⟨1916856, by rfl⟩ : syracuseStep 20446469 = 3833713) B3833713
theorem B9706787 : Blo 1180407 9706787 := bstep (se 1 (by rfl) ⟨7280090, by rfl⟩ : syracuseStep 9706787 = 14560181) B14560181
theorem B6389057 : Blo 1180407 6389057 := bstep (se 2 (by rfl) ⟨2395896, by rfl⟩ : syracuseStep 6389057 = 4791793) B4791793
theorem B2989619 : Blo 1180407 2989619 := bstep (se 1 (by rfl) ⟨2242214, by rfl⟩ : syracuseStep 2989619 = 4484429) B4484429
theorem B2694721 : Blo 1180407 2694721 := bstep (se 2 (by rfl) ⟨1010520, by rfl⟩ : syracuseStep 2694721 = 2021041) B2021041
theorem B1891991 : Blo 1180407 1891991 := bstep (se 1 (by rfl) ⟨1418993, by rfl⟩ : syracuseStep 1891991 = 2837987) B2837987
theorem B3989195 : Blo 1180407 3989195 := bstep (se 1 (by rfl) ⟨2991896, by rfl⟩ : syracuseStep 3989195 = 5983793) B5983793
theorem B3407581 : Blo 1180407 3407581 := bstep (se 3 (by rfl) ⟨638921, by rfl⟩ : syracuseStep 3407581 = 1277843) B1277843
theorem B20168513 : Blo 1180407 20168513 := bstep (se 2 (by rfl) ⟨7563192, by rfl⟩ : syracuseStep 20168513 = 15126385) B15126385
theorem B2244439 : Blo 1180407 2244439 := bstep (se 1 (by rfl) ⟨1683329, by rfl⟩ : syracuseStep 2244439 = 3366659) B3366659
theorem B4489091 : Blo 1180407 4489091 := bstep (se 1 (by rfl) ⟨3366818, by rfl⟩ : syracuseStep 4489091 = 6733637) B6733637
theorem B1261451 : Blo 1180407 1261451 := bstep (se 1 (by rfl) ⟨946088, by rfl⟩ : syracuseStep 1261451 = 1892177) B1892177
theorem B2695091 : Blo 1180407 2695091 := bstep (se 1 (by rfl) ⟨2021318, by rfl⟩ : syracuseStep 2695091 = 4042637) B4042637
theorem B10100659 : Blo 1180407 10100659 := bstep (se 1 (by rfl) ⟨7575494, by rfl⟩ : syracuseStep 10100659 = 15150989) B15150989
theorem B3989465 : Blo 1180407 3989465 := bstep (se 2 (by rfl) ⟨1496049, by rfl⟩ : syracuseStep 3989465 = 2992099) B2992099
theorem B2244667 : Blo 1180407 2244667 := bstep (se 1 (by rfl) ⟨1683500, by rfl⟩ : syracuseStep 2244667 = 3367001) B3367001
theorem B4489303 : Blo 1180407 4489303 := bstep (se 1 (by rfl) ⟨3366977, by rfl⟩ : syracuseStep 4489303 = 6733955) B6733955
theorem B1261703 : Blo 1180407 1261703 := bstep (se 1 (by rfl) ⟨946277, by rfl⟩ : syracuseStep 1261703 = 1892555) B1892555
theorem B2695303 : Blo 1180407 2695303 := bstep (se 1 (by rfl) ⟨2021477, by rfl⟩ : syracuseStep 2695303 = 4042955) B4042955
theorem B2695457 : Blo 1180407 2695457 := bstep (se 2 (by rfl) ⟨1010796, by rfl⟩ : syracuseStep 2695457 = 2021593) B2021593
theorem B12771715 : Blo 1180407 12771715 := bstep (se 1 (by rfl) ⟨9578786, by rfl⟩ : syracuseStep 12771715 = 19157573) B19157573
theorem B38306195 : Blo 1180407 38306195 := bstep (se 1 (by rfl) ⟨28729646, by rfl⟩ : syracuseStep 38306195 = 57459293) B57459293
theorem B2523593 : Blo 1180407 2523593 := bstep (se 2 (by rfl) ⟨946347, by rfl⟩ : syracuseStep 2523593 = 1892695) B1892695
theorem B5980715 : Blo 1180407 5980715 := bstep (se 1 (by rfl) ⟨4485536, by rfl⟩ : syracuseStep 5980715 = 8971073) B8971073
theorem B3990059 : Blo 1180407 3990059 := bstep (se 1 (by rfl) ⟨2992544, by rfl⟩ : syracuseStep 3990059 = 5985089) B5985089
theorem B12132929 : Blo 1180407 12132929 := bstep (se 2 (by rfl) ⟨4549848, by rfl⟩ : syracuseStep 12132929 = 9099697) B9099697
theorem B3785417 : Blo 1180407 3785417 := bstep (se 2 (by rfl) ⟨1419531, by rfl⟩ : syracuseStep 3785417 = 2839063) B2839063
theorem B1180423 : Blo 1180407 1180423 := bstep (se 1 (by rfl) ⟨885317, by rfl⟩ : syracuseStep 1180423 = 1770635) B1770635
theorem B1180431 : Blo 1180407 1180431 := bstep (se 1 (by rfl) ⟨885323, by rfl⟩ : syracuseStep 1180431 = 1770647) B1770647
theorem B5391137 : Blo 1180407 5391137 := bstep (se 2 (by rfl) ⟨2021676, by rfl⟩ : syracuseStep 5391137 = 4043353) B4043353
theorem B1180475 : Blo 1180407 1180475 := bstep (se 1 (by rfl) ⟨885356, by rfl⟩ : syracuseStep 1180475 = 1770713) B1770713
theorem B1262395 : Blo 1180407 1262395 := bstep (se 1 (by rfl) ⟨946796, by rfl⟩ : syracuseStep 1262395 = 1893593) B1893593
theorem B14377817 : Blo 1180407 14377817 := bstep (se 2 (by rfl) ⟨5391681, by rfl⟩ : syracuseStep 14377817 = 10783363) B10783363
theorem B1180551 : Blo 1180407 1180551 := bstep (se 1 (by rfl) ⟨885413, by rfl⟩ : syracuseStep 1180551 = 1770827) B1770827
theorem B1180559 : Blo 1180407 1180559 := bstep (se 1 (by rfl) ⟨885419, by rfl⟩ : syracuseStep 1180559 = 1770839) B1770839
theorem B1180603 : Blo 1180407 1180603 := bstep (se 1 (by rfl) ⟨885452, by rfl⟩ : syracuseStep 1180603 = 1770905) B1770905
theorem B184157155 : Blo 1180407 184157155 := bstep (se 1 (by rfl) ⟨138117866, by rfl⟩ : syracuseStep 184157155 = 276235733) B276235733
theorem B1180679 : Blo 1180407 1180679 := bstep (se 1 (by rfl) ⟨885509, by rfl⟩ : syracuseStep 1180679 = 1771019) B1771019
theorem B1328143 : Blo 1180407 1328143 := bstep (se 1 (by rfl) ⟨996107, by rfl⟩ : syracuseStep 1328143 = 1992215) B1992215
theorem B1180687 : Blo 1180407 1180687 := bstep (se 1 (by rfl) ⟨885515, by rfl⟩ : syracuseStep 1180687 = 1771031) B1771031
theorem B1180731 : Blo 1180407 1180731 := bstep (se 1 (by rfl) ⟨885548, by rfl⟩ : syracuseStep 1180731 = 1771097) B1771097
theorem B1180807 : Blo 1180407 1180807 := bstep (se 1 (by rfl) ⟨885605, by rfl⟩ : syracuseStep 1180807 = 1771211) B1771211
theorem B2991239 : Blo 1180407 2991239 := bstep (se 1 (by rfl) ⟨2243429, by rfl⟩ : syracuseStep 2991239 = 4486859) B4486859
theorem B1180815 : Blo 1180407 1180815 := bstep (se 1 (by rfl) ⟨885611, by rfl⟩ : syracuseStep 1180815 = 1771223) B1771223
theorem B2991289 : Blo 1180407 2991289 := bstep (se 2 (by rfl) ⟨1121733, by rfl⟩ : syracuseStep 2991289 = 2243467) B2243467
theorem B1770683 : Blo 1180407 1770683 := bstep (se 1 (by rfl) ⟨1328012, by rfl⟩ : syracuseStep 1770683 = 2656025) B2656025
theorem B1180859 : Blo 1180407 1180859 := bstep (se 1 (by rfl) ⟨885644, by rfl⟩ : syracuseStep 1180859 = 1771289) B1771289
theorem B1770743 : Blo 1180407 1770743 := bstep (se 1 (by rfl) ⟨1328057, by rfl⟩ : syracuseStep 1770743 = 2656115) B2656115
theorem B1180935 : Blo 1180407 1180935 := bstep (se 1 (by rfl) ⟨885701, by rfl⟩ : syracuseStep 1180935 = 1771403) B1771403
theorem B1770767 : Blo 1180407 1770767 := bstep (se 1 (by rfl) ⟨1328075, by rfl⟩ : syracuseStep 1770767 = 2656151) B2656151
theorem B1180943 : Blo 1180407 1180943 := bstep (se 1 (by rfl) ⟨885707, by rfl⟩ : syracuseStep 1180943 = 1771415) B1771415
theorem B1770809 : Blo 1180407 1770809 := bstep (se 2 (by rfl) ⟨664053, by rfl⟩ : syracuseStep 1770809 = 1328107) B1328107
theorem B1180987 : Blo 1180407 1180987 := bstep (se 1 (by rfl) ⟨885740, by rfl⟩ : syracuseStep 1180987 = 1771481) B1771481
theorem B3073339 : Blo 1180407 3073339 := bstep (se 1 (by rfl) ⟨2305004, by rfl⟩ : syracuseStep 3073339 = 4610009) B4610009
theorem B1770887 : Blo 1180407 1770887 := bstep (se 1 (by rfl) ⟨1328165, by rfl⟩ : syracuseStep 1770887 = 2656331) B2656331
theorem B3835271 : Blo 1180407 3835271 := bstep (se 1 (by rfl) ⟨2876453, by rfl⟩ : syracuseStep 3835271 = 5752907) B5752907
theorem B1181063 : Blo 1180407 1181063 := bstep (se 1 (by rfl) ⟨885797, by rfl⟩ : syracuseStep 1181063 = 1771595) B1771595
theorem B1181071 : Blo 1180407 1181071 := bstep (se 1 (by rfl) ⟨885803, by rfl⟩ : syracuseStep 1181071 = 1771607) B1771607
theorem B1770923 : Blo 1180407 1770923 := bstep (se 1 (by rfl) ⟨1328192, by rfl⟩ : syracuseStep 1770923 = 2656385) B2656385
theorem B1893817 : Blo 1180407 1893817 := bstep (se 2 (by rfl) ⟨710181, by rfl⟩ : syracuseStep 1893817 = 1420363) B1420363
theorem B1181115 : Blo 1180407 1181115 := bstep (se 1 (by rfl) ⟨885836, by rfl⟩ : syracuseStep 1181115 = 1771673) B1771673
theorem B1680841 : Blo 1180407 1680841 := bstep (se 2 (by rfl) ⟨630315, by rfl⟩ : syracuseStep 1680841 = 1260631) B1260631
theorem B1770953 : Blo 1180407 1770953 := bstep (se 2 (by rfl) ⟨664107, by rfl⟩ : syracuseStep 1770953 = 1328215) B1328215
theorem B6727121 : Blo 1180407 6727121 := bstep (se 2 (by rfl) ⟨2522670, by rfl⟩ : syracuseStep 6727121 = 5045341) B5045341
theorem B10929667 : Blo 1180407 10929667 := bstep (se 1 (by rfl) ⟨8197250, by rfl⟩ : syracuseStep 10929667 = 16394501) B16394501
theorem B1328647 : Blo 1180407 1328647 := bstep (se 1 (by rfl) ⟨996485, by rfl⟩ : syracuseStep 1328647 = 1992971) B1992971
theorem B1181191 : Blo 1180407 1181191 := bstep (se 1 (by rfl) ⟨885893, by rfl⟩ : syracuseStep 1181191 = 1771787) B1771787
theorem B1181199 : Blo 1180407 1181199 := bstep (se 1 (by rfl) ⟨885899, by rfl⟩ : syracuseStep 1181199 = 1771799) B1771799
theorem B1992235 : Blo 1180407 1992235 := bstep (se 1 (by rfl) ⟨1494176, by rfl⟩ : syracuseStep 1992235 = 2988353) B2988353
theorem B1771067 : Blo 1180407 1771067 := bstep (se 1 (by rfl) ⟨1328300, by rfl⟩ : syracuseStep 1771067 = 2656601) B2656601
theorem B1181243 : Blo 1180407 1181243 := bstep (se 1 (by rfl) ⟨885932, by rfl⟩ : syracuseStep 1181243 = 1771865) B1771865
theorem B11347523 : Blo 1180407 11347523 := bstep (se 1 (by rfl) ⟨8510642, by rfl⟩ : syracuseStep 11347523 = 17021285) B17021285
theorem B1771127 : Blo 1180407 1771127 := bstep (se 1 (by rfl) ⟨1328345, by rfl⟩ : syracuseStep 1771127 = 2656691) B2656691
theorem B1181319 : Blo 1180407 1181319 := bstep (se 1 (by rfl) ⟨885989, by rfl⟩ : syracuseStep 1181319 = 1771979) B1771979
theorem B1771151 : Blo 1180407 1771151 := bstep (se 1 (by rfl) ⟨1328363, by rfl⟩ : syracuseStep 1771151 = 2656727) B2656727
theorem B1181327 : Blo 1180407 1181327 := bstep (se 1 (by rfl) ⟨885995, by rfl⟩ : syracuseStep 1181327 = 1771991) B1771991
theorem B1992377 : Blo 1180407 1992377 := bstep (se 2 (by rfl) ⟨747141, by rfl⟩ : syracuseStep 1992377 = 1494283) B1494283
theorem B1771193 : Blo 1180407 1771193 := bstep (se 2 (by rfl) ⟨664197, by rfl⟩ : syracuseStep 1771193 = 1328395) B1328395
theorem B1328827 : Blo 1180407 1328827 := bstep (se 1 (by rfl) ⟨996620, by rfl⟩ : syracuseStep 1328827 = 1993241) B1993241
theorem B1181371 : Blo 1180407 1181371 := bstep (se 1 (by rfl) ⟨886028, by rfl⟩ : syracuseStep 1181371 = 1772057) B1772057
theorem B1771271 : Blo 1180407 1771271 := bstep (se 1 (by rfl) ⟨1328453, by rfl⟩ : syracuseStep 1771271 = 2656907) B2656907
theorem B1181447 : Blo 1180407 1181447 := bstep (se 1 (by rfl) ⟨886085, by rfl⟩ : syracuseStep 1181447 = 1772171) B1772171
theorem B1181455 : Blo 1180407 1181455 := bstep (se 1 (by rfl) ⟨886091, by rfl⟩ : syracuseStep 1181455 = 1772183) B1772183
theorem B2991887 : Blo 1180407 2991887 := bstep (se 1 (by rfl) ⟨2243915, by rfl⟩ : syracuseStep 2991887 = 4487831) B4487831
theorem B6383393 : Blo 1180407 6383393 := bstep (se 2 (by rfl) ⟨2393772, by rfl⟩ : syracuseStep 6383393 = 4787545) B4787545
theorem B12764965 : Blo 1180407 12764965 := bstep (se 4 (by rfl) ⟨1196715, by rfl⟩ : syracuseStep 12764965 = 2393431) B2393431
theorem B2656043 : Blo 1180407 2656043 := bstep (se 1 (by rfl) ⟨1992032, by rfl⟩ : syracuseStep 2656043 = 3984065) B3984065
theorem B1771307 : Blo 1180407 1771307 := bstep (se 1 (by rfl) ⟨1328480, by rfl⟩ : syracuseStep 1771307 = 2656961) B2656961
theorem B1181499 : Blo 1180407 1181499 := bstep (se 1 (by rfl) ⟨886124, by rfl⟩ : syracuseStep 1181499 = 1772249) B1772249
theorem B5982011 : Blo 1180407 5982011 := bstep (se 1 (by rfl) ⟨4486508, by rfl⟩ : syracuseStep 5982011 = 8973017) B8973017
theorem B1771337 : Blo 1180407 1771337 := bstep (se 2 (by rfl) ⟨664251, by rfl⟩ : syracuseStep 1771337 = 1328503) B1328503
theorem B28747637 : Blo 1180407 28747637 := bstep (se 5 (by rfl) ⟨1347545, by rfl⟩ : syracuseStep 28747637 = 2695091) B2695091
theorem B1181575 : Blo 1180407 1181575 := bstep (se 1 (by rfl) ⟨886181, by rfl⟩ : syracuseStep 1181575 = 1772363) B1772363
theorem B1181583 : Blo 1180407 1181583 := bstep (se 1 (by rfl) ⟨886187, by rfl⟩ : syracuseStep 1181583 = 1772375) B1772375
theorem B4786073 : Blo 1180407 4786073 := bstep (se 2 (by rfl) ⟨1794777, by rfl⟩ : syracuseStep 4786073 = 3589555) B3589555
theorem B1771451 : Blo 1180407 1771451 := bstep (se 1 (by rfl) ⟨1328588, by rfl⟩ : syracuseStep 1771451 = 2657177) B2657177
theorem B1181627 : Blo 1180407 1181627 := bstep (se 1 (by rfl) ⟨886220, by rfl⟩ : syracuseStep 1181627 = 1772441) B1772441
theorem B5982173 : Blo 1180407 5982173 := bstep (se 3 (by rfl) ⟨1121657, by rfl⟩ : syracuseStep 5982173 = 2243315) B2243315
theorem B1771511 : Blo 1180407 1771511 := bstep (se 1 (by rfl) ⟨1328633, by rfl⟩ : syracuseStep 1771511 = 2657267) B2657267
theorem B1181703 : Blo 1180407 1181703 := bstep (se 1 (by rfl) ⟨886277, by rfl⟩ : syracuseStep 1181703 = 1772555) B1772555
theorem B1771535 : Blo 1180407 1771535 := bstep (se 1 (by rfl) ⟨1328651, by rfl⟩ : syracuseStep 1771535 = 2657303) B2657303
theorem B1181711 : Blo 1180407 1181711 := bstep (se 1 (by rfl) ⟨886283, by rfl⟩ : syracuseStep 1181711 = 1772567) B1772567
theorem B1771577 : Blo 1180407 1771577 := bstep (se 2 (by rfl) ⟨664341, by rfl⟩ : syracuseStep 1771577 = 1328683) B1328683
theorem B1181755 : Blo 1180407 1181755 := bstep (se 1 (by rfl) ⟨886316, by rfl⟩ : syracuseStep 1181755 = 1772633) B1772633
theorem B1771655 : Blo 1180407 1771655 := bstep (se 1 (by rfl) ⟨1328741, by rfl⟩ : syracuseStep 1771655 = 2657483) B2657483
theorem B1181831 : Blo 1180407 1181831 := bstep (se 1 (by rfl) ⟨886373, by rfl⟩ : syracuseStep 1181831 = 1772747) B1772747
theorem B1329295 : Blo 1180407 1329295 := bstep (se 1 (by rfl) ⟨996971, by rfl⟩ : syracuseStep 1329295 = 1993943) B1993943
theorem B1181839 : Blo 1180407 1181839 := bstep (se 1 (by rfl) ⟨886379, by rfl⟩ : syracuseStep 1181839 = 1772759) B1772759
theorem B2656403 : Blo 1180407 2656403 := bstep (se 1 (by rfl) ⟨1992302, by rfl⟩ : syracuseStep 2656403 = 3984605) B3984605
theorem B1771691 : Blo 1180407 1771691 := bstep (se 1 (by rfl) ⟨1328768, by rfl⟩ : syracuseStep 1771691 = 2657537) B2657537
theorem B8964269 : Blo 1180407 8964269 := bstep (se 3 (by rfl) ⟨1680800, by rfl⟩ : syracuseStep 8964269 = 3361601) B3361601
theorem B1181883 : Blo 1180407 1181883 := bstep (se 1 (by rfl) ⟨886412, by rfl⟩ : syracuseStep 1181883 = 1772825) B1772825
theorem B2656457 : Blo 1180407 2656457 := bstep (se 2 (by rfl) ⟨996171, by rfl⟩ : syracuseStep 2656457 = 1992343) B1992343
theorem B1771721 : Blo 1180407 1771721 := bstep (se 2 (by rfl) ⟨664395, by rfl⟩ : syracuseStep 1771721 = 1328791) B1328791
theorem B1181959 : Blo 1180407 1181959 := bstep (se 1 (by rfl) ⟨886469, by rfl⟩ : syracuseStep 1181959 = 1772939) B1772939
theorem B6473999 : Blo 1180407 6473999 := bstep (se 1 (by rfl) ⟨4855499, by rfl⟩ : syracuseStep 6473999 = 9710999) B9710999
theorem B1181967 : Blo 1180407 1181967 := bstep (se 1 (by rfl) ⟨886475, by rfl⟩ : syracuseStep 1181967 = 1772951) B1772951
theorem B5982497 : Blo 1180407 5982497 := bstep (se 2 (by rfl) ⟨2243436, by rfl⟩ : syracuseStep 5982497 = 4486873) B4486873
theorem B1771835 : Blo 1180407 1771835 := bstep (se 1 (by rfl) ⟨1328876, by rfl⟩ : syracuseStep 1771835 = 2657753) B2657753
theorem B1182011 : Blo 1180407 1182011 := bstep (se 1 (by rfl) ⟨886508, by rfl⟩ : syracuseStep 1182011 = 1773017) B1773017
theorem B1993079 : Blo 1180407 1993079 := bstep (se 1 (by rfl) ⟨1494809, by rfl⟩ : syracuseStep 1993079 = 2989619) B2989619
theorem B1771895 : Blo 1180407 1771895 := bstep (se 1 (by rfl) ⟨1328921, by rfl⟩ : syracuseStep 1771895 = 2657843) B2657843
theorem B1182087 : Blo 1180407 1182087 := bstep (se 1 (by rfl) ⟨886565, by rfl⟩ : syracuseStep 1182087 = 1773131) B1773131
theorem B1771919 : Blo 1180407 1771919 := bstep (se 1 (by rfl) ⟨1328939, by rfl⟩ : syracuseStep 1771919 = 2657879) B2657879
theorem B1182095 : Blo 1180407 1182095 := bstep (se 1 (by rfl) ⟨886571, by rfl⟩ : syracuseStep 1182095 = 1773143) B1773143
theorem B1771961 : Blo 1180407 1771961 := bstep (se 2 (by rfl) ⟨664485, by rfl⟩ : syracuseStep 1771961 = 1328971) B1328971
theorem B1182139 : Blo 1180407 1182139 := bstep (se 1 (by rfl) ⟨886604, by rfl⟩ : syracuseStep 1182139 = 1773209) B1773209
theorem B2992585 : Blo 1180407 2992585 := bstep (se 2 (by rfl) ⟨1122219, by rfl⟩ : syracuseStep 2992585 = 2244439) B2244439
theorem B1772039 : Blo 1180407 1772039 := bstep (se 1 (by rfl) ⟨1329029, by rfl⟩ : syracuseStep 1772039 = 2658059) B2658059
theorem B1182215 : Blo 1180407 1182215 := bstep (se 1 (by rfl) ⟨886661, by rfl⟩ : syracuseStep 1182215 = 1773323) B1773323
theorem B1182223 : Blo 1180407 1182223 := bstep (se 1 (by rfl) ⟨886667, by rfl⟩ : syracuseStep 1182223 = 1773335) B1773335
theorem B13445675 : Blo 1180407 13445675 := bstep (se 1 (by rfl) ⟨10084256, by rfl⟩ : syracuseStep 13445675 = 20168513) B20168513
theorem B2837035 : Blo 1180407 2837035 := bstep (se 1 (by rfl) ⟨2127776, by rfl⟩ : syracuseStep 2837035 = 4255553) B4255553
theorem B1772075 : Blo 1180407 1772075 := bstep (se 1 (by rfl) ⟨1329056, by rfl⟩ : syracuseStep 1772075 = 2658113) B2658113
theorem B1182267 : Blo 1180407 1182267 := bstep (se 1 (by rfl) ⟨886700, by rfl⟩ : syracuseStep 1182267 = 1773401) B1773401
theorem B1772105 : Blo 1180407 1772105 := bstep (se 2 (by rfl) ⟨664539, by rfl⟩ : syracuseStep 1772105 = 1329079) B1329079
theorem B2992727 : Blo 1180407 2992727 := bstep (se 1 (by rfl) ⟨2244545, by rfl⟩ : syracuseStep 2992727 = 4489091) B4489091
theorem B1329799 : Blo 1180407 1329799 := bstep (se 1 (by rfl) ⟨997349, by rfl⟩ : syracuseStep 1329799 = 1994699) B1994699
theorem B1182343 : Blo 1180407 1182343 := bstep (se 1 (by rfl) ⟨886757, by rfl⟩ : syracuseStep 1182343 = 1773515) B1773515
theorem B1182351 : Blo 1180407 1182351 := bstep (se 1 (by rfl) ⟨886763, by rfl⟩ : syracuseStep 1182351 = 1773527) B1773527
theorem B3033785 : Blo 1180407 3033785 := bstep (se 2 (by rfl) ⟨1137669, by rfl⟩ : syracuseStep 3033785 = 2275339) B2275339
theorem B1772219 : Blo 1180407 1772219 := bstep (se 1 (by rfl) ⟨1329164, by rfl⟩ : syracuseStep 1772219 = 2658329) B2658329
theorem B1182395 : Blo 1180407 1182395 := bstep (se 1 (by rfl) ⟨886796, by rfl⟩ : syracuseStep 1182395 = 1773593) B1773593
theorem B1772279 : Blo 1180407 1772279 := bstep (se 1 (by rfl) ⟨1329209, by rfl⟩ : syracuseStep 1772279 = 2658419) B2658419
theorem B1772303 : Blo 1180407 1772303 := bstep (se 1 (by rfl) ⟨1329227, by rfl⟩ : syracuseStep 1772303 = 2658455) B2658455
theorem B1772345 : Blo 1180407 1772345 := bstep (se 2 (by rfl) ⟨664629, by rfl⟩ : syracuseStep 1772345 = 1329259) B1329259
theorem B1993531 : Blo 1180407 1993531 := bstep (se 1 (by rfl) ⟨1495148, by rfl⟩ : syracuseStep 1993531 = 2990297) B2990297
theorem B2878267 : Blo 1180407 2878267 := bstep (se 1 (by rfl) ⟨2158700, by rfl⟩ : syracuseStep 2878267 = 4317401) B4317401
theorem B1329979 : Blo 1180407 1329979 := bstep (se 1 (by rfl) ⟨997484, by rfl⟩ : syracuseStep 1329979 = 1994969) B1994969
theorem B4787059 : Blo 1180407 4787059 := bstep (se 1 (by rfl) ⟨3590294, by rfl⟩ : syracuseStep 4787059 = 7180589) B7180589
theorem B2657159 : Blo 1180407 2657159 := bstep (se 1 (by rfl) ⟨1992869, by rfl⟩ : syracuseStep 2657159 = 3985739) B3985739
theorem B1772423 : Blo 1180407 1772423 := bstep (se 1 (by rfl) ⟨1329317, by rfl⟩ : syracuseStep 1772423 = 2658635) B2658635
theorem B3984281 : Blo 1180407 3984281 := bstep (se 2 (by rfl) ⟨1494105, by rfl⟩ : syracuseStep 3984281 = 2988211) B2988211
theorem B1772459 : Blo 1180407 1772459 := bstep (se 1 (by rfl) ⟨1329344, by rfl⟩ : syracuseStep 1772459 = 2658689) B2658689
theorem B1993673 : Blo 1180407 1993673 := bstep (se 2 (by rfl) ⟨747627, by rfl⟩ : syracuseStep 1993673 = 1495255) B1495255
theorem B1772489 : Blo 1180407 1772489 := bstep (se 2 (by rfl) ⟨664683, by rfl⟩ : syracuseStep 1772489 = 1329367) B1329367
theorem B5049373 : Blo 1180407 5049373 := bstep (se 3 (by rfl) ⟨946757, by rfl⟩ : syracuseStep 5049373 = 1893515) B1893515
theorem B2657339 : Blo 1180407 2657339 := bstep (se 1 (by rfl) ⟨1993004, by rfl⟩ : syracuseStep 2657339 = 3986009) B3986009
theorem B1772603 : Blo 1180407 1772603 := bstep (se 1 (by rfl) ⟨1329452, by rfl⟩ : syracuseStep 1772603 = 2658905) B2658905
theorem B13454423 : Blo 1180407 13454423 := bstep (se 1 (by rfl) ⟨10090817, by rfl⟩ : syracuseStep 13454423 = 20181635) B20181635
theorem B1772663 : Blo 1180407 1772663 := bstep (se 1 (by rfl) ⟨1329497, by rfl⟩ : syracuseStep 1772663 = 2658995) B2658995
theorem B1772687 : Blo 1180407 1772687 := bstep (se 1 (by rfl) ⟨1329515, by rfl⟩ : syracuseStep 1772687 = 2659031) B2659031
theorem B2657465 : Blo 1180407 2657465 := bstep (se 2 (by rfl) ⟨996549, by rfl⟩ : syracuseStep 2657465 = 1993099) B1993099
theorem B1772729 : Blo 1180407 1772729 := bstep (se 2 (by rfl) ⟨664773, by rfl⟩ : syracuseStep 1772729 = 1329547) B1329547
theorem B5983469 : Blo 1180407 5983469 := bstep (se 3 (by rfl) ⟨1121900, by rfl⟩ : syracuseStep 5983469 = 2243801) B2243801
theorem B1772807 : Blo 1180407 1772807 := bstep (se 1 (by rfl) ⟨1329605, by rfl⟩ : syracuseStep 1772807 = 2659211) B2659211
theorem B13634849 : Blo 1180407 13634849 := bstep (se 2 (by rfl) ⟨5113068, by rfl⟩ : syracuseStep 13634849 = 10226137) B10226137
theorem B1772843 : Blo 1180407 1772843 := bstep (se 1 (by rfl) ⟨1329632, by rfl⟩ : syracuseStep 1772843 = 2659265) B2659265
theorem B1772873 : Blo 1180407 1772873 := bstep (se 2 (by rfl) ⟨664827, by rfl⟩ : syracuseStep 1772873 = 1329655) B1329655
theorem B5049715 : Blo 1180407 5049715 := bstep (se 1 (by rfl) ⟨3787286, by rfl⟩ : syracuseStep 5049715 = 7574573) B7574573
theorem B5680529 : Blo 1180407 5680529 := bstep (se 2 (by rfl) ⟨2130198, by rfl⟩ : syracuseStep 5680529 = 4260397) B4260397
theorem B1772987 : Blo 1180407 1772987 := bstep (se 1 (by rfl) ⟨1329740, by rfl⟩ : syracuseStep 1772987 = 2659481) B2659481
theorem B1773047 : Blo 1180407 1773047 := bstep (se 1 (by rfl) ⟨1329785, by rfl⟩ : syracuseStep 1773047 = 2659571) B2659571
theorem B2657807 : Blo 1180407 2657807 := bstep (se 1 (by rfl) ⟨1993355, by rfl⟩ : syracuseStep 2657807 = 3986711) B3986711
theorem B1773071 : Blo 1180407 1773071 := bstep (se 1 (by rfl) ⟨1329803, by rfl⟩ : syracuseStep 1773071 = 2659607) B2659607
theorem B2657825 : Blo 1180407 2657825 := bstep (se 2 (by rfl) ⟨996684, by rfl⟩ : syracuseStep 2657825 = 1993369) B1993369
theorem B1773113 : Blo 1180407 1773113 := bstep (se 2 (by rfl) ⟨664917, by rfl⟩ : syracuseStep 1773113 = 1329835) B1329835
theorem B3984983 : Blo 1180407 3984983 := bstep (se 1 (by rfl) ⟨2988737, by rfl⟩ : syracuseStep 3984983 = 5977475) B5977475
theorem B1994375 : Blo 1180407 1994375 := bstep (se 1 (by rfl) ⟨1495781, by rfl⟩ : syracuseStep 1994375 = 2991563) B2991563
theorem B1773191 : Blo 1180407 1773191 := bstep (se 1 (by rfl) ⟨1329893, by rfl⟩ : syracuseStep 1773191 = 2659787) B2659787
theorem B1773227 : Blo 1180407 1773227 := bstep (se 1 (by rfl) ⟨1329920, by rfl⟩ : syracuseStep 1773227 = 2659841) B2659841
theorem B1773257 : Blo 1180407 1773257 := bstep (se 2 (by rfl) ⟨664971, by rfl⟩ : syracuseStep 1773257 = 1329943) B1329943
theorem B54529793 : Blo 1180407 54529793 := bstep (se 2 (by rfl) ⟨20448672, by rfl⟩ : syracuseStep 54529793 = 40897345) B40897345
theorem B3362593 : Blo 1180407 3362593 := bstep (se 2 (by rfl) ⟨1260972, by rfl⟩ : syracuseStep 3362593 = 2521945) B2521945
theorem B1773371 : Blo 1180407 1773371 := bstep (se 1 (by rfl) ⟨1330028, by rfl⟩ : syracuseStep 1773371 = 2660057) B2660057
theorem B18173765 : Blo 1180407 18173765 := bstep (se 4 (by rfl) ⟨1703790, by rfl⟩ : syracuseStep 18173765 = 3407581) B3407581
theorem B2658167 : Blo 1180407 2658167 := bstep (se 1 (by rfl) ⟨1993625, by rfl⟩ : syracuseStep 2658167 = 3987251) B3987251
theorem B1773431 : Blo 1180407 1773431 := bstep (se 1 (by rfl) ⟨1330073, by rfl⟩ : syracuseStep 1773431 = 2660147) B2660147
theorem B1773455 : Blo 1180407 1773455 := bstep (se 1 (by rfl) ⟨1330091, by rfl⟩ : syracuseStep 1773455 = 2660183) B2660183
theorem B2838419 : Blo 1180407 2838419 := bstep (se 1 (by rfl) ⟨2128814, by rfl⟩ : syracuseStep 2838419 = 4257629) B4257629
theorem B1773497 : Blo 1180407 1773497 := bstep (se 2 (by rfl) ⟨665061, by rfl⟩ : syracuseStep 1773497 = 1330123) B1330123
theorem B5976017 : Blo 1180407 5976017 := bstep (se 2 (by rfl) ⟨2241006, by rfl⟩ : syracuseStep 5976017 = 4482013) B4482013
theorem B1773575 : Blo 1180407 1773575 := bstep (se 1 (by rfl) ⟨1330181, by rfl⟩ : syracuseStep 1773575 = 2660363) B2660363
theorem B3190799 : Blo 1180407 3190799 := bstep (se 1 (by rfl) ⟨2393099, by rfl⟩ : syracuseStep 3190799 = 4786199) B4786199
theorem B5984279 : Blo 1180407 5984279 := bstep (se 1 (by rfl) ⟨4488209, by rfl⟩ : syracuseStep 5984279 = 8976419) B8976419
theorem B2658347 : Blo 1180407 2658347 := bstep (se 1 (by rfl) ⟨1993760, by rfl⟩ : syracuseStep 2658347 = 3987521) B3987521
theorem B1773611 : Blo 1180407 1773611 := bstep (se 1 (by rfl) ⟨1330208, by rfl⟩ : syracuseStep 1773611 = 2660417) B2660417
theorem B3985469 : Blo 1180407 3985469 := bstep (se 3 (by rfl) ⟨747275, by rfl⟩ : syracuseStep 3985469 = 1494551) B1494551
theorem B2879641 : Blo 1180407 2879641 := bstep (se 2 (by rfl) ⟨1079865, by rfl⟩ : syracuseStep 2879641 = 2159731) B2159731
theorem B3363083 : Blo 1180407 3363083 := bstep (se 1 (by rfl) ⟨2522312, by rfl⟩ : syracuseStep 3363083 = 5044625) B5044625
theorem B1995023 : Blo 1180407 1995023 := bstep (se 1 (by rfl) ⟨1496267, by rfl⟩ : syracuseStep 1995023 = 2992535) B2992535
theorem B3191069 : Blo 1180407 3191069 := bstep (se 3 (by rfl) ⟨598325, by rfl⟩ : syracuseStep 3191069 = 1196651) B1196651
theorem B5755283 : Blo 1180407 5755283 := bstep (se 1 (by rfl) ⟨4316462, by rfl⟩ : syracuseStep 5755283 = 8632925) B8632925
theorem B2658707 : Blo 1180407 2658707 := bstep (se 1 (by rfl) ⟨1994030, by rfl⟩ : syracuseStep 2658707 = 3988061) B3988061
theorem B2658761 : Blo 1180407 2658761 := bstep (se 2 (by rfl) ⟨997035, by rfl⟩ : syracuseStep 2658761 = 1994071) B1994071
theorem B3191329 : Blo 1180407 3191329 := bstep (se 2 (by rfl) ⟨1196748, by rfl⟩ : syracuseStep 3191329 = 2393497) B2393497
theorem B8966699 : Blo 1180407 8966699 := bstep (se 1 (by rfl) ⟨6725024, by rfl⟩ : syracuseStep 8966699 = 13450049) B13450049
theorem B2241083 : Blo 1180407 2241083 := bstep (se 1 (by rfl) ⟨1680812, by rfl⟩ : syracuseStep 2241083 = 3361625) B3361625
theorem B4485719 : Blo 1180407 4485719 := bstep (se 1 (by rfl) ⟨3364289, by rfl⟩ : syracuseStep 4485719 = 6728579) B6728579
theorem B3592961 : Blo 1180407 3592961 := bstep (se 2 (by rfl) ⟨1347360, by rfl⟩ : syracuseStep 3592961 = 2694721) B2694721
theorem B4789007 : Blo 1180407 4789007 := bstep (se 1 (by rfl) ⟨3591755, by rfl⟩ : syracuseStep 4789007 = 7183511) B7183511
theorem B3363869 : Blo 1180407 3363869 := bstep (se 3 (by rfl) ⟨630725, by rfl⟩ : syracuseStep 3363869 = 1261451) B1261451
theorem B2241569 : Blo 1180407 2241569 := bstep (se 2 (by rfl) ⟨840588, by rfl⟩ : syracuseStep 2241569 = 1681177) B1681177
theorem B4486205 : Blo 1180407 4486205 := bstep (se 3 (by rfl) ⟨841163, by rfl⟩ : syracuseStep 4486205 = 1682327) B1682327
theorem B8975447 : Blo 1180407 8975447 := bstep (se 1 (by rfl) ⟨6731585, by rfl⟩ : syracuseStep 8975447 = 13463171) B13463171
theorem B2659463 : Blo 1180407 2659463 := bstep (se 1 (by rfl) ⟨1994597, by rfl⟩ : syracuseStep 2659463 = 3989195) B3989195
theorem B8516897 : Blo 1180407 8516897 := bstep (se 2 (by rfl) ⟨3193836, by rfl⟩ : syracuseStep 8516897 = 6387673) B6387673
theorem B2659643 : Blo 1180407 2659643 := bstep (se 1 (by rfl) ⟨1994732, by rfl⟩ : syracuseStep 2659643 = 3989465) B3989465
theorem B2241911 : Blo 1180407 2241911 := bstep (se 1 (by rfl) ⟨1681433, by rfl⟩ : syracuseStep 2241911 = 3362867) B3362867
theorem B5387705 : Blo 1180407 5387705 := bstep (se 2 (by rfl) ⟨2020389, by rfl⟩ : syracuseStep 5387705 = 4040779) B4040779
theorem B3986873 : Blo 1180407 3986873 := bstep (se 2 (by rfl) ⟨1495077, by rfl⟩ : syracuseStep 3986873 = 2990155) B2990155
theorem B2659769 : Blo 1180407 2659769 := bstep (se 2 (by rfl) ⟨997413, by rfl⟩ : syracuseStep 2659769 = 1994827) B1994827
theorem B38311501 : Blo 1180407 38311501 := bstep (se 3 (by rfl) ⟨7183406, by rfl⟩ : syracuseStep 38311501 = 14366813) B14366813
theorem B4789847 : Blo 1180407 4789847 := bstep (se 1 (by rfl) ⟨3592385, by rfl⟩ : syracuseStep 4789847 = 7184771) B7184771
theorem B23033443 : Blo 1180407 23033443 := bstep (se 1 (by rfl) ⟨17275082, by rfl⟩ : syracuseStep 23033443 = 34550165) B34550165
theorem B2660111 : Blo 1180407 2660111 := bstep (se 1 (by rfl) ⟨1995083, by rfl⟩ : syracuseStep 2660111 = 3990167) B3990167
theorem B2660129 : Blo 1180407 2660129 := bstep (se 2 (by rfl) ⟨997548, by rfl⟩ : syracuseStep 2660129 = 1995097) B1995097
theorem B7567141 : Blo 1180407 7567141 := bstep (se 4 (by rfl) ⟨709419, by rfl⟩ : syracuseStep 7567141 = 1418839) B1418839
theorem B5978123 : Blo 1180407 5978123 := bstep (se 1 (by rfl) ⟨4483592, by rfl⟩ : syracuseStep 5978123 = 8967185) B8967185
theorem B3987467 : Blo 1180407 3987467 := bstep (se 1 (by rfl) ⟨2990600, by rfl⟩ : syracuseStep 3987467 = 5981201) B5981201
theorem B13645847 : Blo 1180407 13645847 := bstep (se 1 (by rfl) ⟨10234385, by rfl⟩ : syracuseStep 13645847 = 20468771) B20468771
theorem B3987575 : Blo 1180407 3987575 := bstep (se 1 (by rfl) ⟨2990681, by rfl⟩ : syracuseStep 3987575 = 5981363) B5981363
theorem B5978285 : Blo 1180407 5978285 := bstep (se 3 (by rfl) ⟨1120928, by rfl⟩ : syracuseStep 5978285 = 2241857) B2241857
theorem B1595707 : Blo 1180407 1595707 := bstep (se 1 (by rfl) ⟨1196780, by rfl⟩ : syracuseStep 1595707 = 2393561) B2393561
theorem B2128187 : Blo 1180407 2128187 := bstep (se 1 (by rfl) ⟨1596140, by rfl⟩ : syracuseStep 2128187 = 3192281) B3192281
theorem B16177553 : Blo 1180407 16177553 := bstep (se 2 (by rfl) ⟨6066582, by rfl⟩ : syracuseStep 16177553 = 12133165) B12133165
theorem B6732179 : Blo 1180407 6732179 := bstep (se 1 (by rfl) ⟨5049134, by rfl⟩ : syracuseStep 6732179 = 10098269) B10098269
theorem B4487633 : Blo 1180407 4487633 := bstep (se 2 (by rfl) ⟨1682862, by rfl⟩ : syracuseStep 4487633 = 3365725) B3365725
theorem B9583069 : Blo 1180407 9583069 := bstep (se 3 (by rfl) ⟨1796825, by rfl⟩ : syracuseStep 9583069 = 3593651) B3593651
theorem B2988697 : Blo 1180407 2988697 := bstep (se 2 (by rfl) ⟨1120761, by rfl⟩ : syracuseStep 2988697 = 2241523) B2241523
theorem B3988169 : Blo 1180407 3988169 := bstep (se 2 (by rfl) ⟨1495563, by rfl⟩ : syracuseStep 3988169 = 2991127) B2991127
theorem B2988859 : Blo 1180407 2988859 := bstep (se 1 (by rfl) ⟨2241644, by rfl⟩ : syracuseStep 2988859 = 4483289) B4483289
theorem B6732679 : Blo 1180407 6732679 := bstep (se 1 (by rfl) ⟨5049509, by rfl⟩ : syracuseStep 6732679 = 10099019) B10099019
theorem B2243513 : Blo 1180407 2243513 := bstep (se 2 (by rfl) ⟨841317, by rfl⟩ : syracuseStep 2243513 = 1682635) B1682635
theorem B2989001 : Blo 1180407 2989001 := bstep (se 2 (by rfl) ⟨1120875, by rfl⟩ : syracuseStep 2989001 = 2241751) B2241751
theorem B3365975 : Blo 1180407 3365975 := bstep (se 1 (by rfl) ⟨2524481, by rfl⟩ : syracuseStep 3365975 = 5048963) B5048963
theorem B2243855 : Blo 1180407 2243855 := bstep (se 1 (by rfl) ⟨1682891, by rfl⟩ : syracuseStep 2243855 = 3365783) B3365783
theorem B2989345 : Blo 1180407 2989345 := bstep (se 2 (by rfl) ⟨1121004, by rfl⟩ : syracuseStep 2989345 = 2242009) B2242009
theorem B1596745 : Blo 1180407 1596745 := bstep (se 2 (by rfl) ⟨598779, by rfl⟩ : syracuseStep 1596745 = 1197559) B1197559
theorem B11509085 : Blo 1180407 11509085 := bstep (se 3 (by rfl) ⟨2157953, by rfl⟩ : syracuseStep 11509085 = 4315907) B4315907
theorem B10091911 : Blo 1180407 10091911 := bstep (se 1 (by rfl) ⟨7568933, by rfl⟩ : syracuseStep 10091911 = 15137867) B15137867
theorem B3988871 : Blo 1180407 3988871 := bstep (se 1 (by rfl) ⟨2991653, by rfl⟩ : syracuseStep 3988871 = 5983307) B5983307
theorem B3030419 : Blo 1180407 3030419 := bstep (se 1 (by rfl) ⟨2272814, by rfl⟩ : syracuseStep 3030419 = 4545629) B4545629
theorem B13630979 : Blo 1180407 13630979 := bstep (se 1 (by rfl) ⟨10223234, by rfl⟩ : syracuseStep 13630979 = 20446469) B20446469
theorem B6471191 : Blo 1180407 6471191 := bstep (se 1 (by rfl) ⟨4853393, by rfl⟩ : syracuseStep 6471191 = 9706787) B9706787
theorem B5676587 : Blo 1180407 5676587 := bstep (se 1 (by rfl) ⟨4257440, by rfl⟩ : syracuseStep 5676587 = 8514881) B8514881
theorem B4259371 : Blo 1180407 4259371 := bstep (se 1 (by rfl) ⟨3194528, by rfl⟩ : syracuseStep 4259371 = 6389057) B6389057
theorem B6725207 : Blo 1180407 6725207 := bstep (se 1 (by rfl) ⟨5043905, by rfl⟩ : syracuseStep 6725207 = 10087811) B10087811
theorem B5979905 : Blo 1180407 5979905 := bstep (se 2 (by rfl) ⟨2242464, by rfl⟩ : syracuseStep 5979905 = 4484929) B4484929
theorem B3989249 : Blo 1180407 3989249 := bstep (se 2 (by rfl) ⟨1495968, by rfl⟩ : syracuseStep 3989249 = 2991937) B2991937
theorem B1261327 : Blo 1180407 1261327 := bstep (se 1 (by rfl) ⟨945995, by rfl⟩ : syracuseStep 1261327 = 1891991) B1891991
theorem B72720179 : Blo 1180407 72720179 := bstep (se 1 (by rfl) ⟨54540134, by rfl⟩ : syracuseStep 72720179 = 109080269) B109080269
theorem B1597243 : Blo 1180407 1597243 := bstep (se 1 (by rfl) ⟨1197932, by rfl⟩ : syracuseStep 1597243 = 2395865) B2395865
theorem B2989943 : Blo 1180407 2989943 := bstep (se 1 (by rfl) ⟨2242457, by rfl⟩ : syracuseStep 2989943 = 4484915) B4484915
theorem B13467545 : Blo 1180407 13467545 := bstep (se 2 (by rfl) ⟨5050329, by rfl⟩ : syracuseStep 13467545 = 10100659) B10100659
theorem B3366841 : Blo 1180407 3366841 := bstep (se 2 (by rfl) ⟨1262565, by rfl⟩ : syracuseStep 3366841 = 2525131) B2525131
theorem B3989519 : Blo 1180407 3989519 := bstep (se 1 (by rfl) ⟨2992139, by rfl⟩ : syracuseStep 3989519 = 5984279) B5984279
theorem B36388925 : Blo 1180407 36388925 := bstep (se 3 (by rfl) ⟨6822923, by rfl⟩ : syracuseStep 36388925 = 13645847) B13645847
theorem B2990479 : Blo 1180407 2990479 := bstep (se 1 (by rfl) ⟨2242859, by rfl⟩ : syracuseStep 2990479 = 4485719) B4485719
theorem B2523611 : Blo 1180407 2523611 := bstep (se 1 (by rfl) ⟨1892708, by rfl⟩ : syracuseStep 2523611 = 3785417) B3785417
theorem B9585211 : Blo 1180407 9585211 := bstep (se 1 (by rfl) ⟨7188908, by rfl⟩ : syracuseStep 9585211 = 14377817) B14377817
theorem B3990113 : Blo 1180407 3990113 := bstep (se 2 (by rfl) ⟨1496292, by rfl⟩ : syracuseStep 3990113 = 2992585) B2992585
theorem B2990803 : Blo 1180407 2990803 := bstep (se 1 (by rfl) ⟨2243102, by rfl⟩ : syracuseStep 2990803 = 4486205) B4486205
theorem B1180455 : Blo 1180407 1180455 := bstep (se 1 (by rfl) ⟨885341, by rfl⟩ : syracuseStep 1180455 = 1770683) B1770683
theorem B1180495 : Blo 1180407 1180495 := bstep (se 1 (by rfl) ⟨885371, by rfl⟩ : syracuseStep 1180495 = 1770743) B1770743
theorem B1180511 : Blo 1180407 1180511 := bstep (se 1 (by rfl) ⟨885383, by rfl⟩ : syracuseStep 1180511 = 1770767) B1770767
theorem B5677931 : Blo 1180407 5677931 := bstep (se 1 (by rfl) ⟨4258448, by rfl⟩ : syracuseStep 5677931 = 8516897) B8516897
theorem B1180539 : Blo 1180407 1180539 := bstep (se 1 (by rfl) ⟨885404, by rfl⟩ : syracuseStep 1180539 = 1770809) B1770809
theorem B1180591 : Blo 1180407 1180591 := bstep (se 1 (by rfl) ⟨885443, by rfl⟩ : syracuseStep 1180591 = 1770887) B1770887
theorem B2556847 : Blo 1180407 2556847 := bstep (se 1 (by rfl) ⟨1917635, by rfl⟩ : syracuseStep 2556847 = 3835271) B3835271
theorem B1180615 : Blo 1180407 1180615 := bstep (se 1 (by rfl) ⟨885461, by rfl⟩ : syracuseStep 1180615 = 1770923) B1770923
theorem B1180635 : Blo 1180407 1180635 := bstep (se 1 (by rfl) ⟨885476, by rfl⟩ : syracuseStep 1180635 = 1770953) B1770953
theorem B1180711 : Blo 1180407 1180711 := bstep (se 1 (by rfl) ⟨885533, by rfl⟩ : syracuseStep 1180711 = 1771067) B1771067
theorem B1180751 : Blo 1180407 1180751 := bstep (se 1 (by rfl) ⟨885563, by rfl⟩ : syracuseStep 1180751 = 1771127) B1771127
theorem B1180767 : Blo 1180407 1180767 := bstep (se 1 (by rfl) ⟨885575, by rfl⟩ : syracuseStep 1180767 = 1771151) B1771151
theorem B1328251 : Blo 1180407 1328251 := bstep (se 1 (by rfl) ⟨996188, by rfl⟩ : syracuseStep 1328251 = 1992377) B1992377
theorem B1180795 : Blo 1180407 1180795 := bstep (se 1 (by rfl) ⟨885596, by rfl⟩ : syracuseStep 1180795 = 1771193) B1771193
theorem B6382745 : Blo 1180407 6382745 := bstep (se 2 (by rfl) ⟨2393529, by rfl⟩ : syracuseStep 6382745 = 4787059) B4787059
theorem B1180847 : Blo 1180407 1180847 := bstep (se 1 (by rfl) ⟨885635, by rfl⟩ : syracuseStep 1180847 = 1771271) B1771271
theorem B1770695 : Blo 1180407 1770695 := bstep (se 1 (by rfl) ⟨1328021, by rfl⟩ : syracuseStep 1770695 = 2656043) B2656043
theorem B1180871 : Blo 1180407 1180871 := bstep (se 1 (by rfl) ⟨885653, by rfl⟩ : syracuseStep 1180871 = 1771307) B1771307
theorem B1180891 : Blo 1180407 1180891 := bstep (se 1 (by rfl) ⟨885668, by rfl⟩ : syracuseStep 1180891 = 1771337) B1771337
theorem B1180967 : Blo 1180407 1180967 := bstep (se 1 (by rfl) ⟨885725, by rfl⟩ : syracuseStep 1180967 = 1771451) B1771451
theorem B1181007 : Blo 1180407 1181007 := bstep (se 1 (by rfl) ⟨885755, by rfl⟩ : syracuseStep 1181007 = 1771511) B1771511
theorem B1181023 : Blo 1180407 1181023 := bstep (se 1 (by rfl) ⟨885767, by rfl⟩ : syracuseStep 1181023 = 1771535) B1771535
theorem B1770857 : Blo 1180407 1770857 := bstep (se 2 (by rfl) ⟨664071, by rfl⟩ : syracuseStep 1770857 = 1328143) B1328143
theorem B1181051 : Blo 1180407 1181051 := bstep (se 1 (by rfl) ⟨885788, by rfl⟩ : syracuseStep 1181051 = 1771577) B1771577
theorem B1181103 : Blo 1180407 1181103 := bstep (se 1 (by rfl) ⟨885827, by rfl⟩ : syracuseStep 1181103 = 1771655) B1771655
theorem B1770935 : Blo 1180407 1770935 := bstep (se 1 (by rfl) ⟨1328201, by rfl⟩ : syracuseStep 1770935 = 2656403) B2656403
theorem B1181127 : Blo 1180407 1181127 := bstep (se 1 (by rfl) ⟨885845, by rfl⟩ : syracuseStep 1181127 = 1771691) B1771691
theorem B1770971 : Blo 1180407 1770971 := bstep (se 1 (by rfl) ⟨1328228, by rfl⟩ : syracuseStep 1770971 = 2656457) B2656457
theorem B1181147 : Blo 1180407 1181147 := bstep (se 1 (by rfl) ⟨885860, by rfl⟩ : syracuseStep 1181147 = 1771721) B1771721
theorem B1418791 : Blo 1180407 1418791 := bstep (se 1 (by rfl) ⟨1064093, by rfl⟩ : syracuseStep 1418791 = 2128187) B2128187
theorem B1181223 : Blo 1180407 1181223 := bstep (se 1 (by rfl) ⟨885917, by rfl⟩ : syracuseStep 1181223 = 1771835) B1771835
theorem B1328719 : Blo 1180407 1328719 := bstep (se 1 (by rfl) ⟨996539, by rfl⟩ : syracuseStep 1328719 = 1993079) B1993079
theorem B1181263 : Blo 1180407 1181263 := bstep (se 1 (by rfl) ⟨885947, by rfl⟩ : syracuseStep 1181263 = 1771895) B1771895
theorem B1181279 : Blo 1180407 1181279 := bstep (se 1 (by rfl) ⟨885959, by rfl⟩ : syracuseStep 1181279 = 1771919) B1771919
theorem B1181307 : Blo 1180407 1181307 := bstep (se 1 (by rfl) ⟨885980, by rfl⟩ : syracuseStep 1181307 = 1771961) B1771961
theorem B2991755 : Blo 1180407 2991755 := bstep (se 1 (by rfl) ⟨2243816, by rfl⟩ : syracuseStep 2991755 = 4487633) B4487633
theorem B1181359 : Blo 1180407 1181359 := bstep (se 1 (by rfl) ⟨886019, by rfl⟩ : syracuseStep 1181359 = 1772039) B1772039
theorem B8963783 : Blo 1180407 8963783 := bstep (se 1 (by rfl) ⟨6722837, by rfl⟩ : syracuseStep 8963783 = 13445675) B13445675
theorem B1181383 : Blo 1180407 1181383 := bstep (se 1 (by rfl) ⟨886037, by rfl⟩ : syracuseStep 1181383 = 1772075) B1772075
theorem B1181403 : Blo 1180407 1181403 := bstep (se 1 (by rfl) ⟨886052, by rfl⟩ : syracuseStep 1181403 = 1772105) B1772105
theorem B4097785 : Blo 1180407 4097785 := bstep (se 2 (by rfl) ⟨1536669, by rfl⟩ : syracuseStep 4097785 = 3073339) B3073339
theorem B1181479 : Blo 1180407 1181479 := bstep (se 1 (by rfl) ⟨886109, by rfl⟩ : syracuseStep 1181479 = 1772219) B1772219
theorem B1181519 : Blo 1180407 1181519 := bstep (se 1 (by rfl) ⟨886139, by rfl⟩ : syracuseStep 1181519 = 1772279) B1772279
theorem B1181535 : Blo 1180407 1181535 := bstep (se 1 (by rfl) ⟨886151, by rfl⟩ : syracuseStep 1181535 = 1772303) B1772303
theorem B1181563 : Blo 1180407 1181563 := bstep (se 1 (by rfl) ⟨886172, by rfl⟩ : syracuseStep 1181563 = 1772345) B1772345
theorem B2525089 : Blo 1180407 2525089 := bstep (se 2 (by rfl) ⟨946908, by rfl⟩ : syracuseStep 2525089 = 1893817) B1893817
theorem B1771439 : Blo 1180407 1771439 := bstep (se 1 (by rfl) ⟨1328579, by rfl⟩ : syracuseStep 1771439 = 2657159) B2657159
theorem B1181615 : Blo 1180407 1181615 := bstep (se 1 (by rfl) ⟨886211, by rfl⟩ : syracuseStep 1181615 = 1772423) B1772423
theorem B2656187 : Blo 1180407 2656187 := bstep (se 1 (by rfl) ⟨1992140, by rfl⟩ : syracuseStep 2656187 = 3984281) B3984281
theorem B1181639 : Blo 1180407 1181639 := bstep (se 1 (by rfl) ⟨886229, by rfl⟩ : syracuseStep 1181639 = 1772459) B1772459
theorem B1992667 : Blo 1180407 1992667 := bstep (se 1 (by rfl) ⟨1494500, by rfl⟩ : syracuseStep 1992667 = 2989001) B2989001
theorem B1329115 : Blo 1180407 1329115 := bstep (se 1 (by rfl) ⟨996836, by rfl⟩ : syracuseStep 1329115 = 1993673) B1993673
theorem B1181659 : Blo 1180407 1181659 := bstep (se 1 (by rfl) ⟨886244, by rfl⟩ : syracuseStep 1181659 = 1772489) B1772489
theorem B1771529 : Blo 1180407 1771529 := bstep (se 2 (by rfl) ⟨664323, by rfl⟩ : syracuseStep 1771529 = 1328647) B1328647
theorem B1771559 : Blo 1180407 1771559 := bstep (se 1 (by rfl) ⟨1328669, by rfl⟩ : syracuseStep 1771559 = 2657339) B2657339
theorem B1181735 : Blo 1180407 1181735 := bstep (se 1 (by rfl) ⟨886301, by rfl⟩ : syracuseStep 1181735 = 1772603) B1772603
theorem B2656313 : Blo 1180407 2656313 := bstep (se 2 (by rfl) ⟨996117, by rfl⟩ : syracuseStep 2656313 = 1992235) B1992235
theorem B5679161 : Blo 1180407 5679161 := bstep (se 2 (by rfl) ⟨2129685, by rfl⟩ : syracuseStep 5679161 = 4259371) B4259371
theorem B1181775 : Blo 1180407 1181775 := bstep (se 1 (by rfl) ⟨886331, by rfl⟩ : syracuseStep 1181775 = 1772663) B1772663
theorem B1181791 : Blo 1180407 1181791 := bstep (se 1 (by rfl) ⟨886343, by rfl⟩ : syracuseStep 1181791 = 1772687) B1772687
theorem B1771643 : Blo 1180407 1771643 := bstep (se 1 (by rfl) ⟨1328732, by rfl⟩ : syracuseStep 1771643 = 2657465) B2657465
theorem B1181819 : Blo 1180407 1181819 := bstep (se 1 (by rfl) ⟨886364, by rfl⟩ : syracuseStep 1181819 = 1772729) B1772729
theorem B1181871 : Blo 1180407 1181871 := bstep (se 1 (by rfl) ⟨886403, by rfl⟩ : syracuseStep 1181871 = 1772807) B1772807
theorem B1181895 : Blo 1180407 1181895 := bstep (se 1 (by rfl) ⟨886421, by rfl⟩ : syracuseStep 1181895 = 1772843) B1772843
theorem B1181915 : Blo 1180407 1181915 := bstep (se 1 (by rfl) ⟨886436, by rfl⟩ : syracuseStep 1181915 = 1772873) B1772873
theorem B1771769 : Blo 1180407 1771769 := bstep (se 2 (by rfl) ⟨664413, by rfl⟩ : syracuseStep 1771769 = 1328827) B1328827
theorem B3787019 : Blo 1180407 3787019 := bstep (se 1 (by rfl) ⟨2840264, by rfl⟩ : syracuseStep 3787019 = 5680529) B5680529
theorem B1181991 : Blo 1180407 1181991 := bstep (se 1 (by rfl) ⟨886493, by rfl⟩ : syracuseStep 1181991 = 1772987) B1772987
theorem B1182031 : Blo 1180407 1182031 := bstep (se 1 (by rfl) ⟨886523, by rfl⟩ : syracuseStep 1182031 = 1773047) B1773047
theorem B9087319 : Blo 1180407 9087319 := bstep (se 1 (by rfl) ⟨6815489, by rfl⟩ : syracuseStep 9087319 = 13630979) B13630979
theorem B1771871 : Blo 1180407 1771871 := bstep (se 1 (by rfl) ⟨1328903, by rfl⟩ : syracuseStep 1771871 = 2657807) B2657807
theorem B1182047 : Blo 1180407 1182047 := bstep (se 1 (by rfl) ⟨886535, by rfl⟩ : syracuseStep 1182047 = 1773071) B1773071
theorem B1681769 : Blo 1180407 1681769 := bstep (se 2 (by rfl) ⟨630663, by rfl⟩ : syracuseStep 1681769 = 1261327) B1261327
theorem B1771883 : Blo 1180407 1771883 := bstep (se 1 (by rfl) ⟨1328912, by rfl⟩ : syracuseStep 1771883 = 2657825) B2657825
theorem B1182075 : Blo 1180407 1182075 := bstep (se 1 (by rfl) ⟨886556, by rfl⟩ : syracuseStep 1182075 = 1773113) B1773113
theorem B4483457 : Blo 1180407 4483457 := bstep (se 2 (by rfl) ⟨1681296, by rfl⟩ : syracuseStep 4483457 = 3362593) B3362593
theorem B2656655 : Blo 1180407 2656655 := bstep (se 1 (by rfl) ⟨1992491, by rfl⟩ : syracuseStep 2656655 = 3984983) B3984983
theorem B4483471 : Blo 1180407 4483471 := bstep (se 1 (by rfl) ⟨3362603, by rfl⟩ : syracuseStep 4483471 = 6725207) B6725207
theorem B1329583 : Blo 1180407 1329583 := bstep (se 1 (by rfl) ⟨997187, by rfl⟩ : syracuseStep 1329583 = 1994375) B1994375
theorem B1182127 : Blo 1180407 1182127 := bstep (se 1 (by rfl) ⟨886595, by rfl⟩ : syracuseStep 1182127 = 1773191) B1773191
theorem B1182151 : Blo 1180407 1182151 := bstep (se 1 (by rfl) ⟨886613, by rfl⟩ : syracuseStep 1182151 = 1773227) B1773227
theorem B1182171 : Blo 1180407 1182171 := bstep (se 1 (by rfl) ⟨886628, by rfl⟩ : syracuseStep 1182171 = 1773257) B1773257
theorem B1182247 : Blo 1180407 1182247 := bstep (se 1 (by rfl) ⟨886685, by rfl⟩ : syracuseStep 1182247 = 1773371) B1773371
theorem B1993295 : Blo 1180407 1993295 := bstep (se 1 (by rfl) ⟨1494971, by rfl⟩ : syracuseStep 1993295 = 2989943) B2989943
theorem B1772111 : Blo 1180407 1772111 := bstep (se 1 (by rfl) ⟨1329083, by rfl⟩ : syracuseStep 1772111 = 2658167) B2658167
theorem B1182287 : Blo 1180407 1182287 := bstep (se 1 (by rfl) ⟨886715, by rfl⟩ : syracuseStep 1182287 = 1773431) B1773431
theorem B1182303 : Blo 1180407 1182303 := bstep (se 1 (by rfl) ⟨886727, by rfl⟩ : syracuseStep 1182303 = 1773455) B1773455
theorem B1182331 : Blo 1180407 1182331 := bstep (se 1 (by rfl) ⟨886748, by rfl⟩ : syracuseStep 1182331 = 1773497) B1773497
theorem B3984011 : Blo 1180407 3984011 := bstep (se 1 (by rfl) ⟨2988008, by rfl⟩ : syracuseStep 3984011 = 5976017) B5976017
theorem B1182383 : Blo 1180407 1182383 := bstep (se 1 (by rfl) ⟨886787, by rfl⟩ : syracuseStep 1182383 = 1773575) B1773575
theorem B1772231 : Blo 1180407 1772231 := bstep (se 1 (by rfl) ⟨1329173, by rfl⟩ : syracuseStep 1772231 = 2658347) B2658347
theorem B1182407 : Blo 1180407 1182407 := bstep (se 1 (by rfl) ⟨886805, by rfl⟩ : syracuseStep 1182407 = 1773611) B1773611
theorem B2656979 : Blo 1180407 2656979 := bstep (se 1 (by rfl) ⟨1992734, by rfl⟩ : syracuseStep 2656979 = 3985469) B3985469
theorem B2992889 : Blo 1180407 2992889 := bstep (se 2 (by rfl) ⟨1122333, by rfl⟩ : syracuseStep 2992889 = 2244667) B2244667
theorem B1330015 : Blo 1180407 1330015 := bstep (se 1 (by rfl) ⟨997511, by rfl⟩ : syracuseStep 1330015 = 1995023) B1995023
theorem B1772393 : Blo 1180407 1772393 := bstep (se 2 (by rfl) ⟨664647, by rfl⟩ : syracuseStep 1772393 = 1329295) B1329295
theorem B1796971 : Blo 1180407 1796971 := bstep (se 1 (by rfl) ⟨1347728, by rfl⟩ : syracuseStep 1796971 = 2695457) B2695457
theorem B25537463 : Blo 1180407 25537463 := bstep (se 1 (by rfl) ⟨19153097, by rfl⟩ : syracuseStep 25537463 = 38306195) B38306195
theorem B3836855 : Blo 1180407 3836855 := bstep (se 1 (by rfl) ⟨2877641, by rfl⟩ : syracuseStep 3836855 = 5755283) B5755283
theorem B1772471 : Blo 1180407 1772471 := bstep (se 1 (by rfl) ⟨1329353, by rfl⟩ : syracuseStep 1772471 = 2658707) B2658707
theorem B1772507 : Blo 1180407 1772507 := bstep (se 1 (by rfl) ⟨1329380, by rfl⟩ : syracuseStep 1772507 = 2658761) B2658761
theorem B1494055 : Blo 1180407 1494055 := bstep (se 1 (by rfl) ⟨1120541, by rfl⟩ : syracuseStep 1494055 = 2241083) B2241083
theorem B2395307 : Blo 1180407 2395307 := bstep (se 1 (by rfl) ⟨1796480, by rfl⟩ : syracuseStep 2395307 = 3592961) B3592961
theorem B1494379 : Blo 1180407 1494379 := bstep (se 1 (by rfl) ⟨1120784, by rfl⟩ : syracuseStep 1494379 = 2241569) B2241569
theorem B4255105 : Blo 1180407 4255105 := bstep (se 2 (by rfl) ⟨1595664, by rfl⟩ : syracuseStep 4255105 = 3191329) B3191329
theorem B5983631 : Blo 1180407 5983631 := bstep (se 1 (by rfl) ⟨4487723, by rfl⟩ : syracuseStep 5983631 = 8975447) B8975447
theorem B36359597 : Blo 1180407 36359597 := bstep (se 3 (by rfl) ⟨6817424, by rfl⟩ : syracuseStep 36359597 = 13634849) B13634849
theorem B1994159 : Blo 1180407 1994159 := bstep (se 1 (by rfl) ⟨1495619, by rfl⟩ : syracuseStep 1994159 = 2991239) B2991239
theorem B1772975 : Blo 1180407 1772975 := bstep (se 1 (by rfl) ⟨1329731, by rfl⟩ : syracuseStep 1772975 = 2659463) B2659463
theorem B1773065 : Blo 1180407 1773065 := bstep (se 2 (by rfl) ⟨664899, by rfl⟩ : syracuseStep 1773065 = 1329799) B1329799
theorem B3984929 : Blo 1180407 3984929 := bstep (se 2 (by rfl) ⟨1494348, by rfl⟩ : syracuseStep 3984929 = 2988697) B2988697
theorem B1773095 : Blo 1180407 1773095 := bstep (se 1 (by rfl) ⟨1329821, by rfl⟩ : syracuseStep 1773095 = 2659643) B2659643
theorem B30690893 : Blo 1180407 30690893 := bstep (se 3 (by rfl) ⟨5754542, by rfl⟩ : syracuseStep 30690893 = 11509085) B11509085
theorem B1494607 : Blo 1180407 1494607 := bstep (se 1 (by rfl) ⟨1120955, by rfl⟩ : syracuseStep 1494607 = 2241911) B2241911
theorem B3591803 : Blo 1180407 3591803 := bstep (se 1 (by rfl) ⟨2693852, by rfl⟩ : syracuseStep 3591803 = 5387705) B5387705
theorem B2657915 : Blo 1180407 2657915 := bstep (se 1 (by rfl) ⟨1993436, by rfl⟩ : syracuseStep 2657915 = 3986873) B3986873
theorem B1773179 : Blo 1180407 1773179 := bstep (se 1 (by rfl) ⟨1329884, by rfl⟩ : syracuseStep 1773179 = 2659769) B2659769
theorem B4484747 : Blo 1180407 4484747 := bstep (se 1 (by rfl) ⟨3363560, by rfl⟩ : syracuseStep 4484747 = 6727121) B6727121
theorem B7565015 : Blo 1180407 7565015 := bstep (se 1 (by rfl) ⟨5673761, by rfl⟩ : syracuseStep 7565015 = 11347523) B11347523
theorem B8081117 : Blo 1180407 8081117 := bstep (se 3 (by rfl) ⟨1515209, by rfl⟩ : syracuseStep 8081117 = 3030419) B3030419
theorem B3985145 : Blo 1180407 3985145 := bstep (se 2 (by rfl) ⟨1494429, by rfl⟩ : syracuseStep 3985145 = 2988859) B2988859
theorem B2658041 : Blo 1180407 2658041 := bstep (se 2 (by rfl) ⟨996765, by rfl⟩ : syracuseStep 2658041 = 1993531) B1993531
theorem B3837689 : Blo 1180407 3837689 := bstep (se 2 (by rfl) ⟨1439133, by rfl⟩ : syracuseStep 3837689 = 2878267) B2878267
theorem B1683193 : Blo 1180407 1683193 := bstep (se 2 (by rfl) ⟨631197, by rfl⟩ : syracuseStep 1683193 = 1262395) B1262395
theorem B1773305 : Blo 1180407 1773305 := bstep (se 2 (by rfl) ⟨664989, by rfl⟩ : syracuseStep 1773305 = 1329979) B1329979
theorem B1994591 : Blo 1180407 1994591 := bstep (se 1 (by rfl) ⟨1495943, by rfl⟩ : syracuseStep 1994591 = 2991887) B2991887
theorem B1773407 : Blo 1180407 1773407 := bstep (se 1 (by rfl) ⟨1330055, by rfl⟩ : syracuseStep 1773407 = 2660111) B2660111
theorem B4255595 : Blo 1180407 4255595 := bstep (se 1 (by rfl) ⟨3191696, by rfl⟩ : syracuseStep 4255595 = 6383393) B6383393
theorem B1773419 : Blo 1180407 1773419 := bstep (se 1 (by rfl) ⟨1330064, by rfl⟩ : syracuseStep 1773419 = 2660129) B2660129
theorem B6729581 : Blo 1180407 6729581 := bstep (se 3 (by rfl) ⟨1261796, by rfl⟩ : syracuseStep 6729581 = 2523593) B2523593
theorem B19165091 : Blo 1180407 19165091 := bstep (se 1 (by rfl) ⟨14373818, by rfl⟩ : syracuseStep 19165091 = 28747637) B28747637
theorem B3190715 : Blo 1180407 3190715 := bstep (se 1 (by rfl) ⟨2393036, by rfl⟩ : syracuseStep 3190715 = 4786073) B4786073
theorem B245542873 : Blo 1180407 245542873 := bstep (se 2 (by rfl) ⟨92078577, by rfl⟩ : syracuseStep 245542873 = 184157155) B184157155
theorem B3985415 : Blo 1180407 3985415 := bstep (se 1 (by rfl) ⟨2989061, by rfl⟩ : syracuseStep 3985415 = 5978123) B5978123
theorem B2658311 : Blo 1180407 2658311 := bstep (se 1 (by rfl) ⟨1993733, by rfl⟩ : syracuseStep 2658311 = 3987467) B3987467
theorem B17256509 : Blo 1180407 17256509 := bstep (se 3 (by rfl) ⟨3235595, by rfl⟩ : syracuseStep 17256509 = 6471191) B6471191
theorem B2658383 : Blo 1180407 2658383 := bstep (se 1 (by rfl) ⟨1993787, by rfl⟩ : syracuseStep 2658383 = 3987575) B3987575
theorem B5976179 : Blo 1180407 5976179 := bstep (se 1 (by rfl) ⟨4482134, by rfl⟩ : syracuseStep 5976179 = 8964269) B8964269
theorem B3985523 : Blo 1180407 3985523 := bstep (se 1 (by rfl) ⟨2989142, by rfl⟩ : syracuseStep 3985523 = 5978285) B5978285
theorem B32354477 : Blo 1180407 32354477 := bstep (se 3 (by rfl) ⟨6066464, by rfl⟩ : syracuseStep 32354477 = 12132929) B12132929
theorem B10785035 : Blo 1180407 10785035 := bstep (se 1 (by rfl) ⟨8088776, by rfl⟩ : syracuseStep 10785035 = 16177553) B16177553
theorem B3985793 : Blo 1180407 3985793 := bstep (se 2 (by rfl) ⟨1494672, by rfl⟩ : syracuseStep 3985793 = 2989345) B2989345
theorem B8515973 : Blo 1180407 8515973 := bstep (se 4 (by rfl) ⟨798372, by rfl⟩ : syracuseStep 8515973 = 1596745) B1596745
theorem B1995151 : Blo 1180407 1995151 := bstep (se 1 (by rfl) ⟨1496363, by rfl⟩ : syracuseStep 1995151 = 2992727) B2992727
theorem B2658779 : Blo 1180407 2658779 := bstep (se 1 (by rfl) ⟨1994084, by rfl⟩ : syracuseStep 2658779 = 3988169) B3988169
theorem B8090093 : Blo 1180407 8090093 := bstep (se 3 (by rfl) ⟨1516892, by rfl⟩ : syracuseStep 8090093 = 3033785) B3033785
theorem B13455881 : Blo 1180407 13455881 := bstep (se 2 (by rfl) ⟨5045955, by rfl⟩ : syracuseStep 13455881 = 10091911) B10091911
theorem B2241121 : Blo 1180407 2241121 := bstep (se 2 (by rfl) ⟨840420, by rfl⟩ : syracuseStep 2241121 = 1680841) B1680841
theorem B1495675 : Blo 1180407 1495675 := bstep (se 1 (by rfl) ⟨1121756, by rfl⟩ : syracuseStep 1495675 = 2243513) B2243513
theorem B51082001 : Blo 1180407 51082001 := bstep (se 2 (by rfl) ⟨19155750, by rfl⟩ : syracuseStep 51082001 = 38311501) B38311501
theorem B1495903 : Blo 1180407 1495903 := bstep (se 1 (by rfl) ⟨1121927, by rfl⟩ : syracuseStep 1495903 = 2243855) B2243855
theorem B2659247 : Blo 1180407 2659247 := bstep (se 1 (by rfl) ⟨1994435, by rfl⟩ : syracuseStep 2659247 = 3988871) B3988871
theorem B17019953 : Blo 1180407 17019953 := bstep (se 2 (by rfl) ⟨6382482, by rfl⟩ : syracuseStep 17019953 = 12764965) B12764965
theorem B10089521 : Blo 1180407 10089521 := bstep (se 2 (by rfl) ⟨3783570, by rfl⟩ : syracuseStep 10089521 = 7567141) B7567141
theorem B36353195 : Blo 1180407 36353195 := bstep (se 1 (by rfl) ⟨27264896, by rfl⟩ : syracuseStep 36353195 = 54529793) B54529793
theorem B3986603 : Blo 1180407 3986603 := bstep (se 1 (by rfl) ⟨2989952, by rfl⟩ : syracuseStep 3986603 = 5979905) B5979905
theorem B2659499 : Blo 1180407 2659499 := bstep (se 1 (by rfl) ⟨1994624, by rfl⟩ : syracuseStep 2659499 = 3989249) B3989249
theorem B8508797 : Blo 1180407 8508797 := bstep (se 3 (by rfl) ⟨1595399, by rfl⟩ : syracuseStep 8508797 = 3190799) B3190799
theorem B5985737 : Blo 1180407 5985737 := bstep (se 2 (by rfl) ⟨2244651, by rfl⟩ : syracuseStep 5985737 = 4489303) B4489303
theorem B2242055 : Blo 1180407 2242055 := bstep (se 1 (by rfl) ⟨1681541, by rfl⟩ : syracuseStep 2242055 = 3363083) B3363083
theorem B3593737 : Blo 1180407 3593737 := bstep (se 2 (by rfl) ⟨1347651, by rfl⟩ : syracuseStep 3593737 = 2695303) B2695303
theorem B2127379 : Blo 1180407 2127379 := bstep (se 1 (by rfl) ⟨1595534, by rfl⟩ : syracuseStep 2127379 = 3191069) B3191069
theorem B3839521 : Blo 1180407 3839521 := bstep (se 2 (by rfl) ⟨1439820, by rfl⟩ : syracuseStep 3839521 = 2879641) B2879641
theorem B8975933 : Blo 1180407 8975933 := bstep (se 3 (by rfl) ⟨1682987, by rfl⟩ : syracuseStep 8975933 = 3365975) B3365975
theorem B3364541 : Blo 1180407 3364541 := bstep (se 3 (by rfl) ⟨630851, by rfl⟩ : syracuseStep 3364541 = 1261703) B1261703
theorem B5977799 : Blo 1180407 5977799 := bstep (se 1 (by rfl) ⟨4483349, by rfl⟩ : syracuseStep 5977799 = 8966699) B8966699
theorem B3987143 : Blo 1180407 3987143 := bstep (se 1 (by rfl) ⟨2990357, by rfl⟩ : syracuseStep 3987143 = 5980715) B5980715
theorem B2660039 : Blo 1180407 2660039 := bstep (se 1 (by rfl) ⟨1995029, by rfl⟩ : syracuseStep 2660039 = 3990059) B3990059
theorem B17028953 : Blo 1180407 17028953 := bstep (se 2 (by rfl) ⟨6385857, by rfl⟩ : syracuseStep 17028953 = 12771715) B12771715
theorem B3192671 : Blo 1180407 3192671 := bstep (se 1 (by rfl) ⟨2394503, by rfl⟩ : syracuseStep 3192671 = 4789007) B4789007
theorem B3594091 : Blo 1180407 3594091 := bstep (se 1 (by rfl) ⟨2695568, by rfl⟩ : syracuseStep 3594091 = 5391137) B5391137
theorem B12777425 : Blo 1180407 12777425 := bstep (se 2 (by rfl) ⟨4791534, by rfl⟩ : syracuseStep 12777425 = 9583069) B9583069
theorem B2242579 : Blo 1180407 2242579 := bstep (se 1 (by rfl) ⟨1681934, by rfl⟩ : syracuseStep 2242579 = 3363869) B3363869
theorem B3782713 : Blo 1180407 3782713 := bstep (se 2 (by rfl) ⟨1418517, by rfl⟩ : syracuseStep 3782713 = 2837035) B2837035
theorem B3193231 : Blo 1180407 3193231 := bstep (se 1 (by rfl) ⟨2394923, by rfl⟩ : syracuseStep 3193231 = 4789847) B4789847
theorem B8976905 : Blo 1180407 8976905 := bstep (se 2 (by rfl) ⟨3366339, by rfl⟩ : syracuseStep 8976905 = 6732679) B6732679
theorem B3988007 : Blo 1180407 3988007 := bstep (se 1 (by rfl) ⟨2991005, by rfl⟩ : syracuseStep 3988007 = 5982011) B5982011
theorem B3988115 : Blo 1180407 3988115 := bstep (se 1 (by rfl) ⟨2991086, by rfl⟩ : syracuseStep 3988115 = 5982173) B5982173
theorem B6732497 : Blo 1180407 6732497 := bstep (se 2 (by rfl) ⟨2524686, by rfl⟩ : syracuseStep 6732497 = 5049373) B5049373
theorem B4315999 : Blo 1180407 4315999 := bstep (se 1 (by rfl) ⟨3236999, by rfl⟩ : syracuseStep 4315999 = 6473999) B6473999
theorem B3988331 : Blo 1180407 3988331 := bstep (se 1 (by rfl) ⟨2991248, by rfl⟩ : syracuseStep 3988331 = 5982497) B5982497
theorem B3988385 : Blo 1180407 3988385 := bstep (se 2 (by rfl) ⟨1495644, by rfl⟩ : syracuseStep 3988385 = 2991289) B2991289
theorem B4488119 : Blo 1180407 4488119 := bstep (se 1 (by rfl) ⟨3366089, by rfl⟩ : syracuseStep 4488119 = 6732179) B6732179
theorem B8510437 : Blo 1180407 8510437 := bstep (se 4 (by rfl) ⟨797853, by rfl⟩ : syracuseStep 8510437 = 1595707) B1595707
theorem B6732953 : Blo 1180407 6732953 := bstep (se 2 (by rfl) ⟨2524857, by rfl⟩ : syracuseStep 6732953 = 5049715) B5049715
theorem B14572889 : Blo 1180407 14572889 := bstep (se 2 (by rfl) ⟨5464833, by rfl⟩ : syracuseStep 14572889 = 10929667) B10929667
theorem B8969615 : Blo 1180407 8969615 := bstep (se 1 (by rfl) ⟨6727211, by rfl⟩ : syracuseStep 8969615 = 13454423) B13454423
theorem B30711257 : Blo 1180407 30711257 := bstep (se 2 (by rfl) ⟨11516721, by rfl⟩ : syracuseStep 30711257 = 23033443) B23033443
theorem B3988979 : Blo 1180407 3988979 := bstep (se 1 (by rfl) ⟨2991734, by rfl⟩ : syracuseStep 3988979 = 5983469) B5983469
theorem B48463373 : Blo 1180407 48463373 := bstep (se 3 (by rfl) ⟨9086882, by rfl⟩ : syracuseStep 48463373 = 18173765) B18173765
theorem B3784391 : Blo 1180407 3784391 := bstep (se 1 (by rfl) ⟨2838293, by rfl⟩ : syracuseStep 3784391 = 5676587) B5676587
theorem B2129657 : Blo 1180407 2129657 := bstep (se 2 (by rfl) ⟨798621, by rfl⟩ : syracuseStep 2129657 = 1597243) B1597243
theorem B48480119 : Blo 1180407 48480119 := bstep (se 1 (by rfl) ⟨36360089, by rfl⟩ : syracuseStep 48480119 = 72720179) B72720179
theorem B4489121 : Blo 1180407 4489121 := bstep (se 2 (by rfl) ⟨1683420, by rfl⟩ : syracuseStep 4489121 = 3366841) B3366841
theorem B1892279 : Blo 1180407 1892279 := bstep (se 1 (by rfl) ⟨1419209, by rfl⟩ : syracuseStep 1892279 = 2838419) B2838419
theorem B8978363 : Blo 1180407 8978363 := bstep (se 1 (by rfl) ⟨6733772, by rfl⟩ : syracuseStep 8978363 = 13467545) B13467545
theorem B2990105 : Blo 1180407 2990105 := bstep (se 2 (by rfl) ⟨1121289, by rfl⟩ : syracuseStep 2990105 = 2242579) B2242579
theorem B21569651 : Blo 1180407 21569651 := bstep (se 1 (by rfl) ⟨16177238, by rfl⟩ : syracuseStep 21569651 = 32354477) B32354477
theorem B8970587 : Blo 1180407 8970587 := bstep (se 1 (by rfl) ⟨6727940, by rfl⟩ : syracuseStep 8970587 = 13455881) B13455881
theorem B12116425 : Blo 1180407 12116425 := bstep (se 2 (by rfl) ⟨4543659, by rfl⟩ : syracuseStep 12116425 = 9087319) B9087319
theorem B34054667 : Blo 1180407 34054667 := bstep (se 1 (by rfl) ⟨25541000, by rfl⟩ : syracuseStep 34054667 = 51082001) B51082001
theorem B3785287 : Blo 1180407 3785287 := bstep (se 1 (by rfl) ⟨2838965, by rfl⟩ : syracuseStep 3785287 = 5677931) B5677931
theorem B11346635 : Blo 1180407 11346635 := bstep (se 1 (by rfl) ⟨8509976, by rfl⟩ : syracuseStep 11346635 = 17019953) B17019953
theorem B6726347 : Blo 1180407 6726347 := bstep (se 1 (by rfl) ⟨5044760, by rfl⟩ : syracuseStep 6726347 = 10089521) B10089521
theorem B12780281 : Blo 1180407 12780281 := bstep (se 2 (by rfl) ⟨4792605, by rfl⟩ : syracuseStep 12780281 = 9585211) B9585211
theorem B1180463 : Blo 1180407 1180463 := bstep (se 1 (by rfl) ⟨885347, by rfl⟩ : syracuseStep 1180463 = 1770695) B1770695
theorem B1180571 : Blo 1180407 1180571 := bstep (se 1 (by rfl) ⟨885428, by rfl⟩ : syracuseStep 1180571 = 1770857) B1770857
theorem B1180623 : Blo 1180407 1180623 := bstep (se 1 (by rfl) ⟨885467, by rfl⟩ : syracuseStep 1180623 = 1770935) B1770935
theorem B3990491 : Blo 1180407 3990491 := bstep (se 1 (by rfl) ⟨2992868, by rfl⟩ : syracuseStep 3990491 = 5985737) B5985737
theorem B1180647 : Blo 1180407 1180647 := bstep (se 1 (by rfl) ⟨885485, by rfl⟩ : syracuseStep 1180647 = 1770971) B1770971
theorem B22709261 : Blo 1180407 22709261 := bstep (se 3 (by rfl) ⟨4257986, by rfl⟩ : syracuseStep 22709261 = 8515973) B8515973
theorem B3409129 : Blo 1180407 3409129 := bstep (se 2 (by rfl) ⟨1278423, by rfl⟩ : syracuseStep 3409129 = 2556847) B2556847
theorem B1180959 : Blo 1180407 1180959 := bstep (se 1 (by rfl) ⟨885719, by rfl⟩ : syracuseStep 1180959 = 1771439) B1771439
theorem B1770791 : Blo 1180407 1770791 := bstep (se 1 (by rfl) ⟨1328093, by rfl⟩ : syracuseStep 1770791 = 2656187) B2656187
theorem B1181019 : Blo 1180407 1181019 := bstep (se 1 (by rfl) ⟨885764, by rfl⟩ : syracuseStep 1181019 = 1771529) B1771529
theorem B1181039 : Blo 1180407 1181039 := bstep (se 1 (by rfl) ⟨885779, by rfl⟩ : syracuseStep 1181039 = 1771559) B1771559
theorem B1770875 : Blo 1180407 1770875 := bstep (se 1 (by rfl) ⟨1328156, by rfl⟩ : syracuseStep 1770875 = 2656313) B2656313
theorem B3786107 : Blo 1180407 3786107 := bstep (se 1 (by rfl) ⟨2839580, by rfl⟩ : syracuseStep 3786107 = 5679161) B5679161
theorem B1992073 : Blo 1180407 1992073 := bstep (se 2 (by rfl) ⟨747027, by rfl⟩ : syracuseStep 1992073 = 1494055) B1494055
theorem B1181095 : Blo 1180407 1181095 := bstep (se 1 (by rfl) ⟨885821, by rfl⟩ : syracuseStep 1181095 = 1771643) B1771643
theorem B1771001 : Blo 1180407 1771001 := bstep (se 2 (by rfl) ⟨664125, by rfl⟩ : syracuseStep 1771001 = 1328251) B1328251
theorem B1181179 : Blo 1180407 1181179 := bstep (se 1 (by rfl) ⟨885884, by rfl⟩ : syracuseStep 1181179 = 1771769) B1771769
theorem B2524679 : Blo 1180407 2524679 := bstep (se 1 (by rfl) ⟨1893509, by rfl⟩ : syracuseStep 2524679 = 3787019) B3787019
theorem B1181247 : Blo 1180407 1181247 := bstep (se 1 (by rfl) ⟨885935, by rfl⟩ : syracuseStep 1181247 = 1771871) B1771871
theorem B1181255 : Blo 1180407 1181255 := bstep (se 1 (by rfl) ⟨885941, by rfl⟩ : syracuseStep 1181255 = 1771883) B1771883
theorem B1771103 : Blo 1180407 1771103 := bstep (se 1 (by rfl) ⟨1328327, by rfl⟩ : syracuseStep 1771103 = 2656655) B2656655
theorem B1328863 : Blo 1180407 1328863 := bstep (se 1 (by rfl) ⟨996647, by rfl⟩ : syracuseStep 1328863 = 1993295) B1993295
theorem B1181407 : Blo 1180407 1181407 := bstep (se 1 (by rfl) ⟨886055, by rfl⟩ : syracuseStep 1181407 = 1772111) B1772111
theorem B2656007 : Blo 1180407 2656007 := bstep (se 1 (by rfl) ⟨1992005, by rfl⟩ : syracuseStep 2656007 = 3984011) B3984011
theorem B1181487 : Blo 1180407 1181487 := bstep (se 1 (by rfl) ⟨886115, by rfl⟩ : syracuseStep 1181487 = 1772231) B1772231
theorem B1771319 : Blo 1180407 1771319 := bstep (se 1 (by rfl) ⟨1328489, by rfl⟩ : syracuseStep 1771319 = 2656979) B2656979
theorem B1992505 : Blo 1180407 1992505 := bstep (se 2 (by rfl) ⟨747189, by rfl⟩ : syracuseStep 1992505 = 1494379) B1494379
theorem B1181595 : Blo 1180407 1181595 := bstep (se 1 (by rfl) ⟨886196, by rfl⟩ : syracuseStep 1181595 = 1772393) B1772393
theorem B17024975 : Blo 1180407 17024975 := bstep (se 1 (by rfl) ⟨12768731, by rfl⟩ : syracuseStep 17024975 = 25537463) B25537463
theorem B2557903 : Blo 1180407 2557903 := bstep (se 1 (by rfl) ⟨1918427, by rfl⟩ : syracuseStep 2557903 = 3836855) B3836855
theorem B1181647 : Blo 1180407 1181647 := bstep (se 1 (by rfl) ⟨886235, by rfl⟩ : syracuseStep 1181647 = 1772471) B1772471
theorem B2992079 : Blo 1180407 2992079 := bstep (se 1 (by rfl) ⟨2244059, by rfl⟩ : syracuseStep 2992079 = 4488119) B4488119
theorem B1181671 : Blo 1180407 1181671 := bstep (se 1 (by rfl) ⟨886253, by rfl⟩ : syracuseStep 1181671 = 1772507) B1772507
theorem B5679085 : Blo 1180407 5679085 := bstep (se 3 (by rfl) ⟨1064828, by rfl⟩ : syracuseStep 5679085 = 2129657) B2129657
theorem B2836505 : Blo 1180407 2836505 := bstep (se 2 (by rfl) ⟨1063689, by rfl⟩ : syracuseStep 2836505 = 2127379) B2127379
theorem B1992809 : Blo 1180407 1992809 := bstep (se 2 (by rfl) ⟨747303, by rfl⟩ : syracuseStep 1992809 = 1494607) B1494607
theorem B1771625 : Blo 1180407 1771625 := bstep (se 2 (by rfl) ⟨664359, by rfl⟩ : syracuseStep 1771625 = 1328719) B1328719
theorem B1329439 : Blo 1180407 1329439 := bstep (se 1 (by rfl) ⟨997079, by rfl⟩ : syracuseStep 1329439 = 1994159) B1994159
theorem B1181983 : Blo 1180407 1181983 := bstep (se 1 (by rfl) ⟨886487, by rfl⟩ : syracuseStep 1181983 = 1772975) B1772975
theorem B20474171 : Blo 1180407 20474171 := bstep (se 1 (by rfl) ⟨15355628, by rfl⟩ : syracuseStep 20474171 = 30711257) B30711257
theorem B1182043 : Blo 1180407 1182043 := bstep (se 1 (by rfl) ⟨886532, by rfl⟩ : syracuseStep 1182043 = 1773065) B1773065
theorem B2656619 : Blo 1180407 2656619 := bstep (se 1 (by rfl) ⟨1992464, by rfl⟩ : syracuseStep 2656619 = 3984929) B3984929
theorem B1182063 : Blo 1180407 1182063 := bstep (se 1 (by rfl) ⟨886547, by rfl⟩ : syracuseStep 1182063 = 1773095) B1773095
theorem B2394535 : Blo 1180407 2394535 := bstep (se 1 (by rfl) ⟨1795901, by rfl⟩ : syracuseStep 2394535 = 3591803) B3591803
theorem B1771943 : Blo 1180407 1771943 := bstep (se 1 (by rfl) ⟨1328957, by rfl⟩ : syracuseStep 1771943 = 2657915) B2657915
theorem B1182119 : Blo 1180407 1182119 := bstep (se 1 (by rfl) ⟨886589, by rfl⟩ : syracuseStep 1182119 = 1773179) B1773179
theorem B2656763 : Blo 1180407 2656763 := bstep (se 1 (by rfl) ⟨1992572, by rfl⟩ : syracuseStep 2656763 = 3985145) B3985145
theorem B1772027 : Blo 1180407 1772027 := bstep (se 1 (by rfl) ⟨1329020, by rfl⟩ : syracuseStep 1772027 = 2658041) B2658041
theorem B2558459 : Blo 1180407 2558459 := bstep (se 1 (by rfl) ⟨1918844, by rfl⟩ : syracuseStep 2558459 = 3837689) B3837689
theorem B1182203 : Blo 1180407 1182203 := bstep (se 1 (by rfl) ⟨886652, by rfl⟩ : syracuseStep 1182203 = 1773305) B1773305
theorem B1329727 : Blo 1180407 1329727 := bstep (se 1 (by rfl) ⟨997295, by rfl⟩ : syracuseStep 1329727 = 1994591) B1994591
theorem B1182271 : Blo 1180407 1182271 := bstep (se 1 (by rfl) ⟨886703, by rfl⟩ : syracuseStep 1182271 = 1773407) B1773407
theorem B2837063 : Blo 1180407 2837063 := bstep (se 1 (by rfl) ⟨2127797, by rfl⟩ : syracuseStep 2837063 = 4255595) B4255595
theorem B1182279 : Blo 1180407 1182279 := bstep (se 1 (by rfl) ⟨886709, by rfl⟩ : syracuseStep 1182279 = 1773419) B1773419
theorem B32320079 : Blo 1180407 32320079 := bstep (se 1 (by rfl) ⟨24240059, by rfl⟩ : syracuseStep 32320079 = 48480119) B48480119
theorem B2992747 : Blo 1180407 2992747 := bstep (se 1 (by rfl) ⟨2244560, by rfl⟩ : syracuseStep 2992747 = 4489121) B4489121
theorem B2656889 : Blo 1180407 2656889 := bstep (se 2 (by rfl) ⟨996333, by rfl⟩ : syracuseStep 2656889 = 1992667) B1992667
theorem B1772153 : Blo 1180407 1772153 := bstep (se 2 (by rfl) ⟨664557, by rfl⟩ : syracuseStep 1772153 = 1329115) B1329115
theorem B2656943 : Blo 1180407 2656943 := bstep (se 1 (by rfl) ⟨1992707, by rfl⟩ : syracuseStep 2656943 = 3985415) B3985415
theorem B1772207 : Blo 1180407 1772207 := bstep (se 1 (by rfl) ⟨1329155, by rfl⟩ : syracuseStep 1772207 = 2658311) B2658311
theorem B11504339 : Blo 1180407 11504339 := bstep (se 1 (by rfl) ⟨8628254, by rfl⟩ : syracuseStep 11504339 = 17256509) B17256509
theorem B24259283 : Blo 1180407 24259283 := bstep (se 1 (by rfl) ⟨18194462, by rfl⟩ : syracuseStep 24259283 = 36388925) B36388925
theorem B1772255 : Blo 1180407 1772255 := bstep (se 1 (by rfl) ⟨1329191, by rfl⟩ : syracuseStep 1772255 = 2658383) B2658383
theorem B3984119 : Blo 1180407 3984119 := bstep (se 1 (by rfl) ⟨2988089, by rfl⟩ : syracuseStep 3984119 = 5976179) B5976179
theorem B2657015 : Blo 1180407 2657015 := bstep (se 1 (by rfl) ⟨1992761, by rfl⟩ : syracuseStep 2657015 = 3985523) B3985523
theorem B2657195 : Blo 1180407 2657195 := bstep (se 1 (by rfl) ⟨1992896, by rfl⟩ : syracuseStep 2657195 = 3985793) B3985793
theorem B1682407 : Blo 1180407 1682407 := bstep (se 1 (by rfl) ⟨1261805, by rfl⟩ : syracuseStep 1682407 = 2523611) B2523611
theorem B1772519 : Blo 1180407 1772519 := bstep (se 1 (by rfl) ⟨1329389, by rfl⟩ : syracuseStep 1772519 = 2658779) B2658779
theorem B5393395 : Blo 1180407 5393395 := bstep (se 1 (by rfl) ⟨4045046, by rfl⟩ : syracuseStep 5393395 = 8090093) B8090093
theorem B1772777 : Blo 1180407 1772777 := bstep (se 2 (by rfl) ⟨664791, by rfl⟩ : syracuseStep 1772777 = 1329583) B1329583
theorem B1772831 : Blo 1180407 1772831 := bstep (se 1 (by rfl) ⟨1329623, by rfl⟩ : syracuseStep 1772831 = 2659247) B2659247
theorem B4255163 : Blo 1180407 4255163 := bstep (se 1 (by rfl) ⟨3191372, by rfl⟩ : syracuseStep 4255163 = 6382745) B6382745
theorem B24235463 : Blo 1180407 24235463 := bstep (se 1 (by rfl) ⟨18176597, by rfl⟩ : syracuseStep 24235463 = 36353195) B36353195
theorem B2657735 : Blo 1180407 2657735 := bstep (se 1 (by rfl) ⟨1993301, by rfl⟩ : syracuseStep 2657735 = 3986603) B3986603
theorem B1772999 : Blo 1180407 1772999 := bstep (se 1 (by rfl) ⟨1329749, by rfl⟩ : syracuseStep 1772999 = 2659499) B2659499
theorem B1994233 : Blo 1180407 1994233 := bstep (se 2 (by rfl) ⟨747837, by rfl⟩ : syracuseStep 1994233 = 1495675) B1495675
theorem B5672531 : Blo 1180407 5672531 := bstep (se 1 (by rfl) ⟨4254398, by rfl⟩ : syracuseStep 5672531 = 8508797) B8508797
theorem B4484717 : Blo 1180407 4484717 := bstep (se 3 (by rfl) ⟨840884, by rfl⟩ : syracuseStep 4484717 = 1681769) B1681769
theorem B1494703 : Blo 1180407 1494703 := bstep (se 1 (by rfl) ⟨1121027, by rfl⟩ : syracuseStep 1494703 = 2242055) B2242055
theorem B5983955 : Blo 1180407 5983955 := bstep (se 1 (by rfl) ⟨4487966, by rfl⟩ : syracuseStep 5983955 = 8975933) B8975933
theorem B1994503 : Blo 1180407 1994503 := bstep (se 1 (by rfl) ⟨1495877, by rfl⟩ : syracuseStep 1994503 = 2991755) B2991755
theorem B5754665 : Blo 1180407 5754665 := bstep (se 2 (by rfl) ⟨2157999, by rfl⟩ : syracuseStep 5754665 = 4315999) B4315999
theorem B1994537 : Blo 1180407 1994537 := bstep (se 2 (by rfl) ⟨747951, by rfl⟩ : syracuseStep 1994537 = 1495903) B1495903
theorem B1773353 : Blo 1180407 1773353 := bstep (se 2 (by rfl) ⟨665007, by rfl⟩ : syracuseStep 1773353 = 1330015) B1330015
theorem B5975855 : Blo 1180407 5975855 := bstep (se 1 (by rfl) ⟨4481891, by rfl⟩ : syracuseStep 5975855 = 8963783) B8963783
theorem B3985199 : Blo 1180407 3985199 := bstep (se 1 (by rfl) ⟨2988899, by rfl⟩ : syracuseStep 3985199 = 5977799) B5977799
theorem B2658095 : Blo 1180407 2658095 := bstep (se 1 (by rfl) ⟨1993571, by rfl⟩ : syracuseStep 2658095 = 3987143) B3987143
theorem B1773359 : Blo 1180407 1773359 := bstep (se 1 (by rfl) ⟨1330019, by rfl⟩ : syracuseStep 1773359 = 2660039) B2660039
theorem B2395961 : Blo 1180407 2395961 := bstep (se 2 (by rfl) ⟨898485, by rfl⟩ : syracuseStep 2395961 = 1796971) B1796971
theorem B5984603 : Blo 1180407 5984603 := bstep (se 1 (by rfl) ⟨4488452, by rfl⟩ : syracuseStep 5984603 = 8976905) B8976905
theorem B2658671 : Blo 1180407 2658671 := bstep (se 1 (by rfl) ⟨1994003, by rfl⟩ : syracuseStep 2658671 = 3988007) B3988007
theorem B2658743 : Blo 1180407 2658743 := bstep (se 1 (by rfl) ⟨1994057, by rfl⟩ : syracuseStep 2658743 = 3988115) B3988115
theorem B1995259 : Blo 1180407 1995259 := bstep (se 1 (by rfl) ⟨1496444, by rfl⟩ : syracuseStep 1995259 = 2992889) B2992889
theorem B5673473 : Blo 1180407 5673473 := bstep (se 2 (by rfl) ⟨2127552, by rfl⟩ : syracuseStep 5673473 = 4255105) B4255105
theorem B2658887 : Blo 1180407 2658887 := bstep (se 1 (by rfl) ⟨1994165, by rfl⟩ : syracuseStep 2658887 = 3988331) B3988331
theorem B2658923 : Blo 1180407 2658923 := bstep (se 1 (by rfl) ⟨1994192, by rfl⟩ : syracuseStep 2658923 = 3988385) B3988385
theorem B2659319 : Blo 1180407 2659319 := bstep (se 1 (by rfl) ⟨1994489, by rfl⟩ : syracuseStep 2659319 = 3988979) B3988979
theorem B20460595 : Blo 1180407 20460595 := bstep (se 1 (by rfl) ⟨15345446, by rfl⟩ : syracuseStep 20460595 = 30690893) B30690893
theorem B51106909 : Blo 1180407 51106909 := bstep (se 3 (by rfl) ⟨9582545, by rfl⟩ : syracuseStep 51106909 = 19165091) B19165091
theorem B5043343 : Blo 1180407 5043343 := bstep (se 1 (by rfl) ⟨3782507, by rfl⟩ : syracuseStep 5043343 = 7565015) B7565015
theorem B5387411 : Blo 1180407 5387411 := bstep (se 1 (by rfl) ⟨4040558, by rfl⟩ : syracuseStep 5387411 = 8081117) B8081117
theorem B45388997 : Blo 1180407 45388997 := bstep (se 4 (by rfl) ⟨4255218, by rfl⟩ : syracuseStep 45388997 = 8510437) B8510437
theorem B4486387 : Blo 1180407 4486387 := bstep (se 1 (by rfl) ⟨3364790, by rfl⟩ : syracuseStep 4486387 = 6729581) B6729581
theorem B327390497 : Blo 1180407 327390497 := bstep (se 2 (by rfl) ⟨122771436, by rfl⟩ : syracuseStep 327390497 = 245542873) B245542873
theorem B2127143 : Blo 1180407 2127143 := bstep (se 1 (by rfl) ⟨1595357, by rfl⟩ : syracuseStep 2127143 = 3190715) B3190715
theorem B5985575 : Blo 1180407 5985575 := bstep (se 1 (by rfl) ⟨4489181, by rfl⟩ : syracuseStep 5985575 = 8978363) B8978363
theorem B2659679 : Blo 1180407 2659679 := bstep (se 1 (by rfl) ⟨1994759, by rfl⟩ : syracuseStep 2659679 = 3989519) B3989519
theorem B5043617 : Blo 1180407 5043617 := bstep (se 2 (by rfl) ⟨1891356, by rfl⟩ : syracuseStep 5043617 = 3782713) B3782713
theorem B2660075 : Blo 1180407 2660075 := bstep (se 1 (by rfl) ⟨1995056, by rfl⟩ : syracuseStep 2660075 = 3990113) B3990113
theorem B5977961 : Blo 1180407 5977961 := bstep (se 2 (by rfl) ⟨2241735, by rfl⟩ : syracuseStep 5977961 = 4483471) B4483471
theorem B4257641 : Blo 1180407 4257641 := bstep (se 2 (by rfl) ⟨1596615, by rfl⟩ : syracuseStep 4257641 = 3193231) B3193231
theorem B3987305 : Blo 1180407 3987305 := bstep (se 2 (by rfl) ⟨1495239, by rfl⟩ : syracuseStep 3987305 = 2990479) B2990479
theorem B2660201 : Blo 1180407 2660201 := bstep (se 2 (by rfl) ⟨997575, by rfl⟩ : syracuseStep 2660201 = 1995151) B1995151
theorem B28760093 : Blo 1180407 28760093 := bstep (se 3 (by rfl) ⟨5392517, by rfl⟩ : syracuseStep 28760093 = 10785035) B10785035
theorem B2988161 : Blo 1180407 2988161 := bstep (se 2 (by rfl) ⟨1120560, by rfl⟩ : syracuseStep 2988161 = 2241121) B2241121
theorem B3987737 : Blo 1180407 3987737 := bstep (se 2 (by rfl) ⟨1495401, by rfl⟩ : syracuseStep 3987737 = 2990803) B2990803
theorem B2243027 : Blo 1180407 2243027 := bstep (se 1 (by rfl) ⟨1682270, by rfl⟩ : syracuseStep 2243027 = 3364541) B3364541
theorem B11352635 : Blo 1180407 11352635 := bstep (se 1 (by rfl) ⟨8514476, by rfl⟩ : syracuseStep 11352635 = 17028953) B17028953
theorem B2128447 : Blo 1180407 2128447 := bstep (se 1 (by rfl) ⟨1596335, by rfl⟩ : syracuseStep 2128447 = 3192671) B3192671
theorem B8518283 : Blo 1180407 8518283 := bstep (se 1 (by rfl) ⟨6388712, by rfl⟩ : syracuseStep 8518283 = 12777425) B12777425
theorem B129235661 : Blo 1180407 129235661 := bstep (se 3 (by rfl) ⟨24231686, by rfl⟩ : syracuseStep 129235661 = 48463373) B48463373
theorem B2988971 : Blo 1180407 2988971 := bstep (se 1 (by rfl) ⟨2241728, by rfl⟩ : syracuseStep 2988971 = 4483457) B4483457
theorem B4488331 : Blo 1180407 4488331 := bstep (se 1 (by rfl) ⟨3366248, by rfl⟩ : syracuseStep 4488331 = 6732497) B6732497
theorem B4791649 : Blo 1180407 4791649 := bstep (se 2 (by rfl) ⟨1796868, by rfl⟩ : syracuseStep 4791649 = 3593737) B3593737
theorem B5119361 : Blo 1180407 5119361 := bstep (se 2 (by rfl) ⟨1919760, by rfl⟩ : syracuseStep 5119361 = 3839521) B3839521
theorem B1891721 : Blo 1180407 1891721 := bstep (se 2 (by rfl) ⟨709395, by rfl⟩ : syracuseStep 1891721 = 1418791) B1418791
theorem B4488635 : Blo 1180407 4488635 := bstep (se 1 (by rfl) ⟨3366476, by rfl⟩ : syracuseStep 4488635 = 6732953) B6732953
theorem B1596871 : Blo 1180407 1596871 := bstep (se 1 (by rfl) ⟨1197653, by rfl⟩ : syracuseStep 1596871 = 2395307) B2395307
theorem B9715259 : Blo 1180407 9715259 := bstep (se 1 (by rfl) ⟨7286444, by rfl⟩ : syracuseStep 9715259 = 14572889) B14572889
theorem B5979743 : Blo 1180407 5979743 := bstep (se 1 (by rfl) ⟨4484807, by rfl⟩ : syracuseStep 5979743 = 8969615) B8969615
theorem B3989087 : Blo 1180407 3989087 := bstep (se 1 (by rfl) ⟨2991815, by rfl⟩ : syracuseStep 3989087 = 5983631) B5983631
theorem B24239731 : Blo 1180407 24239731 := bstep (se 1 (by rfl) ⟨18179798, by rfl⟩ : syracuseStep 24239731 = 36359597) B36359597
theorem B5463713 : Blo 1180407 5463713 := bstep (se 2 (by rfl) ⟨2048892, by rfl⟩ : syracuseStep 5463713 = 4097785) B4097785
theorem B2244257 : Blo 1180407 2244257 := bstep (se 2 (by rfl) ⟨841596, by rfl⟩ : syracuseStep 2244257 = 1683193) B1683193
theorem B2989831 : Blo 1180407 2989831 := bstep (se 1 (by rfl) ⟨2242373, by rfl⟩ : syracuseStep 2989831 = 4484747) B4484747
theorem B2522927 : Blo 1180407 2522927 := bstep (se 1 (by rfl) ⟨1892195, by rfl⟩ : syracuseStep 2522927 = 3784391) B3784391
theorem B4792121 : Blo 1180407 4792121 := bstep (se 2 (by rfl) ⟨1797045, by rfl⟩ : syracuseStep 4792121 = 3594091) B3594091
theorem B5046077 : Blo 1180407 5046077 := bstep (se 3 (by rfl) ⟨946139, by rfl⟩ : syracuseStep 5046077 = 1892279) B1892279
theorem B3366785 : Blo 1180407 3366785 := bstep (se 2 (by rfl) ⟨1262544, by rfl⟩ : syracuseStep 3366785 = 2525089) B2525089
theorem B5980391 : Blo 1180407 5980391 := bstep (se 1 (by rfl) ⟨4485293, by rfl⟩ : syracuseStep 5980391 = 8970587) B8970587
theorem B3989735 : Blo 1180407 3989735 := bstep (se 1 (by rfl) ⟨2992301, by rfl⟩ : syracuseStep 3989735 = 5984603) B5984603
theorem B8520187 : Blo 1180407 8520187 := bstep (se 1 (by rfl) ⟨6390140, by rfl⟩ : syracuseStep 8520187 = 12780281) B12780281
theorem B16155233 : Blo 1180407 16155233 := bstep (se 2 (by rfl) ⟨6058212, by rfl⟩ : syracuseStep 16155233 = 12116425) B12116425
theorem B15139507 : Blo 1180407 15139507 := bstep (se 1 (by rfl) ⟨11354630, by rfl⟩ : syracuseStep 15139507 = 22709261) B22709261
theorem B5047049 : Blo 1180407 5047049 := bstep (se 2 (by rfl) ⟨1892643, by rfl⟩ : syracuseStep 5047049 = 3785287) B3785287
theorem B3990329 : Blo 1180407 3990329 := bstep (se 2 (by rfl) ⟨1496373, by rfl⟩ : syracuseStep 3990329 = 2992747) B2992747
theorem B218260331 : Blo 1180407 218260331 := bstep (se 1 (by rfl) ⟨163695248, by rfl⟩ : syracuseStep 218260331 = 327390497) B327390497
theorem B1418095 : Blo 1180407 1418095 := bstep (se 1 (by rfl) ⟨1063571, by rfl⟩ : syracuseStep 1418095 = 2127143) B2127143
theorem B1180527 : Blo 1180407 1180527 := bstep (se 1 (by rfl) ⟨885395, by rfl⟩ : syracuseStep 1180527 = 1770791) B1770791
theorem B3990383 : Blo 1180407 3990383 := bstep (se 1 (by rfl) ⟨2992787, by rfl⟩ : syracuseStep 3990383 = 5985575) B5985575
theorem B1180583 : Blo 1180407 1180583 := bstep (se 1 (by rfl) ⟨885437, by rfl⟩ : syracuseStep 1180583 = 1770875) B1770875
theorem B1180667 : Blo 1180407 1180667 := bstep (se 1 (by rfl) ⟨885500, by rfl⟩ : syracuseStep 1180667 = 1771001) B1771001
theorem B1180735 : Blo 1180407 1180735 := bstep (se 1 (by rfl) ⟨885551, by rfl⟩ : syracuseStep 1180735 = 1771103) B1771103
theorem B1770671 : Blo 1180407 1770671 := bstep (se 1 (by rfl) ⟨1328003, by rfl⟩ : syracuseStep 1770671 = 2656007) B2656007
theorem B64627901 : Blo 1180407 64627901 := bstep (se 3 (by rfl) ⟨12117731, by rfl⟩ : syracuseStep 64627901 = 24235463) B24235463
theorem B1180879 : Blo 1180407 1180879 := bstep (se 1 (by rfl) ⟨885659, by rfl⟩ : syracuseStep 1180879 = 1771319) B1771319
theorem B1328539 : Blo 1180407 1328539 := bstep (se 1 (by rfl) ⟨996404, by rfl⟩ : syracuseStep 1328539 = 1992809) B1992809
theorem B1181083 : Blo 1180407 1181083 := bstep (se 1 (by rfl) ⟨885812, by rfl⟩ : syracuseStep 1181083 = 1771625) B1771625
theorem B27280793 : Blo 1180407 27280793 := bstep (se 2 (by rfl) ⟨10230297, by rfl⟩ : syracuseStep 27280793 = 20460595) B20460595
theorem B1992107 : Blo 1180407 1992107 := bstep (se 1 (by rfl) ⟨1494080, by rfl⟩ : syracuseStep 1992107 = 2988161) B2988161
theorem B68142545 : Blo 1180407 68142545 := bstep (se 2 (by rfl) ⟨25553454, by rfl⟩ : syracuseStep 68142545 = 51106909) B51106909
theorem B13649447 : Blo 1180407 13649447 := bstep (se 1 (by rfl) ⟨10237085, by rfl⟩ : syracuseStep 13649447 = 20474171) B20474171
theorem B1771079 : Blo 1180407 1771079 := bstep (se 1 (by rfl) ⟨1328309, by rfl⟩ : syracuseStep 1771079 = 2656619) B2656619
theorem B1181295 : Blo 1180407 1181295 := bstep (se 1 (by rfl) ⟨885971, by rfl⟩ : syracuseStep 1181295 = 1771943) B1771943
theorem B5981849 : Blo 1180407 5981849 := bstep (se 2 (by rfl) ⟨2243193, by rfl⟩ : syracuseStep 5981849 = 4486387) B4486387
theorem B1771175 : Blo 1180407 1771175 := bstep (se 1 (by rfl) ⟨1328381, by rfl⟩ : syracuseStep 1771175 = 2656763) B2656763
theorem B1181351 : Blo 1180407 1181351 := bstep (se 1 (by rfl) ⟨886013, by rfl⟩ : syracuseStep 1181351 = 1772027) B1772027
theorem B1705639 : Blo 1180407 1705639 := bstep (se 1 (by rfl) ⟨1279229, by rfl⟩ : syracuseStep 1705639 = 2558459) B2558459
theorem B21546719 : Blo 1180407 21546719 := bstep (se 1 (by rfl) ⟨16160039, by rfl⟩ : syracuseStep 21546719 = 32320079) B32320079
theorem B1771259 : Blo 1180407 1771259 := bstep (se 1 (by rfl) ⟨1328444, by rfl⟩ : syracuseStep 1771259 = 2656889) B2656889
theorem B1181435 : Blo 1180407 1181435 := bstep (se 1 (by rfl) ⟨886076, by rfl⟩ : syracuseStep 1181435 = 1772153) B1772153
theorem B5678855 : Blo 1180407 5678855 := bstep (se 1 (by rfl) ⟨4259141, by rfl⟩ : syracuseStep 5678855 = 8518283) B8518283
theorem B1771295 : Blo 1180407 1771295 := bstep (se 1 (by rfl) ⟨1328471, by rfl⟩ : syracuseStep 1771295 = 2656943) B2656943
theorem B1181471 : Blo 1180407 1181471 := bstep (se 1 (by rfl) ⟨886103, by rfl⟩ : syracuseStep 1181471 = 1772207) B1772207
theorem B86157107 : Blo 1180407 86157107 := bstep (se 1 (by rfl) ⟨64617830, by rfl⟩ : syracuseStep 86157107 = 129235661) B129235661
theorem B7669559 : Blo 1180407 7669559 := bstep (se 1 (by rfl) ⟨5752169, by rfl⟩ : syracuseStep 7669559 = 11504339) B11504339
theorem B1181503 : Blo 1180407 1181503 := bstep (se 1 (by rfl) ⟨886127, by rfl⟩ : syracuseStep 1181503 = 1772255) B1772255
theorem B2656079 : Blo 1180407 2656079 := bstep (se 1 (by rfl) ⟨1992059, by rfl⟩ : syracuseStep 2656079 = 3984119) B3984119
theorem B1771343 : Blo 1180407 1771343 := bstep (se 1 (by rfl) ⟨1328507, by rfl⟩ : syracuseStep 1771343 = 2657015) B2657015
theorem B2656097 : Blo 1180407 2656097 := bstep (se 2 (by rfl) ⟨996036, by rfl⟩ : syracuseStep 2656097 = 1992073) B1992073
theorem B1992647 : Blo 1180407 1992647 := bstep (se 1 (by rfl) ⟨1494485, by rfl⟩ : syracuseStep 1992647 = 2988971) B2988971
theorem B1771463 : Blo 1180407 1771463 := bstep (se 1 (by rfl) ⟨1328597, by rfl⟩ : syracuseStep 1771463 = 2657195) B2657195
theorem B1181679 : Blo 1180407 1181679 := bstep (se 1 (by rfl) ⟨886259, by rfl⟩ : syracuseStep 1181679 = 1772519) B1772519
theorem B6727805 : Blo 1180407 6727805 := bstep (se 3 (by rfl) ⟨1261463, by rfl⟩ : syracuseStep 6727805 = 2522927) B2522927
theorem B32319641 : Blo 1180407 32319641 := bstep (se 2 (by rfl) ⟨12119865, by rfl⟩ : syracuseStep 32319641 = 24239731) B24239731
theorem B1181851 : Blo 1180407 1181851 := bstep (se 1 (by rfl) ⟨886388, by rfl⟩ : syracuseStep 1181851 = 1772777) B1772777
theorem B1181887 : Blo 1180407 1181887 := bstep (se 1 (by rfl) ⟨886415, by rfl⟩ : syracuseStep 1181887 = 1772831) B1772831
theorem B1992937 : Blo 1180407 1992937 := bstep (se 2 (by rfl) ⟨747351, by rfl⟩ : syracuseStep 1992937 = 1494703) B1494703
theorem B2836775 : Blo 1180407 2836775 := bstep (se 1 (by rfl) ⟨2127581, by rfl⟩ : syracuseStep 2836775 = 4255163) B4255163
theorem B1771817 : Blo 1180407 1771817 := bstep (se 2 (by rfl) ⟨664431, by rfl⟩ : syracuseStep 1771817 = 1328863) B1328863
theorem B2992423 : Blo 1180407 2992423 := bstep (se 1 (by rfl) ⟨2244317, by rfl⟩ : syracuseStep 2992423 = 4488635) B4488635
theorem B1771823 : Blo 1180407 1771823 := bstep (se 1 (by rfl) ⟨1328867, by rfl⟩ : syracuseStep 1771823 = 2657735) B2657735
theorem B1181999 : Blo 1180407 1181999 := bstep (se 1 (by rfl) ⟨886499, by rfl⟩ : syracuseStep 1181999 = 1772999) B1772999
theorem B2656673 : Blo 1180407 2656673 := bstep (se 2 (by rfl) ⟨996252, by rfl⟩ : syracuseStep 2656673 = 1992505) B1992505
theorem B3836443 : Blo 1180407 3836443 := bstep (se 1 (by rfl) ⟨2877332, by rfl⟩ : syracuseStep 3836443 = 5754665) B5754665
theorem B1329691 : Blo 1180407 1329691 := bstep (se 1 (by rfl) ⟨997268, by rfl⟩ : syracuseStep 1329691 = 1994537) B1994537
theorem B1182235 : Blo 1180407 1182235 := bstep (se 1 (by rfl) ⟨886676, by rfl⟩ : syracuseStep 1182235 = 1773353) B1773353
theorem B3983903 : Blo 1180407 3983903 := bstep (se 1 (by rfl) ⟨2987927, by rfl⟩ : syracuseStep 3983903 = 5975855) B5975855
theorem B2656799 : Blo 1180407 2656799 := bstep (se 1 (by rfl) ⟨1992599, by rfl⟩ : syracuseStep 2656799 = 3985199) B3985199
theorem B1772063 : Blo 1180407 1772063 := bstep (se 1 (by rfl) ⟨1329047, by rfl⟩ : syracuseStep 1772063 = 2658095) B2658095
theorem B1182239 : Blo 1180407 1182239 := bstep (se 1 (by rfl) ⟨886679, by rfl⟩ : syracuseStep 1182239 = 1773359) B1773359
theorem B3410537 : Blo 1180407 3410537 := bstep (se 2 (by rfl) ⟨1278951, by rfl⟩ : syracuseStep 3410537 = 2557903) B2557903
theorem B7572113 : Blo 1180407 7572113 := bstep (se 2 (by rfl) ⟨2839542, by rfl⟩ : syracuseStep 7572113 = 5679085) B5679085
theorem B1993403 : Blo 1180407 1993403 := bstep (se 1 (by rfl) ⟨1495052, by rfl⟩ : syracuseStep 1993403 = 2990105) B2990105
theorem B7564013 : Blo 1180407 7564013 := bstep (se 3 (by rfl) ⟨1418252, by rfl⟩ : syracuseStep 7564013 = 2836505) B2836505
theorem B14379767 : Blo 1180407 14379767 := bstep (se 1 (by rfl) ⟨10784825, by rfl⟩ : syracuseStep 14379767 = 21569651) B21569651
theorem B1772447 : Blo 1180407 1772447 := bstep (se 1 (by rfl) ⟨1329335, by rfl⟩ : syracuseStep 1772447 = 2658671) B2658671
theorem B1772495 : Blo 1180407 1772495 := bstep (se 1 (by rfl) ⟨1329371, by rfl⟩ : syracuseStep 1772495 = 2658743) B2658743
theorem B22703111 : Blo 1180407 22703111 := bstep (se 1 (by rfl) ⟨17027333, by rfl⟩ : syracuseStep 22703111 = 34054667) B34054667
theorem B1772585 : Blo 1180407 1772585 := bstep (se 2 (by rfl) ⟨664719, by rfl⟩ : syracuseStep 1772585 = 1329439) B1329439
theorem B1772591 : Blo 1180407 1772591 := bstep (se 1 (by rfl) ⟨1329443, by rfl⟩ : syracuseStep 1772591 = 2658887) B2658887
theorem B1772615 : Blo 1180407 1772615 := bstep (se 1 (by rfl) ⟨1329461, by rfl⟩ : syracuseStep 1772615 = 2658923) B2658923
theorem B7564423 : Blo 1180407 7564423 := bstep (se 1 (by rfl) ⟨5673317, by rfl⟩ : syracuseStep 7564423 = 11346635) B11346635
theorem B4484231 : Blo 1180407 4484231 := bstep (se 1 (by rfl) ⟨3363173, by rfl⟩ : syracuseStep 4484231 = 6726347) B6726347
theorem B1772879 : Blo 1180407 1772879 := bstep (se 1 (by rfl) ⟨1329659, by rfl⟩ : syracuseStep 1772879 = 2659319) B2659319
theorem B2837929 : Blo 1180407 2837929 := bstep (se 2 (by rfl) ⟨1064223, by rfl⟩ : syracuseStep 2837929 = 2128447) B2128447
theorem B1772969 : Blo 1180407 1772969 := bstep (se 2 (by rfl) ⟨664863, by rfl⟩ : syracuseStep 1772969 = 1329727) B1329727
theorem B3591607 : Blo 1180407 3591607 := bstep (se 1 (by rfl) ⟨2693705, by rfl⟩ : syracuseStep 3591607 = 5387411) B5387411
theorem B1773119 : Blo 1180407 1773119 := bstep (se 1 (by rfl) ⟨1329839, by rfl⟩ : syracuseStep 1773119 = 2659679) B2659679
theorem B3362411 : Blo 1180407 3362411 := bstep (se 1 (by rfl) ⟨2521808, by rfl⟩ : syracuseStep 3362411 = 5043617) B5043617
theorem B10096285 : Blo 1180407 10096285 := bstep (se 3 (by rfl) ⟨1893053, by rfl⟩ : syracuseStep 10096285 = 3786107) B3786107
theorem B1683119 : Blo 1180407 1683119 := bstep (se 1 (by rfl) ⟨1262339, by rfl⟩ : syracuseStep 1683119 = 2524679) B2524679
theorem B1773383 : Blo 1180407 1773383 := bstep (se 1 (by rfl) ⟨1330037, by rfl⟩ : syracuseStep 1773383 = 2660075) B2660075
theorem B3985307 : Blo 1180407 3985307 := bstep (se 1 (by rfl) ⟨2988980, by rfl⟩ : syracuseStep 3985307 = 5977961) B5977961
theorem B2658203 : Blo 1180407 2658203 := bstep (se 1 (by rfl) ⟨1993652, by rfl⟩ : syracuseStep 2658203 = 3987305) B3987305
theorem B1773467 : Blo 1180407 1773467 := bstep (se 1 (by rfl) ⟨1330100, by rfl⟩ : syracuseStep 1773467 = 2660201) B2660201
theorem B11349983 : Blo 1180407 11349983 := bstep (se 1 (by rfl) ⟨8512487, by rfl⟩ : syracuseStep 11349983 = 17024975) B17024975
theorem B1994719 : Blo 1180407 1994719 := bstep (se 1 (by rfl) ⟨1496039, by rfl⟩ : syracuseStep 1994719 = 2992079) B2992079
theorem B19173395 : Blo 1180407 19173395 := bstep (se 1 (by rfl) ⟨14380046, by rfl⟩ : syracuseStep 19173395 = 28760093) B28760093
theorem B25907357 : Blo 1180407 25907357 := bstep (se 3 (by rfl) ⟨4857629, by rfl⟩ : syracuseStep 25907357 = 9715259) B9715259
theorem B5984441 : Blo 1180407 5984441 := bstep (se 2 (by rfl) ⟨2244165, by rfl⟩ : syracuseStep 5984441 = 4488331) B4488331
theorem B2658491 : Blo 1180407 2658491 := bstep (se 1 (by rfl) ⟨1993868, by rfl⟩ : syracuseStep 2658491 = 3987737) B3987737
theorem B7565501 : Blo 1180407 7565501 := bstep (se 3 (by rfl) ⟨1418531, by rfl⟩ : syracuseStep 7565501 = 2837063) B2837063
theorem B15126749 : Blo 1180407 15126749 := bstep (se 3 (by rfl) ⟨2836265, by rfl⟩ : syracuseStep 15126749 = 5672531) B5672531
theorem B1495351 : Blo 1180407 1495351 := bstep (se 1 (by rfl) ⟨1121513, by rfl⟩ : syracuseStep 1495351 = 2243027) B2243027
theorem B14569901 : Blo 1180407 14569901 := bstep (se 3 (by rfl) ⟨2731856, by rfl⟩ : syracuseStep 14569901 = 5463713) B5463713
theorem B2658977 : Blo 1180407 2658977 := bstep (se 2 (by rfl) ⟨997116, by rfl⟩ : syracuseStep 2658977 = 1994233) B1994233
theorem B3412907 : Blo 1180407 3412907 := bstep (se 1 (by rfl) ⟨2559680, by rfl⟩ : syracuseStep 3412907 = 5119361) B5119361
theorem B3986441 : Blo 1180407 3986441 := bstep (se 2 (by rfl) ⟨1494915, by rfl⟩ : syracuseStep 3986441 = 2989831) B2989831
theorem B2659337 : Blo 1180407 2659337 := bstep (se 2 (by rfl) ⟨997251, by rfl⟩ : syracuseStep 2659337 = 1994503) B1994503
theorem B3986495 : Blo 1180407 3986495 := bstep (se 1 (by rfl) ⟨2989871, by rfl⟩ : syracuseStep 3986495 = 5979743) B5979743
theorem B2659391 : Blo 1180407 2659391 := bstep (se 1 (by rfl) ⟨1994543, by rfl⟩ : syracuseStep 2659391 = 3989087) B3989087
theorem B1496171 : Blo 1180407 1496171 := bstep (se 1 (by rfl) ⟨1122128, by rfl⟩ : syracuseStep 1496171 = 2244257) B2244257
theorem B3364051 : Blo 1180407 3364051 := bstep (se 1 (by rfl) ⟨2523038, by rfl⟩ : syracuseStep 3364051 = 5046077) B5046077
theorem B3782315 : Blo 1180407 3782315 := bstep (se 1 (by rfl) ⟨2836736, by rfl⟩ : syracuseStep 3782315 = 5673473) B5673473
theorem B3192713 : Blo 1180407 3192713 := bstep (se 2 (by rfl) ⟨1197267, by rfl⟩ : syracuseStep 3192713 = 2394535) B2394535
theorem B25556917 : Blo 1180407 25556917 := bstep (se 5 (by rfl) ⟨1197980, by rfl⟩ : syracuseStep 25556917 = 2395961) B2395961
theorem B2660327 : Blo 1180407 2660327 := bstep (se 1 (by rfl) ⟨1995245, by rfl⟩ : syracuseStep 2660327 = 3990491) B3990491
theorem B2660345 : Blo 1180407 2660345 := bstep (se 2 (by rfl) ⟨997629, by rfl⟩ : syracuseStep 2660345 = 1995259) B1995259
theorem B30259331 : Blo 1180407 30259331 := bstep (se 1 (by rfl) ⟨22694498, by rfl⟩ : syracuseStep 30259331 = 45388997) B45388997
theorem B5044589 : Blo 1180407 5044589 := bstep (se 3 (by rfl) ⟨945860, by rfl⟩ : syracuseStep 5044589 = 1891721) B1891721
theorem B16172855 : Blo 1180407 16172855 := bstep (se 1 (by rfl) ⟨12129641, by rfl⟩ : syracuseStep 16172855 = 24259283) B24259283
theorem B2243209 : Blo 1180407 2243209 := bstep (se 2 (by rfl) ⟨841203, by rfl⟩ : syracuseStep 2243209 = 1682407) B1682407
theorem B7191193 : Blo 1180407 7191193 := bstep (se 2 (by rfl) ⟨2696697, by rfl⟩ : syracuseStep 7191193 = 5393395) B5393395
theorem B6724457 : Blo 1180407 6724457 := bstep (se 2 (by rfl) ⟨2521671, by rfl⟩ : syracuseStep 6724457 = 5043343) B5043343
theorem B4545505 : Blo 1180407 4545505 := bstep (se 2 (by rfl) ⟨1704564, by rfl⟩ : syracuseStep 4545505 = 3409129) B3409129
theorem B7568423 : Blo 1180407 7568423 := bstep (se 1 (by rfl) ⟨5676317, by rfl⟩ : syracuseStep 7568423 = 11352635) B11352635
theorem B6388865 : Blo 1180407 6388865 := bstep (se 2 (by rfl) ⟨2395824, by rfl⟩ : syracuseStep 6388865 = 4791649) B4791649
theorem B2129161 : Blo 1180407 2129161 := bstep (se 2 (by rfl) ⟨798435, by rfl⟩ : syracuseStep 2129161 = 1596871) B1596871
theorem B11353709 : Blo 1180407 11353709 := bstep (se 3 (by rfl) ⟨2128820, by rfl⟩ : syracuseStep 11353709 = 4257641) B4257641
theorem B2989811 : Blo 1180407 2989811 := bstep (se 1 (by rfl) ⟨2242358, by rfl⟩ : syracuseStep 2989811 = 4484717) B4484717
theorem B3989303 : Blo 1180407 3989303 := bstep (se 1 (by rfl) ⟨2991977, by rfl⟩ : syracuseStep 3989303 = 5983955) B5983955
theorem B3194747 : Blo 1180407 3194747 := bstep (se 1 (by rfl) ⟨2396060, by rfl⟩ : syracuseStep 3194747 = 4792121) B4792121
theorem B2244523 : Blo 1180407 2244523 := bstep (se 1 (by rfl) ⟨1683392, by rfl⟩ : syracuseStep 2244523 = 3366785) B3366785
theorem B3989627 : Blo 1180407 3989627 := bstep (se 1 (by rfl) ⟨2992220, by rfl⟩ : syracuseStep 3989627 = 5984441) B5984441
theorem B10084499 : Blo 1180407 10084499 := bstep (se 1 (by rfl) ⟨7563374, by rfl⟩ : syracuseStep 10084499 = 15126749) B15126749
theorem B3989789 : Blo 1180407 3989789 := bstep (se 3 (by rfl) ⟨748085, by rfl⟩ : syracuseStep 3989789 = 1496171) B1496171
theorem B3989897 : Blo 1180407 3989897 := bstep (se 2 (by rfl) ⟨1496211, by rfl⟩ : syracuseStep 3989897 = 2992423) B2992423
theorem B145506887 : Blo 1180407 145506887 := bstep (se 1 (by rfl) ⟨109130165, by rfl⟩ : syracuseStep 145506887 = 218260331) B218260331
theorem B1180447 : Blo 1180407 1180447 := bstep (se 1 (by rfl) ⟨885335, by rfl⟩ : syracuseStep 1180447 = 1770671) B1770671
theorem B2990945 : Blo 1180407 2990945 := bstep (se 2 (by rfl) ⟨1121604, by rfl⟩ : syracuseStep 2990945 = 2243209) B2243209
theorem B20186009 : Blo 1180407 20186009 := bstep (se 2 (by rfl) ⟨7569753, by rfl⟩ : syracuseStep 20186009 = 15139507) B15139507
theorem B18187195 : Blo 1180407 18187195 := bstep (se 1 (by rfl) ⟨13640396, by rfl⟩ : syracuseStep 18187195 = 27280793) B27280793
theorem B1328071 : Blo 1180407 1328071 := bstep (se 1 (by rfl) ⟨996053, by rfl⟩ : syracuseStep 1328071 = 1992107) B1992107
theorem B1180719 : Blo 1180407 1180719 := bstep (se 1 (by rfl) ⟨885539, by rfl⟩ : syracuseStep 1180719 = 1771079) B1771079
theorem B1180783 : Blo 1180407 1180783 := bstep (se 1 (by rfl) ⟨885587, by rfl⟩ : syracuseStep 1180783 = 1771175) B1771175
theorem B1180839 : Blo 1180407 1180839 := bstep (se 1 (by rfl) ⟨885629, by rfl⟩ : syracuseStep 1180839 = 1771259) B1771259
theorem B3785903 : Blo 1180407 3785903 := bstep (se 1 (by rfl) ⟨2839427, by rfl⟩ : syracuseStep 3785903 = 5678855) B5678855
theorem B1180863 : Blo 1180407 1180863 := bstep (se 1 (by rfl) ⟨885647, by rfl⟩ : syracuseStep 1180863 = 1771295) B1771295
theorem B5113039 : Blo 1180407 5113039 := bstep (se 1 (by rfl) ⟨3834779, by rfl⟩ : syracuseStep 5113039 = 7669559) B7669559
theorem B10781903 : Blo 1180407 10781903 := bstep (se 1 (by rfl) ⟨8086427, by rfl⟩ : syracuseStep 10781903 = 16172855) B16172855
theorem B1770719 : Blo 1180407 1770719 := bstep (se 1 (by rfl) ⟨1328039, by rfl⟩ : syracuseStep 1770719 = 2656079) B2656079
theorem B1180895 : Blo 1180407 1180895 := bstep (se 1 (by rfl) ⟨885671, by rfl⟩ : syracuseStep 1180895 = 1771343) B1771343
theorem B1770731 : Blo 1180407 1770731 := bstep (se 1 (by rfl) ⟨1328048, by rfl⟩ : syracuseStep 1770731 = 2656097) B2656097
theorem B1328431 : Blo 1180407 1328431 := bstep (se 1 (by rfl) ⟨996323, by rfl⟩ : syracuseStep 1328431 = 1992647) B1992647
theorem B1180975 : Blo 1180407 1180975 := bstep (se 1 (by rfl) ⟨885731, by rfl⟩ : syracuseStep 1180975 = 1771463) B1771463
theorem B21546427 : Blo 1180407 21546427 := bstep (se 1 (by rfl) ⟨16159820, by rfl⟩ : syracuseStep 21546427 = 32319641) B32319641
theorem B10085897 : Blo 1180407 10085897 := bstep (se 2 (by rfl) ⟨3782211, by rfl⟩ : syracuseStep 10085897 = 7564423) B7564423
theorem B1181211 : Blo 1180407 1181211 := bstep (se 1 (by rfl) ⟨885908, by rfl⟩ : syracuseStep 1181211 = 1771817) B1771817
theorem B1181215 : Blo 1180407 1181215 := bstep (se 1 (by rfl) ⟨885911, by rfl⟩ : syracuseStep 1181215 = 1771823) B1771823
theorem B1771115 : Blo 1180407 1771115 := bstep (se 1 (by rfl) ⟨1328336, by rfl⟩ : syracuseStep 1771115 = 2656673) B2656673
theorem B9094765 : Blo 1180407 9094765 := bstep (se 3 (by rfl) ⟨1705268, by rfl⟩ : syracuseStep 9094765 = 3410537) B3410537
theorem B2655935 : Blo 1180407 2655935 := bstep (se 1 (by rfl) ⟨1991951, by rfl⟩ : syracuseStep 2655935 = 3983903) B3983903
theorem B1771199 : Blo 1180407 1771199 := bstep (se 1 (by rfl) ⟨1328399, by rfl⟩ : syracuseStep 1771199 = 2656799) B2656799
theorem B1181375 : Blo 1180407 1181375 := bstep (se 1 (by rfl) ⟨886031, by rfl⟩ : syracuseStep 1181375 = 1772063) B1772063
theorem B5048075 : Blo 1180407 5048075 := bstep (se 1 (by rfl) ⟨3786056, by rfl⟩ : syracuseStep 5048075 = 7572113) B7572113
theorem B1328935 : Blo 1180407 1328935 := bstep (se 1 (by rfl) ⟨996701, by rfl⟩ : syracuseStep 1328935 = 1993403) B1993403
theorem B9586511 : Blo 1180407 9586511 := bstep (se 1 (by rfl) ⟨7189883, by rfl⟩ : syracuseStep 9586511 = 14379767) B14379767
theorem B1771385 : Blo 1180407 1771385 := bstep (se 2 (by rfl) ⟨664269, by rfl⟩ : syracuseStep 1771385 = 1328539) B1328539
theorem B4482971 : Blo 1180407 4482971 := bstep (se 1 (by rfl) ⟨3362228, by rfl⟩ : syracuseStep 4482971 = 6724457) B6724457
theorem B1181631 : Blo 1180407 1181631 := bstep (se 1 (by rfl) ⟨886223, by rfl⟩ : syracuseStep 1181631 = 1772447) B1772447
theorem B1181663 : Blo 1180407 1181663 := bstep (se 1 (by rfl) ⟨886247, by rfl⟩ : syracuseStep 1181663 = 1772495) B1772495
theorem B1181723 : Blo 1180407 1181723 := bstep (se 1 (by rfl) ⟨886292, by rfl⟩ : syracuseStep 1181723 = 1772585) B1772585
theorem B1181727 : Blo 1180407 1181727 := bstep (se 1 (by rfl) ⟨886295, by rfl⟩ : syracuseStep 1181727 = 1772591) B1772591
theorem B1181743 : Blo 1180407 1181743 := bstep (se 1 (by rfl) ⟨886307, by rfl⟩ : syracuseStep 1181743 = 1772615) B1772615
theorem B13461713 : Blo 1180407 13461713 := bstep (se 2 (by rfl) ⟨5048142, by rfl⟩ : syracuseStep 13461713 = 10096285) B10096285
theorem B1181919 : Blo 1180407 1181919 := bstep (se 1 (by rfl) ⟨886439, by rfl⟩ : syracuseStep 1181919 = 1772879) B1772879
theorem B1181979 : Blo 1180407 1181979 := bstep (se 1 (by rfl) ⟨886484, by rfl⟩ : syracuseStep 1181979 = 1772969) B1772969
theorem B1182079 : Blo 1180407 1182079 := bstep (se 1 (by rfl) ⟨886559, by rfl⟩ : syracuseStep 1182079 = 1773119) B1773119
theorem B1993207 : Blo 1180407 1993207 := bstep (se 1 (by rfl) ⟨1494905, by rfl⟩ : syracuseStep 1993207 = 2989811) B2989811
theorem B1182255 : Blo 1180407 1182255 := bstep (se 1 (by rfl) ⟨886691, by rfl⟩ : syracuseStep 1182255 = 1773383) B1773383
theorem B2992697 : Blo 1180407 2992697 := bstep (se 2 (by rfl) ⟨1122261, by rfl⟩ : syracuseStep 2992697 = 2244523) B2244523
theorem B2656871 : Blo 1180407 2656871 := bstep (se 1 (by rfl) ⟨1992653, by rfl⟩ : syracuseStep 2656871 = 3985307) B3985307
theorem B1772135 : Blo 1180407 1772135 := bstep (se 1 (by rfl) ⟨1329101, by rfl⟩ : syracuseStep 1772135 = 2658203) B2658203
theorem B1182311 : Blo 1180407 1182311 := bstep (se 1 (by rfl) ⟨886733, by rfl⟩ : syracuseStep 1182311 = 1773467) B1773467
theorem B51129053 : Blo 1180407 51129053 := bstep (se 3 (by rfl) ⟨9586697, by rfl⟩ : syracuseStep 51129053 = 19173395) B19173395
theorem B17271571 : Blo 1180407 17271571 := bstep (se 1 (by rfl) ⟨12953678, by rfl⟩ : syracuseStep 17271571 = 25907357) B25907357
theorem B1772327 : Blo 1180407 1772327 := bstep (se 1 (by rfl) ⟨1329245, by rfl⟩ : syracuseStep 1772327 = 2658491) B2658491
theorem B2657249 : Blo 1180407 2657249 := bstep (se 2 (by rfl) ⟨996468, by rfl⟩ : syracuseStep 2657249 = 1992937) B1992937
theorem B1993801 : Blo 1180407 1993801 := bstep (se 2 (by rfl) ⟨747675, by rfl⟩ : syracuseStep 1993801 = 1495351) B1495351
theorem B1772651 : Blo 1180407 1772651 := bstep (se 1 (by rfl) ⟨1329488, by rfl⟩ : syracuseStep 1772651 = 2658977) B2658977
theorem B2657627 : Blo 1180407 2657627 := bstep (se 1 (by rfl) ⟨1993220, by rfl⟩ : syracuseStep 2657627 = 3986441) B3986441
theorem B1772891 : Blo 1180407 1772891 := bstep (se 1 (by rfl) ⟨1329668, by rfl⟩ : syracuseStep 1772891 = 2659337) B2659337
theorem B5115257 : Blo 1180407 5115257 := bstep (se 2 (by rfl) ⟨1918221, by rfl⟩ : syracuseStep 5115257 = 3836443) B3836443
theorem B1772921 : Blo 1180407 1772921 := bstep (se 2 (by rfl) ⟨664845, by rfl⟩ : syracuseStep 1772921 = 1329691) B1329691
theorem B2657663 : Blo 1180407 2657663 := bstep (se 1 (by rfl) ⟨1993247, by rfl⟩ : syracuseStep 2657663 = 3986495) B3986495
theorem B1772927 : Blo 1180407 1772927 := bstep (se 1 (by rfl) ⟨1329695, by rfl⟩ : syracuseStep 1772927 = 2659391) B2659391
theorem B43085267 : Blo 1180407 43085267 := bstep (se 1 (by rfl) ⟨32313950, by rfl⟩ : syracuseStep 43085267 = 64627901) B64627901
theorem B9588257 : Blo 1180407 9588257 := bstep (se 2 (by rfl) ⟨3595596, by rfl⟩ : syracuseStep 9588257 = 7191193) B7191193
theorem B45428363 : Blo 1180407 45428363 := bstep (se 1 (by rfl) ⟨34071272, by rfl⟩ : syracuseStep 45428363 = 68142545) B68142545
theorem B14364479 : Blo 1180407 14364479 := bstep (se 1 (by rfl) ⟨10773359, by rfl⟩ : syracuseStep 14364479 = 21546719) B21546719
theorem B57438071 : Blo 1180407 57438071 := bstep (se 1 (by rfl) ⟨43078553, by rfl⟩ : syracuseStep 57438071 = 86157107) B86157107
theorem B1773551 : Blo 1180407 1773551 := bstep (se 1 (by rfl) ⟨1330163, by rfl⟩ : syracuseStep 1773551 = 2660327) B2660327
theorem B1773563 : Blo 1180407 1773563 := bstep (se 1 (by rfl) ⟨1330172, by rfl⟩ : syracuseStep 1773563 = 2660345) B2660345
theorem B4485203 : Blo 1180407 4485203 := bstep (se 1 (by rfl) ⟨3363902, by rfl⟩ : syracuseStep 4485203 = 6727805) B6727805
theorem B20172887 : Blo 1180407 20172887 := bstep (se 1 (by rfl) ⟨15129665, by rfl⟩ : syracuseStep 20172887 = 30259331) B30259331
theorem B3363059 : Blo 1180407 3363059 := bstep (se 1 (by rfl) ⟨2522294, by rfl⟩ : syracuseStep 3363059 = 5044589) B5044589
theorem B4485401 : Blo 1180407 4485401 := bstep (se 2 (by rfl) ⟨1682025, by rfl⟩ : syracuseStep 4485401 = 3364051) B3364051
theorem B2838881 : Blo 1180407 2838881 := bstep (se 2 (by rfl) ⟨1064580, by rfl⟩ : syracuseStep 2838881 = 2129161) B2129161
theorem B5042675 : Blo 1180407 5042675 := bstep (se 1 (by rfl) ⟨3782006, by rfl⟩ : syracuseStep 5042675 = 7564013) B7564013
theorem B4788809 : Blo 1180407 4788809 := bstep (se 2 (by rfl) ⟨1795803, by rfl⟩ : syracuseStep 4788809 = 3591607) B3591607
theorem B15135407 : Blo 1180407 15135407 := bstep (se 1 (by rfl) ⟨11351555, by rfl⟩ : syracuseStep 15135407 = 22703111) B22703111
theorem B2274185 : Blo 1180407 2274185 := bstep (se 2 (by rfl) ⟨852819, by rfl⟩ : syracuseStep 2274185 = 1705639) B1705639
theorem B2241607 : Blo 1180407 2241607 := bstep (se 1 (by rfl) ⟨1681205, by rfl⟩ : syracuseStep 2241607 = 3362411) B3362411
theorem B2659535 : Blo 1180407 2659535 := bstep (se 1 (by rfl) ⟨1994651, by rfl⟩ : syracuseStep 2659535 = 3989303) B3989303
theorem B34075889 : Blo 1180407 34075889 := bstep (se 2 (by rfl) ⟨12778458, by rfl⟩ : syracuseStep 34075889 = 25556917) B25556917
theorem B2659625 : Blo 1180407 2659625 := bstep (se 2 (by rfl) ⟨997359, by rfl⟩ : syracuseStep 2659625 = 1994719) B1994719
theorem B7566655 : Blo 1180407 7566655 := bstep (se 1 (by rfl) ⟨5674991, by rfl⟩ : syracuseStep 7566655 = 11349983) B11349983
theorem B5043667 : Blo 1180407 5043667 := bstep (se 1 (by rfl) ⟨3782750, by rfl⟩ : syracuseStep 5043667 = 7565501) B7565501
theorem B3986927 : Blo 1180407 3986927 := bstep (se 1 (by rfl) ⟨2990195, by rfl⟩ : syracuseStep 3986927 = 5980391) B5980391
theorem B2659823 : Blo 1180407 2659823 := bstep (se 1 (by rfl) ⟨1994867, by rfl⟩ : syracuseStep 2659823 = 3989735) B3989735
theorem B9713267 : Blo 1180407 9713267 := bstep (se 1 (by rfl) ⟨7284950, by rfl⟩ : syracuseStep 9713267 = 14569901) B14569901
theorem B10770155 : Blo 1180407 10770155 := bstep (se 1 (by rfl) ⟨8077616, by rfl⟩ : syracuseStep 10770155 = 16155233) B16155233
theorem B2660219 : Blo 1180407 2660219 := bstep (se 1 (by rfl) ⟨1995164, by rfl⟩ : syracuseStep 2660219 = 3990329) B3990329
theorem B2660255 : Blo 1180407 2660255 := bstep (se 1 (by rfl) ⟨1995191, by rfl⟩ : syracuseStep 2660255 = 3990383) B3990383
theorem B2275271 : Blo 1180407 2275271 := bstep (se 1 (by rfl) ⟨1706453, by rfl⟩ : syracuseStep 2275271 = 3412907) B3412907
theorem B11360249 : Blo 1180407 11360249 := bstep (se 2 (by rfl) ⟨4260093, by rfl⟩ : syracuseStep 11360249 = 8520187) B8520187
theorem B9099631 : Blo 1180407 9099631 := bstep (se 1 (by rfl) ⟨6824723, by rfl⟩ : syracuseStep 9099631 = 13649447) B13649447
theorem B3987899 : Blo 1180407 3987899 := bstep (se 1 (by rfl) ⟨2990924, by rfl⟩ : syracuseStep 3987899 = 5981849) B5981849
theorem B2521543 : Blo 1180407 2521543 := bstep (se 1 (by rfl) ⟨1891157, by rfl⟩ : syracuseStep 2521543 = 3782315) B3782315
theorem B1890793 : Blo 1180407 1890793 := bstep (se 2 (by rfl) ⟨709047, by rfl⟩ : syracuseStep 1890793 = 1418095) B1418095
theorem B2128475 : Blo 1180407 2128475 := bstep (se 1 (by rfl) ⟨1596356, by rfl⟩ : syracuseStep 2128475 = 3192713) B3192713
theorem B6060673 : Blo 1180407 6060673 := bstep (se 2 (by rfl) ⟨2272752, by rfl⟩ : syracuseStep 6060673 = 4545505) B4545505
theorem B1891183 : Blo 1180407 1891183 := bstep (se 1 (by rfl) ⟨1418387, by rfl⟩ : syracuseStep 1891183 = 2836775) B2836775
theorem B4488317 : Blo 1180407 4488317 := bstep (se 3 (by rfl) ⟨841559, by rfl⟩ : syracuseStep 4488317 = 1683119) B1683119
theorem B3783905 : Blo 1180407 3783905 := bstep (se 2 (by rfl) ⟨1418964, by rfl⟩ : syracuseStep 3783905 = 2837929) B2837929
theorem B13458797 : Blo 1180407 13458797 := bstep (se 3 (by rfl) ⟨2523524, by rfl⟩ : syracuseStep 13458797 = 5047049) B5047049
theorem B5045615 : Blo 1180407 5045615 := bstep (se 1 (by rfl) ⟨3784211, by rfl⟩ : syracuseStep 5045615 = 7568423) B7568423
theorem B4259243 : Blo 1180407 4259243 := bstep (se 1 (by rfl) ⟨3194432, by rfl⟩ : syracuseStep 4259243 = 6388865) B6388865
theorem B2989487 : Blo 1180407 2989487 := bstep (se 1 (by rfl) ⟨2242115, by rfl⟩ : syracuseStep 2989487 = 4484231) B4484231
theorem B7569139 : Blo 1180407 7569139 := bstep (se 1 (by rfl) ⟨5676854, by rfl⟩ : syracuseStep 7569139 = 11353709) B11353709
theorem B2129831 : Blo 1180407 2129831 := bstep (se 1 (by rfl) ⟨1597373, by rfl⟩ : syracuseStep 2129831 = 3194747) B3194747
theorem B2990135 : Blo 1180407 2990135 := bstep (se 1 (by rfl) ⟨2242601, by rfl⟩ : syracuseStep 2990135 = 4485203) B4485203
theorem B2990267 : Blo 1180407 2990267 := bstep (se 1 (by rfl) ⟨2242700, by rfl⟩ : syracuseStep 2990267 = 4485401) B4485401
theorem B1892587 : Blo 1180407 1892587 := bstep (se 1 (by rfl) ⟨1419440, by rfl⟩ : syracuseStep 1892587 = 2838881) B2838881
theorem B12132841 : Blo 1180407 12132841 := bstep (se 2 (by rfl) ⟨4549815, by rfl⟩ : syracuseStep 12132841 = 9099631) B9099631
theorem B1516123 : Blo 1180407 1516123 := bstep (se 1 (by rfl) ⟨1137092, by rfl⟩ : syracuseStep 1516123 = 2274185) B2274185
theorem B2523935 : Blo 1180407 2523935 := bstep (se 1 (by rfl) ⟨1892951, by rfl⟩ : syracuseStep 2523935 = 3785903) B3785903
theorem B1180479 : Blo 1180407 1180479 := bstep (se 1 (by rfl) ⟨885359, by rfl⟩ : syracuseStep 1180479 = 1770719) B1770719
theorem B1180487 : Blo 1180407 1180487 := bstep (se 1 (by rfl) ⟨885365, by rfl⟩ : syracuseStep 1180487 = 1770731) B1770731
theorem B22717259 : Blo 1180407 22717259 := bstep (se 1 (by rfl) ⟨17037944, by rfl⟩ : syracuseStep 22717259 = 34075889) B34075889
theorem B23028761 : Blo 1180407 23028761 := bstep (se 2 (by rfl) ⟨8635785, by rfl⟩ : syracuseStep 23028761 = 17271571) B17271571
theorem B1180743 : Blo 1180407 1180743 := bstep (se 1 (by rfl) ⟨885557, by rfl⟩ : syracuseStep 1180743 = 1771115) B1771115
theorem B1770623 : Blo 1180407 1770623 := bstep (se 1 (by rfl) ⟨1327967, by rfl⟩ : syracuseStep 1770623 = 2655935) B2655935
theorem B1180799 : Blo 1180407 1180799 := bstep (se 1 (by rfl) ⟨885599, by rfl⟩ : syracuseStep 1180799 = 1771199) B1771199
theorem B6391007 : Blo 1180407 6391007 := bstep (se 1 (by rfl) ⟨4793255, by rfl⟩ : syracuseStep 6391007 = 9586511) B9586511
theorem B24249593 : Blo 1180407 24249593 := bstep (se 2 (by rfl) ⟨9093597, by rfl⟩ : syracuseStep 24249593 = 18187195) B18187195
theorem B1180923 : Blo 1180407 1180923 := bstep (se 1 (by rfl) ⟨885692, by rfl⟩ : syracuseStep 1180923 = 1771385) B1771385
theorem B1770761 : Blo 1180407 1770761 := bstep (se 2 (by rfl) ⟨664035, by rfl⟩ : syracuseStep 1770761 = 1328071) B1328071
theorem B1516847 : Blo 1180407 1516847 := bstep (se 1 (by rfl) ⟨1137635, by rfl⟩ : syracuseStep 1516847 = 2275271) B2275271
theorem B6817385 : Blo 1180407 6817385 := bstep (se 2 (by rfl) ⟨2556519, by rfl⟩ : syracuseStep 6817385 = 5113039) B5113039
theorem B1771241 : Blo 1180407 1771241 := bstep (se 2 (by rfl) ⟨664215, by rfl⟩ : syracuseStep 1771241 = 1328431) B1328431
theorem B1771247 : Blo 1180407 1771247 := bstep (se 1 (by rfl) ⟨1328435, by rfl⟩ : syracuseStep 1771247 = 2656871) B2656871
theorem B1181423 : Blo 1180407 1181423 := bstep (se 1 (by rfl) ⟨886067, by rfl⟩ : syracuseStep 1181423 = 1772135) B1772135
theorem B1181551 : Blo 1180407 1181551 := bstep (se 1 (by rfl) ⟨886163, by rfl⟩ : syracuseStep 1181551 = 1772327) B1772327
theorem B1771499 : Blo 1180407 1771499 := bstep (se 1 (by rfl) ⟨1328624, by rfl⟩ : syracuseStep 1771499 = 2657249) B2657249
theorem B1181767 : Blo 1180407 1181767 := bstep (se 1 (by rfl) ⟨886325, by rfl⟩ : syracuseStep 1181767 = 1772651) B1772651
theorem B2992211 : Blo 1180407 2992211 := bstep (se 1 (by rfl) ⟨2244158, by rfl⟩ : syracuseStep 2992211 = 4488317) B4488317
theorem B12126353 : Blo 1180407 12126353 := bstep (se 2 (by rfl) ⟨4547382, by rfl⟩ : syracuseStep 12126353 = 9094765) B9094765
theorem B1771751 : Blo 1180407 1771751 := bstep (se 1 (by rfl) ⟨1328813, by rfl⟩ : syracuseStep 1771751 = 2657627) B2657627
theorem B1181927 : Blo 1180407 1181927 := bstep (se 1 (by rfl) ⟨886445, by rfl⟩ : syracuseStep 1181927 = 1772891) B1772891
theorem B8972531 : Blo 1180407 8972531 := bstep (se 1 (by rfl) ⟨6729398, by rfl⟩ : syracuseStep 8972531 = 13458797) B13458797
theorem B3410171 : Blo 1180407 3410171 := bstep (se 1 (by rfl) ⟨2557628, by rfl⟩ : syracuseStep 3410171 = 5115257) B5115257
theorem B1771775 : Blo 1180407 1771775 := bstep (se 1 (by rfl) ⟨1328831, by rfl⟩ : syracuseStep 1771775 = 2657663) B2657663
theorem B1181947 : Blo 1180407 1181947 := bstep (se 1 (by rfl) ⟨886460, by rfl⟩ : syracuseStep 1181947 = 1772921) B1772921
theorem B1181951 : Blo 1180407 1181951 := bstep (se 1 (by rfl) ⟨886463, by rfl⟩ : syracuseStep 1181951 = 1772927) B1772927
theorem B1992991 : Blo 1180407 1992991 := bstep (se 1 (by rfl) ⟨1494743, by rfl⟩ : syracuseStep 1992991 = 2989487) B2989487
theorem B28723511 : Blo 1180407 28723511 := bstep (se 1 (by rfl) ⟨21542633, by rfl⟩ : syracuseStep 28723511 = 43085267) B43085267
theorem B6392171 : Blo 1180407 6392171 := bstep (se 1 (by rfl) ⟨4794128, by rfl⟩ : syracuseStep 6392171 = 9588257) B9588257
theorem B1771913 : Blo 1180407 1771913 := bstep (se 2 (by rfl) ⟨664467, by rfl⟩ : syracuseStep 1771913 = 1328935) B1328935
theorem B38292047 : Blo 1180407 38292047 := bstep (se 1 (by rfl) ⟨28719035, by rfl⟩ : syracuseStep 38292047 = 57438071) B57438071
theorem B1419887 : Blo 1180407 1419887 := bstep (se 1 (by rfl) ⟨1064915, by rfl⟩ : syracuseStep 1419887 = 2129831) B2129831
theorem B1182367 : Blo 1180407 1182367 := bstep (se 1 (by rfl) ⟨886775, by rfl⟩ : syracuseStep 1182367 = 1773551) B1773551
theorem B1182375 : Blo 1180407 1182375 := bstep (se 1 (by rfl) ⟨886781, by rfl⟩ : syracuseStep 1182375 = 1773563) B1773563
theorem B97004591 : Blo 1180407 97004591 := bstep (se 1 (by rfl) ⟨72753443, by rfl⟩ : syracuseStep 97004591 = 145506887) B145506887
theorem B1993963 : Blo 1180407 1993963 := bstep (se 1 (by rfl) ⟨1495472, by rfl⟩ : syracuseStep 1993963 = 2990945) B2990945
theorem B3362057 : Blo 1180407 3362057 := bstep (se 2 (by rfl) ⟨1260771, by rfl⟩ : syracuseStep 3362057 = 2521543) B2521543
theorem B2657609 : Blo 1180407 2657609 := bstep (se 2 (by rfl) ⟨996603, by rfl⟩ : syracuseStep 2657609 = 1993207) B1993207
theorem B7187935 : Blo 1180407 7187935 := bstep (se 1 (by rfl) ⟨5390951, by rfl⟩ : syracuseStep 7187935 = 10781903) B10781903
theorem B1773023 : Blo 1180407 1773023 := bstep (se 1 (by rfl) ⟨1329767, by rfl⟩ : syracuseStep 1773023 = 2659535) B2659535
theorem B8080897 : Blo 1180407 8080897 := bstep (se 2 (by rfl) ⟨3030336, by rfl⟩ : syracuseStep 8080897 = 6060673) B6060673
theorem B1773083 : Blo 1180407 1773083 := bstep (se 1 (by rfl) ⟨1329812, by rfl⟩ : syracuseStep 1773083 = 2659625) B2659625
theorem B2657951 : Blo 1180407 2657951 := bstep (se 1 (by rfl) ⟨1993463, by rfl⟩ : syracuseStep 2657951 = 3986927) B3986927
theorem B1773215 : Blo 1180407 1773215 := bstep (se 1 (by rfl) ⟨1329911, by rfl⟩ : syracuseStep 1773215 = 2659823) B2659823
theorem B6475511 : Blo 1180407 6475511 := bstep (se 1 (by rfl) ⟨4856633, by rfl⟩ : syracuseStep 6475511 = 9713267) B9713267
theorem B11357981 : Blo 1180407 11357981 := bstep (se 3 (by rfl) ⟨2129621, by rfl⟩ : syracuseStep 11357981 = 4259243) B4259243
theorem B7180103 : Blo 1180407 7180103 := bstep (se 1 (by rfl) ⟨5385077, by rfl⟩ : syracuseStep 7180103 = 10770155) B10770155
theorem B1773479 : Blo 1180407 1773479 := bstep (se 1 (by rfl) ⟨1330109, by rfl⟩ : syracuseStep 1773479 = 2660219) B2660219
theorem B1773503 : Blo 1180407 1773503 := bstep (se 1 (by rfl) ⟨1330127, by rfl⟩ : syracuseStep 1773503 = 2660255) B2660255
theorem B13447133 : Blo 1180407 13447133 := bstep (se 3 (by rfl) ⟨2521337, by rfl⟩ : syracuseStep 13447133 = 5042675) B5042675
theorem B7573499 : Blo 1180407 7573499 := bstep (se 1 (by rfl) ⟨5680124, by rfl⟩ : syracuseStep 7573499 = 11360249) B11360249
theorem B2658401 : Blo 1180407 2658401 := bstep (se 2 (by rfl) ⟨996900, by rfl⟩ : syracuseStep 2658401 = 1993801) B1993801
theorem B8974475 : Blo 1180407 8974475 := bstep (se 1 (by rfl) ⟨6730856, by rfl⟩ : syracuseStep 8974475 = 13461713) B13461713
theorem B2658599 : Blo 1180407 2658599 := bstep (se 1 (by rfl) ⟨1993949, by rfl⟩ : syracuseStep 2658599 = 3987899) B3987899
theorem B1995131 : Blo 1180407 1995131 := bstep (se 1 (by rfl) ⟨1496348, by rfl⟩ : syracuseStep 1995131 = 2992697) B2992697
theorem B10088873 : Blo 1180407 10088873 := bstep (se 2 (by rfl) ⟨3783327, by rfl⟩ : syracuseStep 10088873 = 7566655) B7566655
theorem B3363743 : Blo 1180407 3363743 := bstep (se 1 (by rfl) ⟨2522807, by rfl⟩ : syracuseStep 3363743 = 5045615) B5045615
theorem B13448591 : Blo 1180407 13448591 := bstep (se 1 (by rfl) ⟨10086443, by rfl⟩ : syracuseStep 13448591 = 20172887) B20172887
theorem B2659751 : Blo 1180407 2659751 := bstep (se 1 (by rfl) ⟨1994813, by rfl⟩ : syracuseStep 2659751 = 3989627) B3989627
theorem B6722999 : Blo 1180407 6722999 := bstep (se 1 (by rfl) ⟨5042249, by rfl⟩ : syracuseStep 6722999 = 10084499) B10084499
theorem B2659859 : Blo 1180407 2659859 := bstep (se 1 (by rfl) ⟨1994894, by rfl⟩ : syracuseStep 2659859 = 3989789) B3989789
theorem B2659931 : Blo 1180407 2659931 := bstep (se 1 (by rfl) ⟨1994948, by rfl⟩ : syracuseStep 2659931 = 3989897) B3989897
theorem B3192539 : Blo 1180407 3192539 := bstep (se 1 (by rfl) ⟨2394404, by rfl⟩ : syracuseStep 3192539 = 4788809) B4788809
theorem B10090271 : Blo 1180407 10090271 := bstep (se 1 (by rfl) ⟨7567703, by rfl⟩ : syracuseStep 10090271 = 15135407) B15135407
theorem B13457339 : Blo 1180407 13457339 := bstep (se 1 (by rfl) ⟨10093004, by rfl⟩ : syracuseStep 13457339 = 20186009) B20186009
theorem B8968157 : Blo 1180407 8968157 := bstep (se 3 (by rfl) ⟨1681529, by rfl⟩ : syracuseStep 8968157 = 3363059) B3363059
theorem B2521057 : Blo 1180407 2521057 := bstep (se 2 (by rfl) ⟨945396, by rfl⟩ : syracuseStep 2521057 = 1890793) B1890793
theorem B6723931 : Blo 1180407 6723931 := bstep (se 1 (by rfl) ⟨5042948, by rfl⟩ : syracuseStep 6723931 = 10085897) B10085897
theorem B2521577 : Blo 1180407 2521577 := bstep (se 2 (by rfl) ⟨945591, by rfl⟩ : syracuseStep 2521577 = 1891183) B1891183
theorem B3365383 : Blo 1180407 3365383 := bstep (se 1 (by rfl) ⟨2524037, by rfl⟩ : syracuseStep 3365383 = 5048075) B5048075
theorem B2988647 : Blo 1180407 2988647 := bstep (se 1 (by rfl) ⟨2241485, by rfl⟩ : syracuseStep 2988647 = 4482971) B4482971
theorem B2988809 : Blo 1180407 2988809 := bstep (se 2 (by rfl) ⟨1120803, by rfl⟩ : syracuseStep 2988809 = 2241607) B2241607
theorem B5675933 : Blo 1180407 5675933 := bstep (se 3 (by rfl) ⟨1064237, by rfl⟩ : syracuseStep 5675933 = 2128475) B2128475
theorem B34086035 : Blo 1180407 34086035 := bstep (se 1 (by rfl) ⟨25564526, by rfl⟩ : syracuseStep 34086035 = 51129053) B51129053
theorem B28728569 : Blo 1180407 28728569 := bstep (se 2 (by rfl) ⟨10773213, by rfl⟩ : syracuseStep 28728569 = 21546427) B21546427
theorem B6724889 : Blo 1180407 6724889 := bstep (se 2 (by rfl) ⟨2521833, by rfl⟩ : syracuseStep 6724889 = 5043667) B5043667
theorem B2522603 : Blo 1180407 2522603 := bstep (se 1 (by rfl) ⟨1891952, by rfl⟩ : syracuseStep 2522603 = 3783905) B3783905
theorem B10092185 : Blo 1180407 10092185 := bstep (se 2 (by rfl) ⟨3784569, by rfl⟩ : syracuseStep 10092185 = 7569139) B7569139
theorem B30285575 : Blo 1180407 30285575 := bstep (se 1 (by rfl) ⟨22714181, by rfl⟩ : syracuseStep 30285575 = 45428363) B45428363
theorem B9576319 : Blo 1180407 9576319 := bstep (se 1 (by rfl) ⟨7182239, by rfl⟩ : syracuseStep 9576319 = 14364479) B14364479
theorem B6725915 : Blo 1180407 6725915 := bstep (se 1 (by rfl) ⟨5044436, by rfl⟩ : syracuseStep 6725915 = 10088873) B10088873
theorem B2523449 : Blo 1180407 2523449 := bstep (se 2 (by rfl) ⟨946293, by rfl⟩ : syracuseStep 2523449 = 1892587) B1892587
theorem B8085989 : Blo 1180407 8085989 := bstep (se 4 (by rfl) ⟨758061, by rfl⟩ : syracuseStep 8085989 = 1516123) B1516123
theorem B15352507 : Blo 1180407 15352507 := bstep (se 1 (by rfl) ⟨11514380, by rfl⟩ : syracuseStep 15352507 = 23028761) B23028761
theorem B1180415 : Blo 1180407 1180415 := bstep (se 1 (by rfl) ⟨885311, by rfl⟩ : syracuseStep 1180415 = 1770623) B1770623
theorem B4260671 : Blo 1180407 4260671 := bstep (se 1 (by rfl) ⟨3195503, by rfl⟩ : syracuseStep 4260671 = 6391007) B6391007
theorem B1180507 : Blo 1180407 1180507 := bstep (se 1 (by rfl) ⟨885380, by rfl⟩ : syracuseStep 1180507 = 1770761) B1770761
theorem B4481999 : Blo 1180407 4481999 := bstep (se 1 (by rfl) ⟨3361499, by rfl⟩ : syracuseStep 4481999 = 6722999) B6722999
theorem B1180827 : Blo 1180407 1180827 := bstep (se 1 (by rfl) ⟨885620, by rfl⟩ : syracuseStep 1180827 = 1771241) B1771241
theorem B1180831 : Blo 1180407 1180831 := bstep (se 1 (by rfl) ⟨885623, by rfl⟩ : syracuseStep 1180831 = 1771247) B1771247
theorem B6726847 : Blo 1180407 6726847 := bstep (se 1 (by rfl) ⟨5045135, by rfl⟩ : syracuseStep 6726847 = 10090271) B10090271
theorem B8971559 : Blo 1180407 8971559 := bstep (se 1 (by rfl) ⟨6728669, by rfl⟩ : syracuseStep 8971559 = 13457339) B13457339
theorem B1180999 : Blo 1180407 1180999 := bstep (se 1 (by rfl) ⟨885749, by rfl⟩ : syracuseStep 1180999 = 1771499) B1771499
theorem B1181167 : Blo 1180407 1181167 := bstep (se 1 (by rfl) ⟨885875, by rfl⟩ : syracuseStep 1181167 = 1771751) B1771751
theorem B5981687 : Blo 1180407 5981687 := bstep (se 1 (by rfl) ⟨4486265, by rfl⟩ : syracuseStep 5981687 = 8972531) B8972531
theorem B1181183 : Blo 1180407 1181183 := bstep (se 1 (by rfl) ⟨885887, by rfl⟩ : syracuseStep 1181183 = 1771775) B1771775
theorem B4261447 : Blo 1180407 4261447 := bstep (se 1 (by rfl) ⟨3196085, by rfl⟩ : syracuseStep 4261447 = 6392171) B6392171
theorem B1181275 : Blo 1180407 1181275 := bstep (se 1 (by rfl) ⟨885956, by rfl⟩ : syracuseStep 1181275 = 1771913) B1771913
theorem B3786365 : Blo 1180407 3786365 := bstep (se 3 (by rfl) ⟨709943, by rfl⟩ : syracuseStep 3786365 = 1419887) B1419887
theorem B25528031 : Blo 1180407 25528031 := bstep (se 1 (by rfl) ⟨19146023, by rfl⟩ : syracuseStep 25528031 = 38292047) B38292047
theorem B1992431 : Blo 1180407 1992431 := bstep (se 1 (by rfl) ⟨1494323, by rfl⟩ : syracuseStep 1992431 = 2988647) B2988647
theorem B1992539 : Blo 1180407 1992539 := bstep (se 1 (by rfl) ⟨1494404, by rfl⟩ : syracuseStep 1992539 = 2988809) B2988809
theorem B8513437 : Blo 1180407 8513437 := bstep (se 3 (by rfl) ⟨1596269, by rfl⟩ : syracuseStep 8513437 = 3192539) B3192539
theorem B10774529 : Blo 1180407 10774529 := bstep (se 2 (by rfl) ⟨4040448, by rfl⟩ : syracuseStep 10774529 = 8080897) B8080897
theorem B64669727 : Blo 1180407 64669727 := bstep (se 1 (by rfl) ⟨48502295, by rfl⟩ : syracuseStep 64669727 = 97004591) B97004591
theorem B4483259 : Blo 1180407 4483259 := bstep (se 1 (by rfl) ⟨3362444, by rfl⟩ : syracuseStep 4483259 = 6724889) B6724889
theorem B1771739 : Blo 1180407 1771739 := bstep (se 1 (by rfl) ⟨1328804, by rfl⟩ : syracuseStep 1771739 = 2657609) B2657609
theorem B1182015 : Blo 1180407 1182015 := bstep (se 1 (by rfl) ⟨886511, by rfl⟩ : syracuseStep 1182015 = 1773023) B1773023
theorem B1681735 : Blo 1180407 1681735 := bstep (se 1 (by rfl) ⟨1261301, by rfl⟩ : syracuseStep 1681735 = 2522603) B2522603
theorem B1182055 : Blo 1180407 1182055 := bstep (se 1 (by rfl) ⟨886541, by rfl⟩ : syracuseStep 1182055 = 1773083) B1773083
theorem B6728123 : Blo 1180407 6728123 := bstep (se 1 (by rfl) ⟨5046092, by rfl⟩ : syracuseStep 6728123 = 10092185) B10092185
theorem B1771967 : Blo 1180407 1771967 := bstep (se 1 (by rfl) ⟨1328975, by rfl⟩ : syracuseStep 1771967 = 2657951) B2657951
theorem B1182143 : Blo 1180407 1182143 := bstep (se 1 (by rfl) ⟨886607, by rfl⟩ : syracuseStep 1182143 = 1773215) B1773215
theorem B7571987 : Blo 1180407 7571987 := bstep (se 1 (by rfl) ⟨5678990, by rfl⟩ : syracuseStep 7571987 = 11357981) B11357981
theorem B4786735 : Blo 1180407 4786735 := bstep (se 1 (by rfl) ⟨3590051, by rfl⟩ : syracuseStep 4786735 = 7180103) B7180103
theorem B1182319 : Blo 1180407 1182319 := bstep (se 1 (by rfl) ⟨886739, by rfl⟩ : syracuseStep 1182319 = 1773479) B1773479
theorem B1182335 : Blo 1180407 1182335 := bstep (se 1 (by rfl) ⟨886751, by rfl⟩ : syracuseStep 1182335 = 1773503) B1773503
theorem B3361409 : Blo 1180407 3361409 := bstep (se 2 (by rfl) ⟨1260528, by rfl⟩ : syracuseStep 3361409 = 2521057) B2521057
theorem B8964755 : Blo 1180407 8964755 := bstep (se 1 (by rfl) ⟨6723566, by rfl⟩ : syracuseStep 8964755 = 13447133) B13447133
theorem B5048999 : Blo 1180407 5048999 := bstep (se 1 (by rfl) ⟨3786749, by rfl⟩ : syracuseStep 5048999 = 7573499) B7573499
theorem B1993423 : Blo 1180407 1993423 := bstep (se 1 (by rfl) ⟨1495067, by rfl⟩ : syracuseStep 1993423 = 2990135) B2990135
theorem B1772267 : Blo 1180407 1772267 := bstep (se 1 (by rfl) ⟨1329200, by rfl⟩ : syracuseStep 1772267 = 2658401) B2658401
theorem B5982983 : Blo 1180407 5982983 := bstep (se 1 (by rfl) ⟨4487237, by rfl⟩ : syracuseStep 5982983 = 8974475) B8974475
theorem B1993511 : Blo 1180407 1993511 := bstep (se 1 (by rfl) ⟨1495133, by rfl⟩ : syracuseStep 1993511 = 2990267) B2990267
theorem B1772399 : Blo 1180407 1772399 := bstep (se 1 (by rfl) ⟨1329299, by rfl⟩ : syracuseStep 1772399 = 2658599) B2658599
theorem B1330087 : Blo 1180407 1330087 := bstep (se 1 (by rfl) ⟨997565, by rfl⟩ : syracuseStep 1330087 = 1995131) B1995131
theorem B2657321 : Blo 1180407 2657321 := bstep (se 2 (by rfl) ⟨996495, by rfl⟩ : syracuseStep 2657321 = 1992991) B1992991
theorem B32336941 : Blo 1180407 32336941 := bstep (se 3 (by rfl) ⟨6063176, by rfl⟩ : syracuseStep 32336941 = 12126353) B12126353
theorem B8965241 : Blo 1180407 8965241 := bstep (se 2 (by rfl) ⟨3361965, by rfl⟩ : syracuseStep 8965241 = 6723931) B6723931
theorem B1682623 : Blo 1180407 1682623 := bstep (se 1 (by rfl) ⟨1261967, by rfl⟩ : syracuseStep 1682623 = 2523935) B2523935
theorem B16166395 : Blo 1180407 16166395 := bstep (se 1 (by rfl) ⟨12124796, by rfl⟩ : syracuseStep 16166395 = 24249593) B24249593
theorem B8965727 : Blo 1180407 8965727 := bstep (se 1 (by rfl) ⟨6724295, by rfl⟩ : syracuseStep 8965727 = 13448591) B13448591
theorem B1773167 : Blo 1180407 1773167 := bstep (se 1 (by rfl) ⟨1329875, by rfl⟩ : syracuseStep 1773167 = 2659751) B2659751
theorem B1773239 : Blo 1180407 1773239 := bstep (se 1 (by rfl) ⟨1329929, by rfl⟩ : syracuseStep 1773239 = 2659859) B2659859
theorem B1773287 : Blo 1180407 1773287 := bstep (se 1 (by rfl) ⟨1329965, by rfl⟩ : syracuseStep 1773287 = 2659931) B2659931
theorem B1994807 : Blo 1180407 1994807 := bstep (se 1 (by rfl) ⟨1496105, by rfl⟩ : syracuseStep 1994807 = 2992211) B2992211
theorem B2273447 : Blo 1180407 2273447 := bstep (se 1 (by rfl) ⟨1705085, by rfl⟩ : syracuseStep 2273447 = 3410171) B3410171
theorem B19149007 : Blo 1180407 19149007 := bstep (se 1 (by rfl) ⟨14361755, by rfl⟩ : syracuseStep 19149007 = 28723511) B28723511
theorem B2658617 : Blo 1180407 2658617 := bstep (se 2 (by rfl) ⟨996981, by rfl⟩ : syracuseStep 2658617 = 1993963) B1993963
theorem B2241371 : Blo 1180407 2241371 := bstep (se 1 (by rfl) ⟨1681028, by rfl⟩ : syracuseStep 2241371 = 3362057) B3362057
theorem B12768425 : Blo 1180407 12768425 := bstep (se 2 (by rfl) ⟨4788159, by rfl⟩ : syracuseStep 12768425 = 9576319) B9576319
theorem B20190383 : Blo 1180407 20190383 := bstep (se 1 (by rfl) ⟨15142787, by rfl⟩ : syracuseStep 20190383 = 30285575) B30285575
theorem B15144839 : Blo 1180407 15144839 := bstep (se 1 (by rfl) ⟨11358629, by rfl⟩ : syracuseStep 15144839 = 22717259) B22717259
theorem B2242495 : Blo 1180407 2242495 := bstep (se 1 (by rfl) ⟨1681871, by rfl⟩ : syracuseStep 2242495 = 3363743) B3363743
theorem B16177121 : Blo 1180407 16177121 := bstep (se 2 (by rfl) ⟨6066420, by rfl⟩ : syracuseStep 16177121 = 12132841) B12132841
theorem B4487177 : Blo 1180407 4487177 := bstep (se 2 (by rfl) ⟨1682691, by rfl⟩ : syracuseStep 4487177 = 3365383) B3365383
theorem B4044925 : Blo 1180407 4044925 := bstep (se 3 (by rfl) ⟨758423, by rfl⟩ : syracuseStep 4044925 = 1516847) B1516847
theorem B4544923 : Blo 1180407 4544923 := bstep (se 1 (by rfl) ⟨3408692, by rfl⟩ : syracuseStep 4544923 = 6817385) B6817385
theorem B6724205 : Blo 1180407 6724205 := bstep (se 3 (by rfl) ⟨1260788, by rfl⟩ : syracuseStep 6724205 = 2521577) B2521577
theorem B5978771 : Blo 1180407 5978771 := bstep (se 1 (by rfl) ⟨4484078, by rfl⟩ : syracuseStep 5978771 = 8968157) B8968157
theorem B3783955 : Blo 1180407 3783955 := bstep (se 1 (by rfl) ⟨2837966, by rfl⟩ : syracuseStep 3783955 = 5675933) B5675933
theorem B9583913 : Blo 1180407 9583913 := bstep (se 2 (by rfl) ⟨3593967, by rfl⟩ : syracuseStep 9583913 = 7187935) B7187935
theorem B17268029 : Blo 1180407 17268029 := bstep (se 3 (by rfl) ⟨3237755, by rfl⟩ : syracuseStep 17268029 = 6475511) B6475511
theorem B22724023 : Blo 1180407 22724023 := bstep (se 1 (by rfl) ⟨17043017, by rfl⟩ : syracuseStep 22724023 = 34086035) B34086035
theorem B19152379 : Blo 1180407 19152379 := bstep (se 1 (by rfl) ⟨14364284, by rfl⟩ : syracuseStep 19152379 = 28728569) B28728569
theorem B5390659 : Blo 1180407 5390659 := bstep (se 1 (by rfl) ⟨4042994, by rfl⟩ : syracuseStep 5390659 = 8085989) B8085989
theorem B6062525 : Blo 1180407 6062525 := bstep (se 3 (by rfl) ⟨1136723, by rfl⟩ : syracuseStep 6062525 = 2273447) B2273447
theorem B6382313 : Blo 1180407 6382313 := bstep (se 2 (by rfl) ⟨2393367, by rfl⟩ : syracuseStep 6382313 = 4786735) B4786735
theorem B8512283 : Blo 1180407 8512283 := bstep (se 1 (by rfl) ⟨6384212, by rfl⟩ : syracuseStep 8512283 = 12768425) B12768425
theorem B13460255 : Blo 1180407 13460255 := bstep (se 1 (by rfl) ⟨10095191, by rfl⟩ : syracuseStep 13460255 = 20190383) B20190383
theorem B5981039 : Blo 1180407 5981039 := bstep (se 1 (by rfl) ⟨4485779, by rfl⟩ : syracuseStep 5981039 = 8971559) B8971559
theorem B2524243 : Blo 1180407 2524243 := bstep (se 1 (by rfl) ⟨1893182, by rfl⟩ : syracuseStep 2524243 = 3786365) B3786365
theorem B1328287 : Blo 1180407 1328287 := bstep (se 1 (by rfl) ⟨996215, by rfl⟩ : syracuseStep 1328287 = 1992431) B1992431
theorem B1328359 : Blo 1180407 1328359 := bstep (se 1 (by rfl) ⟨996269, by rfl⟩ : syracuseStep 1328359 = 1992539) B1992539
theorem B2991451 : Blo 1180407 2991451 := bstep (se 1 (by rfl) ⟨2243588, by rfl⟩ : syracuseStep 2991451 = 4487177) B4487177
theorem B43115921 : Blo 1180407 43115921 := bstep (se 2 (by rfl) ⟨16168470, by rfl⟩ : syracuseStep 43115921 = 32336941) B32336941
theorem B1181159 : Blo 1180407 1181159 := bstep (se 1 (by rfl) ⟨885869, by rfl⟩ : syracuseStep 1181159 = 1771739) B1771739
theorem B1181311 : Blo 1180407 1181311 := bstep (se 1 (by rfl) ⟨885983, by rfl⟩ : syracuseStep 1181311 = 1771967) B1771967
theorem B5047991 : Blo 1180407 5047991 := bstep (se 1 (by rfl) ⟨3785993, by rfl⟩ : syracuseStep 5047991 = 7571987) B7571987
theorem B4482803 : Blo 1180407 4482803 := bstep (se 1 (by rfl) ⟨3362102, by rfl⟩ : syracuseStep 4482803 = 6724205) B6724205
theorem B1181511 : Blo 1180407 1181511 := bstep (se 1 (by rfl) ⟨886133, by rfl⟩ : syracuseStep 1181511 = 1772267) B1772267
theorem B1329007 : Blo 1180407 1329007 := bstep (se 1 (by rfl) ⟨996755, by rfl⟩ : syracuseStep 1329007 = 1993511) B1993511
theorem B1181599 : Blo 1180407 1181599 := bstep (se 1 (by rfl) ⟨886199, by rfl⟩ : syracuseStep 1181599 = 1772399) B1772399
theorem B25536505 : Blo 1180407 25536505 := bstep (se 2 (by rfl) ⟨9576189, by rfl⟩ : syracuseStep 25536505 = 19152379) B19152379
theorem B21555193 : Blo 1180407 21555193 := bstep (se 2 (by rfl) ⟨8083197, by rfl⟩ : syracuseStep 21555193 = 16166395) B16166395
theorem B1771547 : Blo 1180407 1771547 := bstep (se 1 (by rfl) ⟨1328660, by rfl⟩ : syracuseStep 1771547 = 2657321) B2657321
theorem B11512019 : Blo 1180407 11512019 := bstep (se 1 (by rfl) ⟨8634014, by rfl⟩ : syracuseStep 11512019 = 17268029) B17268029
theorem B1182111 : Blo 1180407 1182111 := bstep (se 1 (by rfl) ⟨886583, by rfl⟩ : syracuseStep 1182111 = 1773167) B1773167
theorem B1182159 : Blo 1180407 1182159 := bstep (se 1 (by rfl) ⟨886619, by rfl⟩ : syracuseStep 1182159 = 1773239) B1773239
theorem B1182191 : Blo 1180407 1182191 := bstep (se 1 (by rfl) ⟨886643, by rfl⟩ : syracuseStep 1182191 = 1773287) B1773287
theorem B1329871 : Blo 1180407 1329871 := bstep (se 1 (by rfl) ⟨997403, by rfl⟩ : syracuseStep 1329871 = 1994807) B1994807
theorem B5393233 : Blo 1180407 5393233 := bstep (se 2 (by rfl) ⟨2022462, by rfl⟩ : syracuseStep 5393233 = 4044925) B4044925
theorem B4483943 : Blo 1180407 4483943 := bstep (se 1 (by rfl) ⟨3362957, by rfl⟩ : syracuseStep 4483943 = 6725915) B6725915
theorem B1682299 : Blo 1180407 1682299 := bstep (se 1 (by rfl) ⟨1261724, by rfl⟩ : syracuseStep 1682299 = 2523449) B2523449
theorem B1772411 : Blo 1180407 1772411 := bstep (se 1 (by rfl) ⟨1329308, by rfl⟩ : syracuseStep 1772411 = 2658617) B2658617
theorem B2657897 : Blo 1180407 2657897 := bstep (se 2 (by rfl) ⟨996711, by rfl⟩ : syracuseStep 2657897 = 1993423) B1993423
theorem B8973989 : Blo 1180407 8973989 := bstep (se 4 (by rfl) ⟨841311, by rfl⟩ : syracuseStep 8973989 = 1682623) B1682623
theorem B17018687 : Blo 1180407 17018687 := bstep (se 1 (by rfl) ⟨12764015, by rfl⟩ : syracuseStep 17018687 = 25528031) B25528031
theorem B1773449 : Blo 1180407 1773449 := bstep (se 2 (by rfl) ⟨665043, by rfl⟩ : syracuseStep 1773449 = 1330087) B1330087
theorem B10096559 : Blo 1180407 10096559 := bstep (se 1 (by rfl) ⟨7572419, by rfl⟩ : syracuseStep 10096559 = 15144839) B15144839
theorem B10784747 : Blo 1180407 10784747 := bstep (se 1 (by rfl) ⟨8088560, by rfl⟩ : syracuseStep 10784747 = 16177121) B16177121
theorem B4485415 : Blo 1180407 4485415 := bstep (se 1 (by rfl) ⟨3364061, by rfl⟩ : syracuseStep 4485415 = 6728123) B6728123
theorem B2240939 : Blo 1180407 2240939 := bstep (se 1 (by rfl) ⟨1680704, by rfl⟩ : syracuseStep 2240939 = 3361409) B3361409
theorem B5976503 : Blo 1180407 5976503 := bstep (se 1 (by rfl) ⟨4482377, by rfl⟩ : syracuseStep 5976503 = 8964755) B8964755
theorem B3985847 : Blo 1180407 3985847 := bstep (se 1 (by rfl) ⟨2989385, by rfl⟩ : syracuseStep 3985847 = 5978771) B5978771
theorem B30298697 : Blo 1180407 30298697 := bstep (se 2 (by rfl) ⟨11362011, by rfl⟩ : syracuseStep 30298697 = 22724023) B22724023
theorem B5976827 : Blo 1180407 5976827 := bstep (se 1 (by rfl) ⟨4482620, by rfl⟩ : syracuseStep 5976827 = 8965241) B8965241
theorem B5681929 : Blo 1180407 5681929 := bstep (se 2 (by rfl) ⟨2130723, by rfl⟩ : syracuseStep 5681929 = 4261447) B4261447
theorem B5976989 : Blo 1180407 5976989 := bstep (se 3 (by rfl) ⟨1120685, by rfl⟩ : syracuseStep 5976989 = 2241371) B2241371
theorem B5977151 : Blo 1180407 5977151 := bstep (se 1 (by rfl) ⟨4482863, by rfl⟩ : syracuseStep 5977151 = 8965727) B8965727
theorem B11351249 : Blo 1180407 11351249 := bstep (se 2 (by rfl) ⟨4256718, by rfl⟩ : syracuseStep 11351249 = 8513437) B8513437
theorem B25532009 : Blo 1180407 25532009 := bstep (se 2 (by rfl) ⟨9574503, by rfl⟩ : syracuseStep 25532009 = 19149007) B19149007
theorem B2242313 : Blo 1180407 2242313 := bstep (se 2 (by rfl) ⟨840867, by rfl⟩ : syracuseStep 2242313 = 1681735) B1681735
theorem B6059897 : Blo 1180407 6059897 := bstep (se 2 (by rfl) ⟨2272461, by rfl⟩ : syracuseStep 6059897 = 4544923) B4544923
theorem B2840447 : Blo 1180407 2840447 := bstep (se 1 (by rfl) ⟨2130335, by rfl⟩ : syracuseStep 2840447 = 4260671) B4260671
theorem B2987999 : Blo 1180407 2987999 := bstep (se 1 (by rfl) ⟨2240999, by rfl⟩ : syracuseStep 2987999 = 4481999) B4481999
theorem B20470009 : Blo 1180407 20470009 := bstep (se 2 (by rfl) ⟨7676253, by rfl⟩ : syracuseStep 20470009 = 15352507) B15352507
theorem B3987791 : Blo 1180407 3987791 := bstep (se 1 (by rfl) ⟨2990843, by rfl⟩ : syracuseStep 3987791 = 5981687) B5981687
theorem B7183019 : Blo 1180407 7183019 := bstep (se 1 (by rfl) ⟨5387264, by rfl⟩ : syracuseStep 7183019 = 10774529) B10774529
theorem B43113151 : Blo 1180407 43113151 := bstep (se 1 (by rfl) ⟨32334863, by rfl⟩ : syracuseStep 43113151 = 64669727) B64669727
theorem B2988839 : Blo 1180407 2988839 := bstep (se 1 (by rfl) ⟨2241629, by rfl⟩ : syracuseStep 2988839 = 4483259) B4483259
theorem B8969129 : Blo 1180407 8969129 := bstep (se 2 (by rfl) ⟨3363423, by rfl⟩ : syracuseStep 8969129 = 6726847) B6726847
theorem B5045273 : Blo 1180407 5045273 := bstep (se 2 (by rfl) ⟨1891977, by rfl⟩ : syracuseStep 5045273 = 3783955) B3783955
theorem B3365999 : Blo 1180407 3365999 := bstep (se 1 (by rfl) ⟨2524499, by rfl⟩ : syracuseStep 3365999 = 5048999) B5048999
theorem B3988655 : Blo 1180407 3988655 := bstep (se 1 (by rfl) ⟨2991491, by rfl⟩ : syracuseStep 3988655 = 5982983) B5982983
theorem B6389275 : Blo 1180407 6389275 := bstep (se 1 (by rfl) ⟨4791956, by rfl⟩ : syracuseStep 6389275 = 9583913) B9583913
theorem B2989993 : Blo 1180407 2989993 := bstep (se 2 (by rfl) ⟨1121247, by rfl⟩ : syracuseStep 2989993 = 2242495) B2242495
theorem B5980553 : Blo 1180407 5980553 := bstep (se 2 (by rfl) ⟨2242707, by rfl⟩ : syracuseStep 5980553 = 4485415) B4485415
theorem B57484201 : Blo 1180407 57484201 := bstep (se 2 (by rfl) ⟨21556575, by rfl⟩ : syracuseStep 57484201 = 43113151) B43113151
theorem B4039931 : Blo 1180407 4039931 := bstep (se 1 (by rfl) ⟨3029948, by rfl⟩ : syracuseStep 4039931 = 6059897) B6059897
theorem B1893631 : Blo 1180407 1893631 := bstep (se 1 (by rfl) ⟨1420223, by rfl⟩ : syracuseStep 1893631 = 2840447) B2840447
theorem B1991999 : Blo 1180407 1991999 := bstep (se 1 (by rfl) ⟨1493999, by rfl⟩ : syracuseStep 1991999 = 2987999) B2987999
theorem B1181031 : Blo 1180407 1181031 := bstep (se 1 (by rfl) ⟨885773, by rfl⟩ : syracuseStep 1181031 = 1771547) B1771547
theorem B1771049 : Blo 1180407 1771049 := bstep (se 2 (by rfl) ⟨664143, by rfl⟩ : syracuseStep 1771049 = 1328287) B1328287
theorem B1771145 : Blo 1180407 1771145 := bstep (se 2 (by rfl) ⟨664179, by rfl⟩ : syracuseStep 1771145 = 1328359) B1328359
theorem B19154717 : Blo 1180407 19154717 := bstep (se 3 (by rfl) ⟨3591509, by rfl⟩ : syracuseStep 19154717 = 7183019) B7183019
theorem B1992559 : Blo 1180407 1992559 := bstep (se 1 (by rfl) ⟨1494419, by rfl⟩ : syracuseStep 1992559 = 2988839) B2988839
theorem B1181607 : Blo 1180407 1181607 := bstep (se 1 (by rfl) ⟨886205, by rfl⟩ : syracuseStep 1181607 = 1772411) B1772411
theorem B1771931 : Blo 1180407 1771931 := bstep (se 1 (by rfl) ⟨1328948, by rfl⟩ : syracuseStep 1771931 = 2657897) B2657897
theorem B5982659 : Blo 1180407 5982659 := bstep (se 1 (by rfl) ⟨4486994, by rfl⟩ : syracuseStep 5982659 = 8973989) B8973989
theorem B1772009 : Blo 1180407 1772009 := bstep (se 2 (by rfl) ⟨664503, by rfl⟩ : syracuseStep 1772009 = 1329007) B1329007
theorem B1182299 : Blo 1180407 1182299 := bstep (se 1 (by rfl) ⟨886724, by rfl⟩ : syracuseStep 1182299 = 1773449) B1773449
theorem B34048673 : Blo 1180407 34048673 := bstep (se 2 (by rfl) ⟨12768252, by rfl⟩ : syracuseStep 34048673 = 25536505) B25536505
theorem B28740257 : Blo 1180407 28740257 := bstep (se 2 (by rfl) ⟨10777596, by rfl⟩ : syracuseStep 28740257 = 21555193) B21555193
theorem B1493959 : Blo 1180407 1493959 := bstep (se 1 (by rfl) ⟨1120469, by rfl⟩ : syracuseStep 1493959 = 2240939) B2240939
theorem B3984335 : Blo 1180407 3984335 := bstep (se 1 (by rfl) ⟨2988251, by rfl⟩ : syracuseStep 3984335 = 5976503) B5976503
theorem B2657231 : Blo 1180407 2657231 := bstep (se 1 (by rfl) ⟨1992923, by rfl⟩ : syracuseStep 2657231 = 3985847) B3985847
theorem B4041683 : Blo 1180407 4041683 := bstep (se 1 (by rfl) ⟨3031262, by rfl⟩ : syracuseStep 4041683 = 6062525) B6062525
theorem B7187545 : Blo 1180407 7187545 := bstep (se 2 (by rfl) ⟨2695329, by rfl⟩ : syracuseStep 7187545 = 5390659) B5390659
theorem B4254875 : Blo 1180407 4254875 := bstep (se 1 (by rfl) ⟨3191156, by rfl⟩ : syracuseStep 4254875 = 6382313) B6382313
theorem B3984551 : Blo 1180407 3984551 := bstep (se 1 (by rfl) ⟨2988413, by rfl⟩ : syracuseStep 3984551 = 5976827) B5976827
theorem B8973503 : Blo 1180407 8973503 := bstep (se 1 (by rfl) ⟨6730127, by rfl⟩ : syracuseStep 8973503 = 13460255) B13460255
theorem B3984659 : Blo 1180407 3984659 := bstep (se 1 (by rfl) ⟨2988494, by rfl⟩ : syracuseStep 3984659 = 5976989) B5976989
theorem B3984767 : Blo 1180407 3984767 := bstep (se 1 (by rfl) ⟨2988575, by rfl⟩ : syracuseStep 3984767 = 5977151) B5977151
theorem B1773161 : Blo 1180407 1773161 := bstep (se 2 (by rfl) ⟨664935, by rfl⟩ : syracuseStep 1773161 = 1329871) B1329871
theorem B1494875 : Blo 1180407 1494875 := bstep (se 1 (by rfl) ⟨1121156, by rfl⟩ : syracuseStep 1494875 = 2242313) B2242313
theorem B2658527 : Blo 1180407 2658527 := bstep (se 1 (by rfl) ⟨1993895, by rfl⟩ : syracuseStep 2658527 = 3987791) B3987791
theorem B3363515 : Blo 1180407 3363515 := bstep (se 1 (by rfl) ⟨2522636, by rfl⟩ : syracuseStep 3363515 = 5045273) B5045273
theorem B2659103 : Blo 1180407 2659103 := bstep (se 1 (by rfl) ⟨1994327, by rfl⟩ : syracuseStep 2659103 = 3988655) B3988655
theorem B3986657 : Blo 1180407 3986657 := bstep (se 2 (by rfl) ⟨1494996, by rfl⟩ : syracuseStep 3986657 = 2989993) B2989993
theorem B6731039 : Blo 1180407 6731039 := bstep (se 1 (by rfl) ⟨5048279, by rfl⟩ : syracuseStep 6731039 = 10096559) B10096559
theorem B7189831 : Blo 1180407 7189831 := bstep (se 1 (by rfl) ⟨5392373, by rfl⟩ : syracuseStep 7189831 = 10784747) B10784747
theorem B27293345 : Blo 1180407 27293345 := bstep (se 2 (by rfl) ⟨10235004, by rfl⟩ : syracuseStep 27293345 = 20470009) B20470009
theorem B20199131 : Blo 1180407 20199131 := bstep (se 1 (by rfl) ⟨15149348, by rfl⟩ : syracuseStep 20199131 = 30298697) B30298697
theorem B5674855 : Blo 1180407 5674855 := bstep (se 1 (by rfl) ⟨4256141, by rfl⟩ : syracuseStep 5674855 = 8512283) B8512283
theorem B3987359 : Blo 1180407 3987359 := bstep (se 1 (by rfl) ⟨2990519, by rfl⟩ : syracuseStep 3987359 = 5981039) B5981039
theorem B7567499 : Blo 1180407 7567499 := bstep (se 1 (by rfl) ⟨5675624, by rfl⟩ : syracuseStep 7567499 = 11351249) B11351249
theorem B28743947 : Blo 1180407 28743947 := bstep (se 1 (by rfl) ⟨21557960, by rfl⟩ : syracuseStep 28743947 = 43115921) B43115921
theorem B7575905 : Blo 1180407 7575905 := bstep (se 2 (by rfl) ⟨2840964, by rfl⟩ : syracuseStep 7575905 = 5681929) B5681929
theorem B17021339 : Blo 1180407 17021339 := bstep (se 1 (by rfl) ⟨12766004, by rfl⟩ : syracuseStep 17021339 = 25532009) B25532009
theorem B7190977 : Blo 1180407 7190977 := bstep (se 2 (by rfl) ⟨2696616, by rfl⟩ : syracuseStep 7190977 = 5393233) B5393233
theorem B3365327 : Blo 1180407 3365327 := bstep (se 1 (by rfl) ⟨2523995, by rfl⟩ : syracuseStep 3365327 = 5047991) B5047991
theorem B2988535 : Blo 1180407 2988535 := bstep (se 1 (by rfl) ⟨2241401, by rfl⟩ : syracuseStep 2988535 = 4482803) B4482803
theorem B2243065 : Blo 1180407 2243065 := bstep (se 2 (by rfl) ⟨841149, by rfl⟩ : syracuseStep 2243065 = 1682299) B1682299
theorem B3365657 : Blo 1180407 3365657 := bstep (se 2 (by rfl) ⟨1262121, by rfl⟩ : syracuseStep 3365657 = 2524243) B2524243
theorem B7674679 : Blo 1180407 7674679 := bstep (se 1 (by rfl) ⟨5756009, by rfl⟩ : syracuseStep 7674679 = 11512019) B11512019
theorem B3988601 : Blo 1180407 3988601 := bstep (se 2 (by rfl) ⟨1495725, by rfl⟩ : syracuseStep 3988601 = 2991451) B2991451
theorem B2989295 : Blo 1180407 2989295 := bstep (se 1 (by rfl) ⟨2241971, by rfl⟩ : syracuseStep 2989295 = 4483943) B4483943
theorem B5979419 : Blo 1180407 5979419 := bstep (se 1 (by rfl) ⟨4484564, by rfl⟩ : syracuseStep 5979419 = 8969129) B8969129
theorem B8519033 : Blo 1180407 8519033 := bstep (se 2 (by rfl) ⟨3194637, by rfl⟩ : syracuseStep 8519033 = 6389275) B6389275
theorem B2243999 : Blo 1180407 2243999 := bstep (se 1 (by rfl) ⟨1682999, by rfl⟩ : syracuseStep 2243999 = 3365999) B3365999
theorem B11345791 : Blo 1180407 11345791 := bstep (se 1 (by rfl) ⟨8509343, by rfl⟩ : syracuseStep 11345791 = 17018687) B17018687
theorem B2990753 : Blo 1180407 2990753 := bstep (se 2 (by rfl) ⟨1121532, by rfl⟩ : syracuseStep 2990753 = 2243065) B2243065
theorem B1327999 : Blo 1180407 1327999 := bstep (se 1 (by rfl) ⟨995999, by rfl⟩ : syracuseStep 1327999 = 1991999) B1991999
theorem B1180699 : Blo 1180407 1180699 := bstep (se 1 (by rfl) ⟨885524, by rfl⟩ : syracuseStep 1180699 = 1771049) B1771049
theorem B10232905 : Blo 1180407 10232905 := bstep (se 2 (by rfl) ⟨3837339, by rfl⟩ : syracuseStep 10232905 = 7674679) B7674679
theorem B1180763 : Blo 1180407 1180763 := bstep (se 1 (by rfl) ⟨885572, by rfl⟩ : syracuseStep 1180763 = 1771145) B1771145
theorem B18195563 : Blo 1180407 18195563 := bstep (se 1 (by rfl) ⟨13646672, by rfl⟩ : syracuseStep 18195563 = 27293345) B27293345
theorem B76645601 : Blo 1180407 76645601 := bstep (se 2 (by rfl) ⟨28742100, by rfl⟩ : syracuseStep 76645601 = 57484201) B57484201
theorem B1991945 : Blo 1180407 1991945 := bstep (se 2 (by rfl) ⟨746979, by rfl⟩ : syracuseStep 1991945 = 1493959) B1493959
theorem B19162631 : Blo 1180407 19162631 := bstep (se 1 (by rfl) ⟨14371973, by rfl⟩ : syracuseStep 19162631 = 28743947) B28743947
theorem B11347559 : Blo 1180407 11347559 := bstep (se 1 (by rfl) ⟨8510669, by rfl⟩ : syracuseStep 11347559 = 17021339) B17021339
theorem B1181287 : Blo 1180407 1181287 := bstep (se 1 (by rfl) ⟨885965, by rfl⟩ : syracuseStep 1181287 = 1771931) B1771931
theorem B1181339 : Blo 1180407 1181339 := bstep (se 1 (by rfl) ⟨886004, by rfl⟩ : syracuseStep 1181339 = 1772009) B1772009
theorem B2524841 : Blo 1180407 2524841 := bstep (se 2 (by rfl) ⟨946815, by rfl⟩ : syracuseStep 2524841 = 1893631) B1893631
theorem B9586441 : Blo 1180407 9586441 := bstep (se 2 (by rfl) ⟨3594915, by rfl⟩ : syracuseStep 9586441 = 7189831) B7189831
theorem B2656223 : Blo 1180407 2656223 := bstep (se 1 (by rfl) ⟨1992167, by rfl⟩ : syracuseStep 2656223 = 3984335) B3984335
theorem B1771487 : Blo 1180407 1771487 := bstep (se 1 (by rfl) ⟨1328615, by rfl⟩ : syracuseStep 1771487 = 2657231) B2657231
theorem B2836583 : Blo 1180407 2836583 := bstep (se 1 (by rfl) ⟨2127437, by rfl⟩ : syracuseStep 2836583 = 4254875) B4254875
theorem B2656367 : Blo 1180407 2656367 := bstep (se 1 (by rfl) ⟨1992275, by rfl⟩ : syracuseStep 2656367 = 3984551) B3984551
theorem B5982335 : Blo 1180407 5982335 := bstep (se 1 (by rfl) ⟨4486751, by rfl⟩ : syracuseStep 5982335 = 8973503) B8973503
theorem B1992863 : Blo 1180407 1992863 := bstep (se 1 (by rfl) ⟨1494647, by rfl⟩ : syracuseStep 1992863 = 2989295) B2989295
theorem B2656439 : Blo 1180407 2656439 := bstep (se 1 (by rfl) ⟨1992329, by rfl⟩ : syracuseStep 2656439 = 3984659) B3984659
theorem B5679355 : Blo 1180407 5679355 := bstep (se 1 (by rfl) ⟨4259516, by rfl⟩ : syracuseStep 5679355 = 8519033) B8519033
theorem B2656511 : Blo 1180407 2656511 := bstep (se 1 (by rfl) ⟨1992383, by rfl⟩ : syracuseStep 2656511 = 3984767) B3984767
theorem B1182107 : Blo 1180407 1182107 := bstep (se 1 (by rfl) ⟨886580, by rfl⟩ : syracuseStep 1182107 = 1773161) B1773161
theorem B2656745 : Blo 1180407 2656745 := bstep (se 2 (by rfl) ⟨996279, by rfl⟩ : syracuseStep 2656745 = 1992559) B1992559
theorem B1772351 : Blo 1180407 1772351 := bstep (se 1 (by rfl) ⟨1329263, by rfl⟩ : syracuseStep 1772351 = 2658527) B2658527
theorem B1772735 : Blo 1180407 1772735 := bstep (se 1 (by rfl) ⟨1329551, by rfl⟩ : syracuseStep 1772735 = 2659103) B2659103
theorem B9587969 : Blo 1180407 9587969 := bstep (se 2 (by rfl) ⟨3595488, by rfl⟩ : syracuseStep 9587969 = 7190977) B7190977
theorem B3984713 : Blo 1180407 3984713 := bstep (se 2 (by rfl) ⟨1494267, by rfl⟩ : syracuseStep 3984713 = 2988535) B2988535
theorem B2657771 : Blo 1180407 2657771 := bstep (se 1 (by rfl) ⟨1993328, by rfl⟩ : syracuseStep 2657771 = 3986657) B3986657
theorem B2658239 : Blo 1180407 2658239 := bstep (se 1 (by rfl) ⟨1993679, by rfl⟩ : syracuseStep 2658239 = 3987359) B3987359
theorem B5050603 : Blo 1180407 5050603 := bstep (se 1 (by rfl) ⟨3787952, by rfl⟩ : syracuseStep 5050603 = 7575905) B7575905
theorem B2659067 : Blo 1180407 2659067 := bstep (se 1 (by rfl) ⟨1994300, by rfl⟩ : syracuseStep 2659067 = 3988601) B3988601
theorem B3986279 : Blo 1180407 3986279 := bstep (se 1 (by rfl) ⟨2989709, by rfl⟩ : syracuseStep 3986279 = 5979419) B5979419
theorem B3986333 : Blo 1180407 3986333 := bstep (se 3 (by rfl) ⟨747437, by rfl⟩ : syracuseStep 3986333 = 1494875) B1494875
theorem B1495999 : Blo 1180407 1495999 := bstep (se 1 (by rfl) ⟨1121999, by rfl⟩ : syracuseStep 1495999 = 2243999) B2243999
theorem B7566473 : Blo 1180407 7566473 := bstep (se 2 (by rfl) ⟨2837427, by rfl⟩ : syracuseStep 7566473 = 5674855) B5674855
theorem B15127721 : Blo 1180407 15127721 := bstep (se 2 (by rfl) ⟨5672895, by rfl⟩ : syracuseStep 15127721 = 11345791) B11345791
theorem B3987035 : Blo 1180407 3987035 := bstep (se 1 (by rfl) ⟨2990276, by rfl⟩ : syracuseStep 3987035 = 5980553) B5980553
theorem B2242343 : Blo 1180407 2242343 := bstep (se 1 (by rfl) ⟨1681757, by rfl⟩ : syracuseStep 2242343 = 3363515) B3363515
theorem B2693287 : Blo 1180407 2693287 := bstep (se 1 (by rfl) ⟨2019965, by rfl⟩ : syracuseStep 2693287 = 4039931) B4039931
theorem B4487359 : Blo 1180407 4487359 := bstep (se 1 (by rfl) ⟨3365519, by rfl⟩ : syracuseStep 4487359 = 6731039) B6731039
theorem B13466087 : Blo 1180407 13466087 := bstep (se 1 (by rfl) ⟨10099565, by rfl⟩ : syracuseStep 13466087 = 20199131) B20199131
theorem B12769811 : Blo 1180407 12769811 := bstep (se 1 (by rfl) ⟨9577358, by rfl⟩ : syracuseStep 12769811 = 19154717) B19154717
theorem B5044999 : Blo 1180407 5044999 := bstep (se 1 (by rfl) ⟨3783749, by rfl⟩ : syracuseStep 5044999 = 7567499) B7567499
theorem B9583393 : Blo 1180407 9583393 := bstep (se 2 (by rfl) ⟨3593772, by rfl⟩ : syracuseStep 9583393 = 7187545) B7187545
theorem B3988439 : Blo 1180407 3988439 := bstep (se 1 (by rfl) ⟨2991329, by rfl⟩ : syracuseStep 3988439 = 5982659) B5982659
theorem B2243551 : Blo 1180407 2243551 := bstep (se 1 (by rfl) ⟨1682663, by rfl⟩ : syracuseStep 2243551 = 3365327) B3365327
theorem B22699115 : Blo 1180407 22699115 := bstep (se 1 (by rfl) ⟨17024336, by rfl⟩ : syracuseStep 22699115 = 34048673) B34048673
theorem B19160171 : Blo 1180407 19160171 := bstep (se 1 (by rfl) ⟨14370128, by rfl⟩ : syracuseStep 19160171 = 28740257) B28740257
theorem B2243771 : Blo 1180407 2243771 := bstep (se 1 (by rfl) ⟨1682828, by rfl⟩ : syracuseStep 2243771 = 3365657) B3365657
theorem B2694455 : Blo 1180407 2694455 := bstep (se 1 (by rfl) ⟨2020841, by rfl⟩ : syracuseStep 2694455 = 4041683) B4041683
theorem B48521501 : Blo 1180407 48521501 := bstep (se 3 (by rfl) ⟨9097781, by rfl⟩ : syracuseStep 48521501 = 18195563) B18195563
theorem B6734137 : Blo 1180407 6734137 := bstep (se 2 (by rfl) ⟨2525301, by rfl⟩ : syracuseStep 6734137 = 5050603) B5050603
theorem B20177261 : Blo 1180407 20177261 := bstep (se 3 (by rfl) ⟨3783236, by rfl⟩ : syracuseStep 20177261 = 7566473) B7566473
theorem B10085147 : Blo 1180407 10085147 := bstep (se 1 (by rfl) ⟨7563860, by rfl⟩ : syracuseStep 10085147 = 15127721) B15127721
theorem B1327963 : Blo 1180407 1327963 := bstep (se 1 (by rfl) ⟨995972, by rfl⟩ : syracuseStep 1327963 = 1991945) B1991945
theorem B6726665 : Blo 1180407 6726665 := bstep (se 2 (by rfl) ⟨2522499, by rfl⟩ : syracuseStep 6726665 = 5044999) B5044999
theorem B1770665 : Blo 1180407 1770665 := bstep (se 2 (by rfl) ⟨663999, by rfl⟩ : syracuseStep 1770665 = 1327999) B1327999
theorem B2991401 : Blo 1180407 2991401 := bstep (se 2 (by rfl) ⟨1121775, by rfl⟩ : syracuseStep 2991401 = 2243551) B2243551
theorem B1770815 : Blo 1180407 1770815 := bstep (se 1 (by rfl) ⟨1328111, by rfl⟩ : syracuseStep 1770815 = 2656223) B2656223
theorem B1180991 : Blo 1180407 1180991 := bstep (se 1 (by rfl) ⟨885743, by rfl⟩ : syracuseStep 1180991 = 1771487) B1771487
theorem B1770911 : Blo 1180407 1770911 := bstep (se 1 (by rfl) ⟨1328183, by rfl⟩ : syracuseStep 1770911 = 2656367) B2656367
theorem B1328575 : Blo 1180407 1328575 := bstep (se 1 (by rfl) ⟨996431, by rfl⟩ : syracuseStep 1328575 = 1992863) B1992863
theorem B1770959 : Blo 1180407 1770959 := bstep (se 1 (by rfl) ⟨1328219, by rfl⟩ : syracuseStep 1770959 = 2656439) B2656439
theorem B1771007 : Blo 1180407 1771007 := bstep (se 1 (by rfl) ⟨1328255, by rfl⟩ : syracuseStep 1771007 = 2656511) B2656511
theorem B1771163 : Blo 1180407 1771163 := bstep (se 1 (by rfl) ⟨1328372, by rfl⟩ : syracuseStep 1771163 = 2656745) B2656745
theorem B8513207 : Blo 1180407 8513207 := bstep (se 1 (by rfl) ⟨6384905, by rfl⟩ : syracuseStep 8513207 = 12769811) B12769811
theorem B1181567 : Blo 1180407 1181567 := bstep (se 1 (by rfl) ⟨886175, by rfl⟩ : syracuseStep 1181567 = 1772351) B1772351
theorem B15132743 : Blo 1180407 15132743 := bstep (se 1 (by rfl) ⟨11349557, by rfl⟩ : syracuseStep 15132743 = 22699115) B22699115
theorem B12773447 : Blo 1180407 12773447 := bstep (se 1 (by rfl) ⟨9580085, by rfl⟩ : syracuseStep 12773447 = 19160171) B19160171
theorem B1181823 : Blo 1180407 1181823 := bstep (se 1 (by rfl) ⟨886367, by rfl⟩ : syracuseStep 1181823 = 1772735) B1772735
theorem B6391979 : Blo 1180407 6391979 := bstep (se 1 (by rfl) ⟨4793984, by rfl⟩ : syracuseStep 6391979 = 9587969) B9587969
theorem B1796303 : Blo 1180407 1796303 := bstep (se 1 (by rfl) ⟨1347227, by rfl⟩ : syracuseStep 1796303 = 2694455) B2694455
theorem B2656475 : Blo 1180407 2656475 := bstep (se 1 (by rfl) ⟨1992356, by rfl⟩ : syracuseStep 2656475 = 3984713) B3984713
theorem B1771847 : Blo 1180407 1771847 := bstep (se 1 (by rfl) ⟨1328885, by rfl⟩ : syracuseStep 1771847 = 2657771) B2657771
theorem B12781921 : Blo 1180407 12781921 := bstep (se 2 (by rfl) ⟨4793220, by rfl⟩ : syracuseStep 12781921 = 9586441) B9586441
theorem B1772159 : Blo 1180407 1772159 := bstep (se 1 (by rfl) ⟨1329119, by rfl⟩ : syracuseStep 1772159 = 2658239) B2658239
theorem B3591049 : Blo 1180407 3591049 := bstep (se 2 (by rfl) ⟨1346643, by rfl⟩ : syracuseStep 3591049 = 2693287) B2693287
theorem B5983145 : Blo 1180407 5983145 := bstep (se 2 (by rfl) ⟨2243679, by rfl⟩ : syracuseStep 5983145 = 4487359) B4487359
theorem B7572473 : Blo 1180407 7572473 := bstep (se 2 (by rfl) ⟨2839677, by rfl⟩ : syracuseStep 7572473 = 5679355) B5679355
theorem B1993835 : Blo 1180407 1993835 := bstep (se 1 (by rfl) ⟨1495376, by rfl⟩ : syracuseStep 1993835 = 2990753) B2990753
theorem B1772711 : Blo 1180407 1772711 := bstep (se 1 (by rfl) ⟨1329533, by rfl⟩ : syracuseStep 1772711 = 2659067) B2659067
theorem B2657519 : Blo 1180407 2657519 := bstep (se 1 (by rfl) ⟨1993139, by rfl⟩ : syracuseStep 2657519 = 3986279) B3986279
theorem B2657555 : Blo 1180407 2657555 := bstep (se 1 (by rfl) ⟨1993166, by rfl⟩ : syracuseStep 2657555 = 3986333) B3986333
theorem B51097067 : Blo 1180407 51097067 := bstep (se 1 (by rfl) ⟨38322800, by rfl⟩ : syracuseStep 51097067 = 76645601) B76645601
theorem B12775087 : Blo 1180407 12775087 := bstep (se 1 (by rfl) ⟨9581315, by rfl⟩ : syracuseStep 12775087 = 19162631) B19162631
theorem B2658023 : Blo 1180407 2658023 := bstep (se 1 (by rfl) ⟨1993517, by rfl⟩ : syracuseStep 2658023 = 3987035) B3987035
theorem B7565039 : Blo 1180407 7565039 := bstep (se 1 (by rfl) ⟨5673779, by rfl⟩ : syracuseStep 7565039 = 11347559) B11347559
theorem B1683227 : Blo 1180407 1683227 := bstep (se 1 (by rfl) ⟨1262420, by rfl⟩ : syracuseStep 1683227 = 2524841) B2524841
theorem B1994665 : Blo 1180407 1994665 := bstep (se 2 (by rfl) ⟨747999, by rfl⟩ : syracuseStep 1994665 = 1495999) B1495999
theorem B13643873 : Blo 1180407 13643873 := bstep (se 2 (by rfl) ⟨5116452, by rfl⟩ : syracuseStep 13643873 = 10232905) B10232905
theorem B2658959 : Blo 1180407 2658959 := bstep (se 1 (by rfl) ⟨1994219, by rfl⟩ : syracuseStep 2658959 = 3988439) B3988439
theorem B1495847 : Blo 1180407 1495847 := bstep (se 1 (by rfl) ⟨1121885, by rfl⟩ : syracuseStep 1495847 = 2243771) B2243771
theorem B12777857 : Blo 1180407 12777857 := bstep (se 2 (by rfl) ⟨4791696, by rfl⟩ : syracuseStep 12777857 = 9583393) B9583393
theorem B1891055 : Blo 1180407 1891055 := bstep (se 1 (by rfl) ⟨1418291, by rfl⟩ : syracuseStep 1891055 = 2836583) B2836583
theorem B3988223 : Blo 1180407 3988223 := bstep (se 1 (by rfl) ⟨2991167, by rfl⟩ : syracuseStep 3988223 = 5982335) B5982335
theorem B8977391 : Blo 1180407 8977391 := bstep (se 1 (by rfl) ⟨6733043, by rfl⟩ : syracuseStep 8977391 = 13466087) B13466087
theorem B5979581 : Blo 1180407 5979581 := bstep (se 3 (by rfl) ⟨1121171, by rfl⟩ : syracuseStep 5979581 = 2242343) B2242343
theorem B13451507 : Blo 1180407 13451507 := bstep (se 1 (by rfl) ⟨10088630, by rfl⟩ : syracuseStep 13451507 = 20177261) B20177261
theorem B8978849 : Blo 1180407 8978849 := bstep (se 2 (by rfl) ⟨3367068, by rfl⟩ : syracuseStep 8978849 = 6734137) B6734137
theorem B1180443 : Blo 1180407 1180443 := bstep (se 1 (by rfl) ⟨885332, by rfl⟩ : syracuseStep 1180443 = 1770665) B1770665
theorem B1180543 : Blo 1180407 1180543 := bstep (se 1 (by rfl) ⟨885407, by rfl⟩ : syracuseStep 1180543 = 1770815) B1770815
theorem B1180607 : Blo 1180407 1180607 := bstep (se 1 (by rfl) ⟨885455, by rfl⟩ : syracuseStep 1180607 = 1770911) B1770911
theorem B1180639 : Blo 1180407 1180639 := bstep (se 1 (by rfl) ⟨885479, by rfl⟩ : syracuseStep 1180639 = 1770959) B1770959
theorem B1180671 : Blo 1180407 1180671 := bstep (se 1 (by rfl) ⟨885503, by rfl⟩ : syracuseStep 1180671 = 1771007) B1771007
theorem B1180775 : Blo 1180407 1180775 := bstep (se 1 (by rfl) ⟨885581, by rfl⟩ : syracuseStep 1180775 = 1771163) B1771163
theorem B1770617 : Blo 1180407 1770617 := bstep (se 2 (by rfl) ⟨663981, by rfl⟩ : syracuseStep 1770617 = 1327963) B1327963
theorem B4261319 : Blo 1180407 4261319 := bstep (se 1 (by rfl) ⟨3195989, by rfl⟩ : syracuseStep 4261319 = 6391979) B6391979
theorem B1770983 : Blo 1180407 1770983 := bstep (se 1 (by rfl) ⟨1328237, by rfl⟩ : syracuseStep 1770983 = 2656475) B2656475
theorem B1181231 : Blo 1180407 1181231 := bstep (se 1 (by rfl) ⟨885923, by rfl⟩ : syracuseStep 1181231 = 1771847) B1771847
theorem B1181439 : Blo 1180407 1181439 := bstep (se 1 (by rfl) ⟨886079, by rfl⟩ : syracuseStep 1181439 = 1772159) B1772159
theorem B1771433 : Blo 1180407 1771433 := bstep (se 2 (by rfl) ⟨664287, by rfl⟩ : syracuseStep 1771433 = 1328575) B1328575
theorem B5048315 : Blo 1180407 5048315 := bstep (se 1 (by rfl) ⟨3786236, by rfl⟩ : syracuseStep 5048315 = 7572473) B7572473
theorem B1329223 : Blo 1180407 1329223 := bstep (se 1 (by rfl) ⟨996917, by rfl⟩ : syracuseStep 1329223 = 1993835) B1993835
theorem B1181807 : Blo 1180407 1181807 := bstep (se 1 (by rfl) ⟨886355, by rfl⟩ : syracuseStep 1181807 = 1772711) B1772711
theorem B1771679 : Blo 1180407 1771679 := bstep (se 1 (by rfl) ⟨1328759, by rfl⟩ : syracuseStep 1771679 = 2657519) B2657519
theorem B1771703 : Blo 1180407 1771703 := bstep (se 1 (by rfl) ⟨1328777, by rfl⟩ : syracuseStep 1771703 = 2657555) B2657555
theorem B17033449 : Blo 1180407 17033449 := bstep (se 2 (by rfl) ⟨6387543, by rfl⟩ : syracuseStep 17033449 = 12775087) B12775087
theorem B34064711 : Blo 1180407 34064711 := bstep (se 1 (by rfl) ⟨25548533, by rfl⟩ : syracuseStep 34064711 = 51097067) B51097067
theorem B1772015 : Blo 1180407 1772015 := bstep (se 1 (by rfl) ⟨1329011, by rfl⟩ : syracuseStep 1772015 = 2658023) B2658023
theorem B9095915 : Blo 1180407 9095915 := bstep (se 1 (by rfl) ⟨6821936, by rfl⟩ : syracuseStep 9095915 = 13643873) B13643873
theorem B1772639 : Blo 1180407 1772639 := bstep (se 1 (by rfl) ⟨1329479, by rfl⟩ : syracuseStep 1772639 = 2658959) B2658959
theorem B17042561 : Blo 1180407 17042561 := bstep (se 2 (by rfl) ⟨6390960, by rfl⟩ : syracuseStep 17042561 = 12781921) B12781921
theorem B4484443 : Blo 1180407 4484443 := bstep (se 1 (by rfl) ⟨3363332, by rfl⟩ : syracuseStep 4484443 = 6726665) B6726665
theorem B1994267 : Blo 1180407 1994267 := bstep (se 1 (by rfl) ⟨1495700, by rfl⟩ : syracuseStep 1994267 = 2991401) B2991401
theorem B4788065 : Blo 1180407 4788065 := bstep (se 2 (by rfl) ⟨1795524, by rfl⟩ : syracuseStep 4788065 = 3591049) B3591049
theorem B10088495 : Blo 1180407 10088495 := bstep (se 1 (by rfl) ⟨7566371, by rfl⟩ : syracuseStep 10088495 = 15132743) B15132743
theorem B8515631 : Blo 1180407 8515631 := bstep (se 1 (by rfl) ⟨6386723, by rfl⟩ : syracuseStep 8515631 = 12773447) B12773447
theorem B2658815 : Blo 1180407 2658815 := bstep (se 1 (by rfl) ⟨1994111, by rfl⟩ : syracuseStep 2658815 = 3988223) B3988223
theorem B5984927 : Blo 1180407 5984927 := bstep (se 1 (by rfl) ⟨4488695, by rfl⟩ : syracuseStep 5984927 = 8977391) B8977391
theorem B3986387 : Blo 1180407 3986387 := bstep (se 1 (by rfl) ⟨2989790, by rfl⟩ : syracuseStep 3986387 = 5979581) B5979581
theorem B5043359 : Blo 1180407 5043359 := bstep (se 1 (by rfl) ⟨3782519, by rfl⟩ : syracuseStep 5043359 = 7565039) B7565039
theorem B2659553 : Blo 1180407 2659553 := bstep (se 2 (by rfl) ⟨997332, by rfl⟩ : syracuseStep 2659553 = 1994665) B1994665
theorem B32347667 : Blo 1180407 32347667 := bstep (se 1 (by rfl) ⟨24260750, by rfl⟩ : syracuseStep 32347667 = 48521501) B48521501
theorem B6723431 : Blo 1180407 6723431 := bstep (se 1 (by rfl) ⟨5042573, by rfl⟩ : syracuseStep 6723431 = 10085147) B10085147
theorem B4790141 : Blo 1180407 4790141 := bstep (se 3 (by rfl) ⟨898151, by rfl⟩ : syracuseStep 4790141 = 1796303) B1796303
theorem B5675471 : Blo 1180407 5675471 := bstep (se 1 (by rfl) ⟨4256603, by rfl⟩ : syracuseStep 5675471 = 8513207) B8513207
theorem B8518571 : Blo 1180407 8518571 := bstep (se 1 (by rfl) ⟨6388928, by rfl⟩ : syracuseStep 8518571 = 12777857) B12777857
theorem B1260703 : Blo 1180407 1260703 := bstep (se 1 (by rfl) ⟨945527, by rfl⟩ : syracuseStep 1260703 = 1891055) B1891055
theorem B3988763 : Blo 1180407 3988763 := bstep (se 1 (by rfl) ⟨2991572, by rfl⟩ : syracuseStep 3988763 = 5983145) B5983145
theorem B4488605 : Blo 1180407 4488605 := bstep (se 3 (by rfl) ⟨841613, by rfl⟩ : syracuseStep 4488605 = 1683227) B1683227
theorem B3988925 : Blo 1180407 3988925 := bstep (se 3 (by rfl) ⟨747923, by rfl⟩ : syracuseStep 3988925 = 1495847) B1495847
theorem B6725663 : Blo 1180407 6725663 := bstep (se 1 (by rfl) ⟨5044247, by rfl⟩ : syracuseStep 6725663 = 10088495) B10088495
theorem B5677087 : Blo 1180407 5677087 := bstep (se 1 (by rfl) ⟨4257815, by rfl⟩ : syracuseStep 5677087 = 8515631) B8515631
theorem B3989951 : Blo 1180407 3989951 := bstep (se 1 (by rfl) ⟨2992463, by rfl⟩ : syracuseStep 3989951 = 5984927) B5984927
theorem B1180411 : Blo 1180407 1180411 := bstep (se 1 (by rfl) ⟨885308, by rfl⟩ : syracuseStep 1180411 = 1770617) B1770617
theorem B1180655 : Blo 1180407 1180655 := bstep (se 1 (by rfl) ⟨885491, by rfl⟩ : syracuseStep 1180655 = 1770983) B1770983
theorem B4482287 : Blo 1180407 4482287 := bstep (se 1 (by rfl) ⟨3361715, by rfl⟩ : syracuseStep 4482287 = 6723431) B6723431
theorem B1180955 : Blo 1180407 1180955 := bstep (se 1 (by rfl) ⟨885716, by rfl⟩ : syracuseStep 1180955 = 1771433) B1771433
theorem B1181119 : Blo 1180407 1181119 := bstep (se 1 (by rfl) ⟨885839, by rfl⟩ : syracuseStep 1181119 = 1771679) B1771679
theorem B1181135 : Blo 1180407 1181135 := bstep (se 1 (by rfl) ⟨885851, by rfl⟩ : syracuseStep 1181135 = 1771703) B1771703
theorem B22709807 : Blo 1180407 22709807 := bstep (se 1 (by rfl) ⟨17032355, by rfl⟩ : syracuseStep 22709807 = 34064711) B34064711
theorem B1181343 : Blo 1180407 1181343 := bstep (se 1 (by rfl) ⟨886007, by rfl⟩ : syracuseStep 1181343 = 1772015) B1772015
theorem B6063943 : Blo 1180407 6063943 := bstep (se 1 (by rfl) ⟨4547957, by rfl⟩ : syracuseStep 6063943 = 9095915) B9095915
theorem B5679047 : Blo 1180407 5679047 := bstep (se 1 (by rfl) ⟨4259285, by rfl⟩ : syracuseStep 5679047 = 8518571) B8518571
theorem B1181759 : Blo 1180407 1181759 := bstep (se 1 (by rfl) ⟨886319, by rfl⟩ : syracuseStep 1181759 = 1772639) B1772639
theorem B2992403 : Blo 1180407 2992403 := bstep (se 1 (by rfl) ⟨2244302, by rfl⟩ : syracuseStep 2992403 = 4488605) B4488605
theorem B1329511 : Blo 1180407 1329511 := bstep (se 1 (by rfl) ⟨997133, by rfl⟩ : syracuseStep 1329511 = 1994267) B1994267
theorem B1772297 : Blo 1180407 1772297 := bstep (se 2 (by rfl) ⟨664611, by rfl⟩ : syracuseStep 1772297 = 1329223) B1329223
theorem B22711265 : Blo 1180407 22711265 := bstep (se 2 (by rfl) ⟨8516724, by rfl⟩ : syracuseStep 22711265 = 17033449) B17033449
theorem B1772543 : Blo 1180407 1772543 := bstep (se 1 (by rfl) ⟨1329407, by rfl⟩ : syracuseStep 1772543 = 2658815) B2658815
theorem B2657591 : Blo 1180407 2657591 := bstep (se 1 (by rfl) ⟨1993193, by rfl⟩ : syracuseStep 2657591 = 3986387) B3986387
theorem B3362239 : Blo 1180407 3362239 := bstep (se 1 (by rfl) ⟨2521679, by rfl⟩ : syracuseStep 3362239 = 5043359) B5043359
theorem B1773035 : Blo 1180407 1773035 := bstep (se 1 (by rfl) ⟨1329776, by rfl⟩ : syracuseStep 1773035 = 2659553) B2659553
theorem B21565111 : Blo 1180407 21565111 := bstep (se 1 (by rfl) ⟨16173833, by rfl⟩ : syracuseStep 21565111 = 32347667) B32347667
theorem B2659175 : Blo 1180407 2659175 := bstep (se 1 (by rfl) ⟨1994381, by rfl⟩ : syracuseStep 2659175 = 3988763) B3988763
theorem B2659283 : Blo 1180407 2659283 := bstep (se 1 (by rfl) ⟨1994462, by rfl⟩ : syracuseStep 2659283 = 3988925) B3988925
theorem B3192043 : Blo 1180407 3192043 := bstep (se 1 (by rfl) ⟨2394032, by rfl⟩ : syracuseStep 3192043 = 4788065) B4788065
theorem B8967671 : Blo 1180407 8967671 := bstep (se 1 (by rfl) ⟨6725753, by rfl⟩ : syracuseStep 8967671 = 13451507) B13451507
theorem B5985899 : Blo 1180407 5985899 := bstep (se 1 (by rfl) ⟨4489424, by rfl⟩ : syracuseStep 5985899 = 8978849) B8978849
theorem B6723749 : Blo 1180407 6723749 := bstep (se 4 (by rfl) ⟨630351, by rfl⟩ : syracuseStep 6723749 = 1260703) B1260703
theorem B2840879 : Blo 1180407 2840879 := bstep (se 1 (by rfl) ⟨2130659, by rfl⟩ : syracuseStep 2840879 = 4261319) B4261319
theorem B3193427 : Blo 1180407 3193427 := bstep (se 1 (by rfl) ⟨2395070, by rfl⟩ : syracuseStep 3193427 = 4790141) B4790141
theorem B3365543 : Blo 1180407 3365543 := bstep (se 1 (by rfl) ⟨2524157, by rfl⟩ : syracuseStep 3365543 = 5048315) B5048315
theorem B3783647 : Blo 1180407 3783647 := bstep (se 1 (by rfl) ⟨2837735, by rfl⟩ : syracuseStep 3783647 = 5675471) B5675471
theorem B5979257 : Blo 1180407 5979257 := bstep (se 2 (by rfl) ⟨2242221, by rfl⟩ : syracuseStep 5979257 = 4484443) B4484443
theorem B11361707 : Blo 1180407 11361707 := bstep (se 1 (by rfl) ⟨8521280, by rfl⟩ : syracuseStep 11361707 = 17042561) B17042561
theorem B7569449 : Blo 1180407 7569449 := bstep (se 2 (by rfl) ⟨2838543, by rfl⟩ : syracuseStep 7569449 = 5677087) B5677087
theorem B15139871 : Blo 1180407 15139871 := bstep (se 1 (by rfl) ⟨11354903, by rfl⟩ : syracuseStep 15139871 = 22709807) B22709807
theorem B3990599 : Blo 1180407 3990599 := bstep (se 1 (by rfl) ⟨2992949, by rfl⟩ : syracuseStep 3990599 = 5985899) B5985899
theorem B3786031 : Blo 1180407 3786031 := bstep (se 1 (by rfl) ⟨2839523, by rfl⟩ : syracuseStep 3786031 = 5679047) B5679047
theorem B4482499 : Blo 1180407 4482499 := bstep (se 1 (by rfl) ⟨3361874, by rfl⟩ : syracuseStep 4482499 = 6723749) B6723749
theorem B1181531 : Blo 1180407 1181531 := bstep (se 1 (by rfl) ⟨886148, by rfl⟩ : syracuseStep 1181531 = 1772297) B1772297
theorem B4482985 : Blo 1180407 4482985 := bstep (se 2 (by rfl) ⟨1681119, by rfl⟩ : syracuseStep 4482985 = 3362239) B3362239
theorem B15140843 : Blo 1180407 15140843 := bstep (se 1 (by rfl) ⟨11355632, by rfl⟩ : syracuseStep 15140843 = 22711265) B22711265
theorem B1181695 : Blo 1180407 1181695 := bstep (se 1 (by rfl) ⟨886271, by rfl⟩ : syracuseStep 1181695 = 1772543) B1772543
theorem B1771727 : Blo 1180407 1771727 := bstep (se 1 (by rfl) ⟨1328795, by rfl⟩ : syracuseStep 1771727 = 2657591) B2657591
theorem B1182023 : Blo 1180407 1182023 := bstep (se 1 (by rfl) ⟨886517, by rfl⟩ : syracuseStep 1182023 = 1773035) B1773035
theorem B4483775 : Blo 1180407 4483775 := bstep (se 1 (by rfl) ⟨3362831, by rfl⟩ : syracuseStep 4483775 = 6725663) B6725663
theorem B1772681 : Blo 1180407 1772681 := bstep (se 2 (by rfl) ⟨664755, by rfl⟩ : syracuseStep 1772681 = 1329511) B1329511
theorem B1772783 : Blo 1180407 1772783 := bstep (se 1 (by rfl) ⟨1329587, by rfl⟩ : syracuseStep 1772783 = 2659175) B2659175
theorem B1772855 : Blo 1180407 1772855 := bstep (se 1 (by rfl) ⟨1329641, by rfl⟩ : syracuseStep 1772855 = 2659283) B2659283
theorem B1994935 : Blo 1180407 1994935 := bstep (se 1 (by rfl) ⟨1496201, by rfl⟩ : syracuseStep 1994935 = 2992403) B2992403
theorem B4256057 : Blo 1180407 4256057 := bstep (se 2 (by rfl) ⟨1596021, by rfl⟩ : syracuseStep 4256057 = 3192043) B3192043
theorem B3986171 : Blo 1180407 3986171 := bstep (se 1 (by rfl) ⟨2989628, by rfl⟩ : syracuseStep 3986171 = 5979257) B5979257
theorem B7574471 : Blo 1180407 7574471 := bstep (se 1 (by rfl) ⟨5680853, by rfl⟩ : syracuseStep 7574471 = 11361707) B11361707
theorem B2659967 : Blo 1180407 2659967 := bstep (se 1 (by rfl) ⟨1994975, by rfl⟩ : syracuseStep 2659967 = 3989951) B3989951
theorem B7575677 : Blo 1180407 7575677 := bstep (se 3 (by rfl) ⟨1420439, by rfl⟩ : syracuseStep 7575677 = 2840879) B2840879
theorem B2988191 : Blo 1180407 2988191 := bstep (se 1 (by rfl) ⟨2241143, by rfl⟩ : syracuseStep 2988191 = 4482287) B4482287
theorem B5978447 : Blo 1180407 5978447 := bstep (se 1 (by rfl) ⟨4483835, by rfl⟩ : syracuseStep 5978447 = 8967671) B8967671
theorem B2128951 : Blo 1180407 2128951 := bstep (se 1 (by rfl) ⟨1596713, by rfl⟩ : syracuseStep 2128951 = 3193427) B3193427
theorem B2243695 : Blo 1180407 2243695 := bstep (se 1 (by rfl) ⟨1682771, by rfl⟩ : syracuseStep 2243695 = 3365543) B3365543
theorem B2522431 : Blo 1180407 2522431 := bstep (se 1 (by rfl) ⟨1891823, by rfl⟩ : syracuseStep 2522431 = 3783647) B3783647
theorem B28753481 : Blo 1180407 28753481 := bstep (se 2 (by rfl) ⟨10782555, by rfl⟩ : syracuseStep 28753481 = 21565111) B21565111
theorem B8085257 : Blo 1180407 8085257 := bstep (se 2 (by rfl) ⟨3031971, by rfl⟩ : syracuseStep 8085257 = 6063943) B6063943
theorem B5046299 : Blo 1180407 5046299 := bstep (se 1 (by rfl) ⟨3784724, by rfl⟩ : syracuseStep 5046299 = 7569449) B7569449
theorem B10093247 : Blo 1180407 10093247 := bstep (se 1 (by rfl) ⟨7569935, by rfl⟩ : syracuseStep 10093247 = 15139871) B15139871
theorem B10093895 : Blo 1180407 10093895 := bstep (se 1 (by rfl) ⟨7570421, by rfl⟩ : syracuseStep 10093895 = 15140843) B15140843
theorem B1992127 : Blo 1180407 1992127 := bstep (se 1 (by rfl) ⟨1494095, by rfl⟩ : syracuseStep 1992127 = 2988191) B2988191
theorem B1181151 : Blo 1180407 1181151 := bstep (se 1 (by rfl) ⟨885863, by rfl⟩ : syracuseStep 1181151 = 1771727) B1771727
theorem B2991593 : Blo 1180407 2991593 := bstep (se 2 (by rfl) ⟨1121847, by rfl⟩ : syracuseStep 2991593 = 2243695) B2243695
theorem B13452965 : Blo 1180407 13452965 := bstep (se 4 (by rfl) ⟨1261215, by rfl⟩ : syracuseStep 13452965 = 2522431) B2522431
theorem B5048041 : Blo 1180407 5048041 := bstep (se 2 (by rfl) ⟨1893015, by rfl⟩ : syracuseStep 5048041 = 3786031) B3786031
theorem B1181787 : Blo 1180407 1181787 := bstep (se 1 (by rfl) ⟨886340, by rfl⟩ : syracuseStep 1181787 = 1772681) B1772681
theorem B1181855 : Blo 1180407 1181855 := bstep (se 1 (by rfl) ⟨886391, by rfl⟩ : syracuseStep 1181855 = 1772783) B1772783
theorem B1181903 : Blo 1180407 1181903 := bstep (se 1 (by rfl) ⟨886427, by rfl⟩ : syracuseStep 1181903 = 1772855) B1772855
theorem B2837371 : Blo 1180407 2837371 := bstep (se 1 (by rfl) ⟨2128028, by rfl⟩ : syracuseStep 2837371 = 4256057) B4256057
theorem B2657447 : Blo 1180407 2657447 := bstep (se 1 (by rfl) ⟨1993085, by rfl⟩ : syracuseStep 2657447 = 3986171) B3986171
theorem B5049647 : Blo 1180407 5049647 := bstep (se 1 (by rfl) ⟨3787235, by rfl⟩ : syracuseStep 5049647 = 7574471) B7574471
theorem B1773311 : Blo 1180407 1773311 := bstep (se 1 (by rfl) ⟨1329983, by rfl⟩ : syracuseStep 1773311 = 2659967) B2659967
theorem B2838601 : Blo 1180407 2838601 := bstep (se 2 (by rfl) ⟨1064475, by rfl⟩ : syracuseStep 2838601 = 2128951) B2128951
theorem B5050451 : Blo 1180407 5050451 := bstep (se 1 (by rfl) ⟨3787838, by rfl⟩ : syracuseStep 5050451 = 7575677) B7575677
theorem B3985631 : Blo 1180407 3985631 := bstep (se 1 (by rfl) ⟨2989223, by rfl⟩ : syracuseStep 3985631 = 5978447) B5978447
theorem B5976665 : Blo 1180407 5976665 := bstep (se 2 (by rfl) ⟨2241249, by rfl⟩ : syracuseStep 5976665 = 4482499) B4482499
theorem B5977313 : Blo 1180407 5977313 := bstep (se 2 (by rfl) ⟨2241492, by rfl⟩ : syracuseStep 5977313 = 4482985) B4482985
theorem B2659913 : Blo 1180407 2659913 := bstep (se 2 (by rfl) ⟨997467, by rfl⟩ : syracuseStep 2659913 = 1994935) B1994935
theorem B2660399 : Blo 1180407 2660399 := bstep (se 1 (by rfl) ⟨1995299, by rfl⟩ : syracuseStep 2660399 = 3990599) B3990599
theorem B2989183 : Blo 1180407 2989183 := bstep (se 1 (by rfl) ⟨2241887, by rfl⟩ : syracuseStep 2989183 = 4483775) B4483775
theorem B19168987 : Blo 1180407 19168987 := bstep (se 1 (by rfl) ⟨14376740, by rfl⟩ : syracuseStep 19168987 = 28753481) B28753481
theorem B5390171 : Blo 1180407 5390171 := bstep (se 1 (by rfl) ⟨4042628, by rfl⟩ : syracuseStep 5390171 = 8085257) B8085257
theorem B3366967 : Blo 1180407 3366967 := bstep (se 1 (by rfl) ⟨2525225, by rfl⟩ : syracuseStep 3366967 = 5050451) B5050451
theorem B3784801 : Blo 1180407 3784801 := bstep (se 2 (by rfl) ⟨1419300, by rfl⟩ : syracuseStep 3784801 = 2838601) B2838601
theorem B2656169 : Blo 1180407 2656169 := bstep (se 2 (by rfl) ⟨996063, by rfl⟩ : syracuseStep 2656169 = 1992127) B1992127
theorem B1771631 : Blo 1180407 1771631 := bstep (se 1 (by rfl) ⟨1328723, by rfl⟩ : syracuseStep 1771631 = 2657447) B2657447
theorem B1182207 : Blo 1180407 1182207 := bstep (se 1 (by rfl) ⟨886655, by rfl⟩ : syracuseStep 1182207 = 1773311) B1773311
theorem B2657087 : Blo 1180407 2657087 := bstep (se 1 (by rfl) ⟨1992815, by rfl⟩ : syracuseStep 2657087 = 3985631) B3985631
theorem B3984443 : Blo 1180407 3984443 := bstep (se 1 (by rfl) ⟨2988332, by rfl⟩ : syracuseStep 3984443 = 5976665) B5976665
theorem B6728831 : Blo 1180407 6728831 := bstep (se 1 (by rfl) ⟨5046623, by rfl⟩ : syracuseStep 6728831 = 10093247) B10093247
theorem B3984875 : Blo 1180407 3984875 := bstep (se 1 (by rfl) ⟨2988656, by rfl⟩ : syracuseStep 3984875 = 5977313) B5977313
theorem B6729263 : Blo 1180407 6729263 := bstep (se 1 (by rfl) ⟨5046947, by rfl⟩ : syracuseStep 6729263 = 10093895) B10093895
theorem B1994395 : Blo 1180407 1994395 := bstep (se 1 (by rfl) ⟨1495796, by rfl⟩ : syracuseStep 1994395 = 2991593) B2991593
theorem B1773275 : Blo 1180407 1773275 := bstep (se 1 (by rfl) ⟨1329956, by rfl⟩ : syracuseStep 1773275 = 2659913) B2659913
theorem B1773599 : Blo 1180407 1773599 := bstep (se 1 (by rfl) ⟨1330199, by rfl⟩ : syracuseStep 1773599 = 2660399) B2660399
theorem B3985577 : Blo 1180407 3985577 := bstep (se 2 (by rfl) ⟨1494591, by rfl⟩ : syracuseStep 3985577 = 2989183) B2989183
theorem B6730721 : Blo 1180407 6730721 := bstep (se 2 (by rfl) ⟨2524020, by rfl⟩ : syracuseStep 6730721 = 5048041) B5048041
theorem B3593447 : Blo 1180407 3593447 := bstep (se 1 (by rfl) ⟨2695085, by rfl⟩ : syracuseStep 3593447 = 5390171) B5390171
theorem B3364199 : Blo 1180407 3364199 := bstep (se 1 (by rfl) ⟨2523149, by rfl⟩ : syracuseStep 3364199 = 5046299) B5046299
theorem B8968643 : Blo 1180407 8968643 := bstep (se 1 (by rfl) ⟨6726482, by rfl⟩ : syracuseStep 8968643 = 13452965) B13452965
theorem B3783161 : Blo 1180407 3783161 := bstep (se 2 (by rfl) ⟨1418685, by rfl⟩ : syracuseStep 3783161 = 2837371) B2837371
theorem B3366431 : Blo 1180407 3366431 := bstep (se 1 (by rfl) ⟨2524823, by rfl⟩ : syracuseStep 3366431 = 5049647) B5049647
theorem B25558649 : Blo 1180407 25558649 := bstep (se 2 (by rfl) ⟨9584493, by rfl⟩ : syracuseStep 25558649 = 19168987) B19168987
theorem B4489289 : Blo 1180407 4489289 := bstep (se 2 (by rfl) ⟨1683483, by rfl⟩ : syracuseStep 4489289 = 3366967) B3366967
theorem B5046401 : Blo 1180407 5046401 := bstep (se 2 (by rfl) ⟨1892400, by rfl⟩ : syracuseStep 5046401 = 3784801) B3784801
theorem B1770779 : Blo 1180407 1770779 := bstep (se 1 (by rfl) ⟨1328084, by rfl⟩ : syracuseStep 1770779 = 2656169) B2656169
theorem B1181087 : Blo 1180407 1181087 := bstep (se 1 (by rfl) ⟨885815, by rfl⟩ : syracuseStep 1181087 = 1771631) B1771631
theorem B1771391 : Blo 1180407 1771391 := bstep (se 1 (by rfl) ⟨1328543, by rfl⟩ : syracuseStep 1771391 = 2657087) B2657087
theorem B2656295 : Blo 1180407 2656295 := bstep (se 1 (by rfl) ⟨1992221, by rfl⟩ : syracuseStep 2656295 = 3984443) B3984443
theorem B2656583 : Blo 1180407 2656583 := bstep (se 1 (by rfl) ⟨1992437, by rfl⟩ : syracuseStep 2656583 = 3984875) B3984875
theorem B1182183 : Blo 1180407 1182183 := bstep (se 1 (by rfl) ⟨886637, by rfl⟩ : syracuseStep 1182183 = 1773275) B1773275
theorem B1182399 : Blo 1180407 1182399 := bstep (se 1 (by rfl) ⟨886799, by rfl⟩ : syracuseStep 1182399 = 1773599) B1773599
theorem B2657051 : Blo 1180407 2657051 := bstep (se 1 (by rfl) ⟨1992788, by rfl⟩ : syracuseStep 2657051 = 3985577) B3985577
theorem B2395631 : Blo 1180407 2395631 := bstep (se 1 (by rfl) ⟨1796723, by rfl⟩ : syracuseStep 2395631 = 3593447) B3593447
theorem B4485887 : Blo 1180407 4485887 := bstep (se 1 (by rfl) ⟨3364415, by rfl⟩ : syracuseStep 4485887 = 6728831) B6728831
theorem B2659193 : Blo 1180407 2659193 := bstep (se 2 (by rfl) ⟨997197, by rfl⟩ : syracuseStep 2659193 = 1994395) B1994395
theorem B4486175 : Blo 1180407 4486175 := bstep (se 1 (by rfl) ⟨3364631, by rfl⟩ : syracuseStep 4486175 = 6729263) B6729263
theorem B4487147 : Blo 1180407 4487147 := bstep (se 1 (by rfl) ⟨3365360, by rfl⟩ : syracuseStep 4487147 = 6730721) B6730721
theorem B2242799 : Blo 1180407 2242799 := bstep (se 1 (by rfl) ⟨1682099, by rfl⟩ : syracuseStep 2242799 = 3364199) B3364199
theorem B5979095 : Blo 1180407 5979095 := bstep (se 1 (by rfl) ⟨4484321, by rfl⟩ : syracuseStep 5979095 = 8968643) B8968643
theorem B2522107 : Blo 1180407 2522107 := bstep (se 1 (by rfl) ⟨1891580, by rfl⟩ : syracuseStep 2522107 = 3783161) B3783161
theorem B2244287 : Blo 1180407 2244287 := bstep (se 1 (by rfl) ⟨1683215, by rfl⟩ : syracuseStep 2244287 = 3366431) B3366431
theorem B17039099 : Blo 1180407 17039099 := bstep (se 1 (by rfl) ⟨12779324, by rfl⟩ : syracuseStep 17039099 = 25558649) B25558649
theorem B2990591 : Blo 1180407 2990591 := bstep (se 1 (by rfl) ⟨2242943, by rfl⟩ : syracuseStep 2990591 = 4485887) B4485887
theorem B2990783 : Blo 1180407 2990783 := bstep (se 1 (by rfl) ⟨2243087, by rfl⟩ : syracuseStep 2990783 = 4486175) B4486175
theorem B1180519 : Blo 1180407 1180519 := bstep (se 1 (by rfl) ⟨885389, by rfl⟩ : syracuseStep 1180519 = 1770779) B1770779
theorem B1180927 : Blo 1180407 1180927 := bstep (se 1 (by rfl) ⟨885695, by rfl⟩ : syracuseStep 1180927 = 1771391) B1771391
theorem B2991431 : Blo 1180407 2991431 := bstep (se 1 (by rfl) ⟨2243573, by rfl⟩ : syracuseStep 2991431 = 4487147) B4487147
theorem B1770863 : Blo 1180407 1770863 := bstep (se 1 (by rfl) ⟨1328147, by rfl⟩ : syracuseStep 1770863 = 2656295) B2656295
theorem B1771055 : Blo 1180407 1771055 := bstep (se 1 (by rfl) ⟨1328291, by rfl⟩ : syracuseStep 1771055 = 2656583) B2656583
theorem B1771367 : Blo 1180407 1771367 := bstep (se 1 (by rfl) ⟨1328525, by rfl⟩ : syracuseStep 1771367 = 2657051) B2657051
theorem B2992859 : Blo 1180407 2992859 := bstep (se 1 (by rfl) ⟨2244644, by rfl⟩ : syracuseStep 2992859 = 4489289) B4489289
theorem B1772795 : Blo 1180407 1772795 := bstep (se 1 (by rfl) ⟨1329596, by rfl⟩ : syracuseStep 1772795 = 2659193) B2659193
theorem B3362809 : Blo 1180407 3362809 := bstep (se 2 (by rfl) ⟨1261053, by rfl⟩ : syracuseStep 3362809 = 2522107) B2522107
theorem B1495199 : Blo 1180407 1495199 := bstep (se 1 (by rfl) ⟨1121399, by rfl⟩ : syracuseStep 1495199 = 2242799) B2242799
theorem B5984765 : Blo 1180407 5984765 := bstep (se 3 (by rfl) ⟨1122143, by rfl⟩ : syracuseStep 5984765 = 2244287) B2244287
theorem B3986063 : Blo 1180407 3986063 := bstep (se 1 (by rfl) ⟨2989547, by rfl⟩ : syracuseStep 3986063 = 5979095) B5979095
theorem B11359399 : Blo 1180407 11359399 := bstep (se 1 (by rfl) ⟨8519549, by rfl⟩ : syracuseStep 11359399 = 17039099) B17039099
theorem B3364267 : Blo 1180407 3364267 := bstep (se 1 (by rfl) ⟨2523200, by rfl⟩ : syracuseStep 3364267 = 5046401) B5046401
theorem B1597087 : Blo 1180407 1597087 := bstep (se 1 (by rfl) ⟨1197815, by rfl⟩ : syracuseStep 1597087 = 2395631) B2395631
theorem B3989843 : Blo 1180407 3989843 := bstep (se 1 (by rfl) ⟨2992382, by rfl⟩ : syracuseStep 3989843 = 5984765) B5984765
theorem B1180575 : Blo 1180407 1180575 := bstep (se 1 (by rfl) ⟨885431, by rfl⟩ : syracuseStep 1180575 = 1770863) B1770863
theorem B1180703 : Blo 1180407 1180703 := bstep (se 1 (by rfl) ⟨885527, by rfl⟩ : syracuseStep 1180703 = 1771055) B1771055
theorem B1180911 : Blo 1180407 1180911 := bstep (se 1 (by rfl) ⟨885683, by rfl⟩ : syracuseStep 1180911 = 1771367) B1771367
theorem B1181863 : Blo 1180407 1181863 := bstep (se 1 (by rfl) ⟨886397, by rfl⟩ : syracuseStep 1181863 = 1772795) B1772795
theorem B4483745 : Blo 1180407 4483745 := bstep (se 2 (by rfl) ⟨1681404, by rfl⟩ : syracuseStep 4483745 = 3362809) B3362809
theorem B1993727 : Blo 1180407 1993727 := bstep (se 1 (by rfl) ⟨1495295, by rfl⟩ : syracuseStep 1993727 = 2990591) B2990591
theorem B2657375 : Blo 1180407 2657375 := bstep (se 1 (by rfl) ⟨1993031, by rfl⟩ : syracuseStep 2657375 = 3986063) B3986063
theorem B1993855 : Blo 1180407 1993855 := bstep (se 1 (by rfl) ⟨1495391, by rfl⟩ : syracuseStep 1993855 = 2990783) B2990783
theorem B1994287 : Blo 1180407 1994287 := bstep (se 1 (by rfl) ⟨1495715, by rfl⟩ : syracuseStep 1994287 = 2991431) B2991431
theorem B1995239 : Blo 1180407 1995239 := bstep (se 1 (by rfl) ⟨1496429, by rfl⟩ : syracuseStep 1995239 = 2992859) B2992859
theorem B4485689 : Blo 1180407 4485689 := bstep (se 2 (by rfl) ⟨1682133, by rfl⟩ : syracuseStep 4485689 = 3364267) B3364267
theorem B3987197 : Blo 1180407 3987197 := bstep (se 3 (by rfl) ⟨747599, by rfl⟩ : syracuseStep 3987197 = 1495199) B1495199
theorem B8517797 : Blo 1180407 8517797 := bstep (se 4 (by rfl) ⟨798543, by rfl⟩ : syracuseStep 8517797 = 1597087) B1597087
theorem B15145865 : Blo 1180407 15145865 := bstep (se 2 (by rfl) ⟨5679699, by rfl⟩ : syracuseStep 15145865 = 11359399) B11359399
theorem B2990459 : Blo 1180407 2990459 := bstep (se 1 (by rfl) ⟨2242844, by rfl⟩ : syracuseStep 2990459 = 4485689) B4485689
theorem B5678531 : Blo 1180407 5678531 := bstep (se 1 (by rfl) ⟨4258898, by rfl⟩ : syracuseStep 5678531 = 8517797) B8517797
theorem B1329151 : Blo 1180407 1329151 := bstep (se 1 (by rfl) ⟨996863, by rfl⟩ : syracuseStep 1329151 = 1993727) B1993727
theorem B1771583 : Blo 1180407 1771583 := bstep (se 1 (by rfl) ⟨1328687, by rfl⟩ : syracuseStep 1771583 = 2657375) B2657375
theorem B1330159 : Blo 1180407 1330159 := bstep (se 1 (by rfl) ⟨997619, by rfl⟩ : syracuseStep 1330159 = 1995239) B1995239
theorem B2658131 : Blo 1180407 2658131 := bstep (se 1 (by rfl) ⟨1993598, by rfl⟩ : syracuseStep 2658131 = 3987197) B3987197
theorem B2658473 : Blo 1180407 2658473 := bstep (se 2 (by rfl) ⟨996927, by rfl⟩ : syracuseStep 2658473 = 1993855) B1993855
theorem B10097243 : Blo 1180407 10097243 := bstep (se 1 (by rfl) ⟨7572932, by rfl⟩ : syracuseStep 10097243 = 15145865) B15145865
theorem B2659049 : Blo 1180407 2659049 := bstep (se 2 (by rfl) ⟨997143, by rfl⟩ : syracuseStep 2659049 = 1994287) B1994287
theorem B2659895 : Blo 1180407 2659895 := bstep (se 1 (by rfl) ⟨1994921, by rfl⟩ : syracuseStep 2659895 = 3989843) B3989843
theorem B2989163 : Blo 1180407 2989163 := bstep (se 1 (by rfl) ⟨2241872, by rfl⟩ : syracuseStep 2989163 = 4483745) B4483745
theorem B3785687 : Blo 1180407 3785687 := bstep (se 1 (by rfl) ⟨2839265, by rfl⟩ : syracuseStep 3785687 = 5678531) B5678531
theorem B1181055 : Blo 1180407 1181055 := bstep (se 1 (by rfl) ⟨885791, by rfl⟩ : syracuseStep 1181055 = 1771583) B1771583
theorem B1992775 : Blo 1180407 1992775 := bstep (se 1 (by rfl) ⟨1494581, by rfl⟩ : syracuseStep 1992775 = 2989163) B2989163
theorem B1772087 : Blo 1180407 1772087 := bstep (se 1 (by rfl) ⟨1329065, by rfl⟩ : syracuseStep 1772087 = 2658131) B2658131
theorem B1772201 : Blo 1180407 1772201 := bstep (se 2 (by rfl) ⟨664575, by rfl⟩ : syracuseStep 1772201 = 1329151) B1329151
theorem B1772315 : Blo 1180407 1772315 := bstep (se 1 (by rfl) ⟨1329236, by rfl⟩ : syracuseStep 1772315 = 2658473) B2658473
theorem B1993639 : Blo 1180407 1993639 := bstep (se 1 (by rfl) ⟨1495229, by rfl⟩ : syracuseStep 1993639 = 2990459) B2990459
theorem B1772699 : Blo 1180407 1772699 := bstep (se 1 (by rfl) ⟨1329524, by rfl⟩ : syracuseStep 1772699 = 2659049) B2659049
theorem B1773263 : Blo 1180407 1773263 := bstep (se 1 (by rfl) ⟨1329947, by rfl⟩ : syracuseStep 1773263 = 2659895) B2659895
theorem B1773545 : Blo 1180407 1773545 := bstep (se 2 (by rfl) ⟨665079, by rfl⟩ : syracuseStep 1773545 = 1330159) B1330159
theorem B6731495 : Blo 1180407 6731495 := bstep (se 1 (by rfl) ⟨5048621, by rfl⟩ : syracuseStep 6731495 = 10097243) B10097243
theorem B2523791 : Blo 1180407 2523791 := bstep (se 1 (by rfl) ⟨1892843, by rfl⟩ : syracuseStep 2523791 = 3785687) B3785687
theorem B1181391 : Blo 1180407 1181391 := bstep (se 1 (by rfl) ⟨886043, by rfl⟩ : syracuseStep 1181391 = 1772087) B1772087
theorem B1181467 : Blo 1180407 1181467 := bstep (se 1 (by rfl) ⟨886100, by rfl⟩ : syracuseStep 1181467 = 1772201) B1772201
theorem B1181543 : Blo 1180407 1181543 := bstep (se 1 (by rfl) ⟨886157, by rfl⟩ : syracuseStep 1181543 = 1772315) B1772315
theorem B1181799 : Blo 1180407 1181799 := bstep (se 1 (by rfl) ⟨886349, by rfl⟩ : syracuseStep 1181799 = 1772699) B1772699
theorem B1182175 : Blo 1180407 1182175 := bstep (se 1 (by rfl) ⟨886631, by rfl⟩ : syracuseStep 1182175 = 1773263) B1773263
theorem B1182363 : Blo 1180407 1182363 := bstep (se 1 (by rfl) ⟨886772, by rfl⟩ : syracuseStep 1182363 = 1773545) B1773545
theorem B2657033 : Blo 1180407 2657033 := bstep (se 2 (by rfl) ⟨996387, by rfl⟩ : syracuseStep 2657033 = 1992775) B1992775
theorem B2658185 : Blo 1180407 2658185 := bstep (se 2 (by rfl) ⟨996819, by rfl⟩ : syracuseStep 2658185 = 1993639) B1993639
theorem B4487663 : Blo 1180407 4487663 := bstep (se 1 (by rfl) ⟨3365747, by rfl⟩ : syracuseStep 4487663 = 6731495) B6731495
theorem B2991775 : Blo 1180407 2991775 := bstep (se 1 (by rfl) ⟨2243831, by rfl⟩ : syracuseStep 2991775 = 4487663) B4487663
theorem B1771355 : Blo 1180407 1771355 := bstep (se 1 (by rfl) ⟨1328516, by rfl⟩ : syracuseStep 1771355 = 2657033) B2657033
theorem B1772123 : Blo 1180407 1772123 := bstep (se 1 (by rfl) ⟨1329092, by rfl⟩ : syracuseStep 1772123 = 2658185) B2658185
theorem B1682527 : Blo 1180407 1682527 := bstep (se 1 (by rfl) ⟨1261895, by rfl⟩ : syracuseStep 1682527 = 2523791) B2523791
theorem B1180903 : Blo 1180407 1180903 := bstep (se 1 (by rfl) ⟨885677, by rfl⟩ : syracuseStep 1180903 = 1771355) B1771355
theorem B1181415 : Blo 1180407 1181415 := bstep (se 1 (by rfl) ⟨886061, by rfl⟩ : syracuseStep 1181415 = 1772123) B1772123
theorem B2243369 : Blo 1180407 2243369 := bstep (se 2 (by rfl) ⟨841263, by rfl⟩ : syracuseStep 2243369 = 1682527) B1682527
theorem B3989033 : Blo 1180407 3989033 := bstep (se 2 (by rfl) ⟨1495887, by rfl⟩ : syracuseStep 3989033 = 2991775) B2991775
theorem B1495579 : Blo 1180407 1495579 := bstep (se 1 (by rfl) ⟨1121684, by rfl⟩ : syracuseStep 1495579 = 2243369) B2243369
theorem B2659355 : Blo 1180407 2659355 := bstep (se 1 (by rfl) ⟨1994516, by rfl⟩ : syracuseStep 2659355 = 3989033) B3989033
theorem B1772903 : Blo 1180407 1772903 := bstep (se 1 (by rfl) ⟨1329677, by rfl⟩ : syracuseStep 1772903 = 2659355) B2659355
theorem B1994105 : Blo 1180407 1994105 := bstep (se 2 (by rfl) ⟨747789, by rfl⟩ : syracuseStep 1994105 = 1495579) B1495579
theorem B1181935 : Blo 1180407 1181935 := bstep (se 1 (by rfl) ⟨886451, by rfl⟩ : syracuseStep 1181935 = 1772903) B1772903
theorem B1329403 : Blo 1180407 1329403 := bstep (se 1 (by rfl) ⟨997052, by rfl⟩ : syracuseStep 1329403 = 1994105) B1994105
theorem B1772537 : Blo 1180407 1772537 := bstep (se 2 (by rfl) ⟨664701, by rfl⟩ : syracuseStep 1772537 = 1329403) B1329403
theorem B1181691 : Blo 1180407 1181691 := bstep (se 1 (by rfl) ⟨886268, by rfl⟩ : syracuseStep 1181691 = 1772537) B1772537

theorem C0 (j : ℕ) (h1 : 295101 ≤ j) (h2 : j ≤ 295601) : Blo 1180407 (4 * j + 3) := by
  interval_cases j
  · exact B1180407
  · exact B1180411
  · exact B1180415
  · exact B1180419
  · exact B1180423
  · exact B1180427
  · exact B1180431
  · exact B1180435
  · exact B1180439
  · exact B1180443
  · exact B1180447
  · exact B1180451
  · exact B1180455
  · exact B1180459
  · exact B1180463
  · exact B1180467
  · exact B1180471
  · exact B1180475
  · exact B1180479
  · exact B1180483
  · exact B1180487
  · exact B1180491
  · exact B1180495
  · exact B1180499
  · exact B1180503
  · exact B1180507
  · exact B1180511
  · exact B1180515
  · exact B1180519
  · exact B1180523
  · exact B1180527
  · exact B1180531
  · exact B1180535
  · exact B1180539
  · exact B1180543
  · exact B1180547
  · exact B1180551
  · exact B1180555
  · exact B1180559
  · exact B1180563
  · exact B1180567
  · exact B1180571
  · exact B1180575
  · exact B1180579
  · exact B1180583
  · exact B1180587
  · exact B1180591
  · exact B1180595
  · exact B1180599
  · exact B1180603
  · exact B1180607
  · exact B1180611
  · exact B1180615
  · exact B1180619
  · exact B1180623
  · exact B1180627
  · exact B1180631
  · exact B1180635
  · exact B1180639
  · exact B1180643
  · exact B1180647
  · exact B1180651
  · exact B1180655
  · exact B1180659
  · exact B1180663
  · exact B1180667
  · exact B1180671
  · exact B1180675
  · exact B1180679
  · exact B1180683
  · exact B1180687
  · exact B1180691
  · exact B1180695
  · exact B1180699
  · exact B1180703
  · exact B1180707
  · exact B1180711
  · exact B1180715
  · exact B1180719
  · exact B1180723
  · exact B1180727
  · exact B1180731
  · exact B1180735
  · exact B1180739
  · exact B1180743
  · exact B1180747
  · exact B1180751
  · exact B1180755
  · exact B1180759
  · exact B1180763
  · exact B1180767
  · exact B1180771
  · exact B1180775
  · exact B1180779
  · exact B1180783
  · exact B1180787
  · exact B1180791
  · exact B1180795
  · exact B1180799
  · exact B1180803
  · exact B1180807
  · exact B1180811
  · exact B1180815
  · exact B1180819
  · exact B1180823
  · exact B1180827
  · exact B1180831
  · exact B1180835
  · exact B1180839
  · exact B1180843
  · exact B1180847
  · exact B1180851
  · exact B1180855
  · exact B1180859
  · exact B1180863
  · exact B1180867
  · exact B1180871
  · exact B1180875
  · exact B1180879
  · exact B1180883
  · exact B1180887
  · exact B1180891
  · exact B1180895
  · exact B1180899
  · exact B1180903
  · exact B1180907
  · exact B1180911
  · exact B1180915
  · exact B1180919
  · exact B1180923
  · exact B1180927
  · exact B1180931
  · exact B1180935
  · exact B1180939
  · exact B1180943
  · exact B1180947
  · exact B1180951
  · exact B1180955
  · exact B1180959
  · exact B1180963
  · exact B1180967
  · exact B1180971
  · exact B1180975
  · exact B1180979
  · exact B1180983
  · exact B1180987
  · exact B1180991
  · exact B1180995
  · exact B1180999
  · exact B1181003
  · exact B1181007
  · exact B1181011
  · exact B1181015
  · exact B1181019
  · exact B1181023
  · exact B1181027
  · exact B1181031
  · exact B1181035
  · exact B1181039
  · exact B1181043
  · exact B1181047
  · exact B1181051
  · exact B1181055
  · exact B1181059
  · exact B1181063
  · exact B1181067
  · exact B1181071
  · exact B1181075
  · exact B1181079
  · exact B1181083
  · exact B1181087
  · exact B1181091
  · exact B1181095
  · exact B1181099
  · exact B1181103
  · exact B1181107
  · exact B1181111
  · exact B1181115
  · exact B1181119
  · exact B1181123
  · exact B1181127
  · exact B1181131
  · exact B1181135
  · exact B1181139
  · exact B1181143
  · exact B1181147
  · exact B1181151
  · exact B1181155
  · exact B1181159
  · exact B1181163
  · exact B1181167
  · exact B1181171
  · exact B1181175
  · exact B1181179
  · exact B1181183
  · exact B1181187
  · exact B1181191
  · exact B1181195
  · exact B1181199
  · exact B1181203
  · exact B1181207
  · exact B1181211
  · exact B1181215
  · exact B1181219
  · exact B1181223
  · exact B1181227
  · exact B1181231
  · exact B1181235
  · exact B1181239
  · exact B1181243
  · exact B1181247
  · exact B1181251
  · exact B1181255
  · exact B1181259
  · exact B1181263
  · exact B1181267
  · exact B1181271
  · exact B1181275
  · exact B1181279
  · exact B1181283
  · exact B1181287
  · exact B1181291
  · exact B1181295
  · exact B1181299
  · exact B1181303
  · exact B1181307
  · exact B1181311
  · exact B1181315
  · exact B1181319
  · exact B1181323
  · exact B1181327
  · exact B1181331
  · exact B1181335
  · exact B1181339
  · exact B1181343
  · exact B1181347
  · exact B1181351
  · exact B1181355
  · exact B1181359
  · exact B1181363
  · exact B1181367
  · exact B1181371
  · exact B1181375
  · exact B1181379
  · exact B1181383
  · exact B1181387
  · exact B1181391
  · exact B1181395
  · exact B1181399
  · exact B1181403
  · exact B1181407
  · exact B1181411
  · exact B1181415
  · exact B1181419
  · exact B1181423
  · exact B1181427
  · exact B1181431
  · exact B1181435
  · exact B1181439
  · exact B1181443
  · exact B1181447
  · exact B1181451
  · exact B1181455
  · exact B1181459
  · exact B1181463
  · exact B1181467
  · exact B1181471
  · exact B1181475
  · exact B1181479
  · exact B1181483
  · exact B1181487
  · exact B1181491
  · exact B1181495
  · exact B1181499
  · exact B1181503
  · exact B1181507
  · exact B1181511
  · exact B1181515
  · exact B1181519
  · exact B1181523
  · exact B1181527
  · exact B1181531
  · exact B1181535
  · exact B1181539
  · exact B1181543
  · exact B1181547
  · exact B1181551
  · exact B1181555
  · exact B1181559
  · exact B1181563
  · exact B1181567
  · exact B1181571
  · exact B1181575
  · exact B1181579
  · exact B1181583
  · exact B1181587
  · exact B1181591
  · exact B1181595
  · exact B1181599
  · exact B1181603
  · exact B1181607
  · exact B1181611
  · exact B1181615
  · exact B1181619
  · exact B1181623
  · exact B1181627
  · exact B1181631
  · exact B1181635
  · exact B1181639
  · exact B1181643
  · exact B1181647
  · exact B1181651
  · exact B1181655
  · exact B1181659
  · exact B1181663
  · exact B1181667
  · exact B1181671
  · exact B1181675
  · exact B1181679
  · exact B1181683
  · exact B1181687
  · exact B1181691
  · exact B1181695
  · exact B1181699
  · exact B1181703
  · exact B1181707
  · exact B1181711
  · exact B1181715
  · exact B1181719
  · exact B1181723
  · exact B1181727
  · exact B1181731
  · exact B1181735
  · exact B1181739
  · exact B1181743
  · exact B1181747
  · exact B1181751
  · exact B1181755
  · exact B1181759
  · exact B1181763
  · exact B1181767
  · exact B1181771
  · exact B1181775
  · exact B1181779
  · exact B1181783
  · exact B1181787
  · exact B1181791
  · exact B1181795
  · exact B1181799
  · exact B1181803
  · exact B1181807
  · exact B1181811
  · exact B1181815
  · exact B1181819
  · exact B1181823
  · exact B1181827
  · exact B1181831
  · exact B1181835
  · exact B1181839
  · exact B1181843
  · exact B1181847
  · exact B1181851
  · exact B1181855
  · exact B1181859
  · exact B1181863
  · exact B1181867
  · exact B1181871
  · exact B1181875
  · exact B1181879
  · exact B1181883
  · exact B1181887
  · exact B1181891
  · exact B1181895
  · exact B1181899
  · exact B1181903
  · exact B1181907
  · exact B1181911
  · exact B1181915
  · exact B1181919
  · exact B1181923
  · exact B1181927
  · exact B1181931
  · exact B1181935
  · exact B1181939
  · exact B1181943
  · exact B1181947
  · exact B1181951
  · exact B1181955
  · exact B1181959
  · exact B1181963
  · exact B1181967
  · exact B1181971
  · exact B1181975
  · exact B1181979
  · exact B1181983
  · exact B1181987
  · exact B1181991
  · exact B1181995
  · exact B1181999
  · exact B1182003
  · exact B1182007
  · exact B1182011
  · exact B1182015
  · exact B1182019
  · exact B1182023
  · exact B1182027
  · exact B1182031
  · exact B1182035
  · exact B1182039
  · exact B1182043
  · exact B1182047
  · exact B1182051
  · exact B1182055
  · exact B1182059
  · exact B1182063
  · exact B1182067
  · exact B1182071
  · exact B1182075
  · exact B1182079
  · exact B1182083
  · exact B1182087
  · exact B1182091
  · exact B1182095
  · exact B1182099
  · exact B1182103
  · exact B1182107
  · exact B1182111
  · exact B1182115
  · exact B1182119
  · exact B1182123
  · exact B1182127
  · exact B1182131
  · exact B1182135
  · exact B1182139
  · exact B1182143
  · exact B1182147
  · exact B1182151
  · exact B1182155
  · exact B1182159
  · exact B1182163
  · exact B1182167
  · exact B1182171
  · exact B1182175
  · exact B1182179
  · exact B1182183
  · exact B1182187
  · exact B1182191
  · exact B1182195
  · exact B1182199
  · exact B1182203
  · exact B1182207
  · exact B1182211
  · exact B1182215
  · exact B1182219
  · exact B1182223
  · exact B1182227
  · exact B1182231
  · exact B1182235
  · exact B1182239
  · exact B1182243
  · exact B1182247
  · exact B1182251
  · exact B1182255
  · exact B1182259
  · exact B1182263
  · exact B1182267
  · exact B1182271
  · exact B1182275
  · exact B1182279
  · exact B1182283
  · exact B1182287
  · exact B1182291
  · exact B1182295
  · exact B1182299
  · exact B1182303
  · exact B1182307
  · exact B1182311
  · exact B1182315
  · exact B1182319
  · exact B1182323
  · exact B1182327
  · exact B1182331
  · exact B1182335
  · exact B1182339
  · exact B1182343
  · exact B1182347
  · exact B1182351
  · exact B1182355
  · exact B1182359
  · exact B1182363
  · exact B1182367
  · exact B1182371
  · exact B1182375
  · exact B1182379
  · exact B1182383
  · exact B1182387
  · exact B1182391
  · exact B1182395
  · exact B1182399
  · exact B1182403
  · exact B1182407

theorem solution (m : ℕ) (hlo : 1180407 ≤ m) (hhi : m ≤ 1182407) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 295101 ≤ j := by omega
    have hj2 : j ≤ 295601 := by omega
    have hb : Blo 1180407 (4 * j + 3) := by
      exact C0 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
