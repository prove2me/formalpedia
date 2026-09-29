-- Prove2me | solution 1 for syracuse_descends_range_1482061_1484061
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-09T22:45:57.94588+00:00
-- url     : https://prove2.me/submissions/5b296e86-3e7b-4819-89a2-65113d2e399e

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


theorem B11264021 : Blo 1482061 11264021 := bbase (se 6 (by rfl) ⟨264000, by rfl⟩ : syracuseStep 11264021 = 528001) (by norm_num)
theorem B7512101 : Blo 1482061 7512101 := bbase (se 4 (by rfl) ⟨704259, by rfl⟩ : syracuseStep 7512101 = 1408519) (by norm_num)
theorem B3752021 : Blo 1482061 3752021 := bbase (se 8 (by rfl) ⟨21984, by rfl⟩ : syracuseStep 3752021 = 43969) (by norm_num)
theorem B1876061 : Blo 1482061 1876061 := bbase (se 3 (by rfl) ⟨351761, by rfl⟩ : syracuseStep 1876061 = 703523) (by norm_num)
theorem B1876117 : Blo 1482061 1876117 := bbase (se 6 (by rfl) ⟨43971, by rfl⟩ : syracuseStep 1876117 = 87943) (by norm_num)
theorem B3383461 : Blo 1482061 3383461 := bbase (se 4 (by rfl) ⟨317199, by rfl⟩ : syracuseStep 3383461 = 634399) (by norm_num)
theorem B1876213 : Blo 1482061 1876213 := bbase (se 5 (by rfl) ⟨87947, by rfl⟩ : syracuseStep 1876213 = 175895) (by norm_num)
theorem B3563797 : Blo 1482061 3563797 := bbase (se 6 (by rfl) ⟨83526, by rfl⟩ : syracuseStep 3563797 = 167053) (by norm_num)
theorem B5005637 : Blo 1482061 5005637 := bbase (se 4 (by rfl) ⟨469278, by rfl⟩ : syracuseStep 5005637 = 938557) (by norm_num)
theorem B1876385 : Blo 1482061 1876385 := bbase (se 2 (by rfl) ⟨703644, by rfl⟩ : syracuseStep 1876385 = 1407289) (by norm_num)
theorem B3752365 : Blo 1482061 3752365 := bbase (se 3 (by rfl) ⟨703568, by rfl⟩ : syracuseStep 3752365 = 1407137) (by norm_num)
theorem B11256245 : Blo 1482061 11256245 := bbase (se 5 (by rfl) ⟨527636, by rfl⟩ : syracuseStep 11256245 = 1055273) (by norm_num)
theorem B7504325 : Blo 1482061 7504325 := bbase (se 4 (by rfl) ⟨703530, by rfl⟩ : syracuseStep 7504325 = 1407061) (by norm_num)
theorem B1876441 : Blo 1482061 1876441 := bbase (se 2 (by rfl) ⟨703665, by rfl⟩ : syracuseStep 1876441 = 1407331) (by norm_num)
theorem B5071349 : Blo 1482061 5071349 := bbase (se 5 (by rfl) ⟨237719, by rfl⟩ : syracuseStep 5071349 = 475439) (by norm_num)
theorem B3334661 : Blo 1482061 3334661 := bbase (se 4 (by rfl) ⟨312624, by rfl⟩ : syracuseStep 3334661 = 625249) (by norm_num)
theorem B3752477 : Blo 1482061 3752477 := bbase (se 3 (by rfl) ⟨703589, by rfl⟩ : syracuseStep 3752477 = 1407179) (by norm_num)
theorem B5341733 : Blo 1482061 5341733 := bbase (se 4 (by rfl) ⟨500787, by rfl⟩ : syracuseStep 5341733 = 1001575) (by norm_num)
theorem B1876537 : Blo 1482061 1876537 := bbase (se 2 (by rfl) ⟨703701, by rfl⟩ : syracuseStep 1876537 = 1407403) (by norm_num)
theorem B3334733 : Blo 1482061 3334733 := bbase (se 3 (by rfl) ⟨625262, by rfl⟩ : syracuseStep 3334733 = 1250525) (by norm_num)
theorem B7717493 : Blo 1482061 7717493 := bbase (se 5 (by rfl) ⟨361757, by rfl⟩ : syracuseStep 7717493 = 723515) (by norm_num)
theorem B3334805 : Blo 1482061 3334805 := bbase (se 6 (by rfl) ⟨78159, by rfl⟩ : syracuseStep 3334805 = 156319) (by norm_num)
theorem B21660373 : Blo 1482061 21660373 := bbase (se 7 (by rfl) ⟨253832, by rfl⟩ : syracuseStep 21660373 = 507665) (by norm_num)
theorem B25338581 : Blo 1482061 25338581 := bbase (se 7 (by rfl) ⟨296936, by rfl⟩ : syracuseStep 25338581 = 593873) (by norm_num)
theorem B3334877 : Blo 1482061 3334877 := bbase (se 3 (by rfl) ⟨625289, by rfl⟩ : syracuseStep 3334877 = 1250579) (by norm_num)
theorem B3752669 : Blo 1482061 3752669 := bbase (se 3 (by rfl) ⟨703625, by rfl⟩ : syracuseStep 3752669 = 1407251) (by norm_num)
theorem B1876709 : Blo 1482061 1876709 := bbase (se 4 (by rfl) ⟨175941, by rfl⟩ : syracuseStep 1876709 = 351883) (by norm_num)
theorem B4752101 : Blo 1482061 4752101 := bbase (se 4 (by rfl) ⟨445509, by rfl⟩ : syracuseStep 4752101 = 891019) (by norm_num)
theorem B5006069 : Blo 1482061 5006069 := bbase (se 5 (by rfl) ⟨234659, by rfl⟩ : syracuseStep 5006069 = 469319) (by norm_num)
theorem B2376461 : Blo 1482061 2376461 := bbase (se 3 (by rfl) ⟨445586, by rfl⟩ : syracuseStep 2376461 = 891173) (by norm_num)
theorem B1876765 : Blo 1482061 1876765 := bbase (se 3 (by rfl) ⟨351893, by rfl⟩ : syracuseStep 1876765 = 703787) (by norm_num)
theorem B3007261 : Blo 1482061 3007261 := bbase (se 3 (by rfl) ⟨563861, by rfl⟩ : syracuseStep 3007261 = 1127723) (by norm_num)
theorem B3334949 : Blo 1482061 3334949 := bbase (se 4 (by rfl) ⟨312651, by rfl⟩ : syracuseStep 3334949 = 625303) (by norm_num)
theorem B3335021 : Blo 1482061 3335021 := bbase (se 3 (by rfl) ⟨625316, by rfl⟩ : syracuseStep 3335021 = 1250633) (by norm_num)
theorem B1876861 : Blo 1482061 1876861 := bbase (se 3 (by rfl) ⟨351911, by rfl⟩ : syracuseStep 1876861 = 703823) (by norm_num)
theorem B2671501 : Blo 1482061 2671501 := bbase (se 3 (by rfl) ⟨500906, by rfl⟩ : syracuseStep 2671501 = 1001813) (by norm_num)
theorem B3564461 : Blo 1482061 3564461 := bbase (se 3 (by rfl) ⟨668336, by rfl⟩ : syracuseStep 3564461 = 1336673) (by norm_num)
theorem B3335093 : Blo 1482061 3335093 := bbase (se 5 (by rfl) ⟨156332, by rfl⟩ : syracuseStep 3335093 = 312665) (by norm_num)
theorem B3335165 : Blo 1482061 3335165 := bbase (se 3 (by rfl) ⟨625343, by rfl⟩ : syracuseStep 3335165 = 1250687) (by norm_num)
theorem B2139157 : Blo 1482061 2139157 := bbase (se 6 (by rfl) ⟨50136, by rfl⟩ : syracuseStep 2139157 = 100273) (by norm_num)
theorem B1877033 : Blo 1482061 1877033 := bbase (se 2 (by rfl) ⟨703887, by rfl⟩ : syracuseStep 1877033 = 1407775) (by norm_num)
theorem B3753013 : Blo 1482061 3753013 := bbase (se 5 (by rfl) ⟨175922, by rfl⟩ : syracuseStep 3753013 = 351845) (by norm_num)
theorem B3335237 : Blo 1482061 3335237 := bbase (se 4 (by rfl) ⟨312678, by rfl⟩ : syracuseStep 3335237 = 625357) (by norm_num)
theorem B42787925 : Blo 1482061 42787925 := bbase (se 8 (by rfl) ⟨250710, by rfl⟩ : syracuseStep 42787925 = 501421) (by norm_num)
theorem B1877089 : Blo 1482061 1877089 := bbase (se 2 (by rfl) ⟨703908, by rfl⟩ : syracuseStep 1877089 = 1407817) (by norm_num)
theorem B3613805 : Blo 1482061 3613805 := bbase (se 3 (by rfl) ⟨677588, by rfl⟩ : syracuseStep 3613805 = 1355177) (by norm_num)
theorem B3335309 : Blo 1482061 3335309 := bbase (se 3 (by rfl) ⟨625370, by rfl⟩ : syracuseStep 3335309 = 1250741) (by norm_num)
theorem B3753125 : Blo 1482061 3753125 := bbase (se 4 (by rfl) ⟨351855, by rfl⟩ : syracuseStep 3753125 = 703711) (by norm_num)
theorem B5006501 : Blo 1482061 5006501 := bbase (se 4 (by rfl) ⟨469359, by rfl⟩ : syracuseStep 5006501 = 938719) (by norm_num)
theorem B6767797 : Blo 1482061 6767797 := bbase (se 5 (by rfl) ⟨317240, by rfl⟩ : syracuseStep 6767797 = 634481) (by norm_num)
theorem B1877185 : Blo 1482061 1877185 := bbase (se 2 (by rfl) ⟨703944, by rfl⟩ : syracuseStep 1877185 = 1407889) (by norm_num)
theorem B3335381 : Blo 1482061 3335381 := bbase (se 7 (by rfl) ⟨39086, by rfl⟩ : syracuseStep 3335381 = 78173) (by norm_num)
theorem B2376973 : Blo 1482061 2376973 := bbase (se 3 (by rfl) ⟨445682, by rfl⟩ : syracuseStep 2376973 = 891365) (by norm_num)
theorem B4818197 : Blo 1482061 4818197 := bbase (se 6 (by rfl) ⟨112926, by rfl⟩ : syracuseStep 4818197 = 225853) (by norm_num)
theorem B3335453 : Blo 1482061 3335453 := bbase (se 3 (by rfl) ⟨625397, by rfl⟩ : syracuseStep 3335453 = 1250795) (by norm_num)
theorem B3335525 : Blo 1482061 3335525 := bbase (se 4 (by rfl) ⟨312705, by rfl⟩ : syracuseStep 3335525 = 625411) (by norm_num)
theorem B3753317 : Blo 1482061 3753317 := bbase (se 4 (by rfl) ⟨351873, by rfl⟩ : syracuseStep 3753317 = 703747) (by norm_num)
theorem B1877357 : Blo 1482061 1877357 := bbase (se 3 (by rfl) ⟨352004, by rfl⟩ : syracuseStep 1877357 = 704009) (by norm_num)
theorem B8562037 : Blo 1482061 8562037 := bbase (se 5 (by rfl) ⟨401345, by rfl⟩ : syracuseStep 8562037 = 802691) (by norm_num)
theorem B1877413 : Blo 1482061 1877413 := bbase (se 4 (by rfl) ⟨176007, by rfl⟩ : syracuseStep 1877413 = 352015) (by norm_num)
theorem B3335597 : Blo 1482061 3335597 := bbase (se 3 (by rfl) ⟨625424, by rfl⟩ : syracuseStep 3335597 = 1250849) (by norm_num)
theorem B27059669 : Blo 1482061 27059669 := bbase (se 7 (by rfl) ⟨317105, by rfl⟩ : syracuseStep 27059669 = 634211) (by norm_num)
theorem B3335669 : Blo 1482061 3335669 := bbase (se 5 (by rfl) ⟨156359, by rfl⟩ : syracuseStep 3335669 = 312719) (by norm_num)
theorem B5629445 : Blo 1482061 5629445 := bbase (se 4 (by rfl) ⟨527760, by rfl⟩ : syracuseStep 5629445 = 1055521) (by norm_num)
theorem B1877509 : Blo 1482061 1877509 := bbase (se 4 (by rfl) ⟨176016, by rfl⟩ : syracuseStep 1877509 = 352033) (by norm_num)
theorem B3335741 : Blo 1482061 3335741 := bbase (se 3 (by rfl) ⟨625451, by rfl⟩ : syracuseStep 3335741 = 1250903) (by norm_num)
theorem B5006933 : Blo 1482061 5006933 := bbase (se 8 (by rfl) ⟨29337, by rfl⟩ : syracuseStep 5006933 = 58675) (by norm_num)
theorem B3335813 : Blo 1482061 3335813 := bbase (se 4 (by rfl) ⟨312732, by rfl⟩ : syracuseStep 3335813 = 625465) (by norm_num)
theorem B1877681 : Blo 1482061 1877681 := bbase (se 2 (by rfl) ⟨704130, by rfl⟩ : syracuseStep 1877681 = 1408261) (by norm_num)
theorem B3753661 : Blo 1482061 3753661 := bbase (se 3 (by rfl) ⟨703811, by rfl⟩ : syracuseStep 3753661 = 1407623) (by norm_num)
theorem B3335885 : Blo 1482061 3335885 := bbase (se 3 (by rfl) ⟨625478, by rfl⟩ : syracuseStep 3335885 = 1250957) (by norm_num)
theorem B32057045 : Blo 1482061 32057045 := bbase (se 7 (by rfl) ⟨375668, by rfl⟩ : syracuseStep 32057045 = 751337) (by norm_num)
theorem B7505621 : Blo 1482061 7505621 := bbase (se 7 (by rfl) ⟨87956, by rfl⟩ : syracuseStep 7505621 = 175913) (by norm_num)
theorem B1877737 : Blo 1482061 1877737 := bbase (se 2 (by rfl) ⟨704151, by rfl⟩ : syracuseStep 1877737 = 1408303) (by norm_num)
theorem B3335957 : Blo 1482061 3335957 := bbase (se 6 (by rfl) ⟨78186, by rfl⟩ : syracuseStep 3335957 = 156373) (by norm_num)
theorem B5629733 : Blo 1482061 5629733 := bbase (se 4 (by rfl) ⟨527787, by rfl⟩ : syracuseStep 5629733 = 1055575) (by norm_num)
theorem B3753773 : Blo 1482061 3753773 := bbase (se 3 (by rfl) ⟨703832, by rfl⟩ : syracuseStep 3753773 = 1407665) (by norm_num)
theorem B1877833 : Blo 1482061 1877833 := bbase (se 2 (by rfl) ⟨704187, by rfl⟩ : syracuseStep 1877833 = 1408375) (by norm_num)
theorem B3336029 : Blo 1482061 3336029 := bbase (se 3 (by rfl) ⟨625505, by rfl⟩ : syracuseStep 3336029 = 1251011) (by norm_num)
theorem B1582961 : Blo 1482061 1582961 := bbase (se 2 (by rfl) ⟨593610, by rfl⟩ : syracuseStep 1582961 = 1187221) (by norm_num)
theorem B16893845 : Blo 1482061 16893845 := bbase (se 6 (by rfl) ⟨395949, by rfl⟩ : syracuseStep 16893845 = 791899) (by norm_num)
theorem B3336101 : Blo 1482061 3336101 := bbase (se 4 (by rfl) ⟨312759, by rfl⟩ : syracuseStep 3336101 = 625519) (by norm_num)
theorem B1583021 : Blo 1482061 1583021 := bbase (se 3 (by rfl) ⟨296816, by rfl⟩ : syracuseStep 1583021 = 593633) (by norm_num)
theorem B3336173 : Blo 1482061 3336173 := bbase (se 3 (by rfl) ⟨625532, by rfl⟩ : syracuseStep 3336173 = 1251065) (by norm_num)
theorem B3753965 : Blo 1482061 3753965 := bbase (se 3 (by rfl) ⟨703868, by rfl⟩ : syracuseStep 3753965 = 1407737) (by norm_num)
theorem B1878005 : Blo 1482061 1878005 := bbase (se 5 (by rfl) ⟨88031, by rfl⟩ : syracuseStep 1878005 = 176063) (by norm_num)
theorem B5007365 : Blo 1482061 5007365 := bbase (se 4 (by rfl) ⟨469440, by rfl⟩ : syracuseStep 5007365 = 938881) (by norm_num)
theorem B1583149 : Blo 1482061 1583149 := bbase (se 3 (by rfl) ⟨296840, by rfl⟩ : syracuseStep 1583149 = 593681) (by norm_num)
theorem B1878061 : Blo 1482061 1878061 := bbase (se 3 (by rfl) ⟨352136, by rfl⟩ : syracuseStep 1878061 = 704273) (by norm_num)
theorem B3336245 : Blo 1482061 3336245 := bbase (se 5 (by rfl) ⟨156386, by rfl⟩ : syracuseStep 3336245 = 312773) (by norm_num)
theorem B3336317 : Blo 1482061 3336317 := bbase (se 3 (by rfl) ⟨625559, by rfl⟩ : syracuseStep 3336317 = 1251119) (by norm_num)
theorem B1878157 : Blo 1482061 1878157 := bbase (se 3 (by rfl) ⟨352154, by rfl⟩ : syracuseStep 1878157 = 704309) (by norm_num)
theorem B19015829 : Blo 1482061 19015829 := bbase (se 6 (by rfl) ⟨445683, by rfl⟩ : syracuseStep 19015829 = 891367) (by norm_num)
theorem B3336389 : Blo 1482061 3336389 := bbase (se 4 (by rfl) ⟨312786, by rfl⟩ : syracuseStep 3336389 = 625573) (by norm_num)
theorem B4008149 : Blo 1482061 4008149 := bbase (se 7 (by rfl) ⟨46970, by rfl⟩ : syracuseStep 4008149 = 93941) (by norm_num)
theorem B4221173 : Blo 1482061 4221173 := bbase (se 5 (by rfl) ⟨197867, by rfl⟩ : syracuseStep 4221173 = 395735) (by norm_num)
theorem B8448245 : Blo 1482061 8448245 := bbase (se 5 (by rfl) ⟨396011, by rfl⟩ : syracuseStep 8448245 = 792023) (by norm_num)
theorem B3336461 : Blo 1482061 3336461 := bbase (se 3 (by rfl) ⟨625586, by rfl⟩ : syracuseStep 3336461 = 1251173) (by norm_num)
theorem B3754309 : Blo 1482061 3754309 := bbase (se 4 (by rfl) ⟨351966, by rfl⟩ : syracuseStep 3754309 = 703933) (by norm_num)
theorem B7317845 : Blo 1482061 7317845 := bbase (se 10 (by rfl) ⟨10719, by rfl⟩ : syracuseStep 7317845 = 21439) (by norm_num)
theorem B3336533 : Blo 1482061 3336533 := bbase (se 10 (by rfl) ⟨4887, by rfl⟩ : syracuseStep 3336533 = 9775) (by norm_num)
theorem B3336605 : Blo 1482061 3336605 := bbase (se 3 (by rfl) ⟨625613, by rfl⟩ : syracuseStep 3336605 = 1251227) (by norm_num)
theorem B2140589 : Blo 1482061 2140589 := bbase (se 3 (by rfl) ⟨401360, by rfl⟩ : syracuseStep 2140589 = 802721) (by norm_num)
theorem B3754421 : Blo 1482061 3754421 := bbase (se 5 (by rfl) ⟨175988, by rfl⟩ : syracuseStep 3754421 = 351977) (by norm_num)
theorem B5007797 : Blo 1482061 5007797 := bbase (se 5 (by rfl) ⟨234740, by rfl⟩ : syracuseStep 5007797 = 469481) (by norm_num)
theorem B2501077 : Blo 1482061 2501077 := bbase (se 7 (by rfl) ⟨29309, by rfl⟩ : syracuseStep 2501077 = 58619) (by norm_num)
theorem B3336677 : Blo 1482061 3336677 := bbase (se 4 (by rfl) ⟨312813, by rfl⟩ : syracuseStep 3336677 = 625627) (by norm_num)
theorem B1583593 : Blo 1482061 1583593 := bbase (se 2 (by rfl) ⟨593847, by rfl⟩ : syracuseStep 1583593 = 1187695) (by norm_num)
theorem B17132053 : Blo 1482061 17132053 := bbase (se 6 (by rfl) ⟨401532, by rfl⟩ : syracuseStep 17132053 = 803065) (by norm_num)
theorem B2501165 : Blo 1482061 2501165 := bbase (se 3 (by rfl) ⟨468968, by rfl⟩ : syracuseStep 2501165 = 937937) (by norm_num)
theorem B3336749 : Blo 1482061 3336749 := bbase (se 3 (by rfl) ⟨625640, by rfl⟩ : syracuseStep 3336749 = 1251281) (by norm_num)
theorem B1583713 : Blo 1482061 1583713 := bbase (se 2 (by rfl) ⟨593892, by rfl⟩ : syracuseStep 1583713 = 1187785) (by norm_num)
theorem B3336821 : Blo 1482061 3336821 := bbase (se 5 (by rfl) ⟨156413, by rfl⟩ : syracuseStep 3336821 = 312827) (by norm_num)
theorem B3754613 : Blo 1482061 3754613 := bbase (se 5 (by rfl) ⟨175997, by rfl⟩ : syracuseStep 3754613 = 351995) (by norm_num)
theorem B2501293 : Blo 1482061 2501293 := bbase (se 3 (by rfl) ⟨468992, by rfl⟩ : syracuseStep 2501293 = 937985) (by norm_num)
theorem B3336893 : Blo 1482061 3336893 := bbase (se 3 (by rfl) ⟨625667, by rfl⟩ : syracuseStep 3336893 = 1251335) (by norm_num)
theorem B2501381 : Blo 1482061 2501381 := bbase (se 4 (by rfl) ⟨234504, by rfl⟩ : syracuseStep 2501381 = 469009) (by norm_num)
theorem B3336965 : Blo 1482061 3336965 := bbase (se 4 (by rfl) ⟨312840, by rfl⟩ : syracuseStep 3336965 = 625681) (by norm_num)
theorem B14256917 : Blo 1482061 14256917 := bbase (se 6 (by rfl) ⟨334146, by rfl⟩ : syracuseStep 14256917 = 668293) (by norm_num)
theorem B1690417 : Blo 1482061 1690417 := bbase (se 2 (by rfl) ⟨633906, by rfl⟩ : syracuseStep 1690417 = 1267813) (by norm_num)
theorem B3337037 : Blo 1482061 3337037 := bbase (se 3 (by rfl) ⟨625694, by rfl⟩ : syracuseStep 3337037 = 1251389) (by norm_num)
theorem B1583965 : Blo 1482061 1583965 := bbase (se 3 (by rfl) ⟨296993, by rfl⟩ : syracuseStep 1583965 = 593987) (by norm_num)
theorem B1583969 : Blo 1482061 1583969 := bbase (se 2 (by rfl) ⟨593988, by rfl⟩ : syracuseStep 1583969 = 1187977) (by norm_num)
theorem B5008229 : Blo 1482061 5008229 := bbase (se 4 (by rfl) ⟨469521, by rfl⟩ : syracuseStep 5008229 = 939043) (by norm_num)
theorem B2501509 : Blo 1482061 2501509 := bbase (se 4 (by rfl) ⟨234516, by rfl⟩ : syracuseStep 2501509 = 469033) (by norm_num)
theorem B10685333 : Blo 1482061 10685333 := bbase (se 6 (by rfl) ⟨250437, by rfl⟩ : syracuseStep 10685333 = 500875) (by norm_num)
theorem B4221845 : Blo 1482061 4221845 := bbase (se 6 (by rfl) ⟨98949, by rfl⟩ : syracuseStep 4221845 = 197899) (by norm_num)
theorem B3337109 : Blo 1482061 3337109 := bbase (se 6 (by rfl) ⟨78213, by rfl⟩ : syracuseStep 3337109 = 156427) (by norm_num)
theorem B5630917 : Blo 1482061 5630917 := bbase (se 4 (by rfl) ⟨527898, by rfl⟩ : syracuseStep 5630917 = 1055797) (by norm_num)
theorem B3754957 : Blo 1482061 3754957 := bbase (se 3 (by rfl) ⟨704054, by rfl⟩ : syracuseStep 3754957 = 1408109) (by norm_num)
theorem B2501597 : Blo 1482061 2501597 := bbase (se 3 (by rfl) ⟨469049, by rfl⟩ : syracuseStep 2501597 = 938099) (by norm_num)
theorem B3337181 : Blo 1482061 3337181 := bbase (se 3 (by rfl) ⟨625721, by rfl⟩ : syracuseStep 3337181 = 1251443) (by norm_num)
theorem B7506917 : Blo 1482061 7506917 := bbase (se 4 (by rfl) ⟨703773, by rfl⟩ : syracuseStep 7506917 = 1407547) (by norm_num)
theorem B2223101 : Blo 1482061 2223101 := bbase (se 3 (by rfl) ⟨416831, by rfl⟩ : syracuseStep 2223101 = 833663) (by norm_num)
theorem B2223125 : Blo 1482061 2223125 := bbase (se 6 (by rfl) ⟨52104, by rfl⟩ : syracuseStep 2223125 = 104209) (by norm_num)
theorem B4516901 : Blo 1482061 4516901 := bbase (se 4 (by rfl) ⟨423459, by rfl⟩ : syracuseStep 4516901 = 846919) (by norm_num)
theorem B3337253 : Blo 1482061 3337253 := bbase (se 4 (by rfl) ⟨312867, by rfl⟩ : syracuseStep 3337253 = 625735) (by norm_num)
theorem B2223149 : Blo 1482061 2223149 := bbase (se 3 (by rfl) ⟨416840, by rfl⟩ : syracuseStep 2223149 = 833681) (by norm_num)
theorem B1690669 : Blo 1482061 1690669 := bbase (se 3 (by rfl) ⟨317000, by rfl⟩ : syracuseStep 1690669 = 634001) (by norm_num)
theorem B3755069 : Blo 1482061 3755069 := bbase (se 3 (by rfl) ⟨704075, by rfl⟩ : syracuseStep 3755069 = 1408151) (by norm_num)
theorem B2223173 : Blo 1482061 2223173 := bbase (se 4 (by rfl) ⟨208422, by rfl⟩ : syracuseStep 2223173 = 416845) (by norm_num)
theorem B40594517 : Blo 1482061 40594517 := bbase (se 8 (by rfl) ⟨237858, by rfl⟩ : syracuseStep 40594517 = 475717) (by norm_num)
theorem B2223197 : Blo 1482061 2223197 := bbase (se 3 (by rfl) ⟨416849, by rfl⟩ : syracuseStep 2223197 = 833699) (by norm_num)
theorem B2501725 : Blo 1482061 2501725 := bbase (se 3 (by rfl) ⟨469073, by rfl⟩ : syracuseStep 2501725 = 938147) (by norm_num)
theorem B1502309 : Blo 1482061 1502309 := bbase (se 4 (by rfl) ⟨140841, by rfl⟩ : syracuseStep 1502309 = 281683) (by norm_num)
theorem B3337325 : Blo 1482061 3337325 := bbase (se 3 (by rfl) ⟨625748, by rfl⟩ : syracuseStep 3337325 = 1251497) (by norm_num)
theorem B2223221 : Blo 1482061 2223221 := bbase (se 5 (by rfl) ⟨104213, by rfl⟩ : syracuseStep 2223221 = 208427) (by norm_num)
theorem B2223245 : Blo 1482061 2223245 := bbase (se 3 (by rfl) ⟨416858, by rfl⟩ : syracuseStep 2223245 = 833717) (by norm_num)
theorem B2223269 : Blo 1482061 2223269 := bbase (se 4 (by rfl) ⟨208431, by rfl⟩ : syracuseStep 2223269 = 416863) (by norm_num)
theorem B2501813 : Blo 1482061 2501813 := bbase (se 5 (by rfl) ⟨117272, by rfl⟩ : syracuseStep 2501813 = 234545) (by norm_num)
theorem B3337397 : Blo 1482061 3337397 := bbase (se 5 (by rfl) ⟨156440, by rfl⟩ : syracuseStep 3337397 = 312881) (by norm_num)
theorem B2223293 : Blo 1482061 2223293 := bbase (se 3 (by rfl) ⟨416867, by rfl⟩ : syracuseStep 2223293 = 833735) (by norm_num)
theorem B2223317 : Blo 1482061 2223317 := bbase (se 7 (by rfl) ⟨26054, by rfl⟩ : syracuseStep 2223317 = 52109) (by norm_num)
theorem B2223341 : Blo 1482061 2223341 := bbase (se 3 (by rfl) ⟨416876, by rfl⟩ : syracuseStep 2223341 = 833753) (by norm_num)
theorem B5631221 : Blo 1482061 5631221 := bbase (se 5 (by rfl) ⟨263963, by rfl⟩ : syracuseStep 5631221 = 527927) (by norm_num)
theorem B1780985 : Blo 1482061 1780985 := bbase (se 2 (by rfl) ⟨667869, by rfl⟩ : syracuseStep 1780985 = 1335739) (by norm_num)
theorem B3337469 : Blo 1482061 3337469 := bbase (se 3 (by rfl) ⟨625775, by rfl⟩ : syracuseStep 3337469 = 1251551) (by norm_num)
theorem B3755261 : Blo 1482061 3755261 := bbase (se 3 (by rfl) ⟨704111, by rfl⟩ : syracuseStep 3755261 = 1408223) (by norm_num)
theorem B2223365 : Blo 1482061 2223365 := bbase (se 4 (by rfl) ⟨208440, by rfl⟩ : syracuseStep 2223365 = 416881) (by norm_num)
theorem B9506069 : Blo 1482061 9506069 := bbase (se 6 (by rfl) ⟨222798, by rfl⟩ : syracuseStep 9506069 = 445597) (by norm_num)
theorem B5008661 : Blo 1482061 5008661 := bbase (se 6 (by rfl) ⟨117390, by rfl⟩ : syracuseStep 5008661 = 234781) (by norm_num)
theorem B2223389 : Blo 1482061 2223389 := bbase (se 3 (by rfl) ⟨416885, by rfl⟩ : syracuseStep 2223389 = 833771) (by norm_num)
theorem B2223413 : Blo 1482061 2223413 := bbase (se 5 (by rfl) ⟨104222, by rfl⟩ : syracuseStep 2223413 = 208445) (by norm_num)
theorem B2501941 : Blo 1482061 2501941 := bbase (se 5 (by rfl) ⟨117278, by rfl⟩ : syracuseStep 2501941 = 234557) (by norm_num)
theorem B4222277 : Blo 1482061 4222277 := bbase (se 4 (by rfl) ⟨395838, by rfl⟩ : syracuseStep 4222277 = 791677) (by norm_num)
theorem B3337541 : Blo 1482061 3337541 := bbase (se 4 (by rfl) ⟨312894, by rfl⟩ : syracuseStep 3337541 = 625789) (by norm_num)
theorem B2223437 : Blo 1482061 2223437 := bbase (se 3 (by rfl) ⟨416894, by rfl⟩ : syracuseStep 2223437 = 833789) (by norm_num)
theorem B2223461 : Blo 1482061 2223461 := bbase (se 4 (by rfl) ⟨208449, by rfl⟩ : syracuseStep 2223461 = 416899) (by norm_num)
theorem B2223485 : Blo 1482061 2223485 := bbase (se 3 (by rfl) ⟨416903, by rfl⟩ : syracuseStep 2223485 = 833807) (by norm_num)
theorem B3165581 : Blo 1482061 3165581 := bbase (se 3 (by rfl) ⟨593546, by rfl⟩ : syracuseStep 3165581 = 1187093) (by norm_num)
theorem B2502029 : Blo 1482061 2502029 := bbase (se 3 (by rfl) ⟨469130, by rfl⟩ : syracuseStep 2502029 = 938261) (by norm_num)
theorem B3337613 : Blo 1482061 3337613 := bbase (se 3 (by rfl) ⟨625802, by rfl⟩ : syracuseStep 3337613 = 1251605) (by norm_num)
theorem B7122325 : Blo 1482061 7122325 := bbase (se 6 (by rfl) ⟨166929, by rfl⟩ : syracuseStep 7122325 = 333859) (by norm_num)
theorem B2223509 : Blo 1482061 2223509 := bbase (se 6 (by rfl) ⟨52113, by rfl⟩ : syracuseStep 2223509 = 104227) (by norm_num)
theorem B1584533 : Blo 1482061 1584533 := bbase (se 6 (by rfl) ⟨37137, by rfl⟩ : syracuseStep 1584533 = 74275) (by norm_num)
theorem B2223533 : Blo 1482061 2223533 := bbase (se 3 (by rfl) ⟨416912, by rfl⟩ : syracuseStep 2223533 = 833825) (by norm_num)
theorem B2223557 : Blo 1482061 2223557 := bbase (se 4 (by rfl) ⟨208458, by rfl⟩ : syracuseStep 2223557 = 416917) (by norm_num)
theorem B3337685 : Blo 1482061 3337685 := bbase (se 7 (by rfl) ⟨39113, by rfl⟩ : syracuseStep 3337685 = 78227) (by norm_num)
theorem B2223581 : Blo 1482061 2223581 := bbase (se 3 (by rfl) ⟨416921, by rfl⟩ : syracuseStep 2223581 = 833843) (by norm_num)
theorem B2223605 : Blo 1482061 2223605 := bbase (se 5 (by rfl) ⟨104231, by rfl⟩ : syracuseStep 2223605 = 208463) (by norm_num)
theorem B3804661 : Blo 1482061 3804661 := bbase (se 5 (by rfl) ⟨178343, by rfl⟩ : syracuseStep 3804661 = 356687) (by norm_num)
theorem B2223629 : Blo 1482061 2223629 := bbase (se 3 (by rfl) ⟨416930, by rfl⟩ : syracuseStep 2223629 = 833861) (by norm_num)
theorem B2502157 : Blo 1482061 2502157 := bbase (se 3 (by rfl) ⟨469154, by rfl⟩ : syracuseStep 2502157 = 938309) (by norm_num)
theorem B3337757 : Blo 1482061 3337757 := bbase (se 3 (by rfl) ⟨625829, by rfl⟩ : syracuseStep 3337757 = 1251659) (by norm_num)
theorem B2223653 : Blo 1482061 2223653 := bbase (se 4 (by rfl) ⟨208467, by rfl⟩ : syracuseStep 2223653 = 416935) (by norm_num)
theorem B1781293 : Blo 1482061 1781293 := bbase (se 3 (by rfl) ⟨333992, by rfl⟩ : syracuseStep 1781293 = 667985) (by norm_num)
theorem B2223677 : Blo 1482061 2223677 := bbase (se 3 (by rfl) ⟨416939, by rfl⟩ : syracuseStep 2223677 = 833879) (by norm_num)
theorem B4951621 : Blo 1482061 4951621 := bbase (se 4 (by rfl) ⟨464214, by rfl⟩ : syracuseStep 4951621 = 928429) (by norm_num)
theorem B1584721 : Blo 1482061 1584721 := bbase (se 2 (by rfl) ⟨594270, by rfl⟩ : syracuseStep 1584721 = 1188541) (by norm_num)
theorem B2223701 : Blo 1482061 2223701 := bbase (se 8 (by rfl) ⟨13029, by rfl⟩ : syracuseStep 2223701 = 26059) (by norm_num)
theorem B3755605 : Blo 1482061 3755605 := bbase (se 8 (by rfl) ⟨22005, by rfl⟩ : syracuseStep 3755605 = 44011) (by norm_num)
theorem B2502245 : Blo 1482061 2502245 := bbase (se 4 (by rfl) ⟨234585, by rfl⟩ : syracuseStep 2502245 = 469171) (by norm_num)
theorem B3337829 : Blo 1482061 3337829 := bbase (se 4 (by rfl) ⟨312921, by rfl⟩ : syracuseStep 3337829 = 625843) (by norm_num)
theorem B2223725 : Blo 1482061 2223725 := bbase (se 3 (by rfl) ⟨416948, by rfl⟩ : syracuseStep 2223725 = 833897) (by norm_num)
theorem B2223749 : Blo 1482061 2223749 := bbase (se 4 (by rfl) ⟨208476, by rfl⟩ : syracuseStep 2223749 = 416953) (by norm_num)
theorem B1781389 : Blo 1482061 1781389 := bbase (se 3 (by rfl) ⟨334010, by rfl⟩ : syracuseStep 1781389 = 668021) (by norm_num)
theorem B7614101 : Blo 1482061 7614101 := bbase (se 6 (by rfl) ⟨178455, by rfl⟩ : syracuseStep 7614101 = 356911) (by norm_num)
theorem B2223773 : Blo 1482061 2223773 := bbase (se 3 (by rfl) ⟨416957, by rfl⟩ : syracuseStep 2223773 = 833915) (by norm_num)
theorem B1502885 : Blo 1482061 1502885 := bbase (se 4 (by rfl) ⟨140895, by rfl⟩ : syracuseStep 1502885 = 281791) (by norm_num)
theorem B3337901 : Blo 1482061 3337901 := bbase (se 3 (by rfl) ⟨625856, by rfl⟩ : syracuseStep 3337901 = 1251713) (by norm_num)
theorem B2223797 : Blo 1482061 2223797 := bbase (se 5 (by rfl) ⟨104240, by rfl⟩ : syracuseStep 2223797 = 208481) (by norm_num)
theorem B2813629 : Blo 1482061 2813629 := bbase (se 3 (by rfl) ⟨527555, by rfl⟩ : syracuseStep 2813629 = 1055111) (by norm_num)
theorem B1781437 : Blo 1482061 1781437 := bbase (se 3 (by rfl) ⟨334019, by rfl⟩ : syracuseStep 1781437 = 668039) (by norm_num)
theorem B1502917 : Blo 1482061 1502917 := bbase (se 4 (by rfl) ⟨140898, by rfl⟩ : syracuseStep 1502917 = 281797) (by norm_num)
theorem B3755717 : Blo 1482061 3755717 := bbase (se 4 (by rfl) ⟨352098, by rfl⟩ : syracuseStep 3755717 = 704197) (by norm_num)
theorem B2223821 : Blo 1482061 2223821 := bbase (se 3 (by rfl) ⟨416966, by rfl⟩ : syracuseStep 2223821 = 833933) (by norm_num)
theorem B2223845 : Blo 1482061 2223845 := bbase (se 4 (by rfl) ⟨208485, by rfl⟩ : syracuseStep 2223845 = 416971) (by norm_num)
theorem B2502373 : Blo 1482061 2502373 := bbase (se 4 (by rfl) ⟨234597, by rfl⟩ : syracuseStep 2502373 = 469195) (by norm_num)
theorem B3337973 : Blo 1482061 3337973 := bbase (se 5 (by rfl) ⟨156467, by rfl⟩ : syracuseStep 3337973 = 312935) (by norm_num)
theorem B2223869 : Blo 1482061 2223869 := bbase (se 3 (by rfl) ⟨416975, by rfl⟩ : syracuseStep 2223869 = 833951) (by norm_num)
theorem B2223893 : Blo 1482061 2223893 := bbase (se 6 (by rfl) ⟨52122, by rfl⟩ : syracuseStep 2223893 = 104245) (by norm_num)
theorem B15224597 : Blo 1482061 15224597 := bbase (se 6 (by rfl) ⟨356826, by rfl⟩ : syracuseStep 15224597 = 713653) (by norm_num)
theorem B2223917 : Blo 1482061 2223917 := bbase (se 3 (by rfl) ⟨416984, by rfl⟩ : syracuseStep 2223917 = 833969) (by norm_num)
theorem B2502461 : Blo 1482061 2502461 := bbase (se 3 (by rfl) ⟨469211, by rfl⟩ : syracuseStep 2502461 = 938423) (by norm_num)
theorem B3338045 : Blo 1482061 3338045 := bbase (se 3 (by rfl) ⟨625883, by rfl⟩ : syracuseStep 3338045 = 1251767) (by norm_num)
theorem B2223941 : Blo 1482061 2223941 := bbase (se 4 (by rfl) ⟨208494, by rfl⟩ : syracuseStep 2223941 = 416989) (by norm_num)
theorem B2813773 : Blo 1482061 2813773 := bbase (se 3 (by rfl) ⟨527582, by rfl⟩ : syracuseStep 2813773 = 1055165) (by norm_num)
theorem B2223965 : Blo 1482061 2223965 := bbase (se 3 (by rfl) ⟨416993, by rfl⟩ : syracuseStep 2223965 = 833987) (by norm_num)
theorem B2854765 : Blo 1482061 2854765 := bbase (se 3 (by rfl) ⟨535268, by rfl⟩ : syracuseStep 2854765 = 1070537) (by norm_num)
theorem B2223989 : Blo 1482061 2223989 := bbase (se 5 (by rfl) ⟨104249, by rfl⟩ : syracuseStep 2223989 = 208499) (by norm_num)
theorem B3338117 : Blo 1482061 3338117 := bbase (se 4 (by rfl) ⟨312948, by rfl⟩ : syracuseStep 3338117 = 625897) (by norm_num)
theorem B3755909 : Blo 1482061 3755909 := bbase (se 4 (by rfl) ⟨352116, by rfl⟩ : syracuseStep 3755909 = 704233) (by norm_num)
theorem B2224013 : Blo 1482061 2224013 := bbase (se 3 (by rfl) ⟨417002, by rfl⟩ : syracuseStep 2224013 = 834005) (by norm_num)
theorem B2224037 : Blo 1482061 2224037 := bbase (se 4 (by rfl) ⟨208503, by rfl⟩ : syracuseStep 2224037 = 417007) (by norm_num)
theorem B2224061 : Blo 1482061 2224061 := bbase (se 3 (by rfl) ⟨417011, by rfl⟩ : syracuseStep 2224061 = 834023) (by norm_num)
theorem B2502589 : Blo 1482061 2502589 := bbase (se 3 (by rfl) ⟨469235, by rfl⟩ : syracuseStep 2502589 = 938471) (by norm_num)
theorem B3338189 : Blo 1482061 3338189 := bbase (se 3 (by rfl) ⟨625910, by rfl⟩ : syracuseStep 3338189 = 1251821) (by norm_num)
theorem B4337621 : Blo 1482061 4337621 := bbase (se 7 (by rfl) ⟨50831, by rfl⟩ : syracuseStep 4337621 = 101663) (by norm_num)
theorem B2224085 : Blo 1482061 2224085 := bbase (se 7 (by rfl) ⟨26063, by rfl⟩ : syracuseStep 2224085 = 52127) (by norm_num)
theorem B2813933 : Blo 1482061 2813933 := bbase (se 3 (by rfl) ⟨527612, by rfl⟩ : syracuseStep 2813933 = 1055225) (by norm_num)
theorem B2224109 : Blo 1482061 2224109 := bbase (se 3 (by rfl) ⟨417020, by rfl⟩ : syracuseStep 2224109 = 834041) (by norm_num)
theorem B2224133 : Blo 1482061 2224133 := bbase (se 4 (by rfl) ⟨208512, by rfl⟩ : syracuseStep 2224133 = 417025) (by norm_num)
theorem B2502677 : Blo 1482061 2502677 := bbase (se 6 (by rfl) ⟨58656, by rfl⟩ : syracuseStep 2502677 = 117313) (by norm_num)
theorem B3338261 : Blo 1482061 3338261 := bbase (se 6 (by rfl) ⟨78240, by rfl⟩ : syracuseStep 3338261 = 156481) (by norm_num)
theorem B2224157 : Blo 1482061 2224157 := bbase (se 3 (by rfl) ⟨417029, by rfl⟩ : syracuseStep 2224157 = 834059) (by norm_num)
theorem B2224181 : Blo 1482061 2224181 := bbase (se 5 (by rfl) ⟨104258, by rfl⟩ : syracuseStep 2224181 = 208517) (by norm_num)
theorem B4223029 : Blo 1482061 4223029 := bbase (se 5 (by rfl) ⟨197954, by rfl⟩ : syracuseStep 4223029 = 395909) (by norm_num)
theorem B2224205 : Blo 1482061 2224205 := bbase (se 3 (by rfl) ⟨417038, by rfl⟩ : syracuseStep 2224205 = 834077) (by norm_num)
theorem B15224917 : Blo 1482061 15224917 := bbase (se 8 (by rfl) ⟨89208, by rfl⟩ : syracuseStep 15224917 = 178417) (by norm_num)
theorem B3338333 : Blo 1482061 3338333 := bbase (se 3 (by rfl) ⟨625937, by rfl⟩ : syracuseStep 3338333 = 1251875) (by norm_num)
theorem B2224229 : Blo 1482061 2224229 := bbase (se 4 (by rfl) ⟨208521, by rfl⟩ : syracuseStep 2224229 = 417043) (by norm_num)
theorem B6336629 : Blo 1482061 6336629 := bbase (se 5 (by rfl) ⟨297029, by rfl⟩ : syracuseStep 6336629 = 594059) (by norm_num)
theorem B2814077 : Blo 1482061 2814077 := bbase (se 3 (by rfl) ⟨527639, by rfl⟩ : syracuseStep 2814077 = 1055279) (by norm_num)
theorem B2224253 : Blo 1482061 2224253 := bbase (se 3 (by rfl) ⟨417047, by rfl⟩ : syracuseStep 2224253 = 834095) (by norm_num)
theorem B2224277 : Blo 1482061 2224277 := bbase (se 6 (by rfl) ⟨52131, by rfl⟩ : syracuseStep 2224277 = 104263) (by norm_num)
theorem B2502805 : Blo 1482061 2502805 := bbase (se 6 (by rfl) ⟨58659, by rfl⟩ : syracuseStep 2502805 = 117319) (by norm_num)
theorem B3338405 : Blo 1482061 3338405 := bbase (se 4 (by rfl) ⟨312975, by rfl⟩ : syracuseStep 3338405 = 625951) (by norm_num)
theorem B2224301 : Blo 1482061 2224301 := bbase (se 3 (by rfl) ⟨417056, by rfl⟩ : syracuseStep 2224301 = 834113) (by norm_num)
theorem B2224325 : Blo 1482061 2224325 := bbase (se 4 (by rfl) ⟨208530, by rfl⟩ : syracuseStep 2224325 = 417061) (by norm_num)
theorem B2224349 : Blo 1482061 2224349 := bbase (se 3 (by rfl) ⟨417065, by rfl⟩ : syracuseStep 2224349 = 834131) (by norm_num)
theorem B3756253 : Blo 1482061 3756253 := bbase (se 3 (by rfl) ⟨704297, by rfl⟩ : syracuseStep 3756253 = 1408595) (by norm_num)
theorem B2502893 : Blo 1482061 2502893 := bbase (se 3 (by rfl) ⟨469292, by rfl⟩ : syracuseStep 2502893 = 938585) (by norm_num)
theorem B1503469 : Blo 1482061 1503469 := bbase (se 3 (by rfl) ⟨281900, by rfl⟩ : syracuseStep 1503469 = 563801) (by norm_num)
theorem B3338477 : Blo 1482061 3338477 := bbase (se 3 (by rfl) ⟨625964, by rfl⟩ : syracuseStep 3338477 = 1251929) (by norm_num)
theorem B2224373 : Blo 1482061 2224373 := bbase (se 5 (by rfl) ⟨104267, by rfl⟩ : syracuseStep 2224373 = 208535) (by norm_num)
theorem B7508213 : Blo 1482061 7508213 := bbase (se 5 (by rfl) ⟨351947, by rfl⟩ : syracuseStep 7508213 = 703895) (by norm_num)
theorem B3166469 : Blo 1482061 3166469 := bbase (se 4 (by rfl) ⟨296856, by rfl⟩ : syracuseStep 3166469 = 593713) (by norm_num)
theorem B7131397 : Blo 1482061 7131397 := bbase (se 4 (by rfl) ⟨668568, by rfl⟩ : syracuseStep 7131397 = 1337137) (by norm_num)
theorem B2224397 : Blo 1482061 2224397 := bbase (se 3 (by rfl) ⟨417074, by rfl⟩ : syracuseStep 2224397 = 834149) (by norm_num)
theorem B1667353 : Blo 1482061 1667353 := bbase (se 2 (by rfl) ⟨625257, by rfl⟩ : syracuseStep 1667353 = 1250515) (by norm_num)
theorem B2224421 : Blo 1482061 2224421 := bbase (se 4 (by rfl) ⟨208539, by rfl⟩ : syracuseStep 2224421 = 417079) (by norm_num)
theorem B3338549 : Blo 1482061 3338549 := bbase (se 5 (by rfl) ⟨156494, by rfl⟩ : syracuseStep 3338549 = 312989) (by norm_num)
theorem B1667389 : Blo 1482061 1667389 := bbase (se 3 (by rfl) ⟨312635, by rfl⟩ : syracuseStep 1667389 = 625271) (by norm_num)
theorem B2224445 : Blo 1482061 2224445 := bbase (se 3 (by rfl) ⟨417083, by rfl⟩ : syracuseStep 2224445 = 834167) (by norm_num)
theorem B3756365 : Blo 1482061 3756365 := bbase (se 3 (by rfl) ⟨704318, by rfl⟩ : syracuseStep 3756365 = 1408637) (by norm_num)
theorem B2224469 : Blo 1482061 2224469 := bbase (se 10 (by rfl) ⟨3258, by rfl⟩ : syracuseStep 2224469 = 6517) (by norm_num)
theorem B1667425 : Blo 1482061 1667425 := bbase (se 2 (by rfl) ⟨625284, by rfl⟩ : syracuseStep 1667425 = 1250569) (by norm_num)
theorem B2224493 : Blo 1482061 2224493 := bbase (se 3 (by rfl) ⟨417092, by rfl⟩ : syracuseStep 2224493 = 834185) (by norm_num)
theorem B2503021 : Blo 1482061 2503021 := bbase (se 3 (by rfl) ⟨469316, by rfl⟩ : syracuseStep 2503021 = 938633) (by norm_num)
theorem B3166589 : Blo 1482061 3166589 := bbase (se 3 (by rfl) ⟨593735, by rfl⟩ : syracuseStep 3166589 = 1187471) (by norm_num)
theorem B3338621 : Blo 1482061 3338621 := bbase (se 3 (by rfl) ⟨625991, by rfl⟩ : syracuseStep 3338621 = 1251983) (by norm_num)
theorem B1667461 : Blo 1482061 1667461 := bbase (se 4 (by rfl) ⟨156324, by rfl⟩ : syracuseStep 1667461 = 312649) (by norm_num)
theorem B2224517 : Blo 1482061 2224517 := bbase (se 4 (by rfl) ⟨208548, by rfl⟩ : syracuseStep 2224517 = 417097) (by norm_num)
theorem B2814365 : Blo 1482061 2814365 := bbase (se 3 (by rfl) ⟨527693, by rfl⟩ : syracuseStep 2814365 = 1055387) (by norm_num)
theorem B2224541 : Blo 1482061 2224541 := bbase (se 3 (by rfl) ⟨417101, by rfl⟩ : syracuseStep 2224541 = 834203) (by norm_num)
theorem B1667497 : Blo 1482061 1667497 := bbase (se 2 (by rfl) ⟨625311, by rfl⟩ : syracuseStep 1667497 = 1250623) (by norm_num)
theorem B2224565 : Blo 1482061 2224565 := bbase (se 5 (by rfl) ⟨104276, by rfl⟩ : syracuseStep 2224565 = 208553) (by norm_num)
theorem B2503109 : Blo 1482061 2503109 := bbase (se 4 (by rfl) ⟨234666, by rfl⟩ : syracuseStep 2503109 = 469333) (by norm_num)
theorem B3338693 : Blo 1482061 3338693 := bbase (se 4 (by rfl) ⟨313002, by rfl⟩ : syracuseStep 3338693 = 626005) (by norm_num)
theorem B1667533 : Blo 1482061 1667533 := bbase (se 3 (by rfl) ⟨312662, by rfl⟩ : syracuseStep 1667533 = 625325) (by norm_num)
theorem B2224589 : Blo 1482061 2224589 := bbase (se 3 (by rfl) ⟨417110, by rfl⟩ : syracuseStep 2224589 = 834221) (by norm_num)
theorem B2224613 : Blo 1482061 2224613 := bbase (se 4 (by rfl) ⟨208557, by rfl⟩ : syracuseStep 2224613 = 417115) (by norm_num)
theorem B1667569 : Blo 1482061 1667569 := bbase (se 2 (by rfl) ⟨625338, by rfl⟩ : syracuseStep 1667569 = 1250677) (by norm_num)
theorem B10572277 : Blo 1482061 10572277 := bbase (se 5 (by rfl) ⟨495575, by rfl⟩ : syracuseStep 10572277 = 991151) (by norm_num)
theorem B2224637 : Blo 1482061 2224637 := bbase (se 3 (by rfl) ⟨417119, by rfl⟩ : syracuseStep 2224637 = 834239) (by norm_num)
theorem B3338765 : Blo 1482061 3338765 := bbase (se 3 (by rfl) ⟨626018, by rfl⟩ : syracuseStep 3338765 = 1252037) (by norm_num)
theorem B1667605 : Blo 1482061 1667605 := bbase (se 6 (by rfl) ⟨39084, by rfl⟩ : syracuseStep 1667605 = 78169) (by norm_num)
theorem B2224661 : Blo 1482061 2224661 := bbase (se 6 (by rfl) ⟨52140, by rfl⟩ : syracuseStep 2224661 = 104281) (by norm_num)
theorem B2224685 : Blo 1482061 2224685 := bbase (se 3 (by rfl) ⟨417128, by rfl⟩ : syracuseStep 2224685 = 834257) (by norm_num)
theorem B2814517 : Blo 1482061 2814517 := bbase (se 5 (by rfl) ⟨131930, by rfl⟩ : syracuseStep 2814517 = 263861) (by norm_num)
theorem B1667641 : Blo 1482061 1667641 := bbase (se 2 (by rfl) ⟨625365, by rfl⟩ : syracuseStep 1667641 = 1250731) (by norm_num)
theorem B2224709 : Blo 1482061 2224709 := bbase (se 4 (by rfl) ⟨208566, by rfl⟩ : syracuseStep 2224709 = 417133) (by norm_num)
theorem B2503237 : Blo 1482061 2503237 := bbase (se 4 (by rfl) ⟨234678, by rfl⟩ : syracuseStep 2503237 = 469357) (by norm_num)
theorem B3338837 : Blo 1482061 3338837 := bbase (se 8 (by rfl) ⟨19563, by rfl⟩ : syracuseStep 3338837 = 39127) (by norm_num)
theorem B1667677 : Blo 1482061 1667677 := bbase (se 3 (by rfl) ⟨312689, by rfl⟩ : syracuseStep 1667677 = 625379) (by norm_num)
theorem B2224733 : Blo 1482061 2224733 := bbase (se 3 (by rfl) ⟨417137, by rfl⟩ : syracuseStep 2224733 = 834275) (by norm_num)
theorem B2224757 : Blo 1482061 2224757 := bbase (se 5 (by rfl) ⟨104285, by rfl⟩ : syracuseStep 2224757 = 208571) (by norm_num)
theorem B1667713 : Blo 1482061 1667713 := bbase (se 2 (by rfl) ⟨625392, by rfl⟩ : syracuseStep 1667713 = 1250785) (by norm_num)
theorem B2224781 : Blo 1482061 2224781 := bbase (se 3 (by rfl) ⟨417146, by rfl⟩ : syracuseStep 2224781 = 834293) (by norm_num)
theorem B2503325 : Blo 1482061 2503325 := bbase (se 3 (by rfl) ⟨469373, by rfl⟩ : syracuseStep 2503325 = 938747) (by norm_num)
theorem B3338909 : Blo 1482061 3338909 := bbase (se 3 (by rfl) ⟨626045, by rfl⟩ : syracuseStep 3338909 = 1252091) (by norm_num)
theorem B1667749 : Blo 1482061 1667749 := bbase (se 4 (by rfl) ⟨156351, by rfl⟩ : syracuseStep 1667749 = 312703) (by norm_num)
theorem B2224805 : Blo 1482061 2224805 := bbase (se 4 (by rfl) ⟨208575, by rfl⟩ : syracuseStep 2224805 = 417151) (by norm_num)
theorem B2224829 : Blo 1482061 2224829 := bbase (se 3 (by rfl) ⟨417155, by rfl⟩ : syracuseStep 2224829 = 834311) (by norm_num)
theorem B1667785 : Blo 1482061 1667785 := bbase (se 2 (by rfl) ⟨625419, by rfl⟩ : syracuseStep 1667785 = 1250839) (by norm_num)
theorem B2224853 : Blo 1482061 2224853 := bbase (se 7 (by rfl) ⟨26072, by rfl⟩ : syracuseStep 2224853 = 52145) (by norm_num)
theorem B3338981 : Blo 1482061 3338981 := bbase (se 4 (by rfl) ⟨313029, by rfl⟩ : syracuseStep 3338981 = 626059) (by norm_num)
theorem B1667821 : Blo 1482061 1667821 := bbase (se 3 (by rfl) ⟨312716, by rfl⟩ : syracuseStep 1667821 = 625433) (by norm_num)
theorem B2224877 : Blo 1482061 2224877 := bbase (se 3 (by rfl) ⟨417164, by rfl⟩ : syracuseStep 2224877 = 834329) (by norm_num)
theorem B2003717 : Blo 1482061 2003717 := bbase (se 4 (by rfl) ⟨187848, by rfl⟩ : syracuseStep 2003717 = 375697) (by norm_num)
theorem B2224901 : Blo 1482061 2224901 := bbase (se 4 (by rfl) ⟨208584, by rfl⟩ : syracuseStep 2224901 = 417169) (by norm_num)
theorem B1626889 : Blo 1482061 1626889 := bbase (se 2 (by rfl) ⟨610083, by rfl⟩ : syracuseStep 1626889 = 1220167) (by norm_num)
theorem B1667857 : Blo 1482061 1667857 := bbase (se 2 (by rfl) ⟨625446, by rfl⟩ : syracuseStep 1667857 = 1250893) (by norm_num)
theorem B2224925 : Blo 1482061 2224925 := bbase (se 3 (by rfl) ⟨417173, by rfl⟩ : syracuseStep 2224925 = 834347) (by norm_num)
theorem B2503453 : Blo 1482061 2503453 := bbase (se 3 (by rfl) ⟨469397, by rfl⟩ : syracuseStep 2503453 = 938795) (by norm_num)
theorem B3339053 : Blo 1482061 3339053 := bbase (se 3 (by rfl) ⟨626072, by rfl⟩ : syracuseStep 3339053 = 1252145) (by norm_num)
theorem B1667893 : Blo 1482061 1667893 := bbase (se 5 (by rfl) ⟨78182, by rfl⟩ : syracuseStep 1667893 = 156365) (by norm_num)
theorem B2224949 : Blo 1482061 2224949 := bbase (se 5 (by rfl) ⟨104294, by rfl⟩ : syracuseStep 2224949 = 208589) (by norm_num)
theorem B3961669 : Blo 1482061 3961669 := bbase (se 4 (by rfl) ⟨371406, by rfl⟩ : syracuseStep 3961669 = 742813) (by norm_num)
theorem B2224973 : Blo 1482061 2224973 := bbase (se 3 (by rfl) ⟨417182, by rfl⟩ : syracuseStep 2224973 = 834365) (by norm_num)
theorem B1667929 : Blo 1482061 1667929 := bbase (se 2 (by rfl) ⟨625473, by rfl⟩ : syracuseStep 1667929 = 1250947) (by norm_num)
theorem B2814821 : Blo 1482061 2814821 := bbase (se 4 (by rfl) ⟨263889, by rfl⟩ : syracuseStep 2814821 = 527779) (by norm_num)
theorem B2224997 : Blo 1482061 2224997 := bbase (se 4 (by rfl) ⟨208593, by rfl⟩ : syracuseStep 2224997 = 417187) (by norm_num)
theorem B2503541 : Blo 1482061 2503541 := bbase (se 5 (by rfl) ⟨117353, by rfl⟩ : syracuseStep 2503541 = 234707) (by norm_num)
theorem B3339125 : Blo 1482061 3339125 := bbase (se 5 (by rfl) ⟨156521, by rfl⟩ : syracuseStep 3339125 = 313043) (by norm_num)
theorem B1667965 : Blo 1482061 1667965 := bbase (se 3 (by rfl) ⟨312743, by rfl⟩ : syracuseStep 1667965 = 625487) (by norm_num)
theorem B2225021 : Blo 1482061 2225021 := bbase (se 3 (by rfl) ⟨417191, by rfl⟩ : syracuseStep 2225021 = 834383) (by norm_num)
theorem B1782653 : Blo 1482061 1782653 := bbase (se 3 (by rfl) ⟨334247, by rfl⟩ : syracuseStep 1782653 = 668495) (by norm_num)
theorem B2225045 : Blo 1482061 2225045 := bbase (se 6 (by rfl) ⟨52149, by rfl⟩ : syracuseStep 2225045 = 104299) (by norm_num)
theorem B1668001 : Blo 1482061 1668001 := bbase (se 2 (by rfl) ⟨625500, by rfl⟩ : syracuseStep 1668001 = 1251001) (by norm_num)
theorem B4010917 : Blo 1482061 4010917 := bbase (se 4 (by rfl) ⟨376023, by rfl⟩ : syracuseStep 4010917 = 752047) (by norm_num)
theorem B2225069 : Blo 1482061 2225069 := bbase (se 3 (by rfl) ⟨417200, by rfl⟩ : syracuseStep 2225069 = 834401) (by norm_num)
theorem B4281269 : Blo 1482061 4281269 := bbase (se 5 (by rfl) ⟨200684, by rfl⟩ : syracuseStep 4281269 = 401369) (by norm_num)
theorem B5002181 : Blo 1482061 5002181 := bbase (se 4 (by rfl) ⟨468954, by rfl⟩ : syracuseStep 5002181 = 937909) (by norm_num)
theorem B1668037 : Blo 1482061 1668037 := bbase (se 4 (by rfl) ⟨156378, by rfl⟩ : syracuseStep 1668037 = 312757) (by norm_num)
theorem B2225093 : Blo 1482061 2225093 := bbase (se 4 (by rfl) ⟨208602, by rfl⟩ : syracuseStep 2225093 = 417205) (by norm_num)
theorem B2110421 : Blo 1482061 2110421 := bbase (se 7 (by rfl) ⟨24731, by rfl⟩ : syracuseStep 2110421 = 49463) (by norm_num)
theorem B9630677 : Blo 1482061 9630677 := bbase (se 7 (by rfl) ⟨112859, by rfl⟩ : syracuseStep 9630677 = 225719) (by norm_num)
theorem B2225117 : Blo 1482061 2225117 := bbase (se 3 (by rfl) ⟨417209, by rfl⟩ : syracuseStep 2225117 = 834419) (by norm_num)
theorem B1668073 : Blo 1482061 1668073 := bbase (se 2 (by rfl) ⟨625527, by rfl⟩ : syracuseStep 1668073 = 1251055) (by norm_num)
theorem B3167221 : Blo 1482061 3167221 := bbase (se 5 (by rfl) ⟨148463, by rfl⟩ : syracuseStep 3167221 = 296927) (by norm_num)
theorem B2225141 : Blo 1482061 2225141 := bbase (se 5 (by rfl) ⟨104303, by rfl⟩ : syracuseStep 2225141 = 208607) (by norm_num)
theorem B2503669 : Blo 1482061 2503669 := bbase (se 5 (by rfl) ⟨117359, by rfl⟩ : syracuseStep 2503669 = 234719) (by norm_num)
theorem B1668109 : Blo 1482061 1668109 := bbase (se 3 (by rfl) ⟨312770, by rfl⟩ : syracuseStep 1668109 = 625541) (by norm_num)
theorem B2225165 : Blo 1482061 2225165 := bbase (se 3 (by rfl) ⟨417218, by rfl⟩ : syracuseStep 2225165 = 834437) (by norm_num)
theorem B2225189 : Blo 1482061 2225189 := bbase (se 4 (by rfl) ⟨208611, by rfl⟩ : syracuseStep 2225189 = 417223) (by norm_num)
theorem B1782821 : Blo 1482061 1782821 := bbase (se 4 (by rfl) ⟨167139, by rfl⟩ : syracuseStep 1782821 = 334279) (by norm_num)
theorem B1668145 : Blo 1482061 1668145 := bbase (se 2 (by rfl) ⟨625554, by rfl⟩ : syracuseStep 1668145 = 1251109) (by norm_num)
theorem B2225213 : Blo 1482061 2225213 := bbase (se 3 (by rfl) ⟨417227, by rfl⟩ : syracuseStep 2225213 = 834455) (by norm_num)
theorem B5706821 : Blo 1482061 5706821 := bbase (se 4 (by rfl) ⟨535014, by rfl⟩ : syracuseStep 5706821 = 1070029) (by norm_num)
theorem B2503757 : Blo 1482061 2503757 := bbase (se 3 (by rfl) ⟨469454, by rfl⟩ : syracuseStep 2503757 = 938909) (by norm_num)
theorem B1668181 : Blo 1482061 1668181 := bbase (se 8 (by rfl) ⟨9774, by rfl⟩ : syracuseStep 1668181 = 19549) (by norm_num)
theorem B2225237 : Blo 1482061 2225237 := bbase (se 8 (by rfl) ⟨13038, by rfl⟩ : syracuseStep 2225237 = 26077) (by norm_num)
theorem B2225261 : Blo 1482061 2225261 := bbase (se 3 (by rfl) ⟨417236, by rfl⟩ : syracuseStep 2225261 = 834473) (by norm_num)
theorem B1668217 : Blo 1482061 1668217 := bbase (se 2 (by rfl) ⟨625581, by rfl⟩ : syracuseStep 1668217 = 1251163) (by norm_num)
theorem B2225285 : Blo 1482061 2225285 := bbase (se 4 (by rfl) ⟨208620, by rfl⟩ : syracuseStep 2225285 = 417241) (by norm_num)
theorem B1668253 : Blo 1482061 1668253 := bbase (se 3 (by rfl) ⟨312797, by rfl⟩ : syracuseStep 1668253 = 625595) (by norm_num)
theorem B2225309 : Blo 1482061 2225309 := bbase (se 3 (by rfl) ⟨417245, by rfl⟩ : syracuseStep 2225309 = 834491) (by norm_num)
theorem B2004149 : Blo 1482061 2004149 := bbase (se 5 (by rfl) ⟨93944, by rfl⟩ : syracuseStep 2004149 = 187889) (by norm_num)
theorem B2225333 : Blo 1482061 2225333 := bbase (se 5 (by rfl) ⟨104312, by rfl⟩ : syracuseStep 2225333 = 208625) (by norm_num)
theorem B1668289 : Blo 1482061 1668289 := bbase (se 2 (by rfl) ⟨625608, by rfl⟩ : syracuseStep 1668289 = 1251217) (by norm_num)
theorem B2225357 : Blo 1482061 2225357 := bbase (se 3 (by rfl) ⟨417254, by rfl⟩ : syracuseStep 2225357 = 834509) (by norm_num)
theorem B2503885 : Blo 1482061 2503885 := bbase (se 3 (by rfl) ⟨469478, by rfl⟩ : syracuseStep 2503885 = 938957) (by norm_num)
theorem B1668325 : Blo 1482061 1668325 := bbase (se 4 (by rfl) ⟨156405, by rfl⟩ : syracuseStep 1668325 = 312811) (by norm_num)
theorem B2225381 : Blo 1482061 2225381 := bbase (se 4 (by rfl) ⟨208629, by rfl⟩ : syracuseStep 2225381 = 417259) (by norm_num)
theorem B2225405 : Blo 1482061 2225405 := bbase (se 3 (by rfl) ⟨417263, by rfl⟩ : syracuseStep 2225405 = 834527) (by norm_num)
theorem B1668361 : Blo 1482061 1668361 := bbase (se 2 (by rfl) ⟨625635, by rfl⟩ : syracuseStep 1668361 = 1251271) (by norm_num)
theorem B2225429 : Blo 1482061 2225429 := bbase (se 6 (by rfl) ⟨52158, by rfl⟩ : syracuseStep 2225429 = 104317) (by norm_num)
theorem B2503973 : Blo 1482061 2503973 := bbase (se 4 (by rfl) ⟨234747, by rfl⟩ : syracuseStep 2503973 = 469495) (by norm_num)
theorem B1668397 : Blo 1482061 1668397 := bbase (se 3 (by rfl) ⟨312824, by rfl⟩ : syracuseStep 1668397 = 625649) (by norm_num)
theorem B2225453 : Blo 1482061 2225453 := bbase (se 3 (by rfl) ⟨417272, by rfl⟩ : syracuseStep 2225453 = 834545) (by norm_num)
theorem B5633333 : Blo 1482061 5633333 := bbase (se 5 (by rfl) ⟨264062, by rfl⟩ : syracuseStep 5633333 = 528125) (by norm_num)
theorem B2225477 : Blo 1482061 2225477 := bbase (se 4 (by rfl) ⟨208638, by rfl⟩ : syracuseStep 2225477 = 417277) (by norm_num)
theorem B1668433 : Blo 1482061 1668433 := bbase (se 2 (by rfl) ⟨625662, by rfl⟩ : syracuseStep 1668433 = 1251325) (by norm_num)
theorem B2225501 : Blo 1482061 2225501 := bbase (se 3 (by rfl) ⟨417281, by rfl⟩ : syracuseStep 2225501 = 834563) (by norm_num)
theorem B5002613 : Blo 1482061 5002613 := bbase (se 5 (by rfl) ⟨234497, by rfl⟩ : syracuseStep 5002613 = 468995) (by norm_num)
theorem B1668469 : Blo 1482061 1668469 := bbase (se 5 (by rfl) ⟨78209, by rfl⟩ : syracuseStep 1668469 = 156419) (by norm_num)
theorem B2225525 : Blo 1482061 2225525 := bbase (se 5 (by rfl) ⟨104321, by rfl⟩ : syracuseStep 2225525 = 208643) (by norm_num)
theorem B2225549 : Blo 1482061 2225549 := bbase (se 3 (by rfl) ⟨417290, by rfl⟩ : syracuseStep 2225549 = 834581) (by norm_num)
theorem B1668505 : Blo 1482061 1668505 := bbase (se 2 (by rfl) ⟨625689, by rfl⟩ : syracuseStep 1668505 = 1251379) (by norm_num)
theorem B4339109 : Blo 1482061 4339109 := bbase (se 4 (by rfl) ⟨406791, by rfl⟩ : syracuseStep 4339109 = 813583) (by norm_num)
theorem B2225573 : Blo 1482061 2225573 := bbase (se 4 (by rfl) ⟨208647, by rfl⟩ : syracuseStep 2225573 = 417295) (by norm_num)
theorem B2504101 : Blo 1482061 2504101 := bbase (se 4 (by rfl) ⟨234759, by rfl⟩ : syracuseStep 2504101 = 469519) (by norm_num)
theorem B1668541 : Blo 1482061 1668541 := bbase (se 3 (by rfl) ⟨312851, by rfl⟩ : syracuseStep 1668541 = 625703) (by norm_num)
theorem B2225597 : Blo 1482061 2225597 := bbase (se 3 (by rfl) ⟨417299, by rfl⟩ : syracuseStep 2225597 = 834599) (by norm_num)
theorem B2225621 : Blo 1482061 2225621 := bbase (se 7 (by rfl) ⟨26081, by rfl⟩ : syracuseStep 2225621 = 52163) (by norm_num)
theorem B1668577 : Blo 1482061 1668577 := bbase (se 2 (by rfl) ⟨625716, by rfl⟩ : syracuseStep 1668577 = 1251433) (by norm_num)
theorem B2225645 : Blo 1482061 2225645 := bbase (se 3 (by rfl) ⟨417308, by rfl⟩ : syracuseStep 2225645 = 834617) (by norm_num)
theorem B5346805 : Blo 1482061 5346805 := bbase (se 5 (by rfl) ⟨250631, by rfl⟩ : syracuseStep 5346805 = 501263) (by norm_num)
theorem B2504189 : Blo 1482061 2504189 := bbase (se 3 (by rfl) ⟨469535, by rfl⟩ : syracuseStep 2504189 = 939071) (by norm_num)
theorem B1668613 : Blo 1482061 1668613 := bbase (se 4 (by rfl) ⟨156432, by rfl⟩ : syracuseStep 1668613 = 312865) (by norm_num)
theorem B7509509 : Blo 1482061 7509509 := bbase (se 4 (by rfl) ⟨704016, by rfl⟩ : syracuseStep 7509509 = 1408033) (by norm_num)
theorem B2225669 : Blo 1482061 2225669 := bbase (se 4 (by rfl) ⟨208656, by rfl⟩ : syracuseStep 2225669 = 417313) (by norm_num)
theorem B2225693 : Blo 1482061 2225693 := bbase (se 3 (by rfl) ⟨417317, by rfl⟩ : syracuseStep 2225693 = 834635) (by norm_num)
theorem B1668649 : Blo 1482061 1668649 := bbase (se 2 (by rfl) ⟨625743, by rfl⟩ : syracuseStep 1668649 = 1251487) (by norm_num)
theorem B2225717 : Blo 1482061 2225717 := bbase (se 5 (by rfl) ⟨104330, by rfl⟩ : syracuseStep 2225717 = 208661) (by norm_num)
theorem B1668685 : Blo 1482061 1668685 := bbase (se 3 (by rfl) ⟨312878, by rfl⟩ : syracuseStep 1668685 = 625757) (by norm_num)
theorem B2225741 : Blo 1482061 2225741 := bbase (se 3 (by rfl) ⟨417326, by rfl⟩ : syracuseStep 2225741 = 834653) (by norm_num)
theorem B2815573 : Blo 1482061 2815573 := bbase (se 8 (by rfl) ⟨16497, by rfl⟩ : syracuseStep 2815573 = 32995) (by norm_num)
theorem B5633621 : Blo 1482061 5633621 := bbase (se 8 (by rfl) ⟨33009, by rfl⟩ : syracuseStep 5633621 = 66019) (by norm_num)
theorem B2225765 : Blo 1482061 2225765 := bbase (se 4 (by rfl) ⟨208665, by rfl⟩ : syracuseStep 2225765 = 417331) (by norm_num)
theorem B1668721 : Blo 1482061 1668721 := bbase (se 2 (by rfl) ⟨625770, by rfl⟩ : syracuseStep 1668721 = 1251541) (by norm_num)
theorem B1955453 : Blo 1482061 1955453 := bbase (se 3 (by rfl) ⟨366647, by rfl⟩ : syracuseStep 1955453 = 733295) (by norm_num)
theorem B2225789 : Blo 1482061 2225789 := bbase (se 3 (by rfl) ⟨417335, by rfl⟩ : syracuseStep 2225789 = 834671) (by norm_num)
theorem B2504317 : Blo 1482061 2504317 := bbase (se 3 (by rfl) ⟨469559, by rfl⟩ : syracuseStep 2504317 = 939119) (by norm_num)
theorem B1668757 : Blo 1482061 1668757 := bbase (se 6 (by rfl) ⟨39111, by rfl⟩ : syracuseStep 1668757 = 78223) (by norm_num)
theorem B5346965 : Blo 1482061 5346965 := bbase (se 6 (by rfl) ⟨125319, by rfl⟩ : syracuseStep 5346965 = 250639) (by norm_num)
theorem B2225813 : Blo 1482061 2225813 := bbase (se 6 (by rfl) ⟨52167, by rfl⟩ : syracuseStep 2225813 = 104335) (by norm_num)
theorem B2225837 : Blo 1482061 2225837 := bbase (se 3 (by rfl) ⟨417344, by rfl⟩ : syracuseStep 2225837 = 834689) (by norm_num)
theorem B1668793 : Blo 1482061 1668793 := bbase (se 2 (by rfl) ⟨625797, by rfl⟩ : syracuseStep 1668793 = 1251595) (by norm_num)
theorem B2225861 : Blo 1482061 2225861 := bbase (se 4 (by rfl) ⟨208674, by rfl⟩ : syracuseStep 2225861 = 417349) (by norm_num)
theorem B1668829 : Blo 1482061 1668829 := bbase (se 3 (by rfl) ⟨312905, by rfl⟩ : syracuseStep 1668829 = 625811) (by norm_num)
theorem B2225885 : Blo 1482061 2225885 := bbase (se 3 (by rfl) ⟨417353, by rfl⟩ : syracuseStep 2225885 = 834707) (by norm_num)
theorem B2815717 : Blo 1482061 2815717 := bbase (se 4 (by rfl) ⟨263973, by rfl⟩ : syracuseStep 2815717 = 527947) (by norm_num)
theorem B4511477 : Blo 1482061 4511477 := bbase (se 5 (by rfl) ⟨211475, by rfl⟩ : syracuseStep 4511477 = 422951) (by norm_num)
theorem B2225909 : Blo 1482061 2225909 := bbase (se 5 (by rfl) ⟨104339, by rfl⟩ : syracuseStep 2225909 = 208679) (by norm_num)
theorem B2004733 : Blo 1482061 2004733 := bbase (se 3 (by rfl) ⟨375887, by rfl⟩ : syracuseStep 2004733 = 751775) (by norm_num)
theorem B1668865 : Blo 1482061 1668865 := bbase (se 2 (by rfl) ⟨625824, by rfl⟩ : syracuseStep 1668865 = 1251649) (by norm_num)
theorem B2225933 : Blo 1482061 2225933 := bbase (se 3 (by rfl) ⟨417362, by rfl⟩ : syracuseStep 2225933 = 834725) (by norm_num)
theorem B5003045 : Blo 1482061 5003045 := bbase (se 4 (by rfl) ⟨469035, by rfl⟩ : syracuseStep 5003045 = 938071) (by norm_num)
theorem B1668901 : Blo 1482061 1668901 := bbase (se 4 (by rfl) ⟨156459, by rfl⟩ : syracuseStep 1668901 = 312919) (by norm_num)
theorem B3807013 : Blo 1482061 3807013 := bbase (se 4 (by rfl) ⟨356907, by rfl⟩ : syracuseStep 3807013 = 713815) (by norm_num)
theorem B2225957 : Blo 1482061 2225957 := bbase (se 4 (by rfl) ⟨208683, by rfl⟩ : syracuseStep 2225957 = 417367) (by norm_num)
theorem B2225981 : Blo 1482061 2225981 := bbase (se 3 (by rfl) ⟨417371, by rfl⟩ : syracuseStep 2225981 = 834743) (by norm_num)
theorem B1668937 : Blo 1482061 1668937 := bbase (se 2 (by rfl) ⟨625851, by rfl⟩ : syracuseStep 1668937 = 1251703) (by norm_num)
theorem B3610453 : Blo 1482061 3610453 := bbase (se 9 (by rfl) ⟨10577, by rfl⟩ : syracuseStep 3610453 = 21155) (by norm_num)
theorem B2226005 : Blo 1482061 2226005 := bbase (se 9 (by rfl) ⟨6521, by rfl⟩ : syracuseStep 2226005 = 13043) (by norm_num)
theorem B3561317 : Blo 1482061 3561317 := bbase (se 4 (by rfl) ⟨333873, by rfl⟩ : syracuseStep 3561317 = 667747) (by norm_num)
theorem B6338405 : Blo 1482061 6338405 := bbase (se 4 (by rfl) ⟨594225, by rfl⟩ : syracuseStep 6338405 = 1188451) (by norm_num)
theorem B3168109 : Blo 1482061 3168109 := bbase (se 3 (by rfl) ⟨594020, by rfl⟩ : syracuseStep 3168109 = 1188041) (by norm_num)
theorem B1668973 : Blo 1482061 1668973 := bbase (se 3 (by rfl) ⟨312932, by rfl⟩ : syracuseStep 1668973 = 625865) (by norm_num)
theorem B2226029 : Blo 1482061 2226029 := bbase (se 3 (by rfl) ⟨417380, by rfl⟩ : syracuseStep 2226029 = 834761) (by norm_num)
theorem B2815877 : Blo 1482061 2815877 := bbase (se 4 (by rfl) ⟨263988, by rfl⟩ : syracuseStep 2815877 = 527977) (by norm_num)
theorem B2226053 : Blo 1482061 2226053 := bbase (se 4 (by rfl) ⟨208692, by rfl⟩ : syracuseStep 2226053 = 417385) (by norm_num)
theorem B1669009 : Blo 1482061 1669009 := bbase (se 2 (by rfl) ⟨625878, by rfl⟩ : syracuseStep 1669009 = 1251757) (by norm_num)
theorem B2226077 : Blo 1482061 2226077 := bbase (se 3 (by rfl) ⟨417389, by rfl⟩ : syracuseStep 2226077 = 834779) (by norm_num)
theorem B1669045 : Blo 1482061 1669045 := bbase (se 5 (by rfl) ⟨78236, by rfl⟩ : syracuseStep 1669045 = 156473) (by norm_num)
theorem B1669081 : Blo 1482061 1669081 := bbase (se 2 (by rfl) ⟨625905, by rfl⟩ : syracuseStep 1669081 = 1251811) (by norm_num)
theorem B3168229 : Blo 1482061 3168229 := bbase (se 4 (by rfl) ⟨297021, by rfl⟩ : syracuseStep 3168229 = 594043) (by norm_num)
theorem B1669117 : Blo 1482061 1669117 := bbase (se 3 (by rfl) ⟨312959, by rfl⟩ : syracuseStep 1669117 = 625919) (by norm_num)
theorem B2816021 : Blo 1482061 2816021 := bbase (se 6 (by rfl) ⟨66000, by rfl⟩ : syracuseStep 2816021 = 132001) (by norm_num)
theorem B1669153 : Blo 1482061 1669153 := bbase (se 2 (by rfl) ⟨625932, by rfl⟩ : syracuseStep 1669153 = 1251865) (by norm_num)
theorem B3561509 : Blo 1482061 3561509 := bbase (se 4 (by rfl) ⟨333891, by rfl⟩ : syracuseStep 3561509 = 667783) (by norm_num)
theorem B1669189 : Blo 1482061 1669189 := bbase (se 4 (by rfl) ⟨156486, by rfl⟩ : syracuseStep 1669189 = 312973) (by norm_num)
theorem B6338645 : Blo 1482061 6338645 := bbase (se 8 (by rfl) ⟨37140, by rfl⟩ : syracuseStep 6338645 = 74281) (by norm_num)
theorem B1669225 : Blo 1482061 1669225 := bbase (se 2 (by rfl) ⟨625959, by rfl⟩ : syracuseStep 1669225 = 1251919) (by norm_num)
theorem B1669261 : Blo 1482061 1669261 := bbase (se 3 (by rfl) ⟨312986, by rfl⟩ : syracuseStep 1669261 = 625973) (by norm_num)
theorem B1669297 : Blo 1482061 1669297 := bbase (se 2 (by rfl) ⟨625986, by rfl⟩ : syracuseStep 1669297 = 1251973) (by norm_num)
theorem B5003477 : Blo 1482061 5003477 := bbase (se 7 (by rfl) ⟨58634, by rfl⟩ : syracuseStep 5003477 = 117269) (by norm_num)
theorem B17832149 : Blo 1482061 17832149 := bbase (se 7 (by rfl) ⟨208970, by rfl⟩ : syracuseStep 17832149 = 417941) (by norm_num)
theorem B1669333 : Blo 1482061 1669333 := bbase (se 7 (by rfl) ⟨19562, by rfl⟩ : syracuseStep 1669333 = 39125) (by norm_num)
theorem B3168485 : Blo 1482061 3168485 := bbase (se 4 (by rfl) ⟨297045, by rfl⟩ : syracuseStep 3168485 = 594091) (by norm_num)
theorem B1669369 : Blo 1482061 1669369 := bbase (se 2 (by rfl) ⟨626013, by rfl⟩ : syracuseStep 1669369 = 1252027) (by norm_num)
theorem B12024085 : Blo 1482061 12024085 := bbase (se 6 (by rfl) ⟨281814, by rfl⟩ : syracuseStep 12024085 = 563629) (by norm_num)
theorem B1669405 : Blo 1482061 1669405 := bbase (se 3 (by rfl) ⟨313013, by rfl⟩ : syracuseStep 1669405 = 626027) (by norm_num)
theorem B2816309 : Blo 1482061 2816309 := bbase (se 5 (by rfl) ⟨132014, by rfl⟩ : syracuseStep 2816309 = 264029) (by norm_num)
theorem B1669441 : Blo 1482061 1669441 := bbase (se 2 (by rfl) ⟨626040, by rfl⟩ : syracuseStep 1669441 = 1252081) (by norm_num)
theorem B19003733 : Blo 1482061 19003733 := bbase (se 10 (by rfl) ⟨27837, by rfl⟩ : syracuseStep 19003733 = 55675) (by norm_num)
theorem B2111845 : Blo 1482061 2111845 := bbase (se 4 (by rfl) ⟨197985, by rfl⟩ : syracuseStep 2111845 = 395971) (by norm_num)
theorem B1669477 : Blo 1482061 1669477 := bbase (se 4 (by rfl) ⟨156513, by rfl⟩ : syracuseStep 1669477 = 313027) (by norm_num)
theorem B1669513 : Blo 1482061 1669513 := bbase (se 2 (by rfl) ⟨626067, by rfl⟩ : syracuseStep 1669513 = 1252135) (by norm_num)
theorem B1669549 : Blo 1482061 1669549 := bbase (se 3 (by rfl) ⟨313040, by rfl⟩ : syracuseStep 1669549 = 626081) (by norm_num)
theorem B2816461 : Blo 1482061 2816461 := bbase (se 3 (by rfl) ⟨528086, by rfl⟩ : syracuseStep 2816461 = 1056173) (by norm_num)
theorem B3807701 : Blo 1482061 3807701 := bbase (se 7 (by rfl) ⟨44621, by rfl⟩ : syracuseStep 3807701 = 89243) (by norm_num)
theorem B2005501 : Blo 1482061 2005501 := bbase (se 3 (by rfl) ⟨376031, by rfl⟩ : syracuseStep 2005501 = 752063) (by norm_num)
theorem B3045893 : Blo 1482061 3045893 := bbase (se 4 (by rfl) ⟨285552, by rfl⟩ : syracuseStep 3045893 = 571105) (by norm_num)
theorem B5003909 : Blo 1482061 5003909 := bbase (se 4 (by rfl) ⟨469116, by rfl⟩ : syracuseStep 5003909 = 938233) (by norm_num)
theorem B2816765 : Blo 1482061 2816765 := bbase (se 3 (by rfl) ⟨528143, by rfl⟩ : syracuseStep 2816765 = 1056287) (by norm_num)
theorem B2538253 : Blo 1482061 2538253 := bbase (se 3 (by rfl) ⟨475922, by rfl⟩ : syracuseStep 2538253 = 951845) (by norm_num)
theorem B7510805 : Blo 1482061 7510805 := bbase (se 6 (by rfl) ⟨176034, by rfl⟩ : syracuseStep 7510805 = 352069) (by norm_num)
theorem B2374429 : Blo 1482061 2374429 := bbase (se 3 (by rfl) ⟨445205, by rfl⟩ : syracuseStep 2374429 = 890411) (by norm_num)
theorem B3382093 : Blo 1482061 3382093 := bbase (se 3 (by rfl) ⟨634142, by rfl⟩ : syracuseStep 3382093 = 1268285) (by norm_num)
theorem B1604437 : Blo 1482061 1604437 := bbase (se 9 (by rfl) ⟨4700, by rfl⟩ : syracuseStep 1604437 = 9401) (by norm_num)
theorem B4225877 : Blo 1482061 4225877 := bbase (se 9 (by rfl) ⟨12380, by rfl⟩ : syracuseStep 4225877 = 24761) (by norm_num)
theorem B2112437 : Blo 1482061 2112437 := bbase (se 5 (by rfl) ⟨99020, by rfl⟩ : syracuseStep 2112437 = 198041) (by norm_num)
theorem B7322581 : Blo 1482061 7322581 := bbase (se 7 (by rfl) ⟨85811, by rfl⟩ : syracuseStep 7322581 = 171623) (by norm_num)
theorem B2112517 : Blo 1482061 2112517 := bbase (se 4 (by rfl) ⟨198048, by rfl⟩ : syracuseStep 2112517 = 396097) (by norm_num)
theorem B5004341 : Blo 1482061 5004341 := bbase (se 5 (by rfl) ⟨234578, by rfl⟩ : syracuseStep 5004341 = 469157) (by norm_num)
theorem B3169373 : Blo 1482061 3169373 := bbase (se 3 (by rfl) ⟨594257, by rfl⟩ : syracuseStep 3169373 = 1188515) (by norm_num)
theorem B2112637 : Blo 1482061 2112637 := bbase (se 3 (by rfl) ⟨396119, by rfl⟩ : syracuseStep 2112637 = 792239) (by norm_num)
theorem B7503029 : Blo 1482061 7503029 := bbase (se 5 (by rfl) ⟨351704, by rfl⟩ : syracuseStep 7503029 = 703409) (by norm_num)
theorem B2374877 : Blo 1482061 2374877 := bbase (se 3 (by rfl) ⟨445289, by rfl⟩ : syracuseStep 2374877 = 890579) (by norm_num)
theorem B2112733 : Blo 1482061 2112733 := bbase (se 3 (by rfl) ⟨396137, by rfl⟩ : syracuseStep 2112733 = 792275) (by norm_num)
theorem B7126325 : Blo 1482061 7126325 := bbase (se 5 (by rfl) ⟨334046, by rfl⟩ : syracuseStep 7126325 = 668093) (by norm_num)
theorem B2375077 : Blo 1482061 2375077 := bbase (se 4 (by rfl) ⟨222663, by rfl⟩ : syracuseStep 2375077 = 445327) (by norm_num)
theorem B5627333 : Blo 1482061 5627333 := bbase (se 4 (by rfl) ⟨527562, by rfl⟩ : syracuseStep 5627333 = 1055125) (by norm_num)
theorem B5004773 : Blo 1482061 5004773 := bbase (se 4 (by rfl) ⟨469197, by rfl⟩ : syracuseStep 5004773 = 938395) (by norm_num)
theorem B3006029 : Blo 1482061 3006029 := bbase (se 3 (by rfl) ⟨563630, by rfl⟩ : syracuseStep 3006029 = 1127261) (by norm_num)
theorem B7126613 : Blo 1482061 7126613 := bbase (se 8 (by rfl) ⟨41757, by rfl⟩ : syracuseStep 7126613 = 83515) (by norm_num)
theorem B3210877 : Blo 1482061 3210877 := bbase (se 3 (by rfl) ⟨602039, by rfl⟩ : syracuseStep 3210877 = 1204079) (by norm_num)
theorem B1523333 : Blo 1482061 1523333 := bbase (se 4 (by rfl) ⟨142812, by rfl⟩ : syracuseStep 1523333 = 285625) (by norm_num)
theorem B2375333 : Blo 1482061 2375333 := bbase (se 4 (by rfl) ⟨222687, by rfl⟩ : syracuseStep 2375333 = 445375) (by norm_num)
theorem B1875737 : Blo 1482061 1875737 := bbase (se 2 (by rfl) ⟨703401, by rfl⟩ : syracuseStep 1875737 = 1406803) (by norm_num)
theorem B3751717 : Blo 1482061 3751717 := bbase (se 4 (by rfl) ⟨351723, by rfl⟩ : syracuseStep 3751717 = 703447) (by norm_num)
theorem B1875793 : Blo 1482061 1875793 := bbase (se 2 (by rfl) ⟨703422, by rfl⟩ : syracuseStep 1875793 = 1406845) (by norm_num)
theorem B3751829 : Blo 1482061 3751829 := bbase (se 6 (by rfl) ⟨87933, by rfl⟩ : syracuseStep 3751829 = 175867) (by norm_num)
theorem B5005205 : Blo 1482061 5005205 := bbase (se 6 (by rfl) ⟨117309, by rfl⟩ : syracuseStep 5005205 = 234619) (by norm_num)
theorem B1605529 : Blo 1482061 1605529 := bbase (se 2 (by rfl) ⟨602073, by rfl⟩ : syracuseStep 1605529 = 1204147) (by norm_num)
theorem B1875889 : Blo 1482061 1875889 := bbase (se 2 (by rfl) ⟨703458, by rfl⟩ : syracuseStep 1875889 = 1406917) (by norm_num)
theorem B6332357 : Blo 1482061 6332357 := bbase (se 4 (by rfl) ⟨593658, by rfl⟩ : syracuseStep 6332357 = 1187317) (by norm_num)
theorem B1482755 : Blo 1482061 1482755 := bstep (se 1 (by rfl) ⟨1112066, by rfl⟩ : syracuseStep 1482755 = 2224133) B2224133
theorem B1482771 : Blo 1482061 1482771 := bstep (se 1 (by rfl) ⟨1112078, by rfl⟩ : syracuseStep 1482771 = 2224157) B2224157
theorem B1482787 : Blo 1482061 1482787 := bstep (se 1 (by rfl) ⟨1112090, by rfl⟩ : syracuseStep 1482787 = 2224181) B2224181
theorem B1482803 : Blo 1482061 1482803 := bstep (se 1 (by rfl) ⟨1112102, by rfl⟩ : syracuseStep 1482803 = 2224205) B2224205
theorem B32489525 : Blo 1482061 32489525 := bstep (se 5 (by rfl) ⟨1522946, by rfl⟩ : syracuseStep 32489525 = 3045893) B3045893
theorem B1482819 : Blo 1482061 1482819 := bstep (se 1 (by rfl) ⟨1112114, by rfl⟩ : syracuseStep 1482819 = 2224229) B2224229
theorem B1876051 : Blo 1482061 1876051 := bstep (se 1 (by rfl) ⟨1407038, by rfl⟩ : syracuseStep 1876051 = 2814077) B2814077
theorem B1482835 : Blo 1482061 1482835 := bstep (se 1 (by rfl) ⟨1112126, by rfl⟩ : syracuseStep 1482835 = 2224253) B2224253
theorem B1482851 : Blo 1482061 1482851 := bstep (se 1 (by rfl) ⟨1112138, by rfl⟩ : syracuseStep 1482851 = 2224277) B2224277
theorem B5005421 : Blo 1482061 5005421 := bstep (se 3 (by rfl) ⟨938516, by rfl⟩ : syracuseStep 5005421 = 1877033) B1877033
theorem B20299889 : Blo 1482061 20299889 := bstep (se 2 (by rfl) ⟨7612458, by rfl⟩ : syracuseStep 20299889 = 15224917) B15224917
theorem B1482867 : Blo 1482061 1482867 := bstep (se 1 (by rfl) ⟨1112150, by rfl⟩ : syracuseStep 1482867 = 2224301) B2224301
theorem B1482883 : Blo 1482061 1482883 := bstep (se 1 (by rfl) ⟨1112162, by rfl⟩ : syracuseStep 1482883 = 2224325) B2224325
theorem B1482899 : Blo 1482061 1482899 := bstep (se 1 (by rfl) ⟨1112174, by rfl⟩ : syracuseStep 1482899 = 2224349) B2224349
theorem B1482915 : Blo 1482061 1482915 := bstep (se 1 (by rfl) ⟨1112186, by rfl⟩ : syracuseStep 1482915 = 2224373) B2224373
theorem B5005475 : Blo 1482061 5005475 := bstep (se 1 (by rfl) ⟨3754106, by rfl⟩ : syracuseStep 5005475 = 7508213) B7508213
theorem B1482931 : Blo 1482061 1482931 := bstep (se 1 (by rfl) ⟨1112198, by rfl⟩ : syracuseStep 1482931 = 2224397) B2224397
theorem B1482947 : Blo 1482061 1482947 := bstep (se 1 (by rfl) ⟨1112210, by rfl⟩ : syracuseStep 1482947 = 2224421) B2224421
theorem B1482963 : Blo 1482061 1482963 := bstep (se 1 (by rfl) ⟨1112222, by rfl⟩ : syracuseStep 1482963 = 2224445) B2224445
theorem B1482979 : Blo 1482061 1482979 := bstep (se 1 (by rfl) ⟨1112234, by rfl⟩ : syracuseStep 1482979 = 2224469) B2224469
theorem B1482995 : Blo 1482061 1482995 := bstep (se 1 (by rfl) ⟨1112246, by rfl⟩ : syracuseStep 1482995 = 2224493) B2224493
theorem B1483011 : Blo 1482061 1483011 := bstep (se 1 (by rfl) ⟨1112258, by rfl⟩ : syracuseStep 1483011 = 2224517) B2224517
theorem B4006157 : Blo 1482061 4006157 := bstep (se 3 (by rfl) ⟨751154, by rfl⟩ : syracuseStep 4006157 = 1502309) B1502309
theorem B1483027 : Blo 1482061 1483027 := bstep (se 1 (by rfl) ⟨1112270, by rfl⟩ : syracuseStep 1483027 = 2224541) B2224541
theorem B7504163 : Blo 1482061 7504163 := bstep (se 1 (by rfl) ⟨5628122, by rfl⟩ : syracuseStep 7504163 = 11256245) B11256245
theorem B1483043 : Blo 1482061 1483043 := bstep (se 1 (by rfl) ⟨1112282, by rfl⟩ : syracuseStep 1483043 = 2224565) B2224565
theorem B1483059 : Blo 1482061 1483059 := bstep (se 1 (by rfl) ⟨1112294, by rfl⟩ : syracuseStep 1483059 = 2224589) B2224589
theorem B1483075 : Blo 1482061 1483075 := bstep (se 1 (by rfl) ⟨1112306, by rfl⟩ : syracuseStep 1483075 = 2224613) B2224613
theorem B1483091 : Blo 1482061 1483091 := bstep (se 1 (by rfl) ⟨1112318, by rfl⟩ : syracuseStep 1483091 = 2224637) B2224637
theorem B1483107 : Blo 1482061 1483107 := bstep (se 1 (by rfl) ⟨1112330, by rfl⟩ : syracuseStep 1483107 = 2224661) B2224661
theorem B16032113 : Blo 1482061 16032113 := bstep (se 2 (by rfl) ⟨6012042, by rfl⟩ : syracuseStep 16032113 = 12024085) B12024085
theorem B4751729 : Blo 1482061 4751729 := bstep (se 2 (by rfl) ⟨1781898, by rfl⟩ : syracuseStep 4751729 = 3563797) B3563797
theorem B1483123 : Blo 1482061 1483123 := bstep (se 1 (by rfl) ⟨1112342, by rfl⟩ : syracuseStep 1483123 = 2224685) B2224685
theorem B1483139 : Blo 1482061 1483139 := bstep (se 1 (by rfl) ⟨1112354, by rfl⟩ : syracuseStep 1483139 = 2224709) B2224709
theorem B1483155 : Blo 1482061 1483155 := bstep (se 1 (by rfl) ⟨1112366, by rfl⟩ : syracuseStep 1483155 = 2224733) B2224733
theorem B1483171 : Blo 1482061 1483171 := bstep (se 1 (by rfl) ⟨1112378, by rfl⟩ : syracuseStep 1483171 = 2224757) B2224757
theorem B5144995 : Blo 1482061 5144995 := bstep (se 1 (by rfl) ⟨3858746, by rfl⟩ : syracuseStep 5144995 = 7717493) B7717493
theorem B5005745 : Blo 1482061 5005745 := bstep (se 2 (by rfl) ⟨1877154, by rfl⟩ : syracuseStep 5005745 = 3754309) B3754309
theorem B1483187 : Blo 1482061 1483187 := bstep (se 1 (by rfl) ⟨1112390, by rfl⟩ : syracuseStep 1483187 = 2224781) B2224781
theorem B1483203 : Blo 1482061 1483203 := bstep (se 1 (by rfl) ⟨1112402, by rfl⟩ : syracuseStep 1483203 = 2224805) B2224805
theorem B1483219 : Blo 1482061 1483219 := bstep (se 1 (by rfl) ⟨1112414, by rfl⟩ : syracuseStep 1483219 = 2224829) B2224829
theorem B16892387 : Blo 1482061 16892387 := bstep (se 1 (by rfl) ⟨12669290, by rfl⟩ : syracuseStep 16892387 = 25338581) B25338581
theorem B1483235 : Blo 1482061 1483235 := bstep (se 1 (by rfl) ⟨1112426, by rfl⟩ : syracuseStep 1483235 = 2224853) B2224853
theorem B1483251 : Blo 1482061 1483251 := bstep (se 1 (by rfl) ⟨1112438, by rfl⟩ : syracuseStep 1483251 = 2224877) B2224877
theorem B1483267 : Blo 1482061 1483267 := bstep (se 1 (by rfl) ⟨1112450, by rfl⟩ : syracuseStep 1483267 = 2224901) B2224901
theorem B1483283 : Blo 1482061 1483283 := bstep (se 1 (by rfl) ⟨1112462, by rfl⟩ : syracuseStep 1483283 = 2224925) B2224925
theorem B1483299 : Blo 1482061 1483299 := bstep (se 1 (by rfl) ⟨1112474, by rfl⟩ : syracuseStep 1483299 = 2224949) B2224949
theorem B1483315 : Blo 1482061 1483315 := bstep (se 1 (by rfl) ⟨1112486, by rfl⟩ : syracuseStep 1483315 = 2224973) B2224973
theorem B1876547 : Blo 1482061 1876547 := bstep (se 1 (by rfl) ⟨1407410, by rfl⟩ : syracuseStep 1876547 = 2814821) B2814821
theorem B1483331 : Blo 1482061 1483331 := bstep (se 1 (by rfl) ⟨1112498, by rfl⟩ : syracuseStep 1483331 = 2224997) B2224997
theorem B6333005 : Blo 1482061 6333005 := bstep (se 3 (by rfl) ⟨1187438, by rfl⟩ : syracuseStep 6333005 = 2374877) B2374877
theorem B1483347 : Blo 1482061 1483347 := bstep (se 1 (by rfl) ⟨1112510, by rfl⟩ : syracuseStep 1483347 = 2225021) B2225021
theorem B1483363 : Blo 1482061 1483363 := bstep (se 1 (by rfl) ⟨1112522, by rfl⟩ : syracuseStep 1483363 = 2225045) B2225045
theorem B3334769 : Blo 1482061 3334769 := bstep (se 2 (by rfl) ⟨1250538, by rfl⟩ : syracuseStep 3334769 = 2501077) B2501077
theorem B1483379 : Blo 1482061 1483379 := bstep (se 1 (by rfl) ⟨1112534, by rfl⟩ : syracuseStep 1483379 = 2225069) B2225069
theorem B2376307 : Blo 1482061 2376307 := bstep (se 1 (by rfl) ⟨1782230, by rfl⟩ : syracuseStep 2376307 = 3564461) B3564461
theorem B3334787 : Blo 1482061 3334787 := bstep (se 1 (by rfl) ⟨2501090, by rfl⟩ : syracuseStep 3334787 = 5002181) B5002181
theorem B1483395 : Blo 1482061 1483395 := bstep (se 1 (by rfl) ⟨1112546, by rfl⟩ : syracuseStep 1483395 = 2225093) B2225093
theorem B1483411 : Blo 1482061 1483411 := bstep (se 1 (by rfl) ⟨1112558, by rfl⟩ : syracuseStep 1483411 = 2225117) B2225117
theorem B1483427 : Blo 1482061 1483427 := bstep (se 1 (by rfl) ⟨1112570, by rfl⟩ : syracuseStep 1483427 = 2225141) B2225141
theorem B1483443 : Blo 1482061 1483443 := bstep (se 1 (by rfl) ⟨1112582, by rfl⟩ : syracuseStep 1483443 = 2225165) B2225165
theorem B1483459 : Blo 1482061 1483459 := bstep (se 1 (by rfl) ⟨1112594, by rfl⟩ : syracuseStep 1483459 = 2225189) B2225189
theorem B1483475 : Blo 1482061 1483475 := bstep (se 1 (by rfl) ⟨1112606, by rfl⟩ : syracuseStep 1483475 = 2225213) B2225213
theorem B1483491 : Blo 1482061 1483491 := bstep (se 1 (by rfl) ⟨1112618, by rfl⟩ : syracuseStep 1483491 = 2225237) B2225237
theorem B28525283 : Blo 1482061 28525283 := bstep (se 1 (by rfl) ⟨21393962, by rfl⟩ : syracuseStep 28525283 = 42787925) B42787925
theorem B3752689 : Blo 1482061 3752689 := bstep (se 2 (by rfl) ⟨1407258, by rfl⟩ : syracuseStep 3752689 = 2814517) B2814517
theorem B1483507 : Blo 1482061 1483507 := bstep (se 1 (by rfl) ⟨1112630, by rfl⟩ : syracuseStep 1483507 = 2225261) B2225261
theorem B2409203 : Blo 1482061 2409203 := bstep (se 1 (by rfl) ⟨1806902, by rfl⟩ : syracuseStep 2409203 = 3613805) B3613805
theorem B1483523 : Blo 1482061 1483523 := bstep (se 1 (by rfl) ⟨1112642, by rfl⟩ : syracuseStep 1483523 = 2225285) B2225285
theorem B1483539 : Blo 1482061 1483539 := bstep (se 1 (by rfl) ⟨1112654, by rfl⟩ : syracuseStep 1483539 = 2225309) B2225309
theorem B1483555 : Blo 1482061 1483555 := bstep (se 1 (by rfl) ⟨1112666, by rfl⟩ : syracuseStep 1483555 = 2225333) B2225333
theorem B1483571 : Blo 1482061 1483571 := bstep (se 1 (by rfl) ⟨1112678, by rfl⟩ : syracuseStep 1483571 = 2225357) B2225357
theorem B1483587 : Blo 1482061 1483587 := bstep (se 1 (by rfl) ⟨1112690, by rfl⟩ : syracuseStep 1483587 = 2225381) B2225381
theorem B1483603 : Blo 1482061 1483603 := bstep (se 1 (by rfl) ⟨1112702, by rfl⟩ : syracuseStep 1483603 = 2225405) B2225405
theorem B1483619 : Blo 1482061 1483619 := bstep (se 1 (by rfl) ⟨1112714, by rfl⟩ : syracuseStep 1483619 = 2225429) B2225429
theorem B3212131 : Blo 1482061 3212131 := bstep (se 1 (by rfl) ⟨2409098, by rfl⟩ : syracuseStep 3212131 = 4818197) B4818197
theorem B1483635 : Blo 1482061 1483635 := bstep (se 1 (by rfl) ⟨1112726, by rfl⟩ : syracuseStep 1483635 = 2225453) B2225453
theorem B1483651 : Blo 1482061 1483651 := bstep (se 1 (by rfl) ⟨1112738, by rfl⟩ : syracuseStep 1483651 = 2225477) B2225477
theorem B3335057 : Blo 1482061 3335057 := bstep (se 2 (by rfl) ⟨1250646, by rfl⟩ : syracuseStep 3335057 = 2501293) B2501293
theorem B1483667 : Blo 1482061 1483667 := bstep (se 1 (by rfl) ⟨1112750, by rfl⟩ : syracuseStep 1483667 = 2225501) B2225501
theorem B3335075 : Blo 1482061 3335075 := bstep (se 1 (by rfl) ⟨2501306, by rfl⟩ : syracuseStep 3335075 = 5002613) B5002613
theorem B1483683 : Blo 1482061 1483683 := bstep (se 1 (by rfl) ⟨1112762, by rfl⟩ : syracuseStep 1483683 = 2225525) B2225525
theorem B1483699 : Blo 1482061 1483699 := bstep (se 1 (by rfl) ⟨1112774, by rfl⟩ : syracuseStep 1483699 = 2225549) B2225549
theorem B1483715 : Blo 1482061 1483715 := bstep (se 1 (by rfl) ⟨1112786, by rfl⟩ : syracuseStep 1483715 = 2225573) B2225573
theorem B5006285 : Blo 1482061 5006285 := bstep (se 3 (by rfl) ⟨938678, by rfl⟩ : syracuseStep 5006285 = 1877357) B1877357
theorem B1483731 : Blo 1482061 1483731 := bstep (se 1 (by rfl) ⟨1112798, by rfl⟩ : syracuseStep 1483731 = 2225597) B2225597
theorem B18039779 : Blo 1482061 18039779 := bstep (se 1 (by rfl) ⟨13529834, by rfl⟩ : syracuseStep 18039779 = 27059669) B27059669
theorem B1483747 : Blo 1482061 1483747 := bstep (se 1 (by rfl) ⟨1112810, by rfl⟩ : syracuseStep 1483747 = 2225621) B2225621
theorem B1483763 : Blo 1482061 1483763 := bstep (se 1 (by rfl) ⟨1112822, by rfl⟩ : syracuseStep 1483763 = 2225645) B2225645
theorem B3752963 : Blo 1482061 3752963 := bstep (se 1 (by rfl) ⟨2814722, by rfl⟩ : syracuseStep 3752963 = 5629445) B5629445
theorem B5006339 : Blo 1482061 5006339 := bstep (se 1 (by rfl) ⟨3754754, by rfl⟩ : syracuseStep 5006339 = 7509509) B7509509
theorem B1483779 : Blo 1482061 1483779 := bstep (se 1 (by rfl) ⟨1112834, by rfl⟩ : syracuseStep 1483779 = 2225669) B2225669
theorem B3384337 : Blo 1482061 3384337 := bstep (se 2 (by rfl) ⟨1269126, by rfl⟩ : syracuseStep 3384337 = 2538253) B2538253
theorem B1483795 : Blo 1482061 1483795 := bstep (se 1 (by rfl) ⟨1112846, by rfl⟩ : syracuseStep 1483795 = 2225693) B2225693
theorem B1483811 : Blo 1482061 1483811 := bstep (se 1 (by rfl) ⟨1112858, by rfl⟩ : syracuseStep 1483811 = 2225717) B2225717
theorem B1483827 : Blo 1482061 1483827 := bstep (se 1 (by rfl) ⟨1112870, by rfl⟩ : syracuseStep 1483827 = 2225741) B2225741
theorem B2253889 : Blo 1482061 2253889 := bstep (se 2 (by rfl) ⟨845208, by rfl⟩ : syracuseStep 2253889 = 1690417) B1690417
theorem B1483843 : Blo 1482061 1483843 := bstep (se 1 (by rfl) ⟨1112882, by rfl⟩ : syracuseStep 1483843 = 2225765) B2225765
theorem B7504973 : Blo 1482061 7504973 := bstep (se 3 (by rfl) ⟨1407182, by rfl⟩ : syracuseStep 7504973 = 2814365) B2814365
theorem B1483859 : Blo 1482061 1483859 := bstep (se 1 (by rfl) ⟨1112894, by rfl⟩ : syracuseStep 1483859 = 2225789) B2225789
theorem B3564643 : Blo 1482061 3564643 := bstep (se 1 (by rfl) ⟨2673482, by rfl⟩ : syracuseStep 3564643 = 5346965) B5346965
theorem B1483875 : Blo 1482061 1483875 := bstep (se 1 (by rfl) ⟨1112906, by rfl⟩ : syracuseStep 1483875 = 2225813) B2225813
theorem B1483891 : Blo 1482061 1483891 := bstep (se 1 (by rfl) ⟨1112918, by rfl⟩ : syracuseStep 1483891 = 2225837) B2225837
theorem B1483907 : Blo 1482061 1483907 := bstep (se 1 (by rfl) ⟨1112930, by rfl⟩ : syracuseStep 1483907 = 2225861) B2225861
theorem B1483923 : Blo 1482061 1483923 := bstep (se 1 (by rfl) ⟨1112942, by rfl⟩ : syracuseStep 1483923 = 2225885) B2225885
theorem B1483939 : Blo 1482061 1483939 := bstep (se 1 (by rfl) ⟨1112954, by rfl⟩ : syracuseStep 1483939 = 2225909) B2225909
theorem B3335345 : Blo 1482061 3335345 := bstep (se 2 (by rfl) ⟨1250754, by rfl⟩ : syracuseStep 3335345 = 2501509) B2501509
theorem B1483955 : Blo 1482061 1483955 := bstep (se 1 (by rfl) ⟨1112966, by rfl⟩ : syracuseStep 1483955 = 2225933) B2225933
theorem B3335363 : Blo 1482061 3335363 := bstep (se 1 (by rfl) ⟨2501522, by rfl⟩ : syracuseStep 3335363 = 5003045) B5003045
theorem B3753155 : Blo 1482061 3753155 := bstep (se 1 (by rfl) ⟨2814866, by rfl⟩ : syracuseStep 3753155 = 5629733) B5629733
theorem B1483971 : Blo 1482061 1483971 := bstep (se 1 (by rfl) ⟨1112978, by rfl⟩ : syracuseStep 1483971 = 2225957) B2225957
theorem B1483987 : Blo 1482061 1483987 := bstep (se 1 (by rfl) ⟨1112990, by rfl⟩ : syracuseStep 1483987 = 2225981) B2225981
theorem B1484003 : Blo 1482061 1484003 := bstep (se 1 (by rfl) ⟨1113002, by rfl⟩ : syracuseStep 1484003 = 2226005) B2226005
theorem B1484019 : Blo 1482061 1484019 := bstep (se 1 (by rfl) ⟨1113014, by rfl⟩ : syracuseStep 1484019 = 2226029) B2226029
theorem B1877251 : Blo 1482061 1877251 := bstep (se 1 (by rfl) ⟨1407938, by rfl⟩ : syracuseStep 1877251 = 2815877) B2815877
theorem B1484035 : Blo 1482061 1484035 := bstep (se 1 (by rfl) ⟨1113026, by rfl⟩ : syracuseStep 1484035 = 2226053) B2226053
theorem B5006609 : Blo 1482061 5006609 := bstep (se 2 (by rfl) ⟨1877478, by rfl⟩ : syracuseStep 5006609 = 3754957) B3754957
theorem B1484051 : Blo 1482061 1484051 := bstep (se 1 (by rfl) ⟨1113038, by rfl⟩ : syracuseStep 1484051 = 2226077) B2226077
theorem B10691909 : Blo 1482061 10691909 := bstep (se 4 (by rfl) ⟨1002366, by rfl⟩ : syracuseStep 10691909 = 2004733) B2004733
theorem B1877347 : Blo 1482061 1877347 := bstep (se 1 (by rfl) ⟨1408010, by rfl⟩ : syracuseStep 1877347 = 2816021) B2816021
theorem B2852209 : Blo 1482061 2852209 := bstep (se 2 (by rfl) ⟨1069578, by rfl⟩ : syracuseStep 2852209 = 2139157) B2139157
theorem B2254225 : Blo 1482061 2254225 := bstep (se 2 (by rfl) ⟨845334, by rfl⟩ : syracuseStep 2254225 = 1690669) B1690669
theorem B3335633 : Blo 1482061 3335633 := bstep (se 2 (by rfl) ⟨1250862, by rfl⟩ : syracuseStep 3335633 = 2501725) B2501725
theorem B3335651 : Blo 1482061 3335651 := bstep (se 1 (by rfl) ⟨2501738, by rfl⟩ : syracuseStep 3335651 = 5003477) B5003477
theorem B2672099 : Blo 1482061 2672099 := bstep (se 1 (by rfl) ⟨2004074, by rfl⟩ : syracuseStep 2672099 = 4008149) B4008149
theorem B11888099 : Blo 1482061 11888099 := bstep (se 1 (by rfl) ⟨8916074, by rfl⟩ : syracuseStep 11888099 = 17832149) B17832149
theorem B3335921 : Blo 1482061 3335921 := bstep (se 2 (by rfl) ⟨1250970, by rfl⟩ : syracuseStep 3335921 = 2501941) B2501941
theorem B3335939 : Blo 1482061 3335939 := bstep (se 1 (by rfl) ⟨2501954, by rfl⟩ : syracuseStep 3335939 = 5003909) B5003909
theorem B4007693 : Blo 1482061 4007693 := bstep (se 3 (by rfl) ⟨751442, by rfl⟩ : syracuseStep 4007693 = 1502885) B1502885
theorem B5007149 : Blo 1482061 5007149 := bstep (se 3 (by rfl) ⟨938840, by rfl⟩ : syracuseStep 5007149 = 1877681) B1877681
theorem B8447813 : Blo 1482061 8447813 := bstep (se 4 (by rfl) ⟨791982, by rfl⟩ : syracuseStep 8447813 = 1583965) B1583965
theorem B1877843 : Blo 1482061 1877843 := bstep (se 1 (by rfl) ⟨1408382, by rfl⟩ : syracuseStep 1877843 = 2816765) B2816765
theorem B9504611 : Blo 1482061 9504611 := bstep (se 1 (by rfl) ⟨7128458, by rfl⟩ : syracuseStep 9504611 = 14256917) B14256917
theorem B5007203 : Blo 1482061 5007203 := bstep (se 1 (by rfl) ⟨3755402, by rfl⟩ : syracuseStep 5007203 = 7510805) B7510805
theorem B9496433 : Blo 1482061 9496433 := bstep (se 2 (by rfl) ⟨3561162, by rfl⟩ : syracuseStep 9496433 = 7122325) B7122325
theorem B5072881 : Blo 1482061 5072881 := bstep (se 2 (by rfl) ⟨1902330, by rfl⟩ : syracuseStep 5072881 = 3804661) B3804661
theorem B7129073 : Blo 1482061 7129073 := bstep (se 2 (by rfl) ⟨2673402, by rfl⟩ : syracuseStep 7129073 = 5346805) B5346805
theorem B5343245 : Blo 1482061 5343245 := bstep (se 3 (by rfl) ⟨1001858, by rfl⟩ : syracuseStep 5343245 = 2003717) B2003717
theorem B3336209 : Blo 1482061 3336209 := bstep (se 2 (by rfl) ⟨1251078, by rfl⟩ : syracuseStep 3336209 = 2502157) B2502157
theorem B3336227 : Blo 1482061 3336227 := bstep (se 1 (by rfl) ⟨2502170, by rfl⟩ : syracuseStep 3336227 = 5004341) B5004341
theorem B3754097 : Blo 1482061 3754097 := bstep (se 2 (by rfl) ⟨1407786, by rfl⟩ : syracuseStep 3754097 = 2815573) B2815573
theorem B5007473 : Blo 1482061 5007473 := bstep (se 2 (by rfl) ⟨1877802, by rfl⟩ : syracuseStep 5007473 = 3755605) B3755605
theorem B3754147 : Blo 1482061 3754147 := bstep (se 1 (by rfl) ⟨2815610, by rfl⟩ : syracuseStep 3754147 = 5631221) B5631221
theorem B4221229 : Blo 1482061 4221229 := bstep (se 3 (by rfl) ⟨791480, by rfl⟩ : syracuseStep 4221229 = 1582961) B1582961
theorem B3336497 : Blo 1482061 3336497 := bstep (se 2 (by rfl) ⟨1251186, by rfl⟩ : syracuseStep 3336497 = 2502373) B2502373
theorem B3754289 : Blo 1482061 3754289 := bstep (se 2 (by rfl) ⟨1407858, by rfl⟩ : syracuseStep 3754289 = 2815717) B2815717
theorem B3336515 : Blo 1482061 3336515 := bstep (se 1 (by rfl) ⟨2502386, by rfl⟩ : syracuseStep 3336515 = 5004773) B5004773
theorem B4753741 : Blo 1482061 4753741 := bstep (se 3 (by rfl) ⟨891326, by rfl⟩ : syracuseStep 4753741 = 1782653) B1782653
theorem B2501057 : Blo 1482061 2501057 := bstep (se 2 (by rfl) ⟨937896, by rfl⟩ : syracuseStep 2501057 = 1875793) B1875793
theorem B1583555 : Blo 1482061 1583555 := bstep (se 1 (by rfl) ⟨1187666, by rfl⟩ : syracuseStep 1583555 = 2375333) B2375333
theorem B39053765 : Blo 1482061 39053765 := bstep (se 4 (by rfl) ⟨3661290, by rfl⟩ : syracuseStep 39053765 = 7322581) B7322581
theorem B4221389 : Blo 1482061 4221389 := bstep (se 3 (by rfl) ⟨791510, by rfl⟩ : syracuseStep 4221389 = 1583021) B1583021
theorem B2140705 : Blo 1482061 2140705 := bstep (se 2 (by rfl) ⟨802764, by rfl⟩ : syracuseStep 2140705 = 1605529) B1605529
theorem B2501185 : Blo 1482061 2501185 := bstep (se 2 (by rfl) ⟨937944, by rfl⟩ : syracuseStep 2501185 = 1875889) B1875889
theorem B3336785 : Blo 1482061 3336785 := bstep (se 2 (by rfl) ⟨1251294, by rfl⟩ : syracuseStep 3336785 = 2502589) B2502589
theorem B2501219 : Blo 1482061 2501219 := bstep (se 1 (by rfl) ⟨1875914, by rfl⟩ : syracuseStep 2501219 = 3751829) B3751829
theorem B3336803 : Blo 1482061 3336803 := bstep (se 1 (by rfl) ⟨2502602, by rfl⟩ : syracuseStep 3336803 = 5005205) B5005205
theorem B4221571 : Blo 1482061 4221571 := bstep (se 1 (by rfl) ⟨3166178, by rfl⟩ : syracuseStep 4221571 = 6332357) B6332357
theorem B5008013 : Blo 1482061 5008013 := bstep (se 3 (by rfl) ⟨939002, by rfl⟩ : syracuseStep 5008013 = 1878005) B1878005
theorem B5008067 : Blo 1482061 5008067 := bstep (se 1 (by rfl) ⟨3756050, by rfl⟩ : syracuseStep 5008067 = 7512101) B7512101
theorem B2501347 : Blo 1482061 2501347 := bstep (se 1 (by rfl) ⟨1876010, by rfl⟩ : syracuseStep 2501347 = 3752021) B3752021
theorem B5630705 : Blo 1482061 5630705 := bstep (se 2 (by rfl) ⟨2111514, by rfl⟩ : syracuseStep 5630705 = 4223029) B4223029
theorem B9497357 : Blo 1482061 9497357 := bstep (se 3 (by rfl) ⟨1780754, by rfl⟩ : syracuseStep 9497357 = 3561509) B3561509
theorem B4754189 : Blo 1482061 4754189 := bstep (se 3 (by rfl) ⟨891410, by rfl⟩ : syracuseStep 4754189 = 1782821) B1782821
theorem B2501489 : Blo 1482061 2501489 := bstep (se 2 (by rfl) ⟨938058, by rfl⟩ : syracuseStep 2501489 = 1876117) B1876117
theorem B3337073 : Blo 1482061 3337073 := bstep (se 2 (by rfl) ⟨1251402, by rfl⟩ : syracuseStep 3337073 = 2502805) B2502805
theorem B3337091 : Blo 1482061 3337091 := bstep (se 1 (by rfl) ⟨2502818, by rfl⟩ : syracuseStep 3337091 = 5005637) B5005637
theorem B5008337 : Blo 1482061 5008337 := bstep (se 2 (by rfl) ⟨1878126, by rfl⟩ : syracuseStep 5008337 = 3756253) B3756253
theorem B2501617 : Blo 1482061 2501617 := bstep (se 2 (by rfl) ⟨938106, by rfl⟩ : syracuseStep 2501617 = 1876213) B1876213
theorem B2223107 : Blo 1482061 2223107 := bstep (se 1 (by rfl) ⟨1667330, by rfl⟩ : syracuseStep 2223107 = 3334661) B3334661
theorem B2501651 : Blo 1482061 2501651 := bstep (se 1 (by rfl) ⟨1876238, by rfl⟩ : syracuseStep 2501651 = 3752477) B3752477
theorem B2223137 : Blo 1482061 2223137 := bstep (se 2 (by rfl) ⟨833676, by rfl⟩ : syracuseStep 2223137 = 1667353) B1667353
theorem B2223155 : Blo 1482061 2223155 := bstep (se 1 (by rfl) ⟨1667366, by rfl⟩ : syracuseStep 2223155 = 3334733) B3334733
theorem B2223185 : Blo 1482061 2223185 := bstep (se 2 (by rfl) ⟨833694, by rfl⟩ : syracuseStep 2223185 = 1667389) B1667389
theorem B2223203 : Blo 1482061 2223203 := bstep (se 1 (by rfl) ⟨1667402, by rfl⟩ : syracuseStep 2223203 = 3334805) B3334805
theorem B2223233 : Blo 1482061 2223233 := bstep (se 2 (by rfl) ⟨833712, by rfl⟩ : syracuseStep 2223233 = 1667425) B1667425
theorem B5344397 : Blo 1482061 5344397 := bstep (se 3 (by rfl) ⟨1002074, by rfl⟩ : syracuseStep 5344397 = 2004149) B2004149
theorem B3337361 : Blo 1482061 3337361 := bstep (se 2 (by rfl) ⟨1251510, by rfl⟩ : syracuseStep 3337361 = 2503021) B2503021
theorem B2223251 : Blo 1482061 2223251 := bstep (se 1 (by rfl) ⟨1667438, by rfl⟩ : syracuseStep 2223251 = 3334877) B3334877
theorem B2501779 : Blo 1482061 2501779 := bstep (se 1 (by rfl) ⟨1876334, by rfl⟩ : syracuseStep 2501779 = 3752669) B3752669
theorem B3337379 : Blo 1482061 3337379 := bstep (se 1 (by rfl) ⟨2503034, by rfl⟩ : syracuseStep 3337379 = 5006069) B5006069
theorem B2223281 : Blo 1482061 2223281 := bstep (se 2 (by rfl) ⟨833730, by rfl⟩ : syracuseStep 2223281 = 1667461) B1667461
theorem B1584307 : Blo 1482061 1584307 := bstep (se 1 (by rfl) ⟨1188230, by rfl⟩ : syracuseStep 1584307 = 2376461) B2376461
theorem B2223299 : Blo 1482061 2223299 := bstep (se 1 (by rfl) ⟨1667474, by rfl⟩ : syracuseStep 2223299 = 3334949) B3334949
theorem B2223329 : Blo 1482061 2223329 := bstep (se 2 (by rfl) ⟨833748, by rfl⟩ : syracuseStep 2223329 = 1667497) B1667497
theorem B2223347 : Blo 1482061 2223347 := bstep (se 1 (by rfl) ⟨1667510, by rfl⟩ : syracuseStep 2223347 = 3335021) B3335021
theorem B2223377 : Blo 1482061 2223377 := bstep (se 2 (by rfl) ⟨833766, by rfl⟩ : syracuseStep 2223377 = 1667533) B1667533
theorem B3755281 : Blo 1482061 3755281 := bstep (se 2 (by rfl) ⟨1408230, by rfl⟩ : syracuseStep 3755281 = 2816461) B2816461
theorem B2501921 : Blo 1482061 2501921 := bstep (se 2 (by rfl) ⟨938220, by rfl⟩ : syracuseStep 2501921 = 1876441) B1876441
theorem B2223395 : Blo 1482061 2223395 := bstep (se 1 (by rfl) ⟨1667546, by rfl⟩ : syracuseStep 2223395 = 3335093) B3335093
theorem B2223425 : Blo 1482061 2223425 := bstep (se 2 (by rfl) ⟨833784, by rfl⟩ : syracuseStep 2223425 = 1667569) B1667569
theorem B2674001 : Blo 1482061 2674001 := bstep (se 2 (by rfl) ⟨1002750, by rfl⟩ : syracuseStep 2674001 = 2005501) B2005501
theorem B2223443 : Blo 1482061 2223443 := bstep (se 1 (by rfl) ⟨1667582, by rfl⟩ : syracuseStep 2223443 = 3335165) B3335165
theorem B2223473 : Blo 1482061 2223473 := bstep (se 2 (by rfl) ⟨833802, by rfl⟩ : syracuseStep 2223473 = 1667605) B1667605
theorem B22842737 : Blo 1482061 22842737 := bstep (se 2 (by rfl) ⟨8566026, by rfl⟩ : syracuseStep 22842737 = 17132053) B17132053
theorem B2223491 : Blo 1482061 2223491 := bstep (se 1 (by rfl) ⟨1667618, by rfl⟩ : syracuseStep 2223491 = 3335237) B3335237
theorem B2223521 : Blo 1482061 2223521 := bstep (se 2 (by rfl) ⟨833820, by rfl⟩ : syracuseStep 2223521 = 1667641) B1667641
theorem B2502049 : Blo 1482061 2502049 := bstep (se 2 (by rfl) ⟨938268, by rfl⟩ : syracuseStep 2502049 = 1876537) B1876537
theorem B3337649 : Blo 1482061 3337649 := bstep (se 2 (by rfl) ⟨1251618, by rfl⟩ : syracuseStep 3337649 = 2503237) B2503237
theorem B2223539 : Blo 1482061 2223539 := bstep (se 1 (by rfl) ⟨1667654, by rfl⟩ : syracuseStep 2223539 = 3335309) B3335309
theorem B2502083 : Blo 1482061 2502083 := bstep (se 1 (by rfl) ⟨1876562, by rfl⟩ : syracuseStep 2502083 = 3753125) B3753125
theorem B3337667 : Blo 1482061 3337667 := bstep (se 1 (by rfl) ⟨2503250, by rfl⟩ : syracuseStep 3337667 = 5006501) B5006501
theorem B2223569 : Blo 1482061 2223569 := bstep (se 2 (by rfl) ⟨833838, by rfl⟩ : syracuseStep 2223569 = 1667677) B1667677
theorem B2223587 : Blo 1482061 2223587 := bstep (se 1 (by rfl) ⟨1667690, by rfl⟩ : syracuseStep 2223587 = 3335381) B3335381
theorem B2223617 : Blo 1482061 2223617 := bstep (se 2 (by rfl) ⟨833856, by rfl⟩ : syracuseStep 2223617 = 1667713) B1667713
theorem B2223635 : Blo 1482061 2223635 := bstep (se 1 (by rfl) ⟨1667726, by rfl⟩ : syracuseStep 2223635 = 3335453) B3335453
theorem B3755555 : Blo 1482061 3755555 := bstep (se 1 (by rfl) ⟨2816666, by rfl⟩ : syracuseStep 3755555 = 5633333) B5633333
theorem B2223665 : Blo 1482061 2223665 := bstep (se 2 (by rfl) ⟨833874, by rfl⟩ : syracuseStep 2223665 = 1667749) B1667749
theorem B2223683 : Blo 1482061 2223683 := bstep (se 1 (by rfl) ⟨1667762, by rfl⟩ : syracuseStep 2223683 = 3335525) B3335525
theorem B2502211 : Blo 1482061 2502211 := bstep (se 1 (by rfl) ⟨1876658, by rfl⟩ : syracuseStep 2502211 = 3753317) B3753317
theorem B2223713 : Blo 1482061 2223713 := bstep (se 2 (by rfl) ⟨833892, by rfl⟩ : syracuseStep 2223713 = 1667785) B1667785
theorem B28880497 : Blo 1482061 28880497 := bstep (se 2 (by rfl) ⟨10830186, by rfl⟩ : syracuseStep 28880497 = 21660373) B21660373
theorem B2223731 : Blo 1482061 2223731 := bstep (se 1 (by rfl) ⟨1667798, by rfl⟩ : syracuseStep 2223731 = 3335597) B3335597
theorem B2223761 : Blo 1482061 2223761 := bstep (se 2 (by rfl) ⟨833910, by rfl⟩ : syracuseStep 2223761 = 1667821) B1667821
theorem B2223779 : Blo 1482061 2223779 := bstep (se 1 (by rfl) ⟨1667834, by rfl⟩ : syracuseStep 2223779 = 3335669) B3335669
theorem B2223809 : Blo 1482061 2223809 := bstep (se 2 (by rfl) ⟨833928, by rfl⟩ : syracuseStep 2223809 = 1667857) B1667857
theorem B8015557 : Blo 1482061 8015557 := bstep (se 4 (by rfl) ⟨751458, by rfl⟩ : syracuseStep 8015557 = 1502917) B1502917
theorem B3165905 : Blo 1482061 3165905 := bstep (se 2 (by rfl) ⟨1187214, by rfl⟩ : syracuseStep 3165905 = 2374429) B2374429
theorem B2502353 : Blo 1482061 2502353 := bstep (se 2 (by rfl) ⟨938382, by rfl⟩ : syracuseStep 2502353 = 1876765) B1876765
theorem B2223827 : Blo 1482061 2223827 := bstep (se 1 (by rfl) ⟨1667870, by rfl⟩ : syracuseStep 2223827 = 3335741) B3335741
theorem B4009681 : Blo 1482061 4009681 := bstep (se 2 (by rfl) ⟨1503630, by rfl⟩ : syracuseStep 4009681 = 3007261) B3007261
theorem B3337937 : Blo 1482061 3337937 := bstep (se 2 (by rfl) ⟨1251726, by rfl⟩ : syracuseStep 3337937 = 2503453) B2503453
theorem B3337955 : Blo 1482061 3337955 := bstep (se 1 (by rfl) ⟨2503466, by rfl⟩ : syracuseStep 3337955 = 5006933) B5006933
theorem B3755747 : Blo 1482061 3755747 := bstep (se 1 (by rfl) ⟨2816810, by rfl⟩ : syracuseStep 3755747 = 5633621) B5633621
theorem B2223857 : Blo 1482061 2223857 := bstep (se 2 (by rfl) ⟨833946, by rfl⟩ : syracuseStep 2223857 = 1667893) B1667893
theorem B2223875 : Blo 1482061 2223875 := bstep (se 1 (by rfl) ⟨1667906, by rfl⟩ : syracuseStep 2223875 = 3335813) B3335813
theorem B11570957 : Blo 1482061 11570957 := bstep (se 3 (by rfl) ⟨2169554, by rfl⟩ : syracuseStep 11570957 = 4339109) B4339109
theorem B2223905 : Blo 1482061 2223905 := bstep (se 2 (by rfl) ⟨833964, by rfl⟩ : syracuseStep 2223905 = 1667929) B1667929
theorem B2223923 : Blo 1482061 2223923 := bstep (se 1 (by rfl) ⟨1667942, by rfl⟩ : syracuseStep 2223923 = 3335885) B3335885
theorem B11267909 : Blo 1482061 11267909 := bstep (se 4 (by rfl) ⟨1056366, by rfl⟩ : syracuseStep 11267909 = 2112733) B2112733
theorem B2223953 : Blo 1482061 2223953 := bstep (se 2 (by rfl) ⟨833982, by rfl⟩ : syracuseStep 2223953 = 1667965) B1667965
theorem B2502481 : Blo 1482061 2502481 := bstep (se 2 (by rfl) ⟨938430, by rfl⟩ : syracuseStep 2502481 = 1876861) B1876861
theorem B2223971 : Blo 1482061 2223971 := bstep (se 1 (by rfl) ⟨1667978, by rfl⟩ : syracuseStep 2223971 = 3335957) B3335957
theorem B2502515 : Blo 1482061 2502515 := bstep (se 1 (by rfl) ⟨1876886, by rfl⟩ : syracuseStep 2502515 = 3753773) B3753773
theorem B2224001 : Blo 1482061 2224001 := bstep (se 2 (by rfl) ⟨834000, by rfl⟩ : syracuseStep 2224001 = 1668001) B1668001
theorem B2224019 : Blo 1482061 2224019 := bstep (se 1 (by rfl) ⟨1668014, by rfl⟩ : syracuseStep 2224019 = 3336029) B3336029
theorem B2224049 : Blo 1482061 2224049 := bstep (se 2 (by rfl) ⟨834018, by rfl⟩ : syracuseStep 2224049 = 1668037) B1668037
theorem B7507889 : Blo 1482061 7507889 := bstep (se 2 (by rfl) ⟨2815458, by rfl⟩ : syracuseStep 7507889 = 5630917) B5630917
theorem B2224067 : Blo 1482061 2224067 := bstep (se 1 (by rfl) ⟨1668050, by rfl⟩ : syracuseStep 2224067 = 3336101) B3336101
theorem B2224097 : Blo 1482061 2224097 := bstep (se 2 (by rfl) ⟨834036, by rfl⟩ : syracuseStep 2224097 = 1668073) B1668073
theorem B4222961 : Blo 1482061 4222961 := bstep (se 2 (by rfl) ⟨1583610, by rfl⟩ : syracuseStep 4222961 = 3167221) B3167221
theorem B3338225 : Blo 1482061 3338225 := bstep (se 2 (by rfl) ⟨1251834, by rfl⟩ : syracuseStep 3338225 = 2503669) B2503669
theorem B2224115 : Blo 1482061 2224115 := bstep (se 1 (by rfl) ⟨1668086, by rfl⟩ : syracuseStep 2224115 = 3336173) B3336173
theorem B2502643 : Blo 1482061 2502643 := bstep (se 1 (by rfl) ⟨1876982, by rfl⟩ : syracuseStep 2502643 = 3753965) B3753965
theorem B3338243 : Blo 1482061 3338243 := bstep (se 1 (by rfl) ⟨2503682, by rfl⟩ : syracuseStep 3338243 = 5007365) B5007365
theorem B2224145 : Blo 1482061 2224145 := bstep (se 2 (by rfl) ⟨834054, by rfl⟩ : syracuseStep 2224145 = 1668109) B1668109
theorem B2224163 : Blo 1482061 2224163 := bstep (se 1 (by rfl) ⟨1668122, by rfl⟩ : syracuseStep 2224163 = 3336245) B3336245
theorem B2224193 : Blo 1482061 2224193 := bstep (se 2 (by rfl) ⟨834072, by rfl⟩ : syracuseStep 2224193 = 1668145) B1668145
theorem B2224211 : Blo 1482061 2224211 := bstep (se 1 (by rfl) ⟨1668158, by rfl⟩ : syracuseStep 2224211 = 3336317) B3336317
theorem B12677219 : Blo 1482061 12677219 := bstep (se 1 (by rfl) ⟨9507914, by rfl⟩ : syracuseStep 12677219 = 19015829) B19015829
theorem B2224241 : Blo 1482061 2224241 := bstep (se 2 (by rfl) ⟨834090, by rfl⟩ : syracuseStep 2224241 = 1668181) B1668181
theorem B2502785 : Blo 1482061 2502785 := bstep (se 2 (by rfl) ⟨938544, by rfl⟩ : syracuseStep 2502785 = 1877089) B1877089
theorem B2224259 : Blo 1482061 2224259 := bstep (se 1 (by rfl) ⟨1668194, by rfl⟩ : syracuseStep 2224259 = 3336389) B3336389
theorem B2224289 : Blo 1482061 2224289 := bstep (se 2 (by rfl) ⟨834108, by rfl⟩ : syracuseStep 2224289 = 1668217) B1668217
theorem B2814115 : Blo 1482061 2814115 := bstep (se 1 (by rfl) ⟨2110586, by rfl⟩ : syracuseStep 2814115 = 4221173) B4221173
theorem B5632163 : Blo 1482061 5632163 := bstep (se 1 (by rfl) ⟨4224122, by rfl⟩ : syracuseStep 5632163 = 8448245) B8448245
theorem B2224307 : Blo 1482061 2224307 := bstep (se 1 (by rfl) ⟨1668230, by rfl⟩ : syracuseStep 2224307 = 3336461) B3336461
theorem B8016077 : Blo 1482061 8016077 := bstep (se 3 (by rfl) ⟨1503014, by rfl⟩ : syracuseStep 8016077 = 3006029) B3006029
theorem B2224337 : Blo 1482061 2224337 := bstep (se 2 (by rfl) ⟨834126, by rfl⟩ : syracuseStep 2224337 = 1668253) B1668253
theorem B4878563 : Blo 1482061 4878563 := bstep (se 1 (by rfl) ⟨3658922, by rfl⟩ : syracuseStep 4878563 = 7317845) B7317845
theorem B2224355 : Blo 1482061 2224355 := bstep (se 1 (by rfl) ⟨1668266, by rfl⟩ : syracuseStep 2224355 = 3336533) B3336533
theorem B12669155 : Blo 1482061 12669155 := bstep (se 1 (by rfl) ⟨9501866, by rfl⟩ : syracuseStep 12669155 = 19003733) B19003733
theorem B9023729 : Blo 1482061 9023729 := bstep (se 2 (by rfl) ⟨3383898, by rfl⟩ : syracuseStep 9023729 = 6767797) B6767797
theorem B2224385 : Blo 1482061 2224385 := bstep (se 2 (by rfl) ⟨834144, by rfl⟩ : syracuseStep 2224385 = 1668289) B1668289
theorem B2502913 : Blo 1482061 2502913 := bstep (se 2 (by rfl) ⟨938592, by rfl⟩ : syracuseStep 2502913 = 1877185) B1877185
theorem B3338513 : Blo 1482061 3338513 := bstep (se 2 (by rfl) ⟨1251942, by rfl⟩ : syracuseStep 3338513 = 2503885) B2503885
theorem B2224403 : Blo 1482061 2224403 := bstep (se 1 (by rfl) ⟨1668302, by rfl⟩ : syracuseStep 2224403 = 3336605) B3336605
theorem B2502947 : Blo 1482061 2502947 := bstep (se 1 (by rfl) ⟨1877210, by rfl⟩ : syracuseStep 2502947 = 3754421) B3754421
theorem B3338531 : Blo 1482061 3338531 := bstep (se 1 (by rfl) ⟨2503898, by rfl⟩ : syracuseStep 3338531 = 5007797) B5007797
theorem B2224433 : Blo 1482061 2224433 := bstep (se 2 (by rfl) ⟨834162, by rfl⟩ : syracuseStep 2224433 = 1668325) B1668325
theorem B2224451 : Blo 1482061 2224451 := bstep (se 1 (by rfl) ⟨1668338, by rfl⟩ : syracuseStep 2224451 = 3336677) B3336677
theorem B5214541 : Blo 1482061 5214541 := bstep (se 3 (by rfl) ⟨977726, by rfl⟩ : syracuseStep 5214541 = 1955453) B1955453
theorem B2224481 : Blo 1482061 2224481 := bstep (se 2 (by rfl) ⟨834180, by rfl⟩ : syracuseStep 2224481 = 1668361) B1668361
theorem B1667443 : Blo 1482061 1667443 := bstep (se 1 (by rfl) ⟨1250582, by rfl⟩ : syracuseStep 1667443 = 2501165) B2501165
theorem B2224499 : Blo 1482061 2224499 := bstep (se 1 (by rfl) ⟨1668374, by rfl⟩ : syracuseStep 2224499 = 3336749) B3336749
theorem B20304269 : Blo 1482061 20304269 := bstep (se 3 (by rfl) ⟨3807050, by rfl⟩ : syracuseStep 20304269 = 7614101) B7614101
theorem B2224529 : Blo 1482061 2224529 := bstep (se 2 (by rfl) ⟨834198, by rfl⟩ : syracuseStep 2224529 = 1668397) B1668397
theorem B2224547 : Blo 1482061 2224547 := bstep (se 1 (by rfl) ⟨1668410, by rfl⟩ : syracuseStep 2224547 = 3336821) B3336821
theorem B2503075 : Blo 1482061 2503075 := bstep (se 1 (by rfl) ⟨1877306, by rfl⟩ : syracuseStep 2503075 = 3754613) B3754613
theorem B2224577 : Blo 1482061 2224577 := bstep (se 2 (by rfl) ⟨834216, by rfl⟩ : syracuseStep 2224577 = 1668433) B1668433
theorem B8556997 : Blo 1482061 8556997 := bstep (se 4 (by rfl) ⟨802218, by rfl⟩ : syracuseStep 8556997 = 1604437) B1604437
theorem B2224595 : Blo 1482061 2224595 := bstep (se 1 (by rfl) ⟨1668446, by rfl⟩ : syracuseStep 2224595 = 3336893) B3336893
theorem B2224625 : Blo 1482061 2224625 := bstep (se 2 (by rfl) ⟨834234, by rfl⟩ : syracuseStep 2224625 = 1668469) B1668469
theorem B11416049 : Blo 1482061 11416049 := bstep (se 2 (by rfl) ⟨4281018, by rfl⟩ : syracuseStep 11416049 = 8562037) B8562037
theorem B1667587 : Blo 1482061 1667587 := bstep (se 1 (by rfl) ⟨1250690, by rfl⟩ : syracuseStep 1667587 = 2501381) B2501381
theorem B2224643 : Blo 1482061 2224643 := bstep (se 1 (by rfl) ⟨1668482, by rfl⟩ : syracuseStep 2224643 = 3336965) B3336965
theorem B2224673 : Blo 1482061 2224673 := bstep (se 2 (by rfl) ⟨834252, by rfl⟩ : syracuseStep 2224673 = 1668505) B1668505
theorem B3166769 : Blo 1482061 3166769 := bstep (se 2 (by rfl) ⟨1187538, by rfl⟩ : syracuseStep 3166769 = 2375077) B2375077
theorem B2503217 : Blo 1482061 2503217 := bstep (se 2 (by rfl) ⟨938706, by rfl⟩ : syracuseStep 2503217 = 1877413) B1877413
theorem B2224691 : Blo 1482061 2224691 := bstep (se 1 (by rfl) ⟨1668518, by rfl⟩ : syracuseStep 2224691 = 3337037) B3337037
theorem B3338801 : Blo 1482061 3338801 := bstep (se 2 (by rfl) ⟨1252050, by rfl⟩ : syracuseStep 3338801 = 2504101) B2504101
theorem B3338819 : Blo 1482061 3338819 := bstep (se 1 (by rfl) ⟨2504114, by rfl⟩ : syracuseStep 3338819 = 5008229) B5008229
theorem B2224721 : Blo 1482061 2224721 := bstep (se 2 (by rfl) ⟨834270, by rfl⟩ : syracuseStep 2224721 = 1668541) B1668541
theorem B7123555 : Blo 1482061 7123555 := bstep (se 1 (by rfl) ⟨5342666, by rfl⟩ : syracuseStep 7123555 = 10685333) B10685333
theorem B2814563 : Blo 1482061 2814563 := bstep (se 1 (by rfl) ⟨2110922, by rfl⟩ : syracuseStep 2814563 = 4221845) B4221845
theorem B2224739 : Blo 1482061 2224739 := bstep (se 1 (by rfl) ⟨1668554, by rfl⟩ : syracuseStep 2224739 = 3337109) B3337109
theorem B2224769 : Blo 1482061 2224769 := bstep (se 2 (by rfl) ⟨834288, by rfl⟩ : syracuseStep 2224769 = 1668577) B1668577
theorem B12030605 : Blo 1482061 12030605 := bstep (se 3 (by rfl) ⟨2255738, by rfl⟩ : syracuseStep 12030605 = 4511477) B4511477
theorem B1667731 : Blo 1482061 1667731 := bstep (se 1 (by rfl) ⟨1250798, by rfl⟩ : syracuseStep 1667731 = 2501597) B2501597
theorem B2224787 : Blo 1482061 2224787 := bstep (se 1 (by rfl) ⟨1668590, by rfl⟩ : syracuseStep 2224787 = 3337181) B3337181
theorem B2224817 : Blo 1482061 2224817 := bstep (se 2 (by rfl) ⟨834306, by rfl⟩ : syracuseStep 2224817 = 1668613) B1668613
theorem B2503345 : Blo 1482061 2503345 := bstep (se 2 (by rfl) ⟨938754, by rfl⟩ : syracuseStep 2503345 = 1877509) B1877509
theorem B3011267 : Blo 1482061 3011267 := bstep (se 1 (by rfl) ⟨2258450, by rfl⟩ : syracuseStep 3011267 = 4516901) B4516901
theorem B2224835 : Blo 1482061 2224835 := bstep (se 1 (by rfl) ⟨1668626, by rfl⟩ : syracuseStep 2224835 = 3337253) B3337253
theorem B2503379 : Blo 1482061 2503379 := bstep (se 1 (by rfl) ⟨1877534, by rfl⟩ : syracuseStep 2503379 = 3755069) B3755069
theorem B2224865 : Blo 1482061 2224865 := bstep (se 2 (by rfl) ⟨834324, by rfl⟩ : syracuseStep 2224865 = 1668649) B1668649
theorem B27063011 : Blo 1482061 27063011 := bstep (se 1 (by rfl) ⟨20297258, by rfl⟩ : syracuseStep 27063011 = 40594517) B40594517
theorem B5001965 : Blo 1482061 5001965 := bstep (se 3 (by rfl) ⟨937868, by rfl⟩ : syracuseStep 5001965 = 1875737) B1875737
theorem B2224883 : Blo 1482061 2224883 := bstep (se 1 (by rfl) ⟨1668662, by rfl⟩ : syracuseStep 2224883 = 3337325) B3337325
theorem B2224913 : Blo 1482061 2224913 := bstep (se 2 (by rfl) ⟨834342, by rfl⟩ : syracuseStep 2224913 = 1668685) B1668685
theorem B5002019 : Blo 1482061 5002019 := bstep (se 1 (by rfl) ⟨3751514, by rfl⟩ : syracuseStep 5002019 = 7503029) B7503029
theorem B1667875 : Blo 1482061 1667875 := bstep (se 1 (by rfl) ⟨1250906, by rfl⟩ : syracuseStep 1667875 = 2501813) B2501813
theorem B2224931 : Blo 1482061 2224931 := bstep (se 1 (by rfl) ⟨1668698, by rfl⟩ : syracuseStep 2224931 = 3337397) B3337397
theorem B2224961 : Blo 1482061 2224961 := bstep (se 2 (by rfl) ⟨834360, by rfl⟩ : syracuseStep 2224961 = 1668721) B1668721
theorem B4281169 : Blo 1482061 4281169 := bstep (se 2 (by rfl) ⟨1605438, by rfl⟩ : syracuseStep 4281169 = 3210877) B3210877
theorem B3339089 : Blo 1482061 3339089 := bstep (se 2 (by rfl) ⟨1252158, by rfl⟩ : syracuseStep 3339089 = 2504317) B2504317
theorem B2224979 : Blo 1482061 2224979 := bstep (se 1 (by rfl) ⟨1668734, by rfl⟩ : syracuseStep 2224979 = 3337469) B3337469
theorem B2503507 : Blo 1482061 2503507 := bstep (se 1 (by rfl) ⟨1877630, by rfl⟩ : syracuseStep 2503507 = 3755261) B3755261
theorem B6337379 : Blo 1482061 6337379 := bstep (se 1 (by rfl) ⟨4753034, by rfl⟩ : syracuseStep 6337379 = 9506069) B9506069
theorem B3339107 : Blo 1482061 3339107 := bstep (se 1 (by rfl) ⟨2504330, by rfl⟩ : syracuseStep 3339107 = 5008661) B5008661
theorem B2225009 : Blo 1482061 2225009 := bstep (se 2 (by rfl) ⟨834378, by rfl⟩ : syracuseStep 2225009 = 1668757) B1668757
theorem B2814851 : Blo 1482061 2814851 := bstep (se 1 (by rfl) ⟨2111138, by rfl⟩ : syracuseStep 2814851 = 4222277) B4222277
theorem B2225027 : Blo 1482061 2225027 := bstep (se 1 (by rfl) ⟨1668770, by rfl⟩ : syracuseStep 2225027 = 3337541) B3337541
theorem B2225057 : Blo 1482061 2225057 := bstep (se 2 (by rfl) ⟨834396, by rfl⟩ : syracuseStep 2225057 = 1668793) B1668793
theorem B4223917 : Blo 1482061 4223917 := bstep (se 3 (by rfl) ⟨791984, by rfl⟩ : syracuseStep 4223917 = 1583969) B1583969
theorem B2110387 : Blo 1482061 2110387 := bstep (se 1 (by rfl) ⟨1582790, by rfl⟩ : syracuseStep 2110387 = 3165581) B3165581
theorem B1668019 : Blo 1482061 1668019 := bstep (se 1 (by rfl) ⟨1251014, by rfl⟩ : syracuseStep 1668019 = 2502029) B2502029
theorem B2225075 : Blo 1482061 2225075 := bstep (se 1 (by rfl) ⟨1668806, by rfl⟩ : syracuseStep 2225075 = 3337613) B3337613
theorem B2225105 : Blo 1482061 2225105 := bstep (se 2 (by rfl) ⟨834414, by rfl⟩ : syracuseStep 2225105 = 1668829) B1668829
theorem B2503649 : Blo 1482061 2503649 := bstep (se 2 (by rfl) ⟨938868, by rfl⟩ : syracuseStep 2503649 = 1877737) B1877737
theorem B2225123 : Blo 1482061 2225123 := bstep (se 1 (by rfl) ⟨1668842, by rfl⟩ : syracuseStep 2225123 = 3337685) B3337685
theorem B2225153 : Blo 1482061 2225153 := bstep (se 2 (by rfl) ⟨834432, by rfl⟩ : syracuseStep 2225153 = 1668865) B1668865
theorem B2225171 : Blo 1482061 2225171 := bstep (se 1 (by rfl) ⟨1668878, by rfl⟩ : syracuseStep 2225171 = 3337757) B3337757
theorem B5002289 : Blo 1482061 5002289 := bstep (se 2 (by rfl) ⟨1875858, by rfl⟩ : syracuseStep 5002289 = 3751717) B3751717
theorem B2225201 : Blo 1482061 2225201 := bstep (se 2 (by rfl) ⟨834450, by rfl⟩ : syracuseStep 2225201 = 1668901) B1668901
theorem B5076017 : Blo 1482061 5076017 := bstep (se 2 (by rfl) ⟨1903506, by rfl⟩ : syracuseStep 5076017 = 3807013) B3807013
theorem B1668163 : Blo 1482061 1668163 := bstep (se 1 (by rfl) ⟨1251122, by rfl⟩ : syracuseStep 1668163 = 2502245) B2502245
theorem B2225219 : Blo 1482061 2225219 := bstep (se 1 (by rfl) ⟨1668914, by rfl⟩ : syracuseStep 2225219 = 3337829) B3337829
theorem B2225249 : Blo 1482061 2225249 := bstep (se 2 (by rfl) ⟨834468, by rfl⟩ : syracuseStep 2225249 = 1668937) B1668937
theorem B2503777 : Blo 1482061 2503777 := bstep (se 2 (by rfl) ⟨938916, by rfl⟩ : syracuseStep 2503777 = 1877833) B1877833
theorem B4813937 : Blo 1482061 4813937 := bstep (se 2 (by rfl) ⟨1805226, by rfl⟩ : syracuseStep 4813937 = 3610453) B3610453
theorem B2225267 : Blo 1482061 2225267 := bstep (se 1 (by rfl) ⟨1668950, by rfl⟩ : syracuseStep 2225267 = 3337901) B3337901
theorem B2503811 : Blo 1482061 2503811 := bstep (se 1 (by rfl) ⟨1877858, by rfl⟩ : syracuseStep 2503811 = 3755717) B3755717
theorem B11416717 : Blo 1482061 11416717 := bstep (se 3 (by rfl) ⟨2140634, by rfl⟩ : syracuseStep 11416717 = 4281269) B4281269
theorem B5633165 : Blo 1482061 5633165 := bstep (se 3 (by rfl) ⟨1056218, by rfl⟩ : syracuseStep 5633165 = 2112437) B2112437
theorem B4224145 : Blo 1482061 4224145 := bstep (se 2 (by rfl) ⟨1584054, by rfl⟩ : syracuseStep 4224145 = 3168109) B3168109
theorem B3806353 : Blo 1482061 3806353 := bstep (se 2 (by rfl) ⟨1427382, by rfl⟩ : syracuseStep 3806353 = 2854765) B2854765
theorem B2225297 : Blo 1482061 2225297 := bstep (se 2 (by rfl) ⟨834486, by rfl⟩ : syracuseStep 2225297 = 1668973) B1668973
theorem B2225315 : Blo 1482061 2225315 := bstep (se 1 (by rfl) ⟨1668986, by rfl⟩ : syracuseStep 2225315 = 3337973) B3337973
theorem B2225345 : Blo 1482061 2225345 := bstep (se 2 (by rfl) ⟨834504, by rfl⟩ : syracuseStep 2225345 = 1669009) B1669009
theorem B1668307 : Blo 1482061 1668307 := bstep (se 1 (by rfl) ⟨1251230, by rfl⟩ : syracuseStep 1668307 = 2502461) B2502461
theorem B2225363 : Blo 1482061 2225363 := bstep (se 1 (by rfl) ⟨1669022, by rfl⟩ : syracuseStep 2225363 = 3338045) B3338045
theorem B2225393 : Blo 1482061 2225393 := bstep (se 2 (by rfl) ⟨834522, by rfl⟩ : syracuseStep 2225393 = 1669045) B1669045
theorem B2225411 : Blo 1482061 2225411 := bstep (se 1 (by rfl) ⟨1669058, by rfl⟩ : syracuseStep 2225411 = 3338117) B3338117
theorem B2503939 : Blo 1482061 2503939 := bstep (se 1 (by rfl) ⟨1877954, by rfl⟩ : syracuseStep 2503939 = 3755909) B3755909
theorem B2225441 : Blo 1482061 2225441 := bstep (se 2 (by rfl) ⟨834540, by rfl⟩ : syracuseStep 2225441 = 1669081) B1669081
theorem B4224305 : Blo 1482061 4224305 := bstep (se 2 (by rfl) ⟨1584114, by rfl⟩ : syracuseStep 4224305 = 3168229) B3168229
theorem B2225459 : Blo 1482061 2225459 := bstep (se 1 (by rfl) ⟨1669094, by rfl⟩ : syracuseStep 2225459 = 3338189) B3338189
theorem B2225489 : Blo 1482061 2225489 := bstep (se 2 (by rfl) ⟨834558, by rfl⟩ : syracuseStep 2225489 = 1669117) B1669117
theorem B1668451 : Blo 1482061 1668451 := bstep (se 1 (by rfl) ⟨1251338, by rfl⟩ : syracuseStep 1668451 = 2502677) B2502677
theorem B7509347 : Blo 1482061 7509347 := bstep (se 1 (by rfl) ⟨5632010, by rfl⟩ : syracuseStep 7509347 = 11264021) B11264021
theorem B2225507 : Blo 1482061 2225507 := bstep (se 1 (by rfl) ⟨1669130, by rfl⟩ : syracuseStep 2225507 = 3338261) B3338261
theorem B2225537 : Blo 1482061 2225537 := bstep (se 2 (by rfl) ⟨834576, by rfl⟩ : syracuseStep 2225537 = 1669153) B1669153
theorem B2110865 : Blo 1482061 2110865 := bstep (se 2 (by rfl) ⟨791574, by rfl⟩ : syracuseStep 2110865 = 1583149) B1583149
theorem B2225555 : Blo 1482061 2225555 := bstep (se 1 (by rfl) ⟨1669166, by rfl⟩ : syracuseStep 2225555 = 3338333) B3338333
theorem B2504081 : Blo 1482061 2504081 := bstep (se 2 (by rfl) ⟨939030, by rfl⟩ : syracuseStep 2504081 = 1878061) B1878061
theorem B4224419 : Blo 1482061 4224419 := bstep (se 1 (by rfl) ⟨3168314, by rfl⟩ : syracuseStep 4224419 = 6336629) B6336629
theorem B2225585 : Blo 1482061 2225585 := bstep (se 2 (by rfl) ⟨834594, by rfl⟩ : syracuseStep 2225585 = 1669189) B1669189
theorem B2225603 : Blo 1482061 2225603 := bstep (se 1 (by rfl) ⟨1669202, by rfl⟩ : syracuseStep 2225603 = 3338405) B3338405
theorem B2225633 : Blo 1482061 2225633 := bstep (se 2 (by rfl) ⟨834612, by rfl⟩ : syracuseStep 2225633 = 1669225) B1669225
theorem B1668595 : Blo 1482061 1668595 := bstep (se 1 (by rfl) ⟨1251446, by rfl⟩ : syracuseStep 1668595 = 2502893) B2502893
theorem B2225651 : Blo 1482061 2225651 := bstep (se 1 (by rfl) ⟨1669238, by rfl⟩ : syracuseStep 2225651 = 3338477) B3338477
theorem B2110979 : Blo 1482061 2110979 := bstep (se 1 (by rfl) ⟨1583234, by rfl⟩ : syracuseStep 2110979 = 3166469) B3166469
theorem B15218189 : Blo 1482061 15218189 := bstep (se 3 (by rfl) ⟨2853410, by rfl⟩ : syracuseStep 15218189 = 5706821) B5706821
theorem B2225681 : Blo 1482061 2225681 := bstep (se 2 (by rfl) ⟨834630, by rfl⟩ : syracuseStep 2225681 = 1669261) B1669261
theorem B2504209 : Blo 1482061 2504209 := bstep (se 2 (by rfl) ⟨939078, by rfl⟩ : syracuseStep 2504209 = 1878157) B1878157
theorem B2225699 : Blo 1482061 2225699 := bstep (se 1 (by rfl) ⟨1669274, by rfl⟩ : syracuseStep 2225699 = 3338549) B3338549
theorem B4511281 : Blo 1482061 4511281 := bstep (se 2 (by rfl) ⟨1691730, by rfl⟩ : syracuseStep 4511281 = 3383461) B3383461
theorem B2504243 : Blo 1482061 2504243 := bstep (se 1 (by rfl) ⟨1878182, by rfl⟩ : syracuseStep 2504243 = 3756365) B3756365
theorem B2225729 : Blo 1482061 2225729 := bstep (se 2 (by rfl) ⟨834648, by rfl⟩ : syracuseStep 2225729 = 1669297) B1669297
theorem B5002829 : Blo 1482061 5002829 := bstep (se 3 (by rfl) ⟨938030, by rfl⟩ : syracuseStep 5002829 = 1876061) B1876061
theorem B8451661 : Blo 1482061 8451661 := bstep (se 3 (by rfl) ⟨1584686, by rfl⟩ : syracuseStep 8451661 = 3169373) B3169373
theorem B2111059 : Blo 1482061 2111059 := bstep (se 1 (by rfl) ⟨1583294, by rfl⟩ : syracuseStep 2111059 = 3166589) B3166589
theorem B2225747 : Blo 1482061 2225747 := bstep (se 1 (by rfl) ⟨1669310, by rfl⟩ : syracuseStep 2225747 = 3338621) B3338621
theorem B2225777 : Blo 1482061 2225777 := bstep (se 2 (by rfl) ⟨834666, by rfl⟩ : syracuseStep 2225777 = 1669333) B1669333
theorem B5002883 : Blo 1482061 5002883 := bstep (se 1 (by rfl) ⟨3752162, by rfl⟩ : syracuseStep 5002883 = 7504325) B7504325
theorem B1668739 : Blo 1482061 1668739 := bstep (se 1 (by rfl) ⟨1251554, by rfl⟩ : syracuseStep 1668739 = 2503109) B2503109
theorem B2225795 : Blo 1482061 2225795 := bstep (se 1 (by rfl) ⟨1669346, by rfl⟩ : syracuseStep 2225795 = 3338693) B3338693
theorem B2004625 : Blo 1482061 2004625 := bstep (se 2 (by rfl) ⟨751734, by rfl⟩ : syracuseStep 2004625 = 1503469) B1503469
theorem B2225825 : Blo 1482061 2225825 := bstep (se 2 (by rfl) ⟨834684, by rfl⟩ : syracuseStep 2225825 = 1669369) B1669369
theorem B9508529 : Blo 1482061 9508529 := bstep (se 2 (by rfl) ⟨3565698, by rfl⟩ : syracuseStep 9508529 = 7131397) B7131397
theorem B2225843 : Blo 1482061 2225843 := bstep (se 1 (by rfl) ⟨1669382, by rfl⟩ : syracuseStep 2225843 = 3338765) B3338765
theorem B3561155 : Blo 1482061 3561155 := bstep (se 1 (by rfl) ⟨2670866, by rfl⟩ : syracuseStep 3561155 = 5341733) B5341733
theorem B2225873 : Blo 1482061 2225873 := bstep (se 2 (by rfl) ⟨834702, by rfl⟩ : syracuseStep 2225873 = 1669405) B1669405
theorem B2225891 : Blo 1482061 2225891 := bstep (se 1 (by rfl) ⟨1669418, by rfl⟩ : syracuseStep 2225891 = 3338837) B3338837
theorem B2225921 : Blo 1482061 2225921 := bstep (se 2 (by rfl) ⟨834720, by rfl⟩ : syracuseStep 2225921 = 1669441) B1669441
theorem B1668883 : Blo 1482061 1668883 := bstep (se 1 (by rfl) ⟨1251662, by rfl⟩ : syracuseStep 1668883 = 2503325) B2503325
theorem B2225939 : Blo 1482061 2225939 := bstep (se 1 (by rfl) ⟨1669454, by rfl⟩ : syracuseStep 2225939 = 3338909) B3338909
theorem B2815793 : Blo 1482061 2815793 := bstep (se 2 (by rfl) ⟨1055922, by rfl⟩ : syracuseStep 2815793 = 2111845) B2111845
theorem B2225969 : Blo 1482061 2225969 := bstep (se 2 (by rfl) ⟨834738, by rfl⟩ : syracuseStep 2225969 = 1669477) B1669477
theorem B3168067 : Blo 1482061 3168067 := bstep (se 1 (by rfl) ⟨2376050, by rfl⟩ : syracuseStep 3168067 = 4752101) B4752101
theorem B2225987 : Blo 1482061 2225987 := bstep (se 1 (by rfl) ⟨1669490, by rfl⟩ : syracuseStep 2225987 = 3338981) B3338981
theorem B2226017 : Blo 1482061 2226017 := bstep (se 2 (by rfl) ⟨834756, by rfl⟩ : syracuseStep 2226017 = 1669513) B1669513
theorem B2226035 : Blo 1482061 2226035 := bstep (se 1 (by rfl) ⟨1669526, by rfl⟩ : syracuseStep 2226035 = 3339053) B3339053
theorem B5003153 : Blo 1482061 5003153 := bstep (se 2 (by rfl) ⟨1876182, by rfl⟩ : syracuseStep 5003153 = 3752365) B3752365
theorem B2226065 : Blo 1482061 2226065 := bstep (se 2 (by rfl) ⟨834774, by rfl⟩ : syracuseStep 2226065 = 1669549) B1669549
theorem B1669027 : Blo 1482061 1669027 := bstep (se 1 (by rfl) ⟨1251770, by rfl⟩ : syracuseStep 1669027 = 2503541) B2503541
theorem B2226083 : Blo 1482061 2226083 := bstep (se 1 (by rfl) ⟨1669562, by rfl⟩ : syracuseStep 2226083 = 3339125) B3339125
theorem B4749293 : Blo 1482061 4749293 := bstep (se 3 (by rfl) ⟨890492, by rfl⟩ : syracuseStep 4749293 = 1780985) B1780985
theorem B14096369 : Blo 1482061 14096369 := bstep (se 2 (by rfl) ⟨5286138, by rfl⟩ : syracuseStep 14096369 = 10572277) B10572277
theorem B1669171 : Blo 1482061 1669171 := bstep (se 1 (by rfl) ⟨1251878, by rfl⟩ : syracuseStep 1669171 = 2503757) B2503757
theorem B2111617 : Blo 1482061 2111617 := bstep (se 2 (by rfl) ⟨791856, by rfl⟩ : syracuseStep 2111617 = 1583713) B1583713
theorem B7510157 : Blo 1482061 7510157 := bstep (se 3 (by rfl) ⟨1408154, by rfl⟩ : syracuseStep 7510157 = 2816309) B2816309
theorem B1669315 : Blo 1482061 1669315 := bstep (se 1 (by rfl) ⟨1251986, by rfl⟩ : syracuseStep 1669315 = 2503973) B2503973
theorem B1669459 : Blo 1482061 1669459 := bstep (se 1 (by rfl) ⟨1252094, by rfl⟩ : syracuseStep 1669459 = 2504189) B2504189
theorem B2169185 : Blo 1482061 2169185 := bstep (se 2 (by rfl) ⟨813444, by rfl⟩ : syracuseStep 2169185 = 1626889) B1626889
theorem B4225421 : Blo 1482061 4225421 := bstep (se 3 (by rfl) ⟨792266, by rfl⟩ : syracuseStep 4225421 = 1584533) B1584533
theorem B5003693 : Blo 1482061 5003693 := bstep (se 3 (by rfl) ⟨938192, by rfl⟩ : syracuseStep 5003693 = 1876385) B1876385
theorem B5282225 : Blo 1482061 5282225 := bstep (se 2 (by rfl) ⟨1980834, by rfl⟩ : syracuseStep 5282225 = 3961669) B3961669
theorem B5708237 : Blo 1482061 5708237 := bstep (se 3 (by rfl) ⟨1070294, by rfl⟩ : syracuseStep 5708237 = 2140589) B2140589
theorem B21371363 : Blo 1482061 21371363 := bstep (se 1 (by rfl) ⟨16028522, by rfl⟩ : syracuseStep 21371363 = 32057045) B32057045
theorem B5003747 : Blo 1482061 5003747 := bstep (se 1 (by rfl) ⟨3752810, by rfl⟩ : syracuseStep 5003747 = 7505621) B7505621
theorem B3562001 : Blo 1482061 3562001 := bstep (se 2 (by rfl) ⟨1335750, by rfl⟩ : syracuseStep 3562001 = 2671501) B2671501
theorem B5347889 : Blo 1482061 5347889 := bstep (se 2 (by rfl) ⟨2005458, by rfl⟩ : syracuseStep 5347889 = 4010917) B4010917
theorem B2374211 : Blo 1482061 2374211 := bstep (se 1 (by rfl) ⟨1780658, by rfl⟩ : syracuseStep 2374211 = 3561317) B3561317
theorem B4225603 : Blo 1482061 4225603 := bstep (se 1 (by rfl) ⟨3169202, by rfl⟩ : syracuseStep 4225603 = 6338405) B6338405
theorem B11262563 : Blo 1482061 11262563 := bstep (se 1 (by rfl) ⟨8446922, by rfl⟩ : syracuseStep 11262563 = 16893845) B16893845
theorem B13523597 : Blo 1482061 13523597 := bstep (se 3 (by rfl) ⟨2535674, by rfl⟩ : syracuseStep 13523597 = 5071349) B5071349
theorem B2816689 : Blo 1482061 2816689 := bstep (se 2 (by rfl) ⟨1056258, by rfl⟩ : syracuseStep 2816689 = 2112517) B2112517
theorem B4225763 : Blo 1482061 4225763 := bstep (se 1 (by rfl) ⟨3169322, by rfl⟩ : syracuseStep 4225763 = 6338645) B6338645
theorem B5004017 : Blo 1482061 5004017 := bstep (se 2 (by rfl) ⟨1876506, by rfl⟩ : syracuseStep 5004017 = 3753013) B3753013
theorem B2112323 : Blo 1482061 2112323 := bstep (se 1 (by rfl) ⟨1584242, by rfl⟩ : syracuseStep 2112323 = 3168485) B3168485
theorem B2816849 : Blo 1482061 2816849 := bstep (se 2 (by rfl) ⟨1056318, by rfl⟩ : syracuseStep 2816849 = 2112637) B2112637
theorem B2538467 : Blo 1482061 2538467 := bstep (se 1 (by rfl) ⟨1903850, by rfl⟩ : syracuseStep 2538467 = 3807701) B3807701
theorem B4062221 : Blo 1482061 4062221 := bstep (se 3 (by rfl) ⟨761666, by rfl⟩ : syracuseStep 4062221 = 1523333) B1523333
theorem B3169297 : Blo 1482061 3169297 := bstep (se 2 (by rfl) ⟨1188486, by rfl⟩ : syracuseStep 3169297 = 2376973) B2376973
theorem B18037829 : Blo 1482061 18037829 := bstep (se 4 (by rfl) ⟨1691046, by rfl⟩ : syracuseStep 18037829 = 3382093) B3382093
theorem B2817251 : Blo 1482061 2817251 := bstep (se 1 (by rfl) ⟨2112938, by rfl⟩ : syracuseStep 2817251 = 4225877) B4225877
theorem B5004557 : Blo 1482061 5004557 := bstep (se 3 (by rfl) ⟨938354, by rfl⟩ : syracuseStep 5004557 = 1876709) B1876709
theorem B5004611 : Blo 1482061 5004611 := bstep (se 1 (by rfl) ⟨3753458, by rfl⟩ : syracuseStep 5004611 = 7506917) B7506917
theorem B1482067 : Blo 1482061 1482067 := bstep (se 1 (by rfl) ⟨1111550, by rfl⟩ : syracuseStep 1482067 = 2223101) B2223101
theorem B1482083 : Blo 1482061 1482083 := bstep (se 1 (by rfl) ⟨1111562, by rfl⟩ : syracuseStep 1482083 = 2223125) B2223125
theorem B1482099 : Blo 1482061 1482099 := bstep (se 1 (by rfl) ⟨1111574, by rfl⟩ : syracuseStep 1482099 = 2223149) B2223149
theorem B1482115 : Blo 1482061 1482115 := bstep (se 1 (by rfl) ⟨1111586, by rfl⟩ : syracuseStep 1482115 = 2223173) B2223173
theorem B2375057 : Blo 1482061 2375057 := bstep (se 2 (by rfl) ⟨890646, by rfl⟩ : syracuseStep 2375057 = 1781293) B1781293
theorem B1482131 : Blo 1482061 1482131 := bstep (se 1 (by rfl) ⟨1111598, by rfl⟩ : syracuseStep 1482131 = 2223197) B2223197
theorem B1482147 : Blo 1482061 1482147 := bstep (se 1 (by rfl) ⟨1111610, by rfl⟩ : syracuseStep 1482147 = 2223221) B2223221
theorem B6602161 : Blo 1482061 6602161 := bstep (se 2 (by rfl) ⟨2475810, by rfl⟩ : syracuseStep 6602161 = 4951621) B4951621
theorem B1482163 : Blo 1482061 1482163 := bstep (se 1 (by rfl) ⟨1111622, by rfl⟩ : syracuseStep 1482163 = 2223245) B2223245
theorem B2112961 : Blo 1482061 2112961 := bstep (se 2 (by rfl) ⟨792360, by rfl⟩ : syracuseStep 2112961 = 1584721) B1584721
theorem B1482179 : Blo 1482061 1482179 := bstep (se 1 (by rfl) ⟨1111634, by rfl⟩ : syracuseStep 1482179 = 2223269) B2223269
theorem B1482195 : Blo 1482061 1482195 := bstep (se 1 (by rfl) ⟨1111646, by rfl⟩ : syracuseStep 1482195 = 2223293) B2223293
theorem B1482211 : Blo 1482061 1482211 := bstep (se 1 (by rfl) ⟨1111658, by rfl⟩ : syracuseStep 1482211 = 2223317) B2223317
theorem B1482227 : Blo 1482061 1482227 := bstep (se 1 (by rfl) ⟨1111670, by rfl⟩ : syracuseStep 1482227 = 2223341) B2223341
theorem B1482243 : Blo 1482061 1482243 := bstep (se 1 (by rfl) ⟨1111682, by rfl⟩ : syracuseStep 1482243 = 2223365) B2223365
theorem B2375185 : Blo 1482061 2375185 := bstep (se 2 (by rfl) ⟨890694, by rfl⟩ : syracuseStep 2375185 = 1781389) B1781389
theorem B1482259 : Blo 1482061 1482259 := bstep (se 1 (by rfl) ⟨1111694, by rfl⟩ : syracuseStep 1482259 = 2223389) B2223389
theorem B1482275 : Blo 1482061 1482275 := bstep (se 1 (by rfl) ⟨1111706, by rfl⟩ : syracuseStep 1482275 = 2223413) B2223413
theorem B4750883 : Blo 1482061 4750883 := bstep (se 1 (by rfl) ⟨3563162, by rfl⟩ : syracuseStep 4750883 = 7126325) B7126325
theorem B1482291 : Blo 1482061 1482291 := bstep (se 1 (by rfl) ⟨1111718, by rfl⟩ : syracuseStep 1482291 = 2223437) B2223437
theorem B1482307 : Blo 1482061 1482307 := bstep (se 1 (by rfl) ⟨1111730, by rfl⟩ : syracuseStep 1482307 = 2223461) B2223461
theorem B3751505 : Blo 1482061 3751505 := bstep (se 2 (by rfl) ⟨1406814, by rfl⟩ : syracuseStep 3751505 = 2813629) B2813629
theorem B1482323 : Blo 1482061 1482323 := bstep (se 1 (by rfl) ⟨1111742, by rfl⟩ : syracuseStep 1482323 = 2223485) B2223485
theorem B2375249 : Blo 1482061 2375249 := bstep (se 2 (by rfl) ⟨890718, by rfl⟩ : syracuseStep 2375249 = 1781437) B1781437
theorem B5004881 : Blo 1482061 5004881 := bstep (se 2 (by rfl) ⟨1876830, by rfl⟩ : syracuseStep 5004881 = 3753661) B3753661
theorem B1482339 : Blo 1482061 1482339 := bstep (se 1 (by rfl) ⟨1111754, by rfl⟩ : syracuseStep 1482339 = 2223509) B2223509
theorem B1482355 : Blo 1482061 1482355 := bstep (se 1 (by rfl) ⟨1111766, by rfl⟩ : syracuseStep 1482355 = 2223533) B2223533
theorem B3751555 : Blo 1482061 3751555 := bstep (se 1 (by rfl) ⟨2813666, by rfl⟩ : syracuseStep 3751555 = 5627333) B5627333
theorem B1482371 : Blo 1482061 1482371 := bstep (se 1 (by rfl) ⟨1111778, by rfl⟩ : syracuseStep 1482371 = 2223557) B2223557
theorem B1482387 : Blo 1482061 1482387 := bstep (se 1 (by rfl) ⟨1111790, by rfl⟩ : syracuseStep 1482387 = 2223581) B2223581
theorem B1482403 : Blo 1482061 1482403 := bstep (se 1 (by rfl) ⟨1111802, by rfl⟩ : syracuseStep 1482403 = 2223605) B2223605
theorem B1482419 : Blo 1482061 1482419 := bstep (se 1 (by rfl) ⟨1111814, by rfl⟩ : syracuseStep 1482419 = 2223629) B2223629
theorem B1482435 : Blo 1482061 1482435 := bstep (se 1 (by rfl) ⟨1111826, by rfl⟩ : syracuseStep 1482435 = 2223653) B2223653
theorem B1482451 : Blo 1482061 1482451 := bstep (se 1 (by rfl) ⟨1111838, by rfl⟩ : syracuseStep 1482451 = 2223677) B2223677
theorem B1482467 : Blo 1482061 1482467 := bstep (se 1 (by rfl) ⟨1111850, by rfl⟩ : syracuseStep 1482467 = 2223701) B2223701
theorem B4751075 : Blo 1482061 4751075 := bstep (se 1 (by rfl) ⟨3563306, by rfl⟩ : syracuseStep 4751075 = 7126613) B7126613
theorem B1482483 : Blo 1482061 1482483 := bstep (se 1 (by rfl) ⟨1111862, by rfl⟩ : syracuseStep 1482483 = 2223725) B2223725
theorem B1482499 : Blo 1482061 1482499 := bstep (se 1 (by rfl) ⟨1111874, by rfl⟩ : syracuseStep 1482499 = 2223749) B2223749
theorem B3751697 : Blo 1482061 3751697 := bstep (se 2 (by rfl) ⟨1406886, by rfl⟩ : syracuseStep 3751697 = 2813773) B2813773
theorem B1482515 : Blo 1482061 1482515 := bstep (se 1 (by rfl) ⟨1111886, by rfl⟩ : syracuseStep 1482515 = 2223773) B2223773
theorem B1482531 : Blo 1482061 1482531 := bstep (se 1 (by rfl) ⟨1111898, by rfl⟩ : syracuseStep 1482531 = 2223797) B2223797
theorem B1482547 : Blo 1482061 1482547 := bstep (se 1 (by rfl) ⟨1111910, by rfl⟩ : syracuseStep 1482547 = 2223821) B2223821
theorem B1482563 : Blo 1482061 1482563 := bstep (se 1 (by rfl) ⟨1111922, by rfl⟩ : syracuseStep 1482563 = 2223845) B2223845
theorem B1482579 : Blo 1482061 1482579 := bstep (se 1 (by rfl) ⟨1111934, by rfl⟩ : syracuseStep 1482579 = 2223869) B2223869
theorem B1482595 : Blo 1482061 1482595 := bstep (se 1 (by rfl) ⟨1111946, by rfl⟩ : syracuseStep 1482595 = 2223893) B2223893
theorem B10149731 : Blo 1482061 10149731 := bstep (se 1 (by rfl) ⟨7612298, by rfl⟩ : syracuseStep 10149731 = 15224597) B15224597
theorem B1482611 : Blo 1482061 1482611 := bstep (se 1 (by rfl) ⟨1111958, by rfl⟩ : syracuseStep 1482611 = 2223917) B2223917
theorem B1482627 : Blo 1482061 1482627 := bstep (se 1 (by rfl) ⟨1111970, by rfl⟩ : syracuseStep 1482627 = 2223941) B2223941
theorem B8445829 : Blo 1482061 8445829 := bstep (se 4 (by rfl) ⟨791796, by rfl⟩ : syracuseStep 8445829 = 1583593) B1583593
theorem B5627789 : Blo 1482061 5627789 := bstep (se 3 (by rfl) ⟨1055210, by rfl⟩ : syracuseStep 5627789 = 2110421) B2110421
theorem B25681805 : Blo 1482061 25681805 := bstep (se 3 (by rfl) ⟨4815338, by rfl⟩ : syracuseStep 25681805 = 9630677) B9630677
theorem B1482643 : Blo 1482061 1482643 := bstep (se 1 (by rfl) ⟨1111982, by rfl⟩ : syracuseStep 1482643 = 2223965) B2223965
theorem B1482659 : Blo 1482061 1482659 := bstep (se 1 (by rfl) ⟨1111994, by rfl⟩ : syracuseStep 1482659 = 2223989) B2223989
theorem B1482675 : Blo 1482061 1482675 := bstep (se 1 (by rfl) ⟨1112006, by rfl⟩ : syracuseStep 1482675 = 2224013) B2224013
theorem B1482691 : Blo 1482061 1482691 := bstep (se 1 (by rfl) ⟨1112018, by rfl⟩ : syracuseStep 1482691 = 2224037) B2224037
theorem B1482707 : Blo 1482061 1482707 := bstep (se 1 (by rfl) ⟨1112030, by rfl⟩ : syracuseStep 1482707 = 2224061) B2224061
theorem B2891747 : Blo 1482061 2891747 := bstep (se 1 (by rfl) ⟨2168810, by rfl⟩ : syracuseStep 2891747 = 4337621) B4337621
theorem B1482723 : Blo 1482061 1482723 := bstep (se 1 (by rfl) ⟨1112042, by rfl⟩ : syracuseStep 1482723 = 2224085) B2224085
theorem B1875955 : Blo 1482061 1875955 := bstep (se 1 (by rfl) ⟨1406966, by rfl⟩ : syracuseStep 1875955 = 2813933) B2813933
theorem B1482739 : Blo 1482061 1482739 := bstep (se 1 (by rfl) ⟨1112054, by rfl⟩ : syracuseStep 1482739 = 2224109) B2224109
theorem B1482763 : Blo 1482061 1482763 := bstep (se 1 (by rfl) ⟨1112072, by rfl⟩ : syracuseStep 1482763 = 2224145) B2224145
theorem B1482775 : Blo 1482061 1482775 := bstep (se 1 (by rfl) ⟨1112081, by rfl⟩ : syracuseStep 1482775 = 2224163) B2224163
theorem B21659683 : Blo 1482061 21659683 := bstep (se 1 (by rfl) ⟨16244762, by rfl⟩ : syracuseStep 21659683 = 32489525) B32489525
theorem B1482795 : Blo 1482061 1482795 := bstep (se 1 (by rfl) ⟨1112096, by rfl⟩ : syracuseStep 1482795 = 2224193) B2224193
theorem B1482807 : Blo 1482061 1482807 := bstep (se 1 (by rfl) ⟨1112105, by rfl⟩ : syracuseStep 1482807 = 2224211) B2224211
theorem B1482827 : Blo 1482061 1482827 := bstep (se 1 (by rfl) ⟨1112120, by rfl⟩ : syracuseStep 1482827 = 2224241) B2224241
theorem B13533259 : Blo 1482061 13533259 := bstep (se 1 (by rfl) ⟨10149944, by rfl⟩ : syracuseStep 13533259 = 20299889) B20299889
theorem B1482839 : Blo 1482061 1482839 := bstep (se 1 (by rfl) ⟨1112129, by rfl⟩ : syracuseStep 1482839 = 2224259) B2224259
theorem B1482859 : Blo 1482061 1482859 := bstep (se 1 (by rfl) ⟨1112144, by rfl⟩ : syracuseStep 1482859 = 2224289) B2224289
theorem B1482871 : Blo 1482061 1482871 := bstep (se 1 (by rfl) ⟨1112153, by rfl⟩ : syracuseStep 1482871 = 2224307) B2224307
theorem B1482891 : Blo 1482061 1482891 := bstep (se 1 (by rfl) ⟨1112168, by rfl⟩ : syracuseStep 1482891 = 2224337) B2224337
theorem B1482903 : Blo 1482061 1482903 := bstep (se 1 (by rfl) ⟨1112177, by rfl⟩ : syracuseStep 1482903 = 2224355) B2224355
theorem B8446103 : Blo 1482061 8446103 := bstep (se 1 (by rfl) ⟨6334577, by rfl⟩ : syracuseStep 8446103 = 12669155) B12669155
theorem B1482923 : Blo 1482061 1482923 := bstep (se 1 (by rfl) ⟨1112192, by rfl⟩ : syracuseStep 1482923 = 2224385) B2224385
theorem B1482935 : Blo 1482061 1482935 := bstep (se 1 (by rfl) ⟨1112201, by rfl⟩ : syracuseStep 1482935 = 2224403) B2224403
theorem B1482955 : Blo 1482061 1482955 := bstep (se 1 (by rfl) ⟨1112216, by rfl⟩ : syracuseStep 1482955 = 2224433) B2224433
theorem B1482967 : Blo 1482061 1482967 := bstep (se 1 (by rfl) ⟨1112225, by rfl⟩ : syracuseStep 1482967 = 2224451) B2224451
theorem B3752153 : Blo 1482061 3752153 := bstep (se 2 (by rfl) ⟨1407057, by rfl⟩ : syracuseStep 3752153 = 2814115) B2814115
theorem B5005529 : Blo 1482061 5005529 := bstep (se 2 (by rfl) ⟨1877073, by rfl⟩ : syracuseStep 5005529 = 3754147) B3754147
theorem B1482987 : Blo 1482061 1482987 := bstep (se 1 (by rfl) ⟨1112240, by rfl⟩ : syracuseStep 1482987 = 2224481) B2224481
theorem B1482999 : Blo 1482061 1482999 := bstep (se 1 (by rfl) ⟨1112249, by rfl⟩ : syracuseStep 1482999 = 2224499) B2224499
theorem B1483019 : Blo 1482061 1483019 := bstep (se 1 (by rfl) ⟨1112264, by rfl⟩ : syracuseStep 1483019 = 2224529) B2224529
theorem B1483031 : Blo 1482061 1483031 := bstep (se 1 (by rfl) ⟨1112273, by rfl⟩ : syracuseStep 1483031 = 2224547) B2224547
theorem B1483051 : Blo 1482061 1483051 := bstep (se 1 (by rfl) ⟨1112288, by rfl⟩ : syracuseStep 1483051 = 2224577) B2224577
theorem B1483063 : Blo 1482061 1483063 := bstep (se 1 (by rfl) ⟨1112297, by rfl⟩ : syracuseStep 1483063 = 2224595) B2224595
theorem B1483083 : Blo 1482061 1483083 := bstep (se 1 (by rfl) ⟨1112312, by rfl⟩ : syracuseStep 1483083 = 2224625) B2224625
theorem B7610699 : Blo 1482061 7610699 := bstep (se 1 (by rfl) ⟨5708024, by rfl⟩ : syracuseStep 7610699 = 11416049) B11416049
theorem B1483095 : Blo 1482061 1483095 := bstep (se 1 (by rfl) ⟨1112321, by rfl⟩ : syracuseStep 1483095 = 2224643) B2224643
theorem B1483115 : Blo 1482061 1483115 := bstep (se 1 (by rfl) ⟨1112336, by rfl⟩ : syracuseStep 1483115 = 2224673) B2224673
theorem B1483127 : Blo 1482061 1483127 := bstep (se 1 (by rfl) ⟨1112345, by rfl⟩ : syracuseStep 1483127 = 2224691) B2224691
theorem B1483147 : Blo 1482061 1483147 := bstep (se 1 (by rfl) ⟨1112360, by rfl⟩ : syracuseStep 1483147 = 2224721) B2224721
theorem B5628305 : Blo 1482061 5628305 := bstep (se 2 (by rfl) ⟨2110614, by rfl⟩ : syracuseStep 5628305 = 4221229) B4221229
theorem B1876375 : Blo 1482061 1876375 := bstep (se 1 (by rfl) ⟨1407281, by rfl⟩ : syracuseStep 1876375 = 2814563) B2814563
theorem B1483159 : Blo 1482061 1483159 := bstep (se 1 (by rfl) ⟨1112369, by rfl⟩ : syracuseStep 1483159 = 2224739) B2224739
theorem B1483179 : Blo 1482061 1483179 := bstep (se 1 (by rfl) ⟨1112384, by rfl⟩ : syracuseStep 1483179 = 2224769) B2224769
theorem B8020403 : Blo 1482061 8020403 := bstep (se 1 (by rfl) ⟨6015302, by rfl⟩ : syracuseStep 8020403 = 12030605) B12030605
theorem B1483191 : Blo 1482061 1483191 := bstep (se 1 (by rfl) ⟨1112393, by rfl⟩ : syracuseStep 1483191 = 2224787) B2224787
theorem B1483211 : Blo 1482061 1483211 := bstep (se 1 (by rfl) ⟨1112408, by rfl⟩ : syracuseStep 1483211 = 2224817) B2224817
theorem B1483223 : Blo 1482061 1483223 := bstep (se 1 (by rfl) ⟨1112417, by rfl⟩ : syracuseStep 1483223 = 2224835) B2224835
theorem B1483243 : Blo 1482061 1483243 := bstep (se 1 (by rfl) ⟨1112432, by rfl⟩ : syracuseStep 1483243 = 2224865) B2224865
theorem B3334643 : Blo 1482061 3334643 := bstep (se 1 (by rfl) ⟨2500982, by rfl⟩ : syracuseStep 3334643 = 5001965) B5001965
theorem B1483255 : Blo 1482061 1483255 := bstep (se 1 (by rfl) ⟨1112441, by rfl⟩ : syracuseStep 1483255 = 2224883) B2224883
theorem B1483275 : Blo 1482061 1483275 := bstep (se 1 (by rfl) ⟨1112456, by rfl⟩ : syracuseStep 1483275 = 2224913) B2224913
theorem B3334679 : Blo 1482061 3334679 := bstep (se 1 (by rfl) ⟨2501009, by rfl⟩ : syracuseStep 3334679 = 5002019) B5002019
theorem B1483287 : Blo 1482061 1483287 := bstep (se 1 (by rfl) ⟨1112465, by rfl⟩ : syracuseStep 1483287 = 2224931) B2224931
theorem B1483307 : Blo 1482061 1483307 := bstep (se 1 (by rfl) ⟨1112480, by rfl⟩ : syracuseStep 1483307 = 2224961) B2224961
theorem B1483319 : Blo 1482061 1483319 := bstep (se 1 (by rfl) ⟨1112489, by rfl⟩ : syracuseStep 1483319 = 2224979) B2224979
theorem B1483339 : Blo 1482061 1483339 := bstep (se 1 (by rfl) ⟨1112504, by rfl⟩ : syracuseStep 1483339 = 2225009) B2225009
theorem B1483351 : Blo 1482061 1483351 := bstep (se 1 (by rfl) ⟨1112513, by rfl⟩ : syracuseStep 1483351 = 2225027) B2225027
theorem B13009501 : Blo 1482061 13009501 := bstep (se 3 (by rfl) ⟨2439281, by rfl⟩ : syracuseStep 13009501 = 4878563) B4878563
theorem B1483371 : Blo 1482061 1483371 := bstep (se 1 (by rfl) ⟨1112528, by rfl⟩ : syracuseStep 1483371 = 2225057) B2225057
theorem B1483383 : Blo 1482061 1483383 := bstep (se 1 (by rfl) ⟨1112537, by rfl⟩ : syracuseStep 1483383 = 2225075) B2225075
theorem B1483403 : Blo 1482061 1483403 := bstep (se 1 (by rfl) ⟨1112552, by rfl⟩ : syracuseStep 1483403 = 2225105) B2225105
theorem B12026519 : Blo 1482061 12026519 := bstep (se 1 (by rfl) ⟨9019889, by rfl⟩ : syracuseStep 12026519 = 18039779) B18039779
theorem B1483415 : Blo 1482061 1483415 := bstep (se 1 (by rfl) ⟨1112561, by rfl⟩ : syracuseStep 1483415 = 2225123) B2225123
theorem B1483435 : Blo 1482061 1483435 := bstep (se 1 (by rfl) ⟨1112576, by rfl⟩ : syracuseStep 1483435 = 2225153) B2225153
theorem B1483447 : Blo 1482061 1483447 := bstep (se 1 (by rfl) ⟨1112585, by rfl⟩ : syracuseStep 1483447 = 2225171) B2225171
theorem B3334859 : Blo 1482061 3334859 := bstep (se 1 (by rfl) ⟨2501144, by rfl⟩ : syracuseStep 3334859 = 5002289) B5002289
theorem B1483467 : Blo 1482061 1483467 := bstep (se 1 (by rfl) ⟨1112600, by rfl⟩ : syracuseStep 1483467 = 2225201) B2225201
theorem B10683085 : Blo 1482061 10683085 := bstep (se 3 (by rfl) ⟨2003078, by rfl⟩ : syracuseStep 10683085 = 4006157) B4006157
theorem B3384011 : Blo 1482061 3384011 := bstep (se 1 (by rfl) ⟨2538008, by rfl⟩ : syracuseStep 3384011 = 5076017) B5076017
theorem B1483479 : Blo 1482061 1483479 := bstep (se 1 (by rfl) ⟨1112609, by rfl⟩ : syracuseStep 1483479 = 2225219) B2225219
theorem B1483499 : Blo 1482061 1483499 := bstep (se 1 (by rfl) ⟨1112624, by rfl⟩ : syracuseStep 1483499 = 2225249) B2225249
theorem B1483511 : Blo 1482061 1483511 := bstep (se 1 (by rfl) ⟨1112633, by rfl⟩ : syracuseStep 1483511 = 2225267) B2225267
theorem B3334913 : Blo 1482061 3334913 := bstep (se 2 (by rfl) ⟨1250592, by rfl⟩ : syracuseStep 3334913 = 2501185) B2501185
theorem B1483531 : Blo 1482061 1483531 := bstep (se 1 (by rfl) ⟨1112648, by rfl⟩ : syracuseStep 1483531 = 2225297) B2225297
theorem B1483543 : Blo 1482061 1483543 := bstep (se 1 (by rfl) ⟨1112657, by rfl⟩ : syracuseStep 1483543 = 2225315) B2225315
theorem B1483563 : Blo 1482061 1483563 := bstep (se 1 (by rfl) ⟨1112672, by rfl⟩ : syracuseStep 1483563 = 2225345) B2225345
theorem B1483575 : Blo 1482061 1483575 := bstep (se 1 (by rfl) ⟨1112681, by rfl⟩ : syracuseStep 1483575 = 2225363) B2225363
theorem B1483595 : Blo 1482061 1483595 := bstep (se 1 (by rfl) ⟨1112696, by rfl⟩ : syracuseStep 1483595 = 2225393) B2225393
theorem B1483607 : Blo 1482061 1483607 := bstep (se 1 (by rfl) ⟨1112705, by rfl⟩ : syracuseStep 1483607 = 2225411) B2225411
theorem B5628761 : Blo 1482061 5628761 := bstep (se 2 (by rfl) ⟨2110785, by rfl⟩ : syracuseStep 5628761 = 4221571) B4221571
theorem B1483627 : Blo 1482061 1483627 := bstep (se 1 (by rfl) ⟨1112720, by rfl⟩ : syracuseStep 1483627 = 2225441) B2225441
theorem B1483639 : Blo 1482061 1483639 := bstep (se 1 (by rfl) ⟨1112729, by rfl⟩ : syracuseStep 1483639 = 2225459) B2225459
theorem B7127939 : Blo 1482061 7127939 := bstep (se 1 (by rfl) ⟨5345954, by rfl⟩ : syracuseStep 7127939 = 10691909) B10691909
theorem B1483659 : Blo 1482061 1483659 := bstep (se 1 (by rfl) ⟨1112744, by rfl⟩ : syracuseStep 1483659 = 2225489) B2225489
theorem B5006231 : Blo 1482061 5006231 := bstep (se 1 (by rfl) ⟨3754673, by rfl⟩ : syracuseStep 5006231 = 7509347) B7509347
theorem B1483671 : Blo 1482061 1483671 := bstep (se 1 (by rfl) ⟨1112753, by rfl⟩ : syracuseStep 1483671 = 2225507) B2225507
theorem B1483691 : Blo 1482061 1483691 := bstep (se 1 (by rfl) ⟨1112768, by rfl⟩ : syracuseStep 1483691 = 2225537) B2225537
theorem B1483703 : Blo 1482061 1483703 := bstep (se 1 (by rfl) ⟨1112777, by rfl⟩ : syracuseStep 1483703 = 2225555) B2225555
theorem B1483723 : Blo 1482061 1483723 := bstep (se 1 (by rfl) ⟨1112792, by rfl⟩ : syracuseStep 1483723 = 2225585) B2225585
theorem B1483735 : Blo 1482061 1483735 := bstep (se 1 (by rfl) ⟨1112801, by rfl⟩ : syracuseStep 1483735 = 2225603) B2225603
theorem B3335129 : Blo 1482061 3335129 := bstep (se 2 (by rfl) ⟨1250673, by rfl⟩ : syracuseStep 3335129 = 2501347) B2501347
theorem B1483755 : Blo 1482061 1483755 := bstep (se 1 (by rfl) ⟨1112816, by rfl⟩ : syracuseStep 1483755 = 2225633) B2225633
theorem B1483767 : Blo 1482061 1483767 := bstep (se 1 (by rfl) ⟨1112825, by rfl⟩ : syracuseStep 1483767 = 2225651) B2225651
theorem B1483787 : Blo 1482061 1483787 := bstep (se 1 (by rfl) ⟨1112840, by rfl⟩ : syracuseStep 1483787 = 2225681) B2225681
theorem B1483799 : Blo 1482061 1483799 := bstep (se 1 (by rfl) ⟨1112849, by rfl⟩ : syracuseStep 1483799 = 2225699) B2225699
theorem B1483819 : Blo 1482061 1483819 := bstep (se 1 (by rfl) ⟨1112864, by rfl⟩ : syracuseStep 1483819 = 2225729) B2225729
theorem B5628973 : Blo 1482061 5628973 := bstep (se 3 (by rfl) ⟨1055432, by rfl⟩ : syracuseStep 5628973 = 2110865) B2110865
theorem B3335219 : Blo 1482061 3335219 := bstep (se 1 (by rfl) ⟨2501414, by rfl⟩ : syracuseStep 3335219 = 5002829) B5002829
theorem B1483831 : Blo 1482061 1483831 := bstep (se 1 (by rfl) ⟨1112873, by rfl⟩ : syracuseStep 1483831 = 2225747) B2225747
theorem B1483851 : Blo 1482061 1483851 := bstep (se 1 (by rfl) ⟨1112888, by rfl⟩ : syracuseStep 1483851 = 2225777) B2225777
theorem B3335255 : Blo 1482061 3335255 := bstep (se 1 (by rfl) ⟨2501441, by rfl⟩ : syracuseStep 3335255 = 5002883) B5002883
theorem B1483863 : Blo 1482061 1483863 := bstep (se 1 (by rfl) ⟨1112897, by rfl⟩ : syracuseStep 1483863 = 2225795) B2225795
theorem B1483883 : Blo 1482061 1483883 := bstep (se 1 (by rfl) ⟨1112912, by rfl⟩ : syracuseStep 1483883 = 2225825) B2225825
theorem B1483895 : Blo 1482061 1483895 := bstep (se 1 (by rfl) ⟨1112921, by rfl⟩ : syracuseStep 1483895 = 2225843) B2225843
theorem B1483915 : Blo 1482061 1483915 := bstep (se 1 (by rfl) ⟨1112936, by rfl⟩ : syracuseStep 1483915 = 2225873) B2225873
theorem B1483927 : Blo 1482061 1483927 := bstep (se 1 (by rfl) ⟨1112945, by rfl⟩ : syracuseStep 1483927 = 2225891) B2225891
theorem B1483947 : Blo 1482061 1483947 := bstep (se 1 (by rfl) ⟨1112960, by rfl⟩ : syracuseStep 1483947 = 2225921) B2225921
theorem B2671795 : Blo 1482061 2671795 := bstep (se 1 (by rfl) ⟨2003846, by rfl⟩ : syracuseStep 2671795 = 4007693) B4007693
theorem B1483959 : Blo 1482061 1483959 := bstep (se 1 (by rfl) ⟨1112969, by rfl⟩ : syracuseStep 1483959 = 2225939) B2225939
theorem B1877195 : Blo 1482061 1877195 := bstep (se 1 (by rfl) ⟨1407896, by rfl⟩ : syracuseStep 1877195 = 2815793) B2815793
theorem B1483979 : Blo 1482061 1483979 := bstep (se 1 (by rfl) ⟨1112984, by rfl⟩ : syracuseStep 1483979 = 2225969) B2225969
theorem B15221965 : Blo 1482061 15221965 := bstep (se 3 (by rfl) ⟨2854118, by rfl⟩ : syracuseStep 15221965 = 5708237) B5708237
theorem B1483991 : Blo 1482061 1483991 := bstep (se 1 (by rfl) ⟨1112993, by rfl⟩ : syracuseStep 1483991 = 2225987) B2225987
theorem B1484011 : Blo 1482061 1484011 := bstep (se 1 (by rfl) ⟨1113008, by rfl⟩ : syracuseStep 1484011 = 2226017) B2226017
theorem B1484023 : Blo 1482061 1484023 := bstep (se 1 (by rfl) ⟨1113017, by rfl⟩ : syracuseStep 1484023 = 2226035) B2226035
theorem B3335435 : Blo 1482061 3335435 := bstep (se 1 (by rfl) ⟨2501576, by rfl⟩ : syracuseStep 3335435 = 5003153) B5003153
theorem B1484043 : Blo 1482061 1484043 := bstep (se 1 (by rfl) ⟨1113032, by rfl⟩ : syracuseStep 1484043 = 2226065) B2226065
theorem B1484055 : Blo 1482061 1484055 := bstep (se 1 (by rfl) ⟨1113041, by rfl⟩ : syracuseStep 1484055 = 2226083) B2226083
theorem B3335489 : Blo 1482061 3335489 := bstep (se 2 (by rfl) ⟨1250808, by rfl⟩ : syracuseStep 3335489 = 2501617) B2501617
theorem B9397579 : Blo 1482061 9397579 := bstep (se 1 (by rfl) ⟨7048184, by rfl⟩ : syracuseStep 9397579 = 14096369) B14096369
theorem B5629277 : Blo 1482061 5629277 := bstep (se 3 (by rfl) ⟨1055489, by rfl⟩ : syracuseStep 5629277 = 2110979) B2110979
theorem B5006771 : Blo 1482061 5006771 := bstep (se 1 (by rfl) ⟨3755078, by rfl⟩ : syracuseStep 5006771 = 7510157) B7510157
theorem B4752857 : Blo 1482061 4752857 := bstep (se 2 (by rfl) ⟨1782321, by rfl⟩ : syracuseStep 4752857 = 3564643) B3564643
theorem B3335705 : Blo 1482061 3335705 := bstep (se 2 (by rfl) ⟨1250889, by rfl⟩ : syracuseStep 3335705 = 2501779) B2501779
theorem B6333997 : Blo 1482061 6333997 := bstep (se 3 (by rfl) ⟨1187624, by rfl⟩ : syracuseStep 6333997 = 2375249) B2375249
theorem B3335795 : Blo 1482061 3335795 := bstep (se 1 (by rfl) ⟨2501846, by rfl⟩ : syracuseStep 3335795 = 5003693) B5003693
theorem B26035843 : Blo 1482061 26035843 := bstep (se 1 (by rfl) ⟨19526882, by rfl⟩ : syracuseStep 26035843 = 39053765) B39053765
theorem B3335831 : Blo 1482061 3335831 := bstep (se 1 (by rfl) ⟨2501873, by rfl⟩ : syracuseStep 3335831 = 5003747) B5003747
theorem B14247575 : Blo 1482061 14247575 := bstep (se 1 (by rfl) ⟨10685681, by rfl⟩ : syracuseStep 14247575 = 21371363) B21371363
theorem B5007041 : Blo 1482061 5007041 := bstep (se 2 (by rfl) ⟨1877640, by rfl⟩ : syracuseStep 5007041 = 3755281) B3755281
theorem B3565259 : Blo 1482061 3565259 := bstep (se 1 (by rfl) ⟨2673944, by rfl⟩ : syracuseStep 3565259 = 5347889) B5347889
theorem B25356077 : Blo 1482061 25356077 := bstep (se 3 (by rfl) ⟨4754264, by rfl⟩ : syracuseStep 25356077 = 9508529) B9508529
theorem B3802945 : Blo 1482061 3802945 := bstep (se 2 (by rfl) ⟨1426104, by rfl⟩ : syracuseStep 3802945 = 2852209) B2852209
theorem B3336011 : Blo 1482061 3336011 := bstep (se 1 (by rfl) ⟨2502008, by rfl⟩ : syracuseStep 3336011 = 5004017) B5004017
theorem B3753803 : Blo 1482061 3753803 := bstep (se 1 (by rfl) ⟨2815352, by rfl⟩ : syracuseStep 3753803 = 5630705) B5630705
theorem B8030045 : Blo 1482061 8030045 := bstep (se 3 (by rfl) ⟨1505633, by rfl⟩ : syracuseStep 8030045 = 3011267) B3011267
theorem B3336065 : Blo 1482061 3336065 := bstep (se 2 (by rfl) ⟨1251024, by rfl⟩ : syracuseStep 3336065 = 2502049) B2502049
theorem B1877899 : Blo 1482061 1877899 := bstep (se 1 (by rfl) ⟨1408424, by rfl⟩ : syracuseStep 1877899 = 2816849) B2816849
theorem B6424541 : Blo 1482061 6424541 := bstep (se 3 (by rfl) ⟨1204601, by rfl⟩ : syracuseStep 6424541 = 2409203) B2409203
theorem B6015041 : Blo 1482061 6015041 := bstep (se 2 (by rfl) ⟨2255640, by rfl⟩ : syracuseStep 6015041 = 4511281) B4511281
theorem B3336281 : Blo 1482061 3336281 := bstep (se 2 (by rfl) ⟨1251105, by rfl⟩ : syracuseStep 3336281 = 2502211) B2502211
theorem B1878167 : Blo 1482061 1878167 := bstep (se 1 (by rfl) ⟨1408625, by rfl⟩ : syracuseStep 1878167 = 2817251) B2817251
theorem B3336371 : Blo 1482061 3336371 := bstep (se 1 (by rfl) ⟨2502278, by rfl⟩ : syracuseStep 3336371 = 5004557) B5004557
theorem B2672833 : Blo 1482061 2672833 := bstep (se 2 (by rfl) ⟨1002312, by rfl⟩ : syracuseStep 2672833 = 2004625) B2004625
theorem B3336407 : Blo 1482061 3336407 := bstep (se 1 (by rfl) ⟨2502305, by rfl⟩ : syracuseStep 3336407 = 5004611) B5004611
theorem B5007581 : Blo 1482061 5007581 := bstep (se 3 (by rfl) ⟨938921, by rfl⟩ : syracuseStep 5007581 = 1877843) B1877843
theorem B1583371 : Blo 1482061 1583371 := bstep (se 1 (by rfl) ⟨1187528, by rfl⟩ : syracuseStep 1583371 = 2375057) B2375057
theorem B7506269 : Blo 1482061 7506269 := bstep (se 3 (by rfl) ⟨1407425, by rfl⟩ : syracuseStep 7506269 = 2814851) B2814851
theorem B2501003 : Blo 1482061 2501003 := bstep (se 1 (by rfl) ⟨1875752, by rfl⟩ : syracuseStep 2501003 = 3751505) B3751505
theorem B3336587 : Blo 1482061 3336587 := bstep (se 1 (by rfl) ⟨2502440, by rfl⟩ : syracuseStep 3336587 = 5004881) B5004881
theorem B3336641 : Blo 1482061 3336641 := bstep (se 2 (by rfl) ⟨1251240, by rfl⟩ : syracuseStep 3336641 = 2502481) B2502481
theorem B2501131 : Blo 1482061 2501131 := bstep (se 1 (by rfl) ⟨1875848, by rfl⟩ : syracuseStep 2501131 = 3751697) B3751697
theorem B7711325 : Blo 1482061 7711325 := bstep (se 3 (by rfl) ⟨1445873, by rfl⟩ : syracuseStep 7711325 = 2891747) B2891747
theorem B2501273 : Blo 1482061 2501273 := bstep (se 2 (by rfl) ⟨937977, by rfl⟩ : syracuseStep 2501273 = 1875955) B1875955
theorem B3336857 : Blo 1482061 3336857 := bstep (se 2 (by rfl) ⟨1251321, by rfl⟩ : syracuseStep 3336857 = 2502643) B2502643
theorem B3336947 : Blo 1482061 3336947 := bstep (se 1 (by rfl) ⟨2502710, by rfl⟩ : syracuseStep 3336947 = 5005421) B5005421
theorem B3336983 : Blo 1482061 3336983 := bstep (se 1 (by rfl) ⟨2502737, by rfl⟩ : syracuseStep 3336983 = 5005475) B5005475
theorem B3754775 : Blo 1482061 3754775 := bstep (se 1 (by rfl) ⟨2816081, by rfl⟩ : syracuseStep 3754775 = 5632163) B5632163
theorem B2501401 : Blo 1482061 2501401 := bstep (se 2 (by rfl) ⟨938025, by rfl⟩ : syracuseStep 2501401 = 1876051) B1876051
theorem B5344051 : Blo 1482061 5344051 := bstep (se 1 (by rfl) ⟨4008038, by rfl⟩ : syracuseStep 5344051 = 8016077) B8016077
theorem B13536179 : Blo 1482061 13536179 := bstep (se 1 (by rfl) ⟨10152134, by rfl⟩ : syracuseStep 13536179 = 20304269) B20304269
theorem B3337163 : Blo 1482061 3337163 := bstep (se 1 (by rfl) ⟨2502872, by rfl⟩ : syracuseStep 3337163 = 5005745) B5005745
theorem B3337217 : Blo 1482061 3337217 := bstep (se 2 (by rfl) ⟨1251456, by rfl⟩ : syracuseStep 3337217 = 2502913) B2502913
theorem B2223179 : Blo 1482061 2223179 := bstep (se 1 (by rfl) ⟨1667384, by rfl⟩ : syracuseStep 2223179 = 3334769) B3334769
theorem B2223191 : Blo 1482061 2223191 := bstep (se 1 (by rfl) ⟨1667393, by rfl⟩ : syracuseStep 2223191 = 3334787) B3334787
theorem B19016855 : Blo 1482061 19016855 := bstep (se 1 (by rfl) ⟨14262641, by rfl⟩ : syracuseStep 19016855 = 28525283) B28525283
theorem B2223257 : Blo 1482061 2223257 := bstep (se 2 (by rfl) ⟨833721, by rfl⟩ : syracuseStep 2223257 = 1667443) B1667443
theorem B3337433 : Blo 1482061 3337433 := bstep (se 2 (by rfl) ⟨1251537, by rfl⟩ : syracuseStep 3337433 = 2503075) B2503075
theorem B6859993 : Blo 1482061 6859993 := bstep (se 2 (by rfl) ⟨2572497, by rfl⟩ : syracuseStep 6859993 = 5144995) B5144995
theorem B2223371 : Blo 1482061 2223371 := bstep (se 1 (by rfl) ⟨1667528, by rfl⟩ : syracuseStep 2223371 = 3335057) B3335057
theorem B2223383 : Blo 1482061 2223383 := bstep (se 1 (by rfl) ⟨1667537, by rfl⟩ : syracuseStep 2223383 = 3335075) B3335075
theorem B24063277 : Blo 1482061 24063277 := bstep (se 3 (by rfl) ⟨4511864, by rfl⟩ : syracuseStep 24063277 = 9023729) B9023729
theorem B3337523 : Blo 1482061 3337523 := bstep (se 1 (by rfl) ⟨2503142, by rfl⟩ : syracuseStep 3337523 = 5006285) B5006285
theorem B2501975 : Blo 1482061 2501975 := bstep (se 1 (by rfl) ⟨1876481, by rfl⟩ : syracuseStep 2501975 = 3752963) B3752963
theorem B3337559 : Blo 1482061 3337559 := bstep (se 1 (by rfl) ⟨2503169, by rfl⟩ : syracuseStep 3337559 = 5006339) B5006339
theorem B2223449 : Blo 1482061 2223449 := bstep (se 2 (by rfl) ⟨833793, by rfl⟩ : syracuseStep 2223449 = 1667587) B1667587
theorem B2854273 : Blo 1482061 2854273 := bstep (se 2 (by rfl) ⟨1070352, by rfl⟩ : syracuseStep 2854273 = 2140705) B2140705
theorem B3755443 : Blo 1482061 3755443 := bstep (se 1 (by rfl) ⟨2816582, by rfl⟩ : syracuseStep 3755443 = 5633165) B5633165
theorem B2223563 : Blo 1482061 2223563 := bstep (se 1 (by rfl) ⟨1667672, by rfl⟩ : syracuseStep 2223563 = 3335345) B3335345
theorem B2223575 : Blo 1482061 2223575 := bstep (se 1 (by rfl) ⟨1667681, by rfl⟩ : syracuseStep 2223575 = 3335363) B3335363
theorem B2502103 : Blo 1482061 2502103 := bstep (se 1 (by rfl) ⟨1876577, by rfl⟩ : syracuseStep 2502103 = 3753155) B3753155
theorem B9498073 : Blo 1482061 9498073 := bstep (se 2 (by rfl) ⟨3561777, by rfl⟩ : syracuseStep 9498073 = 7123555) B7123555
theorem B3337739 : Blo 1482061 3337739 := bstep (se 1 (by rfl) ⟨2503304, by rfl⟩ : syracuseStep 3337739 = 5006609) B5006609
theorem B2223641 : Blo 1482061 2223641 := bstep (se 2 (by rfl) ⟨833865, by rfl⟩ : syracuseStep 2223641 = 1667731) B1667731
theorem B3337793 : Blo 1482061 3337793 := bstep (se 2 (by rfl) ⟨1251672, by rfl⟩ : syracuseStep 3337793 = 2503345) B2503345
theorem B3755585 : Blo 1482061 3755585 := bstep (se 2 (by rfl) ⟨1408344, by rfl⟩ : syracuseStep 3755585 = 2816689) B2816689
theorem B2223755 : Blo 1482061 2223755 := bstep (se 1 (by rfl) ⟨1667816, by rfl⟩ : syracuseStep 2223755 = 3335633) B3335633
theorem B1781399 : Blo 1482061 1781399 := bstep (se 1 (by rfl) ⟨1336049, by rfl⟩ : syracuseStep 1781399 = 2672099) B2672099
theorem B2223767 : Blo 1482061 2223767 := bstep (se 1 (by rfl) ⟨1667825, by rfl⟩ : syracuseStep 2223767 = 3335651) B3335651
theorem B7925399 : Blo 1482061 7925399 := bstep (se 1 (by rfl) ⟨5944049, by rfl⟩ : syracuseStep 7925399 = 11888099) B11888099
theorem B10145459 : Blo 1482061 10145459 := bstep (se 1 (by rfl) ⟨7609094, by rfl⟩ : syracuseStep 10145459 = 15218189) B15218189
theorem B23137973 : Blo 1482061 23137973 := bstep (se 5 (by rfl) ⟨1084592, by rfl⟩ : syracuseStep 23137973 = 2169185) B2169185
theorem B2223833 : Blo 1482061 2223833 := bstep (se 2 (by rfl) ⟨833937, by rfl⟩ : syracuseStep 2223833 = 1667875) B1667875
theorem B21384965 : Blo 1482061 21384965 := bstep (se 4 (by rfl) ⟨2004840, by rfl⟩ : syracuseStep 21384965 = 4009681) B4009681
theorem B3338009 : Blo 1482061 3338009 := bstep (se 2 (by rfl) ⟨1251753, by rfl⟩ : syracuseStep 3338009 = 2503507) B2503507
theorem B2223947 : Blo 1482061 2223947 := bstep (se 1 (by rfl) ⟨1667960, by rfl⟩ : syracuseStep 2223947 = 3335921) B3335921
theorem B2223959 : Blo 1482061 2223959 := bstep (se 1 (by rfl) ⟨1667969, by rfl⟩ : syracuseStep 2223959 = 3335939) B3335939
theorem B4222813 : Blo 1482061 4222813 := bstep (se 3 (by rfl) ⟨791777, by rfl⟩ : syracuseStep 4222813 = 1583555) B1583555
theorem B3338099 : Blo 1482061 3338099 := bstep (se 1 (by rfl) ⟨2503574, by rfl⟩ : syracuseStep 3338099 = 5007149) B5007149
theorem B5631875 : Blo 1482061 5631875 := bstep (se 1 (by rfl) ⟨4223906, by rfl⟩ : syracuseStep 5631875 = 8447813) B8447813
theorem B5631889 : Blo 1482061 5631889 := bstep (se 2 (by rfl) ⟨2111958, by rfl⟩ : syracuseStep 5631889 = 4223917) B4223917
theorem B6336407 : Blo 1482061 6336407 := bstep (se 1 (by rfl) ⟨4752305, by rfl⟩ : syracuseStep 6336407 = 9504611) B9504611
theorem B3338135 : Blo 1482061 3338135 := bstep (se 1 (by rfl) ⟨2503601, by rfl⟩ : syracuseStep 3338135 = 5007203) B5007203
theorem B2813849 : Blo 1482061 2813849 := bstep (se 2 (by rfl) ⟨1055193, by rfl⟩ : syracuseStep 2813849 = 2110387) B2110387
theorem B2224025 : Blo 1482061 2224025 := bstep (se 2 (by rfl) ⟨834009, by rfl⟩ : syracuseStep 2224025 = 1668019) B1668019
theorem B2224139 : Blo 1482061 2224139 := bstep (se 1 (by rfl) ⟨1668104, by rfl⟩ : syracuseStep 2224139 = 3336209) B3336209
theorem B2224151 : Blo 1482061 2224151 := bstep (se 1 (by rfl) ⟨1668113, by rfl⟩ : syracuseStep 2224151 = 3336227) B3336227
theorem B2502731 : Blo 1482061 2502731 := bstep (se 1 (by rfl) ⟨1877048, by rfl⟩ : syracuseStep 2502731 = 3754097) B3754097
theorem B3338315 : Blo 1482061 3338315 := bstep (se 1 (by rfl) ⟨2503736, by rfl⟩ : syracuseStep 3338315 = 5007473) B5007473
theorem B2224217 : Blo 1482061 2224217 := bstep (se 2 (by rfl) ⟨834081, by rfl⟩ : syracuseStep 2224217 = 1668163) B1668163
theorem B3338369 : Blo 1482061 3338369 := bstep (se 2 (by rfl) ⟨1251888, by rfl⟩ : syracuseStep 3338369 = 2503777) B2503777
theorem B5632193 : Blo 1482061 5632193 := bstep (se 2 (by rfl) ⟨2112072, by rfl⟩ : syracuseStep 5632193 = 4224145) B4224145
theorem B5075137 : Blo 1482061 5075137 := bstep (se 2 (by rfl) ⟨1903176, by rfl⟩ : syracuseStep 5075137 = 3806353) B3806353
theorem B2224331 : Blo 1482061 2224331 := bstep (se 1 (by rfl) ⟨1668248, by rfl⟩ : syracuseStep 2224331 = 3336497) B3336497
theorem B2502859 : Blo 1482061 2502859 := bstep (se 1 (by rfl) ⟨1877144, by rfl⟩ : syracuseStep 2502859 = 3754289) B3754289
theorem B16888013 : Blo 1482061 16888013 := bstep (se 3 (by rfl) ⟨3166502, by rfl⟩ : syracuseStep 16888013 = 6333005) B6333005
theorem B2224343 : Blo 1482061 2224343 := bstep (se 1 (by rfl) ⟨1668257, by rfl⟩ : syracuseStep 2224343 = 3336515) B3336515
theorem B2224409 : Blo 1482061 2224409 := bstep (se 2 (by rfl) ⟨834153, by rfl⟩ : syracuseStep 2224409 = 1668307) B1668307
theorem B1667371 : Blo 1482061 1667371 := bstep (se 1 (by rfl) ⟨1250528, by rfl⟩ : syracuseStep 1667371 = 2501057) B2501057
theorem B2814259 : Blo 1482061 2814259 := bstep (se 1 (by rfl) ⟨2110694, by rfl⟩ : syracuseStep 2814259 = 4221389) B4221389
theorem B2503001 : Blo 1482061 2503001 := bstep (se 2 (by rfl) ⟨938625, by rfl⟩ : syracuseStep 2503001 = 1877251) B1877251
theorem B3338585 : Blo 1482061 3338585 := bstep (se 2 (by rfl) ⟨1251969, by rfl⟩ : syracuseStep 3338585 = 2503939) B2503939
theorem B2224523 : Blo 1482061 2224523 := bstep (se 1 (by rfl) ⟨1668392, by rfl⟩ : syracuseStep 2224523 = 3336785) B3336785
theorem B1667479 : Blo 1482061 1667479 := bstep (se 1 (by rfl) ⟨1250609, by rfl⟩ : syracuseStep 1667479 = 2501219) B2501219
theorem B2224535 : Blo 1482061 2224535 := bstep (se 1 (by rfl) ⟨1668401, by rfl⟩ : syracuseStep 2224535 = 3336803) B3336803
theorem B7508375 : Blo 1482061 7508375 := bstep (se 1 (by rfl) ⟨5631281, by rfl⟩ : syracuseStep 7508375 = 11262563) B11262563
theorem B9015731 : Blo 1482061 9015731 := bstep (se 1 (by rfl) ⟨6761798, by rfl⟩ : syracuseStep 9015731 = 13523597) B13523597
theorem B3338675 : Blo 1482061 3338675 := bstep (se 1 (by rfl) ⟨2504006, by rfl⟩ : syracuseStep 3338675 = 5008013) B5008013
theorem B3338711 : Blo 1482061 3338711 := bstep (se 1 (by rfl) ⟨2504033, by rfl⟩ : syracuseStep 3338711 = 5008067) B5008067
theorem B2224601 : Blo 1482061 2224601 := bstep (se 2 (by rfl) ⟨834225, by rfl⟩ : syracuseStep 2224601 = 1668451) B1668451
theorem B2503129 : Blo 1482061 2503129 := bstep (se 2 (by rfl) ⟨938673, by rfl⟩ : syracuseStep 2503129 = 1877347) B1877347
theorem B8442413 : Blo 1482061 8442413 := bstep (se 3 (by rfl) ⟨1582952, by rfl⟩ : syracuseStep 8442413 = 3165905) B3165905
theorem B8802881 : Blo 1482061 8802881 := bstep (se 2 (by rfl) ⟨3301080, by rfl⟩ : syracuseStep 8802881 = 6602161) B6602161
theorem B1667659 : Blo 1482061 1667659 := bstep (se 1 (by rfl) ⟨1250744, by rfl⟩ : syracuseStep 1667659 = 2501489) B2501489
theorem B2224715 : Blo 1482061 2224715 := bstep (se 1 (by rfl) ⟨1668536, by rfl⟩ : syracuseStep 2224715 = 3337073) B3337073
theorem B2224727 : Blo 1482061 2224727 := bstep (se 1 (by rfl) ⟨1668545, by rfl⟩ : syracuseStep 2224727 = 3337091) B3337091
theorem B12669533 : Blo 1482061 12669533 := bstep (se 3 (by rfl) ⟨2375537, by rfl⟩ : syracuseStep 12669533 = 4751075) B4751075
theorem B72168029 : Blo 1482061 72168029 := bstep (se 3 (by rfl) ⟨13531505, by rfl⟩ : syracuseStep 72168029 = 27063011) B27063011
theorem B3338891 : Blo 1482061 3338891 := bstep (se 1 (by rfl) ⟨2504168, by rfl⟩ : syracuseStep 3338891 = 5008337) B5008337
theorem B1692311 : Blo 1482061 1692311 := bstep (se 1 (by rfl) ⟨1269233, by rfl⟩ : syracuseStep 1692311 = 2538467) B2538467
theorem B2224793 : Blo 1482061 2224793 := bstep (se 2 (by rfl) ⟨834297, by rfl⟩ : syracuseStep 2224793 = 1668595) B1668595
theorem B2708147 : Blo 1482061 2708147 := bstep (se 1 (by rfl) ⟨2031110, by rfl⟩ : syracuseStep 2708147 = 4062221) B4062221
theorem B1667767 : Blo 1482061 1667767 := bstep (se 1 (by rfl) ⟨1250825, by rfl⟩ : syracuseStep 1667767 = 2501651) B2501651
theorem B3166913 : Blo 1482061 3166913 := bstep (se 2 (by rfl) ⟨1187592, by rfl⟩ : syracuseStep 3166913 = 2375185) B2375185
theorem B3338945 : Blo 1482061 3338945 := bstep (se 2 (by rfl) ⟨1252104, by rfl⟩ : syracuseStep 3338945 = 2504209) B2504209
theorem B2224907 : Blo 1482061 2224907 := bstep (se 1 (by rfl) ⟨1668680, by rfl⟩ : syracuseStep 2224907 = 3337361) B3337361
theorem B11268881 : Blo 1482061 11268881 := bstep (se 2 (by rfl) ⟨4225830, by rfl⟩ : syracuseStep 11268881 = 8451661) B8451661
theorem B2224919 : Blo 1482061 2224919 := bstep (se 1 (by rfl) ⟨1668689, by rfl⟩ : syracuseStep 2224919 = 3337379) B3337379
theorem B2814745 : Blo 1482061 2814745 := bstep (se 2 (by rfl) ⟨1055529, by rfl⟩ : syracuseStep 2814745 = 2111059) B2111059
theorem B38507329 : Blo 1482061 38507329 := bstep (se 2 (by rfl) ⟨14440248, by rfl⟩ : syracuseStep 38507329 = 28880497) B28880497
theorem B5002073 : Blo 1482061 5002073 := bstep (se 2 (by rfl) ⟨1875777, by rfl⟩ : syracuseStep 5002073 = 3751555) B3751555
theorem B2224985 : Blo 1482061 2224985 := bstep (se 2 (by rfl) ⟨834369, by rfl⟩ : syracuseStep 2224985 = 1668739) B1668739
theorem B5632861 : Blo 1482061 5632861 := bstep (se 3 (by rfl) ⟨1056161, by rfl⟩ : syracuseStep 5632861 = 2112323) B2112323
theorem B1667947 : Blo 1482061 1667947 := bstep (se 1 (by rfl) ⟨1250960, by rfl⟩ : syracuseStep 1667947 = 2501921) B2501921
theorem B1782667 : Blo 1482061 1782667 := bstep (se 1 (by rfl) ⟨1337000, by rfl⟩ : syracuseStep 1782667 = 2674001) B2674001
theorem B10687409 : Blo 1482061 10687409 := bstep (se 2 (by rfl) ⟨4007778, by rfl⟩ : syracuseStep 10687409 = 8015557) B8015557
theorem B2225099 : Blo 1482061 2225099 := bstep (se 1 (by rfl) ⟨1668824, by rfl⟩ : syracuseStep 2225099 = 3337649) B3337649
theorem B1668055 : Blo 1482061 1668055 := bstep (se 1 (by rfl) ⟨1251041, by rfl⟩ : syracuseStep 1668055 = 2502083) B2502083
theorem B2225111 : Blo 1482061 2225111 := bstep (se 1 (by rfl) ⟨1668833, by rfl⟩ : syracuseStep 2225111 = 3337667) B3337667
theorem B3167255 : Blo 1482061 3167255 := bstep (se 1 (by rfl) ⟨2375441, by rfl⟩ : syracuseStep 3167255 = 4750883) B4750883
theorem B2503703 : Blo 1482061 2503703 := bstep (se 1 (by rfl) ⟨1877777, by rfl⟩ : syracuseStep 2503703 = 3755555) B3755555
theorem B2225177 : Blo 1482061 2225177 := bstep (se 2 (by rfl) ⟨834441, by rfl⟩ : syracuseStep 2225177 = 1668883) B1668883
theorem B4224089 : Blo 1482061 4224089 := bstep (se 2 (by rfl) ⟨1584033, by rfl⟩ : syracuseStep 4224089 = 3168067) B3168067
theorem B1668235 : Blo 1482061 1668235 := bstep (se 1 (by rfl) ⟨1251176, by rfl⟩ : syracuseStep 1668235 = 2502353) B2502353
theorem B2225291 : Blo 1482061 2225291 := bstep (se 1 (by rfl) ⟨1668968, by rfl⟩ : syracuseStep 2225291 = 3337937) B3337937
theorem B2225303 : Blo 1482061 2225303 := bstep (se 1 (by rfl) ⟨1668977, by rfl⟩ : syracuseStep 2225303 = 3337955) B3337955
theorem B2503831 : Blo 1482061 2503831 := bstep (se 1 (by rfl) ⟨1877873, by rfl⟩ : syracuseStep 2503831 = 3755747) B3755747
theorem B11261105 : Blo 1482061 11261105 := bstep (se 2 (by rfl) ⟨4222914, by rfl⟩ : syracuseStep 11261105 = 8445829) B8445829
theorem B7713971 : Blo 1482061 7713971 := bstep (se 1 (by rfl) ⟨5785478, by rfl⟩ : syracuseStep 7713971 = 11570957) B11570957
theorem B2225369 : Blo 1482061 2225369 := bstep (se 2 (by rfl) ⟨834513, by rfl⟩ : syracuseStep 2225369 = 1669027) B1669027
theorem B1668343 : Blo 1482061 1668343 := bstep (se 1 (by rfl) ⟨1251257, by rfl⟩ : syracuseStep 1668343 = 2502515) B2502515
theorem B19010861 : Blo 1482061 19010861 := bstep (se 3 (by rfl) ⟨3564536, by rfl⟩ : syracuseStep 19010861 = 7129073) B7129073
theorem B6763841 : Blo 1482061 6763841 := bstep (se 2 (by rfl) ⟨2536440, by rfl⟩ : syracuseStep 6763841 = 5072881) B5072881
theorem B2815307 : Blo 1482061 2815307 := bstep (se 1 (by rfl) ⟨2111480, by rfl⟩ : syracuseStep 2815307 = 4222961) B4222961
theorem B2225483 : Blo 1482061 2225483 := bstep (se 1 (by rfl) ⟨1669112, by rfl⟩ : syracuseStep 2225483 = 3338225) B3338225
theorem B2225495 : Blo 1482061 2225495 := bstep (se 1 (by rfl) ⟨1669121, by rfl⟩ : syracuseStep 2225495 = 3338243) B3338243
theorem B8451479 : Blo 1482061 8451479 := bstep (se 1 (by rfl) ⟨6338609, by rfl⟩ : syracuseStep 8451479 = 12677219) B12677219
theorem B2225561 : Blo 1482061 2225561 := bstep (se 2 (by rfl) ⟨834585, by rfl⟩ : syracuseStep 2225561 = 1669171) B1669171
theorem B1668523 : Blo 1482061 1668523 := bstep (se 1 (by rfl) ⟨1251392, by rfl⟩ : syracuseStep 1668523 = 2502785) B2502785
theorem B2815489 : Blo 1482061 2815489 := bstep (se 2 (by rfl) ⟨1055808, by rfl⟩ : syracuseStep 2815489 = 2111617) B2111617
theorem B2225675 : Blo 1482061 2225675 := bstep (se 1 (by rfl) ⟨1669256, by rfl⟩ : syracuseStep 2225675 = 3338513) B3338513
theorem B48100877 : Blo 1482061 48100877 := bstep (se 3 (by rfl) ⟨9018914, by rfl⟩ : syracuseStep 48100877 = 18037829) B18037829
theorem B5002775 : Blo 1482061 5002775 := bstep (se 1 (by rfl) ⟨3752081, by rfl⟩ : syracuseStep 5002775 = 7504163) B7504163
theorem B1668631 : Blo 1482061 1668631 := bstep (se 1 (by rfl) ⟨1251473, by rfl⟩ : syracuseStep 1668631 = 2502947) B2502947
theorem B2225687 : Blo 1482061 2225687 := bstep (se 1 (by rfl) ⟨1669265, by rfl⟩ : syracuseStep 2225687 = 3338531) B3338531
theorem B10688075 : Blo 1482061 10688075 := bstep (se 1 (by rfl) ⟨8016056, by rfl⟩ : syracuseStep 10688075 = 16032113) B16032113
theorem B3167819 : Blo 1482061 3167819 := bstep (se 1 (by rfl) ⟨2375864, by rfl⟩ : syracuseStep 3167819 = 4751729) B4751729
theorem B2225753 : Blo 1482061 2225753 := bstep (se 2 (by rfl) ⟨834657, by rfl⟩ : syracuseStep 2225753 = 1669315) B1669315
theorem B11261591 : Blo 1482061 11261591 := bstep (se 1 (by rfl) ⟨8446193, by rfl⟩ : syracuseStep 11261591 = 16892387) B16892387
theorem B2111179 : Blo 1482061 2111179 := bstep (se 1 (by rfl) ⟨1583384, by rfl⟩ : syracuseStep 2111179 = 3166769) B3166769
theorem B1668811 : Blo 1482061 1668811 := bstep (se 1 (by rfl) ⟨1251608, by rfl⟩ : syracuseStep 1668811 = 2503217) B2503217
theorem B2225867 : Blo 1482061 2225867 := bstep (se 1 (by rfl) ⟨1669400, by rfl⟩ : syracuseStep 2225867 = 3338801) B3338801
theorem B2225879 : Blo 1482061 2225879 := bstep (se 1 (by rfl) ⟨1669409, by rfl⟩ : syracuseStep 2225879 = 3338819) B3338819
theorem B6952721 : Blo 1482061 6952721 := bstep (se 2 (by rfl) ⟨2607270, by rfl⟩ : syracuseStep 6952721 = 5214541) B5214541
theorem B6338321 : Blo 1482061 6338321 := bstep (se 2 (by rfl) ⟨2376870, by rfl⟩ : syracuseStep 6338321 = 4753741) B4753741
theorem B2225945 : Blo 1482061 2225945 := bstep (se 2 (by rfl) ⟨834729, by rfl⟩ : syracuseStep 2225945 = 1669459) B1669459
theorem B1668919 : Blo 1482061 1668919 := bstep (se 1 (by rfl) ⟨1251689, by rfl⟩ : syracuseStep 1668919 = 2503379) B2503379
theorem B2226059 : Blo 1482061 2226059 := bstep (se 1 (by rfl) ⟨1669544, by rfl⟩ : syracuseStep 2226059 = 3339089) B3339089
theorem B2226071 : Blo 1482061 2226071 := bstep (se 1 (by rfl) ⟨1669553, by rfl⟩ : syracuseStep 2226071 = 3339107) B3339107
theorem B11409329 : Blo 1482061 11409329 := bstep (se 2 (by rfl) ⟨4278498, by rfl⟩ : syracuseStep 11409329 = 8556997) B8556997
theorem B1669099 : Blo 1482061 1669099 := bstep (se 1 (by rfl) ⟨1251824, by rfl⟩ : syracuseStep 1669099 = 2503649) B2503649
theorem B5003315 : Blo 1482061 5003315 := bstep (se 1 (by rfl) ⟨3752486, by rfl⟩ : syracuseStep 5003315 = 7504973) B7504973
theorem B60889157 : Blo 1482061 60889157 := bstep (se 4 (by rfl) ⟨5708358, by rfl⟩ : syracuseStep 60889157 = 11416717) B11416717
theorem B3209291 : Blo 1482061 3209291 := bstep (se 1 (by rfl) ⟨2406968, by rfl⟩ : syracuseStep 3209291 = 4813937) B4813937
theorem B1669207 : Blo 1482061 1669207 := bstep (se 1 (by rfl) ⟨1251905, by rfl⟩ : syracuseStep 1669207 = 2503811) B2503811
theorem B5634137 : Blo 1482061 5634137 := bstep (se 2 (by rfl) ⟨2112801, by rfl⟩ : syracuseStep 5634137 = 4225603) B4225603
theorem B3168409 : Blo 1482061 3168409 := bstep (se 2 (by rfl) ⟨1188153, by rfl⟩ : syracuseStep 3168409 = 2376307) B2376307
theorem B2816203 : Blo 1482061 2816203 := bstep (se 1 (by rfl) ⟨2112152, by rfl⟩ : syracuseStep 2816203 = 4224305) B4224305
theorem B1669387 : Blo 1482061 1669387 := bstep (se 1 (by rfl) ⟨1252040, by rfl⟩ : syracuseStep 1669387 = 2504081) B2504081
theorem B2816279 : Blo 1482061 2816279 := bstep (se 1 (by rfl) ⟨2112209, by rfl⟩ : syracuseStep 2816279 = 4224419) B4224419
theorem B5003585 : Blo 1482061 5003585 := bstep (se 2 (by rfl) ⟨1876344, by rfl⟩ : syracuseStep 5003585 = 3752689) B3752689
theorem B1669495 : Blo 1482061 1669495 := bstep (se 1 (by rfl) ⟨1252121, by rfl⟩ : syracuseStep 1669495 = 2504243) B2504243
theorem B5708225 : Blo 1482061 5708225 := bstep (se 2 (by rfl) ⟨2140584, by rfl⟩ : syracuseStep 5708225 = 4281169) B4281169
theorem B2374103 : Blo 1482061 2374103 := bstep (se 1 (by rfl) ⟨1780577, by rfl⟩ : syracuseStep 2374103 = 3561155) B3561155
theorem B4282841 : Blo 1482061 4282841 := bstep (se 2 (by rfl) ⟨1606065, by rfl⟩ : syracuseStep 4282841 = 3212131) B3212131
theorem B6330955 : Blo 1482061 6330955 := bstep (se 1 (by rfl) ⟨4748216, by rfl⟩ : syracuseStep 6330955 = 9496433) B9496433
theorem B3562163 : Blo 1482061 3562163 := bstep (se 1 (by rfl) ⟨2671622, by rfl⟩ : syracuseStep 3562163 = 5343245) B5343245
theorem B4512449 : Blo 1482061 4512449 := bstep (se 2 (by rfl) ⟨1692168, by rfl⟩ : syracuseStep 4512449 = 3384337) B3384337
theorem B4225729 : Blo 1482061 4225729 := bstep (se 2 (by rfl) ⟨1584648, by rfl⟩ : syracuseStep 4225729 = 3169297) B3169297
theorem B3005185 : Blo 1482061 3005185 := bstep (se 2 (by rfl) ⟨1126944, by rfl⟩ : syracuseStep 3005185 = 2253889) B2253889
theorem B6331229 : Blo 1482061 6331229 := bstep (se 3 (by rfl) ⟨1187105, by rfl⟩ : syracuseStep 6331229 = 2374211) B2374211
theorem B5004125 : Blo 1482061 5004125 := bstep (se 3 (by rfl) ⟨938273, by rfl⟩ : syracuseStep 5004125 = 1876547) B1876547
theorem B2112409 : Blo 1482061 2112409 := bstep (se 2 (by rfl) ⟨792153, by rfl⟩ : syracuseStep 2112409 = 1584307) B1584307
theorem B2816947 : Blo 1482061 2816947 := bstep (se 1 (by rfl) ⟨2112710, by rfl⟩ : syracuseStep 2816947 = 4225421) B4225421
theorem B3521483 : Blo 1482061 3521483 := bstep (se 1 (by rfl) ⟨2641112, by rfl⟩ : syracuseStep 3521483 = 5282225) B5282225
theorem B2374667 : Blo 1482061 2374667 := bstep (se 1 (by rfl) ⟨1781000, by rfl⟩ : syracuseStep 2374667 = 3562001) B3562001
theorem B2817175 : Blo 1482061 2817175 := bstep (se 1 (by rfl) ⟨2112881, by rfl⟩ : syracuseStep 2817175 = 4225763) B4225763
theorem B6331571 : Blo 1482061 6331571 := bstep (se 1 (by rfl) ⟨4748678, by rfl⟩ : syracuseStep 6331571 = 9497357) B9497357
theorem B3169459 : Blo 1482061 3169459 := bstep (se 1 (by rfl) ⟨2377094, by rfl⟩ : syracuseStep 3169459 = 4754189) B4754189
theorem B3005633 : Blo 1482061 3005633 := bstep (se 2 (by rfl) ⟨1127112, by rfl⟩ : syracuseStep 3005633 = 2254225) B2254225
theorem B2817281 : Blo 1482061 2817281 := bstep (se 2 (by rfl) ⟨1056480, by rfl⟩ : syracuseStep 2817281 = 2112961) B2112961
theorem B1482071 : Blo 1482061 1482071 := bstep (se 1 (by rfl) ⟨1111553, by rfl⟩ : syracuseStep 1482071 = 2223107) B2223107
theorem B1482091 : Blo 1482061 1482091 := bstep (se 1 (by rfl) ⟨1111568, by rfl⟩ : syracuseStep 1482091 = 2223137) B2223137
theorem B1482103 : Blo 1482061 1482103 := bstep (se 1 (by rfl) ⟨1111577, by rfl⟩ : syracuseStep 1482103 = 2223155) B2223155
theorem B1482123 : Blo 1482061 1482123 := bstep (se 1 (by rfl) ⟨1111592, by rfl⟩ : syracuseStep 1482123 = 2223185) B2223185
theorem B1482135 : Blo 1482061 1482135 := bstep (se 1 (by rfl) ⟨1111601, by rfl⟩ : syracuseStep 1482135 = 2223203) B2223203
theorem B1482155 : Blo 1482061 1482155 := bstep (se 1 (by rfl) ⟨1111616, by rfl⟩ : syracuseStep 1482155 = 2223233) B2223233
theorem B3562931 : Blo 1482061 3562931 := bstep (se 1 (by rfl) ⟨2672198, by rfl⟩ : syracuseStep 3562931 = 5344397) B5344397
theorem B1482167 : Blo 1482061 1482167 := bstep (se 1 (by rfl) ⟨1111625, by rfl⟩ : syracuseStep 1482167 = 2223251) B2223251
theorem B1482187 : Blo 1482061 1482187 := bstep (se 1 (by rfl) ⟨1111640, by rfl⟩ : syracuseStep 1482187 = 2223281) B2223281
theorem B1482199 : Blo 1482061 1482199 := bstep (se 1 (by rfl) ⟨1111649, by rfl⟩ : syracuseStep 1482199 = 2223299) B2223299
theorem B1482219 : Blo 1482061 1482219 := bstep (se 1 (by rfl) ⟨1111664, by rfl⟩ : syracuseStep 1482219 = 2223329) B2223329
theorem B1482231 : Blo 1482061 1482231 := bstep (se 1 (by rfl) ⟨1111673, by rfl⟩ : syracuseStep 1482231 = 2223347) B2223347
theorem B1482251 : Blo 1482061 1482251 := bstep (se 1 (by rfl) ⟨1111688, by rfl⟩ : syracuseStep 1482251 = 2223377) B2223377
theorem B1482263 : Blo 1482061 1482263 := bstep (se 1 (by rfl) ⟨1111697, by rfl⟩ : syracuseStep 1482263 = 2223395) B2223395
theorem B1482283 : Blo 1482061 1482283 := bstep (se 1 (by rfl) ⟨1111712, by rfl⟩ : syracuseStep 1482283 = 2223425) B2223425
theorem B1482295 : Blo 1482061 1482295 := bstep (se 1 (by rfl) ⟨1111721, by rfl⟩ : syracuseStep 1482295 = 2223443) B2223443
theorem B1482315 : Blo 1482061 1482315 := bstep (se 1 (by rfl) ⟨1111736, by rfl⟩ : syracuseStep 1482315 = 2223473) B2223473
theorem B15228491 : Blo 1482061 15228491 := bstep (se 1 (by rfl) ⟨11421368, by rfl⟩ : syracuseStep 15228491 = 22842737) B22842737
theorem B1482327 : Blo 1482061 1482327 := bstep (se 1 (by rfl) ⟨1111745, by rfl⟩ : syracuseStep 1482327 = 2223491) B2223491
theorem B16899677 : Blo 1482061 16899677 := bstep (se 3 (by rfl) ⟨3168689, by rfl⟩ : syracuseStep 16899677 = 6337379) B6337379
theorem B1482347 : Blo 1482061 1482347 := bstep (se 1 (by rfl) ⟨1111760, by rfl⟩ : syracuseStep 1482347 = 2223521) B2223521
theorem B1482359 : Blo 1482061 1482359 := bstep (se 1 (by rfl) ⟨1111769, by rfl⟩ : syracuseStep 1482359 = 2223539) B2223539
theorem B1482379 : Blo 1482061 1482379 := bstep (se 1 (by rfl) ⟨1111784, by rfl⟩ : syracuseStep 1482379 = 2223569) B2223569
theorem B1482391 : Blo 1482061 1482391 := bstep (se 1 (by rfl) ⟨1111793, by rfl⟩ : syracuseStep 1482391 = 2223587) B2223587
theorem B1482411 : Blo 1482061 1482411 := bstep (se 1 (by rfl) ⟨1111808, by rfl⟩ : syracuseStep 1482411 = 2223617) B2223617
theorem B1482423 : Blo 1482061 1482423 := bstep (se 1 (by rfl) ⟨1111817, by rfl⟩ : syracuseStep 1482423 = 2223635) B2223635
theorem B1482443 : Blo 1482061 1482443 := bstep (se 1 (by rfl) ⟨1111832, by rfl⟩ : syracuseStep 1482443 = 2223665) B2223665
theorem B1482455 : Blo 1482061 1482455 := bstep (se 1 (by rfl) ⟨1111841, by rfl⟩ : syracuseStep 1482455 = 2223683) B2223683
theorem B1482475 : Blo 1482061 1482475 := bstep (se 1 (by rfl) ⟨1111856, by rfl⟩ : syracuseStep 1482475 = 2223713) B2223713
theorem B1482487 : Blo 1482061 1482487 := bstep (se 1 (by rfl) ⟨1111865, by rfl⟩ : syracuseStep 1482487 = 2223731) B2223731
theorem B1482507 : Blo 1482061 1482507 := bstep (se 1 (by rfl) ⟨1111880, by rfl⟩ : syracuseStep 1482507 = 2223761) B2223761
theorem B1482519 : Blo 1482061 1482519 := bstep (se 1 (by rfl) ⟨1111889, by rfl⟩ : syracuseStep 1482519 = 2223779) B2223779
theorem B1482539 : Blo 1482061 1482539 := bstep (se 1 (by rfl) ⟨1111904, by rfl⟩ : syracuseStep 1482539 = 2223809) B2223809
theorem B1482551 : Blo 1482061 1482551 := bstep (se 1 (by rfl) ⟨1111913, by rfl⟩ : syracuseStep 1482551 = 2223827) B2223827
theorem B1482571 : Blo 1482061 1482571 := bstep (se 1 (by rfl) ⟨1111928, by rfl⟩ : syracuseStep 1482571 = 2223857) B2223857
theorem B1482583 : Blo 1482061 1482583 := bstep (se 1 (by rfl) ⟨1111937, by rfl⟩ : syracuseStep 1482583 = 2223875) B2223875
theorem B1482603 : Blo 1482061 1482603 := bstep (se 1 (by rfl) ⟨1111952, by rfl⟩ : syracuseStep 1482603 = 2223905) B2223905
theorem B1482615 : Blo 1482061 1482615 := bstep (se 1 (by rfl) ⟨1111961, by rfl⟩ : syracuseStep 1482615 = 2223923) B2223923
theorem B7511939 : Blo 1482061 7511939 := bstep (se 1 (by rfl) ⟨5633954, by rfl⟩ : syracuseStep 7511939 = 11267909) B11267909
theorem B1482635 : Blo 1482061 1482635 := bstep (se 1 (by rfl) ⟨1111976, by rfl⟩ : syracuseStep 1482635 = 2223953) B2223953
theorem B1482647 : Blo 1482061 1482647 := bstep (se 1 (by rfl) ⟨1111985, by rfl⟩ : syracuseStep 1482647 = 2223971) B2223971
theorem B6766487 : Blo 1482061 6766487 := bstep (se 1 (by rfl) ⟨5074865, by rfl⟩ : syracuseStep 6766487 = 10149731) B10149731
theorem B1482667 : Blo 1482061 1482667 := bstep (se 1 (by rfl) ⟨1112000, by rfl⟩ : syracuseStep 1482667 = 2224001) B2224001
theorem B3751859 : Blo 1482061 3751859 := bstep (se 1 (by rfl) ⟨2813894, by rfl⟩ : syracuseStep 3751859 = 5627789) B5627789
theorem B17121203 : Blo 1482061 17121203 := bstep (se 1 (by rfl) ⟨12840902, by rfl⟩ : syracuseStep 17121203 = 25681805) B25681805
theorem B1482679 : Blo 1482061 1482679 := bstep (se 1 (by rfl) ⟨1112009, by rfl⟩ : syracuseStep 1482679 = 2224019) B2224019
theorem B1482699 : Blo 1482061 1482699 := bstep (se 1 (by rfl) ⟨1112024, by rfl⟩ : syracuseStep 1482699 = 2224049) B2224049
theorem B5005259 : Blo 1482061 5005259 := bstep (se 1 (by rfl) ⟨3753944, by rfl⟩ : syracuseStep 5005259 = 7507889) B7507889
theorem B12664781 : Blo 1482061 12664781 := bstep (se 3 (by rfl) ⟨2374646, by rfl⟩ : syracuseStep 12664781 = 4749293) B4749293
theorem B1482711 : Blo 1482061 1482711 := bstep (se 1 (by rfl) ⟨1112033, by rfl⟩ : syracuseStep 1482711 = 2224067) B2224067
theorem B1482731 : Blo 1482061 1482731 := bstep (se 1 (by rfl) ⟨1112048, by rfl⟩ : syracuseStep 1482731 = 2224097) B2224097
theorem B1482743 : Blo 1482061 1482743 := bstep (se 1 (by rfl) ⟨1112057, by rfl⟩ : syracuseStep 1482743 = 2224115) B2224115
theorem B1482759 : Blo 1482061 1482759 := bstep (se 1 (by rfl) ⟨1112069, by rfl⟩ : syracuseStep 1482759 = 2224139) B2224139
theorem B1482767 : Blo 1482061 1482767 := bstep (se 1 (by rfl) ⟨1112075, by rfl⟩ : syracuseStep 1482767 = 2224151) B2224151
theorem B1482811 : Blo 1482061 1482811 := bstep (se 1 (by rfl) ⟨1112108, by rfl⟩ : syracuseStep 1482811 = 2224217) B2224217
theorem B1482887 : Blo 1482061 1482887 := bstep (se 1 (by rfl) ⟨1112165, by rfl⟩ : syracuseStep 1482887 = 2224331) B2224331
theorem B1482895 : Blo 1482061 1482895 := bstep (se 1 (by rfl) ⟨1112171, by rfl⟩ : syracuseStep 1482895 = 2224343) B2224343
theorem B1482939 : Blo 1482061 1482939 := bstep (se 1 (by rfl) ⟨1112204, by rfl⟩ : syracuseStep 1482939 = 2224409) B2224409
theorem B3563777 : Blo 1482061 3563777 := bstep (se 2 (by rfl) ⟨1336416, by rfl⟩ : syracuseStep 3563777 = 2672833) B2672833
theorem B6766849 : Blo 1482061 6766849 := bstep (se 2 (by rfl) ⟨2537568, by rfl⟩ : syracuseStep 6766849 = 5075137) B5075137
theorem B1483015 : Blo 1482061 1483015 := bstep (se 1 (by rfl) ⟨1112261, by rfl⟩ : syracuseStep 1483015 = 2224523) B2224523
theorem B3752203 : Blo 1482061 3752203 := bstep (se 1 (by rfl) ⟨2814152, by rfl⟩ : syracuseStep 3752203 = 5628305) B5628305
theorem B1483023 : Blo 1482061 1483023 := bstep (se 1 (by rfl) ⟨1112267, by rfl⟩ : syracuseStep 1483023 = 2224535) B2224535
theorem B5005583 : Blo 1482061 5005583 := bstep (se 1 (by rfl) ⟨3754187, by rfl⟩ : syracuseStep 5005583 = 7508375) B7508375
theorem B1483067 : Blo 1482061 1483067 := bstep (se 1 (by rfl) ⟨1112300, by rfl⟩ : syracuseStep 1483067 = 2224601) B2224601
theorem B5628275 : Blo 1482061 5628275 := bstep (se 1 (by rfl) ⟨4221206, by rfl⟩ : syracuseStep 5628275 = 8442413) B8442413
theorem B1483143 : Blo 1482061 1483143 := bstep (se 1 (by rfl) ⟨1112357, by rfl⟩ : syracuseStep 1483143 = 2224715) B2224715
theorem B1483151 : Blo 1482061 1483151 := bstep (se 1 (by rfl) ⟨1112363, by rfl⟩ : syracuseStep 1483151 = 2224727) B2224727
theorem B8446355 : Blo 1482061 8446355 := bstep (se 1 (by rfl) ⟨6334766, by rfl⟩ : syracuseStep 8446355 = 12669533) B12669533
theorem B48112019 : Blo 1482061 48112019 := bstep (se 1 (by rfl) ⟨36084014, by rfl⟩ : syracuseStep 48112019 = 72168029) B72168029
theorem B3752345 : Blo 1482061 3752345 := bstep (se 2 (by rfl) ⟨1407129, by rfl⟩ : syracuseStep 3752345 = 2814259) B2814259
theorem B1483195 : Blo 1482061 1483195 := bstep (se 1 (by rfl) ⟨1112396, by rfl⟩ : syracuseStep 1483195 = 2224793) B2224793
theorem B1483271 : Blo 1482061 1483271 := bstep (se 1 (by rfl) ⟨1112453, by rfl⟩ : syracuseStep 1483271 = 2224907) B2224907
theorem B7512587 : Blo 1482061 7512587 := bstep (se 1 (by rfl) ⟨5634440, by rfl⟩ : syracuseStep 7512587 = 11268881) B11268881
theorem B1483279 : Blo 1482061 1483279 := bstep (se 1 (by rfl) ⟨1112459, by rfl⟩ : syracuseStep 1483279 = 2224919) B2224919
theorem B5005853 : Blo 1482061 5005853 := bstep (se 3 (by rfl) ⟨938597, by rfl⟩ : syracuseStep 5005853 = 1877195) B1877195
theorem B3334715 : Blo 1482061 3334715 := bstep (se 1 (by rfl) ⟨2501036, by rfl⟩ : syracuseStep 3334715 = 5002073) B5002073
theorem B3752507 : Blo 1482061 3752507 := bstep (se 1 (by rfl) ⟨2814380, by rfl⟩ : syracuseStep 3752507 = 5628761) B5628761
theorem B1483323 : Blo 1482061 1483323 := bstep (se 1 (by rfl) ⟨1112492, by rfl⟩ : syracuseStep 1483323 = 2224985) B2224985
theorem B4751959 : Blo 1482061 4751959 := bstep (se 1 (by rfl) ⟨3563969, by rfl⟩ : syracuseStep 4751959 = 7127939) B7127939
theorem B1483399 : Blo 1482061 1483399 := bstep (se 1 (by rfl) ⟨1112549, by rfl⟩ : syracuseStep 1483399 = 2225099) B2225099
theorem B1483407 : Blo 1482061 1483407 := bstep (se 1 (by rfl) ⟨1112555, by rfl⟩ : syracuseStep 1483407 = 2225111) B2225111
theorem B7512749 : Blo 1482061 7512749 := bstep (se 3 (by rfl) ⟨1408640, by rfl⟩ : syracuseStep 7512749 = 2817281) B2817281
theorem B3334841 : Blo 1482061 3334841 := bstep (se 2 (by rfl) ⟨1250565, by rfl⟩ : syracuseStep 3334841 = 2501131) B2501131
theorem B1483451 : Blo 1482061 1483451 := bstep (se 1 (by rfl) ⟨1112588, by rfl⟩ : syracuseStep 1483451 = 2225177) B2225177
theorem B1483527 : Blo 1482061 1483527 := bstep (se 1 (by rfl) ⟨1112645, by rfl⟩ : syracuseStep 1483527 = 2225291) B2225291
theorem B1483535 : Blo 1482061 1483535 := bstep (se 1 (by rfl) ⟨1112651, by rfl⟩ : syracuseStep 1483535 = 2225303) B2225303
theorem B1483579 : Blo 1482061 1483579 := bstep (se 1 (by rfl) ⟨1112684, by rfl⟩ : syracuseStep 1483579 = 2225369) B2225369
theorem B12673907 : Blo 1482061 12673907 := bstep (se 1 (by rfl) ⟨9505430, by rfl⟩ : syracuseStep 12673907 = 19010861) B19010861
theorem B1876871 : Blo 1482061 1876871 := bstep (se 1 (by rfl) ⟨1407653, by rfl⟩ : syracuseStep 1876871 = 2815307) B2815307
theorem B1483655 : Blo 1482061 1483655 := bstep (se 1 (by rfl) ⟨1112741, by rfl⟩ : syracuseStep 1483655 = 2225483) B2225483
theorem B1483663 : Blo 1482061 1483663 := bstep (se 1 (by rfl) ⟨1112747, by rfl⟩ : syracuseStep 1483663 = 2225495) B2225495
theorem B3752851 : Blo 1482061 3752851 := bstep (se 1 (by rfl) ⟨2814638, by rfl⟩ : syracuseStep 3752851 = 5629277) B5629277
theorem B1483707 : Blo 1482061 1483707 := bstep (se 1 (by rfl) ⟨1112780, by rfl⟩ : syracuseStep 1483707 = 2225561) B2225561
theorem B4006913 : Blo 1482061 4006913 := bstep (se 2 (by rfl) ⟨1502592, by rfl⟩ : syracuseStep 4006913 = 3005185) B3005185
theorem B1483783 : Blo 1482061 1483783 := bstep (se 1 (by rfl) ⟨1112837, by rfl⟩ : syracuseStep 1483783 = 2225675) B2225675
theorem B3335183 : Blo 1482061 3335183 := bstep (se 1 (by rfl) ⟨2501387, by rfl⟩ : syracuseStep 3335183 = 5002775) B5002775
theorem B1483791 : Blo 1482061 1483791 := bstep (se 1 (by rfl) ⟨1112843, by rfl⟩ : syracuseStep 1483791 = 2225687) B2225687
theorem B3335201 : Blo 1482061 3335201 := bstep (se 2 (by rfl) ⟨1250700, by rfl⟩ : syracuseStep 3335201 = 2501401) B2501401
theorem B3752993 : Blo 1482061 3752993 := bstep (se 2 (by rfl) ⟨1407372, by rfl⟩ : syracuseStep 3752993 = 2814745) B2814745
theorem B1483835 : Blo 1482061 1483835 := bstep (se 1 (by rfl) ⟨1112876, by rfl⟩ : syracuseStep 1483835 = 2225753) B2225753
theorem B2376839 : Blo 1482061 2376839 := bstep (se 1 (by rfl) ⟨1782629, by rfl⟩ : syracuseStep 2376839 = 3565259) B3565259
theorem B1483911 : Blo 1482061 1483911 := bstep (se 1 (by rfl) ⟨1112933, by rfl⟩ : syracuseStep 1483911 = 2225867) B2225867
theorem B1483919 : Blo 1482061 1483919 := bstep (se 1 (by rfl) ⟨1112939, by rfl⟩ : syracuseStep 1483919 = 2225879) B2225879
theorem B1483963 : Blo 1482061 1483963 := bstep (se 1 (by rfl) ⟨1112972, by rfl⟩ : syracuseStep 1483963 = 2225945) B2225945
theorem B1484039 : Blo 1482061 1484039 := bstep (se 1 (by rfl) ⟨1113029, by rfl⟩ : syracuseStep 1484039 = 2226059) B2226059
theorem B1484047 : Blo 1482061 1484047 := bstep (se 1 (by rfl) ⟨1113035, by rfl⟩ : syracuseStep 1484047 = 2226071) B2226071
theorem B3335543 : Blo 1482061 3335543 := bstep (se 1 (by rfl) ⟨2501657, by rfl⟩ : syracuseStep 3335543 = 5003315) B5003315
theorem B40592771 : Blo 1482061 40592771 := bstep (se 1 (by rfl) ⟨30444578, by rfl⟩ : syracuseStep 40592771 = 60889157) B60889157
theorem B2139527 : Blo 1482061 2139527 := bstep (se 1 (by rfl) ⟨1604645, by rfl⟩ : syracuseStep 2139527 = 3209291) B3209291
theorem B7505297 : Blo 1482061 7505297 := bstep (se 2 (by rfl) ⟨2814486, by rfl⟩ : syracuseStep 7505297 = 5628973) B5628973
theorem B1877519 : Blo 1482061 1877519 := bstep (se 1 (by rfl) ⟨1408139, by rfl⟩ : syracuseStep 1877519 = 2816279) B2816279
theorem B3335723 : Blo 1482061 3335723 := bstep (se 1 (by rfl) ⟨2501792, by rfl⟩ : syracuseStep 3335723 = 5003585) B5003585
theorem B1582735 : Blo 1482061 1582735 := bstep (se 1 (by rfl) ⟨1187051, by rfl⟩ : syracuseStep 1582735 = 2374103) B2374103
theorem B3336083 : Blo 1482061 3336083 := bstep (se 1 (by rfl) ⟨2502062, by rfl⟩ : syracuseStep 3336083 = 5004125) B5004125
theorem B4220819 : Blo 1482061 4220819 := bstep (se 1 (by rfl) ⟨3165614, by rfl⟩ : syracuseStep 4220819 = 6331229) B6331229
theorem B5007257 : Blo 1482061 5007257 := bstep (se 2 (by rfl) ⟨1877721, by rfl⟩ : syracuseStep 5007257 = 3755443) B3755443
theorem B3336137 : Blo 1482061 3336137 := bstep (se 2 (by rfl) ⟨1251051, by rfl⟩ : syracuseStep 3336137 = 2502103) B2502103
theorem B3753985 : Blo 1482061 3753985 := bstep (se 2 (by rfl) ⟨1407744, by rfl⟩ : syracuseStep 3753985 = 2815489) B2815489
theorem B1583111 : Blo 1482061 1583111 := bstep (se 1 (by rfl) ⟨1187333, by rfl⟩ : syracuseStep 1583111 = 2374667) B2374667
theorem B18540589 : Blo 1482061 18540589 := bstep (se 3 (by rfl) ⟨3476360, by rfl⟩ : syracuseStep 18540589 = 6952721) B6952721
theorem B4221047 : Blo 1482061 4221047 := bstep (se 1 (by rfl) ⟨3165785, by rfl⟩ : syracuseStep 4221047 = 6331571) B6331571
theorem B11266451 : Blo 1482061 11266451 := bstep (se 1 (by rfl) ⟨8449838, by rfl⟩ : syracuseStep 11266451 = 16899677) B16899677
theorem B5630417 : Blo 1482061 5630417 := bstep (se 2 (by rfl) ⟨2111406, by rfl⟩ : syracuseStep 5630417 = 4222813) B4222813
theorem B14256643 : Blo 1482061 14256643 := bstep (se 1 (by rfl) ⟨10692482, by rfl⟩ : syracuseStep 14256643 = 21384965) B21384965
theorem B3754583 : Blo 1482061 3754583 := bstep (se 1 (by rfl) ⟨2815937, by rfl⟩ : syracuseStep 3754583 = 5631875) B5631875
theorem B5007959 : Blo 1482061 5007959 := bstep (se 1 (by rfl) ⟨3755969, by rfl⟩ : syracuseStep 5007959 = 7511939) B7511939
theorem B2501239 : Blo 1482061 2501239 := bstep (se 1 (by rfl) ⟨1875929, by rfl⟩ : syracuseStep 2501239 = 3751859) B3751859
theorem B11414135 : Blo 1482061 11414135 := bstep (se 1 (by rfl) ⟨8560601, by rfl⟩ : syracuseStep 11414135 = 17121203) B17121203
theorem B3336839 : Blo 1482061 3336839 := bstep (se 1 (by rfl) ⟨2502629, by rfl⟩ : syracuseStep 3336839 = 5005259) B5005259
theorem B28879577 : Blo 1482061 28879577 := bstep (se 2 (by rfl) ⟨10829841, by rfl⟩ : syracuseStep 28879577 = 21659683) B21659683
theorem B5630735 : Blo 1482061 5630735 := bstep (se 1 (by rfl) ⟨4223051, by rfl⟩ : syracuseStep 5630735 = 8446103) B8446103
theorem B3754795 : Blo 1482061 3754795 := bstep (se 1 (by rfl) ⟨2816096, by rfl⟩ : syracuseStep 3754795 = 5632193) B5632193
theorem B11258675 : Blo 1482061 11258675 := bstep (se 1 (by rfl) ⟨8444006, by rfl⟩ : syracuseStep 11258675 = 16888013) B16888013
theorem B2501435 : Blo 1482061 2501435 := bstep (se 1 (by rfl) ⟨1876076, by rfl⟩ : syracuseStep 2501435 = 3752153) B3752153
theorem B3337019 : Blo 1482061 3337019 := bstep (se 1 (by rfl) ⟨2502764, by rfl⟩ : syracuseStep 3337019 = 5005529) B5005529
theorem B5073799 : Blo 1482061 5073799 := bstep (se 1 (by rfl) ⟨3805349, by rfl⟩ : syracuseStep 5073799 = 7610699) B7610699
theorem B3337145 : Blo 1482061 3337145 := bstep (se 2 (by rfl) ⟨1251429, by rfl⟩ : syracuseStep 3337145 = 2502859) B2502859
theorem B3754937 : Blo 1482061 3754937 := bstep (se 2 (by rfl) ⟨1408101, by rfl⟩ : syracuseStep 3754937 = 2816203) B2816203
theorem B2223095 : Blo 1482061 2223095 := bstep (se 1 (by rfl) ⟨1667321, by rfl⟩ : syracuseStep 2223095 = 3334643) B3334643
theorem B2223119 : Blo 1482061 2223119 := bstep (se 1 (by rfl) ⟨1667339, by rfl⟩ : syracuseStep 2223119 = 3334679) B3334679
theorem B5868587 : Blo 1482061 5868587 := bstep (se 1 (by rfl) ⟨4401440, by rfl⟩ : syracuseStep 5868587 = 8802881) B8802881
theorem B2223161 : Blo 1482061 2223161 := bstep (se 2 (by rfl) ⟨833685, by rfl⟩ : syracuseStep 2223161 = 1667371) B1667371
theorem B5008445 : Blo 1482061 5008445 := bstep (se 3 (by rfl) ⟨939083, by rfl⟩ : syracuseStep 5008445 = 1878167) B1878167
theorem B1805431 : Blo 1482061 1805431 := bstep (se 1 (by rfl) ⟨1354073, by rfl⟩ : syracuseStep 1805431 = 2708147) B2708147
theorem B2223239 : Blo 1482061 2223239 := bstep (se 1 (by rfl) ⟨1667429, by rfl⟩ : syracuseStep 2223239 = 3334859) B3334859
theorem B2256007 : Blo 1482061 2256007 := bstep (se 1 (by rfl) ⟨1692005, by rfl⟩ : syracuseStep 2256007 = 3384011) B3384011
theorem B2223275 : Blo 1482061 2223275 := bstep (se 1 (by rfl) ⟨1667456, by rfl⟩ : syracuseStep 2223275 = 3334913) B3334913
theorem B8015021 : Blo 1482061 8015021 := bstep (se 3 (by rfl) ⟨1502816, by rfl⟩ : syracuseStep 8015021 = 3005633) B3005633
theorem B2223305 : Blo 1482061 2223305 := bstep (se 2 (by rfl) ⟨833739, by rfl⟩ : syracuseStep 2223305 = 1667479) B1667479
theorem B2501833 : Blo 1482061 2501833 := bstep (se 2 (by rfl) ⟨938187, by rfl⟩ : syracuseStep 2501833 = 1876375) B1876375
theorem B3337487 : Blo 1482061 3337487 := bstep (se 1 (by rfl) ⟨2503115, by rfl⟩ : syracuseStep 3337487 = 5006231) B5006231
theorem B3337505 : Blo 1482061 3337505 := bstep (se 2 (by rfl) ⟨1251564, by rfl⟩ : syracuseStep 3337505 = 2503129) B2503129
theorem B2223419 : Blo 1482061 2223419 := bstep (se 1 (by rfl) ⟨1667564, by rfl⟩ : syracuseStep 2223419 = 3335129) B3335129
theorem B2223479 : Blo 1482061 2223479 := bstep (se 1 (by rfl) ⟨1667609, by rfl⟩ : syracuseStep 2223479 = 3335219) B3335219
theorem B2223503 : Blo 1482061 2223503 := bstep (se 1 (by rfl) ⟨1667627, by rfl⟩ : syracuseStep 2223503 = 3335255) B3335255
theorem B8441273 : Blo 1482061 8441273 := bstep (se 2 (by rfl) ⟨3165477, by rfl⟩ : syracuseStep 8441273 = 6330955) B6330955
theorem B2223545 : Blo 1482061 2223545 := bstep (se 2 (by rfl) ⟨833829, by rfl⟩ : syracuseStep 2223545 = 1667659) B1667659
theorem B7507403 : Blo 1482061 7507403 := bstep (se 1 (by rfl) ⟨5630552, by rfl⟩ : syracuseStep 7507403 = 11261105) B11261105
theorem B17346001 : Blo 1482061 17346001 := bstep (se 2 (by rfl) ⟨6504750, by rfl⟩ : syracuseStep 17346001 = 13009501) B13009501
theorem B2223623 : Blo 1482061 2223623 := bstep (se 1 (by rfl) ⟨1667717, by rfl⟩ : syracuseStep 2223623 = 3335435) B3335435
theorem B4509227 : Blo 1482061 4509227 := bstep (se 1 (by rfl) ⟨3381920, by rfl⟩ : syracuseStep 4509227 = 6763841) B6763841
theorem B2223659 : Blo 1482061 2223659 := bstep (se 1 (by rfl) ⟨1667744, by rfl⟩ : syracuseStep 2223659 = 3335489) B3335489
theorem B2223689 : Blo 1482061 2223689 := bstep (se 2 (by rfl) ⟨833883, by rfl⟩ : syracuseStep 2223689 = 1667767) B1667767
theorem B3337847 : Blo 1482061 3337847 := bstep (se 1 (by rfl) ⟨2503385, by rfl⟩ : syracuseStep 3337847 = 5006771) B5006771
theorem B32067251 : Blo 1482061 32067251 := bstep (se 1 (by rfl) ⟨24050438, by rfl⟩ : syracuseStep 32067251 = 48100877) B48100877
theorem B2223803 : Blo 1482061 2223803 := bstep (se 1 (by rfl) ⟨1667852, by rfl⟩ : syracuseStep 2223803 = 3335705) B3335705
theorem B2223863 : Blo 1482061 2223863 := bstep (se 1 (by rfl) ⟨1667897, by rfl⟩ : syracuseStep 2223863 = 3335795) B3335795
theorem B51343105 : Blo 1482061 51343105 := bstep (se 2 (by rfl) ⟨19253664, by rfl⟩ : syracuseStep 51343105 = 38507329) B38507329
theorem B9498383 : Blo 1482061 9498383 := bstep (se 1 (by rfl) ⟨7123787, by rfl⟩ : syracuseStep 9498383 = 14247575) B14247575
theorem B2223887 : Blo 1482061 2223887 := bstep (se 1 (by rfl) ⟨1667915, by rfl⟩ : syracuseStep 2223887 = 3335831) B3335831
theorem B7507727 : Blo 1482061 7507727 := bstep (se 1 (by rfl) ⟨5630795, by rfl⟩ : syracuseStep 7507727 = 11261591) B11261591
theorem B3338027 : Blo 1482061 3338027 := bstep (se 1 (by rfl) ⟨2503520, by rfl⟩ : syracuseStep 3338027 = 5007041) B5007041
theorem B2223929 : Blo 1482061 2223929 := bstep (se 2 (by rfl) ⟨833973, by rfl⟩ : syracuseStep 2223929 = 1667947) B1667947
theorem B16904051 : Blo 1482061 16904051 := bstep (se 1 (by rfl) ⟨12678038, by rfl⟩ : syracuseStep 16904051 = 25356077) B25356077
theorem B2224007 : Blo 1482061 2224007 := bstep (se 1 (by rfl) ⟨1668005, by rfl⟩ : syracuseStep 2224007 = 3336011) B3336011
theorem B2502535 : Blo 1482061 2502535 := bstep (se 1 (by rfl) ⟨1876901, by rfl⟩ : syracuseStep 2502535 = 3753803) B3753803
theorem B5353363 : Blo 1482061 5353363 := bstep (se 1 (by rfl) ⟨4015022, by rfl⟩ : syracuseStep 5353363 = 8030045) B8030045
theorem B3755929 : Blo 1482061 3755929 := bstep (se 2 (by rfl) ⟨1408473, by rfl⟩ : syracuseStep 3755929 = 2816947) B2816947
theorem B2224043 : Blo 1482061 2224043 := bstep (se 1 (by rfl) ⟨1668032, by rfl⟩ : syracuseStep 2224043 = 3336065) B3336065
theorem B2224073 : Blo 1482061 2224073 := bstep (se 2 (by rfl) ⟨834027, by rfl⟩ : syracuseStep 2224073 = 1668055) B1668055
theorem B7606219 : Blo 1482061 7606219 := bstep (se 1 (by rfl) ⟨5704664, by rfl⟩ : syracuseStep 7606219 = 11409329) B11409329
theorem B4010027 : Blo 1482061 4010027 := bstep (se 1 (by rfl) ⟨3007520, by rfl⟩ : syracuseStep 4010027 = 6015041) B6015041
theorem B2224187 : Blo 1482061 2224187 := bstep (se 1 (by rfl) ⟨1668140, by rfl⟩ : syracuseStep 2224187 = 3336281) B3336281
theorem B3756091 : Blo 1482061 3756091 := bstep (se 1 (by rfl) ⟨2817068, by rfl⟩ : syracuseStep 3756091 = 5634137) B5634137
theorem B2224247 : Blo 1482061 2224247 := bstep (se 1 (by rfl) ⟨1668185, by rfl⟩ : syracuseStep 2224247 = 3336371) B3336371
theorem B2224271 : Blo 1482061 2224271 := bstep (se 1 (by rfl) ⟨1668203, by rfl⟩ : syracuseStep 2224271 = 3336407) B3336407
theorem B3338387 : Blo 1482061 3338387 := bstep (se 1 (by rfl) ⟨2503790, by rfl⟩ : syracuseStep 3338387 = 5007581) B5007581
theorem B2224313 : Blo 1482061 2224313 := bstep (se 2 (by rfl) ⟨834117, by rfl⟩ : syracuseStep 2224313 = 1668235) B1668235
theorem B3338441 : Blo 1482061 3338441 := bstep (se 2 (by rfl) ⟨1251915, by rfl⟩ : syracuseStep 3338441 = 2503831) B2503831
theorem B3756233 : Blo 1482061 3756233 := bstep (se 2 (by rfl) ⟨1408587, by rfl⟩ : syracuseStep 3756233 = 2817175) B2817175
theorem B84537589 : Blo 1482061 84537589 := bstep (se 5 (by rfl) ⟨3962699, by rfl⟩ : syracuseStep 84537589 = 7925399) B7925399
theorem B1667335 : Blo 1482061 1667335 := bstep (se 1 (by rfl) ⟨1250501, by rfl⟩ : syracuseStep 1667335 = 2501003) B2501003
theorem B2224391 : Blo 1482061 2224391 := bstep (se 1 (by rfl) ⟨1668293, by rfl⟩ : syracuseStep 2224391 = 3336587) B3336587
theorem B20295953 : Blo 1482061 20295953 := bstep (se 2 (by rfl) ⟨7610982, by rfl⟩ : syracuseStep 20295953 = 15221965) B15221965
theorem B9146657 : Blo 1482061 9146657 := bstep (se 2 (by rfl) ⟨3429996, by rfl⟩ : syracuseStep 9146657 = 6859993) B6859993
theorem B2224427 : Blo 1482061 2224427 := bstep (se 1 (by rfl) ⟨1668320, by rfl⟩ : syracuseStep 2224427 = 3336641) B3336641
theorem B3805483 : Blo 1482061 3805483 := bstep (se 1 (by rfl) ⟨2854112, by rfl⟩ : syracuseStep 3805483 = 5708225) B5708225
theorem B2855227 : Blo 1482061 2855227 := bstep (se 1 (by rfl) ⟨2141420, by rfl⟩ : syracuseStep 2855227 = 4282841) B4282841
theorem B2224457 : Blo 1482061 2224457 := bstep (se 2 (by rfl) ⟨834171, by rfl⟩ : syracuseStep 2224457 = 1668343) B1668343
theorem B32084369 : Blo 1482061 32084369 := bstep (se 2 (by rfl) ⟨12031638, by rfl⟩ : syracuseStep 32084369 = 24063277) B24063277
theorem B5140883 : Blo 1482061 5140883 := bstep (se 1 (by rfl) ⟨3855662, by rfl⟩ : syracuseStep 5140883 = 7711325) B7711325
theorem B12530105 : Blo 1482061 12530105 := bstep (se 2 (by rfl) ⟨4698789, by rfl⟩ : syracuseStep 12530105 = 9397579) B9397579
theorem B1667515 : Blo 1482061 1667515 := bstep (se 1 (by rfl) ⟨1250636, by rfl⟩ : syracuseStep 1667515 = 2501273) B2501273
theorem B2224571 : Blo 1482061 2224571 := bstep (se 1 (by rfl) ⟨1668428, by rfl⟩ : syracuseStep 2224571 = 3336857) B3336857
theorem B27054557 : Blo 1482061 27054557 := bstep (se 3 (by rfl) ⟨5072729, by rfl⟩ : syracuseStep 27054557 = 10145459) B10145459
theorem B2224631 : Blo 1482061 2224631 := bstep (se 1 (by rfl) ⟨1668473, by rfl⟩ : syracuseStep 2224631 = 3336947) B3336947
theorem B3805697 : Blo 1482061 3805697 := bstep (se 2 (by rfl) ⟨1427136, by rfl⟩ : syracuseStep 3805697 = 2854273) B2854273
theorem B2224655 : Blo 1482061 2224655 := bstep (se 1 (by rfl) ⟨1668491, by rfl⟩ : syracuseStep 2224655 = 3336983) B3336983
theorem B2503183 : Blo 1482061 2503183 := bstep (se 1 (by rfl) ⟨1877387, by rfl⟩ : syracuseStep 2503183 = 3754775) B3754775
theorem B2224697 : Blo 1482061 2224697 := bstep (se 2 (by rfl) ⟨834261, by rfl⟩ : syracuseStep 2224697 = 1668523) B1668523
theorem B9024119 : Blo 1482061 9024119 := bstep (se 1 (by rfl) ⟨6768089, by rfl⟩ : syracuseStep 9024119 = 13536179) B13536179
theorem B2347655 : Blo 1482061 2347655 := bstep (se 1 (by rfl) ⟨1760741, by rfl⟩ : syracuseStep 2347655 = 3521483) B3521483
theorem B2224775 : Blo 1482061 2224775 := bstep (se 1 (by rfl) ⟨1668581, by rfl⟩ : syracuseStep 2224775 = 3337163) B3337163
theorem B2224811 : Blo 1482061 2224811 := bstep (se 1 (by rfl) ⟨1668608, by rfl⟩ : syracuseStep 2224811 = 3337217) B3337217
theorem B2224841 : Blo 1482061 2224841 := bstep (se 2 (by rfl) ⟨834315, by rfl⟩ : syracuseStep 2224841 = 1668631) B1668631
theorem B9507557 : Blo 1482061 9507557 := bstep (se 4 (by rfl) ⟨891333, by rfl⟩ : syracuseStep 9507557 = 1782667) B1782667
theorem B12677903 : Blo 1482061 12677903 := bstep (se 1 (by rfl) ⟨9508427, by rfl⟩ : syracuseStep 12677903 = 19016855) B19016855
theorem B2224955 : Blo 1482061 2224955 := bstep (se 1 (by rfl) ⟨1668716, by rfl⟩ : syracuseStep 2224955 = 3337433) B3337433
theorem B34714457 : Blo 1482061 34714457 := bstep (se 2 (by rfl) ⟨13017921, by rfl⟩ : syracuseStep 34714457 = 26035843) B26035843
theorem B2225015 : Blo 1482061 2225015 := bstep (se 1 (by rfl) ⟨1668761, by rfl⟩ : syracuseStep 2225015 = 3337523) B3337523
theorem B1667983 : Blo 1482061 1667983 := bstep (se 1 (by rfl) ⟨1250987, by rfl⟩ : syracuseStep 1667983 = 2501975) B2501975
theorem B2225039 : Blo 1482061 2225039 := bstep (se 1 (by rfl) ⟨1668779, by rfl⟩ : syracuseStep 2225039 = 3337559) B3337559
theorem B2814905 : Blo 1482061 2814905 := bstep (se 2 (by rfl) ⟨1055589, by rfl⟩ : syracuseStep 2814905 = 2111179) B2111179
theorem B2225081 : Blo 1482061 2225081 := bstep (se 2 (by rfl) ⟨834405, by rfl⟩ : syracuseStep 2225081 = 1668811) B1668811
theorem B2225159 : Blo 1482061 2225159 := bstep (se 1 (by rfl) ⟨1668869, by rfl⟩ : syracuseStep 2225159 = 3337739) B3337739
theorem B2225195 : Blo 1482061 2225195 := bstep (se 1 (by rfl) ⟨1668896, by rfl⟩ : syracuseStep 2225195 = 3337793) B3337793
theorem B2503723 : Blo 1482061 2503723 := bstep (se 1 (by rfl) ⟨1877792, by rfl⟩ : syracuseStep 2503723 = 3755585) B3755585
theorem B2225225 : Blo 1482061 2225225 := bstep (se 2 (by rfl) ⟨834459, by rfl⟩ : syracuseStep 2225225 = 1668919) B1668919
theorem B2503865 : Blo 1482061 2503865 := bstep (se 2 (by rfl) ⟨938949, by rfl⟩ : syracuseStep 2503865 = 1877899) B1877899
theorem B2225339 : Blo 1482061 2225339 := bstep (se 1 (by rfl) ⟨1669004, by rfl⟩ : syracuseStep 2225339 = 3338009) B3338009
theorem B7509185 : Blo 1482061 7509185 := bstep (se 2 (by rfl) ⟨2815944, by rfl⟩ : syracuseStep 7509185 = 5631889) B5631889
theorem B2225399 : Blo 1482061 2225399 := bstep (se 1 (by rfl) ⟨1669049, by rfl⟩ : syracuseStep 2225399 = 3338099) B3338099
theorem B4224271 : Blo 1482061 4224271 := bstep (se 1 (by rfl) ⟨3168203, by rfl⟩ : syracuseStep 4224271 = 6336407) B6336407
theorem B4510991 : Blo 1482061 4510991 := bstep (se 1 (by rfl) ⟨3383243, by rfl⟩ : syracuseStep 4510991 = 6766487) B6766487
theorem B2225423 : Blo 1482061 2225423 := bstep (se 1 (by rfl) ⟨1669067, by rfl⟩ : syracuseStep 2225423 = 3338135) B3338135
theorem B8443187 : Blo 1482061 8443187 := bstep (se 1 (by rfl) ⟨6332390, by rfl⟩ : syracuseStep 8443187 = 12664781) B12664781
theorem B2225465 : Blo 1482061 2225465 := bstep (se 2 (by rfl) ⟨834549, by rfl⟩ : syracuseStep 2225465 = 1669099) B1669099
theorem B1668487 : Blo 1482061 1668487 := bstep (se 1 (by rfl) ⟨1251365, by rfl⟩ : syracuseStep 1668487 = 2502731) B2502731
theorem B2225543 : Blo 1482061 2225543 := bstep (se 1 (by rfl) ⟨1669157, by rfl⟩ : syracuseStep 2225543 = 3338315) B3338315
theorem B2225579 : Blo 1482061 2225579 := bstep (se 1 (by rfl) ⟨1669184, by rfl⟩ : syracuseStep 2225579 = 3338369) B3338369
theorem B18044345 : Blo 1482061 18044345 := bstep (se 2 (by rfl) ⟨6766629, by rfl⟩ : syracuseStep 18044345 = 13533259) B13533259
theorem B2225609 : Blo 1482061 2225609 := bstep (se 2 (by rfl) ⟨834603, by rfl⟩ : syracuseStep 2225609 = 1669207) B1669207
theorem B4224545 : Blo 1482061 4224545 := bstep (se 2 (by rfl) ⟨1584204, by rfl⟩ : syracuseStep 4224545 = 3168409) B3168409
theorem B1668667 : Blo 1482061 1668667 := bstep (se 1 (by rfl) ⟨1251500, by rfl⟩ : syracuseStep 1668667 = 2503001) B2503001
theorem B2225723 : Blo 1482061 2225723 := bstep (se 1 (by rfl) ⟨1669292, by rfl⟩ : syracuseStep 2225723 = 3338585) B3338585
theorem B6010487 : Blo 1482061 6010487 := bstep (se 1 (by rfl) ⟨4507865, by rfl⟩ : syracuseStep 6010487 = 9015731) B9015731
theorem B5346935 : Blo 1482061 5346935 := bstep (se 1 (by rfl) ⟨4010201, by rfl⟩ : syracuseStep 5346935 = 8020403) B8020403
theorem B2225783 : Blo 1482061 2225783 := bstep (se 1 (by rfl) ⟨1669337, by rfl⟩ : syracuseStep 2225783 = 3338675) B3338675
theorem B2225807 : Blo 1482061 2225807 := bstep (se 1 (by rfl) ⟨1669355, by rfl⟩ : syracuseStep 2225807 = 3338711) B3338711
theorem B2225849 : Blo 1482061 2225849 := bstep (se 2 (by rfl) ⟨834693, by rfl⟩ : syracuseStep 2225849 = 1669387) B1669387
theorem B2225927 : Blo 1482061 2225927 := bstep (se 1 (by rfl) ⟨1669445, by rfl⟩ : syracuseStep 2225927 = 3338891) B3338891
theorem B8017679 : Blo 1482061 8017679 := bstep (se 1 (by rfl) ⟨6013259, by rfl⟩ : syracuseStep 8017679 = 12026519) B12026519
theorem B2111275 : Blo 1482061 2111275 := bstep (se 1 (by rfl) ⟨1583456, by rfl⟩ : syracuseStep 2111275 = 3166913) B3166913
theorem B2225963 : Blo 1482061 2225963 := bstep (se 1 (by rfl) ⟨1669472, by rfl⟩ : syracuseStep 2225963 = 3338945) B3338945
theorem B2225993 : Blo 1482061 2225993 := bstep (se 2 (by rfl) ⟨834747, by rfl⟩ : syracuseStep 2225993 = 1669495) B1669495
theorem B7124939 : Blo 1482061 7124939 := bstep (se 1 (by rfl) ⟨5343704, by rfl⟩ : syracuseStep 7124939 = 10687409) B10687409
theorem B2111503 : Blo 1482061 2111503 := bstep (se 1 (by rfl) ⟨1583627, by rfl⟩ : syracuseStep 2111503 = 3167255) B3167255
theorem B1669135 : Blo 1482061 1669135 := bstep (se 1 (by rfl) ⟨1251851, by rfl⟩ : syracuseStep 1669135 = 2503703) B2503703
theorem B2816059 : Blo 1482061 2816059 := bstep (se 1 (by rfl) ⟨2112044, by rfl⟩ : syracuseStep 2816059 = 4224089) B4224089
theorem B162437237 : Blo 1482061 162437237 := bstep (se 5 (by rfl) ⟨7614245, by rfl⟩ : syracuseStep 162437237 = 15228491) B15228491
theorem B5142647 : Blo 1482061 5142647 := bstep (se 1 (by rfl) ⟨3856985, by rfl⟩ : syracuseStep 5142647 = 7713971) B7713971
theorem B5634305 : Blo 1482061 5634305 := bstep (se 2 (by rfl) ⟨2112864, by rfl⟩ : syracuseStep 5634305 = 4225729) B4225729
theorem B5634319 : Blo 1482061 5634319 := bstep (se 1 (by rfl) ⟨4225739, by rfl⟩ : syracuseStep 5634319 = 8451479) B8451479
theorem B14244113 : Blo 1482061 14244113 := bstep (se 2 (by rfl) ⟨5341542, by rfl⟩ : syracuseStep 14244113 = 10683085) B10683085
theorem B3168571 : Blo 1482061 3168571 := bstep (se 1 (by rfl) ⟨2376428, by rfl⟩ : syracuseStep 3168571 = 4752857) B4752857
theorem B7125383 : Blo 1482061 7125383 := bstep (se 1 (by rfl) ⟨5344037, by rfl⟩ : syracuseStep 7125383 = 10688075) B10688075
theorem B2111879 : Blo 1482061 2111879 := bstep (se 1 (by rfl) ⟨1583909, by rfl⟩ : syracuseStep 2111879 = 3167819) B3167819
theorem B7125401 : Blo 1482061 7125401 := bstep (se 2 (by rfl) ⟨2672025, by rfl⟩ : syracuseStep 7125401 = 5344051) B5344051
theorem B7510481 : Blo 1482061 7510481 := bstep (se 2 (by rfl) ⟨2816430, by rfl⟩ : syracuseStep 7510481 = 5632861) B5632861
theorem B4225547 : Blo 1482061 4225547 := bstep (se 1 (by rfl) ⟨3169160, by rfl⟩ : syracuseStep 4225547 = 6338321) B6338321
theorem B2816545 : Blo 1482061 2816545 := bstep (se 2 (by rfl) ⟨1056204, by rfl⟩ : syracuseStep 2816545 = 2112409) B2112409
theorem B4283027 : Blo 1482061 4283027 := bstep (se 1 (by rfl) ⟨3212270, by rfl⟩ : syracuseStep 4283027 = 6424541) B6424541
theorem B8444645 : Blo 1482061 8444645 := bstep (se 4 (by rfl) ⟨791685, by rfl⟩ : syracuseStep 8444645 = 1583371) B1583371
theorem B5004179 : Blo 1482061 5004179 := bstep (se 1 (by rfl) ⟨3753134, by rfl⟩ : syracuseStep 5004179 = 7506269) B7506269
theorem B3562393 : Blo 1482061 3562393 := bstep (se 2 (by rfl) ⟨1335897, by rfl⟩ : syracuseStep 3562393 = 2671795) B2671795
theorem B4225945 : Blo 1482061 4225945 := bstep (se 2 (by rfl) ⟨1584729, by rfl⟩ : syracuseStep 4225945 = 3169459) B3169459
theorem B4750397 : Blo 1482061 4750397 := bstep (se 3 (by rfl) ⟨890699, by rfl⟩ : syracuseStep 4750397 = 1781399) B1781399
theorem B4512829 : Blo 1482061 4512829 := bstep (se 3 (by rfl) ⟨846155, by rfl⟩ : syracuseStep 4512829 = 1692311) B1692311
theorem B2374775 : Blo 1482061 2374775 := bstep (se 1 (by rfl) ⟨1781081, by rfl⟩ : syracuseStep 2374775 = 3562163) B3562163
theorem B12033197 : Blo 1482061 12033197 := bstep (se 3 (by rfl) ⟨2256224, by rfl⟩ : syracuseStep 12033197 = 4512449) B4512449
theorem B12664097 : Blo 1482061 12664097 := bstep (se 2 (by rfl) ⟨4749036, by rfl⟩ : syracuseStep 12664097 = 9498073) B9498073
theorem B1482119 : Blo 1482061 1482119 := bstep (se 1 (by rfl) ⟨1111589, by rfl⟩ : syracuseStep 1482119 = 2223179) B2223179
theorem B1482127 : Blo 1482061 1482127 := bstep (se 1 (by rfl) ⟨1111595, by rfl⟩ : syracuseStep 1482127 = 2223191) B2223191
theorem B8445329 : Blo 1482061 8445329 := bstep (se 2 (by rfl) ⟨3166998, by rfl⟩ : syracuseStep 8445329 = 6333997) B6333997
theorem B1482171 : Blo 1482061 1482171 := bstep (se 1 (by rfl) ⟨1111628, by rfl⟩ : syracuseStep 1482171 = 2223257) B2223257
theorem B1482247 : Blo 1482061 1482247 := bstep (se 1 (by rfl) ⟨1111685, by rfl⟩ : syracuseStep 1482247 = 2223371) B2223371
theorem B1482255 : Blo 1482061 1482255 := bstep (se 1 (by rfl) ⟨1111691, by rfl⟩ : syracuseStep 1482255 = 2223383) B2223383
theorem B1482299 : Blo 1482061 1482299 := bstep (se 1 (by rfl) ⟨1111724, by rfl⟩ : syracuseStep 1482299 = 2223449) B2223449
theorem B2375287 : Blo 1482061 2375287 := bstep (se 1 (by rfl) ⟨1781465, by rfl⟩ : syracuseStep 2375287 = 3562931) B3562931
theorem B1482375 : Blo 1482061 1482375 := bstep (se 1 (by rfl) ⟨1111781, by rfl⟩ : syracuseStep 1482375 = 2223563) B2223563
theorem B1482383 : Blo 1482061 1482383 := bstep (se 1 (by rfl) ⟨1111787, by rfl⟩ : syracuseStep 1482383 = 2223575) B2223575
theorem B1482427 : Blo 1482061 1482427 := bstep (se 1 (by rfl) ⟨1111820, by rfl⟩ : syracuseStep 1482427 = 2223641) B2223641
theorem B5070593 : Blo 1482061 5070593 := bstep (se 2 (by rfl) ⟨1901472, by rfl⟩ : syracuseStep 5070593 = 3802945) B3802945
theorem B1482503 : Blo 1482061 1482503 := bstep (se 1 (by rfl) ⟨1111877, by rfl⟩ : syracuseStep 1482503 = 2223755) B2223755
theorem B1482511 : Blo 1482061 1482511 := bstep (se 1 (by rfl) ⟨1111883, by rfl⟩ : syracuseStep 1482511 = 2223767) B2223767
theorem B15425315 : Blo 1482061 15425315 := bstep (se 1 (by rfl) ⟨11568986, by rfl⟩ : syracuseStep 15425315 = 23137973) B23137973
theorem B1482555 : Blo 1482061 1482555 := bstep (se 1 (by rfl) ⟨1111916, by rfl⟩ : syracuseStep 1482555 = 2223833) B2223833
theorem B1482631 : Blo 1482061 1482631 := bstep (se 1 (by rfl) ⟨1111973, by rfl⟩ : syracuseStep 1482631 = 2223947) B2223947
theorem B1482639 : Blo 1482061 1482639 := bstep (se 1 (by rfl) ⟨1111979, by rfl⟩ : syracuseStep 1482639 = 2223959) B2223959
theorem B1875899 : Blo 1482061 1875899 := bstep (se 1 (by rfl) ⟨1406924, by rfl⟩ : syracuseStep 1875899 = 2813849) B2813849
theorem B1482683 : Blo 1482061 1482683 := bstep (se 1 (by rfl) ⟨1112012, by rfl⟩ : syracuseStep 1482683 = 2224025) B2224025
theorem B5005313 : Blo 1482061 5005313 := bstep (se 2 (by rfl) ⟨1876992, by rfl⟩ : syracuseStep 5005313 = 3753985) B3753985
theorem B1482791 : Blo 1482061 1482791 := bstep (se 1 (by rfl) ⟨1112093, by rfl⟩ : syracuseStep 1482791 = 2224187) B2224187
theorem B1482831 : Blo 1482061 1482831 := bstep (se 1 (by rfl) ⟨1112123, by rfl⟩ : syracuseStep 1482831 = 2224247) B2224247
theorem B1482847 : Blo 1482061 1482847 := bstep (se 1 (by rfl) ⟨1112135, by rfl⟩ : syracuseStep 1482847 = 2224271) B2224271
theorem B1482875 : Blo 1482061 1482875 := bstep (se 1 (by rfl) ⟨1112156, by rfl⟩ : syracuseStep 1482875 = 2224313) B2224313
theorem B1482927 : Blo 1482061 1482927 := bstep (se 1 (by rfl) ⟨1112195, by rfl⟩ : syracuseStep 1482927 = 2224391) B2224391
theorem B1482951 : Blo 1482061 1482951 := bstep (se 1 (by rfl) ⟨1112213, by rfl⟩ : syracuseStep 1482951 = 2224427) B2224427
theorem B1482971 : Blo 1482061 1482971 := bstep (se 1 (by rfl) ⟨1112228, by rfl⟩ : syracuseStep 1482971 = 2224457) B2224457
theorem B3752183 : Blo 1482061 3752183 := bstep (se 1 (by rfl) ⟨2814137, by rfl⟩ : syracuseStep 3752183 = 5628275) B5628275
theorem B21389579 : Blo 1482061 21389579 := bstep (se 1 (by rfl) ⟨16042184, by rfl⟩ : syracuseStep 21389579 = 32084369) B32084369
theorem B1483047 : Blo 1482061 1483047 := bstep (se 1 (by rfl) ⟨1112285, by rfl⟩ : syracuseStep 1483047 = 2224571) B2224571
theorem B13713725 : Blo 1482061 13713725 := bstep (se 3 (by rfl) ⟨2571323, by rfl⟩ : syracuseStep 13713725 = 5142647) B5142647
theorem B1483087 : Blo 1482061 1483087 := bstep (se 1 (by rfl) ⟨1112315, by rfl⟩ : syracuseStep 1483087 = 2224631) B2224631
theorem B1483103 : Blo 1482061 1483103 := bstep (se 1 (by rfl) ⟨1112327, by rfl⟩ : syracuseStep 1483103 = 2224655) B2224655
theorem B7512425 : Blo 1482061 7512425 := bstep (se 2 (by rfl) ⟨2817159, by rfl⟩ : syracuseStep 7512425 = 5634319) B5634319
theorem B1483131 : Blo 1482061 1483131 := bstep (se 1 (by rfl) ⟨1112348, by rfl⟩ : syracuseStep 1483131 = 2224697) B2224697
theorem B1483183 : Blo 1482061 1483183 := bstep (se 1 (by rfl) ⟨1112387, by rfl⟩ : syracuseStep 1483183 = 2224775) B2224775
theorem B1483207 : Blo 1482061 1483207 := bstep (se 1 (by rfl) ⟨1112405, by rfl⟩ : syracuseStep 1483207 = 2224811) B2224811
theorem B1483227 : Blo 1482061 1483227 := bstep (se 1 (by rfl) ⟨1112420, by rfl⟩ : syracuseStep 1483227 = 2224841) B2224841
theorem B1483303 : Blo 1482061 1483303 := bstep (se 1 (by rfl) ⟨1112477, by rfl⟩ : syracuseStep 1483303 = 2224955) B2224955
theorem B23142971 : Blo 1482061 23142971 := bstep (se 1 (by rfl) ⟨17357228, by rfl⟩ : syracuseStep 23142971 = 34714457) B34714457
theorem B1483343 : Blo 1482061 1483343 := bstep (se 1 (by rfl) ⟨1112507, by rfl⟩ : syracuseStep 1483343 = 2225015) B2225015
theorem B1483359 : Blo 1482061 1483359 := bstep (se 1 (by rfl) ⟨1112519, by rfl⟩ : syracuseStep 1483359 = 2225039) B2225039
theorem B1876603 : Blo 1482061 1876603 := bstep (se 1 (by rfl) ⟨1407452, by rfl⟩ : syracuseStep 1876603 = 2814905) B2814905
theorem B1483387 : Blo 1482061 1483387 := bstep (se 1 (by rfl) ⟨1112540, by rfl⟩ : syracuseStep 1483387 = 2225081) B2225081
theorem B9503405 : Blo 1482061 9503405 := bstep (se 3 (by rfl) ⟨1781888, by rfl⟩ : syracuseStep 9503405 = 3563777) B3563777
theorem B1483439 : Blo 1482061 1483439 := bstep (se 1 (by rfl) ⟨1112579, by rfl⟩ : syracuseStep 1483439 = 2225159) B2225159
theorem B1483463 : Blo 1482061 1483463 := bstep (se 1 (by rfl) ⟨1112597, by rfl⟩ : syracuseStep 1483463 = 2225195) B2225195
theorem B1483483 : Blo 1482061 1483483 := bstep (se 1 (by rfl) ⟨1112612, by rfl⟩ : syracuseStep 1483483 = 2225225) B2225225
theorem B1483559 : Blo 1482061 1483559 := bstep (se 1 (by rfl) ⟨1112669, by rfl⟩ : syracuseStep 1483559 = 2225339) B2225339
theorem B5006123 : Blo 1482061 5006123 := bstep (se 1 (by rfl) ⟨3754592, by rfl⟩ : syracuseStep 5006123 = 7509185) B7509185
theorem B3334985 : Blo 1482061 3334985 := bstep (se 2 (by rfl) ⟨1250619, by rfl⟩ : syracuseStep 3334985 = 2501239) B2501239
theorem B1483599 : Blo 1482061 1483599 := bstep (se 1 (by rfl) ⟨1112699, by rfl⟩ : syracuseStep 1483599 = 2225399) B2225399
theorem B3007327 : Blo 1482061 3007327 := bstep (se 1 (by rfl) ⟨2255495, by rfl⟩ : syracuseStep 3007327 = 4510991) B4510991
theorem B1483615 : Blo 1482061 1483615 := bstep (se 1 (by rfl) ⟨1112711, by rfl⟩ : syracuseStep 1483615 = 2225423) B2225423
theorem B5628791 : Blo 1482061 5628791 := bstep (se 1 (by rfl) ⟨4221593, by rfl⟩ : syracuseStep 5628791 = 8443187) B8443187
theorem B1483643 : Blo 1482061 1483643 := bstep (se 1 (by rfl) ⟨1112732, by rfl⟩ : syracuseStep 1483643 = 2225465) B2225465
theorem B1483695 : Blo 1482061 1483695 := bstep (se 1 (by rfl) ⟨1112771, by rfl⟩ : syracuseStep 1483695 = 2225543) B2225543
theorem B1483719 : Blo 1482061 1483719 := bstep (se 1 (by rfl) ⟨1112789, by rfl⟩ : syracuseStep 1483719 = 2225579) B2225579
theorem B1483739 : Blo 1482061 1483739 := bstep (se 1 (by rfl) ⟨1112804, by rfl⟩ : syracuseStep 1483739 = 2225609) B2225609
theorem B1483815 : Blo 1482061 1483815 := bstep (se 1 (by rfl) ⟨1112861, by rfl⟩ : syracuseStep 1483815 = 2225723) B2225723
theorem B5006393 : Blo 1482061 5006393 := bstep (se 2 (by rfl) ⟨1877397, by rfl⟩ : syracuseStep 5006393 = 3754795) B3754795
theorem B4006991 : Blo 1482061 4006991 := bstep (se 1 (by rfl) ⟨3005243, by rfl⟩ : syracuseStep 4006991 = 6010487) B6010487
theorem B3564623 : Blo 1482061 3564623 := bstep (se 1 (by rfl) ⟨2673467, by rfl⟩ : syracuseStep 3564623 = 5346935) B5346935
theorem B1483855 : Blo 1482061 1483855 := bstep (se 1 (by rfl) ⟨1112891, by rfl⟩ : syracuseStep 1483855 = 2225783) B2225783
theorem B1483871 : Blo 1482061 1483871 := bstep (se 1 (by rfl) ⟨1112903, by rfl⟩ : syracuseStep 1483871 = 2225807) B2225807
theorem B1483899 : Blo 1482061 1483899 := bstep (se 1 (by rfl) ⟨1112924, by rfl⟩ : syracuseStep 1483899 = 2225849) B2225849
theorem B1483951 : Blo 1482061 1483951 := bstep (se 1 (by rfl) ⟨1112963, by rfl⟩ : syracuseStep 1483951 = 2225927) B2225927
theorem B1483975 : Blo 1482061 1483975 := bstep (se 1 (by rfl) ⟨1112981, by rfl⟩ : syracuseStep 1483975 = 2225963) B2225963
theorem B1483995 : Blo 1482061 1483995 := bstep (se 1 (by rfl) ⟨1112996, by rfl⟩ : syracuseStep 1483995 = 2225993) B2225993
theorem B5006717 : Blo 1482061 5006717 := bstep (se 3 (by rfl) ⟨938759, by rfl⟩ : syracuseStep 5006717 = 1877519) B1877519
theorem B108291491 : Blo 1482061 108291491 := bstep (se 1 (by rfl) ⟨81218618, by rfl⟩ : syracuseStep 108291491 = 162437237) B162437237
theorem B9496075 : Blo 1482061 9496075 := bstep (se 1 (by rfl) ⟨7122056, by rfl⟩ : syracuseStep 9496075 = 14244113) B14244113
theorem B3008009 : Blo 1482061 3008009 := bstep (se 2 (by rfl) ⟨1128003, by rfl⟩ : syracuseStep 3008009 = 2256007) B2256007
theorem B3335777 : Blo 1482061 3335777 := bstep (se 2 (by rfl) ⟨1250916, by rfl⟩ : syracuseStep 3335777 = 2501833) B2501833
theorem B3753611 : Blo 1482061 3753611 := bstep (se 1 (by rfl) ⟨2815208, by rfl⟩ : syracuseStep 3753611 = 5630417) B5630417
theorem B5006987 : Blo 1482061 5006987 := bstep (se 1 (by rfl) ⟨3755240, by rfl⟩ : syracuseStep 5006987 = 7510481) B7510481
theorem B6260413 : Blo 1482061 6260413 := bstep (se 3 (by rfl) ⟨1173827, by rfl⟩ : syracuseStep 6260413 = 2347655) B2347655
theorem B19253051 : Blo 1482061 19253051 := bstep (se 1 (by rfl) ⟨14439788, by rfl⟩ : syracuseStep 19253051 = 28879577) B28879577
theorem B5629763 : Blo 1482061 5629763 := bstep (se 1 (by rfl) ⟨4222322, by rfl⟩ : syracuseStep 5629763 = 8444645) B8444645
theorem B3753823 : Blo 1482061 3753823 := bstep (se 1 (by rfl) ⟨2815367, by rfl⟩ : syracuseStep 3753823 = 5630735) B5630735
theorem B7505783 : Blo 1482061 7505783 := bstep (se 1 (by rfl) ⟨5629337, by rfl⟩ : syracuseStep 7505783 = 11258675) B11258675
theorem B3336119 : Blo 1482061 3336119 := bstep (se 1 (by rfl) ⟨2502089, by rfl⟩ : syracuseStep 3336119 = 5004179) B5004179
theorem B23128001 : Blo 1482061 23128001 := bstep (se 2 (by rfl) ⟨8673000, by rfl⟩ : syracuseStep 23128001 = 17346001) B17346001
theorem B1583183 : Blo 1482061 1583183 := bstep (se 1 (by rfl) ⟨1187387, by rfl⟩ : syracuseStep 1583183 = 2374775) B2374775
theorem B5343347 : Blo 1482061 5343347 := bstep (se 1 (by rfl) ⟨4007510, by rfl⟩ : syracuseStep 5343347 = 8015021) B8015021
theorem B8022131 : Blo 1482061 8022131 := bstep (se 1 (by rfl) ⟨6016598, by rfl⟩ : syracuseStep 8022131 = 12033197) B12033197
theorem B5630219 : Blo 1482061 5630219 := bstep (se 1 (by rfl) ⟨4222664, by rfl⟩ : syracuseStep 5630219 = 8445329) B8445329
theorem B3336713 : Blo 1482061 3336713 := bstep (se 2 (by rfl) ⟨1251267, by rfl⟩ : syracuseStep 3336713 = 2502535) B2502535
theorem B10283543 : Blo 1482061 10283543 := bstep (se 1 (by rfl) ⟨7712657, by rfl⟩ : syracuseStep 10283543 = 15425315) B15425315
theorem B7137817 : Blo 1482061 7137817 := bstep (se 2 (by rfl) ⟨2676681, by rfl⟩ : syracuseStep 7137817 = 5353363) B5353363
theorem B5007905 : Blo 1482061 5007905 := bstep (se 2 (by rfl) ⟨1877964, by rfl⟩ : syracuseStep 5007905 = 3755929) B3755929
theorem B42740405 : Blo 1482061 42740405 := bstep (se 5 (by rfl) ⟨2003456, by rfl⟩ : syracuseStep 42740405 = 4006913) B4006913
theorem B4221629 : Blo 1482061 4221629 := bstep (se 3 (by rfl) ⟨791555, by rfl⟩ : syracuseStep 4221629 = 1583111) B1583111
theorem B3754745 : Blo 1482061 3754745 := bstep (se 2 (by rfl) ⟨1408029, by rfl⟩ : syracuseStep 3754745 = 2816059) B2816059
theorem B5008121 : Blo 1482061 5008121 := bstep (se 2 (by rfl) ⟨1878045, by rfl⟩ : syracuseStep 5008121 = 3756091) B3756091
theorem B10693405 : Blo 1482061 10693405 := bstep (se 3 (by rfl) ⟨2005013, by rfl⟩ : syracuseStep 10693405 = 4010027) B4010027
theorem B3337055 : Blo 1482061 3337055 := bstep (se 1 (by rfl) ⟨2502791, by rfl⟩ : syracuseStep 3337055 = 5005583) B5005583
theorem B6097771 : Blo 1482061 6097771 := bstep (se 1 (by rfl) ⟨4573328, by rfl⟩ : syracuseStep 6097771 = 9146657) B9146657
theorem B3427255 : Blo 1482061 3427255 := bstep (se 1 (by rfl) ⟨2570441, by rfl⟩ : syracuseStep 3427255 = 5140883) B5140883
theorem B5630903 : Blo 1482061 5630903 := bstep (se 1 (by rfl) ⟨4223177, by rfl⟩ : syracuseStep 5630903 = 8446355) B8446355
theorem B32074679 : Blo 1482061 32074679 := bstep (se 1 (by rfl) ⟨24056009, by rfl⟩ : syracuseStep 32074679 = 48112019) B48112019
theorem B2501563 : Blo 1482061 2501563 := bstep (se 1 (by rfl) ⟨1876172, by rfl⟩ : syracuseStep 2501563 = 3752345) B3752345
theorem B112716785 : Blo 1482061 112716785 := bstep (se 2 (by rfl) ⟨42268794, by rfl⟩ : syracuseStep 112716785 = 84537589) B84537589
theorem B9022465 : Blo 1482061 9022465 := bstep (se 2 (by rfl) ⟨3383424, by rfl⟩ : syracuseStep 9022465 = 6766849) B6766849
theorem B5008391 : Blo 1482061 5008391 := bstep (se 1 (by rfl) ⟨3756293, by rfl⟩ : syracuseStep 5008391 = 7512587) B7512587
theorem B2223113 : Blo 1482061 2223113 := bstep (se 2 (by rfl) ⟨833667, by rfl⟩ : syracuseStep 2223113 = 1667335) B1667335
theorem B3337235 : Blo 1482061 3337235 := bstep (se 1 (by rfl) ⟨2502926, by rfl⟩ : syracuseStep 3337235 = 5005853) B5005853
theorem B2223143 : Blo 1482061 2223143 := bstep (se 1 (by rfl) ⟨1667357, by rfl⟩ : syracuseStep 2223143 = 3334715) B3334715
theorem B2501671 : Blo 1482061 2501671 := bstep (se 1 (by rfl) ⟨1876253, by rfl⟩ : syracuseStep 2501671 = 3752507) B3752507
theorem B5073977 : Blo 1482061 5073977 := bstep (se 2 (by rfl) ⟨1902741, by rfl⟩ : syracuseStep 5073977 = 3805483) B3805483
theorem B6016079 : Blo 1482061 6016079 := bstep (se 1 (by rfl) ⟨4512059, by rfl⟩ : syracuseStep 6016079 = 9024119) B9024119
theorem B5008499 : Blo 1482061 5008499 := bstep (se 1 (by rfl) ⟨3756374, by rfl⟩ : syracuseStep 5008499 = 7512749) B7512749
theorem B2223227 : Blo 1482061 2223227 := bstep (se 1 (by rfl) ⟨1667420, by rfl⟩ : syracuseStep 2223227 = 3334841) B3334841
theorem B8449271 : Blo 1482061 8449271 := bstep (se 1 (by rfl) ⟨6336953, by rfl⟩ : syracuseStep 8449271 = 12673907) B12673907
theorem B2223353 : Blo 1482061 2223353 := bstep (se 2 (by rfl) ⟨833757, by rfl⟩ : syracuseStep 2223353 = 1667515) B1667515
theorem B12668197 : Blo 1482061 12668197 := bstep (se 4 (by rfl) ⟨1187643, by rfl⟩ : syracuseStep 12668197 = 2375287) B2375287
theorem B19008857 : Blo 1482061 19008857 := bstep (se 2 (by rfl) ⟨7128321, by rfl⟩ : syracuseStep 19008857 = 14256643) B14256643
theorem B2223455 : Blo 1482061 2223455 := bstep (se 1 (by rfl) ⟨1667591, by rfl⟩ : syracuseStep 2223455 = 3335183) B3335183
theorem B3337577 : Blo 1482061 3337577 := bstep (se 2 (by rfl) ⟨1251591, by rfl⟩ : syracuseStep 3337577 = 2503183) B2503183
theorem B2223467 : Blo 1482061 2223467 := bstep (se 1 (by rfl) ⟨1667600, by rfl⟩ : syracuseStep 2223467 = 3335201) B3335201
theorem B2501995 : Blo 1482061 2501995 := bstep (se 1 (by rfl) ⟨1876496, by rfl⟩ : syracuseStep 2501995 = 3752993) B3752993
theorem B3755393 : Blo 1482061 3755393 := bstep (se 2 (by rfl) ⟨1408272, by rfl⟩ : syracuseStep 3755393 = 2816545) B2816545
theorem B1584559 : Blo 1482061 1584559 := bstep (se 1 (by rfl) ⟨1188419, by rfl⟩ : syracuseStep 1584559 = 2376839) B2376839
theorem B6335945 : Blo 1482061 6335945 := bstep (se 2 (by rfl) ⟨2375979, by rfl⟩ : syracuseStep 6335945 = 4751959) B4751959
theorem B2223695 : Blo 1482061 2223695 := bstep (se 1 (by rfl) ⟨1667771, by rfl⟩ : syracuseStep 2223695 = 3335543) B3335543
theorem B27061847 : Blo 1482061 27061847 := bstep (se 1 (by rfl) ⟨20296385, by rfl⟩ : syracuseStep 27061847 = 40592771) B40592771
theorem B12029563 : Blo 1482061 12029563 := bstep (se 1 (by rfl) ⟨9022172, by rfl⟩ : syracuseStep 12029563 = 18044345) B18044345
theorem B5705405 : Blo 1482061 5705405 := bstep (se 3 (by rfl) ⟨1069763, by rfl⟩ : syracuseStep 5705405 = 2139527) B2139527
theorem B5631677 : Blo 1482061 5631677 := bstep (se 3 (by rfl) ⟨1055939, by rfl⟩ : syracuseStep 5631677 = 2111879) B2111879
theorem B2223815 : Blo 1482061 2223815 := bstep (se 1 (by rfl) ⟨1667861, by rfl⟩ : syracuseStep 2223815 = 3335723) B3335723
theorem B5345119 : Blo 1482061 5345119 := bstep (se 1 (by rfl) ⟨4008839, by rfl⟩ : syracuseStep 5345119 = 8017679) B8017679
theorem B2223977 : Blo 1482061 2223977 := bstep (se 2 (by rfl) ⟨833991, by rfl⟩ : syracuseStep 2223977 = 1667983) B1667983
theorem B2813879 : Blo 1482061 2813879 := bstep (se 1 (by rfl) ⟨2110409, by rfl⟩ : syracuseStep 2813879 = 4220819) B4220819
theorem B2224055 : Blo 1482061 2224055 := bstep (se 1 (by rfl) ⟨1668041, by rfl⟩ : syracuseStep 2224055 = 3336083) B3336083
theorem B3338171 : Blo 1482061 3338171 := bstep (se 1 (by rfl) ⟨2503628, by rfl⟩ : syracuseStep 3338171 = 5007257) B5007257
theorem B2224091 : Blo 1482061 2224091 := bstep (se 1 (by rfl) ⟨1668068, by rfl⟩ : syracuseStep 2224091 = 3336137) B3336137
theorem B3338297 : Blo 1482061 3338297 := bstep (se 2 (by rfl) ⟨1251861, by rfl⟩ : syracuseStep 3338297 = 2503723) B2503723
theorem B2814031 : Blo 1482061 2814031 := bstep (se 1 (by rfl) ⟨2110523, by rfl⟩ : syracuseStep 2814031 = 4221047) B4221047
theorem B6017105 : Blo 1482061 6017105 := bstep (se 2 (by rfl) ⟨2256414, by rfl⟩ : syracuseStep 6017105 = 4512829) B4512829
theorem B3756203 : Blo 1482061 3756203 := bstep (se 1 (by rfl) ⟨2817152, by rfl⟩ : syracuseStep 3756203 = 5634305) B5634305
theorem B11260133 : Blo 1482061 11260133 := bstep (se 4 (by rfl) ⟨1055637, by rfl⟩ : syracuseStep 11260133 = 2111275) B2111275
theorem B5632361 : Blo 1482061 5632361 := bstep (se 2 (by rfl) ⟨2112135, by rfl⟩ : syracuseStep 5632361 = 4224271) B4224271
theorem B2503055 : Blo 1482061 2503055 := bstep (se 1 (by rfl) ⟨1877291, by rfl⟩ : syracuseStep 2503055 = 3754583) B3754583
theorem B3338639 : Blo 1482061 3338639 := bstep (se 1 (by rfl) ⟨2503979, by rfl⟩ : syracuseStep 3338639 = 5007959) B5007959
theorem B2224559 : Blo 1482061 2224559 := bstep (se 1 (by rfl) ⟨1668419, by rfl⟩ : syracuseStep 2224559 = 3336839) B3336839
theorem B2855351 : Blo 1482061 2855351 := bstep (se 1 (by rfl) ⟨2141513, by rfl⟩ : syracuseStep 2855351 = 4283027) B4283027
theorem B2224649 : Blo 1482061 2224649 := bstep (se 2 (by rfl) ⟨834243, by rfl⟩ : syracuseStep 2224649 = 1668487) B1668487
theorem B1667623 : Blo 1482061 1667623 := bstep (se 1 (by rfl) ⟨1250717, by rfl⟩ : syracuseStep 1667623 = 2501435) B2501435
theorem B2224679 : Blo 1482061 2224679 := bstep (se 1 (by rfl) ⟨1668509, by rfl⟩ : syracuseStep 2224679 = 3337019) B3337019
theorem B2224763 : Blo 1482061 2224763 := bstep (se 1 (by rfl) ⟨1668572, by rfl⟩ : syracuseStep 2224763 = 3337145) B3337145
theorem B2503291 : Blo 1482061 2503291 := bstep (se 1 (by rfl) ⟨1877468, by rfl⟩ : syracuseStep 2503291 = 3754937) B3754937
theorem B13521581 : Blo 1482061 13521581 := bstep (se 3 (by rfl) ⟨2535296, by rfl⟩ : syracuseStep 13521581 = 5070593) B5070593
theorem B3912391 : Blo 1482061 3912391 := bstep (se 1 (by rfl) ⟨2934293, by rfl⟩ : syracuseStep 3912391 = 5868587) B5868587
theorem B3166931 : Blo 1482061 3166931 := bstep (se 1 (by rfl) ⟨2375198, by rfl⟩ : syracuseStep 3166931 = 4750397) B4750397
theorem B3338963 : Blo 1482061 3338963 := bstep (se 1 (by rfl) ⟨2504222, by rfl⟩ : syracuseStep 3338963 = 5008445) B5008445
theorem B2224889 : Blo 1482061 2224889 := bstep (se 2 (by rfl) ⟨834333, by rfl⟩ : syracuseStep 2224889 = 1668667) B1668667
theorem B2224991 : Blo 1482061 2224991 := bstep (se 1 (by rfl) ⟨1668743, by rfl⟩ : syracuseStep 2224991 = 3337487) B3337487
theorem B2110313 : Blo 1482061 2110313 := bstep (se 2 (by rfl) ⟨791367, by rfl⟩ : syracuseStep 2110313 = 1582735) B1582735
theorem B8442731 : Blo 1482061 8442731 := bstep (se 1 (by rfl) ⟨6332048, by rfl⟩ : syracuseStep 8442731 = 12664097) B12664097
theorem B2225003 : Blo 1482061 2225003 := bstep (se 1 (by rfl) ⟨1668752, by rfl⟩ : syracuseStep 2225003 = 3337505) B3337505
theorem B68457473 : Blo 1482061 68457473 := bstep (se 2 (by rfl) ⟨25671552, by rfl⟩ : syracuseStep 68457473 = 51343105) B51343105
theorem B2225231 : Blo 1482061 2225231 := bstep (se 1 (by rfl) ⟨1668923, by rfl⟩ : syracuseStep 2225231 = 3337847) B3337847
theorem B21378167 : Blo 1482061 21378167 := bstep (se 1 (by rfl) ⟨16033625, by rfl⟩ : syracuseStep 21378167 = 32067251) B32067251
theorem B5002397 : Blo 1482061 5002397 := bstep (se 3 (by rfl) ⟨937949, by rfl⟩ : syracuseStep 5002397 = 1875899) B1875899
theorem B2225351 : Blo 1482061 2225351 := bstep (se 1 (by rfl) ⟨1669013, by rfl⟩ : syracuseStep 2225351 = 3338027) B3338027
theorem B11269367 : Blo 1482061 11269367 := bstep (se 1 (by rfl) ⟨8452025, by rfl⟩ : syracuseStep 11269367 = 16904051) B16904051
theorem B2815337 : Blo 1482061 2815337 := bstep (se 2 (by rfl) ⟨1055751, by rfl⟩ : syracuseStep 2815337 = 2111503) B2111503
theorem B2225513 : Blo 1482061 2225513 := bstep (se 2 (by rfl) ⟨834567, by rfl⟩ : syracuseStep 2225513 = 1669135) B1669135
theorem B24720785 : Blo 1482061 24720785 := bstep (se 2 (by rfl) ⟨9270294, by rfl⟩ : syracuseStep 24720785 = 18540589) B18540589
theorem B2225591 : Blo 1482061 2225591 := bstep (se 1 (by rfl) ⟨1669193, by rfl⟩ : syracuseStep 2225591 = 3338387) B3338387
theorem B2225627 : Blo 1482061 2225627 := bstep (se 1 (by rfl) ⟨1669220, by rfl⟩ : syracuseStep 2225627 = 3338441) B3338441
theorem B2504155 : Blo 1482061 2504155 := bstep (se 1 (by rfl) ⟨1878116, by rfl⟩ : syracuseStep 2504155 = 3756233) B3756233
theorem B13530635 : Blo 1482061 13530635 := bstep (se 1 (by rfl) ⟨10147976, by rfl⟩ : syracuseStep 13530635 = 20295953) B20295953
theorem B8353403 : Blo 1482061 8353403 := bstep (se 1 (by rfl) ⟨6265052, by rfl⟩ : syracuseStep 8353403 = 12530105) B12530105
theorem B18036371 : Blo 1482061 18036371 := bstep (se 1 (by rfl) ⟨13527278, by rfl⟩ : syracuseStep 18036371 = 27054557) B27054557
theorem B2537131 : Blo 1482061 2537131 := bstep (se 1 (by rfl) ⟨1902848, by rfl⟩ : syracuseStep 2537131 = 3805697) B3805697
theorem B5002937 : Blo 1482061 5002937 := bstep (se 2 (by rfl) ⟨1876101, by rfl⟩ : syracuseStep 5002937 = 3752203) B3752203
theorem B4224761 : Blo 1482061 4224761 := bstep (se 2 (by rfl) ⟨1584285, by rfl⟩ : syracuseStep 4224761 = 3168571) B3168571
theorem B3806969 : Blo 1482061 3806969 := bstep (se 2 (by rfl) ⟨1427613, by rfl⟩ : syracuseStep 3806969 = 2855227) B2855227
theorem B6338371 : Blo 1482061 6338371 := bstep (se 1 (by rfl) ⟨4753778, by rfl⟩ : syracuseStep 6338371 = 9507557) B9507557
theorem B8451935 : Blo 1482061 8451935 := bstep (se 1 (by rfl) ⟨6338951, by rfl⟩ : syracuseStep 8451935 = 12677903) B12677903
theorem B1669243 : Blo 1482061 1669243 := bstep (se 1 (by rfl) ⟨1251932, by rfl⟩ : syracuseStep 1669243 = 2503865) B2503865
theorem B5003531 : Blo 1482061 5003531 := bstep (se 1 (by rfl) ⟨3752648, by rfl⟩ : syracuseStep 5003531 = 7505297) B7505297
theorem B2816363 : Blo 1482061 2816363 := bstep (se 1 (by rfl) ⟨2112272, by rfl⟩ : syracuseStep 2816363 = 4224545) B4224545
theorem B6765065 : Blo 1482061 6765065 := bstep (se 2 (by rfl) ⟨2536899, by rfl⟩ : syracuseStep 6765065 = 5073799) B5073799
theorem B5003801 : Blo 1482061 5003801 := bstep (se 2 (by rfl) ⟨1876425, by rfl⟩ : syracuseStep 5003801 = 3752851) B3752851
theorem B4749857 : Blo 1482061 4749857 := bstep (se 2 (by rfl) ⟨1781196, by rfl⟩ : syracuseStep 4749857 = 3562393) B3562393
theorem B5634593 : Blo 1482061 5634593 := bstep (se 2 (by rfl) ⟨2112972, by rfl⟩ : syracuseStep 5634593 = 4225945) B4225945
theorem B4749959 : Blo 1482061 4749959 := bstep (se 1 (by rfl) ⟨3562469, by rfl⟩ : syracuseStep 4749959 = 7124939) B7124939
theorem B12024605 : Blo 1482061 12024605 := bstep (se 3 (by rfl) ⟨2254613, by rfl⟩ : syracuseStep 12024605 = 4509227) B4509227
theorem B2407241 : Blo 1482061 2407241 := bstep (se 2 (by rfl) ⟨902715, by rfl⟩ : syracuseStep 2407241 = 1805431) B1805431
theorem B4750255 : Blo 1482061 4750255 := bstep (se 1 (by rfl) ⟨3562691, by rfl⟩ : syracuseStep 4750255 = 7125383) B7125383
theorem B7510967 : Blo 1482061 7510967 := bstep (se 1 (by rfl) ⟨5633225, by rfl⟩ : syracuseStep 7510967 = 11266451) B11266451
theorem B4750267 : Blo 1482061 4750267 := bstep (se 1 (by rfl) ⟨3562700, by rfl⟩ : syracuseStep 4750267 = 7125401) B7125401
theorem B2817031 : Blo 1482061 2817031 := bstep (se 1 (by rfl) ⟨2112773, by rfl⟩ : syracuseStep 2817031 = 4225547) B4225547
theorem B7609423 : Blo 1482061 7609423 := bstep (se 1 (by rfl) ⟨5707067, by rfl⟩ : syracuseStep 7609423 = 11414135) B11414135
theorem B1482063 : Blo 1482061 1482063 := bstep (se 1 (by rfl) ⟨1111547, by rfl⟩ : syracuseStep 1482063 = 2223095) B2223095
theorem B1482079 : Blo 1482061 1482079 := bstep (se 1 (by rfl) ⟨1111559, by rfl⟩ : syracuseStep 1482079 = 2223119) B2223119
theorem B1482107 : Blo 1482061 1482107 := bstep (se 1 (by rfl) ⟨1111580, by rfl⟩ : syracuseStep 1482107 = 2223161) B2223161
theorem B1482159 : Blo 1482061 1482159 := bstep (se 1 (by rfl) ⟨1111619, by rfl⟩ : syracuseStep 1482159 = 2223239) B2223239
theorem B1482183 : Blo 1482061 1482183 := bstep (se 1 (by rfl) ⟨1111637, by rfl⟩ : syracuseStep 1482183 = 2223275) B2223275
theorem B1482203 : Blo 1482061 1482203 := bstep (se 1 (by rfl) ⟨1111652, by rfl⟩ : syracuseStep 1482203 = 2223305) B2223305
theorem B1482279 : Blo 1482061 1482279 := bstep (se 1 (by rfl) ⟨1111709, by rfl⟩ : syracuseStep 1482279 = 2223419) B2223419
theorem B1482319 : Blo 1482061 1482319 := bstep (se 1 (by rfl) ⟨1111739, by rfl⟩ : syracuseStep 1482319 = 2223479) B2223479
theorem B1482335 : Blo 1482061 1482335 := bstep (se 1 (by rfl) ⟨1111751, by rfl⟩ : syracuseStep 1482335 = 2223503) B2223503
theorem B5627515 : Blo 1482061 5627515 := bstep (se 1 (by rfl) ⟨4220636, by rfl⟩ : syracuseStep 5627515 = 8441273) B8441273
theorem B1482363 : Blo 1482061 1482363 := bstep (se 1 (by rfl) ⟨1111772, by rfl⟩ : syracuseStep 1482363 = 2223545) B2223545
theorem B5004935 : Blo 1482061 5004935 := bstep (se 1 (by rfl) ⟨3753701, by rfl⟩ : syracuseStep 5004935 = 7507403) B7507403
theorem B1482415 : Blo 1482061 1482415 := bstep (se 1 (by rfl) ⟨1111811, by rfl⟩ : syracuseStep 1482415 = 2223623) B2223623
theorem B5004989 : Blo 1482061 5004989 := bstep (se 3 (by rfl) ⟨938435, by rfl⟩ : syracuseStep 5004989 = 1876871) B1876871
theorem B1482439 : Blo 1482061 1482439 := bstep (se 1 (by rfl) ⟨1111829, by rfl⟩ : syracuseStep 1482439 = 2223659) B2223659
theorem B1482459 : Blo 1482061 1482459 := bstep (se 1 (by rfl) ⟨1111844, by rfl⟩ : syracuseStep 1482459 = 2223689) B2223689
theorem B1482535 : Blo 1482061 1482535 := bstep (se 1 (by rfl) ⟨1111901, by rfl⟩ : syracuseStep 1482535 = 2223803) B2223803
theorem B1482575 : Blo 1482061 1482575 := bstep (se 1 (by rfl) ⟨1111931, by rfl⟩ : syracuseStep 1482575 = 2223863) B2223863
theorem B6332255 : Blo 1482061 6332255 := bstep (se 1 (by rfl) ⟨4749191, by rfl⟩ : syracuseStep 6332255 = 9498383) B9498383
theorem B1482591 : Blo 1482061 1482591 := bstep (se 1 (by rfl) ⟨1111943, by rfl⟩ : syracuseStep 1482591 = 2223887) B2223887
theorem B5005151 : Blo 1482061 5005151 := bstep (se 1 (by rfl) ⟨3753863, by rfl⟩ : syracuseStep 5005151 = 7507727) B7507727
theorem B1482619 : Blo 1482061 1482619 := bstep (se 1 (by rfl) ⟨1111964, by rfl⟩ : syracuseStep 1482619 = 2223929) B2223929
theorem B1482671 : Blo 1482061 1482671 := bstep (se 1 (by rfl) ⟨1112003, by rfl⟩ : syracuseStep 1482671 = 2224007) B2224007
theorem B10141625 : Blo 1482061 10141625 := bstep (se 2 (by rfl) ⟨3803109, by rfl⟩ : syracuseStep 10141625 = 7606219) B7606219
theorem B1482695 : Blo 1482061 1482695 := bstep (se 1 (by rfl) ⟨1112021, by rfl⟩ : syracuseStep 1482695 = 2224043) B2224043
theorem B1482715 : Blo 1482061 1482715 := bstep (se 1 (by rfl) ⟨1112036, by rfl⟩ : syracuseStep 1482715 = 2224073) B2224073
theorem B3752041 : Blo 1482061 3752041 := bstep (se 2 (by rfl) ⟨1407015, by rfl⟩ : syracuseStep 3752041 = 2814031) B2814031
theorem B1483039 : Blo 1482061 1483039 := bstep (se 1 (by rfl) ⟨1112279, by rfl⟩ : syracuseStep 1483039 = 2224559) B2224559
theorem B1483099 : Blo 1482061 1483099 := bstep (se 1 (by rfl) ⟨1112324, by rfl⟩ : syracuseStep 1483099 = 2224649) B2224649
theorem B1483119 : Blo 1482061 1483119 := bstep (se 1 (by rfl) ⟨1112339, by rfl⟩ : syracuseStep 1483119 = 2224679) B2224679
theorem B1483175 : Blo 1482061 1483175 := bstep (se 1 (by rfl) ⟨1112381, by rfl⟩ : syracuseStep 1483175 = 2224763) B2224763
theorem B1483259 : Blo 1482061 1483259 := bstep (se 1 (by rfl) ⟨1112444, by rfl⟩ : syracuseStep 1483259 = 2224889) B2224889
theorem B152273429 : Blo 1482061 152273429 := bstep (se 6 (by rfl) ⟨3568908, by rfl⟩ : syracuseStep 152273429 = 7137817) B7137817
theorem B1483327 : Blo 1482061 1483327 := bstep (se 1 (by rfl) ⟨1112495, by rfl⟩ : syracuseStep 1483327 = 2224991) B2224991
theorem B5628487 : Blo 1482061 5628487 := bstep (se 1 (by rfl) ⟨4221365, by rfl⟩ : syracuseStep 5628487 = 8442731) B8442731
theorem B1483335 : Blo 1482061 1483335 := bstep (se 1 (by rfl) ⟨1112501, by rfl⟩ : syracuseStep 1483335 = 2225003) B2225003
theorem B3752527 : Blo 1482061 3752527 := bstep (se 1 (by rfl) ⟨2814395, by rfl⟩ : syracuseStep 3752527 = 5628791) B5628791
theorem B45638315 : Blo 1482061 45638315 := bstep (se 1 (by rfl) ⟨34228736, by rfl⟩ : syracuseStep 45638315 = 68457473) B68457473
theorem B2671327 : Blo 1482061 2671327 := bstep (se 1 (by rfl) ⟨2003495, by rfl⟩ : syracuseStep 2671327 = 4006991) B4006991
theorem B1483487 : Blo 1482061 1483487 := bstep (se 1 (by rfl) ⟨1112615, by rfl⟩ : syracuseStep 1483487 = 2225231) B2225231
theorem B2376415 : Blo 1482061 2376415 := bstep (se 1 (by rfl) ⟨1782311, by rfl⟩ : syracuseStep 2376415 = 3564623) B3564623
theorem B3334931 : Blo 1482061 3334931 := bstep (se 1 (by rfl) ⟨2501198, by rfl⟩ : syracuseStep 3334931 = 5002397) B5002397
theorem B1483567 : Blo 1482061 1483567 := bstep (se 1 (by rfl) ⟨1112675, by rfl⟩ : syracuseStep 1483567 = 2225351) B2225351
theorem B36569933 : Blo 1482061 36569933 := bstep (se 3 (by rfl) ⟨6856862, by rfl⟩ : syracuseStep 36569933 = 13713725) B13713725
theorem B7512911 : Blo 1482061 7512911 := bstep (se 1 (by rfl) ⟨5634683, by rfl⟩ : syracuseStep 7512911 = 11269367) B11269367
theorem B1483675 : Blo 1482061 1483675 := bstep (se 1 (by rfl) ⟨1112756, by rfl⟩ : syracuseStep 1483675 = 2225513) B2225513
theorem B1483727 : Blo 1482061 1483727 := bstep (se 1 (by rfl) ⟨1112795, by rfl⟩ : syracuseStep 1483727 = 2225591) B2225591
theorem B1483751 : Blo 1482061 1483751 := bstep (se 1 (by rfl) ⟨1112813, by rfl⟩ : syracuseStep 1483751 = 2225627) B2225627
theorem B9020423 : Blo 1482061 9020423 := bstep (se 1 (by rfl) ⟨6765317, by rfl⟩ : syracuseStep 9020423 = 13530635) B13530635
theorem B20866085 : Blo 1482061 20866085 := bstep (se 4 (by rfl) ⟨1956195, by rfl⟩ : syracuseStep 20866085 = 3912391) B3912391
theorem B3335291 : Blo 1482061 3335291 := bstep (se 1 (by rfl) ⟨2501468, by rfl⟩ : syracuseStep 3335291 = 5002937) B5002937
theorem B3753175 : Blo 1482061 3753175 := bstep (se 1 (by rfl) ⟨2814881, by rfl⟩ : syracuseStep 3753175 = 5629763) B5629763
theorem B6333673 : Blo 1482061 6333673 := bstep (se 2 (by rfl) ⟨2375127, by rfl⟩ : syracuseStep 6333673 = 4750255) B4750255
theorem B3335417 : Blo 1482061 3335417 := bstep (se 2 (by rfl) ⟨1250781, by rfl⟩ : syracuseStep 3335417 = 2501563) B2501563
theorem B6333689 : Blo 1482061 6333689 := bstep (se 2 (by rfl) ⟨2375133, by rfl⟩ : syracuseStep 6333689 = 4750267) B4750267
theorem B15418667 : Blo 1482061 15418667 := bstep (se 1 (by rfl) ⟨11564000, by rfl⟩ : syracuseStep 15418667 = 23128001) B23128001
theorem B3335561 : Blo 1482061 3335561 := bstep (se 2 (by rfl) ⟨1250835, by rfl⟩ : syracuseStep 3335561 = 2501671) B2501671
theorem B3335687 : Blo 1482061 3335687 := bstep (se 1 (by rfl) ⟨2501765, by rfl⟩ : syracuseStep 3335687 = 5003531) B5003531
theorem B3753479 : Blo 1482061 3753479 := bstep (se 1 (by rfl) ⟨2815109, by rfl⟩ : syracuseStep 3753479 = 5630219) B5630219
theorem B1877575 : Blo 1482061 1877575 := bstep (se 1 (by rfl) ⟨1408181, by rfl⟩ : syracuseStep 1877575 = 2816363) B2816363
theorem B3335867 : Blo 1482061 3335867 := bstep (se 1 (by rfl) ⟨2501900, by rfl⟩ : syracuseStep 3335867 = 5003801) B5003801
theorem B12666557 : Blo 1482061 12666557 := bstep (se 3 (by rfl) ⟨2374979, by rfl⟩ : syracuseStep 12666557 = 4749959) B4749959
theorem B28493603 : Blo 1482061 28493603 := bstep (se 1 (by rfl) ⟨21370202, by rfl⟩ : syracuseStep 28493603 = 42740405) B42740405
theorem B3335993 : Blo 1482061 3335993 := bstep (se 2 (by rfl) ⟨1250997, by rfl⟩ : syracuseStep 3335993 = 2501995) B2501995
theorem B3753935 : Blo 1482061 3753935 := bstep (se 1 (by rfl) ⟨2815451, by rfl⟩ : syracuseStep 3753935 = 5630903) B5630903
theorem B21383119 : Blo 1482061 21383119 := bstep (se 1 (by rfl) ⟨16037339, by rfl⟩ : syracuseStep 21383119 = 32074679) B32074679
theorem B5007311 : Blo 1482061 5007311 := bstep (se 1 (by rfl) ⟨3755483, by rfl⟩ : syracuseStep 5007311 = 7510967) B7510967
theorem B18278693 : Blo 1482061 18278693 := bstep (se 4 (by rfl) ⟨1713627, by rfl⟩ : syracuseStep 18278693 = 3427255) B3427255
theorem B18041231 : Blo 1482061 18041231 := bstep (se 1 (by rfl) ⟨13530923, by rfl⟩ : syracuseStep 18041231 = 27061847) B27061847
theorem B3336623 : Blo 1482061 3336623 := bstep (se 1 (by rfl) ⟨2502467, by rfl⟩ : syracuseStep 3336623 = 5004935) B5004935
theorem B3803603 : Blo 1482061 3803603 := bstep (se 1 (by rfl) ⟨2852702, by rfl⟩ : syracuseStep 3803603 = 5705405) B5705405
theorem B3336659 : Blo 1482061 3336659 := bstep (se 1 (by rfl) ⟨2502494, by rfl⟩ : syracuseStep 3336659 = 5004989) B5004989
theorem B3754451 : Blo 1482061 3754451 := bstep (se 1 (by rfl) ⟨2815838, by rfl⟩ : syracuseStep 3754451 = 5631677) B5631677
theorem B4221503 : Blo 1482061 4221503 := bstep (se 1 (by rfl) ⟨3166127, by rfl⟩ : syracuseStep 4221503 = 6332255) B6332255
theorem B3336767 : Blo 1482061 3336767 := bstep (se 1 (by rfl) ⟨2502575, by rfl⟩ : syracuseStep 3336767 = 5005151) B5005151
theorem B6761083 : Blo 1482061 6761083 := bstep (se 1 (by rfl) ⟨5070812, by rfl⟩ : syracuseStep 6761083 = 10141625) B10141625
theorem B3336875 : Blo 1482061 3336875 := bstep (se 1 (by rfl) ⟨2502656, by rfl⟩ : syracuseStep 3336875 = 5005313) B5005313
theorem B7506755 : Blo 1482061 7506755 := bstep (se 1 (by rfl) ⟨5630066, by rfl⟩ : syracuseStep 7506755 = 11260133) B11260133
theorem B2501455 : Blo 1482061 2501455 := bstep (se 1 (by rfl) ⟨1876091, by rfl⟩ : syracuseStep 2501455 = 3752183) B3752183
theorem B4221821 : Blo 1482061 4221821 := bstep (se 3 (by rfl) ⟨791591, by rfl⟩ : syracuseStep 4221821 = 1583183) B1583183
theorem B3754907 : Blo 1482061 3754907 := bstep (se 1 (by rfl) ⟨2816180, by rfl⟩ : syracuseStep 3754907 = 5632361) B5632361
theorem B5008283 : Blo 1482061 5008283 := bstep (se 1 (by rfl) ⟨3756212, by rfl⟩ : syracuseStep 5008283 = 7512425) B7512425
theorem B15428647 : Blo 1482061 15428647 := bstep (se 1 (by rfl) ⟨11571485, by rfl⟩ : syracuseStep 15428647 = 23142971) B23142971
theorem B9014387 : Blo 1482061 9014387 := bstep (se 1 (by rfl) ⟨6760790, by rfl⟩ : syracuseStep 9014387 = 13521581) B13521581
theorem B6335603 : Blo 1482061 6335603 := bstep (se 1 (by rfl) ⟨4751702, by rfl⟩ : syracuseStep 6335603 = 9503405) B9503405
theorem B3337415 : Blo 1482061 3337415 := bstep (se 1 (by rfl) ⟨2503061, by rfl⟩ : syracuseStep 3337415 = 5006123) B5006123
theorem B2223323 : Blo 1482061 2223323 := bstep (se 1 (by rfl) ⟨1667492, by rfl⟩ : syracuseStep 2223323 = 3334985) B3334985
theorem B3337595 : Blo 1482061 3337595 := bstep (se 1 (by rfl) ⟨2503196, by rfl⟩ : syracuseStep 3337595 = 5006393) B5006393
theorem B2223497 : Blo 1482061 2223497 := bstep (se 2 (by rfl) ⟨833811, by rfl⟩ : syracuseStep 2223497 = 1667623) B1667623
theorem B2502137 : Blo 1482061 2502137 := bstep (se 2 (by rfl) ⟨938301, by rfl⟩ : syracuseStep 2502137 = 1876603) B1876603
theorem B3337721 : Blo 1482061 3337721 := bstep (se 2 (by rfl) ⟨1251645, by rfl⟩ : syracuseStep 3337721 = 2503291) B2503291
theorem B3337811 : Blo 1482061 3337811 := bstep (se 1 (by rfl) ⟨2503358, by rfl⟩ : syracuseStep 3337811 = 5006717) B5006717
theorem B7507565 : Blo 1482061 7507565 := bstep (se 3 (by rfl) ⟨1407668, by rfl⟩ : syracuseStep 7507565 = 2815337) B2815337
theorem B14257873 : Blo 1482061 14257873 := bstep (se 2 (by rfl) ⟨5346702, by rfl⟩ : syracuseStep 14257873 = 10693405) B10693405
theorem B2223851 : Blo 1482061 2223851 := bstep (se 1 (by rfl) ⟨1667888, by rfl⟩ : syracuseStep 2223851 = 3335777) B3335777
theorem B2502407 : Blo 1482061 2502407 := bstep (se 1 (by rfl) ⟨1876805, by rfl⟩ : syracuseStep 2502407 = 3753611) B3753611
theorem B3337991 : Blo 1482061 3337991 := bstep (se 1 (by rfl) ⟨2503493, by rfl⟩ : syracuseStep 3337991 = 5006987) B5006987
theorem B4009769 : Blo 1482061 4009769 := bstep (se 2 (by rfl) ⟨1503663, by rfl⟩ : syracuseStep 4009769 = 3007327) B3007327
theorem B8130361 : Blo 1482061 8130361 := bstep (se 2 (by rfl) ⟨3048885, by rfl⟩ : syracuseStep 8130361 = 6097771) B6097771
theorem B7614269 : Blo 1482061 7614269 := bstep (se 3 (by rfl) ⟨1427675, by rfl⟩ : syracuseStep 7614269 = 2855351) B2855351
theorem B2224079 : Blo 1482061 2224079 := bstep (se 1 (by rfl) ⟨1668059, by rfl⟩ : syracuseStep 2224079 = 3336119) B3336119
theorem B12029953 : Blo 1482061 12029953 := bstep (se 2 (by rfl) ⟨4511232, by rfl⟩ : syracuseStep 12029953 = 9022465) B9022465
theorem B3756041 : Blo 1482061 3756041 := bstep (se 2 (by rfl) ⟨1408515, by rfl⟩ : syracuseStep 3756041 = 2817031) B2817031
theorem B10145897 : Blo 1482061 10145897 := bstep (se 2 (by rfl) ⟨3804711, by rfl⟩ : syracuseStep 10145897 = 7609423) B7609423
theorem B2224475 : Blo 1482061 2224475 := bstep (se 1 (by rfl) ⟨1668356, by rfl⟩ : syracuseStep 2224475 = 3336713) B3336713
theorem B4510043 : Blo 1482061 4510043 := bstep (se 1 (by rfl) ⟨3382532, by rfl⟩ : syracuseStep 4510043 = 6765065) B6765065
theorem B3166571 : Blo 1482061 3166571 := bstep (se 1 (by rfl) ⟨2374928, by rfl⟩ : syracuseStep 3166571 = 4749857) B4749857
theorem B3338603 : Blo 1482061 3338603 := bstep (se 1 (by rfl) ⟨2503952, by rfl⟩ : syracuseStep 3338603 = 5007905) B5007905
theorem B3756395 : Blo 1482061 3756395 := bstep (se 1 (by rfl) ⟨2817296, by rfl⟩ : syracuseStep 3756395 = 5634593) B5634593
theorem B2814419 : Blo 1482061 2814419 := bstep (se 1 (by rfl) ⟨2110814, by rfl⟩ : syracuseStep 2814419 = 4221629) B4221629
theorem B2503163 : Blo 1482061 2503163 := bstep (se 1 (by rfl) ⟨1877372, by rfl⟩ : syracuseStep 2503163 = 3754745) B3754745
theorem B3338747 : Blo 1482061 3338747 := bstep (se 1 (by rfl) ⟨2504060, by rfl⟩ : syracuseStep 3338747 = 5008121) B5008121
theorem B8016403 : Blo 1482061 8016403 := bstep (se 1 (by rfl) ⟨6012302, by rfl⟩ : syracuseStep 8016403 = 12024605) B12024605
theorem B2224703 : Blo 1482061 2224703 := bstep (se 1 (by rfl) ⟨1668527, by rfl⟩ : syracuseStep 2224703 = 3337055) B3337055
theorem B3338873 : Blo 1482061 3338873 := bstep (se 2 (by rfl) ⟨1252077, by rfl⟩ : syracuseStep 3338873 = 2504155) B2504155
theorem B3338927 : Blo 1482061 3338927 := bstep (se 1 (by rfl) ⟨2504195, by rfl⟩ : syracuseStep 3338927 = 5008391) B5008391
theorem B2224823 : Blo 1482061 2224823 := bstep (se 1 (by rfl) ⟨1668617, by rfl⟩ : syracuseStep 2224823 = 3337235) B3337235
theorem B12661433 : Blo 1482061 12661433 := bstep (se 2 (by rfl) ⟨4748037, by rfl⟩ : syracuseStep 12661433 = 9496075) B9496075
theorem B4010719 : Blo 1482061 4010719 := bstep (se 1 (by rfl) ⟨3008039, by rfl⟩ : syracuseStep 4010719 = 6016079) B6016079
theorem B3338999 : Blo 1482061 3338999 := bstep (se 1 (by rfl) ⟨2504249, by rfl⟩ : syracuseStep 3338999 = 5008499) B5008499
theorem B5632847 : Blo 1482061 5632847 := bstep (se 1 (by rfl) ⟨4224635, by rfl⟩ : syracuseStep 5632847 = 8449271) B8449271
theorem B2225051 : Blo 1482061 2225051 := bstep (se 1 (by rfl) ⟨1668788, by rfl⟩ : syracuseStep 2225051 = 3337577) B3337577
theorem B2503595 : Blo 1482061 2503595 := bstep (se 1 (by rfl) ⟨1877696, by rfl⟩ : syracuseStep 2503595 = 3755393) B3755393
theorem B4223963 : Blo 1482061 4223963 := bstep (se 1 (by rfl) ⟨3167972, by rfl⟩ : syracuseStep 4223963 = 6335945) B6335945
theorem B8451161 : Blo 1482061 8451161 := bstep (se 2 (by rfl) ⟨3169185, by rfl⟩ : syracuseStep 8451161 = 6338371) B6338371
theorem B2225447 : Blo 1482061 2225447 := bstep (se 1 (by rfl) ⟨1669085, by rfl⟩ : syracuseStep 2225447 = 3338171) B3338171
theorem B2225531 : Blo 1482061 2225531 := bstep (se 1 (by rfl) ⟨1669148, by rfl⟩ : syracuseStep 2225531 = 3338297) B3338297
theorem B4011403 : Blo 1482061 4011403 := bstep (se 1 (by rfl) ⟨3008552, by rfl⟩ : syracuseStep 4011403 = 6017105) B6017105
theorem B2504135 : Blo 1482061 2504135 := bstep (se 1 (by rfl) ⟨1878101, by rfl⟩ : syracuseStep 2504135 = 3756203) B3756203
theorem B2225657 : Blo 1482061 2225657 := bstep (se 2 (by rfl) ⟨834621, by rfl⟩ : syracuseStep 2225657 = 1669243) B1669243
theorem B14259719 : Blo 1482061 14259719 := bstep (se 1 (by rfl) ⟨10694789, by rfl⟩ : syracuseStep 14259719 = 21389579) B21389579
theorem B1668703 : Blo 1482061 1668703 := bstep (se 1 (by rfl) ⟨1251527, by rfl⟩ : syracuseStep 1668703 = 2503055) B2503055
theorem B2225759 : Blo 1482061 2225759 := bstep (se 1 (by rfl) ⟨1669319, by rfl⟩ : syracuseStep 2225759 = 3338639) B3338639
theorem B2111287 : Blo 1482061 2111287 := bstep (se 1 (by rfl) ⟨1583465, by rfl⟩ : syracuseStep 2111287 = 3166931) B3166931
theorem B2225975 : Blo 1482061 2225975 := bstep (se 1 (by rfl) ⟨1669481, by rfl⟩ : syracuseStep 2225975 = 3338963) B3338963
theorem B14252111 : Blo 1482061 14252111 := bstep (se 1 (by rfl) ⟨10689083, by rfl⟩ : syracuseStep 14252111 = 21378167) B21378167
theorem B16480523 : Blo 1482061 16480523 := bstep (se 1 (by rfl) ⟨12360392, by rfl⟩ : syracuseStep 16480523 = 24720785) B24720785
theorem B72194327 : Blo 1482061 72194327 := bstep (se 1 (by rfl) ⟨54145745, by rfl⟩ : syracuseStep 72194327 = 108291491) B108291491
theorem B2005339 : Blo 1482061 2005339 := bstep (se 1 (by rfl) ⟨1504004, by rfl⟩ : syracuseStep 2005339 = 3008009) B3008009
theorem B5568935 : Blo 1482061 5568935 := bstep (se 1 (by rfl) ⟨4176701, by rfl⟩ : syracuseStep 5568935 = 8353403) B8353403
theorem B12024247 : Blo 1482061 12024247 := bstep (se 1 (by rfl) ⟨9018185, by rfl⟩ : syracuseStep 12024247 = 18036371) B18036371
theorem B2816507 : Blo 1482061 2816507 := bstep (se 1 (by rfl) ⟨2112380, by rfl⟩ : syracuseStep 2816507 = 4224761) B4224761
theorem B12835367 : Blo 1482061 12835367 := bstep (se 1 (by rfl) ⟨9626525, by rfl⟩ : syracuseStep 12835367 = 19253051) B19253051
theorem B5634623 : Blo 1482061 5634623 := bstep (se 1 (by rfl) ⟨4225967, by rfl⟩ : syracuseStep 5634623 = 8451935) B8451935
theorem B5003855 : Blo 1482061 5003855 := bstep (se 1 (by rfl) ⟨3752891, by rfl⟩ : syracuseStep 5003855 = 7505783) B7505783
theorem B3562231 : Blo 1482061 3562231 := bstep (se 1 (by rfl) ⟨2671673, by rfl⟩ : syracuseStep 3562231 = 5343347) B5343347
theorem B5348087 : Blo 1482061 5348087 := bstep (se 1 (by rfl) ⟨4011065, by rfl⟩ : syracuseStep 5348087 = 8022131) B8022131
theorem B6855695 : Blo 1482061 6855695 := bstep (se 1 (by rfl) ⟨5141771, by rfl⟩ : syracuseStep 6855695 = 10283543) B10283543
theorem B16890929 : Blo 1482061 16890929 := bstep (se 2 (by rfl) ⟨6334098, by rfl⟩ : syracuseStep 16890929 = 12668197) B12668197
theorem B1604827 : Blo 1482061 1604827 := bstep (se 1 (by rfl) ⟨1203620, by rfl⟩ : syracuseStep 1604827 = 2407241) B2407241
theorem B2112745 : Blo 1482061 2112745 := bstep (se 2 (by rfl) ⟨792279, by rfl⟩ : syracuseStep 2112745 = 1584559) B1584559
theorem B75144523 : Blo 1482061 75144523 := bstep (se 1 (by rfl) ⟨56358392, by rfl⟩ : syracuseStep 75144523 = 112716785) B112716785
theorem B1482075 : Blo 1482061 1482075 := bstep (se 1 (by rfl) ⟨1111556, by rfl⟩ : syracuseStep 1482075 = 2223113) B2223113
theorem B1482095 : Blo 1482061 1482095 := bstep (se 1 (by rfl) ⟨1111571, by rfl⟩ : syracuseStep 1482095 = 2223143) B2223143
theorem B3382651 : Blo 1482061 3382651 := bstep (se 1 (by rfl) ⟨2536988, by rfl⟩ : syracuseStep 3382651 = 5073977) B5073977
theorem B1482151 : Blo 1482061 1482151 := bstep (se 1 (by rfl) ⟨1111613, by rfl⟩ : syracuseStep 1482151 = 2223227) B2223227
theorem B7503353 : Blo 1482061 7503353 := bstep (se 2 (by rfl) ⟨2813757, by rfl⟩ : syracuseStep 7503353 = 5627515) B5627515
theorem B16039417 : Blo 1482061 16039417 := bstep (se 2 (by rfl) ⟨6014781, by rfl⟩ : syracuseStep 16039417 = 12029563) B12029563
theorem B1482235 : Blo 1482061 1482235 := bstep (se 1 (by rfl) ⟨1111676, by rfl⟩ : syracuseStep 1482235 = 2223353) B2223353
theorem B3382841 : Blo 1482061 3382841 := bstep (se 2 (by rfl) ⟨1268565, by rfl⟩ : syracuseStep 3382841 = 2537131) B2537131
theorem B12672571 : Blo 1482061 12672571 := bstep (se 1 (by rfl) ⟨9504428, by rfl⟩ : syracuseStep 12672571 = 19008857) B19008857
theorem B1482303 : Blo 1482061 1482303 := bstep (se 1 (by rfl) ⟨1111727, by rfl⟩ : syracuseStep 1482303 = 2223455) B2223455
theorem B1482311 : Blo 1482061 1482311 := bstep (se 1 (by rfl) ⟨1111733, by rfl⟩ : syracuseStep 1482311 = 2223467) B2223467
theorem B8347217 : Blo 1482061 8347217 := bstep (se 2 (by rfl) ⟨3130206, by rfl⟩ : syracuseStep 8347217 = 6260413) B6260413
theorem B5627501 : Blo 1482061 5627501 := bstep (se 3 (by rfl) ⟨1055156, by rfl⟩ : syracuseStep 5627501 = 2110313) B2110313
theorem B1482463 : Blo 1482061 1482463 := bstep (se 1 (by rfl) ⟨1111847, by rfl⟩ : syracuseStep 1482463 = 2223695) B2223695
theorem B5005097 : Blo 1482061 5005097 := bstep (se 2 (by rfl) ⟨1876911, by rfl⟩ : syracuseStep 5005097 = 3753823) B3753823
theorem B7126825 : Blo 1482061 7126825 := bstep (se 2 (by rfl) ⟨2672559, by rfl⟩ : syracuseStep 7126825 = 5345119) B5345119
theorem B1482543 : Blo 1482061 1482543 := bstep (se 1 (by rfl) ⟨1111907, by rfl⟩ : syracuseStep 1482543 = 2223815) B2223815
theorem B7503677 : Blo 1482061 7503677 := bstep (se 3 (by rfl) ⟨1406939, by rfl⟩ : syracuseStep 7503677 = 2813879) B2813879
theorem B1482651 : Blo 1482061 1482651 := bstep (se 1 (by rfl) ⟨1111988, by rfl⟩ : syracuseStep 1482651 = 2223977) B2223977
theorem B40607669 : Blo 1482061 40607669 := bstep (se 5 (by rfl) ⟨1903484, by rfl⟩ : syracuseStep 40607669 = 3806969) B3806969
theorem B1482703 : Blo 1482061 1482703 := bstep (se 1 (by rfl) ⟨1112027, by rfl⟩ : syracuseStep 1482703 = 2224055) B2224055
theorem B1482727 : Blo 1482061 1482727 := bstep (se 1 (by rfl) ⟨1112045, by rfl⟩ : syracuseStep 1482727 = 2224091) B2224091
theorem B16039937 : Blo 1482061 16039937 := bstep (se 2 (by rfl) ⟨6014976, by rfl⟩ : syracuseStep 16039937 = 12029953) B12029953
theorem B1482983 : Blo 1482061 1482983 := bstep (se 1 (by rfl) ⟨1112237, by rfl⟩ : syracuseStep 1482983 = 2224475) B2224475
theorem B3006695 : Blo 1482061 3006695 := bstep (se 1 (by rfl) ⟨2255021, by rfl⟩ : syracuseStep 3006695 = 4510043) B4510043
theorem B1876279 : Blo 1482061 1876279 := bstep (se 1 (by rfl) ⟨1407209, by rfl⟩ : syracuseStep 1876279 = 2814419) B2814419
theorem B101515619 : Blo 1482061 101515619 := bstep (se 1 (by rfl) ⟨76136714, by rfl⟩ : syracuseStep 101515619 = 152273429) B152273429
theorem B1483135 : Blo 1482061 1483135 := bstep (se 1 (by rfl) ⟨1112351, by rfl⟩ : syracuseStep 1483135 = 2224703) B2224703
theorem B30425543 : Blo 1482061 30425543 := bstep (se 1 (by rfl) ⟨22819157, by rfl⟩ : syracuseStep 30425543 = 45638315) B45638315
theorem B1483215 : Blo 1482061 1483215 := bstep (se 1 (by rfl) ⟨1112411, by rfl⟩ : syracuseStep 1483215 = 2224823) B2224823
theorem B24379955 : Blo 1482061 24379955 := bstep (se 1 (by rfl) ⟨18284966, by rfl⟩ : syracuseStep 24379955 = 36569933) B36569933
theorem B16032329 : Blo 1482061 16032329 := bstep (se 2 (by rfl) ⟨6012123, by rfl⟩ : syracuseStep 16032329 = 12024247) B12024247
theorem B1483367 : Blo 1482061 1483367 := bstep (se 1 (by rfl) ⟨1112525, by rfl⟩ : syracuseStep 1483367 = 2225051) B2225051
theorem B6013615 : Blo 1482061 6013615 := bstep (se 1 (by rfl) ⟨4510211, by rfl⟩ : syracuseStep 6013615 = 9020423) B9020423
theorem B13910723 : Blo 1482061 13910723 := bstep (se 1 (by rfl) ⟨10433042, by rfl⟩ : syracuseStep 13910723 = 20866085) B20866085
theorem B7504649 : Blo 1482061 7504649 := bstep (se 2 (by rfl) ⟨2814243, by rfl⟩ : syracuseStep 7504649 = 5628487) B5628487
theorem B1483631 : Blo 1482061 1483631 := bstep (se 1 (by rfl) ⟨1112723, by rfl⟩ : syracuseStep 1483631 = 2225447) B2225447
theorem B1483687 : Blo 1482061 1483687 := bstep (se 1 (by rfl) ⟨1112765, by rfl⟩ : syracuseStep 1483687 = 2225531) B2225531
theorem B1483771 : Blo 1482061 1483771 := bstep (se 1 (by rfl) ⟨1112828, by rfl⟩ : syracuseStep 1483771 = 2225657) B2225657
theorem B1483839 : Blo 1482061 1483839 := bstep (se 1 (by rfl) ⟨1112879, by rfl⟩ : syracuseStep 1483839 = 2225759) B2225759
theorem B3335273 : Blo 1482061 3335273 := bstep (se 2 (by rfl) ⟨1250727, by rfl⟩ : syracuseStep 3335273 = 2501455) B2501455
theorem B1483983 : Blo 1482061 1483983 := bstep (se 1 (by rfl) ⟨1112987, by rfl⟩ : syracuseStep 1483983 = 2225975) B2225975
theorem B10142941 : Blo 1482061 10142941 := bstep (se 3 (by rfl) ⟨1901801, by rfl⟩ : syracuseStep 10142941 = 3803603) B3803603
theorem B9020909 : Blo 1482061 9020909 := bstep (se 3 (by rfl) ⟨1691420, by rfl⟩ : syracuseStep 9020909 = 3382841) B3382841
theorem B10987015 : Blo 1482061 10987015 := bstep (se 1 (by rfl) ⟨8240261, by rfl⟩ : syracuseStep 10987015 = 16480523) B16480523
theorem B48129551 : Blo 1482061 48129551 := bstep (se 1 (by rfl) ⟨36097163, by rfl⟩ : syracuseStep 48129551 = 72194327) B72194327
theorem B22259245 : Blo 1482061 22259245 := bstep (se 3 (by rfl) ⟨4173608, by rfl⟩ : syracuseStep 22259245 = 8347217) B8347217
theorem B12027487 : Blo 1482061 12027487 := bstep (se 1 (by rfl) ⟨9020615, by rfl⟩ : syracuseStep 12027487 = 18041231) B18041231
theorem B2139769 : Blo 1482061 2139769 := bstep (se 2 (by rfl) ⟨802413, by rfl⟩ : syracuseStep 2139769 = 1604827) B1604827
theorem B1877671 : Blo 1482061 1877671 := bstep (se 1 (by rfl) ⟨1408253, by rfl⟩ : syracuseStep 1877671 = 2816507) B2816507
theorem B3335903 : Blo 1482061 3335903 := bstep (se 1 (by rfl) ⟨2501927, by rfl⟩ : syracuseStep 3335903 = 5003855) B5003855
theorem B59401973 : Blo 1482061 59401973 := bstep (se 5 (by rfl) ⟨2784467, by rfl⟩ : syracuseStep 59401973 = 5568935) B5568935
theorem B3565391 : Blo 1482061 3565391 := bstep (se 1 (by rfl) ⟨2674043, by rfl⟩ : syracuseStep 3565391 = 5348087) B5348087
theorem B18040805 : Blo 1482061 18040805 := bstep (se 4 (by rfl) ⟨1691325, by rfl⟩ : syracuseStep 18040805 = 3382651) B3382651
theorem B11258189 : Blo 1482061 11258189 := bstep (se 3 (by rfl) ⟨2110910, by rfl⟩ : syracuseStep 11258189 = 4221821) B4221821
theorem B10840481 : Blo 1482061 10840481 := bstep (se 2 (by rfl) ⟨4065180, by rfl⟩ : syracuseStep 10840481 = 8130361) B8130361
theorem B3336731 : Blo 1482061 3336731 := bstep (se 1 (by rfl) ⟨2502548, by rfl⟩ : syracuseStep 3336731 = 5005097) B5005097
theorem B2673179 : Blo 1482061 2673179 := bstep (se 1 (by rfl) ⟨2004884, by rfl⟩ : syracuseStep 2673179 = 4009769) B4009769
theorem B28510825 : Blo 1482061 28510825 := bstep (se 2 (by rfl) ⟨10691559, by rfl⟩ : syracuseStep 28510825 = 21383119) B21383119
theorem B24038365 : Blo 1482061 24038365 := bstep (se 3 (by rfl) ⟨4507193, by rfl⟩ : syracuseStep 24038365 = 9014387) B9014387
theorem B2673785 : Blo 1482061 2673785 := bstep (se 2 (by rfl) ⟨1002669, by rfl⟩ : syracuseStep 2673785 = 2005339) B2005339
theorem B8440955 : Blo 1482061 8440955 := bstep (se 1 (by rfl) ⟨6330716, by rfl⟩ : syracuseStep 8440955 = 12661433) B12661433
theorem B2223287 : Blo 1482061 2223287 := bstep (se 1 (by rfl) ⟨1667465, by rfl⟩ : syracuseStep 2223287 = 3334931) B3334931
theorem B3755231 : Blo 1482061 3755231 := bstep (se 1 (by rfl) ⟨2816423, by rfl⟩ : syracuseStep 3755231 = 5632847) B5632847
theorem B5008607 : Blo 1482061 5008607 := bstep (se 1 (by rfl) ⟨3756455, by rfl⟩ : syracuseStep 5008607 = 7512911) B7512911
theorem B2223527 : Blo 1482061 2223527 := bstep (se 1 (by rfl) ⟨1667645, by rfl⟩ : syracuseStep 2223527 = 3335291) B3335291
theorem B9014777 : Blo 1482061 9014777 := bstep (se 2 (by rfl) ⟨3380541, by rfl⟩ : syracuseStep 9014777 = 6761083) B6761083
theorem B2223611 : Blo 1482061 2223611 := bstep (se 1 (by rfl) ⟨1667708, by rfl⟩ : syracuseStep 2223611 = 3335417) B3335417
theorem B4222459 : Blo 1482061 4222459 := bstep (se 1 (by rfl) ⟨3166844, by rfl⟩ : syracuseStep 4222459 = 6333689) B6333689
theorem B2223707 : Blo 1482061 2223707 := bstep (se 1 (by rfl) ⟨1667780, by rfl⟩ : syracuseStep 2223707 = 3335561) B3335561
theorem B2223791 : Blo 1482061 2223791 := bstep (se 1 (by rfl) ⟨1667843, by rfl⟩ : syracuseStep 2223791 = 3335687) B3335687
theorem B2502319 : Blo 1482061 2502319 := bstep (se 1 (by rfl) ⟨1876739, by rfl⟩ : syracuseStep 2502319 = 3753479) B3753479
theorem B9506479 : Blo 1482061 9506479 := bstep (se 1 (by rfl) ⟨7129859, by rfl⟩ : syracuseStep 9506479 = 14259719) B14259719
theorem B2223911 : Blo 1482061 2223911 := bstep (se 1 (by rfl) ⟨1667933, by rfl⟩ : syracuseStep 2223911 = 3335867) B3335867
theorem B2223995 : Blo 1482061 2223995 := bstep (se 1 (by rfl) ⟨1667996, by rfl⟩ : syracuseStep 2223995 = 3335993) B3335993
theorem B2502623 : Blo 1482061 2502623 := bstep (se 1 (by rfl) ⟨1876967, by rfl⟩ : syracuseStep 2502623 = 3753935) B3753935
theorem B3338207 : Blo 1482061 3338207 := bstep (se 1 (by rfl) ⟨2503655, by rfl⟩ : syracuseStep 3338207 = 5007311) B5007311
theorem B12185795 : Blo 1482061 12185795 := bstep (se 1 (by rfl) ⟨9139346, by rfl⟩ : syracuseStep 12185795 = 18278693) B18278693
theorem B2224415 : Blo 1482061 2224415 := bstep (se 1 (by rfl) ⟨1668311, by rfl⟩ : syracuseStep 2224415 = 3336623) B3336623
theorem B2224439 : Blo 1482061 2224439 := bstep (se 1 (by rfl) ⟨1668329, by rfl⟩ : syracuseStep 2224439 = 3336659) B3336659
theorem B2502967 : Blo 1482061 2502967 := bstep (se 1 (by rfl) ⟨1877225, by rfl⟩ : syracuseStep 2502967 = 3754451) B3754451
theorem B8556911 : Blo 1482061 8556911 := bstep (se 1 (by rfl) ⟨6417683, by rfl⟩ : syracuseStep 8556911 = 12835367) B12835367
theorem B2814335 : Blo 1482061 2814335 := bstep (se 1 (by rfl) ⟨2110751, by rfl⟩ : syracuseStep 2814335 = 4221503) B4221503
theorem B2224511 : Blo 1482061 2224511 := bstep (se 1 (by rfl) ⟨1668383, by rfl⟩ : syracuseStep 2224511 = 3336767) B3336767
theorem B3756415 : Blo 1482061 3756415 := bstep (se 1 (by rfl) ⟨2817311, by rfl⟩ : syracuseStep 3756415 = 5634623) B5634623
theorem B100192697 : Blo 1482061 100192697 := bstep (se 2 (by rfl) ⟨37572261, by rfl⟩ : syracuseStep 100192697 = 75144523) B75144523
theorem B2224583 : Blo 1482061 2224583 := bstep (se 1 (by rfl) ⟨1668437, by rfl⟩ : syracuseStep 2224583 = 3336875) B3336875
theorem B2503271 : Blo 1482061 2503271 := bstep (se 1 (by rfl) ⟨1877453, by rfl⟩ : syracuseStep 2503271 = 3754907) B3754907
theorem B3338855 : Blo 1482061 3338855 := bstep (se 1 (by rfl) ⟨2504141, by rfl⟩ : syracuseStep 3338855 = 5008283) B5008283
theorem B21385889 : Blo 1482061 21385889 := bstep (se 2 (by rfl) ⟨8019708, by rfl⟩ : syracuseStep 21385889 = 16039417) B16039417
theorem B11260619 : Blo 1482061 11260619 := bstep (se 1 (by rfl) ⟨8445464, by rfl⟩ : syracuseStep 11260619 = 16890929) B16890929
theorem B4223735 : Blo 1482061 4223735 := bstep (se 1 (by rfl) ⟨3167801, by rfl⟩ : syracuseStep 4223735 = 6335603) B6335603
theorem B16896761 : Blo 1482061 16896761 := bstep (se 2 (by rfl) ⟨6336285, by rfl⟩ : syracuseStep 16896761 = 12672571) B12672571
theorem B2503433 : Blo 1482061 2503433 := bstep (se 2 (by rfl) ⟨938787, by rfl⟩ : syracuseStep 2503433 = 1877575) B1877575
theorem B2224937 : Blo 1482061 2224937 := bstep (se 2 (by rfl) ⟨834351, by rfl⟩ : syracuseStep 2224937 = 1668703) B1668703
theorem B2224943 : Blo 1482061 2224943 := bstep (se 1 (by rfl) ⟨1668707, by rfl⟩ : syracuseStep 2224943 = 3337415) B3337415
theorem B2225063 : Blo 1482061 2225063 := bstep (se 1 (by rfl) ⟨1668797, by rfl⟩ : syracuseStep 2225063 = 3337595) B3337595
theorem B19010497 : Blo 1482061 19010497 := bstep (se 2 (by rfl) ⟨7128936, by rfl⟩ : syracuseStep 19010497 = 14257873) B14257873
theorem B5002235 : Blo 1482061 5002235 := bstep (se 1 (by rfl) ⟨3751676, by rfl⟩ : syracuseStep 5002235 = 7503353) B7503353
theorem B1668091 : Blo 1482061 1668091 := bstep (se 1 (by rfl) ⟨1251068, by rfl⟩ : syracuseStep 1668091 = 2502137) B2502137
theorem B2225147 : Blo 1482061 2225147 := bstep (se 1 (by rfl) ⟨1668860, by rfl⟩ : syracuseStep 2225147 = 3337721) B3337721
theorem B2225207 : Blo 1482061 2225207 := bstep (se 1 (by rfl) ⟨1668905, by rfl⟩ : syracuseStep 2225207 = 3337811) B3337811
theorem B2815049 : Blo 1482061 2815049 := bstep (se 2 (by rfl) ⟨1055643, by rfl⟩ : syracuseStep 2815049 = 2111287) B2111287
theorem B1668271 : Blo 1482061 1668271 := bstep (se 1 (by rfl) ⟨1251203, by rfl⟩ : syracuseStep 1668271 = 2502407) B2502407
theorem B2225327 : Blo 1482061 2225327 := bstep (se 1 (by rfl) ⟨1668995, by rfl⟩ : syracuseStep 2225327 = 3337991) B3337991
theorem B5002451 : Blo 1482061 5002451 := bstep (se 1 (by rfl) ⟨3751838, by rfl⟩ : syracuseStep 5002451 = 7503677) B7503677
theorem B5076179 : Blo 1482061 5076179 := bstep (se 1 (by rfl) ⟨3807134, by rfl⟩ : syracuseStep 5076179 = 7614269) B7614269
theorem B27071779 : Blo 1482061 27071779 := bstep (se 1 (by rfl) ⟨20303834, by rfl⟩ : syracuseStep 27071779 = 40607669) B40607669
theorem B2504027 : Blo 1482061 2504027 := bstep (se 1 (by rfl) ⟨1878020, by rfl⟩ : syracuseStep 2504027 = 3756041) B3756041
theorem B6763931 : Blo 1482061 6763931 := bstep (se 1 (by rfl) ⟨5072948, by rfl⟩ : syracuseStep 6763931 = 10145897) B10145897
theorem B5002721 : Blo 1482061 5002721 := bstep (se 2 (by rfl) ⟨1876020, by rfl⟩ : syracuseStep 5002721 = 3752041) B3752041
theorem B82286117 : Blo 1482061 82286117 := bstep (se 4 (by rfl) ⟨7714323, by rfl⟩ : syracuseStep 82286117 = 15428647) B15428647
theorem B2225735 : Blo 1482061 2225735 := bstep (se 1 (by rfl) ⟨1669301, by rfl⟩ : syracuseStep 2225735 = 3338603) B3338603
theorem B2504263 : Blo 1482061 2504263 := bstep (se 1 (by rfl) ⟨1878197, by rfl⟩ : syracuseStep 2504263 = 3756395) B3756395
theorem B1668775 : Blo 1482061 1668775 := bstep (se 1 (by rfl) ⟨1251581, by rfl⟩ : syracuseStep 1668775 = 2503163) B2503163
theorem B2225831 : Blo 1482061 2225831 := bstep (se 1 (by rfl) ⟨1669373, by rfl⟩ : syracuseStep 2225831 = 3338747) B3338747
theorem B2225915 : Blo 1482061 2225915 := bstep (se 1 (by rfl) ⟨1669436, by rfl⟩ : syracuseStep 2225915 = 3338873) B3338873
theorem B2225951 : Blo 1482061 2225951 := bstep (se 1 (by rfl) ⟨1669463, by rfl⟩ : syracuseStep 2225951 = 3338927) B3338927
theorem B2225999 : Blo 1482061 2225999 := bstep (se 1 (by rfl) ⟨1669499, by rfl⟩ : syracuseStep 2225999 = 3338999) B3338999
theorem B1669063 : Blo 1482061 1669063 := bstep (se 1 (by rfl) ⟨1251797, by rfl⟩ : syracuseStep 1669063 = 2503595) B2503595
theorem B2815975 : Blo 1482061 2815975 := bstep (se 1 (by rfl) ⟨2111981, by rfl⟩ : syracuseStep 2815975 = 4223963) B4223963
theorem B10688537 : Blo 1482061 10688537 := bstep (se 2 (by rfl) ⟨4008201, by rfl⟩ : syracuseStep 10688537 = 8016403) B8016403
theorem B5634107 : Blo 1482061 5634107 := bstep (se 1 (by rfl) ⟨4225580, by rfl⟩ : syracuseStep 5634107 = 8451161) B8451161
theorem B5003369 : Blo 1482061 5003369 := bstep (se 2 (by rfl) ⟨1876263, by rfl⟩ : syracuseStep 5003369 = 3752527) B3752527
theorem B10279111 : Blo 1482061 10279111 := bstep (se 1 (by rfl) ⟨7709333, by rfl⟩ : syracuseStep 10279111 = 15418667) B15418667
theorem B8444189 : Blo 1482061 8444189 := bstep (se 3 (by rfl) ⟨1583285, by rfl⟩ : syracuseStep 8444189 = 3166571) B3166571
theorem B3561769 : Blo 1482061 3561769 := bstep (se 2 (by rfl) ⟨1335663, by rfl⟩ : syracuseStep 3561769 = 2671327) B2671327
theorem B3168553 : Blo 1482061 3168553 := bstep (se 2 (by rfl) ⟨1188207, by rfl⟩ : syracuseStep 3168553 = 2376415) B2376415
theorem B5347625 : Blo 1482061 5347625 := bstep (se 2 (by rfl) ⟨2005359, by rfl⟩ : syracuseStep 5347625 = 4010719) B4010719
theorem B1669423 : Blo 1482061 1669423 := bstep (se 1 (by rfl) ⟨1252067, by rfl⟩ : syracuseStep 1669423 = 2504135) B2504135
theorem B4749641 : Blo 1482061 4749641 := bstep (se 2 (by rfl) ⟨1781115, by rfl⟩ : syracuseStep 4749641 = 3562231) B3562231
theorem B8444371 : Blo 1482061 8444371 := bstep (se 1 (by rfl) ⟨6333278, by rfl⟩ : syracuseStep 8444371 = 12666557) B12666557
theorem B18995735 : Blo 1482061 18995735 := bstep (se 1 (by rfl) ⟨14246801, by rfl⟩ : syracuseStep 18995735 = 28493603) B28493603
theorem B9501407 : Blo 1482061 9501407 := bstep (se 1 (by rfl) ⟨7126055, by rfl⟩ : syracuseStep 9501407 = 14252111) B14252111
theorem B5004233 : Blo 1482061 5004233 := bstep (se 2 (by rfl) ⟨1876587, by rfl⟩ : syracuseStep 5004233 = 3753175) B3753175
theorem B8444897 : Blo 1482061 8444897 := bstep (se 2 (by rfl) ⟨3166836, by rfl⟩ : syracuseStep 8444897 = 6333673) B6333673
theorem B2816993 : Blo 1482061 2816993 := bstep (se 2 (by rfl) ⟨1056372, by rfl⟩ : syracuseStep 2816993 = 2112745) B2112745
theorem B5348537 : Blo 1482061 5348537 := bstep (se 2 (by rfl) ⟨2005701, by rfl⟩ : syracuseStep 5348537 = 4011403) B4011403
theorem B5004503 : Blo 1482061 5004503 := bstep (se 1 (by rfl) ⟨3753377, by rfl⟩ : syracuseStep 5004503 = 7506755) B7506755
theorem B4570463 : Blo 1482061 4570463 := bstep (se 1 (by rfl) ⟨3427847, by rfl⟩ : syracuseStep 4570463 = 6855695) B6855695
theorem B1482215 : Blo 1482061 1482215 := bstep (se 1 (by rfl) ⟨1111661, by rfl⟩ : syracuseStep 1482215 = 2223323) B2223323
theorem B1482331 : Blo 1482061 1482331 := bstep (se 1 (by rfl) ⟨1111748, by rfl⟩ : syracuseStep 1482331 = 2223497) B2223497
theorem B9502433 : Blo 1482061 9502433 := bstep (se 2 (by rfl) ⟨3563412, by rfl⟩ : syracuseStep 9502433 = 7126825) B7126825
theorem B3751667 : Blo 1482061 3751667 := bstep (se 1 (by rfl) ⟨2813750, by rfl⟩ : syracuseStep 3751667 = 5627501) B5627501
theorem B5005043 : Blo 1482061 5005043 := bstep (se 1 (by rfl) ⟨3753782, by rfl⟩ : syracuseStep 5005043 = 7507565) B7507565
theorem B1482567 : Blo 1482061 1482567 := bstep (se 1 (by rfl) ⟨1111925, by rfl⟩ : syracuseStep 1482567 = 2223851) B2223851
theorem B1482719 : Blo 1482061 1482719 := bstep (se 1 (by rfl) ⟨1112039, by rfl⟩ : syracuseStep 1482719 = 2224079) B2224079
theorem B1482943 : Blo 1482061 1482943 := bstep (se 1 (by rfl) ⟨1112207, by rfl⟩ : syracuseStep 1482943 = 2224415) B2224415
theorem B1482959 : Blo 1482061 1482959 := bstep (se 1 (by rfl) ⟨1112219, by rfl⟩ : syracuseStep 1482959 = 2224439) B2224439
theorem B1876223 : Blo 1482061 1876223 := bstep (se 1 (by rfl) ⟨1407167, by rfl⟩ : syracuseStep 1876223 = 2814335) B2814335
theorem B1483007 : Blo 1482061 1483007 := bstep (se 1 (by rfl) ⟨1112255, by rfl⟩ : syracuseStep 1483007 = 2224511) B2224511
theorem B13705481 : Blo 1482061 13705481 := bstep (se 2 (by rfl) ⟨5139555, by rfl⟩ : syracuseStep 13705481 = 10279111) B10279111
theorem B20283695 : Blo 1482061 20283695 := bstep (se 1 (by rfl) ⟨15212771, by rfl⟩ : syracuseStep 20283695 = 30425543) B30425543
theorem B1483055 : Blo 1482061 1483055 := bstep (se 1 (by rfl) ⟨1112291, by rfl⟩ : syracuseStep 1483055 = 2224583) B2224583
theorem B16253303 : Blo 1482061 16253303 := bstep (se 1 (by rfl) ⟨12189977, by rfl⟩ : syracuseStep 16253303 = 24379955) B24379955
theorem B57041333 : Blo 1482061 57041333 := bstep (se 5 (by rfl) ⟨2673812, by rfl⟩ : syracuseStep 57041333 = 5347625) B5347625
theorem B9273815 : Blo 1482061 9273815 := bstep (se 1 (by rfl) ⟨6955361, by rfl⟩ : syracuseStep 9273815 = 13910723) B13910723
theorem B11264507 : Blo 1482061 11264507 := bstep (se 1 (by rfl) ⟨8448380, by rfl⟩ : syracuseStep 11264507 = 16896761) B16896761
theorem B1483291 : Blo 1482061 1483291 := bstep (se 1 (by rfl) ⟨1112468, by rfl⟩ : syracuseStep 1483291 = 2224937) B2224937
theorem B1483295 : Blo 1482061 1483295 := bstep (se 1 (by rfl) ⟨1112471, by rfl⟩ : syracuseStep 1483295 = 2224943) B2224943
theorem B1483375 : Blo 1482061 1483375 := bstep (se 1 (by rfl) ⟨1112531, by rfl⟩ : syracuseStep 1483375 = 2225063) B2225063
theorem B3334823 : Blo 1482061 3334823 := bstep (se 1 (by rfl) ⟨2501117, by rfl⟩ : syracuseStep 3334823 = 5002235) B5002235
theorem B1483431 : Blo 1482061 1483431 := bstep (se 1 (by rfl) ⟨1112573, by rfl⟩ : syracuseStep 1483431 = 2225147) B2225147
theorem B1483471 : Blo 1482061 1483471 := bstep (se 1 (by rfl) ⟨1112603, by rfl⟩ : syracuseStep 1483471 = 2225207) B2225207
theorem B1876699 : Blo 1482061 1876699 := bstep (se 1 (by rfl) ⟨1407524, by rfl⟩ : syracuseStep 1876699 = 2815049) B2815049
theorem B1483551 : Blo 1482061 1483551 := bstep (se 1 (by rfl) ⟨1112663, by rfl⟩ : syracuseStep 1483551 = 2225327) B2225327
theorem B3334967 : Blo 1482061 3334967 := bstep (se 1 (by rfl) ⟨2501225, by rfl⟩ : syracuseStep 3334967 = 5002451) B5002451
theorem B3384119 : Blo 1482061 3384119 := bstep (se 1 (by rfl) ⟨2538089, by rfl⟩ : syracuseStep 3384119 = 5076179) B5076179
theorem B3335147 : Blo 1482061 3335147 := bstep (se 1 (by rfl) ⟨2501360, by rfl⟩ : syracuseStep 3335147 = 5002721) B5002721
theorem B6013939 : Blo 1482061 6013939 := bstep (se 1 (by rfl) ⟨4510454, by rfl⟩ : syracuseStep 6013939 = 9020909) B9020909
theorem B1483823 : Blo 1482061 1483823 := bstep (se 1 (by rfl) ⟨1112867, by rfl⟩ : syracuseStep 1483823 = 2225735) B2225735
theorem B1483887 : Blo 1482061 1483887 := bstep (se 1 (by rfl) ⟨1112915, by rfl⟩ : syracuseStep 1483887 = 2225831) B2225831
theorem B39601315 : Blo 1482061 39601315 := bstep (se 1 (by rfl) ⟨29700986, by rfl⟩ : syracuseStep 39601315 = 59401973) B59401973
theorem B1483943 : Blo 1482061 1483943 := bstep (se 1 (by rfl) ⟨1112957, by rfl⟩ : syracuseStep 1483943 = 2225915) B2225915
theorem B1483967 : Blo 1482061 1483967 := bstep (se 1 (by rfl) ⟨1112975, by rfl⟩ : syracuseStep 1483967 = 2225951) B2225951
theorem B1483999 : Blo 1482061 1483999 := bstep (se 1 (by rfl) ⟨1112999, by rfl⟩ : syracuseStep 1483999 = 2225999) B2225999
theorem B25347329 : Blo 1482061 25347329 := bstep (se 2 (by rfl) ⟨9505248, by rfl⟩ : syracuseStep 25347329 = 19010497) B19010497
theorem B12027203 : Blo 1482061 12027203 := bstep (se 1 (by rfl) ⟨9020402, by rfl⟩ : syracuseStep 12027203 = 18040805) B18040805
theorem B3335579 : Blo 1482061 3335579 := bstep (se 1 (by rfl) ⟨2501684, by rfl⟩ : syracuseStep 3335579 = 5003369) B5003369
theorem B5629459 : Blo 1482061 5629459 := bstep (se 1 (by rfl) ⟨4222094, by rfl⟩ : syracuseStep 5629459 = 8444189) B8444189
theorem B7505459 : Blo 1482061 7505459 := bstep (se 1 (by rfl) ⟨5629094, by rfl⟩ : syracuseStep 7505459 = 11258189) B11258189
theorem B7226987 : Blo 1482061 7226987 := bstep (se 1 (by rfl) ⟨5420240, by rfl⟩ : syracuseStep 7226987 = 10840481) B10840481
theorem B36095705 : Blo 1482061 36095705 := bstep (se 2 (by rfl) ⟨13535889, by rfl⟩ : syracuseStep 36095705 = 27071779) B27071779
theorem B6334271 : Blo 1482061 6334271 := bstep (se 1 (by rfl) ⟨4750703, by rfl⟩ : syracuseStep 6334271 = 9501407) B9501407
theorem B3336155 : Blo 1482061 3336155 := bstep (se 1 (by rfl) ⟨2502116, by rfl⟩ : syracuseStep 3336155 = 5004233) B5004233
theorem B5629931 : Blo 1482061 5629931 := bstep (se 1 (by rfl) ⟨4222448, by rfl⟩ : syracuseStep 5629931 = 8444897) B8444897
theorem B1877995 : Blo 1482061 1877995 := bstep (se 1 (by rfl) ⟨1408496, by rfl⟩ : syracuseStep 1877995 = 2816993) B2816993
theorem B5629945 : Blo 1482061 5629945 := bstep (se 2 (by rfl) ⟨2111229, by rfl⟩ : syracuseStep 5629945 = 4222459) B4222459
theorem B14649353 : Blo 1482061 14649353 := bstep (se 2 (by rfl) ⟨5493507, by rfl⟩ : syracuseStep 14649353 = 10987015) B10987015
theorem B3565691 : Blo 1482061 3565691 := bstep (se 1 (by rfl) ⟨2674268, by rfl⟩ : syracuseStep 3565691 = 5348537) B5348537
theorem B3336335 : Blo 1482061 3336335 := bstep (se 1 (by rfl) ⟨2502251, by rfl⟩ : syracuseStep 3336335 = 5004503) B5004503
theorem B2853025 : Blo 1482061 2853025 := bstep (se 2 (by rfl) ⟨1069884, by rfl⟩ : syracuseStep 2853025 = 2139769) B2139769
theorem B3336425 : Blo 1482061 3336425 := bstep (se 2 (by rfl) ⟨1251159, by rfl⟩ : syracuseStep 3336425 = 2502319) B2502319
theorem B12675305 : Blo 1482061 12675305 := bstep (se 2 (by rfl) ⟨4753239, by rfl⟩ : syracuseStep 12675305 = 9506479) B9506479
theorem B6334955 : Blo 1482061 6334955 := bstep (se 1 (by rfl) ⟨4751216, by rfl⟩ : syracuseStep 6334955 = 9502433) B9502433
theorem B2501111 : Blo 1482061 2501111 := bstep (se 1 (by rfl) ⟨1875833, by rfl⟩ : syracuseStep 2501111 = 3751667) B3751667
theorem B3336695 : Blo 1482061 3336695 := bstep (se 1 (by rfl) ⟨2502521, by rfl⟩ : syracuseStep 3336695 = 5005043) B5005043
theorem B3754633 : Blo 1482061 3754633 := bstep (se 2 (by rfl) ⟨1407987, by rfl⟩ : syracuseStep 3754633 = 2815975) B2815975
theorem B10693291 : Blo 1482061 10693291 := bstep (se 1 (by rfl) ⟨8019968, by rfl⟩ : syracuseStep 10693291 = 16039937) B16039937
theorem B67677079 : Blo 1482061 67677079 := bstep (se 1 (by rfl) ⟨50757809, by rfl⟩ : syracuseStep 67677079 = 101515619) B101515619
theorem B5704607 : Blo 1482061 5704607 := bstep (se 1 (by rfl) ⟨4278455, by rfl⟩ : syracuseStep 5704607 = 8556911) B8556911
theorem B2501705 : Blo 1482061 2501705 := bstep (se 2 (by rfl) ⟨938139, by rfl⟩ : syracuseStep 2501705 = 1876279) B1876279
theorem B3337289 : Blo 1482061 3337289 := bstep (se 2 (by rfl) ⟨1251483, by rfl⟩ : syracuseStep 3337289 = 2502967) B2502967
theorem B14257259 : Blo 1482061 14257259 := bstep (se 1 (by rfl) ⟨10692944, by rfl⟩ : syracuseStep 14257259 = 21385889) B21385889
theorem B7507079 : Blo 1482061 7507079 := bstep (se 1 (by rfl) ⟨5630309, by rfl⟩ : syracuseStep 7507079 = 11260619) B11260619
theorem B5008553 : Blo 1482061 5008553 := bstep (se 2 (by rfl) ⟨1878207, by rfl⟩ : syracuseStep 5008553 = 3756415) B3756415
theorem B11259161 : Blo 1482061 11259161 := bstep (se 2 (by rfl) ⟨4222185, by rfl⟩ : syracuseStep 11259161 = 8444371) B8444371
theorem B2223515 : Blo 1482061 2223515 := bstep (se 1 (by rfl) ⟨1667636, by rfl⟩ : syracuseStep 2223515 = 3335273) B3335273
theorem B38014433 : Blo 1482061 38014433 := bstep (se 2 (by rfl) ⟨14255412, by rfl⟩ : syracuseStep 38014433 = 28510825) B28510825
theorem B4509287 : Blo 1482061 4509287 := bstep (se 1 (by rfl) ⟨3381965, by rfl⟩ : syracuseStep 4509287 = 6763931) B6763931
theorem B54857411 : Blo 1482061 54857411 := bstep (se 1 (by rfl) ⟨41143058, by rfl⟩ : syracuseStep 54857411 = 82286117) B82286117
theorem B2223935 : Blo 1482061 2223935 := bstep (se 1 (by rfl) ⟨1667951, by rfl⟩ : syracuseStep 2223935 = 3335903) B3335903
theorem B32051153 : Blo 1482061 32051153 := bstep (se 2 (by rfl) ⟨12019182, by rfl⟩ : syracuseStep 32051153 = 24038365) B24038365
theorem B2224121 : Blo 1482061 2224121 := bstep (se 2 (by rfl) ⟨834045, by rfl⟩ : syracuseStep 2224121 = 1668091) B1668091
theorem B3756071 : Blo 1482061 3756071 := bstep (se 1 (by rfl) ⟨2817053, by rfl⟩ : syracuseStep 3756071 = 5634107) B5634107
theorem B3166427 : Blo 1482061 3166427 := bstep (se 1 (by rfl) ⟨2374820, by rfl⟩ : syracuseStep 3166427 = 4749641) B4749641
theorem B2224361 : Blo 1482061 2224361 := bstep (se 2 (by rfl) ⟨834135, by rfl⟩ : syracuseStep 2224361 = 1668271) B1668271
theorem B2224487 : Blo 1482061 2224487 := bstep (se 1 (by rfl) ⟨1668365, by rfl⟩ : syracuseStep 2224487 = 3336731) B3336731
theorem B1782119 : Blo 1482061 1782119 := bstep (se 1 (by rfl) ⟨1336589, by rfl⟩ : syracuseStep 1782119 = 2673179) B2673179
theorem B1782523 : Blo 1482061 1782523 := bstep (se 1 (by rfl) ⟨1336892, by rfl⟩ : syracuseStep 1782523 = 2673785) B2673785
theorem B3339017 : Blo 1482061 3339017 := bstep (se 2 (by rfl) ⟨1252131, by rfl⟩ : syracuseStep 3339017 = 2504263) B2504263
theorem B16036649 : Blo 1482061 16036649 := bstep (se 2 (by rfl) ⟨6013743, by rfl⟩ : syracuseStep 16036649 = 12027487) B12027487
theorem B2503487 : Blo 1482061 2503487 := bstep (se 1 (by rfl) ⟨1877615, by rfl⟩ : syracuseStep 2503487 = 3755231) B3755231
theorem B3339071 : Blo 1482061 3339071 := bstep (se 1 (by rfl) ⟨2504303, by rfl⟩ : syracuseStep 3339071 = 5008607) B5008607
theorem B9507709 : Blo 1482061 9507709 := bstep (se 3 (by rfl) ⟨1782695, by rfl⟩ : syracuseStep 9507709 = 3565391) B3565391
theorem B2225033 : Blo 1482061 2225033 := bstep (se 2 (by rfl) ⟨834387, by rfl⟩ : syracuseStep 2225033 = 1668775) B1668775
theorem B2503561 : Blo 1482061 2503561 := bstep (se 2 (by rfl) ⟨938835, by rfl⟩ : syracuseStep 2503561 = 1877671) B1877671
theorem B6009851 : Blo 1482061 6009851 := bstep (se 1 (by rfl) ⟨4507388, by rfl⟩ : syracuseStep 6009851 = 9014777) B9014777
theorem B2225417 : Blo 1482061 2225417 := bstep (se 2 (by rfl) ⟨834531, by rfl⟩ : syracuseStep 2225417 = 1669063) B1669063
theorem B1668415 : Blo 1482061 1668415 := bstep (se 1 (by rfl) ⟨1251311, by rfl⟩ : syracuseStep 1668415 = 2502623) B2502623
theorem B2225471 : Blo 1482061 2225471 := bstep (se 1 (by rfl) ⟨1669103, by rfl⟩ : syracuseStep 2225471 = 3338207) B3338207
theorem B8123863 : Blo 1482061 8123863 := bstep (se 1 (by rfl) ⟨6092897, by rfl⟩ : syracuseStep 8123863 = 12185795) B12185795
theorem B2004463 : Blo 1482061 2004463 := bstep (se 1 (by rfl) ⟨1503347, by rfl⟩ : syracuseStep 2004463 = 3006695) B3006695
theorem B66795131 : Blo 1482061 66795131 := bstep (se 1 (by rfl) ⟨50096348, by rfl⟩ : syracuseStep 66795131 = 100192697) B100192697
theorem B10688219 : Blo 1482061 10688219 := bstep (se 1 (by rfl) ⟨8016164, by rfl⟩ : syracuseStep 10688219 = 16032329) B16032329
theorem B4749025 : Blo 1482061 4749025 := bstep (se 2 (by rfl) ⟨1780884, by rfl⟩ : syracuseStep 4749025 = 3561769) B3561769
theorem B4224737 : Blo 1482061 4224737 := bstep (se 2 (by rfl) ⟨1584276, by rfl⟩ : syracuseStep 4224737 = 3168553) B3168553
theorem B2225897 : Blo 1482061 2225897 := bstep (se 2 (by rfl) ⟨834711, by rfl⟩ : syracuseStep 2225897 = 1669423) B1669423
theorem B1668847 : Blo 1482061 1668847 := bstep (se 1 (by rfl) ⟨1251635, by rfl⟩ : syracuseStep 1668847 = 2503271) B2503271
theorem B2225903 : Blo 1482061 2225903 := bstep (se 1 (by rfl) ⟨1669427, by rfl⟩ : syracuseStep 2225903 = 3338855) B3338855
theorem B2815823 : Blo 1482061 2815823 := bstep (se 1 (by rfl) ⟨2111867, by rfl⟩ : syracuseStep 2815823 = 4223735) B4223735
theorem B5003099 : Blo 1482061 5003099 := bstep (se 1 (by rfl) ⟨3752324, by rfl⟩ : syracuseStep 5003099 = 7504649) B7504649
theorem B1668955 : Blo 1482061 1668955 := bstep (se 1 (by rfl) ⟨1251716, by rfl⟩ : syracuseStep 1668955 = 2503433) B2503433
theorem B1669351 : Blo 1482061 1669351 := bstep (se 1 (by rfl) ⟨1252013, by rfl⟩ : syracuseStep 1669351 = 2504027) B2504027
theorem B8018153 : Blo 1482061 8018153 := bstep (se 2 (by rfl) ⟨3006807, by rfl⟩ : syracuseStep 8018153 = 6013615) B6013615
theorem B12187901 : Blo 1482061 12187901 := bstep (se 3 (by rfl) ⟨2285231, by rfl⟩ : syracuseStep 12187901 = 4570463) B4570463
theorem B32086367 : Blo 1482061 32086367 := bstep (se 1 (by rfl) ⟨24064775, by rfl⟩ : syracuseStep 32086367 = 48129551) B48129551
theorem B7125691 : Blo 1482061 7125691 := bstep (se 1 (by rfl) ⟨5344268, by rfl⟩ : syracuseStep 7125691 = 10688537) B10688537
theorem B13523921 : Blo 1482061 13523921 := bstep (se 2 (by rfl) ⟨5071470, by rfl⟩ : syracuseStep 13523921 = 10142941) B10142941
theorem B12663823 : Blo 1482061 12663823 := bstep (se 1 (by rfl) ⟨9497867, by rfl⟩ : syracuseStep 12663823 = 18995735) B18995735
theorem B29678993 : Blo 1482061 29678993 := bstep (se 2 (by rfl) ⟨11129622, by rfl⟩ : syracuseStep 29678993 = 22259245) B22259245
theorem B5627303 : Blo 1482061 5627303 := bstep (se 1 (by rfl) ⟨4220477, by rfl⟩ : syracuseStep 5627303 = 8440955) B8440955
theorem B1482191 : Blo 1482061 1482191 := bstep (se 1 (by rfl) ⟨1111643, by rfl⟩ : syracuseStep 1482191 = 2223287) B2223287
theorem B1482351 : Blo 1482061 1482351 := bstep (se 1 (by rfl) ⟨1111763, by rfl⟩ : syracuseStep 1482351 = 2223527) B2223527
theorem B1482407 : Blo 1482061 1482407 := bstep (se 1 (by rfl) ⟨1111805, by rfl⟩ : syracuseStep 1482407 = 2223611) B2223611
theorem B1482471 : Blo 1482061 1482471 := bstep (se 1 (by rfl) ⟨1111853, by rfl⟩ : syracuseStep 1482471 = 2223707) B2223707
theorem B1482527 : Blo 1482061 1482527 := bstep (se 1 (by rfl) ⟨1111895, by rfl⟩ : syracuseStep 1482527 = 2223791) B2223791
theorem B1482607 : Blo 1482061 1482607 := bstep (se 1 (by rfl) ⟨1111955, by rfl⟩ : syracuseStep 1482607 = 2223911) B2223911
theorem B1482663 : Blo 1482061 1482663 := bstep (se 1 (by rfl) ⟨1111997, by rfl⟩ : syracuseStep 1482663 = 2223995) B2223995
theorem B1482907 : Blo 1482061 1482907 := bstep (se 1 (by rfl) ⟨1112180, by rfl⟩ : syracuseStep 1482907 = 2224361) B2224361
theorem B1482991 : Blo 1482061 1482991 := bstep (se 1 (by rfl) ⟨1112243, by rfl⟩ : syracuseStep 1482991 = 2224487) B2224487
theorem B38027555 : Blo 1482061 38027555 := bstep (se 1 (by rfl) ⟨28520666, by rfl⟩ : syracuseStep 38027555 = 57041333) B57041333
theorem B10691099 : Blo 1482061 10691099 := bstep (se 1 (by rfl) ⟨8018324, by rfl⟩ : syracuseStep 10691099 = 16036649) B16036649
theorem B1483355 : Blo 1482061 1483355 := bstep (se 1 (by rfl) ⟨1112516, by rfl⟩ : syracuseStep 1483355 = 2225033) B2225033
theorem B4006567 : Blo 1482061 4006567 := bstep (se 1 (by rfl) ⟨3004925, by rfl⟩ : syracuseStep 4006567 = 6009851) B6009851
theorem B1483611 : Blo 1482061 1483611 := bstep (se 1 (by rfl) ⟨1112708, by rfl⟩ : syracuseStep 1483611 = 2225417) B2225417
theorem B5006177 : Blo 1482061 5006177 := bstep (se 2 (by rfl) ⟨1877316, by rfl⟩ : syracuseStep 5006177 = 3754633) B3754633
theorem B1483647 : Blo 1482061 1483647 := bstep (se 1 (by rfl) ⟨1112735, by rfl⟩ : syracuseStep 1483647 = 2225471) B2225471
theorem B4752317 : Blo 1482061 4752317 := bstep (se 3 (by rfl) ⟨891059, by rfl⟩ : syracuseStep 4752317 = 1782119) B1782119
theorem B2376697 : Blo 1482061 2376697 := bstep (se 2 (by rfl) ⟨891261, by rfl⟩ : syracuseStep 2376697 = 1782523) B1782523
theorem B1483931 : Blo 1482061 1483931 := bstep (se 1 (by rfl) ⟨1112948, by rfl⟩ : syracuseStep 1483931 = 2225897) B2225897
theorem B1483935 : Blo 1482061 1483935 := bstep (se 1 (by rfl) ⟨1112951, by rfl⟩ : syracuseStep 1483935 = 2225903) B2225903
theorem B90236105 : Blo 1482061 90236105 := bstep (se 2 (by rfl) ⟨33838539, by rfl⟩ : syracuseStep 90236105 = 67677079) B67677079
theorem B3335399 : Blo 1482061 3335399 := bstep (se 1 (by rfl) ⟨2501549, by rfl⟩ : syracuseStep 3335399 = 5003099) B5003099
theorem B3753287 : Blo 1482061 3753287 := bstep (se 1 (by rfl) ⟨2814965, by rfl⟩ : syracuseStep 3753287 = 5629931) B5629931
theorem B9766235 : Blo 1482061 9766235 := bstep (se 1 (by rfl) ⟨7324676, by rfl⟩ : syracuseStep 9766235 = 14649353) B14649353
theorem B16885097 : Blo 1482061 16885097 := bstep (se 2 (by rfl) ⟨6331911, by rfl⟩ : syracuseStep 16885097 = 12663823) B12663823
theorem B2377127 : Blo 1482061 2377127 := bstep (se 1 (by rfl) ⟨1782845, by rfl⟩ : syracuseStep 2377127 = 3565691) B3565691
theorem B21390911 : Blo 1482061 21390911 := bstep (se 1 (by rfl) ⟨16043183, by rfl⟩ : syracuseStep 21390911 = 32086367) B32086367
theorem B178120349 : Blo 1482061 178120349 := bstep (se 3 (by rfl) ⟨33397565, by rfl⟩ : syracuseStep 178120349 = 66795131) B66795131
theorem B11265965 : Blo 1482061 11265965 := bstep (se 3 (by rfl) ⟨2112368, by rfl⟩ : syracuseStep 11265965 = 4224737) B4224737
theorem B3803071 : Blo 1482061 3803071 := bstep (se 1 (by rfl) ⟨2852303, by rfl⟩ : syracuseStep 3803071 = 5704607) B5704607
theorem B10831817 : Blo 1482061 10831817 := bstep (se 2 (by rfl) ⟨4061931, by rfl⟩ : syracuseStep 10831817 = 8123863) B8123863
theorem B2672617 : Blo 1482061 2672617 := bstep (se 2 (by rfl) ⟨1002231, by rfl⟩ : syracuseStep 2672617 = 2004463) B2004463
theorem B7505945 : Blo 1482061 7505945 := bstep (se 2 (by rfl) ⟨2814729, by rfl⟩ : syracuseStep 7505945 = 5629459) B5629459
theorem B9504839 : Blo 1482061 9504839 := bstep (se 1 (by rfl) ⟨7128629, by rfl⟩ : syracuseStep 9504839 = 14257259) B14257259
theorem B7506107 : Blo 1482061 7506107 := bstep (se 1 (by rfl) ⟨5629580, by rfl⟩ : syracuseStep 7506107 = 11259161) B11259161
theorem B19785995 : Blo 1482061 19785995 := bstep (se 1 (by rfl) ⟨14839496, by rfl⟩ : syracuseStep 19785995 = 29678993) B29678993
theorem B36571607 : Blo 1482061 36571607 := bstep (se 1 (by rfl) ⟨27428705, by rfl⟩ : syracuseStep 36571607 = 54857411) B54857411
theorem B21367435 : Blo 1482061 21367435 := bstep (se 1 (by rfl) ⟨16025576, by rfl⟩ : syracuseStep 21367435 = 32051153) B32051153
theorem B7506593 : Blo 1482061 7506593 := bstep (se 2 (by rfl) ⟨2814972, by rfl⟩ : syracuseStep 7506593 = 5629945) B5629945
theorem B2223215 : Blo 1482061 2223215 := bstep (se 1 (by rfl) ⟨1667411, by rfl⟩ : syracuseStep 2223215 = 3334823) B3334823
theorem B2223311 : Blo 1482061 2223311 := bstep (se 1 (by rfl) ⟨1667483, by rfl⟩ : syracuseStep 2223311 = 3334967) B3334967
theorem B2256079 : Blo 1482061 2256079 := bstep (se 1 (by rfl) ⟨1692059, by rfl⟩ : syracuseStep 2256079 = 3384119) B3384119
theorem B2223431 : Blo 1482061 2223431 := bstep (se 1 (by rfl) ⟨1667573, by rfl⟩ : syracuseStep 2223431 = 3335147) B3335147
theorem B36547949 : Blo 1482061 36547949 := bstep (se 3 (by rfl) ⟨6852740, by rfl⟩ : syracuseStep 36547949 = 13705481) B13705481
theorem B15216133 : Blo 1482061 15216133 := bstep (se 4 (by rfl) ⟨1426512, by rfl⟩ : syracuseStep 15216133 = 2853025) B2853025
theorem B14257721 : Blo 1482061 14257721 := bstep (se 2 (by rfl) ⟨5346645, by rfl⟩ : syracuseStep 14257721 = 10693291) B10693291
theorem B2223719 : Blo 1482061 2223719 := bstep (se 1 (by rfl) ⟨1667789, by rfl⟩ : syracuseStep 2223719 = 3335579) B3335579
theorem B2502265 : Blo 1482061 2502265 := bstep (se 2 (by rfl) ⟨938349, by rfl⟩ : syracuseStep 2502265 = 1876699) B1876699
theorem B24063803 : Blo 1482061 24063803 := bstep (se 1 (by rfl) ⟨18047852, by rfl⟩ : syracuseStep 24063803 = 36095705) B36095705
theorem B12676945 : Blo 1482061 12676945 := bstep (se 2 (by rfl) ⟨4753854, by rfl⟩ : syracuseStep 12676945 = 9507709) B9507709
theorem B3338081 : Blo 1482061 3338081 := bstep (se 2 (by rfl) ⟨1251780, by rfl⟩ : syracuseStep 3338081 = 2503561) B2503561
theorem B4222847 : Blo 1482061 4222847 := bstep (se 1 (by rfl) ⟨3167135, by rfl⟩ : syracuseStep 4222847 = 6334271) B6334271
theorem B2224103 : Blo 1482061 2224103 := bstep (se 1 (by rfl) ⟨1668077, by rfl⟩ : syracuseStep 2224103 = 3336155) B3336155
theorem B2224223 : Blo 1482061 2224223 := bstep (se 1 (by rfl) ⟨1668167, by rfl⟩ : syracuseStep 2224223 = 3336335) B3336335
theorem B2224283 : Blo 1482061 2224283 := bstep (se 1 (by rfl) ⟨1668212, by rfl⟩ : syracuseStep 2224283 = 3336425) B3336425
theorem B5345435 : Blo 1482061 5345435 := bstep (se 1 (by rfl) ⟨4009076, by rfl⟩ : syracuseStep 5345435 = 8018153) B8018153
theorem B8450203 : Blo 1482061 8450203 := bstep (se 1 (by rfl) ⟨6337652, by rfl⟩ : syracuseStep 8450203 = 12675305) B12675305
theorem B52801753 : Blo 1482061 52801753 := bstep (se 2 (by rfl) ⟨19800657, by rfl⟩ : syracuseStep 52801753 = 39601315) B39601315
theorem B19271965 : Blo 1482061 19271965 := bstep (se 3 (by rfl) ⟨3613493, by rfl⟩ : syracuseStep 19271965 = 7226987) B7226987
theorem B4223303 : Blo 1482061 4223303 := bstep (se 1 (by rfl) ⟨3167477, by rfl⟩ : syracuseStep 4223303 = 6334955) B6334955
theorem B1667407 : Blo 1482061 1667407 := bstep (se 1 (by rfl) ⟨1250555, by rfl⟩ : syracuseStep 1667407 = 2501111) B2501111
theorem B2224463 : Blo 1482061 2224463 := bstep (se 1 (by rfl) ⟨1668347, by rfl⟩ : syracuseStep 2224463 = 3336695) B3336695
theorem B2224553 : Blo 1482061 2224553 := bstep (se 2 (by rfl) ⟨834207, by rfl⟩ : syracuseStep 2224553 = 1668415) B1668415
theorem B9015947 : Blo 1482061 9015947 := bstep (se 1 (by rfl) ⟨6761960, by rfl⟩ : syracuseStep 9015947 = 13523921) B13523921
theorem B1667803 : Blo 1482061 1667803 := bstep (se 1 (by rfl) ⟨1250852, by rfl⟩ : syracuseStep 1667803 = 2501705) B2501705
theorem B2224859 : Blo 1482061 2224859 := bstep (se 1 (by rfl) ⟨1668644, by rfl⟩ : syracuseStep 2224859 = 3337289) B3337289
theorem B3339035 : Blo 1482061 3339035 := bstep (se 1 (by rfl) ⟨2504276, by rfl⟩ : syracuseStep 3339035 = 5008553) B5008553
theorem B7508861 : Blo 1482061 7508861 := bstep (se 3 (by rfl) ⟨1407911, by rfl⟩ : syracuseStep 7508861 = 2815823) B2815823
theorem B2225129 : Blo 1482061 2225129 := bstep (se 2 (by rfl) ⟨834423, by rfl⟩ : syracuseStep 2225129 = 1668847) B1668847
theorem B25342955 : Blo 1482061 25342955 := bstep (se 1 (by rfl) ⟨19007216, by rfl⟩ : syracuseStep 25342955 = 38014433) B38014433
theorem B2225273 : Blo 1482061 2225273 := bstep (se 2 (by rfl) ⟨834477, by rfl⟩ : syracuseStep 2225273 = 1668955) B1668955
theorem B2503993 : Blo 1482061 2503993 := bstep (se 2 (by rfl) ⟨938997, by rfl⟩ : syracuseStep 2503993 = 1877995) B1877995
theorem B2504047 : Blo 1482061 2504047 := bstep (se 1 (by rfl) ⟨1878035, by rfl⟩ : syracuseStep 2504047 = 3756071) B3756071
theorem B2110951 : Blo 1482061 2110951 := bstep (se 1 (by rfl) ⟨1583213, by rfl⟩ : syracuseStep 2110951 = 3166427) B3166427
theorem B13522463 : Blo 1482061 13522463 := bstep (se 1 (by rfl) ⟨10141847, by rfl⟩ : syracuseStep 13522463 = 20283695) B20283695
theorem B2225801 : Blo 1482061 2225801 := bstep (se 2 (by rfl) ⟨834675, by rfl⟩ : syracuseStep 2225801 = 1669351) B1669351
theorem B6182543 : Blo 1482061 6182543 := bstep (se 1 (by rfl) ⟨4636907, by rfl⟩ : syracuseStep 6182543 = 9273815) B9273815
theorem B7509671 : Blo 1482061 7509671 := bstep (se 1 (by rfl) ⟨5632253, by rfl⟩ : syracuseStep 7509671 = 11264507) B11264507
theorem B2226011 : Blo 1482061 2226011 := bstep (se 1 (by rfl) ⟨1669508, by rfl⟩ : syracuseStep 2226011 = 3339017) B3339017
theorem B1668991 : Blo 1482061 1668991 := bstep (se 1 (by rfl) ⟨1251743, by rfl⟩ : syracuseStep 1668991 = 2503487) B2503487
theorem B2226047 : Blo 1482061 2226047 := bstep (se 1 (by rfl) ⟨1669535, by rfl⟩ : syracuseStep 2226047 = 3339071) B3339071
theorem B5003261 : Blo 1482061 5003261 := bstep (se 3 (by rfl) ⟨938111, by rfl⟩ : syracuseStep 5003261 = 1876223) B1876223
theorem B16898219 : Blo 1482061 16898219 := bstep (se 1 (by rfl) ⟨12673664, by rfl⟩ : syracuseStep 16898219 = 25347329) B25347329
theorem B8018135 : Blo 1482061 8018135 := bstep (se 1 (by rfl) ⟨6013601, by rfl⟩ : syracuseStep 8018135 = 12027203) B12027203
theorem B9500921 : Blo 1482061 9500921 := bstep (se 2 (by rfl) ⟨3562845, by rfl⟩ : syracuseStep 9500921 = 7125691) B7125691
theorem B43342141 : Blo 1482061 43342141 := bstep (se 3 (by rfl) ⟨8126651, by rfl⟩ : syracuseStep 43342141 = 16253303) B16253303
theorem B5003639 : Blo 1482061 5003639 := bstep (se 1 (by rfl) ⟨3752729, by rfl⟩ : syracuseStep 5003639 = 7505459) B7505459
theorem B7125479 : Blo 1482061 7125479 := bstep (se 1 (by rfl) ⟨5344109, by rfl⟩ : syracuseStep 7125479 = 10688219) B10688219
theorem B8018585 : Blo 1482061 8018585 := bstep (se 2 (by rfl) ⟨3006969, by rfl⟩ : syracuseStep 8018585 = 6013939) B6013939
theorem B8125267 : Blo 1482061 8125267 := bstep (se 1 (by rfl) ⟨6093950, by rfl⟩ : syracuseStep 8125267 = 12187901) B12187901
theorem B5004719 : Blo 1482061 5004719 := bstep (se 1 (by rfl) ⟨3753539, by rfl⟩ : syracuseStep 5004719 = 7507079) B7507079
theorem B1482343 : Blo 1482061 1482343 := bstep (se 1 (by rfl) ⟨1111757, by rfl⟩ : syracuseStep 1482343 = 2223515) B2223515
theorem B3751535 : Blo 1482061 3751535 := bstep (se 1 (by rfl) ⟨2813651, by rfl⟩ : syracuseStep 3751535 = 5627303) B5627303
theorem B6332033 : Blo 1482061 6332033 := bstep (se 2 (by rfl) ⟨2374512, by rfl⟩ : syracuseStep 6332033 = 4749025) B4749025
theorem B3006191 : Blo 1482061 3006191 := bstep (se 1 (by rfl) ⟨2254643, by rfl⟩ : syracuseStep 3006191 = 4509287) B4509287
theorem B1482623 : Blo 1482061 1482623 := bstep (se 1 (by rfl) ⟨1111967, by rfl⟩ : syracuseStep 1482623 = 2223935) B2223935
theorem B1482747 : Blo 1482061 1482747 := bstep (se 1 (by rfl) ⟨1112060, by rfl⟩ : syracuseStep 1482747 = 2224121) B2224121
theorem B1482815 : Blo 1482061 1482815 := bstep (se 1 (by rfl) ⟨1112111, by rfl⟩ : syracuseStep 1482815 = 2224223) B2224223
theorem B1482855 : Blo 1482061 1482855 := bstep (se 1 (by rfl) ⟨1112141, by rfl⟩ : syracuseStep 1482855 = 2224283) B2224283
theorem B3563623 : Blo 1482061 3563623 := bstep (se 1 (by rfl) ⟨2672717, by rfl⟩ : syracuseStep 3563623 = 5345435) B5345435
theorem B1482975 : Blo 1482061 1482975 := bstep (se 1 (by rfl) ⟨1112231, by rfl⟩ : syracuseStep 1482975 = 2224463) B2224463
theorem B1483035 : Blo 1482061 1483035 := bstep (se 1 (by rfl) ⟨1112276, by rfl⟩ : syracuseStep 1483035 = 2224553) B2224553
theorem B70402337 : Blo 1482061 70402337 := bstep (se 2 (by rfl) ⟨26400876, by rfl⟩ : syracuseStep 70402337 = 52801753) B52801753
theorem B7127399 : Blo 1482061 7127399 := bstep (se 1 (by rfl) ⟨5345549, by rfl⟩ : syracuseStep 7127399 = 10691099) B10691099
theorem B1483239 : Blo 1482061 1483239 := bstep (se 1 (by rfl) ⟨1112429, by rfl⟩ : syracuseStep 1483239 = 2224859) B2224859
theorem B5005907 : Blo 1482061 5005907 := bstep (se 1 (by rfl) ⟨3754430, by rfl⟩ : syracuseStep 5005907 = 7508861) B7508861
theorem B1483419 : Blo 1482061 1483419 := bstep (se 1 (by rfl) ⟨1112564, by rfl⟩ : syracuseStep 1483419 = 2225129) B2225129
theorem B1483515 : Blo 1482061 1483515 := bstep (se 1 (by rfl) ⟨1112636, by rfl⟩ : syracuseStep 1483515 = 2225273) B2225273
theorem B11256731 : Blo 1482061 11256731 := bstep (se 1 (by rfl) ⟨8442548, by rfl⟩ : syracuseStep 11256731 = 16885097) B16885097
theorem B1483867 : Blo 1482061 1483867 := bstep (se 1 (by rfl) ⟨1112900, by rfl⟩ : syracuseStep 1483867 = 2225801) B2225801
theorem B4121695 : Blo 1482061 4121695 := bstep (se 1 (by rfl) ⟨3091271, by rfl⟩ : syracuseStep 4121695 = 6182543) B6182543
theorem B5006447 : Blo 1482061 5006447 := bstep (se 1 (by rfl) ⟨3754835, by rfl⟩ : syracuseStep 5006447 = 7509671) B7509671
theorem B1484007 : Blo 1482061 1484007 := bstep (se 1 (by rfl) ⟨1113005, by rfl⟩ : syracuseStep 1484007 = 2226011) B2226011
theorem B1484031 : Blo 1482061 1484031 := bstep (se 1 (by rfl) ⟨1113023, by rfl⟩ : syracuseStep 1484031 = 2226047) B2226047
theorem B3335507 : Blo 1482061 3335507 := bstep (se 1 (by rfl) ⟨2501630, by rfl⟩ : syracuseStep 3335507 = 5003261) B5003261
theorem B11265479 : Blo 1482061 11265479 := bstep (se 1 (by rfl) ⟨8449109, by rfl⟩ : syracuseStep 11265479 = 16898219) B16898219
theorem B6333947 : Blo 1482061 6333947 := bstep (se 1 (by rfl) ⟨4750460, by rfl⟩ : syracuseStep 6333947 = 9500921) B9500921
theorem B13190663 : Blo 1482061 13190663 := bstep (se 1 (by rfl) ⟨9892997, by rfl⟩ : syracuseStep 13190663 = 19785995) B19785995
theorem B3335759 : Blo 1482061 3335759 := bstep (se 1 (by rfl) ⟨2501819, by rfl⟩ : syracuseStep 3335759 = 5003639) B5003639
theorem B3008105 : Blo 1482061 3008105 := bstep (se 2 (by rfl) ⟨1128039, by rfl⟩ : syracuseStep 3008105 = 2256079) B2256079
theorem B24381071 : Blo 1482061 24381071 := bstep (se 1 (by rfl) ⟨18285803, by rfl⟩ : syracuseStep 24381071 = 36571607) B36571607
theorem B3336353 : Blo 1482061 3336353 := bstep (se 2 (by rfl) ⟨1251132, by rfl⟩ : syracuseStep 3336353 = 2502265) B2502265
theorem B24365299 : Blo 1482061 24365299 := bstep (se 1 (by rfl) ⟨18273974, by rfl⟩ : syracuseStep 24365299 = 36547949) B36547949
theorem B3336479 : Blo 1482061 3336479 := bstep (se 1 (by rfl) ⟨2502359, by rfl⟩ : syracuseStep 3336479 = 5004719) B5004719
theorem B9505147 : Blo 1482061 9505147 := bstep (se 1 (by rfl) ⟨7128860, by rfl⟩ : syracuseStep 9505147 = 14257721) B14257721
theorem B2501023 : Blo 1482061 2501023 := bstep (se 1 (by rfl) ⟨1875767, by rfl⟩ : syracuseStep 2501023 = 3751535) B3751535
theorem B4221355 : Blo 1482061 4221355 := bstep (se 1 (by rfl) ⟨3166016, by rfl⟩ : syracuseStep 4221355 = 6332033) B6332033
theorem B16902593 : Blo 1482061 16902593 := bstep (se 2 (by rfl) ⟨6338472, by rfl⟩ : syracuseStep 16902593 = 12676945) B12676945
theorem B16042535 : Blo 1482061 16042535 := bstep (se 1 (by rfl) ⟨12031901, by rfl⟩ : syracuseStep 16042535 = 24063803) B24063803
theorem B11266937 : Blo 1482061 11266937 := bstep (se 2 (by rfl) ⟨4225101, by rfl⟩ : syracuseStep 11266937 = 8450203) B8450203
theorem B57789521 : Blo 1482061 57789521 := bstep (se 2 (by rfl) ⟨21671070, by rfl⟩ : syracuseStep 57789521 = 43342141) B43342141
theorem B2223209 : Blo 1482061 2223209 := bstep (se 2 (by rfl) ⟨833703, by rfl⟩ : syracuseStep 2223209 = 1667407) B1667407
theorem B3337451 : Blo 1482061 3337451 := bstep (se 1 (by rfl) ⟨2503088, by rfl⟩ : syracuseStep 3337451 = 5006177) B5006177
theorem B16895303 : Blo 1482061 16895303 := bstep (se 1 (by rfl) ⟨12671477, by rfl⟩ : syracuseStep 16895303 = 25342955) B25342955
theorem B60157403 : Blo 1482061 60157403 := bstep (se 1 (by rfl) ⟨45118052, by rfl⟩ : syracuseStep 60157403 = 90236105) B90236105
theorem B2223599 : Blo 1482061 2223599 := bstep (se 1 (by rfl) ⟨1667699, by rfl⟩ : syracuseStep 2223599 = 3335399) B3335399
theorem B21368357 : Blo 1482061 21368357 := bstep (se 4 (by rfl) ⟨2003283, by rfl⟩ : syracuseStep 21368357 = 4006567) B4006567
theorem B2502191 : Blo 1482061 2502191 := bstep (se 1 (by rfl) ⟨1876643, by rfl⟩ : syracuseStep 2502191 = 3753287) B3753287
theorem B2223737 : Blo 1482061 2223737 := bstep (se 2 (by rfl) ⟨833901, by rfl⟩ : syracuseStep 2223737 = 1667803) B1667803
theorem B9014975 : Blo 1482061 9014975 := bstep (se 1 (by rfl) ⟨6761231, by rfl⟩ : syracuseStep 9014975 = 13522463) B13522463
theorem B118746899 : Blo 1482061 118746899 := bstep (se 1 (by rfl) ⟨89060174, by rfl⟩ : syracuseStep 118746899 = 178120349) B178120349
theorem B10833689 : Blo 1482061 10833689 := bstep (se 2 (by rfl) ⟨4062633, by rfl⟩ : syracuseStep 10833689 = 8125267) B8125267
theorem B6336559 : Blo 1482061 6336559 := bstep (se 1 (by rfl) ⟨4752419, by rfl⟩ : syracuseStep 6336559 = 9504839) B9504839
theorem B5345423 : Blo 1482061 5345423 := bstep (se 1 (by rfl) ⟨4009067, by rfl⟩ : syracuseStep 5345423 = 8018135) B8018135
theorem B3338657 : Blo 1482061 3338657 := bstep (se 2 (by rfl) ⟨1251996, by rfl⟩ : syracuseStep 3338657 = 2503993) B2503993
theorem B5345723 : Blo 1482061 5345723 := bstep (se 1 (by rfl) ⟨4009292, by rfl⟩ : syracuseStep 5345723 = 8018585) B8018585
theorem B3338729 : Blo 1482061 3338729 := bstep (se 2 (by rfl) ⟨1252023, by rfl⟩ : syracuseStep 3338729 = 2504047) B2504047
theorem B8016509 : Blo 1482061 8016509 := bstep (se 3 (by rfl) ⟨1503095, by rfl⟩ : syracuseStep 8016509 = 3006191) B3006191
theorem B2814601 : Blo 1482061 2814601 := bstep (se 2 (by rfl) ⟨1055475, by rfl⟩ : syracuseStep 2814601 = 2110951) B2110951
theorem B20288177 : Blo 1482061 20288177 := bstep (se 2 (by rfl) ⟨7608066, by rfl⟩ : syracuseStep 20288177 = 15216133) B15216133
theorem B2225321 : Blo 1482061 2225321 := bstep (se 2 (by rfl) ⟨834495, by rfl⟩ : syracuseStep 2225321 = 1668991) B1668991
theorem B2225387 : Blo 1482061 2225387 := bstep (se 1 (by rfl) ⟨1669040, by rfl⟩ : syracuseStep 2225387 = 3338081) B3338081
theorem B2815231 : Blo 1482061 2815231 := bstep (se 1 (by rfl) ⟨2111423, by rfl⟩ : syracuseStep 2815231 = 4222847) B4222847
theorem B25351703 : Blo 1482061 25351703 := bstep (se 1 (by rfl) ⟨19013777, by rfl⟩ : syracuseStep 25351703 = 38027555) B38027555
theorem B2815535 : Blo 1482061 2815535 := bstep (se 1 (by rfl) ⟨2111651, by rfl⟩ : syracuseStep 2815535 = 4223303) B4223303
theorem B25695953 : Blo 1482061 25695953 := bstep (se 2 (by rfl) ⟨9635982, by rfl⟩ : syracuseStep 25695953 = 19271965) B19271965
theorem B6010631 : Blo 1482061 6010631 := bstep (se 1 (by rfl) ⟨4507973, by rfl⟩ : syracuseStep 6010631 = 9015947) B9015947
theorem B2226023 : Blo 1482061 2226023 := bstep (se 1 (by rfl) ⟨1669517, by rfl⟩ : syracuseStep 2226023 = 3339035) B3339035
theorem B28489913 : Blo 1482061 28489913 := bstep (se 2 (by rfl) ⟨10683717, by rfl⟩ : syracuseStep 28489913 = 21367435) B21367435
theorem B6510823 : Blo 1482061 6510823 := bstep (se 1 (by rfl) ⟨4883117, by rfl⟩ : syracuseStep 6510823 = 9766235) B9766235
theorem B14260607 : Blo 1482061 14260607 := bstep (se 1 (by rfl) ⟨10695455, by rfl⟩ : syracuseStep 14260607 = 21390911) B21390911
theorem B6339005 : Blo 1482061 6339005 := bstep (se 3 (by rfl) ⟨1188563, by rfl⟩ : syracuseStep 6339005 = 2377127) B2377127
theorem B7510643 : Blo 1482061 7510643 := bstep (se 1 (by rfl) ⟨5632982, by rfl⟩ : syracuseStep 7510643 = 11265965) B11265965
theorem B3168929 : Blo 1482061 3168929 := bstep (se 2 (by rfl) ⟨1188348, by rfl⟩ : syracuseStep 3168929 = 2376697) B2376697
theorem B5003963 : Blo 1482061 5003963 := bstep (se 1 (by rfl) ⟨3752972, by rfl⟩ : syracuseStep 5003963 = 7505945) B7505945
theorem B5004071 : Blo 1482061 5004071 := bstep (se 1 (by rfl) ⟨3753053, by rfl⟩ : syracuseStep 5004071 = 7506107) B7506107
theorem B4750319 : Blo 1482061 4750319 := bstep (se 1 (by rfl) ⟨3562739, by rfl⟩ : syracuseStep 4750319 = 7125479) B7125479
theorem B5004395 : Blo 1482061 5004395 := bstep (se 1 (by rfl) ⟨3753296, by rfl⟩ : syracuseStep 5004395 = 7506593) B7506593
theorem B1482143 : Blo 1482061 1482143 := bstep (se 1 (by rfl) ⟨1111607, by rfl⟩ : syracuseStep 1482143 = 2223215) B2223215
theorem B1482207 : Blo 1482061 1482207 := bstep (se 1 (by rfl) ⟨1111655, by rfl⟩ : syracuseStep 1482207 = 2223311) B2223311
theorem B1482287 : Blo 1482061 1482287 := bstep (se 1 (by rfl) ⟨1111715, by rfl⟩ : syracuseStep 1482287 = 2223431) B2223431
theorem B1482479 : Blo 1482061 1482479 := bstep (se 1 (by rfl) ⟨1111859, by rfl⟩ : syracuseStep 1482479 = 2223719) B2223719
theorem B12672845 : Blo 1482061 12672845 := bstep (se 3 (by rfl) ⟨2376158, by rfl⟩ : syracuseStep 12672845 = 4752317) B4752317
theorem B28884845 : Blo 1482061 28884845 := bstep (se 3 (by rfl) ⟨5415908, by rfl⟩ : syracuseStep 28884845 = 10831817) B10831817
theorem B5070761 : Blo 1482061 5070761 := bstep (se 2 (by rfl) ⟨1901535, by rfl⟩ : syracuseStep 5070761 = 3803071) B3803071
theorem B3563489 : Blo 1482061 3563489 := bstep (se 2 (by rfl) ⟨1336308, by rfl⟩ : syracuseStep 3563489 = 2672617) B2672617
theorem B1482735 : Blo 1482061 1482735 := bstep (se 1 (by rfl) ⟨1112051, by rfl⟩ : syracuseStep 1482735 = 2224103) B2224103
theorem B3563615 : Blo 1482061 3563615 := bstep (se 1 (by rfl) ⟨2672711, by rfl⟩ : syracuseStep 3563615 = 5345423) B5345423
theorem B4751497 : Blo 1482061 4751497 := bstep (se 2 (by rfl) ⟨1781811, by rfl⟩ : syracuseStep 4751497 = 3563623) B3563623
theorem B13525451 : Blo 1482061 13525451 := bstep (se 1 (by rfl) ⟨10144088, by rfl⟩ : syracuseStep 13525451 = 20288177) B20288177
theorem B12673529 : Blo 1482061 12673529 := bstep (se 2 (by rfl) ⟨4752573, by rfl⟩ : syracuseStep 12673529 = 9505147) B9505147
theorem B3334697 : Blo 1482061 3334697 := bstep (se 2 (by rfl) ⟨1250511, by rfl⟩ : syracuseStep 3334697 = 2501023) B2501023
theorem B5628473 : Blo 1482061 5628473 := bstep (se 2 (by rfl) ⟨2110677, by rfl⟩ : syracuseStep 5628473 = 4221355) B4221355
theorem B7504487 : Blo 1482061 7504487 := bstep (se 1 (by rfl) ⟨5628365, by rfl⟩ : syracuseStep 7504487 = 11256731) B11256731
theorem B1483547 : Blo 1482061 1483547 := bstep (se 1 (by rfl) ⟨1112660, by rfl⟩ : syracuseStep 1483547 = 2225321) B2225321
theorem B1483591 : Blo 1482061 1483591 := bstep (se 1 (by rfl) ⟨1112693, by rfl⟩ : syracuseStep 1483591 = 2225387) B2225387
theorem B3752801 : Blo 1482061 3752801 := bstep (se 2 (by rfl) ⟨1407300, by rfl⟩ : syracuseStep 3752801 = 2814601) B2814601
theorem B19006397 : Blo 1482061 19006397 := bstep (se 3 (by rfl) ⟨3563699, by rfl⟩ : syracuseStep 19006397 = 7127399) B7127399
theorem B16901135 : Blo 1482061 16901135 := bstep (se 1 (by rfl) ⟨12675851, by rfl⟩ : syracuseStep 16901135 = 25351703) B25351703
theorem B1877023 : Blo 1482061 1877023 := bstep (se 1 (by rfl) ⟨1407767, by rfl⟩ : syracuseStep 1877023 = 2815535) B2815535
theorem B16254047 : Blo 1482061 16254047 := bstep (se 1 (by rfl) ⟨12190535, by rfl⟩ : syracuseStep 16254047 = 24381071) B24381071
theorem B17130635 : Blo 1482061 17130635 := bstep (se 1 (by rfl) ⟨12847976, by rfl⟩ : syracuseStep 17130635 = 25695953) B25695953
theorem B14255261 : Blo 1482061 14255261 := bstep (se 3 (by rfl) ⟨2672861, by rfl⟩ : syracuseStep 14255261 = 5345723) B5345723
theorem B4007087 : Blo 1482061 4007087 := bstep (se 1 (by rfl) ⟨3005315, by rfl⟩ : syracuseStep 4007087 = 6010631) B6010631
theorem B1484015 : Blo 1482061 1484015 := bstep (se 1 (by rfl) ⟨1113011, by rfl⟩ : syracuseStep 1484015 = 2226023) B2226023
theorem B3753641 : Blo 1482061 3753641 := bstep (se 2 (by rfl) ⟨1407615, by rfl⟩ : syracuseStep 3753641 = 2815231) B2815231
theorem B5007095 : Blo 1482061 5007095 := bstep (se 1 (by rfl) ⟨3755321, by rfl⟩ : syracuseStep 5007095 = 7510643) B7510643
theorem B3335975 : Blo 1482061 3335975 := bstep (se 1 (by rfl) ⟨2501981, by rfl⟩ : syracuseStep 3335975 = 5003963) B5003963
theorem B3336047 : Blo 1482061 3336047 := bstep (se 1 (by rfl) ⟨2502035, by rfl⟩ : syracuseStep 3336047 = 5004071) B5004071
theorem B3336263 : Blo 1482061 3336263 := bstep (se 1 (by rfl) ⟨2502197, by rfl⟩ : syracuseStep 3336263 = 5004395) B5004395
theorem B8448563 : Blo 1482061 8448563 := bstep (se 1 (by rfl) ⟨6336422, by rfl⟩ : syracuseStep 8448563 = 12672845) B12672845
theorem B8448745 : Blo 1482061 8448745 := bstep (se 2 (by rfl) ⟨3168279, by rfl⟩ : syracuseStep 8448745 = 6336559) B6336559
theorem B46934891 : Blo 1482061 46934891 := bstep (se 1 (by rfl) ⟨35201168, by rfl⟩ : syracuseStep 46934891 = 70402337) B70402337
theorem B3337271 : Blo 1482061 3337271 := bstep (se 1 (by rfl) ⟨2502953, by rfl⟩ : syracuseStep 3337271 = 5005907) B5005907
theorem B21982373 : Blo 1482061 21982373 := bstep (se 4 (by rfl) ⟨2060847, by rfl⟩ : syracuseStep 21982373 = 4121695) B4121695
theorem B3337631 : Blo 1482061 3337631 := bstep (se 1 (by rfl) ⟨2503223, by rfl⟩ : syracuseStep 3337631 = 5006447) B5006447
theorem B2223671 : Blo 1482061 2223671 := bstep (se 1 (by rfl) ⟨1667753, by rfl⟩ : syracuseStep 2223671 = 3335507) B3335507
theorem B4222631 : Blo 1482061 4222631 := bstep (se 1 (by rfl) ⟨3166973, by rfl⟩ : syracuseStep 4222631 = 6333947) B6333947
theorem B8793775 : Blo 1482061 8793775 := bstep (se 1 (by rfl) ⟨6595331, by rfl⟩ : syracuseStep 8793775 = 13190663) B13190663
theorem B2223839 : Blo 1482061 2223839 := bstep (se 1 (by rfl) ⟨1667879, by rfl⟩ : syracuseStep 2223839 = 3335759) B3335759
theorem B2224235 : Blo 1482061 2224235 := bstep (se 1 (by rfl) ⟨1668176, by rfl⟩ : syracuseStep 2224235 = 3336353) B3336353
theorem B18993275 : Blo 1482061 18993275 := bstep (se 1 (by rfl) ⟨14244956, by rfl⟩ : syracuseStep 18993275 = 28489913) B28489913
theorem B2224319 : Blo 1482061 2224319 := bstep (se 1 (by rfl) ⟨1668239, by rfl⟩ : syracuseStep 2224319 = 3336479) B3336479
theorem B9507071 : Blo 1482061 9507071 := bstep (se 1 (by rfl) ⟨7130303, by rfl⟩ : syracuseStep 9507071 = 14260607) B14260607
theorem B11268395 : Blo 1482061 11268395 := bstep (se 1 (by rfl) ⟨8451296, by rfl⟩ : syracuseStep 11268395 = 16902593) B16902593
theorem B21377357 : Blo 1482061 21377357 := bstep (se 3 (by rfl) ⟨4008254, by rfl⟩ : syracuseStep 21377357 = 8016509) B8016509
theorem B10695023 : Blo 1482061 10695023 := bstep (se 1 (by rfl) ⟨8021267, by rfl⟩ : syracuseStep 10695023 = 16042535) B16042535
theorem B8450477 : Blo 1482061 8450477 := bstep (se 3 (by rfl) ⟨1584464, by rfl⟩ : syracuseStep 8450477 = 3168929) B3168929
theorem B3166879 : Blo 1482061 3166879 := bstep (se 1 (by rfl) ⟨2375159, by rfl⟩ : syracuseStep 3166879 = 4750319) B4750319
theorem B2224967 : Blo 1482061 2224967 := bstep (se 1 (by rfl) ⟨1668725, by rfl⟩ : syracuseStep 2224967 = 3337451) B3337451
theorem B40104935 : Blo 1482061 40104935 := bstep (se 1 (by rfl) ⟨30078701, by rfl⟩ : syracuseStep 40104935 = 60157403) B60157403
theorem B1668127 : Blo 1482061 1668127 := bstep (se 1 (by rfl) ⟨1251095, by rfl⟩ : syracuseStep 1668127 = 2502191) B2502191
theorem B6009983 : Blo 1482061 6009983 := bstep (se 1 (by rfl) ⟨4507487, by rfl⟩ : syracuseStep 6009983 = 9014975) B9014975
theorem B79164599 : Blo 1482061 79164599 := bstep (se 1 (by rfl) ⟨59373449, by rfl⟩ : syracuseStep 79164599 = 118746899) B118746899
theorem B7222459 : Blo 1482061 7222459 := bstep (se 1 (by rfl) ⟨5416844, by rfl⟩ : syracuseStep 7222459 = 10833689) B10833689
theorem B19256563 : Blo 1482061 19256563 := bstep (se 1 (by rfl) ⟨14442422, by rfl⟩ : syracuseStep 19256563 = 28884845) B28884845
theorem B3380507 : Blo 1482061 3380507 := bstep (se 1 (by rfl) ⟨2535380, by rfl⟩ : syracuseStep 3380507 = 5070761) B5070761
theorem B2225771 : Blo 1482061 2225771 := bstep (se 1 (by rfl) ⟨1669328, by rfl⟩ : syracuseStep 2225771 = 3338657) B3338657
theorem B32487065 : Blo 1482061 32487065 := bstep (se 2 (by rfl) ⟨12182649, by rfl⟩ : syracuseStep 32487065 = 24365299) B24365299
theorem B2225819 : Blo 1482061 2225819 := bstep (se 1 (by rfl) ⟨1669364, by rfl⟩ : syracuseStep 2225819 = 3338729) B3338729
theorem B7510319 : Blo 1482061 7510319 := bstep (se 1 (by rfl) ⟨5632739, by rfl⟩ : syracuseStep 7510319 = 11265479) B11265479
theorem B2005403 : Blo 1482061 2005403 := bstep (se 1 (by rfl) ⟨1504052, by rfl⟩ : syracuseStep 2005403 = 3008105) B3008105
theorem B34724389 : Blo 1482061 34724389 := bstep (se 4 (by rfl) ⟨3255411, by rfl⟩ : syracuseStep 34724389 = 6510823) B6510823
theorem B4226003 : Blo 1482061 4226003 := bstep (se 1 (by rfl) ⟨3169502, by rfl⟩ : syracuseStep 4226003 = 6339005) B6339005
theorem B7511291 : Blo 1482061 7511291 := bstep (se 1 (by rfl) ⟨5633468, by rfl⟩ : syracuseStep 7511291 = 11266937) B11266937
theorem B38526347 : Blo 1482061 38526347 := bstep (se 1 (by rfl) ⟨28894760, by rfl⟩ : syracuseStep 38526347 = 57789521) B57789521
theorem B1482139 : Blo 1482061 1482139 := bstep (se 1 (by rfl) ⟨1111604, by rfl⟩ : syracuseStep 1482139 = 2223209) B2223209
theorem B11263535 : Blo 1482061 11263535 := bstep (se 1 (by rfl) ⟨8447651, by rfl⟩ : syracuseStep 11263535 = 16895303) B16895303
theorem B1482399 : Blo 1482061 1482399 := bstep (se 1 (by rfl) ⟨1111799, by rfl⟩ : syracuseStep 1482399 = 2223599) B2223599
theorem B14245571 : Blo 1482061 14245571 := bstep (se 1 (by rfl) ⟨10684178, by rfl⟩ : syracuseStep 14245571 = 21368357) B21368357
theorem B1482491 : Blo 1482061 1482491 := bstep (se 1 (by rfl) ⟨1111868, by rfl⟩ : syracuseStep 1482491 = 2223737) B2223737
theorem B2375659 : Blo 1482061 2375659 := bstep (se 1 (by rfl) ⟨1781744, by rfl⟩ : syracuseStep 2375659 = 3563489) B3563489
theorem B2375743 : Blo 1482061 2375743 := bstep (se 1 (by rfl) ⟨1781807, by rfl⟩ : syracuseStep 2375743 = 3563615) B3563615
theorem B1482823 : Blo 1482061 1482823 := bstep (se 1 (by rfl) ⟨1112117, by rfl⟩ : syracuseStep 1482823 = 2224235) B2224235
theorem B1482879 : Blo 1482061 1482879 := bstep (se 1 (by rfl) ⟨1112159, by rfl⟩ : syracuseStep 1482879 = 2224319) B2224319
theorem B7512263 : Blo 1482061 7512263 := bstep (se 1 (by rfl) ⟨5634197, by rfl⟩ : syracuseStep 7512263 = 11268395) B11268395
theorem B3752315 : Blo 1482061 3752315 := bstep (se 1 (by rfl) ⟨2814236, by rfl⟩ : syracuseStep 3752315 = 5628473) B5628473
theorem B1483311 : Blo 1482061 1483311 := bstep (se 1 (by rfl) ⟨1112483, by rfl⟩ : syracuseStep 1483311 = 2224967) B2224967
theorem B4006655 : Blo 1482061 4006655 := bstep (se 1 (by rfl) ⟨3004991, by rfl⟩ : syracuseStep 4006655 = 6009983) B6009983
theorem B11420423 : Blo 1482061 11420423 := bstep (se 1 (by rfl) ⟨8565317, by rfl⟩ : syracuseStep 11420423 = 17130635) B17130635
theorem B9503507 : Blo 1482061 9503507 := bstep (se 1 (by rfl) ⟨7127630, by rfl⟩ : syracuseStep 9503507 = 14255261) B14255261
theorem B2671391 : Blo 1482061 2671391 := bstep (se 1 (by rfl) ⟨2003543, by rfl⟩ : syracuseStep 2671391 = 4007087) B4007087
theorem B2253671 : Blo 1482061 2253671 := bstep (se 1 (by rfl) ⟨1690253, by rfl⟩ : syracuseStep 2253671 = 3380507) B3380507
theorem B46900133 : Blo 1482061 46900133 := bstep (se 4 (by rfl) ⟨4396887, by rfl⟩ : syracuseStep 46900133 = 8793775) B8793775
theorem B11264993 : Blo 1482061 11264993 := bstep (se 2 (by rfl) ⟨4224372, by rfl⟩ : syracuseStep 11264993 = 8448745) B8448745
theorem B1483847 : Blo 1482061 1483847 := bstep (se 1 (by rfl) ⟨1112885, by rfl⟩ : syracuseStep 1483847 = 2225771) B2225771
theorem B1483879 : Blo 1482061 1483879 := bstep (se 1 (by rfl) ⟨1112909, by rfl⟩ : syracuseStep 1483879 = 2225819) B2225819
theorem B5006879 : Blo 1482061 5006879 := bstep (se 1 (by rfl) ⟨3755159, by rfl⟩ : syracuseStep 5006879 = 7510319) B7510319
theorem B21390965 : Blo 1482061 21390965 := bstep (se 5 (by rfl) ⟨1002701, by rfl⟩ : syracuseStep 21390965 = 2005403) B2005403
theorem B25675417 : Blo 1482061 25675417 := bstep (se 2 (by rfl) ⟨9628281, by rfl⟩ : syracuseStep 25675417 = 19256563) B19256563
theorem B37988189 : Blo 1482061 37988189 := bstep (se 3 (by rfl) ⟨7122785, by rfl⟩ : syracuseStep 37988189 = 14245571) B14245571
theorem B5007527 : Blo 1482061 5007527 := bstep (se 1 (by rfl) ⟨3755645, by rfl⟩ : syracuseStep 5007527 = 7511291) B7511291
theorem B25684231 : Blo 1482061 25684231 := bstep (se 1 (by rfl) ⟨19263173, by rfl⟩ : syracuseStep 25684231 = 38526347) B38526347
theorem B6335329 : Blo 1482061 6335329 := bstep (se 2 (by rfl) ⟨2375748, by rfl⟩ : syracuseStep 6335329 = 4751497) B4751497
theorem B7130015 : Blo 1482061 7130015 := bstep (se 1 (by rfl) ⟨5347511, by rfl⟩ : syracuseStep 7130015 = 10695023) B10695023
theorem B8449019 : Blo 1482061 8449019 := bstep (se 1 (by rfl) ⟨6336764, by rfl⟩ : syracuseStep 8449019 = 12673529) B12673529
theorem B2223131 : Blo 1482061 2223131 := bstep (se 1 (by rfl) ⟨1667348, by rfl⟩ : syracuseStep 2223131 = 3334697) B3334697
theorem B2501867 : Blo 1482061 2501867 := bstep (se 1 (by rfl) ⟨1876400, by rfl⟩ : syracuseStep 2501867 = 3752801) B3752801
theorem B11267423 : Blo 1482061 11267423 := bstep (se 1 (by rfl) ⟨8450567, by rfl⟩ : syracuseStep 11267423 = 16901135) B16901135
theorem B4222505 : Blo 1482061 4222505 := bstep (se 2 (by rfl) ⟨1583439, by rfl⟩ : syracuseStep 4222505 = 3166879) B3166879
theorem B2502427 : Blo 1482061 2502427 := bstep (se 1 (by rfl) ⟨1876820, by rfl⟩ : syracuseStep 2502427 = 3753641) B3753641
theorem B3338063 : Blo 1482061 3338063 := bstep (se 1 (by rfl) ⟨2503547, by rfl⟩ : syracuseStep 3338063 = 5007095) B5007095
theorem B2223983 : Blo 1482061 2223983 := bstep (se 1 (by rfl) ⟨1667987, by rfl⟩ : syracuseStep 2223983 = 3335975) B3335975
theorem B2224031 : Blo 1482061 2224031 := bstep (se 1 (by rfl) ⟨1668023, by rfl⟩ : syracuseStep 2224031 = 3336047) B3336047
theorem B2224169 : Blo 1482061 2224169 := bstep (se 2 (by rfl) ⟨834063, by rfl⟩ : syracuseStep 2224169 = 1668127) B1668127
theorem B2502697 : Blo 1482061 2502697 := bstep (se 2 (by rfl) ⟨938511, by rfl⟩ : syracuseStep 2502697 = 1877023) B1877023
theorem B2224175 : Blo 1482061 2224175 := bstep (se 1 (by rfl) ⟨1668131, by rfl⟩ : syracuseStep 2224175 = 3336263) B3336263
theorem B9629945 : Blo 1482061 9629945 := bstep (se 2 (by rfl) ⟨3611229, by rfl⟩ : syracuseStep 9629945 = 7222459) B7222459
theorem B5632375 : Blo 1482061 5632375 := bstep (se 1 (by rfl) ⟨4224281, by rfl⟩ : syracuseStep 5632375 = 8448563) B8448563
theorem B31289927 : Blo 1482061 31289927 := bstep (se 1 (by rfl) ⟨23467445, by rfl⟩ : syracuseStep 31289927 = 46934891) B46934891
theorem B2224847 : Blo 1482061 2224847 := bstep (se 1 (by rfl) ⟨1668635, by rfl⟩ : syracuseStep 2224847 = 3337271) B3337271
theorem B2225087 : Blo 1482061 2225087 := bstep (se 1 (by rfl) ⟨1668815, by rfl⟩ : syracuseStep 2225087 = 3337631) B3337631
theorem B7509023 : Blo 1482061 7509023 := bstep (se 1 (by rfl) ⟨5631767, by rfl⟩ : syracuseStep 7509023 = 11263535) B11263535
theorem B2815087 : Blo 1482061 2815087 := bstep (se 1 (by rfl) ⟨2111315, by rfl⟩ : syracuseStep 2815087 = 4222631) B4222631
theorem B12670181 : Blo 1482061 12670181 := bstep (se 4 (by rfl) ⟨1187829, by rfl⟩ : syracuseStep 12670181 = 2375659) B2375659
theorem B12662183 : Blo 1482061 12662183 := bstep (se 1 (by rfl) ⟨9496637, by rfl⟩ : syracuseStep 12662183 = 18993275) B18993275
theorem B6338047 : Blo 1482061 6338047 := bstep (se 1 (by rfl) ⟨4753535, by rfl⟩ : syracuseStep 6338047 = 9507071) B9507071
theorem B14251571 : Blo 1482061 14251571 := bstep (se 1 (by rfl) ⟨10688678, by rfl⟩ : syracuseStep 14251571 = 21377357) B21377357
theorem B5633651 : Blo 1482061 5633651 := bstep (se 1 (by rfl) ⟨4225238, by rfl⟩ : syracuseStep 5633651 = 8450477) B8450477
theorem B9016967 : Blo 1482061 9016967 := bstep (se 1 (by rfl) ⟨6762725, by rfl⟩ : syracuseStep 9016967 = 13525451) B13525451
theorem B5002991 : Blo 1482061 5002991 := bstep (se 1 (by rfl) ⟨3752243, by rfl⟩ : syracuseStep 5002991 = 7504487) B7504487
theorem B211105597 : Blo 1482061 211105597 := bstep (se 3 (by rfl) ⟨39582299, by rfl⟩ : syracuseStep 211105597 = 79164599) B79164599
theorem B12670931 : Blo 1482061 12670931 := bstep (se 1 (by rfl) ⟨9503198, by rfl⟩ : syracuseStep 12670931 = 19006397) B19006397
theorem B26736623 : Blo 1482061 26736623 := bstep (se 1 (by rfl) ⟨20052467, by rfl⟩ : syracuseStep 26736623 = 40104935) B40104935
theorem B46299185 : Blo 1482061 46299185 := bstep (se 2 (by rfl) ⟨17362194, by rfl⟩ : syracuseStep 46299185 = 34724389) B34724389
theorem B10836031 : Blo 1482061 10836031 := bstep (se 1 (by rfl) ⟨8127023, by rfl⟩ : syracuseStep 10836031 = 16254047) B16254047
theorem B21658043 : Blo 1482061 21658043 := bstep (se 1 (by rfl) ⟨16243532, by rfl⟩ : syracuseStep 21658043 = 32487065) B32487065
theorem B2817335 : Blo 1482061 2817335 := bstep (se 1 (by rfl) ⟨2113001, by rfl⟩ : syracuseStep 2817335 = 4226003) B4226003
theorem B14654915 : Blo 1482061 14654915 := bstep (se 1 (by rfl) ⟨10991186, by rfl⟩ : syracuseStep 14654915 = 21982373) B21982373
theorem B1482447 : Blo 1482061 1482447 := bstep (se 1 (by rfl) ⟨1111835, by rfl⟩ : syracuseStep 1482447 = 2223671) B2223671
theorem B1482559 : Blo 1482061 1482559 := bstep (se 1 (by rfl) ⟨1111919, by rfl⟩ : syracuseStep 1482559 = 2223839) B2223839
theorem B1482779 : Blo 1482061 1482779 := bstep (se 1 (by rfl) ⟨1112084, by rfl⟩ : syracuseStep 1482779 = 2224169) B2224169
theorem B1482783 : Blo 1482061 1482783 := bstep (se 1 (by rfl) ⟨1112087, by rfl⟩ : syracuseStep 1482783 = 2224175) B2224175
theorem B1483231 : Blo 1482061 1483231 := bstep (se 1 (by rfl) ⟨1112423, by rfl⟩ : syracuseStep 1483231 = 2224847) B2224847
theorem B2671103 : Blo 1482061 2671103 := bstep (se 1 (by rfl) ⟨2003327, by rfl⟩ : syracuseStep 2671103 = 4006655) B4006655
theorem B1483391 : Blo 1482061 1483391 := bstep (se 1 (by rfl) ⟨1112543, by rfl⟩ : syracuseStep 1483391 = 2225087) B2225087
theorem B5006015 : Blo 1482061 5006015 := bstep (se 1 (by rfl) ⟨3754511, by rfl⟩ : syracuseStep 5006015 = 7509023) B7509023
theorem B333759221 : Blo 1482061 333759221 := bstep (se 5 (by rfl) ⟨15644963, by rfl⟩ : syracuseStep 333759221 = 31289927) B31289927
theorem B8446787 : Blo 1482061 8446787 := bstep (se 1 (by rfl) ⟨6335090, by rfl⟩ : syracuseStep 8446787 = 12670181) B12670181
theorem B8447105 : Blo 1482061 8447105 := bstep (se 2 (by rfl) ⟨3167664, by rfl⟩ : syracuseStep 8447105 = 6335329) B6335329
theorem B3335327 : Blo 1482061 3335327 := bstep (se 1 (by rfl) ⟨2501495, by rfl⟩ : syracuseStep 3335327 = 5002991) B5002991
theorem B8447287 : Blo 1482061 8447287 := bstep (se 1 (by rfl) ⟨6335465, by rfl⟩ : syracuseStep 8447287 = 12670931) B12670931
theorem B3753449 : Blo 1482061 3753449 := bstep (se 2 (by rfl) ⟨1407543, by rfl⟩ : syracuseStep 3753449 = 2815087) B2815087
theorem B24045245 : Blo 1482061 24045245 := bstep (se 3 (by rfl) ⟨4508483, by rfl⟩ : syracuseStep 24045245 = 9016967) B9016967
theorem B4753343 : Blo 1482061 4753343 := bstep (se 1 (by rfl) ⟨3565007, by rfl⟩ : syracuseStep 4753343 = 7130015) B7130015
theorem B1878223 : Blo 1482061 1878223 := bstep (se 1 (by rfl) ⟨1408667, by rfl⟩ : syracuseStep 1878223 = 2817335) B2817335
theorem B3336569 : Blo 1482061 3336569 := bstep (se 2 (by rfl) ⟨1251213, by rfl⟩ : syracuseStep 3336569 = 2502427) B2502427
theorem B285190645 : Blo 1482061 285190645 := bstep (se 5 (by rfl) ⟨13368311, by rfl⟩ : syracuseStep 285190645 = 26736623) B26736623
theorem B3336929 : Blo 1482061 3336929 := bstep (se 2 (by rfl) ⟨1251348, by rfl⟩ : syracuseStep 3336929 = 2502697) B2502697
theorem B5008175 : Blo 1482061 5008175 := bstep (se 1 (by rfl) ⟨3756131, by rfl⟩ : syracuseStep 5008175 = 7512263) B7512263
theorem B2501543 : Blo 1482061 2501543 := bstep (se 1 (by rfl) ⟨1876157, by rfl⟩ : syracuseStep 2501543 = 3752315) B3752315
theorem B34245641 : Blo 1482061 34245641 := bstep (se 2 (by rfl) ⟨12842115, by rfl⟩ : syracuseStep 34245641 = 25684231) B25684231
theorem B7613615 : Blo 1482061 7613615 := bstep (se 1 (by rfl) ⟨5710211, by rfl⟩ : syracuseStep 7613615 = 11420423) B11420423
theorem B6335671 : Blo 1482061 6335671 := bstep (se 1 (by rfl) ⟨4751753, by rfl⟩ : syracuseStep 6335671 = 9503507) B9503507
theorem B1502447 : Blo 1482061 1502447 := bstep (se 1 (by rfl) ⟨1126835, by rfl⟩ : syracuseStep 1502447 = 2253671) B2253671
theorem B8441455 : Blo 1482061 8441455 := bstep (se 1 (by rfl) ⟨6331091, by rfl⟩ : syracuseStep 8441455 = 12662183) B12662183
theorem B3337919 : Blo 1482061 3337919 := bstep (se 1 (by rfl) ⟨2503439, by rfl⟩ : syracuseStep 3337919 = 5006879) B5006879
theorem B3755767 : Blo 1482061 3755767 := bstep (se 1 (by rfl) ⟨2816825, by rfl⟩ : syracuseStep 3755767 = 5633651) B5633651
theorem B25325459 : Blo 1482061 25325459 := bstep (se 1 (by rfl) ⟨18994094, by rfl⟩ : syracuseStep 25325459 = 37988189) B37988189
theorem B3338351 : Blo 1482061 3338351 := bstep (se 1 (by rfl) ⟨2503763, by rfl⟩ : syracuseStep 3338351 = 5007527) B5007527
theorem B14438695 : Blo 1482061 14438695 := bstep (se 1 (by rfl) ⟨10829021, by rfl⟩ : syracuseStep 14438695 = 21658043) B21658043
theorem B5632679 : Blo 1482061 5632679 := bstep (se 1 (by rfl) ⟨4224509, by rfl⟩ : syracuseStep 5632679 = 8449019) B8449019
theorem B8450729 : Blo 1482061 8450729 := bstep (se 2 (by rfl) ⟨3169023, by rfl⟩ : syracuseStep 8450729 = 6338047) B6338047
theorem B7123709 : Blo 1482061 7123709 := bstep (se 3 (by rfl) ⟨1335695, by rfl⟩ : syracuseStep 7123709 = 2671391) B2671391
theorem B1667911 : Blo 1482061 1667911 := bstep (se 1 (by rfl) ⟨1250933, by rfl⟩ : syracuseStep 1667911 = 2501867) B2501867
theorem B9769943 : Blo 1482061 9769943 := bstep (se 1 (by rfl) ⟨7327457, by rfl⟩ : syracuseStep 9769943 = 14654915) B14654915
theorem B2815003 : Blo 1482061 2815003 := bstep (se 1 (by rfl) ⟨2111252, by rfl⟩ : syracuseStep 2815003 = 4222505) B4222505
theorem B281474129 : Blo 1482061 281474129 := bstep (se 2 (by rfl) ⟨105552798, by rfl⟩ : syracuseStep 281474129 = 211105597) B211105597
theorem B2225375 : Blo 1482061 2225375 := bstep (se 1 (by rfl) ⟨1669031, by rfl⟩ : syracuseStep 2225375 = 3338063) B3338063
theorem B14448041 : Blo 1482061 14448041 := bstep (se 2 (by rfl) ⟨5418015, by rfl⟩ : syracuseStep 14448041 = 10836031) B10836031
theorem B3167657 : Blo 1482061 3167657 := bstep (se 2 (by rfl) ⟨1187871, by rfl⟩ : syracuseStep 3167657 = 2375743) B2375743
theorem B6419963 : Blo 1482061 6419963 := bstep (se 1 (by rfl) ⟨4814972, by rfl⟩ : syracuseStep 6419963 = 9629945) B9629945
theorem B7509833 : Blo 1482061 7509833 := bstep (se 2 (by rfl) ⟨2816187, by rfl⟩ : syracuseStep 7509833 = 5632375) B5632375
theorem B31266755 : Blo 1482061 31266755 := bstep (se 1 (by rfl) ⟨23450066, by rfl⟩ : syracuseStep 31266755 = 46900133) B46900133
theorem B7509995 : Blo 1482061 7509995 := bstep (se 1 (by rfl) ⟨5632496, by rfl⟩ : syracuseStep 7509995 = 11264993) B11264993
theorem B9501047 : Blo 1482061 9501047 := bstep (se 1 (by rfl) ⟨7125785, by rfl⟩ : syracuseStep 9501047 = 14251571) B14251571
theorem B14260643 : Blo 1482061 14260643 := bstep (se 1 (by rfl) ⟨10695482, by rfl⟩ : syracuseStep 14260643 = 21390965) B21390965
theorem B30866123 : Blo 1482061 30866123 := bstep (se 1 (by rfl) ⟨23149592, by rfl⟩ : syracuseStep 30866123 = 46299185) B46299185
theorem B1482087 : Blo 1482061 1482087 := bstep (se 1 (by rfl) ⟨1111565, by rfl⟩ : syracuseStep 1482087 = 2223131) B2223131
theorem B34233889 : Blo 1482061 34233889 := bstep (se 2 (by rfl) ⟨12837708, by rfl⟩ : syracuseStep 34233889 = 25675417) B25675417
theorem B7511615 : Blo 1482061 7511615 := bstep (se 1 (by rfl) ⟨5633711, by rfl⟩ : syracuseStep 7511615 = 11267423) B11267423
theorem B1482655 : Blo 1482061 1482655 := bstep (se 1 (by rfl) ⟨1111991, by rfl⟩ : syracuseStep 1482655 = 2223983) B2223983
theorem B1482687 : Blo 1482061 1482687 := bstep (se 1 (by rfl) ⟨1112015, by rfl⟩ : syracuseStep 1482687 = 2224031) B2224031
theorem B19251593 : Blo 1482061 19251593 := bstep (se 2 (by rfl) ⟨7219347, by rfl⟩ : syracuseStep 19251593 = 14438695) B14438695
theorem B4006525 : Blo 1482061 4006525 := bstep (se 3 (by rfl) ⟨751223, by rfl⟩ : syracuseStep 4006525 = 1502447) B1502447
theorem B6513295 : Blo 1482061 6513295 := bstep (se 1 (by rfl) ⟨4884971, by rfl⟩ : syracuseStep 6513295 = 9769943) B9769943
theorem B1483583 : Blo 1482061 1483583 := bstep (se 1 (by rfl) ⟨1112687, by rfl⟩ : syracuseStep 1483583 = 2225375) B2225375
theorem B5006555 : Blo 1482061 5006555 := bstep (se 1 (by rfl) ⟨3754916, by rfl⟩ : syracuseStep 5006555 = 7509833) B7509833
theorem B5006663 : Blo 1482061 5006663 := bstep (se 1 (by rfl) ⟨3754997, by rfl⟩ : syracuseStep 5006663 = 7509995) B7509995
theorem B3753337 : Blo 1482061 3753337 := bstep (se 2 (by rfl) ⟨1407501, by rfl⟩ : syracuseStep 3753337 = 2815003) B2815003
theorem B8447561 : Blo 1482061 8447561 := bstep (se 2 (by rfl) ⟨3167835, by rfl⟩ : syracuseStep 8447561 = 6335671) B6335671
theorem B6334031 : Blo 1482061 6334031 := bstep (se 1 (by rfl) ⟨4750523, by rfl⟩ : syracuseStep 6334031 = 9501047) B9501047
theorem B5007689 : Blo 1482061 5007689 := bstep (se 2 (by rfl) ⟨1877883, by rfl⟩ : syracuseStep 5007689 = 3755767) B3755767
theorem B5007743 : Blo 1482061 5007743 := bstep (se 1 (by rfl) ⟨3755807, by rfl⟩ : syracuseStep 5007743 = 7511615) B7511615
theorem B3755119 : Blo 1482061 3755119 := bstep (se 1 (by rfl) ⟨2816339, by rfl⟩ : syracuseStep 3755119 = 5632679) B5632679
theorem B3337343 : Blo 1482061 3337343 := bstep (se 1 (by rfl) ⟨2503007, by rfl⟩ : syracuseStep 3337343 = 5006015) B5006015
theorem B222506147 : Blo 1482061 222506147 := bstep (se 1 (by rfl) ⟨166879610, by rfl⟩ : syracuseStep 222506147 = 333759221) B333759221
theorem B5631191 : Blo 1482061 5631191 := bstep (se 1 (by rfl) ⟨4223393, by rfl⟩ : syracuseStep 5631191 = 8446787) B8446787
theorem B187649419 : Blo 1482061 187649419 := bstep (se 1 (by rfl) ⟨140737064, by rfl⟩ : syracuseStep 187649419 = 281474129) B281474129
theorem B5631403 : Blo 1482061 5631403 := bstep (se 1 (by rfl) ⟨4223552, by rfl⟩ : syracuseStep 5631403 = 8447105) B8447105
theorem B2223551 : Blo 1482061 2223551 := bstep (se 1 (by rfl) ⟨1667663, by rfl⟩ : syracuseStep 2223551 = 3335327) B3335327
theorem B2502299 : Blo 1482061 2502299 := bstep (se 1 (by rfl) ⟨1876724, by rfl⟩ : syracuseStep 2502299 = 3753449) B3753449
theorem B4279975 : Blo 1482061 4279975 := bstep (se 1 (by rfl) ⟨3209981, by rfl⟩ : syracuseStep 4279975 = 6419963) B6419963
theorem B2223881 : Blo 1482061 2223881 := bstep (se 2 (by rfl) ⟨833955, by rfl⟩ : syracuseStep 2223881 = 1667911) B1667911
theorem B20844503 : Blo 1482061 20844503 := bstep (se 1 (by rfl) ⟨15633377, by rfl⟩ : syracuseStep 20844503 = 31266755) B31266755
theorem B7122941 : Blo 1482061 7122941 := bstep (se 3 (by rfl) ⟨1335551, by rfl⟩ : syracuseStep 7122941 = 2671103) B2671103
theorem B2224379 : Blo 1482061 2224379 := bstep (se 1 (by rfl) ⟨1668284, by rfl⟩ : syracuseStep 2224379 = 3336569) B3336569
theorem B9507095 : Blo 1482061 9507095 := bstep (se 1 (by rfl) ⟨7130321, by rfl⟩ : syracuseStep 9507095 = 14260643) B14260643
theorem B2224619 : Blo 1482061 2224619 := bstep (se 1 (by rfl) ⟨1668464, by rfl⟩ : syracuseStep 2224619 = 3336929) B3336929
theorem B3338783 : Blo 1482061 3338783 := bstep (se 1 (by rfl) ⟨2504087, by rfl⟩ : syracuseStep 3338783 = 5008175) B5008175
theorem B1667695 : Blo 1482061 1667695 := bstep (se 1 (by rfl) ⟨1250771, by rfl⟩ : syracuseStep 1667695 = 2501543) B2501543
theorem B5075743 : Blo 1482061 5075743 := bstep (se 1 (by rfl) ⟨3806807, by rfl⟩ : syracuseStep 5075743 = 7613615) B7613615
theorem B2225279 : Blo 1482061 2225279 := bstep (se 1 (by rfl) ⟨1668959, by rfl⟩ : syracuseStep 2225279 = 3337919) B3337919
theorem B2225567 : Blo 1482061 2225567 := bstep (se 1 (by rfl) ⟨1669175, by rfl⟩ : syracuseStep 2225567 = 3338351) B3338351
theorem B2504297 : Blo 1482061 2504297 := bstep (se 2 (by rfl) ⟨939111, by rfl⟩ : syracuseStep 2504297 = 1878223) B1878223
theorem B5633819 : Blo 1482061 5633819 := bstep (se 1 (by rfl) ⟨4225364, by rfl⟩ : syracuseStep 5633819 = 8450729) B8450729
theorem B4749139 : Blo 1482061 4749139 := bstep (se 1 (by rfl) ⟨3561854, by rfl⟩ : syracuseStep 4749139 = 7123709) B7123709
theorem B380254193 : Blo 1482061 380254193 := bstep (se 2 (by rfl) ⟨142595322, by rfl⟩ : syracuseStep 380254193 = 285190645) B285190645
theorem B9632027 : Blo 1482061 9632027 := bstep (se 1 (by rfl) ⟨7224020, by rfl⟩ : syracuseStep 9632027 = 14448041) B14448041
theorem B2111771 : Blo 1482061 2111771 := bstep (se 1 (by rfl) ⟨1583828, by rfl⟩ : syracuseStep 2111771 = 3167657) B3167657
theorem B16030163 : Blo 1482061 16030163 := bstep (se 1 (by rfl) ⟨12022622, by rfl⟩ : syracuseStep 16030163 = 24045245) B24045245
theorem B3168895 : Blo 1482061 3168895 := bstep (se 1 (by rfl) ⟨2376671, by rfl⟩ : syracuseStep 3168895 = 4753343) B4753343
theorem B11263049 : Blo 1482061 11263049 := bstep (se 2 (by rfl) ⟨4223643, by rfl⟩ : syracuseStep 11263049 = 8447287) B8447287
theorem B20577415 : Blo 1482061 20577415 := bstep (se 1 (by rfl) ⟨15433061, by rfl⟩ : syracuseStep 20577415 = 30866123) B30866123
theorem B22830427 : Blo 1482061 22830427 := bstep (se 1 (by rfl) ⟨17122820, by rfl⟩ : syracuseStep 22830427 = 34245641) B34245641
theorem B45645185 : Blo 1482061 45645185 := bstep (se 2 (by rfl) ⟨17116944, by rfl⟩ : syracuseStep 45645185 = 34233889) B34233889
theorem B11255273 : Blo 1482061 11255273 := bstep (se 2 (by rfl) ⟨4220727, by rfl⟩ : syracuseStep 11255273 = 8441455) B8441455
theorem B16883639 : Blo 1482061 16883639 := bstep (se 1 (by rfl) ⟨12662729, by rfl⟩ : syracuseStep 16883639 = 25325459) B25325459
theorem B1482919 : Blo 1482061 1482919 := bstep (se 1 (by rfl) ⟨1112189, by rfl⟩ : syracuseStep 1482919 = 2224379) B2224379
theorem B1483079 : Blo 1482061 1483079 := bstep (se 1 (by rfl) ⟨1112309, by rfl⟩ : syracuseStep 1483079 = 2224619) B2224619
theorem B1483519 : Blo 1482061 1483519 := bstep (se 1 (by rfl) ⟨1112639, by rfl⟩ : syracuseStep 1483519 = 2225279) B2225279
theorem B5342033 : Blo 1482061 5342033 := bstep (se 2 (by rfl) ⟨2003262, by rfl⟩ : syracuseStep 5342033 = 4006525) B4006525
theorem B1483711 : Blo 1482061 1483711 := bstep (se 1 (by rfl) ⟨1112783, by rfl⟩ : syracuseStep 1483711 = 2225567) B2225567
theorem B6767657 : Blo 1482061 6767657 := bstep (se 2 (by rfl) ⟨2537871, by rfl⟩ : syracuseStep 6767657 = 5075743) B5075743
theorem B42747101 : Blo 1482061 42747101 := bstep (se 3 (by rfl) ⟨8015081, by rfl⟩ : syracuseStep 42747101 = 16030163) B16030163
theorem B253502795 : Blo 1482061 253502795 := bstep (se 1 (by rfl) ⟨190127096, by rfl⟩ : syracuseStep 253502795 = 380254193) B380254193
theorem B5006825 : Blo 1482061 5006825 := bstep (se 2 (by rfl) ⟨1877559, by rfl⟩ : syracuseStep 5006825 = 3755119) B3755119
theorem B27436553 : Blo 1482061 27436553 := bstep (se 2 (by rfl) ⟨10288707, by rfl⟩ : syracuseStep 27436553 = 20577415) B20577415
theorem B3754127 : Blo 1482061 3754127 := bstep (se 1 (by rfl) ⟨2815595, by rfl⟩ : syracuseStep 3754127 = 5631191) B5631191
theorem B13896335 : Blo 1482061 13896335 := bstep (se 1 (by rfl) ⟨10422251, by rfl⟩ : syracuseStep 13896335 = 20844503) B20844503
theorem B593349725 : Blo 1482061 593349725 := bstep (se 3 (by rfl) ⟨111253073, by rfl⟩ : syracuseStep 593349725 = 222506147) B222506147
theorem B5631389 : Blo 1482061 5631389 := bstep (se 3 (by rfl) ⟨1055885, by rfl⟩ : syracuseStep 5631389 = 2111771) B2111771
theorem B3337703 : Blo 1482061 3337703 := bstep (se 1 (by rfl) ⟨2503277, by rfl⟩ : syracuseStep 3337703 = 5006555) B5006555
theorem B2223593 : Blo 1482061 2223593 := bstep (se 2 (by rfl) ⟨833847, by rfl⟩ : syracuseStep 2223593 = 1667695) B1667695
theorem B22826533 : Blo 1482061 22826533 := bstep (se 4 (by rfl) ⟨2139987, by rfl⟩ : syracuseStep 22826533 = 4279975) B4279975
theorem B3337775 : Blo 1482061 3337775 := bstep (se 1 (by rfl) ⟨2503331, by rfl⟩ : syracuseStep 3337775 = 5006663) B5006663
theorem B5631707 : Blo 1482061 5631707 := bstep (se 1 (by rfl) ⟨4223780, by rfl⟩ : syracuseStep 5631707 = 8447561) B8447561
theorem B4222687 : Blo 1482061 4222687 := bstep (se 1 (by rfl) ⟨3167015, by rfl⟩ : syracuseStep 4222687 = 6334031) B6334031
theorem B3755879 : Blo 1482061 3755879 := bstep (se 1 (by rfl) ⟨2816909, by rfl⟩ : syracuseStep 3755879 = 5633819) B5633819
theorem B3338459 : Blo 1482061 3338459 := bstep (se 1 (by rfl) ⟨2503844, by rfl⟩ : syracuseStep 3338459 = 5007689) B5007689
theorem B3338495 : Blo 1482061 3338495 := bstep (se 1 (by rfl) ⟨2503871, by rfl⟩ : syracuseStep 3338495 = 5007743) B5007743
theorem B7508537 : Blo 1482061 7508537 := bstep (se 2 (by rfl) ⟨2815701, by rfl⟩ : syracuseStep 7508537 = 5631403) B5631403
theorem B7508699 : Blo 1482061 7508699 := bstep (se 1 (by rfl) ⟨5631524, by rfl⟩ : syracuseStep 7508699 = 11263049) B11263049
theorem B2224895 : Blo 1482061 2224895 := bstep (se 1 (by rfl) ⟨1668671, by rfl⟩ : syracuseStep 2224895 = 3337343) B3337343
theorem B30430123 : Blo 1482061 30430123 := bstep (se 1 (by rfl) ⟨22822592, by rfl⟩ : syracuseStep 30430123 = 45645185) B45645185
theorem B1668199 : Blo 1482061 1668199 := bstep (se 1 (by rfl) ⟨1251149, by rfl⟩ : syracuseStep 1668199 = 2502299) B2502299
theorem B4748627 : Blo 1482061 4748627 := bstep (se 1 (by rfl) ⟨3561470, by rfl⟩ : syracuseStep 4748627 = 7122941) B7122941
theorem B6338063 : Blo 1482061 6338063 := bstep (se 1 (by rfl) ⟨4753547, by rfl⟩ : syracuseStep 6338063 = 9507095) B9507095
theorem B12834395 : Blo 1482061 12834395 := bstep (se 1 (by rfl) ⟨9625796, by rfl⟩ : syracuseStep 12834395 = 19251593) B19251593
theorem B2225855 : Blo 1482061 2225855 := bstep (se 1 (by rfl) ⟨1669391, by rfl⟩ : syracuseStep 2225855 = 3338783) B3338783
theorem B4225193 : Blo 1482061 4225193 := bstep (se 2 (by rfl) ⟨1584447, by rfl⟩ : syracuseStep 4225193 = 3168895) B3168895
theorem B1669531 : Blo 1482061 1669531 := bstep (se 1 (by rfl) ⟨1252148, by rfl⟩ : syracuseStep 1669531 = 2504297) B2504297
theorem B555801173 : Blo 1482061 555801173 := bstep (se 8 (by rfl) ⟨3256647, by rfl⟩ : syracuseStep 555801173 = 6513295) B6513295
theorem B6421351 : Blo 1482061 6421351 := bstep (se 1 (by rfl) ⟨4816013, by rfl⟩ : syracuseStep 6421351 = 9632027) B9632027
theorem B30440569 : Blo 1482061 30440569 := bstep (se 2 (by rfl) ⟨11415213, by rfl⟩ : syracuseStep 30440569 = 22830427) B22830427
theorem B5004449 : Blo 1482061 5004449 := bstep (se 2 (by rfl) ⟨1876668, by rfl⟩ : syracuseStep 5004449 = 3753337) B3753337
theorem B250199225 : Blo 1482061 250199225 := bstep (se 2 (by rfl) ⟨93824709, by rfl⟩ : syracuseStep 250199225 = 187649419) B187649419
theorem B1482367 : Blo 1482061 1482367 := bstep (se 1 (by rfl) ⟨1111775, by rfl⟩ : syracuseStep 1482367 = 2223551) B2223551
theorem B7503515 : Blo 1482061 7503515 := bstep (se 1 (by rfl) ⟨5627636, by rfl⟩ : syracuseStep 7503515 = 11255273) B11255273
theorem B6332185 : Blo 1482061 6332185 := bstep (se 2 (by rfl) ⟨2374569, by rfl⟩ : syracuseStep 6332185 = 4749139) B4749139
theorem B1482587 : Blo 1482061 1482587 := bstep (se 1 (by rfl) ⟨1111940, by rfl⟩ : syracuseStep 1482587 = 2223881) B2223881
theorem B11255759 : Blo 1482061 11255759 := bstep (se 1 (by rfl) ⟨8441819, by rfl⟩ : syracuseStep 11255759 = 16883639) B16883639
theorem B5005691 : Blo 1482061 5005691 := bstep (se 1 (by rfl) ⟨3754268, by rfl⟩ : syracuseStep 5005691 = 7508537) B7508537
theorem B5005799 : Blo 1482061 5005799 := bstep (se 1 (by rfl) ⟨3754349, by rfl⟩ : syracuseStep 5005799 = 7508699) B7508699
theorem B1483263 : Blo 1482061 1483263 := bstep (se 1 (by rfl) ⟨1112447, by rfl⟩ : syracuseStep 1483263 = 2224895) B2224895
theorem B1483903 : Blo 1482061 1483903 := bstep (se 1 (by rfl) ⟨1112927, by rfl⟩ : syracuseStep 1483903 = 2225855) B2225855
theorem B8561801 : Blo 1482061 8561801 := bstep (se 2 (by rfl) ⟨3210675, by rfl⟩ : syracuseStep 8561801 = 6421351) B6421351
theorem B370534115 : Blo 1482061 370534115 := bstep (se 1 (by rfl) ⟨277900586, by rfl⟩ : syracuseStep 370534115 = 555801173) B555801173
theorem B30435377 : Blo 1482061 30435377 := bstep (se 2 (by rfl) ⟨11413266, by rfl⟩ : syracuseStep 30435377 = 22826533) B22826533
theorem B3336299 : Blo 1482061 3336299 := bstep (se 1 (by rfl) ⟨2502224, by rfl⟩ : syracuseStep 3336299 = 5004449) B5004449
theorem B166799483 : Blo 1482061 166799483 := bstep (se 1 (by rfl) ⟨125099612, by rfl⟩ : syracuseStep 166799483 = 250199225) B250199225
theorem B162293989 : Blo 1482061 162293989 := bstep (se 4 (by rfl) ⟨15215061, by rfl⟩ : syracuseStep 162293989 = 30430123) B30430123
theorem B3754259 : Blo 1482061 3754259 := bstep (se 1 (by rfl) ⟨2815694, by rfl⟩ : syracuseStep 3754259 = 5631389) B5631389
theorem B5630249 : Blo 1482061 5630249 := bstep (se 2 (by rfl) ⟨2111343, by rfl⟩ : syracuseStep 5630249 = 4222687) B4222687
theorem B3754471 : Blo 1482061 3754471 := bstep (se 1 (by rfl) ⟨2815853, by rfl⟩ : syracuseStep 3754471 = 5631707) B5631707
theorem B676007453 : Blo 1482061 676007453 := bstep (se 3 (by rfl) ⟨126751397, by rfl⟩ : syracuseStep 676007453 = 253502795) B253502795
theorem B3165751 : Blo 1482061 3165751 := bstep (se 1 (by rfl) ⟨2374313, by rfl⟩ : syracuseStep 3165751 = 4748627) B4748627
theorem B3337883 : Blo 1482061 3337883 := bstep (se 1 (by rfl) ⟨2503412, by rfl⟩ : syracuseStep 3337883 = 5006825) B5006825
theorem B8556263 : Blo 1482061 8556263 := bstep (se 1 (by rfl) ⟨6417197, by rfl⟩ : syracuseStep 8556263 = 12834395) B12834395
theorem B2502751 : Blo 1482061 2502751 := bstep (se 1 (by rfl) ⟨1877063, by rfl⟩ : syracuseStep 2502751 = 3754127) B3754127
theorem B2224265 : Blo 1482061 2224265 := bstep (se 2 (by rfl) ⟨834099, by rfl⟩ : syracuseStep 2224265 = 1668199) B1668199
theorem B40587425 : Blo 1482061 40587425 := bstep (se 2 (by rfl) ⟨15220284, by rfl⟩ : syracuseStep 40587425 = 30440569) B30440569
theorem B2225135 : Blo 1482061 2225135 := bstep (se 1 (by rfl) ⟨1668851, by rfl⟩ : syracuseStep 2225135 = 3337703) B3337703
theorem B8442913 : Blo 1482061 8442913 := bstep (se 2 (by rfl) ⟨3166092, by rfl⟩ : syracuseStep 8442913 = 6332185) B6332185
theorem B2225183 : Blo 1482061 2225183 := bstep (se 1 (by rfl) ⟨1668887, by rfl⟩ : syracuseStep 2225183 = 3337775) B3337775
theorem B5002343 : Blo 1482061 5002343 := bstep (se 1 (by rfl) ⟨3751757, by rfl⟩ : syracuseStep 5002343 = 7503515) B7503515
theorem B2503919 : Blo 1482061 2503919 := bstep (se 1 (by rfl) ⟨1877939, by rfl⟩ : syracuseStep 2503919 = 3755879) B3755879
theorem B2225639 : Blo 1482061 2225639 := bstep (se 1 (by rfl) ⟨1669229, by rfl⟩ : syracuseStep 2225639 = 3338459) B3338459
theorem B2225663 : Blo 1482061 2225663 := bstep (se 1 (by rfl) ⟨1669247, by rfl⟩ : syracuseStep 2225663 = 3338495) B3338495
theorem B1582265933 : Blo 1482061 1582265933 := bstep (se 3 (by rfl) ⟨296674862, by rfl⟩ : syracuseStep 1582265933 = 593349725) B593349725
theorem B2226041 : Blo 1482061 2226041 := bstep (se 2 (by rfl) ⟨834765, by rfl⟩ : syracuseStep 2226041 = 1669531) B1669531
theorem B3561355 : Blo 1482061 3561355 := bstep (se 1 (by rfl) ⟨2671016, by rfl⟩ : syracuseStep 3561355 = 5342033) B5342033
theorem B4511771 : Blo 1482061 4511771 := bstep (se 1 (by rfl) ⟨3383828, by rfl⟩ : syracuseStep 4511771 = 6767657) B6767657
theorem B28498067 : Blo 1482061 28498067 := bstep (se 1 (by rfl) ⟨21373550, by rfl⟩ : syracuseStep 28498067 = 42747101) B42747101
theorem B18291035 : Blo 1482061 18291035 := bstep (se 1 (by rfl) ⟨13718276, by rfl⟩ : syracuseStep 18291035 = 27436553) B27436553
theorem B4225375 : Blo 1482061 4225375 := bstep (se 1 (by rfl) ⟨3169031, by rfl⟩ : syracuseStep 4225375 = 6338063) B6338063
theorem B2816795 : Blo 1482061 2816795 := bstep (se 1 (by rfl) ⟨2112596, by rfl⟩ : syracuseStep 2816795 = 4225193) B4225193
theorem B9264223 : Blo 1482061 9264223 := bstep (se 1 (by rfl) ⟨6948167, by rfl⟩ : syracuseStep 9264223 = 13896335) B13896335
theorem B1482395 : Blo 1482061 1482395 := bstep (se 1 (by rfl) ⟨1111796, by rfl⟩ : syracuseStep 1482395 = 2223593) B2223593
theorem B7503839 : Blo 1482061 7503839 := bstep (se 1 (by rfl) ⟨5627879, by rfl⟩ : syracuseStep 7503839 = 11255759) B11255759
theorem B1482843 : Blo 1482061 1482843 := bstep (se 1 (by rfl) ⟨1112132, by rfl⟩ : syracuseStep 1482843 = 2224265) B2224265
theorem B27058283 : Blo 1482061 27058283 := bstep (se 1 (by rfl) ⟨20293712, by rfl⟩ : syracuseStep 27058283 = 40587425) B40587425
theorem B216391985 : Blo 1482061 216391985 := bstep (se 2 (by rfl) ⟨81146994, by rfl⟩ : syracuseStep 216391985 = 162293989) B162293989
theorem B22831469 : Blo 1482061 22831469 := bstep (se 3 (by rfl) ⟨4280900, by rfl⟩ : syracuseStep 22831469 = 8561801) B8561801
theorem B5005961 : Blo 1482061 5005961 := bstep (se 2 (by rfl) ⟨1877235, by rfl⟩ : syracuseStep 5005961 = 3754471) B3754471
theorem B1483423 : Blo 1482061 1483423 := bstep (se 1 (by rfl) ⟨1112567, by rfl⟩ : syracuseStep 1483423 = 2225135) B2225135
theorem B1483455 : Blo 1482061 1483455 := bstep (se 1 (by rfl) ⟨1112591, by rfl⟩ : syracuseStep 1483455 = 2225183) B2225183
theorem B3334895 : Blo 1482061 3334895 := bstep (se 1 (by rfl) ⟨2501171, by rfl⟩ : syracuseStep 3334895 = 5002343) B5002343
theorem B48776093 : Blo 1482061 48776093 := bstep (se 3 (by rfl) ⟨9145517, by rfl⟩ : syracuseStep 48776093 = 18291035) B18291035
theorem B1483759 : Blo 1482061 1483759 := bstep (se 1 (by rfl) ⟨1112819, by rfl⟩ : syracuseStep 1483759 = 2225639) B2225639
theorem B1483775 : Blo 1482061 1483775 := bstep (se 1 (by rfl) ⟨1112831, by rfl⟩ : syracuseStep 1483775 = 2225663) B2225663
theorem B1054843955 : Blo 1482061 1054843955 := bstep (se 1 (by rfl) ⟨791132966, by rfl⟩ : syracuseStep 1054843955 = 1582265933) B1582265933
theorem B247022743 : Blo 1482061 247022743 := bstep (se 1 (by rfl) ⟨185267057, by rfl⟩ : syracuseStep 247022743 = 370534115) B370534115
theorem B1484027 : Blo 1482061 1484027 := bstep (se 1 (by rfl) ⟨1113020, by rfl⟩ : syracuseStep 1484027 = 2226041) B2226041
theorem B3007847 : Blo 1482061 3007847 := bstep (se 1 (by rfl) ⟨2255885, by rfl⟩ : syracuseStep 3007847 = 4511771) B4511771
theorem B11257217 : Blo 1482061 11257217 := bstep (se 2 (by rfl) ⟨4221456, by rfl⟩ : syracuseStep 11257217 = 8442913) B8442913
theorem B111199655 : Blo 1482061 111199655 := bstep (se 1 (by rfl) ⟨83399741, by rfl⟩ : syracuseStep 111199655 = 166799483) B166799483
theorem B18998711 : Blo 1482061 18998711 := bstep (se 1 (by rfl) ⟨14249033, by rfl⟩ : syracuseStep 18998711 = 28498067) B28498067
theorem B3753499 : Blo 1482061 3753499 := bstep (se 1 (by rfl) ⟨2815124, by rfl⟩ : syracuseStep 3753499 = 5630249) B5630249
theorem B4221001 : Blo 1482061 4221001 := bstep (se 2 (by rfl) ⟨1582875, by rfl⟩ : syracuseStep 4221001 = 3165751) B3165751
theorem B5704175 : Blo 1482061 5704175 := bstep (se 1 (by rfl) ⟨4278131, by rfl⟩ : syracuseStep 5704175 = 8556263) B8556263
theorem B3337001 : Blo 1482061 3337001 := bstep (se 2 (by rfl) ⟨1251375, by rfl⟩ : syracuseStep 3337001 = 2502751) B2502751
theorem B3337127 : Blo 1482061 3337127 := bstep (se 1 (by rfl) ⟨2502845, by rfl⟩ : syracuseStep 3337127 = 5005691) B5005691
theorem B3337199 : Blo 1482061 3337199 := bstep (se 1 (by rfl) ⟨2502899, by rfl⟩ : syracuseStep 3337199 = 5005799) B5005799
theorem B324644021 : Blo 1482061 324644021 := bstep (se 5 (by rfl) ⟨15217688, by rfl⟩ : syracuseStep 324644021 = 30435377) B30435377
theorem B2224199 : Blo 1482061 2224199 := bstep (se 1 (by rfl) ⟨1668149, by rfl⟩ : syracuseStep 2224199 = 3336299) B3336299
theorem B2502839 : Blo 1482061 2502839 := bstep (se 1 (by rfl) ⟨1877129, by rfl⟩ : syracuseStep 2502839 = 3754259) B3754259
theorem B450671635 : Blo 1482061 450671635 := bstep (se 1 (by rfl) ⟨338003726, by rfl⟩ : syracuseStep 450671635 = 676007453) B676007453
theorem B2225255 : Blo 1482061 2225255 := bstep (se 1 (by rfl) ⟨1668941, by rfl⟩ : syracuseStep 2225255 = 3337883) B3337883
theorem B4748473 : Blo 1482061 4748473 := bstep (se 2 (by rfl) ⟨1780677, by rfl⟩ : syracuseStep 4748473 = 3561355) B3561355
theorem B5002559 : Blo 1482061 5002559 := bstep (se 1 (by rfl) ⟨3751919, by rfl⟩ : syracuseStep 5002559 = 7503839) B7503839
theorem B5633833 : Blo 1482061 5633833 := bstep (se 2 (by rfl) ⟨2112687, by rfl⟩ : syracuseStep 5633833 = 4225375) B4225375
theorem B1669279 : Blo 1482061 1669279 := bstep (se 1 (by rfl) ⟨1251959, by rfl⟩ : syracuseStep 1669279 = 2503919) B2503919
theorem B12352297 : Blo 1482061 12352297 := bstep (se 2 (by rfl) ⟨4632111, by rfl⟩ : syracuseStep 12352297 = 9264223) B9264223
theorem B7511453 : Blo 1482061 7511453 := bstep (se 3 (by rfl) ⟨1408397, by rfl⟩ : syracuseStep 7511453 = 2816795) B2816795
theorem B1482799 : Blo 1482061 1482799 := bstep (se 1 (by rfl) ⟨1112099, by rfl⟩ : syracuseStep 1482799 = 2224199) B2224199
theorem B18038855 : Blo 1482061 18038855 := bstep (se 1 (by rfl) ⟨13529141, by rfl⟩ : syracuseStep 18038855 = 27058283) B27058283
theorem B5628001 : Blo 1482061 5628001 := bstep (se 2 (by rfl) ⟨2110500, by rfl⟩ : syracuseStep 5628001 = 4221001) B4221001
theorem B144261323 : Blo 1482061 144261323 := bstep (se 1 (by rfl) ⟨108195992, by rfl⟩ : syracuseStep 144261323 = 216391985) B216391985
theorem B15220979 : Blo 1482061 15220979 := bstep (se 1 (by rfl) ⟨11415734, by rfl⟩ : syracuseStep 15220979 = 22831469) B22831469
theorem B1483503 : Blo 1482061 1483503 := bstep (se 1 (by rfl) ⟨1112627, by rfl⟩ : syracuseStep 1483503 = 2225255) B2225255
theorem B3335039 : Blo 1482061 3335039 := bstep (se 1 (by rfl) ⟨2501279, by rfl⟩ : syracuseStep 3335039 = 5002559) B5002559
theorem B7504811 : Blo 1482061 7504811 := bstep (se 1 (by rfl) ⟨5628608, by rfl⟩ : syracuseStep 7504811 = 11257217) B11257217
theorem B12665807 : Blo 1482061 12665807 := bstep (se 1 (by rfl) ⟨9499355, by rfl⟩ : syracuseStep 12665807 = 18998711) B18998711
theorem B3802783 : Blo 1482061 3802783 := bstep (se 1 (by rfl) ⟨2852087, by rfl⟩ : syracuseStep 3802783 = 5704175) B5704175
theorem B5007635 : Blo 1482061 5007635 := bstep (se 1 (by rfl) ⟨3755726, by rfl⟩ : syracuseStep 5007635 = 7511453) B7511453
theorem B3337307 : Blo 1482061 3337307 := bstep (se 1 (by rfl) ⟨2502980, by rfl⟩ : syracuseStep 3337307 = 5005961) B5005961
theorem B2223263 : Blo 1482061 2223263 := bstep (se 1 (by rfl) ⟨1667447, by rfl⟩ : syracuseStep 2223263 = 3334895) B3334895
theorem B32517395 : Blo 1482061 32517395 := bstep (se 1 (by rfl) ⟨24388046, by rfl⟩ : syracuseStep 32517395 = 48776093) B48776093
theorem B703229303 : Blo 1482061 703229303 := bstep (se 1 (by rfl) ⟨527421977, by rfl⟩ : syracuseStep 703229303 = 1054843955) B1054843955
theorem B16469729 : Blo 1482061 16469729 := bstep (se 2 (by rfl) ⟨6176148, by rfl⟩ : syracuseStep 16469729 = 12352297) B12352297
theorem B600895513 : Blo 1482061 600895513 := bstep (se 2 (by rfl) ⟨225335817, by rfl⟩ : syracuseStep 600895513 = 450671635) B450671635
theorem B329363657 : Blo 1482061 329363657 := bstep (se 2 (by rfl) ⟨123511371, by rfl⟩ : syracuseStep 329363657 = 247022743) B247022743
theorem B2224667 : Blo 1482061 2224667 := bstep (se 1 (by rfl) ⟨1668500, by rfl⟩ : syracuseStep 2224667 = 3337001) B3337001
theorem B2224751 : Blo 1482061 2224751 := bstep (se 1 (by rfl) ⟨1668563, by rfl⟩ : syracuseStep 2224751 = 3337127) B3337127
theorem B2224799 : Blo 1482061 2224799 := bstep (se 1 (by rfl) ⟨1668599, by rfl⟩ : syracuseStep 2224799 = 3337199) B3337199
theorem B216429347 : Blo 1482061 216429347 := bstep (se 1 (by rfl) ⟨162322010, by rfl⟩ : syracuseStep 216429347 = 324644021) B324644021
theorem B1668559 : Blo 1482061 1668559 := bstep (se 1 (by rfl) ⟨1251419, by rfl⟩ : syracuseStep 1668559 = 2502839) B2502839
theorem B2225705 : Blo 1482061 2225705 := bstep (se 2 (by rfl) ⟨834639, by rfl⟩ : syracuseStep 2225705 = 1669279) B1669279
theorem B2005231 : Blo 1482061 2005231 := bstep (se 1 (by rfl) ⟨1503923, by rfl⟩ : syracuseStep 2005231 = 3007847) B3007847
theorem B296532413 : Blo 1482061 296532413 := bstep (se 3 (by rfl) ⟨55599827, by rfl⟩ : syracuseStep 296532413 = 111199655) B111199655
theorem B6331297 : Blo 1482061 6331297 := bstep (se 2 (by rfl) ⟨2374236, by rfl⟩ : syracuseStep 6331297 = 4748473) B4748473
theorem B5004665 : Blo 1482061 5004665 := bstep (se 2 (by rfl) ⟨1876749, by rfl⟩ : syracuseStep 5004665 = 3753499) B3753499
theorem B7511777 : Blo 1482061 7511777 := bstep (se 2 (by rfl) ⟨2816916, by rfl⟩ : syracuseStep 7511777 = 5633833) B5633833
theorem B801194017 : Blo 1482061 801194017 := bstep (se 2 (by rfl) ⟨300447756, by rfl⟩ : syracuseStep 801194017 = 600895513) B600895513
theorem B12025903 : Blo 1482061 12025903 := bstep (se 1 (by rfl) ⟨9019427, by rfl⟩ : syracuseStep 12025903 = 18038855) B18038855
theorem B7504001 : Blo 1482061 7504001 := bstep (se 2 (by rfl) ⟨2814000, by rfl⟩ : syracuseStep 7504001 = 5628001) B5628001
theorem B96174215 : Blo 1482061 96174215 := bstep (se 1 (by rfl) ⟨72130661, by rfl⟩ : syracuseStep 96174215 = 144261323) B144261323
theorem B1483111 : Blo 1482061 1483111 := bstep (se 1 (by rfl) ⟨1112333, by rfl⟩ : syracuseStep 1483111 = 2224667) B2224667
theorem B1483167 : Blo 1482061 1483167 := bstep (se 1 (by rfl) ⟨1112375, by rfl⟩ : syracuseStep 1483167 = 2224751) B2224751
theorem B1483199 : Blo 1482061 1483199 := bstep (se 1 (by rfl) ⟨1112399, by rfl⟩ : syracuseStep 1483199 = 2224799) B2224799
theorem B144286231 : Blo 1482061 144286231 := bstep (se 1 (by rfl) ⟨108214673, by rfl⟩ : syracuseStep 144286231 = 216429347) B216429347
theorem B1483803 : Blo 1482061 1483803 := bstep (se 1 (by rfl) ⟨1112852, by rfl⟩ : syracuseStep 1483803 = 2225705) B2225705
theorem B21678263 : Blo 1482061 21678263 := bstep (se 1 (by rfl) ⟨16258697, by rfl⟩ : syracuseStep 21678263 = 32517395) B32517395
theorem B3336443 : Blo 1482061 3336443 := bstep (se 1 (by rfl) ⟨2502332, by rfl⟩ : syracuseStep 3336443 = 5004665) B5004665
theorem B10979819 : Blo 1482061 10979819 := bstep (se 1 (by rfl) ⟨8234864, by rfl⟩ : syracuseStep 10979819 = 16469729) B16469729
theorem B5007851 : Blo 1482061 5007851 := bstep (se 1 (by rfl) ⟨3755888, by rfl⟩ : syracuseStep 5007851 = 7511777) B7511777
theorem B2673641 : Blo 1482061 2673641 := bstep (se 2 (by rfl) ⟨1002615, by rfl⟩ : syracuseStep 2673641 = 2005231) B2005231
theorem B2223359 : Blo 1482061 2223359 := bstep (se 1 (by rfl) ⟨1667519, by rfl⟩ : syracuseStep 2223359 = 3335039) B3335039
theorem B8441729 : Blo 1482061 8441729 := bstep (se 2 (by rfl) ⟨3165648, by rfl⟩ : syracuseStep 8441729 = 6331297) B6331297
theorem B3338423 : Blo 1482061 3338423 := bstep (se 1 (by rfl) ⟨2503817, by rfl⟩ : syracuseStep 3338423 = 5007635) B5007635
theorem B2224745 : Blo 1482061 2224745 := bstep (se 2 (by rfl) ⟨834279, by rfl⟩ : syracuseStep 2224745 = 1668559) B1668559
theorem B2224871 : Blo 1482061 2224871 := bstep (se 1 (by rfl) ⟨1668653, by rfl⟩ : syracuseStep 2224871 = 3337307) B3337307
theorem B219575771 : Blo 1482061 219575771 := bstep (se 1 (by rfl) ⟨164681828, by rfl⟩ : syracuseStep 219575771 = 329363657) B329363657
theorem B10147319 : Blo 1482061 10147319 := bstep (se 1 (by rfl) ⟨7610489, by rfl⟩ : syracuseStep 10147319 = 15220979) B15220979
theorem B5003207 : Blo 1482061 5003207 := bstep (se 1 (by rfl) ⟨3752405, by rfl⟩ : syracuseStep 5003207 = 7504811) B7504811
theorem B8443871 : Blo 1482061 8443871 := bstep (se 1 (by rfl) ⟨6332903, by rfl⟩ : syracuseStep 8443871 = 12665807) B12665807
theorem B197688275 : Blo 1482061 197688275 := bstep (se 1 (by rfl) ⟨148266206, by rfl⟩ : syracuseStep 197688275 = 296532413) B296532413
theorem B1482175 : Blo 1482061 1482175 := bstep (se 1 (by rfl) ⟨1111631, by rfl⟩ : syracuseStep 1482175 = 2223263) B2223263
theorem B5070377 : Blo 1482061 5070377 := bstep (se 2 (by rfl) ⟨1901391, by rfl⟩ : syracuseStep 5070377 = 3802783) B3802783
theorem B468819535 : Blo 1482061 468819535 := bstep (se 1 (by rfl) ⟨351614651, by rfl⟩ : syracuseStep 468819535 = 703229303) B703229303
theorem B1483163 : Blo 1482061 1483163 := bstep (se 1 (by rfl) ⟨1112372, by rfl⟩ : syracuseStep 1483163 = 2224745) B2224745
theorem B1483247 : Blo 1482061 1483247 := bstep (se 1 (by rfl) ⟨1112435, by rfl⟩ : syracuseStep 1483247 = 2224871) B2224871
theorem B192381641 : Blo 1482061 192381641 := bstep (se 2 (by rfl) ⟨72143115, by rfl⟩ : syracuseStep 192381641 = 144286231) B144286231
theorem B146383847 : Blo 1482061 146383847 := bstep (se 1 (by rfl) ⟨109787885, by rfl⟩ : syracuseStep 146383847 = 219575771) B219575771
theorem B3335471 : Blo 1482061 3335471 := bstep (se 1 (by rfl) ⟨2501603, by rfl⟩ : syracuseStep 3335471 = 5003207) B5003207
theorem B5629247 : Blo 1482061 5629247 := bstep (se 1 (by rfl) ⟨4221935, by rfl⟩ : syracuseStep 5629247 = 8443871) B8443871
theorem B14452175 : Blo 1482061 14452175 := bstep (se 1 (by rfl) ⟨10839131, by rfl⟩ : syracuseStep 14452175 = 21678263) B21678263
theorem B625092713 : Blo 1482061 625092713 := bstep (se 2 (by rfl) ⟨234409767, by rfl⟩ : syracuseStep 625092713 = 468819535) B468819535
theorem B16034537 : Blo 1482061 16034537 := bstep (se 2 (by rfl) ⟨6012951, by rfl⟩ : syracuseStep 16034537 = 12025903) B12025903
theorem B13521005 : Blo 1482061 13521005 := bstep (se 3 (by rfl) ⟨2535188, by rfl⟩ : syracuseStep 13521005 = 5070377) B5070377
theorem B2224295 : Blo 1482061 2224295 := bstep (se 1 (by rfl) ⟨1668221, by rfl⟩ : syracuseStep 2224295 = 3336443) B3336443
theorem B7319879 : Blo 1482061 7319879 := bstep (se 1 (by rfl) ⟨5489909, by rfl⟩ : syracuseStep 7319879 = 10979819) B10979819
theorem B3338567 : Blo 1482061 3338567 := bstep (se 1 (by rfl) ⟨2503925, by rfl⟩ : syracuseStep 3338567 = 5007851) B5007851
theorem B1782427 : Blo 1482061 1782427 := bstep (se 1 (by rfl) ⟨1336820, by rfl⟩ : syracuseStep 1782427 = 2673641) B2673641
theorem B1068258689 : Blo 1482061 1068258689 := bstep (se 2 (by rfl) ⟨400597008, by rfl⟩ : syracuseStep 1068258689 = 801194017) B801194017
theorem B5002667 : Blo 1482061 5002667 := bstep (se 1 (by rfl) ⟨3752000, by rfl⟩ : syracuseStep 5002667 = 7504001) B7504001
theorem B64116143 : Blo 1482061 64116143 := bstep (se 1 (by rfl) ⟨48087107, by rfl⟩ : syracuseStep 64116143 = 96174215) B96174215
theorem B2225615 : Blo 1482061 2225615 := bstep (se 1 (by rfl) ⟨1669211, by rfl⟩ : syracuseStep 2225615 = 3338423) B3338423
theorem B6764879 : Blo 1482061 6764879 := bstep (se 1 (by rfl) ⟨5073659, by rfl⟩ : syracuseStep 6764879 = 10147319) B10147319
theorem B131792183 : Blo 1482061 131792183 := bstep (se 1 (by rfl) ⟨98844137, by rfl⟩ : syracuseStep 131792183 = 197688275) B197688275
theorem B1482239 : Blo 1482061 1482239 := bstep (se 1 (by rfl) ⟨1111679, by rfl⟩ : syracuseStep 1482239 = 2223359) B2223359
theorem B5627819 : Blo 1482061 5627819 := bstep (se 1 (by rfl) ⟨4220864, by rfl⟩ : syracuseStep 5627819 = 8441729) B8441729
theorem B1482863 : Blo 1482061 1482863 := bstep (se 1 (by rfl) ⟨1112147, by rfl⟩ : syracuseStep 1482863 = 2224295) B2224295
theorem B128254427 : Blo 1482061 128254427 := bstep (se 1 (by rfl) ⟨96190820, by rfl⟩ : syracuseStep 128254427 = 192381641) B192381641
theorem B2376569 : Blo 1482061 2376569 := bstep (se 2 (by rfl) ⟨891213, by rfl⟩ : syracuseStep 2376569 = 1782427) B1782427
theorem B3752831 : Blo 1482061 3752831 := bstep (se 1 (by rfl) ⟨2814623, by rfl⟩ : syracuseStep 3752831 = 5629247) B5629247
theorem B712172459 : Blo 1482061 712172459 := bstep (se 1 (by rfl) ⟨534129344, by rfl⟩ : syracuseStep 712172459 = 1068258689) B1068258689
theorem B3335111 : Blo 1482061 3335111 := bstep (se 1 (by rfl) ⟨2501333, by rfl⟩ : syracuseStep 3335111 = 5002667) B5002667
theorem B9634783 : Blo 1482061 9634783 := bstep (se 1 (by rfl) ⟨7226087, by rfl⟩ : syracuseStep 9634783 = 14452175) B14452175
theorem B1483743 : Blo 1482061 1483743 := bstep (se 1 (by rfl) ⟨1112807, by rfl⟩ : syracuseStep 1483743 = 2225615) B2225615
theorem B416728475 : Blo 1482061 416728475 := bstep (se 1 (by rfl) ⟨312546356, by rfl⟩ : syracuseStep 416728475 = 625092713) B625092713
theorem B87861455 : Blo 1482061 87861455 := bstep (se 1 (by rfl) ⟨65896091, by rfl⟩ : syracuseStep 87861455 = 131792183) B131792183
theorem B9014003 : Blo 1482061 9014003 := bstep (se 1 (by rfl) ⟨6760502, by rfl⟩ : syracuseStep 9014003 = 13521005) B13521005
theorem B2223647 : Blo 1482061 2223647 := bstep (se 1 (by rfl) ⟨1667735, by rfl⟩ : syracuseStep 2223647 = 3335471) B3335471
theorem B4509919 : Blo 1482061 4509919 := bstep (se 1 (by rfl) ⟨3382439, by rfl⟩ : syracuseStep 4509919 = 6764879) B6764879
theorem B4879919 : Blo 1482061 4879919 := bstep (se 1 (by rfl) ⟨3659939, by rfl⟩ : syracuseStep 4879919 = 7319879) B7319879
theorem B2225711 : Blo 1482061 2225711 := bstep (se 1 (by rfl) ⟨1669283, by rfl⟩ : syracuseStep 2225711 = 3338567) B3338567
theorem B97589231 : Blo 1482061 97589231 := bstep (se 1 (by rfl) ⟨73191923, by rfl⟩ : syracuseStep 97589231 = 146383847) B146383847
theorem B42744095 : Blo 1482061 42744095 := bstep (se 1 (by rfl) ⟨32058071, by rfl⟩ : syracuseStep 42744095 = 64116143) B64116143
theorem B10689691 : Blo 1482061 10689691 := bstep (se 1 (by rfl) ⟨8017268, by rfl⟩ : syracuseStep 10689691 = 16034537) B16034537
theorem B3751879 : Blo 1482061 3751879 := bstep (se 1 (by rfl) ⟨2813909, by rfl⟩ : syracuseStep 3751879 = 5627819) B5627819
theorem B6013225 : Blo 1482061 6013225 := bstep (se 2 (by rfl) ⟨2254959, by rfl⟩ : syracuseStep 6013225 = 4509919) B4509919
theorem B3253279 : Blo 1482061 3253279 := bstep (se 1 (by rfl) ⟨2439959, by rfl⟩ : syracuseStep 3253279 = 4879919) B4879919
theorem B1483807 : Blo 1482061 1483807 := bstep (se 1 (by rfl) ⟨1112855, by rfl⟩ : syracuseStep 1483807 = 2225711) B2225711
theorem B12846377 : Blo 1482061 12846377 := bstep (se 2 (by rfl) ⟨4817391, by rfl⟩ : syracuseStep 12846377 = 9634783) B9634783
theorem B58574303 : Blo 1482061 58574303 := bstep (se 1 (by rfl) ⟨43930727, by rfl⟩ : syracuseStep 58574303 = 87861455) B87861455
theorem B85502951 : Blo 1482061 85502951 := bstep (se 1 (by rfl) ⟨64127213, by rfl⟩ : syracuseStep 85502951 = 128254427) B128254427
theorem B1584379 : Blo 1482061 1584379 := bstep (se 1 (by rfl) ⟨1188284, by rfl⟩ : syracuseStep 1584379 = 2376569) B2376569
theorem B2501887 : Blo 1482061 2501887 := bstep (se 1 (by rfl) ⟨1876415, by rfl⟩ : syracuseStep 2501887 = 3752831) B3752831
theorem B2223407 : Blo 1482061 2223407 := bstep (se 1 (by rfl) ⟨1667555, by rfl⟩ : syracuseStep 2223407 = 3335111) B3335111
theorem B277818983 : Blo 1482061 277818983 := bstep (se 1 (by rfl) ⟨208364237, by rfl⟩ : syracuseStep 277818983 = 416728475) B416728475
theorem B28496063 : Blo 1482061 28496063 := bstep (se 1 (by rfl) ⟨21372047, by rfl⟩ : syracuseStep 28496063 = 42744095) B42744095
theorem B6009335 : Blo 1482061 6009335 := bstep (se 1 (by rfl) ⟨4507001, by rfl⟩ : syracuseStep 6009335 = 9014003) B9014003
theorem B5002505 : Blo 1482061 5002505 := bstep (se 2 (by rfl) ⟨1875939, by rfl⟩ : syracuseStep 5002505 = 3751879) B3751879
theorem B65059487 : Blo 1482061 65059487 := bstep (se 1 (by rfl) ⟨48794615, by rfl⟩ : syracuseStep 65059487 = 97589231) B97589231
theorem B14252921 : Blo 1482061 14252921 := bstep (se 2 (by rfl) ⟨5344845, by rfl⟩ : syracuseStep 14252921 = 10689691) B10689691
theorem B1482431 : Blo 1482061 1482431 := bstep (se 1 (by rfl) ⟨1111823, by rfl⟩ : syracuseStep 1482431 = 2223647) B2223647
theorem B1899126557 : Blo 1482061 1899126557 := bstep (se 3 (by rfl) ⟨356086229, by rfl⟩ : syracuseStep 1899126557 = 712172459) B712172459
theorem B18997375 : Blo 1482061 18997375 := bstep (se 1 (by rfl) ⟨14248031, by rfl⟩ : syracuseStep 18997375 = 28496063) B28496063
theorem B4006223 : Blo 1482061 4006223 := bstep (se 1 (by rfl) ⟨3004667, by rfl⟩ : syracuseStep 4006223 = 6009335) B6009335
theorem B3335003 : Blo 1482061 3335003 := bstep (se 1 (by rfl) ⟨2501252, by rfl⟩ : syracuseStep 3335003 = 5002505) B5002505
theorem B3335849 : Blo 1482061 3335849 := bstep (se 2 (by rfl) ⟨1250943, by rfl⟩ : syracuseStep 3335849 = 2501887) B2501887
theorem B57001967 : Blo 1482061 57001967 := bstep (se 1 (by rfl) ⟨42751475, by rfl⟩ : syracuseStep 57001967 = 85502951) B85502951
theorem B1266084371 : Blo 1482061 1266084371 := bstep (se 1 (by rfl) ⟨949563278, by rfl⟩ : syracuseStep 1266084371 = 1899126557) B1899126557
theorem B8564251 : Blo 1482061 8564251 := bstep (se 1 (by rfl) ⟨6423188, by rfl⟩ : syracuseStep 8564251 = 12846377) B12846377
theorem B8450021 : Blo 1482061 8450021 := bstep (se 4 (by rfl) ⟨792189, by rfl⟩ : syracuseStep 8450021 = 1584379) B1584379
theorem B4337705 : Blo 1482061 4337705 := bstep (se 2 (by rfl) ⟨1626639, by rfl⟩ : syracuseStep 4337705 = 3253279) B3253279
theorem B43372991 : Blo 1482061 43372991 := bstep (se 1 (by rfl) ⟨32529743, by rfl⟩ : syracuseStep 43372991 = 65059487) B65059487
theorem B8017633 : Blo 1482061 8017633 := bstep (se 2 (by rfl) ⟨3006612, by rfl⟩ : syracuseStep 8017633 = 6013225) B6013225
theorem B39049535 : Blo 1482061 39049535 := bstep (se 1 (by rfl) ⟨29287151, by rfl⟩ : syracuseStep 39049535 = 58574303) B58574303
theorem B9501947 : Blo 1482061 9501947 := bstep (se 1 (by rfl) ⟨7126460, by rfl⟩ : syracuseStep 9501947 = 14252921) B14252921
theorem B1482271 : Blo 1482061 1482271 := bstep (se 1 (by rfl) ⟨1111703, by rfl⟩ : syracuseStep 1482271 = 2223407) B2223407
theorem B185212655 : Blo 1482061 185212655 := bstep (se 1 (by rfl) ⟨138909491, by rfl⟩ : syracuseStep 185212655 = 277818983) B277818983
theorem B2891803 : Blo 1482061 2891803 := bstep (se 1 (by rfl) ⟨2168852, by rfl⟩ : syracuseStep 2891803 = 4337705) B4337705
theorem B25329833 : Blo 1482061 25329833 := bstep (se 2 (by rfl) ⟨9498687, by rfl⟩ : syracuseStep 25329833 = 18997375) B18997375
theorem B2670815 : Blo 1482061 2670815 := bstep (se 1 (by rfl) ⟨2003111, by rfl⟩ : syracuseStep 2670815 = 4006223) B4006223
theorem B844056247 : Blo 1482061 844056247 := bstep (se 1 (by rfl) ⟨633042185, by rfl⟩ : syracuseStep 844056247 = 1266084371) B1266084371
theorem B6334631 : Blo 1482061 6334631 := bstep (se 1 (by rfl) ⟨4750973, by rfl⟩ : syracuseStep 6334631 = 9501947) B9501947
theorem B2223335 : Blo 1482061 2223335 := bstep (se 1 (by rfl) ⟨1667501, by rfl⟩ : syracuseStep 2223335 = 3335003) B3335003
theorem B2223899 : Blo 1482061 2223899 := bstep (se 1 (by rfl) ⟨1667924, by rfl⟩ : syracuseStep 2223899 = 3335849) B3335849
theorem B123475103 : Blo 1482061 123475103 := bstep (se 1 (by rfl) ⟨92606327, by rfl⟩ : syracuseStep 123475103 = 185212655) B185212655
theorem B5633347 : Blo 1482061 5633347 := bstep (se 1 (by rfl) ⟨4225010, by rfl⟩ : syracuseStep 5633347 = 8450021) B8450021
theorem B28915327 : Blo 1482061 28915327 := bstep (se 1 (by rfl) ⟨21686495, by rfl⟩ : syracuseStep 28915327 = 43372991) B43372991
theorem B38001311 : Blo 1482061 38001311 := bstep (se 1 (by rfl) ⟨28500983, by rfl⟩ : syracuseStep 38001311 = 57001967) B57001967
theorem B26033023 : Blo 1482061 26033023 := bstep (se 1 (by rfl) ⟨19524767, by rfl⟩ : syracuseStep 26033023 = 39049535) B39049535
theorem B11419001 : Blo 1482061 11419001 := bstep (se 2 (by rfl) ⟨4282125, by rfl⟩ : syracuseStep 11419001 = 8564251) B8564251
theorem B10690177 : Blo 1482061 10690177 := bstep (se 2 (by rfl) ⟨4008816, by rfl⟩ : syracuseStep 10690177 = 8017633) B8017633
theorem B34710697 : Blo 1482061 34710697 := bstep (se 2 (by rfl) ⟨13016511, by rfl⟩ : syracuseStep 34710697 = 26033023) B26033023
theorem B38553769 : Blo 1482061 38553769 := bstep (se 2 (by rfl) ⟨14457663, by rfl⟩ : syracuseStep 38553769 = 28915327) B28915327
theorem B7612667 : Blo 1482061 7612667 := bstep (se 1 (by rfl) ⟨5709500, by rfl⟩ : syracuseStep 7612667 = 11419001) B11419001
theorem B16886555 : Blo 1482061 16886555 := bstep (se 1 (by rfl) ⟨12664916, by rfl⟩ : syracuseStep 16886555 = 25329833) B25329833
theorem B1780543 : Blo 1482061 1780543 := bstep (se 1 (by rfl) ⟨1335407, by rfl⟩ : syracuseStep 1780543 = 2670815) B2670815
theorem B82316735 : Blo 1482061 82316735 := bstep (se 1 (by rfl) ⟨61737551, by rfl⟩ : syracuseStep 82316735 = 123475103) B123475103
theorem B4223087 : Blo 1482061 4223087 := bstep (se 1 (by rfl) ⟨3167315, by rfl⟩ : syracuseStep 4223087 = 6334631) B6334631
theorem B25334207 : Blo 1482061 25334207 := bstep (se 1 (by rfl) ⟨19000655, by rfl⟩ : syracuseStep 25334207 = 38001311) B38001311
theorem B3855737 : Blo 1482061 3855737 := bstep (se 2 (by rfl) ⟨1445901, by rfl⟩ : syracuseStep 3855737 = 2891803) B2891803
theorem B7511129 : Blo 1482061 7511129 := bstep (se 2 (by rfl) ⟨2816673, by rfl⟩ : syracuseStep 7511129 = 5633347) B5633347
theorem B1482223 : Blo 1482061 1482223 := bstep (se 1 (by rfl) ⟨1111667, by rfl⟩ : syracuseStep 1482223 = 2223335) B2223335
theorem B14253569 : Blo 1482061 14253569 := bstep (se 2 (by rfl) ⟨5345088, by rfl⟩ : syracuseStep 14253569 = 10690177) B10690177
theorem B1125408329 : Blo 1482061 1125408329 := bstep (se 2 (by rfl) ⟨422028123, by rfl⟩ : syracuseStep 1125408329 = 844056247) B844056247
theorem B1482599 : Blo 1482061 1482599 := bstep (se 1 (by rfl) ⟨1111949, by rfl⟩ : syracuseStep 1482599 = 2223899) B2223899
theorem B51405025 : Blo 1482061 51405025 := bstep (se 2 (by rfl) ⟨19276884, by rfl⟩ : syracuseStep 51405025 = 38553769) B38553769
theorem B11257703 : Blo 1482061 11257703 := bstep (se 1 (by rfl) ⟨8443277, by rfl⟩ : syracuseStep 11257703 = 16886555) B16886555
theorem B5007419 : Blo 1482061 5007419 := bstep (se 1 (by rfl) ⟨3755564, by rfl⟩ : syracuseStep 5007419 = 7511129) B7511129
theorem B5075111 : Blo 1482061 5075111 := bstep (se 1 (by rfl) ⟨3806333, by rfl⟩ : syracuseStep 5075111 = 7612667) B7612667
theorem B46280929 : Blo 1482061 46280929 := bstep (se 2 (by rfl) ⟨17355348, by rfl⟩ : syracuseStep 46280929 = 34710697) B34710697
theorem B2815391 : Blo 1482061 2815391 := bstep (se 1 (by rfl) ⟨2111543, by rfl⟩ : syracuseStep 2815391 = 4223087) B4223087
theorem B16889471 : Blo 1482061 16889471 := bstep (se 1 (by rfl) ⟨12667103, by rfl⟩ : syracuseStep 16889471 = 25334207) B25334207
theorem B2570491 : Blo 1482061 2570491 := bstep (se 1 (by rfl) ⟨1927868, by rfl⟩ : syracuseStep 2570491 = 3855737) B3855737
theorem B2374057 : Blo 1482061 2374057 := bstep (se 2 (by rfl) ⟨890271, by rfl⟩ : syracuseStep 2374057 = 1780543) B1780543
theorem B54877823 : Blo 1482061 54877823 := bstep (se 1 (by rfl) ⟨41158367, by rfl⟩ : syracuseStep 54877823 = 82316735) B82316735
theorem B9502379 : Blo 1482061 9502379 := bstep (se 1 (by rfl) ⟨7126784, by rfl⟩ : syracuseStep 9502379 = 14253569) B14253569
theorem B750272219 : Blo 1482061 750272219 := bstep (se 1 (by rfl) ⟨562704164, by rfl⟩ : syracuseStep 750272219 = 1125408329) B1125408329
theorem B3383407 : Blo 1482061 3383407 := bstep (se 1 (by rfl) ⟨2537555, by rfl⟩ : syracuseStep 3383407 = 5075111) B5075111
theorem B1876927 : Blo 1482061 1876927 := bstep (se 1 (by rfl) ⟨1407695, by rfl⟩ : syracuseStep 1876927 = 2815391) B2815391
theorem B7505135 : Blo 1482061 7505135 := bstep (se 1 (by rfl) ⟨5628851, by rfl⟩ : syracuseStep 7505135 = 11257703) B11257703
theorem B6334919 : Blo 1482061 6334919 := bstep (se 1 (by rfl) ⟨4751189, by rfl⟩ : syracuseStep 6334919 = 9502379) B9502379
theorem B500181479 : Blo 1482061 500181479 := bstep (se 1 (by rfl) ⟨375136109, by rfl⟩ : syracuseStep 500181479 = 750272219) B750272219
theorem B3427321 : Blo 1482061 3427321 := bstep (se 2 (by rfl) ⟨1285245, by rfl⟩ : syracuseStep 3427321 = 2570491) B2570491
theorem B3165409 : Blo 1482061 3165409 := bstep (se 2 (by rfl) ⟨1187028, by rfl⟩ : syracuseStep 3165409 = 2374057) B2374057
theorem B11259647 : Blo 1482061 11259647 := bstep (se 1 (by rfl) ⟨8444735, by rfl⟩ : syracuseStep 11259647 = 16889471) B16889471
theorem B3338279 : Blo 1482061 3338279 := bstep (se 1 (by rfl) ⟨2503709, by rfl⟩ : syracuseStep 3338279 = 5007419) B5007419
theorem B61707905 : Blo 1482061 61707905 := bstep (se 2 (by rfl) ⟨23140464, by rfl⟩ : syracuseStep 61707905 = 46280929) B46280929
theorem B68540033 : Blo 1482061 68540033 := bstep (se 2 (by rfl) ⟨25702512, by rfl⟩ : syracuseStep 68540033 = 51405025) B51405025
theorem B36585215 : Blo 1482061 36585215 := bstep (se 1 (by rfl) ⟨27438911, by rfl⟩ : syracuseStep 36585215 = 54877823) B54877823
theorem B182773421 : Blo 1482061 182773421 := bstep (se 3 (by rfl) ⟨34270016, by rfl⟩ : syracuseStep 182773421 = 68540033) B68540033
theorem B7506431 : Blo 1482061 7506431 := bstep (se 1 (by rfl) ⟨5629823, by rfl⟩ : syracuseStep 7506431 = 11259647) B11259647
theorem B24390143 : Blo 1482061 24390143 := bstep (se 1 (by rfl) ⟨18292607, by rfl⟩ : syracuseStep 24390143 = 36585215) B36585215
theorem B2502569 : Blo 1482061 2502569 := bstep (se 2 (by rfl) ⟨938463, by rfl⟩ : syracuseStep 2502569 = 1876927) B1876927
theorem B4223279 : Blo 1482061 4223279 := bstep (se 1 (by rfl) ⟨3167459, by rfl⟩ : syracuseStep 4223279 = 6334919) B6334919
theorem B2225519 : Blo 1482061 2225519 := bstep (se 1 (by rfl) ⟨1669139, by rfl⟩ : syracuseStep 2225519 = 3338279) B3338279
theorem B4511209 : Blo 1482061 4511209 := bstep (se 2 (by rfl) ⟨1691703, by rfl⟩ : syracuseStep 4511209 = 3383407) B3383407
theorem B5003423 : Blo 1482061 5003423 := bstep (se 1 (by rfl) ⟨3752567, by rfl⟩ : syracuseStep 5003423 = 7505135) B7505135
theorem B41138603 : Blo 1482061 41138603 := bstep (se 1 (by rfl) ⟨30853952, by rfl⟩ : syracuseStep 41138603 = 61707905) B61707905
theorem B16882181 : Blo 1482061 16882181 := bstep (se 4 (by rfl) ⟨1582704, by rfl⟩ : syracuseStep 16882181 = 3165409) B3165409
theorem B4569761 : Blo 1482061 4569761 := bstep (se 2 (by rfl) ⟨1713660, by rfl⟩ : syracuseStep 4569761 = 3427321) B3427321
theorem B333454319 : Blo 1482061 333454319 := bstep (se 1 (by rfl) ⟨250090739, by rfl⟩ : syracuseStep 333454319 = 500181479) B500181479
theorem B1483679 : Blo 1482061 1483679 := bstep (se 1 (by rfl) ⟨1112759, by rfl⟩ : syracuseStep 1483679 = 2225519) B2225519
theorem B121848947 : Blo 1482061 121848947 := bstep (se 1 (by rfl) ⟨91386710, by rfl⟩ : syracuseStep 121848947 = 182773421) B182773421
theorem B3335615 : Blo 1482061 3335615 := bstep (se 1 (by rfl) ⟨2501711, by rfl⟩ : syracuseStep 3335615 = 5003423) B5003423
theorem B6014945 : Blo 1482061 6014945 := bstep (se 2 (by rfl) ⟨2255604, by rfl⟩ : syracuseStep 6014945 = 4511209) B4511209
theorem B222302879 : Blo 1482061 222302879 := bstep (se 1 (by rfl) ⟨166727159, by rfl⟩ : syracuseStep 222302879 = 333454319) B333454319
theorem B1668379 : Blo 1482061 1668379 := bstep (se 1 (by rfl) ⟨1251284, by rfl⟩ : syracuseStep 1668379 = 2502569) B2502569
theorem B11262077 : Blo 1482061 11262077 := bstep (se 3 (by rfl) ⟨2111639, by rfl⟩ : syracuseStep 11262077 = 4223279) B4223279
theorem B27425735 : Blo 1482061 27425735 := bstep (se 1 (by rfl) ⟨20569301, by rfl⟩ : syracuseStep 27425735 = 41138603) B41138603
theorem B5004287 : Blo 1482061 5004287 := bstep (se 1 (by rfl) ⟨3753215, by rfl⟩ : syracuseStep 5004287 = 7506431) B7506431
theorem B16260095 : Blo 1482061 16260095 := bstep (se 1 (by rfl) ⟨12195071, by rfl⟩ : syracuseStep 16260095 = 24390143) B24390143
theorem B11254787 : Blo 1482061 11254787 := bstep (se 1 (by rfl) ⟨8441090, by rfl⟩ : syracuseStep 11254787 = 16882181) B16882181
theorem B3046507 : Blo 1482061 3046507 := bstep (se 1 (by rfl) ⟨2284880, by rfl⟩ : syracuseStep 3046507 = 4569761) B4569761
theorem B148201919 : Blo 1482061 148201919 := bstep (se 1 (by rfl) ⟨111151439, by rfl⟩ : syracuseStep 148201919 = 222302879) B222302879
theorem B81232631 : Blo 1482061 81232631 := bstep (se 1 (by rfl) ⟨60924473, by rfl⟩ : syracuseStep 81232631 = 121848947) B121848947
theorem B3336191 : Blo 1482061 3336191 := bstep (se 1 (by rfl) ⟨2502143, by rfl⟩ : syracuseStep 3336191 = 5004287) B5004287
theorem B10840063 : Blo 1482061 10840063 := bstep (se 1 (by rfl) ⟨8130047, by rfl⟩ : syracuseStep 10840063 = 16260095) B16260095
theorem B16248037 : Blo 1482061 16248037 := bstep (se 4 (by rfl) ⟨1523253, by rfl⟩ : syracuseStep 16248037 = 3046507) B3046507
theorem B2223743 : Blo 1482061 2223743 := bstep (se 1 (by rfl) ⟨1667807, by rfl⟩ : syracuseStep 2223743 = 3335615) B3335615
theorem B7508051 : Blo 1482061 7508051 := bstep (se 1 (by rfl) ⟨5631038, by rfl⟩ : syracuseStep 7508051 = 11262077) B11262077
theorem B2224505 : Blo 1482061 2224505 := bstep (se 2 (by rfl) ⟨834189, by rfl⟩ : syracuseStep 2224505 = 1668379) B1668379
theorem B18283823 : Blo 1482061 18283823 := bstep (se 1 (by rfl) ⟨13712867, by rfl⟩ : syracuseStep 18283823 = 27425735) B27425735
theorem B7503191 : Blo 1482061 7503191 := bstep (se 1 (by rfl) ⟨5627393, by rfl⟩ : syracuseStep 7503191 = 11254787) B11254787
theorem B16039853 : Blo 1482061 16039853 := bstep (se 3 (by rfl) ⟨3007472, by rfl⟩ : syracuseStep 16039853 = 6014945) B6014945
theorem B5005367 : Blo 1482061 5005367 := bstep (se 1 (by rfl) ⟨3754025, by rfl⟩ : syracuseStep 5005367 = 7508051) B7508051
theorem B1483003 : Blo 1482061 1483003 := bstep (se 1 (by rfl) ⟨1112252, by rfl⟩ : syracuseStep 1483003 = 2224505) B2224505
theorem B10693235 : Blo 1482061 10693235 := bstep (se 1 (by rfl) ⟨8019926, by rfl⟩ : syracuseStep 10693235 = 16039853) B16039853
theorem B14453417 : Blo 1482061 14453417 := bstep (se 2 (by rfl) ⟨5420031, by rfl⟩ : syracuseStep 14453417 = 10840063) B10840063
theorem B2224127 : Blo 1482061 2224127 := bstep (se 1 (by rfl) ⟨1668095, by rfl⟩ : syracuseStep 2224127 = 3336191) B3336191
theorem B21664049 : Blo 1482061 21664049 := bstep (se 2 (by rfl) ⟨8124018, by rfl⟩ : syracuseStep 21664049 = 16248037) B16248037
theorem B5002127 : Blo 1482061 5002127 := bstep (se 1 (by rfl) ⟨3751595, by rfl⟩ : syracuseStep 5002127 = 7503191) B7503191
theorem B98801279 : Blo 1482061 98801279 := bstep (se 1 (by rfl) ⟨74100959, by rfl⟩ : syracuseStep 98801279 = 148201919) B148201919
theorem B54155087 : Blo 1482061 54155087 := bstep (se 1 (by rfl) ⟨40616315, by rfl⟩ : syracuseStep 54155087 = 81232631) B81232631
theorem B12189215 : Blo 1482061 12189215 := bstep (se 1 (by rfl) ⟨9141911, by rfl⟩ : syracuseStep 12189215 = 18283823) B18283823
theorem B1482495 : Blo 1482061 1482495 := bstep (se 1 (by rfl) ⟨1111871, by rfl⟩ : syracuseStep 1482495 = 2223743) B2223743
theorem B3334751 : Blo 1482061 3334751 := bstep (se 1 (by rfl) ⟨2501063, by rfl⟩ : syracuseStep 3334751 = 5002127) B5002127
theorem B36103391 : Blo 1482061 36103391 := bstep (se 1 (by rfl) ⟨27077543, by rfl⟩ : syracuseStep 36103391 = 54155087) B54155087
theorem B7128823 : Blo 1482061 7128823 := bstep (se 1 (by rfl) ⟨5346617, by rfl⟩ : syracuseStep 7128823 = 10693235) B10693235
theorem B9635611 : Blo 1482061 9635611 := bstep (se 1 (by rfl) ⟨7226708, by rfl⟩ : syracuseStep 9635611 = 14453417) B14453417
theorem B3336911 : Blo 1482061 3336911 := bstep (se 1 (by rfl) ⟨2502683, by rfl⟩ : syracuseStep 3336911 = 5005367) B5005367
theorem B231083189 : Blo 1482061 231083189 := bstep (se 5 (by rfl) ⟨10832024, by rfl⟩ : syracuseStep 231083189 = 21664049) B21664049
theorem B65867519 : Blo 1482061 65867519 := bstep (se 1 (by rfl) ⟨49400639, by rfl⟩ : syracuseStep 65867519 = 98801279) B98801279
theorem B8126143 : Blo 1482061 8126143 := bstep (se 1 (by rfl) ⟨6094607, by rfl⟩ : syracuseStep 8126143 = 12189215) B12189215
theorem B1482751 : Blo 1482061 1482751 := bstep (se 1 (by rfl) ⟨1112063, by rfl⟩ : syracuseStep 1482751 = 2224127) B2224127
theorem B24068927 : Blo 1482061 24068927 := bstep (se 1 (by rfl) ⟨18051695, by rfl⟩ : syracuseStep 24068927 = 36103391) B36103391
theorem B175646717 : Blo 1482061 175646717 := bstep (se 3 (by rfl) ⟨32933759, by rfl⟩ : syracuseStep 175646717 = 65867519) B65867519
theorem B9505097 : Blo 1482061 9505097 := bstep (se 2 (by rfl) ⟨3564411, by rfl⟩ : syracuseStep 9505097 = 7128823) B7128823
theorem B12847481 : Blo 1482061 12847481 := bstep (se 2 (by rfl) ⟨4817805, by rfl⟩ : syracuseStep 12847481 = 9635611) B9635611
theorem B2223167 : Blo 1482061 2223167 := bstep (se 1 (by rfl) ⟨1667375, by rfl⟩ : syracuseStep 2223167 = 3334751) B3334751
theorem B43339429 : Blo 1482061 43339429 := bstep (se 4 (by rfl) ⟨4063071, by rfl⟩ : syracuseStep 43339429 = 8126143) B8126143
theorem B2224607 : Blo 1482061 2224607 := bstep (se 1 (by rfl) ⟨1668455, by rfl⟩ : syracuseStep 2224607 = 3336911) B3336911
theorem B154055459 : Blo 1482061 154055459 := bstep (se 1 (by rfl) ⟨115541594, by rfl⟩ : syracuseStep 154055459 = 231083189) B231083189
theorem B1483071 : Blo 1482061 1483071 := bstep (se 1 (by rfl) ⟨1112303, by rfl⟩ : syracuseStep 1483071 = 2224607) B2224607
theorem B102703639 : Blo 1482061 102703639 := bstep (se 1 (by rfl) ⟨77027729, by rfl⟩ : syracuseStep 102703639 = 154055459) B154055459
theorem B117097811 : Blo 1482061 117097811 := bstep (se 1 (by rfl) ⟨87823358, by rfl⟩ : syracuseStep 117097811 = 175646717) B175646717
theorem B6336731 : Blo 1482061 6336731 := bstep (se 1 (by rfl) ⟨4752548, by rfl⟩ : syracuseStep 6336731 = 9505097) B9505097
theorem B8564987 : Blo 1482061 8564987 := bstep (se 1 (by rfl) ⟨6423740, by rfl⟩ : syracuseStep 8564987 = 12847481) B12847481
theorem B16045951 : Blo 1482061 16045951 := bstep (se 1 (by rfl) ⟨12034463, by rfl⟩ : syracuseStep 16045951 = 24068927) B24068927
theorem B1482111 : Blo 1482061 1482111 := bstep (se 1 (by rfl) ⟨1111583, by rfl⟩ : syracuseStep 1482111 = 2223167) B2223167
theorem B57785905 : Blo 1482061 57785905 := bstep (se 2 (by rfl) ⟨21669714, by rfl⟩ : syracuseStep 57785905 = 43339429) B43339429
theorem B308191493 : Blo 1482061 308191493 := bstep (se 4 (by rfl) ⟨28892952, by rfl⟩ : syracuseStep 308191493 = 57785905) B57785905
theorem B22839965 : Blo 1482061 22839965 := bstep (se 3 (by rfl) ⟨4282493, by rfl⟩ : syracuseStep 22839965 = 8564987) B8564987
theorem B136938185 : Blo 1482061 136938185 := bstep (se 2 (by rfl) ⟨51351819, by rfl⟩ : syracuseStep 136938185 = 102703639) B102703639
theorem B78065207 : Blo 1482061 78065207 := bstep (se 1 (by rfl) ⟨58548905, by rfl⟩ : syracuseStep 78065207 = 117097811) B117097811
theorem B21394601 : Blo 1482061 21394601 := bstep (se 2 (by rfl) ⟨8022975, by rfl⟩ : syracuseStep 21394601 = 16045951) B16045951
theorem B4224487 : Blo 1482061 4224487 := bstep (se 1 (by rfl) ⟨3168365, by rfl⟩ : syracuseStep 4224487 = 6336731) B6336731
theorem B91292123 : Blo 1482061 91292123 := bstep (se 1 (by rfl) ⟨68469092, by rfl⟩ : syracuseStep 91292123 = 136938185) B136938185
theorem B14263067 : Blo 1482061 14263067 := bstep (se 1 (by rfl) ⟨10697300, by rfl⟩ : syracuseStep 14263067 = 21394601) B21394601
theorem B5632649 : Blo 1482061 5632649 := bstep (se 2 (by rfl) ⟨2112243, by rfl⟩ : syracuseStep 5632649 = 4224487) B4224487
theorem B205460995 : Blo 1482061 205460995 := bstep (se 1 (by rfl) ⟨154095746, by rfl⟩ : syracuseStep 205460995 = 308191493) B308191493
theorem B15226643 : Blo 1482061 15226643 := bstep (se 1 (by rfl) ⟨11419982, by rfl⟩ : syracuseStep 15226643 = 22839965) B22839965
theorem B52043471 : Blo 1482061 52043471 := bstep (se 1 (by rfl) ⟨39032603, by rfl⟩ : syracuseStep 52043471 = 78065207) B78065207
theorem B10151095 : Blo 1482061 10151095 := bstep (se 1 (by rfl) ⟨7613321, by rfl⟩ : syracuseStep 10151095 = 15226643) B15226643
theorem B34695647 : Blo 1482061 34695647 := bstep (se 1 (by rfl) ⟨26021735, by rfl⟩ : syracuseStep 34695647 = 52043471) B52043471
theorem B60861415 : Blo 1482061 60861415 := bstep (se 1 (by rfl) ⟨45646061, by rfl⟩ : syracuseStep 60861415 = 91292123) B91292123
theorem B3755099 : Blo 1482061 3755099 := bstep (se 1 (by rfl) ⟨2816324, by rfl⟩ : syracuseStep 3755099 = 5632649) B5632649
theorem B9508711 : Blo 1482061 9508711 := bstep (se 1 (by rfl) ⟨7131533, by rfl⟩ : syracuseStep 9508711 = 14263067) B14263067
theorem B273947993 : Blo 1482061 273947993 := bstep (se 2 (by rfl) ⟨102730497, by rfl⟩ : syracuseStep 273947993 = 205460995) B205460995
theorem B13534793 : Blo 1482061 13534793 := bstep (se 2 (by rfl) ⟨5075547, by rfl⟩ : syracuseStep 13534793 = 10151095) B10151095
theorem B23130431 : Blo 1482061 23130431 := bstep (se 1 (by rfl) ⟨17347823, by rfl⟩ : syracuseStep 23130431 = 34695647) B34695647
theorem B2503399 : Blo 1482061 2503399 := bstep (se 1 (by rfl) ⟨1877549, by rfl⟩ : syracuseStep 2503399 = 3755099) B3755099
theorem B12678281 : Blo 1482061 12678281 := bstep (se 2 (by rfl) ⟨4754355, by rfl⟩ : syracuseStep 12678281 = 9508711) B9508711
theorem B81148553 : Blo 1482061 81148553 := bstep (se 2 (by rfl) ⟨30430707, by rfl⟩ : syracuseStep 81148553 = 60861415) B60861415
theorem B182631995 : Blo 1482061 182631995 := bstep (se 1 (by rfl) ⟨136973996, by rfl⟩ : syracuseStep 182631995 = 273947993) B273947993
theorem B15420287 : Blo 1482061 15420287 := bstep (se 1 (by rfl) ⟨11565215, by rfl⟩ : syracuseStep 15420287 = 23130431) B23130431
theorem B3337865 : Blo 1482061 3337865 := bstep (se 2 (by rfl) ⟨1251699, by rfl⟩ : syracuseStep 3337865 = 2503399) B2503399
theorem B9023195 : Blo 1482061 9023195 := bstep (se 1 (by rfl) ⟨6767396, by rfl⟩ : syracuseStep 9023195 = 13534793) B13534793
theorem B121754663 : Blo 1482061 121754663 := bstep (se 1 (by rfl) ⟨91315997, by rfl⟩ : syracuseStep 121754663 = 182631995) B182631995
theorem B8452187 : Blo 1482061 8452187 := bstep (se 1 (by rfl) ⟨6339140, by rfl⟩ : syracuseStep 8452187 = 12678281) B12678281
theorem B54099035 : Blo 1482061 54099035 := bstep (se 1 (by rfl) ⟨40574276, by rfl⟩ : syracuseStep 54099035 = 81148553) B81148553
theorem B24061853 : Blo 1482061 24061853 := bstep (se 3 (by rfl) ⟨4511597, by rfl⟩ : syracuseStep 24061853 = 9023195) B9023195
theorem B81169775 : Blo 1482061 81169775 := bstep (se 1 (by rfl) ⟨60877331, by rfl⟩ : syracuseStep 81169775 = 121754663) B121754663
theorem B36066023 : Blo 1482061 36066023 := bstep (se 1 (by rfl) ⟨27049517, by rfl⟩ : syracuseStep 36066023 = 54099035) B54099035
theorem B2225243 : Blo 1482061 2225243 := bstep (se 1 (by rfl) ⟨1668932, by rfl⟩ : syracuseStep 2225243 = 3337865) B3337865
theorem B5634791 : Blo 1482061 5634791 := bstep (se 1 (by rfl) ⟨4226093, by rfl⟩ : syracuseStep 5634791 = 8452187) B8452187
theorem B10280191 : Blo 1482061 10280191 := bstep (se 1 (by rfl) ⟨7710143, by rfl⟩ : syracuseStep 10280191 = 15420287) B15420287
theorem B24044015 : Blo 1482061 24044015 := bstep (se 1 (by rfl) ⟨18033011, by rfl⟩ : syracuseStep 24044015 = 36066023) B36066023
theorem B1483495 : Blo 1482061 1483495 := bstep (se 1 (by rfl) ⟨1112621, by rfl⟩ : syracuseStep 1483495 = 2225243) B2225243
theorem B16041235 : Blo 1482061 16041235 := bstep (se 1 (by rfl) ⟨12030926, by rfl⟩ : syracuseStep 16041235 = 24061853) B24061853
theorem B13706921 : Blo 1482061 13706921 := bstep (se 2 (by rfl) ⟨5140095, by rfl⟩ : syracuseStep 13706921 = 10280191) B10280191
theorem B3756527 : Blo 1482061 3756527 := bstep (se 1 (by rfl) ⟨2817395, by rfl⟩ : syracuseStep 3756527 = 5634791) B5634791
theorem B54113183 : Blo 1482061 54113183 := bstep (se 1 (by rfl) ⟨40584887, by rfl⟩ : syracuseStep 54113183 = 81169775) B81169775
theorem B9137947 : Blo 1482061 9137947 := bstep (se 1 (by rfl) ⟨6853460, by rfl⟩ : syracuseStep 9137947 = 13706921) B13706921
theorem B16029343 : Blo 1482061 16029343 := bstep (se 1 (by rfl) ⟨12022007, by rfl⟩ : syracuseStep 16029343 = 24044015) B24044015
theorem B2504351 : Blo 1482061 2504351 := bstep (se 1 (by rfl) ⟨1878263, by rfl⟩ : syracuseStep 2504351 = 3756527) B3756527
theorem B36075455 : Blo 1482061 36075455 := bstep (se 1 (by rfl) ⟨27056591, by rfl⟩ : syracuseStep 36075455 = 54113183) B54113183
theorem B21388313 : Blo 1482061 21388313 := bstep (se 2 (by rfl) ⟨8020617, by rfl⟩ : syracuseStep 21388313 = 16041235) B16041235
theorem B12183929 : Blo 1482061 12183929 := bstep (se 2 (by rfl) ⟨4568973, by rfl⟩ : syracuseStep 12183929 = 9137947) B9137947
theorem B14258875 : Blo 1482061 14258875 := bstep (se 1 (by rfl) ⟨10694156, by rfl⟩ : syracuseStep 14258875 = 21388313) B21388313
theorem B1669567 : Blo 1482061 1669567 := bstep (se 1 (by rfl) ⟨1252175, by rfl⟩ : syracuseStep 1669567 = 2504351) B2504351
theorem B24050303 : Blo 1482061 24050303 := bstep (se 1 (by rfl) ⟨18037727, by rfl⟩ : syracuseStep 24050303 = 36075455) B36075455
theorem B21372457 : Blo 1482061 21372457 := bstep (se 2 (by rfl) ⟨8014671, by rfl⟩ : syracuseStep 21372457 = 16029343) B16029343
theorem B16033535 : Blo 1482061 16033535 := bstep (se 1 (by rfl) ⟨12025151, by rfl⟩ : syracuseStep 16033535 = 24050303) B24050303
theorem B8122619 : Blo 1482061 8122619 := bstep (se 1 (by rfl) ⟨6091964, by rfl⟩ : syracuseStep 8122619 = 12183929) B12183929
theorem B28496609 : Blo 1482061 28496609 := bstep (se 2 (by rfl) ⟨10686228, by rfl⟩ : syracuseStep 28496609 = 21372457) B21372457
theorem B2226089 : Blo 1482061 2226089 := bstep (se 2 (by rfl) ⟨834783, by rfl⟩ : syracuseStep 2226089 = 1669567) B1669567
theorem B19011833 : Blo 1482061 19011833 := bstep (se 2 (by rfl) ⟨7129437, by rfl⟩ : syracuseStep 19011833 = 14258875) B14258875
theorem B18997739 : Blo 1482061 18997739 := bstep (se 1 (by rfl) ⟨14248304, by rfl⟩ : syracuseStep 18997739 = 28496609) B28496609
theorem B21660317 : Blo 1482061 21660317 := bstep (se 3 (by rfl) ⟨4061309, by rfl⟩ : syracuseStep 21660317 = 8122619) B8122619
theorem B1484059 : Blo 1482061 1484059 := bstep (se 1 (by rfl) ⟨1113044, by rfl⟩ : syracuseStep 1484059 = 2226089) B2226089
theorem B12674555 : Blo 1482061 12674555 := bstep (se 1 (by rfl) ⟨9505916, by rfl⟩ : syracuseStep 12674555 = 19011833) B19011833
theorem B10689023 : Blo 1482061 10689023 := bstep (se 1 (by rfl) ⟨8016767, by rfl⟩ : syracuseStep 10689023 = 16033535) B16033535
theorem B12665159 : Blo 1482061 12665159 := bstep (se 1 (by rfl) ⟨9498869, by rfl⟩ : syracuseStep 12665159 = 18997739) B18997739
theorem B8449703 : Blo 1482061 8449703 := bstep (se 1 (by rfl) ⟨6337277, by rfl⟩ : syracuseStep 8449703 = 12674555) B12674555
theorem B28504061 : Blo 1482061 28504061 := bstep (se 3 (by rfl) ⟨5344511, by rfl⟩ : syracuseStep 28504061 = 10689023) B10689023
theorem B14440211 : Blo 1482061 14440211 := bstep (se 1 (by rfl) ⟨10830158, by rfl⟩ : syracuseStep 14440211 = 21660317) B21660317
theorem B9626807 : Blo 1482061 9626807 := bstep (se 1 (by rfl) ⟨7220105, by rfl⟩ : syracuseStep 9626807 = 14440211) B14440211
theorem B5633135 : Blo 1482061 5633135 := bstep (se 1 (by rfl) ⟨4224851, by rfl⟩ : syracuseStep 5633135 = 8449703) B8449703
theorem B19002707 : Blo 1482061 19002707 := bstep (se 1 (by rfl) ⟨14252030, by rfl⟩ : syracuseStep 19002707 = 28504061) B28504061
theorem B8443439 : Blo 1482061 8443439 := bstep (se 1 (by rfl) ⟨6332579, by rfl⟩ : syracuseStep 8443439 = 12665159) B12665159
theorem B5628959 : Blo 1482061 5628959 := bstep (se 1 (by rfl) ⟨4221719, by rfl⟩ : syracuseStep 5628959 = 8443439) B8443439
theorem B3755423 : Blo 1482061 3755423 := bstep (se 1 (by rfl) ⟨2816567, by rfl⟩ : syracuseStep 3755423 = 5633135) B5633135
theorem B12668471 : Blo 1482061 12668471 := bstep (se 1 (by rfl) ⟨9501353, by rfl⟩ : syracuseStep 12668471 = 19002707) B19002707
theorem B25671485 : Blo 1482061 25671485 := bstep (se 3 (by rfl) ⟨4813403, by rfl⟩ : syracuseStep 25671485 = 9626807) B9626807
theorem B3752639 : Blo 1482061 3752639 := bstep (se 1 (by rfl) ⟨2814479, by rfl⟩ : syracuseStep 3752639 = 5628959) B5628959
theorem B17114323 : Blo 1482061 17114323 := bstep (se 1 (by rfl) ⟨12835742, by rfl⟩ : syracuseStep 17114323 = 25671485) B25671485
theorem B2503615 : Blo 1482061 2503615 := bstep (se 1 (by rfl) ⟨1877711, by rfl⟩ : syracuseStep 2503615 = 3755423) B3755423
theorem B8445647 : Blo 1482061 8445647 := bstep (se 1 (by rfl) ⟨6334235, by rfl⟩ : syracuseStep 8445647 = 12668471) B12668471
theorem B5630431 : Blo 1482061 5630431 := bstep (se 1 (by rfl) ⟨4222823, by rfl⟩ : syracuseStep 5630431 = 8445647) B8445647
theorem B2501759 : Blo 1482061 2501759 := bstep (se 1 (by rfl) ⟨1876319, by rfl⟩ : syracuseStep 2501759 = 3752639) B3752639
theorem B3338153 : Blo 1482061 3338153 := bstep (se 2 (by rfl) ⟨1251807, by rfl⟩ : syracuseStep 3338153 = 2503615) B2503615
theorem B22819097 : Blo 1482061 22819097 := bstep (se 2 (by rfl) ⟨8557161, by rfl⟩ : syracuseStep 22819097 = 17114323) B17114323
theorem B15212731 : Blo 1482061 15212731 := bstep (se 1 (by rfl) ⟨11409548, by rfl⟩ : syracuseStep 15212731 = 22819097) B22819097
theorem B7507241 : Blo 1482061 7507241 := bstep (se 2 (by rfl) ⟨2815215, by rfl⟩ : syracuseStep 7507241 = 5630431) B5630431
theorem B1667839 : Blo 1482061 1667839 := bstep (se 1 (by rfl) ⟨1250879, by rfl⟩ : syracuseStep 1667839 = 2501759) B2501759
theorem B2225435 : Blo 1482061 2225435 := bstep (se 1 (by rfl) ⟨1669076, by rfl⟩ : syracuseStep 2225435 = 3338153) B3338153
theorem B20283641 : Blo 1482061 20283641 := bstep (se 2 (by rfl) ⟨7606365, by rfl⟩ : syracuseStep 20283641 = 15212731) B15212731
theorem B1483623 : Blo 1482061 1483623 := bstep (se 1 (by rfl) ⟨1112717, by rfl⟩ : syracuseStep 1483623 = 2225435) B2225435
theorem B2223785 : Blo 1482061 2223785 := bstep (se 2 (by rfl) ⟨833919, by rfl⟩ : syracuseStep 2223785 = 1667839) B1667839
theorem B5004827 : Blo 1482061 5004827 := bstep (se 1 (by rfl) ⟨3753620, by rfl⟩ : syracuseStep 5004827 = 7507241) B7507241
theorem B3336551 : Blo 1482061 3336551 := bstep (se 1 (by rfl) ⟨2502413, by rfl⟩ : syracuseStep 3336551 = 5004827) B5004827
theorem B13522427 : Blo 1482061 13522427 := bstep (se 1 (by rfl) ⟨10141820, by rfl⟩ : syracuseStep 13522427 = 20283641) B20283641
theorem B1482523 : Blo 1482061 1482523 := bstep (se 1 (by rfl) ⟨1111892, by rfl⟩ : syracuseStep 1482523 = 2223785) B2223785
theorem B9014951 : Blo 1482061 9014951 := bstep (se 1 (by rfl) ⟨6761213, by rfl⟩ : syracuseStep 9014951 = 13522427) B13522427
theorem B2224367 : Blo 1482061 2224367 := bstep (se 1 (by rfl) ⟨1668275, by rfl⟩ : syracuseStep 2224367 = 3336551) B3336551
theorem B1482911 : Blo 1482061 1482911 := bstep (se 1 (by rfl) ⟨1112183, by rfl⟩ : syracuseStep 1482911 = 2224367) B2224367
theorem B6009967 : Blo 1482061 6009967 := bstep (se 1 (by rfl) ⟨4507475, by rfl⟩ : syracuseStep 6009967 = 9014951) B9014951
theorem B8013289 : Blo 1482061 8013289 := bstep (se 2 (by rfl) ⟨3004983, by rfl⟩ : syracuseStep 8013289 = 6009967) B6009967
theorem B10684385 : Blo 1482061 10684385 := bstep (se 2 (by rfl) ⟨4006644, by rfl⟩ : syracuseStep 10684385 = 8013289) B8013289
theorem B7122923 : Blo 1482061 7122923 := bstep (se 1 (by rfl) ⟨5342192, by rfl⟩ : syracuseStep 7122923 = 10684385) B10684385
theorem B4748615 : Blo 1482061 4748615 := bstep (se 1 (by rfl) ⟨3561461, by rfl⟩ : syracuseStep 4748615 = 7122923) B7122923
theorem B3165743 : Blo 1482061 3165743 := bstep (se 1 (by rfl) ⟨2374307, by rfl⟩ : syracuseStep 3165743 = 4748615) B4748615
theorem B8441981 : Blo 1482061 8441981 := bstep (se 3 (by rfl) ⟨1582871, by rfl⟩ : syracuseStep 8441981 = 3165743) B3165743
theorem B5627987 : Blo 1482061 5627987 := bstep (se 1 (by rfl) ⟨4220990, by rfl⟩ : syracuseStep 5627987 = 8441981) B8441981
theorem B3751991 : Blo 1482061 3751991 := bstep (se 1 (by rfl) ⟨2813993, by rfl⟩ : syracuseStep 3751991 = 5627987) B5627987
theorem B2501327 : Blo 1482061 2501327 := bstep (se 1 (by rfl) ⟨1875995, by rfl⟩ : syracuseStep 2501327 = 3751991) B3751991
theorem B1667551 : Blo 1482061 1667551 := bstep (se 1 (by rfl) ⟨1250663, by rfl⟩ : syracuseStep 1667551 = 2501327) B2501327
theorem B2223401 : Blo 1482061 2223401 := bstep (se 2 (by rfl) ⟨833775, by rfl⟩ : syracuseStep 2223401 = 1667551) B1667551
theorem B1482267 : Blo 1482061 1482267 := bstep (se 1 (by rfl) ⟨1111700, by rfl⟩ : syracuseStep 1482267 = 2223401) B2223401

theorem C0 (j : ℕ) (h1 : 370515 ≤ j) (h2 : j ≤ 371014) : Blo 1482061 (4 * j + 3) := by
  interval_cases j
  · exact B1482063
  · exact B1482067
  · exact B1482071
  · exact B1482075
  · exact B1482079
  · exact B1482083
  · exact B1482087
  · exact B1482091
  · exact B1482095
  · exact B1482099
  · exact B1482103
  · exact B1482107
  · exact B1482111
  · exact B1482115
  · exact B1482119
  · exact B1482123
  · exact B1482127
  · exact B1482131
  · exact B1482135
  · exact B1482139
  · exact B1482143
  · exact B1482147
  · exact B1482151
  · exact B1482155
  · exact B1482159
  · exact B1482163
  · exact B1482167
  · exact B1482171
  · exact B1482175
  · exact B1482179
  · exact B1482183
  · exact B1482187
  · exact B1482191
  · exact B1482195
  · exact B1482199
  · exact B1482203
  · exact B1482207
  · exact B1482211
  · exact B1482215
  · exact B1482219
  · exact B1482223
  · exact B1482227
  · exact B1482231
  · exact B1482235
  · exact B1482239
  · exact B1482243
  · exact B1482247
  · exact B1482251
  · exact B1482255
  · exact B1482259
  · exact B1482263
  · exact B1482267
  · exact B1482271
  · exact B1482275
  · exact B1482279
  · exact B1482283
  · exact B1482287
  · exact B1482291
  · exact B1482295
  · exact B1482299
  · exact B1482303
  · exact B1482307
  · exact B1482311
  · exact B1482315
  · exact B1482319
  · exact B1482323
  · exact B1482327
  · exact B1482331
  · exact B1482335
  · exact B1482339
  · exact B1482343
  · exact B1482347
  · exact B1482351
  · exact B1482355
  · exact B1482359
  · exact B1482363
  · exact B1482367
  · exact B1482371
  · exact B1482375
  · exact B1482379
  · exact B1482383
  · exact B1482387
  · exact B1482391
  · exact B1482395
  · exact B1482399
  · exact B1482403
  · exact B1482407
  · exact B1482411
  · exact B1482415
  · exact B1482419
  · exact B1482423
  · exact B1482427
  · exact B1482431
  · exact B1482435
  · exact B1482439
  · exact B1482443
  · exact B1482447
  · exact B1482451
  · exact B1482455
  · exact B1482459
  · exact B1482463
  · exact B1482467
  · exact B1482471
  · exact B1482475
  · exact B1482479
  · exact B1482483
  · exact B1482487
  · exact B1482491
  · exact B1482495
  · exact B1482499
  · exact B1482503
  · exact B1482507
  · exact B1482511
  · exact B1482515
  · exact B1482519
  · exact B1482523
  · exact B1482527
  · exact B1482531
  · exact B1482535
  · exact B1482539
  · exact B1482543
  · exact B1482547
  · exact B1482551
  · exact B1482555
  · exact B1482559
  · exact B1482563
  · exact B1482567
  · exact B1482571
  · exact B1482575
  · exact B1482579
  · exact B1482583
  · exact B1482587
  · exact B1482591
  · exact B1482595
  · exact B1482599
  · exact B1482603
  · exact B1482607
  · exact B1482611
  · exact B1482615
  · exact B1482619
  · exact B1482623
  · exact B1482627
  · exact B1482631
  · exact B1482635
  · exact B1482639
  · exact B1482643
  · exact B1482647
  · exact B1482651
  · exact B1482655
  · exact B1482659
  · exact B1482663
  · exact B1482667
  · exact B1482671
  · exact B1482675
  · exact B1482679
  · exact B1482683
  · exact B1482687
  · exact B1482691
  · exact B1482695
  · exact B1482699
  · exact B1482703
  · exact B1482707
  · exact B1482711
  · exact B1482715
  · exact B1482719
  · exact B1482723
  · exact B1482727
  · exact B1482731
  · exact B1482735
  · exact B1482739
  · exact B1482743
  · exact B1482747
  · exact B1482751
  · exact B1482755
  · exact B1482759
  · exact B1482763
  · exact B1482767
  · exact B1482771
  · exact B1482775
  · exact B1482779
  · exact B1482783
  · exact B1482787
  · exact B1482791
  · exact B1482795
  · exact B1482799
  · exact B1482803
  · exact B1482807
  · exact B1482811
  · exact B1482815
  · exact B1482819
  · exact B1482823
  · exact B1482827
  · exact B1482831
  · exact B1482835
  · exact B1482839
  · exact B1482843
  · exact B1482847
  · exact B1482851
  · exact B1482855
  · exact B1482859
  · exact B1482863
  · exact B1482867
  · exact B1482871
  · exact B1482875
  · exact B1482879
  · exact B1482883
  · exact B1482887
  · exact B1482891
  · exact B1482895
  · exact B1482899
  · exact B1482903
  · exact B1482907
  · exact B1482911
  · exact B1482915
  · exact B1482919
  · exact B1482923
  · exact B1482927
  · exact B1482931
  · exact B1482935
  · exact B1482939
  · exact B1482943
  · exact B1482947
  · exact B1482951
  · exact B1482955
  · exact B1482959
  · exact B1482963
  · exact B1482967
  · exact B1482971
  · exact B1482975
  · exact B1482979
  · exact B1482983
  · exact B1482987
  · exact B1482991
  · exact B1482995
  · exact B1482999
  · exact B1483003
  · exact B1483007
  · exact B1483011
  · exact B1483015
  · exact B1483019
  · exact B1483023
  · exact B1483027
  · exact B1483031
  · exact B1483035
  · exact B1483039
  · exact B1483043
  · exact B1483047
  · exact B1483051
  · exact B1483055
  · exact B1483059
  · exact B1483063
  · exact B1483067
  · exact B1483071
  · exact B1483075
  · exact B1483079
  · exact B1483083
  · exact B1483087
  · exact B1483091
  · exact B1483095
  · exact B1483099
  · exact B1483103
  · exact B1483107
  · exact B1483111
  · exact B1483115
  · exact B1483119
  · exact B1483123
  · exact B1483127
  · exact B1483131
  · exact B1483135
  · exact B1483139
  · exact B1483143
  · exact B1483147
  · exact B1483151
  · exact B1483155
  · exact B1483159
  · exact B1483163
  · exact B1483167
  · exact B1483171
  · exact B1483175
  · exact B1483179
  · exact B1483183
  · exact B1483187
  · exact B1483191
  · exact B1483195
  · exact B1483199
  · exact B1483203
  · exact B1483207
  · exact B1483211
  · exact B1483215
  · exact B1483219
  · exact B1483223
  · exact B1483227
  · exact B1483231
  · exact B1483235
  · exact B1483239
  · exact B1483243
  · exact B1483247
  · exact B1483251
  · exact B1483255
  · exact B1483259
  · exact B1483263
  · exact B1483267
  · exact B1483271
  · exact B1483275
  · exact B1483279
  · exact B1483283
  · exact B1483287
  · exact B1483291
  · exact B1483295
  · exact B1483299
  · exact B1483303
  · exact B1483307
  · exact B1483311
  · exact B1483315
  · exact B1483319
  · exact B1483323
  · exact B1483327
  · exact B1483331
  · exact B1483335
  · exact B1483339
  · exact B1483343
  · exact B1483347
  · exact B1483351
  · exact B1483355
  · exact B1483359
  · exact B1483363
  · exact B1483367
  · exact B1483371
  · exact B1483375
  · exact B1483379
  · exact B1483383
  · exact B1483387
  · exact B1483391
  · exact B1483395
  · exact B1483399
  · exact B1483403
  · exact B1483407
  · exact B1483411
  · exact B1483415
  · exact B1483419
  · exact B1483423
  · exact B1483427
  · exact B1483431
  · exact B1483435
  · exact B1483439
  · exact B1483443
  · exact B1483447
  · exact B1483451
  · exact B1483455
  · exact B1483459
  · exact B1483463
  · exact B1483467
  · exact B1483471
  · exact B1483475
  · exact B1483479
  · exact B1483483
  · exact B1483487
  · exact B1483491
  · exact B1483495
  · exact B1483499
  · exact B1483503
  · exact B1483507
  · exact B1483511
  · exact B1483515
  · exact B1483519
  · exact B1483523
  · exact B1483527
  · exact B1483531
  · exact B1483535
  · exact B1483539
  · exact B1483543
  · exact B1483547
  · exact B1483551
  · exact B1483555
  · exact B1483559
  · exact B1483563
  · exact B1483567
  · exact B1483571
  · exact B1483575
  · exact B1483579
  · exact B1483583
  · exact B1483587
  · exact B1483591
  · exact B1483595
  · exact B1483599
  · exact B1483603
  · exact B1483607
  · exact B1483611
  · exact B1483615
  · exact B1483619
  · exact B1483623
  · exact B1483627
  · exact B1483631
  · exact B1483635
  · exact B1483639
  · exact B1483643
  · exact B1483647
  · exact B1483651
  · exact B1483655
  · exact B1483659
  · exact B1483663
  · exact B1483667
  · exact B1483671
  · exact B1483675
  · exact B1483679
  · exact B1483683
  · exact B1483687
  · exact B1483691
  · exact B1483695
  · exact B1483699
  · exact B1483703
  · exact B1483707
  · exact B1483711
  · exact B1483715
  · exact B1483719
  · exact B1483723
  · exact B1483727
  · exact B1483731
  · exact B1483735
  · exact B1483739
  · exact B1483743
  · exact B1483747
  · exact B1483751
  · exact B1483755
  · exact B1483759
  · exact B1483763
  · exact B1483767
  · exact B1483771
  · exact B1483775
  · exact B1483779
  · exact B1483783
  · exact B1483787
  · exact B1483791
  · exact B1483795
  · exact B1483799
  · exact B1483803
  · exact B1483807
  · exact B1483811
  · exact B1483815
  · exact B1483819
  · exact B1483823
  · exact B1483827
  · exact B1483831
  · exact B1483835
  · exact B1483839
  · exact B1483843
  · exact B1483847
  · exact B1483851
  · exact B1483855
  · exact B1483859
  · exact B1483863
  · exact B1483867
  · exact B1483871
  · exact B1483875
  · exact B1483879
  · exact B1483883
  · exact B1483887
  · exact B1483891
  · exact B1483895
  · exact B1483899
  · exact B1483903
  · exact B1483907
  · exact B1483911
  · exact B1483915
  · exact B1483919
  · exact B1483923
  · exact B1483927
  · exact B1483931
  · exact B1483935
  · exact B1483939
  · exact B1483943
  · exact B1483947
  · exact B1483951
  · exact B1483955
  · exact B1483959
  · exact B1483963
  · exact B1483967
  · exact B1483971
  · exact B1483975
  · exact B1483979
  · exact B1483983
  · exact B1483987
  · exact B1483991
  · exact B1483995
  · exact B1483999
  · exact B1484003
  · exact B1484007
  · exact B1484011
  · exact B1484015
  · exact B1484019
  · exact B1484023
  · exact B1484027
  · exact B1484031
  · exact B1484035
  · exact B1484039
  · exact B1484043
  · exact B1484047
  · exact B1484051
  · exact B1484055
  · exact B1484059

theorem solution (m : ℕ) (hlo : 1482061 ≤ m) (hhi : m ≤ 1484061) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 370515 ≤ j := by omega
    have hj2 : j ≤ 371014 := by omega
    have hb : Blo 1482061 (4 * j + 3) := by
      exact C0 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
